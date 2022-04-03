import glob 
import sys
import os
import shutil
import subprocess
import multiprocessing as mp

def combine_proofs(clause_set_1, clause_set_2, branch_variable):
  '''
  Clause_set_1 = conflict clauses (list of strings) of branch_variable branch
  clause_set_2 = conflict_clauses (list of strings) of ~branch_variable branch
  returns: set of combined clauses
  '''

  branch_variable_n = branch_variable[1:] if branch_variable[0] == "-" else "-" + branch_variable
  clause_1          = []
  clause_2          = []

  for i in range(len(clause_set_1)):
    if clause_set_1[i][0] != "d":
      clause_1.append( clause_set_1[i][:-2] + branch_variable_n + " 0\n" )
  
  for i in range(len(clause_set_2)):
    if clause_set_2[i][0] != "d":
      clause_2.append(clause_set_2[i][:-2] + branch_variable + " 0\n" )
  
  return clause_1 + clause_2 + ["0\n"]


def sorting_key(tup):
  '''
    returns negative of fourth element in tuple
    Use: To help in sorting
  '''
  
  return -tup[3]


def order_proofs(list_of_proof_files):
  '''
  decides order in which proofs must be combined
  returns: ordered list of tuples denoting proof files to be joined together
  '''
  
  proofs   = []
  ord_list = []
  
  for prooffile in list_of_proof_files:
    prooffile = prooffile[:-6]
    proofname = prooffile.split("/")[-1]
    proofs.append(proofname)
    
  for proofname in proofs:
    prooflits = proofname.split("_")
    lenproof  = len(prooflits)
    lastlit   = prooflits[-1]
    
    if lenproof > 1:
      proofname_inv  = "_".join(prooflits[:-1]) + "_" + (lastlit[1:] if  lastlit[0] == "n" else "n"+lastlit)
      proofname_stub = "_".join(prooflits[:-1])
    else:
      proofname_inv  = "n" + prooflits[0] if prooflits[0][0] != "n" else prooflits[0][1:]
      proofname_stub = ""
     
    if proofname_stub != "":
      proofs.append(proofname_stub)
    
    if proofname_stub == "":
      prooflen = 0
    else:
      prooflen = len(proofname_stub.split("_"))

    if (proofname, proofname_inv, proofname_stub, prooflen) not in ord_list:
      if (proofname_inv, proofname, proofname_stub, prooflen) not in ord_list:
        ord_list.append((proofname, proofname_inv, proofname_stub, prooflen))

  ord_list.sort(key = sorting_key)

  return ord_list
     

def write_proof(f, proof):
  '''
  write proof to file
  '''
  for lemma in proof:
    f.write(lemma)


def write_cnf(f, cnf):
  '''
  write cnf formula to file
  '''
  
  for clause in cnf:
    f.write(clause +"\n")


def split_lits( lit_string ):
  '''
  returns list of literals from string
  '''

  lit_list = lit_string.split("_")
  lit_list = [l if l[0] != "n" else "-"+l[1:] for l in lit_list]
  
  return lit_list


def create_cnf( cnf_file, lits, is_leaf ):
  '''
  Creates CNF file for sub-problem
  '''
  
  decision_lits = split_lits( lits )
  
  with open(cnf_file, "r") as f:
    cnf_clauses = f.readlines()
  
  for i in range(len(cnf_clauses)):
    if "p cnf" in cnf_clauses[i]:
      clause_words     = cnf_clauses[i].split()
      num_clauses      = int(clause_words[-1])
      
      if is_leaf:
        num_clauses    = num_clauses + len(decision_lits)
      else:
        num_clauses    = num_clauses + len(decision_lits) - 1

      clause_words[-1] = str(num_clauses) + "\n"
      cnf_clauses[i]   = " ".join(clause_words)
      break
  
  # append path condition to cnf clauses
  if is_leaf:
    for lit in decision_lits:
      cnf_clauses.append( lit + " 0")
  else:
    for lit in decision_lits[:-1]:
      cnf_clauses.append( lit + " 0")
  
  # write out the cnf formula with path condition
  cnf_name = "./temp-work/" + lits + ".cnf"
  with open(cnf_name, "w") as f:
    write_cnf( f, cnf_clauses )
  
  return cnf_name


def optimize_orig_proofs( proof_list, cnf_file ):
  '''
  Optimizes original proofs by running drat-trim
  '''
  
  process = []

  for proof in proof_list:
    lits     = proof.split("/")[-1][:-6]
    cnf_name = create_cnf( cnf_file, lits, True )
    with open(proof, "r") as f:
      proof_lemmas = f.readlines()
    process.append( subprocess.Popen( ["./drat-trim", cnf_name, proof, "-l",  proof], stdout=subprocess.DEVNULL ) )
  
  for proc in process:
    proc.wait()


def compute_avg_lemma_length( lemmas ):
  '''
  Computes average length of lemmas
  '''
  avg_lemma_length = 0.0

  for lemma in lemmas:
    avg_lemma_length = avg_lemma_length + len(lemma.split())

  return avg_lemma_length/len(lemmas)
  
def find_global_avg( proof_files ):
  '''
  computes avg lemma lenght of all proofs
  TODO: remove deletion information from lemma before using it
  '''
  avg_length = 0.0

  for filename in proof_files:
    with open(filename, "r") as f:
      lemmas  = f.readlines()
      avg_length = avg_length + compute_avg_lemma_length( lemmas )

  return avg_length


def generate_final_proof( ordered_proofs, cnf_name, LEMMA_LENGTH, optimize ):
  '''
  Main function to compute final optimized proof
  runs drat-trim always if optimize = 2
  runs drat-trim intelligently if optimize = 1
  never runs drat-trim if optimize = 0
  '''
  process  = []
  level    = ordered_proofs[0][3]
  
  for tup in ordered_proofs:
    proof_file1 = tup[0] + ".proof"
    proof_file2 = tup[1] + ".proof"
    proof_path  = "./temp-work/"
    curr_lvl    = tup[3]
    proof_1     = []
    proof_2     = []
    proof_comb  = []
    
    if curr_lvl < level:            #wait for previous processes to complete
      level   = curr_lvl
      for proc in process:
        proc.wait()
      process = []
    
    decision_lits = split_lits( tup[0] )  
    
    if len(decision_lits) > 1:
      proof_out_file = tup[2] + ".proof"
    else:
      proof_out_file = "final.proof"
    
    with open("./temp-work/"+proof_file1,"r") as f:
      proof_1 = f.readlines()

    with open("./temp-work/"+proof_file2,"r") as f:
      proof_2 = f.readlines()
    
    proof_comb       = combine_proofs( proof_1, proof_2, decision_lits[-1] )
    avg_lemma_length = compute_avg_lemma_length( proof_comb )

    with open("./temp-work/"+proof_out_file,"w") as f:
      write_proof( f, proof_comb )
  
    cnf_name = create_cnf( cnf_file, tup[0], False)

    if avg_lemma_length > LEMMA_LENGTH:
      if optimize == 1:
        process.append( subprocess.Popen(["./drat-trim", cnf_name, proof_path+proof_out_file, "-l", proof_path+proof_out_file], stdout=subprocess.DEVNULL ) )
      
    if optimize == 2:
      process.append( subprocess.Popen(["./drat-trim", cnf_name, proof_path+proof_out_file, "-l", proof_path+proof_out_file],  stdout=subprocess.DEVNULL ))
   
  for proc in process:
    proc.wait()

# Main Function
if __name__ == "__main__":
  
  if len(sys.argv) != 4:
    print("")
    print("Usage: python3 proof_optimizer.py path/to/cnf path/to/proofs/directory optimize (0, 1, 2)")
    print("")
    print("Optimize = 0: No optimization")
    print("Optimize = 1: Intelligent Optimization using Heuristics")
    print("Optimize = 2: Maximum Optimization (Very slow)")
    print("")
    print("Proof files must have extension .proof")
    sys.exit(0)
  
  cnf_file     = sys.argv[1]
  proof_path   = sys.argv[2]
  optimize     = int(sys.argv[3])
  LEMMA_LENGTH = 10  #default value 
  proof_path   = proof_path if proof_path[-1] == "/" else proof_path+"/"
  
  proof_files = glob.glob(proof_path+"*.proof")
  
  # Move all files to temp-work dir
  if os.path.exists("./temp-work"):
    shutil.rmtree("./temp-work")
  os.mkdir("./temp-work")
  for f in proof_files:
    shutil.copy(f, "./temp-work/")
  
  proof_files = glob.glob("./temp-work/*.proof")

  if proof_files is None:
    print("Proof files not found")
    print("Proof files must have extension .proof")
    sys.exit(0)
  
  optimize_orig_proofs( proof_files, cnf_file )
  
  ordered_proofs = order_proofs( proof_files )
  
  '''
  for o in ordered_proofs:
    print(o)
  '''
  if optimize > 0:
    LEMMA_LENGTH = find_global_avg( proof_files )

  generate_final_proof( ordered_proofs, cnf_file, LEMMA_LENGTH, optimize )
 
