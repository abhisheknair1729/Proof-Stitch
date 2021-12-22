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
  
  for i in range(len(clause_set_1)):
    clause_set_1[i] = clause_set_1[i][:-2]+branch_variable_n+" 0\n"
  

  for i in range(len(clause_set_2)):
    clause_set_2[i] = clause_set_2[i][:-2]+branch_variable+" 0\n"
  #print(clause_set_1)
  return clause_set_1 + clause_set_2 + ["0\n"]


def sorting_key(tup):
  '''
    returns negative of first element in tuple
    Use: To help in sorting
  '''
  return -tup[3]


def order_proofs(list_of_proof_files):
  '''
  decides order in which proofs must be combined
  returns: ordered list of tuples denoting proof files to be joined together
  '''
  proofs = []
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
      proofname_inv = "_".join(prooflits[:-1]) + "_" + (lastlit[1:] if  lastlit[0] == "n" else "n"+lastlit)
      proofname_stub = "_".join(prooflits[:-1])
    else:
      proofname_inv = "n" + prooflits[0] if prooflits[0][0] != "n" else prooflits[0][1:]
      proofname_stub = ""
    
    if proofname_stub != "":
      proofs.append(proofname_stub)
    
    if (proofname, proofname_inv, proofname_stub) not in ord_list:
      if (proofname_inv, proofname, proofname_stub) not in ord_list:
        prooflen = len(proofname_stub.split("_"))
        #print(proofname_stub)
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

if __name__ == "__main__":
  
  if len(sys.argv) != 3:
    print("Usage: python3 run.py path/to/cnf path/to/proofs/directory")
    print("Proof files must have extension .proof")
    sys.exit(0)
  
  cnf_file = sys.argv[1]
  proof_path = sys.argv[2]
  
  proof_path = proof_path if proof_path[-1] == "/" else proof_path+"/"
  
  proof_files = glob.glob(proof_path+"*.proof")

  #print("Making directory temp-work")
  
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
  
  process = []
  for fil in proof_files:
    
    fil_name = fil.split("/")[-1]
    decision_lits = fil_name[:-6].split("_")
    decision_lit = decision_lits[-1] if decision_lits[-1][0]!="n" else "-" + decision_lits[-1][1:]
    decision_lits_actual = []

    for lit in decision_lits:
      decision_lits_actual.append(lit if lit[0] != "n" else "-"+ lit[1:])

    with open(cnf_file, "r") as f:
      cnf_clauses = f.readlines()
    
    # updating number of clauses in cnf file
    for i in range(len(cnf_clauses)):
      if "p cnf" in cnf_clauses[i]:
        temp = cnf_clauses[i].split()
        num_clauses = int(temp[-1])
        #print(num_clauses)
        num_clauses = num_clauses + len(decision_lits_actual)
        temp[-1] = str(num_clauses) + "\n"
        cnf_clauses[i] = " ".join(temp)
        break
    
    # append path condition to cnf clauses
    for lit in decision_lits_actual:
      cnf_clauses.append( lit + " 0")
    
    # write out the cnf formula with path condition
    cnf_name = "./temp-work/"+fil_name+".cnf"
    with open(cnf_name, "w") as f:
      write_cnf(f,cnf_clauses)
    
    with open(fil, "r") as f:
      proof_lemmas = f.readlines()
    
    process.append(subprocess.Popen(["./drat-trim", cnf_name, fil, "-l",  fil],stdout=subprocess.PIPE))
  
  for proc in process:
    proc.wait()
  
  ordered_proof = order_proofs(proof_files)
  #for o in ordered_proof:
  #  print(o)
  process = []
  curr_lvl = -1
  level = ordered_proof[0][3]

  for tup in ordered_proof:
    #read proofs
    proof_file1 = tup[0] + ".proof"
    proof_file2 = tup[1] + ".proof"
    
    curr_lvl = tup[3]
    print(curr_lvl) 
    if curr_lvl < level:
      #wait for previous processes to complete
      print(process)
      for proc in process:
        proc.wait()

      level = curr_lvl
      process = []

    decision_lits = proof_file1[:-6].split("_")
    decision_lit = decision_lits[-1] if decision_lits[-1][0]!="n" else "-" + decision_lits[-1][1:]
    decision_lits_except_last = []

    for lit in decision_lits[:-1]:
      decision_lits_except_last.append(lit if lit[0] != "n" else "-"+ lit[1:])

    if len(decision_lits) > 1:
      proof_out_file = "_".join(decision_lits[:-1]) + ".proof"
    else:
      proof_out_file = "final.proof"
    
    #print(proof_out_file)
    temp_1 = []
    temp_2 = []
    proof_1 = []
    proof_2 = []
    proof_out = []
    
    with open("./temp-work/"+proof_file1,"r") as f:
      temp_1 = f.readlines()

    with open("./temp-work/"+proof_file2,"r") as f:
      temp_2 = f.readlines()
    
    # delete deletion clauses
    for l in temp_1:
      if l[0] != "d":
        proof_1.append(l)
    
    for l in temp_2:
      if l[0] != "d":
        proof_2.append(l)

    proof_out = combine_proofs(proof_1, proof_2, decision_lit)
    
    with open("./temp-work/"+proof_out_file,"w") as f:
      write_proof(f, proof_out)
 
    with open(cnf_file, "r") as f:
      cnf_clauses = f.readlines()
    
    # updating number of clauses in cnf file
    for i in range(len(cnf_clauses)):
      if "p cnf" in cnf_clauses[i]:
        temp = cnf_clauses[i].split()
        num_clauses = int(temp[-1])
        #print(num_clauses)
        num_clauses = num_clauses + len(decision_lits_except_last)
        temp[-1] = str(num_clauses) + "\n"
        cnf_clauses[i] = " ".join(temp)
        break
    
    # append path condition to cnf clauses
    for lit in decision_lits_except_last:
      cnf_clauses.append( lit + " 0")

    # write out the cnf formula with path condition
    cnf_name = "./temp-work/"+proof_out_file+".cnf"
    with open(cnf_name, "w") as f:
      write_cnf(f,cnf_clauses)
    
    process.append(subprocess.Popen(["./drat-trim", cnf_name, "./temp-work/"+proof_out_file, "-l", "./temp-work/"+proof_out_file],stdout=subprocess.PIPE))
        
