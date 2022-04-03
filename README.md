# Clausal Proof Optimizer

### Description

This tool stitches unsatisfiability proofs generated by Cube-and-Conquer SAT solvers into a single optimized proof, reducing proof checking time by several orders of magnitude.

### Prerequisites

1. Python>=3.6.8
2. Linux-based system

### Installation

Clone repository to any linux-based system

### Usage

  python3 proof_optimizer.py CNF_FILE DIRECTORY_CONTAINING_PROOFS OPTIMIZATION_LEVEL

OPTIMIZATION LEVEL : <0, 1, 2>
0: No Optimization. All proofs in directory are concatenated together without attempting to reduce their size.
1: Intelligent Optimization. Proofs are concatenated and then a heuristic is applied to determine if redundant clauses will be removed.
2: Maximum Optimization. Proofs are concatenated and redundant clauses are removed. 

#### Example
  
  python3 proof_optimizer.py example/cnf/random_ksat.dimacs example/proof/ 0

### Contributers

1. [Abhishek Nair](https://github.com/abhisheknair1729)
2. [Saranyu Chattopadhyay](https://github.com/saranyuc3)
3. [Andrew Wu](https://github.com/anwu1219)

