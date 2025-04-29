# Raft Consensus Protocol: Formal Verification and Symbolic Analysis

This project provides a comprehensive, adversarially robust verification of the Raft consensus protocol, combining symbolic execution (KLEE) and formal modeling (TLA+). The repository is organized to support both implementation-level and protocol-level analysis, with all code, models, scripts, and results available for reproducibility.

---

## Project Structure

```
raft-fmss/
│
├── raft/                # cowsql Raft C implementation (as a submodule)
│   └── ...              # Source code, docs, and build files for Raft
│
├── raft_spec/           # TLA+ Raft specification and model checking artifacts
│   ├── Raft.tla         # Main TLA+ specification of Raft (with adversarial extensions)
│   ├── RaftAdversarial.cfg # TLA+ model checker configuration for adversarial scenarios
│   └── Raft.toolbox/    # TLA+ Toolbox project files (model, config, etc.)
│              └── TLAplusModelCheck.out # Example output from TLA+ model checking  
│      
│
├── test_harness/        # KLEE symbolic test harness, scripts, and results
│   ├── raft_klee_test.c # KLEE symbolic test harness for Raft
│   ├── Makefile         # Build instructions for KLEE
│   ├── analyze_klee_results.py # Script to analyze KLEE output
│   ├── klee-out-*/      # Output directories from KLEE runs (test cases, logs, errors)
│   ├── run_docker.bat   # Windows script to run KLEE in Docker
│   └── README.md        # Details on running and interpreting KLEE tests
│
├── run_tests.sh         # Top-level script to build and run all tests (KLEE and regular)
├── .gitmodules          # Git submodule configuration for cowsql Raft
└── .gitignore           # Ignore patterns for build and output files
```

---

## Implementation Overview

- **Raft C Implementation:**  
  The project uses the [cowsql Raft](https://github.com/cowsql/cowsql) C implementation as the basis for symbolic execution and testing.
- **KLEE Symbolic Execution:**  
  The `test_harness/raft_klee_test.c` file is instrumented with symbolic variables for timeouts, delays, and message drops. Assertions check for safety (leader uniqueness, log consistency) and liveness (eventual leader election). The test harness explores a wide range of adversarial scenarios.
- **TLA+ Formal Modeling:**  
  The `raft_spec/Raft.tla` file specifies the Raft protocol, extended with adversarial parameters (message drops, partitions, delays). The TLA+ Toolbox and TLC model checker are used to verify safety and liveness invariants under these conditions.

---

## How to Use This Repository

### 1. **Clone and Initialize Submodules**
```bash
git clone https://github.com/padg9912/raft-fmss.git
cd raft-fmss/raft-analysis
git submodule update --init --recursive
```

### 2. **Run All Tests**
```bash
./run_tests.sh
```
- This script builds and runs both the regular and KLEE symbolic tests.
- KLEE results are stored in `test_harness/klee-out-*` directories.

### 3. **KLEE Symbolic Execution**
- See `test_harness/README.md` for detailed instructions.
- Analyze results using `analyze_klee_results.py`.

### 4. **TLA+ Model Checking**
- Open `raft_spec/Raft.tla` and `Raft.toolbox` in the TLA+ Toolbox.
- Use `RaftAdversarial.cfg` and the provided `.launch` files to run model checking.
- Example output is in `TLAplusModelCheck.out`.

---

## Key Folders and Files

- **`raft/`**: cowsql Raft C implementation (submodule, do not edit directly)
- **`raft_spec/`**: TLA+ specification, configs, and model checking outputs
- **`raft_spec/Raft.toolbox/`**: TLA+ Toolbox project files (model, config)
- **`test_harness/`**: KLEE test harness, scripts, and symbolic execution results
- **`run_tests.sh`**: Script to build and run all tests

---

## Reproducibility

- All code, models, and scripts are available in this repository.
- To reproduce experiments, follow the steps above and consult the `README.md` files in each subdirectory for details.

---

## Contact

For questions or issues, please contact the project maintainer via the [GitHub repository](https://github.com/padg9912/raft-fmss).

---

This README should provide your professor with a clear understanding of the project's structure, implementation, and how to navigate and reproduce your results. If you want to add more details (e.g., about results, evaluation, or specific scripts), let me know! 
