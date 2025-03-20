# PDGF
PDGF is a Predecessor-aware Directed Greybox Fuzzing tool. It can maintain a target-reachable code area (predecessors) and conduct regional fuzzing within this area.

The instrumentation process relies on the [SVF](https://github.com/SVF-tools/SVF).

The fuzzing process is based on the [AFL](https://github.com/google/AFL)

# Docker
We recommend using docker:
```
docker pull seussl/pdgf:latest
```

# Run PDGF
1. Compile with GLLVM
```
export CC=~/gllvm/gclang
export CXX=~/gllvm/gclang++
```
2. Generate Bytecode
```
~/gllvm/get-bc program	# Replace with actual program
```
3. Static Analysis Procedure

3.1 Define Target Points
```
echo $'fileName:Line' > targets  # Replace with actual file/line info
```
3.2 Run Static Analysis
```
~/pdgf/instrument/bin/cbi --targets=targets program.bc
```
3.3 Record Precondition Metrics

Note: Capture the reported precondition region count for subsequent steps

4. Generate Instrumented Binary
```
~/pdgf/fuzz/afl-clang-fast program.bc -o program.ci
```
5. Fuzzing Execution
```
~/pdgf/fuzz/afl-fuzz -i in/ -o out -e 10693 ./program.ci @@
```
Critical Parameters:
-e: Precondition edge count (from Step 3.3)


