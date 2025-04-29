@echo off
echo Running Raft KLEE test...

REM Create clean output directory
if exist klee-last rmdir /s /q klee-last
if exist klee_analysis_report.txt del klee_analysis_report.txt

REM Run the KLEE symbolic test with cleaner output
echo.
echo ===== Running KLEE symbolic test =====
echo.
docker run --rm -v "%cd%":/workdir klee/klee:latest bash -c "cd /workdir && clang -I /klee/include -emit-llvm -c -g -O0 -Wno-everything raft_klee_test.c -o raft_klee_test.bc && klee --libc=uclibc --posix-runtime --optimize --only-output-states-covering-new --max-time=300 raft_klee_test.bc 2>&1 | grep -v 'warning: Linking' | grep -v 'WARNING: this target' | grep -v undefined"

REM Analyze KLEE results with clean output
echo.
echo ===== Analyzing KLEE test results =====
echo.
docker run --rm -v "%cd%":/workdir python:3 bash -c "cd /workdir && python3 analyze_klee_results.py klee-last > klee_analysis_report.txt && cat klee_analysis_report.txt | grep -v WARNING"

echo.
echo Done!
echo Full results have been written to klee_analysis_report.txt 