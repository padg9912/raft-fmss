#!/usr/bin/env python3
"""
KLEE Results Analyzer for Raft Algorithm Testing

This script analyzes KLEE test results to extract metrics on:
1. Leader election success rate
2. Time taken to elect a leader
3. Split brain occurrence detection
4. Liveness property violations
"""

import os
import sys
import re
import glob
from collections import defaultdict

def parse_klee_info(info_file):
    """Parse basic information from KLEE info file"""
    metrics = {
        'total_paths': 0,
        'completed_paths': 0,
        'total_instructions': 0,
        'run_time': '',
    }
    
    try:
        with open(info_file, 'r') as f:
            content = f.read()
            
            # Extract total paths explored
            match = re.search(r'explored paths = (\d+)', content)
            if match:
                metrics['total_paths'] = int(match.group(1))
                
            # Extract completed paths
            match = re.search(r'completed paths = (\d+)', content)
            if match:
                metrics['completed_paths'] = int(match.group(1))
                
            # Extract total instructions
            match = re.search(r'total instructions = (\d+)', content)
            if match:
                metrics['total_instructions'] = int(match.group(1))
                
            # Extract runtime
            match = re.search(r'Elapsed: ([\d:]+)', content)
            if match:
                metrics['run_time'] = match.group(1)
    except Exception as e:
        print(f"Error parsing info file: {e}")
        
    return metrics

def parse_klee_warnings(warnings_file):
    """Parse warnings from KLEE warnings file"""
    warnings = []
    try:
        with open(warnings_file, 'r') as f:
            # Filter out common warnings that are less useful
            for line in f:
                if 'WARNING' in line:
                    if 'undefined reference to function: klee_get_value' in line:
                        continue
                    if 'calling external: syscall' in line:
                        continue
                    if 'Alignment of memory from call "malloc"' in line:
                        continue
                    if 'calling __klee_posix_wrapped_main with extra arguments' in line:
                        continue
                    
                    warnings.append(line.strip())
    except Exception as e:
        print(f"Error parsing warnings file: {e}")
        
    return warnings

def analyze_test_cases(klee_dir):
    """Analyze KLEE test cases to extract metrics"""
    test_files = glob.glob(os.path.join(klee_dir, 'test*.ktest'))
    error_files = glob.glob(os.path.join(klee_dir, 'test*.err'))
    
    # Error analysis
    errors = defaultdict(int)
    liveness_violations = 0
    safety_violations = 0
    
    for err_file in error_files:
        try:
            with open(err_file, 'r') as f:
                content = f.read()
                if "No leader elected" in content or "Liveness violation" in content:
                    liveness_violations += 1
                if "leader per term" in content or "leader_uniqueness" in content:
                    safety_violations += 1
                if "Poor election success rate" in content:
                    errors["Poor election success rate"] += 1
                if "split brain" in content:
                    errors["Split brain detected"] += 1
        except Exception as e:
            print(f"Error analyzing {err_file}: {e}")
    
    return {
        'total_test_cases': len(test_files),
        'error_test_cases': len(error_files),
        'liveness_violations': liveness_violations,
        'safety_violations': safety_violations,
        'error_types': dict(errors)
    }

def calculate_delayed_heartbeat_impact(klee_dir):
    """Calculate impact of delayed heartbeats on leader election"""
    # This is an approximation based on test case analysis
    # For a more accurate analysis, we would need to extract this directly from KLEE
    total_regular_tests = 0
    total_delayed_tests = 0
    regular_success = 0
    delayed_success = 0
    
    test_files = glob.glob(os.path.join(klee_dir, 'test*.ktest'))
    
    # We don't have direct access to the heartbeat delay information in test files
    # But we can make some estimations based on the assertions and test outcomes
    for test_file in test_files:
        err_file = test_file.replace('.ktest', '.err')
        has_error = os.path.exists(err_file)
        
        # The actual decision on whether it's a delayed heartbeat test
        # would require looking at the test content, which is binary
        # This is a placeholder for demonstration purposes
        if "delay" in test_file:  # This is symbolic and won't actually match
            total_delayed_tests += 1
            if not has_error:
                delayed_success += 1
        else:
            total_regular_tests += 1
            if not has_error:
                regular_success += 1
    
    return {
        'delayed_heartbeat_tests': total_delayed_tests,
        'delayed_heartbeat_success_rate': delayed_success / total_delayed_tests if total_delayed_tests > 0 else 0,
        'regular_tests': total_regular_tests,
        'regular_success_rate': regular_success / total_regular_tests if total_regular_tests > 0 else 0
    }

def analyze_klee_results(klee_dir):
    """Analyze all KLEE results and generate metrics report"""
    if not os.path.isdir(klee_dir):
        print(f"Error: {klee_dir} is not a valid directory")
        return
        
    info_file = os.path.join(klee_dir, 'info')
    warnings_file = os.path.join(klee_dir, 'warnings.txt')
    
    info_metrics = parse_klee_info(info_file)
    warnings = parse_klee_warnings(warnings_file)
    test_metrics = analyze_test_cases(klee_dir)
    
    success_rate = 1.0 - (test_metrics['error_test_cases'] / test_metrics['total_test_cases']) if test_metrics['total_test_cases'] > 0 else 0
    
    # Generate report
    report = f"""
============================================================
Raft Algorithm KLEE Symbolic Execution Report
============================================================

Test Summary:
------------
Total Paths Explored: {info_metrics['total_paths']}
Completed Paths: {info_metrics['completed_paths']}
Total Instructions: {info_metrics['total_instructions']}
Run Time: {info_metrics['run_time']}
Total Test Cases: {test_metrics['total_test_cases']}
Error Test Cases: {test_metrics['error_test_cases']}

Safety Properties:
----------------
Leader Uniqueness Violations: {test_metrics['safety_violations']}
Split Brain Scenarios: {test_metrics['error_types'].get('Split brain detected', 0)}

Liveness Properties:
-----------------
Leader Election Failures: {test_metrics['liveness_violations']}
Overall Election Success Rate: {success_rate:.2%}
"""

    # Only add warnings if there are any significant ones to report
    if warnings:
        report += f"""
Important Warnings:
----------------
{os.linesep.join(warnings)}
"""

    # Only add error types if there are any to report
    if test_metrics['error_types']:
        report += f"""
Error Types:
----------
{os.linesep.join([f"- {k}: {v}" for k, v in test_metrics['error_types'].items()])}
"""

    report += """
============================================================
"""
    
    return report

def main():
    klee_dir = 'klee-out-0'  # Default directory
    
    if len(sys.argv) > 1:
        klee_dir = sys.argv[1]
        
    report = analyze_klee_results(klee_dir)
    print(report)
    
    # Write report to file
    with open('klee_analysis_report.txt', 'w') as f:
        f.write(report)
    
    print(f"Report written to klee_analysis_report.txt")

if __name__ == "__main__":
    main() 