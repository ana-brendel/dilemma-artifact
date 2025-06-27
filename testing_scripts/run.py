import os
import json
import subprocess
import sys

def get_dict(path):
    with open(path) as tf:
        return json.load(tf)

def remove_suffix(input_string, suffix):
    if suffix and input_string.endswith(suffix):
        return input_string[:-len(suffix)]
    return input_string 
    
test_folder_dictionary = get_dict(os.path.join(os.getcwd(),"testing_scripts/test_folders.json"))
test_dictionary = get_dict(os.path.join(os.getcwd(),"testing_scripts/tests.json"))
target_lemmas = get_dict(os.path.join(os.getcwd(),"testing_scripts/target_lemmas.json"))
grouped_tests = get_dict(os.path.join(os.getcwd(),"testing_scripts/groups.json"))

def test_folder(suite):
    return os.path.join(os.getcwd(),test_folder_dictionary[suite])

def get_test_file(info):
    if info["location"] == "":
        return info["target"]
    else:
        location = info["location"]
        target = info["target"]
        return f"{location}_by_{target}"

def tests_from_suite(suite):
    return list(map(get_test_file,test_dictionary[suite]))

def get_target(info):
    if info["target"] in target_lemmas:
        return target_lemmas[info["target"]]
    else:
        for i in range(10):
            suffix = "_" + str(i)
            removed = remove_suffix(info["target"],(suffix))
            if removed in target_lemmas:
                return target_lemmas[removed]
        return None
    
def run_test(suite,test):
    suite_cleaned = suite
    for i in range(20):
        suite_cleaned = remove_suffix(suite_cleaned,f"_{i}")
    folder = test_folder(suite_cleaned)
    cmd = f"cd {folder} && coqc {test}.v"
    result = subprocess.check_output(cmd, shell=True, text=True)
    print(result)

def run_tests(suite,tests):
    results = []
    for t in tests:
        r = run_test(suite,t)
        splits = t.split("_by_")
        location = splits[0].strip()
        target = splits[1].strip() if len(splits) == 2 else splits[0].strip()
        results += [(t,get_target({"location" : location, "target" : target}),r)]
    return results

def run_suite(suite):
    tests = tests_from_suite(suite)
    results = run_tests(suite,tests)
    return (suite,results)

def run_group(group):
    tests = grouped_tests[group]
    suite = group
    for i in range(20):
        suite = remove_suffix(suite,f"_{i}")
    results = run_tests(suite,tests)
    return (suite,results)

def display(label,results):
    print(label)
    print(results)
    for test_label,target,r in results:
        print(f"Test: {test_label}")
        print(f"Target: {target}")
        processed = r.split("-------------------- RESULTS --------------------")
        final = processed[1] if len(processed) == 2 else ""
        print(final)

def main():
    if len(sys.argv) == 2:
        suite = sys.argv[1]
        results = run_suite(suite)
        display(suite,results)
    elif len(sys.argv) == 3:
        assert "group" == sys.argv[1]
        group = sys.argv[2]
        results = run_group(group)
        display(group,results)
    else:
        for suite in test_dictionary:
            suite = sys.argv[1]
            results = run_suite(suite)
            display(suite,results)

if __name__ == "__main__":
    main()