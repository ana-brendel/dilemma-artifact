import os
import json
import subprocess

def get_dict(path):
    with open(path) as tf:
        return json.load(tf) 
    
test_folder_dictionary = get_dict(os.path.join(os.getcwd(),"testing_scripts/test_folders.json"))
test_dictionary = get_dict(os.path.join(os.getcwd(),"testing_scripts/tests.json"))
target_lemmas = get_dict(os.path.join(os.getcwd(),"testing_scripts/target_lemmas.json"))
grouped_tests = get_dict(os.path.join(os.getcwd(),"testing_scripts/groups.json"))

def test_folder(suite):
    return os.path.join(os.getcwd(),test_folder_dictionary[suite])

def get_test_file(info):
    if info["location"] == "":
        return info["target"] + ".v"
    else:
        location = info["location"]
        target = info["target"]
        return f"{location}_by_{target}.v"

def tests_from_suite(suite):
    return list(map(get_test_file,test_dictionary[suite]))

def get_target(info):
    if info["target"] in target_lemmas:
        return target_lemmas[info["target"]]
    else:
        for i in range(10):
            suffix = "_" + str(i)
            removed = info["target"].removesuffix(suffix)
            if removed in target_lemmas:
                return target_lemmas[removed]
        return None
    
def run_test(suite,test):
    suite_cleaned = suite
    for i in range(20):
        suite_cleaned = suite_cleaned.removesuffix(f"_{i}")
    folder = test_folder(suite_cleaned)
    cmd = f"cd {folder} && coqc {test}.v"
    result = subprocess.check_output(cmd, shell=True, text=True)
    print(result)