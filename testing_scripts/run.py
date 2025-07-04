import os
import json
import subprocess
import sys

def write(file,content):
    f = open(file, "w")
    f.write(content)
    f.close()

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
group_updated_tests = get_dict(os.path.join(os.getcwd(),"testing_scripts/groups_updated.json"))

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
    try:
        result = subprocess.check_output(cmd, shell=True, text=True)
        return result
    except:
        return ""

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

def run_group_updated(group):
    tests = group_updated_tests[group]
    suite = group
    for i in range(20):
        suite = remove_suffix(suite,f"_{i}")
    results = run_tests(suite,tests)
    return (suite,results)

def display(label,results):
    contents = []
    (suite,result_list) = results
    assert label.startswith(suite)
    for (test_label,target,r) in result_list:
        contents.append("--------------------------------------------------------")
        contents.append(f"Test: {test_label}")
        contents.append(f"Target: {target}")
        processed = r.split("-------------------- RESULTS --------------------")
        final = processed[1] if len(processed) == 2 else ""
        contents.append(final)
        contents.append("--------------------------------------------------------")
        contents.append("")
    return "\n".join(contents)

def create_file(label,contents):
    file = os.path.join(os.path.join(os.getcwd(),"results"),label) + ".txt"
    write (file,contents)

def main():
    if len(sys.argv) == 2:
        suite = sys.argv[1]
        results = run_suite(suite)
        contents = display(suite,results)
        label = f"suite_{suite}"
        create_file(label,contents)
    elif len(sys.argv) == 3:
        assert "group" == sys.argv[1]
        group = sys.argv[2]
        results = run_group(group)
        contents = display(group,results)
        label = f"group_{group}"
        create_file(label,contents)
    elif len(sys.argv) == 3:
        assert "group_updated" == sys.argv[1]
        group = sys.argv[2]
        results = run_group_updated(group)
        contents = display(group,results)
        label = f"group_updated_{group}"
        create_file(label,contents)
    else:
        for suite in test_dictionary:
            suite = sys.argv[1]
            results = run_suite(suite)
            contents = display(suite,results)
            label = f"suite_{suite}"
            create_file(label,contents)

if __name__ == "__main__":
    main()