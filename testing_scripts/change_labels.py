import os

read = lambda x: open(x, "r").read().split("\n")

def write(file,content):
    f = open(file, "w")
    f.write(content)
    f.close()

benchmark_folder = "/Users/anabrendel/Desktop/dilemma-docker/dilemma-artifact/benchmarks"

folders_with_tests =["/Users/anabrendel/Desktop/dilemma-docker/dilemma-artifact/benchmarks/lia/implications/tests"]

for suite in os.listdir(benchmark_folder):
    if suite.startswith("vfa") or suite == "lia" or suite == "clam":
        test_suite = os.path.join(benchmark_folder,suite)
        for test in os.listdir(test_suite):
            if test == "tests" or test == "atomic" or test == "implication":
                full_test = os.path.join(test_suite,test)
                folders_with_tests.append(full_test)

dilemma = "From Dilemma Require Import Dilemma."
findlemma = "From LFindToo Require Import LFindToo."

findlemma_tactic = "findlemma."
dilemma_tactic = "dilemma."

def replace(path):
    content = read(path)
    new_content = []
    for line in content:
        if line == findlemma:
            new_content.append(dilemma)
        elif line.__contains__(findlemma_tactic):
            new_line = line.replace(findlemma_tactic,dilemma_tactic)
            new_content.append(new_line)
        else:
            new_content.append(line)
    new_file_content = "\n".join(new_content)
    write(path,new_file_content)

def replace_all():
    for test_folder in folders_with_tests:
        for test in os.listdir(test_folder):
            assert test.endswith(".v")
            full_test = os.path.join(test_folder,test)
            replace(full_test)

replace_all()