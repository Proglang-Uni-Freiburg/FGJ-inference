import FGJ_AST as FGJ

from FGJ_parser import fgj_parse

import argparse
import sys


def read_from(file_path: str) -> FGJ.Program:
    with open(file_path, "r") as file:
        return fgj_parse(file.read())


def run(file_path: str, out_file_path: str, to_stdout: bool):
    program = read_from(file_path)
    if to_stdout:
        print(program)
    else:
        with open(out_file_path, "w") as file:
            file.write(program)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        prog="python ./FGJ_run.py",
        description="work in progress."
    )

    parser.add_argument("inpath", help="The file your FGJ program is in.")
    parser.add_argument("outpath", nargs="?", help="The file the output is printed in. If none given, the output is printed into the infile.")
    parser.add_argument("-o", "--outpath", action="store_true", help="Print the output to the terminal.")

    options = parser.parse_args(sys.argv[1:])

    run(options.inpath, options.outpath or options.inpath, options.outpath)
