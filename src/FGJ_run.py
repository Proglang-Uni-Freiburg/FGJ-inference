import argparse
import sys

import FGJ_AST as FGJ

from FGJ_parser import fgj_parse
from FGJ_GT import TypeInference


def read_from(file_path: str) -> FGJ.Program:
    with open(file_path, "r") as file:
        return fgj_parse(file.read())


def run(file_path: str, out_file_path: str, to_stdout: bool):
    program = read_from(file_path)
    if to_stdout:
        print(program)
        print()
        d = TypeInference(dict(), 0, program.CT)

        for (ch, m), mss in d.items():
            print(ch, m, ":")
            for ms in mss:
                print(ms)
    else:
        with open(out_file_path, "w") as file:
            file.write(str(program))
            file.write("\n")
            d = TypeInference(dict(), 0, program.CT)

            for (ch, m), mss in d.items():
                file.write(f"\n{ch} {m}:\n")
                for ms in mss:
                    file.write("\t" + str(ms))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        prog="python ./FGJ_run.py",
        description="work in progress."
    )

    parser.add_argument("inpath", help="The file your FGJ program is in.")
    parser.add_argument("outpath", nargs="?", help="The file the output is printed in. If none given, the output is printed into the infile.")
    parser.add_argument("-o", "--out", action="store_true", help="Print the output to the terminal.")

    options = parser.parse_args(sys.argv[1:])
    print(options)

    run(options.inpath, options.outpath or options.inpath, options.out)
