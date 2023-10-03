# FGJ-inference

This is an implementation of a global type inference algorithm for Featherweight Generic Java.

A Featherweight Generic Java program only needs type annotation in class headers and for fields.

A formal definition and a description of this implementation can be found [here](https://github.com/timpehoerig/Thesis/blob/main/thesis/thesis.pdf).

## Usage

The entrypoint to this package is the `FGJ_GT`.

*DISCLAIMER: You may have to change `FGJ_GT` or `./FGJ_GT.py` to the full path. And/or change it so it fits your os.

### Command line

You can use the command line to execute the type inference algorithm directly on a file.

```shell
usage: python3 ./FGJ_GT.py [-h] [-o] inpath [outpath]
```

positional arguments:

    inpath             The file your FGJ program is in.
    outpath            The file the output is printed in. If none given, the output is printed into the infile.

options:

    -h, --help         Show the help message and exit
    -o, --outpath      Print the output to the terminal.

To see the usage at anytime use:
```shell
$ python3 ./FGJ_GT.py --help
```
