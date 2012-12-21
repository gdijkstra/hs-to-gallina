Translating Haskell code to Gallina
===================================

HsToGallina is a tool to assist in translating Haskell programs to Coq
programs.

## Building the tool ##

We expect that UUAGC has already been installed. If this is the case
then running `make` in the top directory suffices. The executable can
be then found in the "dist" directory. Also make sure that the
"lib/Prelude.v" has been compiled with `coqc` and that the directory
is in Coq's include paths.

## Using the tool ##

    Usage: HsToGallina -f FILE [OPTION...]
      -V, -?    --version                      show version number
      -w[FILE]  --write output to file[=FILE]  output FILE
      -e[FILE]  --extract[=FILE]               output FILE
      -f FILE   --file=FILE                    input FILE

The tool defaults to `FILE.v` as the file to write the Coq script to
and to `extracted/FILE.hs` as the file to extract to.

See the report for more information on what features the tool has and
how they can be used.
