# coq-min-imports
Script to remove unnecessary package imports from Coq module

Usage: coq_min_imports <coq_flags> [-cmi-verbose] [-cmi-replace] [-cmi-wrap] <files...>

where

    <coq_flags> - any of optoins supported by 'coqc'
    <files> - list of .v files to process
    -cmi-verbose - enable verbose reporting
    -cmi-replace - replace processed files with optmized version (orignals are saved with ".bak" suffix). Otherwise optimized version is written as a new file with the same name as input but adding ".new" suffix.
    -cmi-wrap - run in a compiler wrapper mode, compiling the files as the side-effect


Author: Vadim Zaliva <lord@crocodile.org>
