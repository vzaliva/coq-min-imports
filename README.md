# coq-min-imports
Script to remove unnecessary package imports from _Coq_ sources

## Usage: 

    coq_min_imports <coq_flags> [-cmi-verbose] [-cmi-replace] [-cmi-wrap] <files...>

where

* *__&lt;coq_flags>__* - any of optoins supported by *'coqc'*
* *__&lt;files>__* - list of *.v* files to process
* __-cmi-verbose__ - enable verbose reporting
* __-cmi-replace__ - replace processed files with optmized version (orignals are saved with the *".bak"* suffix). Otherwise optimized version is written as a new file with the same name as input but adding *".new"* suffix.
* __-cmi-wrap__ - run in a compiler wrapper mode, compiling the files as the side-effect


## Author

Vadim Zaliva <lord@crocodile.org>
