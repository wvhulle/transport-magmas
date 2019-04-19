There are no prec-compiled binaries for the latest versions of the libraries used. These have to be compiled from source.

# Fedora

## Install the Haskell ecosystem
Based on: https://developer.fedoraproject.org/tech/languages/haskell/haskell-installation.html
`sudo dnf copr enable petersen/stack`

Install binaries:
`sudo dnf -y install stack git ncurses-devel zlib-devel emacs && stack upgrade`

## Compile Agda 

`cd` to a fixed directory called `$ROOT` that does not change location.
Download the source code:
`git clone https://github.com/agda/agda && cd agda``

Compile with GHC 8.6.4
`cp stack-8.6.4.yaml stack.yaml && stack setup && stack build`

If this halts, try to find the necessary binaries first such as:
`dnf provides "\*libtinfo.so"`.

Add the directory of the generated `agda` and `agda-mode` to your path in your shell's config file. They may be located in:
`$ROOT/agda/.stack-work/install/x86_64-linux-tinfo6/lts-13.16/8.6.4/bin/`

Reload your shell's config file, for example with:
`source ~/.bashrc`

Test the following command:
`agda --version`

Configure emacs:
`agda-mode setup`


## Install libraries

Go back to the fixed root directory `$ROOT` with `cd ..`
Download the source code with:
`git clone https://github.com/agda/agda-stdlib.git && cd agda-stdlib && git checkout v1.0`

Optionally do `cabal install`

Go back to `$ROOT` with `cd ..`.

Download cubical library with
`git clone https://github.com/agda/cubical`

Prepare the code with:
`cd cubical && make && cd ..`
  
Make the libraries importable by agda making a file `$HOME/.agda/libraries` with contents
```
$ROOT/agda-stdlib/standard-library.agda-lib
$ROOT/cubical/cubical.agda-lib
```

A file `$HOME/.agda/defaults` with contents:
```
standard-library
cubical
```



