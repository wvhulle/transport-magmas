There are no pre-compiled binaries for the latest versions of the libraries used for Ubuntu or Fedora. The libraries are also in constant development. For optimal results, these have to be compiled from source together with the latest development Agda compiler.

# Install the Haskell ecosystem 

## Fedora  
Based on: https://developer.fedoraproject.org/tech/languages/haskell/haskell-installation.html

Enable the stack repository:
`sudo dnf copr enable petersen/stack`


Install pre-compiled distro-specific binaries:
```
sudo dnf -y install stack git ncurses-devel zlib-devel emacs && stack upgrade
```

## Ubuntu

Install stack with the online bash script:
```
curl -sSL https://get.haskellstack.org/ | sh
```

Install pre-compiled distro-specific  binaries as before but now with `apt`.

# Compilation step

`cd` to a fixed directory called `$ROOT` that does not change location.

## Compile Agda 


Download the source code:
```
git clone https://github.com/agda/agda && cd agda
```

Compile with GHC 8.6.4
```
cp stack-8.6.4.yaml stack.yaml && stack setup && stack build
```

If this halts, try to find the necessary binaries first such as:
```
dnf provides "\*libtinfo.so"` or `apt search "libtinfo
```

Add the directory of the generated `agda` and `agda-mode` to your path in your shell's config file. They may be located in:
```
$ROOT/agda/.stack-work/install/x86_64-linux-tinfo6/lts-13.16/8.6.4/bin/
```

Reload your shell's config file, for example with:
```
source ~/.bashrc
```

Test the following command:
```agda --version
```

Configure emacs:
```
agda-mode setup
```

Go back to the fixed root directory `$ROOT` with `cd ..`


## Install libraries


### The standard library

Download the source code with:
```
git clone https://github.com/agda/agda-stdlib.git && cd agda-stdlib && git checkout v1.0
```

Optionally do `cabal install`

Go back to `$ROOT` with `cd ..`.

### The cubical library

Download cubical library with
```
git clone https://github.com/agda/cubical
```

Prepare the code with:
```
cd cubical && make && cd ..
```
  
Make the libraries importable by agda making a file `$HOME/.agda/libraries` with contents
```
$ROOT/agda-stdlib/standard-library.agda-lib
$ROOT/cubical/cubical.agda-lib
```

Make a file `$HOME/.agda/defaults` with the following contents:
```
standard-library
cubical
```


