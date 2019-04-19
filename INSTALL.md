 
https://developer.fedoraproject.org/tech/languages/haskell/haskell-installation.html

sudo dnf copr enable petersen/stack
sudo dnf -y install stack git ncurses-devel zlib-devel texlive-bbm texlive-bbm-macros texlive-yfonts texlive-prftree texlive-bussproofs texlive-cleveref texlive-xargs texlive-todonotes
stack upgrade

git clone https://github.com/agda/agda
cd agda 

cp stack-8.6.4.yaml stack.yaml

# dnf provides \*libtinfo.so


stack setup && stack build
