# Transport of magmas (with univalence)

This repository contains Agda code in which an application of univalence is explored.
See [INSTALL](INSTALL.md) for installation instructions.

Structure of the code:
 - Imports of the standard Agda library and the Cubical library.
 - Definition of two magmas, a simple kind of algebraic structure, with setoids.
 - A proof of equivalence between the carrier sets.
 - Univalence from cubical type theory is used to define an equality term, a path.
 - A proof of a property for one of the structures is transported to the other structure.
 
 
 
 ## How to read this code
 
 Follow the installation instructions and open the file `PropertyTransports.agda` in emacs.
 1. Press `control-{c l}` to typecheck the code.
 2. Normalize the transport property with `control-{c n}`.
 3. Middle mouse click on identifiers to view definitions.
