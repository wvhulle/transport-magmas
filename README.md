# Transport of magmas (with univalence)

This repository contains Agda code in which an application of univalence is explored.
See INSTALL.md for installation instructions.

Structure of the code:
 - Imports of the standard Agda library and the Cubical library.
 - Definition of two magmas, a simple kind of algebraic structure, with setoids.
 - A proof of equivalence between the carrier sets.
 - Univalence from cubical type theory is used to define an equality term, a path.
 - A proof of a property for one of the structures is transported to the other structure.