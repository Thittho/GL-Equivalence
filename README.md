Description 
--

This Magma repository helps with the fast computation of linear transformation between homogeneous polynomials. It is linked to the paper Thomas Bouchet, Reynald Lercier, Jeroen Sijsling, Christophe Ritzenthaler, [_Functionality for isomorphism classes of curves and hypersurfaces, 2026_](https://arxiv.org/abs/2102.04372)

Prerequisites
--

You need an installation of Magma on your machine. Most functions should be compatible with older versions of Magma.

Installation
--

You can enable the functionality of this package in Magma by attaching the GL-Equivalence/magma/spec file with AttachSpec. To make this independent of the directory in which you find yourself, and to active this on startup by default, you may want to indicate the relative path in your `~/.magmarc file`, by adding a line like
```
AttachSpec("~/GL-Equivalence/magma/spec");
```

Usage
--

Examples that test the routines in this package can be found in the directory
[`examples`](examples) (a full list of intrinsics is [here](intrinsics.md)).

```
Citing this work
--

If this repository was helpful to your research, please cite the following article:
Thomas Bouchet, Reynald Lercier, Jeroen Sijsling, Christophe Ritzenthaler, [_Functionality for isomorphism classes of curves and hypersurfaces, 2026_](https://arxiv.org/abs/2102.04372)

Credit
--

The skeleton of this README file was copied from [https://github.com/JRSijsling/quartic/blob/main/README.md](https://github.com/JRSijsling/quartic/blob/main/README.md)