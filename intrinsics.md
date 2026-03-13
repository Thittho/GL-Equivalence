### Auxiliary intrinsics

```
intrinsic Hessian(f::RngMPolElt) -> RngMPolElt
intrinsic DPairing(P::RngMPolElt, Q::RngMPolElt) ->  RngMPolElt
intrinsic TransvectantGeneral(polys::SeqEnum[RngMPolElt], l::RngIntElt : normalize := false) -> RngMPolElt
intrinsic DualSurf(f::RngMPolElt) -> RngMPolElt
```

### Fast isomorphism intrinsics

```
intrinsic IsGL2EquivalentFast(f::RngMPolElt, g::RngMPolElt) -> BoolElt, AlgMatElt
intrinsic IsGL3EquivalentFast(f::RngMPolElt, g::RngMPolElt) -> BoolElt, AlgMatElt
intrinsic IsGL4EquivalentFast(f::RngMPolElt, g::RngMPolElt) -> BoolElt, AlgMatElt
```

### All generality isomorphism intrinsics

```
intrinsic IsGLnEquivalentNaive(f::RngMPolElt, g::RngMPolElt : geometric := false) -> .
intrinsic IsGLnEquivalent(f::RngMPolElt, g::RngMPolElt : geometric := false) -> .
```

### Certificate intrinsics for no geometric automorphisms

```
intrinsic FastAutosGL2(f::RngMPolElt) -> BoolElt
intrinsic FastAutosGL3(f::RngMPolElt) -> BoolElt
intrinsic FastAutosGL4(f::RngMPolElt) -> BoolElt
```