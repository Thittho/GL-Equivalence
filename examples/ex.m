// Verbose flag "Equivalence" can be set to 0 (lowest), 1 or 2 (highest)
SetVerbose("Equivalence", 1);

// General examples, polynomials which are constructed to be equivalent
// In 2 variables 
// Polynomials of degree 50
R<x,y> := PolynomialRing(Rationals(), 2);
f := &+[Random(10,20)*m : m in MonomialsOfDegree(R, 50)];
M := Random(1,100)*ChangeRing(RandomSLnZ(2, 20, 20), Rationals());
g := Random(1,100)*f^M;
time IsGL2EquivalentFast(f, g);


// In 3 variables
// Polynomials of degree 6
R<x,y,z> := PolynomialRing(Rationals(), 3);
f := &+[Random(10,20)*m : m in MonomialsOfDegree(R, 6)];
M := Random(1,100)/Random(1,100)*ChangeRing(RandomSLnZ(3, 20, 20), Rationals());
g := Random(1,100)/Random(1,100)*f^M;
time IsGL3EquivalentFast(f, g);

// In 3 variables
// Polynomials of degree 13
R<x,y,z> := PolynomialRing(Rationals(), 3);
f := &+[Random(10,20)*m : m in MonomialsOfDegree(R, 13)];
M := Random(1,100)/Random(1,100)*ChangeRing(RandomSLnZ(3, 20, 20), Rationals());
g := Random(1,100)/Random(1,100)*f^M;
time IsGL3EquivalentFast(f, g);


// In 4 variables
// Polynomials of degree 3
R<x,y,z,t> := PolynomialRing(Rationals(), 4);
f := &+[Random(10,20)*m : m in MonomialsOfDegree(R, 3)];
M := Random(1,100)/Random(1,100)*ChangeRing(RandomSLnZ(4, 20, 20), Rationals());
g := Random(1,100)/Random(1,100)*f^M;
time IsGL4EquivalentFast(f, g);

// In 4 variables
// Polynomials of degree 4
R<x,y,z,t> := PolynomialRing(Rationals(), 4);
f := &+[Random(10,20)*m : m in MonomialsOfDegree(R, 4)];
M := Random(1,100)/Random(1,100)*ChangeRing(RandomSLnZ(4, 20, 20), Rationals());
g := Random(1,100)/Random(1,100)*f^M;
time IsGL4EquivalentFast(f, g);

// In 4 variables
// Polynomials of degree 5
R<x,y,z,t> := PolynomialRing(Rationals(), 4);
f := &+[Random(10,20)*m : m in MonomialsOfDegree(R, 5)];
M := Random(1,100)/Random(1,100)*ChangeRing(RandomSLnZ(4, 20, 20), Rationals());
g := Random(1,100)/Random(1,100)*f^M;
time IsGL4EquivalentFast(f, g);



// Curves that are geometrically isomorphic
R<x,y,z> := PolynomialRing(GF(19), 3);                                                                                                                   
f := x^4 + y^4 + z^4;
g := x^4 + 2*x^3*y + 4*x^3*z + 14*x^2*y^2 + 18*x^2*y*z + 16*x^2*z^2 + 15*x*y^3 + 16*x*y^2*z + 10*x*y*z^2 + 17*x*z^3 + 10*y^4 + 16*y^3*z + 3*y^2*z^2 + 4*y*z^3 + 12*z^4;
// this will return false, as the curves are not isomorphic over the base field
IsGLnEquivalent(f, g);

// this will return true, as the curves are geometrically isomorphic
IsGLnEquivalent(f, g : geometric := true);


// General case, two isomorphic 
R<x,y,z> := PolynomialRing(GF(19), 3);
f := 14*x^13*y + 16*x^13*z + 3*x^12*y^2 + 18*x^12*y*z + 2*x^12*z^2 + 15*x^11*y^3 + 5*x^11*y^2*z + 3*x^11*y*z^2 + 5*x^11*z^3 + 15*x^10*y^4 + 4*x^10*y^3*z + 17*x^10*y^2*z^2 + 2*x^10*y*z^3 + 5*x^10*z^4 + 15*x^9*y^5 + 3*x^9*y^4*z + 14*x^9*y^3*z^2 + 16*x^9*y^2*z^3 + x^9*y*z^4 + 18*x^9*z^5 + 15*x^8*y^6 + x^8*y^5*z + 15*x^8*y^4*z^2 + 4*x^8*y^3*z^3 + 3*x^8*y^2*z^4 + 17*x^8*y*z^5 + 2*x^8*z^6 + 3*x^7*y^7 + 17*x^7*y^4*z^3 + 15*x^7*y^3*z^4 + 4*x^7*y^2*z^5 + 4*x^7*z^7 + 17*x^6*y^8 + 4*x^6*y^7*z + 3*x^6*y^6*z^2 + 14*x^6*y^5*z^3 + 16*x^6*y^4*z^4 + 16*x^6*y^3*z^5 + 17*x^6*y^2*z^6 + 5*x^6*y*z^7 + x^6*z^8 + 2*x^5*y^9 + 2*x^5*y^8*z + 4*x^5*y^7*z^2 + 18*x^5*y^6*z^3 + x^5*y^4*z^5 + 5*x^5*y^2*z^7 + 16*x^5*y*z^8 + x^5*z^9 + 5*x^4*y^10 + 18*x^4*y^8*z^2 + 14*x^4*y^7*z^3 + x^4*y^6*z^4 + 15*x^4*y^5*z^5 + 3*x^4*y^4*z^6 + x^4*y^3*z^7 + 18*x^4*y^2*z^8 + 2*x^4*z^10 + x^3*y^11 + 15*x^3*y^10*z + 14*x^3*y^9*z^2 + 15*x^3*y^7*z^4 + 14*x^3*y^6*z^5 + 16*x^3*y^5*z^6 + 16*x^3*y^4*z^7 + 17*x^3*y^3*z^8 + 3*x^3*y^2*z^9 + 4*x^3*y*z^10 + 17*x^2*y^12 + 4*x^2*y^11*z + 17*x^2*y^10*z^2 + 3*x^2*y^9*z^3 + 3*x^2*y^8*z^4 + 18*x^2*y^7*z^5 + 18*x^2*y^6*z^6 + 18*x^2*y^5*z^7 + 3*x^2*y^4*z^8 + x^2*y^3*z^9 + 2*x^2*y^2*z^10 + 15*x^2*y*z^11 + 4*x^2*z^12 + 2*x*y^12*z + 5*x*y^11*z^2 + x*y^10*z^3 + 4*x*y^9*z^4 + 17*x*y^8*z^5 + 14*x*y^7*z^6 + 4*x*y^6*z^7 + 16*x*y^5*z^8 + 3*x*y^4*z^9 + x*y^3*z^10 + 15*x*y^2*z^11 + 5*x*y*z^12 + 5*x*z^13 + 2*y^14 + 3*y^13*z + 5*y^12*z^2 + 2*y^11*z^3 + y^10*z^4 + 4*y^8*z^6 + 16*y^7*z^7 + 15*y^6*z^8 + 3*y^5*z^9 + 16*y^4*z^10 + 18*y^2*z^12 + 3*y*z^13 + 14*z^14;
g := 4*x^14 + x^13*y + 14*x^13*z + 17*x^12*y^2 + 12*x^12*y*z + 11*x^11*y^3 + 9*x^11*y^2*z + 5*x^11*y*z^2 + 6*x^11*z^3 + 12*x^10*y^4 + 6*x^10*y^3*z + 16*x^10*y^2*z^2 + 5*x^10*y*z^3 + 10*x^10*z^4 + 10*x^9*y^5 + 11*x^9*y^4*z + 10*x^9*y^3*z^2 + 12*x^9*y^2*z^3 + 15*x^9*z^5 + 3*x^8*y^6 + 12*x^8*y^5*z + 16*x^8*y^4*z^2 + 3*x^8*y^3*z^3 + x^8*y^2*z^4 + 17*x^8*y*z^5 + 9*x^8*z^6 + 8*x^7*y^7 + 12*x^7*y^6*z + 9*x^7*y^5*z^2 + 10*x^7*y^2*z^5 + 8*x^7*y*z^6 + 4*x^7*z^7 + 17*x^6*y^8 + 18*x^6*y^7*z + 9*x^6*y^6*z^2 + 16*x^6*y^5*z^3 + 17*x^6*y^4*z^4 + 17*x^6*y^3*z^5 + 14*x^6*y^2*z^6 + 11*x^6*y*z^7 + 4*x^5*y^9 + 2*x^5*y^8*z + 4*x^5*y^7*z^2 + x^5*y^6*z^3 + 14*x^5*y^5*z^4 + 13*x^5*y^4*z^5 + 18*x^5*y^3*z^6 + 11*x^5*y^2*z^7 + 7*x^5*y*z^8 + 15*x^5*z^9 + 17*x^4*y^10 + 15*x^4*y^9*z + x^4*y^8*z^2 + 3*x^4*y^7*z^3 + 6*x^4*y^6*z^4 + 6*x^4*y^5*z^5 + 13*x^4*y^4*z^6 + 18*x^4*y^3*z^7 + 16*x^4*y^2*z^8 + x^4*y*z^9 + 12*x^4*z^10 + 9*x^3*y^11 + 9*x^3*y^10*z + 15*x^3*y^9*z^2 + 8*x^3*y^8*z^3 + 11*x^3*y^7*z^4 + 3*x^3*y^6*z^5 + x^3*y^5*z^6 + 14*x^3*y^4*z^7 + 12*x^3*y^2*z^9 + 5*x^3*y*z^10 + 10*x^3*z^11 + 13*x^2*y^12 + 15*x^2*y^11*z + 12*x^2*y^9*z^3 + 3*x^2*y^7*z^5 + 16*x^2*y^6*z^6 + 7*x^2*y^5*z^7 + 11*x^2*y^4*z^8 + 8*x^2*y^3*z^9 + 9*x^2*y^2*z^10 + 17*x^2*y*z^11 + 11*x^2*z^12 + 18*x*y^13 + 17*x*y^12*z + x*y^11*z^2 + 12*x*y^10*z^3 + 3*x*y^9*z^4 + 7*x*y^8*z^5 + 8*x*y^7*z^6 + 13*x*y^6*z^7 + 4*x*y^5*z^8 + 13*x*y^4*z^9 + 7*x*y^3*z^10 + 3*x*y^2*z^11 + 15*x*y*z^12 + 14*x*z^13 + 8*y^14 + 7*y^13*z + 10*y^12*z^2 + 15*y^11*z^3 + 17*y^10*z^4 + 10*y^9*z^5 + 11*y^8*z^6 + y^7*z^7 + 3*y^6*z^8 + 6*y^5*z^9 + 5*y^4*z^10 + 7*y^3*z^11 + 5*y^2*z^12 + 5*y*z^13 + 2*z^14;
IsGLnEquivalent(f, g);



