/*
 *  Linear equivalence between homogeneous polynomials 
 *
 *  Thomas Bouchet
 *
 *  See LICENSE.txt for license details.
*/

import "tools_iso.m":
    FindPreImage, XGCDUnique, NormalizeMatrix; 

import "GL3_equivalence.m":
    DualTernaryForm;

//////////////////////////////////////////////////////////////////////////
//////////////////////// some auxiliary functions ////////////////////////
//////////////////////////////////////////////////////////////////////////

// Return the S invariant of a ternary cubic
// Copied from Geometry/SrfDP/inv_cub_surf.m
function S_plane_curve(f)
 r0 := BaseRing(Parent(f));
 r12 := PolynomialRing(r0,12); 
 fac := [Evaluate(f,[r12.(i+3*j) : i in [1..3]]) : j in [0..3]];

/* Apply (123) */ 
 res1 := Derivative(fac[1],1) * (Derivative(fac[2],5)*Derivative(fac[3],9) 
                                -Derivative(fac[2],6)*Derivative(fac[3],8))
       - Derivative(fac[1],2) * (Derivative(fac[2],4)*Derivative(fac[3],9)
                                -Derivative(fac[2],6)*Derivative(fac[3],7))
       + Derivative(fac[1],3) * (Derivative(fac[2],4)*Derivative(fac[3],8)
                                -Derivative(fac[2],5)*Derivative(fac[3],7));
/* 120 Terms in res1 */

/* Apply (234) */
 t1 := Derivative(res1,4); t2 := Derivative(res1,5); t3 := Derivative(res1,6);
 res2 := Derivative(fac[4],10) * (Derivative(t2,9) - Derivative(t3,8))
       - Derivative(fac[4],11) * (Derivative(t1,9) - Derivative(t3,7))
       + Derivative(fac[4],12) * (Derivative(t1,8) - Derivative(t2,7));
/* 324 Terms in res2 */

/* Apply (341) */
 t1 := Derivative(res2,7); t2 := Derivative(res2,8); t3 := Derivative(res2,9);
 res3 := Derivative(Derivative(t1,11),3) - Derivative(Derivative(t1,12),2)
       - Derivative(Derivative(t2,10),3) + Derivative(Derivative(t2,12),1)
       + Derivative(Derivative(t3,10),2) - Derivative(Derivative(t3,11),1); 
/* 6 Terms in res3 */

/* Apply (412) */
 t1 := Derivative(res3,10); t2 := Derivative(res3,11); t3 := Derivative(res3,12);
 res4 := Derivative(Derivative(t1,2),6) - Derivative(Derivative(t1,3),5)
       - Derivative(Derivative(t2,1),6) + Derivative(Derivative(t2,3),4)
       + Derivative(Derivative(t3,1),5) - Derivative(Derivative(t3,2),4);

 return MonomialCoefficient(res4,1);
end function;

function DualCubicSurf(f) // by default the invariant chosen is the transvectant of the form with itself or something similar
    R := Parent(f);
    Rt := PolynomialRing(R, Rank(R)-1); 

    ft := Rt!Evaluate(f, [Rt.i : i in [1..Rank(R)-1]] cat [&+[-Rt.i*R.i : i in [1..Rank(R)-1]]]);
    ft := Homogenization(R!S_plane_curve(ft), R.Rank(R));
    return ft;
end function;

// Return a contravariant associated to f 
intrinsic DualSurf(f::RngMPolElt) -> RngMPolElt
    {
        Return a contravariant associated to the homogeneous polynomial in 4 variables f
    }

    require IsHomogeneous(f) : "f must be homogeneous";
    require Rank(Parent(f)) eq 4 : " f must be a polynomial in 4 variables";

    if Degree(f) eq 3 then
        return DualCubicSurf(f);
    end if;

    R := Parent(f);
    Rt := PolynomialRing(R, Rank(R)-1); 

    ft := Rt!Evaluate(f, [Rt.i : i in [1..Rank(R)-1]] cat [&+[-Rt.i*R.i : i in [1..Rank(R)-1]]]);
    dual := DualTernaryForm(ft);
    if Degree(f) mod 2 eq 0 then
        return Homogenization(R!DPairing(dual, ft), R.Rank(R));
    else
        return Homogenization(R!DPairing(dual, ft^2), R.Rank(R));    
    end if;
end intrinsic;

/////////////////////////////////////////////////////////////////
//////////////////////// some invariants ////////////////////////
/////////////////////////////////////////////////////////////////


function SomeInvariantsQuadricSurfaces(L, wgt)
    return [BaseRing(Universe(L)) | TransvectantGeneral([L[1], L[2], L[3], L[i]], 2 : normalize := true) : i in [4..10]], [wgt[1]+wgt[2]+wgt[3]+wgt[i] : i in [4..10]];
end function;

function SomeInvariantsQuarticSurfaces(L, wgt)
    return [BaseRing(Universe(L)) | TransvectantGeneral([L[1], L[2], L[3], L[i]], 4 : normalize := true) : i in [4..15]], 
    [28, 28, 28, 32, 43, 47, 47, 51, 47, 51, 51, 51];//, 55, 51, 55, 55, 55, 59, 59, 59, 55, 59, 55, 59, 59, 59, 63, 63, 63, 63, 67, 67];
end function;

function SCInvariants(f)
    invs := ClebschSalmonInvariants(f);
    return invs, [8, 16, 24, 32, 40];
end function;


/////////////////////////////////////////////////////////////////////////
//////////////////////// defining all covariants ////////////////////////
/////////////////////////////////////////////////////////////////////////

// Return a covariant of order 3 of f, when the degree of f is not divisible by 2
function CubicCov(f)
    assert f ne 0;
    d := Degree(f);
    assert d in [3, 5, 7]; 
    if d eq 3 then
        return f;
    elif d eq 5 then
        c := TransvectantGeneral([f, f, f, f], 4 : normalize := true);
        C := DualSurf(c);
        return DPairing(C^3, f^3);
    elif d eq 7 then
        c := TransvectantGeneral([f, f, f, f], 6 : normalize := true);
        C := DualSurf(c);
        return DPairing(C, f);
    end if;
end function;

// Return a covariant of order 4 of f, when the degree of f is divisible by 4
function QuarticCov(f)
    d := Degree(f);
    assert d in [4, 8];
    if d eq 4 then 
        return f;
    elif d eq 8 then
        dual := DualSurf(f);
        c1 := DPairing(dual, f^2);
        C := DPairing(f, dual^2);
        dualc1 := DualSurf(c1);
        c2 := DPairing(C, f^2);
        c3 := DPairing(dualc1, f^2);
        t := TransvectantGeneral([f, c1, c2, c3], 1 : normalize := true);
        return DPairing(dual^3, t);
    end if;
end function;

// Return a covariant of order 6 of f, when the degree of f is divisible by 2 but not by 4
function SexticCov(f)
    d := Degree(f);
    assert d in [6];
    if d eq 6 then
        return f;
    end if;
end function;

function SmallOrderCovariant(f)
    d := Degree(f);
    if d mod 4 eq 0 then
        return QuarticCov(f);
    elif d mod 2 eq 0 then
        return SexticCov(f);
    else
        return CubicCov(f);
    end if;
end function;


////////////////////////////////////////////////////////////////////////////////////////////
//////////////////////// defining the different bases of covariants ////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////

// Return 4 generically linearly independent covariants of order 1 of a quaternary cubic 
function LinCov(f)
    assert Degree(f) eq 3;
    R := Parent(f);
    
    C404 := DualCubicSurf(f);
    C44 := Hessian(f);
    C62 := DPairing(C404, f^2);
    C93 := DPairing(C404, f*C44);
    C1002 := DPairing(C62, C404);
    C111 := DPairing(C1002, f);
    
    C1301 := DPairing(C93, C404);
    C142 := DPairing(C1002, C44);

    C191 := DPairing(C1301, C62);
    C271 := DPairing(C1301, C142);

    C431 := DPairing(C1301, DPairing(C1301, DPairing(C1301, C44)));
    
    C := [C111, C191, C271, C431];
    
    if Rank(Matrix([[MonomialCoefficient(c, m) : m in MonomialsOfDegree(R, 1)] : c in C])) lt #C then
        vprint Equivalence, 1 : "Warning: the covariants are not linearly independent";
        return C, [11, 19, 27, 43], false;
    end if;
    
    return C, [11, 19, 27, 43], true;
end function;

// Return 10 generically linearly independent covariants of order 2 of a quaternary sextic 
function QuadCov(f)
    assert Degree(f) eq 6;

    R := Parent(f);

    C306 := DualSurf(f);
    c48 := TransvectantGeneral([f, f, f, f], 4 : normalize := true);

    c72 := DPairing(C306, c48);
    C1004_1 := DPairing(c72, C306);
    C1004_2 := DPairing(c48, C306^2);

    c112_1 := DPairing(C1004_1, f);
    c112_2 := DPairing(C1004_2, f);

    c144_1 := DPairing(C1004_1, c48);
    c144_2 := DPairing(C1004_2, c48);
    
    C1702_1 := DPairing(c72, C1004_1);
    C1702_2 := DPairing(c72, C1004_2);
    
    C2102 := DualSurf(c72);

    c312_1 := DPairing(C1702_1, c144_1);
    c312_2 := DPairing(C1702_2, c144_1);
    c312_3 := DPairing(C1702_1, c144_2);
    c312_4 := DPairing(C1702_2, c144_2);
    
    c352_1 := DPairing(C1702_1^2, f);
    c352_2 := DPairing(C1702_2^2, f);
    c352_3 := DPairing(C2102, c144_1); 

    C := [c72, c112_1, c112_2, c312_1, c312_2, c312_3, c312_4, c352_1, c352_2, c352_3];

    if Rank(Matrix([[MonomialCoefficient(C[i], m) : m in MonomialsOfDegree(R, 2)] : i in [1..#C]])) lt #C then
        vprint Equivalence, 1 : "Warning: the covariants are not linearly independent";
        return C, [7, 11, 11, 31, 31, 31, 31, 35, 35, 35], false;
    end if;
    
    return C, [7, 11, 11, 31, 31, 31, 31, 35, 35, 35], true;
end function;

// Return 35 generically linearly independent covariants of order 4 of a ternary quartic 
function QuarticCov(f)
    R := Parent(f);

    Mon := MonomialsOfDegree(R, 4);
    C304 := DualSurf(f);
    
    c54 := DPairing(C304, f^2);
    C704 := DPairing(f, C304^2);
    
    c94 := DPairing(C304, f*c54);
    c134_1 := DPairing(C304, f*c94); 
    c134_2 := DPairing(C304, c54^2);
    
    c134_3 := DPairing(C704, f*c54);
    c174 := DPairing(C704, f*c94); 

    C := [f, c54, c94, c134_1, c134_2, c134_3, c174];//, c214_2, c224, c274_1, c274_2];
    wgt := [1, 5, 9, 13, 13, 13, 17];

    
    wgt cat:= [wgt[i1]+wgt[i2]+wgt[i3]+wgt[i4] : i4 in [Max(i3+1,6)..#C], i3 in [i2+1..#C], i2 in [i1+1..#C], i1 in [1..#C] | i1+i2+i3+i4 le 20];
    C cat:= [TransvectantGeneral([C[i1], C[i2], C[i3], C[i4]], 3) : i4 in [Max(i3+1,6)..#C], i3 in [i2+1..#C], i2 in [i1+1..#C], i1 in [1..#C] | i1+i2+i3+i4 le 20];

    if Rank(Matrix([[MonomialCoefficient(C[i], m) : m in MonomialsOfDegree(R, 4)] : i in [1..#C]])) lt #C then
        vprint Equivalence, 1 : "Warning: the covariants are not linearly independent";
        return C, wgt, false;
    end if;
    
    return C, wgt, true;
end function;


function BasisCovariants(f)
    d := Degree(f);
    assert d in [3, 4, 6];
    
    if d eq 3 then
        return LinCov(f);
    elif d eq 4 then
        return QuarticCov(f);
    else
        return QuadCov(f);
    end if;
end function;

///////////////////////////////////////////////////////////////
//////////////////////// main function ////////////////////////
///////////////////////////////////////////////////////////////

intrinsic IsGL4EquivalentFast(f::RngMPolElt, g::RngMPolElt) -> BoolElt, AlgMatElt
    {
        Given two homogeneous polynomials in 4 variables, return true and the only possible M in GL_4 (up to scaling) such that f^M = c*g, where c is a scalar. 
        If they are not equivalent, only false is returned. When this method fails, an error is returned.
    }

    R := Parent(f);
    K := BaseRing(R);
    g := R!g;
    d := Degree(f);
    n := Rank(R);
    
    require (n eq 4) and IsHomogeneous(f) and IsHomogeneous(g) : "Polynomials must be homogeneous in four variables.";
    require BaseRing(Parent(f)) eq BaseRing(Parent(g)) : "Polynomials must live in the same polynomial ring.";
    require Degree(g) eq d : "Polynomials must have the same degree.";
    
    if d le 2 then 
        error("Not covered by this method");
    end if;    
    
    vprint Equivalence, 1 : "Computing covariant of smaller order...";    
    cov_f := SmallOrderCovariant(f);
    cov_g := SmallOrderCovariant(g);
    
    vprint Equivalence, 1 : "Computing basis of covariants...";    
    C_f, deg_basis, test_f := BasisCovariants(cov_f);
    C_g, _, test_g := BasisCovariants(cov_g);
    
    if test_f ne test_g then
        vprint Equivalence, 1 : "One is a basis and the other is not, therefore the polynomials are not equivalent.";
        return false;
    end if;

    if not test_f then 
        vprint Equivalence, 1 : "We need two bases to use this method.";    
        error("Not covered by this method");
    end if;
    
    vprint Equivalence, 1 : "Computing invariants...";
    if Degree(cov_f) eq 4 then
        invs_f, wgt := SomeInvariantsQuarticSurfaces(C_f, deg_basis);
        invs_g := SomeInvariantsQuarticSurfaces(C_g, deg_basis);
    elif Degree(cov_f) eq 6 then 
        invs_f, wgt := SomeInvariantsQuadricSurfaces(C_f, deg_basis);
        invs_g := SomeInvariantsQuadricSurfaces(C_g, deg_basis);
    else 
        invs_f, wgt := SCInvariants(cov_f);
        invs_g := SCInvariants(cov_g);    
    end if;
        
    test := WPSEqual(wgt, invs_f, invs_g);

    if not test then
        vprint Equivalence, 1 : "The invariants are not equal, therefore the polynomials are not equivalent.";
        return false;
    end if;
    
    if #[inv : inv in invs_f | inv eq 0] eq #invs_f then
        vprint Equivalence, 1 : "An assumption (which should be very close to always being true) was not satisfied.";
        error("Not covered by this method.");
    end if;
    
    gcd, combi := XGCDUnique([wgt[i] : i in [1..#wgt] | invs_f[i] ne 0]);
    
    if GCD([deg_basis[i]-deg_basis[i+1] : i in [1..#deg_basis-1]]) mod gcd ne 0 then
        vprint Equivalence, 1 : "A technical assumption (which should be very close to always true) was not satisfied.";
        error("Not covered by this method"); 
    end if;

    M_f := NormalizeMatrix(Transpose(Matrix(K, [[MonomialCoefficient(c, m) : m in MonomialsOfDegree(R, Degree(C_f[1]))] : c in C_f])));
    M_g := NormalizeMatrix(Transpose(Matrix(K, [[MonomialCoefficient(c, m) : m in MonomialsOfDegree(R, Degree(C_f[1]))] : c in C_g])));
       
    vprint Equivalence, 1 : "Computing inverse matrix...";
    M_f_inv := M_f^(-1);
    
    vprint Equivalence, 1 : "Normalizing matrices...";
    invs_f_mod := [inv : inv in invs_f | inv ne 0];
    invs_g_mod := [inv : inv in invs_g | inv ne 0];
    inv_mult_f := &*[invs_f_mod[i]^combi[i] : i in [1..#combi]]; // normalizing factor to make all covariants of the same weight
    inv_mult_g := &*[invs_g_mod[i]^combi[i] : i in [1..#combi]];
    
    M_g := Transpose(Matrix([Transpose(M_g)[i]*inv_mult_g^((Max(deg_basis)-deg_basis[i]) div gcd) : i in [1..Ncols(M_g)]]));
    M_f_inv := Matrix([M_f_inv[i]/inv_mult_f^((Max(deg_basis)-deg_basis[i]) div gcd) : i in [1..Ncols(M_f)]]);

    if d mod 2 ne 0 then
        M := NormalizeMatrix(M_g*M_f_inv);
    elif d mod 4 eq 0 then
        M_tilde := M_g*M_f_inv;
        vprint Equivalence, 1 : "Finding pre-image of representation matrix...";
        M, test := FindPreImage(M_tilde, 4, 4); // now we find the actual transformation
        if not test then
            return false; // cannot be equivalent otherwise it should be defined over the base field
        end if;
        
        M := ChangeRing(Transpose(NormalizeMatrix(M)), K);
    else
        M_tilde := M_g*M_f_inv;
        vprint Equivalence, 1 : "Finding pre-image of representation matrix...";
        M, test := FindPreImage(M_tilde, 4, 2); // now we find the actual transformation
        
        if not test then
            return false; // cannot be equivalent otherwise it should be defined over the base field
        end if;
        
        M := ChangeRing(Transpose(NormalizeMatrix(M)), K);
    end if;

    try 
        vprint Equivalence, 1 : "Checking if change of variables works...";
        unit := K!(f^Transpose(M)/g);    
        return true, [* Transpose(M) *];
    catch e
        vprint Equivalence, 1 : "Fail. Checking that the change of variables works on the covariants to check for a potential mistake in the process...";
        _ := K!(cov_f^Transpose(M)/cov_g); // that should always be the case, otherwise an error should be displayed
        vprint Equivalence, 1 : "Polynomials are not equivalent.";
        return false;
    end try;
end intrinsic;

intrinsic FastAutosGL4(f::RngMPolElt) -> BoolElt
    {
        Given a general homogeneous polynomial in 4 variables, returns its geometric stabilizer (in PGL4) if it is trivial.
        For the polynomials not covered by this technique, an error is displayed.
    }

    vprint Equivalence, 1 : "Computing covariant of smaller order...";    
    cov_f := SmallOrderCovariant(f);

    vprint Equivalence, 1 : "Computing basis of covariants...";    
    C_f, deg_basis, test_f := BasisCovariants(cov_f);
    
    if not test_f then 
        vprint Equivalence, 1 : "We need the covariants to form a basis to use this method.";    
        error("Not covered by this method");
    end if;
    
    vprint Equivalence, 1 : "Computing invariants...";
    if Degree(cov_f) eq 4 then
        invs_f, wgt := SomeInvariantsQuarticSurfaces(C_f, deg_basis);
    elif Degree(cov_f) eq 6 then 
        invs_f, wgt := SomeInvariantsQuadricSurfaces(C_f, deg_basis);
    else 
        invs_f, wgt := SCInvariants(cov_f);
    end if;
    
    if #[inv : inv in invs_f | inv eq 0] eq #invs_f then // not stable polys
        vprint Equivalence, 1 : "An assumption (which should be very close to always being true) was not satisfied.";
        error("Not covered by this method");
    end if;

    gcd, combi := XGCDUnique([wgt[i] : i in [1..#wgt] | invs_f[i] ne 0]);
    
    if GCD([deg_basis[i]-deg_basis[i+1] : i in [1..#deg_basis-1]]) mod gcd ne 0 then
        vprint Equivalence, 1 : "A technical assumption (which should be very close to always true) was not satisfied.";
        error("Not covered by this method"); 
    end if;

    return [* IdentityMatrix(BaseRing(Parent(f)), 4) *];
end intrinsic;
