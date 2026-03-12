import "tools_iso.m":
    FindPreImage, XGCDUnique, NormalizeMatrix; 

/////////////////////////////////////////////////////////////////
//////////////////////// some invariants ////////////////////////
/////////////////////////////////////////////////////////////////

// Return the classical 6 invariants classifying binary quintics up to GL2 action (up to constants)
function InvariantsOfBinaryQuintic(f)
    i := Transvectant(f, f, 4); // 2, 2
    j := -Transvectant(i, f, 2); // 3, 3
    
    tau := Transvectant(j, j, 2); // 6, 2
    theta := Transvectant(i, tau, 1); // 8, 2
    
    alpha := Transvectant(i^2, f, 4); // 5, 1
    beta := Transvectant(i, alpha, 1); // 7, 1
    gamma := Transvectant(tau, alpha, 1); // 11, 1
    
    A := Transvectant(i, i, 2); // 4
    B := Transvectant(i, tau, 2); // 8
    C := Transvectant(tau, tau, 2); // 12
    M := Transvectant(beta, alpha, 1); // 12
    N := Transvectant(gamma, alpha, 1); // 16
    R := Transvectant(theta, alpha^2, 2); // 18
    
    return [BaseRing(Parent(f)) | A, B, C, M, N, R], [4, 8, 12, 12, 16, 18];
end function;


/////////////////////////////////////////////////////////////////////////
//////////////////////// defining all covariants ////////////////////////
/////////////////////////////////////////////////////////////////////////

// Return an order 8 covariant of Sym^{2d}(K^2)
function OcticCov(f)
    assert f ne 0;
    d := Degree(f);
    assert d mod 2 eq 0; 
    return TransvectantGeneral([f, f], d-4);
end function;

// Return an order 5 covariant of Sym^{2d+1}(K^2)
function QuinticCov(f)
    assert f ne 0;
    d := Degree(f);
    assert d mod 2 ne 0; 
    if d mod 4 eq 1 then
        return TransvectantGeneral([TransvectantGeneral([f, f], (d-1) div 2), f], d-2);
    else 
        return TransvectantGeneral([TransvectantGeneral([f, f], (d+1) div 2), f], d-3);
    end if;
end function;

function SmallOrderCovariant(f)
    if Degree(f) mod 2 ne 0 then
        return QuinticCov(f);
    else
        return OcticCov(f);
    end if;
end function;


////////////////////////////////////////////////////////////////////////////////////////////
//////////////////////// defining the different bases of covariants ////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////

// Return 2 generically linearly independent covariants of order 1 of a binary quintic
function LinCov(f)
    assert Degree(f) eq 5;
    R := Parent(f);
    i := Transvectant(f, f, 4); // deg 2, ord 2

    c0 := Transvectant(i^2, f, 4); // deg 5, ord 1
    c1 := Transvectant(i, c0, 1); // deg 7, ord 1
    C := [c0,c1];
    
    if Rank(Matrix([[MonomialCoefficient(c, R.i) : i in [1..Rank(R)]] : c in C])) lt #C then
        vprint Equivalence, 1 : "Warning: the covariants are not linearly independent";
        return C, [5, 7], false;
    end if;
    
    return C, [5, 7], true;
end function;

// Return 3 generically linearly independent covariants of order 2 of a binary octic 
function QuadCov(f)
    assert Degree(f) eq 8;
    R := Parent(f);
    
    c24 := Transvectant(f, f, 6); // deg 2, ord 4
    c34 := Transvectant(f, c24, 4); // deg 3, ord 4
    c52 := Transvectant(c24, c34, 3); // deg 5, ord 2
    
    c0 := Transvectant(c24^2, f, 7); // deg 5, ord 2
    c1 := Transvectant(c34*c24, f, 7); // deg 6, ord 2
    c2 := Transvectant(c52, c24, 2); // deg 7, ord 2
    C := [c0, c1, c2];
    
    if Rank(Matrix([[MonomialCoefficient(c, m) : m in MonomialsOfDegree(R, 2)] : c in C])) lt #C then
        vprint Equivalence, 1 : "Warning: the covariants are not linearly independent";
        return C, [5, 6, 7], false;
    end if;
    
    return C, [5, 6, 7], true;
end function;

function BasisCovariants(f)
    d := Degree(f);
    assert d in [5, 8];
    
    if d eq 5 then
        return LinCov(f);
    end if;
    
    return QuadCov(f);
end function;


///////////////////////////////////////////////////////////////
//////////////////////// main function ////////////////////////
///////////////////////////////////////////////////////////////


intrinsic IsGL2EquivalentFast(f::RngMPolElt, g::RngMPolElt) -> BoolElt, AlgMatElt
    {
        Given two homogeneous polynomials in 2 variables, return true and the only possible M in GL_2 (up to scaling) such that f^M = c*g, where c is a scalar. 
        If they are not equivalent, only false is returned. When this method fails, an error is returned.
    }

    R := Parent(f);
    K := BaseRing(R);
    g := R!g;
    d := Degree(f);
    n := Rank(R);
    
    require (n eq 2) and IsHomogeneous(f) and IsHomogeneous(g) : "Polynomials must be homogeneous in two variables.";
    require BaseRing(Parent(f)) eq BaseRing(Parent(g)) : "Polynomials must live in the same polynomial ring.";
    require Degree(g) eq d : "Polynomials must have the same degree.";
    
    if d le 4 then 
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
    if Degree(cov_f) eq 8 then
        invs_f, wgt := ShiodaInvariants(cov_f);
        invs_g := ShiodaInvariants(cov_g);
    else 
        invs_f, wgt := InvariantsOfBinaryQuintic(cov_f);
        invs_g := InvariantsOfBinaryQuintic(cov_g);
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
    else
        M_tilde := M_g*M_f_inv;
        vprint Equivalence, 1 : "Finding pre-image of representation matrix...";
        M, test := FindPreImage(M_tilde, 2, 2); // now we find the actual transformation
                
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

intrinsic FastAutosGL2(f::RngMPolElt) -> BoolElt
    {
        Given a general homogeneous polynomial in 2 variables, returns true if its geometric stabilizer (in PGL2) is trivial.
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
    if Degree(cov_f) eq 8 then
        invs_f, wgt := ShiodaInvariants(cov_f);
    else 
        invs_f, wgt := InvariantsOfBinaryQuintic(cov_f);
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

    return [* IdentityMatrix(BaseRing(Parent(f)), 2) *];
end intrinsic;
