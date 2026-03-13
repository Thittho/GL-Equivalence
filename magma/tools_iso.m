/*
 *  Linear equivalence between homogeneous polynomials 
 *
 *  Thomas Bouchet
 *
 *  See LICENSE.txt for license details.
*/

declare verbose Equivalence, 2;

// Return the Hessian of the homogeneous polynomial f 
intrinsic Hessian(f::RngMPolElt) -> RngMPolElt
    {
        Return the Hessian associated to a homogeneous polynomial f.
    }

    n := Rank(Parent(f));
    return Determinant(Matrix([[Derivative(Derivative(f, i), j) : i in [1..n]] : j in [1..n]]));
end intrinsic;

// Return the differentiation of f whose order in each variable is given by the list indices 
function DerivativeMulti(f, indices)
    R := Parent(f);
    n := Rank(R);

    if #indices ne n then 
        error("Number of e_i's must equal to the number of variables of f.");
    end if;

    if &or[indices[i] gt Degree(f, i) : i in [1..n]] or &+indices gt Degree(f) then
        return Parent(f)!0;
    end if;

    g := f;
    for i in Support(Vector(indices)) do
        g := Derivative(g, indices[i], i);
    end for;
    return g;
end function;

// Return the differentiation of Q along P
intrinsic DPairing(P::RngMPolElt, Q::RngMPolElt) ->  RngMPolElt
    {
        Return the differentiation of Q along P
    }

    RP := Parent(P);
    RQ := Parent(Q);

    if P eq 0 then
        error("P cannot be 0");
    end if;

    Coef, Mon := CoefficientsAndMonomials(P);
    Exp := [Exponents(m) : m in Mon];
    return &+[Coef[i]*DerivativeMulti(Q, exp) : i->exp in Exp];
end intrinsic;


intrinsic TransvectantGeneral(polys::SeqEnum[RngMPolElt], l::RngIntElt : normalize := false) -> RngMPolElt
    {
        Given a list polys = [f_1, ..., f_n] of homogeneous polynomials in the n variables, and an integer l, return the transvectant (f_1, ..., f_n)_l.
        If normalize is set to true, the classical renormalizing factor is applied. For binary forms, this function with normalize set to true matches the Transvectant intrinsic.
    }

    n := #polys;
    R := Universe(polys);

    if Rank(R) ne n then
        error("Number of variables must equal the number of polynomials.");
    end if;

    if l gt Min([Degree(f) : f in polys]) then
        return R!0;
    end if;
    
    // Auxiliary polynomial ring for determinant expansion
    S := PolynomialRing(Rationals(), n^2);

    // Build n x n matrix of variables
    M := Transpose(Matrix(n, n, [ S.(j + n*(i-1)) : j in [1..n], i in [1..n] ]));

    // Computing the determinant of this matrix
    vprint Equivalence, 2 : "Computing power of determinant...";
    det := Determinant(M)^l;
        
    Coeffs, Mons := CoefficientsAndMonomials(det);

    E := PolynomialRing(Rationals(), n);
    MultiIndices := [ Exponents(m) : m in MonomialsOfDegree(E, l) ];
    
    Derivs := [ AssociativeArray() : _ in [1..n] ];  
    vprint Equivalence, 2 : "Computing derivatives...";
    for e in MultiIndices do
        key := Sprint(e);
        for i in [1..n] do
            Derivs[i][key] := DerivativeMulti(polys[i], e);
        end for;
    end for;
        
    EvalMons := [];
    vprint Equivalence, 2 : "Evaluating power of determinant...";
    for m in Mons do
        exp := Exponents(m);
        blocks := [ exp[(i-1)*n+1 .. i*n] : i in [1..n] ];
        Append(~EvalMons, R!&*[ Derivs[i][Sprint(blocks[i])] : i in [1..n] ]);
    end for;
        
    vprint Equivalence, 2 : "Doing final sum...";
    res := &+[ Coeffs[i] * EvalMons[i] : i in [1..#Coeffs] ];
    
    if normalize then
        cfg := &*[Factorial(Degree(f)-l)/Factorial(Degree(f)) : f in polys];
    else 
        cfg := 1;
    end if;

    return cfg*res;
end intrinsic;


// Return the only (up to d-th root of unity) preimage of GL_n -> GL(Sym^d(K^n)) of M_tilde, where M_tilde is assumed to be in the image
function FindPreImage(M_tilde, n, d)
    K := BaseRing(M_tilde);

    vprint Equivalence, 2 : "Computing representation matrix symbolically...";
    R0<[a]> := PolynomialRing(K, n^2);
    S := PolynomialRing(R0, n);
    Basis := MonomialsOfDegree(S, d);

    Change := [
        &+[ a[i + n*(j-1)] * S.i : i in [1..n] ]
        : j in [1..n]
    ];

    M_rep := Matrix(
        [ [ MonomialCoefficient(Evaluate(f, Change), g)
            : f in Basis ]
          : g in Basis ]
    );
    
    // Locate a power entry to normalize
    pos := [ <i,j> : i,j in [1..Ncols(M_rep)]
             | IsPower(Basis[i], d) and M_tilde[i][j] ne 0 ];
    if #pos eq 0 then
        vprint Equivalence, 2 : "No suitable normalization was found.";
        error("No suitable normalization entry found.");
    end if;

    i0, j0 := Explode(pos[1]);
    _, variable := IsPower(M_rep[i0][j0], d);

    alpha := M_tilde[i0][j0];
    M_tilde /:= alpha;

    // Restrict to monomial entries
    Indices := [
        <i,j> : i,j in [1..Ncols(M_rep)]
        | #Monomials(M_rep[i][j]) eq 1
    ];

    MonomialRelations :=
        [ variable - R0!1 ] cat
        [ M_rep[i][j] - R0!M_tilde[i][j]
          where i,j := Explode(ind) : ind in Indices ];

    Relations :=
        [ variable - R0!1 ] cat
        [ M_rep[i][j] - R0!M_tilde[i][j]
          : i, j in [1..n] ];

    vprint Equivalence, 2 : "Computing variety defined by the monomial relations...";
    V := Variety(Ideal(MonomialRelations));

    if V ne [] then // we look only at monomials, therefore we miss some information
        for v in V do
            v_list := [el : el in v];
            if [Evaluate(rel, v_list) : rel in Relations] eq [0 : _ in [1..n^2+1]] then
                return Matrix(n, n, v_list[1..n^2]), true;
            end if;
        end for;
    end if;
    
    error("There exists no preimage over the base field.");
end function;



// Normalize a matrix by the first nonzero entry in its first row
function NormalizeMatrix(M)
    idx := Min([ i : i in [1..Ncols(M)] | M[1][i] ne 0 ]);
    return M / M[1][idx];
end function;


// Extended GCD with unique coefficient vector
// (from Jeroen's hyperelliptic package)
function XGCDUnique(L)
    if #L eq 0 then
        return 0, [];
    end if;

    if #L eq 1 then
        return L[1], [ Universe(L)!1 ];
    end if;

    g := GCD(L);
    C := [ Universe(L)!0 : _ in L ];

    gc, C[1], C[2] := XGCD(L[1], L[2]);
    idx := 2;

    while gc ne g do
        idx +:= 1;
        gc, x, C[idx] := XGCD(gc, L[idx]);
        for i in [1..idx-1] do
            C[i] *:= x;
        end for;
    end while;

    return g, C;
end function;

