import "GL3_equivalence.m" : QuarticCov;

intrinsic IsGLnEquivalentNaive(f::RngMPolElt, g::RngMPolElt : geometric := false) -> .
    {
        Given two homogeneous polynomials f and g in the same number of variables, return true if they differ only from a change of variables over the base field,
        and the list of all matrices M such that f^M is a non-zero scalar multiple of g. Otherwise, false is returned. 
        If the flag geometric is set to true, geometric equivalence is considered.
    }
    
    R := Parent(f);
    K := BaseRing(R);
    n := Rank(R);
    d := Degree(f);

    require Parent(g) eq R : "Polynomials must have the same base ring.";

    if Degree(g) ne d then
        return false;
    end if;

    S<[a]> := PolynomialRing(K, n^2 + 1);
    Rtilde := PolynomialRing(S, n);

    Basis := MonomialsOfDegree(Rtilde, d);

    Change := [ &+[ a[i + n*(j-1)] * Rtilde.i : i in [1..n] ] : j in [1..n] ];

    scale := a[Rank(S)];
    f_trans := scale * Evaluate(Rtilde!f, Change);

    relations := [ MonomialCoefficient(f_trans, m)-MonomialCoefficient(Rtilde!g, m) : m in Basis ];

    geom_eq := false;

    vprint Equivalence, 1 : "Checking from less generic to most generic case...";    
    for i in [1..n] do 
        I := Ideal(relations cat [a[j] : j in [1..n-i]] cat [a[n-i+1]-1]);
    
        vprint Equivalence, 1 : "Computing Gröbner basis " cat Sprint(i) cat "/" cat Sprint(n) cat "...";
        G := GroebnerBasis(I);
        G_list := Eltseq(G);

        if G_list ne [1] then
            geom := [el : el in G_list | Degree(Monomials(el)[1]) gt 1];
            if geom ne [] then
                vars := [i : i in [1..n^2+1] | Max([Degree(el, i) : el in geom]) ge 1];
                S0 := PolynomialRing(K, #vars);
                new_vars := [];
                current := 1;
                for i in [1..n^2+1] do
                    if i in vars then
                        Append(~new_vars, S0.current);
                        current +:= 1;
                    else    
                        Append(~new_vars, S0!0);
                    end if;
                end for;
                Var := Variety(Ideal([Evaluate(el, new_vars) : el in geom]));
                if Var ne [] then    
                    vprint Equivalence, 1 : "Matrix found over the base field";
                    L := K;
                elif geometric then
                    vprint Equivalence, 1 : "Matrix found over an extension";
                    I := Ideal([Evaluate(el, new_vars) : el in geom]);
                    Var := PointsOverSplittingField(Scheme(Spec(S0), I));
                    Var := [v : v in Var];
                    L := Parent(Var[1][1]);
                    S := ChangeRing(S, L);
                    G_list := ChangeUniverse(G_list, S);
                else 
                    geom_eq := true;
                    break i;
                end if;
                res := [* *];
                for rat_pt in Var do
                    current := 1;
                    evaluation := [];
                    for i in [1..n^2+1] do
                        if i in vars then
                            Append(~evaluation, rat_pt[current]);
                            current +:= 1;
                        else    
                            Append(~evaluation, S.i);
                        end if;
                    end for;
                    G_list_eval := [Evaluate(g, evaluation) : g in G_list];
                    Append(~res, Matrix(L, n, n, [NormalForm(evaluation[i], G_list_eval) : i in [1..n^2]]));
                end for;
                return true, res;       
            else
                return true, [* Matrix(K, n, n, [NormalForm(a[i], G) : i in [1..n^2]]) *];
            end if;      
        else 
            vprint Equivalence, 1 : "No matrix found, continuing...";
        end if;
    end for;

    if geom_eq then 
        vprint Equivalence, 1 : "Polynomials are geometrically equivalent, but not over the base field.";
    end if;

    return false;
end intrinsic;


intrinsic IsGLnEquivalent(f::RngMPolElt, g::RngMPolElt : geometric := false) -> .
    {
        Given two homogeneous polynomials f and g in the same number of variables (at most 4), return true if they differ only from a change of variables over the base field,
        and the list of all matrices M such that f^M is a non-zero scalar multiple of g. Otherwise, false is returned. 
        If the flag geometric is set to true, geometric equivalence is considered.
    }

    R := Parent(f);
    K := BaseRing(R);
    n := Rank(R);
    d := Degree(f);
    
    require n le 4 : "The number of variables must be at most 4.";
    require Parent(g) eq R : "Polynomials must have the same base ring.";
    require IsHomogeneous(f) and IsHomogeneous(g) : "Polynomials must be homogeneous.";

    if Degree(g) ne d then
        return false;
    end if;

    vprint Equivalence, 1 : "Trying fast method...";
    if n eq 2 then
        try 
            return IsGL2EquivalentFast(f, g);
        catch e 
            vprint Equivalence, 1 : "Fail. Trying another fast method...";
            S := PolynomialRing(K);
            return IsGL2EquivalentExtended(Evaluate(f, [S.1, 1]), Evaluate(g, [S.1, 1]), d : geometric := geometric);
        end try;
    elif n eq 3 then 
        try 
            return IsGL3EquivalentFast(f, g);
        catch e 
            vprint Equivalence, 1 : "Fail. Trying another fast method...";
            if Degree(f) mod 3 ne 0 then
                cov_f := QuarticCov(f);
                cov_g := QuarticCov(g);
                return IsIsomorphicTernaryQuartics(cov_g, cov_f : geometric := geometric);
            end if;
            vprint Equivalence, 1 : "Fail. Trying slow method...";
            vprint Equivalence, 1 : "Warning: this method uses Gröbner bases and can be very slow.";
            return IsGLnEquivalentNaive(f, g : geometric := geometric);
        end try;
    elif n eq 4 then 
        try 
            return IsGL4EquivalentFast(f, g);
        catch e 
            vprint Equivalence, 1 : "Fail. Trying slow method...";
            vprint Equivalence, 1 : "Warning: this method uses Gröbner bases and can be very slow.";
            return IsGLnEquivalentNaive(f, g : geometric := geometric);
        end try;
    end if;
end intrinsic;


