
/*

function CompatibleExp(n, l)
    fact := Factorial(n);
    permMats := [<M, Determinant(M)> where M := PermutationMatrix(Rationals(), s) : s in Sym(n)];
    S := PolynomialRing(Rationals(), fact);
    time exps := [Exponents(mon) : mon in MonomialsOfDegree(S, l)];
    time list := [<&+[exp[i]*permMats[i][1] : i in sup], &*[permMats[i][2]^exp[i] : i in sup]>  where sup := Support(Vector(exp)) : exp in exps];
    time ParallelSort(~list, ~exps);
    res := [<list[1][1], list[1][2], exps[1]>];
    current := list[1];
    time for i->exp in exps do
        l1, l2 := Explode(list[i]);
        if <l1, l2> ne current then
            Append(~res, <l1, l2, exp>);
            current := <l1, l2>;
        end if;
    end for;
    return res;
end function;




function NaiveEquivalence2(l_f, l_g, l_deg)
    R := Universe(l_f);
    K := BaseRing(R);
    n := Rank(R);
    l_d := [Degree(f) : f in l_f];

    if Universe(l_g) ne R then
        error("Polynomials must have the same base ring.");
    end if;

    if [Degree(g) : g in l_g] ne l_d then
        error("Polynomials must have the same degree.");
    end if;

    S<[a]> := PolynomialRing(K, n^2 + 2);
    Rtilde := PolynomialRing(S, n);

    //Basis := MonomialsOfDegree(Rtilde, d);

    Change := [
        &+[ a[i + n*(j-1)] * Rtilde.i : i in [1..n] ]
        : j in [1..n]
    ];

    scale := a[Rank(S) - 1];
    det := a[Rank(S)];
    l_f_trans := [scale^l_deg[i] * Evaluate(Rtilde!f, Change) : i->f in l_f];

    //Coeff_f := [ MonomialCoefficient(f_trans, m) : m in Basis ];
    //Coeff_g := [ MonomialCoefficient(Rtilde!g, m) : m in Basis ];

    relations := 
        [ a[Rank(S)] - Determinant(Matrix(n, n, a[1..n^2])) ] cat
        &cat[ Coefficients(l_f_trans[i]-Rtilde!l_g[i]) : i in [2..#l_f] ]
    ; // we don't take f and g to be more efficient

    ////////vprint Equivalence: "Computing Gröbner basis...";
    time G := GroebnerBasis(Ideal(relations));
    ////////vprint Equivalence: "Done!";

    time G := GroebnerBasis(Ideal(Eltseq(G) cat Coefficients(l_f_trans[1]-Rtilde!l_g[1])));

    if &and[Degree(el) eq 1 : el in Eltseq(G)[1..n^2-1]] then
        res := [ NormalForm(a[i], G) : i in [1..n^2] ];
        gcd := GCD(res);
        return true, ChangeRing(Matrix(n, n, res) div gcd, K);
    end if;

    if 1 in Eltseq(G) then 
        return false;
    end if;

    "Polynomials might be equivalent over an algebraic extension.";
    return &+[VarietySizeOverAlgebraicClosure(Ideal(relations cat [a[j] : j in [1..i-1]] cat [a[i]-1])) : i in [1..n]];
end function;

*/