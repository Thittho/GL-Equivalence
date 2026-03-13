/*
 *  Linear equivalence between homogeneous polynomials 
 *
 *  Thomas Bouchet
 *
 *  See LICENSE.txt for license details.
*/

SetVerbose("Equivalence", 1);

// In 2 variables 
res := [];
for d in [5..30] do
    res_d := [];
    for p in PrimesInInterval(d+1, 1000) do
        res_p := [];
        for i in [1..5] do
            R<x,y> := PolynomialRing(GF(p^3), 2);
            f := &+[Random(GF(p^3))*m : m in MonomialsOfDegree(R, d)];
            M := 2/3*ChangeRing(RandomSLnZ(2, p-1, 20), GF(p^3));
            g := 5/6*f^M;
            try 
                b := IsGL2EquivalentFast(f, g);
                if b then 
                    Append(~res_p, true);
                else 
                    Append(~res_p, false);
                end if;
            catch e
                Append(~res_p, false);
            end try;
        end for;
        Append(~res_d, Set(res_p));
        res_p;
    end for;
    Append(~res, Set(res_d));
end for;


// In 3 variables 
res := [];
for d in [4..10] do
    res_d := [];
    for p in PrimesInInterval(d+1, 100) do
        res_p := [];
        for i in [1..5] do
            R<x,y,z> := PolynomialRing(GF(p^3), 3);
            f := &+[Random(GF(p^3))*m : m in MonomialsOfDegree(R, d)];
            M := 2/3*ChangeRing(RandomSLnZ(3, p-1, 10), GF(p^3));
            g := 5/6*f^M;
            try 
                b := IsGL3EquivalentFast(f, g);
                if b then 
                    Append(~res_p, true);
                else 
                    Append(~res_p, false);
                end if;
            catch e
                Append(~res_p, false);
            end try;
        end for;
        Append(~res_d, res_p);
        res_p;
    end for;
    Append(~res, res_d);
end for;


// In 4 variables 
res := [];
for d in [3..8] do
    res_d := [];
    for p in PrimesInInterval(d+1, 30) do
        res_p := [];
        for i in [1..5] do
            R<x,y,z,t> := PolynomialRing(GF(p^3), 4);
            f := &+[Random(GF(p^3))*m : m in MonomialsOfDegree(R, d)];
            M := 2*ChangeRing(RandomSLnZ(4, p-1, 10), GF(p^3));
            g := 1/2*f^M;
            try 
                b := IsGL4EquivalentFast(f, g);
                if b then 
                    Append(~res_p, true);
                else 
                    Append(~res_p, false);
                end if;
            catch e
                Append(~res_p, false);
            end try;
        end for;
        Append(~res_d, res_p);
        res_p;
    end for;
    Append(~res, res_d);
end for;
