function x_minus_T(pt, f, A, AtoSG)
  // Compute the image of a point pt on the Jacobian of a genus 2 curve y^2 = f(x)
  // in the Selmer group. AtoSG is the (partially defined) map from the étale algebra A
  // to the Selmer group.
  a := pt[1]; // a-polynomial of Mumford representation
  fact_a := [e[1] : e in Factorization(a) | IsOdd(e[2])]; // squares map to 1
  result := A!1;
  for fa in fact_a do
    c := (-1)^Degree(fa)*Evaluate(fa, A.1);
    flag, quot := IsDivisibleBy(f, fa);
    if flag then
      c +:= (-1)^Degree(quot)*Evaluate(quot, A.1);
    end if;
    result *:= c;
  end for;
  return AtoSG(result);
end function;



function invert_SGtoA(SGtoA)
  // Produce a map that inverts SGtoA.
  // (There are more efficient ways of doing this, but this should be OK.)
  A := Codomain(SGtoA);
  // Splitting of the étale algebra as a product of number fields
  // (use DoLinearExtension to make sure to produce a FldNum and have K.1 = root)
  A0 := [NumberField(e[1] : DoLinearExtension) : e in Factorization(Modulus(A))];
  maps := [hom<A -> K | K.1> : K in A0];
  // Find the images of the Selmer group elements in the product.
  SGtups := [<<m(a) : m in maps> where a := SGtoA(s), s> : s in Domain(SGtoA)];
  AtoSG := function(a)
             // a in A, represents an element of SG
             atup := <m(a) : m in maps>; // image of a in the product
             // Find the correct Selmer group element
             for tup in SGtups do
               if forall{i : i in [1..#A0] | IsSquare(atup[i]*tup[1,i])} then
                 return tup[2];
               end if;
             end for;
             error "The square class of a is not in the image of the Selmer group.";
           end function;
  return AtoSG;
end function;


function goodness_tests(SGtoA)
  f := Modulus(Codomain(SGtoA));
  bad := PrimeDivisors(2*Integers()!Discriminant(f));
  ff := [e[1] : e in Factorization(f)];
  // For each factor, take a representative root
  // and consider another root of the same or a later factor.
  A := Codomain(SGtoA);
  SG := Domain(SGtoA);
  tests := [];
  for i := 1 to #ff do
    K := NumberField(ff[i] : DoLinearExtension); // DoLinearExtension is necessary to guarantee K.1 = root
    ei := K.1;
    PK := PolynomialRing(K);
    k := AbsoluteField(K); Ok := MaximalOrder(k); bask := Basis(Ok);
    for j := i to #ff do
      for f1 in [e[1] : e in Factorization(PK!ff[j]) | Evaluate(e[1], ei) ne 0] do
        L := ext<K | f1 : DoLinearExtension>;
        ktoL := hom<k-> L| Roots(DefiningPolynomial(k),L)[1][1]>;
        Ol := MaximalOrder(L); basl := Basis(Ol);
        LL := AbsoluteField(L);
        basLL := &cat[[(LL!ktoL(b1))*(LL!b2): b2 in basl]: b1 in bask];
        Oll := Order(basLL); OLL := MaximalOrder(Oll);
        ej := LL!L.1;
      //for p in bad do OLL := pMaximalOrder(OLL, p); end for; 
        primes := &cat[[e[1] : e in Decomposition(OLL, p)] : p in bad];
        // The two maps from A to LL corresponding to theta |--> e_i and theta |--> e_j
        AtoLL1 := hom<A -> LL | LL!L!ei>;
        AtoLL2 := hom<A -> LL | ej>;
        r := Signature(LL); // number of real embeddings
        // Set up the test for LL-rational points on the conic corresponding to s in SG
        test := function(s)
                  a := SGtoA(s); // image in A
                  u := -AtoLL1(a)/(ei-ej);
                  v := AtoLL2(a)/(ei-ej); // conic is u*x^2 + v*y^2 = z^2
                  // images of the coefficients under the real embeddings of LL
                  ureal := [Real(Conjugate(u, i)) : i in [1..r]];
                  vreal := [Real(Conjugate(v, i)) : i in [1..r]];
                  // test the local conditions at the infinite and finite places
                  return forall{i : i in [1..r] | ureal[i] gt 0 or vreal[i] gt 0}
                          and forall{p : p in primes | HilbertSymbol(u, v, p) eq 1};
                end function;
        Append(~tests, test);
      end for;
    end for;
  end for;
  return tests;
end function;


