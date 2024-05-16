//This code for requires the curves to have analytic rank associated to the jacobian to be 0.
//The curves must be intered in the format : Y^2 = f(x), where f(x) has odd degree.
Qx<x> := PolynomialRing(Rationals()); 
function convert_monic_integral(C)
	C := IntegralModel(C);
	f := HyperellipticPolynomials(C);
	if IsMonic(f) eq false then // MS: if not IsMonic(f) then ...
                a := LeadingCoefficient(f);
                b := a^2;
                f := b^2*Evaluate(f,x/a );
                C := HyperellipticCurve(f);
	end if;
	return C;
end function;

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

function SS_and_T_in_SG(C)
  C := convert_monic_integral(C);
  f := HyperellipticPolynomials(C);
  J := Jacobian(C);
  // Compute the 2-Selmer group
  SG, SGtoA :=TwoSelmerGroup(J);
  AtoSG := invert_SGtoA(SGtoA);
  A := Codomain(SGtoA);
  T, TtoJ := TorsionSubgroup(J);
  // Reduce to 2-primary subgroup
  T2 := pPrimaryComponent(T, 2);
  TinSG := sub<SG | [x_minus_T(TtoJ(T!t), f, A, AtoSG) : t in OrderedGenerators(T2)]>;
  if #TinSG eq #SG then 
	return SG, {2*SG.1}, SG, SGtoA, AtoSG;
  end if;
  // Compute the 2-Selmer set
  SS, AtoSS := TwoCoverDescent(C);
  A1 := Domain(AtoSS);	
  assert Modulus(A) eq Modulus(A1);
  A1toA := hom<A1 -> A | A.1>;
  // Find the images of the elements of SS in SG
  SSinSG := {AtoSG(A1toA(s @@ AtoSS)) : s in SS}; // image of Selmer set in Selmer group
  // Compute the torsion subgroup
  
  return SG, SSinSG, TinSG, SGtoA, AtoSG;
end function;

function good_subgroup(known_part, SGtoA)
	goodSGelts:= [];
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
    for j := i to #ff do
      for f1 in [e[1] : e in Factorization(PK!ff[j]) | Evaluate(e[1], ei) ne 0] do
        L := ext<K | f1 : DoLinearExtension>;
        LL := AbsoluteField(L);
        ej := LL!L.1;
        OLL := MaximalOrder(LL);  
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
  // Now check, for each element s of SG that is not in known_part,
  // if the associated conics have rational points.
  // If so, update known_part to known_part + <s>.
  for s in SG do
    if s notin known_part and forall{t : t in tests | t(s)} then
      known_part +:= sub<SG | s>;
      Append(~goodSGelts, s);
    end if;
  end for;
  return known_part, goodSGelts;
end function;

function isgood(C)
  // This returns
  // (1) the Selmer group SG as an abstract abelian group
  // (2) the image of the torsion subgroup of the Jacobian in SG
  // (3) the image of the Selmer set in SG as a set	
  // (4) the subgroup generated by "good" elements of SG
  SG, SSinSG, TinSG, SGtoA, AtoSG := SS_and_T_in_SG(C);
  SStors := sub<SG | SSinSG> + TinSG;
  SS := [2*SG.1];
  for s in SSinSG do
 	 if not (s  in sub<SG| SS> or  s in TinSG)  then
	     Append(~SS, s);  
	 end if; 
  end for;
  Exclude(~SS, 2*SG.1);
  good , goodSGelts := good_subgroup(SStors, SGtoA);
  goodSGelts cat:= SS;
  return #SG/#good, SS, TinSG, goodSGelts, SG, SGtoA; 
end function;
