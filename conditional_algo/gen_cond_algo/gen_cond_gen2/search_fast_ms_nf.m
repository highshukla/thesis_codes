//This code for requires the curves to have analytic rank associated to the jacobian to be 0.
//The curves must be intered in the format : Y^2 = f(x), where f(x) has odd degree.
//This file contains the following functions:
/*

1) compute_pol: input : list of coefficients in increasing power order.
		output: a polynomial in Q[x] associated to the input list.

2) convert_monic_integral: input : a hyperelliptic curve C of the form Y^2 = f(x), with f in Q[x].
			   output: a hyperelliptic curve of the form Y^2 = g(x) isomorphic to C, with g in Z[x] and monic.

3) compute_TinSG : input : T (torsion subgroup of jacobian), TtoJ (map from T to J), f (defining polynomial of hyperelliptic curve), A (etale algebra), A0 (cartesian product representation of etale 				   algebra), M (tuple of maps from A to each component of A0), ImgSGinA0 (Image of 2-selmer group in A0), SG (2- selmer group of J)
		   output: Subgroup of selmer group (SG) coming from the torsion subgroup.

4) SS_computation : input : a hyperelliptic curve C of the form Y^2 = f(x) with f in Q[x].
		    output: SG (selmer group of jacobian), SGtoA (map from SG to etale algebra A), subgrp_SS (subgroup generated by selmer set), #SG/#subgrp_SS (index of subgroup of selmer set in SG), 				    TinSG (imgage of torsion subgroup in SG), A (etale algebra), A0 (cartesian product of componenets of etale algebra), M (tuple of maps from etale algebra to each component of 				    A0).

5) compute_orbits : input : gal (group of automorphisms of the splitting field), diff_set (set of difference of roots of f)
		   output : set of representatives of different gal orbits of diff_set. (e_i-e_j is in the orbit of e_k-e_l if either g(e_k-e_l)=\pm (e_i-e_j)).


6) nice_SG_elts : input : f (polynomial from the monic integral model of starting curve), N (splitting field of f), SG (selmer group of jacobian of C : Y^2 = f(x)), SGtoA (map from SG to etale algebra),
		          SS_grp (subgroup of SG generated by selmer set elements), TinSG (subgroup of SG generated by torsion subgroup of jacobian of C)
		  output: subset of SG outside the subgroup generated by TinSG and SS_grp containing good elements. The function does not compute all the good elements of SG but it coputes untill TinSG, 				  SS_grp and the good elements computed till now span all of SG.

6) work_prog : input : a polynomial in Q[x]
	       output: a tuple consisting of classification number (0-4), selmer group, map from selmer group to etale algebra, known_part (subgroup of SG generated by image of torsion inside SG and the 			       selmer set elements), and extra elements of selmer group which are good and not in known-part.

7) search_curves : input : list of polynomials in Q[x].
		 : output : list of curve classifications: good curves, bad curves, good curves which were not tested because of high degree of splitting field, good curves with good points.


Flow chart of computation:= 1) work_prog calls convert_monic_integral.
			  2) work_prog calls SS_computation
				1) SS_computation calls compute_TinSG
			  3) work_prog does initial classification on the basis if selmer set and the image of torsion inside selmer group generates the selmer group
			  4) if not then work_prog checks if the degree of the splitting field is too high i.e. >30 and does further classification on the basis if the curve is to be tested or not.
			  5) work prog calls nice_SG_elts
				1) nice_SG_elts calls compute_orbits
			  6) work prog does the final classification based on the result of nice_SG_elts.

Definitions:
	1) goodpoint : An element of SG\{T + <SS>} is said to be a good point if each of the conics C_ij := di*u^2-dj*v^2 = ej-ei has a solution in the splitting field (say N).
		       Here (d1,d2,d3,d4,d5) in N^5 represents the element of SG and (e1,e2,e3,e4,e5) in N^5 represent the tuple of roots of f.

 	2) good_curve [classification number: 1]: A curve is said to be good if SG is not generated by the image of Torsion in SG and selmer set elements.

	3) gcgp [classification number : 4]: A curve is gcgp (good curve with good points) if it is a good curve and it has at least one good SG point.

	4) non_tested_gc [classification number 3]: A curve is classified as non_tested_gc (non tested good curve) if it is a good curve and the splitting field degree over rationals is >30.

	5) bad_curve [classification number 0]: A curve is said to be a bad curve if it is not any of the above.

The classification is done disjointly i.e. a curve in gcgp is also a good curve but we do not include it there because of a better classficiation available i.e. gcgp.


Method of computing di corresponding to ei:
	Let a be an element in A (etale algebra) denote by a polynomial then d_i = a(e_i).
*/

Qx<x>:=PolynomialRing(Rationals());

/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

// MS: This is not very efficient.
// The simplest way of doing this is:  Qx!a
// (Anyway, this function is apparently not used later.)

compute_pol:=function(a)
	pol:=0;
	for i in [1..#a] do
		pol:=pol+a[i]*x^(i-1);
	end for;
	return pol;
end function;

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

convert_monic_integral := function(C)
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

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

//this function computes the image of Torsion subgroup of J(C) inside the Selmer group

compute_TinSG := function(T, TtoJ, f, A, A0, M, ImgSGinA0, SG)

	factors := Factorization(f);
	tors_list_in_A := []; //to store the coresponding representation in the etale algebra A.
	for i in T do
		if (i eq T!0) then
			continue;
                else
			prod_a := A!1;
                        a := TtoJ(i)[1]; //storing the first element of Mumford rep of i
                        factors_a := Factorization(a);
			//the following for loop computes the \delta map from J(k)-> A^*
                        for j in factors_a do
                                if f mod j[1] eq 0 then//if j divides f
                                // MS: if IsDivisibleBy(f, j[1]) then
					b := f/j[1];
					b := Qx!b;
					// MS: better: b := ExactQuotient(f, j[1]);
                                        j_n := (-1)^(Degree(j[1]))*Evaluate(j[1],A.1);
                                        b := (-1)^(Degree(f)-Degree(j[1]))*Evaluate(b,A.1); // MS: mistake in exponent
//                                         b := (-1)^(Degree(f)-Degree(a))*Evaluate(b,A.1);
                                        c := j_n+b;
                                        prod_a := prod_a*c; // MS: prod_a *:= c;
                                else //if j does not divide f
                                        c := (-1)^(Degree(j[1]))*Evaluate(j[1],A.1);
					prod_a := prod_a*c;
	   			end if;
                        end for;
                        prod_a := <m(prod_a): m in M>;
                        tors_list_in_A := Append(tors_list_in_A, prod_a); // MS: Append(~tors_list_in_A, prod_a);
                end if;
        end for;
	tors_list_set := {}; //to store the elements of SG which come from torsion
	for i in tors_list_in_A do
		for j in ImgSGinA0 do
			if <IsSquare(i[l]/j[l]) : l in [1..#factors]> eq <true : p in factors> then //comparing with image of SG in in A0 modulo squares.
				tors_list_set := Include(tors_list_set, j[#factors + 1]);
			end if;
		end for;
	end for;
	tors_list_set := Setseq(tors_list_set);
	TinSG := sub<SG | tors_list_set>;
	return TinSG;
end function;


////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////


SS_computation:=function(C)
	C := convert_monic_integral(C);
	J:=Jacobian(C);
	f := HyperellipticPolynomials(C);
	factors:=Factorization(f);
	A0:=CartesianProduct(<quo<Qx|[i[1]]>: i in factors>); //defining A0 to be the cartesian product of Number fields corresponding to the irreducible factors of f
	SG, SGtoA :=TwoSelmerGroup(J);    //computing selmer group of J

	A:=Codomain(SGtoA);    //computing the etale algebra
	try
		SS, AtoSS:=TwoCoverDescent(C); //computing two selmer set data (I do not know if it computes two selmer set exactly)
		catch e
		return 0; //return 0 if there is an error in TwoCoverDescent(C)
	end try;
	A1:=Domain(AtoSS); //computing the etale algebra in a different representation
	A1toA:=hom<A1->A|A.1>; //defining the isomorphism between two different representations of the etale algebra A and A1
	ImginA1:={s@@AtoSS : s in SS}; //preimage of SS elements in A1
	ImginA:={A1toA(a): a in ImginA1}; //image of the preimage of SS elements in A1 under the A1toA isomorphism (this is A1toA(AtoSS^{-1}(SS)))
	ImginA:=Setseq(ImginA); //converting to the set sequence
	ImgofSG:={<SGtoA(g),g>: g in SG}; //graph of the image of SG in A
	ImgofSG:=Setseq(ImgofSG); //converting to the set sequence
	M:=<hom<A->Component(A0,i)| Component(A0,i).1>: i in [1..#factors]>;  //defining the isomorphism via component wise projection of elements of A onto components of A0
	A0_zero:=<C!0:C in Components(A0)>;
	ImgSGinA0:=[];
	for a in ImgofSG do
		ImgSGinA0:=Append(ImgSGinA0,Append(<m(a[1]): m in M>,a[2])); //storing the graph of the composite map from SG to A0 in ImgSGinA0
	end for;
	ImgSSinA0:=[];
	for a in ImginA do;
		ImgSSinA0:=Append(ImgSSinA0,<m(a): m in M>); //storing the Image of the composite map from SS to A0 in ImgSSinA0. This is Image(M(A1toA(AtoSS^{-1}(SS)))).
	end for;
	same_elements:=[]; //to store the elements of elements in ImgSGinA0 and ImgSSinA0 which are same modulo square in A0.
	for a in ImgSSinA0 do
		for b in ImgSGinA0 do
		issquare_ab:=<IsSquare(a[i]/b[i]): i in [1..#factors]>; //checking equivalence modulo squares in A0 (component-wise).
			if issquare_ab eq <true:i in factors> then
				same_elements:=Append(same_elements,<a,b[#factors+1]>);
				break;
			end if;
		end for;
	end for;
	subgrp_SS:=sub<SG | [g[2]: g in same_elements]>;

//The following part computes the subgroup of Selmer Group SG
//coming from the Torsion subgroup.

	T, TtoJ := TorsionSubgroup(J);
	TinSG:= compute_TinSG(T, TtoJ, f, A, A0, M, ImgSGinA0, SG);

	return <SG, SGtoA, subgrp_SS, #SG/#subgrp_SS, TinSG, A, A0, M>;
end function;


////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

compute_orbits := function(gal, diff_set)
       	orb_rep :={};
	completed_set := {};
	for i in diff_set do
       	if not (i[1] in completed_set) then
	completed_set := Include(completed_set,i[1]);
	completed_set := Include(completed_set,-i[1]);
		orb_i := {i[1]};
		for g in gal do
			if (g(i[1]) in orb_i) or (-g(i[1]) in orb_i) then
				continue;
			else
			orb_i :=Include(orb_i, g(i[1]));
			completed_set := Include(completed_set,g(i[1]));
			completed_set := Include(completed_set,-g(i[1]));
			end if;
		end for;
		orb_rep := Include(orb_rep, i);
	end if;
	end for;
	return orb_rep;
end function;


////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////


nice_SG_elts := function(f, N, SG, SGtoA, SS_grp, TinSG)
	roots_f := Roots(f,N); //f transfered should be monic and N its splitting field
	goodpts := [];
	known_part := SS_grp+TinSG;	 //SS_grp is the subgroup generated by Selmer Set
					//TinSG is the subgroup of SG generated by torsion

	diff_roots_f:=[]; //to store difference of roots of f upto multiplication by -1 i.e. out of ei-ej and ej-ei only one is saved
	for i in [1..5] do
		for j in [i+1..5] do
			diff_roots_f:=Append(diff_roots_f,<roots_f[i][1]-roots_f[j][1],i,j>);   // we also store the positions of the roots whose difference is taken
		end for;
	end for;

//the idea in the following is to keep updating the known_part by the
//subgroup generated by the previous known_part and the new good point of
//SG found (the one satisfying some more properties)

	for g in SG do
	if not (g in known_part) then
		d := [Evaluate(SGtoA(g), i[1]): i in roots_f];

//d=[d1,d2,d3,d4,d5] corresponding to [e1,e2,e3,e4,e5] where ei are the roots of f.
//This is done by taking the representation of g in A and evaluating the representative
//polynomial at each of the roots of f.


//next 3 lines in the code are to compute the orbits of the
//set diff_roots_f under the galois Group gal using the function
//compute_orbits which outputs orbit representatives.

		gal := Automorphisms(N);
		diff_orbits := compute_orbits(gal, diff_roots_f);
		diff_orbits := Setseq(diff_orbits);
		// MS: The following (until *** below) can be done as follows.
		// if forall{i : i in diff_orbits | HasRationalPoint(Conic([i[1], d[i[2]], -d[i[3]]]))} then
		true_val:=[];
		for i in diff_orbits do
			Cij := Conic([i[1],d[i[2]],-d[i[3]]]);
			if HasRationalPoint(Cij) eq true then
				true_val:=Append(true_val, true);
			else // MS: the else branch can be omitted
				continue;
			end if;
		end for;
		if #true_val eq #diff_orbits then
		// ***
			goodpts:= Append(goodpts, g);
			known_part := sub<SG | known_part, g>;//updating the known_part
		end if;
	end if;

	if known_part eq SG then //known_part is already SG then no point in going forward
		break;
	end if;
	end for;

	return goodpts;
end function;


////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

work_prog := function(f)
	C := HyperellipticCurve(f); //create hyperellipticcurve
	C := convert_monic_integral(C); //creat an isomorphic curve which is defined by monic and integral model odd deg polynomial
	f_new := HyperellipticPolynomials(C);
	J := Jacobian(C);
	T, TtoJ := TorsionSubgroup(J);
	tor_rk := #T/#(2*T);
	SG, SGtoA := TwoSelmerGroup(J);
	if tor_rk eq #SG then //not and interesting curve BSD verified
		return <0,SG,SGtoA, SG, []>;
	end if;

	value := SS_computation(C);

	if #SG/#(value[3]+value[5]) eq 1 then //curve where selmer_set+ torsion equals selmer group
	// MS: if #SG eq #(value[3] + value[5]) then
		return <0, SG, SGtoA, SG, []>;
 
	else
		N := SplittingField(f_new);
		if Degree(N) ge 31 then //not-tested curves possibly good
			return <3,SG,SGtoA, SG, []>;
		end if;
		goodpts := nice_SG_elts(f_new,N, value[1],value[2],value[3], value[5]);

		if #goodpts  ge 1 then //provably good curves
			return <4, value[1], value[2], value[3]+value[5], goodpts>;
		end if;
	end if;
	return <1, value[1], value[2], value[3]+value[5], []>;
	//good curve with no good points but Selmer set does not generate the Selmer Group.
end function;


////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////


search_curves := function(odd_deg_models)

bad_curves:=[];
good_curves:=[];
non_tested_gc := [];
gcgp := [];
iteration := 0;
for f in odd_deg_models do
	iteration := iteration+1;
	print iteration;
	value := work_prog(f);
	if value[1] eq 0 then
		bad_curves := Append(bad_curves,f);
	elif value[1] eq 3 then
		non_tested_gc := Append(non_tested_gc,f);
	elif value[1] eq 1 then
		good_curves := Append(good_curves, f);
	else
		good_subgroup := sub<value[2]| value[4], value[5]>;
		print f, #value[2]/#value[4], #value[2]/#good_subgroup;
		gcgp := Append(gcgp, f);
	end if;
end for;
return <bad_curves, good_curves, non_tested_gc, gcgp>;
end function;

//=========================================================================

// MS:
// This uses only convert_monic_integral() from above.

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

function invert_SGtoA(SGtoA, SG)
  // Produce a map that inverts SGtoA.
  // (There are more efficient ways of doing this, but this should be OK.)
  A := Domain(SGtoA);
  // Splitting of the étale algebra as a product of number fields
  // (use DoLinearExtension to make sure to produce a FldNum and have K.1 = root)
  A0 := [NumberField(e[1] : DoLinearExtension) : e in Factorization(Modulus(A))];
  maps := [hom<A -> K | K.1> : K in A0];
  // Find the images of the Selmer group elements in the product.
  SGtups := [<<m(a) : m in maps> where a := s@@SGtoA, s> : s in SG];
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

function SS_and_T_in_SG(C, SScomp)
  //C := convert_monic_integral(C);
  f := HyperellipticPolynomials(C);
  J := Jacobian(C);
  // Compute the 2-Selmer group
  SG, SGtoA :=TwoSelmerGroup(J);
  AtoSG := SGtoA;
  A := Domain(SGtoA);
  T, TtoJ := TwoTorsionSubgroup(J);
  // Reduce to 2-primary subgroup
  //T2 := pPrimaryComponent(T, 2);
  TinSG := sub<SG | [x_minus_T(TtoJ(t), f, A, SGtoA) : t in OrderedGenerators(T)]>;
  if #TinSG eq #SG then 
	return SG, {2*SG.1}, SG, SGtoA, AtoSG;
  end if;
  // Compute the 2-Selmer set
  if SScomp then
  SS, AtoSS := TwoCoverDescent(C);
  A1 := Domain(AtoSS);	
  assert Modulus(A) eq Modulus(A1);
  A1toA := hom<A1 -> A | A.1>;
  // Find the images of the elements of SS in SG
  SSinSG := {AtoSG(A1toA(s @@ AtoSS)) : s in SS}; // image of Selmer set in Selmer group
  // Compute the torsion subgroup
  
  else 
  SSinSG := {Identity(SG)};
  end if;
  
  return SG, SSinSG, TinSG, SGtoA, AtoSG;
end function;

function good_subgroup(known_part, SGtoA, SG)
  f := Modulus(Domain(SGtoA));
  bad := PrimeDivisors(2*Integers()!Norm(Discriminant(f)));
  ff := [e[1] : e in Factorization(f)];
  // For each factor, take a representative root
  // and consider another root of the same or a later factor.
  A := Domain(SGtoA);
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
                  a := s@@SGtoA; // image in A
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
  // also return the good_elts for later uses;
  good_elts := [];
  for s in SG do
    if s notin known_part and forall{t : t in tests | t(s)} then
      known_part +:= sub<SG | s>; Append(~good_elts, s);
    end if;
  end for;
  return known_part, good_elts;
end function;

function is_good(C, SScomp)
  // This returns
  // (1) the Selmer group SG as an abstract abelian group
  // (2) the image of the torsion subgroup of the Jacobian in SG
  // (3) the image of the Selmer set in SG as a set	
  // (4) the subgroup generated by "good" elements of SG
  SG, SSinSG, TinSG, SGtoA, AtoSG := SS_and_T_in_SG(C, SScomp);
  SStors := sub<SG | SSinSG> + TinSG;
  try 
  good, good_elts := good_subgroup(SStors, SGtoA, SG);
  catch e
  print HyperellipticPolynomials(C);
  return 0;
  end try;
  return (#quo<SG|good> in [1..2]), SG, TinSG, SSinSG, SStors, AtoSG, SGtoA, good, good_elts;
end function;

function fast_curves_search(odd_deg_models)
   for f in odd_deg_models do 
      val := is_good(HyperellipticCurve(f)); 
         if val ne 1 then 
	    print f; 
	 end if;
	 print val;
    end for;
    return 0;
end function;



