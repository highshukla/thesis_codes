//This is the code for runing on the curves, the associated
//jacobians to which have analytic rank 0.

Qx<x>:=PolynomialRing(Rationals());
compute_pol:=function(a)
	pol:=0;
	for i in [1..#a] do 
		pol:=pol+a[i]*x^(i-1);
	end for;
	return pol;
end function;

/*load "g2c_curves.m";

curves:=[];
for i in data do 
	curves:=Append(curves,HyperellipticCurve(compute_pol(i[1]),compute_pol(i[2])));
end for;

odd_deg_models:=[];
for i in curves do 
	a,b,c:=HasOddDegreeModel(i);
	odd_deg_models:=Append(odd_deg_models,b);
end for;
*/

convert_monic_integral := function(C)
	C := IntegralModel(C);
	f := HyperellipticPolynomials(C);
	if IsMonic(f) eq false then
                a := LeadingCoefficient(f);
                b := a^2;
                f := b^2*Evaluate(f,x/a );
                C := HyperellipticCurve(f); 
	end if;
	return C;
end function;


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
					b := f/j[1]; 
					b := Qx!b;
                                        j_n := (-1)^(Degree(j[1]))*Evaluate(j[1],A.1);
                                        b := (-1)^(Degree(f)-Degree(a))*Evaluate(b,A.1);
                                        c := j_n+b;
                                        prod_a := prod_a*c;
                                else //if j does not divide f
                                        c := (-1)^(Degree(j[1]))*Evaluate(j[1],A.1);
					prod_a := prod_a*c;			  
	   			end if;
                        end for;
				prod_a := <m(prod_a): m in M>;
                                tors_list_in_A := Append(tors_list_in_A, prod_a);
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


nice_SG_elts := function(f, N, SG, SGtoA, SS_grp, TinSG)
	roots_f := Roots(f,N); //f transfered should be monic and N its splitting field
	goodpts := [];
	known_part := SS_grp+TinSG;	 //SS_grp is the subgroup generated by Selmer Set 
					//TinSG is the subgroup of SG generated by torsion
	
	
	//the idea in the following is to keep updating the known_part by the 
	//subgroup generated by the previous known_part and the new good point of 
	//SG found (the one satisfying some more properties)
	
	diff_roots_f:=[];
	for i in [1..5] do 
		for j in [i+1..5] do 
			diff_roots_f:=Append(diff_roots_f,<roots_f[i][1]-roots_f[j][1],i,j>);   //in this we keep the difference of roots of f along with the positions of the roots
     //whose difference is taken.
		end for;
	end for;


	for g in SG do
	if not (g in known_part) then 
		d := [Evaluate(SGtoA(g), i[1]): i in roots_f]; 
		//d=[d1,d2,d3,d4,d5] corresponding to [e1,e2,e3,e4,e5] where ei are the roots of f. This is done by taking the representation of g in A and evaluating the representative polynomial at each of the roots of f.
		


//next 3 lines in the code are to compute the orbits of the 
//set diff_roots_f under the galois Group gal using the function 
//compute_orbits which outputs orbit representatives.  
		
		gal := Automorphisms(N);
		diff_orbits := compute_orbits(gal, diff_roots_f);
		diff_orbits := Setseq(diff_orbits);
		true_val:=[];
		for i in diff_orbits do
			Cij := Conic([i[1],d[i[2]],-d[i[3]]]);
			if HasRationalPoint(Cij) eq true then 
				true_val:=Append(true_val, true);
			else
				continue;
			end if;
		end for;
		if #true_val eq #diff_orbits then
			goodpts:= Append(goodpts, g);
			known_part := sub<SG | known_part, g>;   //updating the known_part
		end if;
	end if;

	if known_part eq SG then //known_part is already SG then no point in going forward
		break;
	end if;
	end for;
	
	return goodpts;
end function;



work_pro := function(f)
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




search_curves := function(odd_deg_models)

bad_curves:=[];
good_curves:=[];
non_tested_gc := [];
gcgp := [];
iteration := 0;
for f in odd_deg_models do
	iteration := iteration+1;
	print iteration;
	value := work_pro(f);
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

