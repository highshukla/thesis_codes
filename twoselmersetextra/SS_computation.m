SS_computation:=function(C)

	J:=Jacobian(C);
	f:=HyperellipticPolynomials(C);
	factors:=Factorization(f);
	A0:=CartesianProduct([NumberField(i[1]): i in factors]); //defining A0 to be the cartesian product of Number fields corresponding to the irreducible factors of f
	SG, SGtoA :=TwoSelmerGroup(J);    //computing selmer group of J
	if #SG eq 1 then 
		return 1;
	end if;
	A:=Codomain(SGtoA);    //computing the etale algebra 
	try
		SS, AtoSS:=TwoCoverDescent(C); //computing two selmer set data (I do not know if it computes two selmer set exactly)
		catch e
		return 0; //return 0 if there is an error in TwoCoverDescent(C).
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
	return [same_elements, SS, SG, AtoSS, SGtoA, #ImgSSinA0];

end function;
