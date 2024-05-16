divbylmdpol := function()
	cyc5 := CyclotomicField(5);
	O<x1,x2,y1,y2, A, P, S> := PolynomialRing(cyc5,7);
	K := FieldOfFractions(O);
	z := cyc5.1;
	mat := [x1^(3-i): i in [0..3]] cat [(z*x1)^(3-i) : i in [0..3]] cat [x2^(3-i): i in [0..3]] cat [(z*x2)^(3-i): i in [0..3]];
	M := Matrix(K, 4,4, mat);
	assert Determinant(M) ne 0;
	coef := M^(-1)*Matrix(K,4,1,[y1,-y1, y2, -y2]);
	coef := [coef[j][1]: j in [1..4]];
	Ncoef := [Numerator(coef[j]): j in [1..#coef]];
	Dcoef := [Denominator(coef[j]): j in [1..#coef]];
	B1 := Ncoef[1]^2*Dcoef[4]^2*(x1*x2)^2*z^2;
	A1 := Dcoef[1]^2*(Ncoef[4]^2-Dcoef[4]^2*A);
	A2 := 2*Ncoef[1]*Dcoef[1]*Ncoef[2]-Dcoef[1]^2*Dcoef[2]+Dcoef[2]*Ncoef[1]^2*(x1+x2)*(1+z);
	B2 := Dcoef[2]*Ncoef[1]^2;
	//Removing even powers of y1 and y2 in As and Bs.
	alpha := [A1, A2, B1, B2];
	for i in [1..4] do
		cy := Coefficients(alpha[i],y1);
		alpha[i] := &+[cy[j+1]*(x1^5+A)^(Floor(j/2))*y1^(j-2*Floor(j/2)): j in [0..#cy-1]];
		cy := Coefficients(alpha[i], y2);
		alpha[i] := &+[cy[j+1]*(x2^5+A)^(Floor(j/2))*y2^(j-2*Floor(j/2)): j in [0..#cy-1]];
	end for;
	alpha1 := [Coefficient(alpha[j], O.3,0): j in [1..#alpha]];
	alpha2 := [Coefficient(Coefficient(alpha[j], O.3,1),O.4,1): j in [1..#alpha]];
	eq1 := (alpha1[1]-P*alpha1[3])^2-(alpha2[1]-P*alpha2[3])^2*(x1^5+A)*(x2^5+A);
	eq2 := (alpha1[2]-S*alpha1[4])^2-(alpha2[2]-S*alpha2[4])^2*(x1^5+A)*(x2^5+A);
	c1 := Coefficients(eq1, P);	
	g1 := Gcd(c1);
        c1 := [O!(t/g1): t in c1];
	e1 := &+[P^i*c1[i+1]: i in [0..2]]; //removing the common factors in eq1
	c2 := Coefficients(eq2, S);	
	g2 := Gcd(c2);
        c2 := [O!(t/g2): t in c2];
	e2 := &+[S^i*c2[i+1]: i in [0..2]]; //removing the common factors in eq2	
	//Need to use the structure of the coefficients of y1y2 and the constant term as a polynomial in y1 and y2 of the elements of alpha. Maybe some simplicfication appears in finding the local points.	
	h1 := &cat([[h: h in HomogeneousComponents(c)| h ne 0]: c in c1]);
	h2 := &cat([[h: h in HomogeneousComponents(c)| h ne 0]: c in c2]);
	//verifying that each of the homogeneous components have same power of A in all the terms.
	assert [#[x : x in Coefficients(h, A)| x ne 0]: h in h1] eq [1: h in h1];
	assert [#[x : x in Coefficients(h, A)| x ne 0]: h in h2] eq [1: h in h2]; 
	//verifying no collisions in any of the homogeneous components.
	assert #Set([Degree(h)-Degree(h,A): h in h1]) eq #[Degree(h)-Degree(h,A): h in h1];
	assert #Set([Degree(h)-Degree(h,A): h in h2]) eq #[Degree(h)-Degree(h,A): h in h2];
	j := Matrix(K, 2,2, [Derivative(e1, O.i): i in [1..2]] cat [Derivative(e2, O.i): i in [1..2]]);
	J := Determinant(j);
	Degree(O!J);


	return e1, e2, J;
end function;

//Notes : The gcd of coefficients in eq1 wrt P and eq2 wrt S has same factors although the multiplicity might differ. The factors or GCD are := x1,x2,x1-x2,x1-zeta*x2, x1-zeta^(-1)*x2.
//These cases have to be dealt separately because the equation are set so that these cases do not occur. 


DivisionByLambda := function(A,P,S,z)
	eq1, eq2 := divbylmdpol(A);
	k := Parent(P); //defining field of the point on the jacobian
	O<x1,x2> := PolynomialRing(k,2);
	P := Parent(eq1);
	Eq := [eq1, eq2];
	Emk := hom<BaseRing(Parent(Eq[1]))-> k| z>; //embedding of cyc5 inside k
	h := hom<P->O| Emk, x1, x2, 0, 0, A, P, S>; //embedding of polynomial ring in x1,x2,y1,y2, A variable over cyc5 to a polynomial ring over k in the same variables. Note that eq1 and eq2 do not have y1 or y2 appearing in them. 
						    //
	Eq := [h(Eq[j]): j in [1..2]]; //coercing inside polynomial ring over the local field k.
	ok := IntegerRing(k); 
	pi := UniformizingElement(ok);
	v := Min([Valuation(c): c in Coefficients(Eq[1])]);
	Eq[1] := pi^(-v)*Eq[1];
	v := Min([Valuation(c): c in Coefficients(Eq[2])]);
	Eq[2] := Eq[2]*pi^(-v);
//making at least one coefficient a unit in Ok. 	
//Construct the quotient ring mod higher power of maximal ideal.
//Check if eq1 and eq2 have some interesting factors left between them. 
end function;


