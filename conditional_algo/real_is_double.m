//Currently only for case when the defining polynomial of the curve splits
//completely.
// --hs


//ToRevert 1) removal of addition of half1
//2) uncomment assertions
function IsDouble_inf(J, pt)
  // pt: a point on an odd degree hyperelliptic Jacobian
   //assert Type(J) eq JacHyp;
  f, h := HyperellipticPolynomials(Curve(J));
  error if h ne 0, "Curve must be of the form y^2 = f(x).";
  error if IsEven(Degree(f)), "Curve must be of odd degree.";
  lcf := LeadingCoefficient(f);
  error if not IsSquare(lcf), "Polynomial in curve equation must be monic."; // for now...
  P := Parent(f); x := P.1;
  Qv := BaseRing(P);
  if pt eq [P!1, P!0, P!0] then 
    if Roots(f) ne [] then
    return true, J![P.1-Roots(f)[1][1], P!0]; 
    else return false,_;
    end if;
  end if;
  g := Degree(f) div 2; // the genus; deg(f) = 2g+1
  a := pt[1];
  b := pt[2]; // Polynomials defining pt
  // split off square part of a
  if Degree(realGCD(a, Derivative(a))) eq 0 then
    a0 := P!1;
    a1 := a;
  else
  facta := [<P.1-r[1],r[2]>: r in Roots(a)];
    a0 := &*[P | e[1]^(e[2] div 2) : e in facta];
    a1 := &*[P | e[1] : e in facta | IsOdd(e[2])];
  end if;
  
  //assert locPolEq(a, a0^2*a1);
  half1 := <a0, b mod a0>;
  a := a1; b := b mod a1;
  if Degree(a1) eq 0 then return true, half1; end if;
  ffact := [P.1-e[1] : e in Roots(f)]; // irreducible factors of f
  rootf := [r[1]: r in Roots(f)]; //roots of f
  algs := [ [* A, t, q *] where t := q(x) where A, q := quo<P | p> : p in ffact ];
    // the corresponding field extensions with the images of x and the quotient map
  deg := Degree(a); sign := (-1)^deg;
  d := realGCD(a, f);
  if Degree(d) gt 0 then
    a1 := ExactQuotient(a, d); f1 := ExactQuotient(f, d);
    aa := sign*(a - a1*f1);
  else
    aa := sign*a;
  end if;
  sqrts_aug := <>;
  impt_aug := <Evaluate(aa, e): e in rootf>;
  for i := 1 to #impt_aug do 
    flag, s := IsSquare(impt_aug[i]);
    if flag then Append(~sqrts_aug, s); else return false, _; end if;
  end for;

  impt := <algs[i][1]!impt_aug[i]: i in [1..#ffact]>;
  sqrts := <algs[i][1]!sqrts_aug[i]: i in [1..#ffact]>;      
  //aa, locCR([impt[i]@@algs[i][3]:i in [1..5]],ffact);
  
  /*impt := <Evaluate(aa, e[2]) : e in algs>; // image under x-T map

  sqrts := <>;
  // check if impt is a square and record square roots
  for i := 1 to #impt do
    flag, s := IsSquare(impt[i]);
    if flag then
      Append(~sqrts, s);
    else
      return false, _;
    end if;
  end for;
  */
  K := BaseField(J);
  // helper function, gives coefficients of x^j*pol1 mod pol2 as sequence
  function shcof(j, pol1, pol2)
    pol := (x^j*pol1) mod pol2;
    return [Coefficient(pol, i) : i in [0..Degree(pol2)-1]];
  end function;
  // now set up linear system for coefficients of polynomials q, u, v
  // of degrees <= g, < deg/2, <= g + deg/2, respectively,
  // satisfying   v = q*s mod f  and  v = u*b mod a  (if d=1)
  // or  v = q*s mod f1,  v = 0 mod d,  u*f1 = q*s' mod d  and  v = u*b mod a1  (if d /= 1)
  if Degree(d) eq 0 then
    // lift tuple sqrts to an element mod f
    s := realCR([sqrts[i] @@ algs[i][3] : i in [1..#algs]], ffact);
    //return Gcd(s^2-aa,  f);
    
    //!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
    //assert realPolEq((s^2 - aa) mod f, P!0);//need to correct for precision for this
            // //assertion
    //!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!        
    // set up matrix: first g+1 rows <--> q, given by (x^j*s mod f, 0 mod a)
    //                next [(deg-1)/2]+1 rows <--> u, given by (0, x^j*b mod a)
    //                last g+[deg/2]+1 rows <--> v, given by (-x^j mod f, -x^j mod a)
    za := [K| 0 : j in [0..deg-1]];
    zf := [K| 0 : j in [0..2*g]];
    du := (deg-1) div 2; // max. degree of u
    dv := g + (deg div 2); // max. degree of v
    mat := Matrix([shcof(j, s, f) cat za : j in [0..g]]
                    cat [zf cat shcof(j, b, a) : j in [0..du]]
                    cat [shcof(j, -1, f) cat shcof(j, -1, a) : j in [0..dv]]);
    // solve

    
    ker := Kernel(mat);
    dim := Dimension(ker);
    // want q of smallest degree, reduce by dim(ker)-1
    if dim gt 1 then
      ker meet:= Kernel(VerticalJoin(<ZeroMatrix(K, g-dim+2, dim-1),
                                      IdentityMatrix(K, dim-1),
                                      ZeroMatrix(K, g+deg+1, dim-1)>));
      dim := Dimension(ker);
    end if;
    assert dim eq 1;
    kervec := Basis(ker)[1];
    // extract polynomials
    q := P![kervec[j+1] : j in [0..g]];
    u := P![kervec[j+g+2] : j in [0..du]];
    v := P![kervec[j+g+du+3] : j in [0..dv]];
    // and normalize
    lcq := LeadingCoefficient(q);
    q *:= 1/lcq; u *:= 1/lcq; v *:= 1/lcq;
     //assert realPolEq(u^2*f, v^2 - aa*q^2);
    // extract half: essentially given by (q, r)  where  r*u = -v mod q
    gcd, r1 := realXGCD(u, q);
    q1 := ExactQuotient(q, gcd); u1 := ExactQuotient(u, gcd); v1 := ExactQuotient(v, gcd);
    if Degree(gcd) eq 0 then
      r := (-v*r1) mod q;
      half := <q, r, Degree(q)>;// + half1;
    else
      df := realGCD(gcd, f);
      da := realGCD(gcd, a);
      _, r1 := realXGCD(u1, q1*da);
      r2 := (-v1*r1) mod (q1*da);
      r := realCR([P!0, r2], [df, q1*da]);
      half := <q, r, Degree(q)>;// + half1;
    end if;
     //assert 2*half eq pt;
    return true, half;
  else // d nontrivial
//     printf "gcd(a, f) = %o\n", d;
    // lift sqrts to elements mod f1 and mod d
    inds1 := [i : i in [1..#ffact] | IsDivisibleBy(d, ffact[i])];
    inds2 := [i : i in [1..#ffact] | i notin inds1];
    s := realCR([sqrts[i] @@ algs[i][3] : i in inds2], ffact[inds2]);
    sp := realCR([sqrts[i] @@ algs[i][3] : i in inds1], ffact[inds1]); // s'
     //assert realPolEq((s^2 - sign*a) mod f1,P!0);
     //assert realPolEq((sp^2 + sign*a1*f1) mod d, P!0);
    df1 := Degree(f1);
    da1 := Degree(a1);
    // take v = d*v1 and solve for v1
    du := (deg-1) div 2; // max. degree of u
    dv1 := g + (deg div 2) - Degree(d); // max. degree of v1
    // set up matrix: first g+1 rows <--> q, given by (x^j*s mod f1, 0 mod a1, -x^j*sp mod d)
    //                next [(deg-1)/2]+1 rows <--> u, given by (0, x^j*b mod a1, x^j*f1 mod d)
    //                last g+[deg/2]+1-Degree(d) rows <--> v1,
    //                                given by (-x^j*d mod f1, -x^j*d mod a1, 0 mod d)
    za1 := [K| 0 : j in [0..da1-1]];
    zf1 := [K| 0 : j in [0..df1-1]];
    zd := [K| 0 : j in [0..Degree(d)-1]];
    mat := Matrix([shcof(j, s, f1) cat za1 cat shcof(j, -sp, d) : j in [0..g]]
                    cat [zf1 cat shcof(j, b, a1) cat shcof(j, f1, d) : j in [0..du]]
                    cat [shcof(j, -d, f1) cat shcof(j, -d, a1) cat zd : j in [0..dv1]]);
    // solve
    ker := Kernel(mat);
    dim := Dimension(ker);
    // want q of smallest degree, reduce by dim(ker)-1
    if dim gt 1 then
      ker meet:= Kernel(VerticalJoin(<ZeroMatrix(K, g-dim+2, dim-1),
                                      IdentityMatrix(K, dim-1),
                                      ZeroMatrix(K, g+deg+1-Degree(d), dim-1)>));
      dim := Dimension(ker);
    end if;
     assert dim eq 1;
    kervec := Basis(ker)[1];
    // extract polynomials
    q := P![kervec[j+1] : j in [0..g]];
    u := P![kervec[j+g+2] : j in [0..du]];
    v := P![kervec[j+g+du+3] : j in [0..dv1]];
    // and normalize
    lcq := LeadingCoefficient(q);
    q *:= 1/lcq; u *:= 1/lcq; v *:= 1/lcq;
     assert u^2*f1 eq v^2*d - sign*a1*q^2;
    gcd, r1 := realXGCD(u, q);
    q1 := ExactQuotient(q, gcd); u1 := ExactQuotient(u, gcd); v1 := ExactQuotient(v, gcd);
    if Degree(gcd) eq 0 then
      r := (-d*v*r1) mod q;
      half := <q, r, Degree(q)>;// + half1;
    else
      df := realGCD(gcd, f);
      da := realGCD(gcd, a1);
      _, r1 := realXGCD(u1, q1*da);
      r2 := (-d*v1*r1) mod (q1*da);
      r := realCR([P!0, r2], [df, q1*da]);
      half := <q, r, Degree(q)>;// + half1;
    end if;
     //assert 2*half eq pt;
    return true, half;
  end if;
end function;


