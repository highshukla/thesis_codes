
//This script is under developement. Can even raise syntax errors.
//good_elts is already given as sequence of elements in the Etale algebra A;

adjustPv := function(Pv, chi_val , complexWPts)
  S := Subsets(complexWPts);
  for s in S do 
    Pv := 
  
realCTP:= function(ctpMat,WPts_nf,globmats, S, f, good_elts, real_mor)
  bf := Domain(real_mor);
  l := Degree(f);
  defS := DefiningPolynomial(S);
  C := ComplexField(Precision(Codomain(real_mor)));
  Ct := PolynomialRing(C);
  R := Codomain(real_mor);
  f := Polynomial([real_mor(c): c in Coefficients(f)]);
  rS := Roots(Polynomial([C!real_mor(x): x in ElementToSequence(defS)]))[1][1];
  complex_mor := hom<S -> C| x :-> &+[y[i]*rS^(i-1) where y := ElementToSequence(x): i in
    [1..#ElementToSequence(x)]]>;
  WPts := [complex_mor(pt): pt in WPts_nf];
  real_root_index := [i : i in [1..l]| almost_real(WPts[i])];
  complex_conjugate_index := &cat[[<i,j> : j in [i+1..l]]: i in [1..l-1]| i not in
    real_root_index and almost_real(WPts[i]+WPts[j])];
  

  for a in [1..#good_elts -1] do 
    g := Polynomial([real_mor(x): x in ElementToSequence(good_elts[a])]); 
    g := [Evaluate(g,pt): pt in WPts]; 
    chi_val := [i : i in real_root_index | Sign(Real(g[i])) eq -1];
    sqg := [1: i in [1..l]]; 
    for i in real_root_index do sqg[i]:= SquareRoot(Real(g[i])); end for;
    for pair in complex_conjugate_index do sqg[pair[1]] := SquareRoot(g[pair[1]]);
      sqg[pair[2]]:= ComplexConjugate(sqg[pair[1]]);
    end for;
    if chi_val eq [] then 
      //here we code the previous one.
    end if;
    sortseq := real_root_index;
    Sort(~sortseq , func<s1,s2| Real(WPts[s1])-Real(WPts[s2])>);
    newwpts := [WPts[i]: i in sortseq];
    newg := [g[s]: s in sortseq];
    signchanges := [i : i in [1..#real_roots_index-1]| Real(newg[i]*newg[i+1]) lt 0];
    pts := [Min(Real(newwpts[i]+1), Real(newwpts[i]+newwpts[i+1])/2) : i in signchanges];
    pts := [[pt, SquareRoot(Evaluate(f, pt))]: pt in pts];
    dega := #pts;
    M := Transpose(Matrix(C, dega, dega, [[x[1]^(dega-i) : i in [1..dega]]: x in pts]));
    vec := Vector(C, dega, [x[2] : x in pts]);
    coef := Solution(M,vec); temp := ElementToSequence(coef); coef := [temp[dega-i]: i in [0.. dega -1]];
    mumpol2 := Ct!Polynomial(coef); mumpol1 := &*[Ct.1-x[1]: x in pts];
    assert forall{t: t in real_root_index|
      Real((-1)^dega*Evaluate(mumpol1,WPts[t]))/Real(g[t]) gt 0};
    print "local points:", [mumpol1,mumpol2];
    flag , Pv := IsDouble_inf(BaseChange(J,C), [mumpol1,mumpol2]);
    ca := ElementToSequence(Pv[1]); ca[Degree(Pv[1])+1] := C!1; Pv[1]:= Ct!Polynomial(ca);
    assert flag eq true;


    Gmat := globmats[a][1];
    Pgv := IdentityMatrix(C,l);
    for t in [1..l-1] do for h in [t+1..l] do 
        gpt := GPts[t][h]; Pgv[t][h] :=
        complex_mor(gpt[1])*sqg[t]+complex_mor(gpt[2])*sqg[h];
        Pgv[h][t] := Pgv[t][h];
    end for; end for;

    print "locpt and halfpt computed";
    genus := l div 2;
    f := ChangeRing(f,C);
    flag, fctn := IsRealPrincipalDivisor([WPts[t]]: t in chi_val)

      
