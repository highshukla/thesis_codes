/*Functions in this file: 
 * 1) Pairing
 * 2) comp_Partial
 * 3) comp_epsilon
 * 4) nxtPtCnc
 * 5) globMatPij
 */ 





Pairing := function(f, D, flag)
  K := Parent(f);
  x := K.1;
  y := K.2;
  tamesym := 1;
  prod := 1;
  for plc in Support(D) do
    vd := Valuation(D,plc);
    P := RepresentativePoint(plc);
    vf := Valuation(f, P);
    tamesym := tamesym * (-1)^(vf*vd);
    if P[3] eq 0 then tp := x^2/y; elif P[2] eq 0 then tp := (x-P[1])/y; else tp := x-P[1];
    end if;
    prod := prod * (P@(f*tp^(-vf)))^(vd);  
  end for;
  if flag eq 1 then return prod; else return tamesym*prod; end if;
end function;


fraka := function(chi_val, C, WPts)
  inf := Place(C![1,0,0]);
if chi_val eq SequenceToSet([1..#WPts]) then return DivisorGroup(C)!0; end if;
return Divisor([<Place(C![WPts[i],0,1]),1>: i in chi_val] cat [<inf, -#chi_val>]);
end function;





CbdFraka := function(cs, ct, C, WPts)
  l := #WPts;
  cts := (cs meet ct) join (SequenceToSet([1..l]) diff (cs join ct));
  return fraka(cs, C, WPts) + fraka(ct, C, WPts)-fraka(cts, C, WPts);
end function;





compute_eta := function(cs, ct, ctd,crd, i,C, WPts)
if crd eq 1 then return 1; end if;
parta := CbdFraka(cs, ct, C, WPts); bool, g := IsPrincipal(parta); 
assert bool eq true;
kC := Parent(g);
assert Evaluate(DefiningPolynomial(C),[kC.1, kC.2, 1]) eq kC!0;
val := Pairing(g, Divisor([<Place(C![WPts[i],0,1]), 1>, <Place(C![1,0,0]), -1>]), 1);
if ctd eq -1 then 
val := val/Pairing(kC.1-WPts[i], fraka(cs, C, WPts), -1);
end if;
return val;
end function;




//compute the coboundary of element of the Galois module Div

comp_Partial:= function(g, mumrep ,D)

//if a divisor is given and not the Mumford rep of a point
if mumrep eq [] then
  // function to compute g(D)-D where g has a valid action on the coordinates
  // of points on the support of D.
  C := Curve(D); 
  val := -D;
  D := Decomposition(D);
  for d in D do 
  P := RepresentativePoint(d[1]); P_g := Place(C![g(x): x in ElementToSequence(P)]);
  val := val + Divisor([<P_g, d[2]>]);
  end for;
  return val;
end if;

//if a point on the Jacobian of hyperelliptic curve is given in Mumford
//representation.
if mumrep ne [] then 
  a := mumrep[1];
  b := mumrep[2];
  //still need to interpret this in the field of functions over C
  Da := Divisor(a);
  val := -(&+[Valuation(P, D)*P : P in Support(Da)| P[2] eq Evaluate(b, P[1])]);
  Kvt := Parent(a);
  a := Polynomial([g(x) :x in ElementToSequence(a)]);
  b := Polynomial([g(x): x in ElementToSequence(b)]);
  Da := Divisor(a);
  val := val + &+[Valuation(P, D)*P : P in Support(Da)| P[2] eq Evaluate(b, P[1])];
  return val;
end if; 
end function;


comp_epsilon := function(c, i, c_dp)
/*val := ([t[2]: t in epsilon| t[1] eq c][1][i]); 
if c_dp eq 1 then return val, [],[]; 
else return val/(Pval[i]),[],[];
end if;*/
//construct a function comp_epsilon which returns epsilon_i given the glob
//matrix Pg and the chi val and i. 
//Currently it is done only till l=5
//Return value is sign, seq1 of pij, seq2 of sij, where each element of the
//sequence is a triple of the form <i,j,sign>, where i, j represent which
//indexing for pij (resp sij) and sign represents if it is 1/pij or pij.







zero := SequenceToSet([1..5]);
if (c_dp eq -1 and c eq zero) then return 1,[<i,j,-1>: j in [1..5]| j ne i],[];
end if;
if (c_dp eq 1 and c eq zero) then return 1, [], []; end if;
if (c_dp eq -1 and c eq {i}) then return 1, [], []; end if;
if c_dp eq 1 then
  if i in c then 
    if #c eq 1 then return 1, [<i,j,1>: j in [1..5]| j ne i], [];
    else  return -1, [<i,j,1>: j in [1..5]| j notin c], [<i,j,1>: j in c| j ne i]; 
    end if;
  else 
    if #c eq 1 then return 1, [<i,j,1>: j in c],[];
    else return -1, [<i,j,1>: j in c], [];
    end if;
  end if;
else  
  if #c eq 1 then return  1, [<i,j,-1>: j in zero diff (c join {i})], [];
  else  
    if i in c then
    return -1, [<i,j,-1>: j in c| j ne i], [<i,j,1>: j in c| j ne i]; 
    else
    return -1, [<i,j,-1>: j in zero diff (c join {i})], [];
    end if;
  end if;
end if;


end function;




verifyepsilon := function(Pg, WPts, K, C, sqrtg,i, dp)
  G, s, m := AutomorphismGroup(K);
  l := #WPts;
  zero := SequenceToSet([1..l]);
  flag := IsSquare(K!dp); 
  if flag then sqdp := SquareRoot(K!dp); 
  pos_sig := [<<g,{t: t in [1..l]| m(g)(sqrtg[t]) eq sqrtg[t]}>, m(g)(sqdp)/sqdp>: g in G];
  else 
  pos_sig := [<g,{t: t in [1..l]| m(g)(sqrtg[t]) eq sqrtg[t]}>: g in G];
  pos_sig := &cat[[<t,1>, <t,-1>] : t in pos_sig];
  end if;
  for gs in pos_sig do
  for gtau in pos_sig do
    eps_val1 , pseq1, sseq1 := comp_epsilon(gtau[1][2],i,gtau[2]);
    if gtau[2] eq 1 then
    eps_val2, pseq2 , sseq2 := comp_epsilon(gs[1][2],i,gs[2]);
    else 
    eps_val2 := 1; pseq2 := []; sseq2 := [];
    end if;
    gst := (gs[1][2] meet gtau[1][2]) join (zero diff (gs[1][2] join gtau[1][2]));
    eps_val3, pseq3 , sseq3 := comp_epsilon(gst,i,gs[2]*gtau[2]);
    if gtau[2] eq 1 then 
    eps_val4:= 1; pseq4:=[]; sseq4:=[];
    else
    eps_val4, pseq4 , sseq4 := comp_epsilon(gs[1][2],i,gs[2]);
    end if;
    
    eta := compute_eta(gs[1][2], gtau[1][2], gtau[2], -1, i, C, WPts);
    
    if pseq1 ne [] then
    eps_val1 := eps_val1 *(&*[Pg[t[1]][t[2]]^(t[3]): t in pseq1]); end if;
    if sseq1 ne [] then
    eps_val1 := eps_val1 *(&*[(WPts[t[1]]-WPts[t[2]])^(t[3]): t in sseq1]); end if;
    //print eps_val1;
    if pseq2 ne [] then
    eps_val2 := eps_val2 *(&*[Pg[t[1]][t[2]]^(t[3]): t in pseq2]); end if;
    if sseq2 ne [] then
    eps_val2 := eps_val2 *(&*[(WPts[t[1]]-WPts[t[2]])^(t[3]): t in sseq2]); end if;
    //print eps_val2;
    if pseq3 ne [] then
    eps_val3 := eps_val3 *(&*[Pg[t[1]][t[2]]^(t[3]): t in pseq3]); end if;
    if sseq3 ne [] then
    eps_val3 := eps_val3 *(&*[(WPts[t[1]]-WPts[t[2]])^(t[3]): t in sseq3]); end if;
    //print eps_val3;
    if pseq4 ne [] then
    eps_val4 := eps_val4 *(&*[Pg[t[1]][t[2]]^(t[3]): t in pseq4]); end if;
    if sseq4 ne [] then
    eps_val4 := eps_val4 *(&*[(WPts[t[1]]-WPts[t[2]])^(t[3]): t in sseq4]); end if;
    //print eps_val4;
    val := m(gs[1][1])(eps_val1)*eps_val2/(eps_val3*eps_val4);
    
    if eta ne val then error "Verification of epsilon failed";
    print <gs[1][2],gs[2]>, <gtau[1][2], gtau[2]>;
    print "partial eps :", val;
    print "eta:", eta;
    error "Epsilon not verified";
    end if;
    
    //  if val ne K!eta then print gs, gtau; break;
  //  end if;
  end for;
  end for;
    
return 0; 

end function;




nxtPtCnc := function(coef, Pt)
  //Pt;
  assert &+[coef[i]* Pt[i]^2: i in [1..3]] eq 0; // check if the point is indeed on the
        // conic
  if forall{p : p in Pt | p ne 0} then return Pt; end if; //if all coordinates of Pt are
                                                          //non zero then just return Pt

 //make sure that the 3rd coordinate is 0 if at all any of them is zero
  zind := [x:x in [1..3]| Pt[x] eq 0][1]; 
  if zind ne 3 then Pt[zind]:= Pt[3]; Pt[3]:=0; temp := coef[zind];
    coef[zind]:= coef[3]; coef[3]:= temp;
  end if;

  for B in [1..11] do 
  for C in [1..10] do  
   //B; C; 
    x0 := Pt[1]; y0 := Pt[2];
    a := coef[1]; b := coef[2]; c := coef[3]; 
    if (C^2*b eq -B^2*c) or (C^2*b eq B^2*c) then continue; end if;
    x1 := 1; y1 := y0*(c*B^2-b*C^2)/(x0*(c*B^2+b*C^2)); 
    z1 := 2*B*y0*b*C^2/(x0*C*(b*C^2+c*B^2));
    newPt := [x1,y1,z1];
    assert &+[coef[i]*newPt[i]^2: i in [1..3]] eq 0;
    assert forall{p : p in newPt | p ne 0};
    // in case the zero coordinate was forced to be the third one then revert it again.
    if zind ne 3 then temp := newPt[zind]; newPt[zind]:= newPt[3]; newPt[3] := temp;
    end if;
    print "Pt on Conic:", [p/newPt[3]: p in newPt];
    return [p/newPt[3]: p in newPt]; //scale the z-coordinate to be 1. 
  end for;
  end for;
end function;



//function to compute the global matrix Pg with (i,j) entry representing pij
//(see manuscript)
globMatPij := function(g, WPts)
	l := #WPts;
  K := SplittingField([Polynomial([-d,0,1]): d in g]);
	sqrtg := <SquareRoot(K!d): d in g>;
	Pg := IdentityMatrix(K,l);
	for i:=1 to l do
		for j:=i+1 to l do 
    coef := [g[i],-g[j],WPts[i]-WPts[j]];
			Cij := Conic(coef);
   	Pt := RationalPoint(Cij);
    Pt := ElementToSequence(Pt);
    if not forall{p : p in Pt| p ne 0} then Pt := nxtPtCnc(coef, Pt); 
    end if;
    //transpose again if we did it before calling nxtPtCnc;
    x0 := Pt[1]; y0 := Pt[2]; Pg[i][j] := sqrtg[i]*x0 + sqrtg[j]*y0; 
    Pg[j][i] := Pg[i][j];
  	end for;
	end for;
	return Pg, sqrtg, K;
end function;


/*
new_eps := function(g, sqrtg, P, WPts, f)
  K := Domain(g);
  genus := Degree(f) div 2; l := Degree(f);
  pol1 := P[1]; pol2 := P[2];
  Kt := Parent(pol1);
  //J := Parent(P);
  //C := HyperellipticCurve(J); 
  //pol1g := Polynomial([g(t): t in ElementToSequence(pol1)]);
  //pol2g := Polynomial([g(t): t in ElementToSequence(pol2)]);
  chival := SequenceToSet([t : t in [1..#WPts]| g(sqrtg[t]) eq sqrtg[t]]);
  if chival eq SequenceToSet([1..l]) then return [K!1: t in [1..l]]; end if;
  flag, fctn, newPt := IsrealPrincipalDivisor({WPts[t]: t in chival}, P, f);
  assert flag eq true;
  val := [K!1: t in [1..l]];
  P := Parent(fctn[1]); 
  x := P.1; y := P.2;
  fval := (EvalFuncPairing1(CompMinRep(fctn[1]*x^((#chival)*genus), fctn[2]*y^(#chival), f, false), [1, 0, 0], f, false))^(-1);
  for j in [1..l] do
  val[j] := fval;
  if j in chival then 
  val[j] := val[j] * EvalFuncPairing1(CompMinRep(fctn[1]*y, fctn[2]*(x-WPts[j]),f, false), [WPts[j],0,1], f , false);
  else 
  val[j] := val[j] * EvalFuncPairing1(CompMinRep(fctn[1], fctn[2], f, false), [WPts[j], 0,1], f, false); 
  end if;  
  end for;
  return val;
end function;

*/

/*
verifyNewepsilon := function(WPts, K, P, sqrtg, f, C, gp)
  G, s, m := AutomorphismGroup(K);
  l := #WPts;
  zero := SequenceToSet([1..l]);
  eps_val := [<g, new_eps(m(g), sqrtg, P, WPts, f)>: g in G];
  eps_val := map<G-> Parent(eps_val[1][2]) | eps_val>;
  Pval := [(-1)^(Degree(P[1]))*Evaluate(P[1], WPts[j]): j in [1..l]]; 
  for j in [1..l] do
  dp := gp[j];
  flag := IsSquare(K!dp);
  if flag then sqdp := SquareRoot(K!dp); 
  pos_sig := [<<g,{t: t in [1..l]| m(g)(sqrtg[t]) eq sqrtg[t]}>, m(g)(sqdp)/sqdp>: g in G];
  else 
  pos_sig := [<g,{t: t in [1..l]| m(g)(sqrtg[t]) eq sqrtg[t]}>: g in G];
  pos_sig := &cat[[<t,1>, <t,-1>] : t in pos_sig];
  end if;

  for gs in pos_sig do
  for gtau in pos_sig do
    eps_val1 := eps_val(gtau[1][1])[j];
    if gtau[2] eq -1 then eps_val1 := eps_val1/Pval[j]; end if;
    if gtau[2] eq 1 then
    eps_val2 := eps_val(gs[1][1])[j]; 
    if gs[2] eq -1 then eps_val2 := eps_val2/Pval[j]; end if;
    else 
    eps_val2 := 1;
    end if;
    gst := (gs[1][2] meet gtau[1][2]) join (zero diff (gs[1][2] join gtau[1][2]));
    eps_val3 := eps_val(gs[1][1]*gtau[1][1])[j];
    if gs[2]*gtau[2] eq -1 then eps_val3 := eps_val3/Pval[j]; end if;
    if gtau[2] eq 1 then 
    eps_val4:= 1;
    else
    eps_val4 := eps_val(gs[1][1])[j]; 
    if gs[2] eq -1 then eps_val4 := eps_val4/Pval[j]; end if;
    end if;
    
    eta := compute_eta(gs[1][2], gtau[1][2], gtau[2], -1, j, C, WPts);
//    /*
    if pseq1 ne [] then
    eps_val1 := eps_val1 *(&*[Pg[t[1]][t[2]]^(t[3]): t in pseq1]); end if;
    if sseq1 ne [] then
    eps_val1 := eps_val1 *(&*[(WPts[t[1]]-WPts[t[2]])^(t[3]): t in sseq1]); end if;
    //print eps_val1;
    if pseq2 ne [] then
    eps_val2 := eps_val2 *(&*[Pg[t[1]][t[2]]^(t[3]): t in pseq2]); end if;
    if sseq2 ne [] then
    eps_val2 := eps_val2 *(&*[(WPts[t[1]]-WPts[t[2]])^(t[3]): t in sseq2]); end if;
    //print eps_val2;
    if pseq3 ne [] then
    eps_val3 := eps_val3 *(&*[Pg[t[1]][t[2]]^(t[3]): t in pseq3]); end if;
    if sseq3 ne [] then
    eps_val3 := eps_val3 *(&*[(WPts[t[1]]-WPts[t[2]])^(t[3]): t in sseq3]); end if;
    //print eps_val3;
    if pseq4 ne [] then
    eps_val4 := eps_val4 *(&*[Pg[t[1]][t[2]]^(t[3]): t in pseq4]); end if;
    if sseq4 ne [] then
    eps_val4 := eps_val4 *(&*[(WPts[t[1]]-WPts[t[2]])^(t[3]): t in sseq4]); end if;
    //print eps_val4;
    */

//    val := m(gs[1][1])(eps_val1)*eps_val2/(eps_val3*eps_val4);
 //   val-eta;
    /*
    if eta ne val then error "Verification of epsilon failed";
    print <gs[1][2],gs[2]>, <gtau[1][2], gtau[2]>;
    print "partial eps :", val;
    print "eta:", eta;
    end if;
    */
    //  if val ne K!eta then print gs, gtau; break;
  //  end if;
 // end for;
 // end for;
 // end for;  
//return 0; 

//end function;



