

Pairing := function(f, D, flag)
  K := Parent(f);
genus := Genus(Curve(D));
  x := K.1;
  y := K.2;
  tamesym := 1;
  prod := 1;
  for plc in Support(D) do
    vd := Valuation(D,plc);
    P := RepresentativePoint(plc);
    vf := Valuation(f, P);
    tamesym := tamesym * (-1)^(vf*vd);
    if P[3] eq 0 then tp := x^genus/y; elif P[2] eq 0 then tp := (x-P[1])/y; else tp := x-P[1];
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
  if #ct mod 2 eq 0 then ct := SequenceToSet([1..l]) diff ct; end if;
  cts := (cs meet ct) join (SequenceToSet([1..l]) diff (cs join ct));
  return fraka(cs, C, WPts) + fraka(ct, C, WPts)-fraka(cts, C, WPts);
end function;





compute_eta := function(cs, ct, ctd,crd, i,C, WPts)
l := #WPts;
if crd eq 1 then return 1; end if;
if #ct mod 2 eq 0 then ct := SequenceToSet([1..l]) diff ct; end if;
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


comp_epsilon := function(c, i, c_dp, C, WPts) 
  l := 2*Genus(C) + 1;
  genus := Genus(C);
  gamma_val := 1;
  zero := SequenceToSet([1..l]);
  if c eq zero and c_dp eq 1 then return 1, [], 1; end if;
  if c eq zero and c_dp eq -1 then return 1, [<i, j, -1>: j in [1..l]| j ne i], 1; end if;
  if i in c then nbas := zero diff c; else nbas := c; end if;
  nbas := Sort(SetToSequence(nbas));
  pseq :=[];
  s := #nbas;
  gval := 1;
  if s eq 1 then
  pseq := [<i, nbas[1],1>]; 
  else 
    while #nbas gt 1 do
    //div(frak(a))
      Append(~pseq,<i, nbas[1], 1>);
      a := nbas[1];
      Remove(~nbas, 1);
      gval *:= compute_eta({a}, SequenceToSet(nbas), 1, -1, i, C, WPts);
    end while;
    Append(~pseq,<i, nbas[1], 1>);
  end if;
  if c_dp eq -1 and i in c then 
    pseq := [<i, j, -1> : j in [1..l]| j ne i and j in c];
  elif c_dp eq -1 and i notin c then
  pseq := [<i,j,-1>: j in [1..l]| j ne i and j notin c];
  end if;
  return (-1)^((s*(s-1)) div 2), pseq, 1/gval;
end function;
 

