La>:=FunctionField(Rationals());
K<t>:=PolynomialRing(L);
f:=t^2-a;
I:=ideal<K|f>;
Ka:=quo<K|I>;
sqra:=SquareRoot(Ka!a);
l:=5;
polring<x>:=PolynomialRing(Ka);
C:=HyperellipticCurve(x^l+a);
inf := C![1,0,0];
J:=Jacobian(C);
P:=J![x,sqra];
id:= J!0;
D:=DivisorGroup(C);
ff<x,y>:=FunctionField(C);

alpha:=function(sig)
	return sig*P;
end function;

alpha_pri:=function(sig)
	return sig*P;
end function;

partial_alpha:=function(sig,tau)
	return alpha(sig)+alpha(tau)-alpha((sig+tau) mod l);
end function;

IsCocycle_alpha:=function()
for sig in [0..l-1] do 
	for tau in [0..l-1] do 
		if partial_alpha(sig,tau) ne id then 
		       print "failed", sig, tau, partial_alpha(sig,tau);
	      	end if;
	end for;
end for;
return 0;
end function;

partial_alpha_pri:=function(sig,tau)
	return alpha_pri(sig)+alpha_pri(tau)-alpha_pri((sig+tau) mod l);
end function;

IsCocycle_alpha_pri:=function()
for sig in [0..l-1] do 
	for tau in [0..l-1] do 
		if partial_alpha_pri(sig,tau) ne id then 
		       print "failed", sig, tau, partial_alpha_pri(sig,tau);
	      	end if;
	end for;
end for;
return 0;
end function;

a := function(sig)
	return Divisor(D, [<Place(C![0,sqra,1]),sig>,<Place(C![1,0,0]),-sig>]);
end function;

a_pri:= function(sig)
	return Divisor(D, [<Place(C![0,sqra,1]),sig>,<Place(C![1,0,0]),-sig>]);
end function;

partial_a := function(sig,tau)
	return a(sig)+a(tau)-a((sig+tau) mod l);
end function;

partial_a_pri:= function(sig,tau)
	return a_pri(sig)+a_pri(tau)-a_pri((sig+tau) mod l);
end function;

uniformizer:=function(RP)
	P:=RepresentativePoint(RP);
	if P eq inf then 
		return x^2/y;
	else
		return x-P[1];
	end if;
end function;

pairing1:=function(g, D)
	S,val:=Support(D);
	p:=ff!1;
	for P in S do 
		valp:=val[Index(S,P)];
		p:=p*(Evaluate(g*(uniformizer(P)^(-Valuation(g,P))),P))^(valp);
	end for;
	return p;
end function;

pairing2:=function(g,D)
	S,val:=Support(D);
	p:=ff!1;
	for P in S do
		valp:=val[Index(S,P)];
		valgp:=Valuation(g,P);
		p:=p*(-1)^(valp*valgp)*(Evaluate(g*(uniformizer(P)^(-valgp)),P))^(valp);
	end for;
	return p;
end function;


partial_a_cup_a_pri:= function(sig,tau,rho)
	truth, g := IsPrincipal(partial_a(sig,tau));
	if truth eq true then 
		return pairing1(g,a_pri(rho));
	else
		return "problem in partial_a_cup_a_pri", sig,tau;
	end if;
end function;

a_cup_partial_a_pri:=function(sig,tau,rho)
	truth, g := IsPrincipal(partial_a_pri(tau,rho));
	if truth eq true then 
		return pairing2(g,a(sig));
	else
		return "problem in a_cup_partial_a_pri", tau,rho;
	end if;
end function;

new_eta:=function(sig,tau,taup,rho)
	return partial_a_cup_a_pri(sig,tau,rho)/a_cup_partial_a_pri(sig,taup,rho);
end function;

partial_new_eta:= function(sig1,sig2,sig2p,sig3,sig3p,sig4p);
	value:=(new_eta(sig2,sig3,sig3p,sig4p)*new_eta(sig1,(sig2+sig3) mod l, (sig2p+sig3p) mod l, sig4p)*new_eta(sig1, sig2, sig2p,sig3p))/(new_eta((sig1+sig2) mod l, sig3, sig3p, sig4p)* new_eta(sig1, sig2, sig2p, (sig3p+sig4p) mod l));

	return value;
end function;

IsCocycle_new_eta:=function()
for sig1 in [0..l-1] do 
	for sig2 in [0..l-1] do 
		for sig2p in [0..l-1] do 
			for sig3 in [0..l-1] do 
				for sig3p in [0..l-1] do 
					for sig4p in [0..l-1] do 
						value:= partial_new_eta(sig1,sig2,sig2p,sig3,sig3p,sig4p);
						if value ne 1 then 
							print value, sig1,sig2,sig2p,sig3,sig3p,sig4p;
						end if;
					end for;
				end for;
			end for;
		end for;
	end for;
end for;
return 0;
end function;



pacupapri:=function(sig,tau,rho)
	if (((sig+tau) lt l) or (rho eq 0)) then
		return 1;
	else
		return (2*sqra)^(-rho);
	end if;
end function;

acuppapri:= function(sig,tau,rho)
	if (((tau+rho) lt l) or (sig eq 0)) then 
		return 1;
	else
		return (2*sqra)^(-sig);
	end if;
end function;

eta:=function(sig,tau,taup,rho)
	return pacupapri(sig,tau,rho)/acuppapri(sig,taup,rho);
end function;

parteta:=function(sig1,sig2,sig2p,sig3,sig3p,sig4p)
	value:=(eta(sig2,sig3,sig3p,sig4p)*eta(sig1,(sig2+sig3) mod l, (sig2p+sig3p) mod l, sig4p)*eta(sig1, sig2, sig2p,sig3p))/(eta((sig1+sig2) mod l, sig3, sig3p, sig4p)* eta(sig1, sig2, sig2p, (sig3p+sig4p) mod l));
	return value;
end function;

IsCocycle_eta :=function()

for sig1 in [0..l-1] do 
	for sig2 in [0..l-1] do 
		for sig2p in [0..l-1] do 
			for sig3 in [0..l-1] do 
				for sig3p in [0..l-1] do 
					for sig4p in [0..l-1] do 
						value:= parteta(sig1,sig2,sig2p,sig3,sig3p,sig4p);
						if value ne 1 then 
							print value, sig1,sig2,sig2p,sig3,sig3p,sig4p;
						end if;
					end for;
				end for;
			end for;
		end for;
	end for;
end for;
return 0;
end function;

check_parta:=function()
for i in [0..l-1] do 
	for j in [0..l-1] do 
		for k in [0..l-1] do 
			value:= j+k-((j+k) mod l) + (i+((j+k) mod l))-(((i+j) mod l) + k)- (i+j)+((i+j) mod l);
			print value;
		end for;
	end for;
end for;
return 0;
end function;

epsilon:=function(tau,taup,rho)
	return (2*sqra)^(-tau*rho);
end function;

partial_epsilon:=function(sig,sigp,tau,taup,rho)
	value:= epsilon(tau,taup,rho)*epsilon(sig,sigp,((taup+rho) mod l))/epsilon(((sig+tau) mod l),((sigp+taup) mod l),rho)/epsilon(sig,sigp,taup);
	return value;
end function;

triviality_of_eta:=function()
count := 0;
for sig in [0..l-1] do 
	for sigp in [0..l-1] do 
		for tau in [0..l-1] do 
		       for taup in [0..l-1] do 
		       		for rho in [0..l-1] do 
			 		if partial_epsilon(sig,sigp,tau,taup,rho) eq (eta(sig,tau,taup,rho))^l then
					print eta(sig,tau,taup,rho)^l, partial_epsilon(sig,sigp,tau,taup,rho);
					count:=count+1;
					end if;
				end for;
			end for;
		end for;
	end for;
end for;
return count;
end function;

