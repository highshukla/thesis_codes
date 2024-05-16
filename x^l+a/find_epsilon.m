// Let (a,b,c,d,e,f) be a six tuple and \epsilon((a,b,c),(d,e,f)) denote the value 
// of epsilon at the triplets (a,b,c) and (d,e,f) corresponding to \tau and \rho resp. 
//For \sigma,\tau,\rho=(a,b,c),(d,e,f),(g,h,i) respectively, we have :
// \partial\epsilon ((a,b,c),(d,e,f),(g,h,i)) = \epsilon((d,e,f),(g,h,i))+\epsilon((a,b,c),(d+g,e+h,f+i))- \epsilon((a+d,b+e,c+f),g,h,i)-\epsilon((a,b,c),(d,e,f))=\eta'((a,b,c),(d,e,f),(g,h,i))=aei.
//Given a 9-tuplet (a,b,c),(d,e,f),(g,h,i) we specify an equation number using the function
//cons_c, and given a 6-tuplet (a,b,c),(d,e,f) we specify a variable number as epsilon
//depends only on this.


l:=3;
cl:=GF(l);
function cons_r(a,b,c,d,e,f)   //function to construct row number (variable number)
return a+b*l+c*l^2+d*l^3+e*l^4+f*l^5+1;
end function;

function cons_c(a,b,c,d,e,f,g,h,i) //function to construct column number (equation number)
return a+b*l+c*l^2+d*l^3+e*l^4+f*l^5+g*l^6+h*l^7+i*l^8+1;
end function;

M := Matrix(cl, l^6, l^9,[]);
eta := Vector(cl, l^9,[0: i in [1..l^9]]);

for a in [0..l-1] do 
	for b in [0..l-1] do 
		for c in [0..l-1] do
			for d in [0..l-1] do 
				for e in [0..l-1] do 
					for f in [0..l-1] do 
						for g in [0..l-1] do 
							for h in [0..l-1] do
								for i in [0..l-1] do 
			col:=cons_c(a,b,c,d,e,f,g,h,i);
			M[cons_r(d,e,f,g,h,i),col]:=1;
			M[cons_r(a,b,c,(d+g) mod l,(h+e) mod l,(i+f) mod l),col]:=1;
			M[cons_r((a+d) mod l,(b+e) mod l,(c+f) mod l,g,h,i),col]:=-1;
			M[cons_r(a,b,c,d,e,f),col]:=-1;
			eta[col]:=a*e*i;
								end for;
							end for;
						end for;
					end for;
				end for;
			end for; 
		end for; 
	end for; 
end for;


V,N:=Solution(M,eta);
