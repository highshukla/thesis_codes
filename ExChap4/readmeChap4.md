This directory is for verification of the computations done in examples in Chapter 4. 
There are three subdirectories 
- Q_fsplit
- NF_fsplit
- Q_fnonsplit

**Q_fsplit:** Contains the program to compute CTP matrix between good elements in the
quotient  $S^{(2)}(J/\mathbb{Q})/\mathrm{Im}(J\mathbb{Q}[2])$ and elements in the quotient
$S^{(2)}(J/\mathbb{Q})/\mathrm{Im}(J(\mathbb{Q})[2])$. The curve must be hyperelliptic of
the form $y^2=f(x)$, with $\mathrm{deg}(f)$ as odd, $f$ being monic and $f$ 
splits completely over $\mathbb{Q}$. The following are the magma commands to execute the code. 

- load "main.m";
- f := *defining polynomial of odd degree that splits over $\mathbb{Q}$*;
- C := HyperellipticCurve(f); 
- compctp(C);


**NF_fplit:** Let $K$ be a non-trivial number field. This directory contains the program 
to compute CTP matrix between good elements in the
quotient  $S^{(2)}(J/K)/\mathrm{Im}(J(K)[2])$ and elements in the quotient
$S^{(2)}(J/K)/\mathrm{Im}(J(K)[2])$. The curve must be hyperelliptic of
the form $y^2=f(x)$, with $\mathrm{deg}(f)$ as odd, $f$ being monic and $f$ 
splits completely over $K$. The following are the magma commands to execute the code. 

- load "main.m";
- f := *defining polynomial of odd degree that splits over $K$*;
- C := HyperellipticCurve(f); 
- compctp(C);

**Q_fnonsplit:** This directory is under constant development apart from the files
ex4_5_5.m, ex4_5_6.m and ex4_5_8.m. These files verify examples 4.5.5, 4.5.6 and 4.5.8 in
the thesis. In order to execute them, one can just simple load these files in magma by
using load "ex4_5_x.m", where x is 5, 6 or 8. The value of the CTP is stored in the
variable *ctpval*. 

**Remark:** Due to an error in the code (found later than when the thesis was printed and submitted) and now fixed, the result of the pairing in Example 4.5.6 does not match the output from the program ex4_5_6.m. The file realCTP.m (currently under development) will fix this. 
