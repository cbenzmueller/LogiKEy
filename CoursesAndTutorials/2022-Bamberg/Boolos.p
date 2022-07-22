% Declarations
% Core Problem
 thf(e_decl, type, e : $i).  % one
 thf(s_decl, type, s : $i > $i).  % successor
 thf(d_decl, type, d : $i > $o).  % unary predicate
 thf(f_decl, type, f : $i > $i > $i).  % binary function; axiomatised as Ackermann function below
% Auxiliary definitions 
 thf(isIndSet_decl, type, isIndSet : ($i > $o) > $o).  % second-order unary predicate
 thf(p_decl, type, p : $i > $i > $o).
 
% Axioms
% Axiom 1 for Ackermann function f 
 thf(a1, axiom, ((![N : $i]: ((f @ N @ e) = (s @ e))))).
% Axiom 2 for Ackermann function f 
 thf(a2, axiom, ((![Y : $i]: ((f @ e @ (s @ Y)) = (s @ (s @ (f @ e @ Y))))))).
% Axiom 3 for Ackermann function f 
 thf(a3, axiom, ((![X : $i, Y : $i]: ((f @ (s @ X) @ (s @ Y)) = (f @ X @ (f @ (s @ X) @ Y)))))).
% Property d holds for e 
 thf(a4, axiom, ((d @ e))).
% If property d holds for x then it also holds for the successor of e 
 thf(a5, axiom, ((![X : $i]: ((d @ X) => (d @ (s @ X)))))). 

% Definitions
% X is inductive (over e and s)    
 thf(isIndSet_def, axiom, (isIndSet = (^[Q : $i > $o]: (((Q @ e)) & ((![X : $i]: (((Q @ X)) => ((Q @ (s @ X)))))))))).
% P(x,y) iff F(x,y) is in smallest inductive set (over e and s)    
 thf(p_def, axiom, (p = (^[X: $i]: (^[Y : $i]: ((^[X2 : $i]: (![X3 : $i > $o]: (((isIndSet @ X3)) => ((X3 @ X2))))) @ (f @ X @ Y)))))).

   
% Conjecture 
 thf(conj_0, conjecture, ((d @ (f @ (s @ (s @ (s @ (s @ e)))) @ (s @ (s @ (s @ (s @ e)))))))).
