% Typings
thf(d_decl, type,
    d : $i > $o).
thf(f_decl, type,
    f : $i > $i > $i).
thf(n_decl, type,
    n : $i > $o).
thf(p_decl, type,
    p : $i > $i > $o).
thf(e_decl, type,
    e : $i).
thf(Ind_decl, type,
    Ind : ($i > $o) > $o).
thf(s_decl, type,
    s : $i > $i).

% Axioms 
thf(a1, axiom,
    ((![N : $i]: ((f @ N @ e) = (s @ e))))).
thf(a2, axiom,
    ((![Y : $i]: ((f @ e @ (s @ Y)) = (s @ (s @ (f @ e @ Y))))))). 
thf(a3, axiom,
    ((![X : $i, Y : $i]: ((f @ (s @ X) @ (s @ Y)) = (f @ X @ (f @ (s @ X) @ Y)))))). 
thf(a4, axiom,
    ((d @ e))). 
thf(a5, axiom,
    ((![X : $i]: ((d @ X) => (d @ (s @ X)))))). 

thf(Ind_def, definition,
    (![X3 : $i > $o]: ((Ind @ X3) = ( (((X3 @ e)) & ((![X2 : $i]: (((X3 @ X2)) => ((X3 @ (s @ X2))))))))))). 
thf(n_def, definition,
    (![X2 : $i]: ((n @ X2) = (![X3 : $i > $o]: (((Ind @ X3)) => ((X3 @ X2))))))). 
thf(p_def, definition,
    (![X2 : $i]: (![Y2 : $i]: ((p @ X2 @ Y2) = (n @ (f @ X2 @ Y2)))))). 

% Conjectures (1)
thf(conj_0, conjecture,
    ((d @ (f @ (s @ (s @ (s @ (s @ e)))) @ (s @ (s @ (s @ (s @ e)))))))).
