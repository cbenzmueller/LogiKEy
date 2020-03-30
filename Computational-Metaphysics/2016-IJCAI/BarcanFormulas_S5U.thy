theory BarcanFormulas_S5U imports QML_S5U 
begin
  theorem BF:  "\<lfloor>(\<^bold>\<forall>x. \<^bold>\<box>(\<phi>(x))) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>x. \<phi>(x))\<rfloor>"
  by simp

  theorem CBF:  "\<lfloor>\<^bold>\<box>(\<^bold>\<forall>x. \<phi>(x)) \<^bold>\<rightarrow> (\<^bold>\<forall>x. \<^bold>\<box>(\<phi>(x)))\<rfloor>"
  by simp
end
