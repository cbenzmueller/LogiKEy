theory Day1_LLM_demo
  imports Main
begin

theorem modus_ponens: "((A \<longrightarrow> B) \<and> A) \<longrightarrow> B" by presburger

end
