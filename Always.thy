theory Always
  imports RequirementLemmas
begin

definition always where "always A s  \<equiv>
\<forall> r1. r1 \<le> s \<and> toEnvP r1 \<longrightarrow> A s r1"

definition always_inv where "always_inv A' s \<equiv>
\<forall> r1. r1 \<le> s \<and> toEnvP r1 \<longrightarrow> A' s r1"

lemma always_rule[elims]: "always_inv A' s \<Longrightarrow> consecutive s s' \<Longrightarrow>  always_imp s (A' s) (A' s') \<and> A' s' s' \<Longrightarrow>
 always_inv A' s'"
  apply(unfold always_inv_def always_imp_def)
  apply simp
  by (metis One_nat_def substate_noteq_imp_substate_of_pred)

lemma always_einv2req[elims]: "always_inv A' s  \<Longrightarrow> toEnvP s \<Longrightarrow> always_imp s (A' s) (A s) \<Longrightarrow> always A s"
  apply(unfold always_def always_inv_def always_imp_def)
  by simp

end
