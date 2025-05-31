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

definition always_part where "always_part A s \<equiv> always (\<lambda> s s1. A s1) s"
definition always_inv_part where "always_inv_part A s \<equiv> always_inv (\<lambda> s s1. A s1) s"

lemma always_inv_saving: "always_inv_part A s \<Longrightarrow> consecutive s s' \<Longrightarrow>   A s' \<Longrightarrow>
 always_inv_part A s'"
  unfolding always_inv_part_def
  apply(simp add: always_rule always_imp_refl)
  done

lemma always_einv_imp_req: "always_inv_part A s  \<Longrightarrow> toEnvP s \<Longrightarrow> True \<Longrightarrow> always_part A s"
  unfolding always_inv_part_def always_part_def
  apply(simp add: always_einv2req always_imp_refl)
  done

lemmas always_used_patterns = always_def
lemmas always_inv_used_patterns = always_inv_def
lemmas always_part_used_patterns = always_part_def  always_def
lemmas always_inv_part_used_patterns = always_inv_part_def always_inv_def

end
