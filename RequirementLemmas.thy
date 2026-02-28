theory RequirementLemmas
  imports VCTheoryLemmas
begin

definition always_imp where "always_imp s A A' \<equiv> \<forall> s1. toEnvP s1 \<and> s1 \<le> s \<and> A s1 \<longrightarrow> A' s1"

lemma always_disj_rule: "toEnvP s \<Longrightarrow> always_imp s A A' \<and> always_imp s B B' \<Longrightarrow>
always_imp s (\<lambda> s1. A s1 \<or> B s1) (\<lambda> s1. A' s1 \<or> B' s1)"
  apply(unfold always_imp_def)
  by auto

lemma always_conj_rule: "toEnvP s \<Longrightarrow> always_imp s A A' \<and> always_imp s B B' \<Longrightarrow>
always_imp s (\<lambda> s1. A s1 \<and> B s1) (\<lambda> s1. A' s1 \<and> B' s1)"
  apply(unfold always_imp_def)
  by auto

lemma always_imp_refl: " always_imp s A A"
  apply(unfold always_imp_def)
  by auto

end