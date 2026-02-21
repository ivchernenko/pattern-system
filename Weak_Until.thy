theory Weak_Until
  imports RequirementLemmas
begin

definition weak_until where "weak_until A1 A2 s s1 \<equiv>
(\<exists> s3. toEnvP s3 \<and> s1 \<le> s3 \<and> s3 \<le> s \<and> A2 s s3 \<and>
(\<forall> s2. toEnvP s2 \<and> s1 \<le> s2 \<and> s2 < s3 \<longrightarrow> A1 s s2)) \<or>
(\<forall> s2. toEnvP s2 \<and>s1 \<le> s2 \<and> s2 \<le> s \<longrightarrow> A1 s s2)"

definition weak_until_inv where "weak_until_inv w A1 A2 s s1 \<equiv>
(\<exists> s3. toEnvP s3 \<and> s1 \<le> s3 \<and> s3 \<le> s \<and> A2 s s3 \<and>
(\<forall> s2. toEnvP s2 \<and> s1 \<le> s2 \<and> s2 < s3 \<longrightarrow> A1 s s2)) \<or>
w s \<and> (\<forall> s2. toEnvP s2 \<and> s1 \<le> s2 \<and> s2 \<le> s \<longrightarrow> A1 s s2)"

lemma weak_until_L1: "consecutive s0 s \<Longrightarrow>
always_imp s0 (A1' s0) (A1' s) \<and>
always_imp s0 (A2' s0) (A2' s) \<and>
(\<not> w s0 \<or>  A2' s s \<or> w s \<and> A1' s s) \<Longrightarrow>
always_imp s0 (weak_until_inv w A1' A2' s0) (weak_until_inv w A1' A2' s)"
  unfolding weak_until_inv_def  less_eq_state.simps less_state.simps always_imp_def
  by (smt (verit, best) consecutive.elims(2) substate_noteq_imp_substate_of_pred substate_refl substate_trans)

lemma weak_until_L2: "toEnvP s \<Longrightarrow> A2 s s \<or> w s \<and> A1 s s \<Longrightarrow> weak_until_inv w A1 A2  s s"
  apply(unfold weak_until_inv_def)
  unfolding weak_until_inv_def  less_eq_state.simps less_state.simps
  using substate_antisym substate_refl by blast

lemma weak_until_L3: "
toEnvP s \<Longrightarrow>
always_imp s (A1' s) (A1 s) \<and>
always_imp s (A2' s) (A2 s) \<Longrightarrow>
always_imp s (weak_until_inv w A1' A2' s) (weak_until A1 A2 s)"
  unfolding weak_until_inv_def weak_until_def  less_eq_state.simps less_state.simps always_imp_def
  by (meson substate_trans)

end
