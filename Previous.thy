theory Previous
  imports Always
begin

definition weak_previous where " weak_previous A (s::state) s1 \<equiv>
\<forall> r1. consecutive r1 s1 \<longrightarrow> A s r1"

definition previous where "previous A (s::state) s1 \<equiv>
\<exists> r1. consecutive r1 s1 \<and> A s r1"

definition previous_inv where "previous_inv b (A::state\<Rightarrow>state\<Rightarrow>bool) (s::state) \<equiv> b s \<longrightarrow> A s s"

lemma weak_previous_L7: "previous_inv b A s \<Longrightarrow>  consecutive s s'
 \<Longrightarrow> b s \<and> always_imp s (A s) (A s')
 \<Longrightarrow> weak_previous A s' s'"
  unfolding previous_inv_def weak_previous_def always_imp_def
  apply simp
  by (metis substate_refl toEnvNum_eq_imp_eq2)

lemma previous_L7: "previous_inv b A s \<Longrightarrow> consecutive s s'
 \<Longrightarrow> b s \<and> always_imp s (A s) (A s')
  \<Longrightarrow> previous  A s' s'"
  unfolding previous_inv_def previous_def always_imp_def
  by auto

lemma previous_inv_L6: "previous_inv b A s \<Longrightarrow>  consecutive s s' \<Longrightarrow> b s' \<longrightarrow> A s' s' \<Longrightarrow> previous_inv b A s'"
  unfolding previous_inv_def
  by auto

lemma weak_previous_L4: "consecutive s s' \<Longrightarrow> always_imp s (A s) (A s') 
\<Longrightarrow> always_imp s (\<lambda> s1. weak_previous A s s1) (\<lambda> s1. weak_previous A s' s1)"
  unfolding weak_previous_def always_imp_def
  apply simp
  by (meson substate_trans)

lemma weak_previous_L5: "toEnvP s \<Longrightarrow> always_imp s (A' s) (A s) 
\<Longrightarrow> always_imp s (\<lambda> s1. weak_previous A' s s1) (\<lambda> s1. weak_previous A s s1)"
  unfolding weak_previous_def always_imp_def
  apply simp
  using substate_trans by blast

lemma previous_L4: "consecutive s s' \<Longrightarrow> always_imp s (A s) (A s') 
\<Longrightarrow> always_imp s (\<lambda> s1. previous A s s1) (\<lambda> s1. previous A s' s1)"
  unfolding previous_def always_imp_def
  apply simp
  by (meson substate_trans)

lemma previous_L5: "toEnvP s \<Longrightarrow> always_imp s (A' s) (A s) 
\<Longrightarrow> always_imp s (\<lambda> s1. previous A' s s1) (\<lambda> s1. previous A s s1)"
  unfolding previous_def always_imp_def
  apply simp
  using substate_trans by blast

end
