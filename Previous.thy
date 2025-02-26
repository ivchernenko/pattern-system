theory Previous
  imports Always
begin

definition weak_previous where " weak_previous A (s::state) s1 \<equiv>
\<forall> r1. consecutive r1 s1 \<longrightarrow> A s r1"

definition previous where "previous A (s::state) s1 \<equiv>
\<exists> r1. consecutive r1 s1 \<and> A s r1"

definition previous_inv where "previous_inv b (A::state\<Rightarrow>state\<Rightarrow>bool) (s::state) \<equiv> b s \<longrightarrow> A s s"

definition always2 where  "always2 A1 A2 A3 s \<equiv> 
always (\<lambda> r2 r1. weak_previous (\<lambda> r4 r3. \<not> A1 r3) r2 r1 \<or> \<not> A2 r1 \<or> A3 r2 r1) s"

definition always2_inv where  "always2_inv b A1 A2 A3 s \<equiv> 
always_inv (\<lambda> r2 r1. weak_previous (\<lambda> r4 r3. \<not> A1 r3) r2 r1 \<or> \<not> A2 r1 \<or> A3 r2 r1) s
 \<and> ( previous_inv b (\<lambda> r2 r1. \<not> A1 r1) s )"

lemma weak_previous_one_point[patternintro]: "previous_inv b A s \<Longrightarrow>  consecutive s s'
 \<Longrightarrow> b s \<and> always_imp s (A s) (A s')
 \<Longrightarrow> weak_previous A s' s'"
  unfolding previous_inv_def weak_previous_def always_imp_def
  apply simp
  by (metis substate_refl toEnvNum_eq_imp_eq2)

lemma previous_one_point[patternintro]: "previous_inv b A s \<Longrightarrow> consecutive s s'
 \<Longrightarrow> b s \<and> always_imp s (A s) (A s')
  \<Longrightarrow> previous  A s' s'"
  unfolding previous_inv_def previous_def always_imp_def
  by auto

lemma previous_rule[pastinv]: "previous_inv b A s \<Longrightarrow>  consecutive s s' \<Longrightarrow> b s' \<longrightarrow> A s' s' \<Longrightarrow> previous_inv b A s'"
  unfolding previous_inv_def
  by auto

lemma weak_previous_LS4[invsaving]: "consecutive s s' \<Longrightarrow> always_imp s (A s) (A s') 
\<Longrightarrow> always_imp s (\<lambda> s1. weak_previous A s s1) (\<lambda> s1. weak_previous A s' s1)"
  unfolding weak_previous_def always_imp_def
  apply simp
  by (meson substate_trans)

lemma weak_previous_LS5[inv_req]: "toEnvP s \<Longrightarrow> always_imp s (A' s) (A s) 
\<Longrightarrow> always_imp s (\<lambda> s1. weak_previous A' s s1) (\<lambda> s1. weak_previous A s s1)"
  unfolding weak_previous_def always_imp_def
  apply simp
  using substate_trans by blast

lemma previous_LS4[invsaving]: "consecutive s s' \<Longrightarrow> always_imp s (A s) (A s') 
\<Longrightarrow> always_imp s (\<lambda> s1. previous A s s1) (\<lambda> s1. previous A s' s1)"
  unfolding previous_def always_imp_def
  apply simp
  by (meson substate_trans)

lemma previous_LS5[inv_req]: "toEnvP s \<Longrightarrow> always_imp s (A' s) (A s) 
\<Longrightarrow> always_imp s (\<lambda> s1. previous A' s s1) (\<lambda> s1. previous A s s1)"
  unfolding previous_def always_imp_def
  apply simp
  using substate_trans by blast

end
