theory Constrained_Weak_Until
  imports Previous
begin

definition constrained_weak_until where "constrained_weak_until t A1 A2 s s1 \<equiv>
(\<exists> s4. toEnvP s4 \<and> s1 \<le> s4 \<and> s4 \<le> s \<and> toEnvNum s1 s4 \<le> t \<and> A2 s s4 \<and>
(\<forall> s3. toEnvP s3 \<and> s1 \<le> s3 \<and> s3 < s4 \<longrightarrow> A1 s s3)) \<or>
(\<forall> s3. toEnvP s3 \<and> s1 \<le> s3 \<and> s3 \<le> s \<and> toEnvNum s1 s3 \<le> t \<longrightarrow> A1 s s3)"

definition constrained_weak_until_inv where "constrained_weak_until_inv t t1 A1 A2 s s1 \<equiv>
(\<exists> s4. toEnvP s4 \<and> s1 \<le> s4 \<and> s4 \<le> s \<and> toEnvNum s1 s4 \<le> t \<and> A2 s s4 \<and>
(\<forall> s3. toEnvP s3 \<and> s1 \<le> s3 \<and> s3 < s4 \<longrightarrow> A1 s s3)) \<or>
toEnvNum s1 s \<ge> t1 s \<and>
(\<forall> s3. toEnvP s3 \<and> s1 \<le> s3 \<and> s3 \<le> s \<and> toEnvNum s1 s3 \<le> t \<longrightarrow> A1 s s3)"

lemma constrained_weak_until_one_point[patternintro]: "toEnvP s \<Longrightarrow> A2 s s \<or> t1 s = 0 \<and> A1 s s \<Longrightarrow>
 constrained_weak_until_inv t t1 A1 A2 s s"
  unfolding constrained_weak_until_inv_def less_eq_state.simps less_state.simps
  by (metis substate_antisym substate_refl toEnvNum_id zero_le)

lemma constrained_weak_until_rule[patternintro]: " consecutive s0 s \<Longrightarrow>
always_imp s0 (A1' s0) (A1' s) \<and>
always_imp s0 (A2' s0) (A2' s)  \<and>
(t1 s0 < t \<and> (A2' s s \<and>  t1 s \<le> t+1  \<or>  t1 s \<le> t1 s0 + 1 \<and> A1' s s) \<or> t1 s0 \<ge> t \<and> t1 s \<le> t1 s0 + 1) \<Longrightarrow>
always_imp s0 (constrained_weak_until_inv t t1 A1' A2' s0) (constrained_weak_until_inv t t1 A1' A2' s)"
   unfolding constrained_weak_until_inv_def less_eq_state.simps less_state.simps always_imp_def
  apply(rule allI)
  subgoal for s1
    apply(rule impI)
    apply(erule conjE)+
    apply(rotate_tac -1)
    apply(erule disjE)
     apply (metis consecutive.simps substate_trans)
    apply(erule disjE)
     apply(erule conjE)+
     apply(erule disjE)
      apply(cases "toEnvNum s1 s0 < t")
      apply(rule disjI1)
      apply(rule exI[of _ s])
      apply(rule conjI)
       apply simp
      apply(rule conjI)
        apply (meson consecutive.elims(2) substate_trans)
      apply(rule conjI)
       apply simp
      apply(rule conjI)
        apply (metis Suc_eq_plus1 add_mono1 consecutive.simps less_Suc_eq_le toEnvNum3)
       apply(rule conjI)
        apply simp
       apply (metis add_leE consecutive.simps dual_order.strict_iff_not substate_noteq_imp_substate_of_pred toEnvNum3)
    apply(rule disjI2)
      apply (smt (verit, ccfv_SIG) add.commute consecutive.elims(2) leD leI le_iff_add le_neq_implies_less le_numeral_extra(4) le_trans less_add_one nat_add_left_cancel_le nat_le_linear order.strict_trans1 substate_noteq_imp_substate_of_pred toEnvNum3)
    apply (smt (verit, best) add.commute consecutive.elims(2) nat_add_left_cancel_le order_subst1 substate_noteq_imp_substate_of_pred toEnvNum3)
    apply(rule disjI2)
    apply(rule conjI)
    using toEnvNum3 apply fastforce
    by (metis consecutive.elims(2) dual_order.trans leD less_add_one substate_noteq_imp_substate_of_pred toEnvNum3)
  done

lemma constrained_weak_until_einv2req[patternintro]: "
toEnvP s \<Longrightarrow>
always_imp s (A1' s) (A1 s) \<and>
always_imp s (A2' s) (A2 s) \<Longrightarrow>
always_imp s (constrained_weak_until_inv t t1 A1' A2' s) (constrained_weak_until t A1 A2 s)"
   unfolding constrained_weak_until_inv_def constrained_weak_until_def less_eq_state.simps less_state.simps always_imp_def
  by (meson substate_trans)

end
