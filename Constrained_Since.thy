theory Constrained_Since
  imports RequirementLemmas
begin

definition constrained_since where "constrained_since t1 t2 A1 A2 (s::state) s1 \<equiv>
(\<exists> r1. toEnvP r1 \<and> r1 \<le> s1 \<and> toEnvNum r1 s1 \<ge> t1 \<and> toEnvNum r1 s1 \<le> t2 \<and> A2 s r1 \<and>
  (\<forall> r2. toEnvP r2 \<and> r1 < r2 \<and> r2 \<le> s1 \<longrightarrow> A1 s r2))"

definition dual_constrained_since where "dual_constrained_since t1 t2 A1 A2 (s::state) s1 \<equiv>
(\<forall> r1. toEnvP r1 \<and> r1 \<le> s1 \<and> toEnvNum r1 s1 \<ge> t1 \<and> toEnvNum r1 s1 \<le> t2 \<longrightarrow> A2 s r1 \<or>
  (\<exists> r2. toEnvP r2 \<and> r1 < r2 \<and> r2 \<le> s1 \<and> A1 s r2))"

definition constrained_since0 where "constrained_since0 t1 A1 A2 (s::state) s1 \<equiv>
(\<exists> r1. toEnvP r1 \<and> r1 \<le> s1 \<and> toEnvNum r1 s1 \<le> t1 \<and> A2 s r1 \<and>
  (\<forall> r2. toEnvP r2 \<and> r1 < r2 \<and> r2 \<le> s1 \<longrightarrow> A1 s r2))"

definition dual_constrained_since0 where "dual_constrained_since0 t1 A1 A2 (s::state) s1 \<equiv>
(\<forall> r1. toEnvP r1 \<and> r1 \<le> s1 \<and> toEnvNum r1 s1 \<le> t1 \<longrightarrow> A2 s r1 \<or>
  (\<exists> r2. toEnvP r2 \<and> r1 < r2 \<and> r2 \<le> s1 \<and> A1 s r2))"

definition constrained_since_inv where "constrained_since_inv t1 t2 b t1_1 t2_1 A1 A2 s \<equiv>
b s \<longrightarrow>
(\<exists> r1. toEnvP r1 \<and> r1 \<le> s \<and> toEnvNum r1 s \<ge> t1_1 s \<and> toEnvNum r1 s \<le> t2_1 s \<and> A2 s r1 \<and>
  (\<forall> r2. toEnvP r2 \<and> r1 < r2 \<and> r2 \<le> s \<longrightarrow> A1 s r2))"

definition dual_constrained_since_inv where "dual_constrained_since_inv t1 t2 b t1_1 t2_1 A1 A2 s \<equiv>
b s \<longrightarrow>
(\<forall> r1. toEnvP r1 \<and> r1 \<le> s \<and> toEnvNum r1 s \<ge> t1_1 s \<and> toEnvNum r1 s \<le> t2_1 s \<longrightarrow> A2 s r1 \<or>
  (\<exists> r2. toEnvP r2 \<and> r1 < r2 \<and> r2 \<le> s \<and> A1 s r2))"

definition constrained_since0_inv where "constrained_since0_inv t b t1 A1 A2 s \<equiv>
b s \<longrightarrow>
(\<exists> r1. toEnvP r1 \<and> r1 \<le> s \<and> toEnvNum r1 s \<le> t1 s \<and> A2 s r1 \<and>
  (\<forall> r2. toEnvP r2 \<and> r1 < r2 \<and> r2 \<le> s \<longrightarrow> A1 s r2))"

definition dual_constrained_since0_inv where "dual_constrained_since0_inv t b t1 A1 A2 s \<equiv>
b s \<longrightarrow>
(\<forall> r1. toEnvP r1 \<and> r1 \<le> s \<and> toEnvNum r1 s \<le> t1 s \<longrightarrow> A2 s r1 \<or>
  (\<exists> r2. toEnvP r2 \<and> r1 < r2 \<and> r2 \<le> s \<and> A1 s r2))"

lemma constrained_since_L6: 
"constrained_since_inv t1 t2 b t1_1 t2_1 A1 A2 s \<Longrightarrow>
 consecutive s s' \<Longrightarrow>
b s' \<longrightarrow> t1_1 s' = 0 \<and> A2 s' s' \<or>
b s \<and> always_imp s (A1 s) (A1 s') \<and> always_imp s (A2 s) (A2 s') \<and> t1_1 s' \<le> t1_1 s + 1 \<and> t2_1 s < t2_1 s' \<and> A1 s' s'
 \<Longrightarrow>
constrained_since_inv t1 t2 b t1_1 t2_1 A1 A2 s'"
  unfolding constrained_since_inv_def always_imp_def less_state.simps less_eq_state.simps
  apply(rule impI)
  apply(rotate_tac)
  apply(erule impE)
   apply assumption
    apply(erule disjE)
   apply (metis bot_nat_0.extremum consecutive.simps substate_antisym substate_refl toEnvNum_id)
    apply(erule impE)
     apply simp
    apply(erule exE)
    subgoal for r1
      apply(rule exI[of _ r1])
      by (smt (verit, best) add.commute consecutive.elims(2) interval_class.less_imp_in_less_eq nat_add_left_cancel_le
          order_subst1 substate_noteq_imp_substate_of_pred substate_trans toEnvNum3 verit_comp_simplify1(3))
    done

lemma dual_constrained_since_L6: 
"dual_constrained_since_inv t1 t2 b t1_1 t2_1 A1 A2 s \<Longrightarrow>
 consecutive s s' \<Longrightarrow>
b s' \<longrightarrow> (t1_1 s' > 0 \<or> A2 s' s') \<and>
 (A1 s' s' \<or>
   b s \<and> always_imp s (A1 s) (A1 s') \<and> always_imp s (A2 s) (A2 s') \<and>t1_1 s < t1_1 s' \<and> t2_1 s' \<le> t2_1 s + 1)
 \<Longrightarrow>
dual_constrained_since_inv t1 t2 b t1_1 t2_1 A1 A2 s'"
  unfolding dual_constrained_since_inv_def always_imp_def less_state.simps less_eq_state.simps
  apply(rule impI)
  apply(rotate_tac 2)
  apply(erule impE)
   apply assumption
  apply(rule allI)
  subgoal for r1
    apply(cases "r1 = s'")
     apply auto[1]
    apply(rule impI)
    apply(subgoal_tac "substate r1 s")
    apply(erule conjE)
     apply(rotate_tac -1)
    apply(erule disjE)
    apply simp
    using substate_refl apply blast
     apply(erule impE)
      apply simp
     apply(rotate_tac -1)
     apply(erule allE[of _ r1])
    apply (smt (verit, best) add_le_cancel_right consecutive.simps le_iff_add le_trans less_inc_imp_less_eq substate_trans
        toEnvNum3 trans_less_add1)
    apply simp
    using  substate_noteq_imp_substate_of_pred
    by (metis One_nat_def)
  done

lemma constrained_since_L7: 
"constrained_since_inv t1 t2 b t1_1 t2_1 A1 A2 s \<Longrightarrow>
 consecutive s s' \<Longrightarrow>
 t1 = 0 \<and> A2 s' s' \<or>
b s \<and> always_imp s (A1 s) (A1 s') \<and> always_imp s (A2 s) (A2 s') \<and> t1 \<le> t1_1 s + 1 \<and> t2_1 s < t2 \<and> A1 s' s'
 \<Longrightarrow>
constrained_since t1 t2 A1 A2 s' s'"
  unfolding constrained_since_inv_def constrained_since_def always_imp_def less_state.simps less_eq_state.simps
    apply(erule disjE)
   apply (metis bot_nat_0.extremum consecutive.simps substate_antisym substate_refl toEnvNum_id)
    apply(erule impE)
     apply simp
    apply(erule exE)
    subgoal for r1
      apply(rule exI[of _ r1])
      by (smt (verit, best) add.commute consecutive.elims(2) interval_class.less_imp_in_less_eq nat_add_left_cancel_le
          order_subst1 substate_noteq_imp_substate_of_pred substate_trans toEnvNum3 verit_comp_simplify1(3))
    done

lemma dual_constrained_since_L7: 
"dual_constrained_since_inv t1 t2 b t1_1 t2_1 A1 A2 s \<Longrightarrow>
 consecutive s s' \<Longrightarrow>
 (t1 > 0 \<or> A2 s' s') \<and>
 (A1 s' s' \<or>
   b s \<and> always_imp s (A1 s) (A1 s') \<and> always_imp s (A2 s) (A2 s') \<and>t1_1 s < t1 \<and> t2 \<le> t2_1 s + 1)
 \<Longrightarrow>
dual_constrained_since t1 t2 A1 A2 s' s'"
  unfolding dual_constrained_since_inv_def dual_constrained_since_def always_imp_def less_state.simps less_eq_state.simps
  apply(rule allI)
  subgoal for r1
    apply(cases "r1 = s'")
     apply auto[1]
    apply(rule impI)
    apply(subgoal_tac "substate r1 s")
    apply(erule conjE)
     apply(rotate_tac -1)
    apply(erule disjE)
    apply simp
    using substate_refl apply blast
     apply(erule impE)
      apply simp
     apply(rotate_tac -1)
     apply(erule allE[of _ r1])
    apply (smt (verit, best) add_le_cancel_right consecutive.simps le_iff_add le_trans less_inc_imp_less_eq substate_trans
        toEnvNum3 trans_less_add1)
    apply simp
    using  substate_noteq_imp_substate_of_pred
    by (metis One_nat_def)
  done

lemma constrained_since0_L6: 
"constrained_since0_inv t1 b t1_1 A1 A2 s \<Longrightarrow>
 consecutive s s' \<Longrightarrow>
b s' \<longrightarrow>  A2 s' s' \<or>
 b s \<and> always_imp s (A1 s) (A1 s') \<and> always_imp s (A2 s) (A2 s') \<and> t1_1 s < t1_1 s' \<and> A1 s' s'
 \<Longrightarrow>
constrained_since0_inv t1 b t1_1 A1 A2 s'"
  unfolding constrained_since0_inv_def always_imp_def less_state.simps less_eq_state.simps
  apply(rule impI)
  apply(rotate_tac)
  apply(erule impE)
   apply assumption
    apply(erule disjE)
   apply (metis bot_nat_0.extremum consecutive.simps substate_antisym substate_refl toEnvNum_id)
    apply(erule impE)
     apply simp
    apply(erule exE)
    subgoal for r1
      apply(rule exI[of _ r1])
      by (smt (verit, best) add.commute consecutive.elims(2) interval_class.less_imp_in_less_eq nat_add_left_cancel_le
          order_subst1 substate_noteq_imp_substate_of_pred substate_trans toEnvNum3 verit_comp_simplify1(3))
    done

lemma dual_constrained0_since_L6: 
"dual_constrained_since0_inv t1 b t1_1 A1 A2 s \<Longrightarrow>
 consecutive s s' \<Longrightarrow>
b s' \<longrightarrow> A2 s' s' \<and>
 (A1 s' s' \<or>
   b s \<and> always_imp s (A1 s) (A1 s') \<and> always_imp s (A2 s) (A2 s') \<and> t1_1 s' \<le> t1_1 s + 1)
 \<Longrightarrow>
dual_constrained_since0_inv t1 b t1_1 A1 A2 s'"
  unfolding dual_constrained_since0_inv_def always_imp_def less_state.simps less_eq_state.simps
  apply(rule impI)
  apply(rotate_tac 2)
  apply(erule impE)
   apply assumption
  apply(rule allI)
  subgoal for r1
    apply(cases "r1 = s'")
     apply auto[1]
    apply(rule impI)
    apply(subgoal_tac "substate r1 s")
    apply(erule conjE)
     apply(rotate_tac -1)
    apply(erule disjE)
    apply simp
    using substate_refl apply blast
     apply(erule impE)
      apply simp
     apply(rotate_tac -1)
     apply(erule allE[of _ r1])
    apply (smt (verit, best) add_le_cancel_right consecutive.simps le_iff_add le_trans less_inc_imp_less_eq substate_trans
        toEnvNum3 trans_less_add1)
    apply simp
    using  substate_noteq_imp_substate_of_pred
    by (metis One_nat_def)
  done

lemma constrained_since0_L7: 
"constrained_since0_inv t1 b t1_1 A1 A2 s \<Longrightarrow>
 consecutive s s' \<Longrightarrow>
 A2 s' s' \<or>
 b s \<and> always_imp s (A1 s) (A1 s') \<and> always_imp s (A2 s) (A2 s') \<and>  t1_1 s < t1 \<and> A1 s' s'
 \<Longrightarrow>
constrained_since0 t1 A1 A2 s' s'"
  unfolding constrained_since0_inv_def constrained_since0_def always_imp_def less_state.simps less_eq_state.simps
    apply(erule disjE)
   apply (metis bot_nat_0.extremum consecutive.simps substate_antisym substate_refl toEnvNum_id)
    apply(erule impE)
     apply simp
    apply(erule exE)
    subgoal for r1
      apply(rule exI[of _ r1])
      by (smt (verit, best) add.commute consecutive.elims(2) interval_class.less_imp_in_less_eq nat_add_left_cancel_le
          order_subst1 substate_noteq_imp_substate_of_pred substate_trans toEnvNum3 verit_comp_simplify1(3))
    done

lemma dual_constrained_since0_L7: 
"dual_constrained_since0_inv t1 b t1_1 A1 A2 s \<Longrightarrow>
 consecutive s s' \<Longrightarrow>
 A2 s' s' \<and>
 (A1 s' s' \<or>
   b s \<and> always_imp s (A1 s) (A1 s') \<and> always_imp s (A2 s) (A2 s') \<and> t1 \<le> t1_1 s + 1)
 \<Longrightarrow>
dual_constrained_since0 t1 A1 A2 s' s'"
  unfolding dual_constrained_since0_inv_def dual_constrained_since0_def always_imp_def less_state.simps less_eq_state.simps
  apply(rule allI)
  subgoal for r1
    apply(cases "r1 = s'")
     apply auto[1]
    apply(rule impI)
    apply(subgoal_tac "substate r1 s")
    apply(erule conjE)
     apply(rotate_tac -1)
    apply(erule disjE)
    apply simp
    using substate_refl apply blast
     apply(erule impE)
      apply simp
     apply(rotate_tac -1)
     apply(erule allE[of _ r1])
    apply (smt (verit, best) add_le_cancel_right consecutive.simps le_iff_add le_trans less_inc_imp_less_eq substate_trans
        toEnvNum3 trans_less_add1)
    apply simp
    using  substate_noteq_imp_substate_of_pred
    by (metis One_nat_def)
  done

lemma constrained_since_L4:
"consecutive s s' \<Longrightarrow>
always_imp s (A1' s) (A1' s') \<and> always_imp s (A2' s) (A2' s') \<Longrightarrow>
always_imp s (constrained_since t1 t2 A1' A2' s) (constrained_since t1 t2 A1' A2' s')"
  unfolding constrained_since_def always_imp_def
  by (meson dual_order.trans)

lemma dual_constrained_since_L4:
"consecutive s s' \<Longrightarrow>
always_imp s (A1' s) (A1' s') \<and> always_imp s (A2' s) (A2' s') \<Longrightarrow>
always_imp s (dual_constrained_since t1 t2 A1' A2' s) (dual_constrained_since t1 t2 A1' A2' s')"
  unfolding dual_constrained_since_def always_imp_def
  by (meson dual_order.trans)

lemma constrained_since_L5:
"e s \<Longrightarrow>
always_imp s (A1' s) (A1 s) \<and> always_imp s (A2' s) (A2 s) \<Longrightarrow>
always_imp s (constrained_since t1 t2 A1' A2' s) (constrained_since t1 t2 A1 A2 s)"
  unfolding constrained_since_def always_imp_def
  by (meson dual_order.trans)

lemma dual_constrained_since_L5:
"e s \<Longrightarrow>
always_imp s (A1' s) (A1 s) \<and> always_imp s (A2' s) (A2 s) \<Longrightarrow>
always_imp s (dual_constrained_since t1 t2 A1' A2' s) (dual_constrained_since t1 t2 A1 A2 s)"
  unfolding dual_constrained_since_def always_imp_def
  by (meson dual_order.trans)

lemma constrained_since0_L4:
"consecutive s s' \<Longrightarrow>
always_imp s (A1' s) (A1' s') \<and> always_imp s (A2' s) (A2' s') \<Longrightarrow>
always_imp s (constrained_since0 t A1' A2' s) (constrained_since0 t A1' A2' s')"
  unfolding constrained_since0_def always_imp_def
  by (meson dual_order.trans)

lemma dual_constrained_since0_L4:
"consecutive s s' \<Longrightarrow>
always_imp s (A1' s) (A1' s') \<and> always_imp s (A2' s) (A2' s') \<Longrightarrow>
always_imp s (dual_constrained_since0 t A1' A2' s) (dual_constrained_since0 t A1' A2' s')"
  unfolding dual_constrained_since0_def always_imp_def
  by (meson dual_order.trans)

lemma constrained_since0_L5:
"e s \<Longrightarrow>
always_imp s (A1' s) (A1 s) \<and> always_imp s (A2' s) (A2 s) \<Longrightarrow>
always_imp s (constrained_since0 t A1' A2' s) (constrained_since0 t A1 A2 s)"
  unfolding constrained_since0_def always_imp_def
  by (meson dual_order.trans)

lemma dual_constrained_since0_L5:
"e s \<Longrightarrow>
always_imp s (A1' s) (A1 s) \<and> always_imp s (A2' s) (A2 s) \<Longrightarrow>
always_imp s (dual_constrained_since0 t A1' A2' s) (dual_constrained_since0 t A1 A2 s)"
  unfolding dual_constrained_since0_def always_imp_def
  by (meson dual_order.trans)
  
end
