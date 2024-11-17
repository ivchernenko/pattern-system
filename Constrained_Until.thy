theory Constrained_Until
  imports Always
begin

definition constrained_until where "constrained_until s s1 t A1 A2 \<equiv>
toEnvNum s1 s \<ge> t \<longrightarrow>
(\<exists> r2. toEnvP r2 \<and> s1 \<le> r2 \<and> r2 \<le> s \<and> toEnvNum s1 r2 \<le> t \<and> A2 s r2 \<and>
(\<forall> r1. toEnvP r1 \<and> s1 \<le> r1 \<and> r1 < r2 \<longrightarrow> A1 s r1))"

definition constrained_until_inv where "constrained_until_inv s s1 t t1 A1' A2' \<equiv>
(\<exists> r2. toEnvP r2 \<and> s1 \<le> r2 \<and> r2 \<le> s \<and> toEnvNum s1 r2 \<le> t \<and> A2' s r2 \<and>
(\<forall> r1. toEnvP r1 \<and> s1 \<le> r1 \<and> r1 < r2 \<longrightarrow> A1' s r1)) \<or>
toEnvNum s1 s < t1 s \<and>
(\<forall> r1. toEnvP r1 \<and> s1 \<le> r1 \<and> r1 \<le> s \<longrightarrow> A1' s r1)"

lemma constrained_until_rule[patternintro]: "
consecutive s s' \<Longrightarrow>
always_imp s (A1' s) (A1' s') \<and>
always_imp s (A2' s) (A2' s') \<and>
 (t1 s = 0 \<or> A2' s' s' \<and> t1 s \<le> t \<or> A1' s' s' \<and> t1 s < t1 s') \<Longrightarrow>
always_imp s (\<lambda> s1. constrained_until_inv s s1 t t1 A1' A2') (\<lambda> s1. constrained_until_inv s' s1 t t1 A1' A2')"
  apply(unfold constrained_until_inv_def always_imp_def)
    unfolding less_eq_state.simps less_state.simps
  apply(rule allI)
  subgoal for s1
    apply(rule impI)
    apply(erule conjE)+
    apply(rotate_tac -1)
    apply(erule disjE)
     apply (metis consecutive.simps substate_trans)
    apply(erule disjE)
     apply simp
    apply(erule disjE)
     apply(rule disjI1)
     apply(rule exI[of _ s'])
     apply(rule conjI)
      apply simp
     apply(rule conjI)
      apply simp
      apply (meson substate_trans)
     apply(rule conjI)
      apply simp
     apply(rule conjI)
    using toEnvNum3 apply auto[1]
     apply(rule conjI)
      apply simp
     apply (metis consecutive.elims(2) substate_noteq_imp_substate_of_pred)
    using toEnvNum3
    by (smt (verit, ccfv_SIG) consecutive.elims(2) less_imp_add_positive less_numeral_extra(3) less_one linorder_neqE_nat nat_add_left_cancel_less substate_noteq_imp_substate_of_pred trans_less_add1 zero_less_one)
  done

lemma constrained_until_einv2req[patternintro]: "
always_imp s (A1' s) (A1 s) \<and>
always_imp s (A2' s) (A2 s) \<and>
t1 s \<le> t \<Longrightarrow>
always_imp s (\<lambda> s1. constrained_until_inv s s1 t t1 A1' A2') (\<lambda> s1. constrained_until s s1 t A1 A2)"
  unfolding constrained_until_inv_def constrained_until_def always_imp_def less_eq_state.simps less_state.simps
  by (metis dual_order.trans substate_trans verit_comp_simplify1(3))

lemma constrained_until_one_point[patternintro]: "
toEnvP s \<Longrightarrow>A2' s s \<or> A1' s s \<and> t1 s > 0 \<Longrightarrow> constrained_until_inv s s t t1 A1' A2'"
  unfolding constrained_until_inv_def always_imp_def
  by (metis bot_nat_0.extremum dual_order.refl leD order_le_imp_less_or_eq toEnvNum_id)

definition P1 where "P1 s t A1 A2 A3 \<equiv> 
always s s (\<lambda> r2 r1.  \<not> A1 r1 \<or> constrained_until r2 r1 t A2 A3)"

definition P1_inv where "P1_inv s t t1 A1 A2' A3' \<equiv> 
always_inv s (\<lambda> r2 r1.  \<not> A1 r1 \<or> constrained_until_inv r2 r1 t t1 A2' A3')"

schematic_goal P1'inv_rule_gen: "
 P1_inv s t t1 A1 A2' A3' \<Longrightarrow> consecutive s s' \<Longrightarrow>
B1 \<and> B2 \<Longrightarrow>
 P1_inv s' t t1 A1 A2' A3'"
  unfolding P1_inv_def
  apply(erule elims)
   apply assumption
  apply(erule conjE)
  subgoal premises prems1
    apply(rule conjI)
     apply(insert prems1(1,2))[1]










 