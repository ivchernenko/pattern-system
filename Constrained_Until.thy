theory Constrained_Until
  imports Previous
begin

definition constrained_until where "constrained_until t A1 A2  s s1 \<equiv>
toEnvNum s1 s \<ge> t \<longrightarrow>
(\<exists> r2. toEnvP r2 \<and> s1 \<le> r2 \<and> r2 \<le> s \<and> toEnvNum s1 r2 \<le> t \<and> A2 s r2 \<and>
(\<forall> r1. toEnvP r1 \<and> s1 \<le> r1 \<and> r1 < r2 \<longrightarrow> A1 s r1))"

definition constrained_until_inv where "constrained_until_inv  t t1 A1' A2' s s1 \<equiv>
(\<exists> r2. toEnvP r2 \<and> s1 \<le> r2 \<and> r2 \<le> s \<and> toEnvNum s1 r2 \<le> t \<and> A2' s r2 \<and>
(\<forall> r1. toEnvP r1 \<and> s1 \<le> r1 \<and> r1 < r2 \<longrightarrow> A1' s r1)) \<or>
toEnvNum s1 s < t1 s \<and>
(\<forall> r1. toEnvP r1 \<and> s1 \<le> r1 \<and> r1 \<le> s \<longrightarrow> A1' s r1)"

lemma constrained_until_rule[patternintro]: "
consecutive s s' \<Longrightarrow>
always_imp s (A1' s) (A1' s') \<and>
always_imp s (A2' s) (A2' s') \<and>
 (t1 s = 0 \<or> A2' s' s' \<and> t1 s \<le> t \<or> A1' s' s' \<and> t1 s < t1 s') \<Longrightarrow>
always_imp s (\<lambda> s1. constrained_until_inv t t1 A1' A2' s s1) (\<lambda> s1. constrained_until_inv t t1 A1' A2' s' s1)"
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
toEnvP s \<Longrightarrow>
always_imp s (A1' s) (A1 s) \<and>
always_imp s (A2' s) (A2 s) \<and>
t1 s \<le> t \<Longrightarrow>
always_imp s (\<lambda> s1. constrained_until_inv t t1 A1' A2' s s1) (\<lambda> s1. constrained_until  t A1 A2 s s1)"
  unfolding constrained_until_inv_def constrained_until_def always_imp_def less_eq_state.simps less_state.simps
  by (metis dual_order.trans substate_trans verit_comp_simplify1(3))

lemma constrained_until_one_point[patternintro]: "
toEnvP s \<Longrightarrow>A2' s s \<or> A1' s s \<and> t1 s > 0 \<Longrightarrow> constrained_until_inv t t1 A1' A2' s s"
  unfolding constrained_until_inv_def always_imp_def
  by (metis bot_nat_0.extremum dual_order.refl leD order_le_imp_less_or_eq toEnvNum_id)

definition P1 where "P1 t A1 A2 A3 s \<equiv> 
always  (\<lambda> r2 r1.  \<not> A1 r1 \<or> constrained_until t A2 A3 r2 r1) s"

definition P1_inv where "P1_inv t t1 A1 A2' A3' s \<equiv> 
always_inv (\<lambda> r2 r1.  \<not> A1 r1 \<or> constrained_until_inv t t1 A2' A3' r2 r1) s"

lemma P1'inv_rule_gen: "
 P1_inv t t1 A1 A2' A3' s \<Longrightarrow> consecutive s s' \<Longrightarrow>
(always_imp s (\<lambda>s1. \<not> A1 s1) (\<lambda>s1. \<not> A1 s1) \<and>  always_imp s (A2' s) (A2' s') \<and>
    always_imp s (A3' s) (A3' s') \<and> (t1 s = STOP \<or> A3' s' s' \<and> t1 s \<le> t \<or> A2' s' s' \<and> t1 s < t1 s')) \<and>
 (\<not> A1 s' \<or> A3' s' s' \<or> A2' s' s' \<and> STOP < t1 s') \<Longrightarrow>
 P1_inv t t1 A1 A2' A3'  s'"
  unfolding P1_inv_def
  apply proveOuter
  done
 (* apply(erule elims)
   apply assumption
  apply(erule conjE)
  subgoal premises prems1
    apply(rule conjI)
     apply(insert prems1(1,2))[1]
     apply(rule patternintro)
      apply simp
     apply(erule conjE)
    subgoal premises prems2
      apply(rule conjI)
       apply(insert prems2(1,2))[1]
       apply assumption
      apply(insert prems2(1,3))
      apply(rule patternintro)
       apply assumption
      apply assumption
      done
    apply(insert prems1(1,3))
    apply(erule disjE)
     apply(rule disjI1)
     apply assumption
    apply(rule disjI2)
    apply(rule patternintro)
     apply simp
    apply assumption
    done
  done
*)

lemma P1'inv_einv2req_gen: "
 P1_inv t t1 A1 A2' A3' s \<Longrightarrow> toEnvP s \<Longrightarrow>
always_imp s (\<lambda>s1. \<not> A1 s1) (\<lambda>s1. \<not> A1 s1) \<and>  always_imp s (A2' s) (A2' s) \<and> always_imp s (A3' s) (A3' s) \<and> t1 s \<le> t
  \<Longrightarrow>
 P1 t A1 A2' A3' s"
  unfolding P1_inv_def P1_def
  apply proveOuter
  done
(*  apply(erule elims)
   apply assumption
  apply(rule patternintro)
   apply assumption
  apply(erule conjE)
  subgoal premises prems1
    apply(rule conjI)
     apply(insert prems1(1,2))[1]
     apply assumption
    apply(insert prems1(1,3))
    apply(rule patternintro)
     apply assumption
    apply assumption
    done
  done
*)

end
 