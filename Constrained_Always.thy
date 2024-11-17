theory Constrained_Always
  imports Previous
begin


definition constrained_always where "constrained_always s1 s t A \<equiv>
\<forall> s2. toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s \<and> toEnvNum s1 s2 < t \<longrightarrow> A s2"

definition constrained_always_inv where "constrained_always_inv s1 s t t1 A \<equiv>
t = 0 \<or>toEnvNum s1 s \<ge> t1 \<and>
(\<forall> s2. toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s \<and> toEnvNum s1 s2 < t \<longrightarrow> A s2)"

lemma constrained_always_rule: "consecutive s0 s \<Longrightarrow>
t = 0 \<or> (\<forall> s1. toEnvP s1 \<and> substate s1 s0 \<and> A s1 \<longrightarrow> A' s1) \<and>
(t1 + 1 \<ge> t \<or> A' s) \<and> t1' \<le> t1 + 1 \<Longrightarrow>
(\<forall> s1. toEnvP s1 \<and> substate s1 s0 \<and> constrained_always_inv s1 s0 t t1 A \<longrightarrow> constrained_always_inv s1 s t t1' A')"
  apply(unfold constrained_always_inv_def)
  apply(cases "t = 0")
   apply simp_all
  by (smt (verit) One_nat_def Suc_eq_plus1 dual_order.trans leD not_less_eq_eq substate_noteq_imp_substate_of_pred toEnvNum3)

lemma constrained_always_one_point: "t = 0 \<or> t1 = 0 \<and> ( A s) \<Longrightarrow> constrained_always_inv s s t t1 A"
  apply(unfold constrained_always_inv_def)
  using substate_antisym by blast

lemma constrained_always_einv2req: "
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> A s1 \<longrightarrow> A' s1) \<Longrightarrow>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> constrained_always_inv s1 s t t1 A \<longrightarrow> constrained_always s1 s t A')"
  apply(unfold constrained_always_inv_def constrained_always_def)
  apply auto
  done

definition P2 where "P2 s t A1 A2 A3 \<equiv>
always2 s A1 A2 (\<lambda> s2. constrained_always s2 s t A3)"

definition P2inv where "P2inv s t t1 b A1 A2 A3 \<equiv>
always2_inv s b A1 A2 (\<lambda> s2. constrained_always_inv s2 s t t1 A3)"

lemma P2_rule: "
P2inv s0 t t1 b A1 A2 A3 \<Longrightarrow>consecutive s0 s \<Longrightarrow> (((b \<or> \<not> A2 s) \<or> t = 0 \<or> t1' = 0 \<and> A3 s) \<and> (t = 0 \<or>(t1 + 1 \<ge> t \<or> A3 s) \<and> t1' \<le> t1 + 1)) \<and> (b' \<longrightarrow> \<not> A1 s) \<Longrightarrow>
P2inv s t t1' b' A1 A2 A3"
  apply(unfold P2inv_def)
  apply(erule always2_rule)
   apply simp
  apply(erule conjE)
  subgoal premises prems1
    apply(rule conjI)
     apply(insert prems1(1,2))[1]
     apply(erule conjE)
    subgoal premises prems2
      apply(rule conjI)
       apply(insert prems2(1,2))[1]
       apply(erule disjE)
        apply(rule disjI1)
        apply assumption
       apply(rule disjI2)
       apply(rule constrained_always_one_point)
       apply assumption
      apply(insert prems2(1,3))
      apply(rule constrained_always_rule)
      apply simp
      apply simp
      done
    apply(insert prems1(1,3))
    apply simp
    done
  done

lemma P2_einv2req: "P2inv s t t1 b A1 A2 A3 \<Longrightarrow> P2 s t A1 A2 A3"
  apply(unfold P2inv_def P2_def)
  using always2_einv2req constrained_always_einv2req
  by (metis (no_types, lifting))

definition P5_1 where "P5_1 s t A1 A2 \<equiv>
always s (\<lambda> s1. A1 s1 \<longrightarrow> constrained_always s1 s t A2)"

definition P5_1inv where "P5_1inv s t t1 A1 A2 \<equiv>
always s (\<lambda> s1. A1 s1 \<longrightarrow> constrained_always_inv s1 s t t1 A2)"

lemma P5_1_rule: "
P5_1inv s0 t t1 A1 A2 \<Longrightarrow>consecutive s0 s \<Longrightarrow> ((( \<not> A1 s) \<or> t = 0 \<or> t1' = 0 \<and> A2 s) \<and> (t = 0 \<or>(t1 + 1 \<ge> t \<or> A2 s) \<and> t1' \<le> t1 + 1)) \<Longrightarrow>
P5_1inv s t t1' A1 A2"
  apply(unfold P5_1inv_def)
  apply(simp only: imp_conv_disj)
  apply(erule always_rule)
   apply simp
  apply(erule conjE)
  subgoal premises prems1
    apply(rule conjI)
     apply(insert prems1(1,2))[1]
     apply(erule disjE)
      apply(rule disjI1)
      apply assumption
     apply(rule disjI2)
     apply(rule constrained_always_one_point)
     apply assumption
    apply(insert prems1(1,3))
    apply(rule all_disj_rule)
    apply(rule conjI)
     apply simp
    apply(rule constrained_always_rule)
     apply simp
    apply simp
    done
  done

lemma P5_1_einv2req: "P5_1inv s t t1  A1 A2 \<Longrightarrow> P5_1 s t A1 A2"
  apply(unfold P5_1inv_def P5_1_def)
  using always_einv2req constrained_always_einv2req
  by (smt (verit, ccfv_SIG))

end
