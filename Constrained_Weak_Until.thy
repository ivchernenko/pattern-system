theory Constrained_Weak_Until
  imports Previous
begin

definition constrained_weak_until where "constrained_weak_until s1 s t A1 A2 \<equiv>
(\<exists> s4. toEnvP s4 \<and> substate s1 s4 \<and> substate s4 s \<and> toEnvNum s1 s4 \<le> t \<and> A2 s4 \<and>
(\<forall> s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow> A1 s3)) \<or>
(\<forall> s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s \<and> toEnvNum s1 s3 \<le> t \<longrightarrow> A1 s3)"

definition constrained_weak_until_inv where "constrained_weak_until_inv s1 s t t1 A1 A2 \<equiv>
(\<exists> s4. toEnvP s4 \<and> substate s1 s4 \<and> substate s4 s \<and> toEnvNum s1 s4 \<le> t \<and> A2 s4 \<and>
(\<forall> s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow> A1 s3)) \<or>
toEnvNum s1 s \<ge> t1 \<and>
(\<forall> s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s \<and> toEnvNum s1 s3 \<le> t \<longrightarrow> A1 s3)"

lemma constrained_weak_until_one_point: "toEnvP s \<Longrightarrow> A2 s \<or> t1 = 0 \<and> A1 s \<Longrightarrow> constrained_weak_until_inv s s t t1 A1 A2"
  apply(unfold constrained_weak_until_inv_def)
  by (metis substate_antisym substate_refl toEnvNum_id zero_le)

lemma constrained_weak_until_rule: " consecutive s0 s \<Longrightarrow>
(\<forall> s1. toEnvP s1 \<and> substate s1 s0 \<and> A1 s1 \<longrightarrow> A1' s1) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s0 \<and> A2 s1 \<longrightarrow> A2' s1) \<and>
(t1 < t \<and> (A2' s \<and>  t1' \<le> t+1  \<or>  t1' \<le> t1 + 1 \<and> A1' s) \<or> t1 \<ge> t \<and> t1' \<le> t1 + 1) \<Longrightarrow>
(\<forall> s1. toEnvP s1 \<and> substate s1 s0 \<and> constrained_weak_until_inv s1 s0 t t1 A1 A2 \<longrightarrow> constrained_weak_until_inv s1 s t t1' A1' A2')"
  apply(unfold constrained_weak_until_inv_def)
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
       apply (metis consecutive.elims(2) le_Suc_ex less_or_eq_imp_le substate_noteq_imp_substate_of_pred toEnvNum3 trans_le_add1)
    apply(rule disjI2)
      apply (smt (verit, ccfv_SIG) add.commute consecutive.elims(2) leD leI le_iff_add le_neq_implies_less le_numeral_extra(4) le_trans less_add_one nat_add_left_cancel_le nat_le_linear order.strict_trans1 substate_noteq_imp_substate_of_pred toEnvNum3)
    apply (smt (verit, best) add.commute consecutive.elims(2) nat_add_left_cancel_le order_subst1 substate_noteq_imp_substate_of_pred toEnvNum3)
    apply(rule disjI2)
    apply(rule conjI)
    using toEnvNum3 apply fastforce
    by (metis consecutive.elims(2) dual_order.trans leD less_add_one substate_noteq_imp_substate_of_pred toEnvNum3)
  done

lemma constrained_weak_until_einv2req: "
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> A1 s1 \<longrightarrow> A1' s1) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> A2 s1 \<longrightarrow> A2' s1) \<Longrightarrow>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> constrained_weak_until_inv s1 s t t1 A1 A2 \<longrightarrow> constrained_weak_until s1 s t A1' A2')"
  apply(unfold constrained_weak_until_inv_def constrained_weak_until_def)
  by (meson substate_trans)

definition P4 where "P4 s t A11 A12 A2 A31 A32 \<equiv>
always2 s A11 A12 (\<lambda> s2. constrained_weak_until s2 s t A2 (\<lambda> s4. previous s4 A31 \<and> A32 s4))"

definition P4inv where "P4inv s t t1 b1 b2 A11 A12 A2 A31 A32 \<equiv>
always2_inv s b1 A11 A12 (\<lambda> s2. constrained_weak_until_inv s2 s t t1 A2 (\<lambda> s4. previous s4 A31 \<and> A32 s4)) \<and>  (b2 \<longrightarrow> A31 s)" 

lemma P7_2_rule: "
P4inv s0 t t1 b1 b2 A1 A2 A3 A4 A5 \<Longrightarrow>consecutive s0 s \<Longrightarrow>
 (((( b1 \<or> \<not> A2 s)  \<or> b2 \<and> A5 s \<or> t1' = 0 \<and> A3 s) \<and> 
(t1 < t \<and> ((b2 \<and> A5 s) \<and>  t1' \<le> t+1  \<or>  t1' \<le> t1 + 1 \<and> A3 s) \<or> t1 \<ge> t \<and> t1' \<le> t1 + 1)) \<and> (b1' \<longrightarrow> \<not> A1 s)) \<and> (b2' \<longrightarrow> A4 s) \<Longrightarrow>
P4inv s t t1' b1' b2' A1 A2 A3 A4 A5"
  apply(unfold P4inv_def)
  apply(erule conjE)
  apply(erule conjE)
  subgoal premises prems1
    apply(rule conjI)
     apply(insert prems1(1,2,4))[1]
     apply(erule always2_rule)
      apply simp
     apply(erule conjE)
    subgoal premises prems2
      apply(rule conjI)
       apply(insert prems2(1,2))[1]
       apply(erule conjE)
      subgoal premises prems3
        apply(rule conjI)
         apply(insert prems3(1,2))[1]
         apply(erule disjE)
          apply(rule disjI1)
          apply assumption
         apply(rule disjI2)
         apply(rule constrained_weak_until_one_point)
          apply simp
         apply(erule disjE)
          apply(rule disjI1)
          apply(erule conjE)
        subgoal premises prems4
          apply(rule conjI)
           apply(insert prems4(1,2))[1]
           apply(rule previous_one_point[of s0])
            apply simp
           apply (simp add: prems1(3))
          apply(insert prems4(1,3))
          apply assumption
          done
         apply(rule disjI2)
         apply assumption
        apply(insert prems3(1,3))
        apply(rule constrained_weak_until_rule)
         apply simp
        apply(rule conjI)
         apply simp
        apply(rule conjI)
         apply simp
        apply(erule disjE)
         apply(rule disjI1)
         apply(erule conjE)
        subgoal premises prems4
          apply(rule conjI)
           apply(insert prems4(1,2))[1]
           apply assumption
          apply(insert prems4(1,3))
          apply(erule disjE)
           apply(rule disjI1)
           apply(erule conjE)
          subgoal premises prems5
            apply(rule conjI)
             apply(insert prems5(1,2))[1]
             apply(erule conjE)
            subgoal premises prems6
              apply(rule conjI)
               apply(insert prems6(1,2))[1]
               apply(rule previous_one_point[of s0])
              apply simp
               apply (simp add: prems1(3))
              apply(insert prems6(1,3))
              apply assumption
              done
            apply(insert prems5(1,3))
            apply assumption
            done
          apply(rule disjI2)
          apply assumption
          done
        apply(rule disjI2)
        apply assumption
        done
      apply(insert prems2(1,3))
      apply simp
      done
    apply(insert prems1(1,3,5))
    apply simp
    done
  done

lemma P7_2_einv2req: "P4inv s t t1 b1 b2  A1 A2 A3 A4 A5 \<Longrightarrow> P4 s t A1 A2 A3 A4 A5"
  apply(unfold P4inv_def P4_def)
  using always2_einv2req constrained_weak_until_einv2req
  by (smt (verit, ccfv_SIG))

end
