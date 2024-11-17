theory Weak_Until
  imports Previous
begin


definition weak_until where "weak_until s1 s A1 A2 \<equiv>
(\<exists> s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s \<and> A2 s3 \<and>
(\<forall> s2. toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s3 \<and> s2 \<noteq> s3 \<longrightarrow> A1 s2)) \<or>
(\<forall> s2. toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s\<longrightarrow> A1 s2)"

definition weak_until_inv where "weak_until_inv s1 s w A1 A2 \<equiv>
(\<exists> s3. toEnvP s3 \<and> substate s1 s3 \<and> substate s3 s \<and> A2 s3 \<and>
(\<forall> s2. toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s3 \<and> s2 \<noteq> s3 \<longrightarrow> A1 s2)) \<or>
w \<and> (\<forall> s2. toEnvP s2 \<and> substate s1 s2 \<and> substate s2 s\<longrightarrow> A1 s2)"

lemma weak_until_rule: "consecutive s0 s \<Longrightarrow>
(\<forall> s1. toEnvP s1 \<and> substate s1 s0 \<and> A1 s1 \<longrightarrow> A1' s1) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s0 \<and> A2 s1 \<longrightarrow> A2' s1) \<and>
(\<not> w \<or>  A2' s \<or> w' \<and> A1' s) \<Longrightarrow>
\<forall> s1. toEnvP s1 \<and> substate s1 s0 \<and> weak_until_inv s1 s0 w A1 A2 \<longrightarrow> weak_until_inv s1 s w' A1' A2'"
  apply(unfold weak_until_inv_def)
  by (smt (verit, best) consecutive.elims(2) substate_noteq_imp_substate_of_pred substate_refl substate_trans)

lemma weak_until_one_point: "toEnvP s \<Longrightarrow> A2 s \<or> w \<and> A1 s \<Longrightarrow> weak_until_inv s s w A1 A2"
  apply(unfold weak_until_inv_def)
  using substate_antisym substate_refl by blast

lemma weak_until_einv2req: "
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> A1 s1 \<longrightarrow> A1' s1) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> A2 s1 \<longrightarrow> A2' s1) \<Longrightarrow>
\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> weak_until_inv s1 s w A1 A2 \<longrightarrow> weak_until s1 s A1' A2'"
  apply(unfold weak_until_inv_def weak_until_def)
  by (meson substate_trans)

definition P3 where "P3 s A11 A12 A2 A31 A32 \<equiv>
always2 s (\<lambda> s2. previous s2 A11 \<and> A12 s2) (\<lambda> s3.  True) (\<lambda> s3. weak_until s3 s A2
 (\<lambda> s4. previous s4 A31 \<and> A32 s4))"

definition P3inv where "P3inv s w b1 b2 b3 A11 A12 A2 A31 A32 \<equiv>
always2_inv s b1 (\<lambda> s2. previous s2 A11 \<and> A12 s2) (\<lambda> s3.  True) (\<lambda> s3. weak_until_inv s3 s w A2
 (\<lambda> s4. previous s4 A31 \<and> A32 s4)) \<and> (b2 \<longrightarrow> \<not>A11 s) \<and> (b3 \<longrightarrow> A31 s)"

lemma P3_rule_gen: "
P3inv s0 w b1 b2 b3 A11 A12 A2 A31 A32 \<Longrightarrow> consecutive s0 s \<Longrightarrow>
(( ( b1 \<or> b3 \<and> A32' s \<or> w' \<and> A2' s ) \<and> ((\<forall> s1. toEnvP s1 \<and> substate s1 s0 \<and> A2 s1 \<longrightarrow> A2' s1) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s0 \<and> A32 s1 \<longrightarrow> A32' s1) \<and>
(\<not> w \<or> b3 \<and> A32' s \<or> w' \<and> A2' s))) \<and> (b1' \<longrightarrow> b2 \<or> \<not>A12 s)) \<and>
 (b2' \<longrightarrow>\<not> A11 s) \<and> (b3' \<longrightarrow> A31 s) \<Longrightarrow>
P3inv s w' b1' b2' b3' A11 A12 A2' A31 A32'"
  apply(unfold P3inv_def)
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
          apply simp
         apply(rule disjI2)
         apply(rule weak_until_one_point)
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
          apply simp
          done
         apply(rule disjI2)
         apply simp
        apply(insert prems3(1,3))
        apply(rule weak_until_rule)
        apply simp
        apply(erule conjE)
        subgoal premises prems4
          apply(rule conjI)
           apply(insert prems4(1,2))[1]
           apply simp
          apply(insert prems4(1,3))
          apply(erule conjE)
          subgoal premises prems5
            apply(rule conjI)
             apply(insert prems5(1,2))[1]
             apply simp
            apply(insert prems5(1,3))
            apply(erule disjE)
             apply(rule disjI1)
             apply simp
            apply(rule disjI2)
            apply(erule disjE)
             apply(rule disjI1)
             apply(erule conjE)
            subgoal premises prems6
              apply(rule conjI)
               apply(insert prems6(1,2))[1]
               apply(rule previous_one_point[of s0])
                apply simp
               apply (simp add: prems1(3))
              apply(insert prems6(1,3))
              apply simp
              done
            apply(rule disjI2)
            apply simp
            done
          done
        done
      apply(insert prems2(1,3))
      apply(simp only: imp_conv_disj)
      apply(erule disjE)
       apply(rule disjI1)
       apply simp
      apply(rule disjI2)
      apply(simp only: de_Morgan_conj previous_ex_not)
      apply(erule disjE)
       apply(rule disjI1)
       apply(rule weak_previous_one_point[of s0])
        apply simp
      using prems1(3) apply simp
      apply(rule disjI2)
      apply simp
      done
    apply(insert prems1(1,3,5))
    apply simp
    done
  done

lemma P3_einv2req_gen: "P3inv  s w b1 b2 b3 A11 A12 A2 A31 A32 \<Longrightarrow>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> A2 s1 \<longrightarrow> A2' s1) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> A32 s1 \<longrightarrow> A32' s1) \<Longrightarrow>
 P3 s A11 A12 A2' A31 A32'"
  apply(unfold P3_def P3inv_def)
  using always2_einv2req weak_until_einv2req
  by (smt (verit, ccfv_threshold))

lemma P3_rule: "
P3inv s0 w b1 b2 b3 A11 A12 A2 A31 A32 \<Longrightarrow> consecutive s0 s \<Longrightarrow>
(( ( b1 \<or> b3 \<and> A32 s \<or> w' \<and> A2 s ) \<and> 
(\<not> w \<or> b3 \<and> A32 s \<or> w' \<and> A2 s)) \<and> (b1' \<longrightarrow> b2 \<or> \<not>A12 s)) \<and>
 (b2' \<longrightarrow>\<not> A11 s) \<and> (b3' \<longrightarrow> A31 s) \<Longrightarrow>
P3inv s w' b1' b2' b3' A11 A12 A2 A31 A32"
  using P3_rule_gen apply auto
  done
      
lemma P6_3_einv2req: "P3inv  s w b1 b2 b3 A11 A12 A2 A31 A32 \<Longrightarrow>
 P3 s A11 A12 A2 A31 A32"
  using P3_einv2req_gen apply auto
  done

definition P3_1 where "P3_1 s A11 A12 A2 A3 \<equiv>
P3 s A11 A12 A2 (\<lambda> s4. True) A3"

definition P3_1inv where "P3_1inv s w b1 b2 A11 A12 A2 A3 \<equiv>
P3inv s w b1 b2 True A11 A12 A2 (\<lambda> s4. True) A3"

lemma P3_1_rule_gen: "
P3_1inv s0 w b1 b2 A11 A12 A2 A3 \<Longrightarrow> consecutive s0 s \<Longrightarrow>
(( ( b1 \<or>  A3' s \<or> w' \<and> A2' s ) \<and> ((\<forall> s1. toEnvP s1 \<and> substate s1 s0 \<and> A2 s1 \<longrightarrow> A2' s1) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s0 \<and> A3 s1 \<longrightarrow> A3' s1) \<and>
(\<not> w \<or>  A3' s \<or> w' \<and> A2' s))) \<and> (b1' \<longrightarrow> b2 \<or> \<not>A12 s)) \<and>
 (b2' \<longrightarrow>\<not> A11 s)  \<Longrightarrow>
P3_1inv s w' b1' b2' A11 A12 A2' A3'"
  apply(unfold P3_1inv_def)
  using P3_rule_gen apply auto
  done

lemma P3_1_einv2req_gen: "P3_1inv  s w b1 b2 A11 A12 A2 A3 \<Longrightarrow>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> A2 s1 \<longrightarrow> A2' s1) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> A3 s1 \<longrightarrow> A3' s1) \<Longrightarrow>
 P3_1 s A11 A12 A2' A3'"
  apply(unfold P3_1inv_def P3_1_def)
  using P3_einv2req_gen apply auto
  done

lemma P31_rule: "
P3_1inv s0 w b1 b2 A11 A12 A2 A3 \<Longrightarrow> consecutive s0 s \<Longrightarrow>
(( ( b1 \<or>  A3 s \<or> w' \<and> A2 s ) \<and> 
(\<not> w \<or>  A3 s \<or> w' \<and> A2 s)) \<and> (b1' \<longrightarrow> b2 \<or> \<not>A12 s)) \<and>
 (b2' \<longrightarrow>\<not> A11 s)  \<Longrightarrow>
P3_1inv s w' b1' b2' A11 A12 A2 A3"
  apply(unfold P3_1inv_def)
  using P3_rule_gen apply auto
  done

lemma P3_1_einv2req: "P3_1inv  s w b1 b2 A11 A12 A2 A3 \<Longrightarrow>
 P3_1 s A11 A12 A2 A3"
  apply(unfold P3_1inv_def P3_1_def)
  using P3_einv2req_gen apply auto
  done


end
