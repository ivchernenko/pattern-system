theory Previous
  imports Always
begin

definition weak_previous where " weak_previous s A \<equiv>
\<forall> s1. consecutive s1 s \<longrightarrow> A s1"

definition previous where "previous s A \<equiv>
\<exists> s1. consecutive s1 s \<and> A s1"

definition always2 where  "always2 s A1 A2 A3 \<equiv> 
always s (\<lambda> s2.( previous s2 A1) \<and> A2 s2 \<longrightarrow> A3 s2)"

definition always2_inv where  "always2_inv s b A1 A2 A3 \<equiv> 
always s (\<lambda> s2.( previous s2 A1) \<and> A2 s2 \<longrightarrow> A3 s2) \<and> (b \<longrightarrow> \<not>A1 s)"

lemma weak_previous_one_point: "consecutive s0 s \<Longrightarrow>  A s0 \<Longrightarrow> weak_previous s A"
  apply(unfold  weak_previous_def)
  apply simp
  by (metis toEnvNum_eq_imp_eq2)

lemma previous_one_point: "consecutive s0 s \<Longrightarrow>  A s0  \<Longrightarrow> previous s A"
  apply(unfold  previous_def)
  by auto

lemma previous_ex_not: "\<not> previous s A \<longleftrightarrow> weak_previous s (\<lambda> s0. \<not> A s0)"
  using weak_previous_def previous_def by presburger

lemma always2_rule: "
always2_inv s0 b A1 A2 A3 \<Longrightarrow>consecutive s0 s \<Longrightarrow> (((b \<or> ~ A2 s) \<or> A3' s) \<and> (\<forall> s1. toEnvP s1 \<and> substate s1 s0 \<and> A3 s1 \<longrightarrow> A3' s1)) \<and> (b' \<longrightarrow> \<not>A1 s) \<Longrightarrow>
 always2_inv s b' A1 A2 A3'"
  apply(unfold always2_inv_def)
  apply(simp only: imp_conv_disj de_Morgan_conj previous_ex_not )
  apply(erule conjE)
  apply(erule conjE)
  subgoal premises prems1
    apply(rule conjI)
     apply(insert prems1(1,2,4))[1]
     apply(erule always_rule)
      apply simp
     apply(erule conjE)
    subgoal premises prems2
      apply(rule conjI)
       apply(insert prems2(1,2))[1]
       apply(erule disjE)
        apply(rule disjI1)
        apply(erule disjE)
         apply(rule disjI1)
         apply(rule weak_previous_one_point[of s0])
      apply simp
      using prems1(3) apply simp
        apply(rule disjI2)
        apply assumption 
       apply(rule disjI2)
       apply assumption
      apply(insert prems2(1,3))[1]
      apply auto
      done
    apply(insert prems1(1,3,5))
    apply simp
    done
  done

lemma always2_einv2req: "always2_inv s b A1 A2 A3 \<Longrightarrow>  (\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> A3 s1 \<longrightarrow> A3' s1) \<Longrightarrow> always2 s A1 A2 A3'"
  apply(unfold always2_def always2_inv_def)
  by (metis (mono_tags, lifting) always_einv2req)

definition always2_2 where  "always2_2 s A1 A2 A3 \<equiv> 
always2 s A1 A2 (\<lambda> s2. weak_previous s2 (\<lambda> s1. A3 s1 s2))"

definition always2_2_inv where  "always2_2_inv s b A1 A2 A3 \<equiv> 
always2_inv s b A1 A2 (\<lambda> s2. weak_previous s2 (\<lambda> s1. A3 s1 s2))"

lemma always2_2_rule: "
always2_2_inv s0 b A1 A2 A3 \<Longrightarrow>consecutive s0 s \<Longrightarrow> (((b \<or> ~ A2 s) \<or> A3 s0 s) ) \<and> (b' \<longrightarrow> \<not>A1 s) \<Longrightarrow>
 always2_2_inv s b' A1 A2 A3"
  apply(unfold always2_2_inv_def)
  apply(erule always2_rule)
   apply simp
  apply(erule conjE)
  subgoal premises prems1
    apply(rule conjI)
     apply(insert prems1(1,2))[1]
     apply(rule conjI)
      apply(erule disjE)
       apply(rule disjI1)
       apply simp
      apply(rule disjI2)
      apply(rule weak_previous_one_point[of s0])
       apply simp
      apply simp
     apply simp
    apply(insert prems1(1,3))
    apply simp
    done
  done

end