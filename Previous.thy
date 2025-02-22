theory Previous
  imports Always
begin

definition weak_previous where " weak_previous A (s::state) s1 \<equiv>
\<forall> r1. consecutive r1 s1 \<longrightarrow> A s r1"

definition previous where "previous A (s::state) s1 \<equiv>
\<exists> r1. consecutive r1 s1 \<and> A s r1"

definition previous_inv where "previous_inv (A::state\<Rightarrow>state\<Rightarrow>bool) (s::state) \<equiv> A s s"

definition always2 where  "always2 A1 A2 A3 s \<equiv> 
always (\<lambda> r2 r1. weak_previous (\<lambda> r4 r3. \<not> A1 r3) r2 r1 \<or> \<not> A2 r1 \<or> A3 r2 r1) s"

definition always2_inv where  "always2_inv b A1 A2 A3 s \<equiv> 
always_inv (\<lambda> r2 r1. weak_previous (\<lambda> r4 r3. \<not> A1 r3) r2 r1 \<or> \<not> A2 r1 \<or> A3 r2 r1) s
 \<and> (b s \<longrightarrow> previous_inv (\<lambda> r2 r1. \<not> A1 r1) s )"

lemma weak_previous_one_point[patternintro]: "consecutive s s'
 \<Longrightarrow> previous_inv A s \<and> always_imp s (A s) (A s')
 \<Longrightarrow> weak_previous A s' s'"
  unfolding previous_inv_def weak_previous_def always_imp_def
  apply simp
  by (metis substate_refl toEnvNum_eq_imp_eq2)

lemma previous_one_point[patternintro]: "consecutive s s' \<Longrightarrow> previous_inv A s \<and> always_imp s (A s) (A s')
  \<Longrightarrow> previous  A s' s'"
  unfolding previous_inv_def previous_def always_imp_def
  by auto

lemma previous_rule[pastinv]: "consecutive s s' \<Longrightarrow> A s' s' \<Longrightarrow> previous_inv A s'"
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

lemma always2_rule_gen: 
"always2_inv b A1 A2 A3 s \<Longrightarrow> consecutive s s'
 \<Longrightarrow> ((True \<and> True \<and>  always_imp s (A3 s) (A3 s')) \<and> (b s \<and> True \<or> \<not> A2 s' \<or> A3 s' s')) \<and> (b s' \<longrightarrow> \<not> A1 s')
 \<Longrightarrow> always2_inv b A1 A2 A3  s'"
  unfolding always2_inv_def
  apply(proveOuter add_rules: invsaving)
  done
 (* apply(erule conjE)
  apply(erule conjE)
  subgoal premises prems1
    apply(rule conjI)
     apply(insert prems1(1,2,4))[1]
     apply(erule elims)
      apply assumption
     apply(erule conjE)
    subgoal premises prems2
       apply(rule conjI)
       apply(insert prems2(1,2))[1]
       apply(rule patternintro)
        apply simp
       apply(erule conjE)
      subgoal premises prems3
        apply(rule conjI)
         apply(insert prems3(1,2))[1]
         apply(rule invsaving)
          apply assumption
        apply prove
        apply(insert prems3(1,3))
        apply(rule patternintro)
         apply simp
        apply(erule conjE)
        subgoal premises prems4
          apply(rule conjI)
           apply(insert prems4(1,2))[1]
           apply(rule always_imp_refl)
          apply(insert prems4(1,3))
          apply assumption
          done
        done
      apply(insert prems2(1,3))
      apply(erule disjE)
       apply(rule disjI1)
       apply(rule patternintro)
        apply assumption
       apply(erule conjE)
      subgoal premises prems3
        apply(rule conjI)
         apply(insert prems3(1,2))[1]
         apply(rule mp[OF prems1(3) prems3(2)])
        apply(insert prems3(1,3))
        apply(rule always_imp_refl)
        done
      apply(rule disjI2)
      apply assumption
      done
    apply(insert prems1(1,5))
    apply(rule impI)
    apply(erule impE)
     apply assumption
    subgoal premises prems2
      apply(insert prems2(1,3))
      apply(rule pastinv)
       apply assumption
      apply assumption
      done
    done
  done
*)

lemma always2_rule_gen_simp[elims]:
"always2_inv b A1 A2 A3 s \<Longrightarrow> consecutive s s'
 \<Longrightarrow> ((always_imp s (A3 s) (A3 s')) \<and> (b s \<or> \<not> A2 s' \<or> A3 s' s')) \<and> (b s' \<longrightarrow> \<not> A1 s')
 \<Longrightarrow> always2_inv b A1 A2 A3  s'"
  by(simp add: always2_rule_gen)

lemma always2_einv2req_gen: 
"always2_inv b A1 A2 A3' s \<Longrightarrow> toEnvP s
 \<Longrightarrow> True \<and> True \<and> always_imp s (A3' s) (A3 s)
 \<Longrightarrow> always2 A1 A2 A3 s"
  unfolding always2_inv_def always2_def
  apply(proveOuter add_rules: inv_req)
  done
 (* apply(erule conjE)
  subgoal premises prems1
    apply(insert prems1(1,2,3))
    apply(rotate_tac -1)
    apply(erule elims)
     apply assumption
    apply(rule patternintro)
     apply assumption
    apply(erule conjE)
    subgoal premises prems2
      apply(rule conjI)
       apply(insert prems2(1,2))[1]
       apply(rule inv_req)
        apply assumption
       apply(rule always_imp_refl)
      apply(insert prems2(1,3))
      apply(rule patternintro)
       apply assumption
      apply(erule conjE)
      subgoal premises prems3
        apply(rule conjI)
         apply(insert prems3(1,2))[1]
         apply(rule always_imp_refl)
        apply(insert prems3(1,3))
        apply assumption
        done
      done
    done
  done
*)

lemma always2_einv2req_gen_simp[elims]: 
"always2_inv b A1 A2 A3' s \<Longrightarrow> toEnvP s
 \<Longrightarrow> always_imp s (A3' s) (A3 s)
 \<Longrightarrow> always2 A1 A2 A3 s"
  by(simp add: always2_einv2req_gen)

end
