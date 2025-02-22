theory Constrained_Always
  imports Previous
begin

definition constrained_always where "constrained_always t A  s s1 \<equiv>
\<forall> r1. toEnvP r1 \<and> s1 \<le> r1 \<and> r1 \<le> s \<and> toEnvNum s1 r1 < t \<longrightarrow> A s r1"

definition constrained_always_inv where "constrained_always_inv t t1 A  s s1 \<equiv>
t = 0
 \<or> toEnvNum s1 s \<ge> t1 s \<and> (\<forall> r1. toEnvP r1 \<and> s1 \<le> r1 \<and> r1 \<le> s \<and> toEnvNum s1 r1 < t \<longrightarrow> A s r1)"

lemma constrained_always_rule[patternintro]: "consecutive s s' \<Longrightarrow>
t = 0 \<or> always_imp s (A s) (A s') \<and>
(t1 s + 1 \<ge> t \<or> A s' s') \<and> t1 s' \<le> t1 s + 1 \<Longrightarrow>
always_imp s (\<lambda> s1. constrained_always_inv t t1 A  s s1) (\<lambda> s1. constrained_always_inv t t1 A  s' s1)"
  unfolding constrained_always_inv_def always_imp_def
  apply(cases "t = 0")
   apply simp_all
  apply(rule allI)
  subgoal for s1
    apply(rule impI)
    apply(rule conjI)
     apply (smt (verit, ccfv_SIG) One_nat_def Suc_eq_plus1 add_le_mono dual_order.trans le_numeral_extra(4) toEnvNum3)
    apply(rule allI)
    subgoal for r1
      apply(cases "r1=s'")
       apply(erule conjE)+
       apply(rotate_tac 6)
       apply(erule disjE)
        apply(subgoal_tac "toEnvNum s1 s' \<ge> t")
         apply simp
        apply (smt (verit) One_nat_def Suc_eq_plus1 add_le_mono dual_order.trans le_numeral_extra(4) toEnvNum3)
      apply simp
      by (metis One_nat_def substate_noteq_imp_substate_of_pred)
    done
  done

lemma constrained_always_one_point[patternintro]: "toEnvP s \<Longrightarrow> t = 0 \<or> t1 s = 0 \<and> (A s s) \<Longrightarrow>
 constrained_always_inv  t t1 A s s"
  apply(unfold constrained_always_inv_def)
  using substate_antisym by auto 

lemma constrained_always_einv2req[patternintro]: "
toEnvP s \<Longrightarrow>
always_imp s (A' s) (A s) \<Longrightarrow>
always_imp s (\<lambda> s1. constrained_always_inv  t t1 A' s s1) (\<lambda> s1. constrained_always  t A s s1)"
  unfolding constrained_always_inv_def constrained_always_def always_imp_def
  by auto


definition P2 where "P2 t A1 A2  s \<equiv>
always  (\<lambda> r2 r1. \<not> A1 r1 \<or> constrained_always t A2  r2 r1) s "

definition P2_inv where "P2_inv t t1 A1 A2' s \<equiv>
always_inv (\<lambda> r2 r1. \<not> A1 r1 \<or> constrained_always_inv  t t1 A2' r2 r1)  s "

lemma P2_rule_gen:
"P2_inv t t1 A1 A2'  s \<Longrightarrow> consecutive s s'
\<Longrightarrow> (True \<and> ( t = 0 \<or> always_imp s (A2' s) (A2' s') \<and> (t \<le> t1 s + 1 \<or> A2' s' s') \<and> t1 s' \<le> t1 s + 1))
 \<and>(\<not> A1 s' \<or> t = 0 \<or> t1 s' = 0 \<and> A2' s' s')
\<Longrightarrow> P2_inv  t t1 A1 A2' s'"
  unfolding P2_inv_def
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
       apply(rule always_imp_refl)
      apply(insert prems2(1,3))
      apply(rule patternintro)
       apply assumption
      apply(erule disjE)
       apply(rule disjI1)
       apply assumption
      apply(rule disjI2)
      apply(erule conjE)
      subgoal premises prems3
        apply(rule conjI)
         apply(insert prems3(1,2))[1]
         apply assumption
        apply(insert prems3(1,3))
        apply assumption
        done
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

end
