theory Since
  imports RequirementLemmas
begin

definition dual_since where "dual_since t A1 A2 s s1 \<equiv>
\<forall>  r1. toEnvP r1 \<and> r1 \<le> s1 \<and> toEnvNum r1 s1 \<ge> t \<longrightarrow> A2 s r1 \<or>
(\<exists> r2. toEnvP r2 \<and> r1 < r2 \<and> r2 \<le> s1 \<and> A1 s r2)"

  
definition since where "since t A1 A2 s s1 \<equiv>
\<exists>  r1. toEnvP r1 \<and> r1 \<le> s1 \<and> toEnvNum r1 s1 \<ge> t \<and> A2 s r1 \<and>
(\<forall> r2. toEnvP r2 \<and> r1 < r2 \<and> r2 \<le> s1  \<longrightarrow> A1 s r2)"

definition dual_since_inv where "dual_since_inv (t::nat) t1 A1 A2 s \<equiv>  dual_since (t1 s) A1 A2 s s"

lemma dual_since_one_point[pastinv]: "consecutive s s' \<Longrightarrow>
(t1 s' > 0 \<or> A2' s' s') \<and> (A1' s' s' \<or> dual_since_inv t t1 A1' A2' s \<and> always_imp s (A1' s) (A1' s') \<and>
always_imp s (A2' s) (A2' s') \<and>  t1 s < t1 s') \<Longrightarrow>
dual_since_inv t t1 A1' A2' s' "
  unfolding dual_since_inv_def dual_since_def always_imp_def less_state.simps less_eq_state.simps
  apply(rule allI)
  subgoal for r1
    apply(rule impI)
    apply(cases "r1 = s'")
     apply auto[1]
    apply(erule conjE)
    apply(rotate_tac -1)
    apply(erule disjE)
    using consecutive.simps substate_refl apply blast
    apply(rotate_tac -1)
    apply(erule conjE)
    apply(erule allE[of _ r1])
   apply(subgoal_tac "substate r1 s")
    apply(erule impE)
    apply(simp only: consecutive.simps)
      apply(rule conjI)
       apply simp
      apply(rule conjI)
       apply simp
      apply(subgoal_tac "t1 s < toEnvNum r1 s'")
    using toEnvNum3[of r1 s s'] apply simp
    apply simp
     apply (metis consecutive.simps substate_trans)
    apply (metis consecutive.elims(2) substate_noteq_imp_substate_of_pred)
    done
  done

lemma dual_since_L7[patternintro]: "consecutive s s' \<Longrightarrow>
(t > 0 \<or> A2' s' s') \<and> (A1' s' s' \<or> dual_since_inv t t1 A1' A2' s \<and> always_imp s (A1' s) (A1' s') \<and>
always_imp s (A2' s) (A2' s') \<and>  t1 s < t) \<Longrightarrow>
dual_since t A1' A2' s' s' "
  unfolding dual_since_inv_def dual_since_def always_imp_def less_state.simps less_eq_state.simps
  apply(rule allI)
  subgoal for r1
    apply(rule impI)
    apply(cases "r1 = s'")
    apply auto[1]
    apply(erule conjE)
    apply(rotate_tac -1)
    apply(erule disjE)
    using consecutive.simps substate_refl apply blast
    apply(rotate_tac -1)
    apply(erule conjE)
    apply(erule allE[of _ r1])
   apply(subgoal_tac "substate r1 s")
    apply(erule impE)
    apply(simp only: consecutive.simps)
      apply(rule conjI)
       apply simp
      apply(rule conjI)
       apply simp
      apply(subgoal_tac "t1 s < toEnvNum r1 s'")
    using toEnvNum3[of r1 s s'] apply simp
    apply simp
       apply (metis consecutive.simps substate_trans)
    apply (metis consecutive.elims(2) substate_noteq_imp_substate_of_pred)
    done
  done

lemma dual_since_L4[invsaving]: "
consecutive s s' \<Longrightarrow>
always_imp s (A1' s) (A1' s') \<and> always_imp s (A2' s) (A2' s') \<Longrightarrow>
always_imp s (dual_since t A1' A2' s) (dual_since t A1' A2' s')"
  unfolding always_imp_def dual_since_def  less_state.simps less_eq_state.simps
  by (metis substate_trans)
  
lemma dual_since_L5[inv_req]: "
toEnvP s \<Longrightarrow>
always_imp s (A1' s) (A1 s) \<and> always_imp s (A2' s) (A2 s) \<Longrightarrow>
always_imp s (dual_since t A1' A2' s) (dual_since t A1 A2 s)" 
  unfolding always_imp_def dual_since_def  less_state.simps less_eq_state.simps
  by (metis substate_trans)

end
