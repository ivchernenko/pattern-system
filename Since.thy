theory Since
  imports VCTheoryLemmas
begin

definition dual_since where "dual_since t A1 A2 s s1 \<equiv>
\<forall>  r1. toEnvP r1 \<and> r1 \<le> s1 \<and> toEnvNum r1 s1 \<ge> t \<longrightarrow> A2 s r1 \<or>
(\<exists> r2. toEnvP r2 \<and> r1 < r2 \<and> r2 \<le> s1 \<and> A1 s r2)"

  
definition since where "since t A1 A2 s s1 \<equiv>
\<exists>  r1. toEnvP r1 \<and> r1 \<le> s1 \<and> toEnvNum r1 s1 \<ge> t \<and> A2 s r1 \<and>
(\<forall> r2. toEnvP r2 \<and> r1 < r2 \<and> r2 \<le> s1  \<longrightarrow> A1 s r2)"

lemma einv2req_neg: "   \<not> since s t A1 A2 \<longleftrightarrow> dual_since s t (\<lambda> s2. \<not>A1 s2) (\<lambda> s1. \<not>A2 s1)"
  apply(unfold dual_since_def since_def)
  apply auto
  done

definition dual_since_inv where "dual_since_inv s t b A1 A2 \<equiv> b \<longrightarrow> dual_since s t A1 A2"

lemma dual_since_one_point: "consecutive s0 s \<Longrightarrow>
 dual_since_inv s0 t b A1 A2 \<and> (\<not>b' \<or> (t' > 0 \<or> A2 s) \<and> (A1 s\<or> b \<and> t < t'))  \<Longrightarrow>
 dual_since_inv s t' b' A1 A2"
  apply(unfold dual_since_inv_def dual_since_def)
  apply(erule conjE)
  apply(erule disjE)
   apply simp
  apply(rule impI)
  apply(rule allI)
  subgoal for s1
    apply(erule conjE)
    apply(cases "s1=s")
     apply auto[1]
    apply(rotate_tac 4)
    apply(erule disjE)
    using consecutive.simps substate_refl apply blast
    apply(erule impE)
     apply simp
    apply(rule impI)
    apply(erule allE[of _ s1])
    apply(erule impE)
     apply(subgoal_tac "substate s1 s0")
    using toEnvNum3
    apply auto[1]
     apply (meson consecutive.simps substate_noteq_imp_substate_of_pred)
    using substate_trans
    using consecutive.simps by blast
  done

lemma dual_since_einv2req: "dual_since_inv s t b A1 A2 \<Longrightarrow> b = True \<and> t \<le> t' \<Longrightarrow> dual_since s t' A1 A2"
  apply(unfold dual_since_inv_def dual_since_def)
  apply auto
  done

end


  



end