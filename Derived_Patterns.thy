theory Derived_Patterns imports Basic_Patterns
 begin
definition always2 where "always2 A11 A12 A2 s \<equiv> (always (\<lambda> r2 r1 . ((weak_previous (\<lambda> r4 r3 . (\<not> (A11 r3))) r2 r1) \<or> ((\<not> (A12 r1)) \<or> (A2 r2 r1)))) s)"

definition always2_part where "always2_part A11 A12 A2 s \<equiv> (always2 A11 A12 (\<lambda> s s1 . (A2 s1)) s)"

definition always2_inv where "always2_inv b_0 A11 A12 A2_1 s \<equiv> ((always_inv (\<lambda> r2 r1 . ((weak_previous (\<lambda> r4 r3 . (\<not> (A11 r3))) r2 r1) \<or> ((\<not> (A12 r1)) \<or> (A2_1 r2 r1)))) s) \<and> (previous_inv b_0 (\<lambda> r4 r3 . (\<not> (A11 r3))) s))"

definition always2_inv_part where "always2_inv_part b_0 A11 A12 A2 s \<equiv> (always2_inv b_0 A11 A12 (\<lambda> s s1 . (A2 s1)) s)"

lemma always2_inv_saving_gen: "
always2_inv b_0 A11 A12 A2_1 s0 \<Longrightarrow>
consecutive s0 s \<Longrightarrow>
(((True \<and> (True \<and> (always_imp s0 (\<lambda> r1 . (A2_1 s0 r1)) (\<lambda> r1 . (A2_1 s r1))))) \<and> (((b_0 s0) \<and> True) \<or> ((\<not> (A12 s)) \<or> (A2_1 s s)))) \<and> ((b_0 s) --> (\<not> (A11 s)))) \<Longrightarrow>
always2_inv b_0 A11 A12 A2_1 s"
unfolding always2_inv_def
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
    apply(rule always_disj_rule)
    apply simp
      apply(erule conjE)
      subgoal premises prems3
      apply(rule conjI)
      apply(insert prems3(1,2))[1]
        apply(rule weak_previous_LS4)
        apply simp
          apply(rule always_imp_refl)
      apply(insert prems3(1,3))
        apply(rule always_disj_rule)
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
      apply(rule weak_previous_one_point[OF prems1(3)])
      apply simp
        apply(erule conjE)
        subgoal premises prems5
        apply(rule conjI)
        apply(insert prems5(1,2))[1]
          apply assumption
        apply(insert prems5(1,3))
          apply(rule always_imp_refl)
        done
    apply(rule disjI2)
      apply(erule disjE)
      apply(rule disjI1)
        apply assumption
      apply(rule disjI2)
        apply assumption
  done
apply(insert prems1(1,3,5))
  apply(erule previous_rule)
  apply simp
  apply(rule impI)
  apply(erule impE)
  apply assumption
  subgoal premises prems6
  apply(insert prems6(1,3))
    apply assumption
  done
done
done

lemma always2einv_imp_req_gen: "
always2_inv b_0 A11 A12 A2_1 s0 \<Longrightarrow>
toEnvP s0 \<Longrightarrow>
(True \<and> (True \<and> (always_imp s0 (\<lambda> r1 . (A2_1 s0 r1)) (\<lambda> r1 . (A2 s0 r1))))) \<Longrightarrow>
always2 A11 A12 A2 s0"unfolding always2_inv_def always2_def
subgoal premises prems1
apply(insert prems1(1,2))
apply(erule conjE)
subgoal premises prems2
apply(insert prems2(1,2) prems1(3))
apply(erule always_einv2req)
apply simp
  apply(rule always_disj_rule)
  apply simp
    apply(erule conjE)
    subgoal premises prems3
    apply(rule conjI)
    apply(insert prems3(1,2))[1]
      apply(rule weak_previous_LS5)
      apply simp
        apply(rule always_imp_refl)
    apply(insert prems3(1,3))
      apply(rule always_disj_rule)
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
done
done
done

lemma always2_inv_saving: "
always2_inv_part b_0 A11 A12 A2 s0 \<Longrightarrow>
consecutive s0 s \<Longrightarrow>
(((b_0 s0) \<or> ((\<not> (A12 s)) \<or> (A2 s))) \<and> ((b_0 s) --> (\<not> (A11 s)))) \<Longrightarrow>
always2_inv_part b_0 A11 A12 A2 s"unfolding always2_inv_part_def always2_part_def
apply(simp add: always2_inv_saving_gen always_imp_refl)
done

lemma always2einv_imp_req: "
always2_inv_part b_0 A11 A12 A2 s \<Longrightarrow>
toEnvP s \<Longrightarrow>
True \<Longrightarrow>
always2_part A11 A12 A2 s"unfolding always2_inv_part_def always2_part_def
apply(simp add: always2einv_imp_req_gen always_imp_refl)
done

lemmas always2_used_patterns = always2_def always_def weak_previous_def 

lemmas always2_inv_used_patterns = always2_inv_def always_inv_def weak_previous_def previous_inv_def 

lemmas always2_inv_part_used_patterns = always2_inv_part_def always2_inv_used_patterns

lemmas always2_part_used_patterns = always2_part_def always2_used_patterns

definition P1_1 where "P1_1 t A1 A2 A3 s \<equiv> (always (\<lambda> r2 r1 . ((\<not> (A1 r1)) \<or> (constrained_until t A2 A3 r2 r1))) s)"

definition P1_1_part where "P1_1_part t A1 A2 A3 s \<equiv> (P1_1 t A1 (\<lambda> s s1 . (A2 s1)) (\<lambda> s s1 . (A3 s1)) s)"

definition P1_1_inv where "P1_1_inv t t1_0 A1 A2_1 A3_1 s \<equiv> (always_inv (\<lambda> r2 r1 . ((\<not> (A1 r1)) \<or> (constrained_until_inv t t1_0 A2_1 A3_1 r2 r1))) s)"

definition P1_1_inv_part where "P1_1_inv_part t t1_0 A1 A2 A3 s \<equiv> (P1_1_inv t t1_0 A1 (\<lambda> s s1 . (A2 s1)) (\<lambda> s s1 . (A3 s1)) s)"

lemma P1_1_inv_saving_gen: "
P1_1_inv t t1_0 A1 A2_1 A3_1 s0 \<Longrightarrow>
consecutive s0 s \<Longrightarrow>
((True \<and> ((always_imp s0 (A2_1 s0) (A2_1 s)) \<and> ((always_imp s0 (A3_1 s0) (A3_1 s)) \<and> (((t1_0 s0) = 0) \<or> (((A3_1 s s) \<and> ((t1_0 s0) <= t)) \<or> ((A2_1 s s) \<and> ((t1_0 s0) < (t1_0 s)))))))) \<and> ((\<not> (A1 s)) \<or> ((A3_1 s s) \<or> ((A2_1 s s) \<and> ((t1_0 s) > 0))))) \<Longrightarrow>
P1_1_inv t t1_0 A1 A2_1 A3_1 s"
unfolding P1_1_inv_def
apply(erule always_rule)
  apply simp
  apply(erule conjE)
  subgoal premises prems1
  apply(rule conjI)
  apply(insert prems1(1,2))[1]
    apply(rule always_disj_rule)
    apply simp
      apply(erule conjE)
      subgoal premises prems2
      apply(rule conjI)
      apply(insert prems2(1,2))[1]
        apply(rule always_imp_refl)
      apply(insert prems2(1,3))
        apply(rule constrained_until_rule)
        apply simp
          apply(erule conjE)
          subgoal premises prems3
          apply(rule conjI)
          apply(insert prems3(1,2))[1]
            apply assumption
          apply(insert prems3(1,3))
            apply(erule conjE)
            subgoal premises prems4
            apply(rule conjI)
            apply(insert prems4(1,2))[1]
              apply assumption
            apply(insert prems4(1,3))
              apply(erule disjE)
              apply(rule disjI1)
                apply assumption
              apply(rule disjI2)
                apply(erule disjE)
                apply(rule disjI1)
                  apply(erule conjE)
                  subgoal premises prems5
                  apply(rule conjI)
                  apply(insert prems5(1,2))[1]
                    apply assumption
                  apply(insert prems5(1,3))
                    apply assumption
                  done
                apply(rule disjI2)
                  apply(erule conjE)
                  subgoal premises prems6
                  apply(rule conjI)
                  apply(insert prems6(1,2))[1]
                    apply assumption
                  apply(insert prems6(1,3))
                    apply assumption
                  done
            done
          done
      done
  apply(insert prems1(1,3))
    apply(erule disjE)
    apply(rule disjI1)
      apply assumption
    apply(rule disjI2)
      apply(rule constrained_until_one_point)
      apply simp
        apply(erule disjE)
        apply(rule disjI1)
          apply assumption
        apply(rule disjI2)
          apply(erule conjE)
          subgoal premises prems7
          apply(rule conjI)
          apply(insert prems7(1,2))[1]
            apply assumption
          apply(insert prems7(1,3))
            apply assumption
          done
  done
done

lemma P1_1einv_imp_req_gen: "
P1_1_inv t t1_0 A1 A2_1 A3_1 s0 \<Longrightarrow>
toEnvP s0 \<Longrightarrow>
(True \<and> ((always_imp s0 (A2_1 s0) (A2 s0)) \<and> ((always_imp s0 (A3_1 s0) (A3 s0)) \<and> ((t1_0 s0) <= t)))) \<Longrightarrow>
P1_1 t A1 A2 A3 s0"unfolding P1_1_inv_def P1_1_def
apply(erule always_einv2req)
apply simp
  apply(rule always_disj_rule)
  apply simp
    apply(erule conjE)
    subgoal premises prems3
    apply(rule conjI)
    apply(insert prems3(1,2))[1]
      apply(rule always_imp_refl)
    apply(insert prems3(1,3))
      apply(rule constrained_until_einv2req)
      apply simp
        apply(erule conjE)
        subgoal premises prems4
        apply(rule conjI)
        apply(insert prems4(1,2))[1]
          apply assumption
        apply(insert prems4(1,3))
          apply(erule conjE)
          subgoal premises prems5
          apply(rule conjI)
          apply(insert prems5(1,2))[1]
            apply assumption
          apply(insert prems5(1,3))
            apply assumption
          done
        done
    done
done

lemma P1_1_inv_saving: "
P1_1_inv_part t t1_0 A1 A2 A3 s0 \<Longrightarrow>
consecutive s0 s \<Longrightarrow>
((((t1_0 s0) = 0) \<or> (((A3 s) \<and> ((t1_0 s0) <= t)) \<or> ((A2 s) \<and> ((t1_0 s0) < (t1_0 s))))) \<and> ((\<not> (A1 s)) \<or> ((A3 s) \<or> ((A2 s) \<and> ((t1_0 s) > 0))))) \<Longrightarrow>
P1_1_inv_part t t1_0 A1 A2 A3 s"unfolding P1_1_inv_part_def P1_1_part_def
apply(simp add: P1_1_inv_saving_gen always_imp_refl)
done

lemma P1_1einv_imp_req: "
P1_1_inv_part t t1_0 A1 A2 A3 s \<Longrightarrow>
toEnvP s \<Longrightarrow>
((t1_0 s) <= t) \<Longrightarrow>
P1_1_part t A1 A2 A3 s"unfolding P1_1_inv_part_def P1_1_part_def
apply(simp add: P1_1einv_imp_req_gen always_imp_refl)
done

lemmas P1_1_used_patterns = P1_1_def always_def constrained_until_def 

lemmas P1_1_inv_used_patterns = P1_1_inv_def always_inv_def constrained_until_inv_def 

lemmas P1_1_inv_part_used_patterns = P1_1_inv_part_def P1_1_inv_used_patterns

lemmas P1_1_part_used_patterns = P1_1_part_def P1_1_used_patterns

definition P1_2 where "P1_2 t A11 A12 A2 A3 s \<equiv> (always (\<lambda> r2 r1 . ((weak_previous (\<lambda> r4 r3 . (\<not> (A11 r3))) r2 r1) \<or> ((\<not> (A12 r1)) \<or> (constrained_until t A2 A3 r2 r1)))) s)"

definition P1_2_part where "P1_2_part t A11 A12 A2 A3 s \<equiv> (P1_2 t A11 A12 (\<lambda> s s1 . (A2 s1)) (\<lambda> s s1 . (A3 s1)) s)"

definition P1_2_inv where "P1_2_inv t b_0 t1_0 A11 A12 A2_1 A3_1 s \<equiv> ((always_inv (\<lambda> r2 r1 . ((weak_previous (\<lambda> r4 r3 . (\<not> (A11 r3))) r2 r1) \<or> ((\<not> (A12 r1)) \<or> (constrained_until_inv t t1_0 A2_1 A3_1 r2 r1)))) s) \<and> (previous_inv b_0 (\<lambda> r4 r3 . (\<not> (A11 r3))) s))"

definition P1_2_inv_part where "P1_2_inv_part t b_0 t1_0 A11 A12 A2 A3 s \<equiv> (P1_2_inv t b_0 t1_0 A11 A12 (\<lambda> s s1 . (A2 s1)) (\<lambda> s s1 . (A3 s1)) s)"

lemma P1_2_inv_saving_gen: "
P1_2_inv t b_0 t1_0 A11 A12 A2_1 A3_1 s0 \<Longrightarrow>
consecutive s0 s \<Longrightarrow>
(((True \<and> (True \<and> ((always_imp s0 (A2_1 s0) (A2_1 s)) \<and> ((always_imp s0 (A3_1 s0) (A3_1 s)) \<and> (((t1_0 s0) = 0) \<or> (((A3_1 s s) \<and> ((t1_0 s0) <= t)) \<or> ((A2_1 s s) \<and> ((t1_0 s0) < (t1_0 s))))))))) \<and> (((b_0 s0) \<and> True) \<or> ((\<not> (A12 s)) \<or> ((A3_1 s s) \<or> ((A2_1 s s) \<and> ((t1_0 s) > 0)))))) \<and> ((b_0 s) --> (\<not> (A11 s)))) \<Longrightarrow>
P1_2_inv t b_0 t1_0 A11 A12 A2_1 A3_1 s"
unfolding P1_2_inv_def
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
    apply(rule always_disj_rule)
    apply simp
      apply(erule conjE)
      subgoal premises prems3
      apply(rule conjI)
      apply(insert prems3(1,2))[1]
        apply(rule weak_previous_LS4)
        apply simp
          apply(rule always_imp_refl)
      apply(insert prems3(1,3))
        apply(rule always_disj_rule)
        apply simp
          apply(erule conjE)
          subgoal premises prems4
          apply(rule conjI)
          apply(insert prems4(1,2))[1]
            apply(rule always_imp_refl)
          apply(insert prems4(1,3))
            apply(rule constrained_until_rule)
            apply simp
              apply(erule conjE)
              subgoal premises prems5
              apply(rule conjI)
              apply(insert prems5(1,2))[1]
                apply assumption
              apply(insert prems5(1,3))
                apply(erule conjE)
                subgoal premises prems6
                apply(rule conjI)
                apply(insert prems6(1,2))[1]
                  apply assumption
                apply(insert prems6(1,3))
                  apply(erule disjE)
                  apply(rule disjI1)
                    apply assumption
                  apply(rule disjI2)
                    apply(erule disjE)
                    apply(rule disjI1)
                      apply(erule conjE)
                      subgoal premises prems7
                      apply(rule conjI)
                      apply(insert prems7(1,2))[1]
                        apply assumption
                      apply(insert prems7(1,3))
                        apply assumption
                      done
                    apply(rule disjI2)
                      apply(erule conjE)
                      subgoal premises prems8
                      apply(rule conjI)
                      apply(insert prems8(1,2))[1]
                        apply assumption
                      apply(insert prems8(1,3))
                        apply assumption
                      done
                done
              done
          done
      done
  apply(insert prems2(1,3))
    apply(erule disjE)
    apply(rule disjI1)
      apply(rule weak_previous_one_point[OF prems1(3)])
      apply simp
        apply(erule conjE)
        subgoal premises prems9
        apply(rule conjI)
        apply(insert prems9(1,2))[1]
          apply assumption
        apply(insert prems9(1,3))
          apply(rule always_imp_refl)
        done
    apply(rule disjI2)
      apply(erule disjE)
      apply(rule disjI1)
        apply assumption
      apply(rule disjI2)
        apply(rule constrained_until_one_point)
        apply simp
          apply(erule disjE)
          apply(rule disjI1)
            apply assumption
          apply(rule disjI2)
            apply(erule conjE)
            subgoal premises prems10
            apply(rule conjI)
            apply(insert prems10(1,2))[1]
              apply assumption
            apply(insert prems10(1,3))
              apply assumption
            done
  done
apply(insert prems1(1,3,5))
  apply(erule previous_rule)
  apply simp
  apply(rule impI)
  apply(erule impE)
  apply assumption
  subgoal premises prems11
  apply(insert prems11(1,3))
    apply assumption
  done
done
done

lemma P1_2einv_imp_req_gen: "
P1_2_inv t b_0 t1_0 A11 A12 A2_1 A3_1 s0 \<Longrightarrow>
toEnvP s0 \<Longrightarrow>
(True \<and> (True \<and> ((always_imp s0 (A2_1 s0) (A2 s0)) \<and> ((always_imp s0 (A3_1 s0) (A3 s0)) \<and> ((t1_0 s0) <= t))))) \<Longrightarrow>
P1_2 t A11 A12 A2 A3 s0"unfolding P1_2_inv_def P1_2_def
subgoal premises prems1
apply(insert prems1(1,2))
apply(erule conjE)
subgoal premises prems2
apply(insert prems2(1,2) prems1(3))
apply(erule always_einv2req)
apply simp
  apply(rule always_disj_rule)
  apply simp
    apply(erule conjE)
    subgoal premises prems3
    apply(rule conjI)
    apply(insert prems3(1,2))[1]
      apply(rule weak_previous_LS5)
      apply simp
        apply(rule always_imp_refl)
    apply(insert prems3(1,3))
      apply(rule always_disj_rule)
      apply simp
        apply(erule conjE)
        subgoal premises prems4
        apply(rule conjI)
        apply(insert prems4(1,2))[1]
          apply(rule always_imp_refl)
        apply(insert prems4(1,3))
          apply(rule constrained_until_einv2req)
          apply simp
            apply(erule conjE)
            subgoal premises prems5
            apply(rule conjI)
            apply(insert prems5(1,2))[1]
              apply assumption
            apply(insert prems5(1,3))
              apply(erule conjE)
              subgoal premises prems6
              apply(rule conjI)
              apply(insert prems6(1,2))[1]
                apply assumption
              apply(insert prems6(1,3))
                apply assumption
              done
            done
        done
    done
done
done
done

lemma P1_2_inv_saving: "
P1_2_inv_part t b_0 t1_0 A11 A12 A2 A3 s0 \<Longrightarrow>
consecutive s0 s \<Longrightarrow>
(((((t1_0 s0) = 0) \<or> (((A3 s) \<and> ((t1_0 s0) <= t)) \<or> ((A2 s) \<and> ((t1_0 s0) < (t1_0 s))))) \<and> ((b_0 s0) \<or> ((\<not> (A12 s)) \<or> ((A3 s) \<or> ((A2 s) \<and> ((t1_0 s) > 0)))))) \<and> ((b_0 s) --> (\<not> (A11 s)))) \<Longrightarrow>
P1_2_inv_part t b_0 t1_0 A11 A12 A2 A3 s"unfolding P1_2_inv_part_def P1_2_part_def
apply(simp add: P1_2_inv_saving_gen always_imp_refl)
done

lemma P1_2einv_imp_req: "
P1_2_inv_part t b_0 t1_0 A11 A12 A2 A3 s \<Longrightarrow>
toEnvP s \<Longrightarrow>
((t1_0 s) <= t) \<Longrightarrow>
P1_2_part t A11 A12 A2 A3 s"unfolding P1_2_inv_part_def P1_2_part_def
apply(simp add: P1_2einv_imp_req_gen always_imp_refl)
done

lemmas P1_2_used_patterns = P1_2_def always_def weak_previous_def constrained_until_def 

lemmas P1_2_inv_used_patterns = P1_2_inv_def always_inv_def weak_previous_def constrained_until_inv_def previous_inv_def 

lemmas P1_2_inv_part_used_patterns = P1_2_inv_part_def P1_2_inv_used_patterns

lemmas P1_2_part_used_patterns = P1_2_part_def P1_2_used_patterns

definition P2_1 where "P2_1 t A1 A2 s \<equiv> (always (\<lambda> r2 r1 . ((\<not> (A1 r1)) \<or> (constrained_always t A2 r2 r1))) s)"

definition P2_1_part where "P2_1_part t A1 A2 s \<equiv> (P2_1 t A1 (\<lambda> s s1 . (A2 s1)) s)"

definition P2_1_inv where "P2_1_inv t t1_0 A1 A2_1 s \<equiv> (always_inv (\<lambda> r2 r1 . ((\<not> (A1 r1)) \<or> (constrained_always_inv t t1_0 A2_1 r2 r1))) s)"

definition P2_1_inv_part where "P2_1_inv_part t t1_0 A1 A2 s \<equiv> (P2_1_inv t t1_0 A1 (\<lambda> s s1 . (A2 s1)) s)"

lemma P2_1_inv_saving_gen: "
P2_1_inv t t1_0 A1 A2_1 s0 \<Longrightarrow>
consecutive s0 s \<Longrightarrow>
((True \<and> ((t = 0) \<or> ((always_imp s0 (A2_1 s0) (A2_1 s)) \<and> (((((t1_0 s0) + 1) >= t) \<or> (A2_1 s s)) \<and> ((t1_0 s) <= ((t1_0 s0) + 1)))))) \<and> ((\<not> (A1 s)) \<or> ((t = 0) \<or> (((t1_0 s) = 0) \<and> (A2_1 s s))))) \<Longrightarrow>
P2_1_inv t t1_0 A1 A2_1 s"
unfolding P2_1_inv_def
apply(erule always_rule)
  apply simp
  apply(erule conjE)
  subgoal premises prems1
  apply(rule conjI)
  apply(insert prems1(1,2))[1]
    apply(rule always_disj_rule)
    apply simp
      apply(erule conjE)
      subgoal premises prems2
      apply(rule conjI)
      apply(insert prems2(1,2))[1]
        apply(rule always_imp_refl)
      apply(insert prems2(1,3))
        apply(rule constrained_always_rule)
        apply simp
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
              apply(erule conjE)
              subgoal premises prems4
              apply(rule conjI)
              apply(insert prems4(1,2))[1]
                apply(erule disjE)
                apply(rule disjI1)
                  apply assumption
                apply(rule disjI2)
                  apply assumption
              apply(insert prems4(1,3))
                apply assumption
              done
            done
      done
  apply(insert prems1(1,3))
    apply(erule disjE)
    apply(rule disjI1)
      apply assumption
    apply(rule disjI2)
      apply(rule constrained_always_one_point)
      apply simp
        apply(erule disjE)
        apply(rule disjI1)
          apply assumption
        apply(rule disjI2)
          apply(erule conjE)
          subgoal premises prems5
          apply(rule conjI)
          apply(insert prems5(1,2))[1]
            apply assumption
          apply(insert prems5(1,3))
            apply assumption
          done
  done
done

lemma P2_1einv_imp_req_gen: "
P2_1_inv t t1_0 A1 A2_1 s0 \<Longrightarrow>
toEnvP s0 \<Longrightarrow>
(True \<and> (always_imp s0 (A2_1 s0) (A2 s0))) \<Longrightarrow>
P2_1 t A1 A2 s0"unfolding P2_1_inv_def P2_1_def
apply(erule always_einv2req)
apply simp
  apply(rule always_disj_rule)
  apply simp
    apply(erule conjE)
    subgoal premises prems3
    apply(rule conjI)
    apply(insert prems3(1,2))[1]
      apply(rule always_imp_refl)
    apply(insert prems3(1,3))
      apply(rule constrained_always_einv2req)
      apply simp
        apply assumption
    done
done

lemma P2_1_inv_saving: "
P2_1_inv_part t t1_0 A1 A2 s0 \<Longrightarrow>
consecutive s0 s \<Longrightarrow>
(((t = 0) \<or> (((((t1_0 s0) + 1) >= t) \<or> (A2 s)) \<and> ((t1_0 s) <= ((t1_0 s0) + 1)))) \<and> ((\<not> (A1 s)) \<or> ((t = 0) \<or> (((t1_0 s) = 0) \<and> (A2 s))))) \<Longrightarrow>
P2_1_inv_part t t1_0 A1 A2 s"unfolding P2_1_inv_part_def P2_1_part_def
apply(simp add: P2_1_inv_saving_gen always_imp_refl)
done

lemma P2_1einv_imp_req: "
P2_1_inv_part t t1_0 A1 A2 s \<Longrightarrow>
toEnvP s \<Longrightarrow>
True \<Longrightarrow>
P2_1_part t A1 A2 s"unfolding P2_1_inv_part_def P2_1_part_def
apply(simp add: P2_1einv_imp_req_gen always_imp_refl)
done

lemmas P2_1_used_patterns = P2_1_def always_def constrained_always_def 

lemmas P2_1_inv_used_patterns = P2_1_inv_def always_inv_def constrained_always_inv_def 

lemmas P2_1_inv_part_used_patterns = P2_1_inv_part_def P2_1_inv_used_patterns

lemmas P2_1_part_used_patterns = P2_1_part_def P2_1_used_patterns

definition P2_2 where "P2_2 t A11 A12 A2 s \<equiv> (always (\<lambda> r2 r1 . ((weak_previous (\<lambda> r4 r3 . (\<not> (A11 r3))) r2 r1) \<or> ((\<not> (A12 r1)) \<or> (constrained_always t A2 r2 r1)))) s)"

definition P2_2_part where "P2_2_part t A11 A12 A2 s \<equiv> (P2_2 t A11 A12 (\<lambda> s s1 . (A2 s1)) s)"

definition P2_2_inv where "P2_2_inv t b_0 t1_0 A11 A12 A2_1 s \<equiv> ((always_inv (\<lambda> r2 r1 . ((weak_previous (\<lambda> r4 r3 . (\<not> (A11 r3))) r2 r1) \<or> ((\<not> (A12 r1)) \<or> (constrained_always_inv t t1_0 A2_1 r2 r1)))) s) \<and> (previous_inv b_0 (\<lambda> r4 r3 . (\<not> (A11 r3))) s))"

definition P2_2_inv_part where "P2_2_inv_part t b_0 t1_0 A11 A12 A2 s \<equiv> (P2_2_inv t b_0 t1_0 A11 A12 (\<lambda> s s1 . (A2 s1)) s)"

lemma P2_2_inv_saving_gen: "
P2_2_inv t b_0 t1_0 A11 A12 A2_1 s0 \<Longrightarrow>
consecutive s0 s \<Longrightarrow>
(((True \<and> (True \<and> ((t = 0) \<or> ((always_imp s0 (A2_1 s0) (A2_1 s)) \<and> (((((t1_0 s0) + 1) >= t) \<or> (A2_1 s s)) \<and> ((t1_0 s) <= ((t1_0 s0) + 1))))))) \<and> (((b_0 s0) \<and> True) \<or> ((\<not> (A12 s)) \<or> ((t = 0) \<or> (((t1_0 s) = 0) \<and> (A2_1 s s)))))) \<and> ((b_0 s) --> (\<not> (A11 s)))) \<Longrightarrow>
P2_2_inv t b_0 t1_0 A11 A12 A2_1 s"
unfolding P2_2_inv_def
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
    apply(rule always_disj_rule)
    apply simp
      apply(erule conjE)
      subgoal premises prems3
      apply(rule conjI)
      apply(insert prems3(1,2))[1]
        apply(rule weak_previous_LS4)
        apply simp
          apply(rule always_imp_refl)
      apply(insert prems3(1,3))
        apply(rule always_disj_rule)
        apply simp
          apply(erule conjE)
          subgoal premises prems4
          apply(rule conjI)
          apply(insert prems4(1,2))[1]
            apply(rule always_imp_refl)
          apply(insert prems4(1,3))
            apply(rule constrained_always_rule)
            apply simp
              apply(erule disjE)
              apply(rule disjI1)
                apply assumption
              apply(rule disjI2)
                apply(erule conjE)
                subgoal premises prems5
                apply(rule conjI)
                apply(insert prems5(1,2))[1]
                  apply assumption
                apply(insert prems5(1,3))
                  apply(erule conjE)
                  subgoal premises prems6
                  apply(rule conjI)
                  apply(insert prems6(1,2))[1]
                    apply(erule disjE)
                    apply(rule disjI1)
                      apply assumption
                    apply(rule disjI2)
                      apply assumption
                  apply(insert prems6(1,3))
                    apply assumption
                  done
                done
          done
      done
  apply(insert prems2(1,3))
    apply(erule disjE)
    apply(rule disjI1)
      apply(rule weak_previous_one_point[OF prems1(3)])
      apply simp
        apply(erule conjE)
        subgoal premises prems7
        apply(rule conjI)
        apply(insert prems7(1,2))[1]
          apply assumption
        apply(insert prems7(1,3))
          apply(rule always_imp_refl)
        done
    apply(rule disjI2)
      apply(erule disjE)
      apply(rule disjI1)
        apply assumption
      apply(rule disjI2)
        apply(rule constrained_always_one_point)
        apply simp
          apply(erule disjE)
          apply(rule disjI1)
            apply assumption
          apply(rule disjI2)
            apply(erule conjE)
            subgoal premises prems8
            apply(rule conjI)
            apply(insert prems8(1,2))[1]
              apply assumption
            apply(insert prems8(1,3))
              apply assumption
            done
  done
apply(insert prems1(1,3,5))
  apply(erule previous_rule)
  apply simp
  apply(rule impI)
  apply(erule impE)
  apply assumption
  subgoal premises prems9
  apply(insert prems9(1,3))
    apply assumption
  done
done
done

lemma P2_2einv_imp_req_gen: "
P2_2_inv t b_0 t1_0 A11 A12 A2_1 s0 \<Longrightarrow>
toEnvP s0 \<Longrightarrow>
(True \<and> (True \<and> (always_imp s0 (A2_1 s0) (A2 s0)))) \<Longrightarrow>
P2_2 t A11 A12 A2 s0"unfolding P2_2_inv_def P2_2_def
subgoal premises prems1
apply(insert prems1(1,2))
apply(erule conjE)
subgoal premises prems2
apply(insert prems2(1,2) prems1(3))
apply(erule always_einv2req)
apply simp
  apply(rule always_disj_rule)
  apply simp
    apply(erule conjE)
    subgoal premises prems3
    apply(rule conjI)
    apply(insert prems3(1,2))[1]
      apply(rule weak_previous_LS5)
      apply simp
        apply(rule always_imp_refl)
    apply(insert prems3(1,3))
      apply(rule always_disj_rule)
      apply simp
        apply(erule conjE)
        subgoal premises prems4
        apply(rule conjI)
        apply(insert prems4(1,2))[1]
          apply(rule always_imp_refl)
        apply(insert prems4(1,3))
          apply(rule constrained_always_einv2req)
          apply simp
            apply assumption
        done
    done
done
done
done

lemma P2_2_inv_saving: "
P2_2_inv_part t b_0 t1_0 A11 A12 A2 s0 \<Longrightarrow>
consecutive s0 s \<Longrightarrow>
((((t = 0) \<or> (((((t1_0 s0) + 1) >= t) \<or> (A2 s)) \<and> ((t1_0 s) <= ((t1_0 s0) + 1)))) \<and> ((b_0 s0) \<or> ((\<not> (A12 s)) \<or> ((t = 0) \<or> (((t1_0 s) = 0) \<and> (A2 s)))))) \<and> ((b_0 s) --> (\<not> (A11 s)))) \<Longrightarrow>
P2_2_inv_part t b_0 t1_0 A11 A12 A2 s"unfolding P2_2_inv_part_def P2_2_part_def
apply(simp add: P2_2_inv_saving_gen always_imp_refl)
done

lemma P2_2einv_imp_req: "
P2_2_inv_part t b_0 t1_0 A11 A12 A2 s \<Longrightarrow>
toEnvP s \<Longrightarrow>
True \<Longrightarrow>
P2_2_part t A11 A12 A2 s"unfolding P2_2_inv_part_def P2_2_part_def
apply(simp add: P2_2einv_imp_req_gen always_imp_refl)
done

lemmas P2_2_used_patterns = P2_2_def always_def weak_previous_def constrained_always_def 

lemmas P2_2_inv_used_patterns = P2_2_inv_def always_inv_def weak_previous_def constrained_always_inv_def previous_inv_def 

lemmas P2_2_inv_part_used_patterns = P2_2_inv_part_def P2_2_inv_used_patterns

lemmas P2_2_part_used_patterns = P2_2_part_def P2_2_used_patterns

definition P3_1 where "P3_1 A1 A2 A3 s \<equiv> (always (\<lambda> r2 r1 . ((\<not> (A1 r1)) \<or> (weak_until A2 A3 r2 r1))) s)"

definition P3_1_part where "P3_1_part A1 A2 A3 s \<equiv> (P3_1 A1 (\<lambda> s s1 . (A2 s1)) (\<lambda> s s1 . (A3 s1)) s)"

definition P3_1_inv where "P3_1_inv w_0 A1 A2_1 A3_1 s \<equiv> (always_inv (\<lambda> r2 r1 . ((\<not> (A1 r1)) \<or> (weak_until_inv w_0 A2_1 A3_1 r2 r1))) s)"

definition P3_1_inv_part where "P3_1_inv_part w_0 A1 A2 A3 s \<equiv> (P3_1_inv w_0 A1 (\<lambda> s s1 . (A2 s1)) (\<lambda> s s1 . (A3 s1)) s)"

lemma P3_1_inv_saving_gen: "
P3_1_inv w_0 A1 A2_1 A3_1 s0 \<Longrightarrow>
consecutive s0 s \<Longrightarrow>
((True \<and> ((always_imp s0 (A2_1 s0) (A2_1 s)) \<and> ((always_imp s0 (A3_1 s0) (A3_1 s)) \<and> ((\<not> (w_0 s0)) \<or> ((A3_1 s s) \<or> ((w_0 s) \<and> (A2_1 s s))))))) \<and> ((\<not> (A1 s)) \<or> ((A3_1 s s) \<or> ((w_0 s) \<and> (A2_1 s s))))) \<Longrightarrow>
P3_1_inv w_0 A1 A2_1 A3_1 s"
unfolding P3_1_inv_def
apply(erule always_rule)
  apply simp
  apply(erule conjE)
  subgoal premises prems1
  apply(rule conjI)
  apply(insert prems1(1,2))[1]
    apply(rule always_disj_rule)
    apply simp
      apply(erule conjE)
      subgoal premises prems2
      apply(rule conjI)
      apply(insert prems2(1,2))[1]
        apply(rule always_imp_refl)
      apply(insert prems2(1,3))
        apply(rule weak_until_rule)
        apply simp
          apply(erule conjE)
          subgoal premises prems3
          apply(rule conjI)
          apply(insert prems3(1,2))[1]
            apply assumption
          apply(insert prems3(1,3))
            apply(erule conjE)
            subgoal premises prems4
            apply(rule conjI)
            apply(insert prems4(1,2))[1]
              apply assumption
            apply(insert prems4(1,3))
              apply(erule disjE)
              apply(rule disjI1)
                apply assumption
              apply(rule disjI2)
                apply(erule disjE)
                apply(rule disjI1)
                  apply assumption
                apply(rule disjI2)
                  apply(erule conjE)
                  subgoal premises prems5
                  apply(rule conjI)
                  apply(insert prems5(1,2))[1]
                    apply assumption
                  apply(insert prems5(1,3))
                    apply assumption
                  done
            done
          done
      done
  apply(insert prems1(1,3))
    apply(erule disjE)
    apply(rule disjI1)
      apply assumption
    apply(rule disjI2)
      apply(rule weak_until_one_point)
      apply simp
        apply(erule disjE)
        apply(rule disjI1)
          apply assumption
        apply(rule disjI2)
          apply(erule conjE)
          subgoal premises prems6
          apply(rule conjI)
          apply(insert prems6(1,2))[1]
            apply assumption
          apply(insert prems6(1,3))
            apply assumption
          done
  done
done

lemma P3_1einv_imp_req_gen: "
P3_1_inv w_0 A1 A2_1 A3_1 s0 \<Longrightarrow>
toEnvP s0 \<Longrightarrow>
(True \<and> ((always_imp s0 (A2_1 s0) (A2 s0)) \<and> (always_imp s0 (A3_1 s0) (A3 s0)))) \<Longrightarrow>
P3_1 A1 A2 A3 s0"unfolding P3_1_inv_def P3_1_def
apply(erule always_einv2req)
apply simp
  apply(rule always_disj_rule)
  apply simp
    apply(erule conjE)
    subgoal premises prems3
    apply(rule conjI)
    apply(insert prems3(1,2))[1]
      apply(rule always_imp_refl)
    apply(insert prems3(1,3))
      apply(rule weak_until_einv2req)
      apply simp
        apply(erule conjE)
        subgoal premises prems4
        apply(rule conjI)
        apply(insert prems4(1,2))[1]
          apply assumption
        apply(insert prems4(1,3))
          apply assumption
        done
    done
done

lemma P3_1_inv_saving: "
P3_1_inv_part w_0 A1 A2 A3 s0 \<Longrightarrow>
consecutive s0 s \<Longrightarrow>
(((\<not> (w_0 s0)) \<or> ((A3 s) \<or> ((w_0 s) \<and> (A2 s)))) \<and> ((\<not> (A1 s)) \<or> ((A3 s) \<or> ((w_0 s) \<and> (A2 s))))) \<Longrightarrow>
P3_1_inv_part w_0 A1 A2 A3 s"unfolding P3_1_inv_part_def P3_1_part_def
apply(simp add: P3_1_inv_saving_gen always_imp_refl)
done

lemma P3_1einv_imp_req: "
P3_1_inv_part w_0 A1 A2 A3 s \<Longrightarrow>
toEnvP s \<Longrightarrow>
True \<Longrightarrow>
P3_1_part A1 A2 A3 s"unfolding P3_1_inv_part_def P3_1_part_def
apply(simp add: P3_1einv_imp_req_gen always_imp_refl)
done

lemmas P3_1_used_patterns = P3_1_def always_def weak_until_def 

lemmas P3_1_inv_used_patterns = P3_1_inv_def always_inv_def weak_until_inv_def 

lemmas P3_1_inv_part_used_patterns = P3_1_inv_part_def P3_1_inv_used_patterns

lemmas P3_1_part_used_patterns = P3_1_part_def P3_1_used_patterns

definition P3_2 where "P3_2 A11 A12 A2 A3 s \<equiv> (always (\<lambda> r2 r1 . ((weak_previous (\<lambda> r4 r3 . (\<not> (A11 r3))) r2 r1) \<or> ((\<not> (A12 r1)) \<or> (weak_until A2 A3 r2 r1)))) s)"

definition P3_2_part where "P3_2_part A11 A12 A2 A3 s \<equiv> (P3_2 A11 A12 (\<lambda> s s1 . (A2 s1)) (\<lambda> s s1 . (A3 s1)) s)"

definition P3_2_inv where "P3_2_inv b_0 w_0 A11 A12 A2_1 A3_1 s \<equiv> ((always_inv (\<lambda> r2 r1 . ((weak_previous (\<lambda> r4 r3 . (\<not> (A11 r3))) r2 r1) \<or> ((\<not> (A12 r1)) \<or> (weak_until_inv w_0 A2_1 A3_1 r2 r1)))) s) \<and> (previous_inv b_0 (\<lambda> r4 r3 . (\<not> (A11 r3))) s))"

definition P3_2_inv_part where "P3_2_inv_part b_0 w_0 A11 A12 A2 A3 s \<equiv> (P3_2_inv b_0 w_0 A11 A12 (\<lambda> s s1 . (A2 s1)) (\<lambda> s s1 . (A3 s1)) s)"

lemma P3_2_inv_saving_gen: "
P3_2_inv b_0 w_0 A11 A12 A2_1 A3_1 s0 \<Longrightarrow>
consecutive s0 s \<Longrightarrow>
(((True \<and> (True \<and> ((always_imp s0 (A2_1 s0) (A2_1 s)) \<and> ((always_imp s0 (A3_1 s0) (A3_1 s)) \<and> ((\<not> (w_0 s0)) \<or> ((A3_1 s s) \<or> ((w_0 s) \<and> (A2_1 s s)))))))) \<and> (((b_0 s0) \<and> True) \<or> ((\<not> (A12 s)) \<or> ((A3_1 s s) \<or> ((w_0 s) \<and> (A2_1 s s)))))) \<and> ((b_0 s) --> (\<not> (A11 s)))) \<Longrightarrow>
P3_2_inv b_0 w_0 A11 A12 A2_1 A3_1 s"
unfolding P3_2_inv_def
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
    apply(rule always_disj_rule)
    apply simp
      apply(erule conjE)
      subgoal premises prems3
      apply(rule conjI)
      apply(insert prems3(1,2))[1]
        apply(rule weak_previous_LS4)
        apply simp
          apply(rule always_imp_refl)
      apply(insert prems3(1,3))
        apply(rule always_disj_rule)
        apply simp
          apply(erule conjE)
          subgoal premises prems4
          apply(rule conjI)
          apply(insert prems4(1,2))[1]
            apply(rule always_imp_refl)
          apply(insert prems4(1,3))
            apply(rule weak_until_rule)
            apply simp
              apply(erule conjE)
              subgoal premises prems5
              apply(rule conjI)
              apply(insert prems5(1,2))[1]
                apply assumption
              apply(insert prems5(1,3))
                apply(erule conjE)
                subgoal premises prems6
                apply(rule conjI)
                apply(insert prems6(1,2))[1]
                  apply assumption
                apply(insert prems6(1,3))
                  apply(erule disjE)
                  apply(rule disjI1)
                    apply assumption
                  apply(rule disjI2)
                    apply(erule disjE)
                    apply(rule disjI1)
                      apply assumption
                    apply(rule disjI2)
                      apply(erule conjE)
                      subgoal premises prems7
                      apply(rule conjI)
                      apply(insert prems7(1,2))[1]
                        apply assumption
                      apply(insert prems7(1,3))
                        apply assumption
                      done
                done
              done
          done
      done
  apply(insert prems2(1,3))
    apply(erule disjE)
    apply(rule disjI1)
      apply(rule weak_previous_one_point[OF prems1(3)])
      apply simp
        apply(erule conjE)
        subgoal premises prems8
        apply(rule conjI)
        apply(insert prems8(1,2))[1]
          apply assumption
        apply(insert prems8(1,3))
          apply(rule always_imp_refl)
        done
    apply(rule disjI2)
      apply(erule disjE)
      apply(rule disjI1)
        apply assumption
      apply(rule disjI2)
        apply(rule weak_until_one_point)
        apply simp
          apply(erule disjE)
          apply(rule disjI1)
            apply assumption
          apply(rule disjI2)
            apply(erule conjE)
            subgoal premises prems9
            apply(rule conjI)
            apply(insert prems9(1,2))[1]
              apply assumption
            apply(insert prems9(1,3))
              apply assumption
            done
  done
apply(insert prems1(1,3,5))
  apply(erule previous_rule)
  apply simp
  apply(rule impI)
  apply(erule impE)
  apply assumption
  subgoal premises prems10
  apply(insert prems10(1,3))
    apply assumption
  done
done
done

lemma P3_2einv_imp_req_gen: "
P3_2_inv b_0 w_0 A11 A12 A2_1 A3_1 s0 \<Longrightarrow>
toEnvP s0 \<Longrightarrow>
(True \<and> (True \<and> ((always_imp s0 (A2_1 s0) (A2 s0)) \<and> (always_imp s0 (A3_1 s0) (A3 s0))))) \<Longrightarrow>
P3_2 A11 A12 A2 A3 s0"unfolding P3_2_inv_def P3_2_def
subgoal premises prems1
apply(insert prems1(1,2))
apply(erule conjE)
subgoal premises prems2
apply(insert prems2(1,2) prems1(3))
apply(erule always_einv2req)
apply simp
  apply(rule always_disj_rule)
  apply simp
    apply(erule conjE)
    subgoal premises prems3
    apply(rule conjI)
    apply(insert prems3(1,2))[1]
      apply(rule weak_previous_LS5)
      apply simp
        apply(rule always_imp_refl)
    apply(insert prems3(1,3))
      apply(rule always_disj_rule)
      apply simp
        apply(erule conjE)
        subgoal premises prems4
        apply(rule conjI)
        apply(insert prems4(1,2))[1]
          apply(rule always_imp_refl)
        apply(insert prems4(1,3))
          apply(rule weak_until_einv2req)
          apply simp
            apply(erule conjE)
            subgoal premises prems5
            apply(rule conjI)
            apply(insert prems5(1,2))[1]
              apply assumption
            apply(insert prems5(1,3))
              apply assumption
            done
        done
    done
done
done
done

lemma P3_2_inv_saving: "
P3_2_inv_part b_0 w_0 A11 A12 A2 A3 s0 \<Longrightarrow>
consecutive s0 s \<Longrightarrow>
((((\<not> (w_0 s0)) \<or> ((A3 s) \<or> ((w_0 s) \<and> (A2 s)))) \<and> ((b_0 s0) \<or> ((\<not> (A12 s)) \<or> ((A3 s) \<or> ((w_0 s) \<and> (A2 s)))))) \<and> ((b_0 s) --> (\<not> (A11 s)))) \<Longrightarrow>
P3_2_inv_part b_0 w_0 A11 A12 A2 A3 s"unfolding P3_2_inv_part_def P3_2_part_def
apply(simp add: P3_2_inv_saving_gen always_imp_refl)
done

lemma P3_2einv_imp_req: "
P3_2_inv_part b_0 w_0 A11 A12 A2 A3 s \<Longrightarrow>
toEnvP s \<Longrightarrow>
True \<Longrightarrow>
P3_2_part A11 A12 A2 A3 s"unfolding P3_2_inv_part_def P3_2_part_def
apply(simp add: P3_2einv_imp_req_gen always_imp_refl)
done

lemmas P3_2_used_patterns = P3_2_def always_def weak_previous_def weak_until_def 

lemmas P3_2_inv_used_patterns = P3_2_inv_def always_inv_def weak_previous_def weak_until_inv_def previous_inv_def 

lemmas P3_2_inv_part_used_patterns = P3_2_inv_part_def P3_2_inv_used_patterns

lemmas P3_2_part_used_patterns = P3_2_part_def P3_2_used_patterns

definition P3_3 where "P3_3 A1 A2 A3 s \<equiv> (always (\<lambda> r2 r1 . ((weak_previous (\<lambda> r4 r3 . (\<not> (A1 r3))) r2 r1) \<or> (weak_until A2 A3 r2 r1))) s)"

definition P3_3_part where "P3_3_part A1 A2 A3 s \<equiv> (P3_3 A1 (\<lambda> s s1 . (A2 s1)) (\<lambda> s s1 . (A3 s1)) s)"

definition P3_3_inv where "P3_3_inv b_0 w_0 A1 A2_1 A3_1 s \<equiv> ((always_inv (\<lambda> r2 r1 . ((weak_previous (\<lambda> r4 r3 . (\<not> (A1 r3))) r2 r1) \<or> (weak_until_inv w_0 A2_1 A3_1 r2 r1))) s) \<and> (previous_inv b_0 (\<lambda> r4 r3 . (\<not> (A1 r3))) s))"

definition P3_3_inv_part where "P3_3_inv_part b_0 w_0 A1 A2 A3 s \<equiv> (P3_3_inv b_0 w_0 A1 (\<lambda> s s1 . (A2 s1)) (\<lambda> s s1 . (A3 s1)) s)"

lemma P3_3_inv_saving_gen: "
P3_3_inv b_0 w_0 A1 A2_1 A3_1 s0 \<Longrightarrow>
consecutive s0 s \<Longrightarrow>
(((True \<and> ((always_imp s0 (A2_1 s0) (A2_1 s)) \<and> ((always_imp s0 (A3_1 s0) (A3_1 s)) \<and> ((\<not> (w_0 s0)) \<or> ((A3_1 s s) \<or> ((w_0 s) \<and> (A2_1 s s))))))) \<and> (((b_0 s0) \<and> True) \<or> ((A3_1 s s) \<or> ((w_0 s) \<and> (A2_1 s s))))) \<and> ((b_0 s) --> (\<not> (A1 s)))) \<Longrightarrow>
P3_3_inv b_0 w_0 A1 A2_1 A3_1 s"
unfolding P3_3_inv_def
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
    apply(rule always_disj_rule)
    apply simp
      apply(erule conjE)
      subgoal premises prems3
      apply(rule conjI)
      apply(insert prems3(1,2))[1]
        apply(rule weak_previous_LS4)
        apply simp
          apply(rule always_imp_refl)
      apply(insert prems3(1,3))
        apply(rule weak_until_rule)
        apply simp
          apply(erule conjE)
          subgoal premises prems4
          apply(rule conjI)
          apply(insert prems4(1,2))[1]
            apply assumption
          apply(insert prems4(1,3))
            apply(erule conjE)
            subgoal premises prems5
            apply(rule conjI)
            apply(insert prems5(1,2))[1]
              apply assumption
            apply(insert prems5(1,3))
              apply(erule disjE)
              apply(rule disjI1)
                apply assumption
              apply(rule disjI2)
                apply(erule disjE)
                apply(rule disjI1)
                  apply assumption
                apply(rule disjI2)
                  apply(erule conjE)
                  subgoal premises prems6
                  apply(rule conjI)
                  apply(insert prems6(1,2))[1]
                    apply assumption
                  apply(insert prems6(1,3))
                    apply assumption
                  done
            done
          done
      done
  apply(insert prems2(1,3))
    apply(erule disjE)
    apply(rule disjI1)
      apply(rule weak_previous_one_point[OF prems1(3)])
      apply simp
        apply(erule conjE)
        subgoal premises prems7
        apply(rule conjI)
        apply(insert prems7(1,2))[1]
          apply assumption
        apply(insert prems7(1,3))
          apply(rule always_imp_refl)
        done
    apply(rule disjI2)
      apply(rule weak_until_one_point)
      apply simp
        apply(erule disjE)
        apply(rule disjI1)
          apply assumption
        apply(rule disjI2)
          apply(erule conjE)
          subgoal premises prems8
          apply(rule conjI)
          apply(insert prems8(1,2))[1]
            apply assumption
          apply(insert prems8(1,3))
            apply assumption
          done
  done
apply(insert prems1(1,3,5))
  apply(erule previous_rule)
  apply simp
  apply(rule impI)
  apply(erule impE)
  apply assumption
  subgoal premises prems9
  apply(insert prems9(1,3))
    apply assumption
  done
done
done

lemma P3_3einv_imp_req_gen: "
P3_3_inv b_0 w_0 A1 A2_1 A3_1 s0 \<Longrightarrow>
toEnvP s0 \<Longrightarrow>
(True \<and> ((always_imp s0 (A2_1 s0) (A2 s0)) \<and> (always_imp s0 (A3_1 s0) (A3 s0)))) \<Longrightarrow>
P3_3 A1 A2 A3 s0"unfolding P3_3_inv_def P3_3_def
subgoal premises prems1
apply(insert prems1(1,2))
apply(erule conjE)
subgoal premises prems2
apply(insert prems2(1,2) prems1(3))
apply(erule always_einv2req)
apply simp
  apply(rule always_disj_rule)
  apply simp
    apply(erule conjE)
    subgoal premises prems3
    apply(rule conjI)
    apply(insert prems3(1,2))[1]
      apply(rule weak_previous_LS5)
      apply simp
        apply(rule always_imp_refl)
    apply(insert prems3(1,3))
      apply(rule weak_until_einv2req)
      apply simp
        apply(erule conjE)
        subgoal premises prems4
        apply(rule conjI)
        apply(insert prems4(1,2))[1]
          apply assumption
        apply(insert prems4(1,3))
          apply assumption
        done
    done
done
done
done

lemma P3_3_inv_saving: "
P3_3_inv_part b_0 w_0 A1 A2 A3 s0 \<Longrightarrow>
consecutive s0 s \<Longrightarrow>
((((\<not> (w_0 s0)) \<or> ((A3 s) \<or> ((w_0 s) \<and> (A2 s)))) \<and> ((b_0 s0) \<or> ((A3 s) \<or> ((w_0 s) \<and> (A2 s))))) \<and> ((b_0 s) --> (\<not> (A1 s)))) \<Longrightarrow>
P3_3_inv_part b_0 w_0 A1 A2 A3 s"unfolding P3_3_inv_part_def P3_3_part_def
apply(simp add: P3_3_inv_saving_gen always_imp_refl)
done

lemma P3_3einv_imp_req: "
P3_3_inv_part b_0 w_0 A1 A2 A3 s \<Longrightarrow>
toEnvP s \<Longrightarrow>
True \<Longrightarrow>
P3_3_part A1 A2 A3 s"unfolding P3_3_inv_part_def P3_3_part_def
apply(simp add: P3_3einv_imp_req_gen always_imp_refl)
done

lemmas P3_3_used_patterns = P3_3_def always_def weak_previous_def weak_until_def 

lemmas P3_3_inv_used_patterns = P3_3_inv_def always_inv_def weak_previous_def weak_until_inv_def previous_inv_def 

lemmas P3_3_inv_part_used_patterns = P3_3_inv_part_def P3_3_inv_used_patterns

lemmas P3_3_part_used_patterns = P3_3_part_def P3_3_used_patterns

definition P3_4 where "P3_4 A11 A12 A2 A3 s \<equiv> (always (\<lambda> r2 r1 . ((weak_previous (\<lambda> r4 r3 . ((weak_previous (\<lambda> r6 r5 . (\<not> (A11 r5))) r4 r3) \<or> (\<not> (A12 r3)))) r2 r1) \<or> (weak_until A2 A3 r2 r1))) s)"

definition P3_4_part where "P3_4_part A11 A12 A2 A3 s \<equiv> (P3_4 A11 A12 (\<lambda> s s1 . (A2 s1)) (\<lambda> s s1 . (A3 s1)) s)"

definition P3_4_inv where "P3_4_inv b_0 b_1 w_0 A11 A12 A2_1 A3_1 s \<equiv> (((always_inv (\<lambda> r2 r1 . ((weak_previous (\<lambda> r4 r3 . ((weak_previous (\<lambda> r6 r5 . (\<not> (A11 r5))) r4 r3) \<or> (\<not> (A12 r3)))) r2 r1) \<or> (weak_until_inv w_0 A2_1 A3_1 r2 r1))) s) \<and> (previous_inv b_1 (\<lambda> r4 r3 . ((weak_previous (\<lambda> r6 r5 . (\<not> (A11 r5))) r4 r3) \<or> (\<not> (A12 r3)))) s)) \<and> (previous_inv b_0 (\<lambda> r6 r5 . (\<not> (A11 r5))) s))"

definition P3_4_inv_part where "P3_4_inv_part b_0 b_1 w_0 A11 A12 A2 A3 s \<equiv> (P3_4_inv b_0 b_1 w_0 A11 A12 (\<lambda> s s1 . (A2 s1)) (\<lambda> s s1 . (A3 s1)) s)"

lemma P3_4_inv_saving_gen: "
P3_4_inv b_0 b_1 w_0 A11 A12 A2_1 A3_1 s0 \<Longrightarrow>
consecutive s0 s \<Longrightarrow>
(((((True \<and> True) \<and> ((always_imp s0 (A2_1 s0) (A2_1 s)) \<and> ((always_imp s0 (A3_1 s0) (A3_1 s)) \<and> ((\<not> (w_0 s0)) \<or> ((A3_1 s s) \<or> ((w_0 s) \<and> (A2_1 s s))))))) \<and> (((b_1 s0) \<and> (True \<and> True)) \<or> ((A3_1 s s) \<or> ((w_0 s) \<and> (A2_1 s s))))) \<and> ((b_1 s) --> (((b_0 s0) \<and> True) \<or> (\<not> (A12 s))))) \<and> ((b_0 s) --> (\<not> (A11 s)))) \<Longrightarrow>
P3_4_inv b_0 b_1 w_0 A11 A12 A2_1 A3_1 s"
unfolding P3_4_inv_def
apply(erule conjE)
apply(erule conjE)
subgoal premises prems1
apply(rule conjI)
apply(insert prems1(1,2,4))[1]
apply(erule conjE)
apply(erule conjE)
subgoal premises prems2
apply(rule conjI)
apply(insert prems2(1,2,4))[1]
apply(erule always_rule)
  apply simp
  apply(erule conjE)
  subgoal premises prems3
  apply(rule conjI)
  apply(insert prems3(1,2))[1]
    apply(rule always_disj_rule)
    apply simp
      apply(erule conjE)
      subgoal premises prems4
      apply(rule conjI)
      apply(insert prems4(1,2))[1]
        apply(rule weak_previous_LS4)
        apply simp
          apply(rule always_disj_rule)
          apply simp
            apply(erule conjE)
            subgoal premises prems5
            apply(rule conjI)
            apply(insert prems5(1,2))[1]
              apply(rule weak_previous_LS4)
              apply simp
                apply(rule always_imp_refl)
            apply(insert prems5(1,3))
              apply(rule always_imp_refl)
            done
      apply(insert prems4(1,3))
        apply(rule weak_until_rule)
        apply simp
          apply(erule conjE)
          subgoal premises prems6
          apply(rule conjI)
          apply(insert prems6(1,2))[1]
            apply assumption
          apply(insert prems6(1,3))
            apply(erule conjE)
            subgoal premises prems7
            apply(rule conjI)
            apply(insert prems7(1,2))[1]
              apply assumption
            apply(insert prems7(1,3))
              apply(erule disjE)
              apply(rule disjI1)
                apply assumption
              apply(rule disjI2)
                apply(erule disjE)
                apply(rule disjI1)
                  apply assumption
                apply(rule disjI2)
                  apply(erule conjE)
                  subgoal premises prems8
                  apply(rule conjI)
                  apply(insert prems8(1,2))[1]
                    apply assumption
                  apply(insert prems8(1,3))
                    apply assumption
                  done
            done
          done
      done
  apply(insert prems3(1,3))
    apply(erule disjE)
    apply(rule disjI1)
      apply(rule weak_previous_one_point[OF prems2(3)])
      apply simp
        apply(erule conjE)
        subgoal premises prems9
        apply(rule conjI)
        apply(insert prems9(1,2))[1]
          apply assumption
        apply(insert prems9(1,3))
          apply(rule always_disj_rule)
          apply simp
            apply(erule conjE)
            subgoal premises prems10
            apply(rule conjI)
            apply(insert prems10(1,2))[1]
              apply(rule weak_previous_LS4)
              apply simp
                apply(rule always_imp_refl)
            apply(insert prems10(1,3))
              apply(rule always_imp_refl)
            done
        done
    apply(rule disjI2)
      apply(rule weak_until_one_point)
      apply simp
        apply(erule disjE)
        apply(rule disjI1)
          apply assumption
        apply(rule disjI2)
          apply(erule conjE)
          subgoal premises prems11
          apply(rule conjI)
          apply(insert prems11(1,2))[1]
            apply assumption
          apply(insert prems11(1,3))
            apply assumption
          done
  done
apply(insert prems2(1,3,5))
  apply(erule previous_rule)
  apply simp
  apply(rule impI)
  apply(erule impE)
  apply assumption
  subgoal premises prems12
  apply(insert prems12(1,3))
    apply(erule disjE)
    apply(rule disjI1)
      apply(rule weak_previous_one_point[OF prems1(3)])
      apply simp
        apply(erule conjE)
        subgoal premises prems13
        apply(rule conjI)
        apply(insert prems13(1,2))[1]
          apply assumption
        apply(insert prems13(1,3))
          apply(rule always_imp_refl)
        done
    apply(rule disjI2)
      apply assumption
  done
done
apply(insert prems1(1,3,5))
  apply(erule previous_rule)
  apply simp
  apply(rule impI)
  apply(erule impE)
  apply assumption
  subgoal premises prems14
  apply(insert prems14(1,3))
    apply assumption
  done
done
done

lemma P3_4einv_imp_req_gen: "
P3_4_inv b_0 b_1 w_0 A11 A12 A2_1 A3_1 s0 \<Longrightarrow>
toEnvP s0 \<Longrightarrow>
((True \<and> True) \<and> ((always_imp s0 (A2_1 s0) (A2 s0)) \<and> (always_imp s0 (A3_1 s0) (A3 s0)))) \<Longrightarrow>
P3_4 A11 A12 A2 A3 s0"unfolding P3_4_inv_def P3_4_def
subgoal premises prems1
apply(insert prems1(1,2))
apply(simp only: conj_assoc)
apply(erule conjE)
subgoal premises prems2
apply(insert prems2(1,2) prems1(3))
apply(erule always_einv2req)
apply simp
  apply(rule always_disj_rule)
  apply simp
    apply(erule conjE)
    subgoal premises prems3
    apply(rule conjI)
    apply(insert prems3(1,2))[1]
      apply(rule weak_previous_LS5)
      apply simp
        apply(rule always_disj_rule)
        apply simp
          apply(erule conjE)
          subgoal premises prems4
          apply(rule conjI)
          apply(insert prems4(1,2))[1]
            apply(rule weak_previous_LS5)
            apply simp
              apply(rule always_imp_refl)
          apply(insert prems4(1,3))
            apply(rule always_imp_refl)
          done
    apply(insert prems3(1,3))
      apply(rule weak_until_einv2req)
      apply simp
        apply(erule conjE)
        subgoal premises prems5
        apply(rule conjI)
        apply(insert prems5(1,2))[1]
          apply assumption
        apply(insert prems5(1,3))
          apply assumption
        done
    done
done
done
done

lemma P3_4_inv_saving: "
P3_4_inv_part b_0 b_1 w_0 A11 A12 A2 A3 s0 \<Longrightarrow>
consecutive s0 s \<Longrightarrow>
(((((\<not> (w_0 s0)) \<or> ((A3 s) \<or> ((w_0 s) \<and> (A2 s)))) \<and> ((b_1 s0) \<or> ((A3 s) \<or> ((w_0 s) \<and> (A2 s))))) \<and> ((b_1 s) --> ((b_0 s0) \<or> (\<not> (A12 s))))) \<and> ((b_0 s) --> (\<not> (A11 s)))) \<Longrightarrow>
P3_4_inv_part b_0 b_1 w_0 A11 A12 A2 A3 s"unfolding P3_4_inv_part_def P3_4_part_def
apply(simp add: P3_4_inv_saving_gen always_imp_refl)
done

lemma P3_4einv_imp_req: "
P3_4_inv_part b_0 b_1 w_0 A11 A12 A2 A3 s \<Longrightarrow>
toEnvP s \<Longrightarrow>
True \<Longrightarrow>
P3_4_part A11 A12 A2 A3 s"unfolding P3_4_inv_part_def P3_4_part_def
apply(simp add: P3_4einv_imp_req_gen always_imp_refl)
done

lemmas P3_4_used_patterns = P3_4_def always_def weak_previous_def weak_previous_def weak_until_def 

lemmas P3_4_inv_used_patterns = P3_4_inv_def always_inv_def weak_previous_def weak_previous_def weak_until_inv_def previous_inv_def weak_previous_def previous_inv_def 

lemmas P3_4_inv_part_used_patterns = P3_4_inv_part_def P3_4_inv_used_patterns

lemmas P3_4_part_used_patterns = P3_4_part_def P3_4_used_patterns

definition P4_1 where "P4_1 t A1 A2 A3 s \<equiv> (always (\<lambda> r2 r1 . ((\<not> (A1 r1)) \<or> (constrained_weak_until t A2 A3 r2 r1))) s)"

definition P4_1_part where "P4_1_part t A1 A2 A3 s \<equiv> (P4_1 t A1 (\<lambda> s s1 . (A2 s1)) (\<lambda> s s1 . (A3 s1)) s)"

definition P4_1_inv where "P4_1_inv t t1_0 A1 A2_1 A3_1 s \<equiv> (always_inv (\<lambda> r2 r1 . ((\<not> (A1 r1)) \<or> (constrained_weak_until_inv t t1_0 A2_1 A3_1 r2 r1))) s)"

definition P4_1_inv_part where "P4_1_inv_part t t1_0 A1 A2 A3 s \<equiv> (P4_1_inv t t1_0 A1 (\<lambda> s s1 . (A2 s1)) (\<lambda> s s1 . (A3 s1)) s)"

lemma P4_1_inv_saving_gen: "
P4_1_inv t t1_0 A1 A2_1 A3_1 s0 \<Longrightarrow>
consecutive s0 s \<Longrightarrow>
((True \<and> ((always_imp s0 (A2_1 s0) (A2_1 s)) \<and> ((always_imp s0 (A3_1 s0) (A3_1 s)) \<and> ((((t1_0 s0) < t) \<and> (((A3_1 s s) \<and> ((t1_0 s) <= (t + 1))) \<or> (((t1_0 s) <= ((t1_0 s0) + 1)) \<and> (A2_1 s s)))) \<or> (((t1_0 s0) >= t) \<and> ((t1_0 s) <= ((t1_0 s0) + 1))))))) \<and> ((\<not> (A1 s)) \<or> ((A3_1 s s) \<or> (((t1_0 s) = 0) \<and> (A2_1 s s))))) \<Longrightarrow>
P4_1_inv t t1_0 A1 A2_1 A3_1 s"
unfolding P4_1_inv_def
apply(erule always_rule)
  apply simp
  apply(erule conjE)
  subgoal premises prems1
  apply(rule conjI)
  apply(insert prems1(1,2))[1]
    apply(rule always_disj_rule)
    apply simp
      apply(erule conjE)
      subgoal premises prems2
      apply(rule conjI)
      apply(insert prems2(1,2))[1]
        apply(rule always_imp_refl)
      apply(insert prems2(1,3))
        apply(rule constrained_weak_until_rule)
        apply simp
          apply(erule conjE)
          subgoal premises prems3
          apply(rule conjI)
          apply(insert prems3(1,2))[1]
            apply assumption
          apply(insert prems3(1,3))
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
                  apply assumption
                apply(insert prems5(1,3))
                  apply(erule disjE)
                  apply(rule disjI1)
                    apply(erule conjE)
                    subgoal premises prems6
                    apply(rule conjI)
                    apply(insert prems6(1,2))[1]
                      apply assumption
                    apply(insert prems6(1,3))
                      apply assumption
                    done
                  apply(rule disjI2)
                    apply(erule conjE)
                    subgoal premises prems7
                    apply(rule conjI)
                    apply(insert prems7(1,2))[1]
                      apply assumption
                    apply(insert prems7(1,3))
                      apply assumption
                    done
                done
              apply(rule disjI2)
                apply assumption
            done
          done
      done
  apply(insert prems1(1,3))
    apply(erule disjE)
    apply(rule disjI1)
      apply assumption
    apply(rule disjI2)
      apply(rule constrained_weak_until_one_point)
      apply simp
        apply(erule disjE)
        apply(rule disjI1)
          apply assumption
        apply(rule disjI2)
          apply(erule conjE)
          subgoal premises prems8
          apply(rule conjI)
          apply(insert prems8(1,2))[1]
            apply assumption
          apply(insert prems8(1,3))
            apply assumption
          done
  done
done

lemma P4_1einv_imp_req_gen: "
P4_1_inv t t1_0 A1 A2_1 A3_1 s0 \<Longrightarrow>
toEnvP s0 \<Longrightarrow>
(True \<and> ((always_imp s0 (A2_1 s0) (A2 s0)) \<and> (always_imp s0 (A3_1 s0) (A3 s0)))) \<Longrightarrow>
P4_1 t A1 A2 A3 s0"unfolding P4_1_inv_def P4_1_def
apply(erule always_einv2req)
apply simp
  apply(rule always_disj_rule)
  apply simp
    apply(erule conjE)
    subgoal premises prems3
    apply(rule conjI)
    apply(insert prems3(1,2))[1]
      apply(rule always_imp_refl)
    apply(insert prems3(1,3))
      apply(rule constrained_weak_until_einv2req)
      apply simp
        apply(erule conjE)
        subgoal premises prems4
        apply(rule conjI)
        apply(insert prems4(1,2))[1]
          apply assumption
        apply(insert prems4(1,3))
          apply assumption
        done
    done
done

lemma P4_1_inv_saving: "
P4_1_inv_part t t1_0 A1 A2 A3 s0 \<Longrightarrow>
consecutive s0 s \<Longrightarrow>
(((((t1_0 s0) < t) \<and> (((A3 s) \<and> ((t1_0 s) <= (t + 1))) \<or> (((t1_0 s) <= ((t1_0 s0) + 1)) \<and> (A2 s)))) \<or> (((t1_0 s0) >= t) \<and> ((t1_0 s) <= ((t1_0 s0) + 1)))) \<and> ((\<not> (A1 s)) \<or> ((A3 s) \<or> (((t1_0 s) = 0) \<and> (A2 s))))) \<Longrightarrow>
P4_1_inv_part t t1_0 A1 A2 A3 s"unfolding P4_1_inv_part_def P4_1_part_def
apply(simp add: P4_1_inv_saving_gen always_imp_refl)
done

lemma P4_1einv_imp_req: "
P4_1_inv_part t t1_0 A1 A2 A3 s \<Longrightarrow>
toEnvP s \<Longrightarrow>
True \<Longrightarrow>
P4_1_part t A1 A2 A3 s"unfolding P4_1_inv_part_def P4_1_part_def
apply(simp add: P4_1einv_imp_req_gen always_imp_refl)
done

lemmas P4_1_used_patterns = P4_1_def always_def constrained_weak_until_def 

lemmas P4_1_inv_used_patterns = P4_1_inv_def always_inv_def constrained_weak_until_inv_def 

lemmas P4_1_inv_part_used_patterns = P4_1_inv_part_def P4_1_inv_used_patterns

lemmas P4_1_part_used_patterns = P4_1_part_def P4_1_used_patterns

definition P4_2 where "P4_2 t A11 A12 A2 A3 s \<equiv> (always (\<lambda> r2 r1 . ((weak_previous (\<lambda> r4 r3 . (\<not> (A11 r3))) r2 r1) \<or> ((\<not> (A12 r1)) \<or> (constrained_weak_until t A2 A3 r2 r1)))) s)"

definition P4_2_part where "P4_2_part t A11 A12 A2 A3 s \<equiv> (P4_2 t A11 A12 (\<lambda> s s1 . (A2 s1)) (\<lambda> s s1 . (A3 s1)) s)"

definition P4_2_inv where "P4_2_inv t b_0 t1_0 A11 A12 A2_1 A3_1 s \<equiv> ((always_inv (\<lambda> r2 r1 . ((weak_previous (\<lambda> r4 r3 . (\<not> (A11 r3))) r2 r1) \<or> ((\<not> (A12 r1)) \<or> (constrained_weak_until_inv t t1_0 A2_1 A3_1 r2 r1)))) s) \<and> (previous_inv b_0 (\<lambda> r4 r3 . (\<not> (A11 r3))) s))"

definition P4_2_inv_part where "P4_2_inv_part t b_0 t1_0 A11 A12 A2 A3 s \<equiv> (P4_2_inv t b_0 t1_0 A11 A12 (\<lambda> s s1 . (A2 s1)) (\<lambda> s s1 . (A3 s1)) s)"

lemma P4_2_inv_saving_gen: "
P4_2_inv t b_0 t1_0 A11 A12 A2_1 A3_1 s0 \<Longrightarrow>
consecutive s0 s \<Longrightarrow>
(((True \<and> (True \<and> ((always_imp s0 (A2_1 s0) (A2_1 s)) \<and> ((always_imp s0 (A3_1 s0) (A3_1 s)) \<and> ((((t1_0 s0) < t) \<and> (((A3_1 s s) \<and> ((t1_0 s) <= (t + 1))) \<or> (((t1_0 s) <= ((t1_0 s0) + 1)) \<and> (A2_1 s s)))) \<or> (((t1_0 s0) >= t) \<and> ((t1_0 s) <= ((t1_0 s0) + 1)))))))) \<and> (((b_0 s0) \<and> True) \<or> ((\<not> (A12 s)) \<or> ((A3_1 s s) \<or> (((t1_0 s) = 0) \<and> (A2_1 s s)))))) \<and> ((b_0 s) --> (\<not> (A11 s)))) \<Longrightarrow>
P4_2_inv t b_0 t1_0 A11 A12 A2_1 A3_1 s"
unfolding P4_2_inv_def
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
    apply(rule always_disj_rule)
    apply simp
      apply(erule conjE)
      subgoal premises prems3
      apply(rule conjI)
      apply(insert prems3(1,2))[1]
        apply(rule weak_previous_LS4)
        apply simp
          apply(rule always_imp_refl)
      apply(insert prems3(1,3))
        apply(rule always_disj_rule)
        apply simp
          apply(erule conjE)
          subgoal premises prems4
          apply(rule conjI)
          apply(insert prems4(1,2))[1]
            apply(rule always_imp_refl)
          apply(insert prems4(1,3))
            apply(rule constrained_weak_until_rule)
            apply simp
              apply(erule conjE)
              subgoal premises prems5
              apply(rule conjI)
              apply(insert prems5(1,2))[1]
                apply assumption
              apply(insert prems5(1,3))
                apply(erule conjE)
                subgoal premises prems6
                apply(rule conjI)
                apply(insert prems6(1,2))[1]
                  apply assumption
                apply(insert prems6(1,3))
                  apply(erule disjE)
                  apply(rule disjI1)
                    apply(erule conjE)
                    subgoal premises prems7
                    apply(rule conjI)
                    apply(insert prems7(1,2))[1]
                      apply assumption
                    apply(insert prems7(1,3))
                      apply(erule disjE)
                      apply(rule disjI1)
                        apply(erule conjE)
                        subgoal premises prems8
                        apply(rule conjI)
                        apply(insert prems8(1,2))[1]
                          apply assumption
                        apply(insert prems8(1,3))
                          apply assumption
                        done
                      apply(rule disjI2)
                        apply(erule conjE)
                        subgoal premises prems9
                        apply(rule conjI)
                        apply(insert prems9(1,2))[1]
                          apply assumption
                        apply(insert prems9(1,3))
                          apply assumption
                        done
                    done
                  apply(rule disjI2)
                    apply assumption
                done
              done
          done
      done
  apply(insert prems2(1,3))
    apply(erule disjE)
    apply(rule disjI1)
      apply(rule weak_previous_one_point[OF prems1(3)])
      apply simp
        apply(erule conjE)
        subgoal premises prems10
        apply(rule conjI)
        apply(insert prems10(1,2))[1]
          apply assumption
        apply(insert prems10(1,3))
          apply(rule always_imp_refl)
        done
    apply(rule disjI2)
      apply(erule disjE)
      apply(rule disjI1)
        apply assumption
      apply(rule disjI2)
        apply(rule constrained_weak_until_one_point)
        apply simp
          apply(erule disjE)
          apply(rule disjI1)
            apply assumption
          apply(rule disjI2)
            apply(erule conjE)
            subgoal premises prems11
            apply(rule conjI)
            apply(insert prems11(1,2))[1]
              apply assumption
            apply(insert prems11(1,3))
              apply assumption
            done
  done
apply(insert prems1(1,3,5))
  apply(erule previous_rule)
  apply simp
  apply(rule impI)
  apply(erule impE)
  apply assumption
  subgoal premises prems12
  apply(insert prems12(1,3))
    apply assumption
  done
done
done

lemma P4_2einv_imp_req_gen: "
P4_2_inv t b_0 t1_0 A11 A12 A2_1 A3_1 s0 \<Longrightarrow>
toEnvP s0 \<Longrightarrow>
(True \<and> (True \<and> ((always_imp s0 (A2_1 s0) (A2 s0)) \<and> (always_imp s0 (A3_1 s0) (A3 s0))))) \<Longrightarrow>
P4_2 t A11 A12 A2 A3 s0"unfolding P4_2_inv_def P4_2_def
subgoal premises prems1
apply(insert prems1(1,2))
apply(erule conjE)
subgoal premises prems2
apply(insert prems2(1,2) prems1(3))
apply(erule always_einv2req)
apply simp
  apply(rule always_disj_rule)
  apply simp
    apply(erule conjE)
    subgoal premises prems3
    apply(rule conjI)
    apply(insert prems3(1,2))[1]
      apply(rule weak_previous_LS5)
      apply simp
        apply(rule always_imp_refl)
    apply(insert prems3(1,3))
      apply(rule always_disj_rule)
      apply simp
        apply(erule conjE)
        subgoal premises prems4
        apply(rule conjI)
        apply(insert prems4(1,2))[1]
          apply(rule always_imp_refl)
        apply(insert prems4(1,3))
          apply(rule constrained_weak_until_einv2req)
          apply simp
            apply(erule conjE)
            subgoal premises prems5
            apply(rule conjI)
            apply(insert prems5(1,2))[1]
              apply assumption
            apply(insert prems5(1,3))
              apply assumption
            done
        done
    done
done
done
done

lemma P4_2_inv_saving: "
P4_2_inv_part t b_0 t1_0 A11 A12 A2 A3 s0 \<Longrightarrow>
consecutive s0 s \<Longrightarrow>
((((((t1_0 s0) < t) \<and> (((A3 s) \<and> ((t1_0 s) <= (t + 1))) \<or> (((t1_0 s) <= ((t1_0 s0) + 1)) \<and> (A2 s)))) \<or> (((t1_0 s0) >= t) \<and> ((t1_0 s) <= ((t1_0 s0) + 1)))) \<and> ((b_0 s0) \<or> ((\<not> (A12 s)) \<or> ((A3 s) \<or> (((t1_0 s) = 0) \<and> (A2 s)))))) \<and> ((b_0 s) --> (\<not> (A11 s)))) \<Longrightarrow>
P4_2_inv_part t b_0 t1_0 A11 A12 A2 A3 s"unfolding P4_2_inv_part_def P4_2_part_def
apply(simp add: P4_2_inv_saving_gen always_imp_refl)
done

lemma P4_2einv_imp_req: "
P4_2_inv_part t b_0 t1_0 A11 A12 A2 A3 s \<Longrightarrow>
toEnvP s \<Longrightarrow>
True \<Longrightarrow>
P4_2_part t A11 A12 A2 A3 s"unfolding P4_2_inv_part_def P4_2_part_def
apply(simp add: P4_2einv_imp_req_gen always_imp_refl)
done

lemmas P4_2_used_patterns = P4_2_def always_def weak_previous_def constrained_weak_until_def 

lemmas P4_2_inv_used_patterns = P4_2_inv_def always_inv_def weak_previous_def constrained_weak_until_inv_def previous_inv_def 

lemmas P4_2_inv_part_used_patterns = P4_2_inv_part_def P4_2_inv_used_patterns

lemmas P4_2_part_used_patterns = P4_2_part_def P4_2_used_patterns

definition P4_3 where "P4_3 t A11 A12 A21 A22 A3 s \<equiv> (always (\<lambda> r2 r1 . ((weak_previous (\<lambda> r4 r3 . (\<not> (A11 r3))) r2 r1) \<or> ((\<not> (A12 r1)) \<or> (constrained_weak_until t (\<lambda> r4 r3 . ((previous A21 r4 r3) \<and> (A22 r4 r3))) A3 r2 r1)))) s)"

definition P4_3_part where "P4_3_part t A11 A12 A21 A22 A3 s \<equiv> (P4_3 t A11 A12 (\<lambda> s s1 . (A21 s1)) (\<lambda> s s1 . (A22 s1)) (\<lambda> s s1 . (A3 s1)) s)"

definition P4_3_inv where "P4_3_inv t b_0 b_1 t1_0 A11 A12 A21_1 A22_1 A3_1 s \<equiv> (((always_inv (\<lambda> r2 r1 . ((weak_previous (\<lambda> r4 r3 . (\<not> (A11 r3))) r2 r1) \<or> ((\<not> (A12 r1)) \<or> (constrained_weak_until_inv t t1_0 (\<lambda> r4 r3 . ((previous A21_1 r4 r3) \<and> (A22_1 r4 r3))) A3_1 r2 r1)))) s) \<and> (previous_inv b_0 (\<lambda> r4 r3 . (\<not> (A11 r3))) s)) \<and> (previous_inv b_1 A21_1 s))"

definition P4_3_inv_part where "P4_3_inv_part t b_0 b_1 t1_0 A11 A12 A21 A22 A3 s \<equiv> (P4_3_inv t b_0 b_1 t1_0 A11 A12 (\<lambda> s s1 . (A21 s1)) (\<lambda> s s1 . (A22 s1)) (\<lambda> s s1 . (A3 s1)) s)"

lemma P4_3_inv_saving_gen: "
P4_3_inv t b_0 b_1 t1_0 A11 A12 A21_1 A22_1 A3_1 s0 \<Longrightarrow>
consecutive s0 s \<Longrightarrow>
((((True \<and> (True \<and> (((always_imp s0 (A21_1 s0) (A21_1 s)) \<and> (always_imp s0 (\<lambda> r3 . (A22_1 s0 r3)) (\<lambda> r3 . (A22_1 s r3)))) \<and> ((always_imp s0 (A3_1 s0) (A3_1 s)) \<and> ((((t1_0 s0) < t) \<and> (((A3_1 s s) \<and> ((t1_0 s) <= (t + 1))) \<or> (((t1_0 s) <= ((t1_0 s0) + 1)) \<and> (((b_1 s0) \<and> (always_imp s0 (A21_1 s0) (A21_1 s))) \<and> (A22_1 s s))))) \<or> (((t1_0 s0) >= t) \<and> ((t1_0 s) <= ((t1_0 s0) + 1)))))))) \<and> (((b_0 s0) \<and> True) \<or> ((\<not> (A12 s)) \<or> ((A3_1 s s) \<or> (((t1_0 s) = 0) \<and> (((b_1 s0) \<and> (always_imp s0 (A21_1 s0) (A21_1 s))) \<and> (A22_1 s s))))))) \<and> ((b_0 s) --> (\<not> (A11 s)))) \<and> ((b_1 s) --> (A21_1 s s))) \<Longrightarrow>
P4_3_inv t b_0 b_1 t1_0 A11 A12 A21_1 A22_1 A3_1 s"
unfolding P4_3_inv_def
apply(erule conjE)
apply(erule conjE)
subgoal premises prems1
apply(rule conjI)
apply(insert prems1(1,2,4))[1]
apply(erule conjE)
apply(erule conjE)
subgoal premises prems2
apply(rule conjI)
apply(insert prems2(1,2,4))[1]
apply(erule always_rule)
  apply simp
  apply(erule conjE)
  subgoal premises prems3
  apply(rule conjI)
  apply(insert prems3(1,2))[1]
    apply(rule always_disj_rule)
    apply simp
      apply(erule conjE)
      subgoal premises prems4
      apply(rule conjI)
      apply(insert prems4(1,2))[1]
        apply(rule weak_previous_LS4)
        apply simp
          apply(rule always_imp_refl)
      apply(insert prems4(1,3))
        apply(rule always_disj_rule)
        apply simp
          apply(erule conjE)
          subgoal premises prems5
          apply(rule conjI)
          apply(insert prems5(1,2))[1]
            apply(rule always_imp_refl)
          apply(insert prems5(1,3))
            apply(rule constrained_weak_until_rule)
            apply simp
              apply(erule conjE)
              subgoal premises prems6
              apply(rule conjI)
              apply(insert prems6(1,2))[1]
                apply(rule always_conj_rule)
                apply simp
                  apply(erule conjE)
                  subgoal premises prems7
                  apply(rule conjI)
                  apply(insert prems7(1,2))[1]
                    apply(rule previous_LS4)
                    apply simp
                      apply assumption
                  apply(insert prems7(1,3))
                    apply assumption
                  done
              apply(insert prems6(1,3))
                apply(erule conjE)
                subgoal premises prems8
                apply(rule conjI)
                apply(insert prems8(1,2))[1]
                  apply assumption
                apply(insert prems8(1,3))
                  apply(erule disjE)
                  apply(rule disjI1)
                    apply(erule conjE)
                    subgoal premises prems9
                    apply(rule conjI)
                    apply(insert prems9(1,2))[1]
                      apply assumption
                    apply(insert prems9(1,3))
                      apply(erule disjE)
                      apply(rule disjI1)
                        apply(erule conjE)
                        subgoal premises prems10
                        apply(rule conjI)
                        apply(insert prems10(1,2))[1]
                          apply assumption
                        apply(insert prems10(1,3))
                          apply assumption
                        done
                      apply(rule disjI2)
                        apply(erule conjE)
                        subgoal premises prems11
                        apply(rule conjI)
                        apply(insert prems11(1,2))[1]
                          apply assumption
                        apply(insert prems11(1,3))
                          apply(erule conjE)
                          subgoal premises prems12
                          apply(rule conjI)
                          apply(insert prems12(1,2))[1]
                            apply(rule previous_one_point[OF prems1(3)])
                            apply simp
                              apply(erule conjE)
                              subgoal premises prems13
                              apply(rule conjI)
                              apply(insert prems13(1,2))[1]
                                apply assumption
                              apply(insert prems13(1,3))
                                apply assumption
                              done
                          apply(insert prems12(1,3))
                            apply assumption
                          done
                        done
                    done
                  apply(rule disjI2)
                    apply assumption
                done
              done
          done
      done
  apply(insert prems3(1,3))
    apply(erule disjE)
    apply(rule disjI1)
      apply(rule weak_previous_one_point[OF prems2(3)])
      apply simp
        apply(erule conjE)
        subgoal premises prems14
        apply(rule conjI)
        apply(insert prems14(1,2))[1]
          apply assumption
        apply(insert prems14(1,3))
          apply(rule always_imp_refl)
        done
    apply(rule disjI2)
      apply(erule disjE)
      apply(rule disjI1)
        apply assumption
      apply(rule disjI2)
        apply(rule constrained_weak_until_one_point)
        apply simp
          apply(erule disjE)
          apply(rule disjI1)
            apply assumption
          apply(rule disjI2)
            apply(erule conjE)
            subgoal premises prems15
            apply(rule conjI)
            apply(insert prems15(1,2))[1]
              apply assumption
            apply(insert prems15(1,3))
              apply(erule conjE)
              subgoal premises prems16
              apply(rule conjI)
              apply(insert prems16(1,2))[1]
                apply(rule previous_one_point[OF prems1(3)])
                apply simp
                  apply(erule conjE)
                  subgoal premises prems17
                  apply(rule conjI)
                  apply(insert prems17(1,2))[1]
                    apply assumption
                  apply(insert prems17(1,3))
                    apply assumption
                  done
              apply(insert prems16(1,3))
                apply assumption
              done
            done
  done
apply(insert prems2(1,3,5))
  apply(erule previous_rule)
  apply simp
  apply(rule impI)
  apply(erule impE)
  apply assumption
  subgoal premises prems18
  apply(insert prems18(1,3))
    apply assumption
  done
done
apply(insert prems1(1,3,5))
  apply(erule previous_rule)
  apply simp
  apply(rule impI)
  apply(erule impE)
  apply assumption
  subgoal premises prems19
  apply(insert prems19(1,3))
    apply assumption
  done
done
done

lemma P4_3einv_imp_req_gen: "
P4_3_inv t b_0 b_1 t1_0 A11 A12 A21_1 A22_1 A3_1 s0 \<Longrightarrow>
toEnvP s0 \<Longrightarrow>
(True \<and> (True \<and> (((always_imp s0 (A21_1 s0) (A21 s0)) \<and> (always_imp s0 (\<lambda> r3 . (A22_1 s0 r3)) (\<lambda> r3 . (A22 s0 r3)))) \<and> (always_imp s0 (A3_1 s0) (A3 s0))))) \<Longrightarrow>
P4_3 t A11 A12 A21 A22 A3 s0"unfolding P4_3_inv_def P4_3_def
subgoal premises prems1
apply(insert prems1(1,2))
apply(simp only: conj_assoc)
apply(erule conjE)
subgoal premises prems2
apply(insert prems2(1,2) prems1(3))
apply(erule always_einv2req)
apply simp
  apply(rule always_disj_rule)
  apply simp
    apply(erule conjE)
    subgoal premises prems3
    apply(rule conjI)
    apply(insert prems3(1,2))[1]
      apply(rule weak_previous_LS5)
      apply simp
        apply(rule always_imp_refl)
    apply(insert prems3(1,3))
      apply(rule always_disj_rule)
      apply simp
        apply(erule conjE)
        subgoal premises prems4
        apply(rule conjI)
        apply(insert prems4(1,2))[1]
          apply(rule always_imp_refl)
        apply(insert prems4(1,3))
          apply(rule constrained_weak_until_einv2req)
          apply simp
            apply(erule conjE)
            subgoal premises prems5
            apply(rule conjI)
            apply(insert prems5(1,2))[1]
              apply(rule always_conj_rule)
              apply simp
                apply(erule conjE)
                subgoal premises prems6
                apply(rule conjI)
                apply(insert prems6(1,2))[1]
                  apply(rule previous_LS5)
                  apply simp
                    apply assumption
                apply(insert prems6(1,3))
                  apply assumption
                done
            apply(insert prems5(1,3))
              apply assumption
            done
        done
    done
done
done
done

lemma P4_3_inv_saving: "
P4_3_inv_part t b_0 b_1 t1_0 A11 A12 A21 A22 A3 s0 \<Longrightarrow>
consecutive s0 s \<Longrightarrow>
(((((((t1_0 s0) < t) \<and> (((A3 s) \<and> ((t1_0 s) <= (t + 1))) \<or> (((t1_0 s) <= ((t1_0 s0) + 1)) \<and> ((b_1 s0) \<and> (A22 s))))) \<or> (((t1_0 s0) >= t) \<and> ((t1_0 s) <= ((t1_0 s0) + 1)))) \<and> ((b_0 s0) \<or> ((\<not> (A12 s)) \<or> ((A3 s) \<or> (((t1_0 s) = 0) \<and> ((b_1 s0) \<and> (A22 s))))))) \<and> ((b_0 s) --> (\<not> (A11 s)))) \<and> ((b_1 s) --> (A21 s))) \<Longrightarrow>
P4_3_inv_part t b_0 b_1 t1_0 A11 A12 A21 A22 A3 s"unfolding P4_3_inv_part_def P4_3_part_def
apply(simp add: P4_3_inv_saving_gen always_imp_refl)
done

lemma P4_3einv_imp_req: "
P4_3_inv_part t b_0 b_1 t1_0 A11 A12 A21 A22 A3 s \<Longrightarrow>
toEnvP s \<Longrightarrow>
True \<Longrightarrow>
P4_3_part t A11 A12 A21 A22 A3 s"unfolding P4_3_inv_part_def P4_3_part_def
apply(simp add: P4_3einv_imp_req_gen always_imp_refl)
done

lemmas P4_3_used_patterns = P4_3_def always_def weak_previous_def constrained_weak_until_def previous_def 

lemmas P4_3_inv_used_patterns = P4_3_inv_def always_inv_def weak_previous_def constrained_weak_until_inv_def previous_def previous_inv_def previous_inv_def 

lemmas P4_3_inv_part_used_patterns = P4_3_inv_part_def P4_3_inv_used_patterns

lemmas P4_3_part_used_patterns = P4_3_part_def P4_3_used_patterns

definition P6_1 where "P6_1 t A1 A2 A3 A4 s \<equiv> (always (\<lambda> r2 r1 . ((weak_previous (\<lambda> r4 r3 . (dual_since t (\<lambda> r6 r5 . (\<not> (A2 r5))) (\<lambda> r6 r5 . (\<not> (A1 r5))) r4 r3)) r2 r1) \<or> ((\<not> (A3 r1)) \<or> (A4 r2 r1)))) s)"

definition P6_1_part where "P6_1_part t A1 A2 A3 A4 s \<equiv> (P6_1 t A1 A2 A3 (\<lambda> s s1 . (A4 s1)) s)"

definition P6_1_inv where "P6_1_inv t b_0 t1_0 b_1 A1 A2 A3 A4_1 s \<equiv> (((always_inv (\<lambda> r2 r1 . ((weak_previous (\<lambda> r4 r3 . (dual_since t (\<lambda> r6 r5 . (\<not> (A2 r5))) (\<lambda> r6 r5 . (\<not> (A1 r5))) r4 r3)) r2 r1) \<or> ((\<not> (A3 r1)) \<or> (A4_1 r2 r1)))) s) \<and> (previous_inv b_1 (\<lambda> r4 r3 . (dual_since t (\<lambda> r6 r5 . (\<not> (A2 r5))) (\<lambda> r6 r5 . (\<not> (A1 r5))) r4 r3)) s)) \<and> (dual_since_inv t b_0 t1_0 (\<lambda> r6 r5 . (\<not> (A2 r5))) (\<lambda> r6 r5 . (\<not> (A1 r5))) s))"

definition P6_1_inv_part where "P6_1_inv_part t b_0 t1_0 b_1 A1 A2 A3 A4 s \<equiv> (P6_1_inv t b_0 t1_0 b_1 A1 A2 A3 (\<lambda> s s1 . (A4 s1)) s)"

lemma P6_1_inv_saving_gen: "
P6_1_inv t b_0 t1_0 b_1 A1 A2 A3 A4_1 s0 \<Longrightarrow>
consecutive s0 s \<Longrightarrow>
(((((True \<and> True) \<and> (True \<and> (always_imp s0 (\<lambda> r1 . (A4_1 s0 r1)) (\<lambda> r1 . (A4_1 s r1))))) \<and> (((b_1 s0) \<and> (True \<and> True)) \<or> ((\<not> (A3 s)) \<or> (A4_1 s s)))) \<and> ((b_1 s) --> (((t > 0) \<or> (\<not> (A1 s))) \<and> ((\<not> (A2 s)) \<or> ((b_0 s0) \<and> (True \<and> (True \<and> ((t1_0 s0) < t)))))))) \<and> ((((t1_0 s) > 0) \<or> (\<not> (A1 s))) \<and> ((\<not> (A2 s)) \<or> ((b_0 s0) \<and> (True \<and> (True \<and> ((t1_0 s0) < (t1_0 s)))))))) \<Longrightarrow>
P6_1_inv t b_0 t1_0 b_1 A1 A2 A3 A4_1 s"
unfolding P6_1_inv_def
apply(erule conjE)
apply(erule conjE)
subgoal premises prems1
apply(rule conjI)
apply(insert prems1(1,2,4))[1]
apply(erule conjE)
apply(erule conjE)
subgoal premises prems2
apply(rule conjI)
apply(insert prems2(1,2,4))[1]
apply(erule always_rule)
  apply simp
  apply(erule conjE)
  subgoal premises prems3
  apply(rule conjI)
  apply(insert prems3(1,2))[1]
    apply(rule always_disj_rule)
    apply simp
      apply(erule conjE)
      subgoal premises prems4
      apply(rule conjI)
      apply(insert prems4(1,2))[1]
        apply(rule weak_previous_LS4)
        apply simp
          apply(rule dual_since_L4)
          apply simp
            apply(erule conjE)
            subgoal premises prems5
            apply(rule conjI)
            apply(insert prems5(1,2))[1]
              apply(rule always_imp_refl)
            apply(insert prems5(1,3))
              apply(rule always_imp_refl)
            done
      apply(insert prems4(1,3))
        apply(rule always_disj_rule)
        apply simp
          apply(erule conjE)
          subgoal premises prems6
          apply(rule conjI)
          apply(insert prems6(1,2))[1]
            apply(rule always_imp_refl)
          apply(insert prems6(1,3))
            apply assumption
          done
      done
  apply(insert prems3(1,3))
    apply(erule disjE)
    apply(rule disjI1)
      apply(rule weak_previous_one_point[OF prems2(3)])
      apply simp
        apply(erule conjE)
        subgoal premises prems7
        apply(rule conjI)
        apply(insert prems7(1,2))[1]
          apply assumption
        apply(insert prems7(1,3))
          apply(rule dual_since_L4)
          apply simp
            apply(erule conjE)
            subgoal premises prems8
            apply(rule conjI)
            apply(insert prems8(1,2))[1]
              apply(rule always_imp_refl)
            apply(insert prems8(1,3))
              apply(rule always_imp_refl)
            done
        done
    apply(rule disjI2)
      apply(erule disjE)
      apply(rule disjI1)
        apply assumption
      apply(rule disjI2)
        apply assumption
  done
apply(insert prems2(1,3,5))
  apply(erule previous_rule)
  apply simp
  apply(rule impI)
  apply(erule impE)
  apply assumption
  subgoal premises prems9
  apply(insert prems9(1,3))
    apply(rule dual_since_L7[OF prems1(3)])
    apply simp
      apply(erule conjE)
      subgoal premises prems10
      apply(rule conjI)
      apply(insert prems10(1,2))[1]
        apply(erule disjE)
        apply(rule disjI1)
          apply assumption
        apply(rule disjI2)
          apply assumption
      apply(insert prems10(1,3))
        apply(erule disjE)
        apply(rule disjI1)
          apply assumption
        apply(rule disjI2)
          apply(erule conjE)
          subgoal premises prems11
          apply(rule conjI)
          apply(insert prems11(1,2))[1]
            apply assumption
          apply(insert prems11(1,3))
            apply(erule conjE)
            subgoal premises prems12
            apply(rule conjI)
            apply(insert prems12(1,2))[1]
              apply(rule always_imp_refl)
            apply(insert prems12(1,3))
              apply(erule conjE)
              subgoal premises prems13
              apply(rule conjI)
              apply(insert prems13(1,2))[1]
                apply(rule always_imp_refl)
              apply(insert prems13(1,3))
                apply assumption
              done
            done
          done
      done
  done
done
apply(insert prems1(1,3,5))
  apply(erule dual_since_one_point)
  apply simp
  apply(erule conjE)
  subgoal premises prems14
  apply(rule conjI)
  apply(insert prems14(1,2))[1]
    apply(erule disjE)
    apply(rule disjI1)
      apply assumption
    apply(rule disjI2)
      apply assumption
  apply(insert prems14(1,3))
    apply(erule disjE)
    apply(rule disjI1)
      apply assumption
    apply(rule disjI2)
      apply(erule conjE)
      subgoal premises prems15
      apply(rule conjI)
      apply(insert prems15(1,2))[1]
        apply assumption
      apply(insert prems15(1,3))
        apply(erule conjE)
        subgoal premises prems16
        apply(rule conjI)
        apply(insert prems16(1,2))[1]
          apply(rule always_imp_refl)
        apply(insert prems16(1,3))
          apply(erule conjE)
          subgoal premises prems17
          apply(rule conjI)
          apply(insert prems17(1,2))[1]
            apply(rule always_imp_refl)
          apply(insert prems17(1,3))
            apply assumption
          done
        done
      done
  done
done
done

lemma P6_1einv_imp_req_gen: "
P6_1_inv t b_0 t1_0 b_1 A1 A2 A3 A4_1 s0 \<Longrightarrow>
toEnvP s0 \<Longrightarrow>
((True \<and> True) \<and> (True \<and> (always_imp s0 (\<lambda> r1 . (A4_1 s0 r1)) (\<lambda> r1 . (A4 s0 r1))))) \<Longrightarrow>
P6_1 t A1 A2 A3 A4 s0"unfolding P6_1_inv_def P6_1_def
subgoal premises prems1
apply(insert prems1(1,2))
apply(simp only: conj_assoc)
apply(erule conjE)
subgoal premises prems2
apply(insert prems2(1,2) prems1(3))
apply(erule always_einv2req)
apply simp
  apply(rule always_disj_rule)
  apply simp
    apply(erule conjE)
    subgoal premises prems3
    apply(rule conjI)
    apply(insert prems3(1,2))[1]
      apply(rule weak_previous_LS5)
      apply simp
        apply(rule dual_since_L5)
        apply simp
          apply(erule conjE)
          subgoal premises prems4
          apply(rule conjI)
          apply(insert prems4(1,2))[1]
            apply(rule always_imp_refl)
          apply(insert prems4(1,3))
            apply(rule always_imp_refl)
          done
    apply(insert prems3(1,3))
      apply(rule always_disj_rule)
      apply simp
        apply(erule conjE)
        subgoal premises prems5
        apply(rule conjI)
        apply(insert prems5(1,2))[1]
          apply(rule always_imp_refl)
        apply(insert prems5(1,3))
          apply assumption
        done
    done
done
done
done

lemma P6_1_inv_saving: "
P6_1_inv_part t b_0 t1_0 b_1 A1 A2 A3 A4 s0 \<Longrightarrow>
consecutive s0 s \<Longrightarrow>
((((b_1 s0) \<or> ((\<not> (A3 s)) \<or> (A4 s))) \<and> ((b_1 s) --> (((t > 0) \<or> (\<not> (A1 s))) \<and> ((\<not> (A2 s)) \<or> ((b_0 s0) \<and> ((t1_0 s0) < t)))))) \<and> ((((t1_0 s) > 0) \<or> (\<not> (A1 s))) \<and> ((\<not> (A2 s)) \<or> ((b_0 s0) \<and> ((t1_0 s0) < (t1_0 s)))))) \<Longrightarrow>
P6_1_inv_part t b_0 t1_0 b_1 A1 A2 A3 A4 s"unfolding P6_1_inv_part_def P6_1_part_def
apply(simp add: P6_1_inv_saving_gen always_imp_refl)
done

lemma P6_1einv_imp_req: "
P6_1_inv_part t b_0 t1_0 b_1 A1 A2 A3 A4 s \<Longrightarrow>
toEnvP s \<Longrightarrow>
True \<Longrightarrow>
P6_1_part t A1 A2 A3 A4 s"unfolding P6_1_inv_part_def P6_1_part_def
apply(simp add: P6_1einv_imp_req_gen always_imp_refl)
done

lemmas P6_1_used_patterns = P6_1_def always_def weak_previous_def dual_since_def 

lemmas P6_1_inv_used_patterns = P6_1_inv_def always_inv_def weak_previous_def dual_since_def previous_inv_def dual_since_def dual_since_inv_def 

lemmas P6_1_inv_part_used_patterns = P6_1_inv_part_def P6_1_inv_used_patterns

lemmas P6_1_part_used_patterns = P6_1_part_def P6_1_used_patterns

definition P6_2 where "P6_2 t A1 A2 A3 A4 A5 s \<equiv> (always (\<lambda> r2 r1 . ((weak_previous (\<lambda> r4 r3 . (dual_since t (\<lambda> r6 r5 . (\<not> (A2 r5))) (\<lambda> r6 r5 . (\<not> (A1 r5))) r4 r3)) r2 r1) \<or> ((\<not> (A3 r1)) \<or> (weak_until A4 A5 r2 r1)))) s)"

definition P6_2_part where "P6_2_part t A1 A2 A3 A4 A5 s \<equiv> (P6_2 t A1 A2 A3 (\<lambda> s s1 . (A4 s1)) (\<lambda> s s1 . (A5 s1)) s)"

definition P6_2_inv where "P6_2_inv t b_0 t1_0 b_1 w_0 A1 A2 A3 A4_1 A5_1 s \<equiv> (((always_inv (\<lambda> r2 r1 . ((weak_previous (\<lambda> r4 r3 . (dual_since t (\<lambda> r6 r5 . (\<not> (A2 r5))) (\<lambda> r6 r5 . (\<not> (A1 r5))) r4 r3)) r2 r1) \<or> ((\<not> (A3 r1)) \<or> (weak_until_inv w_0 A4_1 A5_1 r2 r1)))) s) \<and> (previous_inv b_1 (\<lambda> r4 r3 . (dual_since t (\<lambda> r6 r5 . (\<not> (A2 r5))) (\<lambda> r6 r5 . (\<not> (A1 r5))) r4 r3)) s)) \<and> (dual_since_inv t b_0 t1_0 (\<lambda> r6 r5 . (\<not> (A2 r5))) (\<lambda> r6 r5 . (\<not> (A1 r5))) s))"

definition P6_2_inv_part where "P6_2_inv_part t b_0 t1_0 b_1 w_0 A1 A2 A3 A4 A5 s \<equiv> (P6_2_inv t b_0 t1_0 b_1 w_0 A1 A2 A3 (\<lambda> s s1 . (A4 s1)) (\<lambda> s s1 . (A5 s1)) s)"

lemma P6_2_inv_saving_gen: "
P6_2_inv t b_0 t1_0 b_1 w_0 A1 A2 A3 A4_1 A5_1 s0 \<Longrightarrow>
consecutive s0 s \<Longrightarrow>
(((((True \<and> True) \<and> (True \<and> ((always_imp s0 (A4_1 s0) (A4_1 s)) \<and> ((always_imp s0 (A5_1 s0) (A5_1 s)) \<and> ((\<not> (w_0 s0)) \<or> ((A5_1 s s) \<or> ((w_0 s) \<and> (A4_1 s s)))))))) \<and> (((b_1 s0) \<and> (True \<and> True)) \<or> ((\<not> (A3 s)) \<or> ((A5_1 s s) \<or> ((w_0 s) \<and> (A4_1 s s)))))) \<and> ((b_1 s) --> (((t > 0) \<or> (\<not> (A1 s))) \<and> ((\<not> (A2 s)) \<or> ((b_0 s0) \<and> (True \<and> (True \<and> ((t1_0 s0) < t)))))))) \<and> ((((t1_0 s) > 0) \<or> (\<not> (A1 s))) \<and> ((\<not> (A2 s)) \<or> ((b_0 s0) \<and> (True \<and> (True \<and> ((t1_0 s0) < (t1_0 s)))))))) \<Longrightarrow>
P6_2_inv t b_0 t1_0 b_1 w_0 A1 A2 A3 A4_1 A5_1 s"
unfolding P6_2_inv_def
apply(erule conjE)
apply(erule conjE)
subgoal premises prems1
apply(rule conjI)
apply(insert prems1(1,2,4))[1]
apply(erule conjE)
apply(erule conjE)
subgoal premises prems2
apply(rule conjI)
apply(insert prems2(1,2,4))[1]
apply(erule always_rule)
  apply simp
  apply(erule conjE)
  subgoal premises prems3
  apply(rule conjI)
  apply(insert prems3(1,2))[1]
    apply(rule always_disj_rule)
    apply simp
      apply(erule conjE)
      subgoal premises prems4
      apply(rule conjI)
      apply(insert prems4(1,2))[1]
        apply(rule weak_previous_LS4)
        apply simp
          apply(rule dual_since_L4)
          apply simp
            apply(erule conjE)
            subgoal premises prems5
            apply(rule conjI)
            apply(insert prems5(1,2))[1]
              apply(rule always_imp_refl)
            apply(insert prems5(1,3))
              apply(rule always_imp_refl)
            done
      apply(insert prems4(1,3))
        apply(rule always_disj_rule)
        apply simp
          apply(erule conjE)
          subgoal premises prems6
          apply(rule conjI)
          apply(insert prems6(1,2))[1]
            apply(rule always_imp_refl)
          apply(insert prems6(1,3))
            apply(rule weak_until_rule)
            apply simp
              apply(erule conjE)
              subgoal premises prems7
              apply(rule conjI)
              apply(insert prems7(1,2))[1]
                apply assumption
              apply(insert prems7(1,3))
                apply(erule conjE)
                subgoal premises prems8
                apply(rule conjI)
                apply(insert prems8(1,2))[1]
                  apply assumption
                apply(insert prems8(1,3))
                  apply(erule disjE)
                  apply(rule disjI1)
                    apply assumption
                  apply(rule disjI2)
                    apply(erule disjE)
                    apply(rule disjI1)
                      apply assumption
                    apply(rule disjI2)
                      apply(erule conjE)
                      subgoal premises prems9
                      apply(rule conjI)
                      apply(insert prems9(1,2))[1]
                        apply assumption
                      apply(insert prems9(1,3))
                        apply assumption
                      done
                done
              done
          done
      done
  apply(insert prems3(1,3))
    apply(erule disjE)
    apply(rule disjI1)
      apply(rule weak_previous_one_point[OF prems2(3)])
      apply simp
        apply(erule conjE)
        subgoal premises prems10
        apply(rule conjI)
        apply(insert prems10(1,2))[1]
          apply assumption
        apply(insert prems10(1,3))
          apply(rule dual_since_L4)
          apply simp
            apply(erule conjE)
            subgoal premises prems11
            apply(rule conjI)
            apply(insert prems11(1,2))[1]
              apply(rule always_imp_refl)
            apply(insert prems11(1,3))
              apply(rule always_imp_refl)
            done
        done
    apply(rule disjI2)
      apply(erule disjE)
      apply(rule disjI1)
        apply assumption
      apply(rule disjI2)
        apply(rule weak_until_one_point)
        apply simp
          apply(erule disjE)
          apply(rule disjI1)
            apply assumption
          apply(rule disjI2)
            apply(erule conjE)
            subgoal premises prems12
            apply(rule conjI)
            apply(insert prems12(1,2))[1]
              apply assumption
            apply(insert prems12(1,3))
              apply assumption
            done
  done
apply(insert prems2(1,3,5))
  apply(erule previous_rule)
  apply simp
  apply(rule impI)
  apply(erule impE)
  apply assumption
  subgoal premises prems13
  apply(insert prems13(1,3))
    apply(rule dual_since_L7[OF prems1(3)])
    apply simp
      apply(erule conjE)
      subgoal premises prems14
      apply(rule conjI)
      apply(insert prems14(1,2))[1]
        apply(erule disjE)
        apply(rule disjI1)
          apply assumption
        apply(rule disjI2)
          apply assumption
      apply(insert prems14(1,3))
        apply(erule disjE)
        apply(rule disjI1)
          apply assumption
        apply(rule disjI2)
          apply(erule conjE)
          subgoal premises prems15
          apply(rule conjI)
          apply(insert prems15(1,2))[1]
            apply assumption
          apply(insert prems15(1,3))
            apply(erule conjE)
            subgoal premises prems16
            apply(rule conjI)
            apply(insert prems16(1,2))[1]
              apply(rule always_imp_refl)
            apply(insert prems16(1,3))
              apply(erule conjE)
              subgoal premises prems17
              apply(rule conjI)
              apply(insert prems17(1,2))[1]
                apply(rule always_imp_refl)
              apply(insert prems17(1,3))
                apply assumption
              done
            done
          done
      done
  done
done
apply(insert prems1(1,3,5))
  apply(erule dual_since_one_point)
  apply simp
  apply(erule conjE)
  subgoal premises prems18
  apply(rule conjI)
  apply(insert prems18(1,2))[1]
    apply(erule disjE)
    apply(rule disjI1)
      apply assumption
    apply(rule disjI2)
      apply assumption
  apply(insert prems18(1,3))
    apply(erule disjE)
    apply(rule disjI1)
      apply assumption
    apply(rule disjI2)
      apply(erule conjE)
      subgoal premises prems19
      apply(rule conjI)
      apply(insert prems19(1,2))[1]
        apply assumption
      apply(insert prems19(1,3))
        apply(erule conjE)
        subgoal premises prems20
        apply(rule conjI)
        apply(insert prems20(1,2))[1]
          apply(rule always_imp_refl)
        apply(insert prems20(1,3))
          apply(erule conjE)
          subgoal premises prems21
          apply(rule conjI)
          apply(insert prems21(1,2))[1]
            apply(rule always_imp_refl)
          apply(insert prems21(1,3))
            apply assumption
          done
        done
      done
  done
done
done

lemma P6_2einv_imp_req_gen: "
P6_2_inv t b_0 t1_0 b_1 w_0 A1 A2 A3 A4_1 A5_1 s0 \<Longrightarrow>
toEnvP s0 \<Longrightarrow>
((True \<and> True) \<and> (True \<and> ((always_imp s0 (A4_1 s0) (A4 s0)) \<and> (always_imp s0 (A5_1 s0) (A5 s0))))) \<Longrightarrow>
P6_2 t A1 A2 A3 A4 A5 s0"unfolding P6_2_inv_def P6_2_def
subgoal premises prems1
apply(insert prems1(1,2))
apply(simp only: conj_assoc)
apply(erule conjE)
subgoal premises prems2
apply(insert prems2(1,2) prems1(3))
apply(erule always_einv2req)
apply simp
  apply(rule always_disj_rule)
  apply simp
    apply(erule conjE)
    subgoal premises prems3
    apply(rule conjI)
    apply(insert prems3(1,2))[1]
      apply(rule weak_previous_LS5)
      apply simp
        apply(rule dual_since_L5)
        apply simp
          apply(erule conjE)
          subgoal premises prems4
          apply(rule conjI)
          apply(insert prems4(1,2))[1]
            apply(rule always_imp_refl)
          apply(insert prems4(1,3))
            apply(rule always_imp_refl)
          done
    apply(insert prems3(1,3))
      apply(rule always_disj_rule)
      apply simp
        apply(erule conjE)
        subgoal premises prems5
        apply(rule conjI)
        apply(insert prems5(1,2))[1]
          apply(rule always_imp_refl)
        apply(insert prems5(1,3))
          apply(rule weak_until_einv2req)
          apply simp
            apply(erule conjE)
            subgoal premises prems6
            apply(rule conjI)
            apply(insert prems6(1,2))[1]
              apply assumption
            apply(insert prems6(1,3))
              apply assumption
            done
        done
    done
done
done
done

lemma P6_2_inv_saving: "
P6_2_inv_part t b_0 t1_0 b_1 w_0 A1 A2 A3 A4 A5 s0 \<Longrightarrow>
consecutive s0 s \<Longrightarrow>
(((((\<not> (w_0 s0)) \<or> ((A5 s) \<or> ((w_0 s) \<and> (A4 s)))) \<and> ((b_1 s0) \<or> ((\<not> (A3 s)) \<or> ((A5 s) \<or> ((w_0 s) \<and> (A4 s)))))) \<and> ((b_1 s) --> (((t > 0) \<or> (\<not> (A1 s))) \<and> ((\<not> (A2 s)) \<or> ((b_0 s0) \<and> ((t1_0 s0) < t)))))) \<and> ((((t1_0 s) > 0) \<or> (\<not> (A1 s))) \<and> ((\<not> (A2 s)) \<or> ((b_0 s0) \<and> ((t1_0 s0) < (t1_0 s)))))) \<Longrightarrow>
P6_2_inv_part t b_0 t1_0 b_1 w_0 A1 A2 A3 A4 A5 s"unfolding P6_2_inv_part_def P6_2_part_def
apply(simp add: P6_2_inv_saving_gen always_imp_refl)
done

lemma P6_2einv_imp_req: "
P6_2_inv_part t b_0 t1_0 b_1 w_0 A1 A2 A3 A4 A5 s \<Longrightarrow>
toEnvP s \<Longrightarrow>
True \<Longrightarrow>
P6_2_part t A1 A2 A3 A4 A5 s"unfolding P6_2_inv_part_def P6_2_part_def
apply(simp add: P6_2einv_imp_req_gen always_imp_refl)
done

lemmas P6_2_used_patterns = P6_2_def always_def weak_previous_def dual_since_def weak_until_def 

lemmas P6_2_inv_used_patterns = P6_2_inv_def always_inv_def weak_previous_def dual_since_def weak_until_inv_def previous_inv_def dual_since_def dual_since_inv_def 

lemmas P6_2_inv_part_used_patterns = P6_2_inv_part_def P6_2_inv_used_patterns

lemmas P6_2_part_used_patterns = P6_2_part_def P6_2_used_patterns

end
