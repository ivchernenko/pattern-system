theory Ex_Derived_Patterns imports Lib Derived_Patterns 
begin
definition P_constrained_always_after_max_delay where "P_constrained_always_after_max_delay t1 t2 A11 A12 A2 A3 s \<equiv> (P1_2 t1 A11 A12 (\<lambda> r2 r1 . (\<not> (A2 r1))) (\<lambda> r2 r1 . ((A2 r1) \<and> (constrained_always t2 A3 r2 r1))) s)"

definition P_constrained_always_after_max_delay_part where "P_constrained_always_after_max_delay_part t1 t2 A11 A12 A2 A3 s \<equiv> (P_constrained_always_after_max_delay t1 t2 A11 A12 A2 (\<lambda> s s1 . (A3 s1)) s)"

definition P_constrained_always_after_max_delay_inv where "P_constrained_always_after_max_delay_inv t1 t2 t1_0 b_0_0 t1_0_0 A11 A12 A2 A3_1 s \<equiv> (P1_2_inv t1 b_0_0 t1_0_0 A11 A12 (\<lambda> r2 r1 . (\<not> (A2 r1))) (\<lambda> r2 r1 . ((A2 r1) \<and> (constrained_always_inv t2 t1_0 A3_1 r2 r1))) s)"

definition P_constrained_always_after_max_delay_inv_part where "P_constrained_always_after_max_delay_inv_part t1 t2 t1_0 b_0_0 t1_0_0 A11 A12 A2 A3 s \<equiv> (P_constrained_always_after_max_delay_inv t1 t2 t1_0 b_0_0 t1_0_0 A11 A12 A2 (\<lambda> s s1 . (A3 s1)) s)"

lemma P_constrained_always_after_max_delay_inv_saving_gen: "
P_constrained_always_after_max_delay_inv t1 t2 t1_0 b_0_0 t1_0_0 A11 A12 A2 A3_1 s0 \<Longrightarrow>
consecutive s0 s \<Longrightarrow>
(((True \<and> (True \<and> (True \<and> ((True \<and> ((t2 = 0) \<or> ((always_imp s0 (A3_1 s0) (A3_1 s)) \<and> (((((t1_0 s0) + 1) >= t2) \<or> (A3_1 s s)) \<and> ((t1_0 s) <= ((t1_0 s0) + 1)))))) \<and> (((t1_0_0 s0) = 0) \<or> ((((A2 s) \<and> ((t2 = 0) \<or> (((t1_0 s) = 0) \<and> (A3_1 s s)))) \<and> ((t1_0_0 s0) <= t1)) \<or> ((\<not> (A2 s)) \<and> ((t1_0_0 s0) < (t1_0_0 s))))))))) \<and> (((b_0_0 s0) \<and> True) \<or> ((\<not> (A12 s)) \<or> (((A2 s) \<and> ((t2 = 0) \<or> (((t1_0 s) = 0) \<and> (A3_1 s s)))) \<or> ((\<not> (A2 s)) \<and> ((t1_0_0 s) > 0)))))) \<and> ((b_0_0 s) --> (\<not> (A11 s)))) \<Longrightarrow>
P_constrained_always_after_max_delay_inv t1 t2 t1_0 b_0_0 t1_0_0 A11 A12 A2 A3_1 s"
unfolding P_constrained_always_after_max_delay_inv_def
apply(erule P1_2_inv_saving_gen)
  apply simp
  apply(erule conjE)
  subgoal premises prems1
  apply(rule conjI)
  apply(insert prems1(1,2))[1]
    apply(erule conjE)
    subgoal premises prems2
    apply(rule conjI)
    apply(insert prems2(1,2))[1]
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
          apply(erule conjE)
          subgoal premises prems5
          apply(rule conjI)
          apply(insert prems5(1,2))[1]
            apply(rule always_imp_refl)
          apply(insert prems5(1,3))
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
                  apply(rule always_imp_refl)
                apply(insert prems7(1,3))
                  apply(rule constrained_always_rule)
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
                        apply(erule conjE)
                        subgoal premises prems9
                        apply(rule conjI)
                        apply(insert prems9(1,2))[1]
                          apply(erule disjE)
                          apply(rule disjI1)
                            apply assumption
                          apply(rule disjI2)
                            apply assumption
                        apply(insert prems9(1,3))
                          apply assumption
                        done
                      done
                done
            apply(insert prems6(1,3))
              apply(erule disjE)
              apply(rule disjI1)
                apply assumption
              apply(rule disjI2)
                apply(erule disjE)
                apply(rule disjI1)
                  apply(erule conjE)
                  subgoal premises prems10
                  apply(rule conjI)
                  apply(insert prems10(1,2))[1]
                    apply(erule conjE)
                    subgoal premises prems11
                    apply(rule conjI)
                    apply(insert prems11(1,2))[1]
                      apply assumption
                    apply(insert prems11(1,3))
                      apply(rule constrained_always_one_point)
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
                  apply(insert prems10(1,3))
                    apply assumption
                  done
                apply(rule disjI2)
                  apply(erule conjE)
                  subgoal premises prems13
                  apply(rule conjI)
                  apply(insert prems13(1,2))[1]
                    apply assumption
                  apply(insert prems13(1,3))
                    apply assumption
                  done
            done
          done
        done
      done
    apply(insert prems2(1,3))
      apply(erule disjE)
      apply(rule disjI1)
        apply(erule conjE)
        subgoal premises prems14
        apply(rule conjI)
        apply(insert prems14(1,2))[1]
          apply assumption
        apply(insert prems14(1,3))
          apply assumption
        done
      apply(rule disjI2)
        apply(erule disjE)
        apply(rule disjI1)
          apply assumption
        apply(rule disjI2)
          apply(erule disjE)
          apply(rule disjI1)
            apply(erule conjE)
            subgoal premises prems15
            apply(rule conjI)
            apply(insert prems15(1,2))[1]
              apply assumption
            apply(insert prems15(1,3))
              apply(rule constrained_always_one_point)
              apply simp
                apply(erule disjE)
                apply(rule disjI1)
                  apply assumption
                apply(rule disjI2)
                  apply(erule conjE)
                  subgoal premises prems16
                  apply(rule conjI)
                  apply(insert prems16(1,2))[1]
                    apply assumption
                  apply(insert prems16(1,3))
                    apply assumption
                  done
            done
          apply(rule disjI2)
            apply(erule conjE)
            subgoal premises prems17
            apply(rule conjI)
            apply(insert prems17(1,2))[1]
              apply assumption
            apply(insert prems17(1,3))
              apply assumption
            done
    done
  apply(insert prems1(1,3))
    apply(rule impI)
    apply(erule impE)
    apply assumption
    subgoal premises prems18
    apply(insert prems18(1,3))
      apply assumption
    done
  done
done

lemma P_constrained_always_after_max_delayeinv_imp_req_gen: "
P_constrained_always_after_max_delay_inv t1 t2 t1_0 b_0_0 t1_0_0 A11 A12 A2 A3_1 s0 \<Longrightarrow>
toEnvP s0 \<Longrightarrow>
(True \<and> (True \<and> (True \<and> ((True \<and> (always_imp s0 (A3_1 s0) (A3 s0))) \<and> ((t1_0_0 s0) <= t1))))) \<Longrightarrow>
P_constrained_always_after_max_delay t1 t2 A11 A12 A2 A3 s0"unfolding P_constrained_always_after_max_delay_inv_def P_constrained_always_after_max_delay_def
apply(erule P1_2einv_imp_req_gen)
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
      apply(erule conjE)
      subgoal premises prems5
      apply(rule conjI)
      apply(insert prems5(1,2))[1]
        apply(rule always_imp_refl)
      apply(insert prems5(1,3))
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
              apply(rule always_imp_refl)
            apply(insert prems7(1,3))
              apply(rule constrained_always_einv2req)
              apply simp
                apply assumption
            done
        apply(insert prems6(1,3))
          apply assumption
        done
      done
    done
  done
done

lemma P_constrained_always_after_max_delay_inv_saving: "
P_constrained_always_after_max_delay_inv_part t1 t2 t1_0 b_0_0 t1_0_0 A11 A12 A2 A3 s0 \<Longrightarrow>
consecutive s0 s \<Longrightarrow>
(((((t2 = 0) \<or> (((((t1_0 s0) + 1) >= t2) \<or> (A3 s)) \<and> ((t1_0 s) <= ((t1_0 s0) + 1)))) \<and> (((t1_0_0 s0) = 0) \<or> ((((A2 s) \<and> ((t2 = 0) \<or> (((t1_0 s) = 0) \<and> (A3 s)))) \<and> ((t1_0_0 s0) <= t1)) \<or> ((\<not> (A2 s)) \<and> ((t1_0_0 s0) < (t1_0_0 s)))))) \<and> ((b_0_0 s0) \<or> ((\<not> (A12 s)) \<or> (((A2 s) \<and> ((t2 = 0) \<or> (((t1_0 s) = 0) \<and> (A3 s)))) \<or> ((\<not> (A2 s)) \<and> ((t1_0_0 s) > 0)))))) \<and> ((b_0_0 s) --> (\<not> (A11 s)))) \<Longrightarrow>
P_constrained_always_after_max_delay_inv_part t1 t2 t1_0 b_0_0 t1_0_0 A11 A12 A2 A3 s"unfolding P_constrained_always_after_max_delay_inv_part_def P_constrained_always_after_max_delay_part_def
apply(simp add: P_constrained_always_after_max_delay_inv_saving_gen always_imp_refl)
done

lemma P_constrained_always_after_max_delayeinv_imp_req: "
P_constrained_always_after_max_delay_inv_part t1 t2 t1_0 b_0_0 t1_0_0 A11 A12 A2 A3 s \<Longrightarrow>
toEnvP s \<Longrightarrow>
((t1_0_0 s) <= t1) \<Longrightarrow>
P_constrained_always_after_max_delay_part t1 t2 A11 A12 A2 A3 s"unfolding P_constrained_always_after_max_delay_inv_part_def P_constrained_always_after_max_delay_part_def
apply(simp add: P_constrained_always_after_max_delayeinv_imp_req_gen always_imp_refl)
done

lemmas P_constrained_always_after_max_delay_used_patterns = P_constrained_always_after_max_delay_def P1_2_def constrained_always_def 

lemmas P_constrained_always_after_max_delay_inv_used_patterns = P_constrained_always_after_max_delay_inv_def P1_2_inv_def constrained_always_inv_def 

lemmas P_constrained_always_after_max_delay_inv_part_used_patterns = P_constrained_always_after_max_delay_inv_part_def P_constrained_always_after_max_delay_inv_used_patterns

lemmas P_constrained_always_after_max_delay_part_used_patterns = P_constrained_always_after_max_delay_part_def P_constrained_always_after_max_delay_used_patterns

definition P5 where "P5 A11 A12 A2 A3 A4 s \<equiv> (P3_4 A11 A12 (\<lambda> r2 r1 . (\<not> (A2 r1))) (\<lambda> r2 r1 . (((A2 r1) \<and> (A4 r2 r1)) \<or> (A3 r2 r1))) s)"

definition P5_part where "P5_part A11 A12 A2 A3 A4 s \<equiv> (P5 A11 A12 A2 (\<lambda> s s1 . (A3 s1)) (\<lambda> s s1 . (A4 s1)) s)"

definition P5_inv where "P5_inv b_0_0 b_1_0 w_0_0 A11 A12 A2 A3_1 A4_1 s \<equiv> (P3_4_inv b_0_0 b_1_0 w_0_0 A11 A12 (\<lambda> r2 r1 . (\<not> (A2 r1))) (\<lambda> r2 r1 . (((A2 r1) \<and> (A4_1 r2 r1)) \<or> (A3_1 r2 r1))) s)"

definition P5_inv_part where "P5_inv_part b_0_0 b_1_0 w_0_0 A11 A12 A2 A3 A4 s \<equiv> (P5_inv b_0_0 b_1_0 w_0_0 A11 A12 A2 (\<lambda> s s1 . (A3 s1)) (\<lambda> s s1 . (A4 s1)) s)"

lemma P5_inv_saving_gen: "
P5_inv b_0_0 b_1_0 w_0_0 A11 A12 A2 A3_1 A4_1 s0 \<Longrightarrow>
consecutive s0 s \<Longrightarrow>
(((((True \<and> True) \<and> (True \<and> (((True \<and> (always_imp s0 (\<lambda> r1 . (A4_1 s0 r1)) (\<lambda> r1 . (A4_1 s r1)))) \<and> (always_imp s0 (\<lambda> r1 . (A3_1 s0 r1)) (\<lambda> r1 . (A3_1 s r1)))) \<and> ((\<not> (w_0_0 s0)) \<or> ((((A2 s) \<and> (A4_1 s s)) \<or> (A3_1 s s)) \<or> ((w_0_0 s) \<and> (\<not> (A2 s)))))))) \<and> (((b_1_0 s0) \<and> (True \<and> True)) \<or> ((((A2 s) \<and> (A4_1 s s)) \<or> (A3_1 s s)) \<or> ((w_0_0 s) \<and> (\<not> (A2 s)))))) \<and> ((b_1_0 s) --> (((b_0_0 s0) \<and> True) \<or> (\<not> (A12 s))))) \<and> ((b_0_0 s) --> (\<not> (A11 s)))) \<Longrightarrow>
P5_inv b_0_0 b_1_0 w_0_0 A11 A12 A2 A3_1 A4_1 s"
unfolding P5_inv_def
apply(erule P3_4_inv_saving_gen)
  apply simp
  apply(erule conjE)
  subgoal premises prems1
  apply(rule conjI)
  apply(insert prems1(1,2))[1]
    apply(erule conjE)
    subgoal premises prems2
    apply(rule conjI)
    apply(insert prems2(1,2))[1]
      apply(erule conjE)
      subgoal premises prems3
      apply(rule conjI)
      apply(insert prems3(1,2))[1]
        apply(erule conjE)
        subgoal premises prems4
        apply(rule conjI)
        apply(insert prems4(1,2))[1]
          apply(erule conjE)
          subgoal premises prems5
          apply(rule conjI)
          apply(insert prems5(1,2))[1]
            apply assumption
          apply(insert prems5(1,3))
            apply assumption
          done
        apply(insert prems4(1,3))
          apply(erule conjE)
          subgoal premises prems6
          apply(rule conjI)
          apply(insert prems6(1,2))[1]
            apply(rule always_imp_refl)
          apply(insert prems6(1,3))
            apply(erule conjE)
            subgoal premises prems7
            apply(rule conjI)
            apply(insert prems7(1,2))[1]
              apply(rule always_disj_rule)
              apply simp
                apply(erule conjE)
                subgoal premises prems8
                apply(rule conjI)
                apply(insert prems8(1,2))[1]
                  apply(rule always_conj_rule)
                  apply simp
                    apply(erule conjE)
                    subgoal premises prems9
                    apply(rule conjI)
                    apply(insert prems9(1,2))[1]
                      apply(rule always_imp_refl)
                    apply(insert prems9(1,3))
                      apply assumption
                    done
                apply(insert prems8(1,3))
                  apply assumption
                done
            apply(insert prems7(1,3))
              apply(erule disjE)
              apply(rule disjI1)
                apply assumption
              apply(rule disjI2)
                apply(erule disjE)
                apply(rule disjI1)
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
          done
        done
      apply(insert prems3(1,3))
        apply(erule disjE)
        apply(rule disjI1)
          apply(erule conjE)
          subgoal premises prems12
          apply(rule conjI)
          apply(insert prems12(1,2))[1]
            apply assumption
          apply(insert prems12(1,3))
            apply(erule conjE)
            subgoal premises prems13
            apply(rule conjI)
            apply(insert prems13(1,2))[1]
              apply assumption
            apply(insert prems13(1,3))
              apply assumption
            done
          done
        apply(rule disjI2)
          apply(erule disjE)
          apply(rule disjI1)
            apply(erule disjE)
            apply(rule disjI1)
              apply(erule conjE)
              subgoal premises prems14
              apply(rule conjI)
              apply(insert prems14(1,2))[1]
                apply assumption
              apply(insert prems14(1,3))
                apply assumption
              done
            apply(rule disjI2)
              apply assumption
          apply(rule disjI2)
            apply(erule conjE)
            subgoal premises prems15
            apply(rule conjI)
            apply(insert prems15(1,2))[1]
              apply assumption
            apply(insert prems15(1,3))
              apply assumption
            done
      done
    apply(insert prems2(1,3))
      apply(rule impI)
      apply(erule impE)
      apply assumption
      subgoal premises prems16
      apply(insert prems16(1,3))
        apply(erule disjE)
        apply(rule disjI1)
          apply(erule conjE)
          subgoal premises prems17
          apply(rule conjI)
          apply(insert prems17(1,2))[1]
            apply assumption
          apply(insert prems17(1,3))
            apply assumption
          done
        apply(rule disjI2)
          apply assumption
      done
    done
  apply(insert prems1(1,3))
    apply(rule impI)
    apply(erule impE)
    apply assumption
    subgoal premises prems18
    apply(insert prems18(1,3))
      apply assumption
    done
  done
done

lemma P5einv_imp_req_gen: "
P5_inv b_0_0 b_1_0 w_0_0 A11 A12 A2 A3_1 A4_1 s0 \<Longrightarrow>
toEnvP s0 \<Longrightarrow>
((True \<and> True) \<and> (True \<and> ((True \<and> (always_imp s0 (\<lambda> r1 . (A4_1 s0 r1)) (\<lambda> r1 . (A4 s0 r1)))) \<and> (always_imp s0 (\<lambda> r1 . (A3_1 s0 r1)) (\<lambda> r1 . (A3 s0 r1)))))) \<Longrightarrow>
P5 A11 A12 A2 A3 A4 s0"unfolding P5_inv_def P5_def
apply(erule P3_4einv_imp_req_gen)
apply simp
  apply(erule conjE)
  subgoal premises prems3
  apply(rule conjI)
  apply(insert prems3(1,2))[1]
    apply(erule conjE)
    subgoal premises prems4
    apply(rule conjI)
    apply(insert prems4(1,2))[1]
      apply assumption
    apply(insert prems4(1,3))
      apply assumption
    done
  apply(insert prems3(1,3))
    apply(erule conjE)
    subgoal premises prems5
    apply(rule conjI)
    apply(insert prems5(1,2))[1]
      apply(rule always_imp_refl)
    apply(insert prems5(1,3))
      apply(rule always_disj_rule)
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
              apply(rule always_imp_refl)
            apply(insert prems7(1,3))
              apply assumption
            done
        apply(insert prems6(1,3))
          apply assumption
        done
    done
  done
done

lemma P5_inv_saving: "
P5_inv_part b_0_0 b_1_0 w_0_0 A11 A12 A2 A3 A4 s0 \<Longrightarrow>
consecutive s0 s \<Longrightarrow>
(((((\<not> (w_0_0 s0)) \<or> ((((A2 s) \<and> (A4 s)) \<or> (A3 s)) \<or> ((w_0_0 s) \<and> (\<not> (A2 s))))) \<and> ((b_1_0 s0) \<or> ((((A2 s) \<and> (A4 s)) \<or> (A3 s)) \<or> ((w_0_0 s) \<and> (\<not> (A2 s)))))) \<and> ((b_1_0 s) --> ((b_0_0 s0) \<or> (\<not> (A12 s))))) \<and> ((b_0_0 s) --> (\<not> (A11 s)))) \<Longrightarrow>
P5_inv_part b_0_0 b_1_0 w_0_0 A11 A12 A2 A3 A4 s"unfolding P5_inv_part_def P5_part_def
apply(simp add: P5_inv_saving_gen always_imp_refl)
done

lemma P5einv_imp_req: "
P5_inv_part b_0_0 b_1_0 w_0_0 A11 A12 A2 A3 A4 s \<Longrightarrow>
toEnvP s \<Longrightarrow>
True \<Longrightarrow>
P5_part A11 A12 A2 A3 A4 s"unfolding P5_inv_part_def P5_part_def
apply(simp add: P5einv_imp_req_gen always_imp_refl)
done

lemmas P5_used_patterns = P5_def P3_4_def 

lemmas P5_inv_used_patterns = P5_inv_def P3_4_inv_def 

lemmas P5_inv_part_used_patterns = P5_inv_part_def P5_inv_used_patterns

lemmas P5_part_used_patterns = P5_part_def P5_used_patterns

end
