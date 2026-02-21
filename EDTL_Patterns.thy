theory EDTL_Patterns imports Basic_Patterns 
begin

definition EDTL_delay_true where "EDTL_delay_true trigger fin release Inv reaction s \<equiv> (always (\<lambda> r2 r1 . ((\<not> (trigger r1)) \<or> ((release r2 r1) \<or> (weak_until (\<lambda> r4 r3 . ((Inv r4 r3) \<and> (\<not> (fin r3)))) (\<lambda> r4 r3 . ((release r4 r3) \<or> ((fin r3) \<and> ((reaction r4 r3) \<and> (Inv r4 r3))))) r2 r1)))) s)"

definition EDTL_delay_true_part where "EDTL_delay_true_part trigger fin release Inv reaction s \<equiv> (EDTL_delay_true trigger fin (\<lambda> s s1 . (release s1)) (\<lambda> s s1 . (Inv s1)) (\<lambda> s s1 . (reaction s1)) s)"

definition EDTL_delay_true_inv where "EDTL_delay_true_inv w_0 trigger fin release_1 Inv_1 reaction_1 s \<equiv> (always_inv (\<lambda> r2 r1 . ((\<not> (trigger r1)) \<or> ((release_1 r2 r1) \<or> (weak_until_inv w_0 (\<lambda> r4 r3 . ((Inv_1 r4 r3) \<and> (\<not> (fin r3)))) (\<lambda> r4 r3 . ((release_1 r4 r3) \<or> ((fin r3) \<and> ((reaction_1 r4 r3) \<and> (Inv_1 r4 r3))))) r2 r1)))) s)"

definition EDTL_delay_true_inv_part where "EDTL_delay_true_inv_part w_0 trigger fin release Inv reaction s \<equiv> (EDTL_delay_true_inv w_0 trigger fin (\<lambda> s s1 . (release s1)) (\<lambda> s s1 . (Inv s1)) (\<lambda> s s1 . (reaction s1)) s)"

lemma EDTL_delay_true_inv_saving_gen: "
EDTL_delay_true_inv w_0 trigger fin release_1 Inv_1 reaction_1 s0 \<Longrightarrow>
consecutive s0 s \<Longrightarrow>
((True \<and> ((always_imp s0 (\<lambda> r1 . (release_1 s0 r1)) (\<lambda> r1 . (release_1 s r1))) \<and> (((always_imp s0 (\<lambda> r3 . (Inv_1 s0 r3)) (\<lambda> r3 . (Inv_1 s r3))) \<and> True) \<and> (((always_imp s0 (\<lambda> r3 . (release_1 s0 r3)) (\<lambda> r3 . (release_1 s r3))) \<and> (True \<and> ((always_imp s0 (\<lambda> r3 . (reaction_1 s0 r3)) (\<lambda> r3 . (reaction_1 s r3))) \<and> (always_imp s0 (\<lambda> r3 . (Inv_1 s0 r3)) (\<lambda> r3 . (Inv_1 s r3)))))) \<and> ((\<not> (w_0 s0)) \<or> (((release_1 s s) \<or> ((fin s) \<and> ((reaction_1 s s) \<and> (Inv_1 s s)))) \<or> ((w_0 s) \<and> ((Inv_1 s s) \<and> (\<not> (fin s)))))))))) \<and> ((\<not> (trigger s)) \<or> ((release_1 s s) \<or> (((release_1 s s) \<or> ((fin s) \<and> ((reaction_1 s s) \<and> (Inv_1 s s)))) \<or> ((w_0 s) \<and> ((Inv_1 s s) \<and> (\<not> (fin s)))))))) \<Longrightarrow>
EDTL_delay_true_inv w_0 trigger fin release_1 Inv_1 reaction_1 s"

unfolding EDTL_delay_true_inv_def
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
        apply(rule always_disj_rule)
        apply simp
          apply(erule conjE)
          subgoal premises prems3
          apply(rule conjI)
          apply(insert prems3(1,2))[1]
            apply simp
          apply(insert prems3(1,3))
            apply(rule weak_until_rule)
            apply simp
              apply(erule conjE)
              subgoal premises prems4
              apply(rule conjI)
              apply(insert prems4(1,2))[1]
                apply(rule always_conj_rule)
                apply simp
                  apply(erule conjE)
                  subgoal premises prems5
                  apply(rule conjI)
                  apply(insert prems5(1,2))[1]
                    apply simp
                  apply(insert prems5(1,3))
                    apply(rule always_imp_refl)
                  done
              apply(insert prems4(1,3))
                apply(erule conjE)
                subgoal premises prems6
                apply(rule conjI)
                apply(insert prems6(1,2))[1]
                  apply(rule always_disj_rule)
                  apply simp
                    apply(erule conjE)
                    subgoal premises prems7
                    apply(rule conjI)
                    apply(insert prems7(1,2))[1]
                      apply simp
                    apply(insert prems7(1,3))
                      apply(rule always_conj_rule)
                      apply simp
                        apply(erule conjE)
                        subgoal premises prems8
                        apply(rule conjI)
                        apply(insert prems8(1,2))[1]
                          apply(rule always_imp_refl)
                        apply(insert prems8(1,3))
                          apply(rule always_conj_rule)
                          apply simp
                            apply(erule conjE)
                            subgoal premises prems9
                            apply(rule conjI)
                            apply(insert prems9(1,2))[1]
                              apply simp
                            apply(insert prems9(1,3))
                              apply simp
                            done
                        done
                    done
                apply(insert prems6(1,3))
                  apply(erule disjE)
                  apply(rule disjI1)
                    apply simp
                  apply(rule disjI2)
                    apply(erule disjE)
                    apply(rule disjI1)
                      apply(erule disjE)
                      apply(rule disjI1)
                        apply simp
                      apply(rule disjI2)
                        apply(erule conjE)
                        subgoal premises prems10
                        apply(rule conjI)
                        apply(insert prems10(1,2))[1]
                          apply simp
                        apply(insert prems10(1,3))
                          apply(erule conjE)
                          subgoal premises prems11
                          apply(rule conjI)
                          apply(insert prems11(1,2))[1]
                            apply simp
                          apply(insert prems11(1,3))
                            apply simp
                          done
                        done
                    apply(rule disjI2)
                      apply(erule conjE)
                      subgoal premises prems12
                      apply(rule conjI)
                      apply(insert prems12(1,2))[1]
                        apply simp
                      apply(insert prems12(1,3))
                        apply(erule conjE)
                        subgoal premises prems13
                        apply(rule conjI)
                        apply(insert prems13(1,2))[1]
                          apply simp
                        apply(insert prems13(1,3))
                          apply simp
                        done
                      done
                done
              done
          done
      done
  apply(insert prems1(1,3))
    apply(erule disjE)
    apply(rule disjI1)
      apply simp
    apply(rule disjI2)
      apply(erule disjE)
      apply(rule disjI1)
        apply simp
      apply(rule disjI2)
        apply(rule weak_until_one_point)
        apply simp
          apply(erule disjE)
          apply(rule disjI1)
            apply(erule disjE)
            apply(rule disjI1)
              apply simp
            apply(rule disjI2)
              apply(erule conjE)
              subgoal premises prems14
              apply(rule conjI)
              apply(insert prems14(1,2))[1]
                apply simp
              apply(insert prems14(1,3))
                apply(erule conjE)
                subgoal premises prems15
                apply(rule conjI)
                apply(insert prems15(1,2))[1]
                  apply simp
                apply(insert prems15(1,3))
                  apply simp
                done
              done
          apply(rule disjI2)
            apply(erule conjE)
            subgoal premises prems16
            apply(rule conjI)
            apply(insert prems16(1,2))[1]
              apply simp
            apply(insert prems16(1,3))
              apply(erule conjE)
              subgoal premises prems17
              apply(rule conjI)
              apply(insert prems17(1,2))[1]
                apply simp
              apply(insert prems17(1,3))
                apply simp
              done
            done
  done
done

lemma EDTL_delay_trueeinv_imp_req_gen: "
EDTL_delay_true_inv w_0 trigger fin release_1 Inv_1 reaction_1 s0 \<Longrightarrow>
toEnvP s0 \<Longrightarrow>
(True \<and> ((always_imp s0 (\<lambda> r1 . (release_1 s0 r1)) (\<lambda> r1 . (release s0 r1))) \<and> (((always_imp s0 (\<lambda> r3 . (Inv_1 s0 r3)) (\<lambda> r3 . (Inv s0 r3))) \<and> True) \<and> ((always_imp s0 (\<lambda> r3 . (release_1 s0 r3)) (\<lambda> r3 . (release s0 r3))) \<and> (True \<and> ((always_imp s0 (\<lambda> r3 . (reaction_1 s0 r3)) (\<lambda> r3 . (reaction s0 r3))) \<and> (always_imp s0 (\<lambda> r3 . (Inv_1 s0 r3)) (\<lambda> r3 . (Inv s0 r3))))))))) \<Longrightarrow>
EDTL_delay_true trigger fin release Inv reaction s0"

unfolding EDTL_delay_true_inv_def EDTL_delay_true_def
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
      apply(rule always_disj_rule)
      apply simp
        apply(erule conjE)
        subgoal premises prems4
        apply(rule conjI)
        apply(insert prems4(1,2))[1]
          apply simp
        apply(insert prems4(1,3))
          apply(rule weak_until_einv2req)
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
                  apply simp
                apply(insert prems6(1,3))
                  apply(rule always_imp_refl)
                done
            apply(insert prems5(1,3))
              apply(rule always_disj_rule)
              apply simp
                apply(erule conjE)
                subgoal premises prems7
                apply(rule conjI)
                apply(insert prems7(1,2))[1]
                  apply simp
                apply(insert prems7(1,3))
                  apply(rule always_conj_rule)
                  apply simp
                    apply(erule conjE)
                    subgoal premises prems8
                    apply(rule conjI)
                    apply(insert prems8(1,2))[1]
                      apply(rule always_imp_refl)
                    apply(insert prems8(1,3))
                      apply(rule always_conj_rule)
                      apply simp
                        apply(erule conjE)
                        subgoal premises prems9
                        apply(rule conjI)
                        apply(insert prems9(1,2))[1]
                          apply simp
                        apply(insert prems9(1,3))
                          apply simp
                        done
                    done
                done
            done
        done
    done
done

lemma EDTL_delay_true_inv_saving: "
EDTL_delay_true_inv_part w_0 trigger fin release Inv reaction s0 \<Longrightarrow>
consecutive s0 s \<Longrightarrow>
(((\<not> (w_0 s0)) \<or> (((release s) \<or> ((fin s) \<and> ((reaction s) \<and> (Inv s)))) \<or> ((w_0 s) \<and> ((Inv s) \<and> (\<not> (fin s)))))) \<and> ((\<not> (trigger s)) \<or> ((release s) \<or> (((release s) \<or> ((fin s) \<and> ((reaction s) \<and> (Inv s)))) \<or> ((w_0 s) \<and> ((Inv s) \<and> (\<not> (fin s)))))))) \<Longrightarrow>
EDTL_delay_true_inv_part w_0 trigger fin release Inv reaction s"

unfolding EDTL_delay_true_inv_part_def EDTL_delay_true_part_def
apply(simp add: EDTL_delay_true_inv_saving_gen always_imp_refl)
done

lemma EDTL_delay_trueeinv_imp_req: "
EDTL_delay_true_inv_part w_0 trigger fin release Inv reaction s \<Longrightarrow>
toEnvP s \<Longrightarrow>
True \<Longrightarrow>
EDTL_delay_true_part trigger fin release Inv reaction s"

unfolding EDTL_delay_true_inv_part_def EDTL_delay_true_part_def
apply(simp add: EDTL_delay_trueeinv_imp_req_gen always_imp_refl)
done



lemmas EDTL_delay_true_used_patterns = EDTL_delay_true_def always_used_patterns weak_until_def 

lemmas EDTL_delay_true_inv_used_patterns = EDTL_delay_true_inv_def always_inv_used_patterns weak_until_inv_def 

lemmas EDTL_delay_true_inv_part_used_patterns = EDTL_delay_true_inv_part_def EDTL_delay_true_inv_used_patterns

lemmas EDTL_delay_true_part_used_patterns = EDTL_delay_true_part_def EDTL_delay_true_used_patterns

definition EDTL_trigger_prev_delay_true where "EDTL_trigger_prev_delay_true trigger fin release Inv reaction s \<equiv> (always (\<lambda> r2 r1 . ((weak_previous (\<lambda> r4 r3 . (\<not> (trigger r3))) r2 r1) \<or> ((release r2 r1) \<or> (weak_until (\<lambda> r4 r3 . ((Inv r4 r3) \<and> (\<not> (fin r3)))) (\<lambda> r4 r3 . ((release r4 r3) \<or> ((fin r3) \<and> ((reaction r4 r3) \<and> (Inv r4 r3))))) r2 r1)))) s)"

definition EDTL_trigger_prev_delay_true_part where "EDTL_trigger_prev_delay_true_part trigger fin release Inv reaction s \<equiv> (EDTL_trigger_prev_delay_true trigger fin (\<lambda> s s1 . (release s1)) (\<lambda> s s1 . (Inv s1)) (\<lambda> s s1 . (reaction s1)) s)"

definition EDTL_trigger_prev_delay_true_inv where "EDTL_trigger_prev_delay_true_inv b_0 w_0 trigger fin release_1 Inv_1 reaction_1 s \<equiv> ((always_inv (\<lambda> r2 r1 . ((weak_previous (\<lambda> r4 r3 . (\<not> (trigger r3))) r2 r1) \<or> ((release_1 r2 r1) \<or> (weak_until_inv w_0 (\<lambda> r4 r3 . ((Inv_1 r4 r3) \<and> (\<not> (fin r3)))) (\<lambda> r4 r3 . ((release_1 r4 r3) \<or> ((fin r3) \<and> ((reaction_1 r4 r3) \<and> (Inv_1 r4 r3))))) r2 r1)))) s) \<and> (previous_inv b_0 (\<lambda> r4 r3 . (\<not> (trigger r3))) s))"

definition EDTL_trigger_prev_delay_true_inv_part where "EDTL_trigger_prev_delay_true_inv_part b_0 w_0 trigger fin release Inv reaction s \<equiv> (EDTL_trigger_prev_delay_true_inv b_0 w_0 trigger fin (\<lambda> s s1 . (release s1)) (\<lambda> s s1 . (Inv s1)) (\<lambda> s s1 . (reaction s1)) s)"

lemma EDTL_trigger_prev_delay_true_inv_saving_gen: "
EDTL_trigger_prev_delay_true_inv b_0 w_0 trigger fin release_1 Inv_1 reaction_1 s0 \<Longrightarrow>
consecutive s0 s \<Longrightarrow>
(((True \<and> ((always_imp s0 (\<lambda> r1 . (release_1 s0 r1)) (\<lambda> r1 . (release_1 s r1))) \<and> (((always_imp s0 (\<lambda> r3 . (Inv_1 s0 r3)) (\<lambda> r3 . (Inv_1 s r3))) \<and> True) \<and> (((always_imp s0 (\<lambda> r3 . (release_1 s0 r3)) (\<lambda> r3 . (release_1 s r3))) \<and> (True \<and> ((always_imp s0 (\<lambda> r3 . (reaction_1 s0 r3)) (\<lambda> r3 . (reaction_1 s r3))) \<and> (always_imp s0 (\<lambda> r3 . (Inv_1 s0 r3)) (\<lambda> r3 . (Inv_1 s r3)))))) \<and> ((\<not> (w_0 s0)) \<or> (((release_1 s s) \<or> ((fin s) \<and> ((reaction_1 s s) \<and> (Inv_1 s s)))) \<or> ((w_0 s) \<and> ((Inv_1 s s) \<and> (\<not> (fin s)))))))))) \<and> (((b_0 s0) \<and> True) \<or> ((release_1 s s) \<or> (((release_1 s s) \<or> ((fin s) \<and> ((reaction_1 s s) \<and> (Inv_1 s s)))) \<or> ((w_0 s) \<and> ((Inv_1 s s) \<and> (\<not> (fin s)))))))) \<and> ((b_0 s) --> (\<not> (trigger s)))) \<Longrightarrow>
EDTL_trigger_prev_delay_true_inv b_0 w_0 trigger fin release_1 Inv_1 reaction_1 s"

unfolding EDTL_trigger_prev_delay_true_inv_def
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
            apply simp
          apply(insert prems4(1,3))
            apply(rule weak_until_rule)
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
                    apply simp
                  apply(insert prems6(1,3))
                    apply(rule always_imp_refl)
                  done
              apply(insert prems5(1,3))
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
                      apply simp
                    apply(insert prems8(1,3))
                      apply(rule always_conj_rule)
                      apply simp
                        apply(erule conjE)
                        subgoal premises prems9
                        apply(rule conjI)
                        apply(insert prems9(1,2))[1]
                          apply(rule always_imp_refl)
                        apply(insert prems9(1,3))
                          apply(rule always_conj_rule)
                          apply simp
                            apply(erule conjE)
                            subgoal premises prems10
                            apply(rule conjI)
                            apply(insert prems10(1,2))[1]
                              apply simp
                            apply(insert prems10(1,3))
                              apply simp
                            done
                        done
                    done
                apply(insert prems7(1,3))
                  apply(erule disjE)
                  apply(rule disjI1)
                    apply simp
                  apply(rule disjI2)
                    apply(erule disjE)
                    apply(rule disjI1)
                      apply(erule disjE)
                      apply(rule disjI1)
                        apply simp
                      apply(rule disjI2)
                        apply(erule conjE)
                        subgoal premises prems11
                        apply(rule conjI)
                        apply(insert prems11(1,2))[1]
                          apply simp
                        apply(insert prems11(1,3))
                          apply(erule conjE)
                          subgoal premises prems12
                          apply(rule conjI)
                          apply(insert prems12(1,2))[1]
                            apply simp
                          apply(insert prems12(1,3))
                            apply simp
                          done
                        done
                    apply(rule disjI2)
                      apply(erule conjE)
                      subgoal premises prems13
                      apply(rule conjI)
                      apply(insert prems13(1,2))[1]
                        apply simp
                      apply(insert prems13(1,3))
                        apply(erule conjE)
                        subgoal premises prems14
                        apply(rule conjI)
                        apply(insert prems14(1,2))[1]
                          apply simp
                        apply(insert prems14(1,3))
                          apply simp
                        done
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
        subgoal premises prems15
        apply(rule conjI)
        apply(insert prems15(1,2))[1]
          apply simp
        apply(insert prems15(1,3))
          apply(rule always_imp_refl)
        done
    apply(rule disjI2)
      apply(erule disjE)
      apply(rule disjI1)
        apply simp
      apply(rule disjI2)
        apply(rule weak_until_one_point)
        apply simp
          apply(erule disjE)
          apply(rule disjI1)
            apply(erule disjE)
            apply(rule disjI1)
              apply simp
            apply(rule disjI2)
              apply(erule conjE)
              subgoal premises prems16
              apply(rule conjI)
              apply(insert prems16(1,2))[1]
                apply simp
              apply(insert prems16(1,3))
                apply(erule conjE)
                subgoal premises prems17
                apply(rule conjI)
                apply(insert prems17(1,2))[1]
                  apply simp
                apply(insert prems17(1,3))
                  apply simp
                done
              done
          apply(rule disjI2)
            apply(erule conjE)
            subgoal premises prems18
            apply(rule conjI)
            apply(insert prems18(1,2))[1]
              apply simp
            apply(insert prems18(1,3))
              apply(erule conjE)
              subgoal premises prems19
              apply(rule conjI)
              apply(insert prems19(1,2))[1]
                apply simp
              apply(insert prems19(1,3))
                apply simp
              done
            done
  done
apply(insert prems1(1,3,5))
  apply(erule previous_rule)
  apply simp
  apply(rule impI)
  apply(erule impE)
  apply assumption
  subgoal premises prems20
  apply(insert prems20(1,3))
    apply simp
  done
done
done

lemma EDTL_trigger_prev_delay_trueeinv_imp_req_gen: "
EDTL_trigger_prev_delay_true_inv b_0 w_0 trigger fin release_1 Inv_1 reaction_1 s0 \<Longrightarrow>
toEnvP s0 \<Longrightarrow>
(True \<and> ((always_imp s0 (\<lambda> r1 . (release_1 s0 r1)) (\<lambda> r1 . (release s0 r1))) \<and> (((always_imp s0 (\<lambda> r3 . (Inv_1 s0 r3)) (\<lambda> r3 . (Inv s0 r3))) \<and> True) \<and> ((always_imp s0 (\<lambda> r3 . (release_1 s0 r3)) (\<lambda> r3 . (release s0 r3))) \<and> (True \<and> ((always_imp s0 (\<lambda> r3 . (reaction_1 s0 r3)) (\<lambda> r3 . (reaction s0 r3))) \<and> (always_imp s0 (\<lambda> r3 . (Inv_1 s0 r3)) (\<lambda> r3 . (Inv s0 r3))))))))) \<Longrightarrow>
EDTL_trigger_prev_delay_true trigger fin release Inv reaction s0"

unfolding EDTL_trigger_prev_delay_true_inv_def EDTL_trigger_prev_delay_true_def
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
          apply simp
        apply(insert prems4(1,3))
          apply(rule weak_until_einv2req)
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
                  apply simp
                apply(insert prems6(1,3))
                  apply(rule always_imp_refl)
                done
            apply(insert prems5(1,3))
              apply(rule always_disj_rule)
              apply simp
                apply(erule conjE)
                subgoal premises prems7
                apply(rule conjI)
                apply(insert prems7(1,2))[1]
                  apply simp
                apply(insert prems7(1,3))
                  apply(rule always_conj_rule)
                  apply simp
                    apply(erule conjE)
                    subgoal premises prems8
                    apply(rule conjI)
                    apply(insert prems8(1,2))[1]
                      apply(rule always_imp_refl)
                    apply(insert prems8(1,3))
                      apply(rule always_conj_rule)
                      apply simp
                        apply(erule conjE)
                        subgoal premises prems9
                        apply(rule conjI)
                        apply(insert prems9(1,2))[1]
                          apply simp
                        apply(insert prems9(1,3))
                          apply simp
                        done
                    done
                done
            done
        done
    done
done
done
done

lemma EDTL_trigger_prev_delay_true_inv_saving: "
EDTL_trigger_prev_delay_true_inv_part b_0 w_0 trigger fin release Inv reaction s0 \<Longrightarrow>
consecutive s0 s \<Longrightarrow>
((((\<not> (w_0 s0)) \<or> (((release s) \<or> ((fin s) \<and> ((reaction s) \<and> (Inv s)))) \<or> ((w_0 s) \<and> ((Inv s) \<and> (\<not> (fin s)))))) \<and> ((b_0 s0) \<or> ((release s) \<or> (((release s) \<or> ((fin s) \<and> ((reaction s) \<and> (Inv s)))) \<or> ((w_0 s) \<and> ((Inv s) \<and> (\<not> (fin s)))))))) \<and> ((b_0 s) --> (\<not> (trigger s)))) \<Longrightarrow>
EDTL_trigger_prev_delay_true_inv_part b_0 w_0 trigger fin release Inv reaction s"

unfolding EDTL_trigger_prev_delay_true_inv_part_def EDTL_trigger_prev_delay_true_part_def
apply(simp add: EDTL_trigger_prev_delay_true_inv_saving_gen always_imp_refl)
done

lemma EDTL_trigger_prev_delay_trueeinv_imp_req: "
EDTL_trigger_prev_delay_true_inv_part b_0 w_0 trigger fin release Inv reaction s \<Longrightarrow>
toEnvP s \<Longrightarrow>
True \<Longrightarrow>
EDTL_trigger_prev_delay_true_part trigger fin release Inv reaction s"

unfolding EDTL_trigger_prev_delay_true_inv_part_def EDTL_trigger_prev_delay_true_part_def
apply(simp add: EDTL_trigger_prev_delay_trueeinv_imp_req_gen always_imp_refl)
done



lemmas EDTL_trigger_prev_delay_true_used_patterns = EDTL_trigger_prev_delay_true_def always_used_patterns weak_previous_def weak_until_def 

lemmas EDTL_trigger_prev_delay_true_inv_used_patterns = EDTL_trigger_prev_delay_true_inv_def always_inv_used_patterns weak_previous_def weak_until_inv_def previous_inv_def 

lemmas EDTL_trigger_prev_delay_true_inv_part_used_patterns = EDTL_trigger_prev_delay_true_inv_part_def EDTL_trigger_prev_delay_true_inv_used_patterns

lemmas EDTL_trigger_prev_delay_true_part_used_patterns = EDTL_trigger_prev_delay_true_part_def EDTL_trigger_prev_delay_true_used_patterns

definition EDTL_final_nontemporal_or_tau_delay_true where "EDTL_final_nontemporal_or_tau_delay_true finalt trigger finale release Inv reaction s \<equiv> (always (\<lambda> r2 r1 . ((\<not> (trigger r1)) \<or> ((release r2 r1) \<or> ((constrained_until finalt (\<lambda> r4 r3 . ((Inv r4 r3) \<and> (\<not> (finale r3)))) (\<lambda> r4 r3 . ((release r4 r3) \<or> ((finale r3) \<and> ((reaction r4 r3) \<and> (Inv r4 r3))))) r2 r1) \<or> (constrained_until2 finalt finalt (\<lambda> r4 r3 . ((Inv r4 r3) \<and> (\<not> (finale r3)))) (\<lambda> r4 r3 . ((reaction r4 r3) \<and> (Inv r4 r3))) r2 r1))))) s)"

definition EDTL_final_nontemporal_or_tau_delay_true_part where "EDTL_final_nontemporal_or_tau_delay_true_part finalt trigger finale release Inv reaction s \<equiv> (EDTL_final_nontemporal_or_tau_delay_true finalt trigger finale (\<lambda> s s1 . (release s1)) (\<lambda> s s1 . (Inv s1)) (\<lambda> s s1 . (reaction s1)) s)"

definition EDTL_final_nontemporal_or_tau_delay_true_inv where "EDTL_final_nontemporal_or_tau_delay_true_inv finalt t1_0 t1_1_0 t2_1_0 trigger finale release_1 Inv_1 reaction_1 s \<equiv> (always_inv (\<lambda> r2 r1 . ((\<not> (trigger r1)) \<or> ((release_1 r2 r1) \<or> ((constrained_until_inv finalt t1_0 (\<lambda> r4 r3 . ((Inv_1 r4 r3) \<and> (\<not> (finale r3)))) (\<lambda> r4 r3 . ((release_1 r4 r3) \<or> ((finale r3) \<and> ((reaction_1 r4 r3) \<and> (Inv_1 r4 r3))))) r2 r1) \<or> (constrained_until2_inv finalt finalt t1_1_0 t2_1_0 (\<lambda> r4 r3 . ((Inv_1 r4 r3) \<and> (\<not> (finale r3)))) (\<lambda> r4 r3 . ((reaction_1 r4 r3) \<and> (Inv_1 r4 r3))) r2 r1))))) s)"

definition EDTL_final_nontemporal_or_tau_delay_true_inv_part where "EDTL_final_nontemporal_or_tau_delay_true_inv_part finalt t1_0 t1_1_0 t2_1_0 trigger finale release Inv reaction s \<equiv> (EDTL_final_nontemporal_or_tau_delay_true_inv finalt t1_0 t1_1_0 t2_1_0 trigger finale (\<lambda> s s1 . (release s1)) (\<lambda> s s1 . (Inv s1)) (\<lambda> s s1 . (reaction s1)) s)"

lemma EDTL_final_nontemporal_or_tau_delay_true_inv_saving_gen: "
EDTL_final_nontemporal_or_tau_delay_true_inv finalt t1_0 t1_1_0 t2_1_0 trigger finale release_1 Inv_1 reaction_1 s0 \<Longrightarrow>
consecutive s0 s \<Longrightarrow>
((True \<and> ((always_imp s0 (\<lambda> r1 . (release_1 s0 r1)) (\<lambda> r1 . (release_1 s r1))) \<and> ((((always_imp s0 (\<lambda> r3 . (Inv_1 s0 r3)) (\<lambda> r3 . (Inv_1 s r3))) \<and> True) \<and> (((always_imp s0 (\<lambda> r3 . (release_1 s0 r3)) (\<lambda> r3 . (release_1 s r3))) \<and> (True \<and> ((always_imp s0 (\<lambda> r3 . (reaction_1 s0 r3)) (\<lambda> r3 . (reaction_1 s r3))) \<and> (always_imp s0 (\<lambda> r3 . (Inv_1 s0 r3)) (\<lambda> r3 . (Inv_1 s r3)))))) \<and> (((t1_0 s0) = 0) \<or> ((((release_1 s s) \<or> ((finale s) \<and> ((reaction_1 s s) \<and> (Inv_1 s s)))) \<and> ((t1_0 s0) <= finalt)) \<or> (((Inv_1 s s) \<and> (\<not> (finale s))) \<and> ((t1_0 s0) < (t1_0 s))))))) \<and> (((always_imp s0 (\<lambda> r3 . (Inv_1 s0 r3)) (\<lambda> r3 . (Inv_1 s r3))) \<and> True) \<and> (((always_imp s0 (\<lambda> r3 . (reaction_1 s0 r3)) (\<lambda> r3 . (reaction_1 s r3))) \<and> (always_imp s0 (\<lambda> r3 . (Inv_1 s0 r3)) (\<lambda> r3 . (Inv_1 s r3)))) \<and> (((t2_1_0 s0) = 0) \<or> (((t1_1_0 s0) >= (t2_1_0 s0)) \<or> ((((reaction_1 s s) \<and> (Inv_1 s s)) \<and> ((((t1_1_0 s0) + 1) >= finalt) \<and> ((t2_1_0 s0) <= finalt))) \<or> (((Inv_1 s s) \<and> (\<not> (finale s))) \<and> ((((t1_1_0 s0) + 1) >= (t1_1_0 s)) \<and> ((t2_1_0 s0) < (t2_1_0 s)))))))))))) \<and> ((\<not> (trigger s)) \<or> ((release_1 s s) \<or> ((((release_1 s s) \<or> ((finale s) \<and> ((reaction_1 s s) \<and> (Inv_1 s s)))) \<or> (((Inv_1 s s) \<and> (\<not> (finale s))) \<and> ((t1_0 s) > 0))) \<or> (((finalt = 0) \<and> ((reaction_1 s s) \<and> (Inv_1 s s))) \<or> (((Inv_1 s s) \<and> (\<not> (finale s))) \<and> (((t1_1_0 s) = 0) \<and> ((t2_1_0 s) > 0)))))))) \<Longrightarrow>
EDTL_final_nontemporal_or_tau_delay_true_inv finalt t1_0 t1_1_0 t2_1_0 trigger finale release_1 Inv_1 reaction_1 s"

unfolding EDTL_final_nontemporal_or_tau_delay_true_inv_def
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
        apply(rule always_disj_rule)
        apply simp
          apply(erule conjE)
          subgoal premises prems3
          apply(rule conjI)
          apply(insert prems3(1,2))[1]
            apply simp
          apply(insert prems3(1,3))
            apply(rule always_disj_rule)
            apply simp
              apply(erule conjE)
              subgoal premises prems4
              apply(rule conjI)
              apply(insert prems4(1,2))[1]
                apply(rule constrained_until_rule)
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
                        apply simp
                      apply(insert prems6(1,3))
                        apply(rule always_imp_refl)
                      done
                  apply(insert prems5(1,3))
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
                          apply simp
                        apply(insert prems8(1,3))
                          apply(rule always_conj_rule)
                          apply simp
                            apply(erule conjE)
                            subgoal premises prems9
                            apply(rule conjI)
                            apply(insert prems9(1,2))[1]
                              apply(rule always_imp_refl)
                            apply(insert prems9(1,3))
                              apply(rule always_conj_rule)
                              apply simp
                                apply(erule conjE)
                                subgoal premises prems10
                                apply(rule conjI)
                                apply(insert prems10(1,2))[1]
                                  apply simp
                                apply(insert prems10(1,3))
                                  apply simp
                                done
                            done
                        done
                    apply(insert prems7(1,3))
                      apply(erule disjE)
                      apply(rule disjI1)
                        apply simp
                      apply(rule disjI2)
                        apply(erule disjE)
                        apply(rule disjI1)
                          apply(erule conjE)
                          subgoal premises prems11
                          apply(rule conjI)
                          apply(insert prems11(1,2))[1]
                            apply(erule disjE)
                            apply(rule disjI1)
                              apply simp
                            apply(rule disjI2)
                              apply(erule conjE)
                              subgoal premises prems12
                              apply(rule conjI)
                              apply(insert prems12(1,2))[1]
                                apply simp
                              apply(insert prems12(1,3))
                                apply(erule conjE)
                                subgoal premises prems13
                                apply(rule conjI)
                                apply(insert prems13(1,2))[1]
                                  apply simp
                                apply(insert prems13(1,3))
                                  apply simp
                                done
                              done
                          apply(insert prems11(1,3))
                            apply simp
                          done
                        apply(rule disjI2)
                          apply(erule conjE)
                          subgoal premises prems14
                          apply(rule conjI)
                          apply(insert prems14(1,2))[1]
                            apply(erule conjE)
                            subgoal premises prems15
                            apply(rule conjI)
                            apply(insert prems15(1,2))[1]
                              apply simp
                            apply(insert prems15(1,3))
                              apply simp
                            done
                          apply(insert prems14(1,3))
                            apply simp
                          done
                    done
                  done
              apply(insert prems4(1,3))
                apply(rule constrained_until2_rule)
                apply simp
                  apply(erule conjE)
                  subgoal premises prems16
                  apply(rule conjI)
                  apply(insert prems16(1,2))[1]
                    apply(rule always_conj_rule)
                    apply simp
                      apply(erule conjE)
                      subgoal premises prems17
                      apply(rule conjI)
                      apply(insert prems17(1,2))[1]
                        apply simp
                      apply(insert prems17(1,3))
                        apply(rule always_imp_refl)
                      done
                  apply(insert prems16(1,3))
                    apply(erule conjE)
                    subgoal premises prems18
                    apply(rule conjI)
                    apply(insert prems18(1,2))[1]
                      apply(rule always_conj_rule)
                      apply simp
                        apply(erule conjE)
                        subgoal premises prems19
                        apply(rule conjI)
                        apply(insert prems19(1,2))[1]
                          apply simp
                        apply(insert prems19(1,3))
                          apply simp
                        done
                    apply(insert prems18(1,3))
                      apply(erule disjE)
                      apply(rule disjI1)
                        apply simp
                      apply(rule disjI2)
                        apply(erule disjE)
                        apply(rule disjI1)
                          apply simp
                        apply(rule disjI2)
                          apply(erule disjE)
                          apply(rule disjI1)
                            apply(erule conjE)
                            subgoal premises prems20
                            apply(rule conjI)
                            apply(insert prems20(1,2))[1]
                              apply(erule conjE)
                              subgoal premises prems21
                              apply(rule conjI)
                              apply(insert prems21(1,2))[1]
                                apply simp
                              apply(insert prems21(1,3))
                                apply simp
                              done
                            apply(insert prems20(1,3))
                              apply(erule conjE)
                              subgoal premises prems22
                              apply(rule conjI)
                              apply(insert prems22(1,2))[1]
                                apply simp
                              apply(insert prems22(1,3))
                                apply simp
                              done
                            done
                          apply(rule disjI2)
                            apply(erule conjE)
                            subgoal premises prems23
                            apply(rule conjI)
                            apply(insert prems23(1,2))[1]
                              apply(erule conjE)
                              subgoal premises prems24
                              apply(rule conjI)
                              apply(insert prems24(1,2))[1]
                                apply simp
                              apply(insert prems24(1,3))
                                apply simp
                              done
                            apply(insert prems23(1,3))
                              apply(erule conjE)
                              subgoal premises prems25
                              apply(rule conjI)
                              apply(insert prems25(1,2))[1]
                                apply simp
                              apply(insert prems25(1,3))
                                apply simp
                              done
                            done
                    done
                  done
              done
          done
      done
  apply(insert prems1(1,3))
    apply(erule disjE)
    apply(rule disjI1)
      apply simp
    apply(rule disjI2)
      apply(erule disjE)
      apply(rule disjI1)
        apply simp
      apply(rule disjI2)
        apply(erule disjE)
        apply(rule disjI1)
          apply(rule constrained_until_one_point)
          apply simp
            apply(erule disjE)
            apply(rule disjI1)
              apply(erule disjE)
              apply(rule disjI1)
                apply simp
              apply(rule disjI2)
                apply(erule conjE)
                subgoal premises prems26
                apply(rule conjI)
                apply(insert prems26(1,2))[1]
                  apply simp
                apply(insert prems26(1,3))
                  apply(erule conjE)
                  subgoal premises prems27
                  apply(rule conjI)
                  apply(insert prems27(1,2))[1]
                    apply simp
                  apply(insert prems27(1,3))
                    apply simp
                  done
                done
            apply(rule disjI2)
              apply(erule conjE)
              subgoal premises prems28
              apply(rule conjI)
              apply(insert prems28(1,2))[1]
                apply(erule conjE)
                subgoal premises prems29
                apply(rule conjI)
                apply(insert prems29(1,2))[1]
                  apply simp
                apply(insert prems29(1,3))
                  apply simp
                done
              apply(insert prems28(1,3))
                apply simp
              done
        apply(rule disjI2)
          apply(rule constrained_until2_one_point)
          apply simp
            apply(erule disjE)
            apply(rule disjI1)
              apply(erule conjE)
              subgoal premises prems30
              apply(rule conjI)
              apply(insert prems30(1,2))[1]
                apply simp
              apply(insert prems30(1,3))
                apply(erule conjE)
                subgoal premises prems31
                apply(rule conjI)
                apply(insert prems31(1,2))[1]
                  apply simp
                apply(insert prems31(1,3))
                  apply simp
                done
              done
            apply(rule disjI2)
              apply(erule conjE)
              subgoal premises prems32
              apply(rule conjI)
              apply(insert prems32(1,2))[1]
                apply(erule conjE)
                subgoal premises prems33
                apply(rule conjI)
                apply(insert prems33(1,2))[1]
                  apply simp
                apply(insert prems33(1,3))
                  apply simp
                done
              apply(insert prems32(1,3))
                apply(erule conjE)
                subgoal premises prems34
                apply(rule conjI)
                apply(insert prems34(1,2))[1]
                  apply simp
                apply(insert prems34(1,3))
                  apply simp
                done
              done
  done
done

lemma EDTL_final_nontemporal_or_tau_delay_trueeinv_imp_req_gen: "
EDTL_final_nontemporal_or_tau_delay_true_inv finalt t1_0 t1_1_0 t2_1_0 trigger finale release_1 Inv_1 reaction_1 s0 \<Longrightarrow>
toEnvP s0 \<Longrightarrow>
(True \<and> ((always_imp s0 (\<lambda> r1 . (release_1 s0 r1)) (\<lambda> r1 . (release s0 r1))) \<and> ((((always_imp s0 (\<lambda> r3 . (Inv_1 s0 r3)) (\<lambda> r3 . (Inv s0 r3))) \<and> True) \<and> (((always_imp s0 (\<lambda> r3 . (release_1 s0 r3)) (\<lambda> r3 . (release s0 r3))) \<and> (True \<and> ((always_imp s0 (\<lambda> r3 . (reaction_1 s0 r3)) (\<lambda> r3 . (reaction s0 r3))) \<and> (always_imp s0 (\<lambda> r3 . (Inv_1 s0 r3)) (\<lambda> r3 . (Inv s0 r3)))))) \<and> ((t1_0 s0) <= finalt))) \<and> (((always_imp s0 (\<lambda> r3 . (Inv_1 s0 r3)) (\<lambda> r3 . (Inv s0 r3))) \<and> True) \<and> (((always_imp s0 (\<lambda> r3 . (reaction_1 s0 r3)) (\<lambda> r3 . (reaction s0 r3))) \<and> (always_imp s0 (\<lambda> r3 . (Inv_1 s0 r3)) (\<lambda> r3 . (Inv s0 r3)))) \<and> ((t2_1_0 s0) <= finalt)))))) \<Longrightarrow>
EDTL_final_nontemporal_or_tau_delay_true finalt trigger finale release Inv reaction s0"

unfolding EDTL_final_nontemporal_or_tau_delay_true_inv_def EDTL_final_nontemporal_or_tau_delay_true_def
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
      apply(rule always_disj_rule)
      apply simp
        apply(erule conjE)
        subgoal premises prems4
        apply(rule conjI)
        apply(insert prems4(1,2))[1]
          apply simp
        apply(insert prems4(1,3))
          apply(rule always_disj_rule)
          apply simp
            apply(erule conjE)
            subgoal premises prems5
            apply(rule conjI)
            apply(insert prems5(1,2))[1]
              apply(rule constrained_until_einv2req)
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
                      apply simp
                    apply(insert prems7(1,3))
                      apply(rule always_imp_refl)
                    done
                apply(insert prems6(1,3))
                  apply(erule conjE)
                  subgoal premises prems8
                  apply(rule conjI)
                  apply(insert prems8(1,2))[1]
                    apply(rule always_disj_rule)
                    apply simp
                      apply(erule conjE)
                      subgoal premises prems9
                      apply(rule conjI)
                      apply(insert prems9(1,2))[1]
                        apply simp
                      apply(insert prems9(1,3))
                        apply(rule always_conj_rule)
                        apply simp
                          apply(erule conjE)
                          subgoal premises prems10
                          apply(rule conjI)
                          apply(insert prems10(1,2))[1]
                            apply(rule always_imp_refl)
                          apply(insert prems10(1,3))
                            apply(rule always_conj_rule)
                            apply simp
                              apply(erule conjE)
                              subgoal premises prems11
                              apply(rule conjI)
                              apply(insert prems11(1,2))[1]
                                apply simp
                              apply(insert prems11(1,3))
                                apply simp
                              done
                          done
                      done
                  apply(insert prems8(1,3))
                    apply simp
                  done
                done
            apply(insert prems5(1,3))
              apply(rule constrained_until2_einv2req)
              apply simp
                apply(erule conjE)
                subgoal premises prems12
                apply(rule conjI)
                apply(insert prems12(1,2))[1]
                  apply(rule always_conj_rule)
                  apply simp
                    apply(erule conjE)
                    subgoal premises prems13
                    apply(rule conjI)
                    apply(insert prems13(1,2))[1]
                      apply simp
                    apply(insert prems13(1,3))
                      apply(rule always_imp_refl)
                    done
                apply(insert prems12(1,3))
                  apply(erule conjE)
                  subgoal premises prems14
                  apply(rule conjI)
                  apply(insert prems14(1,2))[1]
                    apply(rule always_conj_rule)
                    apply simp
                      apply(erule conjE)
                      subgoal premises prems15
                      apply(rule conjI)
                      apply(insert prems15(1,2))[1]
                        apply simp
                      apply(insert prems15(1,3))
                        apply simp
                      done
                  apply(insert prems14(1,3))
                    apply simp
                  done
                done
            done
        done
    done
done

lemma EDTL_final_nontemporal_or_tau_delay_true_inv_saving: "
EDTL_final_nontemporal_or_tau_delay_true_inv_part finalt t1_0 t1_1_0 t2_1_0 trigger finale release Inv reaction s0 \<Longrightarrow>
consecutive s0 s \<Longrightarrow>
(((((t1_0 s0) = 0) \<or> ((((release s) \<or> ((finale s) \<and> ((reaction s) \<and> (Inv s)))) \<and> ((t1_0 s0) <= finalt)) \<or> (((Inv s) \<and> (\<not> (finale s))) \<and> ((t1_0 s0) < (t1_0 s))))) \<and> (((t2_1_0 s0) = 0) \<or> (((t1_1_0 s0) >= (t2_1_0 s0)) \<or> ((((reaction s) \<and> (Inv s)) \<and> ((((t1_1_0 s0) + 1) >= finalt) \<and> ((t2_1_0 s0) <= finalt))) \<or> (((Inv s) \<and> (\<not> (finale s))) \<and> ((((t1_1_0 s0) + 1) >= (t1_1_0 s)) \<and> ((t2_1_0 s0) < (t2_1_0 s)))))))) \<and> ((\<not> (trigger s)) \<or> ((release s) \<or> ((((release s) \<or> ((finale s) \<and> ((reaction s) \<and> (Inv s)))) \<or> (((Inv s) \<and> (\<not> (finale s))) \<and> ((t1_0 s) > 0))) \<or> (((finalt = 0) \<and> ((reaction s) \<and> (Inv s))) \<or> (((Inv s) \<and> (\<not> (finale s))) \<and> (((t1_1_0 s) = 0) \<and> ((t2_1_0 s) > 0)))))))) \<Longrightarrow>
EDTL_final_nontemporal_or_tau_delay_true_inv_part finalt t1_0 t1_1_0 t2_1_0 trigger finale release Inv reaction s"

unfolding EDTL_final_nontemporal_or_tau_delay_true_inv_part_def EDTL_final_nontemporal_or_tau_delay_true_part_def
apply(simp add: EDTL_final_nontemporal_or_tau_delay_true_inv_saving_gen always_imp_refl)
done

lemma EDTL_final_nontemporal_or_tau_delay_trueeinv_imp_req: "
EDTL_final_nontemporal_or_tau_delay_true_inv_part finalt t1_0 t1_1_0 t2_1_0 trigger finale release Inv reaction s \<Longrightarrow>
toEnvP s \<Longrightarrow>
(((t1_0 s) <= finalt) \<and> ((t2_1_0 s) <= finalt)) \<Longrightarrow>
EDTL_final_nontemporal_or_tau_delay_true_part finalt trigger finale release Inv reaction s"

unfolding EDTL_final_nontemporal_or_tau_delay_true_inv_part_def EDTL_final_nontemporal_or_tau_delay_true_part_def
apply(simp add: EDTL_final_nontemporal_or_tau_delay_trueeinv_imp_req_gen always_imp_refl)
done



lemmas EDTL_final_nontemporal_or_tau_delay_true_used_patterns = EDTL_final_nontemporal_or_tau_delay_true_def always_used_patterns constrained_until_def constrained_until2_def 

lemmas EDTL_final_nontemporal_or_tau_delay_true_inv_used_patterns = EDTL_final_nontemporal_or_tau_delay_true_inv_def always_inv_used_patterns constrained_until_inv_def constrained_until2_inv_def 

lemmas EDTL_final_nontemporal_or_tau_delay_true_inv_part_used_patterns = EDTL_final_nontemporal_or_tau_delay_true_inv_part_def EDTL_final_nontemporal_or_tau_delay_true_inv_used_patterns

lemmas EDTL_final_nontemporal_or_tau_delay_true_part_used_patterns = EDTL_final_nontemporal_or_tau_delay_true_part_def EDTL_final_nontemporal_or_tau_delay_true_used_patterns

definition EDTL_final_prev_delay_true where "EDTL_final_prev_delay_true trigger fin release Inv reaction s \<equiv> (always (\<lambda> r2 r1 . ((\<not> (trigger r1)) \<or> ((release r2 r1) \<or> (weak_until (\<lambda> r4 r3 . ((Inv r4 r3) \<and> (weak_previous (\<lambda> r6 r5 . (\<not> (fin r5))) r4 r3))) (\<lambda> r4 r3 . ((release r4 r3) \<or> ((previous (\<lambda> r6 r5 . (fin r5)) r4 r3) \<and> ((reaction r4 r3) \<and> (Inv r4 r3))))) r2 r1)))) s)"

definition EDTL_final_prev_delay_true_part where "EDTL_final_prev_delay_true_part trigger fin release Inv reaction s \<equiv> (EDTL_final_prev_delay_true trigger fin (\<lambda> s s1 . (release s1)) (\<lambda> s s1 . (Inv s1)) (\<lambda> s s1 . (reaction s1)) s)"

definition EDTL_final_prev_delay_true_inv where "EDTL_final_prev_delay_true_inv b_0 b_1 w_0 trigger fin release_1 Inv_1 reaction_1 s \<equiv> (((always_inv (\<lambda> r2 r1 . ((\<not> (trigger r1)) \<or> ((release_1 r2 r1) \<or> (weak_until_inv w_0 (\<lambda> r4 r3 . ((Inv_1 r4 r3) \<and> (weak_previous (\<lambda> r6 r5 . (\<not> (fin r5))) r4 r3))) (\<lambda> r4 r3 . ((release_1 r4 r3) \<or> ((previous (\<lambda> r6 r5 . (fin r5)) r4 r3) \<and> ((reaction_1 r4 r3) \<and> (Inv_1 r4 r3))))) r2 r1)))) s) \<and> (previous_inv b_0 (\<lambda> r6 r5 . (\<not> (fin r5))) s)) \<and> (previous_inv b_1 (\<lambda> r6 r5 . (fin r5)) s))"

definition EDTL_final_prev_delay_true_inv_part where "EDTL_final_prev_delay_true_inv_part b_0 b_1 w_0 trigger fin release Inv reaction s \<equiv> (EDTL_final_prev_delay_true_inv b_0 b_1 w_0 trigger fin (\<lambda> s s1 . (release s1)) (\<lambda> s s1 . (Inv s1)) (\<lambda> s s1 . (reaction s1)) s)"

lemma EDTL_final_prev_delay_true_inv_saving_gen: "
EDTL_final_prev_delay_true_inv b_0 b_1 w_0 trigger fin release_1 Inv_1 reaction_1 s0 \<Longrightarrow>
consecutive s0 s \<Longrightarrow>
((((True \<and> ((always_imp s0 (\<lambda> r1 . (release_1 s0 r1)) (\<lambda> r1 . (release_1 s r1))) \<and> (((always_imp s0 (\<lambda> r3 . (Inv_1 s0 r3)) (\<lambda> r3 . (Inv_1 s r3))) \<and> True) \<and> (((always_imp s0 (\<lambda> r3 . (release_1 s0 r3)) (\<lambda> r3 . (release_1 s r3))) \<and> (True \<and> ((always_imp s0 (\<lambda> r3 . (reaction_1 s0 r3)) (\<lambda> r3 . (reaction_1 s r3))) \<and> (always_imp s0 (\<lambda> r3 . (Inv_1 s0 r3)) (\<lambda> r3 . (Inv_1 s r3)))))) \<and> ((\<not> (w_0 s0)) \<or> (((release_1 s s) \<or> (((b_1 s0) \<and> True) \<and> ((reaction_1 s s) \<and> (Inv_1 s s)))) \<or> ((w_0 s) \<and> ((Inv_1 s s) \<and> ((b_0 s0) \<and> True))))))))) \<and> ((\<not> (trigger s)) \<or> ((release_1 s s) \<or> (((release_1 s s) \<or> (((b_1 s0) \<and> True) \<and> ((reaction_1 s s) \<and> (Inv_1 s s)))) \<or> ((w_0 s) \<and> ((Inv_1 s s) \<and> ((b_0 s0) \<and> True))))))) \<and> ((b_0 s) --> (\<not> (fin s)))) \<and> ((b_1 s) --> (fin s))) \<Longrightarrow>
EDTL_final_prev_delay_true_inv b_0 b_1 w_0 trigger fin release_1 Inv_1 reaction_1 s"

unfolding EDTL_final_prev_delay_true_inv_def
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
        apply(rule always_imp_refl)
      apply(insert prems4(1,3))
        apply(rule always_disj_rule)
        apply simp
          apply(erule conjE)
          subgoal premises prems5
          apply(rule conjI)
          apply(insert prems5(1,2))[1]
            apply simp
          apply(insert prems5(1,3))
            apply(rule weak_until_rule)
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
                    apply simp
                  apply(insert prems7(1,3))
                    apply(rule weak_previous_LS4)
                    apply simp
                      apply(rule always_imp_refl)
                  done
              apply(insert prems6(1,3))
                apply(erule conjE)
                subgoal premises prems8
                apply(rule conjI)
                apply(insert prems8(1,2))[1]
                  apply(rule always_disj_rule)
                  apply simp
                    apply(erule conjE)
                    subgoal premises prems9
                    apply(rule conjI)
                    apply(insert prems9(1,2))[1]
                      apply simp
                    apply(insert prems9(1,3))
                      apply(rule always_conj_rule)
                      apply simp
                        apply(erule conjE)
                        subgoal premises prems10
                        apply(rule conjI)
                        apply(insert prems10(1,2))[1]
                          apply(rule previous_LS4)
                          apply simp
                            apply(rule always_imp_refl)
                        apply(insert prems10(1,3))
                          apply(rule always_conj_rule)
                          apply simp
                            apply(erule conjE)
                            subgoal premises prems11
                            apply(rule conjI)
                            apply(insert prems11(1,2))[1]
                              apply simp
                            apply(insert prems11(1,3))
                              apply simp
                            done
                        done
                    done
                apply(insert prems8(1,3))
                  apply(erule disjE)
                  apply(rule disjI1)
                    apply simp
                  apply(rule disjI2)
                    apply(erule disjE)
                    apply(rule disjI1)
                      apply(erule disjE)
                      apply(rule disjI1)
                        apply simp
                      apply(rule disjI2)
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
                              apply simp
                            apply(insert prems13(1,3))
                              apply(rule always_imp_refl)
                            done
                        apply(insert prems12(1,3))
                          apply(erule conjE)
                          subgoal premises prems14
                          apply(rule conjI)
                          apply(insert prems14(1,2))[1]
                            apply simp
                          apply(insert prems14(1,3))
                            apply simp
                          done
                        done
                    apply(rule disjI2)
                      apply(erule conjE)
                      subgoal premises prems15
                      apply(rule conjI)
                      apply(insert prems15(1,2))[1]
                        apply simp
                      apply(insert prems15(1,3))
                        apply(erule conjE)
                        subgoal premises prems16
                        apply(rule conjI)
                        apply(insert prems16(1,2))[1]
                          apply simp
                        apply(insert prems16(1,3))
                          apply(rule weak_previous_one_point[OF prems2(3)])
                          apply simp
                            apply(erule conjE)
                            subgoal premises prems17
                            apply(rule conjI)
                            apply(insert prems17(1,2))[1]
                              apply simp
                            apply(insert prems17(1,3))
                              apply(rule always_imp_refl)
                            done
                        done
                      done
                done
              done
          done
      done
  apply(insert prems3(1,3))
    apply(erule disjE)
    apply(rule disjI1)
      apply simp
    apply(rule disjI2)
      apply(erule disjE)
      apply(rule disjI1)
        apply simp
      apply(rule disjI2)
        apply(rule weak_until_one_point)
        apply simp
          apply(erule disjE)
          apply(rule disjI1)
            apply(erule disjE)
            apply(rule disjI1)
              apply simp
            apply(rule disjI2)
              apply(erule conjE)
              subgoal premises prems18
              apply(rule conjI)
              apply(insert prems18(1,2))[1]
                apply(rule previous_one_point[OF prems1(3)])
                apply simp
                  apply(erule conjE)
                  subgoal premises prems19
                  apply(rule conjI)
                  apply(insert prems19(1,2))[1]
                    apply simp
                  apply(insert prems19(1,3))
                    apply(rule always_imp_refl)
                  done
              apply(insert prems18(1,3))
                apply(erule conjE)
                subgoal premises prems20
                apply(rule conjI)
                apply(insert prems20(1,2))[1]
                  apply simp
                apply(insert prems20(1,3))
                  apply simp
                done
              done
          apply(rule disjI2)
            apply(erule conjE)
            subgoal premises prems21
            apply(rule conjI)
            apply(insert prems21(1,2))[1]
              apply simp
            apply(insert prems21(1,3))
              apply(erule conjE)
              subgoal premises prems22
              apply(rule conjI)
              apply(insert prems22(1,2))[1]
                apply simp
              apply(insert prems22(1,3))
                apply(rule weak_previous_one_point[OF prems2(3)])
                apply simp
                  apply(erule conjE)
                  subgoal premises prems23
                  apply(rule conjI)
                  apply(insert prems23(1,2))[1]
                    apply simp
                  apply(insert prems23(1,3))
                    apply(rule always_imp_refl)
                  done
              done
            done
  done
apply(insert prems2(1,3,5))
  apply(erule previous_rule)
  apply simp
  apply(rule impI)
  apply(erule impE)
  apply assumption
  subgoal premises prems24
  apply(insert prems24(1,3))
    apply simp
  done
done
apply(insert prems1(1,3,5))
  apply(erule previous_rule)
  apply simp
  apply(rule impI)
  apply(erule impE)
  apply assumption
  subgoal premises prems25
  apply(insert prems25(1,3))
    apply simp
  done
done
done

lemma EDTL_final_prev_delay_trueeinv_imp_req_gen: "
EDTL_final_prev_delay_true_inv b_0 b_1 w_0 trigger fin release_1 Inv_1 reaction_1 s0 \<Longrightarrow>
toEnvP s0 \<Longrightarrow>
(True \<and> ((always_imp s0 (\<lambda> r1 . (release_1 s0 r1)) (\<lambda> r1 . (release s0 r1))) \<and> (((always_imp s0 (\<lambda> r3 . (Inv_1 s0 r3)) (\<lambda> r3 . (Inv s0 r3))) \<and> True) \<and> ((always_imp s0 (\<lambda> r3 . (release_1 s0 r3)) (\<lambda> r3 . (release s0 r3))) \<and> (True \<and> ((always_imp s0 (\<lambda> r3 . (reaction_1 s0 r3)) (\<lambda> r3 . (reaction s0 r3))) \<and> (always_imp s0 (\<lambda> r3 . (Inv_1 s0 r3)) (\<lambda> r3 . (Inv s0 r3))))))))) \<Longrightarrow>
EDTL_final_prev_delay_true trigger fin release Inv reaction s0"

unfolding EDTL_final_prev_delay_true_inv_def EDTL_final_prev_delay_true_def
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
      apply(rule always_imp_refl)
    apply(insert prems3(1,3))
      apply(rule always_disj_rule)
      apply simp
        apply(erule conjE)
        subgoal premises prems4
        apply(rule conjI)
        apply(insert prems4(1,2))[1]
          apply simp
        apply(insert prems4(1,3))
          apply(rule weak_until_einv2req)
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
                  apply simp
                apply(insert prems6(1,3))
                  apply(rule weak_previous_LS5)
                  apply simp
                    apply(rule always_imp_refl)
                done
            apply(insert prems5(1,3))
              apply(rule always_disj_rule)
              apply simp
                apply(erule conjE)
                subgoal premises prems7
                apply(rule conjI)
                apply(insert prems7(1,2))[1]
                  apply simp
                apply(insert prems7(1,3))
                  apply(rule always_conj_rule)
                  apply simp
                    apply(erule conjE)
                    subgoal premises prems8
                    apply(rule conjI)
                    apply(insert prems8(1,2))[1]
                      apply(rule previous_LS5)
                      apply simp
                        apply(rule always_imp_refl)
                    apply(insert prems8(1,3))
                      apply(rule always_conj_rule)
                      apply simp
                        apply(erule conjE)
                        subgoal premises prems9
                        apply(rule conjI)
                        apply(insert prems9(1,2))[1]
                          apply simp
                        apply(insert prems9(1,3))
                          apply simp
                        done
                    done
                done
            done
        done
    done
done
done
done

lemma EDTL_final_prev_delay_true_inv_saving: "
EDTL_final_prev_delay_true_inv_part b_0 b_1 w_0 trigger fin release Inv reaction s0 \<Longrightarrow>
consecutive s0 s \<Longrightarrow>
(((((\<not> (w_0 s0)) \<or> (((release s) \<or> ((b_1 s0) \<and> ((reaction s) \<and> (Inv s)))) \<or> ((w_0 s) \<and> ((Inv s) \<and> (b_0 s0))))) \<and> ((\<not> (trigger s)) \<or> ((release s) \<or> (((release s) \<or> ((b_1 s0) \<and> ((reaction s) \<and> (Inv s)))) \<or> ((w_0 s) \<and> ((Inv s) \<and> (b_0 s0))))))) \<and> ((b_0 s) --> (\<not> (fin s)))) \<and> ((b_1 s) --> (fin s))) \<Longrightarrow>
EDTL_final_prev_delay_true_inv_part b_0 b_1 w_0 trigger fin release Inv reaction s"

unfolding EDTL_final_prev_delay_true_inv_part_def EDTL_final_prev_delay_true_part_def
apply(simp add: EDTL_final_prev_delay_true_inv_saving_gen always_imp_refl)
done

lemma EDTL_final_prev_delay_trueeinv_imp_req: "
EDTL_final_prev_delay_true_inv_part b_0 b_1 w_0 trigger fin release Inv reaction s \<Longrightarrow>
toEnvP s \<Longrightarrow>
True \<Longrightarrow>
EDTL_final_prev_delay_true_part trigger fin release Inv reaction s"

unfolding EDTL_final_prev_delay_true_inv_part_def EDTL_final_prev_delay_true_part_def
apply(simp add: EDTL_final_prev_delay_trueeinv_imp_req_gen always_imp_refl)
done



lemmas EDTL_final_prev_delay_true_used_patterns = EDTL_final_prev_delay_true_def always_used_patterns weak_until_def weak_previous_def previous_def 

lemmas EDTL_final_prev_delay_true_inv_used_patterns = EDTL_final_prev_delay_true_inv_def always_inv_used_patterns weak_until_inv_def weak_previous_def previous_def previous_inv_def previous_inv_def 

lemmas EDTL_final_prev_delay_true_inv_part_used_patterns = EDTL_final_prev_delay_true_inv_part_def EDTL_final_prev_delay_true_inv_used_patterns

lemmas EDTL_final_prev_delay_true_part_used_patterns = EDTL_final_prev_delay_true_part_def EDTL_final_prev_delay_true_used_patterns

definition EDTL_trigger_prev_final_prev_delay_true where "EDTL_trigger_prev_final_prev_delay_true trigger fin release Inv reaction s \<equiv> (always (\<lambda> r2 r1 . ((weak_previous (\<lambda> r4 r3 . (\<not> (trigger r3))) r2 r1) \<or> ((release r2 r1) \<or> (weak_until (\<lambda> r4 r3 . ((Inv r4 r3) \<and> (weak_previous (\<lambda> r6 r5 . (\<not> (fin r5))) r4 r3))) (\<lambda> r4 r3 . ((release r4 r3) \<or> ((previous (\<lambda> r6 r5 . (fin r5)) r4 r3) \<and> ((reaction r4 r3) \<and> (Inv r4 r3))))) r2 r1)))) s)"

definition EDTL_trigger_prev_final_prev_delay_true_part where "EDTL_trigger_prev_final_prev_delay_true_part trigger fin release Inv reaction s \<equiv> (EDTL_trigger_prev_final_prev_delay_true trigger fin (\<lambda> s s1 . (release s1)) (\<lambda> s s1 . (Inv s1)) (\<lambda> s s1 . (reaction s1)) s)"

definition EDTL_trigger_prev_final_prev_delay_true_inv where "EDTL_trigger_prev_final_prev_delay_true_inv b_0 b_1 b_2 w_0 trigger fin release_1 Inv_1 reaction_1 s \<equiv> ((((always_inv (\<lambda> r2 r1 . ((weak_previous (\<lambda> r4 r3 . (\<not> (trigger r3))) r2 r1) \<or> ((release_1 r2 r1) \<or> (weak_until_inv w_0 (\<lambda> r4 r3 . ((Inv_1 r4 r3) \<and> (weak_previous (\<lambda> r6 r5 . (\<not> (fin r5))) r4 r3))) (\<lambda> r4 r3 . ((release_1 r4 r3) \<or> ((previous (\<lambda> r6 r5 . (fin r5)) r4 r3) \<and> ((reaction_1 r4 r3) \<and> (Inv_1 r4 r3))))) r2 r1)))) s) \<and> (previous_inv b_0 (\<lambda> r4 r3 . (\<not> (trigger r3))) s)) \<and> (previous_inv b_1 (\<lambda> r6 r5 . (\<not> (fin r5))) s)) \<and> (previous_inv b_2 (\<lambda> r6 r5 . (fin r5)) s))"

definition EDTL_trigger_prev_final_prev_delay_true_inv_part where "EDTL_trigger_prev_final_prev_delay_true_inv_part b_0 b_1 b_2 w_0 trigger fin release Inv reaction s \<equiv> (EDTL_trigger_prev_final_prev_delay_true_inv b_0 b_1 b_2 w_0 trigger fin (\<lambda> s s1 . (release s1)) (\<lambda> s s1 . (Inv s1)) (\<lambda> s s1 . (reaction s1)) s)"

lemma EDTL_trigger_prev_final_prev_delay_true_inv_saving_gen: "
EDTL_trigger_prev_final_prev_delay_true_inv b_0 b_1 b_2 w_0 trigger fin release_1 Inv_1 reaction_1 s0 \<Longrightarrow>
consecutive s0 s \<Longrightarrow>
(((((True \<and> ((always_imp s0 (\<lambda> r1 . (release_1 s0 r1)) (\<lambda> r1 . (release_1 s r1))) \<and> (((always_imp s0 (\<lambda> r3 . (Inv_1 s0 r3)) (\<lambda> r3 . (Inv_1 s r3))) \<and> True) \<and> (((always_imp s0 (\<lambda> r3 . (release_1 s0 r3)) (\<lambda> r3 . (release_1 s r3))) \<and> (True \<and> ((always_imp s0 (\<lambda> r3 . (reaction_1 s0 r3)) (\<lambda> r3 . (reaction_1 s r3))) \<and> (always_imp s0 (\<lambda> r3 . (Inv_1 s0 r3)) (\<lambda> r3 . (Inv_1 s r3)))))) \<and> ((\<not> (w_0 s0)) \<or> (((release_1 s s) \<or> (((b_2 s0) \<and> True) \<and> ((reaction_1 s s) \<and> (Inv_1 s s)))) \<or> ((w_0 s) \<and> ((Inv_1 s s) \<and> ((b_1 s0) \<and> True))))))))) \<and> (((b_0 s0) \<and> True) \<or> ((release_1 s s) \<or> (((release_1 s s) \<or> (((b_2 s0) \<and> True) \<and> ((reaction_1 s s) \<and> (Inv_1 s s)))) \<or> ((w_0 s) \<and> ((Inv_1 s s) \<and> ((b_1 s0) \<and> True))))))) \<and> ((b_0 s) --> (\<not> (trigger s)))) \<and> ((b_1 s) --> (\<not> (fin s)))) \<and> ((b_2 s) --> (fin s))) \<Longrightarrow>
EDTL_trigger_prev_final_prev_delay_true_inv b_0 b_1 b_2 w_0 trigger fin release_1 Inv_1 reaction_1 s"

unfolding EDTL_trigger_prev_final_prev_delay_true_inv_def
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
apply(erule conjE)
apply(erule conjE)
subgoal premises prems3
apply(rule conjI)
apply(insert prems3(1,2,4))[1]
apply(erule always_rule)
  apply simp
  apply(erule conjE)
  subgoal premises prems4
  apply(rule conjI)
  apply(insert prems4(1,2))[1]
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
        apply(rule always_disj_rule)
        apply simp
          apply(erule conjE)
          subgoal premises prems6
          apply(rule conjI)
          apply(insert prems6(1,2))[1]
            apply simp
          apply(insert prems6(1,3))
            apply(rule weak_until_rule)
            apply simp
              apply(erule conjE)
              subgoal premises prems7
              apply(rule conjI)
              apply(insert prems7(1,2))[1]
                apply(rule always_conj_rule)
                apply simp
                  apply(erule conjE)
                  subgoal premises prems8
                  apply(rule conjI)
                  apply(insert prems8(1,2))[1]
                    apply simp
                  apply(insert prems8(1,3))
                    apply(rule weak_previous_LS4)
                    apply simp
                      apply(rule always_imp_refl)
                  done
              apply(insert prems7(1,3))
                apply(erule conjE)
                subgoal premises prems9
                apply(rule conjI)
                apply(insert prems9(1,2))[1]
                  apply(rule always_disj_rule)
                  apply simp
                    apply(erule conjE)
                    subgoal premises prems10
                    apply(rule conjI)
                    apply(insert prems10(1,2))[1]
                      apply simp
                    apply(insert prems10(1,3))
                      apply(rule always_conj_rule)
                      apply simp
                        apply(erule conjE)
                        subgoal premises prems11
                        apply(rule conjI)
                        apply(insert prems11(1,2))[1]
                          apply(rule previous_LS4)
                          apply simp
                            apply(rule always_imp_refl)
                        apply(insert prems11(1,3))
                          apply(rule always_conj_rule)
                          apply simp
                            apply(erule conjE)
                            subgoal premises prems12
                            apply(rule conjI)
                            apply(insert prems12(1,2))[1]
                              apply simp
                            apply(insert prems12(1,3))
                              apply simp
                            done
                        done
                    done
                apply(insert prems9(1,3))
                  apply(erule disjE)
                  apply(rule disjI1)
                    apply simp
                  apply(rule disjI2)
                    apply(erule disjE)
                    apply(rule disjI1)
                      apply(erule disjE)
                      apply(rule disjI1)
                        apply simp
                      apply(rule disjI2)
                        apply(erule conjE)
                        subgoal premises prems13
                        apply(rule conjI)
                        apply(insert prems13(1,2))[1]
                          apply(rule previous_one_point[OF prems1(3)])
                          apply simp
                            apply(erule conjE)
                            subgoal premises prems14
                            apply(rule conjI)
                            apply(insert prems14(1,2))[1]
                              apply simp
                            apply(insert prems14(1,3))
                              apply(rule always_imp_refl)
                            done
                        apply(insert prems13(1,3))
                          apply(erule conjE)
                          subgoal premises prems15
                          apply(rule conjI)
                          apply(insert prems15(1,2))[1]
                            apply simp
                          apply(insert prems15(1,3))
                            apply simp
                          done
                        done
                    apply(rule disjI2)
                      apply(erule conjE)
                      subgoal premises prems16
                      apply(rule conjI)
                      apply(insert prems16(1,2))[1]
                        apply simp
                      apply(insert prems16(1,3))
                        apply(erule conjE)
                        subgoal premises prems17
                        apply(rule conjI)
                        apply(insert prems17(1,2))[1]
                          apply simp
                        apply(insert prems17(1,3))
                          apply(rule weak_previous_one_point[OF prems2(3)])
                          apply simp
                            apply(erule conjE)
                            subgoal premises prems18
                            apply(rule conjI)
                            apply(insert prems18(1,2))[1]
                              apply simp
                            apply(insert prems18(1,3))
                              apply(rule always_imp_refl)
                            done
                        done
                      done
                done
              done
          done
      done
  apply(insert prems4(1,3))
    apply(erule disjE)
    apply(rule disjI1)
      apply(rule weak_previous_one_point[OF prems3(3)])
      apply simp
        apply(erule conjE)
        subgoal premises prems19
        apply(rule conjI)
        apply(insert prems19(1,2))[1]
          apply simp
        apply(insert prems19(1,3))
          apply(rule always_imp_refl)
        done
    apply(rule disjI2)
      apply(erule disjE)
      apply(rule disjI1)
        apply simp
      apply(rule disjI2)
        apply(rule weak_until_one_point)
        apply simp
          apply(erule disjE)
          apply(rule disjI1)
            apply(erule disjE)
            apply(rule disjI1)
              apply simp
            apply(rule disjI2)
              apply(erule conjE)
              subgoal premises prems20
              apply(rule conjI)
              apply(insert prems20(1,2))[1]
                apply(rule previous_one_point[OF prems1(3)])
                apply simp
                  apply(erule conjE)
                  subgoal premises prems21
                  apply(rule conjI)
                  apply(insert prems21(1,2))[1]
                    apply simp
                  apply(insert prems21(1,3))
                    apply(rule always_imp_refl)
                  done
              apply(insert prems20(1,3))
                apply(erule conjE)
                subgoal premises prems22
                apply(rule conjI)
                apply(insert prems22(1,2))[1]
                  apply simp
                apply(insert prems22(1,3))
                  apply simp
                done
              done
          apply(rule disjI2)
            apply(erule conjE)
            subgoal premises prems23
            apply(rule conjI)
            apply(insert prems23(1,2))[1]
              apply simp
            apply(insert prems23(1,3))
              apply(erule conjE)
              subgoal premises prems24
              apply(rule conjI)
              apply(insert prems24(1,2))[1]
                apply simp
              apply(insert prems24(1,3))
                apply(rule weak_previous_one_point[OF prems2(3)])
                apply simp
                  apply(erule conjE)
                  subgoal premises prems25
                  apply(rule conjI)
                  apply(insert prems25(1,2))[1]
                    apply simp
                  apply(insert prems25(1,3))
                    apply(rule always_imp_refl)
                  done
              done
            done
  done
apply(insert prems3(1,3,5))
  apply(erule previous_rule)
  apply simp
  apply(rule impI)
  apply(erule impE)
  apply assumption
  subgoal premises prems26
  apply(insert prems26(1,3))
    apply simp
  done
done
apply(insert prems2(1,3,5))
  apply(erule previous_rule)
  apply simp
  apply(rule impI)
  apply(erule impE)
  apply assumption
  subgoal premises prems27
  apply(insert prems27(1,3))
    apply simp
  done
done
apply(insert prems1(1,3,5))
  apply(erule previous_rule)
  apply simp
  apply(rule impI)
  apply(erule impE)
  apply assumption
  subgoal premises prems28
  apply(insert prems28(1,3))
    apply simp
  done
done
done

lemma EDTL_trigger_prev_final_prev_delay_trueeinv_imp_req_gen: "
EDTL_trigger_prev_final_prev_delay_true_inv b_0 b_1 b_2 w_0 trigger fin release_1 Inv_1 reaction_1 s0 \<Longrightarrow>
toEnvP s0 \<Longrightarrow>
(True \<and> ((always_imp s0 (\<lambda> r1 . (release_1 s0 r1)) (\<lambda> r1 . (release s0 r1))) \<and> (((always_imp s0 (\<lambda> r3 . (Inv_1 s0 r3)) (\<lambda> r3 . (Inv s0 r3))) \<and> True) \<and> ((always_imp s0 (\<lambda> r3 . (release_1 s0 r3)) (\<lambda> r3 . (release s0 r3))) \<and> (True \<and> ((always_imp s0 (\<lambda> r3 . (reaction_1 s0 r3)) (\<lambda> r3 . (reaction s0 r3))) \<and> (always_imp s0 (\<lambda> r3 . (Inv_1 s0 r3)) (\<lambda> r3 . (Inv s0 r3))))))))) \<Longrightarrow>
EDTL_trigger_prev_final_prev_delay_true trigger fin release Inv reaction s0"

unfolding EDTL_trigger_prev_final_prev_delay_true_inv_def EDTL_trigger_prev_final_prev_delay_true_def
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
          apply simp
        apply(insert prems4(1,3))
          apply(rule weak_until_einv2req)
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
                  apply simp
                apply(insert prems6(1,3))
                  apply(rule weak_previous_LS5)
                  apply simp
                    apply(rule always_imp_refl)
                done
            apply(insert prems5(1,3))
              apply(rule always_disj_rule)
              apply simp
                apply(erule conjE)
                subgoal premises prems7
                apply(rule conjI)
                apply(insert prems7(1,2))[1]
                  apply simp
                apply(insert prems7(1,3))
                  apply(rule always_conj_rule)
                  apply simp
                    apply(erule conjE)
                    subgoal premises prems8
                    apply(rule conjI)
                    apply(insert prems8(1,2))[1]
                      apply(rule previous_LS5)
                      apply simp
                        apply(rule always_imp_refl)
                    apply(insert prems8(1,3))
                      apply(rule always_conj_rule)
                      apply simp
                        apply(erule conjE)
                        subgoal premises prems9
                        apply(rule conjI)
                        apply(insert prems9(1,2))[1]
                          apply simp
                        apply(insert prems9(1,3))
                          apply simp
                        done
                    done
                done
            done
        done
    done
done
done
done

lemma EDTL_trigger_prev_final_prev_delay_true_inv_saving: "
EDTL_trigger_prev_final_prev_delay_true_inv_part b_0 b_1 b_2 w_0 trigger fin release Inv reaction s0 \<Longrightarrow>
consecutive s0 s \<Longrightarrow>
((((((\<not> (w_0 s0)) \<or> (((release s) \<or> ((b_2 s0) \<and> ((reaction s) \<and> (Inv s)))) \<or> ((w_0 s) \<and> ((Inv s) \<and> (b_1 s0))))) \<and> ((b_0 s0) \<or> ((release s) \<or> (((release s) \<or> ((b_2 s0) \<and> ((reaction s) \<and> (Inv s)))) \<or> ((w_0 s) \<and> ((Inv s) \<and> (b_1 s0))))))) \<and> ((b_0 s) --> (\<not> (trigger s)))) \<and> ((b_1 s) --> (\<not> (fin s)))) \<and> ((b_2 s) --> (fin s))) \<Longrightarrow>
EDTL_trigger_prev_final_prev_delay_true_inv_part b_0 b_1 b_2 w_0 trigger fin release Inv reaction s"

unfolding EDTL_trigger_prev_final_prev_delay_true_inv_part_def EDTL_trigger_prev_final_prev_delay_true_part_def
apply(simp add: EDTL_trigger_prev_final_prev_delay_true_inv_saving_gen always_imp_refl)
done

lemma EDTL_trigger_prev_final_prev_delay_trueeinv_imp_req: "
EDTL_trigger_prev_final_prev_delay_true_inv_part b_0 b_1 b_2 w_0 trigger fin release Inv reaction s \<Longrightarrow>
toEnvP s \<Longrightarrow>
True \<Longrightarrow>
EDTL_trigger_prev_final_prev_delay_true_part trigger fin release Inv reaction s"

unfolding EDTL_trigger_prev_final_prev_delay_true_inv_part_def EDTL_trigger_prev_final_prev_delay_true_part_def
apply(simp add: EDTL_trigger_prev_final_prev_delay_trueeinv_imp_req_gen always_imp_refl)
done



lemmas EDTL_trigger_prev_final_prev_delay_true_used_patterns = EDTL_trigger_prev_final_prev_delay_true_def always_used_patterns weak_previous_def weak_until_def weak_previous_def previous_def 

lemmas EDTL_trigger_prev_final_prev_delay_true_inv_used_patterns = EDTL_trigger_prev_final_prev_delay_true_inv_def always_inv_used_patterns weak_previous_def weak_until_inv_def weak_previous_def previous_def previous_inv_def previous_inv_def previous_inv_def 

lemmas EDTL_trigger_prev_final_prev_delay_true_inv_part_used_patterns = EDTL_trigger_prev_final_prev_delay_true_inv_part_def EDTL_trigger_prev_final_prev_delay_true_inv_used_patterns

lemmas EDTL_trigger_prev_final_prev_delay_true_part_used_patterns = EDTL_trigger_prev_final_prev_delay_true_part_def EDTL_trigger_prev_final_prev_delay_true_used_patterns

definition EDTL_trigger_prev_final_nontemporal_or_tau_delay_true where "EDTL_trigger_prev_final_nontemporal_or_tau_delay_true finalt trigger finale release Inv reaction s \<equiv> (always (\<lambda> r2 r1 . ((weak_previous (\<lambda> r4 r3 . (\<not> (trigger r3))) r2 r1) \<or> ((release r2 r1) \<or> ((constrained_until finalt (\<lambda> r4 r3 . ((Inv r4 r3) \<and> (\<not> (finale r3)))) (\<lambda> r4 r3 . ((release r4 r3) \<or> ((finale r3) \<and> ((reaction r4 r3) \<and> (Inv r4 r3))))) r2 r1) \<or> (constrained_until2 finalt finalt (\<lambda> r4 r3 . ((Inv r4 r3) \<and> (\<not> (finale r3)))) (\<lambda> r4 r3 . ((reaction r4 r3) \<and> (Inv r4 r3))) r2 r1))))) s)"

definition EDTL_trigger_prev_final_nontemporal_or_tau_delay_true_part where "EDTL_trigger_prev_final_nontemporal_or_tau_delay_true_part finalt trigger finale release Inv reaction s \<equiv> (EDTL_trigger_prev_final_nontemporal_or_tau_delay_true finalt trigger finale (\<lambda> s s1 . (release s1)) (\<lambda> s s1 . (Inv s1)) (\<lambda> s s1 . (reaction s1)) s)"

definition EDTL_trigger_prev_final_nontemporal_or_tau_delay_true_inv where "EDTL_trigger_prev_final_nontemporal_or_tau_delay_true_inv finalt b_0 t1_0 t1_1_0 t2_1_0 trigger finale release_1 Inv_1 reaction_1 s \<equiv> ((always_inv (\<lambda> r2 r1 . ((weak_previous (\<lambda> r4 r3 . (\<not> (trigger r3))) r2 r1) \<or> ((release_1 r2 r1) \<or> ((constrained_until_inv finalt t1_0 (\<lambda> r4 r3 . ((Inv_1 r4 r3) \<and> (\<not> (finale r3)))) (\<lambda> r4 r3 . ((release_1 r4 r3) \<or> ((finale r3) \<and> ((reaction_1 r4 r3) \<and> (Inv_1 r4 r3))))) r2 r1) \<or> (constrained_until2_inv finalt finalt t1_1_0 t2_1_0 (\<lambda> r4 r3 . ((Inv_1 r4 r3) \<and> (\<not> (finale r3)))) (\<lambda> r4 r3 . ((reaction_1 r4 r3) \<and> (Inv_1 r4 r3))) r2 r1))))) s) \<and> (previous_inv b_0 (\<lambda> r4 r3 . (\<not> (trigger r3))) s))"

definition EDTL_trigger_prev_final_nontemporal_or_tau_delay_true_inv_part where "EDTL_trigger_prev_final_nontemporal_or_tau_delay_true_inv_part finalt b_0 t1_0 t1_1_0 t2_1_0 trigger finale release Inv reaction s \<equiv> (EDTL_trigger_prev_final_nontemporal_or_tau_delay_true_inv finalt b_0 t1_0 t1_1_0 t2_1_0 trigger finale (\<lambda> s s1 . (release s1)) (\<lambda> s s1 . (Inv s1)) (\<lambda> s s1 . (reaction s1)) s)"

lemma EDTL_trigger_prev_final_nontemporal_or_tau_delay_true_inv_saving_gen: "
EDTL_trigger_prev_final_nontemporal_or_tau_delay_true_inv finalt b_0 t1_0 t1_1_0 t2_1_0 trigger finale release_1 Inv_1 reaction_1 s0 \<Longrightarrow>
consecutive s0 s \<Longrightarrow>
(((True \<and> ((always_imp s0 (\<lambda> r1 . (release_1 s0 r1)) (\<lambda> r1 . (release_1 s r1))) \<and> ((((always_imp s0 (\<lambda> r3 . (Inv_1 s0 r3)) (\<lambda> r3 . (Inv_1 s r3))) \<and> True) \<and> (((always_imp s0 (\<lambda> r3 . (release_1 s0 r3)) (\<lambda> r3 . (release_1 s r3))) \<and> (True \<and> ((always_imp s0 (\<lambda> r3 . (reaction_1 s0 r3)) (\<lambda> r3 . (reaction_1 s r3))) \<and> (always_imp s0 (\<lambda> r3 . (Inv_1 s0 r3)) (\<lambda> r3 . (Inv_1 s r3)))))) \<and> (((t1_0 s0) = 0) \<or> ((((release_1 s s) \<or> ((finale s) \<and> ((reaction_1 s s) \<and> (Inv_1 s s)))) \<and> ((t1_0 s0) <= finalt)) \<or> (((Inv_1 s s) \<and> (\<not> (finale s))) \<and> ((t1_0 s0) < (t1_0 s))))))) \<and> (((always_imp s0 (\<lambda> r3 . (Inv_1 s0 r3)) (\<lambda> r3 . (Inv_1 s r3))) \<and> True) \<and> (((always_imp s0 (\<lambda> r3 . (reaction_1 s0 r3)) (\<lambda> r3 . (reaction_1 s r3))) \<and> (always_imp s0 (\<lambda> r3 . (Inv_1 s0 r3)) (\<lambda> r3 . (Inv_1 s r3)))) \<and> (((t2_1_0 s0) = 0) \<or> (((t1_1_0 s0) >= (t2_1_0 s0)) \<or> ((((reaction_1 s s) \<and> (Inv_1 s s)) \<and> ((((t1_1_0 s0) + 1) >= finalt) \<and> ((t2_1_0 s0) <= finalt))) \<or> (((Inv_1 s s) \<and> (\<not> (finale s))) \<and> ((((t1_1_0 s0) + 1) >= (t1_1_0 s)) \<and> ((t2_1_0 s0) < (t2_1_0 s)))))))))))) \<and> (((b_0 s0) \<and> True) \<or> ((release_1 s s) \<or> ((((release_1 s s) \<or> ((finale s) \<and> ((reaction_1 s s) \<and> (Inv_1 s s)))) \<or> (((Inv_1 s s) \<and> (\<not> (finale s))) \<and> ((t1_0 s) > 0))) \<or> (((finalt = 0) \<and> ((reaction_1 s s) \<and> (Inv_1 s s))) \<or> (((Inv_1 s s) \<and> (\<not> (finale s))) \<and> (((t1_1_0 s) = 0) \<and> ((t2_1_0 s) > 0)))))))) \<and> ((b_0 s) --> (\<not> (trigger s)))) \<Longrightarrow>
EDTL_trigger_prev_final_nontemporal_or_tau_delay_true_inv finalt b_0 t1_0 t1_1_0 t2_1_0 trigger finale release_1 Inv_1 reaction_1 s"

unfolding EDTL_trigger_prev_final_nontemporal_or_tau_delay_true_inv_def
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
            apply simp
          apply(insert prems4(1,3))
            apply(rule always_disj_rule)
            apply simp
              apply(erule conjE)
              subgoal premises prems5
              apply(rule conjI)
              apply(insert prems5(1,2))[1]
                apply(rule constrained_until_rule)
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
                        apply simp
                      apply(insert prems7(1,3))
                        apply(rule always_imp_refl)
                      done
                  apply(insert prems6(1,3))
                    apply(erule conjE)
                    subgoal premises prems8
                    apply(rule conjI)
                    apply(insert prems8(1,2))[1]
                      apply(rule always_disj_rule)
                      apply simp
                        apply(erule conjE)
                        subgoal premises prems9
                        apply(rule conjI)
                        apply(insert prems9(1,2))[1]
                          apply simp
                        apply(insert prems9(1,3))
                          apply(rule always_conj_rule)
                          apply simp
                            apply(erule conjE)
                            subgoal premises prems10
                            apply(rule conjI)
                            apply(insert prems10(1,2))[1]
                              apply(rule always_imp_refl)
                            apply(insert prems10(1,3))
                              apply(rule always_conj_rule)
                              apply simp
                                apply(erule conjE)
                                subgoal premises prems11
                                apply(rule conjI)
                                apply(insert prems11(1,2))[1]
                                  apply simp
                                apply(insert prems11(1,3))
                                  apply simp
                                done
                            done
                        done
                    apply(insert prems8(1,3))
                      apply(erule disjE)
                      apply(rule disjI1)
                        apply simp
                      apply(rule disjI2)
                        apply(erule disjE)
                        apply(rule disjI1)
                          apply(erule conjE)
                          subgoal premises prems12
                          apply(rule conjI)
                          apply(insert prems12(1,2))[1]
                            apply(erule disjE)
                            apply(rule disjI1)
                              apply simp
                            apply(rule disjI2)
                              apply(erule conjE)
                              subgoal premises prems13
                              apply(rule conjI)
                              apply(insert prems13(1,2))[1]
                                apply simp
                              apply(insert prems13(1,3))
                                apply(erule conjE)
                                subgoal premises prems14
                                apply(rule conjI)
                                apply(insert prems14(1,2))[1]
                                  apply simp
                                apply(insert prems14(1,3))
                                  apply simp
                                done
                              done
                          apply(insert prems12(1,3))
                            apply simp
                          done
                        apply(rule disjI2)
                          apply(erule conjE)
                          subgoal premises prems15
                          apply(rule conjI)
                          apply(insert prems15(1,2))[1]
                            apply(erule conjE)
                            subgoal premises prems16
                            apply(rule conjI)
                            apply(insert prems16(1,2))[1]
                              apply simp
                            apply(insert prems16(1,3))
                              apply simp
                            done
                          apply(insert prems15(1,3))
                            apply simp
                          done
                    done
                  done
              apply(insert prems5(1,3))
                apply(rule constrained_until2_rule)
                apply simp
                  apply(erule conjE)
                  subgoal premises prems17
                  apply(rule conjI)
                  apply(insert prems17(1,2))[1]
                    apply(rule always_conj_rule)
                    apply simp
                      apply(erule conjE)
                      subgoal premises prems18
                      apply(rule conjI)
                      apply(insert prems18(1,2))[1]
                        apply simp
                      apply(insert prems18(1,3))
                        apply(rule always_imp_refl)
                      done
                  apply(insert prems17(1,3))
                    apply(erule conjE)
                    subgoal premises prems19
                    apply(rule conjI)
                    apply(insert prems19(1,2))[1]
                      apply(rule always_conj_rule)
                      apply simp
                        apply(erule conjE)
                        subgoal premises prems20
                        apply(rule conjI)
                        apply(insert prems20(1,2))[1]
                          apply simp
                        apply(insert prems20(1,3))
                          apply simp
                        done
                    apply(insert prems19(1,3))
                      apply(erule disjE)
                      apply(rule disjI1)
                        apply simp
                      apply(rule disjI2)
                        apply(erule disjE)
                        apply(rule disjI1)
                          apply simp
                        apply(rule disjI2)
                          apply(erule disjE)
                          apply(rule disjI1)
                            apply(erule conjE)
                            subgoal premises prems21
                            apply(rule conjI)
                            apply(insert prems21(1,2))[1]
                              apply(erule conjE)
                              subgoal premises prems22
                              apply(rule conjI)
                              apply(insert prems22(1,2))[1]
                                apply simp
                              apply(insert prems22(1,3))
                                apply simp
                              done
                            apply(insert prems21(1,3))
                              apply(erule conjE)
                              subgoal premises prems23
                              apply(rule conjI)
                              apply(insert prems23(1,2))[1]
                                apply simp
                              apply(insert prems23(1,3))
                                apply simp
                              done
                            done
                          apply(rule disjI2)
                            apply(erule conjE)
                            subgoal premises prems24
                            apply(rule conjI)
                            apply(insert prems24(1,2))[1]
                              apply(erule conjE)
                              subgoal premises prems25
                              apply(rule conjI)
                              apply(insert prems25(1,2))[1]
                                apply simp
                              apply(insert prems25(1,3))
                                apply simp
                              done
                            apply(insert prems24(1,3))
                              apply(erule conjE)
                              subgoal premises prems26
                              apply(rule conjI)
                              apply(insert prems26(1,2))[1]
                                apply simp
                              apply(insert prems26(1,3))
                                apply simp
                              done
                            done
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
        subgoal premises prems27
        apply(rule conjI)
        apply(insert prems27(1,2))[1]
          apply simp
        apply(insert prems27(1,3))
          apply(rule always_imp_refl)
        done
    apply(rule disjI2)
      apply(erule disjE)
      apply(rule disjI1)
        apply simp
      apply(rule disjI2)
        apply(erule disjE)
        apply(rule disjI1)
          apply(rule constrained_until_one_point)
          apply simp
            apply(erule disjE)
            apply(rule disjI1)
              apply(erule disjE)
              apply(rule disjI1)
                apply simp
              apply(rule disjI2)
                apply(erule conjE)
                subgoal premises prems28
                apply(rule conjI)
                apply(insert prems28(1,2))[1]
                  apply simp
                apply(insert prems28(1,3))
                  apply(erule conjE)
                  subgoal premises prems29
                  apply(rule conjI)
                  apply(insert prems29(1,2))[1]
                    apply simp
                  apply(insert prems29(1,3))
                    apply simp
                  done
                done
            apply(rule disjI2)
              apply(erule conjE)
              subgoal premises prems30
              apply(rule conjI)
              apply(insert prems30(1,2))[1]
                apply(erule conjE)
                subgoal premises prems31
                apply(rule conjI)
                apply(insert prems31(1,2))[1]
                  apply simp
                apply(insert prems31(1,3))
                  apply simp
                done
              apply(insert prems30(1,3))
                apply simp
              done
        apply(rule disjI2)
          apply(rule constrained_until2_one_point)
          apply simp
            apply(erule disjE)
            apply(rule disjI1)
              apply(erule conjE)
              subgoal premises prems32
              apply(rule conjI)
              apply(insert prems32(1,2))[1]
                apply simp
              apply(insert prems32(1,3))
                apply(erule conjE)
                subgoal premises prems33
                apply(rule conjI)
                apply(insert prems33(1,2))[1]
                  apply simp
                apply(insert prems33(1,3))
                  apply simp
                done
              done
            apply(rule disjI2)
              apply(erule conjE)
              subgoal premises prems34
              apply(rule conjI)
              apply(insert prems34(1,2))[1]
                apply(erule conjE)
                subgoal premises prems35
                apply(rule conjI)
                apply(insert prems35(1,2))[1]
                  apply simp
                apply(insert prems35(1,3))
                  apply simp
                done
              apply(insert prems34(1,3))
                apply(erule conjE)
                subgoal premises prems36
                apply(rule conjI)
                apply(insert prems36(1,2))[1]
                  apply simp
                apply(insert prems36(1,3))
                  apply simp
                done
              done
  done
apply(insert prems1(1,3,5))
  apply(erule previous_rule)
  apply simp
  apply(rule impI)
  apply(erule impE)
  apply assumption
  subgoal premises prems37
  apply(insert prems37(1,3))
    apply simp
  done
done
done

lemma EDTL_trigger_prev_final_nontemporal_or_tau_delay_trueeinv_imp_req_gen: "
EDTL_trigger_prev_final_nontemporal_or_tau_delay_true_inv finalt b_0 t1_0 t1_1_0 t2_1_0 trigger finale release_1 Inv_1 reaction_1 s0 \<Longrightarrow>
toEnvP s0 \<Longrightarrow>
(True \<and> ((always_imp s0 (\<lambda> r1 . (release_1 s0 r1)) (\<lambda> r1 . (release s0 r1))) \<and> ((((always_imp s0 (\<lambda> r3 . (Inv_1 s0 r3)) (\<lambda> r3 . (Inv s0 r3))) \<and> True) \<and> (((always_imp s0 (\<lambda> r3 . (release_1 s0 r3)) (\<lambda> r3 . (release s0 r3))) \<and> (True \<and> ((always_imp s0 (\<lambda> r3 . (reaction_1 s0 r3)) (\<lambda> r3 . (reaction s0 r3))) \<and> (always_imp s0 (\<lambda> r3 . (Inv_1 s0 r3)) (\<lambda> r3 . (Inv s0 r3)))))) \<and> ((t1_0 s0) <= finalt))) \<and> (((always_imp s0 (\<lambda> r3 . (Inv_1 s0 r3)) (\<lambda> r3 . (Inv s0 r3))) \<and> True) \<and> (((always_imp s0 (\<lambda> r3 . (reaction_1 s0 r3)) (\<lambda> r3 . (reaction s0 r3))) \<and> (always_imp s0 (\<lambda> r3 . (Inv_1 s0 r3)) (\<lambda> r3 . (Inv s0 r3)))) \<and> ((t2_1_0 s0) <= finalt)))))) \<Longrightarrow>
EDTL_trigger_prev_final_nontemporal_or_tau_delay_true finalt trigger finale release Inv reaction s0"

unfolding EDTL_trigger_prev_final_nontemporal_or_tau_delay_true_inv_def EDTL_trigger_prev_final_nontemporal_or_tau_delay_true_def
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
          apply simp
        apply(insert prems4(1,3))
          apply(rule always_disj_rule)
          apply simp
            apply(erule conjE)
            subgoal premises prems5
            apply(rule conjI)
            apply(insert prems5(1,2))[1]
              apply(rule constrained_until_einv2req)
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
                      apply simp
                    apply(insert prems7(1,3))
                      apply(rule always_imp_refl)
                    done
                apply(insert prems6(1,3))
                  apply(erule conjE)
                  subgoal premises prems8
                  apply(rule conjI)
                  apply(insert prems8(1,2))[1]
                    apply(rule always_disj_rule)
                    apply simp
                      apply(erule conjE)
                      subgoal premises prems9
                      apply(rule conjI)
                      apply(insert prems9(1,2))[1]
                        apply simp
                      apply(insert prems9(1,3))
                        apply(rule always_conj_rule)
                        apply simp
                          apply(erule conjE)
                          subgoal premises prems10
                          apply(rule conjI)
                          apply(insert prems10(1,2))[1]
                            apply(rule always_imp_refl)
                          apply(insert prems10(1,3))
                            apply(rule always_conj_rule)
                            apply simp
                              apply(erule conjE)
                              subgoal premises prems11
                              apply(rule conjI)
                              apply(insert prems11(1,2))[1]
                                apply simp
                              apply(insert prems11(1,3))
                                apply simp
                              done
                          done
                      done
                  apply(insert prems8(1,3))
                    apply simp
                  done
                done
            apply(insert prems5(1,3))
              apply(rule constrained_until2_einv2req)
              apply simp
                apply(erule conjE)
                subgoal premises prems12
                apply(rule conjI)
                apply(insert prems12(1,2))[1]
                  apply(rule always_conj_rule)
                  apply simp
                    apply(erule conjE)
                    subgoal premises prems13
                    apply(rule conjI)
                    apply(insert prems13(1,2))[1]
                      apply simp
                    apply(insert prems13(1,3))
                      apply(rule always_imp_refl)
                    done
                apply(insert prems12(1,3))
                  apply(erule conjE)
                  subgoal premises prems14
                  apply(rule conjI)
                  apply(insert prems14(1,2))[1]
                    apply(rule always_conj_rule)
                    apply simp
                      apply(erule conjE)
                      subgoal premises prems15
                      apply(rule conjI)
                      apply(insert prems15(1,2))[1]
                        apply simp
                      apply(insert prems15(1,3))
                        apply simp
                      done
                  apply(insert prems14(1,3))
                    apply simp
                  done
                done
            done
        done
    done
done
done
done

lemma EDTL_trigger_prev_final_nontemporal_or_tau_delay_true_inv_saving: "
EDTL_trigger_prev_final_nontemporal_or_tau_delay_true_inv_part finalt b_0 t1_0 t1_1_0 t2_1_0 trigger finale release Inv reaction s0 \<Longrightarrow>
consecutive s0 s \<Longrightarrow>
((((((t1_0 s0) = 0) \<or> ((((release s) \<or> ((finale s) \<and> ((reaction s) \<and> (Inv s)))) \<and> ((t1_0 s0) <= finalt)) \<or> (((Inv s) \<and> (\<not> (finale s))) \<and> ((t1_0 s0) < (t1_0 s))))) \<and> (((t2_1_0 s0) = 0) \<or> (((t1_1_0 s0) >= (t2_1_0 s0)) \<or> ((((reaction s) \<and> (Inv s)) \<and> ((((t1_1_0 s0) + 1) >= finalt) \<and> ((t2_1_0 s0) <= finalt))) \<or> (((Inv s) \<and> (\<not> (finale s))) \<and> ((((t1_1_0 s0) + 1) >= (t1_1_0 s)) \<and> ((t2_1_0 s0) < (t2_1_0 s)))))))) \<and> ((b_0 s0) \<or> ((release s) \<or> ((((release s) \<or> ((finale s) \<and> ((reaction s) \<and> (Inv s)))) \<or> (((Inv s) \<and> (\<not> (finale s))) \<and> ((t1_0 s) > 0))) \<or> (((finalt = 0) \<and> ((reaction s) \<and> (Inv s))) \<or> (((Inv s) \<and> (\<not> (finale s))) \<and> (((t1_1_0 s) = 0) \<and> ((t2_1_0 s) > 0)))))))) \<and> ((b_0 s) --> (\<not> (trigger s)))) \<Longrightarrow>
EDTL_trigger_prev_final_nontemporal_or_tau_delay_true_inv_part finalt b_0 t1_0 t1_1_0 t2_1_0 trigger finale release Inv reaction s"

unfolding EDTL_trigger_prev_final_nontemporal_or_tau_delay_true_inv_part_def EDTL_trigger_prev_final_nontemporal_or_tau_delay_true_part_def
apply(simp add: EDTL_trigger_prev_final_nontemporal_or_tau_delay_true_inv_saving_gen always_imp_refl)
done

lemma EDTL_trigger_prev_final_nontemporal_or_tau_delay_trueeinv_imp_req: "
EDTL_trigger_prev_final_nontemporal_or_tau_delay_true_inv_part finalt b_0 t1_0 t1_1_0 t2_1_0 trigger finale release Inv reaction s \<Longrightarrow>
toEnvP s \<Longrightarrow>
(((t1_0 s) <= finalt) \<and> ((t2_1_0 s) <= finalt)) \<Longrightarrow>
EDTL_trigger_prev_final_nontemporal_or_tau_delay_true_part finalt trigger finale release Inv reaction s"

unfolding EDTL_trigger_prev_final_nontemporal_or_tau_delay_true_inv_part_def EDTL_trigger_prev_final_nontemporal_or_tau_delay_true_part_def
apply(simp add: EDTL_trigger_prev_final_nontemporal_or_tau_delay_trueeinv_imp_req_gen always_imp_refl)
done



lemmas EDTL_trigger_prev_final_nontemporal_or_tau_delay_true_used_patterns = EDTL_trigger_prev_final_nontemporal_or_tau_delay_true_def always_used_patterns weak_previous_def constrained_until_def constrained_until2_def 

lemmas EDTL_trigger_prev_final_nontemporal_or_tau_delay_true_inv_used_patterns = EDTL_trigger_prev_final_nontemporal_or_tau_delay_true_inv_def always_inv_used_patterns weak_previous_def constrained_until_inv_def constrained_until2_inv_def previous_inv_def 

lemmas EDTL_trigger_prev_final_nontemporal_or_tau_delay_true_inv_part_used_patterns = EDTL_trigger_prev_final_nontemporal_or_tau_delay_true_inv_part_def EDTL_trigger_prev_final_nontemporal_or_tau_delay_true_inv_used_patterns

lemmas EDTL_trigger_prev_final_nontemporal_or_tau_delay_true_part_used_patterns = EDTL_trigger_prev_final_nontemporal_or_tau_delay_true_part_def EDTL_trigger_prev_final_nontemporal_or_tau_delay_true_used_patterns

definition EDTL_release_false_final_tau_delay_tau where "EDTL_release_false_final_tau_delay_tau fin delay trigger Inv reaction s \<equiv> (always (\<lambda> r2 r1 . ((\<not> (trigger r1)) \<or> (constrained_until2 fin (fin + delay) Inv (\<lambda> r4 r3 . ((reaction r4 r3) \<and> (Inv r4 r3))) r2 r1))) s)"

definition EDTL_release_false_final_tau_delay_tau_part where "EDTL_release_false_final_tau_delay_tau_part fin delay trigger Inv reaction s \<equiv> (EDTL_release_false_final_tau_delay_tau fin delay trigger (\<lambda> s s1 . (Inv s1)) (\<lambda> s s1 . (reaction s1)) s)"

definition EDTL_release_false_final_tau_delay_tau_inv where "EDTL_release_false_final_tau_delay_tau_inv fin delay t1_1_0 t2_1_0 trigger Inv_1 reaction_1 s \<equiv> (always_inv (\<lambda> r2 r1 . ((\<not> (trigger r1)) \<or> (constrained_until2_inv fin (fin + delay) t1_1_0 t2_1_0 Inv_1 (\<lambda> r4 r3 . ((reaction_1 r4 r3) \<and> (Inv_1 r4 r3))) r2 r1))) s)"

definition EDTL_release_false_final_tau_delay_tau_inv_part where "EDTL_release_false_final_tau_delay_tau_inv_part fin delay t1_1_0 t2_1_0 trigger Inv reaction s \<equiv> (EDTL_release_false_final_tau_delay_tau_inv fin delay t1_1_0 t2_1_0 trigger (\<lambda> s s1 . (Inv s1)) (\<lambda> s s1 . (reaction s1)) s)"

lemma EDTL_release_false_final_tau_delay_tau_inv_saving_gen: "
EDTL_release_false_final_tau_delay_tau_inv fin delay t1_1_0 t2_1_0 trigger Inv_1 reaction_1 s0 \<Longrightarrow>
consecutive s0 s \<Longrightarrow>
((True \<and> ((always_imp s0 (Inv_1 s0) (Inv_1 s)) \<and> (((always_imp s0 (\<lambda> r3 . (reaction_1 s0 r3)) (\<lambda> r3 . (reaction_1 s r3))) \<and> (always_imp s0 (\<lambda> r3 . (Inv_1 s0 r3)) (\<lambda> r3 . (Inv_1 s r3)))) \<and> (((t2_1_0 s0) = 0) \<or> (((t1_1_0 s0) >= (t2_1_0 s0)) \<or> ((((reaction_1 s s) \<and> (Inv_1 s s)) \<and> ((((t1_1_0 s0) + 1) >= fin) \<and> ((t2_1_0 s0) <= (fin + delay)))) \<or> ((Inv_1 s s) \<and> ((((t1_1_0 s0) + 1) >= (t1_1_0 s)) \<and> ((t2_1_0 s0) < (t2_1_0 s)))))))))) \<and> ((\<not> (trigger s)) \<or> (((fin = 0) \<and> ((reaction_1 s s) \<and> (Inv_1 s s))) \<or> ((Inv_1 s s) \<and> (((t1_1_0 s) = 0) \<and> ((t2_1_0 s) > 0)))))) \<Longrightarrow>
EDTL_release_false_final_tau_delay_tau_inv fin delay t1_1_0 t2_1_0 trigger Inv_1 reaction_1 s"

unfolding EDTL_release_false_final_tau_delay_tau_inv_def
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
        apply(rule constrained_until2_rule)
        apply simp
          apply(erule conjE)
          subgoal premises prems3
          apply(rule conjI)
          apply(insert prems3(1,2))[1]
            apply simp
          apply(insert prems3(1,3))
            apply(erule conjE)
            subgoal premises prems4
            apply(rule conjI)
            apply(insert prems4(1,2))[1]
              apply(rule always_conj_rule)
              apply simp
                apply(erule conjE)
                subgoal premises prems5
                apply(rule conjI)
                apply(insert prems5(1,2))[1]
                  apply simp
                apply(insert prems5(1,3))
                  apply simp
                done
            apply(insert prems4(1,3))
              apply(erule disjE)
              apply(rule disjI1)
                apply simp
              apply(rule disjI2)
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
                      apply(erule conjE)
                      subgoal premises prems7
                      apply(rule conjI)
                      apply(insert prems7(1,2))[1]
                        apply simp
                      apply(insert prems7(1,3))
                        apply simp
                      done
                    apply(insert prems6(1,3))
                      apply(erule conjE)
                      subgoal premises prems8
                      apply(rule conjI)
                      apply(insert prems8(1,2))[1]
                        apply simp
                      apply(insert prems8(1,3))
                        apply simp
                      done
                    done
                  apply(rule disjI2)
                    apply(erule conjE)
                    subgoal premises prems9
                    apply(rule conjI)
                    apply(insert prems9(1,2))[1]
                      apply simp
                    apply(insert prems9(1,3))
                      apply(erule conjE)
                      subgoal premises prems10
                      apply(rule conjI)
                      apply(insert prems10(1,2))[1]
                        apply simp
                      apply(insert prems10(1,3))
                        apply simp
                      done
                    done
            done
          done
      done
  apply(insert prems1(1,3))
    apply(erule disjE)
    apply(rule disjI1)
      apply simp
    apply(rule disjI2)
      apply(rule constrained_until2_one_point)
      apply simp
        apply(erule disjE)
        apply(rule disjI1)
          apply(erule conjE)
          subgoal premises prems11
          apply(rule conjI)
          apply(insert prems11(1,2))[1]
            apply simp
          apply(insert prems11(1,3))
            apply(erule conjE)
            subgoal premises prems12
            apply(rule conjI)
            apply(insert prems12(1,2))[1]
              apply simp
            apply(insert prems12(1,3))
              apply simp
            done
          done
        apply(rule disjI2)
          apply(erule conjE)
          subgoal premises prems13
          apply(rule conjI)
          apply(insert prems13(1,2))[1]
            apply simp
          apply(insert prems13(1,3))
            apply(erule conjE)
            subgoal premises prems14
            apply(rule conjI)
            apply(insert prems14(1,2))[1]
              apply simp
            apply(insert prems14(1,3))
              apply simp
            done
          done
  done
done

lemma EDTL_release_false_final_tau_delay_taueinv_imp_req_gen: "
EDTL_release_false_final_tau_delay_tau_inv fin delay t1_1_0 t2_1_0 trigger Inv_1 reaction_1 s0 \<Longrightarrow>
toEnvP s0 \<Longrightarrow>
(True \<and> ((always_imp s0 (Inv_1 s0) (Inv s0)) \<and> (((always_imp s0 (\<lambda> r3 . (reaction_1 s0 r3)) (\<lambda> r3 . (reaction s0 r3))) \<and> (always_imp s0 (\<lambda> r3 . (Inv_1 s0 r3)) (\<lambda> r3 . (Inv s0 r3)))) \<and> ((t2_1_0 s0) <= (fin + delay))))) \<Longrightarrow>
EDTL_release_false_final_tau_delay_tau fin delay trigger Inv reaction s0"

unfolding EDTL_release_false_final_tau_delay_tau_inv_def EDTL_release_false_final_tau_delay_tau_def
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
      apply(rule constrained_until2_einv2req)
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
            apply(rule always_conj_rule)
            apply simp
              apply(erule conjE)
              subgoal premises prems6
              apply(rule conjI)
              apply(insert prems6(1,2))[1]
                apply simp
              apply(insert prems6(1,3))
                apply simp
              done
          apply(insert prems5(1,3))
            apply simp
          done
        done
    done
done

lemma EDTL_release_false_final_tau_delay_tau_inv_saving: "
EDTL_release_false_final_tau_delay_tau_inv_part fin delay t1_1_0 t2_1_0 trigger Inv reaction s0 \<Longrightarrow>
consecutive s0 s \<Longrightarrow>
((((t2_1_0 s0) = 0) \<or> (((t1_1_0 s0) >= (t2_1_0 s0)) \<or> ((((reaction s) \<and> (Inv s)) \<and> ((((t1_1_0 s0) + 1) >= fin) \<and> ((t2_1_0 s0) <= (fin + delay)))) \<or> ((Inv s) \<and> ((((t1_1_0 s0) + 1) >= (t1_1_0 s)) \<and> ((t2_1_0 s0) < (t2_1_0 s))))))) \<and> ((\<not> (trigger s)) \<or> (((fin = 0) \<and> ((reaction s) \<and> (Inv s))) \<or> ((Inv s) \<and> (((t1_1_0 s) = 0) \<and> ((t2_1_0 s) > 0)))))) \<Longrightarrow>
EDTL_release_false_final_tau_delay_tau_inv_part fin delay t1_1_0 t2_1_0 trigger Inv reaction s"

unfolding EDTL_release_false_final_tau_delay_tau_inv_part_def EDTL_release_false_final_tau_delay_tau_part_def
apply(simp add: EDTL_release_false_final_tau_delay_tau_inv_saving_gen always_imp_refl)
done

lemma EDTL_release_false_final_tau_delay_taueinv_imp_req: "
EDTL_release_false_final_tau_delay_tau_inv_part fin delay t1_1_0 t2_1_0 trigger Inv reaction s \<Longrightarrow>
toEnvP s \<Longrightarrow>
((t2_1_0 s) <= (fin + delay)) \<Longrightarrow>
EDTL_release_false_final_tau_delay_tau_part fin delay trigger Inv reaction s"

unfolding EDTL_release_false_final_tau_delay_tau_inv_part_def EDTL_release_false_final_tau_delay_tau_part_def
apply(simp add: EDTL_release_false_final_tau_delay_taueinv_imp_req_gen always_imp_refl)
done



lemmas EDTL_release_false_final_tau_delay_tau_used_patterns = EDTL_release_false_final_tau_delay_tau_def always_used_patterns constrained_until2_def 

lemmas EDTL_release_false_final_tau_delay_tau_inv_used_patterns = EDTL_release_false_final_tau_delay_tau_inv_def always_inv_used_patterns constrained_until2_inv_def 

lemmas EDTL_release_false_final_tau_delay_tau_inv_part_used_patterns = EDTL_release_false_final_tau_delay_tau_inv_part_def EDTL_release_false_final_tau_delay_tau_inv_used_patterns

lemmas EDTL_release_false_final_tau_delay_tau_part_used_patterns = EDTL_release_false_final_tau_delay_tau_part_def EDTL_release_false_final_tau_delay_tau_used_patterns

definition EDTL_trigger_prev_release_false_final_tau_delay_tau where "EDTL_trigger_prev_release_false_final_tau_delay_tau fin delay trigger Inv reaction s \<equiv> (always (\<lambda> r2 r1 . ((weak_previous (\<lambda> r4 r3 . (\<not> (trigger r3))) r2 r1) \<or> (constrained_until2 fin (fin + delay) Inv (\<lambda> r4 r3 . ((reaction r4 r3) \<and> (Inv r4 r3))) r2 r1))) s)"

definition EDTL_trigger_prev_release_false_final_tau_delay_tau_part where "EDTL_trigger_prev_release_false_final_tau_delay_tau_part fin delay trigger Inv reaction s \<equiv> (EDTL_trigger_prev_release_false_final_tau_delay_tau fin delay trigger (\<lambda> s s1 . (Inv s1)) (\<lambda> s s1 . (reaction s1)) s)"

definition EDTL_trigger_prev_release_false_final_tau_delay_tau_inv where "EDTL_trigger_prev_release_false_final_tau_delay_tau_inv fin delay b_0 t1_1_0 t2_1_0 trigger Inv_1 reaction_1 s \<equiv> ((always_inv (\<lambda> r2 r1 . ((weak_previous (\<lambda> r4 r3 . (\<not> (trigger r3))) r2 r1) \<or> (constrained_until2_inv fin (fin + delay) t1_1_0 t2_1_0 Inv_1 (\<lambda> r4 r3 . ((reaction_1 r4 r3) \<and> (Inv_1 r4 r3))) r2 r1))) s) \<and> (previous_inv b_0 (\<lambda> r4 r3 . (\<not> (trigger r3))) s))"

definition EDTL_trigger_prev_release_false_final_tau_delay_tau_inv_part where "EDTL_trigger_prev_release_false_final_tau_delay_tau_inv_part fin delay b_0 t1_1_0 t2_1_0 trigger Inv reaction s \<equiv> (EDTL_trigger_prev_release_false_final_tau_delay_tau_inv fin delay b_0 t1_1_0 t2_1_0 trigger (\<lambda> s s1 . (Inv s1)) (\<lambda> s s1 . (reaction s1)) s)"

lemma EDTL_trigger_prev_release_false_final_tau_delay_tau_inv_saving_gen: "
EDTL_trigger_prev_release_false_final_tau_delay_tau_inv fin delay b_0 t1_1_0 t2_1_0 trigger Inv_1 reaction_1 s0 \<Longrightarrow>
consecutive s0 s \<Longrightarrow>
(((True \<and> ((always_imp s0 (Inv_1 s0) (Inv_1 s)) \<and> (((always_imp s0 (\<lambda> r3 . (reaction_1 s0 r3)) (\<lambda> r3 . (reaction_1 s r3))) \<and> (always_imp s0 (\<lambda> r3 . (Inv_1 s0 r3)) (\<lambda> r3 . (Inv_1 s r3)))) \<and> (((t2_1_0 s0) = 0) \<or> (((t1_1_0 s0) >= (t2_1_0 s0)) \<or> ((((reaction_1 s s) \<and> (Inv_1 s s)) \<and> ((((t1_1_0 s0) + 1) >= fin) \<and> ((t2_1_0 s0) <= (fin + delay)))) \<or> ((Inv_1 s s) \<and> ((((t1_1_0 s0) + 1) >= (t1_1_0 s)) \<and> ((t2_1_0 s0) < (t2_1_0 s)))))))))) \<and> (((b_0 s0) \<and> True) \<or> (((fin = 0) \<and> ((reaction_1 s s) \<and> (Inv_1 s s))) \<or> ((Inv_1 s s) \<and> (((t1_1_0 s) = 0) \<and> ((t2_1_0 s) > 0)))))) \<and> ((b_0 s) --> (\<not> (trigger s)))) \<Longrightarrow>
EDTL_trigger_prev_release_false_final_tau_delay_tau_inv fin delay b_0 t1_1_0 t2_1_0 trigger Inv_1 reaction_1 s"

unfolding EDTL_trigger_prev_release_false_final_tau_delay_tau_inv_def
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
        apply(rule constrained_until2_rule)
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
              apply(rule always_conj_rule)
              apply simp
                apply(erule conjE)
                subgoal premises prems6
                apply(rule conjI)
                apply(insert prems6(1,2))[1]
                  apply simp
                apply(insert prems6(1,3))
                  apply simp
                done
            apply(insert prems5(1,3))
              apply(erule disjE)
              apply(rule disjI1)
                apply simp
              apply(rule disjI2)
                apply(erule disjE)
                apply(rule disjI1)
                  apply simp
                apply(rule disjI2)
                  apply(erule disjE)
                  apply(rule disjI1)
                    apply(erule conjE)
                    subgoal premises prems7
                    apply(rule conjI)
                    apply(insert prems7(1,2))[1]
                      apply(erule conjE)
                      subgoal premises prems8
                      apply(rule conjI)
                      apply(insert prems8(1,2))[1]
                        apply simp
                      apply(insert prems8(1,3))
                        apply simp
                      done
                    apply(insert prems7(1,3))
                      apply(erule conjE)
                      subgoal premises prems9
                      apply(rule conjI)
                      apply(insert prems9(1,2))[1]
                        apply simp
                      apply(insert prems9(1,3))
                        apply simp
                      done
                    done
                  apply(rule disjI2)
                    apply(erule conjE)
                    subgoal premises prems10
                    apply(rule conjI)
                    apply(insert prems10(1,2))[1]
                      apply simp
                    apply(insert prems10(1,3))
                      apply(erule conjE)
                      subgoal premises prems11
                      apply(rule conjI)
                      apply(insert prems11(1,2))[1]
                        apply simp
                      apply(insert prems11(1,3))
                        apply simp
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
        subgoal premises prems12
        apply(rule conjI)
        apply(insert prems12(1,2))[1]
          apply simp
        apply(insert prems12(1,3))
          apply(rule always_imp_refl)
        done
    apply(rule disjI2)
      apply(rule constrained_until2_one_point)
      apply simp
        apply(erule disjE)
        apply(rule disjI1)
          apply(erule conjE)
          subgoal premises prems13
          apply(rule conjI)
          apply(insert prems13(1,2))[1]
            apply simp
          apply(insert prems13(1,3))
            apply(erule conjE)
            subgoal premises prems14
            apply(rule conjI)
            apply(insert prems14(1,2))[1]
              apply simp
            apply(insert prems14(1,3))
              apply simp
            done
          done
        apply(rule disjI2)
          apply(erule conjE)
          subgoal premises prems15
          apply(rule conjI)
          apply(insert prems15(1,2))[1]
            apply simp
          apply(insert prems15(1,3))
            apply(erule conjE)
            subgoal premises prems16
            apply(rule conjI)
            apply(insert prems16(1,2))[1]
              apply simp
            apply(insert prems16(1,3))
              apply simp
            done
          done
  done
apply(insert prems1(1,3,5))
  apply(erule previous_rule)
  apply simp
  apply(rule impI)
  apply(erule impE)
  apply assumption
  subgoal premises prems17
  apply(insert prems17(1,3))
    apply simp
  done
done
done

lemma EDTL_trigger_prev_release_false_final_tau_delay_taueinv_imp_req_gen: "
EDTL_trigger_prev_release_false_final_tau_delay_tau_inv fin delay b_0 t1_1_0 t2_1_0 trigger Inv_1 reaction_1 s0 \<Longrightarrow>
toEnvP s0 \<Longrightarrow>
(True \<and> ((always_imp s0 (Inv_1 s0) (Inv s0)) \<and> (((always_imp s0 (\<lambda> r3 . (reaction_1 s0 r3)) (\<lambda> r3 . (reaction s0 r3))) \<and> (always_imp s0 (\<lambda> r3 . (Inv_1 s0 r3)) (\<lambda> r3 . (Inv s0 r3)))) \<and> ((t2_1_0 s0) <= (fin + delay))))) \<Longrightarrow>
EDTL_trigger_prev_release_false_final_tau_delay_tau fin delay trigger Inv reaction s0"

unfolding EDTL_trigger_prev_release_false_final_tau_delay_tau_inv_def EDTL_trigger_prev_release_false_final_tau_delay_tau_def
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
      apply(rule constrained_until2_einv2req)
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
            apply(rule always_conj_rule)
            apply simp
              apply(erule conjE)
              subgoal premises prems6
              apply(rule conjI)
              apply(insert prems6(1,2))[1]
                apply simp
              apply(insert prems6(1,3))
                apply simp
              done
          apply(insert prems5(1,3))
            apply simp
          done
        done
    done
done
done
done

lemma EDTL_trigger_prev_release_false_final_tau_delay_tau_inv_saving: "
EDTL_trigger_prev_release_false_final_tau_delay_tau_inv_part fin delay b_0 t1_1_0 t2_1_0 trigger Inv reaction s0 \<Longrightarrow>
consecutive s0 s \<Longrightarrow>
(((((t2_1_0 s0) = 0) \<or> (((t1_1_0 s0) >= (t2_1_0 s0)) \<or> ((((reaction s) \<and> (Inv s)) \<and> ((((t1_1_0 s0) + 1) >= fin) \<and> ((t2_1_0 s0) <= (fin + delay)))) \<or> ((Inv s) \<and> ((((t1_1_0 s0) + 1) >= (t1_1_0 s)) \<and> ((t2_1_0 s0) < (t2_1_0 s))))))) \<and> ((b_0 s0) \<or> (((fin = 0) \<and> ((reaction s) \<and> (Inv s))) \<or> ((Inv s) \<and> (((t1_1_0 s) = 0) \<and> ((t2_1_0 s) > 0)))))) \<and> ((b_0 s) --> (\<not> (trigger s)))) \<Longrightarrow>
EDTL_trigger_prev_release_false_final_tau_delay_tau_inv_part fin delay b_0 t1_1_0 t2_1_0 trigger Inv reaction s"

unfolding EDTL_trigger_prev_release_false_final_tau_delay_tau_inv_part_def EDTL_trigger_prev_release_false_final_tau_delay_tau_part_def
apply(simp add: EDTL_trigger_prev_release_false_final_tau_delay_tau_inv_saving_gen always_imp_refl)
done

lemma EDTL_trigger_prev_release_false_final_tau_delay_taueinv_imp_req: "
EDTL_trigger_prev_release_false_final_tau_delay_tau_inv_part fin delay b_0 t1_1_0 t2_1_0 trigger Inv reaction s \<Longrightarrow>
toEnvP s \<Longrightarrow>
((t2_1_0 s) <= (fin + delay)) \<Longrightarrow>
EDTL_trigger_prev_release_false_final_tau_delay_tau_part fin delay trigger Inv reaction s"

unfolding EDTL_trigger_prev_release_false_final_tau_delay_tau_inv_part_def EDTL_trigger_prev_release_false_final_tau_delay_tau_part_def
apply(simp add: EDTL_trigger_prev_release_false_final_tau_delay_taueinv_imp_req_gen always_imp_refl)
done



lemmas EDTL_trigger_prev_release_false_final_tau_delay_tau_used_patterns = EDTL_trigger_prev_release_false_final_tau_delay_tau_def always_used_patterns weak_previous_def constrained_until2_def 

lemmas EDTL_trigger_prev_release_false_final_tau_delay_tau_inv_used_patterns = EDTL_trigger_prev_release_false_final_tau_delay_tau_inv_def always_inv_used_patterns weak_previous_def constrained_until2_inv_def previous_inv_def 

lemmas EDTL_trigger_prev_release_false_final_tau_delay_tau_inv_part_used_patterns = EDTL_trigger_prev_release_false_final_tau_delay_tau_inv_part_def EDTL_trigger_prev_release_false_final_tau_delay_tau_inv_used_patterns

lemmas EDTL_trigger_prev_release_false_final_tau_delay_tau_part_used_patterns = EDTL_trigger_prev_release_false_final_tau_delay_tau_part_def EDTL_trigger_prev_release_false_final_tau_delay_tau_used_patterns

end
