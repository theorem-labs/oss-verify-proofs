(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import InitMem SysStep Image SFW1_lemmas Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import MallocRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlBuf YajlLeaf YajlLex YajlFactsLex YajlFactsBuf YajlFactsDecode.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RY_lib RY_lex_number.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages LazyModel NodesA Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import B_iface BYajlRep BYajl_iface BY_ubkit BY_rz BY_lex_rdck BY_lex_rdck2 BY_lex_rdck3 BY_lex_kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac aceil := first [pose proof alloc_ceiling_range as CEILB | idtac].
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma lor32_eE : forall c, 0 <= c < 256 -> (Z.lor c 32 =? 101) = (c =? c_e) || (c =? c_E).
Proof. aceil.
  intros c Hc. unfold c_e, c_E.
  pose proof (byte_forall (fun c => Bool.eqb (Z.lor c 32 =? 101) ((c =? 101) || (c =? 69))) ltac:(vm_compute; reflexivity) c Hc) as H.
  cbn beta in H. apply Bool.eqb_prop in H. exact H.
Qed.

Section S.
Variable K : alexK.
Variable m0 : mem.
Hypothesis ENV : kenvA K.
Hypothesis KP : kpolA K.
Hypothesis SH : alexsh K m0.

Ltac pols := polu KP kp_Ls PLS; polu KP kp_L PL; polu KP kp_T PT; polu KP kp_Hs PHS; polu KP kp_H PH; polu KP kp_stk PSTK.
Ltac prep LM BC := pose proof LM as (MU & WM & MI & ST & FR & OFF & LX & BC); lex_prep ENV BC; pols.

(* [comment removed for export] *)
Definition dig_post (e start : Z) (Q : Z -> Z -> machine_state -> Prop) (r : rdres) : machine_state -> Prop :=
  match r with
  | RD_eof => fun ms' => exists s11v, alex_at K m0 J_EOF s11v e (zlength (k_txt K)) start ms'
  | RD_char c o => Q c o
  end.

(* [comment removed for export] *)
Lemma num_final : forall (rav s1v s2v s6v s9v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 k56 k64 : word)
    (m : mem) (e off start tokc : Z),
  alexmem K m0 m e off start k56 k64 (wz 3) -> 0 < off <= zlength (k_txt K) ->
  evtA bsegs (k_P K) (alex_at K m0 J_TOK (wz tokc) e (off - 1) start)
    (MS (mkR rav (wz (kSQ K)) (k_gp K) (k_tp K) t0 t1 t2 (wz (k_H K + 32)) s1v a0 a1 a2 a3 a4 a5 a6 a7
          s2v (wz (k_L K + 16)) (wz (k_L K + 24)) (wz ((k_H K + 32) / 8 + ASB)) s6v (wz (k_T K)) (wz (zlength (k_txt K))) s9v (wz ASB) (wz tokc)
          t3 t4 t5 t6)
        (k_F K) (wz 0x86024) (k_fc K) None m (seg_rom bsegs)).
Proof. aceil.
  intros until tokc. intros LM BO. prep LM BC.
  shld (rd_shH K m0 _ ENV SH MU WM 32 ltac:(lia)). zstepA. try if_false.     (* [comment removed for export] *)
  zstepA. rewrite ?ysx32_small by lia.                                       (* [comment removed for export] *)
  zstepA. if_cases K0; zify_cond K0. 1:{ kill K0. } clear K0.                (* [comment removed for export] *)
  shld (rd_shH K m0 _ ENV SH MU WM 32 ltac:(lia)). zstepA. try if_false.     (* [comment removed for export] *)
  zstepA. zstoreA ENV. stepA.                                                (* [comment removed for export] *)
  replace (off + -1) with (off - 1) in OFF by lia. fin_at.
Qed.

(* [comment removed for export] *)
Lemma exp_loop : forall (fuel : nat) (rav s1v s2v s9v s11v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 k56 k64 : word)
    (m : mem) (e off start : Z),
  alexmem K m0 m e off start k56 k64 (wz 3) -> 0 <= off <= zlength (k_txt K) -> (Z.to_nat (zlength (k_txt K) - off) < fuel)%nat ->
  evtA bsegs (k_P K) (dig_post e start (fun c o => alex_at K m0 J_TOK (wz 11) e (o - 1) start)
                        (read_past_digits fuel (k_txt K) (zlength (k_txt K)) off))
    (MS (mkR rav (wz (kSQ K)) (k_gp K) (k_tp K) t0 t1 t2 (wz (k_H K + 32)) s1v a0 a1 a2 a3 a4 a5 a6 a7
          s2v (wz (k_L K + 16)) (wz (k_L K + 24)) (wz ((k_H K + 32) / 8 + ASB)) (wz 10) (wz (k_T K)) (wz (zlength (k_txt K))) s9v (wz ASB) s11v
          t3 t4 t5 t6)
        (k_F K) (wz 0x85e6c) (k_fc K) None m (seg_rom bsegs)).
Proof. aceil.
  induction fuel as [|fuel IH]; intros until start; intros LM BO FUEL; [lia|]. prep LM BC.
  cbn [read_past_digits]. unfold read1.
  eofchkA K m0 ENV SH MU WM K0.
  - (* [comment removed for export] *)
    replace (zlength (k_txt K) <=? off) with true by (symmetry; apply Z.leb_le; lia). cbn [dig_post].
    assert (E : off = zlength (k_txt K)) by lia. rewrite E in OFF. fin_at.
  - replace (zlength (k_txt K) <=? off) with false by (symmetry; apply Z.leb_gt; lia).
    rdcharA K m0 ENV KP SH MU WM rdck_10c078 off.
    zstepA. zstepA. if_cases K1; zify_cond K1; digk K1.                     (* [comment removed for export] *)
    + rewrite (is_digit_true (znth (k_txt K) off)) by lia.
      eapply IH; [fin_lexmem| lia| lia].
    + rewrite (is_digit_false (znth (k_txt K) off)) by lia. cbn [dig_post].
      stepA. stepA.                                                          (* [comment removed for export] *)
      eapply num_final; [fin_lexmem| lia].
    + rewrite (is_digit_false (znth (k_txt K) off)) by lia. cbn [dig_post].
      stepA. stepA.
      eapply num_final; [fin_lexmem| lia].
Qed.

Lemma dig_post_exp : forall e start r ms,
  dig_post e start (fun c o => alex_at K m0 J_TOK (wz 11) e (o - 1) start) r ms ->
  sub_post K m0 e start (num_tail (match r with RD_eof => inr (TK_eof, zlength (k_txt K), @None lex_error)
                                              | RD_char c o => inl (c, o, TK_double) end)) ms.
Proof. aceil. intros e start [|c o] ms H; exact H. Qed.

(* [comment removed for export] *)
Lemma num_expdig_walk : forall (rav s1v s2v s6v s9v s11v t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 k56 k64 : word)
    (m : mem) (e o1 start c1 : Z),
  alexmem K m0 m e o1 start k56 k64 (wz 3) -> 0 < o1 <= zlength (k_txt K) -> 0 <= c1 < 256 ->
  evtA bsegs (k_P K) (sub_post K m0 e start (num_tail
        (if is_digit c1 then
           match read_past_digits (lex_fuel (zlength (k_txt K)) o1) (k_txt K) (zlength (k_txt K)) o1 with
           | RD_eof => inr (TK_eof, zlength (k_txt K), None)
           | RD_char c off => inl (c, off, TK_double)
           end
         else inr (TK_error, o1 - 1, Some LE_missing_integer_after_exponent))))
    (MS (mkR rav (wz (kSQ K)) (k_gp K) (k_tp K) t0 t1 t2 (wz (k_H K + 32)) s1v (wz c1) a1 a2 a3 a4 a5 a6 a7
          s2v (wz (k_L K + 16)) (wz (k_L K + 24)) (wz ((k_H K + 32) / 8 + ASB)) s6v (wz (k_T K)) (wz (zlength (k_txt K))) s9v (wz ASB) s11v
          t3 t4 t5 t6)
        (k_F K) (wz 0x85e44) (k_fc K) None m (seg_rom bsegs)).
Proof. aceil.
  intros until c1. intros LM BO CR1. prep LM BC.
  zstepA. stepA. zstepA. if_cases K4; zify_cond K4; digk K4.                (* [comment removed for export] *)
  - (* [comment removed for export] *)
    rewrite (is_digit_false c1) by lia. cbn [num_tail sub_post err_upd lex_error_code tok_code].
    shld (rd_shH K m0 _ ENV SH MU WM 32 ltac:(lia)). zstepA. try if_false.
    zstepA. rewrite ?ysx32_small by lia.
    zstepA. if_cases KU; zify_cond KU. 1:{ kill KU. } clear KU.
    shld (rd_shH K m0 _ ENV SH MU WM 32 ltac:(lia)). zstepA. try if_false.
    zstepA. zstoreA ENV. stepA.                                              (* [comment removed for export] *)
    zstepA. zstepA. zstepA. shadow_addr. zstepA.                               (* [comment removed for export] *)
    shld (rd_shL K m0 _ ENV SH MU WM 8 ltac:(lia)). zstepA. try if_false.     (* [comment removed for export] *)
    stepA. stepA. zstoreA ENV. stepA.                                        (* [comment removed for export] *)
    replace (o1 + -1) with (o1 - 1) in OFF by lia. fin_at.
  - rewrite (is_digit_false c1) by lia. cbn [num_tail sub_post err_upd lex_error_code tok_code].
    shld (rd_shH K m0 _ ENV SH MU WM 32 ltac:(lia)). zstepA. try if_false.
    zstepA. rewrite ?ysx32_small by lia.
    zstepA. if_cases KU; zify_cond KU. 1:{ kill KU. } clear KU.
    shld (rd_shH K m0 _ ENV SH MU WM 32 ltac:(lia)). zstepA. try if_false.
    zstepA. zstoreA ENV. stepA.
    zstepA. zstepA. zstepA. shadow_addr. zstepA.
    shld (rd_shL K m0 _ ENV SH MU WM 8 ltac:(lia)). zstepA. try if_false.
    stepA. stepA. zstoreA ENV. stepA.
    replace (o1 + -1) with (o1 - 1) in OFF by lia. fin_at.
  - (* [comment removed for export] *)
    rewrite (is_digit_true c1) by lia.
    stepA. zstepA. zstepA. zstepA. zstepA. zstepA. zstepA.                   (* [comment removed for export] *)
    eapply evtA_mono; [eapply (exp_loop (lex_fuel (zlength (k_txt K)) o1)); [fin_lexmem| lia| unfold lex_fuel; lia]|].
    intros ms Hs. exact (dig_post_exp _ _ _ _ Hs).
Qed.

(* [comment removed for export] *)
Lemma num_exp_walk : forall (rav s1v s2v s6v s9v s11v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 k56 k64 : word)
    (m : mem) (e off start : Z),
  alexmem K m0 m e off start k56 k64 (wz 3) -> 0 <= off <= zlength (k_txt K) ->
  evtA bsegs (k_P K) (sub_post K m0 e start (num_tail (num_exp (k_txt K) (zlength (k_txt K)) off)))
    (MS (mkR rav (wz (kSQ K)) (k_gp K) (k_tp K) t0 t1 t2 (wz (k_H K + 32)) s1v a0 a1 a2 a3 a4 a5 a6 a7
          s2v (wz (k_L K + 16)) (wz (k_L K + 24)) (wz ((k_H K + 32) / 8 + ASB)) s6v (wz (k_T K)) (wz (zlength (k_txt K))) s9v (wz ASB) s11v
          t3 t4 t5 t6)
        (k_F K) (wz 0x85518) (k_fc K) None m (seg_rom bsegs)).
Proof. aceil.
  intros until start. intros LM BO. prep LM BC.
  unfold num_exp, read1.
  eofchkA K m0 ENV SH MU WM K0.
  - replace (zlength (k_txt K) <=? off) with true by (symmetry; apply Z.leb_le; lia). cbn [num_tail sub_post err_upd].
    assert (E : off = zlength (k_txt K)) by lia. rewrite E in OFF. fin_at.
  - replace (zlength (k_txt K) <=? off) with false by (symmetry; apply Z.leb_gt; lia).
    rdcharA K m0 ENV KP SH MU WM rdck_b858f0 off.
    stepA. zstepA. if_cases K1; zify_cond K1.                                (* [comment removed for export] *)
    + (* [comment removed for export] *)
      replace ((znth (k_txt K) off =? c_plus) || (znth (k_txt K) off =? c_minus)) with true
        by (symmetry; apply orb_true_iff; right; apply Z.eqb_eq; unfold c_minus; lia).
      eofchkA K m0 ENV SH MU WM K2.
      * replace (zlength (k_txt K) <=? off + 1) with true by (symmetry; apply Z.leb_le; lia). cbn [num_tail sub_post err_upd].
        assert (E : off + 1 = zlength (k_txt K)) by lia. rewrite E in OFF. fin_at.
      * replace (zlength (k_txt K) <=? off + 1) with false by (symmetry; apply Z.leb_gt; lia).
        rdcharA K m0 ENV KP SH MU WM rdck_b85e10 (off + 1).
        eapply num_expdig_walk; [fin_lexmem| lia| lia].
    + stepA. zstepA. if_cases K2; zify_cond K2.                              (* [comment removed for export] *)
      * (* [comment removed for export] *)
        replace ((znth (k_txt K) off =? c_plus) || (znth (k_txt K) off =? c_minus)) with false
          by (symmetry; apply orb_false_iff; split; apply Z.eqb_neq; unfold c_plus, c_minus; lia).
        eapply num_expdig_walk; [fin_lexmem| lia| lia].
      * (* [comment removed for export] *)
        replace ((znth (k_txt K) off =? c_plus) || (znth (k_txt K) off =? c_minus)) with true
          by (symmetry; apply orb_true_iff; left; apply Z.eqb_eq; unfold c_plus; lia).
        eofchkA K m0 ENV SH MU WM K3.
        -- replace (zlength (k_txt K) <=? off + 1) with true by (symmetry; apply Z.leb_le; lia). cbn [num_tail sub_post err_upd].
           assert (E : off + 1 = zlength (k_txt K)) by lia. rewrite E in OFF. fin_at.
        -- replace (zlength (k_txt K) <=? off + 1) with false by (symmetry; apply Z.leb_gt; lia).
           rdcharA K m0 ENV KP SH MU WM rdck_b85e10 (off + 1).
           eapply num_expdig_walk; [fin_lexmem| lia| lia].
Qed.
End S.
End RC__1.
