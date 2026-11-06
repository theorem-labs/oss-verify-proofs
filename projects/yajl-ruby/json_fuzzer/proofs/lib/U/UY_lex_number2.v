(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel SFW1_lemmas InitMem Arr Frame.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Images.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import PortShim.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UMallocRep UMalloc_iface.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RYajlRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UYajl_iface.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RY_lib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UY_lex_kit UY_lex_number.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlBuf YajlLex YajlFactsLex YajlFactsDecode.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section S.
Variable K : lexK.
Hypothesis ENV : kenv K.

(* [comment removed for export] *)
Lemma num_echeck_walk : forall (tok : ytok) (rav s0v s1v s6v s7v s8v t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (m0 m : mem) (e off start c : Z),
  text_at usegs m0 (k_T K) (k_txt K) ->
  lexmem K m0 m e off start -> 0 < off <= zlength (k_txt K) -> 0 <= c < 256 ->
  tok = TK_integer \/ tok = TK_double ->
  evt usegs (sub_post K m0 e start (num_echeck (k_txt K) (zlength (k_txt K)) c off tok))
    (MS (mkR rav (wz (kSP K)) (k_gp K) (k_tp K) t0 t1 t2 s0v s1v (wz off) (wz c) a2 a3 a4 a5 a6 a7
          (wz (k_L K)) (wz (k_H K + 32)) (wz (k_T K)) (wz (zlength (k_txt K))) s6v s7v s8v (wz 1) (wz (tok_code tok)) (wz 1) t3 t4 t5 t6)
        (k_F K) (wz 0x14e88) (k_fc K) None m (seg_rom usegs)).
Proof.
  intros until c. intros TX0 LM BO CR TK. pose proof LM as (MU & WM & MI & STK & FR & OFF & LX & BC). lex_prep ENV BC.
  pose proof (tok_code_range tok) as TR.
  unfold num_echeck.
  zstep. zstep. zstep. if_cases K0; zify_cond K0.
  - (* [comment removed for export] *)
    replace ((c =? c_e) || (c =? c_E)) with false by (rewrite <- land223_eE by lia; symmetry; apply Z.eqb_neq; lia).
    cbn [num_tail]. eapply evt_mono; [eapply (num_final K ENV); [fin_lexmem| lia]|].
    intros ms Hs. destruct TK as [-> | ->]; exact Hs.
  - replace ((c =? c_e) || (c =? c_E)) with true by (rewrite <- land223_eE by lia; symmetry; apply Z.eqb_eq; lia).
    eapply (num_exp_walk K ENV); [exact TX0| fin_lexmem| lia].
Qed.

Lemma dig_post_frac : forall m0 e start r ms,
  dig_post K m0 e start (fun c o => sub_post K m0 e start (num_echeck (k_txt K) (zlength (k_txt K)) c o TK_double)) r ms ->
  sub_post K m0 e start (match match r with RD_eof => inr (TK_eof, zlength (k_txt K), @None lex_error)
                                           | RD_char c o => inl (c, o, TK_double) end
                         with inr res => res | inl (c, o, tok) => num_echeck (k_txt K) (zlength (k_txt K)) c o tok end) ms.
Proof. intros m0 e start [|c o] ms H; exact H. Qed.

(* [comment removed for export] *)
Lemma frac_loop : forall (fuel : nat) (nr : Z) (rav s6v s7v s8v s10v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (m0 m : mem) (e off start : Z),
  text_at usegs m0 (k_T K) (k_txt K) ->
  lexmem K m0 m e off start -> 0 <= off <= zlength (k_txt K) -> (Z.to_nat (zlength (k_txt K) - off) < fuel)%nat ->
  0 <= nr <= off ->
  evt usegs (dig_post K m0 e start (fun c o => sub_post K m0 e start (num_echeck (k_txt K) (zlength (k_txt K)) c o TK_double))
               (read_past_digits fuel (k_txt K) (zlength (k_txt K)) off))
    (MS (mkR rav (wz (kSP K)) (k_gp K) (k_tp K) t0 t1 t2 (wz nr) (wz 10) a0 a1 a2 a3 a4 a5 a6 a7
          (wz (k_L K)) (wz (k_H K + 32)) (wz (k_T K)) (wz (zlength (k_txt K))) s6v s7v s8v (wz 1) s10v (wz 1) t3 t4 t5 t6)
        (k_F K) (wz 0x14fc4) (k_fc K) None m (seg_rom usegs)).
Proof.
  induction fuel as [|fuel IH]; intros until start; intros TX0 LM BO FUEL NR; [lia|].
  pose proof LM as (MU & WM & MI & STK & FR & OFF & LX & BC). lex_prep ENV BC.
  cbn [read_past_digits]. unfold read1.
  (* [comment removed for export] *)
  zstep. zstep. rewrite ?(unsigned_lit nr), ?(swrap32_small (nr + 1)) by lia.
  zstep. if_cases G0; zify_cond G0. 1:{ exfalso. revert G0. rewrite ?signed_small by lia. rewrite ?unsigned_lit by lia. lia. }
  eofchk K0.
  - replace (zlength (k_txt K) <=? off) with true by (symmetry; apply Z.leb_le; lia). cbn [dig_post].
    assert (E : off = zlength (k_txt K)) by lia. rewrite E in OFF. zstep. fin_at.
  - replace (zlength (k_txt K) <=? off) with false by (symmetry; apply Z.leb_gt; lia).
    rdchar MU TX0 off.
    zstep. zstep. if_cases K1; zify_cond K1; digk K1.
    + rewrite (is_digit_true (znth (k_txt K) off)) by lia.
      eapply IH; [exact TX0| fin_lexmem| lia| lia| lia].
    + rewrite (is_digit_false (znth (k_txt K) off)) by lia. cbn [dig_post].
      zstep. rewrite ?ysx32_small by lia. zstep. if_cases KZ; zify_cond KZ. 1:{ kill KZ. } clear KZ. zstep. zstep.
      eapply (num_echeck_walk TK_double); [exact TX0| fin_lexmem| lia| lia| right; reflexivity].
    + rewrite (is_digit_false (znth (k_txt K) off)) by lia. cbn [dig_post].
      zstep. rewrite ?ysx32_small by lia. zstep. if_cases KZ; zify_cond KZ. 1:{ kill KZ. } clear KZ. zstep. zstep.
      eapply (num_echeck_walk TK_double); [exact TX0| fin_lexmem| lia| lia| right; reflexivity].
Qed.

(* [comment removed for export] *)
Lemma num_frac_walk : forall (rav s0v s1v s6v s7v s8v s10v t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (m0 m : mem) (e off start : Z),
  text_at usegs m0 (k_T K) (k_txt K) ->
  lexmem K m0 m e off start -> 0 <= off <= zlength (k_txt K) ->
  evt usegs (sub_post K m0 e start (match num_frac (k_txt K) (zlength (k_txt K)) off with
                                   | inr res => res
                                   | inl (c, o, tok) => num_echeck (k_txt K) (zlength (k_txt K)) c o tok end))
    (MS (mkR rav (wz (kSP K)) (k_gp K) (k_tp K) t0 t1 t2 s0v s1v (wz off) a1 a2 a3 a4 a5 a6 a7
          (wz (k_L K)) (wz (k_H K + 32)) (wz (k_T K)) (wz (zlength (k_txt K))) s6v s7v s8v (wz 1) s10v (wz 1) t3 t4 t5 t6)
        (k_F K) (wz 0x14e28) (k_fc K) None m (seg_rom usegs)).
Proof.
  intros until start. intros TX0 LM BO. pose proof LM as (MU & WM & MI & STK & FR & OFF & LX & BC). lex_prep ENV BC.
  unfold num_frac, read1.
  zstep. if_cases K0; zify_cond K0.
  - replace (zlength (k_txt K) <=? off) with true by (symmetry; apply Z.leb_le; lia). cbn [sub_post err_upd].
    assert (E : off = zlength (k_txt K)) by lia. rewrite E in OFF. zstep. fin_at.
  - replace (zlength (k_txt K) <=? off) with false by (symmetry; apply Z.leb_gt; lia).
    rdchar MU TX0 off.
    zstep. zstep. zstep. if_cases K1; zify_cond K1; digk K1.
    + (* [comment removed for export] *)
      rewrite (is_digit_false (znth (k_txt K) off)) by lia. cbn [sub_post err_upd lex_error_code tok_code].
      unread. zstep. zstep. zstep. zstep. zstep. try replace (off + 1 + -1) with off in OFF by lia. replace (off + 1 - 1) with off by lia. fin_at.
    + rewrite (is_digit_false (znth (k_txt K) off)) by lia. cbn [sub_post err_upd lex_error_code tok_code].
      unread. zstep. zstep. zstep. zstep. zstep. try replace (off + 1 + -1) with off in OFF by lia. replace (off + 1 - 1) with off by lia. fin_at.
    + (* [comment removed for export] *)
      rewrite (is_digit_true (znth (k_txt K) off)) by lia.
      zstep. zstep. eapply evt_mono; [eapply (frac_loop (lex_fuel (zlength (k_txt K)) (off + 1)) 0); [exact TX0| fin_lexmem| lia| unfold lex_fuel; lia| lia]|].
      intros ms Hs. exact (dig_post_frac _ _ _ _ _ Hs).
Qed.

(* [comment removed for export] *)
Lemma num_dotcheck_walk : forall (rav s0v s1v s6v s7v s8v s10v t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (m0 m : mem) (e off start c : Z),
  text_at usegs m0 (k_T K) (k_txt K) ->
  lexmem K m0 m e off start -> 0 < off <= zlength (k_txt K) -> 0 <= c < 256 ->
  evt usegs (sub_post K m0 e start (num_dotcheck (k_txt K) (zlength (k_txt K)) c off))
    (MS (mkR rav (wz (kSP K)) (k_gp K) (k_tp K) t0 t1 t2 s0v s1v a0 (wz c) a2 a3 a4 a5 a6 a7
          (wz (k_L K)) (wz (k_H K + 32)) (wz (k_T K)) (wz (zlength (k_txt K))) s6v s7v s8v (wz 1) s10v (wz 1) t3 t4 t5 t6)
        (k_F K) (wz 0x14e1c) (k_fc K) None m (seg_rom usegs)).
Proof.
  intros until c. intros TX0 LM BO CR. pose proof LM as (MU & WM & MI & STK & FR & OFF & LX & BC). lex_prep ENV BC.
  unfold num_dotcheck.
  zstep. rewrite ?ysx32_small by lia. zstep. zstep. if_cases K0; zify_cond K0.
  - (* [comment removed for export] *)
    replace (c =? c_dot) with false by (symmetry; apply Z.eqb_neq; unfold c_dot; lia).
    zstep. eapply (num_echeck_walk TK_integer); [exact TX0| fin_lexmem| lia| lia| left; reflexivity].
  - replace (c =? c_dot) with true by (symmetry; apply Z.eqb_eq; unfold c_dot; lia).
    eapply num_frac_walk; [exact TX0| fin_lexmem| lia].
Qed.

(* [comment removed for export] *)
Lemma int_loop : forall (fuel : nat) (rav s1v s6v s7v s8v s10v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (m0 m : mem) (e off start : Z),
  text_at usegs m0 (k_T K) (k_txt K) ->
  lexmem K m0 m e off start -> 0 <= off <= zlength (k_txt K) -> (Z.to_nat (zlength (k_txt K) - off) < fuel)%nat ->
  evt usegs (dig_post K m0 e start (fun c o => sub_post K m0 e start (num_dotcheck (k_txt K) (zlength (k_txt K)) c o))
               (read_past_digits fuel (k_txt K) (zlength (k_txt K)) off))
    (MS (mkR rav (wz (kSP K)) (k_gp K) (k_tp K) t0 t1 t2 (wz 10) s1v a0 a1 a2 a3 a4 a5 a6 a7
          (wz (k_L K)) (wz (k_H K + 32)) (wz (k_T K)) (wz (zlength (k_txt K))) s6v s7v s8v (wz 1) s10v (wz 1) t3 t4 t5 t6)
        (k_F K) (wz 0x14844) (k_fc K) None m (seg_rom usegs)).
Proof.
  induction fuel as [|fuel IH]; intros until start; intros TX0 LM BO FUEL; [lia|].
  pose proof LM as (MU & WM & MI & STK & FR & OFF & LX & BC). lex_prep ENV BC.
  cbn [read_past_digits]. unfold read1.
  eofchk K0.
  - replace (zlength (k_txt K) <=? off) with true by (symmetry; apply Z.leb_le; lia). cbn [dig_post].
    assert (E : off = zlength (k_txt K)) by lia. rewrite E in OFF. zstep. fin_at.
  - replace (zlength (k_txt K) <=? off) with false by (symmetry; apply Z.leb_gt; lia).
    rdchar MU TX0 off.
    zstep. zstep. if_cases K1; zify_cond K1; digk K1.
    + rewrite (is_digit_true (znth (k_txt K) off)) by lia.
      eapply IH; [exact TX0| fin_lexmem| lia| lia].
    + rewrite (is_digit_false (znth (k_txt K) off)) by lia. cbn [dig_post].
      zstep. eapply num_dotcheck_walk; [exact TX0| fin_lexmem| lia| lia].
    + rewrite (is_digit_false (znth (k_txt K) off)) by lia. cbn [dig_post].
      zstep. eapply num_dotcheck_walk; [exact TX0| fin_lexmem| lia| lia].
Qed.

Lemma dig_post_int : forall m0 e start r ms,
  dig_post K m0 e start (fun c o => sub_post K m0 e start (num_dotcheck (k_txt K) (zlength (k_txt K)) c o)) r ms ->
  sub_post K m0 e start (match Some r with
                         | None => (TK_error, 0, Some LE_missing_integer_after_minus)
                         | Some RD_eof => (TK_eof, zlength (k_txt K), None)
                         | Some (RD_char c o) => num_dotcheck (k_txt K) (zlength (k_txt K)) c o end) ms.
Proof. intros m0 e start [|c o] ms H; exact H. Qed.

(* [comment removed for export] *)
Lemma num_after_first_walk : forall (rav s0v s1v s6v s7v s8v s10v t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (m0 m : mem) (e off start c : Z),
  text_at usegs m0 (k_T K) (k_txt K) ->
  lexmem K m0 m e off start -> 0 < off <= zlength (k_txt K) -> 0 <= c < 256 ->
  evt usegs (sub_post K m0 e start (num_after_first (k_txt K) (zlength (k_txt K)) c off))
    (MS (mkR rav (wz (kSP K)) (k_gp K) (k_tp K) t0 t1 t2 s0v s1v (wz c) a1 a2 a3 a4 a5 a6 a7
          (wz (k_L K)) (wz (k_H K + 32)) (wz (k_T K)) (wz (zlength (k_txt K))) s6v s7v s8v (wz 1) s10v (wz 1) t3 t4 t5 t6)
        (k_F K) (wz 0x147cc) (k_fc K) None m (seg_rom usegs)).
Proof.
  intros until c. intros TX0 LM BO CR. pose proof LM as (MU & WM & MI & STK & FR & OFF & LX & BC). lex_prep ENV BC.
  unfold num_after_first, read1.
  zstep. zstep. if_cases K0; zify_cond K0.
  - (* [comment removed for export] *)
    replace (c =? c_0) with false by (symmetry; apply Z.eqb_neq; unfold c_0; lia).
    zstep. zstep. zstep. if_cases K1; zify_cond K1; digk K1.
    + (* [comment removed for export] *)
      replace ((c_1 <=? c) && (c <=? c_9)) with false by (unfold c_1, c_9; symmetry; destruct (Z.leb_spec 49 c); destruct (Z.leb_spec c 57); cbn [andb]; try reflexivity; lia).
      cbn [sub_post err_upd lex_error_code tok_code].
      unread. zstep. zstep. zstep. zstep. zstep. replace (off + -1) with (off - 1) in OFF by lia. fin_at.
    + replace ((c_1 <=? c) && (c <=? c_9)) with false by (unfold c_1, c_9; symmetry; destruct (Z.leb_spec 49 c); destruct (Z.leb_spec c 57); cbn [andb]; try reflexivity; lia).
      cbn [sub_post err_upd lex_error_code tok_code].
      unread. zstep. zstep. zstep. zstep. zstep. replace (off + -1) with (off - 1) in OFF by lia. fin_at.
    + (* [comment removed for export] *)
      replace ((c_1 <=? c) && (c <=? c_9)) with true by (unfold c_1, c_9; symmetry; apply andb_true_iff; split; apply Z.leb_le; lia).
      zstep. eapply evt_mono; [eapply (int_loop (lex_fuel (zlength (k_txt K)) off)); [exact TX0| fin_lexmem| lia| unfold lex_fuel; lia]|].
      intros ms Hs. exact (dig_post_int _ _ _ _ _ Hs).
  - (* [comment removed for export] *)
    replace (c =? c_0) with true by (symmetry; apply Z.eqb_eq; unfold c_0; lia).
    eofchk K1.
    + replace (zlength (k_txt K) <=? off) with true by (symmetry; apply Z.leb_le; lia). cbn [sub_post err_upd].
      assert (E : off = zlength (k_txt K)) by lia. rewrite E in OFF. zstep. fin_at.
    + replace (zlength (k_txt K) <=? off) with false by (symmetry; apply Z.leb_gt; lia).
      rdchar MU TX0 off.
      eapply num_dotcheck_walk; [exact TX0| fin_lexmem| lia| lia].
Qed.

(* [comment removed for export] *)
Lemma lex_number_walk : forall (rav s0v s1v s6v s7v s8v s10v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (m0 m : mem) (e off0 start : Z),
  text_at usegs m0 (k_T K) (k_txt K) ->
  lexmem K m0 m e (off0 + 1) start -> 0 <= off0 < zlength (k_txt K) ->
  evt usegs (sub_post K m0 e start (ylex_number (k_txt K) (zlength (k_txt K)) off0))
    (MS (mkR rav (wz (kSP K)) (k_gp K) (k_tp K) t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7
          (wz (k_L K)) (wz (k_H K + 32)) (wz (k_T K)) (wz (zlength (k_txt K))) s6v s7v s8v (wz 1) s10v (wz 1) t3 t4 t5 t6)
        (k_F K) (wz 0x144d8) (k_fc K) None m (seg_rom usegs)).
Proof.
  intros until start. intros TX0 LM BO. pose proof LM as (MU & WM & MI & STK & FR & OFF & LX & BC). lex_prep ENV BC.
  rewrite ylex_number_eq. unfold read1.
  replace (zlength (k_txt K) <=? off0) with false by (symmetry; apply Z.leb_gt; lia).
  (* [comment removed for export] *)
  zstep. rewrite ?ysx32_small by lia.
  zstep. if_cases KU; zify_cond KU. 1:{ kill KU. } clear KU.
  zstep. rewrite (swrap32_small (off0 + 1 + -1)) by lia. replace (off0 + 1 + -1) with off0 by lia.
  zstep. zstep. if_cases K0; zify_cond K0. 2:{ kill K0. } clear K0.
  rdchar MU TX0 off0.
  zstep. zstep. if_cases K1; zify_cond K1.
  - (* [comment removed for export] *)
    replace (znth (k_txt K) off0 =? c_minus) with false by (symmetry; apply Z.eqb_neq; unfold c_minus; lia).
    eapply num_after_first_walk; [exact TX0| fin_lexmem| lia| lia].
  - replace (znth (k_txt K) off0 =? c_minus) with true by (symmetry; apply Z.eqb_eq; unfold c_minus; lia).
    eofchk K2.
    + replace (zlength (k_txt K) <=? off0 + 1) with true by (symmetry; apply Z.leb_le; lia). cbn [sub_post err_upd].
      assert (E : off0 + 1 = zlength (k_txt K)) by lia. rewrite E in OFF. zstep. fin_at.
    + replace (zlength (k_txt K) <=? off0 + 1) with false by (symmetry; apply Z.leb_gt; lia).
      rdchar MU TX0 (off0 + 1).
      eapply num_after_first_walk; [exact TX0| fin_lexmem| lia| lia].
Qed.
End S.
End RC__1.
