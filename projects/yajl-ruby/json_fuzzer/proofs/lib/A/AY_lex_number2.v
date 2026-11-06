(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import A_iface AYajlRep AYajl_iface AY_rz AY_lex_rdck AY_lex_rdck2 AY_lex_kit AY_lex_number1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac aceil := first [pose proof alloc_ceiling_range as CEILB | idtac].
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section S.
Variable K : alexK.
Variable m0 : mem.
Hypothesis ENV : kenvA K.
Hypothesis KP : kpolA K.
Hypothesis SH : alexsh K m0.

Ltac pols := polu KP kp_Ls PLS; polu KP kp_L PL; polu KP kp_T PT; polu KP kp_Hs PHS; polu KP kp_H PH; polu KP kp_stk PSTK.
Ltac prep LM BC := pose proof LM as (MU & WM & MI & ST & FR & OFF & LX & BC); lex_prep ENV BC; pols.

(* [comment removed for export] *)
Ltac err_tail K m0 ENV SH MU WM OFF off :=
  shld (rd_shH K m0 _ ENV SH MU WM 32 ltac:(lia)); zstepA; iflit;
  zstepA; rewrite ?ysx32_small by lia;
  (let KU := fresh "KU" in zstepA; if_cases KU; zify_cond KU; [kill KU| clear KU]);
  shld (rd_shH K m0 _ ENV SH MU WM 32 ltac:(lia)); zstepA; iflit;
  zstepA; zstoreA ENV; stepA;
  zstepA; zstepA; zstepA; shadow_addr; zstepA;
  shld (rd_shL K m0 _ ENV SH MU WM 8 ltac:(lia)); zstepA; iflit;
  stepA; stepA; zstoreA ENV; stepA;
  try replace (off + -1) with (off - 1) in OFF by lia.

(* [comment removed for export] *)
Lemma num_echeck_walk : forall (tok : ytok) (rav s2v s3v s6v s10v t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 k8 k64 : word) (k0 : list byte)
    (m : mem) (e off start c : Z),
  alexmem K m0 m e off start k0 k8 k64 -> 0 < off <= zlength (k_txt K) -> 0 <= c < 256 ->
  tok = TK_integer \/ tok = TK_double ->
  evtA asegs (k_P K) (sub_post K m0 e start (num_echeck (k_txt K) (zlength (k_txt K)) c off tok))
    (MS (mkR rav (wz (kSQ K)) (k_gp K) (k_tp K) t0 t1 t2 (wz (k_H K + 32)) (wz (k_L K + 16)) (wz c) a1 a2 a3 a4 a5 a6 a7
          s2v s3v (wz (k_L K + 24)) (wz (k_L K + 28)) s6v (wz (tok_code tok)) (wz (zlength (k_txt K))) (wz ASB) s10v
          (wz ((k_H K + 32) / 8 + ASB)) t3 t4 t5 t6)
        (k_F K) (wz 0x84ef8) (k_fc K) None m (seg_rom asegs)).
Proof. aceil.
  intros until c. intros LM BO CR TK. prep LM BC.
  pose proof (tok_code_range tok) as TR.
  unfold num_echeck.
  zstepA. stepA. zstepA. if_cases K0; zify_cond K0.                         (* [comment removed for export] *)
  - (* [comment removed for export] *)
    replace ((c =? c_e) || (c =? c_E)) with false by (rewrite <- lor32_eE by lia; symmetry; apply Z.eqb_neq; lia).
    cbn [num_tail]. eapply evtA_mono; [eapply (num_final K m0 ENV KP SH); [fin_lexmem| lia]|].
    intros ms Hs. destruct TK as [-> | ->]; exact Hs.
  - replace ((c =? c_e) || (c =? c_E)) with true by (rewrite <- lor32_eE by lia; symmetry; apply Z.eqb_eq; lia).
    eapply (num_exp_walk K m0 ENV KP SH); [fin_lexmem| lia].
Qed.

Lemma dig_post_frac : forall e start r ms,
  dig_post K m0 e start (fun c o => sub_post K m0 e start (num_echeck (k_txt K) (zlength (k_txt K)) c o TK_double)) r ms ->
  sub_post K m0 e start (match match r with RD_eof => inr (TK_eof, zlength (k_txt K), @None lex_error)
                                           | RD_char c o => inl (c, o, TK_double) end
                         with inr res => res | inl (c, o, tok) => num_echeck (k_txt K) (zlength (k_txt K)) c o tok end) ms.
Proof. aceil. intros e start [|c o] ms H; exact H. Qed.

(* [comment removed for export] *)
Lemma frac_loop : forall (fuel : nat) (rav s2v s6v s7v s10v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 k8 k64 : word) (k0 : list byte)
    (m : mem) (e off start : Z),
  alexmem K m0 m e off start k0 k8 k64 -> 0 <= off <= zlength (k_txt K) -> (Z.to_nat (zlength (k_txt K) - off) < fuel)%nat ->
  evtA asegs (k_P K) (dig_post K m0 e start (fun c o => sub_post K m0 e start (num_echeck (k_txt K) (zlength (k_txt K)) c o TK_double))
                        (read_past_digits fuel (k_txt K) (zlength (k_txt K)) off))
    (MS (mkR rav (wz (kSQ K)) (k_gp K) (k_tp K) t0 t1 t2 (wz (k_H K + 32)) (wz (k_L K + 16)) a0 a1 a2 a3 a4 a5 a6 a7
          s2v (wz 10) (wz (k_L K + 24)) (wz (k_L K + 28)) s6v s7v (wz (zlength (k_txt K))) (wz ASB) s10v
          (wz ((k_H K + 32) / 8 + ASB)) t3 t4 t5 t6)
        (k_F K) (wz 0x85230) (k_fc K) None m (seg_rom asegs)).
Proof. aceil.
  induction fuel as [|fuel IH]; intros until start; intros LM BO FUEL; [lia|]. prep LM BC.
  cbn [read_past_digits]. unfold read1.
  eofchkA K m0 ENV SH MU WM K0.
  - replace (zlength (k_txt K) <=? off) with true by (symmetry; apply Z.leb_le; lia). cbn [dig_post].
    assert (E : off = zlength (k_txt K)) by lia. rewrite E in OFF. fin_at.
  - replace (zlength (k_txt K) <=? off) with false by (symmetry; apply Z.leb_gt; lia).
    rdcharA K m0 ENV KP SH MU WM rdck_10bdb0 off.
    zstepA. zstepA. if_cases K1; zify_cond K1; digk K1.                     (* [comment removed for export] *)
    + rewrite (is_digit_true (znth (k_txt K) off)) by lia.
      eapply IH; [fin_lexmem| lia| lia].
    + rewrite (is_digit_false (znth (k_txt K) off)) by lia. cbn [dig_post].
      stepA. stepA. stepA.                                                   (* [comment removed for export] *)
      eapply (num_echeck_walk TK_double); [fin_lexmem| lia| lia| right; reflexivity].
    + rewrite (is_digit_false (znth (k_txt K) off)) by lia. cbn [dig_post].
      stepA. stepA. stepA.
      eapply (num_echeck_walk TK_double); [fin_lexmem| lia| lia| right; reflexivity].
Qed.

(* [comment removed for export] *)
Lemma num_frac_walk : forall (rav s2v s3v s6v s7v s10v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 k8 k64 : word) (k0 : list byte)
    (m : mem) (e off start : Z),
  alexmem K m0 m e off start k0 k8 k64 -> 0 <= off <= zlength (k_txt K) ->
  evtA asegs (k_P K) (sub_post K m0 e start (match num_frac (k_txt K) (zlength (k_txt K)) off with
                                           | inr res => res
                                           | inl (c, o, tok) => num_echeck (k_txt K) (zlength (k_txt K)) c o tok end))
    (MS (mkR rav (wz (kSQ K)) (k_gp K) (k_tp K) t0 t1 t2 (wz (k_H K + 32)) (wz (k_L K + 16)) a0 a1 a2 a3 a4 a5 a6 a7
          s2v s3v (wz (k_L K + 24)) (wz (k_L K + 28)) s6v s7v (wz (zlength (k_txt K))) (wz ASB) s10v
          (wz ((k_H K + 32) / 8 + ASB)) t3 t4 t5 t6)
        (k_F K) (wz 0x84e4c) (k_fc K) None m (seg_rom asegs)).
Proof. aceil.
  intros until start. intros LM BO. prep LM BC.
  unfold num_frac, read1.
  eofchkA K m0 ENV SH MU WM K0.
  - replace (zlength (k_txt K) <=? off) with true by (symmetry; apply Z.leb_le; lia). cbn [sub_post err_upd].
    assert (E : off = zlength (k_txt K)) by lia. rewrite E in OFF. fin_at.
  - replace (zlength (k_txt K) <=? off) with false by (symmetry; apply Z.leb_gt; lia).
    rdcharA K m0 ENV KP SH MU WM rdck_10bbb4 off.
    zstepA. stepA. zstepA. if_cases K1; zify_cond K1; digk K1.              (* [comment removed for export] *)
    + (* [comment removed for export] *)
      rewrite (is_digit_true (znth (k_txt K) off)) by lia.
      stepA. zstepA. zstepA. zstepA. zstepA. zstepA. zstepA.
      eapply evtA_mono; [eapply (frac_loop (lex_fuel (zlength (k_txt K)) (off + 1))); [fin_lexmem| lia| unfold lex_fuel; lia]|].
      intros ms Hs. exact (dig_post_frac _ _ _ _ Hs).
    + (* [comment removed for export] *)
      rewrite (is_digit_false (znth (k_txt K) off)) by lia. cbn [sub_post err_upd lex_error_code tok_code].
      err_tail K m0 ENV SH MU WM OFF (off + 1).
      try replace (off + 1 + -1) with off in OFF by lia. replace (off + 1 - 1) with off by lia. fin_at.
    + rewrite (is_digit_false (znth (k_txt K) off)) by lia. cbn [sub_post err_upd lex_error_code tok_code].
      err_tail K m0 ENV SH MU WM OFF (off + 1).
      try replace (off + 1 + -1) with off in OFF by lia. replace (off + 1 - 1) with off by lia. fin_at.
Qed.

(* [comment removed for export] *)
Lemma num_dotcheck_walk : forall (rav s2v s3v s6v s7v s10v t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 k8 k64 : word) (k0 : list byte)
    (m : mem) (e off start c : Z),
  alexmem K m0 m e off start k0 k8 k64 -> 0 < off <= zlength (k_txt K) -> 0 <= c < 256 ->
  evtA asegs (k_P K) (sub_post K m0 e start (num_dotcheck (k_txt K) (zlength (k_txt K)) c off))
    (MS (mkR rav (wz (kSQ K)) (k_gp K) (k_tp K) t0 t1 t2 (wz (k_H K + 32)) (wz (k_L K + 16)) (wz c) a1 a2 a3 a4 a5 a6 a7
          s2v s3v (wz (k_L K + 24)) (wz (k_L K + 28)) s6v s7v (wz (zlength (k_txt K))) (wz ASB) s10v
          (wz ((k_H K + 32) / 8 + ASB)) t3 t4 t5 t6)
        (k_F K) (wz 0x84e44) (k_fc K) None m (seg_rom asegs)).
Proof. aceil.
  intros until c. intros LM BO CR. prep LM BC.
  unfold num_dotcheck.
  stepA. zstepA. if_cases K0; zify_cond K0.                                  (* [comment removed for export] *)
  - (* [comment removed for export] *)
    replace (c =? c_dot) with false by (symmetry; apply Z.eqb_neq; unfold c_dot; lia).
    stepA.                                                                   (* [comment removed for export] *)
    eapply (num_echeck_walk TK_integer); [fin_lexmem| lia| lia| left; reflexivity].
  - replace (c =? c_dot) with true by (symmetry; apply Z.eqb_eq; unfold c_dot; lia).
    eapply num_frac_walk; [fin_lexmem| lia].
Qed.

(* [comment removed for export] *)
Lemma int_loop : forall (fuel : nat) (rav s2v s6v s7v s10v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 k8 k64 : word) (k0 : list byte)
    (m : mem) (e off start : Z),
  alexmem K m0 m e off start k0 k8 k64 -> 0 <= off <= zlength (k_txt K) -> (Z.to_nat (zlength (k_txt K) - off) < fuel)%nat ->
  evtA asegs (k_P K) (dig_post K m0 e start (fun c o => sub_post K m0 e start (num_dotcheck (k_txt K) (zlength (k_txt K)) c o))
                        (read_past_digits fuel (k_txt K) (zlength (k_txt K)) off))
    (MS (mkR rav (wz (kSQ K)) (k_gp K) (k_tp K) t0 t1 t2 (wz (k_H K + 32)) (wz (k_L K + 16)) a0 a1 a2 a3 a4 a5 a6 a7
          s2v (wz 10) (wz (k_L K + 24)) (wz (k_L K + 28)) s6v s7v (wz (zlength (k_txt K))) (wz ASB) s10v
          (wz ((k_H K + 32) / 8 + ASB)) t3 t4 t5 t6)
        (k_F K) (wz 0x83eb4) (k_fc K) None m (seg_rom asegs)).
Proof. aceil.
  induction fuel as [|fuel IH]; intros until start; intros LM BO FUEL; [lia|]. prep LM BC.
  cbn [read_past_digits]. unfold read1.
  eofchkA K m0 ENV SH MU WM K0.
  2:{ stepA. replace (zlength (k_txt K) <=? off) with true by (symmetry; apply Z.leb_le; lia). cbn [dig_post].
      assert (E : off = zlength (k_txt K)) by lia. rewrite E in OFF. fin_at. }
  replace (zlength (k_txt K) <=? off) with false by (symmetry; apply Z.leb_gt; lia).
  rdcharA K m0 ENV KP SH MU WM rdck_10aa38 off.
  zstepA. zstepA. if_cases K1; zify_cond K1; digk K1.                       (* [comment removed for export] *)
  - rewrite (is_digit_true (znth (k_txt K) off)) by lia.
    eapply IH; [fin_lexmem| lia| lia].
  - rewrite (is_digit_false (znth (k_txt K) off)) by lia. cbn [dig_post].
    stepA. eapply num_dotcheck_walk; [fin_lexmem| lia| lia].                (* [comment removed for export] *)
  - rewrite (is_digit_false (znth (k_txt K) off)) by lia. cbn [dig_post].
    stepA. eapply num_dotcheck_walk; [fin_lexmem| lia| lia].
Qed.

Lemma dig_post_int : forall e start r ms,
  dig_post K m0 e start (fun c o => sub_post K m0 e start (num_dotcheck (k_txt K) (zlength (k_txt K)) c o)) r ms ->
  sub_post K m0 e start (match Some r with
                         | None => (TK_error, 0, Some LE_missing_integer_after_minus)
                         | Some RD_eof => (TK_eof, zlength (k_txt K), None)
                         | Some (RD_char c o) => num_dotcheck (k_txt K) (zlength (k_txt K)) c o end) ms.
Proof. aceil. intros e start [|c o] ms H; exact H. Qed.

(* [comment removed for export] *)
Lemma num_after_first_walk : forall (rav s2v s3v s6v s7v s10v t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 k8 k64 : word) (k0 : list byte)
    (m : mem) (e off start c : Z),
  alexmem K m0 m e off start k0 k8 k64 -> 0 < off <= zlength (k_txt K) -> 0 <= c < 256 ->
  evtA asegs (k_P K) (sub_post K m0 e start (num_after_first (k_txt K) (zlength (k_txt K)) c off))
    (MS (mkR rav (wz (kSQ K)) (k_gp K) (k_tp K) t0 t1 t2 (wz (k_H K + 32)) (wz (k_L K + 16)) (wz c) a1 a2 a3 a4 a5 a6 a7
          s2v s3v (wz (k_L K + 24)) (wz (k_L K + 28)) s6v s7v (wz (zlength (k_txt K))) (wz ASB) s10v
          (wz ((k_H K + 32) / 8 + ASB)) t3 t4 t5 t6)
        (k_F K) (wz 0x83dc8) (k_fc K) None m (seg_rom asegs)).
Proof. aceil.
  intros until c. intros LM BO CR. prep LM BC.
  unfold num_after_first, read1.
  stepA. zstepA. if_cases K0; zify_cond K0.                                  (* [comment removed for export] *)
  - (* [comment removed for export] *)
    replace (c =? c_0) with false by (symmetry; apply Z.eqb_neq; unfold c_0; lia).
    zstepA. stepA. zstepA. if_cases K1; zify_cond K1; digk K1.              (* [comment removed for export] *)
    + (* [comment removed for export] *)
      replace ((c_1 <=? c) && (c <=? c_9)) with false by (unfold c_1, c_9; symmetry; destruct (Z.leb_spec 49 c); destruct (Z.leb_spec c 57); cbn [andb]; try reflexivity; lia).
      cbn [sub_post err_upd lex_error_code tok_code].
      shld (rd_shH K m0 _ ENV SH MU WM 32 ltac:(lia)). zstepA. iflit.        (* [comment removed for export] *)
      zstepA. rewrite ?ysx32_small by lia.                                   (* [comment removed for export] *)
      zstepA. if_cases KU; zify_cond KU. 2:{ kill KU. } clear KU.            (* [comment removed for export] *)
      shld (rd_shH K m0 _ ENV SH MU WM 32 ltac:(lia)). zstepA. iflit.        (* [comment removed for export] *)
      zstepA. zstoreA ENV. stepA.                                            (* [comment removed for export] *)
      zstepA. zstepA. zstepA. shadow_addr. zstepA.
      shld (rd_shL K m0 _ ENV SH MU WM 8 ltac:(lia)). zstepA. iflit.
      stepA. stepA. zstoreA ENV. stepA.                                      (* [comment removed for export] *)
      replace (off + -1) with (off - 1) in OFF by lia. fin_at.
    + replace ((c_1 <=? c) && (c <=? c_9)) with false by (unfold c_1, c_9; symmetry; destruct (Z.leb_spec 49 c); destruct (Z.leb_spec c 57); cbn [andb]; try reflexivity; lia).
      cbn [sub_post err_upd lex_error_code tok_code].
      shld (rd_shH K m0 _ ENV SH MU WM 32 ltac:(lia)). zstepA. iflit.
      zstepA. rewrite ?ysx32_small by lia.
      zstepA. if_cases KU; zify_cond KU. 2:{ kill KU. } clear KU.
      shld (rd_shH K m0 _ ENV SH MU WM 32 ltac:(lia)). zstepA. iflit.
      zstepA. zstoreA ENV. stepA.
      zstepA. zstepA. zstepA. shadow_addr. zstepA.
      shld (rd_shL K m0 _ ENV SH MU WM 8 ltac:(lia)). zstepA. iflit.
      stepA. stepA. zstoreA ENV. stepA.
      replace (off + -1) with (off - 1) in OFF by lia. fin_at.
    + (* [comment removed for export] *)
      replace ((c_1 <=? c) && (c <=? c_9)) with true by (unfold c_1, c_9; symmetry; apply andb_true_iff; split; apply Z.leb_le; lia).
      stepA. zstepA. zstepA. zstepA. zstepA. zstepA. zstepA.
      eapply evtA_mono; [eapply (int_loop (lex_fuel (zlength (k_txt K)) off)); [fin_lexmem| lia| unfold lex_fuel; lia]|].
      intros ms Hs. exact (dig_post_int _ _ _ _ Hs).
  - (* [comment removed for export] *)
    replace (c =? c_0) with true by (symmetry; apply Z.eqb_eq; unfold c_0; lia).
    shld (rd_shH K m0 _ ENV SH MU WM 32 ltac:(lia)). zstepA. iflit.          (* [comment removed for export] *)
    zstepA. rewrite ?ysx32_small by lia. zstepA. if_cases K1; zify_cond K1.  (* [comment removed for export] *)
    2:{ stepA. replace (zlength (k_txt K) <=? off) with true by (symmetry; apply Z.leb_le; lia). cbn [sub_post err_upd].
        assert (E : off = zlength (k_txt K)) by lia. rewrite E in OFF. fin_at. }
    replace (zlength (k_txt K) <=? off) with false by (symmetry; apply Z.leb_gt; lia).
    (* [comment removed for export] *)
    zstepA. shld (rd_shL K m0 _ ENV SH MU WM 28 ltac:(lia)). zstepA. iflit.  (* [comment removed for export] *)
    zstepA. rewrite ?ysx32_small by lia. zstepA. iflit.                       (* [comment removed for export] *)
    stepA.                                                                   (* [comment removed for export] *)
    rdincA K m0 ENV SH MU WM off.
    rdckA K m0 ENV KP SH MU WM rdck_10b900 off.
    txtld K m0 ENV SH MU WM off.
    eapply num_dotcheck_walk; [fin_lexmem| lia| lia].
Qed.

(* [comment removed for export] *)
Lemma lex_number_proof : lex_number_stmt K m0.
Proof. aceil.
  unfold lex_number_stmt. intros until start. intros LM BS BO ER. prep LM BC.
  rewrite ylex_number_eq. unfold read1.
  replace (zlength (k_txt K) <=? off0) with false by (symmetry; apply Z.leb_gt; lia).
  (* [comment removed for export] *)
  shld (rd_shH K m0 _ ENV SH MU WM 32 ltac:(lia)). zstepA. iflit.            (* [comment removed for export] *)
  zstepA. rewrite ?ysx32_small by lia.                                       (* [comment removed for export] *)
  zstepA. if_cases KU; zify_cond KU. 1:{ kill KU. } clear KU.                (* [comment removed for export] *)
  shld (rd_shH K m0 _ ENV SH MU WM 32 ltac:(lia)). zstepA. iflit.            (* [comment removed for export] *)
  zstepA. zstoreA ENV. replace (off0 + 1 + -1) with off0 in * by lia.        (* [comment removed for export] *)
  stepA.                                                                     (* [comment removed for export] *)
  (* [comment removed for export] *)
  shld (rd_shH K m0 _ ENV SH MU WM 32 ltac:(lia)). zstepA. iflit.
  zstepA. rewrite ?ysx32_small by lia. zstepA. if_cases K0; zify_cond K0. 2:{ kill K0. } clear K0.
  rdcharA K m0 ENV KP SH MU WM rdck_10a5c8 off0.
  stepA. zstepA. if_cases K1; zify_cond K1.                                  (* [comment removed for export] *)
  - (* [comment removed for export] *)
    replace (znth (k_txt K) off0 =? c_minus) with false by (symmetry; apply Z.eqb_neq; unfold c_minus; lia).
    eapply num_after_first_walk; [fin_lexmem| lia| lia].
  - replace (znth (k_txt K) off0 =? c_minus) with true by (symmetry; apply Z.eqb_eq; unfold c_minus; lia).
    shld (rd_shH K m0 _ ENV SH MU WM 32 ltac:(lia)). zstepA. iflit.
    zstepA. rewrite ?ysx32_small by lia. zstepA. if_cases K2; zify_cond K2.
    2:{ stepA. replace (zlength (k_txt K) <=? off0 + 1) with true by (symmetry; apply Z.leb_le; lia). cbn [sub_post err_upd].
        assert (E : off0 + 1 = zlength (k_txt K)) by lia. rewrite E in OFF. fin_at. }
    replace (zlength (k_txt K) <=? off0 + 1) with false by (symmetry; apply Z.leb_gt; lia).
    rdcharA K m0 ENV KP SH MU WM rdck_10a880 (off0 + 1).
    eapply num_after_first_walk; [fin_lexmem| lia| lia].
Qed.
End S.
End RC__1.
