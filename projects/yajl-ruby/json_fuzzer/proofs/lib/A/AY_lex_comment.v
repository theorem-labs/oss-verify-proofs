(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RY_lib RY_lex_number RY_lex_main1.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages LazyModel NodesA Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import A_iface AYajlRep AYajl_iface AY_rz AY_lex_rdck AY_lex_kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Open Scope yprog_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
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

(* [comment removed for export] *)
Definition skip_post (e start : Z) (r : rdres) : machine_state -> Prop :=
  match r with
  | RD_eof => fun ms' => exists s7v, alex_at K m0 J_EOF s7v e (zlength (k_txt K)) start ms'
  | RD_char _ o => fun ms' => exists a0v, alex_hd K m0 J_CMT a0v e o start ms'
  end.

Ltac pols := polu KP kp_Ls PLS; polu KP kp_L PL; polu KP kp_T PT; polu KP kp_Hs PHS; polu KP kp_H PH; polu KP kp_stk PSTK.
Ltac fin_hdx :=
  lazymatch goal with |- evtA _ _ _ _ => apply evtA_done | _ => idtac end; cbv beta; eexists; fin_hd.

(* [comment removed for export] *)
Lemma line_cmt_loop : forall (fuel : nat) (rav s2v s3v s10v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 k8 : word) (k0 : list byte)
    (m : mem) (e off start : Z),
  alexmem K m0 m e off start k0 k8 (wz ((k_L K + 32) / 8 + ASB)) -> 0 <= off <= zlength (k_txt K) -> (Z.to_nat (zlength (k_txt K) - off) < fuel)%nat ->
  evtA asegs (k_P K) (skip_post e start (skip_line_comment fuel (k_txt K) (zlength (k_txt K)) off))
    (MS (mkR rav (wz (kSQ K)) (k_gp K) (k_tp K) t0 t1 t2 (wz (k_H K + 32)) (wz (k_L K + 16)) a0 a1 a2 a3 a4 a5 a6 a7
          s2v s3v (wz (k_L K + 24)) (wz (k_L K + 28)) (wz (k_L K + 32)) (wz AY_JT_LEX) (wz (zlength (k_txt K))) (wz ASB) s10v
          (wz ((k_H K + 32) / 8 + ASB)) t3 t4 t5 t6)
        (k_F K) (wz 0x8331c) (k_fc K) None m (seg_rom asegs)).
Proof. aceil.
  induction fuel as [|fuel IH]; intros until start; intros (MU & WM & MI & ST & FR & OFF & LX & BC) BO FUEL; [lia|].
  lex_prep ENV BC. unfold AY_JT_LEX in *. pols.
  cbn [skip_line_comment]. unfold read1.
  eofchkA K m0 ENV SH MU WM K0.
  2:{ (* [comment removed for export] *)
    stepA. replace (zlength (k_txt K) <=? off) with true by (symmetry; apply Z.leb_le; lia). cbn [skip_post].
    assert (E : off = zlength (k_txt K)) by lia. rewrite E in OFF. fin_at. }
  replace (zlength (k_txt K) <=? off) with false by (symmetry; apply Z.leb_gt; lia).
  rdcharA K m0 ENV KP SH MU WM rdck_109eb0 off.
  stepA. zstepA. if_cases K1; zify_cond K1.                                  (* [comment removed for export] *)
  - (* [comment removed for export] *)
    replace (znth (k_txt K) off =? c_lf) with false by (symmetry; apply Z.eqb_neq; unfold c_lf; lia).
    eapply IH; [| lia| lia]. fin_lexmem.
  - replace (znth (k_txt K) off =? c_lf) with true by (symmetry; apply Z.eqb_eq; unfold c_lf; lia).
    stepA. cbn [skip_post]. fin_hdx.                                          (* [comment removed for export] *)
Qed.

(* [comment removed for export] *)
Lemma block_cmt_loop : forall (fuel : nat) (rav s2v s3v s10v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 k8 : word) (k0 : list byte)
    (m : mem) (e off start : Z),
  alexmem K m0 m e off start k0 k8 (wz ((k_L K + 32) / 8 + ASB)) -> 0 <= off <= zlength (k_txt K) -> (Z.to_nat (zlength (k_txt K) - off) < fuel)%nat ->
  evtA asegs (k_P K) (skip_post e start (skip_block_comment fuel (k_txt K) (zlength (k_txt K)) off))
    (MS (mkR rav (wz (kSQ K)) (k_gp K) (k_tp K) t0 t1 t2 (wz (k_H K + 32)) (wz (k_L K + 16)) a0 a1 a2 a3 a4 a5 a6 a7
          s2v s3v (wz (k_L K + 24)) (wz (k_L K + 28)) (wz (k_L K + 32)) (wz AY_JT_LEX) (wz (zlength (k_txt K))) (wz ASB) s10v
          (wz ((k_H K + 32) / 8 + ASB)) t3 t4 t5 t6)
        (k_F K) (wz 0x83458) (k_fc K) None m (seg_rom asegs)).
Proof. aceil.
  induction fuel as [|fuel IH]; intros until start; intros (MU & WM & MI & ST & FR & OFF & LX & BC) BO FUEL; [lia|].
  lex_prep ENV BC. unfold AY_JT_LEX in *. pols.
  cbn [skip_block_comment]. unfold read1.
  zstepA. rewrite ?ysx32_small by lia. zstepA. if_cases K0; zify_cond K0.     (* [comment removed for export] *)
  2:{ (* [comment removed for export] *)
    stepA. replace (zlength (k_txt K) <=? off) with true by (symmetry; apply Z.leb_le; lia). cbn [skip_post].
    assert (E : off = zlength (k_txt K)) by lia. rewrite E in OFF. fin_at. }
  replace (zlength (k_txt K) <=? off) with false by (symmetry; apply Z.leb_gt; lia).
  rdcharA K m0 ENV KP SH MU WM rdck_109fe4 off.
  stepA. zstepA. if_cases K1; zify_cond K1.                                  (* [comment removed for export] *)
  - (* [comment removed for export] *)
    replace (znth (k_txt K) off =? c_star) with false by (symmetry; apply Z.eqb_neq; unfold c_star; lia).
    shld (rd_shH K m0 _ ENV SH MU WM 32 ltac:(lia)). zstepA. try if_true.    (* [comment removed for export] *)
    eapply IH; [| lia| lia]. fin_lexmem.
  - (* [comment removed for export] *)
    replace (znth (k_txt K) off =? c_star) with true by (symmetry; apply Z.eqb_eq; unfold c_star; lia).
    eofchkA K m0 ENV SH MU WM K2.
    2:{ (* [comment removed for export] *)
      stepA. replace (zlength (k_txt K) <=? off + 1) with true by (symmetry; apply Z.leb_le; lia). cbn [skip_post].
      assert (E : off + 1 = zlength (k_txt K)) by lia. rewrite E in OFF. fin_at. }
    replace (zlength (k_txt K) <=? off + 1) with false by (symmetry; apply Z.leb_gt; lia).
    rdcharA K m0 ENV KP SH MU WM rdck_10a0c4 (off + 1).
    stepA. zstepA. if_cases K3; zify_cond K3.                                (* [comment removed for export] *)
    + (* [comment removed for export] *)
      replace (znth (k_txt K) (off + 1) =? c_slash) with true by (symmetry; apply Z.eqb_eq; unfold c_slash; lia).
      cbn [skip_post]. fin_hdx.
    + replace (znth (k_txt K) (off + 1) =? c_slash) with false by (symmetry; apply Z.eqb_neq; unfold c_slash; lia).
      (* [comment removed for export] *)
      shld (rd_shH K m0 _ ENV SH MU WM 32 ltac:(lia)). zstepA. try if_false.
      zstepA. rewrite ?ysx32_small by lia.
      zstepA. if_cases KU; zify_cond KU. 1:{ kill KU. } clear KU.
      shld (rd_shH K m0 _ ENV SH MU WM 32 ltac:(lia)). zstepA. try if_false.
      zstepA. zstoreA ENV.
      try replace (off + 1 + 1 + -1) with (off + 1) in * by lia.
      stepA.                                                                 (* [comment removed for export] *)
      shld (rd_shH K m0 _ ENV SH MU WM 32 ltac:(lia)). zstepA. try if_true.  (* [comment removed for export] *)
      eapply IH; [| lia| lia]. fin_lexmem.
Qed.

Lemma skip_post_cmt : forall e start r ms,
  skip_post e start r ms ->
  cmt_post K m0 e start (match r with RD_eof => (TK_eof, zlength (k_txt K), @None lex_error)
                                     | RD_char _ o2 => (TK_comment, o2, None) end) ms.
Proof. aceil. intros e start [|c o2] ms H; exact H. Qed.

(* [comment removed for export] *)
Lemma lex_comment_proof : lex_comment_stmt K m0.
Proof. aceil.
  unfold lex_comment_stmt. intros until start. intros (MU & WM & MI & ST & FR & OFF & LX & BC) BS BO ER.
  lex_prep ENV BC. unfold AY_JT_LEX in *. pols.
  unfold ylex_comment, read1.
  zstepA. shld (rd_shL K m0 _ ENV SH MU WM 32 ltac:(lia)). zstepA. try if_false.   (* [comment removed for export] *)
  pose proof (rd_shH K m0 _ ENV SH MU WM 32 ltac:(lia)) as RD. zstepA.             (* [comment removed for export] *)
  zstepA. rewrite ?ysx32_small by lia.                                     (* [comment removed for export] *)
  clear RD. rewrite ?zxb_small, ?sxb_small by lia. zstepA. try if_false.    (* [comment removed for export] *)
  zstepA. rewrite ?ysx32_small by lia.                                     (* [comment removed for export] *)
  zstepA. if_cases KA; zify_cond KA. 2:{ kill KA. } clear KA.               (* [comment removed for export] *)
  zstepA. if_cases K0; zify_cond K0.                                       (* [comment removed for export] *)
  2:{ (* [comment removed for export] *)
    stepA. replace (zlength (k_txt K) <=? off) with true by (symmetry; apply Z.leb_le; lia). cbn [cmt_post sub_post err_upd]. fin_at. }
  replace (zlength (k_txt K) <=? off) with false by (symmetry; apply Z.leb_gt; lia).
  rdcharA K m0 ENV KP SH MU WM rdck_109dc4 off.
  stepA. zstepA. if_cases K1; zify_cond K1.                                (* [comment removed for export] *)
  - (* [comment removed for export] *)
    replace (znth (k_txt K) off =? c_slash) with false by (symmetry; apply Z.eqb_neq; unfold c_slash; lia).
    replace (znth (k_txt K) off =? c_star) with true by (symmetry; apply Z.eqb_eq; unfold c_star; lia).
    shld (rd_shH K m0 _ ENV SH MU WM 32 ltac:(lia)). zstepA. try if_false.
    eapply evtA_mono; [eapply (block_cmt_loop (lex_fuel (zlength (k_txt K)) (off + 1))); [fin_lexmem| lia| unfold lex_fuel; lia]|].
    intros ms Hs. exact (skip_post_cmt _ _ _ _ Hs).
  - replace (znth (k_txt K) off =? c_star) with false by (symmetry; apply Z.eqb_neq; unfold c_star; lia).
    stepA. zstepA. if_cases K2; zify_cond K2.                                (* [comment removed for export] *)
    + (* [comment removed for export] *)
      replace (znth (k_txt K) off =? c_slash) with true by (symmetry; apply Z.eqb_eq; unfold c_slash; lia).
      eapply evtA_mono; [eapply (line_cmt_loop (lex_fuel (zlength (k_txt K)) (off + 1))); [fin_lexmem| lia| unfold lex_fuel; lia]|].
      intros ms Hs. exact (skip_post_cmt _ _ _ _ Hs).
    + (* [comment removed for export] *)
      replace (znth (k_txt K) off =? c_slash) with false by (symmetry; apply Z.eqb_neq; unfold c_slash; lia).
      cbn [cmt_post sub_post err_upd lex_error_code tok_code].
      stepA. zstepA. zstepA. zstepA. shadow_addr. zstepA.                    (* [comment removed for export] *)
      shld (rd_shL K m0 _ ENV SH MU WM 8 ltac:(lia)). zstepA. try if_false.  (* [comment removed for export] *)
      stepA. stepA. zstoreA ENV. stepA.                                     (* [comment removed for export] *)
      fin_at.
Qed.
End S.
End RC__1.
