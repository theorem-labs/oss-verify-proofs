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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UY_lex_kit.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlBuf YajlLex YajlFactsLex.
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
Definition skip_post (m0 : mem) (e start : Z) (r : rdres) : machine_state -> Prop :=
  match r with
  | RD_eof => lex_at K m0 J_EOF (wz 3) e (zlength (k_txt K)) start
  | RD_char _ o => lex_hd K m0 J_CMT e o start
  end.

(* [comment removed for export] *)
Ltac rdchar47 MU TX0 off :=
  zstep; rewrite ?ysx32_small by lia;
  zstep; (let K := fresh "KB" in if_cases K; zify_cond K; [ clear K | kill K ]);
  zstep; rewrite ?yzx32_small by lia;
  zstep; zstep; zstep; zstep;
  ugd; zstep; zstep; ugd; ugd;
  (let RD := fresh "RD" in
   pose proof (text_read _ _ _ _ _ off TX0 MU ltac:(intros; cbn; lia) ltac:(lia)) as RD;
   zstep; cbn beta; clear RD);
  rewrite (u8_val (znth _ off)) by (apply text_byte_range; exact (proj1 (proj2 TX0)));
  try (lazymatch goal with H : 0 <= znth _ off < 256 |- _ => idtac
       | |- _ => pose proof (text_byte_range _ off (proj1 (proj2 TX0))) end).

(* [comment removed for export] *)
Lemma line_cmt_loop : forall (fuel : nat) (rav s1v s10v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (m0 m : mem) (e off start : Z),
  text_at usegs m0 (k_T K) (k_txt K) ->
  lexmem K m0 m e off start -> 0 <= off <= zlength (k_txt K) -> (Z.to_nat (zlength (k_txt K) - off) < fuel)%nat ->
  evt usegs (skip_post m0 e start (skip_line_comment fuel (k_txt K) (zlength (k_txt K)) off))
    (MS (mkR rav (wz (kSP K)) (k_gp K) (k_tp K) t0 t1 t2 (wz 90) s1v a0 a1 a2 a3 a4 a5 a6 a7
          (wz (k_L K)) (wz (k_H K + 32)) (wz (k_T K)) (wz (zlength (k_txt K))) (wz 42)
          (wz RY_JT_LEX) (wz 0) (wz 1) s10v (wz 1) t3 t4 t5 t6)
        (k_F K) (wz 0x142b0) (k_fc K) None m (seg_rom usegs)).
Proof.
  induction fuel as [|fuel IH]; intros until start; intros TX0 (MU & WM & MI & STK & FR & OFF & LX & BC) BO FUEL; [lia|].
  lex_prep ENV BC. unfold RY_JT_LEX.
  cbn [skip_line_comment]. unfold read1.
  eofchk K0.
  - replace (zlength (k_txt K) <=? off) with false by (symmetry; apply Z.leb_gt; lia).
    rdchar MU TX0 off.
    zstep. zstep. if_cases K1; zify_cond K1.
    + (* [comment removed for export] *)
      replace (znth (k_txt K) off =? c_lf) with false by (symmetry; apply Z.eqb_neq; unfold c_lf; lia).
      eapply IH; [exact TX0| | lia| lia]. fin_lexmem.
    + replace (znth (k_txt K) off =? c_lf) with true by (symmetry; apply Z.eqb_eq; unfold c_lf; lia).
      cbn [skip_post]. fin_hd.
  - (* [comment removed for export] *)
    replace (zlength (k_txt K) <=? off) with true by (symmetry; apply Z.leb_le; lia). cbn [skip_post].
    assert (E : off = zlength (k_txt K)) by lia. rewrite E in OFF. zstep. zstep. fin_at.
Qed.

(* [comment removed for export] *)
Lemma block_cmt_loop : forall (fuel : nat) (rav s1v t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (m0 m : mem) (e off start : Z),
  text_at usegs m0 (k_T K) (k_txt K) ->
  lexmem K m0 m e off start -> 0 <= off <= zlength (k_txt K) -> (Z.to_nat (zlength (k_txt K) - off) < fuel)%nat ->
  evt usegs (skip_post m0 e start (skip_block_comment fuel (k_txt K) (zlength (k_txt K)) off))
    (MS (mkR rav (wz (kSP K)) (k_gp K) (k_tp K) t0 t1 t2 (wz 90) s1v (wz off) a1 a2 a3 a4 a5 a6 a7
          (wz (k_L K)) (wz (k_H K + 32)) (wz (k_T K)) (wz (zlength (k_txt K))) (wz 42)
          (wz RY_JT_LEX) (wz 0) (wz 1) (wz 47) (wz 1) t3 t4 t5 t6)
        (k_F K) (wz 0x14374) (k_fc K) None m (seg_rom usegs)).
Proof.
  induction fuel as [|fuel IH]; intros until start; intros TX0 (MU & WM & MI & STK & FR & OFF & LX & BC) BO FUEL; [lia|].
  lex_prep ENV BC. unfold RY_JT_LEX.
  cbn [skip_block_comment]. unfold read1.
  zstep. if_cases K0; zify_cond K0.
  { (* [comment removed for export] *)
    replace (zlength (k_txt K) <=? off) with true by (symmetry; apply Z.leb_le; lia). cbn [skip_post].
    assert (E : off = zlength (k_txt K)) by lia. rewrite E in OFF. zstep. fin_at. }
  replace (zlength (k_txt K) <=? off) with false by (symmetry; apply Z.leb_gt; lia).
  (* [comment removed for export] *)
  zstep. rewrite ?ysx32_small by lia.
  zstep. if_cases KB; zify_cond KB. 2:{ kill KB. } clear KB.
  zstep. rewrite ?yzx32_small by lia.
  zstep. rewrite (swrap32_small (off + 1)) by lia.
  zstep. zstep.
  ugd. zstep. zstep. ugd. ugd.
  pose proof (text_read _ _ _ _ _ off TX0 MU ltac:(intros; cbn; lia) ltac:(lia)) as RD.
  zstep. cbn beta. clear RD. rewrite (u8_val (znth _ off)) by (apply text_byte_range; exact (proj1 (proj2 TX0))).
  pose proof (text_byte_range _ off (proj1 (proj2 TX0))) as CR.
  zstep. if_cases K1; zify_cond K1.
  - (* [comment removed for export] *)
    replace (znth (k_txt K) off =? c_star) with false by (symmetry; apply Z.eqb_neq; unfold c_star; lia).
    eapply IH; [exact TX0| | lia| lia]. fin_lexmem.
  - (* [comment removed for export] *)
    replace (znth (k_txt K) off =? c_star) with true by (symmetry; apply Z.eqb_eq; unfold c_star; lia).
    zstep. if_cases K2; zify_cond K2.
    + (* [comment removed for export] *)
      replace (zlength (k_txt K) <=? off + 1) with true by (symmetry; apply Z.leb_le; lia). cbn [skip_post].
      assert (E : off + 1 = zlength (k_txt K)) by lia. rewrite E in OFF. zstep. fin_at.
    + replace (zlength (k_txt K) <=? off + 1) with false by (symmetry; apply Z.leb_gt; lia).
      rdchar MU TX0 (off + 1).
      zstep. if_cases K3; zify_cond K3.
      * (* [comment removed for export] *)
        replace (znth (k_txt K) (off + 1) =? c_slash) with true by (symmetry; apply Z.eqb_eq; unfold c_slash; lia).
        cbn [skip_post]. fin_hd.
      * replace (znth (k_txt K) (off + 1) =? c_slash) with false by (symmetry; apply Z.eqb_neq; unfold c_slash; lia).
        (* [comment removed for export] *)
        zstep. rewrite ?ysx32_small by lia.
        zstep. if_cases KU; zify_cond KU. 1:{ kill KU. } clear KU.
        zstep. rewrite (swrap32_small (off + 2 + -1)) by lia. zstep.
        try replace (off + 2 + -1) with (off + 1) in * by lia.
        zstep.
        eapply IH; [exact TX0| | lia| lia]. fin_lexmem.
Qed.

(* [comment removed for export] *)
Definition cmt_post (m0 : mem) (e start : Z) (r : ytok * Z * option lex_error) : machine_state -> Prop :=
  let '(tok, o, err) := r in
  match tok with
  | TK_comment => lex_hd K m0 J_CMT (err_upd e err) o start
  | _ => sub_post K m0 e start r
  end.

Lemma skip_post_cmt : forall m0 e start r ms,
  skip_post m0 e start r ms ->
  cmt_post m0 e start (match r with RD_eof => (TK_eof, zlength (k_txt K), @None lex_error)
                                  | RD_char _ o2 => (TK_comment, o2, None) end) ms.
Proof. intros m0 e start [|c o2] ms H; exact H. Qed.

(* [comment removed for export] *)
Lemma lex_comment_walk : forall (rav s1v s10v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (m0 m : mem) (e off start : Z),
  text_at usegs m0 (k_T K) (k_txt K) ->
  lexmem K m0 m e off start -> 0 <= off <= zlength (k_txt K) ->
  evt usegs (cmt_post m0 e start (ylex_comment (k_txt K) (zlength (k_txt K)) off))
    (MS (mkR rav (wz (kSP K)) (k_gp K) (k_tp K) t0 t1 t2 (wz 90) s1v a0 a1 a2 a3 a4 a5 a6 a7
          (wz (k_L K)) (wz (k_H K + 32)) (wz (k_T K)) (wz (zlength (k_txt K))) (wz 42)
          (wz RY_JT_LEX) (wz 0) (wz 1) s10v (wz 1) t3 t4 t5 t6)
        (k_F K) (wz 0x141f8) (k_fc K) None m (seg_rom usegs)).
Proof.
  intros until start. intros TX0 (MU & WM & MI & STK & FR & OFF & LX & BC) BO.
  lex_prep ENV BC. unfold RY_JT_LEX.
  unfold ylex_comment, read1.
  zstep. rewrite ?ysx32_small by lia.         (* [comment removed for export] *)
  zstep. rewrite ?ysx32_small by lia.         (* [comment removed for export] *)
  zstep. if_cases KA; zify_cond KA. 1:{ kill KA. } clear KA.
  zstep. if_cases K0; zify_cond K0.
  2:{ (* [comment removed for export] *)
      replace (zlength (k_txt K) <=? off) with true by (symmetry; apply Z.leb_le; lia). cbn [cmt_post sub_post err_upd].
      zstep. zstep. fin_at. }
  replace (zlength (k_txt K) <=? off) with false by (symmetry; apply Z.leb_gt; lia).
  rdchar47 MU TX0 off.
  zstep. if_cases K1; zify_cond K1.
  - (* [comment removed for export] *)
    replace (znth (k_txt K) off =? c_slash) with false by (symmetry; apply Z.eqb_neq; unfold c_slash; lia).
    replace (znth (k_txt K) off =? c_star) with true by (symmetry; apply Z.eqb_eq; unfold c_star; lia).
    zstep. rewrite ?ysx32_small by lia.
    eapply evt_mono; [eapply (block_cmt_loop (lex_fuel (zlength (k_txt K)) (off + 1))); [exact TX0| fin_lexmem| lia| unfold lex_fuel; lia]|].
    intros ms Hs. exact (skip_post_cmt _ _ _ _ _ Hs).
  - replace (znth (k_txt K) off =? c_star) with false by (symmetry; apply Z.eqb_neq; unfold c_star; lia).
    zstep. if_cases K2; zify_cond K2.
    + (* [comment removed for export] *)
      replace (znth (k_txt K) off =? c_slash) with false by (symmetry; apply Z.eqb_neq; unfold c_slash; lia).
      cbn [cmt_post sub_post err_upd lex_error_code tok_code].
      zstep. zstep. zstep. zstep. fin_at.
    + (* [comment removed for export] *)
      replace (znth (k_txt K) off =? c_slash) with true by (symmetry; apply Z.eqb_eq; unfold c_slash; lia).
      eapply evt_mono; [eapply (line_cmt_loop (lex_fuel (zlength (k_txt K)) (off + 1))); [exact TX0| fin_lexmem| lia| unfold lex_fuel; lia]|].
      intros ms Hs. exact (skip_post_cmt _ _ _ _ _ Hs).
Qed.
End S.
End RC__1.
