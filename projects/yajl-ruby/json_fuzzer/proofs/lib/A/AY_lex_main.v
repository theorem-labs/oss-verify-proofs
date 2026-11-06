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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import A_iface AYajlRep AYajl_iface AY_rz AY_lex_rdck AY_lex_kit AY_lex_kw AY_lex_main1 AY_lex_main2.
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
Hypothesis NUM : lex_number_stmt K m0.
Hypothesis STR : lex_string_stmt K m0.
Hypothesis CMT : lex_comment_stmt K m0.
Hypothesis BCLR : aybuf_clear_stmt.

Ltac leaf MS1 IA c lx1 tok o st1 :=
  apply evtA_done; cbv beta; unfold loop_post; exists lx1, tok, o, st1;
  split; [ apply MS1; mnav c IA; apply yl_ret
        | split; [ first [ assumption | apply lex_inv_set_error; assumption ]
                 | cbn [tok_post lex_error_code lx_error lx_set_error tok_code]; fin_at ] ].

Lemma lex_loop_walk : forall fuel, loop_walk_at K m0 fuel.
Proof. aceil.
  induction fuel as [|fuel IH]; unfold loop_walk_at; intros until start; intros LI LM BS BO FUEL; [lia|].
  pose proof LM as (MU & WM & MI & ST & FR & OFF & LX & BC). lex_prep ENV BC. unfold AY_JT_LEX, J_HD in *.
  pose proof LI as (IU & IO & IL & ICH & IA & IV & IB).
  pose proof (lex_error_code_range (lx_error lx)) as ER.
  polu KP kp_Ls PLS. polu KP kp_L PL. polu KP kp_T PT. polu KP kp_Hs PHS. polu KP kp_H PH. polu KP kp_stk PSTK.
  zstepA. if_cases K0; zify_cond K0.                                         (* [comment removed for export] *)
  2:{ (* [comment removed for export] *)
    stepA. apply evtA_done. unfold loop_post. exists lx, TK_eof, off, start. split; [| split; [exact LI|]].
    { rewrite ylex_loop_S. unfold yassert. replace (off <=? zlength (k_txt K)) with true by (symmetry; apply Z.leb_le; lia).
      cbn [ybind]. replace (zlength (k_txt K) <=? off) with true by (symmetry; apply Z.leb_le; lia). apply yl_ret. }
    cbn [tok_post]. fin_at. }
  pose proof (loop_step_leaf K fuel lx off start ltac:(lia) K0) as MS1. cbv zeta in MS1.
  rdcharA K m0 ENV KP SH MU WM rdck_109c88 off.
  set (c := znth (k_txt K) off) in *.
  stepA. zstepA. if_cases K1; zify_cond K1; rewrite ?signed_small in K1 by lia.      (* [comment removed for export] *)
  - (* [comment removed for export] *)
    eapply (lex_hi_walk K m0 ENV KP SH fuel lx); [exact LI| fin_lexmem| lia| lia| exact K1| assumption].
  - (* [comment removed for export] *)
    zstepA. stepA. zstepA. if_cases K2; zify_cond K2.                        (* [comment removed for export] *)
    + (* [comment removed for export] *)
      rewrite land64_sub in K2 by lia.
      match type of K2 with context [if ?k <=? c then _ else _] => destruct (Z.leb_spec k c); [| exfalso; lia] end.
      eapply (lex_table_walk K m0 ENV KP SH NUM STR CMT BCLR fuel IH lx); [exact LI| fin_lexmem| lia| lia| exact FUEL| lia].
    + (* [comment removed for export] *)
      digk K2; stepA; zstepA; zstepA; zstepA; shadow_addr; zstepA;
        shld (rd_shL K m0 _ ENV SH MU WM 8 ltac:(lia)); zstepA; try if_true;
        stepA; stepA; zstoreA ENV; stepA; leaf MS1 IA c (lx_set_error lx LE_invalid_char) TK_error (off + 1) start.
Qed.
End S.
End RC__1.
