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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RMallocRep RMalloc_iface RYajlRep RYajl_iface RY_lib RY_lex_kit
     RY_lex_kw RY_lex_comment RY_lex_number RY_lex_number2 RY_lex_string RY_lex_string_u8 RY_lex_string2.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlBuf YajlLeaf YajlLex YajlFactsLex YajlFactsBuf YajlFactsDecode.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Export RY_lex_main1 RY_lex_main2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Open Scope yprog_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section S.
Variable K : lexK.
Hypothesis ENV : kenv K.

(* [comment removed for export] *)
Ltac lia_cheap_lk := LiaTuning.zify_prune; first [ LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker | Zify.zify; xlia zchecker ].
Ltac mfalse_c x y := replace (x =? y) with false by (symmetry; apply Z.eqb_neq; try unfold y; lia_cheap_lk).
Ltac mtrue_c x y := replace (x =? y) with true by (symmetry; apply Z.eqb_eq; try unfold y; lia_cheap_lk).
(* [comment removed for export] *)
Ltac mnav c IA :=
  repeat (first
    [ match goal with |- context [c =? ?y] => first [ mfalse_c c y | mtrue_c c y | mtrue c y | mfalse c y ] end
    | match goal with |- context [is_lex_ws c] => first [ rewrite (is_lex_ws_false c) by lia | match goal with W : is_lex_ws c = true |- _ => rewrite W end ] end
    | match goal with |- context [is_digit c] => first [ rewrite (is_digit_true c) by lia | rewrite (is_digit_false c) by lia ] end
    | match goal with |- context [lx_allowComments _ =? 0] => rewrite IA; change (1 =? 0) with false end ];
    cbv beta iota zeta).

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma lex_loop_walk : forall (fuel : nat) (lx : ylexer) (rav s1v t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (m0 m : mem) (off start : Z),
  text_at rsegs m0 (k_T K) (k_txt K) -> lex_inv lx ->
  lexmem K m0 m (lex_error_code (lx_error lx)) off ->
  0 <= start <= off -> off <= zlength (k_txt K) -> (Z.to_nat (zlength (k_txt K) - off) < fuel)%nat ->
  evt rsegs (loop_post K m0 fuel lx off start)
    (MS (mkR rav (wz (kSP K)) (k_gp K) (k_tp K) t0 t1 t2 (wz 10) s1v (wz off) a1 a2 a3 a4 a5 a6 a7
          (wz (k_L K)) (wz (k_T K)) (wz (k_H K + 32)) (wz (zlength (k_txt K))) (wz start)
          (wz 90) (wz 49) (wz 42) (wz 47) (wz RY_JT_LEX) t3 t4 t5 t6)
        (k_F K) (wz 0x13f50) (k_fc K) None m (seg_rom rsegs)).
Proof.
  induction fuel as [|fuel IH]; intros until start; intros TX0 LI LM BS BO FUEL; [lia|].
  pose proof LM as (MU & WM & MI & STK & FR & OFF & LX & BC). pose proof ENV as ENV0. lex_prep ENV0 BC. unfold RY_JT_LEX.
  pose proof LI as (IU & IO & IL & ICH & IA & IV & IB).
  pose proof (lex_error_code_range (lx_error lx)) as ER.
  zstep. if_cases K0; zify_cond K0.
  - (* [comment removed for export] *)
    apply evt_done. unfold loop_post. exists lx, TK_eof, off, start. split; [| split; [exact LI|]].
    { rewrite ylex_loop_S. unfold yassert. replace (off <=? zlength (k_txt K)) with true by (symmetry; apply Z.leb_le; lia).
      cbn [ybind]. replace (zlength (k_txt K) <=? off) with true by (symmetry; apply Z.leb_le; lia). apply yl_ret. }
    cbn [tok_post]. fin_at.
  - (* [comment removed for export] *)
    pose proof (loop_step_leaf K fuel lx off start ltac:(lia) K0) as MS1. cbv zeta in MS1.
    (* [comment removed for export] *)
    Ltac leaf MS1 IA c lx1 tok o st1 :=
      apply evt_done; cbv beta; unfold loop_post; exists lx1, tok, o, st1;
      split; [ apply MS1; mnav c IA; apply yl_ret
            | split; [ first [ assumption | apply lex_inv_set_error; assumption ]
                     | cbn [tok_post lex_error_code lx_error lx_set_error tok_code]; fin_at ] ].
    rdchar MU TX0 off.
    set (c := znth (k_txt K) off) in *.
    zstep. if_cases K1; zify_cond K1; rewrite ?signed_small in K1 by lia.
    + (* [comment removed for export] *)
      eapply (lex_hi_walk K ENV fuel lx); [exact TX0| exact LI| fin_lexmem| lia| lia| exact K1| assumption].
    + (* [comment removed for export] *)
      zstep. zstep. if_cases K2; zify_cond K2.
      * (* [comment removed for export] *)
        digk K2; zstep; zstep; zstep; zstep; leaf MS1 IA c (lx_set_error lx LE_invalid_char) TK_error (off + 1) start.
      * (* [comment removed for export] *)
        rewrite land64_sub in K2 by lia.
        match type of K2 with context [if ?k <=? c then _ else _] => destruct (Z.leb_spec k c); [| exfalso; lia] end.
        eapply (lex_table_walk K ENV fuel IH lx); [exact TX0| exact LI| fin_lexmem| lia| lia| exact FUEL| lia].
Qed.
End S.
End RC__1.
