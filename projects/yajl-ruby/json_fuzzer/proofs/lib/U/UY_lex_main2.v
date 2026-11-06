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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UY_lex_kit UY_lex_kw UY_lex_comment UY_lex_number UY_lex_number2 UY_lex_string UY_lex_string_u8 UY_lex_string2.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlBuf YajlLeaf YajlLex YajlFactsLex YajlFactsBuf YajlFactsDecode.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Export UY_lex_main1.
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
Ltac leaf MS1 IA c lx1 tok o st1 :=
  apply evt_done; cbv beta; unfold loop_post; exists lx1, tok, o, st1;
  split; [ apply MS1; mnav c IA; apply yl_ret
        | split; [ first [ assumption | apply lex_inv_set_error; assumption ]
                 | cbn [tok_post lex_error_code lx_error lx_set_error tok_code]; fin_at ] ].

Lemma lex_table_walk : forall (fuel : nat), loop_walk_at K fuel ->
  forall (lx : ylexer) (rav s1v t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m0 m : mem) (off start : Z),
  text_at usegs m0 (k_T K) (k_txt K) -> lex_inv lx ->
  lexmem K m0 m (lex_error_code (lx_error lx)) (off + 1) start ->
  0 <= start <= off -> off < zlength (k_txt K) -> (Z.to_nat (zlength (k_txt K) - off) < S fuel)%nat ->
  9 <= znth (k_txt K) off <= 58 ->
  evt usegs (loop_post K m0 (S fuel) lx off start)
    (MS (mkR rav (wz (kSP K)) (k_gp K) (k_tp K) t0 t1 t2 (wz 90) s1v (wz (znth (k_txt K) off + -9)) (wz 49) a2 a3 a4 a5 a6 a7
          (wz (k_L K)) (wz (k_H K + 32)) (wz (k_T K)) (wz (zlength (k_txt K))) (wz 42)
          (wz RY_JT_LEX) (wz 0) (wz 1) (wz 3) (wz 1) t3 t4 t5 t6)
        (k_F K) (wz 0x141cc) (k_fc K) None m (seg_rom usegs)).
Proof.
  intros fuel IH. unfold loop_walk_at in IH. intros until start; intros TX0 LI LM BS K0 FUEL CR9.
  pose proof LM as (MU & WM & MI & STK & FR & OFF & LX & BC). pose proof ENV as ENV0. lex_prep ENV0 BC. unfold RY_JT_LEX in *.
  pose proof LI as (IU & IO & IL & ICH & IA & IV & IB).
  pose proof (lex_error_code_range (lx_error lx)) as ER.
  pose proof (loop_step_leaf K fuel lx off start ltac:(lia) K0) as MS1. cbv zeta in MS1.
  pose proof (text_byte_range _ off (proj1 (proj2 TX0))) as CR.
  set (c := znth (k_txt K) off) in *.
  zstep. zstep.
  replace ((c + -9) ≪ 2 + 67888) with (67888 + 4 * (c - 9)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  (* [comment removed for export] *)
  Ltac jgo RD := unfold RY_JT_LEX in RD; cbv delta [jt_ws_b jt_def_b jt_str_b jt_comma_b jt_num_b jt_cmt_b jt_colon_b] in RD;
                 zstep; zstep; zstep; clear RD.
  destruct (Z.eq_dec c 44) as [E44|N44].
  { pose proof (jt_read_lit _ c jt_comma_b MI ltac:(lia) ltac:(unfold jt_class; rewrite E44; reflexivity)) as RD. jgo RD.
    zstep. zstep. leaf MS1 IA c lx TK_comma (off + 1) start. }
  destruct (Z.eq_dec c 58) as [E58|N58].
  { pose proof (jt_read_lit _ c jt_colon_b MI ltac:(lia) ltac:(unfold jt_class; rewrite E58; reflexivity)) as RD. jgo RD.
    zstep. zstep. leaf MS1 IA c lx TK_colon (off + 1) start. }
  destruct (is_lex_ws c) eqn:WS.
  { (* [comment removed for export] *)
    pose proof (jt_read_ws _ c MI WS) as RD. jgo RD.
    zstep. rewrite ?ysx32_small by lia. zstep. zstep. rewrite ?(unsigned_lit start) by lia. zstep.
    zstep. if_cases K3; zify_cond K3. 2:{ kill K3. }
    eapply evt_mono; [eapply (IH lx); [exact TX0| exact LI| fin_lexmem| lia| lia| lia]|].
    intros ms Hs. unfold loop_post in Hs |- *. destruct Hs as (lx1 & tok & o1 & st1 & YL & LI1 & TP).
    exists lx1, tok, o1, st1. split; [apply MS1; mnav c IA; exact YL| split; [exact LI1| exact TP]]. }
  destruct (Z.eq_dec c 34) as [E34|N34].
  { (* [comment removed for export] *)
    clear N44 N58 WS.
    pose proof (jt_read_lit _ c jt_str_b MI ltac:(lia) ltac:(unfold jt_class; rewrite E34; reflexivity)) as RD. jgo RD.
    eapply evt_mono; [eapply (lex_string_walk K ENV); [exact TX0| fin_lexmem| lia]|].
    intros ms Hs. unfold loop_post.
    destruct (ylex_string 1 (k_txt K) (zlength (k_txt K)) (off + 1)) as [[tok o] err] eqn:ES. apply sub_post_tok in Hs.
    exists (lx_set_error_opt lx err), tok, o, start.
    split; [apply MS1; mnav c IA; rewrite IV, ?ES; cbv beta iota; apply yl_ret
          | split; [apply lex_inv_set_error_opt; exact LI| rewrite err_upd_set_error_opt; exact Hs]]. }
  destruct ((c =? c_minus) || is_digit c) eqn:ND.
  { (* [comment removed for export] *)
    pose proof (minus_digit_cases c ND) as NDC.
    pose proof (jt_read_num _ c MI WS N34 N44 ND) as RD. jgo RD. clear N44 N58 N34 WS.
    eapply evt_mono; [eapply (lex_number_walk K ENV); [exact TX0| fin_lexmem| lia]|].
    intros ms Hs. unfold loop_post.
    destruct (ylex_number (k_txt K) (zlength (k_txt K)) off) as [[tok o] err] eqn:EN. apply sub_post_tok in Hs.
    exists (lx_set_error_opt lx err), tok, o, start.
    split; [apply MS1; mnav c IA; rewrite ?ND, ?EN; cbv beta iota; rewrite ?EN; cbv beta iota; apply yl_ret
          | split; [apply lex_inv_set_error_opt; exact LI| rewrite err_upd_set_error_opt; exact Hs]]. }
  pose proof (minus_digit_not c ND) as NDN.
  destruct (Z.eq_dec c 47) as [E47|N47].
  { (* [comment removed for export] *)
    pose proof (jt_read_lit _ c jt_cmt_b MI ltac:(lia) ltac:(unfold jt_class; rewrite E47; reflexivity)) as RD. jgo RD.
    clear N44 N58 N34 WS ND NDN.
    eapply evt_cut; [eapply (lex_comment_walk K ENV); [exact TX0| fin_lexmem| lia]|].
    intros ms Hs.
    pose proof (ylex_comment_spec (k_txt K) (zlength (k_txt K)) (off + 1) ltac:(lia)) as CS.
    destruct (ylex_comment (k_txt K) (zlength (k_txt K)) (off + 1)) as [[tok o] err] eqn:EC.
    destruct tok; cbn [cmt_post] in Hs; try (exfalso; exact (proj2 CS)).
    1,2: apply sub_post_tok in Hs; apply evt_done; unfold loop_post;
         exists (lx_set_error_opt lx err); eexists; exists o, start;
         split; [apply MS1; mnav c IA; rewrite ?EC; cbv beta iota; apply yl_ret
               | split; [apply lex_inv_set_error_opt; exact LI| rewrite err_upd_set_error_opt; exact Hs]].
    (* [comment removed for export] *)
    destruct CS as (CO & -> & CO2). cbn [err_upd] in Hs.
    destruct Hs as (rav' & s1' & s10' & s11' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & LM2).
    clear MU WM MI STK FR OFF LX BC.
    pose proof LM2 as (MU & WM & MI & STK & FR & OFF & LX & BC).
    unfold kSP, kAF, kW, lexW, kframe, lex_frame, lxcells, buf_cells in MU, WM, MI, STK, FR, OFF, LX, BC |- *.
    cbn [buf_state_code yb_state yb_len yb_used ybuf_zero] in BC. unfold J_CMT, wz.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned (k_sp K) - 160)) = bv_unsigned (k_sp K) - 160) by (apply unsigned_lit; lia).
    zstep.
    zstep. call (buf_clear_null_walk (k_LB K) (k_H K + 72) (k_lo K)).
    { exact BC. }
    { lia. }
    { lia. }
    { assumption. }
    { rewrite ESP. exact STK. }
    { rewrite ESP. lia. }
    { lia. }
    { lia. }
    { exact MI. }
    { reflexivity. }
    lazymatch goal with H : stk _ _ _ _ |- _ => rewrite ESP in H; rename H into STK' end.
    lazymatch goal with H : rw_cells _ _ (k_LB K) _ |- _ => rename H into BC' end.
    unfold buf_cells in BC'. cbn [yb_len yb_data ybuf_zero buf_state_code yb_state yb_used] in BC'.
    zstep. zstep. rewrite ?ysx32_small by lia. zstep. zstep. zstep. if_cases K3; zify_cond K3. 2:{ kill K3. }
    set (lx' := lx_set_buf lx (mkBuf BS_ok 0 0 None []) (lx_bufOff lx) 0).
    assert (LI' : lex_inv lx') by (unfold lex_inv; cbn; repeat split; auto).
    eapply evt_mono; [eapply (IH lx'); [exact TX0| exact LI'| cbn [lx' lx_error lx_set_buf]; fin_lexmem| lia| lia| lia]|].
    intros ms Hs. unfold loop_post in Hs |- *. destruct Hs as (lx1 & tok1 & o1 & st1 & YL & LI1 & TP).
    exists lx1, tok1, o1, st1. split; [| split; [exact LI1| exact TP]].
    apply MS1. mnav c IA. rewrite ?EC. cbv beta iota.
    rewrite IB. unfold ybuf_clear. cbn [yb_state ybuf_zero ybind yb_len yb_data]. exact YL. }
  (* [comment removed for export] *)
  pose proof (jt_read_def _ c MI ltac:(lia) WS N34 N44 ND N47 N58) as RD. jgo RD.
  zstep. zstep. zstep. zstep. rewrite ND || idtac.
  leaf MS1 IA c (lx_set_error lx LE_invalid_char) TK_error (off + 1) start.
Qed.
End S.
End RC__1.
