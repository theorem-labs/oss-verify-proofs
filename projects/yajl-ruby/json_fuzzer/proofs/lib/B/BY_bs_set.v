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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import MallocRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlBuf YajlLex YajlParser YajlFactsBuf.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import InitMem SysStep Arr SFW1_lemmas.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RYajlRep RY_lib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 AImages Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BY_ubkit B_iface BI_shadow BYajlRep BYajl_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac kill K := exfalso; revert K; unfold wz; rewrite ?unsigned_lit by lia;
  try (change 18446744073709551615 with (Z.ones 64); rewrite ?Z.land_ones by lia; rewrite ?Z.mod_small by lia); lia.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac aceil := first [pose proof alloc_ceiling_range as CEILB | idtac].
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Theorem aybs_set_proof : aybs_set_stmt.
Proof. aceil.
  unfold aybs_set_stmt. intros P h mh s s' rest lo. intros until m.
  intros (MHP & MHA & STKP) STA HS BSR HST HBLK OSH OSS SH1 SH2 SS1 SS2 SEP MI ST LOC LO SPH -> -> PSTK PIMG PH PS.
  unfold wz in *. unfold AY_BS_SET.
  destruct STA as (G1 & G2 & G3 & G4). unfold AY_GOT_SHADOW, AY_SHADOW_VAR, AY_GOT_UAR, AY_UAR_VAR, A_SB, wz in G1, G2, G3, G4.
  aceil. unfold SIZEOF_HANDLE in *.
  unfold opol, pol, oshw_lo, oshw_hi, A_SB, amem in PSTK, PIMG, PH, PS, SH1, SS1. unfold AY_IMG_LO, AY_IMG_HI in PIMG.
  change (2147450880 + 0 / 8 + (2 ^ 47 + 7) / 8) with 0x10007fff8000 in SH1, SS1.
  destruct PH as [PH PHS]. destruct PS as [PS PSS].
  destruct HS as ((pew & pad & HC & PEW) & HB1 & HB2 & HB3 & HB4).
  unfold hand_cells, hand_head_cells, alloc_cells in HC. cbn [app] in HC. unfold wz in HC.
  pose proof BSR as BSR0. unfold bs_rep in BSR. destruct (h_stack_blk h) as [sbk|] eqn:ESB; [| exfalso; exact (HBLK eq_refl)].
  destruct BSR as [SBNZ [junk BSC]].
  assert (USED : h_used h = zlength rest + 1) by (unfold h_used; rewrite HST; unfold zlength; cbn [length]; lia).
  pose proof (zlength_nonneg rest) as Z0.
  pose proof (u8arr_of_CB2 bsegs m _ _ _ _ _ BSC) as (ARR & L1 & L2). clear BSC.
  pose proof (block_shadow_bound bsegs m _ _ _ OSH) as BH. pose proof (block_shadow_bound bsegs m _ _ _ OSS) as BSB. unfold A_SB in BH, BSB.
  unfold oshadow, A_SB in OSH, OSS. open_shadow OSH. open_shadow OSS.
  pose proof (bv_unsigned_in_range 64 sp) as SR. unfold bv_modulus in SR. cbn in SR.
  assert (SC : 0 <= state_code s' < 16) by (destruct s'; cbn; lia).
  assert (MU : munch [(lo, bv_unsigned sp); (mh_stack mh + h_used h - 1, mh_stack mh + h_used h)] m m) by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  carve_frame 32%nat ST.                      (* [comment removed for export] *)
  stepA. stepA. stepA. stepA.                  (* [comment removed for export] *)
  zstepA. ugd.                                 (* [comment removed for export] *)
  do 3 stepA.                                  (* [comment removed for export] *)
  zstepA.                                      (* [comment removed for export] *)
  shadow_fast OSH (mh_addr mh + 60) 4.         (* [comment removed for export] *)
  zstepA. rewrite ysx32_small by lia.          (* [comment removed for export] *)
  zstepA. if_cases K0; zify_cond K0. { kill K0. }   (* [comment removed for export] *)
  zstepA.                                      (* [comment removed for export] *)
  shadow_fast OSH (mh_addr mh + 56) 4.         (* [comment removed for export] *)
  zstepA. rewrite ysx32_small by lia.          (* [comment removed for export] *)
  zstepA. if_cases K1; zify_cond K1. { kill K1. }   (* [comment removed for export] *)
  shadow_fast OSH (mh_addr mh + 48) 8.         (* [comment removed for export] *)
  zstepA.                                      (* [comment removed for export] *)
  zstepA. zstepA. zstepA. rewrite (land_M32_small (h_used h + -1)) by lia.   (* [comment removed for export] *)
  zstepA.                                      (* [comment removed for export] *)
  ugd. zstepA. zstepA. zstepA. ugd. ugd.       (* [comment removed for export] *)
  assert (G8 : (mh_stack mh + (h_used h + -1)) mod 8 + 1 <= 8) by (clear; Z.div_mod_to_equations; lia).
  shadow_cases OSS (mh_stack mh + (h_used h + -1)) 1.   (* [comment removed for export] *)
  2: shadow_slow.
  all: lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
         pose proof (u8arr_store_ok_at bsegs mx (mh_stack mh) _ (h_used h + -1) ARR ltac:(rewrite length_app, L1, L2; lia)) as SOK end.
  all: stepA.                                  (* [comment removed for export] *)
  all: lazymatch type of ARR with u8arr _ ?mx _ _ =>
         pose proof (u8arr_write bsegs mx (mh_stack mh) _ (h_used h + -1) (Z_to_bv 8 (state_code s')) ARR ltac:(rewrite length_app, L1, L2; lia)) as ARR' end.
  all: rewrite le1_wz by lia; clear ARR; store_done.
  all: stepA; stepA; stepA; stepA; stepA.      (* [comment removed for export] *)
  all: release_frame FR ST (bv_unsigned sp).
  all: unfold aybs_set_rpost; finishA.
  all: try (unfold ay_statics, AY_GOT_SHADOW, AY_SHADOW_VAR, AY_GOT_UAR, AY_UAR_VAR, A_SB, wz; split; [|split; [|split]]; assumption).
  all: try (unfold oshadow, block_shadow, A_SB; split; [assumption|]; split; [assumption|]; first [rewrite <- OSHeq; assumption | rewrite <- OSSeq; assumption]).
  all: lazymatch goal with
       | |- RYajlRep.hand_struct _ _ _ _ _ =>
           split; [exists pew, pad; split; [unfold hand_cells, hand_head_cells, alloc_cells; cbn [app]; unfold wz; assumption | exact PEW]|];
           split; [exact HB1|]; split; [exact HB2|]; split; [exact HB3|]; rewrite ESB; exact HB4
       | |- RYajlRep.bs_rep _ _ _ _ =>
           unfold bs_rep; cbn [h_stack_blk h_set_stack h_stack h_stack_size]; rewrite ESB; split; [exact SBNZ|]; exists junk;
           replace (h_used (h_set_stack h (s' :: rest))) with (h_used h) by (rewrite USED; unfold h_used; cbn [h_stack h_set_stack]; unfold zlength; cbn [length]; lia);
           apply CB2_of_u8arr; [| rewrite zbytes_length, stack_bytes_length; cbn [length]; unfold zlength in USED; clear -CEILB USED Z0; unfold zlength; lia | exact L2];
           lazymatch goal with H : u8arr bsegs _ _ (upd _ _ _) |- _ =>
             revert H; rewrite HST, !stack_bytes_cons, !zbytes_app; cbn [zbytes map]; rewrite <- !app_assoc; cbn [app];
             rewrite (upd_app_len _ _ _ _ _) by (rewrite zbytes_length, stack_bytes_length; unfold zlength in USED; clear -CEILB USED Z0; unfold zlength; lia);
             intros H; exact H end
       end.
Qed.
End RC__1.
