(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import PropExec MState Mem InitMem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import MainExport MainFactsAsan MainEntry CatExec AsanInit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib Require Import TopLevel AsanMainU.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AImg AD_handoff0.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.

Lemma bytes_at_def : forall m a bs x, bytes_at asegs m a bs -> a <= x < a + Z.of_nat (length bs) -> 0x665000 <= x ->
  exists b, m (wa x) = Some b.
Proof.
  intros m a bs x (A & B & C) Hx Hlo.
  specialize (C (Z.to_nat (x - a)) ltac:(lia)).
  replace (a + Z.of_nat (Z.to_nat (x - a))) with x in C by lia.
  rewrite ref_mrd_overlay in C by (rewrite wa_unsigned by lia; lia).
  destruct (nth_error bs (Z.to_nat (x - a))) as [b|] eqn:E; [exists b; exact C|]. apply nth_error_None in E. lia.
Qed.

Lemma mro8_def : forall V m a v x, mfact_ok asegs V m (MRo a 8 v) -> zv V a <= x < zv V a + 8 -> 0x665000 <= x ->
  exists b, m (wa x) = Some b.
Proof. intros V m a v x H Hx Hlo. cbn [mfact_ok] in H. eapply bytes_at_def; [exact H| rewrite length_N_to_le_bytes; lia| exact Hlo]. Qed.

(* [comment removed for export] *)
Lemma wrap_def : forall ph sp argv envp uid hw draw x, bv_unsigned sp <= x < bv_unsigned sp + Z.of_nat (length (entry_stack_image ph sp argv envp uid hw draw)) ->
  x < 2^64 -> exists b, wrap_mem ph sp argv envp uid hw draw (wa x) = Some b.
Proof.
  intros ph sp argv envp uid hw draw x Hx H64. rewrite init_at. rewrite wa_unsigned by (pose proof (bv_unsigned_in_range 64 sp); lia).
  replace (Z.leb (bv_unsigned sp) x) with true by (symmetry; apply Z.leb_le; lia).
  replace (Z.ltb (x - bv_unsigned sp) (Z.of_nat (length (entry_stack_image ph sp argv envp uid hw draw)))) with true by (symmetry; apply Z.ltb_lt; lia).
  destruct (nth_error _ _) as [b|] eqn:E; [exists b; reflexivity|]. apply nth_error_None in E. lia.
Qed.

(* [comment removed for export] *)
Lemma image_top : forall ph sp argv envp uid hw draw,
  bv_unsigned sp + Z.of_nat (length (entry_stack_image ph sp argv envp uid hw draw))
  = page_round_up_Z (bv_unsigned sp + Z.of_nat (length (build_stack_bytes ph sp argv envp uid hw draw))).
Proof.
  intros. unfold entry_stack_image. cbv zeta. rewrite length_app, length_entry_slack. unfold entry_slack_len, entry_page_top, entry_block_top.
  set (t := bv_unsigned sp + Z.of_nat (length (build_stack_bytes ph sp argv envp uid hw draw))).
  assert (t <= page_round_up_Z t) by (unfold page_round_up_Z, page_size; Z.div_mod_to_equations; lia).
  rewrite Nat2Z.inj_add, Z2Nat.id by lia. unfold t. lia.
Qed.

Theorem handoff_argdef : forall en inp w V m ms mo,
  valid_entry (mkImage asegs a_init_pc a_phdrs) en inp -> valid_input_either inp ->
  main_open en inp w V m ms mo ->
  forall x, bv_unsigned (en_sp en) <= x < bv_unsigned (en_sp en) - bv_unsigned (en_sp en) mod 4096 + 4096 ->
  exists b, m (wa x) = Some b.
Proof.
  intros en inp w V m ms mo HV HI HM x Hx.
  destruct en as [sp brk0 mbase rdraw]. rewrite (valid_entry_either _ _ _ _ _ _ _ _ HI) in HV. destruct HV as (Hsp & _ & _ & Hfit).
  pose proof HI as (Hva & Hve & _).
  pose proof HM as (_ & VR & PIN & HMF & _ & _ & _ & HID & _). apply Forall_app in HMF as [HMF _].
  destruct PIN as (P0 & P6 & P10 & PSP & P1 & P2 & P3 & P7 & P4 & _).
  cbn [en_sp en_draw en_brk en_mmap_base] in *.
  set (argv := in_argv inp) in *. set (envp := in_envp inp) in *.
  set (usp := bv_unsigned sp) in *.
  pose proof (AsanInit.bsb_ge a_phdrs sp rdraw argv envp (in_uid inp) (in_hwcap inp)) as [G GM].
  pose proof (AsanInit.len_av a_phdrs sp rdraw argv envp (in_uid inp) (in_hwcap inp) Hva) as LAV. pose proof (AsanInit.len_ev a_phdrs sp rdraw argv envp (in_uid inp) (in_hwcap inp) Hve) as LEV.
  pose proof (AsanInit.usp_fit a_phdrs sp rdraw argv envp (in_uid inp) (in_hwcap inp) Hfit) as UF.
  pose proof (image_top a_phdrs sp argv envp (in_uid inp) (in_hwcap inp) rdraw) as IT.
  set (LB := Z.of_nat (length (build_stack_bytes a_phdrs sp argv envp (in_uid inp) (in_hwcap inp) rdraw))) in *.
  assert (HW : 8 * Wblk (mkEntry sp brk0 mbase rdraw) inp = LB - 16 - (8 * Z.of_nat (length argv) + 8 * Z.of_nat (length envp) + 184)).
  { unfold Wblk. cbn [en_sp en_draw]. fold argv envp. fold LB. Z.div_mod_to_equations. lia. }
  assert (USPLO : 0x7fff80000000 <= usp) by (destruct Hsp as [Hlo _]; unfold sp_window_lo in Hlo; lia).
  assert (PT : usp - usp mod 4096 + 4096 <= page_round_up_Z (usp + LB)) by (unfold page_round_up_Z, page_size; Z.div_mod_to_equations; lia).
  assert (XH : x < 2^47) by (unfold page_round_up_Z, page_size in *; Z.div_mod_to_equations; lia).
  (* [comment removed for export] *)
  assert (HIDDEF : hidden_arg (mkEntry sp brk0 mbase rdraw) inp x -> exists b, m (wa x) = Some b).
  { intros Hh. rewrite (HID x Hh). apply wrap_def; [| lia]. rewrite IT. fold LB.
    unfold hidden_arg in Hh. cbn [en_sp] in Hh. fold argv envp usp in Hh. rewrite HW in Hh. unfold page_round_up_Z, page_size in *. Z.div_mod_to_equations. lia. }
  assert (V0E : 32768 * V 0%nat + (16 * V 6%nat + 4096 * V 10%nat) = usp) by lia.
  destruct (Z.lt_ge_cases x (usp + 24)) as [C1|C1].
  { destruct (Z.lt_ge_cases x (usp + 8)) as [D1|D1]; [| destruct (Z.lt_ge_cases x (usp + 16)) as [D2|D2]].
    - mf V m HMF (MRo (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) 8 (ZV 1)) HJ. eapply bytes_at_def; [exact HJ| rewrite length_N_to_le_bytes; lia| lia].
    - mf V m HMF (MRo (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit 8)) 8 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 184))) HJ. eapply bytes_at_def; [exact HJ| rewrite length_N_to_le_bytes; lia| lia].
    - mf V m HMF (MRo (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit 16)) 8 (ZMul (ZLtu (ZLit 1) (ZV 1)) (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZV 3) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10))))))) (ZLit 185)))) HJ. eapply bytes_at_def; [exact HJ| rewrite length_N_to_le_bytes; lia| lia]. }
  destruct (Z.lt_ge_cases x (usp + 8 * Z.of_nat (length argv) + 8 * Z.of_nat (length envp) + 24)) as [C2|C2].
  { apply HIDDEF. unfold hidden_arg. cbn [en_sp]. fold argv envp usp. left. lia. }
  destruct (Z.lt_ge_cases x (usp + 8 * Z.of_nat (length argv) + 8 * Z.of_nat (length envp) + 184)) as [C3|C3].
  { set (j := (x - (usp + 8 * Z.of_nat (length argv) + 8 * Z.of_nat (length envp) + 24)) / 8).
    assert (J : 0 <= j < 20) by (unfold j; Z.div_mod_to_equations; lia).
    assert (JX : usp + 8 * Z.of_nat (length argv) + 8 * Z.of_nat (length envp) + 24 + 8 * j <= x
                 < usp + 8 * Z.of_nat (length argv) + 8 * Z.of_nat (length envp) + 24 + 8 * j + 8) by (unfold j; Z.div_mod_to_equations; lia).
    clearbody j.
    assert (JC : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8 \/ j = 9 \/ j = 10 \/ j = 11 \/ j = 12 \/ j = 13
                 \/ j = 14 \/ j = 15 \/ j = 16 \/ j = 17 \/ j = 18 \/ j = 19) by lia.
    destruct JC as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]]]]]]].
    - mf V m HMF (MRo (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 24)) 8 (ZLit 3)) HJ. eapply bytes_at_def; [exact HJ| rewrite length_N_to_le_bytes; lia| lia].
    - mf V m HMF (MRo (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 32)) 8 (ZLit 65600)) HJ. eapply bytes_at_def; [exact HJ| rewrite length_N_to_le_bytes; lia| lia].
    - mf V m HMF (MRo (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 40)) 8 (ZLit 4)) HJ. eapply bytes_at_def; [exact HJ| rewrite length_N_to_le_bytes; lia| lia].
    - mf V m HMF (MRo (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 48)) 8 (ZLit 56)) HJ. eapply bytes_at_def; [exact HJ| rewrite length_N_to_le_bytes; lia| lia].
    - mf V m HMF (MRo (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 56)) 8 (ZLit 5)) HJ. eapply bytes_at_def; [exact HJ| rewrite length_N_to_le_bytes; lia| lia].
    - mf V m HMF (MRo (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 64)) 8 (ZLit 11)) HJ. eapply bytes_at_def; [exact HJ| rewrite length_N_to_le_bytes; lia| lia].
    - mf V m HMF (MRo (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 72)) 8 (ZLit 16)) HJ. eapply bytes_at_def; [exact HJ| rewrite length_N_to_le_bytes; lia| lia].
    - mf V m HMF (MRo (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 80)) 8 (ZV 9)) HJ. eapply bytes_at_def; [exact HJ| rewrite length_N_to_le_bytes; lia| lia].
    - mf V m HMF (MRo (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 88)) 8 (ZLit 6)) HJ. eapply bytes_at_def; [exact HJ| rewrite length_N_to_le_bytes; lia| lia].
    - mf V m HMF (MRo (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 96)) 8 (ZLit 4096)) HJ. eapply bytes_at_def; [exact HJ| rewrite length_N_to_le_bytes; lia| lia].
    - mf V m HMF (MRo (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 104)) 8 (ZLit 11)) HJ. eapply bytes_at_def; [exact HJ| rewrite length_N_to_le_bytes; lia| lia].
    - mf V m HMF (MRo (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 112)) 8 (ZV 8)) HJ. eapply bytes_at_def; [exact HJ| rewrite length_N_to_le_bytes; lia| lia].
    - mf V m HMF (MRo (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 120)) 8 (ZLit 12)) HJ. eapply bytes_at_def; [exact HJ| rewrite length_N_to_le_bytes; lia| lia].
    - mf V m HMF (MRo (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 128)) 8 (ZV 8)) HJ. eapply bytes_at_def; [exact HJ| rewrite length_N_to_le_bytes; lia| lia].
    - mf V m HMF (MRo (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 136)) 8 (ZLit 23)) HJ. eapply bytes_at_def; [exact HJ| rewrite length_N_to_le_bytes; lia| lia].
    - mf V m HMF (MRo (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 144)) 8 (ZLit 0)) HJ. eapply bytes_at_def; [exact HJ| rewrite length_N_to_le_bytes; lia| lia].
    - mf V m HMF (MRo (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 152)) 8 (ZLit 25)) HJ. eapply bytes_at_def; [exact HJ| rewrite length_N_to_le_bytes; lia| lia].
    - mf V m HMF (MRo (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 160)) 8 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 8) (ZV 4)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10))))))) (ZLit 184))) HJ. eapply bytes_at_def; [exact HJ| rewrite length_N_to_le_bytes; lia| lia].
    - mf V m HMF (MRo (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 168)) 8 (ZLit 0)) HJ. eapply bytes_at_def; [exact HJ| rewrite length_N_to_le_bytes; lia| lia].
    - mf V m HMF (MRo (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 176)) 8 (ZLit 0)) HJ. eapply bytes_at_def; [exact HJ| rewrite length_N_to_le_bytes; lia| lia]. }
  destruct (Z.lt_ge_cases x (usp + 8 * Z.of_nat (length argv) + 8 * Z.of_nat (length envp) + 184 + 8 * Wblk (mkEntry sp brk0 mbase rdraw) inp)) as [C4|C4].
  { apply HIDDEF. unfold hidden_arg. cbn [en_sp]. fold argv envp usp. right; left. lia. }
  destruct (Z.lt_ge_cases x (usp + 8 * Z.of_nat (length argv) + 8 * Z.of_nat (length envp) + 200 + 8 * Wblk (mkEntry sp brk0 mbase rdraw) inp)) as [C5|C5].
  { mf V m HMF (MBlobD (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 8) (ZV 4)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10))))))) (ZLit 184)) 16) HJ. cbn [zv] in HJ.
    destruct (HJ (x - (32768 * V 0%nat + (8 * V 1%nat + (8 * V 2%nat + (8 * V 4%nat + (16 * V 6%nat + 4096 * V 10%nat)))) + 184)) ltac:(lia)) as [b Hb].
    exists b. replace x with (32768 * V 0%nat + (8 * V 1%nat + (8 * V 2%nat + (8 * V 4%nat + (16 * V 6%nat + 4096 * V 10%nat)))) + 184
                               + (x - (32768 * V 0%nat + (8 * V 1%nat + (8 * V 2%nat + (8 * V 4%nat + (16 * V 6%nat + 4096 * V 10%nat)))) + 184))) by lia.
    exact Hb. }
  apply HIDDEF. unfold hidden_arg. cbn [en_sp]. fold argv envp usp. right; right. split; [lia|].
  rewrite HW. replace (usp + 8 * Z.of_nat (length argv) + 8 * Z.of_nat (length envp) + 200 + (LB - 16 - (8 * Z.of_nat (length argv) + 8 * Z.of_nat (length envp) + 184)))
    with (usp + LB) by lia. lia.
Qed.
End CANSEC1.
