(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: handoff_argdef is proved over the new block layout (argc and argv's two pointer words from the start state's layout facts; argv[2..], envp and the strings at the block's top from the launch's initial memory by the new amem0_def; the head from the auxv to argv[0] by main_head_def); the old-layout lemmas wrap_def and image_top are removed. *)
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

(* LPS 727298f3: the launch's initial memory is defined over the whole block, from sp up to the
   stack VMA's end (InitMem's [init_at_block], the block's length from the launch) *)
Lemma amem0_def : forall sp brk mb dr inp x,
  entry_launch_ok_va Sv48 (mkEntry sp brk mb dr) inp ->
  bv_unsigned sp <= x < bv_unsigned (ed_top dr) ->
  exists b, amem0 (mkEntry sp brk mb dr) inp (wa x) = Some b.
Proof.
  intros sp brk mb dr inp x Hlau Hx. unfold amem0. cbn [en_sp en_draw en_mmap_base].
  pose proof (length_entry_stack_image_launch Sv48 inp mb a_phdrs (Z_to_bv 64 (Z.of_N a_init_pc)) sp brk dr Hlau) as L.
  pose proof (top_of_launch inp sp brk mb dr Hlau) as TOPHI. unfold sp_window_hi in TOPHI.
  pose proof (bv_unsigned_in_range 64 sp) as RS.
  assert (Ux : bv_unsigned (wa x) = x) by (apply wa_unsigned; unfold bv_modulus in *; lia).
  rewrite (init_at_block inp mb a_phdrs (Z_to_bv 64 (Z.of_N a_init_pc)) sp dr (wa x)) by (rewrite Ux; lia).
  destruct (nth_error _ _) as [b|] eqn:E; [exists b; reflexivity|]. apply nth_error_None in E. rewrite Ux in E. lia.
Qed.

(* LPS 727298f3: every byte from sp up to sp's page end is defined at main's entry: argc and argv's
   two pointer words (the facts), argv[2..] and envp (the launch's image), the head from the auxv to
   argv[0] ([main_head_def]), the strings at the block's top (the launch's image). *)
Theorem handoff_argdef : forall en inp w V m ms mo,
  valid_entry (mkImage asegs a_init_pc a_phdrs) en inp -> valid_input_either inp ->
  main_open en inp w V m ms mo ->
  forall x, bv_unsigned (en_sp en) <= x < bv_unsigned (en_sp en) - bv_unsigned (en_sp en) mod 4096 + 4096 ->
  exists b, m (wa x) = Some b.
Proof.
  intros en inp w V m ms mo HV HI HM x Hx.
  pose proof (main_hidden en inp w V m ms mo HM) as HIDm.
  pose proof (main_head_def en inp w V m ms mo HM) as HEAD.
  pose proof HM as (_ & VR & PIN & HMF & _).
  destruct PIN as (P0 & P6 & P10 & PSP & P1 & P2 & P3 & P7 & P4 & P5 & P8 & P9 & P11 & P12).
  apply Forall_app in HMF as [HMF0 HMF]. apply Forall_app in HMF as [_ HL].
  unfold asan_mem_facts_l in HL. apply Forall_cons_iff in HL as [H0 HL]. apply Forall_cons_iff in HL as [H1 _].
  cbn [mfact_ok] in H0, H1. rewrite !zv_mkaddr in H0, H1.
  assert (ZS : zv V sp0_z = bv_unsigned (en_sp en)).
  { let ev := eval vm_compute in sp0_z in change sp0_z with ev. cbn [zv]. lia. }
  rewrite ZS in H0, H1.
  destruct en as [sp brk0 mbase rdraw].
  rewrite (valid_entry_either _ _ _ _ _ _ _ _ HI) in HV. destruct HV as (Hsp & _ & _ & _ & Hlau).
  cbn [en_sp en_draw en_brk en_mmap_base] in *.
  pose proof (geom_of_launch Sv48 inp sp brk0 mbase rdraw Hlau) as GEOM. unfold geom_ok, head_len, lsb in GEOM.
  assert (TOPP : bv_unsigned (ed_top rdraw) mod 4096 = 0)
    by (destruct Hlau as ((T1 & _) & _); unfold page_size in T1; Z.div_mod_to_equations; lia).
  assert (USPLO : 0x7fff80000000 <= bv_unsigned sp) by (destruct Hsp as [Hlo _]; unfold sp_window_lo in Hlo; lia).
  assert (XT : x < bv_unsigned (ed_top rdraw)) by (Z.div_mod_to_equations; lia).
  assert (IMGD : bv_unsigned sp <= x -> exists b, amem0 (mkEntry sp brk0 mbase rdraw) inp (wa x) = Some b)
    by (intros XL; apply (amem0_def sp brk0 mbase rdraw inp x Hlau); lia).
  destruct (Z.lt_ge_cases x (bv_unsigned sp + 8)) as [C0|C0].
  { mf V m HMF0 (MRo (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) 8 (ZV 1)) HJ.
    eapply bytes_at_def; [exact HJ| rewrite length_N_to_le_bytes; lia| lia]. }
  destruct (Z.lt_ge_cases x (bv_unsigned sp + 16)) as [C1|C1].
  { eapply bytes_at_def; [exact H0| rewrite length_N_to_le_bytes; lia| lia]. }
  destruct (Z.lt_ge_cases x (bv_unsigned sp + 24)) as [C2|C2].
  { eapply bytes_at_def; [exact H1| rewrite length_N_to_le_bytes; lia| lia]. }
  destruct (Z.lt_ge_cases x (bv_unsigned sp + 8 * Z.of_nat (length (in_argv inp)) + 8 * Z.of_nat (length (in_envp inp)) + 24)) as [C3|C3].
  { rewrite (HIDm x) by (unfold hidden_arg; cbn [en_sp]; left; lia). apply IMGD. lia. }
  destruct (Z.lt_ge_cases x (str0_of (mkEntry sp brk0 mbase rdraw) inp)) as [C4|C4].
  { apply HEAD. cbn [en_sp]. lia. }
  rewrite (HIDm x) by (unfold hidden_arg; cbn [en_sp en_draw]; right; lia). apply IMGD. lia.
Qed.
End CANSEC1.
