(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (asan_rz takes the launch's whole ProcInput apart, passes the launch, channel-reader and CONFIG_RSEQ facts MainEntry.asan_main_boot asks, and lifts the walk to the run's segment list by RomStable.srun_init; it passes MainAsan.MAIN the library node of the certificates for the start state with CONFIG_RSEQ, G0Asan.G0R, beside G0Asan.G0). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Asan.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib Require Import TopLevel.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Import DrvShape.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Top Require Import HaltsLib HaltsKitB.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS Require MainEntry SpinAlg RomStable AsanPlanCore.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AImg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require RzBridge.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueAsm.Run Require MainAsan G0Asan.
Unset Nia Cache. Unset Nra Cache.
Unset Lia Cache.
Import ListNotations.
Open Scope Z_scope.

Module HaltsAsanB.
Import DrvShape AImg.
(* [comment removed for export] *)

Definition ASAN : Image := mkImage asegs a_init_pc a_phdrs.

(* [comment removed for export] *)
Theorem asan_rz : forall sp brk0 mb rnd inp,
  valid_input inp -> valid_entry (mkImage asegs a_init_pc a_phdrs) (mkEntry sp brk0 mb rnd) inp ->
  realizes (run_segments asegs inp sp mb)
    (init_config (run_segments asegs inp sp mb) a_init_pc a_phdrs sp brk0 mb rnd target_alloc_limit inp) (K inp).
Proof.
  intros sp brk0 mbase rdraw inp Hi0 Hv.
  pose proof (valid_input_either_of_valid_input _ Hi0) as Hi.
  assert (MAINA : forall ms mo, MainEntry.amain_at (mkEntry sp brk0 mbase rdraw) inp ms mo ->
                                SpinAlg.srealizes asegs (mkCfg ms mo) (K inp)).
  { intros ms mo Hat. apply RzBridge.RzBridge.srealizes_bridge. exact (MainAsan.MAIN G0Asan.G0 G0Asan.G0R (mkEntry sp brk0 mbase rdraw) inp Hv Hi ms mo Hat). }
  apply RzBridge.RzBridge.realizes_of_srealizes_bridge.
  (* LPS 727298f3 (run_segments, from 75d69e00): the walk is over the image's own segments *)
  apply RomStable.srun_init; [reflexivity|].
  pose proof Hi as (Hva & Hve & Hfs & _ & _ & [Huid Hgid] & Hnof & Hsigm & Hhw & Hvasz & _ & Hlaunch & Hrdr & _).
  apply (proj1 (valid_entry_sv48 _ _ _ Hvasz)) in Hv.
  destruct Hv as (Hsp & Hbrk & Hmb & Hfit & Hlau).
  destruct inp as [argv envp fs stdin uid gid groups net nof sigm hw abt vasz urnd tmpf kb execfn chrdr sigdef sigterm].
  cbn in Hfit, Hva, Hve, Hfs, Huid, Hgid, Hhw, Hvasz. subst vasz.
  (* asan_main_boot takes the section hypotheses its proof uses: each from the context, the main-entry
     states' justification by computation, the trace family's empty trace by K_nil *)
  eapply (MainEntry.asan_main_boot sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nof sigm abt urnd tmpf kb execfn chrdr sigdef sigterm);
    first [exact (MainEntry.main_justified _ (AsanPlanCore.APC.rseq_z_range (kb_rseq kb))) | exact (K_nil _) | eassumption].
Qed.

Lemma lim_source_le_target : ShippedBudgets.lim_source <= target_alloc_limit.
Proof. apply (proj1 (Z.leb_le _ _)). vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Theorem halts_asanB :
  halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source HaltsKitB.S02
    (mkImage Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs).
Proof.
  change (halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source HaltsKitB.S02 ASAN).
  apply (HaltsKitB.haltsB_of_rz asegs a_init_pc a_phdrs target_alloc_limit ShippedBudgets.lim_source HaltsKitB.S02 K
           (fun inp _ => HaltsKitB.K_exits02 inp) lim_source_le_target).
  exact asan_rz.
Qed.

End HaltsAsanB.
