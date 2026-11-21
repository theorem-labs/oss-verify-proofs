(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (both_rz takes the launch's whole ProcInput apart, passes the launch, channel-reader and CONFIG_RSEQ facts MainEntryBoth.both_main_boot asks, and lifts the walk to the run's segment list by RomStable.srun_init; it passes MainBoth.MAIN the library node of the certificates for the start state with CONFIG_RSEQ, G0Both.G0R, beside G0Both.G0). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require AsanUbsan.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib Require Import TopLevel.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Import DrvShape.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Top Require Import HaltsLib HaltsKitB.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS Require MainEntryBoth SpinAlg RomStable AsanPlanCore.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require BImg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require RzBridge.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueAsmB.Run Require MainBoth G0Both.
Unset Nia Cache. Unset Nra Cache.
Unset Lia Cache.
Import ListNotations.
Open Scope Z_scope.

Module HaltsBothB.
Import DrvShape BImg.
(* [comment removed for export] *)

Definition BOTH : Image := mkImage bsegs b_init_pc b_phdrs.

(* [comment removed for export] *)
Theorem both_rz : forall sp brk0 mb rnd inp,
  valid_input inp -> valid_entry (mkImage bsegs b_init_pc b_phdrs) (mkEntry sp brk0 mb rnd) inp ->
  realizes (run_segments bsegs inp sp mb)
    (init_config (run_segments bsegs inp sp mb) b_init_pc b_phdrs sp brk0 mb rnd target_alloc_limit inp) (K inp).
Proof.
  intros sp brk0 mbase rdraw inp Hi0 Hv.
  pose proof (valid_input_either_of_valid_input _ Hi0) as Hi.
  assert (MAINA : forall ms mo, MainEntryBoth.bmain_at (mkEntry sp brk0 mbase rdraw) inp ms mo ->
                                SpinAlg.srealizes bsegs (mkCfg ms mo) (K inp)).
  { intros ms mo Hat. apply RzBridge.RzBridge.srealizes_bridge. exact (MainBoth.MAIN G0Both.G0 G0Both.G0R (mkEntry sp brk0 mbase rdraw) inp Hv Hi ms mo Hat). }
  apply RzBridge.RzBridge.realizes_of_srealizes_bridge.
  (* LPS 727298f3 (run_segments, from 75d69e00): the walk is over the image's own segments *)
  apply RomStable.srun_init; [reflexivity|].
  pose proof Hi as (Hva & Hve & Hfs & _ & _ & [Huid Hgid] & Hnof & Hsigm & Hhw & Hvasz & _ & Hlaunch & Hrdr & _).
  apply (proj1 (valid_entry_sv48 _ _ _ Hvasz)) in Hv.
  destruct Hv as (Hsp & Hbrk & Hmb & Hfit & Hlau).
  destruct inp as [argv envp fs stdin uid gid groups net nof sigm hw abt vasz urnd tmpf kb execfn chrdr sigdef sigterm].
  cbn in Hfit, Hva, Hve, Hfs, Huid, Hgid, Hhw, Hvasz. subst vasz.
  (* both_main_boot takes the section hypotheses its proof uses: each from the context, the main-entry
     states' justification by computation, the trace family's empty trace by K_nil *)
  eapply (MainEntryBoth.both_main_boot sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nof sigm abt urnd tmpf kb execfn chrdr sigdef sigterm);
    first [exact (MainEntryBoth.main_justified _ (AsanPlanCore.APC.rseq_z_range (kb_rseq kb))) | exact (K_nil _) | eassumption].
Qed.

Lemma lim_source_le_target : ShippedBudgets.lim_source <= target_alloc_limit.
Proof. apply (proj1 (Z.leb_le _ _)). vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Theorem halts_bothB :
  halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source HaltsKitB.S02
    (mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs).
Proof.
  change (halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source HaltsKitB.S02 BOTH).
  apply (HaltsKitB.haltsB_of_rz bsegs b_init_pc b_phdrs target_alloc_limit ShippedBudgets.lim_source HaltsKitB.S02 K
           (fun inp _ => HaltsKitB.K_exits02 inp) lim_source_le_target).
  exact both_rz.
Qed.

End HaltsBothB.
