(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS Require MainEntryBoth SpinAlg.
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
  realizes bsegs (init_config bsegs b_init_pc b_phdrs sp brk0 mb rnd target_alloc_limit inp) (K inp).
Proof.
  intros sp brk0 mbase rdraw inp Hi0 Hv.
  pose proof (valid_input_either_of_valid_input _ Hi0) as Hi.
  assert (MAINA : forall ms mo, MainEntryBoth.bmain_at (mkEntry sp brk0 mbase rdraw) inp ms mo ->
                                SpinAlg.srealizes bsegs (mkCfg ms mo) (K inp)).
  { intros ms mo Hat. apply RzBridge.RzBridge.srealizes_bridge. exact (MainBoth.MAIN G0Both.G0 (mkEntry sp brk0 mbase rdraw) inp Hv Hi ms mo Hat). }
  rewrite (valid_entry_either _ _ _ _ _ _ _ _ Hi) in Hv.
  destruct Hv as (Hsp & Hbrk & Hmb & Hfit).
  pose proof Hi as (Hva & Hve & Hfs & _ & [Huid Hgid] & Hnof & Hsigm & Hhw & Hvasz & _).
  destruct inp as [argv envp fs stdin uid gid groups net nof sigm hw abt vasz urnd tmpf].
  cbn in Hfit, Hva, Hve, Hfs, Huid, Hgid, Hhw, Hvasz. subst vasz.
  apply RzBridge.RzBridge.realizes_of_srealizes_bridge.
  exact (MainEntryBoth.both_main_boot sp brk0 mbase rdraw argv envp fs stdin uid gid groups net nof sigm hw abt urnd tmpf
           Hsp Hbrk Hva Hve Hfit Huid Hhw _ (K_nil _) MAINA).
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
