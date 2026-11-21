(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the revised entry stack block, with the strings at its top, and the launch facts; the group id in the auxv; the run's mmap base; the model's channel reader as a premise of the writes; the instance statement over the state at main with the launch conjunct; the walk over the image's own segments lifted to the run's segment list (run_segments, with the vDSO pair)). *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPropExec BShapeAlg BShapeLaws BpinAlg Bcfg BSpec BeapCeil BFBridge.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMem BCells BStep BLFrame BMState BSysStep BExec.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsDriverLaws BsStack0 RtB_Iface RtB_TR.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import DvB_FuzzStmt BsDrvDefs BsMainPre.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BsStartupTop BsMainState BsInstance.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require LbB_RtOwn.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require RtB_Td.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA Require BaseAsanA.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Common.Cfg Require SRomStable.
Import ListNotations.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Open Scope Z_scope.

Lemma hspec_nil : forall argv fs, BSpec.spec argv fs [].
Proof.
  intros argv fs. unfold BSpec.spec.
  destruct argv as [|a [|p [|x l]]]; try (unfold t_die; apply t_emit_has_nil).
  destruct (4096 <=? length p)%nat; [unfold t_die; apply t_emit_has_nil|].
  destruct (list_byte_eqb p []); [unfold t_die; apply t_emit_has_nil|].
  destruct (list_byte_eqb p dot_path); [apply t_alt2_has_nil_l; unfold t_die; apply t_emit_has_nil|].
  destruct (fs_lookup fs p); [apply t_alt2_has_nil_l|]; unfold t_die; apply t_emit_has_nil.
Qed.

Section Parts.

  Variable FZP : fuzz_params.
  Hypothesis FZ_ALL : forall (HCEIL : HeapCeil) (H : asr), asan_rt_hyps_bp H -> asan_driver_laws H -> LbB_RtOwn.rt_own H -> RtB_Td.td_law H -> fuzz_stmt H FZP.
  Hypothesis INST : as_instance_stmt P_mainL FZP.
  Hypothesis MAIN : forall (HCEIL : HeapCeil) (H : asr), asan_rt_hyps_bp H -> asan_driver_laws H ->
    (ADRV_LIVE <= as_LIVE_MAX H /\ ADRV_CNT <= as_LIVE_CNT_MAX H) -> fuzz_stmt H FZP -> as_main_realizes_stmt H FZP.

  Theorem as_realizes_spec_B_of_parts : BaseAsanA.as_realizes_spec_B.
  Proof.
    unfold BaseAsanA.as_realizes_spec_B, BaseAsanA.as_realizes_spec.
    intros en inp Hen Hinp.
    (* LPS #38: the start-up layer now discharges AsanInit's two launch facts, so pull
       them out before Hinp/Hen' are destructed.  Both are published premises -- the
       launch clause of valid_input and valid_entry's fifth conjunct -- so nothing
       weaker is assumed here.  Taken by [tauto] rather than by position, because the
       conjunct order of valid_input_either is not this file's business. *)
    assert (Hlaunch : valid_launch inp)
      by (clear - Hinp; unfold valid_input_either, valid_input in Hinp; tauto).
    (* LPS 727298f3: the published premise's channel-reader clause, for the writes *)
    assert (Hrdr : in_channel_reader inp = true)
      by (clear - Hinp; unfold valid_input_either, valid_input in Hinp; tauto).
    (* LPS 727298f3: the credentials clause's gid half, for the start state's [V_GID] *)
    assert (Hgid : valid_id (in_gid inp))
      by (clear - Hinp; unfold valid_input_either, valid_input, valid_creds in Hinp; tauto).
    destruct Hinp as (Hva & Hve & Hvfs & _ & _ & [Huid _] & _ & _ & Hhw & Hsv48 & _).
    pose proof (proj1 (valid_entry_sv48 _ _ _ Hsv48) Hen) as Hen'.
    destruct en as [sp0 brk0 mbase rdraw]. cbn in Hen'. destruct Hen' as (Hsp & Hbrk & Hmb & Hfit & Hlau).
    cbn [en_sp en_brk en_mmap_base en_draw].
    (* LPS 08b1429: the run reads the image against [run_segments]; the walk below is over the
       image's own segments, lifted by [SRomStable.srun_init] ([vdso_image] is [None] by computation) *)
    apply (SRomStable.srun_init AsanUbsan.M.loaded_segments inp sp0 mbase _ _ brk0 rdraw target_alloc_limit _ eq_refl).
    rewrite <- spec_bridge.
    apply srealizes_bridge.
    rewrite <- LIMIT_eq.
    apply (as_startup_srealizes sp0 brk0 mbase rdraw inp _ Hsp Hbrk Hmb Hva Hve Hfit Huid Hgid Hhw Hlaunch Hlau Hrdr (hspec_nil _ _)).
    intros c HPM.
    destruct (INST sp0 brk0 mbase rdraw inp c HPM)
      as (HCEIL & H & s0 & regs & mem & B & tid & can & HHB & DL & OWN & TDL & LIVE & PRE & FS).
    apply srealizes_of_realizes.
    destruct c as [msF mo]. cbn [cfg_ms cfg_model] in *. rewrite <- FS.
    exact (MAIN HCEIL H HHB DL LIVE (FZ_ALL HCEIL H HHB DL OWN TDL) sp0 (in_argv inp) s0 msF mo regs mem B tid can Hva
             ltac:(rewrite FS; exact Hvfs) PRE).
  Qed.
End Parts.
