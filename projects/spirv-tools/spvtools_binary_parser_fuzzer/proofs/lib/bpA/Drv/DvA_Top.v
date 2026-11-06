(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HPropExec HShapeAlg HShapeLaws SpinAlg Scfg HSpec HeapCeil HFBridge.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HMem HCells HStep HLFrame HMState HSysStep HExec.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ASegs AsShadow AsConst AsIface AsCXXHeap AsDriverLaws AsStack0 RtA_Iface RtA_TR.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import DvA_FuzzStmt AsDrvDefs AsMainPre DvA_MainA.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AsStartupTop AsInstance AS_InstanceKit.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require LbA_RtOwn AS_InstDefs.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require RtA_Td.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA Require BaseAsanA.
Import ListNotations.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Open Scope Z_scope.

Lemma hspec_nil : forall argv fs, HSpec.spec argv fs [].
Proof.
  intros argv fs. unfold HSpec.spec.
  destruct argv as [|a [|p [|x l]]]; try (unfold t_die; apply t_emit_has_nil).
  destruct (4096 <=? length p)%nat; [unfold t_die; apply t_emit_has_nil|].
  destruct (list_byte_eqb p []); [unfold t_die; apply t_emit_has_nil|].
  destruct (list_byte_eqb p dot_path); [apply t_alt2_has_nil_l; unfold t_die; apply t_emit_has_nil|].
  destruct (fs_lookup fs p); [apply t_alt2_has_nil_l|]; unfold t_die; apply t_emit_has_nil.
Qed.

Section Top.

  Variable FZP : fuzz_params.
  Variable LIB : list (list Z).
  Hypothesis FZ_ALL : forall (HCEIL : HeapCeil) (H : asr), asan_rt_hyps_bp H -> asan_driver_laws H -> LbA_RtOwn.rt_own H -> RtA_Td.td_law H -> fuzz_stmt H FZP.
  Hypothesis PO : fz_params_ok FZP.
  Hypothesis FZINV : forall m, mem_inv asegs m -> arelro_none m -> ACONST m -> LbA_DStat.dstat m -> fz_inv FZP m.
  Hypothesis FZINV' : forall m, fz_inv FZP m -> LbA_DStat.dstat m.
  Hypothesis LIBLEN : Nat.leb (length (TR_bp LIB)) 1000 = true.
  Hypothesis PCOST : 4 * fz_cost FZP (2 ^ 26) <= 2 ^ 38.
  Hypothesis PPF : Forall (fun pp : Z * list Z => In (fst pp :: snd pp ++ [0xe8b48]) LIB /\ ~ In (fst pp) (snd pp ++ [0xe8b48])) (fz_pf FZP).
  Hypothesis PTR : forall H : asr, as_TR H = TR_bp LIB -> fz_tr_ok FZP H.

  Hypothesis RTOWN : forall (HC : HeapCeil) (p : AS_InstDefs.iparams), @LbA_RtOwn.rt_own HC (@AS_InstDefs.KHp HC p).

  Theorem as_realizes_spec_A_of_lib : BaseAsanA.as_realizes_spec_A.
  Proof.
    unfold BaseAsanA.as_realizes_spec_A, BaseAsanA.as_realizes_spec.
    intros en inp Hen Hinp.
    destruct Hinp as (Hva & Hve & Hvfs & _ & [Huid _] & _ & _ & Hhw & Hsv48 & _).
    pose proof (proj1 (valid_entry_sv48 _ _ _ Hsv48) Hen) as Hen'.
    destruct en as [sp0 brk0 mbase rdraw]. cbn in Hen'. destruct Hen' as (Hsp & Hbrk & Hmb & Hfit).
    cbn [en_sp en_brk en_mmap_base en_draw].
    rewrite <- spec_bridge.
    apply srealizes_bridge.
    rewrite <- LIMIT_eq.
    apply (as_startup_srealizes sp0 brk0 mbase rdraw inp _ Hsp Hbrk Hmb Hva Hve Hfit Huid Hhw (hspec_nil _ _)).
    intros c HPM.
    destruct (as_instance_kit FZP LIB LIBLEN PCOST PPF PTR RTOWN sp0 brk0 mbase rdraw inp c HPM)
      as (HCEIL & H & s0 & regs & mem & B & tid & can & HHB & DL & OWN & TDL & LIVE & PRE & FS).
    apply srealizes_of_realizes.
    destruct c as [msF mo]. cbn [cfg_ms cfg_model] in *. rewrite <- FS.
    exact (as_main_A H FZP HHB DL LIVE PO FZINV FZINV' (FZ_ALL HCEIL H HHB DL OWN TDL) sp0 (in_argv inp) s0 msF mo regs mem B tid can Hva
             ltac:(rewrite FS; exact Hvfs) PRE).
  Qed.
End Top.

