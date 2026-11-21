(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* Modified by Theorem Labs, 2026-11: made from O2/O2Startup.v: ref_startup_sec and ref_startup restated over the budget carrier rzb, with their released statements; their released proofs are KReplay terms, so they are re-proved by hand (Hlo, Hhi, Hal likewise). *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (ref_startup takes the channel-reader premise and the launch facts, starts from the vDSO run state and is proved from StartupB.ref_startup_sec_b; ref_startup_sec, Hlo, Hhi and Hal dropped as in the source). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.bilateral_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Amb.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import ShapeAlg PureModel RefNodesMF StartupTac ArgvEnv RefLayout.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Reloc Require Import Reloc.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Musl Require StartupBase StartupDefs Startup.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.O2 Require Import O2StartupDefs O2Reloc O2RelocCode O2RelocSites O2RelocImg O2RelocMusl O2RelocStart.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.O2 Require Import O2Startup.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.BudgetWit Require Import Rzb StartupB.
From LinuxProcessSemantics.LinuxProcessSem Require Import Vdso.
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := Plain.M.loaded_segments.
Abbreviation RPH := Plain.M.phdrs.
(* [comment removed for export] *)
Local Notation rsegs := Plain.M.loaded_segments (only parsing).
Local Notation rpc := Plain.M.init_pc (only parsing).
Local Notation rph := Plain.M.phdrs (only parsing).

(* [comment removed for export] *)
Theorem ref_startup : forall sp brk mbase draw lim inp K (Hrd : in_channel_reader inp = true),
  valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase draw) inp ->
  (forall tid regs mem,
     (0 < bv_unsigned tid < 2^22)%Z ->
     @main_entry (amb_of inp draw mbase Hrd) sp (in_argv inp) (in_envp inp) tid regs mem ->
     rzb rsegs (mkCfg (mkst (fx:=fx0) regs (0x17618 : word) mem (seg_rom rsegs))
                      (with_tid tid (with_vdso (vdso_run_init (ed_vdso draw))
                                       (init_model (segments_reserved rsegs) brk mbase sp lim inp)))) K) ->
  rzb rsegs (init_config rsegs rpc rph sp brk mbase draw lim inp) K.
Proof.
  intros sp brk mbase draw lim inp K Hrd Hsp Hva Hve Hvl Hlau HK.
  refine (@StartupB.ref_startup_sec_b o2_reloc o2_code o2_sites o2_img o2_data o2_rw o2_start
            sp inp mbase brk draw Hva Hve Hsp Hvl Hlau rpc _ lim K _).
  - apply bv_eq; reflexivity.
  - intros tid regs mem Htid ME.
    pose proof (HK tid regs mem Htid (main_entry_L _ _ _ _ _ _ _ _ Hrd Hvl Hlau ME)) as R.
    bvlit64_to_Z_in R. exact R.
Qed.
