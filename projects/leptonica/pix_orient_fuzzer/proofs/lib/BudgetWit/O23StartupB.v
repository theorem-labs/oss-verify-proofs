(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* Modified by Theorem Labs, 2026-11: made from O23/O23Startup.v: ref_startup_sec and ref_startup restated over the budget carrier rzb, with their released statements; their released proofs are KReplay terms, so they are re-proved by hand (Hlo, Hhi, Hal likewise). *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch input ProcInput; the m_channel_reader premise; the vDSO). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Vdso Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.pix_orient_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Amb.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import ShapeAlg PureModel RefNodesMF StartupTac ArgvEnv RefLayout.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Reloc Require Import Reloc.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Musl Require StartupBase StartupDefs Startup.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23StartupDefs O23Reloc O23RelocCode O23RelocSites O23RelocImg O23RelocMusl O23RelocStart.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23Startup.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.BudgetWit Require Import Rzb StartupB.
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := Plain.M.loaded_segments.
Abbreviation RPH := Plain.M.phdrs.
(* [comment removed for export] *)
Local Notation rsegs := Plain.M.loaded_segments (only parsing).
Local Notation rpc := Plain.M.init_pc (only parsing).
Local Notation rph := Plain.M.phdrs (only parsing).

(* [O23Startup.ref_startup] over [rzb]: [StartupB.ref_startup_b] at this image's relocation,
   then [O23Startup.main_entry_L] to this image's entry record *)
Theorem ref_startup : forall sp brk mbase draw lim inp K (Hrd : in_channel_reader inp = true),
  valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase draw) inp ->
  (forall tid regs mem,
     (0 < bv_unsigned tid < 2^22)%Z ->
     @main_entry (amb_of inp draw mbase Hrd) sp (in_argv inp) (in_envp inp) tid regs mem ->
     rzb rsegs (mkCfg (mkst (fx:=fx0) regs (0x62b1c : word) mem (seg_rom rsegs))
                      (with_tid tid (with_vdso (vdso_run_init (ed_vdso draw))
                                       (init_model (segments_reserved rsegs) brk mbase sp lim inp)))) K) ->
  rzb rsegs (init_config rsegs rpc rph sp brk mbase draw lim inp) K.
Proof.
  intros sp brk mbase draw lim inp K Hrd Hsp Hva Hve Hvl Hlau HK.
  refine (@StartupB.ref_startup_b o23_reloc o23_code o23_sites o23_img o23_data o23_rw o23_start
            rpc _ sp brk mbase draw lim inp K Hsp Hva Hve Hvl Hlau _).
  - apply bv_eq; reflexivity.
  - intros tid regs mem Htid ME.
    pose proof (HK tid regs mem Htid (main_entry_L _ _ _ _ _ _ _ _ Hrd Hvl Hlau ME)) as R.
    bvlit64_to_Z_in R. exact R.
Qed.
