(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the revised entry stack block, with the strings at its top, and the launch facts; the run's mmap base; the model's channel reader as a premise of the writes; recorded proofs re-encoded or written as text where the change reaches them). *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import Amb RunRandom PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SymExec SymExec2 SymExec2Sound SymDriveX SRealizes.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import S1Spec U1Cells U1Start U1BootDefs U1MainEntry U1MainEntryN U1ReadErr.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section FXALL1.
Context {fx : FPState}.

Record dir_tail_pre {AMB : Amb} {RRND : RunRandom} (sp0 p1 : word) (tid : Z) (mem0 : word -> option byte)
       (R : bvmap 5 word) (M : word -> option byte) : Prop := DIR_TAIL_PRE {
  dt_sp : getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 128);
  dt_gp : getr R 3 = Z_to_bv 64 0x10800;
  dt_tp : getr R 4 = Z_to_bv 64 0x102418;
  dt_s2 : getr R 18 = p1;
  dt_stack : stack_writable M sp0;
  dt_img : Forall (fun iv => img_clear M (fst iv) (snd iv)) re_ivs;
  dt_tid : cell M 0x102370 4 tid;
  dt_tidr : (0 < tid < 2 ^ 22)%Z;
  dt_self : cell M 0x102350 8 0x102350;
  dt_canary : cell M 0x122688 8 rr_canary;
  dt_pagesz : cell M 0x1226d8 8 4096;
  dt_nlocks : cell M 0x1226ab 1 0;
  dt_path : rdn RSEGS M p1 2 = Some [Z_to_bv 8 46; Z_to_bv 8 0];
  dt_t8 : exists t8, rdn RSEGS M (Z_to_bv 64 (bv_unsigned p1 + 1)) 8 = Some t8;
  dt_cells : drv_cells_ok M
}.

Section DirTail.
  Context {AMB : Amb} {RRND : RunRandom}.
  Variable sp0 : word.
  Variable a0s : list byte.
  Variable envv : list (list byte).
  Variable tid : word.
  Variable rdraw : EntryDraw.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Hypothesis Hva : valid_argv [a0s; dot_path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  (* LPS 75d69e00: [U1Start.main_entry] takes the run's whole ProcInput and the mmap
     base in place of (argv, envp, uid, hwcap).  [fs0]/[stdin0]/[mbase] are IMPLICIT, as
     in U1MainEntry.v's own migrated Sections, so the discharged [dir_tail] keeps its
     explicit argument list and infers them from [ME]. *)
  Context {fs0 : Fs.Fs} {stdin0 : InputStream} {mbase : word}.
  Local Notation INP := (mkProcInputC [a0s; dot_path] envv fs0 stdin0) (only parsing).
  Hypothesis ME : main_entry sp0 rdraw INP mbase tid regs0 mem0.

  Theorem dir_tail : forall (R : bvmap 5 word) (M : word -> option byte) (model : Model),
    m_halted model = None -> m_vm_lazy model = [] ->
    fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
    m_channel_reader model = true ->
    dir_tail_pre sp0 (p1 a0s dot_path envv rdraw) (bv_unsigned tid) mem0 R M ->
    srealizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x65a68) M (seg_rom RSEGS)) model)
               (t_die (msg_read_error dot_path) (m_fs model)).
Proof.
    intros R M model Hh Hlazy Hfd2 Hrd0 PRE.
    destruct PRE as [Rsp Rgp Rtp Rs2 Mstack Mimg Mtid Htidr Mself Mcanary Mpagesz Mnlocks
                     Hstr [t8 Ht8] Mcells].
    destruct (main_strN sp0 [a0s; dot_path] envv tid rdraw regs0 mem0 Hva Hve Hvsp ME 1
                ltac:(cbn; lia)) as (_ & Slo & Shi & _ & _).
    eapply (ref_read_error_dot sp0 [] model Hvsp Hh Hlazy Hfd2 Hrd0 (p1 a0s dot_path envv rdraw));
      try eassumption.
    all: unfold p1 in *; lia.
Qed.
End DirTail.

End FXALL1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
