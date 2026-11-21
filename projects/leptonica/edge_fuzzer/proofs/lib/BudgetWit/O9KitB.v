(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from O9/O9Kit.v: the startup walk (O9Startup.ref_startup_sec, ref_startup) and the stdio call (O9LibStdioCall.stdio_call_sound_fr, stdio_call_sound) restated over the budget carrier rzb. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch input ProcInput, the m_channel_reader premise, the vDSO). *)
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.O9 Require O9Kit.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CliDriver Require Amb.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require RefNodesMF.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Musl Require StartupBase.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Musl Require StartupDefs.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Musl Require Startup.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require SpecConsts.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require SymExec.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CliDriver Require SymExec2.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CliDriver Require SymExec2Sound.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CliDriver Require SymRun.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CliDriver Require SymDrive.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CliDriver Require SymDriveX.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CliDriver Require LibKnowFrame.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Musl Require LibStdioCall.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.BudgetWit Require Rzb StartupB LibStdioCallB.

Module O9StartupB.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Monad.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Vdso.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.Riscv.Decode.
Import LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.leptonica.edge_fuzzer.images.Plain.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CliDriver.Amb.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.PureModel.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.RefNodesMF.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.StartupTac.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.ArgvEnv.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.RefLayout.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Reloc.Reloc.
Import O9Kit.O9StartupDefs.
Import O9Kit.O9Reloc.
Import O9Kit.O9RelocCode.
Import O9Kit.O9RelocSites.
Import O9Kit.O9RelocImg.
Import O9Kit.O9RelocMusl.
Import O9Kit.O9RelocStart.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)











Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := Plain.M.loaded_segments.
Abbreviation RPH := Plain.M.phdrs.
(* [comment removed for export] *)
Local Notation rsegs := Plain.M.loaded_segments (only parsing).
Local Notation rpc := Plain.M.init_pc (only parsing).
Local Notation rph := Plain.M.phdrs (only parsing).

(* [comment removed for export] *)

(* [comment removed for export] *)
Import O9Kit.O9Startup.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.BudgetWit.Rzb.

(* [comment removed for export] *)
Theorem ref_startup_b : forall sp brk mbase draw lim inp K (Hrd : in_channel_reader inp = true),
  valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase draw) inp ->
  (forall tid regs mem,
     (0 < bv_unsigned tid < 2^22)%Z ->
     @main_entry (amb_of inp draw mbase Hrd) sp (in_argv inp) (in_envp inp) tid regs mem ->
     rzb rsegs (mkCfg (mkst (fx:=fx0) regs (0x5c8b0 : word) mem (seg_rom rsegs))
                           (with_tid tid (with_vdso (vdso_run_init (ed_vdso draw))
                                            (init_model (segments_reserved rsegs) brk mbase sp lim inp)))) K) ->
  rzb rsegs (init_config rsegs rpc rph sp brk mbase draw lim inp) K.
Proof.
  intros sp brk mbase draw lim inp K Hrd Hsp Hva Hve Hvl Hlau HK.
  refine (@StartupB.ref_startup_sec_b o9_reloc o9_code o9_sites o9_img o9_data o9_rw o9_start
            sp inp mbase brk draw Hva Hve Hsp Hvl Hlau rpc _ lim K _).
  - apply bv_eq; reflexivity.
  - intros tid regs mem Htid ME.
    pose proof (HK tid regs mem Htid (main_entry_L _ _ _ _ _ _ _ _ Hrd Hvl Hlau ME)) as R.
    bvlit64_to_Z_in R. exact R.
Qed.

End O9StartupB.

Module O9LibStdioCallB.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Monad.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.Riscv.Decode.
Import LinuxProcessSemantics.Riscv.DecodeC.
Import LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.leptonica.edge_fuzzer.images.Plain.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.SeqExec.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Nodes.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.AgentLib.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.SpecConsts.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.SymExec.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CliDriver.SymExec2.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CliDriver.SymRun.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CliDriver.SymDrive.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CliDriver.SymDriveX.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CliDriver.LibKnowFrame.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Reloc.Reloc.
Import O9Kit.O9ExitBase.
Import O9Kit.O9StdioDefs.
Import O9Kit.O9Reloc.
Import O9Kit.O9RelocCode.
Import O9Kit.O9RelocSites.
Import O9Kit.O9RelocImg.
Import O9Kit.O9RelocMusl.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)










Import ListNotations.
Import SX2. Import SX2S.
Open Scope Z_scope.

#[local] Abbreviation RSEGS := Plain.M.loaded_segments.

Import O9Kit.O9LibStdioCall.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.BudgetWit.Rzb.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section VP17.
  Context {fx : FPState}.   (* [comment removed for export] *)
Theorem stdio_call_sound_fr_b :
  forall (vals : list word) (ebs : nat -> list byte) (sr : list expr) (kn : list kentry)
         (R : bvmap 5 word) (M : word -> option byte) (model : Model) (res : stdio_res)
         (pending extra : list byte) (K : TSet),
  let E := Env (vals_ev vals) ebs in
  regs_ok E sr R -> know_ok RSEGS E M kn ->
  stdio_call (length vals) sr kn = Some res ->
  let wb := bv_unsigned (edenot E (sc_wb res)) in
  let wp := bv_unsigned (edenot E (sc_wp res)) in
  let s := edenot E (sc_s res) in
  let l := edenot E (sc_l res) in
  let su := bv_unsigned (edenot E (sc_sp res)) in
  (wb <= wp)%Z -> (wp <= 0x800000000000)%Z ->   (* [comment removed for export] *)
  (wp - wb = Z.of_nat (length pending))%Z ->
  (bv_unsigned l = Z.of_nat (length extra))%Z ->
  (Z.of_nat (length pending) + Z.of_nat (length extra) <= 2 ^ 30)%Z ->
  (Z.of_nat (length pending) + Z.of_nat (length extra) <= 2 ^ 30)%Z ->
  (wp <= su - 112 \/ su <= wb)%Z ->
  (bv_unsigned s + bv_unsigned l <= su - 112 \/ su <= bv_unsigned s)%Z ->
  (bv_unsigned s + bv_unsigned l <= 0x800000000000)%Z ->
  rdn RSEGS M (Z_to_bv 64 wb) (length pending) = Some pending ->
  rdn RSEGS M s (length extra) = Some extra ->
  fd_lookup (m_fds model) (Z_to_bv 64 (sc_fd res)) = Some (FdChannel (Z_to_bv 64 (sc_fd res))) ->
  m_channel_reader model = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  K [] ->
  (forall R' M',
     regs_ok (Env (vals_ev (vals ++ junk_vals R')) ebs) (sc_sr res) R' ->
     know_ok RSEGS (Env (vals_ev (vals ++ junk_vals R')) ebs) M' (sc_kn res) ->
     sw_post M (bv_unsigned (edenot E (sc_sp res))) (sc_f res) (edenot E (sc_bufp res)) (edenot E (sc_bufsz res)) M' ->
     rzb RSEGS (mkCfg (mkst R' (Z_to_bv 64 (sc_ret res)) M' (seg_rom RSEGS)) model) K) ->
  rzb RSEGS (mkCfg (mkst R (Z_to_bv 64 0xdba30) M (seg_rom RSEGS)) model)
           (t_emit (map (WriteEv (Z_to_bv 64 (sc_fd res))) (pending ++ extra)) K).
Proof.
  intros vals ebs sr kn R M model res pending extra K E HR HK Hc wb wp s l su
         H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Hrd H13 H14 H15 HCONT.
  rl_tail (@LibStdioCallB.stdio_call_sound_fr_b _ o9_reloc o9_code o9_sites o9_data o9_rw
             vals ebs sr kn R M model res pending extra K HR HK Hc
             H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Hrd H13 H14 H15
             (fun R' M' A B P => HCONT R' M' A B (sw_post_L _ _ _ _ _ _ P))).
Qed.

(* [comment removed for export] *)
Theorem stdio_call_sound_b :
  forall (vals : list word) (ebs : nat -> list byte) (sr : list expr) (kn : list kentry)
         (R : bvmap 5 word) (M : word -> option byte) (model : Model) (res : stdio_res)
         (pending extra : list byte) (K : TSet),
  let E := Env (vals_ev vals) ebs in
  regs_ok E sr R -> know_ok RSEGS E M kn ->
  stdio_call (length vals) sr kn = Some res ->
  let wb := bv_unsigned (edenot E (sc_wb res)) in
  let wp := bv_unsigned (edenot E (sc_wp res)) in
  let s := edenot E (sc_s res) in
  let l := edenot E (sc_l res) in
  let su := bv_unsigned (edenot E (sc_sp res)) in
  (wb <= wp)%Z -> (wp <= 0x800000000000)%Z ->
  (wp - wb = Z.of_nat (length pending))%Z ->
  (bv_unsigned l = Z.of_nat (length extra))%Z ->
  (Z.of_nat (length pending) + Z.of_nat (length extra) <= 2 ^ 30)%Z ->
  (Z.of_nat (length pending) + Z.of_nat (length extra) <= 2 ^ 30)%Z ->
  (wp <= su - 112 \/ su <= wb)%Z ->
  (bv_unsigned s + bv_unsigned l <= su - 112 \/ su <= bv_unsigned s)%Z ->
  (bv_unsigned s + bv_unsigned l <= 0x800000000000)%Z ->
  rdn RSEGS M (Z_to_bv 64 wb) (length pending) = Some pending ->
  rdn RSEGS M s (length extra) = Some extra ->
  fd_lookup (m_fds model) (Z_to_bv 64 (sc_fd res)) = Some (FdChannel (Z_to_bv 64 (sc_fd res))) ->
  m_channel_reader model = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  K [] ->
  (forall R' M',
     regs_ok (Env (vals_ev (vals ++ junk_vals R')) ebs) (sc_sr res) R' ->
     know_ok RSEGS (Env (vals_ev (vals ++ junk_vals R')) ebs) M' (sc_kn res) ->
     rzb RSEGS (mkCfg (mkst R' (Z_to_bv 64 (sc_ret res)) M' (seg_rom RSEGS)) model) K) ->
  rzb RSEGS (mkCfg (mkst R (Z_to_bv 64 0xdba30) M (seg_rom RSEGS)) model)
           (t_emit (map (WriteEv (Z_to_bv 64 (sc_fd res))) (pending ++ extra)) K).
Proof.
  intros vals ebs sr kn R M model res pending extra K E HR HK Hc wb wp s l su; intros.
  eapply stdio_call_sound_fr_b; try eassumption. intros R' M' HR' HK' _. auto.
Qed.
End VP17.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End O9LibStdioCallB.
