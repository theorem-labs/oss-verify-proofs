(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from QCPB.v: rz_run (module Mq0, section Drive) over BudgetWit.QRjHB.realizes. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsRG Qnhz Qrxj QRjH Qpox QsV0 QO3A QBxa Q7m0 QSpR QuJV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCPB.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.BudgetWit Require QRjHB.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import QsRG.Mq0 Qnhz.Mq0 QsRG Qrxj QRjH.Mq3 Qpox QsV0 QRjH QO3A QBxa.Mq1 QBxa.Mq3.
Import Q7m0 QSpR.Mq4 QuJV.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
Import QCPB.Mq0 QRjHB.
Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

Section Drive.
Variable segs : list Segment.

#[using="Type"] Theorem rz_run : forall fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2
E M rom R model T,
sym_exec segs fuel true stops scr (SS pc sr [] kn nx) [] = (ss', scs, scr') ->
carry (s_log ss') kn [] = (kn', scs2, hs2) ->
regs_ok E sr R -> know_ok segs E M kn ->
scs_denot segs M E scs -> scs_denot segs M E scs2 ->
m_halted model = None ->
m_vm_lazy model = [] ->
(forall R' M', regs_ok E (s_regs ss') R' -> know_ok segs E M' kn' ->
M' = mem_denot E M (s_log ss') ->
realizes segs (mkCfg (mkst R' (Z_to_bv 64 (s_pc ss')) M' rom) model) T) ->
realizes segs (mkCfg (mkst R (Z_to_bv 64 pc) M rom) model) T.
Proof.
intros fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2 E M rom R model T
Hex Hc HR HK Hsc Hsc2 Hh Hlazy Hcont.
destruct (run_sound segs fuel stops scr pc sr kn nx ss' scs scr' E M rom R Hex HR HK Hsc)
as (R' & HR' & Hlf & Hms).
eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |].
apply (Hcont R' _ HR'); [|reflexivity].
eapply carry_after; eassumption.
Qed.
End Drive.
End FPGEN1.

End Mq0.
