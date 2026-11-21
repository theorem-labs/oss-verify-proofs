(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from Q9ox.v: rz_sys over BudgetWit.QRjHB.realizes. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qpox QsV0 QsRG Qnhz Qrxj QSjk Qn1e QiVh QRjH QBxa Q9ox.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.BudgetWit Require QRjHB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import Qpox QsV0 QsRG.Mq0 Qnhz.Mq0 QsRG Qrxj QSjk Qn1e.Mq1 QiVh Qn1e QRjH QBxa.Mq4 QRjH.Mq3.
Import QBxa.Mq0.
Import Q9ox.Mq0.
Import QRjHB.
Import ListNotations.
Open Scope bv_scope.
Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

#[using="Type"] Lemma rz_sys : forall segs regs pc mem rom model w T,
m_halted model = None ->
m_vm_lazy model = [] ->
fetch_word segs pc = Some w -> is_ecall w = true ->
realizes segs (mkCfg (epend regs pc mem rom (getr regs 17)) model) T ->
realizes segs (mkCfg (mkst regs pc mem rom) model) T.
Proof.
intros segs regs pc mem rom model w T Hh Hlazy HF HE Hc.
eapply rz_step; [exact Hh | exact Hlazy | reflexivity | eapply step_ecall_epend; eassumption | exact Hc].
Qed.

End FPGEN1.
End Mq0.
