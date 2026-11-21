(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from QBxa.v: rz_ret_only_copyins_silent and rz_cases over BudgetWit.QRjHB.realizes; each takes the budget check of its node. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (RomBase.sys_rob at the system-call nodes: rz_ret_only_copyins_silent and rz_cases take the robust-call check of their node). *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsRG Qnhz Qrxj QSjk QRjH QEVk QiVh QwNp Qpox QsV0 Qn1e QBxa.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Cfg Require RomBase.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.BudgetWit Require QRjHB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import QwNp Qpox QsV0 QsRG Qn1e QRjH.
Import QBxa.Mq4.
Import QRjHB.

Import ListNotations.
Open Scope bv_scope.

Section WithSegs.
Variable segs : list Segment.

#[using="Type"] Lemma rz_ret_only_copyins_silent : forall ms model x8 reads r m' T,
m_halted model = None ->
ms_svc_pending ms = Some x8 ->
~ In (bv_unsigned x8) alloc_mark_sysnos ->
(forall o, syscall_spec (sys_input segs ms x8) model o
<-> o = Ok (with_copyins reads (mkEffect r [] [])) m' []) ->
m_halted m' = None ->
m_vm_lazy m' = [] ->
RomBase.sys_rob segs (mkCfg ms model) ->
realizes segs (mkCfg (advance_past_svc (set_gpr0 ms r)) m') T ->
realizes segs (mkCfg ms model) T.
Proof.
intros ms model x8 reads r m' T Hh Hsvc Hna Hchk Hh' Hlazy Hrob Hc.
eapply rz_silent1; [eapply node_ret_only_copyins; eassumption | exact Hrob
| exact (budget_ok_nalloc ms model x8 Hsvc Hna) | exact Hc].
Qed.

#[using="Type"] Lemma rz_cases : forall c (I : Type) (nx : I -> config) (T : I -> TSet) (i0 : I),
node_ok segs c I (fun _ => []) nx ->
RomBase.sys_rob segs c ->
budget_ok c ->
(forall i, realizes segs (nx i) (T i)) ->
realizes segs c (t_alt T).
Proof.
intros c I nx T i0 Hnode Hrob Hb Hc.
apply (rz_conseq segs c (t_alt (fun i => t_emit [] (T i)))).
- apply (rz_node segs c I (fun _ => []) nx T i0 Hnode Hrob Hb Hc).
- intros tr. split.
+ intros [i Hi]. exists i.
exact (proj1 (t_emit_nil_eq (T i) (realizes_nonempty segs _ _ (Hc i)) tr) Hi).
+ intros [i Hi]. exists i.
exact (proj2 (t_emit_nil_eq (T i) (realizes_nonempty segs _ _ (Hc i)) tr) Hi).
Qed.

End WithSegs.
End Mq4.
