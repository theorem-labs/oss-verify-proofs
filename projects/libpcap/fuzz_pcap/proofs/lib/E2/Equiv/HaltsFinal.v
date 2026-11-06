(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes Decode Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require HeapFull Pcap Prog. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.HeapFull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require UNodes__Equiv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require UPcapA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require UPcapB__Equiv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require HaltsAdq ExitBase ExitHeap ExitProg. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UNodes__Equiv.SimMain OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UNodes__Equiv.EquivPlan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UPcapA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UPcapB__Equiv.EquivFinal OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.HaltsAdq OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.ExitBase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.ExitHeap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.ExitProg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2 Require Import TopLevel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma ptree_exits_in : forall segs tb stk sec inp en mo,
  exits_in nstep nexit (ptree segs tb stk sec inp en) mo (fun c => In c [Z_to_bv 64 0; Z_to_bv 64 2]).
Proof.
  intros segs tb stk sec inp en mo. unfold ptree.
  exact (prog_exits_in (full_ops (CE := ceil_of_sp (en_sp en)))
           (full_ops_noexit (CE := ceil_of_sp (en_sp en))) fo_nop fo_nop_enter fo_nop_ret (stk en) (tb en)
           (fheap_init (sec en) (reservedZ segs)) (in_argv inp) mo).
Qed.

Section HaltsFinal.
Variables (segs : list Segment) (pc : N) (ph : PhdrInfo).
Variables (tb : ExecEntry -> Z) (stk : ExecEntry -> stack_site -> Z) (sec : ExecEntry -> Z).
Hypothesis SEC : forall en, 0 <= sec en < 2^64.
Variable lim : Z.
Hypothesis IO : image_ok segs lim.
Hypothesis TLS : forall en inp, valid_entry (mkImage segs pc ph) en inp -> OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.tls_in_image segs (tb en).
Hypothesis STK : forall en, stk_ok (stk en).
Hypothesis IMPL : exists Q, forall en inp, valid_entry (mkImage segs pc ph) en inp -> valid_input inp ->
  impl segs (at_node segs) (npeek segs) (ptree segs tb stk sec inp en) Q (ms0 segs pc ph en inp).

Theorem halts_final :
  halts_allowed_T_scfg_budgets forced_only_cfg lim [Z_to_bv 64 0; Z_to_bv 64 2] (mkImage segs pc ph).
Proof using SEC IO TLS STK IMPL.
  destruct (tree_ok_S_final segs pc ph tb stk sec SEC lim IO TLS STK IMPL) as [Q HT].
  apply (halts_of_tree segs pc ph lim [Z_to_bv 64 0; Z_to_bv 64 2] (treeS segs tb stk sec) Q HT).
  intros en inp _ _. apply ptree_exits_in.
Qed.
End HaltsFinal.
