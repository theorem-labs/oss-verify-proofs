(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* The G side of libdiginet/fuzz_transport's image-A driver statement: libreac/fuzz_pcap's lib/A/PcapDriver.v
   (origin/ossv/recipes 198234fa4d3) reduced to its G content. PcapDriver.v states the driver obligation (cgif's AD1q.v
   drv_mainX_stmt, DRV_MAINX) with its LIBX at pcap's program contract at the harness globals G_HARNESS. This core keeps
   grant's A/AD1q.v for that statement, so this file holds only what the G change adds to it:
   - the slot states its contract A/ACfn.v tfib_lib_contract_x at its own program-global ranges G (W_journalG.v's
     ajournal_gx G 0 []), and the driver states its call site at the harness globals' hull DRV_G (A/AD2f.v, A/AD1w.v;
     its bounds DRV_G_LO / DRV_G_HI are the start-up layer's A/AD1y.v);
   - a G inside the hull (g_in_hull G) gives the contract at the hull (W_journalG.v's ajournal_gx_G_mono).
   A/AD1q.v takes G and g_in_hull G as Section hypotheses, so the core names no program file: the program side
   instantiates G with its harness globals and proves g_in_hull of them. No function is proved here. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YO09 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import ACfn AD1y AD2f TransportDrvG.
Import ListNotations.
Local Open Scope Z_scope.

(* The program-global ranges G lie in the harness globals' hull. *)
Definition g_in_hull (G : list (Z * Z)) : Prop := forall a, inG G a -> DRV_G_LO <= a < DRV_G_HI.
Lemma g_in_hull_DRV_G : forall G, g_in_hull G -> forall a, inG G a -> inG DRV_G a.
Proof. intros G HG a Ha. exact (inG_DRV_G_of_hull a (HG a Ha)). Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
(* The contract at G gives the contract at the hull: only the post's journal names G. *)
Lemma tfib_lib_contract_x_hull : forall G B MT XM_LIB XN_LIB RLO RHI, g_in_hull G ->
tfib_lib_contract_x G B MT XM_LIB XN_LIB RLO RHI -> tfib_lib_contract_x DRV_G B MT XM_LIB XN_LIB RLO RHI.
Proof.
intros G B MT XM_LIB XN_LIB RLO RHI HG HC ly S W regs mem md p n pl M K HAI HPRE CONT.
apply (HC ly S W regs mem md p n pl M K HAI HPRE).
intros l W' c' Hwle HAI' (ly' & S' & regs' & mem' & md' & k & Hc' & HPOST).
apply (CONT l W' c' Hwle HAI'). exists ly', S', regs', mem', md', k. split; [exact Hc'|].
unfold tfib_lib_post_x in HPOST |- *. destruct HPOST as (HJ & HPOST). split; [|exact HPOST].
eapply ajournal_gx_G_mono; [exact (g_in_hull_DRV_G G HG) | exact HJ].
Qed.
End a.
Lemma tfib_lib_contract_x_all_hull {rc : YM05.RunCeil} {LS : lib_shape} : forall G B MT XM_LIB XN_LIB RLO RHI, g_in_hull G ->
tfib_lib_contract_x_all G B MT XM_LIB XN_LIB RLO RHI -> tfib_lib_contract_x_all DRV_G B MT XM_LIB XN_LIB RLO RHI.
Proof.
intros G B MT XM_LIB XN_LIB RLO RHI HG HC fx.
exact (tfib_lib_contract_x_hull (fx := fx) G B MT XM_LIB XN_LIB RLO RHI HG (HC fx)).
Qed.
