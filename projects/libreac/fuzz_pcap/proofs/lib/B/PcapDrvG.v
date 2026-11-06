(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the asan-ubsan twin of a Theorem Labs lane's lib/A/PcapDrvG.v (a working branch
   9700d736a50; commit 5bede1a6d6b; porter ruling 3), every hunk mirrored: the bridge from the program
   contract's journal (lib/A/Prog/PcapEntry.v tfib_lib_post_x, lib/A/W_journalG.v ajournal_gx at the asan-ubsan
   harness globals G_HARNESS_U = [(0x5d3e40, 8); (0x5d3e60, 8)], lib/B/Prog/PcapEntry.v) to what the driver reads
   off cgif's journal (donor lib/YD1r.v, YCbq.ajournal), and pcap's ONE side condition: every byte the driver
   reads or keeps across the program call lies outside G_HARNESS_U.

   The bridge is lib/A/W_journalG.v's ajournal_gx_inner (fuzz_reply's, copied by path into fuzz_pcap by a Theorem Labs lane)
   at XO = 0, OUT = []: the callee's journal holds from a start memory memS that agrees with the caller's memory on
   every byte outside G. lib/A/PcapDrvG.v Requires lib/A/W_journal.v, which adds only the asan program-walk runner (over
   lib/A/Prog/PcapPa / PcapPaLib, whose asan-ubsan twins are lib/B's) and Exports W_journalG; this twin Requires
   W_journalG, which holds every name it uses (inG, ajournal_gx, ajournal_gx_inner).

   The side condition is stated over the hull [DRV_G_LO, DRV_G_HI) = [0x5d3e40, 0x5d3e80) of the two globals and
   their ASan redzones (Reusable/YD1y.v, MEASURED on the asan-ubsan unstripped twin
   fuzz_pcap.asan-ubsan sha256 c969d83cdd59: .symtab g_file_len 0x5d3e40 size 0x20, g_file 0x5d3e60 size 0x20;
   lib/A/PcapDrvG.v's asan hull is [0x5d3f40, 0x5d3f80)): G_HARNESS_U lies in it (inG_harness_hull), and the driver's kept
   bytes avoid it (drv_keep_not_G): its writable windows DRVW (the split DRV_IVS, YD1y.v), stdout's FILE and buffer
   (STDOUT_MUT, Reusable/YD1w.v: __stdout_FILE [0x9ddc0, 0x9dea8), buf [0x5f4e98, 0x5f52a8)), the read-only image
   (in_ro_tfa, Reusable/YCeg.v: the read-only segments and 0x99198 .. 0x9a3f0 = PCAP_RLO .. PCAP_RHI of
   lib/B/Prog/PcapRelro.v), FINV's cells (finv_img, Reusable/YD1u.v) and the stack. The driver's kept image
   REGIONS are checked per call by YD1y.v's region_avoids_G (YD2f.v's L_mem_avoids_G). rule 24: no function proved
   anew. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK15 YK18 YK00 YP09 YK04 YA0i YA0n YG00 YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI16 YCbq YM05.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PcapImgEnd YImgTop.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceMeta.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Stdio Require Import PSourceK.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapEntry.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapRelro PcapEntry.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YB1v YCeg YD1y YD1u YD2f YD1w.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* G_HARNESS_U lies in the hull of the two globals and their redzones. *)
Lemma inG_harness_hull : forall a, inG G_HARNESS_U a -> DRV_G_LO <= a < DRV_G_HI.
Proof.
intros a Ha. unfold inG, G_HARNESS_U in Ha. unfold DRV_G_LO, DRV_G_HI.
repeat (apply Exists_cons in Ha; destruct Ha as [Ha|Ha]; [unfold in_zr in Ha; cbn [fst snd] in Ha; lia|]).
inversion Ha.
Qed.

(* The set of bytes the driver reads or keeps across the program call. *)
Definition drv_keep_set (a : Z) : Prop :=
DRVW a = true \/ STDOUT_MUT a \/ in_ro_tfa a \/ finv_img a \/ CEIL_MIN <= a.
Lemma FINV_IVS_not_G : ivs_avoid DRV_G_LO DRV_G_HI = true.
Proof. vm_compute. reflexivity. Qed.
(* pcap's ONE side condition (porter ruling 3). *)
Lemma drv_keep_not_G : forall a, drv_keep_set a -> ~ (DRV_G_LO <= a < DRV_G_HI).
Proof.
intros a [Ha|[Ha|[Ha|[Ha|Ha]]]] Hg.
- exact (DRVW_not_G a Ha Hg).
- unfold STDOUT_MUT, STDOUT_LO, STDOUT_HI, SOBUF_LO, SOBUF_HI in Ha. unfold DRV_G_LO, DRV_G_HI in Hg. lia.
- destruct Ha as [(sg & Hs & Hws & Hrg) | Hr]; unfold DRV_G_LO, DRV_G_HI in Hg.
+ cbn in Hs. destruct Hs as [<-|[<-|[<-|[<-|[]]]]]; cbn in Hws, Hrg; try discriminate Hws; lia.
+ unfold PCAP_RLO, PCAP_RHI in Hr. lia.
- exact (ivs_avoid_sound DRV_G_LO DRV_G_HI a FINV_IVS_not_G Hg Ha).
- unfold DRV_G_LO, DRV_G_HI in *. lia.
Qed.
Corollary drv_keep_not_inG : forall a, drv_keep_set a -> ~ inG G_HARNESS_U a.
Proof. intros a Ha HG. exact (drv_keep_not_G a Ha (inG_harness_hull a HG)). Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
(* The bridge: the contract's journal (XO = 0, OUT = []) is the donor's journal from a start memory memS that agrees
   with the caller's memory outside the hull. *)
Lemma drv_journal_of_gx : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
ajournal_gx tfibsegs B G_HARNESS_U 0 [] STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
exists memS, YCbq.ajournal tfibsegs B STK sp0 FP ly S W memS md own ly' S' W' mem' md' k /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (DRV_G_LO <= a < DRV_G_HI) -> aview tfibsegs (w_H W) memS a = aview tfibsegs (w_H W) mem a).
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HJ.
apply ajournal_gx_inner in HJ as (memS & HJ & Hag). rewrite !Z.add_0_r in HJ.
exists memS. split; [exact HJ|].
intros a Ha Hn. apply Hag. rewrite u64_lit by exact Ha. intros HG. exact (Hn (inG_harness_hull a HG)).
Qed.
End b.
