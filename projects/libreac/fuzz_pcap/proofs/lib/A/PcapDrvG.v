(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: new file for libreac/fuzz_pcap's ASan driver (porter ruling 3): the bridge from
   the program contract's journal (lib/A/Prog/PcapEntry.v:69 tfib_lib_post_x, W_journal.v:213 ajournal_gx at the
   harness globals G_HARNESS = [(0x5d3f40, 8); (0x5d3f60, 8)], PcapEntry.v:36) to what the driver reads off cgif's
   journal (donor lib/A/AD1r.v:657, YCbq.ajournal), and pcap's ONE side condition: every byte the driver reads or
   keeps across the program call lies outside G_HARNESS.

   The bridge is W_journal.v:360 ajournal_gx_inner (fuzz_reply's, copied by path into fuzz_pcap by a Theorem Labs lane) at
   XO = 0, OUT = []: the callee's journal holds from a start memory memS that agrees with the caller's memory on
   every byte outside G. At ossv/recipes 25e3d17bdb50 (2026-10-29), a Theorem Labs lane's ACfn_cf bridge had not landed; this is pcap's own, in the
   same form, and is replaced by a citation when it lands.

   The side condition is stated over the hull [DRV_G_LO, DRV_G_HI) = [0x5d3f40, 0x5d3f80) of the two globals and
   their ASan redzones (lib/A/AD1y.v, MEASURED): G_HARNESS lies in it (inG_harness_hull), and the driver's kept
   bytes avoid it (drv_keep_not_G): its writable windows DRVW (the split DRV_IVS, AD1y.v), stdout's FILE and buffer
   (STDOUT_MUT, lib/A/AD1w.v; donor AD1r.v:664), the read-only image (in_ro_tfa, lib/A/ACeg.v; donor AD1r.v:666),
   FINV's cells (finv_img, lib/A/AD1u.v) and the stack (donor AD1r.v:249, :323). The driver's kept image REGIONS
   (donor AD1r.v:277) are checked per call by AD1y.v's region_avoids_G. rule 24: no function proved anew. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK15 YK18 YK00 YP09 YK04 YA0i YA0n YG00 YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI16 YCbq YM05.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PcapImgEnd YImgTop.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceMeta PSourceK.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapRelro PcapEntry PcapEntryA.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import W_journal.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import AB1v ACeg AD1y AD1u AD2f AD1w.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* G_HARNESS lies in the hull of the two globals and their redzones. *)
Lemma inG_harness_hull : forall a, inG G_HARNESS a -> DRV_G_LO <= a < DRV_G_HI.
Proof.
intros a Ha. unfold inG, G_HARNESS in Ha. unfold DRV_G_LO, DRV_G_HI.
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
Corollary drv_keep_not_inG : forall a, drv_keep_set a -> ~ inG G_HARNESS a.
Proof. intros a Ha HG. exact (drv_keep_not_G a Ha (inG_harness_hull a HG)). Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
(* The bridge: the contract's journal (XO = 0, OUT = []) is the donor's journal from a start memory memS that agrees
   with the caller's memory outside the hull. *)
Lemma drv_journal_of_gx : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
ajournal_gx tfibsegs B G_HARNESS 0 [] STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
exists memS, YCbq.ajournal tfibsegs B STK sp0 FP ly S W memS md own ly' S' W' mem' md' k /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (DRV_G_LO <= a < DRV_G_HI) -> aview tfibsegs (w_H W) memS a = aview tfibsegs (w_H W) mem a).
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HJ.
apply ajournal_gx_inner in HJ as (memS & HJ & Hag). rewrite !Z.add_0_r in HJ.
exists memS. split; [exact HJ|].
intros a Ha Hn. apply Hag. rewrite u64_lit by exact Ha. intros HG. exact (Hn (inG_harness_hull a HG)).
Qed.
End b.
