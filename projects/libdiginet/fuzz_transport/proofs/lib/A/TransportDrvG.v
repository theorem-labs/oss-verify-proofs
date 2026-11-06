(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* The G side of libdiginet/fuzz_transport's image-A driver: libreac/fuzz_pcap's lib/A/PcapDrvG.v (origin/ossv/recipes
   198234fa4d3) reduced to its G content. It holds the bridge from the program call's journal (A/AD1w.v lib_site_x:
   W_journalG.v's ajournal_gx at the harness globals' hull DRV_G of A/AD2f.v, XO = 0, OUT = []) to what the driver reads
   off its journal (YCbq.ajournal from a start memory memS that agrees with the caller's memory outside the hull), and
   the one side condition: every byte the driver reads or keeps across the call lies outside the hull
   [DRV_G_LO, DRV_G_HI) of the start-up layer's A/AD1y.v. The driver's write windows DRVW avoid the hull by that file's
   DRVW_not_G (its DRV_IVS is cut around the hull); the kept image regions by A/AD2f.v's L_mem_avoids_G.
   Where it differs from pcap's file: G is the hull itself (DRV_G), so pcap's inG_harness_hull (inG G_HARNESS -> hull)
   is inG_DRV_G_hull, and this file names no program file; the slot's own G (the harness globals) is lifted to the hull
   by A/TransportDriver.v. No function is proved here. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK15 YK18 YK00 YP09 YK04 YA0i YA0n YG00 YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YI16 YCbq YM05.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v ACeg AD1y AD1u AD2f AD1w.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* DRV_G is the hull, as a G list. *)
Lemma inG_DRV_G_hull : forall a, inG DRV_G a -> DRV_G_LO <= a < DRV_G_HI.
Proof.
intros a Ha. unfold inG, DRV_G in Ha.
repeat (apply Exists_cons in Ha; destruct Ha as [Ha|Ha]; [unfold in_zr in Ha; cbn [fst snd] in Ha; lia|]).
inversion Ha.
Qed.
Lemma inG_DRV_G_of_hull : forall a, DRV_G_LO <= a < DRV_G_HI -> inG DRV_G a.
Proof. intros a Ha. unfold inG, DRV_G. apply Exists_cons. left. unfold in_zr. cbn [fst snd]. lia. Qed.

(* The set of bytes the driver reads or keeps across the program call: its write windows (DRVW, A/AD1y.v), stdout's
   FILE and buffer (STDOUT_MUT, A/AD1w.v), the read-only image (in_ro_tfa, A/ACeg.v), FINV's cells (finv_img, A/AD1u.v)
   and the stack. *)
Definition drv_keep_set (a : Z) : Prop :=
DRVW a = true \/ STDOUT_MUT a \/ in_ro_tfa a \/ finv_img a \/ CEIL_MIN <= a.
Lemma FINV_IVS_not_G : ivs_avoid DRV_G_LO DRV_G_HI = true.
Proof. vm_compute. reflexivity. Qed.
(* The side condition. *)
Lemma drv_keep_not_G : forall a, drv_keep_set a -> ~ (DRV_G_LO <= a < DRV_G_HI).
Proof.
intros a [Ha|[Ha|[Ha|[Ha|Ha]]]] Hg.
- exact (DRVW_not_G a Ha Hg).
- unfold STDOUT_MUT, STDOUT_LO, STDOUT_HI, SOBUF_LO, SOBUF_HI in Ha. unfold DRV_G_LO, DRV_G_HI in Hg. lia.
- destruct Ha as [(sg & Hs & Hws & Hrg) | Hr]; unfold DRV_G_LO, DRV_G_HI in Hg.
+ cbn in Hs. destruct Hs as [<-|[<-|[<-|[<-|[]]]]]; cbn in Hws, Hrg; try discriminate Hws; lia.
+ lia.
- exact (ivs_avoid_sound DRV_G_LO DRV_G_HI a FINV_IVS_not_G Hg Ha).
- unfold DRV_G_LO, DRV_G_HI in *. lia.
Qed.
Corollary drv_keep_not_inG : forall a, drv_keep_set a -> ~ inG DRV_G a.
Proof. intros a Ha HG. exact (drv_keep_not_G a Ha (inG_DRV_G_hull a HG)). Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
(* The bridge: the call's journal at the hull (XO = 0, OUT = []) is the donor's journal from a start memory memS that
   agrees with the caller's memory outside the hull. *)
Lemma drv_journal_of_gx : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
ajournal_gx tfibsegs B DRV_G 0 [] STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
exists memS, YCbq.ajournal tfibsegs B STK sp0 FP ly S W memS md own ly' S' W' mem' md' k /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (DRV_G_LO <= a < DRV_G_HI) -> aview tfibsegs (w_H W) memS a = aview tfibsegs (w_H W) mem a).
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HJ.
apply ajournal_gx_inner in HJ as (memS & HJ & Hag). rewrite !Z.add_0_r in HJ.
exists memS. split; [exact HJ|].
intros a Ha Hn. apply Hag. rewrite u64_lit by exact Ha. intros HG. exact (Hn (inG_DRV_G_hull a HG)).
Qed.
End b.
