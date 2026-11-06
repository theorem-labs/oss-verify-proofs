(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from proofs/libreac/fuzz_pcap/lib/B/PcapDrvG.v (origin/ossv/recipes
   198234fa4d3) for libdiginet/fuzz_transport's ASan+UBSan image, reduced to what lib/B/YD1r.v uses: the bridge from
   the program contract's journal (lib/B/YCfn.v tfib_lib_post_x, lib/A/W_journalG.v ajournal_gx at XO = 0, OUT = [],
   at the harness globals G_HARNESS_B of lib/B/TransportGB.v) to the journal the driver reads (YCbq.ajournal), and the
   side condition that the bytes the driver reads or keeps across the program call lie outside the hull
   [G_HARNESS_B_LO, G_HARNESS_B_HI) of those globals.

   The bridge (drv_journal_of_gx) is W_journalG.v's ajournal_gx_inner at XO = 0, OUT = []: the callee's journal holds
   from a start memory memS that agrees with the caller's memory on every byte outside G_HARNESS_B, so on every byte
   outside the hull (inG_harness_hull, from TransportGB.v's G_HARNESS_B_in_hull).

   The side condition (drv_keep_not_G) covers stdout's FILE and buffer (STDOUT_MUT, lib/B/YD1w.v), the read-only
   image (in_ro_tfa, lib/B/YCeg.v), FINV's cells (finv_img, lib/B/YD1u.v) and the stack (CEIL_MIN and above). pcap's
   drv_keep_set also has the driver windows DRVW, which avoid the hull because pcap's DRV_IVS is split around it (pcap
   Reusable/YD1y.v DRV_IVS_not_G / DRVW_not_G); this unit's DRV_IVS is in the generated start-up file lib/B/YD1y.v and
   comes split with the start-up layer's hull cut, and YD1r.v reads no DRVW byte across the call, so that disjunct is
   not stated here. The image regions the driver keeps across the call are checked by lib/B/YD2f.v region_avoids_G
   (L_mem_avoids_G).
   rule 24: proves no function (invariant lemmas over the program contract's G form). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.libdiginet.fuzz_transport.images Require Import AsanUbsan.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK15 YK18 YK00 YP09 YK04 YA0i YA0n YG00 YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YI16 YCbq YM05.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v YCeg YD1y YD1u YD2f YD1w.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* G_HARNESS_B lies in its hull. *)
Lemma inG_harness_hull : forall a, inG G_HARNESS_B a -> G_HARNESS_B_LO <= a < G_HARNESS_B_HI.
Proof.
intros a Ha. unfold inG in Ha. apply Exists_exists in Ha as (r & Hr & Hz).
pose proof (G_HARNESS_B_in_hull r Hr) as [H1 H2]. unfold in_zr in Hz. lia.
Qed.

(* The bytes the driver reads or keeps across the program call. *)
Definition drv_keep_set (a : Z) : Prop :=
STDOUT_MUT a \/ in_ro_tfa a \/ finv_img a \/ CEIL_MIN <= a.
Lemma FINV_IVS_not_G : ivs_avoid G_HARNESS_B_LO G_HARNESS_B_HI = true.
Proof. vm_compute. reflexivity. Qed.
Lemma drv_keep_not_G : forall a, drv_keep_set a -> ~ (G_HARNESS_B_LO <= a < G_HARNESS_B_HI).
Proof.
intros a [Ha|[Ha|[Ha|Ha]]] Hg.
- unfold STDOUT_MUT, STDOUT_LO, STDOUT_HI, SOBUF_LO, SOBUF_HI in Ha. unfold G_HARNESS_B_LO, G_HARNESS_B_HI in Hg. lia.
- destruct Ha as [(sg & Hs & Hws & Hrg) | Hr]; unfold G_HARNESS_B_LO, G_HARNESS_B_HI in Hg.
+ cbn in Hs. destruct Hs as [<-|[<-|[<-|[<-|[]]]]]; cbn in Hws, Hrg; try discriminate Hws; lia.
+ lia.
- exact (ivs_avoid_sound G_HARNESS_B_LO G_HARNESS_B_HI a FINV_IVS_not_G Hg Ha).
- unfold G_HARNESS_B_LO, G_HARNESS_B_HI in *. lia.
Qed.
Corollary drv_keep_not_inG : forall a, drv_keep_set a -> ~ inG G_HARNESS_B a.
Proof. intros a Ha HG. exact (drv_keep_not_G a Ha (inG_harness_hull a HG)). Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
(* The bridge: the contract's journal (XO = 0, OUT = []) is the donor's journal from a start memory memS that agrees
   with the caller's memory outside the hull. *)
Lemma drv_journal_of_gx : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
ajournal_gx tfibsegs B G_HARNESS_B 0 [] STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
exists memS, YCbq.ajournal tfibsegs B STK sp0 FP ly S W memS md own ly' S' W' mem' md' k /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (G_HARNESS_B_LO <= a < G_HARNESS_B_HI) -> aview tfibsegs (w_H W) memS a = aview tfibsegs (w_H W) mem a).
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HJ.
apply ajournal_gx_inner in HJ as (memS & HJ & Hag). rewrite !Z.add_0_r in HJ.
exists memS. split; [exact HJ|].
intros a Ha Hn. apply Hag. rewrite u64_lit by exact Ha. intros HG. exact (Hn (inG_harness_hull a HG)).
Qed.
End b.
