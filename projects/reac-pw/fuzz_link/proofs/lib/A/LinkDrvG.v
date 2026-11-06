(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK15 YK18 YK00 YP09 YK04 YA0i YA0n YG00 YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YI16 YCbq YM05.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import PcapImgEnd YImgTop.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro LinkEntry LinkEntryA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v ACeg AD1y AD1u AD2f AD1w.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* Image A's G_HARNESS (LinkEntryA.v) holds six objects inside the driver's hull [DRV_G_LO, DRV_G_HI) of AD1y.v
   (g_nl, g_names, msg_build.long_alias, g_sink, g_said, g_say) and one outside it, ofl_head [OFL_LO, OFL_HI)
   (AD2f.v), which the driver's loop state clips out of its kept image regions. *)
Definition in_drv_g (a : Z) : Prop := (DRV_G_LO <= a < DRV_G_HI) \/ (OFL_LO <= a < OFL_HI).
Lemma G_HARNESS_cover : forallb (fun g => ((DRV_G_LO <=? fst g) && (fst g + snd g <=? DRV_G_HI)) ||
  ((OFL_LO <=? fst g) && (fst g + snd g <=? OFL_HI)))%bool G_HARNESS = true.
Proof. vm_compute. reflexivity. Qed.
Lemma inG_harness_hull : forall a, inG G_HARNESS a -> in_drv_g a.
Proof.
intros a Ha. unfold inG in Ha. apply Exists_exists in Ha as (g & Hg & Hz). unfold in_zr in Hz.
pose proof (proj1 (forallb_forall _ _) G_HARNESS_cover g Hg) as X. unfold in_drv_g.
apply orb_prop in X as [X|X]; apply andb_prop in X as [X1 X2]; apply Z.leb_le in X1; apply Z.leb_le in X2; [left|right]; lia.
Qed.

(* The bytes the driver reads or keeps across the program call. *)
Definition drv_keep_set (a : Z) : Prop :=
DRVW a = true \/ STDOUT_MUT a \/ in_ro_tfa a \/ CEIL_MIN <= a.
Lemma drv_keep_not_G : forall a, drv_keep_set a -> ~ in_drv_g a.
Proof.
intros a [Ha|[Ha|[Ha|Ha]]] [Hg|Hg].
- exact (DRVW_not_G a Ha Hg).
- pose proof (DRVW_cases a Ha). unfold OFL_LO, OFL_HI in Hg. lia.
- unfold STDOUT_MUT, STDOUT_LO, STDOUT_HI, SOBUF_LO, SOBUF_HI in Ha. unfold DRV_G_LO, DRV_G_HI in Hg. lia.
- unfold STDOUT_MUT, STDOUT_LO, STDOUT_HI, SOBUF_LO, SOBUF_HI in Ha. unfold OFL_LO, OFL_HI in Hg. lia.
- destruct Ha as [(sg & Hs & Hws & Hrg) | Hr]; unfold DRV_G_LO, DRV_G_HI in Hg.
+ cbn in Hs. destruct Hs as [<-|[<-|[<-|[<-|[]]]]]; cbn in Hws, Hrg; try discriminate Hws; lia.
+ unfold PCAP_RLO, PCAP_RHI in Hr. lia.
- destruct Ha as [(sg & Hs & Hws & Hrg) | Hr]; unfold OFL_LO, OFL_HI in Hg.
+ cbn in Hs. destruct Hs as [<-|[<-|[<-|[<-|[]]]]]; cbn in Hws, Hrg; try discriminate Hws; lia.
+ unfold PCAP_RLO, PCAP_RHI in Hr. lia.
- unfold DRV_G_LO, DRV_G_HI in *. lia.
- unfold OFL_LO, OFL_HI in *. lia.
Qed.
Corollary drv_keep_not_inG : forall a, drv_keep_set a -> ~ inG G_HARNESS a.
Proof. intros a Ha HG. exact (drv_keep_not_G a Ha (inG_harness_hull a HG)). Qed.

(* An image region the loop state keeps across the program call avoids ofl_head as AD1y.v's region_avoids_G
   avoids the hull. *)
Definition region_avoids_ofl (r : YP09.region) : bool :=
match r_base r with None => ext_avoids (r_lo r) (r_hi r) (OFL_LO, OFL_HI - OFL_LO) | Some _ => true end.
Lemma region_avoids_ofl_sound : forall r a, region_avoids_ofl r = true -> r_base r = None -> r_lo r <= a < r_hi r ->
~ (OFL_LO <= a < OFL_HI).
Proof.
intros r a H Hb Ha. unfold region_avoids_ofl in H. rewrite Hb in H. unfold ext_avoids in H. cbn [fst snd] in H.
apply orb_prop in H as [H|H]; apply Z.leb_le in H; lia.
Qed.
Lemma region_avoids_drv_g : forall r a, region_avoids_G r = true -> region_avoids_ofl r = true -> r_base r = None ->
r_lo r <= a < r_hi r -> ~ in_drv_g a.
Proof.
intros r a HG HO Hb Ha [X|X]; [exact (region_avoids_G_sound r a HG Hb Ha X) | exact (region_avoids_ofl_sound r a HO Hb Ha X)].
Qed.
Lemma L_mem_avoids_ofl : forallb region_avoids_ofl (tl L_mem) = true.
Proof. vm_compute. reflexivity. Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
(* The bridge: the contract's journal (XO = 0, OUT = []) is the frame's journal from a start memory memS that agrees
   with the caller's memory outside G_HARNESS. *)
Lemma drv_journal_of_gx : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
ajournal_gx tfibsegs B G_HARNESS 0 [] STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
exists memS, YCbq.ajournal tfibsegs B STK sp0 FP ly S W memS md own ly' S' W' mem' md' k /\
(forall a, 0 <= a < 2 ^ 64 -> ~ in_drv_g a -> aview tfibsegs (w_H W) memS a = aview tfibsegs (w_H W) mem a).
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HJ.
apply ajournal_gx_inner in HJ as (memS & HJ & Hag). rewrite !Z.add_0_r in HJ.
exists memS. split; [exact HJ|].
intros a Ha Hn. apply Hag. rewrite u64_lit by exact Ha. intros HG. exact (Hn (inG_harness_hull a HG)).
Qed.
End b.
