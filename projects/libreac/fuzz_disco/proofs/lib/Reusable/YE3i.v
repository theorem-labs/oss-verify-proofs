(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: IMG_RO_HI and img_ro_chunks are generated from fuzz_disco's own asan-ubsan image and its generated YF0m (ae3i.py). *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP01.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI04 YK04 YB1v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition IMG_RO_LO : Z := 0x10000.
Definition IMG_RO_HI : Z := 0x2ff24.
Definition img_ro_chunks : list YP09.chunk :=
[ YP09.mkChunk 0x10000 (CImg (0x102e8 - 0x10000));
YP09.mkChunk 0x102f0 (CImg (0x10308 - 0x102f0));
YP09.mkChunk 0x10310 (CImg (0x10338 - 0x10310));
YP09.mkChunk 0x10340 (CImg (0x10350 - 0x10340));
YP09.mkChunk 0x10358 (CImg (0x103a0 - 0x10358));
YP09.mkChunk 0x103a8 (CImg (0x103b0 - 0x103a8));
YP09.mkChunk 0x103c0 (CImg (0x103d0 - 0x103c0));
YP09.mkChunk 0x103d8 (CImg (0x10448 - 0x103d8));
YP09.mkChunk 0x10488 (CImg (0x10548 - 0x10488));
YP09.mkChunk 0x10588 (CImg (0x1cd70 - 0x10588));
YP09.mkChunk 0x1cd85 (CImg (0x20d00 - 0x1cd85));
YP09.mkChunk 0x20d04 (CImg (0x20f9e - 0x20d04));
YP09.mkChunk 0x20fc0 (CImg (0x20fc8 - 0x20fc0));
YP09.mkChunk 0x20fe0 (CImg (0x20fe6 - 0x20fe0));
YP09.mkChunk 0x21000 (CImg (0x21005 - 0x21000));
YP09.mkChunk 0x21020 (CImg (0x21026 - 0x21020));
YP09.mkChunk 0x21040 (CImg (0x21045 - 0x21040));
YP09.mkChunk 0x21060 (CImg (0x21064 - 0x21060));
YP09.mkChunk 0x21080 (CImg (0x21085 - 0x21080));
YP09.mkChunk 0x210a0 (CImg (0x210a6 - 0x210a0));
YP09.mkChunk 0x210c0 (CImg (0x210c6 - 0x210c0));
YP09.mkChunk 0x210e0 (CImg (0x210e6 - 0x210e0));
YP09.mkChunk 0x21100 (CImg (0x21107 - 0x21100));
YP09.mkChunk 0x21120 (CImg (0x2112a - 0x21120));
YP09.mkChunk 0x21140 (CImg (0x21145 - 0x21140));
YP09.mkChunk 0x21160 (CImg (0x21164 - 0x21160));
YP09.mkChunk 0x21180 (CImg (0x21187 - 0x21180));
YP09.mkChunk 0x211a0 (CImg (0x211c7 - 0x211a0));
YP09.mkChunk 0x211e0 (CImg (0x211e7 - 0x211e0));
YP09.mkChunk 0x21200 (CImg (0x21208 - 0x21200));
YP09.mkChunk 0x21220 (CImg (0x21225 - 0x21220));
YP09.mkChunk 0x21240 (CImg (0x21243 - 0x21240));
YP09.mkChunk 0x21260 (CImg (0x21267 - 0x21260));
YP09.mkChunk 0x21280 (CImg (0x21286 - 0x21280));
YP09.mkChunk 0x212a0 (CImg (0x212e4 - 0x212a0));
YP09.mkChunk 0x21300 (CImg (0x21307 - 0x21300));
YP09.mkChunk 0x21320 (CImg (0x21328 - 0x21320));
YP09.mkChunk 0x21340 (CImg (0x21342 - 0x21340));
YP09.mkChunk 0x21360 (CImg (0x21389 - 0x21360));
YP09.mkChunk 0x213c0 (CImg (0x213c2 - 0x213c0));
YP09.mkChunk 0x213e0 (CImg (0x213e1 - 0x213e0));
YP09.mkChunk 0x21400 (CImg (0x2140d - 0x21400));
YP09.mkChunk 0x21420 (CImg (0x2142e - 0x21420));
YP09.mkChunk 0x21440 (CImg (0x21451 - 0x21440));
YP09.mkChunk 0x21480 (CImg (0x21493 - 0x21480));
YP09.mkChunk 0x214c0 (CImg (0x214cf - 0x214c0));
YP09.mkChunk 0x214e0 (CImg (0x214ec - 0x214e0));
YP09.mkChunk 0x21500 (CImg (0x21505 - 0x21500));
YP09.mkChunk 0x21520 (CImg (0x21526 - 0x21520));
YP09.mkChunk 0x21540 (CImg (0x21550 - 0x21540));
YP09.mkChunk 0x21560 (CImg (0x21562 - 0x21560));
YP09.mkChunk 0x21580 (CImg (0x215a7 - 0x21580));
YP09.mkChunk 0x215c0 (CImg (0x215e7 - 0x215c0));
YP09.mkChunk 0x21600 (CImg (0x21606 - 0x21600));
YP09.mkChunk 0x21620 (CImg (0x21628 - 0x21620));
YP09.mkChunk 0x21640 (CImg (0x21648 - 0x21640));
YP09.mkChunk 0x21660 (CImg (0x2168c - 0x21660));
YP09.mkChunk 0x216a0 (CImg (0x21c28 - 0x216a0));
YP09.mkChunk 0x21c2c (CImg (0x21c8c - 0x21c2c));
YP09.mkChunk 0x21c8e (CImg (IMG_RO_HI - 0x21c8e)) ].
Definition img_ro_region : YP09.region := YP09.mkRegion None IMG_RO_LO IMG_RO_HI 0 0 img_ro_chunks.
Definition ro_img (m : word -> option byte) : Prop := forall E, region_ok tfibsegs E m img_ro_region.
Definition ro_clean (m : word -> option byte) : Prop :=
forall x : word, IMG_RO_LO <= bv_unsigned x < IMG_RO_HI -> m x = None.
Lemma img_ro_bytes_ok : forallb (fun c => zallb (img_byte_ok tfibsegs) (YP09.c_off c) (Z.to_nat (c_len c))) img_ro_chunks = true.
Proof. vm_compute. reflexivity. Qed.
Lemma img_ro_chunks_inside : Forall (fun c => IMG_RO_LO <= YP09.c_off c /\ YP09.c_off c + c_len c <= IMG_RO_HI /\ exists n, YP09.c_val c = CImg n) img_ro_chunks.
Proof. unfold img_ro_chunks, IMG_RO_LO, IMG_RO_HI. repeat (apply Forall_cons; [cbn; split; [lia|]; split; [lia | eexists; reflexivity]|]). apply Forall_nil. Qed.
Lemma region_ok_img_of : forall E m,
(forall a, IMG_RO_LO <= a < IMG_RO_HI -> img_byte_ok tfibsegs a = true -> mbyte tfibsegs m a = img_byte tfibsegs a) ->
region_ok tfibsegs E m img_ro_region.
Proof.
intros E m Hm. unfold region_ok, img_ro_region.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [unfold IMG_RO_LO; lia|]. split; [unfold IMG_RO_HI; lia|]. split; [intros o Ho; lia|].
apply Forall_forall. intros c Hc i Hi.
pose proof (proj1 (Forall_forall _ _) img_ro_chunks_inside c Hc) as (Hlo & Hhi & n & Hv).
pose proof (proj1 (forallb_forall _ _) img_ro_bytes_ok c Hc) as Hz. cbn beta in Hz.
pose proof (zallb_sound _ _ _ (YP09.c_off c + i) Hz ltac:(lia)) as Hb.
rewrite !Z.add_0_l. destruct c as [co cv]; cbn [YP09.c_off YP09.c_val] in *. subst cv. cbn [cbyte].
rewrite (Hm (co + i)) by (first [lia | exact Hb]).
unfold img_byte_ok in Hb. destruct (img_byte tfibsegs (co + i)) as [b|]; [|discriminate]. exists b. split; reflexivity.
Qed.
Lemma region_ok_img_clean : forall E m, ro_clean m -> region_ok tfibsegs E m img_ro_region.
Proof.
intros E m Hc. apply region_ok_img_of. intros a Ha _. unfold img_byte, mbyte.
rewrite (Hc (Z_to_bv 64 a)) by (rewrite unsigned_lit_small by (unfold IMG_RO_LO, IMG_RO_HI in Ha; lia); exact Ha). reflexivity.
Qed.
Lemma ro_img_of_clean : forall m, ro_clean m -> ro_img m.
Proof. intros m Hc E. apply region_ok_img_clean. exact Hc. Qed.
Lemma ro_clean_mrestrict : forall (Hd : word -> bool) m, ro_clean m -> ro_clean (mrestrict Hd m).
Proof. intros Hd m Hc x Hx. unfold mrestrict. rewrite (Hc x Hx). destruct (Hd x); reflexivity. Qed.
Lemma ro_img_kept : forall (Hd : word -> bool) (m m' : word -> option byte),
(forall x : word, IMG_RO_LO <= bv_unsigned x < IMG_RO_HI -> m' x = m x) -> ro_img (mrestrict Hd m) -> ro_img (mrestrict Hd m').
Proof.
intros Hd m m' Heq Hro E. pose proof (Hro E) as (H1 & H2 & H3 & H4). split; [exact H1|]. split; [exact H2|]. split; [intros o Ho; exfalso; clear - Ho; cbn in Ho; lia|].
apply Forall_forall. intros c Hc i Hi. pose proof (proj1 (Forall_forall _ _) H4 c Hc i Hi) as (b & Hcb & Hmb). exists b. split; [exact Hcb|].
pose proof (proj1 (Forall_forall _ _) img_ro_chunks_inside c Hc) as (Hlo & Hhi & _).
revert Hmb. cbn [YP09.r_base base_val]. rewrite !Z.add_0_l. unfold mbyte, mrestrict.
rewrite (Heq (Z_to_bv 64 (YP09.c_off c + i))) by (rewrite unsigned_lit_small by (unfold IMG_RO_LO, IMG_RO_HI in *; lia); lia).
intros Hmb. exact Hmb.
Qed.
End d.
