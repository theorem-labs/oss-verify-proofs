(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YE3i.v (donor image sha256 1c29845fe605), with its module paths changed and its addresses moved to libreac/fuzz_ctrl's ASan build. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YI04 YK04 YB1v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition IMG_RO_LO : Z := 0x10000.
Definition IMG_RO_HI : Z := 0x3012c.
Definition img_ro_chunks : list YP09.chunk :=
[ YP09.mkChunk 0x10000 (CImg (0x102e8 - 0x10000));
YP09.mkChunk 0x102f0 (CImg (0x10308 - 0x102f0));
YP09.mkChunk 0x10310 (CImg (0x10328 - 0x10310));
YP09.mkChunk 0x10330 (CImg (0x10338 - 0x10330));
YP09.mkChunk 0x10340 (CImg (0x10398 - 0x10340));
YP09.mkChunk 0x103a8 (CImg (0x103b0 - 0x103a8));
YP09.mkChunk 0x103b8 (CImg (0x10420 - 0x103b8));
YP09.mkChunk 0x10460 (CImg (0x10520 - 0x10460));
YP09.mkChunk 0x10560 (CImg (0x1d078 - 0x10560));
YP09.mkChunk 0x1d08d (CImg (0x20ecc - 0x1d08d));
YP09.mkChunk 0x20ed0 (CImg (0x21146 - 0x20ed0));
YP09.mkChunk 0x21160 (CImg (0x21161 - 0x21160));
YP09.mkChunk 0x21180 (CImg (0x2118c - 0x21180));
YP09.mkChunk 0x211a0 (CImg (0x211e2 - 0x211a0));
YP09.mkChunk 0x21200 (CImg (0x21207 - 0x21200));
YP09.mkChunk 0x21220 (CImg (0x21225 - 0x21220));
YP09.mkChunk 0x21240 (CImg (0x21247 - 0x21240));
YP09.mkChunk 0x21260 (CImg (0x2126f - 0x21260));
YP09.mkChunk 0x21280 (CImg (0x2128a - 0x21280));
YP09.mkChunk 0x212a0 (CImg (0x212b0 - 0x212a0));
YP09.mkChunk 0x212c0 (CImg (0x212c6 - 0x212c0));
YP09.mkChunk 0x212e0 (CImg (0x212e8 - 0x212e0));
YP09.mkChunk 0x21300 (CImg (0x21307 - 0x21300));
YP09.mkChunk 0x21320 (CImg (0x2132f - 0x21320));
YP09.mkChunk 0x21340 (CImg (0x21350 - 0x21340));
YP09.mkChunk 0x21360 (CImg (0x2136a - 0x21360));
YP09.mkChunk 0x21380 (CImg (0x21390 - 0x21380));
YP09.mkChunk 0x213a0 (CImg (0x213a6 - 0x213a0));
YP09.mkChunk 0x213c0 (CImg (0x213cd - 0x213c0));
YP09.mkChunk 0x213e0 (CImg (0x213e6 - 0x213e0));
YP09.mkChunk 0x21400 (CImg (0x21417 - 0x21400));
YP09.mkChunk 0x21440 (CImg (0x21446 - 0x21440));
YP09.mkChunk 0x21460 (CImg (0x21476 - 0x21460));
YP09.mkChunk 0x214a0 (CImg (0x214a7 - 0x214a0));
YP09.mkChunk 0x214c0 (CImg (0x214c7 - 0x214c0));
YP09.mkChunk 0x214e0 (CImg (0x214fd - 0x214e0));
YP09.mkChunk 0x21520 (CImg (0x2152c - 0x21520));
YP09.mkChunk 0x21540 (CImg (0x2155d - 0x21540));
YP09.mkChunk 0x21580 (CImg (0x21586 - 0x21580));
YP09.mkChunk 0x215a0 (CImg (0x215b7 - 0x215a0));
YP09.mkChunk 0x215e0 (CImg (0x215e8 - 0x215e0));
YP09.mkChunk 0x21600 (CImg (0x21606 - 0x21600));
YP09.mkChunk 0x21620 (CImg (0x21638 - 0x21620));
YP09.mkChunk 0x21660 (CImg (0x21668 - 0x21660));
YP09.mkChunk 0x21680 (CImg (0x21687 - 0x21680));
YP09.mkChunk 0x216a0 (CImg (0x216b8 - 0x216a0));
YP09.mkChunk 0x216e0 (CImg (0x216e9 - 0x216e0));
YP09.mkChunk 0x21700 (CImg (0x21707 - 0x21700));
YP09.mkChunk 0x21720 (CImg (0x21738 - 0x21720));
YP09.mkChunk 0x21760 (CImg (0x21769 - 0x21760));
YP09.mkChunk 0x21780 (CImg (0x21787 - 0x21780));
YP09.mkChunk 0x217a0 (CImg (0x217b7 - 0x217a0));
YP09.mkChunk 0x217e0 (CImg (0x217e8 - 0x217e0));
YP09.mkChunk 0x21800 (CImg (0x21807 - 0x21800));
YP09.mkChunk 0x21820 (CImg (0x21837 - 0x21820));
YP09.mkChunk 0x21860 (CImg (0x21868 - 0x21860));
YP09.mkChunk 0x21880 (CImg (0x21887 - 0x21880));
YP09.mkChunk 0x218a0 (CImg (0x218b8 - 0x218a0));
YP09.mkChunk 0x218e0 (CImg (0x218e8 - 0x218e0));
YP09.mkChunk 0x21900 (CImg (0x21920 - 0x21900));
YP09.mkChunk 0x21940 (CImg (0x21960 - 0x21940));
YP09.mkChunk 0x21980 (CImg (0x219b8 - 0x21980));
YP09.mkChunk 0x219e0 (CImg (0x21a40 - 0x219e0));
YP09.mkChunk 0x21a60 (CImg (0x21a80 - 0x21a60));
YP09.mkChunk 0x21aa0 (CImg (0x22030 - 0x21aa0));
YP09.mkChunk 0x22034 (CImg (0x22094 - 0x22034));
YP09.mkChunk 0x22096 (CImg (IMG_RO_HI - 0x22096)) ].
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
