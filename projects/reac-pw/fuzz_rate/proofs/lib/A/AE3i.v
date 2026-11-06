(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: generated for reac-pw/fuzz_rate image A by ae3i.py 3cf49addef7e from fuzz_rate.asan and lib/A/AF0m.v's Tfib_owned_static (IMG_RO_HI = this image's read-only PT_LOAD end), template proofs/cgif/cgif_file_fuzzer/lib/A/AE3i.v at c8557374ad2e *)
(* Read from: fuzz_rate.asan (reac-pw/fuzz_rate asan) sha256 22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; unstripped twin sha256 0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3 *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP01.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI04 YK04.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import AB1v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition IMG_RO_LO : Z := 0x10000.
Definition IMG_RO_HI : Z := 0x2f9d4.
Definition img_ro_chunks : list YP09.chunk :=
[ YP09.mkChunk 0x10000 (CImg (0x102e8 - 0x10000));
YP09.mkChunk 0x102f0 (CImg (0x10308 - 0x102f0));
YP09.mkChunk 0x10310 (CImg (0x10348 - 0x10310));
YP09.mkChunk 0x10350 (CImg (0x103b8 - 0x10350));
YP09.mkChunk 0x103c8 (CImg (0x103d0 - 0x103c8));
YP09.mkChunk 0x103d8 (CImg (0x10450 - 0x103d8));
YP09.mkChunk 0x10490 (CImg (0x10550 - 0x10490));
YP09.mkChunk 0x10590 (CImg (0x1ce0b - 0x10590));
YP09.mkChunk 0x1ce20 (CImg (0x20cf8 - 0x1ce20));
YP09.mkChunk 0x20cfc (CImg (0x20fae - 0x20cfc));
YP09.mkChunk 0x20fc0 (CImg (0x20fce - 0x20fc0));
YP09.mkChunk 0x20fe0 (CImg (0x20fee - 0x20fe0));
YP09.mkChunk 0x21000 (CImg (0x2100f - 0x21000));
YP09.mkChunk 0x21020 (CImg (0x2102e - 0x21020));
YP09.mkChunk 0x21040 (CImg (0x21053 - 0x21040));
YP09.mkChunk 0x21080 (CImg (0x2108d - 0x21080));
YP09.mkChunk 0x210a0 (CImg (0x210b0 - 0x210a0));
YP09.mkChunk 0x210c0 (CImg (0x210cd - 0x210c0));
YP09.mkChunk 0x210e0 (CImg (0x21118 - 0x210e0));
YP09.mkChunk 0x21140 (CImg (0x21194 - 0x21140));
YP09.mkChunk 0x211c0 (CImg (0x211d0 - 0x211c0));
YP09.mkChunk 0x211e0 (CImg (0x211f0 - 0x211e0));
YP09.mkChunk 0x21200 (CImg (0x2120e - 0x21200));
YP09.mkChunk 0x21220 (CImg (0x21223 - 0x21220));
YP09.mkChunk 0x21240 (CImg (0x21243 - 0x21240));
YP09.mkChunk 0x21260 (CImg (0x21263 - 0x21260));
YP09.mkChunk 0x21280 (CImg (0x21283 - 0x21280));
YP09.mkChunk 0x212a0 (CImg (0x212b5 - 0x212a0));
YP09.mkChunk 0x212e0 (CImg (0x212e1 - 0x212e0));
YP09.mkChunk 0x21300 (CImg (0x21302 - 0x21300));
YP09.mkChunk 0x21320 (CImg (0x21323 - 0x21320));
YP09.mkChunk 0x21340 (CImg (0x21343 - 0x21340));
YP09.mkChunk 0x21360 (CImg (0x21363 - 0x21360));
YP09.mkChunk 0x21380 (CImg (0x21383 - 0x21380));
YP09.mkChunk 0x213a0 (CImg (0x213a3 - 0x213a0));
YP09.mkChunk 0x213c0 (CImg (0x213c4 - 0x213c0));
YP09.mkChunk 0x213e0 (CImg (0x213f6 - 0x213e0));
YP09.mkChunk 0x21420 (CImg (0x21428 - 0x21420));
YP09.mkChunk 0x21440 (CImg (0x21444 - 0x21440));
YP09.mkChunk 0x21460 (CImg (0x21465 - 0x21460));
YP09.mkChunk 0x21480 (CImg (0x21484 - 0x21480));
YP09.mkChunk 0x214a0 (CImg (0x214a6 - 0x214a0));
YP09.mkChunk 0x214c0 (CImg (0x214ca - 0x214c0));
YP09.mkChunk 0x214e0 (CImg (0x214e6 - 0x214e0));
YP09.mkChunk 0x21500 (CImg (0x21502 - 0x21500));
YP09.mkChunk 0x21520 (CImg (0x2152c - 0x21520));
YP09.mkChunk 0x21540 (CImg (0x2154b - 0x21540));
YP09.mkChunk 0x21560 (CImg (0x2156d - 0x21560));
YP09.mkChunk 0x21580 (CImg (0x2158b - 0x21580));
YP09.mkChunk 0x215a0 (CImg (0x215aa - 0x215a0));
YP09.mkChunk 0x215c0 (CImg (0x215c5 - 0x215c0));
YP09.mkChunk 0x215e0 (CImg (0x21605 - 0x215e0));
YP09.mkChunk 0x21620 (CImg (0x2162b - 0x21620));
YP09.mkChunk 0x21640 (CImg (0x2164d - 0x21640));
YP09.mkChunk 0x21660 (CImg (0x2166b - 0x21660));
YP09.mkChunk 0x21680 (CImg (0x2168a - 0x21680));
YP09.mkChunk 0x216a0 (CImg (0x216ac - 0x216a0));
YP09.mkChunk 0x216c0 (CImg (0x216c5 - 0x216c0));
YP09.mkChunk 0x216e0 (CImg (0x216e2 - 0x216e0));
YP09.mkChunk 0x21700 (CImg (0x21701 - 0x21700));
YP09.mkChunk 0x21720 (CImg (0x2172e - 0x21720));
YP09.mkChunk 0x21740 (CImg (0x21cd0 - 0x21740));
YP09.mkChunk 0x21cd4 (CImg (0x21d34 - 0x21cd4));
YP09.mkChunk 0x21d36 (CImg (IMG_RO_HI - 0x21d36)) ].
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
