(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: generated for reac-pw/fuzz_segconf image A by ae3i.py 3cf49addef7e from fuzz_segconf.asan and lib/A/AF0m.v's Tfib_owned_static (IMG_RO_HI = this image's read-only PT_LOAD end), template proofs/cgif/cgif_file_fuzzer/lib/A/AE3i.v at c8557374ad2e *)
(* Read from: fuzz_segconf.asan (reac-pw/fuzz_segconf asan) sha256 48c5355bdacbc5ba2e0a9ff843627969cb5d2913316654369904b549fc904ef8; unstripped twin sha256 4362701197e4cecdb46108f7694774021f7b8d5e7bd85cfe200fa90ad7a63c32 *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI04 YK04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import AB1v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition IMG_RO_LO : Z := 0x10000.
Definition IMG_RO_HI : Z := 0x30ed4.
Definition img_ro_chunks : list YP09.chunk :=
[ YP09.mkChunk 0x10000 (CImg (0x102e8 - 0x10000));
YP09.mkChunk 0x102f0 (CImg (0x10308 - 0x102f0));
YP09.mkChunk 0x10310 (CImg (0x10328 - 0x10310));
YP09.mkChunk 0x10330 (CImg (0x10338 - 0x10330));
YP09.mkChunk 0x10340 (CImg (0x10398 - 0x10340));
YP09.mkChunk 0x103a8 (CImg (0x103b0 - 0x103a8));
YP09.mkChunk 0x103b8 (CImg (0x10428 - 0x103b8));
YP09.mkChunk 0x10468 (CImg (0x10528 - 0x10468));
YP09.mkChunk 0x10568 (CImg (0x1ceea - 0x10568));
YP09.mkChunk 0x1ceff (CImg (0x20d64 - 0x1ceff));
YP09.mkChunk 0x20d68 (CImg (0x20ff9 - 0x20d68));
YP09.mkChunk 0x21020 (CImg (0x21024 - 0x21020));
YP09.mkChunk 0x21040 (CImg (0x21048 - 0x21040));
YP09.mkChunk 0x21060 (CImg (0x21067 - 0x21060));
YP09.mkChunk 0x21080 (CImg (0x21083 - 0x21080));
YP09.mkChunk 0x210a0 (CImg (0x210ad - 0x210a0));
YP09.mkChunk 0x210c0 (CImg (0x210c8 - 0x210c0));
YP09.mkChunk 0x210e0 (CImg (0x210e5 - 0x210e0));
YP09.mkChunk 0x21100 (CImg (0x21108 - 0x21100));
YP09.mkChunk 0x21120 (CImg (0x21125 - 0x21120));
YP09.mkChunk 0x21140 (CImg (0x21145 - 0x21140));
YP09.mkChunk 0x21160 (CImg (0x21167 - 0x21160));
YP09.mkChunk 0x21180 (CImg (0x21186 - 0x21180));
YP09.mkChunk 0x211a0 (CImg (0x211a4 - 0x211a0));
YP09.mkChunk 0x211c0 (CImg (0x211c4 - 0x211c0));
YP09.mkChunk 0x211e0 (CImg (0x211f4 - 0x211e0));
YP09.mkChunk 0x21220 (CImg (0x21226 - 0x21220));
YP09.mkChunk 0x21240 (CImg (0x21247 - 0x21240));
YP09.mkChunk 0x21260 (CImg (0x21264 - 0x21260));
YP09.mkChunk 0x21280 (CImg (0x21285 - 0x21280));
YP09.mkChunk 0x212a0 (CImg (0x212a3 - 0x212a0));
YP09.mkChunk 0x212c0 (CImg (0x212c6 - 0x212c0));
YP09.mkChunk 0x212e0 (CImg (0x212e6 - 0x212e0));
YP09.mkChunk 0x21300 (CImg (0x2130e - 0x21300));
YP09.mkChunk 0x21320 (CImg (0x21343 - 0x21320));
YP09.mkChunk 0x21360 (CImg (0x2136d - 0x21360));
YP09.mkChunk 0x21380 (CImg (0x21384 - 0x21380));
YP09.mkChunk 0x213a0 (CImg (0x213cf - 0x213a0));
YP09.mkChunk 0x21400 (CImg (0x2141c - 0x21400));
YP09.mkChunk 0x21440 (CImg (0x21463 - 0x21440));
YP09.mkChunk 0x214a0 (CImg (0x214a8 - 0x214a0));
YP09.mkChunk 0x214c0 (CImg (0x214fd - 0x214c0));
YP09.mkChunk 0x21520 (CImg (0x2153b - 0x21520));
YP09.mkChunk 0x21560 (CImg (0x2159a - 0x21560));
YP09.mkChunk 0x215c0 (CImg (0x215fb - 0x215c0));
YP09.mkChunk 0x21620 (CImg (0x21666 - 0x21620));
YP09.mkChunk 0x216a0 (CImg (0x216dc - 0x216a0));
YP09.mkChunk 0x21700 (CImg (0x2172d - 0x21700));
YP09.mkChunk 0x21760 (CImg (0x21765 - 0x21760));
YP09.mkChunk 0x21780 (CImg (0x217c1 - 0x21780));
YP09.mkChunk 0x21800 (CImg (0x21806 - 0x21800));
YP09.mkChunk 0x21820 (CImg (0x21825 - 0x21820));
YP09.mkChunk 0x21840 (CImg (0x21842 - 0x21840));
YP09.mkChunk 0x21860 (CImg (0x21861 - 0x21860));
YP09.mkChunk 0x21880 (CImg (0x218b4 - 0x21880));
YP09.mkChunk 0x218e0 (CImg (0x218e7 - 0x218e0));
YP09.mkChunk 0x21900 (CImg (0x21929 - 0x21900));
YP09.mkChunk 0x21960 (CImg (0x21966 - 0x21960));
YP09.mkChunk 0x21980 (CImg (0x21a12 - 0x21980));
YP09.mkChunk 0x21a40 (CImg (0x21a75 - 0x21a40));
YP09.mkChunk 0x21aa0 (CImg (0x21aa8 - 0x21aa0));
YP09.mkChunk 0x21ac0 (CImg (0x21ac5 - 0x21ac0));
YP09.mkChunk 0x21ae0 (CImg (0x21ae5 - 0x21ae0));
YP09.mkChunk 0x21b00 (CImg (0x21b07 - 0x21b00));
YP09.mkChunk 0x21b20 (CImg (0x21b26 - 0x21b20));
YP09.mkChunk 0x21b40 (CImg (0x21b44 - 0x21b40));
YP09.mkChunk 0x21b60 (CImg (0x21b64 - 0x21b60));
YP09.mkChunk 0x21b80 (CImg (0x21b84 - 0x21b80));
YP09.mkChunk 0x21ba0 (CImg (0x21ba5 - 0x21ba0));
YP09.mkChunk 0x21bc0 (CImg (0x21bc3 - 0x21bc0));
YP09.mkChunk 0x21be0 (CImg (0x21be6 - 0x21be0));
YP09.mkChunk 0x21c00 (CImg (0x21c68 - 0x21c00));
YP09.mkChunk 0x21ca0 (CImg (0x21cfc - 0x21ca0));
YP09.mkChunk 0x21d20 (CImg (0x21d46 - 0x21d20));
YP09.mkChunk 0x21d60 (CImg (0x21d77 - 0x21d60));
YP09.mkChunk 0x21da0 (CImg (0x21da6 - 0x21da0));
YP09.mkChunk 0x21dc0 (CImg (0x21dd6 - 0x21dc0));
YP09.mkChunk 0x21e00 (CImg (0x21e07 - 0x21e00));
YP09.mkChunk 0x21e20 (CImg (0x21e3d - 0x21e20));
YP09.mkChunk 0x21e60 (CImg (0x21e6c - 0x21e60));
YP09.mkChunk 0x21e80 (CImg (0x21e9d - 0x21e80));
YP09.mkChunk 0x21ec0 (CImg (0x21ec6 - 0x21ec0));
YP09.mkChunk 0x21ee0 (CImg (0x21ef7 - 0x21ee0));
YP09.mkChunk 0x21f20 (CImg (0x21f26 - 0x21f20));
YP09.mkChunk 0x21f40 (CImg (0x21f58 - 0x21f40));
YP09.mkChunk 0x21f80 (CImg (0x21f87 - 0x21f80));
YP09.mkChunk 0x21fa0 (CImg (0x21fb8 - 0x21fa0));
YP09.mkChunk 0x21fe0 (CImg (0x21fe7 - 0x21fe0));
YP09.mkChunk 0x22000 (CImg (0x22018 - 0x22000));
YP09.mkChunk 0x22040 (CImg (0x22047 - 0x22040));
YP09.mkChunk 0x22060 (CImg (0x22077 - 0x22060));
YP09.mkChunk 0x220a0 (CImg (0x220a7 - 0x220a0));
YP09.mkChunk 0x220c0 (CImg (0x220d7 - 0x220c0));
YP09.mkChunk 0x22100 (CImg (0x22107 - 0x22100));
YP09.mkChunk 0x22120 (CImg (0x22138 - 0x22120));
YP09.mkChunk 0x22160 (CImg (0x226e4 - 0x22160));
YP09.mkChunk 0x226e8 (CImg (0x22748 - 0x226e8));
YP09.mkChunk 0x2274a (CImg (IMG_RO_HI - 0x2274a)) ].
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
