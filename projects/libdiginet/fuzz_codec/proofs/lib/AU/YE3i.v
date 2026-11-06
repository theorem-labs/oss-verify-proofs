(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: IMG_RO_LO / IMG_RO_HI / img_ro_chunks generated for libdiginet/fuzz_codec's asan-ubsan image by ae3i.py (frozen 3cf49addef7e): the chunks are [IMG_RO_LO, IMG_RO_HI) minus lib/AU/YF0m.v's Tfib_owned_static (the rule reproduces cgif's own 15 chunks byte for byte), and IMG_RO_HI is THIS image's read-only PT_LOAD end - the donor's 0x2f1ac is a free choice, not a derivable boundary, so relocating it is unsound *)
(* Read from: fuzz_codec.asan-ubsan (libdiginet/fuzz_codec asan-ubsan) sha256 73109e32e77beff294d41ae6f16d607479ad1884485781b322645e6f8afa99c3; unstripped twin sha256 43feeaa314a42fe569b4443c710a74561e9077e617f7412cc54fbf4a6557b266 *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP01.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI04 YK04. From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition IMG_RO_LO : Z := 0x10000.
Definition IMG_RO_HI : Z := 0x2fc84.
Definition img_ro_chunks : list YP09.chunk :=
[ YP09.mkChunk 0x10000 (CImg (0x102e8 - 0x10000));
YP09.mkChunk 0x102f0 (CImg (0x10308 - 0x102f0));
YP09.mkChunk 0x10310 (CImg (0x10328 - 0x10310));
YP09.mkChunk 0x10330 (CImg (0x10398 - 0x10330));
YP09.mkChunk 0x103a8 (CImg (0x103b0 - 0x103a8));
YP09.mkChunk 0x103b8 (CImg (0x10420 - 0x103b8));
YP09.mkChunk 0x10460 (CImg (0x10520 - 0x10460));
YP09.mkChunk 0x10560 (CImg (0x1ce4d - 0x10560));
YP09.mkChunk 0x1ce62 (CImg (0x20c98 - 0x1ce62));
YP09.mkChunk 0x20c9c (CImg (0x20fac - 0x20c9c));
YP09.mkChunk 0x20fc0 (CImg (0x20fc9 - 0x20fc0));
YP09.mkChunk 0x20fe0 (CImg (0x20fe9 - 0x20fe0));
YP09.mkChunk 0x21000 (CImg (0x21008 - 0x21000));
YP09.mkChunk 0x21020 (CImg (0x2102a - 0x21020));
YP09.mkChunk 0x21040 (CImg (0x21041 - 0x21040));
YP09.mkChunk 0x21060 (CImg (0x21067 - 0x21060));
YP09.mkChunk 0x21080 (CImg (0x21083 - 0x21080));
YP09.mkChunk 0x210a0 (CImg (0x210a6 - 0x210a0));
YP09.mkChunk 0x210c0 (CImg (0x210c6 - 0x210c0));
YP09.mkChunk 0x210e0 (CImg (0x210e5 - 0x210e0));
YP09.mkChunk 0x21100 (CImg (0x21106 - 0x21100));
YP09.mkChunk 0x21120 (CImg (0x21127 - 0x21120));
YP09.mkChunk 0x21140 (CImg (0x21144 - 0x21140));
YP09.mkChunk 0x21160 (CImg (0x21168 - 0x21160));
YP09.mkChunk 0x21180 (CImg (0x21187 - 0x21180));
YP09.mkChunk 0x211a0 (CImg (0x211a7 - 0x211a0));
YP09.mkChunk 0x211c0 (CImg (0x211c6 - 0x211c0));
YP09.mkChunk 0x211e0 (CImg (0x211e5 - 0x211e0));
YP09.mkChunk 0x21200 (CImg (0x21206 - 0x21200));
YP09.mkChunk 0x21220 (CImg (0x21226 - 0x21220));
YP09.mkChunk 0x21240 (CImg (0x21245 - 0x21240));
YP09.mkChunk 0x21260 (CImg (0x21266 - 0x21260));
YP09.mkChunk 0x21280 (CImg (0x21285 - 0x21280));
YP09.mkChunk 0x212a0 (CImg (0x212a5 - 0x212a0));
YP09.mkChunk 0x212c0 (CImg (0x212c4 - 0x212c0));
YP09.mkChunk 0x212e0 (CImg (0x212e5 - 0x212e0));
YP09.mkChunk 0x21300 (CImg (0x21306 - 0x21300));
YP09.mkChunk 0x21320 (CImg (0x21323 - 0x21320));
YP09.mkChunk 0x21340 (CImg (0x21346 - 0x21340));
YP09.mkChunk 0x21360 (CImg (0x21366 - 0x21360));
YP09.mkChunk 0x21380 (CImg (0x21382 - 0x21380));
YP09.mkChunk 0x213a0 (CImg (0x213c9 - 0x213a0));
YP09.mkChunk 0x213e0 (CImg (0x213e9 - 0x213e0));
YP09.mkChunk 0x21400 (CImg (0x2156c - 0x21400));
YP09.mkChunk 0x215c0 (CImg (0x21b44 - 0x215c0));
YP09.mkChunk 0x21b48 (CImg (0x21ba8 - 0x21b48));
YP09.mkChunk 0x21baa (CImg (IMG_RO_HI - 0x21baa)) ].
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
