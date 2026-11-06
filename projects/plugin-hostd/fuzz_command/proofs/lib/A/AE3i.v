(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AE3i.v, with its module paths changed; the read-only image chunks regenerated for plugin-hostd/fuzz_command's ASan build: [0x10000, IMG_RO_HI) minus fuzz_command's owned rodata ranges (A/AF0m.v Tfib_owned_static: const cells, jump-table cells, 172 rodata globals' redzones), IMG_RO_HI = 0x32340 (.eh_frame end; cgif 0x2f1ac); the chunks split where A/AD2j.v's regions do (0x246a4, .rodata end). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI04 YK04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition IMG_RO_LO : Z := 0x10000.
Definition IMG_RO_HI : Z := 0x32340.
Definition img_ro_chunks : list YP09.chunk :=
[ YP09.mkChunk 0x10000 (CImg (0x102e8 - 0x10000));
YP09.mkChunk 0x102f0 (CImg (0x10308 - 0x102f0));
YP09.mkChunk 0x10310 (CImg (0x10328 - 0x10310));
YP09.mkChunk 0x10330 (CImg (0x10340 - 0x10330));
YP09.mkChunk 0x10348 (CImg (0x103a0 - 0x10348));
YP09.mkChunk 0x103b0 (CImg (0x103b8 - 0x103b0));
YP09.mkChunk 0x103c0 (CImg (0x10428 - 0x103c0));
YP09.mkChunk 0x10468 (CImg (0x10528 - 0x10468));
YP09.mkChunk 0x10568 (CImg (0x1cf22 - 0x10568));
YP09.mkChunk 0x1cf37 (CImg (0x20e28 - 0x1cf37));
YP09.mkChunk 0x20e2c (CImg (0x210a3 - 0x20e2c));
YP09.mkChunk 0x210c0 (CImg (0x210c8 - 0x210c0));
YP09.mkChunk 0x210e0 (CImg (0x210e7 - 0x210e0));
YP09.mkChunk 0x21100 (CImg (0x21105 - 0x21100));
YP09.mkChunk 0x21120 (CImg (0x21122 - 0x21120));
YP09.mkChunk 0x21140 (CImg (0x2114b - 0x21140));
YP09.mkChunk 0x21160 (CImg (0x2116b - 0x21160));
YP09.mkChunk 0x21180 (CImg (0x2118e - 0x21180));
YP09.mkChunk 0x211a0 (CImg (0x211b1 - 0x211a0));
YP09.mkChunk 0x211e0 (CImg (0x211e4 - 0x211e0));
YP09.mkChunk 0x21200 (CImg (0x2123d - 0x21200));
YP09.mkChunk 0x21260 (CImg (0x2126c - 0x21260));
YP09.mkChunk 0x21280 (CImg (0x21281 - 0x21280));
YP09.mkChunk 0x212a0 (CImg (0x212ae - 0x212a0));
YP09.mkChunk 0x212c0 (CImg (0x212cb - 0x212c0));
YP09.mkChunk 0x212e0 (CImg (0x212f1 - 0x212e0));
YP09.mkChunk 0x21320 (CImg (0x21331 - 0x21320));
YP09.mkChunk 0x21360 (CImg (0x21371 - 0x21360));
YP09.mkChunk 0x213a0 (CImg (0x213b1 - 0x213a0));
YP09.mkChunk 0x213e0 (CImg (0x213eb - 0x213e0));
YP09.mkChunk 0x21400 (CImg (0x2141f - 0x21400));
YP09.mkChunk 0x21440 (CImg (0x2144c - 0x21440));
YP09.mkChunk 0x21460 (CImg (0x21477 - 0x21460));
YP09.mkChunk 0x214a0 (CImg (0x214ab - 0x214a0));
YP09.mkChunk 0x214c0 (CImg (0x214e3 - 0x214c0));
YP09.mkChunk 0x21520 (CImg (0x21528 - 0x21520));
YP09.mkChunk 0x21540 (CImg (0x21591 - 0x21540));
YP09.mkChunk 0x215c0 (CImg (0x215ca - 0x215c0));
YP09.mkChunk 0x215e0 (CImg (0x215ec - 0x215e0));
YP09.mkChunk 0x21600 (CImg (0x2160f - 0x21600));
YP09.mkChunk 0x21620 (CImg (0x2164c - 0x21620));
YP09.mkChunk 0x21680 (CImg (0x2168b - 0x21680));
YP09.mkChunk 0x216a0 (CImg (0x216a6 - 0x216a0));
YP09.mkChunk 0x216c0 (CImg (0x216dd - 0x216c0));
YP09.mkChunk 0x21700 (CImg (0x21706 - 0x21700));
YP09.mkChunk 0x21720 (CImg (0x21744 - 0x21720));
YP09.mkChunk 0x21780 (CImg (0x2178c - 0x21780));
YP09.mkChunk 0x217a0 (CImg (0x217a8 - 0x217a0));
YP09.mkChunk 0x217c0 (CImg (0x217cf - 0x217c0));
YP09.mkChunk 0x217e0 (CImg (0x217ea - 0x217e0));
YP09.mkChunk 0x21800 (CImg (0x21807 - 0x21800));
YP09.mkChunk 0x21820 (CImg (0x2182a - 0x21820));
YP09.mkChunk 0x21840 (CImg (0x21848 - 0x21840));
YP09.mkChunk 0x21860 (CImg (0x2186b - 0x21860));
YP09.mkChunk 0x21880 (CImg (0x21884 - 0x21880));
YP09.mkChunk 0x218a0 (CImg (0x218a3 - 0x218a0));
YP09.mkChunk 0x218c0 (CImg (0x218c9 - 0x218c0));
YP09.mkChunk 0x218e0 (CImg (0x218e5 - 0x218e0));
YP09.mkChunk 0x21900 (CImg (0x21903 - 0x21900));
YP09.mkChunk 0x21920 (CImg (0x21928 - 0x21920));
YP09.mkChunk 0x21940 (CImg (0x21942 - 0x21940));
YP09.mkChunk 0x21960 (CImg (0x21966 - 0x21960));
YP09.mkChunk 0x21980 (CImg (0x21984 - 0x21980));
YP09.mkChunk 0x219a0 (CImg (0x219a3 - 0x219a0));
YP09.mkChunk 0x219c0 (CImg (0x219c2 - 0x219c0));
YP09.mkChunk 0x219e0 (CImg (0x219e4 - 0x219e0));
YP09.mkChunk 0x21a00 (CImg (0x21a05 - 0x21a00));
YP09.mkChunk 0x21a20 (CImg (0x21a26 - 0x21a20));
YP09.mkChunk 0x21a40 (CImg (0x21a47 - 0x21a40));
YP09.mkChunk 0x21a60 (CImg (0x21a65 - 0x21a60));
YP09.mkChunk 0x21a80 (CImg (0x21a88 - 0x21a80));
YP09.mkChunk 0x21aa0 (CImg (0x21aa2 - 0x21aa0));
YP09.mkChunk 0x21ac0 (CImg (0x21ac2 - 0x21ac0));
YP09.mkChunk 0x21ae0 (CImg (0x21ae4 - 0x21ae0));
YP09.mkChunk 0x21b00 (CImg (0x21b08 - 0x21b00));
YP09.mkChunk 0x21b20 (CImg (0x21b26 - 0x21b20));
YP09.mkChunk 0x21b40 (CImg (0x21b44 - 0x21b40));
YP09.mkChunk 0x21b60 (CImg (0x21b69 - 0x21b60));
YP09.mkChunk 0x21b80 (CImg (0x21c88 - 0x21b80));
YP09.mkChunk 0x21cc0 (CImg (0x21cc4 - 0x21cc0));
YP09.mkChunk 0x21ce0 (CImg (0x21ce7 - 0x21ce0));
YP09.mkChunk 0x21d00 (CImg (0x21d08 - 0x21d00));
YP09.mkChunk 0x21d20 (CImg (0x21d26 - 0x21d20));
YP09.mkChunk 0x21d40 (CImg (0x21d42 - 0x21d40));
YP09.mkChunk 0x21d60 (CImg (0x21d63 - 0x21d60));
YP09.mkChunk 0x21d80 (CImg (0x21d8c - 0x21d80));
YP09.mkChunk 0x21da0 (CImg (0x21dae - 0x21da0));
YP09.mkChunk 0x21dc0 (CImg (0x21dd1 - 0x21dc0));
YP09.mkChunk 0x21e00 (CImg (0x21e11 - 0x21e00));
YP09.mkChunk 0x21e40 (CImg (0x21e4b - 0x21e40));
YP09.mkChunk 0x21e60 (CImg (0x21e6b - 0x21e60));
YP09.mkChunk 0x21e80 (CImg (0x21e8c - 0x21e80));
YP09.mkChunk 0x21ea0 (CImg (0x21eaf - 0x21ea0));
YP09.mkChunk 0x21ec0 (CImg (0x21ecb - 0x21ec0));
YP09.mkChunk 0x21ee0 (CImg (0x21ee4 - 0x21ee0));
YP09.mkChunk 0x21f00 (CImg (0x21f03 - 0x21f00));
YP09.mkChunk 0x21f20 (CImg (0x21f26 - 0x21f20));
YP09.mkChunk 0x21f40 (CImg (0x21f4c - 0x21f40));
YP09.mkChunk 0x21f60 (CImg (0x21f6f - 0x21f60));
YP09.mkChunk 0x21f80 (CImg (0x21f8a - 0x21f80));
YP09.mkChunk 0x21fa0 (CImg (0x21fa2 - 0x21fa0));
YP09.mkChunk 0x21fc0 (CImg (0x21fc4 - 0x21fc0));
YP09.mkChunk 0x21fe0 (CImg (0x21ff0 - 0x21fe0));
YP09.mkChunk 0x22000 (CImg (0x2203d - 0x22000));
YP09.mkChunk 0x22060 (CImg (0x22096 - 0x22060));
YP09.mkChunk 0x220c0 (CImg (0x220c8 - 0x220c0));
YP09.mkChunk 0x220e0 (CImg (0x220ea - 0x220e0));
YP09.mkChunk 0x22100 (CImg (0x2210b - 0x22100));
YP09.mkChunk 0x22120 (CImg (0x22139 - 0x22120));
YP09.mkChunk 0x22160 (CImg (0x2216b - 0x22160));
YP09.mkChunk 0x22180 (CImg (0x22190 - 0x22180));
YP09.mkChunk 0x221a0 (CImg (0x221ab - 0x221a0));
YP09.mkChunk 0x221c0 (CImg (0x221cd - 0x221c0));
YP09.mkChunk 0x221e0 (CImg (0x221ed - 0x221e0));
YP09.mkChunk 0x22200 (CImg (0x22210 - 0x22200));
YP09.mkChunk 0x22220 (CImg (0x2226f - 0x22220));
YP09.mkChunk 0x222a0 (CImg (0x222ab - 0x222a0));
YP09.mkChunk 0x222c0 (CImg (0x22303 - 0x222c0));
YP09.mkChunk 0x22340 (CImg (0x2234c - 0x22340));
YP09.mkChunk 0x22360 (CImg (0x2236b - 0x22360));
YP09.mkChunk 0x22380 (CImg (0x22399 - 0x22380));
YP09.mkChunk 0x223c0 (CImg (0x223cb - 0x223c0));
YP09.mkChunk 0x223e0 (CImg (0x223f2 - 0x223e0));
YP09.mkChunk 0x22420 (CImg (0x22428 - 0x22420));
YP09.mkChunk 0x22440 (CImg (0x22449 - 0x22440));
YP09.mkChunk 0x22460 (CImg (0x2246e - 0x22460));
YP09.mkChunk 0x22480 (CImg (0x22487 - 0x22480));
YP09.mkChunk 0x224a0 (CImg (0x224c3 - 0x224a0));
YP09.mkChunk 0x224e0 (CImg (0x224f2 - 0x224e0));
YP09.mkChunk 0x22520 (CImg (0x22533 - 0x22520));
YP09.mkChunk 0x22560 (CImg (0x22564 - 0x22560));
YP09.mkChunk 0x22580 (CImg (0x2258f - 0x22580));
YP09.mkChunk 0x225a0 (CImg (0x225aa - 0x225a0));
YP09.mkChunk 0x225c0 (CImg (0x225ca - 0x225c0));
YP09.mkChunk 0x225e0 (CImg (0x225ec - 0x225e0));
YP09.mkChunk 0x22600 (CImg (0x2260e - 0x22600));
YP09.mkChunk 0x22620 (CImg (0x22631 - 0x22620));
YP09.mkChunk 0x22660 (CImg (0x22664 - 0x22660));
YP09.mkChunk 0x22680 (CImg (0x22691 - 0x22680));
YP09.mkChunk 0x226c0 (CImg (0x226cb - 0x226c0));
YP09.mkChunk 0x226e0 (CImg (0x226ef - 0x226e0));
YP09.mkChunk 0x22700 (CImg (0x2270c - 0x22700));
YP09.mkChunk 0x22720 (CImg (0x2272b - 0x22720));
YP09.mkChunk 0x22740 (CImg (0x22746 - 0x22740));
YP09.mkChunk 0x22760 (CImg (0x2276c - 0x22760));
YP09.mkChunk 0x22780 (CImg (0x22788 - 0x22780));
YP09.mkChunk 0x227a0 (CImg (0x227ab - 0x227a0));
YP09.mkChunk 0x227c0 (CImg (0x227ca - 0x227c0));
YP09.mkChunk 0x227e0 (CImg (0x227e5 - 0x227e0));
YP09.mkChunk 0x22800 (CImg (0x2280e - 0x22800));
YP09.mkChunk 0x22820 (CImg (0x22831 - 0x22820));
YP09.mkChunk 0x22860 (CImg (0x22864 - 0x22860));
YP09.mkChunk 0x22880 (CImg (0x22888 - 0x22880));
YP09.mkChunk 0x228a0 (CImg (0x228a6 - 0x228a0));
YP09.mkChunk 0x228c0 (CImg (0x228c9 - 0x228c0));
YP09.mkChunk 0x228e0 (CImg (0x228eb - 0x228e0));
YP09.mkChunk 0x22900 (CImg (0x2290d - 0x22900));
YP09.mkChunk 0x22920 (CImg (0x22930 - 0x22920));
YP09.mkChunk 0x22940 (CImg (0x2294b - 0x22940));
YP09.mkChunk 0x22960 (CImg (0x2296c - 0x22960));
YP09.mkChunk 0x22980 (CImg (0x2298b - 0x22980));
YP09.mkChunk 0x229a0 (CImg (0x229ab - 0x229a0));
YP09.mkChunk 0x229c0 (CImg (0x229c8 - 0x229c0));
YP09.mkChunk 0x229e0 (CImg (0x229e9 - 0x229e0));
YP09.mkChunk 0x22a00 (CImg (0x22a0e - 0x22a00));
YP09.mkChunk 0x22a20 (CImg (0x22a38 - 0x22a20));
YP09.mkChunk 0x22a60 (CImg (0x22a6d - 0x22a60));
YP09.mkChunk 0x22a80 (CImg (0x22a93 - 0x22a80));
YP09.mkChunk 0x22ac0 (CImg (0x22ad0 - 0x22ac0));
YP09.mkChunk 0x22ae0 (CImg (0x22afa - 0x22ae0));
YP09.mkChunk 0x22b20 (CImg (0x22b30 - 0x22b20));
YP09.mkChunk 0x22b40 (CImg (0x22b4c - 0x22b40));
YP09.mkChunk 0x22b60 (CImg (0x22b75 - 0x22b60));
YP09.mkChunk 0x22ba0 (CImg (0x22bb7 - 0x22ba0));
YP09.mkChunk 0x22be0 (CImg (0x22bfb - 0x22be0));
YP09.mkChunk 0x22c20 (CImg (0x22c31 - 0x22c20));
YP09.mkChunk 0x22c60 (CImg (0x22c8f - 0x22c60));
YP09.mkChunk 0x22cc0 (CImg (0x22ccf - 0x22cc0));
YP09.mkChunk 0x22ce0 (CImg (0x22cf6 - 0x22ce0));
YP09.mkChunk 0x22d20 (CImg (0x22d39 - 0x22d20));
YP09.mkChunk 0x22d60 (CImg (0x22d6f - 0x22d60));
YP09.mkChunk 0x22d80 (CImg (0x22d82 - 0x22d80));
YP09.mkChunk 0x22da0 (CImg (0x2331c - 0x22da0));
YP09.mkChunk 0x23320 (CImg (0x23380 - 0x23320));
YP09.mkChunk 0x23382 (CImg (0x246a4 - 0x23382));
YP09.mkChunk 0x246a4 (CImg (IMG_RO_HI - 0x246a4)) ].
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
