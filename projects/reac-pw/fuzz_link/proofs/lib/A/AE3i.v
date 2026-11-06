(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Read from: fuzz_link.asan (reac-pw/fuzz_link asan) sha256 059dae63e07ca2d80ae9227fa125d40586a02172c96d2b6884f8617ab912061d; unstripped twin sha256 66cd0f159895f119b29a44eb3760cfda78506402a019729057dba69562af9d9f *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP01.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YI04 YK04.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AF0m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition IMG_RO_LO : Z := 0x10000.
Definition IMG_RO_HI : Z := 0x3026c.
Definition img_ro_chunks : list YP09.chunk :=
[ YP09.mkChunk 0x10000 (CImg (0x102e8 - 0x10000));
YP09.mkChunk 0x102f0 (CImg (0x10308 - 0x102f0));
YP09.mkChunk 0x10310 (CImg (0x10338 - 0x10310));
YP09.mkChunk 0x10340 (CImg (0x103b0 - 0x10340));
YP09.mkChunk 0x103c0 (CImg (0x103c8 - 0x103c0));
YP09.mkChunk 0x103d0 (CImg (0x10438 - 0x103d0));
YP09.mkChunk 0x10478 (CImg (0x10538 - 0x10478));
YP09.mkChunk 0x10578 (CImg (0x1ce78 - 0x10578));
YP09.mkChunk 0x1ce8d (CImg (0x20cfc - 0x1ce8d));
YP09.mkChunk 0x20d00 (CImg (0x20fa5 - 0x20d00));
YP09.mkChunk 0x20fc0 (CImg (0x20fc1 - 0x20fc0));
YP09.mkChunk 0x20fe0 (CImg (0x20fec - 0x20fe0));
YP09.mkChunk 0x21000 (CImg (0x21005 - 0x21000));
YP09.mkChunk 0x21020 (CImg (0x21026 - 0x21020));
YP09.mkChunk 0x21040 (CImg (0x21049 - 0x21040));
YP09.mkChunk 0x21060 (CImg (0x21066 - 0x21060));
YP09.mkChunk 0x21080 (CImg (0x21098 - 0x21080));
YP09.mkChunk 0x210c0 (CImg (0x210c2 - 0x210c0));
YP09.mkChunk 0x210e0 (CImg (0x210f0 - 0x210e0));
YP09.mkChunk 0x21100 (CImg (0x2110f - 0x21100));
YP09.mkChunk 0x21120 (CImg (0x2112f - 0x21120));
YP09.mkChunk 0x21140 (CImg (0x2114b - 0x21140));
YP09.mkChunk 0x21160 (CImg (0x21169 - 0x21160));
YP09.mkChunk 0x21180 (CImg (0x21190 - 0x21180));
YP09.mkChunk 0x211a0 (CImg (0x211a8 - 0x211a0));
YP09.mkChunk 0x211c0 (CImg (0x211c5 - 0x211c0));
YP09.mkChunk 0x211e0 (CImg (0x211e5 - 0x211e0));
YP09.mkChunk 0x21200 (CImg (0x21206 - 0x21200));
YP09.mkChunk 0x21220 (CImg (0x21224 - 0x21220));
YP09.mkChunk 0x21240 (CImg (0x21243 - 0x21240));
YP09.mkChunk 0x21260 (CImg (0x21262 - 0x21260));
YP09.mkChunk 0x21280 (CImg (0x212a9 - 0x21280));
YP09.mkChunk 0x212c0 (CImg (0x212c5 - 0x212c0));
YP09.mkChunk 0x212e0 (CImg (0x212e8 - 0x212e0));
YP09.mkChunk 0x21300 (CImg (0x21394 - 0x21300));
YP09.mkChunk 0x213c0 (CImg (0x213cf - 0x213c0));
YP09.mkChunk 0x213e0 (CImg (0x21447 - 0x213e0));
YP09.mkChunk 0x21480 (CImg (0x214a3 - 0x21480));
YP09.mkChunk 0x214e0 (CImg (0x214e1 - 0x214e0));
YP09.mkChunk 0x21500 (CImg (0x21576 - 0x21500));
YP09.mkChunk 0x215a0 (CImg (0x2161a - 0x215a0));
YP09.mkChunk 0x21640 (CImg (0x21648 - 0x21640));
YP09.mkChunk 0x21660 (CImg (0x2166d - 0x21660));
YP09.mkChunk 0x21680 (CImg (0x21683 - 0x21680));
YP09.mkChunk 0x216a0 (CImg (0x21c28 - 0x216a0));
YP09.mkChunk 0x21c2c (CImg (0x21c8c - 0x21c2c));
YP09.mkChunk 0x21c8e (CImg (IMG_RO_HI - 0x21c8e)) ].
Definition ro_owned_in_range : list (Z * Z) :=
filter (fun r => (IMG_RO_LO <=? fst r) && (fst r + snd r <=? IMG_RO_HI)) AF0m.Tfib_owned_static.
Fixpoint ro_insert (x : Z * Z) (l : list (Z * Z)) : list (Z * Z) :=
match l with
| [] => [x]
| y :: l' => if fst x <=? fst y then x :: y :: l' else y :: ro_insert x l'
end.
Fixpoint ro_sort (l : list (Z * Z)) : list (Z * Z) :=
match l with [] => [] | x :: l' => ro_insert x (ro_sort l') end.
Fixpoint ro_complement (lo : Z) (rs : list (Z * Z)) : list (Z * Z) :=
match rs with
| [] => if lo <? IMG_RO_HI then [(lo, IMG_RO_HI - lo)] else []
| (a, n) :: rs' => (if lo <? a then [(lo, a - lo)] else []) ++ ro_complement (Z.max lo (a + n)) rs'
end.
Lemma img_ro_complement_ok :
map (fun c => (YP09.c_off c, c_len c)) img_ro_chunks = ro_complement IMG_RO_LO (ro_sort ro_owned_in_range).
Proof. vm_compute. reflexivity. Qed.
Lemma img_ro_seg0 :
nth_error (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_base s) + Z.of_N (seg_size s), seg_writable s)) tfibsegs) 0 =
Some (IMG_RO_LO, (IMG_RO_HI + 0xfff) / 0x1000 * 0x1000, false).
Proof. vm_compute. reflexivity. Qed.
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
