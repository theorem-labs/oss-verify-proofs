(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgSat.v at 7379c28ff70f; the same witness for
   image B at the lists of lib/AU/RtPgImgB.v's rate_himg_B: image B's loaded segments, its globals table 0xa0a20,
   its five .data.rel.ro tables (image A's at +0x300), its 46 strings, its 45 read-only cells (two more doubles than
   image A), its four tables and its callee entries; the premises are stated over the record's fields, and the
   registered globals' addressable ranges are added. *)
(* Image B's witnesses for the memory premises of reac-pw/fuzz_rate's callee contracts (lib/A/RtPgCSpec.v) and for
   the image-level lists of its record (lib/AU/RtPgImgB.v rate_himg_B). At the pinned image, one concrete pair
   (H_w, mem_w) satisfies every string premise (RtPgBase.rt_cstr), the read-only constant premise (rt_ro_cells), the
   two 4-byte tables (rt_i32tab: closed_list and reac_rate_drivable_csv.ordered), the two 8-byte tables (rt_u64tab:
   switch.table.check_code and reac_rate_refuse_code.codes) and the addressable range of every one of the 57
   registered globals, at the image's measured addresses, so those premises are not vacuous on image B; each callee
   entry holds its measured first instruction, which ties the contracts' addresses to the image. Every address,
   byte and descriptor field below is checked against the image's loaded segments by computation.
   Pinned image: fuzz_rate.asan-ubsan, sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14 (the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1 holds the same bytes here).
   proves no function (kind: statement text) *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YP09 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0f YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Rate RateCfg.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgImgB.
From OSSVerify.reac_pw.fuzz_rate.images Require AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* Image B: the loaded segments elf-snapshot makes of the pinned fuzz_rate.asan-ubsan. *)
Definition segsB : list Segment := AsanUbsan.M.loaded_segments.

(* ================================ boolean checkers and their soundness ================================ *)
Definition oz_eqb (o : option Z) (v : Z) : bool := match o with Some z => z =? v | None => false end.
Lemma oz_eqb_ok : forall o v, oz_eqb o v = true -> o = Some v.
Proof. intros [z|] v H; cbn [oz_eqb] in H; [apply Z.eqb_eq in H; subst z; reflexivity | discriminate H]. Qed.

Definition is_someb {A : Type} (o : option A) : bool := match o with Some _ => true | None => false end.
Lemma is_someb_ok : forall (A : Type) (o : option A), is_someb o = true -> o <> None.
Proof. intros A [x|] H; cbn [is_someb] in H; [discriminate | discriminate H]. Qed.

Lemma forallb_seq : forall (f : nat -> bool) (n : nat), forallb f (seq 0 n) = true ->
  forall k, (k < n)%nat -> f k = true.
Proof. intros f n H k Hk. rewrite forallb_forall in H. apply H. apply in_seq. lia. Qed.

(* The bytes l at a, read by rd. *)
Definition bytes_chk (rd : reader) (a : Z) (l : list Z) : bool :=
  forallb (fun k => oz_eqb (rd (a + Z.of_nat k)) (nth k l 0)) (seq 0 (length l)).
Lemma bytes_chk_ok : forall rd a l, bytes_chk rd a l = true ->
  forall i, 0 <= i < Z.of_nat (length l) -> rd (a + i) = Some (nth (Z.to_nat i) l 0).
Proof.
intros rd a l Hc i Hi. unfold bytes_chk in Hc. assert (Hk : (Z.to_nat i < length l)%nat) by lia.
pose proof (forallb_seq _ _ Hc _ Hk) as E. cbv beta in E. rewrite Z2Nat.id in E by lia.
exact (oz_eqb_ok _ _ E).
Qed.

Lemma bytes_range_ok : forall l, forallb (fun b => (0 <? b) && (b <? 256)) l = true -> Forall (fun b => 0 < b < 256) l.
Proof.
intros l H. apply Forall_forall. intros b Hb. cbv beta. rewrite forallb_forall in H. specialize (H b Hb). cbv beta in H.
apply andb_prop in H. destruct H as [H1 H2]. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. lia.
Qed.

(* a lies in a loaded segment (YG0d.in_img). *)
Definition in_imgb (segs : list Segment) (a : Z) : bool :=
  existsb (fun sg => (Z.of_N (seg_base sg) <=? a) && (a <? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) segs.
Lemma in_imgb_ok : forall segs a, in_imgb segs a = true -> in_img segs a.
Proof.
intros segs a H. unfold in_imgb in H. apply existsb_exists in H. destruct H as (sg & Hin & Hb). cbv beta in Hb.
apply andb_prop in Hb. destruct Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
unfold in_img. exists sg. split; [exact Hin | lia].
Qed.
Definition img_chk (segs : list Segment) (a : Z) (n : nat) : bool :=
  forallb (fun k => in_imgb segs (a + Z.of_nat k)) (seq 0 n).
Lemma img_chk_ok : forall segs a n, img_chk segs a n = true -> forall i, 0 <= i < Z.of_nat n -> in_img segs (a + i).
Proof.
intros segs a n Hc i Hi. unfold img_chk in Hc. assert (Hk : (Z.to_nat i < n)%nat) by lia.
pose proof (forallb_seq _ _ Hc _ Hk) as E. cbv beta in E. rewrite Z2Nat.id in E by lia.
exact (in_imgb_ok _ _ E).
Qed.

Definition amem_rangeb (p n : Z) : bool :=
  (p + n <=? kLowMemEnd - 1) || ((kHighMemBeg <=? p) && (p + n <=? kHighMemEnd - 1)).
Lemma amem_rangeb_ok : forall p n, amem_rangeb p n = true -> amem_range p n.
Proof.
intros p n H. unfold amem_rangeb in H. unfold amem_range. apply orb_true_iff in H.
destruct H as [H|H]; [left; apply Z.leb_le; exact H|].
right. apply andb_prop in H. destruct H as [H1 H2]. split; [apply Z.leb_le; exact H1 | apply Z.leb_le; exact H2].
Qed.

(* YG0v.range_addressable over the n bytes at a. *)
Definition saddr_okb (x s : Z) : bool := (s =? 0) || ((x mod 8 <? s) && (s <? 8)).
Lemma saddr_okb_ok : forall x s, saddr_okb x s = true -> saddr_ok x s.
Proof.
intros x s H. unfold saddr_okb in H. unfold saddr_ok. apply orb_true_iff in H.
destruct H as [H|H]; [left; apply Z.eqb_eq; exact H|].
right. apply andb_prop in H. destruct H as [H1 H2]. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. split; assumption.
Qed.
Definition ra_chk (rd : reader) (B a : Z) (n : nat) : bool :=
  forallb (fun k => match rd (shadow_of_addr B (a + Z.of_nat k)) with
                    | Some s => saddr_okb (a + Z.of_nat k) s
                    | None => false
                    end) (seq 0 n).
Lemma ra_chk_ok : forall rd B a n len, Z.of_nat n = len -> ra_chk rd B a n = true -> range_addressable rd B a len.
Proof.
intros rd B a n len Hn Hc. unfold range_addressable. intros x Hx. unfold ra_chk in Hc.
assert (Hk : (Z.to_nat (x - a) < n)%nat) by lia.
pose proof (forallb_seq _ _ Hc _ Hk) as E. cbv beta in E. rewrite Z2Nat.id in E by lia.
replace (a + (x - a)) with x in E by ring.
revert E. destruct (rd (shadow_of_addr B x)) as [v|]; cbv beta iota; intros E; [|discriminate E].
exists v. split; [reflexivity | exact (saddr_okb_ok _ _ E)].
Qed.
(* range_addressable over a list of (start, length) ranges, each start moved by f. *)
Definition ranges_chk (rd : reader) (f : Z -> Z) (l : list (Z * Z)) : bool :=
  forallb (fun g => (0 <=? snd g) && ra_chk rd SHADOW_OFF (f (fst g)) (Z.to_nat (snd g))) l.
Lemma ranges_chk_ok : forall rd f l, ranges_chk rd f l = true ->
  Forall (fun g => range_addressable rd SHADOW_OFF (f (fst g)) (snd g)) l.
Proof.
intros rd f l H. apply Forall_forall. intros g Hg. cbv beta. unfold ranges_chk in H. rewrite forallb_forall in H.
specialize (H g Hg). cbv beta in H. apply andb_prop in H. destruct H as [H1 H2]. apply Z.leb_le in H1.
apply (ra_chk_ok _ _ _ (Z.to_nat (snd g))); [apply Z2Nat.id; exact H1 | exact H2].
Qed.

(* YG0d.shadow_hull_vis: every shadow byte of the 8-aligned hull of the shadow of [x, x + n) is readable. *)
Definition hull_chk (rd : reader) (x n : Z) : bool :=
  forallb (fun k => is_someb (rd (shadow_addr x / 8 * 8 + Z.of_nat k)))
    (seq 0 (Z.to_nat (shadow_addr (x + n - 1) / 8 * 8 + 8 - shadow_addr x / 8 * 8))).
Lemma hull_chk_ok : forall rd x n, hull_chk rd x n = true -> shadow_hull_vis rd x n.
Proof.
intros rd x n Hc. unfold shadow_hull_vis. intros s Hs. unfold hull_chk in Hc.
set (lo := shadow_addr x / 8 * 8) in *. set (hi := shadow_addr (x + n - 1) / 8 * 8 + 8) in *.
assert (Hk : (Z.to_nat (s - lo) < Z.to_nat (hi - lo))%nat) by lia.
pose proof (forallb_seq _ _ Hc _ Hk) as E. cbv beta in E. rewrite Z2Nat.id in E by lia.
replace (lo + (s - lo)) with s in E by ring.
exact (is_someb_ok _ _ E).
Qed.

(* RtPgBase.rt_cstr, conjunct by conjunct. *)
Definition cstr_chk (segs : list Segment) (h : word -> bool) (mem : word -> option byte) (a : Z) (s : list Z) : bool :=
  bytes_chk (aview segs h mem) a s &&
  oz_eqb (aview segs h mem (a + Z.of_nat (length s))) 0 &&
  forallb (fun b => (0 <? b) && (b <? 256)) s &&
  (0 <? a) && (a + Z.of_nat (length s) + 1 <=? 2 ^ 63) &&
  img_chk segs a (S (length s)) &&
  amem_rangeb a (Z.of_nat (length s) + 1) &&
  ra_chk (aview segs h mem) SHADOW_OFF a (S (length s)) &&
  hull_chk (aview segs h mem) a (Z.of_nat (length s) + 1).
Lemma cstr_chk_ok : forall segs h mem a s, cstr_chk segs h mem a s = true -> rt_cstr segs h mem a s.
Proof.
intros segs h mem a s Hc. unfold cstr_chk in Hc. rewrite !andb_true_iff in Hc.
destruct Hc as [[[[[[[[C1 C2] C3] C4] C5] C6] C7] C8] C9].
unfold rt_cstr.
split; [exact (bytes_chk_ok _ _ _ C1)|].
split; [exact (oz_eqb_ok _ _ C2)|].
split; [exact (bytes_range_ok _ C3)|].
split; [apply Z.ltb_lt; exact C4|].
split; [apply Z.leb_le; exact C5|].
split; [intros i Hi; apply (img_chk_ok _ _ _ C6); lia|].
split; [exact (amem_rangeb_ok _ _ C7)|].
split; [apply (ra_chk_ok _ _ _ (S (length s))); [lia | exact C8]|].
exact (hull_chk_ok _ _ _ C9).
Qed.

(* YI04.val_mem: the n little-endian bytes of v at a, read through mbyte (mem first, then the image). *)
Definition val_chk (segs : list Segment) (mem : word -> option byte) (a : Z) (n : nat) (v : Z) : bool :=
  forallb (fun k => oz_eqb (option_map (fun b : byte => bv_unsigned b) (mbyte segs mem (a + Z.of_nat k)))
                      (YO0f.le_byte v n k))
    (seq 0 n).
Lemma val_chk_ok : forall segs mem a n v, val_chk segs mem a n v = true -> val_mem segs mem a n v.
Proof.
intros segs mem a n v Hc. unfold val_mem. intros k Hk. unfold val_chk in Hc.
pose proof (forallb_seq _ _ Hc _ Hk) as E. cbv beta in E. apply oz_eqb_ok in E.
revert E. destruct (mbyte segs mem (a + Z.of_nat k)) as [b|]; cbn [option_map]; intros E; [|discriminate E].
injection E as E. rewrite <- E, Z_to_bv_bv_unsigned. reflexivity.
Qed.
Definition cells_chk (segs : list Segment) (mem : word -> option byte) (cs : list (Z * Z)) : bool :=
  forallb (fun c => val_chk segs mem (fst c) 8 (snd c)) cs.
Lemma cells_chk_ok : forall segs mem cs, cells_chk segs mem cs = true ->
  Forall (fun c => val_mem segs mem (fst c) 8 (snd c)) cs.
Proof.
intros segs mem cs H. apply Forall_forall. intros c Hc. cbv beta. unfold cells_chk in H. rewrite forallb_forall in H.
apply val_chk_ok. exact (H c Hc).
Qed.

(* Image-only reads (seg_rom, no memory). *)
Definition img_byte (segs : list Segment) (a : Z) : option Z :=
  option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a)).
Definition img_val_chk (segs : list Segment) (a : Z) (n : nat) (v : Z) : bool :=
  forallb (fun k => oz_eqb (img_byte segs (a + Z.of_nat k)) (YO0f.le_byte v n k)) (seq 0 n).
Lemma img_val_chk_ok : forall segs a n v, img_val_chk segs a n v = true ->
  forall k, (k < n)%nat -> seg_rom segs (Z_to_bv 64 (a + Z.of_nat k)) = Some (Z_to_bv 8 (YO0f.le_byte v n k)).
Proof.
intros segs a n v Hc k Hk. unfold img_val_chk in Hc.
pose proof (forallb_seq _ _ Hc _ Hk) as E. cbv beta in E. apply oz_eqb_ok in E. unfold img_byte in E.
revert E. destruct (seg_rom segs (Z_to_bv 64 (a + Z.of_nat k))) as [b|]; cbn [option_map]; intros E;
  [|discriminate E].
injection E as E. rewrite <- E, Z_to_bv_bv_unsigned. reflexivity.
Qed.
Definition img_bytes_chk (segs : list Segment) (a : Z) (l : list Z) : bool :=
  forallb (fun k => oz_eqb (img_byte segs (a + Z.of_nat k)) (nth k l 0)) (seq 0 (length l)).
(* (address, 4-byte word) pairs. *)
Definition entries_chk (segs : list Segment) (l : list (Z * Z)) : bool :=
  forallb (fun e => img_val_chk segs (fst e) 4 (snd e)) l.
(* (address, 8-byte value) pairs. *)
Definition img_cells_chk (segs : list Segment) (cs : list (Z * Z)) : bool :=
  forallb (fun c => img_val_chk segs (fst c) 8 (snd c)) cs.

(* rt_i32tab and rt_u64tab, conjunct by conjunct. *)
Definition i32tab_chk (segs : list Segment) (h : word -> bool) (mem : word -> option byte) (t : Z) (vs : list Z) : bool :=
  img_chk segs t (4 * length vs) && (t mod 4 =? 0) &&
  forallb (fun k => val_chk segs (mrestrict h mem) (t + 4 * Z.of_nat k) 4 (nth k vs 0)) (seq 0 (length vs)) &&
  ra_chk (aview segs h mem) SHADOW_OFF t (4 * length vs).
Lemma i32tab_chk_ok : forall segs h mem t vs, i32tab_chk segs h mem t vs = true -> rt_i32tab segs h mem t vs.
Proof.
intros segs h mem t vs Hc. unfold i32tab_chk in Hc. rewrite !andb_true_iff in Hc.
destruct Hc as [[[C1 C2] C3] C4]. unfold rt_i32tab.
split; [intros i Hi; apply (img_chk_ok _ _ _ C1); lia|].
split; [apply Z.eqb_eq; exact C2|].
split.
- intros i Hi. assert (Hk : (Z.to_nat i < length vs)%nat) by lia.
  pose proof (forallb_seq _ _ C3 _ Hk) as E. cbv beta in E. rewrite Z2Nat.id in E by lia.
  apply val_chk_ok. exact E.
- apply (ra_chk_ok _ _ _ (4 * length vs)); [lia | exact C4].
Qed.
Definition u64tab_chk (segs : list Segment) (h : word -> bool) (mem : word -> option byte) (t : Z) (vs : list Z) : bool :=
  img_chk segs t (8 * length vs) && (t mod 8 =? 0) &&
  forallb (fun v => (0 <=? v) && (v <? 2 ^ 64)) vs &&
  forallb (fun k => val_chk segs (mrestrict h mem) (t + 8 * Z.of_nat k) 8 (nth k vs 0)) (seq 0 (length vs)) &&
  ra_chk (aview segs h mem) SHADOW_OFF t (8 * length vs).
Lemma u64tab_chk_ok : forall segs h mem t vs, u64tab_chk segs h mem t vs = true -> rt_u64tab segs h mem t vs.
Proof.
intros segs h mem t vs Hc. unfold u64tab_chk in Hc. rewrite !andb_true_iff in Hc.
destruct Hc as [[[[C1 C2] C3] C4] C5]. unfold rt_u64tab.
split; [intros i Hi; apply (img_chk_ok _ _ _ C1); lia|].
split; [apply Z.eqb_eq; exact C2|].
split.
- apply Forall_forall. intros v Hv. cbv beta. rewrite forallb_forall in C3. specialize (C3 v Hv). cbv beta in C3.
  apply andb_prop in C3 as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
- split.
  + intros i Hi. assert (Hk : (Z.to_nat i < length vs)%nat) by lia.
    pose proof (forallb_seq _ _ C4 _ Hk) as E. cbv beta in E. rewrite Z2Nat.id in E by lia.
    apply val_chk_ok. exact E.
  + apply (ra_chk_ok _ _ _ (8 * length vs)); [lia | exact C5].
Qed.

(* ======================================== the measured image facts ======================================== *)
(* 1. Callee entries (address, first instruction word, little-endian 4 bytes), in this order: check_absent,
   check_rate, check_malformed, check_decide, check_code, check_list, check_csv, pod_write_ent (image B only),
   pod_nearest, reac_rate_refuse_code, reac_rate_is_closed, reac_rate_bit, reac_rate_best_drivable,
   reac_rate_drivable_csv, reac_rate_cfg_decide, reac_rate_prop_parse. *)
Definition rate_B_entries : list (Z * Z) :=
  [(0x83558, 0xff010113); (0x83588, 0xff010113); (0x835b4, 0xff010113); (0x835e8, 0xff010113);
   (0x8360c, 0xff010113); (0x83684, 0xff010113); (0x837c0, 0xf4010113); (0x83cc4, 0xfd010113);
   (0x83fcc, 0xfc010113); (0x841b4, 0xff010113); (0x84220, 0x0000b5b7); (0x84254, 0x0000b5b7);
   (0x84298, 0x00457593); (0x842d8, 0xf2010113); (0x846f8, 0x00100693); (0x8474c, 0xfa010113)].
Lemma rate_B_entries_chk : entries_chk segsB rate_B_entries = true.
Proof. vm_compute. reflexivity. Qed.

(* 2. The registered globals: (descriptor address, (beg, size, size_with_redzone)). The descriptor table
   asan_globals is [AG_START, AG_STOP), 57 descriptors of 64 bytes (beg, size, size_with_redzone, name, module,
   has_dynamic_init, location, odr_indicator, each 8 bytes LE; every odr_indicator is -1). *)
Definition AG_START : Z := 0xa0a20.
Definition AG_STOP : Z := 0xa1860.
Definition rate_B_globals : list (Z * (Z * Z * Z)) := [
  (0xa0a20, (0x20fa0, 14, 32)); (0xa0a60, (0x20fc0, 14, 32)); (0xa0aa0, (0x20fe0, 14, 32));
  (0xa0ae0, (0x21000, 15, 32)); (0xa0b20, (0x21020, 14, 32)); (0xa0b60, (0x21040, 19, 64));
  (0xa0ba0, (0x21080, 13, 32)); (0xa0be0, (0x210a0, 16, 32)); (0xa0c20, (0x210c0, 13, 32));
  (0xa0c60, (0x210e0, 56, 96)); (0xa0ca0, (0x21140, 84, 128)); (0xa0ce0, (0x211c0, 16, 32));
  (0xa0d20, (0x211e0, 16, 32)); (0xa0d60, (0x21200, 14, 32)); (0xa0da0, (0x21220, 3, 32));
  (0xa0de0, (0x21240, 3, 32)); (0xa0e20, (0x21260, 3, 32)); (0xa0e60, (0x21280, 3, 32));
  (0xa0ea0, (0x212a0, 21, 64)); (0xa0ee0, (0x212e0, 1, 32)); (0xa0f20, (0x21300, 2, 32));
  (0xa0f60, (0x21320, 3, 32)); (0xa0fa0, (0x21340, 3, 32)); (0xa0fe0, (0x21360, 3, 32));
  (0xa1020, (0x21380, 3, 32)); (0xa1060, (0x213a0, 3, 32)); (0xa10a0, (0x213c0, 4, 32));
  (0xa10e0, (0x213e0, 22, 64)); (0xa1120, (0x21420, 8, 32)); (0xa1160, (0x21440, 4, 32));
  (0xa11a0, (0x21460, 5, 32)); (0xa11e0, (0x21480, 4, 32)); (0xa1220, (0x214a0, 6, 32));
  (0xa1260, (0x214c0, 10, 32)); (0xa12a0, (0x214e0, 6, 32)); (0xa12e0, (0x21500, 2, 32));
  (0xa1320, (0x21520, 12, 32)); (0xa1360, (0x21540, 11, 32)); (0xa13a0, (0x21560, 13, 32));
  (0xa13e0, (0x21580, 11, 32)); (0xa1420, (0x215a0, 10, 32)); (0xa1460, (0x215c0, 5, 32));
  (0xa14a0, (0x21600, 5, 32)); (0xa14e0, (0x21620, 11, 32)); (0xa1520, (0x21640, 13, 32));
  (0xa1560, (0x21660, 11, 32)); (0xa15a0, (0x21680, 10, 32)); (0xa15e0, (0x216a0, 12, 32));
  (0xa1620, (0x216c0, 5, 32)); (0xa1660, (0x216e0, 2, 32)); (0xa16a0, (0x21700, 1, 32));
  (0xa16e0, (0x21720, 14, 32)); (0xa1720, (0x9bdc0, 72, 128)); (0xa1760, (0x9be40, 112, 160));
  (0xa17a0, (0x9bee0, 64, 96)); (0xa17e0, (0x9bf40, 32, 64)); (0xa1820, (0x9bf80, 40, 96))
].
Definition global_chk (segs : list Segment) (e : Z * (Z * Z * Z)) : bool :=
  let '(d, (beg, n, r)) := e in
  (AG_START <=? d) && (d + 64 <=? AG_STOP) && ((d - AG_START) mod 64 =? 0) &&
  img_val_chk segs d 8 beg && img_val_chk segs (d + 8) 8 n && img_val_chk segs (d + 16) 8 r &&
  (beg mod 8 =? 0) && (0 <? n) && (n <=? r).
Definition globals_chk (segs : list Segment) (l : list (Z * (Z * Z * Z))) : bool := forallb (global_chk segs) l.
Lemma rate_B_globals_chk :
  globals_chk segsB rate_B_globals &&
  forallb (fun k => fst (nth k rate_B_globals (0, (0, 0, 0))) =? AG_START + 64 * Z.of_nat k) (seq 0 57) &&
  (Z.of_nat (length rate_B_globals) =? (AG_STOP - AG_START) / 64) = true.
Proof. vm_compute. reflexivity. Qed.
(* They are the rows of hi_globs (address, size). *)
Lemma rate_B_globals_globs :
  map (fun g => let '(_, (b, n, _)) := g in (b, n)) rate_B_globals = hi_globs rate_himg_B.
Proof. vm_compute. reflexivity. Qed.
(* The table is the one the runtime registers: asan.module_ctor (0x8414c) loads a1 and a2 from the cells 0x9cde8 and
   0x9cdf0 (auipc a0, 0x19 at 0x8415c; auipc a2, 0x19 at 0x84160; ld a1, -884(a0); ld a2, -880(a2)) and calls
   __asan_register_elf_globals at 0x40128 (jal at 0x84174); the two cells hold AG_START and AG_STOP. *)
Definition rate_B_reg_words : list (Z * Z) :=
  [(0x8415c, 0x00019517); (0x84160, 0x00019617); (0x84164, 0xc8c53583); (0x84168, 0xc9063603);
   (0x84174, 0xfb5bb0ef)].
Definition rate_B_reg_cells : list (Z * Z) := [(0x9cde8, AG_START); (0x9cdf0, AG_STOP)].
Lemma rate_B_reg_chk :
  entries_chk segsB rate_B_reg_words && img_cells_chk segsB rate_B_reg_cells && (AG_STOP - AG_START =? 57 * 64) = true.
Proof. vm_compute. reflexivity. Qed.

(* 3. The strings the string-comparing callee contracts name: check_code's four table targets and its own literal
   "none"; reac_rate_refuse_code's five codes; reac_rate_prop_parse's key and the harness's own key;
   reac_rate_drivable_csv's format and its two separators. Each is followed by a NUL in the image and is the
   registered global with beg = the address and size = length + 1. *)
Definition rate_B_cstrs : list (Z * list Z) :=
  [(0x21540, rt_code_of_txt 1); (0x21560, rt_code_of_txt 2); (0x21580, rt_code_of_txt 3);
   (0x215a0, rt_code_of_txt 4); (0x215c0, rt_code_of_txt 0);
   (0x21600, rt_refuse_txt 0); (0x21620, rt_refuse_txt 1); (0x21640, rt_refuse_txt 2);
   (0x21660, rt_refuse_txt 3); (0x21680, rt_refuse_txt 4);
   (0x21720, map (fun x : byte => bv_unsigned x) Rate.RATE_KEY);
   (0x20fa0, map (fun x : byte => bv_unsigned x) Rate.RATE_KEY);
   (0x216c0, STR_FMT_SD); (0x216e0, STR_COMMA); (0x21700, STR_EMPTY)].
Definition cstrs_img_chk (segs : list Segment) (gs : list (Z * (Z * Z * Z))) (l : list (Z * list Z)) : bool :=
  forallb (fun c => img_bytes_chk segs (fst c) (snd c ++ [0]) &&
    existsb (fun g => let '(_, (beg, n, _)) := g in (beg =? fst c) && (n =? Z.of_nat (length (snd c)) + 1)) gs) l.
Lemma rate_B_cstrs_chk : cstrs_img_chk segsB rate_B_globals rate_B_cstrs = true.
Proof. vm_compute. reflexivity. Qed.
(* Every string of the record is in the image with its NUL and is the registered global of its address; the
   descriptors' ranges [beg, beg + size_with_redzone) are ascending and apart, so each granule has at most one
   global's shadow byte. *)
Definition gdummy : Z * (Z * Z * Z) := (0, (0, 0, 0)).
Lemma rate_B_globals_apart :
  forallb (fun k => let '(_, (b1, _, r1)) := nth k rate_B_globals gdummy in
                    let '(_, (b2, _, _)) := nth (S k) rate_B_globals gdummy in b1 + r1 <=? b2) (seq 0 56) &&
  cstrs_img_chk segsB rate_B_globals (hi_strs rate_himg_B) = true.
Proof. vm_compute. reflexivity. Qed.

(* 4. reac_rate_prop_parse's read-only doubles (0.5, -2^31, 2^31, and image B's two further bounds). *)
Definition dcs_B : list (Z * Z) :=
  [(0x10388, 0x3fe0000000000000); (0x103f0, 0xc1e0000000000000); (0x10338, 0x41e0000000000000);
   (0x10400, 0xc3e0000000000001); (0x10360, 0x43e0000000000000)].
Lemma dcs_B_chk : img_cells_chk segsB dcs_B = true.
Proof. vm_compute. reflexivity. Qed.

(* 5. The tables: closed_list (0x21520) and reac_rate_drivable_csv.ordered (0x216a0), each the three closed rates as
   4-byte values; switch.table.check_code (0x9bf40, four code_of targets) and reac_rate_refuse_code.codes (0x9bf80,
   five codes targets), each 8-byte pointers in .data.rel.ro. *)
Definition TBL_CLOSED : Z := 0x21520.
Definition TBL_ORDERED : Z := 0x216a0.
Definition TBL_SWITCH : Z := 0x9bf40.
Definition TBL_CODES : Z := 0x9bf80.
Definition rate_B_switch : list Z := [0x21540; 0x21560; 0x21580; 0x215a0].
Definition rate_B_codes : list Z := [0x21600; 0x21620; 0x21640; 0x21660; 0x21680].
Definition CODE_COV : Z := 0x21600.
Definition STR_NONE_CC : Z := 0x215c0.
Definition AKEY_PARSE : Z := 0x21720.
Definition AKEY_HARNESS : Z := 0x20fa0.
Definition AFMT : Z := 0x216c0.
Definition ACOMMA : Z := 0x216e0.
Definition AEMPTY : Z := 0x21700.

(* ================================================ the witness ================================================ *)
(* No byte hidden. *)
Definition H_w : word -> bool := fun _ => false.
(* The shadow byte of the granule at g (g mod 8 = 0) of the global (beg, n, _), beg mod 8 = 0: 0 for a full granule,
   n mod 8 for the last partial one (the runtime's default poison_partial = 1), 0xf9 (the runtime's global-redzone
   magic) for a redzone one. *)
Definition gshadow (beg n g : Z) : Z := if g + 8 <=? beg + n then 0 else if g <? beg + n then n mod 8 else 0xf9.
(* The shadow byte of the granule at g: from the listed global whose [beg, beg + size_with_redzone) holds g, else 0. *)
Definition granule_shadow (gs : list (Z * (Z * Z * Z))) (g : Z) : Z :=
  match find (fun e => let '(_, (beg, _, r)) := e in (beg <=? g) && (g <? beg + r)) gs with
  | Some (_, (beg, n, _)) => gshadow beg n g
  | None => 0
  end.
(* The application spans whose shadow mem_w holds: the .rodata globals of the strings and the two 4-byte tables
   (0x20fa0 .. 0x21740) and the .data.rel.ro span of the five pointer tables (0x9bdc0 .. 0x9c000). mem_w holds the
   byte granule_shadow gives for each granule of a span, which is what the runtime writes when it registers the
   globals of rate_B_globals. The parts of a span that no global covers, [0x20f80, 0x20fa0) and [0x215e0, 0x21600)
   (before the first registered global, and after the last fuzz_rate.c string's redzone before the next unit's
   .str) and [0x9bfe0, 0x9c000), the runtime never writes: their shadow bytes keep the 0 of the freshly mapped
   shadow, which the 8-byte-aligned shadow hulls rt_cstr reads at the ends of the span need. Every other address
   reads None, so each program byte (string, constant, table) comes from the image through mbyte's fall-back to
   seg_rom. The span bounds are 64-aligned, so a shadow hull of a string inside them is inside the span. *)
Definition shadow_spans : list (Z * Z) := [(0x20f80, 0x21740); (0x9bdc0, 0x9c000)].
Definition mem_w : word -> option byte := fun w =>
  if existsb (fun r => (SHADOW_OFF + fst r / 8 <=? bv_unsigned w) && (bv_unsigned w <? SHADOW_OFF + snd r / 8))
       shadow_spans
  then Some (Z_to_bv 8 (granule_shadow rate_B_globals ((bv_unsigned w - SHADOW_OFF) * 8)))
  else None.

(* W1. Every string of rate_B_cstrs satisfies rt_cstr at (H_w, mem_w). *)
Definition cstrs_wit_chk (l : list (Z * list Z)) : bool :=
  forallb (fun c => cstr_chk segsB H_w mem_w (fst c) (snd c)) l.
Lemma rt_cstr_B_chk : cstrs_wit_chk rate_B_cstrs = true.
Proof. vm_compute. reflexivity. Qed.
Lemma rt_cstr_B : forall a s, In (a, s) rate_B_cstrs -> rt_cstr segsB H_w mem_w a s.
Proof.
intros a s Hin. apply cstr_chk_ok.
pose proof rt_cstr_B_chk as E. unfold cstrs_wit_chk in E. rewrite forallb_forall in E.
exact (E (a, s) Hin).
Qed.
Print Assumptions rt_cstr_B.
(* A control: without the shadow bytes the checker refuses the first string (its shadow reads None). *)
Lemma rt_cstr_B_control : cstr_chk segsB H_w (fun _ => None) 0x21540 (rt_code_of_txt 1) = false.
Proof. vm_compute. reflexivity. Qed.

(* W2. reac_rate_prop_parse's read-only doubles. *)
Lemma rt_ro_cells_B : rt_ro_cells segsB H_w mem_w dcs_B.
Proof. unfold rt_ro_cells. apply cells_chk_ok. vm_compute. reflexivity. Qed.
Print Assumptions rt_ro_cells_B.

(* W3. The four tables: closed_list and ordered as rt_i32tab over RateCfg.closed_list; the switch table and the
   codes table as rt_u64tab. *)
Lemma rt_tabs_B :
  rt_i32tab segsB H_w mem_w TBL_CLOSED RateCfg.closed_list /\
  rt_i32tab segsB H_w mem_w TBL_ORDERED RateCfg.closed_list /\
  rt_u64tab segsB H_w mem_w TBL_SWITCH rate_B_switch /\
  rt_u64tab segsB H_w mem_w TBL_CODES rate_B_codes.
Proof.
split; [apply i32tab_chk_ok; vm_compute; reflexivity|].
split; [apply i32tab_chk_ok; vm_compute; reflexivity|].
split; apply u64tab_chk_ok; vm_compute; reflexivity.
Qed.
Print Assumptions rt_tabs_B.

(* W4. Each callee entry holds its measured first instruction word in the image. *)
Lemma rt_entries_B : forall a w, In (a, w) rate_B_entries ->
  forall k, (k < 4)%nat -> seg_rom segsB (Z_to_bv 64 (a + Z.of_nat k)) = Some (Z_to_bv 8 (YO0f.le_byte w 4 k)).
Proof.
intros a w Hin k Hk. refine (img_val_chk_ok segsB a 4 w _ k Hk).
pose proof rate_B_entries_chk as E. unfold entries_chk in E. rewrite forallb_forall in E.
exact (E (a, w) Hin).
Qed.
Print Assumptions rt_entries_B.

(* W5. The premises of the string-comparing callee contracts at image B's literals, in the order the contracts state
   them: rt_check_code_specX at tbl = TBL_SWITCH, lnone = STR_NONE_CC and the four table targets (its last two
   premises), with the compared string s = codes[r] for any r <= 4 (what reac_rate_refuse_code returns);
   rt_parse_specX at akey = AKEY_PARSE; the harness's own key at AKEY_HARNESS; rt_drivable_csv_specX's format and
   separators. *)
Lemma rt_cstr_B_at : forall n a s, nth_error rate_B_cstrs n = Some (a, s) -> rt_cstr segsB H_w mem_w a s.
Proof. intros n a s E. apply rt_cstr_B. eapply nth_error_In. exact E. Qed.
Lemma rt_sat_strs_B :
  (forall i, 0 <= i < 4 -> rt_cstr segsB H_w mem_w (nth (Z.to_nat i) rate_B_switch 0) (rt_code_of_txt (i + 1))) /\
  rt_cstr segsB H_w mem_w STR_NONE_CC (rt_code_of_txt 0) /\
  (forall r, 0 <= r <= 4 ->
     rt_cstr segsB H_w mem_w (rt_refuse rate_B_codes CODE_COV r) (rt_refuse_txt r)) /\
  rt_cstr segsB H_w mem_w AKEY_PARSE (map (fun x : byte => bv_unsigned x) Rate.RATE_KEY) /\
  rt_cstr segsB H_w mem_w AKEY_HARNESS (map (fun x : byte => bv_unsigned x) Rate.RATE_KEY) /\
  rt_cstr segsB H_w mem_w AFMT STR_FMT_SD /\
  rt_cstr segsB H_w mem_w ACOMMA STR_COMMA /\
  rt_cstr segsB H_w mem_w AEMPTY STR_EMPTY.
Proof.
split.
{ intros i Hi. assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3) as C by lia.
  destruct C as [->|[->|[->| ->]]];
    [apply (rt_cstr_B_at 0) | apply (rt_cstr_B_at 1) | apply (rt_cstr_B_at 2) | apply (rt_cstr_B_at 3)];
    reflexivity. }
split; [apply (rt_cstr_B_at 4); reflexivity|].
split.
{ intros r Hr. assert (r = 0 \/ r = 1 \/ r = 2 \/ r = 3 \/ r = 4) as C by lia.
  destruct C as [->|[->|[->|[->| ->]]]]; unfold rt_refuse; cbn [Z.leb Z.to_nat nth rate_B_codes];
    [apply (rt_cstr_B_at 5) | apply (rt_cstr_B_at 6) | apply (rt_cstr_B_at 7) | apply (rt_cstr_B_at 8)
    | apply (rt_cstr_B_at 9)]; reflexivity. }
split; [apply (rt_cstr_B_at 10); reflexivity|].
split; [apply (rt_cstr_B_at 11); reflexivity|].
split; [apply (rt_cstr_B_at 12); reflexivity|].
split; [apply (rt_cstr_B_at 13); reflexivity | apply (rt_cstr_B_at 14); reflexivity].
Qed.
Print Assumptions rt_sat_strs_B.

(* ============================= the record's own image-level lists at the witness =============================
   The lists rate_himg_B carries into rt_seg_pre -- the 57 registered globals' addressable ranges, the 46 strings,
   the 45 read-only cells and the four tables -- hold together at one state, so no one of them is vacuous on image
   B and no two of them contradict each other. *)
Lemma rate_B_globs_chk : ranges_chk (aview segsB H_w mem_w) (fun a => a) (hi_globs rate_himg_B) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma rate_B_globs_sat :
  Forall (fun g => range_addressable (aview segsB H_w mem_w) SHADOW_OFF (fst g) (snd g)) (hi_globs rate_himg_B).
Proof. exact (ranges_chk_ok _ _ _ rate_B_globs_chk). Qed.
Lemma rate_B_strs_sat : Forall (fun s => rt_cstr segsB H_w mem_w (fst s) (snd s)) (hi_strs rate_himg_B).
Proof.
apply Forall_forall. intros c Hc. cbv beta. apply cstr_chk_ok.
assert (E : forallb (fun c => cstr_chk segsB H_w mem_w (fst c) (snd c)) (hi_strs rate_himg_B) = true)
  by (vm_compute; reflexivity).
rewrite forallb_forall in E. exact (E c Hc).
Qed.
Lemma rate_B_cells_sat : rt_ro_cells segsB H_w mem_w (hi_cells rate_himg_B).
Proof. unfold rt_ro_cells. apply cells_chk_ok. vm_compute. reflexivity. Qed.
Lemma rate_B_i32_sat : Forall (fun t => rt_i32tab segsB H_w mem_w (fst t) (snd t)) (hi_i32 rate_himg_B).
Proof.
apply Forall_forall. intros t Ht. cbv beta. apply i32tab_chk_ok.
assert (E : forallb (fun t => i32tab_chk segsB H_w mem_w (fst t) (snd t)) (hi_i32 rate_himg_B) = true)
  by (vm_compute; reflexivity).
rewrite forallb_forall in E. exact (E t Ht).
Qed.
Lemma rate_B_u64_sat : Forall (fun t => rt_u64tab segsB H_w mem_w (fst t) (snd t)) (hi_u64 rate_himg_B).
Proof.
apply Forall_forall. intros t Ht. cbv beta. apply u64tab_chk_ok.
assert (E : forallb (fun t => u64tab_chk segsB H_w mem_w (fst t) (snd t)) (hi_u64 rate_himg_B) = true)
  by (vm_compute; reflexivity).
rewrite forallb_forall in E. exact (E t Ht).
Qed.

Lemma rate_B_record_sat : exists (H : word -> bool) (mem : word -> option byte),
  Forall (fun g => range_addressable (aview segsB H mem) SHADOW_OFF (fst g) (snd g)) (hi_globs rate_himg_B) /\
  Forall (fun s => rt_cstr segsB H mem (fst s) (snd s)) (hi_strs rate_himg_B) /\
  rt_ro_cells segsB H mem (hi_cells rate_himg_B) /\
  Forall (fun t => rt_i32tab segsB H mem (fst t) (snd t)) (hi_i32 rate_himg_B) /\
  Forall (fun t => rt_u64tab segsB H mem (fst t) (snd t)) (hi_u64 rate_himg_B).
Proof.
exists H_w, mem_w.
split; [exact rate_B_globs_sat|].
split; [exact rate_B_strs_sat|].
split; [exact rate_B_cells_sat|].
split; [exact rate_B_i32_sat | exact rate_B_u64_sat].
Qed.
Print Assumptions rate_B_record_sat.
