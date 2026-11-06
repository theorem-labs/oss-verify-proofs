(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgSat.v at 0de5d668c87 for reac-pw/fuzz_headamp
   image A (fuzz_headamp.asan): module paths changed, the rl_ / role_ prefixes renamed to hd_ / headamp_, image A's
   segments read from lib/A/Img0.v (Img0.rsegs, no local copy). Role's boolean checkers and their soundness lemmas
   are taken as they stand; cstr_chk gains the two conjuncts headamp's string predicate HPgBase.hd_cstr adds (the
   len + 8 range and the NUL word's tail, tail_chk). Role's measured facts are replaced by headamp's (ten callee
   entries, the 43 descriptors of asan_globals and the call that registers them, the 36 strings, the 36 cells and the
   two doubles); role's refusal-table witness is left out (headamp's program has no such table); the stack-guard
   witness W3, the guard's eight bytes in the witness memory, and the parse's literal witness W5 are new. *)
(* Image A's witnesses for the memory premises of reac-pw/fuzz_headamp's callee contracts (lib/A/HPgCSpec.v). At the
   pinned image, one concrete pair (H_w, mem_w) satisfies every string premise (HPgBase.hd_cstr), the read-only cell
   premise (HPgBase.hd_ro_cells) and the stack-guard premise (HPgCSpec.hd_guard_ok) at the image's measured
   addresses, and each callee entry holds its measured first instruction, so those contracts are not vacuous on
   image A. Every address, byte and descriptor field below is checked against the image's loaded segments by
   computation.
   Pinned image: fuzz_headamp.asan, sha256 f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47 (symbol
   names from its unstripped twin, sha256 b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a, whose
   loaded sections are byte-equal to the pin's except .note.gnu.build-id).
   proves no function (kind: statement text) *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YP09 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0f YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec HPgImgA.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* ================================ boolean checkers and their soundness ================================ *)
Definition oz_eqb (o : option Z) (v : Z) : bool := match o with Some z => z =? v | None => false end.
Lemma oz_eqb_ok : forall o v, oz_eqb o v = true -> o = Some v.
Proof. intros [z|] v H; cbn [oz_eqb] in H; [apply Z.eqb_eq in H; subst z; reflexivity | discriminate H]. Qed.

Definition is_someb {A : Type} (o : option A) : bool := match o with Some _ => true | None => false end.
Lemma is_someb_ok : forall (A : Type) (o : option A), is_someb o = true -> o <> None.
Proof. intros A [x|] H; cbn [is_someb] in H; [discriminate | discriminate H]. Qed.

Lemma forallb_seq : forall (f : nat -> bool) (n : nat), forallb f (seq 0 n) = true -> forall k, (k < n)%nat -> f k = true.
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
Definition img_chk (segs : list Segment) (a : Z) (n : nat) : bool := forallb (fun k => in_imgb segs (a + Z.of_nat k)) (seq 0 n).
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

(* HPgBase.hd_str_tail: every byte after e up to the end of e's 8-byte word is readable; those are the
   7 - e mod 8 bytes e + 1 .. e + 7 - e mod 8. *)
Definition tail_chk (rd : reader) (e : Z) : bool :=
  forallb (fun k => is_someb (rd (e + 1 + Z.of_nat k))) (seq 0 (Z.to_nat (7 - e mod 8))).
Lemma tail_chk_ok : forall rd e, tail_chk rd e = true -> hd_str_tail rd e.
Proof.
intros rd e Hc a Ha. unfold tail_chk in Hc.
assert (Hm : 0 <= e mod 8 < 8) by (apply Z.mod_pos_bound; lia).
assert (Hk : (Z.to_nat (a - e - 1) < Z.to_nat (7 - e mod 8))%nat) by lia.
pose proof (forallb_seq _ _ Hc _ Hk) as E. cbv beta in E. rewrite Z2Nat.id in E by lia.
replace (e + 1 + (a - e - 1)) with a in E by ring.
exact (is_someb_ok _ _ E).
Qed.

(* HPgBase.hd_cstr, conjunct by conjunct: role's rl_cstr checker with headamp's len + 8 range and the tail. *)
Definition cstr_chk (segs : list Segment) (h : word -> bool) (mem : word -> option byte) (a : Z) (s : list Z) : bool :=
  bytes_chk (aview segs h mem) a s &&
  oz_eqb (aview segs h mem (a + Z.of_nat (length s))) 0 &&
  forallb (fun b => (0 <? b) && (b <? 256)) s &&
  (0 <? a) && (a + Z.of_nat (length s) + 1 <=? 2 ^ 63) &&
  img_chk segs a (S (length s)) &&
  amem_rangeb a (Z.of_nat (length s) + 8) &&
  ra_chk (aview segs h mem) SHADOW_OFF a (S (length s)) &&
  hull_chk (aview segs h mem) a (Z.of_nat (length s) + 1) &&
  tail_chk (aview segs h mem) (a + Z.of_nat (length s)).
Lemma cstr_chk_ok : forall segs h mem a s, cstr_chk segs h mem a s = true -> hd_cstr segs h mem a s.
Proof.
intros segs h mem a s Hc. unfold cstr_chk in Hc. rewrite !andb_true_iff in Hc.
destruct Hc as [[[[[[[[[C1 C2] C3] C4] C5] C6] C7] C8] C9] C10].
unfold hd_cstr.
split; [exact (bytes_chk_ok _ _ _ C1)|].
split; [exact (oz_eqb_ok _ _ C2)|].
split; [exact (bytes_range_ok _ C3)|].
split; [apply Z.ltb_lt; exact C4|].
split; [apply Z.leb_le; exact C5|].
split; [intros i Hi; apply (img_chk_ok _ _ _ C6); lia|].
split; [exact (amem_rangeb_ok _ _ C7)|].
split; [apply (ra_chk_ok _ _ _ (S (length s))); [lia | exact C8]|].
split; [exact (hull_chk_ok _ _ _ C9)|].
exact (tail_chk_ok _ _ C10).
Qed.

(* YI04.val_mem: the n little-endian bytes of v at a, read through mbyte (mem first, then the image). val_mem reads
   them with YO0f.le_byte (YI04's own import), so the checkers below name that constant. *)
Definition val_chk (segs : list Segment) (mem : word -> option byte) (a : Z) (n : nat) (v : Z) : bool :=
  forallb (fun k => oz_eqb (option_map (fun b : byte => bv_unsigned b) (mbyte segs mem (a + Z.of_nat k))) (YO0f.le_byte v n k))
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

(* HPgCSpec.hd_guard_ok: the GOT word reads the guard's address and the guard's word is readable. *)
Definition guard_chk (rd : reader) (gotw guard : Z) : bool := oz_eqb (rdword rd gotw) guard && is_someb (rdword rd guard).
Lemma guard_chk_ok : forall rd gotw guard, guard_chk rd gotw guard = true -> hd_guard_ok rd gotw guard.
Proof.
intros rd gotw guard H. unfold guard_chk in H. apply andb_prop in H. destruct H as [H1 H2].
unfold hd_guard_ok. split; [exact (oz_eqb_ok _ _ H1)|].
revert H2. destruct (rdword rd guard) as [c|]; intros H2; [exists c; reflexivity | cbn [is_someb] in H2; discriminate H2].
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
revert E. destruct (seg_rom segs (Z_to_bv 64 (a + Z.of_nat k))) as [b|]; cbn [option_map]; intros E; [|discriminate E].
injection E as E. rewrite <- E, Z_to_bv_bv_unsigned. reflexivity.
Qed.
Definition img_bytes_chk (segs : list Segment) (a : Z) (l : list Z) : bool :=
  forallb (fun k => oz_eqb (img_byte segs (a + Z.of_nat k)) (nth k l 0)) (seq 0 (length l)).
(* (address, 4-byte word) pairs. *)
Definition entries_chk (segs : list Segment) (l : list (Z * Z)) : bool := forallb (fun e => img_val_chk segs (fst e) 4 (snd e)) l.
(* (address, 8-byte value) pairs. *)
Definition img_cells_chk (segs : list Segment) (cs : list (Z * Z)) : bool := forallb (fun c => img_val_chk segs (fst c) 8 (snd c)) cs.

(* ======================================== the measured image facts ======================================== *)
(* 1. Callee entries (address, first instruction word, little-endian 4 bytes), in this order: check_no_overrun,
   check_count, check_cells_valid, check_object, check_cells, check_keys, check_refusal, check_plain (each
   `addi sp,sp,-0x10`), reac_headamp_prop_parse (`mv a3,zero`), reac_headamp_prop_parse_result
   (`addi sp,sp,-0x100`). Pinned image sha256 f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47. *)
Definition headamp_A_entries : list (Z * Z) :=
  [(0x83e3c, 0xff010113); (0x83ee8, 0xff010113); (0x83f7c, 0xff010113); (0x8405c, 0xff010113);
   (0x84148, 0xff010113); (0x842e8, 0xff010113); (0x84368, 0xff010113); (0x843e8, 0xff010113);
   (0x845ac, 0x00000693); (0x845b4, 0xf0010113)].
Lemma headamp_A_entries_chk : entries_chk Img0.rsegs headamp_A_entries = true.
Proof. vm_compute. reflexivity. Qed.

(* 2. The registered globals: (descriptor address, (beg, size, size_with_redzone)). The descriptor table
   asan_globals is [AG_START, AG_STOP) (its own section, 0xac0 bytes), 43 descriptors of 64 bytes (beg, size,
   size_with_redzone, name, module, has_dynamic_init, location, odr_indicator, each 8 bytes LE; no descriptor has an
   ODR indicator), in table order: the 40 of .rodata, then ent_build.vocab, ent_headamp_key.odd_ch and
   ent_headamp_key.param of .data.rel.ro. Pinned image sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47. *)
Definition AG_START : Z := 0xa0c20.
Definition AG_STOP : Z := 0xa16e0.
Definition headamp_A_globals : list (Z * (Z * Z * Z)) :=
  [(0xa0c20, (0x20ec0, 14, 32)); (0xa0c60, (0x20ee0, 14, 32)); (0xa0ca0, (0x20f00, 14, 32));
   (0xa0ce0, (0x20f20, 15, 32)); (0xa0d20, (0x20f40, 14, 32)); (0xa0d60, (0x20f60, 19, 64));
   (0xa0da0, (0x20fa0, 13, 32)); (0xa0de0, (0x20fc0, 16, 32)); (0xa0e20, (0x20fe0, 13, 32));
   (0xa0e60, (0x21000, 56, 96)); (0xa0ea0, (0x21060, 84, 128)); (0xa0ee0, (0x210e0, 16, 32));
   (0xa0f20, (0x21100, 16, 32)); (0xa0f60, (0x21120, 14, 32)); (0xa0fa0, (0x21140, 3, 32));
   (0xa0fe0, (0x21160, 3, 32)); (0xa1020, (0x21180, 3, 32)); (0xa1060, (0x211a0, 3, 32));
   (0xa10a0, (0x211c0, 21, 64)); (0xa10e0, (0x21200, 1, 32)); (0xa1120, (0x21220, 2, 32));
   (0xa1160, (0x21240, 3, 32)); (0xa11a0, (0x21260, 3, 32)); (0xa11e0, (0x21280, 3, 32));
   (0xa1220, (0x212a0, 3, 32)); (0xa1260, (0x212c0, 3, 32)); (0xa12a0, (0x212e0, 4, 32));
   (0xa12e0, (0x21300, 22, 64)); (0xa1320, (0x21340, 8, 32)); (0xa1360, (0x21360, 4, 32));
   (0xa13a0, (0x21380, 5, 32)); (0xa13e0, (0x213a0, 4, 32)); (0xa1420, (0x213c0, 6, 32));
   (0xa1460, (0x213e0, 10, 32)); (0xa14a0, (0x21400, 6, 32)); (0xa14e0, (0x21420, 2, 32));
   (0xa1520, (0x21460, 14, 32)); (0xa1560, (0x21480, 8, 32)); (0xa15a0, (0x214a0, 4, 32));
   (0xa15e0, (0x214c0, 5, 32)); (0xa1620, (0x9c060, 72, 128)); (0xa1660, (0x9c0e0, 112, 160));
   (0xa16a0, (0x9c180, 64, 96))].
Definition global_chk (segs : list Segment) (e : Z * (Z * Z * Z)) : bool :=
  let '(d, (beg, n, r)) := e in
  (AG_START <=? d) && (d + 64 <=? AG_STOP) && ((d - AG_START) mod 64 =? 0) &&
  img_val_chk segs d 8 beg && img_val_chk segs (d + 8) 8 n && img_val_chk segs (d + 16) 8 r &&
  (beg mod 8 =? 0) && (0 <? n) && (n <=? r).
Definition globals_chk (segs : list Segment) (l : list (Z * (Z * Z * Z))) : bool := forallb (global_chk segs) l.
Definition gdummy : Z * (Z * Z * Z) := (0, (0, 0, 0)).
(* Each row's beg, size and size_with_redzone are the image's; the k-th row is the descriptor at AG_START + 64 k;
   the table holds 43. *)
Lemma headamp_A_globals_chk :
  globals_chk Img0.rsegs headamp_A_globals &&
  forallb (fun k => fst (nth k headamp_A_globals gdummy) =? AG_START + 64 * Z.of_nat k) (seq 0 43) &&
  (Z.of_nat (length headamp_A_globals) =? (AG_STOP - AG_START) / 64) = true.
Proof. vm_compute. reflexivity. Qed.
(* They are the rows of HPgImgA.headamp_A_globs (address, size), the record's hi_globs. *)
Lemma headamp_A_globals_globs :
  map (fun g => let '(_, (b, n, _)) := g in (b, n)) headamp_A_globals = headamp_A_globs /\
  hi_globs headamp_himg_A = headamp_A_globs.
Proof. split; reflexivity. Qed.
(* The table is the one the runtime registers: asan.module_ctor (0x84544) loads a1 and a2 from the cells 0x9cfe8
   and 0x9cff0 (auipc a0, 0x19 at 0x84554; auipc a2, 0x19 at 0x84558; ld a1, -0x56c(a0); ld a2, -0x568(a2)) and
   calls __asan_register_elf_globals at 0x3fad4 (jal at 0x8456c); the two cells hold AG_START and AG_STOP.
   Pinned image sha256 f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47. *)
Definition headamp_A_reg_words : list (Z * Z) :=
  [(0x84554, 0x00019517); (0x84558, 0x00019617); (0x8455c, 0xa9453583); (0x84560, 0xa9863603); (0x8456c, 0xd68bb0ef)].
Definition headamp_A_reg_cells : list (Z * Z) := [(0x9cfe8, AG_START); (0x9cff0, AG_STOP)].
Lemma headamp_A_reg_chk :
  entries_chk Img0.rsegs headamp_A_reg_words && img_cells_chk Img0.rsegs headamp_A_reg_cells &&
  (AG_STOP - AG_START =? 43 * 64) = true.
Proof. vm_compute. reflexivity. Qed.

(* 3. The strings (HPgImgA.headamp_A_strs, address and text): each is followed by a NUL in the image and is the
   registered global of headamp_A_globals with beg = the address and size = length + 1. Pinned image sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47. *)
Definition cstrs_img_chk (segs : list Segment) (gs : list (Z * (Z * Z * Z))) (l : list (Z * list Z)) : bool :=
  forallb (fun c => img_bytes_chk segs (fst c) (snd c ++ [0]) &&
    existsb (fun g => let '(_, (beg, n, _)) := g in (beg =? fst c) && (n =? Z.of_nat (length (snd c)) + 1)) gs) l.
Lemma headamp_A_strs_chk : cstrs_img_chk Img0.rsegs headamp_A_globals headamp_A_strs = true.
Proof. vm_compute. reflexivity. Qed.

(* 4. The read-only cells (HPgImgA.headamp_A_cells: the parse's two doubles, the harness's three division
   constants, the 31 pointer cells of .data.rel.ro) and the parse's two doubles (HPgImgA.headamp_A_dcs: 0.5 at
   0x10378, 256.0 at 0x10340): (cell, 8-byte value). Pinned image sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47. *)
Lemma headamp_A_cells_chk :
  img_cells_chk Img0.rsegs headamp_A_cells && img_cells_chk Img0.rsegs headamp_A_dcs = true.
Proof. vm_compute. reflexivity. Qed.

(* 5. The stack-guard cells: musl's __strtol_internal (0x952f8) loads the GOT word 0x9cff8 (auipc a0, 8 at 0x95320;
   ld s3, -0x328(a0) at 0x95324) and reads the guard through it (ld a0, 0(s3) at 0x95328); the GOT word holds
   0x5f7d90, the address of __stack_chk_guard, which lies in .bss [0xa1700, 0x5f9630). Pinned image sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47. *)
Definition GUARD : Z := 0x5f7d90.
Definition headamp_A_guard_words : list (Z * Z) := [(0x95320, 0x00008517); (0x95324, 0xcd853983); (0x95328, 0x0009b503)].
Lemma headamp_A_guard_chk :
  entries_chk Img0.rsegs headamp_A_guard_words && img_cells_chk Img0.rsegs [(0x9cff8, GUARD)] &&
  (hi_gotw headamp_himg_A =? 0x9cff8) && (hi_guard headamp_himg_A =? GUARD) = true.
Proof. vm_compute. reflexivity. Qed.

(* ================================================ the witness ================================================ *)
(* No byte hidden. *)
Definition H_w : word -> bool := fun _ => false.
(* The shadow byte of the granule at g (g mod 8 = 0) of the global (beg, n, _), beg mod 8 = 0: 0 for a full granule,
   n mod 8 for the last partial one, 0xf9 (the runtime's guard-byte value for globals, PoisonRedZones) for a guard
   one. *)
Definition gshadow (beg n g : Z) : Z := if g + 8 <=? beg + n then 0 else if g <? beg + n then n mod 8 else 0xf9.
(* The shadow byte of the granule at g: from the listed global whose [beg, beg + size_with_redzone) holds g, else 0. *)
Definition granule_shadow (gs : list (Z * (Z * Z * Z))) (g : Z) : Z :=
  match find (fun e => let '(_, (beg, _, r)) := e in (beg <=? g) && (g <? beg + r)) gs with
  | Some (_, (beg, n, _)) => gshadow beg n g
  | None => 0
  end.
(* The application spans whose shadow bytes the witness memory holds: the .rodata span of the 40 .rodata globals,
   64-byte aligned at both ends (it holds every string's shadow hull, which hd_cstr's shadow_hull_vis reads), and the
   span of the three .data.rel.ro globals. Every descriptor's [beg, beg + size_with_redzone) lies in one of them
   (lib/A/HPgSatSeg.v headamp_A_globals_apart_chk). Pinned image sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47. *)
Definition shadow_spans : list (Z * Z) := [(0x20ec0, 0x21500); (0x9c060, 0x9c1e0)].
(* The shadow byte at u >= SHADOW_OFF for an application address in a span: the byte granule_shadow gives for its
   granule, which is what the runtime writes when it registers the 43 globals. The two parts of the first span that
   no descriptor covers, [0x21440, 0x21460) (after .str.31's guard bytes) and [0x214e0, 0x21500) (after the last
   string's), the runtime never writes: their shadow bytes keep the 0 of the freshly mapped shadow (the hulls of
   the strings at 0x21460 and 0x214c0 read them). Pinned image sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47. *)
Definition span_shadow (u : Z) : option byte :=
  if existsb (fun r => (SHADOW_OFF + fst r / 8 <=? u) && (u <? SHADOW_OFF + snd r / 8)) shadow_spans
  then Some (Z_to_bv 8 (granule_shadow headamp_A_globals ((u - SHADOW_OFF) * 8)))
  else None.
(* The guard word __stack_chk_guard [GUARD, GUARD + 8) holds the canary the C library's start-up writes there
   (musl's __init_ssp: random bytes with the second byte set to 0); GUARD_CAN is one such value. The guard lies in
   .bss [0xa1700, 0x5f9630) (pinned image sha256 f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47),
   so it is runtime data, not a program byte: the witness memory holds its eight bytes. *)
Definition GUARD_CAN : Z := 0x0123456789ab00ef.
Definition guard_mem (u : Z) : option byte :=
  if (GUARD <=? u) && (u <? GUARD + 8) then Some (Z_to_bv 8 (YO0f.le_byte GUARD_CAN 8 (Z.to_nat (u - GUARD))))
  else None.
(* mem_w holds the shadow bytes of the spans and the guard's eight bytes; every other address reads None, so each
   program byte (string, constant, pointer cell, GOT word) comes from the image through mbyte's fall-back to
   seg_rom. *)
Definition mem_w : word -> option byte := fun w =>
  if bv_unsigned w <? SHADOW_OFF then guard_mem (bv_unsigned w) else span_shadow (bv_unsigned w).

(* W1. Every string of headamp_A_strs satisfies hd_cstr at (H_w, mem_w). *)
Definition cstrs_wit_chk (l : list (Z * list Z)) : bool := forallb (fun c => cstr_chk Img0.rsegs H_w mem_w (fst c) (snd c)) l.
Lemma hd_cstr_A_chk : cstrs_wit_chk headamp_A_strs = true.
Proof. vm_compute. reflexivity. Qed.
Lemma hd_cstr_A : forall a s, In (a, s) headamp_A_strs -> hd_cstr Img0.rsegs H_w mem_w a s.
Proof.
intros a s Hin. apply cstr_chk_ok.
pose proof hd_cstr_A_chk as E. unfold cstrs_wit_chk in E. rewrite forallb_forall in E.
exact (E (a, s) Hin).
Qed.
Print Assumptions hd_cstr_A.
(* A control: without the shadow bytes the checker refuses the first string (its shadow reads None). *)
Lemma hd_cstr_A_control :
  cstr_chk Img0.rsegs H_w (fun _ => None) (fst (nth 0 headamp_A_strs (0, []))) (snd (nth 0 headamp_A_strs (0, []))) = false.
Proof. vm_compute. reflexivity. Qed.

(* W2. The read-only cells and the parse's two doubles. *)
Lemma hd_ro_cells_A_chk :
  cells_chk Img0.rsegs (mrestrict H_w mem_w) headamp_A_cells &&
  cells_chk Img0.rsegs (mrestrict H_w mem_w) headamp_A_dcs = true.
Proof. vm_compute. reflexivity. Qed.
Lemma hd_ro_cells_A :
  hd_ro_cells Img0.rsegs H_w mem_w headamp_A_cells /\ hd_ro_cells Img0.rsegs H_w mem_w headamp_A_dcs.
Proof.
pose proof hd_ro_cells_A_chk as E. apply andb_prop in E. destruct E as [E1 E2].
split; unfold hd_ro_cells; apply cells_chk_ok; assumption.
Qed.
Print Assumptions hd_ro_cells_A.

(* W3. The stack-guard premise at (hi_gotw, hi_guard) = (0x9cff8, 0x5f7d90): the GOT word (read from the image)
   holds the guard's address, and the guard's word (the witness memory's eight bytes) is readable. *)
Lemma hd_guard_A_chk : guard_chk (aview Img0.rsegs H_w mem_w) (hi_gotw headamp_himg_A) (hi_guard headamp_himg_A) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma hd_guard_A : hd_guard_ok (aview Img0.rsegs H_w mem_w) (hi_gotw headamp_himg_A) (hi_guard headamp_himg_A).
Proof. exact (guard_chk_ok _ _ _ hd_guard_A_chk). Qed.
Print Assumptions hd_guard_A.
(* A measured fact beside W3: the snapshot's fourth loaded segment [0x9e000, 0x5fa000) spans .bss too (its bytes
   there are 0), so the guard's word is readable from the image alone; the premise holds with no memory byte. *)
Lemma hd_guard_A_img_chk :
  guard_chk (aview Img0.rsegs H_w (fun _ => None)) (hi_gotw headamp_himg_A) (hi_guard headamp_himg_A) = true.
Proof. vm_compute. reflexivity. Qed.

(* W4. Each callee entry holds its measured first instruction word in the image. *)
Lemma hd_entries_A : forall a w, In (a, w) headamp_A_entries ->
  forall k, (k < 4)%nat -> seg_rom Img0.rsegs (Z_to_bv 64 (a + Z.of_nat k)) = Some (Z_to_bv 8 (YO0f.le_byte w 4 k)).
Proof.
intros a w Hin k Hk. refine (img_val_chk_ok Img0.rsegs a 4 w _ k Hk).
pose proof headamp_A_entries_chk as E. unfold entries_chk in E. rewrite forallb_forall in E.
exact (E (a, w) Hin).
Qed.
Print Assumptions hd_entries_A.

(* W5. The string premises of hd_parse_result_specX (and hd_parse_specX) at (akey, aph, apad, asens) =
   (0x21460, 0x21480, 0x214a0, 0x214c0) with the shared model's texts (Pod/Headamp.v HA_PREFIX, NAME_PHANTOM,
   NAME_PAD, NAME_SENS), in the order hd_parse_args states them; then the harness's own four literals at
   (hkey, hph, hpad, hsens) = (0x20f00, 0x21340, 0x21360, 0x21380) with the same texts (expect_of compares the
   pod's names with them). The texts are HPgImgA.headamp_A_strs' entries 32 .. 35 and 2, 24, 25, 26
   (HPgImgA.headamp_A_key_text, headamp_A_param_texts). *)
Lemma hd_cstr_A_at : forall n a s, nth_error headamp_A_strs n = Some (a, s) -> hd_cstr Img0.rsegs H_w mem_w a s.
Proof. intros n a s E. apply hd_cstr_A. eapply nth_error_In. exact E. Qed.
Lemma hd_sat_parse_strs_A :
  (hd_cstr Img0.rsegs H_w mem_w (hi_akey headamp_himg_A) (hd_zbytes Headamp.HA_PREFIX) /\
   hd_cstr Img0.rsegs H_w mem_w (hi_aph headamp_himg_A) (hd_zbytes Headamp.NAME_PHANTOM) /\
   hd_cstr Img0.rsegs H_w mem_w (hi_apad headamp_himg_A) (hd_zbytes Headamp.NAME_PAD) /\
   hd_cstr Img0.rsegs H_w mem_w (hi_asens headamp_himg_A) (hd_zbytes Headamp.NAME_SENS)) /\
  (hd_cstr Img0.rsegs H_w mem_w (hi_hkey headamp_himg_A) (hd_zbytes Headamp.HA_PREFIX) /\
   hd_cstr Img0.rsegs H_w mem_w (hi_hph headamp_himg_A) (hd_zbytes Headamp.NAME_PHANTOM) /\
   hd_cstr Img0.rsegs H_w mem_w (hi_hpad headamp_himg_A) (hd_zbytes Headamp.NAME_PAD) /\
   hd_cstr Img0.rsegs H_w mem_w (hi_hsens headamp_himg_A) (hd_zbytes Headamp.NAME_SENS)).
Proof.
destruct headamp_A_param_texts as (Ep & Ea & Es).
rewrite headamp_A_key_text, Ep, Ea, Es.
split; (split; [|split; [|split]]).
- apply (hd_cstr_A_at 32); reflexivity.
- apply (hd_cstr_A_at 33); reflexivity.
- apply (hd_cstr_A_at 34); reflexivity.
- apply (hd_cstr_A_at 35); reflexivity.
- apply (hd_cstr_A_at 2); reflexivity.
- apply (hd_cstr_A_at 24); reflexivity.
- apply (hd_cstr_A_at 25); reflexivity.
- apply (hd_cstr_A_at 26); reflexivity.
Qed.
Print Assumptions hd_sat_parse_strs_A.
