(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from part of proofs/libreac/fuzz_grant/lib/A/Prog/GrantClose.v (itself made from part of proofs/cgif/cgif_file_fuzzer/lib/A/ACfi.v) for libreac/fuzz_disco: is_shc, is_shv, zfind, vscan, glob_chk, in_zr_b and their lemmas, and the shadow of the image and of its registered globals, stated at TfibB (lib/A/AD2l.v) and at disco_segs, the segment list of PB_disco; glob_chk accepts a global with no full granule; the byte check of the read-only ranges (byte_free_b, ro_range_b, ro_unowned_of_b) and its registered-globals part (disco_globs_unowned, disco_glob_readable) are added; module paths changed. *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_disco/lib/A/Prog/DiscoRoClose.v at origin/ossv/recipes 501c0d516c69 (and BoxGShadow.v:53's cell read); for reac-pw/fuzz_rate image A: module paths changed; the facts are stated at any symbol record B with TfibSyms B (lib/A/AF0m.v), through its fields ts_owned, ts_const, ts_zsh and ts_errno, in place of TfibB, over image A's loaded segments, as RtPgBase.v's rt_img_shadow_vis / rt_globs_marked / rt_ro_unowned and RtPgSiteA.v's rate_A_img_facts; the zero shadow is read from AR's am_zshadow (as BoxGShadow.v's img_shadow_vis_box does) in place of al_zshadow; byte_free_b and ro_range_b take the owned-static list and the errno address in place of B; BoxGShadow.v's shadow_cell_view is generalized from one-byte cells to cells of any width (rate_A_const_view); rt_rom_pinned and its checks (rom_ext, cnum, cell_byte_b, pinned_b and the errno check) are new; disco_segs_tfib, disco_globs_unowned, disco_glob_in_ranges, disco_ro_unowned_of_b and disco_glob_readable are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgRoClose.v at af0538adbf24 for image B
   (fuzz_rate.asan-ubsan): the start-up tables are image B's (lib/AU/YF0m.v, generated from the asan-ubsan pin), the
   segments image B's loaded segments, the record RtPgImgB.rate_himg_B and the facts RtPgSiteB.rate_B_img_facts. *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14): the read-only facts of the image that image B's
   walks take, proved by computation over the start-up tables of lib/AU/YF0m.v at any symbol record B with TfibSyms B.
   Proves no function (kind: start-up facts of the image, by computation over the generated start-up tables).
   - rate_B_img_shadow_vis (RtPgBase.rt_img_shadow_vis at [IMG_LO, IMG_TOP)): every shadow byte of the image's range
     is readable in every AR state. The granules [IMG_LO / 8, IMG_TOP / 8) are tiled by the ranges of
     Tfib_zero_shadow (whose shadow AR's am_zshadow keeps zero) and the one-byte cells of Tfib_const_shadow (which
     AR's am_const keeps at their values); vscan walks them.
   - rate_B_globs_marked (RtPgBase.rt_globs_marked at the 57 registered globals of rate_himg_B): each global's full
     granules lie in a zero-shadow range and its last partial granule is a constant shadow cell holding size mod 8
     (glob_chk).
   - rate_B_ro_unowned (RtPgBase.rt_ro_unowned over RtPgCSpec.rt_ro_ranges rate_himg_B: the 46 strings with their
     NUL, the two 4-byte tables, the two 8-byte tables and the 45 read-only cells): no byte is in Tfib_owned_static
     or in the errno cell [TFIB_ERRNO, TFIB_ERRNO + 4).
   - rate_B_img_facts_tfib: RtPgSiteB.rate_B_img_facts, the conjunction of the three.
   - rate_B_rom_pinned_tfib (RtPgBase.rt_rom_pinned): every byte of a read-only segment that is an owned static
     reads, in every AR state, as the image's byte. The read-only segments of image B are computed from its segments
     (rom_ext: the R PT_LOAD [0x10000, 0x2fa0c) and the RX PT_LOAD [0x30a0c, 0x9a994) of the program headers); each
     range of Tfib_owned_static is cut to each of them first, and each byte of a cut is covered by a cell of
     Tfib_const_abs whose byte there is the image's byte (pinned_b); the four errno bytes lie in no read-only segment
     (rate_B_errno_chk). In an AR state such a cell, a constant cell of as_const B ly, reads as its value
     (rate_B_const_view). *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK04 YA0i YA0n YP09.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import YF0m RtPgImgB RtPgSiteB.
From OSSVerify.reac_pw.fuzz_rate.images Require AsanUbsan.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* Image B: the loaded segments elf-snapshot makes of the pinned fuzz_rate.asan-ubsan. *)
Local Notation segs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

(* ======================================== the shadow of the image ======================================== *)
Definition in_zr_b (a : Z) (r : Z * Z) : bool := ((fst r <=? a) && (a <? fst r + snd r))%bool.

Definition is_shc (s : Z) (c : acell) : bool :=
  match c with ACell (ANum s') (S O) (AV (ANum _)) => Z.eqb s' s | _ => false end.
Definition is_shv (s v : Z) (c : acell) : bool :=
  match c with ACell (ANum s') (S O) (AV (ANum v')) => (Z.eqb s' s && Z.eqb v' v)%bool | _ => false end.

Fixpoint zfind (k : Z) (zs : list (Z * Z)) : option Z :=
  match zs with
  | [] => None
  | (q, m) :: r => if ((q / 8 <=? k) && (k <? (q + m) / 8))%bool then Some ((q + m) / 8) else zfind k r
  end.

Fixpoint vscan (fuel : nat) (k hi : Z) : bool :=
  match fuel with
  | O => false
  | S f =>
      if hi <=? k then true else
      match zfind k Tfib_zero_shadow with
      | Some e => vscan f e hi
      | None => (existsb (is_shc (SHADOW_OFF + k)) Tfib_const_shadow && vscan f (k + 1) hi)%bool
      end
  end.

Definition glob_chk (g : Z * Z) : bool :=
  ((fst g mod 8 =? 0) && (0 <=? snd g) &&
   ((snd g / 8 =? 0) ||
    existsb (fun r => (fst r <=? fst g) && (fst g + snd g / 8 * 8 <=? fst r + snd r)) Tfib_zero_shadow) &&
   ((snd g mod 8 =? 0) || existsb (is_shv (SHADOW_OFF + fst g / 8 + snd g / 8) (snd g mod 8)) Tfib_const_shadow))%bool.

(* No byte a is in the owned-static ranges os or in the errno cell [er, er + 4). *)
Definition byte_free_b (os : list (Z * Z)) (er a : Z) : bool :=
  (negb (existsb (in_zr_b a) os) && negb ((er <=? a) && (a <? er + 4)))%bool.

Definition ro_range_b (os : list (Z * Z)) (er : Z) (r : Z * Z) : bool :=
  forallb (fun j => byte_free_b os er (fst r + Z.of_nat j)) (seq 0 (Z.to_nat (snd r))).

Lemma not_Exists_in_zr : forall a l, existsb (in_zr_b a) l = false -> ~ Exists (in_zr a) l.
Proof.
intros a l H HE. apply Exists_exists in HE as (r & Hr & Hz). unfold in_zr in Hz.
assert (E : existsb (in_zr_b a) l = true).
{ apply existsb_exists. exists r. split; [exact Hr|]. unfold in_zr_b. apply andb_true_intro.
  split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
congruence.
Qed.

Lemma le_byte1 : forall v, 0 <= v < 256 -> YG0f.le_byte v 1 0 = v.
Proof.
intros v Hv. unfold YG0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite (Z.mod_small v 256 Hv). exact (Z.mod_small v 256 Hv).
Qed.

Lemma is_shc_eq : forall s c, is_shc s c = true -> exists v, c = z1 (ANum s) v.
Proof.
intros s [ca cw cv] H. destruct ca; try (cbn in H; discriminate H).
destruct cw as [|[|cw]]; try (cbn in H; discriminate H).
destruct cv as [e|m0 v0]; try (cbn in H; discriminate H).
destruct e; try (cbn in H; discriminate H).
cbn in H. apply Z.eqb_eq in H. subst. eexists. reflexivity.
Qed.

Lemma is_shv_eq : forall s v c, is_shv s v c = true -> c = z1 (ANum s) v.
Proof.
intros s v [ca cw cv] H. destruct ca; try (cbn in H; discriminate H).
destruct cw as [|[|cw]]; try (cbn in H; discriminate H).
destruct cv as [e|m0 v0]; try (cbn in H; discriminate H).
destruct e; try (cbn in H; discriminate H).
cbn in H. apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. subst. reflexivity.
Qed.

Lemma zfind_some : forall k zs e, zfind k zs = Some e ->
  exists q m, In (q, m) zs /\ q / 8 <= k < (q + m) / 8 /\ e = (q + m) / 8.
Proof.
intros k zs. induction zs as [|[q m] r IH]; intros e H; cbn [zfind] in H; [discriminate|].
destruct ((q / 8 <=? k) && (k <? (q + m) / 8))%bool eqn:Hb.
- injection H as <-. apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  exists q, m. split; [left; reflexivity|]. split; [split; assumption | reflexivity].
- destruct (IH e H) as (q' & m' & Hin & Hk & He). exists q', m'. split; [right; exact Hin|]. split; [exact Hk | exact He].
Qed.

Lemma vscan_ok : forall fuel k hi, vscan fuel k hi = true -> forall j, k <= j < hi ->
  (exists q m, In (q, m) Tfib_zero_shadow /\ q / 8 <= j < (q + m) / 8) \/
  existsb (is_shc (SHADOW_OFF + j)) Tfib_const_shadow = true.
Proof.
induction fuel as [|f IH]; intros k hi H j Hj; cbn [vscan] in H; [discriminate|].
destruct (hi <=? k) eqn:E; [apply Z.leb_le in E; exfalso; lia|].
destruct (zfind k Tfib_zero_shadow) as [e|] eqn:Ez.
- destruct (zfind_some _ _ _ Ez) as (q & m & Hin & Hk & ->).
  destruct (Z_lt_le_dec j ((q + m) / 8)) as [Hlt|Hge].
  + left. exists q, m. split; [exact Hin|]. split; [|exact Hlt].
    apply (Z.le_trans _ k); [exact (proj1 Hk) | exact (proj1 Hj)].
  + exact (IH _ _ H j (conj Hge (proj2 Hj))).
- apply andb_prop in H as [Hc H]. destruct (Z.eq_dec j k) as [->|Hne]; [right; exact Hc|].
  apply (IH _ _ H). lia.
Qed.

(* vscan walks the image's granules (each zero-shadow range is one step, each constant shadow cell one). *)
Lemma rate_B_vscan : vscan (Pos.to_nat 4096) (IMG_LO / 8) (IMG_TOP / 8) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma rate_B_globs_chk : forallb glob_chk (hi_globs rate_himg_B) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma zs_align_chk : forallb (fun r => (fst r mod 8 =? 0) && (snd r mod 8 =? 0) && (0 <=? snd r))%bool Tfib_zero_shadow = true.
Proof. vm_compute. reflexivity. Qed.

Lemma zs_align : forall q m, In (q, m) Tfib_zero_shadow -> q mod 8 = 0 /\ m mod 8 = 0 /\ 0 <= m.
Proof.
intros q m Hin. pose proof (proj1 (forallb_forall _ _) zs_align_chk (q, m) Hin) as Hb. cbn [fst snd] in Hb.
apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2].
apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. apply Z.leb_le in H3. auto.
Qed.

Lemma zs_gran_end : forall q m, q mod 8 = 0 -> m mod 8 = 0 -> (q + m) / 8 = q / 8 + m / 8.
Proof. intros q m Hq Hm. lia. Qed.

Lemma img_gran : forall a, IMG_LO <= a < IMG_TOP -> IMG_LO / 8 <= a / 8 < IMG_TOP / 8.
Proof. intros a Ha. lia. Qed.

Lemma glob_gran : forall q sz r0 m0 i, q mod 8 = 0 -> r0 mod 8 = 0 -> m0 mod 8 = 0 ->
  r0 <= q -> q + sz / 8 * 8 <= r0 + m0 -> 0 <= i < sz / 8 ->
  r0 / 8 <= q / 8 + i < (r0 + m0) / 8.
Proof. intros q sz r0 m0 i Hq Hr Hm H1 H2 Hi. lia. Qed.

Lemma last_gran : forall sz i, 0 <= sz -> 0 <= i < (sz + 7) / 8 -> sz / 8 <= i ->
  i = sz / 8 /\ sz mod 8 <> 0 /\ 0 <= sz mod 8 < 256.
Proof. intros sz i Hsz Hi Hge. lia. Qed.

(* ======================================== the read-only ranges ======================================== *)
Lemma ro_unowned_of_b : forall B l, forallb (ro_range_b (as_owned_static B) (as_errno B)) l = true ->
  Forall (fun r => rt_ro_unowned B (fst r) (snd r)) l.
Proof.
intros B l H. apply Forall_forall. intros [lo n] Hin a Ha. cbn [fst snd] in Ha.
pose proof (proj1 (forallb_forall _ _) H (lo, n) Hin) as Hr. unfold ro_range_b in Hr. cbn [fst snd] in Hr.
assert (Hj : In (Z.to_nat (a - lo)) (seq 0 (Z.to_nat n))) by (apply in_seq; lia).
pose proof (proj1 (forallb_forall _ _) Hr _ Hj) as Hb. cbv beta in Hb.
rewrite Z2Nat.id in Hb by lia. replace (lo + (a - lo)) with a in Hb by lia.
unfold byte_free_b in Hb. apply andb_prop in Hb as [Ho He]. apply negb_true_iff in Ho. apply negb_true_iff in He.
split; [exact (not_Exists_in_zr _ _ Ho)|].
intros [E1 E2].
assert (X : ((as_errno B <=? a) && (a <? as_errno B + 4))%bool = true)
  by (apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
congruence.
Qed.

Lemma rate_B_ro_chk : forallb (ro_range_b Tfib_owned_static TFIB_ERRNO) (rt_ro_ranges rate_himg_B) = true.
Proof. vm_compute. reflexivity. Qed.

(* ======================================== the read-only segments ======================================== *)
(* The extents (base, size) of the read-only segments of a segment list. *)
Definition rom_ext (sg : list Segment) : list (Z * Z) :=
  map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s))) (List.filter (fun s => negb (seg_writable s)) sg).

Lemma rom_ext_in : forall sg a, YG0d.in_rom sg a -> exists e, In e (rom_ext sg) /\ fst e <= a < fst e + snd e.
Proof.
intros sg a (s & Hs & Hw & Hr). exists (Z.of_N (seg_base s), Z.of_N (seg_size s)). cbn [fst snd]. split; [|exact Hr].
unfold rom_ext. apply in_map_iff. exists s. split; [reflexivity|].
apply filter_In. split; [exact Hs | cbv beta; rewrite Hw; reflexivity].
Qed.

Definition oz_is (o : option Z) (v : Z) : bool := match o with Some z => Z.eqb z v | None => false end.
Lemma oz_is_ok : forall o v, oz_is o v = true -> o = Some v.
Proof. intros [z|] v H; cbn [oz_is] in H; [apply Z.eqb_eq in H; subst z; reflexivity | discriminate H]. Qed.

(* A constant cell at a number with a number as its value: its address, width and value. *)
Definition cnum (c : acell) : option (Z * nat * Z) :=
  match c with ACell (ANum s) w (AV (ANum v)) => Some (s, w, v) | _ => None end.
Lemma cnum_eq : forall c s w v, cnum c = Some (s, w, v) -> c = ACell (ANum s) w (AV (ANum v)).
Proof.
intros [ca cw cv] s w v H. destruct ca; try (cbn in H; discriminate H).
destruct cv as [e|m0 v0]; try (cbn in H; discriminate H).
destruct e; try (cbn in H; discriminate H).
cbn in H. inversion H; subst; reflexivity.
Qed.

(* The cell c covers byte a, and its byte there is the image's byte at a. *)
Definition cell_byte_b (sg : list Segment) (a : Z) (c : acell) : bool :=
  match cnum c with
  | Some (s, w, v) =>
      if ((s <=? a) && (a <? s + Z.of_nat w))%bool
      then oz_is (option_map (fun b : byte => bv_unsigned b) (seg_rom sg (Z_to_bv 64 a))) (YG0f.le_byte v w (Z.to_nat (a - s)))
      else false
  | None => false
  end.
Lemma cell_byte_b_ok : forall sg a c, cell_byte_b sg a c = true ->
  exists s w v, c = ACell (ANum s) w (AV (ANum v)) /\ s <= a < s + Z.of_nat w /\
  option_map (fun b : byte => bv_unsigned b) (seg_rom sg (Z_to_bv 64 a)) = Some (YG0f.le_byte v w (Z.to_nat (a - s))).
Proof.
intros sg a c H. unfold cell_byte_b in H.
destruct (cnum c) as [[[s w] v]|] eqn:Ec; cbv beta iota in H; [|discriminate H].
destruct ((s <=? a) && (a <? s + Z.of_nat w))%bool eqn:Er; cbv iota in H; [|discriminate H].
apply andb_prop in Er as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
exists s, w, v. split; [exact (cnum_eq c s w v Ec)|]. split; [lia|].
exact (oz_is_ok _ _ H).
Qed.

(* Every byte of every owned-static range of os that lies in a read-only segment of sg is covered by a cell of cs
   whose byte there is the image's byte. Each range is cut to each read-only extent first: the bytes outside the
   read-only segments are never enumerated. *)
Definition cut_b (r e : Z * Z) : Z * Z := (Z.max (fst r) (fst e), Z.min (fst r + snd r) (fst e + snd e)).
Definition pinned_b (sg : list Segment) (cs : list acell) (os : list (Z * Z)) : bool :=
  forallb (fun r => forallb (fun e =>
    forallb (fun j => existsb (cell_byte_b sg (fst (cut_b r e) + Z.of_nat j)) cs)
      (seq 0 (Z.to_nat (snd (cut_b r e) - fst (cut_b r e))))) (rom_ext sg)) os.

Lemma pinned_b_ok : forall sg cs os a, pinned_b sg cs os = true -> YG0d.in_rom sg a -> Exists (in_zr a) os ->
  exists c, In c cs /\ cell_byte_b sg a c = true.
Proof.
intros sg cs os a H Hrom Ho.
apply Exists_exists in Ho as (r & Hr & Hzr). unfold in_zr in Hzr.
destruct (rom_ext_in sg a Hrom) as (e & He & Hze).
unfold pinned_b in H. pose proof (proj1 (forallb_forall _ _) H r Hr) as H1. cbv beta in H1.
pose proof (proj1 (forallb_forall _ _) H1 e He) as H2. cbv beta in H2.
unfold cut_b in H2. cbn [fst snd] in H2.
assert (Hj : In (Z.to_nat (a - Z.max (fst r) (fst e)))
               (seq 0 (Z.to_nat (Z.min (fst r + snd r) (fst e + snd e) - Z.max (fst r) (fst e)))))
  by (apply in_seq; lia).
pose proof (proj1 (forallb_forall _ _) H2 _ Hj) as H3. cbv beta in H3.
rewrite Z2Nat.id in H3 by lia. replace (Z.max (fst r) (fst e) + (a - Z.max (fst r) (fst e))) with a in H3 by lia.
apply existsb_exists in H3. exact H3.
Qed.

(* Image B: every non-empty cut of each owned-static range to each read-only extent, byte by byte, is covered by a cell of Tfib_const_abs holding the image's byte. *)
Lemma rate_B_pinned_chk : pinned_b segs Tfib_const_abs Tfib_owned_static = true.
Proof. vm_compute. reflexivity. Qed.

(* Image B: the errno cell [TFIB_ERRNO, TFIB_ERRNO + 4) meets no read-only segment. *)
Lemma rate_B_errno_chk :
  forallb (fun e => (TFIB_ERRNO + 4 <=? fst e) || (fst e + snd e <=? TFIB_ERRNO))%bool (rom_ext segs) = true.
Proof. vm_compute. reflexivity. Qed.

(* ======================================== at a symbol record of image B ======================================== *)
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis HB : TfibSyms B.

(* In every AR state a constant cell of as_const B ly at a number, with a number as its value, reads byte k < w as
   the k-th little-endian byte of its value (BoxGShadow.v's shadow_cell_view, for any width). *)
Lemma rate_B_const_view : forall ly S (W : world segs) mem md s w v k,
  AR segs B ly S W mem md -> In (ACell (ANum s) w (AV (ANum v))) (as_const B ly) -> (k < w)%nat ->
  aview segs (w_H W) mem (s + Z.of_nat k) = Some (YG0f.le_byte v w k).
Proof.
intros ly S W mem md s w v k [HM _] Hin Hk. apply am_const in HM.
pose proof (proj1 (Forall_forall _ _) HM _ Hin) as H. unfold cell_holds in H. cbv zeta in H.
cbn [c_val c_at c_w aeval] in H. exact (H k Hk).
Qed.

Lemma rate_B_shadow_cell : forall ly S (W : world segs) mem md s v,
  AR segs B ly S W mem md -> In (z1 (ANum s) v) Tfib_const_shadow ->
  aview segs (w_H W) mem s = Some (YG0f.le_byte v 1 0).
Proof.
intros ly S W mem md s v HAR Hin.
assert (Hc : In (ACell (ANum s) 1 (AV (ANum v))) (as_const B ly)).
{ rewrite (ts_const B HB ly). unfold Tfib_const. apply in_or_app. right. apply in_or_app. right. exact Hin. }
pose proof (rate_B_const_view ly S W mem md s 1 v 0 HAR Hc ltac:(lia)) as E.
change (s + Z.of_nat 0) with (s + 0) in E. rewrite Z.add_0_r in E. exact E.
Qed.

Lemma rate_B_zs_rd : forall ly S (W : world segs) mem md q m j,
  AR segs B ly S W mem md -> In (q, m) Tfib_zero_shadow -> q / 8 <= j < (q + m) / 8 ->
  aview segs (w_H W) mem (SHADOW_OFF + j) = Some 0.
Proof.
intros ly S W mem md q m j [HM _] Hin Hj. apply am_zshadow in HM. unfold zshadow_ok in HM.
assert (Hin' : In (q, m) (zero_shadow_ranges B ly)).
{ unfold zero_shadow_ranges. right. rewrite (ts_zsh B HB). exact Hin. }
pose proof (proj1 (Forall_forall _ _) HM _ Hin') as Hz. cbn [fst snd] in Hz. unfold zero_shadow in Hz.
destruct (zs_align q m Hin) as (Hq & Hm & Hm0).
rewrite (zs_gran_end q m Hq Hm) in Hj.
replace (SHADOW_OFF + j) with (shadow_of_addr SHADOW_OFF q + (j - q / 8)) by (unfold shadow_of_addr; lia).
apply Hz. lia.
Qed.

Lemma rate_B_img_shadow_vis : rt_img_shadow_vis segs B IMG_LO IMG_TOP.
Proof.
intros ly S W mem md a HAR Ha. unfold shadow_addr.
destruct (vscan_ok _ _ _ rate_B_vscan (a / 8) (img_gran a Ha)) as [(q & m & Hin & Hq) | Hc].
- rewrite (rate_B_zs_rd ly S W mem md q m (a / 8) HAR Hin Hq). discriminate.
- apply existsb_exists in Hc as (c & Hin & Hb). destruct (is_shc_eq _ _ Hb) as [v ->].
  rewrite (rate_B_shadow_cell ly S W mem md _ v HAR Hin). discriminate.
Qed.

Lemma rate_B_globs_marked : rt_globs_marked segs B (hi_globs rate_himg_B).
Proof.
intros ly S W mem md q sz Hin HAR.
pose proof (proj1 (forallb_forall _ _) rate_B_globs_chk (q, sz) Hin) as Hb. unfold glob_chk in Hb. cbn [fst snd] in Hb.
apply andb_prop in Hb as [Hb Hlast]. apply andb_prop in Hb as [Hb Hfull]. apply andb_prop in Hb as [Hq Hsz].
apply Z.eqb_eq in Hq. apply Z.leb_le in Hsz.
split; [exact Hq|]. split; [exact Hsz|]. intros i Hi.
destruct (i <? sz / 8) eqn:Hlt.
- apply Z.ltb_lt in Hlt.
  apply orb_true_iff in Hfull as [H0|H0]; [apply Z.eqb_eq in H0; rewrite H0 in Hlt; exfalso; lia|].
  apply existsb_exists in H0 as ([r0 m0] & Hr & Hf). cbn [fst snd] in Hf.
  apply andb_prop in Hf as [Hf1 Hf2]. apply Z.leb_le in Hf1. apply Z.leb_le in Hf2.
  destruct (zs_align r0 m0 Hr) as (Hr8 & Hm8 & Hm0).
  pose proof (glob_gran q sz r0 m0 i Hq Hr8 Hm8 Hf1 Hf2 (conj (proj1 Hi) Hlt)) as Hg.
  unfold shadow_of_addr.
  replace (SHADOW_OFF + q / 8 + i) with (SHADOW_OFF + (q / 8 + i)) by lia.
  exact (rate_B_zs_rd ly S W mem md r0 m0 (q / 8 + i) HAR Hr Hg).
- apply Z.ltb_ge in Hlt.
  destruct (last_gran sz i Hsz Hi Hlt) as (Hi' & Hnz & Hrng).
  apply orb_true_iff in Hlast as [H0|H0]; [apply Z.eqb_eq in H0; exfalso; exact (Hnz H0)|].
  apply existsb_exists in H0 as (c & Hc & Hcb). apply is_shv_eq in Hcb. subst c. subst i.
  unfold shadow_of_addr.
  rewrite (rate_B_shadow_cell ly S W mem md _ _ HAR Hc). rewrite (le_byte1 _ Hrng). reflexivity.
Qed.

Lemma rate_B_ro_unowned : Forall (fun r => rt_ro_unowned B (fst r) (snd r)) (rt_ro_ranges rate_himg_B).
Proof.
apply ro_unowned_of_b. rewrite (ts_owned B HB), (ts_errno B HB). exact rate_B_ro_chk.
Qed.

Theorem rate_B_img_facts_tfib : rate_B_img_facts segs B.
Proof.
unfold rate_B_img_facts, rt_img_facts.
split; [exact rate_B_ro_unowned|]. split; [exact rate_B_globs_marked | exact rate_B_img_shadow_vis].
Qed.

Theorem rate_B_rom_pinned_tfib : rt_rom_pinned segs B.
Proof.
intros ly S W mem md a HAR Hrom [Ho|He].
- rewrite (ts_owned B HB) in Ho.
  destruct (pinned_b_ok _ _ _ a rate_B_pinned_chk Hrom Ho) as (c & Hc & Hb).
  destruct (cell_byte_b_ok _ _ _ Hb) as (s & w & v & -> & Hs & Hrd).
  assert (Hin : In (ACell (ANum s) w (AV (ANum v))) (as_const B ly)).
  { rewrite (ts_const B HB ly). unfold Tfib_const. apply in_or_app. right. apply in_or_app. left. exact Hc. }
  assert (Hk : (Z.to_nat (a - s) < w)%nat) by lia.
  pose proof (rate_B_const_view ly S W mem md s w v (Z.to_nat (a - s)) HAR Hin Hk) as E.
  rewrite Z2Nat.id in E by lia. replace (s + (a - s)) with a in E by lia.
  rewrite E. symmetry. exact Hrd.
- rewrite (ts_errno B HB) in He. exfalso.
  destruct (rom_ext_in _ a Hrom) as (e & He' & Hz).
  pose proof (proj1 (forallb_forall _ _) rate_B_errno_chk e He') as X. cbv beta in X.
  apply orb_prop in X as [X|X]; apply Z.leb_le in X; lia.
Qed.

End b.

About rate_B_img_facts_tfib.
Print Assumptions rate_B_img_facts_tfib.
About rate_B_rom_pinned_tfib.
Print Assumptions rate_B_rom_pinned_tfib.
