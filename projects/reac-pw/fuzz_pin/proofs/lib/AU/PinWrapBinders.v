(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: made from part of proofs/cgif/cgif_file_fuzzer/lib/A/ACfi.v (link_ML, link_SMP, link_FFL, link_ASF, link_AMEMSET, link_AMEMCPY, tfib_ROB) for libreac/fuzz_grant: the facts are stated at GrantB and at the listing's instance PI_grant, the stack_malloc, bcmp and set_shadow_f5 entries of the memory-checking runtime, the walks' PALib and PALibF records, the shadow of the image and of its registered globals, the image's read-only tables and the image facts of ctrl_finish and reac_ctrl_parse are added; module paths changed. *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_grant/lib/A/Prog/GrantClose.v (sections 6, the shadow of the
   image and of its registered globals) and lib/A/Prog/GrantCloseChk.v (the computable checks), with the binder form of
   proofs/libreac/fuzz_identity/lib/A/Rt/WrapBinders.v, all at origin/ossv/recipes 6ebe35ba632; taken for reac-pw/fuzz_pin
   image A: the checks are stated over any segment list and symbol record (the granule check of a registered global
   allows a zero cell in place of a zero range, the hull check runs per object, and a tail check for the bytes musl's word
   loops read past a NUL is added); they discharge PPgCSpec.pin_ro_law (the one image fact the program walks take) and
   bind the program walks' runtime hypotheses at fuzz_pin.asan's own record TfibB; module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the asan-ubsan twin of lib/A/PinWrapBinders.v of this library, for reac-pw/fuzz_pin's
   image B (fuzz_pin.asan-ubsan, sha256 d6f83d30152279dadae39fc626707a0037090a8909a186dac3c362b12088201f), written by hand
   from that file. Part 1 (the checks and what they say, stated over any segment list and symbol record) is the A file's
   text unchanged. Part 2 binds the same hypotheses at image B's record lib/AU/YD2l.v TfibB: the imports are image B's
   lib/AU twins (AWalkFw0 YF0l YF0m YD2l YCeg YCeh YE2k YE2s YE2q YF0s, lib/AU/Rt, lib/AU/PPgSat, PPgLib, PPgWrapNcmp;
   the shared text lib/A/PPgWrap.v is the same); law_chk is computed on image B's segments and start-up tables; the
   numbers of pin_tfib_lib and pin_ROB are image B's (errno 0x5d45f4 = lib/AU/YF0m.v TFIB_ERRNO, the table
   fuzz_catalogue 0x98000 .. 0x98cb8 = lib/AU/YCeh.v lib_const_addr, the read-only window 0x97c20 .. 0x99e68); the
   wrapper and runtime binders are image B's walks of the same entries (the wrappers and the runtime are at the same
   addresses in both images). *)
(* The binders of fuzz_pin's image-A program walks: each Section hypothesis of the walks about the image, the
   memory-checking runtime and its wrappers, proved at fuzz_pin.asan's own symbol record TfibB (lib/A/AD2l.v), so that
   lib/A/AD2o.v closes the program contract with none left. Rule 24: proves no function (kind: binding). *)
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK11 YK04 YA0i YA0n YP09 YI04 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Prog Require Import pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require Import PPgBase PPgCSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ================================ the checks [GrantCloseChk.v:20-67] ================================ *)
Definition in_zr_b (a : Z) (r : Z * Z) : bool := ((fst r <=? a) && (a <? fst r + snd r))%bool.

Definition in_ro_b (segs : list Segment) (rlo rhi a : Z) : bool :=
  (existsb (fun s : Segment => negb (seg_writable s) && (Z.of_N (seg_base s) <=? a) &&
                               (a <? Z.of_N (seg_base s) + Z.of_N (seg_size s))) segs
   || ((rlo <=? a) && (a <? rhi)))%bool.

(* The byte at a is a read-only byte that arodata_okP speaks of. *)
Definition ro_free_b (segs : list Segment) (rlo rhi : Z) (own : list (Z * Z)) (errno : Z) (a : Z) : bool :=
  (in_ro_b segs rlo rhi a && negb (existsb (in_zr_b a) own) &&
   negb ((errno <=? a) && (a <? errno + 4)))%bool.

(* ... and the image holds v there. *)
Definition ro_read_b (segs : list Segment) (rlo rhi : Z) (own : list (Z * Z)) (errno : Z) (a v : Z) : bool :=
  (ro_free_b segs rlo rhi own errno a &&
   match seg_rom segs (Z_to_bv 64 a) with Some b => bv_unsigned b =? v | None => false end)%bool.

Definition tbl_chk (segs : list Segment) (rlo rhi : Z) (own : list (Z * Z)) (errno : Z) (base : Z) (l : list Z) : bool :=
  forallb (fun j => ro_read_b segs rlo rhi own errno (base + Z.of_nat j) (nth j l 0)) (seq 0 (length l)).

(* The shadow byte at s is one of the given one-byte cells (with value v). *)
Definition is_shc (s : Z) (c : acell) : bool :=
  match c with ACell (ANum s') (S O) (AV (ANum _)) => Z.eqb s' s | _ => false end.
Definition is_shv (s v : Z) (c : acell) : bool :=
  match c with ACell (ANum s') (S O) (AV (ANum v')) => (Z.eqb s' s && Z.eqb v' v)%bool | _ => false end.

(* The end (in granules) of the zero-shadow range that holds granule k, if one does. *)
Fixpoint zfind (k : Z) (zs : list (Z * Z)) : option Z :=
  match zs with
  | [] => None
  | (q, m) :: r => if ((q / 8 <=? k) && (k <? (q + m) / 8))%bool then Some ((q + m) / 8) else zfind k r
  end.

(* Every granule of [k, hi) is in a range of zs or has a cell in cells. *)
Fixpoint vscan (zs : list (Z * Z)) (cells : list acell) (fuel : nat) (k hi : Z) : bool :=
  match fuel with
  | O => false
  | S f =>
      if hi <=? k then true else
      match zfind k zs with
      | Some e => vscan zs cells f e hi
      | None => (existsb (is_shc (SHADOW_OFF + k)) cells && vscan zs cells f (k + 1) hi)%bool
      end
  end.

(* A registered global of n bytes at p: granule i must hold 0 below n / 8 and n mod 8 at the last partial granule;
   a zero granule may come from a zero range or from a zero cell. *)
Definition gran_val (n i : Z) : Z := if i <? n / 8 then 0 else n mod 8.
Definition gran_ok (zs : list (Z * Z)) (cells : list acell) (p n i : Z) : bool :=
  (((gran_val n i =? 0) && match zfind (p / 8 + i) zs with Some _ => true | None => false end)
   || existsb (is_shv (SHADOW_OFF + p / 8 + i) (gran_val n i)) cells)%bool.
Definition blk_chk (zs : list (Z * Z)) (cells : list acell) (p n : Z) : bool :=
  ((p mod 8 =? 0) && (0 <=? n) &&
   forallb (fun i => gran_ok zs cells p n (Z.of_nat i)) (seq 0 (Z.to_nat ((n + 7) / 8))))%bool.

(* The shadow bytes of the 8-byte shadow words around [x, x + n) are readable. The fuel is computed from the bounds,
   not a numeral: a numeral fuel lets conversion unfold vscan on symbolic bounds. *)
Definition hull_lo (x : Z) : Z := shadow_addr x / 8 * 8 - SHADOW_OFF.
Definition hull_hi (x n : Z) : Z := shadow_addr (x + n - 1) / 8 * 8 + 8 - SHADOW_OFF.
Definition hull_chk (zs : list (Z * Z)) (cells : list acell) (x n : Z) : bool :=
  vscan zs cells (Z.to_nat (hull_hi x n - hull_lo x + 1)) (hull_lo x) (hull_hi x n).

(* The byte a is readable: a read-only byte arodata_okP speaks of that the image holds, or a byte of a cell. *)
Definition cov_b (a : Z) (c : acell) : bool :=
  match c with ACell (ANum a0) w (AV _) => ((a0 <=? a) && (a <? a0 + Z.of_nat w))%bool | _ => false end.
Definition vis_b (segs : list Segment) (rlo rhi : Z) (own : list (Z * Z)) (errno : Z) (cs : list acell) (a : Z) : bool :=
  ((ro_free_b segs rlo rhi own errno a && match seg_rom segs (Z_to_bv 64 a) with Some _ => true | None => false end)
   || existsb (cov_b a) cs)%bool.
(* The bytes after x up to the end of x's 8-byte word (pin_str_tail). *)
Definition tail_chk (segs : list Segment) (rlo rhi : Z) (own : list (Z * Z)) (errno : Z) (cs : list acell) (x : Z) : bool :=
  forallb (fun j => vis_b segs rlo rhi own errno cs (x + 1 + Z.of_nat j)) (seq 0 (Z.to_nat (7 - x mod 8))).

Definition amem_range_b (p n : Z) : bool :=
  ((p + n <=? kLowMemEnd - 1) || ((kHighMemBeg <=? p) && (p + n <=? kHighMemEnd - 1)))%bool.

(* A read-only string at x with bytes l, inside a registered global of sz bytes at x. *)
Definition str_chk (segs : list Segment) (rlo rhi : Z) (own : list (Z * Z)) (errno : Z) (zs : list (Z * Z))
    (cells cs : list acell)
    (x sz : Z) (l : list byte) : bool :=
  let n := Z.of_nat (length l) + 1 in
  ((0 <? x) && (x + n <=? 2 ^ 63) && (n <? 2 ^ 32) && amem_range_b x (Z.of_nat (length l) + 8) && (n <=? sz) &&
   tbl_chk segs rlo rhi own errno x (pin_zbytes l ++ [0]) && blk_chk zs cells x sz && hull_chk zs cells x n &&
   tail_chk segs rlo rhi own errno cs (x + Z.of_nat (length l)))%bool.

Definition le8 (v : Z) : list Z := map (fun k => YO0f.le_byte v 8 k) (seq 0 8).

(* pin_ro_law's whole check: the table (its own shadow, its 22 pointers, its 11 tokens) and the ':' set. *)
Definition law_chk (segs : list Segment) (rlo rhi : Z) (own : list (Z * Z)) (errno : Z) (zs : list (Z * Z))
    (cells cs : list acell)
    (cat : Z) (TP DP : nat -> Z) (TSZ : nat -> Z) (colonp colsz : Z) : bool :=
  ((0 <? cat) && (cat mod 8 =? 0) && (cat + CAT_BYTES <=? 2 ^ 63) && amem_range_b cat CAT_BYTES &&
   blk_chk zs cells cat CAT_BYTES &&
   forallb (fun i =>
     tbl_chk segs rlo rhi own errno (row_addr cat i) (le8 (TP i)) &&
     tbl_chk segs rlo rhi own errno (row_addr cat i + 8) (le8 (DP i)) &&
     (0 <=? TP i) && (TP i <? 2 ^ 64) && (0 <=? DP i) && (DP i <? 2 ^ 64) &&
     str_chk segs rlo rhi own errno zs cells cs (TP i) (TSZ i) (tok_bytes i)) (seq 0 CAT_N) &&
   str_chk segs rlo rhi own errno zs cells cs colonp colsz pin_colon_bytes)%bool.

(* ================================ what the checks say [GrantCloseChk.v:69-151] ================================ *)
Lemma in_ro_b_ok : forall segs rlo rhi a, in_ro_b segs rlo rhi a = true -> in_roP segs rlo rhi a.
Proof.
intros segs rlo rhi a H. unfold in_ro_b in H. apply orb_true_iff in H as [H|H].
- left. apply existsb_exists in H as (s & Hs & Hb). apply andb_prop in Hb as [Hb H2]. apply andb_prop in Hb as [Hw H1].
  apply negb_true_iff in Hw. apply Z.leb_le in H1. apply Z.ltb_lt in H2. exists s. split; [exact Hs|]. split; [exact Hw | lia].
- right. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.

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

Lemma le_byte1' : forall v, 0 <= v < 256 -> YO0f.le_byte v 1 0 = v.
Proof. exact le_byte1. Qed.

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
  exists q, m. split; [left; reflexivity|]. split; [lia | reflexivity].
- destruct (IH e H) as (q' & m' & Hin & Hk & He). exists q', m'. split; [right; exact Hin|]. split; [exact Hk | exact He].
Qed.

Lemma vscan_ok : forall zs cells fuel k hi, vscan zs cells fuel k hi = true -> forall j, k <= j < hi ->
  (exists q m, In (q, m) zs /\ q / 8 <= j < (q + m) / 8) \/
  existsb (is_shc (SHADOW_OFF + j)) cells = true.
Proof.
intros zs cells. induction fuel as [|f IH]; intros k hi H j Hj; cbn [vscan] in H; [discriminate|].
destruct (hi <=? k) eqn:E; [apply Z.leb_le in E; exfalso; lia|].
destruct (zfind k zs) as [e|] eqn:Ez.
- destruct (zfind_some _ _ _ Ez) as (q & m & Hin & Hk & ->).
  destruct (Z_lt_le_dec j ((q + m) / 8)) as [Hlt|Hge].
  + left. exists q, m. split; [exact Hin | lia].
  + exact (IH _ _ H j (conj Hge (proj2 Hj))).
- apply andb_prop in H as [Hc H]. destruct (Z.eq_dec j k) as [->|Hne]; [right; exact Hc|].
  apply (IH _ _ H). lia.
Qed.

Lemma nth_map_seq : forall (f : nat -> Z) n s k, (k < n)%nat -> nth k (map f (seq s n)) 0 = f (s + k)%nat.
Proof.
induction n as [|n IH]; intros s k Hk; [lia|].
destruct k as [|k]; cbn [seq map nth]; [f_equal; lia|]. rewrite IH by lia. f_equal. lia.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ---- read-only bytes of the image [GrantCloseChk.v:155-219] ---- *)
Lemma ro_free_ok : forall segs rlo rhi B a, ro_free_b segs rlo rhi (as_owned_static B) (as_errno B) a = true ->
  in_roP segs rlo rhi a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros segs rlo rhi B a Hb. unfold ro_free_b in Hb.
apply andb_prop in Hb as [Hb Herr]. apply andb_prop in Hb as [Hro Hown].
apply negb_true_iff in Hown. apply negb_true_iff in Herr.
split; [exact (in_ro_b_ok _ _ _ _ Hro)|]. split; [exact (not_Exists_in_zr _ _ Hown)|].
intros [E1 E2].
assert (X : ((as_errno B <=? a) && (a <? as_errno B + 4))%bool = true)
  by (apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
congruence.
Qed.

Lemma arodata_aview : forall segs rlo rhi B a v (H : word -> bool) mem,
  ro_read_b segs rlo rhi (as_owned_static B) (as_errno B) a v = true -> arodata_okP segs rlo rhi B (aview segs H mem) ->
  aview segs H mem a = Some v.
Proof.
intros segs rlo rhi B a v H mem Hb HR. unfold ro_read_b in Hb.
apply andb_prop in Hb as [Hf Hrom]. destruct (ro_free_ok _ _ _ _ _ Hf) as (Hro & Hown & He).
pose proof (HR a Hro Hown He) as Ha.
destruct (seg_rom segs (Z_to_bv 64 a)) as [b|] eqn:Eb; [|discriminate Hrom].
cbv beta iota in Hrom. apply Z.eqb_eq in Hrom. subst v. cbn [option_map] in Ha. exact Ha.
Qed.

Lemma arodata_byte : forall segs rlo rhi B a v (H : word -> bool) mem,
  ro_read_b segs rlo rhi (as_owned_static B) (as_errno B) a v = true -> arodata_okP segs rlo rhi B (aview segs H mem) ->
  val_mem segs (mrestrict H mem) a 1 v /\ 0 <= v < 256.
Proof.
intros segs rlo rhi B a v H mem Hb HR.
pose proof (arodata_aview segs rlo rhi B a v H mem Hb HR) as Ha. unfold aview in Ha.
destruct (mbyte segs (mrestrict H mem) a) as [b|] eqn:Em; [|discriminate Ha].
cbn [option_map] in Ha. injection Ha as Hbb. subst v.
pose proof (bv_unsigned_in_range 8 b) as Hr. unfold bv_modulus in Hr. cbn [Z.of_N] in Hr. change (2 ^ 8) with 256 in Hr.
split; [|lia].
intros k Hk. assert (Hk0 : k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r, Em. f_equal.
rewrite (le_byte1' (bv_unsigned b) Hr). symmetry. apply Z_to_bv_bv_unsigned.
Qed.

Lemma arodata_garr8 : forall segs rlo rhi B base l (H : word -> bool) mem,
  tbl_chk segs rlo rhi (as_owned_static B) (as_errno B) base l = true ->
  arodata_okP segs rlo rhi B (aview segs H mem) -> garr8 segs (mrestrict H mem) base l.
Proof.
intros segs rlo rhi B base l H mem Hc HR j Hj.
apply (arodata_byte segs rlo rhi B _ _ H mem); [|exact HR].
unfold tbl_chk in Hc. rewrite forallb_forall in Hc. apply Hc. apply in_seq. lia.
Qed.

Lemma garr8_val_mem : forall segs mem base n v,
  garr8 segs mem base (map (fun k => YO0f.le_byte v n k) (seq 0 n)) -> val_mem segs mem base n v.
Proof.
intros segs mem base n v HG k Hk.
assert (Hl : (k < length (map (fun k => YO0f.le_byte v n k) (seq 0 n)))%nat) by (rewrite length_map, length_seq; exact Hk).
destruct (HG k Hl) as [Hv Hr].
rewrite (nth_map_seq _ n 0 k Hk) in Hv, Hr. cbn [Nat.add] in Hv, Hr.
specialize (Hv 0%nat ltac:(lia)). cbn [Z.of_nat] in Hv. rewrite Z.add_0_r in Hv.
rewrite Hv. f_equal. f_equal. exact (le_byte1' _ Hr).
Qed.

(* ---- the shadow, from the allocator relation [GrantClose.v:199-264, IdentRo.v:47-62] ---- *)
Section s.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.

(* A one-byte cell of the record holds its byte in every state of the allocator relation. *)
Lemma cell1_rd : forall ly S (W : world segs) mem md s v,
  AR segs B ly S W mem md -> In (z1 (ANum s) v) (as_const B ly) ->
  aview segs (w_H W) mem s = Some (YG0f.le_byte v 1 0).
Proof.
intros ly S W mem md s v HAR Hin.
pose proof (am_const _ _ _ _ (proj1 HAR)) as HC. rewrite Forall_forall in HC.
specialize (HC _ Hin). unfold cell_holds, z1, c1 in HC. cbn [c_at c_val c_w aeval] in HC.
specialize (HC 0%nat ltac:(lia)). cbn [Z.of_nat] in HC. rewrite Z.add_0_r in HC. exact HC.
Qed.

(* Any byte a cell of the record covers is readable in every state of the allocator relation. *)
Lemma cell_cov_rd : forall ly S (W : world segs) mem md c a,
  AR segs B ly S W mem md -> In c (as_const B ly) -> cov_b a c = true -> aview segs (w_H W) mem a <> None.
Proof.
intros ly S W mem md [ca cw cv] a HAR Hin Hb.
pose proof (am_const _ _ _ _ (proj1 HAR)) as HC. rewrite Forall_forall in HC.
specialize (HC _ Hin). unfold cov_b in Hb.
destruct ca as [a0 | ? | ? | ? | ? | ? | ? | ? | ? ? | ? | ? | ? | ? | ? | ? | ? | ? | ? | ?]; cbv beta iota in Hb;
  try discriminate Hb.
destruct cv as [e|m0 v0]; cbv beta iota in Hb; try discriminate Hb.
apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
unfold cell_holds in HC. cbn [c_at c_val c_w aeval] in HC.
specialize (HC (Z.to_nat (a - a0)) ltac:(lia)). rewrite Z2Nat.id in HC by lia.
replace (a0 + (a - a0)) with a in HC by lia. rewrite HC. discriminate.
Qed.

(* A granule of a zero-shadow range of the record has shadow byte 0 in every state. *)
Lemma zs_rd : forall ly S (W : world segs) mem md q m j,
  AR segs B ly S W mem md -> In (q, m) (as_zero_shadow B) -> q / 8 <= j < (q + m) / 8 ->
  aview segs (w_H W) mem (SHADOW_OFF + j) = Some 0.
Proof.
intros ly S W mem md q m j HAR Hin Hj.
pose proof (am_syms _ _ _ _ (proj1 HAR)) as HS.
pose proof (proj1 (Forall_forall _ _) (aso_zshadow B HS) (q, m) Hin) as (Hq0 & Hm0 & Hq & Hm & _). cbn [fst snd] in *.
pose proof (al_zshadow _ _ LAWS ly S W mem md (q, m) HAR (or_intror Hin)) as Hz. cbn [fst snd] in Hz.
assert (E : (q + m) / 8 = q / 8 + m / 8).
{ pose proof (Z.div_mod q 8 ltac:(lia)) as Dq.
  replace (q + m) with (m + q / 8 * 8) by lia. rewrite Z.div_add by lia. lia. }
replace (SHADOW_OFF + j) with (shadow_of_addr SHADOW_OFF q + (j - q / 8)) by (unfold shadow_of_addr; lia).
apply Hz. lia.
Qed.

Variable cells : list acell.
Hypothesis CELLS : forall ly, incl cells (as_const B ly).
Variable cs : list acell.
Hypothesis CS : forall ly, incl cs (as_const B ly).

Lemma gran_rd : forall ly S (W : world segs) mem md p n i,
  AR segs B ly S W mem md -> gran_ok (as_zero_shadow B) cells p n i = true -> 0 <= gran_val n i < 256 ->
  aview segs (w_H W) mem (SHADOW_OFF + p / 8 + i) = Some (gran_val n i).
Proof.
intros ly S W mem md p n i HAR Hb Hv. unfold gran_ok in Hb. apply orb_true_iff in Hb as [Hb|Hb].
- apply andb_prop in Hb as [H0 Hz]. apply Z.eqb_eq in H0. rewrite H0.
  destruct (zfind (p / 8 + i) (as_zero_shadow B)) as [e|] eqn:Ez; [|discriminate Hz].
  destruct (zfind_some _ _ _ Ez) as (q & m & Hin & Hk & _).
  replace (SHADOW_OFF + p / 8 + i) with (SHADOW_OFF + (p / 8 + i)) by lia.
  exact (zs_rd ly S W mem md q m (p / 8 + i) HAR Hin Hk).
- apply existsb_exists in Hb as (c & Hc & Hcb). apply is_shv_eq in Hcb. subst c.
  rewrite (cell1_rd ly S W mem md _ _ HAR (CELLS ly _ Hc)). rewrite le_byte1 by exact Hv. reflexivity.
Qed.

Lemma gran_val_range : forall n i, 0 <= gran_val n i < 8.
Proof. intros n i. unfold gran_val. destruct (i <? n / 8); [lia|]. pose proof (Z.mod_pos_bound n 8 ltac:(lia)). lia. Qed.

Lemma blk_shadow : forall ly S (W : world segs) mem md p n,
  AR segs B ly S W mem md -> blk_chk (as_zero_shadow B) cells p n = true ->
  block_shadow (aview segs (w_H W) mem) SHADOW_OFF p n.
Proof.
intros ly S W mem md p n HAR Hb. unfold blk_chk in Hb.
apply andb_prop in Hb as [Hb Hall]. apply andb_prop in Hb as [Hp Hn].
apply Z.eqb_eq in Hp. apply Z.leb_le in Hn.
split; [exact Hp|]. split; [exact Hn|]. intros i Hi.
rewrite forallb_forall in Hall.
assert (Hin : In (Z.to_nat i) (seq 0 (Z.to_nat ((n + 7) / 8)))) by (apply in_seq; lia).
specialize (Hall _ Hin). cbv beta in Hall. rewrite Z2Nat.id in Hall by lia.
pose proof (gran_val_range n i) as Hv.
unfold shadow_of_addr.
exact (gran_rd ly S W mem md p n i HAR Hall ltac:(lia)).
Qed.

Lemma hull_vis : forall ly S (W : world segs) mem md x n,
  AR segs B ly S W mem md -> hull_chk (as_zero_shadow B) cells x n = true ->
  shadow_hull_vis (aview segs (w_H W) mem) x n.
Proof.
intros ly S W mem md x n HAR Hb s Hs. unfold hull_chk in Hb.
assert (Hj : hull_lo x <= s - SHADOW_OFF < hull_hi x n) by (unfold hull_lo, hull_hi; lia).
destruct (vscan_ok _ _ _ _ _ Hb (s - SHADOW_OFF) Hj) as [(q & m & Hin & Hq) | Hc].
- replace s with (SHADOW_OFF + (s - SHADOW_OFF)) by lia.
  rewrite (zs_rd ly S W mem md q m (s - SHADOW_OFF) HAR Hin Hq). discriminate.
- apply existsb_exists in Hc as (c & Hin & Hb'). destruct (is_shc_eq _ _ Hb') as [v ->].
  replace s with (SHADOW_OFF + (s - SHADOW_OFF)) by lia.
  rewrite (cell1_rd ly S W mem md _ v HAR (CELLS ly _ Hin)). discriminate.
Qed.

Variables RLO RHI : Z.

Lemma tail_vis : forall ly S (W : world segs) mem md x,
  AR segs B ly S W mem md -> arodata_okP segs RLO RHI B (aview segs (w_H W) mem) ->
  tail_chk segs RLO RHI (as_owned_static B) (as_errno B) cs x = true -> pin_str_tail (aview segs (w_H W) mem) x.
Proof.
intros ly S W mem md x HAR HRO Hb a Ha. unfold tail_chk in Hb. rewrite forallb_forall in Hb.
pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Hx8.
assert (Hin : In (Z.to_nat (a - x - 1)) (seq 0 (Z.to_nat (7 - x mod 8)))) by (apply in_seq; lia).
specialize (Hb _ Hin). cbv beta in Hb. rewrite Z2Nat.id in Hb by lia. replace (x + 1 + (a - x - 1)) with a in Hb by lia.
unfold vis_b in Hb. apply orb_true_iff in Hb as [Hb|Hb].
- apply andb_prop in Hb as [Hf Hr]. destruct (ro_free_ok _ _ _ _ _ Hf) as (Hro & Hown & He).
  rewrite (HRO a Hro Hown He). destruct (seg_rom segs (Z_to_bv 64 a)); [cbn; discriminate | discriminate Hr].
- apply existsb_exists in Hb as (c & Hc & Hcb). exact (cell_cov_rd ly S W mem md c a HAR (CS ly _ Hc) Hcb).
Qed.

Lemma amem_range_of_b : forall p n, amem_range_b p n = true -> amem_range p n.
Proof.
intros p n H. unfold amem_range_b in H. unfold amem_range.
apply orb_true_iff in H as [H|H]; [left; apply Z.leb_le; exact H|].
right. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

Lemma ro_str_of_chk : forall ly S (W : world segs) mem md x sz l,
  AR segs B ly S W mem md -> arodata_okP segs RLO RHI B (aview segs (w_H W) mem) ->
  str_chk segs RLO RHI (as_owned_static B) (as_errno B) (as_zero_shadow B) cells cs x sz l = true ->
  pin_ro_str segs (mrestrict (w_H W) mem) (aview segs (w_H W) mem) x l.
Proof.
intros ly S W mem md x sz l HAR HRO Hb. unfold str_chk in Hb. cbv zeta in Hb.
apply andb_prop in Hb as [Hb H9]. apply andb_prop in Hb as [Hb H8]. apply andb_prop in Hb as [Hb H7].
apply andb_prop in Hb as [Hb H6]. apply andb_prop in Hb as [Hb H5]. apply andb_prop in Hb as [Hb H4].
apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2].
apply Z.ltb_lt in H1. apply Z.leb_le in H2. apply Z.ltb_lt in H3. apply Z.leb_le in H5.
unfold pin_ro_str.
rewrite Z.add_assoc in H2.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
split; [exact (amem_range_of_b _ _ H4)|].
split; [exact (arodata_garr8 segs RLO RHI B x _ (w_H W) mem H6 HRO)|].
split; [exact (block_shadow_range _ _ x sz x _ (blk_shadow ly S W mem md x sz HAR H7) (Z.le_refl x)
                (proj1 (Z.add_le_mono_l _ _ x) H5))|].
split; [exact (hull_vis ly S W mem md x _ HAR H8)|].
exact (tail_vis ly S W mem md _ HAR HRO H9).
Qed.

(* PPgCSpec.pin_ro_law from law_chk: the bytes from the image under arodata_okP, the shadow from the allocator
   relation's zero-shadow ranges and one-byte cells, the tail bytes from the image or from the record's cells. *)
Theorem pin_ro_law_of_chk : forall cat TP DP TSZ colonp colsz,
  law_chk segs RLO RHI (as_owned_static B) (as_errno B) (as_zero_shadow B) cells cs cat TP DP TSZ colonp colsz = true ->
  pin_ro_law segs B RLO RHI cat TP DP colonp.
Proof.
intros cat TP DP TSZ colonp colsz Hb ly' S' W' mem' md' HAR HRO. unfold law_chk in Hb.
apply andb_prop in Hb as [Hb Hcol]. apply andb_prop in Hb as [Hb Hrows]. apply andb_prop in Hb as [Hb Hblk].
apply andb_prop in Hb as [Hb Hamr]. apply andb_prop in Hb as [Hb Hhi]. apply andb_prop in Hb as [Hlo H8].
apply Z.ltb_lt in Hlo. apply Z.eqb_eq in H8. apply Z.leb_le in Hhi.
split.
- unfold pin_cat_ok. split; [exact Hlo|]. split; [exact H8|]. split; [exact Hhi|].
  split; [exact (amem_range_of_b _ _ Hamr)|].
  split; [exact (block_shadow_range _ _ cat CAT_BYTES cat CAT_BYTES (blk_shadow ly' S' W' mem' md' cat CAT_BYTES HAR Hblk)
                  (Z.le_refl cat) (Z.le_refl (cat + CAT_BYTES)))|].
  intros i Hi. rewrite forallb_forall in Hrows.
  assert (Hin : In i (seq 0 CAT_N)) by (apply in_seq; lia).
  specialize (Hrows i Hin). cbv beta in Hrows.
  apply andb_prop in Hrows as [Hrows S1]. apply andb_prop in Hrows as [Hrows B4]. apply andb_prop in Hrows as [Hrows B3].
  apply andb_prop in Hrows as [Hrows B2]. apply andb_prop in Hrows as [Hrows B1]. apply andb_prop in Hrows as [T1 T2].
  apply Z.leb_le in B1. apply Z.ltb_lt in B2. apply Z.leb_le in B3. apply Z.ltb_lt in B4.
  split; [exact (garr8_val_mem segs _ _ 8%nat _ (arodata_garr8 segs RLO RHI B _ _ (w_H W') mem' T1 HRO))|].
  split; [exact (garr8_val_mem segs _ _ 8%nat _ (arodata_garr8 segs RLO RHI B _ _ (w_H W') mem' T2 HRO))|].
  split; [exact (conj B1 B2)|]. split; [exact (conj B3 B4)|].
  exact (ro_str_of_chk ly' S' W' mem' md' (TP i) _ (tok_bytes i) HAR HRO S1).
- exact (ro_str_of_chk ly' S' W' mem' md' colonp colsz pin_colon_bytes HAR HRO Hcol).
Qed.
End s.
End b.

(* ============================= part 2: the binders at fuzz_pin.asan-ubsan's record TfibB ============================= *)
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YImgTop YG05 YG0q YG0t.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU Require AWalkFw0 YF0l YF0m YD2l YCeg YCeh YE2k YE2s YE2q YF0s.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require PPgWrap.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU Require PPgSat PPgLib PPgWrapNcmp.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU.Rt Require StrlenDef MemchrDef Strlen Memchr StackMalloc0 Strcspn.

(* The sizes of the eleven token globals (image B's asan_globals, lib/AU/PPgSat.v PIN_GLOBS) and of the ':' set. *)
Definition PIN_TSZ (i : nat) : Z := nth i [6; 6; 7; 12; 6; 6; 7; 7; 7; 7; 7] 0.
Definition PIN_COLSZ : Z := 2.

(* The whole check of pin_ro_law, computed on fuzz_pin.asan-ubsan's segments and its record's start-up tables. *)
Lemma pin_law_chk :
  law_chk AWalkFw0.tfibsegs PPgLib.RO_LO PPgLib.RO_HI (as_owned_static YD2l.TfibB) (as_errno YD2l.TfibB)
    (as_zero_shadow YD2l.TfibB) YF0m.Tfib_const_shadow YF0m.Tfib_const_abs
    PPgSat.PIN_CAT PPgSat.PIN_TP PPgSat.PIN_DP PIN_TSZ PPgSat.PIN_COLONP PIN_COLSZ = true.
Proof. vm_compute. reflexivity. Qed.

Lemma pin_cells_shadow : forall ly, incl YF0m.Tfib_const_shadow (as_const YD2l.TfibB ly).
Proof.
intros ly c Hc. cbn [as_const YD2l.TfibB]. unfold YF0m.Tfib_const.
apply in_or_app. right. apply in_or_app. right. exact Hc.
Qed.
Lemma pin_cells_abs : forall ly, incl YF0m.Tfib_const_abs (as_const YD2l.TfibB ly).
Proof.
intros ly c Hc. cbn [as_const YD2l.TfibB]. unfold YF0m.Tfib_const.
apply in_or_app. right. apply in_or_app. left. exact Hc.
Qed.

Section p. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma pin_LAWS : AR_laws AWalkFw0.tfibsegs YD2l.TfibB.
Proof. exact (YG0q.AR_laws_ok AWalkFw0.tfibsegs YD2l.TfibB). Qed.

(* F-RO-LAW at the real record: the one image fact the harness walk takes as a Section hypothesis and
   reac_box_pin_parse takes as a premise (lib/A/PPgCSpec.v pin_ro_law). *)
Theorem pin_ro_law_TfibB :
  pin_ro_law AWalkFw0.tfibsegs YD2l.TfibB PPgLib.RO_LO PPgLib.RO_HI PPgSat.PIN_CAT PPgSat.PIN_TP PPgSat.PIN_DP
    PPgSat.PIN_COLONP.
Proof.
exact (pin_ro_law_of_chk AWalkFw0.tfibsegs YD2l.TfibB pin_LAWS YF0m.Tfib_const_shadow pin_cells_shadow
  YF0m.Tfib_const_abs pin_cells_abs PPgLib.RO_LO PPgLib.RO_HI PPgSat.PIN_CAT PPgSat.PIN_TP PPgSat.PIN_DP PIN_TSZ
  PPgSat.PIN_COLONP PIN_COLSZ pin_law_chk).
Qed.

(* The image record of the program walks (lib/AU/YCeh.v TfibLib), in the form of fuzz_knock's lib/A/APgImgLink.v
   tfibX_lib: the table fuzz_catalogue 0x98000 .. 0x98cb8 (lib_const_addr) is not one of the runtime's own areas. *)
Theorem pin_tfib_lib : YCeh.TfibLib YD2l.TfibB.
Proof.
constructor; try reflexivity.
- cbn [as_errno YD2l.TfibB]. unfold YF0m.TFIB_ERRNO, kLowMemEnd. lia.
- intros a Ha. cbn [as_errno YD2l.TfibB] in Ha. unfold YF0m.TFIB_ERRNO in Ha. unfold in_img.
  assert (C : existsb (fun s : Segment => (Z.of_N (seg_base s) <=? 0x5d45f4) &&
                (0x5d45f4 + 4 <=? Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool AWalkFw0.tfibsegs = true)
    by (vm_compute; reflexivity).
  apply existsb_exists in C as (sg & Hin & Hb). apply andb_prop in Hb as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2.
  exists sg. split; [exact Hin | lia].
- intros a Ha. unfold YCeh.lib_const_addr in Ha. cbn [as_owned_static as_errno YD2l.TfibB]. split.
  + assert (C : forallb (fun r => ((fst r + snd r <=? 0x98000) || (0x98cb8 <=? fst r)))%bool YF0m.Tfib_owned_static = true)
      by (vm_compute; reflexivity).
    intros HE. apply Exists_exists in HE as (r & Hr & Hz). unfold in_zr in Hz.
    rewrite forallb_forall in C. specialize (C r Hr).
    apply orb_true_iff in C as [C|C]; apply Z.leb_le in C; lia.
  + unfold YF0m.TFIB_ERRNO. lia.
- cbn [as_gp YD2l.TfibB]. unfold YF0m.TFIB_GP. lia.
Qed.

(* The image's read-only range lies below the sink's overflow head (lib/AU/YCeh.v ro_tfa_below_ofl), in the form of
   fuzz_grant's lib/A/Prog/GrantClose.v grant_RO: every read-only segment ends below it, and so does the window
   0x97c20 .. 0x99e68 (.data.rel.ro .. .got). *)
Lemma pin_ROB : @YCeh.ro_tfa_below_ofl YE2k.tfib_sink_head.
Proof.
intros a [(s & Hin & Hw & Hr) | Hr]; cbn [YI16.sk_ofl_head YE2k.tfib_sink_head].
- assert (C : forallb (fun s : Segment => seg_writable s ||
                (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? YE2k.A_ofl_head))%bool AWalkFw0.tfibsegs = true)
    by (vm_compute; reflexivity).
  pose proof (proj1 (forallb_forall _ _) C s Hin) as Hb. cbv beta in Hb. rewrite Hw in Hb. cbn [orb] in Hb.
  apply Z.leb_le in Hb. lia.
- unfold YE2k.A_ofl_head. lia.
Qed.

(* The links of the walks at TfibB, in the form of fuzz_knock's lib/A/APgLib.v:254-276 and fuzz_grant's
   lib/A/Prog/GrantClose.v:120-140, 177-180. *)
Lemma pin_ML : model_laws (as_universe YD2l.TfibB).
Proof. exact (YG05.model_laws_ok (as_universe YD2l.TfibB) (YF0m.ts_universe YD2l.TfibB YD2l.TfibB_syms)). Qed.
Lemma pin_SMP : stack_malloc_progressP YD2l.TfibB.
Proof. intros s cid W Hc Hn. exact (YG05.stack_malloc_progress (as_universe YD2l.TfibB) s cid W Hc Hn). Qed.
Lemma pin_FFL : frame_flag_lawP AWalkFw0.tfibsegs YD2l.TfibB.
Proof.
intros ly S W mem md cid pos HAR Hin.
destruct (al_flag _ _ pin_LAWS ly S W mem md cid pos HAR Hin) as (Hp & Ho & Happ & Hceil).
destruct (al_client_img _ _ pin_LAWS ly S W mem md (flag_addr ly cid pos) HAR) as [Hhull Himg].
{ right. right. exists cid, pos. split; [exact Hin | reflexivity]. }
pose proof HAR as (M & L & _). pose proof (YCeh.tfib_img_cover ly S md L) as [C1 C2].
unfold YCeh.TFIB_IMG_LO, YCeh.TFIB_IMG_END, YImgTop.IMG_LO, YImgTop.IMG_TOP in C1, C2.
destruct Happ as [H4096 Hz]. unfold in_zr in Hhull.
split; [exact Hp|]. split; [exact Ho|]. split.
- split; [|exact Himg]. unfold app_addr, in_app, ASAN_CEIL in *. lia.
- split; [exact H4096|]. split; [|exact Hceil].
  unfold zone2, off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.
Lemma pin_ASF : astack_free_law AWalkFw0.tfibsegs YD2l.TfibB.
Proof. exact (YG0t.astack_free_law_ok AWalkFw0.tfibsegs YD2l.TfibB). Qed.
(* the side stack for frames: class 0 for reac_box_pin_parse (jal 0x3c8e4 at image B's 0x80c18), class 1 for
   LLVMFuzzerTestOneInput (jal 0x3ca58 at 0x80724) *)
Lemma pin_ASM0 : astack_malloc_realizes AWalkFw0.tfibsegs YD2l.TfibB 0.
Proof. exact (StackMalloc0.stack_malloc0_contract YD2l.TfibB pin_LAWS YD2l.TfibB_syms). Qed.
Lemma pin_ASM1 : astack_malloc_realizes AWalkFw0.tfibsegs YD2l.TfibB 1.
Proof. exact (YF0s.stack_malloc1_contract YD2l.TfibB pin_LAWS YD2l.TfibB_syms). Qed.

(* The wrapper contracts at their trampolines, each the wrapper walk's theorem at TfibB (the binder form of
   fuzz_identity's lib/A/Rt/WrapBinders.v). *)
Lemma pin_ASTRLEN : StrlenDef.astrlen_realizes AWalkFw0.tfibsegs YD2l.TfibB StrlenDef.STRLEN_ENTRY.
Proof. exact (Strlen.strlen_icpt_contract YD2l.TfibB pin_LAWS YD2l.TfibB_syms). Qed.
Lemma pin_AMEMCHR : MemchrDef.amemchr_realizes AWalkFw0.tfibsegs YD2l.TfibB MemchrDef.MEMCHR_ENTRY.
Proof. exact (Memchr.memchr_icpt_contract YD2l.TfibB pin_LAWS YD2l.TfibB_syms). Qed.
Lemma pin_ABCMP : abcmp_realizes AWalkFw0.tfibsegs YD2l.TfibB 0x41924.
Proof. exact (YE2s.bcmp_icpt_contract YD2l.TfibB pin_LAWS YD2l.TfibB_syms). Qed.
(* __asan_memcpy 0x51a40, the entry LLVMFuzzerTestOneInput calls at image B's 0x8085c (lib/AU/YE2q.v's walk), in the form of
   fuzz_grant's lib/A/Prog/GrantClose.v:167-172 grant_AMEMCPY. *)
Lemma pin_AMEMCPY : aintrin_realizes AWalkFw0.tfibsegs YD2l.TfibB OCpy 0x51a40.
Proof.
intros ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Ham Hra Hhull Hsrc.
exact (YE2q.asan_memcpy_realizes YD2l.TfibB pin_LAWS YD2l.TfibB_syms ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd
  Hdn Hdst Ham Hra Hhull Hsrc).
Qed.
Lemma pin_ASTRCSPN : PPgWrap.astrcspn_realizes AWalkFw0.tfibsegs YD2l.TfibB 0x4191c.
Proof. exact (Strcspn.strcspn_icpt_contract YD2l.TfibB pin_LAWS YD2l.TfibB_syms). Qed.
Lemma pin_ASTRNCMP : PPgWrap.astrncmp_realizes AWalkFw0.tfibsegs YD2l.TfibB 0x41914.
Proof. exact (PPgWrapNcmp.pin_astrncmp YD2l.TfibB YD2l.TfibB_syms). Qed.
End p.
