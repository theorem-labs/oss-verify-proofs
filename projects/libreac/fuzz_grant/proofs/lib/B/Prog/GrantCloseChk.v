(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from part of proofs/libreac/fuzz_grant/lib/A/Prog/GrantClose.v (itself made from part of proofs/cgif/cgif_file_fuzzer/lib/A/ACfi.v) for libreac/fuzz_disco: is_shc, is_shv, zfind, vscan, glob_chk, in_zr_b and their lemmas, and the shadow of the image and of its registered globals, stated at TfibB (lib/A/AD2l.v) and at disco_segs, the segment list of PB_disco; glob_chk accepts a global with no full granule; the byte check of the read-only ranges (byte_free_b, ro_range_b, ro_unowned_of_b) and its registered-globals part (disco_globs_unowned, disco_glob_readable) are added; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoRoClose.v, with its module paths and module names changed; 148 of its 233 lines of code are new or changed and 123 lines of the source are left out. *)
(* Image B (fuzz_grant.asan-ubsan) port of lib/A/Prog/GrantCloseChk.v at a working branch af735a950e2 (arodata_garr8 :191,
   arodata_aview :158, arodata_byte :175, garr8_val_mem :210 and the checks they read): the same text, with its Requires
   pointed at the core (GrantBase -> lib/B/PaBase.v) and at image B's GrantRo.v. At the end, two lemmas this port
   adds (arodata_byte_rom, arodata_garr8_rom): the same step with the check split in two, the image's own bytes checked
   by computation over image B's segments and the two facts about the abstract B (not an owned static, not the errno
   cell) taken as premises, so that the layer can state each IMG_ fact for any B and the closing file discharges the two
   premises at image B's concrete asyms record. *)
(* Computable checks over an image and the lemmas that turn them into the facts the
   walks of lib/A/Prog take: a read-only byte of the image from `arodata_okP`, the
   shadow of the image's read range, and the shadow of a registered global. GrantClose.v
   runs them on fuzz_grant.asan with vm_compute. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK04 YA0i YA0n YP09 YI04 YI00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YO0f.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import GrantRo.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the checks ---------------------------------------------------------------- *)
Definition in_zr_b (a : Z) (r : Z * Z) : bool := ((fst r <=? a) && (a <? fst r + snd r))%bool.

Definition in_ro_b (segs : list Segment) (rlo rhi a : Z) : bool :=
  (existsb (fun s : Segment => negb (seg_writable s) && (Z.of_N (seg_base s) <=? a) &&
                               (a <? Z.of_N (seg_base s) + Z.of_N (seg_size s))) segs
   || ((rlo <=? a) && (a <? rhi)))%bool.

(* The byte at a is a read-only byte that arodata_okP speaks of, and the image holds v there. *)
Definition ro_read_b (segs : list Segment) (rlo rhi : Z) (B : asyms) (a v : Z) : bool :=
  (in_ro_b segs rlo rhi a && negb (existsb (in_zr_b a) (as_owned_static B)) &&
   negb ((as_errno B <=? a) && (a <? as_errno B + 4)) &&
   match seg_rom segs (Z_to_bv 64 a) with Some b => bv_unsigned b =? v | None => false end)%bool.

Definition tbl_chk (segs : list Segment) (rlo rhi : Z) (B : asyms) (base : Z) (l : list Z) : bool :=
  forallb (fun j => ro_read_b segs rlo rhi B (base + Z.of_nat j) (nth j l 0)) (seq 0 (length l)).

(* The shadow byte at s is one of the start-up certificate's one-byte cells. *)
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

(* A registered global's full granules lie in one range of zs, and its last partial
   granule has the cell `size mod 8` in cells. *)
Definition glob_chk (zs : list (Z * Z)) (cells : list acell) (g : Z * Z) : bool :=
  ((fst g mod 8 =? 0) && (0 <=? snd g) &&
   existsb (fun r => (fst r <=? fst g) && (fst g + snd g / 8 * 8 <=? fst r + snd r)) zs &&
   ((snd g mod 8 =? 0) || existsb (is_shv (SHADOW_OFF + fst g / 8 + snd g / 8) (snd g mod 8)) cells))%bool.

(* ---- what the checks say ----------------------------------------------------------- *)
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

Lemma in_zs_of_b : forall B a n,
  existsb (fun r => (fst r <=? a) && (a + n <=? fst r + snd r))%bool (as_zero_shadow B) = true -> in_zs B a n.
Proof.
intros B a n H. apply existsb_exists in H as ([q m] & Hin & Hb). cbn [fst snd] in Hb.
apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
exists q, m. split; [exact Hin|]. lia.
Qed.

Lemma nth_map_seq : forall (f : nat -> Z) n s k, (k < n)%nat -> nth k (map f (seq s n)) 0 = f (s + k)%nat.
Proof.
induction n as [|n IH]; intros s k Hk; [lia|].
destruct k as [|k]; cbn [seq map nth]; [f_equal; lia|]. rewrite IH by lia. f_equal. lia.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ---- read-only bytes of the image ------------------------------------------------ *)
(* A byte the check accepts reads, in any state the read-only view holds in, as the
   image's own byte. *)
Lemma arodata_aview : forall segs rlo rhi B a v (H : word -> bool) mem,
  ro_read_b segs rlo rhi B a v = true -> arodata_okP segs rlo rhi B (aview segs H mem) ->
  aview segs H mem a = Some v.
Proof.
intros segs rlo rhi B a v H mem Hb HR. unfold ro_read_b in Hb.
apply andb_prop in Hb as [Hb Hrom]. apply andb_prop in Hb as [Hb Herr]. apply andb_prop in Hb as [Hro Hown].
apply negb_true_iff in Hown. apply negb_true_iff in Herr.
assert (He : ~ (as_errno B <= a < as_errno B + 4)).
{ intros [E1 E2].
  assert (X : ((as_errno B <=? a) && (a <? as_errno B + 4))%bool = true)
    by (apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
  congruence. }
pose proof (HR a (in_ro_b_ok _ _ _ _ Hro) (not_Exists_in_zr _ _ Hown) He) as Ha.
destruct (seg_rom segs (Z_to_bv 64 a)) as [b|] eqn:Eb; [|discriminate Hrom].
cbv beta iota in Hrom. apply Z.eqb_eq in Hrom. subst v. cbn [option_map] in Ha. exact Ha.
Qed.

Lemma arodata_byte : forall segs rlo rhi B a v (H : word -> bool) mem,
  ro_read_b segs rlo rhi B a v = true -> arodata_okP segs rlo rhi B (aview segs H mem) ->
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

(* One generic lemma for every table of the image: from the read-only view
   (arodata_okP) and the image's own bytes, the table's bytes as garr8. *)
Lemma arodata_garr8 : forall segs rlo rhi B base l (H : word -> bool) mem,
  tbl_chk segs rlo rhi B base l = true ->
  arodata_okP segs rlo rhi B (aview segs H mem) -> garr8 segs (mrestrict H mem) base l.
Proof.
intros segs rlo rhi B base l H mem Hc HR j Hj.
apply (arodata_byte segs rlo rhi B _ _ H mem); [|exact HR].
unfold tbl_chk in Hc. rewrite forallb_forall in Hc. apply Hc. apply in_seq. lia.
Qed.

(* The same table, byte by byte through the reader. *)
Lemma arodata_aview_tbl : forall segs rlo rhi B base l (H : word -> bool) mem,
  tbl_chk segs rlo rhi B base l = true -> arodata_okP segs rlo rhi B (aview segs H mem) ->
  forall j, (j < length l)%nat -> aview segs H mem (base + Z.of_nat j) = Some (nth j l 0).
Proof.
intros segs rlo rhi B base l H mem Hc HR j Hj.
apply (arodata_aview segs rlo rhi B _ _ H mem); [|exact HR].
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

End b.

(* ---- the same step with the check split in two (this port's addition) --------------------------------------- *)
(* The part of ro_read_b that names only the image: the byte is a read-only byte arodata_okP speaks of, and the image
   holds v there. *)
Definition rom_read_b (segs : list Segment) (rlo rhi a v : Z) : bool :=
  (in_ro_b segs rlo rhi a &&
   match seg_rom segs (Z_to_bv 64 a) with Some b => bv_unsigned b =? v | None => false end)%bool.
Definition rom_chk (segs : list Segment) (rlo rhi base : Z) (l : list Z) : bool :=
  forallb (fun j => rom_read_b segs rlo rhi (base + Z.of_nat j) (nth j l 0)) (seq 0 (length l)).
(* The part that names B: no byte of [base, base + n) is an owned static of B or a byte of B's errno cell. *)
Definition ro_free (B : asyms) (base n : Z) : Prop :=
  forall a, base <= a < base + n -> ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma arodata_aview_rom : forall segs rlo rhi B a v (H : word -> bool) mem,
  rom_read_b segs rlo rhi a v = true ->
  ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  arodata_okP segs rlo rhi B (aview segs H mem) -> aview segs H mem a = Some v.
Proof.
intros segs rlo rhi B a v H mem Hb Hown Herr HR. unfold rom_read_b in Hb.
apply andb_prop in Hb as [Hro Hrom].
pose proof (HR a (in_ro_b_ok _ _ _ _ Hro) Hown Herr) as Ha.
destruct (seg_rom segs (Z_to_bv 64 a)) as [b|] eqn:Eb; [|discriminate Hrom].
cbv beta iota in Hrom. apply Z.eqb_eq in Hrom. subst v. cbn [option_map] in Ha. exact Ha.
Qed.
Lemma arodata_byte_rom : forall segs rlo rhi B a v (H : word -> bool) mem,
  rom_read_b segs rlo rhi a v = true ->
  ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  arodata_okP segs rlo rhi B (aview segs H mem) ->
  val_mem segs (mrestrict H mem) a 1 v /\ 0 <= v < 256.
Proof.
intros segs rlo rhi B a v H mem Hb Hown Herr HR.
pose proof (arodata_aview_rom segs rlo rhi B a v H mem Hb Hown Herr HR) as Ha. unfold aview in Ha.
destruct (mbyte segs (mrestrict H mem) a) as [b|] eqn:Em; [|discriminate Ha].
cbn [option_map] in Ha. injection Ha as Hbb. subst v.
pose proof (bv_unsigned_in_range 8 b) as Hr. unfold bv_modulus in Hr. cbn [Z.of_N] in Hr. change (2 ^ 8) with 256 in Hr.
split; [|lia].
intros k Hk. assert (Hk0 : k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r, Em. f_equal.
rewrite (le_byte1' (bv_unsigned b) Hr). symmetry. apply Z_to_bv_bv_unsigned.
Qed.
(* arodata_garr8 with the check split: the image's bytes by computation, B's two facts as premises. *)
Lemma arodata_garr8_rom : forall segs rlo rhi B base l (H : word -> bool) mem,
  rom_chk segs rlo rhi base l = true -> ro_free B base (Z.of_nat (length l)) ->
  arodata_okP segs rlo rhi B (aview segs H mem) -> garr8 segs (mrestrict H mem) base l.
Proof.
intros segs rlo rhi B base l H mem Hc Hf HR j Hj.
destruct (Hf (base + Z.of_nat j) ltac:(lia)) as [Hown Herr].
apply (arodata_byte_rom segs rlo rhi B _ _ H mem); [|exact Hown|exact Herr|exact HR].
unfold rom_chk in Hc. rewrite forallb_forall in Hc. apply Hc. apply in_seq. lia.
Qed.
Lemma arodata_aview_tbl_rom : forall segs rlo rhi B base l (H : word -> bool) mem,
  rom_chk segs rlo rhi base l = true -> ro_free B base (Z.of_nat (length l)) ->
  arodata_okP segs rlo rhi B (aview segs H mem) ->
  forall j, (j < length l)%nat -> aview segs H mem (base + Z.of_nat j) = Some (nth j l 0).
Proof.
intros segs rlo rhi B base l H mem Hc Hf HR j Hj.
destruct (Hf (base + Z.of_nat j) ltac:(lia)) as [Hown Herr].
apply (arodata_aview_rom segs rlo rhi B _ _ H mem); [|exact Hown|exact Herr|exact HR].
unfold rom_chk in Hc. rewrite forallb_forall in Hc. apply Hc. apply in_seq. lia.
Qed.
End c.
