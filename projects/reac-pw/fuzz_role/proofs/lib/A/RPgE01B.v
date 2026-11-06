(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10-29: new file for libreac/fuzz_scene (asan), the start-up certificate of scene's B. *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_scene/lib/A/SceneBCert.v at 6ebe35ba632; restated for reac-pw/fuzz_role image A: the four facts of lib/A/RPgE01S.v, its static law and B's four cell addresses and two code entries, every number read from role's lib/A/AF0m.v and lib/A/RPgImgA.v; the read-only bytes the runtime owns and the .data.rel.ro cells added. *)
(* reac-pw/fuzz_role image A (fuzz_role.asan, pinned sha256
   614cffc0864cc31d9d1ced61322c4efd567b64bc89fe09a227a05b5126e0debb; every address measured on the unstripped twin
   6da77bafc5c050954dd89149e1e55a24064c2211e3cbd351822d1c0a20900ad6, same loaded bytes): THE START-UP CERTIFICATE
   OF THE RUNTIME'S SYMBOL RECORD B FOR SEGMENT S_E01 of the walk of LLVMFuzzerTestOneInput (0x7ff88, ENTRY ->
   K80194, lib/A/RPgE01.v e01_ok). From one hypothesis, `TfibSyms B` (lib/A/AF0m.v, generated from fuzz_role.asan's
   own start-up), it proves:
   - the four facts of B that lib/A/RPgE01S.v e01_static_law takes (e01_globs_marked, e01_img_shadow_vis,
     e01_rom_owned, e01_relro_unowned), and that law at image A's loaded segments and the read-only range
     [0x9a120, 0x9b528);
   - B's four cell addresses (e01_ok's HGOT / HSC / HGU / HUC): each cell of AR's const law is the only cell of its
     width and value in the start-up table, so its address is fixed;
   - the two code entries (e01_ok's HBsm / HBmalloc): __asan_stack_malloc_3 0x3cbfc and the malloc trampoline
     0x52428, from the record's code field.
   The method for the shadow facts is the donor's: the shadow of every granule of the image's range
   [IMG_LO, IMG_TOP) is mapped because it lies in a zero-shadow range of the start-up record (ARm's am_zshadow) or is
   one of its shadow cells (am_const), checked by one boolean scan; each of the 49 registered globals of RPgImgA has
   its full granules in one zero-shadow range and its last partial granule as a shadow cell holding size mod 8,
   checked by one boolean checker. The read-only bytes the runtime owns are each pinned by a const cell whose byte is
   the image's (one checker over the 83 owned ranges: a range that meets no read-only segment is skipped, every
   read-only byte of the others has its pinning cell), and the errno cell lies in no read-only segment. The 31
   .data.rel.ro cells of RPgImgA's hi_cells lie in no owned range and not on the errno cell (one checker).
   proves no function (kind: segment lemma, the start-up certificate of B for S_E01) *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YImgTop YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import Img0 RPgBase RPgCSpec RPgImgA RPgSat RPgHarn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import AF0l AF0m RPgE01D RPgE01S.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ======================================== 1. checkers over the start-up tables ========================================
   (donor sections 2-3) *)
(* The granule (shadow byte) at s is one of the start-up record's shadow cells. *)
Definition e01b_is_shc (s : Z) (c : acell) : bool :=
  match c with ACell (ANum s') (S O) (AV (ANum _)) => Z.eqb s' s | _ => false end.
Definition e01b_is_shv (s v : Z) (c : acell) : bool :=
  match c with ACell (ANum s') (S O) (AV (ANum v')) => (Z.eqb s' s && Z.eqb v' v)%bool | _ => false end.
(* A cell at a literal address, of width w, holding the literal v. *)
Definition e01b_is_wv (w : nat) (v : Z) (c : acell) : bool :=
  match c with ACell (ANum _) w' (AV (ANum v')) => (Nat.eqb w' w && Z.eqb v' v)%bool | _ => false end.

(* The end (in granules) of the zero-shadow range that holds granule k, if one does. *)
Fixpoint e01b_zfind (k : Z) (zs : list (Z * Z)) : option Z :=
  match zs with
  | [] => None
  | (q, m) :: r => if ((q / 8 <=? k) && (k <? (q + m) / 8))%bool then Some ((q + m) / 8) else e01b_zfind k r
  end.

(* Every granule of [k, hi) is in a zero-shadow range or has a shadow cell of the start-up record. *)
Fixpoint e01b_vscan (fuel : nat) (k hi : Z) : bool :=
  match fuel with
  | O => false
  | S f =>
      if hi <=? k then true else
      match e01b_zfind k Tfib_zero_shadow with
      | Some e => e01b_vscan f e hi
      | None => (existsb (e01b_is_shc (SHADOW_OFF + k)) Tfib_const_shadow && e01b_vscan f (k + 1) hi)%bool
      end
  end.

(* A registered global's full granules lie in one zero-shadow range (or it has none), and its last partial granule
   has the shadow cell `size mod 8`. *)
Definition e01b_glob_chk (g : Z * Z) : bool :=
  ((fst g mod 8 =? 0) && (0 <=? snd g) &&
   ((snd g / 8 =? 0) ||
    existsb (fun r => (fst r <=? fst g) && (fst g + snd g / 8 * 8 <=? fst r + snd r)) Tfib_zero_shadow) &&
   ((snd g mod 8 =? 0) || existsb (e01b_is_shv (SHADOW_OFF + fst g / 8 + snd g / 8) (snd g mod 8)) Tfib_const_shadow))%bool.

(* A cell at a literal address holding a literal: its address, width and value. *)
Definition e01b_cell_lit (c : acell) : option (Z * nat * Z) :=
  match c with ACell (ANum c0) w (AV (ANum v)) => Some (c0, w, v) | _ => None end.
(* The cell c covers the byte a, and its byte there is the image's byte at a. *)
Definition e01b_pin (a : Z) (c : acell) : bool :=
  match e01b_cell_lit c with
  | Some (c0, w, v) =>
      if ((c0 <=? a) && (a <? c0 + Z.of_nat w))%bool
      then oz_eqb (RPgSat.img_byte rsegs a) (YG0f.le_byte v w (Z.to_nat (a - c0)))
      else false
  | None => false
  end.
(* The range r meets no read-only segment of the image. *)
Definition e01b_rdisj (r : Z * Z) : bool :=
  forallb (fun sg => (seg_writable sg || (fst r + snd r <=? Z.of_N (seg_base sg)) ||
                      (Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <=? fst r))%bool) rsegs.
(* An owned range: it meets no read-only segment, or each of its read-only bytes is pinned by a cell of the start-up
   record's const list Tfib_const_abs. (`if`, not `||`: the VM evaluates both arguments of `orb`.) *)
Definition e01b_own_chk (r : Z * Z) : bool :=
  if e01b_rdisj r then true else
  forallb (fun k => if e01_romb (fst r + Z.of_nat k) then existsb (e01b_pin (fst r + Z.of_nat k)) Tfib_const_abs
                    else true)
    (seq 0 (Z.to_nat (snd r))).
(* A cell of hi_cells: it is in a read-only segment, or none of its 8 bytes is owned or on the errno cell. *)
Definition e01b_relro_chk (c : Z * Z) : bool :=
  (e01_romb (fst c) ||
   forallb (fun k =>
     negb (existsb (fun r => (fst r <=? fst c + Z.of_nat k) && (fst c + Z.of_nat k <? fst r + snd r)) Tfib_owned_static) &&
     negb ((TFIB_ERRNO <=? fst c + Z.of_nat k) && (fst c + Z.of_nat k <? TFIB_ERRNO + 4))) (seq 0 8))%bool.

(* ======================================== 2. lemmas over the checkers ======================================== *)
Lemma e01b_le_byte1 : forall v, 0 <= v < 256 -> YG0f.le_byte v 1 0 = v.
Proof.
intros v Hv. unfold YG0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite (Z.mod_small v 256 Hv). exact (Z.mod_small v 256 Hv).
Qed.

Lemma e01b_is_shc_eq : forall s c, e01b_is_shc s c = true -> exists v, c = z1 (ANum s) v.
Proof.
intros s [ca cw cv] H. destruct ca; try (cbn in H; discriminate H).
destruct cw as [|[|cw]]; try (cbn in H; discriminate H).
destruct cv as [e|m0 v0]; try (cbn in H; discriminate H).
destruct e; try (cbn in H; discriminate H).
cbn in H. apply Z.eqb_eq in H. subst. eexists. reflexivity.
Qed.

Lemma e01b_is_shv_eq : forall s v c, e01b_is_shv s v c = true -> c = z1 (ANum s) v.
Proof.
intros s v [ca cw cv] H. destruct ca; try (cbn in H; discriminate H).
destruct cw as [|[|cw]]; try (cbn in H; discriminate H).
destruct cv as [e|m0 v0]; try (cbn in H; discriminate H).
destruct e; try (cbn in H; discriminate H).
cbn in H. apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. subst. reflexivity.
Qed.

Definition e01b_cell_addr (c : acell) : Z := match c_at c with ANum a => a | _ => 0 end.
Lemma e01b_is_wv_true8 : forall a v, e01b_is_wv 8 v (z8 (ANum a) v) = true.
Proof. intros a v. unfold e01b_is_wv, z8, c8. cbn [c_at c_w c_val Nat.eqb andb]. apply Z.eqb_refl. Qed.
Lemma e01b_is_wv_true4 : forall a v, e01b_is_wv 4 v (z4 (ANum a) v) = true.
Proof. intros a v. unfold e01b_is_wv, z4, c4. cbn [c_at c_w c_val Nat.eqb andb]. apply Z.eqb_refl. Qed.

Lemma e01b_filter_sing_eq : forall (f : acell -> bool) l x y, List.filter f l = [y] -> In x l -> f x = true -> x = y.
Proof.
intros f l x y Hf Hin Hx.
assert (H : In x (List.filter f l)) by (apply (proj2 (filter_In f x l)); split; assumption).
rewrite Hf in H. destruct H as [H|[]]. symmetry. exact H.
Qed.

Lemma e01b_zfind_some : forall k zs e, e01b_zfind k zs = Some e ->
  exists q m, In (q, m) zs /\ q / 8 <= k < (q + m) / 8 /\ e = (q + m) / 8.
Proof.
intros k zs. induction zs as [|[q m] r IH]; intros e H; cbn [e01b_zfind] in H; [discriminate|].
destruct ((q / 8 <=? k) && (k <? (q + m) / 8))%bool eqn:Hb.
- injection H as <-. apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  exists q, m. split; [left; reflexivity|]. split; [lia | reflexivity].
- destruct (IH e H) as (q' & m' & Hin & Hk & He). exists q', m'. split; [right; exact Hin|]. split; [exact Hk | exact He].
Qed.

Lemma e01b_vscan_ok : forall fuel k hi, e01b_vscan fuel k hi = true -> forall j, k <= j < hi ->
  (exists q m, In (q, m) Tfib_zero_shadow /\ q / 8 <= j < (q + m) / 8) \/
  existsb (e01b_is_shc (SHADOW_OFF + j)) Tfib_const_shadow = true.
Proof.
induction fuel as [|f IH]; intros k hi H j Hj; cbn [e01b_vscan] in H; [discriminate|].
destruct (hi <=? k) eqn:E; [apply Z.leb_le in E; exfalso; lia|].
destruct (e01b_zfind k Tfib_zero_shadow) as [e|] eqn:Ez.
- destruct (e01b_zfind_some _ _ _ Ez) as (q & m & Hin & Hk & ->).
  destruct (Z_lt_le_dec j ((q + m) / 8)) as [Hlt|Hge].
  + left. exists q, m. split; [exact Hin | lia].
  + exact (IH _ _ H j (conj Hge (proj2 Hj))).
- apply andb_prop in H as [Hc H]. destruct (Z.eq_dec j k) as [->|Hne]; [right; exact Hc|].
  apply (IH _ _ H). lia.
Qed.

Lemma e01b_cell_lit_ok : forall c c0 w v, e01b_cell_lit c = Some (c0, w, v) -> c = ACell (ANum c0) w (AV (ANum v)).
Proof.
intros [ca cw cv] c0 w v H. destruct ca; try (cbn in H; discriminate H).
destruct cv as [e|m0 v0]; try (cbn in H; discriminate H).
destruct e; try (cbn in H; discriminate H).
cbn in H. injection H as <- <- <-. reflexivity.
Qed.

Lemma e01b_pin_ok : forall a c, e01b_pin a c = true ->
  exists c0 w v, c = ACell (ANum c0) w (AV (ANum v)) /\ c0 <= a < c0 + Z.of_nat w /\
  RPgSat.img_byte rsegs a = Some (YG0f.le_byte v w (Z.to_nat (a - c0))).
Proof.
intros a c H. unfold e01b_pin in H.
destruct (e01b_cell_lit c) as [[[c0 w] v]|] eqn:E; [|discriminate H].
destruct ((c0 <=? a) && (a <? c0 + Z.of_nat w))%bool eqn:R; [|discriminate H].
apply andb_prop in R as [R1 R2]. apply Z.leb_le in R1. apply Z.ltb_lt in R2.
exists c0, w, v. split; [exact (e01b_cell_lit_ok c c0 w v E)|]. split; [lia | exact (oz_eqb_ok _ _ H)].
Qed.

(* ======================================== 3. the checkers, by computation on fuzz_role.asan ========================
   The image's range [IMG_LO, IMG_TOP) = [0x10000, 0x5f8000) is covered, granule by granule, by the 32 zero-shadow
   ranges and the 581 shadow cells of the start-up record: 613 steps, so 4096 is fuel to spare. *)
Lemma e01b_vscan_chk : e01b_vscan (Pos.to_nat 4096) (YImgTop.IMG_LO / 8) (YImgTop.IMG_TOP / 8) = true.
Proof. vm_compute. reflexivity. Qed.

(* The 49 registered globals of RPgImgA (45 in .rodata, 4 in .data.rel.ro). *)
Lemma e01b_globs_chk : forallb e01b_glob_chk (hi_globs role_himg_A) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma e01b_zs_align_chk :
  forallb (fun r => (fst r mod 8 =? 0) && (snd r mod 8 =? 0) && (0 <=? snd r))%bool Tfib_zero_shadow = true.
Proof. vm_compute. reflexivity. Qed.

Lemma e01b_zs_align : forall q m, In (q, m) Tfib_zero_shadow -> q mod 8 = 0 /\ m mod 8 = 0 /\ 0 <= m.
Proof.
intros q m Hin. pose proof (proj1 (forallb_forall _ _) e01b_zs_align_chk (q, m) Hin) as Hb. cbn [fst snd] in Hb.
apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2].
apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. apply Z.leb_le in H3. auto.
Qed.

(* The 83 owned ranges: 57 meet a read-only segment, and their 1417 read-only bytes are each pinned by a cell of
   Tfib_const_abs that holds the image's byte. *)
Lemma e01b_owned_chk : forallb e01b_own_chk Tfib_owned_static = true.
Proof. vm_compute. reflexivity. Qed.

(* The errno cell [TFIB_ERRNO, TFIB_ERRNO + 4) = [0x5d62ec, 0x5d62f0) is in no read-only segment. *)
Lemma e01b_errno_chk : forallb (fun k => negb (e01_romb (TFIB_ERRNO + Z.of_nat k))) (seq 0 4) = true.
Proof. vm_compute. reflexivity. Qed.

(* The 36 cells of RPgImgA's hi_cells: the 3 in .rodata are read-only, the 33 in .data.rel.ro are unowned. *)
Lemma e01b_relro_chk_ok : forallb e01b_relro_chk (hi_cells role_himg_A) = true.
Proof. vm_compute. reflexivity. Qed.

(* The four runtime cells of asyms_ok's const law are each the only cell of their width and value in the whole
   start-up table. *)
Lemma e01b_filter_shadow_cell :
  List.filter (e01b_is_wv 8 SHADOW_OFF) (Tfib_const_sym ++ Tfib_const_abs ++ Tfib_const_shadow)
  = [z8 (ANum 0xa33f8) SHADOW_OFF].
Proof. vm_compute. reflexivity. Qed.
Lemma e01b_filter_uar_cell :
  List.filter (e01b_is_wv 4 1) (Tfib_const_sym ++ Tfib_const_abs ++ Tfib_const_shadow) = [z4 (ANum 0xa3400) 1].
Proof. vm_compute. reflexivity. Qed.
Lemma e01b_filter_got_shadow :
  List.filter (e01b_is_wv 8 0xa33f8) (Tfib_const_sym ++ Tfib_const_abs ++ Tfib_const_shadow)
  = [z8 (ANum 0x9a830) 0xa33f8].
Proof. vm_compute. reflexivity. Qed.
Lemma e01b_filter_got_uar :
  List.filter (e01b_is_wv 8 0xa3400) (Tfib_const_sym ++ Tfib_const_abs ++ Tfib_const_shadow)
  = [z8 (ANum 0x9a888) 0xa3400].
Proof. vm_compute. reflexivity. Qed.

(* A layout to instantiate asyms_ok's const law at (Tfib_const does not read it). *)
Definition e01b_ly0 : alayout :=
  ALayout 0 0 0 0 0 0 0 0 0 0 0 0 [] [] 0 [] (0, 0) (fun _ => 0).

(* ======================================== 4. the facts of B ======================================== *)
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section c.
Variable B : asyms.
(* The only thing this file assumes: B is image A's start-up record (lib/A/AF0m.v TfibSyms). *)
Hypothesis HB : TfibSyms B.

Lemma e01b_in_const : forall ly c, In c (Tfib_const ly) -> In c (as_const B ly).
Proof. intros ly c H. rewrite (ts_const _ HB ly). exact H. Qed.

Lemma e01b_in_zsh : forall r, In r Tfib_zero_shadow -> In r (as_zero_shadow B).
Proof. intros r H. rewrite (ts_zsh _ HB). exact H. Qed.

(* A shadow cell of the start-up record holds its byte in every state. *)
Lemma e01b_shadow_rd : forall segs ly S (W : world segs) mem md s v,
  AR segs B ly S W mem md -> In (z1 (ANum s) v) Tfib_const_shadow ->
  aview segs (w_H W) mem s = Some (YG0f.le_byte v 1 0).
Proof.
intros segs ly S W mem md s v HAR Hin.
pose proof (am_const _ _ _ _ (proj1 HAR)) as HC. rewrite Forall_forall in HC.
assert (Hin' : In (z1 (ANum s) v) (as_const B ly)).
{ apply e01b_in_const. unfold Tfib_const. apply in_or_app. right. apply in_or_app. right. exact Hin. }
specialize (HC _ Hin'). unfold cell_holds, z1, c1 in HC. cbn [c_at c_val c_w aeval] in HC.
specialize (HC 0%nat ltac:(lia)). cbn [Z.of_nat] in HC. rewrite Z.add_0_r in HC. exact HC.
Qed.

(* A granule of a zero-shadow range of the start-up record has shadow byte 0 in every state (ARm's am_zshadow). *)
Lemma e01b_zs_rd : forall segs ly S (W : world segs) mem md q m j,
  AR segs B ly S W mem md -> In (q, m) Tfib_zero_shadow -> q / 8 <= j < (q + m) / 8 ->
  aview segs (w_H W) mem (SHADOW_OFF + j) = Some 0.
Proof.
intros segs ly S W mem md q m j HAR Hin Hj.
pose proof (am_zshadow _ _ _ _ (proj1 HAR)) as HZ. unfold zshadow_ok, zero_shadow_ranges in HZ.
rewrite Forall_forall in HZ.
pose proof (HZ (q, m) (or_intror (e01b_in_zsh _ Hin))) as Hz. cbn [fst snd] in Hz.
destruct (e01b_zs_align q m Hin) as (Hq & Hm & Hm0).
assert (E : (q + m) / 8 = q / 8 + m / 8).
{ pose proof (Z.div_mod q 8 ltac:(lia)) as Dq.
  replace (q + m) with (m + q / 8 * 8) by lia. rewrite Z.div_add by lia. lia. }
replace (SHADOW_OFF + j) with (shadow_of_addr SHADOW_OFF q + (j - q / 8)) by (unfold shadow_of_addr; lia).
apply Hz. lia.
Qed.

(* every shadow byte of the image's range is mapped, in every state *)
Theorem e01b_img_shadow_vis : e01_img_shadow_vis B.
Proof.
intros ly S W mem md a HAR Ha. unfold shadow_addr.
assert (E8 : 8 * (YImgTop.IMG_TOP / 8) = YImgTop.IMG_TOP) by (vm_compute; reflexivity).
assert (Hj : YImgTop.IMG_LO / 8 <= a / 8 < YImgTop.IMG_TOP / 8).
{ split; [apply Z.div_le_mono; lia | apply Z.div_lt_upper_bound; lia]. }
destruct (e01b_vscan_ok _ _ _ e01b_vscan_chk (a / 8) Hj) as [(q & m & Hin & Hq) | Hc].
- rewrite (e01b_zs_rd rsegs ly S W mem md q m (a / 8) HAR Hin Hq). discriminate.
- apply existsb_exists in Hc as (c & Hin & Hb). destruct (e01b_is_shc_eq _ _ Hb) as [v ->].
  rewrite (e01b_shadow_rd rsegs ly S W mem md _ v HAR Hin). discriminate.
Qed.

(* each registered global's bytes are marked usable, and its partial granule carries size mod 8, in every state *)
Theorem e01b_globs_marked : e01_globs_marked B.
Proof.
intros ly S W mem md q sz Hin HAR.
pose proof (proj1 (forallb_forall _ _) e01b_globs_chk (q, sz) Hin) as Hb.
unfold e01b_glob_chk in Hb. cbn [fst snd] in Hb.
apply andb_prop in Hb as [Hb Hlast]. apply andb_prop in Hb as [Hb Hfull]. apply andb_prop in Hb as [Hq Hsz].
apply Z.eqb_eq in Hq. apply Z.leb_le in Hsz.
unfold block_shadow. split; [exact Hq|]. split; [exact Hsz|]. intros i Hi.
pose proof (Z.div_mod q 8 ltac:(lia)) as Dq.
pose proof (Z.div_mod sz 8 ltac:(lia)) as Ds. pose proof (Z.mod_pos_bound sz 8 ltac:(lia)) as Bs.
pose proof (Z.div_mod (sz + 7) 8 ltac:(lia)) as Ds7. pose proof (Z.mod_pos_bound (sz + 7) 8 ltac:(lia)) as Bs7.
destruct (i <? sz / 8) eqn:Hlt.
- apply Z.ltb_lt in Hlt.
  apply orb_true_iff in Hfull as [H0|H0]; [apply Z.eqb_eq in H0; exfalso; lia|].
  apply existsb_exists in H0 as ([r0 m0] & Hr & Hf). cbn [fst snd] in Hf.
  apply andb_prop in Hf as [Hf1 Hf2]. apply Z.leb_le in Hf1. apply Z.leb_le in Hf2.
  destruct (e01b_zs_align r0 m0 Hr) as (Hr8 & Hm8 & Hm0).
  pose proof (Z.div_mod r0 8 ltac:(lia)) as Dr. pose proof (Z.div_mod m0 8 ltac:(lia)) as Dm.
  pose proof (Z.div_mod (r0 + m0) 8 ltac:(lia)) as Drm. pose proof (Z.mod_pos_bound (r0 + m0) 8 ltac:(lia)) as Brm.
  unfold shadow_of_addr.
  replace (SHADOW_OFF + q / 8 + i) with (SHADOW_OFF + (q / 8 + i)) by lia.
  apply (e01b_zs_rd rsegs ly S W mem md r0 m0); [exact HAR | exact Hr | lia].
- apply Z.ltb_ge in Hlt.
  assert (Hi' : i = sz / 8) by lia.
  apply orb_true_iff in Hlast as [H0|H0]; [apply Z.eqb_eq in H0; exfalso; lia|].
  apply existsb_exists in H0 as (c & Hc & Hcb). apply e01b_is_shv_eq in Hcb. subst c. subst i.
  unfold shadow_of_addr.
  rewrite (e01b_shadow_rd rsegs ly S W mem md _ _ HAR Hc). rewrite e01b_le_byte1 by lia. reflexivity.
Qed.

(* the read-only bytes the runtime owns read as the image's: each is pinned by a const cell holding the image's byte;
   the errno cell is in no read-only segment *)
Theorem e01b_rom_owned : e01_rom_owned B.
Proof.
intros ly S W mem md a HAR Ha [Hown | He].
- apply Exists_exists in Hown as (r & Hr & Hin). rewrite (ts_owned _ HB) in Hr. unfold in_zr in Hin.
  pose proof (proj1 (forallb_forall _ _) e01b_owned_chk r Hr) as Hc. unfold e01b_own_chk in Hc.
  revert Hc. destruct (e01b_rdisj r) eqn:Ed; intro Hc.
  + exfalso. destruct Ha as (sg & Hsg & Hw & Hb). unfold e01b_rdisj in Ed. rewrite forallb_forall in Ed.
    specialize (Ed sg Hsg). cbv beta in Ed. rewrite Hw in Ed. rewrite orb_false_l in Ed.
    apply orb_true_iff in Ed as [E|E]; apply Z.leb_le in E; lia.
  + assert (Hk : (Z.to_nat (a - fst r) < Z.to_nat (snd r))%nat) by lia.
    pose proof (forallb_seq _ _ Hc _ Hk) as E. cbv beta in E. rewrite Z2Nat.id in E by lia.
    replace (fst r + (a - fst r)) with a in E by lia.
    revert E. destruct (e01_romb a) eqn:Er; intro E; [|exfalso; exact (e01_romb_false a Er Ha)].
    apply existsb_exists in E as (c & Hc' & Hp).
    destruct (e01b_pin_ok a c Hp) as (c0 & w & v & -> & Hra & Hi).
    assert (Hin' : In (ACell (ANum c0) w (AV (ANum v))) (as_const B ly)).
    { apply e01b_in_const. unfold Tfib_const. apply in_or_app. right. apply in_or_app. left. exact Hc'. }
    pose proof (am_const _ _ _ _ (proj1 HAR)) as HC. rewrite Forall_forall in HC. specialize (HC _ Hin').
    unfold cell_holds in HC. cbn [c_at c_val c_w aeval] in HC.
    assert (Hkw : (Z.to_nat (a - c0) < w)%nat) by lia.
    specialize (HC _ Hkw). rewrite Z2Nat.id in HC by lia. replace (c0 + (a - c0)) with a in HC by lia.
    rewrite HC. symmetry. exact Hi.
- exfalso. rewrite (ts_errno _ HB) in He.
  assert (Hk : (Z.to_nat (a - TFIB_ERRNO) < 4)%nat) by lia.
  pose proof (forallb_seq _ _ e01b_errno_chk _ Hk) as E. cbv beta in E. rewrite Z2Nat.id in E by lia.
  replace (TFIB_ERRNO + (a - TFIB_ERRNO)) with a in E by lia.
  apply negb_true_iff in E. exact (e01_romb_false a E Ha).
Qed.

(* the .data.rel.ro cells of hi_cells are neither owned nor the errno cell *)
Theorem e01b_relro_unowned : e01_relro_unowned B.
Proof.
intros c i Hin Hr Hi.
pose proof (proj1 (forallb_forall _ _) e01b_relro_chk_ok c Hin) as Hc. unfold e01b_relro_chk in Hc.
revert Hc. destruct (e01_romb (fst c)) eqn:Er; intro Hc; [exfalso; exact (Hr (e01_romb_ok _ Er))|].
rewrite orb_false_l in Hc.
assert (Hk : (Z.to_nat i < 8)%nat) by lia.
pose proof (forallb_seq _ _ Hc _ Hk) as E. cbv beta in E. rewrite Z2Nat.id in E by lia.
apply andb_prop in E as [E1 E2]. apply negb_true_iff in E1. apply negb_true_iff in E2.
rewrite (ts_owned _ HB), (ts_errno _ HB). split.
- intro Hx. apply Exists_exists in Hx as (r & Hrin & Hz). unfold in_zr in Hz.
  assert (Ht : existsb (fun r => (fst r <=? fst c + i) && (fst c + i <? fst r + snd r)) Tfib_owned_static = true).
  { apply existsb_exists. exists r. split; [exact Hrin|]. apply andb_true_iff.
    split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  rewrite Ht in E1. discriminate E1.
- intro Hx. apply andb_false_iff in E2 as [E2|E2]; [apply Z.leb_gt in E2 | apply Z.ltb_ge in E2]; lia.
Qed.

(* lib/A/RPgE01S.v's static law, at B *)
Theorem e01b_static_law : rh_static_law rsegs B 0x9a120 0x9b528.
Proof.
exact (e01_static_law B e01b_globs_marked e01b_img_shadow_vis e01b_rom_owned e01b_relro_unowned).
Qed.

(* ======================================== 5. B's four cell addresses ========================================
   asyms_ok's const law (YG0f.v aso_const_law) puts four cells of B's own addresses in as_const; each is the only
   cell of its width and value in the whole table (section 3), so the four addresses are fixed. *)
Lemma e01b_shadow_cell : as_shadow_cell B = 0xa33f8.
Proof.
destruct (aso_const_law _ (ts_ok _ HB) e01b_ly0) as (I1 & _ & _ & _).
rewrite (ts_const _ HB e01b_ly0) in I1. unfold Tfib_const in I1.
exact (f_equal e01b_cell_addr (e01b_filter_sing_eq _ _ _ _ e01b_filter_shadow_cell I1 (e01b_is_wv_true8 _ _))).
Qed.
Lemma e01b_uar_cell : as_uar_cell B = 0xa3400.
Proof.
destruct (aso_const_law _ (ts_ok _ HB) e01b_ly0) as (_ & I2 & _ & _).
rewrite (ts_const _ HB e01b_ly0) in I2. unfold Tfib_const in I2.
exact (f_equal e01b_cell_addr (e01b_filter_sing_eq _ _ _ _ e01b_filter_uar_cell I2 (e01b_is_wv_true4 _ _))).
Qed.
Lemma e01b_got_shadow : as_got_shadow B = 0x9a830.
Proof.
destruct (aso_const_law _ (ts_ok _ HB) e01b_ly0) as (_ & _ & I3 & _).
rewrite (ts_const _ HB e01b_ly0) in I3. unfold Tfib_const in I3.
rewrite e01b_shadow_cell in I3.
exact (f_equal e01b_cell_addr (e01b_filter_sing_eq _ _ _ _ e01b_filter_got_shadow I3 (e01b_is_wv_true8 _ _))).
Qed.
Lemma e01b_got_uar : as_got_uar B = 0x9a888.
Proof.
destruct (aso_const_law _ (ts_ok _ HB) e01b_ly0) as (_ & _ & _ & I4).
rewrite (ts_const _ HB e01b_ly0) in I4. unfold Tfib_const in I4.
rewrite e01b_uar_cell in I4.
exact (f_equal e01b_cell_addr (e01b_filter_sing_eq _ _ _ _ e01b_filter_got_uar I4 (e01b_is_wv_true8 _ _))).
Qed.

(* ======================================== 6. B's two code entries ======================================== *)
Lemma e01b_sm3 : pc_stack_malloc (as_code B) 3 = E01_SM3.
Proof. rewrite (ts_code _ HB). reflexivity. Qed.
Lemma e01b_malloc : pc_wrap_malloc (as_code B) = E01_MALLOC.
Proof. rewrite (ts_code _ HB). reflexivity. Qed.

End c.
End b.

Print Assumptions e01b_globs_marked.
Print Assumptions e01b_img_shadow_vis.
Print Assumptions e01b_rom_owned.
Print Assumptions e01b_relro_unowned.
Print Assumptions e01b_static_law.
Print Assumptions e01b_got_shadow.
Print Assumptions e01b_shadow_cell.
Print Assumptions e01b_got_uar.
Print Assumptions e01b_uar_cell.
Print Assumptions e01b_sm3.
Print Assumptions e01b_malloc.
