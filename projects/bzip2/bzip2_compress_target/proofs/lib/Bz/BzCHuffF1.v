(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCHuff BzCPermF BzCRebuildF.
Import ListNotations.

From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArrD.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
Module BzCFactsHm.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuff.
Import ListNotations.
Local Open Scope Z_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma upheap_loop_S : forall f h w zz tmp,
  upheap_loop (S f) h w zz tmp =
  (if zget w tmp <? zget w (zget h (Z.shiftr zz 1))
   then upheap_loop f (zset h zz (zget h (Z.shiftr zz 1))) w (Z.shiftr zz 1) tmp else (h, zz)).
Proof. reflexivity. Qed.
Lemma upheap_loop_stop : forall f h w zz tmp,
  (zget w tmp <? zget w (zget h (Z.shiftr zz 1))) = false -> upheap_loop f h w zz tmp = (h, zz).
Proof. intros [|f] h w zz tmp C; [reflexivity|]. rewrite upheap_loop_S, C. reflexivity. Qed.
Lemma upheap_eq : forall h w z h' zz',
  upheap_loop 20 h w z (zget h z) = (h', zz') -> upheap h w z = zset h' zz' (zget h z).
Proof. intros h w z h' zz' E. unfold upheap. rewrite E. reflexivity. Qed.

Definition dh_child (h w : zarr) (nH yy : Z) : Z :=
  if (yy <? nH) && (zget w (zget h (yy + 1)) <? zget w (zget h yy)) then yy + 1 else yy.
Lemma downheap_loop_S : forall f h w nH zz tmp,
  downheap_loop (S f) h w nH zz tmp =
  (if nH <? Z.shiftl zz 1 then (h, zz) else
   let yy := dh_child h w nH (Z.shiftl zz 1) in
   if zget w tmp <? zget w (zget h yy) then (h, zz)
   else downheap_loop f (zset h zz (zget h yy)) w nH yy tmp).
Proof. reflexivity. Qed.
Lemma downheap_loop_stop1 : forall f h w nH zz tmp,
  (nH <? Z.shiftl zz 1) = true -> downheap_loop f h w nH zz tmp = (h, zz).
Proof. intros [|f] h w nH zz tmp C; [reflexivity|]. rewrite downheap_loop_S, C. reflexivity. Qed.
Lemma downheap_loop_stop2 : forall f h w nH zz tmp,
  (nH <? Z.shiftl zz 1) = false -> (zget w tmp <? zget w (zget h (dh_child h w nH (Z.shiftl zz 1)))) = true ->
  downheap_loop f h w nH zz tmp = (h, zz).
Proof. intros [|f] h w nH zz tmp C1 C2; [reflexivity|]. rewrite downheap_loop_S, C1. cbn zeta. rewrite C2. reflexivity. Qed.
Lemma downheap_eq : forall h w nH z h' zz',
  downheap_loop 20 h w nH z (zget h z) = (h', zz') -> downheap h w nH z = zset h' zz' (zget h z).
Proof. intros h w nH z h' zz' E. unfold downheap. rewrite E. reflexivity. Qed.

Lemma hm_depth_S : forall f par k j,
  hm_depth (S f) par k j = (if 0 <=? zget par k then hm_depth f par (zget par k) (j + 1) else j).
Proof. reflexivity. Qed.
Lemma hm_depth_stop : forall f par k j, (0 <=? zget par k) = false -> hm_depth f par k j = j.
Proof. intros [|f] par k j C; [reflexivity|]. rewrite hm_depth_S, C. reflexivity. Qed.

Lemma hm_winit_S : forall n weight freq fb i,
  hm_winit (S n) weight freq fb i =
  hm_winit n (zset weight (i + 1) (Z.shiftl (if zget freq (fb + i) =? 0 then 1 else zget freq (fb + i)) 8)) freq fb (i + 1).
Proof. reflexivity. Qed.
Lemma hm_lens_S : forall n len par lb maxLen i tooLong,
  hm_lens (S n) len par lb maxLen i tooLong =
  hm_lens n (zset len (lb + i - 1) (hm_depth 600 par i 0 mod 256)) par lb maxLen (i + 1) (tooLong || (maxLen <? hm_depth 600 par i 0)).
Proof. reflexivity. Qed.
Lemma hm_rescale_S : forall n weight i,
  hm_rescale (S n) weight i = hm_rescale n (zset weight i (Z.shiftl (1 + Z.shiftr (zget weight i) 8 / 2) 8)) (i + 1).
Proof. reflexivity. Qed.
Lemma hm_combine_S : forall f s,
  hm_combine (S f) s = (if 1 <? hm_nHeap s then hm_combine f (hm_combine_iter s) else s).
Proof. reflexivity. Qed.
(* [comment removed for export] *)
Lemma hm_rounds_S : forall f A maxLen lb s,
  hm_rounds (S f) A maxLen lb s = (if hs_done s then s else hm_rounds f A maxLen lb (hm_round A maxLen lb s)).
Proof. reflexivity. Qed.
Lemma hm_rounds_stay : forall f A maxLen lb s, hs_done s = true -> hm_rounds f A maxLen lb s = s.
Proof. intros [|f] A maxLen lb s D; [reflexivity|]. rewrite hm_rounds_S, D. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint fill_h (n : nat) (h w : zarr) (nH i : Z) : zarr :=
  match n with
  | O => h
  | S n' => fill_h n' (upheap (zset h (nH + 1) i) w (nH + 1)) w (nH + 1) (i + 1)
  end.
Fixpoint pneg (p : zarr) (i : Z) (n : nat) : zarr :=
  match n with O => p | S n' => pneg (zset p i (-1)) (i + 1) n' end.
Lemma fill_h_S : forall n h w nH i, fill_h (S n) h w nH i = fill_h n (upheap (zset h (nH + 1) i) w (nH + 1)) w (nH + 1) (i + 1).
Proof. reflexivity. Qed.
Lemma pneg_S : forall p i n, pneg p i (S n) = pneg (zset p i (-1)) (i + 1) n.
Proof. reflexivity. Qed.
Lemma hm_fill_eq : forall n h w p nH i, hm_fill n h w p nH i = (fill_h n h w nH i, pneg p i n, nH + Z.of_nat n).
Proof.
  induction n as [|n IH]; intros h w p nH i; cbn [hm_fill fill_h pneg].
  - rewrite Z.add_0_r. reflexivity.
  - rewrite IH. f_equal. lia.
Qed.
Lemma pneg_get : forall n p i x, zget (pneg p i n) x = (if (i <=? x) && (x <? i + Z.of_nat n) then -1 else zget p x).
Proof.
  induction n as [|n IH]; intros p i x; cbn [pneg].
  - destruct (Z.leb_spec i x), (Z.ltb_spec x (i + Z.of_nat 0)); cbn [andb]; try reflexivity; lia.
  - rewrite IH, zget_zset. replace (Z.of_nat (S n)) with (Z.of_nat n + 1) by lia.
    destruct (Z.leb_spec (i + 1) x), (Z.ltb_spec x (i + 1 + Z.of_nat n)), (Z.eqb_spec x i), (Z.leb_spec i x), (Z.ltb_spec x (i + (Z.of_nat n + 1))); cbn [andb]; try reflexivity; lia.
Qed.
Lemma pneg_def : forall n p i x, zdef (pneg p i n) x = (((i <=? x) && (x <? i + Z.of_nat n)) || zdef p x)%bool.
Proof.
  induction n as [|n IH]; intros p i x; cbn [pneg].
  - destruct (Z.leb_spec i x), (Z.ltb_spec x (i + Z.of_nat 0)); cbn [andb orb]; try reflexivity; lia.
  - rewrite IH, zdef_zset. replace (Z.of_nat (S n)) with (Z.of_nat n + 1) by lia.
    destruct (Z.leb_spec (i + 1) x), (Z.ltb_spec x (i + 1 + Z.of_nat n)), (Z.eqb_spec x i), (Z.leb_spec i x), (Z.ltb_spec x (i + (Z.of_nat n + 1))), (zdef p x); cbn [andb orb]; try reflexivity; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fmax1 (f : Z) : Z := if f =? 0 then 1 else f.
Lemma hm_winit_get : forall n w freq fb i x,
  zget (hm_winit n w freq fb i) x = (if (i + 1 <=? x) && (x <=? i + Z.of_nat n) then Z.shiftl (fmax1 (zget freq (fb + (x - 1)))) 8 else zget w x).
Proof.
  induction n as [|n IH]; intros w freq fb i x; cbn [hm_winit].
  - destruct (Z.leb_spec (i + 1) x), (Z.leb_spec x (i + Z.of_nat 0)); cbn [andb]; try reflexivity; lia.
  - rewrite IH, zget_zset. replace (Z.of_nat (S n)) with (Z.of_nat n + 1) by lia. unfold fmax1.
    destruct (Z.leb_spec (i + 1 + 1) x), (Z.leb_spec x (i + 1 + Z.of_nat n)), (Z.eqb_spec x (i + 1)), (Z.leb_spec (i + 1) x), (Z.leb_spec x (i + (Z.of_nat n + 1))); cbn [andb]; try reflexivity; try lia.
    subst x. replace (i + 1 - 1) with i by lia. reflexivity.
Qed.
Lemma hm_winit_def : forall n w freq fb i x,
  zdef (hm_winit n w freq fb i) x = (((i + 1 <=? x) && (x <=? i + Z.of_nat n)) || zdef w x)%bool.
Proof.
  induction n as [|n IH]; intros w freq fb i x; cbn [hm_winit].
  - destruct (Z.leb_spec (i + 1) x), (Z.leb_spec x (i + Z.of_nat 0)); cbn [andb orb]; try reflexivity; lia.
  - rewrite IH, zdef_zset. replace (Z.of_nat (S n)) with (Z.of_nat n + 1) by lia.
    destruct (Z.leb_spec (i + 1 + 1) x), (Z.leb_spec x (i + 1 + Z.of_nat n)), (Z.eqb_spec x (i + 1)), (Z.leb_spec (i + 1) x), (Z.leb_spec x (i + (Z.of_nat n + 1))), (zdef w x); cbn [andb orb]; try reflexivity; lia.
Qed.
Definition resc (v : Z) : Z := Z.shiftl (1 + Z.shiftr v 8 / 2) 8.
(* [comment removed for export] *)
Lemma hm_rescale_def : forall n w i x,
  zdef (hm_rescale n w i) x = (((i <=? x) && (x <? i + Z.of_nat n)) || zdef w x)%bool.
Proof.
  induction n as [|n IH]; intros w i x; cbn [hm_rescale].
  - destruct (Z.leb_spec i x), (Z.ltb_spec x (i + Z.of_nat 0)); cbn [andb orb]; try reflexivity; lia.
  - rewrite IH, zdef_zset. replace (Z.of_nat (S n)) with (Z.of_nat n + 1) by lia.
    destruct (Z.leb_spec (i + 1) x), (Z.ltb_spec x (i + 1 + Z.of_nat n)), (Z.eqb_spec x i), (Z.leb_spec i x), (Z.ltb_spec x (i + (Z.of_nat n + 1))), (zdef w x); cbn [andb orb]; try reflexivity; lia.
Qed.
Lemma resc_range : forall v, 0 <= v < 2147483648 -> 256 <= resc v < 2147483648.
Proof. intros v Hv. unfold resc. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change (2^8) with 256. Z.div_mod_to_equations. lia. Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition cb_n1 (c : hms) : Z := zget (hm_heap c) 1.
Definition cb_h1 (c : hms) : zarr := zset (hm_heap c) 1 (zget (hm_heap c) (hm_nHeap c)).       (* [comment removed for export] *)
Definition cb_hp1 (c : hms) : zarr := downheap (cb_h1 c) (hm_weight c) (hm_nHeap c - 1) 1.
Definition cb_n2 (c : hms) : Z := zget (cb_hp1 c) 1.
Definition cb_h2 (c : hms) : zarr := zset (cb_hp1 c) 1 (zget (cb_hp1 c) (hm_nHeap c - 1)).
Definition cb_hp2 (c : hms) : zarr := downheap (cb_h2 c) (hm_weight c) (hm_nHeap c - 2) 1.
Definition cb_aw (c : hms) : Z := addweights (zget (hm_weight c) (cb_n1 c)) (zget (hm_weight c) (cb_n2 c)).
Definition cb_w' (c : hms) : zarr := zset (hm_weight c) (hm_nNodes c + 1) (cb_aw c).
Definition cb_p' (c : hms) : zarr := zset (zset (zset (hm_parent c) (cb_n2 c) (hm_nNodes c + 1)) (cb_n1 c) (hm_nNodes c + 1)) (hm_nNodes c + 1) (-1).
Definition cb_h3 (c : hms) : zarr := zset (cb_hp2 c) (hm_nHeap c - 1) (hm_nNodes c + 1).
Lemma hm_combine_iter_eq : forall c,
  hm_combine_iter c = HMS (upheap (cb_h3 c) (cb_w' c) (hm_nHeap c - 1)) (cb_w' c) (cb_p' c) (hm_nHeap c - 1) (hm_nNodes c + 1).
Proof.
  intros c. unfold hm_combine_iter, cb_h3, cb_hp2, cb_h2, cb_n2, cb_hp1, cb_h1, cb_w', cb_p', cb_aw, cb_n1, cb_n2, cb_hp1, cb_h1.
  replace (hm_nHeap c - 1 - 1) with (hm_nHeap c - 2) by lia. replace (hm_nHeap c - 2 + 1) with (hm_nHeap c - 1) by lia. reflexivity.
Qed.
Lemma hm_combine_iter_nH : forall c, hm_nHeap (hm_combine_iter c) = hm_nHeap c - 1.
Proof. intros c. rewrite hm_combine_iter_eq. reflexivity. Qed.
Lemma hm_combine_iter_nN : forall c, hm_nNodes (hm_combine_iter c) = hm_nNodes c + 1.
Proof. intros c. rewrite hm_combine_iter_eq. reflexivity. Qed.

Lemma iter_S : forall {X} (f : X -> X) k x, Nat.iter (S k) f x = f (Nat.iter k f x).
Proof. reflexivity. Qed.
Lemma iter_S_r : forall {X} (f : X -> X) k x, Nat.iter (S k) f x = Nat.iter k f (f x).
Proof. intros X f k. induction k as [|k IH]; intros x; [reflexivity|]. rewrite iter_S, IH, <- iter_S. reflexivity. Qed.
Lemma iter_nH : forall k c, hm_nHeap (Nat.iter k hm_combine_iter c) = hm_nHeap c - Z.of_nat k.
Proof. induction k as [|k IH]; intros c; [cbn; lia|]. rewrite iter_S, hm_combine_iter_nH, IH. lia. Qed.
Lemma iter_nN : forall k c, hm_nNodes (Nat.iter k hm_combine_iter c) = hm_nNodes c + Z.of_nat k.
Proof. induction k as [|k IH]; intros c; [cbn; lia|]. rewrite iter_S, hm_combine_iter_nN, IH. lia. Qed.
(* [comment removed for export] *)
Lemma hm_combine_iter_run : forall f c k, hm_nHeap c = Z.of_nat k + 1 -> (k <= f)%nat ->
  hm_combine f c = Nat.iter k hm_combine_iter c.
Proof.
  induction f as [|f IH]; intros c k HN Hk.
  - replace k with 0%nat by lia. reflexivity.
  - rewrite hm_combine_S. destruct k as [|k].
    + replace (1 <? hm_nHeap c) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
    + replace (1 <? hm_nHeap c) with true by (symmetry; apply Z.ltb_lt; lia).
      rewrite (IH (hm_combine_iter c) k) by (try rewrite hm_combine_iter_nH; lia).
      symmetry. apply iter_S_r.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Pts.
  Variables (len0 freq : zarr) (lb fb A : Z).
  Definition hp_W0 : zarr := hm_winit (Z.to_nat A) znew freq fb 0.
  Definition hp_s0 : hmst := HMST len0 znew hp_W0 znew false.
  (* [comment removed for export] *)
  Definition hp_rs (r : nat) : hmst := Nat.iter r (hm_round A 17 lb) hp_s0.
  Definition hm_exec (r : nat) : Prop := forall r', (r' <= r)%nat -> hs_done (hp_rs r') = false.
  Lemma hp_rs_S : forall r, hp_rs (S r) = hm_round A 17 lb (hp_rs r). Proof. reflexivity. Qed.
  Lemma hbMakeCodeLengths_pt : forall h0 p0, h0 = znew -> p0 = znew ->
    hbMakeCodeLengths len0 freq h0 znew p0 lb fb A 17 = hm_rounds 40 A 17 lb hp_s0.
  Proof. intros h0 p0 -> ->. reflexivity. Qed.
End Pts.

(* [comment removed for export] *)
Definition hr_h0 (s : hmst) : zarr := zset (hs_heap s) 0 0.
Definition hr_w0 (s : hmst) : zarr := zset (hs_weight s) 0 0.
Definition hr_p0 (s : hmst) : zarr := zset (hs_parent s) 0 (-2).
Definition hr_c0 (A : Z) (s : hmst) : hms :=
  HMS (fill_h (Z.to_nat A) (hr_h0 s) (hr_w0 s) 0 1) (hr_w0 s) (pneg (hr_p0 s) 1 (Z.to_nat A)) A A.
Definition hr_cb (A : Z) (s : hmst) (k : nat) : hms := Nat.iter k hm_combine_iter (hr_c0 A s).
Definition hr_cf (A : Z) (s : hmst) : hms := hr_cb A s (Z.to_nat (A - 1)).
Definition hr_lens (A lb : Z) (s : hmst) : zarr * bool := hm_lens (Z.to_nat A) (hs_len s) (hm_parent (hr_cf A s)) lb 17 1 false.
Definition hr_wr (A : Z) (s : hmst) : zarr := hm_rescale (Z.to_nat A) (hm_weight (hr_cf A s)) 1.

Lemma hr_cb_S : forall A s k, hr_cb A s (S k) = hm_combine_iter (hr_cb A s k). Proof. reflexivity. Qed.
Lemma hr_cb_nH : forall A s k, hm_nHeap (hr_cb A s k) = A - Z.of_nat k.
Proof. intros. unfold hr_cb. rewrite iter_nH. reflexivity. Qed.
(* [comment removed for export] *)
Lemma hr_cf_eq : forall A s, 1 <= A -> hm_combine (Z.to_nat A) (hr_c0 A s) = hr_cf A s.
Proof. intros A s HA. unfold hr_cf, hr_cb. apply hm_combine_iter_run; [cbn [hm_nHeap hr_c0]; lia| lia]. Qed.

(* [comment removed for export] *)
Lemma hm_round_eq : forall A lb s, 1 <= A ->
  hm_round A 17 lb s =
  (let '(len, tooLong) := hr_lens A lb s in
   if tooLong then HMST len (hm_heap (hr_cf A s)) (hr_wr A s) (hm_parent (hr_cf A s)) false
   else HMST len (hm_heap (hr_cf A s)) (hm_weight (hr_cf A s)) (hm_parent (hr_cf A s)) true).
Proof.
  intros A lb s HA. unfold hm_round, hr_lens, hr_wr. fold (hr_h0 s) (hr_w0 s) (hr_p0 s).
  rewrite hm_fill_eq. rewrite Z.add_0_l, Z2Nat.id by lia. fold (hr_c0 A s). rewrite hr_cf_eq by lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition hw (h w : zarr) (nH nN : Z) : Prop :=
  zget h 0 = 0 /\ zget w 0 = 0 /\
  (forall z, 0 <= z <= nH -> zdef h z = true /\ 0 <= zget h z <= nN) /\
  (forall x, 0 <= x <= nN -> zdef w x = true /\ 0 <= zget w x < 2147483648).
(* [comment removed for export] *)
Definition hpar (p : zarr) (nN : Z) : Prop := forall x, 0 <= x <= nN -> zdef p x = true /\ -2 <= zget p x <= nN.

Lemma hw_hset : forall h w nH nN z v, hw h w nH nN -> 1 <= z -> 0 <= v <= nN -> hw (zset h z v) w nH nN.
Proof.
  (intros h w nH nN z v; cps_intros (S1 & S2 & HH & WW); intros Hz Hv). split; [rewrite zget_zset_other by lia; exact S1|]. split; [exact S2|]. split; [|exact WW].
  intros z' Hz'. rewrite zdef_zset, zget_zset. destruct (Z.eqb_spec z' z); cbn [orb]; [lia| apply HH; lia].
Qed.
Lemma hw_nH_le : forall h w nH nH' nN, hw h w nH nN -> nH' <= nH -> hw h w nH' nN.
Proof. (intros h w nH nH' nN; cps_intros (S1 & S2 & HH & WW); intros Hle). split; [exact S1|]. split; [exact S2|]. split; [|exact WW]. intros z Hz. apply HH. lia. Qed.
Lemma hw_push : forall h w nH nN v, hw h w nH nN -> 0 <= nH -> 0 <= v <= nN -> hw (zset h (nH + 1) v) w (nH + 1) nN.
Proof.
  (intros h w nH nN v; cps_intros (S1 & S2 & HH & WW); intros HnH Hv). split; [rewrite zget_zset_other by lia; exact S1|]. split; [exact S2|]. split; [|exact WW].
  intros z Hz. rewrite zdef_zset, zget_zset. destruct (Z.eqb_spec z (nH + 1)); cbn [orb]; [lia| apply HH; lia].
Qed.
Lemma hw_node : forall h w nH nN v, hw h w nH nN -> 0 <= nN -> 0 <= v < 2147483648 -> hw h (zset w (nN + 1) v) nH (nN + 1).
Proof.
  (intros h w nH nN v; cps_intros (S1 & S2 & HH & WW); intros HnN Hv). split; [exact S1|]. split; [rewrite zget_zset_other by lia; exact S2|]. split.
  - intros z Hz. destruct (HH z Hz). split; [assumption| lia].
  - intros x Hx. rewrite zdef_zset, zget_zset. destruct (Z.eqb_spec x (nN + 1)); cbn [orb]; [lia| apply WW; lia].
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma hpar_node : forall par nN n1 n2, hpar par nN -> (0 <= n1 <= nN)%Z -> (0 <= n2 <= nN)%Z ->
  hpar (zset (zset (zset par n2 (nN + 1)) n1 (nN + 1)) (nN + 1) (-1)) (nN + 1).
Proof.
  intros par nN n1 n2 HP H1 H2 x Hx. rewrite !zdef_zset, !zget_zset.
  destruct (Z.eqb_spec x (nN + 1)); cbn [orb]; [lia|].
  destruct (Z.eqb_spec x n1); cbn [orb]; [lia|]. destruct (Z.eqb_spec x n2); cbn [orb]; [lia|].
  destruct (HP x ltac:(lia)). split; [assumption| lia].
Qed.

(* [comment removed for export] *)
Lemma combine_iter_link1 : forall h w par nH nN hA zzA,
  downheap_loop 20 (zset h 1 (zget h nH)) w (nH - 1) 1 (zget h nH) = (hA, zzA) ->
  let s := HMS h w par nH nN in
  let hp1 := zset hA zzA (zget h nH) in
  cb_hp1 s = hp1 /\ cb_n1 s = zget h 1 /\ cb_n2 s = zget hp1 1 /\
  cb_w' s = zset w (nN + 1) (addweights (zget w (zget h 1)) (zget w (zget hp1 1))) /\
  cb_p' s = zset (zset (zset par (zget hp1 1) (nN + 1)) (zget h 1) (nN + 1)) (nN + 1) (-1).
Proof.
  intros h w par nH nN hA zzA E1. cbv zeta.
  assert (P1 : cb_hp1 (HMS h w par nH nN) = zset hA zzA (zget h nH)).
  { unfold cb_hp1, cb_h1. cbn [hm_heap hm_weight hm_nHeap].
    pose proof (downheap_eq (zset h 1 (zget h nH)) w (nH - 1) 1 hA zzA) as D. rewrite zget_zset_same in D. exact (D E1). }
  assert (N2 : cb_n2 (HMS h w par nH nN) = zget (zset hA zzA (zget h nH)) 1) by (unfold cb_n2; rewrite P1; reflexivity).
  assert (N1 : cb_n1 (HMS h w par nH nN) = zget h 1) by reflexivity.
  split; [exact P1|]. split; [exact N1|]. split; [exact N2|]. split.
  - unfold cb_w', cb_aw. rewrite N1, N2. reflexivity.
  - unfold cb_p'. rewrite N1, N2. reflexivity.
Qed.
Lemma combine_iter_link : forall h w par nH nN hA zzA hB zzB hC zzC,
  downheap_loop 20 (zset h 1 (zget h nH)) w (nH - 1) 1 (zget h nH) = (hA, zzA) ->
  (let hp1 := zset hA zzA (zget h nH) in
   downheap_loop 20 (zset hp1 1 (zget hp1 (nH - 1))) w (nH - 2) 1 (zget hp1 (nH - 1)) = (hB, zzB)) ->
  (let hp1 := zset hA zzA (zget h nH) in
   let aw := addweights (zget w (zget h 1)) (zget w (zget hp1 1)) in
   upheap_loop 20 (zset (zset hB zzB (zget hp1 (nH - 1))) (nH - 1) (nN + 1)) (zset w (nN + 1) aw) (nH - 1) (nN + 1) = (hC, zzC)) ->
  let s := HMS h w par nH nN in
  hm_combine_iter s = HMS (zset hC zzC (nN + 1)) (cb_w' s) (cb_p' s) (nH - 1) (nN + 1).
Proof.
  intros h w par nH nN hA zzA hB zzB hC zzC E1 E2 E3. cbv zeta in *.
  cps_destruct (combine_iter_link1 h w par nH nN hA zzA E1) as (P1 & N1 & N2 & W' & PP). cbv zeta in *.
  assert (P2 : cb_hp2 (HMS h w par nH nN) = zset hB zzB (zget (zset hA zzA (zget h nH)) (nH - 1))).
  { unfold cb_hp2, cb_h2. rewrite P1. cbn [hm_heap hm_weight hm_nHeap].
    pose proof (downheap_eq (zset (zset hA zzA (zget h nH)) 1 (zget (zset hA zzA (zget h nH)) (nH - 1))) w (nH - 2) 1 hB zzB) as D.
    rewrite zget_zset_same in D. exact (D E2). }
  rewrite hm_combine_iter_eq. unfold cb_h3. rewrite P2, W'. cbn [hm_heap hm_weight hm_nHeap hm_nNodes]. f_equal.
  pose proof (upheap_eq (zset (zset hB zzB (zget (zset hA zzA (zget h nH)) (nH - 1))) (nH - 1) (nN + 1))
                (zset w (nN + 1) (addweights (zget w (zget h 1)) (zget w (zget (zset hA zzA (zget h nH)) 1)))) (nH - 1) hC zzC) as U.
  rewrite zget_zset_same in U. exact (U E3).
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rf_w (A : Z) (s : hmst) : Prop :=
  forall x, 1 <= x <= A -> zdef (hs_weight s) x = true /\ 0 <= zget (hs_weight s) x < 2147483648.
(* [comment removed for export] *)
Definition rf_cb (c : hms) : Prop :=
  weightof (zget (hm_weight c) (cb_n1 c)) + weightof (zget (hm_weight c) (cb_n2 c)) <= 2147483136. (* [comment removed for export] *)
(* [comment removed for export] *)
Definition rf_par (A : Z) (c : hms) : Prop :=
  forall x, 1 <= x <= 2 * A - 1 -> zget (hm_parent c) x = -1 \/ x < zget (hm_parent c) x <= 2 * A - 1.
Definition round_facts (A : Z) (s : hmst) : Prop :=
  rf_w A s /\ (forall k, (k + 2 <= Z.to_nat A)%nat -> rf_cb (hr_cb A s k)) /\ rf_par A (hr_cf A s).

Definition hm_facts (len0 freq : zarr) (lb fb A : Z) : Prop :=
  hs_done (hm_rounds 40 A 17 lb (hp_s0 len0 freq fb A)) = true /\
  forall r, hm_exec len0 freq lb fb A r -> round_facts A (hp_rs len0 freq lb fb A r).
End BzCFactsHm.

From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
Module BzCHuffF7.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuff.
Import ListNotations.
Local Open Scope Z_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.

(* [comment removed for export] *)

Definition AG (n : Z) (a b : zarr) : Prop := forall z, 0 <= z <= n -> zget a z = zget b z.
Definition HR (n N : Z) (h : zarr) : Prop := forall z, 0 <= z <= n -> 0 <= zget h z <= N.
Definition PR (N : Z) (p : zarr) : Prop := forall k, 0 <= k <= N -> zget p k <= N.
Definition PRg (n N : Z) (p : zarr) : Prop := forall k, 0 <= k <= n -> zget p k <= N.

Lemma AG_set : forall n a b i v, AG n a b -> AG n (zset a i v) (zset b i v).
Proof. intros n a b i v H z Hz. rewrite !zget_zset. destruct (z =? i); [reflexivity| apply H; exact Hz]. Qed.
(* [comment removed for export] *)
Lemma HR_set : forall n N h i v, HR n N h -> 0 <= v <= N -> HR n N (zset h i v).
Proof. intros n N h i v H Hv z Hz. rewrite zget_zset. destruct (z =? i); [exact Hv| apply H; exact Hz]. Qed.
Lemma HR_le : forall n N N' h, HR n N h -> N <= N' -> HR n N' h.
Proof. intros n N N' h H L z Hz. pose proof (H z Hz). lia. Qed.
(* [comment removed for export] *)

Lemma shiftr1 : forall z, 0 <= z -> Z.shiftr z 1 = z / 2.
Proof. intros. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.
Lemma shiftl1 : forall z, Z.shiftl z 1 = 2 * z.
Proof. intros. rewrite Z.shiftl_mul_pow2 by lia. lia. Qed.

Section UP.
  Variables (n N : Z) (w1 w2 : zarr).
  Hypothesis WA : AG N w1 w2.

  Lemma upheap_loop_ag : forall f h1 h2 zz tmp,
    AG n h1 h2 -> HR n N h1 -> 0 <= zz <= n -> 0 <= tmp <= N ->
    let r1 := upheap_loop f h1 w1 zz tmp in let r2 := upheap_loop f h2 w2 zz tmp in
    AG n (fst r1) (fst r2) /\ snd r1 = snd r2 /\ HR n N (fst r1) /\ 0 <= snd r1 <= n.
  Proof.
    induction f as [|f IH]; intros h1 h2 zz tmp HA HH Hzz Ht; cbn zeta.
    - cbn [upheap_loop fst snd]. split; [exact HA| split; [reflexivity| split; [exact HH| exact Hzz]]].
    - cbn [upheap_loop]. rewrite shiftr1 by lia.
      assert (Hz2 : 0 <= zz / 2 <= n) by (split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]).
      rewrite <- (HA (zz / 2)) by exact Hz2.
      pose proof (HH (zz / 2) Hz2) as Hv.
      rewrite <- (WA tmp) by exact Ht. rewrite <- (WA (zget h1 (zz / 2))) by exact Hv.
      destruct (_ <? _).
      + apply IH; [apply AG_set; exact HA| apply HR_set; [exact HH| exact Hv]| exact Hz2| exact Ht].
      + cbn [fst snd]. split; [exact HA| split; [reflexivity| split; [exact HH| exact Hzz]]].
  Qed.

  Lemma upheap_ag : forall h1 h2 z, AG n h1 h2 -> HR n N h1 -> 0 <= z <= n ->
    AG n (upheap h1 w1 z) (upheap h2 w2 z) /\ HR n N (upheap h1 w1 z).
  Proof.
    intros h1 h2 z HA HH Hz. unfold upheap. rewrite <- (HA z) by exact Hz.
    pose proof (HH z Hz) as Ht.
    cps_destruct (upheap_loop_ag 20 h1 h2 z (zget h1 z) HA HH Hz Ht) as (A1 & E1 & R1 & B1).
    destruct (upheap_loop 20 h1 w1 z _) as [ha za]. destruct (upheap_loop 20 h2 w2 z _) as [hb zb]. cbn [fst snd] in *. subst zb.
    split; [apply AG_set; exact A1| apply HR_set; [exact R1| exact Ht]].
  Qed.

  Lemma downheap_loop_ag : forall f h1 h2 nH zz tmp,
    AG n h1 h2 -> HR n N h1 -> 0 <= nH -> nH + 1 <= n -> 0 <= zz <= n -> 0 <= tmp <= N ->
    let r1 := downheap_loop f h1 w1 nH zz tmp in let r2 := downheap_loop f h2 w2 nH zz tmp in
    AG n (fst r1) (fst r2) /\ snd r1 = snd r2 /\ HR n N (fst r1) /\ 0 <= snd r1 <= n.
  Proof.
    induction f as [|f IH]; intros h1 h2 nH zz tmp HA HH HnH Hn Hzz Ht; cbn zeta.
    - cbn [downheap_loop fst snd]. split; [exact HA| split; [reflexivity| split; [exact HH| exact Hzz]]].
    - cbn [downheap_loop]. rewrite shiftl1.
      destruct (Z.ltb_spec nH (2 * zz)) as [L|L]; [cbn [fst snd]; split; [exact HA| split; [reflexivity| split; [exact HH| exact Hzz]]]|].
      destruct (Z.ltb_spec (2 * zz) nH) as [L2|L2]; cbn [andb].
      + rewrite <- (HA (2 * zz + 1)), <- (HA (2 * zz)) by lia.
        pose proof (HH (2 * zz + 1) ltac:(lia)) as V1. pose proof (HH (2 * zz) ltac:(lia)) as V0.
        rewrite <- (WA (zget h1 (2 * zz + 1))), <- (WA (zget h1 (2 * zz))) by assumption.
        set (yy := if _ <? _ then 2 * zz + 1 else 2 * zz).
        assert (Hyy : 0 <= yy <= n /\ 0 <= zget h1 yy <= N) by (subst yy; destruct (_ <? _); split; try lia; assumption).
        destruct Hyy as [Y1 Y2].
        rewrite <- (HA yy) by exact Y1. rewrite <- (WA tmp), <- (WA (zget h1 yy)) by assumption.
        destruct (zget w1 tmp <? zget w1 (zget h1 yy)); [cbn [fst snd]; split; [exact HA| split; [reflexivity| split; [exact HH| exact Hzz]]]|].
        apply IH; try assumption; [apply AG_set; exact HA| apply HR_set; assumption].
      + rewrite <- (HA (2 * zz)) by lia. pose proof (HH (2 * zz) ltac:(lia)) as V0.
        rewrite <- (WA tmp), <- (WA (zget h1 (2 * zz))) by assumption.
        destruct (zget w1 tmp <? zget w1 (zget h1 (2 * zz))); [cbn [fst snd]; split; [exact HA| split; [reflexivity| split; [exact HH| exact Hzz]]]|].
        apply IH; try assumption; [apply AG_set; exact HA| apply HR_set; assumption| lia].
  Qed.

  Lemma downheap_ag : forall h1 h2 nH z, AG n h1 h2 -> HR n N h1 -> 0 <= nH -> nH + 1 <= n -> 0 <= z <= n ->
    AG n (downheap h1 w1 nH z) (downheap h2 w2 nH z) /\ HR n N (downheap h1 w1 nH z).
  Proof.
    intros h1 h2 nH z HA HH H1 H2 Hz. unfold downheap. rewrite <- (HA z) by exact Hz. pose proof (HH z Hz) as Ht.
    cps_destruct (downheap_loop_ag 20 h1 h2 nH z (zget h1 z) HA HH H1 H2 Hz Ht) as (A1 & E1 & R1 & B1).
    destruct (downheap_loop 20 h1 w1 nH z _) as [ha za]. destruct (downheap_loop 20 h2 w2 nH z _) as [hb zb]. cbn [fst snd] in *. subst zb.
    split; [apply AG_set; exact A1| apply HR_set; [exact R1| exact Ht]].
  Qed.
End UP.

(* [comment removed for export] *)
Lemma fill_ag : forall k h1 h2 w1 w2 p1 p2 nH i N M,
  AG N w1 w2 -> AG nH h1 h2 -> HR nH N h1 -> AG (i - 1) p1 p2 -> PRg (i - 1) M p1 -> 0 <= M ->
  0 <= nH -> 1 <= i -> i - 1 + Z.of_nat k <= N ->
  let r1 := hm_fill k h1 w1 p1 nH i in let r2 := hm_fill k h2 w2 p2 nH i in
  snd r1 = snd r2 /\ snd r1 = nH + Z.of_nat k /\
  AG (snd r1) (fst (fst r1)) (fst (fst r2)) /\ HR (snd r1) N (fst (fst r1)) /\
  AG (i - 1 + Z.of_nat k) (snd (fst r1)) (snd (fst r2)) /\ PRg (i - 1 + Z.of_nat k) M (snd (fst r1)).
Proof.
  induction k as [|k IH]; intros h1 h2 w1 w2 p1 p2 nH i N M WA HA HH PA PP HM HnH Hi Hk; cbn zeta.
  - cbn [hm_fill fst snd]. rewrite !Z.add_0_r. split; [reflexivity| split; [reflexivity| split; [exact HA| split; [exact HH| split; [exact PA| exact PP]]]]].
  - cbn [hm_fill].
    assert (HA' : AG (nH + 1) (zset h1 (nH + 1) i) (zset h2 (nH + 1) i)).
    { intros z Hz. rewrite !zget_zset. destruct (Z.eqb_spec z (nH + 1)); [reflexivity| apply HA; lia]. }
    assert (HH' : HR (nH + 1) N (zset h1 (nH + 1) i)).
    { intros z Hz. rewrite zget_zset. destruct (Z.eqb_spec z (nH + 1)); [lia| apply HH; lia]. }
    destruct (upheap_ag (nH + 1) N w1 w2 WA _ _ (nH + 1) HA' HH' ltac:(lia)) as [UA UH].
    specialize (IH (upheap (zset h1 (nH + 1) i) w1 (nH + 1)) (upheap (zset h2 (nH + 1) i) w2 (nH + 1)) w1 w2 (zset p1 i (-1)) (zset p2 i (-1)) (nH + 1) (i + 1) N M WA UA UH).
    replace (i + 1 - 1) with (i - 1 + 1) in IH by lia.
    cps_destruct IH as (E1 & E2 & A3 & R3 & A4 & P4); [| | exact HM| lia| lia| lia|].
    { intros z Hz. rewrite !zget_zset. destruct (Z.eqb_spec z i); [reflexivity| apply PA; lia]. }
    { intros z Hz. rewrite zget_zset. destruct (Z.eqb_spec z i); [lia| apply PP; lia]. }
    replace (i - 1 + Z.of_nat (S k)) with (i - 1 + 1 + Z.of_nat k) by lia. replace (nH + Z.of_nat (S k)) with (nH + 1 + Z.of_nat k) by lia.
    split; [exact E1| split; [exact E2| split; [exact A3| split; [exact R3| split; [exact A4| exact P4]]]]].
Qed.

(* [comment removed for export] *)
Record CA (A : Z) (s1 s2 : hms) : Prop := MKCA {
  ca_nH : hm_nHeap s1 = hm_nHeap s2; ca_nN : hm_nNodes s1 = hm_nNodes s2;
  ca_h : AG A (hm_heap s1) (hm_heap s2); ca_hr : HR A (hm_nNodes s1) (hm_heap s1);
  ca_w : AG (hm_nNodes s1) (hm_weight s1) (hm_weight s2);
  ca_p : AG (hm_nNodes s1) (hm_parent s1) (hm_parent s2); ca_pr : PR (hm_nNodes s1) (hm_parent s1);
  ca_b : 0 <= hm_nHeap s1 <= A; ca_nn : A <= hm_nNodes s1 }.

Lemma combine_iter_ag : forall A s1 s2, CA A s1 s2 -> 1 < hm_nHeap s1 -> CA A (hm_combine_iter s1) (hm_combine_iter s2).
Proof.
  intros A [h1 w1 p1 nH1 nN1] [h2 w2 p2 nH2 nN2] C L. destruct C as [EH EN HA HH WA PA PP HB HN]; cbn [hm_heap hm_weight hm_parent hm_nHeap hm_nNodes] in *.
  assert (HN0 : 0 <= nN1) by lia.
  subst nH2 nN2. unfold hm_combine_iter. cbn [hm_heap hm_weight hm_parent hm_nHeap hm_nNodes].
  (* [comment removed for export] *)
  rewrite <- (HA 1), <- (HA nH1) by lia.
  set (ha1 := zset h1 1 (zget h1 nH1)). set (ha2 := zset h2 1 (zget h1 nH1)).
  assert (A1 : AG A ha1 ha2) by (apply AG_set; exact HA). assert (R1 : HR A nN1 ha1) by (apply HR_set; [exact HH| apply HH; lia]).
  destruct (downheap_ag A nN1 w1 w2 WA ha1 ha2 (nH1 - 1) 1 A1 R1 ltac:(lia) ltac:(lia) ltac:(lia)) as [A2 R2].
  set (hb1 := downheap ha1 w1 (nH1 - 1) 1) in *. set (hb2 := downheap ha2 w2 (nH1 - 1) 1) in *.
  (* [comment removed for export] *)
  rewrite <- (A2 1), <- (A2 (nH1 - 1)) by lia.
  set (hc1 := zset hb1 1 (zget hb1 (nH1 - 1))). set (hc2 := zset hb2 1 (zget hb1 (nH1 - 1))).
  assert (A3 : AG A hc1 hc2) by (apply AG_set; exact A2). assert (R3 : HR A nN1 hc1) by (apply HR_set; [exact R2| apply R2; lia]).
  destruct (downheap_ag A nN1 w1 w2 WA hc1 hc2 (nH1 - 1 - 1) 1 A3 R3 ltac:(lia) ltac:(lia) ltac:(lia)) as [A4 R4].
  set (hd1 := downheap hc1 w1 (nH1 - 1 - 1) 1) in *. set (hd2 := downheap hc2 w2 (nH1 - 1 - 1) 1) in *.
  (* [comment removed for export] *)
  pose proof (HH 1 ltac:(lia)) as N1. pose proof (R2 1 ltac:(lia)) as N2.
  set (n1 := zget h1 1) in *. set (n2 := zget hb1 1) in *.
  rewrite <- (WA n1), <- (WA n2) by assumption.
  set (wv := addweights (zget w1 n1) (zget w1 n2)).
  set (we1 := zset w1 (nN1 + 1) wv). set (we2 := zset w2 (nN1 + 1) wv).
  assert (WA' : AG (nN1 + 1) we1 we2).
  { intros z Hz. subst we1 we2. rewrite !zget_zset. destruct (Z.eqb_spec z (nN1 + 1)); [reflexivity| apply WA; lia]. }
  set (hf1 := zset hd1 (nH1 - 1 - 1 + 1) (nN1 + 1)). set (hf2 := zset hd2 (nH1 - 1 - 1 + 1) (nN1 + 1)).
  assert (A5 : AG A hf1 hf2) by (apply AG_set; exact A4).
  assert (R5 : HR A (nN1 + 1) hf1) by (apply HR_set; [apply HR_le with nN1; [exact R4| lia]| lia]).
  destruct (upheap_ag A (nN1 + 1) we1 we2 WA' hf1 hf2 (nH1 - 1 - 1 + 1) A5 R5 ltac:(lia)) as [A6 R6].
  constructor; cbn [hm_heap hm_weight hm_parent hm_nHeap hm_nNodes]; try reflexivity; try assumption; try lia.
  - intros z Hz. rewrite !zget_zset. destruct (Z.eqb_spec z (nN1 + 1)); [reflexivity|]. destruct (Z.eqb_spec z n1); [reflexivity|].
    destruct (Z.eqb_spec z n2); [reflexivity|]. apply PA. lia.
  - intros k Hk. rewrite !zget_zset. destruct (Z.eqb_spec k (nN1 + 1)); [lia|]. destruct (Z.eqb_spec k n1); [lia|].
    destruct (Z.eqb_spec k n2); [lia|]. pose proof (PP k ltac:(lia)). lia.
Qed.

Lemma combine_ag : forall f A s1 s2, CA A s1 s2 -> CA A (hm_combine f s1) (hm_combine f s2).
Proof.
  induction f as [|f IH]; intros A s1 s2 C; cbn [hm_combine]; [exact C|].
  rewrite <- (ca_nH A s1 s2 C). destruct (Z.ltb_spec 1 (hm_nHeap s1)) as [L|L]; [| exact C].
  apply IH. apply combine_iter_ag; [exact C| exact L].
Qed.

Lemma depth_ag : forall f p1 p2 N k j, AG N p1 p2 -> PR N p1 -> 0 <= k <= N -> hm_depth f p1 k j = hm_depth f p2 k j.
Proof.
  induction f as [|f IH]; intros p1 p2 N k j PA PP Hk; cbn [hm_depth]; [reflexivity|].
  rewrite <- (PA k) by exact Hk. destruct (Z.leb_spec 0 (zget p1 k)) as [L|L]; [| reflexivity].
  apply (IH p1 p2 N); [exact PA| exact PP|]. pose proof (PP k Hk). lia.
Qed.

Lemma lens_ag : forall n len p1 p2 lb mL i tl N, AG N p1 p2 -> PR N p1 -> 0 <= i -> i - 1 + Z.of_nat n <= N ->
  hm_lens n len p1 lb mL i tl = hm_lens n len p2 lb mL i tl.
Proof.
  induction n as [|n IH]; intros len p1 p2 lb mL i tl N PA PP Hi Hn; cbn [hm_lens]; [reflexivity|].
  rewrite (depth_ag 600 p1 p2 N i 0 PA PP ltac:(lia)). apply IH with N; [exact PA| exact PP| lia| lia].
Qed.

Definition WG (A : Z) (w1 w2 : zarr) : Prop := forall z, 1 <= z <= A -> zget w1 z = zget w2 z.

Lemma rescale_ag : forall n w1 w2 i A, WG A w1 w2 -> 1 <= i -> WG A (hm_rescale n w1 i) (hm_rescale n w2 i).
Proof.
  induction n as [|n IH]; intros w1 w2 i A W Hi; cbn [hm_rescale]; [exact W|].
  destruct (Z.le_gt_cases i A) as [L|L].
  - rewrite <- (W i) by lia. apply IH; [| lia]. intros z Hz. rewrite !zget_zset. destruct (z =? i); [reflexivity| apply W; exact Hz].
  - apply IH; [| lia]. intros z Hz. rewrite !zget_zset_other by lia. apply W. exact Hz.
Qed.

Lemma winit_ag : forall n w1 w2 freq fb i A, WG (i) w1 w2 -> 0 <= i -> i + Z.of_nat n = A -> WG A (hm_winit n w1 freq fb i) (hm_winit n w2 freq fb i).
Proof.
  induction n as [|n IH]; intros w1 w2 freq fb i A W Hi Hn; cbn [hm_winit].
  - replace A with i by lia. exact W.
  - apply IH; [| lia| lia]. intros z Hz. rewrite !zget_zset. destruct (Z.eqb_spec z (i + 1)); [reflexivity| apply W; lia].
Qed.

Definition RA (A : Z) (s1 s2 : hmst) : Prop := hs_len s1 = hs_len s2 /\ hs_done s1 = hs_done s2 /\ WG A (hs_weight s1) (hs_weight s2).

Lemma round_ag : forall A mL lb s1 s2, 1 <= A -> RA A s1 s2 -> RA A (hm_round A mL lb s1) (hm_round A mL lb s2).
Proof.
  (intros A mL lb [l1 h1 w1 p1 d1] [l2 h2 w2 p2 d2] HA; cps_intros (EL & ED & W)). cbn [hs_len hs_done hs_weight] in *. subst l2 d2.
  unfold hm_round. cbn [hs_len hs_heap hs_weight hs_parent].
  set (wa1 := zset w1 0 0). set (wa2 := zset w2 0 0).
  assert (WA : AG A wa1 wa2).
  { intros z Hz. subst wa1 wa2. rewrite !zget_zset. destruct (Z.eqb_spec z 0); [reflexivity| apply W; lia]. }
  pose proof (fill_ag (Z.to_nat A) (zset h1 0 0) (zset h2 0 0) wa1 wa2 (zset p1 0 (-2)) (zset p2 0 (-2)) 0 1 A A WA) as F.
  cps_destruct F as (E1 & E2 & A3 & R3 & A4 & P4).
  { intros z Hz. rewrite !zget_zset. destruct (Z.eqb_spec z 0); [reflexivity| lia]. }
  { intros z Hz. rewrite zget_zset. destruct (Z.eqb_spec z 0); lia. }
  { intros z Hz. rewrite !zget_zset. destruct (Z.eqb_spec z 0); [reflexivity| lia]. }
  { intros k Hk. rewrite zget_zset. destruct (Z.eqb_spec k 0); lia. }
  all: try lia.
  destruct (hm_fill (Z.to_nat A) (zset h1 0 0) wa1 _ 0 1) as [[ha pa] na].
  destruct (hm_fill (Z.to_nat A) (zset h2 0 0) wa2 _ 0 1) as [[hb pb] nb].
  cbn [fst snd] in E1, E2, A3, R3, A4, P4. subst nb.
  replace (1 - 1 + Z.of_nat (Z.to_nat A)) with A in A4, P4 by lia. replace (0 + Z.of_nat (Z.to_nat A)) with A in E2 by lia. subst na.
  assert (C0 : CA A (HMS ha wa1 pa A A) (HMS hb wa2 pb A A)).
  { constructor; cbn [hm_heap hm_weight hm_parent hm_nHeap hm_nNodes]; try reflexivity; try assumption; lia. }
  pose proof (combine_ag (Z.to_nat A) A _ _ C0) as CC.
  set (c1 := hm_combine (Z.to_nat A) (HMS ha wa1 pa A A)) in *. set (c2 := hm_combine (Z.to_nat A) (HMS hb wa2 pb A A)) in *.
  destruct CC as [EH EN CH CR CW CP CPP CB CN].
  rewrite <- (lens_ag (Z.to_nat A) l1 (hm_parent c1) (hm_parent c2) lb mL 1 false (hm_nNodes c1) CP CPP ltac:(lia) ltac:(lia)).
  destruct (hm_lens (Z.to_nat A) l1 (hm_parent c1) lb mL 1 false) as [len tl].
  assert (WGc : WG A (hm_weight c1) (hm_weight c2)) by (intros z Hz; apply CW; lia).
  destruct tl; (split; [reflexivity| split; [reflexivity|]]); cbn [hs_weight]; [apply rescale_ag; [exact WGc| lia]| exact WGc].
Qed.

Lemma rounds_ag : forall f A mL lb s1 s2, 1 <= A -> RA A s1 s2 -> RA A (hm_rounds f A mL lb s1) (hm_rounds f A mL lb s2).
Proof.
  induction f as [|f IH]; intros A mL lb s1 s2 HA R; cbn [hm_rounds]; [exact R|].
  cps_destruct R as (EL & ED & W). rewrite <- ED. destruct (hs_done s1) eqn:D1; [split; [exact EL| split; [rewrite D1; exact ED| exact W]]|].
  apply IH; [exact HA|]. apply round_ag; [exact HA|]. split; [exact EL| split; [rewrite D1; exact ED| exact W]].
Qed.

Theorem hbMakeCodeLengths_len_indep : forall len freq h w p lb fb A, 3 <= A <= 258 -> 0 <= fb ->
  (forall v, 0 <= v < A -> 0 <= zget freq (fb + v) < 8388608) ->
  hs_len (hbMakeCodeLengths len freq h w p lb fb A 17) = hs_len (hbMakeCodeLengths len freq znew znew znew lb fb A 17).
Proof.
  intros len freq h w p lb fb A HA _ _. unfold hbMakeCodeLengths.
  match goal with |- hs_len (hm_rounds _ _ _ _ ?s1) = hs_len (hm_rounds _ _ _ _ ?s2) => assert (R0 : RA A s1 s2) end.
  { split; [reflexivity| split; [reflexivity|]]. cbn [hs_weight]. apply winit_ag; [intros z Hz; lia| lia| lia]. }
  exact (proj1 (rounds_ag 40 A 17 lb _ _ ltac:(lia) R0)).
Qed.

End BzCHuffF7.

Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition tw (x : Z) : Z := x / 256.
Definition W32 (x : Z) : Prop := 0 <= x < 4294967296.

Lemma weightof_eq : forall x, W32 x -> weightof x = 256 * tw x.
Proof.
  intros x Hx. unfold weightof, tw, W32 in *. change 4294967040 with (Z.ldiff (Z.ones 32) (Z.ones 8)).
  rewrite Z.ldiff_land, Z.land_assoc, <- Z.ldiff_land, Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite Z.ldiff_ones_r, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change (2^8) with 256. lia.
Qed.

Lemma depthof_range : forall x, 0 <= depthof x < 256.
Proof. intros x. unfold depthof. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. Qed.

Lemma tw_mono : forall x y, x <= y -> tw x <= tw y.
Proof. intros. unfold tw. apply Z.div_le_mono; lia. Qed.
Lemma tw_nonneg : forall x, 0 <= x -> 0 <= tw x.
Proof. intros. unfold tw. apply Z.div_pos; lia. Qed.
Lemma tw_bounds : forall x, 256 * tw x <= x < 256 * tw x + 256.
Proof. intros. unfold tw. pose proof (Z.div_mod x 256 ltac:(lia)). pose proof (Z.mod_pos_bound x 256 ltac:(lia)). lia. Qed.

Lemma land_le_l : forall a b, 0 <= a -> Z.land a b <= a.
Proof.
  intros a b Ha. pose proof (Z.lor_ldiff_and a b) as E. pose proof (Z.add_lor_land (Z.ldiff a b) (Z.land a b)) as F.
  rewrite E in F. rewrite (Z.land_comm (Z.ldiff a b)), <- Z.land_assoc, (Z.land_comm b), Z.land_ldiff, Z.land_0_r in F.
  pose proof (proj2 (Z.ldiff_nonneg a b) (or_introl Ha)). lia.
Qed.

Lemma lor_bounds : forall a b, 0 <= a -> 0 <= b -> Z.max a b <= Z.lor a b <= a + b.
Proof.
  intros a b Ha Hb. pose proof (Z.add_lor_land a b). pose proof (land_le_l a b Ha).
  pose proof (land_le_l b a Hb). rewrite Z.land_comm in H1. pose proof (proj2 (Z.land_nonneg a b) (or_introl Ha)). lia.
Qed.

(* [comment removed for export] *)
Lemma addweights_bounds : forall a b, W32 a -> W32 b ->
  256 * (tw a + tw b) <= addweights a b <= 256 * (tw a + tw b) + 256.
Proof.
  intros a b Ha Hb. unfold addweights. rewrite !weightof_eq by assumption.
  pose proof (depthof_range a). pose proof (depthof_range b).
  pose proof (tw_nonneg a (proj1 Ha)). pose proof (tw_nonneg b (proj1 Hb)).
  pose proof (lor_bounds (256 * tw a + 256 * tw b) (1 + Z.max (depthof a) (depthof b)) ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma addweights_tw : forall a b, W32 a -> W32 b -> tw a + tw b <= tw (addweights a b) <= tw a + tw b + 1.
Proof.
  intros a b Ha Hb. pose proof (addweights_bounds a b Ha Hb) as AB.
  set (s := tw a + tw b) in *. unfold tw.
  split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Heap.
  Variable w : zarr.                      (* [comment removed for export] *)
  Let key (x : Z) : Z := zget w x.

  (* [comment removed for export] *)
  Definition HO (h : zarr) (n : Z) : Prop := forall z, 2 <= z <= n -> key (zget h (z / 2)) <= key (zget h z).

  (* [comment removed for export] *)
  Definition UI (h : zarr) (n e : Z) : Prop :=
    (forall z, 2 <= z <= n -> z <> e -> key (zget h (z / 2)) <= key (zget h z)) /\
    (forall c, 2 <= c <= n -> c / 2 = e -> 2 <= e -> key (zget h (e / 2)) <= key (zget h c)).

  (* [comment removed for export] *)
  Definition hcnt (h : zarr) (n v : Z) : Z := cntP (fun i => zget h (i + 1) =? v) (Z.to_nat n).

  Lemma hcnt_ext : forall h h' n v, (forall z, 1 <= z <= n -> zget h' z = zget h z) -> hcnt h' n v = hcnt h n v.
  Proof. intros h h' n v E. unfold hcnt. apply cntP_ext. intros i Hi. rewrite E by lia. reflexivity. Qed.

  Lemma cntP_ex : forall P n, 1 <= cntP P n -> exists i, 0 <= i < Z.of_nat n /\ P i = true.
  Proof.
    induction n as [|n IH]; intros H; cbn in H; [lia|].
    destruct (P (Z.of_nat n)) eqn:E.
    - exists (Z.of_nat n). split; [lia|exact E].
    - cps_destruct (IH ltac:(lia)) as (i & Hi & Pi). exists i. split; [lia|exact Pi].
  Qed.

  Lemma hcnt_in : forall h n z, 1 <= z <= n -> 1 <= hcnt h n (zget h z).
  Proof. intros h n z Hz. unfold hcnt. apply (cntP_pos _ _ (z - 1)); [lia|]. replace (z - 1 + 1) with z by lia. apply Z.eqb_refl. Qed.

  Lemma hcnt_ex : forall h n v, 1 <= hcnt h n v -> exists z, 1 <= z <= n /\ zget h z = v.
  Proof.
    intros h n v H. cps_destruct (cntP_ex _ _ H) as (i & Hi & E). exists (i + 1). split; [lia|]. apply Z.eqb_eq. exact E.
  Qed.

  (* [comment removed for export] *)
  Lemma hcnt_swap : forall h n a b v, 1 <= a <= n -> 1 <= b <= n ->
    hcnt (zset (zset h a (zget h b)) b (zget h a)) n v = hcnt h n v.
  Proof.
    intros h n a b v Ha Hb. unfold hcnt.
    destruct (Z.eq_dec a b) as [->|NE].
    { apply cntP_ext. intros i Hi. rewrite !zget_zset. destruct (Z.eqb_spec (i+1) b) as [->|]; reflexivity. }
    (* [comment removed for export] *)
    set (P := fun i => zget h (i + 1) =? v).
    set (Q := fun i => zget (zset (zset h a (zget h b)) b (zget h a)) (i + 1) =? v).
    assert (HQ : forall i, Q i = if i + 1 =? b then P (a - 1) else if i + 1 =? a then P (b - 1) else P i).
    { intros i. subst P Q. cbn beta. rewrite !zget_zset. replace (a - 1 + 1) with a by lia. replace (b - 1 + 1) with b by lia.
      destruct (Z.eqb_spec (i + 1) b); [reflexivity|]. destruct (Z.eqb_spec (i + 1) a); reflexivity. }
    (* [comment removed for export] *)
    assert (SS : forall (g : Z -> Z) j m, sumF g j (S m) = g j + sumF g (j + 1) m) by (intros; reflexivity).
    assert (SN : forall (g : Z -> Z) k j, sumF g j (S k) = sumF g j k + g (j + Z.of_nat k)).
    { intros g. induction k as [|k IHk]; intros j.
      - rewrite SS. cbn [sumF]. replace (j + Z.of_nat 0) with j by lia. lia.
      - rewrite SS, (IHk (j + 1)), SS. replace (j + 1 + Z.of_nat k) with (j + Z.of_nat (S k)) by lia. lia. }
    assert (CS : forall R m, cntP R m = sumF (fun i => if R i then 1 else 0) 0 m).
    { intros R m. induction m as [|m IH]; cbn [cntP]; [reflexivity|]. rewrite IH, SN, Z.add_0_l. reflexivity. }
    rewrite !CS.
    set (f := fun i => if P i then 1 else 0).
    transitivity (sumF (fun i => if i =? b - 1 then f (a - 1) else if i =? a - 1 then f (b - 1) else f i) 0 (Z.to_nat n)).
    { apply sumF_ext. intros i Hi. rewrite HQ. subst f. cbn beta.
      replace (i + 1 =? b) with (i =? b - 1) by (destruct (Z.eqb_spec (i+1) b), (Z.eqb_spec i (b-1)); try reflexivity; lia).
      replace (i + 1 =? a) with (i =? a - 1) by (destruct (Z.eqb_spec (i+1) a), (Z.eqb_spec i (a-1)); try reflexivity; lia).
      destruct (i =? b - 1); [reflexivity|]. destruct (i =? a - 1); reflexivity. }
    (* [comment removed for export] *)
    rewrite (sumF_upd (Z.to_nat n) (fun i => if i =? a - 1 then f (b - 1) else f i) _ 0 (b - 1) (f (a - 1) - f (b - 1))).
    - rewrite (sumF_upd (Z.to_nat n) f _ 0 (a - 1) (f (b - 1) - f (a - 1))); [lia|lia|].
      intros x. destruct (Z.eqb_spec x (a - 1)); [subst; lia|reflexivity].
    - lia.
    - intros x. destruct (Z.eqb_spec x (b - 1)) as [->|NB].
      + replace (b - 1 =? a - 1) with false by (symmetry; apply Z.eqb_neq; lia). lia.
      + reflexivity.
  Qed.

End Heap.
