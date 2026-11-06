(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzModel BzLemmasT BzR5a BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDOut.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzModel OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasT OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5a OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOut.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma iif_loopD_state : forall (cf : zarr) indx k t,
  (t <= 7)%nat -> (8 - t <= k)%nat ->
  let '(nb, na) := iif_state (zget cf) indx t in
  BzDBlock.iif_loop k cf indx nb na = fst (iif_state (zget cf) indx 8).
Proof.
  intros cf indx k. induction k as [|k IH]; intros t Ht Hk; [lia|].
  pose proof (iif_step_facts (zget cf) indx t Ht) as SF.
  destruct (iif_state (zget cf) indx t) as [nb na] eqn:E0.
  cps_destruct SF as (A & B & C & D & E & F & SF).
  destruct (iif_state (zget cf) indx (S t)) as [nb' na'] eqn:E1.
  cps_destruct SF as (EQ & G & H & I & J).
  cbn [BzDBlock.iif_loop].
  destruct (zget cf (Z.shiftr (nb + na) 1) <=? indx); injection EQ as -> ->.
  - destruct (Z.eqb_spec (na - Z.shiftr (nb + na) 1) 1) as [X|X].
    + apply J in X. subst t. rewrite E1. reflexivity.
    + destruct (Nat.eq_dec t 7) as [->|NE]; [exfalso; apply X; now apply J|].
      pose proof (IH (S t) ltac:(lia) ltac:(lia)) as R. rewrite E1 in R. exact R.
  - destruct (Z.eqb_spec (Z.shiftr (nb + na) 1 - nb) 1) as [X|X].
    + apply J in X. subst t. rewrite E1. reflexivity.
    + destruct (Nat.eq_dec t 7) as [->|NE]; [exfalso; apply X; now apply J|].
      pose proof (IH (S t) ltac:(lia) ltac:(lia)) as R. rewrite E1 in R. exact R.
Qed.

Lemma indexIntoF_state : forall indx cf, indexIntoF indx cf = fst (iif_state (zget cf) indx 8).
Proof.
  intros indx cf. unfold indexIntoF.
  pose proof (iif_loopD_state cf indx 9 0 ltac:(lia) ltac:(lia)) as L. cbn [iif_state] in L. exact L.
Qed.

Lemma indexIntoF_eq : forall indx cf, indexIntoF indx cf = index_into_f indx (zget cf).
Proof.
  intros indx cf. rewrite indexIntoF_state. symmetry. apply (proj1 (index_into_f_spec indx (zget cf))).
Qed.

Lemma indexIntoF_range : forall indx cf, 0 <= indexIntoF indx cf <= 255.
Proof. intros. rewrite indexIntoF_eq. apply (proj2 (index_into_f_spec _ _)). Qed.

(* [comment removed for export] *)
Lemma iif_mid_eq : forall nb na, 0 <= nb + na <= 512 -> (nb + na) / 2 = Z.shiftr (nb + na) 1.
Proof. intros nb na H. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma iif_stepW : forall cftab indx t nb na,
  (t <= 7)%nat -> iif_state cftab indx t = (nb, na) ->
  let mid := (nb + na) / 2 in
  0 <= nb /\ nb < mid /\ mid < na /\ na <= 256 /\
  iif_state cftab indx (S t) = (if cftab mid <=? indx then (mid, na) else (nb, mid)) /\
  ((if cftab mid <=? indx then na - mid else mid - nb) = 1 <-> t = 7%nat).
Proof.
  intros cftab indx t nb na Ht E.
  pose proof (iif_step_facts cftab indx t Ht) as SF. rewrite E in SF.
  cps_destruct SF as (A & B & C & D & E5 & F & SF).
  destruct (iif_state cftab indx (S t)) as [nb' na'] eqn:E1.
  cps_destruct SF as (EQ & G & H & I & J).
  rewrite (iif_mid_eq nb na) by lia.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  destruct (cftab (Z.shiftr (nb + na) 1) <=? indx); injection EQ as -> ->; (split; [reflexivity| exact J]).
Qed.

(* [comment removed for export] *)
Lemma iif_result : forall cf indx nb na,
  iif_state (zget cf) indx 8 = (nb, na) -> indexIntoF indx cf = nb.
Proof. intros cf indx nb na E. rewrite indexIntoF_state, E. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition llval (v16 v4 i : Z) : Z := v16 + (Z.shiftr v4 (Z.land (i * 4) 4) mod 16) * 65536.

Lemma lor_hi16 : forall lo hi, 0 <= lo < 65536 -> 0 <= hi -> Z.lor (hi * 65536) lo = hi * 65536 + lo.
Proof.
  intros lo hi Hlo Hhi. apply (lor_disjoint (hi * 65536) lo 16); try lia.
  change (2 ^ 16) with 65536. apply Z_mod_mult.
Qed.

Lemma get_ll_llval : forall d i, 0 <= i -> 0 <= zget (d_ll16 d) i < 65536 -> 0 <= zget (d_ll4 d) (i / 2) ->
  get_ll d i = llval (zget (d_ll16 d) i) (zget (d_ll4 d) (i / 2)) i.
Proof.
  intros d i Hi H16 H4. unfold get_ll, get_ll4, llval.
  rewrite (Z.shiftr_div_pow2 i 1), Z.pow_1_r by lia. rewrite (Z.shiftl_mul_pow2 i 2) by lia. change (2^2) with 4.
  rewrite Z.shiftl_mul_pow2 by lia. change (2^16) with 65536.
  change 15 with (Z.ones 4). rewrite Z.land_ones by lia. change (2^4) with 16.
  rewrite Z.lor_comm. rewrite lor_hi16; [lia| lia|]. apply Z.mod_pos_bound. lia.
Qed.

Lemma llval_range : forall v16 v4 i, 0 <= v16 < 65536 -> 0 <= v4 -> 0 <= i -> 0 <= llval v16 v4 i < 1048576.
Proof.
  intros v16 v4 i H16 H4 Hi. unfold llval.
  pose proof (Z.mod_pos_bound (Z.shiftr v4 (Z.land (i * 4) 4)) 16 ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma shl60_shr44 : forall x, 0 <= x ->
  (x * 1152921504606846976) mod 18446744073709551616 / 17592186044416 = (x mod 16) * 65536.
Proof.
  intros x Hx. pose proof (Z.div_mod x 16 ltac:(lia)) as E. pose proof (Z.mod_pos_bound x 16 ltac:(lia)) as R.
  set (q := x / 16) in *. set (r := x mod 16) in *.
  replace (x * 1152921504606846976) with (r * 1152921504606846976 + q * 18446744073709551616) by lia.
  rewrite Z_mod_plus_full. rewrite Z.mod_small by lia.
  replace (r * 1152921504606846976) with (r * 65536 * 17592186044416) by lia. rewrite Z.div_mul by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma land4_mul4 : forall y, Z.land (y * 4) 4 = if Z.odd y then 4 else 0.
Proof.
  intros y. change 4 with (2 ^ 2) at 2 3.
  replace (y * 4) with (y * 2 ^ 2) by reflexivity.
  destruct (Z.odd y) eqn:B.
  - apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.pow2_bits_eqb by lia.
    destruct (Z.eqb_spec 2 n) as [<-|NE].
    + rewrite Z.mul_pow2_bits by lia. change (2 - 2) with 0. rewrite Z.bit0_odd, B. reflexivity.
    + apply Bool.andb_false_r.
  - apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.pow2_bits_eqb, Z.bits_0 by lia.
    destruct (Z.eqb_spec 2 n) as [<-|NE].
    + rewrite Z.mul_pow2_bits by lia. change (2 - 2) with 0. rewrite Z.bit0_odd, B. reflexivity.
    + apply Bool.andb_false_r.
Qed.
Lemma llval_bit2 : forall v16 v4 i, Z.land (llval v16 v4 i * 4) 4 = Z.land (v16 * 4) 4.
Proof.
  intros v16 v4 i. rewrite !land4_mul4. unfold llval.
  rewrite Z.odd_add, Z.odd_mul. change (Z.odd 65536) with false. rewrite Bool.andb_false_r, Bool.xorb_false_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma shiftr_byte : forall v s, 0 <= v < 256 -> 0 <= s -> 0 <= Z.shiftr v s < 256.
Proof.
  intros v s Hv Hs. rewrite Z.shiftr_div_pow2 by lia.
  pose proof (Z.pow_pos_nonneg 2 s ltac:(lia) Hs) as P.
  split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. nia.
Qed.

(* [comment removed for export] *)
Lemma land4_cases : forall x, Z.land x 4 = 0 \/ Z.land x 4 = 4.
Proof.
  intros x. change 4 with (2 ^ 2). destruct (Z.testbit x 2) eqn:B.
  - right. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.pow2_bits_eqb by lia.
    destruct (Z.eqb_spec 2 n) as [<-|NE]; [rewrite B; reflexivity| apply Bool.andb_false_r].
  - left. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.pow2_bits_eqb, Z.bits_0 by lia.
    destruct (Z.eqb_spec 2 n) as [<-|NE]; [rewrite B; reflexivity| apply Bool.andb_false_r].
Qed.
Lemma ll4_shift_cases : forall i, Z.land (i * 4) 4 = 0 \/ Z.land (i * 4) 4 = 4.
Proof. intros i. apply land4_cases. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma iif_state_ext : forall (f g : Z -> Z) indx t, (t <= 8)%nat ->
  (forall i, 1 <= i <= 255 -> f i = g i) -> iif_state f indx t = iif_state g indx t.
Proof.
  intros f g indx t Ht E. induction t as [|t IH]; [reflexivity|].
  cbn [iif_state]. rewrite <- IH by lia.
  pose proof (iif_step_facts f indx t ltac:(lia)) as SF.
  destruct (iif_state f indx t) as [nb na]. cps_destruct SF as (A & B & C & D & E5 & _).
  rewrite (E (Z.shiftr (nb + na) 1)) by lia. reflexivity.
Qed.
Lemma index_into_f_ext : forall (f g : Z -> Z) indx,
  (forall i, 1 <= i <= 255 -> f i = g i) -> index_into_f indx f = index_into_f indx g.
Proof.
  intros f g indx E. rewrite (proj1 (index_into_f_spec indx f)), (proj1 (index_into_f_spec indx g)).
  rewrite (iif_state_ext f g indx 8) by (first [lia | exact E]). reflexivity.
Qed.
