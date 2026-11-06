(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module UbMhSzc.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition szc_x (n : Z) : Z := Z.shiftr (n + 3) 4.

(* [comment removed for export] *)
Definition szc_of_x (x : Z) : Z :=
  if x <? 10 then x else
  let t := Z.log2 (x + 1) in
  let i := 4 * t - 4 in
  let i2 := if x <? size_class (i + 1) then i else i + 2 in
  if x <? size_class i2 then i2 else i2 + 1.

Definition size_to_class (n : Z) : Z := szc_of_x (szc_x n).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint zrange (lo : Z) (k : nat) : list Z :=
  match k with O => [] | S k' => lo :: zrange (lo + 1) k' end.

Lemma zrange_in : forall k lo z, lo <= z < lo + Z.of_nat k -> In z (zrange lo k).
Proof.
  induction k as [|k IH]; intros lo z Hz; cbn; [lia|].
  destruct (Z.eq_dec lo z) as [->|Hne]; [left; reflexivity | right]. apply IH. lia.
Qed.

Lemma forallb_zrange : forall (f : Z -> bool) lo k,
  forallb f (zrange lo k) = true -> forall z, lo <= z < lo + Z.of_nat k -> f z = true.
Proof.
  intros f lo k H z Hz. apply (proj1 (forallb_forall _ _) H). apply zrange_in. exact Hz.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition XMAX : Z := 8190.      (* [comment removed for export] *)

Definition szc_ok_x (x : Z) : bool :=
  let c := szc_of_x x in (0 <=? c) && (c <? 48) && (x + 1 <=? size_class c).

Lemma szc_ok_all : forallb szc_ok_x (zrange 0 8191%nat) = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition szc_min_x (x : Z) : bool :=
  let c := szc_of_x x in (c =? 0) || (size_class (c - 1) <? x + 1).

Lemma szc_min_all : forallb szc_min_x (zrange 0 8191%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Definition sc_incr (c : Z) : bool := size_class c <? size_class (c + 1).
Lemma sc_incr_all : forallb sc_incr (zrange 0 47%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma size_class_mono : forall a b, 0 <= a -> a <= b -> b < 48 -> size_class a <= size_class b.
Proof.
  intros a b Ha Hab Hb.
  assert (STEP : forall c, 0 <= c < 47 -> size_class c < size_class (c + 1)).
  { intros c Hc. pose proof (forallb_zrange sc_incr 0 47%nat sc_incr_all c ltac:(cbn; lia)) as H.
    unfold sc_incr in H. apply Z.ltb_lt in H. exact H. }
  remember (Z.to_nat (b - a)) as d eqn:Hd. revert a b Ha Hab Hb Hd.
  induction d as [|d IH]; intros a b Ha Hab Hb Hd; [assert (a = b) by lia; subst; lia|].
  assert (size_class a <= size_class (b - 1)) by (apply (IH a (b - 1)); lia).
  pose proof (STEP (b - 1) ltac:(lia)). replace (b - 1 + 1) with b in * by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma szc_x_eq : forall n, 0 <= n -> szc_x n = (n + 3) / 16.
Proof. intros n Hn. unfold szc_x. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

Lemma szc_x_bounds : forall n, 0 <= n -> 16 * szc_x n <= n + 3 < 16 * szc_x n + 16.
Proof.
  intros n Hn. rewrite szc_x_eq by lia.
  pose proof (Z.div_mod (n + 3) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (n + 3) 16 ltac:(lia)). lia.
Qed.

Lemma szc_x_rng : forall n, 0 <= n < MMAP_THRESHOLD -> 0 <= szc_x n <= XMAX.
Proof.
  intros n Hn. unfold MMAP_THRESHOLD, XMAX in *. rewrite szc_x_eq by lia.
  split; [apply Z.div_pos; lia | enough ((n + 3) / 16 < 8191) by lia; apply Z.div_lt_upper_bound; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem size_to_class_rng : forall n, 0 <= n < MMAP_THRESHOLD -> 0 <= size_to_class n < 48.
Proof.
  intros n Hn. pose proof (szc_x_rng n Hn) as Hx. unfold XMAX in Hx.
  pose proof (forallb_zrange szc_ok_x 0 8191%nat szc_ok_all (szc_x n) ltac:(change (Z.of_nat 8191) with 8191%Z; lia)) as H.
  unfold szc_ok_x in H. apply andb_prop in H as [H _]. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.ltb_lt in H2. unfold size_to_class. lia.
Qed.

Theorem size_to_class_fits : forall n, 0 <= n < MMAP_THRESHOLD -> n + 4 <= 16 * size_class (size_to_class n).
Proof.
  intros n Hn. pose proof (szc_x_rng n Hn) as Hx. unfold XMAX in Hx. pose proof (szc_x_bounds n ltac:(lia)) as Hb.
  pose proof (forallb_zrange szc_ok_x 0 8191%nat szc_ok_all (szc_x n) ltac:(change (Z.of_nat 8191) with 8191%Z; lia)) as H.
  unfold szc_ok_x in H. apply andb_prop in H as [_ H]. apply Z.leb_le in H. unfold size_to_class. lia.
Qed.

Theorem size_to_class_min : forall n sc, 0 <= n < MMAP_THRESHOLD -> 0 <= sc < 48 ->
  n + 4 <= 16 * size_class sc -> size_to_class n <= sc.
Proof.
  intros n sc Hn Hsc Hfit. pose proof (szc_x_rng n Hn) as Hx. unfold XMAX in Hx. pose proof (szc_x_bounds n ltac:(lia)) as Hb.
  pose proof (size_to_class_rng n Hn) as Hc. unfold size_to_class in *.
  pose proof (forallb_zrange szc_min_x 0 8191%nat szc_min_all (szc_x n) ltac:(change (Z.of_nat 8191) with 8191%Z; lia)) as H.
  unfold szc_min_x in H. apply orb_prop in H as [H|H]; [apply Z.eqb_eq in H; lia|]. apply Z.ltb_lt in H.
  destruct (Z.lt_ge_cases sc (szc_of_x (szc_x n))) as [Hlt|Hge]; [|lia]. exfalso.
  pose proof (size_class_mono sc (szc_of_x (szc_x n) - 1) ltac:(lia) ltac:(lia) ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition szc_t (x : Z) : Z := Z.log2 (x + 1).

Lemma szc_t_rng : forall x, 10 <= x <= XMAX -> 3 <= szc_t x <= 12.
Proof.
  intros x Hx. unfold szc_t, XMAX in *.
  split.
  - replace 3 with (Z.log2 8) by reflexivity. apply Z.log2_le_mono. lia.
  - replace 12 with (Z.log2 8191) by reflexivity. apply Z.log2_le_mono. lia.
Qed.


(* [comment removed for export] *)
Lemma szc_of_x_ge10 : forall x, 10 <= x ->
  szc_of_x x = let i := 4 * szc_t x - 4 in
               let i2 := if x <? size_class (i + 1) then i else i + 2 in
               if x <? size_class i2 then i2 else i2 + 1.
Proof. intros x Hx. unfold szc_of_x, szc_t. replace (x <? 10) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. Qed.

Lemma szc_of_x_lt10 : forall x, 0 <= x < 10 -> szc_of_x x = x.
Proof. intros x Hx. unfold szc_of_x. replace (x <? 10) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. Qed.
End UbMhSzc.
Require LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType OSSVerify.glaze.binary_reflection.images.Ubsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module UbMhCtz.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.glaze.binary_reflection.images.Ubsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma neg_odd_lxor : forall m, Z.odd m = true -> - m = Z.lxor (Z.lnot m) 1.
Proof.
  intros m Hm. rewrite <- Z.add_nocarry_lxor.
  - unfold Z.lnot. lia.
  - apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.eq_dec n 0) as [->|NE].
    + rewrite Z.lnot_spec by lia. rewrite Z.bit0_odd, Hm. reflexivity.
    + rewrite (Z.testbit_0_l) || idtac. replace (Z.testbit 1 n) with false; [apply Bool.andb_false_r|].
      symmetry. change 1 with (2 ^ 0). rewrite Z.pow2_bits_eqb by lia. apply Z.eqb_neq. lia.
Qed.

Lemma lowbit_odd : forall m, Z.odd m = true -> Z.land m (- m) = 1.
Proof.
  intros m Hm. rewrite (neg_odd_lxor m Hm). apply Z.bits_inj'. intros n Hn.
  rewrite Z.land_spec, Z.lxor_spec, Z.lnot_spec by lia.
  destruct (Z.eq_dec n 0) as [->|NE].
  - rewrite Z.bit0_odd, Hm. cbn. reflexivity.
  - replace (Z.testbit 1 n) with false by (symmetry; change 1 with (2 ^ 0); rewrite Z.pow2_bits_eqb by lia; apply Z.eqb_neq; lia).
    rewrite Bool.xorb_false_r. destruct (Z.testbit m n); reflexivity.
Qed.

Lemma lowbit_even : forall h, Z.land (2 * h) (- (2 * h)) = 2 * Z.land h (- h).
Proof.
  intros h. replace (- (2 * h)) with (2 * (- h)) by lia.
  replace (2 * h) with (Z.shiftl h 1) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  replace (2 * - h) with (Z.shiftl (- h) 1) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  replace (2 * Z.land h (- h)) with (Z.shiftl (Z.land h (- h)) 1) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  symmetry. apply Z.shiftl_land.
Qed.

Lemma lowbit_pow2_n : forall n m, 0 < m < 2 ^ Z.of_nat n ->
  exists i, 0 <= i < Z.of_nat n /\ Z.land m (- m) = 2 ^ i /\ Z.testbit m i = true /\ (forall j, 0 <= j < i -> Z.testbit m j = false).
Proof.
  induction n as [|n IH]; intros m Hm.
  - cbn in Hm. lia.
  - destruct (Z.odd m) eqn:Ho.
    + exists 0. split; [lia|]. split; [apply lowbit_odd; exact Ho|]. split; [rewrite Z.bit0_odd; exact Ho|]. intros j Hj. lia.
    + assert (He : Z.even m = true) by (rewrite <- Z.negb_odd, Ho; reflexivity).
      apply Z.even_spec in He. destruct He as [h Eh].
      assert (Hh : 0 < h < 2 ^ Z.of_nat n) by (rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hm by lia; lia).
      destruct (IH h Hh) as (i & Hi & L & T & F). exists (i + 1). rewrite Eh.
      split; [rewrite Nat2Z.inj_succ; lia|]. split; [rewrite lowbit_even, L, Z.pow_add_r by lia; change (2 ^ 1) with 2; lia|].
      split; [replace (i + 1) with (Z.succ i) by lia; rewrite Z.testbit_even_succ by lia; exact T|].
      intros j Hj. destruct (Z.eq_dec j 0) as [->|NE]; [apply Z.testbit_even_0|].
      replace j with (Z.succ (j - 1)) by lia. rewrite Z.testbit_even_succ by lia. apply F. lia.
Qed.

Lemma lowbit_pow2 : forall m, 0 < m < 2 ^ 32 ->
  exists i, 0 <= i < 32 /\ Z.land m (- m) = 2 ^ i /\ Z.testbit m i = true /\ (forall j, 0 <= j < i -> Z.testbit m j = false).
Proof. intros m Hm. exact (lowbit_pow2_n 32 m Hm). Qed.

Lemma pow2_sub_clear : forall m i, 0 <= m -> 0 <= i -> Z.testbit m i = true ->
  0 <= m - 2 ^ i /\ (forall k, 0 <= k -> Z.testbit (m - 2 ^ i) k = if k =? i then false else Z.testbit m k).
Proof.
  intros m i Hm Hi T.
  assert (E : m - 2 ^ i = Z.ldiff m (2 ^ i)).
  { pose proof (Z.add_nocarry_lxor (Z.ldiff m (2 ^ i)) (2 ^ i)) as A.
    assert (L0 : Z.land (Z.ldiff m (2 ^ i)) (2 ^ i) = 0).
    { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.ldiff_spec, Z.bits_0, Z.pow2_bits_eqb by lia.
      destruct (Z.eqb_spec i n); cbn; [rewrite Bool.andb_false_r; reflexivity | rewrite Bool.andb_false_r; reflexivity]. }
    specialize (A L0).
    assert (X : Z.lxor (Z.ldiff m (2 ^ i)) (2 ^ i) = m).
    { apply Z.bits_inj'. intros n Hn. rewrite Z.lxor_spec, Z.ldiff_spec, Z.pow2_bits_eqb by lia.
      destruct (Z.eqb_spec i n) as [<-|NE]; [rewrite T; reflexivity | cbn; rewrite Bool.andb_true_r, Bool.xorb_false_r; reflexivity]. }
    lia. }
  split.
  - rewrite E. apply Z.ldiff_nonneg. left. exact Hm.
  - intros k Hk. rewrite E, Z.ldiff_spec, Z.pow2_bits_eqb by lia.
    destruct (Z.eqb_spec k i) as [->|NE]; [rewrite Z.eqb_refl; cbn; apply Bool.andb_false_r|].
    rewrite (proj2 (Z.eqb_neq i k) ltac:(lia)). cbn. apply Bool.andb_true_r.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition CTZC : Z := 0x77cb531.
Definition ctzix (i : Z) : Z := Z.shiftr ((2 ^ i * CTZC) mod 2 ^ 32) 27.

Section WithFP.
  Context {RN : mh_run}.
  Context {fx : FPState}.

  Lemma ctzix_rng : forall i, 0 <= i < 32 -> 0 <= ctzix i < 32.
  Proof.
    intros i Hi. unfold ctzix. rewrite Z.shiftr_div_pow2 by lia.
    pose proof (Z.mod_pos_bound (2 ^ i * CTZC) (2 ^ 32) ltac:(lia)) as B.
    rewrite pow2_32 in B |- *. replace (2 ^ 27) with 134217728 by reflexivity.
    split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma ctz_srliw : forall i, 0 <= i < 32 ->
    v_srliw (v_mul (s32 (2 ^ i)) (Z_to_bv 64 CTZC)) 27 = Z_to_bv 64 (ctzix i).
  Proof.
    intros i Hi.
    assert (E : exists k, (k < 32)%nat /\ i = Z.of_nat k) by (exists (Z.to_nat i); split; [lia | lia]).
    destruct E as (k & Hk & ->).
    enum_nat k 32%nat ltac:(vm_compute; reflexivity).
  Qed.

  (* [comment removed for export] *)
  Lemma ctz_tab_none : forall k, (k < 32)%nat ->
    rdn RSEGS (fun _ => None) (Z_to_bv 64 (A_TAB_CTZ + ctzix (Z.of_nat k))) 1%nat = Some [Z_to_bv 8 (Z.of_nat k)].
  Proof.
    intros k Hk. enum_nat k 32%nat ltac:(vm_compute; reflexivity).
  Qed.

  Lemma ctz_tab_read : forall mem i, img_clear mem A_TAB_CTZ (A_TAB_CTZ + 32) -> 0 <= i < 32 ->
    rdn RSEGS mem (Z_to_bv 64 (A_TAB_CTZ + ctzix i)) 1%nat = Some [Z_to_bv 8 i].
  Proof.
    intros mem i Himg Hi. pose proof (ctzix_rng i Hi).
    rewrite (rdn_img RSEGS mem _ 1 A_TAB_CTZ (A_TAB_CTZ + 32) Himg) by (unfold A_TAB_CTZ; cbn; lia).
    pose proof (ctz_tab_none (Z.to_nat i) ltac:(lia)) as R. rewrite Z2Nat.id in R by lia. exact R.
  Qed.
End WithFP.
End UbMhCtz.
Require LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhEnframeBase OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFreeA OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM1 OSSVerify.Proofs.glaze.binary_reflection.lib.PuStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module UbMhASlotW1.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.Ubsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhEnframeBase OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFreeA.UbMhGetMeta OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac.UbMhBits OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac UbMhCtz OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM1.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.PuStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac is_Z_lit ::= ps_is_Z_lit.   (* [comment removed for export] *)
#[local] Ltac check_closed_term_fast ::= ps_check_closed.
#[local] Ltac gres ::= pu_gres.
#[local] Ltac chain_step ::= pu_chain_step.   (* [comment removed for export] *)
#[local] Ltac vnorm ::= pu_vnorm.
#[local] Ltac step_simpl ::= pu_step_simpl.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok B SOK := store_ok_peel; eapply (store_ok_sub _ _ _ _ B); [ | exact SOK | | ]; zsimp; lia.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Pro.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (m : mem) (sp sc req can : Z).
  Hypothesis Hsp : (CEIL + 144 <= sp)%Z /\ (sp < 2^64)%Z.
  Hypothesis Hsc : (0 <= sc < 48)%Z.
  Hypothesis Hreq : (0 <= req < 2^64)%Z.
  Hypothesis Hcan : (0 <= can < 2^64)%Z.
  Hypothesis SOK : store_ok RSEGS m (Z_to_bv 64 (sp - 144)) 144%nat = true.
  Hypothesis M_got : rdn RSEGS m (Z_to_bv 64 A_GOT_CANARY) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 A_CANARY)).
  Hypothesis M_can : rdn RSEGS m (Z_to_bv 64 A_CANARY) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 can)).

  Definition as_frame (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : word) : mem :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
      (Z_to_bv 64 (sp - 8)) (word_to_le_bytes 8 ra))
      (Z_to_bv 64 (sp - 16)) (word_to_le_bytes 8 s0))
      (Z_to_bv 64 (sp - 24)) (word_to_le_bytes 8 s1))
      (Z_to_bv 64 (sp - 32)) (word_to_le_bytes 8 s2))
      (Z_to_bv 64 (sp - 40)) (word_to_le_bytes 8 s3))
      (Z_to_bv 64 (sp - 48)) (word_to_le_bytes 8 s4))
      (Z_to_bv 64 (sp - 56)) (word_to_le_bytes 8 s5))
      (Z_to_bv 64 (sp - 64)) (word_to_le_bytes 8 s6))
      (Z_to_bv 64 (sp - 72)) (word_to_le_bytes 8 s7))
      (Z_to_bv 64 (sp - 80)) (word_to_le_bytes 8 s8))
      (Z_to_bv 64 (sp - 88)) (word_to_le_bytes 8 s9))
      (Z_to_bv 64 (sp - 96)) (word_to_le_bytes 8 (Z_to_bv 64 can)).

  Definition clobPro : list reg := [2; 8; 10; 11; 18; 20; 22; 23]%bv.

  Lemma aPro : forall regs rom,
    getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 sc -> getr regs 11 = Z_to_bv 64 req ->
    exists regs',
      msteps RSEGS (mkst regs (0x672b0 : word) m rom)
                   (mkst regs' (0x67308 : word)
                      (as_frame (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20)
                                (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25)) rom)
      /\ getr regs' 2 = Z_to_bv 64 (sp - 144) /\ getr regs' 8 = Z_to_bv 64 sc /\ getr regs' 18 = Z_to_bv 64 req
      /\ getr regs' 20 = Z_to_bv 64 A_CANARY /\ getr regs' 10 = Z_to_bv 64 can
      /\ getr regs' 22 = Z_to_bv 64 MLOCK /\ getr regs' 23 = Z_to_bv 64 (MLOCK + 8 * sc)
      /\ keeps_but clobPro regs regs'.
  Proof using M_can M_got SOK Hsc Hsp RN.
    intros regs rom H2 H10 H11. ceil; unfold A_GOT_CANARY, A_CANARY, MLOCK in *. unfold as_frame.
    eexists. split.
    - stepn F_6725c D_6725c. rewrite H2. addi_renorm.
      stepSTx F_67260 D_67260 (Z_to_bv 64 (sp - 8)) (getr regs 1) ltac:(sok 144%nat SOK).
      stepSTx F_67264 D_67264 (Z_to_bv 64 (sp - 16)) (getr regs 8) ltac:(sok 144%nat SOK).
      stepSTx F_67268 D_67268 (Z_to_bv 64 (sp - 24)) (getr regs 9) ltac:(sok 144%nat SOK).
      stepSTx F_6726c D_6726c (Z_to_bv 64 (sp - 32)) (getr regs 18) ltac:(sok 144%nat SOK).
      stepSTx F_67270 D_67270 (Z_to_bv 64 (sp - 40)) (getr regs 19) ltac:(sok 144%nat SOK).
      stepSTx F_67274 D_67274 (Z_to_bv 64 (sp - 48)) (getr regs 20) ltac:(sok 144%nat SOK).
      stepSTx F_67278 D_67278 (Z_to_bv 64 (sp - 56)) (getr regs 21) ltac:(sok 144%nat SOK).
      stepSTx F_6727c D_6727c (Z_to_bv 64 (sp - 64)) (getr regs 22) ltac:(sok 144%nat SOK).
      stepSTx F_67280 D_67280 (Z_to_bv 64 (sp - 72)) (getr regs 23) ltac:(sok 144%nat SOK).
      stepSTx F_67284 D_67284 (Z_to_bv 64 (sp - 80)) (getr regs 24) ltac:(sok 144%nat SOK).
      stepSTx F_67288 D_67288 (Z_to_bv 64 (sp - 88)) (getr regs 25) ltac:(sok 144%nat SOK).
      stepn F_6728c D_6728c. rewrite H11.
      stepn F_67290 D_67290. rewrite H10.
      stepn F_67294 D_67294.
      stepLD8 F_67298 D_67298 (Z_to_bv 64 699904).
      stepLD8 F_6729c D_6729c (Z_to_bv 64 can).
      stepn F_672a0 D_672a0. 
      stepn F_672a4 D_672a4.
      stepn F_672a8 D_672a8. vals_lit.
      stepSTx F_672ac D_672ac (Z_to_bv 64 (sp - 96)) (Z_to_bv 64 can) ltac:(sok 144%nat SOK).
      stepn F_672b0 D_672b0.
      pu_refl.
    - repeat split; gres; try reflexivity; try assumption; try (apply bv_eq; reflexivity).
      + unfold v_slli, v_add. apply bv_eq. u_norm. rewrite Z.shiftl_mul_pow2 by lia. unorm. change (2 ^ 3)%Z with 8%Z. lia.
      + solve_keeps_but.
  Qed.
End Pro.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section S32.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Lemma v_subw_s32 : forall a b, v_subw (s32 a) (s32 b) = s32 (a - b)%Z.
  Proof using.
    intros a b. unfold v_subw. fold (s32 (bv_unsigned (s32 a) - bv_unsigned (s32 b))).
    apply s32_eq_iff. rewrite !u_s32. rewrite Zminus_mod, !sx32_mod, <- Zminus_mod by lia. reflexivity.
  Qed.
  Lemma zero_s32 : Z_to_bv 64 0 = s32 0. Proof using. symmetry. apply s32_small. lia. Qed.
  Lemma s32_pow2_ne0 : forall i, (0 <= i < 32)%Z -> c_eq (s32 (2 ^ i)) (Z_to_bv 64 0) = false.
  Proof using.
    intros i Hi. rewrite zero_s32, c_eq_s32. apply Z.eqb_neq.
    assert (0 < 2 ^ i /\ 2 ^ i < 2 ^ 32)%Z by (split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_lt_mono_r; lia]).
    rewrite Z.mod_small, Z.mod_0_l by lia. lia.
  Qed.
End S32.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Head.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (m : mem) (sc hd : Z).
  Hypothesis Hsc : (0 <= sc < 48)%Z.
  Hypothesis Hhd : (0 <= hd < 2^64)%Z.
  Hypothesis M_act : rdn RSEGS m (Z_to_bv 64 (ctx_active sc)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 hd)).

  Lemma aHead0 : forall regs rom,
    getr regs 23 = Z_to_bv 64 (MLOCK + 8 * sc) -> hd = 0%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x67308 : word) m rom) (mkst regs' (0x67490 : word) m rom)
      /\ getr regs' 21 = Z_to_bv 64 (ctx_active sc) /\ getr regs' 12 = Z_to_bv 64 0
      /\ keeps_but [12; 21]%bv regs regs'.
  Proof using M_act Hhd Hsc.
    intros regs rom H23 Hz. unfold ctx_active, CTX, MLOCK in *. subst hd.
    eexists. split.
    - stepLD F_672b4 D_672b4 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0)
        ltac:(unfold v_addi; unorm; replace (700048 + 8 * sc + 88)%Z with (700056 + 80 + 8 * sc)%Z by lia; exact M_act)
        ltac:(apply bytes_le_to_Z_8).
      stepn F_672b8 D_672b8. rewrite H23.
      stepb_tk F_672bc D_672bc ltac:(apply c_eq_refl).
      pu_refl.
    - repeat split; gres; try reflexivity; [unfold v_addi; apply bv_eq; unorm; lia | solve_keeps_but].
  Qed.

  Lemma aHead1 : forall regs rom,
    getr regs 23 = Z_to_bv 64 (MLOCK + 8 * sc) -> hd <> 0%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x67308 : word) m rom) (mkst regs' (0x67314 : word) m rom)
      /\ getr regs' 21 = Z_to_bv 64 (ctx_active sc) /\ getr regs' 12 = Z_to_bv 64 hd
      /\ keeps_but [12; 21]%bv regs regs'.
  Proof using M_act Hhd Hsc.
    intros regs rom H23 Hnz. unfold ctx_active, CTX, MLOCK in *.
    eexists. split.
    - stepLD F_672b4 D_672b4 (word_to_le_bytes 8 (Z_to_bv 64 hd)) (Z_to_bv 64 hd)
        ltac:(unfold v_addi; unorm; replace (700048 + 8 * sc + 88)%Z with (700056 + 80 + 8 * sc)%Z by lia; exact M_act)
        ltac:(apply bytes_le_to_Z_8).
      stepn F_672b8 D_672b8. rewrite H23.
      stepb_ft F_672bc D_672bc ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; exact Hnz).
      pu_refl.
    - repeat split; gres; try reflexivity; [unfold v_addi; apply bv_eq; unorm; lia | solve_keeps_but].
  Qed.
End Head.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Avail.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (m : mem) (hd avail : Z).
  Hypothesis Hhd : (HEAPLO <= hd)%Z /\ (hd + 40 <= CEIL)%Z /\ ((hd + 40 <= IMG_LO)%Z \/ (IMG_HI <= hd)%Z).
  Hypothesis Hav : (0 <= avail < 2^32)%Z.
  Hypothesis M_av : rdn RSEGS m (Z_to_bv 64 (hd + 24)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 avail)).

  Lemma aAvailT : forall regs rom,
    getr regs 12 = Z_to_bv 64 hd -> (avail <> 0)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x67314 : word) m rom) (mkst regs' (0x67450 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 hd /\ getr regs' 11 = s32 avail
      /\ keeps_but [10; 11]%bv regs regs'.
  Proof using M_av Hav Hhd RN.
    intros regs rom H12 Hnz. ceil; unfold HEAPLO in *.
    eexists. split.
    - stepLD F_672c0 D_672c0 (word_to_le_bytes 4 (Z_to_bv 64 avail)) (Z_to_bv 64 avail)
        ltac:(addr_norm; exact M_av) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      rewrite v_lw_s32 by lia.
      stepb_ft F_672c4 D_672c4 ltac:(rewrite zero_s32, c_eq_s32; rewrite Z.mod_0_l, Z.mod_small by lia; apply Z.eqb_neq; exact Hnz).
      stepn F_672c8 D_672c8. rewrite H12.
      stepn F_672cc D_672cc.
      pu_refl.
    - repeat split; gres; try reflexivity. solve_keeps_but.
  Qed.

  Lemma aAvail0 : forall regs rom,
    getr regs 12 = Z_to_bv 64 hd -> (avail = 0)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x67314 : word) m rom) (mkst regs' (0x67324 : word) m rom)
      /\ getr regs' 11 = Z_to_bv 64 0
      /\ keeps_but [11]%bv regs regs'.
  Proof using M_av Hav Hhd RN.
    intros regs rom H12 Hz. ceil; unfold HEAPLO in *. subst avail.
    eexists. split.
    - stepLD F_672c0 D_672c0 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
        ltac:(addr_norm; exact M_av) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepb_tk F_672c4 D_672c4 ltac:(apply c_eq_refl).
      pu_refl.
    - repeat split; gres; try reflexivity. solve_keeps_but.
  Qed.
End Avail.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Take.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (m : mem) (g mask i : Z).
  Hypothesis Hg : (HEAPLO <= g)%Z /\ (g + 40 <= CEIL)%Z /\ ((g + 40 <= IMG_LO)%Z \/ (IMG_HI <= g)%Z).
  Hypothesis Hmask : (0 <= mask < 2^32)%Z.
  Hypothesis Hi : (0 <= i < 32)%Z.
  Hypothesis Hlow : Z.land mask (- mask) = (2 ^ i)%Z.
  Hypothesis Hbit : Z.testbit mask i = true.
  Hypothesis SOK : store_ok RSEGS m (Z_to_bv 64 (g + 24)) 4%nat = true.
  Hypothesis M_ctz : img_clear m A_TAB_CTZ (A_TAB_CTZ + 32).

  Definition m_take : mem := wbytes m (Z_to_bv 64 (g + 24)) (word_to_le_bytes 4 (Z_to_bv 64 (mask - 2 ^ i))).

  Lemma pow2_i_rng : (0 < 2 ^ i /\ 2 ^ i < 2 ^ 32)%Z.
  Proof using Hi. split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_lt_mono_r; lia]. Qed.
  Lemma mask_ge : (2 ^ i <= mask)%Z.
  Proof using Hbit Hi Hmask.
    pose proof (pow2_sub_clear mask i ltac:(lia) ltac:(lia) Hbit) as [A _]. lia.
  Qed.

  Lemma aTake : forall regs rom,
    getr regs 10 = Z_to_bv 64 g -> getr regs 11 = s32 mask ->
    exists regs',
      msteps RSEGS (mkst regs (0x67450 : word) m rom) (mkst regs' (0x67b10 : word) m_take rom)
      /\ getr regs' 10 = Z_to_bv 64 i
      /\ keeps_but [10; 11; 12; 13]%bv regs regs'.
  Proof using M_ctz SOK Hbit Hlow Hi Hmask Hg RN.
    intros regs rom H10 H11. ceil; unfold HEAPLO, A_TAB_CTZ in *. unfold m_take.
    pose proof pow2_i_rng as [P1 P2]. pose proof mask_ge as MG. change (2^32)%Z with 4294967296%Z in P2.
    eexists. split.
    - stepn F_673fc D_673fc. rewrite H11, zero_s32, v_subw_s32. replace (0 - mask)%Z with (- mask)%Z by lia.
      stepn F_67400 D_67400. rewrite H11, v_and_s32, Hlow.
      stepn F_67404 D_67404. rewrite H11, v_subw_s32.
      stepSTx F_67408 D_67408 (Z_to_bv 64 (g + 24)) (s32 (mask - 2 ^ i)) ltac:(store_ok_peel; exact SOK).
      rewrite w2le4_s32, (Z.mod_small (mask - 2 ^ i)) by lia.
      stepb_ft F_6740c D_6740c ltac:(apply s32_pow2_ne0; exact Hi).
      stepn F_67410 D_67410. rewrite H11. rewrite zero_s32. rewrite v_subw_s32. replace (0 - mask)%Z with (- mask)%Z by lia.
      stepn F_67414 D_67414. rewrite H11. rewrite v_and_s32. rewrite Hlow.
      stepn F_67418 D_67418.
      stepn F_6741c D_6741c. vals_lit.
      stepn F_67420 D_67420.
      stepn F_67424 D_67424.
      stepn F_67428 D_67428. pose proof (ctz_srliw i Hi) as CZ. unfold CTZC in CZ. rewrite CZ. clear CZ.
      stepn F_6742c D_6742c. vals_lit.
      stepn F_67430 D_67430. rewrite (v_add_ZZ 145740 (ctzix i)) by (pose proof (ctzix_rng i Hi); lia).
      pose proof (ctz_tab_read m i M_ctz Hi) as TB. unfold A_TAB_CTZ in TB. pose proof (ctzix_rng i Hi) as CR.
      stepLBU F_67434 D_67434 (Z_to_bv 8 i) ltac:(addr_norm; replace (145740 + ctzix i + 0)%Z with (145740 + ctzix i)%Z by lia; rdn_by TB).
      stepn F_67438 D_67438.
      pu_refl.
    - repeat split; gres; try reflexivity.
      + apply bv_eq. rewrite (UbMhFreeA.UbMhGetMeta.u8_Z2bv i) by lia. unorm. reflexivity.
      + solve_keeps_but.
  Qed.
End Take.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Epi.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (m : mem) (sp can : Z) (ra s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v : word).
  Hypothesis Hsp : (CEIL + 144 <= sp)%Z /\ (sp < 2^64)%Z.
  Hypothesis Hcan : (0 <= can < 2^64)%Z.
  Hypothesis Hra : ret_ok ra.
  Hypothesis M_can : rdn RSEGS m (Z_to_bv 64 A_CANARY) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 can)).
  Hypothesis M_c96 : rdn RSEGS m (Z_to_bv 64 (sp - 96)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 can)).
  Hypothesis M_ra : rdn RSEGS m (Z_to_bv 64 (sp - 8)) 8%nat = Some (word_to_le_bytes 8 ra).
  Hypothesis M_s0 : rdn RSEGS m (Z_to_bv 64 (sp - 16)) 8%nat = Some (word_to_le_bytes 8 s0v).
  Hypothesis M_s1 : rdn RSEGS m (Z_to_bv 64 (sp - 24)) 8%nat = Some (word_to_le_bytes 8 s1v).
  Hypothesis M_s2 : rdn RSEGS m (Z_to_bv 64 (sp - 32)) 8%nat = Some (word_to_le_bytes 8 s2v).
  Hypothesis M_s3 : rdn RSEGS m (Z_to_bv 64 (sp - 40)) 8%nat = Some (word_to_le_bytes 8 s3v).
  Hypothesis M_s4 : rdn RSEGS m (Z_to_bv 64 (sp - 48)) 8%nat = Some (word_to_le_bytes 8 s4v).
  Hypothesis M_s5 : rdn RSEGS m (Z_to_bv 64 (sp - 56)) 8%nat = Some (word_to_le_bytes 8 s5v).
  Hypothesis M_s6 : rdn RSEGS m (Z_to_bv 64 (sp - 64)) 8%nat = Some (word_to_le_bytes 8 s6v).
  Hypothesis M_s7 : rdn RSEGS m (Z_to_bv 64 (sp - 72)) 8%nat = Some (word_to_le_bytes 8 s7v).
  Hypothesis M_s8 : rdn RSEGS m (Z_to_bv 64 (sp - 80)) 8%nat = Some (word_to_le_bytes 8 s8v).
  Hypothesis M_s9 : rdn RSEGS m (Z_to_bv 64 (sp - 88)) 8%nat = Some (word_to_le_bytes 8 s9v).

  Definition clobEpi : list reg := [1; 2; 8; 9; 11; 12; 18; 19; 20; 21; 22; 23; 24; 25]%bv.

  Lemma aEpi : forall regs rom,
    getr regs 2 = Z_to_bv 64 (sp - 144) -> getr regs 20 = Z_to_bv 64 A_CANARY ->
    exists regs',
      msteps RSEGS (mkst regs (0x67b10 : word) m rom) (mkst regs' ra m rom)
      /\ getr regs' 2 = Z_to_bv 64 sp /\ getr regs' 10 = getr regs 10 /\ getr regs' 1 = ra
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v /\ getr regs' 20 = s4v
      /\ getr regs' 21 = s5v /\ getr regs' 22 = s6v /\ getr regs' 23 = s7v /\ getr regs' 24 = s8v /\ getr regs' 25 = s9v
      /\ keeps_but clobEpi regs regs'.
  Proof using M_s9 M_s8 M_s7 M_s6 M_s5 M_s4 M_s3 M_s2 M_s1 M_s0 M_ra M_c96 M_can Hra Hsp can RN.
    intros regs rom H2 H20. ceil; unfold A_CANARY in *.
    eexists. split.
    - stepLD8 F_67abc D_67abc (Z_to_bv 64 can).
      stepLD8 F_67ac0 D_67ac0 (Z_to_bv 64 can).
      stepb_ft F_67ac4 D_67ac4 ltac:(apply c_eq_refl || (rewrite c_eq_Z by lia; apply Z.eqb_refl)).
      stepLD8 F_67ac8 D_67ac8 ra.
      stepLD8 F_67acc D_67acc s0v.
      stepLD8 F_67ad0 D_67ad0 s1v.
      stepLD8 F_67ad4 D_67ad4 s2v.
      stepLD8 F_67ad8 D_67ad8 s3v.
      stepLD8 F_67adc D_67adc s4v.
      stepLD8 F_67ae0 D_67ae0 s5v.
      stepLD8 F_67ae4 D_67ae4 s6v.
      stepLD8 F_67ae8 D_67ae8 s7v.
      stepLD8 F_67aec D_67aec s8v.
      stepLD8 F_67af0 D_67af0 s9v.
      stepn F_67af4 D_67af4. rewrite H2. addi_renorm.
      stepret F_67af8 D_67af8 ra ltac:(reflexivity).
      pu_refl.
    - repeat split; gres; try reflexivity; try assumption. all: try (f_equal; lia). all: solve_keeps_but.
  Qed.
End Epi.
End UbMhASlotW1.
Module UbMhASlotW2.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.Ubsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac.LibAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhEnframeBase OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFreeA.UbMhGetMeta OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac.UbMhBits OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac UbMhCtz UbMhASlotW1 OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM1.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.PuStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac is_Z_lit ::= ps_is_Z_lit.   (* [comment removed for export] *)
#[local] Ltac check_closed_term_fast ::= ps_check_closed.
#[local] Ltac gres ::= pu_gres.
#[local] Ltac chain_step ::= pu_chain_step.   (* [comment removed for export] *)
#[local] Ltac vnorm ::= pu_vnorm.
#[local] Ltac step_simpl ::= pu_step_simpl.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok B SOK := store_ok_peel; eapply (store_ok_sub _ _ _ _ B); [ | exact SOK | | ]; zsimp; lia.
Ltac post := repeat split; gres; try reflexivity; try assumption; try solve_keeps_but.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Rot.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (m : mem) (sc hd fr nx : Z).
  Hypothesis Hsc : (0 <= sc < 48)%Z.
  Hypothesis Hhd : (HEAPLO <= hd)%Z /\ (hd + 40 <= CEIL)%Z /\ ((hd + 40 <= IMG_LO)%Z \/ (IMG_HI <= hd)%Z).
  Hypothesis Hfr : (0 <= fr < 2^32)%Z.
  Hypothesis Hnx : (0 <= nx < 2^64)%Z.
  Hypothesis M_fr : rdn RSEGS m (Z_to_bv 64 (hd + 28)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 fr)).
  Hypothesis M_nx : rdn RSEGS m (Z_to_bv 64 (hd + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 nx)).
  Hypothesis SOKa : store_ok RSEGS m (Z_to_bv 64 (ctx_active sc)) 8%nat = true.

  Definition m_rot : mem := wbytes m (Z_to_bv 64 (ctx_active sc)) (word_to_le_bytes 8 (Z_to_bv 64 nx)).

  Lemma aRot : forall regs rom,
    getr regs 12 = Z_to_bv 64 hd -> getr regs 21 = Z_to_bv 64 (ctx_active sc) -> fr <> 0%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x67324 : word) m rom) (mkst regs' (0x67378 : word) m_rot rom)
      /\ getr regs' 10 = Z_to_bv 64 nx /\ getr regs' 11 = s32 fr
      /\ keeps_but [10; 11]%bv regs regs'.
  Proof using SOKa M_nx M_fr Hfr Hhd Hsc RN.
    intros regs rom H12 H21 Hnz. ceil; unfold HEAPLO, ctx_active, CTX in *. unfold m_rot.
    eexists. split.
    - stepLD F_672d0 D_672d0 (word_to_le_bytes 4 (Z_to_bv 64 fr)) (Z_to_bv 64 fr)
        ltac:(addr_norm; exact M_fr) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      rewrite v_lw_s32 by lia.
      stepLD8 F_672d4 D_672d4 (Z_to_bv 64 nx).
      stepb_ft F_672d8 D_672d8 ltac:(rewrite zero_s32, c_eq_s32; rewrite Z.mod_0_l, Z.mod_small by lia; apply Z.eqb_neq; exact Hnz).
      stepSTx F_672dc D_672dc (Z_to_bv 64 (700056 + 80 + 8 * sc)) (Z_to_bv 64 nx) ltac:(store_ok_peel; exact SOKa).
      stepn F_672e0 D_672e0.
      pu_refl.
    - post.
  Qed.
End Rot.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Deq.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (m : mem) (sc hd nx pv : Z).
  Hypothesis Hsc : (0 <= sc < 48)%Z.
  Hypothesis Hhd : (HEAPLO <= hd)%Z /\ (hd + 40 <= CEIL)%Z /\ ((hd + 40 <= IMG_LO)%Z \/ (IMG_HI <= hd)%Z).
  Hypothesis Hnx : (HEAPLO <= nx)%Z /\ (nx + 40 <= CEIL)%Z /\ ((nx + 40 <= IMG_LO)%Z \/ (IMG_HI <= nx)%Z).
  Hypothesis Hpv : (HEAPLO <= pv)%Z /\ (pv + 40 <= CEIL)%Z /\ ((pv + 40 <= IMG_LO)%Z \/ (IMG_HI <= pv)%Z).
  Hypothesis M_fr : rdn RSEGS m (Z_to_bv 64 (hd + 28)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)).
  Hypothesis M_nx : rdn RSEGS m (Z_to_bv 64 (hd + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 nx)).
  Hypothesis M_pv : rdn RSEGS m (Z_to_bv 64 hd) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 pv)).
  Hypothesis M_act : rdn RSEGS m (Z_to_bv 64 (ctx_active sc)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 hd)).
  Hypothesis SOKa : store_ok RSEGS m (Z_to_bv 64 (ctx_active sc)) 8%nat = true.
  Hypothesis SOKh : store_ok RSEGS m (Z_to_bv 64 hd) 16%nat = true.

  (* [comment removed for export] *)
  Definition m_deqS : mem :=
    wbytes (wbytes (wbytes m
      (Z_to_bv 64 (ctx_active sc)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 hd) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (hd + 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)).

  Lemma aDeqS : forall regs rom,
    getr regs 12 = Z_to_bv 64 hd -> getr regs 21 = Z_to_bv 64 (ctx_active sc) -> nx = hd ->
    exists regs',
      msteps RSEGS (mkst regs (0x67324 : word) m rom) (mkst regs' (0x67490 : word) m_deqS rom)
      /\ getr regs' 10 = Z_to_bv 64 0
      /\ keeps_but [10; 11]%bv regs regs'.
  Proof using SOKh SOKa M_nx M_fr Hnx Hhd Hsc RN.
    intros regs rom H12 H21 Hs. ceil; unfold HEAPLO, ctx_active, CTX in *. unfold m_deqS. subst nx.
    eexists. split.
    - stepLD F_672d0 D_672d0 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
        ltac:(addr_norm; exact M_fr) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepLD8 F_672d4 D_672d4 (Z_to_bv 64 hd).
      stepb_tk F_672d8 D_672d8 ltac:(apply c_eq_refl).
      stepb_tk F_672e4 D_672e4 ltac:(rewrite H12; apply c_eq_refl).
      stepn F_6730c D_6730c.
      stepSTx F_67310 D_67310 (Z_to_bv 64 (700056 + 80 + 8 * sc)) (Z_to_bv 64 0) ltac:(store_ok_peel; exact SOKa).
      stepSTx F_67314 D_67314 (Z_to_bv 64 hd) (Z_to_bv 64 0) ltac:(sok 16%nat SOKh).
      stepSTx F_67318 D_67318 (Z_to_bv 64 (hd + 8)) (Z_to_bv 64 0) ltac:(sok 16%nat SOKh).
      stepLD8 F_6731c D_6731c (Z_to_bv 64 0).
      stepb_tk F_67320 D_67320 ltac:(apply c_eq_refl).
      pu_refl.
    - post.
  Qed.

  Hypothesis SOKp : store_ok RSEGS m (Z_to_bv 64 (pv + 8)) 8%nat = true.
  Hypothesis SOKn : store_ok RSEGS m (Z_to_bv 64 nx) 8%nat = true.

  (* [comment removed for export] *)
  Definition m_deqN : mem :=
    wbytes (wbytes (wbytes (wbytes (wbytes m
      (Z_to_bv 64 (pv + 8)) (word_to_le_bytes 8 (Z_to_bv 64 nx)))
      (Z_to_bv 64 nx) (word_to_le_bytes 8 (Z_to_bv 64 pv)))
      (Z_to_bv 64 (ctx_active sc)) (word_to_le_bytes 8 (Z_to_bv 64 nx)))
      (Z_to_bv 64 hd) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (hd + 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)).

  Lemma aDeqN : forall regs rom,
    getr regs 12 = Z_to_bv 64 hd -> getr regs 21 = Z_to_bv 64 (ctx_active sc) -> nx <> hd ->
    (pv + 40 <= hd \/ hd + 40 <= pv)%Z -> (nx + 40 <= hd \/ hd + 40 <= nx)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x67324 : word) m rom) (mkst regs' (0x67378 : word) m_deqN rom)
      /\ getr regs' 10 = Z_to_bv 64 nx
      /\ keeps_but [10; 11]%bv regs regs'.
  Proof using SOKn SOKp SOKh SOKa M_act M_pv M_nx M_fr Hpv Hnx Hhd Hsc RN.
    intros regs rom H12 H21 Hne Dp Dn. ceil; unfold HEAPLO, ctx_active, CTX in *. unfold m_deqN.
    eexists. split.
    - stepLD F_672d0 D_672d0 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
        ltac:(addr_norm; exact M_fr) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepLD8 F_672d4 D_672d4 (Z_to_bv 64 nx).
      stepb_tk F_672d8 D_672d8 ltac:(apply c_eq_refl).
      stepb_ft F_672e4 D_672e4 ltac:(rewrite H12, c_eq_Z by lia; apply Z.eqb_neq; exact Hne).
      stepLD8 F_672e8 D_672e8 (Z_to_bv 64 pv).
      stepSTx F_672ec D_672ec (Z_to_bv 64 (pv + 8)) (Z_to_bv 64 nx) ltac:(store_ok_peel; exact SOKp).
      stepLD8 F_672f0 D_672f0 (Z_to_bv 64 pv).
      stepLD8 F_672f4 D_672f4 (Z_to_bv 64 nx).
      stepSTx F_672f8 D_672f8 (Z_to_bv 64 nx) (Z_to_bv 64 pv) ltac:(store_ok_peel; exact SOKn).
      stepLD8 F_672fc D_672fc (Z_to_bv 64 hd).
      stepb_ft F_67300 D_67300 ltac:(rewrite H12; apply c_eq_refl).
      stepLD8 F_67304 D_67304 (Z_to_bv 64 nx).
      stepn F_67308 D_67308.
      stepSTx F_67310 D_67310 (Z_to_bv 64 (700056 + 80 + 8 * sc)) (Z_to_bv 64 nx) ltac:(store_ok_peel; exact SOKa).
      stepSTx F_67314 D_67314 (Z_to_bv 64 hd) (Z_to_bv 64 0) ltac:(sok 16%nat SOKh).
      stepSTx F_67318 D_67318 (Z_to_bv 64 (hd + 8)) (Z_to_bv 64 0) ltac:(sok 16%nat SOKh).
      stepLD8 F_6731c D_6731c (Z_to_bv 64 nx).
      stepb_ft F_67320 D_67320 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).
      pu_refl.
    - post.
  Qed.
End Deq.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Skip.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (m : mem) (sc g fr W nx fr2 : Z).
  Hypothesis Hsc : (0 <= sc < 48)%Z.
  Hypothesis Hg : (HEAPLO <= g)%Z /\ (g + 40 <= CEIL)%Z /\ ((g + 40 <= IMG_LO)%Z \/ (IMG_HI <= g)%Z).
  Hypothesis Hnxr : (HEAPLO <= nx)%Z /\ (nx + 40 <= CEIL)%Z /\ ((nx + 40 <= IMG_LO)%Z \/ (IMG_HI <= nx)%Z).
  Hypothesis Hfr : (0 <= fr < 2^32)%Z.
  Hypothesis Hfr2 : (0 <= fr2 < 2^32)%Z.
  Hypothesis HW : (0 <= W < 2^64)%Z.
  Hypothesis HWf : Z.land W 32 = 32%Z.      (* [comment removed for export] *)
  Hypothesis M_fr : rdn RSEGS m (Z_to_bv 64 (g + 28)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 fr)).
  Hypothesis M_W : rdn RSEGS m (Z_to_bv 64 (g + 32)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 W)).
  Hypothesis M_nx : rdn RSEGS m (Z_to_bv 64 (g + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 nx)).
  Hypothesis M_fr2 : rdn RSEGS m (Z_to_bv 64 (nx + 28)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 fr2)).
  Hypothesis SOKa : store_ok RSEGS m (Z_to_bv 64 (ctx_active sc)) 8%nat = true.

  (* [comment removed for export] *)
  Definition all_mask_of (w : Z) : Z := (2 * 2 ^ (w mod 32) - 1)%Z.
  #[local] Notation all_mask := (all_mask_of W).

  Lemma all_mask_rng : (0 < all_mask < 2^32)%Z.
  Proof using.
    clear. unfold all_mask_of. pose proof (Z.mod_pos_bound W 32 ltac:(lia)) as B.
    pose proof (Z.pow_le_mono_r 2 0 (W mod 32) ltac:(lia) ltac:(lia)) as P0.
    pose proof (Z.pow_le_mono_r 2 (W mod 32) 31 ltac:(lia) ltac:(lia)) as P1.
    change (2^0)%Z with 1%Z in P0. change (2^31)%Z with 2147483648%Z in P1. change (2^32)%Z with 4294967296%Z. lia.
  Qed.

  Lemma E_fb : v_andi (Z_to_bv 64 W) 32 = Z_to_bv 64 32.
  Proof using HWf HW. rewrite v_andi_Z by lia. rewrite HWf. reflexivity. Qed.

  Ltac skip_pre H10 :=
    stepLD F_67324 D_67324 (word_to_le_bytes 4 (Z_to_bv 64 fr)) (Z_to_bv 64 fr)
      ltac:(addr_norm; exact M_fr) ltac:(apply bytes_le_to_Z_4; u_norm; lia);
    rewrite v_lw_s32 by lia;
    stepLD8 F_67328 D_67328 (Z_to_bv 64 W);
    stepn F_6732c D_6732c; rewrite E_fb;
    stepn F_67330 D_67330;
    stepb_ft F_67334 D_67334 ltac:(cond_compute);
    stepn F_67338 D_67338; rewrite (v_sllw_Z_s32 2 W) by lia;
    stepn F_6733c D_6733c; rewrite v_addiw_s32; replace (2 * 2 ^ (W mod 32) + -1)%Z with all_mask by (unfold all_mask_of; lia).

  Lemma aSkipN : forall regs rom,
    getr regs 10 = Z_to_bv 64 g -> fr <> all_mask ->
    exists regs',
      msteps RSEGS (mkst regs (0x67378 : word) m rom) (mkst regs' (0x673a4 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 g /\ getr regs' 13 = s32 fr /\ getr regs' 14 = Z_to_bv 64 2
      /\ keeps_but [11; 12; 13; 14]%bv regs regs'.
  Proof using M_W M_fr HWf HW Hfr Hg RN.
    intros regs rom H10 Hc. ceil; unfold HEAPLO in *. pose proof all_mask_rng as AR.
    eexists. split.
    - skip_pre H10.
      stepb_tk F_67340 D_67340 ltac:(rewrite c_eq_s32; rewrite !Z.mod_small by lia; apply Z.eqb_neq; exact Hc).
      pu_refl.
    - post.
  Qed.

  Definition m_skip : mem := wbytes m (Z_to_bv 64 (ctx_active sc)) (word_to_le_bytes 8 (Z_to_bv 64 nx)).

  Lemma aSkipY : forall regs rom,
    getr regs 10 = Z_to_bv 64 g -> getr regs 21 = Z_to_bv 64 (ctx_active sc) -> fr = all_mask ->
    (nx + 40 <= CTX \/ CTX_END <= nx)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x67378 : word) m rom) (mkst regs' (0x673a4 : word) m_skip rom)
      /\ getr regs' 10 = Z_to_bv 64 nx /\ getr regs' 13 = s32 fr2 /\ getr regs' 14 = Z_to_bv 64 2
      /\ keeps_but [10; 11; 12; 13; 14]%bv regs regs'.
  Proof using SOKa M_fr2 M_nx M_W M_fr HWf HW Hfr2 Hfr Hnxr Hg Hsc RN.
    intros regs rom H10 H21 Hc Dn. ceil; unfold HEAPLO, ctx_active, CTX, CTX_END in *. pose proof all_mask_rng as AR. unfold m_skip.
    eexists. split.
    - skip_pre H10.
      stepb_ft F_67340 D_67340 ltac:(rewrite c_eq_s32; rewrite !Z.mod_small by lia; apply Z.eqb_eq; exact Hc).
      stepLD8 F_67344 D_67344 (Z_to_bv 64 nx).
      stepSTx F_67348 D_67348 (Z_to_bv 64 (700056 + 80 + 8 * sc)) (Z_to_bv 64 nx) ltac:(store_ok_peel; exact SOKa).
      stepLD F_6734c D_6734c (word_to_le_bytes 4 (Z_to_bv 64 fr2)) (Z_to_bv 64 fr2)
        ltac:(addr_norm; rdn_by M_fr2) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      rewrite v_lw_s32 by lia.
      pu_refl.
    - post.
  Qed.
End Skip.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition act_of (b : Z) : Z := (2 * 2 ^ (b mod 32) - 1)%Z.

Section Helpers.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Lemma act_of_rng : forall b, (0 < act_of b < 2^32)%Z.
  Proof using.
    intros b. unfold act_of. pose proof (Z.mod_pos_bound b 32 ltac:(lia)) as B.
    pose proof (Z.pow_le_mono_r 2 0 (b mod 32) ltac:(lia) ltac:(lia)) as P0.
    pose proof (Z.pow_le_mono_r 2 (b mod 32) 31 ltac:(lia) ltac:(lia)) as P1.
    change (2^0)%Z with 1%Z in P0. change (2^31)%Z with 2147483648%Z in P1. change (2^32)%Z with 4294967296%Z. lia.
  Qed.
  Lemma act_of_ones : forall b, act_of b = Z.ones (b mod 32 + 1).
  Proof using.
    intros b. unfold act_of, Z.ones. pose proof (Z.mod_pos_bound b 32 ltac:(lia)).
    rewrite Z.shiftl_1_l, Z.pow_add_r, Z.pow_1_r by lia. lia.
  Qed.
  Lemma land_act_lo : forall fr b, (0 <= fr)%Z -> Z.land fr (act_of b) = lo_bits fr (b mod 32 + 1).
  Proof using.
    intros fr b Hfr. rewrite act_of_ones, Z.land_ones by (pose proof (Z.mod_pos_bound b 32); lia). reflexivity.
  Qed.
  Lemma sc_low_bits : forall x y, (0 <= x -> 0 <= y -> x mod 2^32 = y mod 2^32 -> (x/64) mod 64 = (y/64) mod 64)%Z.
  Proof using.
    intros x y Hx Hy E. change (2^32)%Z with 4294967296%Z in E.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    lia.
  Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  (* [comment removed for export] *)
  Lemma E_sc32 : forall W, (0 <= W < 2^64)%Z -> v_srli (v_slli (s32 (W mod 2^32)) 52) 58 = Z_to_bv 64 (w_sizeclass W).
  Proof using.
    intros W HW. unfold v_srli, v_slli, w_sizeclass. f_equal. rewrite u_s32.
    pose proof (sx32_range (W mod 2^32)) as R.
    rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64)%Z.
    rewrite sc_extract by lia. apply sc_low_bits; [lia|lia|].
    rewrite sx32_mod. apply Z.mod_mod. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma decay_out : forall sc0, (0 <= sc0 < 64)%Z -> (sc0 < 7 \/ 38 < sc0)%Z -> c_ltu (Z_to_bv 64 31) (v_addi (Z_to_bv 64 sc0) (-7)) = true.
  Proof using.
    intros sc0 H R. assert (E : exists k, (k < 64)%nat /\ sc0 = Z.of_nat k) by (exists (Z.to_nat sc0); split; lia).
    destruct E as (k & Hk & ->). enum_nat k 64%nat ltac:(first [vm_compute; reflexivity | exfalso; lia]).
  Qed.
  Lemma decay_in : forall sc0, (7 <= sc0 <= 38)%Z -> c_ltu (Z_to_bv 64 31) (v_addi (Z_to_bv 64 sc0) (-7)) = false.
  Proof using.
    intros sc0 H. assert (E : exists k, (k < 64)%nat /\ sc0 = Z.of_nat k) by (exists (Z.to_nat sc0); split; lia).
    destruct E as (k & Hk & ->). enum_nat k 64%nat ltac:(first [vm_compute; reflexivity | exfalso; lia]).
  Qed.
  Lemma decay_addr : forall sc0, (7 <= sc0 <= 38)%Z -> v_add (Z_to_bv 64 MLOCK) (v_addi (Z_to_bv 64 sc0) (-7)) = Z_to_bv 64 (MLOCK + (sc0 - 7)).
  Proof using. intros sc0 H. unfold v_add, v_addi, MLOCK. apply bv_eq. unorm. unorm. lia. Qed.

  (* [comment removed for export] *)
  Lemma rdn_firstn : forall k n (mm : mem) (a : word) bs,
    rdn RSEGS mm a (k + n)%nat = Some bs -> rdn RSEGS mm a k = Some (firstn k bs).
  Proof using.
    induction k as [|k IH]; intros n mm a bs R; [reflexivity|].
    cbn [rdn Nat.add] in R |- *.
    destruct (match mm a with Some b => Some b | None => seg_rom RSEGS a end) as [b|]; [|discriminate R].
    destruct (rdn RSEGS mm (a + 1) (k + n)) as [rest|] eqn:E; [|discriminate R].
    injection R. intros <-. rewrite (IH n mm (a + 1) rest E). reflexivity.
  Qed.
  Lemma Z_to_le_bytes_firstn : forall k n z, firstn k (Z_to_le_bytes (k + n) z) = Z_to_le_bytes k z.
  Proof using.
    induction k as [|k IH]; intros n z; [reflexivity|]. cbn [Z_to_le_bytes Nat.add firstn]. rewrite IH. reflexivity.
  Qed.
  Lemma rdn_lo4 : forall (mm : mem) a v, (0 <= v < 2^64)%Z ->
    rdn RSEGS mm (Z_to_bv 64 a) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 v)) ->
    rdn RSEGS mm (Z_to_bv 64 a) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 (v mod 2^32))).
  Proof using.
    intros mm a v Hv R8. rewrite (rdn_firstn 4 4 mm _ _ R8). f_equal.
    unfold word_to_le_bytes. change 8%nat with (4 + 4)%nat. rewrite Z_to_le_bytes_firstn.
    apply Z_to_le_bytes_mod. cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Pos.mul]. 
    pose proof (Z.mod_pos_bound v (2^32) ltac:(lia)).
    rewrite !u_Z2bv by lia. rewrite Z.mod_mod by lia. reflexivity.
  Qed.
End Helpers.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Act0.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (m : mem) (sc g memg b fr nx : Z).
  Hypothesis Hsc : (0 <= sc < 48)%Z.
  Hypothesis Hg : (HEAPLO <= g)%Z /\ (g + 40 <= CEIL)%Z /\ ((g + 40 <= IMG_LO)%Z \/ (IMG_HI <= g)%Z).
  Hypothesis Hmemg : (HEAPLO <= memg)%Z /\ (memg + 16 <= CEIL)%Z /\ ((memg + 16 <= IMG_LO)%Z \/ (IMG_HI <= memg)%Z).
  Hypothesis Hb : (0 <= b < 256)%Z.
  Hypothesis Hfr : (0 <= fr < 2^32)%Z.
  Hypothesis Hnx : (HEAPLO <= nx)%Z /\ (nx + 40 <= CEIL)%Z /\ ((nx + 40 <= IMG_LO)%Z \/ (IMG_HI <= nx)%Z).
  Hypothesis M_mem : rdn RSEGS m (Z_to_bv 64 (g + 16)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 memg)).
  Hypothesis M_aib : rdn RSEGS m (Z_to_bv 64 (memg + 8)) 1%nat = Some [Z_to_bv 8 b].
  Hypothesis M_nx : rdn RSEGS m (Z_to_bv 64 (g + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 nx)).
  Hypothesis SOKa : store_ok RSEGS m (Z_to_bv 64 (ctx_active sc)) 8%nat = true.
  #[local] Notation act := (act_of b).

  Ltac act0_pre H10 H13 H14 :=
    stepLD8 F_67350 D_67350 (Z_to_bv 64 memg);
    stepLBU F_67354 D_67354 (Z_to_bv 8 b) ltac:(addr_norm; rdn_solve); rewrite (u8_of_Z b) by lia;
    stepn F_67358 D_67358; rewrite H14; rewrite v_sllw_Z_s32 by lia;
    stepn F_6735c D_6735c; rewrite v_addiw_s32; replace (2 * 2 ^ (b mod 32) + -1)%Z with act by (unfold act_of; lia);
    stepn F_67360 D_67360; rewrite H13, v_and_s32.

  Lemma land_le_l : forall a c, (0 <= a)%Z -> (Z.land a c <= a)%Z.
  Proof using. intros a c Ha. pose proof (Z.sub_land_same_l a c). pose proof (proj2 (Z.land_nonneg a (Z.lnot c)) (or_introl Ha)). lia. Qed.
  Lemma land_act_rng : (0 <= Z.land act fr < 2^32)%Z.
  Proof using Hfr.
    pose proof (act_of_rng b). split; [apply Z.land_nonneg; left; lia|].
    rewrite Z.land_comm. eapply Z.le_lt_trans; [apply land_le_l; lia | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma aAct0a : forall regs rom,
    getr regs 10 = Z_to_bv 64 g -> getr regs 13 = s32 fr -> getr regs 14 = Z_to_bv 64 2 -> Z.land act fr <> 0%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x673a4 : word) m rom) (mkst regs' (0x673cc : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 g
      /\ keeps_but [11; 12; 13; 14]%bv regs regs'.
  Proof using M_aib M_mem Hfr Hb Hmemg Hg memg RN.
    intros regs rom H10 H13 H14 Hnz. ceil; unfold HEAPLO in *. pose proof land_act_rng as LR.
    eexists. split.
    - act0_pre H10 H13 H14.
      stepb_tk F_67364 D_67364 ltac:(rewrite zero_s32, c_eq_s32; rewrite Z.mod_0_l, Z.mod_small by lia; apply Z.eqb_neq; exact Hnz).
      pu_refl.
    - post.
  Qed.

  (* [comment removed for export] *)
  Lemma aAct0g : forall regs rom,
    getr regs 10 = Z_to_bv 64 g -> getr regs 13 = s32 fr -> getr regs 14 = Z_to_bv 64 2 -> Z.land act fr = 0%Z -> nx = g ->
    exists regs',
      msteps RSEGS (mkst regs (0x673a4 : word) m rom) (mkst regs' (0x67784 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 g /\ getr regs' 11 = Z_to_bv 64 memg /\ getr regs' 12 = Z_to_bv 64 b
      /\ keeps_but [11; 12; 13; 14]%bv regs regs'.
  Proof using M_nx M_aib M_mem Hnx Hb Hmemg Hg RN.
    intros regs rom H10 H13 H14 Hz Hs. ceil; unfold HEAPLO in *. subst nx.
    eexists. split.
    - act0_pre H10 H13 H14. rewrite Hz, <- zero_s32.
      stepb_ft F_67364 D_67364 ltac:(apply c_eq_refl).
      stepLD8 F_67368 D_67368 (Z_to_bv 64 g).
      stepb_tk F_6736c D_6736c ltac:(rewrite H10; apply c_eq_refl).
      pu_refl.
    - post.
  Qed.

  Definition m_rot2 : mem := wbytes m (Z_to_bv 64 (ctx_active sc)) (word_to_le_bytes 8 (Z_to_bv 64 nx)).

  (* [comment removed for export] *)
  Lemma aAct0r : forall regs rom,
    getr regs 10 = Z_to_bv 64 g -> getr regs 13 = s32 fr -> getr regs 14 = Z_to_bv 64 2 -> getr regs 21 = Z_to_bv 64 (ctx_active sc) ->
    Z.land act fr = 0%Z -> nx <> g ->
    exists regs',
      msteps RSEGS (mkst regs (0x673a4 : word) m rom) (mkst regs' (0x673cc : word) m_rot2 rom)
      /\ getr regs' 10 = Z_to_bv 64 nx
      /\ keeps_but [10; 11; 12; 13; 14]%bv regs regs'.
  Proof using SOKa M_nx M_aib M_mem Hnx Hb Hmemg Hg Hsc memg RN.
    intros regs rom H10 H13 H14 H21 Hz Hne. ceil; unfold HEAPLO, ctx_active, CTX in *. unfold m_rot2.
    eexists. split.
    - act0_pre H10 H13 H14. rewrite Hz, <- zero_s32.
      stepb_ft F_67364 D_67364 ltac:(apply c_eq_refl).
      stepLD8 F_67368 D_67368 (Z_to_bv 64 nx).
      stepb_ft F_6736c D_6736c ltac:(rewrite H10, c_eq_Z by lia; apply Z.eqb_neq; exact Hne).
      stepSTx F_67370 D_67370 (Z_to_bv 64 (700056 + 80 + 8 * sc)) (Z_to_bv 64 nx) ltac:(store_ok_peel; exact SOKa).
      stepn F_67374 D_67374.
      pu_refl.
    - post.
  Qed.
End Act0.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Chk.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (m : mem) (g : Z).
  Hypothesis Hg : (HEAPLO <= g)%Z /\ (g + 40 <= CEIL)%Z /\ ((g + 40 <= IMG_LO)%Z \/ (IMG_HI <= g)%Z).
  Hypothesis M_av : rdn RSEGS m (Z_to_bv 64 (g + 24)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)).
  Lemma aChk : forall regs rom,
    getr regs 10 = Z_to_bv 64 g ->
    exists regs',
      msteps RSEGS (mkst regs (0x673cc : word) m rom) (mkst regs' (0x673d8 : word) m rom)
      /\ keeps_but [11]%bv regs regs'.
  Proof using M_av Hg RN.
    intros regs rom H10. ceil; unfold HEAPLO in *.
    eexists. split.
    - stepLD F_67378 D_67378 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
        ltac:(addr_norm; exact M_av) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepb_tk F_6737c D_6737c ltac:(apply c_eq_refl).
      pu_refl.
    - solve_keeps_but.
  Qed.
End Chk.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Act8.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (m : mem) (g memg b fr W bnc : Z).
  Hypothesis Hg : (HEAPLO <= g)%Z /\ (g + 40 <= CEIL)%Z /\ ((g + 40 <= IMG_LO)%Z \/ (IMG_HI <= g)%Z) /\ (g mod 8 = 0)%Z.
  Hypothesis Hmemg : (HEAPLO <= memg)%Z /\ (memg + 16 <= CEIL)%Z /\ ((memg + 16 <= IMG_LO)%Z \/ (IMG_HI <= memg)%Z).
  Hypothesis Hb : (0 <= b < 256)%Z.
  Hypothesis Hfr : (0 <= fr < 2^32)%Z.
  Hypothesis HW : (0 <= W < 2^64)%Z.
  Hypothesis Hbnc : (0 <= bnc < 256)%Z.
  Hypothesis M_mem : rdn RSEGS m (Z_to_bv 64 (g + 16)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 memg)).
  Hypothesis M_aib : rdn RSEGS m (Z_to_bv 64 (memg + 8)) 1%nat = Some [Z_to_bv 8 b].
  Hypothesis M_fr : rdn RSEGS m (Z_to_bv 64 (g + 28)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 fr)).
  Hypothesis M_Wlo : rdn RSEGS m (Z_to_bv 64 (g + 32)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 (W mod 2^32))).
  Hypothesis SOKh : store_ok RSEGS m (Z_to_bv 64 (g + 24)) 8%nat = true.
  #[local] Notation ai := (b mod 32)%Z.
  #[local] Notation scw := (w_sizeclass W).
  Hypothesis M_bnc : (7 <= scw <= 38)%Z -> rdn RSEGS m (Z_to_bv 64 (ctx_bounces (scw - 7))) 1%nat = Some [Z_to_bv 8 bnc].
  Hypothesis SOKb : (7 <= scw <= 38)%Z -> store_ok RSEGS m (Z_to_bv 64 (ctx_bounces (scw - 7))) 1%nat = true.
  Hypothesis Hlo : lo_bits fr (ai + 1) <> 0%Z.

  Definition m_act8 : mem :=
    wbytes (wbytes m (Z_to_bv 64 (g + 28)) (word_to_le_bytes 4 (Z_to_bv 64 (hi_bits fr (ai + 1)))))
           (Z_to_bv 64 (g + 24)) (word_to_le_bytes 4 (Z_to_bv 64 (lo_bits fr (ai + 1)))).
  Definition m_act8d : mem :=
    wbytes m_act8 (Z_to_bv 64 (ctx_bounces (scw - 7))) (word_to_le_bytes 1 (Z_to_bv 64 (bnc - 1))).

  Definition clobA8 : list reg := [11; 12; 13; 14; 15; 16; 17]%bv.

  Lemma scw_rng : (0 <= scw < 64)%Z.
  Proof using b g. unfold w_sizeclass. apply Z.mod_pos_bound. lia. Qed.

  Ltac act8_pre H10 :=
    stepLD8 F_67384 D_67384 (Z_to_bv 64 memg);
    stepLBU F_67388 D_67388 (Z_to_bv 8 b) ltac:(addr_norm; rdn_solve); rewrite (u8_of_Z b) by lia;
    stepn F_6738c D_6738c;
    stepn F_67390 D_67390; rewrite v_sllw_Z_s32 by lia;
    stepn F_67394 D_67394; rewrite H10; addi_renorm;
    stepn F_67398 D_67398;
    stepLD F_6739c D_6739c (word_to_le_bytes 4 (Z_to_bv 64 fr)) (Z_to_bv 64 fr)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia);
    rewrite v_lw_s32 by lia;
    stepn F_673a0 D_673a0;
    (* [comment removed for export] *)
    chain_step; [reflexivity
      | eapply (step_lr_w RSEGS _ _ _ _ _ true true 16 12 (word_to_le_bytes 4 (Z_to_bv 64 fr)) (Z_to_bv 64 fr));
        [exact F_673a4 | reflexivity | exact D_673a4 | gres; assumption | gres; addr_norm; rdn_solve | apply bytes_le_to_Z_4; u_norm; lia ]
      | step_simpl ];
    cbn [bv_eqb]; rewrite v_lw_s32 by lia;
    chain_step; [reflexivity
      | eapply step_bne_ft_r; [exact F_673a8 | reflexivity | exact D_673a8 | gres; apply c_eq_refl ]
      | step_simpl ];
    chain_step; [reflexivity
      | eapply step_sc_w_ok; [exact F_673ac | reflexivity | exact D_673ac | gres; assumption | gres; reflexivity
          | gres; store_ok_peel; eapply (store_ok_sub _ _ _ _ 8%nat); [ | exact SOKh | | ]; zsimp; lia ]
      | step_simpl ];
    cbn [bv_eqb]; vnorm;
    stepb_ft F_673b0 D_673b0 ltac:(cond_compute);
    stepn F_673b4 D_673b4; rewrite v_addiw_s32, Z.add_0_r;
    stepb_ft F_673b8 D_673b8 ltac:(apply c_eq_refl);
    stepn F_673bc D_673bc; rewrite v_addiw_s32; replace (2 * 2 ^ ai + -1)%Z with (act_of b) by (unfold act_of; lia);
    stepn F_673c0 D_673c0; rewrite v_and_s32, (land_act_lo fr b) by lia;
    stepSTx F_673c4 D_673c4 (Z_to_bv 64 (g + 24)) (s32 (lo_bits fr (ai + 1)))
      ltac:(store_ok_peel; eapply (store_ok_sub _ _ _ _ 8%nat); [ | exact SOKh | | ]; zsimp; lia);
    rewrite (act_hi_word fr ai) by lia; rewrite w2le4_s32.

  Lemma lo_rng : (0 <= lo_bits fr (ai + 1) < 2^32)%Z /\ (0 <= ai < 32)%Z.
  Proof using Hlo HW Hfr Hb W g.
    pose proof (Z.mod_pos_bound b 32 ltac:(lia)). pose proof (lo_bits_range fr (ai + 1) ltac:(lia) ltac:(lia)). lia.
  Qed.

  Ltac act8_mid :=
    stepb_tk F_673c8 D_673c8 ltac:(rewrite zero_s32, c_eq_s32; rewrite Z.mod_0_l, Z.mod_small by lia; apply Z.eqb_neq; exact Hlo);
    stepLD F_673d0 D_673d0 (word_to_le_bytes 4 (Z_to_bv 64 (W mod 2^32))) (Z_to_bv 64 (W mod 2^32))
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia);
    rewrite v_lw_s32 by lia;
    stepn F_673d4 D_673d4;
    stepn F_673d8 D_673d8; rewrite (E_sc32 W) by lia;
    stepn F_673dc D_673dc;
    stepn F_673e0 D_673e0.

  (* [comment removed for export] *)
  Lemma aAct8n : forall regs rom,
    getr regs 10 = Z_to_bv 64 g -> getr regs 22 = Z_to_bv 64 MLOCK -> (scw < 7 \/ 38 < scw)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x673d8 : word) m rom) (mkst regs' (0x67450 : word) m_act8 rom)
      /\ getr regs' 10 = Z_to_bv 64 g /\ getr regs' 11 = s32 (lo_bits fr (ai + 1))
      /\ keeps_but clobA8 regs regs'.
  Proof using Hlo SOKh M_Wlo M_fr M_aib M_mem Hbnc HW Hfr Hb Hmemg Hg bnc memg RN.
    intros regs rom H10 H22 Hout. ceil; unfold HEAPLO in *. unfold m_act8. pose proof lo_rng as [LR AR]. pose proof scw_rng as SR.
    pose proof (Z.mod_pos_bound W (2^32) ltac:(lia)) as WR.
    assert (Hal : (bv_unsigned (Z_to_bv 64 (g + 28)) mod 4 = 0)%Z).
    { rewrite u_Z2bv by lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
    eexists. split.
    - act8_pre H10. rewrite (Z.mod_small (lo_bits fr (ai + 1))) by lia.
      act8_mid.
      stepb_tk F_673e4 D_673e4 ltac:(apply decay_out; [exact SR | exact Hout]).
      pu_refl.
    - post.
  Qed.

  (* [comment removed for export] *)
  Lemma aAct8z : forall regs rom,
    getr regs 10 = Z_to_bv 64 g -> getr regs 22 = Z_to_bv 64 MLOCK -> (7 <= scw <= 38)%Z -> bnc = 0%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x673d8 : word) m rom) (mkst regs' (0x67450 : word) m_act8 rom)
      /\ getr regs' 10 = Z_to_bv 64 g /\ getr regs' 11 = s32 (lo_bits fr (ai + 1))
      /\ keeps_but clobA8 regs regs'.
  Proof using Hlo SOKb M_bnc SOKh M_Wlo M_fr M_aib M_mem Hbnc HW Hfr Hb Hmemg Hg memg RN.
    intros regs rom H10 H22 Hin Hz. ceil; unfold HEAPLO, ctx_bounces, CTX in *. unfold m_act8. pose proof lo_rng as [LR AR]. pose proof scw_rng as SR.
    pose proof (Z.mod_pos_bound W (2^32) ltac:(lia)) as WR. subst bnc.
    pose proof (M_bnc Hin) as MB.
    assert (Hal : (bv_unsigned (Z_to_bv 64 (g + 28)) mod 4 = 0)%Z).
    { rewrite u_Z2bv by lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
    eexists. split.
    - act8_pre H10. rewrite (Z.mod_small (lo_bits fr (ai + 1))) by lia.
      act8_mid.
      stepb_ft F_673e4 D_673e4 ltac:(apply decay_in; exact Hin).
      stepn F_673e8 D_673e8. rewrite H22, (decay_addr scw Hin). unfold MLOCK.
      stepLBU F_673ec D_673ec (Z_to_bv 8 0) ltac:(unfold v_addi; unorm; replace (700048 + (scw - 7) + 888)%Z with (700056 + 880 + (scw - 7))%Z by lia; rdn_by MB).
      vals_lit.
      stepb_tk F_673f0 D_673f0 ltac:(apply c_eq_refl).
      pu_refl.
    - post.
  Qed.

  (* [comment removed for export] *)
  Lemma aAct8d : forall regs rom,
    getr regs 10 = Z_to_bv 64 g -> getr regs 22 = Z_to_bv 64 MLOCK -> (7 <= scw <= 38)%Z -> bnc <> 0%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x673d8 : word) m rom) (mkst regs' (0x67450 : word) m_act8d rom)
      /\ getr regs' 10 = Z_to_bv 64 g /\ getr regs' 11 = s32 (lo_bits fr (ai + 1))
      /\ keeps_but clobA8 regs regs'.
  Proof using Hlo SOKb M_bnc SOKh M_Wlo M_fr M_aib M_mem Hbnc HW Hfr Hb Hmemg Hg memg RN.
    intros regs rom H10 H22 Hin Hnz. ceil; unfold HEAPLO, ctx_bounces, CTX in *. unfold m_act8d, m_act8, ctx_bounces, CTX.
    pose proof lo_rng as [LR AR]. pose proof scw_rng as SR.
    pose proof (Z.mod_pos_bound W (2^32) ltac:(lia)) as WR.
    pose proof (M_bnc Hin) as MB. pose proof (SOKb Hin) as SB.
    assert (Hal : (bv_unsigned (Z_to_bv 64 (g + 28)) mod 4 = 0)%Z).
    { rewrite u_Z2bv by lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
    eexists. split.
    - act8_pre H10. rewrite (Z.mod_small (lo_bits fr (ai + 1))) by lia.
      act8_mid.
      stepb_ft F_673e4 D_673e4 ltac:(apply decay_in; exact Hin).
      stepn F_673e8 D_673e8. rewrite H22, (decay_addr scw Hin). unfold MLOCK.
      stepLBU F_673ec D_673ec (Z_to_bv 8 bnc) ltac:(unfold v_addi; unorm; replace (700048 + (scw - 7) + 888)%Z with (700056 + 880 + (scw - 7))%Z by lia; rdn_by MB).
      rewrite (u8_of_Z bnc) by lia.
      stepb_ft F_673f0 D_673f0 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; exact Hnz).
      stepn F_673f4 D_673f4.
      stepSTx F_673f8 D_673f8 (Z_to_bv 64 (700056 + 880 + (scw - 7))) (v_addi (Z_to_bv 64 bnc) (-1))
        ltac:(store_ok_peel; exact SB).
      replace [Z_to_bv 8 (bv_unsigned (v_addi (Z_to_bv 64 bnc) (-1)))] with (word_to_le_bytes 1 (Z_to_bv 64 (bnc - 1)))
        by (unfold word_to_le_bytes, v_addi; cbn [Z_to_le_bytes]; unorm; unorm; f_equal; f_equal; lia).
      pu_refl.
    - post.
  Qed.
End Act8.
End UbMhASlotW2.
Module UbMhASlotW3.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.Ubsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac.LibAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhEnframeBase OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFreeA.UbMhGetMeta OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac.UbMhBits OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac UbMhCtz UbMhASlotW1 UbMhASlotW2 OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM1.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.PuStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac is_Z_lit ::= ps_is_Z_lit.   (* [comment removed for export] *)
#[local] Ltac check_closed_term_fast ::= ps_check_closed.
#[local] Ltac gres ::= pu_gres.
#[local] Ltac chain_step ::= pu_chain_step.   (* [comment removed for export] *)
#[local] Ltac vnorm ::= pu_vnorm.
#[local] Ltac step_simpl ::= pu_step_simpl.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac post := repeat split; gres; try reflexivity; try assumption; try solve_keeps_but.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition gcond (span size : Z) : bool := (Z.lxor (span + size - 1) span <? 4096)%Z.
(* [comment removed for export] *)
Fixpoint gl (fuel : nat) (span size : Z) : Z :=
  match fuel with
  | O => 1
  | S f => if gcond span size then 1 + gl f (span + size) size else 1
  end%Z.
Fixpoint gl_ok (fuel : nat) (span size : Z) : bool :=
  match fuel with
  | O => false
  | S f => if gcond span size then gl_ok f (span + size) size else true
  end.
Definition GFUEL : nat := 600.

Section Pure.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Lemma gl_ge1 : forall f span size, (1 <= gl f span size)%Z.
  Proof using. induction f as [|f IH]; intros; cbn; [lia|]. destruct (gcond span size); [pose proof (IH (span + size)%Z size)|]; lia. Qed.
  Lemma gl_le : forall f span size, (gl f span size <= Z.of_nat f + 1)%Z.
  Proof using. induction f as [|f IH]; intros; cbn -[Z.of_nat]; [lia|]. destruct (gcond span size); [pose proof (IH (span + size)%Z size)|]; lia. Qed.

  Lemma lxor_lt_4096 : forall a b, (0 <= a)%Z -> (0 <= b)%Z -> (Z.lxor a b < 4096)%Z -> (a / 4096 = b / 4096)%Z.
  Proof using.
    intros a b Ha Hb Hl.
    assert (X : Z.shiftr (Z.lxor a b) 12 = 0%Z).
    { rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. split; [apply Z.lxor_nonneg; lia | exact Hl]. }
    rewrite Z.shiftr_lxor in X. apply Z.lxor_eq in X. rewrite !Z.shiftr_div_pow2 in X by lia. exact X.
  Qed.

  (* [comment removed for export] *)
  Lemma gl_ok_phase2 : forall n span size, (16 <= size)%Z -> (4096 mod size <> 0)%Z -> (0 <= span)%Z ->
    (span mod 4096) mod size = 0%Z ->
    (4096 - span mod 4096 < 16 * Z.of_nat n)%Z -> gl_ok n span size = true.
  Proof using.
    induction n as [|n IH]; intros span size Hs Hnd Hsp Hj Hm.
    - pose proof (Z.mod_pos_bound span 4096 ltac:(lia)). cbn in Hm. lia.
    - cbn. destruct (gcond span size) eqn:C; [|reflexivity].
      unfold gcond in C. apply Z.ltb_lt in C. apply lxor_lt_4096 in C; [|lia|lia].
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      rewrite Nat2Z.inj_succ in Hm.
      assert (R : (span mod 4096 + size <= 4096)%Z) by nia.
      destruct (Z.eq_dec (span mod 4096 + size) 4096) as [E|NE].
      + exfalso. apply Hnd. clear IH C Hm. rewrite <- E.
        replace (span mod 4096)%Z with (((span mod 4096) / size + 0) * size)%Z by nia.
        replace ((span mod 4096 / size + 0) * size + size)%Z with ((span mod 4096 / size + 1) * size)%Z by lia.
        apply Z_mod_mult.
      + apply IH; [lia|exact Hnd|lia| |]; clear IH C.
        * replace ((span + size) mod 4096)%Z with (span mod 4096 + size)%Z by nia.
          rewrite <- Zplus_mod_idemp_r, Z_mod_same_full, Z.add_0_r. exact Hj.
        * (* [comment removed for export] *) lia.
  Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Lemma gl_ok_phase1 : forall n span size, (16 <= size)%Z -> (4096 mod size <> 0)%Z -> (0 <= span)%Z ->
    (4096 - span mod 4096 + 4112 < 16 * Z.of_nat n)%Z -> gl_ok n span size = true.
  Proof using.
    induction n as [|n IH]; intros span size Hs Hnd Hsp Hm.
    - pose proof (Z.mod_pos_bound span 4096 ltac:(lia)). cbn in Hm. lia.
    - cbn. destruct (gcond span size) eqn:C; [|reflexivity].
      unfold gcond in C. apply Z.ltb_lt in C. apply lxor_lt_4096 in C; [|lia|lia].
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      rewrite Nat2Z.inj_succ in Hm.
      assert (R : (span mod 4096 + size <= 4096)%Z) by nia.
      destruct (Z.eq_dec (span mod 4096 + size) 4096) as [E|NE].
      + apply gl_ok_phase2; [lia|exact Hnd|lia| |]; clear IH C.
        * replace ((span + size) mod 4096)%Z with 0%Z by nia. reflexivity.
        * replace ((span + size) mod 4096)%Z with 0%Z by nia. nia.
      + apply IH; [lia|exact Hnd|lia|]; clear IH C.
        replace ((span + size) mod 4096)%Z with (span mod 4096 + size)%Z by nia. nia.
  Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Lemma gl_ok_GFUEL : forall span size, (16 <= size)%Z -> (4096 mod size <> 0)%Z -> (0 <= span)%Z -> gl_ok GFUEL span size = true.
  Proof using.
    intros span size Hs Hnd Hsp. apply gl_ok_phase1; [lia|exact Hnd|lia|]. pose proof (Z.mod_pos_bound span 4096 ltac:(lia)).
    unfold GFUEL. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
  Qed.

  Lemma v_xor_s32 : forall a b, v_xor (s32 a) (s32 b) = s32 (Z.lxor a b).
  Proof using.
    intros a b. unfold v_xor. apply bv_eq. rewrite !u_s32.
    assert (E : Z.lxor (sx32 a) (sx32 b) = sx32 (Z.lxor a b)).
    { apply Z.bits_inj'. intros k Hk. rewrite Z.lxor_spec, !testbit_sx32 by lia.
      destruct (k <? 32)%Z; [apply eq_sym, Z.lxor_spec|]. destruct (k <? 64)%Z; [apply eq_sym, Z.lxor_spec|reflexivity]. }
    rewrite E. pose proof (sx32_range (Z.lxor a b)). rewrite u_Z2bv by lia. reflexivity.
  Qed.
  Lemma lxor_small31 : forall a b, (0 <= a < 2^31)%Z -> (0 <= b < 2^31)%Z -> (0 <= Z.lxor a b < 2^31)%Z.
  Proof using.
    intros a b Ha Hb. split; [apply Z.lxor_nonneg; lia|].
    destruct (Z.eq_dec (Z.lxor a b) 0) as [->|NE]; [lia|].
    assert (L : (Z.log2 (Z.lxor a b) <= Z.max (Z.log2 a) (Z.log2 b))%Z) by (apply Z.log2_lxor; lia).
    assert (La : (Z.log2 a < 31)%Z) by (destruct (Z.eq_dec a 0) as [->|]; [cbn; lia | apply (proj1 (Z.log2_lt_pow2 a 31 ltac:(lia))); lia]).
    assert (Lb : (Z.log2 b < 31)%Z) by (destruct (Z.eq_dec b 0) as [->|]; [cbn; lia | apply (proj1 (Z.log2_lt_pow2 b 31 ltac:(lia))); lia]).
    apply (proj2 (Z.log2_lt_pow2 (Z.lxor a b) 31 ltac:(pose proof (Z.lxor_nonneg a b); lia))). lia.
  Qed.
  Lemma c_lts_s32_4096 : forall x, (0 <= x < 2^31)%Z -> c_lts (s32 x) (Z_to_bv 64 4096) = (x <? 4096)%Z.
  Proof using.
    intros x Hx. rewrite s32_small by lia. rewrite c_lts_small by (rewrite u_Z2bv by lia; lia).
    unfold bv_ltu. rewrite !u_Z2bv by lia. reflexivity.
  Qed.
End Pure.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Loop.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (m : mem) (size : Z).
  Hypothesis Hsz : (16 <= size < 2^21)%Z.

  Lemma grow_loop : forall fuel regs rom (c span : Z),
    gl_ok fuel span size = true ->
    (0 <= span)%Z -> (span + size * (Z.of_nat fuel + 2) < 2^31)%Z -> (0 <= c)%Z -> (c + Z.of_nat fuel + 1 < 2^31)%Z ->
    getr regs 14 = s32 c -> getr regs 5 = s32 span -> getr regs 16 = s32 (span + size - 1) ->
    getr regs 15 = Z_to_bv 64 size -> getr regs 17 = Z_to_bv 64 4096 ->
    exists regs',
      msteps RSEGS (mkst regs (0x677cc : word) m rom) (mkst regs' (0x677e0 : word) m rom)
      /\ getr regs' 14 = s32 (c + gl fuel span size)
      /\ keeps_but [5; 6; 14; 16]%bv regs regs'.
  Proof using Hsz.
    induction fuel as [|fuel IH]; intros regs rom c span OK Hsp Hb Hc Hcb H14 H5 H16 H15 H17; [discriminate OK|].
    cbn [gl_ok] in OK. cbn [gl].
    assert (SZ : Z_to_bv 64 size = s32 size) by (symmetry; apply s32_small; lia).
    assert (XR : (0 <= Z.lxor (span + size - 1) span < 2^31)%Z) by (apply lxor_small31; nia).
    destruct (gcond span size) eqn:C.
    - (* [comment removed for export] *)
      destruct (IH (regupd (regupd (regupd (regupd regs 6 (s32 (Z.lxor (span + size - 1) span))) 5 (s32 (span + size))) 14 (s32 (c + 1))) 16 (s32 (span + size - 1 + size)))
                   rom (c + 1)%Z (span + size)%Z OK) as (regs' & STEPS & R14 & K); try (gres; reflexivity); try nia.
      { gres. f_equal. lia. }
      { gres. exact H15. }
      { gres. exact H17. }
      eexists. split.
      + stepn F_67778 D_67778. rewrite H16, H5, v_xor_s32.
        stepn F_6777c D_6777c. rewrite H5, H15, SZ, v_addw_s32.
        stepn F_67780 D_67780. rewrite H14, v_addiw_s32.
        stepn F_67784 D_67784. rewrite H16, H15, SZ, v_addw_s32.
        stepb_tk F_67788 D_67788 ltac:(rewrite H17, c_lts_s32_4096 by exact XR; unfold gcond in C; exact C).
        exact STEPS.
      + split; [rewrite R14; f_equal; lia|].
        eapply keeps_but_trans; [|exact K]. solve_keeps_but.
    - eexists. split.
      + stepn F_67778 D_67778. rewrite H16, H5, v_xor_s32.
        stepn F_6777c D_6777c. rewrite H5, H15, SZ, v_addw_s32.
        stepn F_67780 D_67780. rewrite H14, v_addiw_s32.
        stepn F_67784 D_67784. rewrite H16, H15, SZ, v_addw_s32.
        stepb_ft F_67788 D_67788 ltac:(rewrite H17, c_lts_s32_4096 by exact XR; unfold gcond in C; exact C).
        pu_refl.
      + post.
  Qed.
End Loop.

Section OrZ.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Lemma v_or_Z : forall x y, (0 <= x < 2^64)%Z -> (0 <= y < 2^64)%Z -> v_or (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (Z.lor x y).
  Proof using. intros. unfold v_or. rewrite !u_Z2bv by lia. reflexivity. Qed.
End OrZ.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Grow.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (m : mem) (g memg b W : Z) (sbs : list byte).
  Hypothesis Hg : (HEAPLO <= g)%Z /\ (g + 40 <= CEIL)%Z /\ ((g + 40 <= IMG_LO)%Z \/ (IMG_HI <= g)%Z).
  Hypothesis Hmemg : (HEAPLO <= memg)%Z /\ (memg + 16 <= CEIL)%Z /\ ((memg + 16 <= IMG_LO)%Z \/ (IMG_HI <= memg)%Z).
  Hypothesis Hdisj : (memg + 16 <= g \/ g + 40 <= memg)%Z.
  Hypothesis Hb : (0 <= b < 256)%Z.
  Hypothesis HW : (0 <= W < 2^64)%Z.
  #[local] Notation scw := (w_sizeclass W).
  #[local] Notation last := (w_lastidx W).
  #[local] Notation ai := (b mod 32)%Z.
  #[local] Notation size := (16 * size_class scw)%Z.
  Hypothesis Hsc : (scw < 48)%Z.
  Hypothesis M_W : rdn RSEGS m (Z_to_bv 64 (g + 32)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 W)).
  Hypothesis M_sbs : rdn RSEGS m (Z_to_bv 64 (0x2396c + 2 * scw)) 2%nat = Some sbs.
  Hypothesis Hsbs : bytes_le_to_Z sbs = size_class scw.
  Hypothesis M_av : rdn RSEGS m (Z_to_bv 64 (g + 24)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)).
  Hypothesis SOKm : store_ok RSEGS m (Z_to_bv 64 (memg + 8)) 1%nat = true.

  Definition span0_of (bb ww : Z) : Z := (16 * size_class (w_sizeclass ww) * (bb mod 32 + 2) + 16)%Z.
  #[local] Notation span0 := (span0_of b W).
  (* [comment removed for export] *)
  Definition gcnt_of (bb ww : Z) : Z := (bb mod 32 + 1 + gl GFUEL (span0_of bb ww) (16 * size_class (w_sizeclass ww)))%Z.
  Definition gaidx_of (bb ww : Z) : Z := (Z.min (gcnt_of bb ww) (w_lastidx ww + 1) - 1)%Z.
  #[local] Notation cnt' := (gcnt_of b W).
  #[local] Notation aidx' := (gaidx_of b W).
  Definition gbyte_of (bb ww : Z) : Z := Z.lor (gaidx_of bb ww) (Z.land bb 224).
  Hypothesis Hterm : gl_ok GFUEL span0 size = true.

  Definition m_grow : mem := wbytes m (Z_to_bv 64 (memg + 8)) (word_to_le_bytes 1 (Z_to_bv 64 (gbyte_of b W))).

  Lemma scw_rng : (0 <= scw < 48)%Z. Proof using Hsc. split; [unfold w_sizeclass; apply Z.mod_pos_bound; lia | exact Hsc]. Qed.
  Lemma last_rng : (0 <= last < 32)%Z. Proof using. unfold w_lastidx. apply Z.mod_pos_bound. lia. Qed.
  Lemma ai_rng : (0 <= ai < 32)%Z. Proof using. apply Z.mod_pos_bound. lia. Qed.
  Lemma size_rng : (16 <= size <= 131056)%Z.
  Proof using Hsc. pose proof (size_class_pos scw scw_rng). lia. Qed.
  Lemma cnt_rng : (2 <= cnt' <= 634)%Z.
  Proof using Hb. unfold gcnt_of. pose proof ai_rng. pose proof (gl_ge1 GFUEL span0 size). pose proof (gl_le GFUEL span0 size). unfold GFUEL in *. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in *. fold (span0_of b W) in *. lia. Qed.
  Lemma aidx_rng : (0 <= aidx' <= last)%Z /\ (aidx' < 32)%Z.
  Proof using Hb. unfold gaidx_of. fold (gcnt_of b W). pose proof cnt_rng. pose proof last_rng. lia. Qed.
  Lemma gbyte_rng : (0 <= gbyte_of b W < 256)%Z /\ (gbyte_of b W mod 32 = aidx')%Z.
  Proof using HW Hb.
    pose proof aidx_rng as [A1 A2]. unfold gbyte_of. fold (gaidx_of b W).
    assert (L224 : (0 <= Z.land b 224 <= 224)%Z) by (split; [apply Z.land_nonneg; lia | rewrite Z.land_comm; apply land_le_l; lia]).
    assert (L0 : Z.land aidx' (Z.land b 224) = 0%Z).
    { apply Z.bits_inj'. intros n Hn. rewrite !Z.land_spec, Z.bits_0.
      destruct (Z.lt_ge_cases n 5) as [LT5|GE5].
      - replace (Z.testbit 224 n) with false; [rewrite !Bool.andb_false_r; reflexivity|].
        symmetry. assert (E : exists k, (k < 5)%nat /\ n = Z.of_nat k) by (exists (Z.to_nat n); split; lia). destruct E as (k & Hk & ->).
        enum_nat k 5%nat ltac:(reflexivity).
      - rewrite (testbit_high 5 aidx' n) by lia. reflexivity. }
    assert (LO : (Z.lor aidx' (Z.land b 224) = aidx' + Z.land b 224)%Z).
    { rewrite (Z.add_nocarry_lxor _ _ L0). symmetry. apply Z.lxor_lor. exact L0. }
    assert (M224 : ((Z.land b 224) mod 32 = 0)%Z).
    { rewrite <- land_ones_mod with (k := 5%Z) by lia. change (2^5 - 1)%Z with 31%Z. rewrite <- Z.land_assoc.
      change (Z.land 224 31) with 0%Z. apply Z.land_0_r. }
    rewrite LO. split; [lia|].
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
  Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

  Lemma E_ai : v_andi (Z_to_bv 64 b) 31 = Z_to_bv 64 ai.
  Proof using Hb. rewrite v_andi_Z by lia. change 31%Z with (2^5 - 1)%Z. rewrite land_ones_mod by lia. reflexivity. Qed.
  Lemma E_sc2 : v_andi (v_srli (Z_to_bv 64 W) 5) 126 = Z_to_bv 64 (2 * scw).
  Proof using HW.
    rewrite v_srli_Z by lia. rewrite v_andi_Z by (first [lia | split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]]).
    rewrite <- Z.shiftr_div_pow2 by lia. rewrite sc2_extract by lia. reflexivity.
  Qed.
  Lemma E_last : v_andi (Z_to_bv 64 W) 31 = Z_to_bv 64 last.
  Proof using HW. rewrite v_andi_Z by lia. change 31%Z with (2^5 - 1)%Z. rewrite land_ones_mod by lia. reflexivity. Qed.
  Lemma E_b224 : v_andi (Z_to_bv 64 b) 224 = Z_to_bv 64 (Z.land b 224).
  Proof using Hb. rewrite v_andi_Z by lia. reflexivity. Qed.

  Definition clobG : list reg := [5; 6; 7; 11; 12; 13; 14; 15; 16; 17]%bv.

  Lemma aGrow : forall regs rom,
    getr regs 10 = Z_to_bv 64 g -> getr regs 11 = Z_to_bv 64 memg -> getr regs 12 = Z_to_bv 64 b ->
    exists regs',
      msteps RSEGS (mkst regs (0x67784 : word) m rom) (mkst regs' (0x673d8 : word) m_grow rom)
      /\ getr regs' 10 = Z_to_bv 64 g
      /\ keeps_but clobG regs regs'.
  Proof using Hterm SOKm M_av Hsbs M_sbs M_W Hsc HW Hb Hdisj Hmemg Hg sbs RN.
    intros regs rom H10 H11 H12. ceil; unfold HEAPLO in *. unfold m_grow.
    pose proof scw_rng as SR. pose proof last_rng as LR. pose proof ai_rng as AR. pose proof size_rng as ZR.
    pose proof cnt_rng as CR. pose proof aidx_rng as [IR1 IR2]. pose proof gbyte_rng as [BR BM].
    assert (SZ : Z_to_bv 64 size = s32 size) by (symmetry; apply s32_small; lia).
    assert (SPAN0 : (0 <= span0)%Z /\ (span0 + size * (Z.of_nat GFUEL + 2) < 2^31)%Z).
    { unfold span0_of, GFUEL. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. nia. }
    destruct SPAN0 as [S0 S1].
    (* [comment removed for export] *)
    assert (SETUP : exists regs1,
      msteps RSEGS (mkst regs (0x67784 : word) m rom) (mkst regs1 (0x677cc : word) m rom)
      /\ getr regs1 14 = s32 (ai + 1) /\ getr regs1 5 = s32 span0 /\ getr regs1 16 = s32 (span0 + size - 1)
      /\ getr regs1 15 = Z_to_bv 64 size /\ getr regs1 17 = Z_to_bv 64 4096
      /\ getr regs1 10 = Z_to_bv 64 g /\ getr regs1 11 = Z_to_bv 64 memg /\ getr regs1 12 = Z_to_bv 64 b /\ getr regs1 13 = Z_to_bv 64 W
      /\ keeps_but clobG regs regs1).
    { eexists. split.
      - stepn F_67730 D_67730. rewrite H12, E_ai.
        stepLD8 F_67734 D_67734 (Z_to_bv 64 W).
        stepn F_67738 D_67738.
        stepn F_6773c D_6773c. addi_renorm || idtac.
        stepn F_67740 D_67740. vals_lit.
        stepn F_67744 D_67744.
        stepn F_67748 D_67748. rewrite E_sc2.
        stepn F_6774c D_6774c. rewrite (v_add_ZZ 145772 (2 * scw)) by lia.
        stepLHU F_67750 D_67750 sbs (Z_to_bv 64 (size_class scw))
          ltac:(addr_norm; replace (145772 + 2 * scw + 0)%Z with (145772 + 2 * scw)%Z by lia; exact M_sbs) ltac:(rewrite Hsbs; u_norm; lia).
        stepn F_67754 D_67754. unfold v_addi. unorm.
        stepn F_67758 D_67758. rewrite (v_slli_Z ai 4) by (change (2^4)%Z with 16%Z; lia). change (2^4)%Z with 16%Z.
        stepn F_6775c D_6775c. unfold v_addi. unorm.
        stepn F_67760 D_67760. rewrite (v_slli_Z (size_class scw) 4) by (change (2^4)%Z with 16%Z; lia). change (2^4)%Z with 16%Z.
        stepn F_67764 D_67764. rewrite v_mul_Z by (unorm; lia).
        stepn F_67768 D_67768. rewrite v_mul_Z by (unorm; lia).
        stepn F_6776c D_6776c. rewrite v_addiw_Z_s32 by (unorm; nia).
        stepn F_67770 D_67770. rewrite v_addiw_Z_s32 by (unorm; nia).
        stepn F_67774 D_67774.
        pu_refl.
      - repeat split; gres; try reflexivity; try assumption.
        + unfold v_addi. unorm. symmetry. apply s32_small. lia.
        + unorm. unfold span0_of. f_equal. lia.
        + unorm. unorm. unfold span0_of. f_equal. lia.
        + apply bv_eq. unorm. lia.
        + solve_keeps_but. }
    destruct SETUP as (regs1 & ST1 & R14 & R5 & R16 & R15 & R17 & R10 & R11 & R12 & R13 & K1).
    destruct (grow_loop m size ltac:(lia) GFUEL regs1 rom (ai + 1) span0 Hterm S0 S1 ltac:(lia)
                ltac:(unfold GFUEL; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) R14 R5 R16 R15 R17)
      as (regs2 & ST2 & R14' & K2).
    replace (ai + 1 + gl GFUEL span0 size)%Z with cnt' in R14' by reflexivity.
    assert (CS : s32 cnt' = Z_to_bv 64 cnt') by (apply s32_small; lia).
    assert (R10' : getr regs2 10 = Z_to_bv 64 g) by (rewrite (keeps_but_get _ _ _ 10 K2) by reflexivity; exact R10).
    assert (R11' : getr regs2 11 = Z_to_bv 64 memg) by (rewrite (keeps_but_get _ _ _ 11 K2) by reflexivity; exact R11).
    assert (R12' : getr regs2 12 = Z_to_bv 64 b) by (rewrite (keeps_but_get _ _ _ 12 K2) by reflexivity; exact R12).
    assert (R13' : getr regs2 13 = Z_to_bv 64 W) by (rewrite (keeps_but_get _ _ _ 13 K2) by reflexivity; exact R13).
    (* [comment removed for export] *)
    assert (L224 : (0 <= Z.land b 224 <= 224)%Z) by (split; [apply Z.land_nonneg; lia | rewrite Z.land_comm; apply land_le_l; lia]).
    assert (TAIL : forall regs3, getr regs3 14 = Z_to_bv 64 aidx' -> getr regs3 10 = Z_to_bv 64 g -> getr regs3 11 = Z_to_bv 64 memg ->
      getr regs3 12 = Z_to_bv 64 b ->
      exists regs',
      msteps RSEGS (mkst regs3 (0x677f4 : word) m rom) (mkst regs' (0x673d8 : word) m_grow rom)
      /\ getr regs' 10 = Z_to_bv 64 g /\ keeps_but clobG regs3 regs').
    { intros regs3 Q14 Q10 Q11 Q12. unfold m_grow, gbyte_of. fold (gaidx_of b W). eexists. split.
      - stepn F_677a0 D_677a0. rewrite Q14, v_andi_Z by lia. change 31%Z with (2^5-1)%Z. rewrite land_ones_mod, (Z.mod_small aidx') by lia.
        stepn F_677a4 D_677a4. rewrite Q12, E_b224.
        stepn F_677a8 D_677a8. rewrite v_or_Z by lia.
        stepSTx F_677ac D_677ac (Z_to_bv 64 (memg + 8)) (Z_to_bv 64 (Z.lor aidx' (Z.land b 224))) ltac:(store_ok_peel; exact SOKm).
        replace [Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (Z.lor aidx' (Z.land b 224))))] with (word_to_le_bytes 1 (Z_to_bv 64 (Z.lor aidx' (Z.land b 224))))
          by (unfold word_to_le_bytes; cbn [Z_to_le_bytes]; reflexivity).
        stepLD F_677b0 D_677b0 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
          ltac:(addr_norm; rdn_by M_av) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
        stepb_ft F_677b4 D_677b4 ltac:(apply c_eq_refl).
        stepn F_677b8 D_677b8.
        pu_refl.
      - post. }
    destruct (Z_lt_le_dec cnt' (last + 1)) as [LT|GE].
    - assert (EA : aidx' = (cnt' - 1)%Z) by (unfold gaidx_of; fold (gcnt_of b W); lia).
      assert (MID : exists regs3, msteps RSEGS (mkst regs2 (0x677e0 : word) m rom) (mkst regs3 (0x677f4 : word) m rom)
        /\ getr regs3 14 = Z_to_bv 64 aidx' /\ keeps_but [13; 14]%bv regs2 regs3).
      { eexists. split.
        + stepn F_6778c D_6778c. rewrite R13', E_last.
          stepn F_67790 D_67790. addi_renorm.
          stepb_tk F_67794 D_67794 ltac:(rewrite R14', CS, c_ltu_Z by lia; apply Z.ltb_lt; exact LT).
          stepn F_6779c D_6779c. rewrite R14', CS. addi_renorm.
          pu_refl.
        + split; [gres; rewrite EA; reflexivity | solve_keeps_but]. }
      destruct MID as (regs3 & ST3 & Q14 & K3).
      destruct (TAIL regs3 Q14 ltac:(rewrite (keeps_but_get _ _ _ 10 K3) by reflexivity; exact R10')
                 ltac:(rewrite (keeps_but_get _ _ _ 11 K3) by reflexivity; exact R11') ltac:(rewrite (keeps_but_get _ _ _ 12 K3) by reflexivity; exact R12'))
        as (regs4 & ST4 & Q10 & K4).
      exists regs4. split; [|split; [exact Q10|]].
      + eapply msteps_trans; [exact ST1|]. eapply msteps_trans; [exact ST2|]. eapply msteps_trans; [exact ST3 | exact ST4].
      + eapply keeps_but_trans; [exact K1|]. eapply keeps_but_trans; [eapply keeps_but_mono; [exact K2 | intros r Hr; cbn in Hr |- *; tauto]|].
        eapply keeps_but_trans; [eapply keeps_but_mono; [exact K3 | intros r Hr; cbn in Hr |- *; tauto] | exact K4].
    - assert (EA : aidx' = last) by (unfold gaidx_of; fold (gcnt_of b W); lia).
      assert (MID : exists regs3, msteps RSEGS (mkst regs2 (0x677e0 : word) m rom) (mkst regs3 (0x677f4 : word) m rom)
        /\ getr regs3 14 = Z_to_bv 64 aidx' /\ keeps_but [13; 14]%bv regs2 regs3).
      { eexists. split.
        + stepn F_6778c D_6778c. rewrite R13', E_last.
          stepn F_67790 D_67790. addi_renorm.
          stepb_ft F_67794 D_67794 ltac:(rewrite R14', CS, c_ltu_Z by lia; apply Z.ltb_ge; exact GE).
          stepn F_67798 D_67798.
          stepn F_6779c D_6779c. addi_renorm.
          pu_refl.
        + split; [gres; rewrite EA; apply bv_eq; unorm; lia | solve_keeps_but]. }
      destruct MID as (regs3 & ST3 & Q14 & K3).
      destruct (TAIL regs3 Q14 ltac:(rewrite (keeps_but_get _ _ _ 10 K3) by reflexivity; exact R10')
                 ltac:(rewrite (keeps_but_get _ _ _ 11 K3) by reflexivity; exact R11') ltac:(rewrite (keeps_but_get _ _ _ 12 K3) by reflexivity; exact R12'))
        as (regs4 & ST4 & Q10 & K4).
      exists regs4. split; [|split; [exact Q10|]].
      + eapply msteps_trans; [exact ST1|]. eapply msteps_trans; [exact ST2|]. eapply msteps_trans; [exact ST3 | exact ST4].
      + eapply keeps_but_trans; [exact K1|]. eapply keeps_but_trans; [eapply keeps_but_mono; [exact K2 | intros r Hr; cbn in Hr |- *; tauto]|].
        eapply keeps_but_trans; [eapply keeps_but_mono; [exact K3 | intros r Hr; cbn in Hr |- *; tauto] | exact K4].
  Qed.

  Lemma grow_facts : (ai < last)%Z -> (0 <= aidx' <= last)%Z /\ (ai + 1 <= aidx')%Z /\ (0 <= gbyte_of b W < 256)%Z /\ (gbyte_of b W mod 32 = aidx')%Z.
  Proof using HW Hb Hdisj Hmemg Hg memg g RN.
    intros Hlt. pose proof aidx_rng. pose proof gbyte_rng. pose proof cnt_rng.
    assert (ai + 1 <= aidx')%Z.
    { unfold gaidx_of, gcnt_of. fold (span0_of b W). pose proof (gl_ge1 GFUEL span0 size). pose proof ai_rng. pose proof last_rng. lia. }
    tauto.
  Qed.
End Grow.
End UbMhASlotW3.
Module UbMhMallocH.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.Ubsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhEnframeBase OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFreeA.UbMhGetMeta OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac.UbMhBits OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac UbMhCtz UbMhSzc UbMhASlotW1 OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM1.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.PuStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac is_Z_lit ::= ps_is_Z_lit.   (* [comment removed for export] *)
#[local] Ltac check_closed_term_fast ::= ps_check_closed.
#[local] Ltac gres ::= pu_gres.
#[local] Ltac chain_step ::= pu_chain_step.   (* [comment removed for export] *)
#[local] Ltac vnorm ::= pu_vnorm.
#[local] Ltac step_simpl ::= pu_step_simpl.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac post := repeat split; gres; try reflexivity; try assumption; try solve_keeps_but.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition iso_g5 (y : word) : word :=
  let a2 := v_or (v_srliw y 2) y in
  let a0 := v_srliw y 1 in
  let a2 := v_or a2 a0 in
  let a2 := v_srliw a2 2 in
  v_or a2 a0.
Definition iso_g11 (y : word) : word :=
  let a0 := iso_g5 y in
  let a0 := v_or (v_srli a0 4) a0 in
  let a0 := v_or (v_srli a0 8) a0 in
  v_or (v_srli (v_slli a0 33) 49) a0.
Definition iso_bv (y : word) : word :=
  let a0 := iso_g11 y in v_and (v_addi a0 1) (v_xori a0 (-1)).

(* [comment removed for export] *)
Definition iso_c1 (y : word) : word := v_srliw y 2.
Definition iso_c2 (y : word) : word := v_or (iso_c1 y) y.
Definition iso_c3 (y : word) : word := v_srliw y 1.
Definition iso_c4 (y : word) : word := v_or (iso_c2 y) (iso_c3 y).
Definition iso_c5 (y : word) : word := v_srliw (iso_c4 y) 2.
Definition iso_c6 (y : word) : word := v_or (iso_c5 y) (iso_c3 y).
Definition iso_c7 (y : word) : word := v_srli (iso_c6 y) 4.
Definition iso_c8 (y : word) : word := v_or (iso_c7 y) (iso_c6 y).
Definition iso_c9 (y : word) : word := v_srli (iso_c8 y) 8.
Definition iso_c10 (y : word) : word := v_or (iso_c9 y) (iso_c8 y).
Definition iso_c11 (y : word) : word := v_slli (iso_c10 y) 33.
Definition iso_c12 (y : word) : word := v_srli (iso_c11 y) 49.
Definition iso_c13 (y : word) : word := v_or (iso_c12 y) (iso_c10 y).
Definition iso_c14 (y : word) : word := v_addi (iso_c13 y) 1.
Definition iso_c15 (y : word) : word := v_xori (iso_c13 y) (-1).
Definition iso_c16 (y : word) : word := v_and (iso_c14 y) (iso_c15 y).
(* [comment removed for export] *)
Ltac iso_fold c := lazymatch goal with |- msteps _ (mkst (regupd _ _ ?v) _ _ _) _ => change v with c end.

Definition iso_ok (y : Z) : bool := bv_eqb (iso_bv (Z_to_bv 64 y)) (Z_to_bv 64 (2 ^ Z.log2 y)).

Lemma iso_ok_all : forallb iso_ok (zrange 11 8181%nat) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma iso_bv_pow2 : forall x, (10 <= x <= XMAX)%Z -> iso_bv (Z_to_bv 64 (x + 1)) = Z_to_bv 64 (2 ^ szc_t x).
Proof.
  intros x Hx. unfold szc_t, XMAX in *.
  pose proof (forallb_zrange iso_ok 11 8181%nat iso_ok_all (x + 1) ltac:(change (Z.of_nat 8181) with 8181%Z; lia)) as H.
  unfold iso_ok in H. apply bv_eq. apply Z.eqb_eq. exact H.
Qed.

(* [comment removed for export] *)
Definition ix_a0 (t : Z) : word := v_xori (v_slli (Z_to_bv 64 t) 2) 124.
Lemma ix_a0_val : forall t, (3 <= t <= 12)%Z -> ix_a0 t = Z_to_bv 64 (124 - 4 * t).
Proof.
  intros t Ht. assert (E : exists k, (k < 13)%nat /\ t = Z.of_nat k) by (exists (Z.to_nat t); split; lia).
  destruct E as (k & Hk & ->). unfold ix_a0.
  enum_nat k 13%nat ltac:(first [apply bv_eq; vm_compute; reflexivity | lia]).
Qed.

(* [comment removed for export] *)
Lemma lor_even_bit : forall i b, (0 <= i)%Z -> (i mod 2 = 0)%Z -> (0 <= b <= 1)%Z -> Z.lor i b = (i + b)%Z.
Proof.
  intros i b Hi He Hb.
  destruct (Z.eq_dec b 0) as [->|Hb1]; [rewrite Z.lor_0_r; lia|]. assert (b = 1%Z) by lia. subst b.
  assert (Hd : Z.land i 1 = 0%Z).
  { replace 1%Z with (Z.ones 1) by reflexivity. rewrite Z.land_ones by lia. change (2 ^ 1)%Z with 2%Z. exact He. }
  rewrite <- Z.lxor_lor by exact Hd. symmetry. apply Z.add_nocarry_lxor. exact Hd.
Qed.

Lemma ev4a : forall t, ((4 * t - 4) mod 2 = 0)%Z.
Proof. intros. replace (4 * t - 4)%Z with ((2 * t - 2) * 2)%Z by lia. apply Zdiv.Z_mod_mult. Qed.
Lemma ev4b : forall t, ((4 * t - 2) mod 2 = 0)%Z.
Proof. intros. replace (4 * t - 2)%Z with ((2 * t - 1) * 2)%Z by lia. apply Zdiv.Z_mod_mult. Qed.

Lemma v_or_Z : forall x y, (0 <= x < 2^64)%Z -> (0 <= y < 2^64)%Z ->
  v_or (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (Z.lor x y).
Proof. intros. unfold v_or. rewrite !u_Z2bv by lia. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Szc.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (m : mem) (n : Z).
  Hypothesis Hn : (0 <= n < MMAP_THRESHOLD)%Z.
  Hypothesis M_ctz : img_clear m A_TAB_CTZ (A_TAB_CTZ + 32).
  Hypothesis M_sz : sz_img m.

  Definition clobSzc : list reg := [10; 11; 12; 13; 19; 20]%bv.

  (* [comment removed for export] *)
  Lemma mSzcA : forall regs rom,
    getr regs 8 = Z_to_bv 64 n -> getr regs 10 = Z_to_bv 64 0x1ffec -> (n < 157)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x66fb0 : word) m rom) (mkst regs' (0x67134 : word) m rom)
      /\ getr regs' 20 = Z_to_bv 64 (size_to_class n) /\ getr regs' 19 = Z_to_bv 64 A_TAB_CTZ
      /\ keeps_but clobSzc regs regs'.
  Proof using Hn.
    intros regs rom H8 H10 Hlt. unfold MMAP_THRESHOLD, A_TAB_CTZ in *.
    pose proof (szc_x_bounds n ltac:(lia)) as XB. rewrite szc_x_eq in XB by lia.
    assert (Hx : (size_to_class n = (n + 3) / 16)%Z).
    { unfold size_to_class. rewrite szc_of_x_lt10 by (rewrite szc_x_eq by lia; lia). apply szc_x_eq. lia. }
    eexists. split.
    - stepb_tk F_66f5c D_66f5c ltac:(rewrite H8, H10, c_ltu_Z by lia; apply Z.ltb_lt; lia).
      stepn F_66fc8 D_66fc8. rewrite H8. addi_renorm.
      stepn F_66fcc D_66fcc.
      stepn F_66fd0 D_66fd0.
      stepn F_66fd4 D_66fd4. rewrite (v_srli_Z (n + 3) 4) by lia. change (2 ^ 4)%Z with 16%Z.
      stepn F_66fd8 D_66fd8. vals_lit.
      stepb_tk F_66fdc D_66fdc ltac:(rewrite H8, c_ltu_Z by lia; apply Z.ltb_lt; lia).
      pu_refl.
    - post. rewrite Hx. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Ltac szc_prefix H8 H10 :=
    stepb_tk F_66f5c D_66f5c ltac:(rewrite H8, H10, c_ltu_Z by lia; apply Z.ltb_lt; lia);
    stepn F_66fc8 D_66fc8; rewrite H8; addi_renorm;
    stepn F_66fcc D_66fcc;
    stepn F_66fd0 D_66fd0;
    stepn F_66fd4 D_66fd4; rewrite (v_srli_Z (n + 3) 4) by lia; change (2 ^ 4)%Z with 16%Z;
    stepn F_66fd8 D_66fd8; vals_lit;
    stepb_ft F_66fdc D_66fdc ltac:(rewrite H8, c_ltu_Z by lia; apply Z.ltb_ge; lia);
    stepn F_66fe0 D_66fe0; addi_renorm.

  (* [comment removed for export] *)
  Ltac szc_mid x t bs1 Hbs1 Hv1 :=
    stepn F_66fe4 D_66fe4;
    stepn F_66fe8 D_66fe8; iso_fold (iso_c1 (Z_to_bv 64 (x + 1)));
    stepn F_66fec D_66fec; iso_fold (iso_c2 (Z_to_bv 64 (x + 1)));
    stepn F_66ff0 D_66ff0; iso_fold (iso_c3 (Z_to_bv 64 (x + 1)));
    stepn F_66ff4 D_66ff4; vals_lit;
    stepn F_66ff8 D_66ff8; iso_fold (iso_c4 (Z_to_bv 64 (x + 1)));
    stepn F_66ffc D_66ffc; iso_fold (iso_c5 (Z_to_bv 64 (x + 1)));
    stepn F_67000 D_67000; iso_fold (iso_c6 (Z_to_bv 64 (x + 1)));
    stepn F_67004 D_67004; iso_fold (iso_c7 (Z_to_bv 64 (x + 1)));
    stepn F_67008 D_67008; iso_fold (iso_c8 (Z_to_bv 64 (x + 1)));
    stepn F_6700c D_6700c; iso_fold (iso_c9 (Z_to_bv 64 (x + 1)));
    stepn F_67010 D_67010; iso_fold (iso_c10 (Z_to_bv 64 (x + 1)));
    stepn F_67014 D_67014; iso_fold (iso_c11 (Z_to_bv 64 (x + 1)));
    stepn F_67018 D_67018; iso_fold (iso_c12 (Z_to_bv 64 (x + 1)));
    stepn F_6701c D_6701c; iso_fold (iso_c13 (Z_to_bv 64 (x + 1)));
    stepn F_67020 D_67020; iso_fold (iso_c14 (Z_to_bv 64 (x + 1)));
    stepn F_67024 D_67024; iso_fold (iso_c15 (Z_to_bv 64 (x + 1)));
    stepn F_67028 D_67028; iso_fold (iso_c16 (Z_to_bv 64 (x + 1)));
    match goal with |- context [regupd _ 10 ?v] => change v with (iso_bv (Z_to_bv 64 (x + 1))) end;
    rewrite (iso_bv_pow2 x) by (unfold XMAX; lia); fold t;
    rewrite <- (s32_small (2 ^ t)) by lia;
    stepn F_6702c D_6702c;
    stepn F_67030 D_67030; (let CZ := fresh in pose proof (ctz_srliw t ltac:(lia)) as CZ; unfold CTZC in CZ; rewrite CZ; clear CZ);
    stepn F_67034 D_67034; rewrite (v_add_ZZ 145740 (ctzix t)) by lia;
    (let TB := fresh in pose proof (ctz_tab_read m t M_ctz ltac:(lia)) as TB; unfold A_TAB_CTZ in TB;
     stepLBU F_67038 D_67038 (Z_to_bv 8 t) ltac:(addr_norm; replace (145740 + ctzix t + 0)%Z with (145740 + ctzix t)%Z by lia; rdn_by TB);
     clear TB);
    rewrite (u8_Z2bv t) by lia;
    stepn F_6703c D_6703c;
    stepn F_67040 D_67040;
    stepn F_67044 D_67044;
    stepn F_67048 D_67048;
    match goal with |- context [regupd _ 10 ?v] => change v with (ix_a0 t) end; rewrite (ix_a0_val t) by lia;
    stepn F_6704c D_6704c; rewrite (v_sub_ZZ 121 (124 - 4 * t)) by lia; replace (121 - (124 - 4 * t))%Z with (4 * t - 3)%Z by lia;
    stepn F_67050 D_67050; rewrite (v_slli_Z (4 * t - 3) 1) by lia; change (2 ^ 1)%Z with 2%Z;
    stepn F_67054 D_67054; vals_lit;
    stepn F_67058 D_67058; rewrite (v_add_ZZ 145772 ((4 * t - 3) * 2)) by lia;
    replace (145772 + (4 * t - 3) * 2)%Z with (0x2396c + 2 * (4 * t - 3))%Z by lia;
    stepLHU F_6705c D_6705c bs1 (Z_to_bv 64 (size_class (4 * t - 3))) ltac:(addr_norm; exact Hbs1) ltac:(rewrite Hv1; u_norm; lia).

  (* [comment removed for export] *)
  Ltac szc_tail x t c i2 b nb bs2 Hbs2 Hv2 B2 :=
    stepn F_670c4 D_670c4; rewrite (v_sub_ZZ c (124 - 4 * t)) by lia; replace (c - (124 - 4 * t))%Z with i2 by lia;
    stepn F_670c8 D_670c8; rewrite (v_slli_Z i2 1) by lia; change (2 ^ 1)%Z with 2%Z;
    stepn F_670cc D_670cc; rewrite (v_add_ZZ 145772 (i2 * 2)) by lia; replace (145772 + i2 * 2)%Z with (0x2396c + 2 * i2)%Z by lia;
    stepLHU F_670d0 D_670d0 bs2 (Z_to_bv 64 (size_class i2)) ltac:(addr_norm; exact Hbs2) ltac:(rewrite Hv2; u_norm; lia);
    stepn F_670d4 D_670d4;
    match goal with |- context [regupd _ 10 ?v] => replace v with (Z_to_bv 64 b)
      by (change v with (v_sltu (Z_to_bv 64 x) (Z_to_bv 64 (size_class i2))); unfold v_sltu; rewrite c_ltu_Z, B2 by lia; reflexivity) end;
    stepn F_670d8 D_670d8; vals_lit;
    stepn F_670dc D_670dc; rewrite (v_or_Z i2 nb) by lia; rewrite (lor_even_bit i2 nb) by (first [apply ev4a | apply ev4b | lia]);
    pu_refl.

  Lemma mSzcB : forall regs rom,
    getr regs 8 = Z_to_bv 64 n -> getr regs 10 = Z_to_bv 64 0x1ffec -> (157 <= n)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x66fb0 : word) m rom) (mkst regs' (0x67134 : word) m rom)
      /\ getr regs' 20 = Z_to_bv 64 (size_to_class n) /\ getr regs' 19 = Z_to_bv 64 A_TAB_CTZ
      /\ keeps_but clobSzc regs regs'.
  Proof using M_sz M_ctz Hn.
    intros regs rom H8 H10 Hge. unfold MMAP_THRESHOLD, A_TAB_CTZ in *.
    pose proof (szc_x_bounds n ltac:(lia)) as XB. pose proof (szc_x_rng n ltac:(unfold MMAP_THRESHOLD; lia)) as XR.
    assert (Hstc : size_to_class n = szc_of_x (szc_x n)) by reflexivity.
    rewrite szc_x_eq in XB, XR, Hstc by lia. unfold XMAX in XR.
    set (x := ((n + 3) / 16)%Z) in *.
    assert (Hx10 : (10 <= x)%Z) by lia.
    pose proof (szc_t_rng x ltac:(unfold XMAX; lia)) as TR. set (t := szc_t x) in *.
    assert (P2 : (0 < 2 ^ t <= 4096)%Z).
    { split; [apply Z.pow_pos_nonneg; lia|]. change 4096%Z with (2 ^ 12)%Z. apply Z.pow_le_mono_r; lia. }
    change (2 ^ 31)%Z with 2147483648%Z in *.
    pose proof (ctzix_rng t ltac:(lia)) as CR.
    rewrite (szc_of_x_ge10 x Hx10) in Hstc. fold t in Hstc. cbv zeta in Hstc.
    replace (4 * t - 4 + 1)%Z with (4 * t - 3)%Z in Hstc by lia. replace (4 * t - 4 + 2)%Z with (4 * t - 2)%Z in Hstc by lia.
    pose proof (size_class_pos (4 * t - 3) ltac:(lia)) as SP1.
    pose proof (size_class_pos (4 * t - 4) ltac:(lia)) as SP0.
    pose proof (size_class_pos (4 * t - 2) ltac:(lia)) as SP2.
    destruct (sz_entry m (4 * t - 3) M_sz ltac:(lia)) as (bs1 & Hbs1 & Hv1).
    destruct (sz_entry m (4 * t - 4) M_sz ltac:(lia)) as (bs0 & Hbs0 & Hv0).
    destruct (sz_entry m (4 * t - 2) M_sz ltac:(lia)) as (bs2 & Hbs2 & Hv2).
    (* [comment removed for export] *)
    eassert (PRE : msteps RSEGS (mkst regs (0x66fb0 : word) m rom) _).
    { szc_prefix H8 H10. szc_mid x t bs1 Hbs1 Hv1. pu_refl. }
    destruct (x <? size_class (4 * t - 3))%Z eqn:B1.
    - (* [comment removed for export] *)
      apply Z.ltb_lt in B1 as B1'.
      destruct (x <? size_class (4 * t - 4))%Z eqn:B2; rewrite Hstc.
      + eexists. split.
        * eapply msteps_trans; [exact PRE|].
          stepb_tk F_67060 D_67060 ltac:(rewrite c_ltu_Z by lia; exact B1).
          stepn F_670c0 D_670c0.
          szc_tail x t 120%Z (4 * t - 4)%Z 1%Z 0%Z bs0 Hbs0 Hv0 B2.
        * post; try (f_equal; lia).
      + eexists. split.
        * eapply msteps_trans; [exact PRE|].
          stepb_tk F_67060 D_67060 ltac:(rewrite c_ltu_Z by lia; exact B1).
          stepn F_670c0 D_670c0.
          szc_tail x t 120%Z (4 * t - 4)%Z 0%Z 1%Z bs0 Hbs0 Hv0 B2.
        * post; try (f_equal; lia).
    - (* [comment removed for export] *)
      apply Z.ltb_ge in B1 as B1'.
      destruct (x <? size_class (4 * t - 2))%Z eqn:B2; rewrite Hstc.
      + eexists. split.
        * eapply msteps_trans; [exact PRE|].
          stepb_ft F_67060 D_67060 ltac:(rewrite c_ltu_Z by lia; exact B1).
          stepn F_67064 D_67064.
          stepn F_67068 D_67068.
          szc_tail x t 122%Z (4 * t - 2)%Z 1%Z 0%Z bs2 Hbs2 Hv2 B2.
        * post; try (f_equal; lia).
      + eexists. split.
        * eapply msteps_trans; [exact PRE|].
          stepb_ft F_67060 D_67060 ltac:(rewrite c_ltu_Z by lia; exact B1).
          stepn F_67064 D_67064.
          stepn F_67068 D_67068.
          szc_tail x t 122%Z (4 * t - 2)%Z 0%Z 1%Z bs2 Hbs2 Hv2 B2.
        * post; try (f_equal; lia).
  Qed.
End Szc.
End UbMhMallocH.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.glaze.binary_reflection.images Require Import Ubsan.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhEnframeBase OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFreeA OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM1. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhEnframeBase OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFreeA.UbMhGetMeta OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac.UbMhBits OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac UbMhCtz UbMhSzc UbMhASlotW1 UbMhMallocH OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM1.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import PuStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac is_Z_lit ::= ps_is_Z_lit.   (* [comment removed for export] *)
#[local] Ltac check_closed_term_fast ::= ps_check_closed.
#[local] Ltac gres ::= pu_gres.
#[local] Ltac chain_step ::= pu_chain_step.   (* [comment removed for export] *)
#[local] Ltac vnorm ::= pu_vnorm.
#[local] Ltac step_simpl ::= pu_step_simpl.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac post := repeat split; gres; try reflexivity; try assumption; try solve_keeps_but.

(* [comment removed for export] *)
Ltac sextw_norm x := rewrite v_addiw_Z_s32 by lia; rewrite (s32_small (x + 0)) by lia; replace (x + 0)%Z with x by lia.

Section S32b.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Lemma s32_neg_small : forall a, (- 2 ^ 31 <= a < 0)%Z -> s32 a = Z_to_bv 64 (2 ^ 64 + a).
  Proof using.
    intros a Ha. apply bv_eq. rewrite u_s32, u_Z2bv by lia. unfold sx32.
    rewrite testbit_31_mod.
    rewrite <- (Z.mod_unique a (2 ^ 32) (-1) (a + 2 ^ 32)) by lia.
    destruct (Z.leb_spec (2 ^ 31) (a + 2 ^ 32)); lia.
  Qed.
  Lemma v_ori_Z : forall x k, (0 <= x < 2^64)%Z -> (0 <= k < 2^64)%Z -> v_ori (Z_to_bv 64 x) k = Z_to_bv 64 (Z.lor x k).
  Proof using. intros x k Hx Hk. unfold v_ori. rewrite u_Z2bv by lia. unfold bv_wrap. change (bv_modulus 64) with (2^64)%Z. rewrite Z.mod_small by lia. reflexivity. Qed.
  Lemma land1_mod2 : forall a, Z.land a 1 = (a mod 2)%Z.
  Proof using. intros a. change 1%Z with (Z.ones 1) at 1. rewrite Z.land_ones by lia. reflexivity. Qed.
End S32b.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Lck.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variable m : mem.
  Hypothesis M_nl : rdn RSEGS m (Z_to_bv 64 A_NEED_LOCKS) 1%nat = Some [Z_to_bv 8 0].
  Lemma mLck : forall regs rom,
    exists regs',
      msteps RSEGS (mkst regs (0x67134 : word) m rom) (mkst regs' (0x6714c : word) m rom)
      /\ keeps_but [10]%bv regs regs'.
  Proof using M_nl.
    intros regs rom. unfold A_NEED_LOCKS in *.
    eexists. split.
    - stepn F_670e0 D_670e0.
      stepLBU F_670e4 D_670e4 (Z_to_bv 8 0) ltac:(addr_norm; exact M_nl). vals_lit.
      stepb_tk F_670e8 D_670e8 ltac:(cond_compute).
      pu_refl.
    - solve_keeps_but.
  Qed.
End Lck.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Cls.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (m : mem) (sc h0 u0 av0 : Z).
  Hypothesis Hsc : (0 <= sc < 48)%Z.
  Hypothesis Hh0 : (0 <= h0 < 2^64)%Z.
  Hypothesis Hu0 : (0 <= u0 < 2^64)%Z.
  Hypothesis M_act0 : rdn RSEGS m (Z_to_bv 64 (ctx_active sc)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 h0)).
  Hypothesis M_use0 : rdn RSEGS m (Z_to_bv 64 (ctx_usage sc)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 u0)).

  Definition clobCls : list reg := [10; 11; 12; 13; 18; 20]%bv.

  (* [comment removed for export] *)
  Ltac cls_pre H20 H9 :=
    stepn F_670f8 D_670f8; rewrite H20; sextw_norm sc;
    stepn F_670fc D_670fc; rewrite (v_slli_Z sc 3) by lia; change (2 ^ 3)%Z with 8%Z;
    stepn F_67100 D_67100; rewrite H9, (v_add_ZZ 700048 (sc * 8)) by lia;
    stepLD F_67104 D_67104 (word_to_le_bytes 8 (Z_to_bv 64 h0)) (Z_to_bv 64 h0)
      ltac:(unfold v_addi; unorm; replace (700048 + sc * 8 + 88)%Z with (700056 + 80 + 8 * sc)%Z by lia; exact M_act0)
      ltac:(apply bytes_le_to_Z_8).

  Section H.
    Hypothesis Hh0nz : h0 <> 0%Z.
    Hypothesis Hh0r : (HEAPLO <= h0)%Z /\ (h0 + 40 <= CEIL)%Z /\ ((h0 + 40 <= IMG_LO)%Z \/ (IMG_HI <= h0)%Z).
    Hypothesis Hav0 : (0 <= av0 < 2^32)%Z.
    Hypothesis M_av0 : rdn RSEGS m (Z_to_bv 64 (h0 + 24)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 av0)).

    Lemma mClsH : forall regs rom,
      getr regs 20 = Z_to_bv 64 sc -> getr regs 9 = Z_to_bv 64 MLOCK ->
      exists regs',
        msteps RSEGS (mkst regs (0x6714c : word) m rom) (mkst regs' (0x67208 : word) m rom)
        /\ getr regs' 18 = Z_to_bv 64 h0 /\ getr regs' 10 = s32 av0 /\ getr regs' 20 = Z_to_bv 64 sc
        /\ keeps_but clobCls regs regs'.
    Proof using M_av0 Hav0 Hh0nz M_act0 Hh0 Hsc RN.
      intros regs rom H20 H9. ceil; unfold HEAPLO, ctx_active, ctx_usage, CTX, MLOCK in *.
      eexists. split.
      - cls_pre H20 H9.
        stepb_tk F_67108 D_67108 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; exact Hh0nz).
        stepb_ft F_671a4 D_671a4 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; exact Hh0nz).
        stepLD F_671a8 D_671a8 (word_to_le_bytes 4 (Z_to_bv 64 av0)) (Z_to_bv 64 av0)
          ltac:(addr_norm; exact M_av0) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
        rewrite v_lw_s32 by lia.
        stepn F_671ac D_671ac.
        pu_refl.
      - post.
    Qed.
  End H.

  Section Z0.
    Hypothesis Hh0z : h0 = 0%Z.
    (* [comment removed for export] *)
    Hypothesis Hnc : (sc = 6 \/ sc < 4 \/ 32 <= sc \/ sc mod 2 = 1 \/ u0 <> 0)%Z.

    Lemma mClsZ : forall regs rom,
      getr regs 20 = Z_to_bv 64 sc -> getr regs 9 = Z_to_bv 64 MLOCK ->
      exists regs',
        msteps RSEGS (mkst regs (0x6714c : word) m rom) (mkst regs' (0x67208 : word) m rom)
        /\ getr regs' 18 = Z_to_bv 64 0 /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 20 = Z_to_bv 64 sc
        /\ keeps_but clobCls regs regs'.
    Proof using Hnc Hh0z M_use0 M_act0 Hu0 Hsc u0 h0.
      intros regs rom H20 H9. unfold ctx_active, ctx_usage, CTX, MLOCK in *.
      pose proof (Z.mod_pos_bound sc 2 ltac:(lia)) as MB.
      destruct (Z.eq_dec sc 6) as [E6|N6].
      { eexists. split.
        - cls_pre H20 H9.
          stepb_ft F_67108 D_67108 ltac:(rewrite Hh0z; apply c_eq_refl).
          stepn F_6710c D_6710c.
          stepb_tk F_67110 D_67110 ltac:(rewrite E6; apply c_eq_refl).
          stepb_tk F_671a4 D_671a4 ltac:(rewrite Hh0z; apply c_eq_refl).
          stepn F_671b0 D_671b0.
          pu_refl.
        - post. all: rewrite Hh0z; reflexivity. }
      destruct (Z_lt_dec sc 4) as [L4|G4].
      { eexists. split.
        - cls_pre H20 H9.
          stepb_ft F_67108 D_67108 ltac:(rewrite Hh0z; apply c_eq_refl).
          stepn F_6710c D_6710c.
          stepb_ft F_67110 D_67110 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).
          stepn F_67114 D_67114. rewrite H20, v_addiw_Z_s32, s32_neg_small by lia.
          stepn F_67118 D_67118.
          stepb_tk F_6711c D_6711c ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_lt; lia).
          stepb_tk F_671a4 D_671a4 ltac:(rewrite Hh0z; apply c_eq_refl).
          stepn F_671b0 D_671b0.
          pu_refl.
        - post. all: rewrite Hh0z; reflexivity. }
      destruct (Z_le_dec 32 sc) as [G32|L32].
      { eexists. split.
        - cls_pre H20 H9.
          stepb_ft F_67108 D_67108 ltac:(rewrite Hh0z; apply c_eq_refl).
          stepn F_6710c D_6710c.
          stepb_ft F_67110 D_67110 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).
          stepn F_67114 D_67114. rewrite H20, v_addiw_Z_s32, s32_small by lia.
          stepn F_67118 D_67118.
          stepb_tk F_6711c D_6711c ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_lt; lia).
          stepb_tk F_671a4 D_671a4 ltac:(rewrite Hh0z; apply c_eq_refl).
          stepn F_671b0 D_671b0.
          pu_refl.
        - post. all: rewrite Hh0z; reflexivity. }
      destruct (Z.eq_dec (sc mod 2) 1) as [OD|EV].
      { eexists. split.
        - cls_pre H20 H9.
          stepb_ft F_67108 D_67108 ltac:(rewrite Hh0z; apply c_eq_refl).
          stepn F_6710c D_6710c.
          stepb_ft F_67110 D_67110 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).
          stepn F_67114 D_67114. rewrite H20, v_addiw_Z_s32, s32_small by lia.
          stepn F_67118 D_67118.
          stepb_ft F_6711c D_6711c ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_ge; lia).
          stepn F_67120 D_67120. rewrite H20, (v_andi_Z sc 1), land1_mod2, OD by lia.
          stepb_tk F_67124 D_67124 ltac:(cond_compute).
          stepn F_67130 D_67130.
          stepn F_67134 D_67134.
          stepn F_671b0 D_671b0.
          pu_refl.
        - post. all: rewrite Hh0z; reflexivity. }
      assert (Hu0nz : u0 <> 0%Z) by lia.
      eexists. split.
      - cls_pre H20 H9.
        stepb_ft F_67108 D_67108 ltac:(rewrite Hh0z; apply c_eq_refl).
        stepn F_6710c D_6710c.
        stepb_ft F_67110 D_67110 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).
        stepn F_67114 D_67114. rewrite H20, v_addiw_Z_s32, s32_small by lia.
        stepn F_67118 D_67118.
        stepb_ft F_6711c D_6711c ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_ge; lia).
        stepn F_67120 D_67120. rewrite H20, (v_andi_Z sc 1), land1_mod2 by lia. replace (sc mod 2)%Z with 0%Z by lia.
        stepb_ft F_67124 D_67124 ltac:(cond_compute).
        stepLD F_67128 D_67128 (word_to_le_bytes 8 (Z_to_bv 64 u0)) (Z_to_bv 64 u0)
          ltac:(unfold v_addi; unorm; replace (700048 + sc * 8 + 472)%Z with (700056 + 464 + 8 * sc)%Z by lia; exact M_use0)
          ltac:(apply bytes_le_to_Z_8).
        stepb_ft F_6712c D_6712c ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; exact Hu0nz).
        stepn F_67130 D_67130.
        stepn F_67134 D_67134.
        stepn F_671b0 D_671b0.
        pu_refl.
      - post. all: rewrite Hh0z; reflexivity.
    Qed.
  End Z0.

  (* [comment removed for export] *)
  Section C.
    Variables (h1 u1 av1 fr1 : Z).
    Hypothesis Hh0z : h0 = 0%Z.
    Hypothesis Hu0z : u0 = 0%Z.
    Hypothesis Hcs : (4 <= sc < 32)%Z /\ sc <> 6%Z /\ (sc mod 2 = 0)%Z.
    Hypothesis Hh1 : (0 <= h1 < 2^64)%Z.
    Hypothesis Hu1 : (0 <= u1 < 2^64)%Z.          (* [comment removed for export] *)
    Hypothesis M_act1 : rdn RSEGS m (Z_to_bv 64 (ctx_active (sc + 1))) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 h1)).
    Hypothesis M_use1 : rdn RSEGS m (Z_to_bv 64 (ctx_usage (sc + 1))) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 u1)).

    (* [comment removed for export] *)
    Ltac coarse_pre H20 H9 :=
      cls_pre H20 H9;
      stepb_ft F_67108 D_67108 ltac:(rewrite Hh0z; apply c_eq_refl);
      stepn F_6710c D_6710c;
      stepb_ft F_67110 D_67110 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; lia);
      stepn F_67114 D_67114; rewrite H20, v_addiw_Z_s32, s32_small by lia;
      stepn F_67118 D_67118;
      stepb_ft F_6711c D_6711c ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_ge; lia);
      stepn F_67120 D_67120; rewrite H20, (v_andi_Z sc 1), land1_mod2 by lia; replace (sc mod 2)%Z with 0%Z by lia;
      stepb_ft F_67124 D_67124 ltac:(cond_compute);
      stepLD F_67128 D_67128 (word_to_le_bytes 8 (Z_to_bv 64 u0)) (Z_to_bv 64 u0)
        ltac:(unfold v_addi; unorm; replace (700048 + sc * 8 + 472)%Z with (700056 + 464 + 8 * sc)%Z by lia; exact M_use0)
        ltac:(apply bytes_le_to_Z_8);
      stepb_tk F_6712c D_6712c ltac:(rewrite Hu0z; apply c_eq_refl);
      stepn F_67154 D_67154; rewrite H20, (v_ori_Z sc 1), (lor_even_bit sc 1) by lia;
      stepn F_67158 D_67158; sextw_norm (sc + 1)%Z;
      stepn F_6715c D_6715c; rewrite (v_slli_Z (sc + 1) 3) by lia; change (2 ^ 3)%Z with 8%Z;
      stepn F_67160 D_67160; rewrite H9, (v_add_ZZ 700048 ((sc + 1) * 8)) by lia;
      stepLD F_67164 D_67164 (word_to_le_bytes 8 (Z_to_bv 64 h1)) (Z_to_bv 64 h1)
        ltac:(unfold v_addi; unorm; replace (700048 + (sc + 1) * 8 + 88)%Z with (700056 + 80 + 8 * (sc + 1))%Z by lia; exact M_act1)
        ltac:(apply bytes_le_to_Z_8);
      stepLD F_67168 D_67168 (word_to_le_bytes 8 (Z_to_bv 64 u1)) (Z_to_bv 64 u1)
        ltac:(unfold v_addi; unorm; replace (700048 + (sc + 1) * 8 + 472)%Z with (700056 + 464 + 8 * (sc + 1))%Z by lia; exact M_use1)
        ltac:(apply bytes_le_to_Z_8).

    (* [comment removed for export] *)
    Ltac tail_adopt H9 :=
      stepn F_67184 D_67184;
      stepb_tk F_67188 D_67188 ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_lt; lia);
      stepn F_67190 D_67190; sextw_norm (sc + 1)%Z;
      stepn F_67194 D_67194; rewrite (v_slli_Z (sc + 1) 3) by lia; change (2 ^ 3)%Z with 8%Z;
      stepn F_67198 D_67198; rewrite H9, (v_add_ZZ 700048 ((sc + 1) * 8)) by lia;
      stepLD F_6719c D_6719c (word_to_le_bytes 8 (Z_to_bv 64 h1)) (Z_to_bv 64 h1)
        ltac:(unfold v_addi; unorm; replace (700048 + (sc + 1) * 8 + 88)%Z with (700056 + 80 + 8 * (sc + 1))%Z by lia; exact M_act1)
        ltac:(apply bytes_le_to_Z_8);
      stepn F_671a0 D_671a0.
    Ltac tail_keep H20 H9 :=
      stepn F_67184 D_67184;
      stepb_ft F_67188 D_67188 ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_ge; lia);
      stepn F_6718c D_6718c; rewrite H20;
      stepn F_67190 D_67190; sextw_norm sc;
      stepn F_67194 D_67194; rewrite (v_slli_Z sc 3) by lia; change (2 ^ 3)%Z with 8%Z;
      stepn F_67198 D_67198; rewrite H9, (v_add_ZZ 700048 (sc * 8)) by lia;
      stepLD F_6719c D_6719c (word_to_le_bytes 8 (Z_to_bv 64 h0)) (Z_to_bv 64 h0)
        ltac:(unfold v_addi; unorm; replace (700048 + sc * 8 + 88)%Z with (700056 + 80 + 8 * sc)%Z by lia; exact M_act0)
        ltac:(apply bytes_le_to_Z_8);
      stepn F_671a0 D_671a0;
      stepb_tk F_671a4 D_671a4 ltac:(rewrite Hh0z; apply c_eq_refl);
      stepn F_671b0 D_671b0.

    (* [comment removed for export] *)
    Lemma mClsC0 : forall regs rom,
      getr regs 20 = Z_to_bv 64 sc -> getr regs 9 = Z_to_bv 64 MLOCK -> h1 = 0%Z ->
      exists regs',
        msteps RSEGS (mkst regs (0x6714c : word) m rom) (mkst regs' (0x67208 : word) m rom)
        /\ getr regs' 18 = Z_to_bv 64 0 /\ getr regs' 10 = Z_to_bv 64 0
        /\ getr regs' 20 = Z_to_bv 64 (if ((u1 + 3) mod 2 ^ 64 <? 13)%Z then sc + 1 else sc)
        /\ keeps_but clobCls regs regs'.
    Proof using M_use1 M_act1 Hu1 Hcs Hu0z Hh0z M_use0 M_act0 Hsc u0 h0.
      intros regs rom H20 H9 Hh1z. unfold ctx_active, ctx_usage, CTX, MLOCK in *.
      pose proof (Z.mod_pos_bound sc 2 ltac:(lia)) as MB. pose proof (Z.mod_pos_bound (u1 + 3) (2 ^ 64) ltac:(lia)) as MB3.
      destruct ((u1 + 3) mod 2 ^ 64 <? 13)%Z eqn:B.
      - apply Z.ltb_lt in B. eexists. split.
        + coarse_pre H20 H9.
          stepb_tk F_6716c D_6716c ltac:(rewrite Hh1z; apply c_eq_refl).
          stepn F_67180 D_67180. addi_renorm. rewrite (Z_to_bv_mod64 (u1 + 3)).
          tail_adopt H9.
          stepb_tk F_671a4 D_671a4 ltac:(rewrite Hh1z; apply c_eq_refl).
          stepn F_671b0 D_671b0.
          pu_refl.
        + post. all: rewrite ?Hh1z, ?Hh0z; try reflexivity.
      - apply Z.ltb_ge in B. eexists. split.
        + coarse_pre H20 H9.
          stepb_tk F_6716c D_6716c ltac:(rewrite Hh1z; apply c_eq_refl).
          stepn F_67180 D_67180. addi_renorm. rewrite (Z_to_bv_mod64 (u1 + 3)).
          tail_keep H20 H9.
          pu_refl.
        + post. all: rewrite ?Hh1z, ?Hh0z; try reflexivity.
    Qed.

    Section C1.
      Hypothesis Hh1nz : h1 <> 0%Z.
      Hypothesis Hh1r : (HEAPLO <= h1)%Z /\ (h1 + 40 <= CEIL)%Z /\ ((h1 + 40 <= IMG_LO)%Z \/ (IMG_HI <= h1)%Z).
      Hypothesis Hav1 : (0 <= av1 < 2^32)%Z.
      Hypothesis Hfr1 : (0 <= fr1 < 2^32)%Z.
      Hypothesis M_av1 : rdn RSEGS m (Z_to_bv 64 (h1 + 24)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 av1)).
      Hypothesis M_fr1 : rdn RSEGS m (Z_to_bv 64 (h1 + 28)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 fr1)).

      Definition bump1 : Z := if ((av1 =? 0) && (fr1 =? 0))%Z%bool then 3 else 0.

      (* [comment removed for export] *)
      Ltac c1_mid AZ FZ :=
        stepb_ft F_6716c D_6716c ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; exact Hh1nz);
        stepLD F_67170 D_67170 (word_to_le_bytes 4 (Z_to_bv 64 av1)) (Z_to_bv 64 av1)
          ltac:(addr_norm; exact M_av1) ltac:(apply bytes_le_to_Z_4; u_norm; lia);
        rewrite v_lw_s32 by lia;
        lazymatch AZ with
        | false => stepb_tk F_67174 D_67174 ltac:(rewrite zero_s32, c_eq_s32; rewrite Z.mod_0_l, Z.mod_small by lia; apply Z.eqb_neq; lia)
        | true =>
          stepb_ft F_67174 D_67174 ltac:(rewrite zero_s32, c_eq_s32; rewrite Z.mod_0_l, Z.mod_small by lia; apply Z.eqb_eq; lia);
          stepLD F_67178 D_67178 (word_to_le_bytes 4 (Z_to_bv 64 fr1)) (Z_to_bv 64 fr1)
            ltac:(addr_norm; exact M_fr1) ltac:(apply bytes_le_to_Z_4; u_norm; lia);
          rewrite v_lw_s32 by lia;
          lazymatch FZ with
          | false => stepb_tk F_6717c D_6717c ltac:(rewrite zero_s32, c_eq_s32; rewrite Z.mod_0_l, Z.mod_small by lia; apply Z.eqb_neq; lia)
          | true =>
            stepb_ft F_6717c D_6717c ltac:(rewrite zero_s32, c_eq_s32; rewrite Z.mod_0_l, Z.mod_small by lia; apply Z.eqb_eq; lia);
            stepn F_67180 D_67180; addi_renorm; rewrite (Z_to_bv_mod64 (u1 + 3))
          end
        end.

      (* [comment removed for export] *)
      Lemma mClsC1a : forall regs rom,
        getr regs 20 = Z_to_bv 64 sc -> getr regs 9 = Z_to_bv 64 MLOCK -> ((u1 + bump1) mod 2 ^ 64 <? 13)%Z = true ->
        exists regs',
          msteps RSEGS (mkst regs (0x6714c : word) m rom) (mkst regs' (0x67208 : word) m rom)
          /\ getr regs' 18 = Z_to_bv 64 h1 /\ getr regs' 10 = s32 av1 /\ getr regs' 20 = Z_to_bv 64 (sc + 1)
          /\ keeps_but clobCls regs regs'.
      Proof using M_fr1 M_av1 Hfr1 Hav1 Hh1nz M_use1 M_act1 Hu1 Hh1 Hcs Hu0z Hh0z M_use0 M_act0 Hsc u0 h0 RN.
        intros regs rom H20 H9 HB. ceil; unfold ctx_active, ctx_usage, CTX, MLOCK, HEAPLO, bump1 in *.
        pose proof (Z.mod_pos_bound sc 2 ltac:(lia)) as MB. pose proof (Z.mod_pos_bound (u1 + 3) (2 ^ 64) ltac:(lia)) as MB3.
        apply Z.ltb_lt in HB.
        Ltac fin H9 :=
          tail_adopt H9;
          stepb_ft F_671a4 D_671a4 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; exact Hh1nz);
          stepLD F_671a8 D_671a8 (word_to_le_bytes 4 (Z_to_bv 64 av1)) (Z_to_bv 64 av1)
            ltac:(addr_norm; exact M_av1) ltac:(apply bytes_le_to_Z_4; u_norm; lia);
          rewrite v_lw_s32 by lia;
          stepn F_671ac D_671ac;
          pu_refl.
        destruct (av1 =? 0)%Z eqn:EA; [apply Z.eqb_eq in EA | apply Z.eqb_neq in EA].
        - destruct (fr1 =? 0)%Z eqn:EF; [apply Z.eqb_eq in EF | apply Z.eqb_neq in EF]; cbn [andb] in HB.
          + eexists. split; [coarse_pre H20 H9; c1_mid true true; fin H9 | post].
          + rewrite Z.add_0_r, Z.mod_small in HB by lia. eexists. split; [coarse_pre H20 H9; c1_mid true false; fin H9 | post].
        - cbn [andb] in HB. rewrite Z.add_0_r, Z.mod_small in HB by lia. eexists. split; [coarse_pre H20 H9; c1_mid false false; fin H9 | post].
      Qed.

      (* [comment removed for export] *)
      Lemma mClsC1k : forall regs rom,
        getr regs 20 = Z_to_bv 64 sc -> getr regs 9 = Z_to_bv 64 MLOCK -> ((u1 + bump1) mod 2 ^ 64 <? 13)%Z = false ->
        exists regs',
          msteps RSEGS (mkst regs (0x6714c : word) m rom) (mkst regs' (0x67208 : word) m rom)
          /\ getr regs' 18 = Z_to_bv 64 0 /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 20 = Z_to_bv 64 sc
          /\ keeps_but clobCls regs regs'.
      Proof using M_fr1 M_av1 Hfr1 Hav1 Hh1nz M_use1 M_act1 Hu1 Hh1 Hcs Hu0z Hh0z h1 M_use0 M_act0 Hsc u0 h0 RN.
        intros regs rom H20 H9 HB. ceil; unfold ctx_active, ctx_usage, CTX, MLOCK, HEAPLO, bump1 in *.
        pose proof (Z.mod_pos_bound sc 2 ltac:(lia)) as MB. pose proof (Z.mod_pos_bound (u1 + 3) (2 ^ 64) ltac:(lia)) as MB3.
        apply Z.ltb_ge in HB.
        destruct (av1 =? 0)%Z eqn:EA; [apply Z.eqb_eq in EA | apply Z.eqb_neq in EA].
        - destruct (fr1 =? 0)%Z eqn:EF; [apply Z.eqb_eq in EF | apply Z.eqb_neq in EF]; cbn [andb] in HB.
          + eexists. split; [coarse_pre H20 H9; c1_mid true true; tail_keep H20 H9; pu_refl | post; rewrite Hh0z; reflexivity].
          + rewrite Z.add_0_r, Z.mod_small in HB by lia. eexists. split; [coarse_pre H20 H9; c1_mid true false; tail_keep H20 H9; pu_refl | post; rewrite Hh0z; reflexivity].
        - cbn [andb] in HB. rewrite Z.add_0_r, Z.mod_small in HB by lia. eexists. split; [coarse_pre H20 H9; c1_mid false false; tail_keep H20 H9; pu_refl | post; rewrite Hh0z; reflexivity].
      Qed.
    End C1.
  End C.
End Cls.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Msk0.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (m : mem) (sc n : Z).
  Hypothesis Hsc : (0 <= sc < 48)%Z.

  (* [comment removed for export] *)
  Lemma mMsk0 : forall regs rom,
    getr regs 10 = Z_to_bv 64 0 -> getr regs 20 = Z_to_bv 64 sc -> getr regs 8 = Z_to_bv 64 n ->
    exists regs',
      msteps RSEGS (mkst regs (0x67208 : word) m rom) (mkst regs' (0x672b0 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 sc /\ getr regs' 11 = Z_to_bv 64 n /\ getr regs' 18 = Z_to_bv 64 sc
      /\ getr regs' 1 = Z_to_bv 64 0x67250
      /\ keeps_but [1; 10; 11; 18]%bv regs regs'.
  Proof using Hsc.
    intros regs rom H10 H20 H8.
    eexists. split.
    - stepn F_671b4 D_671b4. rewrite H10. vals_lit.
      stepn F_671b8 D_671b8. rewrite H10. vals_lit.
      stepb_tk F_671bc D_671bc ltac:(cond_compute).
      stepn F_671ec D_671ec. rewrite H20. sextw_norm sc.
      stepn F_671f0 D_671f0.
      stepn F_671f4 D_671f4. rewrite H8.
      stepn F_671f8 D_671f8.
      pu_refl.
    - post.
  Qed.
End Msk0.

Section MskT.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (m : mem) (hd mask i : Z).
  Hypothesis Hhd : (HEAPLO <= hd)%Z /\ (hd + 40 <= CEIL)%Z /\ ((hd + 40 <= IMG_LO)%Z \/ (IMG_HI <= hd)%Z).
  Hypothesis Hmask : (0 <= mask < 2^32)%Z.
  Hypothesis Hi : (0 <= i < 32)%Z.
  Hypothesis Hlow : Z.land mask (- mask) = (2 ^ i)%Z.
  Hypothesis Hbit : Z.testbit mask i = true.
  Hypothesis SOK : store_ok RSEGS m (Z_to_bv 64 (hd + 24)) 4%nat = true.
  Hypothesis M_ctz : img_clear m A_TAB_CTZ (A_TAB_CTZ + 32).

  (* [comment removed for export] *)
  Lemma mMskT : forall regs rom,
    getr regs 10 = s32 mask -> getr regs 18 = Z_to_bv 64 hd -> getr regs 19 = Z_to_bv 64 A_TAB_CTZ ->
    exists regs',
      msteps RSEGS (mkst regs (0x67208 : word) m rom) (mkst regs' (0x67264 : word) (m_take m hd mask i) rom)
      /\ getr regs' 19 = Z_to_bv 64 i /\ getr regs' 10 = s32 (mask - 2 ^ i) /\ getr regs' 18 = Z_to_bv 64 hd
      /\ keeps_but [10; 11; 12; 13; 19]%bv regs regs'.
  Proof using M_ctz SOK Hbit Hlow Hi Hmask Hhd RN.
    intros regs rom H10 H18 H19. ceil; unfold HEAPLO, A_TAB_CTZ in *. unfold m_take.
    pose proof (pow2_i_rng i Hi) as [P1 P2]. pose proof (mask_ge mask i Hmask Hi Hbit) as MG.
    change (2^32)%Z with 4294967296%Z in P2.
    pose proof (ctzix_rng i Hi) as CR.
    eexists. split.
    - stepn F_671b4 D_671b4. rewrite H10, zero_s32, v_subw_s32. replace (0 - mask)%Z with (- mask)%Z by lia.
      stepn F_671b8 D_671b8. rewrite H10, v_and_s32, Hlow.
      stepb_ft F_671bc D_671bc ltac:(apply s32_pow2_ne0; exact Hi).
      stepn F_671c0 D_671c0. rewrite H10, zero_s32, v_subw_s32. replace (0 - mask)%Z with (- mask)%Z by lia.
      stepn F_671c4 D_671c4.
      stepn F_671c8 D_671c8. rewrite H10, v_and_s32, Hlow.
      stepn F_671cc D_671cc. vals_lit.
      stepn F_671d0 D_671d0.
      stepn F_671d4 D_671d4. pose proof (ctz_srliw i Hi) as CZ. unfold CTZC in CZ. rewrite CZ. clear CZ.
      stepn F_671d8 D_671d8. rewrite H19, (v_add_ZZ 145740 (ctzix i)) by lia.
      pose proof (ctz_tab_read m i M_ctz Hi) as TB. unfold A_TAB_CTZ in TB.
      stepLBU F_671dc D_671dc (Z_to_bv 8 i) ltac:(addr_norm; replace (145740 + ctzix i + 0)%Z with (145740 + ctzix i)%Z by lia; rdn_by TB).
      stepn F_671e0 D_671e0. rewrite H10, v_subw_s32.
      stepSTx F_671e4 D_671e4 (Z_to_bv 64 (hd + 24)) (s32 (mask - 2 ^ i)) ltac:(store_ok_peel; exact SOK).
      rewrite w2le4_s32, (Z.mod_small (mask - 2 ^ i)) by lia.
      stepn F_671e8 D_671e8.
      pu_refl.
    - post. apply bv_eq. rewrite (UbMhFreeA.UbMhGetMeta.u8_Z2bv i) by lia. unorm. reflexivity.
  Qed.
End MskT.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Ret.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (m : mem) (sc idx hd : Z).
  Hypothesis Hsc : (0 <= sc < 48)%Z.
  Hypothesis Hidx : (0 <= idx < 32)%Z.
  Hypothesis Hhd : (0 <= hd < 2^64)%Z.
  Hypothesis M_act : rdn RSEGS m (Z_to_bv 64 (ctx_active sc)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 hd)).

  Lemma mRet : forall regs rom,
    getr regs 10 = Z_to_bv 64 idx -> getr regs 18 = Z_to_bv 64 sc -> getr regs 9 = Z_to_bv 64 MLOCK ->
    exists regs',
      msteps RSEGS (mkst regs (0x67250 : word) m rom) (mkst regs' (0x67264 : word) m rom)
      /\ getr regs' 19 = Z_to_bv 64 idx /\ getr regs' 18 = Z_to_bv 64 hd
      /\ keeps_but [18; 19]%bv regs regs'.
  Proof using M_act Hidx Hsc.
    intros regs rom H10 H18 H9. unfold ctx_active, CTX, MLOCK in *.
    eexists. split.
    - stepb_ft F_671fc D_671fc ltac:(rewrite H10; apply c_lts_pos_0; u_norm; lia).
      stepn F_67200 D_67200. rewrite H10.
      stepn F_67204 D_67204. rewrite H18, (v_slli_Z sc 3) by lia. change (2 ^ 3)%Z with 8%Z.
      stepn F_67208 D_67208. rewrite H9, (v_add_ZZ 700048 (sc * 8)) by lia.
      stepLD F_6720c D_6720c (word_to_le_bytes 8 (Z_to_bv 64 hd)) (Z_to_bv 64 hd)
        ltac:(unfold v_addi; unorm; replace (700048 + sc * 8 + 88)%Z with (700056 + 80 + 8 * sc)%Z by lia; exact M_act)
        ltac:(apply bytes_le_to_Z_8).
      pu_refl.
    - post.
  Qed.
End Ret.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Tail.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (m : mem) (ctr : Z).
  Hypothesis Hctr : (0 <= ctr < 2^32)%Z.
  Hypothesis M_ctr : rdn RSEGS m (Z_to_bv 64 ctx_mmap_counter) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 ctr)).

  Lemma mTail : forall regs rom,
    getr regs 9 = Z_to_bv 64 MLOCK ->
    exists regs',
      msteps RSEGS (mkst regs (0x67264 : word) m rom) (mkst regs' (0x73da4 : word) m rom)
      /\ getr regs' 20 = s32 ctr /\ getr regs' 10 = Z_to_bv 64 MLOCK /\ getr regs' 1 = Z_to_bv 64 0x67270
      /\ keeps_but [1; 10; 20]%bv regs regs'.
  Proof using M_ctr Hctr.
    intros regs rom H9. unfold ctx_mmap_counter, CTX, MLOCK in *.
    eexists. split.
    - stepLD F_67210 D_67210 (word_to_le_bytes 4 (Z_to_bv 64 ctr)) (Z_to_bv 64 ctr)
        ltac:(addr_norm; exact M_ctr) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      rewrite v_lw_s32 by lia.
      stepn F_67214 D_67214. rewrite H9.
      stepn F_67218 D_67218.
      pu_refl.
    - post.
  Qed.
End Tail.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section ClsAll.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (m : mem) (hd u av fr : Z -> Z).
  Hypothesis Hact : forall s, (0 <= s < 48)%Z ->
    rdn RSEGS m (Z_to_bv 64 (ctx_active s)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (hd s))).
  Hypothesis Huse : forall s, (0 <= s < 48)%Z ->
    rdn RSEGS m (Z_to_bv 64 (ctx_usage s)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (u s))).
  Hypothesis Hhd : forall s, (0 <= s < 48)%Z -> (0 <= hd s < 2^64)%Z.
  Hypothesis Hu : forall s, (0 <= s < 48)%Z -> (0 <= u s < 2^64)%Z.
  Hypothesis Hmeta : forall s, (0 <= s < 48)%Z -> hd s <> 0%Z ->
    (0 <= av s < 2^32)%Z /\ (0 <= fr s < 2^32)%Z /\
    rdn RSEGS m (Z_to_bv 64 (hd s + 24)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 (av s))) /\
    rdn RSEGS m (Z_to_bv 64 (hd s + 28)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 (fr s))).

  Lemma mCls : forall sc0 regs rom, (0 <= sc0 < 48)%Z ->
    getr regs 20 = Z_to_bv 64 sc0 -> getr regs 9 = Z_to_bv 64 MLOCK ->
    exists regs' sc,
      msteps RSEGS (mkst regs (0x6714c : word) m rom) (mkst regs' (0x67208 : word) m rom)
      /\ (0 <= sc < 48)%Z
      /\ (sc = sc0 \/ (sc = sc0 + 1 /\ sc0 mod 2 = 0 /\ 4 <= sc0 < 32 /\ sc0 <> 6))%Z
      /\ getr regs' 20 = Z_to_bv 64 sc /\ getr regs' 18 = Z_to_bv 64 (hd sc)
      /\ getr regs' 10 = (if (hd sc =? 0)%Z then Z_to_bv 64 0 else s32 (av sc))
      /\ keeps_but clobCls regs regs'.
  Proof using Hmeta Hu Hhd Huse Hact fr u RN.
    intros sc0 regs rom Hsc0 H20 H9.
    pose proof (Z.mod_pos_bound sc0 2 ltac:(lia)) as MB.
    destruct (Z.eq_dec (hd sc0) 0) as [Z0|NZ].
    - assert (DEC : {(4 <= sc0 < 32)%Z /\ sc0 <> 6%Z /\ (sc0 mod 2 = 0)%Z /\ u sc0 = 0%Z}
                    + {(sc0 = 6 \/ sc0 < 4 \/ 32 <= sc0 \/ sc0 mod 2 = 1 \/ u sc0 <> 0)%Z}).
      { destruct (Z_le_dec 4 sc0); [|right; lia]. destruct (Z_lt_dec sc0 32); [|right; lia].
        destruct (Z.eq_dec sc0 6); [right; lia|]. destruct (Z.eq_dec (sc0 mod 2) 0); [|right; lia].
        destruct (Z.eq_dec (u sc0) 0); [left; lia | right; lia]. }
      destruct DEC as [(HR & H6 & HE & U0) | Hnc].
      + (* [comment removed for export] *)
        assert (Hsc1 : (0 <= sc0 + 1 < 48)%Z) by lia.
        destruct (Z.eq_dec (hd (sc0 + 1)) 0) as [Z1|NZ1].
        * edestruct (mClsC0 m sc0 (hd sc0) (u sc0) Hsc0 (Hact sc0 Hsc0) (Huse sc0 Hsc0) (hd (sc0 + 1)) (u (sc0 + 1))
                     Z0 U0 (conj HR (conj H6 HE)) (Hu (sc0 + 1) Hsc1) (Hact (sc0 + 1) Hsc1) (Huse (sc0 + 1) Hsc1) regs rom H20 H9 Z1)
            as (r' & S & A18 & A10 & A20 & K).
          destruct ((u (sc0 + 1) + 3) mod 2 ^ 64 <? 13)%Z.
          -- exists r', (sc0 + 1)%Z. rewrite Z1, Z.eqb_refl. repeat split; try assumption; try lia.
          -- exists r', sc0. rewrite Z0, Z.eqb_refl. repeat split; try assumption; try lia.
        * destruct (Hmeta (sc0 + 1) Hsc1 NZ1) as (Rav & Rfr & Mav & Mfr).
          destruct (((u (sc0 + 1) + bump1 (av (sc0 + 1)) (fr (sc0 + 1))) mod 2 ^ 64 <? 13)%Z) eqn:HB.
          -- edestruct (mClsC1a m sc0 (hd sc0) (u sc0) Hsc0 (Hact sc0 Hsc0) (Huse sc0 Hsc0) (hd (sc0 + 1)) (u (sc0 + 1)) (av (sc0 + 1)) (fr (sc0 + 1))
                       Z0 U0 (conj HR (conj H6 HE)) (Hhd (sc0 + 1) Hsc1) (Hu (sc0 + 1) Hsc1) (Hact (sc0 + 1) Hsc1) (Huse (sc0 + 1) Hsc1)
                       NZ1 Rav Rfr Mav Mfr regs rom H20 H9 HB)
               as (r' & S & A18 & A10 & A20 & K).
             exists r', (sc0 + 1)%Z. replace (hd (sc0 + 1) =? 0)%Z with false by (symmetry; apply Z.eqb_neq; exact NZ1).
             repeat split; try assumption; try lia.
          -- edestruct (mClsC1k m sc0 (hd sc0) (u sc0) Hsc0 (Hact sc0 Hsc0) (Huse sc0 Hsc0) (hd (sc0 + 1)) (u (sc0 + 1)) (av (sc0 + 1)) (fr (sc0 + 1))
                       Z0 U0 (conj HR (conj H6 HE)) (Hhd (sc0 + 1) Hsc1) (Hu (sc0 + 1) Hsc1) (Hact (sc0 + 1) Hsc1) (Huse (sc0 + 1) Hsc1)
                       NZ1 Rav Rfr Mav Mfr regs rom H20 H9 HB)
               as (r' & S & A18 & A10 & A20 & K).
             exists r', sc0. rewrite Z0, Z.eqb_refl. repeat split; try assumption; try lia.
      + (* [comment removed for export] *)
        edestruct (mClsZ m sc0 (hd sc0) (u sc0) Hsc0 (Hu sc0 Hsc0) (Hact sc0 Hsc0) (Huse sc0 Hsc0) Z0 Hnc regs rom H20 H9)
          as (r' & S & A18 & A10 & A20 & K).
        exists r', sc0. rewrite Z0, Z.eqb_refl. repeat split; try assumption; try lia.
    - (* [comment removed for export] *)
      destruct (Hmeta sc0 Hsc0 NZ) as (Rav & Rfr & Mav & Mfr).
      edestruct (mClsH m sc0 (hd sc0) (av sc0) Hsc0 (Hhd sc0 Hsc0) (Hact sc0 Hsc0) NZ Rav Mav regs rom H20 H9)
        as (r' & S & A18 & A10 & A20 & K).
      exists r', sc0. replace (hd sc0 =? 0)%Z with false by (symmetry; apply Z.eqb_neq; exact NZ).
      repeat split; try assumption; try lia.
  Qed.
End ClsAll.
