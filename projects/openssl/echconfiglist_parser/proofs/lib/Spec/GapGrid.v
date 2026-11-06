(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Decode.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import KInv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition GRID_M : Z := 2^31.          (* [comment removed for export] *)
Definition GRID_SLOTS : Z := 43680.     (* [comment removed for export] *)
Definition GRID_W : Z := 2^34.          (* [comment removed for export] *)
Definition CBMAX : Z := 2^31.           (* [comment removed for export] *)
Definition GRID_J : Z := 16384.         (* [comment removed for export] *)
Definition GRID_RESV : Z := 8.          (* [comment removed for export] *)
Definition grid_floor : Z := 0x2aaaaaaab000.

Lemma grid_fits : grid_floor + GRID_SLOTS * GRID_M + CBMAX <= CEIL_MIN.
Proof. vm_compute. discriminate. Qed.
Lemma grid_floor_pos : 0 < grid_floor.
Proof. reflexivity. Qed.
Lemma grid_floor_aligned : grid_floor mod 4096 = 0.
Proof. reflexivity. Qed.
Lemma grid_M_aligned : GRID_M mod 4096 = 0.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma pigeon : forall (n : nat) (l : list Z), (length l < n)%nat -> exists i, 0 <= i < Z.of_nat n /\ ~ In i l.
Proof.
  induction n as [|n IH]; intros l Hl; [lia|].
  destruct (in_dec Z.eq_dec (Z.of_nat n) l) as [Hin|Hnot].
  - destruct (in_split _ _ Hin) as (l1 & l2 & ->).
    assert (Hl' : (length (l1 ++ l2) < n)%nat) by (rewrite length_app; rewrite length_app in Hl; cbn in Hl; lia).
    destruct (IH (l1 ++ l2) Hl') as (i & Hi & Hni).
    exists i. split; [lia|]. intros H. apply in_app_or in H as [H|[H|H]]; [apply Hni; apply in_or_app; auto| lia| apply Hni; apply in_or_app; auto].
  - exists (Z.of_nat n). split; [lia| exact Hnot].
Qed.

(* [comment removed for export] *)
Fixpoint esum (E : list (word * word)) : Z :=
  match E with [] => 0 | e :: E' => (ehi e - elo e) + esum E' end.
Lemma esum_app : forall E1 E2, esum (E1 ++ E2) = esum E1 + esum E2.
Proof. induction E1 as [|e E1 IH]; intros E2; [reflexivity|]. cbn [esum app]. rewrite IH. lia. Qed.
Lemma esum_live_bytes : forall maps, esum maps = live_bytes maps.
Proof.
  induction maps as [|[a n] maps IH]; [reflexivity|]. cbn [esum]. unfold ehi, elo. cbn [fst snd].
  change (live_bytes ((a, n) :: maps)) with (bv_unsigned n + live_bytes maps). rewrite IH. lia.
Qed.
Lemma live_bytes_nonneg0 : forall l, 0 <= live_bytes l.
Proof.
  induction l as [|[a n] l IH]; [reflexivity|]. change (live_bytes ((a, n) :: l)) with (bv_unsigned n + live_bytes l).
  pose proof (bv_unsigned_in_range 64 n). lia.
Qed.
Lemma esum_le : forall E W, (forall e, In e E -> elo e < ehi e /\ ehi e - elo e <= W) -> esum E <= Z.of_nat (length E) * W.
Proof.
  induction E as [|e E IH]; intros W HE; [cbn; lia|]. cbn [esum length].
  pose proof (HE e (or_introl eq_refl)). specialize (IH W (fun e' H' => HE e' (or_intror H'))). rewrite Nat2Z.inj_succ. lia.
Qed.

Section Grid.
Variable E : list (word * word).
Variable S : Z.
Hypothesis HS : 0 < S <= CBMAX.
Hypothesis HE : forall e, In e E -> elo e < ehi e /\ ehi e - elo e <= GRID_W.

Definition slot (i : Z) : Z := grid_floor + i * GRID_M.
(* [comment removed for export] *)
Definition clo (e : word * word) : Z := (elo e - S - grid_floor) / GRID_M.
Definition chi (e : word * word) : Z := (ehi e - 1 - grid_floor) / GRID_M.
Definition cells (e : word * word) : list Z :=
  map (fun k => clo e + 1 + Z.of_nat k) (seq 0 (Z.to_nat (chi e - clo e))).

Lemma in_cells : forall e i, clo e < i <= chi e -> In i (cells e).
Proof.
  intros e i Hi. unfold cells. apply in_map_iff. exists (Z.to_nat (i - clo e - 1)). split; [lia|].
  apply in_seq. lia.
Qed.

Lemma meets_cells : forall e i, elo e < slot i + S -> slot i < ehi e -> In i (cells e).
Proof.
  intros e i H1 H2. apply in_cells. unfold clo, chi, slot, GRID_M in *.
  split; Z.div_mod_to_equations; nia.
Qed.

Lemma cells_length : forall e, In e E -> Z.of_nat (length (cells e)) <= (ehi e - elo e) / GRID_M + 2.
Proof.
  intros e He. destruct (HE e He) as [W1 W2]. unfold cells. rewrite length_map, length_seq.
  unfold clo, chi, CBMAX, GRID_M in *. Z.div_mod_to_equations. nia.
Qed.

Definition allcells (E' : list (word * word)) : list Z := concat (map cells E').

Lemma allcells_length : forall E', (forall e, In e E' -> In e E) ->
  Z.of_nat (length (allcells E')) <= esum E' / GRID_M + 2 * Z.of_nat (length E').
Proof.
  induction E' as [|e E' IH]; intros Hsub; [cbn; rewrite Zdiv_0_l; lia|].
  unfold allcells in *. cbn [map concat esum length]. rewrite length_app, Nat2Z.inj_add, Nat2Z.inj_succ.
  pose proof (cells_length e (Hsub e (or_introl eq_refl))) as L1.
  pose proof (IH (fun e' H' => Hsub e' (or_intror H'))) as L2.
  destruct (HE e (Hsub e (or_introl eq_refl))) as [W1 _].
  assert (P0 : 0 <= esum E').
  { clear - Hsub HE. induction E' as [|e' E' IH']; [cbn; lia|]. cbn [esum].
    destruct (HE e' (Hsub e' (or_intror (or_introl eq_refl)))) as [W _].
    specialize (IH' (fun x Hx => Hsub x ltac:(destruct Hx as [<-|Hx]; [left; reflexivity| right; right; exact Hx]))). lia. }
  assert (DV : (ehi e - elo e) / GRID_M + esum E' / GRID_M <= (ehi e - elo e + esum E') / GRID_M).
  { unfold GRID_M. Z.div_mod_to_equations. nia. }
  lia.
Qed.

Theorem grid_gap : esum E / GRID_M + 2 * Z.of_nat (length E) < GRID_SLOTS ->
  exists a, a mod 4096 = 0 /\ grid_floor <= a /\ a + S <= CEIL_MIN
            /\ forall e, In e E -> a + S <= elo e \/ ehi e <= a.
Proof.
  intros HL.
  pose proof (allcells_length E (fun e H => H)) as AL.
  assert (HL' : (length (allcells E) < Z.to_nat GRID_SLOTS)%nat) by (unfold GRID_SLOTS in *; lia).
  destruct (pigeon (Z.to_nat GRID_SLOTS) (allcells E) HL') as (i & Hi & Hni).
  rewrite Z2Nat.id in Hi by (unfold GRID_SLOTS; lia).
  exists (slot i). pose proof grid_fits as GF.
  split; [| split; [| split]].
  - unfold slot, grid_floor, GRID_M. Z.div_mod_to_equations. nia.
  - unfold slot, GRID_M. nia.
  - unfold slot. unfold GRID_SLOTS, GRID_M, CBMAX, grid_floor, CEIL_MIN in *. nia.
  - intros e He.
    destruct (Z.le_gt_cases (slot i + S) (elo e)); [left; lia|].
    destruct (Z.le_gt_cases (ehi e) (slot i)); [right; lia|].
    exfalso. apply Hni. unfold allcells. apply in_concat. exists (cells e). split; [apply in_map; exact He|].
    apply meets_cells; lia.
Qed.
End Grid.

Lemma region_free_introZ : forall maps (a n : word),
  (forall e sz, In (e, sz) maps -> bv_unsigned a + bv_unsigned n <= bv_unsigned e \/ bv_unsigned e + bv_unsigned sz <= bv_unsigned a) ->
  region_free maps a n = true.
Proof.
  induction maps as [|[e0 sz0] maps IH]; intros a n H; [reflexivity|]. cbn [region_free].
  rewrite IH by (intros; apply H; right; assumption).
  specialize (H e0 sz0 (or_introl eq_refl)). unfold iv_overlap.
  destruct (Z.ltb_spec0 (bv_unsigned a) (bv_unsigned e0 + bv_unsigned sz0));
  destruct (Z.ltb_spec0 (bv_unsigned e0) (bv_unsigned a + bv_unsigned n)); cbn; try reflexivity; lia.
Qed.

(* [comment removed for export] *)
Theorem gap_exists : forall (h : VmMaps) (nZ : Z),
  0 < nZ <= CBMAX -> nZ mod 4096 = 0 ->
  (forall e, In e (vm_reserved h ++ vm_maps h) -> elo e < ehi e /\ ehi e - elo e <= GRID_W) ->
  Z.of_nat (length (vm_reserved h)) <= GRID_RESV ->
  Z.of_nat (length (vm_maps h)) < GRID_J ->
  live_bytes (vm_maps h) <= GRID_W ->
  CEIL_MIN <= alloc_top h ->
  exists a : word,
    bv_unsigned a mod page_size = 0 /\ 0 < bv_unsigned a /\ bv_unsigned a + nZ <= alloc_top h
    /\ region_free (vm_reserved h ++ vm_maps h) a (Z_to_bv 64 nZ) = true.
Proof.
  intros h nZ HS Hal HE HR HJ HB HT.
  assert (HL : esum (vm_reserved h ++ vm_maps h) / GRID_M + 2 * Z.of_nat (length (vm_reserved h ++ vm_maps h)) < GRID_SLOTS).
  { rewrite esum_app, (esum_live_bytes (vm_maps h)), length_app, Nat2Z.inj_add.
    pose proof (esum_le (vm_reserved h) GRID_W (fun e He => HE e ltac:(apply in_or_app; left; exact He))) as R1.
    pose proof (live_bytes_nonneg0 (vm_maps h)) as P1.
    assert (R0 : 0 <= esum (vm_reserved h)).
    { clear - HE. induction (vm_reserved h) as [|e l IH]; [cbn; lia|]. cbn [esum].
      destruct (HE e ltac:(apply in_or_app; left; left; reflexivity)) as [W _].
      specialize (IH (fun x Hx => HE x ltac:(apply in_app_or in Hx as [Hx|Hx]; apply in_or_app; [left; right; exact Hx| right; exact Hx]))). lia. }
    unfold GRID_W, GRID_RESV, GRID_J, GRID_SLOTS, GRID_M in *.
    change (2^34) with 17179869184 in *. change (2^31) with 2147483648 in *.
    assert (NUM : esum (vm_reserved h) + live_bytes (vm_maps h) <= 9 * 17179869184) by nia.
    assert (Q : (esum (vm_reserved h) + live_bytes (vm_maps h)) / 2147483648 <= 72).
    { apply Z.lt_succ_r. apply Z.div_lt_upper_bound; lia. }
    lia. }
  destruct (grid_gap (vm_reserved h ++ vm_maps h) nZ HS HE HL) as (a & Ha & Hf & Hc & Hfree).
  pose proof grid_floor_pos as FP. unfold CBMAX in HS.
  assert (Ra : 0 <= a < 2^64) by (unfold grid_floor, CEIL_MIN in *; lia).
  assert (Ua : bv_unsigned (Z_to_bv 64 a) = a) by (rewrite Z_to_bv_unsigned; apply bv_wrap_small; unfold bv_modulus; lia).
  assert (Un : bv_unsigned (Z_to_bv 64 nZ) = nZ) by (rewrite Z_to_bv_unsigned; apply bv_wrap_small; unfold bv_modulus; lia).
  exists (Z_to_bv 64 a). rewrite Ua. split; [unfold page_size; exact Ha|]. split; [lia|]. split; [lia|].
  apply region_free_introZ; intros e sz He.
  specialize (Hfree (e, sz) He). unfold elo, ehi in Hfree. cbn in Hfree. rewrite Ua, Un. lia.
Qed.
