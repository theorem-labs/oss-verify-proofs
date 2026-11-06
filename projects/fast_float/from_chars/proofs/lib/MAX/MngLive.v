(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import AllocNodesCfg PlacementCount.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require Import MallocModel MallocInv MallocWfKf MallocWfBound.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngU.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngU MngMeas MngWk MngRz2 MngBudM MngBud.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngU.MngLedger OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngU OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngMeas OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngWk OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngRz2 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngBudM OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngBud.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Lemma ind_split : forall a b c z, a <= b <= c -> ind (inI a c z) = ind (inI a b z) + ind (inI b c z).
Proof.
  intros a b c z H. unfold ind, inI.
  destruct (Z.leb_spec a z); destruct (Z.ltb_spec z c); destruct (Z.ltb_spec z b); destruct (Z.leb_spec b z); cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma lb_isum : forall rs k,
  fold_right (fun rg acc => if rg_live rg then rg_len rg + acc else acc) 0 rs =
  isum (fun _ rg => if rg_live rg then rg_len rg else 0) k rs.
Proof.
  induction rs as [|rg rs IH]; intros k; cbn [fold_right isum]; [reflexivity|].
  rewrite (IH (S k)). destruct (rg_live rg); ring.
Qed.

Section Live.
Variables (HTOP : Z) (FORB : list (Z * Z)) (L : layout) (x : kf) (md : Model).
Hypothesis HL : LINK HTOP FORB L x md.

(* [comment removed for export] *)
#[using="HTOP FORB HL"] Lemma region_pages_Wt : forall r rg, nth_error (kf_regions x) r = Some rg -> rg_live rg = true ->
  forall k, PGSZ * Z.of_nat k <= rg_len rg ->
  PGSZ * Z.of_nat k <= Wt (vm_maps (m_vmmaps md)) (fun z => ind (inI (ly_reg L r) (ly_reg L r + PGSZ * Z.of_nat k) z)).
Proof. LiaFast.lf_pins (fun (HTOP FORB HL : LiaFast.U) => LiaFast.u0).
  intros r rg H1 H2. induction k as [|k IH]; intros Hk.
  - cbn [Z.of_nat]. rewrite Z.mul_0_r. apply Wt_nonneg. intros z; apply ind_range.
  - rewrite Nat2Z.inj_succ in *.
    assert (Hk0 : PGSZ * Z.of_nat k <= rg_len rg) by (unfold PGSZ in *; lia).
    pose proof (IH Hk0) as W0.
    pose proof (page_Wt HTOP FORB L x md HL r rg (PGSZ * Z.of_nat k) H1 H2 ltac:(unfold PGSZ; lia) ltac:(unfold PGSZ in *; lia)
                  ltac:(unfold PGSZ; rewrite Z.mul_comm; apply Z_mod_mult)) as W1.
    rewrite (Wt_ext _ _ (fun z => ind (inI (ly_reg L r) (ly_reg L r + PGSZ * Z.of_nat k) z) +
                               ind (inI (ly_reg L r + PGSZ * Z.of_nat k) (ly_reg L r + PGSZ * Z.of_nat k + PGSZ) z))).
    + rewrite Wt_add. unfold PGSZ in *. lia.
    + intros p z _ _. replace (ly_reg L r + PGSZ * Z.succ (Z.of_nat k)) with (ly_reg L r + PGSZ * Z.of_nat k + PGSZ) by (unfold PGSZ; lia).
      apply ind_split. unfold PGSZ. lia.
Qed.

(* [comment removed for export] *)
#[using="HTOP FORB HL"] Lemma region_Wt : forall r rg, nth_error (kf_regions x) r = Some rg -> rg_live rg = true ->
  rg_len rg <= Wt (vm_maps (m_vmmaps md)) (fun z => ind (inI (ly_reg L r) (ly_reg L r + rg_len rg) z)).
Proof. LiaFast.lf_pins (fun (HTOP FORB HL : LiaFast.U) => LiaFast.u0).
  intros r rg H1 H2. destruct (lk_rgeo _ _ _ _ _ HL r rg H1 H2) as (_ & _ & G3 & G4 & _).
  assert (E : rg_len rg = PGSZ * Z.of_nat (Z.to_nat (rg_len rg / PGSZ))).
  { rewrite Z2Nat.id by (apply Z.div_pos; unfold PGSZ in *; lia). pose proof (Z.div_mod (rg_len rg) PGSZ ltac:(unfold PGSZ; lia)) as Q.
    rewrite G4, Z.add_0_r in Q. exact Q. }
  pose proof (region_pages_Wt r rg H1 H2 (Z.to_nat (rg_len rg / PGSZ)) ltac:(rewrite <- E; lia)) as W.
  rewrite <- E in W. exact W.
Qed.

(* [comment removed for export] *)
#[using="HTOP FORB L HL"] Theorem live_le_maps :
  isum (fun _ rg => if rg_live rg then rg_len rg else 0) 0 (kf_regions x) <= Wt (vm_maps (m_vmmaps md)) (fun _ => 1).
Proof. LiaFast.lf_pins (fun (HTOP FORB L HL : LiaFast.U) => LiaFast.u0).
  set (h := fun (r : nat) (rg : region) (z : Z) => if rg_live rg then ind (inI (ly_reg L r) (ly_reg L r + rg_len rg) z) else 0).
  assert (A : isum (fun _ rg => if rg_live rg then rg_len rg else 0) 0 (kf_regions x) <=
              isum (fun r rg => Wt (vm_maps (m_vmmaps md)) (h r rg)) 0 (kf_regions x)).
  { apply isum_mono'. intros r rg E. cbn [Nat.add]. unfold h. destruct (rg_live rg) eqn:Hl.
    - exact (region_Wt r rg E Hl).
    - rewrite Wt_0. lia. }
  rewrite <- Wt_isum in A. eapply Z.le_trans; [exact A|]. apply Wt_mono. intros z. apply isum_le1.
  - intros r rg E. cbn [Nat.add]. unfold h. destruct (rg_live rg); [apply ind_range | lia].
  - intros r1 r2 rg1 rg2 Hne E1 E2. cbn [Nat.add]. unfold h.
    destruct (rg_live rg1) eqn:L1; [|left; reflexivity]. destruct (rg_live rg2) eqn:L2; [|right; reflexivity].
    destruct (inI (ly_reg L r1) (ly_reg L r1 + rg_len rg1) z) eqn:I1; [|left; reflexivity]. right.
    destruct (inI (ly_reg L r2) (ly_reg L r2 + rg_len rg2) z) eqn:I2; [|reflexivity].
    apply inI_true in I1. apply inI_true in I2. exfalso. apply Hne. exact (two_regions HTOP FORB L x md HL r1 r2 rg1 rg2 z E1 E2 L1 L2 I1 I2).
Qed.

(* [comment removed for export] *)
#[using="HTOP FORB L HL"] Lemma rtot_small : Um md <= 2 ^ 30 -> rtot (kf_regions x) <= 2 ^ 31.
Proof. LiaFast.lf_pins (fun (HTOP FORB L HL : LiaFast.U) => LiaFast.u0).
  intros HU. pose proof (opened_backed HTOP FORB L x md HL) as OB. pose proof (backed_le HTOP FORB L x md HL) as BL.
  pose proof (backing_le_Um md) as BU. pose proof (lk_k1 _ _ _ _ _ HL) as K1. pose proof (lk_k2 _ _ _ _ _ HL) as K2.
  pose proof (rcnt_nonneg (kf_regions x)) as C0. pose proof (ropen_nonneg (kf_regions x)) as O0.
  set (c := rcnt (kf_regions x)) in *. set (o := ropen (kf_regions x)) in *.
  assert (Hc : c <= 18) by (apply (rcnt_small o c C0 O0); [lia | rewrite <- K1; exact K2]).
  rewrite K1. assert (P : 2 ^ c <= 2 ^ 18) by (apply Z.pow_le_mono_r; lia). unfold PGSZ. lia.
Qed.

(* [comment removed for export] *)
#[using="HTOP FORB L HL"] Theorem live_small : Um md <= 2 ^ 30 ->
  isum (fun _ rg => if rg_live rg then rg_len rg else 0) 0 (kf_regions x) <= 2 ^ 39.
Proof. LiaFast.lf_pins (fun (HTOP FORB L HL : LiaFast.U) => LiaFast.u0).
  intros HU. pose proof live_le_maps as A. pose proof (ledger_bound HTOP FORB L x md HL) as LB.
  assert (E : ledger_size (vm_maps (m_vmmaps md)) = Wt (vm_maps (m_vmmaps md)) (fun _ => 1)).
  { rewrite <- live_bytes_Wt. clear. induction (vm_maps (m_vmmaps md)) as [|[a s] l IH]; [reflexivity|]. cbn. rewrite IH. reflexivity. }
  pose proof (backed_le HTOP FORB L x md HL) as BL. pose proof (backing_le_Um md) as BU. pose proof (rtot_small HU) as RT.
  unfold PGSZ in *. lia.
Qed.

End Live.

(* [comment removed for export] *)
Theorem bounded_of_link : forall HTOP FORB L s md, WF s -> LINK HTOP FORB L (kf_of s) md -> Um md <= 2 ^ 30 -> bounded s.
Proof.
  intros HTOP FORB L s md HW HL HU. apply (bounded_of_live s HW).
  pose proof (live_small HTOP FORB L (kf_of s) md HL HU) as T.
  unfold MallocInv.live_bytes. rewrite (lb_isum _ 0%nat). unfold kf_of, kf_regions in T. cbn [fst] in T. lia.
Qed.

Corollary usage_small_of_link : forall HTOP FORB L s md, WF s -> LINK HTOP FORB L (kf_of s) md -> Um md <= 2 ^ 30 ->
  forall c, 0 <= c < 48 -> usage_of s c < 2 ^ 40.
Proof. intros HTOP FORB L s md HW HL HU c Hc. destruct (bounded_of_link HTOP FORB L s md HW HL HU) as (B & _). apply B. Qed.
