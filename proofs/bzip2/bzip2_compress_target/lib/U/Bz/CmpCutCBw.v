(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream BzCState BzArrD BzCLemmas1 CmpMem. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCNumZ CmpCutCB.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {BZP : BzParams}.


(* [comment removed for export] *)
Lemma bz_hdr4_eq : forall b, bz_hdr4 b = bsW (bsW (bsW (bsW b 8 66) 8 90) 8 104) 8 (48 + BLOCKSIZE100K).   (* [comment removed for export] *)
Proof. intros b. reflexivity. Qed.
Lemma bz_magic6_eq : forall b, bz_magic6 b = bsW (bsW (bsW (bsW (bsW (bsW b 8 49) 8 65) 8 89) 8 38) 8 83) 8 89.
Proof. intros b. reflexivity. Qed.
Lemma bz_fin6_eq : forall b, bz_fin6 b = bsW (bsW (bsW (bsW (bsW (bsW b 8 23) 8 114) 8 69) 8 56) 8 80) 8 144.
Proof. intros b. reflexivity. Qed.
Lemma bsPutUInt32_eq : forall b u,
  bsPutUInt32 b u = bsW (bsW (bsW (bsW b 8 (Z.land (Z.shiftr u 24) 255)) 8 (Z.land (Z.shiftr u 16) 255)) 8 (Z.land (Z.shiftr u 8) 255)) 8 (Z.land u 255).
Proof. intros b u. reflexivity. Qed.

(* [comment removed for export] *)
Lemma bsW8_growth : forall b v, bw_ok b -> 0 <= v ->
  bw_ok (bsW b 8 v) /\ (bw_numZ b <= bw_numZ (bsW b 8 v) <= bw_numZ b + 4) /\ 8 <= bw_live (bsW b 8 v) <= 15.
Proof.
  intros b v OK Hv. cps_destruct (bsW8_ok b v OK Hv) as (OK' & NZ & LV). pose proof (bsW_EM b 8 v ltac:(lia)) as EM1.
  revert OK' NZ LV EM1. generalize (bsW b 8 v) as x. intros x OK' NZ LV EM1.
  unfold EM, bits in EM1. cps_destruct OK as (?&?&?). cps_destruct OK' as (?&?&?). split; [unfold bw_ok; lia| lia].
Qed.
(* [comment removed for export] *)
Lemma bsW_growth : forall b n v, bw_ok b -> 1 <= n <= 24 -> 0 <= v ->
  bw_ok (bsW b n v) /\ (bw_numZ b <= bw_numZ (bsW b n v) <= bw_numZ b + 4) /\ n <= bw_live (bsW b n v) <= 7 + n.
Proof.
  intros b n v OK Hn Hv. cps_destruct (bsW_facts b n v OK Hn Hv) as (_ & OK' & LV & NZ). pose proof (bsW_EM b n v ltac:(lia)) as EM1.
  pose proof (Z.mod_pos_bound (bw_live b) 8 ltac:(lia)) as MB.
  revert OK' NZ LV EM1. generalize (bsW b n v) as x. intros x OK' NZ LV EM1.
  unfold EM, bits in EM1. cps_destruct OK as (?&?&?). cps_destruct OK' as (?&?&?). split; [unfold bw_ok; lia| lia].
Qed.
(* [comment removed for export] *)
Lemma bsPutUInt32_growth : forall b u, bw_ok b -> 0 <= u ->
  bw_ok (bsPutUInt32 b u) /\ (bw_numZ b <= bw_numZ (bsPutUInt32 b u) <= bw_numZ b + 8) /\ 8 <= bw_live (bsPutUInt32 b u) <= 15.
Proof.
  intros b u OK Hu. pose proof (bsPutUInt32_EM b u) as EM1. rewrite bsPutUInt32_eq in EM1 |- *.
  cps_destruct (bsW8_growth b (Z.land (Z.shiftr u 24) 255) OK ltac:(apply Z.land_nonneg; right; lia)) as (O1 & N1 & L1).
  revert O1 N1 L1 EM1. generalize (bsW b 8 (Z.land (Z.shiftr u 24) 255)) as x1. intros x1 O1 N1 L1 EM1.
  cps_destruct (bsW8_growth x1 (Z.land (Z.shiftr u 16) 255) O1 ltac:(apply Z.land_nonneg; right; lia)) as (O2 & N2 & L2).
  revert O2 N2 L2 EM1. generalize (bsW x1 8 (Z.land (Z.shiftr u 16) 255)) as x2. intros x2 O2 N2 L2 EM1.
  cps_destruct (bsW8_growth x2 (Z.land (Z.shiftr u 8) 255) O2 ltac:(apply Z.land_nonneg; right; lia)) as (O3 & N3 & L3).
  revert O3 N3 L3 EM1. generalize (bsW x2 8 (Z.land (Z.shiftr u 8) 255)) as x3. intros x3 O3 N3 L3 EM1.
  cps_destruct (bsW8_growth x3 (Z.land u 255) O3 ltac:(apply Z.land_nonneg; right; lia)) as (O4 & N4 & L4).
  revert O4 N4 L4 EM1. generalize (bsW x3 8 (Z.land u 255)) as x4. intros x4 O4 N4 L4 EM1.
  unfold EM, bits in EM1. cps_destruct OK as (?&?&?). split; [exact O4| lia].
Qed.

(* [comment removed for export] *)
Lemma bs_finish_growth : forall b, bw_ok b -> bw_numZ b <= bw_numZ (bs_finish BS_FUEL b) <= bw_numZ b + 4.
Proof.
  intros b OK. cps_destruct (finish_facts BS_FUEL b) as (B1 & B2 & B3). cps_destruct OK as (O1 & O2 & O3). specialize (B3 ltac:(lia)).
  revert B1 B2 B3. generalize (bs_finish BS_FUEL b) as x. intros x B1 B2 B3. unfold bits in B1. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

End ACeilS1.
