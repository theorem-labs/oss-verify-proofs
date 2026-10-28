(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzArrD BzCState. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCSortM BzCBlock BzCLemmasMs.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams BzParamsLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section ACeilS1. Context {BZP : BzParams}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Points.
  Variable e : est.
  Definition bp_n : Z := e_nblock e.
  Definition bp_a1 : zarr := e_arr1 e.
  Definition bp_a2 : zarr := e_arr2 e.
  Definition bp_ft : zarr := e_ftab e.
  (* [comment removed for export] *)
  Definition bp_qoff : Z := let i := bp_n + BZ_N_OVERSHOOT in if Z.land i 1 =? 0 then i else i + 1.
  Definition bp_budget0 : Z := bp_n * budget_q.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition bp_ft0 : zarr := ms_ftab_zero 65537%nat bp_ft 65536.
  Definition bp_j0 : Z := Z.shiftl (rd8 bp_a2 0) 8.
  (* [comment removed for export] *)
  Definition bp_r1 := ms_radix1 (Z.to_nat bp_n) bp_a2 bp_ft0 bp_qoff (bp_n - 1) bp_j0.
  Definition bp_a2r : zarr := fst (fst bp_r1).
  Definition bp_ft1 : zarr := snd (fst bp_r1).
  (* [comment removed for export] *)
  Definition bp_a2o : zarr := ms_overshoot 34%nat bp_a2r bp_qoff bp_n 0.
  (* [comment removed for export] *)
  Definition bp_ft3 : zarr := ms_accum 65536%nat bp_ft1 1.
  Definition bp_s0 : Z := Z.shiftl (rd8 bp_a2o 0) 8.
  (* [comment removed for export] *)
  Definition bp_r4 := ms_radix2 (Z.to_nat bp_n) bp_a1 bp_a2o bp_ft3 (bp_n - 1) bp_s0.
  Definition bp_a1r : zarr := fst (fst bp_r4).
  Definition bp_ft4 : zarr := snd (fst bp_r4).
  (* [comment removed for export] *)
  Definition bp_bd5 : zarr := fst (ms_ro_init 256%nat znew znew 0).
  Definition bp_ro5 : zarr := snd (ms_ro_init 256%nat znew znew 0).
  Definition bp_ro6 : zarr := ms_shell 8%nat bp_ro5 bp_ft4 364.
  (* [comment removed for export] *)
  Definition bp_S0 : mss := MSS bp_a1r bp_a2o bp_ft4 bp_bd5 znew znew bp_budget0 0 (MQL znew znew znew znew znew znew) false.
  Definition bp_ms : mss := ms_bigs 256%nat bp_ro6 bp_qoff bp_n 0 bp_S0.
End Points.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition bsA_accum (e : est) : Prop :=
  forall v, 0 <= v <= 65536 -> 0 <= zget (bp_ft3 e) v <= bp_n e.
(* [comment removed for export] *)
Definition bsA_radix2 (e : est) : Prop :=
  r2ok (bp_n e) (Z.to_nat (bp_n e)) (bp_a1 e) (bp_a2o e) (bp_ft3 e) (bp_n e - 1) (bp_s0 e).
(* [comment removed for export] *)
Definition bsA_mono (e : est) : Prop :=
  forall b, 0 <= b < 256 -> 0 <= zget (bp_ft4 e) (b * 256) <= zget (bp_ft4 e) ((b + 1) * 256) /\ zget (bp_ft4 e) ((b + 1) * 256) <= bp_n e.

(* [comment removed for export] *)
Definition bs_facts (e : est) : Prop :=
  bsA_accum e /\ bsA_radix2 e /\ bsA_mono e.

End ACeilS1.
