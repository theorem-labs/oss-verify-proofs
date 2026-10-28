(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjNumber SjNumU.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Sj_num_kitu Sj_num_kitn Sj_num_pm_defs Sj_num_pm_round.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ solve_load_base | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].
Local Ltac nnorm ::= nnorm_u.

Section PMUTI.
  Variable E : pmuenv.
  Hypothesis OK : pmu_ok E.
  Notation X := (p_X E).
  Notation IP := (p_IP E).
  Notation IL := (p_IL E).
  Notation FPT := (p_FPT E).
  Notation FL := (p_FL E).

  Lemma pm_ti_de8 : forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa4 xa6 xa7 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm len v16,
    PMUINV E mm len 769 v16 ->
    evt usegs (pmu_post E) (PM E 0x5db34 xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 (Z_to_bv 64 (X + 504)) xa4 (Z_to_bv 64 (18446744073709551615 - X)) xa6 xa7 (Z_to_bv 64 X) xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros until v16. intros INV. pose proof INV as INV0. pm_open INV0. pm_env OK.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5de0c%Z => first [ eapply (pm_exit E OK) with (dg := 769%Z); [exact INV | lia | lia] | fail 100 "cut" pc ]
      | 0x5db38%Z => first [ eapply evt_eq; [| eapply (pm_roundA E OK)]; [num_st_eq | exact INV] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_ti_Z1d : forall (f : nat) (p : Z) xra xt0 xt1 xt2 xs0 xs1 xa2 xa7 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm len v16,
    PMUINV E mm len 769 v16 ->
    FPT <> 0%Z ->
    (FPT <= p < FPT + FL)%Z ->
    (FPT + FL - p <= Z.of_nat f)%Z ->
    evt usegs (pmu_post E) (PM E 0x5db20 xra xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 48) (Z_to_bv 64 p) xa2 (Z_to_bv 64 (X + 504)) (Z_to_bv 64 (FPT + FL)) (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 18446744073709551615) xa7 (Z_to_bv 64 X) xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros f. induction f as [|f IH]; intros until v16; intros INV HF Hp Hf; [exfalso; lia|].
    pose proof INV as INV0. pm_open INV0. pm_env OK. destruct SPN4 as [?|SPN4]; [exfalso; lia|].
    nstep.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5de48%Z => u_trap pc
      | 0x5db38%Z => first [ eapply evt_eq; [| eapply (pm_roundA E OK)]; [num_st_eq | exact INV] | fail 100 "cut" pc ]
      | 0x5db34%Z => first [ eapply evt_eq; [| eapply pm_ti_de8]; [num_st_eq | exact INV] | fail 100 "cut" pc ]
      | 0x5db20%Z => first [ eapply evt_eq; [| eapply (IH (p + 1)%Z)]; [num_st_eq | exact INV | exact HF | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_ti_dc4 : forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa2 xa7 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm len v16 p,
    PMUINV E mm len 769 v16 ->
    FPT <> 0%Z ->
    (FPT <= p <= FPT + FL)%Z ->
    evt usegs (pmu_post E) (PM E 0x5db10 xra xt0 xt1 xt2 xs0 xs1 xa0 (Z_to_bv 64 p) xa2 (Z_to_bv 64 (X + 504)) (Z_to_bv 64 FPT) (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 FL) xa7 (Z_to_bv 64 X) xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros until p. intros INV HF Hp. pose proof INV as INV0. pm_open INV0. pm_env OK. destruct SPN4 as [?|SPN4]; [exfalso; lia|].
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5de48%Z => u_trap pc
      | 0x5db34%Z => first [ eapply evt_eq; [| eapply pm_ti_de8]; [num_st_eq | exact INV] | fail 100 "cut" pc ]
      | 0x5db20%Z => first [ eapply evt_eq; [| eapply (pm_ti_Z1d (Z.to_nat (FPT + FL - p)) p)]; [num_st_eq | exact INV | exact HF | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_ti_Z8d : forall (f : nat) (p : Z) xra xs0 xs1 xa0 xa2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm len v16,
    PMUINV E mm len 769 v16 ->
    FPT <> 0%Z ->
    (FPT <= p)%Z ->
    (p + 8 <= FPT + FL)%Z ->
    (FPT + FL - p <= Z.of_nat f)%Z ->
    evt usegs (pmu_post E) (PM E 0x5daa4 xra (Z_to_bv 64 3472328296227680304) (Z_to_bv 64 7) (Z_to_bv 64 (FPT + FL - p)) xs0 xs1 xa0 (Z_to_bv 64 p) xa2 (Z_to_bv 64 (X + 504)) (Z_to_bv 64 FPT) (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 FL) (Z_to_bv 64 18446744073709551608) (Z_to_bv 64 X) xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros f. induction f as [|f IH]; intros until v16; intros INV HF Hp Hp8 Hf; [exfalso; lia|].
    pose proof INV as INV0. pm_open INV0. pm_env OK. destruct SPN4 as [?|SPN4]; [exfalso; lia|].
    nstep.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5de48%Z => u_trap pc
      | 0x5db38%Z => first [ eapply evt_eq; [| eapply (pm_roundA E OK)]; [num_st_eq | exact INV] | fail 100 "cut" pc ]
      | 0x5db10%Z => first [ eapply evt_eq; [| eapply (pm_ti_dc4)]; [num_st_eq | exact INV | exact HF | lia] | fail 100 "cut" pc ]
      | 0x5daa4%Z => first [ eapply evt_eq; [| eapply (IH (p + 8)%Z)]; [num_st_eq | exact INV | exact HF | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_ti_d20 : forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa2 xa6 xa7 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm len v16,
    PMUINV E mm len 769 v16 ->
    FPT <> 0%Z ->
    evt usegs (pmu_post E) (PM E 0x5da6c xra xt0 xt1 xt2 xs0 xs1 xa0 (Z_to_bv 64 (X + -72)) xa2 (Z_to_bv 64 (X + 504)) (Z_to_bv 64 FPT) (Z_to_bv 64 (18446744073709551615 - X)) xa6 xa7 (Z_to_bv 64 X) xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros until v16. intros INV HF. pose proof INV as INV0. pm_open INV0. pm_env OK. destruct SPN4 as [?|SPN4]; [exfalso; lia|].
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5de48%Z => u_trap pc
      | 0x5db10%Z => first [ eapply evt_eq; [| eapply (pm_ti_dc4)]; [num_st_eq | exact INV | exact HF | lia] | fail 100 "cut" pc ]
      | 0x5daa4%Z => first [ eapply evt_eq; [| eapply (pm_ti_Z8d (Z.to_nat FL) FPT)]; [num_st_eq | exact INV | exact HF | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_ti_Z1c : forall (f : nat) (p : Z) xra xt0 xt1 xt2 xs0 xs1 xa2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm len v16,
    PMUINV E mm len 769 v16 ->
    (IP <= p < IP + IL)%Z ->
    (IP + IL - p <= Z.of_nat f)%Z ->
    evt usegs (pmu_post E) (PM E 0x5da24 xra xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 48) (Z_to_bv 64 (X + -72)) xa2 (Z_to_bv 64 (X + 504)) (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (IP + IL)) (Z_to_bv 64 p) (Z_to_bv 64 X) xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros f. induction f as [|f IH]; intros until v16; intros INV Hp Hf; [exfalso; lia|].
    pose proof INV as INV0. pm_open INV0. pm_env OK.
    nstep.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5de48%Z => u_trap pc
      | 0x5da6c%Z => first [ eapply evt_eq; [| eapply pm_ti_d20]; [num_st_eq | exact INV | lia] | fail 100 "cut" pc ]
      | 0x5db34%Z => first [ eapply evt_eq; [| eapply pm_ti_de8]; [num_st_eq | exact INV] | fail 100 "cut" pc ]
      | 0x5da24%Z => first [ eapply evt_eq; [| eapply (IH (p + 1)%Z)]; [num_st_eq | exact INV | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_ti_Z8c : forall (f : nat) (p : Z) xra xt2 xs0 xs1 xa0 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm len v16,
    PMUINV E mm len 769 v16 ->
    (IP <= p)%Z ->
    (p + 8 <= IP + IL)%Z ->
    (IP + IL - p <= Z.of_nat f)%Z ->
    evt usegs (pmu_post E) (PM E 0x5d9ac xra (Z_to_bv 64 3472328296227680304) (Z_to_bv 64 7) xt2 xs0 xs1 xa0 (Z_to_bv 64 (X + -72)) (Z_to_bv 64 (IP + IL - p)) (Z_to_bv 64 (X + 504)) (Z_to_bv 64 18446744073709551608) (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (IP + IL)) (Z_to_bv 64 p) (Z_to_bv 64 X) xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros f. induction f as [|f IH]; intros until v16; intros INV Hp Hp8 Hf; [exfalso; lia|].
    pose proof INV as INV0. pm_open INV0. pm_env OK.
    nstep.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5de48%Z => u_trap pc
      | 0x5da6c%Z => first [ eapply evt_eq; [| eapply pm_ti_d20]; [num_st_eq | exact INV | lia] | fail 100 "cut" pc ]
      | 0x5db34%Z => first [ eapply evt_eq; [| eapply pm_ti_de8]; [num_st_eq | exact INV] | fail 100 "cut" pc ]
      | 0x5da24%Z => first [ eapply evt_eq; [| eapply (pm_ti_Z1c (Z.to_nat (IP + IL - (p + 8))) (p + 8)%Z)]; [num_st_eq | exact INV | lia | lia] | fail 100 "cut" pc ]
      | 0x5d9ac%Z => first [ eapply evt_eq; [| eapply (IH (p + 8)%Z)]; [num_st_eq | exact INV | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_ti_c3c : forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa2 xa4 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm len v16 p,
    PMUINV E mm len 769 v16 ->
    (IP <= p <= IP + IL)%Z ->
    evt usegs (pmu_post E) (PM E 0x5d988 xra xt0 xt1 xt2 xs0 xs1 xa0 (Z_to_bv 64 (X + -72)) xa2 (Z_to_bv 64 (X + 504)) xa4 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (IP + IL)) (Z_to_bv 64 p) (Z_to_bv 64 X) xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros until p. intros INV Hp. pose proof INV as INV0. pm_open INV0. pm_env OK.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5de48%Z => u_trap pc
      | 0x5da6c%Z => first [ eapply evt_eq; [| eapply pm_ti_d20]; [num_st_eq | exact INV | lia] | fail 100 "cut" pc ]
      | 0x5db34%Z => first [ eapply evt_eq; [| eapply pm_ti_de8]; [num_st_eq | exact INV] | fail 100 "cut" pc ]
      | 0x5da24%Z => first [ eapply evt_eq; [| eapply (pm_ti_Z1c (Z.to_nat (IP + IL - p)) p)]; [num_st_eq | exact INV | lia | lia] | fail 100 "cut" pc ]
      | 0x5d9ac%Z => first [ eapply evt_eq; [| eapply (pm_ti_Z8c (Z.to_nat (IP + IL - p)) p)]; [num_st_eq | exact INV | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_ti_c24 : forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa4 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm len v16 p,
    PMUINV E mm len 769 v16 ->
    (IP <= p <= IP + IL)%Z ->
    (len <= 61)%Z ->
    evt usegs (pmu_post E) (PM E 0x5d970 xra xt0 xt1 xt2 xs0 xs1 xa0 (Z_to_bv 64 (X + -72)) (Z_to_bv 64 len) (Z_to_bv 64 (X + 504)) xa4 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (IP + IL)) (Z_to_bv 64 p) (Z_to_bv 64 X) xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros until p. intros INV Hp Hl. pm_open INV. pm_env OK. assert (DV : IsData xs8) by exact I.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5de48%Z => u_trap pc
      | 0x5d988%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINV E m1 (len + 1) 769 v16) by pm_close); eapply evt_eq; [| eapply pm_ti_c3c]; [num_st_eq | exact INV1 | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_ti_c18 : forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa4 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm len v16 p,
    PMUINV E mm len 769 v16 ->
    (IP <= p <= IP + IL)%Z ->
    evt usegs (pmu_post E) (PM E 0x5d964 xra xt0 xt1 xt2 xs0 xs1 xa0 (Z_to_bv 64 (X + -72)) (Z_to_bv 64 len) (Z_to_bv 64 (X + 504)) xa4 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (IP + IL)) (Z_to_bv 64 p) (Z_to_bv 64 X) xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros until p. intros INV Hp. pose proof INV as INV0. pm_open INV0. pm_env OK.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5d988%Z => first [ eapply evt_eq; [| eapply pm_ti_c3c]; [num_st_eq | exact INV | lia] | fail 100 "cut" pc ]
      | 0x5d970%Z => first [ eapply evt_eq; [| eapply pm_ti_c24]; [num_st_eq | exact INV | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_ti_CA : forall (f : nat) (j : Z) xra xt2 xs0 xs1 xa0 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm len v16 p,
    PMUINV E mm len 769 v16 ->
    (IP <= p <= IP + IL)%Z ->
    (0 <= j <= len - 1)%Z ->
    (len - 1 - j <= Z.of_nat f)%Z ->
    evt usegs (pmu_post E) (PM E 0x5d788 xra (Z_to_bv 64 (18446744073709551112 + 8 * j)) (Z_to_bv 64 (X + 8 + 8 * j)) xt2 xs0 xs1 xa0 (Z_to_bv 64 (X + -72)) (Z_to_bv 64 len) (Z_to_bv 64 (X + 504)) (Z_to_bv 64 (len - 1 - j)) (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (IP + IL)) (Z_to_bv 64 p) (Z_to_bv 64 X) xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros f. induction f as [|f IH]; intros until p; intros INV Hp Hj Hf.
    - pose proof INV as INV0. pm_open INV0. pm_env OK. nstep.
      uwalk ltac:(fun pc => lazymatch pc with
      | 0x5de48%Z => u_trap pc
      | 0x5d964%Z => first [ eapply evt_eq; [| eapply pm_ti_c18]; [num_st_eq | exact INV | lia] | fail 100 "cut" pc ]
      end).
    - pose proof INV as INV0. pm_open INV0. pm_env OK. nstep.
      uwalk ltac:(fun pc => lazymatch pc with
      | 0x5de48%Z => u_trap pc
      | 0x5d964%Z => first [ eapply evt_eq; [| eapply pm_ti_c18]; [num_st_eq | exact INV | lia] | fail 100 "cut" pc ]
      | 0x5d988%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINV E m1 len 769 v16) by pm_close); eapply evt_eq; [| eapply pm_ti_c3c]; [num_st_eq | exact INV1 | lia] | fail 100 "cut" pc ]
      | 0x5d788%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINV E m1 len 769 v16) by pm_close); eapply evt_eq; [| eapply (IH (j + 1)%Z)]; [num_st_eq | exact INV1 | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_ti_a14 : forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa2 xa4 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm len v16 p,
    PMUINV E mm len 769 v16 ->
    (IP <= p <= IP + IL)%Z ->
    evt usegs (pmu_post E) (PM E 0x5d760 xra xt0 xt1 xt2 xs0 xs1 xa0 (Z_to_bv 64 (X + -72)) xa2 (Z_to_bv 64 (X + 504)) xa4 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (IP + IL)) (Z_to_bv 64 p) (Z_to_bv 64 X) xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros until p. intros INV Hp. pose proof INV as INV0. pm_open INV0. pm_env OK. assert (DV : IsData xs8) by exact I.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5de48%Z => u_trap pc
      | 0x5d988%Z => first [ first [ eapply evt_eq; [| eapply pm_ti_c3c]; [num_st_eq | exact INV | lia] | num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINV E m1 len 769 v16) by pm_close); eapply evt_eq; [| eapply pm_ti_c3c]; [num_st_eq | exact INV1 | lia] ] | fail 100 "cut" pc ]
      | 0x5d970%Z => first [ eapply evt_eq; [| eapply pm_ti_c24]; [num_st_eq | exact INV | lia | lia] | fail 100 "cut" pc ]
      | 0x5d788%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINV E m1 len 769 v16) by pm_close); eapply evt_eq; [| eapply (pm_ti_CA (Z.to_nat len) 0%Z)]; [num_st_eq | exact INV1 | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_ti_9f0 : forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa4 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm len v16 p,
    PMUINV E mm len 769 v16 ->
    (IP <= p <= IP + IL)%Z ->
    evt usegs (pmu_post E) (PM E 0x5d73c xra xt0 xt1 xt2 xs0 xs1 xa0 (Z_to_bv 64 (X + -72)) (Z_to_bv 64 len) (Z_to_bv 64 (X + 504)) xa4 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (IP + IL)) (Z_to_bv 64 p) (Z_to_bv 64 X) xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros until p. intros INV Hp. pose proof INV as INV0. pm_open INV0. pm_env OK. assert (DC : IsData xa4) by exact I.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5de48%Z => u_trap pc
      | 0x5d760%Z => first [ first [ eapply evt_eq; [| eapply pm_ti_a14]; [num_st_eq | exact INV | lia] | num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINV E m1 (len + 1) 769 v16) by pm_close); eapply evt_eq; [| eapply pm_ti_a14]; [num_st_eq | exact INV1 | lia] ] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_ti_SM : forall (f : nat) (i : Z) xra xt1 xs0 xs1 xa0 xa4 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt4 xt5 xt6 mm len v16 p,
    PMUINV E mm len 769 v16 ->
    (IP <= p <= IP + IL)%Z ->
    (0 <= i < len)%Z ->
    (len - i <= Z.of_nat f)%Z ->
    evt usegs (pmu_post E) (PM E 0x5d710 xra (Z_to_bv 64 (63 - i)) xt1 (Z_to_bv 64 (X + 8 * len)) xs0 xs1 xa0 (Z_to_bv 64 (X + -72)) (Z_to_bv 64 len) (Z_to_bv 64 (X + 504)) xa4 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (IP + IL)) (Z_to_bv 64 p) (Z_to_bv 64 X) xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 (X + 8 * i)) xt4 xt5 xt6 mm).
  Proof using OK.
    intros f. induction f as [|f IH]; intros until p; intros INV Hp Hi Hf; [exfalso; lia|].
    pose proof INV as INV0. pm_open INV0. pm_env OK. assert (DC : IsData xa4) by exact I. assert (DY : IsData xt1) by exact I.
    nstep.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5de48%Z => u_trap pc
      | 0x5d73c%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINV E m1 len 769 v16) by pm_close); eapply evt_eq; [| eapply pm_ti_9f0]; [num_st_eq | exact INV1 | lia] | fail 100 "cut" pc ]
      | 0x5d710%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINV E m1 len 769 v16) by pm_close); eapply evt_eq; [| eapply (IH (i + 1)%Z)]; [num_st_eq | exact INV1 | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_ti : forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm len v16 p cn,
    PMUINV E mm len 769 v16 ->
    (IP <= p <= IP + IL)%Z ->
    (0 <= cn <= 19)%Z ->
    evt usegs (pmu_post E) (PM E 0x5d6c8 xra xt0 xt1 xt2 xs0 xs1 xa0 (Z_to_bv 64 (X + -72)) xa2 (Z_to_bv 64 (X + 504)) (Z_to_bv 64 PMU_POW10) (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (IP + IL)) (Z_to_bv 64 p) (Z_to_bv 64 X) xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 (Z_to_bv 64 cn) xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros until cn. intros INV Hp Hc. pose proof INV as INV0. pm_open INV0. pm_env OK. unfold PMU_POW10.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5de48%Z => u_trap pc
      | 0x5d760%Z => first [ eapply evt_eq; [| eapply pm_ti_a14]; [num_st_eq | exact INV | lia] | fail 100 "cut" pc ]
      | 0x5d710%Z => first [ eapply evt_eq; [| eapply (pm_ti_SM (Z.to_nat len) 0%Z) with (len := len)]; [num_st_eq | exact INV | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.
End PMUTI.
