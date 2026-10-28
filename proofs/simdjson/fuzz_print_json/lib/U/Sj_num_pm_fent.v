(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjNumber SjNumU.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Sj_num_kitu Sj_num_kitn Sj_num_pm_defs Sj_num_pm_round Sj_num_pm_tf Sj_num_pm_frac.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ solve_load_base | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].
Local Ltac nnorm ::= nnorm_u.

Section PMUFENT.
  Variable E : pmuenv.
  Hypothesis OK : pmu_ok E.
  Notation X := (p_X E).
  Notation IP := (p_IP E).
  Notation IL := (p_IL E).
  Notation FPT := (p_FPT E).
  Notation FL := (p_FL E).

  Lemma pm_fe_61c : forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa7 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm len D v16 p,
    PMUINV E mm len D v16 ->
    FPT <> 0%Z ->
    (0 <= D <= 769)%Z ->
    (19 * len <= 2 * D + 38)%Z ->
    (FPT <= p <= FPT + FL)%Z ->
    evt usegs (pmu_post E) (PM E 0x5d678 xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 (Z_to_bv 64 769) (Z_to_bv 64 (X + 504)) (Z_to_bv 64 116824) (Z_to_bv 64 p) (Z_to_bv 64 (FPT + FL)) xa7 (Z_to_bv 64 X) xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros until p. intros INV HF HD HB Hp. pose proof INV as INV0. pm_open INV0. pm_env OK. destruct SPN4 as [?|SPN4]; [exfalso; lia|].
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5e11c%Z => first [ eapply (pm_exit E OK) with (dg := D); [exact INV | lia | lia] | fail 100 "cut" pc ]
      | 0x5d700%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINVg E m1 len D (Z_to_bv 64 100000000) (D < PMU_NORM_DG)%Z) by (pm_close_with ltac:(exact NB))); eapply evt_eq; [| eapply (fr_body E OK (Z.to_nat (FPT + FL - p)) (fr_head E OK (Z.to_nat (FPT + FL - p)))) with (len := len) (D := D) (p := p)]; [num_st_eq | exact INV1 | exact HF | lia | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_fe_Z1b : forall (f : nat) (p : Z) xra xt0 xt1 xt2 xs0 xs1 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm len D v16,
    PMUINV E mm len D v16 ->
    FPT <> 0%Z ->
    (0 <= D <= 769)%Z ->
    (19 * len <= 2 * D + 38)%Z ->
    (FPT <= p < FPT + FL)%Z ->
    (FPT + FL - p <= Z.of_nat f)%Z ->
    evt usegs (pmu_post E) (PM E 0x5dc58 xra xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 (FPT + FL)) (Z_to_bv 64 48) (Z_to_bv 64 769) (Z_to_bv 64 (X + 504)) (Z_to_bv 64 116824) (Z_to_bv 64 p) (Z_to_bv 64 (FPT + FL)) (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 X) xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros f. induction f as [|f IH]; intros until v16; intros INV HF HD HB Hp Hf; [exfalso; lia|].
    pose proof INV as INV0. pm_open INV0. pm_env OK. destruct SPN4 as [?|SPN4]; [exfalso; lia|].
    nstep.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5e158%Z => u_trap pc
      | 0x5d678%Z => first [ first [ eapply evt_eq; [| eapply pm_fe_61c with (p := p)]; [num_st_eq | exact INV | exact HF | lia | lia | lia] | eapply evt_eq; [| eapply pm_fe_61c with (p := (FPT + FL)%Z)]; [num_st_eq | exact INV | exact HF | lia | lia | lia] ] | fail 100 "cut" pc ]
      | 0x5dc58%Z => first [ eapply evt_eq; [| eapply (IH (p + 1)%Z)]; [num_st_eq | exact INV | exact HF | lia | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_fe_bec : forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm len D v16 p,
    PMUINV E mm len D v16 ->
    FPT <> 0%Z ->
    (0 <= D <= 769)%Z ->
    (19 * len <= 2 * D + 38)%Z ->
    (FPT <= p < FPT + FL)%Z ->
    evt usegs (pmu_post E) (PM E 0x5dc48 xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 (Z_to_bv 64 769) (Z_to_bv 64 (X + 504)) (Z_to_bv 64 116824) (Z_to_bv 64 p) (Z_to_bv 64 (FPT + FL)) (Z_to_bv 64 p) (Z_to_bv 64 X) xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros until p. intros INV HF HD HB Hp. pose proof INV as INV0. pm_open INV0. pm_env OK. destruct SPN4 as [?|SPN4]; [exfalso; lia|].
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5e158%Z => u_trap pc
      | 0x5dc58%Z => first [ eapply evt_eq; [| eapply (pm_fe_Z1b (Z.to_nat (FPT + FL - p)) p)]; [num_st_eq | exact INV | exact HF | lia | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_fe_Z8b : forall (f : nat) (p : Z) xra xs0 xs1 xa0 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm len D v16,
    PMUINV E mm len D v16 ->
    FPT <> 0%Z ->
    (0 <= D <= 769)%Z ->
    (19 * len <= 2 * D + 38)%Z ->
    (FPT <= p)%Z ->
    (p + 8 <= FPT + FL)%Z ->
    (FPT + FL - p <= Z.of_nat f)%Z ->
    evt usegs (pmu_post E) (PM E 0x5dae0 xra (Z_to_bv 64 8) (Z_to_bv 64 3472328296227680304) (Z_to_bv 64 7) xs0 xs1 xa0 (Z_to_bv 64 (FPT + FL - p)) (Z_to_bv 64 769) (Z_to_bv 64 (X + 504)) (Z_to_bv 64 116824) (Z_to_bv 64 p) (Z_to_bv 64 (FPT + FL)) (Z_to_bv 64 p) (Z_to_bv 64 X) xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros f. induction f as [|f IH]; intros until v16; intros INV HF HD HB Hp Hp8 Hf; [exfalso; lia|].
    pose proof INV as INV0. pm_open INV0. pm_env OK. destruct SPN4 as [?|SPN4]; [exfalso; lia|].
    nstep.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5e158%Z => u_trap pc
      | 0x5e11c%Z => first [ eapply (pm_exit E OK) with (dg := D); [exact INV | lia | lia] | fail 100 "cut" pc ]
      | 0x5dc48%Z => first [ first [ eapply evt_eq; [| eapply pm_fe_bec with (p := p)]; [num_st_eq | exact INV | exact HF | lia | lia | lia] | eapply evt_eq; [| eapply pm_fe_bec with (p := (p + 8)%Z)]; [num_st_eq | exact INV | exact HF | lia | lia | lia] ] | fail 100 "cut" pc ]
      | 0x5dae0%Z => first [ eapply evt_eq; [| eapply (IH (p + 8)%Z)]; [num_st_eq | exact INV | exact HF | lia | lia | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_fent : forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa5 xa6 xa7 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm len D v16,
    PMUINV E mm len D v16 ->
    (0 <= D <= 769)%Z ->
    (19 * len <= 2 * D + 38)%Z ->
    evt usegs (pmu_post E) (PM E 0x5d658 xra xt0 xt1 xt2 xs0 xs1 xa0 (Z_to_bv 64 (X + -72)) (Z_to_bv 64 769) (Z_to_bv 64 (X + 504)) (Z_to_bv 64 116824) xa5 xa6 xa7 (Z_to_bv 64 X) xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros until v16. intros INV HD HB. pose proof INV as INV0. pm_open INV0. pm_env OK.
    nstep. zstep.
    if_cases KF; zify_cond KF.
    { uwalk ltac:(fun pc => lazymatch pc with
      | 0x5e11c%Z => first [ eapply (pm_exit E OK) with (dg := D); [exact INV | lia | lia] | fail 100 "cut" pc ]
      end). }
    destruct SPN4 as [?|SPN4]; [exfalso; lia|].
    assert (HF : FPT <> 0%Z) by lia.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5e158%Z => u_trap pc
      | 0x5e11c%Z => first [ eapply (pm_exit E OK) with (dg := D); [exact INV | lia | lia] | fail 100 "cut" pc ]
      | 0x5d678%Z => first [ eapply evt_eq; [| eapply pm_fe_61c with (p := FPT)]; [num_st_eq | exact INV | exact HF | lia | lia | lia] | fail 100 "cut" pc ]
      | 0x5dc48%Z => first [ eapply evt_eq; [| eapply pm_fe_bec with (p := FPT)]; [num_st_eq | exact INV | exact HF | lia | lia | lia] | fail 100 "cut" pc ]
      | 0x5dae0%Z => first [ eapply evt_eq; [| eapply (pm_fe_Z8b (Z.to_nat FL) FPT)]; [num_st_eq | exact INV | exact HF | lia | lia | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.
End PMUFENT.
