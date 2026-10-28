(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjNumber SjNumU.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Sj_num_kitu Sj_num_kitn Sj_num_pm_defs Sj_num_pm_round.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ solve_load_base | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].
Local Ltac nnorm ::= nnorm_u.

Section PMUTF.
  Variable E : pmuenv.
  Hypothesis OK : pmu_ok E.
  Notation X := (p_X E).
  Notation IP := (p_IP E).
  Notation IL := (p_IL E).
  Notation FPT := (p_FPT E).
  Notation FL := (p_FL E).

  Lemma pm_tf_Z1e : forall (f : nat) (p : Z) xra xt0 xt1 xt2 xs0 xs1 xa4 xa7 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm len v16,
    PMUINV E mm len 769 v16 ->
    FPT <> 0%Z ->
    (FPT <= p < FPT + FL)%Z ->
    (FPT + FL - p <= Z.of_nat f)%Z ->
    evt usegs (pmu_post E) (PM E 0x5e000 xra xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 48) (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 (X + 504)) xa4 (Z_to_bv 64 p) (Z_to_bv 64 (FPT + FL)) xa7 (Z_to_bv 64 X) xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros f. induction f as [|f IH]; intros until v16; intros INV HF Hp Hf; [exfalso; lia|].
    pose proof INV as INV0. pm_open INV0. pm_env OK. destruct SPN4 as [?|SPN4]; [exfalso; lia|].
    nstep.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5e158%Z => u_trap pc
      | 0x5e11c%Z => first [ eapply (pm_exit E OK) with (dg := 769%Z); [exact INV | lia | lia] | fail 100 "cut" pc ]
      | 0x5e01c%Z => first [ eapply evt_eq; [| eapply (pm_roundB E OK)]; [num_st_eq | exact INV] | fail 100 "cut" pc ]
      | 0x5e000%Z => first [ eapply evt_eq; [| eapply (IH (p + 1)%Z)]; [num_st_eq | exact INV | exact HF | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_tf_f98 : forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa2 xa4 xa7 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm len v16 p,
    PMUINV E mm len 769 v16 ->
    FPT <> 0%Z ->
    (FPT <= p <= FPT + FL)%Z ->
    evt usegs (pmu_post E) (PM E 0x5dff4 xra xt0 xt1 xt2 xs0 xs1 xa0 (Z_to_bv 64 (18446744073709551615 - X)) xa2 (Z_to_bv 64 (X + 504)) xa4 (Z_to_bv 64 p) (Z_to_bv 64 (FPT + FL)) xa7 (Z_to_bv 64 X) xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros until p. intros INV HF Hp. pose proof INV as INV0. pm_open INV0. pm_env OK. destruct SPN4 as [?|SPN4]; [exfalso; lia|].
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5e11c%Z => first [ eapply (pm_exit E OK) with (dg := 769%Z); [exact INV | lia | lia] | fail 100 "cut" pc ]
      | 0x5e000%Z => first [ eapply evt_eq; [| eapply (pm_tf_Z1e (Z.to_nat (FPT + FL - p)) p)]; [num_st_eq | exact INV | exact HF | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_tf_Z8e : forall (f : nat) (p : Z) xra xt1 xt2 xs0 xs1 xa0 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm len v16,
    PMUINV E mm len 769 v16 ->
    FPT <> 0%Z ->
    (FPT <= p)%Z ->
    (p + 8 <= FPT + FL)%Z ->
    (FPT + FL - p <= Z.of_nat f)%Z ->
    evt usegs (pmu_post E) (PM E 0x5df88 xra (Z_to_bv 64 7) xt1 xt2 xs0 xs1 xa0 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (FPT + FL - p)) (Z_to_bv 64 (X + 504)) (Z_to_bv 64 18446744073709551608) (Z_to_bv 64 p) (Z_to_bv 64 (FPT + FL)) (Z_to_bv 64 3472328296227680304) (Z_to_bv 64 X) xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros f. induction f as [|f IH]; intros until v16; intros INV HF Hp Hp8 Hf; [exfalso; lia|].
    pose proof INV as INV0. pm_open INV0. pm_env OK. destruct SPN4 as [?|SPN4]; [exfalso; lia|].
    nstep.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5e158%Z => u_trap pc
      | 0x5e01c%Z => first [ eapply evt_eq; [| eapply (pm_roundB E OK)]; [num_st_eq | exact INV] | fail 100 "cut" pc ]
      | 0x5dff4%Z => first [ eapply evt_eq; [| eapply pm_tf_f98]; [num_st_eq | exact INV | exact HF | lia] | fail 100 "cut" pc ]
      | 0x5df88%Z => first [ eapply evt_eq; [| eapply (IH (p + 8)%Z)]; [num_st_eq | exact INV | exact HF | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_tf_f08 : forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa2 xa4 xa7 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm len v16 p,
    PMUINV E mm len 769 v16 ->
    FPT <> 0%Z ->
    (FPT <= p <= FPT + FL)%Z ->
    evt usegs (pmu_post E) (PM E 0x5df64 xra xt0 xt1 xt2 xs0 xs1 xa0 (Z_to_bv 64 (18446744073709551615 - X)) xa2 (Z_to_bv 64 (X + 504)) xa4 (Z_to_bv 64 p) (Z_to_bv 64 (FPT + FL)) xa7 (Z_to_bv 64 X) xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros until p. intros INV HF Hp. pose proof INV as INV0. pm_open INV0. pm_env OK. destruct SPN4 as [?|SPN4]; [exfalso; lia|].
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5e158%Z => u_trap pc
      | 0x5dff4%Z => first [ eapply evt_eq; [| eapply pm_tf_f98]; [num_st_eq | exact INV | exact HF | lia] | fail 100 "cut" pc ]
      | 0x5df88%Z => first [ eapply evt_eq; [| eapply (pm_tf_Z8e (Z.to_nat (FPT + FL - p)) p)]; [num_st_eq | exact INV | exact HF | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_tf_ef0 : forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa4 xa7 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm len v16 p,
    PMUINV E mm len 769 v16 ->
    FPT <> 0%Z ->
    (FPT <= p <= FPT + FL)%Z ->
    (len <= 61)%Z ->
    evt usegs (pmu_post E) (PM E 0x5df4c xra xt0 xt1 xt2 xs0 xs1 xa0 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 len) (Z_to_bv 64 (X + 504)) xa4 (Z_to_bv 64 p) (Z_to_bv 64 (FPT + FL)) xa7 (Z_to_bv 64 X) xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros until p. intros INV HF Hp Hl. pm_open INV. pm_env OK. assert (DV : IsData xs7) by exact I.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5e158%Z => u_trap pc
      | 0x5df64%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINV E m1 (len + 1) 769 v16) by pm_close); eapply evt_eq; [| eapply pm_tf_f08]; [num_st_eq | exact INV1 | exact HF | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_tf_ee4 : forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa4 xa7 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm len v16 p,
    PMUINV E mm len 769 v16 ->
    FPT <> 0%Z ->
    (FPT <= p <= FPT + FL)%Z ->
    evt usegs (pmu_post E) (PM E 0x5df40 xra xt0 xt1 xt2 xs0 xs1 xa0 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 len) (Z_to_bv 64 (X + 504)) xa4 (Z_to_bv 64 p) (Z_to_bv 64 (FPT + FL)) xa7 (Z_to_bv 64 X) xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros until p. intros INV HF Hp. pose proof INV as INV0. pm_open INV0. pm_env OK.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5df64%Z => first [ eapply evt_eq; [| eapply pm_tf_f08]; [num_st_eq | exact INV | exact HF | lia] | fail 100 "cut" pc ]
      | 0x5df4c%Z => first [ eapply evt_eq; [| eapply pm_tf_ef0]; [num_st_eq | exact INV | exact HF | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_tf_CA : forall (f : nat) (j : Z) xra xt1 xt2 xs0 xs1 xa0 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm len v16 p,
    PMUINV E mm len 769 v16 ->
    FPT <> 0%Z ->
    (FPT <= p <= FPT + FL)%Z ->
    (0 <= j <= len - 1)%Z ->
    (len - 1 - j <= Z.of_nat f)%Z ->
    evt usegs (pmu_post E) (PM E 0x5dc18 xra (Z_to_bv 64 (X + 8 + 8 * j)) xt1 xt2 xs0 xs1 xa0 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 len) (Z_to_bv 64 (X + 504)) (Z_to_bv 64 (len - 1 - j)) (Z_to_bv 64 p) (Z_to_bv 64 (FPT + FL)) (Z_to_bv 64 (18446744073709551112 + 8 * j)) (Z_to_bv 64 X) xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros f. induction f as [|f IH]; intros until p; intros INV HF Hp Hj Hf.
    - pose proof INV as INV0. pm_open INV0. pm_env OK. nstep.
      uwalk ltac:(fun pc => lazymatch pc with
      | 0x5e158%Z => u_trap pc
      | 0x5df40%Z => first [ eapply evt_eq; [| eapply pm_tf_ee4]; [num_st_eq | exact INV | exact HF | lia] | fail 100 "cut" pc ]
      end).
    - pose proof INV as INV0. pm_open INV0. pm_env OK. nstep.
      uwalk ltac:(fun pc => lazymatch pc with
      | 0x5e158%Z => u_trap pc
      | 0x5df40%Z => first [ eapply evt_eq; [| eapply pm_tf_ee4]; [num_st_eq | exact INV | exact HF | lia] | fail 100 "cut" pc ]
      | 0x5df64%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINV E m1 len 769 v16) by pm_close); eapply evt_eq; [| eapply pm_tf_f08]; [num_st_eq | exact INV1 | exact HF | lia] | fail 100 "cut" pc ]
      | 0x5dc18%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINV E m1 len 769 v16) by pm_close); eapply evt_eq; [| eapply (IH (j + 1)%Z)]; [num_st_eq | exact INV1 | exact HF | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_tf_b94 : forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa2 xa4 xa7 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm len v16 p,
    PMUINV E mm len 769 v16 ->
    FPT <> 0%Z ->
    (FPT <= p <= FPT + FL)%Z ->
    evt usegs (pmu_post E) (PM E 0x5dbf0 xra xt0 xt1 xt2 xs0 xs1 xa0 (Z_to_bv 64 (18446744073709551615 - X)) xa2 (Z_to_bv 64 (X + 504)) xa4 (Z_to_bv 64 p) (Z_to_bv 64 (FPT + FL)) xa7 (Z_to_bv 64 X) xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros until p. intros INV HF Hp. pose proof INV as INV0. pm_open INV0. pm_env OK. assert (DV : IsData xs7) by exact I.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5e158%Z => u_trap pc
      | 0x5df64%Z => first [ first [ eapply evt_eq; [| eapply pm_tf_f08]; [num_st_eq | exact INV | exact HF | lia] | num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINV E m1 len 769 v16) by pm_close); eapply evt_eq; [| eapply pm_tf_f08]; [num_st_eq | exact INV1 | exact HF | lia] ] | fail 100 "cut" pc ]
      | 0x5df4c%Z => first [ eapply evt_eq; [| eapply pm_tf_ef0]; [num_st_eq | exact INV | exact HF | lia | lia] | fail 100 "cut" pc ]
      | 0x5dc18%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINV E m1 len 769 v16) by pm_close); eapply evt_eq; [| eapply (pm_tf_CA (Z.to_nat len) 0%Z) with (len := len)]; [num_st_eq | exact INV1 | exact HF | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_tf_b70 : forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa4 xa7 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm len v16 p,
    PMUINV E mm len 769 v16 ->
    FPT <> 0%Z ->
    (FPT <= p <= FPT + FL)%Z ->
    evt usegs (pmu_post E) (PM E 0x5dbcc xra xt0 xt1 xt2 xs0 xs1 xa0 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 len) (Z_to_bv 64 (X + 504)) xa4 (Z_to_bv 64 p) (Z_to_bv 64 (FPT + FL)) xa7 (Z_to_bv 64 X) xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros until p. intros INV HF Hp. pose proof INV as INV0. pm_open INV0. pm_env OK. assert (DC : IsData xa4) by exact I.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5e158%Z => u_trap pc
      | 0x5dbf0%Z => first [ first [ eapply evt_eq; [| eapply pm_tf_b94]; [num_st_eq | exact INV | exact HF | lia] | num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINV E m1 (len + 1) 769 v16) by pm_close); eapply evt_eq; [| eapply pm_tf_b94]; [num_st_eq | exact INV1 | exact HF | lia] ] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_tf_SM : forall (f : nat) (i : Z) xra xt0 xt2 xs0 xs1 xa4 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm len v16 p,
    PMUINV E mm len 769 v16 ->
    FPT <> 0%Z ->
    (FPT <= p <= FPT + FL)%Z ->
    (0 <= i < len)%Z ->
    (len - i <= Z.of_nat f)%Z ->
    evt usegs (pmu_post E) (PM E 0x5dba0 xra xt0 (Z_to_bv 64 (X + 8 * len)) xt2 xs0 xs1 (Z_to_bv 64 (X + 8 * i)) (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 len) (Z_to_bv 64 (X + 504)) xa4 (Z_to_bv 64 p) (Z_to_bv 64 (FPT + FL)) (Z_to_bv 64 (63 - i)) (Z_to_bv 64 X) xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros f. induction f as [|f IH]; intros until p; intros INV HF Hp Hi Hf; [exfalso; lia|].
    pose proof INV as INV0. pm_open INV0. pm_env OK. assert (DC : IsData xa4) by exact I. assert (DY : IsData xt0) by exact I.
    nstep.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5e158%Z => u_trap pc
      | 0x5dbcc%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINV E m1 len 769 v16) by pm_close); eapply evt_eq; [| eapply pm_tf_b70]; [num_st_eq | exact INV1 | exact HF | lia] | fail 100 "cut" pc ]
      | 0x5dba0%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINV E m1 len 769 v16) by pm_close); eapply evt_eq; [| eapply (IH (i + 1)%Z)]; [num_st_eq | exact INV1 | exact HF | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_tf : forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa2 xa7 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs11 xt3 xt4 xt5 xt6 mm len v16 p cn,
    PMUINV E mm len 769 v16 ->
    FPT <> 0%Z ->
    (FPT <= p <= FPT + FL)%Z ->
    (0 <= cn <= 19)%Z ->
    evt usegs (pmu_post E) (PM E 0x5db58 xra xt0 xt1 xt2 xs0 xs1 xa0 (Z_to_bv 64 (18446744073709551615 - X)) xa2 (Z_to_bv 64 (X + 504)) (Z_to_bv 64 PMU_POW10) (Z_to_bv 64 p) (Z_to_bv 64 (FPT + FL)) xa7 (Z_to_bv 64 X) xs3 xs4 xs5 xs6 xs7 xs8 xs9 (Z_to_bv 64 cn) xs11 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros until cn. intros INV HF Hp Hc. pose proof INV as INV0. pm_open INV0. pm_env OK. unfold PMU_POW10.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5e158%Z => u_trap pc
      | 0x5dbf0%Z => first [ eapply evt_eq; [| eapply pm_tf_b94]; [num_st_eq | exact INV | exact HF | lia] | fail 100 "cut" pc ]
      | 0x5dba0%Z => first [ eapply evt_eq; [| eapply (pm_tf_SM (Z.to_nat len) 0%Z) with (len := len)]; [num_st_eq | exact INV | exact HF | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.
End PMUTF.
