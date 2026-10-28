(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjNumber SjNumU.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Sj_num_kitu Sj_num_kitn Sj_num_pm_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ solve_load_base | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].
Local Ltac nnorm ::= nnorm_u.

Section PMUROUND.
  Variable E : pmuenv.
  Hypothesis OK : pmu_ok E.
  Notation X := (p_X E).

  Lemma pm_0b4 : forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm len v16,
    PMUINV E mm len 769 v16 ->
    evt usegs (pmu_post E) (PM E 0x5e110 xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 (Z_to_bv 64 (X + 504)) xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros until v16. intros INV. pm_open INV. pm_env OK.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5e11c%Z => first [ eapply (pm_exit E OK) with (dg := 770%Z); [pm_close | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_rA_push1 : forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa2 xa4 xa6 xa7 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm len v16,
    PMUINV E mm len 769 v16 ->
    (len <= 61)%Z ->
    evt usegs (pmu_post E) (PM E 0x5df20 xra xt0 xt1 xt2 xs0 xs1 xa0 (Z_to_bv 64 len) xa2 (Z_to_bv 64 (X + 504)) xa4 (Z_to_bv 64 (18446744073709551615 - X)) xa6 xa7 (Z_to_bv 64 X) xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros until v16. intros INV Hl. pm_open INV. pm_env OK.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5e158%Z => u_trap pc
      | 0x5e110%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINV E m1 (len + 1) 769 v16) by pm_close); eapply evt_eq; [| eapply pm_0b4]; [num_st_eq | exact INV1] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_rA_ebc : forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa2 xa4 xa6 xa7 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm len v16,
    PMUINV E mm len 769 v16 ->
    evt usegs (pmu_post E) (PM E 0x5df18 xra xt0 xt1 xt2 xs0 xs1 xa0 (Z_to_bv 64 len) xa2 (Z_to_bv 64 (X + 504)) xa4 (Z_to_bv 64 (18446744073709551615 - X)) xa6 xa7 (Z_to_bv 64 X) xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros until v16. intros INV. pose proof INV as INV0. pm_open INV0. pm_env OK.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5e110%Z => first [ eapply evt_eq; [| eapply pm_0b4]; [num_st_eq | exact INV] | fail 100 "cut" pc ]
      | 0x5df20%Z => first [ eapply evt_eq; [| eapply pm_rA_push1]; [num_st_eq | exact INV | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_rA_CA : forall (f : nat) (j : Z) xra xt0 xt1 xt2 xs0 xs1 xa0 xa7 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm len v16,
    PMUINV E mm len 769 v16 ->
    (0 <= j <= len - 1)%Z ->
    (len - 1 - j <= Z.of_nat f)%Z ->
    evt usegs (pmu_post E) (PM E 0x5def0 xra xt0 xt1 xt2 xs0 xs1 xa0 (Z_to_bv 64 len) (Z_to_bv 64 (len - 1 - j)) (Z_to_bv 64 (X + 504)) (Z_to_bv 64 (18446744073709551112 + 8 * j)) (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (X + 8 + 8 * j)) xa7 (Z_to_bv 64 X) xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros f. induction f as [|f IH]; intros until v16; intros INV Hj Hf.
    - pose proof INV as INV0. pm_open INV0. pm_env OK. nstep.
      uwalk ltac:(fun pc => lazymatch pc with
        | 0x5e158%Z => u_trap pc
        | 0x5df18%Z => first [ eapply evt_eq; [| eapply pm_rA_ebc]; [num_st_eq | exact INV] | fail 100 "cut" pc ]
        end).
    - pose proof INV as INV0. pm_open INV0. pm_env OK. nstep.
      uwalk ltac:(fun pc => lazymatch pc with
        | 0x5e158%Z => u_trap pc
        | 0x5df18%Z => first [ eapply evt_eq; [| eapply pm_rA_ebc]; [num_st_eq | exact INV] | fail 100 "cut" pc ]
        | 0x5e110%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINV E m1 len 769 v16) by pm_close); eapply evt_eq; [| eapply pm_0b4]; [num_st_eq | exact INV1] | fail 100 "cut" pc ]
        | 0x5def0%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINV E m1 len 769 v16) by pm_close);
                               eapply evt_eq; [| eapply (IH (j + 1)%Z)]; [num_st_eq | exact INV1 | lia | lia] | fail 100 "cut" pc ]
        end).
  Qed.

  Lemma pm_rA_inc0 : forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa2 xa4 xa6 xa7 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm len v16,
    PMUINV E mm len 769 v16 ->
    (1 <= len)%Z ->
    evt usegs (pmu_post E) (PM E 0x5ded4 xra xt0 xt1 xt2 xs0 xs1 xa0 (Z_to_bv 64 len) xa2 (Z_to_bv 64 (X + 504)) xa4 (Z_to_bv 64 (18446744073709551615 - X)) xa6 xa7 (Z_to_bv 64 X) xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros until v16. intros INV Hl. pm_open INV. pm_env OK.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5e158%Z => u_trap pc
      | 0x5e110%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINV E m1 len 769 v16) by pm_close); eapply evt_eq; [| eapply pm_0b4]; [num_st_eq | exact INV1] | fail 100 "cut" pc ]
      | 0x5def0%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINV E m1 len 769 v16) by pm_close);
                             eapply evt_eq; [| eapply (pm_rA_CA (Z.to_nat len) 0%Z)]; [num_st_eq | exact INV1 | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_rA_e48 : forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa2 xa4 xa6 xa7 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm len v16,
    PMUINV E mm len 769 v16 ->
    (1 <= len)%Z ->
    evt usegs (pmu_post E) (PM E 0x5dea4 xra xt0 xt1 xt2 xs0 xs1 xa0 (Z_to_bv 64 len) xa2 (Z_to_bv 64 (X + 504)) xa4 (Z_to_bv 64 (18446744073709551615 - X)) xa6 xa7 (Z_to_bv 64 X) xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros until v16. intros INV Hl. pose proof INV as INV0. pm_open INV0. pm_env OK.
    assert (DC : IsData xa2) by exact I.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5e158%Z => u_trap pc
      | 0x5df20%Z => first [ eapply evt_eq; [| eapply pm_rA_push1]; [num_st_eq | exact INV | lia] | fail 100 "cut" pc ]
      | 0x5ded4%Z => first [ eapply evt_eq; [| eapply pm_rA_inc0]; [num_st_eq | exact INV | lia]
                           | num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINV E m1 (len + 1) 769 v16) by pm_close);
                             eapply evt_eq; [| eapply pm_rA_inc0]; [num_st_eq | exact INV1 | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_rA_SM : forall (f : nat) (i : Z) xra xt1 xt2 xs0 xs1 xa0 xa2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm len v16,
    PMUINV E mm len 769 v16 ->
    (0 <= i < len)%Z ->
    (len - i <= Z.of_nat f)%Z ->
    evt usegs (pmu_post E) (PM E 0x5de78 xra (Z_to_bv 64 (X + 8 * i)) xt1 xt2 xs0 xs1 xa0 (Z_to_bv 64 len) xa2 (Z_to_bv 64 (X + 504)) (Z_to_bv 64 (63 - i)) (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (X + 8 * len)) (Z_to_bv 64 10) (Z_to_bv 64 X) xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros f. induction f as [|f IH]; intros until v16; intros INV Hi Hf; [exfalso; lia|].
    pose proof INV as INV0. pm_open INV0. pm_env OK.
    assert (DC : IsData xa2) by exact I.
    nstep.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5e158%Z => u_trap pc
      | 0x5dea4%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINV E m1 len 769 v16) by pm_close);
                             eapply evt_eq; [| eapply pm_rA_e48]; [num_st_eq | exact INV1 | lia] | fail 100 "cut" pc ]
      | 0x5de78%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINV E m1 len 769 v16) by pm_close);
                             eapply evt_eq; [| eapply (IH (i + 1)%Z)]; [num_st_eq | exact INV1 | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_roundA : forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa4 xa6 xa7 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm len v16,
    PMUINV E mm len 769 v16 ->
    evt usegs (pmu_post E) (PM E 0x5de48 xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 (Z_to_bv 64 (X + 504)) xa4 (Z_to_bv 64 (18446744073709551615 - X)) xa6 xa7 (Z_to_bv 64 X) xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros until v16. intros INV. pose proof INV as INV0. pm_open INV0. pm_env OK.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5e158%Z => u_trap pc
      | 0x5df20%Z => first [ eapply evt_eq; [| eapply pm_rA_push1]; [num_st_eq | exact INV | lia] | fail 100 "cut" pc ]
      | 0x5de78%Z => first [ eapply evt_eq; [| eapply (pm_rA_SM (Z.to_nat len) 0%Z)]; [num_st_eq | exact INV | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_rB_push1 : forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa4 xa5 xa6 xa7 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm len v16,
    PMUINV E mm len 769 v16 ->
    (len <= 61)%Z ->
    evt usegs (pmu_post E) (PM E 0x5e0f4 xra xt0 xt1 xt2 xs0 xs1 xa0 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 len) (Z_to_bv 64 (X + 504)) xa4 xa5 xa6 xa7 (Z_to_bv 64 X) xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros until v16. intros INV Hl. pm_open INV. pm_env OK.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5e158%Z => u_trap pc
      | 0x5e110%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINV E m1 (len + 1) 769 v16) by pm_close); eapply evt_eq; [| eapply pm_0b4]; [num_st_eq | exact INV1] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_rB_ebc : forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa4 xa5 xa6 xa7 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm len v16,
    PMUINV E mm len 769 v16 ->
    evt usegs (pmu_post E) (PM E 0x5e0ec xra xt0 xt1 xt2 xs0 xs1 xa0 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 len) (Z_to_bv 64 (X + 504)) xa4 xa5 xa6 xa7 (Z_to_bv 64 X) xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros until v16. intros INV. pose proof INV as INV0. pm_open INV0. pm_env OK.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5e110%Z => first [ eapply evt_eq; [| eapply pm_0b4]; [num_st_eq | exact INV] | fail 100 "cut" pc ]
      | 0x5e0f4%Z => first [ eapply evt_eq; [| eapply pm_rB_push1]; [num_st_eq | exact INV | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_rB_CA : forall (f : nat) (j : Z) xra xt0 xt1 xt2 xs0 xs1 xa0 xa7 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm len v16,
    PMUINV E mm len 769 v16 ->
    (0 <= j <= len - 1)%Z ->
    (len - 1 - j <= Z.of_nat f)%Z ->
    evt usegs (pmu_post E) (PM E 0x5e0c4 xra xt0 xt1 xt2 xs0 xs1 xa0 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 len) (Z_to_bv 64 (X + 504)) (Z_to_bv 64 (len - 1 - j)) (Z_to_bv 64 (18446744073709551112 + 8 * j)) (Z_to_bv 64 (X + 8 + 8 * j)) xa7 (Z_to_bv 64 X) xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros f. induction f as [|f IH]; intros until v16; intros INV Hj Hf.
    - pose proof INV as INV0. pm_open INV0. pm_env OK. nstep.
      uwalk ltac:(fun pc => lazymatch pc with
        | 0x5e158%Z => u_trap pc
        | 0x5e0ec%Z => first [ eapply evt_eq; [| eapply pm_rB_ebc]; [num_st_eq | exact INV] | fail 100 "cut" pc ]
        end).
    - pose proof INV as INV0. pm_open INV0. pm_env OK. nstep.
      uwalk ltac:(fun pc => lazymatch pc with
        | 0x5e158%Z => u_trap pc
        | 0x5e0ec%Z => first [ eapply evt_eq; [| eapply pm_rB_ebc]; [num_st_eq | exact INV] | fail 100 "cut" pc ]
        | 0x5e110%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINV E m1 len 769 v16) by pm_close); eapply evt_eq; [| eapply pm_0b4]; [num_st_eq | exact INV1] | fail 100 "cut" pc ]
        | 0x5e0c4%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINV E m1 len 769 v16) by pm_close);
                               eapply evt_eq; [| eapply (IH (j + 1)%Z)]; [num_st_eq | exact INV1 | lia | lia] | fail 100 "cut" pc ]
        end).
  Qed.

  Lemma pm_rB_inc0 : forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa4 xa5 xa6 xa7 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm len v16,
    PMUINV E mm len 769 v16 ->
    (1 <= len)%Z ->
    evt usegs (pmu_post E) (PM E 0x5e0a8 xra xt0 xt1 xt2 xs0 xs1 xa0 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 len) (Z_to_bv 64 (X + 504)) xa4 xa5 xa6 xa7 (Z_to_bv 64 X) xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros until v16. intros INV Hl. pm_open INV. pm_env OK.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5e158%Z => u_trap pc
      | 0x5e110%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINV E m1 len 769 v16) by pm_close); eapply evt_eq; [| eapply pm_0b4]; [num_st_eq | exact INV1] | fail 100 "cut" pc ]
      | 0x5e0c4%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINV E m1 len 769 v16) by pm_close);
                             eapply evt_eq; [| eapply (pm_rB_CA (Z.to_nat len) 0%Z)]; [num_st_eq | exact INV1 | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_rB_e48 : forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa4 xa5 xa6 xa7 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm len v16,
    PMUINV E mm len 769 v16 ->
    (1 <= len)%Z ->
    evt usegs (pmu_post E) (PM E 0x5e078 xra xt0 xt1 xt2 xs0 xs1 xa0 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 len) (Z_to_bv 64 (X + 504)) xa4 xa5 xa6 xa7 (Z_to_bv 64 X) xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros until v16. intros INV Hl. pose proof INV as INV0. pm_open INV0. pm_env OK.
    assert (DC : IsData xa4) by exact I.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5e158%Z => u_trap pc
      | 0x5e0f4%Z => first [ eapply evt_eq; [| eapply pm_rB_push1]; [num_st_eq | exact INV | lia] | fail 100 "cut" pc ]
      | 0x5e0a8%Z => first [ eapply evt_eq; [| eapply pm_rB_inc0]; [num_st_eq | exact INV | lia]
                           | num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINV E m1 (len + 1) 769 v16) by pm_close);
                             eapply evt_eq; [| eapply pm_rB_inc0]; [num_st_eq | exact INV1 | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_rB_SM : forall (f : nat) (i : Z) xra xt0 xt1 xt2 xs0 xs1 xa4 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm len v16,
    PMUINV E mm len 769 v16 ->
    (0 <= i < len)%Z ->
    (len - i <= Z.of_nat f)%Z ->
    evt usegs (pmu_post E) (PM E 0x5e04c xra xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 (X + 8 * i)) (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 len) (Z_to_bv 64 (X + 504)) xa4 (Z_to_bv 64 (63 - i)) (Z_to_bv 64 (X + 8 * len)) (Z_to_bv 64 10) (Z_to_bv 64 X) xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros f. induction f as [|f IH]; intros until v16; intros INV Hi Hf; [exfalso; lia|].
    pose proof INV as INV0. pm_open INV0. pm_env OK.
    assert (DC : IsData xa4) by exact I.
    nstep.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5e158%Z => u_trap pc
      | 0x5e078%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINV E m1 len 769 v16) by pm_close);
                             eapply evt_eq; [| eapply pm_rB_e48]; [num_st_eq | exact INV1 | lia] | fail 100 "cut" pc ]
      | 0x5e04c%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINV E m1 len 769 v16) by pm_close);
                             eapply evt_eq; [| eapply (IH (i + 1)%Z)]; [num_st_eq | exact INV1 | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_roundB : forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa2 xa4 xa5 xa6 xa7 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm len v16,
    PMUINV E mm len 769 v16 ->
    evt usegs (pmu_post E) (PM E 0x5e01c xra xt0 xt1 xt2 xs0 xs1 xa0 (Z_to_bv 64 (18446744073709551615 - X)) xa2 (Z_to_bv 64 (X + 504)) xa4 xa5 xa6 xa7 (Z_to_bv 64 X) xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros until v16. intros INV. pose proof INV as INV0. pm_open INV0. pm_env OK.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5e158%Z => u_trap pc
      | 0x5e0f4%Z => first [ eapply evt_eq; [| eapply pm_rB_push1]; [num_st_eq | exact INV | lia] | fail 100 "cut" pc ]
      | 0x5e04c%Z => first [ eapply evt_eq; [| eapply (pm_rB_SM (Z.to_nat len) 0%Z)]; [num_st_eq | exact INV | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

End PMUROUND.
