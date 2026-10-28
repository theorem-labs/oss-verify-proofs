(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjNumber SjNumU SjNumN.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_rtf Sj_num_akit Sj_num_amem
  Sj_num_iface Sj_num_bkit Sj_num_bdefs Sj_num_pm_kit Sj_num_pm_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | asan_zr_hook | asan_ptr_hook | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].
Local Ltac nnorm ::= nnorm_u.
Local Ltac unorm_in H ::= unorm_in_n H.

Section PMBROUND.
  Variable E : pmbenv.
  Hypothesis OK : pmb_ok E.
  Hypothesis PV : pmb_prov E.
  Notation X := (p_X E).
  Notation DGA := (p_DG E).
  Notation IP := (p_IP E).
  Notation IL := (p_IL E).
  Notation FPT := (p_FPT E).
  Notation FL := (p_FL E).

  Lemma pm_inc : forall xra xt2 xs0 xs1 xa0 xa1 xa2 xa4 xa5 xa6 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm len w8 w16 w24 w32 w40 w48 w56,
    PMBINV E mm len 769 w8 w16 w24 w32 w40 w48 w56 (Z_to_bv 64 (X / 8)) ->
    evt bsegs (pmb_post E) (PMB E 0xfa94c xra (Z_to_bv 64 (DGA / 8 + 2147450880)) (Z_to_bv 64 2147450880) xt2 xs0 xs1 xa0 xa1 xa2 (Z_to_bv 64 DGA) xa4 xa5 xa6 xa7 xs2 xs3 (Z_to_bv 64 X) xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using OK PV.
    intros until w56. intros INV. pm_open INV. pm_env OK. pm_prov PV.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xfa99c%Z => u_trap pc
      | 0xfa960%Z => first [ eapply (pm_exit E OK) with (dg := 770%Z); [pm_close | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_rA_push1 : forall xra xt2 xs0 xs1 xa0 xa1 xa5 xa6 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm len w8 w16 w24 w32 w40 w48,
    PMBINV E mm len 769 w8 w16 w24 w32 w40 w48 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (X / 8)) ->
    (len <= 61)%Z ->
    evt bsegs (pmb_post E) (PMB E 0xfa618 xra (Z_to_bv 64 (DGA / 8 + 2147450880)) (Z_to_bv 64 2147450880) xt2 xs0 xs1 xa0 xa1 (Z_to_bv 64 len) (Z_to_bv 64 DGA) (Z_to_bv 64 (X + 496)) xa5 xa6 (Z_to_bv 64 ((X + 496) / 8 + 2147450880)) xs2 xs3 (Z_to_bv 64 X) xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using OK PV.
    intros until w48. intros INV Hl. pm_open INV. pm_env OK. pm_prov PV.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xfa99c%Z => u_trap pc
      | 0xfa94c%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMBINV E m1 (len + 1) 769 w8 w16 w24 w32 w40 w48 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (X / 8))) by pm_close); eapply evt_eq; [| eapply pm_inc with (len := (len + 1)%Z)]; [num_st_eq | exact INV1] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_rA_ebc : forall xra xt2 xs0 xs1 xa0 xa1 xa5 xa6 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm len w8 w16 w24 w32 w40 w48,
    PMBINV E mm len 769 w8 w16 w24 w32 w40 w48 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (X / 8)) ->
    evt bsegs (pmb_post E) (PMB E 0xfa610 xra (Z_to_bv 64 (DGA / 8 + 2147450880)) (Z_to_bv 64 2147450880) xt2 xs0 xs1 xa0 xa1 (Z_to_bv 64 len) (Z_to_bv 64 DGA) (Z_to_bv 64 (X + 496)) xa5 xa6 (Z_to_bv 64 ((X + 496) / 8 + 2147450880)) xs2 xs3 (Z_to_bv 64 X) xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using OK PV.
    intros until w48. intros INV. pose proof INV as INV0. pm_open INV0. pm_env OK. pm_prov PV.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xfa99c%Z => u_trap pc
      | 0xfa94c%Z => first [ eapply evt_eq; [| eapply pm_inc with (len := len)]; [num_st_eq | exact INV] | fail 100 "cut" pc ]
      | 0xfa618%Z => first [ eapply evt_eq; [| eapply pm_rA_push1 with (len := len)]; [num_st_eq | exact INV | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_rA_CA : forall (f : nat) (j : Z) xra xt2 xs0 xs1 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm len w8 w16 w24 w32 w40 w48,
    PMBINV E mm len 769 w8 w16 w24 w32 w40 w48 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (X / 8)) ->
    (0 <= j <= len - 1)%Z ->
    (len - 1 - j <= Z.of_nat f)%Z ->
    evt bsegs (pmb_post E) (PMB E 0xfa5c8 xra (Z_to_bv 64 (DGA / 8 + 2147450880)) (Z_to_bv 64 2147450880) xt2 xs0 xs1 (Z_to_bv 64 (X + 8 + 8 * j)) (Z_to_bv 64 (X + 8 + 8 * j)) (Z_to_bv 64 len) (Z_to_bv 64 DGA) (Z_to_bv 64 (X + 496)) (Z_to_bv 64 (len - 1 - j)) (Z_to_bv 64 (18446744073709551112 + 8 * j)) (Z_to_bv 64 ((X + 496) / 8 + 2147450880)) xs2 xs3 (Z_to_bv 64 X) xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using OK PV.
    intros f. induction f as [|f IH]; intros until w48; intros INV Hj Hf.
    - pose proof INV as INV0. pm_open INV0. pm_env OK. pm_prov PV. bstep.
      bwalk ltac:(fun pc => lazymatch pc with
      | 0xfa99c%Z => u_trap pc
      | 0xfa610%Z => first [ eapply evt_eq; [| eapply pm_rA_ebc with (len := len)]; [num_st_eq | exact INV] | fail 100 "cut" pc ]
      end).
    - pose proof INV as INV0. pm_open INV0. pm_env OK. pm_prov PV. bstep.
      bwalk ltac:(fun pc => lazymatch pc with
      | 0xfa99c%Z => u_trap pc
      | 0xfa610%Z => first [ eapply evt_eq; [| eapply pm_rA_ebc with (len := len)]; [num_st_eq | exact INV] | fail 100 "cut" pc ]
      | 0xfa94c%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMBINV E m1 len 769 w8 w16 w24 w32 w40 w48 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (X / 8))) by pm_close); eapply evt_eq; [| eapply pm_inc with (len := len)]; [num_st_eq | exact INV1] | fail 100 "cut" pc ]
      | 0xfa5c8%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMBINV E m1 len 769 w8 w16 w24 w32 w40 w48 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (X / 8))) by pm_close); eapply evt_eq; [| eapply (IH (j + 1)%Z) with (len := len)]; [num_st_eq | exact INV1 | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_rA_inc0 : forall xra xt2 xs0 xs1 xa0 xa1 xa5 xa6 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm len w8 w16 w24 w32 w40 w48,
    PMBINV E mm len 769 w8 w16 w24 w32 w40 w48 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (X / 8)) ->
    (1 <= len)%Z ->
    evt bsegs (pmb_post E) (PMB E 0xfa58c xra (Z_to_bv 64 (DGA / 8 + 2147450880)) (Z_to_bv 64 2147450880) xt2 xs0 xs1 xa0 xa1 (Z_to_bv 64 len) (Z_to_bv 64 DGA) (Z_to_bv 64 (X + 496)) xa5 xa6 (Z_to_bv 64 ((X + 496) / 8 + 2147450880)) xs2 xs3 (Z_to_bv 64 X) xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using OK PV.
    intros until w48. intros INV Hl. pm_open INV. pm_env OK. pm_prov PV.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xfa99c%Z => u_trap pc
      | 0xfa94c%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMBINV E m1 len 769 w8 w16 w24 w32 w40 w48 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (X / 8))) by pm_close); eapply evt_eq; [| eapply pm_inc with (len := len)]; [num_st_eq | exact INV1] | fail 100 "cut" pc ]
      | 0xfa5c8%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMBINV E m1 len 769 w8 w16 w24 w32 w40 w48 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (X / 8))) by pm_close); eapply evt_eq; [| eapply (pm_rA_CA (Z.to_nat len) 0%Z) with (len := len)]; [num_st_eq | exact INV1 | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_rA_e48 : forall xra xt2 xs0 xs1 xa0 xa1 xa5 xa6 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm len w8 w16 w24 w32 w40 w48,
    PMBINV E mm len 769 w8 w16 w24 w32 w40 w48 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (X / 8)) ->
    (1 <= len)%Z ->
    evt bsegs (pmb_post E) (PMB E 0xfa538 xra (Z_to_bv 64 (DGA / 8 + 2147450880)) (Z_to_bv 64 2147450880) xt2 xs0 xs1 xa0 xa1 (Z_to_bv 64 len) (Z_to_bv 64 DGA) (Z_to_bv 64 (X + 496)) xa5 xa6 (Z_to_bv 64 ((X + 496) / 8 + 2147450880)) xs2 xs3 (Z_to_bv 64 X) xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using OK PV.
    intros until w48. intros INV Hl. pose proof INV as INV0. pm_open INV0. pm_env OK. pm_prov PV.
    assert (DC : IsData xa5) by exact I.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xfa99c%Z => u_trap pc
      | 0xfa618%Z => first [ eapply evt_eq; [| eapply pm_rA_push1 with (len := len)]; [num_st_eq | exact INV | lia] | fail 100 "cut" pc ]
      | 0xfa58c%Z => first [ first [ eapply evt_eq; [| eapply pm_rA_inc0 with (len := len)]; [num_st_eq | exact INV | lia] | num_cur_mem ltac:(fun m1 => assert (INV1 : PMBINV E m1 (len + 1) 769 w8 w16 w24 w32 w40 w48 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (X / 8))) by pm_close); eapply evt_eq; [| eapply pm_rA_inc0 with (len := (len + 1)%Z)]; [num_st_eq | exact INV1 | lia] ] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_rA_SM : forall (f : nat) (i : Z) xra xs0 xs1 xa5 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt4 xt5 xt6 mm len w8 w16 w24 w32 w40 w48,
    PMBINV E mm len 769 w8 w16 w24 w32 w40 w48 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (X / 8)) ->
    (0 <= i < len)%Z ->
    (len - i <= Z.of_nat f)%Z ->
    evt bsegs (pmb_post E) (PMB E 0xfa4f4 xra (Z_to_bv 64 (DGA / 8 + 2147450880)) (Z_to_bv 64 2147450880) (Z_to_bv 64 10) xs0 xs1 (Z_to_bv 64 (len - i)) (Z_to_bv 64 (X + 8 * i)) (Z_to_bv 64 len) (Z_to_bv 64 DGA) (Z_to_bv 64 (X + 496)) xa5 (Z_to_bv 64 (63 - i)) (Z_to_bv 64 ((X + 496) / 8 + 2147450880)) xs2 xs3 (Z_to_bv 64 X) xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 (X + 8 * i)) xt4 xt5 xt6 mm).
  Proof using OK PV.
    intros f. induction f as [|f IH]; intros until w48; intros INV Hi Hf; [exfalso; lia|].
    pose proof INV as INV0. pm_open INV0. pm_env OK. pm_prov PV.
    assert (DC : IsData xa5) by exact I.
    bstep.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xfa99c%Z => u_trap pc
      | 0xfa538%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMBINV E m1 len 769 w8 w16 w24 w32 w40 w48 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (X / 8))) by pm_close); eapply evt_eq; [| eapply pm_rA_e48 with (len := len)]; [num_st_eq | exact INV1 | lia] | fail 100 "cut" pc ]
      | 0xfa4f4%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMBINV E m1 len 769 w8 w16 w24 w32 w40 w48 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (X / 8))) by pm_close); eapply evt_eq; [| eapply (IH (i + 1)%Z) with (len := len)]; [num_st_eq | exact INV1 | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_roundA : forall xra xt2 xs0 xs1 xa0 xa1 xa2 xa5 xa6 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm len w8 w16 w24 w32 w40 w48,
    PMBINV E mm len 769 w8 w16 w24 w32 w40 w48 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (X / 8)) ->
    evt bsegs (pmb_post E) (PMB E 0xfa4cc xra (Z_to_bv 64 (DGA / 8 + 2147450880)) (Z_to_bv 64 2147450880) xt2 xs0 xs1 xa0 xa1 xa2 (Z_to_bv 64 DGA) (Z_to_bv 64 (X + 496)) xa5 xa6 (Z_to_bv 64 ((X + 496) / 8 + 2147450880)) xs2 xs3 (Z_to_bv 64 X) xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using OK PV.
    intros until w48. intros INV. pose proof INV as INV0. pm_open INV0. pm_env OK. pm_prov PV.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xfa99c%Z => u_trap pc
      | 0xfa618%Z => first [ eapply evt_eq; [| eapply pm_rA_push1 with (len := len)]; [num_st_eq | exact INV | lia] | fail 100 "cut" pc ]
      | 0xfa4f4%Z => first [ eapply evt_eq; [| eapply (pm_rA_SM (Z.to_nat len) 0%Z) with (len := len)]; [num_st_eq | exact INV | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_rB_push1 : forall xra xt2 xs0 xs1 xa0 xa2 xa5 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm len w8 w16 w24 w32 w40 w48,
    PMBINV E mm len 769 w8 w16 w24 w32 w40 w48 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (X / 8)) ->
    (len <= 61)%Z ->
    evt bsegs (pmb_post E) (PMB E 0xfa914 xra (Z_to_bv 64 (DGA / 8 + 2147450880)) (Z_to_bv 64 2147450880) xt2 xs0 xs1 xa0 (Z_to_bv 64 (X + 496)) xa2 (Z_to_bv 64 DGA) (Z_to_bv 64 len) xa5 (Z_to_bv 64 ((X + 496) / 8 + 2147450880)) xa7 xs2 xs3 (Z_to_bv 64 X) xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using OK PV.
    intros until w48. intros INV Hl. pm_open INV. pm_env OK. pm_prov PV.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xfa99c%Z => u_trap pc
      | 0xfa94c%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMBINV E m1 (len + 1) 769 w8 w16 w24 w32 w40 w48 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (X / 8))) by pm_close); eapply evt_eq; [| eapply pm_inc with (len := (len + 1)%Z)]; [num_st_eq | exact INV1] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_rB_ebc : forall xra xt2 xs0 xs1 xa0 xa2 xa5 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm len w8 w16 w24 w32 w40 w48,
    PMBINV E mm len 769 w8 w16 w24 w32 w40 w48 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (X / 8)) ->
    evt bsegs (pmb_post E) (PMB E 0xfa90c xra (Z_to_bv 64 (DGA / 8 + 2147450880)) (Z_to_bv 64 2147450880) xt2 xs0 xs1 xa0 (Z_to_bv 64 (X + 496)) xa2 (Z_to_bv 64 DGA) (Z_to_bv 64 len) xa5 (Z_to_bv 64 ((X + 496) / 8 + 2147450880)) xa7 xs2 xs3 (Z_to_bv 64 X) xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using OK PV.
    intros until w48. intros INV. pose proof INV as INV0. pm_open INV0. pm_env OK. pm_prov PV.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xfa99c%Z => u_trap pc
      | 0xfa94c%Z => first [ eapply evt_eq; [| eapply pm_inc with (len := len)]; [num_st_eq | exact INV] | fail 100 "cut" pc ]
      | 0xfa914%Z => first [ eapply evt_eq; [| eapply pm_rB_push1 with (len := len)]; [num_st_eq | exact INV | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_rB_CA : forall (f : nat) (j : Z) xra xt2 xs0 xs1 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm len w8 w16 w24 w32 w40 w48,
    PMBINV E mm len 769 w8 w16 w24 w32 w40 w48 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (X / 8)) ->
    (0 <= j <= len - 1)%Z ->
    (len - 1 - j <= Z.of_nat f)%Z ->
    evt bsegs (pmb_post E) (PMB E 0xfa8c4 xra (Z_to_bv 64 (DGA / 8 + 2147450880)) (Z_to_bv 64 2147450880) xt2 xs0 xs1 (Z_to_bv 64 (X + 8 + 8 * j)) (Z_to_bv 64 (X + 496)) (Z_to_bv 64 (X + 8 + 8 * j)) (Z_to_bv 64 DGA) (Z_to_bv 64 len) (Z_to_bv 64 (len - 1 - j)) (Z_to_bv 64 ((X + 496) / 8 + 2147450880)) (Z_to_bv 64 (18446744073709551112 + 8 * j)) xs2 xs3 (Z_to_bv 64 X) xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using OK PV.
    intros f. induction f as [|f IH]; intros until w48; intros INV Hj Hf.
    - pose proof INV as INV0. pm_open INV0. pm_env OK. pm_prov PV. bstep.
      bwalk ltac:(fun pc => lazymatch pc with
      | 0xfa99c%Z => u_trap pc
      | 0xfa90c%Z => first [ eapply evt_eq; [| eapply pm_rB_ebc with (len := len)]; [num_st_eq | exact INV] | fail 100 "cut" pc ]
      end).
    - pose proof INV as INV0. pm_open INV0. pm_env OK. pm_prov PV. bstep.
      bwalk ltac:(fun pc => lazymatch pc with
      | 0xfa99c%Z => u_trap pc
      | 0xfa90c%Z => first [ eapply evt_eq; [| eapply pm_rB_ebc with (len := len)]; [num_st_eq | exact INV] | fail 100 "cut" pc ]
      | 0xfa94c%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMBINV E m1 len 769 w8 w16 w24 w32 w40 w48 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (X / 8))) by pm_close); eapply evt_eq; [| eapply pm_inc with (len := len)]; [num_st_eq | exact INV1] | fail 100 "cut" pc ]
      | 0xfa8c4%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMBINV E m1 len 769 w8 w16 w24 w32 w40 w48 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (X / 8))) by pm_close); eapply evt_eq; [| eapply (IH (j + 1)%Z) with (len := len)]; [num_st_eq | exact INV1 | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_rB_inc0 : forall xra xt2 xs0 xs1 xa0 xa2 xa5 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm len w8 w16 w24 w32 w40 w48,
    PMBINV E mm len 769 w8 w16 w24 w32 w40 w48 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (X / 8)) ->
    (1 <= len)%Z ->
    evt bsegs (pmb_post E) (PMB E 0xfa888 xra (Z_to_bv 64 (DGA / 8 + 2147450880)) (Z_to_bv 64 2147450880) xt2 xs0 xs1 xa0 (Z_to_bv 64 (X + 496)) xa2 (Z_to_bv 64 DGA) (Z_to_bv 64 len) xa5 (Z_to_bv 64 ((X + 496) / 8 + 2147450880)) xa7 xs2 xs3 (Z_to_bv 64 X) xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using OK PV.
    intros until w48. intros INV Hl. pm_open INV. pm_env OK. pm_prov PV.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xfa99c%Z => u_trap pc
      | 0xfa94c%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMBINV E m1 len 769 w8 w16 w24 w32 w40 w48 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (X / 8))) by pm_close); eapply evt_eq; [| eapply pm_inc with (len := len)]; [num_st_eq | exact INV1] | fail 100 "cut" pc ]
      | 0xfa8c4%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMBINV E m1 len 769 w8 w16 w24 w32 w40 w48 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (X / 8))) by pm_close); eapply evt_eq; [| eapply (pm_rB_CA (Z.to_nat len) 0%Z) with (len := len)]; [num_st_eq | exact INV1 | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_rB_e48 : forall xra xt2 xs0 xs1 xa0 xa2 xa5 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm len w8 w16 w24 w32 w40 w48,
    PMBINV E mm len 769 w8 w16 w24 w32 w40 w48 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (X / 8)) ->
    (1 <= len)%Z ->
    evt bsegs (pmb_post E) (PMB E 0xfa834 xra (Z_to_bv 64 (DGA / 8 + 2147450880)) (Z_to_bv 64 2147450880) xt2 xs0 xs1 xa0 (Z_to_bv 64 (X + 496)) xa2 (Z_to_bv 64 DGA) (Z_to_bv 64 len) xa5 (Z_to_bv 64 ((X + 496) / 8 + 2147450880)) xa7 xs2 xs3 (Z_to_bv 64 X) xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using OK PV.
    intros until w48. intros INV Hl. pose proof INV as INV0. pm_open INV0. pm_env OK. pm_prov PV.
    assert (DC : IsData xa5) by exact I.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xfa99c%Z => u_trap pc
      | 0xfa914%Z => first [ eapply evt_eq; [| eapply pm_rB_push1 with (len := len)]; [num_st_eq | exact INV | lia] | fail 100 "cut" pc ]
      | 0xfa888%Z => first [ first [ eapply evt_eq; [| eapply pm_rB_inc0 with (len := len)]; [num_st_eq | exact INV | lia] | num_cur_mem ltac:(fun m1 => assert (INV1 : PMBINV E m1 (len + 1) 769 w8 w16 w24 w32 w40 w48 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (X / 8))) by pm_close); eapply evt_eq; [| eapply pm_rB_inc0 with (len := (len + 1)%Z)]; [num_st_eq | exact INV1 | lia] ] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_rB_SM : forall (f : nat) (i : Z) xra xs0 xs1 xa5 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt4 xt5 xt6 mm len w8 w16 w24 w32 w40 w48,
    PMBINV E mm len 769 w8 w16 w24 w32 w40 w48 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (X / 8)) ->
    (0 <= i < len)%Z ->
    (len - i <= Z.of_nat f)%Z ->
    evt bsegs (pmb_post E) (PMB E 0xfa7f0 xra (Z_to_bv 64 (DGA / 8 + 2147450880)) (Z_to_bv 64 2147450880) (Z_to_bv 64 10) xs0 xs1 (Z_to_bv 64 (X + 8 * i)) (Z_to_bv 64 (X + 496)) (Z_to_bv 64 (X + 8 * i)) (Z_to_bv 64 DGA) (Z_to_bv 64 len) xa5 (Z_to_bv 64 ((X + 496) / 8 + 2147450880)) (Z_to_bv 64 (63 - i)) xs2 xs3 (Z_to_bv 64 X) xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 (len - i)) xt4 xt5 xt6 mm).
  Proof using OK PV.
    intros f. induction f as [|f IH]; intros until w48; intros INV Hi Hf; [exfalso; lia|].
    pose proof INV as INV0. pm_open INV0. pm_env OK. pm_prov PV.
    assert (DC : IsData xa5) by exact I.
    bstep.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xfa99c%Z => u_trap pc
      | 0xfa834%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMBINV E m1 len 769 w8 w16 w24 w32 w40 w48 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (X / 8))) by pm_close); eapply evt_eq; [| eapply pm_rB_e48 with (len := len)]; [num_st_eq | exact INV1 | lia] | fail 100 "cut" pc ]
      | 0xfa7f0%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMBINV E m1 len 769 w8 w16 w24 w32 w40 w48 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (X / 8))) by pm_close); eapply evt_eq; [| eapply (IH (i + 1)%Z) with (len := len)]; [num_st_eq | exact INV1 | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_roundB : forall xra xt2 xs0 xs1 xa0 xa2 xa4 xa5 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm len w8 w16 w24 w32 w40 w48,
    PMBINV E mm len 769 w8 w16 w24 w32 w40 w48 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (X / 8)) ->
    evt bsegs (pmb_post E) (PMB E 0xfa7c8 xra (Z_to_bv 64 (DGA / 8 + 2147450880)) (Z_to_bv 64 2147450880) xt2 xs0 xs1 xa0 (Z_to_bv 64 (X + 496)) xa2 (Z_to_bv 64 DGA) xa4 xa5 (Z_to_bv 64 ((X + 496) / 8 + 2147450880)) xa7 xs2 xs3 (Z_to_bv 64 X) xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using OK PV.
    intros until w48. intros INV. pose proof INV as INV0. pm_open INV0. pm_env OK. pm_prov PV.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xfa99c%Z => u_trap pc
      | 0xfa914%Z => first [ eapply evt_eq; [| eapply pm_rB_push1 with (len := len)]; [num_st_eq | exact INV | lia] | fail 100 "cut" pc ]
      | 0xfa7f0%Z => first [ eapply evt_eq; [| eapply (pm_rB_SM (Z.to_nat len) 0%Z) with (len := len)]; [num_st_eq | exact INV | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

End PMBROUND.
