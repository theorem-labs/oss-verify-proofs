(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Sj Require Import SjNumber SjNumU SjNumN.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_rtf Sj_num_akit Sj_num_amem
  Sj_num_iface Sj_num_bkit Sj_num_bdefs Sj_num_pm_kit Sj_num_pm_defs Sj_num_pm_round Sj_num_pm_ti Sj_num_pm_fent Sj_num_pm_int1 Sj_num_pm_int2 Sj_num_pm_int3.
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

Section PMBINT4.
  Variable E : pmbenv.
  Hypothesis OK : pmb_ok E.
  Hypothesis PV : pmb_prov E.
  Notation X := (p_X E).
  Notation DGA := (p_DG E).
  Notation IP := (p_IP E).
  Notation IL := (p_IL E).
  Notation FPT := (p_FPT E).
  Notation FL := (p_FL E).

  Section BODY.
  Variable f : nat.

  Hypothesis HEAD : forall xra xt2 xa0 xa1 xa6 xa7 xs2 xs5 xs9 xs11 xt4 xt6 mm len D p w8 w32 w40 w48,
    PMBINV E mm len D w8 (Z_to_bv 64 761) (Z_to_bv 64 (p_N E)) w32 w40 w48 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (X / 8)) ->
    (IP <= p <= (IP + IL))%Z -> (0 <= D <= 769)%Z -> (19 * len <= 2 * D + 38)%Z -> (p <> (IP + IL) -> 19 * len <= 2 * D + 0)%Z -> ((IP + IL) - p <= Z.of_nat f)%Z ->
    evt bsegs (pmb_post E) (PMB E 0xea4c4 xra (Z_to_bv 64 (DGA / 8 + 2147450880)) (Z_to_bv 64 2147450880) xt2 (Z_to_bv 64 (X + 8)) (Z_to_bv 64 8) xa0 xa1 (Z_to_bv 64 769) (Z_to_bv 64 DGA) (Z_to_bv 64 (X + 496)) (Z_to_bv 64 p) xa6 xa7 xs2 (Z_to_bv 64 10) (Z_to_bv 64 X) xs5 (Z_to_bv 64 1) (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 17) xs9 (Z_to_bv 64 19) xs11 (Z_to_bv 64 177376) xt4 (Z_to_bv 64 (IP + IL)) xt6 mm).

  Lemma in_L1 : forall (g : nat) xra xa0 xa1 xa7 xs5 xs11 xt6 mm len D p cn w8 w32 w40 w48,
    PMBINV E mm len D w8 (Z_to_bv 64 761) (Z_to_bv 64 (p_N E)) w32 w40 w48 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (X / 8)) ->
    (19 - cn <= Z.of_nat g)%Z ->
    (IP <= p < (IP + IL))%Z ->
    (0 <= cn <= 18)%Z ->
    (D <= 769)%Z ->
    (cn <= D)%Z ->
    (19 * len <= 2 * (D - cn) + 0)%Z ->
    ((IP + IL) - p <= Z.of_nat f + 1)%Z ->
    (1 <= cn -> (IP + IL) - p <= Z.of_nat f)%Z ->
    evt bsegs (pmb_post E) (PMB E 0xea70c xra (Z_to_bv 64 (DGA / 8 + 2147450880)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (cn + 769 - D)) (Z_to_bv 64 (X + 8)) (Z_to_bv 64 8) xa0 xa1 (Z_to_bv 64 769) (Z_to_bv 64 DGA) (Z_to_bv 64 (X + 496)) (Z_to_bv 64 p) (Z_to_bv 64 p) xa7 (Z_to_bv 64 (D + 1)) (Z_to_bv 64 10) (Z_to_bv 64 X) xs5 (Z_to_bv 64 1) (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 17) (Z_to_bv 64 cn) (Z_to_bv 64 19) xs11 (Z_to_bv 64 177376) (Z_to_bv 64 18446744073709550847) (Z_to_bv 64 (IP + IL)) xt6 mm).
  Proof using OK PV HEAD.
    intros g. induction g as [|g IH]; intros until w48; intros INV Hg Hp Hcn HD HcD HB Hm1 Hm2; [exfalso; lia|].
    pose proof INV as INV0. pm_open INV0. pm_env OK. pm_prov PV. assert (DV : IsData xt6) by exact I.
    bstep.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xebc38%Z => u_trap pc
      | 0xeb018%Z => first [ pose proof INV as INVT; replace (D)%Z with 769%Z in INVT by lia; eapply evt_eq; [| eapply (pm_ti E OK PV) with (len := len) (p := p) (cn := cn)]; [num_st_eq | exact INVT | lia | lia] | fail 100 "cut" pc ]
      | 0xea79c%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMBINVg E m1 len (D + 1) w8 (Z_to_bv 64 761) (Z_to_bv 64 (p_N E)) w32 w40 w48 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (X / 8)) ((D + 1) < PMB_NORM_DG)%Z) by (pm_close_with ltac:(intros HN; apply NB; lia))); eapply evt_eq; [| eapply ((in_preadd E OK PV f HEAD)) with (len := len) (D := (D + 1)%Z) (p := (p + 1)%Z) (cn := (cn + 1)%Z)]; [num_st_eq | exact INV1 | lia | lia | lia | lia | lia | lia | lia] | fail 100 "cut" pc ]
      | 0xea70c%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMBINVg E m1 len (D + 1) w8 (Z_to_bv 64 761) (Z_to_bv 64 (p_N E)) w32 w40 w48 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (X / 8)) ((D + 1) < PMB_NORM_DG)%Z) by (pm_close_with ltac:(intros HN; apply NB; lia))); eapply evt_eq; [| eapply IH with (len := len) (D := (D + 1)%Z) (p := (p + 1)%Z) (cn := (cn + 1)%Z)]; [num_st_eq | exact INV1 | lia | lia | lia | lia | lia | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma in_prel1 : forall xra xt2 xa0 xa1 xa6 xa7 xs2 xs5 xs11 xt4 xt6 mm len D p cn w8 w32 w40 w48,
    PMBINV E mm len D w8 (Z_to_bv 64 761) (Z_to_bv 64 (p_N E)) w32 w40 w48 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (X / 8)) ->
    (IP <= p < (IP + IL))%Z ->
    (0 <= cn <= 18)%Z ->
    (D <= 769)%Z ->
    (cn <= D)%Z ->
    (19 * len <= 2 * (D - cn) + 0)%Z ->
    ((IP + IL) - p <= Z.of_nat f + 1)%Z ->
    (1 <= cn -> (IP + IL) - p <= Z.of_nat f)%Z ->
    evt bsegs (pmb_post E) (PMB E 0xea6dc xra (Z_to_bv 64 (DGA / 8 + 2147450880)) (Z_to_bv 64 2147450880) xt2 (Z_to_bv 64 (X + 8)) (Z_to_bv 64 8) xa0 xa1 (Z_to_bv 64 769) (Z_to_bv 64 DGA) (Z_to_bv 64 (X + 496)) (Z_to_bv 64 p) xa6 xa7 xs2 (Z_to_bv 64 10) (Z_to_bv 64 X) xs5 (Z_to_bv 64 1) (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 17) (Z_to_bv 64 cn) (Z_to_bv 64 19) xs11 (Z_to_bv 64 177376) xt4 (Z_to_bv 64 (IP + IL)) xt6 mm).
  Proof using OK PV HEAD.
    intros until w48. intros INV Hp Hcn HD HcD HB Hm1 Hm2. pose proof INV as INV0. pm_open INV0. pm_env OK. pm_prov PV. assert (DV : IsData xt6) by exact I.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xebc38%Z => u_trap pc
      | 0xea70c%Z => first [ eapply evt_eq; [| eapply (in_L1 19%nat) with (len := len) (D := D) (p := p) (cn := cn)]; [num_st_eq | exact INV | lia | lia | lia | lia | lia | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  End BODY.

End PMBINT4.
