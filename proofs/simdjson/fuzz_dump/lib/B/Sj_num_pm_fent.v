(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjNumber SjNumU SjNumN.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_rtf Sj_num_akit Sj_num_amem
  Sj_num_iface Sj_num_bkit Sj_num_bdefs Sj_num_pm_kit Sj_num_pm_defs Sj_num_pm_round Sj_num_pm_tf Sj_num_pm_frac1 Sj_num_pm_frac2 Sj_num_pm_frac3 Sj_num_pm_frac4 Sj_num_pm_frac5.
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

Section PMBFENT.
  Variable E : pmbenv.
  Hypothesis OK : pmb_ok E.
  Hypothesis PV : pmb_prov E.
  Notation X := (p_X E).
  Notation DGA := (p_DG E).
  Notation IP := (p_IP E).
  Notation IL := (p_IL E).
  Notation FPT := (p_FPT E).
  Notation FL := (p_FL E).

  Lemma pm_fe_66c : forall xra xt2 xs0 xs1 xa0 xa1 xa5 xa6 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt5 xt6 mm len D w8 w16 w24 w32 w40 w48 w56 p,
    PMBINV E mm len D w8 w16 w24 w32 w40 w48 w56 (Z_to_bv 64 (X / 8)) ->
    FPT <> 0%Z ->
    (0 <= D <= 769)%Z ->
    (19 * len <= 2 * D + 38)%Z ->
    (FPT <= p <= FPT + FL)%Z ->
    evt bsegs (pmb_post E) (PMB E 0xea6ec xra (Z_to_bv 64 (DGA / 8 + 2147450880)) (Z_to_bv 64 2147450880) xt2 xs0 xs1 xa0 xa1 (Z_to_bv 64 769) (Z_to_bv 64 DGA) (Z_to_bv 64 p) xa5 xa6 xa7 xs2 xs3 (Z_to_bv 64 X) xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 176064) (Z_to_bv 64 (FPT + FL)) xt5 xt6 mm).
  Proof using OK PV.
    intros until p. intros INV HF HD HB Hp. pose proof INV as INV0. pm_open INV0. pm_env OK. pm_prov PV. destruct SPN4 as [?|SPN4]; [exfalso; lia|].
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xeb878%Z => first [ eapply (pm_exit E OK) with (dg := D) (len := len); [exact INV | lia | lia] | fail 100 "cut" pc ]
      | 0xea784%Z => first [ eapply evt_eq; [| eapply (fr_body E OK PV (Z.to_nat (FPT + FL - p)) (fr_head E OK PV (Z.to_nat (FPT + FL - p)))) with (len := len) (D := D) (p := p)]; [num_st_eq | pm_close_with ltac:(exact NB) | exact HF | lia | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_fe_Z1b : forall (f : nat) (p : Z) xra xt2 xs0 xs1 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt5 xt6 mm len D w8 w16 w24 w32 w40 w48 w56,
    PMBINV E mm len D w8 w16 w24 w32 w40 w48 w56 (Z_to_bv 64 (X / 8)) ->
    FPT <> 0%Z ->
    (0 <= D <= 769)%Z ->
    (19 * len <= 2 * D + 38)%Z ->
    (FPT <= p < FPT + FL)%Z ->
    (FPT + FL - p <= Z.of_nat f)%Z ->
    evt bsegs (pmb_post E) (PMB E 0xeb084 xra (Z_to_bv 64 (DGA / 8 + 2147450880)) (Z_to_bv 64 2147450880) xt2 xs0 xs1 (Z_to_bv 64 (FPT + FL)) (Z_to_bv 64 p) (Z_to_bv 64 769) (Z_to_bv 64 DGA) (Z_to_bv 64 p) (Z_to_bv 64 48) (Z_to_bv 64 18446744073709551615) xa7 xs2 xs3 (Z_to_bv 64 X) xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 176064) (Z_to_bv 64 (FPT + FL)) xt5 xt6 mm).
  Proof using OK PV.
    intros f. induction f as [|f IH]; intros until w56; intros INV HF HD HB Hp Hf; [exfalso; lia|].
    pose proof INV as INV0. pm_open INV0. pm_env OK. pm_prov PV. destruct SPN4 as [?|SPN4]; [exfalso; lia|].
    bstep.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xeb8b4%Z => u_trap pc
      | 0xea6ec%Z => first [ first [ eapply evt_eq; [| eapply pm_fe_66c with (len := len) (D := D) (p := p)]; [num_st_eq | exact INV | exact HF | lia | lia | lia] | eapply evt_eq; [| eapply pm_fe_66c with (len := len) (D := D) (p := (FPT + FL)%Z)]; [num_st_eq | exact INV | exact HF | lia | lia | lia] ] | fail 100 "cut" pc ]
      | 0xeb084%Z => first [ eapply evt_eq; [| eapply (IH (p + 1)%Z) with (len := len) (D := D)]; [num_st_eq | exact INV | exact HF | lia | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_fe_fec : forall xra xt2 xs0 xs1 xa0 xa1 xa6 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt5 xt6 mm len D w8 w16 w24 w32 w40 w48 w56 p,
    PMBINV E mm len D w8 w16 w24 w32 w40 w48 w56 (Z_to_bv 64 (X / 8)) ->
    FPT <> 0%Z ->
    (0 <= D <= 769)%Z ->
    (19 * len <= 2 * D + 38)%Z ->
    (FPT <= p <= FPT + FL)%Z ->
    evt bsegs (pmb_post E) (PMB E 0xeb06c xra (Z_to_bv 64 (DGA / 8 + 2147450880)) (Z_to_bv 64 2147450880) xt2 xs0 xs1 xa0 xa1 (Z_to_bv 64 769) (Z_to_bv 64 DGA) (Z_to_bv 64 p) (Z_to_bv 64 p) xa6 xa7 xs2 xs3 (Z_to_bv 64 X) xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 176064) (Z_to_bv 64 (FPT + FL)) xt5 xt6 mm).
  Proof using OK PV.
    intros until p. intros INV HF HD HB Hp. pose proof INV as INV0. pm_open INV0. pm_env OK. pm_prov PV. destruct SPN4 as [?|SPN4]; [exfalso; lia|].
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xeb8b4%Z => u_trap pc
      | 0xeb878%Z => first [ eapply (pm_exit E OK) with (dg := D) (len := len); [exact INV | lia | lia] | fail 100 "cut" pc ]
      | 0xeb084%Z => first [ eapply evt_eq; [| eapply (pm_fe_Z1b (Z.to_nat (FPT + FL - p)) p) with (len := len) (D := D)]; [num_st_eq | exact INV | exact HF | lia | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_fe_Z8b : forall (f : nat) (k : Z) xra xt2 xs1 xa0 xa6 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 mm len D w8 w16 w24 w32 w40 w48 w56,
    PMBINV E mm len D w8 w16 w24 w32 w40 w48 w56 (Z_to_bv 64 (X / 8)) ->
    FPT <> 0%Z ->
    (0 <= D <= 769)%Z ->
    (19 * len <= 2 * D + 38)%Z ->
    (0 <= k)%Z ->
    (FPT + 8 * k + 8 <= FPT + FL)%Z ->
    (FL - 8 * k <= Z.of_nat f)%Z ->
    evt bsegs (pmb_post E) (PMB E 0xeae40 xra (Z_to_bv 64 (DGA / 8 + 2147450880)) (Z_to_bv 64 2147450880) xt2 (Z_to_bv 64 7) xs1 xa0 (Z_to_bv 64 (FL - 8 * k)) (Z_to_bv 64 769) (Z_to_bv 64 DGA) (Z_to_bv 64 (FPT + 8 * k)) (Z_to_bv 64 (FPT + 8 * k)) xa6 (Z_to_bv 64 8) xs2 xs3 (Z_to_bv 64 X) xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 176064) (Z_to_bv 64 (FPT + FL)) (Z_to_bv 64 (2147450880 + FPT / 8 + k)) (Z_to_bv 64 3472328296227680304) mm).
  Proof using OK PV.
    intros f. induction f as [|f IH]; intros until w56; intros INV HF HD HB Hk Hp8 Hf; [exfalso; lia|].
    pose proof INV as INV0. pm_open INV0. pm_env OK. pm_prov PV. destruct SPN4 as [?|SPN4]; [exfalso; lia|].
    bstep.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xeb8b4%Z => u_trap pc
      | 0xeb06c%Z => first [ first [ eapply evt_eq; [| eapply pm_fe_fec with (len := len) (D := D) (p := (FPT + 8 * k)%Z)]; [num_st_eq | exact INV | exact HF | lia | lia | lia] | eapply evt_eq; [| eapply pm_fe_fec with (len := len) (D := D) (p := (FPT + 8 * k + 8)%Z)]; [num_st_eq | exact INV | exact HF | lia | lia | lia] ] | fail 100 "cut" pc ]
      | 0xeae40%Z => first [ eapply evt_eq; [| eapply (IH (k + 1)%Z) with (len := len) (D := D)]; [num_st_eq | exact INV | exact HF | lia | lia | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_fent : forall xra xt2 xs0 xs1 xa0 xa1 xa4 xa5 xa6 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt4 xt5 xt6 mm len D w8 w16 w32 w40 w48 w56,
    PMBINV E mm len D w8 w16 (Z_to_bv 64 (p_N E)) w32 w40 w48 w56 (Z_to_bv 64 (X / 8)) ->
    (0 <= D <= 769)%Z ->
    (19 * len <= 2 * D + 38)%Z ->
    evt bsegs (pmb_post E) (PMB E 0xea684 xra (Z_to_bv 64 (DGA / 8 + 2147450880)) (Z_to_bv 64 2147450880) xt2 xs0 xs1 xa0 xa1 (Z_to_bv 64 769) (Z_to_bv 64 DGA) xa4 xa5 xa6 xa7 xs2 xs3 (Z_to_bv 64 X) xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 176064) xt4 xt5 xt6 mm).
  Proof using OK PV.
    intros until w56. intros INV HD HB. pose proof INV as INV0. pm_open INV0. pm_env OK. pm_prov PV.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xeb8b4%Z => u_trap pc
      | 0xeb878%Z => first [ eapply (pm_exit E OK) with (dg := D) (len := len); [exact INV | lia | lia] | fail 100 "cut" pc ]
      | 0xea6ec%Z => first [ destruct SPN4 as [?|SPN4]; [exfalso; lia|]; assert (HF : FPT <> 0%Z) by lia; eapply evt_eq; [| eapply pm_fe_66c with (len := len) (D := D) (p := FPT)]; [num_st_eq | exact INV | exact HF | lia | lia | lia] | fail 100 "cut" pc ]
      | 0xeb06c%Z => first [ destruct SPN4 as [?|SPN4]; [exfalso; lia|]; assert (HF : FPT <> 0%Z) by lia; eapply evt_eq; [| eapply pm_fe_fec with (len := len) (D := D) (p := FPT)]; [num_st_eq | exact INV | exact HF | lia | lia | lia] | fail 100 "cut" pc ]
      | 0xeae40%Z => first [ destruct SPN4 as [?|SPN4]; [exfalso; lia|]; assert (HF : FPT <> 0%Z) by lia; eapply evt_eq; [| eapply (pm_fe_Z8b (Z.to_nat FL) 0%Z) with (len := len) (D := D)]; [num_st_eq | exact INV | exact HF | lia | lia | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.
End PMBFENT.
