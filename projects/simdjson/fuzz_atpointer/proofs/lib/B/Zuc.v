(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.AS Require Import Zp7 Z1b.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS Z119 FP Z10q.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Sj Require Import Zpe SjNumU SjNumN.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Rnd Zso Zvm.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.B Require Import Layout Zks D_defs D_kit D_clx Zpm Zpl Zq2 Sj_rtf Zqc Zqd
  Zsl Zqh Zqf Zuj Zu5 Zul Zum Zu8 Zu9 Zua Zub.
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

Section PMBFRAC5.
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

  Hypothesis HEAD : forall xt2 xs1 xa0 xa5 xa6 xa7 xs7 xs8 xs9 xs10 xs11 xt5 mm len D p w8 w16 w32 w40 w48,
    PMBINV E mm len D w8 w16 (Z_to_bv 64 761) w32 w40 w48 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (X / 8)) ->
    FPT <> 0%Z ->
    (FPT <= p <= (FPT + FL))%Z -> (0 <= D <= 769)%Z -> (19 * len <= 2 * D + 76)%Z -> (p <> (FPT + FL) -> 19 * len <= 2 * D + 38)%Z -> ((FPT + FL) - p <= Z.of_nat f)%Z ->
    evt bsegs (pmb_post E) (PMB E 0xd3738 (Z_to_bv 64 17) (Z_to_bv 64 (DGA / 8 + 2147450880)) (Z_to_bv 64 2147450880) xt2 (Z_to_bv 64 8) xs1 xa0 (Z_to_bv 64 (X + 496)) (Z_to_bv 64 769) (Z_to_bv 64 DGA) (Z_to_bv 64 p) xa5 xa6 xa7 (Z_to_bv 64 10) (Z_to_bv 64 19) (Z_to_bv 64 X) (Z_to_bv 64 1) (Z_to_bv 64 18446744073709551615) xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 174880) (Z_to_bv 64 (FPT + FL)) xt5 (Z_to_bv 64 (X + 8)) mm).

  Lemma fr_body : forall xt2 xs1 xa0 xa5 xa6 xa7 xs7 xs8 xs9 xs10 xs11 xt5 mm len D p w8 w16 w32 w40 w48,
    PMBINV E mm len D w8 w16 (Z_to_bv 64 761) w32 w40 w48 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (X / 8)) ->
    FPT <> 0%Z ->
    (FPT <= p < (FPT + FL))%Z ->
    (0 <= D <= 769)%Z ->
    (19 * len <= 2 * D + 38)%Z ->
    ((FPT + FL) - p <= Z.of_nat f + 1)%Z ->
    evt bsegs (pmb_post E) (PMB E 0xd3740 (Z_to_bv 64 17) (Z_to_bv 64 (DGA / 8 + 2147450880)) (Z_to_bv 64 2147450880) xt2 (Z_to_bv 64 8) xs1 xa0 (Z_to_bv 64 (X + 496)) (Z_to_bv 64 769) (Z_to_bv 64 DGA) (Z_to_bv 64 p) xa5 xa6 xa7 (Z_to_bv 64 10) (Z_to_bv 64 19) (Z_to_bv 64 X) (Z_to_bv 64 1) (Z_to_bv 64 18446744073709551615) xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 174880) (Z_to_bv 64 (FPT + FL)) xt5 (Z_to_bv 64 (X + 8)) mm).
  Proof using OK PV HEAD.
    intros until w48. intros INV HF Hp HD HB Hm. pose proof INV as INV0. pm_open INV0. pm_env OK. pm_prov PV. destruct SPN4 as [?|SPN4]; [exfalso; lia|].
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xd4870%Z => u_trap pc
      | 0xd3954%Z => first [ first [ eapply evt_eq; [| eapply ((fr_prel1 E OK PV f HEAD)) with (len := len) (D := D) (p := p) (cn := 0%Z)]; [num_st_eq | exact INV | exact HF | lia | lia | lia | lia | lia | lia | lia] | num_cur_mem ltac:(fun m1 => assert (INV1 : PMBINVg E m1 len (D + 8) w8 w16 (Z_to_bv 64 761) w32 w40 w48 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (X / 8)) ((D + 8) < PMB_NORM_DG)%Z) by (pm_close_with ltac:(intros HN; apply NB; lia))); eapply evt_eq; [| eapply ((fr_prel1 E OK PV f HEAD)) with (len := len) (D := (D + 8)%Z) (p := (p + 8)%Z) (cn := 8%Z)]; [num_st_eq | exact INV1 | exact HF | lia | lia | lia | lia | lia | lia | lia] | num_cur_mem ltac:(fun m1 => assert (INV1 : PMBINVg E m1 len (D + 16) w8 w16 (Z_to_bv 64 761) w32 w40 w48 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (X / 8)) ((D + 16) < PMB_NORM_DG)%Z) by (pm_close_with ltac:(intros HN; apply NB; lia))); eapply evt_eq; [| eapply ((fr_prel1 E OK PV f HEAD)) with (len := len) (D := (D + 16)%Z) (p := (p + 16)%Z) (cn := 16%Z)]; [num_st_eq | exact INV1 | exact HF | lia | lia | lia | lia | lia | lia | lia] ] | fail 100 "cut" pc ]
      | 0xd3a0c%Z => first [ first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMBINVg E m1 len (D + 8) w8 w16 (Z_to_bv 64 761) w32 w40 w48 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (X / 8)) ((D + 8) < PMB_NORM_DG)%Z) by (pm_close_with ltac:(intros HN; apply NB; lia))); eapply evt_eq; [| eapply ((fr_preadd E OK PV f HEAD)) with (len := len) (D := (D + 8)%Z) (p := (p + 8)%Z) (cn := 8%Z)]; [num_st_eq | exact INV1 | exact HF | lia | lia | lia | lia | lia | lia | lia] | num_cur_mem ltac:(fun m1 => assert (INV1 : PMBINVg E m1 len (D + 16) w8 w16 (Z_to_bv 64 761) w32 w40 w48 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (X / 8)) ((D + 16) < PMB_NORM_DG)%Z) by (pm_close_with ltac:(intros HN; apply NB; lia))); eapply evt_eq; [| eapply ((fr_preadd E OK PV f HEAD)) with (len := len) (D := (D + 16)%Z) (p := (p + 16)%Z) (cn := 16%Z)]; [num_st_eq | exact INV1 | exact HF | lia | lia | lia | lia | lia | lia | lia] ] | fail 100 "cut" pc ]
      end).
  Qed.

  End BODY.

  Theorem fr_head : forall (f : nat) xt2 xs1 xa0 xa5 xa6 xa7 xs7 xs8 xs9 xs10 xs11 xt5 mm len D p w8 w16 w32 w40 w48,
    PMBINV E mm len D w8 w16 (Z_to_bv 64 761) w32 w40 w48 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (X / 8)) ->
    FPT <> 0%Z ->
    (FPT <= p <= (FPT + FL))%Z -> (0 <= D <= 769)%Z -> (19 * len <= 2 * D + 76)%Z -> (p <> (FPT + FL) -> 19 * len <= 2 * D + 38)%Z -> ((FPT + FL) - p <= Z.of_nat f)%Z ->
    evt bsegs (pmb_post E) (PMB E 0xd3738 (Z_to_bv 64 17) (Z_to_bv 64 (DGA / 8 + 2147450880)) (Z_to_bv 64 2147450880) xt2 (Z_to_bv 64 8) xs1 xa0 (Z_to_bv 64 (X + 496)) (Z_to_bv 64 769) (Z_to_bv 64 DGA) (Z_to_bv 64 p) xa5 xa6 xa7 (Z_to_bv 64 10) (Z_to_bv 64 19) (Z_to_bv 64 X) (Z_to_bv 64 1) (Z_to_bv 64 18446744073709551615) xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 174880) (Z_to_bv 64 (FPT + FL)) xt5 (Z_to_bv 64 (X + 8)) mm).
  Proof using OK PV.
    intros f. induction f as [|f IH]; intros until w48; intros INV HF Hp HD HB1 HB2 Hm; pose proof INV as INV0. pm_open INV0. pm_env OK. pm_prov PV. destruct SPN4 as [?|SPN4]; [exfalso; lia|].
    - bwalk ltac:(fun pc => lazymatch pc with
      | 0xd4834%Z => first [ eapply (pm_exit E OK) with (dg := D) (len := len); [exact INV | lia | lia] | fail 100 "cut" pc ]
      end).
    - bwalk ltac:(fun pc => lazymatch pc with
      | 0xd4834%Z => first [ eapply (pm_exit E OK) with (dg := D) (len := len); [exact INV | lia | lia] | fail 100 "cut" pc ]
      | 0xd3740%Z => first [ eapply evt_eq; [| eapply (fr_body f IH) with (len := len) (D := D) (p := p)]; [num_st_eq | exact INV | exact HF | lia | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.
End PMBFRAC5.
