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
  Sj_num_iface Sj_num_bkit Sj_num_bdefs Sj_num_pm_kit Sj_num_pm_defs Sj_num_pm_round Sj_num_pm_tf Sj_num_pm_frac1.
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

Section PMBFRAC2.
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
    evt bsegs (pmb_post E) (PMB E 0xf9864 (Z_to_bv 64 17) (Z_to_bv 64 (DGA / 8 + 2147450880)) (Z_to_bv 64 2147450880) xt2 (Z_to_bv 64 8) xs1 xa0 (Z_to_bv 64 (X + 496)) (Z_to_bv 64 769) (Z_to_bv 64 DGA) (Z_to_bv 64 p) xa5 xa6 xa7 (Z_to_bv 64 10) (Z_to_bv 64 19) (Z_to_bv 64 X) (Z_to_bv 64 1) (Z_to_bv 64 18446744073709551615) xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 194848) (Z_to_bv 64 (FPT + FL)) xt5 (Z_to_bv 64 (X + 8)) mm).

  Lemma fr_SM : forall (g : nat) (i : Z) xt2 xa0 xs8 xs11 mm len D p cn (ys v : word) w8 w16 w32 w40 w48,
    PMBINV E mm len D w8 w16 (Z_to_bv 64 761) w32 w40 w48 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (X / 8)) ->
    (0 < bv_unsigned ys)%Z ->
    (0 <= i < len)%Z ->
    (len - i <= Z.of_nat g)%Z ->
    FPT <> 0%Z ->
    (FPT <= p <= (FPT + FL))%Z ->
    (1 <= cn <= 19)%Z ->
    (D <= 768)%Z ->
    (cn <= D)%Z ->
    (cn = 19 \/ p = (FPT + FL))%Z ->
    (19 * len <= 2 * (D - cn) + 38)%Z ->
    ((FPT + FL) - p <= Z.of_nat f)%Z ->
    evt bsegs (pmb_post E) (PMB E 0xf9ba4 (Z_to_bv 64 17) (Z_to_bv 64 (DGA / 8 + 2147450880)) (Z_to_bv 64 2147450880) xt2 (Z_to_bv 64 8) ys xa0 (Z_to_bv 64 (X + 496)) (Z_to_bv 64 769) (Z_to_bv 64 DGA) (Z_to_bv 64 p) (Z_to_bv 64 (X + 8 * i)) (Z_to_bv 64 ((X + 496) / 8 + 2147450880)) (Z_to_bv 64 (63 - i)) (Z_to_bv 64 10) (Z_to_bv 64 19) (Z_to_bv 64 X) (Z_to_bv 64 1) (Z_to_bv 64 18446744073709551615) v xs8 (Z_to_bv 64 len) (Z_to_bv 64 (X + 8 * i)) xs11 (Z_to_bv 64 194848) (Z_to_bv 64 (FPT + FL)) (Z_to_bv 64 (len - i)) (Z_to_bv 64 (X + 8)) mm).
  Proof using OK PV HEAD.
    intros g. induction g as [|g IH]; intros until w48; intros INV HY Hi Hg HF Hp Hcn HD HcD HC HB Hm; [exfalso; lia|].
    destruct (Z.eq_dec i (len - 1)) as [IT|IT].
    - pose proof INV as INV0. pm_open INV0. pm_env OK. pm_prov PV. destruct SPN4 as [?|SPN4]; [exfalso; lia|]. bkstep.
      bkwalk ltac:(fun pc => lazymatch pc with
      | 0xfa99c%Z => u_trap pc
      | 0xf9ba4%Z => first [ exfalso; lia | fail 100 "cut" pc ]
      | 0xf9c2c%Z => first [ fold_limbz; lazymatch goal with | XA : u8arr _ _ _ (upd_bytes (upd_bytes _ _ _) _ _) |- _ => num_cur_mem ltac:(fun m1 => assert (INV1 : PMBINVg E m1 (len + 1) D w8 w16 (Z_to_bv 64 761) w32 w40 w48 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (X / 8)) (D < PMB_NORM_DG)%Z) by (pm_close_with ltac:(intros _; apply bignorm_b_push; [lia | lia | lia |]; rewrite unsigned_lit_wrap; change (2 ^ 64)%Z with 18446744073709551616%Z; lazymatch goal with KB : (_ mod _ <> 0)%Z |- _ => exact KB end))); eapply evt_eq; [| eapply ((fr_sadd E OK PV f HEAD)) with (len := (len + 1)%Z) (D := D) (p := p) (cn := cn) (v := v)]; [num_st_eq | exact INV1 | exact HF | lia | lia | lia | lia | lia | lia | lia] | _ => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMBINVg E m1 len D w8 w16 (Z_to_bv 64 761) w32 w40 w48 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (X / 8)) (D < PMB_NORM_DG)%Z) by (pm_close_with ltac:(intros HN; apply bignorm_b_mul_nocarry; [apply NB; exact HN | lia | lia | lia | exact HY | lazymatch goal with KB : (_ mod _ = 0)%Z |- _ => exact KB end]))); eapply evt_eq; [| eapply ((fr_sadd E OK PV f HEAD)) with (len := len) (D := D) (p := p) (cn := cn) (v := v)]; [num_st_eq | exact INV1 | exact HF | lia | lia | lia | lia | lia | lia | lia] | num_cur_mem ltac:(fun m1 => assert (INV1 : PMBINVg E m1 len D w8 w16 (Z_to_bv 64 761) w32 w40 w48 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (X / 8)) (D < PMB_NORM_DG)%Z) by (pm_close_with ltac:(intro; exfalso; lia))); eapply evt_eq; [| eapply ((fr_sadd E OK PV f HEAD)) with (len := len) (D := D) (p := p) (cn := cn) (v := v)]; [num_st_eq | exact INV1 | exact HF | lia | lia | lia | lia | lia | lia | lia] ] end | fail 100 "cut" pc ]
      end).
    - pose proof INV as INV0. pm_open INV0. pm_env OK. pm_prov PV. destruct SPN4 as [?|SPN4]; [exfalso; lia|]. assert (DC : IsData xs11) by exact I. bstep.
      bwalk ltac:(fun pc => lazymatch pc with
      | 0xfa99c%Z => u_trap pc
      | 0xf9c2c%Z => first [ exfalso; lia | fail 100 "cut" pc ]
      | 0xf9ba4%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMBINVg E m1 len D w8 w16 (Z_to_bv 64 761) w32 w40 w48 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (X / 8)) (D < PMB_NORM_DG)%Z) by (pm_close_with ltac:(intros HN; apply bignorm_b_upd_other; [apply NB; exact HN | lia | rewrite ?length_le8; lia | lia]))); eapply evt_eq; [| eapply (IH (i + 1)%Z) with (len := len) (D := D) (p := p) (cn := cn) (ys := ys) (v := v)]; [num_st_eq | exact INV1 | exact HY | lia | lia | exact HF | lia | lia | lia | lia | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  End BODY.

End PMBFRAC2.
