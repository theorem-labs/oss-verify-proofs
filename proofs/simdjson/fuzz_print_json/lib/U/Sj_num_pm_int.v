(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjNumber SjNumU.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Sj_num_kitu Sj_num_kitn Sj_num_pm_defs Sj_num_pm_round Sj_num_pm_ti Sj_num_pm_fent.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ solve_load_base | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].
Local Ltac nnorm ::= nnorm_u.

Section PMUINT.
  Variable E : pmuenv.
  Hypothesis OK : pmu_ok E.
  Notation X := (p_X E).
  Notation IP := (p_IP E).
  Notation IL := (p_IL E).
  Notation FPT := (p_FPT E).
  Notation FL := (p_FL E).

  Section BODY.
  Variable f : nat.

  Hypothesis HEAD : forall xra xt0 xt1 xa0 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 mm len D p,
    PMUINV E mm len D (Z_to_bv 64 761) ->
    (IP <= p <= (IP + IL))%Z -> (0 <= D <= 769)%Z -> (19 * len <= 2 * D + 38)%Z -> (p <> (IP + IL) -> 19 * len <= 2 * D + 0)%Z -> ((IP + IL) - p <= Z.of_nat f)%Z ->
    evt usegs (pmu_post E) (PM E 0x5d360 xra xt0 xt1 (Z_to_bv 64 8) (Z_to_bv 64 19) (Z_to_bv 64 (X + 8)) xa0 (Z_to_bv 64 (X + -72)) (Z_to_bv 64 769) (Z_to_bv 64 (X + 504)) (Z_to_bv 64 116824) (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (IP + IL)) (Z_to_bv 64 p) (Z_to_bv 64 X) xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 9) (Z_to_bv 64 10) (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 17) mm).

  Lemma in_push : forall xra xt0 xt1 xa0 xs3 xs4 xs5 xs6 xs7 xs10 xs11 mm len D p cn (v : word) P,
    PMUINVg E mm len D (Z_to_bv 64 761) P ->
    (bv_unsigned v <> 0)%Z ->
    (len <= 61)%Z ->
    (IP <= p <= (IP + IL))%Z ->
    (1 <= cn <= 19)%Z ->
    (D <= 768)%Z ->
    (cn <= D)%Z ->
    (cn = 19 \/ p = (IP + IL))%Z ->
    (19 * len <= 2 * (D - cn) + 19)%Z ->
    ((IP + IL) - p <= Z.of_nat f)%Z ->
    evt usegs (pmu_post E) (PM E 0x5d63c xra xt0 xt1 (Z_to_bv 64 8) (Z_to_bv 64 19) (Z_to_bv 64 (X + 8)) xa0 (Z_to_bv 64 (X + -72)) (Z_to_bv 64 769) (Z_to_bv 64 (X + 504)) (Z_to_bv 64 116824) (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (IP + IL)) (Z_to_bv 64 p) (Z_to_bv 64 X) xs3 xs4 xs5 xs6 xs7 v (Z_to_bv 64 len) xs10 xs11 (Z_to_bv 64 9) (Z_to_bv 64 10) (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 17) mm).
  Proof using OK HEAD.
    intros until P. intros INV HV Hl Hp Hcn HD HcD HC HB Hm. pm_open INV. pm_env OK.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5e158%Z => u_trap pc
      | 0x5d360%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINVg E m1 (len + 1) D (Z_to_bv 64 761) (D < PMU_NORM_DG)%Z) by (pm_close_with ltac:(intros _; apply bignorm_b_push; [lia | lia | lia | exact HV]))); eapply evt_eq; [| eapply HEAD with (len := (len + 1)%Z) (D := D) (p := p)]; [num_st_eq | exact INV1 | lia | lia | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma in_wrapped : forall xra xt0 xt1 xa0 xs3 xs4 xs5 xs6 xs7 xs8 xs10 xs11 mm len D p cn P,
    PMUINVg E mm len D (Z_to_bv 64 761) P ->
    (1 <= len)%Z ->
    (IP <= p <= (IP + IL))%Z ->
    (1 <= cn <= 19)%Z ->
    (D <= 768)%Z ->
    (cn <= D)%Z ->
    (cn = 19 \/ p = (IP + IL))%Z ->
    (19 * len <= 2 * (D - cn) + 19)%Z ->
    ((IP + IL) - p <= Z.of_nat f)%Z ->
    evt usegs (pmu_post E) (PM E 0x5d630 xra xt0 xt1 (Z_to_bv 64 8) (Z_to_bv 64 19) (Z_to_bv 64 (X + 8)) xa0 (Z_to_bv 64 (X + -72)) (Z_to_bv 64 769) (Z_to_bv 64 (X + 504)) (Z_to_bv 64 116824) (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (IP + IL)) (Z_to_bv 64 p) (Z_to_bv 64 X) xs3 xs4 xs5 xs6 xs7 xs8 (Z_to_bv 64 len) xs10 xs11 (Z_to_bv 64 9) (Z_to_bv 64 10) (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 17) mm).
  Proof using OK HEAD.
    intros until P. intros INV Hl1 Hp Hcn HD HcD HC HB Hm. pose proof INV as INV0. pm_open INV0. pm_env OK.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5d360%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINVg E m1 len D (Z_to_bv 64 761) (D < PMU_NORM_DG)%Z) by (pm_close_with ltac:(intro; exfalso; lia))); eapply evt_eq; [| eapply HEAD with (len := len) (D := D) (p := p)]; [num_st_eq | exact INV1 | lia | lia | lia | lia | lia] | fail 100 "cut" pc ]
      | 0x5d63c%Z => first [ eapply evt_eq; [| eapply (in_push) with (len := len) (D := D) (p := p) (cn := cn) (v := Z_to_bv 64 1) (P := P)]; [num_st_eq | exact INV | rewrite unsigned_lit by lia; lia | lia | lia | lia | lia | lia | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma in_CA : forall (g : nat) (j : Z) xra xt0 xs3 xs4 xs5 xs6 xs7 xs10 xs11 mm len D p cn,
    PMUINVg E mm len D (Z_to_bv 64 761) (j <= len - 2 /\ D < PMU_NORM_DG)%Z ->
    (0 <= j <= len - 1)%Z ->
    (len - 1 - j <= Z.of_nat g)%Z ->
    (IP <= p <= (IP + IL))%Z ->
    (1 <= cn <= 19)%Z ->
    (D <= 768)%Z ->
    (cn <= D)%Z ->
    (cn = 19 \/ p = (IP + IL))%Z ->
    (19 * len <= 2 * (D - cn) + 19)%Z ->
    ((IP + IL) - p <= Z.of_nat f)%Z ->
    evt usegs (pmu_post E) (PM E 0x5d608 xra xt0 (Z_to_bv 64 (len - 1 - j)) (Z_to_bv 64 8) (Z_to_bv 64 19) (Z_to_bv 64 (X + 8)) (Z_to_bv 64 (X + 8 + 8 * j)) (Z_to_bv 64 (X + -72)) (Z_to_bv 64 769) (Z_to_bv 64 (X + 504)) (Z_to_bv 64 116824) (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (IP + IL)) (Z_to_bv 64 p) (Z_to_bv 64 X) xs3 xs4 xs5 xs6 xs7 (Z_to_bv 64 (18446744073709551112 + 8 * j)) (Z_to_bv 64 len) xs10 xs11 (Z_to_bv 64 9) (Z_to_bv 64 10) (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 17) mm).
  Proof using OK HEAD.
    intros g. induction g as [|g IH]; intros until cn; intros INV Hj Hg Hp Hcn HD HcD HC HB Hm.
    - pose proof INV as INV0. pm_open INV0. pm_env OK. nstep.
      uwalk ltac:(fun pc => lazymatch pc with
      | 0x5e158%Z => u_trap pc
      | 0x5d630%Z => first [ eapply evt_eq; [| eapply (in_wrapped) with (len := len) (D := D) (p := p) (cn := cn)]; [num_st_eq | exact INV | lia | lia | lia | lia | lia | lia | lia | lia] | fail 100 "cut" pc ]
      end).
    - destruct (Z.eq_dec j (len - 2)) as [JT|JT].
      +
        pose proof INV as INV0. pm_open INV0. pm_env OK. ukstep.
        ukwalk ltac:(fun pc => lazymatch pc with
      | 0x5e158%Z => u_trap pc
      | 0x5d630%Z => first [ exfalso; lia | fail 100 "cut" pc ]
      | 0x5d360%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINVg E m1 len D (Z_to_bv 64 761) (D < PMU_NORM_DG)%Z) by (pm_close_with ltac:(intros _; apply bignorm_b_upd_top; [lia | lia | lia |]; rewrite unsigned_lit_wrap; fold_limbz; lazymatch goal with KB : _ <> 0%Z |- _ => exact KB end))); eapply evt_eq; [| eapply HEAD with (len := len) (D := D) (p := p)]; [num_st_eq | exact INV1 | lia | lia | lia | lia | lia] | fail 100 "cut" pc ]
      | 0x5d608%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINVg E m1 len D (Z_to_bv 64 761) ((j + 1) <= len - 2 /\ D < PMU_NORM_DG)%Z) by (pm_close_with ltac:(intros [? _]; exfalso; lia))); eapply evt_eq; [| eapply (IH (j + 1)%Z) with (len := len) (D := D) (p := p) (cn := cn)]; [num_st_eq | exact INV1 | lia | lia | lia | lia | lia | lia | lia | lia | lia] | fail 100 "cut" pc ]
      end).
      + pose proof INV as INV0. pm_open INV0. pm_env OK. nstep.
        uwalk ltac:(fun pc => lazymatch pc with
      | 0x5e158%Z => u_trap pc
      | 0x5d630%Z => first [ eapply evt_eq; [| eapply (in_wrapped) with (len := len) (D := D) (p := p) (cn := cn)]; [num_st_eq | exact INV | lia | lia | lia | lia | lia | lia | lia | lia] | fail 100 "cut" pc ]
      | 0x5d360%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINVg E m1 len D (Z_to_bv 64 761) (D < PMU_NORM_DG)%Z) by (pm_close_with ltac:(intros HN; apply bignorm_b_upd_other; [apply NB; lia | lia | rewrite ?length_le8; lia | lia]))); eapply evt_eq; [| eapply HEAD with (len := len) (D := D) (p := p)]; [num_st_eq | exact INV1 | lia | lia | lia | lia | lia] | fail 100 "cut" pc ]
      | 0x5d608%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINVg E m1 len D (Z_to_bv 64 761) ((j + 1) <= len - 2 /\ D < PMU_NORM_DG)%Z) by (pm_close_with ltac:(intros [? HN]; apply bignorm_b_upd_other; [apply NB; lia | lia | rewrite ?length_le8; lia | lia]))); eapply evt_eq; [| eapply (IH (j + 1)%Z) with (len := len) (D := D) (p := p) (cn := cn)]; [num_st_eq | exact INV1 | lia | lia | lia | lia | lia | lia | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma in_sadd : forall xra xt0 xt1 xa0 xs3 xs4 xs5 xs6 xs7 xs9 xs10 xs11 mm len D p cn (v : word),
    PMUINV E mm len D (Z_to_bv 64 761) ->
    (IP <= p <= (IP + IL))%Z ->
    (1 <= cn <= 19)%Z ->
    (D <= 768)%Z ->
    (cn <= D)%Z ->
    (cn = 19 \/ p = (IP + IL))%Z ->
    (19 * len <= 2 * (D - cn) + 19)%Z ->
    ((IP + IL) - p <= Z.of_nat f)%Z ->
    evt usegs (pmu_post E) (PM E 0x5d5e0 xra xt0 xt1 (Z_to_bv 64 8) (Z_to_bv 64 19) (Z_to_bv 64 (X + 8)) xa0 (Z_to_bv 64 (X + -72)) (Z_to_bv 64 769) (Z_to_bv 64 (X + 504)) (Z_to_bv 64 116824) (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (IP + IL)) (Z_to_bv 64 p) (Z_to_bv 64 X) xs3 xs4 xs5 xs6 xs7 v xs9 xs10 xs11 (Z_to_bv 64 9) (Z_to_bv 64 10) (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 17) mm).
  Proof using OK HEAD.
    intros until v. intros INV Hp Hcn HD HcD HC HB Hm. pose proof INV as INV0. pm_open INV0. pm_env OK.
    ukwalk ltac:(fun pc => lazymatch pc with
      | 0x5e158%Z => u_trap pc
      | 0x5d360%Z => first [ first [ eapply evt_eq; [| eapply HEAD with (len := len) (D := D) (p := p)]; [num_st_eq | exact INV | lia | lia | lia | lia | lia] | fold_limbz; num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINVg E m1 len D (Z_to_bv 64 761) (D < PMU_NORM_DG)%Z) by (pm_close_with ltac:(intros HN; destruct (Z.eq_dec len 1) as [L1|L1]; [ apply bignorm_b_upd_top; [lia | lia | lia |]; rewrite unsigned_lit_wrap; specialize (NB HN); destruct NB as [?|NB]; [lia|];   replace (8 * (len - 1))%Z with (X - X)%Z in NB by lia;   lazymatch type of NB with bv_unsigned ?w <> _ => pose proof (bv_unsigned_in_range 64 w) as RW; unfold bv_modulus in RW; change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z in RW end;   change (2 ^ 64)%Z with 18446744073709551616%Z; lia | apply bignorm_b_upd_other; [apply NB; exact HN | lia | rewrite ?length_le8; lia | lia] ]))); eapply evt_eq; [| eapply HEAD with (len := len) (D := D) (p := p)]; [num_st_eq | exact INV1 | lia | lia | lia | lia | lia] ] | fail 100 "cut" pc ]
      | 0x5d63c%Z => first [ eapply evt_eq; [| eapply (in_push) with (len := len) (D := D) (p := p) (cn := cn) (v := v) (P := (D < PMU_NORM_DG)%Z)]; [num_st_eq | exact INV | assumption | lia | lia | lia | lia | lia | lia | lia | lia] | fail 100 "cut" pc ]
      | 0x5d608%Z => first [ fold_limbz; num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINVg E m1 len D (Z_to_bv 64 761) (0 <= len - 2 /\ D < PMU_NORM_DG)%Z) by (pm_close_with ltac:(intros [HJ HN]; apply bignorm_b_upd_other; [apply NB; exact HN | lia | rewrite ?length_le8; lia | lia]))); eapply evt_eq; [| eapply (in_CA (Z.to_nat len) 0%Z) with (len := len) (D := D) (p := p) (cn := cn)]; [num_st_eq | exact INV1 | lia | lia | lia | lia | lia | lia | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma in_SM : forall (g : nat) (i : Z) xt0 xs3 xs4 xs5 xs6 xs7 xs10 mm len D p cn (ys v : word),
    PMUINV E mm len D (Z_to_bv 64 761) ->
    (0 < bv_unsigned ys)%Z ->
    (0 <= i < len)%Z ->
    (len - i <= Z.of_nat g)%Z ->
    (IP <= p <= (IP + IL))%Z ->
    (1 <= cn <= 19)%Z ->
    (D <= 768)%Z ->
    (cn <= D)%Z ->
    (cn = 19 \/ p = (IP + IL))%Z ->
    (19 * len <= 2 * (D - cn) + 0)%Z ->
    ((IP + IL) - p <= Z.of_nat f)%Z ->
    evt usegs (pmu_post E) (PM E 0x5d590 ys xt0 (Z_to_bv 64 (X + 8 * len)) (Z_to_bv 64 8) (Z_to_bv 64 19) (Z_to_bv 64 (X + 8)) (Z_to_bv 64 (X + 8 * i)) (Z_to_bv 64 (X + -72)) (Z_to_bv 64 769) (Z_to_bv 64 (X + 504)) (Z_to_bv 64 116824) (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (IP + IL)) (Z_to_bv 64 p) (Z_to_bv 64 X) xs3 xs4 xs5 xs6 xs7 v (Z_to_bv 64 len) xs10 (Z_to_bv 64 (63 - i)) (Z_to_bv 64 9) (Z_to_bv 64 10) (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 17) mm).
  Proof using OK HEAD.
    intros g. induction g as [|g IH]; intros until v; intros INV HY Hi Hg Hp Hcn HD HcD HC HB Hm; [exfalso; lia|].
    destruct (Z.eq_dec i (len - 1)) as [IT|IT].
    - pose proof INV as INV0. pm_open INV0. pm_env OK. ukstep.
      ukwalk ltac:(fun pc => lazymatch pc with
      | 0x5e158%Z => u_trap pc
      | 0x5d590%Z => first [ exfalso; lia | fail 100 "cut" pc ]
      | 0x5d5e0%Z => first [ fold_limbz; lazymatch goal with | XA : u8arr _ _ _ (upd_bytes (upd_bytes _ _ _) _ _) |- _ => num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINVg E m1 (len + 1) D (Z_to_bv 64 761) (D < PMU_NORM_DG)%Z) by (pm_close_with ltac:(intros _; apply bignorm_b_push; [lia | lia | lia |]; rewrite unsigned_lit_wrap; change (2 ^ 64)%Z with 18446744073709551616%Z; lazymatch goal with KB : (_ mod _ <> 0)%Z |- _ => exact KB end))); eapply evt_eq; [| eapply (in_sadd) with (len := (len + 1)%Z) (D := D) (p := p) (cn := cn) (v := v)]; [num_st_eq | exact INV1 | lia | lia | lia | lia | lia | lia | lia] | KB : (_ mod _ = 0)%Z |- _ => num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINVg E m1 len D (Z_to_bv 64 761) (D < PMU_NORM_DG)%Z) by (pm_close_with ltac:(intros HN; apply bignorm_b_mul_nocarry; [apply NB; exact HN | lia | lia | lia | exact HY | lazymatch goal with KB : (_ mod _ = 0)%Z |- _ => exact KB end]))); eapply evt_eq; [| eapply (in_sadd) with (len := len) (D := D) (p := p) (cn := cn) (v := v)]; [num_st_eq | exact INV1 | lia | lia | lia | lia | lia | lia | lia] | _ => num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINVg E m1 len D (Z_to_bv 64 761) (D < PMU_NORM_DG)%Z) by (pm_close_with ltac:(intro; exfalso; lia))); eapply evt_eq; [| eapply (in_sadd) with (len := len) (D := D) (p := p) (cn := cn) (v := v)]; [num_st_eq | exact INV1 | lia | lia | lia | lia | lia | lia | lia] end | fail 100 "cut" pc ]
      end).
    - pose proof INV as INV0. pm_open INV0. pm_env OK. assert (DC : IsData xt0) by exact I. nstep.
      uwalk ltac:(fun pc => lazymatch pc with
      | 0x5e158%Z => u_trap pc
      | 0x5d5e0%Z => first [ exfalso; lia | fail 100 "cut" pc ]
      | 0x5d590%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINVg E m1 len D (Z_to_bv 64 761) (D < PMU_NORM_DG)%Z) by (pm_close_with ltac:(intros HN; apply bignorm_b_upd_other; [apply NB; exact HN | lia | rewrite ?length_le8; lia | lia]))); eapply evt_eq; [| eapply (IH (i + 1)%Z) with (len := len) (D := D) (p := p) (cn := cn) (ys := ys) (v := v)]; [num_st_eq | exact INV1 | exact HY | lia | lia | lia | lia | lia | lia | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma in_add : forall xra xt0 xt1 xa0 xs3 xs4 xs5 xs6 xs7 xs9 xs10 mm len D p cn (v : word),
    PMUINV E mm len D (Z_to_bv 64 761) ->
    (IP <= p <= (IP + IL))%Z ->
    (1 <= cn <= 19)%Z ->
    (D <= 768)%Z ->
    (cn <= D)%Z ->
    (cn = 19 \/ p = (IP + IL))%Z ->
    (19 * len <= 2 * (D - cn) + 0)%Z ->
    ((IP + IL) - p <= Z.of_nat f)%Z ->
    evt usegs (pmu_post E) (PM E 0x5d550 xra xt0 xt1 (Z_to_bv 64 8) (Z_to_bv 64 19) (Z_to_bv 64 (X + 8)) xa0 (Z_to_bv 64 (X + -72)) (Z_to_bv 64 769) (Z_to_bv 64 (X + 504)) (Z_to_bv 64 116824) (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (IP + IL)) (Z_to_bv 64 p) (Z_to_bv 64 X) xs3 xs4 xs5 xs6 xs7 v xs9 xs10 (Z_to_bv 64 cn) (Z_to_bv 64 9) (Z_to_bv 64 10) (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 17) mm).
  Proof using OK HEAD.
    intros until v. intros INV Hp Hcn HD HcD HC HB Hm. pose proof INV as INV0. pm_open INV0. pm_env OK.
    ukwalk ltac:(fun pc => lazymatch pc with
      | 0x5e158%Z => u_trap pc
      | 0x5d5e0%Z => first [ eapply evt_eq; [| eapply (in_sadd) with (len := len) (D := D) (p := p) (cn := cn) (v := v)]; [num_st_eq | exact INV | lia | lia | lia | lia | lia | lia | lia] | fail 100 "cut" pc ]
      | 0x5d590%Z => first [ fold_limbz; eapply evt_eq; [| eapply (in_SM (Z.to_nat len) 0%Z) with (len := len) (D := D) (p := p) (cn := cn) (v := v)]; [num_st_eq | exact INV | replace (116824 + 8 * cn - 116824)%Z with (8 * cn)%Z by lia; apply pmu_pow10_nz; lia | lia | lia | lia | lia | lia | lia | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma in_L1 : forall (g : nat) xt0 xt1 xa0 xs3 xs4 xs5 xs6 xs7 xs8 xs11 mm len D p cn,
    PMUINV E mm len D (Z_to_bv 64 761) ->
    (19 - cn <= Z.of_nat g)%Z ->
    (IP <= p < (IP + IL))%Z ->
    (0 <= cn <= 18)%Z ->
    (D <= 768)%Z ->
    (cn <= D)%Z ->
    (19 * len <= 2 * (D - cn) + 0)%Z ->
    ((IP + IL) - p <= Z.of_nat f + 1)%Z ->
    (1 <= cn -> (IP + IL) - p <= Z.of_nat f)%Z ->
    evt usegs (pmu_post E) (PM E 0x5d4ec (Z_to_bv 64 p) xt0 xt1 (Z_to_bv 64 8) (Z_to_bv 64 19) (Z_to_bv 64 (X + 8)) xa0 (Z_to_bv 64 (X + -72)) (Z_to_bv 64 769) (Z_to_bv 64 (X + 504)) (Z_to_bv 64 116824) (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (IP + IL)) (Z_to_bv 64 p) (Z_to_bv 64 X) xs3 xs4 xs5 xs6 xs7 xs8 (Z_to_bv 64 D) (Z_to_bv 64 cn) xs11 (Z_to_bv 64 9) (Z_to_bv 64 10) (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 17) mm).
  Proof using OK HEAD.
    intros g. induction g as [|g IH]; intros until cn; intros INV Hg Hp Hcn HD HcD HB Hm1 Hm2; [exfalso; lia|].
    pose proof INV as INV0. pm_open INV0. pm_env OK. assert (DV : IsData xs8) by exact I.
    nstep.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5e158%Z => u_trap pc
      | 0x5d550%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINVg E m1 len (D + 1) (Z_to_bv 64 761) ((D + 1) < PMU_NORM_DG)%Z) by (pm_close_with ltac:(intros HN; apply NB; lia))); eapply evt_eq; [| eapply (in_add) with (len := len) (D := (D + 1)%Z) (p := (p + 1)%Z) (cn := (cn + 1)%Z)]; [num_st_eq | exact INV1 | lia | lia | lia | lia | lia | lia | lia] | fail 100 "cut" pc ]
      | 0x5d9d8%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINVg E m1 len (D + 1) (Z_to_bv 64 761) ((D + 1) < PMU_NORM_DG)%Z) by (pm_close_with ltac:(intros HN; apply NB; lia))); replace (D + 1)%Z with 769%Z in INV1 by lia; eapply evt_eq; [| eapply (pm_ti E OK) with (len := len) (p := (p + 1)%Z) (cn := (cn + 1)%Z)]; [num_st_eq | exact INV1 | lia | lia] | fail 100 "cut" pc ]
      | 0x5d4ec%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINVg E m1 len (D + 1) (Z_to_bv 64 761) ((D + 1) < PMU_NORM_DG)%Z) by (pm_close_with ltac:(intros HN; apply NB; lia))); eapply evt_eq; [| eapply IH with (len := len) (D := (D + 1)%Z) (p := (p + 1)%Z) (cn := (cn + 1)%Z)]; [num_st_eq | exact INV1 | lia | lia | lia | lia | lia | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma in_820 : forall xra xt0 xt1 xa0 xs3 xs4 xs5 xs6 xs7 xs8 xs11 mm len D p cn,
    PMUINV E mm len D (Z_to_bv 64 761) ->
    (IP <= p < (IP + IL))%Z ->
    (0 <= cn <= 18)%Z ->
    (D <= 769)%Z ->
    (cn <= D)%Z ->
    (19 * len <= 2 * (D - cn) + 0)%Z ->
    ((IP + IL) - p <= Z.of_nat f + 1)%Z ->
    (1 <= cn -> (IP + IL) - p <= Z.of_nat f)%Z ->
    evt usegs (pmu_post E) (PM E 0x5d4e4 xra xt0 xt1 (Z_to_bv 64 8) (Z_to_bv 64 19) (Z_to_bv 64 (X + 8)) xa0 (Z_to_bv 64 (X + -72)) (Z_to_bv 64 769) (Z_to_bv 64 (X + 504)) (Z_to_bv 64 116824) (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (IP + IL)) (Z_to_bv 64 p) (Z_to_bv 64 X) xs3 xs4 xs5 xs6 xs7 xs8 (Z_to_bv 64 D) (Z_to_bv 64 cn) xs11 (Z_to_bv 64 9) (Z_to_bv 64 10) (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 17) mm).
  Proof using OK HEAD.
    intros until cn. intros INV Hp Hcn HD HcD HB Hm1 Hm2. pose proof INV as INV0. pm_open INV0. pm_env OK. assert (DV : IsData xs8) by exact I.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5e158%Z => u_trap pc
      | 0x5d550%Z => first [ exfalso; lia | fail 100 "cut" pc ]
      | 0x5d9d8%Z => first [ pose proof INV as INV1; replace (D)%Z with 769%Z in INV1 by lia; eapply evt_eq; [| eapply (pm_ti E OK) with (len := len) (p := p) (cn := cn)]; [num_st_eq | exact INV1 | lia | lia] | fail 100 "cut" pc ]
      | 0x5d4ec%Z => first [ eapply evt_eq; [| eapply (in_L1 19%nat) with (len := len) (D := D) (p := p) (cn := cn)]; [num_st_eq | exact INV | lia | lia | lia | lia | lia | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma in_body : forall xra xt0 xt1 xa0 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 mm len D p,
    PMUINV E mm len D (Z_to_bv 64 761) ->
    (IP <= p < (IP + IL))%Z ->
    (0 <= D <= 769)%Z ->
    (19 * len <= 2 * D + 0)%Z ->
    ((IP + IL) - p <= Z.of_nat f + 1)%Z ->
    evt usegs (pmu_post E) (PM E 0x5d364 xra xt0 xt1 (Z_to_bv 64 8) (Z_to_bv 64 19) (Z_to_bv 64 (X + 8)) xa0 (Z_to_bv 64 (X + -72)) (Z_to_bv 64 769) (Z_to_bv 64 (X + 504)) (Z_to_bv 64 116824) (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (IP + IL)) (Z_to_bv 64 p) (Z_to_bv 64 X) xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 9) (Z_to_bv 64 10) (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 17) mm).
  Proof using OK HEAD.
    intros until p. intros INV Hp HD HB Hm. pose proof INV as INV0. pm_open INV0. pm_env OK.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5e158%Z => u_trap pc
      | 0x5d4e4%Z => first [ first [ eapply evt_eq; [| eapply (in_820) with (len := len) (D := D) (p := p) (cn := 0%Z)]; [num_st_eq | exact INV | lia | lia | lia | lia | lia | lia | lia] | num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINVg E m1 len (D + 8) (Z_to_bv 64 761) ((D + 8) < PMU_NORM_DG)%Z) by (pm_close_with ltac:(intros HN; apply NB; lia))); eapply evt_eq; [| eapply (in_820) with (len := len) (D := (D + 8)%Z) (p := (p + 8)%Z) (cn := 8%Z)]; [num_st_eq | exact INV1 | lia | lia | lia | lia | lia | lia | lia] | num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINVg E m1 len (D + 16) (Z_to_bv 64 761) ((D + 16) < PMU_NORM_DG)%Z) by (pm_close_with ltac:(intros HN; apply NB; lia))); eapply evt_eq; [| eapply (in_820) with (len := len) (D := (D + 16)%Z) (p := (p + 16)%Z) (cn := 16%Z)]; [num_st_eq | exact INV1 | lia | lia | lia | lia | lia | lia | lia] ] | fail 100 "cut" pc ]
      | 0x5d550%Z => first [ first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINVg E m1 len (D + 8) (Z_to_bv 64 761) ((D + 8) < PMU_NORM_DG)%Z) by (pm_close_with ltac:(intros HN; apply NB; lia))); eapply evt_eq; [| eapply (in_add) with (len := len) (D := (D + 8)%Z) (p := (p + 8)%Z) (cn := 8%Z)]; [num_st_eq | exact INV1 | lia | lia | lia | lia | lia | lia | lia] | num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINVg E m1 len (D + 16) (Z_to_bv 64 761) ((D + 16) < PMU_NORM_DG)%Z) by (pm_close_with ltac:(intros HN; apply NB; lia))); eapply evt_eq; [| eapply (in_add) with (len := len) (D := (D + 16)%Z) (p := (p + 16)%Z) (cn := 16%Z)]; [num_st_eq | exact INV1 | lia | lia | lia | lia | lia | lia | lia] ] | fail 100 "cut" pc ]
      | 0x5d9d8%Z => first [ first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINVg E m1 len (D + 8) (Z_to_bv 64 761) ((D + 8) < PMU_NORM_DG)%Z) by (pm_close_with ltac:(intros HN; apply NB; lia))); replace (D + 8)%Z with 769%Z in INV1 by lia; eapply evt_eq; [| eapply (pm_ti E OK) with (len := len) (p := (p + 8)%Z) (cn := 8%Z)]; [num_st_eq | exact INV1 | lia | lia] | num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINVg E m1 len (D + 16) (Z_to_bv 64 761) ((D + 16) < PMU_NORM_DG)%Z) by (pm_close_with ltac:(intros HN; apply NB; lia))); replace (D + 16)%Z with 769%Z in INV1 by lia; eapply evt_eq; [| eapply (pm_ti E OK) with (len := len) (p := (p + 16)%Z) (cn := 16%Z)]; [num_st_eq | exact INV1 | lia | lia] ] | fail 100 "cut" pc ]
      end).
  Qed.
  End BODY.

  Theorem in_head : forall (f : nat) xra xt0 xt1 xa0 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 mm len D p,
    PMUINV E mm len D (Z_to_bv 64 761) ->
    (IP <= p <= (IP + IL))%Z -> (0 <= D <= 769)%Z -> (19 * len <= 2 * D + 38)%Z -> (p <> (IP + IL) -> 19 * len <= 2 * D + 0)%Z -> ((IP + IL) - p <= Z.of_nat f)%Z ->
    evt usegs (pmu_post E) (PM E 0x5d360 xra xt0 xt1 (Z_to_bv 64 8) (Z_to_bv 64 19) (Z_to_bv 64 (X + 8)) xa0 (Z_to_bv 64 (X + -72)) (Z_to_bv 64 769) (Z_to_bv 64 (X + 504)) (Z_to_bv 64 116824) (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (IP + IL)) (Z_to_bv 64 p) (Z_to_bv 64 X) xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 9) (Z_to_bv 64 10) (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 17) mm).
  Proof using OK.
    intros f. induction f as [|f IH]; intros until p; intros INV Hp HD HB1 HB2 Hm; pose proof INV as INV0; pm_open INV0; pm_env OK.
    - uwalk ltac:(fun pc => lazymatch pc with
      | 0x5d658%Z => first [ eapply evt_eq; [| eapply (pm_fent E OK) with (len := len) (D := D)]; [num_st_eq | exact INV | lia | lia] | fail 100 "cut" pc ]
      end).
    - uwalk ltac:(fun pc => lazymatch pc with
      | 0x5d658%Z => first [ eapply evt_eq; [| eapply (pm_fent E OK) with (len := len) (D := D)]; [num_st_eq | exact INV | lia | lia] | fail 100 "cut" pc ]
      | 0x5d364%Z => first [ eapply evt_eq; [| eapply (in_body f IH) with (len := len) (D := D) (p := p)]; [num_st_eq | exact INV | lia | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.
End PMUINT.
