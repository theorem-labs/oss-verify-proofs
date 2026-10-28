(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjNumber SjNumU.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Sj_num_kitu Sj_num_kitn Sj_num_pm_defs Sj_num_pm_round Sj_num_pm_tf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ solve_load_base | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].
Local Ltac nnorm ::= nnorm_u.

Section PMUFRAC.
  Variable E : pmuenv.
  Hypothesis OK : pmu_ok E.
  Notation X := (p_X E).
  Notation IP := (p_IP E).
  Notation IL := (p_IL E).
  Notation FPT := (p_FPT E).
  Notation FL := (p_FL E).

  Section BODY.
  Variable f : nat.

  Hypothesis HEAD : forall xra xs0 xs1 xa0 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 mm len D p v16,
    PMUINV E mm len D v16 ->
    FPT <> 0%Z ->
    (FPT <= p <= (FPT + FL))%Z -> (0 <= D <= 769)%Z -> (19 * len <= 2 * D + 76)%Z -> (p <> (FPT + FL) -> 19 * len <= 2 * D + 38)%Z -> ((FPT + FL) - p <= Z.of_nat f)%Z ->
    evt usegs (pmu_post E) (PM E 0x5d6fc xra (Z_to_bv 64 (X + 8)) (Z_to_bv 64 8) (Z_to_bv 64 9) xs0 xs1 xa0 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 769) (Z_to_bv 64 (X + 504)) (Z_to_bv 64 116824) (Z_to_bv 64 p) (Z_to_bv 64 (FPT + FL)) (Z_to_bv 64 761) (Z_to_bv 64 X) xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 10) (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 17) (Z_to_bv 64 19) mm).

  Lemma fr_push : forall xra xs0 xs1 xa0 xs3 xs4 xs5 xs6 xs9 xs10 xs11 mm len D p cn (v : word) P v16,
    PMUINVg E mm len D v16 P ->
    (bv_unsigned v <> 0)%Z ->
    (len <= 61)%Z ->
    FPT <> 0%Z ->
    (FPT <= p <= (FPT + FL))%Z ->
    (1 <= cn <= 19)%Z ->
    (D <= 768)%Z ->
    (cn <= D)%Z ->
    (cn = 19 \/ p = (FPT + FL))%Z ->
    (19 * len <= 2 * (D - cn) + 57)%Z ->
    ((FPT + FL) - p <= Z.of_nat f)%Z ->
    evt usegs (pmu_post E) (PM E 0x5d6e4 xra (Z_to_bv 64 (X + 8)) (Z_to_bv 64 8) (Z_to_bv 64 9) xs0 xs1 xa0 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 769) (Z_to_bv 64 (X + 504)) (Z_to_bv 64 116824) (Z_to_bv 64 p) (Z_to_bv 64 (FPT + FL)) (Z_to_bv 64 761) (Z_to_bv 64 X) xs3 xs4 xs5 xs6 v (Z_to_bv 64 len) xs9 xs10 xs11 (Z_to_bv 64 10) (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 17) (Z_to_bv 64 19) mm).
  Proof using OK HEAD.
    intros until v16. intros INV HV Hl HF Hp Hcn HD HcD HC HB Hm. pm_open INV. pm_env OK.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5e158%Z => u_trap pc
      | 0x5d6fc%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINVg E m1 (len + 1) D v16 (D < PMU_NORM_DG)%Z) by (pm_close_with ltac:(intros _; apply bignorm_b_push; [lia | lia | lia | exact HV]))); eapply evt_eq; [| eapply HEAD with (len := (len + 1)%Z) (D := D) (p := p)]; [num_st_eq | exact INV1 | exact HF | lia | lia | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma fr_wrapped : forall xra xs0 xs1 xa0 xs3 xs4 xs5 xs6 xs7 xs9 xs10 xs11 mm len D p cn P v16,
    PMUINVg E mm len D v16 P ->
    (1 <= len)%Z ->
    FPT <> 0%Z ->
    (FPT <= p <= (FPT + FL))%Z ->
    (1 <= cn <= 19)%Z ->
    (D <= 768)%Z ->
    (cn <= D)%Z ->
    (cn = 19 \/ p = (FPT + FL))%Z ->
    (19 * len <= 2 * (D - cn) + 57)%Z ->
    ((FPT + FL) - p <= Z.of_nat f)%Z ->
    evt usegs (pmu_post E) (PM E 0x5d9c8 xra (Z_to_bv 64 (X + 8)) (Z_to_bv 64 8) (Z_to_bv 64 9) xs0 xs1 xa0 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 769) (Z_to_bv 64 (X + 504)) (Z_to_bv 64 116824) (Z_to_bv 64 p) (Z_to_bv 64 (FPT + FL)) (Z_to_bv 64 761) (Z_to_bv 64 X) xs3 xs4 xs5 xs6 xs7 (Z_to_bv 64 len) xs9 xs10 xs11 (Z_to_bv 64 10) (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 17) (Z_to_bv 64 19) mm).
  Proof using OK HEAD.
    intros until v16. intros INV Hl1 HF Hp Hcn HD HcD HC HB Hm. pose proof INV as INV0. pm_open INV0. pm_env OK.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5d6fc%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINVg E m1 len D v16 (D < PMU_NORM_DG)%Z) by (pm_close_with ltac:(intro; exfalso; lia))); eapply evt_eq; [| eapply HEAD with (len := len) (D := D) (p := p)]; [num_st_eq | exact INV1 | exact HF | lia | lia | lia | lia | lia] | fail 100 "cut" pc ]
      | 0x5d6e4%Z => first [ eapply evt_eq; [| eapply (fr_push) with (len := len) (D := D) (p := p) (cn := cn) (v := Z_to_bv 64 1) (P := P)]; [num_st_eq | exact INV | rewrite unsigned_lit by lia; lia | lia | exact HF | lia | lia | lia | lia | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma fr_CA : forall (g : nat) (j : Z) xra xs0 xa0 xs3 xs4 xs5 xs6 xs10 xs11 mm len D p cn v16,
    PMUINVg E mm len D v16 (j <= len - 2 /\ D < PMU_NORM_DG)%Z ->
    (0 <= j <= len - 1)%Z ->
    (len - 1 - j <= Z.of_nat g)%Z ->
    FPT <> 0%Z ->
    (FPT <= p <= (FPT + FL))%Z ->
    (1 <= cn <= 19)%Z ->
    (D <= 768)%Z ->
    (cn <= D)%Z ->
    (cn = 19 \/ p = (FPT + FL))%Z ->
    (19 * len <= 2 * (D - cn) + 57)%Z ->
    ((FPT + FL) - p <= Z.of_nat f)%Z ->
    evt usegs (pmu_post E) (PM E 0x5d9a0 xra (Z_to_bv 64 (X + 8)) (Z_to_bv 64 8) (Z_to_bv 64 9) xs0 (Z_to_bv 64 (X + 8 + 8 * j)) xa0 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 769) (Z_to_bv 64 (X + 504)) (Z_to_bv 64 116824) (Z_to_bv 64 p) (Z_to_bv 64 (FPT + FL)) (Z_to_bv 64 761) (Z_to_bv 64 X) xs3 xs4 xs5 xs6 (Z_to_bv 64 (len - 1 - j)) (Z_to_bv 64 len) (Z_to_bv 64 (18446744073709551112 + 8 * j)) xs10 xs11 (Z_to_bv 64 10) (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 17) (Z_to_bv 64 19) mm).
  Proof using OK HEAD.
    intros g. induction g as [|g IH]; intros until v16; intros INV Hj Hg HF Hp Hcn HD HcD HC HB Hm.
    - pose proof INV as INV0. pm_open INV0. pm_env OK. nstep.
      uwalk ltac:(fun pc => lazymatch pc with
      | 0x5e158%Z => u_trap pc
      | 0x5d9c8%Z => first [ eapply evt_eq; [| eapply (fr_wrapped) with (len := len) (D := D) (p := p) (cn := cn)]; [num_st_eq | exact INV | lia | exact HF | lia | lia | lia | lia | lia | lia | lia] | fail 100 "cut" pc ]
      end).
    - destruct (Z.eq_dec j (len - 2)) as [JT|JT].
      +
        pose proof INV as INV0. pm_open INV0. pm_env OK. ukstep.
        ukwalk ltac:(fun pc => lazymatch pc with
      | 0x5e158%Z => u_trap pc
      | 0x5d9c8%Z => first [ exfalso; lia | fail 100 "cut" pc ]
      | 0x5d6fc%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINVg E m1 len D v16 (D < PMU_NORM_DG)%Z) by (pm_close_with ltac:(intros _; apply bignorm_b_upd_top; [lia | lia | lia |]; rewrite unsigned_lit_wrap; fold_limbz; lazymatch goal with KB : _ <> 0%Z |- _ => exact KB end))); eapply evt_eq; [| eapply HEAD with (len := len) (D := D) (p := p)]; [num_st_eq | exact INV1 | exact HF | lia | lia | lia | lia | lia] | fail 100 "cut" pc ]
      | 0x5d9a0%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINVg E m1 len D v16 ((j + 1) <= len - 2 /\ D < PMU_NORM_DG)%Z) by (pm_close_with ltac:(intros [? _]; exfalso; lia))); eapply evt_eq; [| eapply (IH (j + 1)%Z) with (len := len) (D := D) (p := p) (cn := cn)]; [num_st_eq | exact INV1 | lia | lia | exact HF | lia | lia | lia | lia | lia | lia | lia] | fail 100 "cut" pc ]
      end).
      + pose proof INV as INV0. pm_open INV0. pm_env OK. nstep.
        uwalk ltac:(fun pc => lazymatch pc with
      | 0x5e158%Z => u_trap pc
      | 0x5d9c8%Z => first [ eapply evt_eq; [| eapply (fr_wrapped) with (len := len) (D := D) (p := p) (cn := cn)]; [num_st_eq | exact INV | lia | exact HF | lia | lia | lia | lia | lia | lia | lia] | fail 100 "cut" pc ]
      | 0x5d6fc%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINVg E m1 len D v16 (D < PMU_NORM_DG)%Z) by (pm_close_with ltac:(intros HN; apply bignorm_b_upd_other; [apply NB; lia | lia | rewrite ?length_le8; lia | lia]))); eapply evt_eq; [| eapply HEAD with (len := len) (D := D) (p := p)]; [num_st_eq | exact INV1 | exact HF | lia | lia | lia | lia | lia] | fail 100 "cut" pc ]
      | 0x5d9a0%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINVg E m1 len D v16 ((j + 1) <= len - 2 /\ D < PMU_NORM_DG)%Z) by (pm_close_with ltac:(intros [? HN]; apply bignorm_b_upd_other; [apply NB; lia | lia | rewrite ?length_le8; lia | lia]))); eapply evt_eq; [| eapply (IH (j + 1)%Z) with (len := len) (D := D) (p := p) (cn := cn)]; [num_st_eq | exact INV1 | lia | lia | exact HF | lia | lia | lia | lia | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma fr_sadd : forall xra xs0 xs1 xa0 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 mm len D p cn (v : word) v16,
    PMUINV E mm len D v16 ->
    FPT <> 0%Z ->
    (FPT <= p <= (FPT + FL))%Z ->
    (1 <= cn <= 19)%Z ->
    (D <= 768)%Z ->
    (cn <= D)%Z ->
    (cn = 19 \/ p = (FPT + FL))%Z ->
    (19 * len <= 2 * (D - cn) + 57)%Z ->
    ((FPT + FL) - p <= Z.of_nat f)%Z ->
    evt usegs (pmu_post E) (PM E 0x5d978 xra (Z_to_bv 64 (X + 8)) (Z_to_bv 64 8) (Z_to_bv 64 9) xs0 xs1 xa0 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 769) (Z_to_bv 64 (X + 504)) (Z_to_bv 64 116824) (Z_to_bv 64 p) (Z_to_bv 64 (FPT + FL)) (Z_to_bv 64 761) (Z_to_bv 64 X) xs3 xs4 xs5 xs6 v xs8 xs9 xs10 xs11 (Z_to_bv 64 10) (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 17) (Z_to_bv 64 19) mm).
  Proof using OK HEAD.
    intros until v16. intros INV HF Hp Hcn HD HcD HC HB Hm. pose proof INV as INV0. pm_open INV0. pm_env OK.
    ukwalk ltac:(fun pc => lazymatch pc with
      | 0x5e158%Z => u_trap pc
      | 0x5d6fc%Z => first [ first [ eapply evt_eq; [| eapply HEAD with (len := len) (D := D) (p := p)]; [num_st_eq | exact INV | exact HF | lia | lia | lia | lia | lia] | fold_limbz; num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINVg E m1 len D v16 (D < PMU_NORM_DG)%Z) by (pm_close_with ltac:(intros HN; destruct (Z.eq_dec len 1) as [L1|L1]; [ apply bignorm_b_upd_top; [lia | lia | lia |]; rewrite unsigned_lit_wrap; specialize (NB HN); destruct NB as [?|NB]; [lia|];   replace (8 * (len - 1))%Z with (X - X)%Z in NB by lia;   lazymatch type of NB with bv_unsigned ?w <> _ => pose proof (bv_unsigned_in_range 64 w) as RW; unfold bv_modulus in RW; change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z in RW end;   change (2 ^ 64)%Z with 18446744073709551616%Z; lia | apply bignorm_b_upd_other; [apply NB; exact HN | lia | rewrite ?length_le8; lia | lia] ]))); eapply evt_eq; [| eapply HEAD with (len := len) (D := D) (p := p)]; [num_st_eq | exact INV1 | exact HF | lia | lia | lia | lia | lia] ] | fail 100 "cut" pc ]
      | 0x5d6e4%Z => first [ eapply evt_eq; [| eapply (fr_push) with (len := len) (D := D) (p := p) (cn := cn) (v := v) (P := (D < PMU_NORM_DG)%Z)]; [num_st_eq | exact INV | assumption | lia | exact HF | lia | lia | lia | lia | lia | lia | lia] | fail 100 "cut" pc ]
      | 0x5d9a0%Z => first [ fold_limbz; num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINVg E m1 len D v16 (0 <= len - 2 /\ D < PMU_NORM_DG)%Z) by (pm_close_with ltac:(intros [HJ HN]; apply bignorm_b_upd_other; [apply NB; exact HN | lia | rewrite ?length_le8; lia | lia]))); eapply evt_eq; [| eapply (fr_CA (Z.to_nat len) 0%Z) with (len := len) (D := D) (p := p) (cn := cn)]; [num_st_eq | exact INV1 | lia | lia | exact HF | lia | lia | lia | lia | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma fr_SM : forall (g : nat) (i : Z) xs0 xa0 xs3 xs4 xs5 xs6 xs9 mm len D p cn (ys v : word) v16,
    PMUINV E mm len D v16 ->
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
    evt usegs (pmu_post E) (PM E 0x5d928 (Z_to_bv 64 (X + 8 * len)) (Z_to_bv 64 (X + 8)) (Z_to_bv 64 8) (Z_to_bv 64 9) xs0 (Z_to_bv 64 (X + 8 * i)) xa0 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 769) (Z_to_bv 64 (X + 504)) (Z_to_bv 64 116824) (Z_to_bv 64 p) (Z_to_bv 64 (FPT + FL)) (Z_to_bv 64 761) (Z_to_bv 64 X) xs3 xs4 xs5 xs6 v (Z_to_bv 64 len) xs9 (Z_to_bv 64 (63 - i)) ys (Z_to_bv 64 10) (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 17) (Z_to_bv 64 19) mm).
  Proof using OK HEAD.
    intros g. induction g as [|g IH]; intros until v16; intros INV HY Hi Hg HF Hp Hcn HD HcD HC HB Hm; [exfalso; lia|].
    destruct (Z.eq_dec i (len - 1)) as [IT|IT].
    - pose proof INV as INV0. pm_open INV0. pm_env OK. ukstep.
      ukwalk ltac:(fun pc => lazymatch pc with
      | 0x5e158%Z => u_trap pc
      | 0x5d928%Z => first [ exfalso; lia | fail 100 "cut" pc ]
      | 0x5d978%Z => first [ fold_limbz; lazymatch goal with | XA : u8arr _ _ _ (upd_bytes (upd_bytes _ _ _) _ _) |- _ => num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINVg E m1 (len + 1) D v16 (D < PMU_NORM_DG)%Z) by (pm_close_with ltac:(intros _; apply bignorm_b_push; [lia | lia | lia |]; rewrite unsigned_lit_wrap; change (2 ^ 64)%Z with 18446744073709551616%Z; lazymatch goal with KB : (_ mod _ <> 0)%Z |- _ => exact KB end))); eapply evt_eq; [| eapply (fr_sadd) with (len := (len + 1)%Z) (D := D) (p := p) (cn := cn) (v := v)]; [num_st_eq | exact INV1 | exact HF | lia | lia | lia | lia | lia | lia | lia] | KB : (_ mod _ = 0)%Z |- _ => num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINVg E m1 len D v16 (D < PMU_NORM_DG)%Z) by (pm_close_with ltac:(intros HN; apply bignorm_b_mul_nocarry; [apply NB; exact HN | lia | lia | lia | exact HY | lazymatch goal with KB : (_ mod _ = 0)%Z |- _ => exact KB end]))); eapply evt_eq; [| eapply (fr_sadd) with (len := len) (D := D) (p := p) (cn := cn) (v := v)]; [num_st_eq | exact INV1 | exact HF | lia | lia | lia | lia | lia | lia | lia] | _ => num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINVg E m1 len D v16 (D < PMU_NORM_DG)%Z) by (pm_close_with ltac:(intro; exfalso; lia))); eapply evt_eq; [| eapply (fr_sadd) with (len := len) (D := D) (p := p) (cn := cn) (v := v)]; [num_st_eq | exact INV1 | exact HF | lia | lia | lia | lia | lia | lia | lia] end | fail 100 "cut" pc ]
      end).
    - pose proof INV as INV0. pm_open INV0. pm_env OK. assert (DC : IsData xs6) by exact I. nstep.
      uwalk ltac:(fun pc => lazymatch pc with
      | 0x5e158%Z => u_trap pc
      | 0x5d978%Z => first [ exfalso; lia | fail 100 "cut" pc ]
      | 0x5d928%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINVg E m1 len D v16 (D < PMU_NORM_DG)%Z) by (pm_close_with ltac:(intros HN; apply bignorm_b_upd_other; [apply NB; exact HN | lia | rewrite ?length_le8; lia | lia]))); eapply evt_eq; [| eapply (IH (i + 1)%Z) with (len := len) (D := D) (p := p) (cn := cn) (ys := ys) (v := v)]; [num_st_eq | exact INV1 | exact HY | lia | lia | exact HF | lia | lia | lia | lia | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma fr_add : forall xra xs0 xs1 xa0 xs3 xs4 xs5 xs6 xs8 xs9 xs11 mm len D p cn (v : word) v16,
    PMUINV E mm len D v16 ->
    FPT <> 0%Z ->
    (FPT <= p <= (FPT + FL))%Z ->
    (1 <= cn <= 19)%Z ->
    (D <= 768)%Z ->
    (cn <= D)%Z ->
    (cn = 19 \/ p = (FPT + FL))%Z ->
    (19 * len <= 2 * (D - cn) + 38)%Z ->
    ((FPT + FL) - p <= Z.of_nat f)%Z ->
    evt usegs (pmu_post E) (PM E 0x5d8e8 xra (Z_to_bv 64 (X + 8)) (Z_to_bv 64 8) (Z_to_bv 64 9) xs0 xs1 xa0 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 769) (Z_to_bv 64 (X + 504)) (Z_to_bv 64 116824) (Z_to_bv 64 p) (Z_to_bv 64 (FPT + FL)) (Z_to_bv 64 761) (Z_to_bv 64 X) xs3 xs4 xs5 xs6 v xs8 xs9 (Z_to_bv 64 cn) xs11 (Z_to_bv 64 10) (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 17) (Z_to_bv 64 19) mm).
  Proof using OK HEAD.
    intros until v16. intros INV HF Hp Hcn HD HcD HC HB Hm. pose proof INV as INV0. pm_open INV0. pm_env OK.
    ukwalk ltac:(fun pc => lazymatch pc with
      | 0x5e158%Z => u_trap pc
      | 0x5d978%Z => first [ eapply evt_eq; [| eapply (fr_sadd) with (len := len) (D := D) (p := p) (cn := cn) (v := v)]; [num_st_eq | exact INV | exact HF | lia | lia | lia | lia | lia | lia | lia] | fail 100 "cut" pc ]
      | 0x5d928%Z => first [ fold_limbz; eapply evt_eq; [| eapply (fr_SM (Z.to_nat len) 0%Z) with (len := len) (D := D) (p := p) (cn := cn) (v := v)]; [num_st_eq | exact INV | replace (116824 + 8 * cn - 116824)%Z with (8 * cn)%Z by lia; apply pmu_pow10_nz; lia | lia | lia | exact HF | lia | lia | lia | lia | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma fr_L1 : forall (g : nat) xra xs0 xs1 xa0 xs3 xs4 xs5 xs6 xs7 xs10 mm len D p cn v16,
    PMUINV E mm len D v16 ->
    (19 - cn <= Z.of_nat g)%Z ->
    FPT <> 0%Z ->
    (FPT <= p < (FPT + FL))%Z ->
    (0 <= cn <= 18)%Z ->
    (D <= 768)%Z ->
    (cn <= D)%Z ->
    (19 * len <= 2 * (D - cn) + 38)%Z ->
    ((FPT + FL) - p <= Z.of_nat f + 1)%Z ->
    (1 <= cn -> (FPT + FL) - p <= Z.of_nat f)%Z ->
    evt usegs (pmu_post E) (PM E 0x5d884 xra (Z_to_bv 64 (X + 8)) (Z_to_bv 64 8) (Z_to_bv 64 9) xs0 xs1 xa0 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 769) (Z_to_bv 64 (X + 504)) (Z_to_bv 64 116824) (Z_to_bv 64 p) (Z_to_bv 64 (FPT + FL)) (Z_to_bv 64 761) (Z_to_bv 64 X) xs3 xs4 xs5 xs6 xs7 (Z_to_bv 64 D) (Z_to_bv 64 cn) xs10 (Z_to_bv 64 p) (Z_to_bv 64 10) (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 17) (Z_to_bv 64 19) mm).
  Proof using OK HEAD.
    intros g. induction g as [|g IH]; intros until v16; intros INV Hg HF Hp Hcn HD HcD HB Hm1 Hm2; [exfalso; lia|].
    pose proof INV as INV0. pm_open INV0. pm_env OK. assert (DV : IsData xs7) by exact I.
    nstep.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5e158%Z => u_trap pc
      | 0x5d8e8%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINVg E m1 len (D + 1) v16 ((D + 1) < PMU_NORM_DG)%Z) by (pm_close_with ltac:(intros HN; apply NB; lia))); eapply evt_eq; [| eapply (fr_add) with (len := len) (D := (D + 1)%Z) (p := (p + 1)%Z) (cn := (cn + 1)%Z)]; [num_st_eq | exact INV1 | exact HF | lia | lia | lia | lia | lia | lia | lia] | fail 100 "cut" pc ]
      | 0x5db58%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINVg E m1 len (D + 1) v16 ((D + 1) < PMU_NORM_DG)%Z) by (pm_close_with ltac:(intros HN; apply NB; lia))); replace (D + 1)%Z with 769%Z in INV1 by lia; eapply evt_eq; [| eapply (pm_tf E OK) with (len := len) (p := (p + 1)%Z) (cn := (cn + 1)%Z)]; [num_st_eq | exact INV1 | exact HF | lia | lia] | fail 100 "cut" pc ]
      | 0x5d884%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINVg E m1 len (D + 1) v16 ((D + 1) < PMU_NORM_DG)%Z) by (pm_close_with ltac:(intros HN; apply NB; lia))); eapply evt_eq; [| eapply IH with (len := len) (D := (D + 1)%Z) (p := (p + 1)%Z) (cn := (cn + 1)%Z)]; [num_st_eq | exact INV1 | lia | exact HF | lia | lia | lia | lia | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma fr_820 : forall xra xs0 xs1 xa0 xs3 xs4 xs5 xs6 xs7 xs10 xs11 mm len D p cn v16,
    PMUINV E mm len D v16 ->
    FPT <> 0%Z ->
    (FPT <= p < (FPT + FL))%Z ->
    (0 <= cn <= 18)%Z ->
    (D <= 769)%Z ->
    (cn <= D)%Z ->
    (19 * len <= 2 * (D - cn) + 38)%Z ->
    ((FPT + FL) - p <= Z.of_nat f + 1)%Z ->
    (1 <= cn -> (FPT + FL) - p <= Z.of_nat f)%Z ->
    evt usegs (pmu_post E) (PM E 0x5d87c xra (Z_to_bv 64 (X + 8)) (Z_to_bv 64 8) (Z_to_bv 64 9) xs0 xs1 xa0 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 769) (Z_to_bv 64 (X + 504)) (Z_to_bv 64 116824) (Z_to_bv 64 p) (Z_to_bv 64 (FPT + FL)) (Z_to_bv 64 761) (Z_to_bv 64 X) xs3 xs4 xs5 xs6 xs7 (Z_to_bv 64 D) (Z_to_bv 64 cn) xs10 xs11 (Z_to_bv 64 10) (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 17) (Z_to_bv 64 19) mm).
  Proof using OK HEAD.
    intros until v16. intros INV HF Hp Hcn HD HcD HB Hm1 Hm2. pose proof INV as INV0. pm_open INV0. pm_env OK. assert (DV : IsData xs7) by exact I.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5e158%Z => u_trap pc
      | 0x5d8e8%Z => first [ exfalso; lia | fail 100 "cut" pc ]
      | 0x5db58%Z => first [ pose proof INV as INV1; replace (D)%Z with 769%Z in INV1 by lia; eapply evt_eq; [| eapply (pm_tf E OK) with (len := len) (p := p) (cn := cn)]; [num_st_eq | exact INV1 | exact HF | lia | lia] | fail 100 "cut" pc ]
      | 0x5d884%Z => first [ eapply evt_eq; [| eapply (fr_L1 19%nat) with (len := len) (D := D) (p := p) (cn := cn)]; [num_st_eq | exact INV | lia | exact HF | lia | lia | lia | lia | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma fr_body : forall xra xs0 xs1 xa0 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 mm len D p v16,
    PMUINV E mm len D v16 ->
    FPT <> 0%Z ->
    (FPT <= p < (FPT + FL))%Z ->
    (0 <= D <= 769)%Z ->
    (19 * len <= 2 * D + 38)%Z ->
    ((FPT + FL) - p <= Z.of_nat f + 1)%Z ->
    evt usegs (pmu_post E) (PM E 0x5d700 xra (Z_to_bv 64 (X + 8)) (Z_to_bv 64 8) (Z_to_bv 64 9) xs0 xs1 xa0 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 769) (Z_to_bv 64 (X + 504)) (Z_to_bv 64 116824) (Z_to_bv 64 p) (Z_to_bv 64 (FPT + FL)) (Z_to_bv 64 761) (Z_to_bv 64 X) xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 10) (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 17) (Z_to_bv 64 19) mm).
  Proof using OK HEAD.
    intros until v16. intros INV HF Hp HD HB Hm. pose proof INV as INV0. pm_open INV0. pm_env OK.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5e158%Z => u_trap pc
      | 0x5d87c%Z => first [ first [ eapply evt_eq; [| eapply (fr_820) with (len := len) (D := D) (p := p) (cn := 0%Z)]; [num_st_eq | exact INV | exact HF | lia | lia | lia | lia | lia | lia | lia] | num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINVg E m1 len (D + 8) v16 ((D + 8) < PMU_NORM_DG)%Z) by (pm_close_with ltac:(intros HN; apply NB; lia))); eapply evt_eq; [| eapply (fr_820) with (len := len) (D := (D + 8)%Z) (p := (p + 8)%Z) (cn := 8%Z)]; [num_st_eq | exact INV1 | exact HF | lia | lia | lia | lia | lia | lia | lia] | num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINVg E m1 len (D + 16) v16 ((D + 16) < PMU_NORM_DG)%Z) by (pm_close_with ltac:(intros HN; apply NB; lia))); eapply evt_eq; [| eapply (fr_820) with (len := len) (D := (D + 16)%Z) (p := (p + 16)%Z) (cn := 16%Z)]; [num_st_eq | exact INV1 | exact HF | lia | lia | lia | lia | lia | lia | lia] ] | fail 100 "cut" pc ]
      | 0x5d8e8%Z => first [ first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINVg E m1 len (D + 8) v16 ((D + 8) < PMU_NORM_DG)%Z) by (pm_close_with ltac:(intros HN; apply NB; lia))); eapply evt_eq; [| eapply (fr_add) with (len := len) (D := (D + 8)%Z) (p := (p + 8)%Z) (cn := 8%Z)]; [num_st_eq | exact INV1 | exact HF | lia | lia | lia | lia | lia | lia | lia] | num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINVg E m1 len (D + 16) v16 ((D + 16) < PMU_NORM_DG)%Z) by (pm_close_with ltac:(intros HN; apply NB; lia))); eapply evt_eq; [| eapply (fr_add) with (len := len) (D := (D + 16)%Z) (p := (p + 16)%Z) (cn := 16%Z)]; [num_st_eq | exact INV1 | exact HF | lia | lia | lia | lia | lia | lia | lia] ] | fail 100 "cut" pc ]
      | 0x5db58%Z => first [ first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINVg E m1 len (D + 8) v16 ((D + 8) < PMU_NORM_DG)%Z) by (pm_close_with ltac:(intros HN; apply NB; lia))); replace (D + 8)%Z with 769%Z in INV1 by lia; eapply evt_eq; [| eapply (pm_tf E OK) with (len := len) (p := (p + 8)%Z) (cn := 8%Z)]; [num_st_eq | exact INV1 | exact HF | lia | lia] | num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINVg E m1 len (D + 16) v16 ((D + 16) < PMU_NORM_DG)%Z) by (pm_close_with ltac:(intros HN; apply NB; lia))); replace (D + 16)%Z with 769%Z in INV1 by lia; eapply evt_eq; [| eapply (pm_tf E OK) with (len := len) (p := (p + 16)%Z) (cn := 16%Z)]; [num_st_eq | exact INV1 | exact HF | lia | lia] ] | fail 100 "cut" pc ]
      end).
  Qed.
  End BODY.

  Theorem fr_head : forall (f : nat) xra xs0 xs1 xa0 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 mm len D p v16,
    PMUINV E mm len D v16 ->
    FPT <> 0%Z ->
    (FPT <= p <= (FPT + FL))%Z -> (0 <= D <= 769)%Z -> (19 * len <= 2 * D + 76)%Z -> (p <> (FPT + FL) -> 19 * len <= 2 * D + 38)%Z -> ((FPT + FL) - p <= Z.of_nat f)%Z ->
    evt usegs (pmu_post E) (PM E 0x5d6fc xra (Z_to_bv 64 (X + 8)) (Z_to_bv 64 8) (Z_to_bv 64 9) xs0 xs1 xa0 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 769) (Z_to_bv 64 (X + 504)) (Z_to_bv 64 116824) (Z_to_bv 64 p) (Z_to_bv 64 (FPT + FL)) (Z_to_bv 64 761) (Z_to_bv 64 X) xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 10) (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 17) (Z_to_bv 64 19) mm).
  Proof using OK.
    intros f. induction f as [|f IH]; intros until v16; intros INV HF Hp HD HB1 HB2 Hm; pose proof INV as INV0; pm_open INV0; pm_env OK.
    - uwalk ltac:(fun pc => lazymatch pc with
      | 0x5e11c%Z => first [ eapply (pm_exit E OK) with (dg := D); [exact INV | lia | lia] | fail 100 "cut" pc ]
      end).
    - uwalk ltac:(fun pc => lazymatch pc with
      | 0x5e11c%Z => first [ eapply (pm_exit E OK) with (dg := D); [exact INV | lia | lia] | fail 100 "cut" pc ]
      | 0x5d700%Z => first [ eapply evt_eq; [| eapply (fr_body f IH) with (len := len) (D := D) (p := p)]; [num_st_eq | exact INV | exact HF | lia | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.
End PMUFRAC.
