(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjNumber SjNumSwar SjNumU.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Sj_num_kitu Sj_num_kitn Sj_num_kitw Sj_num_sp_defs Sj_num_sp_dc Sj_num_sp_pdefs Sj_num_sp_acc Sj_num_sp_exp Sj_num_ff_defs Sj_num_ff_cf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ solve_load_base | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].
Local Ltac num_abstract_data ::= num_abstract_data_u.
Local Ltac nnorm ::= nnorm_x.

Section FFUPN.
  Hypothesis HSPATH : ffu_spath_stmt.
  Variable E : ffuenv.
  Hypothesis OK : ffu_ok E.
  Notation A := (f_A E).
  Notation TL := (f_TL E).
  Notation FIRST := (f_FIRST E).
  Notation LAST := (f_LAST E).

  Lemma ffu_L5 : forall (f : nat) (c cnt q : Z) xra xt2 xs0 xs1 xa2 xa3 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    FFUINV E mm -> frm0 xfc -> (FIRST < LAST)%Z -> (A <= c < LAST)%Z -> (- (c - A) <= cnt <= 4294967296)%Z ->
    (-9223372036854775808 <= q < 9223372036854775808)%Z -> (LAST - c <= Z.of_nat f)%Z ->
    evt usegs (ffu_post E) (FFS E 0x412c8 xra (Z_to_bv 64 (-1)) (Z_to_bv 64 48) xt2 xs0 xs1 (Z_to_bv 64 FIRST) (Z_to_bv 64 LAST) xa2 xa3 (Z_to_bv 64 c) (Z_to_bv 64 cnt) (Z_to_bv 64 46) (Z_to_bv 64 q)
                               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using HSPATH OK.
    intros f. induction f as [|f IH]; intros until mm; intros INV FRM HLT Hc Hcnt Hq Hf; [exfalso; lia|].
    pose proof INV as INV0. ffu_open INV0. ffu_env OK.
    nstep.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x416f4%Z => u_trap pc
      | 0x416c8%Z => first [ eapply evt_eq; [| eapply (ffu_97c HSPATH E OK)]; [num_st_eq | exact INV | assumption | exact HLT] | fail 100 "cut" pc ]
      | 0x412f4%Z => first [ eapply evt_eq; [| eapply (ffu_5a8 E OK q)]; [num_st_eq | exact INV | assumption | lia] | fail 100 "cut" pc ]
      | 0x412c8%Z => first [ eapply evt_eq; [| eapply (IH (c + 1)%Z _ q)]; [num_st_eq | exact INV | assumption | exact HLT | lia | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma ffu_564 : forall (IP dc q : Z) xra xt0 xt1 xt2 xs0 xs1 xa2 xa3 xa6 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    FFUINV E mm -> frm0 xfc -> (FIRST < LAST)%Z -> (A <= IP < LAST)%Z -> (0 <= dc <= 4294967296)%Z ->
    (-9223372036854775808 <= q < 9223372036854775808)%Z ->
    evt usegs (ffu_post E) (FFS E 0x412b0 xra xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 FIRST) (Z_to_bv 64 LAST) xa2 xa3 (Z_to_bv 64 IP) (Z_to_bv 64 dc) xa6 (Z_to_bv 64 q)
                               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using HSPATH OK.
    intros until mm. intros INV FRM HLT Hip Hdc Hq.
    pose proof INV as INV0. ffu_open INV0. ffu_env OK.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x416f4%Z => u_trap pc
      | 0x416c8%Z => first [ exfalso; lia | fail 100 "cut" pc ]
      | 0x412f4%Z => first [ eapply evt_eq; [| eapply (ffu_5a8 E OK q)]; [num_st_eq | exact INV | assumption | lia] | fail 100 "cut" pc ]
      | 0x412c8%Z => first [ eapply evt_eq; [| eapply (ffu_L5 (Z.to_nat LAST) IP dc q)]; [num_st_eq | exact INV | assumption | exact HLT | lia | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Notation CS pc IP dc ex xra xt0 xt1 xt2 xs0 xs1 xa2 xa3 xa6 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm :=
    (FFS E pc xra xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 FIRST) (Z_to_bv 64 LAST) xa2 xa3 (Z_to_bv 64 IP) (Z_to_bv 64 dc) xa6 (Z_to_bv 64 ex)
         xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).

  Lemma ffu_550 : forall (IP dc ex en : Z) xra xt0 xt1 xt2 xs0 xs1 xa2 xa3 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    FFUINV E mm -> frm0 xfc -> (FIRST < LAST)%Z -> (A <= IP < LAST)%Z -> (0 <= dc <= 4294967296)%Z -> (-2147483648 <= ex <= 0)%Z -> (- EN_MAX <= en <= EN_MAX)%Z ->
    evt usegs (ffu_post E) (CS 0x4129c IP dc ex xra xt0 xt1 xt2 xs0 xs1 xa2 xa3 (Z_to_bv 64 en) xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using HSPATH OK.
    intros until mm. intros INV FRM HLT Hip Hdc Hex Hen. unfold EN_MAX in Hen.
    kwalk ltac:(fun pc => lazymatch pc with
      | 0x416f4%Z => u_trap_b pc
      | 0x412b0%Z => first [ eapply evt_eq; [| eapply (ffu_564 IP dc (ex + en)%Z)]; [num_st_eq | exact INV | assumption | exact HLT | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma ffu_548 : forall (IP dc ex en : Z) xra xt0 xt1 xt2 xs0 xs1 xa2 xa3 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    FFUINV E mm -> frm0 xfc -> (FIRST < LAST)%Z -> (A <= IP < LAST)%Z -> (0 <= dc <= 4294967296)%Z -> (-2147483648 <= ex <= 0)%Z -> (0 <= en <= EN_MAX)%Z ->
    evt usegs (ffu_post E) (CS 0x41294 IP dc ex xra xt0 xt1 xt2 xs0 xs1 xa2 xa3 (Z_to_bv 64 en) xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using HSPATH OK.
    intros until mm. intros INV FRM HLT Hip Hdc Hex Hen.
    kwalk ltac:(fun pc => lazymatch pc with
      | 0x4129c%Z => first [ eapply evt_eq; [| eapply (ffu_550 IP dc ex _)]; [num_st_eq | exact INV | assumption | exact HLT | lia | lia | lia | unfold EN_MAX in *; lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma ffu_L4 : forall (f : nat) (IP dc ex en e : Z) xra xt1 xs0 xs1 xa2 xa3 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xF xfc mm,
    FFUINV E mm -> frm0 xfc -> (FIRST < LAST)%Z -> (A <= IP < LAST)%Z -> (0 <= dc <= 4294967296)%Z -> (-2147483648 <= ex <= 0)%Z -> (0 <= en <= EN_MAX)%Z ->
    (A <= e < LAST)%Z -> (LAST - e <= Z.of_nat f)%Z ->
    evt usegs (ffu_post E) (CS 0x4125c IP dc ex xra (Z_to_bv 64 e) xt1 (Z_to_bv 64 9) xs0 xs1 xa2 xa3 (Z_to_bv 64 en) xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11
                               (Z_to_bv 64 10) (Z_to_bv 64 268435455) (Z_to_bv 64 2) (Z_to_bv 64 e) xF xfc mm).
  Proof using HSPATH OK.
    intros f. induction f as [|f IH]; intros until mm; intros INV FRM HLT Hip Hdc Hex Hen He Hf; [exfalso; lia|].
    pose proof INV as INV0. ffu_open INV0. ffu_env OK. unfold EN_MAX in Hen.
    assert (DR : forall x, (0 <= Z.land x 255 < 256)%Z) by (intros x; rewrite land_255; apply Z.mod_pos_bound; lia).
    kstep.
    kwalk ltac:(fun pc => lazymatch pc with
      | 0x416f4%Z => u_trap_b pc
      | 0x41294%Z => first [ eapply evt_eq; [| eapply (ffu_548 IP dc ex _)]; [num_st_eq | exact INV | assumption | exact HLT | lia | lia | lia |];
                             unfold EN_MAX;
                             repeat match goal with |- context [Z.land ?x 255] => pose proof (DR x); rewrite (land_255 x) in * end; lia
                           | fail 100 "cut" pc ]
      | 0x4125c%Z => first [ eapply evt_eq; [| eapply (IH IP dc ex _ (e + 1)%Z)]; [num_st_eq | exact INV | assumption | exact HLT | lia | lia | lia | | lia | lia];
                             unfold EN_MAX;
                             repeat match goal with |- context [Z.land ?x 255] => pose proof (DR x); rewrite (land_255 x) in * end; lia
                           | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma ffu_478 : forall (IP dc ex p : Z) xra xt0 xt1 xt2 xs0 xs1 xa2 xa3 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    FFUINV E mm -> frm0 xfc -> (FIRST < LAST)%Z -> (A <= IP < LAST)%Z -> (0 <= dc <= 4294967296)%Z -> (-2147483648 <= ex <= 0)%Z -> (A <= p <= LAST)%Z ->
    evt usegs (ffu_post E) (CS 0x411c4 IP dc ex xra xt0 xt1 xt2 xs0 xs1 xa2 xa3 (Z_to_bv 64 p) xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using HSPATH OK.
    intros until mm. intros INV FRM HLT Hip Hdc Hex Hp.
    pose proof INV as INV0. ffu_open INV0. ffu_env OK.
    kwalk ltac:(fun pc => lazymatch pc with
      | 0x416f4%Z => u_trap_b pc
      | 0x412b0%Z => first [ eapply evt_eq; [| eapply (ffu_564 IP dc ex)]; [num_st_eq | exact INV | assumption | exact HLT | lia | lia | lia] | fail 100 "cut" pc ]
      | 0x4125c%Z => first [ eapply evt_eq; [| eapply (ffu_L4 (Z.to_nat LAST) IP dc ex 0%Z _)];
                             [num_st_eq | exact INV | assumption | exact HLT | lia | lia | lia | unfold EN_MAX; lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Notation BS pc IP IL FPT p xra xt0 xt1 xt2 xs0 xs1 xa2 xa3 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm :=
    (FFS E pc xra xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 FIRST) (Z_to_bv 64 LAST) xa2 xa3 (Z_to_bv 64 IP) (Z_to_bv 64 IL) (Z_to_bv 64 p) (Z_to_bv 64 FPT)
         xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Definition ffu_bfacts (IP IL FPT p : Z) : Prop := (FIRST < LAST /\ A <= IP < LAST /\ 0 <= IL <= 2147483648 /\ A <= FPT <= p /\ p <= LAST)%Z.

  Lemma ffu_45c : forall (IP IL FPT p : Z) xra xt0 xt1 xt2 xs0 xs1 xa2 xa3 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    FFUINV E mm -> frm0 xfc -> ffu_bfacts IP IL FPT p ->
    evt usegs (ffu_post E) (BS 0x411a8 IP IL FPT p xra xt0 xt1 xt2 xs0 xs1 xa2 xa3 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using HSPATH OK.
    intros until mm. intros INV FRM (HLT & Hip & Hil & Hf & Hp).
    pose proof INV as INV0. ffu_open INV0. ffu_env OK.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x416f4%Z => u_trap_b pc
      | 0x415b0%Z => first [ eapply evt_eq; [| eapply (ffu_864 E OK)]; [num_st_eq | exact INV | assumption] | fail 100 "cut" pc ]
      | 0x411c4%Z => first [ eapply evt_eq; [| eapply (ffu_478 IP (IL - (FPT - p))%Z (FPT - p)%Z p)]; [num_st_eq | exact INV | assumption | exact HLT | lia | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma ffu_L3 : forall (f : nat) (IP IL FPT p : Z) xra xt0 xs0 xs1 xa2 xa3 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt4 xt5 xt6 xF xfc mm,
    FFUINV E mm -> frm0 xfc -> ffu_bfacts IP IL FPT p -> (p < LAST)%Z -> (LAST - p <= Z.of_nat f)%Z ->
    evt usegs (ffu_post E) (BS 0x41180 IP IL FPT p xra xt0 (Z_to_bv 64 9) (Z_to_bv 64 (-1)) xs0 xs1 xa2 xa3 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 10) xt4 xt5 xt6 xF xfc mm).
  Proof using HSPATH OK.
    intros f. induction f as [|f IH]; intros until mm; intros INV FRM BF Hp Hf; [exfalso; lia|].
    pose proof BF as (HLT & Hip & Hil & Hfp & Hpl).
    pose proof INV as INV0. ffu_open INV0. ffu_env OK. assert (D3 : IsData xa3) by exact I.
    nstep.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x416f4%Z => u_trap_b pc
      | 0x411a8%Z => first [ eapply evt_eq; [| eapply (ffu_45c IP IL FPT _)]; [num_st_eq | exact INV | assumption | unfold ffu_bfacts; lia] | fail 100 "cut" pc ]
      | 0x41180%Z => first [ eapply evt_eq; [| eapply (IH IP IL FPT (p + 1)%Z)]; [num_st_eq | exact INV | assumption | unfold ffu_bfacts; lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma ffu_424 : forall (IP IL FPT p : Z) xra xt0 xt1 xt2 xs0 xs1 xa2 xa3 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    FFUINV E mm -> frm0 xfc -> ffu_bfacts IP IL FPT p ->
    evt usegs (ffu_post E) (BS 0x41170 IP IL FPT p xra xt0 xt1 xt2 xs0 xs1 xa2 xa3 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using HSPATH OK.
    intros until mm. intros INV FRM BF. pose proof BF as (HLT & Hip & Hil & Hfp & Hpl).
    pose proof INV as INV0. ffu_open INV0. ffu_env OK.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x416f4%Z => u_trap_b pc
      | 0x411a8%Z => first [ eapply evt_eq; [| eapply (ffu_45c IP IL FPT p)]; [num_st_eq | exact INV | assumption | exact BF] | fail 100 "cut" pc ]
      | 0x41180%Z => first [ eapply evt_eq; [| eapply (ffu_L3 (Z.to_nat LAST) IP IL FPT p)]; [num_st_eq | exact INV | assumption | exact BF | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma ffu_3ac : forall (IP IL FPT p : Z) xra xt0 xt2 xs0 xs1 xa2 xa3 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    FFUINV E mm -> frm0 xfc -> ffu_bfacts IP IL FPT p -> (p + 4 <= LAST)%Z ->
    evt usegs (ffu_post E) (BS 0x410f8 IP IL FPT p xra xt0 (Z_to_bv 64 p) xt2 xs0 xs1 xa2 xa3 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using HSPATH OK.
    intros until mm. intros INV FRM BF Hp4. pose proof BF as (HLT & Hip & Hil & Hfp & Hpl).
    pose proof INV as INV0. ffu_open INV0. ffu_env OK. assert (D3 : IsData xa3) by exact I. assert (D6 : IsData xs6) by exact I.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x416f4%Z => u_trap_b pc
      | 0x41170%Z => first [ eapply evt_eq; [| eapply (ffu_424 IP IL FPT _)]; [num_st_eq | exact INV | assumption | unfold ffu_bfacts; lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma ffu_37c : forall (IP IL FPT p : Z) xra xt0 xs0 xs1 xa2 xa3 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    FFUINV E mm -> frm0 xfc -> ffu_bfacts IP IL FPT p ->
    evt usegs (ffu_post E) (BS 0x410c8 IP IL FPT p xra xt0 (Z_to_bv 64 p) (Z_to_bv 64 (LAST - p)) xs0 xs1 xa2 xa3 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using HSPATH OK.
    intros until mm. intros INV FRM BF. pose proof BF as (HLT & Hip & Hil & Hfp & Hpl).
    pose proof INV as INV0. ffu_open INV0. ffu_env OK.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x416f4%Z => u_trap_b pc
      | 0x41170%Z => first [ eapply evt_eq; [| eapply (ffu_424 IP IL FPT p)]; [num_st_eq | exact INV | assumption | exact BF] | fail 100 "cut" pc ]
      | 0x410f8%Z => first [ eapply evt_eq; [| eapply (ffu_3ac IP IL FPT p)]; [num_st_eq | exact INV | assumption | exact BF | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma ffu_L2 : forall (f : nat) (IP IL FPT p : Z) xra xt0 xs0 xs1 xa2 xa3 xs2 xs3 xs4 xs6 xs7 xs8 xs9 xs10 xs11 xt4 xt5 xt6 xF xfc mm,
    FFUINV E mm -> frm0 xfc -> ffu_bfacts IP IL FPT p -> (p + 8 <= LAST)%Z -> (LAST - p <= 8 * Z.of_nat f)%Z ->
    evt usegs (ffu_post E) (BS 0x41004 IP IL FPT p xra xt0 (Z_to_bv 64 p) (Z_to_bv 64 (LAST - p)) xs0 xs1 xa2 xa3 xs2 xs3 xs4 (Z_to_bv 64 7) xs6 xs7 xs8 xs9 xs10 xs11
                               (Z_to_bv 64 8) xt4 xt5 xt6 xF xfc mm).
  Proof using HSPATH OK.
    intros f. induction f as [|f IH]; intros until mm; intros INV FRM BF Hp Hf; [exfalso; lia|].
    pose proof BF as (HLT & Hip & Hil & Hfp & Hpl).
    pose proof INV as INV0. ffu_open INV0. ffu_env OK.
    assert (D3 : IsData xa3) by exact I. assert (Dt5 : IsData xt5) by exact I. assert (Dt6 : IsData xt6) by exact I. assert (Dt4 : IsData xt4) by exact I.
    assert (Ds0 : IsData xs0) by exact I. assert (Ds1 : IsData xs1) by exact I. assert (Ds2 : IsData xs2) by exact I. assert (Ds3 : IsData xs3) by exact I. assert (Ds4 : IsData xs4) by exact I.
    nstep.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x416f4%Z => u_trap_b pc
      | 0x410f8%Z => first [ eapply evt_eq; [| eapply (ffu_3ac IP IL FPT p)]; [num_st_eq | exact INV | assumption | exact BF | lia] | fail 100 "cut" pc ]
      | 0x410c8%Z => first [ eapply evt_eq; [| eapply (ffu_37c IP IL FPT (p + 8)%Z)]; [num_st_eq | exact INV | assumption | unfold ffu_bfacts; lia] | fail 100 "cut" pc ]
      | 0x41004%Z => first [ eapply evt_eq; [| eapply (IH IP IL FPT (p + 8)%Z)]; [num_st_eq | exact INV | assumption | unfold ffu_bfacts; lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.
End FFUPN.
