(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Arr Bytes Z10q FP.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Sj Require Import Zpe Zpd.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Zso Zvm Zve Zvd Zv9 Zvj Zv5.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ solve_load_base | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].

Section SPEXP.
  Hypothesis HSET : sp_memset_stmt.
  Hypothesis HPM : sp_pm_stmt.
  Hypothesis HPDC : sp_pdc_stmt.
  Hypothesis HNDC : sp_ndc_stmt.
  Variable E : spenv.
  Hypothesis OK : sp_ok E.
  Notation A := (q_A E).
  Notation LAST := (q_LAST E).
  Notation OUT := (q_OUT E).

  Notation XS pc IP IL FPT FL xra xs0 xs1 xa0 xa3 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt5 xt6 xF xfc mm :=
    (SPS E pc xra (Z_to_bv 64 (IP + IL)) (Z_to_bv 64 IP) (Z_to_bv 64 FPT) xs0 xs1 xa0 (Z_to_bv 64 LAST) (Z_to_bv 64 OUT) xa3
         (Z_to_bv 64 SPATH_A4) (Z_to_bv 64 IL) xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 FL) (Z_to_bv 64 (IL + FL)) xt5 xt6 xF xfc mm).

  Ltac exp_cuts INV PF :=
    fun pc => lazymatch pc with
      | 0x3ab20%Z => first [ eapply evt_eq; [| eapply (sp_330 HSET HPM HPDC HNDC E OK)]; [num_st_eq | exact INV | assumption | exact PF] | fail 100 "cut" pc ]
      | 0x3aa68%Z => first [ eapply evt_eq; [| eapply (sp_278 HSET HPM HPDC HNDC E OK)]; [num_st_eq | exact INV | assumption | exact PF] | fail 100 "cut" pc ]
      end.

  Lemma sp_264 : forall (IP IL FPT FL : Z) xra xs0 xs1 xa0 xa3 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt5 xt6 xF xfc mm,
    SPINV E mm -> frm0 xfc -> sp_pfacts E IP IL FPT FL ->
    evt psegs (sp_post E) (XS 0x3aa54 IP IL FPT FL xra xs0 xs1 xa0 xa3 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt5 xt6 xF xfc mm).
  Proof using HSET HPM HPDC HNDC OK.
    intros until mm. intros INV FRM PF. kwalk ltac:(exp_cuts INV PF).
  Qed.

  Lemma sp_16c : forall (IP IL FPT FL : Z) xra xs0 xs1 xa0 xa3 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt5 xt6 xF xfc mm,
    SPINV E mm -> frm0 xfc -> sp_pfacts E IP IL FPT FL ->
    evt psegs (sp_post E) (XS 0x3a95c IP IL FPT FL xra xs0 xs1 xa0 xa3 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt5 xt6 xF xfc mm).
  Proof using HSET HPM HPDC HNDC OK.
    intros until mm. intros INV FRM PF. kwalk ltac:(exp_cuts INV PF).
  Qed.

  Lemma sp_L4 : forall (f : nat) (IP IL FPT FL e : Z) xra xs1 xa3 xa6 xa7 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt6 xF xfc mm,
    SPINV E mm -> frm0 xfc -> sp_pfacts E IP IL FPT FL -> (A <= e < LAST)%Z -> (LAST - e <= Z.of_nat f)%Z ->
    evt psegs (sp_post E) (XS 0x3a924 IP IL FPT FL xra (Z_to_bv 64 9) xs1 (Z_to_bv 64 10) xa3 xa6 xa7 (Z_to_bv 64 268435456) xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11
                               (Z_to_bv 64 e) xt6 xF xfc mm).
  Proof using HSET HPM HPDC HNDC OK.
    intros f. induction f as [|f IH]; intros until mm; intros INV FRM PF He Hf; [exfalso; lia|].
    pose proof INV as INV0. sp_open INV0. sp_env OK.
    kstep.
    kwalk ltac:(fun pc => lazymatch pc with
      | 0x3aa54%Z => first [ eapply evt_eq; [| eapply (sp_264 IP IL FPT FL)]; [num_st_eq | exact INV | assumption | exact PF] | fail 100 "cut" pc ]
      | 0x3a924%Z => first [ eapply evt_eq; [| eapply (IH IP IL FPT FL (e + 1)%Z)]; [num_st_eq | exact INV | assumption | exact PF | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma sp_108 : forall (IP IL FPT FL e : Z) xra xs0 xs1 xa0 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt6 xF xfc mm,
    SPINV E mm -> frm0 xfc -> sp_pfacts E IP IL FPT FL -> (A <= e <= LAST)%Z ->
    evt psegs (sp_post E) (XS 0x3a8f8 IP IL FPT FL xra xs0 xs1 xa0 (Z_to_bv 64 53) xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 e) xt6 xF xfc mm).
  Proof using HSET HPM HPDC HNDC OK.
    intros until mm. intros INV FRM PF He.
    pose proof INV as INV0. sp_open INV0. sp_env OK.
    kwalk ltac:(fun pc => lazymatch pc with
      | 0x3a95c%Z => first [ eapply evt_eq; [| eapply (sp_16c IP IL FPT FL)]; [num_st_eq | exact INV | assumption | exact PF] | fail 100 "cut" pc ]
      | 0x3a924%Z => first [ eapply evt_eq; [| eapply (sp_L4 (Z.to_nat LAST) IP IL FPT FL e)]; [num_st_eq | exact INV | assumption | exact PF | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma sp_f9c : forall (IP IL FPT FL e : Z) xra xs0 xs1 xa0 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt6 xF xfc mm,
    SPINV E mm -> frm0 xfc -> sp_pfacts E IP IL FPT FL -> (A <= e <= LAST)%Z ->
    evt psegs (sp_post E) (XS 0x3a78c IP IL FPT FL xra xs0 xs1 xa0 (Z_to_bv 64 53) xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 e) xt6 xF xfc mm).
  Proof using HSET HPM HPDC HNDC OK.
    intros until mm. intros INV FRM PF He.
    pose proof INV as INV0. sp_open INV0. sp_env OK.
    kwalk ltac:(fun pc => lazymatch pc with
      | 0x3a8f8%Z => first [ try (match goal with |- context [Z.b2z ?t] => destruct t end; cbn [Z.b2z]);
                             (eapply evt_eq; [| eapply (sp_108 IP IL FPT FL _)]; [num_st_eq | exact INV | assumption | exact PF | lia]) | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma sp_f6c : forall (IP IL FPT FL p : Z) xra xs0 xs1 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt5 xt6 xF xfc mm,
    SPINV E mm -> frm0 xfc -> sp_pfacts E IP IL FPT FL -> (A <= p < LAST)%Z ->
    evt psegs (sp_post E) (XS 0x3a75c IP IL FPT FL xra xs0 xs1 (Z_to_bv 64 p) (Z_to_bv 64 53) xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt5 xt6 xF xfc mm).
  Proof using HSET HPM HPDC HNDC OK.
    intros until mm. intros INV FRM PF Hp.
    pose proof INV as INV0. sp_open INV0. sp_env OK.
    kwalk ltac:(fun pc => lazymatch pc with
      | 0x3a78c%Z => first [ eapply evt_eq; [| eapply (sp_f9c IP IL FPT FL _)]; [num_st_eq | exact INV | assumption | exact PF | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma sp_f1c : forall (IP IL FPT FL p : Z) xra xs0 xs1 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt5 xt6 xF xfc mm,
    SPINV E mm -> frm0 xfc -> sp_pfacts E IP IL FPT FL -> (A <= p <= LAST)%Z ->
    evt psegs (sp_post E) (XS 0x3a70c IP IL FPT FL xra xs0 xs1 (Z_to_bv 64 p) (Z_to_bv 64 53) xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt5 xt6 xF xfc mm).
  Proof using HSET HPM HPDC HNDC OK.
    intros until mm. intros INV FRM PF Hp.
    pose proof INV as INV0. sp_open INV0. sp_env OK.
    kwalk ltac:(fun pc => lazymatch pc with
      | 0x3a95c%Z => first [ eapply evt_eq; [| eapply (sp_16c IP IL FPT FL)]; [num_st_eq | exact INV | assumption | exact PF] | fail 100 "cut" pc ]
      | 0x3a75c%Z => first [ eapply evt_eq; [| eapply (sp_f6c IP IL FPT FL p)]; [num_st_eq | exact INV | assumption | exact PF | lia] | fail 100 "cut" pc ]
      end).
  Qed.
End SPEXP.
