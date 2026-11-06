(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Arr Bytes Z10q FP.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Sj Require Import Zpe.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Zso Zvm Zve Zvd.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ solve_load_base | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].

Section SPCF.
  Hypothesis HSET : sp_memset_stmt.
  Hypothesis HPM : sp_pm_stmt.
  Hypothesis HPDC : sp_pdc_stmt.
  Hypothesis HNDC : sp_ndc_stmt.
  Variable E : spenv.
  Hypothesis OK : sp_ok E.

  Lemma sp_7c8 : forall (q IP IL FPT FL : Z) (xa7 : word) xra xt0 xt1 xt2 xs0 xa0 xa1 xa3 xa4 xa5 xa6 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    SPINV2 E mm IP IL FPT FL -> frm0 xfc -> pm_spans_ok (q_A E) (q_txt E) IP IL FPT FL -> (-342 <= q <= 308)%Z ->
    evt psegs (sp_post E) (SPS E 0x3afb8 xra xt0 xt1 xt2 xs0 (Z_to_bv 64 q) xa0 xa1 (Z_to_bv 64 (q_OUT E)) xa3 xa4 xa5 xa6 xa7
                               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using HSET HPM HPDC HNDC OK.
    intros until mm. intros INV FRM SPN Hq. pose proof INV as INV0. sp_open2 INV0. sp_env OK.
    destruct (image_readable_b psegs mm (Z.to_nat 10416) 0x174a8 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as (p5t & P5L & P5T).
    assert (P5Z : Z.of_nat (length p5t) = 10416%Z) by (rewrite P5L; apply Z2Nat.id; lia). clear P5L.
    assert (DS0 : IsData xs0) by exact I. assert (DS2 : IsData xs2) by exact I. assert (DA7 : IsData xa7) by exact I.
    walk ltac:(fun pc => lazymatch pc with
      | 0x3b20c%Z => first [ eapply sp_a1c; [exact OK | eapply SPINV_of_SPINV2; exact INV | exact FRM] | fail 100 "cut" pc ]
      | 0x3b0ec%Z => first [ eapply (sp_8fc HSET HPM HPDC HNDC E OK _ IP IL FPT FL); [exact INV | exact FRM | exact SPN] | fail 100 "cut" pc ]
      end).
  Qed.

  Ltac cf_tables mm :=
    let p5t := fresh "p5t" in let P5L := fresh "P5L" in let P5T := fresh "P5T" in let P5Z := fresh "P5Z" in
    destruct (image_readable_b psegs mm (Z.to_nat 10416) 0x174a8 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as (p5t & P5L & P5T);
    assert (P5Z : Z.of_nat (length p5t) = 10416%Z) by (rewrite P5L; apply Z2Nat.id; lia); clear P5L.

  Lemma sp_7c0 : forall (q IP IL FPT FL : Z) (xa7 : word) xra xt0 xt1 xt2 (xs0 : word) xa0 xa1 (xa3 xa4 : word) xa5 xa6 (xs2 : word) xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    SPINV2 E mm IP IL FPT FL -> frm0 xfc -> pm_spans_ok (q_A E) (q_txt E) IP IL FPT FL ->
    ((-342 <= q <= 308)%Z \/ (xs0 = xa4 /\ xs2 = xa3)) ->
    evt psegs (sp_post E) (SPS E 0x3afb0 xra xt0 xt1 xt2 xs0 (Z_to_bv 64 q) xa0 xa1 (Z_to_bv 64 (q_OUT E)) xa3 xa4 xa5 xa6 xa7
                               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using HSET HPM HPDC HNDC OK.
    intros until mm. intros INV FRM SPN [Hq | [E1 E2]].
    - walk ltac:(fun pc => lazymatch pc with
        | 0x3b20c%Z => first [ eapply sp_a1c; [exact OK | eapply SPINV_of_SPINV2; exact INV | exact FRM] | fail 100 "cut" pc ]
        | 0x3afb8%Z => first [ eapply (sp_7c8 q IP IL FPT FL); [exact INV | exact FRM | exact SPN | lia] | fail 100 "cut" pc ]
        end).
    - subst xa4 xa3.
      walk ltac:(fun pc => lazymatch pc with
        | 0x3b20c%Z => first [ eapply sp_a1c; [exact OK | eapply SPINV_of_SPINV2; exact INV | exact FRM] | fail 100 "cut" pc ]
        end).
  Qed.

  Definition cf2_k (pc : Z) : Prop :=
    forall (q IP IL FPT FL : Z) (xa7 : word) xra xt0 xt1 xt2 xs0 xa0 xa1 xa3 xa4 xa5 xa6 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
      SPINV2 E mm IP IL FPT FL -> frm0 xfc -> pm_spans_ok (q_A E) (q_txt E) IP IL FPT FL -> (-342 <= q <= 308)%Z ->
      evt psegs (sp_post E) (SPS E pc xra xt0 xt1 xt2 xs0 (Z_to_bv 64 q) xa0 xa1 (Z_to_bv 64 (q_OUT E)) xa3 xa4 xa5 xa6 xa7
                               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).

  Ltac num_mark_words :=
    repeat match goal with
    | x : word |- _ => lazymatch goal with _ : IsData x |- _ => fail | _ => idtac end; let M := fresh "DM" in assert (M : IsData x) by exact I
    end.
  Ltac cf2_start :=
    unfold cf2_k; intros until mm; intros INV FRM SPN Hq;
    lazymatch goal with INVh : SPINV2 _ ?m _ _ _ _ |- _ => let INV0 := fresh "INV0" in pose proof INVh as INV0; sp_open2 INV0; sp_env OK; cf_tables m end;
    num_mark_words.
  Ltac cf2_cut K q IP IL FPT FL INV FRM SPN := first [ eapply (K q IP IL FPT FL); [exact INV | assumption | exact SPN | lia] | fail 100 "cut" ].

  Lemma cf2_7c0 : cf2_k 0x3afb0.
  Proof using HSET HPM HPDC HNDC OK.
    unfold cf2_k. intros until mm. intros INV FRM SPN Hq.
    eapply (sp_7c0 q IP IL FPT FL); [exact INV | exact FRM | exact SPN | left; lia].
  Qed.
  Lemma cf2_77c : cf2_k 0x3af6c.
  Proof using HSET HPM HPDC HNDC OK.
    cf2_start. nstep.
    walk ltac:(fun pc => lazymatch pc with | 0x3afb0%Z => cf2_cut cf2_7c0 q IP IL FPT FL INV FRM SPN end).
  Qed.
  Lemma cf2_744 : cf2_k 0x3af34.
  Proof using HSET HPM HPDC HNDC OK.
    cf2_start. nstep.
    walk ltac:(fun pc => lazymatch pc with | 0x3af6c%Z => cf2_cut cf2_77c q IP IL FPT FL INV FRM SPN | 0x3afb0%Z => cf2_cut cf2_7c0 q IP IL FPT FL INV FRM SPN end).
  Qed.
  Lemma cf2_6e8 : cf2_k 0x3aed8.
  Proof using HSET HPM HPDC HNDC OK.
    cf2_start. nstep.
    walk ltac:(fun pc => lazymatch pc with | 0x3af34%Z => cf2_cut cf2_744 q IP IL FPT FL INV FRM SPN | 0x3afb0%Z => cf2_cut cf2_7c0 q IP IL FPT FL INV FRM SPN end).
  Qed.
  Lemma cf2_600 : cf2_k 0x3adf0.
  Proof using HSET HPM HPDC HNDC OK.
    cf2_start. nstep.
    walk ltac:(fun pc => lazymatch pc with | 0x3aed8%Z => cf2_cut cf2_6e8 q IP IL FPT FL INV FRM SPN end).
  Qed.

  Definition cf1_out (q : Z) (w s0v s2v : word) : Prop :=
    (-342 <= q <= 308)%Z \/ (q < -342 /\ s0v = Z_to_bv 64 0 /\ s2v = Z_to_bv 64 0)%Z \/
    (308 < q /\ s0v = Z_to_bv 64 0 /\ s2v = Z_to_bv 64 2047)%Z \/ (bv_unsigned w = 0)%Z.

  Lemma sp_5c8 : forall (q IP IL FPT FL : Z) (xa7 : word) xra xt0 xt1 xt2 (xs0 : word) xa0 (xa1 : word) xa3 xa4 xa5 xa6 (xs2 : word) xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    SPINV2 E mm IP IL FPT FL -> frm0 xfc -> pm_spans_ok (q_A E) (q_txt E) IP IL FPT FL ->
    (-9223372036854775808 <= q < 9223372036854775808)%Z ->
    (bv_unsigned xa1 <> 0 -> 1 <= bv_unsigned xa7 <= 18446744073709551614)%Z ->
    cf1_out q xa7 xs0 xs2 ->
    evt psegs (sp_post E) (SPS E 0x3adb8 xra xt0 xt1 xt2 xs0 (Z_to_bv 64 q) xa0 xa1 (Z_to_bv 64 (q_OUT E)) xa3 xa4 xa5 xa6 xa7
                               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using HSET HPM HPDC HNDC OK.
    intros until mm. intros INV FRM SPN Hq HTM R. pose proof INV as INV0. sp_open2 INV0. sp_env OK.
    zstep.
    if_cases K0; zify_cond K0.
    { eapply sp_a1c; [exact OK | eapply SPINV_of_SPINV2; exact INV | exact FRM]. }
    specialize (HTM K0).
    assert (W1 : ((bv_unsigned xa7 + 1) mod 18446744073709551616 = bv_unsigned xa7 + 1)%Z) by (apply Z.mod_small; lia).
    destruct R as [R | [(R & -> & ->) | [(R & -> & ->) | R]]]; [ | | | exfalso; lia ].
    - walk ltac:(fun pc => lazymatch pc with
        | 0x3adf0%Z => first [ eapply (cf2_600 q IP IL FPT FL); [exact INV | assumption | exact SPN | lia] | fail 100 "cut" pc ]
        | 0x3afb0%Z => first [ eapply (sp_7c0 q IP IL FPT FL); [exact INV | assumption | exact SPN | left; lia] | fail 100 "cut" pc ]
        end).
    - walk ltac:(fun pc => lazymatch pc with
        | 0x3afb0%Z => first [ eapply (sp_7c0 q IP IL FPT FL); [exact INV | assumption | exact SPN | right; split; reflexivity] | fail 100 "cut" pc ]
        end).
    - walk ltac:(fun pc => lazymatch pc with
        | 0x3afb0%Z => first [ eapply (sp_7c0 q IP IL FPT FL); [exact INV | assumption | exact SPN | right; split; reflexivity] | fail 100 "cut" pc ]
        end).
  Qed.
End SPCF.
