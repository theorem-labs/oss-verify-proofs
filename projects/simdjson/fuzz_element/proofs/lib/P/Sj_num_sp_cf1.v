(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjNumber.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import Sj_num_kit Sj_num_walk Sj_num_sp_defs Sj_num_sp_dc Sj_num_sp_cf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ solve_load_base | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].

Section SPCF1.
  Hypothesis HSET : sp_memset_stmt.
  Hypothesis HPM : sp_pm_stmt.
  Hypothesis HPDC : sp_pdc_stmt.
  Hypothesis HNDC : sp_ndc_stmt.
  Variable E : spenv.
  Hypothesis OK : sp_ok E.

  Ltac num_mark_words :=
    repeat match goal with
    | x : word |- _ => lazymatch goal with _ : IsData x |- _ => fail | _ => idtac end; let M := fresh "DM" in assert (M : IsData x) by exact I
    end.
  Ltac cf_tables mm :=
    let p5t := fresh "p5t" in let P5L := fresh "P5L" in let P5T := fresh "P5T" in let P5Z := fresh "P5Z" in
    destruct (image_readable_b psegs mm (Z.to_nat 10416) 0x18568 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as (p5t & P5L & P5T);
    assert (P5Z : Z.of_nat (length p5t) = 10416%Z) by (rewrite P5L; apply Z2Nat.id; lia); clear P5L.

  Definition cf1_k (pc : Z) : Prop :=
    forall (q IP IL FPT FL : Z) (xa7 xa1 : word) xra xt0 xt1 xt2 xs0 xa0 xa3 xa4 xa5 xa6 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
      SPINV2 E mm IP IL FPT FL -> frm0 xfc -> pm_spans_ok (q_A E) (q_txt E) IP IL FPT FL -> (-342 <= q <= 308)%Z ->
      (bv_unsigned xa1 <> 0 -> 1 <= bv_unsigned xa7 <= 18446744073709551614)%Z ->
      evt psegs (sp_post E) (SPS E pc xra xt0 xt1 xt2 xs0 (Z_to_bv 64 q) xa0 xa1 (Z_to_bv 64 (q_OUT E)) xa3 xa4 xa5 xa6 xa7
                               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).

  Ltac cf1_start :=
    unfold cf1_k; intros until mm; intros INV FRM SPN Hq HTM;
    lazymatch goal with INVh : SPINV2 _ ?m _ _ _ _ |- _ => let INV0 := fresh "INV0" in pose proof INVh as INV0; sp_open2 INV0; sp_env OK; cf_tables m end;
    lazymatch goal with H7 : (bv_unsigned ?x1 <> 0 -> 1 <= bv_unsigned ?x7 <= _)%Z |- _ =>
      let M1 := fresh "KEEP" in let M7 := fresh "KEEP" in
      assert (M1 : IsData x1) by exact I; assert (M7 : IsData x7) by exact I; num_mark_words; clear M1 M7 end.
  Ltac cf1_cut K q IP IL FPT FL INV FRM SPN HTM := first [ eapply (K q IP IL FPT FL); [exact INV | assumption | exact SPN | lia | exact HTM] | fail 100 "cut" ].
  Ltac cf1_5c8 q IP IL FPT FL INV FRM SPN HTM :=
    first [ eapply (sp_5c8 HSET HPM HPDC HNDC E OK q IP IL FPT FL); [exact INV | assumption | exact SPN | lia | exact HTM | left; lia] | fail 100 "cut 5c8" ].

  Lemma cf1_584 : cf1_k 0x51430.
  Proof using HSET HPM HPDC HNDC OK.
    cf1_start. nstep.
    walk ltac:(fun pc => lazymatch pc with | 0x51474%Z => cf1_5c8 q IP IL FPT FL INV FRM SPN HTM end).
  Qed.
  Lemma cf1_54c : cf1_k 0x513f8.
  Proof using HSET HPM HPDC HNDC OK.
    cf1_start. nstep.
    walk ltac:(fun pc => lazymatch pc with | 0x51430%Z => cf1_cut cf1_584 q IP IL FPT FL INV FRM SPN HTM | 0x51474%Z => cf1_5c8 q IP IL FPT FL INV FRM SPN HTM end).
  Qed.
  Lemma cf1_4f0 : cf1_k 0x5139c.
  Proof using HSET HPM HPDC HNDC OK.
    cf1_start. nstep.
    walk ltac:(fun pc => lazymatch pc with | 0x513f8%Z => cf1_cut cf1_54c q IP IL FPT FL INV FRM SPN HTM | 0x51474%Z => cf1_5c8 q IP IL FPT FL INV FRM SPN HTM end).
  Qed.
  Lemma cf1_408 : cf1_k 0x512b4.
  Proof using HSET HPM HPDC HNDC OK.
    cf1_start. nstep.
    walk ltac:(fun pc => lazymatch pc with | 0x5139c%Z => cf1_cut cf1_4f0 q IP IL FPT FL INV FRM SPN HTM end).
  Qed.

  Lemma sp_3d8 : forall (q IP IL FPT FL : Z) (xa7 xa1 : word) xra xt0 xt1 xt2 xs0 xa0 xa3 xa4 xa5 xa6 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    SPINV2 E mm IP IL FPT FL -> frm0 xfc -> pm_spans_ok (q_A E) (q_txt E) IP IL FPT FL ->
    (-9223372036854775808 <= q < 9223372036854775808)%Z ->
    (bv_unsigned xa1 <> 0 -> 1 <= bv_unsigned xa7 <= 18446744073709551614)%Z ->
    evt psegs (sp_post E) (SPS E 0x51284 xra xt0 xt1 xt2 xs0 (Z_to_bv 64 q) xa0 xa1 (Z_to_bv 64 (q_OUT E)) xa3 xa4 xa5 xa6 xa7
                               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using HSET HPM HPDC HNDC OK.
    intros until mm. intros INV FRM SPN Hq HTM.
    walk ltac:(fun pc => lazymatch pc with
      | 0x512b4%Z => first [ eapply (cf1_408 q IP IL FPT FL); [exact INV | assumption | exact SPN | lia | exact HTM] | fail 100 "cut" pc ]
      | 0x51474%Z => first [ eapply (sp_5c8 HSET HPM HPDC HNDC E OK q IP IL FPT FL); [exact INV | assumption | exact SPN | lia | exact HTM |];
                             unfold cf1_out;
                             first [ left; lia | right; left; split; [lia | split; reflexivity]
                                   | right; right; left; split; [lia | split; reflexivity] | right; right; right; lia ]
                           | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma sp_398 : forall (q IP IL FPT FL : Z) (xa7 xa3 : word) xra xt0 xs0 xa0 xa1 xa4 xa6 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt4 xt5 xt6 xF xfc mm,
    SPINV E mm -> frm0 xfc -> pm_spans_ok (q_A E) (q_txt E) IP IL FPT FL ->
    (-9223372036854775808 <= q < 9223372036854775808)%Z ->
    (bv_unsigned xa3 <> 0 -> 1 <= bv_unsigned xa7 <= 18446744073709551614)%Z ->
    evt psegs (sp_post E) (SPS E 0x51244 xra xt0 (Z_to_bv 64 IP) (Z_to_bv 64 FPT) xs0 (Z_to_bv 64 q) xa0 xa1 (Z_to_bv 64 (q_OUT E)) xa3 xa4 (Z_to_bv 64 IL) xa6 xa7
                               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 FL) xt4 xt5 xt6 xF xfc mm).
  Proof using HSET HPM HPDC HNDC OK.
    intros until mm. intros INV FRM SPN Hq HTM. sp_open INV. sp_env OK.
    assert (DA6 : IsData xa6) by exact I.
    destruct (image_readable_b psegs mm 4 0xd18b0 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as (fmin & FML & FMIN).
    destruct (image_readable_b psegs mm 184 0x1afc0 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as (p10d & P10L & P10D).
    destruct (image_readable_b psegs mm 184 0x1b078 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as (mxm & MXL & MXM).
    walk ltac:(fun pc => lazymatch pc with
      | 0x51900%Z => first [ eapply sp_exit; [exact OK | sp_close | assumption] | fail 100 "cut" pc ]
      | 0x51284%Z => first [ eapply (sp_3d8 q IP IL FPT FL); [sp_close2 | assumption | exact SPN | lia
                                                             | first [ (intros C; exfalso; apply C; reflexivity) | (intros _; apply HTM; assumption) ] ]
                           | fail 100 "cut" pc ]
      end).
  Qed.
End SPCF1.
