(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Export StepA StepA2 AImages.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Export Mem Arr Frame Cells Step.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Ltac cstep := stepA; try first [if_true | if_false].
(* [comment removed for export] *)
Ltac amo_phase1 ::=
  match goal with
  | |- context [amo_aligned ?wd ?a] =>
      let H := fresh "AL" in
      first [ assert (H : amo_aligned wd a = true) by prove_amo_aligned
            | fail 100 "stepA: cannot prove natural alignment of the atomic access at" a ];
      rewrite H; clear H; cbv beta iota delta [negb];
      exec_cbvA; simp_is_x0; simp_regs;
      repeat match goal with
      | |- context [Z.eqb ?x ?x] => rewrite (Z.eqb_refl x); cbv beta iota
      | |- context [Z.eqb (bv_unsigned ?x) (bv_unsigned ?y)] =>
          replace (Z.eqb (bv_unsigned x) (bv_unsigned y)) with true by (symmetry; apply Z.eqb_eq; first [reflexivity | zsimp; lia]);
          cbv beta iota
      end
  | _ => idtac
  end.

Notation zb0 := (Z_to_bv 8 0).

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac lia ::=
  first [ LiaTuning.zify_prune; LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | LiaTuning.zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import SecRanges.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= force_section_ranges.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac aceil :=
  lazymatch goal with
  | H : _ <= alloc_ceiling <= _ |- _ => idtac
  | |- context [alloc_ceiling] => repeat match goal with H : True |- _ => clear H end; pose proof alloc_ceiling_range as CEILB
  | H : context [alloc_ceiling] |- _ => repeat match goal with H' : True |- _ => clear H' end; pose proof alloc_ceiling_range as CEILB
  | _ => first [ pose proof I as CEILB | idtac ]
  end.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma bytes_eq_of_unsigned : forall (l1 l2 : list byte), map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof. aceil.
  induction l1 as [|x l1 IH]; intros [|y l2] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1| apply IH; exact H2].
Qed.

Lemma rw_cells_reshape : forall segs m A cs cs',
  cells_wf cs' -> map bv_unsigned (cells_bytes cs') = map bv_unsigned (cells_bytes cs) -> rw_cells segs m A cs -> rw_cells segs m A cs'.
Proof. aceil.
  intros segs m A cs cs' WF EB0 [[WF0 BA] WR]. pose proof (bytes_eq_of_unsigned _ _ EB0) as EB.
  split; [split; [exact WF| rewrite EB; exact BA]|].
  rewrite <- (cells_bytes_length cs' WF), EB, (cells_bytes_length cs WF0). exact WR.
Qed.

Lemma wr_at_sub : forall segs m a n a' n', wr_at segs m a n -> a <= a' -> a' + n' <= a + n -> wr_at segs m a' n'.
Proof. aceil.
  intros segs m a n a' n' (A0 & AN & W) H1 H2. split; [lia|]. split; [lia|].
  intros i Hi. replace (a' + i) with (a + (a' - a + i)) by lia. apply W. lia.
Qed.
End RC__1.
