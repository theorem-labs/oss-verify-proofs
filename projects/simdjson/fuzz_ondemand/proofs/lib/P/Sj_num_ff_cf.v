(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjNumber.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Sj_num_kit Sj_num_walk Sj_num_ff_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ solve_load_base | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].

Section FFCF.
  Variable E : ffenv.
  Hypothesis OK : ff_ok E.

  Ltac num_mark_words :=
    repeat match goal with
    | x : word |- _ => lazymatch goal with _ : IsData x |- _ => fail | _ => idtac end; let M := fresh "DM" in assert (M : IsData x) by exact I
    end.
  Ltac ff_tables :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let p5t := fresh "p5t" in let P5L := fresh "P5L" in let P5T := fresh "P5T" in let P5Z := fresh "P5Z" in
      destruct (image_readable_b psegs mm (Z.to_nat 10416) 0x17700 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as (p5t & P5L & P5T);
      assert (P5Z : Z.of_nat (length p5t) = 10416%Z) by (rewrite P5L; apply Z2Nat.id; lia); clear P5L;
      let fmin := fresh "fmin" in let FML := fresh "FML" in let FMIN := fresh "FMIN" in
      destruct (image_readable_b psegs mm 4 0x78900 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as (fmin & FML & FMIN);
      let p10d := fresh "p10d" in let P10L := fresh "P10L" in let P10D := fresh "P10D" in
      destruct (image_readable_b psegs mm 184 0x1a158 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as (p10d & P10L & P10D);
      let mxm := fresh "mxm" in let MXL := fresh "MXL" in let MXM := fresh "MXM" in
      destruct (image_readable_b psegs mm 184 0x1a210 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as (mxm & MXL & MXM)
    end.

  Definition ff_k0 (pc : Z) : Prop :=
    forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xt3 xt4 xt5 xt6 xF xfc mm, FFINV E mm -> frm0 xfc -> evt psegs (ff_post E) (FFS E pc xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xt3 xt4 xt5 xt6 xF xfc mm).
  Ltac k0_start := unfold ff_k0; intros until mm; intros INV FRM; num_mark_words.
  Ltac k0_cut K INV := first [ eapply K; [exact INV | assumption] | fail 100 "cut" ].

  Lemma ffk_8d0 : ff_k0 0x29470.
  Proof using OK. unfold ff_k0. intros until mm. intros INV FRM. eapply ff_exit; [exact OK | exact INV | exact FRM]. Qed.
  Lemma ffk_920 : ff_k0 0x294c0.
  Proof using OK. k0_start. nstep. walk ltac:(fun pc => lazymatch pc with | 0x29470%Z => k0_cut ffk_8d0 INV end). Qed.
  Lemma ffk_918 : ff_k0 0x294b8.
  Proof using OK. k0_start. nstep. walk ltac:(fun pc => lazymatch pc with | 0x29470%Z => k0_cut ffk_8d0 INV | 0x294c0%Z => k0_cut ffk_920 INV end). Qed.
  Lemma ffk_8b4 : ff_k0 0x29454.
  Proof using OK. k0_start. nstep. walk ltac:(fun pc => lazymatch pc with | 0x29470%Z => k0_cut ffk_8d0 INV end). Qed.
  Lemma ffk_7e8 : ff_k0 0x29388.
  Proof using OK. k0_start. nstep. walk ltac:(fun pc => lazymatch pc with | 0x29454%Z => k0_cut ffk_8b4 INV end). Qed.
  Lemma ffk_7a4 : ff_k0 0x29344.
  Proof using OK. k0_start. nstep. walk ltac:(fun pc => lazymatch pc with | 0x29388%Z => k0_cut ffk_7e8 INV | 0x29454%Z => k0_cut ffk_8b4 INV end). Qed.

  Definition ff_kq (pc : Z) : Prop :=
    forall (q : Z) xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xt3 xt4 xt5 xt6 xF xfc mm, FFINV E mm -> frm0 xfc -> (-342 <= q <= 308)%Z ->
      evt psegs (ff_post E) (FFS E pc xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 (Z_to_bv 64 q) xs2 xs3 xs4 xs5 xs6 xs7 xs8 xt3 xt4 xt5 xt6 xF xfc mm).
  Ltac kq_start := unfold ff_kq; intros until mm; intros INV FRM Hq; pose proof INV as INV0;
    lazymatch goal with INVh : FFINV _ _ |- _ => let I1 := fresh "INV1" in pose proof INVh as I1; ff_open I1 end; ff_env OK; ff_tables; num_mark_words.

  Lemma ffk_748 : ff_kq 0x292e8.
  Proof using OK.
    kq_start. nstep.
    walk ltac:(fun pc => lazymatch pc with | 0x29344%Z => k0_cut ffk_7a4 INV | 0x29388%Z => k0_cut ffk_7e8 INV | 0x29454%Z => k0_cut ffk_8b4 INV end).
  Qed.
  Lemma ffk_660 : ff_kq 0x29200.
  Proof using OK.
    kq_start. nstep.
    walk ltac:(fun pc => lazymatch pc with
      | 0x292e8%Z => first [ eapply (ffk_748 q); [exact INV | assumption | lia] | fail 100 "cut" pc ] end).
  Qed.

  Lemma ff_620 : forall (q : Z) xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 (xa3 : word) xa4 xa5 xa6 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xt3 xt4 xt5 xt6 xF xfc mm,
    FFINV E mm -> frm0 xfc -> (-9223372036854775808 <= q < 9223372036854775808)%Z ->
    evt psegs (ff_post E) (FFS E 0x291c0 xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 (Z_to_bv 64 q) xs2 xs3 xs4 xs5 xs6 xs7 xs8 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK.
    intros until mm. intros INV FRM Hq. pose proof INV as INV0. ff_open INV0. ff_env OK. ff_tables.
    assert (DA2 : IsData xa2) by exact I.
    walk ltac:(fun pc => lazymatch pc with
      | 0x29470%Z => k0_cut ffk_8d0 INV
      | 0x294c0%Z => k0_cut ffk_920 INV
      | 0x294b8%Z => k0_cut ffk_918 INV
      | 0x29454%Z => k0_cut ffk_8b4 INV
      | 0x29200%Z => first [ eapply (ffk_660 q); [exact INV | assumption | lia] | fail 100 "cut" pc ]
      end).
  Qed.
End FFCF.
