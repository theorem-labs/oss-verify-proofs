(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjNumber.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout Shadow RT_iface D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_rtf
  Sj_num_akit Sj_num_amem Sj_num_iface Sj_num_adefs Sj_num_ff_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].

Section FFCF.
  Variable E : ffenv.
  Hypothesis OK : ff_ok E.
  Variable m0 : mem.

  Hypothesis SHL1 : forall m', munch (FF_W E) m0 m' -> wmono asegs m0 m' -> shz m' 0x2a2e0 10416.
  Hypothesis SHL2 : forall m', munch (FF_W E) m0 m' -> wmono asegs m0 m' -> shz m' 0x2cc60 640.

  Ltac num_mark_words :=
    repeat match goal with
    | x : word |- _ => lazymatch goal with _ : IsData x |- _ => fail | _ => idtac end; let M := fresh "DM" in assert (M : IsData x) by exact I
    end.
  Ltac ff_tables :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let p5t := fresh "p5t" in let P5L := fresh "P5L" in let P5T := fresh "P5T" in let P5Z := fresh "P5Z" in
      destruct (image_readable_b asegs mm (Z.to_nat 10416) 0x2a2e0 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as (p5t & P5L & P5T);
      assert (P5Z : Z.of_nat (length p5t) = 10416%Z) by (rewrite P5L; apply Z2Nat.id; lia); clear P5L;
      let fmin := fresh "fmin" in let FML := fresh "FML" in let FMIN := fresh "FMIN" in
      destruct (image_readable_b asegs mm 4 0x16e988 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as (fmin & FML & FMIN);
      let p10d := fresh "p10d" in let P10L := fresh "P10L" in let P10D := fresh "P10D" in
      destruct (image_readable_b asegs mm 184 0x2cd68 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as (p10d & P10L & P10D);
      let mxm := fresh "mxm" in let MXL := fresh "MXL" in let MXM := fresh "MXM" in
      destruct (image_readable_b asegs mm 184 0x2ce20 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as (mxm & MXL & MXM)
    end.

  Definition ff_k0 (pc : Z) : Prop :=
    forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm, FFINV E m0 mm -> frm0 xfc -> evt asegs (ff_mid E m0) (FFS E pc xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Ltac k0_start := unfold ff_k0; intros until mm; intros INV FRM; pose proof INV as INV0;
    lazymatch goal with INVh : FFINV _ _ _ |- _ => let I1 := fresh "INV1" in pose proof INVh as I1; ff_open I1 end; ff_env OK; num_mark_words.
  Ltac k0_cut K INV := first [ eapply K; [exact INV | assumption] | fail 100 "cut" ].

  Lemma ffk_c54 : ff_k0 0xb9ca4.
  Proof using OK. unfold ff_k0. intros until mm. intros INV FRM. eapply ff_exit; [exact OK | exact INV | exact FRM]. Qed.
  Lemma ffk_c50 : ff_k0 0xb9ca0.
  Proof using OK. k0_start. astep. awalk ltac:(fun pc => lazymatch pc with | 0xb9ca4%Z => k0_cut ffk_c54 INV end). Qed.

  Ltac k0_cutm K INV := first [ eapply K; [exact INV | assumption] | eapply K; [ff_close | assumption] | fail 100 "cutm" ].
  Ltac cf_cuts INV pc :=
    lazymatch pc with
    | 0xb9ca4%Z => k0_cutm ffk_c54 INV
    | 0xb9ca0%Z => k0_cutm ffk_c50 INV
    end.

  Lemma ffk_c34 : ff_k0 0xb9c84.
  Proof using OK. k0_start. astep. awalk ltac:(cf_cuts INV). Qed.
  Lemma ffk_c14 : ff_k0 0xb9c64.
  Proof using OK. k0_start. astep. awalk ltac:(cf_cuts INV). Qed.
  Lemma ffk_cbc : ff_k0 0xb9d0c.
  Proof using OK. k0_start. astep. awalk ltac:(cf_cuts INV). Qed.
  Lemma ffk_c1c : ff_k0 0xb9c6c.
  Proof using OK. k0_start. astep. awalk ltac:(fun pc => lazymatch pc with 0xb9c84%Z => k0_cut ffk_c34 INV end). Qed.
  Lemma ffk_b8c : ff_k0 0xb9bdc.
  Proof using OK. k0_start. astep. awalk ltac:(fun pc => lazymatch pc with 0xb9c84%Z => k0_cut ffk_c34 INV | 0xb9c6c%Z => k0_cut ffk_c1c INV end). Qed.
  Lemma ffk_aec : ff_k0 0xb9b3c.
  Proof using OK. k0_start. astep. awalk ltac:(fun pc => lazymatch pc with 0xb9c84%Z => k0_cut ffk_c34 INV end). Qed.

  Definition ff_kq (pc : Z) : Prop :=
    forall (q : Z) xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa6 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm, FFINV E m0 mm -> frm0 xfc -> (-342 <= q <= 308)%Z ->
      evt asegs (ff_mid E m0) (FFS E pc xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 (Z_to_bv 64 q) xa6 (Z_to_bv 64 2147450880) xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Ltac kq_start := unfold ff_kq; intros until mm; intros INV FRM Hq; pose proof INV as INV0;
    lazymatch goal with INVh : FFINV _ _ _ |- _ => let I1 := fresh "INV1" in pose proof INVh as I1; ff_open I1 end; ff_env OK; ff_tables; num_mark_words.

  Lemma ffk_a90 : ff_kq 0xb9ae0.
  Proof using OK.
    kq_start. astep.
    awalk ltac:(fun pc => lazymatch pc with 0xb9b3c%Z => k0_cut ffk_aec INV | 0xb9bdc%Z => k0_cut ffk_b8c INV | 0xb9c84%Z => k0_cut ffk_c34 INV end).
  Qed.
  Lemma ffk_970 : ff_kq 0xb99c0.
  Proof using OK SHL1 SHL2.
    kq_start. astep.
    awalk ltac:(fun pc => lazymatch pc with
      | 0xb9ae0%Z => first [ eapply (ffk_a90 q); [exact INV | assumption | lia] | fail 100 "cut" pc ] end).
  Qed.
  Lemma ffk_c10 : ff_k0 0xb9c60.
  Proof using OK. k0_start. astep. awalk ltac:(fun pc => lazymatch pc with 0xb9c64%Z => k0_cut ffk_c14 INV end). Qed.

  Definition ff_ka (pc : Z) : Prop :=
    forall (q : Z) xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa6 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm, FFINV E m0 mm -> frm0 xfc -> (-9223372036854775808 <= q < 9223372036854775808)%Z ->
      evt asegs (ff_mid E m0) (FFS E pc xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 (Z_to_bv 64 q) xa6 (Z_to_bv 64 2147450880) xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Ltac ka_start := unfold ff_ka; intros until mm; intros INV FRM Hq; pose proof INV as INV0;
    lazymatch goal with INVh : FFINV _ _ _ |- _ => let I1 := fresh "INV1" in pose proof INVh as I1; ff_open I1 end; ff_env OK; ff_tables; num_mark_words.
  Ltac ka_cuts INV q pc :=
    lazymatch pc with
    | 0xb9c84%Z => k0_cut ffk_c34 INV
    | 0xb9c64%Z => k0_cut ffk_c14 INV
    | 0xb9c60%Z => k0_cut ffk_c10 INV
    | 0xb9d0c%Z => k0_cut ffk_cbc INV
    | 0xb99c0%Z => first [ eapply (ffk_970 q); [exact INV | assumption | lia] | fail 100 "cut" pc ]
    end.

  Lemma ffk_93c : ff_ka 0xb998c.
  Proof using OK SHL1 SHL2. ka_start. astep. awalk ltac:(ka_cuts INV q). Qed.

  Lemma ff_930 : ff_ka 0xb9980.
  Proof using OK SHL1 SHL2.
    ka_start.
    awalk ltac:(fun pc => lazymatch pc with
      | 0xb998c%Z => first [ eapply (ffk_93c q); [exact INV | assumption | lia] | fail 100 "cut" pc ]
      | _ => ka_cuts INV q pc end).
  Qed.
End FFCF.
