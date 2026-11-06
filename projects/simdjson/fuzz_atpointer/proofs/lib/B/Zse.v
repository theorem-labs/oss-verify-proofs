(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.AS Require Import Zp7 Z1b.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS Z119 FP Z10q.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Sj Require Import Zpe SjNumU.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Rnd Zso Zvm.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.U Require Import Zv7 Zva.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.B Require Import Layout Zks D_defs D_kit D_clx Zpm Zpl Zq2 Sj_rtf
  Zqc Zqd Zsl Zqh Zqf Zsf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | asan_zr_hook | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].
Local Ltac nnorm ::= nnorm_cf.
Local Ltac num_abstract_data ::= num_abstract_data_u.

Section FFCF.
  Variable E : ffenv.
  Hypothesis OK : ff_ok E.
  Variable m0 : mem.

  Hypothesis SHPT : forall m', munch (FF_W E) m0 m' -> wmono bsegs m0 m' -> shz m' (f_p E) (8 * (f_n E / 8)).
  Hypothesis SHL1 : forall m', munch (FF_W E) m0 m' -> wmono bsegs m0 m' -> shz m' 0x28260 10416.
  Hypothesis SHL2 : forall m', munch (FF_W E) m0 m' -> wmono bsegs m0 m' -> shz m' 0x2abe0 640.
  Notation A := (f_A E).
  Notation TL := (f_TL E).
  Notation FIRST := (f_FIRST E).
  Notation LAST := (f_LAST E).

  Ltac num_mark_words :=
    repeat match goal with
    | x : word |- _ => lazymatch goal with _ : IsData x |- _ => fail | _ => idtac end; let M := fresh "DM" in assert (M : IsData x) by exact I
    end.
  Ltac ff_tables :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let p5t := fresh "p5t" in let P5L := fresh "P5L" in let P5T := fresh "P5T" in let P5Z := fresh "P5Z" in
      destruct (image_readable_b bsegs mm (Z.to_nat 10416) 0x28260 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as (p5t & P5L & P5T);
      assert (P5Z : Z.of_nat (length p5t) = 10416%Z) by (rewrite P5L; apply Z2Nat.id; lia); clear P5L;
      let fmin := fresh "fmin" in let FML := fresh "FML" in let FMIN := fresh "FMIN" in
      destruct (image_readable_b bsegs mm 4 0x11c5a0 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as (fmin & FML & FMIN);
      let p10d := fresh "p10d" in let P10L := fresh "P10L" in let P10D := fresh "P10D" in
      destruct (image_readable_b bsegs mm 184 0x2ace8 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as (p10d & P10L & P10D);
      let mxm := fresh "mxm" in let MXL := fresh "MXL" in let MXM := fresh "MXM" in
      destruct (image_readable_b bsegs mm 184 0x2ada0 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as (mxm & MXL & MXM)
    end.

  Definition ff_k0 (pc : Z) : Prop :=
    forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm, FFINV E m0 mm -> frm0 xfc -> evt bsegs (ff_mid E m0) (FFS E pc xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).

  Definition ff_kq (pc : Z) : Prop :=
    forall (q : Z) xra xt0 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm, FFINV E m0 mm -> frm0 xfc -> (-342 <= q <= 308)%Z ->
      evt bsegs (ff_mid E m0) (FFS E pc xra xt0 (Z_to_bv 64 (q)) xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 (Z_to_bv 64 2147450880) xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).

  Definition ff_ka (pc : Z) : Prop :=
    forall (q : Z) xra xt0 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm, FFINV E m0 mm -> frm0 xfc -> (-9223372036854775808 <= q < 9223372036854775808)%Z ->
      evt bsegs (ff_mid E m0) (FFS E pc xra xt0 (Z_to_bv 64 (q)) xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 (Z_to_bv 64 2147450880) xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).

  Definition ff_kc (pc : Z) : Prop :=
    forall (q : Z) xra xt0 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm, FFINV E m0 mm -> frm0 xfc -> (-22 <= q <= 22)%Z ->
      evt bsegs (ff_mid E m0) (FFS E pc xra xt0 (Z_to_bv 64 (q)) xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 (Z_to_bv 64 2147450880) xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).

  Definition ff_kn (pc : Z) : Prop :=
    forall (q : Z) xra xt0 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm, FFINV E m0 mm -> frm0 xfc -> (-22 <= q <= -1)%Z ->
      evt bsegs (ff_mid E m0) (FFS E pc xra xt0 (Z_to_bv 64 (q)) xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 (Z_to_bv 64 2147450880) xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).

  Ltac k0_start := unfold ff_k0; intros until mm; intros INV FRM; pose proof INV as INV0;
    lazymatch goal with INVh : FFINV _ _ _ |- _ => let I1 := fresh "INV1" in pose proof INVh as I1; ff_open I1 end; ff_env OK; num_mark_words.
  Ltac kq_start K := unfold K; intros until mm; intros INV FRM Hq; pose proof INV as INV0;
    lazymatch goal with INVh : FFINV _ _ _ |- _ => let I1 := fresh "INV1" in pose proof INVh as I1; ff_open I1 end; ff_env OK; ff_tables; num_mark_words.

  Ltac k0_cut K INV := first [ eapply evt_eq; [| eapply K]; [num_st_eq | exact INV | assumption]
                             | eapply evt_eq; [| eapply K]; [num_st_eq | ff_close | assumption] | fail 100 "cut" ].
  Ltac kq_cut K q INV := first [ eapply evt_eq; [| eapply (K q)]; [num_st_eq | exact INV | assumption | lia] | fail 100 "cutq" ].

  Lemma ffk_b70 : ff_k0 0x9bbac.
  Proof using OK. unfold ff_k0. intros until mm. intros INV FRM. eapply ff_exit; [exact OK | exact INV | exact FRM]. Qed.

  Lemma ffk_b6c : ff_k0 0x9bba8.
  Proof using OK. k0_start. bstep. bwalk ltac:(fun pc => lazymatch pc with | 0x9bcf8%Z => u_trap pc | 0x9bbac%Z => k0_cut ffk_b70 INV end). Qed.

  Lemma ffk_b50 : ff_k0 0x9bb8c.
  Proof using OK. k0_start. bstep. bwalk ltac:(fun pc => lazymatch pc with | 0x9bcf8%Z => u_trap pc | 0x9bba8%Z => k0_cut ffk_b6c INV end). Qed.

  Lemma ffk_c60 : ff_k0 0x9bc9c.
  Proof using OK. k0_start. bstep. bwalk ltac:(fun pc => lazymatch pc with | 0x9bcf8%Z => u_trap pc | 0x9bba8%Z => k0_cut ffk_b6c INV end). Qed.

  Lemma ffk_c5c : ff_k0 0x9bc98.
  Proof using OK. k0_start. bstep. bwalk ltac:(fun pc => lazymatch pc with | 0x9bcf8%Z => u_trap pc | 0x9bc9c%Z => k0_cut ffk_c60 INV end). Qed.

  Lemma ffk_c50 : ff_k0 0x9bc8c.
  Proof using OK. k0_start. bstep. bwalk ltac:(fun pc => lazymatch pc with | 0x9bcf8%Z => u_trap pc | 0x9bba8%Z => k0_cut ffk_b6c INV | 0x9bc98%Z => k0_cut ffk_c5c INV end). Qed.

  Lemma ffk_c68 : ff_k0 0x9bca4.
  Proof using OK. k0_start. bstep. bwalk ltac:(fun pc => lazymatch pc with | 0x9bcf8%Z => u_trap pc | 0x9bc9c%Z => k0_cut ffk_c60 INV | 0x9bc98%Z => k0_cut ffk_c5c INV end). Qed.

  Lemma ffk_b14 : ff_k0 0x9bb50.
  Proof using OK. k0_start. bstep. bwalk ltac:(fun pc => lazymatch pc with | 0x9bcf8%Z => u_trap pc | 0x9bb8c%Z => k0_cut ffk_b50 INV end). Qed.

  Lemma ffk_ad0 : ff_k0 0x9bb0c.
  Proof using OK. k0_start. bstep. bwalk ltac:(fun pc => lazymatch pc with | 0x9bcf8%Z => u_trap pc | 0x9bb50%Z => k0_cut ffk_b14 INV end). Qed.

  Lemma ffk_a90 : ff_k0 0x9bacc.
  Proof using OK. k0_start. bstep. bwalk ltac:(fun pc => lazymatch pc with | 0x9bcf8%Z => u_trap pc | 0x9bb0c%Z => k0_cut ffk_ad0 INV end). Qed.

  Lemma ffk_b30 : ff_k0 0x9bb6c.
  Proof using OK. k0_start. bstep. bwalk ltac:(fun pc => lazymatch pc with | 0x9bcf8%Z => u_trap pc | 0x9bb8c%Z => k0_cut ffk_b50 INV end). Qed.

  Lemma ffk_9ec : ff_k0 0x9ba28.
  Proof using OK. k0_start. bstep. bwalk ltac:(fun pc => lazymatch pc with | 0x9bcf8%Z => u_trap pc | 0x9bacc%Z => k0_cut ffk_a90 INV | 0x9bb6c%Z => k0_cut ffk_b30 INV | 0x9bb8c%Z => k0_cut ffk_b50 INV end). Qed.

  Lemma ffq_8c4 : ff_kq 0x9b900.
  Proof using OK SHL1 SHL2.
    kq_start ff_kq. bstep.
    bwalk ltac:(fun pc => lazymatch pc with | 0x9bcf8%Z => u_trap pc | 0x9ba28%Z => k0_cut ffk_9ec INV end).
  Qed.

  Lemma ffa_890 : ff_ka 0x9b8cc.
  Proof using OK SHL1 SHL2.
    kq_start ff_ka. bstep.
    bwalk ltac:(fun pc => lazymatch pc with | 0x9bcf8%Z => u_trap pc | 0x9bb8c%Z => k0_cut ffk_b50 INV | 0x9b900%Z => kq_cut ffq_8c4 q INV end).
  Qed.

  Ltac clg_cuts q INV :=
    fun pc => lazymatch pc with
      | 0x9bcf8%Z => u_trap pc
      | 0x9bc8c%Z => k0_cut ffk_c50 INV
      | 0x9bca4%Z => k0_cut ffk_c68 INV
      | 0x9b900%Z => kq_cut ffq_8c4 q INV
      | 0x9b8cc%Z => kq_cut ffa_890 q INV
      end.

  Lemma ffc_c1c : ff_kn 0x9bc58.
  Proof using OK SHL1 SHL2. kq_start ff_kn. bstep. bwalk ltac:(clg_cuts q INV). Qed.

  Lemma ffc_bb0 : ff_kc 0x9bbec.
  Proof using OK SHL1 SHL2. kq_start ff_kc. bwalk ltac:(clg_cuts q INV). Qed.

  Lemma ffc_a34 : ff_kc 0x9ba70.
  Proof using OK SHL1 SHL2.
    kq_start ff_kc. bstep.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0x9bbec%Z => kq_cut ffc_bb0 q INV
      | 0x9bc58%Z => kq_cut ffc_c1c q INV
      | _ => clg_cuts q INV pc end).
  Qed.

  Lemma ff_884 : ff_ka 0x9b8c0.
  Proof using OK SHL1 SHL2.
    kq_start ff_ka.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0x9ba70%Z => first [ eapply evt_eq; [| eapply (ffc_a34 q)]; [num_st_eq | exact INV | assumption | Z.div_mod_to_equations; lia] | fail 100 "cut" pc ]
      | _ => clg_cuts q INV pc end).
  Qed.
End FFCF.
