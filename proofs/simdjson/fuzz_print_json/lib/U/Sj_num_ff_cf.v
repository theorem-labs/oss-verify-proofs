(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjNumber SjNumU.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Sj_num_kitu Sj_num_kitn Sj_num_kitw Sj_num_sp_defs Sj_num_sp_dc Sj_num_sp_ce Sj_num_sp_cf2 Sj_num_ff_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ solve_load_base | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].
Local Ltac num_abstract_data ::= num_abstract_data_u.
Local Ltac nnorm ::= nnorm_cf.

Section FFUCF.
  Variable E : ffuenv.
  Hypothesis OK : ffu_ok E.

  Ltac num_mark_words :=
    repeat match goal with
    | x : word |- _ => lazymatch goal with _ : IsData x |- _ => fail | _ => idtac end; let M := fresh "DM" in assert (M : IsData x) by exact I
    end.
  Ltac ffk_tables mm :=
    let tb := fresh "tb" in let TBL := fresh "TBL" in let TB := fresh "TB" in let TBZ := fresh "TBZ" in
    destruct (image_readable_b usegs mm (Z.to_nat 10416) 0x19fa8 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as (tb & TBL & TB);
    assert (TBZ : Z.of_nat (length tb) = 10416%Z) by (rewrite TBL; apply Z2Nat.id; lia); clear TBL.

  Definition ffk0 (pc : Z) : Prop :=
    forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
      FFUINV E mm -> frm0 xfc ->
      evt usegs (ffu_post E) (FFS E pc xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).

  Definition ffkq (pc : Z) : Prop :=
    forall (q : Z) xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
      FFUINV E mm -> frm0 xfc -> (-342 <= q <= 308)%Z ->
      evt usegs (ffu_post E) (FFS E pc xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 (Z_to_bv 64 q) xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).

  Ltac ffk_start :=
    intros until mm; intros INV FRM;
    lazymatch goal with INVh : FFUINV _ ?m |- _ => let INV0 := fresh "INV0" in pose proof INVh as INV0; ffu_open INV0; ffu_env OK end;
    num_mark_words.
  Ltac ffq_start :=
    intros until mm; intros INV FRM Hq;
    lazymatch goal with INVh : FFUINV _ ?m |- _ => let INV0 := fresh "INV0" in pose proof INVh as INV0; ffu_open INV0; ffu_env OK; ffk_tables m end;
    num_mark_words.

  Ltac ffk_cut K FRM :=
    first [ let INV1 := fresh "INV1" in
            num_cur_mem ltac:(fun m1 => assert (INV1 : FFUINV E m1) by ffu_close);
            eapply evt_eq; [| eapply K]; [num_st_eq | exact INV1 | assumption]
          | fail 100 "cut" ].
  Ltac ffq_cut K q INV FRM := first [ eapply evt_eq; [| eapply (K q)]; [num_st_eq | exact INV | assumption | lia] | fail 100 "cut" ].

  Lemma ffk_864 : ffk0 0x413f4.
  Proof using OK. unfold ffk0. intros. eapply (ffu_864 E OK); eassumption. Qed.

  Lemma ffk_844 : ffk0 0x413d4.
  Proof using OK.
    unfold ffk0. ffk_start.
    uwalk ltac:(fun pc => lazymatch pc with | 0x41538%Z => u_trap pc | 0x413f4%Z => ffk_cut ffk_864 FRM end).
  Qed.
  Ltac ffk_walk_to K FRM := ffk_start; nstep; uwalk ltac:(fun pc => lazymatch pc with | 0x41538%Z => u_trap pc | _ => K pc end).
  Lemma ffk_808 : ffk0 0x41398.
  Proof using OK. unfold ffk0. ffk_start. nstep. uwalk ltac:(fun pc => lazymatch pc with | 0x41538%Z => u_trap pc | 0x413d4%Z => ffk_cut ffk_844 FRM end). Qed.
  Lemma ffk_7c4 : ffk0 0x41354.
  Proof using OK. unfold ffk0. ffk_start. nstep. uwalk ltac:(fun pc => lazymatch pc with | 0x41538%Z => u_trap pc | 0x41398%Z => ffk_cut ffk_808 FRM end). Qed.
  Lemma ffk_784 : ffk0 0x41314.
  Proof using OK. unfold ffk0. ffk_start. nstep. uwalk ltac:(fun pc => lazymatch pc with | 0x41538%Z => u_trap pc | 0x41354%Z => ffk_cut ffk_7c4 FRM end). Qed.
  Lemma ffk_6f0 : ffk0 0x41280.
  Proof using OK.
    unfold ffk0. ffk_start. nstep.
    uwalk ltac:(fun pc => lazymatch pc with | 0x41538%Z => u_trap pc | 0x41314%Z => ffk_cut ffk_784 FRM | 0x413d4%Z => ffk_cut ffk_844 FRM end).
  Qed.

  Lemma ffq_5e8 : ffkq 0x41178.
  Proof using OK.
    unfold ffkq. ffq_start. nstep.
    uwalk ltac:(fun pc => lazymatch pc with | 0x41538%Z => u_trap pc | 0x41280%Z => ffk_cut ffk_6f0 FRM end).
  Qed.

  Lemma ffu_5b4 : forall (q : Z) xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    FFUINV E mm -> frm0 xfc -> (-9223372036854775808 <= q < 9223372036854775808)%Z ->
    evt usegs (ffu_post E) (FFS E 0x41144 xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 (Z_to_bv 64 q) xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK.
    intros until mm. intros INV FRM Hq. pose proof INV as INV0. ffu_open INV0. ffu_env OK. assert (D3 : IsData xa3) by exact I.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x41538%Z => u_trap pc
      | 0x413d4%Z => ffk_cut ffk_844 FRM
      | 0x41178%Z => ffq_cut ffq_5e8 q INV FRM
      end).
  Qed.

  Ltac clg_cuts q INV FRM :=
    fun pc => lazymatch pc with
      | 0x41538%Z => u_trap pc
      | 0x413f4%Z => ffk_cut ffk_864 FRM
      | 0x413d4%Z => ffk_cut ffk_844 FRM
      | 0x41178%Z => ffq_cut ffq_5e8 q INV FRM
      | 0x41144%Z => first [ eapply evt_eq; [| eapply (ffu_5b4 q)]; [num_st_eq | exact INV | assumption | lia] | fail 100 "cut" pc ]
      end.
  Ltac clg_tables mm :=
    let p10 := fresh "p10" in let P10L := fresh "P10L" in let P10 := fresh "P10" in let mxm := fresh "mxm" in let MXL := fresh "MXL" in let MXM := fresh "MXM" in
    let fmin := fresh "fmin" in let FML := fresh "FML" in let FMIN := fresh "FMIN" in
    destruct (image_readable_b usegs mm 4 0xdcc10 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as (fmin & FML & FMIN);
    destruct (image_readable_b usegs mm 184 0x1ca00 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as (p10 & P10L & P10);
    destruct (image_readable_b usegs mm 184 0x1cab8 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as (mxm & MXL & MXM).

  Lemma ffu_8b0 : forall (q : Z) xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    FFUINV E mm -> frm0 xfc -> (-22 <= q <= 22)%Z ->
    evt usegs (ffu_post E) (FFS E 0x41440 xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 (Z_to_bv 64 q) xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK.
    intros until mm. intros INV FRM Hq. pose proof INV as INV0. ffu_open INV0. ffu_env OK. clg_tables mm.
    assert (D3 : IsData xa3) by exact I. assert (D2 : IsData xa2) by exact I.
    uwalk ltac:(clg_cuts q INV FRM).
  Qed.

  Lemma ffu_738 : forall (q : Z) xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    FFUINV E mm -> frm0 xfc -> (-22 <= q <= 22)%Z ->
    evt usegs (ffu_post E) (FFS E 0x412c8 xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 (Z_to_bv 64 q) xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK.
    intros until mm. intros INV FRM Hq. pose proof INV as INV0. ffu_open INV0. ffu_env OK. clg_tables mm.
    assert (D3 : IsData xa3) by exact I. assert (D2 : IsData xa2) by exact I.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x41440%Z => first [ eapply evt_eq; [| eapply (ffu_8b0 q)]; [num_st_eq | exact INV | assumption | lia] | fail 100 "cut" pc ]
      | _ => clg_cuts q INV FRM pc
      end).
  Qed.

  Lemma ffu_5a8 : forall (q : Z) xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    FFUINV E mm -> frm0 xfc -> (-9223372036854775808 <= q < 9223372036854775808)%Z ->
    evt usegs (ffu_post E) (FFS E 0x41138 xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 (Z_to_bv 64 q) xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK.
    intros until mm. intros INV FRM Hq. pose proof INV as INV0. ffu_open INV0. ffu_env OK. assert (D3 : IsData xa3) by exact I.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x412c8%Z => first [ eapply evt_eq; [| eapply (ffu_738 q)]; [num_st_eq | exact INV | assumption | Z.div_mod_to_equations; lia] | fail 100 "cut" pc ]
      | 0x41178%Z => first [ eapply evt_eq; [| eapply (ffq_5e8 q)]; [num_st_eq | exact INV | assumption | Z.div_mod_to_equations; lia] | fail 100 "cut" pc ]
      | _ => clg_cuts q INV FRM pc
      end).
  Qed.
End FFUCF.
