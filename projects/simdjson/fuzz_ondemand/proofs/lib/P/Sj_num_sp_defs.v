(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjNumber.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Sj_num_kit Sj_num_walk.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ solve_load_base | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].

Definition SPATH_ENTRY : Z := 0x3a1d0.
Definition SPATH_GTOP : Z := 0xab000.

Record spenv : Type := mkSpEnv {
  q_ra : word; q_sp : word; q_gp : word; q_tp : word;
  q_s0 : word; q_s1 : word; q_s2 : word; q_s3 : word; q_s4 : word; q_s5 : word;
  q_s6 : word; q_s7 : word; q_s8 : word; q_s9 : word; q_s10 : word; q_s11 : word;
  q_A : Z; q_FIRST : Z; q_LAST : Z; q_OUT : Z; q_lo : Z; q_txt : list byte; q_m0 : mem }.

Notation q_SP E := (bv_unsigned (q_sp E)).
Notation q_TL E := (Z.of_nat (length (q_txt E))).

Record sp_ok (E : spenv) : Prop := mkSpOk {
  so_room : (q_lo E + SPATH_STACK <= q_SP E)%Z;
  so_gtop : (SPATH_GTOP <= q_lo E)%Z;
  so_tlo : (q_A E + q_TL E <= q_lo E)%Z;
  so_tmax : (q_TL E < NUM_TXT_MAX)%Z;
  so_first : (q_A E <= q_FIRST E < q_LAST E)%Z;
  so_last : (q_LAST E <= q_A E + q_TL E)%Z;
  so_out : (q_SP E <= q_OUT E)%Z }.

Definition sp_W (E : spenv) : list (Z * Z) := [(q_SP E - SPATH_STACK, q_SP E); (q_OUT E, q_OUT E + 8)]%Z.
Notation sp_post E := (spath_post_g psegs (q_ra E) (q_sp E) (q_gp E) (q_tp E) (q_s0 E) (q_s1 E) (q_s2 E) (q_s3 E) (q_s4 E) (q_s5 E)
                          (q_s6 E) (q_s7 E) (q_s8 E) (q_s9 E) (q_s10 E) (q_s11 E) (q_OUT E) (q_lo E) (q_m0 E)).

Definition sp_saved (E : spenv) : list cell :=
  [C8 (q_s11 E); C8 (q_s10 E); C8 (q_s9 E); C8 (q_s8 E); C8 (q_s7 E); C8 (q_s6 E); C8 (q_s5 E); C8 (q_s4 E);
   C8 (q_s3 E); C8 (q_s2 E); C8 (q_s1 E); C8 (q_s0 E); C8 (q_ra E)].

Definition SPINV (E : spenv) (mm : mem) : Prop :=
  (exists j, rw_cells psegs mm (q_SP E + -688) [CB 32 j]) /\
  (exists j, rw_cells psegs mm (q_SP E + -656) [CB 32 j]) /\
  (exists j, rw_cells psegs mm (q_SP E + -624) [CB 8 j]) /\
  (exists j, rw_cells psegs mm (q_SP E + -616) [CB 496 j]) /\
  (exists j, rw_cells psegs mm (q_SP E + -120) [CB 2 j]) /\
  (exists j, rw_cells psegs mm (q_SP E + -118) [CB 6 j]) /\
  (exists j, rw_cells psegs mm (q_SP E + -112) [CB 8 j]) /\
  rw_cells psegs mm (q_SP E + -104) (sp_saved E) /\
  (exists v, rw_cells psegs mm (q_OUT E) [C8 v]) /\
  bytes_at psegs mm (q_A E) (q_txt E) /\
  mem_inv psegs mm /\ munch (sp_W E) (q_m0 E) mm /\ wmono psegs (q_m0 E) mm /\ stk psegs mm (q_lo E) (q_SP E + -688).

Ltac sp_open H :=
  let j1 := fresh "j" in let j2 := fresh "j" in let j3 := fresh "j" in let j4 := fresh "j" in let j5 := fresh "j" in
  let j6 := fresh "j" in let j7 := fresh "j" in let v := fresh "v" in
  destruct H as ((j1 & PNS) & (j2 & SPANS) & (j3 & PERR) & (j4 & BG) & (j5 & BGN) & (j6 & BGP) & (j7 & DGC) & SAVED & (v & OUTC) & TXT & MI & MU & WM & ST);
  unfold sp_saved in SAVED; unfold sp_W, SPATH_STACK, NDC_STACK, P5_STACK, LM_STACK in MU;
  let TXB := fresh "TXB" in pose proof (bytes_at_bound _ _ _ _ TXT) as TXB.

Ltac sp_forget_obj :=
  lazymatch goal with
  | |- exists j, rw_cells ?s ?m ?A [CB ?n j] =>
      lazymatch goal with
      | H : rw_cells s m A ?cs |- _ =>
          let j := fresh "j" in let Hj := fresh "Hj" in
          destruct (rw_cells_forget s m A cs H) as [j Hj]; exists j; exact Hj
      end
  end.
Ltac sp_close :=
  lazymatch goal with
  | |- SPINV _ _ =>
      split; [sp_forget_obj|]; split; [sp_forget_obj|]; split; [sp_forget_obj|]; split; [sp_forget_obj|];
      split; [sp_forget_obj|]; split; [sp_forget_obj|]; split; [sp_forget_obj|]; split; [eassumption|];
      split; [eexists; eassumption|]; split; [eassumption|];
      split; [eassumption|]; split; [eassumption|]; split; eassumption
  end.
Ltac sp_env OK :=
  let ROOM := fresh "ROOM" in let GTOP := fresh "GTOP" in let TLO := fresh "TLO" in let TMAX := fresh "TMAX" in
  let HFIRST := fresh "HFIRST" in let HLAST := fresh "HLAST" in let HOUT := fresh "HOUT" in
  destruct OK as [ROOM GTOP TLO TMAX HFIRST HLAST HOUT];
  unfold SPATH_STACK, NDC_STACK, P5_STACK, LM_STACK, SPATH_GTOP, NUM_TXT_MAX in *;
  lazymatch goal with E : spenv |- _ =>
    let SPR := fresh "SPR" in pose proof (bv_unsigned_in_range 64 (q_sp E)) as SPR; unfold bv_modulus in SPR; cbn in SPR end.

Definition sp_spans (IP IL FPT FL : Z) : list cell := [C8 (Z_to_bv 64 IP); C8 (Z_to_bv 64 IL); C8 (Z_to_bv 64 FPT); C8 (Z_to_bv 64 FL)].
Definition SPINV2 (E : spenv) (mm : mem) (IP IL FPT FL : Z) : Prop :=
  (exists j, rw_cells psegs mm (q_SP E + -688) [CB 32 j]) /\
  rw_cells psegs mm (q_SP E + -656) (sp_spans IP IL FPT FL) /\
  (exists j, rw_cells psegs mm (q_SP E + -624) [CB 8 j]) /\
  (exists j, rw_cells psegs mm (q_SP E + -616) [CB 496 j]) /\
  (exists j, rw_cells psegs mm (q_SP E + -120) [CB 2 j]) /\
  (exists j, rw_cells psegs mm (q_SP E + -118) [CB 6 j]) /\
  (exists j, rw_cells psegs mm (q_SP E + -112) [CB 8 j]) /\
  rw_cells psegs mm (q_SP E + -104) (sp_saved E) /\
  (exists v, rw_cells psegs mm (q_OUT E) [C8 v]) /\
  bytes_at psegs mm (q_A E) (q_txt E) /\
  mem_inv psegs mm /\ munch (sp_W E) (q_m0 E) mm /\ wmono psegs (q_m0 E) mm /\ stk psegs mm (q_lo E) (q_SP E + -688).

Ltac sp_open2 H :=
  let j1 := fresh "j" in let j3 := fresh "j" in let j4 := fresh "j" in let j5 := fresh "j" in
  let j6 := fresh "j" in let j7 := fresh "j" in let v := fresh "v" in
  destruct H as ((j1 & PNS) & SPANS & (j3 & PERR) & (j4 & BG) & (j5 & BGN) & (j6 & BGP) & (j7 & DGC) & SAVED & (v & OUTC) & TXT & MI & MU & WM & ST);
  unfold sp_saved in SAVED; unfold sp_spans in SPANS; unfold sp_W, SPATH_STACK, NDC_STACK, P5_STACK, LM_STACK in MU;
  let TXB := fresh "TXB" in pose proof (bytes_at_bound _ _ _ _ TXT) as TXB.
Ltac sp_close2 :=
  lazymatch goal with
  | |- SPINV2 _ _ _ _ _ _ =>
      split; [sp_forget_obj|]; split; [eassumption|]; split; [sp_forget_obj|]; split; [sp_forget_obj|];
      split; [sp_forget_obj|]; split; [sp_forget_obj|]; split; [sp_forget_obj|]; split; [eassumption|];
      split; [eexists; eassumption|]; split; [eassumption|];
      split; [eassumption|]; split; [eassumption|]; split; eassumption
  end.

Lemma SPINV_of_SPINV2 : forall E mm IP IL FPT FL, SPINV2 E mm IP IL FPT FL -> SPINV E mm.
Proof.
  intros E mm IP IL FPT FL (H1 & H2 & H3). split; [exact H1|]. split; [|exact H3].
  destruct (rw_cells_forget psegs mm _ _ H2) as [j Hj]. exists j. exact Hj.
Qed.

Notation SPS E pc xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm :=
  (MS (mkR xra (Z_to_bv 64 (q_SP E + -688)) (q_gp E) (q_tp E) xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
           xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6) xF (Z_to_bv 64 pc) xfc None mm (seg_rom psegs)).

Section SPDEFS.
  Variable E : spenv.
  Hypothesis OK : sp_ok E.

  Lemma sp_exit : forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    SPINV E mm -> frm0 xfc ->
    evt psegs (sp_post E) (SPS E 0x3b5f4 xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK.
    intros until mm. intros INV FRM. sp_open INV. sp_env OK.
    do 13 zstep. zstep. zstep.
    release_frame PNS ST (q_SP E + -656)%Z.
    release_frame SPANS ST (q_SP E + -624)%Z.
    release_frame PERR ST (q_SP E + -616)%Z.
    release_frame BG ST (q_SP E + -120)%Z.
    release_frame BGN ST (q_SP E + -118)%Z.
    release_frame BGP ST (q_SP E + -112)%Z.
    release_frame DGC ST (q_SP E + -104)%Z.
    release_frame SAVED ST (q_SP E).
    apply evt_done. unfold spath_post_g. do 17 eexists. exists mm, v.
    split; [cbv delta [mkR]; reflexivity|].
    unfold SPATH_STACK, NDC_STACK, P5_STACK, LM_STACK.
    split; [exact FRM|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact OUTC| exact ST].
  Qed.

  Lemma sp_a1c : forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    SPINV E mm -> frm0 xfc ->
    evt psegs (sp_post E) (SPS E 0x3b5bc xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 (Z_to_bv 64 (q_OUT E)) xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK.
    intros until mm. intros INV FRM. sp_open INV. sp_env OK.
    assert (IsData xs0) by exact I. assert (IsData xs2) by exact I. assert (IsData xa6) by exact I. assert (IsData xa7) by exact I.
    walk ltac:(fun pc => lazymatch pc with
      | 0x3b5f4%Z => first [ eapply sp_exit; [sp_close | exact FRM] | fail 100 "cut" pc ]
      end).
  Qed.
End SPDEFS.
