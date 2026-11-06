(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Sj Require Import SjNumber.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Sj_num_kit Sj_num_walk.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_load ::= first [ solve_load_base | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].

Definition FF_ENTRY : Z := 0x3c0a0.
Definition FF_GTOP : Z := 0x101000.
Definition ff_spath_stmt : Prop := spath_stmt_g psegs 0x4d524 FF_GTOP.

Record ffenv : Type := mkFfEnv {
  f_ra : word; f_sp : word; f_gp : word; f_tp : word;
  f_s0 : word; f_s1 : word; f_s2 : word; f_s3 : word; f_s4 : word; f_s5 : word;
  f_s6 : word; f_s7 : word; f_s8 : word; f_s9 : word; f_s10 : word; f_s11 : word;
  f_A : Z; f_FIRST : Z; f_LAST : Z; f_lo : Z; f_txt : list byte; f_m0 : mem }.

Notation f_SP E := (bv_unsigned (f_sp E)).
Notation f_TL E := (Z.of_nat (length (f_txt E))).

Record ff_ok (E : ffenv) : Prop := mkFfOk {
  fo_room : (f_lo E + FF_STACK <= f_SP E)%Z;
  fo_gtop : (FF_GTOP <= f_lo E)%Z;
  fo_tlo : (f_A E + f_TL E <= f_lo E)%Z;
  fo_tmax : (f_TL E < NUM_TXT_MAX)%Z;
  fo_first : (f_A E <= f_FIRST E <= f_LAST E)%Z;
  fo_last : (f_LAST E <= f_A E + f_TL E)%Z }.

Notation ff_post E := (ff_post_g psegs (f_ra E) (f_sp E) (f_gp E) (f_tp E) (f_s0 E) (f_s1 E) (f_s2 E) (f_s3 E) (f_s4 E) (f_s5 E)
                          (f_s6 E) (f_s7 E) (f_s8 E) (f_s9 E) (f_s10 E) (f_s11 E) (f_lo E) (f_m0 E)).

Definition ff_saved (E : ffenv) : list cell :=
  [C8 (f_s8 E); C8 (f_s7 E); C8 (f_s6 E); C8 (f_s5 E); C8 (f_s4 E); C8 (f_s3 E); C8 (f_s2 E); C8 (f_s1 E); C8 (f_s0 E); C8 (f_ra E)].

Definition FFINV (E : ffenv) (mm : mem) : Prop :=
  (exists j v, rw_cells psegs mm (f_SP E + -96) (CB 8 j :: C8 v :: ff_saved E)) /\
  bytes_at psegs mm (f_A E) (f_txt E) /\
  mem_inv psegs mm /\ munch [(f_SP E - FF_STACK, f_SP E)]%Z (f_m0 E) mm /\ wmono psegs (f_m0 E) mm /\ stk psegs mm (f_lo E) (f_SP E + -96).

Ltac ff_open H :=
  let j := fresh "j" in let v := fresh "v" in
  destruct H as ((j & v & FR) & TXT & MI & MU & WM & ST);
  unfold ff_saved in FR; unfold FF_STACK, SPATH_STACK, NDC_STACK, P5_STACK, LM_STACK in MU;
  let TXB := fresh "TXB" in pose proof (bytes_at_bound _ _ _ _ TXT) as TXB.
Ltac ff_close :=
  lazymatch goal with
  | |- FFINV _ _ =>
      split; [eexists _, _; eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; eassumption
  end.
Ltac ff_env OK :=
  let ROOM := fresh "ROOM" in let GTOP := fresh "GTOP" in let TLO := fresh "TLO" in let TMAX := fresh "TMAX" in
  let HFIRST := fresh "HFIRST" in let HLAST := fresh "HLAST" in
  destruct OK as [ROOM GTOP TLO TMAX HFIRST HLAST];
  unfold FF_STACK, SPATH_STACK, NDC_STACK, P5_STACK, LM_STACK, FF_GTOP, NUM_TXT_MAX in *;
  lazymatch goal with E : ffenv |- _ =>
    let SPR := fresh "SPR" in pose proof (bv_unsigned_in_range 64 (f_sp E)) as SPR; unfold bv_modulus in SPR; cbn in SPR end.

Notation FFS E pc xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xt3 xt4 xt5 xt6 xF xfc mm :=
  (MS (mkR xra (Z_to_bv 64 (f_SP E + -96)) (f_gp E) (f_tp E) xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
           xs2 xs3 xs4 xs5 xs6 xs7 xs8 (f_s9 E) (f_s10 E) (f_s11 E) xt3 xt4 xt5 xt6) xF (Z_to_bv 64 pc) xfc None mm (seg_rom psegs)).

Section FFDEFS.
  Hypothesis HSPATH : ff_spath_stmt.
  Variable E : ffenv.
  Hypothesis OK : ff_ok E.

  Lemma ff_exit : forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xt3 xt4 xt5 xt6 xF xfc mm,
    FFINV E mm -> frm0 xfc ->
    evt psegs (ff_post E) (FFS E 0x3c7c4 xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK.
    intros until mm. intros INV FRM. ff_open INV. ff_env OK.
    do 10 zstep. zstep. zstep.
    release_frame FR ST (f_SP E).
    apply evt_done. unfold ff_post_g. do 17 eexists. exists mm.
    split; [cbv delta [mkR]; reflexivity|].
    unfold FF_STACK, SPATH_STACK, NDC_STACK, P5_STACK, LM_STACK.
    split; [exact FRM|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
  Qed.

  Lemma ff_938 : forall xra xt0 xt1 xt2 xs0 xs1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xt3 xt4 xt5 xt6 xF xfc mm,
    FFINV E mm -> frm0 xfc -> (f_FIRST E < f_LAST E)%Z ->
    evt psegs (ff_post E) (FFS E 0x3c82c xra xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 (f_FIRST E)) (Z_to_bv 64 (f_LAST E)) xa2 xa3 xa4 xa5 xa6 xa7
                               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using HSPATH OK.
    intros until mm. intros INV FRM HLT. ff_open INV. ff_env OK.
    assert (LO0 : (0 <= f_lo E)%Z) by (destruct ST as [? _]; assumption).
    walk ltac:(fun pc => lazymatch pc with | 0x4d524%Z => idtac end).
    change (CB 8 j :: C8 v :: [C8 (f_s8 E); C8 (f_s7 E); C8 (f_s6 E); C8 (f_s5 E); C8 (f_s4 E); C8 (f_s3 E); C8 (f_s2 E); C8 (f_s1 E); C8 (f_s0 E); C8 (f_ra E)])
      with ([CB 8 j] ++ [C8 v] ++ ff_saved E) in FR.
    apply num_rw_cells_app in FR. destruct FR as [FR0 FR]. apply num_rw_cells_app in FR. destruct FR as [VAL SAVED].
    cbn [cells_size csize Nat.add] in VAL, SAVED.
    replace (f_SP E + -96 + Z.of_nat 8)%Z with (f_SP E + -88)%Z in * by lia.
    replace (f_SP E + -88 + Z.of_nat 8)%Z with (f_SP E + -80)%Z in * by lia.
    pose proof HSPATH as HS. unfold ff_spath_stmt, spath_stmt_g in HS.
    eapply evt_cut.
    { eapply evt_eq; [| eapply HS with (A := f_A E) (FIRST := f_FIRST E) (LAST := f_LAST E) (OUT := (f_SP E + -88)%Z) (lo := f_lo E) (txt := f_txt E) (v0 := v)];
        [ unfold SPATH_A4; num_st_eq | .. ]; rewrite ?unsigned_lit by lia; unfold SPATH_STACK, NDC_STACK, P5_STACK, LM_STACK, FF_GTOP, NUM_TXT_MAX;
        [ exact MI | exact FRM | exact ST | lia | lia | exact TXT | lia | lia | lia | lia | exact VAL | lia ]. }
    cbv beta. intros ms' P. unfold spath_post_g in P.
    destruct P as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F3 & fc3 & m3 & v3 & -> & FRM3 & MUc & WMc & MI3 & VAL3 & ST3).
    rewrite !unsigned_lit in MUc, ST3 by lia. unfold SPATH_STACK, NDC_STACK, P5_STACK, LM_STACK in MUc.
    clear VAL ST.
    lazymatch type of MUc with munch _ ?mo ?mn => transport_after_call psegs mo mn MUc WMc end.
    clear MUc WMc MI HS.
    num_ret_pc.
    assert (FR : rw_cells psegs m3 (f_SP E + -96) (CB 8 j :: C8 v3 :: ff_saved E)).
    { change (CB 8 j :: C8 v3 :: ff_saved E) with ([CB 8 j] ++ [C8 v3] ++ ff_saved E).
      apply num_rw_cells_app. split; [exact FR0|]. cbn [cells_size csize Nat.add].
      replace (f_SP E + -96 + Z.of_nat 8)%Z with (f_SP E + -88)%Z by lia.
      apply num_rw_cells_app. split; [exact VAL3|]. cbn [cells_size csize Nat.add].
      replace (f_SP E + -88 + Z.of_nat 8)%Z with (f_SP E + -80)%Z by lia. exact SAVED. }
    clear FR0 VAL3 SAVED. rename ST3 into ST. rename MI3 into MI.
    assert (INV : FFINV E m3) by ff_close.
    unfold ff_saved in FR.
    walk ltac:(fun pc => lazymatch pc with
      | 0x3c7c4%Z => first [ eapply ff_exit; [exact INV | assumption] | fail 100 "cut" pc ]
      end).
  Qed.
End FFDEFS.
