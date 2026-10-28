(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjNumber SjNumU.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Sj_num_kitu Sj_num_kitn Sj_num_kitw Sj_num_sp_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_load ::= first [ solve_load_base | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].
Local Ltac num_abstract_data ::= num_abstract_data_u.
Local Ltac nnorm ::= nnorm_w.

Definition FFU_ENTRY : Z := 0x40da0.
Definition ffu_spath_stmt : Prop := spathu_stmt_g usegs 0x5b558 NUMU_GTOP.

Record ffuenv : Type := mkFfuEnv {
  f_ra : word; f_sp : word; f_gp : word; f_tp : word;
  f_s0 : word; f_s1 : word; f_s2 : word; f_s3 : word; f_s4 : word; f_s5 : word;
  f_s6 : word; f_s7 : word; f_s8 : word; f_s9 : word; f_s10 : word; f_s11 : word;
  f_A : Z; f_FIRST : Z; f_LAST : Z; f_lo : Z; f_txt : list byte; f_m0 : mem }.

Notation f_SP E := (bv_unsigned (f_sp E)).
Notation f_TL E := (Z.of_nat (length (f_txt E))).

Record ffu_ok (E : ffuenv) : Prop := mkFfuOk {
  fo_room : (f_lo E + FFU_STACK <= f_SP E)%Z;
  fo_gtop : (NUMU_GTOP <= f_lo E)%Z;
  fo_sp16 : (f_SP E mod 16 = 0)%Z;
  fo_tlo : (f_A E + f_TL E <= f_lo E)%Z;
  fo_tmax : (f_TL E < NUM_TXT_MAX)%Z;
  fo_a0 : (0 < f_A E)%Z;
  fo_first : (f_A E <= f_FIRST E <= f_LAST E)%Z;
  fo_last : (f_LAST E <= f_A E + f_TL E)%Z }.

Notation ffu_post E := (ffu_post_g usegs (f_ra E) (f_sp E) (f_gp E) (f_tp E) (f_s0 E) (f_s1 E) (f_s2 E) (f_s3 E) (f_s4 E) (f_s5 E)
                          (f_s6 E) (f_s7 E) (f_s8 E) (f_s9 E) (f_s10 E) (f_s11 E) (f_lo E) (f_m0 E)).

Definition ffu_saved (E : ffuenv) : list cell :=
  [C8 (f_s11 E); C8 (f_s10 E); C8 (f_s9 E); C8 (f_s8 E); C8 (f_s7 E); C8 (f_s6 E); C8 (f_s5 E); C8 (f_s4 E); C8 (f_s3 E); C8 (f_s2 E); C8 (f_s1 E); C8 (f_s0 E); C8 (f_ra E)].

Definition FFUINV (E : ffuenv) (mm : mem) : Prop :=
  (exists v, rw_cells usegs mm (f_SP E + -112) (C8 v :: ffu_saved E)) /\
  bytes_at usegs mm (f_A E) (f_txt E) /\
  mem_inv usegs mm /\ munch [(f_SP E - FFU_STACK, f_SP E)]%Z (f_m0 E) mm /\ wmono usegs (f_m0 E) mm /\ stk usegs mm (f_lo E) (f_SP E + -112).

Ltac ffu_open H :=
  let v := fresh "v" in
  destruct H as ((v & FR) & TXT & MI & MU & WM & ST);
  unfold ffu_saved in FR; unfold FFU_STACK, SPATHU_STACK, NDCU_STACK, P5U_STACK, LMU_STACK, LAFU_STACK in MU;
  let TXB := fresh "TXB" in pose proof (bytes_at_bound _ _ _ _ TXT) as TXB.
Ltac ffu_close :=
  lazymatch goal with
  | |- FFUINV _ _ =>
      split; [eexists; eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; eassumption
  end.
Ltac ffu_env OK :=
  let ROOM := fresh "ROOM" in let GTOP := fresh "GTOP" in let SP16 := fresh "SP16" in let TLO := fresh "TLO" in let TMAX := fresh "TMAX" in
  let A0 := fresh "A0" in let HFIRST := fresh "HFIRST" in let HLAST := fresh "HLAST" in
  destruct OK as [ROOM GTOP SP16 TLO TMAX A0 HFIRST HLAST];
  unfold FFU_STACK, SPATHU_STACK, NDCU_STACK, P5U_STACK, LMU_STACK, LAFU_STACK, NUMU_GTOP, NUM_TXT_MAX in *;
  lazymatch goal with E : ffuenv |- _ =>
    let SPR := fresh "SPR" in pose proof (bv_unsigned_in_range 64 (f_sp E)) as SPR; unfold bv_modulus in SPR; cbn in SPR end.

Notation FFS E pc xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm :=
  (MS (mkR xra (Z_to_bv 64 (f_SP E + -112)) (f_gp E) (f_tp E) xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
           xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6) xF (Z_to_bv 64 pc) xfc None mm (seg_rom usegs)).

Section FFUDEFS.
  Hypothesis HSPATH : ffu_spath_stmt.
  Variable E : ffuenv.
  Hypothesis OK : ffu_ok E.

  Lemma ffu_exit : forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    FFUINV E mm -> frm0 xfc ->
    evt usegs (ffu_post E) (FFS E 0x415c0 xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK.
    intros until mm. intros INV FRM. ffu_open INV. ffu_env OK.
    do 13 zstep. zstep. zstep.
    release_frame FR ST (f_SP E).
    apply evt_done. unfold ffu_post_g. do 17 eexists. exists mm.
    split; [cbv delta [mkR]; reflexivity|].
    unfold FFU_STACK, SPATHU_STACK, NDCU_STACK, P5U_STACK, LMU_STACK, LAFU_STACK.
    split; [exact FRM|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
  Qed.

  Lemma ffu_864 : forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    FFUINV E mm -> frm0 xfc ->
    evt usegs (ffu_post E) (FFS E 0x415b0 xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK.
    intros until mm. intros INV FRM. pose proof INV as INV0. ffu_open INV0. ffu_env OK.
    assert (D0 : IsData xt0) by exact I.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x415c0%Z => first [ eapply ffu_exit; [exact INV | assumption] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma ffu_870 : forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    FFUINV E mm -> frm0 xfc ->
    evt usegs (ffu_post E) (FFS E 0x415bc xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK.
    intros until mm. intros INV FRM. pose proof INV as INV0. ffu_open INV0. ffu_env OK.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x415c0%Z => first [ eapply ffu_exit; [exact INV | assumption] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma ffu_97c : forall xra xt0 xt1 xt2 xs0 xs1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    FFUINV E mm -> frm0 xfc -> (f_FIRST E < f_LAST E)%Z ->
    evt usegs (ffu_post E) (FFS E 0x416c8 xra xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 (f_FIRST E)) (Z_to_bv 64 (f_LAST E)) xa2 xa3 xa4 xa5 xa6 xa7
                               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using HSPATH OK.
    intros until mm. intros INV FRM HLT. ffu_open INV. ffu_env OK.
    assert (LO0 : (0 <= f_lo E)%Z) by (destruct ST as [? _]; assumption).
    uwalk ltac:(fun pc => lazymatch pc with | 0x5b558%Z => idtac end).
    change (C8 v :: [C8 (f_s11 E); C8 (f_s10 E); C8 (f_s9 E); C8 (f_s8 E); C8 (f_s7 E); C8 (f_s6 E); C8 (f_s5 E); C8 (f_s4 E); C8 (f_s3 E); C8 (f_s2 E); C8 (f_s1 E); C8 (f_s0 E); C8 (f_ra E)])
      with ([C8 v] ++ ffu_saved E) in FR.
    apply num_rw_cells_app in FR. destruct FR as [VAL SAVED].
    cbn [cells_size csize Nat.add] in SAVED.
    replace (f_SP E + -112 + Z.of_nat 8)%Z with (f_SP E + -104)%Z in * by lia.
    pose proof HSPATH as HS. unfold ffu_spath_stmt, spathu_stmt_g in HS.
    eapply evt_cut.
    { eapply evt_eq; [| eapply HS with (A := f_A E) (FIRST := f_FIRST E) (LAST := f_LAST E) (OUT := (f_SP E + -112)%Z) (lo := f_lo E) (txt := f_txt E) (v0 := v)];
        [ unfold SPATH_A4; num_st_eq | .. ]; rewrite ?unsigned_lit by lia; unfold SPATHU_STACK, NDCU_STACK, P5U_STACK, LMU_STACK, LAFU_STACK, NUMU_GTOP, NUM_TXT_MAX;
        [ exact MI | exact FRM | exact ST | lia | lia | Z.div_mod_to_equations; lia | exact TXT | lia | lia | lia | lia | lia | exact VAL | lia | Z.div_mod_to_equations; lia ]. }
    cbv beta. intros ms' P. unfold spathu_post_g in P.
    destruct P as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F3 & fc3 & m3 & v3 & -> & FRM3 & MUc & WMc & MI3 & VAL3 & ST3).
    rewrite !unsigned_lit in MUc, ST3 by lia. unfold SPATHU_STACK, NDCU_STACK, P5U_STACK, LMU_STACK, LAFU_STACK in MUc.
    clear VAL ST.
    lazymatch type of MUc with munch _ ?mo ?mn => transport_after_call usegs mo mn MUc WMc end.
    clear MUc WMc MI HS.
    num_ret_pc.
    assert (FR : rw_cells usegs m3 (f_SP E + -112) (C8 v3 :: ffu_saved E)).
    { change (C8 v3 :: ffu_saved E) with ([C8 v3] ++ ffu_saved E).
      apply num_rw_cells_app. split; [exact VAL3|]. cbn [cells_size csize Nat.add].
      replace (f_SP E + -112 + Z.of_nat 8)%Z with (f_SP E + -104)%Z by lia. exact SAVED. }
    clear VAL3 SAVED. rename ST3 into ST. rename MI3 into MI.
    assert (INV : FFUINV E m3) by ffu_close.
    lazymatch goal with |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ ?ra1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => assert (DA1 : IsData ra1) by exact I end.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x415b0%Z => first [ eapply ffu_864; [exact INV | assumption] | fail 100 "cut" pc ]
      end).
  Qed.
End FFUDEFS.
