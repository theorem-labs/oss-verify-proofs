(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require Import State.
From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From LinuxProcessSemantics.Riscv Require Import Instr.
From LinuxProcessSemantics.Riscv Require Import Decode.
From LinuxProcessSemantics.Riscv Require Import DecodeC.
From LinuxProcessSemantics.Riscv Require Import Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import PropExec.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import CatExec.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import CatSim.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import SeqExec.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import StoreOk.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import Hoare.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import SymEx2.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import SymEx2Tac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import MemRel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import SymAux.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import Prog.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import ZIface.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateState.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateArms.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import Inflate.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateInv.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U Require Import Segs6u.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S Require Import ISLayout.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import IS6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S Require Import InflMem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import InflRod6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import InflCtx6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import InflArmLib6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateInvKit.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateInvRun.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import InflNeed6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateGarbBase.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateInvTab.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import InflDec6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import InflArmLib6b.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require InflA_ClS.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import InflA_Dist3.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InftreesCoverage.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U Require Import Callee6u.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import InflA_Match2.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import InflA_Len3.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import InflA_Len7.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import InffastCtx IfSpec IfSpec6 InflA_LenF.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import Callee6i.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import InflMem2.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import InflA_ClS InflA_Cl1.

Module InflA_Codelens4.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateGarbBase.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvTab.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.CatExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.CatSim.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.SeqExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.StoreOk.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Hoare.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.StepTac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymEx2Expr.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymEx2.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymEx2Tac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.MemRel.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymAux.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.RomRead.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.Prog.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.ZIface.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateState.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateFast.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateArms.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.Inflate.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvKit.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvRun.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U.Segs6u.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S.ISLayout.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.IS6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S.InflMem.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflRod6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflCtx6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflArmLib6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflArmLib6b.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflNeed6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflDec6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflA_Dist3.
Import InflArmLib6e.
Import InflA_ClS.InflA_CodelensS.
Import InflA_Codelens2.
Import InflA_Codelens3.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache.
Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.
Lemma cent_split : forall e, cent e = code_op e + 2 ^ 8 * code_bits e + 2 ^ 16 * code_val e.
Proof.
  intros e. pose proof (cent_shr8 e) as A. pose proof (cent_op e) as B.
  pose proof (Z.div_mod (cent e) (2 ^ 8) ltac:(lia)) as D. rewrite A, B in D. lia.
Qed.
Lemma cent_shr20 : forall e, cent e / 2 ^ 20 = code_val e / 16.
Proof.
  intros e. rewrite cent_split. pose proof (code_op_range e). pose proof (code_bits_range e). pose proof (code_val_range e).
  pose proof (Z.div_mod (code_val e) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (code_val e) 16 ltac:(lia)).
  symmetry. apply (Z.div_unique_pos _ _ (code_val e / 16) (code_op e + 2 ^ 8 * code_bits e + 2 ^ 16 * (code_val e mod 16))); cbn in *; lia.
Qed.
Lemma cent_shl48_shr56 : forall e, (cent e * 2 ^ 48) mod 2 ^ 64 / 2 ^ 56 = code_bits e.
Proof.
  intros e. rewrite cent_split. pose proof (code_op_range e). pose proof (code_bits_range e). pose proof (code_val_range e).
  replace ((code_op e + 2 ^ 8 * code_bits e + 2 ^ 16 * code_val e) * 2 ^ 48) with ((code_op e * 2 ^ 48 + code_bits e * 2 ^ 56) + code_val e * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia. rewrite Z.mod_small by (cbn in *; lia).
  symmetry. apply (Z.div_unique_pos _ _ (code_bits e) (code_op e * 2 ^ 48)); cbn in *; lia.
Qed.

Lemma cent_mod16_shr8 : forall e, cent e mod 2 ^ 16 / 2 ^ 8 = code_bits e.
Proof.
  intros e. rewrite cent_split. pose proof (code_op_range e). pose proof (code_bits_range e). pose proof (code_val_range e).
  replace (code_op e + 2 ^ 8 * code_bits e + 2 ^ 16 * code_val e) with ((code_op e + 2 ^ 8 * code_bits e) + code_val e * 2 ^ 16) by lia.
  rewrite Z.mod_add by lia. rewrite Z.mod_small by (cbn in *; lia).
  symmetry. apply (Z.div_unique_pos _ _ (code_bits e) (code_op e)); cbn in *; lia.
Qed.

Definition ilCV : cfg := ilSx [0x1fa50; 0x1fa68; 0x1fac0; 0x1fb18; 0x1fb6c; 0x1fba0; 0x1fc04; 0x1f8f0; 0x1fc88] [].

Section Split.
  Variable v : icv.
  Hypothesis C : ictx v.

  Definition JREG (s : inflate_state) (r : iregs) (here : Z) (R : bvmap 5 word) : Prop :=
    BKc v s r R /\ getr R 16 = zw (is_have s) /\ getr R 25 = zw (ir_hold r) /\ getr R 23 = zw (ir_have r) /\ getr R 6 = zw (ir_have r)
    /\ getr R 26 = zw (cv_I0 v + ir_next r) /\ getr R 28 = zw (cv_I0 v + ir_next r)
    /\ getr R 5 = zw (ir_bits r) /\ getr R 7 = zw (ir_bits r) /\ getr R 20 = zw (- ir_bits r)
    /\ getr R 24 = zw (cent here) /\ getr R 29 = zw (cent here / 2 ^ 8) /\ getr R 30 = zw (code_bits here) /\ getr R 21 = zw 1.
  Definition VREG (s : inflate_state) (r : iregs) (hb chi val : Z) (R : bvmap 5 word) : Prop :=
    BKc v s r R /\ getr R 16 = zw (is_have s) /\ getr R 25 = zw (ir_hold r) /\ getr R 23 = zw (ir_have r) /\ getr R 6 = zw (ir_have r)
    /\ getr R 26 = zw (cv_I0 v + ir_next r) /\ getr R 28 = zw (cv_I0 v + ir_next r)
    /\ getr R 5 = zw (ir_bits r) /\ getr R 19 = zw (ir_bits r) /\ getr R 7 = zw (ir_bits r)
    /\ getr R 30 = zw hb /\ getr R 29 = zw chi /\ getr R 17 = zw val /\ getr R 31 = zw 16 /\ getr R 21 = zw 1.

  Ltac open_jreg HJ :=
    destruct HJ as ((HF & G9 & G11 & G12 & G13 & G15 & G14) & G16 & G22 & G24 & G6 & G25 & G28 & G5 & G7 & G19 & G23 & G29 & G30 & G20); open_fixc HF;
    let XF := fresh in pose proof HF as XF; unfold LFIXc, INF_FRAME in XF; destruct XF as (P2 & P27 & P8 & _).
  Ltac open_vreg HJ :=
    destruct HJ as ((HF & G9 & G11 & G12 & G13 & G15 & G14) & G16 & G22 & G24 & G6 & G25 & G28 & G5 & G18 & G7 & G30 & G29 & G17 & G31 & G20); open_fixc HF;
    let XF := fresh in pose proof HF as XF; unfold LFIXc, INF_FRAME in XF; destruct XF as (P2 & P27 & P8 & _).

  Definition jpins : list (Z * expr) :=
    [(2, EVar 32%nat); (8, EVar 33%nat); (18, EVar 34%nat); (1, ELit 16209); (9, EAdd (EVar 37%nat) (EVar 38%nat));
     (16, EVar 45%nat); (11, EVar 46%nat); (12, EVar 47%nat); (13, EVar 48%nat); (15, EVar 49%nat); (14, EVar 50%nat);
     (25, EVar 40%nat); (23, EVar 36%nat); (6, EVar 36%nat); (26, EAdd (EVar 43%nat) (EVar 44%nat)); (28, EAdd (EVar 43%nat) (EVar 44%nat));
     (5, EVar 41%nat); (21, ELit 1)].
  Definition jvb : list (nat * Z) :=
    [(45%nat, 512); (46%nat, 512); (47%nat, 512); (48%nat, 16); (49%nat, 2 ^ 15); (50%nat, 2 ^ 63); (51%nat, 2 ^ 32); (52%nat, 2 ^ 24); (53%nat, 16); (54%nat, 65536)].

  Definition cb_facts (v : icv) (s : inflate_state) : Prop :=
    0 <= is_have s < is_nlen s + is_ndist s /\ 0 <= is_nlen s /\ 0 <= is_ndist s /\ is_nlen s + is_ndist s <= 320
    /\ arr_len (is_lens s) = 320 /\ 1 <= is_lenbits s <= 15 /\ is_lencode s = CDyn 0
    /\ (forall i, 0 <= i < 320 -> 0 <= arr_get (is_lens s) i < 65536).

  Lemma cl_lit : forall s c r R M here,
    is_mode s = CODELENS -> cb_facts v s -> RINV (cv_NI v) (cv_NO v) r ->
    code_bits here <= ir_bits r -> code_bits here <= 15 -> code_val here < 16 ->
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LX v (mkW s c r) -> JREG s r here R ->
    exists R' M' pc',
      msteps s6u_segs (mkst R (Z_to_bv 64 0x1f9d8) M s6u_rom) (mkst R' (Z_to_bv 64 pc') M' s6u_rom)
      /\ body_post v (mkW s c r) M (ARun true (mkW (cb_lit_s s here) c (cdrop r (code_bits here)))) R' M' pc'.
  Proof.
    intros s c r R M here Hmode HB RI Hhb Hb15 Hval HM HRC HX HJ.
    destruct HB as (Hhv & Hnl & Hnd & Htot & Halen & Hlb & ELC & Blens). open_jreg HJ.
    pose proof G9 as P9. pose proof G22 as P22. pose proof G24 as P24.
    open_ictx C. open_lmem HM. open_retc HRC. open_lx HX. pose proof RI as RI0. open_rinv RI. open_frame Mfr. unfold mapped in *.
    pose proof (cell_nlens _ _ _ Fnlens) as Fnl. clear Fnlens.
    assert (NH : is_mode s <> HEAD) by (rewrite Hmode; cbv; discriminate).
    assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
    assert (Hput : 0 <= ir_put r <= cv_NO v) by (clear - Rpt0 Rpl Rlf0; lia).
    assert (HA : 0 < ctab6 v (is_lencode s) /\ ctab6 v (is_lencode s) + 4 * cext (is_lencode s) < 2 ^ 63 /\ cext (is_lencode s) = 1444) by (rewrite ELC; cbn [ctab6 codeptr_addr cext]; clear - CS; lia).
    destruct HA as (HA0 & HA1 & HX1444).
    pose proof (ones_range15 (is_lenbits s) Hlb) as Hones.
    pose proof (code_val_range here) as Hvr. pose proof (code_bits_range here) as Hcb. pose proof (cent_range here) as Hcent. pose proof (cent_shr8_range here) as Hc8.
    assert (E20 : cent here / 2 ^ 20 = 0) by (rewrite cent_shr20; apply Z.div_small; lia).
    pose proof (cent_shl48_shr56 here) as E56. pose proof (cent_mod16_shr8 here) as E56'. pose proof (cent_val here) as E16. pose proof (cent_bits6 here ltac:(lia)) as E6.
    pose proof (RINV_drop (cv_NI v) (cv_NO v) ltac:(clear - CI0; lia) ltac:(clear - CP0; lia) r (code_bits here) RI0 ltac:(clear - Hhb Hcb; lia)) as [EW RI'].
    set (r' := cdrop r (code_bits here)) in *.
    assert (Er' : r' = irset_bits (irset_hold r (Z.shiftr (ir_hold r) (code_bits here))) (ir_bits r - code_bits here)) by (subst r'; unfold cdrop; rewrite EW; reflexivity).
    set (s1 := iset_have s (is_have s + 1)). set (s2 := iset_lens s1 (arr_set (is_lens s1) (is_have s) (wrap16 (code_val here)))).
    assert (Es2 : cb_lit_s s here = s2) by (subst s2 s1; unfold cb_lit_s; rewrite wrap32_id by lia; destruct s; reflexivity).
    assert (POST : forall R1 (pc1 : Z) (MORE : (pc1 = 0x1f8f0 /\ is_have s + 1 < is_nlen s + is_ndist s) \/ (pc1 = 0x1fc88 /\ is_nlen s + is_ndist s <= is_have s + 1)),
      let M2 := wbytes (wbytes M (zw (cv_S v + 156)) (Z_to_le_bytes 4 (is_have s + 1))) (zw (cv_S v + is_have s * 2 ^ 1 + 168)) (Z_to_le_bytes 2 (code_val here)) in
      msteps s6u_segs (mkst R (Z_to_bv 64 0x1f9d8) M s6u_rom) (mkst R1 (Z_to_bv 64 pc1) M2 s6u_rom) ->
      (forall rg, reg_in rg [31; 17; 5; 6; 16; 25; 24; 7; 19; 28]%bv = false -> getr R1 rg = getr R rg) ->
      getr R1 16 = zw (is_have s + 1) -> getr R1 25 = zw (ir_hold r / 2 ^ code_bits here) -> getr R1 19 = zw (ir_bits r - code_bits here) ->
      getr R1 17 = zw (cv_I0 v + ir_next r) -> getr R1 31 = zw (ir_have r) ->
      exists R' M' pc',
        msteps s6u_segs (mkst R (Z_to_bv 64 0x1f9d8) M s6u_rom) (mkst R' (Z_to_bv 64 pc') M' s6u_rom)
        /\ body_post v (mkW s c r) M (ARun true (mkW (cb_lit_s s here) c (cdrop r (code_bits here)))) R' M' pc').
    { intros R1 pc1 MORE M2 Hms1 Hfr1 Q16 Q22 Q18 Q17 Q31.
      set (M1 := wbytes M (zw (cv_S v + 156)) (Z_to_le_bytes 4 (is_have s + 1))) in M2.
      assert (HM1 : LMEM v (mkW s1 c r) M1).
      { apply (LMEM_store_scalar v C s c r _ M 156 _ HM); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
        apply (is6_upd_have M (cv_S v) _ s _ Msc); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
      assert (HM2' : LMEM v (mkW s2 c r) M2).
      { subst M2 s2. replace (zw (cv_S v + is_have s * 2 ^ 1 + 168)) with (zw (cv_S v + 168 + 2 * is_have s)) by (f_equal; lia).
        apply (LMEM_store_lens v C s1 c r M1 (is_have s) (code_val here) (code_val here) HM1 Hput); [lia | subst s1; destruct s; exact Halen | apply le2_wrap16]. }
      assert (HM2 : LMEM v (mkW s2 c r') M2) by (apply (LMEM_regs v s2 c r c r' M2 HM2'); rewrite ?Er'; reflexivity).
      exists R1, M2, pc1. split; [exact Hms1|].
      change (cdrop r (code_bits here)) with r'. rewrite Es2. cbn [body_post w_s w_r w_c].
      split; [unfold foot_pc; subst s2 s1; destruct s; cbn in MORE |- *; destruct MORE as [[-> LT] | [-> GE]];
              [replace (_ <? _) with true by (symmetry; apply Z.ltb_lt; exact LT) | replace (_ <? _) with false by (symmetry; apply Z.ltb_ge; exact GE)]; reflexivity|].
      assert (HRC2 : RETC v (mkW s2 c r') M2).
      { subst M2 M1. apply (RETC_regs v (mkW s c r)); [| cbn [w_r]; rewrite Er'; reflexivity].
        apply (RETC_other v C); [| clear - CS Hhv; lia | clear - CS Hhv Htot; cbn; lia | unfold sep in CfS; clear - CfS CS Hhv Htot; cbn; lia].
        retc_tower C HRC. }
      assert (HX2 : LX v (mkW s2 c r')) by (apply (LX_step0 v s c r s2 c r' HX NH NB); subst s2 s1; rewrite ?Er'; try (destruct s; reflexivity); try reflexivity; [destruct s; cbn in Hmode |- *; rewrite Hmode; live_mode_tac | exact Xret | exact Xmsg | destruct s; cbn in Hmode |- *; bk_side]).
      split; [| split; [exact HM2 | split; [exact HRC2 | split; [exact HX2 | split; [subst s2 s1; destruct s; split; [reflexivity | split; reflexivity] |]]]]].
      + unfold WREG, BKc. rewrite Er'. subst s2 s1. cbn -[zw Z.add Z.mul Z.ones ctab6 getr cv_P0 cv_I0 cv_S cv_sp Z.sub Z.pow Z.opp Z.shiftr Z.div].
        repeat match goal with |- _ /\ _ => split end;
          first [ lazymatch goal with |- LFIXc _ _ => unfold LFIXc, INF_FRAME; repeat match goal with |- _ /\ _ => split end;
                      (lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr1 n eq_refl); assumption end) end
                | rewrite Q16; destruct s; reflexivity
                | rewrite Q22; rewrite Z.shiftr_div_pow2 by (clear - Hcb; lia); reflexivity
                | exact Q18 | exact Q17 | exact Q31
                | lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr1 n eq_refl); first [assumption | destruct s; assumption] end
                | match goal with |- ?G => idtac "WREGL LEFT" G end ].
      + rewrite Er'. cbn [ir_put irset_bits irset_hold]. subst M2 M1.
        apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r)); [| lia | clear - CS Hhv; lia | clear - CS Hhv Htot; cbn; lia | right; left; clear - Hhv Htot; cbn; lia].
        apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r) M M); [apply MFRAME_refl | lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia]. }
    destruct (Z_lt_le_dec (is_have s + 1) (is_nlen s + is_ndist s)) as [MORE|DONE].
    - arm_symexP (@nil (Z * expr)) ilCV 26%nat [false; true; true; true; true]
        [RVal (ESub (ELit 18446744073709551447) (EVar 33%nat)); RVal (EAdd (EVar 33%nat) (ELit 168))]
        (jpins ++ [(7, EVar 41%nat); (20, ESub (ELit 0) (EVar 41%nat)); (24, EVar 51%nat); (29, EVar 52%nat); (30, EVar 53%nat)]) jvb v r
        [is_have s; is_nlen s + is_ndist s; is_nlen s; is_lenbits s; Z.ones (is_lenbits s); ctab6 v (is_lencode s); cent here; cent here / 2 ^ 8; code_bits here] NoVals F0
        (mkst R (Z_to_bv 64 0x1f9d8) M s6u_rom) R1 HR1 Hfr1 Hms1.
      all: rewrite ?E20, ?E56, ?E56', ?E16, ?E6.
      all: try arm_side.
      all: match goal with |- ?G => idtac "LEFTLIT1" G end.
      rewrite ?E56, ?E56', ?E16, ?E6 in Hms1. rewrite ?(szwrap32_small (is_have s + 1)) in Hms1 by lia.
      symex_reg HR1 (16%bv : reg) as Q16. symex_reg HR1 (25%bv : reg) as Q22. symex_reg HR1 (19%bv : reg) as Q18. symex_reg HR1 (17%bv : reg) as Q17. symex_reg HR1 (31%bv : reg) as Q31.
      rewrite ?E56, ?E6 in Q22. rewrite ?srl_cent in Q22 by (first [exact Rhold64 | lia]). rewrite ?zalu_srl_small in Q22 by (clear - Rhold64 Hhb Hcb Rbits; lia).
      rewrite ?E56, ?E56' in Q18. rewrite ?szwrap32_small in Q18 by (clear - Hhb Hcb Rbits; lia). rewrite ?szwrap32_small in Q16 by lia.
      apply (POST R1 0x1f8f0 (or_introl (conj eq_refl MORE))); [by_run Hms1 | fr_weak Hfr1 | rewrite Q16; f_equal; lia | rewrite Q22; f_equal; lia | rewrite Q18; f_equal; lia | exact Q17 | exact Q31].
    - arm_symexP (@nil (Z * expr)) ilCV 26%nat [false; true; true; true; false]
        [RVal (ESub (ELit 18446744073709551447) (EVar 33%nat)); RVal (EAdd (EVar 33%nat) (ELit 168))]
        (jpins ++ [(7, EVar 41%nat); (20, ESub (ELit 0) (EVar 41%nat)); (24, EVar 51%nat); (29, EVar 52%nat); (30, EVar 53%nat)]) jvb v r
        [is_have s; is_nlen s + is_ndist s; is_nlen s; is_lenbits s; Z.ones (is_lenbits s); ctab6 v (is_lencode s); cent here; cent here / 2 ^ 8; code_bits here] NoVals F0
        (mkst R (Z_to_bv 64 0x1f9d8) M s6u_rom) R1 HR1 Hfr1 Hms1.
      all: rewrite ?E20, ?E56, ?E56', ?E16, ?E6.
      all: try arm_side.
      all: match goal with |- ?G => idtac "LEFTLIT2" G end.
      rewrite ?E56, ?E56', ?E16, ?E6 in Hms1. rewrite ?(szwrap32_small (is_have s + 1)) in Hms1 by lia.
      symex_reg HR1 (16%bv : reg) as Q16. symex_reg HR1 (25%bv : reg) as Q22. symex_reg HR1 (19%bv : reg) as Q18. symex_reg HR1 (17%bv : reg) as Q17. symex_reg HR1 (31%bv : reg) as Q31.
      rewrite ?E56, ?E6 in Q22. rewrite ?srl_cent in Q22 by (first [exact Rhold64 | lia]). rewrite ?zalu_srl_small in Q22 by (clear - Rhold64 Hhb Hcb Rbits; lia).
      rewrite ?E56, ?E56' in Q18. rewrite ?szwrap32_small in Q18 by (clear - Hhb Hcb Rbits; lia). rewrite ?szwrap32_small in Q16 by lia.
      apply (POST R1 0x1fc88 (or_intror (conj eq_refl DONE))); [by_run Hms1 | fr_weak Hfr1 | rewrite Q16; f_equal; lia | rewrite Q22; f_equal; lia | rewrite Q18; f_equal; lia | exact Q17 | exact Q31].
  Qed.

  Lemma cl_rep_pre : forall s c r R M here,
    cb_facts v s -> RINV (cv_NI v) (cv_NO v) r -> code_bits here <= 15 -> 16 <= code_val here ->
    LMEM v (mkW s c r) M -> JREG s r here R ->
    exists R1,
      msteps s6u_segs (mkst R (Z_to_bv 64 0x1f9d8) M s6u_rom) (mkst R1 (Z_to_bv 64 0x1fa50) M s6u_rom)
      /\ VREG s r (code_bits here) (cent here / 2 ^ 8) (code_val here) R1.
  Proof.
    intros s c r R M here HB RI Hb15 Hval HM HJ.
    destruct HB as (Hhv & Hnl & Hnd & Htot & Halen & Hlb & ELC & Blens). open_jreg HJ.
    pose proof G9 as P9. pose proof G22 as P22. pose proof G24 as P24.
    open_ictx C. open_lmem HM. open_rinv RI. unfold mapped in *.
    assert (HA : 0 < ctab6 v (is_lencode s) /\ ctab6 v (is_lencode s) + 4 * cext (is_lencode s) < 2 ^ 63 /\ cext (is_lencode s) = 1444) by (rewrite ELC; cbn [ctab6 codeptr_addr cext]; clear - CS; lia).
    destruct HA as (HA0 & HA1 & HX1444).
    pose proof (ones_range15 (is_lenbits s) Hlb) as Hones.
    pose proof (code_val_range here) as Hvr. pose proof (code_bits_range here) as Hcb. pose proof (cent_range here) as Hcent. pose proof (cent_shr8_range here) as Hc8.
    assert (E20 : 1 <= cent here / 2 ^ 20) by (rewrite cent_shr20; apply Z.div_le_lower_bound; lia).
    pose proof (cent_val here) as E16.
    arm_symexP (@nil (Z * expr)) ilCV 7%nat [true] (@nil (option expr))
      (jpins ++ [(7, EVar 41%nat); (20, ESub (ELit 0) (EVar 41%nat)); (24, EVar 51%nat); (29, EVar 52%nat); (30, EVar 53%nat)]) jvb v r
      [is_have s; is_nlen s + is_ndist s; is_nlen s; is_lenbits s; Z.ones (is_lenbits s); ctab6 v (is_lencode s); cent here; cent here / 2 ^ 8; code_bits here] NoVals F0
      (mkst R (Z_to_bv 64 0x1f9d8) M s6u_rom) R1 HR1 Hfr1 Hms1.
    all: rewrite ?E16.
    all: try arm_side.
    all: match goal with |- ?G => idtac "LEFTP" G end.
    exists R1. split; [by_run Hms1|].
    symex_reg HR1 (17%bv : reg) as Q17. rewrite ?E16 in Q17. symex_reg HR1 (19%bv : reg) as Q18. rewrite ?szwrap32_small in Q18 by (clear - Rbits; lia). symex_reg HR1 (31%bv : reg) as Q31.
    unfold VREG, BKc. repeat match goal with |- _ /\ _ => split end;
      first [ lazymatch goal with |- LFIXc _ _ => lfixc_close Hfr1 HR1 end
            | exact Q17 | exact Q31 | rewrite Q18; f_equal; lia
            | lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr1 n eq_refl); assumption end
            | match goal with |- ?G => idtac "VREG LEFT" G end ].
  Qed.

  Ltac split_close HR Hfr :=
    unfold NJS, NJE, NK; repeat match goal with |- _ /\ _ => split end;
    first [ lazymatch goal with |- LFIXc _ _ => lfixc_close Hfr HR end
          | lazymatch goal with |- getr _ ?n = _ => first [ rewrite (Hfr n eq_refl); assumption
                                                          | let Q := fresh in symex_reg HR (n : reg) as Q; rewrite Q; first [reflexivity | f_equal; lia] ] end
          | lia
          | match goal with |- ?G => idtac "SPLIT LEFT" G end ].

  Definition vpins : list (Z * expr) := jpins ++ [(19, EVar 41%nat); (7, EVar 41%nat); (30, EVar 53%nat); (29, EVar 52%nat); (17, EVar 54%nat); (31, ELit 16)].

  Lemma cl_split16 : forall s c r R M hb chi,
    cb_facts v s -> RINV (cv_NI v) (cv_NO v) r -> 0 <= hb <= 15 -> 0 <= chi < 2 ^ 24 -> VREG s r hb chi 16 R ->
    exists R1,
      if hb + 2 <=? ir_bits r
      then msteps s6u_segs (mkst R (Z_to_bv 64 0x1fa50) M s6u_rom) (mkst R1 (Z_to_bv 64 0x1fba0) M s6u_rom) /\ NJE v s (hb + 2) hb chi (ir_have r) (ir_next r) c r R1
      else msteps s6u_segs (mkst R (Z_to_bv 64 0x1fa50) M s6u_rom) (mkst R1 (Z_to_bv 64 0x1fac0) M s6u_rom) /\ NJS v s (hb + 2) hb chi (ir_have r) (ir_next r) c r R1.
  Proof.
    intros s c r R M hb chi HB RI Hhb Hchi HV. destruct HB as (Hhv & Hnl & Hnd & Htot & Halen & Hlb & ELC & Blens). open_vreg HV.
    pose proof G9 as P9. pose proof G22 as P22. pose proof G24 as P24.
    open_ictx C. open_rinv RI.
    assert (HA : 0 < ctab6 v (is_lencode s) /\ ctab6 v (is_lencode s) + 4 < 2 ^ 63) by (rewrite ELC; cbn [ctab6 codeptr_addr]; clear - CS; lia). destruct HA as [HA0 HA1].
    pose proof (ones_range15 (is_lenbits s) Hlb) as Hones.
    destruct (Z.leb_spec (hb + 2) (ir_bits r)) as [LE|GT].
    - arm_symexP (@nil (Z * expr)) ilCV 8%nat [true; true] (@nil (option expr)) vpins jvb v r
        [is_have s; is_nlen s + is_ndist s; is_nlen s; is_lenbits s; Z.ones (is_lenbits s); ctab6 v (is_lencode s); 0; chi; hb; 16] NoVals F0
        (mkst R (Z_to_bv 64 0x1fa50) M s6u_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      exists R1. split; [by_run Hms1|]. split_close HR1 Hfr1.
    - arm_symexP (@nil (Z * expr)) ilCV 8%nat [true; false] (@nil (option expr)) vpins jvb v r
        [is_have s; is_nlen s + is_ndist s; is_nlen s; is_lenbits s; Z.ones (is_lenbits s); ctab6 v (is_lencode s); 0; chi; hb; 16] NoVals F0
        (mkst R (Z_to_bv 64 0x1fa50) M s6u_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      exists R1. split; [by_run Hms1|]. split_close HR1 Hfr1.
  Qed.

  Lemma cl_split17 : forall s c r R M hb chi,
    cb_facts v s -> RINV (cv_NI v) (cv_NO v) r -> 0 <= hb <= 15 -> 0 <= chi < 2 ^ 24 -> VREG s r hb chi 17 R ->
    exists R1,
      if hb + 3 <=? ir_bits r
      then msteps s6u_segs (mkst R (Z_to_bv 64 0x1fa50) M s6u_rom) (mkst R1 (Z_to_bv 64 0x1fb6c) M s6u_rom) /\ NJE v s (hb + 3) hb chi (ir_have r) (ir_next r) c r R1
      else msteps s6u_segs (mkst R (Z_to_bv 64 0x1fa50) M s6u_rom) (mkst R1 (Z_to_bv 64 0x1fa68) M s6u_rom) /\ NJS v s (hb + 3) hb chi (ir_have r) (ir_next r) c r R1.
  Proof.
    intros s c r R M hb chi HB RI Hhb Hchi HV. destruct HB as (Hhv & Hnl & Hnd & Htot & Halen & Hlb & ELC & Blens). open_vreg HV.
    pose proof G9 as P9. pose proof G22 as P22. pose proof G24 as P24.
    open_ictx C. open_rinv RI.
    assert (HA : 0 < ctab6 v (is_lencode s) /\ ctab6 v (is_lencode s) + 4 < 2 ^ 63) by (rewrite ELC; cbn [ctab6 codeptr_addr]; clear - CS; lia). destruct HA as [HA0 HA1].
    pose proof (ones_range15 (is_lenbits s) Hlb) as Hones.
    destruct (Z.leb_spec (hb + 3) (ir_bits r)) as [LE|GT].
    - arm_symexP (@nil (Z * expr)) ilCV 10%nat [false; false; true] (@nil (option expr)) vpins jvb v r
        [is_have s; is_nlen s + is_ndist s; is_nlen s; is_lenbits s; Z.ones (is_lenbits s); ctab6 v (is_lencode s); 0; chi; hb; 17] NoVals F0
        (mkst R (Z_to_bv 64 0x1fa50) M s6u_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      exists R1. split; [by_run Hms1|]. split_close HR1 Hfr1.
    - arm_symexP (@nil (Z * expr)) ilCV 10%nat [false; false; false] (@nil (option expr)) vpins jvb v r
        [is_have s; is_nlen s + is_ndist s; is_nlen s; is_lenbits s; Z.ones (is_lenbits s); ctab6 v (is_lencode s); 0; chi; hb; 17] NoVals F0
        (mkst R (Z_to_bv 64 0x1fa50) M s6u_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      exists R1. split; [by_run Hms1|]. split_close HR1 Hfr1.
  Qed.

  Lemma cl_split18 : forall s c r R M hb chi val,
    cb_facts v s -> RINV (cv_NI v) (cv_NO v) r -> 0 <= hb <= 15 -> 0 <= chi < 2 ^ 24 -> 16 <= val < 65536 -> val <> 16 -> val <> 17 -> VREG s r hb chi val R ->
    exists R1,
      if hb + 7 <=? ir_bits r
      then msteps s6u_segs (mkst R (Z_to_bv 64 0x1fa50) M s6u_rom) (mkst R1 (Z_to_bv 64 0x1fc04) M s6u_rom) /\ NJE v s (hb + 7) hb chi (ir_have r) (ir_next r) c r R1
      else msteps s6u_segs (mkst R (Z_to_bv 64 0x1fa50) M s6u_rom) (mkst R1 (Z_to_bv 64 0x1fb18) M s6u_rom) /\ NJS v s (hb + 7) hb chi (ir_have r) (ir_next r) c r R1.
  Proof.
    intros s c r R M hb chi val HB RI Hhb Hchi Hval N16 N17 HV. destruct HB as (Hhv & Hnl & Hnd & Htot & Halen & Hlb & ELC & Blens). open_vreg HV.
    pose proof G9 as P9. pose proof G22 as P22. pose proof G24 as P24.
    open_ictx C. open_rinv RI.
    assert (HA : 0 < ctab6 v (is_lencode s) /\ ctab6 v (is_lencode s) + 4 < 2 ^ 63) by (rewrite ELC; cbn [ctab6 codeptr_addr]; clear - CS; lia). destruct HA as [HA0 HA1].
    pose proof (ones_range15 (is_lenbits s) Hlb) as Hones.
    destruct (Z.leb_spec (hb + 7) (ir_bits r)) as [LE|GT].
    - arm_symexP (@nil (Z * expr)) ilCV 10%nat [false; true; true] (@nil (option expr)) vpins jvb v r
        [is_have s; is_nlen s + is_ndist s; is_nlen s; is_lenbits s; Z.ones (is_lenbits s); ctab6 v (is_lencode s); 0; chi; hb; val] NoVals F0
        (mkst R (Z_to_bv 64 0x1fa50) M s6u_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      exists R1. split; [by_run Hms1|]. split_close HR1 Hfr1.
    - arm_symexP (@nil (Z * expr)) ilCV 10%nat [false; true; false] (@nil (option expr)) vpins jvb v r
        [is_have s; is_nlen s + is_ndist s; is_nlen s; is_lenbits s; Z.ones (is_lenbits s); ctab6 v (is_lencode s); 0; chi; hb; val] NoVals F0
        (mkst R (Z_to_bv 64 0x1fa50) M s6u_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      exists R1. split; [by_run Hms1|]. split_close HR1 Hfr1.
  Qed.
End Split.
End FXG.
End InflA_Codelens4.
Export InflA_Codelens4.

Module InflA_Codelens4b.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateGarbBase.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvTab.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.CatExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.CatSim.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.SeqExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.StoreOk.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Hoare.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.StepTac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymEx2Expr.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymEx2.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymEx2Tac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.MemRel.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymAux.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.RomRead.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.Prog.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.ZIface.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateState.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateFast.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateArms.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.Inflate.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvKit.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvRun.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U.Segs6u.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S.ISLayout.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.IS6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S.InflMem.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflRod6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflCtx6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflArmLib6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflArmLib6b.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflNeed6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflDec6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflA_Dist3.
Import InflArmLib6e.
Import InflA_ClS.InflA_CodelensS.
Import InflA_Codelens2.
Import InflA_Codelens3.
Import InflA_Codelens4.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache.
Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.
Definition ilCR : cfg := ilSx [0x1fc2c] [].

Lemma bits_after_drop : forall h hb k, 0 <= h -> 0 <= hb -> 0 <= k <= 32 ->
  (h / 2 ^ hb) mod 2 ^ k = BITSv (Z.shiftr h hb) k.
Proof. intros h hb k Hh Hhb Hk. rewrite BITSv_land, Z.land_ones, Z.shiftr_div_pow2 by (try apply Z.shiftr_nonneg; lia). reflexivity. Qed.
Lemma drop_drop : forall h hb k, 0 <= hb -> 0 <= k -> h / 2 ^ hb / 2 ^ k = Z.shiftr (Z.shiftr h hb) k.
Proof. intros. rewrite !Z.shiftr_div_pow2 by (try apply Z.shiftr_nonneg; lia). reflexivity. Qed.

Section Reps.
  Variable v : icv.
  Hypothesis C : ictx v.

  Ltac open_nje HJ :=
    let X := fresh in pose proof HJ as X; unfold NJE, NK in X;
    destruct X as ((HF & G9 & G16 & G11 & G12 & G13 & G15 & G14 & G20 & G30 & G31 & G29 & G25 & G6) & G22 & G5 & G24 & G17); open_fixc HF;
    let XF := fresh in pose proof HF as XF; unfold LFIXc, INF_FRAME in XF; destruct XF as (P2 & P27 & P8 & _);
    pose proof G9 as P9; pose proof G22 as P22; pose proof G24 as P24.

  Definition epins : list (Z * expr) :=
    [(2, EVar 32%nat); (8, EVar 33%nat); (18, EVar 34%nat); (1, ELit 16209); (9, EAdd (EVar 37%nat) (EVar 38%nat));
     (16, EVar 45%nat); (11, EVar 46%nat); (12, EVar 47%nat); (13, EVar 48%nat); (15, EVar 49%nat); (14, EVar 50%nat); (21, ELit 1);
     (25, EVar 40%nat); (23, EVar 36%nat); (5, EVar 41%nat); (17, EAdd (EVar 43%nat) (EVar 44%nat));
     (31, EVar 51%nat); (29, EVar 52%nat); (30, EVar 53%nat)].
  Definition evb : list (nat * Z) :=
    [(45%nat, 512); (46%nat, 512); (47%nat, 512); (48%nat, 16); (49%nat, 2 ^ 15); (50%nat, 2 ^ 63); (51%nat, 64); (52%nat, 2 ^ 24); (53%nat, 16); (54%nat, 65536)].

  Ltac kreg_close HR Hfr Hchi6 chi :=
    unfold KREG, BKc; repeat match goal with |- _ /\ _ => split end;
    first [ lazymatch goal with |- LFIXc _ _ => lfixc_close Hfr HR end
          | lazymatch goal with |- getr _ ?n = _ => first [ rewrite (Hfr n eq_refl); assumption
                                                          | let Q := fresh in symex_reg HR (n : reg) as Q; rewrite Q;
                                                            try (lazymatch goal with |- context [zalu ALU_SRL ?h chi] => rewrite (zalu_srl_mod h chi), Hchi6 end);
                                                            rewrite ?zalu_srl_small by lia; rewrite ?szwrap32_small by lia;
                                                            rewrite ?wrap32_id by lia; rewrite ?bits_after_drop, ?drop_drop by lia;
                                                            first [reflexivity | f_equal; lia] ] end
          | match goal with |- ?G => idtac "KREG LEFT" G end ].

  Lemma cl_r17 : forall s c r R M hb chi h0 n0,
    cb_facts v s -> RINV (cv_NI v) (cv_NO v) r -> 0 <= hb <= 15 -> hb + 3 <= ir_bits r -> 0 <= chi < 2 ^ 24 -> chi mod 2 ^ 6 = hb ->
    NJE v s (hb + 3) hb chi h0 n0 c r R ->
    exists R1,
      msteps s6u_segs (mkst R (Z_to_bv 64 0x1fb6c) M s6u_rom) (mkst R1 (Z_to_bv 64 0x1fc2c) M s6u_rom)
      /\ KREG v s (cdrop (cdrop r hb) 3) 0 (3 + BITSv (ir_hold (cdrop r hb)) 3) R1.
  Proof.
    intros s c r R M hb chi h0 n0 HB RI Hhb Hn Hchi Hchi6 HJ. destruct HB as (Hhv & Hnl & Hnd & Htot & Halen & Hlb & ELC & Blens). open_nje HJ.
    open_ictx C. open_rinv RI.
    assert (HA : 0 < ctab6 v (is_lencode s) /\ ctab6 v (is_lencode s) + 4 < 2 ^ 63) by (rewrite ELC; cbn [ctab6 codeptr_addr]; clear - CS; lia). destruct HA as [HA0 HA1].
    pose proof (ones_range15 (is_lenbits s) Hlb) as Hones.
    arm_symexP (@nil (Z * expr)) ilCR 12%nat [true] (@nil (option expr)) epins evb v r
      [is_have s; is_nlen s + is_ndist s; is_nlen s; is_lenbits s; Z.ones (is_lenbits s); ctab6 v (is_lencode s); hb + 3; chi; hb] NoVals F0
      (mkst R (Z_to_bv 64 0x1fb6c) M s6u_rom) R1 HR1 Hfr1 Hms1.
    all: try arm_side.
    all: match goal with |- ?G => idtac "LEFTR17" G end.
    exists R1. split; [by_run Hms1|].
    unfold cdrop. cbn [ir_hold ir_bits ir_have ir_next ir_put ir_left ir_out irset_bits irset_hold].
    kreg_close HR1 Hfr1 Hchi6 chi.
  Qed.

  Lemma cl_r18 : forall s c r R M hb chi h0 n0,
    cb_facts v s -> RINV (cv_NI v) (cv_NO v) r -> 0 <= hb <= 15 -> hb + 7 <= ir_bits r -> 0 <= chi < 2 ^ 24 -> chi mod 2 ^ 6 = hb ->
    NJE v s (hb + 7) hb chi h0 n0 c r R ->
    exists R1,
      msteps s6u_segs (mkst R (Z_to_bv 64 0x1fc04) M s6u_rom) (mkst R1 (Z_to_bv 64 0x1fc2c) M s6u_rom)
      /\ KREG v s (cdrop (cdrop r hb) 7) 0 (11 + BITSv (ir_hold (cdrop r hb)) 7) R1.
  Proof.
    intros s c r R M hb chi h0 n0 HB RI Hhb Hn Hchi Hchi6 HJ. destruct HB as (Hhv & Hnl & Hnd & Htot & Halen & Hlb & ELC & Blens). open_nje HJ.
    open_ictx C. open_rinv RI.
    assert (HA : 0 < ctab6 v (is_lencode s) /\ ctab6 v (is_lencode s) + 4 < 2 ^ 63) by (rewrite ELC; cbn [ctab6 codeptr_addr]; clear - CS; lia). destruct HA as [HA0 HA1].
    pose proof (ones_range15 (is_lenbits s) Hlb) as Hones.
    arm_symexP (@nil (Z * expr)) ilCR 12%nat [true] (@nil (option expr)) epins evb v r
      [is_have s; is_nlen s + is_ndist s; is_nlen s; is_lenbits s; Z.ones (is_lenbits s); ctab6 v (is_lencode s); hb + 7; chi; hb] NoVals F0
      (mkst R (Z_to_bv 64 0x1fc04) M s6u_rom) R1 HR1 Hfr1 Hms1.
    all: try arm_side.
    all: match goal with |- ?G => idtac "LEFTR18" G end.
    exists R1. split; [by_run Hms1|].
    unfold cdrop. cbn [ir_hold ir_bits ir_have ir_next ir_put ir_left ir_out irset_bits irset_hold].
    kreg_close HR1 Hfr1 Hchi6 chi.
  Qed.

  Lemma cl_r16 : forall s c r R M hb chi h0 n0,
    is_mode s = CODELENS -> cb_facts v s -> RINV (cv_NI v) (cv_NO v) r -> 0 <= hb <= 15 -> hb + 2 <= ir_bits r -> 0 <= chi < 2 ^ 24 -> chi mod 2 ^ 6 = hb ->
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LX v (mkW s c r) -> NJE v s (hb + 2) hb chi h0 n0 c r R ->
    exists R1 M1 pc1,
      msteps s6u_segs (mkst R (Z_to_bv 64 0x1fba0) M s6u_rom) (mkst R1 (Z_to_bv 64 pc1) M1 s6u_rom)
      /\ if is_have s =? 0
         then body_post v (mkW s c r) M (ARun false (mkW (iset_mode s BAD) (icset_msg c MSG_invalid_bit_length_repeat) (cdrop r hb))) R1 M1 pc1
         else pc1 = 0x1fc2c /\ M1 = M
              /\ KREG v s (cdrop (cdrop r hb) 2) (arr_get (is_lens s) (is_have s - 1)) (3 + BITSv (ir_hold (cdrop r hb)) 2) R1.
  Proof.
    intros s c r R M hb chi h0 n0 Hmode HB RI Hhb Hn Hchi Hchi6 HM HRC HX HJ. destruct HB as (Hhv & Hnl & Hnd & Htot & Halen & Hlb & ELC & Blens). open_nje HJ.
    open_ictx C. open_lmem HM. open_retc HRC. open_lx HX. pose proof RI as RI0. open_rinv RI. open_frame Mfr. unfold mapped in *.
    pose proof (cell_nlens _ _ _ Fnlens) as Fnl. clear Fnlens.
    assert (NH : is_mode s <> HEAD) by (rewrite Hmode; cbv; discriminate).
    assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
    assert (Hput : 0 <= ir_put r <= cv_NO v) by (clear - Rpt0 Rpl Rlf0; lia).
    assert (HA : 0 < ctab6 v (is_lencode s) /\ ctab6 v (is_lencode s) + 4 < 2 ^ 63) by (rewrite ELC; cbn [ctab6 codeptr_addr]; clear - CS; lia). destruct HA as [HA0 HA1].
    pose proof (ones_range15 (is_lenbits s) Hlb) as Hones.
    pose proof (RINV_drop (cv_NI v) (cv_NO v) ltac:(clear - CI0; lia) ltac:(clear - CP0; lia) r hb RI0 ltac:(clear - Hhb Hn; lia)) as [EW RI'].
    destruct (Z.eqb_spec (is_have s) 0) as [H0|H0].
    -
      arm_symexP (@nil (Z * expr)) ilCR 18%nat [true; false] [RVal (EVar 35%nat)] epins evb v r
        [is_have s; is_nlen s + is_ndist s; is_nlen s; is_lenbits s; Z.ones (is_lenbits s); ctab6 v (is_lencode s); hb + 2; chi; hb] NoVals F0
        (mkst R (Z_to_bv 64 0x1fba0) M s6u_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      all: match goal with |- ?G => idtac "LEFTR16a" G end.
      set (c' := icset_msg c MSG_invalid_bit_length_repeat) in *. set (r' := cdrop r hb) in *.
      set (M1 := wbytes M (zw (cv_ZP v + 48)) (Z_to_le_bytes 8 66234)) in *.
      set (M2 := wbytes M1 (zw (cv_S v + 8)) (Z_to_le_bytes 4 16209)) in *.
      assert (Er' : r' = irset_bits (irset_hold r (Z.shiftr (ir_hold r) hb)) (ir_bits r - hb)) by (subst r'; unfold cdrop; rewrite EW; reflexivity).
      assert (Hput' : 0 <= ir_put r' <= cv_NO v) by (rewrite Er'; exact Hput).
      assert (HM0 : LMEM v (mkW s c r') M) by (apply (LMEM_regs v s c r c r' M HM); rewrite ?Er'; reflexivity).
      assert (HM1 : LMEM v (mkW s c' r') M1) by (exact (LMEM_store_msg v C s c r' M MSG_invalid_bit_length_repeat HM0 Hput')).
      set (s' := iset_mode s BAD) in *.
      assert (HM2 : LMEM v (mkW s' c' r') M2).
      { apply (LMEM_store_scalar v C s c' r' _ M1 8 _ HM1); [lia | cbn; lia | exact Hput' | | reflexivity | reflexivity | reflexivity | reflexivity].
        apply (is6_upd_mode M1 (cv_S v) _ s BAD (lm_sc _ _ _ HM1)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
      pose proof (icset_msg_facts c MSG_invalid_bit_length_repeat) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11).
      arm_disp C HM2 Hfr1 R2 Hms2 G26' Hfr2.
      exists R2, M2, (arm6_pc (is_mode s')). split; [eapply msteps_trans; [| exact Hms2]; subst M2 M1; by_run Hms1|].
      cbn [body_post arm_post]. split; [| subst s'; reflexivity]. split; [subst s'; reflexivity|]. split; [| split; [subst s'; apply same_blocks_mode |]].
      + split; [exact HM2|]. split; [subst M2 M1; apply (RETC_regs v (mkW s c r)); [retc_tower C HRC | cbn [w_r]; rewrite Er'; reflexivity]|]. split.
        * apply (LX_step0 v s c r s' c' r' HX NH NB); subst s' c'; rewrite ?Er'; try reflexivity; [live_mode_tac | exact Xret | rewrite K11; unfold MSG_invalid_bit_length_repeat; lia | bk_side].
        * symex_reg HR1 (26%bv : reg) as Q25. symex_reg HR1 (25%bv : reg) as Q22. symex_reg HR1 (19%bv : reg) as Q18.
          rewrite (zalu_srl_mod (ir_hold r) chi), Hchi6 in Q22. rewrite zalu_srl_small in Q22 by (clear - Rhold64 Hhb; lia). rewrite szwrap32_small in Q18 by (clear - Hhb Hn Rbits; lia).
          unfold LREG_arm. split; [lfix_close2 Hfr2 Hfr1 HR1|]. split; [| intros _; exact G26'].
          unfold LVARS; cbn [w_r]. rewrite Er'. cbn. rewrite Z.shiftr_div_pow2 by lia.
          regs_via2 Hfr2 Hfr1; first [exact Q25 | exact Q22 | rewrite Q18; f_equal; lia | match goal with |- ?G => idtac "R16 LV LEFT" G end].
      + cbn [w_r]. rewrite Er'. cbn [ir_put irset_bits irset_hold]. subst M2 M1.
        apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
        apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r) M M); [apply MFRAME_refl | lia | clear - CZP; lia | clear - CZP; cbn; lia | right; right; left; clear; cbn; lia].
    - pose proof (Mlens (is_have s - 1) ltac:(lia)) as Cprev. pose proof (Blens (is_have s - 1) ltac:(lia)) as Bprev.
      arm_symexP (@nil (Z * expr)) ilCR 22%nat [true; true; true; true] [RVal (ESub (ELit 18446744073709551447) (EVar 33%nat)); RVal (EAdd (EVar 33%nat) (ELit 168)); RVal (EVar 54%nat)] epins evb v r
        [is_have s; is_nlen s + is_ndist s; is_nlen s; is_lenbits s; Z.ones (is_lenbits s); ctab6 v (is_lencode s); hb + 2; chi; hb; arr_get (is_lens s) (is_have s - 1)] NoVals F0
        (mkst R (Z_to_bv 64 0x1fba0) M s6u_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      all: try (lazymatch goal with |- exists bs, rdn _ _ (zw ?a) 2%nat = Some bs /\ _ =>
                  replace a with (cv_S v + 168 + 2 * (is_have s - 1)) by (rewrite ?szwrap32_small by (clear - H0 Hhv Htot; lia); clear - H0 Hhv Htot; lia);
                  apply (cell_read_small s6u_segs M _ 2%nat _ Cprev); cbn; clear - Bprev; lia end).
      all: match goal with |- ?G => idtac "LEFTR16b" G end.
      exists R1, M, 0x1fc2c. split; [by_run Hms1|]. split; [reflexivity|]. split; [reflexivity|].
      unfold cdrop. cbn [ir_hold ir_bits ir_have ir_next ir_put ir_left ir_out irset_bits irset_hold].
      kreg_close HR1 Hfr1 Hchi6 chi.
  Qed.
End Reps.
End FXG.
End InflA_Codelens4b.
Export InflA_Codelens4b.

Module InflA_Codelens5.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateGarbBase.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvTab.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.CatExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.CatSim.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.SeqExec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.StoreOk.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Hoare.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.StepTac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymEx2Expr.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymEx2.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymEx2Tac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.MemRel.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymAux.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.RomRead.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.Prog.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.ZIface.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateState.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.Inftrees.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InftreesCoverage.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateFast.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateArms.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.Inflate.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvKit.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvRun.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U.Segs6u.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U.Callee6u.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S.ISLayout.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.IS6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S.InflMem.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflRod6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflCtx6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflArmLib6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflArmLib6b.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflNeed6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflA_Match2.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflDec6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflA_Len3.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflA_Len7.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.Callee6i.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflMem2.
Import InflA_ClS.InflA_CodelensS.
Import ListNotations.
Local Open Scope Z_scope.
#[local] Transparent bkv sbv.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache.
Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.
Definition ilCD : cfg := CFG [] [] arm_rets (pc6_disp :: arm_stops) [].

Section SegC.
  Variable v : icv.
  Hypothesis C : ictx v.
  Hypothesis IFAST : inflate_fast_spec6.
  Hypothesis FFOK : ffok_stmt.
  Hypothesis FASTOK : fastok_stmt.
  Hypothesis GFOB : gfast_ob_stmt.
  Hypothesis FFRAME : fframe_stmt.

  Definition CREG (s : inflate_state) (c : icall) (r : iregs) (ret : Z) (R : bvmap 5 word) : Prop :=
    getr R 2 = zw (cv_sp v - INF_FRAME) /\ getr R 8 = zw (cv_S v) /\ getr R 18 = zw (cv_ZP v)
    /\ getr R 3 = getr (cv_R0 v) 3 /\ getr R 4 = getr (cv_R0 v) 4
    /\ LVARK v (mkW s c r) R /\ getr R 10 = zw ret.

  Definition cpins : list (Z * expr) :=
    [(2, EVar 32%nat); (8, EVar 33%nat); (18, EVar 34%nat);
     (23, EVar 36%nat); (9, EAdd (EVar 37%nat) (EVar 38%nat)); (25, EVar 40%nat); (19, EVar 41%nat);
     (26, EAdd (EVar 43%nat) (EVar 44%nat)); (10, EVar 45%nat)].

  Lemma codelens_segC : forall s c r R M ret,
    is_mode s = CODELENS -> (ret = 0 -> len_facts v s c) -> RINV (cv_NI v) (cv_NO v) r -> (ret = 0 \/ ret = 1 \/ ret = -1) ->
    (ret = 0 -> pinv (cv_NI v) (cv_NO v) (cv_WN v) (cv_TOT0 v) (mkW (iset_mode s LEN_) c (irset_ret r 0))) ->
    LMEM v (mkW s c r) M -> LX v (mkW s c r) -> CREG s c r ret R ->
    exists R' M' pc',
      msteps s6u_segs (mkst R (Z_to_bv 64 0x1fff8) M s6u_rom) (mkst R' (Z_to_bv 64 pc') M' s6u_rom)
      /\ arm_post v (mkW s c r) M (cdC_res (cv_flush v) s c r ret) R' M' pc'.
  Proof.
    intros s c r R M ret Hmode HLF RI Hret HPL HM HX HR.
    destruct HR as (G2 & G27 & G8 & G3 & G4 & HV & G10). unfold INF_FRAME in G2.
    pose proof HV as X; unfold LVARK in X; cbn [w_r] in X; destruct X as (G24 & G9 & G22 & G18 & G25).
    pose proof G2 as P2. pose proof G27 as P27. pose proof G8 as P8. pose proof G24 as P24. pose proof G9 as P9. pose proof G22 as P22. pose proof G18 as P18. pose proof G25 as P25.
    open_ictx C. open_lmem HM. open_lx HX. pose proof RI as RI0. open_rinv RI. open_frame Mfr. unfold mapped in *.
    assert (NH : is_mode s <> HEAD) by (rewrite Hmode; cbv; discriminate).
    assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
    assert (Hput : 0 <= ir_put r <= cv_NO v) by (clear - Rpt0 Rpl Rlf0; lia).
    assert (Hrm : 0 <= ret mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
    rewrite <- (zw_mod ret) in G10.
    unfold cdC_res. replace (cv_flush v =? Z_TREES) with false by (symmetry; apply Z.eqb_neq; unfold Z_TREES; clear - Cflush; lia).
    destruct (Z.eq_dec ret 0) as [R0|R0].
    -
      subst ret. cbn [Z.eqb negb]. change (0 mod 2 ^ 64) with 0 in G10.
      arm_symexP (@nil (Z * expr)) ilS 14%nat [true; false]
        [RVal (ELit 16209); RVal (EVar 35%nat)]
        cpins [(45%nat, 1)] v r [0] NoVals F0
        (mkst R (Z_to_bv 64 0x1fff8) M s6u_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      all: match goal with |- ?G => idtac "LEFTC1" G end.
      set (M1 := wbytes M (zw (cv_sp v - 256 + 64)) (Z_to_le_bytes 8 0)) in *.
      set (M2 := wbytes M1 (zw (cv_sp v - 256 + 64)) (Z_to_le_bytes 8 0)) in *.
      set (M3 := wbytes M2 (zw (cv_S v + 8)) (Z_to_le_bytes 4 16199)) in *.
      set (r' := irset_ret r 0) in *. set (s' := iset_mode s LEN_) in *.
      assert (Hput' : 0 <= ir_put r' <= cv_NO v) by (subst r'; exact Hput).
      assert (HM0 : LMEM v (mkW s c r') M) by (apply (LMEM_regs v s c r c r' M HM); subst r'; reflexivity).
      assert (HM1 : LMEM v (mkW s c r') M1) by (apply (LMEM_store_fscratch v C s c r' M 64 _ HM0 Hput'); split; [left; reflexivity | reflexivity]).
      assert (HM2 : LMEM v (mkW s c r') M2) by (apply (LMEM_store_fscratch v C s c r' M1 64 _ HM1 Hput'); split; [left; reflexivity | reflexivity]).
      assert (HM3 : LMEM v (mkW s' c r') M3).
      { apply (LMEM_store_scalar v C s c r' _ M2 8 _ HM2); [lia | cbn; lia | exact Hput' | | reflexivity | reflexivity | reflexivity | reflexivity].
        apply (is6_upd_mode M2 (cv_S v) _ s LEN_ (lm_sc _ _ _ HM2)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
      assert (HRC3 : RETC v (mkW s' c r') M3).
      { subst M3. apply (RETC_other v C); [| clear - CS; lia | clear - CS; cbn; lia | unfold sep in CfS; clear - CfS CS; cbn; lia].
        subst M2. apply (RETC_regs v (mkW s c r')); [exact (RETC_store v C s c r' M1) | reflexivity]. }
      assert (HX3 : LX v (mkW s' c r')) by (apply (LX_step0 v s c r s' c r' HX NH NB); subst s' r'; try reflexivity; [live_mode_tac | cbn; lia | exact Xmsg | bk_side]).
      assert (RI' : RINV (cv_NI v) (cv_NO v) r') by (subst r'; unfold RINV in *; cbn; exact RI0).
      symex_reg HR1 (1%bv : reg) as Q1.
      assert (HF3 : LFIXc v R1) by (unfold LFIXc, INF_FRAME; regs_via Hfr1; first [exact Q1 | match goal with |- ?G => idtac "LFIX LEFT" G end]).
      assert (HV3 : LVARS v (mkW s' c r') R1) by (unfold LVARS; cbn [w_r]; subst r'; cbn; regs_via Hfr1; match goal with |- ?G => idtac "LVARS3 LEFT" G end).
      symex_reg HR1 (13%bv : reg) as Q13.
      destruct (len__core v C IFAST FFOK FASTOK GFOB FFRAME s' c r' R1 M3 (HPL eq_refl) ltac:(reflexivity) (len_facts_mode v s c LEN_ (HLF eq_refl)) RI' HM3 HRC3 HX3 HF3 Q13 HV3)
        as (R' & M' & pc' & Hms2 & HPOST).
      exists R', M', pc'. split; [eapply msteps_trans; [| exact Hms2]; subst M3 M2 M1; by_run Hms1|].
      apply (arm_post_rebase v s c r c r'); [subst r'; reflexivity|].
      apply (arm_post_chain v (mkW s c r') (mkW s' c r') M M3); [subst s'; apply same_blocks_mode | | exact HPOST].
      cbn [w_r]. subst r'. cbn [ir_put irset_ret]. subst M3 M2 M1.
      apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
      do 2 (apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r)); [| lia | clear - Csp; lia | clear - Csp; cbn; lia | left; unfold INF_FRAME, INF_SCRATCH; clear; cbn; lia]).
      apply MFRAME_refl.
    -
      replace (negb (ret =? 0)) with true by (symmetry; rewrite Bool.negb_true_iff; apply Z.eqb_neq; exact R0).
      assert (Hrm0 : ret mod 2 ^ 64 <> 0).
      { intros E. apply R0. destruct Hret as [H|[H|H]]; subst ret; [reflexivity | discriminate E | discriminate E]. }
      arm_symexP (@nil (Z * expr)) ilCD 14%nat [false]
        [RVal (ELit 16209); RVal (EVar 35%nat)]
        cpins [(45%nat, 2 ^ 64)] v r [ret mod 2 ^ 64] NoVals F0
        (mkst R (Z_to_bv 64 0x1fff8) M s6u_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      all: match goal with |- ?G => idtac "LEFTC2" G end.
      rewrite le8_mod64 in Hms1.
      set (r' := irset_ret r ret) in *. set (c' := icset_msg c MSG_invalid_distances_set) in *. set (s' := iset_mode s BAD) in *.
      set (M1 := wbytes M (zw (cv_sp v - 256 + 64)) (Z_to_le_bytes 8 ret)) in *.
      set (M2 := wbytes M1 (zw (cv_ZP v + 48)) (Z_to_le_bytes 8 66936)) in *.
      set (M3 := wbytes M2 (zw (cv_S v + 8)) (Z_to_le_bytes 4 16209)) in *.
      assert (Hput' : 0 <= ir_put r' <= cv_NO v) by (subst r'; exact Hput).
      assert (HM0 : LMEM v (mkW s c r') M) by (apply (LMEM_regs v s c r c r' M HM); subst r'; reflexivity).
      assert (HM1 : LMEM v (mkW s c r') M1) by (apply (LMEM_store_fscratch v C s c r' M 64 _ HM0 Hput'); split; [left; reflexivity | reflexivity]).
      assert (HM2 : LMEM v (mkW s c' r') M2) by (exact (LMEM_store_msg v C s c r' M1 MSG_invalid_distances_set HM1 Hput')).
      assert (HM3 : LMEM v (mkW s' c' r') M3).
      { apply (LMEM_store_scalar v C s c' r' _ M2 8 _ HM2); [lia | cbn; lia | exact Hput' | | reflexivity | reflexivity | reflexivity | reflexivity].
        apply (is6_upd_mode M2 (cv_S v) _ s BAD (lm_sc _ _ _ HM2)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
      assert (HRC3 : RETC v (mkW s' c' r') M3).
      { subst M3 M2. apply (RETC_other v C); [| clear - CS; lia | clear - CS; cbn; lia | unfold sep in CfS; clear - CfS CS; cbn; lia].
        apply (RETC_other v C); [| clear - CZP; lia | clear - CZP; cbn; lia | unfold sep in CfZ; clear - CfZ CZP; cbn; lia].
        exact (RETC_store v C s c r' M). }
      pose proof (icset_msg_facts c MSG_invalid_distances_set) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11).
      assert (HX3 : LX v (mkW s' c' r')).
      { apply (LX_step0 v s c r s' c' r' HX NH NB); subst s' c' r'; try reflexivity; [live_mode_tac | cbn; clear - Hret; lia | rewrite K11; unfold MSG_invalid_distances_set; lia | bk_side]. }
      arm_disp C HM3 Hfr1 R2 Hms2 G26' Hfr2.
      exists R2, M3, (arm6_pc (is_mode s')). split; [eapply msteps_trans; [| exact Hms2]; subst M3 M2 M1; by_run Hms1|].
      cbn [arm_post]. split; [subst s'; reflexivity|]. split; [| split; [subst s'; apply same_blocks_mode |]].
      + split; [exact HM3|]. split; [exact HRC3|]. split; [exact HX3|].
        symex_reg HR1 (1%bv : reg) as W1. symex_reg HR1 (13%bv : reg) as W13. symex_reg HR1 (11%bv : reg) as W11.
        unfold LREG_arm. split; [| split; [| intros _; exact G26']].
        * unfold LFIX, INF_FRAME. regs_via2 Hfr2 Hfr1; first [exact W1 | exact W13 | exact W11 | match goal with |- ?G => idtac "LFIX2 LEFT" G end].
        * unfold LVARS; cbn [w_r]. subst r'. cbn. regs_via2 Hfr2 Hfr1; match goal with |- ?G => idtac "LVARS2 LEFT" G end.
      + cbn [w_r]. subst r'. cbn [ir_put irset_ret]. subst M3 M2 M1.
        apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
        apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r)); [| lia | clear - CZP; lia | clear - CZP; cbn; lia | right; right; left; clear; cbn; lia].
        apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r) M M); [apply MFRAME_refl | lia | clear - Csp; lia | clear - Csp; cbn; lia | left; unfold INF_FRAME, INF_SCRATCH; clear; cbn; lia].
  Qed.
End SegC.
End FXG.
End InflA_Codelens5.
Export InflA_Codelens5.

