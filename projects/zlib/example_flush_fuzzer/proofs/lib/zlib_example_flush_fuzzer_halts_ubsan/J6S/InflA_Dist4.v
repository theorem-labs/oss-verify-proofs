(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateGarbBase InflateInvTab.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import Prog ZIface InflateState InflateFast InflateArms Inflate
     InflateInv InflateInvKit InflateInvRun.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6S Require Import Segs6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S Require Import ISLayout IS6 InflMem InflRod6 InflCtx6 InflArmLib6 InflArmLib6b InflNeed6
     InflA_Match2 InflA_Distext2 InflA_Distext3.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S Require Import InflDec6 InflA_Dist2 InflA_Dist3.
Import ListNotations.
Local Open Scope Z_scope.
#[local] Transparent bkv sbv.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

Definition ilDT : cfg := ilSx [0x1e750] [].

Section DistT.
  Variable v : icv.
  Hypothesis C : ictx v.

  Ltac open_dfacts HD :=
    destruct HD as (Hsane & Hlen & Hback & Hwh & Hwn & Hwl & Hws & Hwb & CI & (ext & TD & Hext) & Hofs).

  Definition tpins : list (Z * expr) :=
    [(2, EVar 32%nat); (8, EVar 33%nat); (10, EVar 34%nat); (11, EVar 35%nat); (22, EAdd (EVar 33%nat) (ELit 168)); (20, ELit 16209);
     (19, EAdd (EVar 37%nat) (EVar 38%nat)); (1, EVar 39%nat); (23, EVar 40%nat);
     (18, EAdd (EVar 33%nat) (ELit 7160));
     (17, EVar 36%nat); (30, EAdd (EVar 43%nat) (EVar 44%nat)); (5, EVar 41%nat);
     (6, EVar 45%nat); (14, EVar 46%nat); (16, EVar 47%nat); (15, EVar 48%nat);
     (28, EVar 49%nat); (7, EVar 50%nat)].
  Definition tvb : list (nat * Z) :=
    [(45%nat, 2 ^ 15); (46%nat, 16); (47%nat, 2 ^ 16); (48%nat, 2 ^ 63); (49%nat, 2 ^ 63); (50%nat, 256); (51%nat, 2 ^ 32); (52%nat, 256); (53%nat, 65536)].

  Lemma dist_T : forall s c r R M b1 h1 n1 last,
    is_mode s = DIST -> dist_facts v s c -> RINV (cv_NI v) (cv_NO v) r ->
    1 <= code_op last <= 15 - is_distbits s -> code_bits last = is_distbits s ->
    (forall j, 0 <= j < 2 ^ code_op last ->
       term_ok DISTS (15 - is_distbits s) (cat (is_codes s) (is_distcode s) (code_val last + j)) = true) ->
    (exists ext, tab_ok DISTS (cat (is_codes s) (is_distcode s)) (is_distbits s) ext = true /\ code_val last + 2 ^ code_op last <= ext /\ ext <= cext (is_distcode s)) ->
    wrap32 (code_bits last + code_bits (dent2 s last (ir_hold r))) <= ir_bits r ->
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LX v (mkW s c r) -> DJE2 v s b1 h1 n1 last r R ->
    exists R' M' pc',
      msteps s6_segs (mkst R (Z_to_bv 64 0x1e724) M s6_rom) (mkst R' (Z_to_bv 64 pc') M' s6_rom)
      /\ arm_post v (mkW s c r) M (dist_res (dent2 s last (ir_hold r)) (is_back s + code_bits last) s c (rdrop r (code_bits last))) R' M' pc'.
  Proof.
    intros s c r R M b1 h1 n1 last Hmode HD RI LK LB SUB (ext' & TD' & LXT & Hext') Hneed HM HRC HX HJ. pose proof HD as HD0. open_dfacts HD.
    pose proof HJ as X. unfold DJE2, DK2 in X.
    destruct X as ((G2 & G25 & G10 & G11 & G21 & G19 & G24 & G3 & G4 & G18 & G1 & G9 & G12 & G13 & G27 & G6 & G14 & G16 & G15) & G22 & G17 & G30 & G5 & G28 & G7).
    open_ictx C. open_lmem HM. open_retc HRC. open_lx HX. open_rinv RI. pose proof CI as CI'. open_cinv CI. open_frame Mfr. unfold mapped in *.
    pose proof (tab_ok_root _ _ _ _ TD') as (Rt1 & Rt2 & Rt3).
    pose proof (ctab6_range v (is_distcode s) C Hofs) as [HA0 HA1].
    pose proof (ctab6_cells v s c r M (is_distcode s) C HM Hofs) as TAB.
    pose proof (ones_range15 (code_bits last + code_op last) ltac:(clear - Rt1 LK LB; lia)) as Hones.
    pose proof (code_val_range last) as Hlv.
    pose proof (shiftr_BITSv_sub (ir_hold r) (code_bits last) (code_op last) ltac:(clear - Rt1 LB; lia) ltac:(clear - LK; lia)) as HJ2.
    set (J := code_val last + Z.shiftr (BITSv (ir_hold r) (code_bits last + code_op last)) (code_bits last)) in *.
    set (here := cat (is_codes s) (is_distcode s) J).
    assert (Ehere : dent2 s last (ir_hold r) = here) by reflexivity. rewrite Ehere in Hneed, G7 |- *.
    pose proof (SUB _ HJ2) as TE. change (cat _ _ _) with here in TE.
    destruct (term_ok_DISTS _ _ TE) as (Bh & _).
    pose proof (code_bits_range here) as Hcb. pose proof (code_op_range here) as Hop. pose proof (code_val_range here) as Hval.
    rewrite wrap32_id in Hneed by (clear - Bh Rt1 LB Hcb; lia).
    pose proof (is6_back _ _ _ _ Msc) as C7148.
    assert (Hbm : 0 <= is_back s mod 2 ^ 32 < 2 ^ 32) by (apply Z.mod_pos_bound; lia).
    arm_symexP (@nil (Z * expr)) ilDT 20%nat (@nil bool)
      [RVal (EVar 51%nat); RVal (EVar 52%nat); RVal (EVar 53%nat); RVal (ELit 18446744073709535436); RVal (ELit 75024)] tpins tvb v r
      [Z.ones (code_bits last + code_op last); code_bits last; code_val last; ctab6 v (is_distcode s);
       ctab6 v (is_distcode s) + 4 * J; code_bits here; is_back s mod 2 ^ 32; code_op here; code_val here] NoVals F0
      (mkst R (Z_to_bv 64 0x1e724) M s6_rom) R1 HR1 Hfr1 Hms1.
    all: try arm_side.
    all: subst here J.
    all: try (tab_read TAB (code_val last + Z.shiftr (BITSv (ir_hold r) (code_bits last + code_op last)) (code_bits last)); clear - HJ2 LXT Hext' Hlv; lia).
    set (J := code_val last + Z.shiftr (BITSv (ir_hold r) (code_bits last + code_op last)) (code_bits last)) in *.
    set (here := cat (is_codes s) (is_distcode s) J) in *.
    pose proof (RINV_drop (cv_NI v) (cv_NO v) ltac:(clear - CI0; lia) ltac:(clear - CP0; lia) r (code_bits last) RI ltac:(clear - Hneed Bh Rt1 LB; lia)) as [EW RI'].
    unfold rdrop. rewrite EW.
    set (r' := irset_bits (irset_hold r (Z.shiftr (ir_hold r) (code_bits last))) (ir_bits r - code_bits last)) in *.
    assert (NH : is_mode s <> HEAD) by (rewrite Hmode; cbv; discriminate).
    assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
    assert (HM' : LMEM v (mkW s c r') M) by (apply (LMEM_regs v s c r c r' M HM); subst r'; reflexivity).
    assert (HRC' : RETC v (mkW s c r') M) by (apply (RETC_regs v (mkW s c r)); [exact HRC | subst r'; reflexivity]).
    assert (HX' : LX v (mkW s c r')) by (apply (LX_step0 v s c r s c r' HX NH NB); subst r'; try reflexivity; [exact Xlive | exact Xret | exact Xmsg]).
    symex_reg HR1 (31%bv : reg) as Q31. change 18446744073709535436 with ((-16180) mod 2 ^ 64) in Q31. rewrite zw_neg_mod in Q31.
    symex_reg HR1 (29%bv : reg) as Q29. symex_reg HR1 (30%bv : reg) as Q30.
    symex_reg HR1 (23%bv : reg) as Q23. symex_reg HR1 (13%bv : reg) as Q13. symex_reg HR1 (12%bv : reg) as Q12. symex_reg HR1 (26%bv : reg) as Q27.
    symex_reg HR1 (15%bv : reg) as Q15. symex_reg HR1 (14%bv : reg) as Q14. symex_reg HR1 (6%bv : reg) as Q6. symex_reg HR1 (16%bv : reg) as Q16.
    rewrite zalu_srl_small in Q23 by (clear - Rhold64 Rt1 LB; lia).
    rewrite szwrap32_small in Q13 by (clear - Hneed Bh Rbits Rt1 LB; lia).
    rewrite (szwrap32_of_mod32 (is_back s) Hback) in Q15.
    assert (HFR : FREG v s r' here (is_back s + code_bits last) R1).
    { unfold FREG, LFIX, INF_FRAME, A6_JTAB. subst r'. cbn [ir_put ir_left ir_out ir_hold ir_bits ir_have ir_next irset_bits irset_hold].
      rewrite Z.shiftr_div_pow2 by (clear - Rt1 LB; lia).
      regs_via Hfr1; first [exact Q31 | exact Q29 | exact Q30 | exact Q23 | exact Q13 | exact Q12 | exact Q27 | exact Q15 | exact Q14 | exact Q6 | exact Q16
                           | match goal with |- ?G => idtac "FREG LEFT" G end]. }
    destruct (dist_fin v C s c r' R1 M here (is_back s + code_bits last) (15 - is_distbits s) Hmode HD0 RI' TE
                ltac:(subst r'; cbn; clear - Hneed; lia) HM' HRC' HX' HFR) as (R' & M' & pc' & Hms2 & HPOST).
    exists R', M', pc'. split; [eapply msteps_trans; [| exact Hms2]; by_run Hms1|].
    apply (arm_post_rebase v s c r c r'); [subst r'; reflexivity | exact HPOST].
  Qed.
End DistT.
End FXG.
