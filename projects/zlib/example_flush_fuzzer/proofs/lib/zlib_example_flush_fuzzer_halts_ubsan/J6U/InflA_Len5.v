(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require InflateGarbBase InflateInvTab.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Prog ZIface InflateState InflateFast InflateArms Inflate InflateInv InflateInvKit InflateInvRun.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U Require Segs6u.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S Require ISLayout InflMem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require IS6 InflRod6 InflCtx6 InflArmLib6 InflArmLib6b InflNeed6 InflA_Distext3.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require InflDec6 InflA_Dist3 InflA_Lenext3.

Module InflA_Len1.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateGarbBase OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvTab.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.CatExec OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.CatSim OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.SeqExec OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.StoreOk OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Hoare OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.StepTac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymEx2Expr OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymEx2 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymEx2Tac OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.MemRel OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymAux OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.RomRead.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.Prog OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateFast OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateArms OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.Inflate OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInv OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvKit OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvRun.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U.Segs6u.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S.ISLayout OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S.InflMem.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.IS6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflRod6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflCtx6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflArmLib6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflArmLib6b OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflNeed6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflDec6.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

Definition ilL1 : cfg := ilSx [0x20af4; 0x20b50] [AV (EAdd (EVar 43%nat) (EVar 44%nat)) 0 1 0 (EVar 44%nat)].

Section LenL1.
  Variable v : icv.
  Variables (s : inflate_state) (c : icall).
  Hypothesis C : ictx v.
  Variables (b0 h0 n0 : Z).
  Hypothesis Hb0 : 0 <= b0.
  Hypothesis Hn0 : 0 <= n0.
  Variable ext : Z.
  Hypothesis TD : tab_ok LENS (cat (is_codes s) (is_lencode s)) (is_lenbits s) ext = true.
  Hypothesis Hext : ext <= cext (is_lencode s).
  Hypothesis Hofs : cofs_ok (is_lencode s).
  Hypothesis CI : CINV (cv_NI v) (cv_NO v) c.

  Local Abbreviation db := (is_lenbits s).
  Local Abbreviation A := (ctab6 v (is_lencode s)).
  Definition lent1 (h : Z) : Z := cat (is_codes s) (is_lencode s) (BITSv h db).

  Definition LK1 (r : iregs) (R : bvmap 5 word) : Prop :=
    LFIXc v R /\ getr R 9 = zw (cv_P0 v + ir_put r) /\ getr R 13 = zw A /\ getr R 29 = zw (Z.ones db) /\ getr R 15 = zw 1
    /\ getr R 19 = zw b0 /\ getr R 23 = zw h0 /\ getr R 26 = zw (cv_I0 v + n0) /\ getr R 30 = zw (h0 * 2 ^ 32).
  Definition LJS (r : iregs) (R : bvmap 5 word) : Prop :=
    LK1 r R /\ getr R 25 = zw (ir_hold r) /\ getr R 12 = zw (ir_have r) /\ getr R 17 = zw (ir_have r) /\ getr R 5 = zw (8 * ir_have r)
    /\ getr R 14 = zw (cv_I0 v + ir_next r) /\ getr R 6 = zw (cv_I0 v + ir_next r) /\ getr R 16 = zw (ir_bits r) /\ getr R 11 = zw (ir_bits r)
    /\ b0 + 8 * (h0 - ir_have r) = ir_bits r /\ n0 + (h0 - ir_have r) = ir_next r /\ 0 <= h0 - ir_have r.
  Definition LJE (r : iregs) (R : bvmap 5 word) : Prop :=
    LK1 r R /\ getr R 25 = zw (ir_hold r) /\ getr R 12 = zw (ir_have r) /\ getr R 17 = zw (ir_have r) /\ getr R 5 = zw (8 * ir_have r)
    /\ getr R 14 = zw (cv_I0 v + ir_next r) /\ getr R 6 = zw (cv_I0 v + ir_next r) /\ getr R 16 = zw (ir_bits r) /\ getr R 11 = zw (ir_bits r)
    /\ getr R 20 = zw (cent (lent1 (ir_hold r))) /\ getr R 28 = zw (cent (lent1 (ir_hold r)) / 2 ^ 8) /\ getr R 7 = zw (code_bits (lent1 (ir_hold r))).

  Ltac open_ljs HJ :=
    let X := fresh in pose proof HJ as X; unfold LJS, LK1 in X;
    destruct X as ((HF & G9 & G13 & G29 & G15 & G18 & G24 & G25 & G30) & G22 & G12 & G17 & G5 & G14 & G6 & G16 & G11 & Ib & In & Ih); open_fixc HF.

  Definition lpins1 : list (Z * expr) :=
    [(2, EVar 32%nat); (8, EVar 33%nat); (18, EVar 34%nat); (1, ELit 16209); (9, EAdd (EVar 37%nat) (EVar 38%nat));
     (13, EVar 46%nat); (29, EVar 45%nat); (15, ELit 1);
     (25, EVar 40%nat); (12, EVar 36%nat); (17, EVar 36%nat); (5, EMul (ELit 8) (EVar 36%nat));
     (14, EAdd (EVar 43%nat) (EVar 44%nat)); (6, EAdd (EVar 43%nat) (EVar 44%nat)); (16, EVar 41%nat); (11, EVar 41%nat);
     (19, EVar 47%nat); (23, EVar 48%nat); (26, EAdd (EVar 43%nat) (EVar 49%nat)); (30, EShl (EVar 48%nat) 32)].
  Definition lvb1 : list (nat * Z) :=
    [(45%nat, 2 ^ 15); (46%nat, 2 ^ 63); (47%nat, 2 ^ 63); (48%nat, 2 ^ 31); (49%nat, 2 ^ 31); (50%nat, 65536); (51%nat, 65536)].

  Ltac l1_side Hby Rbits Rhold Hb64 Rt1 Rt2 TAB HA0 HA1 Hext :=
    cbn [famA]; rewrite ?bmod_get by exact Hby;
    rewrite ?idx1_exec by (first [exact Rhold | exact Hby | clear - Rbits Hb64 Rt1; lia]);
    rewrite ?cent_reasm, ?cent_bits;
    lazymatch goal with
    | |- exists bs, rdn _ _ _ _ = Some bs /\ _ => match goal with |- context [BITSv ?h ?n] => tab_read2 TAB (BITSv h n); pose proof (BITSv_bound h n ltac:(lia)); lia end
    | |- 0 <= _ /\ _ <= 2 ^ 64 => match goal with |- context [BITSv ?h ?n] => generalize (BITSv_bound h n ltac:(lia)); clear - HA0 HA1 Hext Rt2; intro; lia end
    | |- context [if _ <? _ then 1 else 0] => match goal with |- context [BITSv ?h ?n] => pose proof (BITSv_bound h n ltac:(lia)); ub_ptr_side end
    | |- exists _, _ => idtac
    | |- _ => first [ assumption | match goal with |- context [BITSv ?h ?n] => pose proof (BITSv_bound h n ltac:(lia)); lia end | idtac ]
    end.

  Ltac lj_close HR Hfr r Hby Rbits Rhold Hb64 Hh Rnh Rnx0 CI0 :=
    let Q22 := fresh in let Q12 := fresh in let Q17 := fresh in let Q5 := fresh in let Q14 := fresh in let Q6 := fresh in
    let Q16 := fresh in let Q11 := fresh in let Q19 := fresh in let Q28 := fresh in let Q7 := fresh in
    symex_reg HR (25%bv : reg) as Q22; symex_reg HR (12%bv : reg) as Q12; symex_reg HR (17%bv : reg) as Q17; symex_reg HR (5%bv : reg) as Q5;
    symex_reg HR (14%bv : reg) as Q14; symex_reg HR (6%bv : reg) as Q6; symex_reg HR (16%bv : reg) as Q16; symex_reg HR (11%bv : reg) as Q11;
    symex_reg HR (20%bv : reg) as Q19; symex_reg HR (28%bv : reg) as Q28; symex_reg HR (7%bv : reg) as Q7;
    cbn [famA] in Q22; rewrite bmod_get in Q22 by exact Hby;
    rewrite ?cent_reasm in Q19; rewrite ?cent_reasm in Q28; rewrite ?cent_reasm, ?cent_bits in Q7;
    unfold LJS, LJE, LK1, pull1; cbn [ir_next ir_have ir_put ir_left ir_hold ir_bits ir_in ir_out ir_ret];
    repeat match goal with |- _ /\ _ => split end;
    first [ assumption
          | lazymatch goal with |- LFIXc _ _ => lfixc_close Hfr HR end
          | lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr n eq_refl); assumption end
          | rewrite Q22; rewrite zalu_sll_small; [f_equal; lia | clear - Hby; lia | clear - Rbits Hb64; lia
              | clear - Hby Rbits Hb64 Rhold; pose proof (pull_hold_lt _ _ _ Rhold (proj1 Rbits) Hby); assert (2 ^ (ir_bits r + 8) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia); lia]
          | rewrite Q12; rewrite ?szwrap32_small by (clear - Hh Rnh Rnx0 CI0; lia); f_equal; lia
          | rewrite Q17; f_equal; lia
          | rewrite Q5; f_equal; lia
          | rewrite Q14; f_equal; lia
          | rewrite Q6; f_equal; lia
          | rewrite Q16; f_equal; lia
          | rewrite Q11; f_equal; lia
          | rewrite Q19; f_equal; f_equal; f_equal; lia
          | rewrite Q28; f_equal; f_equal; f_equal; f_equal; lia
          | rewrite Q7; f_equal; f_equal; f_equal; lia
          | lia
          | match goal with |- ?G => idtac "DJ LEFT" G end ].

  Ltac l1_prep C TD Hofs HM Rt1 Rt2 Rt3 HA0 HA1 TAB Hones :=
    pose proof (tab_ok_root _ _ _ _ TD) as (Rt1 & Rt2 & Rt3);
    pose proof (ctab6_range v (is_lencode s) C Hofs) as [HA0 HA1];
    pose proof (ctab6_cells v s c _ _ (is_lencode s) C HM Hofs) as TAB;
    pose proof (ones_range15 db Rt1) as Hones.

  Lemma len1_step_H : forall r R M,
    LMEM v (mkW s c r) M -> LJS r R -> RINV (cv_NI v) (cv_NO v) r -> 0 < ir_have r -> ir_bits r + 8 < 64 ->
    ir_bits r + 8 < code_bits (lent1 (ir_hold (pull1 c r))) ->
    exists R1, msteps s6u_segs (mkst R (Z_to_bv 64 0x20af4) M s6u_rom) (mkst R1 (Z_to_bv 64 0x20af4) M s6u_rom)
               /\ LJS (pull1 c r) R1.
  Proof.
    intros r R M HM HJ RI Hh Hb64 Hb. open_ljs HJ.
    open_ictx C. open_lmem HM. open_rinv RI. open_cinv CI. unfold mapped in *.
    l1_prep C TD Hofs HM Rt1 Rt2 Rt3 HA0 HA1 TAB Hones.
    assert (Hby : 0 <= arr_get (ic_input c) (ir_next r) < 256) by (apply Cinb; clear - Hh Rnx0 Rhv0 Rnh; lia).
    pose proof (cells_bmod _ _ _ _ Minp Cinb) as Hin0.
    pose proof (fun j (_ : 0 <= j < cv_NI v) => bmod_range (arr_get (ic_input c)) j) as Hinr.
    assert (Hh0 : 0 <= h0 < 2 ^ 31) by (clear - Ih In Hn0 Hh Rnh Rnx0 Rhv0 CI0; lia).
    pose proof (code_bits_range (lent1 (ir_hold (pull1 c r)))) as Hcb.
    pose proof (code_val_range (lent1 (ir_hold (pull1 c r)))) as Hcv.
    pose proof (clo_range (lent1 (ir_hold (pull1 c r)))) as Hclo.
    unfold lent1 in Hb, Hcb, Hcv, Hclo |- *. cbn [ir_hold pull1] in Hb, Hcb, Hcv, Hclo |- *.
    arm_symexP (@nil (Z * expr)) ilL1 34%nat [false; false; false; false; true; false] [RVal (EVar 50%nat); RVal (EVar 51%nat)] lpins1 lvb1 v r
      [Z.ones db; A; b0; h0; n0;
       code_val (cat (is_codes s) (is_lencode s) (BITSv (ir_hold r + arr_get (ic_input c) (ir_next r) * 2 ^ ir_bits r) db));
       clo (cat (is_codes s) (is_lencode s) (BITSv (ir_hold r + arr_get (ic_input c) (ir_next r) * 2 ^ ir_bits r) db))]
      NoVals (famA c s)
      (mkst R (Z_to_bv 64 0x20af4) M s6u_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    all: l1_side Hby Rbits Rhold Hb64 Rt1 Rt2 TAB HA0 HA1 Hext.
    all: match goal with |- ?G => idtac "LEFTL1H" G end.
    exists R1. split; [by_run Hms|].
    lj_close HR1 Hfr r Hby Rbits Rhold Hb64 Hh Rnh Rnx0 CI0.
  Qed.

  Lemma len1_step_E : forall r R M,
    LMEM v (mkW s c r) M -> LJS r R -> RINV (cv_NI v) (cv_NO v) r -> 0 < ir_have r -> ir_bits r + 8 < 64 ->
    code_bits (lent1 (ir_hold (pull1 c r))) <= ir_bits r + 8 ->
    exists R1, msteps s6u_segs (mkst R (Z_to_bv 64 0x20af4) M s6u_rom) (mkst R1 (Z_to_bv 64 0x20b50) M s6u_rom)
               /\ LJE (pull1 c r) R1.
  Proof.
    intros r R M HM HJ RI Hh Hb64 Hb. open_ljs HJ.
    open_ictx C. open_lmem HM. open_rinv RI. open_cinv CI. unfold mapped in *.
    l1_prep C TD Hofs HM Rt1 Rt2 Rt3 HA0 HA1 TAB Hones.
    assert (Hby : 0 <= arr_get (ic_input c) (ir_next r) < 256) by (apply Cinb; clear - Hh Rnx0 Rhv0 Rnh; lia).
    pose proof (cells_bmod _ _ _ _ Minp Cinb) as Hin0.
    pose proof (fun j (_ : 0 <= j < cv_NI v) => bmod_range (arr_get (ic_input c)) j) as Hinr.
    assert (Hh0 : 0 <= h0 < 2 ^ 31) by (clear - Ih In Hn0 Hh Rnh Rnx0 Rhv0 CI0; lia).
    pose proof (code_bits_range (lent1 (ir_hold (pull1 c r)))) as Hcb.
    pose proof (code_val_range (lent1 (ir_hold (pull1 c r)))) as Hcv.
    pose proof (clo_range (lent1 (ir_hold (pull1 c r)))) as Hclo.
    unfold lent1 in Hb, Hcb, Hcv, Hclo |- *. cbn [ir_hold pull1] in Hb, Hcb, Hcv, Hclo |- *.
    arm_symexP (@nil (Z * expr)) ilL1 34%nat [false; false; false; false; true; true] [RVal (EVar 50%nat); RVal (EVar 51%nat)] lpins1 lvb1 v r
      [Z.ones db; A; b0; h0; n0;
       code_val (cat (is_codes s) (is_lencode s) (BITSv (ir_hold r + arr_get (ic_input c) (ir_next r) * 2 ^ ir_bits r) db));
       clo (cat (is_codes s) (is_lencode s) (BITSv (ir_hold r + arr_get (ic_input c) (ir_next r) * 2 ^ ir_bits r) db))]
      NoVals (famA c s)
      (mkst R (Z_to_bv 64 0x20af4) M s6u_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    all: l1_side Hby Rbits Rhold Hb64 Rt1 Rt2 TAB HA0 HA1 Hext.
    all: match goal with |- ?G => idtac "LEFTL1E" G end.
    exists R1. split; [by_run Hms|].
    lj_close HR1 Hfr r Hby Rbits Rhold Hb64 Hh Rnh Rnx0 CI0.
  Qed.

  Lemma len1_dry : forall r R M,
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LJS r R -> RINV (cv_NI v) (cv_NO v) r -> ir_have r = 0 ->
    exists R1, msteps s6u_segs (mkst R (Z_to_bv 64 0x20af4) M s6u_rom) (mkst R1 (Z_to_bv 64 pc6_leave) M s6u_rom)
               /\ LREG_leave v (mkW s c r) R1.
  Proof.
    intros r R M HM HRC HJ RI Hh. open_ljs HJ.
    open_ictx C. open_lmem HM. open_frame Mfr. open_retc HRC. open_rinv RI. open_cinv CI. unfold mapped in *.
    l1_prep C TD Hofs HM Rt1 Rt2 Rt3 HA0 HA1 TAB Hones.
    assert (Hh0 : 0 <= h0 < 2 ^ 31) by (clear - Ih In Hn0 Hh Rnh Rnx0 Rhv0 CI0; lia).
    arm_symexP (@nil (Z * expr)) ilL1 16%nat [true] [RVal (EVar 50%nat); RVal (EVar 35%nat)] lpins1
      [(45%nat, 2 ^ 15); (46%nat, 2 ^ 63); (47%nat, 2 ^ 63); (48%nat, 2 ^ 31); (49%nat, 2 ^ 31); (50%nat, 2 ^ 64)] v r
      [Z.ones db; A; b0; h0; n0; ir_ret r mod 2 ^ 64] NoVals (famA c s)
      (mkst R (Z_to_bv 64 0x20af4) M s6u_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    all: match goal with |- ?G => idtac "LEFTL1D" G end.
    exists R1. split; [by_run Hms|].
    symex_reg HR1 (27%bv : reg) as G26'. symex_reg HR1 (19%bv : reg) as G18'. symex_reg HR1 (23%bv : reg) as G24'. symex_reg HR1 (26%bv : reg) as G25'.
    symex_reg HR1 (13%bv : reg) as G13'. symex_reg HR1 (11%bv : reg) as G11'.
    unfold LREG_leave, LVARS, INF_FRAME; cbn [w_r]. regs_via Hfr.
    all: first [ rewrite G24'; rewrite Hh; reflexivity
               | rewrite G18'; f_equal; clear - Ib Hh; lia
               | rewrite G25'; rewrite ?Z.mod_small by (clear - Hh0; lia); f_equal; clear - In Hh; lia
               | rewrite G26'; apply zw_neg_mod
               | exact G13' | exact G11'
               | match goal with |- ?G => idtac "DRY LEFT" G end ].
  Qed.
End LenL1.
End FXG.
End InflA_Len1.

Module InflA_Len2.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateGarbBase OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvTab.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.CatExec OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.CatSim OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.SeqExec OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.StoreOk OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Hoare OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.StepTac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymEx2Expr OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymEx2 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymEx2Tac OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.MemRel OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymAux OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.RomRead.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.Prog OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateFast OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateArms OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.Inflate OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInv OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvKit OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvRun.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U.Segs6u.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S.ISLayout OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S.InflMem.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.IS6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflRod6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflCtx6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflArmLib6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflArmLib6b OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflNeed6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflDec6.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

Definition ilL2 : cfg := ilSx [0x20bec; 0x20c58] [AV (EAdd (EVar 43%nat) (EVar 44%nat)) 0 1 0 (EVar 44%nat)].

Section LenL2.
  Variable v : icv.
  Variables (s : inflate_state) (c : icall).
  Hypothesis C : ictx v.
  Variables (b1 h1 n1 : Z).
  Hypothesis Hb1 : 0 <= b1.
  Hypothesis Hn1 : 0 <= n1.
  Variables (ext last : Z).
  Hypothesis TD : tab_ok LENS (cat (is_codes s) (is_lencode s)) (is_lenbits s) ext = true.
  Hypothesis Hext : ext <= cext (is_lencode s).
  Hypothesis Hofs : cofs_ok (is_lencode s).
  Hypothesis CI : CINV (cv_NI v) (cv_NO v) c.
  Hypothesis LK : 1 <= code_op last <= 15 - is_lenbits s.
  Hypothesis LB : code_bits last = is_lenbits s.
  Hypothesis LXT : code_val last + 2 ^ code_op last <= ext.

  Local Abbreviation db := (is_lenbits s).
  Local Abbreviation A := (ctab6 v (is_lencode s)).
  Local Abbreviation lb := (code_bits last).
  Local Abbreviation lop := (code_op last).
  Local Abbreviation lv := (code_val last).
  Definition lidx2 (h : Z) : Z := lv + Z.shiftr (BITSv h (lb + lop)) lb.
  Definition lent2 (h : Z) : Z := cat (is_codes s) (is_lencode s) (lidx2 h).

  Definition LK2 (r : iregs) (R : bvmap 5 word) : Prop :=
    LFIXc v R /\ getr R 9 = zw (cv_P0 v + ir_put r) /\ getr R 13 = zw A /\ getr R 15 = zw 1
    /\ getr R 30 = zw (Z.ones (lb + lop)) /\ getr R 7 = zw lb /\ getr R 29 = zw lv /\ getr R 28 = zw (cent last / 2 ^ 8)
    /\ getr R 11 = zw b1 /\ getr R 16 = zw b1 /\ getr R 14 = zw (cv_I0 v + n1) /\ getr R 17 = zw h1 /\ getr R 5 = zw (8 * h1).
  Definition LJS2 (r : iregs) (R : bvmap 5 word) : Prop :=
    LK2 r R /\ getr R 25 = zw (ir_hold r) /\ getr R 12 = zw (ir_have r) /\ getr R 31 = zw (cv_I0 v + ir_next r) /\ getr R 6 = zw (cv_I0 v + ir_next r)
    /\ getr R 21 = zw (ir_bits r) /\ getr R 19 = zw (lb - (ir_bits r - b1))
    /\ b1 + 8 * (h1 - ir_have r) = ir_bits r /\ n1 + (h1 - ir_have r) = ir_next r /\ 0 <= h1 - ir_have r.
  Definition LJE2 (r : iregs) (R : bvmap 5 word) : Prop :=
    LK2 r R /\ getr R 25 = zw (ir_hold r) /\ getr R 12 = zw (ir_have r) /\ getr R 31 = zw (cv_I0 v + ir_next r)
    /\ getr R 21 = zw (ir_bits r) /\ getr R 19 = zw (lb - (ir_bits r - b1))
    /\ getr R 20 = zw (cent (lent2 (ir_hold r))) /\ getr R 22 = zw (cent (lent2 (ir_hold r)) / 2 ^ 8)
    /\ getr R 23 = zw (code_bits (lent2 (ir_hold r)) + lb).

  Ltac open_djs HJ :=
    let X := fresh in pose proof HJ as X; unfold LJS2, LK2 in X;
    destruct X as ((HF & G9 & G13 & G15 & G30 & G7 & G29 & G28 & G11 & G16 & G14 & G17 & G5)
                   & G22 & G12 & G31 & G6 & G20 & G18 & Ib & In & Ih); open_fixc HF.

  Definition lpins2 : list (Z * expr) :=
    [(2, EVar 32%nat); (8, EVar 33%nat); (18, EVar 34%nat); (1, ELit 16209); (9, EAdd (EVar 37%nat) (EVar 38%nat));
     (13, EVar 48%nat); (15, ELit 1); (30, EVar 45%nat); (7, EVar 46%nat); (29, EVar 47%nat); (28, EVar 52%nat);
     (11, EVar 50%nat); (16, EVar 50%nat); (14, EAdd (EVar 43%nat) (EVar 51%nat)); (17, EVar 49%nat); (5, EMul (ELit 8) (EVar 49%nat));
     (25, EVar 40%nat); (12, EVar 36%nat); (31, EAdd (EVar 43%nat) (EVar 44%nat)); (6, EAdd (EVar 43%nat) (EVar 44%nat));
     (21, EVar 41%nat); (19, ESub (EVar 46%nat) (ESub (EVar 41%nat) (EVar 50%nat)))].
  Definition lvb2 : list (nat * Z) :=
    [(45%nat, 2 ^ 15); (46%nat, 16); (47%nat, 2 ^ 16); (48%nat, 2 ^ 63); (49%nat, 2 ^ 31); (50%nat, 2 ^ 63); (51%nat, 2 ^ 31); (52%nat, 2 ^ 24);
     (53%nat, 65536); (54%nat, 65536)].

  Ltac l2_side Hby Rbits Rhold Hb64 Rt1 LK Hlv TAB HA0 HA1 Hext LXT Hb :=
    cbn [famA]; rewrite ?bmod_get by exact Hby;
    rewrite ?idx2_pull by (first [exact Rhold | exact Hby | exact Hlv | clear - Rbits Hb64 Rt1 LK LB; lia]);
    rewrite ?idx2_pull_w by (first [exact Rhold | exact Hby | exact Hlv | clear - Rbits Hb64 Rt1 LK LB; lia]);
    rewrite ?cent_reasm, ?cent_bits;
    lazymatch goal with
    | |- exists bs, rdn _ _ _ _ = Some bs /\ _ =>
        match goal with |- context [Z.shiftr (BITSv ?h (lb + lop)) lb] =>
          tab_read2 TAB (lv + Z.shiftr (BITSv h (lb + lop)) lb); pose proof (shiftr_BITSv_sub h lb lop ltac:(lia) ltac:(lia)); lia end
    | |- 0 <= _ /\ _ <= 2 ^ 64 =>
        match goal with |- context [Z.shiftr (BITSv ?h (lb + lop)) lb] =>
          generalize (shiftr_BITSv_sub h lb lop ltac:(lia) ltac:(lia)); clear - HA0 HA1 Hext LXT Hlv; intro; lia end
    | |- context [if _ <? _ then 1 else 0] =>
        match goal with |- context [Z.shiftr (BITSv ?h (lb + lop)) lb] => pose proof (shiftr_BITSv_sub h lb lop ltac:(lia) ltac:(lia)); ub_ptr_side end
    | |- exists _, _ => idtac
    | |- _ => first [ rewrite wrap32_id in Hb by lia; clear - Hb; lia
                    | match goal with |- context [Z.shiftr (BITSv ?h (lb + lop)) lb] => pose proof (shiftr_BITSv_sub h lb lop ltac:(lia) ltac:(lia)); lia end
                    | idtac ]
    end.

  Ltac lj2_close HR Hfr r Hby Rbits Rhold Hb64 Hh Rnh Rnx0 CI0 Rt1 LK Hlv :=
    let Q22 := fresh in let Q12 := fresh in let Q31 := fresh in let Q6 := fresh in let Q20 := fresh in let Q18 := fresh in
    let Q19 := fresh in let Q21 := fresh in let Q23 := fresh in
    symex_reg HR (25%bv : reg) as Q22; symex_reg HR (12%bv : reg) as Q12; symex_reg HR (31%bv : reg) as Q31; symex_reg HR (6%bv : reg) as Q6;
    symex_reg HR (21%bv : reg) as Q20; symex_reg HR (19%bv : reg) as Q18;
    symex_reg HR (20%bv : reg) as Q19; symex_reg HR (22%bv : reg) as Q21; symex_reg HR (23%bv : reg) as Q23;
    cbn [famA] in Q22; rewrite bmod_get in Q22 by exact Hby;
    cbn [famA] in Q19; rewrite ?bmod_get in Q19 by exact Hby; rewrite ?idx2_pull_w in Q19 by (first [exact Rhold | exact Hby | exact Hlv | clear - Rbits Hb64 Rt1 LK LB; lia]); rewrite ?cent_reasm in Q19;
    cbn [famA] in Q21; rewrite ?bmod_get in Q21 by exact Hby; rewrite ?idx2_pull_w in Q21 by (first [exact Rhold | exact Hby | exact Hlv | clear - Rbits Hb64 Rt1 LK LB; lia]); rewrite ?cent_reasm in Q21;
    cbn [famA] in Q23; rewrite ?bmod_get in Q23 by exact Hby; rewrite ?idx2_pull_w in Q23 by (first [exact Rhold | exact Hby | exact Hlv | clear - Rbits Hb64 Rt1 LK LB; lia]); rewrite ?cent_reasm, ?cent_bits in Q23;
    unfold LJS2, LJE2, LK2, pull1; cbn [ir_next ir_have ir_put ir_left ir_hold ir_bits ir_in ir_out ir_ret];
    repeat match goal with |- _ /\ _ => split end;
    first [ assumption
          | lazymatch goal with |- LFIXc _ _ => lfixc_close Hfr HR end
          | lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr n eq_refl); assumption end
          | rewrite Q22; rewrite zalu_sll_small; [f_equal; lia | clear - Hby; lia | clear - Rbits Hb64; lia
              | clear - Hby Rbits Hb64 Rhold; pose proof (pull_hold_lt _ _ _ Rhold (proj1 Rbits) Hby); assert (2 ^ (ir_bits r + 8) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia); lia]
          | rewrite Q12; rewrite ?szwrap32_small by (clear - Hh Rnh Rnx0 CI0; lia); f_equal; lia
          | rewrite Q31; f_equal; lia
          | rewrite Q6; f_equal; lia
          | rewrite Q20; f_equal; lia
          | rewrite Q18; f_equal; lia
          | rewrite Q19; f_equal; f_equal; f_equal; f_equal; lia
          | rewrite Q21; f_equal; f_equal; f_equal; f_equal; f_equal; lia
          | rewrite Q23; f_equal; f_equal; [f_equal; f_equal; f_equal; lia | reflexivity]
          | lia
          | match goal with |- ?G => idtac "LJ2 LEFT" G end ].

  Ltac l2_prep C TD Hofs HM Rt1 Rt2 Rt3 HA0 HA1 TAB Hones Hlv Hc7 :=
    pose proof (tab_ok_root _ _ _ _ TD) as (Rt1 & Rt2 & Rt3);
    pose proof (ctab6_range v (is_lencode s) C Hofs) as [HA0 HA1];
    pose proof (ctab6_cells v s c _ _ (is_lencode s) C HM Hofs) as TAB;
    pose proof (ones_range15 (lb + lop) ltac:(clear - Rt1 LK LB; lia)) as Hones;
    pose proof (code_val_range last) as Hlv;
    pose proof (cent_shr8_range last) as Hc7.

  Lemma len2_step_H : forall r R M,
    LMEM v (mkW s c r) M -> LJS2 r R -> RINV (cv_NI v) (cv_NO v) r -> 0 < ir_have r -> ir_bits r + 8 < 64 ->
    ir_bits r + 8 < wrap32 (lb + code_bits (lent2 (ir_hold (pull1 c r)))) ->
    exists R1, msteps s6u_segs (mkst R (Z_to_bv 64 0x20bec) M s6u_rom) (mkst R1 (Z_to_bv 64 0x20bec) M s6u_rom)
               /\ LJS2 (pull1 c r) R1.
  Proof.
    intros r R M HM HJ RI Hh Hb64 Hb. open_djs HJ. open_ictx C. open_lmem HM. open_rinv RI. open_cinv CI. unfold mapped in *.
    l2_prep C TD Hofs HM Rt1 Rt2 Rt3 HA0 HA1 TAB Hones Hlv Hc7.
    assert (Hh0 : 0 <= h1 < 2 ^ 31) by (clear - Ih In Hn1 Hh Rnh Rnx0 Rhv0 CI0; lia).
    assert (Hby : 0 <= arr_get (ic_input c) (ir_next r) < 256) by (apply Cinb; clear - Hh Rnx0 Rhv0 Rnh; lia).
    pose proof (cells_bmod _ _ _ _ Minp Cinb) as Hin0.
    pose proof (fun j (_ : 0 <= j < cv_NI v) => bmod_range (arr_get (ic_input c)) j) as Hinr.
    pose proof (code_bits_range (lent2 (ir_hold (pull1 c r)))) as Hcb.
    pose proof (code_val_range (lent2 (ir_hold (pull1 c r)))) as Hcv.
    pose proof (clo_range (lent2 (ir_hold (pull1 c r)))) as Hclo.
    unfold lent2, lidx2 in Hb, Hcb, Hcv, Hclo |- *. cbn [ir_hold pull1] in Hb, Hcb, Hcv, Hclo |- *.
    arm_symexP (@nil (Z * expr)) ilL2 36%nat [false; false; false; false; true; false] [RVal (EVar 53%nat); RVal (EVar 54%nat)] lpins2 lvb2 v r
      [Z.ones (lb + lop); lb; lv; A; h1; b1; n1; cent last / 2 ^ 8;
       code_val (cat (is_codes s) (is_lencode s) (lv + Z.shiftr (BITSv (ir_hold r + arr_get (ic_input c) (ir_next r) * 2 ^ ir_bits r) (lb + lop)) lb));
       clo (cat (is_codes s) (is_lencode s) (lv + Z.shiftr (BITSv (ir_hold r + arr_get (ic_input c) (ir_next r) * 2 ^ ir_bits r) (lb + lop)) lb))]
      NoVals (famA c s)
      (mkst R (Z_to_bv 64 0x20bec) M s6u_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    all: l2_side Hby Rbits Rhold Hb64 Rt1 LK Hlv TAB HA0 HA1 Hext LXT Hb.
    all: match goal with |- ?G => idtac "LEFTL2H" G end.
    exists R1. split; [by_run Hms|].
    lj2_close HR1 Hfr r Hby Rbits Rhold Hb64 Hh Rnh Rnx0 CI0 Rt1 LK Hlv.
  Qed.

  Lemma len2_step_E : forall r R M,
    LMEM v (mkW s c r) M -> LJS2 r R -> RINV (cv_NI v) (cv_NO v) r -> 0 < ir_have r -> ir_bits r + 8 < 64 ->
    wrap32 (lb + code_bits (lent2 (ir_hold (pull1 c r)))) <= ir_bits r + 8 ->
    exists R1, msteps s6u_segs (mkst R (Z_to_bv 64 0x20bec) M s6u_rom) (mkst R1 (Z_to_bv 64 0x20c58) M s6u_rom)
               /\ LJE2 (pull1 c r) R1.
  Proof.
    intros r R M HM HJ RI Hh Hb64 Hb. open_djs HJ. open_ictx C. open_lmem HM. open_rinv RI. open_cinv CI. unfold mapped in *.
    l2_prep C TD Hofs HM Rt1 Rt2 Rt3 HA0 HA1 TAB Hones Hlv Hc7.
    assert (Hh0 : 0 <= h1 < 2 ^ 31) by (clear - Ih In Hn1 Hh Rnh Rnx0 Rhv0 CI0; lia).
    assert (Hby : 0 <= arr_get (ic_input c) (ir_next r) < 256) by (apply Cinb; clear - Hh Rnx0 Rhv0 Rnh; lia).
    pose proof (cells_bmod _ _ _ _ Minp Cinb) as Hin0.
    pose proof (fun j (_ : 0 <= j < cv_NI v) => bmod_range (arr_get (ic_input c)) j) as Hinr.
    pose proof (code_bits_range (lent2 (ir_hold (pull1 c r)))) as Hcb.
    pose proof (code_val_range (lent2 (ir_hold (pull1 c r)))) as Hcv.
    pose proof (clo_range (lent2 (ir_hold (pull1 c r)))) as Hclo.
    unfold lent2, lidx2 in Hb, Hcb, Hcv, Hclo |- *. cbn [ir_hold pull1] in Hb, Hcb, Hcv, Hclo |- *.
    arm_symexP (@nil (Z * expr)) ilL2 36%nat [false; false; false; false; true; true] [RVal (EVar 53%nat); RVal (EVar 54%nat)] lpins2 lvb2 v r
      [Z.ones (lb + lop); lb; lv; A; h1; b1; n1; cent last / 2 ^ 8;
       code_val (cat (is_codes s) (is_lencode s) (lv + Z.shiftr (BITSv (ir_hold r + arr_get (ic_input c) (ir_next r) * 2 ^ ir_bits r) (lb + lop)) lb));
       clo (cat (is_codes s) (is_lencode s) (lv + Z.shiftr (BITSv (ir_hold r + arr_get (ic_input c) (ir_next r) * 2 ^ ir_bits r) (lb + lop)) lb))]
      NoVals (famA c s)
      (mkst R (Z_to_bv 64 0x20bec) M s6u_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    all: l2_side Hby Rbits Rhold Hb64 Rt1 LK Hlv TAB HA0 HA1 Hext LXT Hb.
    all: try (rewrite wrap32_id in Hb by lia; clear - Hb; lia).
    all: match goal with |- ?G => idtac "LEFTL2E" G end.
    exists R1. split; [by_run Hms|].
    lj2_close HR1 Hfr r Hby Rbits Rhold Hb64 Hh Rnh Rnx0 CI0 Rt1 LK Hlv.
  Qed.

  Lemma len2_dry : forall r R M,
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LJS2 r R -> RINV (cv_NI v) (cv_NO v) r -> ir_have r = 0 ->
    exists R1, msteps s6u_segs (mkst R (Z_to_bv 64 0x20bec) M s6u_rom) (mkst R1 (Z_to_bv 64 pc6_leave) M s6u_rom)
               /\ LREG_leave v (mkW s c r) R1.
  Proof.
    intros r R M HM HRC HJ RI Hh. open_djs HJ. open_ictx C. open_lmem HM. open_frame Mfr. open_rinv RI. open_cinv CI. unfold mapped in *.
    l2_prep C TD Hofs HM Rt1 Rt2 Rt3 HA0 HA1 TAB Hones Hlv Hc7.
    assert (Hh0 : 0 <= h1 < 2 ^ 31) by (clear - Ih In Hn1 Hh Rnh Rnx0 Rhv0 CI0; lia). open_retc HRC.
    arm_symexP (@nil (Z * expr)) ilL2 14%nat [true] [RVal (EVar 53%nat); RVal (EVar 35%nat)] lpins2
      [(45%nat, 2 ^ 15); (46%nat, 16); (47%nat, 2 ^ 16); (48%nat, 2 ^ 63); (49%nat, 2 ^ 31); (50%nat, 2 ^ 63); (51%nat, 2 ^ 31); (52%nat, 2 ^ 24); (53%nat, 2 ^ 64)] v r
      [Z.ones (lb + lop); lb; lv; A; h1; b1; n1; cent last / 2 ^ 8; ir_ret r mod 2 ^ 64] NoVals (famA c s)
      (mkst R (Z_to_bv 64 0x20bec) M s6u_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    all: match goal with |- ?G => idtac "LEFTL2D" G end.
    exists R1. split; [by_run Hms|].
    symex_reg HR1 (27%bv : reg) as G26'. symex_reg HR1 (19%bv : reg) as G18'. symex_reg HR1 (23%bv : reg) as G24'. symex_reg HR1 (26%bv : reg) as G25'.
    symex_reg HR1 (13%bv : reg) as G13'. symex_reg HR1 (11%bv : reg) as G11'.
    unfold LREG_leave, LVARS, INF_FRAME; cbn [w_r]. regs_via Hfr.
    all: first [ rewrite G24'; rewrite Hh; reflexivity
               | rewrite G18'; f_equal; clear - Ib Hh; lia
               | rewrite G25'; f_equal; clear - In Hh; lia
               | rewrite G26'; apply zw_neg_mod
               | exact G13' | exact G11'
               | match goal with |- ?G => idtac "DRYL2 LEFT" G end ].
  Qed.
End LenL2.
End FXG.
End InflA_Len2.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require InflA_Len3 InflA_Len4.

From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateGarbBase InflateInvTab.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import Prog ZIface InflateState InflateFast InflateArms Inflate InflateInv InflateInvKit InflateInvRun.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U Require Import Segs6u.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S Require Import ISLayout InflMem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import IS6 InflRod6 InflCtx6 InflArmLib6 InflArmLib6b InflNeed6. From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require InflA_Distext3. Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflA_Distext3.InflA_Distext2. From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import InflA_Distext3.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import InflDec6 InflA_Dist3. From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require InflA_Lenext3. Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflA_Lenext3.InflA_Lenext2. From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import InflA_Lenext3. Import InflA_Len1. Import InflA_Len2. From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import InflA_Len3 InflA_Len4.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

Definition ilLT : cfg := ilSx [0x20c78] [].

Lemma opm1_term : forall op, 0 <= op < 256 -> (op = 0 \/ 16 <= op) -> 14 < (op + -1) mod 2 ^ 64.
Proof.
  intros op Hop [E|GE]; [rewrite E; change ((0 + -1) mod 2 ^ 64) with 18446744073709551615; lia|]. rewrite Z.mod_small by lia. lia.
Qed.
Lemma opm1_link : forall op, 1 <= op <= 15 -> (op + -1) mod 2 ^ 64 <= 14.
Proof. intros op Hop. rewrite Z.mod_small by lia. lia. Qed.

Section LenT.
  Variable v : icv.
  Hypothesis C : ictx v.

  Ltac open_lfacts HD :=
    destruct HD as (Hsane & Hwh & Hwn & Hwl & Hws & Hwb & CI & (extL & TL & HextL) & Hlofs & (extD & TD & HextD) & Hdofs).

  Definition ltpins : list (Z * expr) :=
    [(2, EVar 32%nat); (8, EVar 33%nat); (18, EVar 34%nat); (1, ELit 16209); (9, EAdd (EVar 37%nat) (EVar 38%nat));
     (25, EVar 40%nat); (12, EVar 36%nat); (31, EAdd (EVar 43%nat) (EVar 44%nat)); (21, EVar 41%nat);
     (7, EVar 45%nat); (11, EVar 46%nat); (19, ESub (EVar 45%nat) (ESub (EVar 41%nat) (EVar 46%nat))); (28, EVar 47%nat);
     (20, EVar 48%nat); (22, EVar 49%nat)].
  Definition ltvb : list (nat * Z) :=
    [(45%nat, 16); (46%nat, 64); (47%nat, 2 ^ 24); (48%nat, 2 ^ 32); (49%nat, 2 ^ 24)].

  Lemma len_T : forall s c r R M b1 h1 n1 last,
    is_mode s = LEN -> len_facts v s c -> RINV (cv_NI v) (cv_NO v) r -> is_back s = 0 ->
    1 <= code_op last <= 15 - is_lenbits s -> code_bits last = is_lenbits s -> 0 <= b1 < 64 ->
    (forall j, 0 <= j < 2 ^ code_op last ->
       term_ok LENS (15 - is_lenbits s) (cat (is_codes s) (is_lencode s) (code_val last + j)) = true) ->
    (exists ext, tab_ok LENS (cat (is_codes s) (is_lencode s)) (is_lenbits s) ext = true /\ code_val last + 2 ^ code_op last <= ext /\ ext <= cext (is_lencode s)) ->
    wrap32 (code_bits last + code_bits (lent2 s last (ir_hold r))) <= ir_bits r ->
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LX v (mkW s c r) -> LJE2 v s b1 h1 n1 last r R ->
    exists R' M' pc',
      msteps s6u_segs (mkst R (Z_to_bv 64 0x20c58) M s6u_rom) (mkst R' (Z_to_bv 64 pc') M' s6u_rom)
      /\ arm_post v (mkW s c r) M (len_res (lent2 s last (ir_hold r)) (is_back s + code_bits last) s c (rdrop r (code_bits last))) R' M' pc'.
  Proof.
    intros s c r R M b1 h1 n1 last Hmode HD RI Hbk LK LB Hb1 SUB (ext' & TL' & LXT & Hext') Hneed HM HRC HX HJ. pose proof HD as HD0. open_lfacts HD.
    pose proof HJ as X. unfold LJE2, LK2 in X.
    destruct X as ((HF & G9 & G13 & G15 & G30 & G7 & G29 & G28 & G11 & G16 & G14 & G17 & G5) & G22 & G12 & G31 & G20 & G18 & G19 & G21 & G23). open_fixc HF.
    pose proof G2 as P2. pose proof G27 as P27. pose proof G8 as P8. pose proof G9 as P9. pose proof G22 as P22. pose proof G12 as P12.
    open_ictx C. open_lmem HM. open_retc HRC. open_lx HX. open_rinv RI. pose proof CI as CI'. open_cinv CI. open_frame Mfr. unfold mapped in *.
    pose proof (tab_ok_root _ _ _ _ TL') as (Rt1 & Rt2 & Rt3).
    pose proof (code_val_range last) as Hlv. pose proof (cent_shr8_range last) as Hl8.
    pose proof (shiftr_BITSv_sub (ir_hold r) (code_bits last) (code_op last) ltac:(clear - Rt1 LB; lia) ltac:(clear - LK; lia)) as HJ2.
    set (J := code_val last + Z.shiftr (BITSv (ir_hold r) (code_bits last + code_op last)) (code_bits last)) in *.
    set (here := cat (is_codes s) (is_lencode s) J).
    assert (Ehere : lent2 s last (ir_hold r) = here) by reflexivity. rewrite Ehere in Hneed, G19, G21, G23 |- *.
    pose proof (SUB _ HJ2) as TE. change (cat _ _ _) with here in TE.
    destruct (term_ok_LENS _ _ TE) as (Bh & _).
    pose proof (code_bits_range here) as Hcb. pose proof (code_op_range here) as Hop. pose proof (code_val_range here) as Hval.
    pose proof (cent_range here) as Hcent. pose proof (cent_shr8_range here) as Hc8.
    rewrite wrap32_id in Hneed by (clear - Bh Rt1 LB Hcb; lia).
    arm_symexP (@nil (Z * expr)) ilLT 12%nat (@nil bool) [RVal (EAdd (EVar 33%nat) (ELit 7160))] ltpins ltvb v r
      [code_bits last; b1; cent last / 2 ^ 8; cent here; cent here / 2 ^ 8] NoVals F0
      (mkst R (Z_to_bv 64 0x20c58) M s6u_rom) R1 HR1 Hfr1 Hms1.
    all: try arm_side.
    all: match goal with |- ?G => idtac "LEFTLT" G end.
    pose proof (RINV_drop (cv_NI v) (cv_NO v) ltac:(clear - CI0; lia) ltac:(clear - CP0; lia) r (code_bits last) RI ltac:(clear - Hneed Bh Rt1 LB; lia)) as [EW RI'].
    unfold rdrop. rewrite EW.
    set (r' := irset_bits (irset_hold r (Z.shiftr (ir_hold r) (code_bits last))) (ir_bits r - code_bits last)) in *.
    set (M1 := wbytes M (zw (cv_S v + 7164)) (Z_to_le_bytes 4 (code_bits last))) in *.
    assert (NH : is_mode s <> HEAD) by (rewrite Hmode; cbv; discriminate).
    assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
    assert (Hput : 0 <= ir_put r <= cv_NO v) by (clear - Rpt0 Rpl Rlf0; lia).
    assert (HM1 : LMEM v (mkW (iset_back s (is_back s + code_bits last)) c r') M1).
    { rewrite Hbk, Z.add_0_l. apply (LMEM_regs v _ c r c r' M1); [| subst r'; reflexivity ..].
      apply (LMEM_store_scalar v C s c r _ M 7164 _ HM); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
      apply (is6_upd_back M (cv_S v) _ s _ Msc); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
    assert (HRC' : RETC v (mkW s c r') M1) by (subst M1; apply (RETC_regs v (mkW s c r)); [retc_tower C HRC | subst r'; reflexivity]).
    assert (HX' : LX v (mkW s c r')) by (apply (LX_step0 v s c r s c r' HX NH NB); subst r'; try reflexivity; [exact Xlive | exact Xret | exact Xmsg | bk_side]).
    symex_reg HR1 (25%bv : reg) as Q22. symex_reg HR1 (11%bv : reg) as Q11. symex_reg HR1 (29%bv : reg) as Q29. symex_reg HR1 (28%bv : reg) as Q28'. symex_reg HR1 (14%bv : reg) as Q14.
    rewrite cent_bits5 in Q22 by (clear - Rt1 LB; lia). rewrite zalu_srl_small in Q22 by (clear - Rhold64 Rt1 LB; lia).
    rewrite szwrap32_small in Q11 by (clear - Hneed Bh Rbits Rt1 LB; lia).
    rewrite cent_op in Q29.
    assert (HFR : LFREG v s r' here (is_back s + code_bits last) R1).
    { unfold LFREG. subst r'. cbn [ir_put ir_left ir_out ir_hold ir_bits ir_have ir_next irset_bits irset_hold].
      rewrite Z.shiftr_div_pow2 by (clear - Rt1 LB; lia). rewrite Hbk, Z.add_0_l.
      split; [lfixc_close Hfr1 HR1|].
      regs_via Hfr1; first [exact Q22 | rewrite Q11; f_equal; lia | exact Q14 | exact Q28' | exact Q29 | match goal with |- ?G => idtac "LFREG LEFT" G end]. }
    destruct (len_fin v C s c r' R1 M1 here (is_back s + code_bits last) (15 - is_lenbits s) Hmode HD0 RI' TE ltac:(clear - Rt1; lia)
                ltac:(subst r'; cbn; clear - Hneed; lia) ltac:(rewrite Hbk; clear - Rt1 LB; lia) HM1 HRC' HX' HFR) as (R' & M' & pc' & Hms2 & HPOST).
    exists R', M', pc'. split; [eapply msteps_trans; [| exact Hms2]; subst M1; by_run Hms1|].
    apply (arm_post_chain v (mkW s c r) (mkW (iset_back s (is_back s + code_bits last)) c r') M M1); [split; [reflexivity | split; reflexivity] | | exact HPOST].
    cbn [w_r]. subst r'. cbn [ir_put irset_bits irset_hold]. subst M1.
    apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r) M M); [apply MFRAME_refl | lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
  Qed.

  Definition lqpins : list (Z * expr) :=
    [(2, EVar 32%nat); (8, EVar 33%nat); (18, EVar 34%nat); (1, ELit 16209); (9, EAdd (EVar 37%nat) (EVar 38%nat));
     (25, EVar 40%nat); (12, EVar 36%nat); (17, EVar 36%nat); (5, EMul (ELit 8) (EVar 36%nat));
     (14, EAdd (EVar 43%nat) (EVar 44%nat)); (6, EAdd (EVar 43%nat) (EVar 44%nat)); (16, EVar 41%nat); (11, EVar 41%nat);
     (13, EVar 46%nat); (15, ELit 1); (20, EVar 47%nat); (28, EVar 48%nat); (7, EVar 49%nat)].
  Definition lqvb : list (nat * Z) :=
    [(45%nat, 2 ^ 15); (46%nat, 2 ^ 63); (47%nat, 2 ^ 32); (48%nat, 2 ^ 24); (49%nat, 16); (50%nat, 65536); (51%nat, 65536)].

  Lemma len_Q_term : forall s c r R M b0 h0 n0,
    is_mode s = LEN -> len_facts v s c -> RINV (cv_NI v) (cv_NO v) r -> is_back s = 0 ->
    let last := lent1 s (ir_hold r) in
    code_bits last <= ir_bits r -> term_ok LENS (is_lenbits s) last = true -> (code_op last = 0 \/ 16 <= code_op last) ->
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LX v (mkW s c r) -> LJE v s b0 h0 n0 r R ->
    exists R' M' pc',
      msteps s6u_segs (mkst R (Z_to_bv 64 0x20b50) M s6u_rom) (mkst R' (Z_to_bv 64 pc') M' s6u_rom)
      /\ arm_post v (mkW s c r) M (len_res last (is_back s) s c r) R' M' pc'.
  Proof.
    intros s c r R M b0 h0 n0 Hmode HD RI Hbk last Hlb TM OT HM HRC HX HJ. pose proof HD as HD0. open_lfacts HD.
    pose proof HJ as X. unfold LJE, LK1 in X.
    destruct X as ((HF & G9 & G13 & G29 & G15 & G18 & G24 & G25 & G30) & G22 & G12 & G17 & G5 & G14 & G6 & G16 & G11 & G19 & G28 & G7). open_fixc HF.
    pose proof G2 as P2. pose proof G27 as P27. pose proof G8 as P8. pose proof G9 as P9. pose proof G22 as P22. pose proof G12 as P12.
    open_ictx C. open_lmem HM. open_retc HRC. open_lx HX. pose proof RI as RI0. open_rinv RI. pose proof CI as CI'. open_cinv CI. open_frame Mfr. unfold mapped in *.
    pose proof (tab_ok_root _ _ _ _ TL) as (Rt1 & Rt2 & Rt3).
    pose proof (ctab6_range v (is_lencode s) C Hlofs) as [HA0 HA1].
    pose proof (ones_range15 (is_lenbits s) Rt1) as Hones.
    pose proof (code_bits_range last) as Hcb. pose proof (code_op_range last) as Hop. pose proof (code_val_range last) as Hval.
    pose proof (cent_range last) as Hcent. pose proof (cent_shr8_range last) as Hc8.
    destruct (term_ok_LENS _ _ TM) as (Bh & _).
    pose proof (opm1_term (code_op last) Hop OT) as OPM.
    arm_symexP (@nil (Z * expr)) ilLT 8%nat [true] (@nil (option expr)) lqpins lqvb v r
      [Z.ones (is_lenbits s); ctab6 v (is_lencode s); cent last; cent last / 2 ^ 8; code_bits last] NoVals F0
      (mkst R (Z_to_bv 64 0x20b50) M s6u_rom) R1 HR1 Hfr1 Hms1.
    all: rewrite ?cent_op.
    all: try arm_side.
    all: match goal with |- ?G => idtac "LEFTLQT" G end.
    symex_reg HR1 (7%bv : reg) as Q7. symex_reg HR1 (29%bv : reg) as Q29. rewrite cent_op in Q29.
    assert (HFR : LFREG v s r last (is_back s) R1).
    { unfold LFREG. split; [lfixc_close Hfr1 HR1|]. rewrite Hbk.
      regs_via Hfr1; first [exact Q7 | exact Q29 | match goal with |- ?G => idtac "LFREG1 LEFT" G end]. }
    destruct (len_fin v C s c r R1 M last (is_back s) (is_lenbits s) Hmode HD0 RI0 TM ltac:(clear - Rt1; lia) Hlb ltac:(rewrite Hbk; lia)
                ltac:(rewrite iset_back_self; exact HM) HRC HX HFR) as (R' & M' & pc' & Hms2 & HPOST).
    rewrite iset_back_self in HPOST.
    exists R', M', pc'. split; [eapply msteps_trans; [| exact Hms2]; by_run Hms1 | exact HPOST].
  Qed.
End LenT.
End FXG.
