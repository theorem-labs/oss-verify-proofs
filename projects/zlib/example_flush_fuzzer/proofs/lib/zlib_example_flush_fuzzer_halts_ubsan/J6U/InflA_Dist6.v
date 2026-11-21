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
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require InflDec6.

Module InflA_Dist1.
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

Definition ilD1 : cfg := ilSx [0x20d74; 0x20dd0] [AV (EAdd (EVar 43%nat) (EVar 44%nat)) 0 1 0 (EVar 44%nat)].

Section DistL1.
  Variable v : icv.
  Variables (s : inflate_state) (c : icall).
  Hypothesis C : ictx v.
  Variables (b0 h0 n0 : Z).
  Hypothesis Hb0 : 0 <= b0.
  Hypothesis Hn0 : 0 <= n0.
  Variable ext : Z.
  Hypothesis TD : tab_ok DISTS (cat (is_codes s) (is_distcode s)) (is_distbits s) ext = true.
  Hypothesis Hext : ext <= cext (is_distcode s).
  Hypothesis Hofs : cofs_ok (is_distcode s).
  Hypothesis CI : CINV (cv_NI v) (cv_NO v) c.

  Local Abbreviation db := (is_distbits s).
  Local Abbreviation A := (ctab6 v (is_distcode s)).
  Definition dent1 (h : Z) : Z := cat (is_codes s) (is_distcode s) (BITSv h db).

  Definition DK (r : iregs) (R : bvmap 5 word) : Prop :=
    LFIXc v R /\ getr R 9 = zw (cv_P0 v + ir_put r) /\ getr R 11 = zw A /\ getr R 29 = zw (Z.ones db) /\ getr R 13 = zw 1
    /\ getr R 19 = zw b0 /\ getr R 23 = zw h0 /\ getr R 26 = zw (cv_I0 v + n0) /\ getr R 31 = zw (h0 * 2 ^ 32).
  Definition DJS (r : iregs) (R : bvmap 5 word) : Prop :=
    DK r R /\ getr R 25 = zw (ir_hold r) /\ getr R 12 = zw (ir_have r) /\ getr R 16 = zw (ir_have r) /\ getr R 17 = zw (8 * ir_have r)
    /\ getr R 5 = zw (cv_I0 v + ir_next r) /\ getr R 6 = zw (cv_I0 v + ir_next r) /\ getr R 15 = zw (ir_bits r) /\ getr R 14 = zw (ir_bits r)
    /\ b0 + 8 * (h0 - ir_have r) = ir_bits r /\ n0 + (h0 - ir_have r) = ir_next r /\ 0 <= h0 - ir_have r.
  Definition DJE (r : iregs) (R : bvmap 5 word) : Prop :=
    DK r R /\ getr R 25 = zw (ir_hold r) /\ getr R 12 = zw (ir_have r) /\ getr R 16 = zw (ir_have r) /\ getr R 17 = zw (8 * ir_have r)
    /\ getr R 5 = zw (cv_I0 v + ir_next r) /\ getr R 6 = zw (cv_I0 v + ir_next r) /\ getr R 15 = zw (ir_bits r) /\ getr R 14 = zw (ir_bits r)
    /\ getr R 30 = zw (cent (dent1 (ir_hold r))) /\ getr R 7 = zw (cent (dent1 (ir_hold r)) / 2 ^ 8) /\ getr R 28 = zw (code_bits (dent1 (ir_hold r))).

  Ltac open_djs HJ :=
    let X := fresh in pose proof HJ as X; unfold DJS, DK in X;
    destruct X as ((HF & G9 & G11 & G29 & G13 & G18 & G24 & G25 & G31) & G22 & G12 & G16 & G17 & G5 & G6 & G15 & G14 & Ib & In & Ih); open_fixc HF.

  Definition dpins : list (Z * expr) :=
    [(2, EVar 32%nat); (8, EVar 33%nat); (18, EVar 34%nat); (1, ELit 16209); (9, EAdd (EVar 37%nat) (EVar 38%nat));
     (11, EVar 46%nat); (29, EVar 45%nat); (13, ELit 1);
     (25, EVar 40%nat); (12, EVar 36%nat); (16, EVar 36%nat); (17, EMul (ELit 8) (EVar 36%nat));
     (5, EAdd (EVar 43%nat) (EVar 44%nat)); (6, EAdd (EVar 43%nat) (EVar 44%nat)); (15, EVar 41%nat); (14, EVar 41%nat);
     (19, EVar 47%nat); (23, EVar 48%nat); (26, EAdd (EVar 43%nat) (EVar 49%nat)); (31, EShl (EVar 48%nat) 32)].
  Definition dvb : list (nat * Z) :=
    [(45%nat, 2 ^ 15); (46%nat, 2 ^ 63); (47%nat, 2 ^ 63); (48%nat, 2 ^ 31); (49%nat, 2 ^ 31); (50%nat, 65536); (51%nat, 65536)].

  Ltac d1_side Hby Rbits Rhold Hb64 Rt1 Rt2 TAB HA0 HA1 Hext :=
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

  Ltac dj_close HR Hfr r Hby Rbits Rhold Hb64 Hh Rnh Rnx0 CI0 :=
    let Q22 := fresh in let Q12 := fresh in let Q16 := fresh in let Q17 := fresh in let Q5 := fresh in let Q6 := fresh in
    let Q15 := fresh in let Q14 := fresh in let Q30 := fresh in let Q7 := fresh in let Q28 := fresh in
    symex_reg HR (25%bv : reg) as Q22; symex_reg HR (12%bv : reg) as Q12; symex_reg HR (16%bv : reg) as Q16; symex_reg HR (17%bv : reg) as Q17;
    symex_reg HR (5%bv : reg) as Q5; symex_reg HR (6%bv : reg) as Q6; symex_reg HR (15%bv : reg) as Q15; symex_reg HR (14%bv : reg) as Q14;
    symex_reg HR (30%bv : reg) as Q30; symex_reg HR (7%bv : reg) as Q7; symex_reg HR (28%bv : reg) as Q28;
    cbn [famA] in Q22; rewrite bmod_get in Q22 by exact Hby;
    rewrite ?cent_reasm in Q30; rewrite ?cent_reasm in Q7; rewrite ?cent_reasm, ?cent_bits in Q28;
    unfold DJS, DJE, DK, pull1; cbn [ir_next ir_have ir_put ir_left ir_hold ir_bits ir_in ir_out ir_ret];
    repeat match goal with |- _ /\ _ => split end;
    first [ assumption
          | lazymatch goal with |- LFIXc _ _ => lfixc_close Hfr HR end
          | lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr n eq_refl); assumption end
          | rewrite Q22; rewrite zalu_sll_small; [f_equal; lia | clear - Hby; lia | clear - Rbits Hb64; lia
              | clear - Hby Rbits Hb64 Rhold; pose proof (pull_hold_lt _ _ _ Rhold (proj1 Rbits) Hby); assert (2 ^ (ir_bits r + 8) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia); lia]
          | rewrite Q12; rewrite ?szwrap32_small by (clear - Hh Rnh Rnx0 CI0; lia); f_equal; lia
          | rewrite Q16; f_equal; lia
          | rewrite Q17; f_equal; lia
          | rewrite Q5; f_equal; lia
          | rewrite Q6; f_equal; lia
          | rewrite Q15; f_equal; lia
          | rewrite Q14; f_equal; lia
          | rewrite Q30; f_equal; f_equal; f_equal; lia
          | rewrite Q7; f_equal; f_equal; f_equal; f_equal; lia
          | rewrite Q28; f_equal; f_equal; f_equal; lia
          | lia
          | match goal with |- ?G => idtac "DJ LEFT" G end ].

  Ltac d1_prep C TD Hofs HM Rt1 Rt2 Rt3 HA0 HA1 TAB Hones :=
    pose proof (tab_ok_root _ _ _ _ TD) as (Rt1 & Rt2 & Rt3);
    pose proof (ctab6_range v (is_distcode s) C Hofs) as [HA0 HA1];
    pose proof (ctab6_cells v s c _ _ (is_distcode s) C HM Hofs) as TAB;
    pose proof (ones_range15 db Rt1) as Hones.

  Lemma dist1_step_H : forall r R M,
    LMEM v (mkW s c r) M -> DJS r R -> RINV (cv_NI v) (cv_NO v) r -> 0 < ir_have r -> ir_bits r + 8 < 64 ->
    ir_bits r + 8 < code_bits (dent1 (ir_hold (pull1 c r))) ->
    exists R1, msteps s6u_segs (mkst R (Z_to_bv 64 0x20d74) M s6u_rom) (mkst R1 (Z_to_bv 64 0x20d74) M s6u_rom)
               /\ DJS (pull1 c r) R1.
  Proof.
    intros r R M HM HJ RI Hh Hb64 Hb. open_djs HJ.
    open_ictx C. open_lmem HM. open_rinv RI. open_cinv CI. unfold mapped in *.
    d1_prep C TD Hofs HM Rt1 Rt2 Rt3 HA0 HA1 TAB Hones.
    assert (Hby : 0 <= arr_get (ic_input c) (ir_next r) < 256) by (apply Cinb; clear - Hh Rnx0 Rhv0 Rnh; lia).
    pose proof (cells_bmod _ _ _ _ Minp Cinb) as Hin0.
    pose proof (fun j (_ : 0 <= j < cv_NI v) => bmod_range (arr_get (ic_input c)) j) as Hinr.
    assert (Hh0 : 0 <= h0 < 2 ^ 31) by (clear - Ih In Hn0 Hh Rnh Rnx0 Rhv0 CI0; lia).
    pose proof (code_bits_range (dent1 (ir_hold (pull1 c r)))) as Hcb.
    pose proof (code_val_range (dent1 (ir_hold (pull1 c r)))) as Hcv.
    pose proof (clo_range (dent1 (ir_hold (pull1 c r)))) as Hclo.
    unfold dent1 in Hb, Hcb, Hcv, Hclo |- *. cbn [ir_hold pull1] in Hb, Hcb, Hcv, Hclo |- *.
    arm_symexP (@nil (Z * expr)) ilD1 34%nat [false; false; false; false; true; false] [RVal (EVar 50%nat); RVal (EVar 51%nat)] dpins dvb v r
      [Z.ones db; A; b0; h0; n0;
       code_val (cat (is_codes s) (is_distcode s) (BITSv (ir_hold r + arr_get (ic_input c) (ir_next r) * 2 ^ ir_bits r) db));
       clo (cat (is_codes s) (is_distcode s) (BITSv (ir_hold r + arr_get (ic_input c) (ir_next r) * 2 ^ ir_bits r) db))]
      NoVals (famA c s)
      (mkst R (Z_to_bv 64 0x20d74) M s6u_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    all: d1_side Hby Rbits Rhold Hb64 Rt1 Rt2 TAB HA0 HA1 Hext.
    all: match goal with |- ?G => idtac "LEFTD1H" G end.
    exists R1. split; [by_run Hms|].
    dj_close HR1 Hfr r Hby Rbits Rhold Hb64 Hh Rnh Rnx0 CI0.
  Qed.

  Lemma dist1_step_E : forall r R M,
    LMEM v (mkW s c r) M -> DJS r R -> RINV (cv_NI v) (cv_NO v) r -> 0 < ir_have r -> ir_bits r + 8 < 64 ->
    code_bits (dent1 (ir_hold (pull1 c r))) <= ir_bits r + 8 ->
    exists R1, msteps s6u_segs (mkst R (Z_to_bv 64 0x20d74) M s6u_rom) (mkst R1 (Z_to_bv 64 0x20dd0) M s6u_rom)
               /\ DJE (pull1 c r) R1.
  Proof.
    intros r R M HM HJ RI Hh Hb64 Hb. open_djs HJ.
    open_ictx C. open_lmem HM. open_rinv RI. open_cinv CI. unfold mapped in *.
    d1_prep C TD Hofs HM Rt1 Rt2 Rt3 HA0 HA1 TAB Hones.
    assert (Hby : 0 <= arr_get (ic_input c) (ir_next r) < 256) by (apply Cinb; clear - Hh Rnx0 Rhv0 Rnh; lia).
    pose proof (cells_bmod _ _ _ _ Minp Cinb) as Hin0.
    pose proof (fun j (_ : 0 <= j < cv_NI v) => bmod_range (arr_get (ic_input c)) j) as Hinr.
    assert (Hh0 : 0 <= h0 < 2 ^ 31) by (clear - Ih In Hn0 Hh Rnh Rnx0 Rhv0 CI0; lia).
    pose proof (code_bits_range (dent1 (ir_hold (pull1 c r)))) as Hcb.
    pose proof (code_val_range (dent1 (ir_hold (pull1 c r)))) as Hcv.
    pose proof (clo_range (dent1 (ir_hold (pull1 c r)))) as Hclo.
    unfold dent1 in Hb, Hcb, Hcv, Hclo |- *. cbn [ir_hold pull1] in Hb, Hcb, Hcv, Hclo |- *.
    arm_symexP (@nil (Z * expr)) ilD1 34%nat [false; false; false; false; true; true] [RVal (EVar 50%nat); RVal (EVar 51%nat)] dpins dvb v r
      [Z.ones db; A; b0; h0; n0;
       code_val (cat (is_codes s) (is_distcode s) (BITSv (ir_hold r + arr_get (ic_input c) (ir_next r) * 2 ^ ir_bits r) db));
       clo (cat (is_codes s) (is_distcode s) (BITSv (ir_hold r + arr_get (ic_input c) (ir_next r) * 2 ^ ir_bits r) db))]
      NoVals (famA c s)
      (mkst R (Z_to_bv 64 0x20d74) M s6u_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    all: d1_side Hby Rbits Rhold Hb64 Rt1 Rt2 TAB HA0 HA1 Hext.
    all: match goal with |- ?G => idtac "LEFTD1E" G end.
    exists R1. split; [by_run Hms|].
    dj_close HR1 Hfr r Hby Rbits Rhold Hb64 Hh Rnh Rnx0 CI0.
  Qed.

  Lemma dist1_dry : forall r R M,
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> DJS r R -> RINV (cv_NI v) (cv_NO v) r -> ir_have r = 0 ->
    exists R1, msteps s6u_segs (mkst R (Z_to_bv 64 0x20d74) M s6u_rom) (mkst R1 (Z_to_bv 64 pc6_leave) M s6u_rom)
               /\ LREG_leave v (mkW s c r) R1.
  Proof.
    intros r R M HM HRC HJ RI Hh. open_djs HJ.
    open_ictx C. open_lmem HM. open_frame Mfr. open_retc HRC. open_rinv RI. open_cinv CI. unfold mapped in *.
    d1_prep C TD Hofs HM Rt1 Rt2 Rt3 HA0 HA1 TAB Hones.
    assert (Hh0 : 0 <= h0 < 2 ^ 31) by (clear - Ih In Hn0 Hh Rnh Rnx0 Rhv0 CI0; lia).
    arm_symexP (@nil (Z * expr)) ilD1 16%nat [true] [RVal (EVar 50%nat); RVal (EVar 35%nat)] dpins
      [(45%nat, 2 ^ 15); (46%nat, 2 ^ 63); (47%nat, 2 ^ 63); (48%nat, 2 ^ 31); (49%nat, 2 ^ 31); (50%nat, 2 ^ 64)] v r
      [Z.ones db; A; b0; h0; n0; ir_ret r mod 2 ^ 64] NoVals (famA c s)
      (mkst R (Z_to_bv 64 0x20d74) M s6u_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    all: match goal with |- ?G => idtac "LEFTD1D" G end.
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
End DistL1.
End FXG.
End InflA_Dist1.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require InflA_Dist2 InflA_Dist3.

Module InflA_Dist4.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateGarbBase OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvTab.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.CatExec OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.CatSim OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.SeqExec OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.StoreOk OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Hoare OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.StepTac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymEx2Expr OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymEx2 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymEx2Tac OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.MemRel OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymAux OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.RomRead.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.Prog OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateFast OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateArms OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.Inflate OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInv OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvKit OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvRun.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U.Segs6u.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S.ISLayout OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S.InflMem.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.IS6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflRod6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflCtx6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflArmLib6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflArmLib6b OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflNeed6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflA_Distext3.InflA_Distext2 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflA_Distext3.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflDec6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflA_Dist2 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflA_Dist3.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

Definition ilDT : cfg := ilSx [0x20f04] [].

Section DistT.
  Variable v : icv.
  Hypothesis C : ictx v.

  Ltac open_dfacts HD :=
    destruct HD as (Hsane & Hlen & Hback & Hwh & Hwn & Hwl & Hws & Hwb & CI & (ext & TD & Hext) & Hofs).

  Definition tpins : list (Z * expr) :=
    [(2, EVar 32%nat); (8, EVar 33%nat); (18, EVar 34%nat); (1, ELit 16209); (9, EAdd (EVar 37%nat) (EVar 38%nat));
     (25, EVar 40%nat); (12, EVar 36%nat); (26, EAdd (EVar 43%nat) (EVar 44%nat)); (20, EVar 41%nat);
     (28, EVar 45%nat); (14, EVar 46%nat); (19, ESub (EVar 45%nat) (ESub (EVar 41%nat) (EVar 46%nat))); (7, EVar 47%nat);
     (30, EVar 48%nat); (22, EVar 49%nat); (21, EVar 50%nat)].
  Definition tvb : list (nat * Z) :=
    [(45%nat, 16); (46%nat, 2 ^ 63); (47%nat, 2 ^ 24); (48%nat, 2 ^ 32); (49%nat, 2 ^ 24); (50%nat, 256); (51%nat, 2 ^ 32)].

  Lemma dist_T : forall s c r R M b1 h1 n1 last,
    is_mode s = DIST -> dist_facts v s c -> RINV (cv_NI v) (cv_NO v) r ->
    1 <= code_op last <= 15 - is_distbits s -> code_bits last = is_distbits s -> 0 <= b1 < 64 ->
    (forall j, 0 <= j < 2 ^ code_op last ->
       term_ok DISTS (15 - is_distbits s) (cat (is_codes s) (is_distcode s) (code_val last + j)) = true) ->
    (exists ext, tab_ok DISTS (cat (is_codes s) (is_distcode s)) (is_distbits s) ext = true /\ code_val last + 2 ^ code_op last <= ext /\ ext <= cext (is_distcode s)) ->
    wrap32 (code_bits last + code_bits (dent2 s last (ir_hold r))) <= ir_bits r ->
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LX v (mkW s c r) -> DJE2 v s b1 h1 n1 last r R ->
    exists R' M' pc',
      msteps s6u_segs (mkst R (Z_to_bv 64 0x20edc) M s6u_rom) (mkst R' (Z_to_bv 64 pc') M' s6u_rom)
      /\ arm_post v (mkW s c r) M (dist_res (dent2 s last (ir_hold r)) (is_back s + code_bits last) s c (rdrop r (code_bits last))) R' M' pc'.
  Proof.
    intros s c r R M b1 h1 n1 last Hmode HD RI LK LB Hb1 SUB (ext' & TD' & LXT & Hext') Hneed HM HRC HX HJ. pose proof HD as HD0. open_dfacts HD.
    pose proof HJ as X. unfold DJE2, DK2 in X.
    destruct X as ((HF & G9 & G11 & G13 & G31 & G28 & G29 & G7 & G14 & G15 & G5 & G16 & G17) & G22 & G12 & G25 & G19 & G18 & G30 & G21 & G20 & G23). open_fixc HF.
    pose proof G2 as P2. pose proof G27 as P27. pose proof G8 as P8. pose proof G9 as P9. pose proof G22 as P22. pose proof G12 as P12. pose proof G25 as P25.
    open_ictx C. open_lmem HM. open_retc HRC. open_lx HX. open_rinv RI. pose proof CI as CI'. open_cinv CI. open_frame Mfr. unfold mapped in *.
    pose proof (tab_ok_root _ _ _ _ TD') as (Rt1 & Rt2 & Rt3).
    pose proof (code_val_range last) as Hlv. pose proof (cent_shr8_range last) as Hl8.
    pose proof (shiftr_BITSv_sub (ir_hold r) (code_bits last) (code_op last) ltac:(clear - Rt1 LB; lia) ltac:(clear - LK; lia)) as HJ2.
    set (J := code_val last + Z.shiftr (BITSv (ir_hold r) (code_bits last + code_op last)) (code_bits last)) in *.
    set (here := cat (is_codes s) (is_distcode s) J).
    assert (Ehere : dent2 s last (ir_hold r) = here) by reflexivity. rewrite Ehere in Hneed, G30, G21, G20, G23 |- *.
    pose proof (SUB _ HJ2) as TE. change (cat _ _ _) with here in TE.
    destruct (term_ok_DISTS _ _ TE) as (Bh & _).
    pose proof (code_bits_range here) as Hcb. pose proof (code_op_range here) as Hop. pose proof (code_val_range here) as Hval.
    pose proof (cent_range here) as Hcent. pose proof (cent_shr8_range here) as Hc8.
    rewrite wrap32_id in Hneed by (clear - Bh Rt1 LB Hcb; lia).
    pose proof (is6_back _ _ _ _ Msc) as C7148.
    assert (Hbk : 0 <= is_back s <= 128) by (destruct Xbk as [_ XD]; exact (XD Hmode)).
    assert (Hbm : is_back s mod 2 ^ 32 = is_back s) by (apply Z.mod_small; lia).
    arm_symexP (@nil (Z * expr)) ilDT 14%nat [false] [RVal (EAdd (EVar 33%nat) (ELit 7160)); RVal (EVar 51%nat)] tpins tvb v r
      [code_bits last; b1; cent last / 2 ^ 8; cent here; cent here / 2 ^ 8; code_bits here; is_back s mod 2 ^ 32] NoVals F0
      (mkst R (Z_to_bv 64 0x20edc) M s6u_rom) R1 HR1 Hfr1 Hms1.
    all: try arm_side.
    all: match goal with |- ?G => idtac "LEFTDT" G end.
    rewrite ?Hbm, ?(szwrap32_small (is_back s)) in Hms1 by (clear - Hbk; lia).
    pose proof (RINV_drop (cv_NI v) (cv_NO v) ltac:(clear - CI0; lia) ltac:(clear - CP0; lia) r (code_bits last) RI ltac:(clear - Hneed Bh Rt1 LB; lia)) as [EW RI'].
    unfold rdrop. rewrite EW.
    set (r' := irset_bits (irset_hold r (Z.shiftr (ir_hold r) (code_bits last))) (ir_bits r - code_bits last)) in *.
    set (M1 := wbytes M (zw (cv_S v + 7164)) (Z_to_le_bytes 4 (is_back s + code_bits last))) in *.
    assert (NH : is_mode s <> HEAD) by (rewrite Hmode; cbv; discriminate).
    assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
    assert (Hput : 0 <= ir_put r <= cv_NO v) by (clear - Rpt0 Rpl Rlf0; lia).
    assert (HM1 : LMEM v (mkW (iset_back s (is_back s + code_bits last)) c r') M1).
    { apply (LMEM_regs v _ c r c r' M1); [| subst r'; reflexivity ..].
      apply (LMEM_store_scalar v C s c r _ M 7164 _ HM); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
      apply (is6_upd_back M (cv_S v) _ s _ Msc); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
    assert (HRC' : RETC v (mkW s c r') M1) by (subst M1; apply (RETC_regs v (mkW s c r)); [retc_tower C HRC | subst r'; reflexivity]).
    assert (HX' : LX v (mkW s c r')) by (apply (LX_step0 v s c r s c r' HX NH NB); subst r'; try reflexivity; [exact Xlive | exact Xret | exact Xmsg | bk_side]).
    symex_reg HR1 (25%bv : reg) as Q22. symex_reg HR1 (14%bv : reg) as Q14. symex_reg HR1 (29%bv : reg) as Q29.
    rewrite cent_bits5 in Q22 by (clear - Rt1 LB; lia). rewrite zalu_srl_small in Q22 by (clear - Rhold64 Rt1 LB; lia).
    rewrite szwrap32_small in Q14 by (clear - Hneed Bh Rbits Rt1 LB; lia).
    rewrite cent_op in Q29.
    assert (HFR : FREG v s r' here R1).
    { unfold FREG. subst r'. cbn [ir_put ir_left ir_out ir_hold ir_bits ir_have ir_next irset_bits irset_hold].
      rewrite Z.shiftr_div_pow2 by (clear - Rt1 LB; lia).
      split; [lfixc_close Hfr1 HR1|].
      regs_via Hfr1; first [exact Q22 | rewrite Q14; f_equal; lia | exact Q29 | match goal with |- ?G => idtac "FREG LEFT" G end]. }
    destruct (dist_fin v C s c r' R1 M1 here (is_back s + code_bits last) (15 - is_distbits s) Hmode HD0 RI' TE
                ltac:(subst r'; cbn; clear - Hneed; lia) ltac:(clear - Hbk Rt1 LB; lia) HM1 HRC' HX' HFR) as (R' & M' & pc' & Hms2 & HPOST).
    exists R', M', pc'. split; [eapply msteps_trans; [| exact Hms2]; subst M1; by_run Hms1|].
    apply (arm_post_chain v (mkW s c r) (mkW (iset_back s (is_back s + code_bits last)) c r') M M1); [split; [reflexivity | split; reflexivity] | | exact HPOST].
    cbn [w_r]. subst r'. cbn [ir_put irset_bits irset_hold]. subst M1.
    apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r) M M); [apply MFRAME_refl | lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
  Qed.
End DistT.
End FXG.
End InflA_Dist4.

Module InflA_Dist5.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateGarbBase OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvTab.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.CatExec OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.CatSim OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.SeqExec OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.StoreOk OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Hoare OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.StepTac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymEx2Expr OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymEx2 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymEx2Tac OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.MemRel OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymAux OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.RomRead.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.Prog OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateFast OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateArms OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.Inflate OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInv OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvKit OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvRun.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U.Segs6u.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S.ISLayout OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S.InflMem.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.IS6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflRod6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflCtx6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflArmLib6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflArmLib6b OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflNeed6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflA_Distext3.InflA_Distext2 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflA_Distext3.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflDec6 InflA_Dist1 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflA_Dist2 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflA_Dist3.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.


Definition dist_after1 (s0 : inflate_state) (last : Z) : AM unit :=
  (do here <- (if Z.land (code_op last) 240 =? 0 then
                 let last' := last in
                 do here <- DECODE2 (is_distcode s0) last' ;
                 DROPBITS (code_bits last') ;; add_back ivar_ref (code_bits last') ;; aret here
               else aret last) ;
   DROPBITS (code_bits here) ;; add_back ivar_ref (code_bits here) ;;
   if negb (Z.land (code_op here) 64 =? 0) then go_bad MSG_invalid_distance_code
   else us (fun s => iset_extra (iset_offset s (code_val here)) (Z.land (code_op here) 15)) ;; set_mode DISTEXT ;; arm_DISTEXT ivar_ref)%am.

Lemma arm_DIST_dec1 : forall s c r,
  arm_DIST ivar_ref (mkW s c r)
  = match DECODE1 (is_distcode s) (is_distbits s) (mkW s c r) with
    | ARun last w1 => dist_after1 s last w1 | ALeave w1 => ALeave w1 | ARet rc w1 => ARet rc w1 end.
Proof. intros s c r. unfold arm_DIST. mstep1 (@gs_eq inflate_state). rewrite abind_run. reflexivity. Qed.

Lemma dist_after1_term : forall s last c r,
  (Z.land (code_op last) 240 =? 0) = false -> dist_after1 s last (mkW s c r) = dist_res last (is_back s) s c r.
Proof.
  intros s last c r E240. unfold dist_after1. rewrite E240. mstep1 (@aret_eq Z).
  mstep1 DROPBITS_eq. rewrite abind_run, add_back_eq. cbn [iv_aux ivar_ref bkv].
  unfold dist_res, rdrop. destruct (negb (Z.land (code_op last) 64 =? 0)).
  - rewrite go_bad_eq. irnorm. reflexivity.
  - mstep1 us_eq. mstep1 set_mode_eq. irnorm. reflexivity.
Qed.

Lemma dist_after1_link : forall s last c r here r2,
  (Z.land (code_op last) 240 =? 0) = true ->
  DECODE2 (is_distcode s) last (mkW s c r) = ARun here (mkW s c r2) ->
  dist_after1 s last (mkW s c r) = dist_res here (is_back s + code_bits last) s c (rdrop r2 (code_bits last)).
Proof.
  intros s last c r here r2 E240 HD2. unfold dist_after1. rewrite E240. rewrite abind_run. rewrite abind_run, HD2.
  mstep1 DROPBITS_eq. rewrite abind_run, add_back_eq. cbn [iv_aux ivar_ref bkv]. rewrite aret_eq.
  mstep1 DROPBITS_eq. rewrite abind_run, add_back_eq. cbn [iv_aux ivar_ref bkv is_back iset_back].
  unfold dist_res, rdrop. irnorm. rewrite iset_back_back, swrap32_add_l.
  destruct (negb (Z.land (code_op here) 64 =? 0)).
  - rewrite go_bad_eq. cbn [is_back iset_back]. reflexivity.
  - mstep1 us_eq. mstep1 set_mode_eq. reflexivity.
Qed.

Lemma dist_after1_leave2 : forall s last c r w2,
  (Z.land (code_op last) 240 =? 0) = true ->
  DECODE2 (is_distcode s) last (mkW s c r) = ALeave w2 -> dist_after1 s last (mkW s c r) = ALeave w2.
Proof. intros s last c r w2 E240 HD2. unfold dist_after1. rewrite E240. rewrite abind_run. rewrite abind_run, HD2. reflexivity. Qed.


Definition ilDQ : cfg := ilSx [0x20f04; 0x20e64; 0x20e68; 0x20edc] [].

Section DistQ.
  Variable v : icv.
  Hypothesis C : ictx v.

  Ltac open_dfacts HD :=
    destruct HD as (Hsane & Hlen & Hback & Hwh & Hwn & Hwl & Hws & Hwb & CI & (ext & TD & Hext) & Hofs).

  Definition qpins : list (Z * expr) :=
    [(2, EVar 32%nat); (8, EVar 33%nat); (18, EVar 34%nat); (1, ELit 16209); (9, EAdd (EVar 37%nat) (EVar 38%nat));
     (25, EVar 40%nat); (12, EVar 36%nat); (16, EVar 36%nat); (17, EMul (ELit 8) (EVar 36%nat));
     (5, EAdd (EVar 43%nat) (EVar 44%nat)); (6, EAdd (EVar 43%nat) (EVar 44%nat)); (15, EVar 41%nat); (14, EVar 41%nat);
     (11, EVar 46%nat); (13, ELit 1); (30, EVar 47%nat); (7, EVar 48%nat); (28, EVar 49%nat)].
  Definition qvb : list (nat * Z) :=
    [(45%nat, 2 ^ 15); (46%nat, 2 ^ 63); (47%nat, 2 ^ 32); (48%nat, 2 ^ 24); (49%nat, 16); (50%nat, 65536); (51%nat, 65536)].

  Lemma dist_Q_term : forall s c r R M b0 h0 n0,
    is_mode s = DIST -> dist_facts v s c -> RINV (cv_NI v) (cv_NO v) r ->
    let last := dent1 s (ir_hold r) in
    code_bits last <= ir_bits r -> term_ok DISTS (is_distbits s) last = true -> 16 <= code_op last ->
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LX v (mkW s c r) -> DJE v s b0 h0 n0 r R ->
    exists R' M' pc',
      msteps s6u_segs (mkst R (Z_to_bv 64 0x20dd0) M s6u_rom) (mkst R' (Z_to_bv 64 pc') M' s6u_rom)
      /\ arm_post v (mkW s c r) M (dist_res last (is_back s) s c r) R' M' pc'.
  Proof.
    intros s c r R M b0 h0 n0 Hmode HD RI last Hlb TM O16 HM HRC HX HJ. pose proof HD as HD0. open_dfacts HD.
    pose proof HJ as X. unfold DJE, DK in X.
    destruct X as ((HF & G9 & G11 & G29 & G13 & G18 & G24 & G25 & G31) & G22 & G12 & G16 & G17 & G5 & G6 & G15 & G14 & G30 & G7 & G28). open_fixc HF.
    pose proof G2 as P2. pose proof G27 as P27. pose proof G8 as P8. pose proof G9 as P9. pose proof G22 as P22. pose proof G12 as P12.
    open_ictx C. open_lmem HM. open_retc HRC. open_lx HX. pose proof RI as RI0. open_rinv RI. pose proof CI as CI'. open_cinv CI. open_frame Mfr. unfold mapped in *.
    pose proof (tab_ok_root _ _ _ _ TD) as (Rt1 & Rt2 & Rt3).
    pose proof (ctab6_range v (is_distcode s) C Hofs) as [HA0 HA1].
    pose proof (ones_range15 (is_distbits s) Rt1) as Hones.
    pose proof (code_bits_range last) as Hcb. pose proof (code_op_range last) as Hop. pose proof (code_val_range last) as Hval.
    pose proof (cent_range last) as Hcent. pose proof (cent_shr8_range last) as Hc8.
    destruct (term_ok_DISTS _ _ TM) as (Bh & _).
    arm_symexP (@nil (Z * expr)) ilDQ 9%nat [true] (@nil (option expr)) qpins qvb v r
      [Z.ones (is_distbits s); ctab6 v (is_distcode s); cent last; cent last / 2 ^ 8; code_bits last] NoVals F0
      (mkst R (Z_to_bv 64 0x20dd0) M s6u_rom) R1 HR1 Hfr1 Hms1.
    all: rewrite ?cent_op.
    all: try arm_side.
    all: match goal with |- ?G => idtac "LEFTQT" G end.
    symex_reg HR1 (22%bv : reg) as Q21. symex_reg HR1 (21%bv : reg) as Q20. symex_reg HR1 (29%bv : reg) as Q29. symex_reg HR1 (26%bv : reg) as Q25.
    rewrite cent_op in Q29.
    assert (HFR : FREG v s r last R1).
    { unfold FREG. split; [lfixc_close Hfr1 HR1|].
      regs_via Hfr1; first [exact Q21 | exact Q20 | exact Q29 | exact Q25 | match goal with |- ?G => idtac "FREG1 LEFT" G end]. }
    assert (Hbk : 0 <= is_back s <= 128) by (destruct Xbk as [_ XD]; exact (XD Hmode)).
    destruct (dist_fin v C s c r R1 M last (is_back s) (is_distbits s) Hmode HD0 RI0 TM Hlb ltac:(clear - Hbk; lia)
                ltac:(rewrite iset_back_self; exact HM) HRC HX HFR) as (R' & M' & pc' & Hms2 & HPOST).
    rewrite iset_back_self in HPOST.
    exists R', M', pc'. split; [eapply msteps_trans; [| exact Hms2]; by_run Hms1 | exact HPOST].
  Qed.
End DistQ.
End FXG.
End InflA_Dist5.

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
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import InflDec6. Import InflA_Dist1. From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import InflA_Dist2 InflA_Dist3. Import InflA_Dist4. Import InflA_Dist5.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

Lemma cent_op4 : forall v, cent v mod 2 ^ 4 = code_op v mod 2 ^ 4.
Proof.
  intros v. unfold cent. rewrite code_op_eq. apply Z.bits_inj'. intros n Hn. change 256 with (2 ^ 8). change 4294967296 with (2 ^ 32).
  destruct (Z_lt_le_dec n 4) as [L|G].
  - rewrite !Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Definition ilDL : cfg := ilDQ.

Section DistQL.
  Variable v : icv.
  Hypothesis C : ictx v.

  Ltac open_dfacts HD :=
    destruct HD as (Hsane & Hlen & Hback & Hwh & Hwn & Hwl & Hws & Hwb & CI & (ext & TD & Hext) & Hofs).

  Definition QREG (s : inflate_state) (r : iregs) (last here J2 : Z) (R : bvmap 5 word) : Prop :=
    LFIXc v R /\ getr R 9 = zw (cv_P0 v + ir_put r)
    /\ getr R 25 = zw (ir_hold r) /\ getr R 12 = zw (ir_have r) /\ getr R 26 = zw (cv_I0 v + ir_next r) /\ getr R 6 = zw (cv_I0 v + ir_next r)
    /\ getr R 20 = zw (ir_bits r) /\ getr R 19 = zw (code_bits last) /\ getr R 14 = zw (ir_bits r) /\ getr R 15 = zw (ir_bits r)
    /\ getr R 5 = zw (cv_I0 v + ir_next r) /\ getr R 16 = zw (ir_have r) /\ getr R 17 = zw (8 * ir_have r)
    /\ getr R 11 = zw (ctab6 v (is_distcode s)) /\ getr R 13 = zw 1
    /\ getr R 31 = zw (Z.ones (code_bits last + code_op last)) /\ getr R 28 = zw (code_bits last) /\ getr R 29 = zw (code_val last)
    /\ getr R 7 = zw (cent last / 2 ^ 8)
    /\ getr R 30 = zw (cent here) /\ getr R 22 = zw (cent here / 2 ^ 8) /\ getr R 21 = zw (code_bits here)
    /\ getr R 23 = zw (code_bits here + code_bits last).

  Definition lpins : list (Z * expr) :=
    [(2, EVar 32%nat); (8, EVar 33%nat); (18, EVar 34%nat); (1, ELit 16209); (9, EAdd (EVar 37%nat) (EVar 38%nat));
     (25, EVar 40%nat); (12, EVar 36%nat); (26, EAdd (EVar 43%nat) (EVar 44%nat)); (6, EAdd (EVar 43%nat) (EVar 44%nat));
     (20, EVar 41%nat); (19, EVar 46%nat); (14, EVar 41%nat); (15, EVar 41%nat);
     (5, EAdd (EVar 43%nat) (EVar 44%nat)); (16, EVar 36%nat); (17, EMul (ELit 8) (EVar 36%nat));
     (11, EVar 48%nat); (13, ELit 1); (31, EVar 45%nat); (28, EVar 46%nat); (29, EVar 47%nat); (7, EVar 49%nat);
     (30, EVar 50%nat); (22, EVar 51%nat); (21, EVar 52%nat); (23, EAdd (EVar 52%nat) (EVar 46%nat))].
  Definition lvb : list (nat * Z) :=
    [(45%nat, 2 ^ 15); (46%nat, 16); (47%nat, 2 ^ 16); (48%nat, 2 ^ 63); (49%nat, 2 ^ 24); (50%nat, 2 ^ 32); (51%nat, 2 ^ 24); (52%nat, 16)].

  Lemma dist_QL_pre : forall s c r R M b0 h0 n0,
    dist_facts v s c -> RINV (cv_NI v) (cv_NO v) r ->
    let last := dent1 s (ir_hold r) in
    let J2 := code_val last + Z.shiftr (BITSv (ir_hold r) (code_bits last + code_op last)) (code_bits last) in
    let here := cat (is_codes s) (is_distcode s) J2 in
    1 <= code_op last <= 15 - is_distbits s -> code_bits last = is_distbits s ->
    (exists ext, tab_ok DISTS (cat (is_codes s) (is_distcode s)) (is_distbits s) ext = true /\ code_val last + 2 ^ code_op last <= ext /\ ext <= cext (is_distcode s)) ->
    code_bits here <= 15 ->
    LMEM v (mkW s c r) M -> DJE v s b0 h0 n0 r R ->
    exists R1,
      msteps s6u_segs (mkst R (Z_to_bv 64 0x20dd0) M s6u_rom) (mkst R1 (Z_to_bv 64 0x20e64) M s6u_rom)
      /\ QREG s r last here J2 R1.
  Proof.
    intros s c r R M b0 h0 n0 HD RI last J2 here LK LB (ext' & TD' & LXT & Hext') Bh HM HJ. open_dfacts HD.
    pose proof HJ as X. unfold DJE, DK in X.
    destruct X as ((HF & G9 & G11 & G29 & G13 & G18 & G24 & G25 & G31) & G22 & G12 & G16 & G17 & G5 & G6 & G15 & G14 & G30 & G7 & G28). open_fixc HF.
    pose proof G2 as P2. pose proof G27 as P27. pose proof G8 as P8. pose proof G9 as P9. pose proof G22 as P22. pose proof G12 as P12.
    open_ictx C. open_lmem HM. open_rinv RI. open_cinv CI. open_frame Mfr. unfold mapped in *.
    pose proof (tab_ok_root _ _ _ _ TD) as (Rt1 & Rt2 & Rt3).
    pose proof (ctab6_range v (is_distcode s) C Hofs) as [HA0 HA1].
    pose proof (ctab6_cells v s c r M (is_distcode s) C HM Hofs) as TAB.
    pose proof (ones_range15 (is_distbits s) Rt1) as Hones.
    pose proof (BITSv_bound (ir_hold r) (is_distbits s) ltac:(lia)) as HJ1.
    pose proof (code_bits_range last) as Hcb. pose proof (code_op_range last) as Hop. pose proof (code_val_range last) as Hval.
    pose proof (cent_range last) as Hcent. pose proof (cent_shr8_range last) as Hc8.
    pose proof (code_bits_range here) as Hcb2. pose proof (code_val_range here) as Hval2. pose proof (clo_range here) as Hclo2.
    pose proof (cent_range here) as Hcent2. pose proof (cent_shr8_range here) as Hc82.
    pose proof (shiftr_BITSv_sub (ir_hold r) (code_bits last) (code_op last) ltac:(clear - Rt1 LB; lia) ltac:(clear - LK; lia)) as HJ2.
    pose proof (land57344_cent last ltac:(clear - Rt1 LB; lia)) as L57344.
    assert (Hop4 : cent last mod 2 ^ 4 = code_op last) by (rewrite cent_op4; apply Z.mod_small; clear - LK Hop Rt1; lia).
    arm_symexP (@nil (Z * expr)) ilDL 40%nat [false; false; false; false; false]
      [RVal (EVar 53%nat); RVal (EVar 54%nat)] qpins
      [(45%nat, 2 ^ 15); (46%nat, 2 ^ 63); (47%nat, 2 ^ 32); (48%nat, 2 ^ 24); (49%nat, 16); (53%nat, 65536); (54%nat, 65536)] v r
      [Z.ones (is_distbits s); ctab6 v (is_distcode s); cent last; cent last / 2 ^ 8; code_bits last; 0; 0; 0; code_val here; clo here] NoVals F0
      (mkst R (Z_to_bv 64 0x20dd0) M s6u_rom) R1 HR1 Hfr1 Hms1.
    all: rewrite ?cent_op, ?Hop4, ?cent_val.
    all: try arm_side.
    all: rewrite ?idx2_probe by (first [exact Rhold64 | exact Hval | clear - Rt1 LK LB; lia]).
    all: rewrite ?idx2_probe_w by (first [exact Rhold64 | exact Hval | clear - Rt1 LK LB; lia]).
    all: rewrite ?cent_reasm, ?cent_bits.
    all: try (subst here J2; tab_read2 TAB (code_val last + Z.shiftr (BITSv (ir_hold r) (code_bits last + code_op last)) (code_bits last)); clear - HJ2 LXT Hext' Hval; lia).
    all: try (generalize HJ2; clear - HA0 HA1 LXT Hext' Hval; intro; lia).
    all: try ub_ptr_side.
    all: match goal with |- ?G => idtac "LEFTQL" G end.
    exists R1. split; [by_run Hms1|].
    symex_reg HR1 (19%bv : reg) as Q18. symex_reg HR1 (20%bv : reg) as Q19. symex_reg HR1 (26%bv : reg) as Q25.
    symex_reg HR1 (31%bv : reg) as Q31. rewrite ?cent_op, ?Hop4 in Q31. rewrite mask_reg in Q31 by (clear - Rt1 LK LB; lia).
    symex_reg HR1 (29%bv : reg) as Q29. rewrite ?cent_val in Q29.
    symex_reg HR1 (30%bv : reg) as Q30. rewrite ?cent_reasm in Q30.
    symex_reg HR1 (22%bv : reg) as Q21. rewrite ?cent_reasm in Q21.
    symex_reg HR1 (21%bv : reg) as Q20. rewrite ?cent_reasm, ?cent_bits in Q20.
    symex_reg HR1 (23%bv : reg) as Q23. rewrite ?cent_reasm, ?cent_bits in Q23.
    unfold QREG. split; [lfixc_close Hfr1 HR1|].
    regs_via Hfr1; first [exact Q18 | exact Q19 | exact Q25 | exact Q31 | exact Q29 | exact Q30 | exact Q21 | exact Q20 | exact Q23
                         | rewrite Q23; f_equal; lia
                         | match goal with |- ?G => idtac "QREG LEFT" G end].
  Qed.

  Ltac open_qreg HQ :=
    destruct HQ as (HF & G9 & G22 & G12 & G25 & G6 & G19 & G18 & G14 & G15 & G5 & G16 & G17 & G11 & G13 & G31 & G28 & G29 & G7 & G30 & G21 & G20 & G23); open_fixc HF;
    let XF := fresh in pose proof HF as XF; unfold LFIXc, INF_FRAME in XF; destruct XF as (P2 & P27 & P8 & _);
    pose proof G9 as P9; pose proof G22 as P22; pose proof G12 as P12; pose proof G25 as P25.

  Lemma dist_QL_hit : forall s c r R M,
    is_mode s = DIST -> dist_facts v s c -> RINV (cv_NI v) (cv_NO v) r ->
    let last := dent1 s (ir_hold r) in
    let J2 := code_val last + Z.shiftr (BITSv (ir_hold r) (code_bits last + code_op last)) (code_bits last) in
    let here := cat (is_codes s) (is_distcode s) J2 in
    1 <= code_op last <= 15 - is_distbits s -> code_bits last = is_distbits s ->
    (forall j, 0 <= j < 2 ^ code_op last -> term_ok DISTS (15 - is_distbits s) (cat (is_codes s) (is_distcode s) (code_val last + j)) = true) ->
    (exists ext, tab_ok DISTS (cat (is_codes s) (is_distcode s)) (is_distbits s) ext = true /\ code_val last + 2 ^ code_op last <= ext /\ ext <= cext (is_distcode s)) ->
    code_bits last + code_bits here <= ir_bits r ->
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LX v (mkW s c r) -> QREG s r last here J2 R ->
    exists R' M' pc',
      msteps s6u_segs (mkst R (Z_to_bv 64 0x20e64) M s6u_rom) (mkst R' (Z_to_bv 64 pc') M' s6u_rom)
      /\ arm_post v (mkW s c r) M (dist_res here (is_back s + code_bits last) s c (rdrop r (code_bits last))) R' M' pc'.
  Proof.
    intros s c r R M Hmode HD RI last J2 here LK LB SUB HXT LE HM HRC HX HQ. pose proof HD as HD0. open_dfacts HD. open_qreg HQ.
    open_ictx C. pose proof RI as RI0. open_rinv RI.
    pose proof (tab_ok_root _ _ _ _ TD) as (Rt1 & Rt2 & Rt3).
    pose proof (ctab6_range v (is_distcode s) C Hofs) as [HA0 HA1].
    pose proof (ones_range15 (code_bits last + code_op last) ltac:(clear - Rt1 LK LB; lia)) as Hones.
    pose proof (code_val_range last) as Hval. pose proof (cent_shr8_range last) as Hc8.
    pose proof (shiftr_BITSv_sub (ir_hold r) (code_bits last) (code_op last) ltac:(clear - Rt1 LB; lia) ltac:(clear - LK; lia)) as HJ2.
    pose proof (SUB _ HJ2) as TE. change (cat _ _ _) with here in TE. destruct (term_ok_DISTS _ _ TE) as (Bh & _).
    pose proof (cent_range here) as Hcent2. pose proof (cent_shr8_range here) as Hc82. pose proof (code_bits_range here) as Hcb2.
    destruct HXT as (ext' & TD' & LXT & Hext').
    arm_symexP (@nil (Z * expr)) ilDL 3%nat [true] (@nil (option expr)) lpins lvb v r
      [Z.ones (code_bits last + code_op last); code_bits last; code_val last; ctab6 v (is_distcode s); cent last / 2 ^ 8; cent here; cent here / 2 ^ 8; code_bits here] NoVals F0
      (mkst R (Z_to_bv 64 0x20e64) M s6u_rom) R1 HR1 Hfr1 Hms1.
    all: try arm_side.
    all: match goal with |- ?G => idtac "LEFTQH" G end.
    assert (HJE : DJE2 v s (ir_bits r) (ir_have r) (ir_next r) last r R1).
    { unfold DJE2, DK2. change (didx2 last (ir_hold r)) with J2. change (dent2 s last (ir_hold r)) with here.
      split; [split; [lfixc_close Hfr1 HR1|]|]; regs_via Hfr1; first [ rewrite (Hfr1 (19%bv : reg) eq_refl); rewrite G18; f_equal; lia
                                                               | rewrite (Hfr1 (23%bv : reg) eq_refl); exact G23
                                                               | match goal with |- ?G => idtac "DJE2 LEFT" G end]. }
    destruct (dist_T v C s c r R1 M (ir_bits r) (ir_have r) (ir_next r) last Hmode HD0 RI0 LK LB Rbits SUB (ex_intro _ ext' (conj TD' (conj LXT Hext')))
                ltac:(change (dent2 s last (ir_hold r)) with here; rewrite wrap32_id by (clear - Bh Rt1 LB Hcb2; lia); exact LE)
                HM HRC HX HJE) as (R' & M' & pc' & Hms2 & HPOST).
    exists R', M', pc'. split; [eapply msteps_trans; [| exact Hms2]; by_run Hms1 | exact HPOST].
  Qed.

  Lemma dist_QL_loop : forall s c r R M,
    is_mode s = DIST -> dist_facts v s c -> RINV (cv_NI v) (cv_NO v) r ->
    let last := dent1 s (ir_hold r) in
    let J2 := code_val last + Z.shiftr (BITSv (ir_hold r) (code_bits last + code_op last)) (code_bits last) in
    let here := cat (is_codes s) (is_distcode s) J2 in
    1 <= code_op last <= 15 - is_distbits s -> code_bits last = is_distbits s ->
    (forall j, 0 <= j < 2 ^ code_op last -> term_ok DISTS (15 - is_distbits s) (cat (is_codes s) (is_distcode s) (code_val last + j)) = true) ->
    (exists ext, tab_ok DISTS (cat (is_codes s) (is_distcode s)) (is_distbits s) ext = true /\ code_val last + 2 ^ code_op last <= ext /\ ext <= cext (is_distcode s)) ->
    ir_bits r < code_bits last + code_bits here ->
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LX v (mkW s c r) -> QREG s r last here J2 R ->
    exists R' M' pc',
      msteps s6u_segs (mkst R (Z_to_bv 64 0x20e64) M s6u_rom) (mkst R' (Z_to_bv 64 pc') M' s6u_rom)
      /\ arm_post v (mkW s c r) M
           (match (PULLBYTE ;; DECODE_k 7 (is_distcode s) (didx2 last) (fun h => wrap32 (code_bits last + code_bits h)))%am (mkW s c r) with
            | ARun here2 (mkW s2 c2 r2) => dist_res here2 (is_back s + code_bits last) s c (rdrop r2 (code_bits last))
            | ALeave w2 => ALeave w2
            | ARet rc w2 => ARet rc w2
            end) R' M' pc'.
  Proof.
    intros s c r R M Hmode HD RI last J2 here LK LB SUB HXT GT HM HRC HX HQ. pose proof HD as HD0. open_dfacts HD. open_qreg HQ.
    open_ictx C. pose proof RI as RI0. open_rinv RI. open_lx HX.
    pose proof (tab_ok_root _ _ _ _ TD) as (Rt1 & Rt2 & Rt3).
    pose proof (ctab6_range v (is_distcode s) C Hofs) as [HA0 HA1].
    pose proof (ones_range15 (code_bits last + code_op last) ltac:(clear - Rt1 LK LB; lia)) as Hones.
    pose proof (code_val_range last) as Hval. pose proof (cent_shr8_range last) as Hc8.
    pose proof (shiftr_BITSv_sub (ir_hold r) (code_bits last) (code_op last) ltac:(clear - Rt1 LB; lia) ltac:(clear - LK; lia)) as HJ2.
    pose proof (SUB _ HJ2) as TE. change (cat _ _ _) with here in TE. destruct (term_ok_DISTS _ _ TE) as (Bh & _).
    pose proof (cent_range here) as Hcent2. pose proof (cent_shr8_range here) as Hc82. pose proof (code_bits_range here) as Hcb2.
    destruct HXT as (ext' & TD' & LXT & Hext').
    assert (SUB' : forall j, 0 <= j < 2 ^ code_op last -> term_ok DISTS (15 - is_distbits s) (cat (is_codes s) (is_distcode s) (code_val last + j)) = true) by exact SUB.
    arm_symexP (@nil (Z * expr)) ilDL 3%nat [false] (@nil (option expr)) lpins lvb v r
      [Z.ones (code_bits last + code_op last); code_bits last; code_val last; ctab6 v (is_distcode s); cent last / 2 ^ 8; cent here; cent here / 2 ^ 8; code_bits here] NoVals F0
      (mkst R (Z_to_bv 64 0x20e64) M s6u_rom) R1 HR1 Hfr1 Hms1.
    all: try arm_side.
    all: match goal with |- ?G => idtac "LEFTQLL" G end.
    assert (HJS : DJS2 v s (ir_bits r) (ir_have r) (ir_next r) last r R1).
    { unfold DJS2, DK2.
      split; [split; [lfixc_close Hfr1 HR1|]|]; regs_via Hfr1; first [ rewrite (Hfr1 (19%bv : reg) eq_refl); rewrite G18; f_equal; lia
                                                               | clear; lia | clear - Rbits; lia
                                                               | match goal with |- ?G => idtac "DJS2 LEFT" G end]. }
    assert (NH : is_mode s <> HEAD) by (rewrite Hmode; cbv; discriminate).
    assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
    pose proof (dec_loop v s c (is_distcode s) (didx2 last) (fun h => wrap32 (code_bits last + code_bits h)) 30 0x20e68 0x20edc
                  (DJS2 v s (ir_bits r) (ir_have r) (ir_next r) last) (DJE2 v s (ir_bits r) (ir_have r) (ir_next r) last) C ltac:(lia)
                  (fun h Hh => need2_bound DISTS _ _ _ last h TD' Hh LK LB SUB')
                  CI
                  (dist2_step_H v s c C (ir_bits r) (ir_have r) (ir_next r) (proj1 Rbits) Rnx0 ext' last TD' Hext' Hofs CI LK LB LXT)
                  (dist2_step_E v s c C (ir_bits r) (ir_have r) (ir_next r) (proj1 Rbits) Rnx0 ext' last TD' Hext' Hofs CI LK LB LXT)
                  (dist2_dry v s c C (ir_bits r) (ir_have r) (ir_next r) (proj1 Rbits) Rnx0 ext' last TD' Hext' Hofs CI LK LB)
                  7%nat r R1 M HM HRC HJS RI0
                  ltac:(cbv beta; change (code_at s (is_distcode s) (didx2 last (ir_hold r))) with here; rewrite wrap32_id by (clear - Bh Rt1 LB Hcb2; lia); exact GT)
                  ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; clear - Rbits; lia)) as NL.
    destruct ((PULLBYTE ;; DECODE_k 7 (is_distcode s) (didx2 last) (fun h => wrap32 (code_bits last + code_bits h)))%am (mkW s c r))
      as [here2 w1 | w1 | rc w1]; [| | destruct NL].
    - destruct NL as (r1 & R2 & -> & Hms2 & HJE & RI1 & S5 & Eh2 & Hb1 & HM1 & HRC1).
      destruct S5 as (Q1 & Q2 & Q3 & Q4 & Q5).
      assert (HX1 : LX v (mkW s c r1)) by (apply (LX_step0 v s c r s c r1 HX NH NB); try reflexivity; [exact Xlive | exact Q3 | rewrite Q5; exact Xret | exact Xmsg | bk_side]).
      subst here2.
      destruct (dist_T v C s c r1 R2 M (ir_bits r) (ir_have r) (ir_next r) last Hmode HD0 RI1 LK LB Rbits SUB (ex_intro _ ext' (conj TD' (conj LXT Hext')))
                  ltac:(exact (proj1 Hb1)) HM1 HRC1 HX1 HJE) as (R' & M' & pc' & Hms3 & HPOST).
      exists R', M', pc'. split; [eapply msteps_trans; [| eapply msteps_trans; [exact Hms2 | exact Hms3]]; by_run Hms1|].
      apply (arm_post_rebase v s c r c r1); [symmetry; exact Q1 | exact HPOST].
    - destruct NL as (r1 & R2 & -> & Hms2 & HL1 & RI1 & S5 & Hz & Hb1 & HM1 & HRC1).
      destruct S5 as (Q1 & Q2 & Q3 & Q4 & Q5).
      exists R2, M, pc6_leave. split; [eapply msteps_trans; [| exact Hms2]; by_run Hms1|].
      cbn [arm_post w_r]. split; [reflexivity|]. rewrite Q1. split; [| apply MFRAME_refl].
      split; [exact HM1|]. split; [| split; [apply same_blocks_refl | exact HL1]].
      apply (LX_step0 v s c r s c r1 HX NH NB); try reflexivity; [exact Xlive | exact Q3 | rewrite Q5; exact Xret | exact Xmsg | bk_side].
  Qed.

  Lemma dist_Q_link : forall s c r R M b0 h0 n0 ext,
    is_mode s = DIST -> dist_facts v s c -> RINV (cv_NI v) (cv_NO v) r ->
    let last := dent1 s (ir_hold r) in
    code_bits last <= ir_bits r ->
    tab_ok DISTS (cat (is_codes s) (is_distcode s)) (is_distbits s) ext = true -> ext <= cext (is_distcode s) ->
    1 <= code_op last <= 15 - is_distbits s -> code_bits last = is_distbits s -> code_val last + 2 ^ code_op last <= ext ->
    (forall j, 0 <= j < 2 ^ code_op last ->
       is_linkop (code_op (cat (is_codes s) (is_distcode s) (code_val last + j))) = false
       /\ term_ok DISTS (15 - is_distbits s) (cat (is_codes s) (is_distcode s) (code_val last + j)) = true) ->
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LX v (mkW s c r) -> DJE v s b0 h0 n0 r R ->
    exists R' M' pc',
      msteps s6u_segs (mkst R (Z_to_bv 64 0x20dd0) M s6u_rom) (mkst R' (Z_to_bv 64 pc') M' s6u_rom)
      /\ arm_post v (mkW s c r) M (dist_after1 s last (mkW s c r)) R' M' pc'.
  Proof.
    intros s c r R M b0 h0 n0 ext' Hmode HD RI last Hlb TD' Hext' LK LB LXT SUB HM HRC HX HJ. pose proof HD as HD0. open_dfacts HD.
    open_ictx C. pose proof RI as RI0. open_rinv RI. pose proof CI as CI'. open_cinv CI.
    pose proof (tab_ok_root _ _ _ _ TD) as (Rt1 & Rt2 & Rt3).
    assert (L : 1 <= code_op last <= 15) by (clear - LK Rt1; lia).
    destruct (op_link_tests _ L) as (_ & _ & E240 & _).
    assert (E240b : (Z.land (code_op last) 240 =? 0) = true) by (apply Z.eqb_eq; exact E240).
    assert (SUB' : forall j, 0 <= j < 2 ^ code_op last -> term_ok DISTS (15 - is_distbits s) (cat (is_codes s) (is_distcode s) (code_val last + j)) = true)
      by (intros j Hj; exact (proj2 (SUB j Hj))).
    pose proof (shiftr_BITSv_sub (ir_hold r) (code_bits last) (code_op last) ltac:(clear - Rt1 LB; lia) ltac:(clear - LK; lia)) as HJ2.
    set (J2 := code_val last + Z.shiftr (BITSv (ir_hold r) (code_bits last + code_op last)) (code_bits last)) in *.
    set (here := cat (is_codes s) (is_distcode s) J2) in *.
    pose proof (SUB' _ HJ2) as TE. change (cat _ _ _) with here in TE. destruct (term_ok_DISTS _ _ TE) as (Bh & _).
    pose proof (code_bits_range here) as Hcb2.
    assert (HXT : exists ext0, tab_ok DISTS (cat (is_codes s) (is_distcode s)) (is_distbits s) ext0 = true
                    /\ code_val last + 2 ^ code_op last <= ext0 /\ ext0 <= cext (is_distcode s)) by (exists ext'; split; [exact TD' | split; [exact LXT | exact Hext']]).
    destruct (dist_QL_pre s c r R M b0 h0 n0 HD0 RI0 LK LB HXT ltac:(subst here J2 last; clear - Bh Rt1; lia) HM HJ) as (R1 & Hms1 & HQ).
    assert (ED2 : DECODE2 (is_distcode s) last (mkW s c r)
                  = if wrap32 (code_bits last + code_bits here) <=? ir_bits r then ARun here (mkW s c r)
                    else (PULLBYTE ;; DECODE_k 7 (is_distcode s) (didx2 last) (fun h => wrap32 (code_bits last + code_bits h)))%am (mkW s c r)).
    { unfold DECODE2. rewrite DECODE_k_S. rewrite code_at_cat. reflexivity. }
    rewrite wrap32_id in ED2 by (clear - Bh Rt1 LB Hcb2; lia).
    destruct (Z.leb_spec (code_bits last + code_bits here) (ir_bits r)) as [LE2|GT2].
    - rewrite (dist_after1_link s last c r here r E240b ED2).
      destruct (dist_QL_hit s c r R1 M Hmode HD0 RI0 LK LB SUB' HXT LE2 HM HRC HX HQ) as (R' & M' & pc' & Hms2 & HPOST).
      exists R', M', pc'. split; [eapply msteps_trans; [exact Hms1 | exact Hms2] | exact HPOST].
    - pose proof (DECODE_k_run (cv_NI v) (cv_NO v) ltac:(clear - CI0; lia) ltac:(clear - CP0; lia) 8 (is_distcode s) (didx2 last)
                    (fun h => wrap32 (code_bits last + code_bits h)) 30 s c r RI0 ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; clear - Rbits; lia)
                    (fun h Hh => need2_bound DISTS _ _ _ last h TD' Hh LK LB SUB') Cil Cinb) as DR.
      change (DECODE_k 8 (is_distcode s) (didx2 last) (fun h => wrap32 (code_bits last + code_bits h))) with (DECODE2 (is_distcode s) last) in DR.
      rewrite ED2 in DR.
      destruct (dist_QL_loop s c r R1 M Hmode HD0 RI0 LK LB SUB' HXT GT2 HM HRC HX HQ) as (R' & M' & pc' & Hms2 & HPOST).
      exists R', M', pc'. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
      change (dent1 s (ir_hold r)) with last in HPOST.
      destruct ((PULLBYTE ;; DECODE_k 7 (is_distcode s) (didx2 last) (fun h => wrap32 (code_bits last + code_bits h)))%am (mkW s c r))
        as [here2 w1 | w1 | rc w1] eqn:EN; [| | destruct DR].
      + destruct DR as (r2 & -> & _). rewrite (dist_after1_link s last c r here2 r2 E240b ltac:(first [exact ED2 | rewrite ED2; exact EN])). exact HPOST.
      + rewrite (dist_after1_leave2 s last c r w1 E240b ltac:(first [exact ED2 | rewrite ED2; exact EN])). exact HPOST.
  Qed.

  Lemma dist_Q : forall s c r R M b0 h0 n0,
    is_mode s = DIST -> dist_facts v s c -> RINV (cv_NI v) (cv_NO v) r ->
    let last := dent1 s (ir_hold r) in
    code_bits last <= ir_bits r ->
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LX v (mkW s c r) -> DJE v s b0 h0 n0 r R ->
    exists R' M' pc',
      msteps s6u_segs (mkst R (Z_to_bv 64 0x20dd0) M s6u_rom) (mkst R' (Z_to_bv 64 pc') M' s6u_rom)
      /\ arm_post v (mkW s c r) M (dist_after1 s last (mkW s c r)) R' M' pc'.
  Proof.
    intros s c r R M b0 h0 n0 Hmode HD RI last Hlb HM HRC HX HJ. pose proof HD as HD0. open_dfacts HD.
    pose proof RI as RI0. open_rinv RI.
    pose proof (tab_ok_root _ _ _ _ TD) as (Rt1 & Rt2 & Rt3).
    pose proof (BITSv_bound (ir_hold r) (is_distbits s) ltac:(lia)) as HJ1.
    pose proof (tab_root_entry DISTS _ _ _ (BITSv (ir_hold r) (is_distbits s)) TD HJ1) as RE. cbv beta in RE.
    change (cat (is_codes s) (is_distcode s) (BITSv (ir_hold r) (is_distbits s))) with last in RE.
    destruct RE as (HB & _ & _ & CASES).
    pose proof (code_op_range last) as Hop.
    destruct CASES as [[NL TM] | (L' & BB & V & XT & SUB)].
    - destruct (term_ok_DISTS _ _ TM) as (_ & CL).
      assert (O16 : 16 <= code_op last).
      { destruct CL as [(Oe & _) | (Ie & _)]; [exact (proj1 Oe)|].
        destruct (Z_lt_le_dec (code_op last) 16) as [LT|GE]; [| exact GE]. exfalso. apply Ie.
        assert (E : code_op last = 0 \/ 1 <= code_op last <= 15) by lia. destruct E as [E|E]; [rewrite E; reflexivity|].
        exact (proj1 (proj2 (op_link_tests _ E))). }
      rewrite dist_after1_term by (rewrite <- op_lt16_240 by exact Hop; apply Z.ltb_ge; exact O16).
      exact (dist_Q_term v C s c r R M b0 h0 n0 Hmode HD0 RI0 Hlb TM O16 HM HRC HX HJ).
    - exact (dist_Q_link s c r R M b0 h0 n0 ext Hmode HD0 RI0 Hlb TD Hext L' BB XT SUB HM HRC HX HJ).
  Qed.
End DistQL.
End FXG.
