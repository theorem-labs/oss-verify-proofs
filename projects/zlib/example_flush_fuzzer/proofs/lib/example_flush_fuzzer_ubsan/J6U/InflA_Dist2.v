(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import InflateGarbBase InflateInvTab.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import Prog ZIface InflateState InflateFast InflateArms Inflate InflateInv InflateInvKit InflateInvRun.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6U Require Import Segs6u.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import ISLayout InflMem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require Import IS6 InflRod6 InflCtx6 InflArmLib6 InflArmLib6b InflNeed6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require Import InflDec6.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Definition ilD2 : cfg := ilSx [0x20e68; 0x20edc] [AV (EAdd (EVar 43%nat) (EVar 44%nat)) 0 1 0 (EVar 44%nat)].

Section DistL2.
  Variable v : icv.
  Variables (s : inflate_state) (c : icall).
  Hypothesis C : ictx v.
  Variables (b1 h1 n1 : Z).
  Hypothesis Hb1 : 0 <= b1.
  Hypothesis Hn1 : 0 <= n1.
  Variables (ext last : Z).
  Hypothesis TD : tab_ok DISTS (cat (is_codes s) (is_distcode s)) (is_distbits s) ext = true.
  Hypothesis Hext : ext <= cext (is_distcode s).
  Hypothesis Hofs : cofs_ok (is_distcode s).
  Hypothesis CI : CINV (cv_NI v) (cv_NO v) c.
  Hypothesis LK : 1 <= code_op last <= 15 - is_distbits s.
  Hypothesis LB : code_bits last = is_distbits s.
  Hypothesis LXT : code_val last + 2 ^ code_op last <= ext.

  Local Abbreviation db := (is_distbits s).
  Local Abbreviation A := (ctab6 v (is_distcode s)).
  Local Abbreviation lb := (code_bits last).
  Local Abbreviation lop := (code_op last).
  Local Abbreviation lv := (code_val last).
  Definition didx2 (h : Z) : Z := lv + Z.shiftr (BITSv h (lb + lop)) lb.
  Definition dent2 (h : Z) : Z := cat (is_codes s) (is_distcode s) (didx2 h).

  Definition DK2 (r : iregs) (R : bvmap 5 word) : Prop :=
    LFIXc v R /\ getr R 9 = zw (cv_P0 v + ir_put r) /\ getr R 11 = zw A /\ getr R 13 = zw 1
    /\ getr R 31 = zw (Z.ones (lb + lop)) /\ getr R 28 = zw lb /\ getr R 29 = zw lv /\ getr R 7 = zw (cent last / 2 ^ 8)
    /\ getr R 14 = zw b1 /\ getr R 15 = zw b1 /\ getr R 5 = zw (cv_I0 v + n1) /\ getr R 16 = zw h1 /\ getr R 17 = zw (8 * h1).
  Definition DJS2 (r : iregs) (R : bvmap 5 word) : Prop :=
    DK2 r R /\ getr R 25 = zw (ir_hold r) /\ getr R 12 = zw (ir_have r) /\ getr R 26 = zw (cv_I0 v + ir_next r) /\ getr R 6 = zw (cv_I0 v + ir_next r)
    /\ getr R 20 = zw (ir_bits r) /\ getr R 19 = zw (lb - (ir_bits r - b1))
    /\ b1 + 8 * (h1 - ir_have r) = ir_bits r /\ n1 + (h1 - ir_have r) = ir_next r /\ 0 <= h1 - ir_have r.
  Definition DJE2 (r : iregs) (R : bvmap 5 word) : Prop :=
    DK2 r R /\ getr R 25 = zw (ir_hold r) /\ getr R 12 = zw (ir_have r) /\ getr R 26 = zw (cv_I0 v + ir_next r)
    /\ getr R 20 = zw (ir_bits r) /\ getr R 19 = zw (lb - (ir_bits r - b1))
    /\ getr R 30 = zw (cent (dent2 (ir_hold r))) /\ getr R 22 = zw (cent (dent2 (ir_hold r)) / 2 ^ 8)
    /\ getr R 21 = zw (code_bits (dent2 (ir_hold r))) /\ getr R 23 = zw (code_bits (dent2 (ir_hold r)) + lb).

  Ltac open_djs HJ :=
    let X := fresh in pose proof HJ as X; unfold DJS2, DK2 in X;
    destruct X as ((HF & G9 & G11 & G13 & G31 & G28 & G29 & G7 & G14 & G15 & G5 & G16 & G17)
                   & G22 & G12 & G25 & G6 & G19 & G18 & Ib & In & Ih); open_fixc HF.

  Definition dpins2 : list (Z * expr) :=
    [(2, EVar 32%nat); (8, EVar 33%nat); (18, EVar 34%nat); (1, ELit 16209); (9, EAdd (EVar 37%nat) (EVar 38%nat));
     (11, EVar 48%nat); (13, ELit 1); (31, EVar 45%nat); (28, EVar 46%nat); (29, EVar 47%nat); (7, EVar 52%nat);
     (14, EVar 50%nat); (15, EVar 50%nat); (5, EAdd (EVar 43%nat) (EVar 51%nat)); (16, EVar 49%nat); (17, EMul (ELit 8) (EVar 49%nat));
     (25, EVar 40%nat); (12, EVar 36%nat); (26, EAdd (EVar 43%nat) (EVar 44%nat)); (6, EAdd (EVar 43%nat) (EVar 44%nat));
     (20, EVar 41%nat); (19, ESub (EVar 46%nat) (ESub (EVar 41%nat) (EVar 50%nat)))].
  Definition dvb2 : list (nat * Z) :=
    [(45%nat, 2 ^ 15); (46%nat, 16); (47%nat, 2 ^ 16); (48%nat, 2 ^ 63); (49%nat, 2 ^ 31); (50%nat, 2 ^ 63); (51%nat, 2 ^ 31); (52%nat, 2 ^ 24);
     (53%nat, 65536); (54%nat, 65536)].

  Ltac d2_side Hby Rbits Rhold Hb64 Rt1 LK Hlv TAB HA0 HA1 Hext LXT Hb :=
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

  Ltac dj2_close HR Hfr r Hby Rbits Rhold Hb64 Hh Rnh Rnx0 CI0 Rt1 LK Hlv :=
    let Q22 := fresh in let Q12 := fresh in let Q25 := fresh in let Q6 := fresh in let Q19 := fresh in let Q18 := fresh in
    let Q30 := fresh in let Q21 := fresh in let Q20 := fresh in let Q23 := fresh in
    symex_reg HR (25%bv : reg) as Q22; symex_reg HR (12%bv : reg) as Q12; symex_reg HR (26%bv : reg) as Q25; symex_reg HR (6%bv : reg) as Q6;
    symex_reg HR (20%bv : reg) as Q19; symex_reg HR (19%bv : reg) as Q18;
    symex_reg HR (30%bv : reg) as Q30; symex_reg HR (22%bv : reg) as Q21; symex_reg HR (21%bv : reg) as Q20; symex_reg HR (23%bv : reg) as Q23;
    cbn [famA] in Q22; rewrite bmod_get in Q22 by exact Hby;
    cbn [famA] in Q30; rewrite ?bmod_get in Q30 by exact Hby; rewrite ?idx2_pull_w in Q30 by (first [exact Rhold | exact Hby | exact Hlv | clear - Rbits Hb64 Rt1 LK LB; lia]); rewrite ?cent_reasm in Q30;
    cbn [famA] in Q21; rewrite ?bmod_get in Q21 by exact Hby; rewrite ?idx2_pull_w in Q21 by (first [exact Rhold | exact Hby | exact Hlv | clear - Rbits Hb64 Rt1 LK LB; lia]); rewrite ?cent_reasm in Q21;
    cbn [famA] in Q20; rewrite ?bmod_get in Q20 by exact Hby; rewrite ?idx2_pull_w in Q20 by (first [exact Rhold | exact Hby | exact Hlv | clear - Rbits Hb64 Rt1 LK LB; lia]); rewrite ?cent_reasm, ?cent_bits in Q20;
    cbn [famA] in Q23; rewrite ?bmod_get in Q23 by exact Hby; rewrite ?idx2_pull_w in Q23 by (first [exact Rhold | exact Hby | exact Hlv | clear - Rbits Hb64 Rt1 LK LB; lia]); rewrite ?cent_reasm, ?cent_bits in Q23;
    unfold DJS2, DJE2, DK2, pull1; cbn [ir_next ir_have ir_put ir_left ir_hold ir_bits ir_in ir_out ir_ret];
    repeat match goal with |- _ /\ _ => split end;
    first [ assumption
          | lazymatch goal with |- LFIXc _ _ => lfixc_close Hfr HR end
          | lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr n eq_refl); assumption end
          | rewrite Q22; rewrite zalu_sll_small; [f_equal; lia | clear - Hby; lia | clear - Rbits Hb64; lia
              | clear - Hby Rbits Hb64 Rhold; pose proof (pull_hold_lt _ _ _ Rhold (proj1 Rbits) Hby); assert (2 ^ (ir_bits r + 8) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia); lia]
          | rewrite Q12; rewrite ?szwrap32_small by (clear - Hh Rnh Rnx0 CI0; lia); f_equal; lia
          | rewrite Q25; f_equal; lia
          | rewrite Q6; f_equal; lia
          | rewrite Q19; f_equal; lia
          | rewrite Q18; f_equal; lia
          | rewrite Q30; f_equal; f_equal; f_equal; f_equal; lia
          | rewrite Q21; f_equal; f_equal; f_equal; f_equal; f_equal; lia
          | rewrite Q20; f_equal; f_equal; f_equal; f_equal; lia
          | rewrite Q23; f_equal; f_equal; [f_equal; f_equal; f_equal; lia | reflexivity]
          | lia
          | match goal with |- ?G => idtac "DJ2 LEFT" G end ].

  Ltac d2_prep C TD Hofs HM Rt1 Rt2 Rt3 HA0 HA1 TAB Hones Hlv Hc7 :=
    pose proof (tab_ok_root _ _ _ _ TD) as (Rt1 & Rt2 & Rt3);
    pose proof (ctab6_range v (is_distcode s) C Hofs) as [HA0 HA1];
    pose proof (ctab6_cells v s c _ _ (is_distcode s) C HM Hofs) as TAB;
    pose proof (ones_range15 (lb + lop) ltac:(clear - Rt1 LK LB; lia)) as Hones;
    pose proof (code_val_range last) as Hlv;
    pose proof (cent_shr8_range last) as Hc7.

  Lemma dist2_step_H : forall r R M,
    LMEM v (mkW s c r) M -> DJS2 r R -> RINV (cv_NI v) (cv_NO v) r -> 0 < ir_have r -> ir_bits r + 8 < 64 ->
    ir_bits r + 8 < wrap32 (lb + code_bits (dent2 (ir_hold (pull1 c r)))) ->
    exists R1, msteps s6u_segs (mkst R (Z_to_bv 64 0x20e68) M s6u_rom) (mkst R1 (Z_to_bv 64 0x20e68) M s6u_rom)
               /\ DJS2 (pull1 c r) R1.
  Proof.
    intros r R M HM HJ RI Hh Hb64 Hb. open_djs HJ. open_ictx C. open_lmem HM. open_rinv RI. open_cinv CI. unfold mapped in *.
    d2_prep C TD Hofs HM Rt1 Rt2 Rt3 HA0 HA1 TAB Hones Hlv Hc7.
    assert (Hh0 : 0 <= h1 < 2 ^ 31) by (clear - Ih In Hn1 Hh Rnh Rnx0 Rhv0 CI0; lia).
    assert (Hby : 0 <= arr_get (ic_input c) (ir_next r) < 256) by (apply Cinb; clear - Hh Rnx0 Rhv0 Rnh; lia).
    pose proof (cells_bmod _ _ _ _ Minp Cinb) as Hin0.
    pose proof (fun j (_ : 0 <= j < cv_NI v) => bmod_range (arr_get (ic_input c)) j) as Hinr.
    pose proof (code_bits_range (dent2 (ir_hold (pull1 c r)))) as Hcb.
    pose proof (code_val_range (dent2 (ir_hold (pull1 c r)))) as Hcv.
    pose proof (clo_range (dent2 (ir_hold (pull1 c r)))) as Hclo.
    unfold dent2, didx2 in Hb, Hcb, Hcv, Hclo |- *. cbn [ir_hold pull1] in Hb, Hcb, Hcv, Hclo |- *.
    arm_symexP (@nil (Z * expr)) ilD2 36%nat [false; false; false; false; true; false] [RVal (EVar 53%nat); RVal (EVar 54%nat)] dpins2 dvb2 v r
      [Z.ones (lb + lop); lb; lv; A; h1; b1; n1; cent last / 2 ^ 8;
       code_val (cat (is_codes s) (is_distcode s) (lv + Z.shiftr (BITSv (ir_hold r + arr_get (ic_input c) (ir_next r) * 2 ^ ir_bits r) (lb + lop)) lb));
       clo (cat (is_codes s) (is_distcode s) (lv + Z.shiftr (BITSv (ir_hold r + arr_get (ic_input c) (ir_next r) * 2 ^ ir_bits r) (lb + lop)) lb))]
      NoVals (famA c s)
      (mkst R (Z_to_bv 64 0x20e68) M s6u_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    all: d2_side Hby Rbits Rhold Hb64 Rt1 LK Hlv TAB HA0 HA1 Hext LXT Hb.
    all: match goal with |- ?G => idtac "LEFTD2H" G end.
    exists R1. split; [by_run Hms|].
    dj2_close HR1 Hfr r Hby Rbits Rhold Hb64 Hh Rnh Rnx0 CI0 Rt1 LK Hlv.
  Qed.

  Lemma dist2_step_E : forall r R M,
    LMEM v (mkW s c r) M -> DJS2 r R -> RINV (cv_NI v) (cv_NO v) r -> 0 < ir_have r -> ir_bits r + 8 < 64 ->
    wrap32 (lb + code_bits (dent2 (ir_hold (pull1 c r)))) <= ir_bits r + 8 ->
    exists R1, msteps s6u_segs (mkst R (Z_to_bv 64 0x20e68) M s6u_rom) (mkst R1 (Z_to_bv 64 0x20edc) M s6u_rom)
               /\ DJE2 (pull1 c r) R1.
  Proof.
    intros r R M HM HJ RI Hh Hb64 Hb. open_djs HJ. open_ictx C. open_lmem HM. open_rinv RI. open_cinv CI. unfold mapped in *.
    d2_prep C TD Hofs HM Rt1 Rt2 Rt3 HA0 HA1 TAB Hones Hlv Hc7.
    assert (Hh0 : 0 <= h1 < 2 ^ 31) by (clear - Ih In Hn1 Hh Rnh Rnx0 Rhv0 CI0; lia).
    assert (Hby : 0 <= arr_get (ic_input c) (ir_next r) < 256) by (apply Cinb; clear - Hh Rnx0 Rhv0 Rnh; lia).
    pose proof (cells_bmod _ _ _ _ Minp Cinb) as Hin0.
    pose proof (fun j (_ : 0 <= j < cv_NI v) => bmod_range (arr_get (ic_input c)) j) as Hinr.
    pose proof (code_bits_range (dent2 (ir_hold (pull1 c r)))) as Hcb.
    pose proof (code_val_range (dent2 (ir_hold (pull1 c r)))) as Hcv.
    pose proof (clo_range (dent2 (ir_hold (pull1 c r)))) as Hclo.
    unfold dent2, didx2 in Hb, Hcb, Hcv, Hclo |- *. cbn [ir_hold pull1] in Hb, Hcb, Hcv, Hclo |- *.
    arm_symexP (@nil (Z * expr)) ilD2 36%nat [false; false; false; false; true; true] [RVal (EVar 53%nat); RVal (EVar 54%nat)] dpins2 dvb2 v r
      [Z.ones (lb + lop); lb; lv; A; h1; b1; n1; cent last / 2 ^ 8;
       code_val (cat (is_codes s) (is_distcode s) (lv + Z.shiftr (BITSv (ir_hold r + arr_get (ic_input c) (ir_next r) * 2 ^ ir_bits r) (lb + lop)) lb));
       clo (cat (is_codes s) (is_distcode s) (lv + Z.shiftr (BITSv (ir_hold r + arr_get (ic_input c) (ir_next r) * 2 ^ ir_bits r) (lb + lop)) lb))]
      NoVals (famA c s)
      (mkst R (Z_to_bv 64 0x20e68) M s6u_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    all: d2_side Hby Rbits Rhold Hb64 Rt1 LK Hlv TAB HA0 HA1 Hext LXT Hb.
    all: try (rewrite wrap32_id in Hb by lia; clear - Hb; lia).
    all: match goal with |- ?G => idtac "LEFTD2E" G end.
    exists R1. split; [by_run Hms|].
    dj2_close HR1 Hfr r Hby Rbits Rhold Hb64 Hh Rnh Rnx0 CI0 Rt1 LK Hlv.
  Qed.

  Lemma dist2_dry : forall r R M,
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> DJS2 r R -> RINV (cv_NI v) (cv_NO v) r -> ir_have r = 0 ->
    exists R1, msteps s6u_segs (mkst R (Z_to_bv 64 0x20e68) M s6u_rom) (mkst R1 (Z_to_bv 64 pc6_leave) M s6u_rom)
               /\ LREG_leave v (mkW s c r) R1.
  Proof.
    intros r R M HM HRC HJ RI Hh. open_djs HJ. open_ictx C. open_lmem HM. open_frame Mfr. open_rinv RI. open_cinv CI. unfold mapped in *.
    d2_prep C TD Hofs HM Rt1 Rt2 Rt3 HA0 HA1 TAB Hones Hlv Hc7.
    assert (Hh0 : 0 <= h1 < 2 ^ 31) by (clear - Ih In Hn1 Hh Rnh Rnx0 Rhv0 CI0; lia). open_retc HRC.
    arm_symexP (@nil (Z * expr)) ilD2 14%nat [true] [RVal (EVar 53%nat); RVal (EVar 35%nat)] dpins2
      [(45%nat, 2 ^ 15); (46%nat, 16); (47%nat, 2 ^ 16); (48%nat, 2 ^ 63); (49%nat, 2 ^ 31); (50%nat, 2 ^ 63); (51%nat, 2 ^ 31); (52%nat, 2 ^ 24); (53%nat, 2 ^ 64)] v r
      [Z.ones (lb + lop); lb; lv; A; h1; b1; n1; cent last / 2 ^ 8; ir_ret r mod 2 ^ 64] NoVals (famA c s)
      (mkst R (Z_to_bv 64 0x20e68) M s6u_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    all: match goal with |- ?G => idtac "LEFTD2D" G end.
    exists R1. split; [by_run Hms|].
    symex_reg HR1 (27%bv : reg) as G26'. symex_reg HR1 (19%bv : reg) as G18'. symex_reg HR1 (23%bv : reg) as G24'. symex_reg HR1 (26%bv : reg) as G25'.
    symex_reg HR1 (13%bv : reg) as G13'. symex_reg HR1 (11%bv : reg) as G11'.
    unfold LREG_leave, LVARS, INF_FRAME; cbn [w_r]. regs_via Hfr.
    all: first [ rewrite G24'; rewrite Hh; reflexivity
               | rewrite G18'; f_equal; clear - Ib Hh; lia
               | rewrite G25'; f_equal; clear - In Hh; lia
               | rewrite G26'; apply zw_neg_mod
               | exact G13' | exact G11'
               | match goal with |- ?G => idtac "DRY2 LEFT" G end ].
  Qed.
End DistL2.
End FXG.
