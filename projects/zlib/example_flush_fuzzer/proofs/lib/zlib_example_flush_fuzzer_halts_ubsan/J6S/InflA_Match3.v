(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import Prog ZIface InflateState InflateFast InflateArms Inflate
     InflateInv InflateInvKit InflateInvRun.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6S Require Import Segs6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S Require Import ISLayout IS6 InflMem InflRod6 InflCtx6 InflArmLib6 InflArmLib6b
     InflA_Match1 InflA_Match2.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

Definition match_facts (v : icv) (s : inflate_state) (c : icall) (r : iregs) : Prop :=
  is_sane s = 1 /\ 1 <= is_length s <= 258 /\ 1 <= is_offset s <= 32768
  /\ 0 <= is_whave s <= is_wsize s /\ 0 <= is_wnext s <= is_wsize s
  /\ arr_len (is_window s) = cv_WN v /\ (is_wsize s = 0 \/ is_wsize s = cv_WN v)
  /\ (forall i, 0 <= i < cv_WN v -> 0 <= arr_get (is_window s) i < 256)
  /\ RINV (cv_NI v) (cv_NO v) r /\ CINV (cv_NI v) (cv_NO v) c.

Lemma match_facts_of_pinv : forall v s c r,
  is_mode s = MATCH -> pinv (cv_NI v) (cv_NO v) (cv_WN v) (cv_TOT0 v) (mkW s c r) -> match_facts v s c r.
Proof.
  intros v s c r Hmode HP. open_pinv HP.
  pose proof (sr_sane s SR) as Hsane. pose proof (sinv_match s PS Hmode) as [Hlen Hoff]. pose proof (sinv_wcur s PS) as [Hwh Hwn].
  pose proof WI as WI'. unfold WINV in WI'. cbn [w_s] in WI'. destruct WI' as (Hwl & _ & _ & Hws).
  pose proof (sr_winb s SR) as Hwb. rewrite Hwl in Hwb.
  unfold match_facts. repeat (split; [assumption|]). exact CI.
Qed.

Section MatchWinWrap.
  Variable v : icv.
  Hypothesis C : ictx v.

  Lemma match_win_wrap : forall s c r R M,
    is_mode s = MATCH ->
    ENTRY v (mkW s c r) R M -> match_facts v s c r ->
    ir_left r <> 0 -> ir_out r - ir_left r < is_offset s -> is_offset s - (ir_out r - ir_left r) <= is_whave s ->
    is_wnext s < is_offset s - (ir_out r - ir_left r) ->
    exists R' M' pc',
      msteps s6_segs (mkst R (Z_to_bv 64 0x1e828) M s6_rom) (mkst R' (Z_to_bv 64 pc') M' s6_rom)
      /\ arm_post v (mkW s c r) M (arm_MATCH ivar_ref (mkW s c r)) R' M' pc'.
  Proof.
    intros s c r R M Hmode HE HP HL0 HLT HBW HWR. destruct HE as (HM & HRC & HX & (HF & HV & G8)).
    destruct HP as (Hsane & Hlen & Hoff & Hwh & Hwn & Hwl & Hws & Hwb & RI & CI).
    open_ictx C. open_lmem HM. open_retc HRC. open_lx HX. open_fix HF. open_vars HV. open_rinv RI. open_cinv CI.
    pose proof (pins_of_regs _ _ _ _ _ HF HV) as (P2 & P25 & P10 & P11 & P21 & P31 & P29 & P24 & P19 & P9 & P18 & P1 & P22 & P23 & P26).
    unfold mapped in *.
    assert (NH : is_mode s <> HEAD) by (rewrite Hmode; cbv; discriminate).
    assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
    assert (Hput : 0 <= ir_put r <= cv_NO v) by (clear - Rpt0 Rpl Rlf0; lia).
    assert (Hcp : 0 <= ir_out r - ir_left r <= ir_put r) by (clear - Rout Routp; lia).
    rewrite (arm_MATCH_eq s c r Hsane) by (first [clear - Hcp Hput CP0; lia | clear - Hoff; lia | clear - Hwn; lia | clear - Rlf0 Rpl Rpt0 CP0; lia | clear - Hlen; lia]).
    pose proof (is6_offset _ _ _ _ Msc) as C96. pose proof (is6_length _ _ _ _ Msc) as C92.
    pose proof (is6_whave _ _ _ _ Msc) as C64. pose proof (is6_wnext _ _ _ _ Msc) as C68. pose proof (is6_wsize _ _ _ _ Msc) as C60.
    pose proof (is6_window _ _ _ _ Msc) as C72. cbn [q_window] in C72.
    pose proof (is6_sane _ _ _ _ Msc) as C7144. rewrite Hsane in C7144.
    open_frame Mfr.
    destruct (Z.eqb_spec (ir_left r) 0) as [L0|L0]; [exfalso; clear - L0 HL0; lia|].
    unfold msel.
    destruct (Z.ltb_spec (ir_out r - ir_left r) (is_offset s)) as [LT|GE]; [| exfalso; clear - GE HLT; lia].
      set (cw := is_offset s - (ir_out r - ir_left r)) in *.
      assert (Hcw : 1 <= cw <= 32768) by (subst cw; clear - LT Hcp Hoff; lia).
      destruct (Z.ltb_spec (is_whave s) cw) as [BW|BW]; [exfalso; clear - BW HBW; lia|].
      assert (WSZ : is_wsize s = 32768 /\ cv_WN v = 32768).
      { destruct CWB as (_ & _ & [[W0 _] | (W1 & _ & _)]); [exfalso; rewrite W0 in Hws; clear - Hws Hwh BW Hcw; lia|].
        split; [| exact W1]. rewrite W1 in Hws. clear - Hws Hwh BW Hcw. lia. }
      destruct WSZ as [Ews EWN]. rewrite Ews in C60. rewrite Ews.
      assert (HWB : 0 < cv_WB v /\ cv_WB v + 32768 < 2 ^ 63) by (destruct CWB as (W0 & W1 & [[Z1 _] | (_ & W2 & _)]); [rewrite EWN in Z1; discriminate | rewrite EWN in W1; clear - W1 W2; lia]).
      assert (WIN : forall (i copy : Z) R1,
        0 <= i -> 1 <= copy <= is_length s -> i + copy <= 32768 ->
        msteps s6_segs (mkst R (Z_to_bv 64 0x1e828) M s6_rom)
               (mkst R1 (Z_to_bv 64 0x1e8d8) (wbytes M (zw (cv_S v + 108)) (Z_to_le_bytes 4 (is_length s - mclamp r copy))) s6_rom) ->
        (forall rg, reg_in rg [12; 13; 14; 15; 16]%bv = false -> getr R1 rg = getr R rg) ->
        getr R1 13 = zw (cv_WB v + i) -> getr R1 12 = zw (mclamp r copy) -> getr R1 14 = zw (cv_WB v + i + mclamp r copy) ->
        exists R' M' pc',
          msteps s6_segs (mkst R (Z_to_bv 64 0x1e828) M s6_rom) (mkst R' (Z_to_bv 64 pc') M' s6_rom)
          /\ arm_post v (mkW s c r) M
               (let '(ob, put', _, _) := match_copy (is_window s) (ic_outbuf c, ir_put r, FWin i, mclamp r copy) in
                ARun tt (mkW (if is_length s - mclamp r copy =? 0 then iset_mode (iset_length s (is_length s - mclamp r copy)) LEN else iset_length s (is_length s - mclamp r copy))
                             (icset_outbuf c ob) (irset_put (irset_left r (ir_left r - mclamp r copy)) put'))) R' M' pc').
      { intros i copy R1 Hi Hcopy Hic Hms1 Hfr1 G13 G12 G14.
        assert (Hcpy : 1 <= mclamp r copy <= is_length s /\ mclamp r copy <= ir_left r /\ mclamp r copy <= copy)
          by (unfold mclamp; destruct (Z.ltb_spec (ir_left r) copy) as [Q|Q]; clear - L0 Hcopy Rlf0 Q; lia).
        pose proof (match_tail v C s c r R M R1 (FWin i) (mclamp r copy) Hmode (proj1 Hcpy) (proj1 (proj2 Hcpy)) (proj2 Hlen) HM HRC HX HF HV RI CI Hwl Hwb
                      ltac:(cbn; rewrite EWN; clear - Hi Hic Hcpy; lia) Hfr1 G13 G12 G14) as T.
        cbv zeta in T. destruct (match_copy (is_window s) (ic_outbuf c, ir_put r, FWin i, mclamp r copy)) as [[[ob put'] fr'] c'].
        destruct T as (R' & M' & pc' & Hms2 & HPOST).
        exists R', M', pc'. split; [eapply msteps_trans; [exact Hms1 | exact Hms2] | exact HPOST]. }
      destruct (Z.ltb_spec (is_wnext s) cw) as [NW_WR|NW_WR]; [| exfalso; clear - NW_WR HWR; subst cw; lia].
        set (c2 := cw - is_wnext s) in *.
        assert (Hc2 : 1 <= c2 <= 32768 /\ c2 <= cw) by (subst c2; clear - NW_WR Hcw Hwn; lia).
        cbv beta iota.
        destruct (Z_lt_le_dec c2 (is_length s)) as [CL1|CL1].
        * replace (if is_length s <? c2 then is_length s else c2) with c2 by (destruct (Z.ltb_spec (is_length s) c2); lia).
          destruct (Z_lt_le_dec c2 (ir_left r)) as [CL2|CL2].
          -- idtac.
          arm_symex ilMS 40%nat [false; false; true; false; true; true] [RVal (EVar 45%nat); RVal (EVar 42%nat); RVal (EVar 46%nat); RVal (EVar 47%nat); RVal (ELit 32768); RVal (EVar 48%nat); RVal (EVar 49%nat)] (@nil (Z * expr)) [(45%nat, 32769); (46%nat, 32769); (47%nat, 32769); (48%nat, 259); (49%nat, 2 ^ 63)] v r [is_offset s; is_whave s; is_wnext s; is_length s; cv_WB v] NoVals F0
            (mkst R (Z_to_bv 64 0x1e828) M s6_rom) R1 HR1 Hfr1 Hms1.
          all: try arm_side.
          all: match goal with |- ?G => idtac "W1" G end.
          symex_reg HR1 (13%bv : reg) as G13. symex_reg HR1 (12%bv : reg) as G12. symex_reg HR1 (14%bv : reg) as G14.
          apply (WIN (32768 - c2) (c2) R1); [clear - Hc2 Hcw NW_WR Hwn Hwh Ews; lia | clear - Hlen Hc2 Hcw CL1; lia | clear - Hc2 Hcw NW_WR Hwn Hwh Ews CL1 Hlen; lia
            | replace (mclamp r (c2)) with (c2) by (unfold mclamp; destruct (Z.ltb_spec (ir_left r) (c2)); lia);
              first [rewrite <- (le4_szwrap (is_length s - c2)); by_run Hms1 | replace (is_length s - c2) with 0 by lia; by_run Hms1 | by_run Hms1]
            | fr_weak Hfr1
            | rewrite G13; f_equal; rewrite ?szwrap32_small by lia; rewrite ?Z.mod_small by lia; lia
            | replace (mclamp r (c2)) with (c2) by (unfold mclamp; destruct (Z.ltb_spec (ir_left r) (c2)); lia); rewrite G12; f_equal; rewrite ?szwrap32_small by lia; rewrite ?Z.mod_small by lia; lia
            | replace (mclamp r (c2)) with (c2) by (unfold mclamp; destruct (Z.ltb_spec (ir_left r) (c2)); lia); rewrite G14; f_equal; rewrite ?szwrap32_small by lia; rewrite ?Z.mod_small by lia; lia ].
          -- idtac.
          arm_symex ilMS 40%nat [false; false; true; false; true; false] [RVal (EVar 45%nat); RVal (EVar 42%nat); RVal (EVar 46%nat); RVal (EVar 47%nat); RVal (ELit 32768); RVal (EVar 48%nat); RVal (EVar 49%nat)] (@nil (Z * expr)) [(45%nat, 32769); (46%nat, 32769); (47%nat, 32769); (48%nat, 259); (49%nat, 2 ^ 63)] v r [is_offset s; is_whave s; is_wnext s; is_length s; cv_WB v] NoVals F0
            (mkst R (Z_to_bv 64 0x1e828) M s6_rom) R1 HR1 Hfr1 Hms1.
          all: try arm_side.
          all: match goal with |- ?G => idtac "W2" G end.
          symex_reg HR1 (13%bv : reg) as G13. symex_reg HR1 (12%bv : reg) as G12. symex_reg HR1 (14%bv : reg) as G14.
          apply (WIN (32768 - c2) (c2) R1); [clear - Hc2 Hcw NW_WR Hwn Hwh Ews; lia | clear - Hlen Hc2 Hcw CL1; lia | clear - Hc2 Hcw NW_WR Hwn Hwh Ews CL1 Hlen; lia
            | replace (mclamp r (c2)) with (ir_left r) by (unfold mclamp; destruct (Z.ltb_spec (ir_left r) (c2)); lia);
              first [rewrite <- (le4_szwrap (is_length s - ir_left r)); by_run Hms1 | replace (is_length s - ir_left r) with 0 by lia; by_run Hms1 | by_run Hms1]
            | fr_weak Hfr1
            | rewrite G13; f_equal; rewrite ?szwrap32_small by lia; rewrite ?Z.mod_small by lia; lia
            | replace (mclamp r (c2)) with (ir_left r) by (unfold mclamp; destruct (Z.ltb_spec (ir_left r) (c2)); lia); rewrite G12; f_equal; rewrite ?szwrap32_small by lia; rewrite ?Z.mod_small by lia; lia
            | replace (mclamp r (c2)) with (ir_left r) by (unfold mclamp; destruct (Z.ltb_spec (ir_left r) (c2)); lia); rewrite G14; f_equal; rewrite ?szwrap32_small by lia; rewrite ?Z.mod_small by lia; lia ].
        * replace (if is_length s <? c2 then is_length s else c2) with (is_length s) by (destruct (Z.ltb_spec (is_length s) c2); lia).
          destruct (Z_lt_le_dec (is_length s) (ir_left r)) as [CL2|CL2].
          -- idtac.
          arm_symex ilMS 40%nat [false; false; true; false; false; true] [RVal (EVar 45%nat); RVal (EVar 42%nat); RVal (EVar 46%nat); RVal (EVar 47%nat); RVal (ELit 32768); RVal (EVar 48%nat); RVal (EVar 49%nat)] (@nil (Z * expr)) [(45%nat, 32769); (46%nat, 32769); (47%nat, 32769); (48%nat, 259); (49%nat, 2 ^ 63)] v r [is_offset s; is_whave s; is_wnext s; is_length s; cv_WB v] NoVals F0
            (mkst R (Z_to_bv 64 0x1e828) M s6_rom) R1 HR1 Hfr1 Hms1.
          all: try arm_side.
          all: match goal with |- ?G => idtac "W3" G end.
          symex_reg HR1 (13%bv : reg) as G13. symex_reg HR1 (12%bv : reg) as G12. symex_reg HR1 (14%bv : reg) as G14.
          apply (WIN (32768 - c2) (is_length s) R1); [clear - Hc2 Hcw NW_WR Hwn Hwh Ews; lia | clear - Hlen Hc2 Hcw CL1; lia | clear - Hc2 Hcw NW_WR Hwn Hwh Ews CL1 Hlen; lia
            | replace (mclamp r (is_length s)) with (is_length s) by (unfold mclamp; destruct (Z.ltb_spec (ir_left r) (is_length s)); lia);
              first [rewrite <- (le4_szwrap (is_length s - is_length s)); by_run Hms1 | replace (is_length s - is_length s) with 0 by lia; by_run Hms1 | by_run Hms1]
            | fr_weak Hfr1
            | rewrite G13; f_equal; rewrite ?szwrap32_small by lia; rewrite ?Z.mod_small by lia; lia
            | replace (mclamp r (is_length s)) with (is_length s) by (unfold mclamp; destruct (Z.ltb_spec (ir_left r) (is_length s)); lia); rewrite G12; f_equal; rewrite ?szwrap32_small by lia; rewrite ?Z.mod_small by lia; lia
            | replace (mclamp r (is_length s)) with (is_length s) by (unfold mclamp; destruct (Z.ltb_spec (ir_left r) (is_length s)); lia); rewrite G14; f_equal; rewrite ?szwrap32_small by lia; rewrite ?Z.mod_small by lia; lia ].
          -- idtac.
          arm_symex ilMS 40%nat [false; false; true; false; false; false] [RVal (EVar 45%nat); RVal (EVar 42%nat); RVal (EVar 46%nat); RVal (EVar 47%nat); RVal (ELit 32768); RVal (EVar 48%nat); RVal (EVar 49%nat)] (@nil (Z * expr)) [(45%nat, 32769); (46%nat, 32769); (47%nat, 32769); (48%nat, 259); (49%nat, 2 ^ 63)] v r [is_offset s; is_whave s; is_wnext s; is_length s; cv_WB v] NoVals F0
            (mkst R (Z_to_bv 64 0x1e828) M s6_rom) R1 HR1 Hfr1 Hms1.
          all: try arm_side.
          all: match goal with |- ?G => idtac "W4" G end.
          symex_reg HR1 (13%bv : reg) as G13. symex_reg HR1 (12%bv : reg) as G12. symex_reg HR1 (14%bv : reg) as G14.
          apply (WIN (32768 - c2) (is_length s) R1); [clear - Hc2 Hcw NW_WR Hwn Hwh Ews; lia | clear - Hlen Hc2 Hcw CL1; lia | clear - Hc2 Hcw NW_WR Hwn Hwh Ews CL1 Hlen; lia
            | replace (mclamp r (is_length s)) with (ir_left r) by (unfold mclamp; destruct (Z.ltb_spec (ir_left r) (is_length s)); lia);
              first [rewrite <- (le4_szwrap (is_length s - ir_left r)); by_run Hms1 | replace (is_length s - ir_left r) with 0 by lia; by_run Hms1 | by_run Hms1]
            | fr_weak Hfr1
            | rewrite G13; f_equal; rewrite ?szwrap32_small by lia; rewrite ?Z.mod_small by lia; lia
            | replace (mclamp r (is_length s)) with (ir_left r) by (unfold mclamp; destruct (Z.ltb_spec (ir_left r) (is_length s)); lia); rewrite G12; f_equal; rewrite ?szwrap32_small by lia; rewrite ?Z.mod_small by lia; lia
            | replace (mclamp r (is_length s)) with (ir_left r) by (unfold mclamp; destruct (Z.ltb_spec (ir_left r) (is_length s)); lia); rewrite G14; f_equal; rewrite ?szwrap32_small by lia; rewrite ?Z.mod_small by lia; lia ].
  Qed.
End MatchWinWrap.
End FXG.
