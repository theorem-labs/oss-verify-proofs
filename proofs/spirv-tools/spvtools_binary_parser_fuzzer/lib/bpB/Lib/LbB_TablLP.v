(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HWord.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require TablLib TablStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsWalk.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablData TablGrammar TablRep TablByValue.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_RGl LbB_Own LbB_TablStmt LbB_TablImg.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_TablLO LbB_TablAcc LbB_TablSpec LbB_TablLX.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition LP_HEAD : Z := 0xfe6a0.
Definition LP_EXIT : Z := 0xfe728.
Definition LP_RET  : Z := 0xfe780.
Definition PB : Z := 0x48260.
Definition NOP : Z := 1245.

#[local] Abbreviation V := (VAL OPND).

Lemma NOP_eq : Zlen OPND = NOP. Proof. reflexivity. Qed.

Lemma OPND_cellA : forall m j, tvis m -> 0 <= j < NOP -> cell4 ASEGS m (PB + 52 * j) (V j).
Proof.
  intros m j TV Hj. rewrite <- NOP_eq in Hj.
  destruct (opnd_cell ASEGS LYT_A tiA rodataA IFXA m j (tvis_ro m TV) Hj) as (C & _ & _). exact C.
Qed.

Lemma OPND_sh0 : forall m j k, tvis m -> 0 <= j < NOP -> 0 <= k < 4 -> sh0 m (PB + 52 * j + k).
Proof.
  intros m j k (_ & AC) Hj Hk. eapply (sh0_global m 0x48260 64740 80928); [exact AC | exact in_g_opnd | lia |].
  change (8 * (64740 / 8)) with 64736. unfold PB, NOP in *. lia.
Qed.

Lemma VP_range : forall j, 0 <= j < NOP -> 0 <= V j < 2 ^ 32.
Proof. intros j Hj. rewrite <- NOP_eq in Hj. destruct (VAL_row OPND_KIND OPND opnd_cert j Hj) as (r & _ & _ & HV). exact HV. Qed.

Definition KSLP : list reg := [1; 2; 3; 4; 8; 9; 10; 12; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

Section LB.
  Context {HCEIL : HeapCeil}.
  Variables (M : mem) (ro : word -> option byte) (F : bvmap 5 word) (fc : bv 32) (y f c : Z).
  Hypothesis HTV : tvis M.
  Hypothesis Hy : 0 <= y < 2 ^ 32.
  Hypothesis Hf : 0 <= f.
  Hypothesis Hfc : f + c <= NOP.
  Hypothesis HS : sorted_adj (map v_value (zsub f c OPND)) = true.

  Definition PREG (R : bvmap 5 word) (i len : Z) : Prop :=
    getr R 13 = Z_to_bv 64 (PB + 52 * i) /\ getr R 28 = Z_to_bv 64 len /\ getr R 11 = Z_to_bv 64 (sx32A y) /\
    getr R 15 = Z_to_bv 64 0x7fff8000 /\ getr R 5 = Z_to_bv 64 52 /\ getr R 6 = Z_to_bv 64 (2 ^ 64 - 52).

  Definition PSR : list expr := srs sr_id [(13%bv, EVar 32); (28%bv, EVar 33); (11%bv, EVar 34); (15%bv, ELit 2147450880); (5%bv, ELit 52); (6%bv, ELit (2 ^ 64 - 52))].

  Lemma lp_step : forall R i len,
    f <= i -> 0 < len -> i + len <= f + c -> PREG R i len ->
    let half := len / 2 in
    let i' := (if y <=? V (i + half) then i else i + half + 1) in
    let len' := (if y <=? V (i + half) then half else len - half - 1) in
    exists R', CatSim.msteps asegs (MS R F (Z_to_bv 64 LP_HEAD) fc None M ro)
                 (MS R' F (Z_to_bv 64 (if len' =? 0 then LP_EXIT else LP_HEAD)) fc None M ro)
      /\ PREG R' i' len' /\ kept_in KSLP R R'.
  Proof.
    intros R i len Hi Hlen Hil (H13 & H6 & H11 & H15 & H17 & H6b) half i' len'.
    assert (Hlen5 : len <= 1245) by (unfold NOP in Hfc; lia). assert (Hi5 : i + len <= 1245) by (unfold NOP in Hfc; lia).
    pose proof (half_boundsX len Hlen) as [Hh1 Hh2]. fold half in Hh1, Hh2.
    pose proof (VP_range (i + half) ltac:(unfold NOP in *; lia)) as HV.
    pose proof (OPND_cellA M (i + half) HTV ltac:(unfold NOP in *; lia)) as CELL.
    pose (E := Eseed R [Z_to_bv 64 (PB + 52 * i); Z_to_bv 64 len; Z_to_bv 64 (sx32A y); sxw (V (i + half))]).
    assert (HR : regs_ok E PSR R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs;
      [exact H13 | exact H6 | exact H11 | exact H15 | exact H17 | exact H6b]. }
    assert (HK : know_ok asegs E M
       (kn_fix 4 [LP_HEAD; LP_EXIT] (SCR [false; true; true] [EVar 35] []) LP_HEAD PSR
          [ KRange (EVar 32) PB (PB + 64740); KRange (EVar 33) 1 1245; KAlign (EVar 32) 4 ] 36)).
    { kn_eval. unfold know_ok.
      do 2 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by (unfold PB, NOP in *; lia); unfold PB, NOP in *; lia|]).
      apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by (unfold PB, NOP in *; lia); split; [lia | unfold PB; Z.div_mod_to_equations; lia]|].
      apply Forall_cons; [|apply Forall_nil].
      eapply (kshadow0 _ _ _ (PB + 52 * (i + half))); [evs; zbv_norm; f_equal; subst half; lia | unfold PB, NOP in *; lia |].
      replace (PB + 52 * (i + half)) with (PB + 52 * (i + half) + 0) by lia.
      apply OPND_sh0; [exact HTV | unfold NOP in *; lia | lia]. }
    assert (RD : forall sa, adenot E sa = Z_to_bv 64 (PB + 52 * (i + half)) -> sc_denot asegs M E (SCReadBase sa 4 true (EVar 35))).
    { intros sa Ha. eapply (sc_read_cell4_sx asegs _ _ _ _ _ _ CELL); [exact Ha | evs; reflexivity]. }
    assert (BR : forall b : bool, (if b then y <= V (i + half) else V (i + half) < y) ->
                 sc_denot asegs M E (SCBr b BC_GEU (EVar 35) (EVar 34))).
    { intros b Hb. cbn [sc_denot]. evs. rewrite sxA_sxw by lia. rewrite TablLib.br_geu_sxw by lia. destruct b; bool_lia. }
    Ltac rdtac RD := apply RD; unfold adenot; cbn [a_base a_off]; evs; zbv_norm; rewrite ?v_addi_Z by (unfold PB, NOP in *; lia);
                     f_equal; lia.
    Ltac brz := cbn [sc_denot]; evs; zbv_norm; first [rewrite br_eq by (unfold NOP in *; lia) | rewrite br_ne by (unfold NOP in *; lia)]; bool_lia.
    destruct (Z.leb_spec y (V (i + half))) as [GE|LT].
    - destruct (Z.eqb_spec half 0) as [Hz|Hnz].
      + subst i' len'. rewrite Hz. cbn [Z.eqb].
        xrun_at (PropExec.mkFP F fc) asegs R LP_HEAD M ro HR HK 60%nat [LP_HEAD; LP_EXIT] (SCR [false; true; true] [EVar 35] []) 36%N.
        { split_scs; first [rdtac RD | apply BR; exact GE | idtac].
          all: cbn [sc_denot]; evs; zbv_norm; fold half; first [ rewrite sltu_ge0 by (unfold PB, NOP in *; lia); vm_compute; reflexivity | idtac ]; rewrite Hz; rewrite br_eq by (unfold NOP in *; lia); bool_lia. }
        exists R'. split; [exact Hms|]. split.
        { rreg HR' 13%bv G13. rreg HR' 28%bv G6. rreg HR' 11%bv G11. rreg HR' 15%bv G15. rreg HR' 5%bv G17. rreg HR' 6%bv G6b.
          split; [exact G13|]. split; [rewrite G6; zbv_norm; fold half; rewrite Hz; reflexivity|].
          split; [exact G11|]. split; [exact G15|]. split; [exact G17 | exact G6b]. }
        intros rr Hrr. eapply (syms_id_sound R _ _ R' KSLP HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hrr].
      + subst i' len'. replace (half =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hnz).
        xrun_at (PropExec.mkFP F fc) asegs R LP_HEAD M ro HR HK 60%nat [LP_HEAD; LP_EXIT] (SCR [false; true; false] [EVar 35] []) 36%N.
        { split_scs; first [rdtac RD | apply BR; exact GE | idtac].
          all: cbn [sc_denot]; evs; zbv_norm; fold half; first [ rewrite sltu_ge0 by (unfold PB, NOP in *; lia); vm_compute; reflexivity | idtac ]; rewrite br_eq by (unfold NOP in *; lia); bool_lia. }
        exists R'. split; [exact Hms|]. split.
        { rreg HR' 13%bv G13. rreg HR' 28%bv G6. rreg HR' 11%bv G11. rreg HR' 15%bv G15. rreg HR' 5%bv G17. rreg HR' 6%bv G6b.
          split; [exact G13|]. split; [rewrite G6; zbv_norm; reflexivity|].
          split; [exact G11|]. split; [exact G15|]. split; [exact G17 | exact G6b]. }
        intros rr Hrr. eapply (syms_id_sound R _ _ R' KSLP HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hrr].
    - destruct (Z.eqb_spec (len - half - 1) 0) as [Hz|Hnz].
      + subst i' len'. rewrite Hz. cbn [Z.eqb].
        xrun_at (PropExec.mkFP F fc) asegs R LP_HEAD M ro HR HK 60%nat [LP_HEAD; LP_EXIT] (SCR [false; false; true] [EVar 35] []) 36%N.
        { split_scs; first [rdtac RD | apply BR; exact LT | idtac].
          all: cbn [sc_denot]; evs; zbv_norm; fold half; first [ rewrite sltu_ge0 by (unfold PB, NOP in *; lia); vm_compute; reflexivity | idtac ];
               first [ replace (len + -1 * half + -1) with 0 by lia | replace (len + - (half + 1)) with 0 by lia
                     | replace (len - (half + 1)) with 0 by lia | idtac ];
               rewrite br_eq by (unfold NOP in *; lia); bool_lia. }
        exists R'. split; [exact Hms|]. split.
        { rreg HR' 13%bv G13. rreg HR' 28%bv G6. rreg HR' 11%bv G11. rreg HR' 15%bv G15. rreg HR' 5%bv G17. rreg HR' 6%bv G6b.
          split; [rewrite G13; zbv_norm; fold half; f_equal; lia|].
          split; [rewrite G6; zbv_norm; fold half; f_equal; lia|].
          split; [exact G11|]. split; [exact G15|]. split; [exact G17 | exact G6b]. }
        intros rr Hrr. eapply (syms_id_sound R _ _ R' KSLP HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hrr].
      + subst i' len'. replace (len - half - 1 =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hnz).
        xrun_at (PropExec.mkFP F fc) asegs R LP_HEAD M ro HR HK 60%nat [LP_HEAD; LP_EXIT] (SCR [false; false; false] [EVar 35] []) 36%N.
        { split_scs; first [rdtac RD | apply BR; exact LT | idtac].
          all: cbn [sc_denot]; evs; zbv_norm; fold half; first [ rewrite sltu_ge0 by (unfold PB, NOP in *; lia); vm_compute; reflexivity | idtac ];
               first [ replace (len + -1 * half + -1) with (len - half - 1) by lia | replace (len + - (half + 1)) with (len - half - 1) by lia
                     | replace (len - (half + 1)) with (len - half - 1) by lia | idtac ];
               rewrite br_eq by (unfold NOP in *; lia); bool_lia. }
        exists R'. split; [exact Hms|]. split.
        { rreg HR' 13%bv G13. rreg HR' 28%bv G6. rreg HR' 11%bv G11. rreg HR' 15%bv G15. rreg HR' 5%bv G17. rreg HR' 6%bv G6b.
          split; [rewrite G13; zbv_norm; fold half; f_equal; lia|].
          split; [rewrite G6; zbv_norm; fold half; f_equal; lia|].
          split; [exact G11|]. split; [exact G15|]. split; [exact G17 | exact G6b]. }
        intros rr Hrr. eapply (syms_id_sound R _ _ R' KSLP HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hrr].
  Qed.

  Definition split_atP (i len : Z) : Prop :=
    (forall j, f <= j < i -> V j < y) /\ (forall j, i + len <= j < f + c -> y <= V j).

  Lemma lp_loop : forall (k : nat) R i len,
    len <= Z.of_nat k -> f <= i -> 0 < len -> i + len <= f + c -> split_atP i len -> PREG R i len ->
    exists R' i', CatSim.msteps asegs (MS R F (Z_to_bv 64 LP_HEAD) fc None M ro) (MS R' F (Z_to_bv 64 LP_EXIT) fc None M ro) /\
      PREG R' i' 0 /\ f <= i' <= f + c /\ split_atP i' 0 /\ kept_in KSLP R R'.
  Proof.
    induction k as [|k IH]; intros R i len Hm Hi Hlen Hil [SL SR] HL; [lia|].
    pose proof (half_boundsX len Hlen) as [Hh1 Hh2].
    destruct (lp_step R i len Hi Hlen Hil HL) as (R1 & MS1 & HL1 & K1).
    cbv zeta in MS1, HL1.
    set (half := len / 2) in *.
    destruct (Z.leb_spec y (V (i + half))) as [GE|LT].
    - assert (SPL : split_atP i half).
      { split; [exact SL|]. intros j Hj. destruct (Z.lt_ge_cases j (i + len)); [|apply SR; lia].
        pose proof (VAL_mono OPND_KIND OPND opnd_cert f c (i + half) j Hf ltac:(rewrite NOP_eq; lia) HS ltac:(lia) ltac:(lia) ltac:(lia)). lia. }
      destruct (Z.eqb_spec half 0) as [Hz|Hnz].
      + exists R1, i. split; [exact MS1|]. split; [rewrite Hz in HL1; exact HL1|]. split; [lia|].
        split; [rewrite Hz in SPL; exact SPL | exact K1].
      + destruct (IH R1 i half ltac:(lia) Hi ltac:(lia) ltac:(lia) SPL HL1) as (R' & i' & MS' & P1 & P2 & P3 & K').
        exists R', i'. split; [eapply CatSim.msteps_trans; [exact MS1|exact MS']|].
        split; [exact P1|]. split; [exact P2|]. split; [exact P3 | exact (kept_in_trans _ _ _ _ K1 K')].
    - assert (SPL : split_atP (i + half + 1) (len - half - 1)).
      { split; [|intros j Hj; apply SR; lia]. intros j Hj. destruct (Z.lt_ge_cases j i); [apply SL; lia|].
        pose proof (VAL_mono OPND_KIND OPND opnd_cert f c j (i + half) Hf ltac:(rewrite NOP_eq; lia) HS ltac:(lia) ltac:(lia) ltac:(lia)). lia. }
      destruct (Z.eqb_spec (len - half - 1) 0) as [Hz|Hnz].
      + exists R1, (i + half + 1). split; [exact MS1|]. split; [rewrite Hz in HL1; exact HL1|]. split; [lia|].
        split; [rewrite Hz in SPL; exact SPL | exact K1].
      + destruct (IH R1 (i + half + 1) (len - half - 1) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) SPL HL1) as (R' & i' & MS' & P1 & P2 & P3 & K').
        exists R', i'. split; [eapply CatSim.msteps_trans; [exact MS1|exact MS']|].
        split; [exact P1|]. split; [exact P2|]. split; [exact P3 | exact (kept_in_trans _ _ _ _ K1 K')].
  Qed.
End LB.

Definition KSTP : list reg := [3; 4; 5; 6; 7; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.

Definition LPT_SR : list expr :=
  srs sr_id [(13%bv, EVar 32); (11%bv, EVar 33); (12%bv, EVar 34); (2%bv, EVar 35); (16%bv, EVar 37); (17%bv, EVar 38);
             (10%bv, ELit 18446744073709551607); (15%bv, ELit 2147450880)].

Section Tail.
  Context {HCEIL : HeapCeil}.
  Variables (M : mem) (ro : word -> option byte) (F : bvmap 5 word) (fc : bv 32) (y f c : Z).
  Hypothesis HTV : tvis M.
  Hypothesis Hy : 0 <= y < 2 ^ 32.
  Hypothesis Hf : 0 <= f.
  Hypothesis Hc : 0 < c.
  Hypothesis Hfc : f + c <= NOP.

#[local] Definition HTbATablLP_0 : list kentry := [KWord (SA (EVar 35) 8) 8 (EVar 36); KWr (SA (EVar 34) 0) (ELit 8)].
  Lemma lp_tail : forall R i pd sp (ra : word),
    PREG y R i 0 -> f <= i <= f + c -> getr R 12 = Z_to_bv 64 pd -> getr R 2 = Z_to_bv 64 (sp - 16) ->
    getr R 16 = Z_to_bv 64 c -> getr R 17 = Z_to_bv 64 (PB + 52 * f) -> getr R 10 = Z_to_bv 64 (-9) ->
    rw_cells asegs M (sp - 8) [C8 ra] -> 2 ^ 45 <= sp - 16 -> sp <= 2 ^ 47 ->
    wr_at asegs M pd 8 -> accessible M pd 8 -> pd mod 8 = 0 -> 0x6e8000 <= pd -> pd + 8 <= 2 ^ 47 ->
    (pd + 8 <= sp - 16 \/ sp <= pd) ->
    exists R' M', CatSim.msteps asegs (MS R F (Z_to_bv 64 LP_EXIT) fc None M ro) (MS R' F (Z_to_bv 64 LP_RET) fc None M' ro)
      /\ getr R' 2 = Z_to_bv 64 sp /\ getr R' 1 = ra /\ kept_in KSTP R R'
      /\ munch [(pd, pd + 8)] M M' /\ wmono asegs M M' /\ (forall lo hi, stk asegs M lo hi -> stk asegs M' lo hi)
      /\ ((i < f + c /\ V i = y /\ getr R' 10 = Z_to_bv 64 0 /\ rw_cells asegs M' pd [C8 (Z_to_bv 64 (PB + 52 * i))])
          \/ (~ (i < f + c /\ V i = y) /\ getr R' 10 = Z_to_bv 64 (-9) /\ M' = M)).
  Proof.
    intros R i pd sp ra (H13 & H6 & H11 & H15 & H17' & H6b) Hi H12 H2 H16 H17 H10 RA Hsp0 Hsp1 WP AP P8 P0 P1 PAP.
    pose proof (sh0_of_acc8 M pd AP P8) as SP0.
    set (vi := if i <? f + c then V i else 0).
    pose (E := Eseed R [Z_to_bv 64 (PB + 52 * i); Z_to_bv 64 (sx32A y); Z_to_bv 64 pd; Z_to_bv 64 (sp - 16); ra;
                        Z_to_bv 64 c; Z_to_bv 64 (PB + 52 * f); sxw vi]).
    assert (HR : regs_ok E LPT_SR R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs;
      first [exact H13 | exact H11 | exact H12 | exact H2 | exact H16 | exact H17 | exact H15 | rewrite H10; apply bv_eq; vm_compute; reflexivity]. }
    assert (KRA : kentry_ok asegs E M (KWord (SA (EVar 35) 8) 8 (EVar 36))).
    { eapply (kword_of_rw_cells asegs E M (sp - 8) _ 0%nat (C8 ra)); [exact RA | reflexivity | reflexivity | lia
        | unfold estart; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia | lia | lia | evs; reflexivity]. }
    assert (KPD : kentry_ok asegs E M (KWr (SA (EVar 34) 0) (ELit 8))).
    { eapply kwr_of_wr_at; [exact WP | unfold estart; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia
        | unfold estart, elenZ; evs; rewrite !u64_of_Z by lia; cbn [a_off]; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
    assert (KR : Forall (kentry_ok asegs E M) [KRange (EVar 32) PB (PB + 64740); KRange (EVar 34) 0x6e8000 (2 ^ 47 - 8);
                                              KRange (EVar 35) (2 ^ 45) (2 ^ 47 - 16); KRange (EVar 37) 1 1245;
                                              KRange (EVar 38) PB (PB + 64740); KAlign (EVar 32) 4; KAlign (EVar 34) 8]).
    { repeat (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by (unfold PB, NOP in *; lia); first [unfold PB, NOP in *; lia | split; [lia | first [exact P8 | unfold PB; Z.div_mod_to_equations; lia]]]|]).
      apply Forall_nil. }
    assert (ENDEQ : forall e, edenot E e = Z_to_bv 64 (PB + 52 * (f + c)) ->
                    forall b : bool, (if b then i = f + c else i <> f + c) -> sc_denot asegs M E (SCBr b BC_EQ (EVar 32) e)).
    { intros e He b Hb. cbn [sc_denot]. rewrite He. evs. rewrite br_eq by (unfold PB, NOP in *; lia). destruct b; bool_lia. }
    Ltac endtac ENDEQ := apply ENDEQ; [evs; zbv_norm; f_equal; lia | simpl; lia].
    destruct (Z_lt_le_dec i (f + c)) as [Hlt|Hge].
    - pose proof (VP_range i ltac:(lia)) as HV. pose proof (OPND_cellA M i HTV ltac:(lia)) as CELL.
      assert (Hvi : vi = V i) by (subst vi; destruct (Z.ltb_spec i (f + c)); [reflexivity | lia]).
      assert (RD : sc_denot asegs M E (SCReadBase (SA (EVar 32) 0) 4 true (EVar 39))).
      { eapply (sc_read_cell4_sx asegs _ _ _ _ _ _ CELL); [| evs; rewrite Hvi; reflexivity].
        unfold adenot. cbn [a_base a_off]. evs. rewrite v_addi_Z by (unfold PB, NOP in *; lia). f_equal. lia. }
      assert (SROW : sh0 M (PB + 52 * i)) by (replace (PB + 52 * i) with (PB + 52 * i + 0) by lia; apply OPND_sh0; [exact HTV | lia | lia]).
      assert (NE_END : i <> f + c) by lia.
      destruct (Z.eq_dec (V i) y) as [EQ|NE].
      +
        assert (HK : know_ok asegs E M
           (kn_fix 4 [LP_RET] (SCR [false; false] [EVar 39] []) LP_EXIT LPT_SR
              (HTbATablLP_0 ++
               [KRange (EVar 32) PB (PB + 64740); KRange (EVar 34) 0x6e8000 (2 ^ 47 - 8);
                KRange (EVar 35) (2 ^ 45) (2 ^ 47 - 16); KRange (EVar 37) 1 1245; KRange (EVar 38) PB (PB + 64740); KAlign (EVar 32) 4; KAlign (EVar 34) 8]) 40)).
        { kn_eval. unfold know_ok. apply Forall_cons; [exact KRA|]. apply Forall_cons; [exact KPD|].
          inversion KR as [|? ? K1 KR1]; subst. inversion KR1 as [|? ? K2 KR2]; subst. inversion KR2 as [|? ? K3 KR3]; subst.
          inversion KR3 as [|? ? K4 KR4]; subst. inversion KR4 as [|? ? K5 KR5]; subst. inversion KR5 as [|? ? K6 KR6]; subst. inversion KR6 as [|? ? K7 _]; subst.
          apply Forall_cons; [exact K1|]. apply Forall_cons; [exact K2|]. apply Forall_cons; [exact K3|]. apply Forall_cons; [exact K4|].
          apply Forall_cons; [exact K5|]. apply Forall_cons; [exact K6|]. apply Forall_cons; [exact K7|].
          apply Forall_cons; [eapply kshadow0; [evs; reflexivity | unfold PB, NOP in *; lia | exact SROW]|].
          apply Forall_cons; [eapply kshadow0; [evs; reflexivity | lia | exact SP0]|].
          apply Forall_nil. }
        xrun_at (PropExec.mkFP F fc) asegs R LP_EXIT M ro HR HK 40%nat [LP_RET] (SCR [false; false] [EVar 39] []) 40%N.
        { split_scs; first [exact RD | sc_dj | endtac ENDEQ | idtac].
          cbn [sc_denot]. evs. rewrite Hvi, sxA_sxw by lia. rewrite HLib.br_ne_sxw by lia. rewrite EQ. bool_lia. }
        lazymatch type of Hlf with log_flat _ ?lg =>
          lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
            change mm with (mem_denot E M lg) in Hms; set (M1 := mem_denot E M lg) in Hms end end.
        assert (HB : bv_unsigned (edenot E (EVar 34)) = pd) by (evs; rewrite u64_of_Z by lia; reflexivity).
        assert (WS : forall a, pd <= a -> a + 8 <= pd + 8 -> wr_at asegs M a 8).
        { intros a Ha1 Ha2. destruct WP as (W1 & W2 & W). split; [lia|]. split; [lia|]. intros j Hj.
          replace (a + j) with (pd + (a - pd + j)) by lia. apply W. lia. }
        assert (MU : munch [(pd, pd + 8)] M M1).
        { pose proof (munch_mem_denot_sb [(0, 8)] (EVar 34) E M _ Hlf ltac:(vm_cast_no_check (@eq_refl bool true))) as MU.
          rewrite HB in MU. cbn [map fst snd] in MU. eapply munch_eqW; [exact MU | repeat f_equal; lia]. }
        assert (WM : wmono asegs M M1) by (subst M1; apply wmono_mem_denot).
        assert (CP : rw_cells asegs M1 pd [C8 (Z_to_bv 64 (PB + 52 * i))]) by (subst M1; lgcell2 Hlf HB WS 0%nat).
        exists R', M1. split; [exact Hms|].
        rreg HR' 2%bv G2. rreg HR' 1%bv G1. rreg HR' 10%bv G10.
        split; [rewrite G2, w_add by lia; f_equal; lia|]. split; [exact G1|].
        split; [intros rr Hrr; eapply (syms_id_sound R _ _ R' KSTP HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hrr]|].
        split; [exact MU|]. split; [exact WM|]. split; [intros lo' hi' S; subst M1; apply stk_mem_denot; exact S|].
        left. split; [exact Hlt|]. split; [exact EQ|]. split; [rewrite G10; apply bv_eq; vm_compute; reflexivity | exact CP].
      +
        assert (HK : know_ok asegs E M
           (kn_fix 4 [LP_RET] (SCR [false; true] [EVar 39] []) LP_EXIT LPT_SR
              (HTbATablLP_0 ++
               [KRange (EVar 32) PB (PB + 64740); KRange (EVar 34) 0x6e8000 (2 ^ 47 - 8);
                KRange (EVar 35) (2 ^ 45) (2 ^ 47 - 16); KRange (EVar 37) 1 1245; KRange (EVar 38) PB (PB + 64740); KAlign (EVar 32) 4; KAlign (EVar 34) 8]) 40)).
        { kn_eval. unfold know_ok. apply Forall_cons; [exact KRA|]. apply Forall_cons; [exact KPD|].
          inversion KR as [|? ? K1 KR1]; subst. inversion KR1 as [|? ? K2 KR2]; subst. inversion KR2 as [|? ? K3 KR3]; subst.
          inversion KR3 as [|? ? K4 KR4]; subst. inversion KR4 as [|? ? K5 KR5]; subst. inversion KR5 as [|? ? K6 KR6]; subst. inversion KR6 as [|? ? K7 _]; subst.
          apply Forall_cons; [exact K1|]. apply Forall_cons; [exact K2|]. apply Forall_cons; [exact K3|]. apply Forall_cons; [exact K4|].
          apply Forall_cons; [exact K5|]. apply Forall_cons; [exact K6|]. apply Forall_cons; [exact K7|].
          apply Forall_cons; [eapply kshadow0; [evs; reflexivity | unfold PB, NOP in *; lia | exact SROW]|].
          apply Forall_nil. }
        xrun_at (PropExec.mkFP F fc) asegs R LP_EXIT M ro HR HK 40%nat [LP_RET] (SCR [false; true] [EVar 39] []) 40%N.
        { split_scs; first [exact RD | sc_dj | endtac ENDEQ | idtac].
          cbn [sc_denot]. evs. rewrite Hvi, sxA_sxw by lia. rewrite HLib.br_ne_sxw by lia. bool_lia. }
        cbn [mem_denot] in Hms.
        exists R', M. split; [exact Hms|].
        rreg HR' 2%bv G2. rreg HR' 1%bv G1. rreg HR' 10%bv G10.
        split; [rewrite G2, w_add by lia; f_equal; lia|]. split; [exact G1|].
        split; [intros rr Hrr; eapply (syms_id_sound R _ _ R' KSTP HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hrr]|].
        split; [apply munch_refl|]. split; [intros a Ha; exact Ha|]. split; [intros lo' hi' S; exact S|].
        right. split; [lia|]. split; [rewrite G10; apply bv_eq; vm_compute; reflexivity | reflexivity].
    -
      assert (Hi' : i = f + c) by lia.
      assert (HK : know_ok asegs E M
         (kn_fix 4 [LP_RET] (SCR [true] [EVar 39] []) LP_EXIT LPT_SR
            (HTbATablLP_0 ++
             [KRange (EVar 32) PB (PB + 64740); KRange (EVar 34) 0x6e8000 (2 ^ 47 - 8);
              KRange (EVar 35) (2 ^ 45) (2 ^ 47 - 16); KRange (EVar 37) 1 1245; KRange (EVar 38) PB (PB + 64740); KAlign (EVar 32) 4; KAlign (EVar 34) 8]) 40)).
      { kn_eval. unfold know_ok. apply Forall_cons; [exact KRA|]. apply Forall_cons; [exact KPD|]. exact KR. }
      xrun_at (PropExec.mkFP F fc) asegs R LP_EXIT M ro HR HK 40%nat [LP_RET] (SCR [true] [EVar 39] []) 40%N.
      { split_scs; first [sc_dj | endtac ENDEQ | idtac]. }
      cbn [mem_denot] in Hms.
      exists R', M. split; [exact Hms|].
      rreg HR' 2%bv G2. rreg HR' 1%bv G1. rreg HR' 10%bv G10.
      split; [rewrite G2, w_add by lia; f_equal; lia|]. split; [exact G1|].
      split; [intros rr Hrr; eapply (syms_id_sound R _ _ R' KSTP HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hrr]|].
      split; [apply munch_refl|]. split; [intros a Ha; exact Ha|]. split; [intros lo' hi' S; exact S|].
      right. split; [lia|]. split; [rewrite G10; apply bv_eq; vm_compute; reflexivity | reflexivity].
  Qed.
End Tail.

Definition KSEP : list reg := [3; 4; 7; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 29; 30; 31]%bv.

Definition LPE_SR (e : Z) : list expr := srs sr_id [(10%bv, ELit e); (11%bv, EVar 32); (12%bv, EVar 33); (2%bv, EVar 34); (1%bv, EVar 35)].
Definition LPE_KN : list kentry :=
  [ KWord (SA (ELit 0) AGOT_SHBASE) 8 (ELit ASHBASE_CELL);
    KWord (SA (ELit 0) ASHBASE_CELL) 8 (ELit 0x7fff8000);
    KWr (SA (EVar 34) (-16)) (ELit 16);
    KRange (EVar 34) (2 ^ 45) (2 ^ 47);
    KImg 0x10000 0x91000 ].

Section Entry.
  Context {HCEIL : HeapCeil}.

  Lemma lpe_kn_ok : forall E m (sp lo : Z),
    bv_unsigned (edenot E (EVar 34)) = sp -> stk asegs m lo sp -> lo <= sp - 16 -> 2 ^ 45 <= lo -> sp <= 2 ^ 47 ->
    mem_inv asegs m -> ACONST m -> know_ok asegs E m LPE_KN.
  Proof.
    intros E m sp lo HB ST Hlo Hlo45 Hsp MI AC.
    pose proof (ACONST_shbase m AC) as [CG CS].
    unfold LPE_KN, know_ok.
    apply Forall_cons.
    { eapply (kword_of_rw_cells asegs E m 0x1850a0 _ 0%nat (C8 (wz ASHBASE_CELL))); [exact CG | reflexivity | reflexivity | lia | reflexivity | cbn; lia | cbn; lia | reflexivity]. }
    apply Forall_cons.
    { eapply (kword_of_rw_cells asegs E m 0x191038 _ 0%nat (C8 (wz ASHADOW_BASE))); [exact CS | reflexivity | reflexivity | lia | reflexivity | cbn; lia | cbn; lia | reflexivity]. }
    apply Forall_cons.
    { eapply kwr_of_stk; [exact ST | unfold estart; cbn [a_base a_off]; rewrite HB; lia
                         | unfold estart, elenZ; cbn [a_base a_off]; rewrite HB; evs; rewrite u64_of_Z by lia; lia
                         | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
    apply Forall_cons; [cbn [kentry_ok]; rewrite HB; lia|].
    apply Forall_cons; [apply kimg_of_mem_inv; [exact MI | lia | lia]|].
    apply Forall_nil.
  Qed.

  Lemma lp_entry : forall R F fc m ro (y pd sp lo f c : Z) (ra : word),
    getr R 11 = Z_to_bv 64 (sx32A y) -> getr R 12 = Z_to_bv 64 pd -> getr R 2 = Z_to_bv 64 sp -> getr R 1 = ra ->
    stk asegs m lo sp -> lo <= sp - 16 -> 2 ^ 45 <= lo -> sp <= 2 ^ 47 ->
    (forall E, E = Eseed R [Z_to_bv 64 (sx32A y); Z_to_bv 64 pd; Z_to_bv 64 sp; ra] ->
       exists R' lg, CatSim.msteps asegs (MS R F (Z_to_bv 64 AT_LOOKUP_OPERAND) fc None m ro)
                                         (MS R' F (Z_to_bv 64 LP_HEAD) fc None (mem_denot E m lg) ro)
         /\ lg = [SE (SA (EVar 34) (-8)) 8 (EVar 35)] /\ log_flat E lg
         /\ kept_in KSEP R R' /\ PREG y R' f c /\ getr R' 12 = Z_to_bv 64 pd /\ getr R' 2 = Z_to_bv 64 (sp - 16) /\ getr R' 1 = ra
         /\ getr R' 16 = Z_to_bv 64 c /\ getr R' 17 = Z_to_bv 64 (PB + 52 * f) /\ getr R' 10 = Z_to_bv 64 (-9)) ->
    exists R' m', CatSim.msteps asegs (MS R F (Z_to_bv 64 AT_LOOKUP_OPERAND) fc None m ro) (MS R' F (Z_to_bv 64 LP_HEAD) fc None m' ro)
      /\ PREG y R' f c /\ getr R' 12 = Z_to_bv 64 pd /\ getr R' 2 = Z_to_bv 64 (sp - 16) /\ getr R' 1 = ra /\ kept_in KSEP R R'
      /\ getr R' 16 = Z_to_bv 64 c /\ getr R' 17 = Z_to_bv 64 (PB + 52 * f) /\ getr R' 10 = Z_to_bv 64 (-9)
      /\ munch [(sp - 16, sp)] m m' /\ wmono asegs m m' /\ rw_cells asegs m' (sp - 8) [C8 ra] /\ stk asegs m' lo sp.
  Proof.
    intros R F fc m ro y pd sp lo f c ra H11 H12 H2 H1 ST Hlo Hlo45 Hsp RUN.
    destruct (RUN _ eq_refl) as (R' & lg & MS1 & Hlg & Hlf & KK & XR & G12 & G2 & G1 & G16 & G17 & G10). subst lg.
    set (E := Eseed R [Z_to_bv 64 (sx32A y); Z_to_bv 64 pd; Z_to_bv 64 sp; ra]) in *.
    set (M1 := mem_denot E m [SE (SA (EVar 34) (-8)) 8 (EVar 35)]) in *.
    assert (HB : bv_unsigned (edenot E (EVar 34)) = sp).
    { subst E. evs. rewrite u64_of_Z by lia. reflexivity. }
    assert (WS : forall a, sp - 16 <= a -> a + 8 <= sp -> wr_at asegs m a 8).
    { intros a Ha1 Ha2. pose proof (wr_at_of_stk asegs m lo sp ST) as W. destruct W as (W1 & W2 & W).
      split; [lia|]. split; [lia|]. intros i Hi. replace (a + i) with (lo + (a - lo + i)) by lia. apply W. lia. }
    assert (MU : munch [(sp - 16, sp)] m M1).
    { pose proof (munch_mem_denot_sb [(-16, 0)] (EVar 34) E m _ Hlf ltac:(vm_cast_no_check (@eq_refl bool true))) as MU.
      rewrite HB in MU. cbn [map fst snd] in MU. eapply munch_eqW; [exact MU | repeat f_equal; lia]. }
    assert (WM : wmono asegs m M1) by (subst M1; apply wmono_mem_denot).
    assert (RA : rw_cells asegs M1 (sp - 8) [C8 ra]).
    { subst M1. assert (RAV : edenot E (EVar 35) = ra) by (subst E; evs; reflexivity).
      lgcell2 Hlf HB WS 0%nat. }
    assert (ST1 : stk asegs M1 lo sp) by (subst M1; apply stk_mem_denot; exact ST).
    clearbody M1 E.
    exists R', M1. split; [exact MS1|]. split; [exact XR|]. split; [exact G12|]. split; [exact G2|]. split; [exact G1|].
    split; [exact KK|]. split; [exact G16|]. split; [exact G17|]. split; [exact G10|].
    split; [exact MU|]. split; [exact WM|]. split; [exact RA | exact ST1].
  Qed.
End Entry.

Definition LP_Q (x y pd : Z) (m : mem) : word -> word -> mem -> Prop :=
  fun r0 _ m' => exists r, r0 = Z_to_bv 64 r /\ - 2 ^ 31 <= r < 2 ^ 31
    /\ (r = 0 <-> (exists l, g_operand TG x y = Some l))
    /\ (r = 0 -> exists d, rw_cells asegs m' pd [C8 (Z_to_bv 64 d)] /\ odescA d x y)
    /\ (r <> 0 -> forall a, pd <= a < pd + 8 -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)).

Section Main.
  Context {HCEIL : HeapCeil}.

  Lemma lp_finish : forall (x y pd f c : Z) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
                      (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (R1 : bvmap 5 word) (m1 : mem),
    kind_range OPND_KIND x = (f, c) -> 0 <= f -> 0 < c -> f + c <= NOP -> sorted_adj (map v_value (zsub f c OPND)) = true ->
    0 <= y < 2 ^ 32 ->
    stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - TL_STACK -> bv_unsigned sp <= 2 ^ 47 ->
    mem_inv asegs m -> ACONST m -> pd mod 8 = 0 -> tl_cell m (bv_unsigned sp) pd 8 ->
    CatSim.msteps asegs (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                            F (Z_to_bv 64 AT_LOOKUP_OPERAND) fc None m (seg_rom asegs))
                        (MS R1 F (Z_to_bv 64 LP_HEAD) fc None m1 (seg_rom asegs)) ->
    PREG y R1 f c -> getr R1 12 = Z_to_bv 64 pd -> getr R1 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr R1 1 = ra ->
    kept_in KSEP (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) R1 ->
    getr R1 16 = Z_to_bv 64 c -> getr R1 17 = Z_to_bv 64 (PB + 52 * f) -> getr R1 10 = Z_to_bv 64 (-9) ->
    munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m1 -> wmono asegs m m1 -> rw_cells asegs m1 (bv_unsigned sp - 8) [C8 ra] ->
    stk asegs m1 lo (bv_unsigned sp) ->
    evt asegs (tl_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc TL_STACK [(pd, pd + 8)] lo m (LP_Q x y pd m))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 AT_LOOKUP_OPERAND) fc None m (seg_rom asegs)).
  Proof.
    intros x y pd f c ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo R1 m1
           Hk Hf Hc Hfc HS Hy ST CE LO S47 MI AC P8 (WP & AP & AOK & PAP & PBd) MS1 XR1 G12 G2 G1 K1 G16 G17 G10 MU1 WM1 RA1 ST1.
    pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
    set (spz := bv_unsigned sp) in *.
    assert (Hsp : sp = Z_to_bv 64 spz) by (subst spz; symmetry; apply Z_to_bv_bv_unsigned).
    unfold TL_STACK in *.
    remember (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) as R0 eqn:HR0.
    assert (RF0 : rfull R0) by (rewrite HR0; apply rfull_mkR).
    assert (WIN1 : Forall aconst_ok [(spz - 16, spz)]).
    { apply Forall_cons; [|apply Forall_nil]. apply aconst_ok_high; [replace (sh AIMG_TOP) with 0x800d5000 by reflexivity; lia | right; left; lia]. }
    assert (AC1 : ACONST m1) by exact (ACONST_frame _ _ _ AC MU1 WM1 WIN1).
    assert (MI1 : mem_inv asegs m1) by exact (msteps_mem_inv asegs _ _ MS1 MI).
    assert (TV1 : tvis m1) by (split; assumption).
    assert (SPL0 : split_atP y f c f c) by (split; intros j Hj; lia).
    destruct (lp_loop m1 (seg_rom asegs) F fc y f c TV1 Hy Hf Hfc HS (Z.to_nat c) R1 f c ltac:(lia) ltac:(lia) Hc ltac:(lia) SPL0 XR1)
      as (R2 & i & MS2 & XR2 & Hi & SPL & K2).
    assert (WP1 : wr_at asegs m1 pd 8) by exact (LbB_Own.wr_at_wmono m m1 pd 8 WP WM1).
    assert (AP1 : accessible m1 pd 8).
    { eapply accessible_transport_hi; [exact AP | exact MU1 |]. apply Forall_cons; [|apply Forall_nil]. right. cbn [fst].
      unfold AHI_LO. lia. }
    destruct (lp_tail m1 (seg_rom asegs) F fc y f c TV1 Hy Hf Hc Hfc R2 i pd spz ra XR2 Hi)
      as (R3 & m2 & MS3 & G2' & G1' & K3 & MU3 & WM3 & SK3 & RES);
      [rewrite (K2 12%bv ltac:(inb)); exact G12 | rewrite (K2 2%bv ltac:(inb)); exact G2
      | rewrite (K2 16%bv ltac:(inb)); exact G16 | rewrite (K2 17%bv ltac:(inb)); exact G17 | rewrite (K2 10%bv ltac:(inb)); exact G10
      | exact RA1 | lia | lia | exact WP1 | exact AP1
      | exact P8 | destruct PBd; lia | destruct PBd; lia | lia |].
    assert (MS13 : CatSim.msteps asegs (MS R0 F (Z_to_bv 64 AT_LOOKUP_OPERAND) fc None m (seg_rom asegs))
                                       (MS R3 F (Z_to_bv 64 LP_RET) fc None m2 (seg_rom asegs))).
    { eapply CatSim.msteps_trans; [exact MS1|]. eapply CatSim.msteps_trans; [exact MS2 | exact MS3]. }
    assert (RF3 : rfull R3) by exact (msteps_full asegs _ _ MS13 RF0).
    assert (KK : kept_in KCS R0 R3).
    { eapply kept_in_trans; [eapply kept_in_trans|].
      - eapply kept_in_incl; [exact K1 | vm_cast_no_check (@eq_refl bool true)].
      - eapply kept_in_incl; [exact K2 | vm_cast_no_check (@eq_refl bool true)].
      - eapply kept_in_incl; [exact K3 | vm_cast_no_check (@eq_refl bool true)]. }
    assert (E3 : R3 = mkR ra sp gp tp (getr R3 5) (getr R3 6) (getr R3 7) s0 s1 (getr R3 10) (getr R3 11) (getr R3 12)
                          (getr R3 13) (getr R3 14) (getr R3 15) (getr R3 16) (getr R3 17) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                          (getr R3 28) (getr R3 29) (getr R3 30) (getr R3 31)).
    { rewrite (rfull_eq R3 RF3) at 1.
      rewrite G1', G2', <- Hsp, (KK 3%bv ltac:(inb)), (KK 4%bv ltac:(inb)), (KK 8%bv ltac:(inb)), (KK 9%bv ltac:(inb)),
              (KK 18%bv ltac:(inb)), (KK 19%bv ltac:(inb)), (KK 20%bv ltac:(inb)), (KK 21%bv ltac:(inb)), (KK 22%bv ltac:(inb)),
              (KK 23%bv ltac:(inb)), (KK 24%bv ltac:(inb)), (KK 25%bv ltac:(inb)), (KK 26%bv ltac:(inb)), (KK 27%bv ltac:(inb)).
      subst R0. reflexivity. }
    assert (MI2 : mem_inv asegs m2) by exact (msteps_mem_inv asegs _ _ MS13 MI).
    assert (MU : munch ((spz - 64, spz) :: [(pd, pd + 8)]) m m2).
    { eapply munch_trans; eapply munch_weaken; [| exact MU1 | | exact MU3];
        intros z Hz; cbn [outside] in Hz |- *; lia. }
    assert (WM : wmono asegs m m2) by exact (wmono_trans asegs _ _ _ WM1 WM3).
    assert (ST2 : stk asegs m2 lo spz) by (apply SK3; exact ST1).
    assert (AC2 : ACONST m2).
    { eapply (ACONST_frame _ _ _ AC MU WM). apply Forall_cons; [|apply Forall_cons; [exact AOK | apply Forall_nil]].
      apply aconst_ok_high; [replace (sh AIMG_TOP) with 0x800d5000 by reflexivity; lia | right; left; lia]. }
    eapply evt_of_msteps; [exact MS13|]. rewrite E3.
    step.
    apply evt_done.
    exists (getr R3 5), (getr R3 6), (getr R3 7), (getr R3 10), (getr R3 11), (getr R3 12), (getr R3 13), (getr R3 14),
      (getr R3 15), (getr R3 16), (getr R3 17), (getr R3 28), (getr R3 29), (getr R3 30), (getr R3 31), m2.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI2|]. split; [exact ST2|]. split; [exact AC2|].
    destruct SPL as [SL SR]. rewrite Z.add_0_r in SR.
    destruct RES as [(Hlt & HV & A10 & CP)|(Hno & A10 & HM')].
    - destruct (lbv_found OPND_KIND OPND opnd_cert x f c y i Hk Hf ltac:(lia) ltac:(rewrite NOP_eq; lia) HV SL) as (r & Hfd & Hr).
      exists 0. split; [exact A10|]. split; [lia|]. split.
      { split; [intros _; exists (v_span r); cbn [g_operand TG]; unfold tg_operand, find_opnd; rewrite Hfd; reflexivity | intros _; reflexivity]. }
      split; [|intros C; lia].
      intros _. exists (PB + 52 * i). split; [exact CP|]. exists i, r. split; [exact Hfd | reflexivity].
    - pose proof (lbv_missed OPND_KIND OPND opnd_cert x f c y i Hk Hf ltac:(lia) ltac:(rewrite NOP_eq; lia) HS Hi SL SR Hno) as Hnone.
      exists (-9). split; [exact A10|]. split; [lia|]. split.
      { split; [intros C; lia|]. intros [l Hl]. cbn [g_operand TG] in Hl. unfold tg_operand, find_opnd in Hl. rewrite Hnone in Hl. discriminate. }
      split; [intros C; lia|].
      intros _ a Ha. subst m2. apply MU1. rewrite u64_of_Z by lia. cbn [outside]. lia.
  Qed.

  Lemma lp_none : forall (x y pd : Z) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
                    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (R' : bvmap 5 word) (M1 : mem),
    kind_range OPND_KIND x = (0, 0) -> pd mod 8 = 0 -> tl_cell m (bv_unsigned sp) pd 8 ->
    CatSim.msteps asegs (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                            F (Z_to_bv 64 AT_LOOKUP_OPERAND) fc None m (seg_rom asegs))
                 (MS (mkR ra sp gp tp (getr R' 5) (getr R' 6) (getr R' 7) s0 s1 (getr R' 10) (getr R' 11) (getr R' 12)
                      (getr R' 13) (getr R' 14) (getr R' 15) (getr R' 16) (getr R' 17) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                      (getr R' 28) (getr R' 29) (getr R' 30) (getr R' 31)) F (Z_to_bv 64 LP_RET) fc None M1 (seg_rom asegs)) ->
    munch ((bv_unsigned sp - TL_STACK, bv_unsigned sp) :: []) m M1 -> wmono asegs m M1 -> mem_inv asegs M1 ->
    stk asegs M1 lo (bv_unsigned sp) -> ACONST M1 -> getr R' 10 = Z_to_bv 64 (-9) ->
    evt asegs (tl_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc TL_STACK [(pd, pd + 8)] lo m (LP_Q x y pd m))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 AT_LOOKUP_OPERAND) fc None m (seg_rom asegs)).
  Proof.
    intros x y pd ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo R' M1
           Hk P8 (WP & AP & AOK & PAP & PBd) MS MU WM MI1 ST1 AC1 A10.
    unfold TL_STACK in *.
    eapply evt_of_msteps; [exact MS|].
    step.
    apply evt_done.
    exists (getr R' 5), (getr R' 6), (getr R' 7), (getr R' 10), (getr R' 11), (getr R' 12), (getr R' 13), (getr R' 14),
      (getr R' 15), (getr R' 16), (getr R' 17), (getr R' 28), (getr R' 29), (getr R' 30), (getr R' 31), M1.
    split; [reflexivity|]. split; [eapply munch_weaken; [|exact MU]; intros z Hz; cbn [outside] in Hz |- *; lia|].
    split; [exact WM|]. split; [exact MI1|]. split; [exact ST1|]. split; [exact AC1|].
    exists (-9). split; [exact A10|]. split; [lia|]. split.
    { split; [intros C; lia|]. intros [l Hl]. cbn [g_operand TG] in Hl. unfold tg_operand, find_opnd in Hl.
      rewrite (kind_empty OPND_KIND OPND x y Hk) in Hl. discriminate. }
    split; [intros C; lia|].
    intros _ a Ha. apply MU. rewrite u64_of_Z by (pose proof (bv_unsigned_in_range 64 sp); lia). cbn [outside]. lia.
  Qed.

  Definition lp_goal (x : Z) : Prop :=
    forall (y pd : Z) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - TL_STACK -> bv_unsigned sp <= 2 ^ 47 ->
      mem_inv asegs m -> ACONST m ->
      0 <= x < 2 ^ 32 -> a0 = Z_to_bv 64 x -> a1 = Z_to_bv 64 (sx32A y) -> 0 <= y < 2 ^ 32 -> a2 = Z_to_bv 64 pd ->
      pd mod 8 = 0 -> tl_cell m (bv_unsigned sp) pd 8 ->
      evt asegs (tl_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc TL_STACK [(pd, pd + 8)] lo m (LP_Q x y pd m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AT_LOOKUP_OPERAND) fc None m (seg_rom asegs)).
End Main.

Ltac lp_fin_none E m :=
  lazymatch goal with
  | Hlf : log_flat _ ?lg, Hms : CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _), HR' : regs_ok _ _ ?R' |- _ =>
      change mm with (mem_denot E m lg) in Hms;
      eexists R', _; split; [exact Hms|]; split; [exact Hlf|]; split; [vm_cast_no_check (@eq_refl bool true)|];
      subst E;
      split; [intros rr Hrr; eapply (syms_id_sound _ _ _ R' KCS HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hrr]|];
      let G1 := fresh "G1" in let G2 := fresh "G2" in let G10 := fresh "G10" in
      rreg HR' 1%bv G1; rreg HR' 2%bv G2; rreg HR' 10%bv G10;
      split; [exact G1|]; split; [exact G2|]; rewrite G10; apply bv_eq; vm_compute; reflexivity
  end.

Ltac lp_fin_real E m :=
  lazymatch goal with
  | Hlf : log_flat _ ?lg, Hms : CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _), HR' : regs_ok _ _ ?R' |- _ =>
      change mm with (mem_denot E m lg) in Hms;
      eexists R', _; split; [exact Hms|]; split; [reflexivity|]; split; [exact Hlf|];
      subst E;
      split; [intros rr Hrr; eapply (syms_id_sound _ _ _ R' KSEP HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hrr]|];
      let A13 := fresh "A13" in let A7 := fresh "A7" in let A11 := fresh "A11" in let A15 := fresh "A15" in
      let A17 := fresh "A17" in let A12 := fresh "A12" in let A2 := fresh "A2" in let A1 := fresh "A1" in
      let A16 := fresh "A16" in let A5 := fresh "A5" in let A10 := fresh "A10" in let A6b := fresh "A6b" in
      rreg HR' 13%bv A13; rreg HR' 28%bv A7; rreg HR' 11%bv A11; rreg HR' 15%bv A15; rreg HR' 5%bv A17; rreg HR' 6%bv A6b;
      rreg HR' 12%bv A12; rreg HR' 2%bv A2; rreg HR' 1%bv A1; rreg HR' 16%bv A16; rreg HR' 17%bv A5; rreg HR' 10%bv A10;
      split; [split; [rewrite A13; f_equal; reflexivity|]; split; [rewrite A7; f_equal; reflexivity|];
              split; [exact A11|]; split; [rewrite A15; reflexivity|]; split; [rewrite A17; reflexivity | rewrite A6b; reflexivity]|];
      split; [exact A12|]; split; [rewrite A2, w_addm by lia; reflexivity|]; split; [exact A1|];
      split; [rewrite A16; f_equal; reflexivity|]; split; [rewrite A5; f_equal; reflexivity|];
      rewrite A10; apply bv_eq; vm_compute; reflexivity
  end.

Ltac lp_case :=
  lazymatch goal with
  | ST : stk asegs ?m ?lo (bv_unsigned ?sp), CE : aceil <= ?lo, LO : ?lo <= bv_unsigned ?sp - TL_STACK,
    S47 : bv_unsigned ?sp <= 2 ^ 47, MI : mem_inv asegs ?m, AC : ACONST ?m,
    Ha0 : ?a0 = Z_to_bv 64 ?xv, Ha1 : ?a1 = Z_to_bv 64 (sx32A ?y), Hy : 0 <= ?y < 2 ^ 32, Ha2 : ?a2 = Z_to_bv 64 ?pd,
    P8 : ?pd mod 8 = 0, PC : tl_cell ?m (bv_unsigned ?sp) ?pd 8
    |- evt asegs (tl_post ?ra ?sp ?gp ?tp ?s0 ?s1 ?s2 ?s3 ?s4 ?s5 ?s6 ?s7 ?s8 ?s9 ?s10 ?s11 ?F ?fc _ _ ?lo ?m _)
         (MS (mkR ?ra ?sp ?gp ?tp ?t0 ?t1 ?t2 ?s0 ?s1 ?a0 ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?s2 ?s3 ?s4 ?s5 ?s6 ?s7 ?s8 ?s9 ?s10 ?s11 ?t3 ?t4 ?t5 ?t6)
             ?F _ ?fc None ?m _) =>
    pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4);
    pose proof (bv_unsigned_in_range 64 sp) as Hspr; change (bv_modulus 64) with (2 ^ 64) in Hspr;
    unfold TL_STACK in *;
    pose proof (ACONST_shbase m AC) as [CG CS];
    let fcv := eval vm_compute in (kind_range OPND_KIND xv) in
    lazymatch fcv with
    | (0, 0) =>
        destruct (acc_run AT_LOOKUP_OPERAND LP_RET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                    t3 t4 t5 t6 F fc m lo xv 0 0 (fun r0 _ => r0 = Z_to_bv 64 (-9)) ST CE LO S47 MI AC)
          as (Rr & M1 & MSr & MUr & WMr & MI1 & ST1r & AC1r & P10r);
        [ intros E HE;
          assert (HR : regs_ok E (srs sr_id [(10%bv, ELit xv); (2%bv, EVar 33); (1%bv, EVar 34)])
                         (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6))
            by (subst E; apply regs_ok_srs; [apply regs_ok_seed|];
                repeat apply Forall_cons; try apply Forall_nil; (split; [intros X; discriminate X|]); evs; first [exact Ha0 | reflexivity]);
          assert (HK : know_ok asegs E m (ACC_KN xv xv ++ [KImg 0x10000 0x91000]))
            by (unfold ACC_KN, know_ok; subst E;
                apply Forall_cons;
                [ eapply (kword_of_rw_cells asegs _ m 0x1850a0 _ 0%nat (C8 (wz ASHBASE_CELL))); [exact CG | reflexivity | reflexivity | lia | reflexivity | cbn; lia | cbn; lia | reflexivity] |];
                apply Forall_cons;
                [ eapply (kword_of_rw_cells asegs _ m 0x191038 _ 0%nat (C8 (wz ASHADOW_BASE))); [exact CS | reflexivity | reflexivity | lia | reflexivity | cbn; lia | cbn; lia | reflexivity] |];
                apply Forall_cons;
                [ eapply kwr_of_stk; [exact ST | unfold estart; evs; rewrite ?u64_of_Z by lia; cbn [a_off]; lia
                                     | unfold estart, elenZ; evs; rewrite ?u64_of_Z by lia; cbn [a_off]; lia | unfold elenZ; evs; rewrite ?u64_of_Z by lia; lia] |];
                apply Forall_cons; [cbn [kentry_ok]; evs; lia|];
                apply Forall_cons; [cbn [kentry_ok]; evs; rewrite ?u64_of_Z by lia; lia|];
                apply Forall_cons; [apply kimg_of_mem_inv; [exact MI | lia | lia]|];
                apply Forall_nil);
          change (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 AT_LOOKUP_OPERAND) fc None m (seg_rom asegs))
            with (@PropExec.mkst (PropExec.mkFP F fc) (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     (Z_to_bv 64 AT_LOOKUP_OPERAND) m (seg_rom asegs));
          xrun_at (PropExec.mkFP F fc) asegs (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            AT_LOOKUP_OPERAND m (seg_rom asegs) HR HK 60%nat [LP_RET] (SCR [] [] []) 37%N;
          [ first [ apply Forall_nil | split_scs ] | ];
          lp_fin_none E m
        | eapply lp_none; [reflexivity | exact P8 | exact PC | exact MSr | exact MUr | exact WMr | exact MI1 | exact ST1r | exact AC1r | exact P10r] ]
    | (?fv, ?cv) =>
        let spz := fresh "spz" in let Hsp := fresh "Hsp" in
        set (spz := bv_unsigned sp) in *;
        assert (Hsp : sp = Z_to_bv 64 spz) by (subst spz; symmetry; apply Z_to_bv_bv_unsigned);
        destruct (lp_entry (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F fc m (seg_rom asegs) y pd spz lo fv cv ra)
          as (R1 & m1 & MS1 & XR1 & G12 & G2 & G1 & K1 & G16 & G17 & G10 & MU1 & WM1 & RA1 & ST1);
          [ exact Ha1 | exact Ha2 | exact Hsp | reflexivity | exact ST | lia | lia | lia | | ];
        [ intros E HE;
          assert (HR : regs_ok E (LPE_SR xv) (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6))
            by (subst E; unfold LPE_SR; apply regs_ok_srs; [apply regs_ok_seed|];
                repeat apply Forall_cons; try apply Forall_nil; (split; [intros X; discriminate X|]); evs;
                first [exact Ha0 | exact Ha1 | exact Ha2 | exact Hsp | reflexivity]);
          assert (HK : know_ok asegs E m LPE_KN)
            by (apply (lpe_kn_ok E m spz lo); [subst E; evs; rewrite u64_of_Z by lia; reflexivity | exact ST | lia | lia | lia | exact MI | exact AC]);
          change (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 AT_LOOKUP_OPERAND) fc None m (seg_rom asegs))
            with (@PropExec.mkst (PropExec.mkFP F fc) (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     (Z_to_bv 64 AT_LOOKUP_OPERAND) m (seg_rom asegs));
          xrun_at (PropExec.mkFP F fc) asegs (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            AT_LOOKUP_OPERAND m (seg_rom asegs) HR HK 60%nat [LP_HEAD] (SCR [] [] []) 36%N;
          [ first [ apply Forall_nil | split_scs; try sc_dj ] | ];
          lp_fin_real E m
        | eapply (lp_finish _ y pd fv cv ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                    F fc m lo R1 m1);
          [ reflexivity | lia | lia | unfold NOP; lia | vm_compute; reflexivity | exact Hy | exact ST | exact CE | exact LO | exact S47
          | exact MI | exact AC | exact P8 | exact PC | exact MS1 | exact XR1 | exact G12 | exact G2 | exact G1
          | exact K1 | exact G16 | exact G17 | exact G10 | exact MU1 | exact WM1 | exact RA1 | exact ST1 ] ]
    end
  end.

Lemma lp_big {HCEIL : HeapCeil} : forall x, 108 <= x -> lp_goal x.
Proof.
  intros x X108 y pd ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
         ST CE LO S47 MI AC Hx Ha0 Ha1 Hy Ha2 P8 PC.
  pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
  pose proof (bv_unsigned_in_range 64 sp) as Hspr. change (bv_modulus 64) with (2 ^ 64) in Hspr.
  unfold TL_STACK in *.
  pose proof (ACONST_shbase m AC) as [CG CS].
  destruct (acc_run AT_LOOKUP_OPERAND LP_RET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
              t3 t4 t5 t6 F fc m lo x 0 0 (fun r0 _ => r0 = Z_to_bv 64 (-9)) ST CE LO S47 MI AC)
    as (R' & M1 & MS & MU & WM & MI1 & ST1 & AC1 & P10).
  { intros E HE.
    assert (HR : regs_ok E ACC_SR (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)).
    { subst E. unfold ACC_SR. apply regs_ok_srs; [apply regs_ok_seed|].
      repeat apply Forall_cons; try apply Forall_nil; (split; [intros X; discriminate X|]); evs; first [exact Ha0 | reflexivity]. }
    assert (HK : know_ok asegs E m (ACC_KN 108 4294967295)).
    { unfold ACC_KN, know_ok. subst E.
      apply Forall_cons.
      { eapply (kword_of_rw_cells asegs _ m 0x1850a0 _ 0%nat (C8 (wz ASHBASE_CELL))); [exact CG | reflexivity | reflexivity | lia | reflexivity | cbn; lia | cbn; lia | reflexivity]. }
      apply Forall_cons.
      { eapply (kword_of_rw_cells asegs _ m 0x191038 _ 0%nat (C8 (wz ASHADOW_BASE))); [exact CS | reflexivity | reflexivity | lia | reflexivity | cbn; lia | cbn; lia | reflexivity]. }
      apply Forall_cons.
      { eapply kwr_of_stk; [exact ST | unfold estart; evs; rewrite ?u64_of_Z by lia; cbn [a_off]; lia
                           | unfold estart, elenZ; evs; rewrite ?u64_of_Z by lia; cbn [a_off]; lia | unfold elenZ; evs; rewrite ?u64_of_Z by lia; lia]. }
      apply Forall_cons; [cbn [kentry_ok]; evs; lia|].
      apply Forall_cons; [cbn [kentry_ok]; evs; rewrite ?u64_of_Z by lia; lia|].
      apply Forall_nil. }
    change (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 AT_LOOKUP_OPERAND) fc None m (seg_rom asegs))
      with (@PropExec.mkst (PropExec.mkFP F fc) (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               (Z_to_bv 64 AT_LOOKUP_OPERAND) m (seg_rom asegs)).
    xrun_at (PropExec.mkFP F fc) asegs (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      AT_LOOKUP_OPERAND m (seg_rom asegs) HR HK 40%nat [LP_RET] (SCR [true] [] []) 37%N.
    { first [ apply Forall_nil | split_scs ]. }
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms end end.
    eexists R', _. split; [exact Hms|]. split; [exact Hlf|]. split; [vm_cast_no_check (@eq_refl bool true)|].
    subst E.
    split; [intros rr Hrr; eapply (syms_id_sound _ _ _ R' KCS HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hrr]|].
    rreg HR' 1%bv G1. rreg HR' 2%bv G2. rreg HR' 10%bv G10.
    split; [exact G1|]. split; [exact G2|]. rewrite G10. apply bv_eq. vm_compute. reflexivity. }
  assert (Hk0 : kind_range OPND_KIND x = (0, 0)).
  { unfold kind_range.
    destruct (find (fun k => v_value k =? x) OPND_KIND) as [k|] eqn:EF; [|reflexivity].
    apply find_some in EF as [Hin Eq]. apply Z.eqb_eq in Eq. exfalso.
    assert (HB : forallb (fun k => v_value k <? 108) OPND_KIND = true) by (vm_compute; reflexivity).
    rewrite forallb_forall in HB. specialize (HB k Hin). apply Z.ltb_lt in HB. lia. }
  eapply lp_none; [exact Hk0 | exact P8 | exact PC | exact MS | exact MU | exact WM | exact MI1 | exact ST1 | exact AC1 | exact P10].
Qed.

