(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac WalkTac StoreOk Hoare ShapeAlg SRealizes RefMemcpyLib LibIface LibEff
  SymExec3 SymExec3Sound SymRun3 MmapSim.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablData TablGrammar TablRep TablStmts TablLib TablByValue.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require TablImgP1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module Img := TablImgP1.
Abbreviation SEGS := Plain.M.loaded_segments.
Abbreviation L := Img.Ly.L.
Abbreviation ti := Img.ti.
Abbreviation tc := Img.tc.

Definition LE_ENTRY : Z := 0x6b340.
Definition LE_LOOP  : Z := 0x6b860.
Definition LE_EXIT  : Z := 0x6b884.
Definition LE_RET   : Z := 0x6b8a4.
Definition LE_STOPS : list Z := [LE_LOOP; LE_EXIT; LE_RET].
Definition NEXT : Z := 1245.
Lemma NEXT_eq : Zlen OPND = NEXT. Proof. reflexivity. Qed.
Lemma ext_base_bounds : 0x10000 <= ti_opnd ti /\ ti_opnd ti + 52 * NEXT + 52 <= 2 ^ 40.
Proof. unfold NEXT. cbn [ti_opnd Img.ti]. lia. Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma half_bounds : forall len, 0 < len -> 0 <= len / 2 < len /\ 0 <= len - len / 2 - 1 < len.
Proof. intros len H. lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation V := (VAL OPND).

Section LE.
  Context {fx : FPState}.
Context {AC : AllocCeiling}.
  Variables (M : mem) (y : Z) (f c : Z).
  Hypothesis HRO : ro_clear L M.
  Hypothesis Hy : 0 <= y < 2 ^ 32.
  Hypothesis Hf : 0 <= f.
  Hypothesis Hc : 0 <= c.
  Hypothesis Hfc : f + c <= NEXT.
  Hypothesis HS : sorted_adj (map v_value (zsub f c OPND)) = true.
  #[local] Abbreviation st R pc := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom SEGS)).
  Let base := ti_opnd ti.

  Definition keptX (R R' : bvmap 5 word) : Prop :=
    kept R R' /\ getr R' 10%bv = getr R 10%bv /\ getr R' 11%bv = getr R 11%bv /\ getr R' 12%bv = getr R 12%bv
    /\ getr R' 14%bv = getr R 14%bv /\ getr R' 16%bv = getr R 16%bv /\ getr R' 15%bv = getr R 15%bv.
  Lemma keptX_trans : forall R1 R2 R3, keptX R1 R2 -> keptX R2 R3 -> keptX R1 R3.
  Proof using y Hy. intros R1 R2 R3 (A & B) (D & E). split; [exact (keeps_cs_trans _ _ _ A D) | repeat split; intuition congruence]. Qed.
  Ltac keptX_of HR' :=
    split; [exact (kept_of_syms _ _ _ _ HR' eq_refl)
          | repeat split;
            [ let H := fresh in rreg HR' 10%bv H; first [exact H | rewrite H; symmetry; assumption]
            | let H := fresh in rreg HR' 11%bv H; first [exact H | rewrite H; symmetry; assumption]
            | let H := fresh in rreg HR' 12%bv H; first [exact H | rewrite H; symmetry; assumption]
            | let H := fresh in rreg HR' 14%bv H; first [exact H | rewrite H; symmetry; assumption]
            | let H := fresh in rreg HR' 16%bv H; first [exact H | rewrite H; symmetry; assumption]
            | let H := fresh in rreg HR' 15%bv H; first [exact H | rewrite H; symmetry; assumption] ] ].

  Definition split_at (i len : Z) : Prop :=
    (forall j, f <= j < i -> V j < y) /\ (forall j, i + len <= j < f + c -> y <= V j).

  Lemma lb_step : forall R i len,
    f <= i -> 0 < len -> i + len <= f + c ->
    getr R 13%bv = Z_to_bv 64 (base + 52 * i) -> getr R 5%bv = Z_to_bv 64 len -> getr R 11%bv = Z_to_bv 64 (TablStmts.sx32 y) ->
    getr R 15%bv = Z_to_bv 64 52 ->
    let half := len / 2 in
    let i' := (if y <=? V (i + half) then i else i + half + 1) in
    let len' := (if y <=? V (i + half) then half else len - half - 1) in
    exists R', keptX R R' /\
      msteps SEGS (st R LE_LOOP) (st R' (if len' =? 0 then LE_EXIT else LE_LOOP)) /\
      getr R' 13%bv = Z_to_bv 64 (base + 52 * i') /\ getr R' 5%bv = Z_to_bv 64 len'.
  Proof using fx M y f c HRO Hy Hf Hfc.
    intros R i len Hi Hlen Hil H13 H17 H11 H15 half i' len'.
    pose proof ext_base_bounds as [B0 B1]. pose proof (half_bounds len Hlen) as [Hh1 Hh2].
    pose proof (VAL_row OPND_KIND OPND opnd_cert (i + half)) as VR0. rewrite NEXT_eq in VR0. destruct (VR0 ltac:(lia)) as (r & _ & _ & HV). clear VR0.
    pose proof (opnd_cell SEGS L ti Img.rodata Img.IFX M (i + half) HRO) as CL. rewrite NEXT_eq in CL. destruct (CL ltac:(lia)) as (CELL & _ & _). clear CL.
    pose (E := Eseed R [Z_to_bv 64 (base + 52 * i); Z_to_bv 64 len; Z_to_bv 64 (TablStmts.sx32 y); Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0;
                        sxw (V (i + half))]).
    assert (HR : regs_ok E (srs sr_id [(13%bv, EVar 32); (5%bv, EVar 33); (11%bv, EVar 34); (15%bv, ELit 52)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
    assert (HK : know_ok SEGS E M []) by constructor.
    assert (ADDR : alu64 ALU_ADD (Z_to_bv 64 (base + 52 * i)) (mul_div M_MUL (Z_to_bv 64 52) (alu64 ALU_SRL (Z_to_bv 64 len) (Z_to_bv 64 1)))
                   = Z_to_bv 64 (base + 52 * (i + half))).
    { rewrite w_srl by lia. change (2 ^ 1) with 2. rewrite zbv_mul, zbv_add. f_equal. subst half. lia. }
    assert (RD : sc_denot SEGS M E (SCReadBase (SA (EAlu ALU_ADD (EVar 32) (EMd M_MUL (ELit 52) (EAlu ALU_SRL (EVar 33) (ELit 1)))) 0) 4 true (EVar 40))).
    { eapply (sc_read_cell4_sx _ _ _ _ _ _ _ CELL); [| evs; reflexivity].
      unfold adenot. cbn [a_base a_off]. evs. rewrite ADDR. rewrite v_addi_Z by (unfold NEXT in *; lia). f_equal. lia. }
    assert (FL : sc_denot SEGS M E (SCFlat (SA (EAlu ALU_ADD (EVar 32) (EMd M_MUL (ELit 52) (EAlu ALU_SRL (EVar 33) (ELit 1)))) 0) (ELit 4))).
    { cbn [sc_denot]. unfold flat, estart, elenZ. cbn [a_base a_off edenot]. evs. rewrite ADDR. rewrite !u64_of_Z by (unfold NEXT in *; lia). unfold NEXT in *. lia. }
    assert (BR : forall b : bool, (if b then y <= V (i + half) else V (i + half) < y) ->
                 sc_denot SEGS M E (SCBr b BC_GEU (EVar 40) (EVar 34))).
    { intros b Hb. cbn [sc_denot]. evs. rewrite sx32_sxw by lia. rewrite br_geu_sxw by lia. destruct b; bool_lia. }
    assert (LEN0 : forall b : bool, (if b then len' = 0 else len' <> 0) ->
      sc_denot SEGS M E (SCBr b BC_EQ
         (if y <=? V (i + half) then EAlu ALU_SRL (EVar 33) (ELit 1)
          else EAlu ALU_ADD (EAlu ALU_ADD (EVar 33) (EMd M_MUL (ELit (-1)) (EAlu ALU_SRL (EVar 33) (ELit 1)))) (ELit (-1))) (ELit 0))).
    { intros b Hb. subst len'. cbn [sc_denot]. destruct (Z.leb_spec y (V (i + half))); cbn [sc_denot]; evs;
        rewrite w_srl by lia; change (2 ^ 1) with 2; fold half; rewrite ?zbv_mul, ?zbv_add.
      - rewrite br_eq by lia. destruct b; bool_lia.
      - replace (len + -1 * half + -1) with (len - half - 1) by lia. rewrite br_eq by lia. destruct b; bool_lia. }
    destruct (Z.leb_spec y (V (i + half))) as [GE|LT].
    - destruct (Z.eqb_spec half 0) as [Hz|Hnz].
      + subst i' len'. rewrite Hz. cbn [Z.eqb].
        xrun HR HK 40%nat LE_STOPS (SCR [true; true] [EVar 40] []) 41%N.
        { split_scs; first [exact RD | exact FL | apply BR; exact GE | apply (LEN0 true); exact Hz | sc_auto1]. }
        exists R'. split; [keptX_of HR'|]. split; [exact Hms|].
        rreg HR' 13%bv H13'. rreg HR' 5%bv H17'. rewrite H13', H17'. rewrite w_srl by lia. change (2 ^ 1) with 2. fold half. rewrite Hz. split; reflexivity.
      + subst i' len'. replace (half =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hnz).
        xrun HR HK 40%nat LE_STOPS (SCR [true; false] [EVar 40] []) 41%N.
        { split_scs; first [exact RD | exact FL | apply BR; exact GE | apply (LEN0 false); exact Hnz | sc_auto1]. }
        exists R'. split; [keptX_of HR'|]. split; [exact Hms|].
        rreg HR' 13%bv H13'. rreg HR' 5%bv H17'. rewrite H13', H17'. rewrite w_srl by lia. change (2 ^ 1) with 2. split; reflexivity.
    - destruct (Z.eqb_spec (len - half - 1) 0) as [Hz|Hnz].
      + subst i' len'. rewrite Hz. cbn [Z.eqb].
        xrun HR HK 40%nat LE_STOPS (SCR [false; true] [EVar 40] []) 41%N.
        { split_scs; first [exact RD | exact FL | apply BR; exact LT | apply (LEN0 true); exact Hz | sc_auto1]. }
        exists R'. split; [keptX_of HR'|]. split; [exact Hms|].
        rreg HR' 13%bv H13'. rreg HR' 5%bv H17'. rewrite H13', H17'. rewrite w_srl by lia. change (2 ^ 1) with 2. fold half.
        rewrite !zbv_mul, !zbv_add. split; f_equal; lia.
      + subst i' len'. replace (len - half - 1 =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hnz).
        xrun HR HK 40%nat LE_STOPS (SCR [false; false] [EVar 40] []) 41%N.
        { split_scs; first [exact RD | exact FL | apply BR; exact LT | apply (LEN0 false); exact Hnz | sc_auto1]. }
        exists R'. split; [keptX_of HR'|]. split; [exact Hms|].
        rreg HR' 13%bv H13'. rreg HR' 5%bv H17'. rewrite H13', H17'. rewrite w_srl by lia. change (2 ^ 1) with 2. fold half.
        rewrite !zbv_mul, !zbv_add. split; f_equal; lia.
  Qed.

  Lemma lb_loop : forall (m : nat) R i len,
    len <= Z.of_nat m -> f <= i -> 0 < len -> i + len <= f + c -> split_at i len ->
    getr R 13%bv = Z_to_bv 64 (base + 52 * i) -> getr R 5%bv = Z_to_bv 64 len -> getr R 11%bv = Z_to_bv 64 (TablStmts.sx32 y) ->
    getr R 15%bv = Z_to_bv 64 52 ->
    exists R' i', keptX R R' /\ msteps SEGS (st R LE_LOOP) (st R' LE_EXIT) /\
      getr R' 13%bv = Z_to_bv 64 (base + 52 * i') /\ f <= i' <= f + c /\ split_at i' 0.
  Proof using fx M y f c HRO Hy Hf Hfc HS.
    induction m as [|m IH]; intros R i len Hm Hi Hlen Hil [SL SR] H13 H17 H11 H15; [lia|].
    pose proof (half_bounds len Hlen) as [Hh1 Hh2].
    destruct (lb_step R i len Hi Hlen Hil H13 H17 H11 H15) as (R1 & K1 & MS1 & A13 & A17).
    cbv zeta in MS1, A13, A17.
    set (half := len / 2) in *.
    destruct (Z.leb_spec y (V (i + half))) as [GE|LT].
    - assert (SPL : split_at i half).
      { split; [exact SL|]. intros j Hj. destruct (Z.lt_ge_cases j (i + len)); [|apply SR; lia].
        pose proof (VAL_mono OPND_KIND OPND opnd_cert f c (i + half) j Hf ltac:(rewrite NEXT_eq; lia) HS ltac:(lia) ltac:(lia) ltac:(lia)). lia. }
      destruct (Z.eqb_spec half 0) as [Hz|Hnz].
      + exists R1, i. split; [exact K1|]. split; [exact MS1|]. split; [exact A13|]. split; [lia|]. rewrite Hz in SPL. exact SPL.
      + destruct K1 as (K1 & K1a & K1b & K1c & K1d & K1e & K1f).
        destruct (IH R1 i half ltac:(lia) Hi ltac:(lia) ltac:(lia) SPL A13 A17 ltac:(rewrite K1b; exact H11) ltac:(rewrite K1f; exact H15)) as (R' & i' & K' & MS' & P).
        exists R', i'. split; [exact (keptX_trans _ _ _ (conj K1 (conj K1a (conj K1b (conj K1c (conj K1d (conj K1e K1f)))))) K')|]. split; [eapply msteps_trans; [exact MS1|exact MS']|]. exact P.
    - assert (SPL : split_at (i + half + 1) (len - half - 1)).
      { split; [|intros j Hj; apply SR; lia]. intros j Hj. destruct (Z.lt_ge_cases j i); [apply SL; lia|].
        pose proof (VAL_mono OPND_KIND OPND opnd_cert f c j (i + half) Hf ltac:(rewrite NEXT_eq; lia) HS ltac:(lia) ltac:(lia) ltac:(lia)). lia. }
      destruct (Z.eqb_spec (len - half - 1) 0) as [Hz|Hnz].
      + exists R1, (i + half + 1). split; [exact K1|]. split; [exact MS1|]. split; [exact A13|]. split; [lia|]. rewrite Hz in SPL. exact SPL.
      + destruct K1 as (K1 & K1a & K1b & K1c & K1d & K1e & K1f).
        destruct (IH R1 (i + half + 1) (len - half - 1) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) SPL A13 A17 ltac:(rewrite K1b; exact H11) ltac:(rewrite K1f; exact H15)) as (R' & i' & K' & MS' & P).
        exists R', i'. split; [exact (keptX_trans _ _ _ (conj K1 (conj K1a (conj K1b (conj K1c (conj K1d (conj K1e K1f)))))) K')|]. split; [eapply msteps_trans; [exact MS1|exact MS']|]. exact P.
  Qed.

#[local] Definition HTupOpndP1_0 : list (reg * expr) := [(13%bv, EVar 32); (11%bv, EVar 33); (12%bv, EVar 34); (14%bv, EVar 35); (16%bv, EVar 36); (10%bv, EVar 37)].
  Lemma tail_block : forall R i pd (ret : word),
    f <= i <= f + c -> split_at i 0 ->
    getr R 13%bv = Z_to_bv 64 (base + 52 * i) -> getr R 14%bv = Z_to_bv 64 c -> getr R 16%bv = Z_to_bv 64 (base + 52 * f) ->
    getr R 11%bv = Z_to_bv 64 (TablStmts.sx32 y) -> getr R 12%bv = Z_to_bv 64 pd -> getr R 10%bv = Z_to_bv 64 (-9) ->
    alloc_ceiling <= pd -> pd + 8 <= 2 ^ 47 -> mdef M pd 8 ->
    getr R 1%bv = ret -> ret_ok ret ->
    exists R' M',
      kept R R' /\ msteps SEGS (st R LE_EXIT) (@mkst fx R' ret M' (seg_rom SEGS)) /\
      ( (i < f + c /\ V i = y /\ getr R' 10%bv = Z_to_bv 64 0 /\ M' = wbytes M (Z_to_bv 64 pd) (word_to_le_bytes 8 (Z_to_bv 64 (base + 52 * i))))
      \/ (~ (i < f + c /\ V i = y) /\ getr R' 10%bv = Z_to_bv 64 (-9) /\ M' = M) ).
  Proof using fx AC M y f c HRO Hy Hf Hc Hfc.
    intros R i pd ret Hi [SL SR] H13 H14 H16 H11 H12 H10 Hce Hpd Hdef Hra Hret.
    pose proof ext_base_bounds as [B0 B1]. pose proof ac_bounds_lit as HAC.
    assert (Dpd : defined M pd 8) by (intros k Hk; apply Hdef; lia).
    assert (ENDEQ : alu64 ALU_ADD (mul_div M_MUL (Z_to_bv 64 52) (Z_to_bv 64 c)) (Z_to_bv 64 (base + 52 * f)) = Z_to_bv 64 (base + 52 * (f + c))).
    { rewrite zbv_mul, zbv_add. f_equal. lia. }
    destruct (Z_lt_le_dec i (f + c)) as [Hlt|Hge].
    - pose proof (VAL_row OPND_KIND OPND opnd_cert i) as VR0. rewrite NEXT_eq in VR0. destruct (VR0 ltac:(lia)) as (r & _ & _ & HV). clear VR0.
      pose proof (opnd_cell SEGS L ti Img.rodata Img.IFX M i HRO) as CL. rewrite NEXT_eq in CL. destruct (CL ltac:(lia)) as (CELL & _ & _). clear CL.
      pose (E := Eseed R [Z_to_bv 64 (base + 52 * i); Z_to_bv 64 (TablStmts.sx32 y); Z_to_bv 64 pd; Z_to_bv 64 c; Z_to_bv 64 (base + 52 * f); Z_to_bv 64 (-9); Z_to_bv 64 0; Z_to_bv 64 0; sxw (V i)]).
      assert (HR : regs_ok E (srs sr_id HTupOpndP1_0) R).
      { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
      assert (HK : know_ok SEGS E M [KRange (EVar 34) 1 (2 ^ 47)]).
      { constructor; [|constructor]. eapply krange_var; [evs; reflexivity | lia | lia]. }
      assert (BE : sc_denot SEGS M E (SCBr false BC_EQ (EVar 32) (EAlu ALU_ADD (EMd M_MUL (ELit 52) (EVar 35)) (EVar 36)))).
      { cbn [sc_denot]. evs. rewrite ENDEQ. rewrite br_eq by lia. bool_lia. }
      destruct (Z.eq_dec (V i) y) as [EQ|NE].
      + xrun HR HK 30%nat LE_STOPS (SCR [false; false] [EVar 40] []) 41%N.
        { split_scs; try sc_auto1; first [exact BE | sc_rd_sx CELL | sc_so; rewrite Z.add_0_r; exact Dpd
                                          | cbn [sc_denot]; evs; rewrite sx32_sxw by lia; rewrite br_ne_sxw by lia; bool_lia ]. }
        assert (Hra1 : getr R' 1%bv = ret) by (etransitivity; [apply (kept_of_syms _ _ _ R' HR' eq_refl); (first [solve [clear; cbn; tauto] | cbn; tauto]) | exact Hra]).
        eexists R', _. split; [exact (kept_of_syms _ _ _ _ HR' eq_refl)|]. split.
        { eapply msteps_trans; [exact Hms|]. eapply ret_run; [vm_compute; reflexivity | exact Hra1 | exact Hret]. }
        left. split; [exact Hlt|]. split; [exact EQ|]. split; [rreg HR' 10%bv H10'; exact H10'|].
        evs. rewrite v_addi_Z by lia. rewrite Z.add_0_r. reflexivity.
      + xrun HR HK 30%nat LE_STOPS (SCR [false; true] [EVar 40] []) 41%N.
        { split_scs; try sc_auto1; first [exact BE | sc_rd_sx CELL
                                          | cbn [sc_denot]; evs; rewrite sx32_sxw by lia; rewrite br_ne_sxw by lia; bool_lia ]. }
        assert (Hra1 : getr R' 1%bv = ret) by (etransitivity; [apply (kept_of_syms _ _ _ R' HR' eq_refl); (first [solve [clear; cbn; tauto] | cbn; tauto]) | exact Hra]).
        eexists R', M. split; [exact (kept_of_syms _ _ _ _ HR' eq_refl)|]. split.
        { eapply msteps_trans; [exact Hms|]. eapply ret_run; [vm_compute; reflexivity | exact Hra1 | exact Hret]. }
        right. split; [lia|]. split; [rreg HR' 10%bv H10'; rewrite H10'; apply bv_eq; vm_compute; reflexivity | reflexivity].
    - assert (Hi' : i = f + c) by lia.
      pose (E := Eseed R [Z_to_bv 64 (base + 52 * i); Z_to_bv 64 (TablStmts.sx32 y); Z_to_bv 64 pd; Z_to_bv 64 c; Z_to_bv 64 (base + 52 * f); Z_to_bv 64 (-9)]).
      assert (HR : regs_ok E (srs sr_id HTupOpndP1_0) R).
      { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
      assert (HK : know_ok SEGS E M []) by constructor.
      xrun HR HK 30%nat LE_STOPS (SCR [true] [EVar 40] []) 41%N.
      { split_scs; try sc_auto1. all: cbn [sc_denot]; evs; rewrite ENDEQ; rewrite Hi'; rewrite br_eq by lia; bool_lia. }
      assert (Hra1 : getr R' 1%bv = ret) by (etransitivity; [apply (kept_of_syms _ _ _ R' HR' eq_refl); (first [solve [clear; cbn; tauto] | cbn; tauto]) | exact Hra]).
      eexists R', M. split; [exact (kept_of_syms _ _ _ _ HR' eq_refl)|]. split.
      { eapply msteps_trans; [exact Hms|]. eapply ret_run; [vm_compute; reflexivity | exact Hra1 | exact Hret]. }
      right. split; [lia|]. split; [rreg HR' 10%bv H10'; rewrite H10'; apply bv_eq; vm_compute; reflexivity | reflexivity].
  Qed.
End LE.

Section Post.
  Context {fx : FPState}.
Context {AC : AllocCeiling}.
  Variables (R : bvmap 5 word) (M : mem) (x y pd sp : Z) (ret : word).

  #[local] Notation le_post R' M' r d :=
    (msteps SEGS (@mkst fx R (Z_to_bv 64 (tc_lookup_operand tc)) M (seg_rom SEGS)) (@mkst fx R' ret M' (seg_rom SEGS))
    /\ kept R R' /\ getr R' 10%bv = Z_to_bv 64 r /\ - 2 ^ 31 <= r < 2 ^ 31
    /\ CRep.fld SEGS M' pd 8 d
    /\ (r = 0 <-> (exists l, g_operand TG x y = Some l)) /\ (r = 0 -> odesc ti d x y)
    /\ frame_eq (fun a => zwin pd (pd + 8) a \/ zwin (sp - tc_lookup_stack tc) sp a) M M'
    /\ (forall a : word, M a <> None -> M' a <> None)) (only parsing).

  Lemma post_missed : forall R', find_opnd x y = None -> mdef M pd 8 -> alloc_ceiling <= pd -> pd + 8 <= 2 ^ 47 ->
    msteps SEGS (@mkst fx R (Z_to_bv 64 (tc_lookup_operand tc)) M (seg_rom SEGS)) (@mkst fx R' ret M (seg_rom SEGS)) ->
    kept R R' -> getr R' 10%bv = Z_to_bv 64 (-9) ->
    exists R'' M' r d, le_post R'' M' r d.
  Proof using fx AC R M x y pd sp ret.
    intros R' Hnone Hdef Hce Hpd MS K A10. pose proof ac_bounds_lit.
    destruct (mdef8_fld SEGS M pd Hdef ltac:(lia) ltac:(lia)) as (d0 & _ & Fd0).
    exists R', M, (-9), d0. split; [exact MS|]. split; [exact K|]. split; [exact A10|]. split; [lia|]. split; [exact Fd0|].
    split. { split; [intros C; lia|]. intros [l Hl]. cbn [g_operand TG] in Hl. unfold tg_operand in Hl. rewrite Hnone in Hl. discriminate. }
    split. { intros C; lia. }
    split; [intros a _; reflexivity | intros a Ha; exact Ha].
  Qed.

  Lemma post_found : forall R' i r, find_opnd x y = Some (i, r) -> alloc_ceiling <= pd -> pd + 8 <= 2 ^ 47 ->
    msteps SEGS (@mkst fx R (Z_to_bv 64 (tc_lookup_operand tc)) M (seg_rom SEGS))
                (@mkst fx R' ret (wbytes M (Z_to_bv 64 pd) (word_to_le_bytes 8 (Z_to_bv 64 (ti_opnd ti + 52 * i)))) (seg_rom SEGS)) ->
    kept R R' -> getr R' 10%bv = Z_to_bv 64 0 ->
    exists R'' M' rr d, le_post R'' M' rr d.
  Proof using fx AC R M x y pd sp ret.
    intros R' i r Hf Hce Hpd MS K A10. pose proof ac_bounds_lit.
    exists R', (wbytes M (Z_to_bv 64 pd) (word_to_le_bytes 8 (Z_to_bv 64 (ti_opnd ti + 52 * i)))), 0, (ti_opnd ti + 52 * i).
    split; [exact MS|]. split; [exact K|]. split; [exact A10|]. split; [lia|]. split; [apply fld_wbytes8; lia|].
    split. { split; [|intros; reflexivity]. intros _. exists (v_span r). cbn [g_operand TG]. unfold tg_operand. rewrite Hf. reflexivity. }
    split. { intros _. exists i, r. split; [exact Hf | reflexivity]. }
    split. { apply frame_wbytes8; [lia|lia|]. intros a Ha. left. unfold zwin. lia. }
    intros a Ha. apply defined_wbytes8; [lia|lia|exact Ha].
  Qed.
End Post.

Lemma HKimg_ext : forall E M, ro_clear L M -> know_ok SEGS E M [KImg (ti_ro_lo ti) (ti_ro_hi ti)].
Proof. intros E M HRO. constructor; [|constructor]. apply (kimg_ro SEGS L E M _ _ HRO Img.rodata); cbn; lia. Qed.

Lemma kind_run {AC : AllocCeiling} : forall (fx : FPState) R M x y pd sp (ret : word) R1 f c,
  ro_clear L M -> 0 <= y < 2 ^ 32 -> kind_range OPND_KIND x = (f, c) -> 0 <= f -> 0 < c -> f + c <= NEXT ->
  sorted_adj (map v_value (zsub f c OPND)) = true ->
  alloc_ceiling <= pd -> pd + 8 <= 2 ^ 47 -> mdef M pd 8 -> getr R 1%bv = ret -> ret_ok ret ->
  msteps SEGS (@mkst fx R (Z_to_bv 64 (tc_lookup_operand tc)) M (seg_rom SEGS)) (@mkst fx R1 (Z_to_bv 64 LE_LOOP) M (seg_rom SEGS)) ->
  kept R R1 ->
  getr R1 13%bv = Z_to_bv 64 (ti_opnd ti + 52 * f) -> getr R1 5%bv = Z_to_bv 64 c -> getr R1 11%bv = Z_to_bv 64 (TablStmts.sx32 y) ->
  getr R1 14%bv = Z_to_bv 64 c -> getr R1 16%bv = Z_to_bv 64 (ti_opnd ti + 52 * f) -> getr R1 12%bv = Z_to_bv 64 pd -> getr R1 10%bv = Z_to_bv 64 (-9) ->
  getr R1 15%bv = Z_to_bv 64 52 ->
  exists R' M' r d,
    msteps SEGS (@mkst fx R (Z_to_bv 64 (tc_lookup_operand tc)) M (seg_rom SEGS)) (@mkst fx R' ret M' (seg_rom SEGS))
    /\ kept R R' /\ getr R' 10%bv = Z_to_bv 64 r /\ - 2 ^ 31 <= r < 2 ^ 31
    /\ CRep.fld SEGS M' pd 8 d
    /\ (r = 0 <-> (exists l, g_operand TG x y = Some l)) /\ (r = 0 -> odesc ti d x y)
    /\ frame_eq (fun a => zwin pd (pd + 8) a \/ zwin (sp - tc_lookup_stack tc) sp a) M M'
    /\ (forall a : word, M a <> None -> M' a <> None).
Proof.
  intros fx R M x y pd sp ret R1 f c HRO Hy Hk Hf Hc Hfc HS Hce Hpd Hdef Hra Hret MS1 K1 A13 A17 A11 A14 A16 A12 A10 A15.
  assert (SP0 : split_at y f c f c) by (split; intros j Hj; lia).
  destruct (lb_loop M y f c HRO Hy Hf Hfc HS (Z.to_nat c) R1 f c ltac:(lia) ltac:(lia) Hc ltac:(lia) SP0 A13 A17 A11 A15)
    as (R2 & i & (K2 & K2a & K2b & K2c & K2d & K2e & K2f) & MS2 & B13 & Hi & SPL).
  destruct (tail_block M y f c HRO Hy Hf ltac:(lia) Hfc R2 i pd ret Hi SPL B13
              ltac:(rewrite K2d; exact A14) ltac:(rewrite K2e; exact A16) ltac:(rewrite K2b; exact A11) ltac:(rewrite K2c; exact A12) ltac:(rewrite K2a; exact A10)
              Hce Hpd Hdef ltac:(rewrite K2, K1; [exact Hra | (first [solve [clear; cbn; tauto] | cbn; tauto]) | (first [solve [clear; cbn; tauto] | cbn; tauto])]) Hret) as (R3 & M' & K3 & MS3 & RES).
  assert (KK : kept R R3) by (exact (keeps_cs_trans _ _ _ (keeps_cs_trans _ _ _ K1 K2) K3)).
  assert (MS : msteps SEGS (@mkst fx R (Z_to_bv 64 (tc_lookup_operand tc)) M (seg_rom SEGS)) (@mkst fx R3 ret M' (seg_rom SEGS))).
  { eapply msteps_trans; [exact MS1|]. eapply msteps_trans; [exact MS2|exact MS3]. }
  destruct SPL as [SL SR]. rewrite Z.add_0_r in SR.
  destruct RES as [(Hlt & HV & B10 & HM')|(Hno & B10 & HM')]; subst M'.
  - destruct (lbv_found OPND_KIND OPND opnd_cert x f c y i Hk Hf ltac:(lia) ltac:(rewrite NEXT_eq; lia) HV SL) as (r & Hfd & Hr).
    eapply post_found; [exact Hfd | exact Hce | exact Hpd | exact MS | exact KK | exact B10].
  - pose proof (lbv_missed OPND_KIND OPND opnd_cert x f c y i Hk Hf ltac:(lia) ltac:(rewrite NEXT_eq; lia) HS Hi SL SR Hno) as Hnone.
    eapply post_missed; [exact Hnone | exact Hdef | exact Hce | exact Hpd | exact MS | exact KK | exact B10].
Qed.

Theorem lookup_operand_spec {AC : AllocCeiling} : lookup_operand_stmt SEGS L TG tc (odesc ti).
Proof.
  intros fx R M x y pd sp ret HRO Ha0 Hx _ H3 Hsp Hce Hpd8 Hdef Hal Hdisj Hroom Hcs Hsp47 Hsp16 Hra Hret.
  destruct (H3 eq_refl) as (H11 & Hy & H12). clear H3.
  pose proof ac_bounds_lit as HAC. pose proof ext_base_bounds as [B0 B1].

  assert (Hcases : 108 <= x \/ (0 <= x < 0 + Z.of_nat 108)) by lia.
  destruct Hcases as [X108 | XR].
  - pose (E := Eseed R [Z_to_bv 64 x]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; exact Ha0. }
    assert (HK : know_ok SEGS E M [KRange (EVar 32) 108 4294967295]).
    { constructor; [|constructor]. eapply krange_var; [evs; reflexivity | lia | lia]. }
    xrun HR HK 60%nat LE_STOPS (SCR [] [] []) 41%N. { split_scs; try sc_auto1. }
    assert (Hra1 : getr R' 1%bv = ret) by (etransitivity; [apply (kept_of_syms _ _ _ R' HR' eq_refl); (first [solve [clear; cbn; tauto] | cbn; tauto]) | exact Hra]).
    assert (Hk0 : kind_range OPND_KIND x = (0, 0)).
    { unfold kind_range.
      destruct (find (fun k => v_value k =? x) OPND_KIND) as [k|] eqn:EF; [|reflexivity].
      apply find_some in EF as [Hin Eq]. apply Z.eqb_eq in Eq. exfalso.
      assert (HB : forallb (fun k => v_value k <? 108) OPND_KIND = true) by (vm_compute; reflexivity).
      rewrite forallb_forall in HB. specialize (HB k Hin). apply Z.ltb_lt in HB. lia. }
    eapply (post_missed R M x y pd sp ret R'); [apply (kind_empty OPND_KIND OPND); exact Hk0 | exact Hdef | exact Hce | exact Hpd8 | | exact (kept_of_syms _ _ _ _ HR' eq_refl) | rreg HR' 10%bv H10'; rewrite H10'; apply bv_eq; vm_compute; reflexivity].
    eapply msteps_trans; [exact Hms|]. eapply ret_run; [vm_compute; reflexivity | exact Hra1 | exact Hret].
  -
    enum_range x 0 108%nat XR; lit_in Ha0;
    lazymatch type of Ha0 with getr _ _ = Z_to_bv 64 ?xv =>
      let fc := eval vm_compute in (kind_range OPND_KIND xv) in
      pose (E := Eseed R [Z_to_bv 64 (TablStmts.sx32 y); Z_to_bv 64 pd]);
      assert (HR : regs_ok E (srs sr_id [(10%bv, ELit xv); (11%bv, EVar 32); (12%bv, EVar 33)]) R)
        by (apply regs_ok_srs; [apply regs_ok_seed|]; repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption);
      pose proof (HKimg_ext E M HRO) as HK;
      xrun HR HK 60%nat LE_STOPS (SCR [] [] []) 41%N; [split_scs; try sc_auto1|];
      lazymatch fc with
      | (0, 0) =>
          assert (Hra1 : getr R' 1%bv = ret) by (etransitivity; [apply (kept_of_syms _ _ _ R' HR' eq_refl); (first [solve [clear; cbn; tauto] | cbn; tauto]) | exact Hra]);
          eapply (post_missed R M xv y pd sp ret R');
          [ apply (kind_empty OPND_KIND OPND); reflexivity | exact Hdef | exact Hce | exact Hpd8
          | eapply msteps_trans; [exact Hms|]; eapply ret_run; [vm_compute; reflexivity | exact Hra1 | exact Hret]
          | exact (kept_of_syms _ _ _ _ HR' eq_refl) | rreg HR' 10%bv H10'; rewrite H10'; apply bv_eq; vm_compute; reflexivity ]
      | (?f, ?c) =>
        rreg HR' 13%bv A13; rreg HR' 5%bv A17; rreg HR' 11%bv A11; rreg HR' 14%bv A14; rreg HR' 16%bv A16; rreg HR' 12%bv A12; rreg HR' 10%bv A10; rreg HR' 15%bv A15;
        eapply (kind_run fx R M xv y pd sp ret R' f c HRO Hy eq_refl);
        [ lia | lia | unfold NEXT; lia | vm_compute; reflexivity | exact Hce | exact Hpd8 | exact Hdef | exact Hra | exact Hret
        | exact Hms | exact (kept_of_syms _ _ _ _ HR' eq_refl)
        | rewrite A13; f_equal; reflexivity | exact A17 | exact A11 | exact A14 | rewrite A16; f_equal; reflexivity | exact A12
        | rewrite A10; apply bv_eq; vm_compute; reflexivity | exact A15 ]
      end end.
Qed.
