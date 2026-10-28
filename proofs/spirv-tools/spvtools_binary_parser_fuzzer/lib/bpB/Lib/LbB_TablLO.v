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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require TablLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsWalk.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablData TablGrammar TablRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_RGl LbB_Own LbB_TablStmt LbB_TablImg.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition LO_HEAD : Z := 0xfe024.
Definition LO_EXIT : Z := 0xfe0c0.
Definition LO_RET  : Z := 0xfe124.
Definition IBASE : Z := 0x381c0.
Definition NROWS : Z := 876.

Definition OP (j : Z) : Z := match nth_error INSN (Z.to_nat j) with Some r => i_opcode r | None => 2 ^ 32 end.

Fixpoint sorted_adj (l : list Z) : bool :=
  match l with
  | a :: ((b :: _) as l') => (a <? b) && sorted_adj l'
  | _ => true
  end.

Lemma insn_cert : sorted_adj (map i_opcode INSN) = true /\ forallb (fun r => (0 <=? i_opcode r) && (i_opcode r <? 2 ^ 31)) INSN = true
                  /\ Zlen INSN = NROWS.
Proof. vm_compute. split; [reflexivity | split; reflexivity]. Qed.

Lemma sorted_adj_nth : forall l i a b, sorted_adj l = true ->
  nth_error l i = Some a -> nth_error l (S i) = Some b -> a < b.
Proof.
  induction l as [|u l IH]; intros i a b Hs Ha Hb; [destruct i; discriminate|].
  destruct l as [|v l']; [destruct i; cbn in Hb; [discriminate|destruct i; discriminate]|].
  cbn [sorted_adj] in Hs. apply andb_prop in Hs as [H1 H2]. apply Z.ltb_lt in H1.
  destruct i as [|i].
  - cbn in Ha, Hb. injection Ha as <-. injection Hb as <-. exact H1.
  - cbn in Ha, Hb. eapply IH; [exact H2 | exact Ha | exact Hb].
Qed.

Lemma OP_row : forall j, 0 <= j < NROWS -> exists r, nth_error INSN (Z.to_nat j) = Some r /\ OP j = i_opcode r /\ 0 <= OP j < 2 ^ 31.
Proof.
  intros j Hj. pose proof insn_cert as (_ & HB & HL). unfold OP.
  destruct (nth_error INSN (Z.to_nat j)) as [r|] eqn:E.
  - exists r. split; [reflexivity|]. split; [reflexivity|].
    rewrite forallb_forall in HB. specialize (HB r (nth_error_In _ _ E)). apply andb_prop in HB as [A B].
    apply Z.leb_le in A. apply Z.ltb_lt in B. lia.
  - exfalso. apply nth_error_None in E. unfold Zlen in HL. lia.
Qed.

Lemma OP_succ : forall j, 0 <= j -> j + 1 < NROWS -> OP j < OP (j + 1).
Proof.
  intros j Hj Hj1. pose proof insn_cert as (HS & _ & HL).
  destruct (OP_row j ltac:(lia)) as (r & Er & -> & _). destruct (OP_row (j + 1) ltac:(lia)) as (r' & Er' & -> & _).
  apply (sorted_adj_nth (map i_opcode INSN) (Z.to_nat j)); [exact HS| |].
  - rewrite nth_error_map, Er. reflexivity.
  - replace (S (Z.to_nat j)) with (Z.to_nat (j + 1)) by lia. rewrite nth_error_map, Er'. reflexivity.
Qed.

Lemma OP_mono : forall j k, 0 <= j -> j <= k -> k < NROWS -> OP j <= OP k.
Proof.
  intros j k Hj Hjk Hk. replace k with (j + Z.of_nat (Z.to_nat (k - j))) by lia.
  assert (Hm : j + Z.of_nat (Z.to_nat (k - j)) < NROWS) by lia. revert Hm.
  induction (Z.to_nat (k - j)) as [|m IH]; intros Hm; [rewrite Z.add_0_r; lia|].
  pose proof (IH ltac:(lia)). pose proof (OP_succ (j + Z.of_nat m) ltac:(lia) ltac:(lia)).
  replace (j + Z.of_nat (S m)) with (j + Z.of_nat m + 1) by lia. lia.
Qed.

Lemma OP_lt : forall j k, 0 <= j -> j < k -> k < NROWS -> OP j < OP k.
Proof. intros j k Hj Hjk Hk. pose proof (OP_succ j Hj ltac:(lia)). pose proof (OP_mono (j + 1) k ltac:(lia) ltac:(lia) Hk). lia. Qed.

Lemma lb_found : forall x i, 0 <= i < NROWS -> OP i = x -> (forall j, 0 <= j < i -> OP j < x) ->
  exists r, find_insn x = Some (i, r) /\ nth_error INSN (Z.to_nat i) = Some r.
Proof.
  intros x i Hi Hx Hlt. destruct (OP_row i Hi) as (r & Er & EO & _). exists r. split; [|exact Er].
  unfold find_insn. rewrite (find_ix_hit _ INSN (Z.to_nat i) r 0 Er).
  - f_equal. f_equal. lia.
  - apply Z.eqb_eq. congruence.
  - intros m z Hm Hz. apply Z.eqb_neq. pose proof (Hlt (Z.of_nat m) ltac:(lia)) as L1.
    unfold OP in L1. rewrite Nat2Z.id, Hz in L1. lia.
Qed.

Lemma lb_missed : forall x i, 0 <= i <= NROWS -> (forall j, 0 <= j < i -> OP j < x) -> (forall j, i <= j < NROWS -> x <= OP j) ->
  ~ (i < NROWS /\ OP i = x) -> find_insn x = None.
Proof.
  intros x i Hi Hlt Hge Hn. unfold find_insn. apply find_ix_none. intros y Hy. apply Z.eqb_neq.
  destruct (In_nth_error _ _ Hy) as [m Hm].
  assert (HmN : Z.of_nat m < NROWS). { pose proof insn_cert as (_ & _ & HL). unfold Zlen in HL. pose proof (proj1 (nth_error_Some INSN m) ltac:(rewrite Hm; discriminate)). lia. }
  assert (EO : OP (Z.of_nat m) = i_opcode y) by (unfold OP; rewrite Nat2Z.id, Hm; reflexivity).
  rewrite <- EO. destruct (Z.lt_ge_cases (Z.of_nat m) i) as [Hl|Hg].
  - pose proof (Hlt (Z.of_nat m) ltac:(lia)). lia.
  - pose proof (Hge (Z.of_nat m) ltac:(lia)).
    destruct (Z.eq_dec (Z.of_nat m) i) as [E|NE].
    + intros C. apply Hn. rewrite <- E. lia.
    + pose proof (Hge i ltac:(lia)). pose proof (OP_lt i (Z.of_nat m) ltac:(lia) ltac:(lia) HmN).
      assert (OP i <> x) by (intros C; apply Hn; lia). lia.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma half_bounds : forall len, 0 < len -> 0 <= len / 2 < len /\ 0 <= len - len / 2 - 1 < len.
Proof. intros len H. lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma OP_cellA : forall m j, tvis m -> 0 <= j < NROWS -> cell4 ASEGS m (IBASE + 60 * j) (OP j).
Proof.
  intros m j TV Hj. destruct (OP_row j Hj) as (r & Er & EO & Hb).
  pose proof (chk_insn_nth ASEGS tiA 0 INSN (if_insn _ _ IFXA) (Z.to_nat j) r Er) as C. cbn beta iota zeta in C.
  rewrite Z2Nat.id in C by lia. rewrite Z.add_0_l in C. destruct C as (Cw & C0 & _).
  destruct (in_win_bounds tiA _ _ Cw) as [Wlo Whi]. unfold INSN_STRIDE in *.
  destruct (fld_of_chk ASEGS LYT_A tiA rodataA m _ _ (tvis_ro m TV) (if_w0 _ _ IFXA) (if_w1 _ _ IFXA) Wlo ltac:(lia) C0) as [F B].
  rewrite EO. split; [cbn; lia | exact F].
Qed.

Lemma OP_sh0 : forall m j k, tvis m -> 0 <= j < NROWS -> 0 <= k < 60 -> sh0 m (IBASE + 60 * j + k).
Proof.
  intros m j k (_ & AC) Hj Hk. eapply (sh0_global m 0x381c0 52560 65696); [exact AC | exact in_g_insn | lia |].
  change (8 * (52560 / 8)) with 52560. unfold IBASE, NROWS in *. lia.
Qed.

Definition KSLO : list reg := [1; 2; 3; 4; 8; 9; 11; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 29; 30; 31]%bv.

Lemma sltu_ge0 : forall a b, 0 <= b <= a -> a < 2 ^ 64 -> alu64 ALU_SLTU (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 0.
Proof. intros a b Hb Ha. rewrite HWord.w_sltu by lia. replace (a <? b) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. Qed.

Section LB.
  Context {HCEIL : HeapCeil}.
  Variables (M : mem) (ro : word -> option byte) (F : bvmap 5 word) (fc : bv 32) (x : Z).
  Hypothesis HTV : tvis M.
  Hypothesis Hx : 0 <= x < 2 ^ 32.

  Definition LREG (R : bvmap 5 word) (i len : Z) : Prop :=
    getr R 15 = Z_to_bv 64 IBASE /\ getr R 16 = Z_to_bv 64 (60 * i) /\ getr R 6 = Z_to_bv 64 len /\
    getr R 10 = Z_to_bv 64 x /\ getr R 14 = Z_to_bv 64 SHBASE /\ getr R 13 = Z_to_bv 64 60 /\
    getr R 17 = Z_to_bv 64 (2 ^ 64 - 60).

#[local] Definition HTbATablLO_0 : list (reg * expr) := [(15%bv, ELit IBASE); (16%bv, EMd M_MUL (ELit 60) (EVar 32)); (6%bv, EVar 33); (10%bv, EVar 34); (14%bv, ELit SHBASE); (13%bv, ELit 60); (17%bv, ELit (2 ^ 64 - 60))].
  Lemma lb_step : forall R i len,
    0 <= i -> 0 < len -> i + len <= NROWS -> LREG R i len ->
    let half := len / 2 in
    let i' := (if x <=? OP (i + half) then i else i + half + 1) in
    let len' := (if x <=? OP (i + half) then half else len - half - 1) in
    exists R', CatSim.msteps asegs (MS R F (Z_to_bv 64 LO_HEAD) fc None M ro)
                 (MS R' F (Z_to_bv 64 (if len' =? 0 then LO_EXIT else LO_HEAD)) fc None M ro)
      /\ LREG R' i' len' /\ kept_in KSLO R R'.
  Proof.
    intros R i len Hi Hlen Hil (H15 & H16 & H6 & H10 & H14 & H13 & H17) half i' len'.
    pose proof (half_bounds len Hlen) as [Hh1 Hh2]. fold half in Hh1, Hh2.
    pose proof (OP_row (i + half) ltac:(unfold NROWS in *; lia)) as (r & _ & _ & HOP).
    pose proof (OP_cellA M (i + half) HTV ltac:(unfold NROWS in *; lia)) as CELL.
    pose (E := Eseed R [Z_to_bv 64 i; Z_to_bv 64 len; Z_to_bv 64 x; sxw (OP (i + half))]).
    assert (HR : regs_ok E (srs sr_id HTbATablLO_0) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs;
      [exact H15 | rewrite H16, TablLib.zbv_mul; reflexivity | exact H6 | exact H10 | exact H14 | exact H13 | exact H17]. }
    assert (HK : know_ok asegs E M
       (kn_fix 4 [LO_HEAD; LO_EXIT] (SCR [false; true; true] [EVar 35] []) LO_HEAD
          (srs sr_id HTbATablLO_0)
          [ KRange (EVar 32) 0 (NROWS - 1); KRange (EVar 33) 1 NROWS; KRange (EVar 34) 0 (2 ^ 32 - 1) ] 36)).
    { kn_eval. unfold know_ok.
      do 3 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by (unfold NROWS in *; lia); unfold NROWS in *; lia|]).
      apply Forall_cons; [|apply Forall_nil].
      eapply kshadow0 with (x := IBASE + 60 * (i + half) + 0).
      - evs. rewrite HWord.w_srl by (unfold NROWS in *; lia). change (2 ^ 1) with 2. fold half.
        rewrite !TablLib.zbv_mul, !TablLib.zbv_add. f_equal. unfold IBASE. lia.
      - unfold IBASE, NROWS in *. lia.
      - apply OP_sh0; [exact HTV | unfold NROWS in *; lia | lia]. }
    assert (RD : sc_denot asegs M E (SCReadBase (SA (EAlu ALU_ADD (EMd M_MUL (ELit 60) (EVar 32)) (EMd M_MUL (ELit 60) (EAlu ALU_SRL (EVar 33) (ELit 1)))) IBASE) 4 true (EVar 35))).
    { eapply (sc_read_cell4_sx asegs _ _ _ _ _ _ CELL); [| evs; reflexivity].
      unfold adenot. cbn [a_base a_off]. evs. rewrite HWord.w_srl by (unfold NROWS in *; lia). change (2 ^ 1) with 2. fold half.
      rewrite !TablLib.zbv_mul, TablLib.zbv_add. rewrite v_addi_Z by (unfold NROWS in *; lia). f_equal. lia. }
    assert (BR : forall b : bool, (if b then x <= OP (i + half) else OP (i + half) < x) ->
                 sc_denot asegs M E (SCBr b BC_GEU (EVar 35) (EVar 34))).
    { intros b Hb. cbn [sc_denot]. evs. rewrite TablLib.sxw_small by lia. rewrite br_geu by lia. destruct b; bool_lia. }
    destruct (Z.leb_spec x (OP (i + half))) as [GE|LT].
    - destruct (Z.eqb_spec half 0) as [Hz|Hnz].
      + subst i' len'. rewrite Hz. cbn [Z.eqb].
        xrun_at (PropExec.mkFP F fc) asegs R LO_HEAD M ro HR HK 60%nat [LO_HEAD; LO_EXIT] (SCR [false; true; true] [EVar 35] []) 36%N.
        { split_scs; first [exact RD | apply BR; exact GE | idtac].
          all: cbn [sc_denot]; evs; rewrite ?HWord.w_srl by (unfold NROWS in *; lia); change (2 ^ 1) with 2; fold half;
               rewrite ?TablLib.zbv_mul, ?TablLib.zbv_add;
               first [ rewrite sltu_ge0 by (unfold IBASE, NROWS in *; lia); vm_compute; reflexivity
                     | rewrite br_eq by (unfold NROWS in *; lia); bool_lia ]. }
        exists R'. split; [exact Hms|]. split.
        { rreg HR' 15%bv G15. rreg HR' 16%bv G16. rreg HR' 6%bv G6. rreg HR' 10%bv G10. rreg HR' 14%bv G14.
          rreg HR' 13%bv G13. rreg HR' 17%bv G17.
          split; [exact G15|].
          split; [rewrite G16; evs; rewrite ?HWord.w_srl by (unfold NROWS in *; lia); change (2 ^ 1) with 2; fold half;
                  rewrite ?TablLib.zbv_mul, ?TablLib.zbv_add; f_equal; lia|].
          split; [rewrite G6; evs; rewrite ?HWord.w_srl by (unfold NROWS in *; lia); change (2 ^ 1) with 2; fold half;
                  rewrite ?TablLib.zbv_mul, ?TablLib.zbv_add; f_equal; lia|].
          split; [exact G10|]. split; [exact G14|]. split; [exact G13 | exact G17]. }
        intros rr Hrr. eapply (syms_id_sound R _ _ R' KSLO HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hrr].
      + subst i' len'. replace (half =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hnz).
        xrun_at (PropExec.mkFP F fc) asegs R LO_HEAD M ro HR HK 60%nat [LO_HEAD; LO_EXIT] (SCR [false; true; false] [EVar 35] []) 36%N.
        { split_scs; first [exact RD | apply BR; exact GE | idtac].
          all: cbn [sc_denot]; evs; rewrite ?HWord.w_srl by (unfold NROWS in *; lia); change (2 ^ 1) with 2; fold half;
               rewrite ?TablLib.zbv_mul, ?TablLib.zbv_add;
               first [ rewrite sltu_ge0 by (unfold IBASE, NROWS in *; lia); vm_compute; reflexivity
                     | rewrite br_eq by (unfold NROWS in *; lia); bool_lia ]. }
        exists R'. split; [exact Hms|]. split.
        { rreg HR' 15%bv G15. rreg HR' 16%bv G16. rreg HR' 6%bv G6. rreg HR' 10%bv G10. rreg HR' 14%bv G14.
          rreg HR' 13%bv G13. rreg HR' 17%bv G17.
          split; [exact G15|].
          split; [rewrite G16; evs; rewrite ?HWord.w_srl by (unfold NROWS in *; lia); change (2 ^ 1) with 2; fold half;
                  rewrite ?TablLib.zbv_mul, ?TablLib.zbv_add; f_equal; lia|].
          split; [rewrite G6; evs; rewrite ?HWord.w_srl by (unfold NROWS in *; lia); change (2 ^ 1) with 2; fold half;
                  rewrite ?TablLib.zbv_mul, ?TablLib.zbv_add; f_equal; lia|].
          split; [exact G10|]. split; [exact G14|]. split; [exact G13 | exact G17]. }
        intros rr Hrr. eapply (syms_id_sound R _ _ R' KSLO HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hrr].
    - destruct (Z.eqb_spec (len - half - 1) 0) as [Hz|Hnz].
      + subst i' len'. rewrite Hz. cbn [Z.eqb].
        xrun_at (PropExec.mkFP F fc) asegs R LO_HEAD M ro HR HK 60%nat [LO_HEAD; LO_EXIT] (SCR [false; false; true] [EVar 35] []) 36%N.
        { split_scs; first [exact RD | apply BR; exact LT | idtac].
          all: cbn [sc_denot]; evs; rewrite ?HWord.w_srl by (unfold NROWS in *; lia); change (2 ^ 1) with 2; fold half;
               rewrite ?TablLib.zbv_mul, ?TablLib.zbv_add;
               first [ rewrite sltu_ge0 by (unfold IBASE, NROWS in *; lia); vm_compute; reflexivity
                     | rewrite br_eq by (unfold NROWS in *; lia); bool_lia ]. }
        exists R'. split; [exact Hms|]. split.
        { rreg HR' 15%bv G15. rreg HR' 16%bv G16. rreg HR' 6%bv G6. rreg HR' 10%bv G10. rreg HR' 14%bv G14.
          rreg HR' 13%bv G13. rreg HR' 17%bv G17.
          split; [exact G15|].
          split; [rewrite G16; evs; rewrite ?HWord.w_srl by (unfold NROWS in *; lia); change (2 ^ 1) with 2; fold half;
                  rewrite ?TablLib.zbv_mul, ?TablLib.zbv_add; f_equal; lia|].
          split; [rewrite G6; evs; rewrite ?HWord.w_srl by (unfold NROWS in *; lia); change (2 ^ 1) with 2; fold half;
                  rewrite ?TablLib.zbv_mul, ?TablLib.zbv_add; f_equal; lia|].
          split; [exact G10|]. split; [exact G14|]. split; [exact G13 | exact G17]. }
        intros rr Hrr. eapply (syms_id_sound R _ _ R' KSLO HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hrr].
      + subst i' len'. replace (len - half - 1 =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hnz).
        xrun_at (PropExec.mkFP F fc) asegs R LO_HEAD M ro HR HK 60%nat [LO_HEAD; LO_EXIT] (SCR [false; false; false] [EVar 35] []) 36%N.
        { split_scs; first [exact RD | apply BR; exact LT | idtac].
          all: cbn [sc_denot]; evs; rewrite ?HWord.w_srl by (unfold NROWS in *; lia); change (2 ^ 1) with 2; fold half;
               rewrite ?TablLib.zbv_mul, ?TablLib.zbv_add;
               first [ rewrite sltu_ge0 by (unfold IBASE, NROWS in *; lia); vm_compute; reflexivity
                     | rewrite br_eq by (unfold NROWS in *; lia); bool_lia ]. }
        exists R'. split; [exact Hms|]. split.
        { rreg HR' 15%bv G15. rreg HR' 16%bv G16. rreg HR' 6%bv G6. rreg HR' 10%bv G10. rreg HR' 14%bv G14.
          rreg HR' 13%bv G13. rreg HR' 17%bv G17.
          split; [exact G15|].
          split; [rewrite G16; evs; rewrite ?HWord.w_srl by (unfold NROWS in *; lia); change (2 ^ 1) with 2; fold half;
                  rewrite ?TablLib.zbv_mul, ?TablLib.zbv_add; f_equal; lia|].
          split; [rewrite G6; evs; rewrite ?HWord.w_srl by (unfold NROWS in *; lia); change (2 ^ 1) with 2; fold half;
                  rewrite ?TablLib.zbv_mul, ?TablLib.zbv_add; f_equal; lia|].
          split; [exact G10|]. split; [exact G14|]. split; [exact G13 | exact G17]. }
        intros rr Hrr. eapply (syms_id_sound R _ _ R' KSLO HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hrr].
  Qed.
  Definition split_at (i len : Z) : Prop :=
    (forall j, 0 <= j < i -> OP j < x) /\ (forall j, i + len <= j < NROWS -> x <= OP j).

  Lemma lb_loop : forall (k : nat) R i len,
    len <= Z.of_nat k -> 0 <= i -> 0 < len -> i + len <= NROWS -> split_at i len -> LREG R i len ->
    exists R' i', CatSim.msteps asegs (MS R F (Z_to_bv 64 LO_HEAD) fc None M ro) (MS R' F (Z_to_bv 64 LO_EXIT) fc None M ro) /\
      LREG R' i' 0 /\ 0 <= i' <= NROWS /\ split_at i' 0 /\ kept_in KSLO R R'.
  Proof.
    induction k as [|k IH]; intros R i len Hm Hi Hlen Hil [SL SR] HL; [lia|].
    pose proof (half_bounds len Hlen) as [Hh1 Hh2].
    destruct (lb_step R i len Hi Hlen Hil HL) as (R1 & MS1 & HL1 & K1).
    cbv zeta in MS1, HL1.
    set (half := len / 2) in *.
    destruct (Z.leb_spec x (OP (i + half))) as [GE|LT].
    - assert (SPL : split_at i half).
      { split; [exact SL|]. intros j Hj. destruct (Z.lt_ge_cases j (i + len)); [|apply SR; lia].
        pose proof (OP_mono (i + half) j ltac:(lia) ltac:(lia) ltac:(lia)). lia. }
      destruct (Z.eqb_spec half 0) as [Hz|Hnz].
      + exists R1, i. split; [exact MS1|]. split; [rewrite Hz in HL1; exact HL1|]. split; [lia|].
        split; [rewrite Hz in SPL; exact SPL | exact K1].
      + destruct (IH R1 i half ltac:(lia) Hi ltac:(lia) ltac:(lia) SPL HL1) as (R' & i' & MS' & P1 & P2 & P3 & K').
        exists R', i'. split; [eapply CatSim.msteps_trans; [exact MS1|exact MS']|].
        split; [exact P1|]. split; [exact P2|]. split; [exact P3 | exact (kept_in_trans _ _ _ _ K1 K')].
    - assert (SPL : split_at (i + half + 1) (len - half - 1)).
      { split; [|intros j Hj; apply SR; lia]. intros j Hj. destruct (Z.lt_ge_cases j i); [apply SL; lia|].
        pose proof (OP_mono j (i + half) ltac:(lia) ltac:(lia) ltac:(lia)). lia. }
      destruct (Z.eqb_spec (len - half - 1) 0) as [Hz|Hnz].
      + exists R1, (i + half + 1). split; [exact MS1|]. split; [rewrite Hz in HL1; exact HL1|]. split; [lia|].
        split; [rewrite Hz in SPL; exact SPL | exact K1].
      + destruct (IH R1 (i + half + 1) (len - half - 1) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) SPL HL1) as (R' & i' & MS' & P1 & P2 & P3 & K').
        exists R', i'. split; [eapply CatSim.msteps_trans; [exact MS1|exact MS']|].
        split; [exact P1|]. split; [exact P2|]. split; [exact P3 | exact (kept_in_trans _ _ _ _ K1 K')].
  Qed.
End LB.

Definition LO_SR0 : list expr := srs sr_id [(10%bv, EVar 32); (11%bv, EVar 33); (2%bv, EVar 34); (1%bv, EVar 35)].
Definition LO_KN0 : list kentry :=
  [ KWord (SA (ELit 0) AGOT_SHBASE) 8 (ELit ASHBASE_CELL);
    KWord (SA (ELit 0) ASHBASE_CELL) 8 (ELit 0x7fff8000);
    KWr (SA (EVar 34) (-16)) (ELit 16);
    KRange (EVar 34) (2 ^ 45) (2 ^ 47) ].

Definition KSE : list reg := [3; 4; 5; 7; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.

Lemma lo_entry : forall R F fc m ro (x pd sp lo : Z) (ra : word),
  getr R 10 = Z_to_bv 64 x -> getr R 11 = Z_to_bv 64 pd -> getr R 2 = Z_to_bv 64 sp -> getr R 1 = ra ->
  0 <= x < 2 ^ 32 -> stk asegs m lo sp -> lo <= sp - 16 -> 2 ^ 45 <= lo -> sp <= 2 ^ 47 -> ACONST m ->
  exists R' m', CatSim.msteps asegs (MS R F (Z_to_bv 64 AT_LOOKUP_OPCODE) fc None m ro) (MS R' F (Z_to_bv 64 LO_HEAD) fc None m' ro)
    /\ LREG x R' 0 NROWS /\ getr R' 11 = Z_to_bv 64 pd /\ getr R' 2 = Z_to_bv 64 (sp - 16) /\ getr R' 1 = ra /\ kept_in KSE R R'
    /\ munch [(sp - 16, sp)] m m' /\ wmono asegs m m' /\ rw_cells asegs m' (sp - 8) [C8 ra] /\ stk asegs m' lo sp.
Proof.
  intros R F fc m ro x pd sp lo ra H10 H11 H2 H1 Hx ST Hlo Hlo45 Hsp AC.
  pose (E := Eseed R [Z_to_bv 64 x; Z_to_bv 64 pd; Z_to_bv 64 sp; ra]).
  assert (HR : regs_ok E LO_SR0 R).
  { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs;
    [exact H10 | exact H11 | exact H2 | exact H1]. }
  pose proof (ACONST_shbase m AC) as [CG CS].
  assert (HK : know_ok asegs E m LO_KN0).
  { unfold LO_KN0, know_ok.
    apply Forall_cons.
    { eapply (kword_of_rw_cells asegs E m 0x1850a0 _ 0%nat (C8 (wz ASHBASE_CELL))); [exact CG | reflexivity | reflexivity | lia | reflexivity | cbn; lia | cbn; lia | reflexivity]. }
    apply Forall_cons.
    { eapply (kword_of_rw_cells asegs E m 0x191038 _ 0%nat (C8 (wz ASHADOW_BASE))); [exact CS | reflexivity | reflexivity | lia | reflexivity | cbn; lia | cbn; lia | reflexivity]. }
    apply Forall_cons.
    { eapply kwr_of_stk; [exact ST | unfold estart; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia
                         | unfold estart, elenZ; evs; rewrite !u64_of_Z by lia; cbn [a_off]; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
    apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|]. apply Forall_nil. }
  change (MS R F (Z_to_bv 64 AT_LOOKUP_OPCODE) fc None m ro) with (@PropExec.mkst (PropExec.mkFP F fc) R (Z_to_bv 64 AT_LOOKUP_OPCODE) m ro).
  xrun_at (PropExec.mkFP F fc) asegs R AT_LOOKUP_OPCODE m ro HR HK 40%nat [LO_HEAD] (SCR [] [] []) 36%N.
  { split_scs; sc_dj. }
  lazymatch type of Hlf with log_flat _ ?lg =>
    lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
      change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
  assert (HB : bv_unsigned (edenot E (EVar 34)) = sp) by (evs; rewrite u64_of_Z by lia; reflexivity).
  assert (WS : forall a, sp - 16 <= a -> a + 8 <= sp -> wr_at asegs m a 8).
  { intros a Ha1 Ha2. pose proof (wr_at_of_stk asegs m lo sp ST) as W. destruct W as (W1 & W2 & W).
    split; [lia|]. split; [lia|]. intros i Hi. replace (a + i) with (lo + (a - lo + i)) by lia. apply W. lia. }

  assert (MU : munch [(sp - 16, sp)] m M1).
  { pose proof (munch_mem_denot_sb [(-16, 0)] (EVar 34) E m _ Hlf ltac:(vm_cast_no_check (@eq_refl bool true))) as MU.
    rewrite HB in MU. cbn [map fst snd] in MU. eapply munch_eqW; [exact MU | repeat f_equal; lia]. }
  assert (WM : wmono asegs m M1) by (subst M1; apply wmono_mem_denot).
  assert (RA : rw_cells asegs M1 (sp - 8) [C8 ra]) by (subst M1; lgcell2 Hlf HB WS 0%nat).
  assert (ST1 : stk asegs M1 lo sp) by (subst M1; apply stk_mem_denot; exact ST).
  exists R', M1. split; [exact Hms|].
  rreg HR' 15%bv G15. rreg HR' 16%bv G16. rreg HR' 6%bv G6. rreg HR' 10%bv G10. rreg HR' 14%bv G14. rreg HR' 13%bv G13.
  rreg HR' 17%bv G17. rreg HR' 11%bv G11. rreg HR' 2%bv G2. rreg HR' 1%bv G1.
  split; [split; [exact G15|]; split; [exact G16|]; split; [exact G6|]; split; [rewrite G10; reflexivity|];
          split; [exact G14|]; split; [exact G13 | exact G17]|].
  split; [exact G11|]. split; [rewrite G2, w_addm by lia; reflexivity|]. split; [exact G1|].
  split; [intros rr Hrr; eapply (syms_id_sound R _ _ R' KSE HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hrr]|].
  split; [exact MU|]. split; [exact WM|]. split; [exact RA | exact ST1].
Qed.

Lemma sh0_of_acc8 : forall M a, accessible M a 8 -> a mod 8 = 0 -> sh0 M a.
Proof.
  intros M a H A8. destruct (shk_of_accessible M a 8 (a + 7) H ltac:(pose proof (proj1 H); lia)) as (v & K & Hv & Hor).
  assert (Hm : (a + 7) mod 8 = 7) by (rewrite Z.add_mod, A8 by lia; reflexivity).
  assert (v = 0) by lia. subst v.
  unfold sh0, shk in *. replace ((a + 7) / 8) with (a / 8) in K; [exact K|].
  clear - A8. Z.div_mod_to_equations. lia.
Qed.

Definition KST : list reg := [3; 4; 5; 6; 7; 8; 9; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition LO_SRT : list expr := srs sr_id [(15%bv, ELit IBASE); (16%bv, EMd M_MUL (ELit 60) (EVar 32)); (10%bv, EVar 33); (11%bv, EVar 34); (2%bv, EVar 35); (14%bv, ELit SHBASE)].
Definition LO_PD : Z := 0x6e8000.

Section Tail.
  Context {HCEIL : HeapCeil}.
  Variables (M : mem) (ro : word -> option byte) (F : bvmap 5 word) (fc : bv 32) (x : Z).
  Hypothesis HTV : tvis M.
  Hypothesis Hx : 0 <= x < 2 ^ 32.

#[local] Definition HTbATablLO_1 : list kentry := [KWord (SA (EVar 35) 8) 8 (EVar 36); KWr (SA (EVar 34) 0) (ELit 8)].
  Lemma lo_tail : forall R i pd sp (ra : word),
    LREG x R i 0 -> 0 <= i <= NROWS -> getr R 11 = Z_to_bv 64 pd -> getr R 2 = Z_to_bv 64 (sp - 16) ->
    rw_cells asegs M (sp - 8) [C8 ra] -> 2 ^ 45 <= sp - 16 -> sp <= 2 ^ 47 ->
    wr_at asegs M pd 8 -> accessible M pd 8 -> pd mod 8 = 0 -> 0x6e8000 <= pd -> pd + 8 <= 2 ^ 47 ->
    (pd + 8 <= sp - 16 \/ sp <= pd) ->
    exists R' M', CatSim.msteps asegs (MS R F (Z_to_bv 64 LO_EXIT) fc None M ro) (MS R' F (Z_to_bv 64 LO_RET) fc None M' ro)
      /\ getr R' 2 = Z_to_bv 64 sp /\ getr R' 1 = ra /\ kept_in KST R R'
      /\ munch [(pd, pd + 8)] M M' /\ wmono asegs M M' /\ (forall lo hi, stk asegs M lo hi -> stk asegs M' lo hi)
      /\ ((i < NROWS /\ OP i = x /\ getr R' 10 = Z_to_bv 64 0 /\ rw_cells asegs M' pd [C8 (Z_to_bv 64 (IBASE + 60 * i))])
          \/ (~ (i < NROWS /\ OP i = x) /\ getr R' 10 = Z_to_bv 64 (-9) /\ M' = M)).
  Proof.
    intros R i pd sp ra (H15 & H16 & H6 & H10 & H14 & H13 & H17) Hi H11 H2 RA Hsp0 Hsp1 WP AP P8 P0 P1 PAP.
    pose proof (sh0_of_acc8 M pd AP P8) as SP0.
    set (oi := if i <? NROWS then OP i else 0).
    pose (E := Eseed R [Z_to_bv 64 i; Z_to_bv 64 x; Z_to_bv 64 pd; Z_to_bv 64 (sp - 16); ra; sxw oi]).
    assert (HR : regs_ok E LO_SRT R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs;
      [exact H15 | rewrite H16, TablLib.zbv_mul; reflexivity | exact H10 | exact H11 | exact H2 | exact H14]. }
    assert (KRA : kentry_ok asegs E M (KWord (SA (EVar 35) 8) 8 (EVar 36))).
    { eapply (kword_of_rw_cells asegs E M (sp - 8) _ 0%nat (C8 ra)); [exact RA | reflexivity | reflexivity | lia
        | unfold estart; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia | lia | lia | evs; reflexivity]. }
    assert (KPD : kentry_ok asegs E M (KWr (SA (EVar 34) 0) (ELit 8))).
    { eapply kwr_of_wr_at; [exact WP | unfold estart; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia
        | unfold estart, elenZ; evs; rewrite !u64_of_Z by lia; cbn [a_off]; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
    assert (KR : Forall (kentry_ok asegs E M) [KRange (EVar 32) 0 NROWS; KRange (EVar 34) LO_PD (2 ^ 47 - 8);
                                              KRange (EVar 35) (2 ^ 45) (2 ^ 47 - 16); KRange (EVar 33) 0 (2 ^ 32 - 1);
                                              KAlign (EVar 34) 8]).
    { unfold LO_PD in *.
      do 4 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by (unfold NROWS in *; lia); unfold NROWS in *; lia|]).
      apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; split; [lia | exact P8]|].
      apply Forall_nil. }
    assert (HEQ : forall b : bool, (if b then i = NROWS else i < NROWS) ->
                  sc_denot asegs M E (SCBr b BC_EQ (EMd M_MUL (ELit 60) (EVar 32)) (ELit (60 * NROWS)))).
    { intros b Hb. cbn [sc_denot]. evs. rewrite TablLib.zbv_mul. rewrite br_eq by (unfold NROWS in *; lia).
      unfold NROWS in *. destruct b; bool_lia. }
    destruct (Z_lt_le_dec i NROWS) as [Hlt|Hge].
    - pose proof (OP_row i ltac:(lia)) as (r & _ & _ & HOP). pose proof (OP_cellA M i HTV ltac:(lia)) as CELL.
      assert (Hoi : oi = OP i) by (subst oi; destruct (Z.ltb_spec i NROWS); [reflexivity | lia]).
      assert (RD : sc_denot asegs M E (SCReadBase (SA (EMd M_MUL (ELit 60) (EVar 32)) IBASE) 4 true (EVar 37))).
      { eapply (sc_read_cell4_sx asegs _ _ _ _ _ _ CELL); [| evs; rewrite Hoi; reflexivity].
        unfold adenot. cbn [a_base a_off]. evs. rewrite TablLib.zbv_mul, v_addi_Z by (unfold NROWS in *; lia). f_equal. lia. }
      assert (SROW : sh0 M (IBASE + 60 * i)) by (replace (IBASE + 60 * i) with (IBASE + 60 * i + 0) by lia; apply OP_sh0; [exact HTV | lia | lia]).
      destruct (Z.eq_dec (OP i) x) as [EQ|NE].
      +
        assert (HK : know_ok asegs E M
           (kn_fix 4 [LO_RET] (SCR [false; false] [EVar 37] []) LO_EXIT LO_SRT
              (HTbATablLO_1 ++
               [KRange (EVar 32) 0 NROWS; KRange (EVar 34) LO_PD (2 ^ 47 - 8);
                KRange (EVar 35) (2 ^ 45) (2 ^ 47 - 16); KRange (EVar 33) 0 (2 ^ 32 - 1); KAlign (EVar 34) 8]) 38)).
        { kn_eval. unfold know_ok. apply Forall_cons; [exact KRA|]. apply Forall_cons; [exact KPD|].
          inversion KR as [|? ? K1 KR1]; subst. inversion KR1 as [|? ? K2 KR2]; subst. inversion KR2 as [|? ? K3 KR3]; subst.
          inversion KR3 as [|? ? K4 KR4]; subst. inversion KR4 as [|? ? K5 _]; subst.
          apply Forall_cons; [exact K1|]. apply Forall_cons; [exact K2|]. apply Forall_cons; [exact K3|]. apply Forall_cons; [exact K4|].
          apply Forall_cons; [exact K5|].
          apply Forall_cons; [eapply kshadow0; [evs; rewrite TablLib.zbv_mul, TablLib.zbv_add, (Z.add_comm (60 * i)); reflexivity
                                        | unfold IBASE, NROWS in *; lia | exact SROW]|].
          apply Forall_cons; [eapply kshadow0; [evs; reflexivity | lia | exact SP0]|].
          apply Forall_nil. }
        xrun_at (PropExec.mkFP F fc) asegs R LO_EXIT M ro HR HK 40%nat [LO_RET] (SCR [false; false] [EVar 37] []) 38%N.
        { split_scs; first [exact RD | apply HEQ; exact Hlt | sc_dj | idtac].
          cbn [sc_denot]. evs. rewrite Hoi, TablLib.sxw_small by lia. rewrite br_ne by lia. rewrite EQ. bool_lia. }
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
        assert (CP : rw_cells asegs M1 pd [C8 (Z_to_bv 64 (IBASE + 60 * i))]).
        { subst M1. eapply (rw_cells_log_nth_sb _ _ _ 0%nat);
            [ exact Hlf | reflexivity | vm_cast_no_check (@eq_refl bool true) | rewrite HB; lia
            | apply WS; lia | reflexivity | exact I
            | evs; rewrite TablLib.zbv_mul, TablLib.zbv_add, (Z.add_comm (60 * i)); reflexivity ]. }
        exists R', M1. split; [exact Hms|].
        rreg HR' 2%bv G2. rreg HR' 1%bv G1. rreg HR' 10%bv G10.
        split; [rewrite G2, w_add by lia; f_equal; lia|]. split; [exact G1|].
        split; [intros rr Hrr; eapply (syms_id_sound R _ _ R' KST HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hrr]|].
        split; [exact MU|]. split; [exact WM|]. split; [intros lo' hi' S; subst M1; apply stk_mem_denot; exact S|].
        left. split; [exact Hlt|]. split; [exact EQ|]. split; [exact G10 | exact CP].
      +
        assert (HK : know_ok asegs E M
           (kn_fix 4 [LO_RET] (SCR [false; true] [EVar 37] []) LO_EXIT LO_SRT
              (HTbATablLO_1 ++
               [KRange (EVar 32) 0 NROWS; KRange (EVar 34) LO_PD (2 ^ 47 - 8);
                KRange (EVar 35) (2 ^ 45) (2 ^ 47 - 16); KRange (EVar 33) 0 (2 ^ 32 - 1); KAlign (EVar 34) 8]) 38)).
        { kn_eval. unfold know_ok. apply Forall_cons; [exact KRA|]. apply Forall_cons; [exact KPD|].
          inversion KR as [|? ? K1 KR1]; subst. inversion KR1 as [|? ? K2 KR2]; subst. inversion KR2 as [|? ? K3 KR3]; subst.
          inversion KR3 as [|? ? K4 KR4]; subst. inversion KR4 as [|? ? K5 _]; subst.
          apply Forall_cons; [exact K1|]. apply Forall_cons; [exact K2|]. apply Forall_cons; [exact K3|]. apply Forall_cons; [exact K4|].
          apply Forall_cons; [exact K5|].
          apply Forall_cons; [eapply kshadow0; [evs; rewrite TablLib.zbv_mul, TablLib.zbv_add, (Z.add_comm (60 * i)); reflexivity
                                        | unfold IBASE, NROWS in *; lia | exact SROW]|].
          apply Forall_nil. }
        xrun_at (PropExec.mkFP F fc) asegs R LO_EXIT M ro HR HK 40%nat [LO_RET] (SCR [false; true] [EVar 37] []) 38%N.
        { split_scs; first [exact RD | apply HEQ; exact Hlt | sc_dj | idtac].
          cbn [sc_denot]. evs. rewrite Hoi, TablLib.sxw_small by lia. rewrite br_ne by lia. bool_lia. }
        cbn [mem_denot] in Hms.
        exists R', M. split; [exact Hms|].
        rreg HR' 2%bv G2. rreg HR' 1%bv G1. rreg HR' 10%bv G10.
        split; [rewrite G2, w_add by lia; f_equal; lia|]. split; [exact G1|].
        split; [intros rr Hrr; eapply (syms_id_sound R _ _ R' KST HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hrr]|].
        split; [apply munch_refl|]. split; [intros a Ha; exact Ha|]. split; [intros lo' hi' S; exact S|].
        right. split; [lia|]. split; [rewrite G10; apply bv_eq; vm_compute; reflexivity | reflexivity].
    -
      assert (Hi' : i = NROWS) by lia.
      assert (HK : know_ok asegs E M
         (kn_fix 4 [LO_RET] (SCR [true] [EVar 37] []) LO_EXIT LO_SRT
            (HTbATablLO_1 ++
             [KRange (EVar 32) 0 NROWS; KRange (EVar 34) LO_PD (2 ^ 47 - 8);
              KRange (EVar 35) (2 ^ 45) (2 ^ 47 - 16); KRange (EVar 33) 0 (2 ^ 32 - 1); KAlign (EVar 34) 8]) 38)).
      { kn_eval. unfold know_ok. apply Forall_cons; [exact KRA|]. apply Forall_cons; [exact KPD|]. exact KR. }
      xrun_at (PropExec.mkFP F fc) asegs R LO_EXIT M ro HR HK 40%nat [LO_RET] (SCR [true] [EVar 37] []) 38%N.
      { split_scs; first [apply HEQ; exact Hi' | sc_dj | idtac]. }
      cbn [mem_denot] in Hms.
      exists R', M. split; [exact Hms|].
      rreg HR' 2%bv G2. rreg HR' 1%bv G1. rreg HR' 10%bv G10.
      split; [rewrite G2, w_add by lia; f_equal; lia|]. split; [exact G1|].
      split; [intros rr Hrr; eapply (syms_id_sound R _ _ R' KST HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hrr]|].
      split; [apply munch_refl|]. split; [intros a Ha; exact Ha|]. split; [intros lo' hi' S; exact S|].
      right. split; [lia|]. split; [rewrite G10; apply bv_eq; vm_compute; reflexivity | reflexivity].
  Qed.
End Tail.

Lemma kept_in_incl : forall ks ks' R R', kept_in ks R R' ->
  forallb (fun r => existsb (fun y => bv_eqb r y) ks) ks' = true -> kept_in ks' R R'.
Proof.
  intros ks ks' R R' K Hb r Hr. apply K. rewrite forallb_forall in Hb. apply inb_In. exact (Hb r Hr).
Qed.

Definition KCS : list reg := [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

Section Main.
  Context {HCEIL : HeapCeil}.

  Theorem lookup_opcode_okA : lookup_opcode_stmtA.
  Proof.
    intros [[x y] pd] ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
           ST CE LO S16 S47 MI AC PRE.
    destruct PRE as (Hx & Ha0 & Ha1 & _ & P8 & (WP & AP & AOK & PAP & PB)). specialize (Ha1 eq_refl).
    pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
    set (spz := bv_unsigned sp) in *.
    assert (Hsp : sp = Z_to_bv 64 spz) by (subst spz; symmetry; apply Z_to_bv_bv_unsigned).
    unfold TL_STACK in *.
    remember (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) as R0 eqn:HR0.
    assert (RF0 : rfull R0) by (rewrite HR0; apply rfull_mkR).
    destruct (lo_entry R0 F fc m (seg_rom asegs) x pd spz lo ra)
      as (R1 & m1 & MS1 & LR1 & G11 & G2 & G1 & K1 & MU1 & WM1 & RA1 & ST1);
      [subst R0; exact Ha0 | subst R0; exact Ha1 | subst R0; exact Hsp | subst R0; reflexivity | exact Hx | exact ST | lia | lia | lia | exact AC |].
    assert (WIN1 : Forall aconst_ok [(spz - 16, spz)]).
    { apply Forall_cons; [|apply Forall_nil]. apply aconst_ok_high; [replace (sh AIMG_TOP) with 0x800d5000 by reflexivity; lia | right; left; lia]. }
    assert (AC1 : ACONST m1) by exact (ACONST_frame _ _ _ AC MU1 WM1 WIN1).
    assert (MI1 : mem_inv asegs m1) by exact (msteps_mem_inv asegs _ _ MS1 MI).
    assert (TV1 : tvis m1) by (split; assumption).
    assert (SPL0 : split_at x 0 NROWS) by (split; intros j Hj; unfold NROWS in *; lia).
    destruct (lb_loop m1 (seg_rom asegs) F fc x TV1 Hx (Z.to_nat NROWS) R1 0 NROWS ltac:(lia) ltac:(lia) ltac:(unfold NROWS; lia)
                ltac:(lia) SPL0 LR1) as (R2 & i & MS2 & LR2 & Hi & SPL & K2).
    assert (WP1 : wr_at asegs m1 pd 8) by exact (LbB_Own.wr_at_wmono m m1 pd 8 WP WM1).
    assert (AP1 : accessible m1 pd 8).
    { eapply accessible_transport_hi; [exact AP | exact MU1 |]. apply Forall_cons; [|apply Forall_nil]. right. cbn [fst].
      unfold AHI_LO. lia. }
    destruct (lo_tail m1 (seg_rom asegs) F fc x TV1 Hx R2 i pd spz ra LR2 Hi) as (R3 & m2 & MS3 & G2' & G1' & K3 & MU3 & WM3 & SK3 & RES);
      [rewrite (K2 11%bv ltac:(inb)); exact G11 | rewrite (K2 2%bv ltac:(inb)); exact G2 | exact RA1 | lia | lia | exact WP1 | exact AP1
      | exact P8 | destruct PB; lia | destruct PB; lia | lia |].
    assert (MS13 : CatSim.msteps asegs (MS R0 F (Z_to_bv 64 AT_LOOKUP_OPCODE) fc None m (seg_rom asegs))
                                       (MS R3 F (Z_to_bv 64 LO_RET) fc None m2 (seg_rom asegs))).
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
    destruct RES as [(Hlt & HOP & A10 & CP)|(Hno & A10 & HM')].
    - destruct (lb_found x i ltac:(lia) HOP SL) as (r & Hf & Hr).
      exists 0. split; [exact A10|]. split; [lia|]. split.
      { split; [intros _; exists (i_span r); cbn [g_op TG]; unfold tg_op; rewrite Hf; reflexivity | intros _; reflexivity]. }
      split; [|intros C; lia].
      intros _. exists (IBASE + 60 * i). split; [exact CP|]. exists i, r. split; [exact Hf | reflexivity].
    - pose proof (lb_missed x i Hi SL SR Hno) as Hnone.
      exists (-9). split; [exact A10|]. split; [lia|]. split.
      { split; [intros C; lia|]. intros [l Hl]. cbn [g_op TG] in Hl. unfold tg_op in Hl. rewrite Hnone in Hl. discriminate. }
      split; [intros C; lia|].
      intros _ a Ha. subst m2. apply MU1. rewrite u64_of_Z by lia. cbn [outside]. lia.
  Qed.
End Main.
