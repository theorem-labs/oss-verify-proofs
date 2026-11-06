(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac WalkTac StoreOk Hoare ShapeAlg SRealizes RefMemcpyLib LibIface LibEff
  SymExec3 SymExec3Sound SymRun3 MmapSim.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablData TablGrammar TablRep TablStmts TablLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require TablImgU1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module Img := TablImgU1.
Abbreviation SEGS := Ubsan.M.loaded_segments.
Abbreviation L := Img.Ly.L.
Abbreviation ti := Img.ti.
Abbreviation tc := Img.tc.

Definition LO_ENTRY : Z := 0x6c804.
Definition LO_LOOP  : Z := 0x6c838.
Definition LO_EXIT  : Z := 0x6c8b0.
Definition LO_RET   : Z := 0x6c8ec.
Definition LO_TRAP  : Z := 0x6c8ac.
Definition LO_STOPS : list Z := [LO_LOOP; LO_EXIT; LO_RET; LO_TRAP].

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

Lemma OP_cell : forall M j, ro_clear L M -> 0 <= j < NROWS ->
  cell4 SEGS M (ti_insn ti + 60 * j) (OP j).
Proof.
  intros M j HRO Hj. destruct (OP_row j Hj) as (r & Er & EO & Hb).
  pose proof (chk_insn_nth SEGS ti 0 INSN (if_insn _ _ Img.IFX) (Z.to_nat j) r Er) as C. cbn beta iota zeta in C.
  rewrite Z2Nat.id in C by lia. rewrite Z.add_0_l in C. destruct C as (Cw & C0 & _).
  destruct (in_win_bounds ti _ _ Cw) as [Wlo Whi]. unfold INSN_STRIDE in *.
  destruct (fld_of_chk SEGS L ti Img.rodata M _ _ HRO (if_w0 _ _ Img.IFX) (if_w1 _ _ Img.IFX) Wlo ltac:(lia) C0) as [F B].
  rewrite EO. split; [cbn; lia | exact F].
Qed.

Lemma insn_base_bounds : 0x10000 <= ti_insn ti /\ ti_insn ti + 60 * NROWS + 60 <= 2 ^ 40.
Proof. unfold NROWS. cbn [ti_insn Img.ti]. lia. Qed.

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

Lemma addchk_false : forall a k, 0 <= a -> 0 <= k -> a + k < 2 ^ 63 ->
  branch_taken BC_EQ (alu64 ALU_XOR (alu64 ALU_XOR (alu64 ALU_SLTU (Z_to_bv 64 (a + k)) (Z_to_bv 64 a)) (Z_to_bv 64 0)) (Z_to_bv 64 1)) (Z_to_bv 64 0) = false.
Proof.
  intros a k Ha Hk Hak. rewrite w_sltu by lia. destruct (Z.ltb_spec (a + k) a); [lia|].
  replace (alu64 ALU_XOR (alu64 ALU_XOR (Z_to_bv 64 0) (Z_to_bv 64 0)) (Z_to_bv 64 1)) with (Z_to_bv 64 1 : word) by (apply bv_eq; vm_compute; reflexivity).
  rewrite br_eq by lia. reflexivity.
Qed.

Section LB.
  Context {fx : FPState}.
Context {AC : AllocCeiling}.
  Variables (M : mem) (x : Z).
  Hypothesis HRO : ro_clear L M.
  Hypothesis Hx : 0 <= x < 2 ^ 32.
  #[local] Abbreviation st R pc := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom SEGS)).
  Let base := ti_insn ti.

  Definition keptX (R R' : bvmap 5 word) : Prop :=
    kept R R' /\ getr R' 10%bv = getr R 10%bv /\ getr R' 11%bv = getr R 11%bv.
  Lemma keptX_trans : forall R1 R2 R3, keptX R1 R2 -> keptX R2 R3 -> keptX R1 R3.
  Proof using. intros R1 R2 R3 (A & B & C) (D & E & F). split; [exact (keeps_cs_trans _ _ _ A D) | split; congruence]. Qed.

  Ltac keptX_of HR' :=
    split; [exact (kept_of_syms _ _ _ _ HR' eq_refl)
          | split; [ let H := fresh in rreg HR' 10%bv H; first [exact H | rewrite H; symmetry; assumption]
                   | let H := fresh in rreg HR' 11%bv H; first [exact H | rewrite H; symmetry; assumption] ] ].

  Definition LREG (R : bvmap 5 word) (i len : Z) : Prop :=
    getr R 14%bv = Z_to_bv 64 (60 * i) /\ getr R 17%bv = Z_to_bv 64 len /\ getr R 10%bv = Z_to_bv 64 x /\
    getr R 13%bv = Z_to_bv 64 base /\ getr R 12%bv = Z_to_bv 64 60 /\ getr R 15%bv = Z_to_bv 64 (-60).

  Lemma lb_step : forall R i len,
    0 <= i -> 0 < len -> i + len <= NROWS -> LREG R i len ->
    let half := len / 2 in
    let i' := (if x <=? OP (i + half) then i else i + half + 1) in
    let len' := (if x <=? OP (i + half) then half else len - half - 1) in
    exists R', keptX R R' /\
      msteps SEGS (st R LO_LOOP) (st R' (if len' =? 0 then LO_EXIT else LO_LOOP)) /\ LREG R' i' len'.
  Proof using fx M x HRO Hx.
    intros R i len Hi Hlen Hil (H14 & H17 & H10 & H13 & H12 & H15) half i' len'.
    pose proof insn_base_bounds as [B0 B1]. pose proof (half_bounds len Hlen) as [Hh1 Hh2].
    assert (Hbase : base = 0x23f18) by reflexivity.
    pose proof (OP_row (i + half) ltac:(unfold NROWS in *; lia)) as (r & _ & _ & HOP).
    pose proof (OP_cell M (i + half) HRO ltac:(unfold NROWS in *; lia)) as CELL.
    pose (E := Eseed R [Z_to_bv 64 (60 * i); Z_to_bv 64 len; Z_to_bv 64 x; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0;
                        sxw (OP (i + half))]).
    assert (HR : regs_ok E (srs sr_id [(14%bv, EVar 32); (17%bv, EVar 33); (10%bv, EVar 34); (13%bv, ELit 0x23f18); (12%bv, ELit 60); (15%bv, ELit (-60))]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; try assumption; rewrite H13, Hbase; reflexivity. }
    assert (HK : know_ok SEGS E M [KRange (EVar 32) 0 52500; KAlign (EVar 32) 60; KRange (EVar 33) 1 876; KRange (EVar 34) 0 4294967295]).
    { repeat apply Forall_cons; [ | | | | apply Forall_nil].
      - eapply krange_var; [evs; reflexivity | unfold NROWS in *; lia | unfold NROWS in *; lia].
      - eapply kalign_var; [evs; reflexivity | unfold NROWS in *; lia | lia | rewrite Z.mul_comm; apply Z_mod_mult].
      - eapply krange_var; [evs; reflexivity | unfold NROWS in *; lia | unfold NROWS in *; lia].
      - eapply krange_var; [evs; reflexivity | lia | lia]. }

    assert (ADDR : alu64 ALU_ADD (Z_to_bv 64 (60 * i)) (mul_div M_MUL (Z_to_bv 64 60) (alu64 ALU_SRL (Z_to_bv 64 len) (Z_to_bv 64 1)))
                   = Z_to_bv 64 (60 * (i + half))).
    { rewrite w_srl by lia. change (2 ^ 1) with 2. rewrite zbv_mul, zbv_add. f_equal. subst half. lia. }
    assert (RD : sc_denot SEGS M E (SCReadBase (SA (EAlu ALU_ADD (EVar 32) (EMd M_MUL (ELit 60) (EAlu ALU_SRL (EVar 33) (ELit 1)))) 0x23f18) 4 true (EVar 40))).
    { eapply (sc_read_cell4_sx _ _ _ _ _ _ _ CELL); [| evs; reflexivity].
      unfold adenot. cbn [a_base a_off]. evs. rewrite ADDR. rewrite v_addi_Z by (unfold NROWS in *; lia). f_equal. subst base. rewrite Hbase. lia. }
    assert (HAC_ : sc_denot SEGS M E (SCBr false BC_EQ
              (EAlu ALU_XOR (EAlu ALU_XOR (EAlu ALU_SLTU
                 (EAlu ALU_ADD (EAlu ALU_ADD (EVar 32) (EMd M_MUL (ELit 60) (EAlu ALU_SRL (EVar 33) (ELit 1)))) (ELit 0x23f18))
                 (EAlu ALU_ADD (EVar 32) (ELit 0x23f18))) (ELit 0)) (ELit 1)) (ELit 0))).
    { cbn [sc_denot]. evs. rewrite ADDR, !zbv_add.
      replace (60 * (i + half) + 147224) with (60 * i + 147224 + 60 * half) by lia. apply addchk_false; unfold NROWS in *; lia. }
    assert (BR : forall b : bool, (if b then x <= OP (i + half) else OP (i + half) < x) ->
                 sc_denot SEGS M E (SCBr b BC_GEU (EVar 40) (EVar 34))).
    { intros b Hb. cbn [sc_denot]. evs. rewrite sxw_small by lia. rewrite br_geu by lia. destruct b; bool_lia. }
    assert (FIN : forall R', regs_ok E
              [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 34; EVar 11; ELit 60; ELit 147224]%list R' -> True) by (intros; exact I).
    destruct (Z.leb_spec x (OP (i + half))) as [GE|LT].
    -
      destruct (Z.eqb_spec half 0) as [Hz|Hnz].
      + subst i' len'. rewrite Hz. cbn [Z.eqb].
        xrun HR HK 40%nat LO_STOPS (SCR [false; true; true] [EVar 40] []) 41%N.
        { split_scs; first [exact HAC_ | exact RD | apply BR; exact GE | sc_auto1].
          all: cbn [sc_denot]; evs; rewrite w_srl by lia; change (2 ^ 1) with 2; fold half; rewrite Hz; rewrite br_eq by lia; bool_lia. }
        exists R'. split; [keptX_of HR'|]. split; [exact Hms|].
        repeat split; [rreg HR' 14%bv X; exact X | rreg HR' 17%bv X; rewrite X, w_srl by lia; change (2 ^ 1) with 2; fold half; rewrite Hz; reflexivity
                      | rreg HR' 10%bv X; exact X | rreg HR' 13%bv X; rewrite X, Hbase; reflexivity | rreg HR' 12%bv X; exact X | rreg HR' 15%bv X; exact X].
      + subst i' len'. replace (half =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hnz).
        xrun HR HK 40%nat LO_STOPS (SCR [false; true; false] [EVar 40] []) 41%N.
        { split_scs; first [exact HAC_ | exact RD | apply BR; exact GE | sc_auto1].
          all: cbn [sc_denot]; evs; rewrite w_srl by lia; change (2 ^ 1) with 2; fold half; rewrite br_eq by lia; bool_lia. }
        exists R'. split; [keptX_of HR'|]. split; [exact Hms|].
        repeat split; [rreg HR' 14%bv X; exact X | rreg HR' 17%bv X; rewrite X, w_srl by lia; change (2 ^ 1) with 2; reflexivity
                      | rreg HR' 10%bv X; exact X | rreg HR' 13%bv X; rewrite X, Hbase; reflexivity | rreg HR' 12%bv X; exact X | rreg HR' 15%bv X; exact X].
    -
      destruct (Z.eqb_spec (len - half - 1) 0) as [Hz|Hnz].
      + subst i' len'. rewrite Hz. cbn [Z.eqb].
        xrun HR HK 40%nat LO_STOPS (SCR [false; false; true] [EVar 40] []) 41%N.
        { split_scs; first [exact HAC_ | exact RD | apply BR; exact LT | sc_auto1].
          all: cbn [sc_denot]; evs; rewrite w_srl by lia; change (2 ^ 1) with 2; fold half; rewrite !zbv_mul, !zbv_add;
               replace (len + -1 * half + -1) with 0 by lia; rewrite br_eq by lia; bool_lia. }
        exists R'. split; [keptX_of HR'|]. split; [exact Hms|].
        repeat split; [rreg HR' 14%bv X; rewrite X, w_srl by lia; change (2 ^ 1) with 2; fold half; rewrite !zbv_mul, !zbv_add; f_equal; lia
                      | rreg HR' 17%bv X; rewrite X, w_srl by lia; change (2 ^ 1) with 2; fold half; rewrite !zbv_mul, !zbv_add; f_equal; lia
                      | rreg HR' 10%bv X; exact X | rreg HR' 13%bv X; rewrite X, Hbase; reflexivity | rreg HR' 12%bv X; exact X | rreg HR' 15%bv X; exact X].
      + subst i' len'. replace (len - half - 1 =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hnz).
        xrun HR HK 40%nat LO_STOPS (SCR [false; false; false] [EVar 40] []) 41%N.
        { split_scs; first [exact HAC_ | exact RD | apply BR; exact LT | sc_auto1].
          all: cbn [sc_denot]; evs; rewrite w_srl by lia; change (2 ^ 1) with 2; fold half; rewrite !zbv_mul, !zbv_add;
               replace (len + -1 * half + -1) with (len - half - 1) by lia; rewrite br_eq by lia; bool_lia. }
        exists R'. split; [keptX_of HR'|]. split; [exact Hms|].
        repeat split; [rreg HR' 14%bv X; rewrite X, w_srl by lia; change (2 ^ 1) with 2; fold half; rewrite !zbv_mul, !zbv_add; f_equal; lia
                      | rreg HR' 17%bv X; rewrite X, w_srl by lia; change (2 ^ 1) with 2; fold half; rewrite !zbv_mul, !zbv_add; f_equal; lia
                      | rreg HR' 10%bv X; exact X | rreg HR' 13%bv X; rewrite X, Hbase; reflexivity | rreg HR' 12%bv X; exact X | rreg HR' 15%bv X; exact X].
  Qed.

  Definition split_at (i len : Z) : Prop :=
    (forall j, 0 <= j < i -> OP j < x) /\ (forall j, i + len <= j < NROWS -> x <= OP j).

  Lemma lb_loop : forall (m : nat) R i len,
    len <= Z.of_nat m -> 0 <= i -> 0 < len -> i + len <= NROWS -> split_at i len -> LREG R i len ->
    exists R' i', keptX R R' /\ msteps SEGS (st R LO_LOOP) (st R' LO_EXIT) /\
      LREG R' i' 0 /\ 0 <= i' <= NROWS /\ split_at i' 0.
  Proof using fx M x HRO Hx.
    induction m as [|m IH]; intros R i len Hm Hi Hlen Hil [SL SR] HL; [lia|].
    pose proof (half_bounds len Hlen) as [Hh1 Hh2].
    destruct (lb_step R i len Hi Hlen Hil HL) as (R1 & K1 & MS1 & HL1).
    cbv zeta in MS1, HL1.
    set (half := len / 2) in *.
    destruct (Z.leb_spec x (OP (i + half))) as [GE|LT].
    - assert (SPL : split_at i half).
      { split; [exact SL|]. intros j Hj. destruct (Z.lt_ge_cases j (i + len)); [|apply SR; lia].
        pose proof (OP_mono (i + half) j ltac:(lia) ltac:(lia) ltac:(lia)). lia. }
      destruct (Z.eqb_spec half 0) as [Hz|Hnz].
      + exists R1, i. split; [exact K1|]. split; [exact MS1|]. split; [rewrite Hz in HL1; exact HL1|]. split; [lia|].
        rewrite Hz in SPL. exact SPL.
      + destruct (IH R1 i half ltac:(lia) Hi ltac:(lia) ltac:(lia) SPL HL1) as (R' & i' & K' & MS' & P).
        exists R', i'. split; [exact (keptX_trans _ _ _ K1 K')|]. split; [eapply msteps_trans; [exact MS1|exact MS']|]. exact P.
    - assert (SPL : split_at (i + half + 1) (len - half - 1)).
      { split; [|intros j Hj; apply SR; lia]. intros j Hj. destruct (Z.lt_ge_cases j i); [apply SL; lia|].
        pose proof (OP_mono j (i + half) ltac:(lia) ltac:(lia) ltac:(lia)). lia. }
      destruct (Z.eqb_spec (len - half - 1) 0) as [Hz|Hnz].
      + exists R1, (i + half + 1). split; [exact K1|]. split; [exact MS1|]. split; [rewrite Hz in HL1; exact HL1|]. split; [lia|].
        rewrite Hz in SPL. exact SPL.
      + destruct (IH R1 (i + half + 1) (len - half - 1) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) SPL HL1) as (R' & i' & K' & MS' & P).
        exists R', i'. split; [exact (keptX_trans _ _ _ K1 K')|]. split; [eapply msteps_trans; [exact MS1|exact MS']|]. exact P.
  Qed.

  Lemma entry_block : forall R,
    getr R 10%bv = Z_to_bv 64 x ->
    exists R', keptX R R' /\ msteps SEGS (st R LO_ENTRY) (st R' LO_LOOP) /\ LREG R' 0 NROWS.
  Proof using fx M x.
    intros R H10.
    pose (E := Eseed R [Z_to_bv 64 x]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
    assert (HK : know_ok SEGS E M []) by constructor.
    xrun HR HK 20%nat LO_STOPS (SCR [] [] []) 41%N. { split_scs; try sc_auto1. }
    exists R'. split; [keptX_of HR'|]. split; [exact Hms|].
    repeat split; [rreg HR' 14%bv X; exact X | rreg HR' 17%bv X; exact X | rreg HR' 10%bv X; exact X | rreg HR' 13%bv X; exact X | rreg HR' 12%bv X; exact X
                  | rreg HR' 15%bv X; rewrite X; apply bv_eq; vm_compute; reflexivity].
  Qed.

  Lemma tail_block : forall R i pd (ret : word),
    0 <= i <= NROWS -> split_at i 0 -> LREG R i 0 -> getr R 11%bv = Z_to_bv 64 pd ->
    alloc_ceiling <= pd -> pd + 8 <= 2 ^ 47 -> mdef M pd 8 -> pd mod 8 = 0 ->
    getr R 1%bv = ret -> ret_ok ret ->
    exists R' M',
      kept R R' /\ msteps SEGS (st R LO_EXIT) (@mkst fx R' ret M' (seg_rom SEGS)) /\
      ( (i < NROWS /\ OP i = x /\ getr R' 10%bv = Z_to_bv 64 0 /\ M' = wbytes M (Z_to_bv 64 pd) (word_to_le_bytes 8 (Z_to_bv 64 (base + 60 * i))))
      \/ (~ (i < NROWS /\ OP i = x) /\ getr R' 10%bv = Z_to_bv 64 (-9) /\ M' = M) ).
  Proof using fx AC M x HRO Hx.
    intros R i pd ret Hi [SL SR] (H14 & H17 & H10 & H13 & H12 & H15) H11 Hce Hpd Hdef Hal Hra Hret.
    pose proof insn_base_bounds as [B0 B1]. pose proof ac_bounds_lit as HAC. assert (Hbase : base = 0x23f18) by reflexivity.
    assert (Dpd : defined M pd 8) by (intros k Hk; apply Hdef; lia).
    pose (E := Eseed R [Z_to_bv 64 (60 * i); Z_to_bv 64 x; Z_to_bv 64 pd; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; sxw (OP i)]).
    assert (HR : regs_ok E (srs sr_id [(14%bv, EVar 32); (10%bv, EVar 33); (11%bv, EVar 34); (13%bv, ELit 0x23f18)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; try assumption; rewrite H13, Hbase; reflexivity. }
    assert (HK : know_ok SEGS E M [KRange (EVar 34) 1 (2 ^ 47); KAlign (EVar 34) 8; KRange (EVar 32) 0 52560; KAlign (EVar 32) 60]).
    { repeat apply Forall_cons; [ | | | | apply Forall_nil].
      - eapply krange_var; [evs; reflexivity | lia | lia].
      - eapply kalign_var; [evs; reflexivity | lia | lia | exact Hal].
      - eapply krange_var; [evs; reflexivity | unfold NROWS in *; lia | unfold NROWS in *; lia].
      - eapply kalign_var; [evs; reflexivity | unfold NROWS in *; lia | lia | rewrite Z.mul_comm; apply Z_mod_mult]. }
    destruct (Z_lt_le_dec i NROWS) as [Hlt|Hge].
    - pose proof (OP_row i ltac:(lia)) as (r & _ & _ & HOP). pose proof (OP_cell M i HRO ltac:(lia)) as CELL.
      assert (BE : sc_denot SEGS M E (SCBr false BC_EQ (EVar 32) (ELit 52560))).
      { cbn [sc_denot]. evs. rewrite br_eq by (unfold NROWS in *; lia). unfold NROWS in *. bool_lia. }
      destruct (Z.eq_dec (OP i) x) as [EQ|NE].
      + xrun HR HK 30%nat LO_STOPS (SCR [false; false] [EVar 40] []) 41%N.
        { split_scs; try sc_auto1; first [exact BE | sc_rd_sx CELL | sc_so; rewrite Z.add_0_r; exact Dpd
                                          | cbn [sc_denot]; evs; rewrite sxw_small by lia; rewrite br_ne by lia; bool_lia ]. }
        assert (Hra1 : getr R' 1%bv = ret) by (etransitivity; [apply (kept_of_syms _ _ _ R' HR' eq_refl); (first [solve [clear; cbn; tauto] | cbn; tauto]) | exact Hra]).
        eexists R', _. split; [exact (kept_of_syms _ _ _ _ HR' eq_refl)|]. split.
        { eapply msteps_trans; [exact Hms|]. eapply ret_run; [vm_compute; reflexivity | exact Hra1 | exact Hret]. }
        left. split; [exact Hlt|]. split; [exact EQ|]. split; [rreg HR' 10%bv H10'; exact H10'|].
        evs. rewrite v_addi_Z by lia. rewrite Z.add_0_r, zbv_add. do 3 f_equal. rewrite Hbase. lia.
      + xrun HR HK 30%nat LO_STOPS (SCR [false; true] [EVar 40] []) 41%N.
        { split_scs; try sc_auto1; first [exact BE | sc_rd_sx CELL
                                          | cbn [sc_denot]; evs; rewrite sxw_small by lia; rewrite br_ne by lia; bool_lia ]. }
        assert (Hra1 : getr R' 1%bv = ret) by (etransitivity; [apply (kept_of_syms _ _ _ R' HR' eq_refl); (first [solve [clear; cbn; tauto] | cbn; tauto]) | exact Hra]).
        eexists R', M. split; [exact (kept_of_syms _ _ _ _ HR' eq_refl)|]. split.
        { eapply msteps_trans; [exact Hms|]. eapply ret_run; [vm_compute; reflexivity | exact Hra1 | exact Hret]. }
        right. split; [lia|]. split; [rreg HR' 10%bv H10'; rewrite H10'; apply bv_eq; vm_compute; reflexivity| reflexivity].
    - assert (Hi' : i = NROWS) by lia.
      xrun HR HK 30%nat LO_STOPS (SCR [true] [EVar 40] []) 41%N.
      { split_scs; try sc_auto1. all: cbn [sc_denot]; evs; rewrite Hi'; rewrite br_eq by lia; bool_lia. }
      assert (Hra1 : getr R' 1%bv = ret) by (etransitivity; [apply (kept_of_syms _ _ _ R' HR' eq_refl); (first [solve [clear; cbn; tauto] | cbn; tauto]) | exact Hra]).
      eexists R', M. split; [exact (kept_of_syms _ _ _ _ HR' eq_refl)|]. split.
      { eapply msteps_trans; [exact Hms|]. eapply ret_run; [vm_compute; reflexivity | exact Hra1 | exact Hret]. }
      right. split; [lia|]. split; [rreg HR' 10%bv H10'; rewrite H10'; apply bv_eq; vm_compute; reflexivity| reflexivity].
  Qed.
End LB.

Theorem lookup_opcode_spec {AC : AllocCeiling} : lookup_opcode_stmt SEGS L TG tc (idesc ti).
Proof.
  intros fx R M x y pd sp ret HRO Ha0 Hx H2 _ Hsp Hce Hpd8 Hdef Hal Hdisj Hroom Hcs Hsp47 Hsp16 Hra Hret.
  specialize (H2 eq_refl). pose proof ac_bounds_lit as HAC. pose proof insn_base_bounds as [B0 B1].
  destruct (entry_block M x R Ha0) as (R1 & (K1 & K1a & K1b) & MS1 & HL1).
  assert (SP0 : split_at x 0 NROWS) by (split; intros j Hj; unfold NROWS in *; lia).
  destruct (lb_loop M x HRO Hx (Z.to_nat NROWS) R1 0 NROWS ltac:(lia) ltac:(lia) ltac:(unfold NROWS; lia) ltac:(lia) SP0 HL1)
    as (R2 & i & (K2 & K2a & K2b) & MS2 & HL2 & Hi & SPL).
  destruct (tail_block M x HRO Hx R2 i pd ret Hi SPL HL2 ltac:(rewrite K2b, K1b; exact H2) Hce Hpd8 Hdef Hal
              ltac:(rewrite K2, K1; [exact Hra | (first [solve [clear; cbn; tauto] | cbn; tauto]) | (first [solve [clear; cbn; tauto] | cbn; tauto])]) Hret) as (R3 & M' & K3 & MS3 & RES).
  assert (KK : kept R R3) by (exact (keeps_cs_trans _ _ _ (keeps_cs_trans _ _ _ K1 K2) K3)).
  assert (MS : msteps SEGS (@mkst fx R (Z_to_bv 64 (tc_lookup_opcode tc)) M (seg_rom SEGS)) (@mkst fx R3 ret M' (seg_rom SEGS))).
  { change (tc_lookup_opcode tc) with LO_ENTRY. eapply msteps_trans; [exact MS1|]. eapply msteps_trans; [exact MS2|exact MS3]. }
  destruct SPL as [SL SR]. rewrite Z.add_0_r in SR.
  destruct RES as [(Hlt & HOP & A10 & HM')|(Hno & A10 & HM')].
  -
    destruct (lb_found x i ltac:(lia) HOP SL) as (r & Hf & Hr).
    exists R3, M', 0, (ti_insn ti + 60 * i). subst M'.
    split; [exact MS|]. split; [exact KK|]. split; [exact A10|]. split; [lia|]. split.
    { apply fld_wbytes8; lia. }
    split. { split; [intros _; exists (i_span r); cbn [g_op TG]; unfold tg_op; rewrite Hf; reflexivity | intros _; reflexivity]. }
    split. { intros _. exists i, r. split; [exact Hf | reflexivity]. }
    split.
    { apply frame_wbytes8; [lia|lia|]. intros a Ha. left. unfold zwin. lia. }
    intros a Ha. apply defined_wbytes8; [lia|lia|exact Ha].
  -
    pose proof (lb_missed x i Hi SL SR Hno) as Hnone.
    destruct (mdef8_fld SEGS M pd Hdef ltac:(lia) ltac:(lia)) as (d0 & _ & Fd0).
    exists R3, M', (-9), d0. subst M'.
    split; [exact MS|]. split; [exact KK|]. split; [exact A10|]. split; [lia|]. split; [exact Fd0|].
    split. { split; [intros C; lia|]. intros [l Hl]. cbn [g_op TG] in Hl. unfold tg_op in Hl. rewrite Hnone in Hl. discriminate. }
    split. { intros C; lia. }
    split; [intros a _; reflexivity | intros a Ha; exact Ha].
Qed.
