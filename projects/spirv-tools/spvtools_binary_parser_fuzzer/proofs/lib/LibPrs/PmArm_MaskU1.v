(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require list.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac WalkTac StartupTac SumWalkTac StoreOk MemSplit Hoare ShapeAlg
  SRealizes RefMemcpyLib RefReadLib FPSteps LibIface LibBudget LibEff MmapSim LibMaskBits
  ZStores SymExec3 SymExec3Sound SymRun3 U1Layout.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContLib StrLib LiveStats ContStmts ContStmts2 U1Facts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts HStmtsU1 HCommonU1 HLib HConstsU1 HWord.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar PrsNeeds PrsInv PrsStmts PmBaseU1 PmHyps PmHypsU1 PmCoreU1 PmStepU1. Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep2U1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep2U1.PmUpdU1. From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PmStep2U1 PmLoopU1 PmInstU1 PmStep3U1 PmZw PmODefsU1 PmStep4U1 PmArm_SpecU1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PeLia.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Local Ltac lia ::= pe3_lia.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Abbreviation SEGS := Ubsan.M.loaded_segments.

Lemma in_reg_list : forall (r : bv 5) (l : list (bv 5)),
  existsb (fun x => Z.eqb (bv_unsigned x) (bv_unsigned r)) l = true -> In r l.
Proof.
  intros r l; induction l as [|x l IH]; cbn; [discriminate|]. intros H. apply Bool.orb_true_iff in H.
  destruct H as [H|H]; [left; apply bv_eq; apply Z.eqb_eq; exact H | right; apply IH; exact H].
Qed.
Ltac keptQ KEPT G Q ::=
  lazymatch type of G with getr _ ?r = _ => pose proof G as Q; rewrite <- (KEPT r) in Q by (clear; apply in_reg_list; reflexivity) end.

Lemma testbit_high0 : forall x i, 0 <= x < 2 ^ 32 -> 32 <= i -> Z.testbit x i = false.
Proof.
  intros x i Hx Hi. destruct (Z.eq_dec x 0) as [->|Hn]; [apply Z.bits_0|].
  apply Z.bits_above_log2; [lia|]. apply (Z.lt_le_trans _ 32); [apply Z.log2_lt_pow2; lia | lia].
Qed.

Lemma testbit31_hi : forall x, 2 ^ 31 <= x < 2 ^ 32 -> Z.testbit x 31 = true.
Proof.
  intros x Hx. apply Z.testbit_true; [lia|]. rewrite <- (Z.div_unique x (2 ^ 31) 1 (x - 2 ^ 31)); [reflexivity | | lia]. left. lia.
Qed.
Lemma testbit31_lo : forall x, 0 <= x < 2 ^ 31 -> Z.testbit x 31 = false.
Proof.
  intros x Hx. destruct (Z.eq_dec x 0) as [->|Hn]; [apply Z.bits_0|].
  apply Z.bits_above_log2; [lia|]. apply Z.log2_lt_pow2; lia.
Qed.

Lemma hi_fill : forall x, 0 <= x < 2 ^ 32 -> x + (2 ^ 64 - 2 ^ 32) = Z.lor x (Z.shiftl (Z.ones 32) 32).
Proof.
  intros x Hx.
  assert (D : Z.land x (Z.shiftl (Z.ones 32) 32) = 0).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0, Z.shiftl_spec by lia.
    destruct (Z.lt_ge_cases n 32); [rewrite (Z.testbit_neg_r _ (n - 32)) by lia; apply andb_false_r | rewrite (testbit_high0 x n) by lia; reflexivity]. }
  rewrite <- Z.lxor_lor by exact D. rewrite <- Z.add_nocarry_lxor by exact D.
  rewrite Z.shiftl_mul_pow2, Z.ones_equiv by lia. reflexivity.
Qed.

Lemma testbit_swrap32 : forall x i, 0 <= x < 2 ^ 32 -> 0 <= i ->
  Z.testbit (bv_swrap 32 x mod 2 ^ 64) i = if i <? 32 then Z.testbit x i else if i <? 64 then Z.testbit x 31 else false.
Proof.
  intros x i Hx Hi. rewrite bv_swrap32_cases by lia.
  destruct (Z.ltb_spec x (2 ^ 31)) as [Hs|Hb].
  - rewrite Z.mod_small by lia. rewrite (testbit31_lo x) by lia.
    destruct (Z.ltb_spec i 32); [reflexivity|]. rewrite (testbit_high0 x i) by lia. destruct (i <? 64); reflexivity.
  - replace ((x - 2 ^ 32) mod 2 ^ 64) with (x + (2 ^ 64 - 2 ^ 32)) by (rewrite <- (Z.mod_add _ 1) by lia; rewrite Z.mod_small by lia; lia).
    rewrite (hi_fill x Hx), Z.lor_spec, Z.shiftl_spec by lia. rewrite (testbit31_hi x) by lia.
    destruct (Z.ltb_spec i 32).
    + rewrite (Z.testbit_neg_r _ (i - 32)) by lia. apply orb_false_r.
    + rewrite Z.testbit_ones_nonneg by lia. rewrite (testbit_high0 x i) by lia. cbn.
      destruct (Z.ltb_spec i 64); [apply Z.ltb_lt; lia | apply Z.ltb_ge; lia].
Qed.

Lemma swrap32_mod_range : forall x, 0 <= bv_swrap 32 x mod 2 ^ 64 < 2 ^ 64.
Proof. intros x. apply Z.mod_pos_bound. lia. Qed.

Lemma land32_range : forall a b, 0 <= a < 2 ^ 32 -> 0 <= b -> 0 <= Z.land a b < 2 ^ 32.
Proof. intros a b Ha Hb. split; [apply Z.land_nonneg; lia|]. apply (Z.le_lt_trans _ a); [apply SymExec3Sound.SX2S.land_le_l; lia | lia]. Qed.
Lemma lxor32_range : forall a b, 0 <= a < 2 ^ 32 -> 0 <= b < 2 ^ 32 -> 0 <= Z.lxor a b < 2 ^ 32.
Proof.
  intros a b Ha Hb. pose proof (Z.lxor_nonneg a b). split; [lia|].
  destruct (Z.eq_dec (Z.lxor a b) 0) as [->|Hn]; [lia|].
  destruct (Z.eq_dec a 0) as [->|Ha0]; [rewrite Z.lxor_0_l; lia|]. destruct (Z.eq_dec b 0) as [->|Hb0]; [rewrite Z.lxor_0_r; lia|].
  apply Z.log2_lt_pow2; [lia|]. apply (Z.le_lt_trans _ (Z.max (Z.log2 a) (Z.log2 b))); [apply Z.log2_lxor; lia|].
  apply Z.max_lub_lt; apply Z.log2_lt_pow2; lia.
Qed.

Lemma land_sxw : forall a b, 0 <= a < 2 ^ 32 -> 0 <= b < 2 ^ 32 ->
  alu64 ALU_AND (sxw a) (sxw b) = sxw (Z.land a b).
Proof.
  intros a b Ha Hb. pose proof (land32_range a b Ha ltac:(lia)) as Hab.
  unfold sxw. rewrite (Z_to_bv_mod64 (bv_swrap 32 a)), (Z_to_bv_mod64 (bv_swrap 32 b)), (Z_to_bv_mod64 (bv_swrap 32 (Z.land a b))).
  rewrite w_and by (apply swrap32_mod_range). f_equal.
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, !testbit_swrap32 by lia.
  destruct (Z.ltb_spec i 32); [apply eq_sym, Z.land_spec|]. destruct (Z.ltb_spec i 64); [apply eq_sym, Z.land_spec | reflexivity].
Qed.

Lemma lxor_sxw : forall a b, 0 <= a < 2 ^ 32 -> 0 <= b < 2 ^ 32 ->
  alu64 ALU_XOR (sxw a) (sxw b) = sxw (Z.lxor a b).
Proof.
  intros a b Ha Hb. pose proof (lxor32_range a b Ha Hb) as Hab.
  unfold sxw. rewrite (Z_to_bv_mod64 (bv_swrap 32 a)), (Z_to_bv_mod64 (bv_swrap 32 b)), (Z_to_bv_mod64 (bv_swrap 32 (Z.lxor a b))).
  rewrite w_xor by (apply swrap32_mod_range). f_equal.
  apply Z.bits_inj'. intros i Hi. rewrite Z.lxor_spec, !testbit_swrap32 by lia.
  destruct (Z.ltb_spec i 32); [apply eq_sym, Z.lxor_spec|]. destruct (Z.ltb_spec i 64); [apply eq_sym, Z.lxor_spec | reflexivity].
Qed.

Lemma sxw_small' : forall v, 0 <= v < 2 ^ 31 -> sxw v = Z_to_bv 64 v.
Proof. intros v Hv. unfold sxw. rewrite bv_swrap32_cases by lia. destruct (Z.ltb_spec v (2 ^ 31)); [reflexivity | lia]. Qed.

Lemma pow2_lt31 : forall j, 0 <= j <= 30 -> 0 < 2 ^ j < 2 ^ 31.
Proof. intros j Hj. split; [apply Z.pow_pos_nonneg; lia|]. apply Z.pow_lt_mono_r; lia. Qed.

Lemma srliw1_mask : forall j, 1 <= j <= 31 ->
  sext 64 (alu32 ALU_SRL (low32 (sxw (2 ^ j))) (low32 (Z_to_bv 64 1))) = sxw (2 ^ (j - 1)).
Proof.
  intros j Hj. destruct (Z.eq_dec j 31) as [->|Hne]; [apply bv_eq; vm_compute; reflexivity|].
  pose proof (pow2_lt31 j ltac:(lia)) as H1. pose proof (pow2_lt31 (j - 1) ltac:(lia)) as H2.
  rewrite !sxw_small' by lia. apply bv_eq.
  rewrite (SymExec3Sound.SX2S.u_srlw_small _ _ 1); rewrite ?u64_of_Z by lia; [| reflexivity | lia |].
  - change (1 mod 32) with 1. rewrite Z.pow_sub_r by lia. reflexivity.
  - change (1 mod 32) with 1. rewrite <- Z.pow_sub_r by lia. lia.
Qed.

Lemma testbit_mod_pow2 : forall w j k, 0 <= j < k -> Z.testbit (w mod 2 ^ k) j = Z.testbit w j.
Proof. intros w j k H. apply Z.mod_pow2_bits_low. lia. Qed.

Lemma mod_pow2_step : forall w j, 0 <= w -> 0 <= j ->
  w mod 2 ^ (j + 1) = (if Z.testbit w j then 2 ^ j else 0) + w mod 2 ^ j.
Proof.
  intros w j Hw Hj. pose proof (Z.pow_pos_nonneg 2 j ltac:(lia) Hj) as Hp.
  rewrite Z.pow_add_r, Z.pow_1_r by lia. rewrite Z.rem_mul_r by lia.
  pose proof (Z.testbit_spec' w j Hj) as Hb. rewrite <- Hb. destruct (Z.testbit w j); cbn [Z.b2z]; lia.
Qed.

Lemma land_pow2_testbit : forall x j, 0 <= x -> 0 <= j -> Z.land (2 ^ j) x = (if Z.testbit x j then 2 ^ j else 0).
Proof.
  intros x j Hx Hj. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.pow2_bits_eqb by lia.
  destruct (Z.eqb_spec j i) as [<-|Hne]; cbn [andb].
  - destruct (Z.testbit x j); [rewrite Z.pow2_bits_true; lia | rewrite Z.bits_0; reflexivity].
  - destruct (Z.testbit x j); [rewrite Z.pow2_bits_false by lia; reflexivity | rewrite Z.bits_0; reflexivity].
Qed.

Lemma lxor_pow2_clear : forall x j, 0 <= x -> 0 <= j -> Z.testbit x j = true ->
  Z.lxor (2 ^ j) x = x - 2 ^ j.
Proof.
  intros x j Hx Hj Hb.
  assert (D : Z.land (Z.lxor (2 ^ j) x) (2 ^ j) = 0).
  { apply Z.bits_inj'; intros i Hi. rewrite Z.land_spec, Z.lxor_spec, Z.pow2_bits_eqb, Z.bits_0 by lia.
    destruct (Z.eqb_spec j i) as [<-|Hne]; [rewrite Hb; reflexivity | apply andb_false_r]. }
  pose proof (Z.add_nocarry_lxor _ _ D) as E.
  rewrite (Z.lxor_comm (2 ^ j) x), Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_r in E.
  rewrite Z.lxor_comm in E. lia.
Qed.

Module Ly := U1Layout.

Section PM.
Context {AC : AllocCeiling}.
  Context {MI : MallocIface SEGS Ly.L} {ST : StaticsIface SEGS Ly.L}.
  Context {G : grammar} {idesc : Z -> Z -> Prop} {odesc edesc : Z -> Z -> Z -> Prop}
          {generates_type is_ext_inst is_nonsemantic : Z -> bool}
          {ds_rep : AS MI -> mem -> Z -> Z -> Z -> list (Z * Z) -> Prop}.
  Variable CL : pm_calleesU1 SEGS Ly.L MI ST G tcU1 dcU1 nfcU1 HConstsU1.hc ccU1 kcU1
                  idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep.

  #[local] Notation PMX := (PmBaseU1.PMX MI ST).
  #[local] Notation cfg fx R pc M model := (mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom SEGS)) model).
  #[local] Notation DL := (cu_ds_laws _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  #[local] Notation pm_exit := (PmCoreU1.pm_exit MI ST).
  #[local] Notation pmx_ds_room := (PmStepU1.pmx_ds_room CL).
  #[local] Notation pm_tail_6733c := (PmStepU1.pm_tail_6733c CL).
  #[local] Notation cregs_kept := (PmStepU1.cregs_kept CL).
  #[local] Notation pm_put_cstr := (PmStepU1.pm_put_cstr CL).
  #[local] Notation pm_put_chars := (PmStepU1.pm_put_chars CL).
  #[local] Notation pm_put_num := (PmStepU1.pm_put_num CL).
  #[local] Notation pm_put_u16 := (PmStepU1.pm_put_u16 CL).
  #[local] Notation pm_put_u32 := (PmStepU1.pm_put_u32 CL).
  #[local] Notation pm_put_u64 := (PmStepU1.pm_put_u64 CL).
  #[local] Notation pm_put_int := (PmStepU1.pm_put_int CL).
  #[local] Notation pm_pdiagQ := (PmStepU1.pm_pdiagQ CL).
  #[local] Notation pm_dtor := (PmStepU1.pm_dtor CL).
  #[local] Notation pm_exhausted := (PmStepU1.pm_exhausted CL).
  #[local] Notation pm_fixword := (PmStepU1.pm_fixword CL).
  #[local] Notation pm_is_host_endian := (PmStepU1.pm_is_host_endian CL).
  #[local] Notation pm_binend := (PmStepU1.pm_binend CL).
  #[local] Notation pm_ecw_pbs := (PmStep2U1.pm_ecw_pbs CL).
  #[local] Notation pm_opcode_split := (PmStep2U1.pm_opcode_split CL).
  #[local] Notation pm_lookup_opcode := (PmStep2U1.pm_lookup_opcode CL).
  #[local] Notation pm_lookup_operand := (PmStep2U1.pm_lookup_operand CL).
  #[local] Notation pm_lookup_ext := (PmStep2U1.pm_lookup_ext CL).
  #[local] Notation pm_idesc_operands := (PmStep3U1.pm_idesc_operands CL).
  #[local] Notation pm_odesc_operands := (PmStep3U1.pm_odesc_operands CL).
  #[local] Notation pm_edesc_operands := (PmStep3U1.pm_edesc_operands CL).
  #[local] Notation pm_push_types := (PmStep3U1.pm_push_types CL).
  #[local] Notation pm_take_first := (PmStep3U1.pm_take_first CL).

  #[local] Notation izero := (PmInstU1.izero).
  #[local] Notation ictx := (PmInstU1.ictx).
  #[local] Notation nodes := (PmLoopU1.nodes).
  #[local] Notation macct := (PmLoopU1.macct).
  #[local] Notation GOK := (cu_G _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  #[local] Notation MAXLEN := (cu_maxlen _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  #[local] Notation MASKLEN := (cu_mask_len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  #[local] Notation ipure := (PmODefsU1.ipure (G:=G) (idesc:=idesc)).
  #[local] Notation arm_stmt := (PmODefsU1.arm_stmt (MI:=MI) (ST:=ST) (G:=G) (idesc:=idesc)).
  #[local] Notation OBASE := (PmODefsU1.OBASE (MI:=MI) (ST:=ST)).
  #[local] Notation oregs := (PmODefsU1.oregs (MI:=MI) (ST:=ST)).
  #[local] Notation ifr := (PmODefsU1.ifr (MI:=MI) (ST:=ST)).
  #[local] Notation popnd := (PmODefsU1.popnd (MI:=MI) (ST:=ST)).
  #[local] Notation pm_find_m3 := (PmStep4U1.pm_find_m3 CL).
  #[local] Notation pm_find_m1 := (PmStep4U1.pm_find_m1 CL).
  #[local] Notation pm_spec_lookup := (PmStep4U1.pm_spec_lookup CL).
  #[local] Notation pm_oty_pb := (PmStep4U1.pm_oty_pb CL).
  Definition pm_is_ext_inst := pm_leafA (MI:=MI) (ST:=ST) _ _ _ (cu_is_ext_inst _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  Definition pm_is_nonsemantic := pm_leafA (MI:=MI) (ST:=ST) _ _ _ (cu_is_nonsemantic _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  Definition pm_operand_type_str := pm_leafA (MI:=MI) (ST:=ST) _ _ _ (cu_operand_type_str _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  Definition pm_strlen := pm_leafA (MI:=MI) (ST:=ST) _ _ _ (cu_strlen _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).

  Ltac oregs_seeded HRn Qgp Qtp :=
    let G2 := fresh in let G3 := fresh in let G4 := fresh in let G8 := fresh in let G9 := fresh in
    let G18 := fresh in let G19 := fresh in let G20 := fresh in let G21 := fresh in let G25 := fresh in
    rreg HRn 2%bv G2; rreg HRn 3%bv G3; rreg HRn 4%bv G4; rreg HRn 8%bv G8; rreg HRn 9%bv G9;
    rreg HRn 18%bv G18; rreg HRn 19%bv G19; rreg HRn 20%bv G20; rreg HRn 21%bv G21; rreg HRn 25%bv G25;
    unfold oregs, loop_regs; rewrite G2, G3, G4, G8, G9, G18, G19, G20, G21, G25; fixregs; rewrite ?Qgp, ?Qtp;
    rewrite ?SymExec.alu64_add_lit; repeat split; reflexivity.
  #[local] Notation OREGSEED := [(9%bv, EAlu ALU_ADD (EVar 33) (ELit 88)); (18%bv, ELit 1); (19%bv, ELit (2 ^ 61)); (20%bv, ELit 20); (21%bv, EAlu ALU_ADD (EVar 33) (ELit 264)); (25%bv, ELit 5)]%list.

  Lemma w2le4_sxw : forall v, word_to_le_bytes 4 (sxw v) = word_to_le_bytes 4 (Z_to_bv 64 v).
  Proof using. intros v. unfold sxw. change 4%nat with (N.to_nat 4). change 32%N with (8 * 4)%N. apply word_to_le_bytes_swrap. cbn; lia. Qed.

  #[local] Notation pm_span_push := (PmArm_SpecU1.pm_span_push CL).
  #[local] Notation pm_opnd_push := (PmArm_SpecU1.pm_opnd_push CL).
  #[local] Notation ODESC_PTR := (cu_odesc_ptr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  Definition MREGS : list reg := [23; 26; 27]%bv.

  Lemma rodata_kimg : forall (w : pmw MI ST) A M model c E (lo hi : Z),
    PMX w A M model c -> 0x10000 <= lo -> hi <= 0xe8000 -> kentry_ok SEGS E M (KImg lo hi).
  Proof using AC MI ST.
    intros w A M model c E lo hi X Hlo Hhi. apply kimg_abs; [lia | lia |]. intros i Hi.
    apply (ro_clear_at _ M i (x_roc X)); [lia|]. unfold ro_addr. cbn [ly_img ly_rw ly_relro Ly.L]. rewrite !in_ranges_1. lia.
  Qed.

  Lemma mask_w0 : forall (w : pmw MI ST) c0 K (fx : FPState) (I : ictxR) A M model c R (t : Z),
    PMS w c0 K -> OBASE w I A M model c R ->
    getr R 27%bv = Z_to_bv 64 t -> getr R 23%bv = Z_to_bv 64 (i_io I) -> getr R 26%bv = Z_to_bv 64 (i_op I) -> 0 <= t < 2 ^ 31 ->
    cellw SEGS M (w_sp w + 718) 2 1 ->
    Zlen (t3b (c_v3 c)) + g_maxlen G <= V3MAX -> g_maxlen G <= 125 ->
    PUSHK w I K fx c t -> In t MASK_TYPES ->
    srealizes SEGS (cfg fx R 0x67a7c M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx I A M model c R t PS OB Q27 Q23 Q26 Ht C718 Hmax Hml PK HInM.
    assert (Ht36 : t <> OT_RESULT_ID /\ t <> OT_LITERAL_INTEGER /\ t <> OT_LITERAL_STRING).
    { unfold MASK_TYPES in HInM. cbn [In] in HInM. unfold OT_RESULT_ID, OT_LITERAL_INTEGER, OT_LITERAL_STRING. repeat split; intros ->; intuition lia. }
    pose proof OB as OB'. destruct OB' as (X & Htr & BUD & OR & LM & IC & FR & Hic & Hend & Hwnz & MAC & V3R).
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof OR as OR'. destruct OR' as (Qsp & Qgp & Qtp & Qs0 & Qs1 & Qs2 & Qs3 & Qs4 & Qs5 & Qs9).

    pm_seed R w c [Z_to_bv 64 t].
    seedHR HR E ([(2%bv, EVar 32); (8%bv, EVar 33); (27%bv, EVar 39)] ++ OREGSEED)%list R. seedHK HK w A M model c E X.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R1.
    rreg HRn (1%bv) G1. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12. rreg HRn (27%bv) G27.
    pose proof (syms_id_sound _ _ _ _ [22; 23; 24; 26]%bv HRn eq_refl) as GK1.
    assert (OR1 : oregs w R1) by (oregs_seeded HRn Qgp Qtp).
    pose proof OR1 as OR'. destruct OR' as (G2 & G3 & G4 & G8 & _). clear HRn HR HK.
    rewrite ?SymExec.alu64_add_lit in G12. rewrite ?w_add in G12 by lia.
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M1 := m) in * end.
    assert (ST1 : stores_in (zwin (w_sp w + 280) (w_sp w + 288)) M M1) by (unfold M1; stin).
    assert (X1 : PMX w A M1 model c).
    { eapply (pmx_frame_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img w A M M1 model c (zwin (w_sp w + 280) (w_sp w + 288)));
        [exact X | exact ST1 | unfold zwin, w_sp0, PM_FRAME; intros; lia]. }
    pose proof (x_ms X1) as MS1.
    eapply (pm_lookup_operand w A M1 model c fx R1 t 0 (w_sp w + 280) _ K X1 G10 ltac:(lia) ltac:(intros HH; discriminate HH)
              ltac:(intros _; split; [rewrite G11; reflexivity | split; [lia | exact G12]]) G2 ltac:(lia) ltac:(unfold w_sp0, PM_FRAME; lia)
              ltac:(apply mod16_8; [exact Gsp16 | reflexivity]) G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
    intros R2 M2 r d KEPT Hr Rr Fd Hfound Hhnd X2 AG.
    keptQ KEPT G2 Qsp2. keptQ KEPT G8 Qs02. keptQ KEPT G3 Qgp2. keptQ KEPT G4 Qtp2. keptQ KEPT G27 Q27b.
    pose proof (oregs_kept w R1 R2 OR1 KEPT) as OR2.
    assert (GK2 : forall r', In r' [22; 23; 24; 26]%bv -> getr R2 r' = getr R r').
    { intros r' Hr'. rewrite (KEPT r') by (revert Hr'; clear; intros Hr'; apply in_reg_list; cbn in Hr'; decompose [or] Hr'; try contradiction; subst r'; reflexivity). apply GK1. exact Hr'. }
    clear G1 G2 G3 G4 G8 G10 G11 G12 G27 GK1 OR1 KEPT.
    pose proof (x_ms X2) as MS2.
    assert (AG02 : CRep.agree_on (fun a => w_sp w <= a < w_sp w + 864 /\ ~ zwin (w_sp w + 280) (w_sp w + 288) a) M M2).
    { intros a Ha. rewrite (AG a ltac:(unfold w_sp0, PM_FRAME, zwin in *; lia)). apply (stores_in_agree _ _ _ _ ST1 ltac:(intros b Hb; exact Hb)). unfold zwin in *. lia. }
    assert (OB2 : forall Rx, oregs w Rx -> OBASE w I A M2 model c Rx).
    { intros Rx ORx. split; [exact X2|]. split; [exact Htr|]. split; [exact BUD|]. split; [exact ORx|].
      split; [eapply (loop_mem_frame w M M2); [exact LM | lia | lia | eapply agree_on_weaken; [exact AG02 | unfold zwin; cbn; intros; lia]]|].
      split; [eapply (ictx_agree w M M2); [exact IC | lia | lia | eapply agree_on_weaken; [exact AG02 | unfold zwin; cbn; intros; lia]]|].
      split; [eapply (ifr_agree w M M2); [exact FR | lia | lia | eapply agree_on_weaken; [exact AG02 | unfold zwin; cbn; intros; lia]]|].
      split; [exact Hic|]. split; [exact Hend|]. split; [exact Hwnz|]. split; [exact MAC | exact V3R]. }
    assert (C718' : cellw SEGS M2 (w_sp w + 718) 2 1).
    { eapply (cellw_frame M M2); [exact C718 | lia | cbn; lia | eapply agree_on_weaken; [exact AG02 | unfold zwin; cbn; intros; lia]]. }
    clear ST1 X X1 MS MS1 AG. clearbody M1. clear M1.
    pose proof OR2 as OR'. destruct OR' as (_ & _ & _ & _ & Ps1 & Ps2 & Ps3 & Ps4 & Ps5 & Ps9).

    destruct (Z.eq_dec r 0) as [Hr0 | Hr1].
    -
      subst r. specialize (Hhnd eq_refl). cbn beta in Hhnd.
      pose proof (ODESC_PTR d t 0 Hhnd) as (Hd1 & Hd2 & Hd4).
      pm_seed R2 w c [Z_to_bv 64 0; Z_to_bv 64 d].
      seedHR HR E ([(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, EVar 39)] ++ OREGSEED)%list R2. seedHK HK w A M2 model c E X2.
      apply (know_more E M2 [KRange (EVar 39) 0 0; KWord (SA (EVar 32) 280) (N.to_nat 8) (EVar 40); KRange (EVar 40) 0x10000 (2 ^ 40); KAlign (EVar 40) 4]) in HK.
      2: { repeat apply Forall_cons; try apply Forall_nil.
           - eapply krange_var; [evs; reflexivity | lia | lia].
           - eapply kword_var; [eapply fld_cellw; [exact Fd | cbn; lia] | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
           - eapply krange_var; [evs; reflexivity | lia | lia].
           - eapply kalign_var; [evs; reflexivity | lia | lia | exact Hd4]. }
      xruns HR HK 100%nat (0x67f48 :: STOPS) (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
      postrun. name_run HRn R3.
      rreg HRn (10%bv) G10.
      pose proof (syms_id_sound _ _ _ _ [22; 23; 24; 26; 27]%bv HRn eq_refl) as GK3.
      assert (OR3 : oregs w R3) by (oregs_seeded HRn Qgp2 Qtp2). clear HRn HR HK.
      eapply (pm_opnd_push w c0 K fx I A M2 model c R3 d t 0 PS (OB2 R3 OR3) Hhnd G10 Hmax).
      intros A' M' model' R' b' cap' l l' Hg El' SF' Hlen' OB' GK' AG'.
      pose proof (go_len_operand G GOK t 0 l Hg) as Hll. unfold HRep.Zlength in Hll. change (Zlen l <= g_maxlen G) in Hll.
      eapply (PK A' M' model' _ R' 1 l' OB').
      + rewrite (GK' 27%bv ltac:(first [solve [clear; cbn; tauto] | cbn; tauto])), (GK3 27%bv ltac:(first [solve [clear; cbn; tauto] | cbn; tauto])). exact Q27b.
      + rewrite (GK' 23%bv ltac:(first [solve [clear; cbn; tauto] | cbn; tauto])), (GK3 23%bv ltac:(first [solve [clear; cbn; tauto] | cbn; tauto])), (GK2 23%bv ltac:(first [solve [clear; cbn; tauto] | cbn; tauto])). exact Q23.
      + rewrite (GK' 26%bv ltac:(first [solve [clear; cbn; tauto] | cbn; tauto])), (GK3 26%bv ltac:(first [solve [clear; cbn; tauto] | cbn; tauto])), (GK2 26%bv ltac:(first [solve [clear; cbn; tauto] | cbn; tauto])). exact Q26.
      + eapply (cellw_frame M2 M'); [exact C718' | lia | cbn; lia | eapply agree_on_weaken; [exact AG' | unfold zwin, w_sp0, PM_FRAME; cbn; intros; lia]].
      + left. lia.
      + reflexivity. + reflexivity. + reflexivity.
      + unfold PmLoopU1.nodes. cbn [set_v3 c_m1 c_m2 c_m3]. lia.
      + cbn [set_v3 c_v3 t3b fst snd]. exact El'.
      + exact SF'.
      + lia.
      + right. exact Ht36.
      + reflexivity. + left; reflexivity. + left; reflexivity.
      + exact (notrid_operand CL _ _ _ _ _ Hg El').
    -
      pm_seed R2 w c [Z_to_bv 64 r].
      seedHR HR E ([(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, EVar 39)] ++ OREGSEED)%list R2. seedHK HK w A M2 model c E X2.
      apply (know_more E M2 [KRange (EVar 39) 1 (2 ^ 64 - 1)]) in HK.
      2: { repeat apply Forall_cons; try apply Forall_nil. eapply krange_var; [evs; reflexivity | lia | lia]. }
      xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
      postrun. name_run HRn R3.
      pose proof (syms_id_sound _ _ _ _ [22; 23; 24; 26; 27]%bv HRn eq_refl) as GK3.
      assert (OR3 : oregs w R3) by (oregs_seeded HRn Qgp2 Qtp2). clear HRn HR HK.
      eapply (PK A M2 model c R3 1 [] (OB2 R3 OR3)).
      + rewrite (GK3 27%bv ltac:(first [solve [clear; cbn; tauto] | cbn; tauto])). exact Q27b.
      + rewrite (GK3 23%bv ltac:(first [solve [clear; cbn; tauto] | cbn; tauto])), (GK2 23%bv ltac:(first [solve [clear; cbn; tauto] | cbn; tauto])). exact Q23.
      + rewrite (GK3 26%bv ltac:(first [solve [clear; cbn; tauto] | cbn; tauto])), (GK2 26%bv ltac:(first [solve [clear; cbn; tauto] | cbn; tauto])). exact Q26.
      + exact C718'.
      + left. lia.
      + reflexivity. + reflexivity. + reflexivity.
      + lia.
      + rewrite app_nil_r. reflexivity.
      + exact seed_free_nil.
      + rewrite Zlen_nil. lia.
      + left; reflexivity.
      + reflexivity. + left; reflexivity. + left; reflexivity. + intros [].
  Qed.

  Definition mask_et (t : Z) : Z :=
    if t =? 43 then 35 else if t =? 44 then 40 else if t =? 78 then 77 else if t =? 87 then 86
    else if t =? 92 then 91 else if t =? 104 then 103 else t.

  Ltac mdisp1 w A M model c R X CONT Q27 OR C720 :=
    lazymatch type of Q27 with getr _ _ = Z_to_bv 64 ?tv =>
    let E := fresh "E" in let HR := fresh "HR" in let HK := fresh "HK" in
    pm_seed R w c (@nil word);
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (27%bv, ELit tv)] R; seedHK HK w A M model c E X;
    apply (know_more E M [KImg 0x14840 0x1491c]) in HK;
    [ xruns HR HK 100%nat (0x67a08 :: STOPS) (SCR [] [] []) 50%N; [ split_scs; try sc_auto1 |];
      postrun;
      let HRn := fresh "HRn" in let R1 := fresh "R1" in
      name_run HRn R1;
      let G2 := fresh "G2" in let G3 := fresh "G3" in let G4 := fresh "G4" in let G8 := fresh "G8" in
      let G27 := fresh "G27" in let GS := fresh "GS" in let GK := fresh "GK" in
      rreg HRn (2%bv) G2; rreg HRn (3%bv) G3; rreg HRn (4%bv) G4; rreg HRn (8%bv) G8; rreg HRn (27%bv) G27;
      pose proof (syms_id_sound _ _ _ _ PmInstU1.SREGS HRn eq_refl) as GS;
      pose proof (syms_id_sound _ _ _ _ [22; 23; 24; 26]%bv HRn eq_refl) as GK;
      clear HRn HR HK; fixregs;
      eapply (CONT R1 _ ltac:(eapply (PmInstU1.loop_regs_glue w R R1); [exact OR | exact GS | exact G2 | exact G3 | exact G4 | exact G8]));
      [exact G27 | exact GK | first [left; reflexivity | right; reflexivity] | first [exact C720 | split; [cbn; lia | rdback]] ]
    | repeat apply Forall_cons; try apply Forall_nil; eapply (rodata_kimg w); [exact X | lia | lia] ]
    end.

  Lemma mask_disp : forall (w : pmw MI ST) A M model c (fx : FPState) R (t : Z) K,
    PMX w A M model c -> oregs w R -> getr R 27%bv = Z_to_bv 64 t -> In t MASK_TYPES -> cellw SEGS M (w_sp w + 720) 4 t ->
    (forall R' M', oregs w R' -> getr R' 27%bv = Z_to_bv 64 t ->
        (forall r, In r [22; 23; 24; 26]%bv -> getr R' r = getr R r) ->
        (M' = M \/ M' = wbytes M (Z_to_bv 64 (w_sp w + 720)) (word_to_le_bytes 4 (Z_to_bv 64 (mask_et t)))) ->
        cellw SEGS M' (w_sp w + 720) 4 (mask_et t) ->
        srealizes SEGS (cfg fx R' 0x67a08 M' model) K) ->
    srealizes SEGS (cfg fx R 0x678d8 M model) K.
  Proof using AC MI ST.
    intros w A M model c fx R t K X OR Q27 HIn C720 CONT.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof OR as OR'. destruct OR' as (Qsp & Qgp & Qtp & Qs0 & Qs1 & Qs2 & Qs3 & Qs4 & Qs5 & Qs9).
    unfold MASK_TYPES in HIn. cbn in HIn.
    repeat match type of HIn with
           | _ \/ _ => destruct HIn as [HIn|HIn]; [subst t; cbn [mask_et Z.eqb Pos.eqb] in CONT; mdisp1 w A M model c R X CONT Q27 OR C720 |]
           | False => destruct HIn
           end.
  Qed.

  Definition MDIAGK (w : pmw MI ST) (K : TSet) (fx : FPState) (word et : Z) : Prop :=
    forall A M model c' R (m : Z),
      PMX w A M model c' -> c_tr c' = [] -> pm_bud (w_n w) c' -> oregs w R ->
      cellw SEGS M (w_sp w + 712) 4 word -> cellw SEGS M (w_sp w + 720) 4 et -> getr R 24%bv = sxw m -> 0 < m < 2 ^ 32 ->
      srealizes SEGS (cfg fx R 0x67aac M model) K.

  Lemma mask_diag : forall (w : pmw MI ST) c0 K (fx : FPState) (wv et : Z),
    PMS w c0 K -> frm_zero (@fp_csr fx) -> CHECKK w K fx -> 0 <= wv < 2 ^ 32 -> 0 <= et < 2 ^ 31 ->
    MDIAGK w K fx wv et.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx wv et PS FZ CK Hword Het. unfold MDIAGK.
    intros A M model c R m X Htr BUD OR C712 C720 Q24 Hm.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (x_scal X) as (Sc1 & Sc2 & Sc3 & Sc4).
    pose proof OR as OR'. destruct OR' as (Qsp & Qgp & Qtp & Qs0 & Qs1 & Qs2 & Qs3 & Qs4 & Qs5 & Qs9).
    assert (Het32 : 0 <= et < 2 ^ 32) by lia.
    pm_seed R w c (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (18%bv, ELit 1)] R. seedHK HK w A M model c E X.
    apply (know_more E M [KWord (SA (EVar 33) 40) (N.to_nat 1) (ELit 0)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         - eapply kword_var; [eapply fld_cellw; [exact (x_hunk X) | cbn; lia] | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | cbn [edenot]; reflexivity]. }
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R1.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12. rreg HRn (24%bv) G24.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    try replace (Z_to_bv 5 (Z.of_N 24)) with (24%bv : reg) in * by (apply bv_eq; reflexivity). rewrite ?Q24 in *. clear Q24. rename G24 into Q24.
    eapply (pm_pdiagQ w c0 K fx A M model c R1 (-4) _ []);
      [exact PS | exact X | exact Htr | exact BUD | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | rewrite G12; apply bv_eq; vm_compute; reflexivity | lia |].
    clear Qsp Qs0 Qgp Qtp. intros A1 R1c M1 model1 B1 X1 BUD1 KEPT DS1 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp. keptQ KEPT Q24 Q24_. clear Q24. rename Q24_ into Q24.
    eapply (cellw_frame _ M1) in C712; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M1) in C720; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X0 BUD0. pose proof (x_ms X1) as MS1.
    pm_seed R1c w (set_tr c (B1 ++ [])) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R1c. seedHK HK w A1 M1 model1 (set_tr c (B1 ++ [])) E X1.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R2.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12. rreg HRn (24%bv) G24.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    try replace (Z_to_bv 5 (Z.of_N 24)) with (24%bv : reg) in * by (apply bv_eq; reflexivity). rewrite ?Q24 in *. clear Q24. rename G24 into Q24.
    eapply (pm_put_cstr w c0 K fx A1 M1 model1 (set_tr c (B1 ++ [])) R2 (-4) _ 0x10556 8 8 _ B1 []);
      [exact PS | exact X1 | reflexivity | exact BUD1 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS1 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | apply ro_cstr_of_chk; vm_compute; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A2 R2c M2 model2 B2 X2 BUD2 KEPT _ DS2 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp. keptQ KEPT Q24 Q24_. clear Q24. rename Q24_ into Q24.
    eapply (cellw_frame _ M2) in C712; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M2) in C720; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X1 BUD1 DS1. pose proof (x_ms X2) as MS2.
    pm_seed R2c w (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) [Z_to_bv 64 et].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R2c. seedHK HK w A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) E X2.
    apply (know_more E M2 [KWord (SA (EVar 32) 720) (N.to_nat 4) (EVar 39); KRange (EVar 39) 0 (2 ^ 31 - 1)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         - eapply kword_var; [exact C720 | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply krange_var; [evs; reflexivity | lia | lia]. }
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R3.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (24%bv) G24.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    try replace (Z_to_bv 5 (Z.of_N 24)) with (24%bv : reg) in * by (apply bv_eq; reflexivity). rewrite ?Q24 in *. clear Q24. rename G24 into Q24.
    rewrite ?ext_val_sx4, ?sx32_small in G10 by lia.
    eapply (pm_operand_type_str w A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) fx R3 _ K X2 (ex_intro _ et (conj Het32 G10)) G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
    clear Qsp Qs0 Qgp Qtp. intros R3n KEPT (pnm & nnm & ROnm & Hn256 & Gnm).
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp. keptQ KEPT Q24 Q24_. clear Q24. rename Q24_ into Q24.
    clear G1 G2 G3 G4 G8 G10 KEPT; try clear G9; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    pose proof ROnm as RO'. destruct RO' as (Rp1 & Rn0 & Rp2 & _).
    pm_seed R3n w (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) [Z_to_bv 64 pnm].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, EVar 39)] R3n. seedHK HK w A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) E X2.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R4.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (22%bv) G22. rreg HRn (24%bv) G24.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    try replace (Z_to_bv 5 (Z.of_N 24)) with (24%bv : reg) in * by (apply bv_eq; reflexivity). rewrite ?Q24 in *. clear Q24. rename G24 into Q24.
    try replace (Z_to_bv 5 (Z.of_N 22)) with (22%bv : reg) in * by (apply bv_eq; reflexivity). rename G22 into Q22p.
    eapply (pm_strlen w A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) fx R4 _ K X2 (ex_intro _ pnm (ex_intro _ nnm (conj ROnm G10))) G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
    clear Qsp Qs0 Qgp Qtp. intros R4s KEPT POst. pose proof (POst pnm nnm ROnm G10) as Gsl. clear POst.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp. keptQ KEPT Q24 Q24_. clear Q24. rename Q24_ into Q24. keptQ KEPT Q22p Q22p_. clear Q22p. rename Q22p_ into Q22p.
    clear G1 G2 G3 G4 G8 G10 KEPT; try clear G9; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    pm_seed R4s w (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) [Z_to_bv 64 nnm; Z_to_bv 64 pnm].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, EVar 39); (22%bv, EVar 40)] R4s. seedHK HK w A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) E X2.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R5.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12. rreg HRn (24%bv) G24.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    try replace (Z_to_bv 5 (Z.of_N 24)) with (24%bv : reg) in * by (apply bv_eq; reflexivity). rewrite ?Q24 in *. clear Q24. rename G24 into Q24.
    eapply (pm_put_cstr w c0 K fx A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) R5 (-4) _ pnm nnm nnm _ B2 []);
      [exact PS | exact X2 | reflexivity | exact BUD2 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS2 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | exact ROnm | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A5 R5c M5 model5 B5 X5 BUD5 KEPT _ DS5 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp. keptQ KEPT Q24 Q24_. clear Q24. rename Q24_ into Q24.
    eapply (cellw_frame _ M5) in C712; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M5) in C720; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X4 BUD4 DS4. pose proof (x_ms X5) as MS5.
    pm_seed R5c w (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R5c. seedHK HK w A5 M5 model5 (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) E X5.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R6.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12. rreg HRn (24%bv) G24.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    try replace (Z_to_bv 5 (Z.of_N 24)) with (24%bv : reg) in * by (apply bv_eq; reflexivity). rewrite ?Q24 in *. clear Q24. rename G24 into Q24.
    eapply (pm_put_cstr w c0 K fx A5 M5 model5 (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) R6 (-4) _ 0x126ed 10 10 _ B5 []);
      [exact PS | exact X5 | reflexivity | exact BUD5 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS5 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | apply ro_cstr_of_chk; vm_compute; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A6 R6c M6 model6 B6 X6 BUD6 KEPT _ DS6 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp. keptQ KEPT Q24 Q24_. clear Q24. rename Q24_ into Q24.
    eapply (cellw_frame _ M6) in C712; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M6) in C720; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X5 BUD5 DS5. pose proof (x_ms X6) as MS6.
    pm_seed R6c w (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) [sxw wv].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R6c. seedHK HK w A6 M6 model6 (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) E X6.
    xruns HR HK 100%nat STOPS (SCR [] [EVar 39] []) 50%N. { split_scs; try sc_auto1. all: sc_rd_sx C712. }
    postrun. name_run HRn R7.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (24%bv) G24.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    try replace (Z_to_bv 5 (Z.of_N 24)) with (24%bv : reg) in * by (apply bv_eq; reflexivity). rewrite ?Q24 in *. clear Q24. rename G24 into Q24.
    eapply (pm_put_u32 w c0 K fx A6 M6 model6 (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) R7 (-4) _ (wv) _ B6 []);
      [exact PS | exact X6 | reflexivity | exact BUD6 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS6 | cregs_tac G1 G2 G3 G4
      | exact G10 | rewrite G11; apply sxw_sx32; lia | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A7 R7c M7 model7 B7 X7 BUD7 KEPT _ DS7 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp. keptQ KEPT Q24 Q24_. clear Q24. rename Q24_ into Q24.
    eapply (cellw_frame _ M7) in C712; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M7) in C720; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X6 BUD6 DS6. pose proof (x_ms X7) as MS7.
    pm_seed R7c w (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R7c. seedHK HK w A7 M7 model7 (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) E X7.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R8.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12. rreg HRn (24%bv) G24.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    try replace (Z_to_bv 5 (Z.of_N 24)) with (24%bv : reg) in * by (apply bv_eq; reflexivity). rewrite ?Q24 in *. clear Q24. rename G24 into Q24.
    eapply (pm_put_cstr w c0 K fx A7 M7 model7 (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) R8 (-4) _ 0x109b6 28 28 _ B7 []);
      [exact PS | exact X7 | reflexivity | exact BUD7 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS7 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | apply ro_cstr_of_chk; vm_compute; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A8 R8c M8 model8 B8 X8 BUD8 KEPT _ DS8 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp. keptQ KEPT Q24 Q24_. clear Q24. rename Q24_ into Q24.
    eapply (cellw_frame _ M8) in C712; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M8) in C720; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X7 BUD7 DS7. pose proof (x_ms X8) as MS8.
    pm_seed R8c w (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) [sxw m].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (24%bv, EVar 39)] R8c. seedHK HK w A8 M8 model8 (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) E X8.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R9.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_put_u32 w c0 K fx A8 M8 model8 (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) R9 (-4) _ (m) _ B8 []);
      [exact PS | exact X8 | reflexivity | exact BUD8 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS8 | cregs_tac G1 G2 G3 G4
      | exact G10 | rewrite G11; apply sxw_sx32; lia | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A9 R9c M9 model9 B9 X9 BUD9 KEPT _ DS9 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    eapply (cellw_frame _ M9) in C712; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M9) in C720; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X8 BUD8 DS8. pose proof (x_ms X9) as MS9.
    pose proof (dl_err _ _ _ _ _ _ DL _ _ _ _ _ _ DS9) as Herrc. unfold CRep.fld in Herrc.
    assert (Cerr : cell4 SEGS M9 (w_sp w + 304 + 360) ((-4) mod 2 ^ 32)).
    { split; [pose proof (Z.mod_pos_bound (-4) (2 ^ 32)); cbn; lia | exact Herrc]. }
    pm_seed R9c w (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) (B9 ++ [])) [sxw ((-4) mod 2 ^ 32)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R9c. seedHK HK w A9 M9 model9 (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) (B9 ++ [])) E X9.
    xruns HR HK 100%nat STOPS (SCR [] [EVar 39] []) 50%N. { split_scs; try sc_auto1. all: sc_rd_sx Cerr. }
    postrun. name_run HRn R9cd. rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (22%bv) G22.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.  rewrite w_add in G10 by lia.
    eapply (pm_dtor w c0 K fx A9 M9 model9 (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) (B9 ++ [])) R9cd (-4) _ _ B9 []);
      [exact PS | exact X9 | cbn [c_tr set_tr]; rewrite ?app_nil_r; reflexivity | exact BUD9 | rewrite Zlength_nil; lia | exact DS9 | cregs_tac G1 G2 G3 G4 | exact G10 |].
    intros Ad Rd Md modeld Xd BUDd KEPT AGd.
    keptQ KEPT G2 Qsp'. keptQ KEPT G3 Qgp'. keptQ KEPT G4 Qtp'. keptQ KEPT G8 Qs0'. keptQ KEPT G22 Qs6.
    pose proof (Z.mod_pos_bound (-4) (2 ^ 32) ltac:(lia)) as Hm'.
    assert (Hnz : (-4) mod 2 ^ 32 <> 0) by (rewrite <- (Z.mod_add (-4) 1 (2 ^ 32)) by lia; rewrite Z.mod_small by lia; lia).
    pose proof (x_ms Xd) as MSd.
    try clear E. pm_seed Rd w (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) (B9 ++ [])) []) [sxw ((-4) mod 2 ^ 32)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (22%bv, EVar 39)] Rd. seedHK HK w Ad Md modeld (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) (B9 ++ [])) []) E Xd.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn Re. rreg HRn (2%bv) T2. rreg HRn (3%bv) T3. rreg HRn (4%bv) T4. rreg HRn (8%bv) T8. rreg HRn (22%bv) T22.
    clear HRn HR HK. fixregs. rewrite Qgp' in T3. rewrite Qtp' in T4.
    eapply (CK Ad Md modeld (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) (B9 ++ [])) []) Re ((-4) mod 2 ^ 32) Xd ltac:(cbn [c_tr set_tr]; reflexivity) BUDd T2 T3 T4 T8 T22 ltac:(lia)).
  Qed.

  Section MaskLoop.
    Variables (w : pmw MI ST) (c0 : parserC) (K : TSet) (fx : FPState) (I : ictxR) (c : pmc) (t word : Z).
    Hypothesis PS : PMS w c0 K.
    Hypothesis IP : ipure I.
    Hypothesis HIn : In t MASK_TYPES.
    Hypothesis Ht : 0 <= t < 2 ^ 31.
    Hypothesis Hword : 0 < word < 2 ^ 32.
    Hypothesis V3B : Zlen (t3b (c_v3 c)) + 126 <= V3MAX.
    Hypothesis PK : PUSHK w I K fx c t.
    Hypothesis DK : MDIAGK w K fx word (mask_et t).

    Lemma pow2_range32 : forall j, 0 <= j <= 31 -> 0 < 2 ^ j < 2 ^ 32.
    Proof using. intros j Hj. split; [apply Z.pow_pos_nonneg; lia|]. apply Z.pow_lt_mono_r; lia. Qed.

    Ltac scM Hand := split_scs; try sc_auto1; cbn [sc_denot]; evs; rewrite ?Hand; rewrite <- ?(sxw_small' 0) by lia;
      rewrite br_eq_sxw by lia; bool_lia.

    Definition mcells (M : mem) : Prop :=
      cellw SEGS M (w_sp w + 718) 2 1 /\ cellw SEGS M (w_sp w + 712) 4 word /\ cellw SEGS M (w_sp w + 720) 4 (mask_et t).
    Lemma mcells_agree : forall M M', mcells M -> 0 <= w_sp w -> w_sp w + 724 < 2 ^ 64 ->
      CRep.agree_on (zwin (w_sp w + 712) (w_sp w + 724)) M M' -> mcells M'.
    Proof using AC MI ST w t word.
      intros M M' (C1 & C2 & C3) Hlo Hhi AG. unfold mcells.
      repeat match goal with |- _ /\ _ => split end;
        (eapply (cellw_frame M M'); [eassumption | lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold zwin; cbn; intros; lia]]).
    Qed.

    Lemma mask_loop : forall (k : nat) A M model c' R (L : list Z),
      Z.of_nat k <= 31 ->
      OBASE w I A M model c' R ->
      c_widx c' = c_widx c -> c_v1 c' = c_v1 c -> c_v2 c' = c_v2 c -> nodes c' = nodes c ->
      c_m1 c' = c_m1 c -> c_m2 c' = c_m2 c -> c_m3 c' = c_m3 c ->
      t3b (c_v3 c') = t3b (c_v3 c) ++ L -> seed_free L -> ~ In OT_RESULT_ID L -> Zlen L <= 3 * (31 - Z.of_nat k) ->
      getr R 27%bv = Z_to_bv 64 t -> getr R 23%bv = Z_to_bv 64 (i_io I) -> getr R 26%bv = Z_to_bv 64 (i_op I) ->
      getr R 24%bv = sxw (2 ^ Z.of_nat k) -> getr R 22%bv = sxw (word mod 2 ^ (Z.of_nat k + 1)) -> word mod 2 ^ (Z.of_nat k + 1) <> 0 ->
      mcells M ->
      srealizes SEGS (cfg fx R 0x67a1c M model) K.
    Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL w c0 K fx I c t word PS HIn Ht Hword V3B PK DK.
      intros k. induction k as [kk IH] using (well_founded_induction Wf_nat.lt_wf).
      intros A M model c' R L Hk OB Ewidx Ev1 Ev2 Enodes Em1c Em2c Em3c EL SFL NRL HLL Q27 Q23 Q26 Q24 Q22 Hrem MC.
      set (j := Z.of_nat kk) in *.
      pose proof OB as OB'. destruct OB' as (X & Htr & BUD & OR & LM & IC & FR & Hic & Hend & Hwnz & MAC & V3R).
      pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
      destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
      pose proof OR as OR'. destruct OR' as (Qsp & Qgp & Qtp & Qs0 & Qs1 & Qs2 & Qs3 & Qs4 & Qs5 & Qs9).
      assert (Hj : 0 <= j <= 31) by lia. pose proof (pow2_range32 j Hj) as Hpj.
      set (rem := word mod 2 ^ (j + 1)) in *.
      assert (Hremr : 0 <= rem < 2 ^ (j + 1)) by (subst rem; apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia).
      assert (Hjr : 2 ^ (j + 1) <= 2 ^ 32) by (apply Z.pow_le_mono_r; lia).
      pose proof (mod_pow2_step word j ltac:(lia) ltac:(lia)) as STEP. fold rem in STEP.
      assert (Hbit : Z.testbit rem j = Z.testbit word j) by (subst rem; apply testbit_mod_pow2; lia).
      assert (Het : 0 <= mask_et t < 2 ^ 31) by (unfold mask_et; repeat match goal with |- context [if ?x =? ?y then _ else _] => destruct (Z.eqb_spec x y) end; lia).

      pm_seed R w c' [sxw (2 ^ j); sxw rem; Z_to_bv 64 t].
      seedHR HR E ([(2%bv, EVar 32); (8%bv, EVar 33); (24%bv, EVar 39); (22%bv, EVar 40); (27%bv, EVar 41)] ++ OREGSEED)%list R. seedHK HK w A M model c' E X.
      assert (Hand : alu64 ALU_AND (sxw (2 ^ j)) (sxw rem) = sxw (if Z.testbit word j then 2 ^ j else 0)).
      { rewrite land_sxw by lia. rewrite land_pow2_testbit, Hbit by lia. reflexivity. }
      destruct (Z.testbit word j) eqn:TB.
      2: {
           assert (Erem : rem = word mod 2 ^ j) by lia.
           assert (Hj1 : 1 <= j).
           { destruct (Z.eq_dec j 0) as [E0|]; [| lia]. exfalso. rewrite E0 in Erem. change (2 ^ 0) with 1 in Erem. rewrite Z.mod_1_r in Erem. lia. }
           xruns HR HK 100%nat (0x67a1c :: 0x67aac :: STOPS) (SCR [true; false] [] []) 50%N; [scM Hand|].
           postrun. name_run HRn R1.
           rreg HRn (24%bv) G24. rreg HRn (22%bv) G22. rreg HRn (27%bv) G27.
           pose proof (syms_id_sound _ _ _ _ [23; 26]%bv HRn eq_refl) as GK.
           assert (OR1 : oregs w R1) by (oregs_seeded HRn Qgp Qtp). clear HRn HR HK.
           rewrite srliw1_mask in G24 by lia.
           destruct kk as [|kk']; [exfalso; subst j; cbn in Hj1; lia|].
           apply (IH kk' ltac:(lia) A M model c' R1 L ltac:(lia)).
           - split; [exact X|]. split; [exact Htr|]. split; [exact BUD|]. split; [exact OR1|]. repeat (split; [assumption|]). exact V3R.
           - exact Ewidx. - exact Ev1. - exact Ev2. - exact Enodes. - exact Em1c. - exact Em2c. - exact Em3c. - exact EL. - exact SFL. - exact NRL. - lia.
           - exact G27. - rewrite (GK 23%bv) by (clear; inl); exact Q23. - rewrite (GK 26%bv) by (clear; inl); exact Q26.
           - rewrite G24. f_equal. f_equal. lia.
           - rewrite G22. rewrite Erem. f_equal. f_equal. f_equal. lia.
           - replace (Z.of_nat kk' + 1) with j by lia. rewrite <- Erem. lia.
           - exact MC. }

      assert (Hrj : 2 ^ j <= rem) by lia.
      xruns HR HK 100%nat (0x67a1c :: 0x67aac :: STOPS) (SCR [false] [] []) 50%N.
      { scM Hand. }
      postrun. name_run HRn R1.
      rreg HRn (1%bv) G1. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
      rreg HRn (27%bv) G27. rreg HRn (22%bv) G22a. rreg HRn (24%bv) G24a.
      pose proof (syms_id_sound _ _ _ _ [23; 26]%bv HRn eq_refl) as GK1.
      assert (OR1 : oregs w R1) by (oregs_seeded HRn Qgp Qtp).
      pose proof OR1 as OR'. destruct OR' as (G2 & G3 & G4 & G8 & _). clear HRn HR HK.
      rewrite ?SymExec.alu64_add_lit in G12. rewrite ?w_add in G12 by lia.
      lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M1 := m) in * end.
      assert (ST1 : stores_in (zwin (w_sp w + 280) (w_sp w + 288)) M M1) by (unfold M1; stin).
      assert (X1 : PMX w A M1 model c').
      { eapply (pmx_frame_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img w A M M1 model c' (zwin (w_sp w + 280) (w_sp w + 288)));
          [exact X | exact ST1 | unfold zwin, w_sp0, PM_FRAME; intros; lia]. }
      pose proof (x_ms X1) as MS1.
      eapply (pm_lookup_operand w A M1 model c' fx R1 t (2 ^ j) (w_sp w + 280) _ K X1 G10 ltac:(lia) ltac:(intros HH; discriminate HH)
                ltac:(intros _; split; [rewrite G11, TablStmts.sx32_prs; apply sxw_sx32; lia | split; [lia | exact G12]]) G2 ltac:(lia) ltac:(unfold w_sp0, PM_FRAME; lia)
                ltac:(apply mod16_8; [exact Gsp16 | reflexivity]) G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
      intros R2 M2 r d KEPT Hr Rr Fd Hfound Hhnd X2 AG.
      keptQ KEPT G2 Qsp2. keptQ KEPT G8 Qs02. keptQ KEPT G3 Qgp2. keptQ KEPT G4 Qtp2. keptQ KEPT G27 Q27b. keptQ KEPT G22a Q22b. keptQ KEPT G24a Q24b.
      pose proof (oregs_kept w R1 R2 OR1 KEPT) as OR2.
      assert (GK2 : forall r', In r' [23; 26]%bv -> getr R2 r' = getr R r').
      { intros r' Hr'. rewrite (KEPT r') by (revert Hr'; clear; intros Hr'; apply in_reg_list; cbn in Hr'; decompose [or] Hr'; try contradiction; subst r'; reflexivity). apply GK1. exact Hr'. }
      clear G1 G2 G3 G4 G8 G10 G11 G12 GK1 OR1 KEPT G22a G24a.
      pose proof (x_ms X2) as MS2.
      assert (AG02 : CRep.agree_on (fun a => w_sp w <= a < w_sp w + 864 /\ ~ zwin (w_sp w + 280) (w_sp w + 288) a) M M2).
      { intros a Ha. rewrite (AG a ltac:(unfold w_sp0, PM_FRAME, zwin in *; lia)). apply (stores_in_agree _ _ _ _ ST1 ltac:(intros b Hb; exact Hb)). unfold zwin in *. lia. }
      assert (LM2 : loop_mem w M2) by (eapply (loop_mem_frame w M M2); [exact LM | lia | lia | eapply agree_on_weaken; [exact AG02 | unfold zwin; cbn; intros; lia]]).
      assert (IC2 : ictx w M2 (i_io I) (i_fw I) (i_iwc I) (i_op I) (i_d I)) by (eapply (ictx_agree w M M2); [exact IC | lia | lia | eapply agree_on_weaken; [exact AG02 | unfold zwin; cbn; intros; lia]]).
      assert (FR2 : ifr w M2) by (eapply (ifr_agree w M M2); [exact FR | lia | lia | eapply agree_on_weaken; [exact AG02 | unfold zwin; cbn; intros; lia]]).
      assert (MC2 : mcells M2) by (eapply (mcells_agree M M2); [exact MC | lia | lia | eapply agree_on_weaken; [exact AG02 | unfold zwin; cbn; intros; lia]]).
      clear ST1 X X1 MS MS1 AG. clearbody M1. clear M1.
      pose proof OR2 as OR'. destruct OR' as (_ & _ & _ & _ & Ps1 & Ps2 & Ps3 & Ps4 & Ps5 & Ps9).

      pm_seed R2 w c' [Z_to_bv 64 r; Z_to_bv 64 d; sxw (2 ^ j); sxw rem].
      seedHR HR E ([(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, EVar 39); (24%bv, EVar 41); (22%bv, EVar 42)] ++ OREGSEED)%list R2. seedHK HK w A M2 model c' E X2.
      destruct (Z.eq_dec r 0) as [Hr0 | Hr1].
      2: {
           apply (know_more E M2 [KRange (EVar 39) 1 (2 ^ 64 - 1)]) in HK.
           2: { repeat apply Forall_cons; try apply Forall_nil. eapply krange_var; [evs; reflexivity | lia | lia]. }
           xruns HR HK 100%nat (0x67a1c :: 0x67aac :: STOPS) (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
           postrun. name_run HRn R3.
           rreg HRn (24%bv) G24.
           assert (OR3 : oregs w R3) by (oregs_seeded HRn Qgp2 Qtp2). clear HRn HR HK.
           destruct MC2 as (C718_2 & C712_2 & C720_2).
           apply (DK A M2 model c' R3 (2 ^ j) X2 Htr BUD OR3 C712_2 C720_2 G24). lia. }

      subst r. specialize (Hhnd eq_refl). cbn beta in Hhnd.
      pose proof (ODESC_PTR d t (2 ^ j) Hhnd) as (Hd1 & Hd2 & Hd4).
      apply (know_more E M2 [KRange (EVar 39) 0 0; KWord (SA (EVar 32) 280) (N.to_nat 8) (EVar 40); KRange (EVar 40) 0x10000 (2 ^ 40); KAlign (EVar 40) 4]) in HK.
      2: { repeat apply Forall_cons; try apply Forall_nil.
           - eapply krange_var; [evs; reflexivity | lia | lia].
           - eapply kword_var; [eapply fld_cellw; [exact Fd | cbn; lia] | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
           - eapply krange_var; [evs; reflexivity | lia | lia].
           - eapply kalign_var; [evs; reflexivity | lia | lia | exact Hd4]. }
      xruns HR HK 100%nat (0x67a1c :: 0x67aac :: STOPS) (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
      postrun. name_run HRn R3.
      rreg HRn (1%bv) G1. rreg HRn (10%bv) G10. rreg HRn (22%bv) G22. rreg HRn (24%bv) G24.
      pose proof (syms_id_sound _ _ _ _ [23; 26; 27]%bv HRn eq_refl) as GK3.
      assert (OR3 : oregs w R3) by (oregs_seeded HRn Qgp2 Qtp2).
      pose proof OR3 as OR'. destruct OR' as (G2 & G3 & G4 & G8 & _). clear HRn HR HK.
      rewrite lxor_sxw, lxor_pow2_clear in G22 by first [lia | rewrite Hbit; reflexivity].
      eapply (pm_odesc_operands w A M2 model c' fx R3 _ K X2 (ex_intro _ d (ex_intro _ t (ex_intro _ (2 ^ j) (conj Hhnd G10)))) G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
      intros R4 KEPT POST. destruct (POST d t (2 ^ j) Hhnd G10) as (p & l & Hg & RS & Hp4 & Qa0' & Qa1').
      keptQ KEPT G2 Qsp4. keptQ KEPT G8 Qs04. keptQ KEPT G3 Qgp4. keptQ KEPT G4 Qtp4. keptQ KEPT G22 Q224. keptQ KEPT G24 Q244.
      pose proof (oregs_kept w R3 R4 OR3 KEPT) as OR4.
      assert (GK4 : forall r', In r' [23; 26; 27]%bv -> getr R4 r' = getr R2 r').
      { intros r' Hr'. rewrite (KEPT r') by (revert Hr'; clear; intros Hr'; apply in_reg_list; cbn in Hr'; decompose [or] Hr'; try contradiction; subst r'; reflexivity). apply GK3. exact Hr'. }
      clear KEPT POST GK3 OR3 G1 G2 G3 G4 G8 G10 G22 G24.
      pose proof RS as RS'. destruct RS' as (Rp0 & Rp1 & _).
      pose proof (MASKLEN t (2 ^ j) l HIn Hg) as Hll. assert (Hl0 : 0 <= Zlen l) by (unfold Zlen; lia). pose proof MAXLEN as Hml.
      pose proof (go_len_operand G GOK t (2 ^ j) l Hg) as Hll2. unfold HRep.Zlength in Hll2. change (Zlen l <= g_maxlen G) in Hll2.
      pose proof OR4 as OR'. destruct OR' as (_ & _ & _ & _ & Fs1 & Fs2 & Fs3 & Fs4 & Fs5 & Fs9).

      pm_seed R4 w c' [Z_to_bv 64 p; Z_to_bv 64 (Zlen l)].
      seedHR HR E ([(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, EVar 39); (11%bv, EVar 40)] ++ OREGSEED)%list R4. seedHK HK w A M2 model c' E X2.
      xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
      postrun. name_run HRn R5.
      rreg HRn (1%bv) G1. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11.
      pose proof (syms_id_sound _ _ _ _ [22; 23; 24; 26; 27]%bv HRn eq_refl) as GK5.
      assert (OR5 : oregs w R5) by (oregs_seeded HRn Qgp4 Qtp4).
      pose proof OR5 as OR'. destruct OR' as (G2 & G3 & G4 & G8 & _). clear HRn HR HK.
      rewrite ?SymExec.alu64_add_lit in G10. rewrite ?w_add in G10 by lia. rewrite ?SymExec.alu64_add_lit in G11. rewrite ?w_add in G11 by lia.
      lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M3 := m) in * end.
      assert (ST3 : stores_in (zwin (w_sp w + 304) (w_sp w + 320)) M2 M3) by (unfold M3; stin).
      assert (X3 : PMX w A M3 model c').
      { eapply (pmx_frame_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img w A M2 M3 model c' (zwin (w_sp w + 304) (w_sp w + 320)));
          [exact X2 | exact ST3 | unfold zwin, w_sp0, PM_FRAME; intros; lia]. }
      assert (Fp : fld SEGS M3 (w_sp w + 304) 8 p) by (unfold M3; rdback).
      assert (Fl : fld SEGS M3 (w_sp w + 304 + 8) 8 (Zlen l)) by (unfold M3; replace (w_sp w + 304 + 8) with (w_sp w + 312) by lia; rdback).
      pose proof (x_ms X3) as MS3.
      assert (Hrange : Forall (fun x => 0 <= x < 2 ^ 31) l).
      { apply Forall_forall. intros x Hx. eapply (go_range G GOK l x); [right; left; exists t, (2 ^ j); exact Hg | exact Hx]. }
      assert (HLc' : Zlen (t3b (c_v3 c')) = Zlen (t3b (c_v3 c)) + Zlen L) by (rewrite EL, Zlen_app; reflexivity).
      eapply (pm_push_types w c0 K fx A M3 model c' R5 (w_sp w + 304) p _ l PS X3 Htr BUD ltac:(cregs_tac G1 G2 G3 G4) G10);
        [unfold O_V3; exact G11 | exact Fp | exact Fl | exact RS | exact Hp4 | lia | exact Hrange
        | lia | unfold w_sp0, PM_FRAME; lia | lia |].
      intros A6 R6 M6 model6 b' cap' X6 BUD6 KEPT AG.
      pose proof (oregs_kept w R5 R6 OR5 KEPT) as OR6.
      assert (GK6 : forall r', In r' [22; 23; 24; 26; 27]%bv -> getr R6 r' = getr R4 r').
      { intros r' Hr'. rewrite (KEPT r') by (revert Hr'; clear; intros Hr'; apply in_reg_list; cbn in Hr'; decompose [or] Hr'; try contradiction; subst r'; reflexivity). apply GK5. exact Hr'. }
      clear G1 G2 G3 G4 G8 G10 G11 KEPT GK5 OR5.
      destruct (push_types_facts l (t3b (c_v3 c')) (go_operand_zw G GOK t (2 ^ j) l Hg) Hrange) as (l' & El' & Hlen' & SF' & Hr').
      assert (AG26 : CRep.agree_on (fun a => w_sp w <= a < w_sp w + 864 /\ ~ zwin (w_sp w + 304) (w_sp w + 320) a) M2 M6).
      { intros a Ha. rewrite (AG a ltac:(unfold w_sp0, PM_FRAME; lia)). apply (stores_in_agree _ _ _ _ ST3 ltac:(intros b Hb; exact Hb)). unfold zwin in *. lia. }
      set (c6 := set_v3 c' (b', push_types l (t3b (c_v3 c')), cap')) in *.
      assert (OB6 : forall Rx, oregs w Rx -> OBASE w I A6 M6 model6 c6 Rx).
      { intros Rx ORx. split; [exact X6|]. split; [exact Htr|]. split; [exact BUD6|]. split; [exact ORx|].
        split; [eapply (loop_mem_frame w M2 M6); [exact LM2 | lia | lia | eapply agree_on_weaken; [exact AG26 | unfold zwin; cbn; intros; lia]]|].
        split; [eapply (ictx_agree w M2 M6); [exact IC2 | lia | lia | eapply agree_on_weaken; [exact AG26 | unfold zwin; cbn; intros; lia]]|].
        split; [eapply (ifr_agree w M2 M6); [exact FR2 | lia | lia | eapply agree_on_weaken; [exact AG26 | unfold zwin; cbn; intros; lia]]|].
        cbn [c6 set_v3 c_icount c_endian c_v3 t3b fst snd]. split; [exact Hic|]. split; [exact Hend|]. split; [exact Hwnz|].
        split; [exact MAC|]. rewrite El'. apply Forall_app. split; [exact V3R | exact Hr']. }
      assert (MC6 : mcells M6) by (eapply (mcells_agree M2 M6); [exact MC2 | lia | lia | eapply agree_on_weaken; [exact AG26 | unfold zwin; cbn; intros; lia]]).
      clear AG ST3 X3 MS3 Fp Fl. clearbody M3. clear M3. pose proof (x_ms X6) as MS6.

      pose proof OR6 as OR6'. destruct OR6' as (Qsp6 & Qgp6 & Qtp6 & Qs06 & Ys1 & Ys2 & Ys3 & Ys4 & Ys5 & Ys9).
      assert (Q246 : getr R6 24%bv = sxw (2 ^ j)) by (rewrite (GK6 24%bv) by (clear; inl); exact Q244).
      assert (Q226 : getr R6 22%bv = sxw (rem - 2 ^ j)) by (rewrite (GK6 22%bv) by (clear; inl); exact Q224).
      destruct MC6 as (C718_6 & C712_6 & C720_6).
      pm_seed R6 w c6 [sxw (2 ^ j); sxw (rem - 2 ^ j); Z_to_bv 64 word].
      seedHR HR E ([(2%bv, EVar 32); (8%bv, EVar 33); (24%bv, EVar 39); (22%bv, EVar 40)] ++ OREGSEED)%list R6.
      seedHK HK w A6 M6 model6 c6 E X6.
      apply (know_more E M6 [KWord (SA (EVar 32) 712) (N.to_nat 4) (EVar 41); KRange (EVar 41) 1 (2 ^ 32 - 1)]) in HK.
      2: { repeat apply Forall_cons; try apply Forall_nil.
           - eapply kword_var; [exact C712_6 | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
           - eapply krange_var; [evs; reflexivity | lia | lia]. }
      destruct (Z.eq_dec (rem - 2 ^ j) 0) as [Hdone | Hmore].
      -
        xruns HR HK 100%nat (0x67a1c :: 0x67aac :: STOPS) (SCR [true; true] [] []) 50%N.
        { rewrite Hdone in *. split_scs; try sc_auto1; cbn [sc_denot]; evs; rewrite ?Hand; rewrite <- ?(sxw_small' 0) by lia;
          rewrite ?ext_val_sx4, <- ?sxw_sx32 by lia; rewrite ?br_eq_sxw, ?br_ne_sxw by lia; try bool_lia. }
        postrun. name_run HRn R7.
        pose proof (syms_id_sound _ _ _ _ [23; 26; 27]%bv HRn eq_refl) as GK7.
        assert (OR7 : oregs w R7) by (oregs_seeded HRn Qgp6 Qtp6). clear HRn HR HK.
        eapply (PK A6 M6 model6 c6 R7 1 (L ++ l') (OB6 R7 OR7)).
        + rewrite (GK7 27%bv), (GK6 27%bv), (GK4 27%bv) by (clear; inl). exact Q27b.
        + rewrite (GK7 23%bv), (GK6 23%bv), (GK4 23%bv), (GK2 23%bv) by (clear; inl). exact Q23.
        + rewrite (GK7 26%bv), (GK6 26%bv), (GK4 26%bv), (GK2 26%bv) by (clear; inl). exact Q26.
        + exact C718_6.
        + left. lia.
        + cbn [c6 set_v3 c_widx]. exact Ewidx. + cbn [c6 set_v3 c_v1]. exact Ev1. + cbn [c6 set_v3 c_v2]. exact Ev2.
        + unfold PmLoopU1.nodes in *. cbn [c6 set_v3 c_m1 c_m2 c_m3]. cbn [c_m1 c_m2 c_m3] in Enodes. lia.
        + cbn [c6 set_v3 c_v3 t3b fst snd]. rewrite El', EL, <- app_assoc. reflexivity.
        + apply seed_free_app; [exact SFL | exact SF'].
        + rewrite Zlen_app. lia.
        + right. clear - HIn. unfold MASK_TYPES in HIn. cbn [In] in HIn. unfold OT_RESULT_ID, OT_LITERAL_INTEGER, OT_LITERAL_STRING. repeat split; intros ->; intuition lia.
        + cbn [c6 set_v3 c_m2]. exact Em2c.
        + left. cbn [c6 set_v3 c_m1]. exact Em1c.
        + left. cbn [c6 set_v3 c_m3]. exact Em3c.
        + intros Hin3. apply in_app_or in Hin3. destruct Hin3 as [Hin3|Hin3]; [exact (NRL Hin3) | exact (notrid_operand CL _ _ _ _ _ Hg El' Hin3)].
      -
        assert (Erem : rem - 2 ^ j = word mod 2 ^ j) by lia.
        assert (Hj1 : 1 <= j).
        { destruct (Z.eq_dec j 0) as [E0|]; [| lia]. exfalso. apply Hmore. rewrite Erem, E0. apply Z.mod_1_r. }
        assert (Hr2 : 0 <= rem - 2 ^ j < 2 ^ 31) by (pose proof (Z.mod_pos_bound word (2 ^ j) ltac:(lia)); assert (2 ^ j <= 2 ^ 31) by (apply Z.pow_le_mono_r; lia); lia).
        xruns HR HK 100%nat (0x67a1c :: 0x67aac :: STOPS) (SCR [false] [] []) 50%N.
        { scM Hand. }
        postrun. name_run HRn R7.
        rreg HRn (24%bv) G24. rreg HRn (22%bv) G22.
        pose proof (syms_id_sound _ _ _ _ [23; 26; 27]%bv HRn eq_refl) as GK7.
        assert (OR7 : oregs w R7) by (oregs_seeded HRn Qgp6 Qtp6). clear HRn HR HK.
        rewrite srliw1_mask in G24 by lia.
        destruct kk as [|kk']; [exfalso; subst j; cbn in Hj1; lia|].
        apply (IH kk' ltac:(lia) A6 M6 model6 c6 R7 (L ++ l') ltac:(lia) (OB6 R7 OR7)).
        + cbn [c6 set_v3 c_widx]. exact Ewidx. + cbn [c6 set_v3 c_v1]. exact Ev1. + cbn [c6 set_v3 c_v2]. exact Ev2.
        + unfold PmLoopU1.nodes in *. cbn [c6 set_v3 c_m1 c_m2 c_m3]. cbn [c_m1 c_m2 c_m3] in Enodes. lia.
        + cbn [c6 set_v3 c_m1]. exact Em1c. + cbn [c6 set_v3 c_m2]. exact Em2c. + cbn [c6 set_v3 c_m3]. exact Em3c.
        + cbn [c6 set_v3 c_v3 t3b fst snd]. rewrite El', EL, <- app_assoc. reflexivity.
        + apply seed_free_app; [exact SFL | exact SF'].
        + intros Hin3. apply in_app_or in Hin3. destruct Hin3 as [Hin3|Hin3]; [exact (NRL Hin3) | exact (notrid_operand CL _ _ _ _ _ Hg El' Hin3)].
        + rewrite Zlen_app. lia.
        + rewrite (GK7 27%bv), (GK6 27%bv), (GK4 27%bv) by (clear; inl). exact Q27b.
        + rewrite (GK7 23%bv), (GK6 23%bv), (GK4 23%bv), (GK2 23%bv) by (clear; inl). exact Q23.
        + rewrite (GK7 26%bv), (GK6 26%bv), (GK4 26%bv), (GK2 26%bv) by (clear; inl). exact Q26.
        + rewrite G24. f_equal. f_equal. lia.
        + rewrite G22, Erem. f_equal. f_equal. f_equal. lia.
        + replace (Z.of_nat kk' + 1) with j by lia. rewrite <- Erem. exact Hmore.
        + split; [exact C718_6 | split; [exact C712_6 | exact C720_6]].
    Qed.
  End MaskLoop.

  Lemma mask_et_range : forall t, 0 <= t < 2 ^ 31 -> 0 <= mask_et t < 2 ^ 31.
  Proof using. intros t Ht. unfold mask_et. repeat match goal with |- context [if ?x =? ?y then _ else _] => destruct (Z.eqb_spec x y) end; lia. Qed.

  Lemma lui_mask31 : Z_to_bv 64 18446744071562067968 = sxw (2 ^ Z.of_nat 31).
  Proof using. apply bv_eq. vm_compute. reflexivity. Qed.

  Theorem arm_MASK_U1 : forall t, In t MASK_TYPES -> arm_stmt t 0x678d8.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros t HIn w c0 K fx I A M model c R wv PS FZ FC IP HAE PK CK AACC. specialize (PK fx FZ FC). specialize (CK fx FZ FC).
    pose proof (AE_facts w I A M model c R t wv IP HAE) as (_ & _ & _ & V3B & _ & _).
    destruct HAE as (OB & Hw1 & Hw2 & Hn & Hv1 & Hv2 & Hlen & Ht & Hword & Q22 & Q27 & Q24 & Q23 & Q26 & PO & C712).
    pose proof OB as OB'. destruct OB' as (X & Htr & BUD & OR & LM & IC & FR & Hic & Hend & Hwnz & MAC & V3R).
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof MAXLEN as Hml.
    destruct PO as (_ & C718 & C720 & _).
    apply (mask_disp w A M model c fx R t K X OR Q27 HIn C720). intros R' M' OR' Q27' GK HM' C720'.

    assert (STd : stores_in (zwin (w_sp w + 720) (w_sp w + 724)) M M').
    { destruct HM' as [-> | ->]; [apply stores_in_refl | stin]. }
    clear HM'.
    assert (X' : PMX w A M' model c).
    { eapply (pmx_frame_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img w A M M' model c (zwin (w_sp w + 720) (w_sp w + 724)));
        [exact X | exact STd | unfold zwin, w_sp0, PM_FRAME; intros; lia]. }
    assert (AGd : CRep.agree_on (fun a => w_sp w <= a < w_sp w + 864 /\ ~ zwin (w_sp w + 720) (w_sp w + 724) a) M M').
    { eapply stores_in_agree; [exact STd | intros b Hb; unfold zwin in *; lia]. }
    assert (OB1 : forall Rx, oregs w Rx -> OBASE w I A M' model c Rx).
    { intros Rx ORx. split; [exact X'|]. split; [exact Htr|]. split; [exact BUD|]. split; [exact ORx|].
      split; [eapply (loop_mem_frame w M M'); [exact LM | lia | lia | eapply agree_on_weaken; [exact AGd | unfold zwin; cbn; intros; lia]]|].
      split; [eapply (ictx_agree w M M'); [exact IC | lia | lia | eapply agree_on_weaken; [exact AGd | unfold zwin; cbn; intros; lia]]|].
      split; [eapply (ifr_agree w M M'); [exact FR | lia | lia | eapply agree_on_weaken; [exact AGd | unfold zwin; cbn; intros; lia]]|].
      split; [exact Hic|]. split; [exact Hend|]. split; [exact Hwnz|]. split; [exact MAC | exact V3R]. }
    assert (C718' : cellw SEGS M' (w_sp w + 718) 2 1).
    { eapply (cellw_frame M M'); [exact C718 | lia | cbn; lia | eapply agree_on_weaken; [exact AGd | unfold zwin; cbn; intros; lia]]. }
    assert (C712' : cellw SEGS M' (w_sp w + 712) 4 wv).
    { eapply (cellw_frame M M'); [exact C712 | lia | cbn; lia | eapply agree_on_weaken; [exact AGd | unfold zwin; cbn; intros; lia]]. }
    pose proof (x_ms X') as MS'. clear STd AGd X LM IC FR C718 C712 C720.
    pose proof OR' as OR''. destruct OR'' as (Qsp & Qgp & Qtp & Qs0 & Qs1 & Qs2 & Qs3 & Qs4 & Qs5 & Qs9).
    assert (Q22' : getr R' 22%bv = sxw wv) by (rewrite (GK 22%bv) by (clear; inl); rewrite Q22; symmetry; apply sxw_sx32; lia).
    assert (Q23' : getr R' 23%bv = Z_to_bv 64 (i_io I)) by (rewrite (GK 23%bv) by (clear; inl); exact Q23).
    assert (Q26' : getr R' 26%bv = Z_to_bv 64 (i_op I)) by (rewrite (GK 26%bv) by (clear; inl); exact Q26).
    destruct (Z.eq_dec wv 0) as [Hw0 | Hwnz0].
    -
      assert (Q22z : getr R' 22%bv = Z_to_bv 64 0) by (rewrite Q22', Hw0; apply (sxw_small' 0); lia).
      pm_seed R' w c (@nil word).
      seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (22%bv, ELit 0)] R'. seedHK HK w A M' model c E X'.
      xruns HR HK 100%nat (0x67a7c :: STOPS) (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
      postrun. name_run HRn R1.
      rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8.
      pose proof (syms_id_sound _ _ _ _ PmInstU1.SREGS HRn eq_refl) as GS.
      pose proof (syms_id_sound _ _ _ _ [23; 26; 27]%bv HRn eq_refl) as GK1.
      clear HRn HR HK. fixregs.
      assert (OR1 : oregs w R1) by (eapply (PmInstU1.loop_regs_glue w R' R1); [exact OR' | exact GS | exact G2 | exact G3 | exact G4 | exact G8]).
      eapply (mask_w0 w c0 K fx I A M' model c R1 t PS (OB1 R1 OR1)).
      + rewrite (GK1 27%bv) by (clear; inl). exact Q27'.
      + rewrite (GK1 23%bv) by (clear; inl). exact Q23'.
      + rewrite (GK1 26%bv) by (clear; inl). exact Q26'.
      + exact Ht.
      + exact C718'.
      + lia.
      + lia.
      + exact PK.
      + exact HIn.
    -
      pm_seed R' w c [sxw wv].
      seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (22%bv, EVar 39)] R'. seedHK HK w A M' model c E X'.
      xruns HR HK 100%nat (0x67a1c :: STOPS) (SCR [false] [] []) 50%N.
      { split_scs; try sc_auto1; cbn [sc_denot]; evs; rewrite <- ?(sxw_small' 0) by lia; rewrite br_eq_sxw by lia; bool_lia. }
      postrun. name_run HRn R1.
      rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (22%bv) G22. rreg HRn (24%bv) G24.
      pose proof (syms_id_sound _ _ _ _ PmInstU1.SREGS HRn eq_refl) as GS.
      pose proof (syms_id_sound _ _ _ _ [23; 26; 27]%bv HRn eq_refl) as GK1.
      clear HRn HR HK. fixregs.
      assert (OR1 : oregs w R1) by (eapply (PmInstU1.loop_regs_glue w R' R1); [exact OR' | exact GS | exact G2 | exact G3 | exact G4 | exact G8]).
      eapply (mask_loop w c0 K fx I c t wv PS HIn Ht ltac:(lia) V3B PK
                (mask_diag w c0 K fx wv (mask_et t) PS FZ CK ltac:(lia) (mask_et_range t Ht))
                31%nat A M' model c R1 [] ltac:(cbn; lia) (OB1 R1 OR1) eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl).
      + rewrite app_nil_r. reflexivity.
      + exact PmZw.seed_free_nil.
      + intros [].
      + rewrite PmZw.Zlen_nil. cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.sub Z.mul Z.pos_sub Z.add Z.opp Z.succ_double Z.pred_double Z.double]. lia.
      + rewrite (GK1 27%bv) by (clear; inl). exact Q27'.
      + rewrite (GK1 23%bv) by (clear; inl). exact Q23'.
      + rewrite (GK1 26%bv) by (clear; inl). exact Q26'.
      + rewrite G24. apply lui_mask31.
      + rewrite G22. change (Z.of_nat 31 + 1) with 32. rewrite Z.mod_small by lia. reflexivity.
      + change (Z.of_nat 31 + 1) with 32. rewrite Z.mod_small by lia. exact Hwnz0.
      + split; [exact C718' | split; [exact C712' | exact C720']].
  Qed.
End PM.
