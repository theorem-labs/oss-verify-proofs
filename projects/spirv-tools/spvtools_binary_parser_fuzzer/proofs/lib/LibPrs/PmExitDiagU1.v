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
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts HStmtsU1 HCommonU1 HLib HFpu HConstsU1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsNeeds PrsInv PrsStmts PmBaseU1 PmHyps PmHypsU1 PmCoreU1 PmStepU1. Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep2U1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep2U1.PmUpdU1. From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PmStep2U1 PmStep3U1 PmLoopU1 PmInstU1 PmODefsU1 PmBody1U1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PeLia.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Local Ltac lia ::= pe_lia.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Abbreviation SEGS := Ubsan.M.loaded_segments.
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
  #[local] Notation IDP := (cu_idesc_ptr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  #[local] Notation pm_put_cstr := (PmStepU1.pm_put_cstr CL).
  #[local] Notation pm_put_u16 := (PmStepU1.pm_put_u16 CL).
  #[local] Notation pm_put_u64 := (PmStepU1.pm_put_u64 CL).
  #[local] Notation pm_pdiagQ := (PmStepU1.pm_pdiagQ CL).
  #[local] Notation pm_dtor := (PmStepU1.pm_dtor CL).
  #[local] Notation pm_tail_676a4 := (PmBody1U1.pm_tail_676a4 CL).
  #[local] Notation loop_mem := (PmStepU1.loop_mem (MI:=MI) (ST:=ST)).
  #[local] Notation loop_regs := (PmStepU1.loop_regs (MI:=MI) (ST:=ST)).
  #[local] Notation izero := (PmInstU1.izero).
  #[local] Notation ictx := (PmInstU1.ictx).
  #[local] Notation ipure := (PmODefsU1.ipure (G:=G) (idesc:=idesc)).
  #[local] Notation OLI := (PmODefsU1.OLI (MI:=MI) (ST:=ST) (generates_type:=generates_type)).
  #[local] Notation oregs := (PmODefsU1.oregs (MI:=MI) (ST:=ST)).
  Definition pm_idesc_name := pm_leafA (MI:=MI) (ST:=ST) _ _ _ (cu_idesc_name _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  Definition pm_strlen := pm_leafA (MI:=MI) (ST:=ST) _ _ _ (cu_strlen _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  #[local] Notation ext_val_zx2 := PmInstU1.ext_val_zx2.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  Lemma low32_val : forall a, bv_unsigned (low32 (Z_to_bv 64 a)) = a mod 2 ^ 32.
  Proof using.
    intros a. unfold low32. rewrite bv_extract_unsigned, Z_to_bv_unsigned, bv_wrap64_mod, Z.shiftr_0_r.
    unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32). nia.
  Qed.

  Lemma aluw_sub_val : forall a b,
    sext 64 (alu32 ALU_SUB (low32 (Z_to_bv 64 a)) (low32 (Z_to_bv 64 b))) = Z_to_bv 64 (PrsGrammar.sx32 ((a - b) mod 2 ^ 32)).
  Proof using.
    intros a b. apply bv_eq. unfold sext. rewrite bv_sign_extend_unsigned. cbn [alu32 alu]. unfold bv_signed.
    rewrite bv_sub_unsigned, !low32_val, Z_to_bv_unsigned, bv_wrap64_mod.
    unfold bv_swrap, bv_half_modulus, bv_wrap. change (bv_modulus 32) with (2 ^ 32). change (bv_modulus 64) with (2 ^ 64).
    rewrite <- Zminus_mod. unfold PrsGrammar.sx32.
    set (v := (a - b) mod 2 ^ 32). assert (Hv : 0 <= v < 2 ^ 32) by (subst v; apply Z.mod_pos_bound; lia).
    destruct (Z.ltb_spec v (2 ^ 31)); nia.
  Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Lemma sx32_nonneg : forall u, 0 <= u -> 0 <= PrsGrammar.sx32 u.
  Proof using. intros u Hu. unfold PrsGrammar.sx32. destruct (Z.ltb_spec u (2 ^ 31)); lia. Qed.
  Lemma sx32_trunc16 : forall z, (PrsGrammar.sx32 (z mod 2 ^ 32)) mod 2 ^ 16 = z mod 2 ^ 16.
  Proof using.
    intros z. unfold PrsGrammar.sx32.
    pose proof (Z.mod_pos_bound z (2 ^ 32) ltac:(lia)) as Hu. set (u := z mod 2 ^ 32) in *.
    assert (Hz : u mod 2 ^ 16 = z mod 2 ^ 16).
    { subst u. apply Z.mod_mod_divide. exists (2 ^ 16). reflexivity. }
    rewrite <- Hz. destruct (Z.ltb_spec u (2 ^ 31)); [reflexivity|].
    replace (u + 2 ^ 64 - 2 ^ 32) with (u + (2 ^ 48 - 2 ^ 16) * 2 ^ 16) by lia. rewrite Z.mod_add by lia. reflexivity.
  Qed.
  Lemma w_mul_lit : forall a b, mul_div M_MUL (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a * b).
  Proof using. intros. apply PmBody1U1.zbv_mul. Qed.
  Lemma w_zx16 : forall v, 0 <= v ->
    alu64 ALU_SRL (mul_div M_MUL (Z_to_bv 64 281474976710656) (Z_to_bv 64 v)) (Z_to_bv 64 48) = Z_to_bv 64 (v mod 2 ^ 16).
  Proof using.
    intros v Hv. pose proof (Z.mod_pos_bound v (2 ^ 16) ltac:(lia)) as Hm.
    rewrite w_mul_lit. apply bv_eq. rewrite u_srl64. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
    rewrite (Z.mod_small 48) by lia. change (48 mod 64) with 48. rewrite (Z.mod_small (v mod 2 ^ 16)) by lia.
    change 281474976710656 with (2 ^ 48). rewrite (Z.mul_comm (2 ^ 48) v). change (2 ^ 64) with (2 ^ 16 * 2 ^ 48).
    rewrite Z.mul_mod_distr_r by lia. rewrite Z.div_mul by lia. reflexivity.
  Qed.

#[local] Definition HTitDiagU1_0 : list (reg * expr) := [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, EVar 39); (22%bv, EVar 40)].
  Lemma pm_D8 : forall (w : pmw MI ST) c0 K (fx : FPState) (I : ictxR) A M model c R,
    PMS w c0 K -> frm_zero (@fp_csr fx) -> ipure I -> OLI w I A M model c R ->
    srealizes SEGS (cfg fx R 0x68770 M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx I A M model c R PS FZ IP HOLI.
    destruct HOLI as (OB & Hw1 & _). destruct OB as (X & Htr & BUD & OR & LM & IC & IFR & Hic & He2 & Hw & _).
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (x_scal X) as (Sc1 & Sc2 & Sc3 & Sc4). pose proof (ipure_ranges I IP) as (Riwc & Rop).
    pose proof IP as IP'. destruct IP' as (_ & _ & _ & _ & Hg & Hdesc & Rio).
    destruct (IDP (i_d I) (i_op I) Hdesc) as (Hd0 & Hd1 & Hd4).
    destruct OR as (Qsp & Qgp & Qtp & Qs0 & Qs1 & Qs2 & Qs3 & Qs4 & Qs5 & Qs9).
    destruct IC as (Cio & Cfw & Ciwc & Cop & Fd). pose proof (proj1 Cio) as Rio64. pose proof (proj1 Ciwc) as Riwc16. cbn in Rio64, Riwc16.
    pose proof (fld_cellw M _ 8 _ Fd ltac:(lia)) as Fdm.
    pose proof (fld_cellw M _ 8 _ (x_widx X) ltac:(lia)) as Cwi. unfold O_WIDX in Cwi.
    clear Cwi.
    pm_seed R w c (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R. seedHK HK w A M model c E X.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R1.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite ?w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_pdiagQ w c0 K fx A M model c R1 (-4) _ []);
      [exact PS | exact X | exact Htr | exact BUD | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | rewrite G12; apply bv_eq; vm_compute; reflexivity | lia |].
    clear Qsp Qs0 Qgp Qtp. intros A1 R1c M1 model1 B1 X1 BUD1 KEPT DS1 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    eapply (cellw_frame _ M1) in Cio; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M1) in Ciwc; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M1) in Fdm; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (loop_mem_frame w _ M1) in LM; [| lia | lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G22; try clear G23.
    try clear X0 BUD0 MS0. pose proof (x_ms X1) as MS1.
    pm_seed R1c w (set_tr c (B1 ++ [])) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R1c. seedHK HK w A1 M1 model1 (set_tr c (B1 ++ [])) E X1.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R2.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite ?w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_put_cstr w c0 K fx A1 M1 model1 (set_tr c (B1 ++ [])) R2 (-4) _ 0x11738 38 38 _ B1 []);
      [exact PS | exact X1 | reflexivity | exact BUD1 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS1 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | apply ro_cstr_of_chk; vm_compute; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A2 R2c M2 model2 B2 X2 BUD2 KEPT _ DS2 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    eapply (cellw_frame _ M2) in Cio; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M2) in Ciwc; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M2) in Fdm; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (loop_mem_frame w _ M2) in LM; [| lia | lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G22; try clear G23.
    try clear X1 BUD1 DS1 MS1. pose proof (x_ms X2) as MS2.
    pm_seed R2c w (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) [Z_to_bv 64 (i_d I)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R2c. seedHK HK w A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) E X2.
    apply (know_more E M2 [KWord (SA (EVar 32) 224) (N.to_nat 8) (EVar 39); KRange (EVar 39) 0x10000 (2 ^ 40); KAlign (EVar 39) 4]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         - eapply kword_var; [exact Fdm | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply krange_var; [evs; reflexivity | lia | lia].
         - eapply kalign_var; [evs; reflexivity | lia | lia | exact Hd4]. }
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R3.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_idesc_name w A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) fx R3 _ K X2 (ex_intro _ (i_d I) (ex_intro _ (i_op I) (conj Hdesc G10))) G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
    clear Qsp Qs0 Qgp Qtp. intros R3n KEPT (pnm & nnm & ROnm & Hn256 & Gnm).
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    clear G1 G2 G3 G4 G8 KEPT; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G22; try clear G23.
    pose proof ROnm as RO'. destruct RO' as (Rp1 & Rn0 & Rp2 & _).
    pm_seed R3n w (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) [Z_to_bv 64 pnm].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, EVar 39)] R3n. seedHK HK w A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) E X2.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R4.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (22%bv) G22.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    try replace (Z_to_bv 5 (Z.of_N 22)) with (22%bv : reg) in * by (apply bv_eq; reflexivity). rename G22 into Q22p.
    eapply (pm_strlen w A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) fx R4 _ K X2 (ex_intro _ pnm (ex_intro _ nnm (conj ROnm G10))) G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
    clear Qsp Qs0 Qgp Qtp. intros R4s KEPT POst. pose proof (POst pnm nnm ROnm G10) as Gsl. clear POst.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp. keptQ KEPT Q22p Q22p_. clear Q22p. rename Q22p_ into Q22p.
    clear G1 G2 G3 G4 G8 KEPT; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G22; try clear G23.
    pm_seed R4s w (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) [Z_to_bv 64 nnm; Z_to_bv 64 pnm].
    seedHR HR E HTitDiagU1_0 R4s. seedHK HK w A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) E X2.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R5.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite ?w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    clear Q22p.
    eapply (pm_put_cstr w c0 K fx A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) R5 (-4) _ pnm nnm nnm _ B2 []);
      [exact PS | exact X2 | reflexivity | exact BUD2 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS2 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | exact ROnm | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A5 R5c M5 model5 B5 X5 BUD5 KEPT _ DS5 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    eapply (cellw_frame _ M5) in Cio; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M5) in Ciwc; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M5) in Fdm; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (loop_mem_frame w _ M5) in LM; [| lia | lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G22; try clear G23.
    try clear X4 BUD4 DS4 MS4. pose proof (x_ms X5) as MS5.
    pm_seed R5c w (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R5c. seedHK HK w A5 M5 model5 (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) E X5.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R6.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite ?w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_put_cstr w c0 K fx A5 M5 model5 (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) R6 (-4) _ 0x11599 18 18 _ B5 []);
      [exact PS | exact X5 | reflexivity | exact BUD5 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS5 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | apply ro_cstr_of_chk; vm_compute; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A6 R6c M6 model6 B6 X6 BUD6 KEPT _ DS6 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    eapply (cellw_frame _ M6) in Cio; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M6) in Ciwc; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M6) in Fdm; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (loop_mem_frame w _ M6) in LM; [| lia | lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G22; try clear G23.
    try clear X5 BUD5 DS5 MS5. pose proof (x_ms X6) as MS6.
    pm_seed R6c w (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) [Z_to_bv 64 (i_io I)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R6c. seedHK HK w A6 M6 model6 (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) E X6.
    apply (know_more E M6 [KWord (SA (EVar 32) 216) (N.to_nat 8) (EVar 39)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         - eapply kword_var; [exact Cio | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity]. }
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R7.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite ?w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_put_u64 w c0 K fx A6 M6 model6 (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) R7 (-4) _ (i_io I) _ B6 []);
      [exact PS | exact X6 | reflexivity | exact BUD6 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS6 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A7 R7c M7 model7 B7 X7 BUD7 KEPT _ DS7 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    eapply (cellw_frame _ M7) in Cio; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M7) in Ciwc; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M7) in Fdm; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (loop_mem_frame w _ M7) in LM; [| lia | lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G22; try clear G23.
    try clear X6 BUD6 DS6 MS6. pose proof (x_ms X7) as MS7.
    pm_seed R7c w (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R7c. seedHK HK w A7 M7 model7 (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) E X7.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R8.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite ?w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_put_cstr w c0 K fx A7 M7 model7 (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) R8 (-4) _ 0x10298 31 31 _ B7 []);
      [exact PS | exact X7 | reflexivity | exact BUD7 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS7 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | apply ro_cstr_of_chk; vm_compute; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A8 R8c M8 model8 B8 X8 BUD8 KEPT _ DS8 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    eapply (cellw_frame _ M8) in Cio; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M8) in Ciwc; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M8) in Fdm; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (loop_mem_frame w _ M8) in LM; [| lia | lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G22; try clear G23.
    try clear X7 BUD7 DS7 MS7. pose proof (x_ms X8) as MS8.
    pm_seed R8c w (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) [Z_to_bv 64 (i_iwc I)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R8c. seedHK HK w A8 M8 model8 (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) E X8.
    apply (know_more E M8 [KWord (SA (EVar 32) 234) (N.to_nat 2) (EVar 39)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         - eapply kword_var; [exact Ciwc | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity]. }
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R9.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite ?w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_put_u16 w c0 K fx A8 M8 model8 (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) R9 (-4) _ (i_iwc I) _ B8 []);
      [exact PS | exact X8 | reflexivity | exact BUD8 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS8 | cregs_tac G1 G2 G3 G4
      | exact G10 | rewrite G11; rewrite ext_val_zx2 by lia; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A9 R9c M9 model9 B9 X9 BUD9 KEPT _ DS9 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    eapply (cellw_frame _ M9) in Cio; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M9) in Ciwc; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M9) in Fdm; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (loop_mem_frame w _ M9) in LM; [| lia | lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G22; try clear G23.
    try clear X8 BUD8 DS8 MS8. pose proof (x_ms X9) as MS9.
    pm_seed R9c w (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) (B9 ++ [])) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R9c. seedHK HK w A9 M9 model9 (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) (B9 ++ [])) E X9.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R10.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite ?w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_put_cstr w c0 K fx A9 M9 model9 (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) (B9 ++ [])) R10 (-4) _ 0x13aeb 7 7 _ B9 []);
      [exact PS | exact X9 | reflexivity | exact BUD9 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS9 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | apply ro_cstr_of_chk; vm_compute; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A10 R10c M10 model10 B10 X10 BUD10 KEPT _ DS10 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    eapply (cellw_frame _ M10) in Cio; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M10) in Ciwc; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M10) in Fdm; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (loop_mem_frame w _ M10) in LM; [| lia | lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G22; try clear G23.
    try clear X9 BUD9 DS9 MS9. pose proof (x_ms X10) as MS10.
    pm_seed R10c w (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) (B9 ++ [])) (B10 ++ [])) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R10c. seedHK HK w A10 M10 model10 (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) (B9 ++ [])) (B10 ++ [])) E X10.
    xruns HR HK 100%nat (0x67748 :: STOPS) (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn Rt. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_tail_676a4 w c0 K fx A10 M10 model10 _ Rt (-4) _ B10);
      [exact PS | exact X10 | cbn [c_tr set_tr]; rewrite ?app_nil_r; reflexivity | exact BUD10 | exact DS10 | lia | exact FZ
      | exact G2 | exact G3 | exact G4].
  Qed.

  Lemma pm_D9 : forall (w : pmw MI ST) c0 K (fx : FPState) (I : ictxR) A M model c R,
    PMS w c0 K -> frm_zero (@fp_csr fx) -> ipure I -> OLI w I A M model c R ->
    srealizes SEGS (cfg fx R 0x686a0 M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx I A M model c R PS FZ IP HOLI.
    destruct HOLI as (OB & Hw1 & _). destruct OB as (X & Htr & BUD & OR & LM & IC & IFR & Hic & He2 & Hw & _).
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (x_scal X) as (Sc1 & Sc2 & Sc3 & Sc4). pose proof (ipure_ranges I IP) as (Riwc & Rop).
    pose proof IP as IP'. destruct IP' as (_ & _ & _ & _ & Hg & Hdesc & Rio).
    destruct (IDP (i_d I) (i_op I) Hdesc) as (Hd0 & Hd1 & Hd4).
    destruct OR as (Qsp & Qgp & Qtp & Qs0 & Qs1 & Qs2 & Qs3 & Qs4 & Qs5 & Qs9).
    destruct IC as (Cio & Cfw & Ciwc & Cop & Fd). pose proof (proj1 Cio) as Rio64. pose proof (proj1 Ciwc) as Riwc16. cbn in Rio64, Riwc16.
    pose proof (fld_cellw M _ 8 _ Fd ltac:(lia)) as Fdm.
    pm_seed R w c (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R. seedHK HK w A M model c E X.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R1.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite ?w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_pdiagQ w c0 K fx A M model c R1 (-4) _ []);
      [exact PS | exact X | exact Htr | exact BUD | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | rewrite G12; apply bv_eq; vm_compute; reflexivity | lia |].
    clear Qsp Qs0 Qgp Qtp. intros A1 R1c M1 model1 B1 X1 BUD1 KEPT DS1 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    eapply (cellw_frame _ M1) in Cio; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M1) in Ciwc; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M1) in Fdm; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (loop_mem_frame w _ M1) in LM; [| lia | lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G22; try clear G23.
    try clear X0 BUD0 MS0. pose proof (x_ms X1) as MS1.
    pm_seed R1c w (set_tr c (B1 ++ [])) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R1c. seedHK HK w A1 M1 model1 (set_tr c (B1 ++ [])) E X1.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R2.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite ?w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_put_cstr w c0 K fx A1 M1 model1 (set_tr c (B1 ++ [])) R2 (-4) _ 0x12b18 22 22 _ B1 []);
      [exact PS | exact X1 | reflexivity | exact BUD1 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS1 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | apply ro_cstr_of_chk; vm_compute; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A2 R2c M2 model2 B2 X2 BUD2 KEPT _ DS2 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    eapply (cellw_frame _ M2) in Cio; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M2) in Ciwc; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M2) in Fdm; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (loop_mem_frame w _ M2) in LM; [| lia | lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G22; try clear G23.
    try clear X1 BUD1 DS1 MS1. pose proof (x_ms X2) as MS2.
    pm_seed R2c w (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) [Z_to_bv 64 (i_d I)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R2c. seedHK HK w A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) E X2.
    apply (know_more E M2 [KWord (SA (EVar 32) 224) (N.to_nat 8) (EVar 39); KRange (EVar 39) 0x10000 (2 ^ 40); KAlign (EVar 39) 4]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         - eapply kword_var; [exact Fdm | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply krange_var; [evs; reflexivity | lia | lia].
         - eapply kalign_var; [evs; reflexivity | lia | lia | exact Hd4]. }
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R3.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_idesc_name w A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) fx R3 _ K X2 (ex_intro _ (i_d I) (ex_intro _ (i_op I) (conj Hdesc G10))) G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
    clear Qsp Qs0 Qgp Qtp. intros R3n KEPT (pnm & nnm & ROnm & Hn256 & Gnm).
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    clear G1 G2 G3 G4 G8 KEPT; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G22; try clear G23.
    pose proof ROnm as RO'. destruct RO' as (Rp1 & Rn0 & Rp2 & _).
    pm_seed R3n w (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) [Z_to_bv 64 pnm].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, EVar 39)] R3n. seedHK HK w A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) E X2.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R4.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (22%bv) G22.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    try replace (Z_to_bv 5 (Z.of_N 22)) with (22%bv : reg) in * by (apply bv_eq; reflexivity). rename G22 into Q22p.
    eapply (pm_strlen w A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) fx R4 _ K X2 (ex_intro _ pnm (ex_intro _ nnm (conj ROnm G10))) G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
    clear Qsp Qs0 Qgp Qtp. intros R4s KEPT POst. pose proof (POst pnm nnm ROnm G10) as Gsl. clear POst.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp. keptQ KEPT Q22p Q22p_. clear Q22p. rename Q22p_ into Q22p.
    clear G1 G2 G3 G4 G8 KEPT; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G22; try clear G23.
    pm_seed R4s w (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) [Z_to_bv 64 nnm; Z_to_bv 64 pnm].
    seedHR HR E HTitDiagU1_0 R4s. seedHK HK w A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) E X2.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R5.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite ?w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    clear Q22p.
    eapply (pm_put_cstr w c0 K fx A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) R5 (-4) _ pnm nnm nnm _ B2 []);
      [exact PS | exact X2 | reflexivity | exact BUD2 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS2 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | exact ROnm | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A5 R5c M5 model5 B5 X5 BUD5 KEPT _ DS5 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    eapply (cellw_frame _ M5) in Cio; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M5) in Ciwc; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M5) in Fdm; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (loop_mem_frame w _ M5) in LM; [| lia | lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G22; try clear G23.
    try clear X4 BUD4 DS4 MS4. pose proof (x_ms X5) as MS5.
    pm_seed R5c w (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R5c. seedHK HK w A5 M5 model5 (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) E X5.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R6.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite ?w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_put_cstr w c0 K fx A5 M5 model5 (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) R6 (-4) _ 0x11599 18 18 _ B5 []);
      [exact PS | exact X5 | reflexivity | exact BUD5 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS5 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | apply ro_cstr_of_chk; vm_compute; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A6 R6c M6 model6 B6 X6 BUD6 KEPT _ DS6 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    eapply (cellw_frame _ M6) in Cio; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M6) in Ciwc; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M6) in Fdm; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (loop_mem_frame w _ M6) in LM; [| lia | lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G22; try clear G23.
    try clear X5 BUD5 DS5 MS5. pose proof (x_ms X6) as MS6.
    pm_seed R6c w (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) [Z_to_bv 64 (i_io I)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R6c. seedHK HK w A6 M6 model6 (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) E X6.
    apply (know_more E M6 [KWord (SA (EVar 32) 216) (N.to_nat 8) (EVar 39)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         - eapply kword_var; [exact Cio | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity]. }
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R7.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite ?w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_put_u64 w c0 K fx A6 M6 model6 (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) R7 (-4) _ (i_io I) _ B6 []);
      [exact PS | exact X6 | reflexivity | exact BUD6 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS6 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A7 R7c M7 model7 B7 X7 BUD7 KEPT _ DS7 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    eapply (cellw_frame _ M7) in Cio; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M7) in Ciwc; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M7) in Fdm; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (loop_mem_frame w _ M7) in LM; [| lia | lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G22; try clear G23.
    try clear X6 BUD6 DS6 MS6. pose proof (x_ms X7) as MS7.
    pm_seed R7c w (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R7c. seedHK HK w A7 M7 model7 (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) E X7.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R8.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite ?w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_put_cstr w c0 K fx A7 M7 model7 (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) R8 (-4) _ 0x131bc 13 13 _ B7 []);
      [exact PS | exact X7 | reflexivity | exact BUD7 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS7 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | apply ro_cstr_of_chk; vm_compute; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A8 R8c M8 model8 B8 X8 BUD8 KEPT _ DS8 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    eapply (cellw_frame _ M8) in Cio; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M8) in Ciwc; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M8) in Fdm; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (loop_mem_frame w _ M8) in LM; [| lia | lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G22; try clear G23.
    try clear X7 BUD7 DS7 MS7. pose proof (x_ms X8) as MS8.
    pm_seed R8c w (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) [Z_to_bv 64 (i_iwc I)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R8c. seedHK HK w A8 M8 model8 (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) E X8.
    apply (know_more E M8 [KWord (SA (EVar 32) 234) (N.to_nat 2) (EVar 39)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         - eapply kword_var; [exact Ciwc | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity]. }
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R9.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite ?w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_put_u16 w c0 K fx A8 M8 model8 (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) R9 (-4) _ (i_iwc I) _ B8 []);
      [exact PS | exact X8 | reflexivity | exact BUD8 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS8 | cregs_tac G1 G2 G3 G4
      | exact G10 | rewrite G11; rewrite ext_val_zx2 by lia; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A9 R9c M9 model9 B9 X9 BUD9 KEPT _ DS9 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    eapply (cellw_frame _ M9) in Cio; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M9) in Ciwc; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M9) in Fdm; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (loop_mem_frame w _ M9) in LM; [| lia | lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G22; try clear G23.
    try clear X8 BUD8 DS8 MS8. pose proof (x_ms X9) as MS9.
    pm_seed R9c w (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) (B9 ++ [])) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R9c. seedHK HK w A9 M9 model9 (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) (B9 ++ [])) E X9.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R10.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite ?w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_put_cstr w c0 K fx A9 M9 model9 (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) (B9 ++ [])) R10 (-4) _ 0x109a3 18 18 _ B9 []);
      [exact PS | exact X9 | reflexivity | exact BUD9 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS9 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | apply ro_cstr_of_chk; vm_compute; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A10 R10c M10 model10 B10 X10 BUD10 KEPT _ DS10 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    eapply (cellw_frame _ M10) in Cio; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M10) in Ciwc; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M10) in Fdm; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (loop_mem_frame w _ M10) in LM; [| lia | lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G22; try clear G23.
    try clear X9 BUD9 DS9 MS9. pose proof (x_ms X10) as MS10.
    pm_seed R10c w (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) (B9 ++ [])) (B10 ++ [])) [Z_to_bv 64 (i_io I)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R10c. seedHK HK w A10 M10 model10 (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) (B9 ++ [])) (B10 ++ [])) E X10.
    apply (know_more E M10 [KWord (SA (EVar 32) 216) (N.to_nat 8) (EVar 39)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         - eapply kword_var; [exact Cio | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity]. }
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R11.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite ?w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    rewrite ?PmBody1U1.zbv_mul, ?PmBody1U1.zbv_add, ?SymExec.alu64_add_lit in G11.
    eapply (pm_put_u64 w c0 K fx A10 M10 model10 (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) (B9 ++ [])) (B10 ++ [])) R11 (-4) _ (c_widx c - i_io I) _ B10 []);
      [exact PS | exact X10 | reflexivity | exact BUD10 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS10 | cregs_tac G1 G2 G3 G4
      | exact G10 | rewrite G11; f_equal; lia | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A11 R11c M11 model11 B11 X11 BUD11 KEPT _ DS11 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    eapply (cellw_frame _ M11) in Cio; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M11) in Ciwc; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M11) in Fdm; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (loop_mem_frame w _ M11) in LM; [| lia | lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G22; try clear G23.
    try clear X10 BUD10 DS10 MS10. pose proof (x_ms X11) as MS11.
    pm_seed R11c w (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) (B9 ++ [])) (B10 ++ [])) (B11 ++ [])) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R11c. seedHK HK w A11 M11 model11 (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) (B9 ++ [])) (B10 ++ [])) (B11 ++ [])) E X11.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R12.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite ?w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_put_cstr w c0 K fx A11 M11 model11 (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) (B9 ++ [])) (B10 ++ [])) (B11 ++ [])) R12 (-4) _ 0x13974 15 15 _ B11 []);
      [exact PS | exact X11 | reflexivity | exact BUD11 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS11 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | apply ro_cstr_of_chk; vm_compute; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A12 R12c M12 model12 B12 X12 BUD12 KEPT _ DS12 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    eapply (cellw_frame _ M12) in Cio; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M12) in Ciwc; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M12) in Fdm; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (loop_mem_frame w _ M12) in LM; [| lia | lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G22; try clear G23.
    try clear X11 BUD11 DS11 MS11. pose proof (x_ms X12) as MS12.
    pm_seed R12c w (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) (B9 ++ [])) (B10 ++ [])) (B11 ++ [])) (B12 ++ [])) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R12c. seedHK HK w A12 M12 model12 (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) (B9 ++ [])) (B10 ++ [])) (B11 ++ [])) (B12 ++ [])) E X12.
    xruns HR HK 100%nat (0x67748 :: STOPS) (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn Rt. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_tail_676a4 w c0 K fx A12 M12 model12 _ Rt (-4) _ B12);
      [exact PS | exact X12 | cbn [c_tr set_tr]; rewrite ?app_nil_r; reflexivity | exact BUD12 | exact DS12 | lia | exact FZ
      | exact G2 | exact G3 | exact G4].
  Qed.

#[local] Definition HTitDiagU1_1 : list (reg * expr) := [(2%bv, EVar 32); (8%bv, EVar 33); (22%bv, EVar 38); (23%bv, EVar 39)].
  Lemma pm_D7 : forall (w : pmw MI ST) c0 K (fx : FPState) (I : ictxR) A M model c R,
    PMS w c0 K -> frm_zero (@fp_csr fx) -> ipure I -> OLI w I A M model c R ->
    c_widx c < i_io I + i_iwc I -> t3b (c_v3 c) = [] ->
    getr R 22%bv = Z_to_bv 64 (c_widx c) -> getr R 23%bv = Z_to_bv 64 (i_io I) -> getr R 10%bv = Z_to_bv 64 (i_iwc I) ->
    srealizes SEGS (cfg fx R 0x685b4 M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx I A M model c R PS FZ IP HOLI Hlt Hnil Q22 Q23 Qa0.
    destruct HOLI as (OB & Hw1 & _). destruct OB as (X & Htr & BUD & OR & LM & IC & IFR & Hic & He2 & Hw & _).
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (x_scal X) as (Sc1 & Sc2 & Sc3 & Sc4). pose proof (ipure_ranges I IP) as (Riwc & Rop).
    pose proof IP as IP'. destruct IP' as (_ & _ & _ & _ & Hg & Hdesc & Rio).
    destruct (IDP (i_d I) (i_op I) Hdesc) as (Hd0 & Hd1 & Hd4).
    destruct OR as (Qsp & Qgp & Qtp & Qs0 & Qs1 & Qs2 & Qs3 & Qs4 & Qs5 & Qs9).
    destruct IC as (Cio & Cfw & Ciwc & Cop & Fd). pose proof (proj1 Cio) as Rio64. pose proof (proj1 Ciwc) as Riwc16. cbn in Rio64, Riwc16.
    pose proof (fld_cellw M _ 8 _ Fd ltac:(lia)) as Fdm.
    clear Qa0.
    pm_seed R w c [Z_to_bv 64 (i_io I)].
    seedHR HR E HTitDiagU1_1 R. seedHK HK w A M model c E X.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R1.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12. rreg HRn (22%bv) G22. rreg HRn (23%bv) G23.
    rewrite ?w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    try replace (Z_to_bv 5 (Z.of_N 22)) with (22%bv : reg) in * by (apply bv_eq; reflexivity). rewrite ?Q22 in *. clear Q22. rename G22 into Q22.
    try replace (Z_to_bv 5 (Z.of_N 23)) with (23%bv : reg) in * by (apply bv_eq; reflexivity). rewrite ?Q23 in *. clear Q23. rename G23 into Q23.
    eapply (pm_pdiagQ w c0 K fx A M model c R1 (-4) _ []);
      [exact PS | exact X | exact Htr | exact BUD | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | rewrite G12; apply bv_eq; vm_compute; reflexivity | lia |].
    clear Qsp Qs0 Qgp Qtp. intros A1 R1c M1 model1 B1 X1 BUD1 KEPT DS1 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp. keptQ KEPT Q22 Q22_. clear Q22. rename Q22_ into Q22. keptQ KEPT Q23 Q23_. clear Q23. rename Q23_ into Q23.
    eapply (cellw_frame _ M1) in Cio; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M1) in Ciwc; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M1) in Fdm; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (loop_mem_frame w _ M1) in LM; [| lia | lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G22; try clear G23.
    try clear X0 BUD0 MS0. pose proof (x_ms X1) as MS1.
    pm_seed R1c w (set_tr c (B1 ++ [])) [Z_to_bv 64 (i_io I)].
    seedHR HR E HTitDiagU1_1 R1c. seedHK HK w A1 M1 model1 (set_tr c (B1 ++ [])) E X1.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R2.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12. rreg HRn (22%bv) G22. rreg HRn (23%bv) G23.
    rewrite ?w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    try replace (Z_to_bv 5 (Z.of_N 22)) with (22%bv : reg) in * by (apply bv_eq; reflexivity). rewrite ?Q22 in *. clear Q22. rename G22 into Q22.
    try replace (Z_to_bv 5 (Z.of_N 23)) with (23%bv : reg) in * by (apply bv_eq; reflexivity). rewrite ?Q23 in *. clear Q23. rename G23 into Q23.
    eapply (pm_put_cstr w c0 K fx A1 M1 model1 (set_tr c (B1 ++ [])) R2 (-4) _ 0x10758 22 22 _ B1 []);
      [exact PS | exact X1 | reflexivity | exact BUD1 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS1 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | apply ro_cstr_of_chk; vm_compute; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A2 R2c M2 model2 B2 X2 BUD2 KEPT _ DS2 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp. keptQ KEPT Q22 Q22_. clear Q22. rename Q22_ into Q22. keptQ KEPT Q23 Q23_. clear Q23. rename Q23_ into Q23.
    eapply (cellw_frame _ M2) in Cio; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M2) in Ciwc; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M2) in Fdm; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (loop_mem_frame w _ M2) in LM; [| lia | lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G22; try clear G23.
    try clear X1 BUD1 DS1 MS1. pose proof (x_ms X2) as MS2.
    pm_seed R2c w (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) [Z_to_bv 64 (i_io I); Z_to_bv 64 (i_d I)].
    seedHR HR E HTitDiagU1_1 R2c. seedHK HK w A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) E X2.
    apply (know_more E M2 [KWord (SA (EVar 32) 224) (N.to_nat 8) (EVar 40); KRange (EVar 40) 0x10000 (2 ^ 40); KAlign (EVar 40) 4]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         - eapply kword_var; [exact Fdm | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply krange_var; [evs; reflexivity | lia | lia].
         - eapply kalign_var; [evs; reflexivity | lia | lia | exact Hd4]. }
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R3.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (23%bv) G23.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    try replace (Z_to_bv 5 (Z.of_N 23)) with (23%bv : reg) in * by (apply bv_eq; reflexivity). clear Q22 Q23. rename G23 into Q23.
    rewrite aluw_sub_val in Q23. cbn [c_widx set_tr] in Q23.
    eapply (pm_idesc_name w A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) fx R3 _ K X2 (ex_intro _ (i_d I) (ex_intro _ (i_op I) (conj Hdesc G10))) G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
    clear Qsp Qs0 Qgp Qtp. intros R3n KEPT (pnm & nnm & ROnm & Hn256 & Gnm).
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp. keptQ KEPT Q23 Q23_. clear Q23. rename Q23_ into Q23.
    clear G1 G2 G3 G4 G8 KEPT; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G22; try clear G23.
    pose proof ROnm as RO'. destruct RO' as (Rp1 & Rn0 & Rp2 & _).
    pm_seed R3n w (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) [Z_to_bv 64 pnm].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, EVar 39)] R3n. seedHK HK w A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) E X2.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R4.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (22%bv) G22. rreg HRn (23%bv) G23.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    try replace (Z_to_bv 5 (Z.of_N 23)) with (23%bv : reg) in * by (apply bv_eq; reflexivity). rewrite ?Q23 in *. clear Q23. rename G23 into Q23.
    try replace (Z_to_bv 5 (Z.of_N 22)) with (22%bv : reg) in * by (apply bv_eq; reflexivity). rename G22 into Q22p.
    eapply (pm_strlen w A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) fx R4 _ K X2 (ex_intro _ pnm (ex_intro _ nnm (conj ROnm G10))) G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
    clear Qsp Qs0 Qgp Qtp. intros R4s KEPT POst. pose proof (POst pnm nnm ROnm G10) as Gsl. clear POst.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp. keptQ KEPT Q23 Q23_. clear Q23. rename Q23_ into Q23. keptQ KEPT Q22p Q22p_. clear Q22p. rename Q22p_ into Q22p.
    clear G1 G2 G3 G4 G8 KEPT; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G22; try clear G23.
    pm_seed R4s w (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) [Z_to_bv 64 nnm; Z_to_bv 64 pnm].
    seedHR HR E HTitDiagU1_0 R4s. seedHK HK w A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) E X2.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R5.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12. rreg HRn (23%bv) G23.
    rewrite ?w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    try replace (Z_to_bv 5 (Z.of_N 23)) with (23%bv : reg) in * by (apply bv_eq; reflexivity). rewrite ?Q23 in *. clear Q23. rename G23 into Q23.
    clear Q22p.
    eapply (pm_put_cstr w c0 K fx A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) R5 (-4) _ pnm nnm nnm _ B2 []);
      [exact PS | exact X2 | reflexivity | exact BUD2 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS2 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | exact ROnm | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A5 R5c M5 model5 B5 X5 BUD5 KEPT _ DS5 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp. keptQ KEPT Q23 Q23_. clear Q23. rename Q23_ into Q23.
    eapply (cellw_frame _ M5) in Cio; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M5) in Ciwc; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M5) in Fdm; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (loop_mem_frame w _ M5) in LM; [| lia | lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G22; try clear G23.
    try clear X4 BUD4 DS4 MS4. pose proof (x_ms X5) as MS5.
    pm_seed R5c w (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R5c. seedHK HK w A5 M5 model5 (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) E X5.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R6.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12. rreg HRn (23%bv) G23.
    rewrite ?w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    try replace (Z_to_bv 5 (Z.of_N 23)) with (23%bv : reg) in * by (apply bv_eq; reflexivity). rewrite ?Q23 in *. clear Q23. rename G23 into Q23.
    eapply (pm_put_cstr w c0 K fx A5 M5 model5 (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) R6 (-4) _ 0x11599 18 18 _ B5 []);
      [exact PS | exact X5 | reflexivity | exact BUD5 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS5 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | apply ro_cstr_of_chk; vm_compute; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A6 R6c M6 model6 B6 X6 BUD6 KEPT _ DS6 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp. keptQ KEPT Q23 Q23_. clear Q23. rename Q23_ into Q23.
    eapply (cellw_frame _ M6) in Cio; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M6) in Ciwc; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M6) in Fdm; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (loop_mem_frame w _ M6) in LM; [| lia | lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G22; try clear G23.
    try clear X5 BUD5 DS5 MS5. pose proof (x_ms X6) as MS6.
    pm_seed R6c w (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) [Z_to_bv 64 (i_io I)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R6c. seedHK HK w A6 M6 model6 (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) E X6.
    apply (know_more E M6 [KWord (SA (EVar 32) 216) (N.to_nat 8) (EVar 39)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         - eapply kword_var; [exact Cio | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity]. }
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R7.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12. rreg HRn (23%bv) G23.
    rewrite ?w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    try replace (Z_to_bv 5 (Z.of_N 23)) with (23%bv : reg) in * by (apply bv_eq; reflexivity). rewrite ?Q23 in *. clear Q23. rename G23 into Q23.
    eapply (pm_put_u64 w c0 K fx A6 M6 model6 (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) R7 (-4) _ (i_io I) _ B6 []);
      [exact PS | exact X6 | reflexivity | exact BUD6 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS6 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A7 R7c M7 model7 B7 X7 BUD7 KEPT _ DS7 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp. keptQ KEPT Q23 Q23_. clear Q23. rename Q23_ into Q23.
    eapply (cellw_frame _ M7) in Cio; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M7) in Ciwc; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M7) in Fdm; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (loop_mem_frame w _ M7) in LM; [| lia | lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G22; try clear G23.
    try clear X6 BUD6 DS6 MS6. pose proof (x_ms X7) as MS7.
    pm_seed R7c w (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R7c. seedHK HK w A7 M7 model7 (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) E X7.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R8.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12. rreg HRn (23%bv) G23.
    rewrite ?w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    try replace (Z_to_bv 5 (Z.of_N 23)) with (23%bv : reg) in * by (apply bv_eq; reflexivity). rewrite ?Q23 in *. clear Q23. rename G23 into Q23.
    eapply (pm_put_cstr w c0 K fx A7 M7 model7 (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) R8 (-4) _ 0x121a9 34 34 _ B7 []);
      [exact PS | exact X7 | reflexivity | exact BUD7 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS7 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | apply ro_cstr_of_chk; vm_compute; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A8 R8c M8 model8 B8 X8 BUD8 KEPT _ DS8 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp. keptQ KEPT Q23 Q23_. clear Q23. rename Q23_ into Q23.
    eapply (cellw_frame _ M8) in Cio; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M8) in Ciwc; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M8) in Fdm; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (loop_mem_frame w _ M8) in LM; [| lia | lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G22; try clear G23.
    try clear X7 BUD7 DS7 MS7. pose proof (x_ms X8) as MS8.
    lazymatch type of Q23 with getr _ _ = ?v => pm_seed R8c w (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) [v] end.
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (23%bv, EVar 39)] R8c. seedHK HK w A8 M8 model8 (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) E X8.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R9.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite ?w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    rewrite w_zx16 in G11 by (apply sx32_nonneg; apply Z.mod_pos_bound; lia). rewrite sx32_trunc16 in G11. clear Q23.
    pose proof (Z.mod_pos_bound (c_widx c - i_io I) (2 ^ 16) ltac:(lia)) as Hm16.
    eapply (pm_put_u16 w c0 K fx A8 M8 model8 (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) R9 (-4) _ ((c_widx c - i_io I) mod 2 ^ 16) _ B8 []);
      [exact PS | exact X8 | reflexivity | exact BUD8 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS8 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A9 R9c M9 model9 B9 X9 BUD9 KEPT _ DS9 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    eapply (cellw_frame _ M9) in Cio; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M9) in Ciwc; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M9) in Fdm; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (loop_mem_frame w _ M9) in LM; [| lia | lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G22; try clear G23.
    try clear X8 BUD8 DS8 MS8. pose proof (x_ms X9) as MS9.
    pm_seed R9c w (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) (B9 ++ [])) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R9c. seedHK HK w A9 M9 model9 (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) (B9 ++ [])) E X9.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R10.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite ?w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_put_cstr w c0 K fx A9 M9 model9 (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) (B9 ++ [])) R10 (-4) _ 0x12973 33 33 _ B9 []);
      [exact PS | exact X9 | reflexivity | exact BUD9 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS9 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | apply ro_cstr_of_chk; vm_compute; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A10 R10c M10 model10 B10 X10 BUD10 KEPT _ DS10 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    eapply (cellw_frame _ M10) in Cio; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M10) in Ciwc; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M10) in Fdm; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (loop_mem_frame w _ M10) in LM; [| lia | lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G22; try clear G23.
    try clear X9 BUD9 DS9 MS9. pose proof (x_ms X10) as MS10.
    pm_seed R10c w (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) (B9 ++ [])) (B10 ++ [])) [Z_to_bv 64 (i_iwc I)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R10c. seedHK HK w A10 M10 model10 (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) (B9 ++ [])) (B10 ++ [])) E X10.
    apply (know_more E M10 [KWord (SA (EVar 32) 234) (N.to_nat 2) (EVar 39)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         - eapply kword_var; [exact Ciwc | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity]. }
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R11.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite ?w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_put_u16 w c0 K fx A10 M10 model10 (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) (B9 ++ [])) (B10 ++ [])) R11 (-4) _ (i_iwc I) _ B10 []);
      [exact PS | exact X10 | reflexivity | exact BUD10 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS10 | cregs_tac G1 G2 G3 G4
      | exact G10 | rewrite G11; rewrite ext_val_zx2 by lia; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A11 R11c M11 model11 B11 X11 BUD11 KEPT _ DS11 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    eapply (cellw_frame _ M11) in Cio; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M11) in Ciwc; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M11) in Fdm; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (loop_mem_frame w _ M11) in LM; [| lia | lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G22; try clear G23.
    try clear X10 BUD10 DS10 MS10. pose proof (x_ms X11) as MS11.
    pm_seed R11c w (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) (B9 ++ [])) (B10 ++ [])) (B11 ++ [])) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R11c. seedHK HK w A11 M11 model11 (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) (B9 ++ [])) (B10 ++ [])) (B11 ++ [])) E X11.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R12.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite ?w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_put_cstr w c0 K fx A11 M11 model11 (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) (B9 ++ [])) (B10 ++ [])) (B11 ++ [])) R12 (-4) _ 0x11098 1 1 _ B11 []);
      [exact PS | exact X11 | reflexivity | exact BUD11 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS11 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | apply ro_cstr_of_chk; vm_compute; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A12 R12c M12 model12 B12 X12 BUD12 KEPT _ DS12 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    eapply (cellw_frame _ M12) in Cio; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M12) in Ciwc; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M12) in Fdm; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (loop_mem_frame w _ M12) in LM; [| lia | lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G22; try clear G23.
    try clear X11 BUD11 DS11 MS11. pose proof (x_ms X12) as MS12.
    pm_seed R12c w (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) (B9 ++ [])) (B10 ++ [])) (B11 ++ [])) (B12 ++ [])) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R12c. seedHK HK w A12 M12 model12 (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) (B9 ++ [])) (B10 ++ [])) (B11 ++ [])) (B12 ++ [])) E X12.
    xruns HR HK 100%nat (0x67748 :: STOPS) (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn Rt. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_tail_676a4 w c0 K fx A12 M12 model12 _ Rt (-4) _ B12);
      [exact PS | exact X12 | cbn [c_tr set_tr]; rewrite ?app_nil_r; reflexivity | exact BUD12 | exact DS12 | lia | exact FZ
      | exact G2 | exact G3 | exact G4].
  Qed.
End PM.
