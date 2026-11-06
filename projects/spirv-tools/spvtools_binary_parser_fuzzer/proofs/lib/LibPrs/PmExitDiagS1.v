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
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac WalkTac StartupTac SumWalkTac StoreOk MemSplit Hoare ShapeAlg
  SRealizes RefMemcpyLib RefReadLib FPSteps LibIface LibBudget LibEff MmapSim LibMaskBits
  ZStores SymExec3 SymExec3Sound SymRun3 S1Layout.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContLib StrLib LiveStats ContStmts S1Facts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts HCommon HLib HConstsS1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsNeeds PrsInv PrsStmts PmBase PmHyps PmCoreS1 PmStepS1. Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep2S1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep2S1.PmUpd. From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PmStep2S1 PmLoopS1 PmBody1S1 PmStep3S1 PmODefsS1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PeLia.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Local Ltac lia ::= pe_lia.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Abbreviation SEGS := Plain.M.loaded_segments.

Module Ly := S1Layout.

Section PM.
Context {AC : AllocCeiling}.
  Context {MI : MallocIface SEGS Ly.L} {ST : StaticsIface SEGS Ly.L}.
  Context {G : grammar} {idesc : Z -> Z -> Prop} {odesc edesc : Z -> Z -> Z -> Prop}
          {generates_type is_ext_inst is_nonsemantic : Z -> bool}
          {ds_rep : AS MI -> mem -> Z -> Z -> Z -> list (Z * Z) -> Prop}.
  Variable CL : pm_callees SEGS Ly.L MI ST G tcS1 dcS1 nfcS1 HConstsS1.hc ccS1 kcS1
                  idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep.

  #[local] Notation PMX := (PmBase.PMX MI ST).
  #[local] Notation cfg fx R pc M model := (mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom SEGS)) model).
  #[local] Notation DL := (cl_ds_laws _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  #[local] Notation pm_exit := (PmCoreS1.pm_exit MI ST).
  #[local] Notation pmx_ds_room := (PmStepS1.pmx_ds_room CL).
  #[local] Notation pm_tail_68410 := (PmStepS1.pm_tail_68410 CL).
  #[local] Notation cregs_kept := (PmStepS1.cregs_kept CL).
  #[local] Notation pm_put_cstr := (PmStepS1.pm_put_cstr CL).
  #[local] Notation pm_put_num := (PmStepS1.pm_put_num CL).
  #[local] Notation pm_put_u16 := (PmStepS1.pm_put_u16 CL).
  #[local] Notation pm_put_u32 := (PmStepS1.pm_put_u32 CL).
  #[local] Notation pm_put_u64 := (PmStepS1.pm_put_u64 CL).
  #[local] Notation pm_put_int := (PmStepS1.pm_put_int CL).
  #[local] Notation pm_ctor := (PmStepS1.pm_ctor CL).
  #[local] Notation pm_pdiag := (PmStepS1.pm_pdiag CL).
  #[local] Notation pm_pdiag0 := (PmStepS1.pm_pdiag0 CL).
  #[local] Notation pm_pdiagE := (PmStepS1.pm_pdiagE CL).
  #[local] Notation pm_dtor := (PmStepS1.pm_dtor CL).
  #[local] Notation pm_exhausted := (PmStepS1.pm_exhausted CL).
  #[local] Notation pm_fixword := (PmStepS1.pm_fixword CL).
  #[local] Notation pm_is_host_endian := (PmStepS1.pm_is_host_endian CL).
  #[local] Notation pm_binend := (PmStepS1.pm_binend CL).
  #[local] Notation pm_ecw_pb := (PmStep2S1.pm_ecw_pb CL).
  #[local] Notation pm_opcode_split := (PmStep2S1.pm_opcode_split CL).
  #[local] Notation pm_lookup_opcode := (PmStep2S1.pm_lookup_opcode CL).
  #[local] Notation pm_lookup_operand := (PmStep2S1.pm_lookup_operand CL).
  #[local] Notation pm_lookup_ext := (PmStep2S1.pm_lookup_ext CL).
  #[local] Notation pm_idesc_operands := (PmStep3S1.pm_idesc_operands CL).
  #[local] Notation pm_odesc_operands := (PmStep3S1.pm_odesc_operands CL).
  #[local] Notation pm_edesc_operands := (PmStep3S1.pm_edesc_operands CL).
  #[local] Notation pm_push_types := (PmStep3S1.pm_push_types CL).
  #[local] Notation pm_take_first := (PmStep3S1.pm_take_first CL).

  #[local] Notation izero := (PmBody1S1.izero).
  #[local] Notation ictx := (PmBody1S1.ictx).
  #[local] Notation ipure := (PmODefsS1.ipure (G:=G) (idesc:=idesc)).
  #[local] Notation OLI := (PmODefsS1.OLI (MI:=MI) (ST:=ST) (generates_type:=generates_type)).
  #[local] Notation iacc := (PmODefsS1.iacc (generates_type:=generates_type)).
  Definition pm_idesc_name := pm_leafA (MI:=MI) (ST:=ST) _ _ _ (cl_idesc_name _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  Definition pm_strlen := pm_leafA (MI:=MI) (ST:=ST) _ _ _ (cl_strlen _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  Lemma fld_mod64 : forall M a d, fld SEGS M a 8 d -> fld SEGS M a 8 (d mod 2 ^ 64).
  Proof using. intros M a d F. unfold CRep.fld in *. rewrite <- (LibMaskBits.Z_to_bv_mod64 d). exact F. Qed.
  Lemma ext_val_zx2 : forall v, 0 <= v < 2 ^ 16 -> ext_val false 0 2 (Z_to_bv 64 v) = Z_to_bv 64 v.
  Proof using. intros v Hv. apply ext_val_zx_id. rewrite u64_of_Z by lia. cbn. lia. Qed.
  Lemma w_mul_lit : forall a b, mul_div M_MUL (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a * b).
  Proof using.
    intros a b. apply bv_eq. cbn [mul_div].
    rewrite bv_mul_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite <- Zmult_mod. reflexivity.
  Qed.
  Lemma w_zx16 : forall v, 0 <= v ->
    alu64 ALU_SRL (mul_div M_MUL (Z_to_bv 64 281474976710656) (Z_to_bv 64 v)) (Z_to_bv 64 48) = Z_to_bv 64 (v mod 2 ^ 16).
  Proof using.
    intros v Hv. pose proof (Z.mod_pos_bound v (2 ^ 16) ltac:(lia)) as Hm.
    rewrite w_mul_lit. apply bv_eq. rewrite u_srl64. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
    rewrite (Z.mod_small 48) by lia. change (48 mod 64) with 48. rewrite (Z.mod_small (v mod 2 ^ 16)) by lia.
    change 281474976710656 with (2 ^ 48). rewrite (Z.mul_comm (2 ^ 48) v). change (2 ^ 64) with (2 ^ 16 * 2 ^ 48).
    rewrite Z.mul_mod_distr_r by lia. rewrite Z.div_mul by lia. reflexivity.
  Qed.

#[local] Definition HTitDiagS1_0 : list (reg * expr) := [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, EVar 39); (21%bv, EVar 40)].
  Lemma pm_D7 : forall (w : pmw MI ST) c0 K (fx : FPState) (I : ictxR) A M model c R,
    PMS w c0 K -> frm_zero (@fp_csr fx) -> ipure I -> OLI w I A M model c R ->
    c_widx c < i_io I + i_iwc I -> t3b (c_v3 c) = [] ->
    getr R 22%bv = Z_to_bv 64 (c_widx c) -> getr R 21%bv = Z_to_bv 64 (i_io I) -> getr R 10%bv = Z_to_bv 64 (i_iwc I) ->
    srealizes SEGS (cfg fx R 0x67a78 M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx I A M model c R PS FZ IP HOLI Hlt Hnil Q22 Q21 Qa0.
    destruct HOLI as (OB & Hw1 & _). destruct OB as (X & Htr & BUD & OR & LM & IC & IFR & Hic & He2 & Hw & _).
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & Gc2 & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (x_scal X) as (Sc1 & Sc2 & Sc3 & Sc4). pose proof (ipure_ranges I IP) as (Riwc & Rop).
    pose proof IP as IP'. destruct IP' as (_ & _ & _ & _ & Hg & Hdesc & Rio).
    destruct OR as (Qsp & Qgp & Qtp & Qs0 & Qs1 & Qs3 & Qs4 & Qs8).
    destruct IC as (Cio & Cfw & Ciwc & Cop & Fd). pose proof (proj1 Cio) as Rio64. pose proof (proj1 Ciwc) as Riwc16. cbn in Rio64, Riwc16.
    pose proof (fld_cellw M _ 8 _ (fld_mod64 M _ _ Fd) ltac:(apply Z.mod_pos_bound; lia)) as Fdm.
    pm_seed R w c (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R. seedHK HK w A M model c E X.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R1.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12. rreg HRn (13%bv) G13. rreg HRn (14%bv) G14. rreg HRn (15%bv) G15. rreg HRn (21%bv) G21. rreg HRn (22%bv) G22.
    rewrite w_add in G10, G11, G13, G15 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    try replace (Z_to_bv 5 (Z.of_N 21)) with (21%bv : reg) in * by (apply bv_eq; reflexivity). rewrite ?Q21 in *. clear Q21. rename G21 into Q21.
    try replace (Z_to_bv 5 (Z.of_N 22)) with (22%bv : reg) in * by (apply bv_eq; reflexivity). rewrite ?Q22 in *. clear Q22. rename G22 into Q22.
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (Mw0 := m) end.
    assert (STw : stores_in (fun a => zwin (w_sp w + 752) (w_sp w + 752 + 24) a \/ zwin (w_sp w + 728) (w_sp w + 728 + 2) a \/ zwin (w_sp w + 704) (w_sp w + 704 + 2) a) M Mw0) by (unfold Mw0; stin).
    assert (Xw : PMX w A Mw0 model c).
    { eapply (pmx_frame_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img); [exact X | exact STw | unfold zwin, w_sp0, PM_FRAME; intros; lia]. }
    eapply (cellw_frame _ Mw0) in Cio; [| lia | cbn; lia | eapply stores_in_agree; [exact STw | unfold zwin; cbn; intros; lia]].
    eapply (cellw_frame _ Mw0) in Ciwc; [| lia | cbn; lia | eapply stores_in_agree; [exact STw | unfold zwin; cbn; intros; lia]].
    eapply (cellw_frame _ Mw0) in Fdm; [| lia | cbn; lia | eapply stores_in_agree; [exact STw | unfold zwin; cbn; intros; lia]].
    eapply (loop_mem_frame w _ Mw0) in LM; [| lia | lia | eapply stores_in_agree; [exact STw | unfold zwin; intros; lia]].
    clear STw.
    eapply (pm_ctor w c0 K fx A Mw0 model c R1 (-4) (w_sp w + 752) (w_sp w + 728) (w_sp w + 704) _ []);
      [exact PS | exact Xw | exact Htr | exact BUD | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | exact G13 | exact G14 | exact G15 | lia
      | unfold ftemp, w_sp0, PM_FRAME, DS_SIZE; lia | unfold ftemp, w_sp0, PM_FRAME, DS_SIZE; lia | unfold ftemp, w_sp0, PM_FRAME, DS_SIZE; lia
      | unfold Mw0; rdback | unfold Mw0; rdback |].
    clear Xw.
    clear Qsp Qs0 Qgp Qtp. intros A1 R1c M1 model1 B1 X1 BUD1 KEPT DS1 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp. keptQ KEPT Q21 Q21_. clear Q21. rename Q21_ into Q21. keptQ KEPT Q22 Q22_. clear Q22. rename Q22_ into Q22.
    eapply (cellw_frame _ M1) in Cio; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M1) in Ciwc; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M1) in Fdm; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (loop_mem_frame w _ M1) in LM; [| lia | lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X0 BUD0. pose proof (x_ms X1) as MS1.
    assert (C704 : cellw SEGS M1 (w_sp w + 704) 1 0).
    { split; [cbn; lia|]. change (N.to_nat 1) with 1%nat. rewrite (rdn_agree_win SEGS Mw0 M1 (w_sp w + 704) 1); [unfold Mw0; rdback | lia | lia |].
      eapply agree_on_weaken; [exact AG|]. unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE. intros; lia. }
    assert (C728 : cellw SEGS M1 (w_sp w + 728) 1 0).
    { split; [cbn; lia|]. change (N.to_nat 1) with 1%nat. rewrite (rdn_agree_win SEGS Mw0 M1 (w_sp w + 728) 1); [unfold Mw0; rdback | lia | lia |].
      eapply agree_on_weaken; [exact AG|]. unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE. intros; lia. }
    clear AG. clearbody Mw0.
    pm_seed R1c w (set_tr c (B1 ++ [])) [Z_to_bv 64 0].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R1c. seedHK HK w A1 M1 model1 (set_tr c (B1 ++ [])) E X1.
    apply (know_more E M1 [KWord (SA (EVar 32) 704) (N.to_nat 1) (EVar 39); KWord (SA (EVar 32) 728) (N.to_nat 1) (EVar 39); KRange (EVar 39) 0 0; KWord (SA (EVar 32) 120) (N.to_nat 8) (ELit 67416)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         - eapply kword_var; [exact C704 | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply kword_var; [exact C728 | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply krange_var; [evs; reflexivity | lia | lia].
         - eapply kword_var; [eapply (PmBody1S1.loop_mem_cell w _ 120 67416 LM); [(first [ solve [cbn [In]; repeat (first [left; reflexivity | right])] | cbn; repeat (first [left; reflexivity | right]) ]) | lia] | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | cbn [edenot]; reflexivity]. }
    xruns HR HK 100%nat STOPS (SCR [true; true] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R2.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12. rreg HRn (18%bv) G18. rreg HRn (21%bv) G21. rreg HRn (22%bv) G22.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    try replace (Z_to_bv 5 (Z.of_N 21)) with (21%bv : reg) in * by (apply bv_eq; reflexivity). rewrite ?Q21 in *. clear Q21. rename G21 into Q21.
    try replace (Z_to_bv 5 (Z.of_N 22)) with (22%bv : reg) in * by (apply bv_eq; reflexivity). rewrite ?Q22 in *. clear Q22. rename G22 into Q22.
    clear C704 C728.
    rewrite w_mul_lit, SymExec.alu64_add_lit in G18. replace (-1 * i_io I + c_widx c) with (c_widx c - i_io I) in G18 by lia. rename G18 into Q18. clear Q21 Q22.
    eapply (pm_put_cstr w c0 K fx A1 M1 model1 (set_tr c (B1 ++ [])) R2 (-4) _ 0x10758 22 22 _ B1 []);
      [exact PS | exact X1 | reflexivity | exact BUD1 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS1 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | apply ro_cstr_of_chk; vm_compute; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A2 R2c M2 model2 B2 X2 BUD2 KEPT _ DS2 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp. keptQ KEPT Q18 Q18_. clear Q18. rename Q18_ into Q18.
    eapply (cellw_frame _ M2) in Cio; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M2) in Ciwc; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M2) in Fdm; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (loop_mem_frame w _ M2) in LM; [| lia | lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X1 BUD1 DS1. pose proof (x_ms X2) as MS2.
    pm_seed R2c w (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) [Z_to_bv 64 (i_d I mod 2 ^ 64)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R2c. seedHK HK w A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) E X2.
    apply (know_more E M2 [KWord (SA (EVar 32) 208) (N.to_nat 8) (EVar 39)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         - eapply kword_var; [exact Fdm | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity]. }
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R3.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (18%bv) G18.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    try replace (Z_to_bv 5 (Z.of_N 18)) with (18%bv : reg) in * by (apply bv_eq; reflexivity). rewrite ?Q18 in *. clear Q18. rename G18 into Q18.
    rewrite <- (LibMaskBits.Z_to_bv_mod64 (i_d I)) in G10.
    eapply (pm_idesc_name w A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) fx R3 _ K X2 (ex_intro _ (i_d I) (ex_intro _ (i_op I) (conj Hdesc G10))) G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
    clear Qsp Qs0 Qgp Qtp. intros R3n KEPT (pnm & nnm & ROnm & Hn256 & Gnm).
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp. keptQ KEPT Q18 Q18_. clear Q18. rename Q18_ into Q18.
    clear G1 G2 G3 G4 G8 G10 KEPT; try clear G9; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    pose proof ROnm as RO'. destruct RO' as (Rp1 & Rn0 & Rp2 & _).
    pm_seed R3n w (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) [Z_to_bv 64 pnm].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, EVar 39)] R3n. seedHK HK w A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) E X2.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R4.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (18%bv) G18. rreg HRn (21%bv) G21.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    try replace (Z_to_bv 5 (Z.of_N 18)) with (18%bv : reg) in * by (apply bv_eq; reflexivity). rewrite ?Q18 in *. clear Q18. rename G18 into Q18.
    try replace (Z_to_bv 5 (Z.of_N 21)) with (21%bv : reg) in * by (apply bv_eq; reflexivity). rename G21 into Q21p.
    eapply (pm_strlen w A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) fx R4 _ K X2 (ex_intro _ pnm (ex_intro _ nnm (conj ROnm G10))) G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
    clear Qsp Qs0 Qgp Qtp. intros R4s KEPT POst. pose proof (POst pnm nnm ROnm G10) as Gsl. clear POst.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp. keptQ KEPT Q18 Q18_. clear Q18. rename Q18_ into Q18. keptQ KEPT Q21p Q21p_. clear Q21p. rename Q21p_ into Q21p.
    clear G1 G2 G3 G4 G8 G10 KEPT; try clear G9; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    pm_seed R4s w (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) [Z_to_bv 64 nnm; Z_to_bv 64 pnm].
    seedHR HR E HTitDiagS1_0 R4s. seedHK HK w A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) E X2.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R5.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12. rreg HRn (18%bv) G18.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    try replace (Z_to_bv 5 (Z.of_N 18)) with (18%bv : reg) in * by (apply bv_eq; reflexivity). rewrite ?Q18 in *. clear Q18. rename G18 into Q18.
    eapply (pm_put_cstr w c0 K fx A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) R5 (-4) _ pnm nnm nnm _ B2 []);
      [exact PS | exact X2 | reflexivity | exact BUD2 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS2 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | exact ROnm | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A5 R5c M5 model5 B5 X5 BUD5 KEPT _ DS5 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp. keptQ KEPT Q18 Q18_. clear Q18. rename Q18_ into Q18.
    eapply (cellw_frame _ M5) in Cio; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M5) in Ciwc; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M5) in Fdm; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (loop_mem_frame w _ M5) in LM; [| lia | lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X4 BUD4 DS4. pose proof (x_ms X5) as MS5.
    pm_seed R5c w (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R5c. seedHK HK w A5 M5 model5 (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) E X5.
    apply (know_more E M5 [KWord (SA (EVar 32) 112) (N.to_nat 8) (ELit 71065)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         - eapply kword_var; [eapply (PmBody1S1.loop_mem_cell w _ 112 71065 LM); [(first [ solve [cbn [In]; repeat (first [left; reflexivity | right])] | cbn; repeat (first [left; reflexivity | right]) ]) | lia] | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | cbn [edenot]; reflexivity]. }
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R6.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12. rreg HRn (18%bv) G18.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    try replace (Z_to_bv 5 (Z.of_N 18)) with (18%bv : reg) in * by (apply bv_eq; reflexivity). rewrite ?Q18 in *. clear Q18. rename G18 into Q18.
    eapply (pm_put_cstr w c0 K fx A5 M5 model5 (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) R6 (-4) _ 0x11599 18 18 _ B5 []);
      [exact PS | exact X5 | reflexivity | exact BUD5 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS5 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | apply ro_cstr_of_chk; vm_compute; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A6 R6c M6 model6 B6 X6 BUD6 KEPT _ DS6 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp. keptQ KEPT Q18 Q18_. clear Q18. rename Q18_ into Q18.
    eapply (cellw_frame _ M6) in Cio; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M6) in Ciwc; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M6) in Fdm; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (loop_mem_frame w _ M6) in LM; [| lia | lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X5 BUD5 DS5. pose proof (x_ms X6) as MS6.
    pm_seed R6c w (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) [Z_to_bv 64 (i_io I)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R6c. seedHK HK w A6 M6 model6 (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) E X6.
    apply (know_more E M6 [KWord (SA (EVar 32) 200) (N.to_nat 8) (EVar 39)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         - eapply kword_var; [exact Cio | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity]. }
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R7.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12. rreg HRn (18%bv) G18.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    try replace (Z_to_bv 5 (Z.of_N 18)) with (18%bv : reg) in * by (apply bv_eq; reflexivity). rewrite ?Q18 in *. clear Q18. rename G18 into Q18.
    eapply (pm_put_u64 w c0 K fx A6 M6 model6 (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) R7 (-4) _ (i_io I) _ B6 []);
      [exact PS | exact X6 | reflexivity | exact BUD6 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS6 | cregs_tac G1 G2 G3 G4
      | exact G10 | rewrite G11; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A7 R7c M7 model7 B7 X7 BUD7 KEPT _ DS7 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp. keptQ KEPT Q18 Q18_. clear Q18. rename Q18_ into Q18.
    eapply (cellw_frame _ M7) in Cio; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M7) in Ciwc; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M7) in Fdm; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (loop_mem_frame w _ M7) in LM; [| lia | lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X6 BUD6 DS6. pose proof (x_ms X7) as MS7.
    pm_seed R7c w (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R7c. seedHK HK w A7 M7 model7 (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) E X7.
    apply (know_more E M7 [KWord (SA (EVar 32) 104) (N.to_nat 8) (ELit 74153)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         - eapply kword_var; [eapply (PmBody1S1.loop_mem_cell w _ 104 74153 LM); [(first [ solve [cbn [In]; repeat (first [left; reflexivity | right])] | cbn; repeat (first [left; reflexivity | right]) ]) | lia] | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | cbn [edenot]; reflexivity]. }
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R8.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12. rreg HRn (18%bv) G18.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    try replace (Z_to_bv 5 (Z.of_N 18)) with (18%bv : reg) in * by (apply bv_eq; reflexivity). rewrite ?Q18 in *. clear Q18. rename G18 into Q18.
    eapply (pm_put_cstr w c0 K fx A7 M7 model7 (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) R8 (-4) _ 0x121a9 34 34 _ B7 []);
      [exact PS | exact X7 | reflexivity | exact BUD7 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS7 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | apply ro_cstr_of_chk; vm_compute; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A8 R8c M8 model8 B8 X8 BUD8 KEPT _ DS8 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp. keptQ KEPT Q18 Q18_. clear Q18. rename Q18_ into Q18.
    eapply (cellw_frame _ M8) in Cio; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M8) in Ciwc; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M8) in Fdm; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (loop_mem_frame w _ M8) in LM; [| lia | lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X7 BUD7 DS7. pose proof (x_ms X8) as MS8.
    pm_seed R8c w (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) [Z_to_bv 64 (c_widx c - i_io I)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (18%bv, EVar 39)] R8c. seedHK HK w A8 M8 model8 (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) E X8.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R9.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    pose proof (Z.mod_pos_bound (c_widx c - i_io I) (2 ^ 16) ltac:(lia)) as Hm16.
    eapply (pm_put_u16 w c0 K fx A8 M8 model8 (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) R9 (-4) _ ((c_widx c - i_io I) mod 2 ^ 16) _ B8 []);
      [exact PS | exact X8 | reflexivity | exact BUD8 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS8 | cregs_tac G1 G2 G3 G4
      | exact G10 | rewrite G11; rewrite w_zx16 by lia; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A9 R9c M9 model9 B9 X9 BUD9 KEPT _ DS9 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    eapply (cellw_frame _ M9) in Cio; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M9) in Ciwc; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M9) in Fdm; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (loop_mem_frame w _ M9) in LM; [| lia | lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X8 BUD8 DS8. pose proof (x_ms X9) as MS9.
    pm_seed R9c w (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) (B9 ++ [])) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R9c. seedHK HK w A9 M9 model9 (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) (B9 ++ [])) E X9.
    apply (know_more E M9 [KWord (SA (EVar 32) 96) (N.to_nat 8) (ELit 76147)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         - eapply kword_var; [eapply (PmBody1S1.loop_mem_cell w _ 96 76147 LM); [(first [ solve [cbn [In]; repeat (first [left; reflexivity | right])] | cbn; repeat (first [left; reflexivity | right]) ]) | lia] | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | cbn [edenot]; reflexivity]. }
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R10.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite w_add in G10 by lia.
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
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X9 BUD9 DS9. pose proof (x_ms X10) as MS10.
    pm_seed R10c w (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) (B9 ++ [])) (B10 ++ [])) [Z_to_bv 64 (i_iwc I)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R10c. seedHK HK w A10 M10 model10 (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) (B9 ++ [])) (B10 ++ [])) E X10.
    apply (know_more E M10 [KWord (SA (EVar 32) 218) (N.to_nat 2) (EVar 39)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         - eapply kword_var; [exact Ciwc | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity]. }
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R11.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite w_add in G10 by lia.
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
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X10 BUD10 DS10. pose proof (x_ms X11) as MS11.
    pm_seed R11c w (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) (B9 ++ [])) (B10 ++ [])) (B11 ++ [])) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R11c. seedHK HK w A11 M11 model11 (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) (B9 ++ [])) (B10 ++ [])) (B11 ++ [])) E X11.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R12.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite w_add in G10 by lia.
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
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X11 BUD11 DS11. pose proof (x_ms X12) as MS12.
    pose proof (dl_err _ _ _ _ _ _ DL _ _ _ _ _ _ DS12) as Herrc. unfold CRep.fld in Herrc.
    assert (Cerr : cell4 SEGS M12 (w_sp w + 272 + 360) ((-4) mod 2 ^ 32)).
    { split; [pose proof (Z.mod_pos_bound (-4) (2 ^ 32)); cbn; lia | exact Herrc]. }
    pm_seed R12c w (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) (B9 ++ [])) (B10 ++ [])) (B11 ++ [])) (B12 ++ [])) [sxw ((-4) mod 2 ^ 32)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R12c. seedHK HK w A12 M12 model12 (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) (B9 ++ [])) (B10 ++ [])) (B11 ++ [])) (B12 ++ [])) E X12.
    xruns HR HK 100%nat STOPS (SCR [] [EVar 39] []) 50%N. { split_scs; try sc_auto1. all: sc_rd_sx Cerr. }
    postrun. name_run HRn R12cd. rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (10%bv) G10. rreg HRn (26%bv) G26.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4. rewrite w_add in G10 by lia.
    eapply (pm_dtor w c0 K fx A12 M12 model12 (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) (B9 ++ [])) (B10 ++ [])) (B11 ++ [])) (B12 ++ [])) R12cd (-4) _ _ B12 []);
      [exact PS | exact X12 | cbn [c_tr set_tr]; rewrite ?app_nil_r; reflexivity | exact BUD12 | rewrite Zlength_nil; lia | exact DS12 | cregs_tac G1 G2 G3 G4 | exact G10 |].
    intros Ad Rd Md modeld Xd BUDd KEPT AGd.
    keptQ KEPT G2 Qsp'. keptQ KEPT G3 Qgp'. keptQ KEPT G4 Qtp'. keptQ KEPT G26 Qs10.
    pose proof (Z.mod_pos_bound (-4) (2 ^ 32) ltac:(lia)) as Hm.
    assert (Hnz : (-4) mod 2 ^ 32 <> 0) by (rewrite <- (Z.mod_add (-4) 1 (2 ^ 32)) by lia; rewrite Z.mod_small by lia; lia).
    pose proof (x_ms Xd) as MSd.
    try clear E. pm_seed Rd w (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) (B9 ++ [])) (B10 ++ [])) (B11 ++ [])) (B12 ++ [])) []) [sxw ((-4) mod 2 ^ 32)].
    seedHR HR E [(2%bv, EVar 32); (26%bv, EVar 39)] Rd. seedHK HK w Ad Md modeld (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) (B9 ++ [])) (B10 ++ [])) (B11 ++ [])) (B12 ++ [])) []) E Xd.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn Re. rreg HRn (2%bv) T2. rreg HRn (3%bv) T3. rreg HRn (4%bv) T4. rreg HRn (26%bv) T26.
    clear HRn HR HK. fixregs. rewrite Qgp' in T3. rewrite Qtp' in T4.
    eapply (PmLoopS1.pm_latch_err w c0 K fx Ad Md modeld (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) (B9 ++ [])) (B10 ++ [])) (B11 ++ [])) (B12 ++ [])) []) Re ((-4) mod 2 ^ 32) PS Xd ltac:(cbn [c_tr set_tr]; reflexivity) BUDd FZ T2 T3 T4 T26 ltac:(lia)).
  Qed.

  Lemma pm_D8 : forall (w : pmw MI ST) c0 K (fx : FPState) (I : ictxR) A M model c R,
    PMS w c0 K -> frm_zero (@fp_csr fx) -> ipure I -> OLI w I A M model c R ->
    srealizes SEGS (cfg fx R 0x67ce0 M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx I A M model c R PS FZ IP HOLI.
    destruct HOLI as (OB & Hw1 & _). destruct OB as (X & Htr & BUD & OR & LM & IC & IFR & Hic & He2 & Hw & _).
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & Gc2 & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (x_scal X) as (Sc1 & Sc2 & Sc3 & Sc4). pose proof (ipure_ranges I IP) as (Riwc & Rop).
    pose proof IP as IP'. destruct IP' as (_ & _ & _ & _ & Hg & Hdesc & Rio).
    destruct OR as (Qsp & Qgp & Qtp & Qs0 & Qs1 & Qs3 & Qs4 & Qs8).
    destruct IC as (Cio & Cfw & Ciwc & Cop & Fd). pose proof (proj1 Cio) as Rio64. pose proof (proj1 Ciwc) as Riwc16. cbn in Rio64, Riwc16.
    pose proof (fld_cellw M _ 8 _ (fld_mod64 M _ _ Fd) ltac:(apply Z.mod_pos_bound; lia)) as Fdm.
    pose proof (fld_cellw M _ 8 _ (x_widx X) ltac:(lia)) as Cwi. unfold O_WIDX in Cwi.
    pm_seed R w c (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R. seedHK HK w A M model c E X.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R1.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12. rreg HRn (13%bv) G13. rreg HRn (14%bv) G14. rreg HRn (15%bv) G15.
    rewrite w_add in G10, G11, G13, G15 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (Mw0 := m) end.
    assert (STw : stores_in (fun a => zwin (w_sp w + 752) (w_sp w + 752 + 24) a \/ zwin (w_sp w + 728) (w_sp w + 728 + 2) a \/ zwin (w_sp w + 704) (w_sp w + 704 + 2) a) M Mw0) by (unfold Mw0; stin).
    assert (Xw : PMX w A Mw0 model c).
    { eapply (pmx_frame_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img); [exact X | exact STw | unfold zwin, w_sp0, PM_FRAME; intros; lia]. }
    eapply (cellw_frame _ Mw0) in Cio; [| lia | cbn; lia | eapply stores_in_agree; [exact STw | unfold zwin; cbn; intros; lia]].
    eapply (cellw_frame _ Mw0) in Ciwc; [| lia | cbn; lia | eapply stores_in_agree; [exact STw | unfold zwin; cbn; intros; lia]].
    eapply (cellw_frame _ Mw0) in Fdm; [| lia | cbn; lia | eapply stores_in_agree; [exact STw | unfold zwin; cbn; intros; lia]].
    eapply (loop_mem_frame w _ Mw0) in LM; [| lia | lia | eapply stores_in_agree; [exact STw | unfold zwin; intros; lia]].
    clear STw.
    eapply (pm_ctor w c0 K fx A Mw0 model c R1 (-4) (w_sp w + 752) (w_sp w + 728) (w_sp w + 704) _ []);
      [exact PS | exact Xw | exact Htr | exact BUD | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | exact G13 | exact G14 | exact G15 | lia
      | unfold ftemp, w_sp0, PM_FRAME, DS_SIZE; lia | unfold ftemp, w_sp0, PM_FRAME, DS_SIZE; lia | unfold ftemp, w_sp0, PM_FRAME, DS_SIZE; lia
      | unfold Mw0; rdback | unfold Mw0; rdback |].
    clear Xw.
    clear Qsp Qs0 Qgp Qtp. intros A1 R1c M1 model1 B1 X1 BUD1 KEPT DS1 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    eapply (cellw_frame _ M1) in Cio; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M1) in Ciwc; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M1) in Fdm; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (loop_mem_frame w _ M1) in LM; [| lia | lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X0 BUD0. pose proof (x_ms X1) as MS1.
    assert (C704 : cellw SEGS M1 (w_sp w + 704) 1 0).
    { split; [cbn; lia|]. change (N.to_nat 1) with 1%nat. rewrite (rdn_agree_win SEGS Mw0 M1 (w_sp w + 704) 1); [unfold Mw0; rdback | lia | lia |].
      eapply agree_on_weaken; [exact AG|]. unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE. intros; lia. }
    assert (C728 : cellw SEGS M1 (w_sp w + 728) 1 0).
    { split; [cbn; lia|]. change (N.to_nat 1) with 1%nat. rewrite (rdn_agree_win SEGS Mw0 M1 (w_sp w + 728) 1); [unfold Mw0; rdback | lia | lia |].
      eapply agree_on_weaken; [exact AG|]. unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE. intros; lia. }
    clear AG. clearbody Mw0.
    pm_seed R1c w (set_tr c (B1 ++ [])) [Z_to_bv 64 0].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R1c. seedHK HK w A1 M1 model1 (set_tr c (B1 ++ [])) E X1.
    apply (know_more E M1 [KWord (SA (EVar 32) 704) (N.to_nat 1) (EVar 39); KWord (SA (EVar 32) 728) (N.to_nat 1) (EVar 39); KRange (EVar 39) 0 0]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         - eapply kword_var; [exact C704 | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply kword_var; [exact C728 | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply krange_var; [evs; reflexivity | lia | lia]. }
    xruns HR HK 100%nat STOPS (SCR [true; true] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R2.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    clear C704 C728.
    eapply (pm_put_cstr w c0 K fx A1 M1 model1 (set_tr c (B1 ++ [])) R2 (-4) _ 0x11738 38 38 _ B1 []);
      [exact PS | exact X1 | reflexivity | exact BUD1 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS1 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | apply ro_cstr_of_chk; vm_compute; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A2 R2c M2 model2 B2 X2 BUD2 KEPT _ DS2 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    eapply (cellw_frame _ M2) in Cio; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M2) in Ciwc; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M2) in Fdm; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (loop_mem_frame w _ M2) in LM; [| lia | lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X1 BUD1 DS1. pose proof (x_ms X2) as MS2.
    pm_seed R2c w (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) [Z_to_bv 64 (i_d I mod 2 ^ 64)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R2c. seedHK HK w A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) E X2.
    apply (know_more E M2 [KWord (SA (EVar 32) 208) (N.to_nat 8) (EVar 39)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         - eapply kword_var; [exact Fdm | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity]. }
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R3.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    rewrite <- (LibMaskBits.Z_to_bv_mod64 (i_d I)) in G10.
    eapply (pm_idesc_name w A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) fx R3 _ K X2 (ex_intro _ (i_d I) (ex_intro _ (i_op I) (conj Hdesc G10))) G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
    clear Qsp Qs0 Qgp Qtp. intros R3n KEPT (pnm & nnm & ROnm & Hn256 & Gnm).
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    clear G1 G2 G3 G4 G8 G10 KEPT; try clear G9; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    pose proof ROnm as RO'. destruct RO' as (Rp1 & Rn0 & Rp2 & _).
    pm_seed R3n w (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) [Z_to_bv 64 pnm].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, EVar 39)] R3n. seedHK HK w A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) E X2.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R4.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (21%bv) G21.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    try replace (Z_to_bv 5 (Z.of_N 21)) with (21%bv : reg) in * by (apply bv_eq; reflexivity). rename G21 into Q21p.
    eapply (pm_strlen w A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) fx R4 _ K X2 (ex_intro _ pnm (ex_intro _ nnm (conj ROnm G10))) G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
    clear Qsp Qs0 Qgp Qtp. intros R4s KEPT POst. pose proof (POst pnm nnm ROnm G10) as Gsl. clear POst.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp. keptQ KEPT Q21p Q21p_. clear Q21p. rename Q21p_ into Q21p.
    clear G1 G2 G3 G4 G8 G10 KEPT; try clear G9; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    pm_seed R4s w (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) [Z_to_bv 64 nnm; Z_to_bv 64 pnm].
    seedHR HR E HTitDiagS1_0 R4s. seedHK HK w A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) E X2.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R5.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_put_cstr w c0 K fx A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) R5 (-4) _ pnm nnm nnm _ B2 []);
      [exact PS | exact X2 | reflexivity | exact BUD2 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS2 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | exact ROnm | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A5 R5c M5 model5 B5 X5 BUD5 KEPT _ DS5 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    eapply (cellw_frame _ M5) in Cio; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M5) in Ciwc; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M5) in Fdm; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (loop_mem_frame w _ M5) in LM; [| lia | lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X4 BUD4 DS4. pose proof (x_ms X5) as MS5.
    pm_seed R5c w (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R5c. seedHK HK w A5 M5 model5 (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) E X5.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R6.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite w_add in G10 by lia.
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
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X5 BUD5 DS5. pose proof (x_ms X6) as MS6.
    pm_seed R6c w (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) [Z_to_bv 64 (i_io I)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R6c. seedHK HK w A6 M6 model6 (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) E X6.
    apply (know_more E M6 [KWord (SA (EVar 32) 200) (N.to_nat 8) (EVar 39)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         - eapply kword_var; [exact Cio | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity]. }
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R7.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_put_u64 w c0 K fx A6 M6 model6 (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) R7 (-4) _ (i_io I) _ B6 []);
      [exact PS | exact X6 | reflexivity | exact BUD6 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS6 | cregs_tac G1 G2 G3 G4
      | exact G10 | rewrite G11; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A7 R7c M7 model7 B7 X7 BUD7 KEPT _ DS7 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    eapply (cellw_frame _ M7) in Cio; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M7) in Ciwc; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M7) in Fdm; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (loop_mem_frame w _ M7) in LM; [| lia | lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X6 BUD6 DS6. pose proof (x_ms X7) as MS7.
    pm_seed R7c w (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R7c. seedHK HK w A7 M7 model7 (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) E X7.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R8.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite w_add in G10 by lia.
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
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X7 BUD7 DS7. pose proof (x_ms X8) as MS8.
    pm_seed R8c w (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) [Z_to_bv 64 (i_iwc I)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R8c. seedHK HK w A8 M8 model8 (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) E X8.
    apply (know_more E M8 [KWord (SA (EVar 32) 218) (N.to_nat 2) (EVar 39)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         - eapply kword_var; [exact Ciwc | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity]. }
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R9.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite w_add in G10 by lia.
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
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X8 BUD8 DS8. pose proof (x_ms X9) as MS9.
    pm_seed R9c w (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) (B9 ++ [])) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R9c. seedHK HK w A9 M9 model9 (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) (B9 ++ [])) E X9.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R10.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite w_add in G10 by lia.
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
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X9 BUD9 DS9. pose proof (x_ms X10) as MS10.
    pose proof (dl_err _ _ _ _ _ _ DL _ _ _ _ _ _ DS10) as Herrc. unfold CRep.fld in Herrc.
    assert (Cerr : cell4 SEGS M10 (w_sp w + 272 + 360) ((-4) mod 2 ^ 32)).
    { split; [pose proof (Z.mod_pos_bound (-4) (2 ^ 32)); cbn; lia | exact Herrc]. }
    pm_seed R10c w (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) (B9 ++ [])) (B10 ++ [])) [sxw ((-4) mod 2 ^ 32)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R10c. seedHK HK w A10 M10 model10 (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) (B9 ++ [])) (B10 ++ [])) E X10.
    xruns HR HK 100%nat STOPS (SCR [] [EVar 39] []) 50%N. { split_scs; try sc_auto1. all: sc_rd_sx Cerr. }
    postrun. name_run HRn R10cd. rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (10%bv) G10. rreg HRn (26%bv) G26.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4. rewrite w_add in G10 by lia.
    eapply (pm_dtor w c0 K fx A10 M10 model10 (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) (B9 ++ [])) (B10 ++ [])) R10cd (-4) _ _ B10 []);
      [exact PS | exact X10 | cbn [c_tr set_tr]; rewrite ?app_nil_r; reflexivity | exact BUD10 | rewrite Zlength_nil; lia | exact DS10 | cregs_tac G1 G2 G3 G4 | exact G10 |].
    intros Ad Rd Md modeld Xd BUDd KEPT AGd.
    keptQ KEPT G2 Qsp'. keptQ KEPT G3 Qgp'. keptQ KEPT G4 Qtp'. keptQ KEPT G26 Qs10.
    pose proof (Z.mod_pos_bound (-4) (2 ^ 32) ltac:(lia)) as Hm.
    assert (Hnz : (-4) mod 2 ^ 32 <> 0) by (rewrite <- (Z.mod_add (-4) 1 (2 ^ 32)) by lia; rewrite Z.mod_small by lia; lia).
    pose proof (x_ms Xd) as MSd.
    try clear E. pm_seed Rd w (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) (B9 ++ [])) (B10 ++ [])) []) [sxw ((-4) mod 2 ^ 32)].
    seedHR HR E [(2%bv, EVar 32); (26%bv, EVar 39)] Rd. seedHK HK w Ad Md modeld (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) (B9 ++ [])) (B10 ++ [])) []) E Xd.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn Re. rreg HRn (2%bv) T2. rreg HRn (3%bv) T3. rreg HRn (4%bv) T4. rreg HRn (26%bv) T26.
    clear HRn HR HK. fixregs. rewrite Qgp' in T3. rewrite Qtp' in T4.
    eapply (PmLoopS1.pm_latch_err w c0 K fx Ad Md modeld (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) (B9 ++ [])) (B10 ++ [])) []) Re ((-4) mod 2 ^ 32) PS Xd ltac:(cbn [c_tr set_tr]; reflexivity) BUDd FZ T2 T3 T4 T26 ltac:(lia)).
  Qed.

  Lemma pm_D9 : forall (w : pmw MI ST) c0 K (fx : FPState) (I : ictxR) A M model c R,
    PMS w c0 K -> frm_zero (@fp_csr fx) -> ipure I -> OLI w I A M model c R ->
    srealizes SEGS (cfg fx R 0x67bc0 M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx I A M model c R PS FZ IP HOLI.
    destruct HOLI as (OB & Hw1 & _). destruct OB as (X & Htr & BUD & OR & LM & IC & IFR & Hic & He2 & Hw & _).
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & Gc2 & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (x_scal X) as (Sc1 & Sc2 & Sc3 & Sc4). pose proof (ipure_ranges I IP) as (Riwc & Rop).
    pose proof IP as IP'. destruct IP' as (_ & _ & _ & _ & Hg & Hdesc & Rio).
    destruct OR as (Qsp & Qgp & Qtp & Qs0 & Qs1 & Qs3 & Qs4 & Qs8).
    destruct IC as (Cio & Cfw & Ciwc & Cop & Fd). pose proof (proj1 Cio) as Rio64. pose proof (proj1 Ciwc) as Riwc16. cbn in Rio64, Riwc16.
    pose proof (fld_cellw M _ 8 _ (fld_mod64 M _ _ Fd) ltac:(apply Z.mod_pos_bound; lia)) as Fdm.
    pose proof (fld_cellw M _ 8 _ (x_widx X) ltac:(lia)) as Cwi. unfold O_WIDX in Cwi.
    pm_seed R w c (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R. seedHK HK w A M model c E X.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R1.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12. rreg HRn (13%bv) G13. rreg HRn (14%bv) G14. rreg HRn (15%bv) G15.
    rewrite w_add in G10, G11, G13, G15 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (Mw0 := m) end.
    assert (STw : stores_in (fun a => zwin (w_sp w + 752) (w_sp w + 752 + 24) a \/ zwin (w_sp w + 728) (w_sp w + 728 + 2) a \/ zwin (w_sp w + 704) (w_sp w + 704 + 2) a) M Mw0) by (unfold Mw0; stin).
    assert (Xw : PMX w A Mw0 model c).
    { eapply (pmx_frame_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img); [exact X | exact STw | unfold zwin, w_sp0, PM_FRAME; intros; lia]. }
    eapply (cellw_frame _ Mw0) in Cio; [| lia | cbn; lia | eapply stores_in_agree; [exact STw | unfold zwin; cbn; intros; lia]].
    eapply (cellw_frame _ Mw0) in Ciwc; [| lia | cbn; lia | eapply stores_in_agree; [exact STw | unfold zwin; cbn; intros; lia]].
    eapply (cellw_frame _ Mw0) in Fdm; [| lia | cbn; lia | eapply stores_in_agree; [exact STw | unfold zwin; cbn; intros; lia]].
    eapply (loop_mem_frame w _ Mw0) in LM; [| lia | lia | eapply stores_in_agree; [exact STw | unfold zwin; intros; lia]].
    clear STw.
    eapply (pm_ctor w c0 K fx A Mw0 model c R1 (-4) (w_sp w + 752) (w_sp w + 728) (w_sp w + 704) _ []);
      [exact PS | exact Xw | exact Htr | exact BUD | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | exact G13 | exact G14 | exact G15 | lia
      | unfold ftemp, w_sp0, PM_FRAME, DS_SIZE; lia | unfold ftemp, w_sp0, PM_FRAME, DS_SIZE; lia | unfold ftemp, w_sp0, PM_FRAME, DS_SIZE; lia
      | unfold Mw0; rdback | unfold Mw0; rdback |].
    clear Xw.
    clear Qsp Qs0 Qgp Qtp. intros A1 R1c M1 model1 B1 X1 BUD1 KEPT DS1 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    eapply (cellw_frame _ M1) in Cio; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M1) in Ciwc; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M1) in Fdm; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (loop_mem_frame w _ M1) in LM; [| lia | lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X0 BUD0. pose proof (x_ms X1) as MS1.
    assert (C704 : cellw SEGS M1 (w_sp w + 704) 1 0).
    { split; [cbn; lia|]. change (N.to_nat 1) with 1%nat. rewrite (rdn_agree_win SEGS Mw0 M1 (w_sp w + 704) 1); [unfold Mw0; rdback | lia | lia |].
      eapply agree_on_weaken; [exact AG|]. unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE. intros; lia. }
    assert (C728 : cellw SEGS M1 (w_sp w + 728) 1 0).
    { split; [cbn; lia|]. change (N.to_nat 1) with 1%nat. rewrite (rdn_agree_win SEGS Mw0 M1 (w_sp w + 728) 1); [unfold Mw0; rdback | lia | lia |].
      eapply agree_on_weaken; [exact AG|]. unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE. intros; lia. }
    clear AG. clearbody Mw0.
    pm_seed R1c w (set_tr c (B1 ++ [])) [Z_to_bv 64 0].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R1c. seedHK HK w A1 M1 model1 (set_tr c (B1 ++ [])) E X1.
    apply (know_more E M1 [KWord (SA (EVar 32) 704) (N.to_nat 1) (EVar 39); KWord (SA (EVar 32) 728) (N.to_nat 1) (EVar 39); KRange (EVar 39) 0 0]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         - eapply kword_var; [exact C704 | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply kword_var; [exact C728 | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply krange_var; [evs; reflexivity | lia | lia]. }
    xruns HR HK 100%nat STOPS (SCR [true; true] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R2.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    clear C704 C728.
    eapply (pm_put_cstr w c0 K fx A1 M1 model1 (set_tr c (B1 ++ [])) R2 (-4) _ 0x12b18 22 22 _ B1 []);
      [exact PS | exact X1 | reflexivity | exact BUD1 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS1 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | apply ro_cstr_of_chk; vm_compute; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A2 R2c M2 model2 B2 X2 BUD2 KEPT _ DS2 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    eapply (cellw_frame _ M2) in Cio; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M2) in Ciwc; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M2) in Fdm; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (loop_mem_frame w _ M2) in LM; [| lia | lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X1 BUD1 DS1. pose proof (x_ms X2) as MS2.
    pm_seed R2c w (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) [Z_to_bv 64 (i_d I mod 2 ^ 64)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R2c. seedHK HK w A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) E X2.
    apply (know_more E M2 [KWord (SA (EVar 32) 208) (N.to_nat 8) (EVar 39)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         - eapply kword_var; [exact Fdm | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity]. }
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R3.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    rewrite <- (LibMaskBits.Z_to_bv_mod64 (i_d I)) in G10.
    eapply (pm_idesc_name w A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) fx R3 _ K X2 (ex_intro _ (i_d I) (ex_intro _ (i_op I) (conj Hdesc G10))) G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
    clear Qsp Qs0 Qgp Qtp. intros R3n KEPT (pnm & nnm & ROnm & Hn256 & Gnm).
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    clear G1 G2 G3 G4 G8 G10 KEPT; try clear G9; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    pose proof ROnm as RO'. destruct RO' as (Rp1 & Rn0 & Rp2 & _).
    pm_seed R3n w (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) [Z_to_bv 64 pnm].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, EVar 39)] R3n. seedHK HK w A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) E X2.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R4.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (21%bv) G21.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    try replace (Z_to_bv 5 (Z.of_N 21)) with (21%bv : reg) in * by (apply bv_eq; reflexivity). rename G21 into Q21p.
    eapply (pm_strlen w A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) fx R4 _ K X2 (ex_intro _ pnm (ex_intro _ nnm (conj ROnm G10))) G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
    clear Qsp Qs0 Qgp Qtp. intros R4s KEPT POst. pose proof (POst pnm nnm ROnm G10) as Gsl. clear POst.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp. keptQ KEPT Q21p Q21p_. clear Q21p. rename Q21p_ into Q21p.
    clear G1 G2 G3 G4 G8 G10 KEPT; try clear G9; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    pm_seed R4s w (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) [Z_to_bv 64 nnm; Z_to_bv 64 pnm].
    seedHR HR E HTitDiagS1_0 R4s. seedHK HK w A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) E X2.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R5.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_put_cstr w c0 K fx A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) R5 (-4) _ pnm nnm nnm _ B2 []);
      [exact PS | exact X2 | reflexivity | exact BUD2 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS2 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | exact ROnm | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A5 R5c M5 model5 B5 X5 BUD5 KEPT _ DS5 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    eapply (cellw_frame _ M5) in Cio; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M5) in Ciwc; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M5) in Fdm; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (loop_mem_frame w _ M5) in LM; [| lia | lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X4 BUD4 DS4. pose proof (x_ms X5) as MS5.
    pm_seed R5c w (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R5c. seedHK HK w A5 M5 model5 (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) E X5.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R6.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite w_add in G10 by lia.
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
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X5 BUD5 DS5. pose proof (x_ms X6) as MS6.
    pm_seed R6c w (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) [Z_to_bv 64 (i_io I)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R6c. seedHK HK w A6 M6 model6 (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) E X6.
    apply (know_more E M6 [KWord (SA (EVar 32) 200) (N.to_nat 8) (EVar 39)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         - eapply kword_var; [exact Cio | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity]. }
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R7.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_put_u64 w c0 K fx A6 M6 model6 (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) R7 (-4) _ (i_io I) _ B6 []);
      [exact PS | exact X6 | reflexivity | exact BUD6 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS6 | cregs_tac G1 G2 G3 G4
      | exact G10 | rewrite G11; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A7 R7c M7 model7 B7 X7 BUD7 KEPT _ DS7 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    eapply (cellw_frame _ M7) in Cio; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M7) in Ciwc; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M7) in Fdm; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (loop_mem_frame w _ M7) in LM; [| lia | lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X6 BUD6 DS6. pose proof (x_ms X7) as MS7.
    pm_seed R7c w (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R7c. seedHK HK w A7 M7 model7 (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) E X7.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R8.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite w_add in G10 by lia.
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
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X7 BUD7 DS7. pose proof (x_ms X8) as MS8.
    pm_seed R8c w (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) [Z_to_bv 64 (i_iwc I)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R8c. seedHK HK w A8 M8 model8 (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) E X8.
    apply (know_more E M8 [KWord (SA (EVar 32) 218) (N.to_nat 2) (EVar 39)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         - eapply kword_var; [exact Ciwc | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity]. }
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R9.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite w_add in G10 by lia.
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
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X8 BUD8 DS8. pose proof (x_ms X9) as MS9.
    pm_seed R9c w (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) (B9 ++ [])) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R9c. seedHK HK w A9 M9 model9 (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) (B9 ++ [])) E X9.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R10.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite w_add in G10 by lia.
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
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X9 BUD9 DS9. pose proof (x_ms X10) as MS10.
    clear Cwi. pose proof (fld_cellw M10 _ 8 _ (x_widx X10) ltac:(cbn [c_widx set_tr]; lia)) as Cwi. unfold O_WIDX in Cwi. cbn [c_widx set_tr] in Cwi.
    pm_seed R10c w (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) (B9 ++ [])) (B10 ++ [])) [Z_to_bv 64 (i_io I)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R10c. seedHK HK w A10 M10 model10 (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) (B9 ++ [])) (B10 ++ [])) E X10.
    apply (know_more E M10 [KWord (SA (EVar 33) 72) (N.to_nat 8) (EVar 38); KWord (SA (EVar 32) 200) (N.to_nat 8) (EVar 39)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         - eapply kword_var; [exact Cwi | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply kword_var; [exact Cio | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity]. }
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R11.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    rewrite ?w_mul_lit, ?SymExec.alu64_add_lit, ?SymExec.alu64_sub_lit in G11. cbn [c_widx set_tr] in G11. try replace (c_widx c + -1 * i_io I) with (c_widx c - i_io I) in G11 by lia.
    eapply (pm_put_u64 w c0 K fx A10 M10 model10 (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) (B9 ++ [])) (B10 ++ [])) R11 (-4) _ (c_widx c - i_io I) _ B10 []);
      [exact PS | exact X10 | reflexivity | exact BUD10 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS10 | cregs_tac G1 G2 G3 G4
      | exact G10 | rewrite G11; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A11 R11c M11 model11 B11 X11 BUD11 KEPT _ DS11 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    eapply (cellw_frame _ M11) in Cio; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M11) in Ciwc; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M11) in Fdm; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (loop_mem_frame w _ M11) in LM; [| lia | lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X10 BUD10 DS10. pose proof (x_ms X11) as MS11.
    pm_seed R11c w (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) (B9 ++ [])) (B10 ++ [])) (B11 ++ [])) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R11c. seedHK HK w A11 M11 model11 (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) (B9 ++ [])) (B10 ++ [])) (B11 ++ [])) E X11.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R12.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite w_add in G10 by lia.
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
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X11 BUD11 DS11. pose proof (x_ms X12) as MS12.
    pose proof (dl_err _ _ _ _ _ _ DL _ _ _ _ _ _ DS12) as Herrc. unfold CRep.fld in Herrc.
    assert (Cerr : cell4 SEGS M12 (w_sp w + 272 + 360) ((-4) mod 2 ^ 32)).
    { split; [pose proof (Z.mod_pos_bound (-4) (2 ^ 32)); cbn; lia | exact Herrc]. }
    pm_seed R12c w (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) (B9 ++ [])) (B10 ++ [])) (B11 ++ [])) (B12 ++ [])) [sxw ((-4) mod 2 ^ 32)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R12c. seedHK HK w A12 M12 model12 (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) (B9 ++ [])) (B10 ++ [])) (B11 ++ [])) (B12 ++ [])) E X12.
    xruns HR HK 100%nat STOPS (SCR [] [EVar 39] []) 50%N. { split_scs; try sc_auto1. all: sc_rd_sx Cerr. }
    postrun. name_run HRn R12cd. rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (10%bv) G10. rreg HRn (26%bv) G26.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4. rewrite w_add in G10 by lia.
    eapply (pm_dtor w c0 K fx A12 M12 model12 (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) (B9 ++ [])) (B10 ++ [])) (B11 ++ [])) (B12 ++ [])) R12cd (-4) _ _ B12 []);
      [exact PS | exact X12 | cbn [c_tr set_tr]; rewrite ?app_nil_r; reflexivity | exact BUD12 | rewrite Zlength_nil; lia | exact DS12 | cregs_tac G1 G2 G3 G4 | exact G10 |].
    intros Ad Rd Md modeld Xd BUDd KEPT AGd.
    keptQ KEPT G2 Qsp'. keptQ KEPT G3 Qgp'. keptQ KEPT G4 Qtp'. keptQ KEPT G26 Qs10.
    pose proof (Z.mod_pos_bound (-4) (2 ^ 32) ltac:(lia)) as Hm.
    assert (Hnz : (-4) mod 2 ^ 32 <> 0) by (rewrite <- (Z.mod_add (-4) 1 (2 ^ 32)) by lia; rewrite Z.mod_small by lia; lia).
    pose proof (x_ms Xd) as MSd.
    try clear E. pm_seed Rd w (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) (B9 ++ [])) (B10 ++ [])) (B11 ++ [])) (B12 ++ [])) []) [sxw ((-4) mod 2 ^ 32)].
    seedHR HR E [(2%bv, EVar 32); (26%bv, EVar 39)] Rd. seedHK HK w Ad Md modeld (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) (B9 ++ [])) (B10 ++ [])) (B11 ++ [])) (B12 ++ [])) []) E Xd.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn Re. rreg HRn (2%bv) T2. rreg HRn (3%bv) T3. rreg HRn (4%bv) T4. rreg HRn (26%bv) T26.
    clear HRn HR HK. fixregs. rewrite Qgp' in T3. rewrite Qtp' in T4.
    eapply (PmLoopS1.pm_latch_err w c0 K fx Ad Md modeld (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) (B9 ++ [])) (B10 ++ [])) (B11 ++ [])) (B12 ++ [])) []) Re ((-4) mod 2 ^ 32) PS Xd ltac:(cbn [c_tr set_tr]; reflexivity) BUDd FZ T2 T3 T4 T26 ltac:(lia)).
  Qed.
End PM.
