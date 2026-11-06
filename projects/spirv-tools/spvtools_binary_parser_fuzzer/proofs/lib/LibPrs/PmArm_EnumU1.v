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
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep2U1.PmUpdU1. From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PmStep2U1 PmLoopU1 PmInstU1 PmStep3U1 PmZw PmODefsU1 PmStep4U1 PmDispatchU1 PmArm_SpecU1.
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

  Ltac inl := first [ solve [cbn [In]; repeat (first [left; reflexivity | right])] | cbn; repeat (first [left; reflexivity | right]) ].

  Lemma sxw_small' : forall v, 0 <= v < 2 ^ 31 -> sxw v = Z_to_bv 64 v.
  Proof using. intros v Hv. unfold sxw. rewrite bv_swrap32_cases by lia. destruct (Z.ltb_spec v (2 ^ 31)); [reflexivity | lia]. Qed.

  Lemma OBASE_frame : forall (w : pmw MI ST) (I : ictxR) A M M1 model c R R1 (lo hi : Z),
    OBASE w I A M model c R -> stores_in (zwin (w_sp w + lo) (w_sp w + hi)) M M1 -> 280 <= lo -> lo <= hi -> hi <= 760 ->
    oregs w R1 -> OBASE w I A M1 model c R1.
  Proof using AC MI ST.
    intros w I A M M1 model c R R1 lo hi OB STI Hlo Hlh Hhi OR1.
    destruct OB as (X & Htr & BUD & OR & LM & IC & FR & Hic & Hend & Hwnz & MAC & V3R).
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & Gc2 & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    assert (X1 : PMX w A M1 model c).
    { eapply (pmx_frame_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img w A M M1 model c (zwin (w_sp w + lo) (w_sp w + hi)));
        [exact X | exact STI | unfold zwin, w_sp0, PM_FRAME; intros; lia]. }
    assert (AG1 : CRep.agree_on (fun a => w_sp w <= a < w_sp w + 864 /\ ~ zwin (w_sp w + lo) (w_sp w + hi) a) M M1).
    { eapply stores_in_agree; [exact STI | intros b Hb; unfold zwin in *; lia]. }
    split; [exact X1|]. split; [exact Htr|]. split; [exact BUD|]. split; [exact OR1|].
    split; [eapply (loop_mem_frame w M M1); [exact LM | lia | lia | eapply agree_on_weaken; [exact AG1 | unfold zwin; cbn; intros; lia]]|].
    split; [eapply (ictx_agree w M M1); [exact IC | lia | lia | eapply agree_on_weaken; [exact AG1 | unfold zwin; cbn; intros; lia]]|].
    split; [eapply (ifr_agree w M M1); [exact FR | lia | lia | eapply agree_on_weaken; [exact AG1 | unfold zwin; cbn; intros; lia]]|].
    split; [exact Hic|]. split; [exact Hend|]. split; [exact Hwnz|]. split; [exact MAC | exact V3R].
  Qed.
  Lemma OBASE_regs : forall (w : pmw MI ST) (I : ictxR) A M model c R R1,
    OBASE w I A M model c R -> oregs w R1 -> OBASE w I A M model c R1.
  Proof using AC MI ST.
    intros w I A M model c R R1 OB OR1. destruct OB as (X & Htr & BUD & OR & rest).
    split; [exact X|]. split; [exact Htr|]. split; [exact BUD|]. split; [exact OR1 | exact rest].
  Qed.

  Lemma enum_diag : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R (wv et : Z),
    PMS w c0 K -> frm_zero (@fp_csr fx) -> CHECKK w K fx -> PMX w A M model c -> c_tr c = [] -> pm_bud (w_n w) c ->
    getr R 2%bv = Z_to_bv 64 (w_sp w) -> getr R 3%bv = Z_to_bv 64 (ly_gp Ly.L) -> getr R 4%bv = Z_to_bv 64 (ly_tp Ly.L) ->
    getr R 8%bv = Z_to_bv 64 (w_p w) ->
    cellw SEGS M (w_sp w + 712) 4 wv -> cellw SEGS M (w_sp w + 720) 4 et -> 0 <= et < 2 ^ 31 ->
    srealizes SEGS (cfg fx R 0x67964 M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx A M model c R wv et PS FZ CK X Htr BUD Qsp Qgp Qtp Qs0 C712 C720 Het.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (x_scal X) as (Sc1 & Sc2 & Sc3 & Sc4).
    pose proof (proj1 C712) as Hwv. cbn in Hwv. assert (Het32 : 0 <= et < 2 ^ 32) by lia.
    pm_seed R w c (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R. seedHK HK w A M model c E X.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R1.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_pdiagQ w c0 K fx A M model c R1 (-4) _ []);
      [exact PS | exact X | exact Htr | exact BUD | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | rewrite G12; apply bv_eq; vm_compute; reflexivity | lia |].
    clear Qsp Qs0 Qgp Qtp. intros A1 R1c M1 model1 B1 X1 BUD1 KEPT DS1 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    eapply (cellw_frame _ M1) in C712; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M1) in C720; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X0 BUD0. pose proof (x_ms X1) as MS1.
    pm_seed R1c w (set_tr c (B1 ++ [])) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R1c. seedHK HK w A1 M1 model1 (set_tr c (B1 ++ [])) E X1.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R2.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_put_cstr w c0 K fx A1 M1 model1 (set_tr c (B1 ++ [])) R2 (-4) _ 0x10556 8 8 _ B1 []);
      [exact PS | exact X1 | reflexivity | exact BUD1 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS1 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | apply ro_cstr_of_chk; vm_compute; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A2 R2c M2 model2 B2 X2 BUD2 KEPT _ DS2 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
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
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    rewrite ?ext_val_sx4, ?sx32_small in G10 by lia.
    assert (Hlit3 : 0 <= et < 2 ^ 32) by lia.
    eapply (pm_operand_type_str w A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) fx R3 _ K X2 (ex_intro _ et (conj Hlit3 G10)) G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
    clear Qsp Qs0 Qgp Qtp. intros R3n KEPT (pnm & nnm & ROnm & Hn256 & Gnm).
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    clear G1 G2 G3 G4 G8 G10 KEPT; try clear G9; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
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
    clear G1 G2 G3 G4 G8 G10 KEPT; try clear G9; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    pm_seed R4s w (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) [Z_to_bv 64 nnm; Z_to_bv 64 pnm].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, EVar 39); (22%bv, EVar 40)] R4s. seedHK HK w A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) E X2.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R5.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    clear Q22p.
    eapply (pm_put_cstr w c0 K fx A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) R5 (-4) _ pnm nnm nnm _ B2 []);
      [exact PS | exact X2 | reflexivity | exact BUD2 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS2 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | exact ROnm | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A5 R5c M5 model5 B5 X5 BUD5 KEPT _ DS5 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    eapply (cellw_frame _ M5) in C712; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M5) in C720; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X4 BUD4 DS4. pose proof (x_ms X5) as MS5.
    pm_seed R5c w (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R5c. seedHK HK w A5 M5 model5 (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) E X5.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R6.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_put_cstr w c0 K fx A5 M5 model5 (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) R6 (-4) _ 0x126ed 10 10 _ B5 []);
      [exact PS | exact X5 | reflexivity | exact BUD5 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS5 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | apply ro_cstr_of_chk; vm_compute; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A6 R6c M6 model6 B6 X6 BUD6 KEPT _ DS6 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    eapply (cellw_frame _ M6) in C712; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M6) in C720; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X5 BUD5 DS5. pose proof (x_ms X6) as MS6.
    pm_seed R6c w (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) [sxw wv].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R6c. seedHK HK w A6 M6 model6 (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) E X6.
    xruns HR HK 100%nat STOPS (SCR [] [EVar 39] []) 50%N. { split_scs; try sc_auto1. all: sc_rd_sx C712. }
    postrun. name_run HRn R7.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_put_u32 w c0 K fx A6 M6 model6 (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) R7 (-4) _ (wv) _ B6 []);
      [exact PS | exact X6 | reflexivity | exact BUD6 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS6 | cregs_tac G1 G2 G3 G4
      | exact G10 | rewrite G11; apply sxw_sx32; lia | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A7 R7c M7 model7 B7 X7 BUD7 KEPT _ DS7 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    eapply (cellw_frame _ M7) in C712; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M7) in C720; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X6 BUD6 DS6. pose proof (x_ms X7) as MS7.
    pose proof (dl_err _ _ _ _ _ _ DL _ _ _ _ _ _ DS7) as Herrc. unfold CRep.fld in Herrc.
    assert (Cerr : cell4 SEGS M7 (w_sp w + 304 + 360) ((-4) mod 2 ^ 32)).
    { split; [pose proof (Z.mod_pos_bound (-4) (2 ^ 32)); cbn; lia | exact Herrc]. }
    pm_seed R7c w (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) [sxw ((-4) mod 2 ^ 32)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R7c. seedHK HK w A7 M7 model7 (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) E X7.
    xruns HR HK 100%nat STOPS (SCR [] [EVar 39] []) 50%N. { split_scs; try sc_auto1. all: sc_rd_sx Cerr. }
    postrun. name_run HRn R7cd. rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (22%bv) G22.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.  rewrite w_add in G10 by lia.
    eapply (pm_dtor w c0 K fx A7 M7 model7 (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) R7cd (-4) _ _ B7 []);
      [exact PS | exact X7 | cbn [c_tr set_tr]; rewrite ?app_nil_r; reflexivity | exact BUD7 | rewrite Zlength_nil; lia | exact DS7 | cregs_tac G1 G2 G3 G4 | exact G10 |].
    intros Ad Rd Md modeld Xd BUDd KEPT AGd.
    keptQ KEPT G2 Qsp'. keptQ KEPT G3 Qgp'. keptQ KEPT G4 Qtp'. keptQ KEPT G8 Qs0'. keptQ KEPT G22 Qs6.
    pose proof (Z.mod_pos_bound (-4) (2 ^ 32) ltac:(lia)) as Hm'.
    assert (Hnz : (-4) mod 2 ^ 32 <> 0) by (rewrite <- (Z.mod_add (-4) 1 (2 ^ 32)) by lia; rewrite Z.mod_small by lia; lia).
    pose proof (x_ms Xd) as MSd.
    try clear E. pm_seed Rd w (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) []) [sxw ((-4) mod 2 ^ 32)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (22%bv, EVar 39)] Rd. seedHK HK w Ad Md modeld (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) []) E Xd.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn Re. rreg HRn (2%bv) T2. rreg HRn (3%bv) T3. rreg HRn (4%bv) T4. rreg HRn (8%bv) T8. rreg HRn (22%bv) T22.
    clear HRn HR HK. fixregs. rewrite Qgp' in T3. rewrite Qtp' in T4.
    eapply (CK Ad Md modeld (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) []) Re ((-4) mod 2 ^ 32) Xd ltac:(cbn [c_tr set_tr]; reflexivity) BUDd T2 T3 T4 T8 T22 ltac:(lia)).
  Qed.

  Lemma srclang_diag : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R (wv et : Z),
    PMS w c0 K -> frm_zero (@fp_csr fx) -> CHECKK w K fx -> PMX w A M model c -> c_tr c = [] -> pm_bud (w_n w) c ->
    getr R 2%bv = Z_to_bv 64 (w_sp w) -> getr R 3%bv = Z_to_bv 64 (ly_gp Ly.L) -> getr R 4%bv = Z_to_bv 64 (ly_tp Ly.L) ->
    getr R 8%bv = Z_to_bv 64 (w_p w) ->
    cellw SEGS M (w_sp w + 712) 4 wv -> cellw SEGS M (w_sp w + 720) 4 et -> 0 <= et < 2 ^ 31 ->
    srealizes SEGS (cfg fx R 0x67eac M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx A M model c R wv et PS FZ CK X Htr BUD Qsp Qgp Qtp Qs0 C712 C720 Het.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (x_scal X) as (Sc1 & Sc2 & Sc3 & Sc4).
    pose proof (proj1 C712) as Hwv. cbn in Hwv. assert (Het32 : 0 <= et < 2 ^ 32) by lia.
    pm_seed R w c (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R. seedHK HK w A M model c E X.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R1.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_pdiagQ w c0 K fx A M model c R1 (-4) _ []);
      [exact PS | exact X | exact Htr | exact BUD | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | rewrite G12; apply bv_eq; vm_compute; reflexivity | lia |].
    clear Qsp Qs0 Qgp Qtp. intros A1 R1c M1 model1 B1 X1 BUD1 KEPT DS1 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    eapply (cellw_frame _ M1) in C712; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M1) in C720; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X0 BUD0. pose proof (x_ms X1) as MS1.
    pm_seed R1c w (set_tr c (B1 ++ [])) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R1c. seedHK HK w A1 M1 model1 (set_tr c (B1 ++ [])) E X1.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R2.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_put_cstr w c0 K fx A1 M1 model1 (set_tr c (B1 ++ [])) R2 (-4) _ 0x10556 8 8 _ B1 []);
      [exact PS | exact X1 | reflexivity | exact BUD1 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS1 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | apply ro_cstr_of_chk; vm_compute; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A2 R2c M2 model2 B2 X2 BUD2 KEPT _ DS2 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
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
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    rewrite ?ext_val_sx4, ?sx32_small in G10 by lia.
    assert (Hlit3 : 0 <= et < 2 ^ 32) by lia.
    eapply (pm_operand_type_str w A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) fx R3 _ K X2 (ex_intro _ et (conj Hlit3 G10)) G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
    clear Qsp Qs0 Qgp Qtp. intros R3n KEPT (pnm & nnm & ROnm & Hn256 & Gnm).
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    clear G1 G2 G3 G4 G8 G10 KEPT; try clear G9; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
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
    clear G1 G2 G3 G4 G8 G10 KEPT; try clear G9; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    pm_seed R4s w (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) [Z_to_bv 64 nnm; Z_to_bv 64 pnm].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, EVar 39); (22%bv, EVar 40)] R4s. seedHK HK w A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) E X2.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R5.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    clear Q22p.
    eapply (pm_put_cstr w c0 K fx A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) R5 (-4) _ pnm nnm nnm _ B2 []);
      [exact PS | exact X2 | reflexivity | exact BUD2 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS2 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | exact ROnm | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A5 R5c M5 model5 B5 X5 BUD5 KEPT _ DS5 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    eapply (cellw_frame _ M5) in C712; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M5) in C720; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X4 BUD4 DS4. pose proof (x_ms X5) as MS5.
    pm_seed R5c w (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R5c. seedHK HK w A5 M5 model5 (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) E X5.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R6.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_put_cstr w c0 K fx A5 M5 model5 (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) R6 (-4) _ 0x126ed 10 10 _ B5 []);
      [exact PS | exact X5 | reflexivity | exact BUD5 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS5 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | apply ro_cstr_of_chk; vm_compute; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A6 R6c M6 model6 B6 X6 BUD6 KEPT _ DS6 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    eapply (cellw_frame _ M6) in C712; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M6) in C720; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X5 BUD5 DS5. pose proof (x_ms X6) as MS6.
    pm_seed R6c w (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) [sxw wv].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R6c. seedHK HK w A6 M6 model6 (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) E X6.
    xruns HR HK 100%nat STOPS (SCR [] [EVar 39] []) 50%N. { split_scs; try sc_auto1. all: sc_rd_sx C712. }
    postrun. name_run HRn R7.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_put_u32 w c0 K fx A6 M6 model6 (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) R7 (-4) _ (wv) _ B6 []);
      [exact PS | exact X6 | reflexivity | exact BUD6 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS6 | cregs_tac G1 G2 G3 G4
      | exact G10 | rewrite G11; apply sxw_sx32; lia | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A7 R7c M7 model7 B7 X7 BUD7 KEPT _ DS7 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    eapply (cellw_frame _ M7) in C712; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    eapply (cellw_frame _ M7) in C720; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X6 BUD6 DS6. pose proof (x_ms X7) as MS7.
    pm_seed R7c w (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R7c. seedHK HK w A7 M7 model7 (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) E X7.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R8.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_put_cstr w c0 K fx A7 M7 model7 (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) R8 (-4) _ 0x11271 130 130 _ B7 []);
      [exact PS | exact X7 | reflexivity | exact BUD7 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS7 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | apply ro_cstr_of_chk; vm_compute; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A8 R8c M8 model8 B8 X8 BUD8 KEPT _ DS8 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X7 BUD7 DS7. pose proof (x_ms X8) as MS8.
    pose proof (dl_err _ _ _ _ _ _ DL _ _ _ _ _ _ DS8) as Herrc. unfold CRep.fld in Herrc.
    assert (Cerr : cell4 SEGS M8 (w_sp w + 304 + 360) ((-4) mod 2 ^ 32)).
    { split; [pose proof (Z.mod_pos_bound (-4) (2 ^ 32)); cbn; lia | exact Herrc]. }
    pm_seed R8c w (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) [sxw ((-4) mod 2 ^ 32)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R8c. seedHK HK w A8 M8 model8 (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) E X8.
    xruns HR HK 100%nat STOPS (SCR [] [EVar 39] []) 50%N. { split_scs; try sc_auto1. all: sc_rd_sx Cerr. }
    postrun. name_run HRn R8cd. rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (22%bv) G22.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.  rewrite w_add in G10 by lia.
    eapply (pm_dtor w c0 K fx A8 M8 model8 (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) R8cd (-4) _ _ B8 []);
      [exact PS | exact X8 | cbn [c_tr set_tr]; rewrite ?app_nil_r; reflexivity | exact BUD8 | rewrite Zlength_nil; lia | exact DS8 | cregs_tac G1 G2 G3 G4 | exact G10 |].
    intros Ad Rd Md modeld Xd BUDd KEPT AGd.
    keptQ KEPT G2 Qsp'. keptQ KEPT G3 Qgp'. keptQ KEPT G4 Qtp'. keptQ KEPT G8 Qs0'. keptQ KEPT G22 Qs6.
    pose proof (Z.mod_pos_bound (-4) (2 ^ 32) ltac:(lia)) as Hm'.
    assert (Hnz : (-4) mod 2 ^ 32 <> 0) by (rewrite <- (Z.mod_add (-4) 1 (2 ^ 32)) by lia; rewrite Z.mod_small by lia; lia).
    pose proof (x_ms Xd) as MSd.
    try clear E. pm_seed Rd w (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) []) [sxw ((-4) mod 2 ^ 32)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (22%bv, EVar 39)] Rd. seedHK HK w Ad Md modeld (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) []) E Xd.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn Re. rreg HRn (2%bv) T2. rreg HRn (3%bv) T3. rreg HRn (4%bv) T4. rreg HRn (8%bv) T8. rreg HRn (22%bv) T22.
    clear HRn HR HK. fixregs. rewrite Qgp' in T3. rewrite Qtp' in T4.
    eapply (CK Ad Md modeld (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B5 ++ [])) (B6 ++ [])) (B7 ++ [])) (B8 ++ [])) []) Re ((-4) mod 2 ^ 32) Xd ltac:(cbn [c_tr set_tr]; reflexivity) BUDd T2 T3 T4 T8 T22 ltac:(lia)).
  Qed.

  Lemma enum_tail : forall (w : pmw MI ST) c0 K (fx : FPState) (I : ictxR) A M model c R (t wv et : Z),
    PMS w c0 K -> frm_zero (@fp_csr fx) -> CHECKK w K fx -> PUSHK w I K fx c t ->
    OBASE w I A M model c R ->
    getr R 22%bv = sxw wv -> 0 <= wv < 2 ^ 32 -> getr R 27%bv = Z_to_bv 64 t -> 0 <= t < 2 ^ 31 ->
    getr R 23%bv = Z_to_bv 64 (i_io I) -> getr R 26%bv = Z_to_bv 64 (i_op I) ->
    cellw SEGS M (w_sp w + 712) 4 wv -> cellw SEGS M (w_sp w + 720) 4 et -> 0 <= et < 2 ^ 31 ->
    cellw SEGS M (w_sp w + 718) 2 1 -> Zlen (t3b (c_v3 c)) + g_maxlen G <= V3MAX ->
    t <> OT_RESULT_ID /\ t <> OT_LITERAL_INTEGER /\ t <> OT_LITERAL_STRING ->
    srealizes SEGS (cfg fx R 0x67934 M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx I A M model c R t wv et PS FZ CK PK OB Q22 Hword Q27 Ht Q23 Q26 C712 C720 Het C718 Hmax Ht36.
    pose proof OB as OB'. destruct OB' as (X & Htr & BUD & OR & LM & IC & FR & Hic & Hend & Hwnz & MAC & V3R).
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof OR as OR'. destruct OR' as (Qsp & Qgp & Qtp & Qs0 & Qs1 & Qs2 & Qs3 & Qs4 & Qs5 & Qs9).

    pm_seed R w c [Z_to_bv 64 t; sxw wv].
    seedHR HR E ([(2%bv, EVar 32); (8%bv, EVar 33); (27%bv, EVar 39); (22%bv, EVar 40)] ++ OREGSEED)%list R. seedHK HK w A M model c E X.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R1.
    rreg HRn (1%bv) G1. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12. rreg HRn (27%bv) G27.
    pose proof (syms_id_sound _ _ _ _ [23; 24; 26]%bv HRn eq_refl) as GK1.
    assert (OR1 : oregs w R1) by (oregs_seeded HRn Qgp Qtp).
    pose proof OR1 as OR'. destruct OR' as (G2 & G3 & G4 & G8 & _). clear HRn HR HK.
    rewrite ?SymExec.alu64_add_lit in G12. rewrite ?w_add in G12 by lia.
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M1 := m) in * end.
    assert (ST1 : stores_in (zwin (w_sp w + 280) (w_sp w + 288)) M M1) by (unfold M1; stin).
    assert (X1 : PMX w A M1 model c).
    { eapply (pmx_frame_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img w A M M1 model c (zwin (w_sp w + 280) (w_sp w + 288)));
        [exact X | exact ST1 | unfold zwin, w_sp0, PM_FRAME; intros; lia]. }
    pose proof (x_ms X1) as MS1.
    eapply (pm_lookup_operand w A M1 model c fx R1 t wv (w_sp w + 280) _ K X1 G10 ltac:(lia) ltac:(intros HH; discriminate HH)
              ltac:(intros _; split; [rewrite G11; apply sxw_sx32; lia | split; [lia | exact G12]]) G2 ltac:(lia) ltac:(unfold w_sp0, PM_FRAME; lia)
              ltac:(apply mod16_8; [exact Gsp16 | reflexivity]) G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
    intros R2 M2 r d KEPT Hr Rr Fd Hfound Hhnd X2 AG.
    keptQ KEPT G2 Qsp2. keptQ KEPT G8 Qs02. keptQ KEPT G3 Qgp2. keptQ KEPT G4 Qtp2. keptQ KEPT G27 Q27b.
    pose proof (oregs_kept w R1 R2 OR1 KEPT) as OR2.
    assert (GK2 : forall r', In r' [23; 24; 26]%bv -> getr R2 r' = getr R r').
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
    assert (C712' : cellw SEGS M2 (w_sp w + 712) 4 wv).
    { eapply (cellw_frame M M2); [exact C712 | lia | cbn; lia | eapply agree_on_weaken; [exact AG02 | unfold zwin; cbn; intros; lia]]. }
    assert (C720' : cellw SEGS M2 (w_sp w + 720) 4 et).
    { eapply (cellw_frame M M2); [exact C720 | lia | cbn; lia | eapply agree_on_weaken; [exact AG02 | unfold zwin; cbn; intros; lia]]. }
    clear ST1 X X1 MS MS1 AG C718 C712 C720. clearbody M1. clear M1.
    pose proof OR2 as OR'. destruct OR' as (_ & _ & _ & _ & Ps1 & Ps2 & Ps3 & Ps4 & Ps5 & Ps9).

    destruct (Z.eq_dec r 0) as [Hr0 | Hr1].
    -
      subst r. specialize (Hhnd eq_refl). cbn beta in Hhnd.
      pose proof (ODESC_PTR d t wv Hhnd) as (Hd1 & Hd2 & Hd4).
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
      eapply (pm_opnd_push w c0 K fx I A M2 model c R3 d t wv PS (OB2 R3 OR3) Hhnd G10 Hmax).
      intros A' M' model' R' b' cap' l l' Hg El' SF' Hlen' OB' GK' AG'.
      pose proof (go_len_operand G GOK t wv l Hg) as Hll. unfold HRep.Zlength in Hll. change (Zlen l <= g_maxlen G) in Hll.
      pose proof MAXLEN as Hml.
      eapply (PK A' M' model' _ R' 1 l' OB').
      + rewrite (GK' 27%bv ltac:(clear; inl)), (GK3 27%bv ltac:(clear; inl)). exact Q27b.
      + rewrite (GK' 23%bv ltac:(clear; inl)), (GK3 23%bv ltac:(clear; inl)), (GK2 23%bv ltac:(clear; inl)). exact Q23.
      + rewrite (GK' 26%bv ltac:(clear; inl)), (GK3 26%bv ltac:(clear; inl)), (GK2 26%bv ltac:(clear; inl)). exact Q26.
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
      apply (know_more E M2 [KRange (EVar 39) 1 (2 ^ 64 - 1); KWord (SA (EVar 33) 40) (N.to_nat 1) (ELit 0)]) in HK.
      2: { repeat apply Forall_cons; try apply Forall_nil.
           - eapply krange_var; [evs; reflexivity | lia | lia].
           - eapply kword_var; [eapply fld_cellw; [exact (x_hunk X2) | cbn; lia] | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | cbn [edenot]; reflexivity]. }
      xruns HR HK 100%nat (0x67964 :: STOPS) (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
      postrun. name_run HRn R3.
      rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8.
      clear HRn HR HK. fixregs. rewrite Qgp2 in G3. rewrite Qtp2 in G4.
      exact (enum_diag w c0 K fx A M2 model c R3 wv et PS FZ CK X2 Htr BUD G2 G3 G4 G8 C712' C720' Het).
  Qed.

  Definition ENUM_TYPES : list Z := [13; 14; 15; 16; 17; 18; 19; 20; 21; 24; 25; 26; 27; 28; 29; 30; 31; 32; 33; 34; 49; 51; 57; 58; 59; 60; 62; 63; 64; 65; 66; 67; 68; 69; 70; 71; 72; 73; 74; 75; 76; 82; 83; 84; 85; 105; 107].

  Lemma in_enum_types : forall t, existsb (Z.eqb t) ENUM_TYPES = true -> In t ENUM_TYPES.
  Proof using.
    intros t. generalize ENUM_TYPES. induction l as [|x l IH]; cbn; [discriminate|]. intros H. apply Bool.orb_true_iff in H.
    destruct H as [H|H]; [left; symmetry; apply Z.eqb_eq; exact H | right; apply IH; exact H].
  Qed.

  Definition enum_et (t : Z) : Z := if t =? 49 then 26 else if t =? 76 then 75 else if t =? 51 then 34 else if t =? 105 then 33 else t.

  #[local] Ltac arm_intro :=
    intros w c0 K fx I A M model c R wv PS FZ FC IP HAE PK CK AACC; specialize (PK fx FZ FC); specialize (CK fx FZ FC);
    pose proof (AE_facts w I A M model c R _ wv IP HAE) as (_ & _ & Hoff & V3B & _ & _);
    destruct HAE as (OB & Hw1 & Hw2 & Hn & Hv1 & Hv2 & Hlen & Ht31 & Hword & Q22 & Q27 & Q24 & Q23 & Q26 & PO & C712);
    pose proof OB as OB'; destruct OB' as (X & Htr & BUD & OR & LM & IC & FR & Hic & Hend & Hwnz & MAC & V3R);
    pose proof (x_geo X) as GEO; pose proof ac_bounds_lit as Hcv; pose proof (x_ms X) as MS;
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw); unfold w_sp0, PM_FRAME, PARSER_SIZE in *;
    pose proof OR as OR'; destruct OR' as (Qsp & Qgp & Qtp & Qs0 & Qs1 & Qs2 & Qs3 & Qs4 & Qs5 & Qs9);
    destruct PO as (_ & C718 & C720 & _).

  Ltac enum_remap tv w c A M model I R X OB C712 C718 Qgp Qtp Q22' Q23 Q26 TAIL :=
    let E := fresh "E" in let HR := fresh "HR" in let HK := fresh "HK" in
    pm_seed R w c (@nil word);
    seedHR HR E ([(2%bv, EVar 32); (8%bv, EVar 33); (27%bv, ELit tv)] ++ OREGSEED)%list R; seedHK HK w A M model c E X;
    xruns HR HK 100%nat (0x67934 :: STOPS) (SCR [] [] []) 50%N; [split_scs; try sc_auto1 |];
    postrun;
    let HRn := fresh "HRn" in let R1 := fresh "R1" in
    name_run HRn R1;
    let G27 := fresh "G27" in let GK1 := fresh "GK1" in let OR1 := fresh "OR1" in
    rreg HRn (27%bv) G27;
    pose proof (syms_id_sound _ _ _ _ [22; 23; 26]%bv HRn eq_refl) as GK1;
    assert (OR1 : oregs w R1) by (oregs_seeded HRn Qgp Qtp); clear HRn HR HK;
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ =>
      let M1 := fresh "M1" in let ST1 := fresh "ST1" in let OB1 := fresh "OB1" in
      let C712' := fresh "C712'" in let C718' := fresh "C718'" in let C720' := fresh "C720'" in
      set (M1 := m) in *;
      assert (ST1 : stores_in (zwin (w_sp w + 720) (w_sp w + 724)) M M1) by (unfold M1; stin);
      pose proof (OBASE_frame w I A M M1 model c R R1 720 724 OB ST1 ltac:(lia) ltac:(lia) ltac:(lia) OR1) as OB1;
      assert (C712' : cellw SEGS M1 (w_sp w + 712) 4 _)
        by (eapply (cellw_frame M M1); [exact C712 | lia | cbn; lia | eapply stores_in_agree; [exact ST1 | unfold zwin; cbn; intros; lia]]);
      assert (C718' : cellw SEGS M1 (w_sp w + 718) 2 1)
        by (eapply (cellw_frame M M1); [exact C718 | lia | cbn; lia | eapply stores_in_agree; [exact ST1 | unfold zwin; cbn; intros; lia]]);
      let etv := eval cbv in (enum_et tv) in
      assert (C720' : cellw SEGS M1 (w_sp w + 720) 4 etv) by (split; [cbn; lia | unfold M1; change (N.to_nat 4) with 4%nat; rdback]);
      clear ST1; clearbody M1;
      apply (TAIL R1 M1 OB1); [ rewrite (GK1 22%bv) by (clear; inl); exact Q22' | exact G27
                              | rewrite (GK1 23%bv) by (clear; inl); exact Q23 | rewrite (GK1 26%bv) by (clear; inl); exact Q26
                              | exact C712' | exact C720' | exact C718' ]
    end.

  Theorem arm_ENUM_U1 : forall t, In t ENUM_TYPES -> arm_stmt t 0x678c0.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros t HIn. arm_intro.
    assert (Ht36 : t <> OT_RESULT_ID /\ t <> OT_LITERAL_INTEGER /\ t <> OT_LITERAL_STRING).
    { unfold ENUM_TYPES in HIn. cbn [In] in HIn. unfold OT_RESULT_ID, OT_LITERAL_INTEGER, OT_LITERAL_STRING. repeat split; intros ->; intuition lia. }
    pose proof MAXLEN as Hml. assert (Hmax : Zlen (t3b (c_v3 c)) + g_maxlen G <= V3MAX) by lia.
    assert (Q22' : getr R 22%bv = sxw wv) by (rewrite Q22; symmetry; apply sxw_sx32; lia).
    assert (TAIL : forall R1 M1, OBASE w I A M1 model c R1 -> getr R1 22%bv = sxw wv -> getr R1 27%bv = Z_to_bv 64 t ->
                   getr R1 23%bv = Z_to_bv 64 (i_io I) -> getr R1 26%bv = Z_to_bv 64 (i_op I) ->
                   cellw SEGS M1 (w_sp w + 712) 4 wv -> cellw SEGS M1 (w_sp w + 720) 4 (enum_et t) -> cellw SEGS M1 (w_sp w + 718) 2 1 ->
                   srealizes SEGS (cfg fx R1 0x67934 M1 model) K).
    { intros R1 M1 OB1 X22 X27 X23 X26 X712 X720 X718.
      eapply (enum_tail w c0 K fx I A M1 model c R1 t wv (enum_et t)); try eassumption.
      unfold enum_et. repeat match goal with |- context [?a =? ?b] => destruct (Z.eqb_spec a b) end; lia. }
    assert (Hcases : t = 49 \/ t = 76 \/ t = 51 \/ t = 105 \/ (t <> 49 /\ t <> 76 /\ t <> 51 /\ t <> 105)) by lia.
    clear HIn. destruct Hcases as [-> | [-> | [-> | [-> | (N49 & N76 & N51 & N105)]]]].
    -
      cbn [enum_et Z.eqb Pos.eqb] in TAIL. enum_remap 49 w c A M model I R X OB C712 C718 Qgp Qtp Q22' Q23 Q26 TAIL.
    -
      cbn [enum_et Z.eqb Pos.eqb] in TAIL. enum_remap 76 w c A M model I R X OB C712 C718 Qgp Qtp Q22' Q23 Q26 TAIL.
    -
      cbn [enum_et Z.eqb Pos.eqb] in TAIL. enum_remap 51 w c A M model I R X OB C712 C718 Qgp Qtp Q22' Q23 Q26 TAIL.
    -
      cbn [enum_et Z.eqb Pos.eqb] in TAIL. enum_remap 105 w c A M model I R X OB C712 C718 Qgp Qtp Q22' Q23 Q26 TAIL.
    -
      pm_seed R w c [Z_to_bv 64 t].
      seedHR HR E ([(2%bv, EVar 32); (8%bv, EVar 33); (27%bv, EVar 39)] ++ OREGSEED)%list R. seedHK HK w A M model c E X.
      apply (know_more E M [KRange (EVar 39) 0 (2 ^ 31 - 1)]) in HK.
      2: { repeat apply Forall_cons; try apply Forall_nil. eapply krange_var; [evs; reflexivity | lia | lia]. }
      xruns HR HK 100%nat (0x67934 :: STOPS) (SCR [false; true; false; true] [] []) 50%N.
      { split_scs; try sc_auto1; cbn [sc_denot]; evs; rewrite ?br_eq, ?br_ne by lia; bool_lia. }
      postrun. name_run HRn R1.
      rreg HRn (27%bv) G27.
      pose proof (syms_id_sound _ _ _ _ [22; 23; 26]%bv HRn eq_refl) as GK1.
      assert (OR1 : oregs w R1) by (oregs_seeded HRn Qgp Qtp). clear HRn HR HK.
      apply (TAIL R1 M (OBASE_regs w I A M model c R R1 OB OR1));
        [ rewrite (GK1 22%bv) by (clear; inl); exact Q22' | exact G27
        | rewrite (GK1 23%bv) by (clear; inl); exact Q23 | rewrite (GK1 26%bv) by (clear; inl); exact Q26
        | exact C712 | unfold enum_et; rewrite !(proj2 (Z.eqb_neq _ _)) by lia; exact C720 | exact C718 ].
  Qed.

  Theorem arm_SRCLANG_U1 : forall t, t = 12 -> arm_stmt t 0x67e7c.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros t Ht. arm_intro. subst t.
    assert (Ht36 : 12 <> OT_RESULT_ID /\ 12 <> OT_LITERAL_INTEGER /\ 12 <> OT_LITERAL_STRING) by (unfold OT_RESULT_ID, OT_LITERAL_INTEGER, OT_LITERAL_STRING; lia).
    pose proof MAXLEN as Hml. assert (Hmax : Zlen (t3b (c_v3 c)) + g_maxlen G <= V3MAX) by lia.
    assert (Q22' : getr R 22%bv = sxw wv) by (rewrite Q22; symmetry; apply sxw_sx32; lia).

    pm_seed R w c [sxw wv].
    seedHR HR E ([(2%bv, EVar 32); (8%bv, EVar 33); (22%bv, EVar 39)] ++ OREGSEED)%list R. seedHK HK w A M model c E X.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R1.
    rreg HRn (1%bv) G1. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    pose proof (syms_id_sound _ _ _ _ [23; 24; 26; 27]%bv HRn eq_refl) as GK1.
    assert (OR1 : oregs w R1) by (oregs_seeded HRn Qgp Qtp).
    pose proof OR1 as OR'. destruct OR' as (G2 & G3 & G4 & G8 & _). clear HRn HR HK.
    rewrite ?SymExec.alu64_add_lit in G12. rewrite ?w_add in G12 by lia.
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M1 := m) in * end.
    assert (ST1 : stores_in (zwin (w_sp w + 280) (w_sp w + 288)) M M1) by (unfold M1; stin).
    assert (X1 : PMX w A M1 model c).
    { eapply (pmx_frame_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img w A M M1 model c (zwin (w_sp w + 280) (w_sp w + 288)));
        [exact X | exact ST1 | unfold zwin, w_sp0, PM_FRAME; intros; lia]. }
    pose proof (x_ms X1) as MS1.
    eapply (pm_lookup_operand w A M1 model c fx R1 12 wv (w_sp w + 280) _ K X1 G10 ltac:(lia) ltac:(intros HH; discriminate HH)
              ltac:(intros _; split; [rewrite G11; apply sxw_sx32; lia | split; [lia | exact G12]]) G2 ltac:(lia) ltac:(unfold w_sp0, PM_FRAME; lia)
              ltac:(apply mod16_8; [exact Gsp16 | reflexivity]) G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
    intros R2 M2 r d KEPT Hr Rr Fd Hfound Hhnd X2 AG.
    keptQ KEPT G2 Qsp2. keptQ KEPT G8 Qs02. keptQ KEPT G3 Qgp2. keptQ KEPT G4 Qtp2.
    pose proof (oregs_kept w R1 R2 OR1 KEPT) as OR2.
    assert (GK2 : forall r', In r' [23; 24; 26; 27]%bv -> getr R2 r' = getr R r').
    { intros r' Hr'. rewrite (KEPT r') by (revert Hr'; clear; intros Hr'; apply in_reg_list; cbn in Hr'; decompose [or] Hr'; try contradiction; subst r'; reflexivity). apply GK1. exact Hr'. }
    clear G1 G2 G3 G4 G8 G10 G11 G12 GK1 OR1 KEPT.
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
    assert (C712' : cellw SEGS M2 (w_sp w + 712) 4 wv).
    { eapply (cellw_frame M M2); [exact C712 | lia | cbn; lia | eapply agree_on_weaken; [exact AG02 | unfold zwin; cbn; intros; lia]]. }
    assert (C720' : cellw SEGS M2 (w_sp w + 720) 4 12).
    { eapply (cellw_frame M M2); [exact C720 | lia | cbn; lia | eapply agree_on_weaken; [exact AG02 | unfold zwin; cbn; intros; lia]]. }
    clear ST1 X X1 MS MS1 AG C718 C712 C720. clearbody M1. clear M1.
    pose proof OR2 as OR'. destruct OR' as (_ & _ & _ & _ & Ps1 & Ps2 & Ps3 & Ps4 & Ps5 & Ps9).

    destruct (Z.eq_dec r 0) as [Hr0 | Hr1].
    -
      subst r. specialize (Hhnd eq_refl). cbn beta in Hhnd.
      pose proof (ODESC_PTR d 12 wv Hhnd) as (Hd1 & Hd2 & Hd4).
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
      eapply (pm_opnd_push w c0 K fx I A M2 model c R3 d 12 wv PS (OB2 R3 OR3) Hhnd G10 Hmax).
      intros A' M' model' R' b' cap' l l' Hg El' SF' Hlen' OB' GK' AG'.
      pose proof (go_len_operand G GOK 12 wv l Hg) as Hll. unfold HRep.Zlength in Hll. change (Zlen l <= g_maxlen G) in Hll.
      eapply (PK A' M' model' _ R' 1 l' OB').
      + rewrite (GK' 27%bv ltac:(clear; inl)), (GK3 27%bv ltac:(clear; inl)), (GK2 27%bv ltac:(clear; inl)). exact Q27.
      + rewrite (GK' 23%bv ltac:(clear; inl)), (GK3 23%bv ltac:(clear; inl)), (GK2 23%bv ltac:(clear; inl)). exact Q23.
      + rewrite (GK' 26%bv ltac:(clear; inl)), (GK3 26%bv ltac:(clear; inl)), (GK2 26%bv ltac:(clear; inl)). exact Q26.
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
      apply (know_more E M2 [KRange (EVar 39) 1 (2 ^ 64 - 1); KWord (SA (EVar 33) 40) (N.to_nat 1) (ELit 0)]) in HK.
      2: { repeat apply Forall_cons; try apply Forall_nil.
           - eapply krange_var; [evs; reflexivity | lia | lia].
           - eapply kword_var; [eapply fld_cellw; [exact (x_hunk X2) | cbn; lia] | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | cbn [edenot]; reflexivity]. }
      xruns HR HK 100%nat (0x67eac :: STOPS) (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
      postrun. name_run HRn R3.
      rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8.
      clear HRn HR HK. fixregs. rewrite Qgp2 in G3. rewrite Qtp2 in G4.
      exact (srclang_diag w c0 K fx A M2 model c R3 wv 12 PS FZ CK X2 Htr BUD G2 G3 G4 G8 C712' C720' ltac:(lia)).
  Qed.
End PM.
