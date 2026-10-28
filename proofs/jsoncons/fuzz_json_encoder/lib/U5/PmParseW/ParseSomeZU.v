(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5 PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5 PmEncSpecs_u5 PmLibSpecsX_u5 PmLibSpecsW_u5 PmRef_u5 PmRefFacts_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import RelLeaf.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutL5 CutAutoX CutHeap2V.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseSums_u5 ParseSums2_u5 ParseSums2X_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmParse Require Import ParseSomeKn. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseSpecs_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmParse Require Import ParseProve. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseBridges_u5 ParseBridges2_u5 ParseBridges3_u5 ParseBridges4_u5 ParseBridgesX_u5 ParseBridges5_u5 ParseSomeAt_u5 ParseSomeSem_u5 ParseBridges6_u5 ParseBridges6X_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParseW Require Import ParseSomeChk_u5 ParseSomeChk2_u5 ParseSomeChk3_u5 ParseSomeChk4_u5 ParseSomeAU ParseSomeBU ParseSomeBXU ParseSomeCU ParseSomeD_u5 ParseSomeD2U ParseSomeEU ParseSomeChk5_u5 ParseSomeChk6_u5 ParseSomeFU ParseSomeGU ParseSomeHU ParseSomeJU ParseSomeKU ParseSomeVU.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParseW Require Import ParseSomeBWU ParseSomeYWU.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmSmall Require Import SmallKnX. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmSmall Require Import SmallPtX_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmSmall Require Import VisitSumsX. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmSmall Require Import VisitBridgeX_u5.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Import PSMC.
Module PSZKU.
(* [comment removed for export] *)
Definition kinv_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TOther pc =>
      if (Z.eqb pc L0PC || Z.eqb pc LPC || Z.eqb pc L2PC)%bool then
        match kind_of i with
        | KInv | KVec => Z.eqb pc LPC
        | KPop => (Z.eqb pc LPC || Z.eqb pc L0PC)%bool
        | KPt => true
        | _ => false
        end
      else true
  | _ => true
  end.
Lemma kinv_ok : CH2.leaves_all PSMC.G.CPS PSMC.G.TAGS kinv_chk = true.
Proof. vm_compute. reflexivity. Qed.
End PSZKU.
Module PSZU.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Abbreviation uv := PB.uv.

Section Z.
Context {SCFG_P : ScfgP}.
Variable I : PSIU.inst.
Local Abbreviation L := (PSIU.iL I).      Local Abbreviation HI := (PSIU.iHI I).    Local Abbreviation LBo := (PSIU.iLBo I).  Local Abbreviation cr := (PSIU.icr I).
Local Abbreviation sp := (PSIU.isp I).    Local Abbreviation r := (PSIU.ir I).      Local Abbreviation P := (PSIU.iP I).      Local Abbreviation V := (PSIU.iV I).      Local Abbreviation E := (PSIU.iE I).
Local Abbreviation B := (PSIU.iB I).      Local Abbreviation kx := (PSIU.ikx I).    Local Abbreviation bx := (PSIU.ibx I).    Local Abbreviation g := (PSIU.ig I).      Local Abbreviation ps := (PSIU.ips I).
Local Abbreviation fx := (PSIU.ifx I).    Local Abbreviation R := (PSIU.iR I).      Local Abbreviation M := (PSIU.iM I).      Local Abbreviation model := (PSIU.imodel I).  Local Abbreviation K := (PSIU.iK I).
Local Abbreviation HIok := (PSIU.iHIok I).  Local Abbreviation LAY := (PSIU.iLAY I).
Local Abbreviation E0 := (PSIU.E0 I).     Local Abbreviation W := (PSIU.W I).       Local Abbreviation Cred := (PSIU.Cred I). Local Abbreviation XI := (PSIU.XI I).
Local Abbreviation HAMB := (CH2.heap_amb L HI GT.NF E0 M model LBo sp G.HDECL W G.BLS Cred).
Local Abbreviation AMB3 := (CH2.amb3 L HI GT.NF E0 M model LBo sp G.HDECL W G.BLS Cred XI).
Local Abbreviation is_leaf := (CH2.is_leaf G.CPS G.TAGS).
Let LS : hl_segs L = RSEGS := PmLayout.ly_segs L LAY.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.
(* [comment removed for export] *)
Hypothesis SETEC_OK : PMS.set_ec_spec L.
Hypothesis POP_OK : PMS.pop_state_spec L.
Hypothesis PARENT_OK : PMS.parent_spec L.
Hypothesis VECPUSH_OK : PMS.vec_push_spec L HI.
Hypothesis PUSHB_OK : PMS.str_push_back_spec L HI.
Hypothesis SKIP_OK : PMW.skip_space_specw L HI PML.STRTOD_SCR_V PMR.the_rm.      (* [comment removed for export] *)
Hypothesis BMEM_OK : PMW.begin_member_specw L HI PML.STRTOD_SCR_V PMR.the_rm.
Hypothesis BOBJ_OK : PMW.begin_object_specwU L HI PML.STRTOD_SCR_V PMES.WD_SCR_X PMR.the_rm.
Hypothesis BARR_OK : PMW.begin_array_specwU L HI PML.STRTOD_SCR_V PMES.WD_SCR_X PMR.the_rm.
Hypothesis EOBJ_OK : PMW.end_object_specwU L HI PML.STRTOD_SCR_V PMES.WD_SCR_X PMR.the_rm.
Hypothesis EARR_OK : PMW.end_array_specwU L HI PML.STRTOD_SCR_V PMES.WD_SCR_X PMR.the_rm.
Hypothesis NULL_OK : PMW.parse_null_specwU L HI PML.STRTOD_SCR_V PMES.WD_SCR_X PMR.the_rm.
Hypothesis TRUE_OK : PMW.parse_true_specwU L HI PML.STRTOD_SCR_V PMES.WD_SCR_X PMR.the_rm.
Hypothesis FALSE_OK : PMW.parse_false_specwU L HI PML.STRTOD_SCR_V PMES.WD_SCR_X PMR.the_rm.
Hypothesis STRING_OK : PMW.parse_string_specwU L HI PML.STRTOD_SCR_V PMES.WD_SCR_X PMR.the_rm.
Hypothesis NUMBER_OK : PMW.parse_number_specwU L HI PML.STRTOD_SCR_V PMES.WD_SCR_X PMR.the_rm.
Hypothesis ENDINT_OK : PMW.end_integer_value_specwU L HI PML.STRTOD_SCR_V PMES.WD_SCR_X PMR.the_rm.
Hypothesis ENDFRAC_OK : PMW.end_fraction_value_specwU L HI PML.STRTOD_SCR_V PMES.WD_SCR_X PMR.the_rm.
Hypothesis VNULL_OK : PMES.visit_null_specU L HI PMES.WD_SCR_X.
Hypothesis VBOOL_OK : PMES.visit_bool_specU L HI PMES.WD_SCR_X.

Lemma begin_rel : forall kind st' (pst ps2 : PML.pstate) (code : Z) (R2 : bvmap 5 word),
  ((code = 0 /\ PML.ps_level ps2 = PML.ps_level pst + 1 /\ PML.ps_st ps2 = st' /\ PML.ps_more ps2 = true /\ PML.ps_stack ps2 = PML.ps_stack pst ++ [kind] /\ PML.ps_win ps2 = PML.ps_win pst) \/ (code = 5 /\ PML.ps_level pst = 1024)) ->
  code = 0 -> PML.ps_more ps2 = true /\ PML.ps_win ps2 = PML.ps_win pst.
Proof. intros kind st' pst ps2 code R2 [(_ & _ & _ & Hm & _ & Hw)|(Hc & _)] H0; [split; assumption | exfalso; lia]. Qed.
Lemma end_rel : forall kind (pst ps2 : PML.pstate) (code : Z) (R2 : bvmap 5 word),
  ((code = 0 /\ PML.ps_level ps2 = PML.ps_level pst - 1 /\ PML.ps_more ps2 = true /\ (exists rest, PML.ps_stack pst = rest ++ [kind] /\ PML.ps_stack ps2 = rest) /\
    PML.ps_st ps2 = (if Z.eqb (PML.ps_level ps2) 0 then PML.ST_ACCEPT else PML.ST_EXPECT_COMMA_OR_END) /\ PML.ps_win ps2 = PML.ps_win pst) \/ In code [20; 21; 22; 23]) ->
  code = 0 -> PML.ps_more ps2 = true /\ PML.ps_win ps2 = PML.ps_win pst.
Proof. intros kind pst ps2 code R2 [(_ & _ & Hm & _ & _ & Hw)|Hc] H0; [split; assumption | exfalso; cbn [In] in Hc; lia]. Qed.

(* [comment removed for export] *)
Lemma calls : forall g1 M0c (OKV : CH2V.okV L M LBo sp G.HDECL W M0c) i c k ps1 pc, is_leaf i c k ps1 (CC.TOther pc) -> is_exit_pc pc = false -> CH2V.leaf_okV L HI GT.NF E0 M model LBo sp G.HDECL W G.BLS PMES.eghost VBX.gB (PSIU.Cred I) (PSIU.XIv I) G.CPS K PML.fp_ok g1 M0c i c ps1.
Proof.
  intros g1 M0c OKV i c k ps1 pc IL Hx.
  pose proof (CH2.leaves_all_sound _ _ _ struct_ok _ _ _ _ _ IL) as XS. unfold struct_chk in XS. rewrite Hx in XS. unfold call_chk in XS.
  destruct (CH2.ret_of G.RETS i k) as [j|] eqn:Hret.
  - destruct (nth_error G.CPS j) as [cj|]; [|discriminate XS]. apply andb_prop in XS as [_ XS]. revert XS.
    destruct (Z.eqb_spec pc VECPUSH) as [->|N1]; [intros _; apply CH2V.leaf_okV_of; [exact OKV | exact (PSHU.leaf_vec I g1 M0c OKV VECPUSH_OK i c k ps1 j IL Hret)]|].
    destruct (Z.eqb_spec pc PUSHB) as [->|N2]; [intros _; apply CH2V.leaf_okV_of; [exact OKV | exact (PSHU.leaf_pushb I g1 M0c OKV PUSHB_OK i c k ps1 j IL Hret)]|].
    destruct (Z.eqb_spec pc POP) as [->|N3]; [intros _; apply CH2V.leaf_okV_of; [exact OKV | exact (PSGU.leaf_pop I g1 M0c OKV POP_OK i c k ps1 j IL Hret)]|].
    destruct (Z.eqb_spec pc PARENT) as [->|N4]; [intros _; apply CH2V.leaf_okV_of; [exact OKV | exact (PSGU.leaf_parent I g1 M0c OKV PARENT_OK i c k ps1 j IL Hret)]|].
    destruct (Z.eqb_spec pc SETEC) as [->|N5]; [intros _; apply CH2V.leaf_okV_of; [exact OKV | exact (PSFU.leaf_setec I g1 M0c OKV SETEC_OK i c k ps1 j IL Hret)]|].
    (* [comment removed for export] *)
    destruct (Z.eqb pc VNULL || Z.eqb pc VBOOL)%bool eqn:Hvis.
    { intros _. apply (PSVU.leaf_vis I g1 M0c OKV (PSYWU.vis_ret_w I g1) VNULL_OK VBOOL_OK i c k ps1 pc j IL); [|exact Hret].
      apply orb_prop in Hvis as [Q|Q]; apply Z.eqb_eq in Q; [left | right]; exact Q. }
    destruct (pt_of pc) as [[[scr ereg] isx]|] eqn:Hpt; [intros _ | intros XS; discriminate XS].
    unfold pt_of in Hpt. destruct (find _ PTS) as [y|] eqn:Hf; [|discriminate Hpt]. apply find_some in Hf as [Hin He]. apply Z.eqb_eq in He. subst pc. clear Hpt Hx N1 N2 N3 N4 N5 Hvis.
    unfold PTS in Hin. cbn [In] in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]; cbn [fst] in IL.
    + exact (PSJU.leaf_skip I g1 M0c OKV SKIP_OK i c k ps1 j IL Hret).
    + exact (PSJU.leaf_bmember I g1 M0c OKV BMEM_OK i c k ps1 j IL Hret).
    + exact (PSJU.leaf_container I g1 M0c OKV PML.PC_BEGIN_OBJECT PMW.FBeginObject _ eq_refl eq_refl BOBJ_OK (begin_rel _ _) i c k ps1 j IL Hret).
    + exact (PSJU.leaf_container I g1 M0c OKV PML.PC_BEGIN_ARRAY PMW.FBeginArray _ eq_refl eq_refl BARR_OK (begin_rel _ _) i c k ps1 j IL Hret).
    + exact (PSJU.leaf_container I g1 M0c OKV PML.PC_END_OBJECT PMW.FEndObject _ eq_refl eq_refl EOBJ_OK (end_rel _) i c k ps1 j IL Hret).
    + exact (PSJU.leaf_container I g1 M0c OKV PML.PC_END_ARRAY PMW.FEndArray _ eq_refl eq_refl EARR_OK (end_rel _) i c k ps1 j IL Hret).
    + exact (PSJU.leaf_null I g1 M0c OKV NULL_OK i c k ps1 j IL Hret).
    + exact (PSJU.leaf_string I g1 M0c OKV STRING_OK i c k ps1 j IL Hret).
    + exact (PSJU.leaf_number I g1 M0c OKV NUMBER_OK i c k ps1 j IL Hret).
    + exact (PSJU.leaf_lit I g1 M0c OKV PML.PC_PARSE_TRUE PMW.FParseTrue eq_refl eq_refl TRUE_OK i c k ps1 j IL Hret).
    + exact (PSJU.leaf_lit I g1 M0c OKV PML.PC_PARSE_FALSE PMW.FParseFalse eq_refl eq_refl FALSE_OK i c k ps1 j IL Hret).
    + exact (PSJU.leaf_endnum I g1 M0c OKV PML.PC_END_INT PMW.FEndInt eq_refl eq_refl ENDINT_OK i c k ps1 j IL Hret).
    + exact (PSJU.leaf_endnum I g1 M0c OKV PML.PC_END_FRAC PMW.FEndFrac eq_refl eq_refl ENDFRAC_OK i c k ps1 j IL Hret).
  - apply andb_prop in XS as [XS _]. apply Z.eqb_eq in XS. subst pc. apply CH2V.leaf_okV_of; [exact OKV | exact (PSTU.leaf_tail I g1 M0c OKV SETEC_OK i c k ps1 IL Hret)].
Qed.

Lemma leaves : forall g1 M0c (OKV : CH2V.okV L M LBo sp G.HDECL W M0c) i c k ps1 pc, is_leaf i c k ps1 (CC.TOther pc) -> CH2V.leaf_okV L HI GT.NF E0 M model LBo sp G.HDECL W G.BLS PMES.eghost VBX.gB (PSIU.Cred I) (PSIU.XIv I) G.CPS K PML.fp_ok g1 M0c i c ps1.
Proof.
  intros g1 M0c OKV i c k ps1 pc IL. destruct (is_exit_pc pc) eqn:Hx; [|exact (calls g1 M0c OKV i c k ps1 pc IL Hx)].
  apply CH2V.leaf_okV_of; [exact OKV|].      (* [comment removed for export] *)
  unfold is_exit_pc in Hx. destruct (Z.eqb_spec pc RETPC) as [->|N1]; [exact (PSXU.exits I g1 M0c OKV i c k ps1 IL)|]. destruct (Z.eqb_spec pc DEADPC) as [->|N2]; [exact (PSXU.dead I g1 M0c OKV i c k ps1 IL)|].
  destruct (Z.eqb_spec pc HPC) as [->|N3]; [exact (PSEU.leaf_reH I g1 M0c OKV i c k ps1 IL)|].
  assert (Hpc : pc = L0PC \/ pc = LPC \/ pc = L2PC) by (destruct (Z.eqb_spec pc L0PC); [tauto|]; destruct (Z.eqb_spec pc LPC); [tauto|]; destruct (Z.eqb_spec pc L2PC); [tauto | discriminate Hx]).
  destruct (kind_of i) eqn:K1.
  - (* [comment removed for export] *)
    assert (pc = LPC) as -> by (pose proof (CH2.leaves_all_sound _ _ _ PSZKU.kinv_ok _ _ _ _ _ IL) as Q; unfold PSZKU.kinv_chk in Q; rewrite K1 in Q; destruct Hpc as [-> | [-> | ->]]; [discriminate Q | reflexivity | discriminate Q]).
    exact (PSEU.leaf_reAcc I g1 M0c OKV i c k ps1 IL K1).
  - exfalso. pose proof (CH2.leaves_all_sound _ _ _ PSZKU.kinv_ok _ _ _ _ _ IL) as Q. unfold PSZKU.kinv_chk in Q. rewrite K1 in Q. destruct Hpc as [-> | [-> | ->]]; discriminate Q.
  - assert (pc = LPC) as -> by (pose proof (CH2.leaves_all_sound _ _ _ PSZKU.kinv_ok _ _ _ _ _ IL) as Q; unfold PSZKU.kinv_chk in Q; rewrite K1 in Q; destruct Hpc as [-> | [-> | ->]]; [discriminate Q | reflexivity | discriminate Q]).
    exact (PSEU.leaf_reVec I g1 M0c OKV i c k ps1 IL K1).
  - exfalso. pose proof (CH2.leaves_all_sound _ _ _ PSZKU.kinv_ok _ _ _ _ _ IL) as Q. unfold PSZKU.kinv_chk in Q. rewrite K1 in Q. destruct Hpc as [-> | [-> | ->]]; discriminate Q.
  - assert (Hp2 : pc = LPC \/ pc = L0PC) by (pose proof (CH2.leaves_all_sound _ _ _ PSZKU.kinv_ok _ _ _ _ _ IL) as Q; unfold PSZKU.kinv_chk in Q; rewrite K1 in Q; destruct Hpc as [-> | [-> | ->]]; [tauto | tauto | discriminate Q]).
    exact (PSEU.leaf_rePop I g1 M0c OKV i c k ps1 pc IL Hp2 K1).
  - exfalso. pose proof (CH2.leaves_all_sound _ _ _ PSZKU.kinv_ok _ _ _ _ _ IL) as Q. unfold PSZKU.kinv_chk in Q. rewrite K1 in Q. destruct Hpc as [-> | [-> | ->]]; discriminate Q.
  - exfalso. pose proof (CH2.leaves_all_sound _ _ _ PSZKU.kinv_ok _ _ _ _ _ IL) as Q. unfold PSZKU.kinv_chk in Q. rewrite K1 in Q. destruct Hpc as [-> | [-> | ->]]; discriminate Q.
  - exact (PSEU.leaf_rePt I g1 M0c i c k ps1 pc IL ltac:(tauto) K1).
  - exfalso. pose proof (CH2.leaves_all_sound _ _ _ PSZKU.kinv_ok _ _ _ _ _ IL) as Q. unfold PSZKU.kinv_chk in Q. rewrite K1 in Q. destruct Hpc as [-> | [-> | ->]]; discriminate Q.
Qed.

Lemma main : srealizes RSEGS SCFG (@PML.cfg fx R PML.PC_PARSE_SOME M model) K.
Proof.
  unfold PML.cfg. change PML.PC_PARSE_SOME with (CC.cp_pc G.cp0). rewrite <- LS.
  eapply (CH2V.cert_sound3V L HI HIok (PB.LYI_ L LAY) (PB.LYE_ L LAY) (PmLayout.ly_ro L LAY) GT.NF E0 M model LBo sp G.HDECL W G.BLS PMES.eghost VBX.gB (PSIU.Cred I) (PSIU.XIv I) (PSIU.STKF I) PSIU.SCRP PSIU.NF32 (PSIU.U2 I) (PSIU.W_OK I) (PSIU.WRS_OK I)
            G.CPS K PML.fp_ok G.TAGS) with (i := 0%nat) (E := E0).
  - rewrite LS. exact FPM.
  - rewrite LS. exact Cut_psome_xsrcw_u5.plans.
  - exact Cut_psome_xsrcw_u5.tags_ok.
  - exact heap_ok3.
  - intros g1. exact (PSBU.goto_cred I g1).
  - intros g1 M0c OKV. exact (PSBU.goto_xiv I g1 M0c OKV (fun i c k ps1 j s IL E1 R1 E' R' M1 M' model1 HAt HA Hag HLF HX HSM => PSBWU.goto_sim I g1 M0c OKV i c k ps1 j s IL E1 R1 E' R' M1 M' model1 HAt HA Hag HLF HX HSM (PSBU.goto_xi I g1 M0c OKV i c k ps1 j s IL E1 R1 E' R' M1 M' model1 HAt HA Hag HLF HX))).      (* [comment removed for export] *)
  - intros i c k ps1 pc IL g1 M0c OKV. exact (leaves g1 M0c OKV i c k ps1 pc IL).
  - reflexivity.
  - rewrite LS. exact (PSIU.At0 I).
  - (* [comment removed for export] *)
    pose proof (PSIU.UU I) as (U2 & U10 & U11 & U12 & U32 & U33 & U34 & U35 & U36 & U37 & U38 & U39 & U40 & U41 & U42 & U43 & U44 & U45 & U46 & U47 & U48).
    pose proof (PSIU.NUM I) as (BRb & BRs & Hdb & Hdsb & A1 & A2 & A3 & N8 & N9 & N10 & N11 & N12 & N13 & N14 & N15 & N16 & N17 & N18 & N19 & N20 & N21 & N22 & N23).
    pose proof (PSIU.WIN I) as (W0 & W1 & W2 & Hwd & W4).
    assert (Hden0 : CH2.den E0 (nth 0 G.BLS []) = PML.ps_blocks ps).
    { change (nth 0 G.BLS []) with [(EVar 37, APC.escale 2 (EVar 35)); (EVar 38, EVar 40)]. rewrite !PB.den_cons. change (CH2.den E0 []) with (@nil (Z * Z)). unfold PML.ps_blocks.
      fold (PSIU.bptr I) (PSIU.bcap I) (PSIU.sb I) (PSIU.scap I). rewrite PB.uv_escale. unfold PB.uv. cbn [edenot]. rewrite U35, U37, U38, U40, <- N8. rewrite Z.mod_small by lia. reflexivity. }
    apply (CH2V.amb3V_intro L HI GT.NF E0 M model LBo sp G.HDECL W G.BLS PMES.eghost VBX.gB (PSIU.Cred I) (PSIU.XIv I) (PSIU.ieg I) M 0%nat E0 M model (CH2V.okV_refl L M LBo sp G.HDECL W (PSIU.DEF0 I))).
    split.
    + split; [exact (PSIU.iHmo I)|]. split; [apply L5C.model_but_vm_refl|]. split; [apply CC.env_agree_refl|].
      split; [|split; [reflexivity | intros a _ _ Hd; exact Hd]].
      exists cr. split; [unfold CH2.cur, CH2V.LBr, VBX.gB; rewrite Hden0; exact (PSIU.iHH I)|].
      apply (PSIU.cred_of_blocks I (PSIU.ieg I) 0 E0 cr ps Hden0); [destruct (PSIU.iHWF I) as (_ & _ & _ & W4' & _); exact W4' | rewrite <- (PSIU.iHbxu I); exact (PSIU.iHPC I)].
    + split; [|split; [exact (conj (PSIU.iHINV I) (PSIU.iHLIT I)) | exact (PSYWU.zentry I)]].      (* [comment removed for export] *)      (* [comment removed for export] *)
      pose proof (PSIU.UU I) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & U41' & _).
      unfold PSIU.XI. split; [exact (PSIU.DEF0 I)|]. split; [intros Q; exfalso; apply Q; reflexivity|]. split; [intros Q; vm_compute in Q; discriminate Q|].
      split; [unfold PSIU.XDEP; change (kind_of 0) with KInv;
              change (PSM2.vw 0) with (Some (PB4.PV2 (EVar 41) WEND (EVar 32) (EVar 42) (EVar 43) (EVar 44) (EVar 45) (EVar 46) (EVar 36) (EVar 38) (APC.eadd (EVar 38) (EVar 39)) (APC.eadd (EVar 38) (EVar 40)), EVar 37, APC.escale 2 (EVar 35)));
              cbv beta iota; cbn [PB4.pv_level]; unfold PB.uv; cbn [edenot]; rewrite U41'; exact (proj1 (PSIU.iHSYNC I))|].      (* [comment removed for export] *)
      change (kind_of 0) with KInv. change (PSM2.vw 0) with (Some (PB4.PV2 (EVar 41) WEND (EVar 32) (EVar 42) (EVar 43) (EVar 44) (EVar 45) (EVar 46) (EVar 36) (EVar 38) (APC.eadd (EVar 38) (EVar 39)) (APC.eadd (EVar 38) (EVar 40)), EVar 37, APC.escale 2 (EVar 35))).
      exists (PML.ps_more ps), (PML.ps_done ps), (PML.ps_stack ps), (PML.ps_buf ps).
      pose proof (PSIU.iHPA I) as HPA0. unfold PML.parser_at in HPA0.
      destruct HPA0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstr & _ & _ & _ & _ & Hstk & Hsl & _).
      destruct (PSBU.FRZ I E0 (CC.env_agree_refl _ _)) as (_ & _ & _ & _ & F5 & F6 & F7 & _).
      assert (VSE : uv E0 (APC.eadd (EVar 38) (EVar 39)) = PSIU.sb I + PSIU.slen I) by (rewrite PB.uv_eadd; unfold PB.uv; cbn [edenot]; rewrite U38, U39; apply Z.mod_small; destruct BRs as (? & _ & _ & _ & ?); unfold hl_ceil in *; pose proof (PSIU.SPF I) as (_ & _ & _ & S4 & _); lia).
      assert (VSC : uv E0 (APC.eadd (EVar 38) (EVar 40)) = PSIU.sb I + PSIU.scap I) by (rewrite PB.uv_eadd; unfold PB.uv; cbn [edenot]; rewrite U38, U40; apply Z.mod_small; destruct BRs as (? & _ & _ & _ & ?); unfold hl_ceil in *; pose proof (PSIU.SPF I) as (_ & _ & _ & S4 & _); lia).
      assert (VCE : uv E0 (APC.escale 2 (EVar 35)) = PSIU.bcap I) by (rewrite PB.uv_escale; unfold PB.uv; cbn [edenot]; rewrite U35, <- N8; apply Z.mod_small; lia).
      assert (Hps : PSIU.ps_of (PB4.PV2 (EVar 41) WEND (EVar 32) (EVar 42) (EVar 43) (EVar 44) (EVar 45) (EVar 46) (EVar 36) (EVar 38) (APC.eadd (EVar 38) (EVar 39)) (APC.eadd (EVar 38) (EVar 40))) (EVar 37) (APC.escale 2 (EVar 35)) E0
                        (PML.ps_more ps) (PML.ps_done ps) (PML.ps_stack ps) (PML.ps_buf ps) = ps).
      { unfold PSIU.ps_of. cbn [PB4.pv_st PB4.pv_sst PB4.pv_nst PB4.pv_level PB4.pv_sb PB4.pv_scend PB4.pv_wptr PB4.pv_wend]. rewrite VSC, VCE, F7. change (EVar 32) with SEG. rewrite F5.
        unfold PB.uv. cbn [edenot]. rewrite U41, U42, U43, U44, U37, U38.
        assert (Hwin : PB4.win_of (PSIU.seg I) (PSIU.wend I) = PML.ps_win ps).
        { unfold PB4.win_of, PSIU.seg, PSIU.wend, PSIU.seg_of, PSIU.wend_of. destruct (PML.ps_win ps) as [[p e]|] eqn:Hw; cbn [PSA.wincells fst snd]; [|reflexivity].
          destruct W4 as [[Q1 Q2]|(ch & Hch & Hc1 & Hc2 & (B0 & _))]; unfold PSIU.seg, PSIU.wend, PSIU.seg_of, PSIU.wend_of in *; rewrite Hw in *; cbn [PSA.wincells fst snd] in *.
          - pose proof (PSIU.iHWIN I) as HWK. unfold PML.win_ok in HWK. rewrite Hw in HWK. destruct HWK as (ch & Hch & Hc1 & Hc2 & _).
            destruct (hio_wf L SCFG HI HIok _ _ _ _ (PSIU.iHH I)) as (Hwf & _). destruct (Hwf (ch, 16384) ltac:(apply in_or_app; right; apply in_or_app; left; exact Hch)) as ((Q & _) & _).      (* [comment removed for export] *) cbn [fst] in Q. lia.
          - destruct (Z.eqb_spec e 0); [lia | reflexivity]. }
        rewrite Hwin. unfold PSIU.level, PSIU.st0, PSIU.sst0, PSIU.nst0, PSIU.bptr, PSIU.sb, PSIU.bcap, PSIU.scap. destruct ps; cbn; f_equal; lia. }
      rewrite Hps. split.
      * unfold PSIU.contents. cbn [PB4.pv_st PB4.pv_sb PB4.pv_send PB4.pv_scend PB4.pv_wptr PB4.pv_wend PB4.pv_size PB4.pv_more PB4.pv_done]. rewrite VSE, VSC, VCE, F7. change (EVar 32) with SEG. rewrite F5.
        unfold PB.uv. cbn [edenot]. rewrite U38, U36, U37, U45, U46, U42.
        split; [exact Hstk|]. split; [reflexivity|]. split; [unfold PSIU.slen, PSIU.scap in *; lia|]. split; [reflexivity|]. split; [lia|]. split; [reflexivity|]. split; [unfold PSIU.size0, PSIU.bcap in *; lia|].
        split; [intros _; destruct Hstr as ((_ & _ & _ & _ & Hb & _) & _); exact Hb|]. split; [reflexivity|]. split; [reflexivity|].
        cbn [PB4.pv_level PB4.pv_st edenot]. rewrite ?U41, ?U42. exact (proj2 (PSIU.iXS I _ _ (PSIU.iHSYNC I))).      (* [comment removed for export] *)
      * split; [exact (PSIU.iHLS I)|]. split; [exact (PSIU.iHWF I)|]. split; [exact (PSIU.iHBB I)|]. split; [intros Q; rewrite (PSIU.iHmore I) in Q; discriminate Q|].
        split; [intros [Q|[Q|[Q|[Q|Q]]]]; discriminate Q | intros Q; discriminate Q].
  - exact (PSIU.iHfp I).
Qed.
End Z.

(* [comment removed for export] *)
Section Final.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.
(* [comment removed for export] *)
Hypothesis SETEC_OK : PMS.set_ec_spec L.
Hypothesis POP_OK : PMS.pop_state_spec L.
Hypothesis PARENT_OK : PMS.parent_spec L.
Hypothesis VECPUSH_OK : PMS.vec_push_spec L HI.
Hypothesis PUSHB_OK : PMS.str_push_back_spec L HI.
Hypothesis SKIP_OK : PMW.skip_space_specw L HI PML.STRTOD_SCR_V PMR.the_rm.      (* [comment removed for export] *)
Hypothesis BMEM_OK : PMW.begin_member_specw L HI PML.STRTOD_SCR_V PMR.the_rm.
Hypothesis BOBJ_OK : PMW.begin_object_specwU L HI PML.STRTOD_SCR_V PMES.WD_SCR_X PMR.the_rm.
Hypothesis BARR_OK : PMW.begin_array_specwU L HI PML.STRTOD_SCR_V PMES.WD_SCR_X PMR.the_rm.
Hypothesis EOBJ_OK : PMW.end_object_specwU L HI PML.STRTOD_SCR_V PMES.WD_SCR_X PMR.the_rm.
Hypothesis EARR_OK : PMW.end_array_specwU L HI PML.STRTOD_SCR_V PMES.WD_SCR_X PMR.the_rm.
Hypothesis NULL_OK : PMW.parse_null_specwU L HI PML.STRTOD_SCR_V PMES.WD_SCR_X PMR.the_rm.
Hypothesis TRUE_OK : PMW.parse_true_specwU L HI PML.STRTOD_SCR_V PMES.WD_SCR_X PMR.the_rm.
Hypothesis FALSE_OK : PMW.parse_false_specwU L HI PML.STRTOD_SCR_V PMES.WD_SCR_X PMR.the_rm.
Hypothesis STRING_OK : PMW.parse_string_specwU L HI PML.STRTOD_SCR_V PMES.WD_SCR_X PMR.the_rm.
Hypothesis NUMBER_OK : PMW.parse_number_specwU L HI PML.STRTOD_SCR_V PMES.WD_SCR_X PMR.the_rm.
Hypothesis ENDINT_OK : PMW.end_integer_value_specwU L HI PML.STRTOD_SCR_V PMES.WD_SCR_X PMR.the_rm.
Hypothesis ENDFRAC_OK : PMW.end_fraction_value_specwU L HI PML.STRTOD_SCR_V PMES.WD_SCR_X PMR.the_rm.
Hypothesis VNULL_OK : PMES.visit_null_specU L HI PMES.WD_SCR_X.
Hypothesis VBOOL_OK : PMES.visit_bool_specU L HI PMES.WD_SCR_X.

(* [comment removed for export] *)
Theorem parse_some_okw : PMW.parse_some_specwU L HI PML.STRTOD_SCR_V PMES.WD_SCR_X PMR.the_rm.
Proof.
  unfold PMW.parse_some_specwU, PMW.ptransxwU, PMW.ptrans_gxwU, PMW.ptrans_gbxwU. intros LBo cr sp r P V E S2 B kx bx g ps eg w x c. unfold PML.cps_heap.
  intros fx R M model K HH Hmo HKnil Hfp (Hentry & ((Ha0 & Ha1 & Ha2) & Hmore) & HPA & HWF & HWIN & HBB & HVIS & HEC & HLS & HG & HINV & HLIT & HSYNC & Hkx & Hbx & HPC & OBJS & HWBY & HRM & HROOM) Hcont.
  pose proof (PMX.objs_x_j L sp P V E S2 OBJS) as (OP & _).
  pose proof (PSBU.pa_def _ _ _ HPA) as HdP.
  destruct (PB2.cell_exists M (P + 160) 8 ltac:(lia)) as (line0 & Rl & Hl); [eapply (L5.defined_sub _ _ _ _ _ HdP); cbn; lia|].
  destruct (PB2.cell_exists M (P + 168) 8 ltac:(lia)) as (pos0 & Rp & Hp); [eapply (L5.defined_sub _ _ _ _ _ HdP); cbn; lia|].
  assert (HWB : (L5.bytes_at RSEGS M (PSIU.seg_of ps) w /\ Z.of_nat (length w) = PSIU.wend_of ps - PSIU.seg_of ps) /\ Forall (fun b => 0 <= b <= 255) w).
  { unfold PSIU.seg_of, PSIU.wend_of. unfold PMW.win_bytes in HWBY. destruct (PML.ps_win ps) as [[p e]|]; cbn [PSA.wincells fst snd].
    - destruct HWBY as (B1 & B2 & B3). split; [split; [exact B1 | exact B2] | exact B3].
    - subst w. split; [split; [intros i Hi; cbn in Hi; lia | reflexivity] | constructor]. }
  destruct HWB as [Hwinb Hwrng].
  (* [comment removed for export] *)
  assert (HP220 : 0 <= P + 220 /\ P + 220 + Z.of_nat 1 <= 2 ^ 64).
  { destruct OP as (OPa & OPb & OPc). pose proof (L5C.stk_floor _ _ _ _ (proj2 (proj2 (proj2 (proj2 Hentry))))) as FL. change (PMX.PSOMEX_SCR PML.STRTOD_SCR_V PMES.WD_SCR_X) with 12800 in FL.
    pose proof (L5C.stk_window _ _ _ _ (proj2 (proj2 (proj2 (proj2 Hentry))))) as (SW1 & SW2 & SW3). cbn [Z.of_nat Pos.to_nat Pos.of_succ_nat]. clear -OPa OPb FL SW2 SW3. lia. }
  destruct (PB3.bytes_of_defined_r M 1%nat (P + 220) (proj1 HP220) (proj2 HP220)) as (tb & Htl & Htb & Htr); [eapply (L5.defined_sub _ _ _ _ _ HdP); cbn; lia|].
  destruct tb as [|tag0 [|? ?]]; try discriminate Htl. pose proof (Forall_inv Htr) as Rtag; cbn beta in Rtag.
  assert (Htag : PML.u8 M (P + 220) tag0) by (specialize (Htb 0%nat ltac:(cbn; lia)); cbn [nth Z.of_nat] in Htb; rewrite Z.add_0_r in Htb; exact Htb).
  set (I := @PSIU.Inst SCFG_P L HI HIok LAY LBo cr sp r P V E S2 B kx (bx + PMES.benc L eg) g ps eg fx R M model K HH Hmo HKnil Hfp Hentry Ha0 Ha1 Ha2 Hmore HPA HWF HWIN HBB HVIS HEC HLS HG Hkx HPC bx eq_refl Hbx HINV HLIT HSYNC
                        (fun _ _ H => H) (fun _ _ H => H) OBJS line0 pos0 w Hl Rl Hp Rp tag0 Htag Rtag Hwinb Hwrng x c HRM HROOM Hcont).
  exact (main I FPM SETEC_OK POP_OK PARENT_OK VECPUSH_OK PUSHB_OK SKIP_OK BMEM_OK BOBJ_OK BARR_OK EOBJ_OK EARR_OK NULL_OK TRUE_OK FALSE_OK STRING_OK NUMBER_OK ENDINT_OK ENDFRAC_OK VNULL_OK VBOOL_OK).
Qed.
End Final.
End PSZU.
Print Assumptions PSZU.parse_some_okw.