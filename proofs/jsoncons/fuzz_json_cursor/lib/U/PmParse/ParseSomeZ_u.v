(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10PlanKit_u PmLibDefs_u PmLibSpecs_u PmLayout_u PmCurDefs_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutCert Require Import Pm10CutKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeap2 CutL5 CutAutoX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseSums_u ParseSums2_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmParse Require Import ParseSomeKn. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseSpecs_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmParse Require Import ParseProve. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseBridges_u ParseBridges2_u ParseBridges3_u ParseBridges4_u ParseBridges5_u ParseSomeAt_u ParseSomeSem_u ParseSomeSemC_u ParseSomeCurC_u ParseSomeChk_u ParseSomeChk2_u ParseSomeChk3_u ParseSomeChk4_u ParseSomeA_u ParseSomeB_u ParseSomeC_u ParseSomeD_u ParseSomeD2_u ParseSomeE_u ParseBridges6_u ParseSomeChk5_u ParseSomeChk6_u ParseSomeF_u ParseSomeG_u ParseSomeH_u ParseSomeJ_u ParseSomeK_u ParseSomeChk7_u ParseSomeV_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Import PSMC.
Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module PSZK.

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
Proof. vmc_refl. Qed.
End PSZK.
Module PSZ.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Abbreviation uv := PB.uv.

Section Z.
Context {SCFG_P : ScfgP}.
Variable I : PSI.inst.
Local Abbreviation L := (PSI.iL I).      Local Abbreviation HI := (PSI.iHI I).    Local Abbreviation LBo := (PSI.iLBo I).  Local Abbreviation cr := (PSI.icr I).
Local Abbreviation sp := (PSI.isp I).    Local Abbreviation r := (PSI.ir I).      Local Abbreviation P := (PSI.iP I).      Local Abbreviation V := (PSI.iV I).      Local Abbreviation E := (PSI.iE I).
Local Abbreviation B := (PSI.iB I).      Local Abbreviation kx := (PSI.ikx I).    Local Abbreviation bx := (PSI.ibx I).    Local Abbreviation g := (PSI.ig I).      Local Abbreviation ps := (PSI.ips I).
Local Abbreviation fx := (PSI.ifx I).    Local Abbreviation R := (PSI.iR I).      Local Abbreviation M := (PSI.iM I).      Local Abbreviation model := (PSI.imodel I).  Local Abbreviation K := (PSI.iK I).
Local Abbreviation HIok := (PSI.iHIok I).  Local Abbreviation LAY := (PSI.iLAY I).
Local Abbreviation E0 := (PSI.E0 I).     Local Abbreviation W := (PSI.W I).       Local Abbreviation Cred := (PSI.Cred I). Local Abbreviation XI := (PSI.XI I).
Local Abbreviation HAMB := (CH2.heap_amb L HI GT.NF E0 M model LBo sp G.HDECL W G.BLS Cred).
Local Abbreviation AMB3 := (CH2.amb3 L HI GT.NF E0 M model LBo sp G.HDECL W G.BLS Cred XI).
Local Abbreviation is_leaf := (CH2.is_leaf G.CPS G.TAGS).
Let LS : hl_segs L = RSEGS := PmLayout.ly_segs L LAY.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.

Hypothesis SETEC_OK : PMS.set_ec_spec L.
Hypothesis POP_OK : PMS.pop_state_spec L.
Hypothesis PARENT_OK : PMS.parent_spec L.
Hypothesis VECPUSH_OK : PMS.vec_push_spec L HI.
Hypothesis PUSHB_OK : PMS.str_push_back_spec L HI.
Hypothesis SKIP_OK : PMS.skip_space_spec L HI PML.STRTOD_SCR_V.
Hypothesis BMEM_OK : PMS.begin_member_spec L HI PML.STRTOD_SCR_V.
Hypothesis BOBJ_OK : PMS.begin_object_spec L HI PML.STRTOD_SCR_V.
Hypothesis BARR_OK : PMS.begin_array_spec L HI PML.STRTOD_SCR_V.
Hypothesis EOBJ_OK : PMS.end_object_spec L HI PML.STRTOD_SCR_V.
Hypothesis EARR_OK : PMS.end_array_spec L HI PML.STRTOD_SCR_V.
Hypothesis NULL_OK : PMS.parse_null_spec L HI PML.STRTOD_SCR_V.
Hypothesis TRUE_OK : PMS.parse_true_spec L HI PML.STRTOD_SCR_V.
Hypothesis FALSE_OK : PMS.parse_false_spec L HI PML.STRTOD_SCR_V.
Hypothesis STRING_OK : PMS.parse_string_spec L HI PML.STRTOD_SCR_V.
Hypothesis NUMBER_OK : PMS.parse_number_spec L HI PML.STRTOD_SCR_V.
Hypothesis ENDINT_OK : PMS.end_integer_value_spec L HI PML.STRTOD_SCR_V.
Hypothesis ENDFRAC_OK : PMS.end_fraction_value_spec L HI PML.STRTOD_SCR_V.
Hypothesis VNULL_OK : PMS.visit_null_spec L VNULL.
Hypothesis VBOOL_OK : PMS.visit_bool_spec L VBOOL.

Lemma begin_rel : forall kind st' (pst ps2 : PML.pstate) (code : Z) (R2 : bvmap 5 word),
  ((code = 0 /\ PML.ps_level ps2 = PML.ps_level pst + 1 /\ PML.ps_st ps2 = st' /\ PML.ps_more ps2 = false /\ PML.ps_stack ps2 = PML.ps_stack pst ++ [kind] /\ PML.ps_win ps2 = PML.ps_win pst) \/ (code = 5 /\ PML.ps_level pst = 1024)) ->
  code = 0 -> PML.ps_win ps2 = PML.ps_win pst.
Proof. intros kind st' pst ps2 code R2 [(_ & _ & _ & Hm & _ & Hw)|(Hc & _)] H0; [exact Hw | exfalso; lia]. Qed.
Lemma end_rel : forall kind (pst ps2 : PML.pstate) (code : Z) (R2 : bvmap 5 word),
  ((code = 0 /\ PML.ps_level ps2 = PML.ps_level pst - 1 /\ PML.ps_more ps2 = false /\ (exists rest, PML.ps_stack pst = rest ++ [kind] /\ PML.ps_stack ps2 = rest) /\
    PML.ps_st ps2 = (if Z.eqb (PML.ps_level ps2) 0 then PML.ST_ACCEPT else PML.ST_EXPECT_COMMA_OR_END) /\ PML.ps_win ps2 = PML.ps_win pst) \/ In code [20; 21; 22; 23]) ->
  code = 0 -> PML.ps_win ps2 = PML.ps_win pst.
Proof. intros kind pst ps2 code R2 [(_ & _ & Hm & _ & _ & Hw)|Hc] H0; [exact Hw | exfalso; cbn [In] in Hc; lia]. Qed.

Lemma calls : forall i c k ps1 pc, is_leaf i c k ps1 (CC.TOther pc) -> is_exit_pc pc = false -> CC.leaf_ok (hl_segs L) G.CPS AMB3 K PML.fp_ok i c ps1.
Proof.
  intros i c k ps1 pc IL Hx.
  pose proof (CH2.leaves_all_sound _ _ _ struct_ok _ _ _ _ _ IL) as XS. unfold struct_chk in XS. rewrite Hx in XS. unfold call_chk in XS.
  destruct (CH2.ret_of G.RETS i k) as [j|] eqn:Hret.
  - destruct (nth_error G.CPS j) as [cj|]; [|discriminate XS]. apply andb_prop in XS as [_ XS]. revert XS.
    destruct (Z.eqb_spec pc VECPUSH) as [->|N1]; [intros _; exact (PSH.leaf_vec I VECPUSH_OK i c k ps1 j IL Hret)|].
    destruct (Z.eqb_spec pc PUSHB) as [->|N2]; [intros _; exact (PSH.leaf_pushb I PUSHB_OK i c k ps1 j IL Hret)|].
    destruct (Z.eqb_spec pc POP) as [->|N3]; [intros _; exact (PSG.leaf_pop I POP_OK i c k ps1 j IL Hret)|].
    destruct (Z.eqb_spec pc PARENT) as [->|N4]; [intros _; exact (PSG.leaf_parent I PARENT_OK i c k ps1 j IL Hret)|].
    destruct (Z.eqb_spec pc SETEC) as [->|N5]; [intros _; exact (PSF.leaf_setec I SETEC_OK i c k ps1 j IL Hret)|].
    destruct (Z.eqb_spec pc VNULL) as [->|N6]; [intros _; exact (PSV.leaf_vis I VNULL_OK VBOOL_OK i c k ps1 VNULL j IL (or_introl eq_refl) Hret)|].
    destruct (Z.eqb_spec pc VBOOL) as [->|N7]; [intros _; exact (PSV.leaf_vis I VNULL_OK VBOOL_OK i c k ps1 VBOOL j IL (or_intror eq_refl) Hret)|].
    cbn [orb].
    destruct (pt_of pc) as [[scr ereg]|] eqn:Hpt; [intros _ | intros XS; discriminate XS].
    unfold pt_of in Hpt. destruct (find _ PTS) as [y|] eqn:Hf; [|discriminate Hpt]. apply find_some in Hf as [Hin He]. apply Z.eqb_eq in He. subst pc. clear Hpt Hx N1 N2 N3 N4 N5 N6 N7.
    unfold PTS in Hin. cbn [In] in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]; cbn [fst] in IL.
    + exact (PSJ.leaf_skip I SKIP_OK i c k ps1 j IL Hret).
    + exact (PSJ.leaf_bmember I BMEM_OK i c k ps1 j IL Hret).
    + exact (PSJ.leaf_container I PML.PC_BEGIN_OBJECT _ eq_refl BOBJ_OK (begin_rel _ _) i c k ps1 j IL Hret).
    + exact (PSJ.leaf_container I PML.PC_BEGIN_ARRAY _ eq_refl BARR_OK (begin_rel _ _) i c k ps1 j IL Hret).
    + exact (PSJ.leaf_container I PML.PC_END_OBJECT _ eq_refl EOBJ_OK (end_rel _) i c k ps1 j IL Hret).
    + exact (PSJ.leaf_container I PML.PC_END_ARRAY _ eq_refl EARR_OK (end_rel _) i c k ps1 j IL Hret).
    + exact (PSJ.leaf_null I NULL_OK i c k ps1 j IL Hret).
    + exact (PSJ.leaf_string I STRING_OK i c k ps1 j IL Hret).
    + exact (PSJ.leaf_number I NUMBER_OK i c k ps1 j IL Hret).
    + exact (PSJ.leaf_lit I PML.PC_PARSE_TRUE eq_refl TRUE_OK i c k ps1 j IL Hret).
    + exact (PSJ.leaf_lit I PML.PC_PARSE_FALSE eq_refl FALSE_OK i c k ps1 j IL Hret).
    + exact (PSJ.leaf_endnum I PML.PC_END_INT eq_refl ENDINT_OK i c k ps1 j IL Hret).
    + exact (PSJ.leaf_endnum I PML.PC_END_FRAC eq_refl ENDFRAC_OK i c k ps1 j IL Hret).
  - apply andb_prop in XS as [XS _]. apply Z.eqb_eq in XS. subst pc. exact (PST.leaf_tail I SETEC_OK i c k ps1 IL Hret).
Qed.

Lemma leaves : forall i c k ps1 pc, is_leaf i c k ps1 (CC.TOther pc) -> CC.leaf_ok (hl_segs L) G.CPS AMB3 K PML.fp_ok i c ps1.
Proof.
  intros i c k ps1 pc IL. destruct (is_exit_pc pc) eqn:Hx; [|exact (calls i c k ps1 pc IL Hx)].
  unfold is_exit_pc in Hx. destruct (Z.eqb_spec pc RETPC) as [->|N1]; [exact (PSX.exits I i c k ps1 IL)|]. destruct (Z.eqb_spec pc DEADPC) as [->|N2]; [exact (PSX.dead I i c k ps1 IL)|].
  destruct (Z.eqb_spec pc HPC) as [->|N3]; [exact (PSE.leaf_reH I i c k ps1 IL)|].
  assert (Hpc : pc = L0PC \/ pc = LPC \/ pc = L2PC) by (destruct (Z.eqb_spec pc L0PC); [tauto|]; destruct (Z.eqb_spec pc LPC); [tauto|]; destruct (Z.eqb_spec pc L2PC); [tauto | discriminate Hx]).
  destruct (kind_of i) eqn:K1.
  -
    assert (pc = LPC) as -> by (pose proof (CH2.leaves_all_sound _ _ _ PSZK.kinv_ok _ _ _ _ _ IL) as Q; unfold PSZK.kinv_chk in Q; rewrite K1 in Q; destruct Hpc as [-> | [-> | ->]]; [discriminate Q | reflexivity | discriminate Q]).
    exact (PSE.leaf_reAcc I i c k ps1 IL K1).
  - exfalso. pose proof (CH2.leaves_all_sound _ _ _ PSZK.kinv_ok _ _ _ _ _ IL) as Q. unfold PSZK.kinv_chk in Q. rewrite K1 in Q. destruct Hpc as [-> | [-> | ->]]; discriminate Q.
  - assert (pc = LPC) as -> by (pose proof (CH2.leaves_all_sound _ _ _ PSZK.kinv_ok _ _ _ _ _ IL) as Q; unfold PSZK.kinv_chk in Q; rewrite K1 in Q; destruct Hpc as [-> | [-> | ->]]; [discriminate Q | reflexivity | discriminate Q]).
    exact (PSE.leaf_reVec I i c k ps1 IL K1).
  - exfalso. pose proof (CH2.leaves_all_sound _ _ _ PSZK.kinv_ok _ _ _ _ _ IL) as Q. unfold PSZK.kinv_chk in Q. rewrite K1 in Q. destruct Hpc as [-> | [-> | ->]]; discriminate Q.
  - assert (Hp2 : pc = LPC \/ pc = L0PC) by (pose proof (CH2.leaves_all_sound _ _ _ PSZK.kinv_ok _ _ _ _ _ IL) as Q; unfold PSZK.kinv_chk in Q; rewrite K1 in Q; destruct Hpc as [-> | [-> | ->]]; [tauto | tauto | discriminate Q]).
    exact (PSE.leaf_rePop I i c k ps1 pc IL Hp2 K1).
  - exfalso. pose proof (CH2.leaves_all_sound _ _ _ PSZK.kinv_ok _ _ _ _ _ IL) as Q. unfold PSZK.kinv_chk in Q. rewrite K1 in Q. destruct Hpc as [-> | [-> | ->]]; discriminate Q.
  - exfalso. pose proof (CH2.leaves_all_sound _ _ _ PSZK.kinv_ok _ _ _ _ _ IL) as Q. unfold PSZK.kinv_chk in Q. rewrite K1 in Q. destruct Hpc as [-> | [-> | ->]]; discriminate Q.
  - exact (PSE.leaf_rePt I i c k ps1 pc IL ltac:(tauto) K1).
  -
    exfalso. pose proof (CH2.leaves_all_sound _ _ _ PSZK.kinv_ok _ _ _ _ _ IL) as Q. unfold PSZK.kinv_chk in Q. rewrite K1 in Q. destruct Hpc as [-> | [-> | ->]]; discriminate Q.
Qed.

Lemma main : srealizes RSEGS SCFG (@PML.cfg fx R PML.PC_PARSE_SOME M model) K.
Proof.
  unfold PML.cfg. change PML.PC_PARSE_SOME with (CC.cp_pc G.cp0). rewrite <- LS.
  eapply (CH2.cert_sound3 L HI HIok (PB.LYI_ L LAY) (PB.LYE_ L LAY) (PmLayout.ly_ro L LAY) GT.NF E0 M model LBo sp G.HDECL W G.BLS Cred (PSI.STKF I) PSI.SCRP PSI.NF32 (PSI.U2 I) (PSI.W_OK I) (PSI.WRS_OK I)
            G.CPS K PML.fp_ok G.TAGS XI) with (i := 0%nat) (E := E0).
  - rewrite LS. exact FPM.
  - rewrite LS. exact Cut_psome_csrc_u.plans.
  - exact Cut_psome_csrc_u.tags_ok.
  - exact heap_ok3.
  - exact (PSB.goto_cred I).
  - exact (PSB.goto_xi I).
  - exact leaves.
  - reflexivity.
  - rewrite LS. exact (PSI.At0 I).
  -
    pose proof (PSI.UU I) as (U2 & U10 & U11 & U12 & U32 & U33 & U34 & U35 & U36 & U37 & U38 & U39 & U40 & U41 & U42 & U43 & U44 & U45 & U46 & U47 & U48).
    pose proof (PSI.NUM I) as (BRb & BRs & Hdb & Hdsb & A1 & A2 & A3 & N8 & N9 & N10 & N11 & N12 & N13 & N14 & N15 & N16 & N17 & N18 & N19 & N20 & N21 & N22 & N23).
    pose proof (PSI.WIN I) as (W0 & W1 & W2 & Hwd & W4).
    assert (Hden0 : CH2.den E0 (nth 0 G.BLS []) = PML.ps_blocks ps).
    { change (nth 0 G.BLS []) with [(EVar 37, APC.escale 2 (EVar 35)); (EVar 38, EVar 40)]. rewrite !PB.den_cons. change (CH2.den E0 []) with (@nil (Z * Z)). unfold PML.ps_blocks.
      fold (PSI.bptr I) (PSI.bcap I) (PSI.sb I) (PSI.scap I). rewrite PB.uv_escale. unfold PB.uv. cbn [edenot]. rewrite U35, U37, U38, U40, <- N8. rewrite Z.mod_small by lia. reflexivity. }
    split.
    + split; [exact (PSI.iHmo I)|]. split; [apply L5C.model_but_vm_refl|]. split; [apply CC.env_agree_refl|].
      split; [|split; [reflexivity | intros a _ _ Hd; exact Hd]].
      exists cr. split; [unfold CH2.cur; rewrite Hden0; exact (PSI.iHH I)|].
      apply (PSI.cred_of_blocks I 0 E0 cr ps Hden0); [destruct (PSI.iHWF I) as (_ & _ & _ & W4' & _); exact W4' | exact (PSI.iHPC I)].
    + unfold PSI.XI. split; [exact (PSI.DEF0 I)|]. split; [intros Q; exfalso; apply Q; reflexivity|]. split; [intros Q; vm_compute in Q; discriminate Q|].
      change (kind_of 0) with KInv. change (PSM2.vw 0) with (Some (PB4.PV2 (EVar 41) WEND (EVar 32) (EVar 42) (EVar 43) (EVar 44) (EVar 45) (EVar 46) (EVar 36) (EVar 38) (APC.eadd (EVar 38) (EVar 39)) (APC.eadd (EVar 38) (EVar 40)), EVar 37, APC.escale 2 (EVar 35))).
      exists (PML.ps_more ps), (PML.ps_done ps), (PML.ps_stack ps), (PML.ps_buf ps).
      pose proof (PSI.iHPA I) as HPA0. unfold PML.parser_at in HPA0.
      destruct HPA0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstr & _ & _ & _ & _ & Hstk & Hsl & _).
      destruct (PSB.FRZ I E0 (CC.env_agree_refl _ _)) as (_ & _ & _ & _ & F5 & F6 & F7 & _).
      assert (VSE : uv E0 (APC.eadd (EVar 38) (EVar 39)) = PSI.sb I + PSI.slen I) by (rewrite PB.uv_eadd; unfold PB.uv; cbn [edenot]; rewrite U38, U39; apply Z.mod_small; destruct BRs as (? & _ & _ & _ & ?); unfold hl_ceil in *; pose proof (PSI.SPF I) as (_ & _ & _ & S4 & _); lia).
      assert (VSC : uv E0 (APC.eadd (EVar 38) (EVar 40)) = PSI.sb I + PSI.scap I) by (rewrite PB.uv_eadd; unfold PB.uv; cbn [edenot]; rewrite U38, U40; apply Z.mod_small; destruct BRs as (? & _ & _ & _ & ?); unfold hl_ceil in *; pose proof (PSI.SPF I) as (_ & _ & _ & S4 & _); lia).
      assert (VCE : uv E0 (APC.escale 2 (EVar 35)) = PSI.bcap I) by (rewrite PB.uv_escale; unfold PB.uv; cbn [edenot]; rewrite U35, <- N8; apply Z.mod_small; lia).
      assert (Hps : PSI.ps_of (PB4.PV2 (EVar 41) WEND (EVar 32) (EVar 42) (EVar 43) (EVar 44) (EVar 45) (EVar 46) (EVar 36) (EVar 38) (APC.eadd (EVar 38) (EVar 39)) (APC.eadd (EVar 38) (EVar 40))) (EVar 37) (APC.escale 2 (EVar 35)) E0
                        (PML.ps_more ps) (PML.ps_done ps) (PML.ps_stack ps) (PML.ps_buf ps) = ps).
      { unfold PSI.ps_of. cbn [PB4.pv_st PB4.pv_sst PB4.pv_nst PB4.pv_level PB4.pv_sb PB4.pv_scend PB4.pv_wptr PB4.pv_wend]. rewrite VSC, VCE, F7. change (EVar 32) with SEG. rewrite F5.
        unfold PB.uv. cbn [edenot]. rewrite U41, U42, U43, U44, U37, U38.
        assert (Hwin : PB4.win_of (PSI.seg I) (PSI.wend I) = PML.ps_win ps).
        { unfold PB4.win_of, PSI.seg, PSI.wend, PSI.seg_of, PSI.wend_of. destruct (PML.ps_win ps) as [[p e]|] eqn:Hw; cbn [PSA.wincells fst snd]; [|reflexivity].
          destruct W4 as [[Q1 Q2]|(ch & Hch & Hc1 & Hc2 & (B0 & _))]; unfold PSI.seg, PSI.wend, PSI.seg_of, PSI.wend_of in *; rewrite Hw in *; cbn [PSA.wincells fst snd] in *.
          - pose proof (PSI.iHWIN I) as HWK. unfold PML.win_ok in HWK. rewrite Hw in HWK. destruct HWK as (ch & Hch & Hc1 & Hc2 & _).
            destruct (hio_wf L SCFG HI HIok _ _ _ _ (PSI.iHH I)) as (Hwf & _). destruct (Hwf (ch, 16384) ltac:(right; right; exact Hch)) as ((Q & _) & _). cbn [fst] in Q. lia.
          - destruct (Z.eqb_spec e 0); [lia | reflexivity]. }
        rewrite Hwin. unfold PSI.level, PSI.st0, PSI.sst0, PSI.nst0, PSI.bptr, PSI.sb, PSI.bcap, PSI.scap. destruct ps; cbn; f_equal; lia. }
      rewrite Hps. split.
      * unfold PSI.contents. cbn [PB4.pv_st PB4.pv_sb PB4.pv_send PB4.pv_scend PB4.pv_wptr PB4.pv_wend PB4.pv_size PB4.pv_more PB4.pv_done]. rewrite VSE, VSC, VCE, F7. change (EVar 32) with SEG. rewrite F5.
        unfold PB.uv. cbn [edenot]. rewrite U38, U36, U37, U45, U46, U42.
        split; [exact Hstk|]. split; [reflexivity|]. split; [unfold PSI.slen, PSI.scap in *; lia|]. split; [reflexivity|]. split; [lia|]. split; [reflexivity|]. split; [unfold PSI.size0, PSI.bcap in *; lia|].
        split; [intros _; destruct Hstr as ((_ & _ & _ & _ & Hb & _) & _); exact Hb | split; reflexivity].
      * split; [exact (PSI.iHLS I)|]. split; [exact (PSI.iHWF I)|]. split; [exact (PSI.iHBB I)|].
        split; [split; [split; [exact (PSI.iHLV I) | intros _; reflexivity] | intros Q; rewrite (PSI.iHmore I) in Q; discriminate Q]|].
        split; [intros [Q|[Q|[Q|Q]]]; discriminate Q | intros Q; discriminate Q].
  - exact (PSI.iHfp I).
Qed.
End Z.

Section Final.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.

Hypothesis SETEC_OK : PMS.set_ec_spec L.
Hypothesis POP_OK : PMS.pop_state_spec L.
Hypothesis PARENT_OK : PMS.parent_spec L.
Hypothesis VECPUSH_OK : PMS.vec_push_spec L HI.
Hypothesis PUSHB_OK : PMS.str_push_back_spec L HI.
Hypothesis SKIP_OK : PMS.skip_space_spec L HI PML.STRTOD_SCR_V.
Hypothesis BMEM_OK : PMS.begin_member_spec L HI PML.STRTOD_SCR_V.
Hypothesis BOBJ_OK : PMS.begin_object_spec L HI PML.STRTOD_SCR_V.
Hypothesis BARR_OK : PMS.begin_array_spec L HI PML.STRTOD_SCR_V.
Hypothesis EOBJ_OK : PMS.end_object_spec L HI PML.STRTOD_SCR_V.
Hypothesis EARR_OK : PMS.end_array_spec L HI PML.STRTOD_SCR_V.
Hypothesis NULL_OK : PMS.parse_null_spec L HI PML.STRTOD_SCR_V.
Hypothesis TRUE_OK : PMS.parse_true_spec L HI PML.STRTOD_SCR_V.
Hypothesis FALSE_OK : PMS.parse_false_spec L HI PML.STRTOD_SCR_V.
Hypothesis STRING_OK : PMS.parse_string_spec L HI PML.STRTOD_SCR_V.
Hypothesis NUMBER_OK : PMS.parse_number_spec L HI PML.STRTOD_SCR_V.
Hypothesis ENDINT_OK : PMS.end_integer_value_spec L HI PML.STRTOD_SCR_V.
Hypothesis ENDFRAC_OK : PMS.end_fraction_value_spec L HI PML.STRTOD_SCR_V.
Hypothesis VNULL_OK : PMS.visit_null_spec L VNULL.
Hypothesis VBOOL_OK : PMS.visit_bool_spec L VBOOL.

Theorem parse_some_ok : PMS.parse_some_spec L HI PML.STRTOD_SCR_V.
Proof.
  unfold PMS.parse_some_spec, PMS.ptrans, PMS.ptrans_g, PMS.ptrans_gb. intros LBo cr sp r P V E B kx bx g ps. unfold PML.cps_heap.
  intros fx R M model K HH Hmo HKnil Hfp (Hentry & ((Ha0 & Ha1 & Ha2) & Hmore) & HPA & (HWF & HLV) & HWIN & HBB & HVIS & HEC & HLS & HG & HPC & OP & OV & OE & AP1 & AP2 & AP3) Hcont.
  pose proof (PSB.pa_def _ _ _ HPA) as HdP.
  destruct (PB2.cell_exists M (P + 160) 8 ltac:(lia)) as (line0 & Rl & Hl); [eapply (L5.defined_sub _ _ _ _ _ HdP); cbn; lia|].
  destruct (PB2.cell_exists M (P + 168) 8 ltac:(lia)) as (pos0 & Rp & Hp); [eapply (L5.defined_sub _ _ _ _ _ HdP); cbn; lia|].
  assert (HWB : exists winb, L5.bytes_at RSEGS M (PSI.seg_of ps) winb /\ Z.of_nat (length winb) = PSI.wend_of ps - PSI.seg_of ps).
  { unfold PSI.seg_of, PSI.wend_of. pose proof HWIN as HW. unfold PML.win_ok in HW. pose proof HPA as HPA0. unfold PML.parser_at in HPA0.
    destruct HPA0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CW & _).
    destruct (PML.ps_win ps) as [[p e]|]; cbn [PSA.wincells fst snd]; [|exists []; split; [intros i Hi; cbn in Hi; lia | reflexivity]].
    destruct CW as (_ & _ & Hpe). destruct HW as (ch & Hch & C1 & C2 & Hwd).
    destruct (hio_wf L SCFG HI HIok _ _ _ _ HH) as (Hwf & _). destruct (Hwf (ch, 16384) ltac:(right; right; exact Hch)) as ((B0 & B1 & B2 & B3 & B4) & _). cbn [fst snd] in *.
    destruct Hentry as (_ & _ & _ & _ & Hstk). pose proof (L5C.stk_window _ _ _ _ Hstk) as (W1 & W2 & W3). unfold hl_ceil in B4.
    destruct (PB3.bytes_of_defined_r M (Z.to_nat (e - p)) p ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as (winb & Hwl & Hwb & _); [rewrite Z2Nat.id by lia; exact Hwd|].
    exists winb. split; [exact Hwb | rewrite Hwl; apply Z2Nat.id; lia]. }
  destruct HWB as (winb & Hwinb).
  set (I := @PSI.Inst SCFG_P L HI HIok LAY LBo cr sp r P V E B kx bx g ps fx R M model K HH Hmo HKnil Hfp Hentry Ha0 Ha1 Ha2 Hmore HPA HWF HLV HWIN HBB HVIS HEC HLS HG HPC OP OV OE AP1 AP2 AP3
                        line0 pos0 winb Hl Rl Hp Rp Hwinb Hcont).
  exact (main I FPM SETEC_OK POP_OK PARENT_OK VECPUSH_OK PUSHB_OK SKIP_OK BMEM_OK BOBJ_OK BARR_OK EOBJ_OK EARR_OK NULL_OK TRUE_OK FALSE_OK STRING_OK NUMBER_OK ENDINT_OK ENDFRAC_OK VNULL_OK VBOOL_OK).
Qed.
End Final.
End PSZ.

