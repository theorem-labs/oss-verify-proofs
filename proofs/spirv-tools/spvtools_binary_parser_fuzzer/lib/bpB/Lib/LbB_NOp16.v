(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil BMState BMem BCells BArr BExec BLFrame BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 BakeStackRep BllocRepX RtB_IMemset RtB_Td.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Bridge LbB_Conv LbB_Call LbB_DStat LbB_NBr LbB_NMc LbB_NLeaf LbB_NPc1 LbB_NLoops LbB_NSnp LbB_NKit LbB_NIf LbB_NDoUL LbB_NBack.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_DPdK LbB_PqK LbB_DRep LbB_DiagStmt LbB_PcStmt.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac StoreOk MemSplit Hoare ShapeAlg SRealizes MmapSim
  RefMemcpyLib LibIface LibEff LibMaskBits ZStores SymExec3 SymExec3Sound SymRun3 LibTail SumWalkTac.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContLib StrLib ContStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag Require Import DiagTac NumTac NumLeaf.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S. Import LbB_NLoops.NDig.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Notation SEGS := asegs (only parsing).
Local Ltac xms H := first [exact H | apply msteps_bridge; exact H].

Definition OP_ENTRY : Z := 0x124e6c.
Definition OP_RET : Z := 0x124f88.
Definition OP_RETPC : Z := 0x124fd0.
Definition OP_FR : Z := 80.

Definition op_xok (xenc : Z) : Prop := 0 <= xenc < 2 ^ 16.

Definition kn_num (fill : Z) : list kentry :=
  [KWr (SA (EVar 2) (-128)) (ELit 128);
   KWr (SA (EVar 10) 0) (ELit 392);
   KRange (EVar 2) (2 ^ 33 + 128) (2 ^ 47); KRange (EVar 10) 0x6e8000 (2 ^ 47 - 392);
   KDisj (SA (EVar 10) 0) (ELit 392) (SA (EVar 2) (-128)) (ELit 128);
   KImg 0x17e000 0x186000;
   KWord (SA (EVar 10) 0) (N.to_nat 8) (ELit LbB_DRep.VT_OS_A);
   KWord (SA (EVar 10) 8) (N.to_nat 8) (ELit LbB_DRep.VT_SB_A);
   KWord (SA (EVar 10) 120) (N.to_nat 4) (EVar 32);
   KWord (SA (EVar 10) 136) (N.to_nat 8) (ELit 0);
   KWord (SA (EVar 10) 144) (N.to_nat 4) (ELit 0);
   KWord (SA (EVar 10) 152) (N.to_nat 8) (EAlu ALU_ADD (EVar 10) (ELit 8));
   KWord (SA (EVar 10) 160) (N.to_nat 8) (ELit LbB_DRep.LOC_IMP_A);
   KWord (SA (EVar 10) 248) (N.to_nat 8) (ELit 0);
   KWord (SA (EVar 10) 256) (N.to_nat 4) (ELit fill);
   KWord (SA (ELit 0) A_CTYPE_ID) (N.to_nat 8) (ELit (2 ^ 64 - 1));
   KWord (SA (ELit 0) (A_CTYPE_ID + 8)) (N.to_nat 4) (ELit 3);
   KWord (SA (ELit 0) (LbB_DRep.LOC_IMP_A + 16)) (N.to_nat 8) (ELit FACETS_BEG);
   KWord (SA (ELit 0) (LbB_DRep.LOC_IMP_A + 24)) (N.to_nat 8) (ELit FACETS_END);
   KWord (SA (ELit 0) (FACETS_BEG + 16)) (N.to_nat 8) (ELit A_CTYPE_OBJ);
   KWord (SA (ELit 0) A_CTYPE_OBJ) (N.to_nat 8) (ELit VT_CTYPE);
   KWord (SA (ELit 0) A_NUMPUT_ID) (N.to_nat 8) (ELit (2 ^ 64 - 1));
   KWord (SA (ELit 0) (A_NUMPUT_ID + 8)) (N.to_nat 4) (ELit 15);
   KWord (SA (ELit 0) (FACETS_BEG + 112)) (N.to_nat 8) (ELit A_NUMPUT_OBJ);
   KWord (SA (ELit 0) A_NUMPUT_OBJ) (N.to_nat 8) (ELit VT_NUMPUT)].

Ltac kabsN DT := kabsA DT.

Section Op.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Variables (F : bvmap 5 word) (fc : bv 32).
  Variables (R : bvmap 5 word) (M : mem) (sp ds xenc fl fill ret lo shi gd : Z).
  Hypothesis PRE : npre R M sp ds xenc fl fill ret lo shi gd OP_FR.
  Hypothesis XOK : op_xok xenc.

  Definition SVOP : list word :=
    [Z_to_bv 64 ret; getr R 8%bv; getr R 9%bv; getr R 18%bv; getr R 19%bv; getr R 20%bv; getr R 21%bv; Z_to_bv 64 LbB_DRep.LOC_IMP_A; Z_to_bv 64 ds].

  Record atdp (R1 : bvmap 5 word) (M1 : mem) (sv21 : word) (v : Z) : Prop := ATDP {
    ad_st : stores_in (fun a => zwin (sp - 128) sp a \/ zwin (ds + 256) (ds + 260) a) M M1;
    ad_fill : fld SEGS M1 (ds + 256) 4 32;
    ad_sv : slots SEGS M1 sp SVOP;
    ad_r1 : getr R1 1%bv = Z_to_bv 64 OP_RET; ad_r2 : getr R1 2%bv = Z_to_bv 64 (sp - 80);
    ad_r3 : getr R1 3%bv = getr R 3%bv; ad_r4 : getr R1 4%bv = getr R 4%bv;
    ad_r8 : getr R1 8%bv = Z_to_bv 64 ds; ad_r11 : getr R1 11%bv = Z_to_bv 64 (ds + 8); ad_r12 : getr R1 12%bv = Z_to_bv 64 (ds + 112);
    ad_r13 : getr R1 13%bv = Z_to_bv 64 32; ad_r14 : getr R1 14%bv = Z_to_bv 64 v; ad_v : 0 <= v < 2 ^ 64; ad_r21 : getr R1 21%bv = sv21;
    ad_cs : forall r, In r [22; 23; 24; 25; 26; 27]%bv -> getr R1 r = getr R r;
    ad_rf : rfull R1 }.

  Lemma op_pre : exists R1 M1 sv21 v,
    BExec.msteps SEGS (@mkst (PropExec.mkFP F fc) R (Z_to_bv 64 OP_ENTRY) M (seg_rom SEGS)) (@mkst (PropExec.mkFP F fc) R1 (Z_to_bv 64 A_NUMPUT_UL) M1 (seg_rom SEGS))
    /\ atdp R1 M1 sv21 v.
  Proof.
    destruct PRE as [Hra Hret Hretr Hsp Htp Ha0 Ha1 Hslo Hshi Hal HD Hds DJds Gdef APP Gvt F0 Ifl Iflr Iwid Ist Irdbuf Iloc Itie Ifill Ifillr DT FCAN Hgd RF NI STK CEIL LOS SHI].
    destruct Hds as (Hds0 & Hds1 & Hds2). unfold AIMG_TOP in Hds0. unfold NWIN, OP_FR in *. unfold op_xok in XOK.
    pose proof NI as (ROC & _ & _ & RRC).
    set (E := Eseed R [Z_to_bv 64 fl; Z_to_bv 64 fill]).
    assert (HR : regs_ok E sr_id R) by (apply regs_ok_seed).
    assert (HK : know_ok SEGS E M (kn_num fill)).
    { unfold kn_num. repeat apply Forall_cons; try apply Forall_nil.
      - eapply (kwr_of_mdef _ _ _ _ sp (-128) 128); [evs; exact Hsp | lia | lia | lia | lia | eapply mdef_sub; [exact HD | lia | lia]].
      - eapply (kwr_of_mdef _ _ _ _ ds 0 392); [evs; exact Ha0 | lia | lia | lia | lia | replace (ds + 0) with ds by lia; exact Gdef].
      - krv Hsp. - krv Ha0.
      - kdjx Ha0 Hsp ds 392 sp 128. lia.
      - apply kimg_relro. exact RRC.
      - eapply (kword_var _ _ _ _ ds); [eapply fld_cellw; [fld_fix Gvt | unfold LbB_DRep.VT_OS_A; cbn; lia] | cbn; lia | evs; exact Ha0 | lia | lia | cbn; lia | evs; reflexivity ].
      - eapply (kword_var _ _ _ _ ds); [eapply fld_cellw; [fld_fix F0 | unfold LbB_DRep.VT_SB_A; cbn; lia] | cbn; lia | evs; exact Ha0 | lia | lia | cbn; lia | evs; reflexivity ].
      - eapply (kword_var _ _ _ _ ds); [eapply fld_cellw; [fld_fix Ifl | destruct Iflr as [-> | ->]; unfold LbB_DiagStmt.DS_FL0, LbB_DiagStmt.DS_FLHEX; cbn; lia] | cbn; lia | evs; exact Ha0 | lia | lia | cbn; lia | evs; reflexivity ].
      - kwv Iwid Ha0.
      - kwv Ist Ha0.
      - eapply (kword_var _ _ _ _ ds); [eapply fld_cellw; [fld_fix Irdbuf | cbn; lia] | cbn; lia | evs; exact Ha0 | lia | lia | cbn; lia | evs ].
        regsub. rewrite alu_Z by lia. cbn [zar]. rewrite Z.mod_small by lia. reflexivity.
      - eapply (kword_var _ _ _ _ ds); [eapply fld_cellw; [fld_fix Iloc | unfold LbB_DRep.LOC_IMP_A; cbn; lia] | cbn; lia | evs; exact Ha0 | lia | lia | cbn; lia | evs; reflexivity ].
      - kwv Itie Ha0.
      - eapply (kword_var _ _ _ _ ds); [eapply fld_cellw; [fld_fix Ifill | destruct Ifillr as [-> | ->]; cbn; lia] | cbn; lia | evs; exact Ha0 | lia | lia | cbn; lia | evs; reflexivity ].
      - kabsN DT. - kabsN DT. - kabsN DT. - kabsN DT. - kabsN DT. - kabsN DT.
      - kabsN DT. - kabsN DT. - kabsN DT. - kabsN DT. }
    destruct Ifillr as [Hf | Hf]; rewrite Hf in HK.
    -
      xrun_at HR HK (PropExec.mkFP F fc) OP_ENTRY (seg_rom SEGS) 400%nat [A_NUMPUT_UL; OP_RETPC] (SCR [] [] []) 60%N.
      { scs_auto. }
      clear HK. rename HR' into HR1. rename R' into R1. rename Hms into Hms1. wnorm_inA Hms1.
      lazymatch type of Hms1 with msteps _ _ (mkst _ _ ?mm _) => set (M1 := mm) in Hms1 end.
      exists R1, M1, (Z_to_bv 64 (ds + 112)), xenc. split; [xms Hms1|]. constructor.
      + subst M1. stores_tower.
      + pose proof (fld4_of_bytes M1 (ds + 256) 32 0 0 0 32 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as FB.
        apply FB; [ | | | | vm_compute; reflexivity];
          unfold fld; subst M1; peel;
          lazymatch goal with |- rdn _ (wbytes _ (Z_to_bv 64 ?b) _) (Z_to_bv 64 ?a) _ = _ => replace (Z_to_bv 64 a) with (Z_to_bv 64 b) by (f_equal; lia) end;
          apply ContLib.rdn_wbytes_hit1; rewrite u64_of_Z by lia; lia.
      + subst M1. unfold SVOP. slots_tower.
      + regval HR1 (1%bv : reg) OP_RET V. exact V. + regval HR1 (2%bv : reg) (sp - 80) V. exact V.
      + kept_chain HR1. + kept_chain HR1.
      + regval HR1 (8%bv : reg) ds V. exact V. + regval HR1 (11%bv : reg) (ds + 8) V. exact V. + regval HR1 (12%bv : reg) (ds + 112) V. exact V.
      + regval HR1 (13%bv : reg) 32 V. exact V. +   regval HR1 (14%bv : reg) xenc V. exact V. +   clear - XOK; unfold op_xok in XOK; lia. + regval HR1 (21%bv : reg) (ds + 112) V. exact V.
      + intros r Hr. cbn in Hr. repeat (destruct Hr as [<-|Hr]; [kept_chain HR1|]). destruct Hr.
      + exact (msteps_full asegs _ _ Hms1 RF).
    -
      xrun_at HR HK (PropExec.mkFP F fc) OP_ENTRY (seg_rom SEGS) 400%nat [A_NUMPUT_UL; OP_RETPC] (SCR [] [] []) 60%N.
      { scs_auto. }
      clear HK. rename HR' into HR1. rename R' into R1. rename Hms into Hms1. wnorm_inA Hms1.
      lazymatch type of Hms1 with msteps _ _ (mkst _ _ ?mm _) => set (M1 := mm) in Hms1 end.
      exists R1, M1, (getr R 21%bv), xenc. split; [xms Hms1|]. constructor.
      + subst M1. stores_tower.
      + rewrite <- Hf. eapply fld_agree; [lia | cbn; lia | exact Ifill |].
        assert (STx : stores_in (zwin (sp - 128) sp) M M1) by (subst M1; stores_tower).
        eapply stores_in_agree; [exact STx|]. intros a Ha. unfold zwin in *. cbn in Ha. lia.
      + subst M1. unfold SVOP. slots_tower.
      + regval HR1 (1%bv : reg) OP_RET V. exact V. + regval HR1 (2%bv : reg) (sp - 80) V. exact V.
      + kept_chain HR1. + kept_chain HR1.
      + regval HR1 (8%bv : reg) ds V. exact V. + regval HR1 (11%bv : reg) (ds + 8) V. exact V. + regval HR1 (12%bv : reg) (ds + 112) V. exact V.
      + regval HR1 (13%bv : reg) 32 V. exact V. +   regval HR1 (14%bv : reg) xenc V. exact V. +   clear - XOK; unfold op_xok in XOK; lia. + kept_chain HR1.
      + intros r Hr. cbn in Hr. repeat (destruct Hr as [<-|Hr]; [kept_chain HR1|]). destruct Hr.
      + exact (msteps_full asegs _ _ Hms1 RF).
  Qed.

  #[local] Notation nmidU := (fun sv9 sv18 sv19 sv20 sv21 sv22 sv23 =>
     nmid R M sp ds OP_FR PADRA_UL OP_RET (Z_to_bv 64 32) SVOP sv9 sv18 sv19 sv20 sv21 sv22 sv23).

  Lemma ex_a : exists nc R2 M2 sv9 sv18 sv19 sv20 sv21,
    BExec.msteps SEGS (@mkst (PropExec.mkFP F fc) R (Z_to_bv 64 OP_ENTRY) M (seg_rom SEGS)) (@mkst (PropExec.mkFP F fc) R2 (Z_to_bv 64 LbB_PcStmt.AXSP) M2 (seg_rom SEGS))
    /\ nmidU sv9 sv18 sv19 sv20 sv21 (getr R 22%bv) (getr R 23%bv) nc R2 M2.
  Proof.
    destruct op_pre as (R1 & M1 & sv21 & v & Hms1 & AD).
    destruct AD as [ST1 FFILL SV1 X1 X2 X3 X4 X8 X11 X12 X13 X14 Hv X21 XCS RF1].
    destruct PRE as [Hra Hret Hretr Hsp Htp Ha0 Ha1 Hslo Hshi Hal HD Hds DJds Gdef APP Gvt F0 Ifl Iflr Iwid Ist Irdbuf Iloc Itie Ifill Ifillr DT FCAN Hgd RF NI STK CEIL LOS SHI].
    destruct Hds as (Hds0 & Hds1 & Hds2). unfold AIMG_TOP in Hds0. unfold NWIN, OP_FR in *.
    pose proof aceil_facts as ((AF1 & AF2) & _).
    set (W1 := fun a => zwin (sp - 128) sp a \/ zwin (ds + 256) (ds + 260) a) in ST1.
    assert (W1hi : forall a, W1 a -> 0x6e8000 <= a) by (intros a [Ha|Ha]; unfold zwin in Ha; lia).
    assert (HD1 : mdef M1 (sp - 8272) 8272) by (eapply stores_in_mdef; [exact ST1 | exact HD]).
    assert (T01 : forall a (k : nat) vv, (a + Z.of_nat k <= ds + 256 \/ ds + 260 <= a) -> (a + Z.of_nat k <= sp - 128 \/ sp <= a) -> 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> fld SEGS M a k vv -> fld SEGS M1 a k vv).
    { intros a k vv H1 H2 H3 H4 HF. eapply (fld_via_stores SEGS); [exact ST1 | intros y Hy; unfold W1, zwin; lia | lia | lia | exact HF]. }
    assert (DT1 : dstat_rs D_DIAG_A M1) by (eapply dstat_hi; [exact DT | exact ST1 | exact W1hi]).
    assert (FCAN1 : fld SEGS M1 A_CANARY 8 gd).
    { eapply (fld_via_stores SEGS); [exact ST1 | intros y Hy K; pose proof (W1hi _ K); unfold A_CANARY, ASSPGUARD in *; lia | unfold A_CANARY, ASSPGUARD; lia | unfold A_CANARY, ASSPGUARD; cbn; lia | exact FCAN]. }
    assert (NI1 : ninv lo shi M1).
    { eapply (ninv_obj lo shi M M1 W1 ds 392 NI ST1 APP); [lia|]. intros a [Ha|Ha]; unfold zwin in Ha; [left | right]; lia. }
    assert (STK1 : stk asegs M1 lo (sp - 80)).
    { eapply LbB_PqK.stk_keep; [exact (proj1 (stk_split asegs M lo (sp - 80) sp STK ltac:(clear - LOS; lia)))
        | eapply (munch_of_stores_in _ [(sp - 128, sp); (ds + 256, ds + 260)]); [exact ST1 | intros y Hy; cbv beta in Hy; cbn [outside fst snd]; unfold W1, zwin in Hy; clear - Hy; lia]
        | exact (wmono_of_stores_in _ _ _ ST1) | clear - CEIL AF1; unfold AIMG_TOP; lia]. }
    assert (G120 : fld SEGS M1 (ds + 120) 4 fl) by (apply (T01 (ds + 120) 4%nat fl); [cbn; lia | cbn; lia | lia | cbn; lia | exact Ifl]).
    assert (G160 : fld SEGS M1 (ds + 160) 8 LbB_DRep.LOC_IMP_A) by (apply (T01 (ds + 160) 8%nat LbB_DRep.LOC_IMP_A); [cbn; lia | cbn; lia | lia | cbn; lia | exact Iloc]).
    assert (G136 : fld SEGS M1 (ds + 136) 8 0) by (apply (T01 (ds + 136) 8%nat 0); [cbn; lia | cbn; lia | lia | cbn; lia | exact Iwid]).
    assert (G8 : fld SEGS M1 (ds + 8) 8 LbB_DRep.VT_SB_A) by (apply (T01 (ds + 8) 8%nat LbB_DRep.VT_SB_A); [cbn; lia | cbn; lia | lia | cbn; lia | exact F0]).
    assert (HD80 : mdef M1 (sp - 80 - 8192) 8192) by (eapply mdef_sub; [exact HD1 | lia | lia]).
    assert (Hds3 : 2 ^ 16 <= ds /\ ds + 392 <= 2 ^ 47 /\ ds mod 8 = 0) by (split; [lia | split; [lia | exact Hds2]]).
    assert (X4' : getr R1 4%bv = Z_to_bv 64 ATP) by (rewrite X4; exact Htp).
    pose proof (doput_ul H HH F fc gd Hgd R1 M1 (sp - 80) ds v fl OP_RET lo shi (Z_to_bv 64 32)) as DP.
    repeat lazymatch type of DP with (exists _, _) => fail | forall _ : ?T, _ =>
      specialize (DP ltac:(first [eassumption | reflexivity | unfold OP_RET; lia | mlia | clear - LOS; lia | clear - SHI; lia | clear - DJds; lia])) end.
    destruct DP as (nc & R2 & M2 & HmsD & DPM).
    destruct DPM as [ST12 TD2 SV2 PSV2 Y1 Y2 Y3 Y4 Y8 Y9 Y10 Y11 Y12 Y19 YCS Hnc RF2 NI2 STK2].
    rewrite X8, X21 in SV2.
    exists nc, R2, M2, (getr R1 9%bv), (getr R1 18%bv), (getr R1 19%bv), (getr R1 20%bv), sv21.
    split; [eapply BExec.msteps_trans; [exact Hms1 | exact HmsD]|].
    cbv beta. rewrite <- (XCS 22%bv ltac:(inl)), <- (XCS 23%bv ltac:(inl)).
    constructor; try unfold NWIN.
    - eapply (stores_in_join _ _ _ M M1 M2); [exact ST1 | exact ST12 | ..]; intros a Ha; cbv beta in *; unfold W1, zwin in *; lia.
    - eapply (fld_via_stores SEGS); [exact ST12 | intros y Hy; cbv beta; unfold zwin, ATDLOC; cbn in Hy; lia | lia | cbn; lia | exact FFILL].
    - eapply slots_agree; [exact SV1 | cbn; lia | lia | cbn [SVOP length Z.of_nat Pos.of_succ_nat Pos.succ Pos.mul Z.mul]].
      eapply stores_in_agree; [exact ST12|]. intros a Ha. cbv beta. unfold zwin, ATDLOC in *. lia.
    - exact SV2.
    - exact PSV2.
    - exact Y1. - exact Y2.
    - rewrite Y3; exact X3. - rewrite Y4; exact X4.
    - exact Y8. - exact Y9. - exact Y10. - exact Y11. - exact Y12. - exact Y19.
    - intros r Hr. rewrite (YCS r Hr). apply XCS. cbn in Hr |- *. tauto.
    - exact Hnc.
    - exact RF2.
    - exact TD2.
  Qed.

  Lemma op_tail : forall (R' R3 : bvmap 5 word) (M1 M3 : mem) sv9 sv18 sv19 sv20 sv21,
    natop sp ds OP_FR sv9 sv18 sv19 sv20 sv21 (getr R 22%bv) (getr R 23%bv) R' R3 ->
    getr R' 3%bv = getr R 3%bv -> getr R' 4%bv = getr R 4%bv -> (forall r, In r [24; 25; 26; 27]%bv -> getr R' r = getr R r) ->
    slots SEGS M1 sp SVOP -> agree_on (zwin (sp - 80) sp) M1 M3 ->
    mdef M3 (sp - 8272) 8272 -> relro_clear M3 ->
    fld SEGS M3 ds 8 LbB_DRep.VT_OS_A -> fld SEGS M3 (ds + 120) 4 fl -> fld SEGS M3 (ds + 144) 4 0 -> fld SEGS M3 (ds + 152) 8 (ds + 8) ->
    exists R4 M4,
      BExec.msteps SEGS (@mkst (PropExec.mkFP F fc) R3 (Z_to_bv 64 OP_RET) M3 (seg_rom SEGS)) (@mkst (PropExec.mkFP F fc) R4 (Z_to_bv 64 ret) M4 (seg_rom SEGS))
      /\ stores_in (zwin (sp - 96) (sp - 80)) M3 M4
      /\ getr R4 1%bv = Z_to_bv 64 ret /\ getr R4 2%bv = Z_to_bv 64 sp /\ getr R4 10%bv = Z_to_bv 64 ds
      /\ (forall r, In r NCS -> getr R4 r = getr R r) /\ rfull R4.
  Proof.
    intros Rq R3 M1 M3 sv9 sv18 sv19 sv20 sv21 [Y2 Y3 Y4 Y10 Y8 Y9 Y18 Y19 Y20 Y21 Y22 Y23 YCS RF3] K3 K4 KCS SL1 AG13 HD3 RRC3 Gvt Ifl Ist Irdbuf.
    destruct PRE as [Hra Hret Hretr Hsp Htp Ha0 Ha1 Hslo Hshi Hal HD Hds DJds Gdef APP _ _ _ Iflr _ _ _ _ _ _ _ DT FCAN Hgd RF NI STK CEIL LOS SHI].
    destruct Hds as (Hds0 & Hds1 & Hds2). unfold AIMG_TOP in Hds0. unfold NWIN, OP_FR in *.
    assert (SL3 : slots SEGS M3 sp SVOP).
    { eapply slots_agree; [exact SL1 | cbn; lia | lia | cbn [SVOP length Z.of_nat Pos.of_succ_nat Pos.succ Pos.mul Z.mul]].
      eapply agree_on_weaken; [exact AG13|]. intros a Ha. unfold zwin in *. lia. }
    set (E3 := Eseed R3 [Z_to_bv 64 ret; getr R 8%bv; getr R 9%bv; getr R 18%bv; getr R 19%bv; getr R 20%bv; getr R 21%bv; Z_to_bv 64 fl]).
    assert (HR3 : regs_ok E3 (srs sr_id [(10%bv : reg, EAlu ALU_ADD (EVar 8) (ELit 8))]) R3) by srs_ok.
    assert (HK3 : know_ok SEGS E3 M3
      [KWr (SA (EVar 2) (-16)) (ELit 16); KRange (EVar 2) (2 ^ 33 + 16) (2 ^ 47 - 80); KRange (EVar 8) 0x6e8000 (2 ^ 47 - 392);
       KDisj (SA (EVar 8) 0) (ELit 392) (SA (EVar 2) (-16)) (ELit 16);
       KImg 0x17e000 0x186000;
       KWord (SA (EVar 2) 72) (N.to_nat 8) (EVar 32); KWord (SA (EVar 2) 64) (N.to_nat 8) (EVar 33); KWord (SA (EVar 2) 56) (N.to_nat 8) (EVar 34);
       KWord (SA (EVar 2) 48) (N.to_nat 8) (EVar 35); KWord (SA (EVar 2) 40) (N.to_nat 8) (EVar 36); KWord (SA (EVar 2) 32) (N.to_nat 8) (EVar 37);
       KWord (SA (EVar 2) 24) (N.to_nat 8) (EVar 38); KWord (SA (EVar 2) 8) (N.to_nat 8) (EVar 8);
       KWord (SA (EVar 8) 0) (N.to_nat 8) (ELit LbB_DRep.VT_OS_A); KWord (SA (EVar 8) 120) (N.to_nat 4) (EVar 39);
       KWord (SA (EVar 8) 144) (N.to_nat 4) (ELit 0); KWord (SA (EVar 8) 152) (N.to_nat 8) (EAlu ALU_ADD (EVar 8) (ELit 8))]).
    { repeat apply Forall_cons; try apply Forall_nil.
      - eapply (kwr_of_mdef _ _ _ _ (sp - 80) (-16) 16); [evs; exact Y2 | lia | lia | lia | lia | eapply mdef_sub; [exact HD3 | lia | lia]].
      - krv Y2. - krv Y8.
      - kdjx Y8 Y2 ds 392 (sp - 80) 16. lia.
      - apply kimg_relro. exact RRC3.
      - kwe (SL3 0%nat ltac:(cbn; lia)) Y2. - kwe (SL3 1%nat ltac:(cbn; lia)) Y2. - kwe (SL3 2%nat ltac:(cbn; lia)) Y2.
      - kwe (SL3 3%nat ltac:(cbn; lia)) Y2. - kwe (SL3 4%nat ltac:(cbn; lia)) Y2. - kwe (SL3 5%nat ltac:(cbn; lia)) Y2.
      - kwe (SL3 6%nat ltac:(cbn; lia)) Y2. - kwe (SL3 8%nat ltac:(cbn; lia)) Y2.
      - eapply (kword_var _ _ _ _ ds); [eapply fld_cellw; [fld_fix Gvt | unfold LbB_DRep.VT_OS_A; cbn; lia] | cbn; lia | evs; exact Y8 | lia | lia | cbn; lia | evs; reflexivity ].
      - eapply (kword_var _ _ _ _ ds); [eapply fld_cellw; [fld_fix Ifl | destruct Iflr as [-> | ->]; unfold LbB_DiagStmt.DS_FL0, LbB_DiagStmt.DS_FLHEX; cbn; lia] | cbn; lia | evs; exact Y8 | lia | lia | cbn; lia | evs; reflexivity ].
      - kwv Ist Y8.
      - eapply (kword_var _ _ _ _ ds); [eapply fld_cellw; [fld_fix Irdbuf | cbn; lia] | cbn; lia | evs; exact Y8 | lia | lia | cbn; lia | evs ].
        regsub. rewrite alu_Z by lia. cbn [zar]. rewrite Z.mod_small by lia. reflexivity. }
    xrun_at HR3 HK3 (PropExec.mkFP F fc) OP_RET (seg_rom SEGS) 100%nat [OP_RETPC] (SCR [true] [] []) 40%N.
    { repeat apply Forall_cons; try apply Forall_nil.
      cbn [sc_denot]. evs. destruct Iflr as [-> | ->]; vm_compute; reflexivity. }
    clear HK3. rename HR' into HR4. rename R' into R4. rename Hms into Hms4. wnorm_inA Hms4.
    lazymatch type of Hms4 with msteps _ _ (mkst _ _ ?mm _) => set (M4 := mm) in Hms4 end.
    regval HR4 (1%bv : reg) ret V1. regval HR4 (10%bv : reg) ds V10.
    pose proof (@ret_at (PropExec.mkFP F fc) SEGS OP_RETPC R4 M4 (seg_rom SEGS) (Z_to_bv 64 ret) ltac:(vm_refl_bv) V1 Hret) as Hms5.
    exists R4, M4. split; [eapply BExec.msteps_trans; [xms Hms4 | xms Hms5]|].
    split; [subst M4; stores_tower|].
    split; [exact V1|]. split; [regval HR4 (2%bv : reg) sp X; exact X|]. split; [exact V10|].
    split; [| exact (msteps_full asegs _ _ Hms4 RF3)].
    intros r Hr. unfold NCS in Hr. cbn in Hr.
    destruct Hr as [<-|Hr]; [kept_chain HR4; rewrite Y3; exact K3|].
    destruct Hr as [<-|Hr]; [kept_chain HR4; rewrite Y4; exact K4|].
    destruct Hr as [<-|Hr]; [rreg HR4 (8%bv : reg) X; rewrite X; reflexivity|].
    destruct Hr as [<-|Hr]; [rreg HR4 (9%bv : reg) X; rewrite X; reflexivity|].
    destruct Hr as [<-|Hr]; [rreg HR4 (18%bv : reg) X; rewrite X; reflexivity|].
    destruct Hr as [<-|Hr]; [rreg HR4 (19%bv : reg) X; rewrite X; reflexivity|].
    destruct Hr as [<-|Hr]; [rreg HR4 (20%bv : reg) X; rewrite X; reflexivity|].
    destruct Hr as [<-|Hr]; [rreg HR4 (21%bv : reg) X; rewrite X; reflexivity|].
    destruct Hr as [<-|Hr]; [kept_chain HR4; rewrite Y22; reflexivity|].
    destruct Hr as [<-|Hr]; [kept_chain HR4; rewrite Y23; reflexivity|].
    repeat (destruct Hr as [<-|Hr]; [kept_chain HR4 YCS KCS|]). destruct Hr.
  Qed.

  Lemma ex_b : forall nc R1 M1 R' M' sv9 sv18 sv19 sv20 sv21,
    nmidU sv9 sv18 sv19 sv20 sv21 (getr R 22%bv) (getr R 23%bv) nc R1 M1 ->
    nback sp ds fl lo shi OP_FR nc R1 M1 R' M' ->
    exists R4 M4,
      BExec.msteps SEGS (@mkst (PropExec.mkFP F fc) R' (Z_to_bv 64 A_PAD_XS_RET) M' (seg_rom SEGS)) (@mkst (PropExec.mkFP F fc) R4 (Z_to_bv 64 ret) M4 (seg_rom SEGS))
      /\ nfin R sp ds ret OP_FR M' R4 M4.
  Proof.
    intros nc R1 M1 R' M' sv9 sv18 sv19 sv20 sv21 NM NB. cbv beta in NM.
    pose proof PRE as [Hra Hret Hretr Hsp Htp Ha0 Ha1 Hslo Hshi Hal HD Hds DJds Gdef APP Gvt F0 Ifl Iflr Iwid Ist Irdbuf Iloc Itie Ifill Ifillr DT FCAN Hgd RF NI STK CEIL LOS SHI].
    destruct (stage_back F fc R M sp ds fl lo shi OP_FR PADRA_UL OP_RET DPU_RETPC (Z_to_bv 64 32) SVOP sv9 sv18 sv19 sv20 sv21 (getr R 22%bv) (getr R 23%bv)
                ltac:(left; reflexivity) ltac:(left; split; reflexivity) ltac:(unfold OP_RET; lia) ltac:(apply bv_eq; vm_compute; reflexivity)
                Hslo Hshi Hal Hds DJds nc R1 M1 R' M' NM NB) as (R3 & Hms3 & NA).
    pose proof NM as [ST1 FFILL SLop SL1 SL2 X1 X2 X3 X4 X8 X9 X10 X11 X12 X19 XCS Hnc RF1 TD1].
    pose proof NB as [KEPT R'10 RF' AGS HDS' HDM' Gvt' Gfl' Gst' Grdb' NI'].
    pose proof NI' as (ROC' & _ & _ & RRC').
    destruct Hds as (Hds0 & Hds1 & Hds2). unfold AIMG_TOP in Hds0. unfold NWIN, OP_FR in *.
    set (M3 := wbytes M' (Z_to_bv 64 (ds + 136)) (word_to_le_bytes 8 (Z_to_bv 64 0))) in *.
    assert (ST3 : stores_in (zwin (ds + 136) (ds + 144)) M' M3) by (subst M3; stores_tower).
    assert (T3 : forall a (k : nat) v, (a + Z.of_nat k <= ds + 136 \/ ds + 144 <= a) -> 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> fld SEGS M' a k v -> fld SEGS M3 a k v).
    { intros a k v H1 H2 H3 HF. eapply (fld_via_stores SEGS); [exact ST3 | intros y Hy; unfold zwin; lia | lia | lia | exact HF]. }
    destruct (op_tail R' R3 M1 M3 sv9 sv18 sv19 sv20 sv21 NA) as (R4 & M4 & Hms4 & ST4 & V1 & V2 & V10 & VCS & RF4).
    - rewrite (KEPT 3%bv) by (unfold NKEPT; inl). exact X3.
    - rewrite (KEPT 4%bv) by (unfold NKEPT; inl). exact X4.
    - intros r Hr. rewrite (KEPT r) by (unfold NKEPT; cbn in Hr |- *; tauto). exact (XCS r Hr).
    - exact SLop.
    - intros a Ha. rewrite (proj1 ST3 (Z_to_bv 64 a)) by (rewrite u64_of_Z by (unfold zwin in Ha; lia); unfold zwin in *; lia).
      apply AGS. unfold zwin in *. lia.
    - eapply stores_in_mdef; [exact ST3 | exact HDS'].
    - eapply relro_clear_hi; [exact RRC' | exact ST3 | intros a Ha; unfold zwin in Ha; lia].
    - apply T3; [cbn; lia | lia | cbn; lia | exact Gvt'].
    - apply T3; [cbn; lia | lia | cbn; lia | exact Gfl'].
    - apply T3; [cbn; lia | lia | cbn; lia | exact Gst'].
    - apply T3; [cbn; lia | lia | cbn; lia | exact Grdb'].
    - exists R4, M4. split; [eapply BExec.msteps_trans; [exact Hms3 | exact Hms4]|].
      constructor; try unfold NWIN.
      + eapply (stores_in_join _ _ _ M' M3 M4); [exact ST3 | exact ST4 | ..]; intros a Ha; unfold zwin in *; lia.
      + eapply (fld_via_stores SEGS); [exact ST4 | intros y Hy; unfold zwin; lia | lia | cbn; lia |].
        unfold fld. subst M3. peel.
      + exact V1.
      + exact V2.
      + exact V10.
      + exact VCS.
      + exact RF4.
  Qed.
End Op.
