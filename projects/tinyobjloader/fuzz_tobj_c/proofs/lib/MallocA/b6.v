(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b5.
From Stdlib Require FunctionalExtensionality.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_instG ax bl CDepotCall.

(* [comment removed for export] *)
Module SegQF_ri.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rm"; "valuation"; "rl"; "rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "view"; "cell_ok"; "mkACell"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "of_nat"; "pow"; "to_nat"; "@Corelib.Init.Datatypes"; "list"; "length"; "bool"; "true"; "Some"; "nat"; "option"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_cache_inited"; "class_state"; "aa_cls"; "cs_free_array"; "aa_geom"; "ag_spacebeg"; "cs_allocated_user"; "cs_cache"; "cs_empty"; "cs_mapped_free_array"; "cs_mapped_user"; "list_upd"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ"; "K0"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2"; "cls_of"; "@Corelib.Lists.ListDef"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "IMG_LO"; "RI_allocated_meta"; "RI_allocated_user"; "RI_exhausted"; "RI_mapped_free_array"; "RI_mapped_meta"; "RI_mapped_user"; "RI_mutex"; "RI_num_freed"; "region_info"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "nthZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RebuildG"; "setclsA"; "@Stdlib.Lists.List"; "In"; "nth_error"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymFrame Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface SegQ_defs Inv InvLaws RefillModel DrainModel SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require az.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RebuildRZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.InvQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.InvQ4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildRZ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RebuildG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b5.RebuildD.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma list_upd_same {T} : ltac2:(tb__ "0|1|
S14VT;A1M0S19VT;S29R2S15VT;R3A2A2S0G0S28VT;R4R3S32VT;R3R4R2A4A4R4A3F_;Fd;Fi;Fl;").
Proof. induction l as [|x l IH]; intros i d Hi; [cbn in Hi; lia|]. destruct i as [|i]; cbn; [reflexivity|]. f_equal. apply IH. cbn in Hi. lia. Qed.
Lemma setclsA_same : ltac2:(tb__ "0|0|
S1cScS0S16S1dR2A1S17A3S29S13R2A1S15S1eS1fR3A1A2A2S0S1cS3fR4R3S3eS1eS1fR4A1R3S25A4A3R4A3F_;F_;Fc;FA;").
Proof. intros A c HCI HL. unfold setclsA, nthZ. rewrite (list_upd_same _ _ _ HL). destruct A. cbn in HCI |- *. subst. reflexivity. Qed.
Lemma nth_error_lt {T} : ltac2:(tb__ "0|0|
S14VT;A1S19VT;S0S1aVT;A1S41VT;R3R2A3S18VT;R1A2A3S29R3S15VT;R4A2A2F_;Fx;Fi;Fl;").
Proof. intros l i x H. apply nth_error_Some. rewrite H. discriminate. Qed.
Lemma cst_nil : cst_ok []. Proof. intros a (b & n & [] & _). Qed.
Lemma xgl_nil : xgl_ok []. Proof. intros a (b & n & [] & _). Qed.

Lemma K0_ri_blind : ltac2:(tb__ "0|a|
S2fS1cS5S5S14S2bQ40M0A1M1A1S14S2eA1S2dScS30R8A1S1SfZ1R2A2SfR2Z1eA2A2S0S16S1dR9A1S17A3SdS0G1S7R9R1A2S7RaR1A2A3Fi;SdS0S14S2bQ8A1M2A1S6RaR1A2S6RbR1A2A3Fl;S3dS22S21RcA1A1R6A2ScS31RdR7A2S1eScS3S1SfR3R1A2S10R1SeR3Z80M3A2A2A2A1S0S1aG2A1M4S9S8S4ReA1R2A3S9S8S4RfA1M5R2A3A3F_;Fz;ScS1SfR4R1A2S10R1SeR4G3A2A2A2S2G2G2S0G4S9S8S4R10A1M6R3A3S18G2R1A2A3Lb;A2F_;Fz;ScS1SfS34R1A2S10R1S33A2A2S0G4S4R10S2cG0R2A2M7A2S4R11G7A2A3F_;Fa;SaS9S8G5A2SbSeR5S3bA2U8M8Z0M9A3A2SaS9S8G6A2SbSeR6S3cA2G8S11S15ScS20R5A1A2A1A3A2SaS9S8S4R11A1A2SbSeR7S38A2G8S26R6A1A3A2SaS9S8S4R12A1A2SbSeR8S36A2G8S23R7A1A3A2SaS9S8S4R13A1A2SbSeR9S35A2G8G9A3A2SaS9S8S4R14A1A2SbSeRaS3aA2G8S27R9A1A3A2SaS9S8S4R15A1A2SbSeRbS39A2G8G9A3A2SaS9S8S4R16A1A2SbSeRcS37A2U1G9A3A2S2aR1aR19R18R16R15R14A6S2aR1bR1aR18R17R16R15A6F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Tcs;Tri;F_;F_;F_;F_;F_;Fc;Fmd;Ftr;Ftp;Fr';Fr;FA;FKc;").
Proof.
  intros Kc A r r' tp tr md c HKc Hc HCI Hw Hl ri cs VO PRES HIMG R1 R2 R3 R4 R5 R6 R7 R8 HK.
  pose proof HK as (HA & HKc' & Htp & Htop & HRG).
  pose proof (K0_laws Kc HKc) as HL. destruct (kq_facts segsA (K0 Kc) HL A r tp _ _ HK) as [HG _ _ _ _ HLEN HCLS _ _ _ HSEP3 _ _].
  pose proof (HCLS HCI c Hc) as CV. fold cs in CV.
  pose proof HA as (_ & _ & _ & HRest & HM & _ & HB). cbn zeta in HRest. destruct HRest as (_ & _ & Hprim & _ & (HQP & _) & _). destruct Hprim as (_ & _ & _ & PC).
  pose proof (PC c Hc) as PCc.
  pose proof (entry_cls_pureQ _ A c Hc PCc HQP) as HP0.
  assert (ES : setclsA A c (nthZ (aa_cls A) c cs_empty) = A) by (apply setclsA_same; [exact HCI | rewrite HLEN; lia]).
  pose proof (cv_fa_bounds _ _ _ _ _ CV) as (FB1 & FB2 & FB3). pose proof (cv_len _ _ _ _ _ CV) as KLEN. destruct (kchunks_facts c Hc) as (KC1 & KC2 & _).
  pose proof (geom_nums _ HG) as (_ & _ & _ & T0 & T1 & _ & _ & _ & _ & _ & S1 & S2 & _ & TG). destruct HSEP3 as (P1 & _).
  unfold HIGH_SHADOW_END in S1. rewrite kSpaceSize_val in S2, P1.
  set (SB := ag_spacebeg (aa_geom A)) in *. set (T := ag_thread (aa_geom A)) in *.
  assert (RIv : ri = SB + 2 ^ 37 + c * 128) by (unfold ri, region_info, kRegionInfoStride; rewrite kSpaceSize_val; reflexivity).
  assert (TR : forall cc, (forall z, c_addr cc <= z < c_addr cc + Z.of_nat (c_w cc) -> ~ (ri <= z < ri + 128)) -> cell_ok (view segsA (rm r)) cc -> cell_ok (view segsA (rm r')) cc).
  { intros cc Hcc Hc0. apply (cell_ok_agree_rangeD (view segsA (rm r)) (view segsA (rm r')) cc); [|exact Hc0]. intros z Hz. exact (VO z (Hcc z Hz)). }
  destruct (class_rebuild [] [] cst_nil xgl_nil A r r' tp tp md md c (nthZ (aa_cls A) c cs_empty) (fun z => ri <= z < ri + 128) HA Hc HCI) as (HA' & _ & _).
  - exact HP0.
  - apply Z.le_refl.
  - apply Z.le_refl.
  - apply Z.le_refl.
  - exact KLEN.
  - intros z. lia.
  - intros z Hz. left. fold SB. rewrite RIv in Hz. lia.
  - exact VO.
  - exact PRES.
  - exact HIMG.
  - exact R1.
  - exact R2.
  - exact R3.
  - exact R4.
  - exact R5.
  - exact R6.
  - exact R7.
  - exact R8.
  - intros i x Hi. apply TR; [|exact (cv_fa_cells _ _ _ _ _ CV i x Hi)]. cbn [c_addr c_w]. intros z Hz. pose proof (nth_error_lt _ _ _ Hi) as L.
    fold SB in Hz. unfold free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize in *. change (nthZ (aa_cls A) c cs_empty) with cs in L. rewrite RIv. lia.
  - apply TR; [|exact (cv_count _ _ _ _ _ CV)]. cbn [c_addr c_w]. unfold pc_entry. fold T. intros z Hz. rewrite RIv. lia.
  - intros i x Hi. apply TR; [|exact (cv_chunks _ _ _ _ _ CV i x Hi)]. cbn [c_addr c_w]. unfold pc_entry. fold T. intros z Hz. pose proof (nth_error_lt _ _ _ Hi) as L. change (nthZ (aa_cls A) c cs_empty) with cs in L. rewrite RIv. lia.
  - intros z Hz. exfalso. lia.
  - intros z Hz. exfalso. lia.
  - intros z Hz. exfalso. lia.
  - rewrite ES. exact HM.
  - apply (bandtp_mono (view segsA (rm r)) (view segsA (rm r')) tp); [|exact HB]. intros z Hz Hd. rewrite VO; [exact Hd|].
    unfold SHADOW_BAND_HI, HIGH_SHADOW_END in Hz. rewrite RIv. lia.
  - rewrite ES in HA'. split; [exact HA'|]. split; [exact HKc'|]. split; [|split].
    + unfold tp_ok in *. rewrite Hw. exact Htp.
    + unfold top_high in *. rewrite !Hw. exact Htop.
    + unfold rigidQ in *. rewrite !Hw. exact HRG.
Qed.

Lemma K0_id24_bound : ltac2:(tb__ "0|1|
S2fS1cS5S14S2bQ40A1A1S14S2eA1S2dScS30R7A1S0S16S1dR7A1S17A3S2aR9R8R7R6R5R4A6S40ScR4S1bScS20S31R9Z18A2M0A1S24G0A1A3A3S1SfZ0R5A2S10R5S12Z2Z1cA2A2A2F_;F_;F_;F_;Fx;Fmd;Ftr;Ftp;Fr;FA;FKc;").
Proof.
  intros Kc A r tp tr md x HKc HCI HK Hx. pose proof HK as (HA & _).
  pose proof (K0_laws Kc HKc) as HL. destruct (kq_facts segsA (K0 Kc) HL A r tp _ _ HK) as [_ _ _ _ _ _ HCLS _ _ _ _ _ _].
  pose proof (HCLS HCI 24 ltac:(lia)) as CV. pose proof (cv_bounds _ _ _ _ _ CV) as (_ & B2 & B3 & _).
  pose proof HA as (_ & _ & _ & HRest & _). cbn zeta in HRest. destruct HRest as (_ & _ & Hprim & _ & (HQP & _) & _). destruct Hprim as (_ & _ & _ & PC).
  pose proof (entry_cls_pureQ _ A 24 ltac:(lia) (PC 24 ltac:(lia)) HQP) as (_ & _ & _ & _ & _ & _ & HIDS & _).
  destruct (HIDS x ltac:(rewrite app_assoc; apply in_or_app; left; exact Hx)) as (X0 & _ & X2).
  change (Size 24) with 8192 in X2. unfold SegQ_wf2.cls_of in B2, B3. unfold kUserSpaceSize, kRegionSize, kFreeArraySize, kUserMapSize in B3. lia.
Qed.
End SegQF_ri.

(* [comment removed for export] *)
Module RefillCL.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "of_nat"; "lt"; "mul"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "and"; "eq"; "or"; "@Corelib.Init.Datatypes"; "length"; "bool"; "list"; "true"; "nil"; "prod"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs"; "qall"; "q_ids"; "qitems"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "cs_mapped_user"; "AA"; "aa_geom"; "class_state"; "ag_spacebeg"; "cs_cache"; "cs_free_array"; "cs_mapped_free_array"; "ag_thread"; "ageom"; "qbatch"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "kUserMapSize"; "Sh"; "kFreeArraySize"; "kFreeArrayMapSize"; "kQuarantineBatchCount"; "kRegionInfoStride"; "kRegionSize"; "kUserSpaceSize"; "region_beg"; "region_info"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit"; "qmax"; "MUCAP"; "NBQ"; "QCAP"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.InvQC"; "AInvQC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel"; "needs_populate"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2"; "cls_of"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "isum"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RefillS"; "refill_zone"; "rf_grows"; "rf_new"; "@Stdlib.Lists.List"; "In"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells SegQ_defs PrimCredit PrimCreditLaws Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.PrimRoom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.InvQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RefillS.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma q_ids_bound_of_counts : ltac2:(tb__ "0|3|
S14S5S6S0Z1M0R1A2S0R1Z1eA2A2S0S2S9S1dS10R3A1A2A1S2aA2S0S2S9SeS5S5A2M1S12S10R4A1A1A2A1S4S22S2aA2A2S0S32S12S10R5A1A1A1S2bA2G1S36G1R1S12S10R7A1M2A1A3S0G0SfS5S5R2A3A2F_;Fit;S0S2S9S5S11S15R7A1G2R6A3A2A1S28R6A1A2F_;F_;F_;F_;F_;Fc;FA;").
Proof.
  intros A c Hc NB NI IS I1.
  unfold q_ids, qmax. rewrite length_app, !length_map, Nat2Z.inj_add.
  set (p := fun it : Z * Z => is_primary (snd it) && (it_cls it =? c)).
  assert (ITEMS : Z.of_nat (length (List.filter p (qitems (qall A)))) <= (if nmin c =? 0 then 0 else Z.min (kQuarantineBatchCount * NBQ) (QCAP / nmin c))).
  { assert (PN : forall it, In it (qitems (qall A)) -> p it = true -> 1 <= nmin c <= snd it).
    { intros it Hit Hp. unfold p in Hp. apply andb_prop in Hp as [Hp1 Hp2]. apply Z.eqb_eq in Hp2. unfold it_cls in Hp2.
      pose proof (I1 it Hit) as H1.
      assert (H2 : snd it <= 64512).
      { destruct (Z_le_dec (snd it) 64512) as [L|G]; [exact L|]. rewrite (not_primary_large (snd it)) in Hp1 by lia. discriminate Hp1. }
      pose proof (nmin_ok (snd it) (conj H1 H2)) as NM. rewrite Hp2 in NM. exact NM. }
    destruct (Z.eqb_spec (nmin c) 0) as [E0|NE].
    -
      destruct (List.filter p (qitems (qall A))) as [|it l] eqn:EF; [cbn; lia|]. exfalso.
      assert (Hin : In it (List.filter p (qitems (qall A)))) by (rewrite EF; left; reflexivity). apply filter_In in Hin as [Hi Hp].
      pose proof (PN it Hi Hp). lia.
    - apply Z.min_glb.
      + pose proof (filter_length_le p (qitems (qall A))) as FL. apply Nat2Z.inj_le in FL. lia.
      + assert (NP : 1 <= nmin c).
        { destruct (List.filter p (qitems (qall A))) as [|it l] eqn:EF.
          -   unfold nmin in *. clear -NE Hc.
            assert (C : forall k, In k nmin_tab -> 0 <= k) by (intros k Hk; unfold nmin_tab in Hk; repeat (destruct Hk as [<-|Hk]; [lia|]); destruct Hk).
            assert (0 <= nth (Z.to_nat (c - 1)) nmin_tab 0) by (apply C; apply nth_In; unfold nmin_tab; cbn [length]; lia). lia.
          - assert (Hin : In it (List.filter p (qitems (qall A)))) by (rewrite EF; left; reflexivity). apply filter_In in Hin as [Hi Hp]. exact (proj1 (PN it Hi Hp)). }
        apply Z.div_le_lower_bound; [lia|].
        pose proof (isum_filter_ge p (nmin c) (qitems (qall A)) (fun it Hit => ltac:(pose proof (I1 it Hit); lia)) (fun it Hit Hp => proj2 (PN it Hit Hp))) as W. lia. }
  destruct (c =? 24); [rewrite length_map | cbn [length]]; fold p; lia.
Qed.

Theorem populate_roomQ : ltac2:(tb__ "0|0|
S14S2dSbS31Q40A1A1S2cS5S2eR5R4R3R2A4S6S0Z1R2A2S0R2Z1eA2A2S30R7R3A2S16S7SbS5A1S18R1A1SdS5A1A3S0S2S9S5S19R2A1A2A1Z7A2S0S2S9S5S11S15RaA1S10RaA1R6A3A2A1S28R6A1A2S0S1S13R4A1S1eA2S29R7A1A2F_;F_;F_;Tcs;F_;F_;Fc;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md c HA Hc cs Hcache Hfa QB.
  destruct HA as (_ & _ & _ & HRest & _ & HI3 & _).
  destruct HRest as (_ & _ & HPR & _). destruct HPR as (_ & _ & _ & PC). pose proof (PC c Hc) as P4. change (nthZ (aa_cls A) c cs_empty) with cs in P4.
  unfold class_repr in P4.
  destruct P4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & N2 & _ & N4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TI & CV & _ & _).
  destruct HI3 as (_ & _ & _ & _ & _ & _ & _ & SL & _).
  pose proof (live_ids_bound (aa_geom A) A c) as LB.
  destruct (cap_facts c Hc) as (HS & _ & MCU & _).
  rewrite Hcache in CV. cbn [length] in CV. unfold slots in CV.
  assert (Eau : cs_allocated_user cs = Size c * (cs_allocated_user cs / Size c)) by (apply Z.div_exact; [clear -HS; lia | exact N4]).
  rewrite !Nat2Z.inj_add in CV. cbn [Z.of_nat] in CV.
  unfold MUCAP. set (S := Size c) in *. set (sl := cs_allocated_user cs / S) in *. set (mu := cs_mapped_user cs) in *. set (au := cs_allocated_user cs) in *.
  set (nf := Z.of_nat (length (cs_free_array cs))) in *. set (nl := Z.of_nat (length (live_ids (aa_geom A) A c))) in *. set (nq := Z.of_nat (length (q_ids (aa_geom A) (qall A) c))) in *.
  set (q := qmax c) in *. set (sv := small_live A) in *. unfold PRIM_LIVE_MAX in *. unfold kUserMapSize.
  clearbody S sl mu au nf nl nq q sv. clear -HS TI CV Eau Hfa QB LB SL. nia.
Qed.

Corollary rfacts_room : ltac2:(tb__ "0|0|
S14S2dSbS31Q40A1A1S2cS5S2eR5R4R3R2A4S6S0Z1R2A2S0R2Z1eA2A2S30R7R3A2S16S7SbS5A1S18R1A1SdS5A1A3S0S2S9S5S11S15R9A1S10R9A1R5A3A2A1S28R5A1A2S7SaS2fR6R3A2ScA3S0S1S13R4A1S1eA2S29R7A1A2F_;F_;F_;Tcs;F_;F_;Fc;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md c HA Hc cs Hcache QB NP. apply (populate_roomQ A rho tp md c HA Hc Hcache); [|exact QB].
  unfold needs_populate in NP. apply Z.ltb_lt in NP. destruct (kchunks_facts c Hc) as (K1 & _). subst cs. clear -NP K1. lia.
Qed.

Lemma refill_zone_where : ltac2:(tb__ "0|4|
S1cSaS5S16S5S6S0Z1R3A2S0R3Z1eA2A2S0Z0M0S17R6A1A2S0G0S13R4A1A2S0G0S1aR5A1A2S7SaS2fR7R6A2ScA3S6S0S1S13R7A1S1eA2S25A2S6S0G0S35R8R7A2M1A2S0S4Z4S1S2S9S5S19R7A1A2A1G1A2A2S20A2A2A2F_;S7SaS34R8R7A2ScA3S0S1S1aR8A1S21A2S20A2F_;S33RbRaR9R8R7A5S1bRcA1S5S17RdA1S5S26R1RcA2S5S8S6S0S1R3Z120A2RbA2S3RbS1R3Zad0A2A2A2S8S6S0S27R2RdA2M2RbA2S3RbS1G2S23A2A2A2S8S6S0R1RbA2S3RbS1R1S24A2M3A2A2S6S0S1fR1A1RbA2S3RbS1fG3A1A2A2A2A2A2Trb;TSB;TT;F_;F_;F_;F_;F_;F_;F_;Fz;Fcs;Fc;Finited;FG;").
Proof.
  intros G inited c cs z Hc HSB HMU HMF HP HG HZ T SB rb. unfold refill_zone in HZ. cbn zeta in HZ. fold T SB in HZ.
  pose proof (Zle_0_nat (length (cs_free_array cs))) as NF0. destruct (kchunks_facts c Hc) as (K1 & _).
  assert (RB0 : 0 <= rb) by (unfold rb, region_beg, kRegionSize; fold SB; lia).
  assert (SHP : forall a, rb <= a -> a + 262144 <= rb + 2 ^ 32 -> Sh rb <= Sh a /\ Sh a + 32768 <= Sh (rb + 2 ^ 32)).
  { intros a A1 A2. split; [apply Geometry.Sh_mono; exact A1|]. unfold Sh.
    pose proof (Z.div_le_mono (a + 262144) (rb + 2 ^ 32) 8 ltac:(lia) A2) as D.
    replace (a + 262144) with (a + 32768 * 8) in D by lia. rewrite Z.div_add in D by lia. lia. }
  unfold free_array in HZ. fold rb in HZ. unfold kRegionInfoStride, kRegionSize, kUserSpaceSize, kFreeArraySize, kFreeArrayMapSize, kUserMapSize, kRegionSize in *.
  destruct HZ as [H|[H|[H|[(NP & H)|[(GR & H)|(_ & H)]]]]].
  - left. lia.
  - left. lia.
  - right; left. lia.
  - destruct (HP NP) as (P1 & P2 & P3). destruct H as [H|[H|H]].
    + right; right; left. lia.
    + right; right; right. destruct (SHP (rb + cs_mapped_user cs) ltac:(lia) ltac:(lia)) as [S1 S2]. lia.
    + right; right; left. lia.
  - specialize (HG GR). destruct H as [H|H].
    + right; right; left. lia.
    + right; right; right. destruct (SHP (rb + (2 ^ 32 - 2 ^ 29) + cs_mapped_free_array cs) ltac:(lia) ltac:(lia)) as [S1 S2]. lia.
  - left. exact H.
Qed.
End RefillCL.

(* [comment removed for export] *)
Module F0A_instokC.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "nat"; "pair"; "cons"; "bool"; "true"; "prod"; "list"; "nil"; "app"; "fst"; "snd"; "orb"; "negb"; "option"; "andb"; "false"; "length"; "@Corelib.Init.Logic"; "eq"; "and"; "or"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "carve_obj"; "rho_sets"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "opp"; "pow"; "sub"; "modulo"; "mul"; "of_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "rw"; "sprop"; "SLit"; "rm"; "obj_range"; "valuation"; "holds"; "rl"; "agree_below"; "SAlu"; "SPUlt"; "SVar"; "eval"; "pairwise_disjoint"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones"; "zdesc"; "in_zone"; "zcheck"; "@Stdlib.Lists.List"; "forallb"; "In"; "Forall2"; "existsb"; "tl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.F0A_inst"; "NRT"; "carve_ok"; "spec_zone"; "zone_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "qbatch"; "topG"; "aa_q_thread"; "ag_thread"; "ag_ctx"; "ag_spacebeg"; "aa_geom"; "aa_live"; "cs_mapped_user"; "qb_items"; "@stdpp.bitvector.definitions"; "bv"; "bv_signed"; "bv_unsigned"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok"; "ZD_NRT"; "zhiF"; "zloF"; "img_okb"; "cache24"; "spec_ne"; "rhoF_of"; "cnt24"; "hw_of"; "j_min"; "j_qb"; "j_qf"; "j_st"; "lastq"; "top24"; "@Corelib.Init.Peano"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.F0A_instokC"; "NVC"; "offp"; "ZUC"; "NVN"; "K_i1"; "K_i2"; "K_pcc"; "VFC"; "ZD_NVC"; "K_bhf"; "K_qc"; "K_qce"; "VFN"; "eRIS"; "qcondCx"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_laws"; "N8"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "cell_ok"; "mkACell"; "view"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.F0A_dzone"; "img_okD"; "zoneF"; "rng_below"; "same_rng"; "winpb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "Wcan"; "V_DEPTH"; "chain_pre"; "free_depth"; "top_high"; "ulink"; "ustop"; "unwind_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "vQB"; "vQF"; "vQS"; "vBS"; "vNX"; "vQN"; "vSB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull"; "F_geom_fn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls"; "F_pc"; "cls_hyp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instG"; "instG_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.F0A_instokC.FACTSC"; "rd_okG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ax.F0A_pins"; "spec_on"; "sprop_on"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "F_cas"; "cA"; "cQ"; "O_blkN"; "O_sh"; "QBe"; "QBf"; "VFACT"; "qvar"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "kQuarantineMax"; "kSpaceSize"; "IMG_HI"; "IMG_LO"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "kQuarantineBatchCount"; "kUserMapSize"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel"; "refillA"; "needs_populate"; "@Stdlib.PArith.BinPos.Pos"; "eqb"; "@LinuxProcessSemantics.Riscv.Instr";
"ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.F0A_instokC.FACTSC.VARIANT"; "rd_okG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "QG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit"; "MUCAP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2"; "cls_of"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA GlueA GlueA2 SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocInv Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI SpineMallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_skel F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_instok.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require az.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_instG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ax.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillModel.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQI_side OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.LiveGeom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.F0A_dzone OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ax.F0A_pins OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_wf2 PrimCredit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require az.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition eRIS : sv := ltac2:(tb__ "0|0|
S2eSa1S85S27S97A1A3").
Definition K_pcc : carve_spec := ltac2:(tb__ "0|4|
S3S7S7S23S0A2M0S0A2S8S7S7S0S2A2M1S23A2M2A1S3G0S0S3S23S0S8eZ780M3A4Z784A4S4G2S3G1S23S3S0S2G3U4A4S27Z0A1A4S9G2A1A3A4").
Definition K_i1 : carve_spec := ltac2:(tb__ "0|4|
S3S7S7S23S0A2M0S0A2S8S7S7S0S2A2M1S23A2M2A1S3G0S0S3S23S0S27Z0A1Zeddc0M3A4Zeddc4A4S4G2S3G1S23S3S0S2G3U4A4S27ZffffffffA1A4S9G2A1A3A4").
Definition K_i2 : carve_spec := ltac2:(tb__ "0|5|
S3S7S7S23S0A2M0S0A2S8S7S7S0S2A2M1S23A2M2A1S3G0S0S3S23S0S27Z0A1M3Zeddc8M4A4Zeddd1A4S4G2S3G1S23S3S0S2G4U8A4S6cA4S4G2S3G1S23S3S0S2Zeddd0U1A4G3A4S9G2A1A3A3A4").
Definition K_qce : carve_spec := ltac2:(tb__ "0|5|
S3S7S7S23S0A2M0S0A2S8S7S7S0S2A2M1S23A2M2A1S3G0S0S3S23S0S8fZ0M3A4Z20A4S4G2S3G1S23S3S0S2G3U8M4A4S27G3A1A4S4G2S3G1S23S3S0S2Z8G4A4S80A4S4G2S3G1S23S3S0S2Z10G4A4S7fA4S4G2S3G1S23S3S0S2Z18G4A4S81A4S9G2A1A3A3A3A3A4").
Definition K_qc : carve_spec := ltac2:(tb__ "0|5|
S3S7S7S23S0A2M0S0A2S8S7S7S0S2A2M1S23A2M2A1S3G0S0S3S23S0S8fZ0M3A4Z20A4S4G2S3G1S23S3S0S2G3U8M4A4S84A4S4G2S3G1S23S3S0S2Z8G4A4S80A4S4G2S3G1S23S3S0S2Z10G4A4S7fA4S4G2S3G1S23S3S0S2Z18G4A4S81A4S9G2A1A3A3A3A3A4").
Definition K_bhf : carve_spec := ltac2:(tb__ "0|5|
S3S7S7S23S0A2M0S0A2S8S7S7S0S2A2M1S23A2M2A1S3G0S0S3S23S0S7fZ0M3A4Z18A4S4G2S3G1S23S3S0S2G3U8M4A4S83A4S4G2S3G1S23S3S0S2Z8G4A4S82A4S4G2S3G1S23S3S0S2Z10G4A4S27Z3fdA1A4S9G2A1A3A3A3A4").

Definition NVC (f : bool) : list carve_spec := ltac2:(tb__ "0|1|
S5S8S17A1Lf;Vf;S4S17S69S4S17S68S4S17S65S4S17S63S4S17S64S9S17A1A3A3A3M0A3A3S4S17S6aG0A3X5x2").
Definition VFC (f : bool) : list sprop := ltac2:(tb__ "0|0|
S94S5S95Lf;Vf;S93S92X5x2A1").
Definition NVN : list carve_spec := [].
Definition BIGF : sprop := ltac2:(tb__ "0|0|
S2fS27S96A1S30PdA1A2").
Definition VFN : list sprop := [BIGF].

Definition qcondCx (f : bool) (A : AA) : Prop := ltac2:(tb__ "0|1|
S14S5OLf;Vf;S14S16S13S8S3fA1S41VA;A1S9S3fA1A3M0A1S13S0S22S12S7S0S0A2S48S5bVA;A1A1A2A1S9cA3A2G0X5x2S13S8S0A1S52VA;A1S9S0A1A3A2").
Definition ZD_NVC (f : bool) : list zdesc := ltac2:(tb__ "0|6|
S5S8S33A1Lf;Vf;S4S7S7S2S0A2M0S0A2M1S3G0S0S3S2S0U1M2Z50A4Z70A4M3S4G1S3G0S0S3S2S0U4Z0A4Z18A4S4G1S3G0S0S3S2S0G2Z850A4Z854A4S4G1S3G0S0S3S2S0U0M4Zeddc0A4Zeddc4A4S4G1S3G0S0S3S2S0G4Zeddc8A4Zeddd1A4S9G1A1A3A3A3M5A3A3S4G1G3G5A3X5x2").
Definition ZUC (f : bool) : list nat := ltac2:(tb__ "0|5|
S5S8S2A1Lf;Vf;S4S2U0M0S4S2U1M1S4S2U2M2S4S2U3M3S4S2U4S9S2A1M4A3A3A3A3A3S4S2G0S4S2G1S4S2G2S4S2G3G4A3A3A3A3X5x2").
Lemma ZD_chkC : ltac2:(tb__ "0|1|
S5S14S13S5S35SaS33S4eS67R1A1A3M0A1S6A3S14S13S5S36S33S51G0A3S6A3S14S13S5S36S17S53SaS17S3bS5fR1A1A3A3S6A3S13S5S36S33S72G0A3S6A3A2A2A2Ff;").
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma ZD_chkN : ltac2:(tb__ "0|0|
S14S13S5S35S4eA1S6A3S14S13S5S36S33S51S4eA3S6A3S14S13S5S36S17S53S3bA3S6A3S13S5S36S33S72S4eA3S6A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition offp (i : positive) : bool := ltac2:(tb__ "0|0|
S10SeSa0Vi;P7fA2A1SeSa0Vi;P82A2A1A2").
Lemma offp_chk : ltac2:(tb__ "0|1|
S5S14S13S5S36S17S8bS60A1SaS17S3bS5fR1A1A3A3S6A3S14S13S5S36S26S8cS60A1M0SaS26S86SaS26S3aS26S87S6A1A2S8dA3A3A3S6A3S13S5S36S26G0SaS26S86SaS26S3aS26S87S11A1A2S8dA3A3A3S6A3A2A2Ff;").
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Section FACTSC.
Let segs : list Segment := segsA.
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Variables (A : AA) (rho : valuation) (tp : list word) (md : Model) (p n : Z).
Hypothesis HA : ltac2:(tb__ "0|0|
VAInv;VA;Vrho;Vtp;Vmd;A4").
Hypothesis HL : ltac2:(tb__ "0|0|
S37S7S0S0A2S3S0S0Vp;Vn;A4S46VA;A1A3").
Hypothesis HCL : blk_cls p n.
Hypothesis Hii : aa_internal_inited A = true.
Hypothesis Hp12 : ltac2:(tb__ "0|0|
S13S0S4bQ40S25Vrho;PcA2A2Vp;A3").
Hypothesis Hn13 : ltac2:(tb__ "0|0|
S13S0S4bQ40S25Vrho;PdA2A2Vn;A3").
Variable t : Z.
Hypothesis Ht : ltac2:(tb__ "0|2|
S14S14S1aZ0Vt;A2S1cVt;Z100A2A2S14S13S0S20Vt;Z4A2Z1A3S14S6fS71Vsegs;S28Vrho;A1A2M0S70S1fVp;Z10A2U4M1S56Vt;Vn;A2A3A2S6fG0S70S1fVp;ZcA2G1S20Vn;S1eZ2Z20A2A2A3A2A2A2A2").
Variable jv : junkF.
Hypothesis Hjv : ltac2:(tb__ "0|9|
S14S14S1aZ0M0S57Vjv;A1M1A2S1cG1S1eZ2Z40A2M2A2A2S14S14S1aG0S5aVjv;A1M3A2S1cG3G2A2A2S14S14S1aG0S59Vjv;A1M4A2S1cG4G2A2A2S14S14S1aG0S58Vjv;A1M5A2S1cG5G2A2A2S14S6fS71Vsegs;S28Vrho;A1A2M6S70S1bSa3Z48A2U8M7G1A3A2S14S6fG6S70S1bS42S45VA;A1A1M8Zae0A2G7G3A3A2S13S8S3fA1S41VA;A1S9S3fA1A3S14S6fG6S70S1bG8Z58A2G7G4A3A2S6fG6S70S1bG8Z60A2G7G5A3A2A2F_;A2A2A2A2A2A2").
Let G : ageom := aa_geom A.
Let m : bview := ltac2:(tb__ "0|0|
S71Vsegs;S28Vrho;A1A2").
Let rho1 : valuation := ltac2:(tb__ "0|0|
S54VA;Vrho;Vp;Vn;Vt;Vjv;A6").

Definition rhoC_of : valuation := ltac2:(tb__ "0|0|
S54S9eVA;Z18A2Vrho;Vp;Vn;Vt;Vjv;A6").
Let rho1R : valuation := rhoC_of.

Lemma rw_rho_sets_pw : ltac2:(tb__ "0|4|
S8S7S1S49Q40A1M0A2M1A1M2G2S2aS2aS1S38G1G1G1G1S14S13S1SbS1G0R2A3M3SbS1G0R1A3A3S13S1G3R3A3S13G0ScS1G0R3A3ScS1G0R2A3A3F_;A2Lb;La;R5R4A5S13G0S25R4R2A2S25R3R2A2A3S13G0S25S19R5R7A2R3A2S25S19R4R6A2R3A2A3F_;F_;Fi;Fr';Fr;Fl';Fl;").
Proof.
  intros l l' r r' i HF. revert r r'. induction HF as [|[k v] [k' v'] l l' [Ek Ev] HF IH]; intros r r' Hr; cbn [rho_sets]; [exact Hr|].
  cbn [fst snd] in Ek, Ev. subst k'. apply IH. unfold rho_set_rw. cbn [rw]. destruct (Pos.eqb_spec i k) as [->|NE]; [exact (Ev eq_refl) | exact Hr].
Qed.
Lemma pins_off : ltac2:(tb__ "0|0|
S1S13S5S60R1A1S6A3S13S49Q40A1S25Vrho1R;R2A2S25Vrho1;R2A2A3F_;Fi;").
Proof.
  intros i Hi. unfold offp in Hi. apply andb_prop in Hi as [H1 H2]. apply negb_true_iff in H1, H2. apply Pos.eqb_neq in H1, H2.
  unfold rho1R, rhoC_of, rho1, rhoF_of. apply rw_rho_sets_pw; [|reflexivity].
  repeat (apply Forall2_cons; [cbn [fst snd]; split; [reflexivity | intros E; first [reflexivity | exfalso; congruence]]|]). apply Forall2_nil.
Qed.
Lemma pins_rl : ltac2:(tb__ "0|0|
S1S13S8S49Q8A1A1S2cVrho1R;R1A2S2cVrho1;R1A2A3Fl;").
Proof. intros l. unfold rho1R, rhoC_of, rho1, rhoF_of. rewrite !rl_rho_sets. reflexivity. Qed.
Lemma pins_rm : ltac2:(tb__ "0|0|
S13S49Q40A1SfS49Q8A1A1F_;S28Vrho1R;A1S28Vrho1;A1A3").
Proof. unfold rho1R, rhoC_of, rho1, rhoF_of. rewrite !rm_rho_sets. reflexivity. Qed.
Lemma pins_rm0 : ltac2:(tb__ "0|0|
S13S49Q40A1SfS49Q8A1A1F_;S28Vrho1R;A1S28Vrho;A1A3"). Proof. unfold rho1R, rhoC_of, rhoF_of. apply rm_rho_sets. Qed.

Lemma geoT : ltac2:(tb__ "0|4|
S14S1aZ1000M0S42VG;A1M1A2S14S1aS1bG1G0A2M2S40VG;A1M3A2S14S15S1aG2Z10000A2S1aZ646000G1A2A2S1aG3Z7fffff800000A2A2A2A2").
Proof.
  pose proof (geomF A rho tp md n HA t) as (T1 & T2 & _). pose proof (geomTI A rho tp md HA) as TI. pose proof (topG_range G) as TR. unfold G in *. split; [lia|]. split; [lia|]. split; [exact TI | lia].
Qed.
Lemma EcA1 : ltac2:(tb__ "0|0|
S13S0S4bQ40S31Vrho1;S8eA2A2S1bS42VG;A1Zd0A2A3").
Proof.
  pose proof geoT as (T1 & T2 & _ & T4). cbn [eval cA vT]. change (rw rho1 151%positive) with (Z_to_bv 64 (ag_thread G)).
  rewrite add_val, !u64_lit by lia. apply Z.mod_small. lia.
Qed.

Lemma carve_pcc : ltac2:(tb__ "0|0|
S13S8S0A1S52VA;A1S9S0A1A3S3cVrho1;S65A2F_;").
Proof.
  intros HC0. pose proof HA as (HG & HR & HF & HRest & HM & HI3 & HBT). destruct HRest as (Hsep & HLB & HPR & _).
  destruct HPR as (_ & _ & _ & PC). specialize (PC 24 ltac:(lia)). unfold class_repr in PC.
  destruct PC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PE & _ & _ & CI & CN & _).
  pose proof geoT as (T1 & T2 & TI & T4). fold G in PE, CI, CN.
  assert (MVT : forall z, ag_thread G <= z < ag_thread G + 0x1000 -> maskv (fs_footb (aa_geom A)) (view segs (rm rho)) z = view segs (rm rho) z) by (intros z Hz; apply (MV_T A rho tp md HA); exact Hz).
  assert (CW : cell_ok m (mkACell (ag_thread G + 208 + 1920) 4 0)).
  { unfold cache24 in HC0. destruct (aa_cache_inited A) eqn:ECI.
    - destruct (CI eq_refl) as (C1 & _). rewrite HC0 in C1. cbn [length Z.of_nat] in C1.
      intros j Hj. specialize (C1 j Hj). cbn [c_addr c_w RtCells.c_val] in C1, Hj |- *. rewrite MVT in C1 by lia. replace (ag_thread G + 208 + 1920 + Z.of_nat j) with (ag_thread G + 208 + 80 * 24 + Z.of_nat j) by lia. exact C1.
    - destruct (CN eq_refl) as (_ & FZ). intros j Hj. cbn [c_addr c_w RtCells.c_val] in Hj |- *.
      rewrite nth_enc_bytes by lia. unfold le_byte. rewrite Z.mod_0_l by lia. rewrite Z.shiftr_0_l, Z.mod_0_l by (cbn; lia).
      specialize (FZ (ag_thread G + 208 + 1920 + Z.of_nat j) ltac:(lia)). rewrite MVT in FZ by lia. exact FZ. }
  unfold K_pcc, carve_ok. cbn zeta. rewrite EcA1.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia|].
  split.
  - intros off Hoff. change (rm rho1) with (rm rho). apply (cell_wok_rd2 (rm rho) (ag_thread G + 208 + 1920) 4 0 (ag_thread G + 208 + off) CW); cbn [Z.of_nat]; lia.
  - unfold cells_in_view. repeat apply Forall_cons; try apply Forall_nil. change (rm rho1) with (rm rho).
    exact (civ_cell rho1 (rm rho) (ag_thread G + 208) 1920 4 0 (SLit 0) CW eq_refl ltac:(lia) ltac:(lia)).
Qed.

Lemma carve_inst : ltac2:(tb__ "0|0|
S14S3cVrho1;S63A2S3cVrho1;S64A2A2").
Proof.
  pose proof HA as (HG & HR & _). pose proof (geomF A rho tp md n HA t) as (_ & _ & _ & _ & _ & S1 & S2 & _). rewrite kSpaceSize_val in S2. unfold HIGH_SHADOW_END in S1.
  pose proof (topG_range (aa_geom A)) as ACV.
  assert (E155 : rw rho1 155%positive = Z_to_bv 64 (ag_spacebeg (aa_geom A))) by reflexivity.
  assert (ERIS : eval rho1 eRIS = Z_to_bv 64 (ag_spacebeg (aa_geom A) + kSpaceSize)).
  { unfold eRIS, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states.vSB. cbn [eval]. rewrite E155. rewrite kSpaceSize_val. apply bv_eq. rewrite add_val, !u64_lit by lia. apply Z.mod_small. lia. }
  assert (Erm : rm rho1 = rm rho) by reflexivity.
  split; unfold K_i1, K_i2, carve_ok; cbn zeta; cbn [eval]; rewrite ?u64_lit by lia.
  all: split; [lia|]. all: split; [lia|]. all: split; [lia|]. all: split; [lia|]. all: split; [lia|].
  all: split; [unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia|].
  all: rewrite ?Erm.
  all: split; [intros off Hoff; split; [apply wok_of_imageA; lia | apply rd_of_imageA; lia]|].
  all: unfold cells_in_view; repeat apply Forall_cons; try apply Forall_nil.
  all: try (rewrite ERIS; rewrite kSpaceSize_val).
  all: cbn [eval]; civ_any2 HR.
Qed.

Let qbF : Z := qb_addr (lastq A).
Let nbF : Z := ltac2:(tb__ "0|0|
S1bS1bS44VG;A1S21Z18S1eZ2Z20A2A2A2S21Z10S5cVA;A1A2A2").
Let zbF (z : nat) : Z := ltac2:(tb__ "0|0|
S2S0Lz;Vz;Z0S2S2S0Ln0;R1S42VG;A1S2S2S0Ln1;R1S43VG;A1S2S2S0Ln2;R1Vp;S2S2S0Ln3;R1VqbF;S2VnbF;Ln4;X2x2Ln3;X2x2Ln2;X2x2Ln1;X2x2Ln0;X2x2").

Section VARIANT.
Variables (NV : list carve_spec) (ZD : list zdesc) (ZU : list nat).
Hypothesis HZU : ltac2:(tb__ "0|0|
S2S37S2R1VZU;A3S5dR2U4A2F_;Fz;").
Hypothesis HZ4 : ltac2:(tb__ "0|0|
S37S2U4VZU;A3S16S13S8S3fA1S41VA;A1S9S3fA1A3A1F_;").
Hypothesis H03 : ltac2:(tb__ "0|0|
S2S5dR1U3A2S37S2R2VZU;A3F_;Fz;").
Hypothesis HINZ : ltac2:(tb__ "0|0|
S38S24S33S34Vrho1;VzbF;S50S4fVZU;A5S4dS17S24S18VNV;A4VZD;A5").
Hypothesis HCHK : ltac2:(tb__ "0|1|
S14S13S5S35SaS33S4eVZD;A3M0A1S6A3S14S13S5S36S33S51G0A3S6A3S14S13S5S36S17S53SaS17S3bVNV;A3A3S6A3S13S5S36S33S72G0A3S6A3A2A2A2").
Hypothesis HCARVE : ltac2:(tb__ "0|0|
S4cS17S3cVrho1;A1VNV;A3").

Lemma Q4facts : ltac2:(tb__ "0|5|
S37S2U4VZU;A3S14S15S1aS1bVqbF;Z2000A2M0S42VG;A1M1A2S1aS1bG1Z1000M2A2VqbF;A2A2S14S15S1aG0S43VG;A1M3A2S1aS1bG3G2A2VqbF;A2A2S14S15S1aS1bVp;S6eVn;A1A2VqbF;A2S1aG0S1fVp;Z10A2A2A2S14S1aS44VG;A1M4VqbF;A2S1aG0S1bG4S97A2A2A2A2A2A2F_;").
Proof.
  intros H4. pose proof (HZ4 H4) as HNE. pose proof (qF A rho tp md p n HA HL) as QF. cbn zeta in QF. destruct QF as (_ & _ & _ & _ & _ & QL).
  destruct (QL HNE) as (_ & _ & _ & _ & _ & _ & _ & _ & BS1 & BS2 & BT' & BC' & BP'). unfold kQuarantineBatchSize in *. unfold qbF, lastq, G.
  split; [exact BT'|]. split; [exact BC'|]. split; [exact BP'|]. split; [exact BS1 | exact BS2].
Qed.
Lemma zsepC : ltac2:(tb__ "0|3|
S2S2S37S2R2VZU;A3M0G0S16S13S2R4R3A3A1S15S1aS1bVzbF;R5A1M1S4fR5A1A2S1bVzbF;R4A1M2S50R4A1A2A2S1aS1bG2S4fR4A1A2S1bG1S50R5A1A2A2A2F_;F_;F_;Fz';Fz;").
Proof.
  assert (HZ : forall y, In y ZU -> (y = 0 \/ y = 1 \/ y = 2 \/ y = 3 \/ (y = 4 /\ In 4 ZU))%nat).
  { intros y Hy. pose proof (HZU y Hy). destruct y as [|[|[|[|[|y]]]]]; try lia. do 4 right. split; [reflexivity | exact Hy]. }
  pose proof (geomF A rho tp md n HA t) as (T1 & T2 & _ & C1 & C2 & S1 & S2 & _ & _ & _ & TC & TR & TI & CI & TB & CB).
  pose proof (blkF_geom A rho tp md p n HA HL HCL) as (B1 & _ & B3 & B4 & BT & BC & BN & _). unfold blk_geo in B1. pose proof (N8_facts n B3) as (N1 & _).
  rewrite kSpaceSize_val in S2. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, HIGH_SHADOW_END, IMG_LO, IMG_HI, LOW_SHADOW_BEG in *.
  unfold G in *.
  assert (P01 : 0 + 0x646000 <= ag_thread (aa_geom A) + 0 \/ ag_thread (aa_geom A) + 0x1000 <= 0 + 0xe4000) by (clear -TI; lia).
  assert (P02 : 0 + 0x646000 <= ag_ctx (aa_geom A) + 8 \/ ag_ctx (aa_geom A) + 0x1000 <= 0 + 0xe4000) by (clear -CI; lia).
  assert (P03 : 0 + 0x646000 <= p + -16 \/ p + 0 <= 0 + 0xe4000) by (clear -B1; lia).
  assert (P12 : ag_thread (aa_geom A) + 0x1000 <= ag_ctx (aa_geom A) + 8 \/ ag_ctx (aa_geom A) + 0x1000 <= ag_thread (aa_geom A) + 0) by (clear -TC; lia).
  assert (P13 : ag_thread (aa_geom A) + 0x1000 <= p + -16 \/ p + 0 <= ag_thread (aa_geom A) + 0) by (clear -BT N1 B3; lia).
  assert (P23 : ag_ctx (aa_geom A) + 0x1000 <= p + -16 \/ p + 0 <= ag_ctx (aa_geom A) + 8) by (clear -BC B3; lia).
  assert (P4 : In 4%nat ZU ->
     (0 + 0x646000 <= qbF + 0 \/ qbF + 8192 <= 0 + 0xe4000)
     /\ (ag_thread (aa_geom A) + 0x1000 <= qbF + 0 \/ qbF + 8192 <= ag_thread (aa_geom A) + 0)
     /\ (ag_ctx (aa_geom A) + 0x1000 <= qbF + 0 \/ qbF + 8192 <= ag_ctx (aa_geom A) + 8)
     /\ (p + 0 <= qbF + 0 \/ qbF + 8192 <= p + -16)).
  { intros H4. destruct (Q4facts H4) as (X1 & X2 & X3 & X4 & _). unfold G in *. split; [clear -X4 S1; lia|]. split; [clear -X1; lia|]. split; [clear -X2; lia|]. clear -X3 N1 B3; lia. }
  assert (SYM : forall a b c d : Z, a <= b \/ c <= d -> c <= d \/ a <= b) by (clear; intros; lia).
  clear T1 T2 C1 C2 S1 S2 TC TR TI CI TB CB B1 B3 B4 BT BC BN N1.
  intros z z' Hz Hz' NE.
  destruct (HZ z Hz) as [-> |[-> |[-> |[-> |[-> H4]]]]]; destruct (HZ z' Hz') as [-> |[-> |[-> |[-> |[-> H4']]]]];
    try (exfalso; apply NE; reflexivity); cbn [zbF zloF zhiF];
    try match goal with H : In 4%nat ZU |- _ => pose proof (P4 H) as (P04 & P14 & P24 & P34) end;
    first [ assumption | apply SYM; assumption ].
Qed.
Lemma inz_G : ltac2:(tb__ "0|0|
S38S24S33S34Vrho1;VzbF;S50S4fVZU;A5S4dS17S24S18SaS17S3bVNV;A3A4SaS33S4eVZD;A3A5").
Proof. rewrite map_app. apply Forall2_app; [|exact HINZ]. exact (inz_NRT A rho tp md p n HA HL HCL Hp12 t Ht jv ZU H03). Qed.
Theorem pd_G : ltac2:(tb__ "0|0|
S32Vrho1;S4dS17S24S18SaS17S3bVNV;A3A4A2").
Proof. apply (zones_pd rho1 zbF zloF zhiF ZU zsepC _ (ZD_NRT ++ ZD)); [exact inz_G | exact (proj1 HCHK)]. Qed.
Lemma zfactsC : ltac2:(tb__ "0|3|
S2S37S2R1VZU;A3S16S13S2R2U0A3A1S14S1aZ1000S1bVzbF;R3A1M0S50R3A1A2M1A2S14S1aS1bG0S4fR3A1A2M2S40VG;A1A2S14S15S1aG2S99A2S1aS98G1A2A2S14S15S1aG2S9bA2S1aS9aG1A2A2S15S1aG2Vp;A2S1aS1bVp;S6eVn;A1A2G1A2A2A2A2A2A2F_;F_;Fz;").
Proof.
  intros z Hz NZ.
  assert (HZ : (z = 1 \/ z = 2 \/ z = 3 \/ (z = 4 /\ In 4 ZU))%nat).
  { pose proof (HZU z Hz). destruct z as [|[|[|[|[|z]]]]]; try lia. do 3 right. split; [reflexivity | exact Hz]. }
  pose proof (topG_range G) as ACV.
  pose proof (geomF A rho tp md n HA t) as (T1 & T2 & _ & C1 & C2 & S1 & S2 & _ & _ & _ & TC & TR & TI & CI & TB & CB).
  pose proof (blkF_geom A rho tp md p n HA HL HCL) as (B1 & _ & B3 & B4 & BT & BC & BN & _). unfold blk_geo in B1. pose proof (N8_facts n B3) as (N1 & _).
  rewrite kSpaceSize_val in S2. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, HIGH_SHADOW_END, IMG_LO, IMG_HI, LOW_SHADOW_BEG in *. fold G in T1, T2, C1, C2, S1, S2, TC, TR, TI, CI, TB, CB, B4, BT, BC.
  destruct HZ as [-> |[-> |[-> |[-> H4]]]]; cbn [zbF zloF zhiF].
  - clear -T1 T2 TI TB BT N1 B3. lia.
  - clear -C1 C2 CI CB BC N1 B3. lia.
  - clear -B1 B3 B4 N1 ACV. lia.
  - destruct (Q4facts H4) as (_ & _ & BP' & BS1 & BS2). rewrite kSpaceSize_val in BS2. clear -BS1 BS2 BP' S1 S2 N1 B3. lia.
Qed.
Lemma zone_of_inzC : ltac2:(tb__ "0|2|
S24S33S34Vrho1;VzbF;S50S4fVZU;R2R1A7S13S5S51R2A1S6A3S1cSbS0S0S29Vrho1;R4A2M0A3ScS0S0G0A3A2S3eS40VG;A1Vp;S6eVn;A1SbS0S0S29Vrho1;R5A2M1A3ScS0S0G1A3A5F_;F_;F_;Fd;Fo;").
Proof.
  intros o [[z lo] hi] (HU & L1 & L2 & R) Hi NE. unfold img_okb in Hi. unfold zone_ok.
  destruct R as [R|[R1 R2]]; [lia|]. split; [lia|].
  destruct (Nat.eqb_spec z 0) as [->|NZ].
  - left. cbn [zbF zloF zhiF] in *. repeat (apply andb_prop in Hi as [Hi ?X]).
    repeat match goal with H : (_ || _) = true |- _ => apply Bool.orb_prop in H | H : (_ <=? _) = true |- _ => apply Z.leb_le in H end.
    all: repeat match goal with H : (_ <=? _) = true \/ _ |- _ => destruct H as [H|H] | H : (_ <=? _) = true |- _ => apply Z.leb_le in H end.
    all: lia.
  - right. destruct (zfactsC z HU NZ) as (F1 & F2 & F3 & F4 & F5). repeat split; lia.
Qed.
Theorem carve_G : ltac2:(tb__ "0|0|
S4cS17S3cVrho1;A1SaS17S3bVNV;A3A3").
Proof. apply Forall_app. split; [exact (carve_NRT A rho tp md p n HA HL HCL Hii Hp12 t Ht jv Hjv) | exact HCARVE]. Qed.
Theorem zone_G : ltac2:(tb__ "0|0|
S4cS17S3dVrho1;S40VG;A1Vp;S6eVn;A1A4SaS17S3bVNV;A3A3").
Proof.
  pose proof inz_G as HF2. destruct HCHK as (_ & Himg & Hne & _).
  apply Forall_forall. intros k Hk.
  destruct (Forall2_In_l _ _ _ (carve_obj k) HF2 (in_map _ _ _ Hk)) as (d & Hd & Hin).
  pose proof (proj1 (forallb_forall _ _) Himg d Hd) as Hi. pose proof (proj1 (forallb_forall _ _) Hne k Hk) as Hn.
  pose proof (proj1 (Forall_forall _ _) carve_G k Hk) as Ck.
  destruct k as [[[base lo] hi] cs]. unfold spec_zone. unfold spec_ne in Hn. apply Z.ltb_lt in Hn. unfold carve_ok in Ck. destruct Ck as (C1 & C2 & C3 & _).
  pose proof (zone_of_inzC _ d Hin Hi) as ZZ. cbn [carve_obj] in ZZ. unfold carved in ZZ. rewrite obj_range_mk in ZZ by lia. cbn [fst snd] in ZZ.
  apply ZZ. lia.
Qed.

Theorem nfs_zoneG : ltac2:(tb__ "0|1|
S17S37S17R1SaS17S3bVNV;A3A3S0S14S1aSbS0S0S29Vrho1;S18R3A1A2M0A3R1A2S1cR1ScS0S0G0A3A2A2S73VA;R2A2F_;Fa;F_;Fk;").
Proof.
  intros k Hk a Ha. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.F0A_dzone.zoneF. cbn zeta.
  destruct (Forall2_In_l _ _ _ (carve_obj k) inz_G (in_map carve_obj _ _ Hk)) as (d & Hd & IZ).
  pose proof (proj1 (forallb_forall _ _) (proj2 (proj2 (proj2 HCHK))) d Hd) as OKd.
  destruct d as [ [z lo] hi]. unfold in_zone in IZ. destruct IZ as (HU & L1 & L2 & R). destruct R as [R|[R1 R2]]; [lia|].
  assert (Z5 : (z = 0 \/ z = 1 \/ z = 2 \/ z = 3 \/ z = 4)%nat) by (pose proof (HZU z HU); lia).
  destruct Z5 as [-> | [-> | [-> | [-> | ->] ] ] ]; cbn [zloF zhiF] in L1, L2; cbn [zbF] in R1, R2.
  - unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.F0A_dzone.img_okD in OKd. cbn [Nat.eqb] in OKd. apply andb_prop in OKd as [OK1 OK3]. apply andb_prop in OK1 as [OK1 OK2].
    apply Z.leb_le in OK1, OK2. left. split; [lia|]. apply Bool.orb_prop in OK3 as [OK3|OK3]; apply Z.leb_le in OK3; lia.
  - right. left. unfold G in *. lia.
  - right. right. left. unfold G in *. lia.
  - apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.F0A_dzone.chunk_zoneF A rho tp md p n a HA HL : (fun P => P) _). pose proof (N8_facts n) as NF. destruct (blkF_geom A rho tp md p n HA HL HCL) as (_ & _ & N1 & _). specialize (NF N1). lia.
  - destruct (Q4facts HU) as (_ & _ & _ & S1 & S2). unfold qbF in *. do 3 right. left. unfold G in *. lia.
Qed.

Definition rd_okG (nW : nat) (o : sobj) : bool := ltac2:(tb__ "0|1|
SdSdSdSdS39S24S75Vo;A1M0S4dS17S24S18SaS17S3bVNV;A3A4A3S75Vo;S91A2A2S75Vo;S90A2A2S76Vo;A1A2S39S24G0S7eS77VnW;A1A1A3A2").
Variable rr : valuation.
Hypothesis HRW : ltac2:(tb__ "0|0|
S1S13S5S60R1A1S6A3S13S49Q40A1S25Vrr;R2A2S25Vrho1;R2A2A3F_;Fi;").
Hypothesis HRL : ltac2:(tb__ "0|0|
S1S13S8S49Q8A1A1S2cVrr;R1A2S2cVrho1;R1A2A3Fl;").
Hypothesis HON : ltac2:(tb__ "0|0|
S13S5S36S17S8bS60A1SaS17S3bVNV;A3A3S6A3").
Theorem rd_zoneG : ltac2:(tb__ "0|1|
S2S2aS2dS5eVrr;R1A3S7bVA;R2A2S1aS4aQ40S25R3S78A2A2S1dS7aA1A2S4cS26S2bR4A1S79S77R5A1A1A3S24S13S5Sa2R7R1A2S6A3S13S5S74S5eR2A2S6A3S0S14S1aSbS0S0S29R9R4A2M0A3R1A2S1cR1ScS0S0G0A3A2A2S73VA;R2A2F_;Fa;F_;F_;Fo;F_;F_;F_;F_;FrhoE;FnW;").
Proof.
  intros nW rhoE HAG HTOP HDEP HCH o Hok Hb a Ha. rewrite (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.F0A_dzone.rng_below_agree GW rr rhoE o HAG Hb) in Ha.
  pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.F0A_dzone.BNDz A rho tp md p n HA HL HCL t Ht) as (B1 & B2 & B3 & B4 & B5). unfold blk_geo in B1.
  unfold rd_okG in Hok. apply Bool.orb_prop in Hok as [Hok|Hok]; [apply Bool.orb_prop in Hok as [Hok|Hok]; [apply Bool.orb_prop in Hok as [Hok|Hok]; [apply Bool.orb_prop in Hok as [Hok|Hok]|]|]|].
  - apply existsb_exists in Hok as (o' & Ho' & Hs). rewrite (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.F0A_dzone.same_rng_range rr o o' Hs) in Ha.
    apply in_map_iff in Ho' as (k & <- & Hk). rewrite (carve_range_on offp rho1 rr HRW HRL k (proj1 (forallb_forall _ _) HON k Hk)) in Ha. exact (nfs_zoneG k Hk a Ha).
  - rewrite (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.F0A_dzone.same_rng_range rr o O_sh Hok), (obj_range_on offp rho1 rr HRW HRL O_sh eq_refl) in Ha.
    change (obj_range rho1 O_sh) with (obj_range (rhoF_of A rho p n t jv) O_sh) in Ha. rewrite (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.F0A_dzone.R_sh1 A rho tp md p n HA HL HCL Hp12 t jv Ht) in Ha. cbn [fst snd] in Ha.
    unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.F0A_dzone.zoneF. cbn zeta. do 5 right. left.
    pose proof (Sh_in_band p ltac:(unfold IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in B1; lia)) as S1. pose proof (Sh_in_band (p + N8 n) ltac:(unfold IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in B1; lia)) as S2.
    assert (S3 : Sh p + N8 n / 8 <= Sh (p + N8 n)).
    { unfold Sh. pose proof (N8_facts n B2) as (_ & _ & _ & N4). rewrite <- N4 at 2. rewrite Z.div_add by lia. lia. }
    lia.
  - rewrite (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.F0A_dzone.same_rng_range rr o O_blkN Hok), (obj_range_on offp rho1 rr HRW HRL O_blkN eq_refl) in Ha.
    change (obj_range rho1 O_blkN) with (obj_range (rhoF_of A rho p n t jv) O_blkN) in Ha. rewrite (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.F0A_dzone.R_blk1 A rho tp md p n HA HL HCL Hp12 t jv Ht) in Ha. cbn [fst snd] in Ha.
    apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.F0A_dzone.chunk_zoneF A rho tp md p n a HA HL). lia.
  - unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.F0A_dzone.winpb in Hok. destruct o as [ob olo ohi ocs od]. cbn [ob_base ob_lo ob_hi] in Hok.
    destruct ob as [| v | | | | | | ]; try discriminate. destruct v as [v|v|]; try discriminate. do 3 (destruct v as [v|v|]; try discriminate).
    destruct olo as [lo| | | | | | | ]; try discriminate. destruct ohi as [hi| | | | | | | ]; try discriminate.
    apply andb_prop in Hok as [Hok H3]. apply andb_prop in Hok as [H1 H2]. apply Z.leb_le in H1, H2, H3. unfold free_depth in *.
    rewrite obj_range_mk in Ha by lia. cbn [fst snd eval] in Ha.
    assert (E10 : rw rr 10%positive = rw rhoE 10%positive) by (apply (proj1 HAG); unfold GW; lia). rewrite E10 in Ha.
    unfold top_high in HTOP. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.F0A_dzone.zoneF. cbn zeta. do 6 right. lia.
  - apply existsb_exists in Hok as (o' & Ho' & Hs). rewrite (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.F0A_dzone.same_rng_range rr o o' Hs) in Ha.
    assert (LNK : Forall (fun o => bv_unsigned (rw rhoE 10%positive) + 16 <= bv_unsigned (eval rhoE (ob_base o)) <= 2 ^ 47 /\ ob_lo o = SLit (-16) /\ ob_hi o = SLit 0) (unwind_objs (Wcan nW))).
    { unfold unwind_objs. destruct (Wcan nW) as [|l W'] eqn:EW; [constructor|].
      unfold chain_pre in HCH. cbn [app] in HCH.
      pose proof (Forall_inv HCH) as C0. pose proof (Forall_inv (Forall_inv_tail HCH)) as C1.
      pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HCH))) as C2. do 3 apply Forall_inv_tail in HCH.
      cbn [holds eval] in C0, C1, C2. rewrite u64_lit in C0 by lia. rewrite add_val, !u64_lit in C1 by lia. rewrite u64_lit in C2 by lia.
      pose proof (urange (rw rhoE 10%positive)). rewrite Z.mod_small in C1 by lia.
      eapply Forall_impl; [|apply (chain_facts_bases rhoE (SVar 28) (l :: W') HCH); cbn [eval]; lia].
      intros o0 (B & L & Hh). cbn [eval] in B. repeat split; try assumption; lia. }
    pose proof (proj1 (Forall_forall _ _) LNK o' Ho') as (L1 & L2 & L3).
    assert (WF' : OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.F0A_dzone.rng_below GW o' = true).
    { unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.F0A_dzone.rng_below in Hb |- *. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.F0A_dzone.same_rng in Hs. apply andb_prop in Hs as [Hs S3]. apply andb_prop in Hs as [S1 S2].
      apply sv_eqb_sound in S1, S2, S3. rewrite <- S1, <- S2, <- S3. exact Hb. }
    rewrite <- (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.F0A_dzone.rng_below_agree GW rr rhoE o' HAG WF') in Ha.
    destruct o' as [ob olo ohi ocs od]. cbn [ob_base ob_lo ob_hi] in L1, L2, L3. subst olo ohi. rewrite obj_range_mk in Ha by lia. cbn [fst snd] in Ha.
    unfold top_high in HTOP. unfold free_depth in HDEP. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.F0A_dzone.zoneF. cbn zeta. do 6 right. lia.
Qed.
End VARIANT.

Lemma room24 : ltac2:(tb__ "0|2|
S13S8S0A1S52VA;A1S9S0A1A3S13S5S9fZ18M0Sa5VA;G0A2M1A2S6A3S1aS1bS47G1A1S9dA2Sa4G0A1A2F_;F_;").
Proof.
  intros HC0. pose proof HA as (HG & _ & _ & HRest & _). destruct HRest as (_ & _ & _ & _ & HQR & _).
  destruct (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.PrimRoom.quarantine_counts _ A HQR) as (Q1 & Q2 & Q3 & Q4).
  apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.RefillCL.rfacts_room A rho tp md 24 (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.InvQC.AInvA_QC A rho tp md HA) ltac:(lia) HC0).
  exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.RefillCL.q_ids_bound_of_counts A 24 ltac:(lia) Q1 Q2 Q3 Q4).
Qed.
Lemma cnt24R : ltac2:(tb__ "0|0|
S13S8S0A1S52VA;A1S9S0A1A3S13S0S55S9eVA;Z18A2A1Z1A3F_;").
Proof.
  intros HC0. pose proof HA as (HG & _ & _ & HRest & _). destruct HRest as (_ & _ & HPR & _ & HQR & _).
  destruct HPR as (PL & _ & _ & PC). pose proof (PC 24 ltac:(lia)) as P24.
  pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.RebuildRP.entry_cls_pure _ A 24 ltac:(lia) HG P24 HQR) as CP.
  destruct (refill_pure 24 _ _ ltac:(lia) CP HC0 (room24 HC0)) as (_ & K).
  unfold cnt24, cache24, refillA, nthZ. cbn [aa_cls]. change (Z.to_nat 24) with 24%nat. rewrite nth_list_upd_same by (rewrite PL; lia).
  unfold nthZ in K. change (Z.to_nat 24) with 24%nat in K. rewrite K. reflexivity.
Qed.

Section CF.
Variable f : bool.
Hypothesis QC : qcondCx f A.
Lemma HC0 : cache24 A = []. Proof. exact (proj2 QC). Qed.
Lemma carve_NVC : ltac2:(tb__ "0|0|
S4cS17S3cVrho1;A1S5fVf;A1A3").
Proof.
  destruct carve_inst as [CI1 CI2]. pose proof (carve_pcc HC0) as CP. destruct QC as [QT _]. unfold NVC. destruct f.
  - destruct QT as [HNE HK]. repeat apply Forall_cons; try apply Forall_nil; try assumption.
    + exact (carve_cQ A rho tp md p n HA HL t Ht jv Hjv HNE).
    + exact (carve_bhf A rho tp md p n HA HL t Ht jv Hjv HNE HK).
  - repeat apply Forall_cons; try apply Forall_nil; try assumption.
    exact (carve_cQe A rho tp md p n HA HL t Ht jv Hjv QT).
Qed.
Lemma inz_NVC : ltac2:(tb__ "0|0|
S38S24S33S34Vrho1;VzbF;S50S4fS61Vf;A1A5S4dS17S24S18S5fVf;A1A4S67Vf;A1A5").
Proof.
  pose proof (topG_range G) as ACV. pose proof geoT as (T1 & T2 & _ & T4). assert (EQ : bv_unsigned (eval rho1 cQ) = ag_thread G + 80) by exact (E_cQ A rho tp md p n HA t Ht jv). pose proof EcA1 as EA.
  assert (HB : aa_q_thread A <> [] -> bv_unsigned (eval rho1 vQB) = qbF /\ HIGH_SHADOW_END <= qbF /\ qbF + kQuarantineBatchSize <= 140737479966720).
  { intros HNE. pose proof (qF A rho tp md p n HA HL) as QF. cbn zeta in QF. destruct QF as (_ & _ & _ & _ & _ & QL).
    destruct (QL HNE) as (_ & _ & _ & _ & _ & _ & _ & _ & BS1 & BS2 & _). clear QL.
    pose proof (geomF A rho tp md n HA t) as (_ & _ & _ & _ & _ & S1 & S2 & _). rewrite kSpaceSize_val in S2, BS2. fold G in S1, S2, BS1, BS2.
    unfold qbF, lastq, HIGH_SHADOW_END, kQuarantineBatchSize in *. change (eval rho1 vQB) with (eval (rhoF_of A rho p n t jv) vQB). rewrite (E_vQB A rho p n t jv Hjv HNE). unfold lastq. rewrite u64_lit by lia. repeat split; lia. }
  destruct QC as [QT _]. unfold NVC, ZD_NVC, ZUC, K_qc, K_qce, K_bhf, K_pcc, K_i1, K_i2. destruct f; cbn [map carve_obj].
  - destruct QT as [HNE HK]. destruct (HB HNE) as (EB & Q1 & Q2). unfold kQuarantineBatchSize, HIGH_SHADOW_END in *.
    repeat apply Forall2_cons; try apply Forall2_nil.
    all: unfold in_zone; split; [cbn; tauto | split; [cbn; lia | split; [cbn; lia | right]]].
    all: unfold carved; rewrite obj_range_mk by lia; cbn [fst snd zbF]; rewrite ?EQ, ?EB, ?EA; cbn [eval]; rewrite ?u64_lit by lia; unfold G in *; lia.
  - repeat apply Forall2_cons; try apply Forall2_nil.
    all: unfold in_zone; split; [cbn; tauto | split; [cbn; lia | split; [cbn; lia | right]]].
    all: unfold carved; rewrite obj_range_mk by lia; cbn [fst snd zbF]; rewrite ?EQ, ?EA; cbn [eval]; rewrite ?u64_lit by lia; unfold G in *; lia.
Qed.
Lemma ZUC_le : ltac2:(tb__ "0|0|
S2S37S2R1S61Vf;A1A3S5dR2U4A2F_;Fz;"). Proof. intros z Hz. unfold ZUC in Hz. destruct f; cbn in Hz; lia. Qed.
Lemma ZUC_4 : ltac2:(tb__ "0|0|
S37S2U4S61Vf;A1A3S16S13S8S3fA1S41VA;A1S9S3fA1A3A1F_;").
Proof. intros H4. destruct QC as [QT _]. unfold ZUC in H4. destruct f; [exact (proj1 QT) | cbn in H4; exfalso; lia]. Qed.
Lemma ZUC_03 : ltac2:(tb__ "0|0|
S2S5dR1U3A2S37S2R2S61Vf;A1A3F_;Fz;").
Proof. intros z Hz. unfold ZUC. destruct z as [|[|[|[|z]]]]; [| | | |lia]; destruct f; cbn; tauto. Qed.

Lemma holds_VFC : ltac2:(tb__ "0|0|
S4cS26S2bVrho1R;A1S66Vf;A1A3").
Proof.
  pose proof (topG_range G) as ACV. pose proof (geomF A rho tp md n HA t) as (_ & _ & _ & _ & _ & S1 & S2 & S3 & _). rewrite kSpaceSize_val in S2. unfold HIGH_SHADOW_END in S1. fold G in S1, S2, S3.
  assert (E127 : rw rho1R 127%positive = Z_to_bv 64 1) by (change (rw rho1R 127%positive) with (Z_to_bv 64 (cnt24 (refillA A 24))); rewrite (cnt24R HC0); reflexivity).
  assert (E155 : rw rho1R 155%positive = Z_to_bv 64 (ag_spacebeg G)) by reflexivity.
  assert (E120 : rw rho1R 120%positive = Z_to_bv 64 (Z.of_nat (length (aa_q_thread A)))) by reflexivity.
  assert (HFQB : Forall (holds rho1R) F_QB).
  { unfold F_QB, vPK, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states.vSB. unfold HIGH_SHADOW_END. rewrite kSpaceSize_val.
    repeat apply Forall_cons; try apply Forall_nil; cbn [holds eval]; rewrite ?E127, ?E155, ?u64_lit by lia; try lia.
    all: split; [lia | exact S3]. }
  destruct QC as [QT _]. unfold VFC. destruct f; cbn [VFACT]; [|exact HFQB].
  destruct QT as [HNE HK]. apply Forall_app. split; [exact HFQB|].
  pose proof (qF A rho tp md p n HA HL) as QF. cbn zeta in QF. destruct QF as (_ & _ & _ & QS & QLB & QL).
  destruct (QL HNE) as (_ & _ & _ & _ & _ & BK & _ & B16a & BS1 & BS2 & _). clear QL. unfold kQuarantineCacheMax in QS. rewrite kSpaceSize_val in BS2. fold G in BS1, BS2.
  assert (E122 : rw rho1R 122%positive = Z_to_bv 64 (qb_addr (lastq A))).
  { change (rw rho1R 122%positive) with (Z_to_bv 64 (match aa_q_thread A with [] => j_qb jv | _ => qb_addr (lastq A) end)). destruct (aa_q_thread A); [congruence | reflexivity]. }
  assert (A8 : qb_addr (lastq A) mod 8 = 0) by (unfold lastq; rewrite <- (Z.mod_mod_divide _ 16 8) by (exists 2; reflexivity); rewrite B16a; reflexivity).
  assert (LN : 0 < Z.of_nat (length (aa_q_thread A)) <= 128) by (destruct (aa_q_thread A); [congruence|]; cbn [length] in *; lia).
  assert (QB64 : 0 <= qb_addr (lastq A) < 2 ^ 64) by (unfold lastq, kQuarantineBatchSize in *; lia).
  unfold vQN. repeat apply Forall_cons; try apply Forall_nil; cbn [holds eval branch_taken]; unfold bv_eqb; rewrite ?E120, ?E122, ?u64_lit by lia; try lia.
  all: try (rewrite Z.eqb_eq; lia).
  all: split; [lia | exact A8].
Qed.

Theorem instG_here_C : ltac2:(tb__ "0|0|
S5S8S7cA1S7dS88R3Vp;Vn;A3S89R4R3R2S5fVf;A1S66Vf;A1Vrho1R;Vp;Vn;S6eVn;A1S40VG;A1AaF_;Fst;FW;Fkhi;").
Proof.
  intros khi W st HK. pose proof (topG_range G) as ACV. pose proof (blkF_geom A rho tp md p n HA HL HCL) as (B1 & B2 & B3 & B4 & _ & _ & BN & _ & _). unfold blk_geo in B1. pose proof (N8_facts n B3) as (N1 & N2 & N3 & N4).
  pose proof (blkF_mem A rho tp md p n HA HL HCL) as (t' & _ & _ & _ & _ & HSH & HPAD). unfold IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in B1.
  destruct (offp_chk f) as (OK1 & OK2 & OK3).
  pose proof (fun i Hi => pins_off i Hi) as PW.
  constructor.
  - change (rw rho1R 12%positive) with (rw rho 12%positive). rewrite <- Hp12. symmetry. apply Z_to_bv_bv_unsigned.
  - change (rw rho1R 13%positive) with (rw rho 13%positive). rewrite <- Hn13. symmetry. apply Z_to_bv_bv_unsigned.
  - reflexivity.
  - reflexivity.
  - split; [unfold blk_geo, IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END; exact B1|]. fold G in B4. repeat split; lia.
  - apply (Forall_carve_ok_on offp rho1 rho1R PW pins_rl pins_rm _ OK1). exact (carve_G (NVC f) carve_NVC).
  - apply (Forall_spec_zone_on offp rho1 rho1R PW pins_rl _ _ _ _ OK1). exact (zone_G (NVC f) (ZD_NVC f) (ZUC f) ZUC_le ZUC_4 ZUC_03 inz_NVC (ZD_chkC f) carve_NVC).
  - apply (pd_on offp rho1 rho1R PW pins_rl _ OK1). exact (pd_G (NVC f) (ZD_NVC f) (ZUC f) ZUC_le ZUC_4 ZUC_03 inz_NVC (ZD_chkC f)).
  - intros z Hz. destruct (HSH z Hz) as [x Hx]. exists x. rewrite pins_rm0. rewrite view_in in Hx; [exact Hx|].
    unfold Sh, SHADOW_OFF in *. split; [lia|]. pose proof (Z.div_lt_upper_bound (p + N8 n) 8 (2 ^ 50) ltac:(fold G in B4; lia) ltac:(fold G in B4; lia)). pose proof (Z.div_le_mono p (p + N8 n) 8 ltac:(lia) ltac:(lia)).
    assert (N8 n / 8 <= (p + N8 n) / 8) by (apply Z.div_le_mono; lia). lia.
  - intros z Hz. destruct (HPAD z Hz) as [x Hx]. exists x. rewrite pins_rm0. rewrite view_in in Hx; [exact Hx | fold G in B4; lia].
  - apply Forall_app. split; [|apply Forall_app; split; [|apply Forall_app; split; [|exact holds_VFC]]].
    + apply (Forall_holds_on offp rho1 rho1R PW pins_rl F_geom_fn); [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | exact (holds_geom A rho tp md p n HA t Ht jv)].
    + apply (Forall_holds_on offp rho1 rho1R PW pins_rl (tl (F_pc khi))); [destruct khi; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | exact (holds_p A rho tp md p n HA HL HCL Hp12 Hn13 t Ht jv khi HK)].
    + apply (Forall_holds_on offp rho1 rho1R PW pins_rl F_cas); [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | exact (holds_cas A rho tp md p n HA HL HCL Hp12 t Ht jv)].
  - intros rho' Hag. pose proof (rig_F A rho tp md p n HA HL HCL Hp12 Hn13 t Ht jv rho') as RG.
    assert (AG1 : agree_vals NF rho' rho1).
    { destruct Hag as [Aw Al]. split; [intros i Hi; rewrite (Aw i Hi); apply pins_off; unfold offp; unfold NF in Hi; destruct (Pos.eqb_spec i 127), (Pos.eqb_spec i 130); subst; try reflexivity; lia | intros l; rewrite (Al l); apply pins_rl]. }
    destruct (RG AG1) as [_ R2 R3 R4 R5 R6 R7 R8 R9 R10].
    pose proof (pins_off 12 eq_refl) as P12. pose proof (pins_off 13 eq_refl) as P13. pose proof (pins_off 103 eq_refl) as P103. pose proof (pins_off 104 eq_refl) as P104.
    pose proof (pins_off 105 eq_refl) as P105. pose proof (pins_off 106 eq_refl) as P106. pose proof (pins_off 107 eq_refl) as P107.
    constructor; [exact Hag | | | | | | | | | ]; rewrite ?P12, ?P13, ?P103, ?P104, ?P105, ?P106, ?P107; assumption.
Qed.
End CF.

Theorem rd_zone_C : ltac2:(tb__ "0|1|
S5S6dR1VA;A2S2S2aS2dS5eVrho1R;R1A3S7bVA;R2A2S1aS4aQ40S25R3S78A2A2S1dS7aA1A2S4cS26S2bR4A1S79S77R5A1A1A3S24S13S5S8aS5fR9A1R7R1A3S6A3S13S5S74S5eR2A2S6A3S0S14S1aSbS0S0S29R9R4A2M0A3R1A2S1cR1ScS0S0G0A3A2A2S73VA;R2A2F_;Fa;F_;F_;Fo;F_;F_;F_;F_;FrhoE;FnW;F_;Ff;").
Proof.
  intros f QC.
  refine (rd_zoneG (NVC f) (ZD_NVC f) (ZUC f) _ _ _ _ (ZD_chkC f) rho1R pins_off pins_rl (proj1 (offp_chk f))).
  - first [exact (ZUC_le f QC) | exact (ZUC_le f)].
  - first [exact (ZUC_4 f QC) | exact (ZUC_4 f)].
  - first [exact (ZUC_03 f QC) | exact (ZUC_03 f)].
  - exact (inz_NVC f QC).
Qed.

Lemma ZD_chkN0 : ltac2:(tb__ "0|1|
S14S13S5S35SaS33S4eS9S33A1A3M0A1S6A3S14S13S5S36S33S51G0A3S6A3S14S13S5S36S17S53SaS17S3bS62A3A3S6A3S13S5S36S33S72G0A3S6A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma ZUN_le : ltac2:(tb__ "0|0|
S2S37S2R1S4S2U0S4S2U1S4S2U2S4S2U3S9S2A1A3A3A3A3A3S5dR2U4A2F_;Fz;"). Proof. intros z Hz. cbn in Hz. lia. Qed.
Lemma ZUN_4 : ltac2:(tb__ "0|0|
S37S2U4S4S2U0S4S2U1S4S2U2S4S2U3S9S2A1A3A3A3A3A3S16S13S8S3fA1S41VA;A1S9S3fA1A3A1F_;"). Proof. intros H4. cbn in H4. exfalso. lia. Qed.
Lemma ZUN_03 : ltac2:(tb__ "0|1|
S2S5dR1U3M0A2S37S2R2S4S2U0S4S2U1S4S2U2S4S2G0S9S2A1A3A3A3A3A3F_;Fz;"). Proof. intros z Hz. destruct z as [|[|[|[|z]]]]; cbn; try tauto. lia. Qed.
Theorem instG_here_N : ltac2:(tb__ "0|0|
S5S8S7cA1S7dS88R3Vp;Vn;A3S1cS96Vn;A2S89R5R4R3S62S6bVrho1;Vp;Vn;S6eVn;A1S40VG;A1AaF_;F_;Fst;FW;Fkhi;").
Proof.
  intros khi W st HK HBG. pose proof (topG_range G) as ACV. pose proof (blkF_geom A rho tp md p n HA HL HCL) as (B1 & B2 & B3 & B4 & _ & _ & BN & _ & _). unfold blk_geo in B1. pose proof (N8_facts n B3) as (N1 & N2 & N3 & N4).
  pose proof (blkF_mem A rho tp md p n HA HL HCL) as (t' & _ & _ & _ & _ & HSH & HPAD). unfold IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in B1. fold G in B4.
  assert (HIN : Forall2 (in_zone rho1 zbF zloF zhiF [0; 1; 2; 3]%nat) (map carve_obj NVN) []) by constructor.
  constructor.
  - change (rw rho1 12%positive) with (rw rho 12%positive). rewrite <- Hp12. symmetry. apply Z_to_bv_bv_unsigned.
  - change (rw rho1 13%positive) with (rw rho 13%positive). rewrite <- Hn13. symmetry. apply Z_to_bv_bv_unsigned.
  - reflexivity.
  - reflexivity.
  - split; [unfold blk_geo, IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END; exact B1|]. repeat split; lia.
  - exact (carve_G NVN (Forall_nil _)).
  - exact (zone_G NVN [] [0; 1; 2; 3]%nat ZUN_le ZUN_4 ZUN_03 HIN ZD_chkN0 (Forall_nil _)).
  - exact (pd_G NVN [] [0; 1; 2; 3]%nat ZUN_le ZUN_4 ZUN_03 HIN ZD_chkN0).
  - intros z Hz. destruct (HSH z Hz) as [x Hx]. exists x. change (rm rho1) with (rm rho). rewrite view_in in Hx; [exact Hx|].
    unfold Sh, SHADOW_OFF in *. split; [lia|]. pose proof (Z.div_lt_upper_bound (p + N8 n) 8 (2 ^ 50) ltac:(lia) ltac:(lia)). pose proof (Z.div_le_mono p (p + N8 n) 8 ltac:(lia) ltac:(lia)).
    assert (N8 n / 8 <= (p + N8 n) / 8) by (apply Z.div_le_mono; lia). lia.
  - intros z Hz. destruct (HPAD z Hz) as [x Hx]. exists x. change (rm rho1) with (rm rho). rewrite view_in in Hx; [exact Hx | lia].
  - apply Forall_app. split; [exact (holds_geom A rho tp md p n HA t Ht jv)|]. apply Forall_app. split; [exact (holds_p A rho tp md p n HA HL HCL Hp12 Hn13 t Ht jv khi HK)|].
    apply Forall_app. split; [exact (holds_cas A rho tp md p n HA HL HCL Hp12 t Ht jv)|].
    unfold VFN, BIGF. apply Forall_cons; [|apply Forall_nil]. cbn [holds eval]. change (rw rho1 13%positive) with (rw rho 13%positive). rewrite Hn13, u64_lit by (unfold kQuarantineMax; lia). exact HBG.
  - exact (rig_F A rho tp md p n HA HL HCL Hp12 Hn13 t Ht jv).
Qed.
Theorem rd_zone_N : ltac2:(tb__ "0|1|
S2S2aS2dS5eVrho1;R1A3S7bVA;R2A2S1aS4aQ40S25R3S78A2A2S1dS7aA1A2S4cS26S2bR4A1S79S77R5A1A1A3S24S13S5S8aS62R7R1A3S6A3S13S5S74S5eR2A2S6A3S0S14S1aSbS0S0S29R9R4A2M0A3R1A2S1cR1ScS0S0G0A3A2A2S73VA;R2A2F_;Fa;F_;F_;Fo;F_;F_;F_;F_;FrhoE;FnW;").
Proof.
  assert (HIN : Forall2 (in_zone rho1 zbF zloF zhiF [0; 1; 2; 3]%nat) (map carve_obj NVN) []) by constructor.
  exact (rd_zoneG NVN [] [0; 1; 2; 3]%nat ZUN_le ZUN_4 ZUN_03 HIN ZD_chkN0 rho1 (fun _ _ => eq_refl) (fun _ => eq_refl) ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)).
Qed.
End FACTSC.
End F0A_instokC.

(* [comment removed for export] *)
Module SpineMallocQ2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "and"; "eq"; "or"; "ex"; "True"; "@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "mul"; "lt"; "modulo"; "div"; "of_nat"; "@Corelib.Init.Datatypes"; "list"; "pair"; "bool"; "cons"; "true"; "nil"; "prod"; "Some"; "option"; "false"; "app"; "andb"; "length"; "nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sv"; "rw"; "sobj"; "ss_next"; "sprop"; "obj_range"; "ss_lenient"; "holds"; "rm"; "ss_facts"; "ss_objs"; "sstate"; "swf"; "agree_below"; "eval"; "ranges_disjoint"; "smatch"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "leafA"; "la_state"; "sym_runA"; "axst"; "ax_setS"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "ag_thread"; "ag_spacebeg"; "ageom"; "aa_cache_inited"; "ag_ctx"; "class_state"; "cs_allocated_user"; "cs_cache"; "cs_free_array"; "cs_mapped_free_array"; "cs_mapped_user"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "ulink"; "ustop"; "UStopLeOrPc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillJ"; "JR"; "PCE"; "phase"; "frozen"; "ghosts"; "ph_fill"; "gh_new"; "gh_nf"; "ph0"; "ph_cnt"; "ph_pop"; "zoneR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "cls_of"; "cnt_of"; "cst_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b5.SpineMallocQ1"; "entryRq"; "cQ0"; "BASEFq"; "BASEOq"; "armint"; "factsQ"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR"; "k_e"; "GR"; "fa_e"; "ri_e"; "vFA"; "vK"; "vRI"; "O_pcm"; "O_ri"; "cR1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.SpineMallocQ2"; "cfacts"; "rigids"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3"; "skel"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Size"; "max_count"; "kSpaceSize"; "region_info"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "cell_ok"; "mkACell"; "present"; "bview"; "view"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "diffs_ok"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "O_pcc0"; "O_st"; "pc_base"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.InvQC"; "AInvQC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit"; "FACAP"; "MUCAP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel"; "kchunks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2"; "only_var"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5"; "tab1_ok"; "@Stdlib.Lists.List"; "In"; "incl"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SMGlue InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require PrimCredit PrimCreditLaws RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillTR RefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.InvQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RefillS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b5.SpineMallocQ1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition rigids (A : AA) (rb r : valuation) : Prop := ltac2:(tb__ "0|5|
S35Q40M0S1dVrb;PcM1A2M2A2S5S56R1A1S5S37VA;A1S3aS0S1S33G0A1M3S1dVr;G1A2G2A3S0S1G3S1dVr;P94A2S34G0S6fR2A1A2A3S0S1G3S1dVr;P97A2S34G0S38R1A1A2A3S0S1G3S1dVr;P98A2S34G0S3cR1A1A2A3S0S1G3S1dVr;P9bA2S34G0S39R1A1M4A2A3S0S1G3S1dVr;P9cA2S34G0S7G4S71A2A2A3S0S4S1G3S1dVr;P9eA2S34G0R2A2A3A2A2A2A2A2A2A2TG;Tc;Tnv;").
Lemma entry_rigids : ltac2:(tb__ "0|0|
S36S1bSdS33Q40A1A1S45SdS47A1S48S1bS1bS59R8R7R6R5R4R3R2A7S4dR8R2A2S6cRaR9R3A3F_;F_;Fr;Frho;Fst;FW;Fmd0;Ftp0;Frb;FA;").
Proof.
  intros A rb tp0 md0 W st rho r (((E151 & E152 & E155 & E156) & E158 & E148 & _) & _) [Fw _].
  unfold rigids. cbn zeta.
  split; [symmetry; apply Fw; lia|]. split; [rewrite <- (Fw _) by lia; exact E148|]. split; [rewrite <- (Fw _) by lia; exact E151|].
  split; [rewrite <- (Fw _) by lia; exact E152|]. split; [rewrite <- (Fw _) by lia; exact E155|]. split; [rewrite <- (Fw _) by lia; exact E156|].
  split; [exact I|]. rewrite <- (Fw _) by lia. exact E158.
Qed.

Definition cfacts (A : AA) (rb : valuation) : Prop := ltac2:(tb__ "0|d|
S35Q40S1dVrb;PcA2A2S5S56R1A1S5S58VA;R2A2S3dS37VA;A1S3aS39R1A1S5S38R2A1S5S0S0S0S6Z1M0R6A2S6R6Zfc00A2A2S0S0S6G0R5A2S6R5Z1eA2A2S0S0S6Z20S6fR5A1M1A2S6G1Z10000M2A2A2S1S5SaG1Z10A2Z0M3A3A2A2A2S0S0S0S6G0S85R5A1M4A2S6G4Z8A2A2S0S1S5S8Z2G4A2S70R5A1A3S6S8G4G1A2G2A2A2A2S0S0S1S5SaS42R4A1M5Z40000M6A2G3A3S0S0S6G3S3eR4A1M7A2S6G7G5A2A2S0S6G5Ze0000000A2S0S1S5SaG7G1A2G3A3S9G5S7G7G1A2A2A2A2A2A2S0S0S1S5SaS41R4A1M8G6A2G3A3S0S6S8Z4ScS19S5S40R4A1A2A1A2G8A2S6G8Z20000000A2A2A2S0S0S6G5S84R5A1A2S0S6G8S83R5A1A2S1SdS5A1S3fR4A1S12S5A1A3A2A2S0S0S1S5SaR2G2A2G3A3S0S6Z100080000000R2A2S0S6S7S7R2Z2000000000A2Z1000M9A2MaS43R3A1MbA2S6GbZ7fffff800000A2A2A2A2S0S0S6G9R1A2S0S6S7R1G9A2McGbA2S0S2S6GcG2A2S6Z646000R1A2A2S2S6GcR2A2S6GaR1A2A2A2A2A2S2S6GcZ7fff7000A2S6Z10007fff8000R1A2A2A2A2A2A2A2A2A2TT;TSB;TG;Tcs;Tc;Tnv;").
Lemma entry_cfacts : ltac2:(tb__ "0|0|
S36S1bSdS33Q40A1A1S45SdS47A1S48S1bS59R7R6R5R4R3R2R1A7S6bR8R7A2F_;Frho;Fst;FW;Fmd0;Ftp0;Frb;FA;").
Proof.
  intros A rb tp0 md0 W st rho (_ & HA & _ & _ & _ & Hnv & _ & Hcnt & _). unfold cfacts. cbn zeta.
  set (nv := bv_unsigned (rw rb 12%positive)) in *.
  pose proof (cls_facts nv Hnv) as (C1 & C2 & C3 & C4). destruct (kchunks_facts _ C1) as (K1 & K2 & K3).
  destruct (cap_facts _ C1) as (S1 & _).
  pose proof HA as (HG & _ & _ & HRest & _ & HI3 & _).
  destruct HRest as (_ & _ & Hprim & _). destruct Hprim as (_ & _ & _ & P4). specialize (P4 (cls_of nv) C1).
  unfold class_repr in P4.
  destruct P4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & N2 & N3 & N4 & N5 & N6 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TI10 & _ & MC10 & FC10).
  unfold kUserMapSize, kUserSpaceSize, kRegionSize, kFreeArraySize, kFreeArrayMapSize in N1, N2, N3, N5, N6.
  pose proof (geom_old _ HG) as HG'. rewrite FS_total_val, kSpaceSize_val in HG'. unfold HIGH_SHADOW_END, IMG_HI, PG in HG'.
  destruct HG' as (_ & _ & _ & _ & G5 & G6 & _ & _ & _ & _ & _ & G12 & G13 & G14 & _).
  pose proof (geom_bands _ HG) as (_ & TB & _ & _ & TI & _ & _). unfold IMG_LO, IMG_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in TI, TB.
  pose proof (topG_range (aa_geom A)) as TG. destruct (proj1 HI3) as (PS1 & _). rewrite kSpaceSize_val in PS1.
  assert (Hc0 : cs_cache (cst_of A nv) = []).
  { unfold cnt_of in Hcnt. destruct (cs_cache (cst_of A nv)); [reflexivity | cbn [length] in Hcnt; lia]. }
  unfold cst_of. fold (cst_of A nv).
  split; [repeat split; first [exact C3 | lia]|]. split; [repeat split; lia|].
  split; [unfold cst_of; repeat split; first [exact N1 | exact N4 | lia]|].
  split; [unfold cst_of; repeat split; first [exact N5 | lia]|].
  split; [split; [exact MC10 | split; [exact FC10 | exact Hc0]]|].
  split; [repeat split; first [exact G12 | lia]|]. split; [repeat split; lia | lia].
Qed.

Definition tabK_okb : bool := ltac2:(tb__ "0|2|
S18S87PdcM0S61S5SbR1Z2M1A2Lz;G1UfA5S86G0S61A2A2").
Lemma tabK_ok : tabK_okb = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma r1_diffs : ltac2:(tb__ "0|1|
S36S1bS1bS6bR3R2A2S6cR4R3R2A3S4eR5R4R3A3S7aR4S10S13S1cS1cA2M0SeS1cS1cS64S67A4S10G0SeS1cS1cS61S66A4S10G0SeS1cS1cS63S65A4S12G0A1A3A3A3A2F_;F_;F_;Fr;Frb;FA;").
Proof.
  intros A rb r CF RG GH. unfold cfacts in CF. cbn zeta in CF.
  destruct CF as ((_ & C1 & _) & (K1 & K2 & _) & _ & _ & _ & (G12 & G13 & G14 & TG) & _ & _).
  destruct RG as (_ & _ & _ & _ & E155 & E156 & _ & E158). destruct GH as (Q220 & _ & _ & _ & _ & Q225 & Q226 & Q227 & _).
  unfold region_info, kRegionInfoStride in Q225. rewrite kSpaceSize_val in Q225, E156.
  unfold FAb, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize in Q226.
  unfold diffs_ok. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
  - unfold ri_e, vRI, vRIS, V_CLS. cbn [eval]. rewrite E156, E158, Q225. apply bv_eq.
    rewrite add_val, sll_val, !u64_lit by lia. change (7 mod 64) with 7. rewrite Z.shiftl_mul_pow2 by lia.
    rewrite (Z.mod_small (_ * 2 ^ 7)) by lia. rewrite Z.mod_small by lia. lia.
  - unfold vK. cbn [eval]. rewrite Q227. pose proof tabK_ok as TK. unfold tabK_okb in TK. apply andb_prop in TK as [TK OV].
    rewrite (tab1_ok_sound 220 k_e (fun z => z / 2) 2 15 r (max_count (cls_of (bv_unsigned (rw rb 12%positive)))) TK OV Q220) by lia.
    unfold kchunks. reflexivity.
  - unfold fa_e, vFA, vSB, V_CLS. cbn [eval]. rewrite E155, E158, Q226. apply bv_eq.
    rewrite add_val, add_val, sll_val, !u64_lit by lia. change (32 mod 64) with 32. rewrite Z.shiftl_mul_pow2 by lia.
    rewrite (Z.mod_small (_ * 2 ^ 32)) by lia. rewrite (Z.mod_small (_ + 3758096384)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma arm_base_disj : ltac2:(tb__ "0|4|
S36S1bSdS33Q40A1A1S45SdS47A1M0S48S1bS27SdS1eA1M1S1bS13SdS46A1S7dA2S1S48R6S49A3S1G0R8S12S47A1A3F_;S59RcRbRaR9R8R7R6A7S4dRcR4A2S2cS7cR5R7R4A4S1SdS13S13S1cS1cA2S1cA2M2A1M3S5fS1eG2S6dS26R8A1A4S5fS1eG2S6dS17S1eS5cRbA1R7A3A4A3S89S20S5bRcRbA2S25R9A1A3S3G1G1S3G1G1S0S1G1S26RcA1S17S1eR2R1A3A3S0S1G3S5fS1eG2S6dR1A4S5fS1eG2S6dRbA4A3S5S5S5dS37R15A1R2R1A3S60S1eS1eS2bS21ReR1A2SeS5S5R4R3A4A2Lo';R5A3F_;Fhi;Flo;A2A2Lox;A2Lob;A2F_;F_;F_;F_;F_;F_;Fw;Fr;Fextra;FS;Frho;Fst;FW;Fmd0;Ftp0;Frb;FA;").
Proof.
  intros A rb tp0 md0 W st rho S extra r w HW HE HFz Hsm HSK HXF.
  pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as (_ & _ & R151 & R152 & _).
  destruct HE as (_ & HA & _ & _ & _ & _ & Htop & _).
  pose proof HA as (HG & _ & _ & _ & _ & HI3 & _). pose proof (proj1 HI3) as HS3.
  destruct HFz as [Fw _].
  pose proof (smatch_facts_hold _ _ _ _ Hsm) as HFa.
  assert (HFX : forall p, In p (BASEFq W st) -> holds r p) by (intros p Hp; exact (proj1 (Forall_forall _ _) HFa p (HXF p Hp))).
  destruct (map_eq_app _ _ _ _ ltac:(rewrite <- map_app; exact HSK)) as (ob & ox & EO & SKb & SKx).
  exists ob, ox. split; [exact EO|]. split; [exact SKx|].
  intros lo hi HI.
  apply (base_zone (aa_geom A) r S w ob lo hi HG HS3 Hsm); [intros o Ho; rewrite EO; apply in_or_app; left; exact Ho | exact SKb | | | exact R151 | exact R152 | exact HI].
  - apply HFX. unfold BASEFq, pre_facts. cbn; tauto.
  - unfold top_high in Htop. rewrite <- (Fw 10%positive) by lia. rewrite <- (Fw V_DEPTH) by (unfold V_DEPTH; lia). exact Htop.
Qed.

Lemma arm_extra_ranges : ltac2:(tb__ "0|4|
S36S1bS1bS6bR3R2A2S6cR4R3R2A3S4eR5R4R3A3S38S37R6A1A1S5S72S39S37R7A1A1S56S35Q40M0S1dR6PcA2A2A1A2S5S0S1S5S35G0S2aR6S80A2A2S4bR8R7A2M1A3S0S1S13S5S5A2M2S21R6S7eA2SeS5S5G1S7G1Z4A2M3A4A3S0S1G2S21R6S7fA2SeS5S5S7R2Zad0A2S7R2Zc60A2A4A3S0S1G2S21R6S68A2SeS5S5G3S7G1Z8A2A4A3S1G2S21R6S69A2SeS5S5R1S7R1Z80A2A4A3A2A2A2A2Tri;TT;F_;F_;F_;Fr;Frb;FA;").
Proof.
  intros A rb r CF RG GH T ri. unfold cfacts in CF. cbn zeta in CF.
  destruct CF as ((_ & C1 & _) & _ & _ & _ & _ & (G12 & G13 & G14 & TG) & (T1 & T2 & _ & _) & _). fold T in T1, T2.
  destruct RG as (_ & _ & E151 & _ & _ & _ & _ & E158). fold T in E151. destruct GH as (_ & _ & _ & _ & _ & Q225 & _). fold ri in Q225.
  assert (EB : bv_unsigned (eval r pc_base) = PCE A rb).
  { unfold pc_base, vT, V_CLS, PCE. cbn [eval]. rewrite E151, E158. rewrite add_val, add_val, mul_val, !u64_lit by lia.
    rewrite (Z.mod_small (_ * 80)) by lia. rewrite (Z.mod_small (T + 208)) by lia. rewrite Z.mod_small by lia. fold T. lia. }
  split; [exact EB|].
  split; [unfold O_pcc0; rewrite obj_range_mk by lia; rewrite EB; f_equal; lia|].
  split; [unfold O_st, vT; rewrite obj_range_mk by lia; cbn [eval]; rewrite E151, u64_lit by lia; reflexivity|].
  split; [unfold O_pcm; rewrite obj_range_mk by lia; rewrite EB; reflexivity|].
  unfold O_ri, vRI. rewrite obj_range_mk by lia. cbn [eval]. rewrite Q225, u64_lit by (unfold ri, region_info, kRegionInfoStride; rewrite kSpaceSize_val; lia). f_equal; lia.
Qed.

Lemma entry_pc_cells : ltac2:(tb__ "0|2|
S36S1bSdS33Q40M0A1A1S45SdS47A1S48S1bS59R7R6R5R4R3R2R1A7S1SfS3bR8A1S11A3S77S81S24R8A1A2S76S56S35G0S1dR9PcA2A2A1S5S0S73R2S74S7S4bRbRaA2M1Z4A2U4S70R1A1A3A2S0S73R2S74S7G1Z8A2U8S6fR1A1A3A2S75R2G1S7G1Z50A2A3A2A2Tc;Tm0;F_;F_;Frho;Fst;FW;Fmd0;Ftp0;Frb;FA;").
Proof.
  intros A rb tp0 md0 W st rho HE Hini m0 c.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. fold c in CF.
  destruct CF as ((_ & C1 & _) & _ & _ & _ & _ & _ & (T1 & T2 & _) & _).
  destruct HE as (_ & HA & _ & _ & _ & Hnv & _ & Hcnt & _).
  pose proof HA as (HG & _ & _ & HRest & _). destruct HRest as (_ & _ & Hprim & _). destruct Hprim as (_ & _ & _ & P4). specialize (P4 c C1).
  assert (MT : forall z, ag_thread (aa_geom A) <= z < ag_thread (aa_geom A) + 0x1000 -> maskv (fs_footb (aa_geom A)) m0 z = m0 z).
  { intros z Hz. apply maskv_out. apply fs_footb_thread; [exact HG | exact Hz]. }
  unfold class_repr in P4.
  destruct P4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PE & _ & _ & CI & _).
  destruct (CI Hini) as (_ & D2 & D3 & _).
  assert (PCr : PCE A rb = ag_thread (aa_geom A) + 208 + 80 * c) by (unfold PCE; fold c; lia).
  split; [|split].
  - intros j Hj. specialize (D2 j Hj). cbn [c_addr c_w RtCells.c_val] in D2, Hj |- *. rewrite MT in D2 by lia. rewrite PCr. exact D2.
  - intros j Hj. specialize (D3 j Hj). cbn [c_addr c_w RtCells.c_val] in D3, Hj |- *. rewrite MT in D3 by lia. rewrite PCr. exact D3.
  - intros z Hz. rewrite PCr in Hz. destruct (PE z ltac:(lia)) as [b Hb]. exists b. rewrite <- MT by lia. exact Hb.
Qed.

Lemma zone_thread_gen : ltac2:(tb__ "0|7|
S36S1bS4cS5S6bR4R3A2S9Z0M0S4fR3A1A2S0S6G0S51R6R5A2M1A2S0S6S8Z4M2S7G1S50R6R5A2M3A2A2Z20000000A2S6S4fR4A1G3A2A2A2F_;S0S6S7S38S37R6A1A1M4Z120A2R3A2S9R3S7G4Zc60A2A2A2S55R7R6R5R4A4S2S0S6S7S4bR8R7A2M5Z10A2M6R5A2S9R5S7G6S8G2S54R6A1A2A2A2A2S0S1SfS53R6A1S11A3S0S6G5R5A2S9R5S7G5G2A2A2A2A2A2F_;F_;F_;F_;Fz;Fph;Frb;FA;").
Proof.
  intros A rb ph z CF HFL Hz HZ. unfold cfacts in CF. cbn zeta in CF.
  destruct CF as ((_ & C1 & _) & _ & (_ & MU0 & MU1 & _) & (_ & MF0) & _ & (G12 & G13 & G14 & TG) & (T1 & T2 & TI & PS1) & TB).
  pose proof (Zle_0_nat (length (cs_free_array (cst_of A (bv_unsigned (rw rb 12%positive)))))) as NF0.
  unfold zoneR in HZ.
  unfold U0, F0, FAb, free_array, region_beg, region_info, kRegionInfoStride, kUserSpaceSize, kRegionSize, kFreeArraySize, kUserMapSize, kFreeArrayMapSize, Sh, SHADOW_OFF in HZ.
  rewrite kSpaceSize_val in HZ.
  destruct HZ as [[_ X]|[[_ X]|[[_ X]|[[_ X]|[[X X2]|[X|[X|[_ X]]]]]]]]; [exfalso | exfalso | exfalso | exfalso | exfalso | left; exact X | right; exact X | exfalso].
  - clear -X Hz MU0 MU1 C1 G13 G14 TG TB T1 T2. lia.
  - clear -X Hz MU0 MU1 C1 G13 G14 TG PS1 T1 T2. lia.
  - clear -X Hz MF0 NF0 C1 G13 G14 TG TB T1 T2. lia.
  - clear -X Hz MF0 NF0 C1 G13 G14 TG PS1 T1 T2. lia.
  - destruct (HFL X2) as (F1 & F2 & F3). clear -X Hz F1 F2 F3 C1 G13 G14 TG PS1 T1 T2. lia.
  - clear -X Hz C1 G13 G14 TG PS1 T1 T2. lia.
Qed.

Section STEPS.
Let segs : list Segment := segsA.
Variables (A : AA) (Kc : KcA) (rb : valuation) (tp0 : list word) (md0 : Model).
Variable TR : assn -> assn -> Prop.
Hypothesis KIT : TRok Kc TR.
Hypothesis HKc : Kc_ok Kc.
Notation JRp := (JR A Kc rb tp0 md0).

Lemma jr_run : ltac2:(tb__ "0|1|
S1aSdS5A1S31SdS2eA1M0S4cS1bSdS33Q40A1A1S6eS1S15G0A1S30Vsegs;R8R7R6S11A5S14G0R5A2A3S1SfS22S2dR7A1A1S16A3S1SfS78S62S1fS2dR8A1A1A2S11A3S2eS1bS88S2eR2RaA3S29S1fS2dRcA1A1R9R2A3VTR;S44Vsegs;S4aVA;VKc;Vrb;Vtp0;Vmd0;RbA6S2fR4A1R3R9A5R8A2F_;F_;Frho';FL;VTR;S44Vsegs;S4aVA;VKc;Vrb;Vtp0;Vmd0;R8A6RaR7R6A5R5A2F_;F_;F_;F_;FQ;Ftp;Frho;Fph;Fleaves;FE;Fcuts;Ffuel;").
Proof.
  intros fuel cuts E leaves ph rho tp Q Hrun Hl Hn HL.
  apply (tr_run Kc TR KIT fuel cuts E leaves (JRp ph) rho tp Q (JR_K A Kc rb tp0 md0 ph)); [|exact Hrun | exact Hl | exact HL].
  apply JR_stable; [exact HKc | apply Pos.leb_le; exact Hn].
Qed.

Lemma jr_restate : ltac2:(tb__ "0|3|
S31S27SdS13S1cS1cA2A1M0SdS20A1M1S4cS1bSdS33Q40A1A1S6eS1SfS28R7A1S11A3S1S15S13G0G1A2M2A1S7bS2dR9A1R8A2S14G2SeG0G1R7R6A4A2A3S1SfS79S1fR9A1S1fS2dRaA1A1A2S11A3SdS46A1S45S4aVA;VKc;Vrb;Vtp0;Vmd0;R9R8R7R2R1AaS60S20S23R9A1S25S2dReA1A1A3S0S7aRaRdA2S60S20S23RaA1RcA3A2F_;F_;Fmd;Ftr;VTR;S44Vsegs;S4aVA;VKc;Vrb;Vtp0;Vmd0;R8A6S32RcRbA2R7R6A5R5A2VTR;S44Vsegs;S4aVA;VKc;Vrb;Vtp0;Vmd0;R9A6RdR8R7A5R6A2F_;F_;F_;F_;F_;FQ;Ftp;Frho;Fph;Fnf;Fd;FS';FE;").
Proof.
  intros E S' d nf ph rho tp Q Hwf Hsd Hnx Hsem HT.
  apply (tr_pre Kc TR KIT _ _ Q) with (2 := HT). intros w Hw.
  pose proof (SPA_facts_hold segs _ rho E tp w Hw) as HF.
  destruct (Hsem _ _ (proj2 Hw) HF) as [Hd Hn].
  apply (SPA_restate segs _ rho E S' tp w d nf Hwf Hsd); [apply Pos.eqb_eq; exact Hnx | exact Hd | exact Hn | exact Hw].
Qed.

Section PREFIX.
Variable F : nat.
Variables (E3 : axst) (L1 LP LJ : leafA).
Let CR1 : axst := ltac2:(tb__ "0|0|
S6aS5eVE3;A1S2fVL1;A1A2").
Hypothesis R_1 : ltac2:(tb__ "0|1|
S1S15SdS2eA1M0A1S30Vsegs;VF;S10S5Z412e8S12S5A1A3S5aVE3;A1S11A5S14G0S10S2eVL1;S12S2eA1A3A2A3").
Hypothesis LN_0 : ltac2:(tb__ "0|0|
S1SfS22S2dS5aVE3;A1A1A1S16A3").
Hypothesis NX_0 : ltac2:(tb__ "0|0|
S1SfS78S62S1fS2dS5aVE3;A1A1A1A2S11A3").
Hypothesis W_r1 : ltac2:(tb__ "0|0|
S1SfS28S2dVCR1;A1A1S11A3").
Hypothesis D_r1 : ltac2:(tb__ "0|4|
S1S15S13SdS13S1cS1cA2M0A1M1SdS20A1M2A2M3A1S7bS2dS2fVL1;A1A1S2dVCR1;A1A2S14G3SeG1G2S10G0SeS1cS1cS64S67A4S10G0SeS1cS1cS61S66A4S10G0SeS1cS1cS63S65A4S12G0A1A3A3A3S12S20A1A4A2A3").
Hypothesis NX_r1 : ltac2:(tb__ "0|0|
S1SfS79S1fS2dVCR1;A1A1S1fS2dS2fVL1;A1A1A1A2S11A3").
Hypothesis R_2 : ltac2:(tb__ "0|1|
S1S15SdS2eA1M0A1S30Vsegs;VF;S10S5Z41570S10S5Z413ccS12S5A1A3A3VCR1;S11A5S14G0S10S2eVLP;S10S2eVLJ;S12S2eA1A3A3A2A3").
Hypothesis LN_1 : ltac2:(tb__ "0|0|
S1SfS22S2dVCR1;A1A1S16A3").
Hypothesis NX_1 : ltac2:(tb__ "0|0|
S1SfS78S62S1fS2dVCR1;A1A1A2S11A3").

Lemma refill_prefix : ltac2:(tb__ "0|1|
SdS47A1S48S1bS1bSdS33Q40A1A1S6eS59VA;Vrb;Vtp0;Vmd0;R6R5R4A7S1bVTR;S44Vsegs;S4aVA;VKc;Vrb;Vtp0;Vmd0;S52A6M0S2fVLP;A1R1R4A5R3A2Fr';S1bVTR;S44Vsegs;G0S2fVLJ;A1R1R5A5R4A2Fr';VTR;S44Vsegs;G0S5aVE3;A1R6R5A5R4A2F_;F_;F_;FQ;Ftp;Fr;Frho;Fst;FW;").
Proof.
  intros W st rho r tp Q HE HP HJ.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF.
  apply (jr_run F [0x412e8] (cQ0 E3) [L1] ph0 r tp Q R_1 LN_0 NX_0).
  intros L r1 [<-|[]] _.
  apply (jr_restate (la_state L1) (ax_S CR1) _ _ ph0 r1 tp Q W_r1 D_r1 NX_r1).
  { intros tr md (HFz & HGh & _) _. split; [|constructor].
    exact (r1_diffs A rb r1 CF (entry_rigids _ _ _ _ _ _ _ _ HE HFz) HGh). }
  change (ax_setS (la_state L1) (ax_S CR1)) with CR1.
  apply (jr_run F [0x41570; 0x413cc] CR1 [LP; LJ] ph0 r1 tp Q R_2 LN_1 NX_1).
  intros L r2 [<-|[<-|[]]] _; [apply HP | apply HJ].
Qed.
End PREFIX.
End STEPS.

Lemma pc_entry_facts0Q : ltac2:(tb__ "0|3|
S36S1bSdS33Q40A1A1S45S5S82R5R4R3R2A4S0S6Z1R2A2S6R2Zfc00A2A2S1S5S57R7R3A2Z0M0A3S37R8A1S3aS56R5A1S5S7S7S38R2A1Zd0A2S8Z50M1R1A2A2S5S77S7cS24RaA1A2S76S0S73R1S74R2U4G0A3A2S0S75R1R2S7R2G1A2A3S75R1S7S38R4A1M2Zad0A2S7G2Zc60A2A3A2A2Tm;Te;Tc;TG;F_;F_;F_;Fnv;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md nv HA Hnv Hcnt G c e m. unfold e, m, c, G. clear G c e m.
  pose proof (cls_facts nv Hnv) as (C1 & C2 & C3 & C4).
  unfold cnt_of, cst_of in *.
  set (G := aa_geom A) in *. set (c := cls_of nv) in *. set (m := view segsA (rm rho)) in *.
  pose proof HA as (HG & HR & HF & HRest & HM).
  destruct HRest as (Hsep & Hlive & Hprim & _ & _ & _ & _ & HTH & _).
  destruct Hprim as (_ & _ & _ & P4). specialize (P4 c C1).
  assert (MT : forall z, ag_thread G <= z < ag_thread G + 0x1000 -> maskv (fs_footb G) (view segsA (rm rho)) z = m z).
  { intros z Hz. apply maskv_out. apply fs_footb_thread; [exact HG | exact Hz]. }
  unfold class_repr in P4.
  destruct P4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & N2 & N3 & N4 & N5 & N6 & _ & _ & N7 & _ & _ & PE & ND & LV & CI & CN & _ & _ & _ & _).
  set (cs := nthZ (aa_cls A) c cs_empty) in *.
  split.
  { assert (D : cell_ok (maskv (fs_footb G) (view segsA (rm rho))) (mkACell (ag_thread G + 208 + 80 * c) 4 0)).
    { destruct (aa_cache_inited A) eqn:E.
      - destruct (CI eq_refl) as (D1 & _). rewrite Hcnt in D1. exact D1.
      - destruct (CN eq_refl) as [_ FL]. intros j Hj. cbn [c_addr c_w RtCells.c_val] in Hj |- *.
        etransitivity; [apply FL; subst G c; lia|].
        rewrite nth_enc_bytes by lia. unfold MallocInv.le_byte. rewrite Z.mod_0_l, Z.shiftr_0_l, Z.mod_0_l by lia. reflexivity. }
    intros j Hj. specialize (D j Hj). cbn [c_addr c_w RtCells.c_val] in D, Hj |- *. rewrite MT in D by lia. exact D. }
  split.
  { intros z Hz. destruct (PE z Hz) as [b Hb]. exists b. rewrite <- (MT z) by lia. exact Hb. }
  unfold thread_inv in HTH. destruct HTH as [_ HTS]. intros z Hz. assert (Hz' : ag_thread (aa_geom A) + 2688 <= z < ag_thread (aa_geom A) + 3168) by (unfold G in Hz; clear -Hz; lia). destruct (HTS z Hz') as [b Hb]. exists b. rewrite <- (MT z) by lia. exact Hb.
Qed.
End SpineMallocQ2.

(* [comment removed for export] *)
Module SpineCallocR11.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "leafA"; "la_state"; "sym_runA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "sprop"; "ss_next"; "SLit"; "reg_sv"; "eval"; "ss_facts"; "valuation"; "ss_objs"; "swf"; "sprop_below"; "ss_lenient"; "ss_pc"; "sv_below"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "true"; "list"; "nil"; "prod"; "Some"; "option"; "pair"; "app"; "false"; "nat"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Lists.ListDef"; "map"; "firstn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSR"; "GR"; "rMS"; "sMS"; "O_pcm"; "O_ri"; "beg1"; "beg2"; "cX"; "idx_rot"; "nobj"; "relM"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3"; "skel"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Stdlib.ZArith.BinInt.Z"; "add"; "ge"; "le"; "modulo"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "headroom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CRefillJ"; "JR"; "ghosts"; "mlink"; "F0"; "U0"; "entryR"; "frozen"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.CRefillJP"; "ph_set"; "pbase"; "ph_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP"; "O_pcc0"; "O_st"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.SpineCallocR11"; "a0_e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineCallocR2"; "BASEF"; "BASEO"; "rigids"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bk.SpineCallocR9"; "O_piece"; "O_shp"; "@Stdlib.Lists.List"; "forallb"; "incl"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "nodupN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "aa_geom"; "ag_spacebeg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR"; "memset_post"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bl.SpineCallocR10"; "a2_e"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA EntailA CFGA GlueA SummaryA LedgerA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Inv InvLaws GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require al.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillModel RefillBits.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillTR CRefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bl.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillBits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CRefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.CRefillJP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SpineCallocR1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineCallocR2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SpineCallocR3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bk.SpineCallocR8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bk.SpineCallocR9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bl.SpineCallocR10.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree.segsA.

Definition a0_e (eb : sv) : sv := SAlu ALU_AND eb (SLit 18446744073709547520).

Lemma a0_val : ltac2:(tb__ "0|1|
SfS8S22S0S22S34Q40M0SdR3R2A2A2R1A3S0S22S38R2Z1000A2Z0A3S0S33G0A1SdR5S4dR4A1A2SdR5R4A2A3F_;F_;FB;Feb;Fr;").
Proof.
  intros r eb B EB HM. unfold a0_e. cbn [eval]. apply bv_eq. rewrite and_val. replace (bv_unsigned (Z_to_bv 64 18446744073709547520)) with 18446744073709547520 by reflexivity.
  rewrite EB. apply land_m4096_id; [|exact HM]. rewrite <- EB. apply urange.
Qed.

Section ADDR.
Variables (A : AA) (rb r : valuation).
Hypothesis CF : cfacts A rb.
Hypothesis RG : ltac2:(tb__ "0|0|
S50VA;Vrb;Vr;A3").
Hypothesis GH : ltac2:(tb__ "0|0|
S42VA;Vrb;Vr;A3").

Lemma beg1_val : ltac2:(tb__ "0|0|
S0S22S34Q40SdVr;S2cA2A2S45VA;Vrb;A2A3").
Proof.
  unfold cfacts in CF. cbn zeta in CF. destruct CF as ((_ & C1 & _) & _ & (_ & AU0 & MU1 & _) & _ & _ & (G12 & G13 & G14 & TG) & _).
  destruct RG as (_ & _ & _ & _ & E155 & _ & _ & E158). destruct GH as (_ & _ & _ & _ & Q224 & _).
  unfold beg1, rb_e, vMU, vSB, V_CLS, U0, region_beg, kRegionSize. cbn [eval]. rewrite !add_val, sll_val, E155, E158, Q224, !u64_lit by lia.
  change (32 mod 64) with 32. rewrite Z.shiftl_mul_pow2 by lia. rewrite (Z.mod_small (_ * 2 ^ 32)) by lia. rewrite (Z.mod_small (_ + _ * 2 ^ 32)) by lia.
  rewrite Z.mod_small by lia. lia.
Qed.
Lemma beg2_val : ltac2:(tb__ "0|0|
S0S22S34Q40SdVr;S2dA2A2S44VA;Vrb;A2A3").
Proof.
  unfold cfacts in CF. cbn zeta in CF. destruct CF as ((_ & C1 & _) & _ & _ & (_ & MF0) & _ & (G12 & G13 & G14 & TG) & _).
  pose proof (Zle_0_nat (length (cs_free_array (cst_of A (bv_unsigned (rw rb 12%positive)))))) as NF0.
  destruct RG as (_ & _ & _ & _ & E155 & _ & _ & E158). destruct GH as (_ & _ & Q222 & _).
  unfold beg2, fa_e2, rb_e, vMFA, vSB, V_CLS, F0, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize. cbn [eval].
  rewrite !add_val, sll_val, E155, E158, Q222, !u64_lit by lia.
  change (32 mod 64) with 32. rewrite Z.shiftl_mul_pow2 by lia. rewrite (Z.mod_small (_ * 2 ^ 32)) by lia. rewrite (Z.mod_small (_ + _ * 2 ^ 32)) by lia.
  rewrite (Z.mod_small (_ + _ * 2 ^ 32 + 3758096384)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
End ADDR.

Section PIECE.
Variables (A : AA) (Kc : KcA) (rb : valuation) (tp0 : list word) (md0 : Model).
Variable TR : assn -> assn -> Prop.
Hypothesis KIT : TRok Kc TR.
Hypothesis HKc : Kc_ok Kc.
Variables (W : list ulink) (st : ustop) (rho : valuation).
Hypothesis HW : stopJ_w W st.
Hypothesis HE : ltac2:(tb__ "0|0|
S46VA;Vrb;Vtp0;Vmd0;VW;Vst;Vrho;A7").
Notation JRp := (JR A Kc rb tp0 md0).

Variable p : piece.
Variable eb : sv.
Variable ph : phase.
Hypothesis PH0 : ltac2:(tb__ "0|0|
S0S21S4aVp;Vph;A2U0A3").
Hypothesis PORD : pord p ph.
Hypothesis PQ : ph_quiet ph.
Let B : Z := ltac2:(tb__ "0|0|
S49VA;Vrb;Vp;A3").
Hypothesis HBv : ltac2:(tb__ "0|0|
SfS47Vrb;R1A2S42VA;Vrb;R2A3S0S22S34Q40SdR3Veb;A2A2VB;A3F_;F_;Fr;").
Hypothesis HBn : ltac2:(tb__ "0|1|
S1S37S35S5dS5cVA;A1A1M0Z100000000A2VB;A2S1S37S35VB;Z40000A2S35G0Z2000000000A2A2S0S22S38VB;Z10000A2Z0A3A2A2").
Hypothesis HROOM_c : ltac2:(tb__ "0|0|
S19S33Q40A1A1S39S43VA;Vrb;Vtp0;Vmd0;Vph;R2R1A7S36S40R2R3A2Z40000A2F_;Fmd;Ftp;").
Hypothesis HROOM_r : ltac2:(tb__ "0|0|
S19S33Q40A1A1S39S43VA;Vrb;Vtp0;Vmd0;S48Vp;U1Vph;A3R2R1A7S36S40R2R3A2Z8000A2F_;Fmd;Ftp;").

Variable F : nat.
Variables (C0 : axst) (LX LM : leafA).
Let CX : axst := ltac2:(tb__ "0|0|
S2eS4VLX;A1Veb;A2").
Let G1 : axst := commit_post CX eb 262144.
Let EM : axst := la_state LM.
Let CMR : axst := cMr EM.
Let CMC : axst := cMc EM eb.
Let DM : axst := dMSf CMC.
Let RM : axst := rotM DM.

Hypothesis R_x : ltac2:(tb__ "0|1|
S0S1dS19S3A1M0A1S5S25VF;S16S22Z7050cS1aS22A1A3VC0;S18A5S1cG0S16S3VLX;S1aS3A1A3A2A3").
Hypothesis LN_0 : ltac2:(tb__ "0|0|
S0S17S13S2VC0;A1A1S20A3").
Hypothesis NX_0 : ltac2:(tb__ "0|0|
S0S17S26S27SaS2VC0;A1A1A2S18A3").
Hypothesis W_x : ltac2:(tb__ "0|0|
S0S17S11S2VCX;A1A1S18A3").
Hypothesis D_x : ltac2:(tb__ "0|4|
S0S1dS1bS19S1bS8S8A2M0A1M1S19S9A1M2A2M3A1S3eS2S4VLX;A1A1S2VCX;A1A2S1cG3S1eG1G2S16G0S1eS8S8S4dVeb;A1Veb;A4S1aG0A1A3S1aS9A1A4A2A3").

Hypothesis SK_x : ltac2:(tb__ "0|1|
S0S19S1bS1bS8S8A2S8A2M0A1S23S7G0S32S10S2VCX;A1A1A4S23S7G0S32S1fS7S4fVW;A1S16S7S4bS16S7S4cS16S7S2aS16S7S2bS1aS7A1A3A3A3A3A3A4A3").
Hypothesis XF_x : ltac2:(tb__ "0|0|
S54S9S4eVW;Vst;A2SeS2VCX;A1A1A3").
Hypothesis XX_x : ax_X CX = [].
Hypothesis NX_x : ltac2:(tb__ "0|0|
S0S17S26S27SaS2VCX;A1A1A2S18A3").
Hypothesis IC_x : ltac2:(tb__ "0|0|
S0S1dS3aA1S59S25S14S2VCX;A1A1A2S1cS3aS3bA2A3").
Hypothesis R17_x : ltac2:(tb__ "0|0|
S0S8ScS2VCX;A1Z11A2SbZdeA1A3").
Hypothesis R10_x : ltac2:(tb__ "0|0|
S0S8ScS2VCX;A1ZaA2Veb;A3").
Hypothesis BEL_x : ltac2:(tb__ "0|0|
S0S17S15SaS2VCX;A1A1Veb;A2S18A3").
Hypothesis R11_x : ltac2:(tb__ "0|0|
S0S8ScS2VCX;A1ZbA2SbZ40000A1A3").
Hypothesis R12_x : ltac2:(tb__ "0|0|
S0S8ScS2VCX;A1ZcA2SbZ3A1A3").
Hypothesis R13_x : ltac2:(tb__ "0|0|
S0S8ScS2VCX;A1ZdA2SbZ32A1A3").
Hypothesis R14_x : ltac2:(tb__ "0|0|
S0S8ScS2VCX;A1ZeA2SbZffffffffffffffffA1A3").
Hypothesis R15_x : ltac2:(tb__ "0|0|
S0S8ScS2VCX;A1ZfA2SbZ0A1A3").

Hypothesis R_m : ltac2:(tb__ "0|1|
S0S1dS19S3A1M0A1S5S25VF;S16S22Zde378S1aS22A1A3VG1;S18A5S1cG0S16S3VLM;S1aS3A1A3A2A3").
Hypothesis LN_g : ltac2:(tb__ "0|0|
S0S17S13S2VG1;A1A1S20A3").
Hypothesis NX_g : ltac2:(tb__ "0|0|
S0S17S26S27SaS2VG1;A1A1A2S18A3").
Hypothesis SK_m : ltac2:(tb__ "0|1|
S0S19S1bS1bS8S8A2S8A2M0A1S23S7G0S32S10S2VEM;A1A1A4S23S7G0S32S1fS7S4fVW;A1S16S7S4bS16S7S4cS16S7S2aS16S7S2bS16S7S51Veb;A1S1aS7A1A3A3A3A3A3A3A4A3").
Hypothesis XF_m : ltac2:(tb__ "0|0|
S54S9S4eVW;Vst;A2SeS2VEM;A1A1A3").
Hypothesis XX_m : ax_X EM = [].
Hypothesis W_mr : ltac2:(tb__ "0|0|
S0S17S11S2VCMR;A1A1S18A3").
Hypothesis D_mr : ltac2:(tb__ "0|4|
S0S1dS1bS19S1bS8S8A2M0A1M1S19S9A1M2A2M3A1S3eS2VEM;A1S2VCMR;A1A2S1cG3S1eG1G2S16G0S1eS8S8S5fVeb;A1SbZ8000A1A4S1aG0A1A3S1aS9A1A4A2A3").
Hypothesis W_mc : ltac2:(tb__ "0|0|
S0S17S11S2VCMC;A1A1S18A3").
Hypothesis E_ms : ltac2:(tb__ "0|1|
S0S1dS19S7A1M0A1S5bVCMC;S3cS29VCMC;A1A3S1cG0S28VCMC;A1A2A3").
Hypothesis CHK_ms : ltac2:(tb__ "0|0|
S0S17S5aVCMC;S3cS29VCMC;A1S28VCMC;A1S23S3S6S4S3dA4A5S18A3").
Hypothesis NF_ms : ltac2:(tb__ "0|0|
S0S17S26S57SaS2VCMC;A1A1A2S18A3").
Hypothesis NX_ms : ltac2:(tb__ "0|0|
S0S17S26S27SaS2VCMC;A1A1A2S18A3").
Hypothesis FBC_ms : ltac2:(tb__ "0|1|
S0S17S53S9S12SaS2VCMC;A1M0A1A1SeG0A1A3S18A3").
Hypothesis FBT_ms : ltac2:(tb__ "0|0|
S0S17S53S9S12SaS2S5eVCMC;S29VCMC;A1S28VCMC;A1A3A1A1A1SeS2VCMC;A1A1A3S18A3").
Hypothesis ND_r : ltac2:(tb__ "0|0|
S0S17S58S2fVDM;A1A1S18A3").
Hypothesis NO_r : (1 <= nobj DM)%nat.
Hypothesis OB_r : ltac2:(tb__ "0|1|
S0S19S7A1S10S2VRM;A1A1M0S1fS7S24S7S55S30VDM;A1U2A2G0A3S16S7S51Veb;A1S16S7S52Veb;A1S1aS7A1A3A3A3A3").

Theorem piece_full : ltac2:(tb__ "0|1|
SfS19S33Q40A1A1M0S56SfG0VTR;S3fS25S41VA;VKc;Vrb;Vtp0;Vmd0;S48Vp;U3Vph;A3A6S31VDM;A1R2R1A5R3A2Ftp';Fr';VTR;S3fS25S41VA;VKc;Vrb;Vtp0;Vmd0;Vph;A6VC0;R4R3A5R2A2F_;FQ;Ftp;Fr;").
Proof.
  intros r tp Q HC.
  apply (jr_run A Kc rb tp0 md0 TR KIT HKc F [0x7050c] C0 [LX] ph r tp Q R_x LN_0 NX_0).
  intros L r1 [<-|[]] _.
  apply (jr_restate A Kc rb tp0 md0 TR KIT (la_state LX) (ax_S CX) _ _ ph r1 tp Q W_x D_x ltac:(apply Pos.eqb_refl)).
  { intros tr md (HFz & HGh & _) _. split; [|constructor]. unfold diffs_ok. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    destruct HBn as (_ & _ & HB3). apply (a0_val r1 eb B (HBv r1 HFz HGh)).
    destruct (proj1 (Z.mod_divide B 65536 ltac:(clear; lia)) HB3) as [q Hq]. rewrite Hq. replace (q * 65536) with (q * 16 * 4096) by (clear; lia). apply Z_mod_mult. }
  change (ax_setS (la_state LX) (ax_S CX)) with CX.
  assert (HBn' : ag_spacebeg (aa_geom A) + 4294967296 <= B /\ B + 262144 <= ag_spacebeg (aa_geom A) + 137438953472 /\ B mod 4096 = 0).
  { destruct HBn as (H1 & H2 & HB3). split; [exact H1|]. split; [exact H2|].
    destruct (proj1 (Z.mod_divide B 65536 ltac:(clear; lia)) HB3) as [q Hq]. rewrite Hq. replace (q * 65536) with (q * 16 * 4096) by (clear; lia). apply Z_mod_mult. }
  apply (piece_commit A Kc rb tp0 md0 TR KIT HKc W st rho HW HE p eb ph PH0 PORD PQ HBv HBn' HROOM_c CX SK_x XF_x XX_x NX_x IC_x R17_x R10_x BEL_x R11_x R12_x R13_x R14_x R15_x r1 tp Q).
  fold G1.
  apply (piece_map A Kc rb tp0 md0 TR KIT HKc W st rho HW HE p eb (ph_set p 1 ph) (ph_get_set p 1 ph) (ph_quiet_set p 1 ph PQ) HBv HBn HROOM_r
           F G1 LM R_m LN_g NX_g SK_m XF_m XX_m W_mr D_mr W_mc E_ms CHK_ms NF_ms NX_ms FBC_ms FBT_ms ND_r NO_r OB_r r1 tp Q).
  intros r' tp'. rewrite ph_set_set. exact (HC r' tp').
Qed.
End PIECE.
End SpineCallocR11.

(* [comment removed for export] *)
Module SpineCallocR4.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "valuation"; "sprop"; "ss_next"; "ss_objs"; "swf"; "eval"; "ss_facts"; "SLit"; "sprop_below"; "ss_lenient"; "DUnknown"; "cell"; "enc_bytes"; "mkObj"; "smatch"; "soff"; "sstate"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "leafA"; "la_state"; "ax_X"; "axst"; "sym_runA"; "@Corelib.Init.Datatypes"; "bool"; "list"; "true"; "cons"; "nil"; "Some"; "prod"; "app"; "option"; "false"; "pair"; "length"; "andb"; "nat"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CRefillJ"; "JR"; "ph_fill"; "ph_pop"; "ghosts"; "mkPh"; "ph_cnt"; "ph_f"; "ph_ri"; "ph_u"; "entryR"; "frozen"; "gh_new"; "gh_nf"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@Corelib.Lists.ListDef"; "map"; "firstn"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSR"; "cE3b"; "O_pcm"; "F_x"; "GR"; "O_pccK"; "cE3a"; "ri_has"; "cE1"; "cE3"; "choffK"; "k_e"; "nobj"; "vK"; "vRI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.SpineCallocR4"; "ph_setcnt"; "ph_setri"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3"; "skel"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "mul"; "of_nat"; "sub"; "leb"; "ltb"; "pow"; "to_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel"; "refill_cs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.SpineCallocR4.EXIT"; "O_rif"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "cst_of"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP"; "O_pcc0"; "O_st"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "cs_cache"; "class_state"; "cs_allocated_user"; "cs_free_array"; "cs_mapped_free_array"; "cs_mapped_user"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineCallocR2"; "BASEF"; "BASEO"; "@Stdlib.Lists.List"; "forallb"; "incl"; "nth_error"; "In"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "eqb"; "@Corelib.Init.Nat"; "sub"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "Build_machine_state"; "machine_state"; "ms_fcsr"; "ms_fregs"; "ms_pc_val"; "ms_regs"; "ms_resv"; "ms_rom"; "ms_svc_pending"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SMGlue InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require al.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineCallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CDepotCall PrimCredit PrimCreditLaws RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillTR CRefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineCallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CDepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CRefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SpineCallocR1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineCallocR2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SpineCallocR3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree.segsA.

Definition cnt_mem (pce kk : Z) : word -> option byte := ltac2:(tb__ "0|5|
S39Q40M0A1S1cS24S39Q8M1A1M2A1L_;S28S57Vpce;S3bG0R1A2M3A2S58G3S52Vpce;Z4A2A2A2S21G2S3fG2S5aS56G3Vpce;A2A1S11U4S3aG0Vkk;A2A2S3aG1Z0A2M4A4A2S21G2G4A2X1cx2La;").
Definition msOfR (f : word -> option byte) (ms : machine_state) : machine_state := ltac2:(tb__ "0|0|
S73S78Vms;A1S76Vms;A1S77Vms;A1S7bVms;A1S79Vms;A1S75Vms;A1Vf;S7aVms;A1A8").

Definition ph_setcnt (p : phase) : phase := ltac2:(tb__ "0|0|
S30S34Vp;A1S32Vp;A1S2dVp;A1S2eVp;A1S1eS33Vp;A1A6").
Definition ph_setri (p : phase) : phase := ltac2:(tb__ "0|0|
S30S34Vp;A1S32Vp;A1S2dVp;A1S2eVp;A1S31Vp;A1S1eA6").

Section EXIT.
Variables (A : AA) (Kc : KcA) (rb : valuation) (tp0 : list word) (md0 : Model).
Variable TR : assn -> assn -> Prop.
Hypothesis KIT : TRok Kc TR.
Hypothesis HKc : Kc_ok Kc.
Variables (W : list ulink) (st : ustop) (rho : valuation).
Hypothesis HW : stopJ_w W st.
Hypothesis HE : ltac2:(tb__ "0|0|
S35VA;Vrb;Vtp0;Vmd0;VW;Vst;Vrho;A7").
Notation JRp := (JR A Kc rb tp0 md0).
Let nv : Z := bv_unsigned (rw rb 12%positive).
Let c : Z := cls_of nv.
Let k : Z := kchunks c.
Variable phX : phase.
Hypothesis PHX : ltac2:(tb__ "0|0|
S1S0S2aS2eVphX;A1Vk;A3S1S0S1cS31VphX;A1S25A3S0S1cS33VphX;A1S25A3A2A2").
Hypothesis HFILLX : ltac2:(tb__ "0|4|
S53Z0M0S2dVphX;A1M1A2S1S51G0S38VA;Vrb;A2M2A2S1S51S54Z4S52G2S37VA;Vrb;A2M3A2A2Z20000000A2S51G1G3A2A2A2F_;").

Lemma cnt_rebase : ltac2:(tb__ "0|1|
S1aS29S5S1dS39Q40A1A1S60S0S1dS22S4S4A2M0A1S19R5A1S20G0A1A3S0S24S3A1S6eS3S8S16R6A1A1R5A3S21S3S44A2A3S3cS2bS2cVA;VKc;Vrb;Vtp0;Vmd0;VphX;A6R7R5R4R3A6S2S5S5S3cS2bS2cVA;VKc;Vrb;Vtp0;Vmd0;S4eVphX;A1A6R9R1R6R5A6Lr';A2F_;F_;F_;Fw;Ftp;Fr;Fic;FX1;").
Proof.
  intros X1 ic r tp w HXX HIC Hsp. destruct w as [tr [ms md]].
  pose proof (proj2 Hsp) as HJ. cbn [w_tr w_cfg cfg_model fst snd] in HJ. destruct HJ as (HFz & HGh & HK' & HM & HR & HRM).
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF0. pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG.
  destruct (arm_extra_ranges A rb r CF0 RG HGh) as (EB & _).
  unfold cfacts in CF0. cbn zeta in CF0. fold nv c in CF0.
  destruct CF0 as ((_ & C1 & _) & (K1 & _ & _) & _ & _ & _ & (G12 & G13 & G14 & _) & (T1 & T2 & _ & PS1) & _). fold k in K1. pose proof (topG_range (aa_geom A)) as TG.
  assert (PCr : PCE A rb = ag_thread (aa_geom A) + 208 + 80 * c) by (unfold PCE; fold nv c; lia).
  assert (RNc : obj_range r O_pccK = (PCE A rb, PCE A rb + 4)).
  { unfold O_pccK. rewrite obj_range_mk by lia. rewrite EB. f_equal; lia. }
  set (msf := msOfR (cnt_mem (PCE A rb) k) ms).
  exists (rho_absorb r [O_pccK] msf).
  apply (SPA_absorb_any segs (JRp phX) (JRp (ph_setcnt phX)) r X1 [O_pccK] msf tp (tr, mkCfg ms md) HXX); [| exact Hsp |].
  { intros o a [<-|[]] Ha. exists O_pccK. split; [eapply nth_error_In; exact HIC | exact Ha]. }
  cbn [w_tr w_cfg cfg_model fst snd].
  set (r' := rho_absorb r [O_pccK] msf).
  assert (INR : forall z, 0 <= z < 2 ^ 64 -> (in_ranges r [O_pccK] (Z_to_bv 64 z) <-> PCE A rb <= z < PCE A rb + 4)).
  { intros z Hz. split.
    - intros (o & [<-|[]] & Hr). rewrite RNc in Hr. cbn [fst snd] in Hr. rewrite u64_lit in Hr by lia. exact Hr.
    - intros Hr. exists O_pccK. split; [left; reflexivity|]. rewrite RNc. cbn [fst snd]. rewrite u64_lit by lia. exact Hr. }
  assert (VOUT : forall z, ~ (PCE A rb <= z < PCE A rb + 4) -> view segs (rm r') z = view segs (rm r) z).
  { intros z Hz. unfold view. destruct ((0 <=? z) && (z <? 2 ^ 64))%bool eqn:E; [|reflexivity].
    apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
    unfold rd_of, r'. rewrite rm_absorb_out; [reflexivity|]. intros Hin. apply Hz. apply (INR z ltac:(lia)). exact Hin. }
  assert (VIN : forall j, (j < 4)%nat -> view segs (rm r') (PCE A rb + Z.of_nat j) = Some (nth j (enc_bytes 4 (Z_to_bv 64 k)) (Z_to_bv 8 0))).
  { intros j Hj. rewrite view_in by lia. unfold rd_of, r'. rewrite rm_absorb_in by (apply (INR (PCE A rb + Z.of_nat j) ltac:(lia)); lia).
    unfold msf, msOfR, cnt_mem. cbn [ms_mem]. rewrite u64_lit by lia.
    replace ((PCE A rb <=? PCE A rb + Z.of_nat j) && (PCE A rb + Z.of_nat j <? PCE A rb + 4))%bool with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    replace (Z.to_nat (PCE A rb + Z.of_nat j - PCE A rb)) with j by lia. reflexivity. }
  unfold JR. split; [exact HFz|]. split; [exact HGh|]. split; [exact HK'|]. split; [exact HM|].
  split; [|apply (rmlink_absorb _ r [O_pccK] msf HRM); intros o [<-|[]]; rewrite RNc; cbn [fst snd];
           pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CFx; unfold cfacts in CFx; cbn zeta in CFx; fold nv c in CFx;
           destruct CFx as (_ & _ & _ & _ & _ & _ & (_ & _ & TIx & _) & _); unfold IMG_LO, IMG_HI; rewrite PCr; lia].
  unfold rlink in HR |- *. destruct HR as (L1 & L2 & L3 & L4 & L5 & L6). destruct PHX as (PX1 & PX2 & PX3).
  assert (ZI : forall z, zoneR A rb (ph_setcnt phX) z <-> (zoneR A rb phX z \/ PCE A rb <= z < PCE A rb + 4)).
  { intros z. unfold zoneR, ph_setcnt. cbn [ph_u ph_f ph_fill ph_pop ph_cnt ph_ri]. rewrite PX2. fold nv c. split.
    - intros [H|[H|[H|[H|[H|[H|[H|H]]]]]]].
      + left; left; exact H.
      + left; right; left; exact H.
      + left; right; right; left; exact H.
      + left; right; right; right; left; exact H.
      + left; right; right; right; right; left; exact H.
      + left; right; right; right; right; right; left; exact H.
      + right. exact (proj2 H).
      + left; right; right; right; right; right; right; right; exact H.
    - intros [[H|[H|[H|[H|[H|[H|[H|H]]]]]]]|H].
      + left; exact H.
      + right; left; exact H.
      + right; right; left; exact H.
      + right; right; right; left; exact H.
      + right; right; right; right; left; exact H.
      + right; right; right; right; right; left; exact H.
      + destruct H as [H _]. discriminate H.
      + right; right; right; right; right; right; right; exact H.
      + right; right; right; right; right; right; left. split; [reflexivity | exact H]. }
  split; [|split; [|split; [|split; [|split]]]].
  - intros z Hz. rewrite VOUT by (intros X; apply Hz; apply ZI; right; exact X). apply L1. intros X. apply Hz. apply ZI. left. exact X.
  - intros z Hz. apply ZI in Hz. destruct (Z_le_dec (PCE A rb) z) as [H1|H1]; [destruct (Z_lt_dec z (PCE A rb + 4)) as [H2|H2]|].
    + replace z with (PCE A rb + Z.of_nat (Z.to_nat (z - PCE A rb))) by lia. rewrite VIN by lia. discriminate.
    + rewrite VOUT by lia. apply L2. destruct Hz as [Hz|Hz]; [exact Hz | exfalso; lia].
    + rewrite VOUT by lia. apply L2. destruct Hz as [Hz|Hz]; [exact Hz | exfalso; lia].
  - intros j Hj. cbn [ph_fill ph_setcnt] in Hj |- *. eapply cell_ok_agree_range; [|exact (L3 j Hj)]. cbn [c_addr c_w]. intros z Hz. apply VOUT.
    destruct (HFILLX ltac:(lia)) as (F1 & F2 & F3). rewrite PCr. change (Z.of_nat 4) with 4 in Hz.
    unfold FAb, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize in Hz. fold nv c in Hz.
    clear -Hz C1 PS1 T1 T2 G13 G14 TG Hj F1 F2 F3. lia.
  - intros i' Hi'. cbn [ph_pop ph_setcnt] in Hi'. eapply cell_ok_agree_range; [|exact (L4 i' Hi')]. cbn [c_addr c_w]. intros z Hz. apply VOUT. lia.
  - intros _. intros j Hj. cbn [c_addr c_w RtCells.c_val] in Hj |- *. fold nv c k. apply VIN. exact Hj.
  - intros X. cbn [ph_ri ph_setcnt] in X. rewrite PX3 in X. discriminate X.
Qed.

Hypothesis Hini : aa_cache_inited A = true.
Variables e16 e24 e32 e48 : sv.
Hypothesis HRIv : ltac2:(tb__ "0|2|
S5S36Vrb;R1A2S2fVA;Vrb;R2A3S5bVc;S5dVA;Vnv;A2A2S65S1S0S39Q40M0A1M1SaR4Ve16;A2S3aG0S55S27S2aS67R1A1A2A1A2A3S1S0G1SaR4Ve24;A2S3aG0S68R1A1A2A3S1S0G1SaR4Ve32;A2S3aG0S66R1A1A2A3S0G1SaR4Ve48;A2S3aG0S69R1A1A2A3A2A2A2TcsR;F_;F_;Fr;").
Definition O_rif (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S12S4dScZ0A1ScZ80A1Vcells;SfA5").

Lemma ri_release : ltac2:(tb__ "0|4|
S15S1dS3A1M0S1dS10A1S5S1dS39Q40A1A1S1dS5fA1M1S74S5eS5eS0G0S8R9A1S23S3R8S1fS3S41S1fS3S5cR7A1S20S3A1M2A3A3A3A3S0S1cS46R8Ve16;Ve24;Ve32;Ve48;A5S1eA3S13S2bR8RbS26G1S7cR6S7dR5R4A2A4A4S2cVA;VKc;Vrb;Vtp0;Vmd0;S4eVphX;A1M3R9R8R7R4AaS2cVA;VKc;Vrb;Vtp0;Vmd0;S4fG3A1S7fRaS1fS3S41S1fS3S5cRbA1G2A3A3R7A3R9R8R5AaF_;F_;F_;F_;FmdJ;Fmd;Fms;Ftr;Ftp;Fr;Fcells;FK;FS;").
Proof.
  intros S K cells r tp tr ms md mdJ HO HRI Hsm (HFz & HGh & HK' & HM & HR & HRM).
  set (R := [O_pcm; O_rif cells]). set (r3 := rho_absorb r R ms).
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF0. pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG.
  destruct (arm_extra_ranges A rb r CF0 RG HGh) as (EB & _ & _ & RNm & RNr). cbn zeta in RNr. fold nv c in RNr.
  destruct (entry_pc_cells _ _ _ _ _ _ _ HE Hini) as (D2 & _ & _). cbn zeta in D2. fold nv c in D2.
  unfold cfacts in CF0. cbn zeta in CF0. fold nv c in CF0.
  destruct CF0 as ((_ & C1 & _) & (K1 & _ & _) & _ & _ & _ & (G12 & G13 & G14 & _) & (T1 & T2 & _ & PS1) & _). fold k in K1. pose proof (topG_range (aa_geom A)) as TG.
  assert (PCr : PCE A rb = ag_thread (aa_geom A) + 208 + 80 * c) by (unfold PCE; fold nv c; lia).
  set (ri := region_info (ag_spacebeg (aa_geom A)) c) in *.
  assert (RIr : ag_spacebeg (aa_geom A) + 137438953472 <= ri /\ ri + 128 <= ag_spacebeg (aa_geom A) + 137438953472 + 4096).
  { unfold ri, region_info, kRegionInfoStride. rewrite kSpaceSize_val. lia. }
  assert (RNf : obj_range r (O_rif cells) = (ri, ri + 128)).
  { rewrite <- RNr. apply obj_range_skel. reflexivity. }
  pose proof HGh as (Q220 & _ & _ & _ & _ & Q225 & _). fold nv c in Q220. fold nv c ri in Q225.
  set (m := view segs (rm r)) in *. set (m3 := view segs (rm r3)).
  unfold rlink in HR. fold m in HR. destruct HR as (L1 & L2 & L3 & L4 & L5 & L6). destruct PHX as (PX1 & PX2 & PX3).

  assert (NZm : forall z, PCE A rb + 4 <= z < PCE A rb + 8 -> ~ zoneR A rb (ph_setcnt phX) z).
  { intros z Hz HZ.
    destruct (zone_thread_gen A rb (ph_setcnt phX) z (entry_cfacts _ _ _ _ _ _ _ HE) HFILLX ltac:(rewrite PCr in Hz; lia) HZ) as [X|[_ X]]; cbn [ph_pop ph_setcnt] in X; lia. }
  assert (M3m : forall j, (j < 4)%nat -> m3 (PCE A rb + 4 + Z.of_nat j) = m (PCE A rb + 4 + Z.of_nat j)).
  { intros j Hj. rewrite (L1 (PCE A rb + 4 + Z.of_nat j) (NZm (PCE A rb + 4 + Z.of_nat j) ltac:(lia))). specialize (D2 j Hj). cbn [c_addr c_w RtCells.c_val] in D2. rewrite D2.
    destruct (absorb_obj r S tr ms md K R O_pcm Hsm HO (or_introl eq_refl)) as (_ & AS & _).
    destruct (AS (mkCell (SLit 4) 4 vMC) (or_introl eq_refl)) as (_ & _ & ASb). specialize (ASb j Hj).
    cbn [ob_base O_pcm c_off SymState.c_val c_width] in ASb. rewrite EB, soff_lit_small in ASb by lia. unfold vMC in ASb. cbn [eval] in ASb. rewrite Q220 in ASb.
    unfold m3. rewrite view_in by lia. exact ASb. }
  assert (AGR : forall z, ~ (ri <= z < ri + 128) -> m3 z = m z).
  { intros z Hz. destruct (Z_le_dec (PCE A rb + 4) z) as [H1|H1]; [destruct (Z_lt_dec z (PCE A rb + 8)) as [H2|H2]|].
    - replace z with (PCE A rb + 4 + Z.of_nat (Z.to_nat (z - (PCE A rb + 4)))) by lia. apply M3m. lia.
    - unfold m3, r3. apply view_absorb_out. intros o [<-|[<-|[]]]; [rewrite RNm | rewrite RNf]; cbn [fst snd]; lia.
    - unfold m3, r3. apply view_absorb_out. intros o [<-|[<-|[]]]; [rewrite RNm | rewrite RNf]; cbn [fst snd]; lia. }
  idtac "rr:1".
  destruct (absorb_obj r S tr ms md K R (O_rif cells) Hsm HO (or_intror (or_introl eq_refl))) as (_ & ASc & ASp & _).
  cbn [ob_base O_rif ob_cells ob_dflt] in ASc, ASp. unfold obj_lo_of, obj_hi_of in ASp. cbn [ob_lo ob_hi O_rif] in ASp. rewrite !soff_lit_small in ASp by lia.
  assert (ERI : bv_unsigned (eval r vRI) = ri) by (unfold vRI; cbn [eval]; rewrite Q225; apply u64_lit; lia).
  rewrite ERI in ASc, ASp.
  assert (RC : forall off (w : nat) e val, In (mkCell (SLit off) (Z.of_nat w) e) cells -> 0 <= off -> off + Z.of_nat w <= 128 -> eval r e = Z_to_bv 64 val ->
            cell_ok m3 (mkACell (ri + off) w val)).
  { intros off w e val Hin Ho1 Ho2 Ee j Hj. cbn [c_addr c_w RtCells.c_val] in Hj |- *.
    destruct (ASc _ Hin) as (_ & _ & ASb). cbn [c_off SymState.c_val c_width] in ASb. rewrite Nat2Z.id, soff_lit_small, Ee in ASb by lia.
    unfold m3. rewrite view_in by lia. exact (ASb j Hj). }
  assert (INC : forall cc, In cc [mkCell (SLit 0) 8 (SLit 0); mkCell (SLit 16) 8 e16; mkCell (SLit 24) 8 e24; mkCell (SLit 32) 8 e32; mkCell (SLit 40) 8 (SLit 0);
                               mkCell (SLit 48) 8 e48; mkCell (SLit 56) 8 (SLit 0); mkCell (SLit 68) 1 (SLit 0)] -> In cc cells).
  { intros cc Hcc. unfold ri_has in HRI. pose proof (proj1 (forallb_forall _ _) HRI cc Hcc) as X. apply existsb_exists in X as (c' & Hin & E).
    apply cell_eqb_sound in E. subst c'. exact Hin. }
  destruct (HRIv r HFz HGh) as (V16 & V24 & V32 & V48). cbn zeta in V16, V24, V32, V48.
  unfold JR. split; [exact HFz|]. split; [exact HGh|]. split; [exact HK'|]. split; [exact HM|].
  split; [|apply (rmlink_absorb _ r R ms HRM); intros o [<-|[<-|[]]]; [rewrite RNm | rewrite RNf]; cbn [fst snd];
           pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CFx; unfold cfacts in CFx; cbn zeta in CFx; fold nv c in CFx;
           destruct CFx as (_ & _ & _ & _ & _ & _ & (_ & _ & TIx & _) & _); unfold IMG_LO, IMG_HI; rewrite ?PCr; lia].
  fold r3 m3. unfold rlink.
  assert (ZI : forall z, zoneR A rb (ph_setri (ph_setcnt phX)) z <-> (zoneR A rb (ph_setcnt phX) z \/ ri <= z < ri + 128)).
  { intros z. unfold zoneR, ph_setri, ph_setcnt. cbn [ph_u ph_f ph_fill ph_pop ph_cnt ph_ri]. rewrite PX3. fold nv c ri. split.
    - intros [H|[H|[H|[H|[H|[H|[H|H]]]]]]].
      + left; left; exact H.
      + left; right; left; exact H.
      + left; right; right; left; exact H.
      + left; right; right; right; left; exact H.
      + left; right; right; right; right; left; exact H.
      + left; right; right; right; right; right; left; exact H.
      + left; right; right; right; right; right; right; left; exact H.
      + right. exact (proj2 H).
    - intros [[H|[H|[H|[H|[H|[H|[H|H]]]]]]]|H].
      + left; exact H.
      + right; left; exact H.
      + right; right; left; exact H.
      + right; right; right; left; exact H.
      + right; right; right; right; left; exact H.
      + right; right; right; right; right; left; exact H.
      + right; right; right; right; right; right; left; exact H.
      + destruct H as [H _]. discriminate H.
      + right; right; right; right; right; right; right. split; [reflexivity | exact H]. }
  split; [|split; [|split; [|split; [|split]]]].
  - intros z Hz. rewrite AGR by (intros X; apply Hz; apply ZI; right; exact X). apply L1. intros X. apply Hz. apply ZI. left. exact X.
  - intros z Hz. apply ZI in Hz. destruct (Z_le_dec ri z) as [H1|H1]; [destruct (Z_lt_dec z (ri + 128)) as [H2|H2]|].
    + destruct (ASp (or_introl eq_refl) (z - ri) ltac:(lia)) as [x Hx]. replace (ri + (z - ri)) with z in Hx by lia.
      unfold m3, r3. rewrite view_in by lia. rewrite Hx. discriminate.
    + rewrite AGR by lia. apply L2. destruct Hz as [Hz|Hz]; [exact Hz | exfalso; lia].
    + rewrite AGR by lia. apply L2. destruct Hz as [Hz|Hz]; [exact Hz | exfalso; lia].
  - intros j Hj. cbn [ph_fill ph_setri ph_setcnt] in Hj |- *. eapply cell_ok_agree_range; [|exact (L3 j Hj)]. cbn [c_addr c_w]. intros z Hz. apply AGR.
    destruct (HFILLX ltac:(lia)) as (F1 & F2 & F3). change (Z.of_nat 4) with 4 in Hz.
    unfold FAb, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize in Hz. fold nv c in Hz.
    clear -Hz C1 RIr Hj F1 F2 F3. lia.
  - intros i' Hi'. cbn [ph_pop ph_setri ph_setcnt] in Hi'. eapply cell_ok_agree_range; [|exact (L4 i' Hi')]. cbn [c_addr c_w]. intros z Hz. apply AGR.
    change (Z.of_nat 4) with 4 in Hz. rewrite PX1 in Hi'. rewrite PCr in Hz. clear -Hz Hi' K1 C1 RIr PS1 T1 T2 G13 G14 TG. lia.
  - intros X. eapply cell_ok_agree_range; [|exact (L5 eq_refl)]. cbn [c_addr c_w]. intros z Hz. apply AGR.
    change (Z.of_nat 4) with 4 in Hz. rewrite PCr in Hz. clear -Hz C1 RIr PS1 T1 T2 G13 G14 TG. lia.
  - intros _. cbn zeta. fold nv c ri. unfold RI_mutex, RI_num_freed, RI_mapped_free_array, RI_allocated_user, RI_allocated_meta, RI_mapped_user, RI_mapped_meta, RI_exhausted.
    split; [apply (RC 0 8%nat (SLit 0) 0); [apply INC; cbn; tauto | lia | cbn; lia | reflexivity]|].
    split; [apply (RC 16 8%nat e16); [apply INC; cbn; tauto | lia | cbn; lia | exact V16]|].
    split; [apply (RC 24 8%nat e24); [apply INC; cbn; tauto | lia | cbn; lia | exact V24]|].
    split; [apply (RC 32 8%nat e32); [apply INC; cbn; tauto | lia | cbn; lia | exact V32]|].
    split; [apply (RC 40 8%nat (SLit 0) 0); [apply INC; cbn; tauto | lia | cbn; lia | reflexivity]|].
    split; [apply (RC 48 8%nat e48); [apply INC; cbn; tauto | lia | cbn; lia | exact V48]|].
    split; [apply (RC 56 8%nat (SLit 0) 0); [apply INC; cbn; tauto | lia | cbn; lia | reflexivity]|].
    apply (RC 68 1%nat (SLit 0) 0); [apply INC; cbn; tauto | lia | cbn; lia | reflexivity].
Qed.

Hypothesis HLEN : ltac2:(tb__ "0|0|
S0S2aS55S27S2aS64S5bVc;S5dVA;Vnv;A2A2A1A2A1Vk;A3").
Hypothesis HIDC : ltac2:(tb__ "0|0|
S2aS6fS2aR1S64S5bVc;S5dVA;Vnv;A2A2A1A3S1S51Z0R2A2S53R2S59Z2Z1cA2A2A2F_;Fx;").
Notation phF := (ph_setri (ph_setcnt phX)).

Lemma choffK_val : ltac2:(tb__ "0|0|
S5S2fVA;Vrb;R1A3S0S2aS14R2S49A2S52Z10S54Z4S56Vk;Z1A2A2A2A3F_;Fr;").
Proof.
  intros r HGh. destruct HGh as (_ & _ & _ & _ & _ & _ & _ & Q227 & _). fold nv c k in Q227.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF0. unfold cfacts in CF0. cbn zeta in CF0. fold nv c in CF0. destruct CF0 as (_ & (K1 & _) & _). fold k in K1.
  set (kk := k) in *. clearbody kk.
  unfold choffK, vK. rewrite soff_snorm. unfold U. cbn [eval]. rewrite Q227. clear -K1. rewrite add_val, sll_val, add_val. rewrite (u64_lit kk), (u64_lit 16) by lia.
  replace (bv_unsigned (Z_to_bv 64 (-1))) with (2 ^ 64 - 1) by reflexivity.
  replace ((kk + (2 ^ 64 - 1)) mod 2 ^ 64) with (kk - 1) by (rewrite <- (Z.mod_add _ (-1)) by lia; rewrite Z.mod_small by lia; lia).
  change (2 mod 64) with 2. rewrite Z.shiftl_mul_pow2 by lia. rewrite (Z.mod_small (_ * 2 ^ 2)) by lia. rewrite Z.mod_small by lia.
  unfold snorm. rewrite Z.mod_small by lia. destruct (Z.ltb_spec ((kk - 1) * 2 ^ 2 + 16) (2 ^ 63)); lia.
Qed.

Lemma exit_carve : ltac2:(tb__ "0|4|
S1aS5S1dS39Q40A1A1S60S0S1dS22S22S4S4A2M0S4A2M1A1S3dS3G1S50S8S16R4A1A1A4S3dS3G1S50S23S3S6bVW;A1S1fS3S62S1fS3S63S20S3A1A3A3A3A4A3S0S1dG0A1S19R5A1S20G0A1A3S6dS6S6aVW;Vst;A2SbS16R6A1A1A3S0S1cS9S16S45R7A1A1A1S1eA3S0S1cS9S16S40R8A1A1A1S1eA3S0S1cS6cS6SdS7S16S40R9A1A1M2A1A1S23S6S42SbG2A1A3A3S1eA3S3cS2bS2cVA;VKc;Vrb;Vtp0;Vmd0;S4fS4eVphX;A1A1A6M3RaR9R8R7A6S3cS2bG3S48RbA1RaR9R8A6F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Fr;FX2;").
Proof.
  intros X2 r tp w SK2 XX2 XF2 W3a W3b FB3 H.
  pose proof H as [HsmA (HFz & HGh & _ & _ & HR & _)].
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF0. pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG.
  destruct (arm_extra_ranges A rb r CF0 RG HGh) as (EB & RNc & RNs & _ & _). cbn zeta in RNs.
  destruct (entry_pc_cells _ _ _ _ _ _ _ HE Hini) as (_ & D3 & PE0). cbn zeta in D3, PE0. fold nv c in D3.
  pose proof (proj1 HsmA) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm.
  destruct (arm_base_disj A rb tp0 md0 W st rho (ax_S X2) [O_pcc0; O_st] r _ HW HE HFz Hsm SK2 XF2) as (ob & ox & EO & SKx & BZ).
  destruct ox as [|oc [|os [|? ?]]]; cbn [map] in SKx; try (exfalso; clear -SKx; discriminate SKx).
  assert (SKc : skel oc = skel O_pcc0) by (clear -SKx; congruence). assert (SKs : skel os = skel O_st) by (clear -SKx; congruence).
  rewrite <- (obj_range_skel r oc O_pcc0 SKc) in RNc. rewrite <- (obj_range_skel r os O_st SKs) in RNs.
  pose proof CF0 as CF1. unfold cfacts in CF1. cbn zeta in CF1. fold nv c in CF1.
  destruct CF1 as ((_ & C1 & _) & (K1 & _ & _) & _ & _ & _ & (G12 & G13 & G14 & _) & (T1 & T2 & TI & PS1) & _). fold k in K1. pose proof (topG_range (aa_geom A)) as TG.
  assert (PCr : PCE A rb = ag_thread (aa_geom A) + 208 + 80 * c) by (unfold PCE; fold nv c; lia).
  destruct PHX as (PX1 & PX2 & PX3).
  set (m := view segs (rm r)) in *. unfold rlink in HR. fold m in HR. destruct HR as (L1 & L2 & L3 & L4 & L5 & L6).
  pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as (_ & E148 & _). fold nv c in E148.
  pose proof HGh as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Q229).

  assert (NZ : forall z, PCE A rb + 4 <= z < PCE A rb + 80 -> ~ (PCE A rb + 16 <= z < PCE A rb + 16 + 4 * k) -> ~ zoneR A rb phF z).
  { intros z Hz Hn HZ.
    destruct (zone_thread_gen A rb phF z CF0 HFILLX ltac:(rewrite PCr in Hz; lia) HZ) as [X|[_ X]]; cbn [ph_pop ph_setri ph_setcnt] in X; lia. }
  assert (PRE : forall z, PCE A rb + 4 <= z < PCE A rb + 80 -> exists b, m z = Some b).
  { intros z Hz. destruct (Z_le_dec (PCE A rb + 16) z) as [H1|H1]; [destruct (Z_lt_dec z (PCE A rb + 16 + 4 * k)) as [H2|H2]|].
    - assert (HZ : zoneR A rb phF z) by (unfold zoneR; cbn [ph_pop ph_setri ph_setcnt]; rewrite PX1; fold nv c k; do 5 right; left; lia).
      specialize (L2 z HZ). destruct (m z) as [b|] eqn:Em; [exists b; reflexivity | exfalso; apply L2; first [exact Em | reflexivity]].
    - rewrite (L1 z (NZ z Hz ltac:(lia))). apply PE0. lia.
    - rewrite (L1 z (NZ z Hz ltac:(lia))). apply PE0. lia. }
  assert (WR : forall z, PCE A rb + 4 <= z < PCE A rb + 80 -> wok_of segs (rm r) (Z_to_bv 64 z) = true /\ exists x, rd_of segs (rm r) (Z_to_bv 64 z) = Some x).
  { intros z Hz. destruct (PRE z Hz) as [b Hb]. unfold m in Hb. rewrite view_in in Hb by lia. eapply wok_rd_off_image2; [| |exact Hb]; lia. }
  idtac "xc:1".

  assert (Ha : SPA segs (JRp phF) (cE3a X2) r tp w).
  { unfold cE3a, addobjs, nxt.
    apply (SPA_carve_gen segs _ r X2 tp w pc_base 8 16 [mkCell (SLit 8) 8 (SVar V_SIZE)] (ss_next (ax_S X2)) H W3a (Pos.le_refl _)); rewrite ?EB; try lia.
    - unfold gcells_inside. repeat apply Forall_cons; try apply Forall_nil; cbn [c_off c_width SymState.c_val]; rewrite ?soff_lit_small by lia; lia.
    - rewrite EO. apply Forall_app. split; [apply BZ; left; rewrite PCr; lia|].
      repeat apply Forall_cons; try apply Forall_nil; rewrite ?RNc, ?RNs; unfold ranges_disjoint; cbn [fst snd]; rewrite ?PCr; lia.
    - intros off Hoff. apply WR. lia.
    - unfold gcells_in_view. repeat apply Forall_cons; try apply Forall_nil; cbn [c_off c_width SymState.c_val Z.to_nat Pos.to_nat]; rewrite ?soff_lit_small by lia.
      intros j Hj. cbn [eval]. unfold V_SIZE. rewrite E148. specialize (D3 j Hj). cbn [c_addr c_w RtCells.c_val] in D3.
      rewrite <- (L1 _ (NZ (PCE A rb + 8 + Z.of_nat j) ltac:(cbn in Hj; lia) ltac:(cbn in Hj; lia))) in D3. unfold m in D3. rewrite view_in in D3 by (cbn in Hj; lia). exact D3.
    - unfold xwords_clear. rewrite XX2. intros rr y j []. }
  idtac "xc:2".

  pose proof (choffK_val r HGh) as ECH.
  assert (OBa : ss_objs (ax_S (cE3a X2)) = ss_objs (ax_S X2) ++ [O_pcs]) by reflexivity.
  assert (Hb : SPA segs (JRp phF) (cE3b X2) r tp w).
  { unfold cE3b, addobjs, nxt.
    apply (SPA_carve_gsym segs _ r (cE3a X2) tp w pc_base choffK (SLit 80) [mkCell choffK 4 vCHX] (ss_next (ax_S X2)) Ha W3b (Pos.le_refl _)); rewrite ?EB, ?ECH, ?soff_lit_small by lia; try lia.
    - unfold gcells_inside. repeat apply Forall_cons; try apply Forall_nil; cbn [c_off c_width SymState.c_val]; rewrite ?ECH; lia.
    - rewrite OBa, EO. apply Forall_app. split; [apply Forall_app; split|].
      + apply BZ. left. rewrite PCr. lia.
      + repeat apply Forall_cons; try apply Forall_nil; rewrite ?RNc, ?RNs; unfold ranges_disjoint; cbn [fst snd]; rewrite ?PCr; lia.
      + repeat apply Forall_cons; try apply Forall_nil. unfold O_pcs. rewrite obj_range_mk by lia. rewrite EB. unfold ranges_disjoint; cbn [fst snd]. lia.
    - intros off Hoff. replace (PCE A rb + off) with (PCE A rb + off) by lia. apply WR. lia.
    - unfold gcells_in_view. repeat apply Forall_cons; try apply Forall_nil; cbn [c_off c_width SymState.c_val Z.to_nat Pos.to_nat]; rewrite ?ECH.
      intros j Hj. unfold vCHX. cbn [eval]. rewrite Q229.
      pose proof (L4 (k - 1) ltac:(cbn [ph_pop ph_setri ph_setcnt]; rewrite PX1; lia)) as Hc. specialize (Hc j Hj). cbn [c_addr c_w RtCells.c_val] in Hc.
      unfold m in Hc. rewrite view_in in Hc by (cbn in Hj; lia).
      replace (PCE A rb + (16 + 4 * (k - 1)) + Z.of_nat j) with (PCE A rb + 16 + 4 * (k - 1) + Z.of_nat j) by lia. rewrite Hc. do 3 f_equal.
      unfold gh_chx. fold nv c. replace (Z.to_nat (k - 1)) with (length (cs_cache (refill_cs c (cst_of A nv))) - 1)%nat by (clear -HLEN K1; lia). reflexivity.
    - unfold xwords_clear. cbn [ax_X cE3a addobjs ax_setS]. rewrite XX2. intros rr y j []. }
  idtac "xc:3".

  unfold cE3. apply (SPA_refacts segs _ r (cE3b X2) _ tp w Hb FB3).
  intros HF0. apply Forall_app. split; [|exact HF0].
  unfold F_x, vCHX. repeat apply Forall_cons; try apply Forall_nil. cbn [holds eval]. rewrite Q229.
  assert (Hg : 0 <= gh_chx A rb < 2 ^ 28).
  { apply HIDC. unfold gh_chx. fold nv c. apply nth_In. lia. }
  rewrite !u64_lit by lia. lia.
Qed.

Variable F : nat.
Variable XL : axst.
Variables L9 LZ : leafA.
Variable ic : nat.
Variable cells_f : list cell.
Let X1 : axst := ltac2:(tb__ "0|0|
S47S18VL9;A1Vic;A2").
Let X2 : axst := cE2 X1.
Let X3 : axst := cE3 X2.
Hypothesis R_9 : ltac2:(tb__ "0|1|
S0S24S1dS17A1M0A1S1bS2bVF;S1fS2aZ40cc8S20S2aA1A3VXL;S1eA5S21G0S1fS17VL9;S20S17A1A3A2A3").
Hypothesis LN_9 : ltac2:(tb__ "0|0|
S0S1cSeS16VXL;A1A1S25A3").
Hypothesis NX_9 : ltac2:(tb__ "0|0|
S0S1cS70S43S7S16VXL;A1A1A2S1eA3").
Hypothesis W_x1 : ltac2:(tb__ "0|0|
S0S1cS9S16VX1;A1A1S1eA3").
Hypothesis D_x1 : ltac2:(tb__ "0|4|
S0S24S22S1dS22S4S4A2M0A1M1S1dS6A1M2A2M3A1S7eS16S18VL9;A1A1S16VX1;A1A2S21G3S26G1G2S1fG0S26S4S4S4aS4cA4S20G0A1A3S20S6A1A4A2A3").
Hypothesis NX_x1 : ltac2:(tb__ "0|0|
S0S1cS71S7S16VX1;A1A1S7S16S18VL9;A1A1A1A2S1eA3").
Hypothesis XX_1 : ax_X X1 = [].
Hypothesis IC_1 : ltac2:(tb__ "0|0|
S0S24S3A1S6eS3S8S16VX1;A1A1Vic;A3S21S3S44A2A3").
Hypothesis OB_1 : ltac2:(tb__ "0|1|
S0S1dS3A1S8S16VX1;A1A1M0S23S3S3eS3S72S4bVX1;A1U2A2G0A3S1fS3S41S1fS3S5cVcells_f;A1S20S3A1A3A3A3A3").
Hypothesis RI_1 : ltac2:(tb__ "0|0|
S0S1cS46Vcells_f;Ve16;Ve24;Ve32;Ve48;A5S1eA3").
Hypothesis SK_2 : ltac2:(tb__ "0|1|
S0S1dS22S22S4S4A2S4A2M0A1S3dS3G0S50S8S16VX2;A1A1A4S3dS3G0S50S23S3S6bVW;A1S1fS3S62S1fS3S63S20S3A1A3A3A3A4A3").
Hypothesis XX_2 : ax_X X2 = [].
Hypothesis XF_2 : ltac2:(tb__ "0|0|
S6dS6S6aVW;Vst;A2SbS16VX2;A1A1A3").
Hypothesis W_3a : ltac2:(tb__ "0|0|
S0S1cS9S16S45VX2;A1A1A1S1eA3").
Hypothesis W_3b : ltac2:(tb__ "0|0|
S0S1cS9S16S40VX2;A1A1A1S1eA3").
Hypothesis FB_3 : ltac2:(tb__ "0|1|
S0S1cS6cS6SdS7S16S40VX2;A1A1M0A1A1S23S6S42SbG0A1A3A3S1eA3").
Hypothesis R_z : ltac2:(tb__ "0|1|
S0S24S1dS17A1M0A1S1bS2bVF;S1fS2aZ3c480S20S2aA1A3VX3;S1eA5S21G0S1fS17VLZ;S20S17A1A3A2A3").
Hypothesis LN_z : ltac2:(tb__ "0|0|
S0S1cSeS16VX3;A1A1S25A3").
Hypothesis NX_z : ltac2:(tb__ "0|0|
S0S1cS70S43S7S16VX3;A1A1A2S1eA3").

Lemma exit_steps : ltac2:(tb__ "0|0|
S5S1dS39Q40A1A1S61S5VTR;S3cS2bS2cVA;VKc;Vrb;Vtp0;Vmd0;S4fS4eVphX;A1A1A6S18VLZ;A1R1R3A5R2A2Fr';VTR;S3cS2bS2cVA;VKc;Vrb;Vtp0;Vmd0;VphX;A6VXL;R4R3A5R2A2F_;FQ;Ftp;Fr;").
Proof.
  intros r tp Q HZ.
  apply (jr_run A Kc rb tp0 md0 TR KIT HKc F [0x40cc8] XL [L9] phX r tp Q R_9 LN_9 NX_9).
  intros L r1 [<-|[]] _.
  apply (jr_restate A Kc rb tp0 md0 TR KIT (la_state L9) (ax_S X1) _ _ phX r1 tp Q W_x1 D_x1 NX_x1).
  { intros tr md (HFz & HGh & _) _. split; [|constructor].
    pose proof (r1_diffs A rb r1 (entry_cfacts _ _ _ _ _ _ _ HE) (entry_rigids _ _ _ _ _ _ _ _ HE HFz) HGh) as D.
    unfold diffs_ok in *. apply Forall_cons; [|apply Forall_nil]. exact (Forall_inv (Forall_inv_tail D)). }
  change (ax_setS (la_state L9) (ax_S X1)) with X1.
  apply (tr_cut Kc TR KIT valuation _ (fun r2 => SPA segs (JRp (ph_setcnt phX)) X1 r2 tp) Q (fun w Hw => cnt_rebase X1 ic r1 tp w XX_1 IC_1 Hw)).
  intros r2.
  apply (tr_cut Kc TR KIT valuation _ (fun r3 => SPA segs (JRp phF) X2 r3 tp) Q).
  { intros [tr [ms md]] Hw. exists (rho_absorb r2 [O_pcm; O_rif cells_f] (vms md tp ms)).
    apply (SPA_unobj_J (JRp (ph_setcnt phX)) (JRp phF) r2 X1 _ [O_pcm; O_rif cells_f] tp tr ms md OB_1 Hw).
    intros Hsm HJ. exact (ri_release (ax_S X1) _ cells_f r2 tp tr (vms md tp ms) (vmd md) md OB_1 RI_1 Hsm HJ). }
  intros r3.
  apply (tr_pre Kc TR KIT (SPA segs (JRp phF) X3 r3 tp)); [intros w Hw; exact (exit_carve X2 r3 tp w SK_2 XX_2 XF_2 W_3a W_3b FB_3 Hw)|].
  apply (jr_run A Kc rb tp0 md0 TR KIT HKc F [0x3c480] X3 [LZ] phF r3 tp Q R_z LN_z NX_z).
  intros L r4 [<-|[]] _. apply HZ.
Qed.
End EXIT.
End SpineCallocR4.

