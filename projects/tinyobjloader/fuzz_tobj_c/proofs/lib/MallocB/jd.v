(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require bitvector list.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jc.
From Stdlib Require NArith PArith.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.

(* [comment removed for export] *)
Module InvQ6.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rm"; "valuation"; "rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "view"; "@stdpp.bitvector.definitions"; "bv"; "@Corelib.Init.Datatypes"; "list"; "option"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ"; "AInvQ"; "K0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "topG"; "@Stdlib.ZArith.BinInt.Z"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector list.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import BackingAlgebra Virt SoundA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull SMGlue RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jc.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.LiveGeom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jb.InvQ2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jc.InvQ3.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem AInvQ_frame_top : ltac2:(tb__ "0|0|
SfS1S1S6S5Q40A1A1SbSdR5R4R2R1A4S9S12R1S11S10R7A1A1A2S8S7S5Q8A1A1S4S3S0R6A1R2A3S4S3S0R7A1R2A3A3F_;Fz;SdR7R5R4R3A4F_;F_;Fmd;Ftp;Frho';Frho;FA;").
Proof.
  intros A rho rho' tp md HX AV. unfold AInvQ in HX |- *. cbn zeta in HX |- *.
  set (G := aa_geom A) in *. set (m := view segsA (rm rho)) in *. set (m' := view segsA (rm rho')) in *.
  destruct HX as (HG & HR & HF & HRest & HM & HI3 & HB).
  destruct HRest as (R1 & R2 & R3 & R4 & (R5 & R5m) & R6 & R7 & R8 & R9).
  pose proof (geom_old _ HG) as (_ & F1 & F2 & _ & T1 & T2 & _ & C1 & C2 & D1 & D2 & _ & S1 & S2 & _). fold G in F1, F2, T1, T2, C1, C2, D1, D2, S1, S2.
  pose proof (topG_range G) as TG.
  assert (HPAB : dyn_ok (topG G) (ag_pab G) kPtrArrayReserve) by (destruct R4 as (_ & _ & _ & _ & S4 & _); exact S4).

  set (mk := maskv (fs_footb G) m) in *. set (mk' := maskv (fs_footb G) m').
  assert (MK : forall z, m' z = m z -> mk' z = mk z) by (intros z E; unfold mk, mk', maskv; rewrite E; reflexivity).
  assert (Zimg : forall z, IMG_LO <= z < IMG_HI -> ~ dstatw z -> m' z = m z) by (intros z Hz _; apply AV; unfold IMG_HI in Hz; clear -Hz TG; lia).
  assert (Zimg' : forall z, IMG_LO <= z < IMG_HI -> m' z = m z) by (intros z Hz; apply AV; unfold IMG_HI in Hz; clear -Hz TG; lia).
  assert (Zsp : forall z, ag_spacebeg G <= z < ag_spacebeg G + kSpaceSize + 4096 -> m' z = m z) by (intros z Hz; apply AV; clear -Hz S2; lia).
  assert (Zth : forall z, ag_thread G <= z < ag_thread G + 0x1000 -> m' z = m z) by (intros z Hz; apply AV; clear -Hz T2; lia).
  assert (Zctx : forall z, ag_ctx G <= z < ag_ctx G + 0x1000 -> m' z = m z) by (intros z Hz; apply AV; clear -Hz C2; lia).
  assert (Zdtls : forall z, ag_dtls G <= z < ag_dtls G + 0x1000 -> m' z = m z) by (intros z Hz; apply AV; clear -Hz D2; lia).
  assert (Zfs : forall z, ag_fsb G <= z < ag_fsb G + FS_total -> m' z = m z) by (intros z Hz; apply AV; clear -Hz F2; lia).
  assert (Zpab : forall z, ag_pab G <= z < ag_pab G + kPtrArrayReserve -> m' z = m z).
  { intros z Hz. apply AV. destruct HPAB as [_ (_ & _ & P3 & _)]. clear -Hz P3. lia. }
  assert (Zsec : forall ch z, In ch (aa_sec A) -> sc_map_beg ch <= z < sc_map_beg ch + sc_map_size ch -> m' z = m z).
  { intros ch z Hch Hz. apply AV. destruct (In_nth_error _ _ Hch) as [i Hi]. destruct R4 as [S1' _].
    destruct (S1' i ch Hi) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & D12 & _). fold G in D12. clear -Hz D12. lia. }
  assert (Zband : forall z, SHADOW_BAND_LO <= z < SHADOW_BAND_HI -> m' z = m z).
  { intros z Hz. apply AV. unfold SHADOW_BAND_HI, HIGH_SHADOW_END in Hz. clear -Hz TG. lia. }
  split; [exact HG|].
  split.
  { eapply (rtc_inv_z G m m'); first [ eassumption | intros; first [ apply Zimg; assumption | apply Zth; assumption | apply Zctx; assumption | apply Zdtls; assumption | apply Zfs; assumption ] ]. }
  split.
  { replace (restrictv (fs_footb G) m') with (restrictv (fs_footb G) m); [exact HF|].
    apply functional_extensionality. intros z. unfold restrictv. destruct (fs_footb G z) eqn:E; [|reflexivity].
    symmetry. apply AV. unfold fs_footb in E. cbn zeta in E.
    pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4.Sh_lt_HSE (ag_fsb G + FS_total) ltac:(clear -F2 TG; lia)) as SL. unfold HIGH_SHADOW_END in SL.
    apply orb_prop in E as [E|E]; [apply orb_prop in E as [E|E]|]; apply andb_prop in E as [_ E]; apply Z.ltb_lt in E; rewrite ?FS_total_val in *; clear -E F2 SL TG; lia. }
  split; [|split; [exact HM | split; [exact HI3 | eapply bandtp_agree; [exact Zband | exact HB]]]].
  split; [exact R1|].
  Ltac zargQ MK Zimg Zsp Zth Zctx Zdtls Zfs Zpab Zsec Zband :=
    first [ eassumption | reflexivity
          | intros; apply MK; first [ apply Zsp; assumption | apply Zth; assumption | apply Zctx; assumption | apply Zdtls; assumption
                                    | apply Zfs; assumption | apply Zpab; assumption | apply Zband; assumption
                                    | eapply Zsec; eassumption | apply Zimg; assumption ] ].
  split; [eapply (live_block_repr_z G (aa_sec A) mk mk'); zargQ MK Zimg Zsp Zth Zctx Zdtls Zfs Zpab Zsec Zband|].
  split; [eapply (primary_repr_z G mk mk'); zargQ MK Zimg Zsp Zth Zctx Zdtls Zfs Zpab Zsec Zband|].
  split; [eapply (secondary_repr_z G (aa_sec A) mk mk'); zargQ MK Zimg Zsp Zth Zctx Zdtls Zfs Zpab Zsec Zband|].
  split.
  { split; [exact R5|]. eapply cell_ok_agree; [|exact R5m]. cbn [c_addr c_w]. intros k Hk. apply MK. apply Zimg'. unfold QG, IMG_LO, IMG_HI. clear -Hk. lia. }
  split.
  { destruct HI3 as (_ & _ & _ & _ & DEP3 & _). unfold depot_wf in *. eapply depot_mem_frame; [|exact R6]. intros a Ha. apply MK.
    destruct Ha as [Hs|[(bb & Hbb & Hab)|(bb & Hbb & Hab)]].
    - apply Zimg'. exact (dstat_img a Hs).
    - apply AV. destruct (DEP3 (bb, NBSZ)) as ((_ & _ & W3 & _) & _); [unfold dblocks; apply in_or_app; left; apply in_map_iff; exists bb; split; [reflexivity | exact Hbb]|].
      cbn [fst snd] in W3. fold G in W3. clear -Hab W3. lia.
    - apply AV. destruct (DEP3 (bb, FBSZ)) as ((_ & _ & W3 & _) & _); [unfold dblocks; apply in_or_app; right; apply in_map_iff; exists bb; split; [reflexivity | exact Hbb]|].
      cbn [fst snd] in W3. fold G in W3. clear -Hab W3. lia. }
  split; [eapply (ia_inv_z mk mk'); zargQ MK Zimg Zsp Zth Zctx Zdtls Zfs Zpab Zsec Zband|].
  split; [eapply (thread_inv_z G mk mk'); zargQ MK Zimg Zsp Zth Zctx Zdtls Zfs Zpab Zsec Zband|].
  eapply (misc_inv_z mk mk'); zargQ MK Zimg Zsp Zth Zctx Zdtls Zfs Zpab Zsec Zband.
Qed.

Theorem K0_frame_top : ltac2:(tb__ "0|1|
S13SfS1S1S6S5Q40A1M0A1S6ScA1SbSaS8G0S2R5R1A2S2R6R1A2A3Fi;S9S12R1S11S10R8A1A1A2S8S7S5Q8A1A1S4S3S0R7A1R2A3S4S3S0R8A1R2A3A3F_;Fz;SeR9R8R7R5R4R3A6SeRaR9R7R6R5R4A6F_;F_;F_;Fmd;Ftr;Ftp;Frho';Frho;FA;FKc;").
Proof.
  intros Kc A rho rho' tp tr md Hw AV (HA & HK & Htp & Htop & HRG).
  split; [exact (AInvQ_frame_top A rho rho' tp md HA AV)|]. split; [exact HK|]. split; [|split].
  - unfold tp_ok in *. rewrite (Hw 24%positive). exact Htp.
  - unfold top_high in *. rewrite (Hw 10%positive), (Hw V_DEPTH). exact Htop.
  - destruct HRG as (E1 & E2 & E3 & E4). unfold rigidQ. rewrite !Hw. exact (conj E1 (conj E2 (conj E3 E4))).
Qed.
End InvQ6.

(* [comment removed for export] *)
Module InvQ5.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "and"; "eq"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "qsize"; "fs_footb"; "AInvA"; "QG"; "q_foot"; "quarantine_repr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@Corelib.Init.Datatypes"; "bool"; "false"; "list"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kQuarantineCacheMax"; "kQuarantineMax"; "Sh"; "kQuarantineMin"; "kUserSpaceSize"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "aa_q_global"; "aa_q_thread"; "ag_fsb"; "cs_allocated_user"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2"; "q_mem"; "cls_of"; "q_pure"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rm"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "view"; "bview"; "cell_ok"; "mkACell"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "top_high"; "tp_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ"; "AInvQ"; "K0"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector list.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import BackingAlgebra Virt SoundA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull SMGlue RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jc.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.LiveGeom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jb.InvQ2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jc.InvQ3.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma qrepr_of_split : ltac2:(tb__ "0|0|
S24S16S1eR1A1S1cR3R2A2S25R4S26S1SaZ48A2U8S14A3A2S0S7S19R4A1A1S11A2S0S7S18R5A1A1S12A2ScR7R6A2F_;F_;F_;F_;F_;FA;Fm;").
Proof.
  intros m A [QP QN] (QB & QL1 & QL2 & QH1 & QH2 & QMX) HMIN HB1 HB2. unfold quarantine_repr. fold (qall A).
  split; [|exact (conj QL1 (conj QL2 (conj QH1 (conj QH2 (conj QMX (conj HMIN (conj HB1 (conj HB2 QN))))))))].
  apply Forall_forall. intros b Hb.
  pose proof (proj1 (Forall_forall _ _) QP b Hb) as (P1 & P2 & (y & E & Y0 & YM & Y1) & P4).
  pose proof (proj1 (Forall_forall _ _) QB b Hb) as (M1 & M2 & M3 & M4 & M5).
  unfold batch_repr. split; [unfold HIGH_SHADOW_END, IMG_HI in *; lia|]. split; [exact M1|]. split; [exact M2|]. split; [exact P2|]. split; [exact M3|]. split; [exact M4|].
  split; [|exists y; exact (conj E (conj Y0 (conj YM Y1)))].
  intros i it Hi. destruct (M5 i it Hi) as [C IM]. split; [exact C|].
  pose proof (proj1 (Forall_forall _ _) P4 it (nth_error_In _ _ Hi)) as (I1 & I2 & I3 & I4).
  destruct IM as (X1 & X2 & X3 & X4 & X5 & X6 & X7). unfold q_item_ok. cbn zeta. unfold cls_of in I3.
  exact (conj I1 (conj I2 (conj X1 (conj X2 (conj X3 (conj X4 (conj X5 (conj X6 (conj I3 (conj I4 X7)))))))))).
Qed.

Section Back.
Variable A : AA.
Hypothesis HG : geom_ok (aa_geom A).
Hypothesis HI3 : inv3 A.
Hypothesis HQP : q_pure A.
Hypothesis HAU : ltac2:(tb__ "0|1|
S3S4S0Z1R1A2S0R1Z1eA2A2S4S0Z0S1bS1dVA;R2A2A1M0A2S0G0S15A2A2F_;Fc;").
Variable mq : bview.
Hypothesis HSR : secondary_repr mq A.
Local Abbreviation Gq := (aa_geom A).
Local Abbreviation SBq := (ag_spacebeg (aa_geom A)).
Local Abbreviation Fq := (ag_fsb (aa_geom A)).

Lemma fs_out : ltac2:(tb__ "0|2|
S3S3S3S4S0R3R1A2S2R1R2A2A2S6S0R3S1aS17VA;A1M0A1M1A2S0S1G1Zb09000A2R4A2A2S6S0R4Z7fff7000A2S0Z10007fff8000R5A2A2S5SeS8G0R4A2SfA3F_;F_;F_;Fz;Fhi;Flo;").
Proof.
  intros lo hi z Hz OF OB. pose proof HI3 as (H3 & _).
  pose proof (geoQ2 A HG H3) as ((F1 & FT & FS & FB) & _). pose proof (geoQ A HG H3) as (_ & _ & _ & _ & _ & _ & _ & _ & TG).
  pose proof (geom_numsS _ HG) as (_ & _ & F2 & _).
  assert (B1 : 2147450880 <= Sh (Fq + FS_frames_off)).
  { unfold Sh, SHADOW_OFF. rewrite ?FS_frames_off_val. pose proof (Z.div_pos (Fq + FS_frames_off) 8) as D. rewrite ?FS_frames_off_val in D. lia. }
  pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4.Sh_lt_HSE (Fq + FS_total) ltac:(rewrite FS_total_val; clear -F2 TG; lia)) as B2. unfold HIGH_SHADOW_END in B2.
  apply fs_footb_false_intro; rewrite ?FS_total_val in *; unfold FS_kFlagsOffset; clear -Hz OF OB B1 B2; lia.
Qed.
Lemma fs_sh_out : ltac2:(tb__ "0|2|
S3S3S3S4S0S13R3A1R1A2S2R1S13R2A1A2A2S0Z0R4A2S0R4Z7fffff800000A2S6S0R5S1aS17VA;A1M0A1M1A2S0S1G1Zb09000A2R6A2A2S5SeS8G0R5A2SfA3F_;F_;F_;F_;Fz;Fhi;Flo;").
Proof.
  intros lo hi z Hz L0 HT OF. pose proof HI3 as (H3 & _).
  pose proof (geoQ2 A HG H3) as ((F1 & FT & FS & FB) & _).
  assert (B1 : 2147450880 <= Sh lo) by (unfold Sh, SHADOW_OFF; pose proof (Z.div_pos lo 8 L0 ltac:(lia)); lia).
  assert (B2 : Sh hi <= 17594332446720).
  { unfold Sh, SHADOW_OFF. pose proof (Z.div_le_mono hi 140737479966720 8 ltac:(lia) HT) as M. change (140737479966720 / 8) with 17592184995840 in M. lia. }
  assert (M3 : z < Sh (Fq + FS_frames_off) \/ Sh (Fq + FS_total) <= z).
  { rewrite FS_total_val. destruct OF as [O|O].
    - left. pose proof (Geometry.Sh_mono hi Fq O). pose proof (Geometry.Sh_mono Fq (Fq + FS_frames_off) ltac:(rewrite ?FS_frames_off_val; lia)). lia.
    - right. pose proof (Geometry.Sh_mono (Fq + 11571200) lo O). lia. }
  apply fs_footb_false_intro; [| | exact M3]; rewrite ?FS_total_val; unfold FS_kFlagsOffset; clear -Hz FB B1 B2; lia.
Qed.

Lemma QF_fs : ltac2:(tb__ "0|0|
S3SbVA;R1A2S5SeS8S17VA;A1R2A2SfA3F_;Fz;").
Proof.
  intros z Hz. pose proof HI3 as (H3 & _ & SEC3 & _). pose proof (geoQ A HG H3) as (T1 & T2 & S1 & S2 & S8 & ST & TB & TI & TG).
  unfold q_foot in Hz. fold (qall A) in Hz. apply Exists_exists in Hz as (b & Hb & Hz).
  assert (PRIM : qzone A z -> fs_footb Gq z = false).
  { intros QZ. exact (QT_fs A HG H3 HQP HAU z (or_introl (or_introl QZ))). }
  destruct Hz as [Hz|Hz].
  - apply PRIM. unfold qzone. apply Exists_exists. exists b. split; [exact Hb | left; exact Hz].
  - apply Exists_exists in Hz as (it & Hit & Hz). destruct (is_primary (snd it)) eqn:EP.
    + apply PRIM. unfold qzone. apply Exists_exists. exists b. split; [exact Hb | right]. apply Exists_exists. exists it. split; [exact Hit|]. split; [exact EP | exact Hz].
    + destruct HQP as [QP _]. pose proof (proj1 (Forall_forall _ _) QP b Hb) as (_ & _ & _ & HIP). pose proof (proj1 (Forall_forall _ _) HIP it Hit) as (IP1 & IP2 & _ & IP4).
      destruct (IP4 EP) as (ch & Hch & Eu & Esz). destruct (In_nth_error _ _ Hch) as [i Hi].
      destruct HSR as (HS1 & _). destruct (HS1 i ch Hi) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & D11 & D12 & _).
      destruct (SEC3 i ch Hi) as (_ & _ & _ & X4 & _). rewrite FS_total_val in X4.
      destruct D10 as (E1 & E2 & E3 & E4 & E5). unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in E5.
      pose proof (rz_sec (snd it) IP2 EP) as RZ. pose proof (round_up_ge8 (snd it)) as R8. unfold PG in *.
      destruct Hz as [Hz|Hz].
      * apply (fs_out (sc_map_beg ch) (sc_map_beg ch + sc_map_size ch) z); [clear -Hz RZ Eu Esz D8 R8 IP2; lia | exact X4 | exact E5].
      * apply (fs_sh_out (sc_map_beg ch) (sc_map_beg ch + sc_map_size ch) z); [| clear -E1; lia | clear -E3 TG; lia | exact X4].
        assert (B8 : fst it mod 8 = 0).
        { destruct (proj1 (Z.mod_divide (sc_map_beg ch) 4096 ltac:(lia)) D6) as [k0 Hk0]. apply Z.mod_divide; [lia|]. exists (k0 * 512 + 768). lia. }
        pose proof (Sh_SB (fst it) (8 * ((snd it + 7) / 8)) B8) as E8. rewrite (Z.mul_comm 8), Z.div_mul in E8 by lia.
        pose proof (Z.div_mod (snd it + 7) 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (snd it + 7) 8 ltac:(lia)) as MB.
        pose proof (Geometry.Sh_mono (sc_map_beg ch) (fst it) ltac:(clear -Eu; lia)) as M1.
        pose proof (Geometry.Sh_mono (fst it + (snd it + 7) / 8 * 8) (sc_map_beg ch + sc_map_size ch) ltac:(clear -Eu Esz D8 R8 DM MB; lia)) as M2.
        clear -Hz E8 M1 M2. lia.
Qed.
End Back.

Theorem AInvQ_back : ltac2:(tb__ "0|0|
S16S22S10S27Q40A1A1S1fS2bR4R3R2R1A4S1cS23SdS21R4A1A2R5A2S0S7S19R6A1A1S11A2S0S7S18R7A1A1S12A2S9SdR8R7R6R5A5F_;F_;F_;F_;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md (HG & HR & HF & HRest & HM & HI3 & HB) HQM HB1 HB2. cbn zeta in *.
  destruct HRest as (R1 & R2 & R3 & R4 & (R5 & R5m) & R6 & R7 & R8 & R9).
  set (m := view segsA (rm rho)) in *.
  assert (HAU : forall c, 1 <= c <= 30 -> 0 <= cs_allocated_user (cls_of A c) <= kUserSpaceSize).
  { intros c Hc. destruct R3 as (_ & _ & _ & P4). pose proof (P4 c Hc) as HC. unfold class_repr in HC. cbn zeta in HC.
    destruct HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & N2 & N3 & _). unfold cls_of, kUserMapSize in *. lia. }
  assert (HMINp : cell_ok m (mkACell (QG + 72) 8 kQuarantineMin)).
  { apply (cell_tr A m); [|exact R5m]. cbn [c_addr c_w]. intros k Hk. apply (MI A m HG). unfold QG. lia. }
  pose proof (qrepr_of_split m A R5 HQM HMINp HB1 HB2) as QR.
  unfold AInvA. cbn zeta. fold m.
  split; [exact HG|]. split; [exact HR|]. split; [exact HF|]. split; [|exact (conj HM (conj HI3 HB))].
  split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [|exact (conj R6 (conj R7 (conj R8 R9)))].
  apply (quarantine_repr_agree_gen m (maskv (fs_footb (aa_geom A)) m) A A eq_refl eq_refl eq_refl eq_refl); [| | | exact R1 | | | | | exact QR].
  - intros c. reflexivity.
  - intros c. reflexivity.
  - intros c x H. exact H.
  - apply Forall_forall. intros qb _. apply Forall_forall. intros it _. pose proof (rz_bound (snd it)). lia.
  - intros z Hz. apply maskv_out. exact (QF_fs A HG HI3 R5 HAU _ R4 z Hz).
  - intros z Hz. apply maskv_out. apply fs_footb_T; [exact HG | lia].
  - intros z Hz. apply maskv_out. apply fs_footb_img; [exact HG | unfold QG in Hz; lia].
Qed.

Theorem K0_back : ltac2:(tb__ "0|0|
S28S16S22S10S27Q40A1A1S10S20A1S1fS2cR6R5R4R3R2R1A6S1cS23SdS21R5A1A2R6A2S0S7S19R7A1A1S11A2S0S7S18R8A1A1S12A2S4S9SdR9R8R7R5A5S4RaR6R5A2S4S2aR9R8A2S29R9R8A2A2A2A2F_;F_;F_;F_;Fmd;Ftr;Ftp;Frho;FA;FKc;").
Proof.
  intros Kc A rho tp tr md (HA & HK & Htp & Htop & _) HQM HB1 HB2.
  exact (conj (AInvQ_back A rho tp md HA HQM HB1 HB2) (conj HK (conj Htp Htop))).
Qed.
End InvQ5.

(* [comment removed for export] *)
Module InvQ4.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "ex"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "qbatch"; "aa_geom"; "cs_cache"; "cs_allocated_user"; "AA"; "ageom"; "class_state"; "aa_cache_inited"; "cs_mapped_free_array"; "qb_items"; "ag_thread"; "cs_mapped_user"; "mkQB"; "cs_free_array"; "aa_cls"; "aa_live"; "aa_q_global"; "aa_q_thread"; "aa_sec"; "is_large"; "qb_addr"; "ag_spacebeg"; "list_upd"; "sec_chunk"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "of_nat"; "lt"; "mul"; "eqb"; "modulo"; "shiftl"; "to_nat"; "@Corelib.Init.Datatypes"; "app"; "list"; "nil"; "length"; "cons"; "bool"; "prod"; "option"; "true"; "None"; "snd"; "nat"; "Some"; "andb"; "false"; "fst"; "negb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "view"; "cell_ok"; "mkACell"; "maskv"; "bview"; "acell"; "c_addr"; "c_w"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2"; "cls_of"; "set_q"; "push_cache"; "QW"; "pc_entry"; "push_zone"; "batch_pure"; "push_cs"; "KQ_laws"; "q_pure"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rm"; "rw"; "rl"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs"; "q_ids"; "qall"; "qitems"; "it_cls"; "it_id"; "qb_id"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ"; "K0"; "@Stdlib.Lists.List"; "In"; "filter"; "nth_error"; "@Stdlib.Sorting.Permutation"; "Permutation"; "@Corelib.Init.Nat"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "is_primary"; "Size"; "max_count"; "kCompactPtrScale"; "free_array"; "kUserSpaceSize"; "region_info"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "fs_footb"; "class_repr"; "live_ids"; "q_foot"; "geom_ok"; "inv3"; "live_sep"; "model_inv"; "primary_repr"; "qlarge"; "secondary_repr"; "slot_zone"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "@Corelib.Lists.ListDef"; "map"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCredit"; "prim_credit"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jd.InvQ4"; "cls_metaRF"; "@stdpp.base"; "NoDup"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector list.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import BackingAlgebra Virt SoundA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull SMGlue RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jc.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.LiveGeom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jb.InvQ2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jc.InvQ3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require PrimCredit PrimCreditLaws.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma perm_push : ltac2:(tb__ "0|1|
S29S0A1M0G0G0G0S0S5bS0S28S0R5S28S0S28S0R4S2cS0R1S2aS0A1A3A3S28S0R3R2A3A3A3S28S0R5S28S0R4S28S0R3S2cS0R1R2A3A3A3A3A3Fx;FB;FL;FC;FF;").
Proof.
  intros F C L B x. apply Permutation_app_head. rewrite <- app_assoc. apply Permutation_app_head. cbn [app]. apply Permutation_middle.
Qed.

Lemma qitems_mid : ltac2:(tb__ "0|2|
S29S7A1M0S7G0S2S29S2eS0S0A2M1A1S52S28S7R3S2cS7R2R1A3A3A1S28G1S52R3A1S28G1S10R2A1S52R1A1A3A3A3Fg2;Fb;Fg1;").
Proof. intros. unfold qitems. rewrite flat_map_app. reflexivity. Qed.

Lemma filter_map_mid : forall {X Y} (f : X -> Y) (P : X -> bool) (l1 : list X) (x : X) (l2 l3 : list X),
  Permutation (map f (List.filter P (l1 ++ (x :: l2) ++ l3))) ((if P x then [f x] else []) ++ map f (List.filter P (l1 ++ l2 ++ l3))).
Proof.
  intros X Y f P l1 x l2 l3. rewrite !List.filter_app. cbn [List.filter]. destruct (P x).
  - rewrite !map_app. cbn [map app]. apply Permutation_sym. apply Permutation_middle.
  - cbn [app]. apply Permutation_refl.
Qed.
Lemma q_ids_pop_item : ltac2:(tb__ "0|3|
ScS29S7A1M0G0S0S2eS0S0A2M1S29G1A1S0S0S0S5bS0S50R9S28S7R8S2cS7S13R6S2cG1R5R4A3R3A3R7A3A3R1A3S28S0S2dS29S0A1L_;S35S5dS32S0S0R5A3A1S24S53R5A1R1A2A2S2cS0S54R9R5A2S2aS0A1M2A3G2X2dx2S50R9S28S7R8S2cS7S13R6R4R2A3R7A3A3R1A3A3A3Fc';Fs';Fs;Fi2;Fit;Fa;Fg2;Fg1;FG;").
Proof.
  intros G g1 g2 a it i2 s s' c'. unfold q_ids. rewrite !qitems_mid. cbn [qb_items].
  replace (map (qb_id G) (g1 ++ mkQB a (it :: i2) s :: g2)) with (map (qb_id G) (g1 ++ mkQB a i2 s' :: g2)) by (rewrite !map_app; reflexivity).
  eapply Permutation_trans.
  { apply Permutation_app_tail. exact (filter_map_mid (it_id G) (fun it0 : Z * Z => is_primary (snd it0) && (it_cls it0 =? c')) (qitems g1) it i2 (qitems g2)). }
  cbn beta. rewrite <- app_assoc. apply Permutation_refl.
Qed.

Lemma q_ids_pop_batch : ltac2:(tb__ "0|3|
ScS29S7A1M0G0S7S0S2S29S2eS0S0A2M1A1S10R2A1S2aG1A1A3S5bS0S50R6S28S7R5S2cS7R3R4A3A3R2A3S28S0S2dS29S0A1L_;S24R2Z18A2S2cS0S55R6R3A2S2aS0A1M2A3G2X2dx2S50R6S28S7R5R4A3R2A3A3A3F_;Fc';Fb;Fg2;Fg1;FG;").
Proof.
  intros G g1 g2 b c' HE. unfold q_ids. rewrite qitems_mid, HE. cbn [app].
  replace (qitems g1 ++ qitems g2) with (qitems (g1 ++ g2)) by (unfold qitems; apply flat_map_app).
  destruct (c' =? 24).
  - rewrite !map_app. cbn [map app].
    set (F := map (it_id G) _). set (M1 := map (qb_id G) g1). set (M2 := map (qb_id G) g2).
    rewrite (app_assoc F M1). rewrite (app_assoc F M1 M2). apply Permutation_sym. apply Permutation_middle.
  - cbn [app]. apply Permutation_refl.
Qed.

Lemma batch_pure_same : ltac2:(tb__ "0|0|
SbSbS7S2ScS8R2A1S8R3A1A3S2S29S1eA1S19R3A1S19R4A1A3S0S2S0SaS42R5R1A2A1SaS42R6R1A2A1A3Fc';S48R6R4A2S48R6R5A2F_;F_;F_;F_;Fb;FA';FA;").
Proof.
  intros A A' b EG ES EAU (B1 & B2 & (y & E & Y0 & YM & Y1) & B4). unfold batch_pure. rewrite EG, (EAU 24).
  split; [exact B1|]. split; [exact B2|]. split; [exists y; exact (conj E (conj Y0 (conj YM Y1)))|].
  eapply Forall_impl; [|exact B4]. intros it (I1 & I2 & I3 & I4). unfold item_pure. cbn zeta. rewrite EG, ES, (EAU (ClassID (needed (snd it)))).
  exact (conj I1 (conj I2 (conj I3 I4))).
Qed.

Definition cls_metaRF (G : ageom) (c : Z) (cs : class_state) (z : Z) : Prop := ltac2:(tb__ "0|1|
S63S1cVG;A1M0Vc;A2S0S61G0Vc;A2S0S6S3S20R2Vz;A2S22Vz;S1fR2Z80A2A2A2S3S20R1Vz;A2S22Vz;S1fR1SfVcs;A1A2A2A2A2Tfa;Tri;").

Lemma class_repr_push_gen : ltac2:(tb__ "0|e|
S3eS3eScSbSbS0SdSdS3S20Z1R3A2S20R3Z1eA2A2S2S2dSeR5A1SeR6A1A3S2S29S2eS0S0A2A1S16R6A1S16R7A1A3S2S29S0A1S14R4A1S14R5A1A3S2S0SfR5A1SfR6A1A3S2S0SaR6A1SaR7A1A3S2S0S12R7A1S12R8A1A3S0S77ReRbRaR1A4S2S2fS56Q8A1M0A1M1R10R2A1R11R2A1A3F_;Fz;S0S5G0G0S2G1R12R2A1S34G0R1A2M2A3Lb;A2S5G0G0S2G1R12R3A1G2A3Lb;A2F_;Fz;S78S0S28S0S14RbA1S28S0S9RaA1S28S0S66RfRdRcA3S50RfS51RdA1RcA3A3A3A3A2S2S33S5cS5cS2bS0S9RbA1A2S2bS0S66R10ReRdA3A2A2S2bS0S50R10S51ReA1RdA3A2A2S5cS5cS2bS0S9RcA1A2S2bS0S66R10RfRdA3A2A2S2bS0S50R10S51RfA1RdA3A2A2A3S0S58S0R1S9RdA1M3A3S3S20Z0M4R2A2S3S2S0S25S26R2S60A2M5S5eR10A1M6A2G4A3S20S1fG5G6A2SaRfA1A2A2A2F_;Fx;S3S3bR13S3cS1fS1fS11R12A1Zd0M7A2S23Z50M8RfA2A2M9U4MaS21S2bS0G3A2A1MbA3A2S3S3bR13S3cS1fG9Z4McA2GaS5fRfA1MdA3A2S3S3bR13S3cS1fG9Z8A2U8S5eRfA1A3A2S3S33S0S2S2fS0A1S5aS0S9RfA1R2A3S34S0R1A2A3S3bR16S3cS1fS1fS1fS1fS11R15A1G7A2S23G8R12A2A2Z10A2S23GcS21R3A1A2A2GaR2A3A2F_;Fx;Fi;S20GbGdA2A2A2A2A2S2S2dSeR12A1S30A3S65R16R14R13R11R10A5S65R16R15R13R12R10A5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fcs';Fcs;Fc;FA';FA;FG;Fm';Fm;").
Proof.
  intros m m' G A A' c cs cs' Hc ECI ELV EF EMF EAU EMU AG PK ND' CNT' SL' CI' HCI P4.
  assert (CA : forall cc, (forall k, (k < c_w cc)%nat -> cls_metaRF G c cs (c_addr cc + Z.of_nat k)) -> cell_ok m cc -> cell_ok m' cc).
  { intros cc Hf. apply cell_ok_agree. intros k Hk. apply AG. exact (Hf k Hk). }
  assert (PP : forall lo hi, present m lo hi -> present m' lo hi) by (intros lo hi H z Hz; exact (PK z (H z Hz))).
  unfold class_repr in P4 |- *. rewrite ECI, ELV, EF, EMF, EAU, EMU.
  set (ri := region_info (ag_spacebeg G) c) in *. set (fa := free_array (ag_spacebeg G) c) in *. set (rb := region_beg (ag_spacebeg G) c) in *.
  destruct P4 as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & PRI & N1 & N2 & N3 & N4 & N5 & N6 & C9 & PR & N7 & PU & PS & PE & ND & LV & CI & CN & CT & CC & CMU & CFA).
  assert (FRI : forall off w, 0 <= off -> off + Z.of_nat w <= 72 -> forall k, (k < w)%nat -> cls_metaRF G c cs (ri + off + Z.of_nat k)).
  { intros off w Ho Hw k Hk. left. unfold ri in *. lia. }
  split; [apply CA; [cbn [c_addr c_w]; apply FRI; unfold RI_mutex; lia | exact C1]|].
  split; [apply CA; [cbn [c_addr c_w]; apply FRI; unfold RI_num_freed; lia | exact C2]|].
  split; [apply CA; [cbn [c_addr c_w]; apply FRI; unfold RI_mapped_free_array; lia | exact C3]|].
  split; [apply CA; [cbn [c_addr c_w]; apply FRI; unfold RI_allocated_user; lia | exact C4]|].
  split; [apply CA; [cbn [c_addr c_w]; apply FRI; unfold RI_allocated_meta; lia | exact C5]|].
  split; [apply CA; [cbn [c_addr c_w]; apply FRI; unfold RI_mapped_user; lia | exact C6]|].
  split; [apply CA; [cbn [c_addr c_w]; apply FRI; unfold RI_mapped_meta; lia | exact C7]|].
  split; [apply CA; [cbn [c_addr c_w]; apply FRI; unfold RI_exhausted; lia | exact C8]|].
  split; [exact (PP _ _ PRI)|].
  split; [exact N1|]. split; [exact N2|]. split; [exact N3|]. split; [exact N4|]. split; [exact N5|]. split; [exact N6|].
  split.
  { intros i x Hi. apply CA; [|exact (C9 i x Hi)]. cbn [c_addr c_w]. intros k Hk. right.
    pose proof (nth_error_Some_lt _ _ _ Hi) as L. unfold fa in *. lia. }
  split; [exact (PP _ _ PR)|].
  split.
  { intros x0 Hx0. apply in_app_or in Hx0 as [Hx0|Hx0]; [apply N7; apply in_or_app; left; exact Hx0 | exact (SL' x0 Hx0)]. }
  split; [intros z Hz Hn; exact (PK z (PU z Hz Hn))|].
  split; [exact (PP _ _ PS)|]. split; [exact (PP _ _ PE)|].
  split; [exact ND'|].
  split; [exact LV|].
  split; [intros _; exact CI'|]. split; [intros HF; rewrite HCI in HF; discriminate|].
  split; [exact CT|]. split; [|exact (conj CMU CFA)].
  unfold slots in CC |- *. rewrite EAU, CC. f_equal. clear -CNT'. lia.
Qed.

Section Push.
Variables (Kc : KcA) (A : AA) (rho rho' : valuation) (tp : list word) (tr : list event) (md : Model).
Variables (q' : list qbatch) (c x : Z).
Local Abbreviation Gq := (aa_geom A).
Local Abbreviation SBq := (ag_spacebeg (aa_geom A)).
Local Abbreviation Tq := (ag_thread (aa_geom A)).
Local Abbreviation v0 := (view segsA (rm rho)).
Local Abbreviation v1 := (view segsA (rm rho')).
Local Abbreviation mm := (maskv (fs_footb (aa_geom A)) (view segsA (rm rho))).
Local Abbreviation mm' := (maskv (fs_footb (aa_geom A)) (view segsA (rm rho'))).
Local Abbreviation kk := (Z.of_nat (length (cs_cache (cls_of A c)))).
Local Abbreviation A1 := (set_q A [] q').
Local Abbreviation Ap := (push_cache (set_q A [] q') c x).

Hypothesis HK : ltac2:(tb__ "0|0|
S57VKc;VA;Vrho;Vtp;Vtr;Vmd;A6").
Hypothesis HCI : aa_cache_inited A = true.
Hypothesis Hc : 1 <= c <= 30.
Hypothesis Hk : kk < max_count c.
Hypothesis Hw : ltac2:(tb__ "0|0|
S1S2S56Q40A1S4dVrho';R1A2S4dVrho;R1A2A3Fi;").
Hypothesis HOUT : ltac2:(tb__ "0|0|
S0S4S45VA;R1A2A1S4S47S8VA;A1Vc;S21S2bS0S9S42VA;Vc;A2A1A2A1R2A4A1S2S2fS56Q8A1A1S3aS39S4cVrho';A1R3A3S3aS39S4cVrho;A1R3A3A3F_;F_;Fz;").
Hypothesis HIN : ltac2:(tb__ "0|3|
S0S45VA;R1A2S4S2S2fS56Q8A1M0A1M1S3aS39S4cVrho;A1R2A3S31G0A1M2A3A1S4S2G1S3aS39S4cVrho';A1R3A3G2A3A1F_;F_;Fz;").
Hypothesis HC1 : ltac2:(tb__ "0|0|
S3bS3aS39S4cVrho';A1A2S3cS46S8VA;A1Vc;A2U4S1fS21S2bS0S9S42VA;Vc;A2A1A2A1Z1A2A3A2").
Hypothesis HC2 : ltac2:(tb__ "0|0|
S3bS3aS39S4cVrho';A1A2S3cS1fS1fS46S8VA;A1Vc;A2Z10A2S23Z4S21S2bS0S9S42VA;Vc;A2A1A2A1A2A2U4Vx;A3A2").

Hypothesis HQ1 : Forall (batch_pure A) q'.
Hypothesis HQ2 : NoDup (map qb_addr q').
Hypothesis HQ3 : ltac2:(tb__ "0|2|
S0S3S20Z1R1A2S20R1Z1eA2A2S5bS0S50S8VA;A1M0S51VA;A1R2A3S28S0S2dS29S0A1L_;S24R2Vc;A2S2cS0Vx;S2aS0A1M1A3G1X2dx2S50G0Vq';R2A3A3A3F_;Fc';").
Hypothesis HSUB : ltac2:(tb__ "0|1|
S7S58S7R1Vq';A3S5S7S7S3S58S7R1S51VA;A1A3S3S2S0S1bR3A1S1bR1A1A3S2eS0S0A2M0S58G0R1S10R4A1A3S58G0R2S10R3A1A3F_;Fit;A2A2Lb;A2F_;Fb';").
Hypothesis HQ6 : ltac2:(tb__ "0|3|
S5bS0S72S2eS0S0A2M0S0S37S0S0A2M1S59G0G0S38S5dS32S0S0R1A3A1A1Lit;M2S52Vq';A1A3A4S72G0S0G1S59G0G2S52S51VA;A1A1A3A4A3").
Hypothesis HQ7 : ltac2:(tb__ "0|1|
S2S0S21S2bS2eS0S0A2M0S59G0S1aS52Vq';A1A3A2A1S6dVA;A1A3").
Hypothesis HX : ltac2:(tb__ "0|3|
S3S20Z0M0Vx;A2S3S2S0S25S26Vx;S60A2M1S5eVc;A1M2A2G0A3S20S1fG1G2A2SaS42VA;Vc;A2A1A2A2A2").

Lemma P_facts : ltac2:(tb__ "0|3|
S3S68S8VA;A1M0A1S3S69VA;A1S3S4bVA;A1S3S6aVA;A1S3S6cS3dS64G0A1S3aS39S4cVrho;A1A2A2M1VA;A2S3S6eG1VA;A2S0S3S20Z1R1A2S20R1Z1eA2A2S3S20Z0SaS42VA;R2A2A1M2A2S20G2S62A2A2F_;Fc';A2A2A2A2A2A2").
Proof.
  pose proof HK as (HA & _). destruct HA as (HG & _ & _ & HRest & _ & HI3 & _). cbn zeta in HRest.
  destruct HRest as (R1 & _ & R3 & R4 & (R5 & _) & _).
  split; [exact HG|]. split; [exact HI3|]. split; [exact R5|]. split; [exact R1|]. split; [exact R3|]. split; [exact R4|].
  intros c' Hc'. destruct R3 as (_ & _ & _ & P4). pose proof (P4 c' Hc') as HC. unfold class_repr in HC. cbn zeta in HC.
  destruct HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & N2 & N3 & _). unfold cls_of, kUserMapSize in *. lia.
Qed.

Lemma PZ_T : ltac2:(tb__ "0|2|
S0S47S8VA;A1M0Vc;S21S2bS0S9S42VA;Vc;A2A1A2A1R1A4S3S20S1fS11G0A1M1Zd0A2R2A2S22R2S1fG1Zad0A2A2A2F_;Fz;").
Proof.
  intros z Hz. unfold push_zone, pc_entry in Hz. pose proof (max_count_le16 c Hc) as M16. pose proof (Zle_0_nat (length (cs_cache (cls_of A c)))) as K0'.
  clear -Hz Hc Hk M16 K0'. lia.
Qed.
Lemma HINp : ltac2:(tb__ "0|3|
S0S6S45VA;R1A2S47S8VA;A1Vc;S21S2bS0S9S42VA;Vc;A2A1A2A1R1A4A2S4S2S2fS56Q8A1M0A1M1S3aS39S4cVrho;A1R2A3S31G0A1M2A3A1S4S2G1S3aS39S4cVrho';A1R3A3G2A3A1F_;F_;Fz;").
Proof.
  intros z [H|H] Hz; [exact (HIN z H Hz)|]. destruct H as [H|H].
  - apply (cell_ok_some v1 _ 4%nat _ z HC1). replace (Z.of_nat 4) with 4 by reflexivity. exact H.
  - apply (cell_ok_some v1 _ 4%nat _ z HC2). replace (Z.of_nat 4) with 4 by reflexivity. exact H.
Qed.

Lemma PLEN : length (aa_cls A) = 32%nat.
Proof. pose proof P_facts as (_ & _ & _ & _ & (PL & _) & _). exact PL. Qed.
Lemma ECLS_raw : ltac2:(tb__ "0|0|
S2S29SdA1S15S44S43VA;S2aS7A1Vq';A3Vc;Vx;A3A1S1dSdS15VA;A1S27Vc;A1S49S42VA;Vc;A2Vx;A2A4A3").
Proof. reflexivity. Qed.
Lemma ECLS_c : ltac2:(tb__ "0|0|
S2SdS42S44S43VA;S2aS7A1Vq';A3Vc;Vx;A3Vc;A2S49S42VA;Vc;A2Vx;A2A3").
Proof. unfold cls_of at 1. unfold nthZ. rewrite ECLS_raw. apply nth_list_upd_same. rewrite PLEN. clear -Hc. lia. Qed.
Lemma ECLS_o : ltac2:(tb__ "0|0|
S0S3S20Z1R1A2S20R1Z1eA2A2S4S2S0R2Vc;A3A1S2SdS42S44S43VA;S2aS7A1Vq';A3Vc;Vx;A3R3A2S42VA;R3A2A3F_;F_;Fc';").
Proof. intros c' Hc' NE. unfold cls_of, nthZ. rewrite ECLS_raw. apply nth_list_upd_other. clear -Hc Hc' NE. lia. Qed.
Lemma ECLS_nums : ltac2:(tb__ "0|2|
S0S3S2S0SaS42S44S43VA;S2aS7A1Vq';A3Vc;Vx;A3R1A2M0A1SaS42VA;R1A2M1A1A3S2S0S12G0A1S12G1A1A3A2Fc';").
Proof.
  intros c'. unfold cls_of, nthZ. rewrite ECLS_raw. destruct (Nat.eq_dec (Z.to_nat c) (Z.to_nat c')) as [E|NE].
  - rewrite <- E. rewrite nth_list_upd_same by (rewrite PLEN; clear -Hc; lia). split; reflexivity.
  - rewrite nth_list_upd_other by exact NE. split; reflexivity.
Qed.

Lemma NX : ltac2:(tb__ "0|0|
S4S58S0Vx;S50S8VA;A1Vq';Vc;A3A3A1").
Proof.
  intros Hin. pose proof P_facts as (_ & _ & _ & _ & (_ & _ & _ & P4) & _).
  destruct (P4 c Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ND & _).
  apply NoDup_app_r in ND. apply NoDup_app_r in ND. apply NoDup_app_r in ND.
  pose proof (HQ3 c Hc) as P. rewrite Z.eqb_refl in P.
  pose proof (ND_permQ _ _ (Permutation_sym P) ND) as ND2.
  exact (NoDup_app_disj [x] (q_ids Gq q' c) x ND2 (or_introl eq_refl) Hin).
Qed.

Lemma QP1 : q_pure A1.
Proof. split; [exact HQ1 | exact HQ2]. Qed.
Lemma QFOOT_sub : ltac2:(tb__ "0|0|
S0S67S43VA;S2aS7A1Vq';A3R1A2S67VA;R2A2F_;Fz;").
Proof.
  intros z Hz. unfold q_foot in *. change (aa_q_thread A1 ++ aa_q_global A1) with q' in Hz. fold (qall A).
  apply Exists_exists in Hz as (b' & Hb' & Hz). destruct (HSUB b' Hb') as (b & Hb & EA & HI). apply Exists_exists. exists b. split; [exact Hb|].
  rewrite <- EA. destruct Hz as [Hz|Hz]; [left; exact Hz | right].
  apply Exists_exists in Hz as (it & Hit & Hz). apply Exists_exists. exists it. split; [exact (HI it Hit) | exact Hz].
Qed.

Lemma QFOOT_slot : ltac2:(tb__ "0|0|
S0S67S43VA;S2aS7A1Vq';A3R1A2S4S6fS8VA;A1Vc;Vx;R2A4A1F_;Fz;").
Proof.
  intros z Hz HS. pose proof P_facts as (HG & HI3 & HQP & HLS & HPR & HSR & HAU). pose proof HI3 as (H3 & _ & SEC3 & _).
  pose proof (geoQ A HG H3) as (T1 & T2 & S1 & S2 & S8 & ST & TB & TI & TG).
  apply (slot_czone A c x z) in HS.
  pose proof HX as (X0 & XM & XE). unfold kCompactPtrScale in XM, XE. rewrite Z.shiftl_mul_pow2 in XM, XE by lia. change (2 ^ 4) with 16 in XM, XE.
  replace (x * 16) with (16 * x) in XM, XE by lia.
  pose proof (HAU c Hc) as AUc. rewrite kUserSpaceSize_val in AUc.
  unfold q_foot in Hz. change (aa_q_thread A1 ++ aa_q_global A1) with q' in Hz.
  apply Exists_exists in Hz as (b & Hb & Hz).
  assert (PRIM : qzone A1 z -> False).
  { intros QZ. destruct (qzone_czone A1 HG H3 QP1 HAU z QZ) as (c' & o' & (C1' & O0' & OM' & OE' & IDin') & CZ').
    apply (czone_slots_disj SBq c (16 * x) c' o' z S1 ltac:(clear -S2 TG; lia) S8 Hc C1' ltac:(clear -X0; lia) O0' XM OM' ltac:(clear -XE AUc; lia) OE'); [|exact HS|exact CZ'].
    destruct (Z.eq_dec c c') as [EC|NC]; [right | left; exact NC]. subst c'. intros EO. apply NX.
    rewrite <- EO in IDin'. replace (16 * x / 16) with x in IDin' by (rewrite Z.mul_comm, Z.div_mul; lia). exact IDin'. }
  destruct Hz as [Hz|Hz].
  - apply PRIM. unfold qzone. apply Exists_exists. exists b. split; [exact Hb | left; exact Hz].
  - apply Exists_exists in Hz as (it & Hit & Hz). destruct (is_primary (snd it)) eqn:EP.
    + apply PRIM. unfold qzone. apply Exists_exists. exists b. split; [exact Hb | right]. apply Exists_exists. exists it. split; [exact Hit|]. split; [exact EP | exact Hz].
    + pose proof (proj1 (Forall_forall _ _) HQ1 b Hb) as (_ & _ & _ & HIP). pose proof (proj1 (Forall_forall _ _) HIP it Hit) as (IP1 & IP2 & _ & IP4).
      destruct (IP4 EP) as (ch & Hch & Eu & Esz). destruct (In_nth_error _ _ Hch) as [i Hi].
      destruct HSR as (HS1 & _). destruct (HS1 i ch Hi) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & D11 & D12 & _).
      destruct (SEC3 i ch Hi) as (X1 & _). rewrite kSpaceSize_val in X1.
      destruct D10 as (E1 & E2 & E3 & E4 & E5). unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in E5.
      pose proof (rz_sec (snd it) IP2 EP) as RZ. pose proof (round_up_ge8 (snd it)) as R8. unfold PG in *.
      destruct Hz as [Hz|Hz].
      * apply (czone_out A HG H3 c (16 * x) (sc_map_beg ch) (sc_map_beg ch + sc_map_size ch) z Hc ltac:(clear -X0; lia) XM ltac:(clear -XE AUc; lia));
          [clear -Hz RZ Eu Esz D8 R8 IP2; lia | clear -X1; lia | exact E5 | exact HS].
      * apply (czone_sh_out A HG H3 c (16 * x) (sc_map_beg ch) (sc_map_beg ch + sc_map_size ch) z Hc ltac:(clear -X0; lia) XM ltac:(clear -XE AUc; lia));
          [| clear -E1; lia | clear -E3 TG; lia | clear -X1; lia | exact HS].
        assert (B8 : fst it mod 8 = 0).
        { destruct (proj1 (Z.mod_divide (sc_map_beg ch) 4096 ltac:(lia)) D6) as [k0 Hk0]. apply Z.mod_divide; [lia|]. exists (k0 * 512 + 768). lia. }
        pose proof (Sh_SB (fst it) (8 * ((snd it + 7) / 8)) B8) as E8. rewrite (Z.mul_comm 8), Z.div_mul in E8 by lia.
        pose proof (Z.div_mod (snd it + 7) 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (snd it + 7) 8 ltac:(lia)) as MB.
        pose proof (Geometry.Sh_mono (sc_map_beg ch) (fst it) ltac:(clear -Eu; lia)) as M1.
        pose proof (Geometry.Sh_mono (fst it + (snd it + 7) / 8 * 8) (sc_map_beg ch + sc_map_size ch) ltac:(clear -Eu Esz D8 R8 DM MB; lia)) as M2.
        clear -Hz E8 M1 M2. lia.
Qed.

Lemma CELLM : ltac2:(tb__ "0|3|
S3fS33S76R1S41R2A1A2S3S4S45VA;S1fS40R3A1S21R2A1A2M0A2A1S4S47S8VA;A1M1Vc;S21S2bS0S9S42VA;Vc;A2A1A2A1G0A4A1A2F_;Fj;S3bS3dS64G1A1M2S3aS39S4cVrho;A1A2A2R2A2S3bS3dG2S3aS39S4cVrho';A1A2A2R3A2F_;F_;Fcc;").
Proof. intros cc H. apply cell_ok_agree. intros j Hj. destruct (H j Hj) as [N1 N2]. unfold maskv. rewrite (HOUT _ N1 N2). reflexivity. Qed.
Lemma MT_eq : ltac2:(tb__ "0|2|
S3eS0S3S20S11S8VA;A1M0A1M1R1A2S22R1S1fG1Z1000A2A2A2S2S2fS56Q8A1A1S3dS64G0A1R3R2A3R3R2A1A3F_;Fz;Fv;").
Proof. intros v z Hz. pose proof P_facts as (HG & _). apply maskv_out. apply fs_footb_T; [exact HG | exact Hz]. Qed.

Lemma CR_push : ltac2:(tb__ "0|2|
S0S3S20Z1R1A2S20R1Z1eA2A2S65S3dS64S8VA;A1M0A1S3aS39S4cVrho';A1A2A2G0S44S43VA;S2aS7A1Vq';A3Vc;Vx;A3M1R2S42G1R2A2A5F_;Fc';").
Proof.
  intros c' Hc'. pose proof P_facts as (HG & HI3 & HQP & HLS & HPR & HSR & HAU). pose proof HI3 as (H3 & _).
  pose proof (geoQ A HG H3) as (T1 & T2 & S1 & S2 & S8 & ST & TB & TI & TG).
  destruct HPR as (PL & _ & _ & P4). pose proof (P4 c' Hc') as PC. fold (cls_of A c') in PC.
  assert (HFA : 0 <= cs_mapped_free_array (cls_of A c') <= kFreeArraySize).
  { unfold class_repr in PC. cbn zeta in PC. destruct PC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & N6 & _). clear -N6. lia. }
  assert (NPZ : forall z, SBq <= z < SBq + 2 ^ 37 + 4096 -> ~ push_zone Gq c kk z).
  { intros z Hz HP. pose proof (PZ_T z HP) as HT. clear -Hz HT ST. lia. }
  assert (AGRF : forall z, cls_metaRF Gq c' (cls_of A c') z -> mm' z = mm z).
  { intros z Hz. unfold maskv. rewrite HOUT; [reflexivity | |].
    - intros HQ. apply (QW_not_metaV A HG H3 HQP HAU c' (cls_of A c') Hc' HFA z HQ). unfold cls_metaRF in Hz. unfold cls_metaV. cbn zeta in *. destruct Hz as [Hz|Hz]; [left | right; left]; exact Hz.
    - apply NPZ. unfold cls_metaRF, region_info, free_array, region_beg, kRegionInfoStride in Hz. cbn zeta in Hz. rewrite kSpaceSize_val in Hz.
      unfold kFreeArraySize in HFA. rewrite kUserSpaceSize_val in Hz. unfold kRegionSize in Hz. clear -Hz Hc' HFA. nia. }
  assert (PK : forall z, (exists b, mm z = Some b) -> exists b, mm' z = Some b).
  { exact (MSOME A HG H3 HQP HAU rho rho' (push_zone Gq c kk) PZ_T HOUT HINp). }
  destruct (Z.eq_dec c' c) as [EC|NC].
  - subst c'. rewrite ECLS_c.
    pose proof PC as PC0. unfold class_repr in PC0. cbn zeta in PC0.
    destruct PC0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & N7 & _ & _ & _ & ND & _ & CI & _).
    destruct (CI HCI) as (K1 & K2 & K3 & K4 & K5).
    apply (class_repr_push_gen mm mm' Gq A Ap c (cls_of A c) (push_cs (cls_of A c) x) Hc eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl AGRF PK); [| | | | exact HCI | exact PC].
    + cbn [push_cs cs_cache]. change (qall Ap) with q'. change (live_ids Gq Ap c) with (live_ids Gq A c).
      eapply ND_permQ; [|exact ND]. eapply Permutation_trans; [apply perm_push|].
      apply Permutation_app_head. apply Permutation_app_head. apply Permutation_app_head.
      pose proof (HQ3 c Hc) as P. rewrite Z.eqb_refl in P. cbn [app] in P. apply Permutation_sym. exact P.
    +   cbn [push_cs cs_cache]. change (qall Ap) with q'. change (live_ids Gq Ap c) with (live_ids Gq A c).
      pose proof (HQ3 c Hc) as P. rewrite Z.eqb_refl in P. apply Permutation_length in P. cbn [app length] in P. rewrite length_app. cbn [length]. clear -P. lia.
    + cbn [push_cs cs_cache]. intros x0 Hx0. apply in_app_or in Hx0 as [Hx0|Hx0]; [apply N7; apply in_or_app; right; exact Hx0|].
      destruct Hx0 as [<-|[]]. exact HX.
    + cbn [push_cs cs_cache]. rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. change (Z.of_nat 1) with 1.
      pose proof (max_count_le16 c Hc) as M16. pose proof (Zle_0_nat (length (cs_cache (cls_of A c)))) as K0'.
      split; [|split; [|split; [|split; [|clear -Hk; lia]]]].
      * eapply cell_ok_agree; [|exact HC1]. cbn [c_addr c_w]. intros j Hj. apply MT_eq. unfold pc_entry. clear -Hj Hc. lia.
      * apply CELLM; [|exact K2]. cbn [c_addr c_w]. intros j Hj. split; [apply (QW_T A HG H3 HQP HAU); clear -Hj Hc; lia|].
        unfold push_zone, pc_entry. clear -Hj K0'. lia.
      * apply CELLM; [|exact K3]. cbn [c_addr c_w]. intros j Hj. split; [apply (QW_T A HG H3 HQP HAU); clear -Hj Hc; lia|].
        unfold push_zone, pc_entry. clear -Hj K0'. lia.
      * intros i x0 Hi. destruct (Nat.lt_ge_cases i (length (cs_cache (cls_of A c)))) as [L|L].
        -- rewrite nth_error_app1 in Hi by exact L. apply CELLM; [|exact (K4 i x0 Hi)]. cbn [c_addr c_w]. intros j Hj.
           split; [apply (QW_T A HG H3 HQP HAU); clear -Hj Hc L Hk M16; lia|]. unfold push_zone, pc_entry. clear -Hj L. lia.
        -- rewrite nth_error_app2 in Hi by exact L. destruct (i - length (cs_cache (cls_of A c)))%nat as [|d] eqn:ED; [|destruct d; discriminate].
           cbn in Hi. injection Hi as <-. assert (Ei : i = length (cs_cache (cls_of A c))) by (clear -L ED; lia). rewrite Ei.
           eapply cell_ok_agree; [|exact HC2]. cbn [c_addr c_w]. intros j Hj. apply MT_eq. unfold pc_entry. clear -Hj Hc Hk M16 K0'. lia.
  - rewrite (ECLS_o c' Hc' NC).
    pose proof PC as PC0. unfold class_repr in PC0. cbn zeta in PC0.
    destruct PC0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & N7 & _ & _ & _ & ND & _ & CI & _).
    destruct (CI HCI) as (K1 & K2 & K3 & K4 & K5).
    pose proof (max_count_le16 c' Hc') as M16.
    assert (PCE : forall z, Tq + 208 + 80 * c' <= z < Tq + 208 + 80 * c' + 80 -> ~ QW A z /\ ~ push_zone Gq c kk z).
    { intros z Hz. split; [apply (QW_T A HG H3 HQP HAU); clear -Hz Hc'; lia|]. intros HP. unfold push_zone, pc_entry in HP.
      pose proof (max_count_le16 c Hc) as M16c. pose proof (Zle_0_nat (length (cs_cache (cls_of A c)))) as K0'. clear -Hz HP NC Hk M16c K0'. lia. }
    apply (class_repr_push_gen mm mm' Gq A Ap c' (cls_of A c') (cls_of A c') Hc' eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl AGRF PK); [| | | | exact HCI | exact PC].
    + change (qall Ap) with q'. change (live_ids Gq Ap c') with (live_ids Gq A c').
      eapply ND_permQ; [|exact ND]. apply Permutation_app_head. apply Permutation_app_head. apply Permutation_app_head.
      pose proof (HQ3 c' Hc') as P. destruct (Z.eqb_spec c' c) as [E|_]; [exfalso; exact (NC E)|]. cbn [app] in P. apply Permutation_sym. exact P.
    +   change (qall Ap) with q'. change (live_ids Gq Ap c') with (live_ids Gq A c').
      pose proof (HQ3 c' Hc') as P. destruct (Z.eqb_spec c' c) as [E|_]; [exfalso; exact (NC E)|]. cbn [app] in P. apply Permutation_length in P. clear -P. lia.
    + intros x0 Hx0. apply N7. apply in_or_app. right. exact Hx0.
    + split; [|split; [|split; [|split; [|exact K5]]]].
      * apply CELLM; [|exact K1]. cbn [c_addr c_w]. intros j Hj. apply PCE. clear -Hj. lia.
      * apply CELLM; [|exact K2]. cbn [c_addr c_w]. intros j Hj. apply PCE. clear -Hj. lia.
      * apply CELLM; [|exact K3]. cbn [c_addr c_w]. intros j Hj. apply PCE. clear -Hj. lia.
      * intros i x0 Hi. pose proof (nth_error_Some_lt _ _ _ Hi) as L. apply CELLM; [|exact (K4 i x0 Hi)]. cbn [c_addr c_w]. intros j Hj. apply PCE. clear -Hj L K5 M16. lia.
Qed.

Lemma PR_push : primary_repr mm' Ap.
Proof.
  pose proof P_facts as (_ & _ & _ & _ & (PL & P0 & P31 & _) & _).
  split; [rewrite ECLS_raw, length_list_upd; exact PL|].
  split; [unfold nthZ in *; rewrite ECLS_raw, nth_list_upd_other by (clear -Hc; lia); exact P0|].
  split; [unfold nthZ in *; rewrite ECLS_raw, nth_list_upd_other by (clear -Hc; lia); exact P31|].
  intros c' Hc'. exact (CR_push c' Hc').
Qed.

Lemma QP_push : q_pure Ap.
Proof.
  split; [|exact HQ2]. change (qall Ap) with q'. eapply Forall_impl; [|exact HQ1]. intros b Hb.
  apply (batch_pure_same A Ap b eq_refl eq_refl); [|exact Hb]. intros c'. exact (proj1 (ECLS_nums c')).
Qed.

Lemma I3_push : inv3 Ap.
Proof.
  pose proof P_facts as (_ & HI3 & _). destruct HI3 as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9). unfold inv3. cbn zeta.
  change (aa_geom Ap) with (aa_geom A). change (aa_live Ap) with (aa_live A). change (aa_sec Ap) with (aa_sec A). change (aa_depot Ap) with (aa_depot A).
  split; [exact I1|]. split; [exact I2|]. split; [exact I3|].
  split.
  { intros z Hz. change (q_foot A1 z) in Hz. destruct (I4 z (QFOOT_sub z Hz)) as [NT NC]. split; [exact NT|].
    intros c' x' Hc' Hx'. fold (cls_of Ap c') in Hx'. destruct (Z.eq_dec c' c) as [EC|NE].
    - subst c'. rewrite ECLS_c in Hx'. cbn [push_cs cs_cache] in Hx'. apply in_app_or in Hx' as [Hx'|Hx'].
      + exact (NC c x' Hc Hx').
      + destruct Hx' as [<-|[]]. exact (QFOOT_slot z Hz).
    - rewrite (ECLS_o c' Hc' NE) in Hx'. exact (NC c' x' Hc' Hx'). }
  split; [exact I5|].
  split.
  { change (qall Ap) with q'. eapply ND_permQ; [|exact I6]. apply Permutation_app_head. exact HQ6. }
  split; [unfold qlarge, large_live in *; change (qall Ap) with q'; change (aa_live Ap) with (aa_live A); rewrite HQ7; exact I7|].
  split; [exact I8 | intros _; exact HCI].
Qed.

Lemma ECLS_mfa : ltac2:(tb__ "0|0|
S0S2S0SfS42S44S43VA;S2aS7A1Vq';A3Vc;Vx;A3R1A2A1SfS42VA;R1A2A1A3Fc';").
Proof.
  intros c'. unfold cls_of, nthZ. rewrite ECLS_raw. destruct (Nat.eq_dec (Z.to_nat c) (Z.to_nat c')) as [E|NE].
  - rewrite <- E. rewrite nth_list_upd_same by (rewrite PLEN; clear -Hc; lia). reflexivity.
  - rewrite nth_list_upd_other by exact NE. reflexivity.
Qed.
Lemma PC_push : ltac2:(tb__ "0|0|
S2S0S75S44S43VA;S2aS7A1Vq';A3Vc;Vx;A3A1S75VA;A1A3").
Proof. apply PrimCreditLaws.prim_credit_maps. intros c' Hc'. split; [exact (proj2 (ECLS_nums c')) | exact (ECLS_mfa c')]. Qed.

Lemma MD_push : ltac2:(tb__ "0|0|
S6bS39S44S43VA;S2aS7A1Vq';A3Vc;Vx;A3Vtp;Vmd;A4").
Proof.
  pose proof HK as (HA & _). destruct HA as (_ & _ & _ & _ & HM & _).
  unfold model_inv in HM |- *. destruct HM as (VG & PB & LIM & V0 & K0' & F0 & TOPm & LED).
  split; [exact VG|]. split; [rewrite PC_push; exact PB|]. split; [exact LIM|]. split; [exact V0|]. split; [exact K0'|]. split; [exact F0|]. split; [exact TOPm|].
  unfold ledger_inv in LED |- *. destruct LED as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9).
  split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. split; [exact L4|]. split; [exact L5|]. split; [exact L6|]. split; [exact L7|].
  split; [exact L8 | exact L9].
Qed.

Theorem K0_push_gen : ltac2:(tb__ "0|0|
S57VKc;S44S43VA;S2aS7A1Vq';A3Vc;Vx;A3Vrho';Vtp;Vtr;Vmd;A6").
Proof.
  pose proof P_facts as (HG & HI3 & HQP & HLS & HPR & HSR & HAU). pose proof HI3 as (H3 & _).
  pose proof HK as (HA & HKc & Htp & Htop & HRG).
  pose proof (view_parts A HG H3 HQP HAU rho rho' (push_zone Gq c kk) PZ_T HOUT HINp tp md HA) as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10).
  split; [|split; [exact HKc|split; [|split]]].
  - unfold AInvQ. cbn zeta. change (aa_geom Ap) with (aa_geom A).
    split; [exact HG|]. split; [exact V1|]. split; [exact V2|]. split; [|split; [exact MD_push | split; [exact I3_push | exact V10]]].
    split; [exact HLS|]. split; [exact V3|]. split; [exact PR_push|]. split; [exact V4|]. split; [exact (conj QP_push V5)|].
    split; [exact V6|]. split; [exact V7|]. split; [exact V8 | exact V9].
  - unfold tp_ok in *. change (aa_geom Ap) with (aa_geom A). rewrite (Hw 24%positive). exact Htp.
  - unfold top_high in *. change (aa_geom Ap) with (aa_geom A). rewrite (Hw 10%positive), (Hw V_DEPTH). exact Htop.
  - destruct HRG as (E1 & E2 & E3 & E4). unfold rigidQ. change (aa_geom Ap) with (aa_geom A). rewrite !Hw. exact (conj E1 (conj E2 (conj E3 E4))).
Qed.
End Push.

Lemma primary_not_large : ltac2:(tb__ "0|0|
S2eS0S0A2S2S2dS5dS32S0S0R1A3A1S30A3S2S2dS1aR2A1S36A3F_;Fit;").
Proof.
  intros it HP. unfold is_large. apply Z.leb_gt. destruct (Z_le_dec 64513 (snd it)) as [L|L]; [|lia].
  rewrite (not_primary_large _ L) in HP. discriminate.
Qed.

Theorem K0_push_item : ltac2:(tb__ "0|b|
S70SbS4fS4fS29S56Q40A1M0A1S29S74A1S73S29S7A1M1G1S0S2eS0S0A2M2S29G2A1S0S0S2G1S18RdA1S2aS7A1M3A3S2G1S17ReA1S28S7R8S2cS7S13R6S2cG2R5R4A3R3A3R7A3A3A3S2S2dSeRfA1S30A3S2S2dS5dS32S0S0R7A3A1S30A3S8R11A1ScS53R9A1S0S54R2RaA2S0S21S2bS0S9S42R14R2A2A1A2A1S0S22R1S5fR3A1A2S1S2G0S4dR15R1A2S4dR16R1A2A3Fi;S1S2S29S56Q8A1M4A1S4eR16R1A2S4eR17R1A2A3Fl;S0S4S45R19R1A2A1S4S47R9R8R6R2A4A1S2S2fG4A1M5S3aS39S4cR19A1M6R3A3S3aS39S4cR1aA1M7R3A3M8A3F_;F_;Fz;S0S45R1aR1A2S4S2G5S3aS39G7R2A3S31G4A1M9A3A1S4S2G5G8G9A3A1F_;F_;Fz;S3bS3aS39S4cR18A1A2S3cS46R9R8A2U4MaS1fR6Z1A2A3A2S3bS3aS39G6A2S3cS1fS1fS46RaR9A2Z10A2S23Z4R7A2A2GaR8A3A2S57R1dR1cR1bR19R18R17A6S57R1eS44S43R1dG3S28S7R17S2cS7S13R15R13R11A3R16A3A3A3RbRaA3R1bR1aR19R18A6F_;F_;F_;F_;F_;F_;F_;F_;Tk;Tx;Tc;TG;F_;F_;F_;F_;Fs';Fs;Fi2;Fit;Fa;Fg2;Fg1;Fmd;Ftr;Ftp;Frho';Frho;FA;FKc;").
Proof.
  intros Kc A rho rho' tp tr md g1 g2 a it i2 s s' HT HGL HCI HP G c x k Hk Hw Hl HOUT HIN HC1 HC2 HK. subst G.
  assert (EQA : qall A = g1 ++ mkQB a (it :: i2) s :: g2) by (unfold qall; rewrite HT, HGL; reflexivity).
  pose proof HK as (HA & _). pose proof HA as (HG & _ & _ & HRest & _ & HI3 & _). cbn zeta in HRest.
  destruct HRest as (_ & _ & R3 & _ & (R5 & _) & _). pose proof HI3 as (H3 & _).
  assert (HAU : forall c', 1 <= c' <= 30 -> 0 <= cs_allocated_user (cls_of A c') <= kUserSpaceSize).
  { intros c' Hc'. destruct R3 as (_ & _ & _ & P4). pose proof (P4 c' Hc') as HC. unfold class_repr in HC. cbn zeta in HC.
    destruct HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & N2 & N3 & _). unfold cls_of, kUserMapSize in *. lia. }
  assert (Hit : In it (qitems (qall A))) by (rewrite EQA, qitems_mid; apply in_or_app; right; left; reflexivity).
  pose proof (item_slot A R5 HAU HG it Hit HP) as IS. cbv zeta in IS. fold c in IS.
  destruct IS as (C1 & RB1 & M1 & U1 & A16 & Z1 & Z2 & RZ & RZ16 & EU & UN & N1 & HS & TOP).
  pose proof R5 as [QF QN]. rewrite EQA in QF, QN.
  apply (K0_push_gen Kc A rho rho' tp tr md (g1 ++ mkQB a i2 s' :: g2) c x HK HCI C1 Hk Hw HOUT HIN HC1 HC2).
  -
    apply Forall_app in QF as [QF1 QF2]. inversion QF2 as [|? ? QB QF3]; subst. apply Forall_app. split; [exact QF1|]. constructor; [|exact QF3].
    unfold batch_pure in QB |- *. cbn [qb_addr qb_items] in QB |- *. destruct QB as (B1 & B2 & B3 & B4). split; [exact B1|]. split; [cbn [length] in B2; clear -B2; lia|]. split; [exact B3|].
    inversion B4; subst; assumption.
  - rewrite map_app in QN |- *. cbn [map qb_addr] in QN |- *. exact QN.
  - intros c' Hc'. rewrite EQA. pose proof (q_ids_pop_item (aa_geom A) g1 g2 a it i2 s s' c') as P. rewrite HP in P. cbn [andb] in P. fold c in P.
    rewrite (Z.eqb_sym c' c). exact P.
  - intros b' Hb'. apply in_app_or in Hb' as [Hb'|[<-|Hb']].
    + exists b'. split; [rewrite EQA; apply in_or_app; left; exact Hb' | split; [reflexivity | intros it0 H0; exact H0]].
    + exists (mkQB a (it :: i2) s). split; [rewrite EQA; apply in_or_app; right; left; reflexivity | split; [reflexivity | intros it0 H0; right; exact H0]].
    + exists b'. split; [rewrite EQA; apply in_or_app; right; right; exact Hb' | split; [reflexivity | intros it0 H0; exact H0]].
  - rewrite EQA, !qitems_mid. cbn [qb_items]. rewrite !List.filter_app. cbn [List.filter]. rewrite HP. cbn [negb]. apply Permutation_refl.
  - unfold qlarge. rewrite EQA, !qitems_mid. cbn [qb_items]. rewrite !List.filter_app. cbn [List.filter]. rewrite (primary_not_large it HP). reflexivity.
  -
    assert (EX : Z.shiftl x kCompactPtrScale = it_ab it - (ag_spacebeg (aa_geom A) + c * 2 ^ 32)).
    { unfold x, it_id, ptr_to_compact, kCompactPtrScale, region_beg, kRegionSize. fold c. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16.
      assert (M16 : (it_ab it - (ag_spacebeg (aa_geom A) + c * 2 ^ 32)) mod 16 = 0).
      { destruct (proj1 (Z.mod_divide _ (Size c) ltac:(lia)) M1) as [j Hj]. destruct (proj1 (Z.mod_divide (Size c) 16 ltac:(lia)) Z2) as [j2 Hj2].
        apply Z.mod_divide; [lia|]. exists (j * j2). rewrite Hj, Hj2. ring. }
      pose proof (Z.div_mod (it_ab it - (ag_spacebeg (aa_geom A) + c * 2 ^ 32)) 16 ltac:(lia)) as DM. rewrite M16 in DM. lia. }
    assert (X0 : 0 <= x).
    { unfold x, it_id, ptr_to_compact, kCompactPtrScale, region_beg, kRegionSize. fold c. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_pos; [clear -RB1; lia | lia]. }
    rewrite EX. pose proof R5 as [QF0 _]. rewrite EQA in QF0. apply Forall_app in QF0 as [_ QF2]. inversion QF2 as [|? ? QB _]; subst.
    destruct QB as (_ & _ & _ & B4). inversion B4 as [|? ? IP _]; subst. destruct IP as (_ & _ & IP3 & _). specialize (IP3 HP). cbn zeta in IP3.
    unfold region_beg, kRegionSize in IP3. split; [exact X0|]. split; [exact M1|].
    unfold c, it_cls, it_ab in *. unfold cls_of in *. clear -IP3. lia.
Qed.

Theorem K0_push_batch : ltac2:(tb__ "0|c|
S70SbS4fS4fS29S56Q40A1M0A1S29S74A1S73S29S7A1M1G1S7S2G1S18R9A1S2aS7A1M2A3S2G1S17RaA1S28S7R4S2cS7R2R3A3A3A3S2S29S2eS0S0A2M3A1S10R3A1S2aG3A1A3S2S2dSeRcA1S30A3S8RdA1ScS55R1R6A2S0S21S2bS0S9S42RfZ18M4A2A1A2A1S0S22R1S5fG4A1A2S1S2G0S4dR10R1A2S4dR11R1A2A3Fi;S1S2S29S56Q8A1M5A1S4eR11R1A2S4eR12R1A2A3Fl;S0S4S45R14R1A2A1S4S47R8G4R6R2A4A1S2S2fG5A1M6S3aS39S4cR14A1M7R3A3S3aS39S4cR15A1M8R3A3M9A3F_;F_;Fz;S0S45R15R1A2S4S2G6S3aS39G8R2A3S31G5A1MaA3A1S4S2G6G9GaA3A1F_;F_;Fz;S3bS3aS39S4cR13A1A2S3cS46R8G4A2U4MbS1fR6Z1A2A3A2S3bS3aS39G7A2S3cS1fS1fS46R9G4A2Z10A2S23Z4R7A2A2GbR8A3A2S57R18R17R16R14R13R12A6S57R19S44S43R18G2S28S7R12R11A3A3G4RaA3R16R15R14R13A6F_;F_;F_;F_;F_;F_;F_;F_;Tk;Tx;TG;F_;F_;F_;F_;Fb;Fg2;Fg1;Fmd;Ftr;Ftp;Frho';Frho;FA;FKc;").
Proof.
  intros Kc A rho rho' tp tr md g1 g2 b HT HGL HE HCI G x k Hk Hw Hl HOUT HIN HC1 HC2 HK. subst G.
  assert (EQA : qall A = g1 ++ b :: g2) by (unfold qall; rewrite HT, HGL; reflexivity).
  pose proof HK as (HA & _). pose proof HA as (HG & _ & _ & HRest & _ & HI3 & _). cbn zeta in HRest.
  destruct HRest as (_ & _ & R3 & _ & (R5 & _) & _).
  pose proof R5 as [QF QN]. rewrite EQA in QF, QN.
  apply (K0_push_gen Kc A rho rho' tp tr md (g1 ++ g2) 24 x HK HCI ltac:(lia) Hk Hw HOUT HIN HC1 HC2).
  - apply Forall_app in QF as [QF1 QF2]. inversion QF2; subst. apply Forall_app. split; assumption.
  - rewrite map_app in QN |- *. cbn [map] in QN.
    pose proof (ND_permQ _ _ (Permutation_middle (map qb_addr g1) (map qb_addr g2) (qb_addr b)) QN) as QN'.
    exact (NoDup_app_r [qb_addr b] _ QN').
  - intros c' Hc'. rewrite EQA. exact (q_ids_pop_batch (aa_geom A) g1 g2 b c' HE).
  - intros b' Hb'. exists b'. split; [rewrite EQA; apply in_app_or in Hb' as [Hb'|Hb']; apply in_or_app; [left | right; right]; exact Hb' | split; [reflexivity | intros it0 H0; exact H0]].
  - rewrite EQA, qitems_mid, HE. cbn [app]. replace (qitems g1 ++ qitems g2) with (qitems (g1 ++ g2)) by (unfold qitems; apply flat_map_app). apply Permutation_refl.
  - unfold qlarge. rewrite EQA, qitems_mid, HE. cbn [app]. replace (qitems g1 ++ qitems g2) with (qitems (g1 ++ g2)) by (unfold qitems; apply flat_map_app). reflexivity.
  - apply Forall_app in QF as [_ QF2]. inversion QF2 as [|? ? QB _]; subst. destruct QB as (_ & _ & (y & E & Y0 & YM & Y1) & _).
    assert (EX : x = y).
    { unfold x, qb_id, ptr_to_compact, kCompactPtrScale. rewrite E. replace (region_beg (ag_spacebeg (aa_geom A)) 24 + 16 * y - region_beg (ag_spacebeg (aa_geom A)) 24) with (y * 2 ^ 4) by lia.
      rewrite Z.shiftr_div_pow2, Z.div_mul by lia. reflexivity. }
    clearbody x. subst x. unfold kCompactPtrScale. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16. change (Size 24) with 8192. unfold kQuarantineBatchSize in Y1.
    split; [exact Y0|]. split; [|clear -Y1; lia].
    apply Z.mod_divide; [lia|]. destruct (proj1 (Z.mod_divide y 512 ltac:(lia)) YM) as [j Hj]. exists j. clear -Hj. lia.
Qed.

Theorem K0_laws : ltac2:(tb__ "0|0|
S70S71R1A1S4aS39S57R2A1A2F_;FKc;").
Proof.
  intros Kc HKc. constructor.
  - intros A. exact (K0_stable Kc A HKc).
  - intros A rho tp tr md H. exact (K0_facts Kc A rho tp tr md H).
  - intros A rho rho' tp tr md Hw Hl HO HI H. exact (K0_view Kc A rho rho' tp tr md Hw Hl HO HI H).
  - intros A t g rho tp tr md P H. exact (K0_perm Kc A t g rho tp tr md P H).
  - intros A rho rho' tp tr md g1 g2 a it i2 s s'. exact (K0_push_item Kc A rho rho' tp tr md g1 g2 a it i2 s s').
  - intros A rho rho' tp tr md g1 g2 b. exact (K0_push_batch Kc A rho rho' tp tr md g1 g2 b).
Qed.
End InvQ4.

(* [comment removed for export] *)
Module SpineMallocE.

From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundR SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildM SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocS9.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.GlueMZ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SpineMallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineMallocS7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineMallocS8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocS9.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section E.
Variable nW : nat. Variable st : ustop. Variable tmax : Z.
Let W : list ulink := Wcan nW.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : forall a, in_rangesZ CST a -> in_rangesZ IMG_M a -> False.
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let J (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) : jpredA := J_alloc_preT AInv W st A Kc (SVar 12).
Hypothesis law_die : forall A rho tp md, AInv A rho tp md -> cell_ok (view segs (rm rho)) (mkACell 0x17fbdc 4 0).

Lemma ecfg_cut : forall fuel cutpcs g (cuts exits : list vnodeA) (Jx : jpredA) (Q : world -> Prop) tp (C : axst) rho,
  stableA segs g Jx ->
  (forall n, In n cuts -> (g <= ss_next (ax_S (vna_state n)))%positive) ->
  check_ecfgA segs fuel cutpcs g cuts exits = true ->
  (forall E rho', In E exits ->
     etriple segs (SPA segs Jx (vna_state E) rho' tp) (fun w => SPfamEA segs (map (to_enodeA Jx) cuts) tp (vmeasA E rho') w \/ Q w)) ->
  In (mkVNA C 1 (SLit 0)) cuts ->
  etriple segs (SPA segs Jx C rho tp) Q.
Proof. intros fuel cutpcs g cuts exits Jx Q tp C rho HS HN HC HE HI. exact (cfg_complete_autoA segs fuel cutpcs g cuts exits Jx Q tp HS HN HC HE (mkVNA C 1 (SLit 0)) rho HI). Qed.

Section ECall.
Variables (Cst T D : axst) (s : wsub) (R : list sobj) (sd : wsub).
Variables (Pre : axst) (Posts : list leafA) (Pret : sstate).
Hypothesis HPosts : Posts = [mkLeafA (liftA Pret) RsSymJump].
Hypothesis Hsum : forall (Jx : jpredA) rho tp, stableA Code.segs NF Jx -> etriple Code.segs (SPA Code.segs Jx Pre rho tp) (LQA Code.segs Jx NF rho tp Posts).
Hypothesis He : entails_frA Cst Pre s = Some R.
Hypothesis Hchk : call_checkA Cst Pre s R (map la_state Posts) = true.
Hypothesis HT : import_postA s Pre (liftA Pret) Cst R = T.
Hypothesis FBC : forallb (sprop_below (ss_next (ax_S Cst))) (ss_facts (ax_S Cst)) = true.
Hypothesis FBT : forallb (sprop_below (ss_next (ax_S T))) (ss_facts (ax_S Cst)) = true.
Hypothesis ENT : entailsA (ax_with_facts T (ss_facts (ax_S Cst))) D sd = true.
Hypothesis SID : wsub_id_below sd GW = true.
Hypothesis NXC : (GW <= ss_next (ax_S Cst))%positive.
Hypothesis NPre : ss_next (ax_S Pre) = NF.

Lemma ecall_gen : forall A Kc rho tp rhoE (Q : world -> Prop),
  stopJ_stable W st -> Kc_ok Kc ->
  (forall rhoX tpX, etriple segs (SPA segs (JGb W st A Kc rho) D rhoX tpX) Q) ->
  etriple segs (SPA segs (JGb W st A Kc rho) Cst rhoE tp) Q.
Proof.
  intros A Kc rho tp rhoE Q HUS HKc HD.
  pose proof (JGb_stable nW st A Kc rho HUS HKc) as HST.
  set (Jf := (fun (_ : valuation) t tr md => JGb W st A Kc rho rhoE t tr md) : jpredA).
  assert (Jf_st : stableA segs NF Jf).
  { intros r r' t tr md md' Hag Hme HJ. unfold Jf in *. eapply HST; [apply agree_below_refl | exact Hme | exact HJ]. }
  apply (etriple_pre_pure segs _ _ (Forall (holds rhoE) (ss_facts (ax_S Cst)))).
  { intros w Hw. exact (SPA_facts_hold segs _ rhoE Cst tp w Hw). }
  intros HFC.
  apply (call_completeA segs (JGb W st A Kc rho) Jf Jf (JGb W st A Kc rho) Cst Pre s R Posts Q rhoE tp He Hchk).
  - intros rho1 tp1. rewrite NPre. exact (Hsum Jf rho1 tp1 Jf_st).
  - intros tr ms md Hsm HJ. exact HJ.
  - intros L rho' rhoL tpL tr ms md tr' md' HinL Hsm HJ HLK HJ'. unfold Jf in HJ'.
    eapply HST; [| apply mat_equiv_refl | exact HJ'].
    eapply agree_below_le; [exact NXC | exact (proj1 HLK)].
  - intros L rho' tpL HinL Hag. rewrite HPosts in HinL. destruct HinL as [<-|[]]. cbn [la_state]. rewrite HT.
    eapply etriple_conseq; [intros w Hw | intros w Hw; exact Hw | apply (HD (rho_sub rho' sd) tpL)].
    apply (SPA_entails0 segs (JGb W st A Kc rho) GW (ax_with_facts T (ss_facts (ax_S Cst))) D sd rho' tpL w ENT SID HST).
    apply SPA_refacts; [exact Hw | exact FBT |]. intros _.
    exact (Forall_holds_agree _ rhoE rho' _ Hag FBC HFC).
Qed.
End ECall.

Section E_spine_s1.
Hypothesis WC1 : swf (ax_S (C1g W st tmax)) = true.
Hypothesis DC1 : forall k, 0 <= k <= 7 -> state_diff (ax_S (E_s1 W st tmax k)) (ax_S (C1g W st tmax)) = Some (d_k k, F_gen).
Hypothesis Cert1 : check_cfgA segsA 4000%nat [0x40bac] GW (s1_cuts nW st) (s1_exits nW st tmax) = true.

Hypothesis NXhi : (GW <= ss_next (ax_S (P0_s1 W st F_hi)))%positive.
Hypothesis NXlo : (GW <= ss_next (ax_S (P0_s1 W st F_lo)))%positive.
Hypothesis ECert1 : check_ecfgA segsA 4000%nat [0x40bac] GW (map (fun c => mkVNA c 1 (SLit 0)) (s1_cuts nW st)) (map (fun e => mkVNA e 0 (SLit 0)) (s1_exits nW st tmax)) = true.
Theorem espine_s1 : forall (A : AA) (Kc : KcA) rho tp (Q : world -> Prop),
  (st = UStopLeOrPc -> W = []) -> stopJ_stable W st -> Kc_ok Kc ->
  swf (sa_m W st) = true -> state_diff (ax_S (Pre_mallocI AE_A W st)) (sa_m W st) = Some ([(SVar 24, SLit TP_A)], []) ->
  swf (sb_m W st) = true ->
  forallb (sprop_below NW2) ((((unwind_factsS W st ++ pre_facts malloc_depth) ++ F_geom_fn) ++ F_s1) ++ F_hi) = true ->
  forallb (sprop_below NW2) ((((unwind_factsS W st ++ pre_facts malloc_depth) ++ F_geom_fn) ++ F_s1) ++ F_lo) = true ->
  (forall rhoE, etriple segs (SPA segs (JG W st A Kc rho) (C1g W st tmax) rhoE tp) Q) ->
  (forall rhoE, etriple segs (SPA segs (JG W st A Kc rho) (E_s1 W st tmax 8) rhoE tp) Q) ->
  etriple segs (SPA segs (J W st A Kc) (Pre_mallocI AE_A W st) rho tp) Q.
Proof.
  intros A Kc rho tp Q HW HUS HKc Wa Da Wb Fbh Fbl HC1 HSEC.
  eapply etriple_conseq; [intros w Hw; exact (m_instantiate law_die W st A Kc rho tp w HW HUS Wa Da Wb Fbh Fbl Hw) | intros w Hw; exact Hw |].
  set (P0 := P0_s1 W st (if Z_lt_dec (bv_unsigned (rw rho 12%positive)) 64513 then F_lo else F_hi)).
  eapply etriple_conseq; [intros w Hw; exact (SPA_withG_intro segs _ GW P0 (rhoM_of A rho) tp w Hw) | intros w Hw; exact Hw |].
  apply (ecfg_cut 4000%nat [0x40bac] GW (map (fun c => mkVNA c 1 (SLit 0)) (s1_cuts nW st)) (map (fun e => mkVNA e 0 (SLit 0)) (s1_exits nW st tmax))
           (JG W st A Kc rho) Q tp P0 _ (JG_stable nW st A Kc rho HUS HKc)).
  - intros n Hn. unfold s1_cuts in Hn. cbn [map] in Hn. destruct Hn as [<-|[<-|[]]]; cbn [vna_state]; [exact NXhi | exact NXlo].
  - exact ECert1.
  - intros E rhoE HinE. clear NXhi NXlo ECert1. unfold s1_exits in HinE. cbn [map] in HinE.
    destruct HinE as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]; cbn [vna_state].
    9: { eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | apply HSEC]. }
    all: eapply etriple_conseq; [intros w Hw; eapply (e_s1_c1g nW st tmax WC1 DC1 _ A Kc rho tp w rhoE); [|exact Hw]; lia | intros w Hw; right; exact Hw | apply HC1].
  - unfold s1_cuts, P0. cbn [map]. destruct (Z_lt_dec _ _); [right; left; reflexivity | left; reflexivity].
Qed.
End E_spine_s1.

Section E_spine_s2.
Let Xa : axst := ax_setS (E2a W st tmax) (ax_S (E2a' nW st tmax)).
Let Xb : axst := ax_setS (E2b W st tmax) (ax_S (E2b' nW st tmax)).
Hypothesis Cert2 : check_cfgA segsA 4000%nat [0x40d40] GW [C1g W st tmax] [E2a W st tmax; E2b W st tmax] = true.
Hypothesis OVa : only_var 157 (creg_a W st tmax) = true.
Hypothesis OVb : only_var 157 (creg_b W st tmax) = true.
Hypothesis TABa : tab_ok 157 (creg_a W st tmax) ClassID 520 8128%nat = true.
Hypothesis TABb : tab_ok 157 (creg_b W st tmax) ClassID 24 62%nat = true.
Hypothesis Wa' : swf (ax_S (E2a' nW st tmax)) = true.
Hypothesis Wb' : swf (ax_S (E2b' nW st tmax)) = true.
Hypothesis Da' : state_diff (ax_S (E2a W st tmax)) (ax_S (E2a' nW st tmax)) = Some ([(creg_a W st tmax, SVar V_CLS)], []).
Hypothesis Db' : state_diff (ax_S (E2b W st tmax)) (ax_S (E2b' nW st tmax)) = Some ([(creg_b W st tmax, SVar V_CLS)], []).
Hypothesis NXa : ss_next (ax_S (E2a' nW st tmax)) = ss_next (ax_S (E2a W st tmax)).
Hypothesis NXb : ss_next (ax_S (E2b' nW st tmax)) = ss_next (ax_S (E2b W st tmax)).
Hypothesis Fa : In (SPBranch BC_LTU (SLit 512) (SVar V_ND)) (ss_facts (ax_S (E2a W st tmax))).
Hypothesis Fb : In (SPNot (SPBranch BC_LTU (SLit 512) (SVar V_ND))) (ss_facts (ax_S (E2b W st tmax))).
Hypothesis Ga : incl F_gen (ss_facts (ax_S (E2a W st tmax))).
Hypothesis Gb : incl F_gen (ss_facts (ax_S (E2b W st tmax))).
Hypothesis SKa : map skel (ss_objs (ax_S Xa)) = map skel (((sw_s1 :: unwind_objs W ++ A_globals) ++ RT_m1)).
Hypothesis SKb : map skel (ss_objs (ax_S Xb)) = map skel (((sw_s1 :: unwind_objs W ++ A_globals) ++ RT_m1)).
Hypothesis XXa : ax_X Xa = [].
Hypothesis XXb : ax_X Xb = [].
Hypothesis XFa : incl (((unwind_factsS W st ++ pre_facts malloc_depth) ++ F_s1) ++ F_gen) (ss_facts (ax_S Xa)).
Hypothesis XFb : incl (((unwind_factsS W st ++ pre_facts malloc_depth) ++ F_s1) ++ F_gen) (ss_facts (ax_S Xb)).
Hypothesis W1a : swf (ax_S (X1 Xa)) = true.
Hypothesis W1ba : swf (ax_S (X1b Xa)) = true.
Hypothesis W1ca : swf (ax_S (X1c Xa)) = true.
Hypothesis W2a : swf (ax_S (X2 Xa)) = true.
Hypothesis W1ra : swf (ax_S (X1r Xa)) = true.
Hypothesis W2ra : swf (ax_S (X2r Xa)) = true.
Hypothesis W1b : swf (ax_S (X1 Xb)) = true.
Hypothesis W1bb : swf (ax_S (X1b Xb)) = true.
Hypothesis W1cb : swf (ax_S (X1c Xb)) = true.
Hypothesis W2b : swf (ax_S (X2 Xb)) = true.
Hypothesis W1rb : swf (ax_S (X1r Xb)) = true.
Hypothesis W2rb : swf (ax_S (X2r Xb)) = true.
Variables sa sra sb srb : wsub.
Hypothesis ENTa : entailsA (X2 Xa) (C2p0 W st tmax) sa = true.
Hypothesis ENTra : entailsA (X2r Xa) (C2r0 W st tmax) sra = true.
Hypothesis ENTb : entailsA (X2 Xb) (C2p0 W st tmax) sb = true.
Hypothesis ENTrb : entailsA (X2r Xb) (C2r0 W st tmax) srb = true.
Hypothesis SIDa : wsub_id_below sa GW = true.
Hypothesis SIDra : wsub_id_below sra GW = true.
Hypothesis SIDb : wsub_id_below sb GW = true.
Hypothesis SIDrb : wsub_id_below srb GW = true.
Hypothesis FB : forallb (sprop_below (ss_next (ax_S (C2p0 W st tmax)))) (F_cls ++ F_pop) = true.
Hypothesis FBr : forallb (sprop_below (ss_next (ax_S (C2r0 W st tmax)))) F_cls = true.

Hypothesis NXC1g : (GW <= ss_next (ax_S (C1g W st tmax)))%positive.
Hypothesis ECert2 : check_ecfgA segsA 4000%nat [0x40d40] GW [mkVNA (C1g W st tmax) 1 (SLit 0)] [mkVNA (E2a W st tmax) 0 (SLit 0); mkVNA (E2b W st tmax) 0 (SLit 0)] = true.
Theorem espine_s2 : forall (A : AA) (Kc : KcA) rho tp (Q : world -> Prop),
  (st = UStopLeOrPc -> W = []) -> stopJ_stable W st -> Kc_ok Kc ->
  (forall rhoE, etriple segs (SPA segs (JG W st A Kc rho) (C2p W st tmax) rhoE tp) Q) ->
  (forall rhoE, etriple segs (SPA segs (JG W st A Kc rho) (C2r W st tmax) rhoE tp) Q) ->
  forall rhoE, etriple segs (SPA segs (JG W st A Kc rho) (C1g W st tmax) rhoE tp) Q.
Proof.
  intros A Kc rho tp Q HW HUS HKc HP HR rhoE.
  pose proof (Zle_0_nat (length (cs_cache (cst_of A (bv_unsigned (rw rho 12%positive)))))) as Hc0.
  change (0 <= cnt_of A (bv_unsigned (rw rho 12%positive))) in Hc0.
  apply (ecfg_cut 4000%nat [0x40d40] GW [mkVNA (C1g W st tmax) 1 (SLit 0)] [mkVNA (E2a W st tmax) 0 (SLit 0); mkVNA (E2b W st tmax) 0 (SLit 0)] (JG W st A Kc rho) Q tp (C1g W st tmax) _ (JG_stable nW st A Kc rho HUS HKc)).
  - intros n Hn. destruct Hn as [<-|[]]; cbn [vna_state]; first [exact NXC1g].
  - exact ECert2.
  - intros E rhoX HinE. clear NXC1g ECert2. destruct HinE as [<-|[<-|[]]]; cbn [vna_state].
    +
      destruct (Z_lt_dec 0 (cnt_of A (bv_unsigned (rw rho 12%positive)))) as [Hp|Hz].
      * eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HP (rho_sub rhoX sa))].
        apply (b1_pop nW st tmax Xa SKa XXa XFa W1a W1ba W1ca W2a sa sra ENTa SIDa FB ENTra FBr A Kc rho tp w rhoX HW HUS HKc ltac:(lia)).
        exact (class_restate_a nW st tmax OVa TABa Wa' Da' NXa NXb Fa Ga A Kc rho tp w rhoX Hw).
      * eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HR (rho_sub rhoX sra))].
        apply (b1_refill nW st tmax Xa SKa XXa XFa W1ra W2ra sa sra ENTa FB ENTra SIDra FBr A Kc rho tp w rhoX HW HUS HKc ltac:(lia)).
        exact (class_restate_a nW st tmax OVa TABa Wa' Da' NXa NXb Fa Ga A Kc rho tp w rhoX Hw).
    +
      destruct (Z_lt_dec 0 (cnt_of A (bv_unsigned (rw rho 12%positive)))) as [Hp|Hz].
      * eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HP (rho_sub rhoX sb))].
        apply (b1_pop nW st tmax Xb SKb XXb XFb W1b W1bb W1cb W2b sb srb ENTb SIDb FB ENTrb FBr A Kc rho tp w rhoX HW HUS HKc ltac:(lia)).
        exact (class_restate_b nW st tmax OVb TABb Wb' NXa NXb Db' Fb Gb A Kc rho tp w rhoX Hw).
      * eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HR (rho_sub rhoX srb))].
        apply (b1_refill nW st tmax Xb SKb XXb XFb W1rb W2rb sb srb ENTb FB ENTrb SIDrb FBr A Kc rho tp w rhoX HW HUS HKc ltac:(lia)).
        exact (class_restate_b nW st tmax OVb TABb Wb' NXa NXb Db' Fb Gb A Kc rho tp w rhoX Hw).
  - left. reflexivity.
Qed.
End E_spine_s2.

Section E_spine_s3p.
Hypothesis Cert3p : check_cfgA segsA 4000%nat [0x40e58; 0x3c614] GW [C2p W st tmax] [E3p W st tmax] = true.
Hypothesis SKY : map skel (ss_objs (ax_S (E3p W st tmax))) = map skel ((((sw_s1 :: unwind_objs W ++ A_globals) ++ RT_m1) ++ [O_pcc; O_pcs; O_pck; O_st])).
Hypothesis YX : ax_X (E3p W st tmax) = [].
Hypothesis YF : incl (((unwind_factsS W st ++ pre_facts malloc_depth) ++ F_s1) ++ F_gen) (ss_facts (ax_S (E3p W st tmax))).
Hypothesis YP : In (SPUle (SLit 1) (SVar V_CNT)) (ss_facts (ax_S (E3p W st tmax))).
Hypothesis WY1 : swf (ax_S (Y1 (E3p W st tmax))) = true.
Hypothesis WY2 : swf (ax_S (Y2 (E3p W st tmax))) = true.
Hypothesis WY3 : swf (ax_S (Y3 (E3p W st tmax))) = true.
Hypothesis WY4 : swf (ax_S (Y4 (E3p W st tmax))) = true.
Hypothesis WY5 : swf (ax_S (Y5 (E3p W st tmax))) = true.
Hypothesis WY6 : swf (ax_S (Y6 (E3p W st tmax))) = true.
Hypothesis WY7 : swf (ax_S (Y7 (E3p W st tmax))) = true.
Variable s3 : wsub.
Hypothesis ENT3 : entailsA (Y7 (E3p W st tmax)) (C3 W st tmax) s3 = true.
Hypothesis SID3 : wsub_id_below s3 GW = true.

Hypothesis NXC2p : (GW <= ss_next (ax_S (C2p W st tmax)))%positive.
Hypothesis ECert3p : check_ecfgA segsA 4000%nat [0x40e58; 0x3c614] GW [mkVNA (C2p W st tmax) 1 (SLit 0)] [mkVNA (E3p W st tmax) 0 (SLit 0)] = true.
Theorem espine_s3p : forall (A : AA) (Kc : KcA) rho tp (Q : world -> Prop),
  (st = UStopLeOrPc -> W = []) -> stopJ_stable W st -> Kc_ok Kc -> sep_geom (aa_geom A) ->
  (forall rhoE, etriple segs (SPA segs (JG W st A Kc rho) (C3 W st tmax) rhoE tp) Q) ->
  forall rhoE, etriple segs (SPA segs (JG W st A Kc rho) (C2p W st tmax) rhoE tp) Q.
Proof.
  intros A Kc rho tp Q HW HUS HKc HSEP HC rhoE.
  apply (ecfg_cut 4000%nat [0x40e58; 0x3c614] GW [mkVNA (C2p W st tmax) 1 (SLit 0)] [mkVNA (E3p W st tmax) 0 (SLit 0)] (JG W st A Kc rho) Q tp (C2p W st tmax) _ (JG_stable nW st A Kc rho HUS HKc)).
  - intros n Hn. destruct Hn as [<-|[]]; cbn [vna_state]; first [exact NXC2p].
  - exact ECert3p.
  - intros E rhoX HinE. clear NXC2p ECert3p. destruct HinE as [<-|[]]; cbn [vna_state].
    eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC (rho_sub rhoX s3))].
    apply (b3_carve nW st tmax (E3p W st tmax) SKY YX YF WY1 WY2 WY3 WY4 WY5 WY6 WY7 s3 ENT3 SID3 A Kc rho tp w rhoX HW HUS HKc HSEP); [|exact Hw].
    exact (cnt_pos_of_fact nW st A Kc rho rhoX tp w _ Hw YP).
  - left. reflexivity.
Qed.
End E_spine_s3p.

Section E_spine_s3r.
Hypothesis Cert3r : check_cfgA segsA 4000%nat [0x40e58; 0x3c614] GW [C2r W st tmax] [E3r W st tmax] = true.

Hypothesis NXC2r : (GW <= ss_next (ax_S (C2r W st tmax)))%positive.
Hypothesis ECert3r : check_ecfgA segsA 4000%nat [0x40e58; 0x3c614] GW [mkVNA (C2r W st tmax) 1 (SLit 0)] [mkVNA (E3r W st tmax) 0 (SLit 0)] = true.
Theorem espine_s3r : forall (A : AA) (Kc : KcA) rho tp (Q : world -> Prop),
  stopJ_stable W st -> Kc_ok Kc ->
  (forall rhoE, etriple segs (SPA segs (JG W st A Kc rho) (E3r W st tmax) rhoE tp) Q) ->
  forall rhoE, etriple segs (SPA segs (JG W st A Kc rho) (C2r W st tmax) rhoE tp) Q.
Proof.
  intros A Kc rho tp Q HUS HKc HR rhoE.
  apply (ecfg_cut 4000%nat [0x40e58; 0x3c614] GW [mkVNA (C2r W st tmax) 1 (SLit 0)] [mkVNA (E3r W st tmax) 0 (SLit 0)] (JG W st A Kc rho) Q tp (C2r W st tmax) _ (JG_stable nW st A Kc rho HUS HKc)).
  - intros n Hn. destruct Hn as [<-|[]]; cbn [vna_state]; first [exact NXC2r].
  - exact ECert3r.
  - intros E rhoX HinE. clear NXC2r ECert3r. destruct HinE as [<-|[]]; cbn [vna_state].
    eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | apply HR].
  - left. reflexivity.
Qed.
End E_spine_s3r.

Definition HDE_stmt (keep : Z -> Prop) (A : AA) (Kc : KcA) (rho : valuation) (Q : world -> Prop) : Prop :=
  forall rhoE tp,
    (forall A' rho' rhoX tp', depot_onlyK A A' -> hd_link keep rho rho' ->
       etriple segs (SPA segs (JGb W st A' Kc rho') (C5 W st tmax) rhoX tp') Q) ->
    etriple segs (SPA segs (JG W st A Kc rho) (E4d W st tmax) rhoE tp) Q.
Section E_spine_s4.
Hypothesis Cert4 : check_cfgA segsA 4000%nat [0x7e9e4] GW [C3 W st tmax] [E4d W st tmax] = true.

Hypothesis NXC3 : (GW <= ss_next (ax_S (C3 W st tmax)))%positive.
Hypothesis ECert4 : check_ecfgA segsA 4000%nat [0x7e9e4] GW [mkVNA (C3 W st tmax) 1 (SLit 0)] [mkVNA (E4d W st tmax) 0 (SLit 0)] = true.
Theorem espine_s4 : forall keep (A : AA) (Kc : KcA) rho tp (Q : world -> Prop),
  stopJ_stable W st -> Kc_ok Kc ->
  HDE_stmt keep A Kc rho Q ->
  (forall A' rho' rhoX tp', depot_onlyK A A' -> hd_link keep rho rho' ->
     etriple segs (SPA segs (JGb W st A' Kc rho') (C5 W st tmax) rhoX tp') Q) ->
  forall rhoE, etriple segs (SPA segs (JG W st A Kc rho) (C3 W st tmax) rhoE tp) Q.
Proof.
  intros keep A Kc rho tp Q HUS HKc HD HC rhoE.
  apply (ecfg_cut 4000%nat [0x7e9e4] GW [mkVNA (C3 W st tmax) 1 (SLit 0)] [mkVNA (E4d W st tmax) 0 (SLit 0)] (JG W st A Kc rho) Q tp (C3 W st tmax) _ (JG_stable nW st A Kc rho HUS HKc)).
  - intros n Hn. destruct Hn as [<-|[]]; cbn [vna_state]; first [exact NXC3].
  - exact ECert4.
  - intros E rhoX HinE. clear NXC3 ECert4. destruct HinE as [<-|[]]; cbn [vna_state].
    eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | apply HD; exact HC].
  - left. reflexivity.
Qed.
End E_spine_s4.

Section E_spine_s5.
Hypothesis Cert5 : check_cfgA segsA 4000%nat [0x3c774; 0x3c80c] GW [C5 W st tmax] [E5n W st tmax; E5f W st tmax] = true.
Variable s6n : wsub.
Hypothesis ENT6n : entailsA (E5n W st tmax) (C6 W st tmax) s6n = true.
Hypothesis SID6n : wsub_id_below s6n GW = true.
Hypothesis W5b : swf (ax_S (C5b W st tmax)) = true.
Hypothesis D5b : state_diff (ax_S (E5f W st tmax)) (ax_S (C5b W st tmax)) = Some ([(clsp_e31, SVar V_CLS); (clsp_e, SVar V_CLS)], []).
Hypothesis NX5b : ss_next (ax_S (C5b W st tmax)) = ss_next (ax_S (E5f W st tmax)).
Hypothesis F5f64 : In (SPUle (SVar 12) (SLit 64512)) (ss_facts (ax_S (E5f W st tmax))).

Hypothesis NXC5 : (GW <= ss_next (ax_S (C5 W st tmax)))%positive.
Hypothesis ECert5 : check_ecfgA segsA 4000%nat [0x3c774; 0x3c80c] GW [mkVNA (C5 W st tmax) 1 (SLit 0)] [mkVNA (E5n W st tmax) 0 (SLit 0); mkVNA (E5f W st tmax) 0 (SLit 0)] = true.
Theorem espine_s5 : forall (A : AA) (Kc : KcA) rho tp (Q : world -> Prop),
  stopJ_stable W st -> Kc_ok Kc ->
  1 <= cnt_of A (bv_unsigned (rw rho 12%positive)) ->
  (forall rhoX, etriple segs (SPA segs (JGb W st A Kc rho) (C6 W st tmax) rhoX tp) Q) ->
  (forall rhoX, etriple segs (SPA segs (JGb W st A Kc rho) (C5b W st tmax) rhoX tp) Q) ->
  forall rhoE, etriple segs (SPA segs (JGb W st A Kc rho) (C5 W st tmax) rhoE tp) Q.
Proof.
  intros A Kc rho tp Q HUS HKc Hcnt H6 H5b rhoE.
  apply (ecfg_cut 4000%nat [0x3c774; 0x3c80c] GW [mkVNA (C5 W st tmax) 1 (SLit 0)] [mkVNA (E5n W st tmax) 0 (SLit 0); mkVNA (E5f W st tmax) 0 (SLit 0)] (JGb W st A Kc rho) Q tp (C5 W st tmax) _ (JGb_stable nW st A Kc rho HUS HKc)).
  - intros n Hn. destruct Hn as [<-|[]]; cbn [vna_state]; first [exact NXC5].
  - exact ECert5.
  - intros E rhoX HinE. clear NXC5 ECert5. destruct HinE as [<-|[<-|[]]]; cbn [vna_state].
    +
      eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (H6 (rho_sub rhoX s6n))].
      apply (SPA_entails0 segs (JGb W st A Kc rho) GW (E5n W st tmax) (C6 W st tmax) s6n rhoX tp w ENT6n SID6n); [|exact Hw].
      apply JGb_stable; [exact HUS | exact HKc].
    +
      eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (H5b rhoX)].
      destruct w as [tr [ms md]].
      pose proof (JGb_rigid nW st A Kc rho rhoX tp tr md (proj2 Hw)) as (E12 & E148 & E149 & E150 & E158 & E159).
      destruct (JGb_model nW st A Kc rho rhoX tp tr md (proj2 Hw)) as [HA HN].
      pose proof (fact_of_stateB nW st A Kc rho rhoX tp _ _ _ Hw F5f64) as F64. cbn [holds eval] in F64. rewrite E12, u64_lit in F64 by lia.
      set (nv := bv_unsigned (rw rho 12%positive)) in HA, HN, F64, E148, E149, E150, E158, E159, Hcnt |- *.
      pose proof (cls_facts nv ltac:(lia)) as (C1 & _ & _ & _).
      pose proof (pc_entry_facts segs A rhoX tp md nv HA ltac:(lia) Hcnt) as PF. cbn zeta in PF. destruct PF as (_ & _ & _ & _ & _ & Hch & _ & _).
      destruct (clsp_eval rhoX (cls_of nv) (chk_of A nv) E158 E159 ltac:(lia) Hch) as [EV1 EV2].
      unfold C5b, upd. lazy zeta. eapply SPA_restate; [exact W5b | exact D5b | exact NX5b | | constructor | exact Hw].
      unfold diffs_ok. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; unfold V_CLS; cbn [eval]; rewrite ?EV1, ?EV2, E158; reflexivity.
  - left. reflexivity.
Qed.
End E_spine_s5.

Section E_spine_s5b.
Hypothesis Cert5b : check_cfgA segsA 4000%nat [0x3c7e0] GW [C5b W st tmax] [E5s1 W st tmax; E5s2 W st tmax] = true.
Hypothesis OV1 : only_var 158 (sreg1 W st tmax) = true.
Hypothesis OV2 : only_var 158 (sreg2 W st tmax) = true.
Hypothesis TAB1 : tab1_ok 158 (sreg1 W st tmax) Size 17 14%nat = true.
Hypothesis TAB2 : tab1_ok 158 (sreg2 W st tmax) Size 1 16%nat = true.
Hypothesis W1' : swf (ax_S (E5s1' nW st tmax)) = true.
Hypothesis W2' : swf (ax_S (E5s2' nW st tmax)) = true.
Hypothesis D1' : state_diff (ax_S (E5s1 W st tmax)) (ax_S (E5s1' nW st tmax)) = Some ([(sreg1 W st tmax, SVar V_SIZE)], []).
Hypothesis D2' : state_diff (ax_S (E5s2 W st tmax)) (ax_S (E5s2' nW st tmax)) = Some ([(sreg2 W st tmax, SVar V_SIZE)], []).
Hypothesis NX1' : ss_next (ax_S (E5s1' nW st tmax)) = ss_next (ax_S (E5s1 W st tmax)).
Hypothesis NX2' : ss_next (ax_S (E5s2' nW st tmax)) = ss_next (ax_S (E5s2 W st tmax)).
Hypothesis F1gt : In (SPBranch BC_LTU (SLit 16) (SVar V_CLS)) (ss_facts (ax_S (E5s1 W st tmax))).
Hypothesis F2le : In (SPNot (SPBranch BC_LTU (SLit 16) (SVar V_CLS))) (ss_facts (ax_S (E5s2 W st tmax))).
Hypothesis F1_64 : In (SPUle (SVar 12) (SLit 64512)) (ss_facts (ax_S (E5s1 W st tmax))).
Hypothesis F2_64 : In (SPUle (SVar 12) (SLit 64512)) (ss_facts (ax_S (E5s2 W st tmax))).
Variables s1 s2 : wsub.
Hypothesis ENT1 : entailsA (E5s1' nW st tmax) (C5c W st tmax) s1 = true.
Hypothesis ENT2 : entailsA (E5s2' nW st tmax) (C5c W st tmax) s2 = true.
Hypothesis SID1 : wsub_id_below s1 GW = true.
Hypothesis SID2 : wsub_id_below s2 GW = true.

Hypothesis NXC5b : (GW <= ss_next (ax_S (C5b W st tmax)))%positive.
Hypothesis ECert5b : check_ecfgA segsA 4000%nat [0x3c7e0] GW [mkVNA (C5b W st tmax) 1 (SLit 0)] [mkVNA (E5s1 W st tmax) 0 (SLit 0); mkVNA (E5s2 W st tmax) 0 (SLit 0)] = true.
Theorem espine_s5b : forall (A : AA) (Kc : KcA) rho tp (Q : world -> Prop),
  stopJ_stable W st -> Kc_ok Kc ->
  (forall rhoX, etriple segs (SPA segs (JGb W st A Kc rho) (C5c W st tmax) rhoX tp) Q) ->
  forall rhoE, etriple segs (SPA segs (JGb W st A Kc rho) (C5b W st tmax) rhoE tp) Q.
Proof.
  intros A Kc rho tp Q HUS HKc HC rhoE.
  apply (ecfg_cut 4000%nat [0x3c7e0] GW [mkVNA (C5b W st tmax) 1 (SLit 0)] [mkVNA (E5s1 W st tmax) 0 (SLit 0); mkVNA (E5s2 W st tmax) 0 (SLit 0)] (JGb W st A Kc rho) Q tp (C5b W st tmax) _ (JGb_stable nW st A Kc rho HUS HKc)).
  - intros n Hn. destruct Hn as [<-|[]]; cbn [vna_state]; first [exact NXC5b].
  - exact ECert5b.
  - intros E rhoX HinE. clear NXC5b ECert5b. destruct HinE as [<-|[<-|[]]]; cbn [vna_state].
    + eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC (rho_sub rhoX s1))].
      destruct w as [tr [ms md]].
      pose proof (JGb_rigid nW st A Kc rho rhoX tp tr md (proj2 Hw)) as (E12 & E148 & E149 & E150 & E158 & E159).
      destruct (JGb_model nW st A Kc rho rhoX tp tr md (proj2 Hw)) as [HA HN].
      pose proof (fact_of_stateB nW st A Kc rho rhoX tp _ _ _ Hw F1_64) as F64. cbn [holds eval] in F64. rewrite E12, u64_lit in F64 by lia.
      pose proof (fact_of_stateB nW st A Kc rho rhoX tp _ _ _ Hw F1gt) as Fgt. cbn [holds eval] in Fgt. unfold V_CLS in Fgt. rewrite E158 in Fgt.
      set (nv := bv_unsigned (rw rho 12%positive)) in HA, HN, F64, Fgt, E148, E149, E150, E158, E159 |- *.
      pose proof (cls_facts nv ltac:(lia)) as (C1 & _ & _ & _).
      rewrite bt_ltu_lit in Fgt by lia. apply Z.ltb_lt in Fgt.
      assert (H' : SPA segs (JGb W st A Kc rho) (E5s1' nW st tmax) rhoX tp (tr, mkCfg ms md)).
      { unfold E5s1', upd. lazy zeta. eapply SPA_restate; [exact W1' | exact D1' | exact NX1' | | constructor | exact Hw].
        unfold diffs_ok. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. unfold V_SIZE. cbn [eval]. rewrite E148.
        exact (tab1_ok_sound 158 _ Size 17 14%nat rhoX (cls_of nv) TAB1 OV1 E158 ltac:(cbn; lia)). }
      apply (SPA_entails0 segs (JGb W st A Kc rho) GW (E5s1' nW st tmax) (C5c W st tmax) s1 rhoX tp _ ENT1 SID1); [|exact H'].
      apply JGb_stable; [exact HUS | exact HKc].
    + eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC (rho_sub rhoX s2))].
      destruct w as [tr [ms md]].
      pose proof (JGb_rigid nW st A Kc rho rhoX tp tr md (proj2 Hw)) as (E12 & E148 & E149 & E150 & E158 & E159).
      destruct (JGb_model nW st A Kc rho rhoX tp tr md (proj2 Hw)) as [HA HN].
      pose proof (fact_of_stateB nW st A Kc rho rhoX tp _ _ _ Hw F2_64) as F64. cbn [holds eval] in F64. rewrite E12, u64_lit in F64 by lia.
      pose proof (fact_of_stateB nW st A Kc rho rhoX tp _ _ _ Hw F2le) as Fle. cbn [holds eval] in Fle. unfold V_CLS in Fle. rewrite E158 in Fle.
      set (nv := bv_unsigned (rw rho 12%positive)) in HA, HN, F64, Fle, E148, E149, E150, E158, E159 |- *.
      pose proof (cls_facts nv ltac:(lia)) as (C1 & _ & _ & _).
      rewrite bt_ltu_lit in Fle by lia.
      assert (Hle : cls_of nv <= 16) by (destruct (Z.ltb_spec 16 (cls_of nv)); [exfalso; apply Fle; reflexivity | lia]).
      assert (H' : SPA segs (JGb W st A Kc rho) (E5s2' nW st tmax) rhoX tp (tr, mkCfg ms md)).
      { unfold E5s2', upd. lazy zeta. eapply SPA_restate; [exact W2' | exact D2' | exact NX2' | | constructor | exact Hw].
        unfold diffs_ok. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. unfold V_SIZE. cbn [eval]. rewrite E148.
        exact (tab1_ok_sound 158 _ Size 1 16%nat rhoX (cls_of nv) TAB2 OV2 E158 ltac:(cbn; lia)). }
      apply (SPA_entails0 segs (JGb W st A Kc rho) GW (E5s2' nW st tmax) (C5c W st tmax) s2 rhoX tp _ ENT2 SID2); [|exact H'].
      apply JGb_stable; [exact HUS | exact HKc].
  - left. reflexivity.
Qed.
End E_spine_s5b.

Section E_spine_s5c.
Hypothesis Cert5c : check_cfgA segsA 4000%nat [0xdb004] GW [C5c W st tmax] [E5m1 W st tmax] = true.
Hypothesis G5m1 : incl F_gen (ss_facts (ax_S (E5m1 W st tmax))).
Hypothesis W5m1 : swf (ax_S (C5m1 W st tmax)) = true.
Hypothesis D5m1 : state_diff (ax_S (E5m1 W st tmax)) (ax_S (C5m1 W st tmax)) = Some ([(len1e, LLe)], []).
Hypothesis NX5m1 : ss_next (ax_S (C5m1 W st tmax)) = ss_next (ax_S (E5m1 W st tmax)).
Variables (s51 sd51 : wsub) (R51 : list sobj) (T51 : axst).
Hypothesis He51 : entails_frA (C5m1 W st tmax) Pre_memsetA s51 = Some R51.
Hypothesis Hchk51 : call_checkA (C5m1 W st tmax) Pre_memsetA s51 R51 (map la_state Posts_memsetA) = true.
Hypothesis HT51 : import_postA s51 Pre_memsetA (liftA (P_ret_memset memset_entryA)) (C5m1 W st tmax) R51 = T51.
Hypothesis FBC51 : forallb (sprop_below (ss_next (ax_S (C5m1 W st tmax)))) (ss_facts (ax_S (C5m1 W st tmax))) = true.
Hypothesis FBT51 : forallb (sprop_below (ss_next (ax_S T51))) (ss_facts (ax_S (C5m1 W st tmax))) = true.
Hypothesis ENT51 : entailsA (ax_with_facts T51 (ss_facts (ax_S (C5m1 W st tmax)))) (C5d W st tmax) sd51 = true.
Hypothesis SID51 : wsub_id_below sd51 GW = true.
Hypothesis NXC51 : (GW <= ss_next (ax_S (C5m1 W st tmax)))%positive.

Hypothesis NXC5c : (GW <= ss_next (ax_S (C5c W st tmax)))%positive.
Hypothesis ECert5c : check_ecfgA segsA 4000%nat [0xdb004] GW [mkVNA (C5c W st tmax) 1 (SLit 0)] [mkVNA (E5m1 W st tmax) 0 (SLit 0)] = true.
Theorem espine_s5c : forall (A : AA) (Kc : KcA) rho tp (Q : world -> Prop),
  stopJ_stable W st -> Kc_ok Kc ->
  1 <= cnt_of A (bv_unsigned (rw rho 12%positive)) ->
  (forall rhoX tpX, etriple segs (SPA segs (JGb W st A Kc rho) (C5d W st tmax) rhoX tpX) Q) ->
  forall rhoE, etriple segs (SPA segs (JGb W st A Kc rho) (C5c W st tmax) rhoE tp) Q.
Proof.
  intros A Kc rho tp Q HUS HKc Hcnt HC rhoE.
  apply (ecfg_cut 4000%nat [0xdb004] GW [mkVNA (C5c W st tmax) 1 (SLit 0)] [mkVNA (E5m1 W st tmax) 0 (SLit 0)] (JGb W st A Kc rho) Q tp (C5c W st tmax) _ (JGb_stable nW st A Kc rho HUS HKc)).
  - intros n Hn. destruct Hn as [<-|[]]; cbn [vna_state]; first [exact NXC5c].
  - exact ECert5c.
  - intros E rhoX HinE. clear NXC5c ECert5c. destruct HinE as [<-|[]]; cbn [vna_state].
    eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw |].
    2:{ apply (ecall_gen (C5m1 W st tmax) T51 (C5d W st tmax) s51 R51 sd51 Pre_memsetA Posts_memsetA (P_ret_memset memset_entryA)
                eq_refl (fun Jx r0 t0 Hs => memset_sumA_ex Jx r0 t0 Hs) He51 Hchk51 HT51 FBC51 FBT51 ENT51 SID51 NXC51 eq_refl
                A Kc rho tp rhoX Q HUS HKc HC). }
    pose proof (JGb_pvals nW st A Kc rho rhoX tp w _ Hw G5m1 Hcnt) as PV. cbn zeta in PV.
    unfold C5m1, upd. lazy zeta. eapply SPA_restate; [exact W5m1 | exact D5m1 | exact NX5m1 | | constructor | exact Hw].
    unfold diffs_ok. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. exact (pv_len1 rhoX _ _ _ _ _ _ PV).
  - left. reflexivity.
Qed.
End E_spine_s5c.

Section E_spine_s5d.
Hypothesis Cert5d : check_cfgA segsA 4000%nat [0xdb004] GW [C5d W st tmax] [E5m2 W st tmax] = true.
Hypothesis G5m2 : incl F_gen (ss_facts (ax_S (E5m2 W st tmax))).
Hypothesis W5m2 : swf (ax_S (C5m2 W st tmax)) = true.
Hypothesis D5m2 : state_diff (ax_S (E5m2 W st tmax)) (ax_S (C5m2 W st tmax)) = Some ([(a0e2, BR); (len2e, LRe)], []).
Hypothesis NX5m2 : ss_next (ax_S (C5m2 W st tmax)) = ss_next (ax_S (E5m2 W st tmax)).
Variables (s52 sd52 : wsub) (R52 : list sobj) (T52 : axst).
Hypothesis He52 : entails_frA (C5m2 W st tmax) Pre_memsetA s52 = Some R52.
Hypothesis Hchk52 : call_checkA (C5m2 W st tmax) Pre_memsetA s52 R52 (map la_state Posts_memsetA) = true.
Hypothesis HT52 : import_postA s52 Pre_memsetA (liftA (P_ret_memset memset_entryA)) (C5m2 W st tmax) R52 = T52.
Hypothesis FBC52 : forallb (sprop_below (ss_next (ax_S (C5m2 W st tmax)))) (ss_facts (ax_S (C5m2 W st tmax))) = true.
Hypothesis FBT52 : forallb (sprop_below (ss_next (ax_S T52))) (ss_facts (ax_S (C5m2 W st tmax))) = true.
Hypothesis ENT52 : entailsA (ax_with_facts T52 (ss_facts (ax_S (C5m2 W st tmax)))) (C5e W st tmax) sd52 = true.
Hypothesis SID52 : wsub_id_below sd52 GW = true.
Hypothesis NXC52 : (GW <= ss_next (ax_S (C5m2 W st tmax)))%positive.

Hypothesis NXC5d : (GW <= ss_next (ax_S (C5d W st tmax)))%positive.
Hypothesis ECert5d : check_ecfgA segsA 4000%nat [0xdb004] GW [mkVNA (C5d W st tmax) 1 (SLit 0)] [mkVNA (E5m2 W st tmax) 0 (SLit 0)] = true.
Theorem espine_s5d : forall (A : AA) (Kc : KcA) rho tp (Q : world -> Prop),
  stopJ_stable W st -> Kc_ok Kc ->
  1 <= cnt_of A (bv_unsigned (rw rho 12%positive)) ->
  (forall rhoX tpX, etriple segs (SPA segs (JGb W st A Kc rho) (C5e W st tmax) rhoX tpX) Q) ->
  forall rhoE, etriple segs (SPA segs (JGb W st A Kc rho) (C5d W st tmax) rhoE tp) Q.
Proof.
  intros A Kc rho tp Q HUS HKc Hcnt HC rhoE.
  apply (ecfg_cut 4000%nat [0xdb004] GW [mkVNA (C5d W st tmax) 1 (SLit 0)] [mkVNA (E5m2 W st tmax) 0 (SLit 0)] (JGb W st A Kc rho) Q tp (C5d W st tmax) _ (JGb_stable nW st A Kc rho HUS HKc)).
  - intros n Hn. destruct Hn as [<-|[]]; cbn [vna_state]; first [exact NXC5d].
  - exact ECert5d.
  - intros E rhoX HinE. clear NXC5d ECert5d. destruct HinE as [<-|[]]; cbn [vna_state].
    eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw |].
    2:{ apply (ecall_gen (C5m2 W st tmax) T52 (C5e W st tmax) s52 R52 sd52 Pre_memsetA Posts_memsetA (P_ret_memset memset_entryA)
                eq_refl (fun Jx r0 t0 Hs => memset_sumA_ex Jx r0 t0 Hs) He52 Hchk52 HT52 FBC52 FBT52 ENT52 SID52 NXC52 eq_refl
                A Kc rho tp rhoX Q HUS HKc HC). }
    pose proof (JGb_pvals nW st A Kc rho rhoX tp w _ Hw G5m2 Hcnt) as PV. cbn zeta in PV.
    unfold C5m2, upd. lazy zeta. eapply SPA_restate; [exact W5m2 | exact D5m2 | exact NX5m2 | | constructor | exact Hw].
    unfold diffs_ok. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd].
    + exact (pv_a0e2 rhoX _ _ _ _ _ _ PV).
    + exact (pv_len2 rhoX _ _ _ _ _ _ PV).
  - left. reflexivity.
Qed.
End E_spine_s5d.

Section E_spine_s5e.
Hypothesis Cert5e : check_cfgA segsA 4000%nat [0x3c80c] GW [C5e W st tmax] [E5j W st tmax] = true.
Variable s6j : wsub.
Hypothesis ENT6j : entailsA (E5j W st tmax) (C6 W st tmax) s6j = true.
Hypothesis SID6j : wsub_id_below s6j GW = true.

Hypothesis NXC5e : (GW <= ss_next (ax_S (C5e W st tmax)))%positive.
Hypothesis ECert5e : check_ecfgA segsA 4000%nat [0x3c80c] GW [mkVNA (C5e W st tmax) 1 (SLit 0)] [mkVNA (E5j W st tmax) 0 (SLit 0)] = true.
Theorem espine_s5e : forall (A : AA) (Kc : KcA) rho tp (Q : world -> Prop),
  stopJ_stable W st -> Kc_ok Kc ->
  (forall rhoX, etriple segs (SPA segs (JGb W st A Kc rho) (C6 W st tmax) rhoX tp) Q) ->
  forall rhoE, etriple segs (SPA segs (JGb W st A Kc rho) (C5e W st tmax) rhoE tp) Q.
Proof.
  intros A Kc rho tp Q HUS HKc HC rhoE.
  apply (ecfg_cut 4000%nat [0x3c80c] GW [mkVNA (C5e W st tmax) 1 (SLit 0)] [mkVNA (E5j W st tmax) 0 (SLit 0)] (JGb W st A Kc rho) Q tp (C5e W st tmax) _ (JGb_stable nW st A Kc rho HUS HKc)).
  - intros n Hn. destruct Hn as [<-|[]]; cbn [vna_state]; first [exact NXC5e].
  - exact ECert5e.
  - intros E rhoX HinE. clear NXC5e ECert5e. destruct HinE as [<-|[]]; cbn [vna_state].
    eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC (rho_sub rhoX s6j))].
    apply (SPA_entails0 segs (JGb W st A Kc rho) GW (E5j W st tmax) (C6 W st tmax) s6j rhoX tp w ENT6j SID6j); [|exact Hw].
    apply JGb_stable; [exact HUS | exact HKc].
  - left. reflexivity.
Qed.
End E_spine_s5e.

Section E_spine_s6.
Hypothesis Cert6 : check_cfgA segsA 4000%nat [0x5f9f8; 0x3c82c] GW [C6 W st tmax] [E6s W st tmax; E6l W st tmax] = true.
Variable k6 : nat.
Hypothesis NTH6s : nth_error (ss_objs (ax_S (E6s W st tmax))) k6 = Some O_U.
Hypothesis ZC6s : zero_covered (ss_facts (ax_S (E6s W st tmax))) O_U = true.
Variable s7s : wsub.
Hypothesis ENT7s : entailsA (ax_setS (E6s W st tmax) (set_objs (ax_S (E6s W st tmax)) (list_set (ss_objs (ax_S (E6s W st tmax))) k6 (zobj O_U))))
                            (C7 W st tmax) s7s = true.
Hypothesis SID7s : wsub_id_below s7s GW = true.
Hypothesis G6l : incl F_gen (ss_facts (ax_S (E6l W st tmax))).
Hypothesis W6l : swf (ax_S (C6l W st tmax)) = true.
Hypothesis D6l : state_diff (ax_S (E6l W st tmax)) (ax_S (C6l W st tmax)) = Some ([(len3e, LUe)], []).
Hypothesis NX6l : ss_next (ax_S (C6l W st tmax)) = ss_next (ax_S (E6l W st tmax)).

Hypothesis NXC6 : (GW <= ss_next (ax_S (C6 W st tmax)))%positive.
Hypothesis ECert6 : check_ecfgA segsA 4000%nat [0x5f9f8; 0x3c82c] GW [mkVNA (C6 W st tmax) 1 (SLit 0)] [mkVNA (E6s W st tmax) 0 (SLit 0); mkVNA (E6l W st tmax) 0 (SLit 0)] = true.
Theorem espine_s6 : forall (A : AA) (Kc : KcA) rho tp (Q : world -> Prop),
  stopJ_stable W st -> Kc_ok Kc ->
  1 <= cnt_of A (bv_unsigned (rw rho 12%positive)) ->
  (forall rhoX, etriple segs (SPA segs (JGb W st A Kc rho) (C7 W st tmax) rhoX tp) Q) ->
  (forall rhoX, etriple segs (SPA segs (JGb W st A Kc rho) (C6l W st tmax) rhoX tp) Q) ->
  forall rhoE, etriple segs (SPA segs (JGb W st A Kc rho) (C6 W st tmax) rhoE tp) Q.
Proof.
  intros A Kc rho tp Q HUS HKc Hcnt HC7 HC6l rhoE.
  apply (ecfg_cut 4000%nat [0x5f9f8; 0x3c82c] GW [mkVNA (C6 W st tmax) 1 (SLit 0)] [mkVNA (E6s W st tmax) 0 (SLit 0); mkVNA (E6l W st tmax) 0 (SLit 0)] (JGb W st A Kc rho) Q tp (C6 W st tmax) _ (JGb_stable nW st A Kc rho HUS HKc)).
  - intros n Hn. destruct Hn as [<-|[]]; cbn [vna_state]; first [exact NXC6].
  - exact ECert6.
  - intros E rhoX HinE. clear NXC6 ECert6. destruct HinE as [<-|[<-|[]]]; cbn [vna_state].
    + eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC7 (rho_sub rhoX s7s))].
      apply (SPA_entails0 segs (JGb W st A Kc rho) GW _ (C7 W st tmax) s7s rhoX tp w ENT7s SID7s); [apply JGb_stable; [exact HUS | exact HKc]|].
      apply (SPA_zero_fold segs (JGb W st A Kc rho) rhoX (E6s W st tmax) tp w k6 O_U NTH6s ZC6s Hw).
    + eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC6l rhoX)].
      pose proof (JGb_pvals nW st A Kc rho rhoX tp w _ Hw G6l Hcnt) as PV. cbn zeta in PV.
      unfold C6l, upd. lazy zeta. eapply SPA_restate; [exact W6l | exact D6l | exact NX6l | | constructor | exact Hw].
      unfold diffs_ok. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. exact (pv_len3 rhoX _ _ _ _ _ _ PV).
  - left. reflexivity.
Qed.
End E_spine_s6.

Section E_spine_s6l.
Hypothesis Cert6l : check_cfgA segsA 4000%nat [0xdb004] GW [C6l W st tmax] [E6m W st tmax] = true.
Hypothesis W6m : swf (ax_S (C6m W st tmax)) = true.
Hypothesis D6m : state_diff (ax_S (E6m W st tmax)) (ax_S (C6m W st tmax)) = Some ([], []).
Hypothesis NX6m : ss_next (ax_S (C6m W st tmax)) = ss_next (ax_S (E6m W st tmax)).
Variables (s6 sd6 : wsub) (R6 : list sobj) (T6 : axst).
Hypothesis He6 : entails_frA (C6m W st tmax) Pre_mszA s6 = Some R6.
Hypothesis Hchk6 : call_checkA (C6m W st tmax) Pre_mszA s6 R6 (map la_state Posts_mszA) = true.
Hypothesis HT6 : import_postA s6 Pre_mszA (liftA P_msz) (C6m W st tmax) R6 = T6.
Hypothesis FBC6 : forallb (sprop_below (ss_next (ax_S (C6m W st tmax)))) (ss_facts (ax_S (C6m W st tmax))) = true.
Hypothesis FBT6 : forallb (sprop_below (ss_next (ax_S T6))) (ss_facts (ax_S (C6m W st tmax))) = true.
Hypothesis ENT6 : entailsA (ax_with_facts T6 (ss_facts (ax_S (C6m W st tmax)))) (C6b W st tmax) sd6 = true.
Hypothesis SID6 : wsub_id_below sd6 GW = true.
Hypothesis NXC6 : (GW <= ss_next (ax_S (C6m W st tmax)))%positive.

Hypothesis NXC6l : (GW <= ss_next (ax_S (C6l W st tmax)))%positive.
Hypothesis ECert6l : check_ecfgA segsA 4000%nat [0xdb004] GW [mkVNA (C6l W st tmax) 1 (SLit 0)] [mkVNA (E6m W st tmax) 0 (SLit 0)] = true.
Theorem espine_s6l : forall (A : AA) (Kc : KcA) rho tp (Q : world -> Prop),
  stopJ_stable W st -> Kc_ok Kc ->
  (forall rhoX tpX, etriple segs (SPA segs (JGb W st A Kc rho) (C6b W st tmax) rhoX tpX) Q) ->
  forall rhoE, etriple segs (SPA segs (JGb W st A Kc rho) (C6l W st tmax) rhoE tp) Q.
Proof.
  intros A Kc rho tp Q HUS HKc HC rhoE.
  apply (ecfg_cut 4000%nat [0xdb004] GW [mkVNA (C6l W st tmax) 1 (SLit 0)] [mkVNA (E6m W st tmax) 0 (SLit 0)] (JGb W st A Kc rho) Q tp (C6l W st tmax) _ (JGb_stable nW st A Kc rho HUS HKc)).
  - intros n Hn. destruct Hn as [<-|[]]; cbn [vna_state]; first [exact NXC6l].
  - exact ECert6l.
  - intros E rhoX HinE. clear NXC6l ECert6l. destruct HinE as [<-|[]]; cbn [vna_state].
    eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw |].
    2:{ apply (ecall_gen (C6m W st tmax) T6 (C6b W st tmax) s6 R6 sd6 Pre_mszA Posts_mszA P_msz
                eq_refl (fun Jx r0 t0 Hs => memsetZ_sumA_ex Jx Hs r0 t0) He6 Hchk6 HT6 FBC6 FBT6 ENT6 SID6 NXC6 eq_refl
                A Kc rho tp rhoX Q HUS HKc HC). }
    unfold C6m, upd. lazy zeta. eapply SPA_restate; [exact W6m | exact D6m | exact NX6m | constructor | constructor | exact Hw].
  - left. reflexivity.
Qed.
End E_spine_s6l.

Section E_spine_s6b.
Hypothesis Cert6b : check_cfgA segsA 4000%nat [0x3c82c] GW [C6b W st tmax] [E6j W st tmax] = true.
Variable s7j : wsub.
Hypothesis ENT7j : entailsA (E6j W st tmax) (C7 W st tmax) s7j = true.
Hypothesis SID7j : wsub_id_below s7j GW = true.

Hypothesis NXC6b : (GW <= ss_next (ax_S (C6b W st tmax)))%positive.
Hypothesis ECert6b : check_ecfgA segsA 4000%nat [0x3c82c] GW [mkVNA (C6b W st tmax) 1 (SLit 0)] [mkVNA (E6j W st tmax) 0 (SLit 0)] = true.
Theorem espine_s6b : forall (A : AA) (Kc : KcA) rho tp (Q : world -> Prop),
  stopJ_stable W st -> Kc_ok Kc ->
  (forall rhoX, etriple segs (SPA segs (JGb W st A Kc rho) (C7 W st tmax) rhoX tp) Q) ->
  forall rhoE, etriple segs (SPA segs (JGb W st A Kc rho) (C6b W st tmax) rhoE tp) Q.
Proof.
  intros A Kc rho tp Q HUS HKc HC rhoE.
  apply (ecfg_cut 4000%nat [0x3c82c] GW [mkVNA (C6b W st tmax) 1 (SLit 0)] [mkVNA (E6j W st tmax) 0 (SLit 0)] (JGb W st A Kc rho) Q tp (C6b W st tmax) _ (JGb_stable nW st A Kc rho HUS HKc)).
  - intros n Hn. destruct Hn as [<-|[]]; cbn [vna_state]; first [exact NXC6b].
  - exact ECert6b.
  - intros E rhoX HinE. clear NXC6b ECert6b. destruct HinE as [<-|[]]; cbn [vna_state].
    eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC (rho_sub rhoX s7j))].
    apply (SPA_entails0 segs (JGb W st A Kc rho) GW (E6j W st tmax) (C7 W st tmax) s7j rhoX tp w ENT7j SID7j); [|exact Hw].
    apply JGb_stable; [exact HUS | exact HKc].
  - left. reflexivity.
Qed.
End E_spine_s6b.

Section E_spine_s7.
Hypothesis Cert7 : check_cfgA segsA 4000%nat [0x3c8bc; 0x3ca04] GW [C7 W st tmax] [E7c1 W st tmax; E7c2 W st tmax; E7p W st tmax] = true.
Hypothesis OV7a : only_var 157 (creg7a W st tmax) = true.
Hypothesis OV7b : only_var 157 (creg7b W st tmax) = true.
Hypothesis TAB7a : tab_ok 157 (creg7a W st tmax) ClassID 520 8128%nat = true.
Hypothesis TAB7b : tab_ok 157 (creg7b W st tmax) ClassID 24 62%nat = true.
Hypothesis W7a : swf (ax_S (E7c1' nW st tmax)) = true.
Hypothesis W7b : swf (ax_S (E7c2' nW st tmax)) = true.
Hypothesis D7a : state_diff (ax_S (E7c1 W st tmax)) (ax_S (E7c1' nW st tmax)) = Some ([(creg7a W st tmax, SVar V_CLS)], []).
Hypothesis D7b : state_diff (ax_S (E7c2 W st tmax)) (ax_S (E7c2' nW st tmax)) = Some ([(creg7b W st tmax, SVar V_CLS)], []).
Hypothesis NX7a : ss_next (ax_S (E7c1' nW st tmax)) = ss_next (ax_S (E7c1 W st tmax)).
Hypothesis NX7b : ss_next (ax_S (E7c2' nW st tmax)) = ss_next (ax_S (E7c2 W st tmax)).
Hypothesis G7a : incl F_gen (ss_facts (ax_S (E7c1 W st tmax))).
Hypothesis G7b : incl F_gen (ss_facts (ax_S (E7c2 W st tmax))).
Hypothesis F7a : In (SPBranch BC_LTU (SLit 512) (SVar V_ND)) (ss_facts (ax_S (E7c1 W st tmax))).
Hypothesis F7b : In (SPNot (SPBranch BC_LTU (SLit 512) (SVar V_ND))) (ss_facts (ax_S (E7c2 W st tmax))).
Variables s8a s8b : wsub.
Hypothesis ENT8a : entailsA (E7c1' nW st tmax) (C8 W st tmax) s8a = true.
Hypothesis ENT8b : entailsA (E7c2' nW st tmax) (C8 W st tmax) s8b = true.
Hypothesis SID8a : wsub_id_below s8a GW = true.
Hypothesis SID8b : wsub_id_below s8b GW = true.
Hypothesis G7p : incl F_gen (ss_facts (ax_S (E7p W st tmax))).
Hypothesis F7p : In (SPNot (SPBranch BC_EQ (SVar 12) n8e)) (ss_facts (ax_S (E7p W st tmax))).
Hypothesis W7p : swf (ax_S (C7p W st tmax)) = true.
Hypothesis D7p : state_diff (ax_S (E7p W st tmax)) (ax_S (C7p W st tmax)) = Some ([(a0e7, BP)], [SPUle (SLit 1) LPe]).
Hypothesis NX7p : ss_next (ax_S (C7p W st tmax)) = ss_next (ax_S (E7p W st tmax)).
Hypothesis F7an : In (SPBranch BC_EQ (SVar 12) n8e) (ss_facts (ax_S (E7c1 W st tmax))).
Hypothesis F7bn : In (SPBranch BC_EQ (SVar 12) n8e) (ss_facts (ax_S (E7c2 W st tmax))).

Hypothesis NXC7 : (GW <= ss_next (ax_S (C7 W st tmax)))%positive.
Hypothesis ECert7 : check_ecfgA segsA 4000%nat [0x3c8bc; 0x3ca04] GW [mkVNA (C7 W st tmax) 1 (SLit 0)] [mkVNA (E7c1 W st tmax) 0 (SLit 0); mkVNA (E7c2 W st tmax) 0 (SLit 0); mkVNA (E7p W st tmax) 0 (SLit 0)] = true.
Theorem espine_s7 : forall (A : AA) (Kc : KcA) rho tp (Q : world -> Prop),
  stopJ_stable W st -> Kc_ok Kc ->
  1 <= cnt_of A (bv_unsigned (rw rho 12%positive)) ->
  (bv_unsigned (rw rho 12%positive) mod 8 = 0 -> forall rhoX, etriple segs (SPA segs (JGb W st A Kc rho) (C8 W st tmax) rhoX tp) Q) ->
  (bv_unsigned (rw rho 12%positive) mod 8 <> 0 -> forall rhoX, etriple segs (SPA segs (JGb W st A Kc rho) (C7p W st tmax) rhoX tp) Q) ->
  forall rhoE, etriple segs (SPA segs (JGb W st A Kc rho) (C7 W st tmax) rhoE tp) Q.
Proof.
  intros A Kc rho tp Q HUS HKc Hcnt HC8 HC7p rhoE.
  apply (ecfg_cut 4000%nat [0x3c8bc; 0x3ca04] GW [mkVNA (C7 W st tmax) 1 (SLit 0)] [mkVNA (E7c1 W st tmax) 0 (SLit 0); mkVNA (E7c2 W st tmax) 0 (SLit 0); mkVNA (E7p W st tmax) 0 (SLit 0)] (JGb W st A Kc rho) Q tp (C7 W st tmax) _ (JGb_stable nW st A Kc rho HUS HKc)).
  - intros n Hn. destruct Hn as [<-|[]]; cbn [vna_state]; first [exact NXC7].
  - exact ECert7.
  - intros E rhoX HinE. clear NXC7 ECert7. destruct HinE as [<-|[<-|[<-|[]]]]; cbn [vna_state].
    + apply (etriple_pre_pure segs _ _ (bv_unsigned (rw rho 12%positive) mod 8 = 0)); [intros w Hw; exact (nmod8_of_fact nW st tmax NX7a NX7b NX7p A Kc rho rhoX tp w _ true Hw G7a F7an)|]. intros Hm0.
      eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC8 Hm0 (rho_sub rhoX s8a))].
      apply (SPA_entails0 segs (JGb W st A Kc rho) GW (E7c1' nW st tmax) (C8 W st tmax) s8a rhoX tp w ENT8a SID8a); [apply JGb_stable; [exact HUS | exact HKc]|].
      unfold E7c1', upd. lazy zeta.
      apply (class_restate_gen nW st (E7c1 W st tmax) _ (creg7a W st tmax) 520 8128%nat A Kc rho tp w rhoX OV7a TAB7a W7a D7a NX7a); [|exact Hw].
      exact (needed_range nW st A Kc rho rhoX tp w _ true Hw G7a F7a).
    + apply (etriple_pre_pure segs _ _ (bv_unsigned (rw rho 12%positive) mod 8 = 0)); [intros w Hw; exact (nmod8_of_fact nW st tmax NX7a NX7b NX7p A Kc rho rhoX tp w _ true Hw G7b F7bn)|]. intros Hm0.
      eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC8 Hm0 (rho_sub rhoX s8b))].
      apply (SPA_entails0 segs (JGb W st A Kc rho) GW (E7c2' nW st tmax) (C8 W st tmax) s8b rhoX tp w ENT8b SID8b); [apply JGb_stable; [exact HUS | exact HKc]|].
      unfold E7c2', upd. lazy zeta.
      apply (class_restate_gen nW st (E7c2 W st tmax) _ (creg7b W st tmax) 24 62%nat A Kc rho tp w rhoX OV7b TAB7b W7b D7b NX7b); [|exact Hw].
      exact (needed_range nW st A Kc rho rhoX tp w _ false Hw G7b F7b).
    + apply (etriple_pre_pure segs _ _ (bv_unsigned (rw rho 12%positive) mod 8 <> 0)); [intros w Hw; exact (nmod8_of_fact nW st tmax NX7a NX7b NX7p A Kc rho rhoX tp w _ false Hw G7p F7p)|]. intros Hm8.
      eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC7p Hm8 rhoX)].
      pose proof (JGb_pvals nW st A Kc rho rhoX tp w _ Hw G7p Hcnt) as PV. cbn zeta in PV.
      destruct w as [tr [ms md]].
      unfold C7p, upd. lazy zeta. eapply SPA_restate; [exact W7p | exact D7p | exact NX7p | | | exact Hw].
      * unfold diffs_ok. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. exact (pv_a0e7 rhoX _ _ _ _ _ _ PV).
      * apply Forall_cons; [|apply Forall_nil]. cbn [holds eval]. fold LPe. rewrite (pv_lp1 rhoX _ _ _ _ _ _ PV Hm8). rewrite u64_lit by lia. lia.
  - left. reflexivity.
Qed.
End E_spine_s7.

Section E_spine_s7p.
Hypothesis Cert7p : check_cfgA segsA 4000%nat [0x3ca04] GW [C7p W st tmax] [E7q1 W st tmax; E7q2 W st tmax] = true.
Hypothesis OV7c : only_var 157 (creg7c W st tmax) = true.
Hypothesis OV7d : only_var 157 (creg7d W st tmax) = true.
Hypothesis TAB7c : tab_ok 157 (creg7c W st tmax) ClassID 520 8128%nat = true.
Hypothesis TAB7d : tab_ok 157 (creg7d W st tmax) ClassID 24 62%nat = true.
Hypothesis W7c : swf (ax_S (E7q1' nW st tmax)) = true.
Hypothesis W7d : swf (ax_S (E7q2' nW st tmax)) = true.
Hypothesis D7c : state_diff (ax_S (E7q1 W st tmax)) (ax_S (E7q1' nW st tmax)) = Some ([(creg7c W st tmax, SVar V_CLS)], []).
Hypothesis D7d : state_diff (ax_S (E7q2 W st tmax)) (ax_S (E7q2' nW st tmax)) = Some ([(creg7d W st tmax, SVar V_CLS)], []).
Hypothesis NX7c : ss_next (ax_S (E7q1' nW st tmax)) = ss_next (ax_S (E7q1 W st tmax)).
Hypothesis NX7d : ss_next (ax_S (E7q2' nW st tmax)) = ss_next (ax_S (E7q2 W st tmax)).
Hypothesis G7c : incl F_gen (ss_facts (ax_S (E7q1 W st tmax))).
Hypothesis G7d : incl F_gen (ss_facts (ax_S (E7q2 W st tmax))).
Hypothesis F7c : In (SPBranch BC_LTU (SLit 512) (SVar V_ND)) (ss_facts (ax_S (E7q1 W st tmax))).
Hypothesis F7d : In (SPNot (SPBranch BC_LTU (SLit 512) (SVar V_ND))) (ss_facts (ax_S (E7q2 W st tmax))).
Variables s8c s8d : wsub.
Hypothesis ENT8c : entailsA (E7q1' nW st tmax) (C8p W st tmax) s8c = true.
Hypothesis ENT8d : entailsA (E7q2' nW st tmax) (C8p W st tmax) s8d = true.
Hypothesis SID8c : wsub_id_below s8c GW = true.
Hypothesis SID8d : wsub_id_below s8d GW = true.

Hypothesis NXC7p : (GW <= ss_next (ax_S (C7p W st tmax)))%positive.
Hypothesis ECert7p : check_ecfgA segsA 4000%nat [0x3ca04] GW [mkVNA (C7p W st tmax) 1 (SLit 0)] [mkVNA (E7q1 W st tmax) 0 (SLit 0); mkVNA (E7q2 W st tmax) 0 (SLit 0)] = true.
Theorem espine_s7p : forall (A : AA) (Kc : KcA) rho tp (Q : world -> Prop),
  stopJ_stable W st -> Kc_ok Kc ->
  (forall rhoX, etriple segs (SPA segs (JGb W st A Kc rho) (C8p W st tmax) rhoX tp) Q) ->
  forall rhoE, etriple segs (SPA segs (JGb W st A Kc rho) (C7p W st tmax) rhoE tp) Q.
Proof.
  intros A Kc rho tp Q HUS HKc HC8 rhoE.
  apply (ecfg_cut 4000%nat [0x3ca04] GW [mkVNA (C7p W st tmax) 1 (SLit 0)] [mkVNA (E7q1 W st tmax) 0 (SLit 0); mkVNA (E7q2 W st tmax) 0 (SLit 0)] (JGb W st A Kc rho) Q tp (C7p W st tmax) _ (JGb_stable nW st A Kc rho HUS HKc)).
  - intros n Hn. destruct Hn as [<-|[]]; cbn [vna_state]; first [exact NXC7p].
  - exact ECert7p.
  - intros E rhoX HinE. clear NXC7p ECert7p. destruct HinE as [<-|[<-|[]]]; cbn [vna_state].
    + eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC8 (rho_sub rhoX s8c))].
      apply (SPA_entails0 segs (JGb W st A Kc rho) GW (E7q1' nW st tmax) (C8p W st tmax) s8c rhoX tp w ENT8c SID8c); [apply JGb_stable; [exact HUS | exact HKc]|].
      unfold E7q1', upd. lazy zeta.
      apply (class_restate_gen nW st (E7q1 W st tmax) _ (creg7c W st tmax) 520 8128%nat A Kc rho tp w rhoX OV7c TAB7c W7c D7c NX7c); [|exact Hw].
      exact (needed_range nW st A Kc rho rhoX tp w _ true Hw G7c F7c).
    + eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC8 (rho_sub rhoX s8d))].
      apply (SPA_entails0 segs (JGb W st A Kc rho) GW (E7q2' nW st tmax) (C8p W st tmax) s8d rhoX tp w ENT8d SID8d); [apply JGb_stable; [exact HUS | exact HKc]|].
      unfold E7q2', upd. lazy zeta.
      apply (class_restate_gen nW st (E7q2 W st tmax) _ (creg7d W st tmax) 24 62%nat A Kc rho tp w rhoX OV7d TAB7d W7d D7d NX7d); [|exact Hw].
      exact (needed_range nW st A Kc rho rhoX tp w _ false Hw G7d F7d).
  - left. reflexivity.
Qed.
End E_spine_s7p.

Section E_spine_s8_gen.
Variables (CC8 CC9 EE8a EE8b CC8ma : axst).
Hypothesis Cert8 : check_cfgA segsA 4000%nat [0xdb004; 0x3ca54] GW [CC8] [EE8a; EE8b] = true.
Hypothesis HCC8ma : CC8ma = upd W st tmax EE8a MSENT [(10%nat, ube)] [] false [].
Hypothesis W8a : swf (ax_S CC8ma) = true.
Hypothesis D8a : state_diff (ax_S EE8a) (ax_S CC8ma) = Some ([], []).
Hypothesis NX8a : ss_next (ax_S CC8ma) = ss_next (ax_S EE8a).
Variables (s8 sd8 : wsub) (R8 : list sobj) (T8 : axst).
Hypothesis He8 : entails_frA CC8ma Pre_memsetA s8 = Some R8.
Hypothesis Hchk8 : call_checkA CC8ma Pre_memsetA s8 R8 (map la_state Posts_memsetA) = true.
Hypothesis HT8 : import_postA s8 Pre_memsetA (liftA (P_ret_memset memset_entryA)) CC8ma R8 = T8.
Hypothesis FBC8 : forallb (sprop_below (ss_next (ax_S CC8ma))) (ss_facts (ax_S CC8ma)) = true.
Hypothesis FBT8 : forallb (sprop_below (ss_next (ax_S T8))) (ss_facts (ax_S CC8ma)) = true.
Hypothesis ENT9 : entailsA (ax_with_facts T8 (ss_facts (ax_S CC8ma))) CC9 sd8 = true.
Hypothesis SID9 : wsub_id_below sd8 GW = true.
Hypothesis NXC8 : (GW <= ss_next (ax_S CC8ma))%positive.
Variables (i8 : nat) (S8s : sstate).
Hypothesis SPL8 : split_obj_at (ax_S EE8b) i8 (SLit 4096) = Some S8s.
Let X8b : axst := ax_setS EE8b S8s.
Variables (s8b sd8b : wsub) (R8b : list sobj) (T8b : axst).
Hypothesis He8b : entails_frA X8b Pre_memsetA s8b = Some R8b.
Hypothesis Hchk8b : call_checkA X8b Pre_memsetA s8b R8b (map la_state Posts_memsetA) = true.
Hypothesis HT8b : import_postA s8b Pre_memsetA (liftA (P_ret_memset memset_entryA)) X8b R8b = T8b.
Hypothesis FBC8b : forallb (sprop_below (ss_next (ax_S X8b))) (ss_facts (ax_S X8b)) = true.
Hypothesis FBT8b : forallb (sprop_below (ss_next (ax_S T8b))) (ss_facts (ax_S X8b)) = true.
Hypothesis NXC8b : (GW <= ss_next (ax_S X8b))%positive.
Variables (i9 : nat) (SU SM : sstate).
Let U8b0 : axst := ax_add_facts [SPNot (SPBranch BC_LTU (SVar 12) (SLit 4096))] CC9.
Hypothesis SPLU : split_obj_at (ax_S U8b0) i9 (SLit 4096) = Some SU.
Let U8b : axst := ax_setS U8b0 SU.
Hypothesis ENTU : entailsA (ax_with_facts T8b (ss_facts (ax_S X8b))) U8b sd8b = true.
Hypothesis SIDU : wsub_id_below sd8b GW = true.
Hypothesis MRG : merge_objs_at (ax_S U8b) i9 = Some SM.
Variable s9m : wsub.
Hypothesis ENTM : entailsA (ax_setS U8b SM) CC9 s9m = true.
Hypothesis SIDM : wsub_id_below s9m GW = true.

Hypothesis NXCC8 : (GW <= ss_next (ax_S (CC8)))%positive.
Hypothesis ECert8 : check_ecfgA segsA 4000%nat [0xdb004; 0x3ca54] GW [mkVNA (CC8) 1 (SLit 0)] [mkVNA (EE8a) 0 (SLit 0); mkVNA (EE8b) 0 (SLit 0)] = true.
Theorem espine_s8_gen : forall (A : AA) (Kc : KcA) rho tp (Q : world -> Prop),
  stopJ_stable W st -> Kc_ok Kc ->
  (forall rhoX tpX, etriple segs (SPA segs (JGb W st A Kc rho) CC9 rhoX tpX) Q) ->
  forall rhoE, etriple segs (SPA segs (JGb W st A Kc rho) CC8 rhoE tp) Q.
Proof.
  intros A Kc rho tp Q HUS HKc HC9 rhoE.
  pose proof (JGb_stable nW st A Kc rho HUS HKc) as HST.
  apply (ecfg_cut 4000%nat [0xdb004; 0x3ca54] GW [mkVNA (CC8) 1 (SLit 0)] [mkVNA (EE8a) 0 (SLit 0); mkVNA (EE8b) 0 (SLit 0)] (JGb W st A Kc rho) Q tp (CC8) _ (JGb_stable nW st A Kc rho HUS HKc)).
  - intros n Hn. destruct Hn as [<-|[]]; cbn [vna_state]; first [exact NXCC8].
  - exact ECert8.
  - intros E rhoX HinE. clear NXCC8 ECert8. destruct HinE as [<-|[<-|[]]]; cbn [vna_state].
    +
      eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw |].
      2:{ apply (ecall_gen CC8ma T8 CC9 s8 R8 sd8 Pre_memsetA Posts_memsetA (P_ret_memset memset_entryA)
                  eq_refl (fun Jx r0 t0 Hs => memset_sumA_ex Jx r0 t0 Hs) He8 Hchk8 HT8 FBC8 FBT8 ENT9 SID9 NXC8 eq_refl
                A Kc rho tp rhoX Q HUS HKc HC9). }
      rewrite HCC8ma. unfold upd. lazy zeta. rewrite HCC8ma in W8a, D8a, NX8a. unfold upd in W8a, D8a, NX8a.
      eapply SPA_restate; [exact W8a | exact D8a | exact NX8a | constructor | constructor | exact Hw].
    +
      eapply etriple_conseq; [intros w Hw; exact (SPA_split segs (JGb W st A Kc rho) rhoX EE8b i8 (SLit 4096) S8s tp w SPL8 Hw) | intros w Hw; right; exact Hw |].
      apply (ecall_gen X8b T8b U8b s8b R8b sd8b Pre_memsetA Posts_memsetA (P_ret_memset memset_entryA)
               eq_refl (fun Jx r0 t0 Hs => memset_sumA_ex Jx r0 t0 Hs) He8b Hchk8b HT8b FBC8b FBT8b ENTU SIDU NXC8b eq_refl
               A Kc rho tp rhoX Q HUS HKc).
      intros rhoY tpY.
      eapply etriple_conseq; [intros w Hw | intros w Hw; exact Hw | apply (HC9 (rho_sub rhoY s9m) tpY)].
      apply (SPA_entails0 segs (JGb W st A Kc rho) GW (ax_setS U8b SM) CC9 s9m rhoY tpY w ENTM SIDM HST).
      exact (SPA_merge segs (JGb W st A Kc rho) rhoY U8b i9 SM tpY w MRG Hw).
  - left. reflexivity.
Qed.
End E_spine_s8_gen.

Section E_spine_s9.
Variable partial : bool.
Variables (CC9 Fa Fb : axst).
Hypothesis ECert9a : check_ecfgA segsA 4000%nat [] GW [mkVNA (ax_add_facts [SPUle (SLit 32) (SVar V_RZ)] CC9) 1 (SLit 0)] [mkVNA Fa 0 (SLit 0)] = true.
Hypothesis ECert9b : check_ecfgA segsA 4000%nat [] GW [mkVNA (ax_add_facts [SPUle (SVar V_RZ) (SLit 16)] CC9) 1 (SLit 0)] [mkVNA Fb 0 (SLit 0)] = true.
Hypothesis NX9 : (GW <= ss_next (ax_S CC9))%positive.
Hypothesis FGC : incl F_gen (ss_facts (ax_S CC9)).
Variables (swca scellsa hcellsa swcb scellsb hcellsb : list cell) (sa sb : wsub).
Hypothesis FHa : fin_hyps nW st Fa swca scellsa hcellsa partial sa.
Hypothesis FHb : fin_hyps nW st Fb swcb scellsb hcellsb partial sb.

Theorem espine_s9_P : forall (A0 A : AA) (Kc : KcA) (rho0 rho : valuation) (keep : Z -> Prop) tp0 (Posts : list (axst * jpostA)),
  In (L_malloc_ok AE_A W st, JL_malloc_ok AInv CST XGL A0 Kc) Posts ->
  (st = UStopLeOrPc -> W = []) -> stopJ_stable W st -> Kc_ok Kc ->
  depot_onlyK A0 A -> hd_link keep rho0 rho ->
  (forall a, client_addrA CST A0 a \/ client_shadowA CST XGL A0 a -> keep a) ->
  1 <= cnt_of A (bv_unsigned (rw rho 12%positive)) ->
  prim_room A ->
  (if partial then bv_unsigned (rw rho 12%positive) mod 8 <> 0 else bv_unsigned (rw rho 12%positive) mod 8 = 0) ->
  forall rhoX tpX, etriple segs (SPA segs (JGb W st A Kc rho) CC9 rhoX tpX) (LQPA segs NF rho0 tp0 Posts).
Proof.
  intros A0 A Kc rho0 rho keep tp0 Posts HPin HW HUS HKc HDO HL HKEEP Hcnt HPRM Hpar rhoX tpX.
  pose proof (JGb_stable nW st A Kc rho HUS HKc) as HST.
  set (nv := bv_unsigned (rw rho 12%positive)) in *.
  apply (etriple_pre_pure segs _ _ (rw rhoX V_RZ = Z_to_bv 64 (rz nv) /\ (16 <= rz nv <= 1024 /\ rz nv mod 16 = 0))).
  { intros w Hw. pose proof (JGb_pvals nW st A Kc rho rhoX tpX w CC9 Hw FGC Hcnt) as PV. cbn zeta in PV.
    destruct PV as (_ & _ & E150 & _ & _ & _ & _ & _ & Brz & _). split; [exact E150 | exact Brz]. }
  intros [E150 RZF].
  assert (NXF : forall Fs, (GW <= ss_next (ax_S (ax_add_facts Fs CC9)))%positive) by (intros Fs; exact NX9).
  destruct (Z.eq_dec (rz nv) 16) as [E16|N16].
  - eapply etriple_conseq; [intros w Hw | intros w Hw; exact Hw |].
    { apply (SPA_add_facts (JGb W st A Kc rho) rhoX CC9 [SPUle (SVar V_RZ) (SLit 16)] tpX w); [| |exact Hw].
      - constructor; [|constructor]. cbn [holds eval]. rewrite E150, !u64_lit by lia. lia.
      - cbn. unfold V_RZ. rewrite !andb_true_r. apply (proj2 (Pos.ltb_lt _ _)). unfold GW in NX9. lia. }
    apply (ecfg_cut 4000%nat [] GW [mkVNA (ax_add_facts [SPUle (SVar V_RZ) (SLit 16)] CC9) 1 (SLit 0)] [mkVNA Fb 0 (SLit 0)] (JGb W st A Kc rho) _ tpX _ _ HST).
    + intros n Hn. destruct Hn as [<-|[]]. cbn [vna_state]. exact (NXF _).
    + exact ECert9b.
    + intros E rhoY HinE. clear ECert9a ECert9b. destruct HinE as [<-|[]]. cbn [vna_state].
      eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw |].
      eapply etriple_conseq; [intros w Hw; exact Hw | | apply etriple_refl].
      intros w Hw. exact (malloc_finish'_P nW st CST XGL HCST HXGL HCSTM law_die Fb swcb scellsb hcellsb partial sb FHb A0 A Kc rho0 rho keep rhoY tp0 tpX w Posts HPin HW HKc HDO HL HKEEP Hcnt HPRM Hpar Hw).
    + left. reflexivity.
  - eapply etriple_conseq; [intros w Hw | intros w Hw; exact Hw |].
    { apply (SPA_add_facts (JGb W st A Kc rho) rhoX CC9 [SPUle (SLit 32) (SVar V_RZ)] tpX w); [| |exact Hw].
      - constructor; [|constructor]. cbn [holds eval]. rewrite E150, !u64_lit by lia. lia.
      - cbn. unfold V_RZ. rewrite !andb_true_r. apply (proj2 (Pos.ltb_lt _ _)). unfold GW in NX9. lia. }
    apply (ecfg_cut 4000%nat [] GW [mkVNA (ax_add_facts [SPUle (SLit 32) (SVar V_RZ)] CC9) 1 (SLit 0)] [mkVNA Fa 0 (SLit 0)] (JGb W st A Kc rho) _ tpX _ _ HST).
    + intros n Hn. destruct Hn as [<-|[]]. cbn [vna_state]. exact (NXF _).
    + exact ECert9a.
    + intros E rhoY HinE. clear ECert9a ECert9b. destruct HinE as [<-|[]]. cbn [vna_state].
      eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw |].
      eapply etriple_conseq; [intros w Hw; exact Hw | | apply etriple_refl].
      intros w Hw. exact (malloc_finish'_P nW st CST XGL HCST HXGL HCSTM law_die Fa swca scellsa hcellsa partial sa FHa A0 A Kc rho0 rho keep rhoY tp0 tpX w Posts HPin HW HKc HDO HL HKEEP Hcnt HPRM Hpar Hw).
    + left. reflexivity.
Qed.
Theorem espine_s9 : forall (A0 A : AA) (Kc : KcA) (rho0 rho : valuation) (keep : Z -> Prop) tp0,
  (st = UStopLeOrPc -> W = []) -> stopJ_stable W st -> Kc_ok Kc ->
  depot_onlyK A0 A -> hd_link keep rho0 rho ->
  (forall a, client_addrA CST A0 a \/ client_shadowA CST XGL A0 a -> keep a) ->
  1 <= cnt_of A (bv_unsigned (rw rho 12%positive)) ->
  prim_room A ->
  (if partial then bv_unsigned (rw rho 12%positive) mod 8 <> 0 else bv_unsigned (rw rho 12%positive) mod 8 = 0) ->
  forall rhoX tpX, etriple segs (SPA segs (JGb W st A Kc rho) CC9 rhoX tpX) (LQPA segs NF rho0 tp0 (Posts_malloc AE_A AInv CST XGL W st A0 Kc)).
Proof.
  intros A0 A Kc rho0 rho keep tp0. apply espine_s9_P. unfold Posts_malloc. right. left. reflexivity.
Qed.
End E_spine_s9.

End E.
End SpineMallocE.

(* [comment removed for export] *)
Module SpineCallocS9.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "SLit"; "cell"; "SVar"; "valuation"; "sprop"; "rw"; "SAlu"; "ss_next"; "ss_facts"; "mkCell"; "DUnknown"; "ss_objs"; "mkObj"; "rm"; "SPUle"; "eval"; "c_width"; "ob_dflt"; "sprop_below"; "sstate"; "swf"; "c_off"; "dflt_writable"; "enc_bytes"; "ob_cells"; "odefault"; "smatch"; "soff"; "DZero"; "c_val"; "covered"; "holds"; "mkSS"; "ob_base"; "obj_hi_of"; "obj_lo_of"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_pc"; "ss_regs"; "ss_resv"; "sv_eqb"; "@Corelib.Init.Logic"; "eq"; "and"; "or"; "not"; "False"; "ex"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@Corelib.Init.Datatypes"; "bool"; "list"; "cons"; "true"; "nat"; "prod"; "nil"; "pair"; "app"; "Some"; "option"; "length"; "None"; "andb"; "false"; "fst"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "xr_below"; "ax_X"; "ax_base"; "cell_eqb"; "la_state"; "leafA"; "mkAX"; "@LinuxProcessSemantics.Riscv.Instr"; "aluop"; "ALU_ADD"; "mulop"; "ALU_AND"; "ALU_OR"; "@Stdlib.Lists.List"; "In"; "forallb"; "incl"; "existsb"; "@Stdlib.ZArith.BinInt.Z"; "le"; "modulo"; "land"; "add"; "pow"; "lor"; "lt"; "to_nat"; "eqb"; "leb"; "ltb"; "of_nat"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "bv_wrap"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "prim_room"; "ag_spacebeg"; "ag_ctx"; "ag_stack_bottom"; "ag_stack_top"; "ag_thread"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP"; "V_RZ"; "ube"; "F_gen"; "ab_e"; "BP"; "LPe"; "MSENT"; "O_L"; "O_R"; "O_T"; "O_UBz"; "O_Uz"; "O_pck"; "O_pcs"; "V_CNT"; "pc_base"; "upd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "jpredA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CallocPosts"; "Lc_ok"; "JLc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase"; "stopJ_w"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "client_addrA"; "client_shadowA"; "V_RES"; "base_sv"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "J_alloc_preT"; "O_got"; "O_rtc"; "V_DEPTH"; "unwind_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocS5"; "JGb"; "depot_onlyK"; "hd_link"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "cnt_of"; "stopJ_stable"; "N_m1"; "@Corelib.Init.Nat"; "add"; "@Corelib.Lists.ListDef"; "seq"; "Forall"; "nth"; "map"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jd.SpineCallocS9"; "idxs9"; "S2_of"; "R9"; "X9_of"; "hc_cptr"; "hc_magic"; "hc_type"; "pcell"; "tya_okb"; "tyv"; "KEPT9";
"O_Hf"; "O_Pf"; "O_pccf"; "O_stf"; "hc_size"; "hc_sizehi"; "hc_state"; "sw9"; "ty_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub_id_below"; "rho_absorb"; "in_ranges"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ"; "Pre_mszA"; "P_msz"; "Posts_mszA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "cells_in_view"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "nodupN"; "select"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "vT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "cell_ok"; "in_rangesZ"; "mkACell"; "view"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jd.SpineCallocS9.S9"; "fin_hyps"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "ltb"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy"; "liftA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1"; "RT_m1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "kSpaceSize"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "kAllocBegMagic"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM"; "IMG_M"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocInv ReprGlue Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Inv.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildSM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SMGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineCallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.GlueMZ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineCallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CallocArith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineCallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineCallocI2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CallocPosts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition sw9 (swc : list cell) : sobj := ltac2:(tb__ "0|0|
SeS4PaA1S4S9fA1S2Z0A1Vswc;ScA5").
Definition O_pccf : sobj := ltac2:(tb__ "0|2|
SeS86S2Z0A1M0S2Z4M1A1S38S3SbG0G1S8S52S4S85A1S2N1A1A3A3S3cS3A1A3ScA5").
Definition O_stf (scells : list cell) : sobj := ltac2:(tb__ "0|0|
SeSd9S2Zad0A1S2Zc60A1Vscells;ScA5").
Definition O_Hf (hcells : list cell) : sobj := ltac2:(tb__ "0|0|
SeS7aS2Z0A1S4S77A1Vhcells;ScA5").
Definition O_Pf (pcells : list cell) : sobj := ltac2:(tb__ "0|0|
SeS7bS2Z0A1S7cVpcells;ScA5").
Definition pcell : cell := ltac2:(tb__ "0|0|
SbS2Z0A1Z1S8S54S4PcA1S2Z7A1A3A3").
Definition hc_state : cell := ltac2:(tb__ "0|0|
SbS8S52S4S77A1S2N10A1A3Z1S2Z2A1A3").
Definition hc_size : cell := ltac2:(tb__ "0|0|
SbS8S52S4S77A1S2NcA1A3Z4S4PcA1A3").
Definition hc_sizehi : cell := ltac2:(tb__ "0|0|
SbS8S52S4S77A1S2NeA1A3Z2S2Z0A1A3").

Definition hc_magic : cell := ltac2:(tb__ "0|0|
SbS2Z0A1Z8S2Se8A1A3").
Definition hc_cptr : cell := ltac2:(tb__ "0|1|
SbS2Z8M0A1G0S8S52S8S52S7aS4S77A1A3S2N10A1A3A3").
Definition KEPT9 (W : list ulink) (swc : list cell) : list sobj := ltac2:(tb__ "0|0|
S3eS1S38S1Sc4Vswc;A1Sa0VW;A1A3S38S1S81S38S1S9dS38S1S9eS3cS1A1A3A3A3A3").
Definition R9 (scells hcells pcells : list cell) : list sobj := ltac2:(tb__ "0|0|
S3eS1Se5S38S1SbfS38S1S84S38S1S83S38S1Sc0Vscells;A1S38S1SbdVhcells;A1S38S1S80S38S1S7eS38S1S82S38S1SbeVpcells;A1S38S1S7fS3cS1A1A3A3A3A3A3A3A3A3A3A3A3").

Definition S2_of (F : axst) (K : list sobj) : sstate := ltac2:(tb__ "0|1|
S47VF;A1S15S22S29R1A1S89S2aR1A1S38S3bS3aS0A2M0S3dS3aS0U4S4P18A1A4S3cG0A1A3A2S27R1A1S26R1A1S2bR1A1VK;SaR1A1S9R1A1S28R1A1A9TS;").
Definition X9_of (F : axst) (K : list sobj) : axst := ltac2:(tb__ "0|1|
S50Sb3VF;VK;A2S38S3bS0S0A2M0S3dS0S0S78S4PcA1A4S3cG0A1A3S98A3").

Definition idxs9 (nW : nat) : list nat := ltac2:(tb__ "0|1|
S3eS3aS38S3aU0Sa8U1M0VnW;A2A3S3eS3aS38S3aSa7VnW;U26A2S38S3aSa7VnW;G0A2S38S3aSa7VnW;U2A2S3cS3aA1A3A3A3S3eS3aSa8Sa7VnW;U3A2U23A2Sa8Sa7VnW;U27A2U5A2A3A3A3").

Section Absorb.
Let segs : list Segment := segsA.
Lemma absorb_obj : ltac2:(tb__ "0|e|
S5S15S37SadA1M0Sd1SacS37S1A1M1G1S1S1cVsegs;R8R7S3dG0Sd2R6Sd3R5R4A2A4A4S2dG1SdR8A1S3eS1R4R3A3A3S56S1R3R4A3S66Q40M2S11RbS23R4A1A2A2S33S25RcR5A2S33S24RdR6A2S33Sc8ReR8RbA3S5S2eS2eS5aZ0M3S5dR4R3A2A2S2eS5aS5dR4R2A2S5eZ2Z40A2A2S5aR3R2A2A2A2S2eS3S56S3R1S1aR9A1A3S2eS5aR5S1dR11S17R2A1A2M4A2S2eS5aS5dG4S12R2A1A2R4A2S3aSe2R1S61S12R3A1A1A2S2dS40S67Q8M5A1M6A1M7ScfVsegs;SfR5A1M8S68G2S5dS5dR8S1dR13S17R4A1A2A2S65R2A1A2A2A3S3fG6SaaG6R2S19S61S12R4A1A1S11R13S1fR4A1A2A2S68G5G3A2M9A4A2A3F_;Fj;A2A2F_;Fc;S2eS2fS2dS1bS13R8A1MaScA3S2dS1bGaS1eA3MbA2S33S2eS5aR5R1A2S60R1R4A2A2McS32G6G6S2dG7ScfVsegs;G8S68G2S5dR8R3A2A2A3MdS3fG6R1A2A3Lx;A2F_;Foff;F_;GbS33GcS30S20R12S1aRbA1R2A3A1S2dG7GdS3fG6G9A2A3F_;F_;Foff;F_;A2A2A2Trho';Thi;Tlo;Tb;F_;F_;F_;Fo;FR;Fobjs;Fmd;Fms;Ftr;FS;Frho;").
Proof using.
  intros rho S tr ms md objs R o Hsm Ho Hin b lo hi rho'.
  destruct Hsm as (Hswf & Hpc & Hpend & Hhalt & Hrom & Hro & Hr & Hf & Hc & Hv & (Hall & Hpd & Hfr) & Hfa).
  cbn [fst snd cfg_ms cfg_model] in *.
  rewrite Ho in Hall. apply Forall_app in Hall as [_ HallR].
  pose proof (proj1 (Forall_forall _ _) HallR _ Hin) as Hoh.
  unfold obj_holds in Hoh. fold b lo hi in Hoh. cbn zeta in Hoh.
  destruct Hoh as (Hbnd & Hwv & Hcl & Hdf & _).
  assert (RNG : forall off, lo <= off < hi -> in_ranges rho R (Z_to_bv 64 (b + off))).
  { intros off Hoff. exists o. split; [exact Hin|]. unfold obj_range. fold b lo hi. cbn [fst snd]. rewrite u64_of_sum by lia. lia. }
  assert (CB : forall c, In c (ob_cells o) -> lo <= soff rho (c_off c) /\ soff rho (c_off c) + c_width c <= hi
            /\ forall j, (j < Z.to_nat (c_width c))%nat ->
                 rd ms (Z_to_bv 64 (b + soff rho (c_off c) + Z.of_nat j)) = Some (nth j (enc_bytes (Z.to_nat (c_width c)) (eval rho (SymState.c_val c))) (Z_to_bv 8 0))).
  { intros c Hcin. pose proof (proj1 (Forall_forall _ _) Hcl _ Hcin) as Hch. unfold cell_holds in Hch.
    destruct Hch as (Hc1 & Hc2 & Hrb). split; [exact Hc1|]. split; [exact Hc2|]. intros j Hj.
    pose proof (rd_bytes_nth ms (Z.to_nat (c_width c)) (oaddr rho (ob_base o) (soff rho (c_off c))) _ j Hrb Hj) as X.
    rewrite oaddr_unsigned in X by lia. fold b in X. apply X. lia. }
  split; [lia|]. split.
  - intros c Hcin. destruct (CB c Hcin) as (C1 & C2 & C3). split; [exact C1|]. split; [exact C2|]. intros j Hj.
    unfold rho'. rewrite (rd_of_absorb_in segs rho R ms _ Hrom) by (replace (b + soff rho (c_off c) + Z.of_nat j) with (b + (soff rho (c_off c) + Z.of_nat j)) by lia; apply RNG; lia).
    exact (C3 j Hj).
  - split.
    + intros Hd off Hoff. unfold rho'. rewrite (rd_of_absorb_in segs rho R ms _ Hrom (RNG off Hoff)).
      destruct (covered_dec rho (ob_cells o) off) as [Hcov|Hncov].
      * unfold covered in Hcov. apply Exists_exists in Hcov as (c & Hcin & Hic). unfold in_cell in Hic.
        destruct (CB c Hcin) as (C1 & C2 & C3).
        specialize (C3 (Z.to_nat (off - soff rho (c_off c))) ltac:(lia)).
        replace (b + soff rho (c_off c) + Z.of_nat (Z.to_nat (off - soff rho (c_off c)))) with (b + off) in C3 by lia.
        eexists. exact C3.
      * specialize (Hdf off Hoff Hncov). unfold dflt_holds in Hdf. destruct Hd as [Hd|Hd]; rewrite Hd in Hdf; [exact Hdf | eexists; exact Hdf].
    + intros Hd off Hoff Hncov. unfold rho'. rewrite (rd_of_absorb_in segs rho R ms _ Hrom (RNG off Hoff)).
      specialize (Hdf off Hoff Hncov). unfold dflt_holds in Hdf. rewrite Hd in Hdf. exact Hdf.
Qed.

Lemma absorb_defined : ltac2:(tb__ "0|4|
S5S15S37SadA1M0Sd1SacS37S1A1M1G1S67Q40M2A1S1cVsegs;R8R7S3dG0Sd2R6Sd3R5R4A2A4A4S2dG1SdR8A1S3eS1R4R3A3A3Sa9S1S1S2dS36S18S13R1A1A1S39A3Lo;R4A3Sc9RbR5R4A3S5aSe6S66G2R5A2A2S30S2dS40S67Q8A1M3A1SfSc8RdR7RaA3R6A2S42G3A1A3A1F_;F_;F_;F_;F_;Fa;FR;Fobjs;Fmd;Fms;Ftr;FS;Frho;").
Proof using.
  intros rho S tr ms md objs R a Hsm Ho HW Hin Ha.
  rewrite (rm_absorb_in rho R ms a Hin).
  destruct Hsm as (Hswf & Hpc & Hpend & Hhalt & Hrom & Hro & Hr & Hf & Hc & Hv & (Hall & Hpd & Hfr) & Hfa).
  cbn [fst snd cfg_ms cfg_model] in *.
  rewrite Ho in Hall. apply Forall_app in Hall as [_ HallR].
  destruct Hin as (o & Hoin & Hr'). pose proof (proj1 (Forall_forall _ _) HallR _ Hoin) as Hoh.
  pose proof (proj1 (Forall_forall _ _) HW _ Hoin) as Wo. cbn beta in Wo.
  unfold obj_holds in Hoh. cbn zeta in Hoh. destruct Hoh as (Hbnd & Hwv & _).
  unfold obj_range in Hr'. cbn [fst snd] in Hr'.
  specialize (Hwv (bv_unsigned a - bv_unsigned (eval rho (ob_base o))) ltac:(unfold obj_lo_of, obj_hi_of in *; lia) Wo).
  replace (bv_unsigned (eval rho (ob_base o)) + (bv_unsigned a - bv_unsigned (eval rho (ob_base o)))) with (bv_unsigned a) in Hwv by lia.
  rewrite Z_to_bv_bv_unsigned in Hwv. unfold wview in Hwv.
  destruct (ms_mem ms a) as [bt|] eqn:Em; [discriminate|].
  pose proof (urange a). unfold segs in Hwv. rewrite (find_segment_A_off (bv_unsigned a)) in Hwv by (unfold IMG_HI in Ha; lia). exfalso. apply Hwv. reflexivity.
Qed.
End Absorb.

Section Civ.
Let segs : list Segment := segsA.
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Hypothesis law_die : ltac2:(tb__ "0|0|
S6aS5S37S67Q40A1A1SacVAInv;R4R3R2R1A4SdaSddVsegs;SfR4A1A2SdcZ17fbdcU4Z0A3A2F_;Fmd;Ftp;Frho;FA;").

Lemma N_m1_civ : ltac2:(tb__ "0|5|
S6aS5S37S67Q40M0A1M1A1SacVAInv;R4R3R2R1A4S2dG1S7R4P97A2S68G0S71S6bR5A1A1A2A3S2dG1S7R5P98A2S68G0S6eS6bR6A1A1A2A3S2dG1S7R6P99A2S68G0S70S6bR7A1A1A2A3S2dG1S7R7P9aA2S68G0S6fS6bR8A1A1A2A3S2dG1S7R8P9bA2S68G0S6dS6bR9A1A1A2A3S2dG1S7R9P9cA2S68G0S5dS6dS6bRaA1A1Se7A2A2A3Sa9Sd7Sd7S3bS3bS3bS0S33A2M2S33A2M3S37S3bS3bS33S3aA2S0A2A1M4A2OLk;R1G3G4G3OLp;R2G2S33G2OLp0;R2S0S33Sd0R11ScfVsegs;SfR11A1A2S66G0S11R11R2A2A2R5A4Llo;Lbase;X3bx1Lhi;Lp0;X3bx1Lcs;Lp;X3bx1Lk;Sa6A3F_;F_;F_;F_;F_;F_;F_;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md HA E151 E152 E153 E154 E155 E156.
  pose proof HA as (HG & HR & HF & HRest & HM).
  pose proof (topG_range (aa_geom A)) as ACV.
  pose proof HG as HG0. pose proof (geom_old _ HG0) as HG'. rewrite FS_total_val, kSpaceSize_val in HG'. unfold HIGH_SHADOW_END, IMG_HI, PG in HG'.
  destruct HG' as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22 & G23 & G24).
  clear G15 G16 G17 G18 G19 G20 G21.
  destruct HRest as (Hsep & _ & _ & _ & _ & _ & _ & HTH & HMI). unfold thread_inv in HTH. destruct HTH as [HTH HTS].
  rewrite maskv_out in HTH by (apply fs_footb_thread; [exact HG0 | lia]).
  destruct HMI as [HMIc _]. pose proof (Forall_inv (Forall_inv_tail HMIc)) as HPP.
  assert (HPP' : cell_ok (view segs (rm rho)) (mkACell (0 + 0xeb90d) 1 1)).
  { intros j Hj. specialize (HPP j Hj). cbn [c_addr c_w c_val] in HPP, Hj |- *. rewrite Z.add_0_l.
    rewrite maskv_out in HPP; [exact HPP | apply fs_footb_img; [exact HG0 | lia]]. }
  pose proof (law_die A rho tp _ HA) as HDIE.
  assert (HDIE' : cell_ok (view segs (rm rho)) (mkACell (0 + 0x17fbdc) 4 0)) by (rewrite Z.add_0_l; exact HDIE).
  pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HMIc))) as HCSD.
  assert (HCSD' : cell_ok (view segs (rm rho)) (mkACell (0 + 0x17fcd8) 4 0)).
  { intros j Hj. specialize (HCSD j Hj). cbn [c_addr c_w c_val] in HCSD, Hj |- *. rewrite Z.add_0_l.
    rewrite maskv_out in HCSD; [exact HCSD | apply fs_footb_img; [exact HG0 | lia]]. }
  unfold N_m1, N_rest, N_fn, N_m5. cbn [tl app]. unfold vT, vCTX, vTOP, vBOT, vSB, vRIS.
  repeat apply Forall_cons; try apply Forall_nil; cbn [eval]; rewrite ?E151, ?E152, ?E153, ?E154, ?E155, ?E156, ?u64_lit by lia.

  all: first [ exact (civ_cell rho (rm rho) 0 0xeb90d 1 1 (SLit 1) HPP' eq_refl ltac:(lia) ltac:(lia))
             | exact (civ_cell rho (rm rho) 0 0x17fbdc 4 0 (SLit 0) HDIE' eq_refl ltac:(lia) ltac:(lia))
             | exact (civ_cell rho (rm rho) 0 0x17fcd8 4 0 (SLit 0) HCSD' eq_refl ltac:(lia) ltac:(lia))
             | (intros j Hj; replace j with 0%nat by lia; rewrite nth0_enc1_zero'; cbn [Z.of_nat]; rewrite Z.add_0_r; rewrite <- view_in by lia; exact HTH)
             | civ_any2 HR ].
Qed.
End Civ.

Lemma In_of_cellb : ltac2:(tb__ "0|0|
S3S37S3A1S2dS36S59S3S4dR2A1R1A3S39A3S56S3R3R2A3F_;Fl;Fc;").
Proof. intros c l H. apply existsb_exists in H as (c' & Hin & E). apply cell_eqb_sound in E. subst c'. exact Hin. Qed.

Lemma nth0_enc1_two' : ltac2:(tb__ "0|3|
S2dS67Q8M0A1M1SaaG1U0S19U1S68Q40Z2M2A2A2S68G0Z0A2A4S68G0G2A2A3").
Proof. reflexivity. Qed.

Definition tyv (x : sv) (a : Z) : sv := ltac2:(tb__ "0|0|
S8S54S8S55S8S54S8S52S8S54Vx;S2ZfffffffffffffffcA1A3S2Z1A1A3S2Z8fA1A3S2Va;A1A3S2Zf3A1A3").
Definition hc_type (x : sv) (a : Z) : cell := ltac2:(tb__ "0|0|
SbS8S52S4S77A1S2NfA1A3Z1SbbVx;Va;A2A3").

Definition ty_of_cell (c : cell) : option (sv * Z) := ltac2:(tb__ "0|19|
S3S40S3bS0S33A2M0A1M1Lc;Vc;S0S33S0S33G1Lc_width;R2S42G0A1M2S34S34G1Lp;R1S34G2Lp0;M3G3S0G1Lc_val;R2S33G2Lz;M4S34G2Li;M5S51S0S0S51G1Lop;R3G2G2G2G2G2G2G2G2G2S0G1La0;R2G4G5S51S0S0S51G1Lop0;R3G2G2G2G2G2G2G2G2S0G1La1;R2G4G5S51S0S0S51G1Lop1;R3G2G2G2G2G2G2G2G2G2S0G1La2;R2G4G5S51S0S0S51G1Lop2;R3S0G1La3;R2G4G5S51S0S0S51G1Lop3;R3G2G2G2G2G2G2G2G2G2S0G1Lb3;R1S33S0G1Lb2;R5S33S0G1Lb1;R9S33S0G1Lb0;RdS33S0G1Lb;R11S33S36G1L_;S2cR18S8S52S4S77A1S2NfA1A3A2S3fG0S3dS0S33R7R2A4A2G2X36x2Lz2;G5S51S0S0G2Lb4;M6La4;M7Lop4;M8G8S53G7Lop4;M9G9S36S35S0G2La4;Lw;Lsgn;S34S0S33G2Lk;Li;Ll;MaX0x8La;G5S51S0G6La;MbLop4;McGcS53GbLop4;MdGdS36S35S0G2La;Lw;Lsgn;MeGaX0x8Lz1;G5GcGcGdGdGeGaX0x8Lz0;G5GcGcGdGdGeGaX0x8Lz;G5GcGcGdGdGeGaX0x8X51xaLb3;Lx;Lop3;S51S0S0G2Lb3;La;MfLop3;S53GfLop3;M10G10GeGaX0x8G2G2G2G2G2G2G2G2G2X51xaLb2;La3;Lop2;S51S0S0G2Lb2;La;M11Lop2;S53G11Lop2;M12G12GeGaX0x8X51xaLb1;La2;Lop1;S51S0S0G2Lb1;La;M13Lop1;S53G13Lop1;M14G14GeGaX0x8G2X51xaLb0;La1;Lop0;S51S0S0G2Lb0;La;M15Lop0;S53G15Lop0;M16G16GeGaX0x8X51xaLb;La0;Lop;S51S0S0G2Lb;La;M17Lop;S53G17Lop;M18G18GeGaX0x8X34x3Lp;S34G2Lp;X33x3Lc_val;Lc_width;Loff;X3x1").
Fixpoint ty_of (l : list cell) : sv * Z :=
  match l with [] => (SLit 0, 0) | c :: r => match ty_of_cell c with Some p => p | None => ty_of r end end.
Lemma land_mod4 : ltac2:(tb__ "0|2|
S33S33S5aZ0R2A2M0G0S2dS33S5bS5cR4R3A2Z4M1A2S5cS5bR4G1A2S5bR3G1A2A2A3F_;F_;Fb;Fa;").
Proof.
  intros a b Ha Hb. change 4 with (2 ^ 2). rewrite <- !Z.land_ones by (try apply Z.land_nonneg; lia).
  apply Z.bits_inj'. intros n Hn. rewrite !Z.land_spec.
  destruct (Z.testbit a n), (Z.testbit b n), (Z.testbit (Z.ones 2) n); reflexivity.
Qed.
Lemma lor_mod4 : ltac2:(tb__ "0|2|
S33S33S5aZ0R2A2M0G0S2dS33S5bS5fR4R3A2Z4M1A2S5fS5bR4G1A2S5bR3G1A2A2A3F_;F_;Fb;Fa;").
Proof.
  intros a b Ha Hb. change 4 with (2 ^ 2). rewrite <- !Z.land_ones by (try apply Z.lor_nonneg; lia).
  apply Z.bits_inj'. intros n Hn. rewrite ?Z.land_spec, ?Z.lor_spec, ?Z.land_spec.
  destruct (Z.testbit a n), (Z.testbit b n), (Z.testbit (Z.ones 2) n); reflexivity.
Qed.
Lemma tyZ_mod4 : ltac2:(tb__ "0|3|
S33S33S5aZ0M0R2A2M1G1S2dS33S5cR3Z3A2G0A3S2dS33S5bS5cS5fS5cS69Q40S5dS5cR5ZfffffffffffffffcA2Z1M2A2A2Z8fA2R4A2Zf3A2Z4A2G2A3F_;F_;F_;Fa;Fx;").
Proof.
  intros x a Hx Ha Ha3.
  assert (L0 : 0 <= Z.land x 18446744073709551612) by (apply Z.land_nonneg; lia).
  assert (M0 : (Z.land x 18446744073709551612) mod 4 = 0).
  { rewrite land_mod4 by lia. change (18446744073709551612 mod 4) with 0. apply Z.land_0_r. }
  set (y := Z.land x 18446744073709551612) in *.
  assert (M1 : (bv_wrap 64 (y + 1)) mod 4 = 1 /\ 0 <= bv_wrap 64 (y + 1)).
  { unfold bv_wrap. change (bv_modulus 64%N) with (4 * 2 ^ 62).
    pose proof (Z.div_mod (y + 1) (4 * 2 ^ 62) ltac:(lia)) as D. pose proof (Z.mod_pos_bound (y + 1) (4 * 2 ^ 62) ltac:(lia)) as B.
    pose proof (Z.div_mod y 4 ltac:(lia)) as D4. rewrite M0 in D4.
    set (r := (y + 1) mod (4 * 2 ^ 62)) in *. set (q := (y + 1) / (4 * 2 ^ 62)) in *.
    split; [|lia]. symmetry. apply Z.mod_unique with (q := y / 4 - q * 2 ^ 62); lia. }
  destruct M1 as [M1 W].
  rewrite land_mod4 by (try apply Z.lor_nonneg; try split; try apply Z.land_nonneg; lia).
  rewrite lor_mod4 by (try apply Z.land_nonneg; lia).
  rewrite land_mod4 by lia. rewrite M1.
  change (143 mod 4) with 3. change (243 mod 4) with 3.
  replace (a mod 4) with 0.
  2: { change 4 with (2 ^ 2). rewrite <- Z.land_ones by lia. change (Z.ones 2) with 3. symmetry. exact Ha3. }
  reflexivity.
Qed.
Lemma tyv_sound : ltac2:(tb__ "0|1|
S5S0S33S2eS5aZ0M0R1A2S60R1S5eZ2Z40A2A2A2S2dS33S5cR2Z3A2G0A3S2dS33S5bS66Q40S11R5SbbR4R3A2A2A2Z4A2Z1A3F_;F_;Fa;Fx;Frho;").
Proof.
  intros rho x a Ha Ha3. unfold tyv. cbn [eval]. unfold alu64, alu.
  rewrite bv_and_unsigned, bv_or_unsigned, bv_and_unsigned, bv_add_unsigned, bv_and_unsigned.
  rewrite !Z_to_bv_unsigned. change (bv_wrap 64 18446744073709551612) with 18446744073709551612.
  change (bv_wrap 64 1) with 1. change (bv_wrap 64 143) with 143. change (bv_wrap 64 243) with 243.
  replace (bv_wrap 64 a) with a by (unfold bv_wrap; rewrite Z.mod_small; [reflexivity | exact Ha]).
  apply tyZ_mod4; [pose proof (bv_unsigned_in_range 64 (eval rho x)); lia | lia | exact Ha3].
Qed.
Definition tya_okb (a : Z) : bool := ltac2:(tb__ "0|1|
S43S43S63Z0M0Va;A2S64Va;S5eZ2Z40A2A2A2S62S5cVa;Z3A2G0A2A2").
Lemma tya_okb_sound : ltac2:(tb__ "0|1|
S33S2dS36SbaR1A1S39A3S2eS2eS5aZ0M0R2A2S60R2S5eZ2Z40A2A2A2S2dS33S5cR2Z3A2G0A3A2F_;Fa;").
Proof. intros a H. unfold tya_okb in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.eqb_eq in H3. lia. Qed.
Lemma R9_writable : ltac2:(tb__ "0|1|
S37S3A1M0G0G0Sa9S1S1S2dS36S18S13R1A1A1S39A3Lo;Sb4R3R2R1A3A3Fpc;Fhc;Fsc;").
Proof. intros. unfold R9, RT_m1. cbn. repeat (apply Forall_cons; [reflexivity|]). apply Forall_nil. Qed.

Section S9.
Variable nW : nat. Variable st : ustop. Variable tmax : Z.
Let W : list ulink := Wcan nW.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
S33SdbVCST;R1A2SdbSe9R2A2S31F_;F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let J (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|0|
S9cVAInv;VW;Vst;VA;VKc;S4PcA1A6").
Hypothesis law_die : ltac2:(tb__ "0|0|
S6aS5S37S67Q40A1A1SacVAInv;R4R3R2R1A4SdaSddVsegs;SfR4A1A2SdcZ17fbdcU4Z0A3A2F_;Fmd;Ftp;Frho;FA;").

Section B14.

Variable F : axst.
Variables swc scells hcells : list cell.
Variable partial : bool.
Let pcells : list cell := ltac2:(tb__ "0|1|
S36S37S3A1Lpartial;Vpartial;S38S3Sb9S3cS3A1M0A3G0X36x2").
Let K : list sobj := KEPT9 W swc.
Let R : list sobj := ltac2:(tb__ "0|0|
Sb4Vscells;Vhcells;Vpcells;A3").
Hypothesis SEL9 : ltac2:(tb__ "0|0|
S2dS37S1A1Sd5SdS47VF;A1A1Sb2VnW;A1A2S3eS1VK;VR;A3A3").
Hypothesis ND9 : ltac2:(tb__ "0|0|
S2dS36Sd4Sb2VnW;A1A1S39A3").
Hypothesis BND9 : ltac2:(tb__ "0|0|
S2dS36S57S3aS3aSe0R1S41S1SdS47VF;A1A1A2A2Li;Sb2VnW;A1A3S39A3").
Hypothesis COV9 : ltac2:(tb__ "0|0|
S2dS36S57S3aS3aS59S3aSdfR1A1Sb2VnW;A1A3Li;Sa8U0S41S1SdS47VF;A1A1A2A2A3S39A3").
Hypothesis XF : ax_X F = [].
Hypothesis BF9 : ax_base F = base_sv.
Hypothesis HCs : In hc_state hcells.
Hypothesis HCn : In hc_size hcells.
Hypothesis HC0 : In hc_sizehi hcells.
Variables (tyx : sv) (tya : Z).
Hypothesis HCt : ltac2:(tb__ "0|0|
S56S3Sb8Vtyx;Vtya;A2Vhcells;A3").
Hypothesis HTA : tya_okb tya = true.
Hypothesis HMG : ltac2:(tb__ "0|0|
S2fS56S6S10S4S77A1S2Z10A1A2SaS47VF;A1A1A3S2eS56S3Sb7Vhcells;A3S56S3Sb6Vhcells;A3A2A2").
Hypothesis FG9 : ltac2:(tb__ "0|0|
S58S6S79SaS47VF;A1A1A3").
Hypothesis FP9 : ltac2:(tb__ "0|0|
S58S6S3eS6S9bVW;Vst;A2S9aS99A1A3SaS47VF;A1A1A3").
Hypothesis W9 : ltac2:(tb__ "0|0|
S2dS36S16Sb3VF;VK;A2A1S39A3").
Hypothesis D9 : ltac2:(tb__ "0|4|
S2dS40S3bS37S3bS0S0A2M0A1M1S37S6A1M2A2M3A1SceSd6S47VF;A1VK;A2Sb3VF;VK;A2A2S3fG3S3dG1G2S38G0S3dS0S0S2Sd8A1S4P18A1A4S3cG0A1A3S3cS6A1A4A2A3").
Hypothesis XB9 : ltac2:(tb__ "0|0|
S2dS36S4aS9S47VF;A1A1S3dS0S0S78S4PcA1A4A2S39A3").
Variable s9 : wsub.
Hypothesis ENT9 : ltac2:(tb__ "0|0|
S2dS36S49Sb5VF;VK;A2S8eVW;Vst;A2Vs9;A3S39A3").
Hypothesis SID9 : ltac2:(tb__ "0|0|
S2dS36Sc7Vs9;S88A2S39A3").
Hypothesis G110 : ltac2:(tb__ "0|0|
S2dS0Sc6Vs9;S97A2S78A3").
Hypothesis G143 : wsub_get s9 143%positive = SVar 143.
Hypothesis G144 : wsub_get s9 144%positive = SVar 144.

Theorem calloc_finish_P : ltac2:(tb__ "0|5|
S6aS6aS93S5S5S33OF_;S5S37S67Q40M0A1A1M1G1S90S37S3bS48S72A2M2A1S56G2S3dS48S72S8eVW;Vst;A2S8fVCST;VXGL;RbR9A4A4R1A3S92VW;Vst;A2S94RbA1Sa2ReRdA2Sa3RaRcRbA3S33S2fS95VCST;R11R1A3S96VCST;VXGL;R11R1A4A2RdR2A1F_;Fa;S5aZ1Sa4R10S66G0S7RdPcM3A2A2A2A2S6cR11A1S36OLpartial;Vpartial;S30S2dS33S5bS66G0S7RfG3A2A2Z8A2Z0A3M4A1G4X36x2S8aVsegs;Sa1VW;Vst;R13R12R10A5VF;ReRcRbA6S73Vsegs;S88R12ReRbRcA6F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FPosts;Fw;Ftp;Ftp0;FrhoE;Fkeep;Frho;Frho0;FKc;FA;FA0;").
Proof.
  intros A0 A Kc rho0 rho keep rhoE tp0 tp w Posts HPin HW HKc HDO HL HKEEP Hcnt HPRM Hpar H.
  destruct w as [tr [ms md]].
  pose proof H as [HsmA [Hag HJ]]. pose proof Hag as (Hagw & Hagl & Hagm).
  pose proof HJ as (HA & HK & Htp & HU & HB & HN & Htop). cbn [w_tr w_cfg cfg_model fst snd] in HA, HK, Htp, HU, HB, HN.
  pose proof (JGb_pvals nW st A Kc rho rhoE tp _ F H FG9 Hcnt) as PV. cbn zeta in PV.
  set (nv := bv_unsigned (rw rho 12%positive)) in *.
  pose proof PV as (E12 & E148 & E150 & E155 & E158 & E159 & Bn & Bsz & Brz & Bfit & BSB & Bc & Bx & Btop).
  set (SB := ag_spacebeg (aa_geom A)) in *. set (c := cls_of nv) in *. set (x := chk_of A nv) in *. set (sz := Size c) in *.
  set (ab := SB + c * 2 ^ 32 + 16 * x). set (ub := ab + rz nv). set (ue := ub + nv).
  set (G := aa_geom A) in *. set (T := ag_thread G). set (pce := T + 0xd0 + 80 * c). set (cnt := cnt_of A nv) in *.
  assert (E151 : rw rhoE 151%positive = Z_to_bv 64 T). { rewrite <- (Hagw 151%positive) by (unfold GW; lia). reflexivity. }
  assert (E152 : rw rhoE 152%positive = Z_to_bv 64 (ag_ctx G)). { rewrite <- (Hagw 152%positive) by (unfold GW; lia). reflexivity. }
  assert (E153 : rw rhoE 153%positive = Z_to_bv 64 (ag_stack_top G)). { rewrite <- (Hagw 153%positive) by (unfold GW; lia). reflexivity. }
  assert (E154 : rw rhoE 154%positive = Z_to_bv 64 (ag_stack_bottom G)). { rewrite <- (Hagw 154%positive) by (unfold GW; lia). reflexivity. }
  assert (E156 : rw rhoE 156%positive = Z_to_bv 64 (SB + kSpaceSize)). { rewrite <- (Hagw 156%positive) by (unfold GW; lia). reflexivity. }
  assert (E149 : rw rhoE 149%positive = Z_to_bv 64 cnt). { rewrite <- (Hagw 149%positive) by (unfold GW; lia). reflexivity. }
  assert (Erm : rm rhoE = rm rho). { apply functional_extensionality. intros a. symmetry. exact (Hagm a). }
  pose proof HA as (HG & HR & _). pose proof (geom_numsS _ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & _). fold G in G3, G5. fold G T in G4, G5. pose proof (topG_range G) as ACV.
  pose proof (cls_facts nv ltac:(lia)) as (C1 & _ & _ & C4). fold c in C1, C4.
  assert (GS2 : SB + 2 ^ 37 + 4096 <= 140737479966720).
  { pose proof (geom_old _ HG) as X. rewrite kSpaceSize_val in X. unfold SB, G in *. clear -X ACV.
    destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X14 & _). lia. }
  assert (CNT16 : cnt <= 16) by exact (proj1 (proj2 (proj2 (proj2 (proj2 (pc_entry_facts segs A rhoE tp md nv HA ltac:(lia) Hcnt)))))).

  pose proof (pv_ab rhoE _ _ _ _ _ _ PV) as Eab. pose proof (pv_ub rhoE _ _ _ _ _ _ PV) as Eub. pose proof (pv_ue rhoE _ _ _ _ _ _ PV) as Eue.
  pose proof (pv_bsh rhoE _ _ _ _ _ _ PV) as Ebsh. pose proof (pv_bu rhoE _ _ _ _ _ _ PV) as Ebu. pose proof (pv_lu rhoE _ _ _ _ _ _ PV) as Elu.
  pose proof (pv_lp rhoE _ _ _ _ _ _ PV) as Elp. pose proof (pv_lt rhoE _ _ _ _ _ _ PV) as Elt. pose proof (pv_bp rhoE _ _ _ _ _ _ PV) as Ebp.
  pose proof (pv_br rhoE _ _ _ _ _ _ PV) as Ebr. pose proof (pv_lr rhoE _ _ _ _ _ _ PV) as [Elr Blr]. pose proof (r8_facts rhoE _ _ _ _ _ _ PV) as R8F.
  cbn zeta in Eab, Eub, Eue, Ebsh, Ebu, Elu, Elp, Elt, Ebp, Ebr, Elr, Blr, R8F. fold ab in Eab, Eub, Eue, Ebsh, Ebu, Ebp, Ebr. fold ub in Eub, Eue, Ebu, Ebp, Ebr.
  set (r8 := nv + 7 - (nv + 7) mod 8) in *. set (lp := if Z.eq_dec (nv mod 8) 0 then 0 else 1) in *.
  assert (EB : bv_unsigned (eval rhoE pc_base) = pce).
  { unfold pc_base, vT, V_CLS. cbn [eval]. rewrite E151, E158. rewrite add_val, add_val, mul_val, !u64_lit by lia.
    rewrite (Z.mod_small (c * 80)) by lia. rewrite (Z.mod_small (T + 208)) by lia. rewrite Z.mod_small by lia. unfold pce. lia. }
  assert (ET : bv_unsigned (eval rhoE vT) = T). { unfold vT. cbn [eval]. rewrite E151. apply u64_lit. lia. }
  assert (ECH : soff rhoE choff = 16 + 4 * (cnt - 1)).
  { unfold choff, V_CNT. rewrite soff_snorm. unfold U. cbn [eval]. rewrite E149. rewrite add_val, sll_val, add_val, !u64_lit by lia.
    replace (bv_unsigned (Z_to_bv 64 (-1))) with (2 ^ 64 - 1) by reflexivity.
    replace ((cnt + (2 ^ 64 - 1)) mod 2 ^ 64) with (cnt - 1) by (rewrite <- (Z.mod_add _ (-1)) by lia; rewrite Z.mod_small by lia; lia).
    change (2 mod 64) with 2. rewrite ?u64_lit by lia. rewrite Z.shiftl_mul_pow2 by lia. rewrite (Z.mod_small (_ * 2 ^ 2)) by lia. rewrite Z.mod_small by lia.
    unfold snorm. rewrite Z.mod_small by lia. destruct (Z.ltb_spec ((cnt - 1) * 2 ^ 2 + 16) (2 ^ 63)); lia. }
  assert (ERZ : soff rhoE (SVar V_RZ) = rz nv). { apply soff_of_val; [|lia]. cbn [eval]. unfold V_RZ. rewrite E150. apply u64_lit. lia. }
  idtac "mf:1".

  set (KJ := (fun (_ : valuation) (_ : list word) (t : list event) (m : Model) => Kc t m) : jpredA).
  assert (Ha : SPA segs KJ F rhoE tp (tr, {| cfg_ms := ms; cfg_model := md |})) by (split; [exact HsmA | exact HK]).
  pose proof (SPA_select segs KJ rhoE F (idxs9 nW) tp _ Ha ND9
                ltac:(intros i Hi; apply Nat.ltb_lt; exact (proj1 (forallb_forall _ _) BND9 i Hi))
                ltac:(intros i Hi; pose proof (proj1 (forallb_forall _ _) COV9 i ltac:(apply in_seq; lia)) as X;
                      apply existsb_exists in X as (i' & Hi' & E); apply Nat.eqb_eq in E; subst i'; exact Hi')) as Hsel.
  rewrite SEL9 in Hsel. clear Ha.

  pose proof (SPA_unobj segs KJ rhoE (ax_setS F (set_objs (ax_S F) (K ++ R))) K R tp tr ms md eq_refl Hsel (fun k => k)) as Hb.
  cbn zeta in Hb. set (rho3 := rho_absorb rhoE R (vms md tp ms)) in *.
  pose proof (proj1 (proj1 Hsel)) as Hsm1. unfold virt in Hsm1. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S ax_setS] in Hsm1.
  idtac "mf:2".

  destruct (proj1 (Z.mod_divide (rz nv) 16 ltac:(clear -ACV; lia)) ltac:(clear -Brz; tauto)) as [qr Hqr].
  destruct (proj1 (Z.mod_divide sz 16 ltac:(clear -ACV; lia)) ltac:(clear -Bsz; tauto)) as [qs Hqs].
  assert (AB8 : ab mod 8 = 0).
  { apply Z.mod_divide; [clear -ACV; lia|]. destruct (proj1 (Z.mod_divide SB (2 ^ 16) ltac:(clear -ACV; lia)) ltac:(clear -BSB; tauto)) as [q Hq].
    exists (q * 2 ^ 13 + c * 2 ^ 29 + 2 * x). unfold ab. clear -Hq. lia. }
  assert (EShub : Sh ub = Sh ab + 2 * qr).
  { unfold ub. rewrite (Sh_SB ab (rz nv) AB8). rewrite Hqr. replace (qr * 16 / 8) with (2 * qr) by (clear -ACV; apply Z.div_unique with 0; lia). reflexivity. }
  pose proof (Z.div_mod nv 8 ltac:(clear -ACV; lia)) as DMn. pose proof (Z.mod_pos_bound nv 8 ltac:(clear -ACV; lia)) as MBn.
  set (qn := nv / 8) in *.
  assert (Er8 : r8 / 8 = qn + lp /\ (sz - rz nv - r8) / 8 = 2 * qs - 2 * qr - qn - lp /\ sz / 8 = 2 * qs /\ rz nv / 8 = 2 * qr /\ 0 <= lp <= 1
               /\ nv <= 8 * qn + 8 * lp /\ 8 * qn + 8 * lp + rz nv <= sz).
  { destruct R8F as (R1 & R2 & R3 & R4). unfold lp in *.
    destruct (Z.eq_dec (nv mod 8) 0) as [Ez|Nz].
    - rewrite R4. rewrite Hqs, Hqr. repeat split.
      1-4: symmetry; apply Z.div_unique with 0; clear -ACV; lia.
      + clear -ACV; lia. + clear -ACV; lia.
      + clear -DMn Ez. lia.
      + rewrite R4, Hqs, Hqr in Blr. clear -Blr DMn Ez Bfit Hqs Hqr. lia.
    - rewrite R4. rewrite Hqs, Hqr. repeat split.
      1-4: symmetry; apply Z.div_unique with 0; clear -ACV; lia.
      + clear -ACV; lia. + clear -ACV; lia.
      + clear -DMn MBn. lia.
      + rewrite R4, Hqs, Hqr in Blr. clear -Blr DMn MBn Bfit Hqs Hqr. lia. }
  destruct Er8 as (Er8a & Er8b & Esz8 & Erz8 & Blp & Bn8 & Bfit8).
  idtac "mf:3".

  set (P10 := [O_pccf; O_pcs; O_pck; O_stf scells; O_Hf hcells; O_T; O_L; O_Uz; O_Pf pcells; O_R]).
  assert (ER : R = RT_m1 ++ P10) by reflexivity.
  assert (RG1 : obj_range rhoE O_pccf = (pce, pce + 4)).
  { unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi O_pccf]. rewrite !soff_lit_small by (clear -ACV; lia). rewrite EB. apply f_equal2; clear; lia. }
  assert (RG2 : obj_range rhoE O_pcs = (pce + 8, pce + 16)).
  { unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi O_pcs]. rewrite !soff_lit_small by (clear -ACV; lia). rewrite EB. reflexivity. }
  assert (RG3 : obj_range rhoE O_pck = (pce + 16 + 4 * (cnt - 1), pce + 80)).
  { unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi O_pck]. rewrite !soff_lit_small by (clear -ACV; lia). rewrite EB, ECH. apply f_equal2; clear; lia. }
  assert (RG4 : obj_range rhoE (O_stf scells) = (T + 2768, T + 3168)).
  { unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi O_stf]. rewrite !soff_lit_small by (clear -ACV; lia). rewrite ET. reflexivity. }
  assert (RG5 : obj_range rhoE (O_Hf hcells) = (ab, ub)).
  { unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi O_Hf]. rewrite !soff_lit_small by (clear -ACV; lia). rewrite Eab, ERZ. apply f_equal2; [clear; lia | unfold ub; clear; lia]. }
  assert (RG6 : obj_range rhoE O_T = (ue, ab + sz)).
  { unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi O_T]. rewrite !soff_lit_small by (clear -ACV; lia). rewrite Eue.
    rewrite (soff_of_val rhoE LTe _ Elt) by (clear -Bfit Bsz Bn Brz; lia). fold ue. apply f_equal2; [clear; lia | unfold ue, ub; clear; lia]. }
  assert (ELL : bv_unsigned (eval rhoE LLe) = 2 * qr).
  { unfold LLe. cbn [eval]. unfold V_RZ. rewrite E150, srl_val, !u64_lit by (clear -Brz; lia). change (3 mod 64) with 3. rewrite Z.shiftr_div_pow2 by (clear; lia). exact Erz8. }
  assert (RG7 : obj_range rhoE O_L = (Sh ab, Sh ab + 2 * qr)).
  { unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi O_L]. rewrite !soff_lit_small by (clear -ACV; lia). rewrite Ebsh.
    rewrite (soff_of_val rhoE LLe (2 * qr) ELL) by (clear -Brz Hqr; lia). apply f_equal2; clear; lia. }
  assert (RG8 : obj_range rhoE O_Uz = (Sh ub, Sh ub + qn)).
  { unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi O_Uz]. rewrite !soff_lit_small by (clear -ACV; lia). rewrite Ebu.
    rewrite (soff_of_val rhoE LUe qn Elu) by (clear -Bn DMn MBn; lia). apply f_equal2; clear; lia. }
  assert (RG9 : obj_range rhoE (O_Pf pcells) = (Sh ub + qn, Sh ub + qn + lp)).
  { unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi O_Pf]. rewrite !soff_lit_small by (clear -ACV; lia). rewrite Ebp.
    rewrite (soff_of_val rhoE LPe lp Elp) by (clear -Blp; lia). fold qn. apply f_equal2; clear; lia. }
  assert (RG10 : obj_range rhoE O_R = (Sh ub + qn + lp, Sh ab + 2 * qs)).
  { unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi O_R]. rewrite !soff_lit_small by (clear -ACV; lia). rewrite Ebr.
    rewrite (soff_of_val rhoE LRe _ Elr) by (rewrite Er8b; clear -Blp Bfit8 Hqs Hqr Bsz Brz DMn MBn Bn; lia). rewrite Er8a, Er8b, EShub. apply f_equal2; clear; lia. }
  assert (PIN : forall o z, In o P10 -> fst (obj_range rhoE o) <= z < snd (obj_range rhoE o) -> chg_m G pce ab ub ue sz cnt z).
  { intros o z Ho Hz. unfold chg_m. fold T. rewrite Esz8. unfold P10 in Ho.
    destruct Ho as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]];
      first [rewrite RG1 in Hz | rewrite RG2 in Hz | rewrite RG3 in Hz | rewrite RG4 in Hz | rewrite RG5 in Hz
            | rewrite RG6 in Hz | rewrite RG7 in Hz | rewrite RG8 in Hz | rewrite RG9 in Hz | rewrite RG10 in Hz];
      cbn [fst snd] in Hz; rewrite ?EShub in Hz;
      clear -Hz Blp Bn8 Bfit8 Hqr Hqs Hcnt CNT16 DMn MBn Bn Brz Bsz Bfit; unfold ub, ue in *; lia. }
  idtac "mf:4".

  set (v3 := view segs (rm rho3)). set (vE := view segs (rm rhoE)).
  assert (AO : forall o, In o R -> _) by (intros o Ho; exact (absorb_obj rhoE _ tr (vms md tp ms) (vmd md) K R o Hsm1 eq_refl Ho)).
  assert (INP : forall o, In o P10 -> In o R) by (intros o Ho; rewrite ER; apply in_or_app; right; exact Ho).
  assert (P1 : In O_pccf P10) by (unfold P10; cbn; tauto).
  assert (P2 : In O_pcs P10) by (unfold P10; cbn; tauto).
  assert (P5 : In (O_Hf hcells) P10) by (unfold P10; cbn; tauto).
  assert (P8 : In O_Uz P10) by (unfold P10; cbn; tauto).
  assert (P9 : In (O_Pf pcells) P10) by (unfold P10; cbn; tauto).
assert (PCEB : 4096 <= pce /\ pce + 80 <= 140737479966720) by (unfold pce; clear -G4 G5 C1 ACV; lia).
  assert (ABB : 17594333495296 <= ab /\ ab + sz <= 140737479966720 /\ 16 <= rz nv /\ nv + rz nv <= sz) by (unfold ab; clear -BSB Bc Bx Btop Brz Bfit; lia).
  assert (VC : cell_ok v3 (mkACell pce 4 (cnt - 1))).
  { destruct (AO _ (INP _ P1)) as (_ & CO & _). cbn [ob_base ob_cells ob_lo ob_hi ob_dflt O_pccf] in CO. specialize (CO _ (or_introl eq_refl)). cbn [c_off c_width SymState.c_val] in CO.
    destruct CO as (_ & _ & CO). rewrite soff_lit_small in CO by (clear; lia). rewrite EB in CO.
    assert (EV : eval rhoE (SAlu ALU_ADD (SVar V_CNT) (SLit (-1))) = Z_to_bv 64 (cnt - 1)).
    { apply bv_eq. cbn [eval]. unfold V_CNT. rewrite E149, add_val, u64_lit by (clear -Hcnt CNT16; lia).
      replace (bv_unsigned (Z_to_bv 64 (-1))) with (2 ^ 64 - 1) by reflexivity. rewrite u64_lit by (clear -Hcnt CNT16; lia).
      rewrite <- (Z.mod_add _ (-1)) by (clear; lia). rewrite Z.mod_small; clear -Hcnt CNT16; lia. }
    rewrite EV in CO. intros k Hk. cbn [c_addr c_w RtCells.c_val]. unfold v3. rewrite view_in by (clear -PCEB Hk ACV; cbn in Hk; lia).
    replace (pce + Z.of_nat k) with (pce + 0 + Z.of_nat k) by (clear; lia). exact (CO k Hk). }
  assert (VS : cell_ok v3 (mkACell (pce + 8) 8 sz)).
  { destruct (AO _ (INP _ P2)) as (_ & CO & _). cbn [ob_base ob_cells ob_lo ob_hi ob_dflt O_pcs] in CO. specialize (CO _ (or_introl eq_refl)). cbn [c_off c_width SymState.c_val] in CO.
    destruct CO as (_ & _ & CO). rewrite soff_lit_small in CO by (clear; lia). rewrite EB in CO. cbn [eval] in CO. unfold V_SIZE in CO. rewrite E148 in CO.
    intros k Hk. cbn [c_addr c_w RtCells.c_val]. unfold v3. rewrite view_in by (clear -PCEB Hk ACV; cbn in Hk; lia). exact (CO k Hk). }
  assert (SOFFH : forall d, -16 <= d < 0 -> soff rhoE (SAlu ALU_ADD (SVar V_RZ) (SLit d)) = rz nv + d).
  { intros d Hd. apply soff_of_val; [|clear -Hd Brz; lia]. cbn [eval]. unfold V_RZ. rewrite E150, add_val, u64_lit by (clear -Brz; lia).
    replace (bv_unsigned (Z_to_bv 64 d)) with (d + 1 * 2 ^ 64).
    2: { rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite two64. rewrite <- (Z.mod_add d 1 (2 ^ 64)) by (clear; lia). symmetry. apply Z.mod_small. clear -Hd. lia. }
    rewrite Z.add_assoc. rewrite Z.mod_add by (clear; lia). rewrite Z.mod_small; clear -Brz Hd; lia. }
  destruct (AO _ (INP _ P5)) as (_ & COH & _). cbn [ob_base ob_cells ob_lo ob_hi ob_dflt O_Hf] in COH.
  assert (VH2 : v3 (ub - 16) = Some (Z_to_bv 8 2)).
  { destruct (COH _ HCs) as (_ & _ & CO). cbn [c_off c_width SymState.c_val hc_state] in CO. rewrite (SOFFH (-16)) in CO by (clear; lia).
    rewrite Eab in CO. specialize (CO 0%nat ltac:(clear; cbn; lia)). cbn [eval Z.of_nat Z.to_nat Pos.to_nat Pos.iter_op nth] in CO.
    unfold v3. rewrite view_in by (clear -ABB ACV Bn; unfold ub; lia). replace (ub - 16) with (ab + (rz nv + -16) + 0) by (unfold ub; clear; lia).
    etransitivity; [exact CO|]. f_equal; exact nth0_enc1_two'. }
  assert (VHN : cell_ok v3 (mkACell (ub - 12) 4 nv)).
  { destruct (COH _ HCn) as (_ & _ & CO). cbn [c_off c_width SymState.c_val hc_size] in CO. rewrite (SOFFH (-12)) in CO by (clear; lia).
    rewrite Eab in CO. cbn [eval] in CO. rewrite E12 in CO.
    intros k Hk. cbn [c_addr c_w RtCells.c_val]. cbn in Hk. unfold v3. rewrite view_in by (clear -ABB ACV Hk Bn; unfold ub; lia).
    replace (ub - 12 + Z.of_nat k) with (ab + (rz nv + -12) + Z.of_nat k) by (unfold ub; clear; lia). exact (CO k Hk). }
  assert (VH0 : cell_ok v3 (mkACell (ub - 14) 2 0)).
  { destruct (COH _ HC0) as (_ & _ & CO). cbn [c_off c_width SymState.c_val hc_sizehi] in CO. rewrite (SOFFH (-14)) in CO by (clear; lia).
    rewrite Eab in CO. cbn [eval] in CO.
    intros k Hk. cbn [c_addr c_w RtCells.c_val]. cbn in Hk. unfold v3. rewrite view_in by (clear -ABB ACV Hk Bn; unfold ub; lia).
    replace (ub - 14 + Z.of_nat k) with (ab + (rz nv + -14) + Z.of_nat k) by (unfold ub; clear; lia). exact (CO k Hk). }

  assert (VH1 : exists t, v3 (ub - 15) = Some t /\ bv_unsigned t mod 4 = 1).
  { destruct (COH _ HCt) as (_ & _ & CO). cbn [c_off c_width SymState.c_val hc_type] in CO. rewrite (SOFFH (-15)) in CO by (clear; lia).
    rewrite Eab in CO. specialize (CO 0%nat ltac:(clear; cbn; lia)). cbn [Z.of_nat nth enc_bytes Z_to_le_bytes Z.to_nat Pos.to_nat Pos.iter_op] in CO.
    exists (Z_to_bv 8 (bv_unsigned (eval rhoE (tyv tyx tya)))). split.
    - unfold v3. rewrite view_in by (clear -ABB ACV Bn; unfold ub; lia). replace (ub - 15) with (ab + (rz nv + -15) + 0) by (unfold ub; clear; lia). exact CO.
    - destruct (tya_okb_sound tya HTA) as [TA1 TA2]. pose proof (tyv_sound rhoE tyx tya TA1 TA2) as M4.
      rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8%N) with (4 * 64).
      set (u := bv_unsigned (eval rhoE (tyv tyx tya))) in *. pose proof (bv_unsigned_in_range 64 (eval rhoE (tyv tyx tya))) as UR. fold u in UR.
      pose proof (Z.div_mod u (4 * 64) ltac:(clear; lia)) as D1. pose proof (Z.mod_pos_bound u (4 * 64) ltac:(clear; lia)) as B1.
      pose proof (Z.div_mod u 4 ltac:(clear; lia)) as D2. rewrite M4 in D2.
      symmetry. apply Z.mod_unique with (q := u / 4 - (u / (4 * 64)) * 64); clear -D1 B1 D2 UR; lia. }
  assert (SHB : 2147450880 <= Sh ab /\ Sh ab + 2 * qs < 17594333495296).
  { unfold Sh, SHADOW_OFF. pose proof (Z.div_pos ab 8 ltac:(clear -ABB; lia) ltac:(clear; lia)) as D0.
    pose proof (Z.div_le_mono (ab + sz) 140737479966720 8 ltac:(clear; lia) ltac:(clear -ABB; lia)) as D1.
    replace (ab + sz) with (ab + 2 * qs * 8) in D1 by (clear -Hqs; lia). rewrite Z.div_add in D1 by (clear; lia).
    change (140737479966720 / 8) with 17592184995840 in D1. clear -D0 D1. lia. }
  assert (VZ : forall g, 0 <= g < nv / 8 -> v3 (Sh ub + g) = Some (Z_to_bv 8 0)).
  { intros g Hg. destruct (AO _ (INP _ P8)) as (_ & _ & _ & ZO). cbn [ob_base ob_cells ob_lo ob_hi ob_dflt O_Uz] in ZO. specialize (ZO eq_refl g).
    unfold obj_lo_of, obj_hi_of in ZO. cbn [ob_lo ob_hi ob_cells ob_base O_Uz] in ZO. rewrite soff_lit_small in ZO by (clear; lia).
    rewrite (soff_of_val rhoE LUe qn Elu) in ZO by (clear -Bn DMn MBn; lia). rewrite Ebu in ZO.
    unfold v3. rewrite view_in by (rewrite EShub; clear -SHB Hg Bfit8 Hqr Hqs Blp DMn MBn Bn Brz; unfold qn in *; lia).
    apply ZO; [clear -Hg; unfold qn; lia|]. intros HC. unfold covered in HC. apply Exists_exists in HC as (cc & Hcc & _). exact Hcc. }
  assert (VP : nv mod 8 <> 0 -> v3 (Sh ub + nv / 8) = Some (Z_to_bv 8 (nv mod 8))).
  { intros Hm. destruct partial eqn:EP; [|exfalso; exact (Hm Hpar)].
    destruct (AO _ (INP _ P9)) as (_ & CO & _). cbn [ob_base ob_cells ob_lo ob_hi ob_dflt O_Pf] in CO. specialize (CO pcell ltac:(unfold pcells; left; reflexivity)).
    cbn [c_off c_width SymState.c_val pcell] in CO. destruct CO as (_ & _ & CO). rewrite soff_lit_small in CO by (clear; lia). rewrite Ebp in CO.
    specialize (CO 0%nat ltac:(clear; cbn; lia)). cbn [Z.of_nat] in CO. rewrite Z.add_0_r in CO.
    assert (EV : eval rhoE (SAlu ALU_AND (SVar 12) (SLit 7)) = Z_to_bv 64 (nv mod 8)).
    { apply bv_eq. cbn [eval]. rewrite E12, and_val, !u64_lit by (clear -Bn MBn; lia). apply land_7. clear -Bn; lia. }
    rewrite EV in CO. change (Z.to_nat 1) with 1%nat in CO. rewrite (nth_enc_bytes 1 0 (nv mod 8) ltac:(clear; lia) ltac:(clear; lia)) in CO.
    unfold le_byte in CO. rewrite Z.shiftr_0_r in CO. change (2 ^ (8 * Z.of_nat 1)) with 256 in CO. rewrite !Z.mod_small in CO by (clear -MBn; lia).
    unfold v3. rewrite view_in by (rewrite EShub; clear -SHB Bfit8 Hqr Hqs Blp DMn MBn Bn Brz Hm; unfold qn, lp in *; destruct (Z.eq_dec (nv mod 8) 0); lia).
    replace (Sh ub + nv / 8) with (Sh ub + nv / 8 + 0) by (clear; lia). exact CO. }
  idtac "mf:5".
  assert (PRESo : forall o z, In o P10 -> fst (obj_range rhoE o) <= z < snd (obj_range rhoE o) -> exists bb, v3 z = Some bb).
  { intros o z Ho Hz. destruct (AO _ (INP _ Ho)) as (Bo & _ & Po & _). unfold obj_range in Hz. cbn [fst snd] in Hz.
    assert (DD : ob_dflt o = DUnknown \/ ob_dflt o = DZero).
    { unfold P10 in Ho. clear -Ho. destruct Ho as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]; cbn; tauto. }
    destruct (Po DD (z - bv_unsigned (eval rhoE (ob_base o))) ltac:(clear -Hz; lia)) as [bb Hbb]. exists bb.
    unfold v3. rewrite view_in by (clear -Hz Bo; lia).
    replace z with (bv_unsigned (eval rhoE (ob_base o)) + (z - bv_unsigned (eval rhoE (ob_base o)))) at 1 by (clear; lia). exact Hbb. }
  assert (PRES : forall z, chg_m G pce ab ub ue sz cnt z -> exists bb, v3 z = Some bb).
  { intros z Hz. unfold chg_m in Hz. fold T in Hz. rewrite Esz8 in Hz.
    destruct Hz as [Hz|[Hz|[Hz|[Hz|[Hz|[Hz|Hz]]]]]].
    - apply (PRESo O_pccf); [exact P1 | rewrite RG1; cbn [fst snd]; clear -Hz; lia].
    - apply (PRESo O_pcs); [exact P2 | rewrite RG2; cbn [fst snd]; clear -Hz; lia].
    - apply (PRESo O_pck); [unfold P10; cbn; tauto | rewrite RG3; cbn [fst snd]; clear -Hz; lia].
    - apply (PRESo (O_stf scells)); [unfold P10; cbn; tauto | rewrite RG4; cbn [fst snd]; clear -Hz; lia].
    - apply (PRESo (O_Hf hcells)); [exact P5 | rewrite RG5; cbn [fst snd]; clear -Hz; lia].
    - apply (PRESo O_T); [unfold P10; cbn; tauto | rewrite RG6; cbn [fst snd]; clear -Hz; lia].
    - destruct (Z_lt_dec z (Sh ub)); [|destruct (Z_lt_dec z (Sh ub + qn)); [|destruct (Z_lt_dec z (Sh ub + qn + lp))]].
      + apply (PRESo O_L); [unfold P10; cbn; tauto | rewrite RG7; cbn [fst snd]; rewrite EShub in *; clear -Hz l; lia].
      + apply (PRESo O_Uz); [exact P8 | rewrite RG8; cbn [fst snd]; clear -Hz n l; lia].
      + apply (PRESo (O_Pf pcells)); [exact P9 | rewrite RG9; cbn [fst snd]; clear -Hz n0 l; lia].
      + apply (PRESo O_R); [unfold P10; cbn; tauto | rewrite RG10; cbn [fst snd]; clear -Hz n1; lia]. }
  idtac "mf:6".
  assert (NK : forall k, In k N_m1 -> In (carve_obj k) R /\ spec_small k /\ spec_covered k
            /\ cells_in_view rhoE (rd_of segs (rm rhoE)) (fst (spec_range rhoE k) - (let '(_, lo, _, _) := k in lo)) (let '(_, _, _, cs) := k in cs)).
  { intros k Hk. split; [rewrite ER; apply in_or_app; left; rewrite <- N_m1_ok; apply in_map; exact Hk|].
    split; [exact (proj1 (Forall_forall _ _) N_m1_small k Hk)|].
    split; [apply coverb_sound; exact (proj1 (forallb_forall _ _) N_m1_coverb k Hk)|].
    pose proof (proj1 (Forall_forall _ _) (N_m1_civ law_die A rhoE tp md HA E151 E152 E153 E154 E155 E156) k Hk) as CV. cbn beta in CV.
    destruct k as [[[base lo] hi] cs]. cbn [spec_range fst]. replace (bv_unsigned (eval rhoE base) + lo - lo) with (bv_unsigned (eval rhoE base)) by (clear; lia). exact CV. }
  assert (INR : forall a, in_ranges rhoE R a ->
            (exists k, In k N_m1 /\ fst (spec_range rhoE k) <= bv_unsigned a < snd (spec_range rhoE k)) \/ chg_m G pce ab ub ue sz cnt (bv_unsigned a)).
  { intros a (o & HoR & Hr). rewrite ER in HoR. apply in_app_or in HoR as [HoR|HoR].
    - left. rewrite <- N_m1_ok in HoR. apply in_map_iff in HoR as (k & <- & Hk). exists k. split; [exact Hk|].
      pose proof (proj1 (Forall_forall _ _) N_m1_small k Hk) as Sk. destruct k as [[[base lo] hi] cs]. destruct Sk as (S1 & S2 & S3 & _).
      cbn [carve_obj] in Hr. unfold carved in Hr. rewrite obj_range_mk in Hr by (clear -S1 S2 S3; lia). cbn [spec_range fst snd] in Hr |- *. exact Hr.
    - right. exact (PIN o _ HoR Hr). }
  assert (VO : forall z, ~ chg_m G pce ab ub ue sz cnt z -> v3 z = vE z).
  { intros z Hz. unfold v3, vE. destruct (Z_le_dec 0 z); [destruct (Z_lt_dec z (2 ^ 64))|].
    2,3: rewrite !view_out by (clear -n; lia) || rewrite !view_out by (clear -n l; lia); reflexivity.
    rewrite !view_in by (clear -l l0; lia).
    destruct (in_ranges_dec rhoE R (Z_to_bv 64 z)) as [Hin|Hout].
    - destruct (INR _ Hin) as [(k & Hk & Hr)|Hc]; [|rewrite u64_lit in Hc by (clear -l l0; lia); exfalso; exact (Hz Hc)].
      rewrite u64_lit in Hr by (clear -l l0; lia). unfold rho3.
      exact (absorb_specs_view rhoE _ tr (vms md tp ms) (vmd md) K R N_m1 (rd_of segs (rm rhoE)) Hsm1 eq_refl NK z k Hk Hr).
    - unfold rho3, rd_of. rewrite rm_absorb_out by exact Hout. reflexivity. }
  assert (RMO : forall a, 0 <= a < 2 ^ 64 -> ~ chg_m G pce ab ub ue sz cnt a -> ~ rt_zoneM G a -> rm rho3 (Z_to_bv 64 a) = rm rhoE (Z_to_bv 64 a)).
  { intros a Ha Hc Hrt. unfold rho3. apply rm_absorb_out. intros Hin.
    destruct (INR _ Hin) as [(k & Hk & Hr)|Hc']; rewrite u64_lit in * by (clear -Ha; lia).
    - apply Hrt. exact (N_m1_zone G rhoE k a HG E151 E152 Hk Hr).
    - exact (Hc Hc'). }
  assert (DEFM : forall a, IMG_HI <= a < 2 ^ 64 -> rm rhoE (Z_to_bv 64 a) <> None -> rm rho3 (Z_to_bv 64 a) <> None).
  { intros a Ha Hd. destruct (in_ranges_dec rhoE R (Z_to_bv 64 a)) as [Hin|Hout].
    - unfold rho3. apply (absorb_defined rhoE _ tr (vms md tp ms) (vmd md) K R _ Hsm1 eq_refl (R9_writable scells hcells pcells) Hin).
      rewrite u64_lit by (unfold IMG_HI in Ha; clear -Ha; lia). clear -Ha; lia.
    - unfold rho3. rewrite rm_absorb_out by exact Hout. exact Hd. }
  assert (VMG : alloc_magic_ok v3 ub nv).
  { destruct HMG as [HF16|[HM1 HM2]].
    - left. pose proof (fact_of_stateB nW st A Kc rho rhoE tp _ F _ H HF16) as X. cbn [holds eval] in X. unfold V_RZ in X.
      rewrite E150, !u64_lit in X by (clear -Brz; lia). clear -X Brz. lia.
    - right. split.
      + destruct (COH _ HM1) as (_ & _ & CO). cbn [c_off c_width SymState.c_val hc_magic] in CO. rewrite soff_lit in CO. cbn [snorm Z.ltb] in CO.
        rewrite Eab in CO. cbn [eval] in CO.
        intros k Hk. cbn [c_addr c_w RtCells.c_val]. cbn in Hk. unfold v3. rewrite view_in by (clear -ABB ACV Hk Bn Brz; unfold ub; lia).
        replace (ub - rz nv + Z.of_nat k) with (ab + 0 + Z.of_nat k) by (unfold ub; clear; lia). unfold kAllocBegMagic. exact (CO k Hk).
      + destruct (COH _ HM2) as (_ & _ & CO). cbn [c_off c_width SymState.c_val hc_cptr] in CO. rewrite soff_lit in CO. cbn [snorm Z.ltb] in CO.
        rewrite Eab in CO.
        assert (EV : eval rhoE (SAlu ALU_ADD (SAlu ALU_ADD ab_e (SVar V_RZ)) (SLit (-16))) = Z_to_bv 64 (ub - 16)).
        { apply bv_eq. change (eval rhoE (SAlu ALU_ADD (SAlu ALU_ADD ab_e (SVar V_RZ)) (SLit (-16)))) with (alu64 ALU_ADD (eval rhoE ube) (Z_to_bv 64 (-16))).
          rewrite add_val, Eub. rewrite (u64_lit (ub - 16)) by (clear -ABB ACV Bn; unfold ub; lia).
          replace (bv_unsigned (Z_to_bv 64 (-16))) with (2 ^ 64 - 16) by (rewrite Z_to_bv_unsigned; reflexivity).
          replace (ub + (2 ^ 64 - 16)) with ((ub - 16) + 1 * 2 ^ 64) by (clear; lia). rewrite Z.mod_add by (clear; lia). apply Z.mod_small. clear -ABB ACV Bn; unfold ub; lia. }
        rewrite EV in CO.
        intros k Hk. cbn [c_addr c_w RtCells.c_val]. cbn in Hk. unfold v3. rewrite view_in by (clear -ABB ACV Hk Bn Brz; unfold ub; lia).
        replace (ub - rz nv + 8 + Z.of_nat k) with (ab + 8 + Z.of_nat k) by (unfold ub; clear; lia). exact (CO k Hk). }
  idtac "mf:7".
  destruct (malloc_rebuild CST XGL HCST HXGL HCSTM A rhoE rho3 tp md nv (aa_Km A) ltac:(clear; lia) HA ltac:(clear -Bn; lia) Hcnt HPRM
              VC VS VH2 VHN VH0 VH1 VZ VP VMG PRES VO RMO DEFM) as (A2 & HA2 & HL2 & HFR2 & HV2 & HKm2 & HKf2 & HGe2 & KEPT2 & CK2).
  idtac "mf:8".

  set (A1 := ax_setS (ax_setS F (set_objs (ax_S F) (K ++ R))) (set_objs (ax_S (ax_setS F (set_objs (ax_S F) (K ++ R)))) K)) in Hb.
  assert (Hc : SPA segs KJ (ax_setS A1 (S2_of F K)) rho3 tp (tr, {| cfg_ms := ms; cfg_model := md |})).
  { eapply SPA_restate; [exact W9 | exact D9 | reflexivity | | constructor | exact Hb].
    constructor; [|constructor]. cbn [fst snd eval]. unfold tp_ok in Htp. apply bv_eq. rewrite u64_lit by (unfold TP_A; clear; lia).
    unfold rho3. cbn [rho_absorb rw]. rewrite Htp. pose proof (geom_old _ HG) as HGt. destruct HGt as (_ & _ & _ & G4' & _). unfold G in G4'. rewrite G4'. reflexivity. }
  clear Hb.

  assert (Eub3 : bv_unsigned (eval rho3 ube) = ub) by (unfold rho3; rewrite eval_absorb; exact Eub).
  assert (E12_3 : bv_unsigned (eval rho3 (SVar 12)) = nv) by (unfold rho3; rewrite eval_absorb; cbn [eval]; rewrite E12; apply u64_lit; clear -Bn; lia).

  pose proof (proj1 (proj1 Hc)) as Hsm2. unfold virt in Hsm2. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S ax_setS] in Hsm2.
  assert (HFX : forall p, In p (unwind_factsS W st ++ pre_facts malloc_depth) -> holds rho3 p).
  { intros p Hp. unfold rho3. apply (proj2 (holds_absorb rhoE R (vms md tp ms) p)). exact (fact_of_stateB nW st A Kc rho rhoE tp _ F p H (FP9 p Hp)). }
  assert (Hhigh : holds rho3 F_sp_high) by (apply HFX; apply in_or_app; right; cbn; tauto).
  destruct (sw_range_gen segs rho3 (S2_of F K) _ (sw9 swc) Hsm2 ltac:(cbn; left; reflexivity) eq_refl Hhigh) as (SW1 & SW2 & SW3).
  assert (LNK : Forall (fun o => 140735332483072 + 16 <= bv_unsigned (eval rho3 (ob_base o)) <= 2 ^ 47 /\ ob_lo o = SLit (-16) /\ ob_hi o = SLit 0) (unwind_objs W)).
  { apply (unwind_objs_above _ _ 140735332483072); [|clear -SW1 SW2 SW3; lia|clear; lia]. apply Forall_forall. intros p Hp. apply HFX. apply in_or_app. left. exact (chain_pre_factsS W st p HW Hp). }
  assert (OUTK : forall z, SHADOW_OFF <= z < 17594333495296 -> outside_all rho3 K (Z_to_bv 64 z)).
  { intros z Hz. unfold K, KEPT9, outside_all. rewrite u64_lit by (unfold SHADOW_OFF in Hz; clear -Hz; lia). cbn [app]. constructor.
    - cbn zeta. clear -SW1 SW3 Hz ACV. unfold SHADOW_OFF in Hz. lia.
    - apply Forall_app. split.
      + eapply Forall_impl; [|exact LNK]. intros [ob olo ohi ocs od] (B1 & L1 & H1). cbn [ob_base ob_lo ob_hi] in B1, L1, H1. subst olo ohi.
        cbn zeta. rewrite obj_range_mk by (clear; lia). cbn [fst snd]. clear -B1 Hz ACV. unfold SHADOW_OFF in Hz. lia.
      + unfold O_UBz, O_got, O_rtc, GOT_LO, GOT_HI, RTC_LO, RTC_HI. repeat apply Forall_cons; try apply Forall_nil; cbn zeta.
        * unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite soff_lit_small by (clear; lia).
          rewrite (soff_of_val rho3 (SVar 12) nv E12_3) by (clear -Bn; lia). rewrite Eub3. cbn [fst snd]. clear -Hz ABB. unfold ub, SHADOW_OFF in *. lia.
        * rewrite obj_range_mk by (clear; lia). cbn [fst snd eval]. rewrite u64_lit by (clear; lia). unfold SHADOW_OFF in Hz. clear -Hz. lia.
        * rewrite obj_range_mk by (clear; lia). cbn [fst snd eval]. rewrite u64_lit by (clear; lia). unfold SHADOW_OFF in Hz. clear -Hz. lia. }

  pose proof HA as (_ & _ & _ & HRest & _). destruct HRest as (_ & _ & Hprim & _). destruct Hprim as (_ & _ & _ & PC).
  pose proof (PC c C1) as PCc. fold G in PCc. unfold class_repr in PCc.
  destruct PCc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & N2 & N3 & _ & _ & _ & _ & _ & N7 & _ & PSH & _).
  assert (Hxin : In x (cs_free_array (nthZ (aa_cls A) c cs_empty) ++ cs_cache (nthZ (aa_cls A) c cs_empty))).
  { apply in_or_app. right. unfold x, chk_of, cst_of. fold c. apply nth_In.
    unfold cnt, cnt_of, cst_of in Hcnt. fold c in Hcnt. clear -Hcnt. lia. }
  destruct (N7 x Hxin) as (_ & _ & X3). unfold kCompactPtrScale in X3. rewrite Z.shiftl_mul_pow2 in X3 by (clear; lia). change (2 ^ 4) with 16 in X3. fold sz in X3.
  set (mu := cs_mapped_user (nthZ (aa_cls A) c cs_empty)) in *. set (au := cs_allocated_user (nthZ (aa_cls A) c cs_empty)) in *.
  unfold kUserMapSize, kUserSpaceSize, kRegionSize, kFreeArraySize in N1, N2, N3. fold SB in PSH.
  assert (ERB : region_beg SB c = SB + c * 2 ^ 32) by reflexivity. rewrite ERB in PSH.
  destruct (proj1 (Z.mod_divide SB (2 ^ 16) ltac:(clear; lia)) ltac:(clear -BSB; tauto)) as [qb Hqb].
  destruct (proj1 (Z.mod_divide mu (2 ^ 18) ltac:(clear; lia)) N1) as [qm Hqm].
  assert (ESHrb : Sh (SB + c * 2 ^ 32) = qb * 2 ^ 13 + c * 2 ^ 29 + SHADOW_OFF).
  { unfold Sh. rewrite Hqb. f_equal. symmetry. apply Z.div_unique with 0; clear; lia. }
  assert (ESHre : Sh (SB + c * 2 ^ 32 + mu) = qb * 2 ^ 13 + c * 2 ^ 29 + qm * 2 ^ 15 + SHADOW_OFF).
  { unfold Sh. rewrite Hqb, Hqm. f_equal. symmetry. apply Z.div_unique with 0; clear; lia. }
  assert (ESHab : Sh ab = qb * 2 ^ 13 + c * 2 ^ 29 + 2 * x + SHADOW_OFF).
  { unfold Sh, ab. rewrite Hqb. f_equal. symmetry. apply Z.div_unique with 0; clear; lia. }
  assert (ESHsp : Sh SB = qb * 2 ^ 13 + SHADOW_OFF).
  { unfold Sh. rewrite Hqb. f_equal. symmetry. apply Z.div_unique with 0; clear; lia. }
  assert (ESHtop : Sh (SB + 2 ^ 37 + 4096) = qb * 2 ^ 13 + 2 ^ 34 + 512 + SHADOW_OFF).
  { unfold Sh. rewrite Hqb. f_equal. symmetry. apply Z.div_unique with 0; clear; lia. }
  assert (CHGD : forall z, chg_m G pce ab ub ue sz cnt z \/ ~ chg_m G pce ab ub ue sz cnt z) by (intros z; unfold chg_m; clear; lia).
  assert (WDEF : forall w, Sh (SB + c * 2 ^ 32) <= w < Sh (SB + c * 2 ^ 32 + mu) -> rm rho3 (Z_to_bv 64 w) <> None).
  { intros w Hw.
    assert (Bw : 0x643000 <= w < 2 ^ 64).
    { rewrite ESHrb, ESHre in Hw. unfold SHADOW_OFF in Hw. clear -Hw Hqb Hqm BSB Bc N2 N3 Btop Bx Bsz ACV. lia. }
    assert (VW : exists bb, v3 w = Some bb).
    { destruct (CHGD w) as [Hcw|Hnw]; [exact (PRES w Hcw)|]. rewrite (VO w Hnw).
      destruct (PSH w Hw) as [bb Hbb]. exists bb. unfold vE. rewrite <- (maskv_out (fs_footb G) _ w); [exact Hbb|].
      apply fs_footb_space_sh; [exact HG|]. fold SB. rewrite kSpaceSize_val, ESHsp, ESHtop. rewrite ESHrb, ESHre in Hw.
      clear -Hw Bc N2 N3 Hqm. lia. }
    destruct VW as [bb Hbb]. unfold v3 in Hbb. rewrite view_in in Hbb by (clear -Bw; lia).
    rewrite (rd_off_image _ _ _ Bw Hbb). discriminate. }
  idtac "mf:9".
  destruct (proj1 (Z.mod_divide ab 8 ltac:(clear; lia)) AB8) as [qa Hqa].
  assert (Hd : SPA segs KJ (ax_setX (ax_setS A1 (S2_of F K)) ((ube, SVar 12) :: ax_X (ax_setS A1 (S2_of F K)))) rho3 tp (tr, {| cfg_ms := ms; cfg_model := md |})).
  { apply SPA_x_publish; [exact XB9 | | exact Hc].
    change (ax_base (ax_setS A1 (S2_of F K))) with (ax_base F). rewrite BF9. change (ss_objs (ax_S (ax_setS A1 (S2_of F K)))) with K.
    unfold xr_ok. cbn [fst snd]. rewrite Eub3, E12_3. unfold base_sv. cbn [eval]. rewrite u64_lit by (unfold SHADOW_OFF; clear; lia).
    split; [unfold ub; rewrite Hqr, Hqa; apply Z.mod_divide; [clear; lia|]; exists (qa + 2 * qr); clear; lia|].
    split; [clear -ABB ACV Bn; unfold ub; lia|].
    intros a Ha.
    pose proof (Z.div_mod a 8 ltac:(clear; lia)) as DMa. pose proof (Z.mod_pos_bound a 8 ltac:(clear; lia)) as MBa.
    set (pa := a / 8) in *.
    assert (PA : qa + 2 * qr <= pa /\ 8 * pa <= a /\ a < qa * 8 + 16 * qs /\ 8 * (qa + 2 * qr) = ub).
    { unfold ub, ue in Ha. rewrite Hqa, Hqr in Ha. clear -Ha DMa MBa Hqa Hqr Hqs Bfit Bn. unfold ub. split; [|lia]. nia. }
    assert (PA2 : pa < qa + 2 * qs) by (clear -PA DMa MBa; nia).
    assert (SHA : SHADOW_OFF + pa = Sh ub + (pa - qa - 2 * qr)).
    { unfold Sh, ub. rewrite Hqa, Hqr. replace (qa * 8 + qr * 16) with ((qa + 2 * qr) * 8) by (clear; lia). rewrite Z.div_mul by (clear; lia). clear; lia. }
    assert (RB : Sh (SB + c * 2 ^ 32) <= (SHADOW_OFF + pa) / 8 * 8 /\ (SHADOW_OFF + pa) / 8 * 8 + 8 <= Sh (SB + c * 2 ^ 32 + mu)).
    { rewrite ESHrb, ESHre. unfold SHADOW_OFF.
      pose proof (Z.div_mod (2147450880 + pa) 8 ltac:(clear; lia)) as DMs. pose proof (Z.mod_pos_bound (2147450880 + pa) 8 ltac:(clear; lia)) as MBs.
      assert (LO : qb * 2 ^ 13 + c * 2 ^ 29 + 2147450880 <= 2147450880 + pa).
      { unfold ab in Hqa. rewrite Hqb in Hqa. clear -Hqa PA Bx Brz Hqr. lia. }
      assert (HI : 2147450880 + pa < qb * 2 ^ 13 + c * 2 ^ 29 + qm * 2 ^ 15 + 2147450880).
      { unfold ab in Hqa. rewrite Hqb in Hqa. rewrite Hqm, Hqs in *. clear -Hqa PA2 X3 N2 Bx. lia. }
      pose proof (Z.div_le_mono _ _ 8 ltac:(clear; lia) LO) as D1.
      replace ((qb * 2 ^ 13 + c * 2 ^ 29 + 2147450880) / 8) with (qb * 2 ^ 10 + c * 2 ^ 26 + 268431360) in D1 by (apply Z.div_unique with 0; clear; lia).
      pose proof (Z.div_lt_upper_bound (2147450880 + pa) 8 (qb * 2 ^ 10 + c * 2 ^ 26 + qm * 2 ^ 12 + 268431360) ltac:(clear; lia) ltac:(clear -HI; lia)) as D2.
      clear -D1 D2 DMs MBs. lia. }
    split; [clear -PA PA2 Hqa Hqs Hqr Bsz Brz ABB ACV; unfold ub in *; unfold SHADOW_OFF; lia|].
    split; [unfold shadow_addr; fold pa; apply OUTK; clear -PA PA2 Hqa Hqs Bsz Brz Hqr ABB ACV; unfold ub in *; unfold SHADOW_OFF; lia|].
    split.
    { intros j Hj. unfold word_byte. fold pa. split.
      - apply OUTK. rewrite ESHrb, ESHre in RB. unfold SHADOW_OFF in *. clear -RB Hj BSB Hqb Bc N2 N3 Hqm GS2 ACV. lia.
      - apply WDEF. clear -RB Hj. lia. }
    destruct (Z_lt_dec (pa - qa - 2 * qr) qn) as [LT|GE].
    - exists (Z_to_bv 8 0). split; [|left; reflexivity].
      unfold shadow_addr. fold pa. rewrite SHA. pose proof (VZ (pa - qa - 2 * qr) ltac:(clear -LT PA; unfold qn; lia)) as X. unfold v3 in X.
      rewrite view_in in X by (rewrite <- SHA; clear -PA PA2 Hqa Hqs Hqr Bsz Brz ABB ACV; unfold ub in *; unfold SHADOW_OFF; lia).
      refine (rd_off_image _ _ _ _ X). rewrite <- SHA. clear -PA PA2 Hqa Hqs Hqr Bsz Brz ABB ACV. unfold ub in *. unfold SHADOW_OFF. lia.
    - assert (EQ : pa - qa - 2 * qr = qn /\ nv mod 8 <> 0).
      { clear -GE PA DMa MBa DMn MBn Bn Ha Hqa Hqr. unfold ub in *. unfold qn in *. lia. }
      destruct EQ as [EQ NZ]. exists (Z_to_bv 8 (nv mod 8)). split.
      + unfold shadow_addr. fold pa. rewrite SHA, EQ. pose proof (VP NZ) as X. unfold v3 in X. fold qn in X.
        rewrite view_in in X by (rewrite EShub; clear -SHB Bfit8 Hqr Hqs Blp DMn MBn Bn Brz; unfold qn in *; lia).
        refine (rd_off_image _ _ _ _ X). rewrite EShub. clear -SHB Bfit8 Hqr Hqs Blp DMn MBn Bn Brz. unfold qn in *. lia.
      + right. split.
        * rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. rewrite Z.mod_small by (clear -MBn; lia).
          rewrite <- (proj2 (proj2 (proj2 PA))). rewrite Z.add_comm, Z.mul_comm, Z.mod_add by (clear; lia). reflexivity.
        * rewrite <- (proj2 (proj2 (proj2 PA))). fold pa. rewrite Z.add_comm, Z.mul_comm, Z.div_add by (clear; lia). clear -EQ DMn MBn. unfold qn in *. lia. }
  clear Hc.
  idtac "mf:10".

  change (ax_setX (ax_setS A1 (S2_of F K)) ((ube, SVar 12) :: ax_X (ax_setS A1 (S2_of F K))))
    with (mkAX (S2_of F K) ((ube, SVar 12) :: ax_X F) (ax_base F)) in Hd.
  rewrite XF, BF9 in Hd. change (mkAX (S2_of F K) [(ube, SVar 12)] base_sv) with (X9_of F K) in Hd.
  pose proof (smatchA_entails segs (X9_of F K) (Lc_ok W st) s9 rho3 tp _ ENT9 (proj1 Hd)) as Hsm4.
  set (rho4 := rho_sub rho3 s9) in Hsm4.
  assert (Hlow : forall k, (k < NF)%positive -> rw rho4 k = rw rhoE k).
  { intros k Hk. unfold rho4. cbn [rho_sub rw]. rewrite (wsub_get_id _ _ _ SID9 Hk). cbn [eval]. unfold rho3. cbn [rho_absorb rw]. reflexivity. }
  assert (E110 : bv_unsigned (rw rho4 V_RES) = ub). { unfold rho4. cbn [rho_sub rw]. rewrite G110. exact Eub3. }
  assert (Erm4 : rm rho4 = rm rho3) by exact (rm_rho_sub' rho3 s9).
  destruct HL as (HLw & HLl & HLm & HLd).
  pose proof (rhoM_agree A rho) as (RMw & RMl & RMm).
  assert (LOWE : forall k, (k < NF)%positive -> rw rhoE k = rw rho0 k).
  { intros k Hk. rewrite <- (Hagw k) by (unfold GW, NF in *; clear -Hk; lia). rewrite <- (RMw k Hk). exact (HLw k). }
  destruct HDO as (Dgeom & Dcls & Dci & Dsec & Dpc & Dlive & Dqt & Dqg & Dii & Dbusy & Dhint & DV & DKm & DKf).
  assert (CLE : forall a, client_addrA CST A0 a <-> client_addrA CST A a).
  { intros a. unfold client_addrA, client_mut_addrA, aa_frames, frame_flag. rewrite Dlive, Dbusy, Dgeom. split; intros X; exact X. }
  assert (CSE : forall a, client_shadowA CST XGL A0 a <-> client_shadowA CST XGL A a).
  { intros a. unfold client_shadowA. split; intros [(y & Y1 & Y2)|Y]; [left; exists y; split; [apply (proj1 (CLE y)); exact Y1 | exact Y2] | right; exact Y
      | left; exists y; split; [apply (proj2 (CLE y)); exact Y1 | exact Y2] | right; exact Y]. }
  apply (LQPA_intro segs NF rho0 tp0 _ (Lc_ok W st) (JLc_ok CST XGL A0 Kc) rho4 tp _ KJ).
  - exact HPin.
  - split; [exact Hsm4 | exact HK].
  - split.
    + intros i Hi. rewrite (Hlow i Hi), (LOWE i Hi). reflexivity.
    + intros l. unfold rho4. cbn [rho_sub rl]. unfold rho3. cbn [rho_absorb rl]. rewrite <- (Hagl l). rewrite <- (RMl l). symmetry. exact (HLl l).
  - intros _. unfold JLc_ok. split.
    2:{ assert (SL : forall k, (k = 143 \/ k = 144)%positive -> wsub_get s9 k = SVar k -> rw rho4 k = rw rho0 k).
        { intros k0 Hk0 Hg. unfold rho4. cbn [rho_sub rw]. rewrite Hg. cbn [eval]. unfold rho3. cbn [rho_absorb rw].
          rewrite <- (Hagw k0) by (unfold GW; clear -Hk0; lia). rewrite (rhoM_of_keep A rho k0) by (clear -Hk0; tauto). exact (HLw k0). }
        split; [exact (SL 143%positive ltac:(tauto) G143) | exact (SL 144%positive ltac:(tauto) G144)]. }
    unfold JL_malloc_ok. cbn [w_tr w_cfg cfg_model].
    exists A2, [], (aa_live A0). cbn [app].
    split; [unfold AInv, AInvA in HA2 |- *; rewrite Erm4; exact HA2|].
    split; [rewrite HL2, E110, <- (HLw 12%positive), Dlive; reflexivity|].
    split; [reflexivity|].
    split; [rewrite HFR2; unfold aa_frames; rewrite Dbusy; reflexivity|].
    split; [rewrite HV2, DV, <- (HLw 12%positive); reflexivity|].
    split; [rewrite HKm2, DKm; reflexivity|]. split; [rewrite HKf2, DKf; reflexivity|]. split; [rewrite HGe2, Dgeom; reflexivity|].
    split.
    { split.
      - intros a Ha Hcl. rewrite Erm4.

        assert (EQ0 : rm rho (Z_to_bv 64 a) = rm rho0 (Z_to_bv 64 a)).
        { apply HLm. rewrite u64_lit by exact Ha. apply HKEEP. destruct Hcl as [(X & _)|(X & _)]; [left | right]; exact X. }
        assert (Hcl' : (client_addrA CST A a /\ client_addrA CST A2 a /\ ~ errno_addrA a)
                       \/ (client_shadowA CST XGL A a /\ client_shadowA CST XGL A2 a /\ rm rhoE (Z_to_bv 64 a) <> None)).
        { destruct Hcl as [(X & Y & NE)|(X & Y & DEF)]; [left; split; [apply (proj1 (CLE a)); exact X | exact (conj Y NE)]
                                                         | right; split; [apply (proj1 (CSE a)); exact X | split; [exact Y | rewrite Erm, EQ0; exact DEF]]]. }
        rewrite (proj1 KEPT2 a Ha Hcl'). rewrite Erm. exact EQ0.
      - intros xx jj Hx Hj Hdef. rewrite Erm4. apply (proj2 KEPT2 xx jj); [| exact Hj |].
        + destruct Hx as [[X Y]|X]; [left; split; [apply (proj1 (CLE xx)); exact X | exact Y] | right; exact X].
        + rewrite Erm. apply HLd; [|exact Hdef].

          assert (BX : 0 <= xx < 2 ^ 47).
          { destruct Hx as [[X _]|X]; [apply (proj1 (CLE xx)) in X; exact (proj1 (client_addr_bounds CST HCST A xx _ HG (proj1 (proj2 (proj2 HA))) (proj1 (proj1 (proj2 (proj2 (proj2 HA))))) X))|].
            destruct (HXGL xx X). unfold IMG_HI in *. clear -H0 H1. lia. }
          pose proof (Sh_in_band xx BX) as SBX. unfold word_byte. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *.
          rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64%N) with (2 ^ 64).
          pose proof (Z.div_mod (Sh xx) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (Sh xx) 8 ltac:(lia)). rewrite Z.mod_small by (clear -SBX Hj H0 H1; lia). clear -SBX Hj H0 H1. lia. }
    split; [exact HK|].
    rewrite <- (HLw 12%positive). fold nv. intros c0 Hc0 Hor Hfr. apply (CK2 c0 Hc0 Hor). unfold class_fresh in Hfr |- *. rewrite Dcls. exact Hfr.
Qed.
End B14.

Definition fin_hyps (F : axst) (swc scells hcells : list cell) (partial : bool) (s9 : wsub) : Prop := ltac2:(tb__ "0|10|
SbcVW;Vswc;A2S37S1A1M0Sc5Vhcells;A1S3bS0S33A2S2eS2dG0Sd5SdS47VF;A1M1A1M2Sb2VnW;A1M3A2S3eS1R2Sb4Vscells;Vhcells;S36S37S3A1Lpartial;Vpartial;S38S3Sb9S3cS3A1M4A3G4X36x2A3A3A3S2eS2dS36Sd4G3A1S39A3S2eS2dS36S57S3aS3aSe0R1S41S1G2A2M5A2Li;G3A3S39A3S2eS2dS36S57S3aS3aS59S3aSdfR1A1G3A3Li;Sa8U0G5A2A3S39A3S2eS2dS37S3bS0S0A2M6A1M7S4bVF;A1S3cG6A1M8A3S2eS2dS0S4cVF;A1S98A3S2eS56S3Sc3Vhcells;A3S2eS56S3Sc1Vhcells;A3S2eS56S3Sc2Vhcells;A3S2eS56S3Sb8S45S0S33R1A3S46S0S33R1A3M9A2Vhcells;A3S2eS2dS36SbaG9A1S39A3S2eS2fS56S6S10S4S77A1S2Z10A1A2SaG1A1MaA3S2eS56S3Sb7Vhcells;A3S56S3Sb6Vhcells;A3A2A2S2eS58S6S79GaA3S2eS58S6S3eS6S9bVW;Vst;A2S9aS99A1A3GaA3S2eS2dS36S16Sb3VF;R2A2MbA1S39A3S2eS2dS40S3bG7S37S6A1McA2MdA1SceSd6G1R2A2GbA2S3fGdS3dG7GcS38G6S3dS0S0S2Sd8A1S4P18A1A4G8A3S3cS6A1A4A2A3S2eS2dS36S4aS9G1A1S3dS0S0S78S4PcA1A4A2S39A3S2eS2dS36S49Sb5VF;R2A2S8eVW;Vst;A2Vs9;A3S39A3S2eS2dS36Sc7Vs9;S88A2S39A3S2eS2dS0Sc6Vs9;S97A2S78A3S2eS2dS0Sc6Vs9;P8fMeA2S4GeA1A3S2dS0Sc6Vs9;P90MfA2S4GfA1A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2Tty;TK;").

Lemma calloc_finish'_P : ltac2:(tb__ "0|6|
S48S37S3A1M0G0G0S36ScaSdeR6R5R4R3R2R1A6S6aS6aS93S5S5S33OF_;S5S37S67Q40M1A1A1M2G2S90S37S3bS48S72A2M3A1S56G3S3dS48S72S8eVW;Vst;A2S8fVCST;VXGL;RbR9A4A4R1A3S92VW;Vst;A2S94RbA1Sa2ReRdA2Sa3RaRcRbA3S33S2fS95VCST;R11R1A3S96VCST;VXGL;R11R1A4A2RdR2A1F_;Fa;S5aZ1Sa4R10S66G1S7RdPcM4A2A2A2A2S6cR11A1S36OLpartial;R16S30S2dS33S5bS66G1S7RfG4A2A2Z8A2Z0A3M5A1G5X36x2S8aVsegs;Sa1VW;Vst;R13R12R10A5R1bReRcRbA6S73Vsegs;S88R12ReRbRcA6F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FPosts;Fw;Ftp;Ftp0;FrhoE;Fkeep;Frho;Frho0;FKc;FA;FA0;F_;Fs9;Fpartial;Fhcells;Fscells;Fswc;FF;").
Proof.
  intros F swc scells hcells partial s9 (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H9t & H9a & H9m & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19).
  exact (calloc_finish_P F swc scells hcells partial H1 H2 H3 H4 H5 H6 H7 H8 H9 _ _ H9t H9a H9m H10 H11 H12 H13 H14 s9 H15 H16 H17 H18 H19).
Qed.

Lemma SPA_add_facts : ltac2:(tb__ "0|0|
S8dS5S48S37S6A1S37S67Q40A1A1S90Sa9S6S21R5A1R3A3S2dS36S57S6S14S9S47R5A1A1A1R4A3S39A3S8aVsegs;R8R6R7R4R3A6S8aVsegs;R9SaeR6R7A2R8R5R4A6F_;F_;F_;Fw;Ftp;FFs;FA;Frho;FJx;").
Proof. intros Jx rho A Fs tp w HF HB [Hsm HJ]. split; [exact (smatchA_add_facts segs rho tp Fs A w Hsm HF HB) | exact HJ]. Qed.

Section ARM.
Variable partial : bool.
Variable Frz : list sprop.
Variables (CC9 EE9m CC9m T9 CC10 F10 : axst).
Hypothesis Cert9 : ltac2:(tb__ "0|1|
S2dS36SafSb1Ufa0S38S33Zdb004S3cS33A1A3Sb0S38S48SaeVFrz;VCC9;A2S3cS48A1M0A3S38S48VEE9m;G0A3A6S39A3").
Hypothesis HCC9m : ltac2:(tb__ "0|1|
S2dS48VCC9m;S87VW;Vst;Vtmax;VEE9m;S7dS38S3bS3aS0A2M0S3dS3aS0UaS78A4S38G0S3dS3aS0UcS4PcA1A4S3cG0A1A3A3S3cS1A1S44S3cS6A1A9A3").
Hypothesis W9m : ltac2:(tb__ "0|0|
S2dS36S16S47VCC9m;A1A1S39A3").
Hypothesis D9m : ltac2:(tb__ "0|4|
S2dS40S3bS37S3bS0S0A2M0A1M1S37S6A1M2A2M3A1SceS47VEE9m;A1S47VCC9m;A1A2S3fG3S3dG1G2S3cG0A1S3cS6A1A4A2A3").
Hypothesis NX9m : ltac2:(tb__ "0|0|
S2dS34S9S47VCC9m;A1A1S9S47VEE9m;A1A1A3").
Variables (sm sdm : wsub) (Rm : list sobj).
Hypothesis Hem : ltac2:(tb__ "0|1|
S2dS40S37S1A1M0A1S75VCC9m;ScbVsm;A3S3fG0VRm;A2A3").
Hypothesis Hchkm : ltac2:(tb__ "0|0|
S2dS36S74VCC9m;ScbVsm;VRm;SabS4fS48S4eScdA4A5S39A3").
Hypothesis HTm : ltac2:(tb__ "0|0|
S2dS48S76Vsm;ScbSe3SccA1VCC9m;VRm;A5VT9;A3").
Hypothesis FBCm : ltac2:(tb__ "0|1|
S2dS36S57S6S14S9S47VCC9m;A1M0A1A1SaG0A1A3S39A3").
Hypothesis FBTm : ltac2:(tb__ "0|0|
S2dS36S57S6S14S9S47VT9;A1A1A1SaS47VCC9m;A1A1A3S39A3").
Hypothesis ENT10 : ltac2:(tb__ "0|0|
S2dS36S49Se4VT9;SaS47VCC9m;A1A1A2VCC10;Vsdm;A3S39A3").
Hypothesis SID10 : ltac2:(tb__ "0|0|
S2dS36Sc7Vsdm;Sb0A2S39A3").
Hypothesis NXCm : ltac2:(tb__ "0|0|
Se1Sb0S9S47VCC9m;A1A1A2").
Hypothesis Cert10 : ltac2:(tb__ "0|1|
S2dS36SafSb1Ufa0S3cS33A1Sb0S38S48VCC10;S3cS48A1M0A3S38S48VF10;G0A3A6S39A3").
Variables (swc scells hcells : list cell) (sf : wsub).
Hypothesis FH : ltac2:(tb__ "0|0|
SdeVF10;Vswc;Vscells;Vhcells;Vpartial;Vsf;A6").

Lemma s9c_arm : ltac2:(tb__ "0|5|
S90OF_;S6aS6aS93S5S5S33OF_;S37S67Q40M0A1A1M1S37S3bS48S72A2M2A1S56G2S3dS48S72S8eVW;Vst;A2S8fVCST;VXGL;R8R6A4A4R1A3S92VW;Vst;A2Sa5VW;Vst;A2S94R9A1S8cVsegs;RdS8bRaA1A3Sa2RdRcA2Sa3R9RbRaA3S33S2fS95VCST;R10R1A3S96VCST;VXGL;R10R1A4A2RcR2A1F_;Fa;S5aZ1Sa4RfS66G0S7RcPcM3A2A2A2A2S6cR10A1S36OLpartial;Vpartial;S30S2dS33S5bS66G0S7ReG3A2A2Z8A2Z0A3M4A1G4X36x2S5G1S91Vsegs;R16S8aVsegs;Sa1VW;Vst;R14R13R11A5SaeVFrz;VCC9;A2R2R1A5S73Vsegs;S88R12RfReA5A4FtpX;FrhoX;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FPosts;Ftp0;Fkeep;Frho;Frho0;FKc;FA;FA0;Fok;").
Proof.
  intros ok A0 A Kc rho0 rho keep tp0 Posts HPin HW HUS HKc Hokf HDO HL HKEEP Hcnt HPRM Hpar rhoX tpX.
  pose proof (JGb_stable nW st A Kc rho HUS HKc) as HST.
  apply (cfg_soundA segs 4000%nat [0xdb004] GW [ax_add_facts Frz CC9] [EE9m] (JGb W st A Kc rho) ok _ tpX).
  - intros r t tr ms md msv' [_ HJ] HMI Hh Hp Hs. destruct HJ as (_ & HK & _). exact (Hokf r t tr ms md msv' HK HMI Hh Hp Hs).
  - exact HST.
  - exact Cert9.
  - intros E rhoY HinE. destruct HinE as [<-|[]].
    eapply triple_conseq; [intros w Hw | intros w Hw; right; exact Hw |].
    2:{ apply (call_gen nW st CC9m T9 CC10 sm Rm sdm Pre_mszA Posts_mszA P_msz
                eq_refl (fun ok0 Jx r0 t0 Ho Hs => memsetZ_sumA ok0 Jx Ho Hs r0 t0) Hem Hchkm HTm FBCm FBTm ENT10 SID10 NXCm eq_refl
                ok A Kc rho tpX rhoY _ HUS HKc Hokf).
        intros rhoZ tpZ.
        apply (cfg_soundA segs 4000%nat [] GW [CC10] [F10] (JGb W st A Kc rho) ok _ tpZ).
        - intros r t tr ms md msv' [_ HJ] HMI Hh Hp Hs. destruct HJ as (_ & HK & _). exact (Hokf r t tr ms md msv' HK HMI Hh Hp Hs).
        - exact HST.
        - exact Cert10.
        - intros E' rhoV HinE'. destruct HinE' as [<-|[]].
          eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw |].
          eapply triple_conseq; [intros w Hw; exact Hw | | apply triple_refl].
          intros w Hw. exact (calloc_finish'_P F10 swc scells hcells partial sf FH A0 A Kc rho0 rho keep rhoV tp0 tpZ w Posts HPin HW HKc HDO HL HKEEP Hcnt HPRM Hpar Hw).
        - left. reflexivity. }
    rewrite HCC9m. unfold upd. lazy zeta. rewrite HCC9m in W9m, D9m, NX9m. unfold upd in W9m, D9m, NX9m.
    eapply SPA_restate; [exact W9m | exact D9m | exact NX9m | constructor | constructor | exact Hw].
  - left. reflexivity.
Qed.
End ARM.

Section B15.
Variable partial : bool.
Variable CC9 : axst.
Hypothesis NX9 : ltac2:(tb__ "0|0|
Se1Sb0S9S47VCC9;A1A1A2").
Hypothesis FGC : ltac2:(tb__ "0|0|
S58S6S79SaS47VCC9;A1A1A3").
Hypothesis ARMa : ltac2:(tb__ "0|5|
S90OF_;S6aS6aS93S5S5S33OF_;S37S67Q40M0A1A1M1S37S3bS48S72A2M2A1S56G2S3dS48S72S8eVW;Vst;A2S8fVCST;VXGL;R8R6A4A4R1A3S92VW;Vst;A2Sa5VW;Vst;A2S94R9A1S8cVsegs;RdS8bRaA1A3Sa2RdRcA2Sa3R9RbRaA3S33S2fS95VCST;R10R1A3S96VCST;VXGL;R10R1A4A2RcR2A1F_;Fa;S5aZ1Sa4RfS66G0S7RcPcM3A2A2A2A2S6cR10A1S36OLpartial;Vpartial;S30S2dS33S5bS66G0S7ReG3A2A2Z8A2Z0A3M4A1G4X36x2S5G1S91Vsegs;R16S8aVsegs;Sa1VW;Vst;R14R13R11A5SaeS38S6S10S2Z20A1S4S77A1A2S3cS6A1A3VCC9;A2R2R1A5S73Vsegs;S88R12RfReA5A4FtpX;FrhoX;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FPosts;Ftp0;Fkeep;Frho;Frho0;FKc;FA;FA0;Fok;").
Hypothesis ARMb : ltac2:(tb__ "0|5|
S90OF_;S6aS6aS93S5S5S33OF_;S37S67Q40M0A1A1M1S37S3bS48S72A2M2A1S56G2S3dS48S72S8eVW;Vst;A2S8fVCST;VXGL;R8R6A4A4R1A3S92VW;Vst;A2Sa5VW;Vst;A2S94R9A1S8cVsegs;RdS8bRaA1A3Sa2RdRcA2Sa3R9RbRaA3S33S2fS95VCST;R10R1A3S96VCST;VXGL;R10R1A4A2RcR2A1F_;Fa;S5aZ1Sa4RfS66G0S7RcPcM3A2A2A2A2S6cR10A1S36OLpartial;Vpartial;S30S2dS33S5bS66G0S7ReG3A2A2Z8A2Z0A3M4A1G4X36x2S5G1S91Vsegs;R16S8aVsegs;Sa1VW;Vst;R14R13R11A5SaeS38S6S10S4S77A1S2Z10A1A2S3cS6A1A3VCC9;A2R2R1A5S73Vsegs;S88R12RfReA5A4FtpX;FrhoX;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FPosts;Ftp0;Fkeep;Frho;Frho0;FKc;FA;FA0;Fok;").

Theorem spine_s9c_P : ltac2:(tb__ "0|5|
S90OF_;S6aS6aS93S5S5S33OF_;S37S67Q40M0A1A1M1S37S3bS48S72A2M2A1S56G2S3dS48S72S8eVW;Vst;A2S8fVCST;VXGL;R8R6A4A4R1A3S92VW;Vst;A2Sa5VW;Vst;A2S94R9A1S8cVsegs;RdS8bRaA1A3Sa2RdRcA2Sa3R9RbRaA3S33S2fS95VCST;R10R1A3S96VCST;VXGL;R10R1A4A2RcR2A1F_;Fa;S5aZ1Sa4RfS66G0S7RcPcM3A2A2A2A2S6cR10A1S36OLpartial;Vpartial;S30S2dS33S5bS66G0S7ReG3A2A2Z8A2Z0A3M4A1G4X36x2S5G1S91Vsegs;R16S8aVsegs;Sa1VW;Vst;R14R13R11A5VCC9;R2R1A5S73Vsegs;S88R12RfReA5A4FtpX;FrhoX;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FPosts;Ftp0;Fkeep;Frho;Frho0;FKc;FA;FA0;Fok;").
Proof.
  intros ok A0 A Kc rho0 rho keep tp0 Posts HPin HW HUS HKc Hokf HDO HL HKEEP Hcnt HPRM Hpar rhoX tpX.
  set (nv := bv_unsigned (rw rho 12%positive)) in *.
  apply (triple_pre_pure segs ok _ _ (rw rhoX V_RZ = Z_to_bv 64 (rz nv) /\ (16 <= rz nv <= 1024 /\ rz nv mod 16 = 0))).
  { intros w Hw. pose proof (JGb_pvals nW st A Kc rho rhoX tpX w CC9 Hw FGC Hcnt) as PV. cbn zeta in PV.
    destruct PV as (_ & _ & E150 & _ & _ & _ & _ & _ & Brz & _). split; [exact E150 | exact Brz]. }
  intros [E150 RZF].
  destruct (Z.eq_dec (rz nv) 16) as [E16|N16].
  - eapply triple_conseq; [intros w Hw | intros w Hw; exact Hw | exact (ARMb ok A0 A Kc rho0 rho keep tp0 Posts HPin HW HUS HKc Hokf HDO HL HKEEP Hcnt HPRM Hpar rhoX tpX)].
    apply (SPA_add_facts (JGb W st A Kc rho) rhoX CC9 [SPUle (SVar V_RZ) (SLit 16)] tpX w); [| |exact Hw].
    + constructor; [|constructor]. cbn [holds eval]. rewrite E150, !u64_lit by lia. lia.
    + cbn. unfold V_RZ. rewrite !andb_true_r. apply (proj2 (Pos.ltb_lt _ _)). unfold GW in NX9. lia.
  - eapply triple_conseq; [intros w Hw | intros w Hw; exact Hw | exact (ARMa ok A0 A Kc rho0 rho keep tp0 Posts HPin HW HUS HKc Hokf HDO HL HKEEP Hcnt HPRM Hpar rhoX tpX)].
    apply (SPA_add_facts (JGb W st A Kc rho) rhoX CC9 [SPUle (SLit 32) (SVar V_RZ)] tpX w); [| |exact Hw].
    + constructor; [|constructor]. cbn [holds eval]. rewrite E150, !u64_lit by lia. lia.
    + cbn. unfold V_RZ. rewrite !andb_true_r. apply (proj2 (Pos.ltb_lt _ _)). unfold GW in NX9. lia.
Qed.
End B15.
End S9.
End SpineCallocS9.

(* [comment removed for export] *)
Module SpineMallocR8.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "reg_sv"; "SLit"; "valuation"; "ss_next"; "ss_objs"; "eval"; "obj_range"; "ranges_disjoint"; "sprop"; "ss_facts"; "ss_pc"; "sv_below"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "ge"; "modulo"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@Corelib.Init.Datatypes"; "list"; "bool"; "cons"; "prod"; "true"; "app"; "pair"; "fst"; "nil"; "Some"; "nat"; "option"; "snd"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger"; "apartW"; "maps_disjoint"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "aa_geom"; "ag_spacebeg"; "AA"; "ag_top"; "@Stdlib.Lists.List"; "In"; "incl"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "region_free"; "alloc_top"; "m_vmmaps"; "map_contains"; "vm_limit"; "vm_maps"; "vm_reserved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillJ"; "JR"; "mlink"; "entryR"; "frozen"; "ghosts"; "phase"; "@Corelib.Lists.ListDef"; "map"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "ulink"; "UStopLeOrPc"; "ustop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3"; "skel"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.BackingAlgebra"; "overlap_sum"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "headroom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget"; "LIMIT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "O_pcc0"; "O_st"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR"; "GR"; "O_pcm"; "O_ri"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kSpaceSize"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.RefillJP"; "pbase"; "ph_get"; "ph_set"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR"; "commit_post"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SpineMallocR2"; "BASEF"; "BASEO"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA MmapA MmapFixedA LedgerA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Inv InvLaws.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillTR RefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jc.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.RefillJP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocR1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SpineMallocR2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jc.SpineMallocR3.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree.segsA.

Lemma Rregion_free_of_apart : ltac2:(tb__ "0|2|
S17S1aS16Q40A1M0G0A2M1A1G0G0G1S2cG1R1R4A3S26S1dG0G0R4R3A4R2A2F_;Fe;S0S18S2fR4R3R2A3S1bA3F_;Fn;Fa;Fl;").
Proof.
  induction l as [|[b s] l IH]; intros a n H; [reflexivity|]. cbn [region_free].
  rewrite (IH a n) by (intros e He; apply H; right; exact He). rewrite andb_true_r.
  pose proof (H (b, s) (or_introl eq_refl)) as X. unfold apartW in X. cbn [fst snd] in X.
  unfold iv_overlap. apply negb_true_iff. apply andb_false_iff. destruct X as [X|X]; [right|left]; apply Z.ltb_ge; lia.
Qed.
Lemma RapartW_sub : ltac2:(tb__ "0|4|
S16Q40M0A1M1G1S1aG1G1A2M2G2S12S15G0S1eG1G1R2A3A2S15G0R4A2M3A2S12S11S15G0R5A2G3A2S11S15G0S1eG1G1R3A3A2S15G0S23G1G1R3A3A2A2A2S26R4R3A2S26S1dG1G1R7R6A4R4A2F_;F_;F_;Fe';Fe;Fn;Fa;").
Proof. intros a n e e' H1 H2 [X|X]; unfold apartW in *; cbn [fst snd] in *; [left|right]; lia. Qed.
Lemma Rmaps_disjoint_pick : ltac2:(tb__ "0|4|
S17S1aS16Q40A1M0G0A2M1A1M2G2G1G2S27S1cG1R4S1cG1R3S19G1R2R1A3A3A3A1S1G1S2cG1R1R6A3S26R5R2A2M3F_;Fe';G1S2cG1R1S1cG1R5R3A3A3G3F_;Fe';A2F_;Fl2;Fe;Fl1;FR;").
Proof.
  intros R l1 e l2 H. unfold maps_disjoint in H.
  apply ranges_apart_app in H as (_ & H12 & XR). apply ranges_apart_app in H12 as (_ & H2 & X1). cbn in H2. destruct H2 as [F2 _].
  split.
  - intros e' He'. apply apartW_sym. apply (XR e' e He'). apply in_or_app. right. left. reflexivity.
  - intros e' He'. apply in_app_or in He' as [He'|He'].
    + apply apartW_sym. apply (X1 e' e He'). left. reflexivity.
    + exact (proj1 (Forall_forall _ _) F2 e' He').
Qed.

Lemma space_commit_model : ltac2:(tb__ "0|8|
S2aS7S17S16Q40M0A1M1A1M2S2eS3cG2S2eG1G1S50S25R9R8R7R6A5S38RaR9R8R7R6R5R4A7S12S29S28RbA1A1S15G0R4A2M3A2S12S11S15G0R5A2M4G3A2S11S11S29S28RcA1A1S4fA2Z1000A2A2S1S0S18S2fS35S31R7A1M5A1R6R5A3S1bA3S1S0S18S32S34G5A1M6R6R5A3S1bA3S1S12S47G6S15G0R6A2M7S11G7G4A2A3G4A2S1S0S24S30G5A1S2bS28RdA1A1A3S0S24S33G5A1S49A3A2A2A2A2F_;F_;F_;F_;Fn0;Fa0;Fmd;Ftp;Fph;Fmd0;Ftp0;Frb;FA;").
Proof.
  intros A rb tp0 md0 ph tp md a0 n0 HA HM H1 H2.
  unfold mlink in HM. cbn zeta in HM. destruct HM as (M1 & M2 & M3 & M4 & _). rewrite M1, M2, M3, M4.
  destruct HA as (_ & _ & _ & _ & HMI & _). destruct HMI as (VG & _ & LIM & _ & _ & _ & TOPm & LI).
  destruct VG as (_ & N2 & _). destruct LI as (_ & _ & L3 & _).
  destruct N2 as (e & He & B1 & B2).
  destruct (in_split _ _ He) as (l1 & l2 & EM). rewrite EM in L3.
  destruct (Rmaps_disjoint_pick _ _ _ _ L3) as [XR XM].
  assert (SUB : forall e', apartW e e' -> apartW (a0, n0) e') by (intros e' X; apply (RapartW_sub a0 n0 e e'); [lia | lia | exact X]).
  split; [apply Rregion_free_of_apart; intros e' He'; apply SUB; exact (XR e' He')|].
  split.
  { unfold map_contains. apply existsb_exists. exists e. split; [exact He|]. apply andb_true_intro. split; apply Z.leb_le; lia. }
  split; [rewrite EM; apply overlap_sum_split_le; apply Rregion_free_of_apart; intros e' He'; apply SUB; exact (XM e' He')|].
  split; [exact TOPm | exact LIM].
Qed.

Section COMMIT.
Variables (A : AA) (Kc : KcA) (rb : valuation) (tp0 : list word) (md0 : Model).
Variable TR : assn -> assn -> Prop.
Hypothesis KIT : TRok Kc TR.
Hypothesis HKc : Kc_ok Kc.
Variables (W : list ulink) (st : ustop) (rho : valuation).
Hypothesis HW : ltac2:(tb__ "0|0|
S0S42Vst;S41A3S0S17S40A1VW;S1fS40A1A3F_;").
Hypothesis HE : ltac2:(tb__ "0|0|
S39VA;Vrb;Vtp0;Vmd0;VW;Vst;Vrho;A7").
Notation JRp := (JR A Kc rb tp0 md0).
Let nv : Z := bv_unsigned (rw rb 12%positive).
Let c : Z := cls_of nv.

Variable p : piece.
Variable eb : sv.
Variable ph : phase.
Hypothesis PH0 : ltac2:(tb__ "0|0|
S0S21S52Vp;Vph;A2U0A3").
Hypothesis PORD : pord p ph.
Hypothesis PQ : ph_quiet ph.
Let B : Z := ltac2:(tb__ "0|0|
S51VA;Vrb;Vp;A3").
Hypothesis HBv : ltac2:(tb__ "0|0|
S7S3aVrb;R1A2S3bVA;Vrb;R2A3S0S24S15Q40SaR3Veb;A2A2VB;A3F_;F_;Fr;").
Hypothesis HBn : ltac2:(tb__ "0|1|
S1S12S11S29S28VA;A1A1M0Z100000000A2VB;A2S1S12S11VB;Z40000A2S11G0Z2000000000A2A2S0S24S14VB;Z1000A2Z0A3A2A2").
Hypothesis HROOM : ltac2:(tb__ "0|0|
S17S16Q40A1A1S2eS38VA;Vrb;Vtp0;Vmd0;Vph;R2R1A7S13S48R2R3A2Z40000A2F_;Fmd;Ftp;").

Variable CX : axst.
Hypothesis SK_x : ltac2:(tb__ "0|1|
S0S17S1aS1aS4S4A2S4A2M0A1S3dS3G0S43S9S2VCX;A1A1A4S3dS3G0S43S1cS3S56VW;A1S19S3S4aS19S3S4bS19S3S4dS19S3S4eS1fS3A1A3A3A3A3A3A4A3").
Hypothesis XF_x : ltac2:(tb__ "0|0|
S2dSdS55VW;Vst;A2SeS2VCX;A1A1A3").
Hypothesis XX_x : ax_X CX = [].
Hypothesis NX_x : ltac2:(tb__ "0|0|
S0S18S57S4cS8S2VCX;A1A1A2S1bA3").
Hypothesis IC_x : ltac2:(tb__ "0|0|
S0S22S3eA1S46S25SfS2VCX;A1A1A2S20S3eS3fA2A3").
Hypothesis R17_x : ltac2:(tb__ "0|0|
S0S4S5S2VCX;A1Z11A2S6ZdeA1A3").
Hypothesis R10_x : ltac2:(tb__ "0|0|
S0S4S5S2VCX;A1ZaA2Veb;A3").
Hypothesis BEL_x : ltac2:(tb__ "0|0|
S0S18S10S8S2VCX;A1A1Veb;A2S1bA3").
Hypothesis R11_x : ltac2:(tb__ "0|0|
S0S4S5S2VCX;A1ZbA2S6Z40000A1A3").
Hypothesis R12_x : ltac2:(tb__ "0|0|
S0S4S5S2VCX;A1ZcA2S6Z3A1A3").
Hypothesis R13_x : ltac2:(tb__ "0|0|
S0S4S5S2VCX;A1ZdA2S6Z32A1A3").
Hypothesis R14_x : ltac2:(tb__ "0|0|
S0S4S5S2VCX;A1ZeA2S6ZffffffffffffffffA1A3").
Hypothesis R15_x : ltac2:(tb__ "0|0|
S0S4S5S2VCX;A1ZfA2S6Z0A1A3").

Lemma commit_objs : ltac2:(tb__ "0|0|
S7S17S16Q40A1A1S45S36S25S37VA;VKc;Vrb;Vtp0;Vmd0;Vph;A6VCX;R3R2R1A6S3S2cS3R1S9S2VCX;A1A1A3ScSbR6R2A2S1dS24S24VB;S11VB;Z40000A2A4A2F_;Fo;F_;Fw;Ftp;Fr;").
Proof.
  intros r tp w [HsmA HJ]. pose proof HJ as (HFz & HGh & _).
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF0. pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG.
  destruct (arm_extra_ranges A rb r CF0 RG HGh) as (EB & RNc & RNs & RNm & RNr). cbn zeta in RNs, RNr. fold nv c in RNr.
  unfold cfacts in CF0. cbn zeta in CF0. fold nv c in CF0.
  destruct CF0 as ((_ & C1 & _) & _ & _ & _ & _ & (G12 & G13 & G14 & TG) & (T1 & T2 & TI & PS1) & TB).
  pose proof (proj1 HsmA) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm.
  destruct (arm_base_disj A rb tp0 md0 W st rho (ax_S CX) [O_pcc0; O_st; O_pcm; O_ri] r _ HW HE HFz Hsm SK_x XF_x) as (ob & ox & EO & SKx & BZ).
  destruct ox as [|oc [|os [|om [|ori [|? ?]]]]]; cbn [map] in SKx; try (exfalso; clear -SKx; discriminate SKx).
  assert (SKc : skel oc = skel O_pcc0) by (clear -SKx; congruence). assert (SKs : skel os = skel O_st) by (clear -SKx; congruence).
  assert (SKm : skel om = skel O_pcm) by (clear -SKx; congruence). assert (SKr : skel ori = skel O_ri) by (clear -SKx; congruence).
  rewrite <- (obj_range_skel r oc O_pcc0 SKc) in RNc. rewrite <- (obj_range_skel r os O_st SKs) in RNs.
  rewrite <- (obj_range_skel r om O_pcm SKm) in RNm. rewrite <- (obj_range_skel r ori O_ri SKr) in RNr.
  assert (PCr : PCE A rb = ag_thread (aa_geom A) + 208 + 80 * c) by (unfold PCE; fold nv c; clear; lia).
  destruct HBn as (HB1 & HB2 & _).
  apply Forall_forall. rewrite EO. apply Forall_app. split.
  - apply BZ. right; left. rewrite kSpaceSize_val. clear -HB1 HB2. lia.
  - repeat apply Forall_cons; try apply Forall_nil; rewrite ?RNc, ?RNs, ?RNm, ?RNr; unfold ranges_disjoint; cbn [fst snd]; rewrite ?PCr;
      unfold region_info, kRegionInfoStride; rewrite ?kSpaceSize_val; clear -HB1 HB2 C1 T1 PS1; lia.
Qed.

Theorem piece_commit : ltac2:(tb__ "0|0|
S7S17S16Q40A1A1S44VTR;S36S25S37VA;VKc;Vrb;Vtp0;Vmd0;S53Vp;U1Vph;A3A6S54VCX;Veb;Z40000A3R3R2A5R1A2VTR;S36S25S37VA;VKc;Vrb;Vtp0;Vmd0;Vph;A6VCX;R4R3A5R2A2F_;FQ;Ftp;Fr;").
Proof.
  intros r tp Q HT.
  apply (tr_pure Kc TR KIT (forall o, In o (ss_objs (ax_S CX)) -> ranges_disjoint (obj_range r o) (B, B + 262144))).
  { intros w Hw. exact (commit_objs r tp w Hw). }
  intros OBJD.
  apply (tr_commit Kc TR KIT (JRp ph) (JRp (ph_set p 1 ph)) CX r tp eb 262144 Q (JR_K A Kc rb tp0 md0 ph)
           (JR_stable A Kc rb tp0 md0 ph _ HKc ltac:(apply Pos.leb_le; exact NX_x)) IC_x R17_x R10_x BEL_x R11_x R12_x R13_x R14_x R15_x eq_refl ltac:(clear; lia)); [|exact HT].
  intros tr ms md Hsp HJ. cbn zeta.
  pose proof HJ as (HFz & HGh & HK & HM & HR & HRM).
  pose proof (HBv r HFz HGh) as EB. destruct HBn as (HB1 & HB2 & HB3).
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF0. unfold cfacts in CF0. cbn zeta in CF0.
  destruct CF0 as (_ & _ & _ & _ & _ & (G12 & G13 & G14 & TG) & _).
  pose proof HE as (_ & HA & _).
  assert (Un : bv_unsigned (Z_to_bv 64 262144) = 262144) by (apply u64_lit; clear; lia).
  destruct (space_commit_model A rb tp0 md0 ph tp md (eval r eb) (Z_to_bv 64 262144) HA HM
              ltac:(rewrite EB; clear -HB1; lia) ltac:(rewrite EB, Un, kSpaceSize_val; clear -HB2; lia)) as (RF & MC & OV & ETOP & ELIM).
  rewrite Un in OV. rewrite EB in OV |- *.
  pose proof (smatch_pendingA_MI segs _ _ _ _ _ _ Hsp) as HMI.
  split; [exact HB3|]. split; [clear -HB1 G13; lia|].
  split.
  { rewrite ETOP. destruct HA as (HG & _). rewrite <- (geom_top _ HG). clear -HB2 G14. lia. }
  split; [exact RF|]. split; [exact MC|]. split; [exact OV|].
  split; [exact (HROOM tp md HM)|].
  split; [exact OBJD|].
  split.
  { intros x Hx. unfold ro_addr. rewrite find_segment_A_off; [reflexivity|]. clear -Hx HB1 G13. lia. }
  split; [intros rr y Hin; rewrite XX_x in Hin; destruct Hin|].

  pose proof (MI_ivs_wf segs _ _ HMI) as (Wm & Wn & Wl).
  split; [exact HFz|]. split; [exact HGh|].
  split.
  { unfold vm_forget_range. rewrite with_vm_backing_with_vm. apply HKc.
    match goal with |- Kc _ (with_vmmaps ?h ?m) =>
      replace (with_vmmaps h m) with (with_vm (mkVmState h (m_vm_lazy m) (m_vm_materialized m)) m) by (destruct m; reflexivity) end.
    apply HKc. exact HK. }
  split.
  { apply (mlink_commit A rb tp0 md0 p ph tp md _ HM PH0 PORD); fold B.
    - rewrite m_vmmaps_vm_forget_range, m_vmmaps_with_vmmaps. reflexivity.
    - rewrite m_vmmaps_vm_forget_range, m_vmmaps_with_vmmaps. reflexivity.
    - rewrite m_vmmaps_vm_forget_range, m_vmmaps_with_vmmaps. reflexivity.
    - rewrite m_vmmaps_vm_forget_range, m_vmmaps_with_vmmaps. reflexivity.
    - rewrite m_vmmaps_vm_forget_range, m_vmmaps_with_vmmaps. cbn [mmap_fixed_rw_next vm_noaccess]. rewrite EB, Un. reflexivity.
    - rewrite m_vm_lazy_vm_forget_range, m_vm_lazy_with_vmmaps. reflexivity.
    -
      set (h' := mmap_fixed_rw_next (m_vmmaps md) (eval r eb) (Z_to_bv 64 262144)). set (md1 := with_vmmaps h' md).
      assert (Hwf1 : ivs_wf (m_vm_lazy md1)) by (unfold md1; rewrite m_vm_lazy_with_vmmaps; exact Wl).
      pose proof (used_commit_le md h' (eval r eb) (Z_to_bv 64 262144) (conj Wm (conj Wn Wl)) eq_refl eq_refl) as PU1. fold md1 in PU1. rewrite EB, Un in PU1.
      pose proof (unpaid_forget_le md1 B (B + 262144) tp Hwf1 (MI_nodupT segs _ _ HMI)) as PU2. apply Nat2Z.inj_le in PU2.
      assert (PU3 : unpaid md1 tp = unpaid md tp) by (unfold md1; apply unpaid_ext; reflexivity). rewrite PU3 in PU2.
      unfold paid. pose proof page_size_pos. fold md1. clear -PU1 PU2 OV H. nia. }
  split; [|exact HRM].
  apply (rlink_grow_quiet A rb ph (ph_set p 1 ph) (fun _ => False) (view segs (rm rb)) (view segs (rm r)) (view segs (rm r)) PQ (ph_quiet_set p 1 ph PQ)); [| | exact HR | |].
  - intros z. rewrite (zone_commit A rb p ph z PH0). tauto.
  - intros z. right. intros X. exact X.
  - intros z _. reflexivity.
  - intros z X. destruct X.
Qed.
End COMMIT.
End SpineMallocR8.

