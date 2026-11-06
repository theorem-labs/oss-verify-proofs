(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Specs Run.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Refusable.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundR SymCall SymExit Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import InitLayout InitState SumConv SysOpen.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec Require Import DriverSpec SpecTop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model RtCells Iface IfaceEx IfaceS InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import BudA TobjJA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts Code Init Start0 StartLib KxA StartMain StartArgBytes
  DrvTLXa DrvIfaceT DrvIfaceR DrvIfaceM DrvM_states DrvM DrvR DrvR_facts DrvR_dstates DrvFw MainJoin SpineA Lib_fuzz_iface2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import TopA.
(* [comment removed for export] *)
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Inv TopGlueA ContractStackMalloc ContractStackFree
  ContractFreeNull ContractFreeNullInit MallocHit0 MallocHit0E RebuildM SegD_wf AllocLaws InvInitH MallocAsm MallocAsmS CallocAsm SpineMallocSec2 ContractFreeNullTop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Asan_memset_contract Asan_memcpy_contract Asan_set_shadow_iface Asan_set_shadow00 Asan_set_shadow Start7 StartTop StartHandoff StartHandoffFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require InvQ8 F0A_rebuild F0A_drain F0A_skeln F0A_cN0 F0A_cN1 F0A_cN2 F0A_cLN0 F0A_cLN1 F0A_cLN2 F0A_top F0A_hxN0 F0A_hxN1 F0A_hxN2 F0A_hxLN0 F0A_hxLN1 F0A_hxLN2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_iface Lib_load_obj_pf Lib_fuzz_one_pf Asan_memcpy48_contract Asan_memcpyR_contract.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition AInv_A : AA -> valuation -> list word -> Model -> Prop := Inv.AInvA segsA.

(* [comment removed for export] *)
Definition CST_A : list (Z * Z) := DrvTLXa.CST_drv ++ DrvIfaceR.CST_drv2.

(* [comment removed for export] *)
Definition XGL_A : list (Z * Z) :=
  Eval vm_compute in map (fun p : sv * sv => match p with (SLit b, SLit n) => (b, n) | _ => (0, 0) end) OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_fuzz_iface.X_lits.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition range_inb (l : list (Z * Z)) (r : Z * Z) : bool :=
  existsb (fun q => (fst q <=? fst r) && (fst r + snd r <=? fst q + snd q)) l.
Definition ranges_inb (l sub : list (Z * Z)) : bool := forallb (range_inb l) sub.
Definition range_apartb (r q : Z * Z) : bool := (fst r + snd r <=? fst q) || (fst q + snd q <=? fst r).
Definition ranges_apartb (l m : list (Z * Z)) : bool := forallb (fun r => forallb (range_apartb r) m) l.

Lemma in_rangesZ_app : forall l1 l2 a, in_rangesZ (l1 ++ l2) a <-> in_rangesZ l1 a \/ in_rangesZ l2 a.
Proof.
  intros l1 l2 a. unfold in_rangesZ. split.
  - intros (b & n & Hin & Hr). apply in_app_or in Hin. destruct Hin as [Hin|Hin]; [left|right]; exists b, n; tauto.
  - intros [(b & n & Hin & Hr)|(b & n & Hin & Hr)]; exists b, n; split; [apply in_or_app; tauto|exact Hr|apply in_or_app; tauto|exact Hr].
Qed.
Lemma ranges_inb_sound : forall l sub, ranges_inb l sub = true -> forall a, in_rangesZ sub a -> in_rangesZ l a.
Proof.
  intros l sub H a (b & n & Hin & Hr). unfold ranges_inb in H.
  pose proof (proj1 (forallb_forall _ _) H (b, n) Hin) as Hb. unfold range_inb in Hb.
  apply existsb_exists in Hb. destruct Hb as ([b' n'] & Hin' & Hb). cbn [fst snd] in Hb.
  apply andb_prop in Hb. destruct Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  exists b', n'. split; [exact Hin'|lia].
Qed.
Lemma ranges_apartb_sound : forall l m, ranges_apartb l m = true -> forall a, in_rangesZ l a -> in_rangesZ m a -> False.
Proof.
  intros l m H a (b & n & Hin & Hr) (b' & n' & Hin' & Hr'). unfold ranges_apartb in H.
  pose proof (proj1 (forallb_forall _ _) H (b, n) Hin) as Hb.
  pose proof (proj1 (forallb_forall _ _) Hb (b', n') Hin') as Hq. unfold range_apartb in Hq. cbn [fst snd] in Hq.
  apply orb_prop in Hq. destruct Hq as [Hq|Hq]; apply Z.leb_le in Hq; lia.
Qed.

(* [comment removed for export] *)
Definition cell_rng (c : acell) : Z * Z := (c_addr c, Z.of_nat (c_w c)).
Definition cst_okb (CST : list (Z * Z)) : bool :=
  forallb (fun r => (IMG_LO <=? fst r) && (fst r + snd r <=? IMG_HI) && (0 <=? snd r)) CST
  && ranges_apartb CST (map cell_rng (rtc_cells_img RTC_A G0)).
Lemma cst_okb_sound : forall CST, cst_okb CST = true -> cst_ok CST.
Proof.
  intros CST H a Ha. unfold cst_okb in H. apply andb_prop in H. destruct H as [H1 H2].
  pose proof Ha as (b & n & Hin & Hr).
  pose proof (proj1 (forallb_forall _ _) H1 (b, n) Hin) as Hb. cbn [fst snd] in Hb.
  apply andb_prop in Hb. destruct Hb as [Hb H0]. apply andb_prop in Hb. destruct Hb as [HL HH].
  apply Z.leb_le in HL. apply Z.leb_le in HH.
  split; [lia|].
  destruct (cells_footb (rtc_cells_img RTC_A G0) a) eqn:E; [|reflexivity]. exfalso.
  unfold cells_footb in E. apply existsb_exists in E. destruct E as (c & Hc & E). unfold in_cellb in E.
  apply andb_prop in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  apply (ranges_apartb_sound _ _ H2 a Ha). exists (c_addr c), (Z.of_nat (c_w c)). split; [|lia].
  apply in_map_iff. exists c. split; [reflexivity|exact Hc].
Qed.

Lemma HCSTok_A : cst_ok CST_A.
Proof. apply cst_okb_sound. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HCST_A : forall a, in_rangesZ CST_A a -> 0 <= a < IMG_HI.
Proof. intros a Ha. destruct (HCSTok_A a Ha) as [H _]. unfold IMG_LO in H. lia. Qed.
Lemma HXGLok_A : xgl_ok XGL_A.
Proof.
  intros a (b & n & Hin & Hr).
  assert (Hb : forallb (fun r => (0 <=? fst r) && (fst r + snd r <=? IMG_HI)) XGL_A = true) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  pose proof (proj1 (forallb_forall _ _) Hb (b, n) Hin) as H. cbn [fst snd] in H.
  apply andb_prop in H. destruct H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.
Lemma HXGL_A : forall a, in_rangesZ XGL_A a -> 0 <= a < IMG_HI.
Proof. exact HXGLok_A. Qed.
Lemma HCSTdrv_A : forall z, in_rangesZ DrvTLXa.CST_drv z -> in_rangesZ CST_A z.
Proof. intros z H. apply (proj2 (in_rangesZ_app _ _ z)). left. exact H. Qed.
Lemma HCSTdrv2_A : forall z, in_rangesZ DrvIfaceR.CST_drv2 z -> in_rangesZ CST_A z.
Proof. intros z H. apply (proj2 (in_rangesZ_app _ _ z)). right. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma HCSTM_A : forall a, in_rangesZ CST_A a -> in_rangesZ RebuildM.IMG_M a -> False.
Proof. exact (ranges_apartb_sound CST_A RebuildM.IMG_M ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)). Qed.
Lemma HCSTS_A : forall a, in_rangesZ CST_A a -> in_rangesZ SpineMallocSec2.IMG_S a -> False.
Proof. exact (ranges_apartb_sound CST_A SpineMallocSec2.IMG_S ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)). Qed.
(* [comment removed for export] *)
Lemma HCSTD_A : forall a, in_rangesZ CST_A a -> ~ SegD_wf.dfp_static a.
Proof. apply MallocHit0.cstD_okb_sound. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
(* [comment removed for export] *)
Lemma HCST2_A : forall a, in_rangesZ CST_A a -> ~ (Inv.IA_BEG <= a < Inv.IA_END) /\ ~ (0x180e88 <= a < 0x180e8c).
Proof.
  intros a Ha.
  pose proof (ranges_apartb_sound CST_A [(Inv.IA_BEG, Inv.IA_END - Inv.IA_BEG); (0x180e88, 4)] ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) a Ha) as H.
  split; intros Hr; apply H; [exists Inv.IA_BEG, (Inv.IA_END - Inv.IA_BEG) | exists 0x180e88, 4]; split; cbn; try tauto; unfold Inv.IA_BEG, Inv.IA_END in *; lia.
Qed.
(* [comment removed for export] *)
Lemma HXlits_A : forall a, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_fuzz_iface.in_lits a -> in_rangesZ XGL_A a.
Proof.
  intros a H. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_fuzz_iface.in_lits, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_fuzz_iface.X_lits in H. cbn [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_fuzz_iface.in_litsL] in H.
  unfold in_rangesZ, XGL_A.
  repeat match type of H with
  | _ \/ _ => destruct H as [H|H]; [eexists _, _; split; [ | exact H]; cbn; tauto |]
  | False => destruct H
  end.
Qed.
Lemma HXpow_A : forall a, 145824 <= a < 145824 + 184 -> in_rangesZ XGL_A a.
Proof. intros a H. exists 145824, 184. split; [cbn; tauto | exact H]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma HLV_A : law_view_stmt AInv_A.
Proof. exact InvLaws.AInvA_view. Qed.
Lemma HLF_A : law_fds_stmt AInv_A.
Proof. exact InvLaws.AInvA_fds. Qed.
(* [comment removed for export] *)
Lemma HLV_A_ms : Asan_memset_contract.law_view_stmt AInv_A.
Proof. exact InvLaws.AInvA_view. Qed.
Lemma HLV_A_mc : Asan_memcpy_contract.law_view_stmt AInv_A.
Proof. exact InvLaws.AInvA_view. Qed.

(* [comment removed for export] *)
Lemma LFLAG_A : TobjJAS.law_flag_stmt AInv_A.
Proof. exact InvLaws.AInvA_flag. Qed.
Lemma LFSH_A : TobjJAS.law_fshadow_stmt AInv_A.
Proof. exact InvLaws.AInvA_frame_shadow. Qed.
Lemma HLPP_A : DrvTLXa.law_pp_stmt AInv_A CST_A.
Proof.
  split.
  - exact InvLaws.AInvA_poison_partial.
  - intros H. exact (ranges_apartb_sound CST_A [(DrvTLXa.PPF, 1)] ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) DrvTLXa.PPF H
                       ltac:(exists DrvTLXa.PPF, 1; split; [cbn; tauto | unfold DrvTLXa.PPF; lia])).
Qed.
Lemma HLV_A_ss : Asan_set_shadow.law_view_stmt AInv_A.
Proof. exact InvLaws.AInvA_view. Qed.

Section TopClosedA.
(* [comment removed for export] *)
Lemma TODO_ALA : alloc_lawsA segsA AInv_A CST_A.
Proof. apply (AllocLaws.alloc_laws_A_b CST_A HCSTok_A). OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition TODO_malloc : malloc_contractA segsA AE_A AInv_A CST_A XGL_A := MallocAsm.malloc_contract_A CST_A XGL_A HCSTok_A HXGLok_A HCSTM_A HCSTS_A HCSTD_A.
Definition TODO_malloc_ex : malloc_contractA_ex segsA AE_A AInv_A CST_A XGL_A := MallocAsm.malloc_contract_A_ex CST_A XGL_A HCSTok_A HXGLok_A HCSTM_A HCSTS_A HCSTD_A.
(* [comment removed for export] *)
Definition TODO_calloc : calloc_contractA segsA AE_A AInv_A CST_A XGL_A := CallocAsm.calloc_contract_A CST_A XGL_A HCSTok_A HXGLok_A HCSTM_A HCSTS_A HCSTD_A.
Definition TODO_calloc_ex : calloc_contractA_ex segsA AE_A AInv_A CST_A XGL_A := CallocAsm.calloc_contract_A_ex CST_A XGL_A HCSTok_A HXGLok_A HCSTM_A HCSTS_A HCSTD_A.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma HCSTF_A : forall a, in_rangesZ CST_A a -> in_rangesZ F0A_rebuild.IMG_F a \/ (Inv.IA_BEG <= a < Inv.IA_END) -> False.
Proof.
  intros a Ha [Hf | Hi].
  - exact (AllocLaws.ranges_apartb_sound CST_A F0A_rebuild.IMG_F ltac:(vm_cast_no_check (eq_refl true)) a Ha Hf).
  - exact (proj1 (HCST2_A a Ha) Hi).
Qed.
Lemma HCSTQ_A : forall a, in_rangesZ CST_A a -> ~ InvQ8.QRD_img a.
Proof. apply InvQ8.HCSTQ_of_apart. exact (AllocLaws.ranges_apartb_sound CST_A InvQ8.QRD_IMG ltac:(vm_cast_no_check (eq_refl true))). Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition TODO_free : free_contractA segsA AE_A AInv_A CST_A XGL_A :=
  F0A_top.free_contractA_A CST_A XGL_A HCSTok_A HXGLok_A HCSTF_A HCSTD_A HCSTQ_A HCST2_A
    (F0A_hxN0.HBIGN_N0 CST_A XGL_A HCSTok_A HXGLok_A HCSTF_A HCSTQ_A) (F0A_hxN1.HBIGN_N1 CST_A XGL_A HCSTok_A HXGLok_A HCSTF_A HCSTQ_A) (F0A_hxN2.HBIGN_N2 CST_A XGL_A HCSTok_A HXGLok_A HCSTF_A HCSTQ_A) (F0A_hxLN0.HBIGN_LN0 CST_A XGL_A HCSTok_A HXGLok_A HCSTF_A HCSTQ_A) (F0A_hxLN1.HBIGN_LN1 CST_A XGL_A HCSTok_A HXGLok_A HCSTF_A HCSTQ_A) (F0A_hxLN2.HBIGN_LN2 CST_A XGL_A HCSTok_A HXGLok_A HCSTF_A HCSTQ_A).
Definition TODO_free_ex : free_contractA_ex segsA AE_A AInv_A CST_A XGL_A :=
  F0A_top.free_contractA_ex_A CST_A XGL_A HCSTok_A HXGLok_A HCSTF_A HCSTD_A HCSTQ_A HCST2_A
    (F0A_hxN0.HBIGNE_N0 CST_A XGL_A HCSTok_A HXGLok_A HCSTF_A HCSTQ_A) (F0A_hxN1.HBIGNE_N1 CST_A XGL_A HCSTok_A HXGLok_A HCSTF_A HCSTQ_A) (F0A_hxN2.HBIGNE_N2 CST_A XGL_A HCSTok_A HXGLok_A HCSTF_A HCSTQ_A) (F0A_hxLN0.HBIGNE_LN0 CST_A XGL_A HCSTok_A HXGLok_A HCSTF_A HCSTQ_A) (F0A_hxLN1.HBIGNE_LN1 CST_A XGL_A HCSTok_A HXGLok_A HCSTF_A HCSTQ_A) (F0A_hxLN2.HBIGNE_LN2 CST_A XGL_A HCSTok_A HXGLok_A HCSTF_A HCSTQ_A).
(* [comment removed for export] *)
Definition TODO_free_null : free_null_contractA segsA AE_A AInv_A CST_A XGL_A := ContractFreeNullTop.free_null_contractA_A CST_A XGL_A HCSTok_A HXGLok_A HCST2_A.
Definition TODO_free_null_ex : free_null_contractA_ex segsA AE_A AInv_A CST_A XGL_A := ContractFreeNullTop.free_null_contractA_ex_A CST_A XGL_A HCSTok_A HXGLok_A HCST2_A.

Lemma AC_A : alloc_contractsA segsA AE_A AInv_A CST_A XGL_A.
Proof.
  constructor.
  - exact TODO_malloc.
  - exact TODO_calloc.
  - exact TODO_free.
  - exact TODO_free_null.
  - exact (ContractStackMalloc.stack_malloc_contracts CST_A XGL_A HCSTok_A HXGLok_A).
  - exact (ContractStackFree.stack_free_contracts CST_A XGL_A HCSTok_A HXGLok_A).
  - exact (Asan_memset_contract.aca_asan_memset_of_laws AInv_A CST_A XGL_A TODO_ALA HLV_A_ms HCSTok_A HXGLok_A).
  - exact (Asan_memcpy_contract.aca_asan_memcpy_of_laws AInv_A CST_A XGL_A TODO_ALA HLV_A_mc HCSTok_A HXGLok_A).
Qed.

Lemma ACX_A : alloc_contractsA_ex segsA AE_A AInv_A CST_A XGL_A.
Proof.
  constructor.
  - exact TODO_malloc_ex.
  - exact TODO_calloc_ex.
  - exact TODO_free_ex.
  - exact TODO_free_null_ex.
  - exact (ContractStackMalloc.stack_malloc_contracts_ex CST_A XGL_A HCSTok_A HXGLok_A).
  - exact (ContractStackFree.stack_free_contracts_ex CST_A XGL_A HCSTok_A HXGLok_A).
  - exact (Asan_memset_contract.acx_asan_memset_of_laws AInv_A CST_A XGL_A TODO_ALA HLV_A_ms HCSTok_A HXGLok_A).
  - exact (Asan_memcpy_contract.acx_asan_memcpy_of_laws AInv_A CST_A XGL_A TODO_ALA HLV_A_mc HCSTok_A HXGLok_A).
Qed.

(* [comment removed for export] *)
Lemma SSC_A : forall xx, In xx [0; 245; 248] -> Asan_set_shadow_iface.set_shadow_contractA segsA AE_A AInv_A CST_A XGL_A xx.
Proof.
  intros xx Hin. cbn in Hin. destruct Hin as [<-|[<-|[<-|[]]]].
  - exact (Asan_set_shadow00.set_shadow_00_contract AInv_A CST_A XGL_A TODO_ALA HLV_A_ss HCSTok_A HXGLok_A).
  - exact (Asan_set_shadow.set_shadow_f5_contract AInv_A CST_A XGL_A TODO_ALA HLV_A_ss HCSTok_A HXGLok_A).
  - exact (Asan_set_shadow.set_shadow_f8_contract AInv_A CST_A XGL_A TODO_ALA HLV_A_ss HCSTok_A HXGLok_A).
Qed.
Lemma SSCX_A : forall xx, In xx [0; 245; 248] -> Asan_set_shadow_iface.set_shadow_contractA_ex segsA AE_A AInv_A CST_A XGL_A xx.
Proof.
  intros xx Hin. cbn in Hin. destruct Hin as [<-|[<-|[<-|[]]]].
  - exact (Asan_set_shadow00.set_shadow_00_contract_ex AInv_A CST_A XGL_A TODO_ALA HLV_A_ss HCSTok_A HXGLok_A).
  - exact (Asan_set_shadow.set_shadow_f5_contract_ex AInv_A CST_A XGL_A TODO_ALA HLV_A_ss HCSTok_A HXGLok_A).
  - exact (Asan_set_shadow.set_shadow_f8_contract_ex AInv_A CST_A XGL_A TODO_ALA HLV_A_ss HCSTok_A HXGLok_A).
Qed.

(* [comment removed for export] *)
Definition TODO_malloc_strong : malloc_contractA_strong segsA AE_A AInv_A CST_A XGL_A := MallocAsmS.malloc_contract_A_strong CST_A XGL_A HCSTok_A HXGLok_A HCSTM_A HCSTS_A HCSTD_A.
Definition TODO_malloc_strong_ex : malloc_contractA_strong_ex segsA AE_A AInv_A CST_A XGL_A := MallocAsmS.malloc_contract_A_strong_ex CST_A XGL_A HCSTok_A HXGLok_A HCSTM_A HCSTS_A HCSTD_A.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition TODO_load_obj : Lib_load_obj_iface.load_obj_stmt := Lib_load_obj_pf.load_obj_ok.
Definition TODO_load_obj_ex : Lib_load_obj_iface.load_obj_stmt_ex := Lib_load_obj_pf.load_obj_ok_ex.
Lemma TODO_fuzz_one : forall Kc ok', Kc_ok Kc -> ok_frameKA segsA Kc ok' -> fuzz_one_sumT AInv_A CST_A XGL_A Kc ok'.
Proof.
  intros Kc ok' HKc Hok.
  exact (Lib_fuzz_one_pf.fuzz_one_T AInv_A CST_A XGL_A TODO_ALA HCST_A HXGL_A HXlits_A LFLAG_A LFSH_A Kc HKc ok' Hok AC_A SSC_A
           (Asan_memcpy48_contract.mc48_of_laws AInv_A CST_A XGL_A TODO_ALA HLV_A_mc HCSTok_A HXGLok_A)
           (Asan_memcpyR_contract.mcR_hv_of_laws AInv_A CST_A XGL_A TODO_ALA HLV_A_mc HCSTok_A HXGLok_A)
           TODO_load_obj).
Qed.
Lemma TODO_fuzz_one_ex : forall Kc, Kc_ok Kc -> fuzz_one_sumE AInv_A CST_A XGL_A Kc.
Proof.
  intros Kc HKc.
  exact (Lib_fuzz_one_pf.fuzz_one_E AInv_A CST_A XGL_A TODO_ALA HCST_A HXGL_A HXlits_A LFLAG_A LFSH_A Kc HKc ACX_A SSCX_A
           (Asan_memcpy48_contract.mc48x_of_laws AInv_A CST_A XGL_A TODO_ALA HLV_A_mc HCSTok_A HXGLok_A)
           (Asan_memcpyR_contract.mcRx_hv_of_laws AInv_A CST_A XGL_A TODO_ALA HLV_A_mc HCSTok_A HXGLok_A)
           TODO_load_obj_ex).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Variable sp brk mb : word.
Variable draw : EntryDraw.
Variable inp : ProcInput.
Hypothesis Hent : valid_entry48 imgA (mkEntry sp brk mb draw) inp.
Hypothesis Hinp : valid_input_either inp.
Let lim : Z := target_alloc_limit.

(* [comment removed for export] *)
Let argv : list (list byte) := in_argv inp.
Let FS0 : Fs := in_fs inp.
(* [comment removed for export] *)
Lemma HandM_A : forall w, ARGC inp = 2 -> QMain sp brk mb draw lim inp w ->
  exists (Mm : Model) (B : Z) (rhoM : valuation) (tpM : list word) (A0 : AA),
    SPA segsA (KxA Mm B) DrvIfaceM.S_M rhoM tpM w
    /\ DrvM.P0M (nth 1 argv []) rhoM
    /\ m_fds Mm = std_fds /\ m_fs Mm = FS0
    /\ A0_facts AInv_A Mm B rhoM tpM A0.
Proof. exact (InvInitH.handoff_M_A sp brk mb draw lim inp Hent Hinp eq_refl). Qed.
Lemma HandU_A : forall w, ARGC inp <> 2 -> QMain sp brk mb draw lim inp w ->
  exists (Mm : Model) (B : Z) (rhoM : valuation) (tpM : list word) (A0 : AA),
    SPA segsA (KxA Mm B) DrvIfaceM.S_U rhoM tpM w
    /\ MainJoin.P0U (hd [] argv) rhoM
    /\ m_fds Mm = std_fds /\ m_fs Mm = FS0
    /\ A0_facts AInv_A Mm B rhoM tpM A0.
Proof.
  intros w NE HQ.
  destruct (InvInitH.handoff_U_A sp brk mb draw lim inp Hent Hinp eq_refl w NE HQ) as (Mm & B & rhoM & tpM & A0 & H1 & H2 & H3).
  exists Mm, B, rhoM, tpM, A0. split; [exact H1|]. split; [rewrite TopA.hd_nth0; exact H2 | exact H3].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem top_closed_A :
  SOUND segsA (c0A sp brk mb draw target_alloc_limit inp) (Spec inp) /\
  COMPLETE segsA (c0A sp brk mb draw target_alloc_limit inp) (Spec inp) /\
  ~ reaches_error_a segsA (c0A sp brk mb draw target_alloc_limit inp).
Proof.
  exact (TopA.top_A sp brk mb draw inp Hent Hinp AInv_A CST_A XGL_A
           TODO_ALA HCST_A HXGL_A HLV_A HLF_A HCSTok_A HCSTdrv_A HLPP_A HCSTdrv2_A
           AC_A ACX_A TODO_malloc_strong TODO_malloc_strong_ex
           TODO_fuzz_one TODO_fuzz_one_ex HandM_A HandU_A).
Qed.
End TopClosedA.

(* [comment removed for export] *)
