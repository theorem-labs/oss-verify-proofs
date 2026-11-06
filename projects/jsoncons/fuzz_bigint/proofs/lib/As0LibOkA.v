(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import HeapIface HeapIfaceA IcptIfaceA LibIface LibIfaceA L5Defs L5DefsA L5CoreA L5CoreSpecsA
   L5ParseSpecsA L5OpmodSpecsA L5UnwindSpecsA ArtIfaceInst ArtIfaceLayout XIcptA XIcptAs0Kit XIcptAs0 As0MainPhaseA L5TopA L5AE1Top L5ACatch1 L5ACatch2 L5ACatch3
   L5CoreSliceA L5AStrInit L5ACopy L5ACopyS L5ACstr L5AStrctor L5ATobig L5ADetail L5AMul10 L5AAddd L5AAssign L5AOpdel L5ADivWireC As0DrvLibL As0DrvLibInit As0DrvG As0DrvMain.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition LayA0 : lib_layoutA := L5TOPA.TopLayA 73728 6 0 4 8 8 (fun c => 8 * c + 640) (fun c => 24 * c + 640) art_L.

Section LibOk.
Variable scfg : SpuriousCfg.
#[local] Instance scfgP : ScfgP := MkScfgP scfg.
Variable IL : icpt_layout.
Hypothesis ILY : as0_icpt_layout IL.
(* [comment removed for export] *)
Hypothesis HOM1 : forall ar HI, asan_iface_ok art_L ar art_C scfg HI -> aicpt_ok art_L ar IL scfg HI ->
  L5OMA.opmod1A_spec art_L ar HI L5USA.XS (L5USA.xs_pre ar) L5USA.xs_foot (L5USA.e2_landed art_L) (L5USA.e3_landed art_L) 73728 6 0 4 8 (fun c => 8 * c + 640).
Hypothesis HOM2 : forall ar HI, asan_iface_ok art_L ar art_C scfg HI -> aicpt_ok art_L ar IL scfg HI ->
  L5OMA.opmod2A_spec art_L ar HI 73728 6 0 4 8 (fun c => 24 * c + 640).

Theorem as0_lib_ok : lib_ok_stmt scfg art_L art_C IL LayA0 L5TOPA.TopLSA.
Proof.
  intros ar HI HIok ICok. split. reflexivity.
  pose proof art_as0_layout as LY. pose proof art_unw_layout as UNWL.
  pose proof (L5SLICEA.opnew_ok (SCFG_P := scfgP) art_L ar art_C HI LY HIok) as Hnew.
  pose proof (L5SLICEA.reserve_ok (SCFG_P := scfgP) art_L ar art_C HI LY HIok) as Hrsv.
  pose proof (L5SLICEA.resize_ok (SCFG_P := scfgP) art_L ar art_C HI LY HIok) as Hrz.
  pose proof (L5ADEL.opdel_sized_ok (SCFG_P := scfgP) art_L ar art_C HI LY HIok) as Hdel.
  pose proof (L5AASG.assign_ok (SCFG_P := scfgP) art_L ar art_C HI LY HIok Hrz) as Hasg.
  pose proof (L5AMUL.mul10_ok (SCFG_P := scfgP) art_L ar art_C HI LY HIok Hrz) as Hmul.
  pose proof (L5AADD.addd_ok (SCFG_P := scfgP) art_L ar art_C HI LY HIok Hrz) as Hadd.
  pose proof (L5ADET.detail_ok (SCFG_P := scfgP) art_L ar art_C IL HI LY ILY HIok ICok Hasg Hrsv Hmul Hadd Hdel) as Hdet.
  pose proof (L5ATB.tobig4_ok (SCFG_P := scfgP) art_L ar art_C IL HI LY ILY HIok ICok Hdet) as Htb4.
  pose proof (L5ATB.tobig3_ok (SCFG_P := scfgP) art_L ar art_C IL HI LY ILY HIok ICok Hdet) as Htb3.
  apply (L5TOPA.top_iface_okA (SCFG_P := scfgP) art_L ar art_C HI IL LY HIok UNWL 73728 6 0 4 8 8 (fun c => 8 * c + 640) (fun c => 24 * c + 640)).
  - exact (L5ASTR.strinit_ok (SCFG_P := scfgP) art_L ar art_C HI LY HIok Hnew).
  - exact Hdel.
  - exact (L5ACPY.copy_ok (SCFG_P := scfgP) art_L ar art_C HI LY HIok Hnew).
  - exact (L5ACPS.copy_stk_ok (SCFG_P := scfgP) art_L ar art_C HI LY HIok Hnew).
  - exact (L5ACST.cstr_ok (SCFG_P := scfgP) art_L ar art_C IL HI LY ILY HIok ICok Htb4).
  - apply (L5ASC.strctor_norm_ok (SCFG_P := scfgP) art_L ar art_C IL HI LY HIok). unfold L5USA.CHAIN_SCR. lia. exact Htb3.
  - exact (HOM1 ar HI HIok ICok).
  - exact (HOM2 ar HI HIok ICok).
  - exact (L5AE1Top.e1_chainA_ok (SCFG_P := scfgP) art_L ar art_C IL HI LY ILY HIok ICok as0_icpt_fill as0_icpt_copy as0_icpt_tls UNWL).
  - exact (L5ACA1.catch1A_ok (SCFG_P := scfgP) art_L ar art_C HI LY HIok as0_icpt_fill as0_icpt_copy as0_icpt_tls UNWL).
  - exact (L5ACA2.catch2A_ok (SCFG_P := scfgP) art_L ar art_C HI LY HIok as0_icpt_fill as0_icpt_copy as0_icpt_tls UNWL).
  - exact (L5ACA3.catch3A_ok (SCFG_P := scfgP) art_L ar art_C HI LY HIok as0_icpt_fill as0_icpt_copy as0_icpt_tls UNWL).
  - split; [lia | reflexivity].
  - split; [lia | intros c Hc; lia].
  - split; [lia | intros c Hc; lia].
  - split; intros c c' Hc; lia.
  - intros c Hc. unfold L5USA.EXC23_SZ, L5USA.REF2_SZ. lia.
  - intros c Hc. unfold L5USA.EXC23_SZ, L5USA.MSG3_SZ, L5USA.REF3_SZ. lia.
Qed.
End LibOk.

(* [comment removed for export] *)
Theorem as0_lib_ok_closed (scfg : SpuriousCfg) (IL : icpt_layout) : as0_icpt_layout IL -> lib_ok_stmt scfg art_L art_C IL LayA0 L5TOPA.TopLSA.
Proof.
  intros ILY. apply (as0_lib_ok scfg IL ILY).
  - intros ar HI HIok ICok.
    exact (L5ADWIREC.Hom1_closed (SCFG_P := scfgP scfg) art_L ar art_C IL HI art_as0_layout ILY HIok ICok as0_icpt_fill as0_icpt_copy as0_icpt_tls art_unw_layout).
  - intros ar HI HIok ICok.
    exact (L5ADWIREC.Hom2_closed (SCFG_P := scfgP scfg) art_L ar art_C HI art_as0_layout HIok).
Qed.

(* [comment removed for export] *)
Lemma as0_lib_layout : drv_lib_layoutA LayA0 art_L.
Proof.
  constructor.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - vm_compute. repeat split; discriminate.
  - reflexivity.
  - intros iv Hin. cbn in Hin. unfold LIB_HOLES.
    destruct Hin as [<-|[<-|[<-|[]]]]; cbn [fst snd]; [exists 0x6101c8, 0x6101d4 | exists 0x6103f0, 0x6103f8 | exists 0x610c31, 0x610c37]; (split; [cbn [In]; tauto | lia]).
  - intros iv Hin. cbn in Hin. unfold LIB_HOLES. destruct Hin as [<-|[]]; cbn [fst snd]. exists 0x610c64, 0x610c68. split; [cbn [In]; tauto | lia].
  - intros n Hn. cbn. unfold L5TOPA.TOP_KT, L5TOPA.TOP_NEED, L5TOPA.TOP_REST. lia.
  - intros k Hk. cbn [In] in Hk. destruct Hk as [<-|[<-|[<-|[]]]]; vm_compute; repeat split; discriminate.
Qed.

Lemma as0_lib_cells : drv_lib_cellsA LayA0.
Proof.
  constructor; try reflexivity.
  - intros iv Hin. cbn in Hin. unfold LIBINIT_IMG.
    destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [fst snd];
      first [ (exists 65536, 880640; split; [cbn [In]; tauto | lia]) | (exists 6357393, 6357396; split; [cbn [In]; tauto | lia]) | (exists 6357397, 6360120; split; [cbn [In]; tauto | lia]) | (exists 892736, 892792; split; [cbn [In]; tauto | lia]) | (exists 6492112, 6492160; split; [cbn [In]; tauto | lia]) ].
  - cbn. lia.
  - intros iv Hin. cbn in Hin. destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [fst snd]; lia.
Qed.

Lemma as0_lib_budget : drv_budgetA art_L LayA0.
Proof.
  intros n Hn. unfold credA, CAPk, adebit. cbn. unfold L5TOPA.TOP_KT, L5TOPA.TOP_NEED, L5TOPA.TOP_REST. lia.
Qed.
