(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/DGg1Rh.v (commit eb934de95d13, blob 10c8e0724c34) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb), from reply A d751b179ea49 (pin 42c58610e125); module paths changed; 2 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1w AE3d AFeq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AGImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DeallocG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import DGbase DGgm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DGif0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import ADIfaceA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require DGfv DGfw DGgd DGgf AFew AFeu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require DGg1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require DIfaceRh.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Ltac numc := ceil; unfold zone3, zone3cases, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize,
kPrimResvSize, kNodesBlockSize, kStoreBlockSize, t_qc, t_cache, t_unwinding, t_stats, DFSTACK, TFIB_IMG_END, DEP_STK, SHADOW_OFF,
TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_W, TFIB_IAL_FLAG, TFIB_TP, TFIB_TSD in *.
Lemma wvb_self_e : forall md, with_vm_backing (m_vm_lazy md) (m_vm_materialized md) md = md.
Proof. intros [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Lemma amreal_ask_depot_e {R} : forall trc s (k : Z -> itree astate R) (Wx : world tfibsegs) c Q,
SRr tfibsegs Wx c (fun W1 c1 => exists z, aok s (KDepot trc) z /\ amreal tfibsegs (k z) W1 c1 Q) ->
amreal tfibsegs (IAsk (KDepot trc) s k) Wx c Q.
Proof. intros trc s k Wx c Q H. exact H. Qed.
Lemma amreal_pure_e {A R} : forall (m : M A) (f : A -> M R) s a s' (W : world tfibsegs) c Q,
m s = IRet (a, s') -> amreal tfibsegs (f a s') W c Q -> amreal tfibsegs (bind m f s) W c Q.
Proof. intros m f s a s' W c Q E H. unfold bind. rewrite E. cbn [ibind]. exact H. Qed.

Section e.
Local Open Scope am_scope.
Variable B : asyms.
Variable U : list Z -> astate -> Prop.
Variable ft : sptr -> list Z -> M unit.
Variables (ARX ARXr : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop).
Variable AOX : alayout -> astate -> Z -> Prop.
Variable rpre : astate -> Z -> Prop.
Variable lpost : astate -> Prop.
Variable fpre : alayout -> astate -> world tfibsegs -> (word -> option byte) -> sptr -> Z -> Prop.
Variable dpost : Z -> alayout -> astate -> world tfibsegs -> list Z -> Z -> (word -> option byte) -> Prop.
Variable dbody : astate -> M unit.
Variable L24 : Z.
Variable QB : astate -> Prop.
Variable DRq : astate -> list chunk -> list Z -> Prop.
Variable MP : (word -> option byte) -> Prop.
Hypothesis IF : DIfaceRh.DIface_rh B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq MP.
Hypothesis TS : TfibSyms B.
Local Notation Fshape := (DIfaceRh.dih_shape B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq MP IF).
Local Notation Fview := (DIfaceRh.dih_view B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq MP IF).
Local Notation Fdepot := (DIfaceRh.dih_depot B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq MP IF).
Local Notation Fdaok := (DIfaceRh.dih_dpost_aok B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq MP IF).

Lemma to_enq : forall inst so bp ly S W regs mem md p n tr k hb1 j1 j2 j3 (Q : unit * astate -> world tfibsegs -> config -> Prop),
DeallocG.dealloc_pre tfibsegs B U ARX rpre fpre 1 inst so bp ly S W regs mem md p n tr -> In (p, n) (blocks S) ->
find_user (st_chunks S) p = Some k -> ck_state k = CAllocated ->
0 <= hb1 < 256 -> val_mem tfibsegs (mrestrict (w_H W) mem) (sptr_addr B ly p - 16) 4 (2 + 256 * hb1) ->
DGgm.free_hyps W ly (dregs regs (sptr_addr B ly p) inst bp so) mem tr (sptr_addr B ly p) (req_size n) hb1 (st_qthread S) j1 j2 j3 regs ->
(forall z (msE : machine_state) mat E5, aok (dtick S) (KDepot tr) z ->
  msE = mkst (ms_regs msE) (w64 0x36a74) (ms_mem msE) (seg_rom tfibsegs) ->
  (forall k0, (k0 < aHAVf)%nat ->
    ew E5 k0 = ew (DGgm.E0 ly (dregs regs (sptr_addr B ly p) inst bp so) tr (sptr_addr B ly p) (req_size n) hb1 (st_qthread S) j1 j2 j3) k0) ->
  st_ok tfibsegs E5 DGfw.SS_E (restrict (w_H W) msE) ->
  dmem_m W ly (bv_unsigned (getr regs 2)) mem (sptr_addr B ly p) (req_size n) hb1 (dpost inst ly S W tr z) (ms_mem msE) ->
  amreal tfibsegs ((enqueue (qk k) ;; dmd dbody) (qx S k z tr)) W (mkCfg msE (with_vm_backing (m_vm_lazy md) mat md)) Q) ->
amreal tfibsegs (ft p tr S) W (cfg_at tfibsegs 0x322a4 regs mem md) Q.
Proof using IF TS.
intros inst so bp ly S W regs mem md p n tr k hb1 j1 j2 j3 Q PRE HBLK Hf Hst Hhb1 Hhdr FH HC.
destruct PRE as (HARX & HRP & Hra & Hra4096 & Hal & Hlo & Hbot & Hhi & Hpres & Hgp & Htp & Hr10 & Hr11 & Hr12 & Hr13 & Hr14 & Hr15 &
Hso1 & Hso2 & Hso3 & Hbp1 & Hbp2 & Hbp3 & Htrlen & PSO & PLEN & PBUF & Htr & Hp0 & HFP).
pose proof (dv_nonnull B W ly inst mem S p n (Fview inst ly S W mem md p n HARX HRP HFP HBLK)) as PNN.
rewrite (Fshape p n tr S k PNN HRP HBLK Hf Hst).
set (pa := sptr_addr B ly p) in *. set (nn := req_size n) in *. set (q := st_qthread S) in *.
set (regs0 := dregs regs pa inst bp so) in *.
unfold spZ, raZ in *.
assert (R2 : getr regs0 2%bv = getr regs 2%bv) by (unfold regs0; apply dregs_other; vm_compute; discriminate).
pose proof (DGg1.sp_facts_m W ly regs0 mem tr pa nn hb1 q j1 j2 j3 regs FH) as SPF. rewrite R2 in SPF. unfold DFSTACK in SPF.
assert (Usp : 0 <= bv_unsigned (getr regs 2) < 2 ^ 64) by apply u64_range.
assert (BP0 : bv_unsigned (getr regs0 12) = bp).
{ unfold regs0. rewrite dregs_12. unfold w64. apply unsigned_lit_small. clear - SPF Usp Hbp1 Hbp2. unfold kHighMemEnd, kHighMemBeg in *. lia. }
pose proof (DGgm.LYB W ly regs0 mem tr pa nn hb1 q j1 j2 j3 regs FH) as LB.
pose proof (DGgm.derived_ranges W ly regs0 mem tr pa nn hb1 q j1 j2 j3 regs FH) as DR.
pose proof (DGgm.N8_ge W ly regs0 mem tr pa nn hb1 q j1 j2 j3 regs FH) as [N8a N8b].
pose proof (DGgm.fh_Hp _ _ _ _ _ _ _ _ _ _ _ _ _ FH) as ZP.
pose proof (DGgm.fh_Hp10 _ _ _ _ _ _ _ _ _ _ _ _ _ FH) as Hp10.
pose proof (DGgm.fh_Hnn _ _ _ _ _ _ _ _ _ _ _ _ _ FH) as Hnn.
unfold depot_put. cbn [bind askz ibind]. apply amreal_ask_depot_e.
unfold cfg_at. rewrite <- (wvb_self_e md) at 1.
eapply SRr_bind; [exact (DGgd.segB W ly regs0 mem md tr pa nn hb1 q j1 j2 j3 regs (m_vm_materialized md) FH)|].
intros W1 c1 _ (-> & msD & mat1 & E3 & -> & HshD & HEn3 & HS & MEQD & TRQ & PRESD).
rreg HS (1%bv : bv 5) Q1. rreg HS (2%bv : bv 5) Q2.
rewrite (HEn3 2%nat ltac:(cbv; lia)), (DGgm.E2 ly regs0 tr pa nn hb1 q j1 j2 j3) in Q2.
assert (SPD : bv_unsigned (getr (ms_regs msD) 2) = bv_unsigned (getr regs0 2) - 48).
{ rewrite Q2. unfold w64. rewrite unsigned_lit_small; [reflexivity|]. rewrite R2. clear - SPF Usp. numc. lia. }
rewrite HshD. eapply SRr_bind.
{ apply (Fdepot inst ly S W mem md tr (ms_regs msD) (ms_mem msD) (with_vm_backing (m_vm_lazy md) mat1 md) bp HARX Htr).
  - intros x Hx. apply (proj1 MEQD).
    + destruct Hx as [Hd|[Hc _]]; [exact (proj1 (DGg1.DZONE_out_m W ly regs0 mem tr pa nn hb1 q j1 j2 j3 regs FH _ Hd)) |
      exact (DGg1.CZONE_out_m W ly regs0 mem tr pa nn hb1 q j1 j2 j3 regs FH _ Hc)].
    + destruct Hx as [Hd|[_ Hi]]; [exact (proj1 (proj2 (DGg1.DZONE_out_m W ly regs0 mem tr pa nn hb1 q j1 j2 j3 regs FH _ Hd))) | exact Hi].
  - rreg HS (10%bv : bv 5) R. rewrite R, (HEn3 12%nat ltac:(cbv; lia)), (DGgm.E12 ly regs0 tr pa nn hb1 q j1 j2 j3).
    unfold regs0. rewrite dregs_12. reflexivity.
  - rreg HS (11%bv : bv 5) R. rewrite R, (HEn3 36%nat ltac:(cbv; lia)), (DGgm.EaLEN ly regs0 tr pa nn hb1 q j1 j2 j3). reflexivity.
  - rreg HS (3%bv : bv 5) R. rewrite R, (HEn3 3%nat ltac:(cbv; lia)), (DGgm.Er ly regs0 tr pa nn hb1 q j1 j2 j3 3 3%bv eq_refl).
    unfold regs0. rewrite dregs_other by (vm_compute; discriminate). exact Hgp.
  - rreg HS (4%bv : bv 5) R. rewrite R. reflexivity.
  - rreg HS (1%bv : bv 5) R. rewrite R. apply YK0s.ret_ok_even. reflexivity.
  - intros i Hi. pose proof (TRQ i Hi) as TQ. rewrite BP0 in TQ. exact TQ.
  - exact Hbp3.
  - clear - SPF Hbp1. lia.
  - exact Hbp2.
  - right. rewrite SPD, R2. lia.
  - rewrite SPD, R2. replace (bv_unsigned (getr regs 2) - 48) with (bv_unsigned (getr regs 2) + (-3) * 16) by lia.
    rewrite Z_mod_plus_full. exact Hal.
  - rewrite SPD, R2. clear - SPF. unfold DEP_STK, YFl0C.DEP_STK in *. lia.
  - rewrite SPD, R2. lia.
  - intros a Ha. rewrite SPD in Ha. apply PRESD. unfold DEP_STK, YFl0C.DEP_STK, DFSTACK in *. lia. }
intros W2 c2 _ (-> & z & regs4 & mem4 & mat4 & -> & HP4 & Hfr4 & Hpr4 & DP4). srr_norm_model.
rewrite SPD in Hfr4.
pose proof (Fdaok _ _ _ _ _ _ _ DP4) as AOK.
rewrite Q1. eapply SRr_bind.
{ apply (DGgf.segCm1 W ly regs0 mem md tr pa nn hb1 q j1 j2 j3 regs FH msD E3 regs4 mem4 mat4).
  split; [exact HshD|]. split; [exact HEn3|]. split; [exact HS|]. split; [exact HP4|]. split; [exact Hfr4|].
  split; [exact Hpr4|]. split; [exact MEQD | exact PRESD]. }
intros W3 c3 _ (-> & msE & matE & E5 & -> & HshE & HEn5 & HS5 & EQE & PRES5).
apply SRr_ret. exists z. split; [exact AOK|].
assert (BT : bv_unsigned (ew E5 32) = ly_T ly).
{ rewrite (HEn5 32%nat ltac:(cbv; lia)), (DGgm.EaT ly regs0 tr pa nn hb1 q j1 j2 j3). unfold w64. apply unsigned_lit_small.
  destruct LB as (LB1 & LB2 & _). clear - LB1 LB2. numc. lia. }
assert (B10 : bv_unsigned (ew E5 10) = pa).
{ rewrite (HEn5 10%nat ltac:(cbv; lia)), (DGgm.E10 ly regs0 tr pa nn hb1 q j1 j2 j3), Hp10. unfold w64. apply unsigned_lit_small.
  clear - DR N8a. numc. lia. }
assert (R38 : rho_of E5 38%nat = 2 + 256 * hb1).
{ unfold rho_of. rewrite (HEn5 38%nat ltac:(cbv; lia)), (DGgm.EaHW ly regs0 tr pa nn hb1 q j1 j2 j3). unfold w64, DGgm.HWv.
  apply unsigned_lit_small. lia. }
assert (T1V : zev (rho_of E5) T1term = 3 + 256 * hb1) by (apply T1_val; [exact Hhb1 | exact R38]).
assert (OT : forall a, ly_T ly <= a < ly_T ly + kThreadObjSize -> off_img a) by (intros a Ha; exact (zone3_off_img _ _ a (proj1 LB) Ha)).
assert (OP : forall a, pa - 16 <= a < pa + 8 -> off_img a) by (intros a Ha; apply (zone3_off_img _ _ a ZP); lia).
assert (DM : dmem_m W ly (bv_unsigned (getr regs0 2)) mem pa nn hb1 (dpost inst ly S W tr z) (ms_mem msE)).
{ apply (DGg1.dmem_m_ok W ly regs0 mem tr pa nn hb1 q j1 j2 j3 regs FH (dpost inst ly S W tr z) (ms_mem msD) mem4 (ms_mem msE)
    MEQD Hfr4 Hpr4 DP4 EQE PRES5).
  - intros a [[Ha|Ha]|[Ha|Ha]].
    + eapply (st_ok_window_apresent_off (w_H W) E5 _ _ 34 _ a HS5); [reflexivity
      | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BT; clear - Ha; unfold t_unwinding in *; lia
      | apply OT; clear - Ha; unfold kThreadObjSize, t_unwinding in *; lia].
    + eapply (st_ok_window_apresent_off (w_H W) E5 _ _ 35 _ a HS5); [reflexivity
      | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BT; clear - Ha; unfold t_stats in *; lia
      | apply OT; clear - Ha; unfold kThreadObjSize, t_stats in *; lia].
    + eapply (st_ok_window_apresent_off (w_H W) E5 _ _ 36 _ a HS5); [reflexivity
      | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite B10; clear - Ha; lia
      | apply OP; clear - Ha; lia].
    + eapply (st_ok_window_apresent_off (w_H W) E5 _ _ 37 _ a HS5); [reflexivity
      | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite B10; clear - Ha; lia
      | apply OP; clear - Ha; lia].
  - memv HS5 36%nat 0%nat; [cbn [base_val YP09.r_base]; rewrite B10; lia | apply DGgf.denot_by_zev; [reflexivity | lia | exact T1V] | lia].
  - memv HS5 36%nat 1%nat; [cbn [base_val YP09.r_base]; rewrite B10; lia
    | cbn [sv_denot]; rewrite (HEn5 39%nat ltac:(cbv; lia)), (DGgm.EaN ly regs0 tr pa nn hb1 q j1 j2 j3); unfold w64; rewrite Zbv_add_unsigned; f_equal; lia
    | lia].
  - memv HS5 34%nat 0%nat; [cbn [base_val YP09.r_base]; rewrite BT; unfold t_unwinding; lia | reflexivity | lia]. }
rewrite R2 in DM.
pose proof AOK as AOK0.
destruct AOK as [-> | [-> _]].
- cbn [Z.eqb ret ibind]. eapply amreal_pure_e; [reflexivity|]. exact (HC 0 msE matE E5 AOK0 HshE HEn5 HS5 DM).
- cbn [Z.eqb bind get ret ibind].
  lazymatch goal with |- context [mcheck ?b1 14] => destruct b1 end; cbn [mcheck ret ibind]; [|exact I].
  lazymatch goal with |- context [mcheck ?b2 13] => destruct b2 end; cbn [mcheck ret put ibind]; [|exact I].
  eapply amreal_pure_e; [reflexivity|]. exact (HC 1 msE matE E5 AOK0 HshE HEn5 HS5 DM).
Qed.
End e.
End f.
