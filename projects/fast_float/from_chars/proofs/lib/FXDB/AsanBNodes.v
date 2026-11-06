(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct FxLin FxCore FxSound FxMem FxFacts FxSubst FxDrv FxCall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxChRecont FxChFam FxChSep.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require Import AcCarve AcSteps AcEntry AcSplitS AcPsr.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require FxQNode FxQRNodeS AsanQSites AsanPNodes AsanCpS FxBDec.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require FxBDec.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require FxBandNode.

Module AsanOvlNode.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxLoop FxPlan FxFrame FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.FxAcct.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChLib.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChSep.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChEnt FxChStart FxChWv.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChSeg OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChSep OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChNode OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChEnt OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChStart OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChWv.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require FxQNode FxMNode FxRunPost FxRunPostM AsanSNodes AsanCpS.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxQChk OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxQNode OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxMNode OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxRunPost OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxRunPostM OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanSNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanCpS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Record osite : Type := OS { os_pc : Z; os_rD : reg; os_rS : reg; os_rE1 : reg; os_rE2 : reg; os_fail : bv 13 }.
Definition osite_ok (segs : list Segment) (s : osite) : Prop :=
  0 <= os_pc s /\ os_pc s + 12 < two64 /\
  qins segs (os_pc s) 0 (Branch BC_EQ (os_rD s) (os_rS s) (Z_to_bv 13 12)) /\
  qins segs (os_pc s) 1 (Branch BC_GEU (os_rS s) (os_rE2 s) (Z_to_bv 13 8)) /\
  qins segs (os_pc s) 2 (Branch BC_LTU (os_rD s) (os_rE1 s) (os_fail s)).

Definition ovl_chk (s : osite) (S : sst) : bool :=
  let fs := s_facts S in let rgs := s_rgs S in
  let d := rget (s_regs S) (rkey (os_rD s)) in let sr := rget (s_regs S) (rkey (os_rS s)) in
  let nl := lsub (rget (s_regs S) (rkey (os_rE1 s))) sr in
  match s_resv S, find_win rk_rd fs rgs d nl O, find_win rk_rd fs rgs sr nl O with
  | RNone, Some j0, Some j1 =>
      (Z.eqb (s_pc S) (os_pc s) && negb (Nat.eqb j0 j1) && lin_eqb (lsub (rget (s_regs S) (rkey (os_rE2 s))) d) nl &&
       Z.leb 1 (fst (irange fs nl)) && Z.leb (snd (irange fs nl)) (2 ^ 40))%bool
  | _, _, _ => false
  end.
Definition ovl_post (s : osite) (S : sst) : sst := run_post S (os_pc s + 12) [] [].

Section Node.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.
Hypothesis Hwx : wx_segs_nowrap ASEGSN.

#[using="Type"] Lemma btgt_q : forall pc0 k d, btgt (qpc pc0 k) (4 * d) = qpc pc0 (k + d).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros pc0 k d. unfold btgt, v_addi, qpc. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

#[using="Hwx"] Theorem den_ovl : forall s S M E ms model T,
  osite_ok ASEGSN s -> ovl_chk s S = true -> DEN ASEGSN LIMIT model0 mem0 E S M ms model ->
  (forall E' ms' model', agree (s_next S) E E' -> DEN ASEGSN LIMIT model0 mem0 E' (ovl_post s S) M ms' model' ->
      realizes_cfg ASEGSN cfg (mkCfg ms' model') T) ->
  realizes_cfg ASEGSN cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (Hwx : LiaFast.U) => LiaFast.u0).
  intros s S M E ms model T Hs Hck Hd Hk.
  destruct s as [pc0 rD rS rE1 rE2 bf]. destruct Hs as (Hp0 & Hp12 & I0 & I1 & I2). cbn [os_pc os_rD os_rS os_rE1 os_rE2 os_fail] in *.
  unfold ovl_chk in Hck. cbn [os_pc os_rD os_rS os_rE1 os_rE2] in Hck.
  set (fs := s_facts S) in *. set (d := rget (s_regs S) (rkey rD)) in *. set (sr := rget (s_regs S) (rkey rS)) in *.
  set (nl := lsub (rget (s_regs S) (rkey rE1)) sr) in *.
  destruct (s_resv S) eqn:Hrv; try discriminate.
  destruct (find_win rk_rd fs (s_rgs S) d nl O) as [j0|] eqn:Hf0; [|discriminate].
  destruct (find_win rk_rd fs (s_rgs S) sr nl O) as [j1|] eqn:Hf1; [|discriminate].
  repeat match type of Hck with ((_ && _)%bool = true) => apply andb_prop in Hck as [Hck ?Hc] end.
  apply Z.eqb_eq in Hck. apply negb_true_iff, Nat.eqb_neq in Hc2. apply lin_eqb_eq in Hc1. apply Z.leb_le in Hc0, Hc.
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh0 Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  set (H := Hof E M model) in *.
  destruct (sden_0 _ _ _ _ Hsd) as (Hpcv & Hsvc & Hrsv & HR & HG & HD & HF & Hfrm).
  rewrite Hrv in Hrsv. cbn [rsv_ok] in Hrsv.
  cbn [restrict ms_pc_val ms_svc_pending ms_resv ms_regs] in Hpcv, Hsvc, Hrsv, HR.
  (* [comment removed for export] *)
  destruct (find_win_spec _ _ _ _ _ _ _ Hf0) as (Rd & Hj0 & _ & _ & Hw0). rewrite Nat.sub_0_r in Hj0.
  destruct (find_win_spec _ _ _ _ _ _ _ Hf1) as (Rs & Hj1 & _ & _ & Hw1). rewrite Nat.sub_0_r in Hj1.
  pose proof (irange_sound E fs nl HF) as Rn. fold (uE E nl) in Rn. set (N := uE E nl) in *.
  assert (HN : N <= 2 ^ 40) by lia.
  destruct (win_ok_sound E fs d nl Rd HF Hw0 HN) as (W1 & W2 & W3 & W4 & W5).
  destruct (win_ok_sound E fs sr nl Rs HF Hw1 HN) as (V1 & V2 & V3 & V4 & V5).
  pose proof (rgs_disj_nth E (s_rgs S) j0 j1 Rd Rs HD Hc2 Hj0 Hj1) as X. unfold rg_disj in X.
  fold (uE E (rg_base Rd)) (uE E (rg_base Rs)) in X.
  set (Dv := uE E d) in *. set (Sv := uE E sr) in *.
  assert (Hdisj : Dv + N <= Sv \/ Sv + N <= Dv) by (fold N in W2, V2; lia).
  (* [comment removed for export] *)
  assert (HD0 : getr (ms_regs ms) rD = Z_to_bv 64 Dv) by (rewrite (HR rD); unfold Dv, uE; symmetry; apply Z_to_bv_bv_unsigned).
  assert (HS0 : getr (ms_regs ms) rS = Z_to_bv 64 Sv) by (rewrite (HR rS); unfold Sv, uE; symmetry; apply Z_to_bv_bv_unsigned).
  assert (HnE1 : lden E (lsub (rget (s_regs S) (rkey rE1)) sr) = Z_to_bv 64 N) by (unfold N, uE; symmetry; apply Z_to_bv_bv_unsigned).
  assert (HnE2 : lden E (lsub (rget (s_regs S) (rkey rE2)) d) = Z_to_bv 64 N) by (rewrite Hc1; exact HnE1).
  assert (HE1 : getr (ms_regs ms) rE1 = Z_to_bv 64 (Sv + N)).
  { rewrite (HR rE1). rewrite (lsub_const_add E _ sr N HnE1). unfold v_add. fold (uE E sr). fold Sv. rewrite (u_small N) by (unfold two64; lia). reflexivity. }
  assert (HE2 : getr (ms_regs ms) rE2 = Z_to_bv 64 (Dv + N)).
  { rewrite (HR rE2). rewrite (lsub_const_add E _ d N HnE2). unfold v_add. fold (uE E d). fold Dv. rewrite (u_small N) by (unfold two64; lia). reflexivity. }
  pose proof (uE_range E d) as RD. pose proof (uE_range E sr) as RS. fold Dv in RD. fold Sv in RS.
  assert (HDS : 0 <= Dv + N < two64 /\ 0 <= Sv + N < two64) by (unfold two64 in *; lia).
  destruct I0 as (w0 & F0 & E0 & D0). destruct I1 as (w1 & F1 & E1 & D1). destruct I2 as (w2 & F2 & E2 & D2).
  set (mm := mrestrict H (ms_mem ms)). set (regs := ms_regs ms) in *.
  assert (S0 : RiscvSemantics.step ASEGSN (@mkst (mkFP (ms_fregs ms) (ms_fcsr ms)) regs (qpc pc0 0) mm (ms_rom ms)) =
               MachineOk (@mkst (mkFP (ms_fregs ms) (ms_fcsr ms)) regs (qpc pc0 1) mm (ms_rom ms))).
  { rewrite (step_beq_ft ASEGSN regs (qpc pc0 0) mm (ms_rom ms) w0 rD rS (Z_to_bv 13 12) F0 E0 D0); [rewrite qpc_succ; reflexivity|].
    rewrite HD0, HS0. unfold c_eq. apply bv_eqb_neq. intros Hc'. apply (f_equal bv_unsigned) in Hc'. rewrite !u_small in Hc' by lia. lia. }
  assert (Hrun : FxStep.isteps ASEGSN (@mkst (mkFP (ms_fregs ms) (ms_fcsr ms)) regs (qpc pc0 0) mm (ms_rom ms))
                                      (@mkst (mkFP (ms_fregs ms) (ms_fcsr ms)) regs (qpc pc0 3) mm (ms_rom ms))).
  { eapply FxStep.ist_step; [reflexivity | exact S0|].
    destruct (Z_le_gt_dec (Dv + N) Sv) as [Ha|Hb].
    - (* [comment removed for export] *)
      eapply FxStep.ist_step; [reflexivity | | apply FxStep.ist_refl].
      rewrite (step_bgeu_tk ASEGSN regs (qpc pc0 1) mm (ms_rom ms) w1 rS rE2 (Z_to_bv 13 8) F1 E1 D1).
      + change (bv_signed (Z_to_bv 13 8)) with (4 * 2). rewrite btgt_q. reflexivity.
      + rewrite HS0, HE2. unfold c_ltu, bv_ltu. apply Z.ltb_ge. rewrite !u_small by lia. lia.
    - (* [comment removed for export] *)
      assert (Hcb : Sv + N <= Dv) by lia.
      eapply FxStep.ist_step; [reflexivity | |].
      + rewrite (step_bgeu_ft ASEGSN regs (qpc pc0 1) mm (ms_rom ms) w1 rS rE2 (Z_to_bv 13 8) F1 E1 D1); [rewrite qpc_succ; reflexivity|].
        rewrite HS0, HE2. unfold c_ltu, bv_ltu. apply Z.ltb_lt. rewrite !u_small by lia. lia.
      + eapply FxStep.ist_step; [reflexivity | | apply FxStep.ist_refl].
        rewrite (step_bltu_ft ASEGSN regs (qpc pc0 2) mm (ms_rom ms) w2 rD rE1 bf F2 E2 D2); [rewrite qpc_succ; reflexivity|].
        rewrite HD0, HE1. unfold c_ltu, bv_ltu. apply Z.ltb_ge. rewrite !u_small by lia. lia. }
  assert (Hmsr : restrict H ms = @mkst (mkFP (ms_fregs ms) (ms_fcsr ms)) regs (qpc pc0 0) mm (ms_rom ms)).
  { unfold regs, mm. destruct ms as [rg fr pcv sv rv fc mem rom]. cbn [ms_pc_val ms_svc_pending ms_resv] in Hsvc, Hrsv, Hpcv. subst sv rv.
    cbn [ms_pc_val] in Hpcv. rewrite Hck in Hpcv. subst pcv.
    unfold restrict, mkst, qpc. cbn [ms_regs ms_fregs ms_fcsr ms_mem ms_rom fp_regs fp_csr ms_pc_val ms_svc_pending ms_resv].
    replace (pc0 + 4 * 0) with pc0 by lia. reflexivity. }
  apply (den_run_post ASEGSN cfg LIMIT model0 mem0 Hwx E S M ms model T regs (pc0 + 12) [] [] Hd Hrv).
  - fold H. rewrite Hmsr. replace (Z_to_bv 64 (pc0 + 12)) with (qpc pc0 3) by (unfold qpc; f_equal; lia). exact Hrun.
  - apply Forall_nil.
  - apply Forall_nil.
  - intros r _ _. reflexivity.
  - exact Hk.
Qed.
End Node.

(* [comment removed for export] *)
Definition OS_MEMCPY : osite := OS 0x613f8 (Z_to_bv 5 10) (Z_to_bv 5 11) (Z_to_bv 5 19) (Z_to_bv 5 20) (Z_to_bv 13 (0x615bc - 0x61400)).
Lemma OS_MEMCPY_ok : osite_ok ASEGSN OS_MEMCPY.
Proof.
  unfold osite_ok, OS_MEMCPY; cbn [os_pc os_rD os_rS os_rE1 os_rE2 os_fail].
  split; [lia|]. split; [unfold two64; lia|].
  repeat split; unfold qins; eexists; (split; [vm_compute; reflexivity|]); (split; [vm_compute; reflexivity|]); vm_compute;
    repeat match goal with |- @eq (bv _) _ _ => apply bv_eq; vm_compute; reflexivity | |- _ = _ => f_equal end.
Qed.
(* [comment removed for export] *)
End AsanOvlNode.


Module AsanImmS.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec SeqExec CatExec CatSim.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require StepTac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require MemSplit RefMemcpyLib ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.SeqExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.CatExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.CatSim OSSVerify.Proofs.fast_float.from_chars.lib.Common.StepTac.Hoare OSSVerify.Proofs.fast_float.from_chars.lib.Common.MemSplit OSSVerify.Proofs.fast_float.from_chars.lib.Common.RefMemcpyLib OSSVerify.Proofs.fast_float.from_chars.lib.Common.ShapeSet OSSVerify.Proofs.fast_float.from_chars.lib.Common.RealizesCfg OSSVerify.Proofs.fast_float.from_chars.lib.Common.AsanAcct OSSVerify.Proofs.fast_float.from_chars.lib.Common.PlacementCount OSSVerify.Proofs.fast_float.from_chars.lib.Common.AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxLoop FxPlan FxFrame FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxDrv.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.FxAcct OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChLib.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChSep.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChEnt FxChStart FxChWv.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChSeg OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChSep OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChNode OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChEnt OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChStart OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChWv.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require FxQNode FxMchr FxMNode FxRunPost FxRunPostM FxSNodes AsanCpS.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxQChk OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxQNode OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxMchr OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxMNode OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxRunPost OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxRunPostM OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxSNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanCpS.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_np.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_ims.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Abbreviation ASEGSN := AsanUbsan.M.loaded_segments.

Definition IMM_PC : Z := 0x733dc.
Definition IMM_RET : Z := 0x73430.
Definition IMM_HAVS : list reg := List.map xr [11; 12; 13; 14; 15; 16].

Definition imm_chk (S : sst) (M : smodel) : bool :=
  let fs := s_facts S in let rgs := s_rgs S in
  let d := rget (s_regs S) (rkey (xr 10)) in let s := rget (s_regs S) (rkey (xr 11)) in let nl := rget (s_regs S) (rkey (xr 12)) in
  match s_resv S, find_win rk_wz fs rgs d nl O, find_win rk_rd fs rgs s nl O with
  | RNone, Some j0, Some j1 =>
      (Z.eqb (s_pc S) IMM_PC && negb (Nat.eqb j0 j1) && Z.leb 1 (fst (irange fs nl)) && Z.leb (snd (irange fs nl)) (2 ^ 40))%bool
  | _, _, _ => false
  end.
Definition imm_post (S : sst) : sst :=
  match find_win rk_wz (s_facts S) (s_rgs S) (rget (s_regs S) (rkey (xr 10))) (rget (s_regs S) (rkey (xr 12))) O with
  | Some j0 => run_post_all S IMM_RET [] IMM_HAVS j0
  | None => S
  end.

Section Node.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.
Hypothesis Hwx : wx_segs_nowrap ASEGSN.

#[using="Hwx"] Theorem den_imm : forall S M E ms model T,
  imm_chk S M = true -> DEN ASEGSN LIMIT model0 mem0 E S M ms model ->
  (forall E' ms' model', agree (s_next S) E E' -> DEN ASEGSN LIMIT model0 mem0 E' (imm_post S) M ms' model' ->
      realizes_cfg ASEGSN cfg (mkCfg ms' model') T) ->
  realizes_cfg ASEGSN cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (Hwx : LiaFast.U) => LiaFast.u0).
  intros S M E ms model T Hck Hd Hk.
  unfold imm_chk in Hck. unfold imm_post in Hk.
  set (fs := s_facts S) in *. set (d := rget (s_regs S) (rkey (xr 10))) in *. set (s := rget (s_regs S) (rkey (xr 11))) in *.
  set (nl := rget (s_regs S) (rkey (xr 12))) in *.
  destruct (s_resv S) eqn:Hrv; try discriminate.
  destruct (find_win rk_wz fs (s_rgs S) d nl O) as [j0|] eqn:Hf0; [|discriminate].
  destruct (find_win rk_rd fs (s_rgs S) s nl O) as [j1|] eqn:Hf1; [|discriminate].
  apply andb_prop in Hck as [Hck Hnl]. apply andb_prop in Hck as [Hck Hnl1]. apply andb_prop in Hck as [Hpc0 Hj01].
  apply Z.eqb_eq in Hpc0. apply Z.leb_le in Hnl. apply Z.leb_le in Hnl1. apply negb_true_iff, Nat.eqb_neq in Hj01.
  (* [comment removed for export] *)
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh0 Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  set (H := Hof E M model) in *.
  destruct (sden_0 _ _ _ _ Hsd) as (Hpc & Hsvc & Hrsv & HR & HG & HD & HF & Hfrm).
  rewrite Hrv in Hrsv. cbn [rsv_ok] in Hrsv.
  cbn [restrict ms_pc_val ms_svc_pending ms_resv ms_regs] in Hpc, Hsvc, Hrsv, HR.
  destruct (find_win_spec _ _ _ _ _ _ _ Hf0) as (Rd & Hj0 & _ & Hk0 & Hw0). rewrite Nat.sub_0_r in Hj0.
  destruct (find_win_spec _ _ _ _ _ _ _ Hf1) as (Rs & Hj1 & _ & Hk1 & Hw1). rewrite Nat.sub_0_r in Hj1.
  pose proof (irange_sound E fs nl HF) as Rn. fold (uE E nl) in Rn.
  assert (HN : uE E nl <= 2 ^ 40) by lia.
  assert (HN1 : 1 <= uE E nl) by lia.
  destruct (win_ok_sound E fs d nl Rd HF Hw0 HN) as (W1 & W2 & W3 & W4 & W5).
  destruct (win_ok_sound E fs s nl Rs HF Hw1 HN) as (V1 & V2 & V3 & V4 & V5).
  pose proof (uE_range E nl) as UN. pose proof (uE_range E d) as UD. pose proof (uE_range E s) as US.
  set (D := uE E d) in *. set (Sx := uE E s) in *. set (N := uE E nl) in *.
  set (AD := uE E (rg_base Rd)) in *. set (AS := uE E (rg_base Rs)) in *.
  rewrite Forall_nth' in HG.
  pose proof (HG j0 Rd Hj0) as HRd. pose proof (HG j1 Rs Hj1) as HRs.
  destruct HRd as (Hdsz & Hdfl & Hdpts & _). destruct HRs as (Hssz & Hsfl & Hspts & _).
  fold AD in Hdpts. fold AS in Hspts.
  (* [comment removed for export] *)
  assert (H10 : getr (ms_regs ms) 10%bv = Z_to_bv 64 D).
  { replace (10%bv : reg) with (xr 10) by (apply bv_eq; reflexivity). rewrite (HR (xr 10)). fold d. unfold D, uE. symmetry. apply u64_of. }
  assert (H11 : getr (ms_regs ms) 11%bv = Z_to_bv 64 Sx).
  { replace (11%bv : reg) with (xr 11) by (apply bv_eq; reflexivity). rewrite (HR (xr 11)). fold s. unfold Sx, uE. symmetry. apply u64_of. }
  assert (H12 : getr (ms_regs ms) 12%bv = Z_to_bv 64 N).
  { replace (12%bv : reg) with (xr 12) by (apply bv_eq; reflexivity). rewrite (HR (xr 12)). fold nl. unfold N, uE. symmetry. apply u64_of. }
  set (mm := mrestrict H (ms_mem ms)).
  (* [comment removed for export] *)
  assert (Hpts_s : forall i, 0 <= i < rsz E Rs -> rd1 ASEGSN mm (Z_to_bv 64 (AS + i)) <> None).
  { intros i Hi. specialize (Hspts i Hi). unfold rk_rd in Hk1.
    destruct (rg_kind Rs); try discriminate; [exact (proj1 Hspts) | exact (proj1 (proj1 Hspts)) | exact (proj1 (proj1 Hspts)) | exact Hspts]. }
  assert (Hsrc : OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_ims.AXG_imm.rdable mm Sx N).
  { intros i Hi. pose proof (Hpts_s (Sx - AS + i) ltac:(lia)) as X. replace (AS + (Sx - AS + i)) with (Sx + i) in X by lia.
    unfold rd1 in X. destruct (match mm (Z_to_bv 64 (Sx + i)) with Some b => Some b | None => seg_rom ASEGSN (Z_to_bv 64 (Sx + i)) end) as [b|] eqn:Eb; [|congruence].
    exists (bv_unsigned b). pose proof (bv_unsigned_in_range 8 b) as Rb. change (bv_modulus 8) with 256 in Rb. split; [lia|].
    unfold wa. cbn [rdn]. rewrite Eb. rewrite N_to_le_bytes_1_small. rewrite u_small64 by (unfold two64; lia).
    rewrite Z_to_bv_bv_unsigned. reflexivity. }
  (* [comment removed for export] *)
  assert (Hpt_d : forall i, 0 <= i < rsz E Rd -> rd1 ASEGSN mm (Z_to_bv 64 (AD + i)) <> None /\ wview ASEGSN mm (Z_to_bv 64 (AD + i)) <> None).
  { intros i Hi. specialize (Hdpts i Hi). unfold rk_wz in Hk0. destruct (rg_kind Rd); try discriminate; [exact Hdpts | exact (proj1 Hdpts)]. }
  assert (Hdst : AXG_np.wr mm D N).
  { intros dd k Hdd Hkk. unfold wa. apply store_ok_from; [lia | unfold two64; lia|].
    intros i Hi. replace (D + dd + i) with (AD + (D - AD + dd + i)) by lia. apply Hpt_d. lia. }
  assert (Hdisj : D + N <= Sx \/ Sx + N <= D).
  { pose proof (rgs_disj_nth E (s_rgs S) j0 j1 Rd Rs HD Hj01 Hj0 Hj1) as X. unfold rg_disj in X. fold (uE E (rg_base Rd)) (uE E (rg_base Rs)) in X.
    fold AD AS in X. lia. }
  destruct (@OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_ims.AXG_imm.imm_contract (mkFP (ms_fregs ms) (ms_fcsr ms)) (ms_rom ms) (ms_regs ms) mm D Sx N H10 H11 H12
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hdisj Hsrc Hdst) as (regs' & mem' & Hms & Hkeep & Hfr & Hext).
  assert (Hmsr : restrict H ms = @mkst (mkFP (ms_fregs ms) (ms_fcsr ms)) (ms_regs ms) (wa 0x733dc) mm (ms_rom ms)).
  { destruct ms as [rg fr pcv sv rv fc mem rom]. cbn [ms_pc_val ms_svc_pending ms_resv] in Hsvc, Hrsv, Hpc. subst sv rv.
    cbn [ms_pc_val] in Hpc. rewrite Hpc0 in Hpc. unfold IMM_PC in Hpc. subst pcv.
    unfold restrict, mkst, mm, wa. cbn. first [reflexivity | (f_equal; apply bv_eq; reflexivity)]. }
  apply (den_run_post_all_m ASEGSN cfg LIMIT model0 mem0 Hwx E S M ms model T regs' IMM_RET [] IMM_HAVS j0 Rd mem' Hd Hrv Hj0 Hk0).
  - fold H. rewrite Hmsr. apply fx_isteps_of_msteps. exact Hms.
  - intros w Hw. fold AD in Hw. pose proof (bv_unsigned_in_range 64 w) as Rw. change (bv_modulus 64) with (2^64) in Rw.
    assert (Ew : w = wa (bv_unsigned w)) by (symmetry; apply u64_of). rewrite Ew. fold mm. apply (Hfr (bv_unsigned w) Rw). lia.
  - intros i Hi. specialize (Hpt_d i Hi). fold AD. destruct Hpt_d as [P1 P2].
    split; [exact (mm_or_rd1_s _ _ _ _ (Hext _) P1) | exact (mm_or_wview_s _ _ _ _ (Hext _) P2)].
  - apply Forall_nil.
  - unfold IMM_HAVS. repeat constructor; intros Hc; apply (f_equal bv_unsigned) in Hc; vm_compute in Hc; discriminate.
  - intros rr Es Eh.
    assert (Hex : exists k, 0 <= k < 32 /\ rr = Z_to_bv 5 k).
    { exists (bv_unsigned rr). split; [pose proof (bv_unsigned_in_range _ rr) as X; change (bv_modulus 5) with 32 in X; lia|].
      symmetry; apply Z_to_bv_bv_unsigned. }
    destruct Hex as (k & Hk32 & ->).
    assert (Hc : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31) by lia.
    destruct Hc as [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | -> ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ].
    all: first
      [ (vm_compute in Eh; discriminate Eh)
      | (replace (Z_to_bv 5 0) with (0%bv : reg) by (apply bv_eq; reflexivity); rewrite !getr_zero; reflexivity)
      | (lazymatch goal with |- getr _ (Z_to_bv 5 ?kz) = _ => let n := eval vm_compute in (Z.to_nat kz) in
           exact (Hkeep n ltac:(unfold OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_ims.AXG_imm.KIMM; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In]; tauto ])) end) ].
  - intros E' ms' model' Ha' Hd' _. exact (Hk E' ms' model' Ha' Hd').
Qed.
End Node.
(* [comment removed for export] *)
End AsanImmS.

From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcEntry.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcMALp.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanQcsNode.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanQcsNode.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanQcsNode.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChEnt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChEnt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require FxBDec.

Module AsanImsZ.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec SeqExec CatExec CatSim.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require StepTac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require MemSplit RefMemcpyLib ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.SeqExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.CatExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.CatSim OSSVerify.Proofs.fast_float.from_chars.lib.Common.StepTac.Hoare OSSVerify.Proofs.fast_float.from_chars.lib.Common.MemSplit OSSVerify.Proofs.fast_float.from_chars.lib.Common.RefMemcpyLib OSSVerify.Proofs.fast_float.from_chars.lib.Common.ShapeSet OSSVerify.Proofs.fast_float.from_chars.lib.Common.RealizesCfg OSSVerify.Proofs.fast_float.from_chars.lib.Common.AsanAcct OSSVerify.Proofs.fast_float.from_chars.lib.Common.PlacementCount OSSVerify.Proofs.fast_float.from_chars.lib.Common.AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxLoop FxPlan FxFrame FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxDrv.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.FxAcct OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChLib.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChSep.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChEnt FxChStart FxChWv.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChSeg OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChSep OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChNode OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChEnt OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChStart OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChWv.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require FxQNode FxMchr FxMNode FxRunPost FxRunPostM FxSNodes AsanCpS.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxQChk OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxQNode OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxMchr OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxMNode OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxRunPost OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxRunPostM OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxSNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanCpS.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_np.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_ims.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_ims.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Abbreviation ASEGSN := AsanUbsan.M.loaded_segments.

(* [comment removed for export] *)
Section RunFZ.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.
Hypothesis Hwx : wx_segs_nowrap segs.

#[using="Hwx"] Theorem den_run_post_fz : forall E S M ms model T (regs' : bvmap 5 word) (pc' : Z) (sets : list (reg * lin)) (havs : list reg)
    (j0 : nat) (R0 : region) (lo hi : Z) (mem' : word -> option byte),
  DEN segs LIMIT model0 mem0 E S M ms model -> s_resv S = RNone ->
  nth_error (s_rgs S) j0 = Some R0 -> rk_wz (rg_kind R0) = true -> 0 <= lo -> lo <= hi -> hi <= rsz E R0 ->
  isteps segs (restrict (Hof E M model) ms)
    (@mkst (mkFP (ms_fregs ms) (ms_fcsr ms)) regs' (Z_to_bv 64 pc') mem' (ms_rom ms)) ->
  (forall w : word, ~ (uE E (rg_base R0) + lo <= bv_unsigned w < uE E (rg_base R0) + hi) -> mem' w = mrestrict (Hof E M model) (ms_mem ms) w) ->
  (forall i, lo <= i < hi -> rd1 segs mem' (Z_to_bv 64 (uE E (rg_base R0) + i)) <> None /\ wview segs mem' (Z_to_bv 64 (uE E (rg_base R0) + i)) <> None) ->
  (forall i, lo <= i < hi -> rd1 segs mem' (Z_to_bv 64 (uE E (rg_base R0) + i)) = Some (Z_to_bv 8 0)) ->
  Forall (fun p => fst p <> 0%bv /\ lwf (s_next S) (snd p) = true /\ getr regs' (fst p) = lden E (snd p)) sets ->
  Forall (fun r => r <> 0%bv) havs ->
  (forall r, existsb (fun p => bv_eqb (fst p) r) sets = false -> existsb (fun h => bv_eqb h r) havs = false ->
     getr regs' r = getr (ms_regs ms) r) ->
  (forall E' ms' model', agree (s_next S) E E' -> DEN segs LIMIT model0 mem0 E' (run_post_fw S pc' sets havs j0 lo hi) M ms' model' ->
     realizes_cfg segs cfg (mkCfg ms' model') T) ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (Hwx : LiaFast.U) => LiaFast.u0).
  intros E S M ms model T regs' pc' sets havs j0 R0 lo hi mem' Hd Hrv Hj0 Hk0 Hlo Hlh Hhi Hst Hfr Hwr Hzz Hsets Hnz Ho Hk.
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  set (H := Hof E M model) in *.
  destruct (sden_0 _ _ _ _ Hsd) as (Hpc & Hsvc & Hrsv & HR & HG & HD & HF & Hfrm).
  rewrite Hrv in Hrsv. cbn [rsv_ok] in Hrsv.
  cbn [restrict ms_pc_val ms_svc_pending ms_resv ms_regs] in Hpc, Hsvc, Hrsv, HR.
  set (n := s_next S) in *.
  set (E1 := hav_val E regs' havs n).
  assert (Ha1 : agree n E E1) by apply hav_val_agree.
  set (S1 := bump S (pos_add n (length havs))).
  assert (Hnx : (s_next S <= s_next S1)%positive) by (unfold S1, bump; cbn [s_next]; apply pos_add_le).
  assert (HdS1 : DEN segs LIMIT model0 mem0 E1 S1 M ms model)
    by (apply den_bump; [exact (den_agree segs LIMIT model0 mem0 E E1 S M ms model Hd Ha1) | apply pos_add_le]).
  assert (HH1 : Hof E1 M model = H) by (unfold Hof, H; rewrite (allowA_agree (s_next S) E E1 M Hwf Ha1); reflexivity).
  set (R0' := RG (rg_base R0) (rg_size R0) (rg_kind R0) (havoc_range (rg_cont R0) lo hi)).
  assert (Hpw : run_post_fw S pc' sets havs j0 lo hi = SST pc' (hav_regs (set_regs (s_regs S) sets) havs n) (upd_nth (s_rgs S) j0 R0')
                   (s_facts S) (pos_add n (length havs)) (s_resv S)) by (unfold run_post_fw; rewrite Hj0; reflexivity).
  set (msr' := @mkst (mkFP (ms_fregs ms) (ms_fcsr ms)) regs' (Z_to_bv 64 pc') mem' (ms_rom ms)).
  assert (Hpost : sden segs E1 (run_post_fw S pc' sets havs j0 lo hi) msr').
  { rewrite Hpw. intros E' Ha'.
    assert (HaE : agree n E E') by exact (agree_trans _ E E1 E' Ha1 (agree_mono _ _ E1 E' (pos_add_le (length havs) n) Ha')).
    destruct (Hsd E' HaE) as (Hpc' & Hsvc' & Hrsv' & HR' & HG' & HD' & HF' & Hfrm').
    cbn [restrict ms_regs ms_mem ms_fcsr ms_resv] in HR', HG', Hfrm', Hrsv'.
    assert (HbE : lden E' (rg_base R0) = lden E (rg_base R0)).
    { unfold bases_wf in Hbw. rewrite forallb_forall in Hbw. destruct (andb_prop _ _ (Hbw R0 (nth_error_In _ _ Hj0))) as [B1 _].
      exact (lden_agree_wf n E E' _ B1 HaE). }
    assert (HsE : rsz E' R0 = rsz E R0).
    { unfold bases_wf in Hbw. rewrite forallb_forall in Hbw. destruct (andb_prop _ _ (Hbw R0 (nth_error_In _ _ Hj0))) as [_ B2].
      unfold rsz. rewrite (lden_agree_wf n E E' _ B2 HaE). reflexivity. }
    unfold sden0. cbn [s_pc s_regs s_rgs s_facts s_resv msr' mkst ms_pc_val ms_svc_pending ms_resv ms_regs ms_mem ms_fcsr fp_csr].
    split; [reflexivity|]. split; [reflexivity|]. split; [rewrite Hrv; reflexivity|]. split.
    - apply (regs_ok_ext E' _ (upd_havs (upd_sets (ms_regs ms) sets regs') havs regs')).
      + apply regs_ok_hav'; [| exact Hnz |].
        * apply regs_ok_set'; [exact HR'|]. rewrite Forall_forall in Hsets |- *. intros p Hp.
          destruct (Hsets p Hp) as (Hp0 & Hpw' & Hpv). split; [exact Hp0|]. rewrite Hpv. symmetry. exact (lden_agree_wf n E E' _ Hpw' HaE).
        * intros i Hi. rewrite <- (hav_val_at havs E regs' n i Hi). symmetry. apply Ha'. cbn [s_next]. apply pos_add_lt. exact Hi.
      + intros r. rewrite upd_havs_get, upd_sets_get.
        destruct (existsb (fun h => bv_eqb h r) havs) eqn:Eh; [reflexivity|].
        destruct (existsb (fun p => bv_eqb (fst p) r) sets) eqn:Es; [reflexivity|].
        symmetry. exact (Ho r Es Eh).
    - split; [|split; [|split; [exact HF' | exact Hfrm']]].
      + (* [comment removed for export] *)
        apply Forall_nth'. intros j R HRj. rewrite Forall_nth' in HG'.
        destruct (Nat.eq_dec j j0) as [->|Hne].
        * rewrite (nth_upd_same (s_rgs S) j0 R0' R0 Hj0) in HRj. injection HRj as <-.
          destruct (HG' j0 R0 Hj0) as (Hsz & Hflat & Hall & Hcont).
          assert (Hrsz : rsz E' R0' = rsz E R0) by (unfold R0', rsz; cbn [rg_size]; unfold rsz in HsE; exact HsE).
          assert (Hbase : lden E' (rg_base R0') = lden E (rg_base R0)) by (unfold R0'; cbn [rg_base]; exact HbE).
          assert (HkR' : rg_kind R0' = rg_kind R0) by reflexivity.
          assert (Hcont' : rg_cont R0' = havoc_range (rg_cont R0) lo hi) by reflexivity.
          unfold rg_ok. rewrite Hrsz, Hbase, HkR', Hcont'. rewrite HbE, HsE in *. fold (uE E (rg_base R0)) in *.
          split; [exact Hsz|]. split; [exact Hflat|]. split.
          -- intros i Hi. specialize (Hall i Hi).
             assert (Hout : ~ (lo <= i < hi) -> mem' (Z_to_bv 64 (uE E (rg_base R0) + i)) = mrestrict H (ms_mem ms) (Z_to_bv 64 (uE E (rg_base R0) + i))).
             { intros Hn. apply Hfr. pose proof (uE_range E (rg_base R0)). rewrite u_small64 by (unfold two64 in *; lia). lia. }
             unfold rk_wz in Hk0. destruct (rg_kind R0) eqn:HKK; try discriminate.
             ++ (* [comment removed for export] *)
                destruct (Z_lt_le_dec i lo) as [Hl|Hl]; [|destruct (Z_lt_le_dec i hi) as [Hh2|Hh2]].
                ** unfold rd1, wview in *. rewrite Hout by lia. exact Hall.
                ** exact (Hwr i ltac:(lia)).
                ** unfold rd1, wview in *. rewrite Hout by lia. exact Hall.
             ++ (* [comment removed for export] *)
                destruct (Z_lt_le_dec i lo) as [Hl|Hl]; [|destruct (Z_lt_le_dec i hi) as [Hh2|Hh2]].
                ** assert (Htg : tget (okey i) (havoc_range (rg_cont R0) lo hi) = tget (okey i) (rg_cont R0)).
                   { unfold havoc_range. rewrite tget_tfilter. destruct (tget (okey i) (rg_cont R0)); [|reflexivity].
                     unfold okey. rewrite Z2Pos.id by lia. replace (i + 1 - 1) with i by ring.
                     replace (Z.leb lo i) with false by (symmetry; apply Z.leb_gt; lia). reflexivity. }
                   rewrite Htg. unfold rd1, wview in *. rewrite Hout by lia. exact Hall.
                ** split; [exact (Hwr i ltac:(lia))|]. intros _. exact (Hzz i ltac:(lia)).
                ** assert (Htg : tget (okey i) (havoc_range (rg_cont R0) lo hi) = tget (okey i) (rg_cont R0)).
                   { unfold havoc_range. rewrite tget_tfilter. destruct (tget (okey i) (rg_cont R0)); [|reflexivity].
                     unfold okey. rewrite Z2Pos.id by lia. replace (i + 1 - 1) with i by ring.
                     replace (Z.ltb i hi) with false by (symmetry; apply Z.ltb_ge; lia). rewrite andb_false_r. reflexivity. }
                   rewrite Htg. unfold rd1, wview in *. rewrite Hout by lia. exact Hall.
          -- intros p v Hp. unfold havoc_range in Hp. rewrite tget_tfilter in Hp.
             destruct (tget p (rg_cont R0)) as [x|] eqn:Hx; [|discriminate].
             destruct (negb (Z.leb lo (Zpos p - 1) && Z.ltb (Zpos p - 1) hi)) eqn:Hn; [|discriminate]. injection Hp as <-.
             destruct (Hcont p x Hx) as [Hp1 Hp2]. rewrite ?HbE, ?HsE in Hp1, Hp2. fold (uE E (rg_base R0)) in Hp2. split; [exact Hp1|].
             apply negb_true_iff in Hn. apply andb_false_iff in Hn.
             unfold rd1 in *. rewrite Hfr; [exact Hp2|]. pose proof (Pos2Z.is_pos p). pose proof (uE_range E (rg_base R0)).
             rewrite u_small64 by (unfold two64 in *; lia).
             destruct Hn as [Hn|Hn]; [apply Z.leb_gt in Hn | apply Z.ltb_ge in Hn]; lia.
        * rewrite (nth_upd_other (s_rgs S) j0 j R0' ltac:(lia)) in HRj.
          apply (rg_ok_frame segs E' (mrestrict H (ms_mem ms)) mem' R (HG' j R HRj)).
          intros x Hx. apply Hfr.
          pose proof (rgs_disj_nth E' (s_rgs S) j j0 R R0 HD' Hne HRj Hj0) as Hdis. unfold rg_disj in Hdis.
          rewrite HbE, HsE in Hdis. fold (uE E (rg_base R0)) in Hdis. unfold uE in *. lia.
      + apply (rgs_disj_upd E' (s_rgs S) j0 R0' R0 Hj0 eq_refl eq_refl HD'). }
  assert (Hmsr : restrict H ms = @mkst (mkFP (ms_fregs ms) (ms_fcsr ms)) (ms_regs ms) (Z_to_bv 64 (s_pc S)) (mrestrict H (ms_mem ms)) (ms_rom ms)).
  { destruct ms as [rg fr pcv sv rv fc mem rom]. cbn [ms_pc_val ms_svc_pending ms_resv] in Hsvc, Hrsv, Hpc. subst sv rv.
    cbn [ms_pc_val] in Hpc. subst pcv. reflexivity. }
  apply (den_isteps segs cfg LIMIT model0 mem0 Hwx E1 S1 M ms model T (run_post_fw S pc' sets havs j0 lo hi) msr' E1 HdS1).
  - rewrite HH1. exact Hst.
  - exact Hpost.
  - apply agree_refl.
  - rewrite Hpw. unfold S1, bump. cbn [s_next]. apply Pos.le_refl.
  - intros y Hy. rewrite HH1. unfold msr', mkst. cbn [ms_mem]. apply Hfr.
    unfold outside in Hy. rewrite Forall_forall in Hy. specialize (Hy R0 (nth_error_In _ _ Hj0)).
    cbn [S1 bump s_rgs] in Hy.
    unfold bases_wf in Hbw. rewrite forallb_forall in Hbw. destruct (andb_prop _ _ (Hbw R0 (nth_error_In _ _ Hj0))) as [B1 B2].
    assert (HbE1 : lden E1 (rg_base R0) = lden E (rg_base R0)) by exact (lden_agree_wf n E E1 _ B1 Ha1).
    assert (HsE1 : rsz E1 R0 = rsz E R0) by (unfold rsz; rewrite (lden_agree_wf n E E1 _ B2 Ha1); reflexivity).
    rewrite HbE1, HsE1 in Hy. unfold uE. lia.
  - rewrite Hpw. cbn [s_rgs S1 bump]. exact (shape_upd (s_rgs S) j0 R0' R0 Hj0 eq_refl eq_refl).
  - intros E2 ms2 model2 HD2 Ha2. apply (Hk E2 ms2 model2); [|exact HD2].
    exact (agree_trans _ E E1 E2 Ha1 (agree_mono _ _ E1 E2 Hnx Ha2)).
Qed.
End RunFZ.

(* [comment removed for export] *)
Definition IMS_PC : Z := 0x73434.
Definition IMS_RET : Z := 0x73490.
Definition IMS_HAVS : list reg := List.map xr [11; 12; 13].

(* [comment removed for export] *)
Fixpoint find_zwin (rgs : list region) (d : lin) (n : Z) (j : nat) : option (nat * Z) :=
  match rgs with
  | [] => None
  | R :: rs => match rk_wz (rg_kind R), is_const (rg_size R), lin_off d (rg_base R) with
               | true, Some sz, Some o => if Z.leb (o + n) sz then Some (j, o) else find_zwin rs d n (Datatypes.S j)
               | _, _, _ => find_zwin rs d n (Datatypes.S j)
               end
  end.
Lemma find_zwin_spec : forall rgs d n j j0 o, find_zwin rgs d n j = Some (j0, o) ->
  exists R sz, nth_error rgs (j0 - j) = Some R /\ (j <= j0)%nat /\ rk_wz (rg_kind R) = true /\ is_const (rg_size R) = Some sz /\
    lin_off d (rg_base R) = Some o /\ o + n <= sz.
Proof.
  induction rgs as [|R rs IH]; intros d n j j0 o H; cbn [find_zwin] in H; [discriminate|].
  assert (Hrec : find_zwin rs d n (Datatypes.S j) = Some (j0, o) ->
    exists R1 sz, nth_error (R :: rs) (j0 - j) = Some R1 /\ (j <= j0)%nat /\ rk_wz (rg_kind R1) = true /\ is_const (rg_size R1) = Some sz /\
      lin_off d (rg_base R1) = Some o /\ o + n <= sz).
  { intros H'. destruct (IH d n (Datatypes.S j) j0 o H') as (R' & sz & Hn & Hj & X). exists R', sz.
    replace (j0 - j)%nat with (Datatypes.S (j0 - Datatypes.S j)) by lia. split; [exact Hn|]. split; [lia | exact X]. }
  destruct (rk_wz (rg_kind R)) eqn:Hk; [|exact (Hrec H)].
  destruct (is_const (rg_size R)) as [sz|] eqn:Hs; [|exact (Hrec H)].
  destruct (lin_off d (rg_base R)) as [o0|] eqn:Ho; [|exact (Hrec H)].
  destruct (Z.leb (o0 + n) sz) eqn:Hc; [|exact (Hrec H)].
  injection H as <- <-. apply Z.leb_le in Hc. exists R, sz. rewrite Nat.sub_diag. split; [reflexivity|]. split; [lia|].
  split; [exact Hk|]. split; [exact Hs|]. split; [exact Ho | exact Hc].
Qed.

Definition ims_chk (S : sst) (M : smodel) : bool :=
  let fs := s_facts S in
  let d := rget (s_regs S) (rkey (xr 10)) in let c := rget (s_regs S) (rkey (xr 11)) in let nl := rget (s_regs S) (rkey (xr 12)) in
  match s_resv S, is_const c, is_const nl with
  | RNone, Some 0, Some n =>
      match find_zwin (s_rgs S) d n O with
      | Some _ => (Z.eqb (s_pc S) IMS_PC && Z.leb 1 n && Z.leb n (2 ^ 40) && Z.leb (snd (irange fs d) + n) (2 ^ 62))%bool
      | None => false
      end
  | _, _, _ => false
  end.
Definition ims_post (S : sst) : sst :=
  match is_const (rget (s_regs S) (rkey (xr 12))) with
  | Some n => match find_zwin (s_rgs S) (rget (s_regs S) (rkey (xr 10))) n O with
              | Some (j0, o) => run_post_fw S IMS_RET [] IMS_HAVS j0 o (o + n)
              | None => S
              end
  | None => S
  end.

Section Node.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.
Hypothesis Hwx : wx_segs_nowrap ASEGSN.

#[using="Hwx"] Theorem den_ims : forall S M E ms model T,
  ims_chk S M = true -> DEN ASEGSN LIMIT model0 mem0 E S M ms model ->
  (forall E' ms' model', agree (s_next S) E E' -> DEN ASEGSN LIMIT model0 mem0 E' (ims_post S) M ms' model' ->
      realizes_cfg ASEGSN cfg (mkCfg ms' model') T) ->
  realizes_cfg ASEGSN cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (Hwx : LiaFast.U) => LiaFast.u0).
  intros S M E ms model T Hck Hd Hk.
  unfold ims_chk in Hck. unfold ims_post in Hk.
  set (fs := s_facts S) in *. set (d := rget (s_regs S) (rkey (xr 10))) in *. set (c := rget (s_regs S) (rkey (xr 11))) in *.
  set (nl := rget (s_regs S) (rkey (xr 12))) in *.
  destruct (s_resv S) eqn:Hrv; try discriminate.
  destruct (is_const c) as [cz|] eqn:Hcz; [|discriminate]. destruct cz; try discriminate.
  destruct (is_const nl) as [n|] eqn:Hnz; [|discriminate].
  destruct (find_zwin (s_rgs S) d n O) as [[j0 o]|] eqn:Hf0; [|discriminate].
  apply andb_prop in Hck as [Hck Hd62]. apply andb_prop in Hck as [Hck Hn40]. apply andb_prop in Hck as [Hpc0 Hn1].
  apply Z.eqb_eq in Hpc0. apply Z.leb_le in Hd62. apply Z.leb_le in Hn40. apply Z.leb_le in Hn1.
  (* [comment removed for export] *)
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh0 Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  set (H := Hof E M model) in *.
  destruct (sden_0 _ _ _ _ Hsd) as (Hpc & Hsvc & Hrsv & HR & HG & HD & HF & Hfrm).
  rewrite Hrv in Hrsv. cbn [rsv_ok] in Hrsv.
  cbn [restrict ms_pc_val ms_svc_pending ms_resv ms_regs] in Hpc, Hsvc, Hrsv, HR.
  destruct (find_zwin_spec _ _ _ _ _ _ Hf0) as (Rd & sz & Hj0 & _ & Hk0 & Hsz & Hoff & Hon). rewrite Nat.sub_0_r in Hj0.
  pose proof (irange_sound E fs d HF) as Rdd. fold (uE E d) in Rdd.
  pose proof (is_const_u E nl n Hnz) as HN. pose proof (is_const_u E c 0 Hcz) as HC. pose proof (is_const_u E (rg_size Rd) sz Hsz) as HSZ.
  destruct (lin_off_sound E d (rg_base Rd) o Hoff) as (Hoo & Horng).
  set (D := uE E d) in *. set (AD := uE E (rg_base Rd)) in *.
  rewrite Forall_nth' in HG.
  pose proof (HG j0 Rd Hj0) as HRd. destruct HRd as (Hdsz & Hdfl & Hdpts & _). fold AD in Hdpts, Hdfl. unfold rsz in Hdsz, Hdfl, Hdpts. rewrite HSZ in Hdsz, Hdfl, Hdpts.
  pose proof (uE_range E d) as UD. pose proof (uE_range E (rg_base Rd)) as UA. change (0 <= D < two64) in UD. change (0 <= AD < two64) in UA.
  (* [comment removed for export] *)
  assert (HDo : D = AD + o).
  { assert (Y : o = (D - AD) mod two64).
    { pose proof (f_equal bv_unsigned Hoo) as Y. rewrite lden_lsub, bv_sub_unsigned in Y. rewrite Z_to_bv_unsigned in Y.
      unfold bv_wrap in Y. change (bv_modulus 64) with two64 in Y. rewrite (Z.mod_small o) in Y by exact Horng.
      symmetry. exact Y. }
    destruct (Z_lt_le_dec D AD) as [Hlt|Hge].
    - exfalso. rewrite <- (Z_mod_plus_full (D - AD) 1 two64) in Y.
      assert (Hdfl' : AD + sz <= two64) by exact Hdfl.
      clearbody D AD. clear - Y UD UA Hlt Hdfl' Hon Hn1 Horng. unfold two64 in *.
      rewrite Z.mod_small in Y by lia. lia.
    - clearbody D AD. clear - Y UD UA Hge. unfold two64 in *. rewrite Z.mod_small in Y by lia. lia. }
  (* [comment removed for export] *)
  assert (H10 : getr (ms_regs ms) 10%bv = Z_to_bv 64 D).
  { replace (10%bv : reg) with (xr 10) by (apply bv_eq; reflexivity). rewrite (HR (xr 10)). fold d. unfold D, uE. symmetry. apply u64_of. }
  assert (H11 : getr (ms_regs ms) 11%bv = Z_to_bv 64 0).
  { replace (11%bv : reg) with (xr 11) by (apply bv_eq; reflexivity). rewrite (HR (xr 11)). fold c. rewrite <- HC. symmetry. apply u64_of. }
  assert (H12 : getr (ms_regs ms) 12%bv = Z_to_bv 64 n).
  { replace (12%bv : reg) with (xr 12) by (apply bv_eq; reflexivity). rewrite (HR (xr 12)). fold nl. rewrite <- HN. symmetry. apply u64_of. }
  set (mm := mrestrict H (ms_mem ms)).
  (* [comment removed for export] *)
  assert (Hpt_d : forall i, 0 <= i < sz -> rd1 ASEGSN mm (Z_to_bv 64 (AD + i)) <> None /\ wview ASEGSN mm (Z_to_bv 64 (AD + i)) <> None).
  { intros i Hi. specialize (Hdpts i Hi). unfold rk_wz in Hk0. destruct (rg_kind Rd); try discriminate; [exact Hdpts | exact (proj1 Hdpts)]. }
  assert (Hdst : AXG_np.wr mm D n).
  { intros dd k Hdd Hkk. unfold wa. apply store_ok_from; [lia | unfold two64 in *; lia|].
    intros i Hi. replace (D + dd + i) with (AD + (o + dd + i)) by lia. apply Hpt_d. lia. }
  destruct (@AXG_ims.ims_contract (mkFP (ms_fregs ms) (ms_fcsr ms)) (ms_rom ms) (ms_regs ms) mm D n H10 H11 H12
              ltac:(lia) ltac:(lia) ltac:(lia) Hdst) as (regs' & mem' & Hms & Hkeep & _ & _ & _ & Hfr & Hext & Hzz).
  assert (Hmsr : restrict H ms = @mkst (mkFP (ms_fregs ms) (ms_fcsr ms)) (ms_regs ms) (wa 0x73434) mm (ms_rom ms)).
  { destruct ms as [rg fr pcv sv rv fc mem rom]. cbn [ms_pc_val ms_svc_pending ms_resv] in Hsvc, Hrsv, Hpc. subst sv rv.
    cbn [ms_pc_val] in Hpc. rewrite Hpc0 in Hpc. unfold IMS_PC in Hpc. subst pcv.
    unfold restrict, mkst, mm, wa. cbn. first [reflexivity | (f_equal; apply bv_eq; reflexivity)]. }
  apply (den_run_post_fz ASEGSN cfg LIMIT model0 mem0 Hwx E S M ms model T regs' IMS_RET [] IMS_HAVS j0 Rd o (o + n) mem' Hd Hrv Hj0 Hk0).
  - lia.
  - lia.
  - unfold rsz. rewrite HSZ. lia.
  - fold H. rewrite Hmsr. apply fx_isteps_of_msteps. exact Hms.
  - intros w Hw. fold AD in Hw. pose proof (bv_unsigned_in_range 64 w) as Rw. change (bv_modulus 64) with (2^64) in Rw.
    assert (Ew : w = wa (bv_unsigned w)) by (symmetry; apply u64_of). rewrite Ew. fold mm. apply (Hfr (bv_unsigned w) Rw). lia.
  - intros i Hi. specialize (Hpt_d i ltac:(lia)). fold AD. destruct Hpt_d as [P1 P2].
    split; [exact (mm_or_rd1_s _ _ _ _ (Hext _) P1) | exact (mm_or_wview_s _ _ _ _ (Hext _) P2)].
  - intros i Hi. fold AD. unfold rd1. replace (AD + i) with (D + (i - o)) by lia. fold (wa (D + (i - o))).
    rewrite (Hzz (i - o) ltac:(lia)). reflexivity.
  - apply Forall_nil.
  - unfold IMS_HAVS. repeat constructor; intros Hc; apply (f_equal bv_unsigned) in Hc; vm_compute in Hc; discriminate.
  - intros rr Es Eh.
    assert (Hex : exists k, 0 <= k < 32 /\ rr = Z_to_bv 5 k).
    { exists (bv_unsigned rr). split; [pose proof (bv_unsigned_in_range _ rr) as X; change (bv_modulus 5) with 32 in X; lia|].
      symmetry; apply Z_to_bv_bv_unsigned. }
    destruct Hex as (k & Hk32 & ->).
    assert (Hc : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31) by lia.
    destruct Hc as [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | -> ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ].
    all: first
      [ (vm_compute in Eh; discriminate Eh)
      | (replace (Z_to_bv 5 0) with (0%bv : reg) by (apply bv_eq; reflexivity); rewrite !getr_zero; reflexivity)
      | (lazymatch goal with |- getr _ (Z_to_bv 5 ?kz) = _ => let n := eval vm_compute in (Z.to_nat kz) in
           exact (Hkeep n ltac:(unfold AXG_ims.KIMS; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In]; tauto ])) end) ].
  - intros E' ms' model' Ha' Hd'. exact (Hk E' ms' model' Ha' Hd').
Qed.
End Node.
(* [comment removed for export] *)
End AsanImsZ.

From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require FxNormWI.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require FxNormWI.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require FxNormWI.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxQChk OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxQNode OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxQRNodeS OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanQSites OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanPNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanCpS OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxBDec OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxBDec.FxVConst OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxBandNode OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBNodes.AsanOvlNode OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBNodes.AsanImmS OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcEntry.AsanMergeS OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcMALp.FxRgNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanQcsNode.AsanRpNode OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanQcsNode.AsanRpNodeS OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanQcsNode.FxWrapOut OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChEnt.FxPlaceE OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChEnt.FxPlaceW OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxBDec.FxVLin OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBNodes.AsanImsZ OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxNormWI.FxNormW OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxNormWI.FxSplitW32 OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxNormWI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Inductive bnode : Type := BTrack (i : nat) (k0 : positive) | BRecont (i : nat) (k0 : positive) (c : Z) | BRecontA (i : nat) (k0 : positive) | BCut (i : nat) (o1 o2 : Z) | BCps
  | BDec (v : positive) (k : Z) | BPerm (ix : list nat) | BBand (j : nat) | BSplit2 (i : nat) (o : Z) | BOvl | BImm | BMergeS (i : nat) | BSplitReg (i : nat) (rp rm : Z) | BFront (j : nat) | BConc (v : positive)
  | BTrack1 (i : nat) | BMergeTZ (i : nat) | BSplitZ (i : nat) (m : lin)
  | BRpS      (* [comment removed for export] *)
  | BSplitW (i : nat) (m : lin)    (* [comment removed for export] *)
  | BDrop (i : nat)                (* [comment removed for export] *)
  | BPlaceE (j : nat) (os : list lin)    (* [comment removed for export] *)
  | BEqSize (i : nat) (l : lin) (k : Z)  (* [comment removed for export] *)
  | BPlaceW (j : nat)                   (* [comment removed for export] *)
  | BQrS (j : nat)                      (* [comment removed for export] *)
  | BIms                               (* [comment removed for export] *)
  | BNormW (a : Z)                      (* [comment removed for export] *)
  | BSplitW32 (i : nat) (o : Z)         (* [comment removed for export] *)
  | BPsrMov (src dst : positive)        (* [comment removed for export] *)
  | BIxfP (c : Z) (ka kb : positive)    (* [comment removed for export] *)
  | BPsrLin (dst : positive) (c1 : Z) (k1 : positive) (c2 : Z) (k2 : positive) (c0 : Z)
                                        (* [comment removed for export] *)
  | BIxfK (k : positive)                (* [comment removed for export] *)
  | BIrV (v : positive)                 (* [comment removed for export] *)
  | BNormWI (a : Z) (lit : bool)        (* [comment removed for export] *)
  | BIrL (l : lin).                     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition BS_ALLOC : bsite := BS 0x3fd4c (Z_to_bv 5 22) (Z_to_bv 5 9) (Z_to_bv 5 10) 3 48.
Definition BSITES : list bsite := [BS_ALLOC].
Lemma BSITES_ok : Forall (bsite_ok ASEGSN) BSITES.
Proof.
  apply Forall_cons; [|apply Forall_nil]. unfold bsite_ok, BS_ALLOC; cbn [bs_pc bs_rd bs_ra bs_rm bs_k bs_j].
  split; [intros Hc; apply (f_equal bv_unsigned) in Hc; vm_compute in Hc; discriminate|].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [unfold two64; lia|].
  unfold qins. eexists. split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|]. vm_compute.
  repeat match goal with |- @eq (bv _) _ _ => apply bv_eq; vm_compute; reflexivity | |- _ = _ => f_equal end.
Qed.

(* [comment removed for export] *)
Fixpoint bk_val (t : tree bval) (k0 : positive) (j : nat) : option Z :=
  match j with
  | O => Some 0
  | Datatypes.S j' => match tget (Pos.of_nat (Pos.to_nat k0 + j')) t, bk_val t k0 j' with
                      | Some (BK b), Some v => Some (v + b * 2 ^ (8 * Z.of_nat j'))
                      | _, _ => None
                      end
  end.
Definition recontA_post (S : sst) (i : nat) (k0 : positive) : option sst :=
  match nth_error (s_rgs S) i with
  | Some R => match bk_val (rg_cont R) k0 8 with Some c => recont_post S i k0 c | None => None end
  | None => None
  end.

(* [comment removed for export] *)
Definition sub_rg (R : region) (o z : Z) (k : rkind) : region :=
  RG (laddc (rg_base R) o) (lconst z) k
     (put_list TEmpty (List.map (fun '(p, v) => (Z.to_pos (Zpos p - o), v))
        (List.filter (fun '(p, _) => (Z.leb o (Zpos p - 1) && Z.ltb (Zpos p - 1) (o + z))%bool) (FxCall.telems (rg_cont R))))).
Definition cut_post (S : sst) (i : nat) (o1 o2 : Z) : option sst :=
  match nth_error (s_rgs S) i with
  | Some R => match is_const (rg_size R) with
              | Some z => let R23 := sub_rg R o1 (z - o1) (rg_kind R) in
                  match steps_rgs (s_next S) (s_facts S) (s_rgs S)
                          [RSplit i (sub_rg R 0 o1 (rg_kind R)) R23 o1; RSplit (Datatypes.S i) (sub_rg R23 0 (o2 - o1) RW) (sub_rg R23 (o2 - o1) (z - o2) (rg_kind R23)) (o2 - o1)] with
                  | Some l => Some (with_rgs S l)
                  | None => None
                  end
              | None => None
              end
  | None => None
  end.

Definition split2_post (S : sst) (i : nat) (o : Z) : option sst :=
  match nth_error (s_rgs S) i with
  | Some R => match is_const (rg_size R) with
              | Some z => match steps_rgs (s_next S) (s_facts S) (s_rgs S) [RSplit i (sub_rg R 0 o (rg_kind R)) (sub_rg R o (z - o) (rg_kind R)) o] with
                          | Some l => Some (with_rgs S l)
                          | None => None
                          end
              | None => None
              end
  | None => None
  end.

(* [comment removed for export] *)
Definition merge_s_post (S : sst) (i : nat) : option sst :=
  match nth_error (s_rgs S) i, nth_error (s_rgs S) (Datatypes.S i) with
  | Some R1, Some R2 =>
      let fs := s_facts S in
      let b1r := irange fs (rg_base R1) in let s1r := irange fs (rg_size R1) in let s2r := irange fs (rg_size R2) in
      if (rkind_eqb (rg_kind R1) RW && rkind_eqb (rg_kind R2) RW && tempty_b (rg_cont R1) && tempty_b (rg_cont R2) &&
          lin_eqb (ladd (rg_base R1) (rg_size R1)) (rg_base R2) && Z.leb 1 (fst s1r) && Z.leb 1 (fst s2r) &&
          Z.ltb (snd b1r + snd s1r + snd s2r) two64 &&
          (if (Z.leb SH_HI (fst b1r) || (Z.leb (snd b1r + snd s1r + snd s2r) SH_LO || Z.leb (snd (irange fs (ladd (rg_base R1) (ladd (rg_size R1) (rg_size R2))))) SH_LO) || (Z.leb SH_LO (fst b1r) && (Z.leb (snd b1r + snd s1r + snd s2r) SH_HI || Z.leb (snd (irange fs (ladd (rg_base R1) (ladd (rg_size R1) (rg_size R2))))) SH_HI)))%bool then true
           else wrap_out fs (s_rgs S) (rg_base R1) (ladd (rg_size R1) (rg_size R2)) (snd s1r + snd s2r)))%bool
      then Some (with_rgs S (firstn i (s_rgs S) ++ RG (rg_base R1) (ladd (rg_size R1) (rg_size R2)) RW TEmpty :: skipn (Datatypes.S (Datatypes.S i)) (s_rgs S)))
      else None
  | _, _ => None
  end.
(* [comment removed for export] *)
Definition merge_tz_post (S : sst) (i : nat) : option sst :=
  match nth_error (s_rgs S) i, nth_error (s_rgs S) (Datatypes.S i) with
  | Some R1, Some R2 =>
      match is_const (rg_size R1) with
      | Some c =>
          let fs := s_facts S in
          let b1r := irange fs (rg_base R1) in let s2r := irange fs (rg_size R2) in
          if (rkind_eqb (rg_kind R1) RZ && rkind_eqb (rg_kind R2) RZ && tempty_b (rg_cont R2) && Z.leb 1 c &&
              lin_eqb (laddc (rg_base R1) c) (rg_base R2) && Z.leb 1 (fst s2r) &&
              Z.leb SH_LO (fst b1r) &&
              (* [comment removed for export] *)
              (if Z.ltb (snd b1r + c + snd s2r) SH_HI then true
               else (Z.ltb (snd b1r + c + snd s2r) two64 && Z.leb (snd (irange fs (ladd (rg_base R1) (laddc (rg_size R2) c)))) SH_HI)%bool))%bool
          then Some (with_rgs S (firstn i (s_rgs S) ++ RG (rg_base R1) (laddc (rg_size R2) c) RZ (rg_cont R1) :: skipn (Datatypes.S (Datatypes.S i)) (s_rgs S)))
          else None
      | None => None
      end
  | _, _ => None
  end.
(* [comment removed for export] *)
Definition splitz_post (S : sst) (i : nat) (m : lin) : option sst :=
  match nth_error (s_rgs S) i with
  | Some R =>
      let fs := s_facts S in let t := lsub (rg_size R) m in
      if (rkind_eqb (rg_kind R) RZ && tempty_b (rg_cont R) && lwf (s_next S) m && lwf (s_next S) t &&
          Z.leb 1 (fst (irange fs m)) && Z.leb 1 (fst (irange fs t)) && Z.ltb (snd (irange fs m) + snd (irange fs t)) (2 ^ 62) &&
          Z.ltb (snd (irange fs (rg_base R)) + snd (irange fs (rg_size R))) two64)%bool
      then Some (with_rgs S (firstn i (s_rgs S) ++ RG (rg_base R) m RZ TEmpty :: RG (ladd (rg_base R) m) t RZ TEmpty :: skipn (Datatypes.S i) (s_rgs S)))
      else None
  | None => None
  end.
Definition splitw_post (S : sst) (i : nat) (m : lin) : option sst :=
  match nth_error (s_rgs S) i with
  | Some R =>
      let fs := s_facts S in let t := lsub (rg_size R) m in
      if (rkind_eqb (rg_kind R) RW && tempty_b (rg_cont R) && lwf (s_next S) m && lwf (s_next S) t &&
          Z.leb 1 (fst (irange fs m)) && Z.leb 1 (fst (irange fs t)) && Z.ltb (snd (irange fs m) + snd (irange fs t)) (2 ^ 62) &&
          Z.ltb (snd (irange fs (rg_base R)) + snd (irange fs (rg_size R))) two64)%bool
      then Some (with_rgs S (firstn i (s_rgs S) ++ RG (rg_base R) m RW TEmpty :: RG (ladd (rg_base R) m) t RW TEmpty :: skipn (Datatypes.S i) (s_rgs S)))
      else None
  | None => None
  end.
Definition splitreg_post (S : sst) (i : nat) (rp rm : Z) : option sst :=
  split_post_s S i (rget (s_regs S) (rkey (Z_to_bv 5 rp))) (rget (s_regs S) (rkey (Z_to_bv 5 rm))).

Definition perm_post (S : sst) (ix : list nat) : option sst :=
  if perm_ix_ok (List.length (s_rgs S)) ix then Some (with_rgs S (List.map (fun k => nth k (s_rgs S) (RG lc0 lc0 RW TEmpty)) ix)) else None.

Definition front_ix (n j : nat) : list nat := j :: List.seq 0 j ++ List.seq (Datatypes.S j) (n - Datatypes.S j).

(* [comment removed for export] *)
Fixpoint find_cw (rgs : list region) (a : Z) (i : nat) : option (nat * Z) :=
  match rgs with
  | [] => None
  | R :: r => match is_const (rg_base R), is_const (rg_size R) with
              | Some b, Some z => if (Z.leb b a && Z.leb (a + 8) (b + z))%bool then Some (i, a - b) else find_cw r a (Datatypes.S i)
              | _, _ => find_cw r a (Datatypes.S i)
              end
  end.
Definition normw_post (S : sst) (a : Z) : option sst :=
  match find_cw (s_rgs S) a O with
  | Some (i, o) => normw_at S i (okey o)
  | None => None
  end.
Definition normwi_post (img : tree Z) (lit : bool) (S : sst) (a : Z) : option sst :=
  match find_cw (s_rgs S) a O with
  | Some (i, o) => normwi_at img lit S i (okey o)
  | None => None
  end.

Section B.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable img : tree Z.
Hypothesis Hwx : wx_segs_nowrap ASEGSN.
Hypothesis Himg : img_ok ASEGSN img.

Definition ppostB (p : bnode) (S : sst) (M : smodel) : option sst :=
  match p with
  | BTrack i k0 => rz_track_post S i k0
  | BRecont i k0 c => recont_post S i k0 c
  | BRecontA i k0 => recontA_post S i k0
  | BCut i o1 o2 => cut_post S i o1 o2
  | BCps => if cps_chk img S M then Some (cps_post S) else None
  | BDec v k => dec_post S M v k
  | BPerm ix => perm_post S ix
  | BBand j => match nth_error BSITES j with Some s => band_post s S | None => None end
  | BSplit2 i o => split2_post S i o
  | BOvl => if ovl_chk OS_MEMCPY S then Some (ovl_post OS_MEMCPY S) else None
  | BImm => if imm_chk S M then Some (imm_post S) else None
  | BMergeS i => merge_s_post S i
  | BSplitReg i rp rm => splitreg_post S i rp rm
  | BFront j => perm_post S (front_ix (List.length (s_rgs S)) j)
  | BConc v => vconst_post S M v
  | BTrack1 i => match track1_post S i with   (* [comment removed for export] *)
                 | Some S1 => Some (match vconst_post S1 M (s_next S) with Some S2 => S2 | None => S1 end)
                 | None => None
                 end
  | BMergeTZ i => merge_tz_post S i
  | BSplitZ i m => splitz_post S i m
  | BRpS => if rps_chk img S M then Some (rp_post S) else None
  | BSplitW i m => splitw_post S i m
  | BDrop i => match steps_rgs (s_next S) (s_facts S) (s_rgs S) [RDrop i] with Some l => Some (with_rgs S l) | None => None end
  | BPlaceE j os => place_post S M j os
  | BEqSize i l k => match nth_error (s_rgs S) i with
                     | Some R => match l_t (rg_size R) with [(v, c)] => if Z.eqb c 1 then vlin_post S M v l k else None | _ => None end
                     | None => None
                     end
  | BPlaceW j => placew_post S M j
  | BQrS j => match nth_error QSITES_P j with
              | Some q => if qcrs_chk img q S M then Some (qc_post q S) else None
              | None => None
              end
  | BIms => if ims_chk S M then Some (ims_post S) else None
  | BNormW a => normw_post S a
  | BSplitW32 i o => splitw32_at S i (okey o)
  | BPsrMov src dst => if Pos.ltb 32 dst then Some (with_reg S dst (rget (s_regs S) src)) else None
  | BIxfP c ka kb => let l := lsub (lscale c (rget (s_regs S) ka)) (rget (s_regs S) kb) in
                     Some (add_fact S (FRange l (fst (irange_x (s_facts S) l)) (snd (irange_x (s_facts S) l))))
  | BPsrLin dst c1 k1 c2 k2 c0 =>
      if Pos.ltb 32 dst then Some (with_reg S dst (laddc (ladd (lscale c1 (rget (s_regs S) k1)) (lscale c2 (rget (s_regs S) k2))) c0)) else None
  | BIxfK k => let l := rget (s_regs S) k in Some (add_fact S (FRange l (fst (irange_x (s_facts S) l)) (snd (irange_x (s_facts S) l))))
  | BIrV v => Some (add_fact S (FRange (lvar v) (fst (irange (s_facts S) (lvar v))) (snd (irange (s_facts S) (lvar v)))))
  | BNormWI a lit => normwi_post img lit S a
  | BIrL l => Some (add_fact S (FRange l (fst (irange_x (s_facts S) l)) (snd (irange_x (s_facts S) l))))
  end.

#[using="Hwx Himg"] Theorem pnodeB_ok : forall p, pnode_ok ASEGSN cfg LIMIT ppostB p.
Proof. LiaFast.lf_pins (fun (Hwx Himg : LiaFast.U) => LiaFast.u0).
  intros p S M S' Hp model0 mem0 E ms model T Hd Hk. destruct p as [i k0|i k0 c|i k0|i o1 o2| |v k|ix|j|i o| | |i|i rp rm|j|v|i|i|i m| |i m|i|j os|i l k|j|j| |a|i o|src dst|c ka kb|dst c1 k1 c2 k2 c0|k|v|a lit|l]; cbn [ppostB] in Hp.
  - exact (Hk E ms model (agree_refl _ _) (den_rz_track ASEGSN LIMIT mem0 model0 E S M ms model i k0 S' Hd Hp)).
  - exact (Hk E ms model (agree_refl _ _) (den_recont ASEGSN LIMIT mem0 model0 E S M ms model i k0 c S' Hd Hp)).
  - unfold recontA_post in Hp. destruct (nth_error (s_rgs S) i) as [R|]; [|discriminate]. destruct (bk_val (rg_cont R) k0 8) as [c|]; [|discriminate].
    exact (Hk E ms model (agree_refl _ _) (den_recont ASEGSN LIMIT mem0 model0 E S M ms model i k0 c S' Hd Hp)).
  - unfold cut_post in Hp. destruct (nth_error (s_rgs S) i) as [R|]; [|discriminate]. destruct (is_const (rg_size R)) as [z|]; [|discriminate].
    match type of Hp with (match ?x with _ => _ end) = _ => destruct x as [l|] eqn:Hst; [|discriminate] end.
    injection Hp as <-. exact (Hk E ms model (agree_refl _ _) (den_steps ASEGSN LIMIT model0 mem0 _ E S M ms model l Hd Hst)).
  - destruct (cps_chk img S M) eqn:Hc; [|discriminate]. injection Hp as <-.
    exact (den_cps cfg LIMIT model0 mem0 img Hwx S M E ms model T Hc Hd Hk).
  - exact (den_dec ASEGSN cfg LIMIT model0 mem0 S M v k S' Hp E ms model T Hd Hk).
  - unfold perm_post in Hp. destruct (perm_ix_ok (List.length (s_rgs S)) ix) eqn:Hix; [|discriminate]. injection Hp as <-.
    exact (Hk E ms model (agree_refl _ _)
             (den_perm ASEGSN LIMIT model0 mem0 E S M ms model _ Hd (perm_ix_sound (s_rgs S) (RG lc0 lc0 RW TEmpty) ix Hix))).
  - destruct (nth_error BSITES j) as [s|] eqn:Hj; [|discriminate].
    pose proof BSITES_ok as Hss. rewrite Forall_forall in Hss.
    exact (den_band ASEGSN cfg LIMIT model0 mem0 Hwx s S S' M E ms model T (Hss s (nth_error_In _ _ Hj)) Hp Hd Hk).
  - unfold split2_post in Hp. destruct (nth_error (s_rgs S) i) as [R|]; [|discriminate]. destruct (is_const (rg_size R)) as [z|]; [|discriminate].
    match type of Hp with (match ?x with _ => _ end) = _ => destruct x as [l|] eqn:Hst; [|discriminate] end.
    injection Hp as <-. exact (Hk E ms model (agree_refl _ _) (den_steps ASEGSN LIMIT model0 mem0 _ E S M ms model l Hd Hst)).
  - destruct (ovl_chk OS_MEMCPY S) eqn:Hc; [|discriminate]. injection Hp as <-.
    exact (den_ovl cfg LIMIT model0 mem0 Hwx OS_MEMCPY S M E ms model T OS_MEMCPY_ok Hc Hd Hk).
  - destruct (imm_chk S M) eqn:Hc; [|discriminate]. injection Hp as <-.
    exact (den_imm cfg LIMIT model0 mem0 Hwx S M E ms model T Hc Hd Hk).
  - (* [comment removed for export] *)
    unfold merge_s_post in Hp. destruct (nth_error (s_rgs S) i) as [R1|] eqn:Hi1; [|discriminate].
    destruct (nth_error (s_rgs S) (Datatypes.S i)) as [R2|] eqn:Hi2; [|discriminate]. cbv zeta in Hp.
    match type of Hp with ((if ?c then _ else _) = _) => destruct c eqn:Hb; [|discriminate] end. injection Hp as <-.
    repeat match type of Hb with ((_ && _)%bool = true) => apply andb_prop in Hb as [Hb ?Hx] end.
    rename Hb into Hk1. match goal with H : (if _ then true else _) = true |- _ => rename H into Hsh0 end.
    repeat match goal with H : Z.leb _ _ = true |- _ => apply Z.leb_le in H | H : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in H
                        | H : lin_eqb _ _ = true |- _ => apply lin_eqb_eq in H | H : rkind_eqb _ _ = true |- _ => apply rkind_eqb_eq in H
                        | H : tempty_b _ = true |- _ => apply tempty_b_eq in H end.
    destruct R1 as [b1 s1 k1 c1]. destruct R2 as [b2 s2 k2 c2]. cbn [rg_base rg_size rg_kind rg_cont] in *. subst k1 k2 c1 c2.
    assert (Hadj : ladd b1 s1 = b2) by assumption.
    pose proof (nth_split2 _ i _ _ Hi1 Hi2) as HS.
    assert (HFa : forall E', agree (s_next S) E E' -> Forall (fact_ok E') (s_facts S)).
    { intros E' Ha. destruct (dn_sden _ _ _ _ _ _ _ _ _ Hd E' Ha) as (_ & _ & _ & _ & _ & _ & X & _). exact X. }
    assert (Hgeo : forall E', agree (s_next S) E E' -> 0 < uE E' s1 /\ 0 < uE E' s2 /\ uE E' s1 + uE E' s2 < two64 /\ uE E' b2 = uE E' b1 + uE E' s1).
    { intros E' Ha. pose proof (irange_sound E' _ b1 (HFa E' Ha)) as I1. pose proof (irange_sound E' _ s1 (HFa E' Ha)) as I2.
      pose proof (irange_sound E' _ s2 (HFa E' Ha)) as I3. fold (uE E' b1) in I1. fold (uE E' s1) in I2. fold (uE E' s2) in I3.
      pose proof (bv_unsigned_in_range _ (lden E' b1)) as U1. fold (uE E' b1) in U1.
      split; [lia|]. split; [lia|]. split; [lia|]. rewrite <- Hadj. unfold uE. rewrite lden_ladd, bv_add_unsigned.
      unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64. apply Z.mod_small. unfold uE in *. lia. }
    apply (Hk E ms model (agree_refl _ _)).
    pose proof (irange_sound E _ b1 (HFa E (agree_refl _ _))) as I1. pose proof (irange_sound E _ s1 (HFa E (agree_refl _ _))) as I2.
    pose proof (irange_sound E _ s2 (HFa E (agree_refl _ _))) as I3. fold (uE E b1) in I1. fold (uE E s1) in I2. fold (uE E s2) in I3.
    match type of Hsh0 with ((if ?c then true else _) = true) => destruct c eqn:Hsh end;
      [|rename Hsh0 into Hwr;
        apply (den_merge_s ASEGSN LIMIT model0 mem0 E S M ms model (firstn i (s_rgs S)) b1 b2 s1 s2 (skipn (Datatypes.S (Datatypes.S i)) (s_rgs S)) Hd HS Hgeo);
        intros w Hw; destruct (Hgeo E (agree_refl _ _)) as (G1 & G2 & G3 & _);
        assert (Hl : uE E (ladd s1 s2) = uE E s1 + uE E s2)
          by (unfold uE; rewrite lden_ladd, bv_add_unsigned; unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 64) with two64; apply Z.mod_small; unfold uE in *; lia);
        destruct (wrap_out_spec E _ _ b1 (ladd s1 s2) _ (HFa E (agree_refl _ _)) Hwr ltac:(rewrite Hl; lia) ltac:(rewrite Hl; lia)) as [Hlo|Hhi];
        unfold in_shadow; apply andb_false_iff; [left; apply Z.leb_gt; rewrite Hl in Hlo; lia | right; apply Z.ltb_ge; lia]].
    apply orb_prop in Hsh as [Hsh|Hsh].
    + apply (den_merge_s ASEGSN LIMIT model0 mem0 E S M ms model (firstn i (s_rgs S)) b1 b2 s1 s2 (skipn (Datatypes.S (Datatypes.S i)) (s_rgs S)) Hd HS Hgeo).
      intros w Hw. unfold in_shadow. apply andb_false_iff.
      apply orb_prop in Hsh as [Hsh|Hsh]; [apply Z.leb_le in Hsh; right; apply Z.ltb_ge; lia|].
      apply orb_prop in Hsh as [Hsh|Hsh]; apply Z.leb_le in Hsh; [left; apply Z.leb_gt; lia|].
      pose proof (irange_sound E _ (ladd b1 (ladd s1 s2)) (HFa E (agree_refl _ _))) as I4. destruct (Hgeo E (agree_refl _ _)) as (G1 & G2 & G3 & _).
      pose proof (uE_range E b1) as RB1.
      assert (Hl4 : bv_unsigned (lden E (ladd b1 (ladd s1 s2))) = uE E b1 + (uE E s1 + uE E s2)).
      { rewrite !lden_ladd, !bv_add_unsigned. fold (uE E b1) (uE E s1) (uE E s2). unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64.
        rewrite (Z.mod_small (uE E s1 + uE E s2)) by (unfold uE in *; lia). apply Z.mod_small. unfold uE in *. lia. }
      rewrite Hl4 in I4. left. apply Z.leb_gt. lia.
    + apply andb_prop in Hsh as [Hs1 Hs2]. apply Z.leb_le in Hs1.
      apply (den_merge_sh ASEGSN LIMIT model0 mem0 E S M ms model (firstn i (s_rgs S)) b1 b2 s1 s2 (skipn (Datatypes.S (Datatypes.S i)) (s_rgs S)) Hd HS Hgeo).
      intros w Hw. unfold in_shadow. apply andb_true_iff. split; [apply Z.leb_le; lia | apply Z.ltb_lt].
      apply orb_prop in Hs2 as [Hs2|Hs2]; apply Z.leb_le in Hs2; [lia|].
      pose proof (irange_sound E _ (ladd b1 (ladd s1 s2)) (HFa E (agree_refl _ _))) as I4. destruct (Hgeo E (agree_refl _ _)) as (G1 & G2 & G3 & _).
      pose proof (uE_range E b1) as RB1.
      assert (Hl4 : bv_unsigned (lden E (ladd b1 (ladd s1 s2))) = uE E b1 + (uE E s1 + uE E s2)).
      { rewrite !lden_ladd, !bv_add_unsigned. fold (uE E b1) (uE E s1) (uE E s2). unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64.
        rewrite (Z.mod_small (uE E s1 + uE E s2)) by (unfold uE in *; lia). apply Z.mod_small. unfold uE in *. lia. }
      rewrite Hl4 in I4. lia.
  - (* [comment removed for export] *)
    exact (Hk E ms model (agree_refl _ _) (den_split_s ASEGSN LIMIT mem0 model0 E S M ms model i _ _ S' Hd Hp)).
  - (* [comment removed for export] *)
    unfold perm_post in Hp. destruct (perm_ix_ok (List.length (s_rgs S)) (front_ix (List.length (s_rgs S)) j)) eqn:Hix; [|discriminate]. injection Hp as <-.
    exact (Hk E ms model (agree_refl _ _)
             (den_perm ASEGSN LIMIT model0 mem0 E S M ms model _ Hd (perm_ix_sound (s_rgs S) (RG lc0 lc0 RW TEmpty) _ Hix))).
  - (* [comment removed for export] *)
    exact (Hk E ms model (agree_refl _ _) (den_vconst ASEGSN LIMIT model0 mem0 S M v S' E ms model Hp Hd)).
  - (* [comment removed for export] *)
    destruct (track1_post S i) as [S1|] eqn:Ht; [|discriminate]. injection Hp as <-.
    destruct (den_track1 ASEGSN LIMIT model0 mem0 S M i S1 E ms model Ht Hd) as (E' & Ha & Hd').
    destruct (vconst_post S1 M (s_next S)) as [S2|] eqn:Hv;
      [exact (Hk E' ms model Ha (den_vconst ASEGSN LIMIT model0 mem0 S1 M _ S2 E' ms model Hv Hd')) | exact (Hk E' ms model Ha Hd')].
  - (* [comment removed for export] *)
    unfold merge_tz_post in Hp. destruct (nth_error (s_rgs S) i) as [R1|] eqn:Hi1; [|discriminate].
    destruct (nth_error (s_rgs S) (Datatypes.S i)) as [R2|] eqn:Hi2; [|discriminate].
    destruct (is_const (rg_size R1)) as [c|] eqn:Hc1; [|discriminate]. cbv zeta in Hp.
    match type of Hp with ((if ?c then _ else _) = _) => destruct c eqn:Hb; [|discriminate] end. injection Hp as <-.
    repeat match type of Hb with ((_ && _)%bool = true) => apply andb_prop in Hb as [Hb ?Hx] end.
    repeat match goal with H : Z.leb _ _ = true |- _ => apply Z.leb_le in H | H : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in H
                        | H : lin_eqb _ _ = true |- _ => apply lin_eqb_eq in H | H : rkind_eqb _ _ = true |- _ => apply rkind_eqb_eq in H
                        | H : tempty_b _ = true |- _ => apply tempty_b_eq in H end.
    destruct R1 as [b1 s1 k1 c1]. destruct R2 as [b2 s2 k2 c2]. cbn [rg_base rg_size rg_kind rg_cont] in *. subst k1 k2 c2.
    assert (Hadj : laddc b1 c = b2) by assumption.
    pose proof (nth_split2 _ i _ _ Hi1 Hi2) as HS.
    assert (HFa : forall E', agree (s_next S) E E' -> Forall (fact_ok E') (s_facts S)).
    { intros E' Ha. destruct (dn_sden _ _ _ _ _ _ _ _ _ Hd E' Ha) as (_ & _ & _ & _ & _ & _ & X & _). exact X. }
    assert (Hcr : 0 <= c < two64) by (destruct (is_const_sound E s1 c Hc1) as [_ X]; exact X).
    match goal with H : (if Z.ltb _ SH_HI then true else _) = true |- _ => rename H into Hend end.
    assert (Hsum : forall E', agree (s_next S) E E' -> uE E' b1 + c + uE E' s2 < two64 /\ uE E' b1 + c + uE E' s2 <= SH_HI).
    { intros E' Ha. pose proof (irange_sound E' _ b1 (HFa E' Ha)) as I1. pose proof (irange_sound E' _ s2 (HFa E' Ha)) as I3.
      fold (uE E' b1) in I1. fold (uE E' s2) in I3.
      pose proof (uE_range E' b1) as U1. pose proof (uE_range E' s2) as U3.
      destruct (Z.ltb (snd (irange (s_facts S) b1) + c + snd (irange (s_facts S) s2)) SH_HI) eqn:Hlt.
      - apply Z.ltb_lt in Hlt. unfold SH_HI, two64 in *. lia.
      - apply andb_prop in Hend as [Hw He]. apply Z.ltb_lt in Hw. apply Z.leb_le in He.
        pose proof (irange_sound E' _ (ladd b1 (laddc s2 c)) (HFa E' Ha)) as I4. fold (uE E' (ladd b1 (laddc s2 c))) in I4.
        assert (Hv1 : uE E' (laddc s2 c) = uE E' s2 + c) by (unfold uE; rewrite lden_laddc; fold (uE E' s2); apply u_small64; lia).
        assert (Hv2 : uE E' (ladd b1 (laddc s2 c)) = uE E' b1 + (uE E' s2 + c)).
        { unfold uE. rewrite lden_ladd, bv_add_unsigned. fold (uE E' b1) (uE E' (laddc s2 c)). rewrite Hv1. unfold bv_wrap, bv_modulus.
          change (2 ^ Z.of_N 64) with two64. apply Z.mod_small. unfold uE in *. lia. }
        split; [lia|]. rewrite Hv2 in I4. lia. }
    assert (Hgeo : forall E', agree (s_next S) E E' -> 0 < uE E' s2 /\ c + uE E' s2 < two64 /\ uE E' b2 = uE E' b1 + c).
    { intros E' Ha. pose proof (irange_sound E' _ b1 (HFa E' Ha)) as I1. pose proof (irange_sound E' _ s2 (HFa E' Ha)) as I3.
      fold (uE E' b1) in I1. fold (uE E' s2) in I3. destruct (Hsum E' Ha) as [Hs1 Hs2].
      pose proof (bv_unsigned_in_range _ (lden E' b1)) as U1. fold (uE E' b1) in U1. unfold bv_modulus in U1. change (2 ^ Z.of_N 64) with two64 in U1.
      split; [lia|]. split; [lia|]. rewrite <- Hadj. unfold uE. rewrite lden_laddc.
      apply u_small64. unfold uE in *. lia. }
    apply (Hk E ms model (agree_refl _ _)).
    apply (den_merge_tz ASEGSN LIMIT model0 mem0 E S M ms model (firstn i (s_rgs S)) b1 b2 s1 c s2 c1 (skipn (Datatypes.S (Datatypes.S i)) (s_rgs S)) Hd HS Hc1 ltac:(lia) Hgeo).
    intros w Hw. pose proof (irange_sound E _ b1 (HFa E (agree_refl _ _))) as I1. pose proof (irange_sound E _ s2 (HFa E (agree_refl _ _))) as I3.
    fold (uE E b1) in I1. fold (uE E s2) in I3. destruct (Hsum E (agree_refl _ _)) as [Hs1 Hs2].
    unfold in_shadow. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
  - (* [comment removed for export] *)
    unfold splitz_post in Hp. destruct (nth_error (s_rgs S) i) as [R|] eqn:Hi; [|discriminate]. cbv zeta in Hp.
    match type of Hp with ((if ?c then _ else _) = _) => destruct c eqn:Hb; [|discriminate] end. injection Hp as <-.
    repeat match type of Hb with ((_ && _)%bool = true) => apply andb_prop in Hb as [Hb ?Hx] end.
    repeat match goal with H : Z.leb _ _ = true |- _ => apply Z.leb_le in H | H : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in H
                        | H : rkind_eqb _ _ = true |- _ => apply rkind_eqb_eq in H | H : tempty_b _ = true |- _ => apply tempty_b_eq in H end.
    destruct R as [b z k c]. cbn [rg_base rg_size rg_kind rg_cont] in *. subst k c.
    pose proof (AcSteps.nth_split _ i _ Hi) as HS.
    assert (HFa : forall E', agree (s_next S) E E' -> Forall (fact_ok E') (s_facts S)).
    { intros E' Ha. destruct (dn_sden _ _ _ _ _ _ _ _ _ Hd E' Ha) as (_ & _ & _ & _ & _ & _ & X & _). exact X. }
    apply (Hk E ms model (agree_refl _ _)).
    match goal with Hwm : lwf _ m = true, Hwt : lwf _ (lsub z m) = true |- _ =>
      apply (den_split_zz ASEGSN LIMIT model0 mem0 E S M ms model (firstn i (s_rgs S)) b z m (lsub z m) (skipn (Datatypes.S i) (s_rgs S)) Hd HS Hwm Hwt) end.
    intros E' Ha. pose proof (irange_sound E' _ m (HFa E' Ha)) as I1. pose proof (irange_sound E' _ (lsub z m) (HFa E' Ha)) as I2.
    pose proof (irange_sound E' _ b (HFa E' Ha)) as I3. pose proof (irange_sound E' _ z (HFa E' Ha)) as I4.
    fold (uE E' m) in I1. fold (uE E' (lsub z m)) in I2. fold (uE E' b) in I3. fold (uE E' z) in I4.
    pose proof (uE_range E' z) as Rz. pose proof (uE_range E' m) as Rm.
    destruct (small_diff E' z m _ _ I2) as [[Hl He]|[Hl He]]; [|exfalso; unfold two64 in *; lia].
    split; [lia|]. split; [lia|]. split; [lia|]. lia.
  - (* [comment removed for export] *)
    destruct (rps_chk img S M) eqn:Hc; [|discriminate]. injection Hp as <-.
    exact (den_rps cfg LIMIT model0 mem0 img Hwx Himg S M E ms model T Hc Hd Hk).
  - (* [comment removed for export] *)
    unfold splitw_post in Hp. destruct (nth_error (s_rgs S) i) as [R|] eqn:Hi; [|discriminate]. cbv zeta in Hp.
    match type of Hp with ((if ?c then _ else _) = _) => destruct c eqn:Hb; [|discriminate] end. injection Hp as <-.
    repeat match type of Hb with ((_ && _)%bool = true) => apply andb_prop in Hb as [Hb ?Hx] end.
    repeat match goal with H : Z.leb _ _ = true |- _ => apply Z.leb_le in H | H : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in H
                        | H : rkind_eqb _ _ = true |- _ => apply rkind_eqb_eq in H | H : tempty_b _ = true |- _ => apply tempty_b_eq in H end.
    destruct R as [b z k c]. cbn [rg_base rg_size rg_kind rg_cont] in *. subst k c.
    pose proof (AcSteps.nth_split _ i _ Hi) as HS.
    assert (HFa : forall E', agree (s_next S) E E' -> Forall (fact_ok E') (s_facts S)).
    { intros E' Ha. destruct (dn_sden _ _ _ _ _ _ _ _ _ Hd E' Ha) as (_ & _ & _ & _ & _ & _ & X & _). exact X. }
    apply (Hk E ms model (agree_refl _ _)).
    match goal with Hwm : lwf _ m = true, Hwt : lwf _ (lsub z m) = true |- _ =>
      apply (den_split_ww ASEGSN LIMIT model0 mem0 E S M ms model (firstn i (s_rgs S)) b z m (lsub z m) (skipn (Datatypes.S i) (s_rgs S)) Hd HS Hwm Hwt) end.
    intros E' Ha. pose proof (irange_sound E' _ m (HFa E' Ha)) as I1. pose proof (irange_sound E' _ (lsub z m) (HFa E' Ha)) as I2.
    pose proof (irange_sound E' _ b (HFa E' Ha)) as I3. pose proof (irange_sound E' _ z (HFa E' Ha)) as I4.
    fold (uE E' m) in I1. fold (uE E' (lsub z m)) in I2. fold (uE E' b) in I3. fold (uE E' z) in I4.
    pose proof (uE_range E' z) as Rz. pose proof (uE_range E' m) as Rm.
    destruct (small_diff E' z m _ _ I2) as [[Hl He]|[Hl He]]; [|exfalso; unfold two64 in *; lia].
    split; [lia|]. split; [lia|]. split; [lia|]. lia.
  - (* [comment removed for export] *)
    match type of Hp with (match ?x with _ => _ end) = _ => destruct x as [l|] eqn:Hst; [|discriminate] end.
    injection Hp as <-. exact (Hk E ms model (agree_refl _ _) (den_steps ASEGSN LIMIT model0 mem0 _ E S M ms model l Hd Hst)).
  - (* [comment removed for export] *)
    exact (Hk E ms model (agree_refl _ _) (den_place ASEGSN LIMIT model0 mem0 E S M ms model j os S' Hd Hp)).
  - (* [comment removed for export] *)
    destruct (nth_error (s_rgs S) i) as [R|]; [|discriminate]. destruct (l_t (rg_size R)) as [|[v c] [|? ?]]; try discriminate.
    destruct (Z.eqb c 1); [|discriminate].
    exact (Hk E ms model (agree_refl _ _) (den_vlin ASEGSN LIMIT model0 mem0 S M v l k S' E ms model Hp Hd)).
  - (* [comment removed for export] *)
    exact (Hk E ms model (agree_refl _ _) (den_placew ASEGSN LIMIT model0 mem0 E S M ms model j S' Hd Hp)).
  - (* [comment removed for export] *)
    destruct (nth_error QSITES_P j) as [q|] eqn:Hq; [|discriminate].
    destruct (qcrs_chk img q S M) eqn:Hc; [|discriminate]. injection Hp as <-.
    pose proof QSITES_P_ok as Hqs. rewrite Forall_forall in Hqs.
    exact (den_qcrs ASEGSN cfg LIMIT model0 mem0 img Hwx Himg q S M E ms model T (Hqs q (nth_error_In _ _ Hq)) Hc Hd Hk).
  - (* [comment removed for export] *)
    destruct (ims_chk S M) eqn:Hc; [|discriminate]. injection Hp as <-.
    exact (den_ims cfg LIMIT model0 mem0 Hwx S M E ms model T Hc Hd Hk).
  - (* [comment removed for export] *)
    unfold normw_post in Hp. destruct (find_cw (s_rgs S) a O) as [[i o]|]; [|discriminate].
    exact (Hk E ms model (agree_refl _ _) (den_normw ASEGSN LIMIT mem0 model0 E S M ms model i (okey o) S' Hd Hp)).
  - (* [comment removed for export] *)
    exact (Hk E ms model (agree_refl _ _) (den_splitw32 ASEGSN LIMIT mem0 model0 E S M ms model i (okey o) S' Hd Hp)).
  - (* [comment removed for export] *)
    destruct (Pos.ltb 32 dst) eqn:Hk32; [|discriminate]. injection Hp as <-. apply Pos.ltb_lt in Hk32.
    exact (Hk E ms model (agree_refl _ _) (den_psr LIMIT model0 mem0 E S M ms model dst _ Hk32 Hd)).
  - (* [comment removed for export] *)
    injection Hp as <-. apply (Hk E ms model (agree_refl _ _)).
    apply (FxChain.den_addfact ASEGSN LIMIT model0 mem0); [exact Hd|]. intros E' Ha'.
    destruct (dn_sden _ _ _ _ _ _ _ _ _ Hd E' Ha') as (_ & _ & _ & _ & _ & _ & HF' & _).
    cbn [fact_ok]. rewrite irange_x_eq. exact (irange_x_ref_sound E' _ _ HF').
  - (* [comment removed for export] *)
    destruct (Pos.ltb 32 dst) eqn:Hk32; [|discriminate]. injection Hp as <-. apply Pos.ltb_lt in Hk32.
    exact (Hk E ms model (agree_refl _ _) (den_psr LIMIT model0 mem0 E S M ms model dst _ Hk32 Hd)).
  - (* [comment removed for export] *)
    injection Hp as <-. apply (Hk E ms model (agree_refl _ _)).
    apply (FxChain.den_addfact ASEGSN LIMIT model0 mem0); [exact Hd|]. intros E' Ha'.
    destruct (dn_sden _ _ _ _ _ _ _ _ _ Hd E' Ha') as (_ & _ & _ & _ & _ & _ & HF' & _).
    cbn [fact_ok]. rewrite irange_x_eq. exact (irange_x_ref_sound E' _ _ HF').
  - (* [comment removed for export] *)
    injection Hp as <-. apply (Hk E ms model (agree_refl _ _)).
    apply (FxChain.den_addfact ASEGSN LIMIT model0 mem0); [exact Hd|]. intros E' Ha'.
    destruct (dn_sden _ _ _ _ _ _ _ _ _ Hd E' Ha') as (_ & _ & _ & _ & _ & _ & HF' & _).
    cbn [fact_ok]. exact (irange_sound E' _ _ HF').
  - (* [comment removed for export] *)
    unfold normwi_post in Hp. destruct (find_cw (s_rgs S) a O) as [[i o]|]; [|discriminate].
    exact (Hk E ms model (agree_refl _ _) (den_normwi ASEGSN LIMIT mem0 img Himg lit model0 E S M ms model i (okey o) S' Hd Hp)).
  - (* [comment removed for export] *)
    injection Hp as <-. apply (Hk E ms model (agree_refl _ _)).
    apply (FxChain.den_addfact ASEGSN LIMIT model0 mem0); [exact Hd|]. intros E' Ha'.
    destruct (dn_sden _ _ _ _ _ _ _ _ _ Hd E' Ha') as (_ & _ & _ & _ & _ & _ & HF' & _).
    cbn [fact_ok]. rewrite irange_x_eq. exact (irange_x_ref_sound E' _ _ HF').
Qed.
End B.
(* [comment removed for export] *)
