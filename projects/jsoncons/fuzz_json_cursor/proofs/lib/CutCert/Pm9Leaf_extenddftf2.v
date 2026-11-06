(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3
  AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm9PlanKit Pm9L5DefsA FrmInv FpBridge Pm9FrmInv Pm9FpSites.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmHeapIfaceA PmLibDefsA PmLibSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutOpsD CutHeap CutAuto CutAutoD CutLib CutHeap2 CutL5 CutCertA CutHeapA CutL5A CutBridgeA CutRtA CutRtB CutPureA CutVF CutVFA Pm9CutKitD.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_extenddftf2_cboth_T Cut_extenddftf2_cboth.
Import ListNotations. Import AX2.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module Leaf_extenddftf2_cboth.
Module G := Cut_extenddftf2_cboth.
Module GT := Cut_extenddftf2_cboth_T.
Definition ENTRY : Z := 1261296.
Definition SCR : Z := 0.
Definition ENDS : list Z := [1261360; 1261600; 1261624; 1261688].
Definition INL : list (Z * (Z * list nat * option Z)) := [].
Definition IMG : option (Z * Z) := None.
Definition CALLEES : list (Z * (Z * option (Z * Z))) := [].
Definition GLO : Z := 1368064. Definition GHI : Z := 1368064.
Lemma chk : CVFA.vf_chkA G.CPS G.TAGS G.HDECL ENTRY SCR ENDS G.RETS INL IMG CALLEES [] GLO GHI = true. Proof. vmc_refl. Qed.
Lemma heap_ok : CHA.heap_chkA CVF.NF G.HDECL (CPA.NOB G.CPS) (CPA.NOF G.CPS) G.CPS G.TAGS = true. Proof. vmc_refl. Qed.
Lemma pure_ok : CH2.leaves_all G.CPS G.TAGS (CPA.pure_leaf_chk CVF.NF G.HDECL ENDS) = true. Proof. vmc_refl. Qed.
Lemma tagpc_ok : CH2.leaves_all G.CPS G.TAGS CVFA.tag_pc_chk = true. Proof. vmc_refl. Qed.
Lemma foot_ok : CC.cps_all G.CPS (fun _ c => CHA.foot_chk CVF.NF G.HDECL c [] []) = true. Proof. vmc_refl. Qed.
Lemma rets : forall pc, In pc ENDS -> CL.is_ret_at RSEGS pc.
Proof. intros pc H. cbn [ENDS In] in H. destruct H as [<-|H]; [CL.solve_is_ret|]. destruct H as [<-|H]; [CL.solve_is_ret|]. destruct H as [<-|H]; [CL.solve_is_ret|]. destruct H as [<-|H]; [CL.solve_is_ret|]. destruct H. Qed.
Lemma inl : forall e, In e INL -> CVF.inl_sem RSEGS e.
Proof. intros e H. cbn [INL In] in H.  destruct H. Qed.

Lemma lems : G.LEMS_OK. Proof. unfold G.LEMS_OK, CXD.LEMS_OK, G.LEMS. apply Forall_nil. Qed.
Section Final.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout. Variable ar : asan_run. Variable C : asan_statics_cells. Variable HI : asan_iface.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LAY : L5A.as0_layout L C.

Theorem ok : CVFA.vf_contractA L ar HI PMSA.fp_ok 1261292 SCR IMG.
Proof.
  pose proof (L5A.aly_segs L C LAY) as LS. pose proof (L5A.aly_img_lo L C LAY) as ILO. pose proof (L5A.aly_img_hi L C LAY) as IHI.
  assert (LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO) by (rewrite ILO, IHI; unfold BIGSHADOW_LO; lia).
  assert (LYR : forall a, hl_rt_ro L a -> hl_img_lo L <= a < hl_img_hi L) by (intros a Ha; rewrite ILO, IHI; exact (L5A.aly_ro_img L C LAY a Ha)).
  assert (LYB : segs_below_b (hl_segs L) (hl_img_hi L) = true) by (rewrite LS, IHI; exact L5A.segs_below).
  assert (LYN : wx_segs_nowrap (hl_segs L)) by (rewrite LS; exact L5A.wx_nowrap).
  assert (FPM : forall (fx fx' : FPState) R pc M R' pc' M',
            msteps (hl_segs L) (@mkst fx R (Z_to_bv 64 pc) M (seg_rom (hl_segs L))) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom (hl_segs L))) -> PMSA.fp_ok fx -> PMSA.fp_ok fx').
  { rewrite LS. intros fx fx' R pc M R' pc' M' H Hf. exact (Pm9FrmInv.msteps_fp_ok fx fx' R _ M _ R' _ M' _ H Hf). }
  assert (PL : forall i c, nth_error G.CPS i = Some c -> CC.plan_sound (hl_segs L) c) by (rewrite LS; exact (G.plans lems)).
  assert (RT : forall pc, In pc ENDS -> CL.is_ret_at (hl_segs L) pc) by (rewrite LS; exact rets).
  assert (IN : forall e, In e INL -> CVF.inl_sem (hl_segs L) e) by (rewrite LS; exact inl).
  assert (SC_OK : incl (@nil (Z * Z * Z)) (asc_cells C) /\ Forall (fun c : Z * Z * Z => 0 <= fst (fst c) /\ fst (fst c) + snd (fst c) <= hl_img_hi L /\ 0 <= snd (fst c) <= 8) (@nil (Z * Z * Z)))
    by (split; [intros x [] | apply Forall_nil]).
  assert (GOT_OK : asc_got_lo C <= GLO /\ GHI <= asc_got_hi C /\ 0 <= GLO /\ GHI <= hl_img_hi L)
    by (unfold GLO, GHI; rewrite (L5A.aly_got_lo L C LAY), (L5A.aly_got_hi L C LAY), IHI; lia).
  assert (IMG_OK : forall (rg : Z * Z) (a : Z), In rg (CH.hd_img G.HDECL) -> fst rg <= a < snd rg -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a).
  { intros rg a Hrg Ha. cbn [CH.hd_img G.HDECL GT.HDECL In] in Hrg. rewrite ILO, IHI.
    repeat (destruct Hrg as [<-|Hrg]; [cbn [fst snd] in Ha; split; [lia | intros Hs; pose proof (L5A.aly_static_lo L C LAY a Hs); lia]|]). destruct Hrg. }
  assert (CAL_OK : forall pc SCRc IMGc, In (pc, (SCRc, IMGc)) CALLEES -> CVFA.vf_contractA L ar HI PMSA.fp_ok pc SCRc IMGc).
  { intros pc SCRc IMGc H. cbn [CALLEES In] in H.  destruct H. }
  assert (SITE0 : FPB.inl_step (hl_segs L) 1261292 4 [11%nat]) by (rewrite LS; exact Pm9FpSites.site_133ea4).
  exact (CVFA.vf_leaf_soundA_pre L ar C HI HIok LYI LYR LYB LYN PMSA.fp_ok (fun fx H => H) FPM G.CPS G.TAGS G.HDECL ENTRY SCR ENDS G.RETS INL IMG CALLEES [] GLO GHI SC_OK GOT_OK
           eq_refl eq_refl eq_refl IMG_OK PL G.tags_ok chk heap_ok pure_ok tagpc_ok foot_ok RT IN CAL_OK 1261292 [11%nat] eq_refl SITE0 ltac:(intros x Hx; cbn in Hx; unfold CVF.CSAVED; cbn; intuition lia)).
Qed.
End Final.
End Leaf_extenddftf2_cboth.
