(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto HeapIface HeapIfaceA L5Defs L5Core L5LazyA
  Pm8PlanKit Pm8L5DefsA FrmInv Pm8FrmInv FpBridge Pm8FpSites PmHeapIfaceA PmLibDefsA PmLibSpecsA CutVFXM DecIface DecScanPure DecOkDefsM DecOkSemM DecOkSemA DecIfaceA Pm8DecKinds5 Pm8DecfloatLems5.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutVF.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutHeap2 CutAuto CutLib CutL5 CutOpsD CutAutoD CutCertA CutHeapA CutL5A CutBridgeA CutPureA CutVFA Pm8CutKitD DecAssume.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import Pm8Leaf_extenddftf2 Pm8Leaf_letf2 Pm8Leaf_getf2 Pm8Leaf_multf3 Pm8Leaf_addtf3 Pm8Leaf_subtf3 Pm8Leaf_floatsitf Pm8Leaf_divtf3 Pm8Leaf_scalbn Pm8Leaf_floatunsitf Pm8Leaf_copysignl Pm8Leaf_fmodl Pm8Leaf_fabsl.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_decfloat5_casan.
Import ListNotations. Import AX2. Import AX2B. Import AX2S. Import DOK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module DFOA.
Definition AD : PDC.addrs := PDCA.casan.
Definition SCANEXP : Z := 1317684.   Definition RET_PC : Z := 1312956.   Definition SCALBNL : Z := 1319092.
Definition TPV : Z := 6883920.       Definition ERRNO : Z := 6883756.    Definition GA : Z := 7015056.
Definition IMG_LO : Z := 65536.    Definition IMG_HI : Z := 1392640.
Definition GLO : Z := 1359872. Definition GHI : Z := 1359872.
Definition INL : list (Z * (Z * list nat * option Z)) := map (fun pc => (pc, (4, [], None))) [1312204; 1312432; 1312436; 1312440; 1312788; 1312796; 1312800; 1314956; 1314968; 1315008; 1315204; 1315248; 1315252; 1315268].
Definition CALLEES : list (Z * (Z * option (Z * Z))) := [(1255888, (0, None)); (1276736, (0, None)); (1276936, (0, None)); (1277124, (80, None)); (1279476, (48, None)); (1281532, (48, None)); (1281548, (0, None)); (1281812, (112, None)); (1284120, (0, (Some (65536, 1392640)))); (1306728, (0, None)); (1318308, (0, None)); (1318348, (192, None)); (1319080, (0, None))].
Lemma ad_ok : PDC.a_scanexp AD = SCANEXP /\ PDC.a_TP AD = TPV /\ PDC.a_G AD = GA /\ PDC.a_img_lo AD = IMG_LO /\ PDC.a_img_hi AD = IMG_HI /\ TPV - 164 = ERRNO. Proof. repeat split; reflexivity. Qed.

Definition cutc := DOSA.cut_chk CPS RETS DK5.DKINDS SCANEXP.
Definition gchk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TGoto j s => match nth_error CPS j with Some cj => DOSA.goto_chk2 CPS RETS DK5.DKINDS SCANEXP i c ps j cj s | None => false end
  | CC.TOther _ => true
  end.
Definition ochk := DOSA.other_chk CPS RETS DK5.DKINDS SCANEXP RET_PC SCALBNL INL CALLEES IMG_LO IMG_HI HDECL [] GLO GHI.
Lemma cuts_ok : CC.cps_all CPS cutc = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma gotos_ok : CH2.leaves_all CPS TAGS gchk = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma others_ok : CC.others_all CPS TAGS ochk = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma heap_ok : CHA.heap_chkA DOK.NF HDECL (CPA.NOB CPS) (CPA.NOF CPS) CPS TAGS = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma foot_ok : CC.cps_all CPS (fun _ c => CHA.foot_chk DOK.NF HDECL c [] []) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma hd_ok : CH.hd_scr HDECL = 256 /\ CH.hd_wrs HDECL = [(EVar 2, 0, ELit 8416); (EVar 21, 8, ELit 8); (EVar 4, -164, ELit 4)]
  /\ CH.hd_crs HDECL = [(EVar 32, 0, APC.eaddz (EVar 47) 1); (EVar 21, 16, ELit 184); (ELit 0, GA, ELit 8)] /\ CH.hd_img HDECL = [(IMG_LO, IMG_HI)].
Proof. repeat split; reflexivity. Qed.
Lemma ret_pc_ok : CL.is_ret_at RSEGS RET_PC.
Proof. CL.solve_is_ret. Qed.
Lemma lems : LEMS_OK. Proof. exact Pm8DecfloatLems5.lems_ok. Qed.

Lemma inl_ok : forall e, In e INL -> CVF.inl_sem RSEGS e.
Proof.
  intros e H. unfold INL in H. cbn [map In] in H.
  destruct H as [<-|H]; [cbn; exact Pm8FpSites.site_140588|].
  destruct H as [<-|H]; [cbn; exact Pm8FpSites.site_14066c|].
  destruct H as [<-|H]; [cbn; exact Pm8FpSites.site_140670|].
  destruct H as [<-|H]; [cbn; exact Pm8FpSites.site_140674|].
  destruct H as [<-|H]; [cbn; exact Pm8FpSites.site_1407d0|].
  destruct H as [<-|H]; [cbn; exact Pm8FpSites.site_1407d8|].
  destruct H as [<-|H]; [cbn; exact Pm8FpSites.site_1407dc|].
  destruct H as [<-|H]; [cbn; exact Pm8FpSites.site_141048|].
  destruct H as [<-|H]; [cbn; exact Pm8FpSites.site_141054|].
  destruct H as [<-|H]; [cbn; exact Pm8FpSites.site_14107c|].
  destruct H as [<-|H]; [cbn; exact Pm8FpSites.site_141140|].
  destruct H as [<-|H]; [cbn; exact Pm8FpSites.site_14116c|].
  destruct H as [<-|H]; [cbn; exact Pm8FpSites.site_141170|].
  destruct H as [<-|H]; [cbn; exact Pm8FpSites.site_141180|].
  destruct H.
Qed.

Section Final.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout. Variable ar : asan_run. Variable C : asan_statics_cells. Variable HI : asan_iface.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LAY : L5A.as0_layout L C.
Lemma callees_ok : forall pc SCRc IMG, In (pc, (SCRc, IMG)) CALLEES -> CVFA.vf_contractA L ar HI PMSA.fp_ok pc SCRc IMG.
Proof.
  intros pc SCRc IMG H. unfold CALLEES in H. cbn [In] in H.
  repeat (destruct H as [H|H]; [injection H as <- <- <- |]); try contradiction.
  - exact (Leaf_extenddftf2_casan.ok L ar C HI HIok LAY).
  - exact (Leaf_letf2_casan.ok L ar C HI HIok LAY).
  - exact (Leaf_getf2_casan.ok L ar C HI HIok LAY).
  - exact (Leaf_multf3_casan.ok L ar C HI HIok LAY).
  - exact (Leaf_addtf3_casan.ok L ar C HI HIok LAY).
  - exact (Leaf_subtf3_casan.ok L ar C HI HIok LAY).
  - exact (Leaf_floatsitf_casan.ok L ar C HI HIok LAY).
  - exact (Leaf_divtf3_casan.ok L ar C HI HIok LAY).
  - exact (Leaf_scalbn_casan.ok L ar C HI HIok LAY).
  - exact (Leaf_floatunsitf_casan.ok L ar C HI HIok LAY).
  - exact (Leaf_copysignl_casan.ok L ar C HI HIok LAY).
  - exact (Leaf_fmodl_casan.ok L ar C HI HIok LAY).
  - exact (Leaf_fabsl_casan.ok L ar C HI HIok LAY).
Qed.
End Final.
End DFOA.
