(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto HeapIface HeapIfaceA L5Defs L5Core L5LazyA
  Pm5PlanKit Pm5L5DefsA FrmInv Pm5FrmInv FpBridge Pm5FpSites PmHeapIfaceA PmLibDefsA PmLibSpecsA CutVFXM DecIface DecScanPure DecOkDefsM DecOkSemM DecOkSemA DecIfaceA Pm5DecKinds5 Pm5DecfloatLems5.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutVF.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutHeap2 CutAuto CutLib CutL5 CutOpsD CutAutoD CutCertA CutHeapA CutL5A CutBridgeA CutPureA CutVFA Pm5CutKitD DecAssume.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import Pm5Leaf_extenddftf2 Pm5Leaf_letf2 Pm5Leaf_getf2 Pm5Leaf_multf3 Pm5Leaf_addtf3 Pm5Leaf_subtf3 Pm5Leaf_floatsitf Pm5Leaf_divtf3 Pm5Leaf_scalbn Pm5Leaf_floatunsitf Pm5Leaf_copysignl Pm5Leaf_fmodl Pm5Leaf_fabsl.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_decfloat5_xboth.
Import ListNotations. Import AX2. Import AX2B. Import AX2S. Import DOK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module DFOA.
Definition AD : PDC.addrs := PDCA.xboth.
Definition SCANEXP : Z := 1388776.   Definition RET_PC : Z := 1384048.   Definition SCALBNL : Z := 1390184.
Definition TPV : Z := 6953104.       Definition ERRNO : Z := 6952940.    Definition GA : Z := 7084240.
Definition IMG_LO : Z := 65536.    Definition IMG_HI : Z := 1466368.
Definition GLO : Z := 1433600. Definition GHI : Z := 1433600.
Definition INL : list (Z * (Z * list nat * option Z)) := map (fun pc => (pc, (4, [], None))) [1383296; 1383524; 1383528; 1383532; 1383880; 1383888; 1383892; 1386048; 1386060; 1386100; 1386296; 1386340; 1386344; 1386360].
Definition CALLEES : list (Z * (Z * option (Z * Z))) := [(1326820, (0, None)); (1347828, (0, None)); (1348028, (0, None)); (1348216, (80, None)); (1350568, (48, None)); (1352624, (48, None)); (1352640, (0, None)); (1352904, (112, None)); (1355212, (0, (Some (65536, 1466368)))); (1377820, (0, None)); (1389400, (0, None)); (1389440, (192, None)); (1390172, (0, None))].
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
Lemma lems : LEMS_OK. Proof. exact Pm5DecfloatLems5.lems_ok. Qed.

Lemma inl_ok : forall e, In e INL -> CVF.inl_sem RSEGS e.
Proof.
  intros e H. unfold INL in H. cbn [map In] in H.
  destruct H as [<-|H]; [cbn; exact Pm5FpSites.site_151b44|].
  destruct H as [<-|H]; [cbn; exact Pm5FpSites.site_151c28|].
  destruct H as [<-|H]; [cbn; exact Pm5FpSites.site_151c2c|].
  destruct H as [<-|H]; [cbn; exact Pm5FpSites.site_151c30|].
  destruct H as [<-|H]; [cbn; exact Pm5FpSites.site_151d8c|].
  destruct H as [<-|H]; [cbn; exact Pm5FpSites.site_151d94|].
  destruct H as [<-|H]; [cbn; exact Pm5FpSites.site_151d98|].
  destruct H as [<-|H]; [cbn; exact Pm5FpSites.site_152604|].
  destruct H as [<-|H]; [cbn; exact Pm5FpSites.site_152610|].
  destruct H as [<-|H]; [cbn; exact Pm5FpSites.site_152638|].
  destruct H as [<-|H]; [cbn; exact Pm5FpSites.site_1526fc|].
  destruct H as [<-|H]; [cbn; exact Pm5FpSites.site_152728|].
  destruct H as [<-|H]; [cbn; exact Pm5FpSites.site_15272c|].
  destruct H as [<-|H]; [cbn; exact Pm5FpSites.site_15273c|].
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
  - exact (Leaf_extenddftf2_xboth.ok L ar C HI HIok LAY).
  - exact (Leaf_letf2_xboth.ok L ar C HI HIok LAY).
  - exact (Leaf_getf2_xboth.ok L ar C HI HIok LAY).
  - exact (Leaf_multf3_xboth.ok L ar C HI HIok LAY).
  - exact (Leaf_addtf3_xboth.ok L ar C HI HIok LAY).
  - exact (Leaf_subtf3_xboth.ok L ar C HI HIok LAY).
  - exact (Leaf_floatsitf_xboth.ok L ar C HI HIok LAY).
  - exact (Leaf_divtf3_xboth.ok L ar C HI HIok LAY).
  - exact (Leaf_scalbn_xboth.ok L ar C HI HIok LAY).
  - exact (Leaf_floatunsitf_xboth.ok L ar C HI HIok LAY).
  - exact (Leaf_copysignl_xboth.ok L ar C HI HIok LAY).
  - exact (Leaf_fmodl_xboth.ok L ar C HI HIok LAY).
  - exact (Leaf_fabsl_xboth.ok L ar C HI HIok LAY).
Qed.
End Final.
End DFOA.
