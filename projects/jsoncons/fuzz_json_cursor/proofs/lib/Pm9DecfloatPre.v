(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto HeapIface HeapIfaceA L5Defs L5Core L5LazyA
  Pm9PlanKit Pm9L5DefsA FrmInv Pm9FrmInv FpBridge Pm9FpSites PmHeapIfaceA PmLibDefsA PmLibSpecsA CutVFXM DecIface DecScanPure DecOkDefsM DecOkSemM DecOkSemA DecIfaceA Pm9DecKinds5 Pm9DecfloatLems5.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutVF.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutHeap2 CutAuto CutLib CutL5 CutOpsD CutAutoD CutCertA CutHeapA CutL5A CutBridgeA CutPureA CutVFA Pm9CutKitD DecAssume.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import Pm9Leaf_extenddftf2 Pm9Leaf_letf2 Pm9Leaf_getf2 Pm9Leaf_multf3 Pm9Leaf_addtf3 Pm9Leaf_subtf3 Pm9Leaf_floatsitf Pm9Leaf_divtf3 Pm9Leaf_scalbn Pm9Leaf_floatunsitf Pm9Leaf_copysignl Pm9Leaf_fmodl Pm9Leaf_fabsl.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_decfloat5_cboth.
Import ListNotations. Import AX2. Import AX2B. Import AX2S. Import DOK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module DFOA.
Definition AD : PDC.addrs := PDCA.cboth.
Definition SCANEXP : Z := 1323248.   Definition RET_PC : Z := 1318520.   Definition SCALBNL : Z := 1324656.
Definition TPV : Z := 6888848.       Definition ERRNO : Z := 6888684.    Definition GA : Z := 7019984.
Definition IMG_LO : Z := 65536.    Definition IMG_HI : Z := 1400832.
Definition GLO : Z := 1368064. Definition GHI : Z := 1368064.
Definition INL : list (Z * (Z * list nat * option Z)) := map (fun pc => (pc, (4, [], None))) [1317768; 1317996; 1318000; 1318004; 1318352; 1318360; 1318364; 1320520; 1320532; 1320572; 1320768; 1320812; 1320816; 1320832].
Definition CALLEES : list (Z * (Z * option (Z * Z))) := [(1261292, (0, None)); (1282300, (0, None)); (1282500, (0, None)); (1282688, (80, None)); (1285040, (48, None)); (1287096, (48, None)); (1287112, (0, None)); (1287376, (112, None)); (1289684, (0, (Some (65536, 1400832)))); (1312292, (0, None)); (1323872, (0, None)); (1323912, (192, None)); (1324644, (0, None))].
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
Lemma lems : LEMS_OK. Proof. exact Pm9DecfloatLems5.lems_ok. Qed.

Lemma inl_ok : forall e, In e INL -> CVF.inl_sem RSEGS e.
Proof.
  intros e H. unfold INL in H. cbn [map In] in H.
  destruct H as [<-|H]; [cbn; exact Pm9FpSites.site_141b4c|].
  destruct H as [<-|H]; [cbn; exact Pm9FpSites.site_141c30|].
  destruct H as [<-|H]; [cbn; exact Pm9FpSites.site_141c34|].
  destruct H as [<-|H]; [cbn; exact Pm9FpSites.site_141c38|].
  destruct H as [<-|H]; [cbn; exact Pm9FpSites.site_141d94|].
  destruct H as [<-|H]; [cbn; exact Pm9FpSites.site_141d9c|].
  destruct H as [<-|H]; [cbn; exact Pm9FpSites.site_141da0|].
  destruct H as [<-|H]; [cbn; exact Pm9FpSites.site_14260c|].
  destruct H as [<-|H]; [cbn; exact Pm9FpSites.site_142618|].
  destruct H as [<-|H]; [cbn; exact Pm9FpSites.site_142640|].
  destruct H as [<-|H]; [cbn; exact Pm9FpSites.site_142704|].
  destruct H as [<-|H]; [cbn; exact Pm9FpSites.site_142730|].
  destruct H as [<-|H]; [cbn; exact Pm9FpSites.site_142734|].
  destruct H as [<-|H]; [cbn; exact Pm9FpSites.site_142744|].
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
  - exact (Leaf_extenddftf2_cboth.ok L ar C HI HIok LAY).
  - exact (Leaf_letf2_cboth.ok L ar C HI HIok LAY).
  - exact (Leaf_getf2_cboth.ok L ar C HI HIok LAY).
  - exact (Leaf_multf3_cboth.ok L ar C HI HIok LAY).
  - exact (Leaf_addtf3_cboth.ok L ar C HI HIok LAY).
  - exact (Leaf_subtf3_cboth.ok L ar C HI HIok LAY).
  - exact (Leaf_floatsitf_cboth.ok L ar C HI HIok LAY).
  - exact (Leaf_divtf3_cboth.ok L ar C HI HIok LAY).
  - exact (Leaf_scalbn_cboth.ok L ar C HI HIok LAY).
  - exact (Leaf_floatunsitf_cboth.ok L ar C HI HIok LAY).
  - exact (Leaf_copysignl_cboth.ok L ar C HI HIok LAY).
  - exact (Leaf_fmodl_cboth.ok L ar C HI HIok LAY).
  - exact (Leaf_fabsl_cboth.ok L ar C HI HIok LAY).
Qed.
End Final.
End DFOA.
