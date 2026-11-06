(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Namei.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Open.
From OSSVerify.openssl.hashtable.images Require Import Asan.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import PropExec CatExec ShapeAlg AgentLib AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanNodesIO AsanInit.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import ClaVerdict Spec SpecGen HTSpec ShapeLaws.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import CxRel CxPlan CxPlanSound CxOfAps CxReblob HAPlanImage HAAtable HAChain HACheckG HAParity HAJoin HATgtGlue HAOpenDefs HAHdrDefs HAFullDefs.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import HAKge1B2.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import KC1B2Lit FIEndK1B2 KC2B2Lit FIEndK2B2 KC3B2Lit FIEndK3B2 KC4B2Lit FIEndK4B2 KC5B2Lit FIEndK5B2 KC6B2Lit FIEndK6B2 KC7B2Lit FIEndK7B2 KC8B2Lit FIEndK8B2 KC9B2Lit FIEndK9B2 KC10B2Lit FIEndK10B2.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import FI8HoleK1B2 FI8HoleK2B2 FI8HoleK3B2 FI8HoleK4B2 FI8HoleK5B2 FI8HoleK6B2 FI8HoleK7B2 FI8HoleK8B2 FI8HoleK9B2 FI8HoleK10B2.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import NK1eTail VG1KB2e1 FeHoleK1e FeHoleK1ec FeHoleK1es.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import NK2eTail VG2KB2e2 FeHoleK2es.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import NK3eTail VG3KB2e3 FeHoleK3es.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import NK4eTail VG4KB2e4 FeHoleK4es.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import NK5eTail VG5KB2e5 FeHoleK5es.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import NK6eTail VG6KB2e6 FeHoleK6es.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import NK7eTail VG7KB2e7 FeHoleK7es.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import NK8eTail VG8KB2e8 FeHoleK8es.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import NK9eTail VG9KB2e9 FeHoleK9es.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import NK10eTail VG10KB2e10 FeHoleK10es.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.

Section S.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 : word.
  Variables argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variables uid hw : word.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Let c := content_of argv fs.
  #[local] Notation SV := (SINVm HAPH sp rdraw brk0 argv envp uid hw c).
  #[local] Notation argH := (argH0 HAPH sp rdraw argv envp uid hw).
  #[local] Notation ISP := (bv_unsigned sp).


  Lemma kr6_fiendk1b2 : knows_range (kn fiendk1b2) 6%nat 6 6 = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma pk1 : piece SV argH ISP fs kc1b2_hs301 TTK.
  Proof.
    apply (HAChain.hole_compose SV argH ISP fs kc1b2_hs301 fiendk1b2 TTK); [vm_compute; lia | exact TTK_agree | exact (FI8HoleK1B2.fi_hole_k1b2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HAJoin.piece_even_only SV argH ISP fs fiendk1b2 TTK kr6_fiendk1b2
      (HAJoin.piece_svg_all SV argH ISP fs NK1eTail.PALL _ TTK (fun _ => I)
        (VG1KB2e1.vtail_b2e1 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit NK1eTail.PALL NK1eTail.PALL_agree TTK TTK_agree TTK_nil
           (NK1eTail.tail_g1t012e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (FeHoleK1e.fe_hole_k1e sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleK1ec.fe_hole_k1ec sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleK1es.fe_hole_k1es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG NK1eTail.PALL SV) argH ISP fs (with_facts fiendk1b2 [par_even]) TTK))).
  Qed.
  Lemma kr6_fiendk2b2 : knows_range (kn fiendk2b2) 6%nat 6 6 = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma pk2 : piece SV argH ISP fs kc2b2_hs302 TTK.
  Proof.
    apply (HAChain.hole_compose SV argH ISP fs kc2b2_hs302 fiendk2b2 TTK); [vm_compute; lia | exact TTK_agree | exact (FI8HoleK2B2.fi_hole_k2b2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HAJoin.piece_even_only SV argH ISP fs fiendk2b2 TTK kr6_fiendk2b2
      (HAJoin.piece_svg_all SV argH ISP fs NK2eTail.PALL _ TTK (fun _ => I)
        (VG2KB2e2.vtail_b2e2 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit NK2eTail.PALL NK2eTail.PALL_agree TTK TTK_agree TTK_nil
           (NK2eTail.tail_g2t012e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (FeHoleK2es.fe_hole_k2es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG NK2eTail.PALL SV) argH ISP fs (with_facts fiendk2b2 [par_even]) TTK))).
  Qed.
  Lemma kr6_fiendk3b2 : knows_range (kn fiendk3b2) 6%nat 6 6 = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma pk3 : piece SV argH ISP fs kc3b2_hs303 TTK.
  Proof.
    apply (HAChain.hole_compose SV argH ISP fs kc3b2_hs303 fiendk3b2 TTK); [vm_compute; lia | exact TTK_agree | exact (FI8HoleK3B2.fi_hole_k3b2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HAJoin.piece_even_only SV argH ISP fs fiendk3b2 TTK kr6_fiendk3b2
      (HAJoin.piece_svg_all SV argH ISP fs NK3eTail.PALL _ TTK (fun _ => I)
        (VG3KB2e3.vtail_b2e3 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit NK3eTail.PALL NK3eTail.PALL_agree TTK TTK_agree TTK_nil
           (NK3eTail.tail_g3t012e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (FeHoleK3es.fe_hole_k3es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG NK3eTail.PALL SV) argH ISP fs (with_facts fiendk3b2 [par_even]) TTK))).
  Qed.
  Lemma kr6_fiendk4b2 : knows_range (kn fiendk4b2) 6%nat 6 6 = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma pk4 : piece SV argH ISP fs kc4b2_hs304 TTK.
  Proof.
    apply (HAChain.hole_compose SV argH ISP fs kc4b2_hs304 fiendk4b2 TTK); [vm_compute; lia | exact TTK_agree | exact (FI8HoleK4B2.fi_hole_k4b2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HAJoin.piece_even_only SV argH ISP fs fiendk4b2 TTK kr6_fiendk4b2
      (HAJoin.piece_svg_all SV argH ISP fs NK4eTail.PALL _ TTK (fun _ => I)
        (VG4KB2e4.vtail_b2e4 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit NK4eTail.PALL NK4eTail.PALL_agree TTK TTK_agree TTK_nil
           (NK4eTail.tail_g4t012e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (FeHoleK4es.fe_hole_k4es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG NK4eTail.PALL SV) argH ISP fs (with_facts fiendk4b2 [par_even]) TTK))).
  Qed.
  Lemma kr6_fiendk5b2 : knows_range (kn fiendk5b2) 6%nat 6 6 = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma pk5 : piece SV argH ISP fs kc5b2_hs305 TTK.
  Proof.
    apply (HAChain.hole_compose SV argH ISP fs kc5b2_hs305 fiendk5b2 TTK); [vm_compute; lia | exact TTK_agree | exact (FI8HoleK5B2.fi_hole_k5b2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HAJoin.piece_even_only SV argH ISP fs fiendk5b2 TTK kr6_fiendk5b2
      (HAJoin.piece_svg_all SV argH ISP fs NK5eTail.PALL _ TTK (fun _ => I)
        (VG5KB2e5.vtail_b2e5 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit NK5eTail.PALL NK5eTail.PALL_agree TTK TTK_agree TTK_nil
           (NK5eTail.tail_g5t012e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (FeHoleK5es.fe_hole_k5es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG NK5eTail.PALL SV) argH ISP fs (with_facts fiendk5b2 [par_even]) TTK))).
  Qed.
  Lemma kr6_fiendk6b2 : knows_range (kn fiendk6b2) 6%nat 6 6 = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma pk6 : piece SV argH ISP fs kc6b2_hs306 TTK.
  Proof.
    apply (HAChain.hole_compose SV argH ISP fs kc6b2_hs306 fiendk6b2 TTK); [vm_compute; lia | exact TTK_agree | exact (FI8HoleK6B2.fi_hole_k6b2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HAJoin.piece_even_only SV argH ISP fs fiendk6b2 TTK kr6_fiendk6b2
      (HAJoin.piece_svg_all SV argH ISP fs NK6eTail.PALL _ TTK (fun _ => I)
        (VG6KB2e6.vtail_b2e6 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit NK6eTail.PALL NK6eTail.PALL_agree TTK TTK_agree TTK_nil
           (NK6eTail.tail_g6t012e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (FeHoleK6es.fe_hole_k6es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG NK6eTail.PALL SV) argH ISP fs (with_facts fiendk6b2 [par_even]) TTK))).
  Qed.
  Lemma kr6_fiendk7b2 : knows_range (kn fiendk7b2) 6%nat 6 6 = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma pk7 : piece SV argH ISP fs kc7b2_hs307 TTK.
  Proof.
    apply (HAChain.hole_compose SV argH ISP fs kc7b2_hs307 fiendk7b2 TTK); [vm_compute; lia | exact TTK_agree | exact (FI8HoleK7B2.fi_hole_k7b2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HAJoin.piece_even_only SV argH ISP fs fiendk7b2 TTK kr6_fiendk7b2
      (HAJoin.piece_svg_all SV argH ISP fs NK7eTail.PALL _ TTK (fun _ => I)
        (VG7KB2e7.vtail_b2e7 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit NK7eTail.PALL NK7eTail.PALL_agree TTK TTK_agree TTK_nil
           (NK7eTail.tail_g7t012e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (FeHoleK7es.fe_hole_k7es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG NK7eTail.PALL SV) argH ISP fs (with_facts fiendk7b2 [par_even]) TTK))).
  Qed.
  Lemma kr6_fiendk8b2 : knows_range (kn fiendk8b2) 6%nat 6 6 = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma pk8 : piece SV argH ISP fs kc8b2_hs308 TTK.
  Proof.
    apply (HAChain.hole_compose SV argH ISP fs kc8b2_hs308 fiendk8b2 TTK); [vm_compute; lia | exact TTK_agree | exact (FI8HoleK8B2.fi_hole_k8b2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HAJoin.piece_even_only SV argH ISP fs fiendk8b2 TTK kr6_fiendk8b2
      (HAJoin.piece_svg_all SV argH ISP fs NK8eTail.PALL _ TTK (fun _ => I)
        (VG8KB2e8.vtail_b2e8 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit NK8eTail.PALL NK8eTail.PALL_agree TTK TTK_agree TTK_nil
           (NK8eTail.tail_g8t012e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (FeHoleK8es.fe_hole_k8es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG NK8eTail.PALL SV) argH ISP fs (with_facts fiendk8b2 [par_even]) TTK))).
  Qed.
  Lemma kr6_fiendk9b2 : knows_range (kn fiendk9b2) 6%nat 6 6 = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma pk9 : piece SV argH ISP fs kc9b2_hs309 TTK.
  Proof.
    apply (HAChain.hole_compose SV argH ISP fs kc9b2_hs309 fiendk9b2 TTK); [vm_compute; lia | exact TTK_agree | exact (FI8HoleK9B2.fi_hole_k9b2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HAJoin.piece_even_only SV argH ISP fs fiendk9b2 TTK kr6_fiendk9b2
      (HAJoin.piece_svg_all SV argH ISP fs NK9eTail.PALL _ TTK (fun _ => I)
        (VG9KB2e9.vtail_b2e9 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit NK9eTail.PALL NK9eTail.PALL_agree TTK TTK_agree TTK_nil
           (NK9eTail.tail_g9t012e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (FeHoleK9es.fe_hole_k9es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG NK9eTail.PALL SV) argH ISP fs (with_facts fiendk9b2 [par_even]) TTK))).
  Qed.
  Lemma kr6_fiendk10b2 : knows_range (kn fiendk10b2) 6%nat 6 6 = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma pk10 : piece SV argH ISP fs kc10b2_hs310 TTK.
  Proof.
    apply (HAChain.hole_compose SV argH ISP fs kc10b2_hs310 fiendk10b2 TTK); [vm_compute; lia | exact TTK_agree | exact (FI8HoleK10B2.fi_hole_k10b2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HAJoin.piece_even_only SV argH ISP fs fiendk10b2 TTK kr6_fiendk10b2
      (HAJoin.piece_svg_all SV argH ISP fs NK10eTail.PALL _ TTK (fun _ => I)
        (VG10KB2e10.vtail_b2e10 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit NK10eTail.PALL NK10eTail.PALL_agree TTK TTK_agree TTK_nil
           (NK10eTail.tail_g10t012e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (FeHoleK10es.fe_hole_k10es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG NK10eTail.PALL SV) argH ISP fs (with_facts fiendk10b2 [par_even]) TTK))).
  Qed.

  Theorem hfi_b2_sec : forall k, 1 <= k <= 10 -> 2 ^ (15 + k) <= flen c <= 2 ^ (16 + k) - 1 -> piece SV argH ISP fs (HAKge1B2.fi_start_b2 k) TTK.
  Proof.
    intros k HK _.
    assert (HKk : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10) by lia.
    destruct HKk as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]; [exact pk1 | exact pk2 | exact pk3 | exact pk4 | exact pk5 | exact pk6 | exact pk7 | exact pk8 | exact pk9 | exact pk10].
  Qed.
End S.

Theorem hfi_b2 : forall sp rdraw brk0 argv envp fs uid hw, valid_sp sp -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp argv envp ->
  forall k, 1 <= k <= 10 -> 2 ^ (15 + k) <= flen (content_of argv fs) <= 2 ^ (16 + k) - 1 ->
  piece (SINVm HAPH sp rdraw brk0 argv envp uid hw (content_of argv fs)) (argH0 HAPH sp rdraw argv envp uid hw) (bv_unsigned sp) fs (HAKge1B2.fi_start_b2 k) TTK.
Proof. intros sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit. exact (hfi_b2_sec sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit). Qed.
