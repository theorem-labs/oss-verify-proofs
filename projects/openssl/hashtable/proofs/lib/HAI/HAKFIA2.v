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
From OSSVerify.Proofs.openssl.hashtable.lib Require Import HAKge1A2.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import KC1A2Lit FIEndK1A2 KC2A2Lit FIEndK2A2 KC3A2Lit FIEndK3A2 KC4A2Lit FIEndK4A2 KC5A2Lit FIEndK5A2 KC6A2Lit FIEndK6A2 KC7A2Lit FIEndK7A2 KC8A2Lit FIEndK8A2 KC9A2Lit FIEndK9A2 KC10A2Lit FIEndK10A2.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import FI8HoleK1A2 FI8HoleK2A2 FI8HoleK3A2 FI8HoleK4A2 FI8HoleK5A2 FI8HoleK6A2 FI8HoleK7A2 FI8HoleK8A2 FI8HoleK9A2 FI8HoleK10A2.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import NK1eTail VG1KA2e1 FeHoleK1e FeHoleK1ec FeHoleK1es.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import NK2eTail VG2KA2e2 FeHoleK2es.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import NK3eTail VG3KA2e3 FeHoleK3es.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import NK4eTail VG4KA2e4 FeHoleK4es.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import NK5eTail VG5KA2e5 FeHoleK5es.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import NK6eTail VG6KA2e6 FeHoleK6es.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import NK7eTail VG7KA2e7 FeHoleK7es.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import NK8eTail VG8KA2e8 FeHoleK8es.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import NK9eTail VG9KA2e9 FeHoleK9es.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import NK10eTail VG10KA2e10 FeHoleK10es.
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


  Lemma kr6_fiendk1a2 : knows_range (kn fiendk1a2) 6%nat 6 6 = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma pk1 : piece SV argH ISP fs kc1a2_hs301 TTK.
  Proof.
    apply (HAChain.hole_compose SV argH ISP fs kc1a2_hs301 fiendk1a2 TTK); [vm_compute; lia | exact TTK_agree | exact (FI8HoleK1A2.fi_hole_k1a2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HAJoin.piece_even_only SV argH ISP fs fiendk1a2 TTK kr6_fiendk1a2
      (HAJoin.piece_svg_all SV argH ISP fs NK1eTail.PALL _ TTK (fun _ => I)
        (VG1KA2e1.vtail_a2e1 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit NK1eTail.PALL NK1eTail.PALL_agree TTK TTK_agree TTK_nil
           (NK1eTail.tail_g1t012e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (FeHoleK1e.fe_hole_k1e sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleK1ec.fe_hole_k1ec sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleK1es.fe_hole_k1es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG NK1eTail.PALL SV) argH ISP fs (with_facts fiendk1a2 [par_even]) TTK))).
  Qed.
  Lemma kr6_fiendk2a2 : knows_range (kn fiendk2a2) 6%nat 6 6 = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma pk2 : piece SV argH ISP fs kc2a2_hs302 TTK.
  Proof.
    apply (HAChain.hole_compose SV argH ISP fs kc2a2_hs302 fiendk2a2 TTK); [vm_compute; lia | exact TTK_agree | exact (FI8HoleK2A2.fi_hole_k2a2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HAJoin.piece_even_only SV argH ISP fs fiendk2a2 TTK kr6_fiendk2a2
      (HAJoin.piece_svg_all SV argH ISP fs NK2eTail.PALL _ TTK (fun _ => I)
        (VG2KA2e2.vtail_a2e2 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit NK2eTail.PALL NK2eTail.PALL_agree TTK TTK_agree TTK_nil
           (NK2eTail.tail_g2t012e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (FeHoleK2es.fe_hole_k2es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG NK2eTail.PALL SV) argH ISP fs (with_facts fiendk2a2 [par_even]) TTK))).
  Qed.
  Lemma kr6_fiendk3a2 : knows_range (kn fiendk3a2) 6%nat 6 6 = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma pk3 : piece SV argH ISP fs kc3a2_hs303 TTK.
  Proof.
    apply (HAChain.hole_compose SV argH ISP fs kc3a2_hs303 fiendk3a2 TTK); [vm_compute; lia | exact TTK_agree | exact (FI8HoleK3A2.fi_hole_k3a2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HAJoin.piece_even_only SV argH ISP fs fiendk3a2 TTK kr6_fiendk3a2
      (HAJoin.piece_svg_all SV argH ISP fs NK3eTail.PALL _ TTK (fun _ => I)
        (VG3KA2e3.vtail_a2e3 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit NK3eTail.PALL NK3eTail.PALL_agree TTK TTK_agree TTK_nil
           (NK3eTail.tail_g3t012e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (FeHoleK3es.fe_hole_k3es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG NK3eTail.PALL SV) argH ISP fs (with_facts fiendk3a2 [par_even]) TTK))).
  Qed.
  Lemma kr6_fiendk4a2 : knows_range (kn fiendk4a2) 6%nat 6 6 = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma pk4 : piece SV argH ISP fs kc4a2_hs304 TTK.
  Proof.
    apply (HAChain.hole_compose SV argH ISP fs kc4a2_hs304 fiendk4a2 TTK); [vm_compute; lia | exact TTK_agree | exact (FI8HoleK4A2.fi_hole_k4a2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HAJoin.piece_even_only SV argH ISP fs fiendk4a2 TTK kr6_fiendk4a2
      (HAJoin.piece_svg_all SV argH ISP fs NK4eTail.PALL _ TTK (fun _ => I)
        (VG4KA2e4.vtail_a2e4 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit NK4eTail.PALL NK4eTail.PALL_agree TTK TTK_agree TTK_nil
           (NK4eTail.tail_g4t012e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (FeHoleK4es.fe_hole_k4es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG NK4eTail.PALL SV) argH ISP fs (with_facts fiendk4a2 [par_even]) TTK))).
  Qed.
  Lemma kr6_fiendk5a2 : knows_range (kn fiendk5a2) 6%nat 6 6 = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma pk5 : piece SV argH ISP fs kc5a2_hs305 TTK.
  Proof.
    apply (HAChain.hole_compose SV argH ISP fs kc5a2_hs305 fiendk5a2 TTK); [vm_compute; lia | exact TTK_agree | exact (FI8HoleK5A2.fi_hole_k5a2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HAJoin.piece_even_only SV argH ISP fs fiendk5a2 TTK kr6_fiendk5a2
      (HAJoin.piece_svg_all SV argH ISP fs NK5eTail.PALL _ TTK (fun _ => I)
        (VG5KA2e5.vtail_a2e5 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit NK5eTail.PALL NK5eTail.PALL_agree TTK TTK_agree TTK_nil
           (NK5eTail.tail_g5t012e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (FeHoleK5es.fe_hole_k5es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG NK5eTail.PALL SV) argH ISP fs (with_facts fiendk5a2 [par_even]) TTK))).
  Qed.
  Lemma kr6_fiendk6a2 : knows_range (kn fiendk6a2) 6%nat 6 6 = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma pk6 : piece SV argH ISP fs kc6a2_hs306 TTK.
  Proof.
    apply (HAChain.hole_compose SV argH ISP fs kc6a2_hs306 fiendk6a2 TTK); [vm_compute; lia | exact TTK_agree | exact (FI8HoleK6A2.fi_hole_k6a2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HAJoin.piece_even_only SV argH ISP fs fiendk6a2 TTK kr6_fiendk6a2
      (HAJoin.piece_svg_all SV argH ISP fs NK6eTail.PALL _ TTK (fun _ => I)
        (VG6KA2e6.vtail_a2e6 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit NK6eTail.PALL NK6eTail.PALL_agree TTK TTK_agree TTK_nil
           (NK6eTail.tail_g6t012e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (FeHoleK6es.fe_hole_k6es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG NK6eTail.PALL SV) argH ISP fs (with_facts fiendk6a2 [par_even]) TTK))).
  Qed.
  Lemma kr6_fiendk7a2 : knows_range (kn fiendk7a2) 6%nat 6 6 = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma pk7 : piece SV argH ISP fs kc7a2_hs307 TTK.
  Proof.
    apply (HAChain.hole_compose SV argH ISP fs kc7a2_hs307 fiendk7a2 TTK); [vm_compute; lia | exact TTK_agree | exact (FI8HoleK7A2.fi_hole_k7a2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HAJoin.piece_even_only SV argH ISP fs fiendk7a2 TTK kr6_fiendk7a2
      (HAJoin.piece_svg_all SV argH ISP fs NK7eTail.PALL _ TTK (fun _ => I)
        (VG7KA2e7.vtail_a2e7 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit NK7eTail.PALL NK7eTail.PALL_agree TTK TTK_agree TTK_nil
           (NK7eTail.tail_g7t012e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (FeHoleK7es.fe_hole_k7es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG NK7eTail.PALL SV) argH ISP fs (with_facts fiendk7a2 [par_even]) TTK))).
  Qed.
  Lemma kr6_fiendk8a2 : knows_range (kn fiendk8a2) 6%nat 6 6 = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma pk8 : piece SV argH ISP fs kc8a2_hs308 TTK.
  Proof.
    apply (HAChain.hole_compose SV argH ISP fs kc8a2_hs308 fiendk8a2 TTK); [vm_compute; lia | exact TTK_agree | exact (FI8HoleK8A2.fi_hole_k8a2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HAJoin.piece_even_only SV argH ISP fs fiendk8a2 TTK kr6_fiendk8a2
      (HAJoin.piece_svg_all SV argH ISP fs NK8eTail.PALL _ TTK (fun _ => I)
        (VG8KA2e8.vtail_a2e8 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit NK8eTail.PALL NK8eTail.PALL_agree TTK TTK_agree TTK_nil
           (NK8eTail.tail_g8t012e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (FeHoleK8es.fe_hole_k8es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG NK8eTail.PALL SV) argH ISP fs (with_facts fiendk8a2 [par_even]) TTK))).
  Qed.
  Lemma kr6_fiendk9a2 : knows_range (kn fiendk9a2) 6%nat 6 6 = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma pk9 : piece SV argH ISP fs kc9a2_hs309 TTK.
  Proof.
    apply (HAChain.hole_compose SV argH ISP fs kc9a2_hs309 fiendk9a2 TTK); [vm_compute; lia | exact TTK_agree | exact (FI8HoleK9A2.fi_hole_k9a2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HAJoin.piece_even_only SV argH ISP fs fiendk9a2 TTK kr6_fiendk9a2
      (HAJoin.piece_svg_all SV argH ISP fs NK9eTail.PALL _ TTK (fun _ => I)
        (VG9KA2e9.vtail_a2e9 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit NK9eTail.PALL NK9eTail.PALL_agree TTK TTK_agree TTK_nil
           (NK9eTail.tail_g9t012e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (FeHoleK9es.fe_hole_k9es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG NK9eTail.PALL SV) argH ISP fs (with_facts fiendk9a2 [par_even]) TTK))).
  Qed.
  Lemma kr6_fiendk10a2 : knows_range (kn fiendk10a2) 6%nat 6 6 = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma pk10 : piece SV argH ISP fs kc10a2_hs310 TTK.
  Proof.
    apply (HAChain.hole_compose SV argH ISP fs kc10a2_hs310 fiendk10a2 TTK); [vm_compute; lia | exact TTK_agree | exact (FI8HoleK10A2.fi_hole_k10a2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HAJoin.piece_even_only SV argH ISP fs fiendk10a2 TTK kr6_fiendk10a2
      (HAJoin.piece_svg_all SV argH ISP fs NK10eTail.PALL _ TTK (fun _ => I)
        (VG10KA2e10.vtail_a2e10 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit NK10eTail.PALL NK10eTail.PALL_agree TTK TTK_agree TTK_nil
           (NK10eTail.tail_g10t012e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (FeHoleK10es.fe_hole_k10es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG NK10eTail.PALL SV) argH ISP fs (with_facts fiendk10a2 [par_even]) TTK))).
  Qed.

  Theorem hfi_a2_sec : forall k, 1 <= k <= 10 -> 2 ^ (15 + k) <= flen c <= 2 ^ (16 + k) - 1 -> piece SV argH ISP fs (HAKge1A2.fi_start_a2 k) TTK.
  Proof.
    intros k HK _.
    assert (HKk : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10) by lia.
    destruct HKk as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]; [exact pk1 | exact pk2 | exact pk3 | exact pk4 | exact pk5 | exact pk6 | exact pk7 | exact pk8 | exact pk9 | exact pk10].
  Qed.
End S.

Theorem hfi_a2 : forall sp rdraw brk0 argv envp fs uid hw, valid_sp sp -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp argv envp ->
  forall k, 1 <= k <= 10 -> 2 ^ (15 + k) <= flen (content_of argv fs) <= 2 ^ (16 + k) - 1 ->
  piece (SINVm HAPH sp rdraw brk0 argv envp uid hw (content_of argv fs)) (argH0 HAPH sp rdraw argv envp uid hw) (bv_unsigned sp) fs (HAKge1A2.fi_start_a2 k) TTK.
Proof. intros sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit. exact (hfi_a2_sec sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit). Qed.
