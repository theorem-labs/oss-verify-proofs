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
From OSSVerify.Proofs.openssl.hashtable.lib Require Import HAKge1A1.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import KC1A1Lit FIEndK1A1 KC2A1Lit FIEndK2A1 KC3A1Lit FIEndK3A1 KC4A1Lit FIEndK4A1 KC5A1Lit FIEndK5A1 KC6A1Lit FIEndK6A1 KC7A1Lit FIEndK7A1 KC8A1Lit FIEndK8A1 KC9A1Lit FIEndK9A1 KC10A1Lit FIEndK10A1.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import FI8HoleK1A1 FI8HoleK2A1 FI8HoleK3A1 FI8HoleK4A1 FI8HoleK5A1 FI8HoleK6A1 FI8HoleK7A1 FI8HoleK8A1 FI8HoleK9A1 FI8HoleK10A1.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import NK1eTail VG1KA1e1 FeHoleK1e FeHoleK1ec FeHoleK1es.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import NK1oTail VG1KA1o1 FeHoleK1o FeHoleK1oc FeHoleK1os.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import NK2eTail VG2KA1e2 FeHoleK2es.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import NK2oTail VG2KA1o2 FeHoleK2os.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import NK3eTail VG3KA1e3 FeHoleK3es.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import NK3oTail VG3KA1o3 FeHoleK3os.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import NK4eTail VG4KA1e4 FeHoleK4es.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import NK4oTail VG4KA1o4 FeHoleK4os.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import NK5eTail VG5KA1e5 FeHoleK5es.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import NK5oTail VG5KA1o5 FeHoleK5os.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import NK6eTail VG6KA1e6 FeHoleK6es.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import NK6oTail VG6KA1o6 FeHoleK6os.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import NK7eTail VG7KA1e7 FeHoleK7es.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import NK7oTail VG7KA1o7 FeHoleK7os.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import NK8eTail VG8KA1e8 FeHoleK8es.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import NK8oTail VG8KA1o8 FeHoleK8os.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import NK9eTail VG9KA1e9 FeHoleK9es.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import NK9oTail VG9KA1o9 FeHoleK9os.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import NK10eTail VG10KA1e10 FeHoleK10es.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import NK10oTail VG10KA1o10 FeHoleK10os.
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


  Lemma pk1 : piece SV argH ISP fs kc1a1_hs301 TTK.
  Proof.
    apply (HAChain.hole_compose SV argH ISP fs kc1a1_hs301 fiendk1a1 TTK); [vm_compute; lia | exact TTK_agree | exact (FI8HoleK1A1.fi_hole_k1a1 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HAParity.piece_parity SV argH ISP fs fiendk1a1 TTK
      (HAJoin.piece_svg_all SV argH ISP fs NK1eTail.PALL _ TTK (fun _ => I)
        (VG1KA1e1.vtail_a1e1 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit NK1eTail.PALL NK1eTail.PALL_agree TTK TTK_agree TTK_nil
           (NK1eTail.tail_g1t012e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (FeHoleK1e.fe_hole_k1e sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleK1ec.fe_hole_k1ec sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleK1es.fe_hole_k1es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG NK1eTail.PALL SV) argH ISP fs (with_facts fiendk1a1 [par_even]) TTK))
      (HAJoin.piece_svg_all SV argH ISP fs NK1oTail.PALL _ TTK (fun _ => I)
        (VG1KA1o1.vtail_a1o1 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit NK1oTail.PALL NK1oTail.PALL_agree TTK TTK_agree TTK_nil
           (NK1oTail.tail_g1t012o sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (FeHoleK1o.fe_hole_k1o sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleK1oc.fe_hole_k1oc sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleK1os.fe_hole_k1os sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG NK1oTail.PALL SV) argH ISP fs (with_facts fiendk1a1 [par_odd]) TTK))).
  Qed.
  Lemma pk2 : piece SV argH ISP fs kc2a1_hs302 TTK.
  Proof.
    apply (HAChain.hole_compose SV argH ISP fs kc2a1_hs302 fiendk2a1 TTK); [vm_compute; lia | exact TTK_agree | exact (FI8HoleK2A1.fi_hole_k2a1 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HAParity.piece_parity SV argH ISP fs fiendk2a1 TTK
      (HAJoin.piece_svg_all SV argH ISP fs NK2eTail.PALL _ TTK (fun _ => I)
        (VG2KA1e2.vtail_a1e2 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit NK2eTail.PALL NK2eTail.PALL_agree TTK TTK_agree TTK_nil
           (NK2eTail.tail_g2t012e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (FeHoleK2es.fe_hole_k2es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG NK2eTail.PALL SV) argH ISP fs (with_facts fiendk2a1 [par_even]) TTK))
      (HAJoin.piece_svg_all SV argH ISP fs NK2oTail.PALL _ TTK (fun _ => I)
        (VG2KA1o2.vtail_a1o2 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit NK2oTail.PALL NK2oTail.PALL_agree TTK TTK_agree TTK_nil
           (NK2oTail.tail_g2t012o sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (FeHoleK2os.fe_hole_k2os sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG NK2oTail.PALL SV) argH ISP fs (with_facts fiendk2a1 [par_odd]) TTK))).
  Qed.
  Lemma pk3 : piece SV argH ISP fs kc3a1_hs303 TTK.
  Proof.
    apply (HAChain.hole_compose SV argH ISP fs kc3a1_hs303 fiendk3a1 TTK); [vm_compute; lia | exact TTK_agree | exact (FI8HoleK3A1.fi_hole_k3a1 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HAParity.piece_parity SV argH ISP fs fiendk3a1 TTK
      (HAJoin.piece_svg_all SV argH ISP fs NK3eTail.PALL _ TTK (fun _ => I)
        (VG3KA1e3.vtail_a1e3 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit NK3eTail.PALL NK3eTail.PALL_agree TTK TTK_agree TTK_nil
           (NK3eTail.tail_g3t012e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (FeHoleK3es.fe_hole_k3es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG NK3eTail.PALL SV) argH ISP fs (with_facts fiendk3a1 [par_even]) TTK))
      (HAJoin.piece_svg_all SV argH ISP fs NK3oTail.PALL _ TTK (fun _ => I)
        (VG3KA1o3.vtail_a1o3 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit NK3oTail.PALL NK3oTail.PALL_agree TTK TTK_agree TTK_nil
           (NK3oTail.tail_g3t012o sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (FeHoleK3os.fe_hole_k3os sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG NK3oTail.PALL SV) argH ISP fs (with_facts fiendk3a1 [par_odd]) TTK))).
  Qed.
  Lemma pk4 : piece SV argH ISP fs kc4a1_hs304 TTK.
  Proof.
    apply (HAChain.hole_compose SV argH ISP fs kc4a1_hs304 fiendk4a1 TTK); [vm_compute; lia | exact TTK_agree | exact (FI8HoleK4A1.fi_hole_k4a1 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HAParity.piece_parity SV argH ISP fs fiendk4a1 TTK
      (HAJoin.piece_svg_all SV argH ISP fs NK4eTail.PALL _ TTK (fun _ => I)
        (VG4KA1e4.vtail_a1e4 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit NK4eTail.PALL NK4eTail.PALL_agree TTK TTK_agree TTK_nil
           (NK4eTail.tail_g4t012e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (FeHoleK4es.fe_hole_k4es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG NK4eTail.PALL SV) argH ISP fs (with_facts fiendk4a1 [par_even]) TTK))
      (HAJoin.piece_svg_all SV argH ISP fs NK4oTail.PALL _ TTK (fun _ => I)
        (VG4KA1o4.vtail_a1o4 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit NK4oTail.PALL NK4oTail.PALL_agree TTK TTK_agree TTK_nil
           (NK4oTail.tail_g4t012o sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (FeHoleK4os.fe_hole_k4os sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG NK4oTail.PALL SV) argH ISP fs (with_facts fiendk4a1 [par_odd]) TTK))).
  Qed.
  Lemma pk5 : piece SV argH ISP fs kc5a1_hs305 TTK.
  Proof.
    apply (HAChain.hole_compose SV argH ISP fs kc5a1_hs305 fiendk5a1 TTK); [vm_compute; lia | exact TTK_agree | exact (FI8HoleK5A1.fi_hole_k5a1 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HAParity.piece_parity SV argH ISP fs fiendk5a1 TTK
      (HAJoin.piece_svg_all SV argH ISP fs NK5eTail.PALL _ TTK (fun _ => I)
        (VG5KA1e5.vtail_a1e5 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit NK5eTail.PALL NK5eTail.PALL_agree TTK TTK_agree TTK_nil
           (NK5eTail.tail_g5t012e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (FeHoleK5es.fe_hole_k5es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG NK5eTail.PALL SV) argH ISP fs (with_facts fiendk5a1 [par_even]) TTK))
      (HAJoin.piece_svg_all SV argH ISP fs NK5oTail.PALL _ TTK (fun _ => I)
        (VG5KA1o5.vtail_a1o5 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit NK5oTail.PALL NK5oTail.PALL_agree TTK TTK_agree TTK_nil
           (NK5oTail.tail_g5t012o sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (FeHoleK5os.fe_hole_k5os sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG NK5oTail.PALL SV) argH ISP fs (with_facts fiendk5a1 [par_odd]) TTK))).
  Qed.
  Lemma pk6 : piece SV argH ISP fs kc6a1_hs306 TTK.
  Proof.
    apply (HAChain.hole_compose SV argH ISP fs kc6a1_hs306 fiendk6a1 TTK); [vm_compute; lia | exact TTK_agree | exact (FI8HoleK6A1.fi_hole_k6a1 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HAParity.piece_parity SV argH ISP fs fiendk6a1 TTK
      (HAJoin.piece_svg_all SV argH ISP fs NK6eTail.PALL _ TTK (fun _ => I)
        (VG6KA1e6.vtail_a1e6 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit NK6eTail.PALL NK6eTail.PALL_agree TTK TTK_agree TTK_nil
           (NK6eTail.tail_g6t012e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (FeHoleK6es.fe_hole_k6es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG NK6eTail.PALL SV) argH ISP fs (with_facts fiendk6a1 [par_even]) TTK))
      (HAJoin.piece_svg_all SV argH ISP fs NK6oTail.PALL _ TTK (fun _ => I)
        (VG6KA1o6.vtail_a1o6 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit NK6oTail.PALL NK6oTail.PALL_agree TTK TTK_agree TTK_nil
           (NK6oTail.tail_g6t012o sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (FeHoleK6os.fe_hole_k6os sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG NK6oTail.PALL SV) argH ISP fs (with_facts fiendk6a1 [par_odd]) TTK))).
  Qed.
  Lemma pk7 : piece SV argH ISP fs kc7a1_hs307 TTK.
  Proof.
    apply (HAChain.hole_compose SV argH ISP fs kc7a1_hs307 fiendk7a1 TTK); [vm_compute; lia | exact TTK_agree | exact (FI8HoleK7A1.fi_hole_k7a1 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HAParity.piece_parity SV argH ISP fs fiendk7a1 TTK
      (HAJoin.piece_svg_all SV argH ISP fs NK7eTail.PALL _ TTK (fun _ => I)
        (VG7KA1e7.vtail_a1e7 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit NK7eTail.PALL NK7eTail.PALL_agree TTK TTK_agree TTK_nil
           (NK7eTail.tail_g7t012e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (FeHoleK7es.fe_hole_k7es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG NK7eTail.PALL SV) argH ISP fs (with_facts fiendk7a1 [par_even]) TTK))
      (HAJoin.piece_svg_all SV argH ISP fs NK7oTail.PALL _ TTK (fun _ => I)
        (VG7KA1o7.vtail_a1o7 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit NK7oTail.PALL NK7oTail.PALL_agree TTK TTK_agree TTK_nil
           (NK7oTail.tail_g7t012o sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (FeHoleK7os.fe_hole_k7os sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG NK7oTail.PALL SV) argH ISP fs (with_facts fiendk7a1 [par_odd]) TTK))).
  Qed.
  Lemma pk8 : piece SV argH ISP fs kc8a1_hs308 TTK.
  Proof.
    apply (HAChain.hole_compose SV argH ISP fs kc8a1_hs308 fiendk8a1 TTK); [vm_compute; lia | exact TTK_agree | exact (FI8HoleK8A1.fi_hole_k8a1 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HAParity.piece_parity SV argH ISP fs fiendk8a1 TTK
      (HAJoin.piece_svg_all SV argH ISP fs NK8eTail.PALL _ TTK (fun _ => I)
        (VG8KA1e8.vtail_a1e8 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit NK8eTail.PALL NK8eTail.PALL_agree TTK TTK_agree TTK_nil
           (NK8eTail.tail_g8t012e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (FeHoleK8es.fe_hole_k8es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG NK8eTail.PALL SV) argH ISP fs (with_facts fiendk8a1 [par_even]) TTK))
      (HAJoin.piece_svg_all SV argH ISP fs NK8oTail.PALL _ TTK (fun _ => I)
        (VG8KA1o8.vtail_a1o8 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit NK8oTail.PALL NK8oTail.PALL_agree TTK TTK_agree TTK_nil
           (NK8oTail.tail_g8t012o sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (FeHoleK8os.fe_hole_k8os sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG NK8oTail.PALL SV) argH ISP fs (with_facts fiendk8a1 [par_odd]) TTK))).
  Qed.
  Lemma pk9 : piece SV argH ISP fs kc9a1_hs309 TTK.
  Proof.
    apply (HAChain.hole_compose SV argH ISP fs kc9a1_hs309 fiendk9a1 TTK); [vm_compute; lia | exact TTK_agree | exact (FI8HoleK9A1.fi_hole_k9a1 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HAParity.piece_parity SV argH ISP fs fiendk9a1 TTK
      (HAJoin.piece_svg_all SV argH ISP fs NK9eTail.PALL _ TTK (fun _ => I)
        (VG9KA1e9.vtail_a1e9 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit NK9eTail.PALL NK9eTail.PALL_agree TTK TTK_agree TTK_nil
           (NK9eTail.tail_g9t012e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (FeHoleK9es.fe_hole_k9es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG NK9eTail.PALL SV) argH ISP fs (with_facts fiendk9a1 [par_even]) TTK))
      (HAJoin.piece_svg_all SV argH ISP fs NK9oTail.PALL _ TTK (fun _ => I)
        (VG9KA1o9.vtail_a1o9 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit NK9oTail.PALL NK9oTail.PALL_agree TTK TTK_agree TTK_nil
           (NK9oTail.tail_g9t012o sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (FeHoleK9os.fe_hole_k9os sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG NK9oTail.PALL SV) argH ISP fs (with_facts fiendk9a1 [par_odd]) TTK))).
  Qed.
  Lemma pk10 : piece SV argH ISP fs kc10a1_hs310 TTK.
  Proof.
    apply (HAChain.hole_compose SV argH ISP fs kc10a1_hs310 fiendk10a1 TTK); [vm_compute; lia | exact TTK_agree | exact (FI8HoleK10A1.fi_hole_k10a1 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HAParity.piece_parity SV argH ISP fs fiendk10a1 TTK
      (HAJoin.piece_svg_all SV argH ISP fs NK10eTail.PALL _ TTK (fun _ => I)
        (VG10KA1e10.vtail_a1e10 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit NK10eTail.PALL NK10eTail.PALL_agree TTK TTK_agree TTK_nil
           (NK10eTail.tail_g10t012e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (FeHoleK10es.fe_hole_k10es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG NK10eTail.PALL SV) argH ISP fs (with_facts fiendk10a1 [par_even]) TTK))
      (HAJoin.piece_svg_all SV argH ISP fs NK10oTail.PALL _ TTK (fun _ => I)
        (VG10KA1o10.vtail_a1o10 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit NK10oTail.PALL NK10oTail.PALL_agree TTK TTK_agree TTK_nil
           (NK10oTail.tail_g10t012o sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (FeHoleK10os.fe_hole_k10os sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG NK10oTail.PALL SV) argH ISP fs (with_facts fiendk10a1 [par_odd]) TTK))).
  Qed.

  Theorem hfi_a1_sec : forall k, 1 <= k <= 10 -> 2 ^ (15 + k) <= flen c <= 2 ^ (16 + k) - 1 -> piece SV argH ISP fs (HAKge1A1.fi_start_a1 k) TTK.
  Proof.
    intros k HK _.
    assert (HKk : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10) by lia.
    destruct HKk as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]; [exact pk1 | exact pk2 | exact pk3 | exact pk4 | exact pk5 | exact pk6 | exact pk7 | exact pk8 | exact pk9 | exact pk10].
  Qed.
End S.

Theorem hfi_a1 : forall sp rdraw brk0 argv envp fs uid hw, valid_sp sp -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp argv envp ->
  forall k, 1 <= k <= 10 -> 2 ^ (15 + k) <= flen (content_of argv fs) <= 2 ^ (16 + k) - 1 ->
  piece (SINVm HAPH sp rdraw brk0 argv envp uid hw (content_of argv fs)) (argH0 HAPH sp rdraw argv envp uid hw) (bv_unsigned sp) fs (HAKge1A1.fi_start_a1 k) TTK.
Proof. intros sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit. exact (hfi_a1_sec sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit). Qed.
