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
From OSSVerify.Proofs.openssl.hashtable.lib Require Import HAKge1B3.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import KC1B3Lit FIEndK1B3 KC2B3Lit FIEndK2B3 KC3B3Lit FIEndK3B3 KC4B3Lit FIEndK4B3 KC5B3Lit FIEndK5B3 KC6B3Lit FIEndK6B3 KC7B3Lit FIEndK7B3 KC8B3Lit FIEndK8B3 KC9B3Lit FIEndK9B3 KC10B3Lit FIEndK10B3.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import FI8HoleK1B3 FI8HoleK2B3 FI8HoleK3B3 FI8HoleK4B3 FI8HoleK5B3 FI8HoleK6B3 FI8HoleK7B3 FI8HoleK8B3 FI8HoleK9B3 FI8HoleK10B3.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import NH1eTail VG1KB3e1 FeHoleH1e FeHoleH1ec FeHoleH1es.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import NH1oTail VG1KB3o1 FeHoleH1o FeHoleH1oc FeHoleH1os.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import NH2eTail VG2KB3e2 FeHoleH2es.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import NH2oTail VG2KB3o2 FeHoleH2os.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import NH3eTail VG3KB3e3 FeHoleH3es.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import NH3oTail VG3KB3o3 FeHoleH3os.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import NH4eTail VG4KB3e4 FeHoleH4es.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import NH4oTail VG4KB3o4 FeHoleH4os.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import NH5eTail VG5KB3e5 FeHoleH5es.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import NH5oTail VG5KB3o5 FeHoleH5os.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import NH6eTail VG6KB3e6 FeHoleH6es.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import NH6oTail VG6KB3o6 FeHoleH6os.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import NH7eTail VG7KB3e7 FeHoleH7es.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import NH7oTail VG7KB3o7 FeHoleH7os.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import NH8eTail VG8KB3e8 FeHoleH8es.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import NH8oTail VG8KB3o8 FeHoleH8os.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import NH9eTail VG9KB3e9 FeHoleH9es.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import NH9oTail VG9KB3o9 FeHoleH9os.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import NH10eTail VG10KB3e10 FeHoleH10es.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import NH10oTail VG10KB3o10 FeHoleH10os.
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


  Lemma pk1 : piece SV argH ISP fs kc1b3_hs301 TTK.
  Proof.
    apply (HAChain.hole_compose SV argH ISP fs kc1b3_hs301 fiendk1b3 TTK); [vm_compute; lia | exact TTK_agree | exact (FI8HoleK1B3.fi_hole_k1b3 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HAParity.piece_parity SV argH ISP fs fiendk1b3 TTK
      (HAJoin.piece_svg_all SV argH ISP fs NH1eTail.PALL _ TTK (fun _ => I)
        (VG1KB3e1.vtail_b3e1 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit NH1eTail.PALL NH1eTail.PALL_agree TTK TTK_agree TTK_nil
           (NH1eTail.tail_g1t3e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (FeHoleH1e.fe_hole_h1e sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleH1ec.fe_hole_h1ec sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleH1es.fe_hole_h1es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG NH1eTail.PALL SV) argH ISP fs (with_facts fiendk1b3 [par_even]) TTK))
      (HAJoin.piece_svg_all SV argH ISP fs NH1oTail.PALL _ TTK (fun _ => I)
        (VG1KB3o1.vtail_b3o1 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit NH1oTail.PALL NH1oTail.PALL_agree TTK TTK_agree TTK_nil
           (NH1oTail.tail_g1t3o sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (FeHoleH1o.fe_hole_h1o sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleH1oc.fe_hole_h1oc sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleH1os.fe_hole_h1os sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG NH1oTail.PALL SV) argH ISP fs (with_facts fiendk1b3 [par_odd]) TTK))).
  Qed.
  Lemma pk2 : piece SV argH ISP fs kc2b3_hs302 TTK.
  Proof.
    apply (HAChain.hole_compose SV argH ISP fs kc2b3_hs302 fiendk2b3 TTK); [vm_compute; lia | exact TTK_agree | exact (FI8HoleK2B3.fi_hole_k2b3 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HAParity.piece_parity SV argH ISP fs fiendk2b3 TTK
      (HAJoin.piece_svg_all SV argH ISP fs NH2eTail.PALL _ TTK (fun _ => I)
        (VG2KB3e2.vtail_b3e2 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit NH2eTail.PALL NH2eTail.PALL_agree TTK TTK_agree TTK_nil
           (NH2eTail.tail_g2t3e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (FeHoleH2es.fe_hole_h2es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG NH2eTail.PALL SV) argH ISP fs (with_facts fiendk2b3 [par_even]) TTK))
      (HAJoin.piece_svg_all SV argH ISP fs NH2oTail.PALL _ TTK (fun _ => I)
        (VG2KB3o2.vtail_b3o2 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit NH2oTail.PALL NH2oTail.PALL_agree TTK TTK_agree TTK_nil
           (NH2oTail.tail_g2t3o sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (FeHoleH2os.fe_hole_h2os sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG NH2oTail.PALL SV) argH ISP fs (with_facts fiendk2b3 [par_odd]) TTK))).
  Qed.
  Lemma pk3 : piece SV argH ISP fs kc3b3_hs303 TTK.
  Proof.
    apply (HAChain.hole_compose SV argH ISP fs kc3b3_hs303 fiendk3b3 TTK); [vm_compute; lia | exact TTK_agree | exact (FI8HoleK3B3.fi_hole_k3b3 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HAParity.piece_parity SV argH ISP fs fiendk3b3 TTK
      (HAJoin.piece_svg_all SV argH ISP fs NH3eTail.PALL _ TTK (fun _ => I)
        (VG3KB3e3.vtail_b3e3 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit NH3eTail.PALL NH3eTail.PALL_agree TTK TTK_agree TTK_nil
           (NH3eTail.tail_g3t3e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (FeHoleH3es.fe_hole_h3es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG NH3eTail.PALL SV) argH ISP fs (with_facts fiendk3b3 [par_even]) TTK))
      (HAJoin.piece_svg_all SV argH ISP fs NH3oTail.PALL _ TTK (fun _ => I)
        (VG3KB3o3.vtail_b3o3 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit NH3oTail.PALL NH3oTail.PALL_agree TTK TTK_agree TTK_nil
           (NH3oTail.tail_g3t3o sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (FeHoleH3os.fe_hole_h3os sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG NH3oTail.PALL SV) argH ISP fs (with_facts fiendk3b3 [par_odd]) TTK))).
  Qed.
  Lemma pk4 : piece SV argH ISP fs kc4b3_hs304 TTK.
  Proof.
    apply (HAChain.hole_compose SV argH ISP fs kc4b3_hs304 fiendk4b3 TTK); [vm_compute; lia | exact TTK_agree | exact (FI8HoleK4B3.fi_hole_k4b3 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HAParity.piece_parity SV argH ISP fs fiendk4b3 TTK
      (HAJoin.piece_svg_all SV argH ISP fs NH4eTail.PALL _ TTK (fun _ => I)
        (VG4KB3e4.vtail_b3e4 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit NH4eTail.PALL NH4eTail.PALL_agree TTK TTK_agree TTK_nil
           (NH4eTail.tail_g4t3e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (FeHoleH4es.fe_hole_h4es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG NH4eTail.PALL SV) argH ISP fs (with_facts fiendk4b3 [par_even]) TTK))
      (HAJoin.piece_svg_all SV argH ISP fs NH4oTail.PALL _ TTK (fun _ => I)
        (VG4KB3o4.vtail_b3o4 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit NH4oTail.PALL NH4oTail.PALL_agree TTK TTK_agree TTK_nil
           (NH4oTail.tail_g4t3o sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (FeHoleH4os.fe_hole_h4os sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG NH4oTail.PALL SV) argH ISP fs (with_facts fiendk4b3 [par_odd]) TTK))).
  Qed.
  Lemma pk5 : piece SV argH ISP fs kc5b3_hs305 TTK.
  Proof.
    apply (HAChain.hole_compose SV argH ISP fs kc5b3_hs305 fiendk5b3 TTK); [vm_compute; lia | exact TTK_agree | exact (FI8HoleK5B3.fi_hole_k5b3 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HAParity.piece_parity SV argH ISP fs fiendk5b3 TTK
      (HAJoin.piece_svg_all SV argH ISP fs NH5eTail.PALL _ TTK (fun _ => I)
        (VG5KB3e5.vtail_b3e5 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit NH5eTail.PALL NH5eTail.PALL_agree TTK TTK_agree TTK_nil
           (NH5eTail.tail_g5t3e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (FeHoleH5es.fe_hole_h5es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG NH5eTail.PALL SV) argH ISP fs (with_facts fiendk5b3 [par_even]) TTK))
      (HAJoin.piece_svg_all SV argH ISP fs NH5oTail.PALL _ TTK (fun _ => I)
        (VG5KB3o5.vtail_b3o5 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit NH5oTail.PALL NH5oTail.PALL_agree TTK TTK_agree TTK_nil
           (NH5oTail.tail_g5t3o sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (FeHoleH5os.fe_hole_h5os sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG NH5oTail.PALL SV) argH ISP fs (with_facts fiendk5b3 [par_odd]) TTK))).
  Qed.
  Lemma pk6 : piece SV argH ISP fs kc6b3_hs306 TTK.
  Proof.
    apply (HAChain.hole_compose SV argH ISP fs kc6b3_hs306 fiendk6b3 TTK); [vm_compute; lia | exact TTK_agree | exact (FI8HoleK6B3.fi_hole_k6b3 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HAParity.piece_parity SV argH ISP fs fiendk6b3 TTK
      (HAJoin.piece_svg_all SV argH ISP fs NH6eTail.PALL _ TTK (fun _ => I)
        (VG6KB3e6.vtail_b3e6 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit NH6eTail.PALL NH6eTail.PALL_agree TTK TTK_agree TTK_nil
           (NH6eTail.tail_g6t3e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (FeHoleH6es.fe_hole_h6es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG NH6eTail.PALL SV) argH ISP fs (with_facts fiendk6b3 [par_even]) TTK))
      (HAJoin.piece_svg_all SV argH ISP fs NH6oTail.PALL _ TTK (fun _ => I)
        (VG6KB3o6.vtail_b3o6 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit NH6oTail.PALL NH6oTail.PALL_agree TTK TTK_agree TTK_nil
           (NH6oTail.tail_g6t3o sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (FeHoleH6os.fe_hole_h6os sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG NH6oTail.PALL SV) argH ISP fs (with_facts fiendk6b3 [par_odd]) TTK))).
  Qed.
  Lemma pk7 : piece SV argH ISP fs kc7b3_hs307 TTK.
  Proof.
    apply (HAChain.hole_compose SV argH ISP fs kc7b3_hs307 fiendk7b3 TTK); [vm_compute; lia | exact TTK_agree | exact (FI8HoleK7B3.fi_hole_k7b3 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HAParity.piece_parity SV argH ISP fs fiendk7b3 TTK
      (HAJoin.piece_svg_all SV argH ISP fs NH7eTail.PALL _ TTK (fun _ => I)
        (VG7KB3e7.vtail_b3e7 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit NH7eTail.PALL NH7eTail.PALL_agree TTK TTK_agree TTK_nil
           (NH7eTail.tail_g7t3e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (FeHoleH7es.fe_hole_h7es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG NH7eTail.PALL SV) argH ISP fs (with_facts fiendk7b3 [par_even]) TTK))
      (HAJoin.piece_svg_all SV argH ISP fs NH7oTail.PALL _ TTK (fun _ => I)
        (VG7KB3o7.vtail_b3o7 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit NH7oTail.PALL NH7oTail.PALL_agree TTK TTK_agree TTK_nil
           (NH7oTail.tail_g7t3o sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (FeHoleH7os.fe_hole_h7os sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG NH7oTail.PALL SV) argH ISP fs (with_facts fiendk7b3 [par_odd]) TTK))).
  Qed.
  Lemma pk8 : piece SV argH ISP fs kc8b3_hs308 TTK.
  Proof.
    apply (HAChain.hole_compose SV argH ISP fs kc8b3_hs308 fiendk8b3 TTK); [vm_compute; lia | exact TTK_agree | exact (FI8HoleK8B3.fi_hole_k8b3 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HAParity.piece_parity SV argH ISP fs fiendk8b3 TTK
      (HAJoin.piece_svg_all SV argH ISP fs NH8eTail.PALL _ TTK (fun _ => I)
        (VG8KB3e8.vtail_b3e8 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit NH8eTail.PALL NH8eTail.PALL_agree TTK TTK_agree TTK_nil
           (NH8eTail.tail_g8t3e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (FeHoleH8es.fe_hole_h8es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG NH8eTail.PALL SV) argH ISP fs (with_facts fiendk8b3 [par_even]) TTK))
      (HAJoin.piece_svg_all SV argH ISP fs NH8oTail.PALL _ TTK (fun _ => I)
        (VG8KB3o8.vtail_b3o8 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit NH8oTail.PALL NH8oTail.PALL_agree TTK TTK_agree TTK_nil
           (NH8oTail.tail_g8t3o sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (FeHoleH8os.fe_hole_h8os sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG NH8oTail.PALL SV) argH ISP fs (with_facts fiendk8b3 [par_odd]) TTK))).
  Qed.
  Lemma pk9 : piece SV argH ISP fs kc9b3_hs309 TTK.
  Proof.
    apply (HAChain.hole_compose SV argH ISP fs kc9b3_hs309 fiendk9b3 TTK); [vm_compute; lia | exact TTK_agree | exact (FI8HoleK9B3.fi_hole_k9b3 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HAParity.piece_parity SV argH ISP fs fiendk9b3 TTK
      (HAJoin.piece_svg_all SV argH ISP fs NH9eTail.PALL _ TTK (fun _ => I)
        (VG9KB3e9.vtail_b3e9 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit NH9eTail.PALL NH9eTail.PALL_agree TTK TTK_agree TTK_nil
           (NH9eTail.tail_g9t3e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (FeHoleH9es.fe_hole_h9es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG NH9eTail.PALL SV) argH ISP fs (with_facts fiendk9b3 [par_even]) TTK))
      (HAJoin.piece_svg_all SV argH ISP fs NH9oTail.PALL _ TTK (fun _ => I)
        (VG9KB3o9.vtail_b3o9 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit NH9oTail.PALL NH9oTail.PALL_agree TTK TTK_agree TTK_nil
           (NH9oTail.tail_g9t3o sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (FeHoleH9os.fe_hole_h9os sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG NH9oTail.PALL SV) argH ISP fs (with_facts fiendk9b3 [par_odd]) TTK))).
  Qed.
  Lemma pk10 : piece SV argH ISP fs kc10b3_hs310 TTK.
  Proof.
    apply (HAChain.hole_compose SV argH ISP fs kc10b3_hs310 fiendk10b3 TTK); [vm_compute; lia | exact TTK_agree | exact (FI8HoleK10B3.fi_hole_k10b3 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HAParity.piece_parity SV argH ISP fs fiendk10b3 TTK
      (HAJoin.piece_svg_all SV argH ISP fs NH10eTail.PALL _ TTK (fun _ => I)
        (VG10KB3e10.vtail_b3e10 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit NH10eTail.PALL NH10eTail.PALL_agree TTK TTK_agree TTK_nil
           (NH10eTail.tail_g10t3e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (FeHoleH10es.fe_hole_h10es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG NH10eTail.PALL SV) argH ISP fs (with_facts fiendk10b3 [par_even]) TTK))
      (HAJoin.piece_svg_all SV argH ISP fs NH10oTail.PALL _ TTK (fun _ => I)
        (VG10KB3o10.vtail_b3o10 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit NH10oTail.PALL NH10oTail.PALL_agree TTK TTK_agree TTK_nil
           (NH10oTail.tail_g10t3o sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (FeHoleH10os.fe_hole_h10os sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG NH10oTail.PALL SV) argH ISP fs (with_facts fiendk10b3 [par_odd]) TTK))).
  Qed.

  Theorem hfi_b3_sec : forall k, 1 <= k <= 10 -> 2 ^ (15 + k) <= flen c <= 2 ^ (16 + k) - 1 -> piece SV argH ISP fs (HAKge1B3.fi_start_b3 k) TTK.
  Proof.
    intros k HK _.
    assert (HKk : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10) by lia.
    destruct HKk as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]; [exact pk1 | exact pk2 | exact pk3 | exact pk4 | exact pk5 | exact pk6 | exact pk7 | exact pk8 | exact pk9 | exact pk10].
  Qed.
End S.

Theorem hfi_b3 : forall sp rdraw brk0 argv envp fs uid hw, valid_sp sp -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp argv envp ->
  forall k, 1 <= k <= 10 -> 2 ^ (15 + k) <= flen (content_of argv fs) <= 2 ^ (16 + k) - 1 ->
  piece (SINVm HAPH sp rdraw brk0 argv envp uid hw (content_of argv fs)) (argH0 HAPH sp rdraw argv envp uid hw) (bv_unsigned sp) fs (HAKge1B3.fi_start_b3 k) TTK.
Proof. intros sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit. exact (hfi_b3_sec sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit). Qed.
