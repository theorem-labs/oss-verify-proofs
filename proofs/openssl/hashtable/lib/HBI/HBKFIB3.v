(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Namei.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Open.
From OssFuzzTheorems.openssl.hashtable.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import PropExec CatExec ShapeAlg AgentLib AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanNodesIO AsanInit.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import ClaVerdict Spec SpecGen HTSpec ShapeLaws.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CxRel CxPlan CxPlanSound CxOfAps CxReblob HBPlanImage HBAtable HBChain HBCheckG HBParity HBJoin HBTgtGlue HBOpenDefs HBHdrDefs HBFullDefs.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import HBKge1B3.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BKC1B3Lit BFIEndK1B3 BKC2B3Lit BFIEndK2B3 BKC3B3Lit BFIEndK3B3 BKC4B3Lit BFIEndK4B3 BKC5B3Lit BFIEndK5B3 BKC6B3Lit BFIEndK6B3 BKC7B3Lit BFIEndK7B3 BKC8B3Lit BFIEndK8B3 BKC9B3Lit BFIEndK9B3 BKC10B3Lit BFIEndK10B3.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BFI8HoleK1B3 BFI8HoleK2B3 BFI8HoleK3B3 BFI8HoleK4B3 BFI8HoleK5B3 BFI8HoleK6B3 BFI8HoleK7B3 BFI8HoleK8B3 BFI8HoleK9B3 BFI8HoleK10B3.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNH1eTail BVG1KB3e1 BFeHoleH1e BFeHoleH1ec BFeHoleH1es.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNH1oTail BVG1KB3o1 BFeHoleH1o BFeHoleH1oc BFeHoleH1os.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNH2eTail BVG2KB3e2 BFeHoleH2es.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNH2oTail BVG2KB3o2 BFeHoleH2os.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNH3eTail BVG3KB3e3 BFeHoleH3es.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNH3oTail BVG3KB3o3 BFeHoleH3os.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNH4eTail BVG4KB3e4 BFeHoleH4es.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNH4oTail BVG4KB3o4 BFeHoleH4os.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNH5eTail BVG5KB3e5 BFeHoleH5es.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNH5oTail BVG5KB3o5 BFeHoleH5os.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNH6eTail BVG6KB3e6 BFeHoleH6es.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNH6oTail BVG6KB3o6 BFeHoleH6os.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNH7eTail BVG7KB3e7 BFeHoleH7es.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNH7oTail BVG7KB3o7 BFeHoleH7os.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNH8eTail BVG8KB3e8 BFeHoleH8es.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNH8oTail BVG8KB3o8 BFeHoleH8os.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNH9eTail BVG9KB3e9 BFeHoleH9es.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNH9oTail BVG9KB3o9 BFeHoleH9os.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNH10eTail BVG10KB3e10 BFeHoleH10es.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNH10oTail BVG10KB3o10 BFeHoleH10os.
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
    apply (HBChain.hole_compose SV argH ISP fs kc1b3_hs301 fiendk1b3 TTK); [vm_compute; lia | exact TTK_agree | exact (BFI8HoleK1B3.fi_hole_k1b3 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HBParity.piece_parity SV argH ISP fs fiendk1b3 TTK
      (HBJoin.piece_svg_all SV argH ISP fs BNH1eTail.PALL _ TTK (fun _ => I)
        (BVG1KB3e1.vtail_b3e1 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNH1eTail.PALL BNH1eTail.PALL_agree TTK TTK_agree TTK_nil
           (BNH1eTail.tail_g1t3e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleH1e.fe_hole_h1e sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleH1ec.fe_hole_h1ec sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleH1es.fe_hole_h1es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNH1eTail.PALL SV) argH ISP fs (with_facts fiendk1b3 [par_even]) TTK))
      (HBJoin.piece_svg_all SV argH ISP fs BNH1oTail.PALL _ TTK (fun _ => I)
        (BVG1KB3o1.vtail_b3o1 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNH1oTail.PALL BNH1oTail.PALL_agree TTK TTK_agree TTK_nil
           (BNH1oTail.tail_g1t3o sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleH1o.fe_hole_h1o sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleH1oc.fe_hole_h1oc sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleH1os.fe_hole_h1os sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNH1oTail.PALL SV) argH ISP fs (with_facts fiendk1b3 [par_odd]) TTK))).
  Qed.
  Lemma pk2 : piece SV argH ISP fs kc2b3_hs302 TTK.
  Proof.
    apply (HBChain.hole_compose SV argH ISP fs kc2b3_hs302 fiendk2b3 TTK); [vm_compute; lia | exact TTK_agree | exact (BFI8HoleK2B3.fi_hole_k2b3 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HBParity.piece_parity SV argH ISP fs fiendk2b3 TTK
      (HBJoin.piece_svg_all SV argH ISP fs BNH2eTail.PALL _ TTK (fun _ => I)
        (BVG2KB3e2.vtail_b3e2 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNH2eTail.PALL BNH2eTail.PALL_agree TTK TTK_agree TTK_nil
           (BNH2eTail.tail_g2t3e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleH2es.fe_hole_h2es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNH2eTail.PALL SV) argH ISP fs (with_facts fiendk2b3 [par_even]) TTK))
      (HBJoin.piece_svg_all SV argH ISP fs BNH2oTail.PALL _ TTK (fun _ => I)
        (BVG2KB3o2.vtail_b3o2 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNH2oTail.PALL BNH2oTail.PALL_agree TTK TTK_agree TTK_nil
           (BNH2oTail.tail_g2t3o sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleH2os.fe_hole_h2os sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNH2oTail.PALL SV) argH ISP fs (with_facts fiendk2b3 [par_odd]) TTK))).
  Qed.
  Lemma pk3 : piece SV argH ISP fs kc3b3_hs303 TTK.
  Proof.
    apply (HBChain.hole_compose SV argH ISP fs kc3b3_hs303 fiendk3b3 TTK); [vm_compute; lia | exact TTK_agree | exact (BFI8HoleK3B3.fi_hole_k3b3 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HBParity.piece_parity SV argH ISP fs fiendk3b3 TTK
      (HBJoin.piece_svg_all SV argH ISP fs BNH3eTail.PALL _ TTK (fun _ => I)
        (BVG3KB3e3.vtail_b3e3 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNH3eTail.PALL BNH3eTail.PALL_agree TTK TTK_agree TTK_nil
           (BNH3eTail.tail_g3t3e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleH3es.fe_hole_h3es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNH3eTail.PALL SV) argH ISP fs (with_facts fiendk3b3 [par_even]) TTK))
      (HBJoin.piece_svg_all SV argH ISP fs BNH3oTail.PALL _ TTK (fun _ => I)
        (BVG3KB3o3.vtail_b3o3 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNH3oTail.PALL BNH3oTail.PALL_agree TTK TTK_agree TTK_nil
           (BNH3oTail.tail_g3t3o sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleH3os.fe_hole_h3os sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNH3oTail.PALL SV) argH ISP fs (with_facts fiendk3b3 [par_odd]) TTK))).
  Qed.
  Lemma pk4 : piece SV argH ISP fs kc4b3_hs304 TTK.
  Proof.
    apply (HBChain.hole_compose SV argH ISP fs kc4b3_hs304 fiendk4b3 TTK); [vm_compute; lia | exact TTK_agree | exact (BFI8HoleK4B3.fi_hole_k4b3 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HBParity.piece_parity SV argH ISP fs fiendk4b3 TTK
      (HBJoin.piece_svg_all SV argH ISP fs BNH4eTail.PALL _ TTK (fun _ => I)
        (BVG4KB3e4.vtail_b3e4 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNH4eTail.PALL BNH4eTail.PALL_agree TTK TTK_agree TTK_nil
           (BNH4eTail.tail_g4t3e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleH4es.fe_hole_h4es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNH4eTail.PALL SV) argH ISP fs (with_facts fiendk4b3 [par_even]) TTK))
      (HBJoin.piece_svg_all SV argH ISP fs BNH4oTail.PALL _ TTK (fun _ => I)
        (BVG4KB3o4.vtail_b3o4 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNH4oTail.PALL BNH4oTail.PALL_agree TTK TTK_agree TTK_nil
           (BNH4oTail.tail_g4t3o sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleH4os.fe_hole_h4os sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNH4oTail.PALL SV) argH ISP fs (with_facts fiendk4b3 [par_odd]) TTK))).
  Qed.
  Lemma pk5 : piece SV argH ISP fs kc5b3_hs305 TTK.
  Proof.
    apply (HBChain.hole_compose SV argH ISP fs kc5b3_hs305 fiendk5b3 TTK); [vm_compute; lia | exact TTK_agree | exact (BFI8HoleK5B3.fi_hole_k5b3 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HBParity.piece_parity SV argH ISP fs fiendk5b3 TTK
      (HBJoin.piece_svg_all SV argH ISP fs BNH5eTail.PALL _ TTK (fun _ => I)
        (BVG5KB3e5.vtail_b3e5 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNH5eTail.PALL BNH5eTail.PALL_agree TTK TTK_agree TTK_nil
           (BNH5eTail.tail_g5t3e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleH5es.fe_hole_h5es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNH5eTail.PALL SV) argH ISP fs (with_facts fiendk5b3 [par_even]) TTK))
      (HBJoin.piece_svg_all SV argH ISP fs BNH5oTail.PALL _ TTK (fun _ => I)
        (BVG5KB3o5.vtail_b3o5 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNH5oTail.PALL BNH5oTail.PALL_agree TTK TTK_agree TTK_nil
           (BNH5oTail.tail_g5t3o sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleH5os.fe_hole_h5os sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNH5oTail.PALL SV) argH ISP fs (with_facts fiendk5b3 [par_odd]) TTK))).
  Qed.
  Lemma pk6 : piece SV argH ISP fs kc6b3_hs306 TTK.
  Proof.
    apply (HBChain.hole_compose SV argH ISP fs kc6b3_hs306 fiendk6b3 TTK); [vm_compute; lia | exact TTK_agree | exact (BFI8HoleK6B3.fi_hole_k6b3 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HBParity.piece_parity SV argH ISP fs fiendk6b3 TTK
      (HBJoin.piece_svg_all SV argH ISP fs BNH6eTail.PALL _ TTK (fun _ => I)
        (BVG6KB3e6.vtail_b3e6 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNH6eTail.PALL BNH6eTail.PALL_agree TTK TTK_agree TTK_nil
           (BNH6eTail.tail_g6t3e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleH6es.fe_hole_h6es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNH6eTail.PALL SV) argH ISP fs (with_facts fiendk6b3 [par_even]) TTK))
      (HBJoin.piece_svg_all SV argH ISP fs BNH6oTail.PALL _ TTK (fun _ => I)
        (BVG6KB3o6.vtail_b3o6 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNH6oTail.PALL BNH6oTail.PALL_agree TTK TTK_agree TTK_nil
           (BNH6oTail.tail_g6t3o sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleH6os.fe_hole_h6os sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNH6oTail.PALL SV) argH ISP fs (with_facts fiendk6b3 [par_odd]) TTK))).
  Qed.
  Lemma pk7 : piece SV argH ISP fs kc7b3_hs307 TTK.
  Proof.
    apply (HBChain.hole_compose SV argH ISP fs kc7b3_hs307 fiendk7b3 TTK); [vm_compute; lia | exact TTK_agree | exact (BFI8HoleK7B3.fi_hole_k7b3 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HBParity.piece_parity SV argH ISP fs fiendk7b3 TTK
      (HBJoin.piece_svg_all SV argH ISP fs BNH7eTail.PALL _ TTK (fun _ => I)
        (BVG7KB3e7.vtail_b3e7 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNH7eTail.PALL BNH7eTail.PALL_agree TTK TTK_agree TTK_nil
           (BNH7eTail.tail_g7t3e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleH7es.fe_hole_h7es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNH7eTail.PALL SV) argH ISP fs (with_facts fiendk7b3 [par_even]) TTK))
      (HBJoin.piece_svg_all SV argH ISP fs BNH7oTail.PALL _ TTK (fun _ => I)
        (BVG7KB3o7.vtail_b3o7 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNH7oTail.PALL BNH7oTail.PALL_agree TTK TTK_agree TTK_nil
           (BNH7oTail.tail_g7t3o sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleH7os.fe_hole_h7os sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNH7oTail.PALL SV) argH ISP fs (with_facts fiendk7b3 [par_odd]) TTK))).
  Qed.
  Lemma pk8 : piece SV argH ISP fs kc8b3_hs308 TTK.
  Proof.
    apply (HBChain.hole_compose SV argH ISP fs kc8b3_hs308 fiendk8b3 TTK); [vm_compute; lia | exact TTK_agree | exact (BFI8HoleK8B3.fi_hole_k8b3 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HBParity.piece_parity SV argH ISP fs fiendk8b3 TTK
      (HBJoin.piece_svg_all SV argH ISP fs BNH8eTail.PALL _ TTK (fun _ => I)
        (BVG8KB3e8.vtail_b3e8 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNH8eTail.PALL BNH8eTail.PALL_agree TTK TTK_agree TTK_nil
           (BNH8eTail.tail_g8t3e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleH8es.fe_hole_h8es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNH8eTail.PALL SV) argH ISP fs (with_facts fiendk8b3 [par_even]) TTK))
      (HBJoin.piece_svg_all SV argH ISP fs BNH8oTail.PALL _ TTK (fun _ => I)
        (BVG8KB3o8.vtail_b3o8 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNH8oTail.PALL BNH8oTail.PALL_agree TTK TTK_agree TTK_nil
           (BNH8oTail.tail_g8t3o sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleH8os.fe_hole_h8os sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNH8oTail.PALL SV) argH ISP fs (with_facts fiendk8b3 [par_odd]) TTK))).
  Qed.
  Lemma pk9 : piece SV argH ISP fs kc9b3_hs309 TTK.
  Proof.
    apply (HBChain.hole_compose SV argH ISP fs kc9b3_hs309 fiendk9b3 TTK); [vm_compute; lia | exact TTK_agree | exact (BFI8HoleK9B3.fi_hole_k9b3 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HBParity.piece_parity SV argH ISP fs fiendk9b3 TTK
      (HBJoin.piece_svg_all SV argH ISP fs BNH9eTail.PALL _ TTK (fun _ => I)
        (BVG9KB3e9.vtail_b3e9 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNH9eTail.PALL BNH9eTail.PALL_agree TTK TTK_agree TTK_nil
           (BNH9eTail.tail_g9t3e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleH9es.fe_hole_h9es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNH9eTail.PALL SV) argH ISP fs (with_facts fiendk9b3 [par_even]) TTK))
      (HBJoin.piece_svg_all SV argH ISP fs BNH9oTail.PALL _ TTK (fun _ => I)
        (BVG9KB3o9.vtail_b3o9 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNH9oTail.PALL BNH9oTail.PALL_agree TTK TTK_agree TTK_nil
           (BNH9oTail.tail_g9t3o sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleH9os.fe_hole_h9os sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNH9oTail.PALL SV) argH ISP fs (with_facts fiendk9b3 [par_odd]) TTK))).
  Qed.
  Lemma pk10 : piece SV argH ISP fs kc10b3_hs310 TTK.
  Proof.
    apply (HBChain.hole_compose SV argH ISP fs kc10b3_hs310 fiendk10b3 TTK); [vm_compute; lia | exact TTK_agree | exact (BFI8HoleK10B3.fi_hole_k10b3 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HBParity.piece_parity SV argH ISP fs fiendk10b3 TTK
      (HBJoin.piece_svg_all SV argH ISP fs BNH10eTail.PALL _ TTK (fun _ => I)
        (BVG10KB3e10.vtail_b3e10 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNH10eTail.PALL BNH10eTail.PALL_agree TTK TTK_agree TTK_nil
           (BNH10eTail.tail_g10t3e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleH10es.fe_hole_h10es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNH10eTail.PALL SV) argH ISP fs (with_facts fiendk10b3 [par_even]) TTK))
      (HBJoin.piece_svg_all SV argH ISP fs BNH10oTail.PALL _ TTK (fun _ => I)
        (BVG10KB3o10.vtail_b3o10 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNH10oTail.PALL BNH10oTail.PALL_agree TTK TTK_agree TTK_nil
           (BNH10oTail.tail_g10t3o sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleH10os.fe_hole_h10os sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNH10oTail.PALL SV) argH ISP fs (with_facts fiendk10b3 [par_odd]) TTK))).
  Qed.

  Theorem hfi_b3_sec : forall k, 1 <= k <= 10 -> 2 ^ (15 + k) <= flen c <= 2 ^ (16 + k) - 1 -> piece SV argH ISP fs (HBKge1B3.fi_start_b3 k) TTK.
  Proof.
    intros k HK _.
    assert (HKk : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10) by lia.
    destruct HKk as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]; [exact pk1 | exact pk2 | exact pk3 | exact pk4 | exact pk5 | exact pk6 | exact pk7 | exact pk8 | exact pk9 | exact pk10].
  Qed.
End S.

Theorem hfi_b3 : forall sp rdraw brk0 argv envp fs uid hw, valid_sp sp -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp argv envp ->
  forall k, 1 <= k <= 10 -> 2 ^ (15 + k) <= flen (content_of argv fs) <= 2 ^ (16 + k) - 1 ->
  piece (SINVm HAPH sp rdraw brk0 argv envp uid hw (content_of argv fs)) (argH0 HAPH sp rdraw argv envp uid hw) (bv_unsigned sp) fs (HBKge1B3.fi_start_b3 k) TTK.
Proof. intros sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit. exact (hfi_b3_sec sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit). Qed.
