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
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import HBKge1A1.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BKC1A1Lit BFIEndK1A1 BKC2A1Lit BFIEndK2A1 BKC3A1Lit BFIEndK3A1 BKC4A1Lit BFIEndK4A1 BKC5A1Lit BFIEndK5A1 BKC6A1Lit BFIEndK6A1 BKC7A1Lit BFIEndK7A1 BKC8A1Lit BFIEndK8A1 BKC9A1Lit BFIEndK9A1 BKC10A1Lit BFIEndK10A1.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BFI8HoleK1A1 BFI8HoleK2A1 BFI8HoleK3A1 BFI8HoleK4A1 BFI8HoleK5A1 BFI8HoleK6A1 BFI8HoleK7A1 BFI8HoleK8A1 BFI8HoleK9A1 BFI8HoleK10A1.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNK1eTail BVG1KA1e1 BFeHoleK1e BFeHoleK1ec BFeHoleK1es.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNK1oTail BVG1KA1o1 BFeHoleK1o BFeHoleK1oc BFeHoleK1os.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNK2eTail BVG2KA1e2 BFeHoleK2es.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNK2oTail BVG2KA1o2 BFeHoleK2os.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNK3eTail BVG3KA1e3 BFeHoleK3es.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNK3oTail BVG3KA1o3 BFeHoleK3os.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNK4eTail BVG4KA1e4 BFeHoleK4es.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNK4oTail BVG4KA1o4 BFeHoleK4os.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNK5eTail BVG5KA1e5 BFeHoleK5es.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNK5oTail BVG5KA1o5 BFeHoleK5os.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNK6eTail BVG6KA1e6 BFeHoleK6es.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNK6oTail BVG6KA1o6 BFeHoleK6os.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNK7eTail BVG7KA1e7 BFeHoleK7es.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNK7oTail BVG7KA1o7 BFeHoleK7os.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNK8eTail BVG8KA1e8 BFeHoleK8es.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNK8oTail BVG8KA1o8 BFeHoleK8os.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNK9eTail BVG9KA1e9 BFeHoleK9es.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNK9oTail BVG9KA1o9 BFeHoleK9os.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNK10eTail BVG10KA1e10 BFeHoleK10es.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNK10oTail BVG10KA1o10 BFeHoleK10os.
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
    apply (HBChain.hole_compose SV argH ISP fs kc1a1_hs301 fiendk1a1 TTK); [vm_compute; lia | exact TTK_agree | exact (BFI8HoleK1A1.fi_hole_k1a1 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HBParity.piece_parity SV argH ISP fs fiendk1a1 TTK
      (HBJoin.piece_svg_all SV argH ISP fs BNK1eTail.PALL _ TTK (fun _ => I)
        (BVG1KA1e1.vtail_a1e1 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNK1eTail.PALL BNK1eTail.PALL_agree TTK TTK_agree TTK_nil
           (BNK1eTail.tail_g1t012e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleK1e.fe_hole_k1e sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleK1ec.fe_hole_k1ec sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleK1es.fe_hole_k1es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNK1eTail.PALL SV) argH ISP fs (with_facts fiendk1a1 [par_even]) TTK))
      (HBJoin.piece_svg_all SV argH ISP fs BNK1oTail.PALL _ TTK (fun _ => I)
        (BVG1KA1o1.vtail_a1o1 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNK1oTail.PALL BNK1oTail.PALL_agree TTK TTK_agree TTK_nil
           (BNK1oTail.tail_g1t012o sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleK1o.fe_hole_k1o sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleK1oc.fe_hole_k1oc sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleK1os.fe_hole_k1os sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNK1oTail.PALL SV) argH ISP fs (with_facts fiendk1a1 [par_odd]) TTK))).
  Qed.
  Lemma pk2 : piece SV argH ISP fs kc2a1_hs302 TTK.
  Proof.
    apply (HBChain.hole_compose SV argH ISP fs kc2a1_hs302 fiendk2a1 TTK); [vm_compute; lia | exact TTK_agree | exact (BFI8HoleK2A1.fi_hole_k2a1 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HBParity.piece_parity SV argH ISP fs fiendk2a1 TTK
      (HBJoin.piece_svg_all SV argH ISP fs BNK2eTail.PALL _ TTK (fun _ => I)
        (BVG2KA1e2.vtail_a1e2 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNK2eTail.PALL BNK2eTail.PALL_agree TTK TTK_agree TTK_nil
           (BNK2eTail.tail_g2t012e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleK2es.fe_hole_k2es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNK2eTail.PALL SV) argH ISP fs (with_facts fiendk2a1 [par_even]) TTK))
      (HBJoin.piece_svg_all SV argH ISP fs BNK2oTail.PALL _ TTK (fun _ => I)
        (BVG2KA1o2.vtail_a1o2 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNK2oTail.PALL BNK2oTail.PALL_agree TTK TTK_agree TTK_nil
           (BNK2oTail.tail_g2t012o sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleK2os.fe_hole_k2os sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNK2oTail.PALL SV) argH ISP fs (with_facts fiendk2a1 [par_odd]) TTK))).
  Qed.
  Lemma pk3 : piece SV argH ISP fs kc3a1_hs303 TTK.
  Proof.
    apply (HBChain.hole_compose SV argH ISP fs kc3a1_hs303 fiendk3a1 TTK); [vm_compute; lia | exact TTK_agree | exact (BFI8HoleK3A1.fi_hole_k3a1 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HBParity.piece_parity SV argH ISP fs fiendk3a1 TTK
      (HBJoin.piece_svg_all SV argH ISP fs BNK3eTail.PALL _ TTK (fun _ => I)
        (BVG3KA1e3.vtail_a1e3 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNK3eTail.PALL BNK3eTail.PALL_agree TTK TTK_agree TTK_nil
           (BNK3eTail.tail_g3t012e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleK3es.fe_hole_k3es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNK3eTail.PALL SV) argH ISP fs (with_facts fiendk3a1 [par_even]) TTK))
      (HBJoin.piece_svg_all SV argH ISP fs BNK3oTail.PALL _ TTK (fun _ => I)
        (BVG3KA1o3.vtail_a1o3 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNK3oTail.PALL BNK3oTail.PALL_agree TTK TTK_agree TTK_nil
           (BNK3oTail.tail_g3t012o sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleK3os.fe_hole_k3os sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNK3oTail.PALL SV) argH ISP fs (with_facts fiendk3a1 [par_odd]) TTK))).
  Qed.
  Lemma pk4 : piece SV argH ISP fs kc4a1_hs304 TTK.
  Proof.
    apply (HBChain.hole_compose SV argH ISP fs kc4a1_hs304 fiendk4a1 TTK); [vm_compute; lia | exact TTK_agree | exact (BFI8HoleK4A1.fi_hole_k4a1 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HBParity.piece_parity SV argH ISP fs fiendk4a1 TTK
      (HBJoin.piece_svg_all SV argH ISP fs BNK4eTail.PALL _ TTK (fun _ => I)
        (BVG4KA1e4.vtail_a1e4 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNK4eTail.PALL BNK4eTail.PALL_agree TTK TTK_agree TTK_nil
           (BNK4eTail.tail_g4t012e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleK4es.fe_hole_k4es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNK4eTail.PALL SV) argH ISP fs (with_facts fiendk4a1 [par_even]) TTK))
      (HBJoin.piece_svg_all SV argH ISP fs BNK4oTail.PALL _ TTK (fun _ => I)
        (BVG4KA1o4.vtail_a1o4 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNK4oTail.PALL BNK4oTail.PALL_agree TTK TTK_agree TTK_nil
           (BNK4oTail.tail_g4t012o sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleK4os.fe_hole_k4os sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNK4oTail.PALL SV) argH ISP fs (with_facts fiendk4a1 [par_odd]) TTK))).
  Qed.
  Lemma pk5 : piece SV argH ISP fs kc5a1_hs305 TTK.
  Proof.
    apply (HBChain.hole_compose SV argH ISP fs kc5a1_hs305 fiendk5a1 TTK); [vm_compute; lia | exact TTK_agree | exact (BFI8HoleK5A1.fi_hole_k5a1 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HBParity.piece_parity SV argH ISP fs fiendk5a1 TTK
      (HBJoin.piece_svg_all SV argH ISP fs BNK5eTail.PALL _ TTK (fun _ => I)
        (BVG5KA1e5.vtail_a1e5 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNK5eTail.PALL BNK5eTail.PALL_agree TTK TTK_agree TTK_nil
           (BNK5eTail.tail_g5t012e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleK5es.fe_hole_k5es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNK5eTail.PALL SV) argH ISP fs (with_facts fiendk5a1 [par_even]) TTK))
      (HBJoin.piece_svg_all SV argH ISP fs BNK5oTail.PALL _ TTK (fun _ => I)
        (BVG5KA1o5.vtail_a1o5 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNK5oTail.PALL BNK5oTail.PALL_agree TTK TTK_agree TTK_nil
           (BNK5oTail.tail_g5t012o sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleK5os.fe_hole_k5os sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNK5oTail.PALL SV) argH ISP fs (with_facts fiendk5a1 [par_odd]) TTK))).
  Qed.
  Lemma pk6 : piece SV argH ISP fs kc6a1_hs306 TTK.
  Proof.
    apply (HBChain.hole_compose SV argH ISP fs kc6a1_hs306 fiendk6a1 TTK); [vm_compute; lia | exact TTK_agree | exact (BFI8HoleK6A1.fi_hole_k6a1 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HBParity.piece_parity SV argH ISP fs fiendk6a1 TTK
      (HBJoin.piece_svg_all SV argH ISP fs BNK6eTail.PALL _ TTK (fun _ => I)
        (BVG6KA1e6.vtail_a1e6 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNK6eTail.PALL BNK6eTail.PALL_agree TTK TTK_agree TTK_nil
           (BNK6eTail.tail_g6t012e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleK6es.fe_hole_k6es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNK6eTail.PALL SV) argH ISP fs (with_facts fiendk6a1 [par_even]) TTK))
      (HBJoin.piece_svg_all SV argH ISP fs BNK6oTail.PALL _ TTK (fun _ => I)
        (BVG6KA1o6.vtail_a1o6 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNK6oTail.PALL BNK6oTail.PALL_agree TTK TTK_agree TTK_nil
           (BNK6oTail.tail_g6t012o sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleK6os.fe_hole_k6os sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNK6oTail.PALL SV) argH ISP fs (with_facts fiendk6a1 [par_odd]) TTK))).
  Qed.
  Lemma pk7 : piece SV argH ISP fs kc7a1_hs307 TTK.
  Proof.
    apply (HBChain.hole_compose SV argH ISP fs kc7a1_hs307 fiendk7a1 TTK); [vm_compute; lia | exact TTK_agree | exact (BFI8HoleK7A1.fi_hole_k7a1 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HBParity.piece_parity SV argH ISP fs fiendk7a1 TTK
      (HBJoin.piece_svg_all SV argH ISP fs BNK7eTail.PALL _ TTK (fun _ => I)
        (BVG7KA1e7.vtail_a1e7 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNK7eTail.PALL BNK7eTail.PALL_agree TTK TTK_agree TTK_nil
           (BNK7eTail.tail_g7t012e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleK7es.fe_hole_k7es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNK7eTail.PALL SV) argH ISP fs (with_facts fiendk7a1 [par_even]) TTK))
      (HBJoin.piece_svg_all SV argH ISP fs BNK7oTail.PALL _ TTK (fun _ => I)
        (BVG7KA1o7.vtail_a1o7 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNK7oTail.PALL BNK7oTail.PALL_agree TTK TTK_agree TTK_nil
           (BNK7oTail.tail_g7t012o sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleK7os.fe_hole_k7os sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNK7oTail.PALL SV) argH ISP fs (with_facts fiendk7a1 [par_odd]) TTK))).
  Qed.
  Lemma pk8 : piece SV argH ISP fs kc8a1_hs308 TTK.
  Proof.
    apply (HBChain.hole_compose SV argH ISP fs kc8a1_hs308 fiendk8a1 TTK); [vm_compute; lia | exact TTK_agree | exact (BFI8HoleK8A1.fi_hole_k8a1 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HBParity.piece_parity SV argH ISP fs fiendk8a1 TTK
      (HBJoin.piece_svg_all SV argH ISP fs BNK8eTail.PALL _ TTK (fun _ => I)
        (BVG8KA1e8.vtail_a1e8 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNK8eTail.PALL BNK8eTail.PALL_agree TTK TTK_agree TTK_nil
           (BNK8eTail.tail_g8t012e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleK8es.fe_hole_k8es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNK8eTail.PALL SV) argH ISP fs (with_facts fiendk8a1 [par_even]) TTK))
      (HBJoin.piece_svg_all SV argH ISP fs BNK8oTail.PALL _ TTK (fun _ => I)
        (BVG8KA1o8.vtail_a1o8 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNK8oTail.PALL BNK8oTail.PALL_agree TTK TTK_agree TTK_nil
           (BNK8oTail.tail_g8t012o sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleK8os.fe_hole_k8os sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNK8oTail.PALL SV) argH ISP fs (with_facts fiendk8a1 [par_odd]) TTK))).
  Qed.
  Lemma pk9 : piece SV argH ISP fs kc9a1_hs309 TTK.
  Proof.
    apply (HBChain.hole_compose SV argH ISP fs kc9a1_hs309 fiendk9a1 TTK); [vm_compute; lia | exact TTK_agree | exact (BFI8HoleK9A1.fi_hole_k9a1 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HBParity.piece_parity SV argH ISP fs fiendk9a1 TTK
      (HBJoin.piece_svg_all SV argH ISP fs BNK9eTail.PALL _ TTK (fun _ => I)
        (BVG9KA1e9.vtail_a1e9 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNK9eTail.PALL BNK9eTail.PALL_agree TTK TTK_agree TTK_nil
           (BNK9eTail.tail_g9t012e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleK9es.fe_hole_k9es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNK9eTail.PALL SV) argH ISP fs (with_facts fiendk9a1 [par_even]) TTK))
      (HBJoin.piece_svg_all SV argH ISP fs BNK9oTail.PALL _ TTK (fun _ => I)
        (BVG9KA1o9.vtail_a1o9 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNK9oTail.PALL BNK9oTail.PALL_agree TTK TTK_agree TTK_nil
           (BNK9oTail.tail_g9t012o sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleK9os.fe_hole_k9os sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNK9oTail.PALL SV) argH ISP fs (with_facts fiendk9a1 [par_odd]) TTK))).
  Qed.
  Lemma pk10 : piece SV argH ISP fs kc10a1_hs310 TTK.
  Proof.
    apply (HBChain.hole_compose SV argH ISP fs kc10a1_hs310 fiendk10a1 TTK); [vm_compute; lia | exact TTK_agree | exact (BFI8HoleK10A1.fi_hole_k10a1 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HBParity.piece_parity SV argH ISP fs fiendk10a1 TTK
      (HBJoin.piece_svg_all SV argH ISP fs BNK10eTail.PALL _ TTK (fun _ => I)
        (BVG10KA1e10.vtail_a1e10 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNK10eTail.PALL BNK10eTail.PALL_agree TTK TTK_agree TTK_nil
           (BNK10eTail.tail_g10t012e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleK10es.fe_hole_k10es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNK10eTail.PALL SV) argH ISP fs (with_facts fiendk10a1 [par_even]) TTK))
      (HBJoin.piece_svg_all SV argH ISP fs BNK10oTail.PALL _ TTK (fun _ => I)
        (BVG10KA1o10.vtail_a1o10 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNK10oTail.PALL BNK10oTail.PALL_agree TTK TTK_agree TTK_nil
           (BNK10oTail.tail_g10t012o sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleK10os.fe_hole_k10os sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNK10oTail.PALL SV) argH ISP fs (with_facts fiendk10a1 [par_odd]) TTK))).
  Qed.

  Theorem hfi_a1_sec : forall k, 1 <= k <= 10 -> 2 ^ (15 + k) <= flen c <= 2 ^ (16 + k) - 1 -> piece SV argH ISP fs (HBKge1A1.fi_start_a1 k) TTK.
  Proof.
    intros k HK _.
    assert (HKk : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10) by lia.
    destruct HKk as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]; [exact pk1 | exact pk2 | exact pk3 | exact pk4 | exact pk5 | exact pk6 | exact pk7 | exact pk8 | exact pk9 | exact pk10].
  Qed.
End S.

Theorem hfi_a1 : forall sp rdraw brk0 argv envp fs uid hw, valid_sp sp -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp argv envp ->
  forall k, 1 <= k <= 10 -> 2 ^ (15 + k) <= flen (content_of argv fs) <= 2 ^ (16 + k) - 1 ->
  piece (SINVm HAPH sp rdraw brk0 argv envp uid hw (content_of argv fs)) (argH0 HAPH sp rdraw argv envp uid hw) (bv_unsigned sp) fs (HBKge1A1.fi_start_a1 k) TTK.
Proof. intros sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit. exact (hfi_a1_sec sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit). Qed.
