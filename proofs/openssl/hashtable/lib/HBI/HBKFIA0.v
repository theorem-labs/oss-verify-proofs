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
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import HBKge1A0.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BKC1A0Lit BFIEndK1A0 BKC2A0Lit BFIEndK2A0 BKC3A0Lit BFIEndK3A0 BKC4A0Lit BFIEndK4A0 BKC5A0Lit BFIEndK5A0 BKC6A0Lit BFIEndK6A0 BKC7A0Lit BFIEndK7A0 BKC8A0Lit BFIEndK8A0 BKC9A0Lit BFIEndK9A0 BKC10A0Lit BFIEndK10A0.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BFI8HoleK1A0 BFI8HoleK2A0 BFI8HoleK3A0 BFI8HoleK4A0 BFI8HoleK5A0 BFI8HoleK6A0 BFI8HoleK7A0 BFI8HoleK8A0 BFI8HoleK9A0 BFI8HoleK10A0.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNK1eTail BVG1KA0e1 BFeHoleK1e BFeHoleK1ec BFeHoleK1es.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNK1oTail BVG1KA0o1 BFeHoleK1o BFeHoleK1oc BFeHoleK1os.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNK2eTail BVG2KA0e2 BFeHoleK2es.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNK2oTail BVG2KA0o2 BFeHoleK2os.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNK3eTail BVG3KA0e3 BFeHoleK3es.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNK3oTail BVG3KA0o3 BFeHoleK3os.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNK4eTail BVG4KA0e4 BFeHoleK4es.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNK4oTail BVG4KA0o4 BFeHoleK4os.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNK5eTail BVG5KA0e5 BFeHoleK5es.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNK5oTail BVG5KA0o5 BFeHoleK5os.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNK6eTail BVG6KA0e6 BFeHoleK6es.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNK6oTail BVG6KA0o6 BFeHoleK6os.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNK7eTail BVG7KA0e7 BFeHoleK7es.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNK7oTail BVG7KA0o7 BFeHoleK7os.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNK8eTail BVG8KA0e8 BFeHoleK8es.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNK8oTail BVG8KA0o8 BFeHoleK8os.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNK9eTail BVG9KA0e9 BFeHoleK9es.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNK9oTail BVG9KA0o9 BFeHoleK9os.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNK10eTail BVG10KA0e10 BFeHoleK10es.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNK10oTail BVG10KA0o10 BFeHoleK10os.
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


  Lemma pk1 : piece SV argH ISP fs kc1a0_hs301 TTK.
  Proof.
    apply (HBChain.hole_compose SV argH ISP fs kc1a0_hs301 fiendk1a0 TTK); [vm_compute; lia | exact TTK_agree | exact (BFI8HoleK1A0.fi_hole_k1a0 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HBParity.piece_parity SV argH ISP fs fiendk1a0 TTK
      (HBJoin.piece_svg_all SV argH ISP fs BNK1eTail.PALL _ TTK (fun _ => I)
        (BVG1KA0e1.vtail_a0e1 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNK1eTail.PALL BNK1eTail.PALL_agree TTK TTK_agree TTK_nil
           (BNK1eTail.tail_g1t012e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleK1e.fe_hole_k1e sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleK1ec.fe_hole_k1ec sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleK1es.fe_hole_k1es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNK1eTail.PALL SV) argH ISP fs (with_facts fiendk1a0 [par_even]) TTK))
      (HBJoin.piece_svg_all SV argH ISP fs BNK1oTail.PALL _ TTK (fun _ => I)
        (BVG1KA0o1.vtail_a0o1 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNK1oTail.PALL BNK1oTail.PALL_agree TTK TTK_agree TTK_nil
           (BNK1oTail.tail_g1t012o sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleK1o.fe_hole_k1o sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleK1oc.fe_hole_k1oc sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleK1os.fe_hole_k1os sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNK1oTail.PALL SV) argH ISP fs (with_facts fiendk1a0 [par_odd]) TTK))).
  Qed.
  Lemma pk2 : piece SV argH ISP fs kc2a0_hs302 TTK.
  Proof.
    apply (HBChain.hole_compose SV argH ISP fs kc2a0_hs302 fiendk2a0 TTK); [vm_compute; lia | exact TTK_agree | exact (BFI8HoleK2A0.fi_hole_k2a0 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HBParity.piece_parity SV argH ISP fs fiendk2a0 TTK
      (HBJoin.piece_svg_all SV argH ISP fs BNK2eTail.PALL _ TTK (fun _ => I)
        (BVG2KA0e2.vtail_a0e2 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNK2eTail.PALL BNK2eTail.PALL_agree TTK TTK_agree TTK_nil
           (BNK2eTail.tail_g2t012e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleK2es.fe_hole_k2es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNK2eTail.PALL SV) argH ISP fs (with_facts fiendk2a0 [par_even]) TTK))
      (HBJoin.piece_svg_all SV argH ISP fs BNK2oTail.PALL _ TTK (fun _ => I)
        (BVG2KA0o2.vtail_a0o2 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNK2oTail.PALL BNK2oTail.PALL_agree TTK TTK_agree TTK_nil
           (BNK2oTail.tail_g2t012o sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleK2os.fe_hole_k2os sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNK2oTail.PALL SV) argH ISP fs (with_facts fiendk2a0 [par_odd]) TTK))).
  Qed.
  Lemma pk3 : piece SV argH ISP fs kc3a0_hs303 TTK.
  Proof.
    apply (HBChain.hole_compose SV argH ISP fs kc3a0_hs303 fiendk3a0 TTK); [vm_compute; lia | exact TTK_agree | exact (BFI8HoleK3A0.fi_hole_k3a0 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HBParity.piece_parity SV argH ISP fs fiendk3a0 TTK
      (HBJoin.piece_svg_all SV argH ISP fs BNK3eTail.PALL _ TTK (fun _ => I)
        (BVG3KA0e3.vtail_a0e3 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNK3eTail.PALL BNK3eTail.PALL_agree TTK TTK_agree TTK_nil
           (BNK3eTail.tail_g3t012e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleK3es.fe_hole_k3es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNK3eTail.PALL SV) argH ISP fs (with_facts fiendk3a0 [par_even]) TTK))
      (HBJoin.piece_svg_all SV argH ISP fs BNK3oTail.PALL _ TTK (fun _ => I)
        (BVG3KA0o3.vtail_a0o3 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNK3oTail.PALL BNK3oTail.PALL_agree TTK TTK_agree TTK_nil
           (BNK3oTail.tail_g3t012o sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleK3os.fe_hole_k3os sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNK3oTail.PALL SV) argH ISP fs (with_facts fiendk3a0 [par_odd]) TTK))).
  Qed.
  Lemma pk4 : piece SV argH ISP fs kc4a0_hs304 TTK.
  Proof.
    apply (HBChain.hole_compose SV argH ISP fs kc4a0_hs304 fiendk4a0 TTK); [vm_compute; lia | exact TTK_agree | exact (BFI8HoleK4A0.fi_hole_k4a0 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HBParity.piece_parity SV argH ISP fs fiendk4a0 TTK
      (HBJoin.piece_svg_all SV argH ISP fs BNK4eTail.PALL _ TTK (fun _ => I)
        (BVG4KA0e4.vtail_a0e4 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNK4eTail.PALL BNK4eTail.PALL_agree TTK TTK_agree TTK_nil
           (BNK4eTail.tail_g4t012e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleK4es.fe_hole_k4es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNK4eTail.PALL SV) argH ISP fs (with_facts fiendk4a0 [par_even]) TTK))
      (HBJoin.piece_svg_all SV argH ISP fs BNK4oTail.PALL _ TTK (fun _ => I)
        (BVG4KA0o4.vtail_a0o4 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNK4oTail.PALL BNK4oTail.PALL_agree TTK TTK_agree TTK_nil
           (BNK4oTail.tail_g4t012o sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleK4os.fe_hole_k4os sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNK4oTail.PALL SV) argH ISP fs (with_facts fiendk4a0 [par_odd]) TTK))).
  Qed.
  Lemma pk5 : piece SV argH ISP fs kc5a0_hs305 TTK.
  Proof.
    apply (HBChain.hole_compose SV argH ISP fs kc5a0_hs305 fiendk5a0 TTK); [vm_compute; lia | exact TTK_agree | exact (BFI8HoleK5A0.fi_hole_k5a0 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HBParity.piece_parity SV argH ISP fs fiendk5a0 TTK
      (HBJoin.piece_svg_all SV argH ISP fs BNK5eTail.PALL _ TTK (fun _ => I)
        (BVG5KA0e5.vtail_a0e5 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNK5eTail.PALL BNK5eTail.PALL_agree TTK TTK_agree TTK_nil
           (BNK5eTail.tail_g5t012e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleK5es.fe_hole_k5es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNK5eTail.PALL SV) argH ISP fs (with_facts fiendk5a0 [par_even]) TTK))
      (HBJoin.piece_svg_all SV argH ISP fs BNK5oTail.PALL _ TTK (fun _ => I)
        (BVG5KA0o5.vtail_a0o5 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNK5oTail.PALL BNK5oTail.PALL_agree TTK TTK_agree TTK_nil
           (BNK5oTail.tail_g5t012o sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleK5os.fe_hole_k5os sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNK5oTail.PALL SV) argH ISP fs (with_facts fiendk5a0 [par_odd]) TTK))).
  Qed.
  Lemma pk6 : piece SV argH ISP fs kc6a0_hs306 TTK.
  Proof.
    apply (HBChain.hole_compose SV argH ISP fs kc6a0_hs306 fiendk6a0 TTK); [vm_compute; lia | exact TTK_agree | exact (BFI8HoleK6A0.fi_hole_k6a0 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HBParity.piece_parity SV argH ISP fs fiendk6a0 TTK
      (HBJoin.piece_svg_all SV argH ISP fs BNK6eTail.PALL _ TTK (fun _ => I)
        (BVG6KA0e6.vtail_a0e6 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNK6eTail.PALL BNK6eTail.PALL_agree TTK TTK_agree TTK_nil
           (BNK6eTail.tail_g6t012e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleK6es.fe_hole_k6es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNK6eTail.PALL SV) argH ISP fs (with_facts fiendk6a0 [par_even]) TTK))
      (HBJoin.piece_svg_all SV argH ISP fs BNK6oTail.PALL _ TTK (fun _ => I)
        (BVG6KA0o6.vtail_a0o6 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNK6oTail.PALL BNK6oTail.PALL_agree TTK TTK_agree TTK_nil
           (BNK6oTail.tail_g6t012o sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleK6os.fe_hole_k6os sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNK6oTail.PALL SV) argH ISP fs (with_facts fiendk6a0 [par_odd]) TTK))).
  Qed.
  Lemma pk7 : piece SV argH ISP fs kc7a0_hs307 TTK.
  Proof.
    apply (HBChain.hole_compose SV argH ISP fs kc7a0_hs307 fiendk7a0 TTK); [vm_compute; lia | exact TTK_agree | exact (BFI8HoleK7A0.fi_hole_k7a0 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HBParity.piece_parity SV argH ISP fs fiendk7a0 TTK
      (HBJoin.piece_svg_all SV argH ISP fs BNK7eTail.PALL _ TTK (fun _ => I)
        (BVG7KA0e7.vtail_a0e7 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNK7eTail.PALL BNK7eTail.PALL_agree TTK TTK_agree TTK_nil
           (BNK7eTail.tail_g7t012e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleK7es.fe_hole_k7es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNK7eTail.PALL SV) argH ISP fs (with_facts fiendk7a0 [par_even]) TTK))
      (HBJoin.piece_svg_all SV argH ISP fs BNK7oTail.PALL _ TTK (fun _ => I)
        (BVG7KA0o7.vtail_a0o7 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNK7oTail.PALL BNK7oTail.PALL_agree TTK TTK_agree TTK_nil
           (BNK7oTail.tail_g7t012o sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleK7os.fe_hole_k7os sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNK7oTail.PALL SV) argH ISP fs (with_facts fiendk7a0 [par_odd]) TTK))).
  Qed.
  Lemma pk8 : piece SV argH ISP fs kc8a0_hs308 TTK.
  Proof.
    apply (HBChain.hole_compose SV argH ISP fs kc8a0_hs308 fiendk8a0 TTK); [vm_compute; lia | exact TTK_agree | exact (BFI8HoleK8A0.fi_hole_k8a0 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HBParity.piece_parity SV argH ISP fs fiendk8a0 TTK
      (HBJoin.piece_svg_all SV argH ISP fs BNK8eTail.PALL _ TTK (fun _ => I)
        (BVG8KA0e8.vtail_a0e8 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNK8eTail.PALL BNK8eTail.PALL_agree TTK TTK_agree TTK_nil
           (BNK8eTail.tail_g8t012e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleK8es.fe_hole_k8es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNK8eTail.PALL SV) argH ISP fs (with_facts fiendk8a0 [par_even]) TTK))
      (HBJoin.piece_svg_all SV argH ISP fs BNK8oTail.PALL _ TTK (fun _ => I)
        (BVG8KA0o8.vtail_a0o8 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNK8oTail.PALL BNK8oTail.PALL_agree TTK TTK_agree TTK_nil
           (BNK8oTail.tail_g8t012o sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleK8os.fe_hole_k8os sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNK8oTail.PALL SV) argH ISP fs (with_facts fiendk8a0 [par_odd]) TTK))).
  Qed.
  Lemma pk9 : piece SV argH ISP fs kc9a0_hs309 TTK.
  Proof.
    apply (HBChain.hole_compose SV argH ISP fs kc9a0_hs309 fiendk9a0 TTK); [vm_compute; lia | exact TTK_agree | exact (BFI8HoleK9A0.fi_hole_k9a0 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HBParity.piece_parity SV argH ISP fs fiendk9a0 TTK
      (HBJoin.piece_svg_all SV argH ISP fs BNK9eTail.PALL _ TTK (fun _ => I)
        (BVG9KA0e9.vtail_a0e9 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNK9eTail.PALL BNK9eTail.PALL_agree TTK TTK_agree TTK_nil
           (BNK9eTail.tail_g9t012e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleK9es.fe_hole_k9es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNK9eTail.PALL SV) argH ISP fs (with_facts fiendk9a0 [par_even]) TTK))
      (HBJoin.piece_svg_all SV argH ISP fs BNK9oTail.PALL _ TTK (fun _ => I)
        (BVG9KA0o9.vtail_a0o9 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNK9oTail.PALL BNK9oTail.PALL_agree TTK TTK_agree TTK_nil
           (BNK9oTail.tail_g9t012o sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleK9os.fe_hole_k9os sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNK9oTail.PALL SV) argH ISP fs (with_facts fiendk9a0 [par_odd]) TTK))).
  Qed.
  Lemma pk10 : piece SV argH ISP fs kc10a0_hs310 TTK.
  Proof.
    apply (HBChain.hole_compose SV argH ISP fs kc10a0_hs310 fiendk10a0 TTK); [vm_compute; lia | exact TTK_agree | exact (BFI8HoleK10A0.fi_hole_k10a0 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HBParity.piece_parity SV argH ISP fs fiendk10a0 TTK
      (HBJoin.piece_svg_all SV argH ISP fs BNK10eTail.PALL _ TTK (fun _ => I)
        (BVG10KA0e10.vtail_a0e10 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNK10eTail.PALL BNK10eTail.PALL_agree TTK TTK_agree TTK_nil
           (BNK10eTail.tail_g10t012e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleK10es.fe_hole_k10es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNK10eTail.PALL SV) argH ISP fs (with_facts fiendk10a0 [par_even]) TTK))
      (HBJoin.piece_svg_all SV argH ISP fs BNK10oTail.PALL _ TTK (fun _ => I)
        (BVG10KA0o10.vtail_a0o10 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNK10oTail.PALL BNK10oTail.PALL_agree TTK TTK_agree TTK_nil
           (BNK10oTail.tail_g10t012o sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleK10os.fe_hole_k10os sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNK10oTail.PALL SV) argH ISP fs (with_facts fiendk10a0 [par_odd]) TTK))).
  Qed.

  Theorem hfi_a0_sec : forall k, 1 <= k <= 10 -> 2 ^ (15 + k) <= flen c <= 2 ^ (16 + k) - 1 -> piece SV argH ISP fs (HBKge1A0.fi_start_a0 k) TTK.
  Proof.
    intros k HK _.
    assert (HKk : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10) by lia.
    destruct HKk as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]; [exact pk1 | exact pk2 | exact pk3 | exact pk4 | exact pk5 | exact pk6 | exact pk7 | exact pk8 | exact pk9 | exact pk10].
  Qed.
End S.

Theorem hfi_a0 : forall sp rdraw brk0 argv envp fs uid hw, valid_sp sp -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp argv envp ->
  forall k, 1 <= k <= 10 -> 2 ^ (15 + k) <= flen (content_of argv fs) <= 2 ^ (16 + k) - 1 ->
  piece (SINVm HAPH sp rdraw brk0 argv envp uid hw (content_of argv fs)) (argH0 HAPH sp rdraw argv envp uid hw) (bv_unsigned sp) fs (HBKge1A0.fi_start_a0 k) TTK.
Proof. intros sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit. exact (hfi_a0_sec sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit). Qed.
