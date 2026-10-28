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
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import HBKge1A3.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BKC1A3Lit BFIEndK1A3 BKC2A3Lit BFIEndK2A3 BKC3A3Lit BFIEndK3A3 BKC4A3Lit BFIEndK4A3 BKC5A3Lit BFIEndK5A3 BKC6A3Lit BFIEndK6A3 BKC7A3Lit BFIEndK7A3 BKC8A3Lit BFIEndK8A3 BKC9A3Lit BFIEndK9A3 BKC10A3Lit BFIEndK10A3.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BFI8HoleK1A3 BFI8HoleK2A3 BFI8HoleK3A3 BFI8HoleK4A3 BFI8HoleK5A3 BFI8HoleK6A3 BFI8HoleK7A3 BFI8HoleK8A3 BFI8HoleK9A3 BFI8HoleK10A3.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNH1eTail BVG1KA3e1 BFeHoleH1e BFeHoleH1ec BFeHoleH1es.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNH1oTail BVG1KA3o1 BFeHoleH1o BFeHoleH1oc BFeHoleH1os.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNH2eTail BVG2KA3e2 BFeHoleH2es.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNH2oTail BVG2KA3o2 BFeHoleH2os.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNH3eTail BVG3KA3e3 BFeHoleH3es.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNH3oTail BVG3KA3o3 BFeHoleH3os.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNH4eTail BVG4KA3e4 BFeHoleH4es.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNH4oTail BVG4KA3o4 BFeHoleH4os.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNH5eTail BVG5KA3e5 BFeHoleH5es.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNH5oTail BVG5KA3o5 BFeHoleH5os.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNH6eTail BVG6KA3e6 BFeHoleH6es.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNH6oTail BVG6KA3o6 BFeHoleH6os.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNH7eTail BVG7KA3e7 BFeHoleH7es.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNH7oTail BVG7KA3o7 BFeHoleH7os.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNH8eTail BVG8KA3e8 BFeHoleH8es.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNH8oTail BVG8KA3o8 BFeHoleH8os.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNH9eTail BVG9KA3e9 BFeHoleH9es.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNH9oTail BVG9KA3o9 BFeHoleH9os.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNH10eTail BVG10KA3e10 BFeHoleH10es.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNH10oTail BVG10KA3o10 BFeHoleH10os.
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


  Lemma pk1 : piece SV argH ISP fs kc1a3_hs301 TTK.
  Proof.
    apply (HBChain.hole_compose SV argH ISP fs kc1a3_hs301 fiendk1a3 TTK); [vm_compute; lia | exact TTK_agree | exact (BFI8HoleK1A3.fi_hole_k1a3 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HBParity.piece_parity SV argH ISP fs fiendk1a3 TTK
      (HBJoin.piece_svg_all SV argH ISP fs BNH1eTail.PALL _ TTK (fun _ => I)
        (BVG1KA3e1.vtail_a3e1 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNH1eTail.PALL BNH1eTail.PALL_agree TTK TTK_agree TTK_nil
           (BNH1eTail.tail_g1t3e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleH1e.fe_hole_h1e sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleH1ec.fe_hole_h1ec sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleH1es.fe_hole_h1es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNH1eTail.PALL SV) argH ISP fs (with_facts fiendk1a3 [par_even]) TTK))
      (HBJoin.piece_svg_all SV argH ISP fs BNH1oTail.PALL _ TTK (fun _ => I)
        (BVG1KA3o1.vtail_a3o1 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNH1oTail.PALL BNH1oTail.PALL_agree TTK TTK_agree TTK_nil
           (BNH1oTail.tail_g1t3o sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleH1o.fe_hole_h1o sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleH1oc.fe_hole_h1oc sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleH1os.fe_hole_h1os sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNH1oTail.PALL SV) argH ISP fs (with_facts fiendk1a3 [par_odd]) TTK))).
  Qed.
  Lemma pk2 : piece SV argH ISP fs kc2a3_hs302 TTK.
  Proof.
    apply (HBChain.hole_compose SV argH ISP fs kc2a3_hs302 fiendk2a3 TTK); [vm_compute; lia | exact TTK_agree | exact (BFI8HoleK2A3.fi_hole_k2a3 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HBParity.piece_parity SV argH ISP fs fiendk2a3 TTK
      (HBJoin.piece_svg_all SV argH ISP fs BNH2eTail.PALL _ TTK (fun _ => I)
        (BVG2KA3e2.vtail_a3e2 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNH2eTail.PALL BNH2eTail.PALL_agree TTK TTK_agree TTK_nil
           (BNH2eTail.tail_g2t3e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleH2es.fe_hole_h2es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNH2eTail.PALL SV) argH ISP fs (with_facts fiendk2a3 [par_even]) TTK))
      (HBJoin.piece_svg_all SV argH ISP fs BNH2oTail.PALL _ TTK (fun _ => I)
        (BVG2KA3o2.vtail_a3o2 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNH2oTail.PALL BNH2oTail.PALL_agree TTK TTK_agree TTK_nil
           (BNH2oTail.tail_g2t3o sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleH2os.fe_hole_h2os sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNH2oTail.PALL SV) argH ISP fs (with_facts fiendk2a3 [par_odd]) TTK))).
  Qed.
  Lemma pk3 : piece SV argH ISP fs kc3a3_hs303 TTK.
  Proof.
    apply (HBChain.hole_compose SV argH ISP fs kc3a3_hs303 fiendk3a3 TTK); [vm_compute; lia | exact TTK_agree | exact (BFI8HoleK3A3.fi_hole_k3a3 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HBParity.piece_parity SV argH ISP fs fiendk3a3 TTK
      (HBJoin.piece_svg_all SV argH ISP fs BNH3eTail.PALL _ TTK (fun _ => I)
        (BVG3KA3e3.vtail_a3e3 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNH3eTail.PALL BNH3eTail.PALL_agree TTK TTK_agree TTK_nil
           (BNH3eTail.tail_g3t3e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleH3es.fe_hole_h3es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNH3eTail.PALL SV) argH ISP fs (with_facts fiendk3a3 [par_even]) TTK))
      (HBJoin.piece_svg_all SV argH ISP fs BNH3oTail.PALL _ TTK (fun _ => I)
        (BVG3KA3o3.vtail_a3o3 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNH3oTail.PALL BNH3oTail.PALL_agree TTK TTK_agree TTK_nil
           (BNH3oTail.tail_g3t3o sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleH3os.fe_hole_h3os sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNH3oTail.PALL SV) argH ISP fs (with_facts fiendk3a3 [par_odd]) TTK))).
  Qed.
  Lemma pk4 : piece SV argH ISP fs kc4a3_hs304 TTK.
  Proof.
    apply (HBChain.hole_compose SV argH ISP fs kc4a3_hs304 fiendk4a3 TTK); [vm_compute; lia | exact TTK_agree | exact (BFI8HoleK4A3.fi_hole_k4a3 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HBParity.piece_parity SV argH ISP fs fiendk4a3 TTK
      (HBJoin.piece_svg_all SV argH ISP fs BNH4eTail.PALL _ TTK (fun _ => I)
        (BVG4KA3e4.vtail_a3e4 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNH4eTail.PALL BNH4eTail.PALL_agree TTK TTK_agree TTK_nil
           (BNH4eTail.tail_g4t3e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleH4es.fe_hole_h4es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNH4eTail.PALL SV) argH ISP fs (with_facts fiendk4a3 [par_even]) TTK))
      (HBJoin.piece_svg_all SV argH ISP fs BNH4oTail.PALL _ TTK (fun _ => I)
        (BVG4KA3o4.vtail_a3o4 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNH4oTail.PALL BNH4oTail.PALL_agree TTK TTK_agree TTK_nil
           (BNH4oTail.tail_g4t3o sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleH4os.fe_hole_h4os sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNH4oTail.PALL SV) argH ISP fs (with_facts fiendk4a3 [par_odd]) TTK))).
  Qed.
  Lemma pk5 : piece SV argH ISP fs kc5a3_hs305 TTK.
  Proof.
    apply (HBChain.hole_compose SV argH ISP fs kc5a3_hs305 fiendk5a3 TTK); [vm_compute; lia | exact TTK_agree | exact (BFI8HoleK5A3.fi_hole_k5a3 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HBParity.piece_parity SV argH ISP fs fiendk5a3 TTK
      (HBJoin.piece_svg_all SV argH ISP fs BNH5eTail.PALL _ TTK (fun _ => I)
        (BVG5KA3e5.vtail_a3e5 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNH5eTail.PALL BNH5eTail.PALL_agree TTK TTK_agree TTK_nil
           (BNH5eTail.tail_g5t3e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleH5es.fe_hole_h5es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNH5eTail.PALL SV) argH ISP fs (with_facts fiendk5a3 [par_even]) TTK))
      (HBJoin.piece_svg_all SV argH ISP fs BNH5oTail.PALL _ TTK (fun _ => I)
        (BVG5KA3o5.vtail_a3o5 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNH5oTail.PALL BNH5oTail.PALL_agree TTK TTK_agree TTK_nil
           (BNH5oTail.tail_g5t3o sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleH5os.fe_hole_h5os sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNH5oTail.PALL SV) argH ISP fs (with_facts fiendk5a3 [par_odd]) TTK))).
  Qed.
  Lemma pk6 : piece SV argH ISP fs kc6a3_hs306 TTK.
  Proof.
    apply (HBChain.hole_compose SV argH ISP fs kc6a3_hs306 fiendk6a3 TTK); [vm_compute; lia | exact TTK_agree | exact (BFI8HoleK6A3.fi_hole_k6a3 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HBParity.piece_parity SV argH ISP fs fiendk6a3 TTK
      (HBJoin.piece_svg_all SV argH ISP fs BNH6eTail.PALL _ TTK (fun _ => I)
        (BVG6KA3e6.vtail_a3e6 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNH6eTail.PALL BNH6eTail.PALL_agree TTK TTK_agree TTK_nil
           (BNH6eTail.tail_g6t3e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleH6es.fe_hole_h6es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNH6eTail.PALL SV) argH ISP fs (with_facts fiendk6a3 [par_even]) TTK))
      (HBJoin.piece_svg_all SV argH ISP fs BNH6oTail.PALL _ TTK (fun _ => I)
        (BVG6KA3o6.vtail_a3o6 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNH6oTail.PALL BNH6oTail.PALL_agree TTK TTK_agree TTK_nil
           (BNH6oTail.tail_g6t3o sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleH6os.fe_hole_h6os sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNH6oTail.PALL SV) argH ISP fs (with_facts fiendk6a3 [par_odd]) TTK))).
  Qed.
  Lemma pk7 : piece SV argH ISP fs kc7a3_hs307 TTK.
  Proof.
    apply (HBChain.hole_compose SV argH ISP fs kc7a3_hs307 fiendk7a3 TTK); [vm_compute; lia | exact TTK_agree | exact (BFI8HoleK7A3.fi_hole_k7a3 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HBParity.piece_parity SV argH ISP fs fiendk7a3 TTK
      (HBJoin.piece_svg_all SV argH ISP fs BNH7eTail.PALL _ TTK (fun _ => I)
        (BVG7KA3e7.vtail_a3e7 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNH7eTail.PALL BNH7eTail.PALL_agree TTK TTK_agree TTK_nil
           (BNH7eTail.tail_g7t3e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleH7es.fe_hole_h7es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNH7eTail.PALL SV) argH ISP fs (with_facts fiendk7a3 [par_even]) TTK))
      (HBJoin.piece_svg_all SV argH ISP fs BNH7oTail.PALL _ TTK (fun _ => I)
        (BVG7KA3o7.vtail_a3o7 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNH7oTail.PALL BNH7oTail.PALL_agree TTK TTK_agree TTK_nil
           (BNH7oTail.tail_g7t3o sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleH7os.fe_hole_h7os sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNH7oTail.PALL SV) argH ISP fs (with_facts fiendk7a3 [par_odd]) TTK))).
  Qed.
  Lemma pk8 : piece SV argH ISP fs kc8a3_hs308 TTK.
  Proof.
    apply (HBChain.hole_compose SV argH ISP fs kc8a3_hs308 fiendk8a3 TTK); [vm_compute; lia | exact TTK_agree | exact (BFI8HoleK8A3.fi_hole_k8a3 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HBParity.piece_parity SV argH ISP fs fiendk8a3 TTK
      (HBJoin.piece_svg_all SV argH ISP fs BNH8eTail.PALL _ TTK (fun _ => I)
        (BVG8KA3e8.vtail_a3e8 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNH8eTail.PALL BNH8eTail.PALL_agree TTK TTK_agree TTK_nil
           (BNH8eTail.tail_g8t3e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleH8es.fe_hole_h8es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNH8eTail.PALL SV) argH ISP fs (with_facts fiendk8a3 [par_even]) TTK))
      (HBJoin.piece_svg_all SV argH ISP fs BNH8oTail.PALL _ TTK (fun _ => I)
        (BVG8KA3o8.vtail_a3o8 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNH8oTail.PALL BNH8oTail.PALL_agree TTK TTK_agree TTK_nil
           (BNH8oTail.tail_g8t3o sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleH8os.fe_hole_h8os sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNH8oTail.PALL SV) argH ISP fs (with_facts fiendk8a3 [par_odd]) TTK))).
  Qed.
  Lemma pk9 : piece SV argH ISP fs kc9a3_hs309 TTK.
  Proof.
    apply (HBChain.hole_compose SV argH ISP fs kc9a3_hs309 fiendk9a3 TTK); [vm_compute; lia | exact TTK_agree | exact (BFI8HoleK9A3.fi_hole_k9a3 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HBParity.piece_parity SV argH ISP fs fiendk9a3 TTK
      (HBJoin.piece_svg_all SV argH ISP fs BNH9eTail.PALL _ TTK (fun _ => I)
        (BVG9KA3e9.vtail_a3e9 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNH9eTail.PALL BNH9eTail.PALL_agree TTK TTK_agree TTK_nil
           (BNH9eTail.tail_g9t3e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleH9es.fe_hole_h9es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNH9eTail.PALL SV) argH ISP fs (with_facts fiendk9a3 [par_even]) TTK))
      (HBJoin.piece_svg_all SV argH ISP fs BNH9oTail.PALL _ TTK (fun _ => I)
        (BVG9KA3o9.vtail_a3o9 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNH9oTail.PALL BNH9oTail.PALL_agree TTK TTK_agree TTK_nil
           (BNH9oTail.tail_g9t3o sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleH9os.fe_hole_h9os sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNH9oTail.PALL SV) argH ISP fs (with_facts fiendk9a3 [par_odd]) TTK))).
  Qed.
  Lemma pk10 : piece SV argH ISP fs kc10a3_hs310 TTK.
  Proof.
    apply (HBChain.hole_compose SV argH ISP fs kc10a3_hs310 fiendk10a3 TTK); [vm_compute; lia | exact TTK_agree | exact (BFI8HoleK10A3.fi_hole_k10a3 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HBParity.piece_parity SV argH ISP fs fiendk10a3 TTK
      (HBJoin.piece_svg_all SV argH ISP fs BNH10eTail.PALL _ TTK (fun _ => I)
        (BVG10KA3e10.vtail_a3e10 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNH10eTail.PALL BNH10eTail.PALL_agree TTK TTK_agree TTK_nil
           (BNH10eTail.tail_g10t3e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleH10es.fe_hole_h10es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNH10eTail.PALL SV) argH ISP fs (with_facts fiendk10a3 [par_even]) TTK))
      (HBJoin.piece_svg_all SV argH ISP fs BNH10oTail.PALL _ TTK (fun _ => I)
        (BVG10KA3o10.vtail_a3o10 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNH10oTail.PALL BNH10oTail.PALL_agree TTK TTK_agree TTK_nil
           (BNH10oTail.tail_g10t3o sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleH10os.fe_hole_h10os sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNH10oTail.PALL SV) argH ISP fs (with_facts fiendk10a3 [par_odd]) TTK))).
  Qed.

  Theorem hfi_a3_sec : forall k, 1 <= k <= 10 -> 2 ^ (15 + k) <= flen c <= 2 ^ (16 + k) - 1 -> piece SV argH ISP fs (HBKge1A3.fi_start_a3 k) TTK.
  Proof.
    intros k HK _.
    assert (HKk : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10) by lia.
    destruct HKk as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]; [exact pk1 | exact pk2 | exact pk3 | exact pk4 | exact pk5 | exact pk6 | exact pk7 | exact pk8 | exact pk9 | exact pk10].
  Qed.
End S.

Theorem hfi_a3 : forall sp rdraw brk0 argv envp fs uid hw, valid_sp sp -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp argv envp ->
  forall k, 1 <= k <= 10 -> 2 ^ (15 + k) <= flen (content_of argv fs) <= 2 ^ (16 + k) - 1 ->
  piece (SINVm HAPH sp rdraw brk0 argv envp uid hw (content_of argv fs)) (argH0 HAPH sp rdraw argv envp uid hw) (bv_unsigned sp) fs (HBKge1A3.fi_start_a3 k) TTK.
Proof. intros sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit. exact (hfi_a3_sec sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit). Qed.
