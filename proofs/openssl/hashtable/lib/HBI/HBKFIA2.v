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
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import HBKge1A2.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BKC1A2Lit BFIEndK1A2 BKC2A2Lit BFIEndK2A2 BKC3A2Lit BFIEndK3A2 BKC4A2Lit BFIEndK4A2 BKC5A2Lit BFIEndK5A2 BKC6A2Lit BFIEndK6A2 BKC7A2Lit BFIEndK7A2 BKC8A2Lit BFIEndK8A2 BKC9A2Lit BFIEndK9A2 BKC10A2Lit BFIEndK10A2.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BFI8HoleK1A2 BFI8HoleK2A2 BFI8HoleK3A2 BFI8HoleK4A2 BFI8HoleK5A2 BFI8HoleK6A2 BFI8HoleK7A2 BFI8HoleK8A2 BFI8HoleK9A2 BFI8HoleK10A2.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNK1eTail BVG1KA2e1 BFeHoleK1e BFeHoleK1ec BFeHoleK1es.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNK2eTail BVG2KA2e2 BFeHoleK2es.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNK3eTail BVG3KA2e3 BFeHoleK3es.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNK4eTail BVG4KA2e4 BFeHoleK4es.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNK5eTail BVG5KA2e5 BFeHoleK5es.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNK6eTail BVG6KA2e6 BFeHoleK6es.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNK7eTail BVG7KA2e7 BFeHoleK7es.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNK8eTail BVG8KA2e8 BFeHoleK8es.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNK9eTail BVG9KA2e9 BFeHoleK9es.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNK10eTail BVG10KA2e10 BFeHoleK10es.
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
    apply (HBChain.hole_compose SV argH ISP fs kc1a2_hs301 fiendk1a2 TTK); [vm_compute; lia | exact TTK_agree | exact (BFI8HoleK1A2.fi_hole_k1a2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HBJoin.piece_even_only SV argH ISP fs fiendk1a2 TTK kr6_fiendk1a2
      (HBJoin.piece_svg_all SV argH ISP fs BNK1eTail.PALL _ TTK (fun _ => I)
        (BVG1KA2e1.vtail_a2e1 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNK1eTail.PALL BNK1eTail.PALL_agree TTK TTK_agree TTK_nil
           (BNK1eTail.tail_g1t012e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleK1e.fe_hole_k1e sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleK1ec.fe_hole_k1ec sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleK1es.fe_hole_k1es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNK1eTail.PALL SV) argH ISP fs (with_facts fiendk1a2 [par_even]) TTK))).
  Qed.
  Lemma kr6_fiendk2a2 : knows_range (kn fiendk2a2) 6%nat 6 6 = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma pk2 : piece SV argH ISP fs kc2a2_hs302 TTK.
  Proof.
    apply (HBChain.hole_compose SV argH ISP fs kc2a2_hs302 fiendk2a2 TTK); [vm_compute; lia | exact TTK_agree | exact (BFI8HoleK2A2.fi_hole_k2a2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HBJoin.piece_even_only SV argH ISP fs fiendk2a2 TTK kr6_fiendk2a2
      (HBJoin.piece_svg_all SV argH ISP fs BNK2eTail.PALL _ TTK (fun _ => I)
        (BVG2KA2e2.vtail_a2e2 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNK2eTail.PALL BNK2eTail.PALL_agree TTK TTK_agree TTK_nil
           (BNK2eTail.tail_g2t012e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleK2es.fe_hole_k2es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNK2eTail.PALL SV) argH ISP fs (with_facts fiendk2a2 [par_even]) TTK))).
  Qed.
  Lemma kr6_fiendk3a2 : knows_range (kn fiendk3a2) 6%nat 6 6 = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma pk3 : piece SV argH ISP fs kc3a2_hs303 TTK.
  Proof.
    apply (HBChain.hole_compose SV argH ISP fs kc3a2_hs303 fiendk3a2 TTK); [vm_compute; lia | exact TTK_agree | exact (BFI8HoleK3A2.fi_hole_k3a2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HBJoin.piece_even_only SV argH ISP fs fiendk3a2 TTK kr6_fiendk3a2
      (HBJoin.piece_svg_all SV argH ISP fs BNK3eTail.PALL _ TTK (fun _ => I)
        (BVG3KA2e3.vtail_a2e3 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNK3eTail.PALL BNK3eTail.PALL_agree TTK TTK_agree TTK_nil
           (BNK3eTail.tail_g3t012e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleK3es.fe_hole_k3es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNK3eTail.PALL SV) argH ISP fs (with_facts fiendk3a2 [par_even]) TTK))).
  Qed.
  Lemma kr6_fiendk4a2 : knows_range (kn fiendk4a2) 6%nat 6 6 = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma pk4 : piece SV argH ISP fs kc4a2_hs304 TTK.
  Proof.
    apply (HBChain.hole_compose SV argH ISP fs kc4a2_hs304 fiendk4a2 TTK); [vm_compute; lia | exact TTK_agree | exact (BFI8HoleK4A2.fi_hole_k4a2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HBJoin.piece_even_only SV argH ISP fs fiendk4a2 TTK kr6_fiendk4a2
      (HBJoin.piece_svg_all SV argH ISP fs BNK4eTail.PALL _ TTK (fun _ => I)
        (BVG4KA2e4.vtail_a2e4 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNK4eTail.PALL BNK4eTail.PALL_agree TTK TTK_agree TTK_nil
           (BNK4eTail.tail_g4t012e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleK4es.fe_hole_k4es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNK4eTail.PALL SV) argH ISP fs (with_facts fiendk4a2 [par_even]) TTK))).
  Qed.
  Lemma kr6_fiendk5a2 : knows_range (kn fiendk5a2) 6%nat 6 6 = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma pk5 : piece SV argH ISP fs kc5a2_hs305 TTK.
  Proof.
    apply (HBChain.hole_compose SV argH ISP fs kc5a2_hs305 fiendk5a2 TTK); [vm_compute; lia | exact TTK_agree | exact (BFI8HoleK5A2.fi_hole_k5a2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HBJoin.piece_even_only SV argH ISP fs fiendk5a2 TTK kr6_fiendk5a2
      (HBJoin.piece_svg_all SV argH ISP fs BNK5eTail.PALL _ TTK (fun _ => I)
        (BVG5KA2e5.vtail_a2e5 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNK5eTail.PALL BNK5eTail.PALL_agree TTK TTK_agree TTK_nil
           (BNK5eTail.tail_g5t012e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleK5es.fe_hole_k5es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNK5eTail.PALL SV) argH ISP fs (with_facts fiendk5a2 [par_even]) TTK))).
  Qed.
  Lemma kr6_fiendk6a2 : knows_range (kn fiendk6a2) 6%nat 6 6 = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma pk6 : piece SV argH ISP fs kc6a2_hs306 TTK.
  Proof.
    apply (HBChain.hole_compose SV argH ISP fs kc6a2_hs306 fiendk6a2 TTK); [vm_compute; lia | exact TTK_agree | exact (BFI8HoleK6A2.fi_hole_k6a2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HBJoin.piece_even_only SV argH ISP fs fiendk6a2 TTK kr6_fiendk6a2
      (HBJoin.piece_svg_all SV argH ISP fs BNK6eTail.PALL _ TTK (fun _ => I)
        (BVG6KA2e6.vtail_a2e6 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNK6eTail.PALL BNK6eTail.PALL_agree TTK TTK_agree TTK_nil
           (BNK6eTail.tail_g6t012e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleK6es.fe_hole_k6es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNK6eTail.PALL SV) argH ISP fs (with_facts fiendk6a2 [par_even]) TTK))).
  Qed.
  Lemma kr6_fiendk7a2 : knows_range (kn fiendk7a2) 6%nat 6 6 = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma pk7 : piece SV argH ISP fs kc7a2_hs307 TTK.
  Proof.
    apply (HBChain.hole_compose SV argH ISP fs kc7a2_hs307 fiendk7a2 TTK); [vm_compute; lia | exact TTK_agree | exact (BFI8HoleK7A2.fi_hole_k7a2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HBJoin.piece_even_only SV argH ISP fs fiendk7a2 TTK kr6_fiendk7a2
      (HBJoin.piece_svg_all SV argH ISP fs BNK7eTail.PALL _ TTK (fun _ => I)
        (BVG7KA2e7.vtail_a2e7 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNK7eTail.PALL BNK7eTail.PALL_agree TTK TTK_agree TTK_nil
           (BNK7eTail.tail_g7t012e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleK7es.fe_hole_k7es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNK7eTail.PALL SV) argH ISP fs (with_facts fiendk7a2 [par_even]) TTK))).
  Qed.
  Lemma kr6_fiendk8a2 : knows_range (kn fiendk8a2) 6%nat 6 6 = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma pk8 : piece SV argH ISP fs kc8a2_hs308 TTK.
  Proof.
    apply (HBChain.hole_compose SV argH ISP fs kc8a2_hs308 fiendk8a2 TTK); [vm_compute; lia | exact TTK_agree | exact (BFI8HoleK8A2.fi_hole_k8a2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HBJoin.piece_even_only SV argH ISP fs fiendk8a2 TTK kr6_fiendk8a2
      (HBJoin.piece_svg_all SV argH ISP fs BNK8eTail.PALL _ TTK (fun _ => I)
        (BVG8KA2e8.vtail_a2e8 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNK8eTail.PALL BNK8eTail.PALL_agree TTK TTK_agree TTK_nil
           (BNK8eTail.tail_g8t012e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleK8es.fe_hole_k8es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNK8eTail.PALL SV) argH ISP fs (with_facts fiendk8a2 [par_even]) TTK))).
  Qed.
  Lemma kr6_fiendk9a2 : knows_range (kn fiendk9a2) 6%nat 6 6 = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma pk9 : piece SV argH ISP fs kc9a2_hs309 TTK.
  Proof.
    apply (HBChain.hole_compose SV argH ISP fs kc9a2_hs309 fiendk9a2 TTK); [vm_compute; lia | exact TTK_agree | exact (BFI8HoleK9A2.fi_hole_k9a2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HBJoin.piece_even_only SV argH ISP fs fiendk9a2 TTK kr6_fiendk9a2
      (HBJoin.piece_svg_all SV argH ISP fs BNK9eTail.PALL _ TTK (fun _ => I)
        (BVG9KA2e9.vtail_a2e9 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNK9eTail.PALL BNK9eTail.PALL_agree TTK TTK_agree TTK_nil
           (BNK9eTail.tail_g9t012e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleK9es.fe_hole_k9es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNK9eTail.PALL SV) argH ISP fs (with_facts fiendk9a2 [par_even]) TTK))).
  Qed.
  Lemma kr6_fiendk10a2 : knows_range (kn fiendk10a2) 6%nat 6 6 = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma pk10 : piece SV argH ISP fs kc10a2_hs310 TTK.
  Proof.
    apply (HBChain.hole_compose SV argH ISP fs kc10a2_hs310 fiendk10a2 TTK); [vm_compute; lia | exact TTK_agree | exact (BFI8HoleK10A2.fi_hole_k10a2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HBJoin.piece_even_only SV argH ISP fs fiendk10a2 TTK kr6_fiendk10a2
      (HBJoin.piece_svg_all SV argH ISP fs BNK10eTail.PALL _ TTK (fun _ => I)
        (BVG10KA2e10.vtail_a2e10 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNK10eTail.PALL BNK10eTail.PALL_agree TTK TTK_agree TTK_nil
           (BNK10eTail.tail_g10t012e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleK10es.fe_hole_k10es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNK10eTail.PALL SV) argH ISP fs (with_facts fiendk10a2 [par_even]) TTK))).
  Qed.

  Theorem hfi_a2_sec : forall k, 1 <= k <= 10 -> 2 ^ (15 + k) <= flen c <= 2 ^ (16 + k) - 1 -> piece SV argH ISP fs (HBKge1A2.fi_start_a2 k) TTK.
  Proof.
    intros k HK _.
    assert (HKk : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10) by lia.
    destruct HKk as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]; [exact pk1 | exact pk2 | exact pk3 | exact pk4 | exact pk5 | exact pk6 | exact pk7 | exact pk8 | exact pk9 | exact pk10].
  Qed.
End S.

Theorem hfi_a2 : forall sp rdraw brk0 argv envp fs uid hw, valid_sp sp -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp argv envp ->
  forall k, 1 <= k <= 10 -> 2 ^ (15 + k) <= flen (content_of argv fs) <= 2 ^ (16 + k) - 1 ->
  piece (SINVm HAPH sp rdraw brk0 argv envp uid hw (content_of argv fs)) (argH0 HAPH sp rdraw argv envp uid hw) (bv_unsigned sp) fs (HBKge1A2.fi_start_a2 k) TTK.
Proof. intros sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit. exact (hfi_a2_sec sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit). Qed.
