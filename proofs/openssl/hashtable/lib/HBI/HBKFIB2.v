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
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import HBKge1B2.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BKC1B2Lit BFIEndK1B2 BKC2B2Lit BFIEndK2B2 BKC3B2Lit BFIEndK3B2 BKC4B2Lit BFIEndK4B2 BKC5B2Lit BFIEndK5B2 BKC6B2Lit BFIEndK6B2 BKC7B2Lit BFIEndK7B2 BKC8B2Lit BFIEndK8B2 BKC9B2Lit BFIEndK9B2 BKC10B2Lit BFIEndK10B2.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BFI8HoleK1B2 BFI8HoleK2B2 BFI8HoleK3B2 BFI8HoleK4B2 BFI8HoleK5B2 BFI8HoleK6B2 BFI8HoleK7B2 BFI8HoleK8B2 BFI8HoleK9B2 BFI8HoleK10B2.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNK1eTail BVG1KB2e1 BFeHoleK1e BFeHoleK1ec BFeHoleK1es.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNK2eTail BVG2KB2e2 BFeHoleK2es.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNK3eTail BVG3KB2e3 BFeHoleK3es.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNK4eTail BVG4KB2e4 BFeHoleK4es.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNK5eTail BVG5KB2e5 BFeHoleK5es.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNK6eTail BVG6KB2e6 BFeHoleK6es.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNK7eTail BVG7KB2e7 BFeHoleK7es.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNK8eTail BVG8KB2e8 BFeHoleK8es.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNK9eTail BVG9KB2e9 BFeHoleK9es.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNK10eTail BVG10KB2e10 BFeHoleK10es.
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
    apply (HBChain.hole_compose SV argH ISP fs kc1b2_hs301 fiendk1b2 TTK); [vm_compute; lia | exact TTK_agree | exact (BFI8HoleK1B2.fi_hole_k1b2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HBJoin.piece_even_only SV argH ISP fs fiendk1b2 TTK kr6_fiendk1b2
      (HBJoin.piece_svg_all SV argH ISP fs BNK1eTail.PALL _ TTK (fun _ => I)
        (BVG1KB2e1.vtail_b2e1 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNK1eTail.PALL BNK1eTail.PALL_agree TTK TTK_agree TTK_nil
           (BNK1eTail.tail_g1t012e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleK1e.fe_hole_k1e sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleK1ec.fe_hole_k1ec sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleK1es.fe_hole_k1es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNK1eTail.PALL SV) argH ISP fs (with_facts fiendk1b2 [par_even]) TTK))).
  Qed.
  Lemma kr6_fiendk2b2 : knows_range (kn fiendk2b2) 6%nat 6 6 = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma pk2 : piece SV argH ISP fs kc2b2_hs302 TTK.
  Proof.
    apply (HBChain.hole_compose SV argH ISP fs kc2b2_hs302 fiendk2b2 TTK); [vm_compute; lia | exact TTK_agree | exact (BFI8HoleK2B2.fi_hole_k2b2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HBJoin.piece_even_only SV argH ISP fs fiendk2b2 TTK kr6_fiendk2b2
      (HBJoin.piece_svg_all SV argH ISP fs BNK2eTail.PALL _ TTK (fun _ => I)
        (BVG2KB2e2.vtail_b2e2 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNK2eTail.PALL BNK2eTail.PALL_agree TTK TTK_agree TTK_nil
           (BNK2eTail.tail_g2t012e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleK2es.fe_hole_k2es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNK2eTail.PALL SV) argH ISP fs (with_facts fiendk2b2 [par_even]) TTK))).
  Qed.
  Lemma kr6_fiendk3b2 : knows_range (kn fiendk3b2) 6%nat 6 6 = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma pk3 : piece SV argH ISP fs kc3b2_hs303 TTK.
  Proof.
    apply (HBChain.hole_compose SV argH ISP fs kc3b2_hs303 fiendk3b2 TTK); [vm_compute; lia | exact TTK_agree | exact (BFI8HoleK3B2.fi_hole_k3b2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HBJoin.piece_even_only SV argH ISP fs fiendk3b2 TTK kr6_fiendk3b2
      (HBJoin.piece_svg_all SV argH ISP fs BNK3eTail.PALL _ TTK (fun _ => I)
        (BVG3KB2e3.vtail_b2e3 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNK3eTail.PALL BNK3eTail.PALL_agree TTK TTK_agree TTK_nil
           (BNK3eTail.tail_g3t012e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleK3es.fe_hole_k3es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNK3eTail.PALL SV) argH ISP fs (with_facts fiendk3b2 [par_even]) TTK))).
  Qed.
  Lemma kr6_fiendk4b2 : knows_range (kn fiendk4b2) 6%nat 6 6 = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma pk4 : piece SV argH ISP fs kc4b2_hs304 TTK.
  Proof.
    apply (HBChain.hole_compose SV argH ISP fs kc4b2_hs304 fiendk4b2 TTK); [vm_compute; lia | exact TTK_agree | exact (BFI8HoleK4B2.fi_hole_k4b2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HBJoin.piece_even_only SV argH ISP fs fiendk4b2 TTK kr6_fiendk4b2
      (HBJoin.piece_svg_all SV argH ISP fs BNK4eTail.PALL _ TTK (fun _ => I)
        (BVG4KB2e4.vtail_b2e4 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNK4eTail.PALL BNK4eTail.PALL_agree TTK TTK_agree TTK_nil
           (BNK4eTail.tail_g4t012e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleK4es.fe_hole_k4es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNK4eTail.PALL SV) argH ISP fs (with_facts fiendk4b2 [par_even]) TTK))).
  Qed.
  Lemma kr6_fiendk5b2 : knows_range (kn fiendk5b2) 6%nat 6 6 = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma pk5 : piece SV argH ISP fs kc5b2_hs305 TTK.
  Proof.
    apply (HBChain.hole_compose SV argH ISP fs kc5b2_hs305 fiendk5b2 TTK); [vm_compute; lia | exact TTK_agree | exact (BFI8HoleK5B2.fi_hole_k5b2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HBJoin.piece_even_only SV argH ISP fs fiendk5b2 TTK kr6_fiendk5b2
      (HBJoin.piece_svg_all SV argH ISP fs BNK5eTail.PALL _ TTK (fun _ => I)
        (BVG5KB2e5.vtail_b2e5 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNK5eTail.PALL BNK5eTail.PALL_agree TTK TTK_agree TTK_nil
           (BNK5eTail.tail_g5t012e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleK5es.fe_hole_k5es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNK5eTail.PALL SV) argH ISP fs (with_facts fiendk5b2 [par_even]) TTK))).
  Qed.
  Lemma kr6_fiendk6b2 : knows_range (kn fiendk6b2) 6%nat 6 6 = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma pk6 : piece SV argH ISP fs kc6b2_hs306 TTK.
  Proof.
    apply (HBChain.hole_compose SV argH ISP fs kc6b2_hs306 fiendk6b2 TTK); [vm_compute; lia | exact TTK_agree | exact (BFI8HoleK6B2.fi_hole_k6b2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HBJoin.piece_even_only SV argH ISP fs fiendk6b2 TTK kr6_fiendk6b2
      (HBJoin.piece_svg_all SV argH ISP fs BNK6eTail.PALL _ TTK (fun _ => I)
        (BVG6KB2e6.vtail_b2e6 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNK6eTail.PALL BNK6eTail.PALL_agree TTK TTK_agree TTK_nil
           (BNK6eTail.tail_g6t012e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleK6es.fe_hole_k6es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNK6eTail.PALL SV) argH ISP fs (with_facts fiendk6b2 [par_even]) TTK))).
  Qed.
  Lemma kr6_fiendk7b2 : knows_range (kn fiendk7b2) 6%nat 6 6 = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma pk7 : piece SV argH ISP fs kc7b2_hs307 TTK.
  Proof.
    apply (HBChain.hole_compose SV argH ISP fs kc7b2_hs307 fiendk7b2 TTK); [vm_compute; lia | exact TTK_agree | exact (BFI8HoleK7B2.fi_hole_k7b2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HBJoin.piece_even_only SV argH ISP fs fiendk7b2 TTK kr6_fiendk7b2
      (HBJoin.piece_svg_all SV argH ISP fs BNK7eTail.PALL _ TTK (fun _ => I)
        (BVG7KB2e7.vtail_b2e7 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNK7eTail.PALL BNK7eTail.PALL_agree TTK TTK_agree TTK_nil
           (BNK7eTail.tail_g7t012e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleK7es.fe_hole_k7es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNK7eTail.PALL SV) argH ISP fs (with_facts fiendk7b2 [par_even]) TTK))).
  Qed.
  Lemma kr6_fiendk8b2 : knows_range (kn fiendk8b2) 6%nat 6 6 = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma pk8 : piece SV argH ISP fs kc8b2_hs308 TTK.
  Proof.
    apply (HBChain.hole_compose SV argH ISP fs kc8b2_hs308 fiendk8b2 TTK); [vm_compute; lia | exact TTK_agree | exact (BFI8HoleK8B2.fi_hole_k8b2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HBJoin.piece_even_only SV argH ISP fs fiendk8b2 TTK kr6_fiendk8b2
      (HBJoin.piece_svg_all SV argH ISP fs BNK8eTail.PALL _ TTK (fun _ => I)
        (BVG8KB2e8.vtail_b2e8 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNK8eTail.PALL BNK8eTail.PALL_agree TTK TTK_agree TTK_nil
           (BNK8eTail.tail_g8t012e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleK8es.fe_hole_k8es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNK8eTail.PALL SV) argH ISP fs (with_facts fiendk8b2 [par_even]) TTK))).
  Qed.
  Lemma kr6_fiendk9b2 : knows_range (kn fiendk9b2) 6%nat 6 6 = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma pk9 : piece SV argH ISP fs kc9b2_hs309 TTK.
  Proof.
    apply (HBChain.hole_compose SV argH ISP fs kc9b2_hs309 fiendk9b2 TTK); [vm_compute; lia | exact TTK_agree | exact (BFI8HoleK9B2.fi_hole_k9b2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HBJoin.piece_even_only SV argH ISP fs fiendk9b2 TTK kr6_fiendk9b2
      (HBJoin.piece_svg_all SV argH ISP fs BNK9eTail.PALL _ TTK (fun _ => I)
        (BVG9KB2e9.vtail_b2e9 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNK9eTail.PALL BNK9eTail.PALL_agree TTK TTK_agree TTK_nil
           (BNK9eTail.tail_g9t012e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleK9es.fe_hole_k9es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNK9eTail.PALL SV) argH ISP fs (with_facts fiendk9b2 [par_even]) TTK))).
  Qed.
  Lemma kr6_fiendk10b2 : knows_range (kn fiendk10b2) 6%nat 6 6 = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma pk10 : piece SV argH ISP fs kc10b2_hs310 TTK.
  Proof.
    apply (HBChain.hole_compose SV argH ISP fs kc10b2_hs310 fiendk10b2 TTK); [vm_compute; lia | exact TTK_agree | exact (BFI8HoleK10B2.fi_hole_k10b2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) |].
    exact (HBJoin.piece_even_only SV argH ISP fs fiendk10b2 TTK kr6_fiendk10b2
      (HBJoin.piece_svg_all SV argH ISP fs BNK10eTail.PALL _ TTK (fun _ => I)
        (BVG10KB2e10.vtail_b2e10 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit BNK10eTail.PALL BNK10eTail.PALL_agree TTK TTK_agree TTK_nil
           (BNK10eTail.tail_g10t012e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFeHoleK10es.fe_hole_k10es sp rdraw brk0 argv envp fs uid hw Hsp Hva))
         : piece (SVG BNK10eTail.PALL SV) argH ISP fs (with_facts fiendk10b2 [par_even]) TTK))).
  Qed.

  Theorem hfi_b2_sec : forall k, 1 <= k <= 10 -> 2 ^ (15 + k) <= flen c <= 2 ^ (16 + k) - 1 -> piece SV argH ISP fs (HBKge1B2.fi_start_b2 k) TTK.
  Proof.
    intros k HK _.
    assert (HKk : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10) by lia.
    destruct HKk as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]; [exact pk1 | exact pk2 | exact pk3 | exact pk4 | exact pk5 | exact pk6 | exact pk7 | exact pk8 | exact pk9 | exact pk10].
  Qed.
End S.

Theorem hfi_b2 : forall sp rdraw brk0 argv envp fs uid hw, valid_sp sp -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp argv envp ->
  forall k, 1 <= k <= 10 -> 2 ^ (15 + k) <= flen (content_of argv fs) <= 2 ^ (16 + k) - 1 ->
  piece (SINVm HAPH sp rdraw brk0 argv envp uid hw (content_of argv fs)) (argH0 HAPH sp rdraw argv envp uid hw) (bv_unsigned sp) fs (HBKge1B2.fi_start_b2 k) TTK.
Proof. intros sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit. exact (hfi_b2_sec sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit). Qed.
