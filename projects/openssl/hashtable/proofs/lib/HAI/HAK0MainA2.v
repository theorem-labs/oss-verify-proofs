(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.openssl.hashtable.images Require Import Asan.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import PropExec ShapeAlg AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanInit.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import CxRel CxPlan CxPlanSound HAPlanImage HAAtable HAChain HACheckG HAParity HAJoin HATgtGlue HAOpenDefs CxReblob.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import C7A2Lit.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import NTeTail NTeMainA2e FI8HoleA2ae FI8HoleA2be FeHoleTNe FeHoleTNec FeHoleTNes.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.

Section Main25.
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

  Lemma kr6_a2 : knows_range (kn c7a2_hs25) 6%nat 6 6 = true.
  Proof. vm_compute. reflexivity. Qed.
  Theorem main25_a2_sec : piece SV argH ISP fs c7a2_hs25 TT0.
  Proof.
    exact (HAJoin.piece_even_only SV argH ISP fs c7a2_hs25 TT0 kr6_a2
      (HAJoin.piece_svg_all SV argH ISP fs NTeTail.PALL _ TT0 (fun _ => I)
         (NTeMainA2e.main_a2e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (FI8HoleA2ae.fi_hole_a2ae sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FI8HoleA2be.fi_hole_a2be sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleTNe.fe_hole_tne sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleTNec.fe_hole_tnec sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleTNes.fe_hole_tnes sp rdraw brk0 argv envp fs uid hw Hsp Hva)
            : piece (SVG NTeTail.PALL SV) argH ISP fs (with_facts c7a2_hs25 [par_even]) TT0))).
  Qed.
End Main25.

Theorem main25_a2 : forall sp rdraw brk0 argv envp fs uid hw, valid_sp sp -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp argv envp ->
  piece (SINVm HAPH sp rdraw brk0 argv envp uid hw (content_of argv fs)) (argH0 HAPH sp rdraw argv envp uid hw) (bv_unsigned sp) fs c7a2_hs25 TT0.
Proof. intros sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit. exact (main25_a2_sec sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit). Qed.
