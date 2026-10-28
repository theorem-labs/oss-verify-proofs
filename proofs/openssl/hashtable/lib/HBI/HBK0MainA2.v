(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.openssl.hashtable.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import PropExec ShapeAlg AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanInit.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CxRel CxPlan CxPlanSound HBPlanImage HBAtable HBChain HBCheckG HBParity HBJoin HBTgtGlue HBOpenDefs CxReblob.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BC7A2Lit.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNTeTail BNTeMainA2e BFI8HoleA2ae BFI8HoleA2be BFeHoleTNe BFeHoleTNec BFeHoleTNes.
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
    exact (HBJoin.piece_even_only SV argH ISP fs c7a2_hs25 TT0 kr6_a2
      (HBJoin.piece_svg_all SV argH ISP fs BNTeTail.PALL _ TT0 (fun _ => I)
         (BNTeMainA2e.main_a2e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFI8HoleA2ae.fi_hole_a2ae sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFI8HoleA2be.fi_hole_a2be sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleTNe.fe_hole_tne sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleTNec.fe_hole_tnec sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleTNes.fe_hole_tnes sp rdraw brk0 argv envp fs uid hw Hsp Hva)
            : piece (SVG BNTeTail.PALL SV) argH ISP fs (with_facts c7a2_hs25 [par_even]) TT0))).
  Qed.
End Main25.

Theorem main25_a2 : forall sp rdraw brk0 argv envp fs uid hw, valid_sp sp -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp argv envp ->
  piece (SINVm HAPH sp rdraw brk0 argv envp uid hw (content_of argv fs)) (argH0 HAPH sp rdraw argv envp uid hw) (bv_unsigned sp) fs c7a2_hs25 TT0.
Proof. intros sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit. exact (main25_a2_sec sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit). Qed.
