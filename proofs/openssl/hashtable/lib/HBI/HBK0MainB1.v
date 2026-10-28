(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.openssl.hashtable.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import PropExec ShapeAlg AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanInit.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CxRel CxPlan CxPlanSound HBPlanImage HBAtable HBChain HBCheckG HBParity HBJoin HBTgtGlue HBOpenDefs CxReblob.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BC7B1Lit.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNTeTail BNTeMainB1e BFI8HoleB1ae BFI8HoleB1be BFeHoleTNe BFeHoleTNec BFeHoleTNes.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNToTail BNToMainB1o BFI8HoleB1ao BFI8HoleB1bo BFeHoleTNo BFeHoleTNoc BFeHoleTNos.
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

  Theorem main25_b1_sec : piece SV argH ISP fs c7b1_hs25 TT0.
  Proof.
    exact (HBParity.piece_parity SV argH ISP fs c7b1_hs25 TT0
      (HBJoin.piece_svg_all SV argH ISP fs BNTeTail.PALL _ TT0 (fun _ => I)
         (BNTeMainB1e.main_b1e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFI8HoleB1ae.fi_hole_b1ae sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFI8HoleB1be.fi_hole_b1be sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleTNe.fe_hole_tne sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleTNec.fe_hole_tnec sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleTNes.fe_hole_tnes sp rdraw brk0 argv envp fs uid hw Hsp Hva)
            : piece (SVG BNTeTail.PALL SV) argH ISP fs (with_facts c7b1_hs25 [par_even]) TT0))
      (HBJoin.piece_svg_all SV argH ISP fs BNToTail.PALL _ TT0 (fun _ => I)
         (BNToMainB1o.main_b1o sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFI8HoleB1ao.fi_hole_b1ao sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFI8HoleB1bo.fi_hole_b1bo sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleTNo.fe_hole_tno sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleTNoc.fe_hole_tnoc sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleTNos.fe_hole_tnos sp rdraw brk0 argv envp fs uid hw Hsp Hva)
            : piece (SVG BNToTail.PALL SV) argH ISP fs (with_facts c7b1_hs25 [par_odd]) TT0))).
  Qed.
End Main25.

Theorem main25_b1 : forall sp rdraw brk0 argv envp fs uid hw, valid_sp sp -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp argv envp ->
  piece (SINVm HAPH sp rdraw brk0 argv envp uid hw (content_of argv fs)) (argH0 HAPH sp rdraw argv envp uid hw) (bv_unsigned sp) fs c7b1_hs25 TT0.
Proof. intros sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit. exact (main25_b1_sec sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit). Qed.
