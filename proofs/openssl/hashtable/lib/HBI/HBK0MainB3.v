(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.openssl.hashtable.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import PropExec ShapeAlg AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanInit.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CxRel CxPlan CxPlanSound HBPlanImage HBAtable HBChain HBCheckG HBParity HBJoin HBTgtGlue HBOpenDefs CxReblob.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BC7B3Lit.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNT3eTail BNT3eMainB3e BFI8HoleB3ae BFI8HoleB3be BFeHoleT3e BFeHoleT3ec BFeHoleT3es.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import BNT3oTail BNT3oMainB3o BFI8HoleB3ao BFI8HoleB3bo BFeHoleT3o BFeHoleT3oc BFeHoleT3os.
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

  Theorem main25_b3_sec : piece SV argH ISP fs c7b3_hs25 TT0.
  Proof.
    exact (HBParity.piece_parity SV argH ISP fs c7b3_hs25 TT0
      (HBJoin.piece_svg_all SV argH ISP fs BNT3eTail.PALL _ TT0 (fun _ => I)
         (BNT3eMainB3e.main_b3e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFI8HoleB3ae.fi_hole_b3ae sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFI8HoleB3be.fi_hole_b3be sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleT3e.fe_hole_t3e sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleT3ec.fe_hole_t3ec sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleT3es.fe_hole_t3es sp rdraw brk0 argv envp fs uid hw Hsp Hva)
            : piece (SVG BNT3eTail.PALL SV) argH ISP fs (with_facts c7b3_hs25 [par_even]) TT0))
      (HBJoin.piece_svg_all SV argH ISP fs BNT3oTail.PALL _ TT0 (fun _ => I)
         (BNT3oMainB3o.main_b3o sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (BFI8HoleB3ao.fi_hole_b3ao sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFI8HoleB3bo.fi_hole_b3bo sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleT3o.fe_hole_t3o sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleT3oc.fe_hole_t3oc sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleT3os.fe_hole_t3os sp rdraw brk0 argv envp fs uid hw Hsp Hva)
            : piece (SVG BNT3oTail.PALL SV) argH ISP fs (with_facts c7b3_hs25 [par_odd]) TT0))).
  Qed.
End Main25.

Theorem main25_b3 : forall sp rdraw brk0 argv envp fs uid hw, valid_sp sp -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp argv envp ->
  piece (SINVm HAPH sp rdraw brk0 argv envp uid hw (content_of argv fs)) (argH0 HAPH sp rdraw argv envp uid hw) (bv_unsigned sp) fs c7b3_hs25 TT0.
Proof. intros sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit. exact (main25_b3_sec sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit). Qed.
