(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.openssl.hashtable.images Require Import Asan.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import PropExec ShapeAlg AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanInit.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import CxRel CxPlan CxPlanSound HAPlanImage HAAtable HAChain HACheckG HAParity HAJoin HATgtGlue HAOpenDefs CxReblob.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import C7B3Lit.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import NT3eTail NT3eMainB3e FI8HoleB3ae FI8HoleB3be FeHoleT3e FeHoleT3ec FeHoleT3es.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import NT3oTail NT3oMainB3o FI8HoleB3ao FI8HoleB3bo FeHoleT3o FeHoleT3oc FeHoleT3os.
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
    exact (HAParity.piece_parity SV argH ISP fs c7b3_hs25 TT0
      (HAJoin.piece_svg_all SV argH ISP fs NT3eTail.PALL _ TT0 (fun _ => I)
         (NT3eMainB3e.main_b3e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (FI8HoleB3ae.fi_hole_b3ae sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FI8HoleB3be.fi_hole_b3be sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleT3e.fe_hole_t3e sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleT3ec.fe_hole_t3ec sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleT3es.fe_hole_t3es sp rdraw brk0 argv envp fs uid hw Hsp Hva)
            : piece (SVG NT3eTail.PALL SV) argH ISP fs (with_facts c7b3_hs25 [par_even]) TT0))
      (HAJoin.piece_svg_all SV argH ISP fs NT3oTail.PALL _ TT0 (fun _ => I)
         (NT3oMainB3o.main_b3o sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit (FI8HoleB3ao.fi_hole_b3ao sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FI8HoleB3bo.fi_hole_b3bo sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleT3o.fe_hole_t3o sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleT3oc.fe_hole_t3oc sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleT3os.fe_hole_t3os sp rdraw brk0 argv envp fs uid hw Hsp Hva)
            : piece (SVG NT3oTail.PALL SV) argH ISP fs (with_facts c7b3_hs25 [par_odd]) TT0))).
  Qed.
End Main25.

Theorem main25_b3 : forall sp rdraw brk0 argv envp fs uid hw, valid_sp sp -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp argv envp ->
  piece (SINVm HAPH sp rdraw brk0 argv envp uid hw (content_of argv fs)) (argH0 HAPH sp rdraw argv envp uid hw) (bv_unsigned sp) fs c7b3_hs25 TT0.
Proof. intros sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit. exact (main25_b3_sec sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit). Qed.
