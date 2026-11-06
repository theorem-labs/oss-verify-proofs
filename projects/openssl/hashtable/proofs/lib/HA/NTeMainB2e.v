(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.openssl.hashtable.images Require Import Asan.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import PropExec CatExec ShapeAlg AgentLib AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanNodesIO AsanInit.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import CxRel CxPlan CxPlanSound CxGlue CxOfAps CxReblob HAPlanImage HAAtable HACheck0 HACheck1 HACheckG HAArg HAChain HAUsageDefs HAHop HAParity HASel
  C7B2Lit FIaEndB2e C7mB2eLit FIEndB2se7 NFiSplitB2e VT012Lit VHB2e NTeFE NTeFEE NTecFE NTecFEE NTesFE NTesFEE NTeTail.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.
Section Main.
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
  Hypothesis H_FIa : fx_hole SV argH ISP fs (with_facts c7b2_hs25 [par_even]) fiaendb2e.
  Hypothesis H_FIb : fx_hole SV argH ISP fs c7mb2e_hs27 fiendb2se7.
  Hypothesis H_FE : fx_hole SV argH ISP fs nte_tfe ntefee.
  Hypothesis H_FEc : fx_hole SV argH ISP fs ntec_tfe ntecfee.
  Hypothesis H_FEs : fx_hole SV argH ISP fs ntes_tfe ntesfee.
  Theorem main_b2e : piece (SVG PALL SV) argH ISP fs (with_facts c7b2_hs25 [par_even]) T0.
  Proof.
    exact (fi_split_b2e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FIa H_FIb PALL PALL_agree T0 T0_agree T0_nil
             (vtail_b2e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit PALL PALL_agree T0 T0_agree T0_nil
                (tail_t012e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FE H_FEc H_FEs))).
  Qed.
End Main.
Lemma cover_b2e : forall E, 0 <= nb_of E <= 65529 -> PALL E. Proof. exact cover. Qed.
