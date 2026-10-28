(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.openssl.hashtable.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import PropExec CatExec ShapeAlg AgentLib AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanNodesIO AsanInit.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CxRel CxPlan CxPlanSound CxGlue CxOfAps CxReblob HBPlanImage HBAtable HBCheck0 HBCheck1 HBCheckG HBArg HBChain HBUsageDefs HBHop HBParity HBSel
  BC7A1Lit BFIaEndA1o BC7mA1oLit BFIEndA1so BNFiSplitA1o BVT012Lit BVHA1o BNToFE BNToFEE BNTocFE BNTocFEE BNTosFE BNTosFEE BNToTail.
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
  Hypothesis H_FIa : fx_hole SV argH ISP fs (with_facts c7a1_hs25 [par_odd]) fiaenda1o.
  Hypothesis H_FIb : fx_hole SV argH ISP fs c7ma1o_hs27 fienda1so.
  Hypothesis H_FE : fx_hole SV argH ISP fs nto_tfe ntofee.
  Hypothesis H_FEc : fx_hole SV argH ISP fs ntoc_tfe ntocfee.
  Hypothesis H_FEs : fx_hole SV argH ISP fs ntos_tfe ntosfee.
  Theorem main_a1o : piece (SVG PALL SV) argH ISP fs (with_facts c7a1_hs25 [par_odd]) T0.
  Proof.
    exact (fi_split_a1o sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FIa H_FIb PALL PALL_agree T0 T0_agree T0_nil
             (vtail_a1o sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit PALL PALL_agree T0 T0_agree T0_nil
                (tail_t012o sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FE H_FEc H_FEs))).
  Qed.
End Main.
Lemma cover_a1o : forall E, 0 <= nb_of E <= 65529 -> PALL E. Proof. exact cover. Qed.
