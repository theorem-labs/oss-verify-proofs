(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.openssl.hashtable.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import PropExec CatExec ShapeAlg AgentLib AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanNodesIO AsanInit.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CxRel CxPlan CxPlanSound CxGlue CxOfAps CxReblob HBPlanImage HBAtable HBCheck0 HBCheck1 HBCheckG HBArg HBChain HBUsageDefs HBHop HBParity HBSel
  BC7A3Lit BFIaEndA3e BC7mA3eLit BFIEndA3se7 BNFiSplitA3e BVT012Lit BVHA3e BNT3eFE BNT3eFEE BNT3ecFE BNT3ecFEE BNT3esFE BNT3esFEE BNT3eTail.
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
  Hypothesis H_FIa : fx_hole SV argH ISP fs (with_facts c7a3_hs25 [par_even]) fiaenda3e.
  Hypothesis H_FIb : fx_hole SV argH ISP fs c7ma3e_hs27 fienda3se7.
  Hypothesis H_FE : fx_hole SV argH ISP fs nt3e_tfe nt3efee.
  Hypothesis H_FEc : fx_hole SV argH ISP fs nt3ec_tfe nt3ecfee.
  Hypothesis H_FEs : fx_hole SV argH ISP fs nt3es_tfe nt3esfee.
  Theorem main_a3e : piece (SVG PALL SV) argH ISP fs (with_facts c7a3_hs25 [par_even]) T0.
  Proof.
    exact (fi_split_a3e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FIa H_FIb PALL PALL_agree T0 T0_agree T0_nil
             (vtail_a3e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit PALL PALL_agree T0 T0_agree T0_nil
                (tail_t3e sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FE H_FEc H_FEs))).
  Qed.
End Main.
Lemma cover_a3e : forall E, 0 <= nb_of E <= 65529 -> PALL E. Proof. exact cover. Qed.
