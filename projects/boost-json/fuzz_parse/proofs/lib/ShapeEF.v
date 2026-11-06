(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import Scfg SimInv ExitSim CatSim ShapeAlg.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypek17mkImage3h5LinuxProcessSemanticsfLinuxProcessSem3Runo07mkEntryo08run_scfg69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Scfg~~~~~~s18the_scfg37Corelib4Init9Datatypeshg34list37Corelib4Init5Logichi33and01N01Z3h5LinuxProcessSemanticsh5EquivalenceDefinitionbEquivalencehk4aerror_freek18PhdrInfok17Segmento09bh_traceso0binit_config3h5LinuxProcessSemanticsfLinuxProcessSembStackLayouthrc9EntryDraw69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8ShapeAlg~~~~~~hvd8realizeshk4btrace_equiv3h5LinuxProcessSemanticsfLinuxProcessSem5Stateil39ProcInputhvd4TSethk4hcstrong_equiv_error_free_scfgil3h2source_alloc_limitil3h2target_alloc_limit" s.

Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

Section WithCfg.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Context {SC : StepCfg}.

Theorem shape_strong_equiv_ef : ltac2:(zQ "h42!h9!jc!n6!qc!r6!v8!hhb!hj7!hje!hk1!hnf!hod!hp8!hq2!hqe!hv0!ij8!ik4!io1!ioe&@5$4@1$5?2SC@3$2^h4^h3^h2^d@4$3^h1^h0^f^e^3&@5$4@1$5?2SC@3$2^c^b^a^5@4$3^9^8^7^6^3>bsource_segs@1$6$c>3rpc$8>3rph$b>3rsp@1$1@1$0#k0>4rbrk@1$1@1$0#k0>3rmb@1$1@1$0#k0>4rrnd$f>4rlim$9>btarget_segs@1$6$c>3apc$8>3aph$b>3asp@1$1@1$0#k0>4abrk@1$1@1$0#k0>3amb@1$1@1$0#k0>4arnd$f>4alim$9>1T$h3>3inp$h2>0@4$h0^h2?2SC@9$e^h2^h1^h0^f^e^d^c^b^1^2>0@4$h0^b?2SC@9$e^b^a^9^8^7^6^5^4^2^3@2$7@1$a~0@2$7@1$a~1@2$h1@1$d~0@1$d~1").
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim
    T inp Hsource Htarget.
  split; [| split].
  - cbn. eapply realizes_no_error; exact Hsource.
  - cbn. eapply realizes_no_error; exact Htarget.
  - intro tr. cbn.
    rewrite (realizes_obs_iff source_segs _ T Hsource tr).
    rewrite (realizes_obs_iff target_segs _ T Htarget tr).
    reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Corollary shape_strong_equiv_ef_scfg : ltac2:(zQ "h10!h9!jc!hhb!hje!hod!hp8!n6!hqe!qc!hv0!ij8!ip6!io1!ir7!ise!v8!ioe>bsource_segs@1$2$5>3rpc$3>3rph$4>3rsp@1$1@1$0#k0>4rbrk@1$1@1$0#k0>3rmb@1$1@1$0#k0>4rrnd$9>btarget_segs@1$2$5>3apc$3>3aph$4>3asp@1$1@1$0#k0>4abrk@1$1@1$0#k0>3amb@1$1@1$0#k0>4arnd$9>1T$h0>3inp$c>0@4$a^h0?2SC@9$7^h0^f^e^d^c^b^a$d^1^2>0@4$a^a?2SC@9$7^a^9^8^7^6^5^4$e^2^3@6$b@1$f?2SC@3$6^h2^h1^h0@3$6^b^a^9@4$8^f^e^d^c@4$8^8^7^6^5^3").
Proof.
  intros. unfold strong_equiv_error_free_scfg. eapply shape_strong_equiv_ef; eassumption.
Qed.

(* [comment removed for export] *)

End WithCfg.
(* [comment removed for export] *)
