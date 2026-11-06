(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import Scfg SimInv ExitSim CatSim ShapeAlg ShapeEF ShapeEFA SpinAlg.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init9Datatypesk14list37Corelib4Init5Logicm03not01N01Z3h5LinuxProcessSemanticsh5EquivalenceDefinitionbEquivalenceo0edies_by_signal3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypesc8PhdrInfosc7Segmentsc7mkImage3h5LinuxProcessSemanticsfLinuxProcessSem3Runhi0binit_confighi07mkEntryhi08run_scfg3h5LinuxProcessSemanticsfLinuxProcessSembStackLayouthn29EntryDraw3h5LinuxProcessSemanticsfLinuxProcessSem5Statehr39ProcInput69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Scfg~~~~~~hue8the_scfg69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8ShapeAlg~~~~~~ij14TSet69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8ShapeEFA~~~~~~in49kill_free69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7SpinAlg~~~~~~irc9srealizeso0iastrong_equiv_error_free_budgets_scfg_abortij18realizeso0hcstrong_equiv_error_free_scfghr3h2source_alloc_limithr3h2target_alloc_limit" s.   (* [comment removed for export] *)

Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section WithCfg.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Context {SC : StepCfg}.

Lemma srealizes_not_dies : ltac2:(zQ "h30!h9!jc!l9!n4!na!nd!rb!hg1!hgc!hh6!hkc!hlb!hm6!hq6!hu1!ii5!imc!iqf!iv6>4segs@1$2$8>2pc$4>2ph$7>2sp@1$1@1$0#k0>4brk0@1$1@1$0#k0>2mb@1$1@1$0#k0>3rnd$d>3lim$5>3inp$e>1T$h0>0@4$h2^a?2SC@9$a^a^9^8^7^6^5^4^3^2^1>0@1$h1^2@1$3@1$6@5$c@1$f?2SC@3$9^c^b^a^5@4$b^9^8^7^6^4").
Proof.
  (intros segs pc ph sp brk0 mb rnd lim inp T Hrz HK nd_i1; ndestruct nd_i1 as (tr & sig & fs & Htr & Hin)).
  cbn in Htr. apply (srealizes_obs_iff segs _ T Hrz tr) in Htr.
  pose proof (HK tr Htr _ Hin) as Hk. discriminate Hk.
Qed.

Theorem shape_strong_equiv_ef_abort_s : ltac2:(zQ "h20!h9!jc!l9!na!nd!hg1!hgc!hh6!hkc!hlb!hq6!jg3!hu1!ii5!imc!jj1!iqf!iv6>bsource_segs@1$2$6>3rpc$3>3rph$5>3rsp@1$1@1$0#k0>4rbrk@1$1@1$0#k0>3rmb@1$1@1$0#k0>4rrnd$a>4rlim$4>btarget_segs@1$2$6>3apc$3>3aph$5>3asp@1$1@1$0#k0>4abrk@1$1@1$0#k0>3amb@1$1@1$0#k0>4arnd$a>4alim$4>1T$e>3inp$c>0@4$f^h2?2SC@9$8^h2^h1^h0^f^e^d^c^b^1^2>0@4$h1^b?2SC@9$8^b^a^9^8^7^6^5^4^2^3>0@1$h0^4@8$b@1$d?2SC^e^6@3$7^h5^h4^h3@3$7^d^c^b@4$9^h2^h1^h0^f@4$9^a^9^8^7^4").
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim
    T inp Hsource Htarget HK.
  unfold strong_equiv_error_free_budgets_scfg_abort, error_free_unkilled.
  repeat split.
  - cbn. eapply realizes_no_error; exact Hsource.
  - eapply realizes_not_dies; eassumption.
  - cbn. eapply srealizes_no_error; exact Htarget.
  - eapply srealizes_not_dies; eassumption.
  - intros H. cbn in H |- *.
    apply (srealizes_obs_iff target_segs _ T Htarget tr).
    apply (realizes_obs_iff source_segs _ T Hsource tr). exact H.
  - intros H. cbn in H |- *.
    apply (realizes_obs_iff source_segs _ T Hsource tr).
    apply (srealizes_obs_iff target_segs _ T Htarget tr). exact H.
Qed.

(* [comment removed for export] *)


(* [comment removed for export] *)
Corollary shape_strong_equiv_ef_scfg_s : ltac2:(zQ "h20!h9!jc!l9!na!hg1!hgc!hh6!hkc!hlb!hq6!jjd!hu1!jld!jn4!ii5!imc!jj1!iv6>bsource_segs@1$2$5>3rpc$3>3rph$4>3rsp@1$1@1$0#k0>4rbrk@1$1@1$0#k0>3rmb@1$1@1$0#k0>4rrnd$9>btarget_segs@1$2$5>3apc$3>3aph$4>3asp@1$1@1$0#k0>4abrk@1$1@1$0#k0>3amb@1$1@1$0#k0>4arnd$9>1T$f>3inp$b>0@4$h0^h0?2SC@9$7^h0^f^e^d^c^b^a$c^1^2>0@4$h1^a?2SC@9$7^a^9^8^7^6^5^4$d^2^3@6$a@1$e?2SC@3$6^h2^h1^h0@3$6^b^a^9@4$8^f^e^d^c@4$8^8^7^6^5^3").
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd T inp Hsource Htarget.
  unfold strong_equiv_error_free_scfg. split; [| split].
  - cbn. eapply realizes_no_error; exact Hsource.
  - cbn. eapply srealizes_no_error; exact Htarget.
  - intro tr. cbn.
    rewrite (realizes_obs_iff source_segs _ T Hsource tr).
    rewrite (srealizes_obs_iff target_segs _ T Htarget tr).
    reflexivity.
Qed.

End WithCfg.
(* [comment removed for export] *)
