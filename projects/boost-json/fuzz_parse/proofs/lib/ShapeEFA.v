(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: statements written out as text, the run's segment list (run_segments), the launch input as a ProcInput. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import Scfg SimInv ExitSim CatSim ShapeAlg ShapeEF.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04bool3h5LinuxProcessSemanticsfLinuxProcessSem5Statehe5event37Corelib7Numbers7BinNumsl44Npos35stdpp9bitvectorbdefinitionsn42bv05false3h5LinuxProcessSemanticsfLinuxProcessSem2Fspd2Fs04true69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8ShapeAlg~~~~~~t34TSet04list37Corelib4Init5Logichhb2eq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8ShapeEFA4FPX1~~~~~~hj57is_kill36Stdlib5Lists4Listho02Int35t_nilhj59kill_free3h5LinuxProcessSemanticsfLinuxProcessSem3Runhqe9is_prefix04negbt36t_emitho07forallbt36t_alt2t36t_exit37Corelib5Lists7ListDefih33maphe7WriteEvhhb3notl41Nl41Z3h5LinuxProcessSemanticsh5EquivalenceDefinitionbEquivalenceikaedies_by_signal3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypeip78PhdrInfoip77Segmentip77mkImagehqebinit_confighqe7mkEntryhqe8run_scfg3h5LinuxProcessSemanticsfLinuxProcessSembStackLayoutjh49EntryDrawhe9ProcInput69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Scfg~~~~~~jm18the_scfgt38realizes69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8ShapeEFA~~~~~~jqf9kill_freeikaiastrong_equiv_error_free_budgets_scfg_abort" s.   (* [comment removed for export] *)

Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

(* [comment removed for export] *)

Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition is_kill : ltac2:(zQ "20!h8!kc>1e$1$0") := ltac2:(zQ "71!md!p1!p6!kc!s8!h8!sd&\2ch@1$1@1$0#k0\1b@1$1@1$0#8$2\1e$3M3\1e$3$5^1~0~0\4code@1$1@1$0#k0\2fs$4$2\3sig@1$1@1$0#k0\2fs$4$6").

Definition kill_free : ltac2:(zQ "10!hge>1T$0P") := ltac2:(zQ "80!kc!h8!p6!hh5!hif!hge!hn5!hp3\1T$5>2tr@1$3$0>0@1^2^1>1e$0>0@3$7$0^1^3@3$4$1@1$6^2$2").

Lemma kill_free_nil : ltac2:(zQ "20!hp9!hq1@1$1$0").
Proof. intros tr Htr e Hin. unfold t_nil in Htr. subst tr. destruct Hin. Qed.

Lemma is_prefix_In : ltac2:(zQ "40!kc!hh5!hp3!hta>2l1@1$1$0>2l2@1$1$0>1e$0>0@3$3$0^3^2>0@3$2$0^2^4@3$2$0^3^4").
Proof.
  induction l1 as [|x l1 IH]; intros l2 e Hp Hin; [destruct Hin|].
  destruct l2 as [|y l2]; [destruct Hp|]. cbn in Hp. destruct Hp as [<- Hp].
  destruct Hin as [<- | Hin]; [now left | right; eapply IH; eauto].
Qed.

Lemma kill_free_emit : ltac2:(zQ "b0!kc!hq1!h8!hh5!hu7!sd!hif!hge!hud!hn5!hv6>3evs@1$3$0>1T$7>0@3$6$2@3$a$0\1e$0@1$4@1$9^1^2$5>0@1$1^2@1$1@2$8^4^3").
Proof.
  intros evs T Hevs HK tr Htr e Hin.
  assert (Hblk : forall e', In e' evs -> is_kill e' = false).
  { intros e' He'. pose proof (proj1 (forallb_forall _ _) Hevs e' He') as Hb.
    cbn in Hb. destruct (is_kill e'); [cbn in Hb; congruence | reflexivity]. }
  destruct Htr as [Hp | (tr' & -> & Htr')].
  - apply Hblk. eapply is_prefix_In; eauto.
  - apply in_app_iff in Hin as [Hin | Hin].
    + apply Hblk; exact Hin.
    + exact (HK tr' Htr' e Hin).
Qed.

Lemma kill_free_alt2 : ltac2:(zQ "30!hq1!hge!ig1>1A$1>1B$1>0@1$0^2>0@1$0^2@1$0@2$2^4^3").
Proof. intros A B HA HB tr [Htr | Htr] e Hin; [exact (HA tr Htr e Hin) | exact (HB tr Htr e Hin)]. Qed.

Lemma kill_free_exit : ltac2:(zQ "50!md!s8!iga!hq1!p1>4code@1$4@1$0#k0>2fs$1@1$3@2$2^2^1").
Proof. intros code fs. unfold t_exit. apply kill_free_emit; [reflexivity | apply kill_free_nil]. Qed.

(* [comment removed for export] *)
Lemma forallb_not_kill_map_write : ltac2:(zQ "c0!md!kc!p1!h8!hh5!hu7!sd!hif!iia!ij1!hn5!hv6>2ch@1$2@1$0#k0>1s@1$4@1$2@1$0#8@3$7$3@3$b$1\1e$1@1$5@1$a^1@4$8@1$2@1$0#8$1@1$9^2^1$6").
Proof. intros ch s. induction s as [|b s IH]; [reflexivity | cbn; exact IH]. Qed.
End FPX1.

(* [comment removed for export] *)

Section WithCfg.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Context {SC : StepCfg}.

Lemma realizes_not_dies : forall segs pc ph sp brk0 mb rnd lim inp T,
  realizes (run_segments segs inp sp mb)
    (init_config (run_segments segs inp sp mb) pc ph sp brk0 mb rnd lim inp) T ->
  kill_free T ->
  ~ dies_by_signal (run_scfg the_scfg (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp).
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp T Hrz HK (tr & sig & fs & Htr & Hin).
  cbn in Htr. apply (realizes_obs_iff (run_segments segs inp sp mb) _ T Hrz tr) in Htr.
  pose proof (HK tr Htr _ Hin) as Hk. discriminate Hk.
Qed.

Theorem shape_strong_equiv_ef_abort :
  forall source_segs rpc rph rsp rbrk rmb rrnd (rlim : Z)
         target_segs apc aph asp abrk amb arnd (alim : Z)
         (T : TSet) (inp : ProcInput),
  realizes (run_segments source_segs inp rsp rmb)
    (init_config (run_segments source_segs inp rsp rmb) rpc rph rsp rbrk rmb rrnd rlim inp) T ->
  realizes (run_segments target_segs inp asp amb)
    (init_config (run_segments target_segs inp asp amb) apc aph asp abrk amb arnd alim inp) T ->
  kill_free T ->
  strong_equiv_error_free_budgets_scfg_abort the_scfg rlim alim
    (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
    (mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp.
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim
    T inp Hsource Htarget HK.
  npose (shape_strong_equiv_ef source_segs rpc rph rsp rbrk rmb rrnd rlim
                target_segs apc aph asp abrk amb arnd alim T inp Hsource Htarget) as (Hs & Ht & Htr).
  unfold strong_equiv_error_free_budgets_scfg_abort, error_free_unkilled.
  repeat split.
  - exact Hs.
  - eapply realizes_not_dies; eassumption.
  - exact Ht.
  - eapply realizes_not_dies; eassumption.
  - apply Htr.
  - apply Htr.
Qed.

(* [comment removed for export] *)

End WithCfg.
(* [comment removed for export] *)
