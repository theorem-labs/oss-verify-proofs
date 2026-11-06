(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require RefU0Gc5. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Ref0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import PropExec MState Mem ITree Nodes Decode.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import Prelim Monad MSafeP STree Malloc Prog KInv MmNodes GapGrid KLink KLink2 KLink3.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require MI_Contracts.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import MallocMF_klink.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4Prog~~~~~~06PState37Corelib4Init9Datatypesk44list3h5LinuxProcessSemanticsfLinuxProcessSem5Statem35Model79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6MSafeP~~~~~~p94assn04bptr79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~u44cptr37Corelib4Init5Logichi93and37Corelib7Numbers7BinNumshk41Zk43fstk44prod37Corelib5Lists7ListDefhmf3map79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4KInv~~~~~~hod4mledhi92ex79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUeMallocMF_klink~~~~~~ht74KLBMhod6creachhod7ld_live06ps_brk04ps_m36Stdlib5Lists4Listik85NoDupik84inclk46option89OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUeMallocMF_model2HC~~~~~~in54OWNMk44cons79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec5KLink~~~~~~isd8frame_okp95mspec79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec7MmNodes~~~~~~jhe6mmsafe0araw_malloc46Stdlib6ZArith6BinInt1Zjn32lejn32ltjn33powk44unit08raw_free" s.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).
Notation mspec := (MSafeP.mspec mmsafe).
Notation MP := (Monad.M PState).

Section HC.
Context {HC : HeapCeil}.

(* [comment removed for export] *)
Definition OWNM : ltac2:(zQ "50!jc!lc!p1!t7!te>1X@1$1$4>1G>0$0>0$2P@1$3$0") := ltac2:(zQ "h30!hi2!hjd!hld!hm2!hm8!ho6!p1!hs9!jc!lc!ht1!ihd!ii5!iif!te!ija!ik2!ilb!im4\1X@1$9$e\1G>0$8>0$6P\1s$8\2mo$6@2$1@2$a$7\1L$7@2$1@2$c@1$h0^3^1@2$1@4$b?2HC^1@1$f^3^2@3$h2$0@4$5@2$4$0$2$0@2$3$0$2^5@1$d^1@2$1@2$h1$0@4$5@2$4$0$2$0@2$3$0$2^4@2^3^2^1").

(* [comment removed for export] *)

Lemma mspec_get_bind' {A} (P : assn PState) (f : PState -> MP A) Q :
  (forall s0, mspec (fun s mo => s = s0 /\ P s mo) (f s0) Q) -> mspec P (x <- mget ;; f x) Q.
Proof. intros H s mo HP. unfold mbind, mget. cbn. apply (H s). auto. Qed.

(* [comment removed for export] *)
Theorem raw_malloc_spec_mf : ltac2:(zQ "h00!te!imc!ire!jc!p1!is6!lc!hjd!hld!jga!jh6!jld!jm7!job!jp1!jp7>1X@1$6$0>1G>0$3>0$4P>1n$8>0@1$9^2>0@2$dZ^2@6$a$b$3@1$1$0@2$2^5^4@2$c?2HC^3\1r@1$1$0\1s$3\2mo$4M1\1r@1$1$0P^3\1p$0@2$7@4$2@3$5$0^1^9^8^3^2@2$e^7@2$f+2+jf@4$2^8^7^2^1").
Proof.
  intros X G n HG Hn. unfold raw_malloc.
  apply mspec_get_bind'. intros s0.
  apply mspec_pointwise. intros s1 mo1 [-> ((L & Hc & HK & Hi) & Hnd & HGs)].
  eapply mspec_bind.
  { eapply mspec_pre; [apply (membed_spec_mf (cmalloc (ps_m s0) n) _ G L s0 HG (MI_Contracts.cmalloc_contract_proof _ _ _ Hc Hn))|].
    intros s mo [-> ->]. splits; auto. }
  intros [st' p]. cbn beta iota.
  apply mspec_pointwise. (intros s2 mo2 nd_i9; ndestruct nd_i9 as (L' & Hp & HPost & HK' & HG' & Hm & Hfa & Hso)).
  pose proof (cpath_live _ _ _ _ Hp) as Hlive. cbn [snd] in HPost.
  eapply mspec_seq with (R := fun s mo => s = set_m st' s2 /\ mo = mo2).
  { apply mspec_upd'. intros s mo [-> ->]. auto. }
  intros []. apply mspec_ret. intros s mo [-> ->].
  assert (Hcr : creach st' (match p with Some c => set_live (c :: ld_live L') L' | None => L' end)).
  { exact (creach_malloc _ _ _ _ _ _ Hc Hn Hp). }
  assert (HG2 : G (set_m st' s2) mo2). { apply (HG s2 _ mo2 _); [reflexivity|reflexivity|apply vm_only_refl| exact HG']. }
  destruct p as [c|].
  - split.
    + split; [|split; [|exact HG2]].
      * exists (set_live (c :: ld_live L') L'). split; [exact Hcr|]. split; [apply KLBM_set_live; exact HK'|].
        cbn. intros x [<-|Hx]; [left; reflexivity| right]. rewrite Hlive. apply Hi. exact Hx.
      * cbn. constructor; [|exact Hnd]. intros Hin. apply HPost. rewrite Hlive. apply Hi. exact Hin.
    + destruct (size_overflows n) eqn:E.
      * exfalso. rewrite (cmalloc_overflow _ _ E) in Hp. inversion Hp.
      * unfold size_overflows in E. apply Z.leb_gt in E. lia.
  - split; [|split; [exact Hnd|exact HG2]].
    exists L'. split; [exact Hcr|]. split; [exact HK'|]. cbn. intros x Hx. rewrite Hlive. apply Hi. exact Hx.
Qed.

Theorem raw_free_spec_mf : ltac2:(zQ "b0!te!jpe!ire!jc!is6!lc!p1!jga!jh6!jld!jq5>1X@1$5$0>1G>0$3>0$6P>1p$0>0@1$7^2@6$8$9$3$1@2$2@3$4$0^2^4^3@2$a?2HC^2\0$1@2$2^5^4").
Proof.
  intros X G p HG. unfold raw_free.
  apply mspec_get_bind'. intros s0.
  apply mspec_pointwise. intros s1 mo1 [-> ((L & Hc & HK & Hi) & Hnd & HGs)].
  assert (Hin : In (fst p) (ld_live L)) by (apply Hi; left; reflexivity).
  eapply mspec_bind.
  { eapply mspec_pre; [apply (membed_spec_mf (cfree (ps_m s0) (Some (fst p))) _ G L s0 HG
                               (MI_Contracts.cfree_contract_proof _ _ _ Hc Hin))|].
    intros s mo [-> ->]. splits; auto. }
  intros st'. cbn beta iota.
  apply mspec_pointwise. (intros s2 mo2 nd_i10; ndestruct nd_i10 as (L' & Hp & _ & HK' & HG' & Hm & Hfa & Hso)).
  pose proof (cpath_live _ _ _ _ Hp) as Hlive.
  apply mspec_upd'. intros s mo [-> ->].
  assert (Hcr : creach st' (set_live (ap_remove (fst p) (ld_live L')) L')).
  { exact (creach_free _ _ _ _ _ Hc Hin Hp). }
  split; [|split; [inversion Hnd; assumption| apply (HG s2 _ mo2 _); [reflexivity|reflexivity|apply vm_only_refl| exact HG']]].
  exists (set_live (ap_remove (fst p) (ld_live L')) L'). split; [exact Hcr|]. split; [apply KLBM_set_live; exact HK'|].
  cbn. intros x Hx. rewrite Hlive. apply in_ap_remove.
  - apply Hi. right. exact Hx.
  - inversion Hnd; subst. intros ->. apply H1. exact Hx.
Qed.
End HC.
(* [comment removed for export] *)
