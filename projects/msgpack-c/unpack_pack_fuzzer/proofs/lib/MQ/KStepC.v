(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import PropExec MState ITree Nodes NodesM Decode DecodeM.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc Require Import Prelim STree Malloc KInv.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require Import Monad MSafe Prog KLink KStep.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc Require MI_Contracts.

Set Keyed Unification.
Import ListNotations.
Import ITree.Exc.
Local Open Scope Z_scope.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import CeilLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Lemma raw_malloc_spec_c : forall X G n, frame_ok G -> 0 <= n ->
  mspec (OWN X G) (raw_malloc n)
        (fun r s mo => match r with
                       | Some p => OWN (p :: X) G s mo /\ n < 2^63
                       | None => OWN X G s mo
                       end).
Proof.
  intros X G n HG Hn. unfold raw_malloc.
  eapply mspec_bind; [apply mspec_get|]. intros s0.
  apply mspec_pointwise. intros s1 mo1 [-> [(L & Hc & HK & Hi) [Hnd HGs]]].
  eapply mspec_bind.
  { eapply mspec_pre; [apply (membed_spec (cmalloc (ps_m s1) n) _ G L s1 HG (MI_Contracts.cmalloc_contract_proof _ _ _ Hc Hn))|].
    intros s mo [-> ->]. auto. }
  intros [st' p]. cbn beta iota.
  apply mspec_pointwise. intros s2 mo2 (L' & Hp & HPost & HK' & HG' & Hm & Hfa & Hso).
  pose proof (cpath_live _ _ _ _ Hp) as Hlive. cbn [snd] in HPost.
  eapply mspec_seq with (R := fun s mo => s = set_m st' s2 /\ mo = mo2).
  { apply mspec_upd'. intros s mo [-> ->]. auto. }
  intros _. apply mspec_ret. intros s mo [-> ->].
  assert (Hcr : creach st' (match p with Some c => set_live (c :: ld_live L') L' | None => L' end)).
  { exact (creach_malloc _ _ _ _ _ _ Hc Hn Hp). }
  assert (HG2 : G (set_m st' s2) mo2). { apply (HG s2 _ mo2 _); [reflexivity|reflexivity|apply vm_only_refl| exact HG']. }
  destruct p as [c|].
  - split.
    + split; [|split; [|exact HG2]].
      * exists (set_live (c :: ld_live L') L'). split; [exact Hcr|]. split; [apply KL_set_live; exact HK'|].
        cbn. intros x [<-|Hx]; [left; reflexivity| right]. rewrite Hlive. apply Hi. exact Hx.
      * cbn. constructor; [|exact Hnd]. intros Hin. apply HPost. rewrite Hlive. apply Hi. exact Hin.
    + destruct (size_overflows n) eqn:E.
      * exfalso. rewrite (cmalloc_overflow _ _ E) in Hp. inversion Hp.
      * unfold size_overflows in E. apply Z.leb_gt in E. lia.
  - split; [|split; [exact Hnd| exact HG2]].
    exists L'. split; [exact Hcr|]. split; [exact HK'|]. rewrite Hlive. exact Hi.
Qed.

Lemma raw_free_spec_c : forall X G p, frame_ok G ->
  mspec (OWN (p :: X) G) (raw_free p) (fun _ => OWN X G).
Proof.
  intros X G p HG. unfold raw_free.
  eapply mspec_bind; [apply mspec_get|]. intros s0.
  apply mspec_pointwise. intros s1 mo1 [-> [(L & Hc & HK & Hi) [Hnd HGs]]].
  assert (Hin : In (fst p) (ld_live L)) by (apply Hi; left; reflexivity).
  eapply mspec_bind.
  { eapply mspec_pre; [apply (membed_spec (cfree (ps_m s1) (Some (fst p))) _ G L s1 HG (MI_Contracts.cfree_contract_proof _ _ _ Hc Hin))|].
    intros s mo [-> ->]. auto. }
  intros st'. cbn beta iota.
  apply mspec_pointwise. intros s2 mo2 (L' & Hp & _ & HK' & HG' & Hm & Hfa & Hso).
  pose proof (cpath_live _ _ _ _ Hp) as Hlive.
  apply mspec_upd'. intros s mo [-> ->].
  assert (Hcr : creach st' (set_live (ap_remove (fst p) (ld_live L')) L')).
  { exact (creach_free _ _ _ _ _ Hc Hin Hp). }
  split; [|split; [inversion Hnd; assumption| apply (HG s2 _ mo2 _); [reflexivity|reflexivity|apply vm_only_refl| exact HG']]].
  exists (set_live (ap_remove (fst p) (ld_live L')) L'). split; [exact Hcr|]. split; [apply KL_set_live; exact HK'|].
  cbn. intros x Hx. rewrite Hlive. apply in_ap_remove.
  - apply Hi. right. exact Hx.
  - inversion Hnd; subst. intros ->. apply H1. exact Hx.
Qed.

End CEIL.
