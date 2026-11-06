(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad MSafe MSafeP MPaths STree Malloc KInv KStep PState KLink KEv StepB MI_NN.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Malloc Require Import ProgDeps.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma tpath_msys_mret {A B} : forall n (dec : resp -> option A) (g : A -> B) (s s' : PState) mo tr (b : B) mo',
  tpath nstepP (mbind (msys n dec) (fun a => mret (g a)) s) mo tr (Ok (b, s')) mo' ->
  exists rsp a, nstepP n mo rsp mo' tr /\ dec rsp = Some a /\ b = g a /\ s' = s.
Proof.
  intros n dec g s s' mo tr b mo' Hp.
  apply tpath_mbind_ok in Hp as (tr1 & a & s1 & mo1 & tr2 & H1 & H2 & ->).
  apply tpath_msys_ok in H1 as (rsp & Hst & Hd & ->).
  apply (tpath_mret (st:=nstepP)) in H2 as (E & -> & ->). injection E as -> ->.
  exists rsp, a. rewrite app_nil_r. auto.
Qed.

Lemma is_err_false_of_ceiling : forall x len atop, 0 < len -> atop < 2^63 -> x + mmap_len len <= atop -> is_err x = false.
Proof.
  intros x len atop Hlen Hat Hc. pose proof (mmap_len_ge len Hlen).
  unfold is_err, TWO64. apply Z.ltb_ge. lia.
Qed.

(* [comment removed for export] *)
Lemma ev_step_okz : forall L e s mo tr z s' mo' atop, atop < 2^63 ->
  event_pre L e -> tpath nstepP (ev_step atop e s) mo tr (Ok (z, s')) mo' -> okz e z.
Proof.
  intros L e s mo tr z s' mo' atop Hat Hpre Hp. destruct e as [req|addr len prot flags|addr len|addr len prot|? ? ?|?]; cbn [okz]; try exact I.
  - (* [comment removed for export] *)
    unfold ev_step in Hp. change MAP_FIXED_Z with MAP_FIXED in Hp.
    destruct (Z.land flags MAP_FIXED =? 0) eqn:EF; [| left; reflexivity]. right. cbn [negb] in Hp.
    cbn [event_pre] in Hpre. destruct Hpre as [(Hq & -> & -> & Hprot & Hlen)|(cur & _ & _ & _ & _ & ->)].
    2:{ exfalso. revert EF. cbv. discriminate. }
    destruct (prot =? 0).
    + apply tpath_msys_mret in Hp as (rsp & a & [Hst HnP] & Hd & -> & ->).
      specialize (HnP I). apply dec_mmap_none_Some in Hd as (ci & Hd).
      destruct a as [e|x].
      * destruct Hd as [-> He]. exfalso. cbn [eff_ret efferr_ci eff0_ci] in HnP. rewrite errno_of_errno_ret in HnP by lia. discriminate.
      * destruct Hd as [_ Hok]. apply mmap_addr_ok_true in Hok as [(_ & _ & Hc) _]. eapply is_err_false_of_ceiling; [| exact Hat| exact Hc]. lia.
    + apply tpath_msys_mret in Hp as (rsp & a & [Hst HnP] & Hd & -> & ->).
      specialize (HnP I). apply dec_mmap_Some in Hd as (ci & Hd).
      destruct a as [e|x].
      * destruct Hd as [-> He]. exfalso. cbn [eff_ret efferr_ci eff0_ci] in HnP. rewrite errno_of_errno_ret in HnP by lia. discriminate.
      * destruct Hd as [_ Hok]. apply mmap_addr_ok_true in Hok as [(_ & _ & Hc) _]. eapply is_err_false_of_ceiling; [| exact Hat| exact Hc]. lia.
  - (* [comment removed for export] *)
    unfold ev_step in Hp. apply tpath_msys_mret in Hp as (rsp & a & [Hst HnP] & Hd & -> & ->).
    specialize (HnP I). unfold dec_mprotect_rw in Hd.
    destruct (dec_mprotect addr len rsp) as [[e|[|]]|] eqn:Hd0; try discriminate.
    + exfalso. apply dec_mprotect_Some in Hd0 as (ci & -> & He). cbn [eff_ret efferr_ci eff0_ci] in HnP.
      rewrite errno_of_errno_ret in HnP by lia. discriminate.
    + injection Hd as <-. reflexivity.
  - (* [comment removed for export] *)
    unfold ev_step in Hp. apply (tpath_munr (st:=nstepP)) in Hp as (E & _). discriminate.
Qed.

(* [comment removed for export] *)
Lemma ev_step_specP : forall L e (G : PState -> Model -> Prop) s0,
  frame_ok G -> event_pre L e ->
  mspecP (fun s mo => s = s0 /\ KL L (ps_brk s) mo /\ G s mo) (ev_step (ld_atop L) e)
         (fun z s mo => ev_step_post L e G s0 z s mo /\ okz e z).
Proof.
  intros L e G s0 HG Hpre.
  eapply mspecP_post.
  - eapply (mspecP_paths _ _ _ (fun z _ => okz e z)).
    + apply mspec_mspecP. apply ev_step_spec; assumption.
    + intros s mo tr z s' mo' (_ & HK & _) Hp. eapply ev_step_okz; [exact (proj2 (KL_atop_lt _ _ _ HK))| exact Hpre| exact Hp].
  - intros z s mo [H1 H2]. split; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma membed_specP {R} : forall (t : stree ev Z R) (Post : mled -> R -> Prop) (P : R -> Prop) (G : PState -> Model -> Prop) L s0,
  frame_ok G -> ctree_ok L t Post -> nn P t ->
  mspecP (fun s mo => s = s0 /\ KL L (ps_brk s) mo /\ G s mo) (membed (ld_atop L) t)
         (fun r s mo => (exists L', cpath L t L' r /\ Post L' r /\ KL L' (ps_brk s) mo /\ G s mo
                        /\ ps_m s = ps_m s0 /\ ps_fa s = ps_fa s0 /\ ps_so s = ps_so s0) /\ P r).
Proof.
  intros t. induction t as [r|e k IH]; intros Post P G L s0 HG Hok Hnn.
  - cbn [membed]. apply mspecP_ret. intros s mo (-> & HK & HGs). split; [| exact Hnn]. exists L.
    split; [constructor|]. cbn in Hok. splits; auto.
  - cbn [membed]. cbn in Hok. destruct Hok as [Hpre Hk]. cbn [nn] in Hnn.
    eapply mspecP_bind; [apply (ev_step_specP L e G s0 HG Hpre)|].
    intros z. unfold ev_step_post. apply mspecP_pointwise. intros s1 mo1 ((Hans & HK1 & HG1 & Hm & Hfa & Hso) & Hz).
    rewrite <- (event_post_atop L e z).
    eapply mspecP_conseq; [apply (IH z Post P G (event_post L e z) s1 HG (Hk z Hans) (Hnn z Hz))| |].
    + intros s mo [-> ->]. auto.
    + intros r s mo [(L' & Hp & HP & HK & HG' & Hm' & Hfa' & Hso') HPr]. split; [| exact HPr]. exists L'. split; [econstructor; eauto|].
      splits; auto; congruence.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem raw_malloc_specP : forall X G n, frame_ok G -> 0 <= n -> size_overflows n = false ->
  mspecP (OWN X G) (raw_malloc n)
         (fun r s mo => match r with
                        | Some p => OWN (p :: X) G s mo /\ n < 2^63
                        | None => False
                        end).
Proof.
  intros X G n HG Hn Hov. unfold raw_malloc.
  eapply mspecP_bind; [apply mspecP_get|]. intros s0.
  apply mspecP_pointwise. intros s1 mo1 [-> [(L & Hc & HK & Hi) [Hnd HGs]]].
  eapply mspecP_bind.
  { rewrite (MI_Contracts.creach_atop _ _ Hc).
    eapply mspecP_pre; [apply (membed_specP (cmalloc (ps_m s1) n) _ _ G L s1 HG (MI_Contracts.cmalloc_contract_proof _ _ _ Hc Hn) (cmalloc_nn (ps_m s1) n Hov))|].
    intros s mo [-> ->]. auto. }
  intros [st' p]. cbn beta iota.
  apply mspecP_pointwise. intros s2 mo2 [(L' & Hp & HPost & HK' & HG' & Hm & Hfa & Hso) HNN]. cbn [snd] in HPost, HNN.
  eapply mspecP_seq with (R := fun s mo => s = set_m st' s2 /\ mo = mo2).
  { apply mspecP_upd'. intros s mo [-> ->]. auto. }
  intros _. apply mspecP_ret. intros s mo [-> ->].
  destruct p as [c|]; [| exfalso; apply HNN; reflexivity].
  pose proof (cpath_live _ _ _ _ Hp) as Hlive.
  assert (Hcr : creach st' (set_live (c :: ld_live L') L')).
  { exact (creach_malloc _ _ _ _ _ (Some c) Hc Hn Hp). }
  assert (HG2 : G (set_m st' s2) mo2). { apply (HG s2 _ mo2 _); [reflexivity|reflexivity|apply vm_only_refl| exact HG']. }
  split.
  - split; [|split; [|exact HG2]].
    + exists (set_live (c :: ld_live L') L'). split; [exact Hcr|]. split; [apply KL_set_live; exact HK'|].
      cbn. intros x [<-|Hx]; [left; reflexivity| right]. rewrite Hlive. apply Hi. exact Hx.
    + cbn. constructor; [|exact Hnd]. intros Hin. apply HPost. rewrite Hlive. apply Hi. exact Hin.
  - unfold size_overflows in Hov. apply Z.leb_gt in Hov. lia.
Qed.

Theorem raw_free_specP : forall X G p, frame_ok G ->
  mspecP (OWN (p :: X) G) (raw_free p) (fun _ => OWN X G).
Proof. intros X G p HG. apply mspec_mspecP. apply raw_free_spec. exact HG. Qed.

(* [comment removed for export] *)
Theorem raw_malloc_specP_weak : forall X G n, frame_ok G -> 0 <= n ->
  mspecP (OWN X G) (raw_malloc n)
         (fun r s mo => match r with
                        | Some p => OWN (p :: X) G s mo /\ n < 2^63
                        | None => OWN X G s mo
                        end).
Proof. intros X G n HG Hn. apply mspec_mspecP. apply raw_malloc_spec; assumption. Qed.
