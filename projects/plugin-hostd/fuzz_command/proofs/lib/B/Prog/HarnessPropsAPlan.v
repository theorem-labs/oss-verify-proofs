(* What the daemon's plan of one message is, for any value of atoi.

   The released plain proof states the plan of a message (pspec, lib/Prog/HarnessPropsProof.v:1110-1154) and proves
   that Verbs.plan computes it (pspec_holds :1158-1242, receive_spec :1244-1250) with musl's atoi value atoi_val
   fixed. Those proofs read no property of atoi: the plan and the after-reply call (lib/Spec/Verbs.v:245-319) take
   atoi as a parameter, and each step that reads its value is a case split on it. This file states the same plan
   with atoi a parameter, so that the ASan build's atoi wrapper (atoi_a, lib/B/Prog/sup_reply_code_c.v:61) can use it,
   and reuses every atoi-free lemma of the plain proof by Require. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel check_arity_c
  HarnessPropsProof.
Import ListNotations.
Open Scope Z_scope.

Section plan.
Variable atoi : list byte -> Z.

(* the plain after_none and after_bc (HarnessPropsProof.v:1074-1088) at any atoi *)
Lemma after_none_at : forall v args,
  (Verbs.verb_is_m v Verbs.Lit.fmt_preset_load || Verbs.verb_is_m v Verbs.Lit.fmt_patch_set) = false ->
  Verbs.after atoi (v :: args) = None.
Proof. intros v [|a args] H; [reflexivity|]. unfold Verbs.after. rewrite H. reflexivity. Qed.

Lemma after_bc_at : forall v args, tokp v -> Verbs.is_instance_verb v = false -> Verbs.after atoi (v :: args) = None.
Proof.
  intros v [|a args] Tv H; [reflexivity|]. unfold Verbs.after.
  destruct Verbs.format_words as (_ & _ & _ & _ & FW5 & FW6).
  destruct (Verbs.verb_is_m v Verbs.Lit.fmt_preset_load) eqn:E1.
  { apply (Verbs.verb_is_m_token v _ Tv) in E1. rewrite FW5 in E1. subst v. vm_compute in H. discriminate H. }
  destruct (Verbs.verb_is_m v Verbs.Lit.fmt_patch_set) eqn:E2.
  { apply (Verbs.verb_is_m_token v _ Tv) in E2. rewrite FW6 in E2. subst v. vm_compute in H. discriminate H. }
  reflexivity.
Qed.

(* the plain pspec (HarnessPropsProof.v:1110-1154) with atoi in place of atoi_val *)
Inductive pspec_at (ln : list byte) : list (list byte) -> Verbs.step -> option (Z * list byte) -> Prop :=
| pa_rej : forall tk, pspec_at ln tk Verbs.reject None
| pa_add2 : forall u i, pspec_at ln [Verbs.Lit.verb_add; u; i] (Verbs.SAdd u (atoi i) None None) None
| pa_add3p : forall u i x, Verbs.is_placement_m x = true ->
    pspec_at ln [Verbs.Lit.verb_add; u; i; x] (Verbs.SAdd u (atoi i) (Some x) None) None
| pa_add3c : forall u i x, Verbs.is_placement_m x = false ->
    pspec_at ln [Verbs.Lit.verb_add; u; i; x] (Verbs.SAdd u (atoi i) None (Some x)) None
| pa_add4 : forall u i x y, Verbs.is_placement_m x = true ->
    pspec_at ln [Verbs.Lit.verb_add; u; i; x; y] (Verbs.SAdd u (atoi i) (Some x) (Some y)) None
| pa_dget : forall a, pspec_at ln [Verbs.Lit.verb_descriptor_get; a] (Verbs.SCall (Verbs.descriptors_get a)) None
| pa_pget : forall a, pspec_at ln [Verbs.Lit.verb_panel_get; a] (Verbs.SCall (Verbs.descriptors_panel_get a)) None
| pa_remall : forall a, pspec_at ln [Verbs.Lit.verb_remove; a] (Verbs.SCall Verbs.sup_remove_all) None
| pa_rem : forall a, pspec_at ln [Verbs.Lit.verb_remove; a] (Verbs.SCall (Verbs.sup_remove (atoi a))) None
| pa_wlist : pspec_at ln [Verbs.Lit.verb_worker_list] (Verbs.SCall Verbs.sup_worker_list) None
| pa_iinfo : forall a,
    pspec_at ln [Verbs.Lit.verb_instance_info; a] (Verbs.SCall (Verbs.sup_instance_info (atoi a))) None
| pa_reset0 : pspec_at ln [Verbs.Lit.verb_supervisor_reset] (Verbs.SCall (Verbs.sup_reset Verbs.Lit.word_all)) None
| pa_reset1 : forall a, pspec_at ln [Verbs.Lit.verb_supervisor_reset; a] (Verbs.SCall (Verbs.sup_reset a)) None
| pa_qclear : forall a,
    pspec_at ln [Verbs.Lit.verb_quarantine_clear; a] (Verbs.SCall (Verbs.sup_quarantine_clear a)) None
| pa_policy : forall a b,
    pspec_at ln [Verbs.Lit.verb_policy_set; a; b] (Verbs.SCall (Verbs.sup_policy_set a b)) None
| pa_lv2 : forall a b,
    pspec_at ln [Verbs.Lit.verb_lv2_worker_set; a; b] (Verbs.SCall (Verbs.sup_lv2_worker_set a b)) None
| pa_pool : forall a b,
    pspec_at ln [Verbs.Lit.verb_pool_config; a; b] (Verbs.SCall (Verbs.sup_pool_config a (atoi b))) None
| pa_env : forall a b c,
    pspec_at ln [Verbs.Lit.verb_worker_env; a; b; c] (Verbs.SCall (Verbs.sup_worker_env a b c)) None
| pa_chain : forall a rest id ids, rest <> [] -> Verbs.number_m a = Some id -> Verbs.numbers_m rest = Some ids ->
    pspec_at ln (Verbs.Lit.verb_chain :: a :: rest) (Verbs.SCall (Verbs.sup_chain id ids)) None
| pa_cclear : forall a id, Verbs.number_m a = Some id ->
    pspec_at ln [Verbs.Lit.verb_chain_clear; a] (Verbs.SCall (Verbs.sup_chain_clear id)) None
| pa_pin3 : forall u f l, pspec_at ln [Verbs.Lit.verb_pin_set; u; f; l] (Verbs.SPinSet u f l None) None
| pa_pin4 : forall u f l vd, Verbs.has_prefix Verbs.Lit.word_verdict vd = true ->
    pspec_at ln [Verbs.Lit.verb_pin_set; u; f; l; vd] (Verbs.SPinSet u f l (Some (skipn 8 vd))) None
| pa_paccept : forall a, pspec_at ln [Verbs.Lit.verb_pin_accept; a] (Verbs.SCall (Verbs.sup_pin_accept a)) None
| pa_pclear : forall a, pspec_at ln [Verbs.Lit.verb_pin_clear; a] (Verbs.SPinClear a) None
| pa_quit : pspec_at ln [Verbs.Lit.verb_quit] Verbs.SQuit None
| pa_ledger : forall v args led, Verbs.ledger_of v Verbs.Lit.instance_info_verbs = Some led ->
    pspec_at ln (v :: args) (Verbs.SCall (Verbs.sup_instance_verb ln led)) (Verbs.after atoi (v :: args))
| pa_bc0 : forall v, afree v -> pspec_at ln [v] (Verbs.SBroadcast ln [v]) None
| pa_call : forall v a rest, row_find v parsed_rows = None ->
    pspec_at ln (v :: a :: rest) (Verbs.SCall (Verbs.sup_call (atoi a) ln)) (Verbs.after atoi (v :: a :: rest))
| pa_conn : forall v a b, v = Verbs.Lit.verb_connect \/ v = Verbs.Lit.verb_disconnect ->
    pspec_at ln [v; a; b] (Verbs.SCall (Verbs.sup_connect v ln a b)) None
| pa_bc : forall v a rest, afree v -> pspec_at ln (v :: a :: rest) (Verbs.SBroadcast ln (v :: a :: rest)) None.

(* the plain pspec_holds (HarnessPropsProof.v:1158-1242), the same proof at any atoi *)
Lemma pspec_holds_at : forall ln tk, (forall t, In t tk -> tokp t) ->
  pspec_at ln tk (Verbs.plan atoi ln tk) (Verbs.after atoi tk).
Proof.
  intros ln tk Htk. destruct tk as [|v args]; [apply pa_rej|].
  assert (Tv : tokp v) by (apply Htk; left; reflexivity).
  destruct Verbs.format_words as (FW1 & FW2 & FW3 & FW4 & FW5 & FW6).
  unfold Verbs.plan.
  destruct (Verbs.list_eqb v Verbs.Lit.verb_add) eqn:E1.
  { apply Verbs.list_eqb_eq in E1. subst v. rewrite after_none_at by (vm_compute; reflexivity).
    unfold Verbs.add_m. destruct args as [|u [|i [|x [|y [|z rest]]]]]; cbv beta iota; try apply pa_rej.
    - apply pa_add2.
    - destruct (Verbs.is_placement_m x) eqn:P; [apply pa_add3p | apply pa_add3c]; exact P.
    - destruct (Verbs.is_placement_m x) eqn:P; [apply pa_add4; exact P | apply pa_rej]. }
  destruct (Verbs.list_eqb v Verbs.Lit.verb_descriptor_get) eqn:E2.
  { apply Verbs.list_eqb_eq in E2. subst v. rewrite after_none_at by (vm_compute; reflexivity).
    destruct args as [|a [|b rest]]; cbv beta iota; try apply pa_rej. apply pa_dget. }
  destruct (Verbs.list_eqb v Verbs.Lit.verb_panel_get) eqn:E3.
  { apply Verbs.list_eqb_eq in E3. subst v. rewrite after_none_at by (vm_compute; reflexivity).
    destruct args as [|a [|b rest]]; cbv beta iota; try apply pa_rej. apply pa_pget. }
  destruct (Verbs.verb_is_m v Verbs.Lit.fmt_remove) eqn:E4.
  { apply (Verbs.verb_is_m_token v _ Tv) in E4. rewrite FW1 in E4. subst v.
    rewrite after_none_at by (vm_compute; reflexivity).
    destruct args as [|a [|b rest]]; cbv beta iota; try apply pa_rej.
    destruct (atoi a =? -1); [apply pa_remall | apply pa_rem]. }
  destruct (Verbs.list_eqb v Verbs.Lit.verb_worker_list) eqn:E5.
  { apply Verbs.list_eqb_eq in E5. subst v. rewrite after_none_at by (vm_compute; reflexivity).
    destruct args as [|a rest]; cbv beta iota; try apply pa_rej. apply pa_wlist. }
  destruct (Verbs.list_eqb v Verbs.Lit.verb_instance_info) eqn:E6.
  { apply Verbs.list_eqb_eq in E6. subst v. rewrite after_none_at by (vm_compute; reflexivity).
    destruct args as [|a [|b rest]]; cbv beta iota; try apply pa_rej. apply pa_iinfo. }
  destruct (Verbs.list_eqb v Verbs.Lit.verb_supervisor_reset) eqn:E7.
  { apply Verbs.list_eqb_eq in E7. subst v. rewrite after_none_at by (vm_compute; reflexivity).
    destruct args as [|a [|b rest]]; cbv beta iota; try apply pa_rej; [apply pa_reset0 | apply pa_reset1]. }
  destruct (Verbs.list_eqb v Verbs.Lit.verb_quarantine_clear) eqn:E8.
  { apply Verbs.list_eqb_eq in E8. subst v. rewrite after_none_at by (vm_compute; reflexivity).
    destruct args as [|a [|b rest]]; cbv beta iota; try apply pa_rej. apply pa_qclear. }
  destruct (Verbs.list_eqb v Verbs.Lit.verb_policy_set) eqn:E9.
  { apply Verbs.list_eqb_eq in E9. subst v. rewrite after_none_at by (vm_compute; reflexivity).
    destruct args as [|a [|b [|c rest]]]; cbv beta iota; try apply pa_rej. apply pa_policy. }
  destruct (Verbs.list_eqb v Verbs.Lit.verb_lv2_worker_set) eqn:E10.
  { apply Verbs.list_eqb_eq in E10. subst v. rewrite after_none_at by (vm_compute; reflexivity).
    destruct args as [|a [|b [|c rest]]]; cbv beta iota; try apply pa_rej. apply pa_lv2. }
  destruct (Verbs.list_eqb v Verbs.Lit.verb_pool_config) eqn:E11.
  { apply Verbs.list_eqb_eq in E11. subst v. rewrite after_none_at by (vm_compute; reflexivity).
    destruct args as [|a [|b [|c rest]]]; cbv beta iota; try apply pa_rej. apply pa_pool. }
  destruct (Verbs.list_eqb v Verbs.Lit.verb_worker_env) eqn:E12.
  { apply Verbs.list_eqb_eq in E12. subst v. rewrite after_none_at by (vm_compute; reflexivity).
    destruct args as [|a [|b [|c [|d rest]]]]; cbv beta iota; try apply pa_rej. apply pa_env. }
  destruct (Verbs.list_eqb v Verbs.Lit.verb_chain) eqn:E13.
  { apply Verbs.list_eqb_eq in E13. subst v. rewrite after_none_at by (vm_compute; reflexivity).
    unfold Verbs.chain_words_m. destruct args as [|a [|b rest]]; cbv beta iota; try apply pa_rej.
    destruct (Verbs.number_m a) as [id|] eqn:N1; [|apply pa_rej].
    destruct (Verbs.numbers_m (b :: rest)) as [ids|] eqn:N2; [|apply pa_rej].
    apply pa_chain; [discriminate|exact N1|exact N2]. }
  destruct (Verbs.list_eqb v Verbs.Lit.verb_chain_clear) eqn:E14.
  { apply Verbs.list_eqb_eq in E14. subst v. rewrite after_none_at by (vm_compute; reflexivity).
    destruct args as [|a [|b rest]]; cbv beta iota; try apply pa_rej.
    destruct (Verbs.number_m a) as [id|] eqn:N; [apply pa_cclear; exact N|apply pa_rej]. }
  destruct (Verbs.list_eqb v Verbs.Lit.verb_pin_set) eqn:E15.
  { apply Verbs.list_eqb_eq in E15. subst v. rewrite after_none_at by (vm_compute; reflexivity).
    unfold Verbs.pin_set_words_m. destruct args as [|u [|f [|l [|vd [|z rest]]]]]; cbv beta iota; try apply pa_rej.
    - dif; [apply pa_rej|apply pa_pin3].
    - dif; [apply pa_rej|]. dif; [apply pa_pin4; assumption|apply pa_rej]. }
  destruct (Verbs.list_eqb v Verbs.Lit.verb_pin_accept) eqn:E16.
  { apply Verbs.list_eqb_eq in E16. subst v. rewrite after_none_at by (vm_compute; reflexivity).
    destruct args as [|a [|b rest]]; cbv beta iota; try apply pa_rej. apply pa_paccept. }
  destruct (Verbs.list_eqb v Verbs.Lit.verb_pin_clear) eqn:E17.
  { apply Verbs.list_eqb_eq in E17. subst v. rewrite after_none_at by (vm_compute; reflexivity).
    destruct args as [|a [|b rest]]; cbv beta iota; try apply pa_rej. apply pa_pclear. }
  destruct (Verbs.verb_is_m v Verbs.Lit.fmt_quit) eqn:E18.
  { apply (Verbs.verb_is_m_token v _ Tv) in E18. rewrite FW2 in E18. subst v.
    rewrite after_none_at by (vm_compute; reflexivity).
    destruct args as [|a rest]; cbv beta iota; try apply pa_rej. apply pa_quit. }
  assert (EV : early v = false) by (unfold early; rewrite E1, E2, E3, E4, E5, E6, E7, E8, E9, E10, E11, E12,
    E13, E14, E15, E16, E17, E18; reflexivity).
  destruct (Verbs.ledger_of v Verbs.Lit.instance_info_verbs) as [led|] eqn:EL; [apply pa_ledger; exact EL|].
  destruct args as [|a rest]; [apply pa_bc0; apply afree_of; exact EV|].
  destruct (Verbs.is_instance_verb v) eqn:EI; [apply pa_call; apply inst_row_none; assumption|].
  rewrite (after_bc_at v (a :: rest) Tv EI).
  destruct rest as [|b [|c rest']]; [apply pa_bc; apply afree_of; exact EV| |apply pa_bc; apply afree_of; exact EV].
  destruct (Verbs.verb_is_m v Verbs.Lit.fmt_connect || Verbs.verb_is_m v Verbs.Lit.fmt_disconnect) eqn:EC;
    [|apply pa_bc; apply afree_of; exact EV].
  apply pa_conn. apply orb_true_iff in EC. destruct EC as [EC|EC]; apply (Verbs.verb_is_m_token v _ Tv) in EC;
    [left; rewrite <- FW3 | right; rewrite <- FW4]; exact EC.
Qed.

(* the plain receive_spec (HarnessPropsProof.v:1244-1250) at any atoi *)
Lemma receive_spec_at : forall D,
  pspec_at (Verbs.line D) (Verbs.toks D) (fst (Verbs.receive atoi D)) (snd (Verbs.receive atoi D)).
Proof.
  intros D. unfold Verbs.receive. destruct (Verbs.toks D) as [|t tl] eqn:Et; [apply pa_rej|].
  apply pspec_holds_at. intros t' Ht'. rewrite <- Et in Ht'. destruct (Verbs.toks_word D t' Ht') as [_ H].
  intros b Hb. destruct (H b Hb) as (H1 & H2 & _). split; assumption.
Qed.

End plan.
