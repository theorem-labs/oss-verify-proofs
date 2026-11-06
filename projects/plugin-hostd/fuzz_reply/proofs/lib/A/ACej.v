(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: re-derived for plugin-hostd/fuzz_reply's asan image by tools/startup/universe.py (sha256 8510965be502; from pautrlen/compose.py over fuzz_reply.asan, hand decisions in decisions.fuzz_reply.asan.json (sha256 b215ef20ad8f; internal record)): CTX_/TRACES_ per fuzz_reply function, 32 allocator traces, Tfib_universe 42; module paths changed *)
(* Modified by Theorem Labs, 2026-10: Tfib_universe_ok states universe_ok over the trace carrier Univ (YG00.v), at univ_of Tfib_universe [] (the fixed traces, no wild prefix; universe.py --carrier univ); its tables are those of --carrier list *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG01.
Import ListNotations.
Local Open Scope Z_scope.
Definition CTX_strndup : list (list Z) :=
[[0x838e4]].
Definition TRACES_strndup : list (list Z) :=
[[0x5408c; 0x427b8; 0x838e4]].
Definition CTX_main : list (list Z) :=
[[0x8c5b4]].
Definition TRACES_main : list (list Z) :=
[[0x53f2c; 0x81f18];
[0x53f2c; 0x82048];
[0x5408c; 0x81ea0];
[0x5408c; 0x81ef4]].
Definition CTX_target_alloc_init : list (list Z) :=
[[0x81fac]].
Definition CTX_target_alloc_count : list (list Z) :=
[[0x81fd0]].
Definition CTX_target_run : list (list Z) :=
[[0x81fc0]].
Definition TRACES_target_run : list (list Z) :=
[[0x53f2c; 0x82214];
[0x5408c; 0x82180]].
Definition CTX_emit_printf : list (list Z) :=
[[0x821f8]].
Definition CTX_relay_finish : list (list Z) :=
[[0x84c74];
[0x84c74; 0x821e8];
[0x84d4c];
[0x84d4c; 0x821e8]].
Definition TRACES_relay_finish : list (list Z) :=
[[0x53f2c; 0x82474; 0x84c74];
[0x53f2c; 0x82474; 0x84c74; 0x821e8];
[0x53f2c; 0x82474; 0x84d4c];
[0x53f2c; 0x82474; 0x84d4c; 0x821e8]].
Definition CTX_gestures_end : list (list Z) :=
[[0x82484; 0x84c74];
[0x82484; 0x84c74; 0x821e8];
[0x82484; 0x84d4c];
[0x82484; 0x84d4c; 0x821e8];
[0x83f74; 0x846c4];
[0x83f74; 0x846c4; 0x821e8];
[0x83f74; 0x849e0];
[0x83f74; 0x849e0; 0x821e8]].
Definition TRACES_gestures_end : list (list Z) :=
[[0x53f2c; 0x82610];
[0x53f2c; 0x82650]].
Definition CTX_relay_event : list (list Z) :=
[[0x84b10];
[0x84b10; 0x821e8]].
Definition CTX_send_line : list (list Z) :=
[[0x825e8];
[0x8271c];
[0x82e90; 0x8483c];
[0x82e90; 0x8483c; 0x821e8];
[0x83748];
[0x857f8]].
Definition TRACES_send_line : list (list Z) :=
[[0x54328; 0x82844]].
Definition CTX_relay_add : list (list Z) :=
[[0x85018]].
Definition TRACES_relay_add : list (list Z) :=
[[0x54328; 0x82a9c; 0x85018]].
Definition CTX_relay_instance_gone : list (list Z) :=
[[0x8483c];
[0x8483c; 0x821e8]].
Definition TRACES_relay_instance_gone : list (list Z) :=
[[0x53f2c; 0x82eb8; 0x8483c];
[0x53f2c; 0x82eb8; 0x8483c; 0x821e8]].
Definition CTX_drain : list (list Z) :=
[[0x82dd0; 0x8483c];
[0x82dd0; 0x8483c; 0x821e8];
[0x83f68; 0x846c4];
[0x83f68; 0x846c4; 0x821e8];
[0x83f68; 0x849e0];
[0x83f68; 0x849e0; 0x821e8];
[0x84a5c];
[0x84a5c; 0x821e8]].
Definition TRACES_drain : list (list Z) :=
[[0x53f2c; 0x8361c];
[0x53f2c; 0x83950];
[0x54328; 0x8324c];
[0x54328; 0x838c4]].
Definition CTX_relay_remove : list (list Z) :=
[[0x846c4];
[0x846c4; 0x821e8];
[0x849e0];
[0x849e0; 0x821e8]].
Definition TRACES_relay_remove : list (list Z) :=
[[0x53f2c; 0x83f98; 0x846c4];
[0x53f2c; 0x83f98; 0x846c4; 0x821e8];
[0x53f2c; 0x83f98; 0x849e0];
[0x53f2c; 0x83f98; 0x849e0; 0x821e8]].
Definition CTX_LLVMFuzzerTestOneInput : list (list Z) :=
[[0x821e8]].
Definition TRACES_LLVMFuzzerTestOneInput : list (list Z) :=
[[0x53f2c; 0x84b20];
[0x53f2c; 0x84b20; 0x821e8];
[0x5408c; 0x84ad0];
[0x5408c; 0x84ad0; 0x821e8]].
Definition CTX_op_add : list (list Z) :=
[[0x84234];
[0x84234; 0x821e8];
[0x8442c];
[0x8442c; 0x821e8]].
Definition TRACES_op_add : list (list Z) :=
[[0x5408c; 0x84fdc]].
Definition CTX_list_push : list (list Z) :=
[[0x834f4];
[0x8448c];
[0x8448c; 0x821e8];
[0x85a9c]].
Definition TRACES_list_push : list (list Z) :=
[[0x5408c; 0x85160];
[0x54328; 0x8513c]].
Definition CTX_check_bounded : list (list Z) :=
[[0x84494];
[0x84494; 0x821e8]].
Definition CTX_check_shape_ends : list (list Z) :=
[[0x848ec];
[0x848ec; 0x821e8];
[0x84a0c];
[0x84a0c; 0x821e8];
[0x84cf4];
[0x84cf4; 0x821e8]].
Definition TRACES_check_shape_ends : list (list Z) :=
[[0x53f2c; 0x8551c];
[0x53f2c; 0x8562c]].
Definition CTX_check_shape_done : list (list Z) :=
[[0x84954];
[0x84954; 0x821e8];
[0x84a14];
[0x84a14; 0x821e8];
[0x84a80];
[0x84a80; 0x821e8];
[0x84b18];
[0x84b18; 0x821e8];
[0x84d54];
[0x84d54; 0x821e8]].
Definition CTX_source_reset : list (list Z) :=
[[0x84a1c];
[0x84a1c; 0x821e8];
[0x84d74];
[0x84d74; 0x821e8];
[0x84fa8]].
Definition TRACES_source_reset : list (list Z) :=
[[0x53f2c; 0x857b0]].
Definition CTX_gesture_end : list (list Z) :=
[[0x825e8];
[0x82e90; 0x8483c];
[0x82e90; 0x8483c; 0x821e8]].
Definition CTX_list_drop : list (list Z) :=
[[0x85a9c]].
Definition TRACES_list_drop : list (list Z) :=
[[0x53f2c; 0x85874]].
Definition CTX_check_no_loss_read : list (list Z) :=
[[0x84858];
[0x84858; 0x821e8];
[0x849ec];
[0x849ec; 0x821e8];
[0x84a6c];
[0x84a6c; 0x821e8]].
Definition CTX_check_no_loss : list (list Z) :=
[[0x848dc];
[0x848dc; 0x821e8];
[0x849f8];
[0x849f8; 0x821e8];
[0x84a78];
[0x84a78; 0x821e8]].
Definition TRACES_check_no_loss : list (list Z) :=
[[0x53f2c; 0x85ac0]].
Definition CTX_gesture_model : list (list Z) :=
[[0x85a9c]].
Definition CTX_next_line : list (list Z) :=
[[0x855ac];
[0x85a34];
[0x85fd8]].
Definition CTX_list_find : list (list Z) :=
[[0x855e4];
[0x85ca8];
[0x85d18]].
Definition CTX_check_shape_event : list (list Z) :=
[[0x84b18];
[0x84b18; 0x821e8]].
Definition CTX_has_prefix : list (list Z) :=
[[0x85480];
[0x85508];
[0x855fc]].
Definition CTX_list_free : list (list Z) :=
[[0x85784];
[0x8578c];
[0x85794]].
Definition TRACES_list_free : list (list Z) :=
[[0x53f2c; 0x86118];
[0x53f2c; 0x86178]].
Definition Tfib_universe : list (list Z) :=
[[0x53f2c];
[0x53f2c; 0x81f18];
[0x53f2c; 0x82048];
[0x53f2c; 0x82214];
[0x53f2c; 0x82474; 0x84c74];
[0x53f2c; 0x82474; 0x84c74; 0x821e8];
[0x53f2c; 0x82474; 0x84d4c];
[0x53f2c; 0x82474; 0x84d4c; 0x821e8];
[0x53f2c; 0x82610];
[0x53f2c; 0x82650];
[0x53f2c; 0x82eb8; 0x8483c];
[0x53f2c; 0x82eb8; 0x8483c; 0x821e8];
[0x53f2c; 0x8361c];
[0x53f2c; 0x83950];
[0x53f2c; 0x83f98; 0x846c4];
[0x53f2c; 0x83f98; 0x846c4; 0x821e8];
[0x53f2c; 0x83f98; 0x849e0];
[0x53f2c; 0x83f98; 0x849e0; 0x821e8];
[0x53f2c; 0x84b20];
[0x53f2c; 0x84b20; 0x821e8];
[0x53f2c; 0x8551c];
[0x53f2c; 0x8562c];
[0x53f2c; 0x857b0];
[0x53f2c; 0x85874];
[0x53f2c; 0x85ac0];
[0x53f2c; 0x86118];
[0x53f2c; 0x86178];
[0x5408c];
[0x5408c; 0x427b8; 0x838e4];
[0x5408c; 0x81ea0];
[0x5408c; 0x81ef4];
[0x5408c; 0x82180];
[0x5408c; 0x84ad0];
[0x5408c; 0x84ad0; 0x821e8];
[0x5408c; 0x84fdc];
[0x5408c; 0x85160];
[0x54328];
[0x54328; 0x82844];
[0x54328; 0x82a9c; 0x85018];
[0x54328; 0x8324c];
[0x54328; 0x838c4];
[0x54328; 0x8513c]].
Fixpoint listZ_eqb (a b : list Z) : bool :=
match a, b with [], [] => true | x :: a', y :: b' => Z.eqb x y && listZ_eqb a' b' | _, _ => false end.
Fixpoint memZL (t : list Z) (l : list (list Z)) : bool :=
match l with [] => false | u :: l' => listZ_eqb t u || memZL t l' end.
Lemma listZ_eqb_eq : forall a b, listZ_eqb a b = true -> a = b.
Proof.
induction a as [|x a IH]; destruct b as [|y b]; cbn; intros H; try discriminate; [reflexivity|].
apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. f_equal; [exact H1 | apply IH, H2].
Qed.
Lemma memZL_In : forall t l, memZL t l = true -> In t l.
Proof.
induction l as [|u l IH]; cbn; intros H; [discriminate|].
apply Bool.orb_prop in H as [H|H]; [left; symmetry; apply listZ_eqb_eq, H | right; apply IH, H].
Qed.
Fixpoint allb {X} (f : X -> bool) (l : list X) : bool := match l with [] => true | x :: l' => f x && allb f l' end.
Lemma allb_In : forall {X} (f : X -> bool) l x, allb f l = true -> In x l -> f x = true.
Proof. induction l; cbn; intros x H Hin; [destruct Hin|]. apply andb_prop in H as [H1 H2]. destruct Hin as [<-|Hin]; auto. Qed.
Lemma TRACES_strndup_U : forall t, In t TRACES_strndup -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_strndup t ltac:(vm_compute; reflexivity) H). Qed.
Lemma TRACES_main_U : forall t, In t TRACES_main -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_main t ltac:(vm_compute; reflexivity) H). Qed.
Lemma TRACES_target_run_U : forall t, In t TRACES_target_run -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_target_run t ltac:(vm_compute; reflexivity) H). Qed.
Lemma TRACES_relay_finish_U : forall t, In t TRACES_relay_finish -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_relay_finish t ltac:(vm_compute; reflexivity) H). Qed.
Lemma TRACES_gestures_end_U : forall t, In t TRACES_gestures_end -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_gestures_end t ltac:(vm_compute; reflexivity) H). Qed.
Lemma TRACES_send_line_U : forall t, In t TRACES_send_line -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_send_line t ltac:(vm_compute; reflexivity) H). Qed.
Lemma TRACES_relay_add_U : forall t, In t TRACES_relay_add -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_relay_add t ltac:(vm_compute; reflexivity) H). Qed.
Lemma TRACES_relay_instance_gone_U : forall t, In t TRACES_relay_instance_gone -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_relay_instance_gone t ltac:(vm_compute; reflexivity) H). Qed.
Lemma TRACES_drain_U : forall t, In t TRACES_drain -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_drain t ltac:(vm_compute; reflexivity) H). Qed.
Lemma TRACES_relay_remove_U : forall t, In t TRACES_relay_remove -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_relay_remove t ltac:(vm_compute; reflexivity) H). Qed.
Lemma TRACES_LLVMFuzzerTestOneInput_U : forall t, In t TRACES_LLVMFuzzerTestOneInput -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_LLVMFuzzerTestOneInput t ltac:(vm_compute; reflexivity) H). Qed.
Lemma TRACES_op_add_U : forall t, In t TRACES_op_add -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_op_add t ltac:(vm_compute; reflexivity) H). Qed.
Lemma TRACES_list_push_U : forall t, In t TRACES_list_push -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_list_push t ltac:(vm_compute; reflexivity) H). Qed.
Lemma TRACES_check_shape_ends_U : forall t, In t TRACES_check_shape_ends -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_check_shape_ends t ltac:(vm_compute; reflexivity) H). Qed.
Lemma TRACES_source_reset_U : forall t, In t TRACES_source_reset -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_source_reset t ltac:(vm_compute; reflexivity) H). Qed.
Lemma TRACES_list_drop_U : forall t, In t TRACES_list_drop -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_list_drop t ltac:(vm_compute; reflexivity) H). Qed.
Lemma TRACES_check_no_loss_U : forall t, In t TRACES_check_no_loss -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_check_no_loss t ltac:(vm_compute; reflexivity) H). Qed.
Lemma TRACES_list_free_U : forall t, In t TRACES_list_free -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_list_free t ltac:(vm_compute; reflexivity) H). Qed.
Fixpoint nodupZL (l : list (list Z)) : bool :=
match l with [] => true | t :: l' => negb (memZL t l') && nodupZL l' end.
Lemma memZL_false : forall t l, memZL t l = false -> ~ In t l.
Proof.
induction l as [|u l IH]; cbn; intros H Hin; [exact Hin|].
apply Bool.orb_false_elim in H as [H1 H2]. destruct Hin as [<-|Hin]; [|exact (IH H2 Hin)].
assert (E : forall a, listZ_eqb a a = true) by (induction a; cbn; [reflexivity|]; rewrite Z.eqb_refl; assumption).
rewrite E in H1. discriminate.
Qed.
Lemma nodupZL_NoDup : forall l, nodupZL l = true -> NoDup l.
Proof.
induction l as [|t l IH]; cbn; intros H; [constructor|].
apply andb_prop in H as [H1 H2]. constructor; [apply memZL_false; destruct (memZL t l); [discriminate|reflexivity] | apply IH, H2].
Qed.
Lemma Tfib_universe_ok : universe_ok (univ_of Tfib_universe []).
Proof.
apply univ_of_ok.
- unfold DEPOT_MAX. apply Z.leb_le. vm_compute. reflexivity.
- apply Forall_forall. intros t Ht.
pose proof (allb_In (fun t : list Z => (length t <=? kUnwindMax)%nat) Tfib_universe t ltac:(vm_compute; reflexivity) Ht) as H.
apply Nat.leb_le in H. exact H.
- apply nodupZL_NoDup. vm_compute. reflexivity.
Qed.
