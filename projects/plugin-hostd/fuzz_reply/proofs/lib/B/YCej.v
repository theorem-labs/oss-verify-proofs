(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: re-derived for plugin-hostd/fuzz_reply's asan-ubsan image by tools/startup/universe.py (sha256 8510965be502; pautrlen/compose.py over fuzz_reply.asan-ubsan; hand decisions in traces/decisions.fuzz_reply.asan-ubsan.json): 25 allocator traces, Tfib_universe 31; module paths changed *)
(* Modified by Theorem Labs, 2026-10: Tfib_universe_ok states universe_ok over the trace carrier Univ (YG00.v), at univ_of Tfib_universe [] (the fixed traces, no wild prefix; universe.py --carrier univ); its tables are those of --carrier list *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG01.
Import ListNotations.
Local Open Scope Z_scope.
Definition CTX_strndup : list (list Z) :=
[[0x83c0c]].
Definition TRACES_strndup : list (list Z) :=
[[0x540e4; 0x42810; 0x83c0c]].
Definition CTX_main : list (list Z) :=
[[0x8cb34]].
Definition TRACES_main : list (list Z) :=
[[0x53f84; 0x81f70];
[0x53f84; 0x820a0];
[0x540e4; 0x81ef8];
[0x540e4; 0x81f4c]].
Definition CTX_target_alloc_init : list (list Z) :=
[[0x82004]].
Definition CTX_target_alloc_count : list (list Z) :=
[[0x82028]].
Definition CTX_target_run : list (list Z) :=
[[0x82018]].
Definition TRACES_target_run : list (list Z) :=
[[0x53f84; 0x8226c];
[0x540e4; 0x821d8]].
Definition CTX_emit_printf : list (list Z) :=
[[0x82250]].
Definition CTX_relay_finish : list (list Z) :=
[[0x84f08];
[0x84f08; 0x82240];
[0x84fe8];
[0x84fe8; 0x82240]].
Definition TRACES_relay_finish : list (list Z) :=
[[0x53f84; 0x8240c]].
Definition CTX_wake : list (list Z) :=
[[0x82388];
[0x82c14];
[0x8485c];
[0x8485c; 0x82240]].
Definition CTX_gestures_end : list (list Z) :=
[[0x8242c];
[0x84318]].
Definition TRACES_gestures_end : list (list Z) :=
[[0x53f84; 0x8272c];
[0x53f84; 0x82768]].
Definition CTX_relay_event : list (list Z) :=
[[0x84d90];
[0x84d90; 0x82240]].
Definition CTX_send_line : list (list Z) :=
[[0x826e0];
[0x8283c];
[0x82f6c; 0x84b4c];
[0x82f6c; 0x84b4c; 0x82240];
[0x839f4];
[0x85b34]].
Definition TRACES_send_line : list (list Z) :=
[[0x54380; 0x829f4]].
Definition CTX_relay_add : list (list Z) :=
[[0x852a4]].
Definition TRACES_relay_add : list (list Z) :=
[[0x54380; 0x82b84]].
Definition CTX_relay_instance_gone : list (list Z) :=
[[0x84b4c];
[0x84b4c; 0x82240]].
Definition TRACES_relay_instance_gone : list (list Z) :=
[[0x53f84; 0x82fb8; 0x84b4c];
[0x53f84; 0x82fb8; 0x84b4c; 0x82240]].
Definition CTX_drain : list (list Z) :=
[[0x82e6c; 0x84b4c];
[0x82e6c; 0x84b4c; 0x82240];
[0x842f8];
[0x8490c];
[0x8490c; 0x82240]].
Definition TRACES_drain : list (list Z) :=
[[0x53f84; 0x83cd0];
[0x54380; 0x83414];
[0x54380; 0x83bec]].
Definition CTX_relay_remove : list (list Z) :=
[[0x8485c];
[0x8485c; 0x82240]].
Definition TRACES_relay_remove : list (list Z) :=
[[0x53f84; 0x84360]].
Definition CTX_LLVMFuzzerTestOneInput : list (list Z) :=
[[0x82240]].
Definition TRACES_LLVMFuzzerTestOneInput : list (list Z) :=
[[0x53f84; 0x84da0];
[0x53f84; 0x84da0; 0x82240];
[0x540e4; 0x84d4c];
[0x540e4; 0x84d4c; 0x82240]].
Definition CTX_op_add : list (list Z) :=
[[0x84594];
[0x84594; 0x82240];
[0x84788];
[0x84788; 0x82240]].
Definition TRACES_op_add : list (list Z) :=
[[0x540e4; 0x85268]].
Definition CTX_list_push : list (list Z) :=
[[0x837a8];
[0x84800];
[0x84800; 0x82240];
[0x85f9c]].
Definition TRACES_list_push : list (list Z) :=
[[0x540e4; 0x85408];
[0x54380; 0x853e4]].
Definition CTX_check_bounded : list (list Z) :=
[[0x84808];
[0x84808; 0x82240]].
Definition CTX_check_shape_ends : list (list Z) :=
[[0x84888];
[0x84888; 0x82240];
[0x84c28];
[0x84c28; 0x82240];
[0x84f90];
[0x84f90; 0x82240]].
Definition CTX_check_shape_done : list (list Z) :=
[[0x84890];
[0x84890; 0x82240];
[0x84934];
[0x84934; 0x82240];
[0x84c8c];
[0x84c8c; 0x82240];
[0x84d98];
[0x84d98; 0x82240];
[0x84ff0];
[0x84ff0; 0x82240];
[0x865f8]].
Definition CTX_source_reset : list (list Z) :=
[[0x84898];
[0x84898; 0x82240];
[0x8500c];
[0x8500c; 0x82240];
[0x8522c]].
Definition TRACES_source_reset : list (list Z) :=
[[0x53f84; 0x85ae8]].
Definition CTX_gesture_end : list (list Z) :=
[[0x826e0];
[0x82f6c; 0x84b4c];
[0x82f6c; 0x84b4c; 0x82240]].
Definition CTX_list_drop : list (list Z) :=
[[0x83918];
[0x85928];
[0x85a04];
[0x85f9c];
[0x85fa8];
[0x866e0]].
Definition TRACES_list_drop : list (list Z) :=
[[0x53f84; 0x85bec]].
Definition CTX_relay_source : list (list Z) :=
[[0x848c4];
[0x848c4; 0x82240];
[0x86524];
[0x86524; 0x82240]].
Definition CTX_check_no_loss_read : list (list Z) :=
[[0x84868];
[0x84868; 0x82240];
[0x84920];
[0x84920; 0x82240];
[0x84b6c];
[0x84b6c; 0x82240]].
Definition CTX_check_no_loss : list (list Z) :=
[[0x84874];
[0x84874; 0x82240];
[0x8492c];
[0x8492c; 0x82240];
[0x84c18];
[0x84c18; 0x82240]].
Definition CTX_gesture_model : list (list Z) :=
[[0x85f9c]].
Definition CTX_next_line : list (list Z) :=
[[0x85994];
[0x865c8]].
Definition CTX_list_find : list (list Z) :=
[[0x859dc];
[0x8617c];
[0x861f4]].
Definition CTX_relay_reads : list (list Z) :=
[[0x84834];
[0x84834; 0x82240];
[0x84b10];
[0x84b10; 0x82240]].
Definition CTX_check_shape_event : list (list Z) :=
[[0x84d98];
[0x84d98; 0x82240]].
Definition CTX_has_prefix : list (list Z) :=
[[0x85864];
[0x85918];
[0x859f4]].
Definition CTX_list_free : list (list Z) :=
[[0x85abc];
[0x85ac4];
[0x85acc]].
Definition TRACES_list_free : list (list Z) :=
[[0x53f84; 0x86718]].
Definition Tfib_universe : list (list Z) :=
[[0x53f84];
[0x53f84; 0x81f70];
[0x53f84; 0x820a0];
[0x53f84; 0x8226c];
[0x53f84; 0x8240c];
[0x53f84; 0x8272c];
[0x53f84; 0x82768];
[0x53f84; 0x82fb8; 0x84b4c];
[0x53f84; 0x82fb8; 0x84b4c; 0x82240];
[0x53f84; 0x83cd0];
[0x53f84; 0x84360];
[0x53f84; 0x84da0];
[0x53f84; 0x84da0; 0x82240];
[0x53f84; 0x85ae8];
[0x53f84; 0x85bec];
[0x53f84; 0x86718];
[0x540e4];
[0x540e4; 0x42810; 0x83c0c];
[0x540e4; 0x81ef8];
[0x540e4; 0x81f4c];
[0x540e4; 0x821d8];
[0x540e4; 0x84d4c];
[0x540e4; 0x84d4c; 0x82240];
[0x540e4; 0x85268];
[0x540e4; 0x85408];
[0x54380];
[0x54380; 0x829f4];
[0x54380; 0x82b84];
[0x54380; 0x83414];
[0x54380; 0x83bec];
[0x54380; 0x853e4]].
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
Lemma TRACES_source_reset_U : forall t, In t TRACES_source_reset -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_source_reset t ltac:(vm_compute; reflexivity) H). Qed.
Lemma TRACES_list_drop_U : forall t, In t TRACES_list_drop -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_list_drop t ltac:(vm_compute; reflexivity) H). Qed.
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
