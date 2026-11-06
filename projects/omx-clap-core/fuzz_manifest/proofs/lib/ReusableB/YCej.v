(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: re-derived for omx-clap-core/fuzz_manifest's asan-ubsan image by a Theorem Labs lane's tools/startup/universe.py (pautrlen/compose.py, CTXALL=1, over the unstripped fuzz_manifest.asan-ubsan; program region [main 0x804dc, __wrap_getenv 0x82620); hand decisions in decisions.fuzz_manifest.asan-ubsan.json); module paths changed *)
(* Read from: fuzz_manifest.asan-ubsan (omx-clap-core/fuzz_manifest asan-ubsan) sha256 ca61e5c9eabc00501d5cebab7618d8c03e73419f52c9f0b9be51c8bedff96e5e; unstripped twin sha256 b9568e38145a50214b3744e4f26bfc2ec9f670eca737d4da9be2dca6a0cfc2de *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG01.
Import ListNotations.
Local Open Scope Z_scope.
Definition CTX_main : list (list Z) :=
[[0x88974]].
Definition TRACES_main : list (list Z) :=
[[0x52f58; 0x805a8];
[0x52f58; 0x806d8];
[0x530b8; 0x80530];
[0x530b8; 0x80584]].
Definition CTX_target_alloc_init : list (list Z) :=
[[0x8063c]].
Definition CTX_target_alloc_count : list (list Z) :=
[[0x80660]].
Definition CTX_target_run : list (list Z) :=
[[0x80650]].
Definition TRACES_target_run : list (list Z) :=
[[0x52f58; 0x808a4];
[0x530b8; 0x80810]].
Definition CTX_emit_printf : list (list Z) :=
[[0x80888]].
Definition CTX_LLVMFuzzerTestOneInput : list (list Z) :=
[[0x80878]].
Definition TRACES_LLVMFuzzerTestOneInput : list (list Z) :=
[[0x52f58; 0x80b6c];
[0x52f58; 0x80b74];
[0x530b8; 0x80a7c];
[0x530b8; 0x80ac8]].
Definition CTX_check_no_overread : list (list Z) :=
[[0x80a6c]].
Definition TRACES_check_no_overread : list (list Z) :=
[[0x52f58; 0x80a6c];
[0x52f58; 0x80e48];
[0x52f58; 0x80e50];
[0x52f58; 0x80e58];
[0x530b8; 0x80c3c];
[0x530b8; 0x80cbc];
[0x530b8; 0x80d38];
[0x530b8; 0x80db0]].
Definition CTX_check_bounded_alloc : list (list Z) :=
[[0x80b38]].
Definition CTX_check_as_written : list (list Z) :=
[[0x80b48]].
Definition CTX_check_reject_clean : list (list Z) :=
[[0x80b50];
[0x80b5c]].
Definition CTX_check_reject_clean_starved : list (list Z) :=
[[0x80b5c]].
Definition CTX_check_round_trip : list (list Z) :=
[[0x80b64]].
Definition TRACES_check_round_trip : list (list Z) :=
[[0x52f58; 0x80b64];
[0x530b8; 0x81074]].
Definition CTX_expected : list (list Z) :=
[[0x80f40];
[0x81af8]].
Definition CTX_plain : list (list Z) :=
[[0x81124];
[0x816c0]].
Definition CTX_must_name : list (list Z) :=
[[0x810a0];
[0x81150];
[0x81178];
[0x811a0]].
Definition CTX_as_ruled : list (list Z) :=
[[0x810c4];
[0x811c8]].
Definition CTX_fuzz_malloc : list (list Z) :=
[[0x81f00; 0x81e88]].
Definition TRACES_fuzz_malloc : list (list Z) :=
[[0x530b8; 0x81bd0]].
Definition CTX_own : list (list Z) :=
[[0x81f00; 0x81e88]].
Definition CTX_fuzz_free : list (list Z) :=
[[0x81f38; 0x81e88]].
Definition TRACES_fuzz_free : list (list Z) :=
[[0x52f58; 0x81f38; 0x81e88]].
Definition CTX_fuzz_alloc_live : list (list Z) :=
[[0x80b10];
[0x80f7c];
[0x80fbc]].
Definition CTX_fuzz_alloc_peak : list (list Z) :=
[[0x80b2c]].
Definition CTX_fuzz_alloc_peak_reset : list (list Z) :=
[[0x80b18]].
Definition CTX_fuzz_alloc_fail : list (list Z) :=
[[0x80fc8];
[0x80fdc]].
Definition CTX_lv2_locate_manifest_names : list (list Z) :=
[[0x80b24];
[0x80e2c];
[0x80e3c];
[0x80fd4];
[0x81058];
[0x81aa8];
[0x81ae8]].
Definition CTX_lv2_locate_manifest_readings : list (list Z) :=
[[0x81e88]].
Definition CTX_has_prefixed : list (list Z) :=
[[0x82338]].
Definition CTX_name_char : list (list Z) :=
[[0x824e4];
[0x8251c]].
Definition Tfib_universe : list (list Z) :=
[[0x52f58];
[0x52f58; 0x805a8];
[0x52f58; 0x806d8];
[0x52f58; 0x808a4];
[0x52f58; 0x80a6c];
[0x52f58; 0x80b64];
[0x52f58; 0x80b6c];
[0x52f58; 0x80b74];
[0x52f58; 0x80e48];
[0x52f58; 0x80e50];
[0x52f58; 0x80e58];
[0x52f58; 0x81f38; 0x81e88];
[0x530b8];
[0x530b8; 0x80530];
[0x530b8; 0x80584];
[0x530b8; 0x80810];
[0x530b8; 0x80a7c];
[0x530b8; 0x80ac8];
[0x530b8; 0x80c3c];
[0x530b8; 0x80cbc];
[0x530b8; 0x80d38];
[0x530b8; 0x80db0];
[0x530b8; 0x81074];
[0x530b8; 0x81bd0]].
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
Lemma TRACES_main_U : forall t, In t TRACES_main -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_main t ltac:(vm_compute; reflexivity) H). Qed.
Lemma TRACES_target_run_U : forall t, In t TRACES_target_run -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_target_run t ltac:(vm_compute; reflexivity) H). Qed.
Lemma TRACES_LLVMFuzzerTestOneInput_U : forall t, In t TRACES_LLVMFuzzerTestOneInput -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_LLVMFuzzerTestOneInput t ltac:(vm_compute; reflexivity) H). Qed.
Lemma TRACES_check_no_overread_U : forall t, In t TRACES_check_no_overread -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_check_no_overread t ltac:(vm_compute; reflexivity) H). Qed.
Lemma TRACES_check_round_trip_U : forall t, In t TRACES_check_round_trip -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_check_round_trip t ltac:(vm_compute; reflexivity) H). Qed.
Lemma TRACES_fuzz_malloc_U : forall t, In t TRACES_fuzz_malloc -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_fuzz_malloc t ltac:(vm_compute; reflexivity) H). Qed.
Lemma TRACES_fuzz_free_U : forall t, In t TRACES_fuzz_free -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_fuzz_free t ltac:(vm_compute; reflexivity) H). Qed.
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
Lemma Tfib_universe_ok : universe_ok Tfib_universe.
Proof.
split; [unfold DEPOT_MAX; (first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])|]. split.
- apply Forall_forall. intros t Ht.
pose proof (allb_In (fun t : list Z => (length t <=? kUnwindMax)%nat) Tfib_universe t ltac:(vm_compute; reflexivity) Ht) as H.
apply Nat.leb_le in H. exact H.
- apply nodupZL_NoDup. vm_compute. reflexivity.
Qed.
