(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: generated for libreac/fuzz_identity image A by universe.py, a generator this repository does not ship, over fuzz_identity.asan (sha256 c954b804786cb87fc218414447199e35235b9788453ec0db312f97cd0dc4291b; names from its unstripped twin sha256 5b0cbe57303630895c71979f5c3209f1d343f0f42aad36e87c9f5193408da124), decisions: CTX_/TRACES_ per fuzz_identity function, never relocated from cgif *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG01.
Import ListNotations.
Local Open Scope Z_scope.
Definition CTX_main : list (list Z) :=
[[0x8a6fc]].
Definition TRACES_main : list (list Z) :=
[[0x52ce8; 0x80338];
[0x52ce8; 0x80468];
[0x52e48; 0x802c0];
[0x52e48; 0x80314]].
Definition CTX_target_alloc_init : list (list Z) :=
[[0x803cc]].
Definition CTX_target_alloc_count : list (list Z) :=
[[0x803f0]].
Definition CTX_target_run : list (list Z) :=
[[0x803e0]].
Definition TRACES_target_run : list (list Z) :=
[[0x52ce8; 0x80634];
[0x52e48; 0x805a0]].
Definition CTX_emit_printf : list (list Z) :=
[[0x80618]].
Definition CTX_LLVMFuzzerTestOneInput : list (list Z) :=
[[0x80608]].
Definition TRACES_LLVMFuzzerTestOneInput : list (list Z) :=
[[0x52ce8; 0x80cd8];
[0x52ce8; 0x80cd8; 0x80608];
[0x52ce8; 0x813f4];
[0x52ce8; 0x813f4; 0x80608];
[0x52ce8; 0x8173c];
[0x52ce8; 0x8173c; 0x80608];
[0x52ce8; 0x81784];
[0x52ce8; 0x81784; 0x80608];
[0x52ce8; 0x82098];
[0x52ce8; 0x82098; 0x80608];
[0x52ce8; 0x820a0];
[0x52ce8; 0x820a0; 0x80608];
[0x52ce8; 0x820a8];
[0x52ce8; 0x820a8; 0x80608];
[0x52e48; 0x80bcc];
[0x52e48; 0x80bcc; 0x80608];
[0x52e48; 0x80c44];
[0x52e48; 0x80c44; 0x80608];
[0x52e48; 0x816e8];
[0x52e48; 0x816e8; 0x80608];
[0x52e48; 0x81748];
[0x52e48; 0x81748; 0x80608];
[0x52e48; 0x818bc];
[0x52e48; 0x818bc; 0x80608];
[0x52e48; 0x818d4];
[0x52e48; 0x818d4; 0x80608];
[0x52e48; 0x818ec];
[0x52e48; 0x818ec; 0x80608]].
Definition CTX_check_str : list (list Z) :=
[[0x812bc];
[0x812bc; 0x80608];
[0x81718];
[0x81718; 0x80608];
[0x81734];
[0x81734; 0x80608];
[0x8177c];
[0x8177c; 0x80608];
[0x81e88];
[0x81e88; 0x80608];
[0x81ea0];
[0x81ea0; 0x80608];
[0x81eb8];
[0x81eb8; 0x80608]].
Definition CTX_put_dec : list (list Z) :=
[[0x8100c];
[0x8100c; 0x80608];
[0x81048];
[0x81048; 0x80608];
[0x8105c];
[0x8105c; 0x80608];
[0x817c0];
[0x817c0; 0x80608];
[0x81810];
[0x81810; 0x80608];
[0x81aa0];
[0x81aa0; 0x80608];
[0x81ab4];
[0x81ab4; 0x80608];
[0x81d00];
[0x81d00; 0x80608];
[0x81d8c];
[0x81d8c; 0x80608]].
Definition CTX_reac_box_family_of : list (list Z) :=
[[0x80a54];
[0x80a54; 0x80608];
[0x81584];
[0x81584; 0x80608];
[0x81884];
[0x81884; 0x80608]].
Definition CTX_reac_box_family_stem : list (list Z) :=
[[0x8189c];
[0x8189c; 0x80608]].
Definition CTX_reac_box_name : list (list Z) :=
[[0x81934];
[0x81934; 0x80608];
[0x81970];
[0x81970; 0x80608]].
Definition CTX_sb_dec : list (list Z) :=
[[0x82cb8; 0x81934];
[0x82cb8; 0x81934; 0x80608];
[0x82cb8; 0x81970];
[0x82cb8; 0x81970; 0x80608];
[0x82cc8; 0x81934];
[0x82cc8; 0x81934; 0x80608];
[0x82cc8; 0x81970];
[0x82cc8; 0x81970; 0x80608];
[0x83120; 0x81934];
[0x83120; 0x81934; 0x80608];
[0x83120; 0x81970];
[0x83120; 0x81970; 0x80608];
[0x831c8; 0x81934];
[0x831c8; 0x81934; 0x80608];
[0x831c8; 0x81970];
[0x831c8; 0x81970; 0x80608]].
Definition CTX_reac_box_catalogue_defect : list (list Z) :=
[[0x80a48];
[0x80a48; 0x80608];
[0x81fe4];
[0x81fe4; 0x80608];
[0x82044];
[0x82044; 0x80608]].
Definition CTX_reac_box_catalogue : list (list Z) :=
[[0x81fb0];
[0x81fb0; 0x80608]].
Definition CTX_reac_identity_init : list (list Z) :=
[[0x809b0];
[0x809b0; 0x80608];
[0x809bc];
[0x809bc; 0x80608]].
Definition CTX_reac_identity_ingest : list (list Z) :=
[[0x809d0];
[0x809d0; 0x80608];
[0x809f0];
[0x809f0; 0x80608];
[0x80c30];
[0x80c30; 0x80608];
[0x80ccc];
[0x80ccc; 0x80608]].
Definition CTX_reac_identity_fw_str : list (list Z) :=
[[0x80a08];
[0x80a08; 0x80608];
[0x812ac];
[0x812ac; 0x80608];
[0x8170c];
[0x8170c; 0x80608];
[0x81728];
[0x81728; 0x80608];
[0x81848];
[0x81848; 0x80608]].
Definition CTX_reac_identity_reac_ver_str : list (list Z) :=
[[0x80a28];
[0x80a28; 0x80608];
[0x81098];
[0x81098; 0x80608];
[0x81770];
[0x81770; 0x80608]].
Definition CTX_write_uint : list (list Z) :=
[[0x84094];
[0x840c4];
[0x840fc]].
Definition Tfib_universe : list (list Z) :=
[[0x52ce8];
[0x52ce8; 0x80338];
[0x52ce8; 0x80468];
[0x52ce8; 0x80634];
[0x52ce8; 0x80cd8];
[0x52ce8; 0x80cd8; 0x80608];
[0x52ce8; 0x813f4];
[0x52ce8; 0x813f4; 0x80608];
[0x52ce8; 0x8173c];
[0x52ce8; 0x8173c; 0x80608];
[0x52ce8; 0x81784];
[0x52ce8; 0x81784; 0x80608];
[0x52ce8; 0x82098];
[0x52ce8; 0x82098; 0x80608];
[0x52ce8; 0x820a0];
[0x52ce8; 0x820a0; 0x80608];
[0x52ce8; 0x820a8];
[0x52ce8; 0x820a8; 0x80608];
[0x52e48];
[0x52e48; 0x802c0];
[0x52e48; 0x80314];
[0x52e48; 0x805a0];
[0x52e48; 0x80bcc];
[0x52e48; 0x80bcc; 0x80608];
[0x52e48; 0x80c44];
[0x52e48; 0x80c44; 0x80608];
[0x52e48; 0x816e8];
[0x52e48; 0x816e8; 0x80608];
[0x52e48; 0x81748];
[0x52e48; 0x81748; 0x80608];
[0x52e48; 0x818bc];
[0x52e48; 0x818bc; 0x80608];
[0x52e48; 0x818d4];
[0x52e48; 0x818d4; 0x80608];
[0x52e48; 0x818ec];
[0x52e48; 0x818ec; 0x80608]].
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
