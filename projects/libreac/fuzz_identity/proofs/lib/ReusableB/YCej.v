(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: generated for libreac/fuzz_identity image B by universe.py, a generator this repository does not ship, over fuzz_identity.asan-ubsan (sha256 baf1a4d065e02f55521d39f05d8c8d9ed763a0ef798c70cc3eabe5816ffb3f66; names from its unstripped twin sha256 43b44d50be8a5e68f626662181c9cc17c0e0fef138e55f3c8bab371987a9c064), decisions: CTX_/TRACES_ per fuzz_identity function, never relocated from cgif *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG01.
Import ListNotations.
Local Open Scope Z_scope.
Definition CTX_main : list (list Z) :=
[[0x8a9e8]].
Definition TRACES_main : list (list Z) :=
[[0x52d50; 0x803a0];
[0x52d50; 0x804d0];
[0x52eb0; 0x80328];
[0x52eb0; 0x8037c]].
Definition CTX_target_alloc_init : list (list Z) :=
[[0x80434]].
Definition CTX_target_alloc_count : list (list Z) :=
[[0x80458]].
Definition CTX_target_run : list (list Z) :=
[[0x80448]].
Definition TRACES_target_run : list (list Z) :=
[[0x52d50; 0x8069c];
[0x52eb0; 0x80608]].
Definition CTX_emit_printf : list (list Z) :=
[[0x80680]].
Definition CTX_LLVMFuzzerTestOneInput : list (list Z) :=
[[0x80670]].
Definition TRACES_LLVMFuzzerTestOneInput : list (list Z) :=
[[0x52d50; 0x80da4];
[0x52d50; 0x80da4; 0x80670];
[0x52d50; 0x815d8];
[0x52d50; 0x815d8; 0x80670];
[0x52d50; 0x818ec];
[0x52d50; 0x818ec; 0x80670];
[0x52d50; 0x81928];
[0x52d50; 0x81928; 0x80670];
[0x52d50; 0x82368];
[0x52d50; 0x82368; 0x80670];
[0x52d50; 0x82370];
[0x52d50; 0x82370; 0x80670];
[0x52d50; 0x82378];
[0x52d50; 0x82378; 0x80670];
[0x52eb0; 0x80c94];
[0x52eb0; 0x80c94; 0x80670]].
Definition CTX_buf_of : list (list Z) :=
[[0x80d10];
[0x80d10; 0x80670];
[0x818a0];
[0x818a0; 0x80670];
[0x818f4];
[0x818f4; 0x80670];
[0x81a60];
[0x81a60; 0x80670];
[0x81a6c];
[0x81a6c; 0x80670];
[0x81a78];
[0x81a78; 0x80670]].
Definition TRACES_buf_of : list (list Z) :=
[[0x52eb0; 0x82814];
[0x52eb0; 0x82814; 0x80670]].
Definition CTX_check_str : list (list Z) :=
[[0x81440];
[0x81440; 0x80670];
[0x818c8];
[0x818c8; 0x80670];
[0x818e4];
[0x818e4; 0x80670];
[0x81920];
[0x81920; 0x80670];
[0x8211c];
[0x8211c; 0x80670];
[0x82134];
[0x82134; 0x80670];
[0x82150];
[0x82150; 0x80670]].
Definition CTX_put_dec : list (list Z) :=
[[0x81148];
[0x81148; 0x80670];
[0x81194];
[0x81194; 0x80670];
[0x811a8];
[0x811a8; 0x80670];
[0x81964];
[0x81964; 0x80670];
[0x819b0];
[0x819b0; 0x80670];
[0x81c64];
[0x81c64; 0x80670];
[0x81c78];
[0x81c78; 0x80670];
[0x81f58];
[0x81f58; 0x80670];
[0x81ffc];
[0x81ffc; 0x80670]].
Definition CTX_reac_box_family_of : list (list Z) :=
[[0x80abc];
[0x80abc; 0x80670];
[0x81778];
[0x81778; 0x80670];
[0x81a20];
[0x81a20; 0x80670]].
Definition CTX_reac_box_family_stem : list (list Z) :=
[[0x81a34];
[0x81a34; 0x80670]].
Definition CTX_reac_box_name : list (list Z) :=
[[0x81ab0];
[0x81ab0; 0x80670];
[0x81af0];
[0x81af0; 0x80670]].
Definition CTX_sb_dec : list (list Z) :=
[[0x83010; 0x81ab0];
[0x83010; 0x81ab0; 0x80670];
[0x83010; 0x81af0];
[0x83010; 0x81af0; 0x80670];
[0x83020; 0x81ab0];
[0x83020; 0x81ab0; 0x80670];
[0x83020; 0x81af0];
[0x83020; 0x81af0; 0x80670];
[0x83338; 0x81ab0];
[0x83338; 0x81ab0; 0x80670];
[0x83338; 0x81af0];
[0x83338; 0x81af0; 0x80670];
[0x83394; 0x81ab0];
[0x83394; 0x81ab0; 0x80670];
[0x83394; 0x81af0];
[0x83394; 0x81af0; 0x80670]].
Definition CTX_sb_ch : list (list Z) :=
[[0x83094; 0x81ab0];
[0x83094; 0x81ab0; 0x80670];
[0x83094; 0x81af0];
[0x83094; 0x81af0; 0x80670];
[0x83118; 0x81ab0];
[0x83118; 0x81ab0; 0x80670];
[0x83118; 0x81af0];
[0x83118; 0x81af0; 0x80670];
[0x83134; 0x81ab0];
[0x83134; 0x81ab0; 0x80670];
[0x83134; 0x81af0];
[0x83134; 0x81af0; 0x80670];
[0x83214; 0x81ab0];
[0x83214; 0x81ab0; 0x80670];
[0x83214; 0x81af0];
[0x83214; 0x81af0; 0x80670];
[0x832a4; 0x81ab0];
[0x832a4; 0x81ab0; 0x80670];
[0x832a4; 0x81af0];
[0x832a4; 0x81af0; 0x80670];
[0x8330c; 0x81ab0];
[0x8330c; 0x81ab0; 0x80670];
[0x8330c; 0x81af0];
[0x8330c; 0x81af0; 0x80670];
[0x83368; 0x81ab0];
[0x83368; 0x81ab0; 0x80670];
[0x83368; 0x81af0];
[0x83368; 0x81af0; 0x80670];
[0x833c4; 0x81ab0];
[0x833c4; 0x81ab0; 0x80670];
[0x833c4; 0x81af0];
[0x833c4; 0x81af0; 0x80670];
[0x83778; 0x83010; 0x81ab0];
[0x83778; 0x83010; 0x81ab0; 0x80670];
[0x83778; 0x83010; 0x81af0];
[0x83778; 0x83010; 0x81af0; 0x80670];
[0x83778; 0x83020; 0x81ab0];
[0x83778; 0x83020; 0x81ab0; 0x80670];
[0x83778; 0x83020; 0x81af0];
[0x83778; 0x83020; 0x81af0; 0x80670];
[0x83778; 0x83338; 0x81ab0];
[0x83778; 0x83338; 0x81ab0; 0x80670];
[0x83778; 0x83338; 0x81af0];
[0x83778; 0x83338; 0x81af0; 0x80670];
[0x83778; 0x83394; 0x81ab0];
[0x83778; 0x83394; 0x81ab0; 0x80670];
[0x83778; 0x83394; 0x81af0];
[0x83778; 0x83394; 0x81af0; 0x80670]].
Definition CTX_reac_box_catalogue_defect : list (list Z) :=
[[0x80ab0];
[0x80ab0; 0x80670];
[0x822ac];
[0x822ac; 0x80670];
[0x82314];
[0x82314; 0x80670]].
Definition CTX_reac_box_catalogue : list (list Z) :=
[[0x8225c];
[0x8225c; 0x80670]].
Definition CTX_reac_identity_init : list (list Z) :=
[[0x80a18];
[0x80a18; 0x80670];
[0x80a24];
[0x80a24; 0x80670]].
Definition CTX_reac_identity_ingest : list (list Z) :=
[[0x80a38];
[0x80a38; 0x80670];
[0x80a58];
[0x80a58; 0x80670];
[0x80cfc];
[0x80cfc; 0x80670];
[0x80d98];
[0x80d98; 0x80670]].
Definition CTX_reac_identity_fw_str : list (list Z) :=
[[0x80a70];
[0x80a70; 0x80670];
[0x81430];
[0x81430; 0x80670];
[0x818bc];
[0x818bc; 0x80670];
[0x818d8];
[0x818d8; 0x80670];
[0x819e0];
[0x819e0; 0x80670]].
Definition CTX_reac_identity_reac_ver_str : list (list Z) :=
[[0x80a90];
[0x80a90; 0x80670];
[0x811ec];
[0x811ec; 0x80670];
[0x81914];
[0x81914; 0x80670]].
Definition CTX_write_uint : list (list Z) :=
[[0x842f0];
[0x84358];
[0x843d4]].
Definition Tfib_universe : list (list Z) :=
[[0x52d50];
[0x52d50; 0x803a0];
[0x52d50; 0x804d0];
[0x52d50; 0x8069c];
[0x52d50; 0x80da4];
[0x52d50; 0x80da4; 0x80670];
[0x52d50; 0x815d8];
[0x52d50; 0x815d8; 0x80670];
[0x52d50; 0x818ec];
[0x52d50; 0x818ec; 0x80670];
[0x52d50; 0x81928];
[0x52d50; 0x81928; 0x80670];
[0x52d50; 0x82368];
[0x52d50; 0x82368; 0x80670];
[0x52d50; 0x82370];
[0x52d50; 0x82370; 0x80670];
[0x52d50; 0x82378];
[0x52d50; 0x82378; 0x80670];
[0x52eb0];
[0x52eb0; 0x80328];
[0x52eb0; 0x8037c];
[0x52eb0; 0x80608];
[0x52eb0; 0x80c94];
[0x52eb0; 0x80c94; 0x80670];
[0x52eb0; 0x82814];
[0x52eb0; 0x82814; 0x80670]].
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
Lemma TRACES_buf_of_U : forall t, In t TRACES_buf_of -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_buf_of t ltac:(vm_compute; reflexivity) H). Qed.
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
