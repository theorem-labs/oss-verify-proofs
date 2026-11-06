(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: generated for reac-pw/fuzz_segconf image B by universe.py 4fd01bdf8b9b (the start-up tool set of record at tools commit f1417943331) from pautrlen/compose.py's walk of fuzz_segconf.asan-ubsan (CTXALL=1, names from its unstripped twin without mapping symbols), the program region [main 0x84920, 0x8a934), RA_TOP 0x84cbc (target_run after its LLVMFuzzerTestOneInput call), main's return address 0x90c88; the 6 WILD context sites (check_absent's four query calls, reac_segconf_role's call of reac_segconf_find, reac_declared_vlan_split's call of name_ok) have no determined chain, from the disassembly, and state no context row; template proofs/cgif/cgif_file_fuzzer/lib/YCej.v at c8557374ad2e, module paths changed (Requires placed in lib/Reusable / lib/B) *)
(* Read from: fuzz_segconf.asan-ubsan (reac-pw/fuzz_segconf asan-ubsan) sha256 c3796c0b38f3666f32a3ecff43c9fdb55ead356833af6013a07c404bd0254509; unstripped twin sha256 80e82127e8ca1e8b2ee142f113e0e529fd7b8052d654e8dfc120fd8d4ae40a21 *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG01.
Import ListNotations.
Local Open Scope Z_scope.
Definition CTX_main : list (list Z) :=
[[0x90c88]].
Definition TRACES_main : list (list Z) :=
[[0x56e00; 0x849ec];
[0x56e00; 0x84b1c];
[0x56f60; 0x84974];
[0x56f60; 0x849c8]].
Definition CTX_target_alloc_init : list (list Z) :=
[[0x84a80]].
Definition CTX_target_alloc_count : list (list Z) :=
[[0x84aa4]].
Definition CTX_target_run : list (list Z) :=
[[0x84a94]].
Definition TRACES_target_run : list (list Z) :=
[[0x56e00; 0x84ce8];
[0x56f60; 0x84c54]].
Definition CTX_emit_printf : list (list Z) :=
[[0x84ccc]].
Definition CTX_LLVMFuzzerTestOneInput : list (list Z) :=
[[0x84cbc]].
Definition TRACES_LLVMFuzzerTestOneInput : list (list Z) :=
[[0x56e00; 0x85530];
[0x56e00; 0x85530; 0x84cbc];
[0x56e00; 0x85e9c];
[0x56e00; 0x85e9c; 0x84cbc];
[0x56e00; 0x85ea4];
[0x56e00; 0x85ea4; 0x84cbc];
[0x56e00; 0x85eac];
[0x56e00; 0x85eac; 0x84cbc];
[0x56e00; 0x85eb4];
[0x56e00; 0x85eb4; 0x84cbc];
[0x56f60; 0x85068];
[0x56f60; 0x85068; 0x84cbc];
[0x56f60; 0x85210];
[0x56f60; 0x85210; 0x84cbc];
[0x57194; 0x8507c];
[0x57194; 0x8507c; 0x84cbc];
[0x57194; 0x85984];
[0x57194; 0x85984; 0x84cbc];
[0x57194; 0x85994];
[0x57194; 0x85994; 0x84cbc]].
Definition CTX_m_file : list (list Z) :=
[[0x852d4];
[0x852d4; 0x84cbc];
[0x85338];
[0x85338; 0x84cbc]].
Definition CTX_check_segments : list (list Z) :=
[[0x855d8];
[0x855d8; 0x84cbc]].
Definition CTX_check_role : list (list Z) :=
[[0x85664];
[0x85664; 0x84cbc]].
Definition CTX_check_model : list (list Z) :=
[[0x85678];
[0x85678; 0x84cbc]].
Definition CTX_check_ignore : list (list Z) :=
[[0x8568c];
[0x8568c; 0x84cbc]].
Definition CTX_check_provenance : list (list Z) :=
[[0x856b8];
[0x856b8; 0x84cbc]].
Definition CTX_check_refusals : list (list Z) :=
[[0x85700];
[0x85700; 0x84cbc]].
Definition CTX_check_address : list (list Z) :=
[[0x857e4];
[0x857e4; 0x84cbc]].
Definition CTX_check_knock_refused : list (list Z) :=
[[0x85814];
[0x85814; 0x84cbc]].
Definition CTX_m_find : list (list Z) :=
[[0x858f8];
[0x858f8; 0x84cbc];
[0x8595c];
[0x8595c; 0x84cbc];
[0x865cc; 0x852d4];
[0x865cc; 0x852d4; 0x84cbc];
[0x865cc; 0x85338];
[0x865cc; 0x85338; 0x84cbc]].
Definition CTX_check_absent : list (list Z) :=
[[0x85908];
[0x85908; 0x84cbc];
[0x85970];
[0x85970; 0x84cbc]].
Definition CTX_check_declared : list (list Z) :=
[[0x85e94];
[0x85e94; 0x84cbc]].
Definition CTX_m_refuse : list (list Z) :=
[[0x853f4];
[0x853f4; 0x84cbc];
[0x85428];
[0x85428; 0x84cbc];
[0x86618; 0x852d4];
[0x86618; 0x852d4; 0x84cbc];
[0x86618; 0x85338];
[0x86618; 0x85338; 0x84cbc];
[0x867b0; 0x852d4];
[0x867b0; 0x852d4; 0x84cbc];
[0x867b0; 0x85338];
[0x867b0; 0x85338; 0x84cbc];
[0x867cc; 0x852d4];
[0x867cc; 0x852d4; 0x84cbc];
[0x867cc; 0x85338];
[0x867cc; 0x85338; 0x84cbc];
[0x867e0; 0x852d4];
[0x867e0; 0x852d4; 0x84cbc];
[0x867e0; 0x85338];
[0x867e0; 0x85338; 0x84cbc];
[0x8681c; 0x852d4];
[0x8681c; 0x852d4; 0x84cbc];
[0x8681c; 0x85338];
[0x8681c; 0x85338; 0x84cbc];
[0x86b4c; 0x852d4];
[0x86b4c; 0x852d4; 0x84cbc];
[0x86b4c; 0x85338];
[0x86b4c; 0x85338; 0x84cbc]].
Definition CTX_strip : list (list Z) :=
[[0x864c4; 0x852d4];
[0x864c4; 0x852d4; 0x84cbc];
[0x864c4; 0x85338];
[0x864c4; 0x85338; 0x84cbc];
[0x86534; 0x852d4];
[0x86534; 0x852d4; 0x84cbc];
[0x86534; 0x85338];
[0x86534; 0x85338; 0x84cbc];
[0x865a4; 0x852d4];
[0x865a4; 0x852d4; 0x84cbc];
[0x865a4; 0x85338];
[0x865a4; 0x85338; 0x84cbc];
[0x8665c; 0x852d4];
[0x8665c; 0x852d4; 0x84cbc];
[0x8665c; 0x85338];
[0x8665c; 0x85338; 0x84cbc];
[0x86668; 0x852d4];
[0x86668; 0x852d4; 0x84cbc];
[0x86668; 0x85338];
[0x86668; 0x85338; 0x84cbc]].
Definition CTX_ieq : list (list Z) :=
[[0x86558; 0x852d4];
[0x86558; 0x852d4; 0x84cbc];
[0x86558; 0x85338];
[0x86558; 0x85338; 0x84cbc];
[0x86724; 0x852d4];
[0x86724; 0x852d4; 0x84cbc];
[0x86724; 0x85338];
[0x86724; 0x85338; 0x84cbc];
[0x86854; 0x852d4];
[0x86854; 0x852d4; 0x84cbc];
[0x86854; 0x85338];
[0x86854; 0x85338; 0x84cbc]].
Definition CTX_fold : list (list Z) :=
[[0x8673c; 0x852d4];
[0x8673c; 0x852d4; 0x84cbc];
[0x8673c; 0x85338];
[0x8673c; 0x85338; 0x84cbc];
[0x86870; 0x852d4];
[0x86870; 0x852d4; 0x84cbc];
[0x86870; 0x85338];
[0x86870; 0x85338; 0x84cbc]].
Definition CTX_reac_segconf_init : list (list Z) :=
[[0x850d8];
[0x850d8; 0x84cbc]].
Definition CTX_reac_segconf_parse_file : list (list Z) :=
[[0x852e4];
[0x852e4; 0x84cbc];
[0x897a8]].
Definition CTX_refuse : list (list Z) :=
[[0x882b8; 0x852e4];
[0x882b8; 0x852e4; 0x84cbc];
[0x882b8; 0x897a8];
[0x885fc; 0x852e4];
[0x885fc; 0x852e4; 0x84cbc];
[0x885fc; 0x897a8];
[0x887dc; 0x852e4];
[0x887dc; 0x852e4; 0x84cbc];
[0x887dc; 0x897a8];
[0x8897c; 0x852e4];
[0x8897c; 0x852e4; 0x84cbc];
[0x8897c; 0x897a8];
[0x889a4; 0x852e4];
[0x889a4; 0x852e4; 0x84cbc];
[0x889a4; 0x897a8];
[0x88bf0; 0x852e4];
[0x88bf0; 0x852e4; 0x84cbc];
[0x88bf0; 0x897a8];
[0x88c9c; 0x852e4];
[0x88c9c; 0x852e4; 0x84cbc];
[0x88c9c; 0x897a8];
[0x88efc; 0x852e4];
[0x88efc; 0x852e4; 0x84cbc];
[0x88efc; 0x897a8];
[0x89904];
[0x89948]].
Definition CTX_trim : list (list Z) :=
[[0x88390; 0x852e4];
[0x88390; 0x852e4; 0x84cbc];
[0x88390; 0x897a8];
[0x88428; 0x852e4];
[0x88428; 0x852e4; 0x84cbc];
[0x88428; 0x897a8];
[0x88438; 0x852e4];
[0x88438; 0x852e4; 0x84cbc];
[0x88438; 0x897a8];
[0x884ec; 0x852e4];
[0x884ec; 0x852e4; 0x84cbc];
[0x884ec; 0x897a8];
[0x88790; 0x852e4];
[0x88790; 0x852e4; 0x84cbc];
[0x88790; 0x897a8]].
Definition CTX_reac_segconf_parse : list (list Z) :=
[[0x854e0];
[0x854e0; 0x84cbc]].
Definition CTX_cross_check : list (list Z) :=
[[0x897b4]].
Definition CTX_reac_segconf_find : list (list Z) :=
[[0x8760c];
[0x89b94];
[0x89c04];
[0x89cd8];
[0x89d7c];
[0x89e20]].
Definition CTX_reac_segconf_ignored : list (list Z) :=
[[0x85684];
[0x85684; 0x84cbc];
[0x87630]].
Definition CTX_reac_segconf_role : list (list Z) :=
[[0x85658];
[0x85658; 0x84cbc];
[0x87620]].
Definition CTX_reac_segconf_role_file : list (list Z) :=
[[0x85698];
[0x85698; 0x84cbc]].
Definition CTX_reac_segconf_ignore_file : list (list Z) :=
[[0x856a8];
[0x856a8; 0x84cbc]].
Definition CTX_reac_segconf_model : list (list Z) :=
[[0x85670];
[0x85670; 0x84cbc];
[0x87640]].
Definition CTX_reac_segconf_declared : list (list Z) :=
[[0x85e74];
[0x85e74; 0x84cbc]].
Definition CTX_reac_declared_vlan_split : list (list Z) :=
[[0x8a044; 0x85e74];
[0x8a044; 0x85e74; 0x84cbc]].
Definition CTX_name_ok : list (list Z) :=
[[0x8a3b0]].
Definition CTX_reac_declared_vlan_add : list (list Z) :=
[[0x8a070; 0x85e74];
[0x8a070; 0x85e74; 0x84cbc]].
Definition CTX_fuzz_catalogue_row : list (list Z) :=
[[0x86880; 0x852d4];
[0x86880; 0x852d4; 0x84cbc];
[0x86880; 0x85338];
[0x86880; 0x85338; 0x84cbc];
[0x889dc; 0x852e4];
[0x889dc; 0x852e4; 0x84cbc];
[0x889dc; 0x897a8]].
Definition CTX_reac_box_catalogue : list (list Z) :=
[[0x88adc; 0x852e4];
[0x88adc; 0x852e4; 0x84cbc];
[0x88adc; 0x897a8]].
Definition CTX_reac_box_catalogue_by_token : list (list Z) :=
[[0x889dc; 0x852e4];
[0x889dc; 0x852e4; 0x84cbc];
[0x889dc; 0x897a8]].
Definition Tfib_universe : list (list Z) :=
[[0x56e00];
[0x56e00; 0x849ec];
[0x56e00; 0x84b1c];
[0x56e00; 0x84ce8];
[0x56e00; 0x85530];
[0x56e00; 0x85530; 0x84cbc];
[0x56e00; 0x85e9c];
[0x56e00; 0x85e9c; 0x84cbc];
[0x56e00; 0x85ea4];
[0x56e00; 0x85ea4; 0x84cbc];
[0x56e00; 0x85eac];
[0x56e00; 0x85eac; 0x84cbc];
[0x56e00; 0x85eb4];
[0x56e00; 0x85eb4; 0x84cbc];
[0x56f60];
[0x56f60; 0x84974];
[0x56f60; 0x849c8];
[0x56f60; 0x84c54];
[0x56f60; 0x85068];
[0x56f60; 0x85068; 0x84cbc];
[0x56f60; 0x85210];
[0x56f60; 0x85210; 0x84cbc];
[0x57194];
[0x57194; 0x8507c];
[0x57194; 0x8507c; 0x84cbc];
[0x57194; 0x85984];
[0x57194; 0x85984; 0x84cbc];
[0x57194; 0x85994];
[0x57194; 0x85994; 0x84cbc]].
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
