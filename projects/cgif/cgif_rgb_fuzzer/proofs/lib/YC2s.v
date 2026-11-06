(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG01 YG0h YG0d YB0z YF8z YF90 YF93 YC1d YD16 YD17 YC1a.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Lemma tra_lib_consts_chk :
forallb (fun r => ((fst r + snd r <=? 0x103b8) || (0x103c0 <=? fst r)) && ((fst r + snd r <=? 0xa2dd8) || (0xa2e00 <=? fst r)))%bool
Tra_owned_static = true.
Proof. vm_compute. reflexivity. Qed.
Theorem TraB_lib : TraLib TraB.
Proof.
constructor; try reflexivity.
-   cbn [as_errno TraB]. unfold TRA_ERRNO, kLowMemEnd. lia.
-
intros a Ha. cbn [as_errno TraB] in Ha. unfold TRA_ERRNO in Ha. unfold in_img.
assert (Hb : nth_error (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) trasegs) 3 = Some (0xa3000, 0x55c000))
by (vm_compute; reflexivity).
rewrite nth_error_map in Hb. destruct (nth_error trasegs 3) as [sg|] eqn:E; [|discriminate Hb]. cbn in Hb. injection Hb as H1 H2.
exists sg. split; [exact (nth_error_In _ 3 E) | rewrite H1, H2; lia].
-   intros t Ht. exact Ht.
-   intros a Ha. cbn [as_owned_static as_errno TraB]. unfold TRA_ERRNO. unfold lib_const_addr in Ha. split; [|lia].
intros HE. apply Exists_exists in HE as (r & Hr & [H1 H2]).
pose proof (proj1 (forallb_forall _ _) tra_lib_consts_chk r Hr) as Hb. cbn beta in Hb.
apply andb_prop in Hb as [Hb1 Hb2]. apply Bool.orb_prop in Hb1 as [Hb1|Hb1]; apply Z.leb_le in Hb1;
apply Bool.orb_prop in Hb2 as [Hb2|Hb2]; apply Z.leb_le in Hb2; lia.
-   cbn [as_gp TraB]. unfold TRA_GP. lia.
Qed.
Theorem TraBx_lib : forall xs, TraLib (TraBx xs).
Proof.
intros xs. destruct TraB_lib as [L1 L2 L3 L4 L5 L6 L7 L8 L9 L10].
constructor; [exact L1 | exact L2 | exact L3 | exact L4 | exact L5 | exact L6 | exact L7 | | exact L9 | exact L10].
intros t Ht. cbn [as_universe TraBx]. apply in_or_app. left. exact Ht.
Qed.
Definition TraB_facts : TraSyms TraB /\ TraLib TraB := conj TraB_syms TraB_lib.
