(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG01 YG0h YG0d YB1u YF9i YF9j YF9m YCeb YD2g YCe8.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Lemma trb_lib_consts_chk :
forallb (fun r => ((fst r + snd r <=? 0x103d8) || (0x103e0 <=? fst r)) && ((fst r + snd r <=? 0xa3ec8) || (0xa3ef0 <=? fst r)))%bool
Trb_owned_static = true.
Proof. vm_compute. reflexivity. Qed.
Theorem TrbB_lib : TrbLib TrbB.
Proof.
constructor; try reflexivity.
-   cbn [as_errno TrbB]. unfold TRB_ERRNO, kLowMemEnd. lia.
-
intros a Ha. cbn [as_errno TrbB] in Ha. unfold TRB_ERRNO in Ha. unfold in_img.
assert (Hb : nth_error (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) trbsegs) 3 = Some (0xa4000, 0x55c000))
by (vm_compute; reflexivity).
rewrite nth_error_map in Hb. destruct (nth_error trbsegs 3) as [sg|] eqn:E; [|discriminate Hb]. cbn in Hb. injection Hb as H1 H2.
exists sg. split; [exact (nth_error_In _ 3 E) | rewrite H1, H2; lia].
-   intros a Ha. cbn [as_owned_static as_errno TrbB]. unfold TRB_ERRNO. unfold lib_const_addr in Ha. split; [|lia].
intros HE. apply Exists_exists in HE as (r & Hr & [H1 H2]).
pose proof (proj1 (forallb_forall _ _) trb_lib_consts_chk r Hr) as Hb. cbn beta in Hb.
apply andb_prop in Hb as [Hb1 Hb2]. apply Bool.orb_prop in Hb1 as [Hb1|Hb1]; apply Z.leb_le in Hb1;
apply Bool.orb_prop in Hb2 as [Hb2|Hb2]; apply Z.leb_le in Hb2; lia.
-   cbn [as_gp TrbB]. unfold TRB_GP. lia.
Qed.
Definition TrbB_facts : TrbSyms TrbB /\ TrbLib TrbB := conj TrbB_syms TrbB_lib.
