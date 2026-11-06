(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG01 YG0h YF8z YF90 YF93 YC1d.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Definition TraB : asyms := {|
as_code := Tra_code;
as_inst := TRA_INST;
as_gp := TRA_GP;
as_tp := TRA_TP;
as_tsd := TRA_TSD;
as_shadow_cell := 0xaa1b8;
as_uar_cell := 0xaa1c0;
as_got_shadow := 0xa2160;
as_got_uar := 0xa21b8;
as_errno := TRA_ERRNO;
as_depot := TRA_DEPOT;
as_store := TRA_STORE;
as_ialloc_lo := TRA_IAL_LO;
as_ialloc_hi := TRA_IAL_HI;
as_ialloc_w := TRA_IAL_W;
as_ialloc_flag := TRA_IAL_FLAG;
as_oom_byte := TRA_OOM;
as_dhash := tra_dhash;
as_const := Tra_const;
as_junk := fun _ => [(ANum 0xa6e08, 40)];
as_owned_static := Tra_owned_static;
as_zero_shadow := Tra_zero_shadow;
as_universe := Tra_universe |}.
Lemma In_of_existsb : forall (t : list Z) (U : list (list Z)),
existsb (fun u => if list_eq_dec Z.eq_dec u t then true else false) U = true -> In t U.
Proof.
intros t U H. apply existsb_exists in H as (u & Hu & Hb). destruct (list_eq_dec Z.eq_dec u t) as [<-|]; [exact Hu | discriminate].
Qed.
Lemma zr_sub_of_b : forall r l,
existsb (fun r' => (fst r' <=? fst r) && (fst r + snd r <=? fst r' + snd r'))%bool l = true -> Exists (zr_sub r) l.
Proof.
intros r l H. apply existsb_exists in H as (r' & Hr' & Hb). apply Exists_exists. exists r'. split; [exact Hr'|].
apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. unfold zr_sub. split; [exact H1 | exact H2].
Qed.
Lemma TraB_ok : asyms_ok TraB.
Proof.
constructor.
-   cbn [as_owned_static TraB]. unfold Tra_owned_static, kImgEnd.
repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil.
-
apply Forall_forall. intros r Hr. apply zr_sub_of_b.
assert (R : forallb (fun r => existsb (fun r' => (fst r' <=? fst r) && (fst r + snd r <=? fst r' + snd r'))%bool Tra_owned_static)
(asyms_areas TraB) = true) by (vm_compute; reflexivity).
exact (proj1 (forallb_forall _ _) R r Hr).
-   intros ly. cbn [as_const as_shadow_cell as_uar_cell as_got_shadow as_got_uar TraB]. unfold Tra_const.
assert (A : forall c, In c Tra_const_abs -> In c (Tra_const_sym ++ Tra_const_abs ++ Tra_const_shadow)).
{ intros c Hc. apply in_app_iff. right. apply in_app_iff. left. exact Hc. }
split; [|split; [|split]]; apply A.
+ apply (nth_error_In Tra_const_abs 49). reflexivity.
+ apply (nth_error_In Tra_const_abs 50). reflexivity.
+ apply (nth_error_In Tra_const_abs 144). reflexivity.
+ apply (nth_error_In Tra_const_abs 155). reflexivity.
-   cbn [as_zero_shadow TraB]. unfold Tra_zero_shadow, kLowMemEnd.
repeat (apply Forall_cons; [cbn [fst snd]; repeat split; try lia; reflexivity|]). apply Forall_nil.
-   cbn [as_ialloc_lo as_ialloc_w as_ialloc_hi TraB]. unfold TRA_IAL_LO, TRA_IAL_HI, TRA_IAL_W. lia.
-   cbn -[Z.le Z.lt Z.add Z.sub Z.mul Z.pow]. unfold TRA_INST, TRA_DEPOT, TRA_STORE, TRA_IAL_LO, TRA_IAL_HI, TRA_IAL_FLAG, TRA_OOM, TRA_TP, kLowMemEnd. lia.
Qed.
Theorem TraB_syms : TraSyms TraB.
Proof.
constructor; try reflexivity.
- exact TraB_ok.
-   intros ly r Hr. destruct Hr as [<- | []]. exists 0xa6e08. cbn [fst snd]. refine (conj eq_refl _). lia.
-   intros ly. left. reflexivity.
-   exact Tra_universe_ok.
-   intros t Ht. cbn [as_universe TraB].
assert (R : forallb (fun t0 => existsb (fun u => if list_eq_dec Z.eq_dec u t0 then true else false) Tra_universe) DRV_TRACES = true)
by (vm_compute; reflexivity).
exact (In_of_existsb t Tra_universe (proj1 (forallb_forall _ _) R t Ht)).
-   intros h Hh. cbn [as_dhash TraB]. destruct h as [|[|h]]; [vm_compute; reflexivity | vm_compute; reflexivity | lia].
Qed.
Definition TraB_pair : asyms_ok TraB /\ TraSyms TraB := conj TraB_ok TraB_syms.
