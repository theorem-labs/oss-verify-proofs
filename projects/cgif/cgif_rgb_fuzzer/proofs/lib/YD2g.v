(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG01 YG0h YF9i YF9j YF9m YCeb.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Definition TrbB : asyms := {|
as_code := Trb_code;
as_inst := TRB_INST;
as_gp := TRB_GP;
as_tp := TRB_TP;
as_tsd := TRB_TSD;
as_shadow_cell := 0xab278;
as_uar_cell := 0xab280;
as_got_shadow := 0xa3250;
as_got_uar := 0xa32a8;
as_errno := TRB_ERRNO;
as_depot := TRB_DEPOT;
as_store := TRB_STORE;
as_ialloc_lo := TRB_IAL_LO;
as_ialloc_hi := TRB_IAL_HI;
as_ialloc_w := TRB_IAL_W;
as_ialloc_flag := TRB_IAL_FLAG;
as_oom_byte := TRB_OOM;
as_dhash := trb_dhash;
as_const := Trb_const;
as_junk := fun _ => [(ANum 0xa7ec8, 40)];
as_owned_static := Trb_owned_static;
as_zero_shadow := Trb_zero_shadow;
as_universe := Trb_universe |}.
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
Lemma TrbB_ok : asyms_ok TrbB.
Proof.
constructor.
-   cbn [as_owned_static TrbB]. unfold Trb_owned_static, kImgEnd.
repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil.
-
apply Forall_forall. intros r Hr. apply zr_sub_of_b.
assert (R : forallb (fun r => existsb (fun r' => (fst r' <=? fst r) && (fst r + snd r <=? fst r' + snd r'))%bool Trb_owned_static)
(asyms_areas TrbB) = true) by (vm_compute; reflexivity).
exact (proj1 (forallb_forall _ _) R r Hr).
-   intros ly. cbn [as_const as_shadow_cell as_uar_cell as_got_shadow as_got_uar TrbB]. unfold Trb_const.
assert (A : forall c, In c Trb_const_abs -> In c (Trb_const_sym ++ Trb_const_abs ++ Trb_const_shadow)).
{ intros c Hc. apply in_app_iff. right. apply in_app_iff. left. exact Hc. }
split; [|split; [|split]]; apply A.
+ apply (nth_error_In Trb_const_abs 49). reflexivity.
+ apply (nth_error_In Trb_const_abs 50). reflexivity.
+ apply (nth_error_In Trb_const_abs 144). reflexivity.
+ apply (nth_error_In Trb_const_abs 155). reflexivity.
-   cbn [as_zero_shadow TrbB]. unfold Trb_zero_shadow, kLowMemEnd.
repeat (apply Forall_cons; [cbn [fst snd]; repeat split; try lia; reflexivity|]). apply Forall_nil.
-   cbn [as_ialloc_lo as_ialloc_w as_ialloc_hi TrbB]. unfold TRB_IAL_LO, TRB_IAL_HI, TRB_IAL_W. lia.
-   cbn -[Z.le Z.lt Z.add Z.sub Z.mul Z.pow]. unfold TRB_INST, TRB_DEPOT, TRB_STORE, TRB_IAL_LO, TRB_IAL_HI, TRB_IAL_FLAG, TRB_OOM, TRB_TP, kLowMemEnd. lia.
Qed.
Theorem TrbB_syms : TrbSyms TrbB.
Proof.
constructor; try reflexivity.
- exact TrbB_ok.
-   intros ly r Hr. destruct Hr as [<- | []]. exists 0xa7ec8. cbn [fst snd]. refine (conj eq_refl _). lia.
-   intros ly. left. reflexivity.
-   exact Trb_universe_ok.
-   intros t Ht. cbn [as_universe TrbB].
assert (R : forallb (fun t0 => existsb (fun u => if list_eq_dec Z.eq_dec u t0 then true else false) Trb_universe) DRV_TRACES = true)
by (vm_compute; reflexivity).
exact (In_of_existsb t Trb_universe (proj1 (forallb_forall _ _) R t Ht)).
-   intros h Hh. cbn [as_dhash TrbB]. destruct h as [|[|h]]; [vm_compute; reflexivity | vm_compute; reflexivity | lia].
Qed.
Definition TrbB_pair : asyms_ok TrbB /\ TrbSyms TrbB := conj TrbB_ok TrbB_syms.
