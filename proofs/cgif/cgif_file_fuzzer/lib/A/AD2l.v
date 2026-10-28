(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG01 YG0f.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AF0l AF0m.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YF0p.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACej.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Definition TfibB : asyms := {|
as_code := Tfib_code;
as_inst := TFIB_INST;
as_gp := TFIB_GP;
as_tp := TFIB_TP;
as_tsd := TFIB_TSD;
as_shadow_cell := 0xa5ff8;
as_uar_cell := 0xa6000;
as_got_shadow := 0x9df98;
as_got_uar := 0x9dff0;
as_errno := TFIB_ERRNO;
as_depot := TFIB_DEPOT;
as_store := TFIB_STORE;
as_ialloc_lo := TFIB_IAL_LO;
as_ialloc_hi := TFIB_IAL_HI;
as_ialloc_w := TFIB_IAL_W;
as_ialloc_flag := TFIB_IAL_FLAG;
as_oom_byte := TFIB_OOM;
as_dhash := tfib_dhash;
as_const := Tfib_const;
as_junk := fun _ => [(ANum 0xa2c48, 40)];
as_owned_static := Tfib_owned_static;
as_zero_shadow := Tfib_zero_shadow;
as_universe := Tfib_universe |}.
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
Lemma TfibB_ok : asyms_ok TfibB.
Proof.
constructor.
-   cbn [as_owned_static TfibB]. unfold Tfib_owned_static, kImgEnd.
repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil.
-
apply Forall_forall. intros r Hr. apply zr_sub_of_b.
assert (R : forallb (fun r => existsb (fun r' => (fst r' <=? fst r) && (fst r + snd r <=? fst r' + snd r'))%bool Tfib_owned_static)
(asyms_areas TfibB) = true) by (vm_compute; reflexivity).
exact (proj1 (forallb_forall _ _) R r Hr).
-   intros ly. cbn [as_const as_shadow_cell as_uar_cell as_got_shadow as_got_uar TfibB]. unfold Tfib_const.
assert (A : forall c, In c Tfib_const_abs -> In c (Tfib_const_sym ++ Tfib_const_abs ++ Tfib_const_shadow)).
{ intros c Hc. apply in_app_iff. right. apply in_app_iff. left. exact Hc. }
split; [|split; [|split]]; apply A.
+ apply (nth_error_In Tfib_const_abs 49). reflexivity.
+ apply (nth_error_In Tfib_const_abs 50). reflexivity.
+ apply (nth_error_In Tfib_const_abs 144). reflexivity.
+ apply (nth_error_In Tfib_const_abs 155). reflexivity.
-   cbn [as_zero_shadow TfibB]. unfold Tfib_zero_shadow, kLowMemEnd.
repeat (apply Forall_cons; [cbn [fst snd]; repeat split; try lia; reflexivity|]). apply Forall_nil.
-   cbn [as_ialloc_lo as_ialloc_w as_ialloc_hi TfibB]. unfold TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_W. lia.
-   cbn -[Z.le Z.lt Z.add Z.sub Z.mul Z.pow]. unfold TFIB_INST, TFIB_DEPOT, TFIB_STORE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, TFIB_OOM, TFIB_TP, kLowMemEnd. lia.
Qed.
Theorem TfibB_syms : TfibSyms TfibB.
Proof.
constructor; try reflexivity.
- exact TfibB_ok.
-   intros ly r Hr. destruct Hr as [<- | []]. exists 0xa2c48. cbn [fst snd]. refine (conj eq_refl _). lia.
-   intros ly. left. reflexivity.
-   exact Tfib_universe_ok.
-   intros t Ht. cbn [as_universe TfibB].
assert (R : forallb (fun t0 => existsb (fun u => if list_eq_dec Z.eq_dec u t0 then true else false) Tfib_universe) DRV_TRACES = true)
by (vm_compute; reflexivity).
exact (In_of_existsb t Tfib_universe (proj1 (forallb_forall _ _) R t Ht)).
-   intros h Hh. cbn [as_dhash TfibB]. destruct h as [|[|h]]; [vm_compute; reflexivity | vm_compute; reflexivity | lia].
Qed.
Definition TfibB_pair : asyms_ok TfibB /\ TfibSyms TfibB := conj TfibB_ok TfibB_syms.
