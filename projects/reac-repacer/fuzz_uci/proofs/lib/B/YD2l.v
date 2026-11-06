(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AD2l.v, with its module paths changed, names TfibB -> UciB, TfibSyms -> UciSyms, TfibB_syms -> UciB_syms, TfibB_ok -> UciB_ok, TfibB_pair -> UciB_pair and its addresses moved to libreac/fuzz_grant's ASan build. *)
(* Modified by Theorem Labs, 2026-10: grant A's file relocated to image B (fuzz_grant.asan-ubsan fde52226dc48) by port_core 53ec3af2afc9, A -> B; the numbers below are image B's unless a comment says image A. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_grant/lib/YD2l.v (donor image sha256 fde52226dc48), with its module paths changed, names GrantB -> UciB, GrantSyms -> UciSyms, GrantB_syms -> UciB_syms, GrantB_ok -> UciB_ok and its addresses moved to reac-repacer/fuzz_uci's ASan build. *)
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YG00 YG01 YG0f.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B Require Import YF0l YF0m.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YF0p.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B Require Import YCej.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Definition UciB : asyms := {|
as_code := Tfib_code;
as_inst := TFIB_INST;
as_gp := TFIB_GP;
as_tp := TFIB_TP;
as_tsd := TFIB_TSD;
as_shadow_cell := 0x9f0f8;
as_uar_cell := 0x9f100;
as_got_shadow := 0x97128;
as_got_uar := 0x97180;
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
as_junk := fun _ => [(ANum 0x9bd48, 40)];
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
Lemma UciB_ok : asyms_ok UciB.
Proof.
constructor.
-   cbn [as_owned_static UciB]. unfold Tfib_owned_static, kImgEnd.
repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil.
-
apply Forall_forall. intros r Hr. apply zr_sub_of_b.
assert (R : forallb (fun r => existsb (fun r' => (fst r' <=? fst r) && (fst r + snd r <=? fst r' + snd r'))%bool Tfib_owned_static)
(asyms_areas UciB) = true) by (vm_compute; reflexivity).
exact (proj1 (forallb_forall _ _) R r Hr).
-   intros ly. cbn [as_const as_shadow_cell as_uar_cell as_got_shadow as_got_uar UciB]. unfold Tfib_const.
assert (A : forall c, In c Tfib_const_abs -> In c (Tfib_const_sym ++ Tfib_const_abs ++ Tfib_const_shadow)).
{ intros c Hc. apply in_app_iff. right. apply in_app_iff. left. exact Hc. }
split; [|split; [|split]]; apply A.
+ apply (nth_error_In Tfib_const_abs 49). reflexivity.
+ apply (nth_error_In Tfib_const_abs 50). reflexivity.
+ apply (nth_error_In Tfib_const_abs 144). reflexivity.
+ apply (nth_error_In Tfib_const_abs 155). reflexivity.
-   cbn [as_zero_shadow UciB]. unfold Tfib_zero_shadow, kLowMemEnd.
repeat (apply Forall_cons; [cbn [fst snd]; repeat split; try lia; reflexivity|]). apply Forall_nil.
-   cbn [as_ialloc_lo as_ialloc_w as_ialloc_hi UciB]. unfold TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_W. lia.
-   cbn -[Z.le Z.lt Z.add Z.sub Z.mul Z.pow]. unfold TFIB_INST, TFIB_DEPOT, TFIB_STORE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, TFIB_OOM, TFIB_TP, kLowMemEnd. lia.
Qed.
Theorem UciB_syms : UciSyms UciB.
Proof.
constructor; try reflexivity.
- exact UciB_ok.
-   intros ly r Hr. destruct Hr as [<- | []]. exists 0x9bd48. cbn [fst snd]. refine (conj eq_refl _). lia.
-   intros ly. left. reflexivity.
-   exact Tfib_universe_ok.
-   intros t Ht. cbn [as_universe UciB].
assert (R : forallb (fun t0 => existsb (fun u => if list_eq_dec Z.eq_dec u t0 then true else false) Tfib_universe) DRV_TRACES = true)
by (vm_compute; reflexivity).
exact (In_of_existsb t Tfib_universe (proj1 (forallb_forall _ _) R t Ht)).
-   intros h Hh. cbn [as_dhash UciB]. destruct h as [|[|h]]; [vm_compute; reflexivity | vm_compute; reflexivity | lia].
Qed.
Definition UciB_pair : asyms_ok UciB /\ UciSyms UciB := conj UciB_ok UciB_syms.
