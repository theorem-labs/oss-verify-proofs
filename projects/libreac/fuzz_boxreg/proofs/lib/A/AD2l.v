(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AD2l.v (origin/ossv/recipes c8557374ad2) in the form of libreac/fuzz_grant's lib/A/AD2l.v (a working branch ac3f475adac), with its module paths changed, TfibSyms -> BoxregSyms (the name lib/A/AF0m.v has), its addresses measured on libreac/fuzz_boxreg's ASan build, and the four aso_const_law cells found in Tfib_const_abs by search instead of by position. *)
(* libreac/fuzz_boxreg's asyms instance for its ASan build (fuzz_boxreg.asan, sha256 eacfa20547ad7dc0...): TfibB, with
   asyms_ok (TfibB_ok) and BoxregSyms (TfibB_syms). Rule 24: no function is proved here.
   Its data is lib/A/AF0m.v, the file a Theorem Labs lane's run of a Theorem Labs lane's tools/startup/af0m.py writes (TFIB_*, DRV_TRACES,
   Tfib_const, Tfib_owned_static, Tfib_zero_shadow, TFIB_TR0 / TFIB_HASH), and lib/A/ACej.v, the file its universe.py
   writes (Tfib_universe); lib/A/Prog/BoxTraces.v is a cross-check reference only. None of these values is restated here.
   The fields this file sets, each measured on this image (nm): as_shadow_cell 0xa0f78
   (__asan_shadow_memory_dynamic_address), as_uar_cell 0xa0f80 (__asan_option_detect_stack_use_after_return), their GOT
   slots as_got_shadow 0x98eb8 and as_got_uar 0x98f10 (.got + 0x60 and + 0xb8; the two GOTs of fuzz_grant.asan and this
   image hold the same symbol in each slot); as_junk, the allocator instance's combined stats TFIB_INST + o_comb_stats =
   0x9dbc8, 40 bytes (cgif's field). The aso_const_law cells are found in Tfib_const_abs by zcell_in (a vm_compute search),
   so a re-run of the generator that moves rows does not break the proof.
   The read-only gate (a Theorem Labs lane's row 37; a Theorem Labs lane's ruling 23:56Z): TfibB_ro_gate, with no premise. Every owned byte in a
   read-only segment is pinned to its image byte by a row of Tfib_const_abs, which af0m.py emits since its 01:59Z re-run
   (lib/A/AF0mCheck.v box_ro_pinned, one vm_compute; the 26 pin rows, appended at the table's end as rows 230..255 of 255, cover the 144 bytes
   of the 5 read-only globals' right redzones).
   Needs, not on this branch: lib/A/AF0m.v and lib/A/ACej.v (generated, pending their gate), lib/A/AF0l.v (Tfib_code, the
   core file lib/A/AF0m.v Requires; lib/A/Prog/BoxB.v's box_code holds the same 25 entries measured on this image) and
   lib/Reusable/YF0p.v (tfib_dhash, the depot hash; cgif's lib/YF0p.v). lib/A/AF0mCheck.v lands with this file. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG00 YG01 YG0f.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A Require Import AF0l AF0m.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YF0p.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A Require Import ACej AF0mCheck.
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
as_shadow_cell := 0xa0f78;
as_uar_cell := 0xa0f80;
as_got_shadow := 0x98eb8;
as_got_uar := 0x98f10;
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
as_junk := fun _ => [(ANum 0x9dbc8, 40)];
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
Definition zcell_eqb (c : acell) (a : Z) (w : nat) (v : Z) : bool :=
match c with ACell (ANum a') w' (AV (ANum v')) => (a' =? a) && Nat.eqb w' w && (v' =? v) | _ => false end.
Lemma zcell_in : forall l a w v, existsb (fun c => zcell_eqb c a w v) l = true -> In (ACell (ANum a) w (AV (ANum v))) l.
Proof.
intros l a w v H. apply existsb_exists in H as (c & Hc & Hb). destruct c as [e w' av].
destruct e; cbn in Hb; try discriminate. destruct av as [e'|]; cbn in Hb; try discriminate. destruct e'; cbn in Hb; try discriminate. apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2].
apply Z.eqb_eq in H1. apply Nat.eqb_eq in H2. apply Z.eqb_eq in H3. subst. exact Hc.
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
split; [|split; [|split]]; apply A; cbv [z8 z4 c8 c4]; apply zcell_in; vm_compute; reflexivity.
-   cbn [as_zero_shadow TfibB]. unfold Tfib_zero_shadow, kLowMemEnd.
repeat (apply Forall_cons; [cbn [fst snd]; repeat split; try lia; reflexivity|]). apply Forall_nil.
-   cbn [as_ialloc_lo as_ialloc_w as_ialloc_hi TfibB]. unfold TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_W. lia.
-   cbn -[Z.le Z.lt Z.add Z.sub Z.mul Z.pow]. unfold TFIB_INST, TFIB_DEPOT, TFIB_STORE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, TFIB_OOM, TFIB_TP, kLowMemEnd. lia.
Qed.
Theorem TfibB_syms : BoxregSyms TfibB.
Proof.
constructor; try reflexivity.
- exact TfibB_ok.
-   intros ly r Hr. destruct Hr as [<- | []]. exists 0x9dbc8. cbn [fst snd]. refine (conj eq_refl _). lia.
-   intros ly. left. reflexivity.
-   exact Tfib_universe_ok.
-   intros t Ht. cbn [as_universe TfibB].
assert (R : forallb (fun t0 => existsb (fun u => if list_eq_dec Z.eq_dec u t0 then true else false) Tfib_universe) DRV_TRACES = true)
by (vm_compute; reflexivity).
exact (In_of_existsb t Tfib_universe (proj1 (forallb_forall _ _) R t Ht)).
-   intros h Hh. cbn [as_dhash TfibB]. destruct h as [|[|h]]; [vm_compute; reflexivity | vm_compute; reflexivity | lia].
Qed.
Definition TfibB_pair : asyms_ok TfibB /\ BoxregSyms TfibB := conj TfibB_ok TfibB_syms.
Lemma TfibB_ro_gate : forall ly a, Exists (fun s => fst s <= a < fst s + snd s) box_ro_ranges ->
Exists (fun r => fst r <= a < fst r + snd r) (as_owned_static TfibB) ->
Exists (fun c => exists a' v, c_at c = ANum a' /\ c_val c = AV (ANum v) /\ a' <= a < a' + Z.of_nat (c_w c) /\
  img_word a' (c_w c) = Some v) (as_const TfibB ly).
Proof.
intros ly a Hs Ho. cbn [as_const as_owned_static TfibB] in Ho |- *.
pose proof (box_ro_gate_holds a Hs Ho) as G. apply Exists_exists in G as (c & Hc & Pc). apply Exists_exists. exists c. split; [|exact Pc].
unfold Tfib_const. apply in_app_iff. right. apply in_app_iff. left. exact Hc.
Qed.
