(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YD2l.v, with its module paths changed and its addresses moved to libreac/fuzz_scene's asan-ubsan build. *)
(* Modified by Theorem Labs, 2026-10-29: libreac/fuzz_scene's concrete start-up record B for the asan-ubsan image,
   the instance of `TfibSyms` (lib/AU/YF0m.v:906-930) that lib/AU/SceneBCertBU.v gives to the start-up certificate.
   The names are the record's own (TfibB, TfibB_ok, TfibB_syms), as YF0m.v and SceneBCertU.v state them.
   Its tables are a Theorem Labs lane's (lib/AU/YF0l.v, lib/AU/YF0m.v at a working branch a00b0ed6266) and its
   trace universe is a Theorem Labs lane's measured one (lib/AU/YCej.v at a working branch 1c79108a270). The
   five literals were measured on fuzz_scene.asan-ubsan (unstripped sha256 ef0b41158fe08b45..., stripped
   e98b1ed286c1aa5c..., by an ELF symtab / .got / PT_LOAD read): each is scene's, none is cgif's.
     as_shadow_cell 0xa3af8 = st_value of __asan_shadow_memory_dynamic_address (.bss, 8 bytes) + 0;
     as_uar_cell    0xa3b00 = st_value of __asan_option_detect_stack_use_after_return (.bss, 4 bytes) + 0;
     as_got_shadow  0x9ba40 = the only 8-byte word of the image that holds 0xa3af8 (.got); auipc 0x34148 + ld 0x3414c
                              (in __asan::Allocator::Allocate) loads it;
     as_got_uar     0x9ba98 = the only 8-byte word of the image that holds 0xa3b00 (.got); auipc 0x3f1c4 + ld 0x3f1c8
                              (in __asan_stack_malloc_1) loads it;
     as_junk row    (0xa0748, 40) = TFIB_INST + o_comb_stats = st_value of __asan::instance 0xa0498 + 0x2b0 (YG0f.v:207).
   The two .bss cells hold SHADOW_OFF and 1 only after start-up; their values are the start-up certificate's
   cells Tfib_const_abs[49] and [50] (YF0m.v:83-84), not file bytes. *)
(* ZERO-MARGIN facts of this record's Tfib_owned_static (YF0m.v:894-901), measured on fuzz_scene.asan-ubsan, for
   whoever next edits these tables: each is a premise of the entry statement that holds with no byte to spare.
     - trailer window [0x20e00, 0x20e28): the owned row (0x20dd2, 0x2e) ends exactly at 0x20e00, and (0x20e2c, 0x14)
       starts right after the trailer bytes [0x20e20, 0x20e2c) (HRO_TT, proved in lib/AU/SceneBCertBU.v);
     - placeholder reac_scene_placeholder [0x20e80, 0x23148): the owned row (0x23148, 0x8b8) starts exactly at its
       end. Its length is 8904, the asan_globals descriptor's size; it is NOT the ELF st_size 11136 (0x2b80),
       which includes the 0x8b8-byte redzone, and a range of that length overlaps (0x23148, 0x8b8);
     - the .got word 0x9c6b8 that holds the placeholder's address (loaded by auipc 0x82c64 + ld 0x82c68): the next
       owned row (0x9c6c0, 0x10) starts exactly at its end.
   MEASURED by a Theorem Labs lane (04:19Z): TFIB_TP 0x5d6a98 is tp in all 50 hand-off states of lib/AU/YB01.v (a00b0ed6266),
   builtin_tls + 0xc8; TFIB_ERRNO 0x5d69f4 = tp - 0xa4, from __errno_location (0x8b24c): mv a0, tp;
   addi a0, a0, -0xa4; ret. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG00 YG01 YG0f.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import YF0l YF0m.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YF0p.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import YCej.
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
as_shadow_cell := 0xa3af8;
as_uar_cell := 0xa3b00;
as_got_shadow := 0x9ba40;
as_got_uar := 0x9ba98;
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
as_junk := fun _ => [(ANum 0xa0748, 40)];
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
-   intros ly r Hr. destruct Hr as [<- | []]. exists 0xa0748. cbn [fst snd]. refine (conj eq_refl _). lia.
-   intros ly. left. reflexivity.
-   exact Tfib_universe_ok.
-   intros t Ht. cbn [as_universe TfibB].
assert (R : forallb (fun t0 => existsb (fun u => if list_eq_dec Z.eq_dec u t0 then true else false) Tfib_universe) DRV_TRACES = true)
by (vm_compute; reflexivity).
exact (In_of_existsb t Tfib_universe (proj1 (forallb_forall _ _) R t Ht)).
-   intros h Hh. cbn [as_dhash TfibB]. destruct h as [|[|h]]; [vm_compute; reflexivity | vm_compute; reflexivity | lia].
Qed.
Definition TfibB_pair : asyms_ok TfibB /\ TfibSyms TfibB := conj TfibB_ok TfibB_syms.
(* Stack-malloc class 8 has no entry in scene's Tfib_code (YF0l.v:13, the `else 0` branch). *)
Example TfibB_class8 : pc_stack_malloc (as_code TfibB) 8 = 0.
Proof. reflexivity. Qed.
