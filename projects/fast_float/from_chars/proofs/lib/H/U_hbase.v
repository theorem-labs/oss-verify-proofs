(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg FPInv.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac RegsEquiv Bridge.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require Import HIface.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Notation USEGS := Ubsan.M.loaded_segments.

Definition U_IMG_LO : Z := 0x10000.
Definition U_IMG_END : Z := 0x99000.
Definition U_PC_MALLOC : Z := 0x530c8.
Definition U_PC_FREE : Z := 0x52f88.
Definition U_MNEED : Z := 8192.          (* [comment removed for export] *)
Definition U_FNEED : Z := 8192.          (* [comment removed for export] *)

(* [comment removed for export] *)
Definition U_KEEP : list ivl := [(0x65b58, 0x65b60); (0x97c00, 0x97c08); (0x18288, 0x182a8); (0x182a8, 0x18327)]%Z.

(* [comment removed for export] *)
Ltac keep_side := let a := fresh "a" in let Ha := fresh "Ha" in
  intros a Ha; unfold U_KEEP in Ha; apply not_outside_4 in Ha; split; [lia|]; cbn [outside]; repeat split; try exact I; lia.

Definition U_heap_ok (cfg : SpuriousCfg) (HI : heap_iface) (GP TP : word) (HTOP : Z) (STATIC : list ivl) : Prop :=
  heap_ok USEGS cfg HI GP TP U_IMG_LO U_IMG_END HTOP STATIC U_KEEP U_PC_MALLOC U_MNEED U_PC_FREE U_FNEED.

(* [comment removed for export] *)
Definition keep (P : Prop) : Prop := P.

(* [comment removed for export] *)
Ltac exit_rz r HR :=
  apply evt_exit_rz; let fx := fresh "fx" in let Hfc := fresh "Hfc" in intros fx r HR Hfc; try unfold mkR in HR.

(* [comment removed for export] *)
Ltac resume MD :=
  apply rz_of_evt; [exact MD|]; unfold mkR_of.

(* [comment removed for export] *)
Ltac getr_of HR k := let H := fresh "G" in pose proof (HR k) as H; cbn [getr_mkR] in H; rewrite getr_mkR in H; cbv beta iota in H.

(* [comment removed for export] *)
Ltac getr_leaf_in H :=
  lazymatch type of H with
  | _ = getr ?R ?k =>
      let b := eval vm_compute in (bv_eqb k 0) in
      let p := eval vm_compute in (bv_key k) in
      change (getr R k) with (if b then Z_to_bv 64 0 else match tget p R with Some v => v | None => w0 end) in H;
      cbv beta iota delta [tget] in H
  end.
Ltac getr_leaf :=
  match goal with
  | |- context [getr ?R ?k] => is_concrete_map R;
      let b := eval vm_compute in (bv_eqb k 0) in
      let p := eval vm_compute in (bv_key k) in
      change (getr R k) with (if b then Z_to_bv 64 0 else match tget p R with Some v => v | None => w0 end);
      cbv beta iota delta [tget]
  end.
(* [comment removed for export] *)
Ltac getr_all HR :=
  let G1 := fresh "G1" in pose proof (HR 1) as G1; getr_leaf_in G1;
  let G2 := fresh "G2" in pose proof (HR 2) as G2; getr_leaf_in G2;
  let G3 := fresh "G3" in pose proof (HR 3) as G3; getr_leaf_in G3;
  let G4 := fresh "G4" in pose proof (HR 4) as G4; getr_leaf_in G4;
  let G8 := fresh "G8" in pose proof (HR 8) as G8; getr_leaf_in G8;
  let G9 := fresh "G9" in pose proof (HR 9) as G9; getr_leaf_in G9;
  let G10 := fresh "G10" in pose proof (HR 10) as G10; getr_leaf_in G10;
  let G11 := fresh "G11" in pose proof (HR 11) as G11; getr_leaf_in G11;
  let G12 := fresh "G12" in pose proof (HR 12) as G12; getr_leaf_in G12;
  let G13 := fresh "G13" in pose proof (HR 13) as G13; getr_leaf_in G13;
  let G18 := fresh "G18" in pose proof (HR 18) as G18; getr_leaf_in G18;
  let G19 := fresh "G19" in pose proof (HR 19) as G19; getr_leaf_in G19;
  let G20 := fresh "G20" in pose proof (HR 20) as G20; getr_leaf_in G20;
  let G21 := fresh "G21" in pose proof (HR 21) as G21; getr_leaf_in G21;
  let G22 := fresh "G22" in pose proof (HR 22) as G22; getr_leaf_in G22;
  let G23 := fresh "G23" in pose proof (HR 23) as G23; getr_leaf_in G23;
  let G24 := fresh "G24" in pose proof (HR 24) as G24; getr_leaf_in G24;
  let G25 := fresh "G25" in pose proof (HR 25) as G25; getr_leaf_in G25;
  let G26 := fresh "G26" in pose proof (HR 26) as G26; getr_leaf_in G26;
  let G27 := fresh "G27" in pose proof (HR 27) as G27; getr_leaf_in G27.

(* [comment removed for export] *)
Ltac cs_resume CS HR1 :=
  let C2 := fresh "CSr" in let C3 := fresh "CSr" in let C4 := fresh "CSr" in let C8 := fresh "CSr" in let C9 := fresh "CSr" in
  let C18 := fresh "CSr" in let C19 := fresh "CSr" in let C20 := fresh "CSr" in let C21 := fresh "CSr" in let C22 := fresh "CSr" in
  let C23 := fresh "CSr" in let C24 := fresh "CSr" in let C25 := fresh "CSr" in let C26 := fresh "CSr" in let C27 := fresh "CSr" in
  destruct CS as (C2 & C3 & C4 & C8 & C9 & C18 & C19 & C20 & C21 & C22 & C23 & C24 & C25 & C26 & C27);
  rewrite C2, C3, C4, C8, C9, C18, C19, C20, C21, C22, C23, C24, C25, C26, C27;
  rewrite !HR1; repeat getr_leaf.

(* [comment removed for export] *)
Ltac if_vm :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
      let v := eval vm_compute in c in replace c with v by (vm_compute; reflexivity); cbv iota
  end.
