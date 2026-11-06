(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Run StackLayout.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaTuning Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Class runConstT : Type := RunConst {
  ATOP : Z;
  SECRET : Z;
  CAN : word;
  ATOP_lo : 0x7fff7f800000 <= ATOP;
  ATOP_hi : ATOP <= 0x7FFFFF800000;
  ATOP_pg : ATOP mod 4096 = 0;       (* [comment removed for export] *)
  SECRET_rng : 0 <= SECRET < 2^64
}.

Lemma ATOP_al16 {rc : runConstT} : ATOP mod 16 = 0.
Proof. pose proof (@ATOP_pg rc) as P. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
#[export] Instance ceil_of_rc {rc : runConstT} : CEIL :=
  {| alloc_ceiling := ATOP; ceil_floor := ATOP_lo; ceil_max := ATOP_hi; ceil_pg := ATOP_pg |}.
Lemma alloc_ceiling_rc : forall {rc : runConstT}, @alloc_ceiling ceil_of_rc = ATOP.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition ATOP_MIN : Z := 0x7fff7f800000.
Definition ATOP_MAX : Z := 0x7FFFFF800000.

Lemma ATOP_range {rc : runConstT} : ATOP_MIN <= ATOP <= ATOP_MAX.
Proof. unfold ATOP_MIN, ATOP_MAX. split; [apply ATOP_lo | apply ATOP_hi]. Qed.

(* [comment removed for export] *)
Definition rc_of_ceil {CE : CEIL} (sec : Z) (c : word) (Hs : 0 <= sec < 2^64) : runConstT :=
  {| ATOP := alloc_ceiling; SECRET := sec; CAN := c;
     ATOP_lo := ceil_floor; ATOP_hi := ceil_max; ATOP_pg := ceil_pg; SECRET_rng := Hs |}.

Lemma rc_of_ceil_ATOP : forall {CE : CEIL} sec c Hs, @ATOP (rc_of_ceil sec c Hs) = alloc_ceiling.
Proof. reflexivity. Qed.
Lemma rc_of_ceil_SECRET : forall {CE : CEIL} sec c Hs, @SECRET (rc_of_ceil sec c Hs) = sec.
Proof. reflexivity. Qed.
Lemma rc_of_ceil_CAN : forall {CE : CEIL} sec c Hs, @CAN (rc_of_ceil sec c Hs) = c.
Proof. reflexivity. Qed.
