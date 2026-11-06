(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjS1Out SjStage2 SjLeaves.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Sj_stage2_defs Sj_stage2_numkit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Section NumODefs.
  Variable E : s2env.
  Notation bs := (e_bs E).

  Definition OSL (neg : Z) (s : st) (Wv : Z) (j0 j8 j16 j72 : list byte) : list cell :=
    [CB 8 j0; CB 8 j8; CB 8 j16; C8 (Z_to_bv 64 (e_BUF E + e_off E (k s))); C8 (Z_to_bv 64 neg); C8 (Z_to_bv 64 (depth s));
     C8 (Z_to_bv 64 (e_IDX E + 4 * (k s + 1))); C8 (Z_to_bv 64 (e_TAPE E + 8 * Wv)); C8 (Z_to_bv 64 (e_SBUF E + sb s)); CB 8 j72].

  Lemma MEMI_OSL : forall nxt neg s Wv c0 c8 c16 c72 sc fc m1,
    MEMI E nxt [c0; c8; c16; C8 (Z_to_bv 64 (e_BUF E + e_off E (k s))); C8 (Z_to_bv 64 neg); C8 (Z_to_bv 64 (depth s));
                C8 (Z_to_bv 64 (e_IDX E + 4 * (k s + 1))); C8 (Z_to_bv 64 (e_TAPE E + 8 * Wv)); C8 (Z_to_bv 64 (e_SBUF E + sb s)); c72] sc fc m1 ->
    csize c0 = 8%nat -> csize c8 = 8%nat -> csize c16 = 8%nat -> csize c72 = 8%nat ->
    MEMI E nxt (OSL neg s Wv (cbytes c0) (cbytes c8) (cbytes c16) (cbytes c72)) sc fc m1.
  Proof.
    intros nxt neg s Wv c0 c8 c16 c72 sc fc m1 H E0 E8 E16 E72. unfold OSL.
    apply (MEMI_forget8 E nxt [] c0 _ sc fc m1 E0) in H. cbn [app] in H.
    apply (MEMI_forget8 E nxt [_] c8 _ sc fc m1 E8) in H. cbn [app] in H.
    apply (MEMI_forget8 E nxt [_; _] c16 _ sc fc m1 E16) in H. cbn [app] in H.
    apply (MEMI_forget8 E nxt [_; _; _; _; _; _; _; _; _] c72 _ sc fc m1 E72) in H. cbn [app] in H.
    exact H.
  Qed.

  Definition OFSL (v0 v8 v16 : word) (neg : Z) (s : st) (Wv : Z) (j72 : list byte) : list cell :=
    [C8 v0; C8 v8; C8 v16; C8 (Z_to_bv 64 (e_BUF E + e_off E (k s))); C8 (Z_to_bv 64 neg); C8 (Z_to_bv 64 (depth s));
     C8 (Z_to_bv 64 (e_IDX E + 4 * (k s + 1))); C8 (Z_to_bv 64 (e_TAPE E + 8 * Wv)); C8 (Z_to_bv 64 (e_SBUF E + sb s)); CB 8 j72].

  Definition numo_scan_k (Q : machine_state -> Prop) (s : st) (neg : Z) (Wv : Z) (pc p : Z) : Prop :=
    forall xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa4 xa6 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt4 xt5 xt6 j0 j8 j16 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) (OSL neg s Wv j0 j8 j16 j72) (scopes s) fc m1 ->
      evt psegs Q (S2R E pc xra xt0 xt1 xt2 (Z_to_bv 64 (e_THIS E)) xs1 xa0 xa1 xa2 (Z_to_bv 64 (e_off E (k s))) xa4 (Z_to_bv 64 (e_BUF E + p)) xa6 xa7 xs2 xs3 (Z_to_bv 64 (e_BUF E)) xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 (B bs p)) xt4 xt5 xt6 F fc m1).

  Definition numo_frac_k (Q : machine_state -> Prop) (s : st) (neg : Z) (Wv : Z) (p : Z) : Prop :=
    forall xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa4 xa6 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 j0 j8 j16 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) (OSL neg s Wv j0 j8 j16 j72) (scopes s) fc m1 ->
      evt psegs Q (S2R E 0x49e50 xra xt0 xt1 xt2 (Z_to_bv 64 (e_THIS E)) xs1 xa0 xa1 xa2 (Z_to_bv 64 (e_off E (k s))) xa4 (Z_to_bv 64 (e_BUF E + p)) xa6 xa7 xs2 xs3 (Z_to_bv 64 (e_BUF E)) xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).

  Definition numo_flt_k (Q : machine_state -> Prop) (s : st) (neg : Z) (Wv : Z) (c : Z) : Prop :=
    forall xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa4 xa5 xa6 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt4 xt5 xt6 j0 j8 j16 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) (OSL neg s Wv j0 j8 j16 j72) (scopes s) fc m1 ->
      evt psegs Q (S2R E 0x4a300 xra xt0 xt1 xt2 (Z_to_bv 64 (e_THIS E)) xs1 xa0 xa1 xa2 (Z_to_bv 64 (e_off E (k s))) xa4 xa5 xa6 xa7 xs2 xs3 (Z_to_bv 64 (e_BUF E)) xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 (c)) xt4 xt5 xt6 F fc m1).

  Definition numo_int_k (Q : machine_state -> Prop) (s : st) (neg : Z) (Wv : Z) (p : Z) : Prop :=
    forall xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa6 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 j0 j8 j16 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) (OSL neg s Wv j0 j8 j16 j72) (scopes s) fc m1 ->
      evt psegs Q (S2R E 0x4a574 xra xt0 xt1 xt2 (Z_to_bv 64 (e_THIS E)) xs1 xa0 xa1 xa2 xa3 xa4 (Z_to_bv 64 (e_BUF E + p)) xa6 xa7 xs2 xs3 (Z_to_bv 64 (e_BUF E)) xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).

  Definition numo_e48_k (Q : machine_state -> Prop) (s : st) (neg : Z) (Wv : Z) (q0 : Z) : Prop :=
    forall xra xt1 xt2 xs1 xa0 xa1 xa2 xa4 xa5 xa6 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 j0 j8 j16 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) (OSL neg s Wv j0 j8 j16 j72) (scopes s) fc m1 ->
      evt psegs Q (S2R E 0x4a290 xra (Z_to_bv 64 (B bs q0)) xt1 xt2 (Z_to_bv 64 (e_THIS E)) xs1 xa0 xa1 xa2 (Z_to_bv 64 (e_off E (k s))) xa4 xa5 xa6 (Z_to_bv 64 (e_BUF E + q0)) xs2 xs3 (Z_to_bv 64 (e_BUF E)) xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).

  Definition numo_e98_k (Q : machine_state -> Prop) (s : st) (neg : Z) (Wv : Z) (c : Z) : Prop :=
    forall xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa4 xa5 xa6 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt4 xt5 xt6 j0 j8 j16 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) (OSL neg s Wv j0 j8 j16 j72) (scopes s) fc m1 ->
      evt psegs Q (S2R E 0x4a2e0 xra xt0 xt1 xt2 (Z_to_bv 64 (e_THIS E)) xs1 xa0 xa1 xa2 (Z_to_bv 64 (e_off E (k s))) xa4 xa5 xa6 xa7 xs2 xs3 (Z_to_bv 64 (e_BUF E)) xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 (c)) xt4 xt5 xt6 F fc m1).

  Definition numo_join_k (Q : machine_state -> Prop) (s : st) (neg : Z) (Wv : Z)  : Prop :=
    forall xra xt0 xt1 xt2 xs1 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 j0 j8 j16 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) (OSL neg s Wv j0 j8 j16 j72) (scopes s) fc m1 ->
      evt psegs Q (S2R E 0x4a7d0 xra xt0 xt1 xt2 (Z_to_bv 64 (e_THIS E)) xs1 (Z_to_bv 64 (1)) xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 (Z_to_bv 64 (e_BUF E)) xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).

  Definition numo_wr_k (Q : machine_state -> Prop) (s : st) (neg : Z) (Wv : Z) : Prop :=
    forall a0v xra xt0 xt1 xt2 xs1 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 j0 j8 j16 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      (a0v = 0 \/ a0v = 9)%Z ->
      MEMI E (e_nxt0 E) (OSL neg s Wv j0 j8 j16 j72) (scopes s) fc m1 ->
      evt psegs Q (S2R E 0x4a6c0 xra xt0 xt1 xt2 (Z_to_bv 64 (e_THIS E)) xs1 (Z_to_bv 64 a0v) xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 (Z_to_bv 64 (e_BUF E)) xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).

  Definition numo_cmp_k (Q : machine_state -> Prop) (s : st) (neg : Z) (Wv : Z) (e : Z) : Prop :=
    forall xra xt0 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 j0 j8 j16 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) (OSL neg s Wv j0 j8 j16 j72) (scopes s) fc m1 ->
      evt psegs Q (S2R E 0x4a3e8 xra xt0 (Z_to_bv 64 (e)) xt2 (Z_to_bv 64 (e_THIS E)) xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 (Z_to_bv 64 (e_BUF E)) xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).

  Definition numo_tail_k (Q : machine_state -> Prop) (s : st) (neg : Z) (Wv : Z) (pc : Z) : Prop :=
    forall xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 j0 j8 j16 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) (OSL neg s Wv j0 j8 j16 j72) (scopes s) fc m1 ->
      evt psegs Q (S2R E pc xra xt0 xt1 xt2 (Z_to_bv 64 (e_THIS E)) xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 (Z_to_bv 64 (e_BUF E)) xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).

  Definition numo_ftail_k (Q : machine_state -> Prop) (s : st) (neg : Z) (Wv : Z) (p d r : Z) : Prop :=
    forall xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa4 xa6 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt5 v0 v8 v16 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) (OFSL v0 v8 v16 neg s Wv j72) (scopes s) fc m1 ->
      evt psegs Q (S2R E 0x49ffc xra xt0 xt1 xt2 (Z_to_bv 64 (e_THIS E)) xs1 xa0 xa1 xa2 (Z_to_bv 64 (e_off E (k s))) xa4 (Z_to_bv 64 (e_BUF E + p)) xa6 xa7 xs2 xs3 (Z_to_bv 64 (e_BUF E)) xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 (Z_to_bv 64 (d)) xt5 (Z_to_bv 64 (V8 (B bs r) (B bs (r + 1)) (B bs (r + 2)) (B bs (r + 3)) (B bs (r + 4)) (B bs (r + 5)) (B bs (r + 6)) (B bs (r + 7)))) F fc m1).

  Definition numo_fdig_k (Q : machine_state -> Prop) (s : st) (neg : Z) (Wv : Z) (p d : Z) : Prop :=
    forall xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa4 xa6 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt5 xt6 v0 v8 v16 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) (OFSL v0 v8 v16 neg s Wv j72) (scopes s) fc m1 ->
      evt psegs Q (S2R E 0x4a068 xra xt0 xt1 xt2 (Z_to_bv 64 (e_THIS E)) xs1 xa0 xa1 xa2 (Z_to_bv 64 (e_off E (k s))) xa4 (Z_to_bv 64 (e_BUF E + p)) xa6 xa7 xs2 xs3 (Z_to_bv 64 (e_BUF E)) xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 (Z_to_bv 64 (d)) xt5 xt6 F fc m1).
End NumODefs.
