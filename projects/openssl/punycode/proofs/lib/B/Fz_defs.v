(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.openssl.punycode.lib.Lib Require Import Tac ImageA.
From OSSVerify.Proofs.openssl.punycode.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.punycode.lib.B Require Import Layout RT_iface D_libiface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition e_fz : Z := 0x1edff0.              (* [comment removed for export] *)
Definition e_cmalloc : Z := 0x1ee344.         (* [comment removed for export] *)
Definition e_czalloc : Z := 0x1ee410.         (* [comment removed for export] *)
Definition e_cfree : Z := 0x1ee868.           (* [comment removed for export] *)
Definition e_decode : Z := 0x430dbc.          (* [comment removed for export] *)
Definition e_a2u : Z := 0x4312f4.             (* [comment removed for export] *)
Definition e_wp_init : Z := 0x272528.         (* [comment removed for export] *)
Definition e_wp_cleanup : Z := 0x273e1c.      (* [comment removed for export] *)
Definition e_stack_malloc_6 : Z := 0x1a1e00.
Definition e_stack_free_6 : Z := 0x1a1f9c.

(* [comment removed for export] *)
Definition G_MALLOC_IMPL : Z := 0x5e68c0.
Definition G_FREE_IMPL : Z := 0x5e6900.
Definition G_LATCH : Z := 0xbd6100.
Definition LIB_A (m : mem) : Prop :=
  ro_cells bsegs m G_MALLOC_IMPL [C8 (Z_to_bv 64 e_cmalloc)]
  /\ ro_cells bsegs m G_FREE_IMPL [C8 (Z_to_bv 64 e_cfree)]
  /\ (exists v, rw_cells bsegs m G_LATCH [C1 v]).

(* [comment removed for export] *)
Lemma land_m32 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551584 = 32 * (x / 32).
Proof.
  intros x Hx. change 18446744073709551584 with (Z.ldiff (Z.ones 64) (Z.ones 5)).
  rewrite Z.ldiff_land, Z.land_assoc, Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
  change (2^5) with 32. lia.
Qed.
Lemma land_m32_al : forall x, 0 <= x < 2^64 -> x mod 32 = 0 -> Z.land x 18446744073709551584 = x.
Proof. intros x Hx H. rewrite land_m32 by lia. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
Definition fz_frame (s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
  [C8 (Z_to_bv 64 0); C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
