(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prelim Monad MSafe STree Malloc Prog KInv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma PGSZ_eq : PGSZ = 4096. Proof. reflexivity. Qed.
Lemma page_size_eq : page_size = 4096. Proof. reflexivity. Qed.

Lemma land_4095 : forall x, Z.land x 4095 = x mod 4096.
Proof. intros x. change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma round_up_pg_aligned : forall x, x mod 4096 = 0 -> round_up_pg x = x.
Proof.
  intros x Hx. unfold round_up_pg. rewrite PGSZ_eq. change (4096 - 1) with 4095. rewrite land_4095.
  assert ((- x) mod 4096 = 0). { apply Z.mod_opp_l_z; lia. } lia.
Qed.

Lemma round_up_pg_eq : forall x, round_up_pg x = page_round_up_Z x.
Proof.
  intros x. unfold round_up_pg, page_round_up_Z. rewrite PGSZ_eq, page_size_eq. change (4096 - 1) with 4095. rewrite land_4095.
  pose proof (Z.mod_pos_bound (-x) 4096 ltac:(lia)) as H1.
  pose proof (Z_div_mod_eq_full (-x) 4096) as H2.
  pose proof (Z_div_mod_eq_full (x + 4095) 4096) as H3.
  pose proof (Z.mod_pos_bound (x + 4095) 4096 ltac:(lia)) as H4.
  nia.
Qed.

Lemma round_up_pg_ge : forall x, x <= round_up_pg x.
Proof. intros x. unfold round_up_pg. rewrite PGSZ_eq. change (4096 - 1) with 4095. rewrite land_4095. pose proof (Z.mod_pos_bound (-x) 4096 ltac:(lia)). lia. Qed.

Lemma mmap_len_bound : forall len, (0 < len)%Z -> (len <= mmap_len len < len + 4096)%Z.
Proof. intros len H. unfold mmap_len, page_round_up_Z. rewrite page_size_eq. pose proof (Z_div_mod_eq_full (len + 4095) 4096). pose proof (Z.mod_pos_bound (len + 4095) 4096). lia. Qed.
Lemma mmap_len_ge : forall l, 0 < l -> l <= mmap_len l < l + 4096.
Proof. intros. apply mmap_len_bound. assumption. Qed.

Lemma mmap_len_aligned : forall l, (mmap_len l) mod 4096 = 0.
Proof. intros. unfold mmap_len, page_round_up_Z. rewrite page_size_eq. apply Z_mod_mult. Qed.

Lemma mmap_len_of_aligned : forall l, 0 <= l -> l mod 4096 = 0 -> mmap_len l = l.
Proof. intros l Hl Ha. unfold mmap_len, page_round_up_Z. rewrite page_size_eq. pose proof (Z_div_mod_eq_full l 4096). pose proof (Z_div_mod_eq_full (l + 4095) 4096). pose proof (Z.mod_pos_bound (l+4095) 4096). nia. Qed.

Lemma unsigned_wz : forall z, 0 <= z < 2^64 -> bv_unsigned (wz z) = z.
Proof. intros. unfold wz. apply unsigned_lit. assumption. Qed.

Lemma alloc_ceiling_lt : alloc_ceiling < 2^63.
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Lemma alloc_ceiling_Decode : Decode.alloc_ceiling = alloc_ceiling.
Proof. reflexivity. Qed.
