(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prelim STree Malloc KInv.
Import ListNotations.
Open Scope Z_scope.
Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).
Lemma PGSZ_eq : PGSZ = 4096. Proof. reflexivity. Qed.
Lemma page_size_eq : page_size = 4096. Proof. reflexivity. Qed.
Lemma land_4095 : forall x, Z.land x 4095 = x mod 4096.
Proof. intros x. change 4095 with (Z.ones 12). Local Ltac2 Set LiaHints.tbl := fun () => "0010=17209195814.1000001S".
rewrite Z.land_ones by lia. reflexivity. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma round_up_pg_aligned : forall x, x mod 4096 = 0 -> round_up_pg x = x.
Proof.
intros x Hx. unfold round_up_pg. rewrite PGSZ_eq. change (4096 - 1) with 4095. rewrite land_4095.
assert ((- x) mod 4096 = 0). { Local Ltac2 Set LiaHints.tbl := fun () => "0030=10704888369.218926750396.245404618834.3000004005008S2HxSS1H".
apply Z.mod_opp_l_z; lia. } lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma round_up_pg_eq : forall x, round_up_pg x = page_round_up_Z x.
Proof.
intros x. unfold round_up_pg, page_round_up_Z. rewrite PGSZ_eq, page_size_eq. change (4096 - 1) with 4095. rewrite land_4095.
Local Ltac2 Set LiaHints.tbl := fun () => "0020=18928845099.418930165734.1000001002SS".
pose proof (Z.mod_pos_bound (-x) 4096 ltac:(lia)) as H1.
pose proof (Z_div_mod_eq_full (-x) 4096) as H2.
pose proof (Z_div_mod_eq_full (x + 4095) 4096) as H3.
pose proof (Z.mod_pos_bound (x + 4095) 4096 ltac:(lia)) as H4.
nia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma mmap_len_ge : forall l, 0 < l -> l <= mmap_len l < l + 4096.
Proof. intros. apply mmap_len_bound. assumption. Qed.
Lemma mmap_len_aligned : forall l, (mmap_len l) mod 4096 = 0.
Proof. intros. unfold mmap_len, page_round_up_Z. rewrite page_size_eq. apply Z_mod_mult. Qed.
Lemma mmap_len_of_aligned : forall l, 0 <= l -> l mod 4096 = 0 -> mmap_len l = l.
Proof. intros l Hl Ha. unfold mmap_len, page_round_up_Z. rewrite page_size_eq. pose proof (Z_div_mod_eq_full l 4096). pose proof (Z_div_mod_eq_full (l + 4095) 4096). pose proof (Z.mod_pos_bound (l+4095) 4096). nia. Qed.
Lemma alloc_ceiling_lt : alloc_ceiling < 2^63.
Proof. rewrite alloc_ceiling_val. Local Ltac2 Set LiaHints.tbl := fun () => "0010=11124115036.0000001S".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma alloc_top_lt64 : forall h, alloc_top h < 2^64 - 2^23.
Proof. intros h. unfold alloc_top, stack_max_size. pose proof (bv_unsigned_in_range 64 (vm_init_sp h)) as R. unfold bv_modulus in R. cbn in R. Local Ltac2 Set LiaHints.tbl := fun () => "0010=41045437285.2000003S1R".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
