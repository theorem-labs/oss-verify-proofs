(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08 YI0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI5w YI5z.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0x YC4a YC80 YC1f YC1g YC1h YC81 YC4b YC20 YC44 YC45.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACjr ACj1 ACj0 ACja.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACj1 ACj0 ACja ACj6.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08 YI0f.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC7x.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACi0.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YI0e.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Lemma U_wtest : forall E ba fa, ew E 653 = Z_to_bv 64 ba -> ew E 52 = Z_to_bv 64 fa -> 0 <= ba < 2 ^ 32 -> 0 <= fa < 2 ^ 32 ->
U E (SAlu ALU_OR (SAlu ALU_AND (SAlu ALU_OR (SOff 653 0) (SOff 52 0)) (SLit 4)) (SAlu ALU_AND (SOff 52 0) (SLit 1)))
= Z.lor (Z.land (Z.lor ba fa) 4) (Z.land fa 1).
Proof.
intros E ba fa E653 E52 Rb Rf.
assert (UO : U E (SAlu ALU_OR (SOff 653 0) (SOff 52 0)) = Z.lor ba fa).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 653 ba E653), (U_atom E 52 fa E52) by lia.
apply zcanon_id. rewrite M64_val. pose proof (Z.add_lor_land ba fa) as AL. pose proof (Z.land_nonneg ba fa) as LN. pose proof (Z.lor_nonneg ba fa) as LO. lia. }
rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_and_lit E _ 4) by lia. rewrite UO. rewrite (U_and_atom E 52 fa 1 E52) by lia.
pose proof (Z.land_nonneg (Z.lor ba fa) 4) as L1. pose proof (Z_land_upper (Z.lor ba fa) 4 ltac:(lia)) as L1'.
pose proof (Z.land_nonneg fa 1) as L2. pose proof (Z_land_upper fa 1 ltac:(lia)) as L2'.
apply zcanon_id. rewrite M64_val.
pose proof (Z.add_lor_land (Z.land (Z.lor ba fa) 4) (Z.land fa 1)) as AL. pose proof (Z.land_nonneg (Z.land (Z.lor ba fa) 4) (Z.land fa 1)) as LN.
pose proof (Z.lor_nonneg (Z.land (Z.lor ba fa) 4) (Z.land fa 1)) as LO. lia.
Qed.
Lemma wtest_zero : forall ba fa, Z.lor (Z.land (Z.lor ba fa) 4) (Z.land fa 1) = 0 -> Z.land ba 4 = 0 /\ Z.land fa 4 = 0 /\ Z.land fa 1 = 0.
Proof.
intros ba fa H. apply Z.lor_eq_0_iff in H. destruct H as [H1 H2]. rewrite Z.land_lor_distr_l in H1. apply Z.lor_eq_0_iff in H1. tauto.
Qed.
Lemma wtest_nonzero : forall ba fa, Z.lor (Z.land (Z.lor ba fa) 4) (Z.land fa 1) <> 0 -> Z.land ba 4 <> 0 \/ Z.land fa 4 <> 0 \/ Z.land fa 1 <> 0.
Proof.
intros ba fa H. destruct (Z.eq_dec (Z.land ba 4) 0) as [E1|]; [|left; assumption]. destruct (Z.eq_dec (Z.land fa 4) 0) as [E2|]; [|right; left; assumption].
destruct (Z.eq_dec (Z.land fa 1) 0) as [E3|]; [|right; right; assumption]. exfalso. apply H.
rewrite Z.land_lor_distr_l, E1, E2, E3. reflexivity.
Qed.
Lemma px_ne_slow_w : forall g cur b, Z.land (YO07.f_attr b) 1 <> 0 \/ Z.land (YO07.f_attr b) 4 <> 0 \/ Z.land (YO07.f_attr cur) 4 <> 0 \/ Z.land (YO07.f_attr cur) 1 <> 0 ->
YO07.px_ne g cur b = YO07.cmp_pixel g cur b.
Proof.
intros g cur b H. apply YI0e.px_ne_slow. unfold YO07.flag.
destruct H as [H | [H | [H | H]]]; rewrite (proj2 (Z.eqb_neq _ _) H); cbn [negb orb]; rewrite ?orb_true_r; reflexivity.
Qed.
Lemma px_ne_fast_w : forall g cur b, Z.land (YO07.f_attr b) 1 = 0 -> Z.land (YO07.f_attr b) 4 = 0 -> Z.land (YO07.f_attr cur) 4 = 0 -> Z.land (YO07.f_attr cur) 1 = 0 ->
YO07.px_ne g cur b = (fun c q : Z => negb (c =? q)).
Proof.
intros g cur b H1 H2 H3 H4. apply YI0e.px_ne_fast; unfold YO07.flag; [rewrite H1 | rewrite H4 | rewrite H2 | rewrite H3]; reflexivity.
Qed.
