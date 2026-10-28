(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YM06 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d YO0e.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 YI06 UI5b YI09 YI08 YI0r
UI1w UI21 UI20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI14 YI13 UI5c.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma mem_grows_of_eq : forall (m1 m2 : word -> option byte), (forall x, m2 x = m1 x) -> mem_grows m1 m2.
Proof using. intros m1 m2 Heq x Hx. rewrite Heq. exact Hx. Qed.
Lemma mbyte_of_eq : forall segs (m1 m2 : word -> option byte) a, (forall x, m2 x = m1 x) -> mbyte segs m2 a = mbyte segs m1 a.
Proof using. intros segs m1 m2 a Heq. unfold mbyte. rewrite Heq. reflexivity. Qed.
Definition CMP_CLOB : list reg := [5; 6; 10; 11; 12; 13; 14; 15; 16; 17]%bv.
Lemma cmp_clob_out : forall r : reg, reg_in r CMP_CLOB = false ->
r <> 5%bv /\ r <> 6%bv /\ r <> 10%bv /\ r <> 11%bv /\ r <> 12%bv /\ r <> 13%bv /\ r <> 14%bv /\ r <> 15%bv /\ r <> 16%bv /\ r <> 17%bv.
Proof using. intros r Hr. repeat split; intros ->; vm_compute in Hr; discriminate. Qed.
Definition BCMP_CLOB : list reg := [10; 11; 12; 13; 14]%bv.
Lemma LAY_Frame_split : LAY_Frame = LAY_FrameConfig ++ [(32, 1%N); (33, 1%N)].
Proof using. reflexivity. Qed.
Lemma cgif_fp_in : forall g s N b n a,
In (b, n) (cgif_blocks g s N) -> b <= a < b + n -> inFP (blocks_fp (cgif_blocks g s N)) a.
Proof using. intros g s N b n a Hin Ha. apply inFP_blocks_fp. exists b, n. auto. Qed.
End c.
