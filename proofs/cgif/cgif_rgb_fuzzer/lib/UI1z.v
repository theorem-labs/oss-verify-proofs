(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ00.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 YI00 YI02 YI01 YI03
UI1e UI1i UI1h.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma mem_grows_of_eq : forall (m1 m2 : word -> option byte), (forall x, m2 x = m1 x) -> mem_grows m1 m2.
Proof. intros m1 m2 Heq x Hx. rewrite Heq. exact Hx. Qed.
Lemma mbyte_of_eq : forall segs (m1 m2 : word -> option byte) a, (forall x, m2 x = m1 x) -> mbyte segs m2 a = mbyte segs m1 a.
Proof. intros segs m1 m2 a Heq. unfold mbyte. rewrite Heq. reflexivity. Qed.
Definition CMP_CLOB : list reg := [5; 6; 10; 11; 12; 13; 14; 15; 16; 17]%bv.
Lemma cmp_clob_out : forall r : reg, reg_in r CMP_CLOB = false ->
r <> 5%bv /\ r <> 6%bv /\ r <> 10%bv /\ r <> 11%bv /\ r <> 12%bv /\ r <> 13%bv /\ r <> 14%bv /\ r <> 15%bv /\ r <> 16%bv /\ r <> 17%bv.
Proof. intros r Hr. repeat split; intros ->; vm_compute in Hr; discriminate. Qed.
Definition BCMP_CLOB : list reg := [10; 11; 12; 13; 14]%bv.
Lemma LAY_Frame_split : LAY_Frame = LAY_FrameConfig ++ [(32, 1%N); (33, 1%N)].
Proof. reflexivity. Qed.
Lemma cgif_fp_in : forall g s N b n a,
In (b, n) (cgif_blocks g s N) -> b <= a < b + n -> inFP (blocks_fp (cgif_blocks g s N)) a.
Proof. intros g s N b n a Hin Ha. apply inFP_blocks_fp. exists b, n. auto. Qed.
End c.
