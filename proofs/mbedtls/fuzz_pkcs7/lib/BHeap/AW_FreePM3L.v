(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtS AEvtA AShadow. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import ARt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModelX APop APopGen. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import AVmLib. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Populate AW_Populate2 AW_GetFrom AW_MallocGenLib HMLib HM HMFrame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Ltac2 gd_tbl_AW_FreePM3L () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Init.Datatypes.list"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Populate2.carve_list"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Lists.ListDef.map"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.Lists.List.rev"; "RocqVerifyHarness.AgentSubmission.BHeap.APopGen.newc"].

Section ARUN_1. Context {hAR : arun}.

(* [comment removed for export] *)
#[using="Type"] Lemma sx32_small : forall q, 0 <= q < 2^31 -> sx32 (Z_to_bv 64 q) = Z_to_bv 64 q.
Proof.
  intros q Hq. unfold sx32. rewrite u64_lit by lia. f_equal. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32). rewrite Z.mod_small by lia. lia.
Qed.
Definition toZ (w : word) : Z := bv_unsigned w mod 2^32.
#[using="Type"] Lemma toZ_lit : forall q, 0 <= q < 2^32 -> toZ (Z_to_bv 64 q) = q.
Proof. intros q Hq. unfold toZ. rewrite u64_lit by lia. apply Z.mod_small. lia. Qed.
#[using="Type"] Lemma map_toZ_lits : forall (l : list Z), Forall (fun q => 0 <= q < 2^32) l -> map toZ (map (Z_to_bv 64) l) = l.
Proof. intros l H. induction H as [|q l Hq H IH]; [reflexivity|]. cbn. rewrite toZ_lit, IH by exact Hq. reflexivity. Qed.


(* [comment removed for export] *)
#[using="Type"] Lemma carve_list_newc : ltac2:(CDefT.buildp (gd_tbl_AW_FreePM3L ()) "Pau,$0.Pcs,$0.Pcv,$0.Pnw,$0.P,(1.$0.R4.(2.R3.R2.))P,(3.=R2.)(1.(4.(5.&40.))(6.R6.R5.(7.R3.))(8.$0.(5.&40.)(9.&40.)(:.$0.(;.R5.R4.R3.))))")
(* [comment removed for export] *).
Proof.
  intros au cs cv nw E NW. unfold carve_list, newc. apply nth_error_ext. intros i.
  rewrite !nth_error_map, nth_error_rev, length_map, length_seq, nth_error_seq.
  destruct (Nat.ltb_spec i (Z.to_nat nw)) as [LT|GE]; [| reflexivity].
  rewrite nth_error_map, nth_error_seq.
  destruct (Nat.ltb_spec (Z.to_nat nw - S i) (Z.to_nat nw)) as [LT2|GE2]; [| exfalso; clear - LT GE2; lia].
  cbn [option_map]. f_equal. f_equal. f_equal. subst au.
  replace (Z.of_nat (0 + (Z.to_nat nw - S i))) with (Z.of_nat (Z.to_nat nw) - 1 - Z.of_nat (0 + i)) by (clear - LT; lia). ring.
Qed.

(* [comment removed for export] *)
End ARUN_1.
