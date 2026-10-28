(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac AsanAcct HeapIface HeapIfaceA HeapIfaceABx As0StepLib ArtMem ArtTac.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0_code_r5fac4_60344_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Lemma art_S_pred : forall y, HeapIfaceA.S y - 1 <= HeapIfaceA.S (y - 1).
Proof.
  intros y. unfold HeapIfaceA.S. pose proof (Z.div_mod y 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound y 8 ltac:(lia)) as R.
  assert (y / 8 - 1 <= (y - 1) / 8); [|lia]. apply Z.div_le_lower_bound; lia.
Qed.

Lemma art_kept_preserved : forall (R R' : bvmap 5 word), getr R' 2 = getr R 2 ->
  (forall r : reg, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr R' r = getr R r) -> regs_preserved R R'.
Proof.
  intros R R' P2 PK r Hr. unfold callee_saved_idx in Hr. rewrite <- (Z_to_bv_bv_unsigned _ r). set (z := bv_unsigned r) in *. cbn [In] in Hr.
  destruct Hr as [<-|Hr]; [exact P2|].
  repeat (destruct Hr as [<-|Hr]; [apply PK; cbn [In]; repeat first [left; apply bv_eq; reflexivity|right]|]). destruct Hr.
Qed.

Section FPX. Context {fx : PropExec.FPState}.
#[using="Type"] Lemma art_malloc_thunk : forall regs (M rom : word -> option byte), msteps ASEGS (mkst regs (0x79818 : word) M rom) (mkst regs (0x799f4 : word) M rom).
Proof. intros regs M rom. stepj F_79400 D_79400. apply mst_refl. Qed.
End FPX.

Lemma art_byte_unrestrict : forall H (M : word -> option byte) a v, byte_at (mrestrict H M) a v -> byte_at M a v.
Proof. intros H M a v B. unfold byte_at, mrestrict in *. destruct (H (Z_to_bv 64 a)); [discriminate B|exact B]. Qed.

