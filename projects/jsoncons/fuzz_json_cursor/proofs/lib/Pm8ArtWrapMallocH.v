(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac AsanAcct HeapIface HeapIfaceA As0StepLib ArtMem ArtTac.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import Pm8_code_80000_81000.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
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
Lemma art_malloc_thunk : forall regs (M rom : word -> option byte), msteps ASEGS (mkst regs (0x809f8 : word) M rom) (mkst regs (0x80bd4 : word) M rom).
Proof. intros regs M rom. stepj F_809a8 D_809a8. apply mst_refl. Qed.
End FPX.

Lemma art_byte_unrestrict : forall H (M : word -> option byte) a v, byte_at (mrestrict H M) a v -> byte_at M a v.
Proof. intros H M a v B. unfold byte_at, mrestrict in *. destruct (H (Z_to_bv 64 a)); [discriminate B|exact B]. Qed.

