(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_Own LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmHdr LbB_PmCall LbB_PmXp LbB_DiagStmt LbB_PmDS LbB_PmGlue.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition TBL_BM : list (Z * expr) :=
  [(1056, EVar 33); (968, EVar 33); (1040, EVar 33);
   (1048, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 56)) (ELit 3)) (ELit 2147450880));
   (1008, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 48)) (ELit 3)) (ELit 2147450880));
   (1000, EAlu ALU_ADD (EVar 32) (ELit 48))].
Definition BM_INS : list nat := [86; 87]%nat.

Lemma sh0_of_acc8 : forall m a, accessible m a 8 -> sh0 m a.
Proof.
  intros m a (A0 & A1 & AC).
  assert (Hx : a <= a + (7 - a mod 8) < a + 8) by (pose proof (Z.mod_pos_bound a 8 ltac:(lia)); lia).
  destruct (AC _ Hx) as (v & V0 & RD & OK).
  assert (SHE : sh (a + (7 - a mod 8)) = sh a) by (unfold sh; f_equal; Z.div_mod_to_equations; lia).
  destruct OK as [->|OK].
  - apply sh0_of_mrd; [lia|]. rewrite <- SHE. exact RD.
  - exfalso. replace ((a + (7 - a mod 8)) mod 8) with 7 in OK by (Z.div_mod_to_equations; lia). lia.
Qed.

Lemma swrap32_sx32 : forall x, 0 <= x < 2 ^ 32 -> Z_to_bv 64 (bv_swrap 32 x) = Z_to_bv 64 (sx32 x).
Proof.
  intros x Hx. unfold sx32. destruct (Z.ltb_spec x 2147483648) as [L|L]; apply bv_eq; rewrite !Z_to_bv_unsigned;
    unfold bv_swrap, bv_wrap; change (bv_modulus 32) with (2 ^ 32); change (bv_half_modulus 32) with (2 ^ 31);
    change (bv_modulus 64) with (2 ^ 64).
  - rewrite (Z.mod_small (x + 2 ^ 31) (2 ^ 32)) by lia. replace (x + 2 ^ 31 - 2 ^ 31) with x by lia. reflexivity.
  - replace (x + 2 ^ 31) with ((x - 2 ^ 31) + 1 * 2 ^ 32) by lia. rewrite Z_mod_plus_full. rewrite (Z.mod_small (x - 2 ^ 31)) by lia.
    rewrite <- (Z_mod_plus_full (x - 2 ^ 31 - 2 ^ 31) 1 (2 ^ 64)). f_equal. lia.
Qed.

Lemma rdn4_of_mdef : forall m a, mdef m a 4 -> 0 <= a -> a + 4 < 2 ^ 64 ->
  exists bs, PropExec.rdn asegs m (Z_to_bv 64 a) 4 = Some bs /\ length bs = 4%nat.
Proof.
  intros m a MD H0 H1.
  assert (G : forall i, 0 <= i < 4 -> exists b, m (Z_to_bv 64 (a + i)) = Some b).
  { intros i Hi. pose proof (MD i Hi) as D. destruct (m (Z_to_bv 64 (a + i))) as [b|]; [exists b; reflexivity | contradiction]. }
  destruct (G 0 ltac:(lia)) as (b0 & E0). destruct (G 1 ltac:(lia)) as (b1 & E1).
  destruct (G 2 ltac:(lia)) as (b2 & E2). destruct (G 3 ltac:(lia)) as (b3 & E3).
  exists [b0; b1; b2; b3]. split; [| reflexivity].
  rewrite Z.add_0_r in E0. cbn [PropExec.rdn]. rewrite E0.
  rewrite (bv_add1_lit a) by lia. rewrite E1. rewrite (bv_add1_lit (a + 1)) by lia. replace (a + 1 + 1) with (a + 2) by lia. rewrite E2.
  rewrite (bv_add1_lit (a + 2)) by lia. replace (a + 2 + 1) with (a + 3) by lia. rewrite E3. reflexivity.
Qed.

Lemma bytes_le_to_Z_rng : forall bs : list byte, 0 <= bytes_le_to_Z bs < 2 ^ (8 * Z.of_nat (length bs)).
Proof.
  induction bs as [|b bs IH]; cbn [bytes_le_to_Z length].
  - cbn. lia.
  - pose proof (bv_unsigned_in_range 8 b) as Hb. change (bv_modulus 8) with 256 in Hb.
    rewrite BBytes.lor_shiftl8_add by lia. rewrite Nat2Z.inj_succ, Z.mul_succ_r, Z.pow_add_r by lia.
    change (2 ^ 8) with 256. nia.
Qed.

Lemma bytes_le_to_Z_range4 : forall bs : list byte, length bs = 4%nat -> 0 <= bytes_le_to_Z bs < 2 ^ 32.
Proof. intros bs L. pose proof (bytes_le_to_Z_rng bs) as R. rewrite L in R. exact R. Qed.

Lemma hex_flags : forall E e fl, edenot E e = Z_to_bv 64 fl -> (fl = DS_FL0 \/ fl = DS_FLHEX) ->
  edenot E (EAlu ALU_ADD (EAlu ALU_AND (EExt false 0 4 e) (ELit (-75))) (ELit 8)) = Z_to_bv 64 DS_FLHEX.
Proof.
  intros E e fl He Hf. cbn [edenot]. rewrite He. unfold DS_FL0, DS_FLHEX in Hf. destruct Hf as [->| ->]; vm_compute; reflexivity.
Qed.
