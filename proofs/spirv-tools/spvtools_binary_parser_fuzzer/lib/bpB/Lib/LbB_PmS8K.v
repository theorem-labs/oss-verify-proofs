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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require StrLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_Own LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmU2K LbB_MkStrR LbB_PmLH LbB_PmOL.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition SO_STR : Z := 5936.
Definition OB_STR : nat := 24.

Definition S_STR : list nat := [3; 4; 24; 39; 40; 41; 43; 45]%nat.

Definition RT_S8B : list (reg * expr) :=
  [(1%bv, ELit 990940); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 5936));
   (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880));
   (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].

Lemma w1_b8 : forall x, 0 <= x < 256 -> word_to_le_bytes 1 (Z_to_bv 64 x) = [b8 x].
Proof. intros x Hx. unfold b8. apply StrLib.w1_bytes_small. exact Hx. Qed.

Lemma ev_zext1 : forall E (n : N) x, edenot E (EVar n) = Z_to_bv 64 x -> 0 <= x < 256 ->
  edenot E (EExt false 0 1 (EVar n)) = Z_to_bv 64 x.
Proof. intros E n x He Hx. apply (edenot_zext E n 1 x He); [cbn; lia | lia]. Qed.

Lemma ev_b0_and1 : forall E (n : N) b0, edenot E (EVar n) = Z_to_bv 64 b0 -> 0 <= b0 < 256 ->
  edenot E (EAlu ALU_AND (EExt false 0 1 (EVar n)) (ELit 1)) = Z_to_bv 64 (b0 mod 2).
Proof.
  intros E n b0 He Hb. cbn [edenot]. change (edenot E (EExt false 0 1 (EVar n))) with (edenot E (EExt false 0 1 (EVar n))).
  pose proof (ev_zext1 E n b0 He Hb) as Z1. cbn [edenot] in Z1. rewrite Z1.
  rewrite HLib.w_and by lia. f_equal. change 1 with (Z.ones 1). rewrite Z.land_ones by lia. reflexivity.
Qed.

Lemma ev_b0_srl1 : forall E (n : N) b0, edenot E (EVar n) = Z_to_bv 64 b0 -> 0 <= b0 < 256 ->
  edenot E (EAlu ALU_SRL (EExt false 0 1 (EVar n)) (ELit 1)) = Z_to_bv 64 (b0 / 2).
Proof.
  intros E n b0 He Hb. cbn [edenot]. pose proof (ev_zext1 E n b0 He Hb) as Z1. cbn [edenot] in Z1. rewrite Z1.
  rewrite (w_srlk b0 1) by lia. reflexivity.
Qed.

Lemma ev_mul4 : forall E (n : N) x, edenot E (EVar n) = Z_to_bv 64 x -> 0 <= x < 2 ^ 61 ->
  edenot E (EMd M_MUL (ELit 4) (EVar n)) = Z_to_bv 64 (4 * x).
Proof.
  intros E n x He Hx. cbn [edenot]. change (ev E n) with (edenot E (EVar n)). rewrite He.
  apply HLib.w_mul; lia.
Qed.

Lemma sc_b0_long_ne : forall E (n : N) b0, edenot E (EVar n) = Z_to_bv 64 b0 -> 0 <= b0 < 256 ->
  branch_taken BC_NE (edenot E (EAlu ALU_AND (EExt false 0 1 (EVar n)) (ELit 1))) (edenot E (ELit 0)) = negb (b0 mod 2 =? 0).
Proof.
  intros E n b0 He Hb. rewrite (ev_b0_and1 E n b0 He Hb). change (edenot E (ELit 0)) with (Z_to_bv 64 0).
  apply HLib.br_ne; [pose proof (Z.mod_pos_bound b0 2 ltac:(lia)); lia | lia].
Qed.
Lemma sc_b0_long_eq : forall E (n : N) b0, edenot E (EVar n) = Z_to_bv 64 b0 -> 0 <= b0 < 256 ->
  branch_taken BC_EQ (edenot E (EAlu ALU_AND (EExt false 0 1 (EVar n)) (ELit 1))) (edenot E (ELit 0)) = (b0 mod 2 =? 0).
Proof.
  intros E n b0 He Hb. rewrite (ev_b0_and1 E n b0 He Hb). change (edenot E (ELit 0)) with (Z_to_bv 64 0).
  apply HLib.br_eq; [pose proof (Z.mod_pos_bound b0 2 ltac:(lia)); lia | lia].
Qed.
Lemma sc_len_short : forall E (n r : N) b0 x, edenot E (EVar n) = Z_to_bv 64 b0 -> 0 <= b0 < 256 ->
  edenot E (EVar r) = Z_to_bv 64 x -> 0 <= x < 2 ^ 61 ->
  branch_taken BC_EQ (edenot E (EMd M_MUL (ELit 4) (EVar r))) (edenot E (EAlu ALU_SRL (EExt false 0 1 (EVar n)) (ELit 1))) = (4 * x =? b0 / 2).
Proof.
  intros E n r b0 x He Hb Hr Hx. rewrite (ev_mul4 E r x Hr Hx), (ev_b0_srl1 E n b0 He Hb).
  apply HLib.br_eq; [lia | pose proof (Z.div_pos b0 2 ltac:(lia) ltac:(lia)); pose proof (Z.div_le_upper_bound b0 2 256 ltac:(lia) ltac:(lia)); lia].
Qed.
Lemma sc_op_ne : forall E (n : N) op k, edenot E (EVar n) = Z_to_bv 64 op -> 0 <= op < 2 ^ 64 -> 0 <= k < 2 ^ 64 ->
  branch_taken BC_NE (edenot E (EVar n)) (edenot E (ELit k)) = negb (op =? k).
Proof. intros E n op k He Ho Hk. rewrite He. change (edenot E (ELit k)) with (Z_to_bv 64 k). apply HLib.br_ne; lia. Qed.

Lemma even2_mod : forall len, (2 * len) mod 2 = 0.
Proof. intros len. rewrite Z.mul_comm. apply Z_mod_mult. Qed.
Lemma even2_div : forall len, 2 * len / 2 = len.
Proof. intros len. rewrite Z.mul_comm. apply Z_div_mult. lia. Qed.

Lemma ev_s8_nw : forall E (n : N) b0, edenot E (EVar n) = Z_to_bv 64 b0 -> 0 <= b0 < 256 ->
  edenot E (EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_SRL (EExt false 0 1 (EVar n)) (ELit 1)) (ELit 2)) (ELit 1)) = Z_to_bv 64 (b0 / 2 / 4 + 1).
Proof.
  intros E n b0 He Hb. pose proof (ev_b0_srl1 E n b0 He Hb) as S1. cbn [edenot] in S1 |- *. rewrite S1.
  assert (0 <= b0 / 2 < 128) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite (w_srlk (b0 / 2) 2) by lia. change (2 ^ 2) with 4.
  assert (0 <= b0 / 2 / 4 < 32) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  apply HLib.w_add; lia.
Qed.

Lemma sc_size_ne : forall E (s r : N) sz x, edenot E (EVar s) = Z_to_bv 64 sz -> 0 <= sz < 2 ^ 64 ->
  edenot E (EVar r) = Z_to_bv 64 x -> 0 <= x < 2 ^ 61 ->
  branch_taken BC_NE (edenot E (EVar s)) (edenot E (EMd M_MUL (ELit 4) (EVar r))) = negb (sz =? 4 * x).
Proof. intros E s r sz x Hs Hsz Hr Hx. rewrite (ev_mul4 E r x Hr Hx), Hs. apply HLib.br_ne; lia. Qed.
Lemma sc_size_geu : forall E (s : N) sz k, edenot E (EVar s) = Z_to_bv 64 sz -> 0 <= sz < 2 ^ 64 -> 0 <= k < 2 ^ 64 ->
  branch_taken BC_GEU (edenot E (EVar s)) (edenot E (ELit k)) = negb (sz <? k).
Proof. intros E s sz k Hs Hsz Hk. rewrite Hs. change (edenot E (ELit k)) with (Z_to_bv 64 k). apply HLib.br_geu; lia. Qed.
Lemma ev_s8_nwl : forall E (s : N) sz, edenot E (EVar s) = Z_to_bv 64 sz -> 0 <= sz < 2 ^ 63 ->
  edenot E (EAlu ALU_ADD (EAlu ALU_SRL (EVar s) (ELit 2)) (ELit 1)) = Z_to_bv 64 (sz / 4 + 1).
Proof.
  intros E s sz Hs Hsz. cbn [edenot]. change (ev E s) with (edenot E (EVar s)). rewrite Hs.
  rewrite (w_srlk sz 2) by lia. change (2 ^ 2) with 4.
  assert (0 <= sz / 4 <= sz) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  apply HLib.w_add; lia.
Qed.

Definition RT_S8C : list (reg * expr) :=
  [(2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984));
   (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880));
   (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].

Definition RT_S8D (flag : Z) : list (reg * expr) :=
  [(2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880));
   (21%bv, ELit flag); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_S8D1 : list (reg * expr) := RT_S8D 1.
Definition RT_S8D0 : list (reg * expr) := RT_S8D 0.

Definition RT_S8M : list (reg * expr) :=
  [(2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984));
   (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880));
   (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].

Definition s8b_wins (ff : Z) : list (Z * Z) :=
  [(ff / 8 + 2147450880, ff / 8 + 2147452928); (ff + 116, ff + 120); (ff + 114, ff + 116)].

Definition RT_S8C0 : list (reg * expr) := RT_S8C ++ [(10%bv, ELit 0)].
