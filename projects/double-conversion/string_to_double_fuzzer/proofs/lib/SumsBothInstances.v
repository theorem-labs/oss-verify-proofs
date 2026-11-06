(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import SumsLib Sums_code Sums2_code AsanIMemset AsanIMemcpy AsanMemIsZero AsanIStrncpy.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section FPW_1. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition both_imemset_entry : word := 0x87b8c.

Lemma both_imemset_code :
  code_at ImgB.M.loaded_segments both_imemset_entry 0 imemset_words.
Proof. unfold imemset_words. code_at_vm. Qed.

Theorem both_imemset : forall mem0 (s c : word) n rom regs (ret : word),
  (0 <= n)%Z -> (bv_unsigned s + n < 2 ^ 64)%Z ->
  store_ok ImgB.M.loaded_segments mem0 s (Z.to_nat n) = true ->
  (align15 n s = 0%Z -> n <> 0%Z -> (bv_unsigned c < 256)%Z) ->
  ret_ok ret -> getr regs 1 = ret ->
  getr regs 10 = s -> getr regs 11 = c -> getr regs 12 = Z_to_bv 64 n ->
  exists regs',
    msteps ImgB.M.loaded_segments
           (mkst regs both_imemset_entry mem0 rom)
           (mkst regs' ret (wbytes mem0 s (repeat (Z_to_bv 8 (bv_unsigned c)) (Z.to_nat n))) rom)
    /\ regs_agree (fun r => In r imemset_clob) regs regs'.
Proof.
  intros mem0 s c n rom regs ret Hn Hnw Hok HC256.
  rewrite <- (at_0 both_imemset_entry).
  apply (imemset_run _ _ mem0 s c n rom both_imemset_code Hn Hnw Hok HC256).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition both_imemcpy_entry : word := 0x87b10.

Lemma both_imemcpy_code :
  code_at ImgB.M.loaded_segments both_imemcpy_entry 0 imemcpy_words.
Proof. unfold imemcpy_words. code_at_vm. Qed.

Theorem both_imemcpy : forall mem0 (dst src : word) n bs rom regs (ret : word),
  cpyH ImgB.M.loaded_segments mem0 dst src n bs ->
  ret_ok ret -> getr regs 1 = ret ->
  getr regs 10 = dst -> getr regs 11 = src -> getr regs 12 = Z_to_bv 64 n ->
  exists regs',
    msteps ImgB.M.loaded_segments
           (mkst regs both_imemcpy_entry mem0 rom) (mkst regs' ret (wbytes mem0 dst bs) rom)
    /\ regs_agree (fun r => In r imemcpy_clob) regs regs'.
Proof.
  intros mem0 dst src n bs rom regs ret HOK.
  rewrite <- (at_0 both_imemcpy_entry).
  apply (imemcpy_run _ _ mem0 dst src n bs rom both_imemcpy_code HOK).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition both_mem_is_zero_entry : word := 0x880d8.

Lemma both_mem_is_zero_code :
  code_at ImgB.M.loaded_segments both_mem_is_zero_entry 0 memisz_words.
Proof. unfold memisz_words. code_at_vm. Qed.

Theorem both_mem_is_zero : forall mem (beg sp : word) N rom regs (ret : word),
  (0 <= N <= 2 ^ 40)%Z ->
  (bv_unsigned beg + N + 8 <= 2 ^ 64)%Z ->
  (16 <= bv_unsigned sp)%Z ->
  store_ok ImgB.M.loaded_segments mem (Z_to_bv 64 (bv_unsigned sp - 8)) 8 = true ->
  (bv_unsigned beg + N <= bv_unsigned sp - 8 \/ bv_unsigned sp <= bv_unsigned beg)%Z ->
  (forall a : word, (bv_unsigned beg <= bv_unsigned a < bv_unsigned beg + N)%Z ->
     rdn ImgB.M.loaded_segments mem a 1 = Some [Z_to_bv 8 0]) ->
  ret_ok ret -> getr regs 1 = ret -> getr regs 2 = sp ->
  getr regs 10 = beg -> getr regs 11 = Z_to_bv 64 N ->
  exists regs',
    msteps ImgB.M.loaded_segments
           (mkst regs both_mem_is_zero_entry mem rom)
           (mkst regs' ret (wbytes mem (Z_to_bv 64 (bv_unsigned sp - 8)) (word_to_le_bytes 8 ret)) rom)
    /\ regs_agree (fun r => In r memisz_clob) regs regs'
    /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 2 = sp /\ getr regs' 1 = ret.
Proof.
  intros mem beg sp N rom regs ret.
  apply (mem_is_zero_summary _ _ mem beg sp N rom regs ret both_mem_is_zero_code).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition both_istrncpy_entry : word := 0x87fb8.
Definition both_sealed_src : Z := 0x11b36.

Lemma both_istrncpy_code :
  code_at ImgB.M.loaded_segments both_istrncpy_entry 0 istrncpy_words.
Proof. unfold istrncpy_words. code_at_vm. Qed.

(* [comment removed for export] *)
Lemma both_sealed_src_img : forall mem,
  (forall i, (both_sealed_src <= i < both_sealed_src + 9)%Z -> mem (Z_to_bv 64 i) = None) ->
  rdn ImgB.M.loaded_segments mem (Z_to_bv 64 both_sealed_src) 8 = Some sealed8
  /\ rdn ImgB.M.loaded_segments mem (at_ (Z_to_bv 64 both_sealed_src) 8) 1 = Some [Z_to_bv 8 0].
Proof.
  intros mem Hnone. unfold both_sealed_src in *. split.
  - rewrite (rdn_ext _ 8 mem (fun _ => None)); [vm_compute; reflexivity | u_norm; cbn; lia |].
    intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply Hnone. revert Hx. u_norm. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
  - rewrite (rdn_ext _ 1 mem (fun _ => None)); [vm_compute; reflexivity | rewrite at_u by (u_norm; lia); u_norm; cbn; lia |].
    intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply Hnone. revert Hx. rewrite at_u by (u_norm; lia). u_norm. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
Qed.

Theorem both_istrncpy_sealed : forall mem0 (dst : word) rom regs (ret : word),
  (forall i, (both_sealed_src <= i < both_sealed_src + 9)%Z -> mem0 (Z_to_bv 64 i) = None) ->
  store_ok ImgB.M.loaded_segments mem0 dst 4095%nat = true ->
  (bv_unsigned dst + 4095 < 2 ^ 64)%Z ->
  (bv_unsigned dst + 4095 <= both_sealed_src \/ both_sealed_src + 9 <= bv_unsigned dst)%Z ->
  ret_ok ret -> getr regs 1 = ret ->
  getr regs 10 = dst -> getr regs 11 = Z_to_bv 64 both_sealed_src -> getr regs 12 = Z_to_bv 64 4095 ->
  exists regs',
    msteps ImgB.M.loaded_segments
           (mkst regs both_istrncpy_entry mem0 rom) (mkst regs' ret (wbytes mem0 dst strncpy_sealed_bytes) rom)
    /\ regs_agree (fun r => In r istrncpy_clob) regs regs'.
Proof.
  intros mem0 dst rom regs ret Hnone Hok Hnw Hdisj Hret H1 H10 H11 H12.
  destruct (both_sealed_src_img mem0 Hnone) as [Hs Hn].
  rewrite <- (at_0 both_istrncpy_entry).
  apply (istrncpy_run _ _ mem0 dst (Z_to_bv 64 both_sealed_src) rom both_istrncpy_code Hs Hn); try assumption;
    unfold both_sealed_src in *; u_norm; lia.
Qed.

End FPW_1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
