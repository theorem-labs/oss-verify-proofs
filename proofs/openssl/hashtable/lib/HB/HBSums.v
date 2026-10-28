(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.openssl.hashtable.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import PropExec CatExec CatSim SeqExec StoreOk AsanPopFree.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import SumsLib RtSumsCode RtIMemset RtIMemcpy RtMemIsZero RtIStrncpy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

#[local] Notation HASEGS0 := AsanUbsan.M.loaded_segments (only parsing).

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ha_imemset_entry : word := 0x1d0470.

Lemma ha_imemset_code :
  code_at AsanUbsan.M.loaded_segments ha_imemset_entry 0 imemset_words.
Proof. unfold imemset_words. code_at_vm. Qed.

Theorem ha_imemset : forall mem0 (s c : word) n rom regs (ret : word),
  (0 <= n)%Z -> (bv_unsigned s + n < 2 ^ 64)%Z ->
  store_ok AsanUbsan.M.loaded_segments mem0 s (Z.to_nat n) = true ->
  (align15 n s = 0%Z -> n <> 0%Z -> (bv_unsigned c < 256)%Z) ->
  ret_ok ret -> getr regs 1 = ret ->
  getr regs 10 = s -> getr regs 11 = c -> getr regs 12 = Z_to_bv 64 n ->
  exists regs',
    msteps AsanUbsan.M.loaded_segments
           (mkst regs ha_imemset_entry mem0 rom)
           (mkst regs' ret (wbytes mem0 s (repeat (Z_to_bv 8 (bv_unsigned c)) (Z.to_nat n))) rom)
    /\ regs_agree (fun r => In r imemset_clob) regs regs'.
Proof.
  intros mem0 s c n rom regs ret Hn Hnw Hok HC256.
  rewrite <- (at_0 ha_imemset_entry).
  apply (imemset_run _ _ mem0 s c n rom ha_imemset_code Hn Hnw Hok HC256).
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ha_imemcpy_entry : word := 0x1d03f4.

Lemma ha_imemcpy_code :
  code_at AsanUbsan.M.loaded_segments ha_imemcpy_entry 0 imemcpy_words.
Proof. unfold imemcpy_words. code_at_vm. Qed.

Theorem ha_imemcpy : forall mem0 (dst src : word) n bs rom regs (ret : word),
  cpyH AsanUbsan.M.loaded_segments mem0 dst src n bs ->
  ret_ok ret -> getr regs 1 = ret ->
  getr regs 10 = dst -> getr regs 11 = src -> getr regs 12 = Z_to_bv 64 n ->
  exists regs',
    msteps AsanUbsan.M.loaded_segments
           (mkst regs ha_imemcpy_entry mem0 rom) (mkst regs' ret (wbytes mem0 dst bs) rom)
    /\ regs_agree (fun r => In r imemcpy_clob) regs regs'.
Proof.
  intros mem0 dst src n bs rom regs ret HOK.
  rewrite <- (at_0 ha_imemcpy_entry).
  apply (imemcpy_run _ _ mem0 dst src n bs rom ha_imemcpy_code HOK).
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ha_mem_is_zero_entry : word := 0x1d09a0.

Lemma ha_mem_is_zero_code :
  code_at AsanUbsan.M.loaded_segments ha_mem_is_zero_entry 0 memisz_words.
Proof. unfold memisz_words. code_at_vm. Qed.

Theorem ha_mem_is_zero : forall mem (beg sp : word) N rom regs (ret : word),
  (0 <= N <= 2 ^ 40)%Z ->
  (bv_unsigned beg + N + 8 <= 2 ^ 64)%Z ->
  (16 <= bv_unsigned sp)%Z ->
  store_ok AsanUbsan.M.loaded_segments mem (Z_to_bv 64 (bv_unsigned sp - 8)) 8 = true ->
  (bv_unsigned beg + N <= bv_unsigned sp - 8 \/ bv_unsigned sp <= bv_unsigned beg)%Z ->
  (forall a : word, (bv_unsigned beg <= bv_unsigned a < bv_unsigned beg + N)%Z ->
     rdn AsanUbsan.M.loaded_segments mem a 1 = Some [Z_to_bv 8 0]) ->
  ret_ok ret -> getr regs 1 = ret -> getr regs 2 = sp ->
  getr regs 10 = beg -> getr regs 11 = Z_to_bv 64 N ->
  exists regs',
    msteps AsanUbsan.M.loaded_segments
           (mkst regs ha_mem_is_zero_entry mem rom)
           (mkst regs' ret (wbytes mem (Z_to_bv 64 (bv_unsigned sp - 8)) (word_to_le_bytes 8 ret)) rom)
    /\ regs_agree (fun r => In r memisz_clob) regs regs'
    /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 2 = sp /\ getr regs' 1 = ret.
Proof.
  intros mem beg sp N rom regs ret.
  apply (mem_is_zero_summary _ _ mem beg sp N rom regs ret ha_mem_is_zero_code).
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ha_istrncpy_entry : word := 0x1d089c.
Definition ha_sealed_src : Z := 0x1410c.

Lemma ha_istrncpy_code :
  code_at AsanUbsan.M.loaded_segments ha_istrncpy_entry 0 istrncpy_words.
Proof. unfold istrncpy_words. code_at_vm. Qed.

(* [comment removed for export] *)
Lemma ha_sealed_src_img : forall mem,
  (forall i, (ha_sealed_src <= i < ha_sealed_src + 9)%Z -> mem (Z_to_bv 64 i) = None) ->
  rdn AsanUbsan.M.loaded_segments mem (Z_to_bv 64 ha_sealed_src) 8 = Some sealed8
  /\ rdn AsanUbsan.M.loaded_segments mem (at_ (Z_to_bv 64 ha_sealed_src) 8) 1 = Some [Z_to_bv 8 0].
Proof.
  intros mem Hnone. unfold ha_sealed_src in *. split.
  - rewrite (rdn_ext _ 8 mem (fun _ => None)); [vm_compute; reflexivity | u_norm; cbn; lia |].
    intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply Hnone. revert Hx. u_norm. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
  - rewrite (rdn_ext _ 1 mem (fun _ => None)); [vm_compute; reflexivity | rewrite at_u by (u_norm; lia); u_norm; cbn; lia |].
    intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply Hnone. revert Hx. rewrite at_u by (u_norm; lia). u_norm. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
Qed.

Theorem ha_istrncpy_sealed : forall mem0 (dst : word) rom regs (ret : word),
  (forall i, (ha_sealed_src <= i < ha_sealed_src + 9)%Z -> mem0 (Z_to_bv 64 i) = None) ->
  store_ok AsanUbsan.M.loaded_segments mem0 dst 4095%nat = true ->
  (bv_unsigned dst + 4095 < 2 ^ 64)%Z ->
  (bv_unsigned dst + 4095 <= ha_sealed_src \/ ha_sealed_src + 9 <= bv_unsigned dst)%Z ->
  ret_ok ret -> getr regs 1 = ret ->
  getr regs 10 = dst -> getr regs 11 = Z_to_bv 64 ha_sealed_src -> getr regs 12 = Z_to_bv 64 4095 ->
  exists regs',
    msteps AsanUbsan.M.loaded_segments
           (mkst regs ha_istrncpy_entry mem0 rom) (mkst regs' ret (wbytes mem0 dst strncpy_sealed_bytes) rom)
    /\ regs_agree (fun r => In r istrncpy_clob) regs regs'.
Proof.
  intros mem0 dst rom regs ret Hnone Hok Hnw Hdisj Hret H1 H10 H11 H12.
  destruct (ha_sealed_src_img mem0 Hnone) as [Hs Hn].
  rewrite <- (at_0 ha_istrncpy_entry).
  apply (istrncpy_run _ _ mem0 dst (Z_to_bv 64 ha_sealed_src) rom ha_istrncpy_code Hs Hn); try assumption;
    unfold ha_sealed_src in *; u_norm; lia.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ha_popfree_head : Z := 0x19b7c4.


Lemma PF0 : fetch_word HASEGS0 (Z_to_bv 64 ha_popfree_head) = Some PW0. Proof. vm_refl. Qed.
Lemma PF1 : fetch_word HASEGS0 (Z_to_bv 64 (ha_popfree_head + 4)) = Some PW1. Proof. vm_refl. Qed.
Lemma PF2 : fetch_word HASEGS0 (Z_to_bv 64 (ha_popfree_head + 8)) = Some PW2. Proof. vm_refl. Qed.
Lemma PF3 : fetch_word HASEGS0 (Z_to_bv 64 (ha_popfree_head + 12)) = Some PW3. Proof. vm_refl. Qed.
Lemma PF4 : fetch_word HASEGS0 (Z_to_bv 64 (ha_popfree_head + 16)) = Some PW4. Proof. vm_refl. Qed.
Lemma PF5 : fetch_word HASEGS0 (Z_to_bv 64 (ha_popfree_head + 20)) = Some PW5. Proof. vm_refl. Qed.
Lemma PF6 : fetch_word HASEGS0 (Z_to_bv 64 (ha_popfree_head + 24)) = Some PW6. Proof. vm_refl. Qed.
Lemma PF7 : fetch_word HASEGS0 (Z_to_bv 64 (ha_popfree_head + 28)) = Some PW7. Proof. vm_refl. Qed.

Theorem ha_popfree_spec : popfree_spec AsanUbsan.M.loaded_segments ha_popfree_head.
Proof.
  apply popfree_spec_of_code; [unfold ha_popfree_head; lia | exact PF0 | exact PF1 | exact PF2 | exact PF3 | exact PF4 | exact PF5 | exact PF6 | exact PF7].
Qed.

(* [comment removed for export] *)
Theorem ha_popfree_loop_run : forall regs mem rom i e c s n,
  getr regs 10 = Z_to_bv 64 i -> getr regs 11 = Z_to_bv 64 e -> getr regs 12 = Z_to_bv 64 c ->
  getr regs 21 = Z_to_bv 64 s -> getr regs 19 = Z_to_bv 64 n ->
  (0 <= i)%Z -> (i < n)%Z -> (4 * n <= e)%Z -> (e < 2 ^ 64)%Z ->
  (0 <= c)%Z -> (0 <= s)%Z -> (c + (n - i) * s < 2 ^ 64)%Z ->
  (forall d (m : nat), (0 <= d)%Z -> (d + Z.of_nat m <= 4 * (n - i))%Z ->
     RiscvSemantics.store_ok HASEGS0 mem (Z_to_bv 64 (e - 4 * n + d)) m = true) ->
  exists regs',
    msteps HASEGS0 (mkst regs (Z_to_bv 64 ha_popfree_head) mem rom)
                (mkst regs' (Z_to_bv 64 (ha_popfree_head + 32)) (pf_mem mem e c s i (Z.to_nat (n - i))) rom)
    /\ getr regs' 10 = Z_to_bv 64 n /\ getr regs' 11 = Z_to_bv 64 e
    /\ getr regs' 12 = Z_to_bv 64 (c + (n - i) * s)
    /\ getr regs' 21 = Z_to_bv 64 s /\ getr regs' 19 = Z_to_bv 64 n
    /\ getr regs' 14 = Z_to_bv 64 ((c + (n - i - 1) * s) / 16) /\ getr regs' 15 = Z_to_bv 64 (e - 4 * n)
    /\ (forall r : reg, r <> 10 -> r <> 12 -> r <> 14 -> r <> 15 -> getr regs' r = getr regs r).
Proof.
  apply (popfree_loop_run HASEGS0 ha_popfree_head); [unfold ha_popfree_head; lia | exact PF0 | exact PF1 | exact PF2 | exact PF3 | exact PF4 | exact PF5 | exact PF6 | exact PF7].
Qed.
