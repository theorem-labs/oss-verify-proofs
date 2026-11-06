(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEpW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEpW.
Open Scope Z_scope.

Lemma land56_bits : forall fl, Z.land fl 56 = 0 -> Z.land fl 32 = 0 /\ Z.land fl 16 = 0 /\ Z.land fl 8 = 0.
Proof.
intros fl H. repeat split.
- replace 32 with (Z.land 56 32) by reflexivity. rewrite Z.land_assoc, H. reflexivity.
- replace 16 with (Z.land 56 16) by reflexivity. rewrite Z.land_assoc, H. reflexivity.
- replace 8 with (Z.land 56 8) by reflexivity. rewrite Z.land_assoc, H. reflexivity.
Qed.

Lemma br_and_zero : forall fl k, 0 <= fl < 2^64 -> 0 <= k < 2^64 -> Z.land fl k = 0 ->
branch_taken BC_EQ (alu64 ALU_AND (Z_to_bv 64 fl) (Z_to_bv 64 k)) (Z_to_bv 64 0) = true.
Proof.
intros fl k Hf Hk H. unfold branch_taken. cbn -[Z_to_bv bv_unsigned Z.land].
apply (proj2 (Fs.bv_eqb_eq _ _)). apply bv_eq. rewrite bv_and_unsigned, !unsigned_lit by lia. exact H.
Qed.
Lemma br_and_nonzero : forall fl k, 0 <= fl < 2^64 -> 0 <= k < 2^64 -> Z.land fl k <> 0 ->
branch_taken BC_EQ (alu64 ALU_AND (Z_to_bv 64 fl) (Z_to_bv 64 k)) (Z_to_bv 64 0) = false.
Proof.
intros fl k Hf Hk H. unfold branch_taken. cbn -[Z_to_bv bv_unsigned Z.land].
destruct (bv_eqb _ _) eqn:E; [|reflexivity]. exfalso. apply (proj1 (Fs.bv_eqb_eq _ _)) in E.
apply H. apply (f_equal bv_unsigned) in E. rewrite bv_and_unsigned, !unsigned_lit in E by lia. exact E.
Qed.
Lemma brne_and_zero : forall fl k, 0 <= fl < 2^64 -> 0 <= k < 2^64 -> Z.land fl k = 0 ->
branch_taken BC_NE (alu64 ALU_AND (Z_to_bv 64 fl) (Z_to_bv 64 k)) (Z_to_bv 64 0) = false.
Proof.
intros fl k Hf Hk H. unfold branch_taken. cbn -[Z_to_bv bv_unsigned Z.land].
rewrite (proj2 (Fs.bv_eqb_eq _ _)); [reflexivity|]. apply bv_eq. rewrite bv_and_unsigned, !unsigned_lit by lia. exact H.
Qed.
Lemma brne_and_nonzero : forall fl k, 0 <= fl < 2^64 -> 0 <= k < 2^64 -> Z.land fl k <> 0 ->
branch_taken BC_NE (alu64 ALU_AND (Z_to_bv 64 fl) (Z_to_bv 64 k)) (Z_to_bv 64 0) = true.
Proof.
intros fl k Hf Hk H. unfold branch_taken. cbn -[Z_to_bv bv_unsigned Z.land].
destruct (bv_eqb _ _) eqn:E; [|reflexivity]. exfalso. apply (proj1 (Fs.bv_eqb_eq _ _)) in E.
apply H. apply (f_equal bv_unsigned) in E. rewrite bv_and_unsigned, !unsigned_lit in E by lia. exact E.
Qed.

Lemma abs63_unsigned : forall x : word,
bv_unsigned (alu64 ALU_SRL (alu64 ALU_SLL x (Z_to_bv 64 1)) (Z_to_bv 64 1)) = bv_unsigned x mod 2^63.
Proof.
intros x. pose proof (bv_unsigned_in_range 64 x) as R. unfold bv_modulus in R. cbn in R.
unfold alu64, alu. cbn iota beta.
replace (bv_and (Z_to_bv 64 1) (Z_to_bv 64 63)) with (Z_to_bv 64 1) by (apply bv_eq; vm_compute; reflexivity).
rewrite bv_shiftr_unsigned, bv_shiftl_unsigned, !unsigned_lit by lia. unfold bv_wrap.
replace (bv_modulus 64) with (2^64) by reflexivity.
rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change (2^1) with 2.
Z.div_mod_to_equations. lia.
Qed.
Lemma abs63_ltu : forall (x : word) k, 0 <= k < 2^64 ->
branch_taken BC_LTU (alu64 ALU_SRL (alu64 ALU_SLL x (Z_to_bv 64 1)) (Z_to_bv 64 1)) (Z_to_bv 64 k) = (bv_unsigned x mod 2^63 <? k).
Proof.
intros x k Hk. unfold branch_taken. cbn -[alu64 Z_to_bv bv_unsigned Z.ltb]. unfold bv_ltu. rewrite abs63_unsigned, unsigned_lit by lia. reflexivity.
Qed.
Lemma abs63_ne : forall (x : word) k, 0 <= k < 2^64 ->
branch_taken BC_NE (alu64 ALU_SRL (alu64 ALU_SLL x (Z_to_bv 64 1)) (Z_to_bv 64 1)) (Z_to_bv 64 k) = negb (bv_unsigned x mod 2^63 =? k).
Proof.
intros x k Hk. unfold branch_taken. cbn -[alu64 Z_to_bv bv_unsigned Z.eqb].
destruct (Z.eqb_spec (bv_unsigned x mod 2^63) k) as [E|NE]; cbn [negb].
- rewrite (proj2 (Fs.bv_eqb_eq _ _)); [reflexivity|]. apply bv_eq. rewrite abs63_unsigned, unsigned_lit by lia. exact E.
- destruct (bv_eqb _ _) eqn:E; [|reflexivity]. exfalso. apply (proj1 (Fs.bv_eqb_eq _ _)) in E. apply NE.
apply (f_equal bv_unsigned) in E. rewrite abs63_unsigned, unsigned_lit in E by lia. exact E.
Qed.

Lemma abs63m_unsigned : forall x : word,
bv_unsigned (alu64 ALU_SRL (mul_div M_MUL (Z_to_bv 64 2) x) (Z_to_bv 64 1)) = bv_unsigned x mod 2^63.
Proof.
intros x. pose proof (bv_unsigned_in_range 64 x) as R. unfold bv_modulus in R. cbn in R.
unfold alu64, alu, mul_div. cbn iota beta.
replace (bv_and (Z_to_bv 64 1) (Z_to_bv 64 63)) with (Z_to_bv 64 1) by (apply bv_eq; vm_compute; reflexivity).
rewrite bv_shiftr_unsigned, bv_mul_unsigned, !unsigned_lit by lia. unfold bv_wrap.
replace (bv_modulus 64) with (2^64) by reflexivity.
rewrite Z.shiftr_div_pow2 by lia. change (2^1) with 2.
Z.div_mod_to_equations. lia.
Qed.
Lemma abs63m_ltu : forall (x : word) k, 0 <= k < 2^64 ->
bv_ltu (alu64 ALU_SRL (mul_div M_MUL (Z_to_bv 64 2) x) (Z_to_bv 64 1)) (Z_to_bv 64 k) = (bv_unsigned x mod 2^63 <? k).
Proof. intros x k Hk. unfold bv_ltu. rewrite abs63m_unsigned, unsigned_lit by lia. reflexivity. Qed.
Lemma abs63m_eqb : forall (x : word) k, 0 <= k < 2^64 ->
bv_eqb (alu64 ALU_SRL (mul_div M_MUL (Z_to_bv 64 2) x) (Z_to_bv 64 1)) (Z_to_bv 64 k) = (bv_unsigned x mod 2^63 =? k).
Proof.
intros x k Hk. destruct (Z.eqb_spec (bv_unsigned x mod 2^63) k) as [E|NE].
- apply (proj2 (Fs.bv_eqb_eq _ _)). apply bv_eq. rewrite abs63m_unsigned, unsigned_lit by lia. exact E.
- destruct (bv_eqb _ _) eqn:E; [|reflexivity]. exfalso. apply (proj1 (Fs.bv_eqb_eq _ _)) in E. apply NE.
apply (f_equal bv_unsigned) in E. rewrite abs63m_unsigned, unsigned_lit in E by lia. exact E.
Qed.

Lemma inf_bits : forall x : word, bv_unsigned x mod 2^63 = 0x7FF0000000000000 ->
x = Z_to_bv 64 0x7FF0000000000000 \/ x = Z_to_bv 64 0xFFF0000000000000.
Proof.
intros x H. pose proof (bv_unsigned_in_range 64 x) as R. unfold bv_modulus in R. cbn in R.
assert (D : bv_unsigned x / 2^63 = 0 \/ bv_unsigned x / 2^63 = 1) by (Z.div_mod_to_equations; lia).
destruct D as [D|D]; [left|right]; apply bv_eq; rewrite unsigned_lit by lia; Z.div_mod_to_equations; lia.
Qed.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH.
Lemma fsaved_set_tmp : forall F F' (k : bv 5) v,
fsaved F F' -> ~ In (bv_unsigned k) FSAVED -> fsaved F (bvmap_set k v F').
Proof.
intros F F' k v H Hk j Hj. rewrite QEpW.reg_get_set_other; [apply H; exact Hj|].
intros E. apply Hk. rewrite E. rewrite Z_to_bv_unsigned. unfold bv_wrap.
replace (bv_modulus 5) with 32 by reflexivity. cbn in Hj.
repeat (destruct Hj as [<-|Hj]; [cbn; tauto|]). destruct Hj.
Qed.

Ltac fsaved_tmp := repeat (apply fsaved_set_tmp; [| vm_compute; intuition discriminate]); first [apply fsaved_refl | assumption].

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7.
Lemma abs_idiom_nonneg : forall len, 0 <= len < 2^63 ->
Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 len))
(bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_signed (Z_to_bv 64 len)) (63 mod 64)))))) -
bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_signed (Z_to_bv 64 len)) (63 mod 64))))
= Z_to_bv 64 len.
Proof.
intros len H. rewrite (signed_lit len) by lia. change (63 mod 64) with 63.
rewrite (Z.shiftr_div_pow2 len 63) by lia. rewrite (Z.div_small len (2^63)) by lia.
rewrite (unsigned_lit 0) by lia. rewrite (unsigned_lit len) by lia. rewrite Z.lxor_0_r. rewrite unsigned_lit by lia. f_equal. lia.
Qed.

Lemma land3_mod : forall x, Z.land x 3 = x mod 4.
Proof. intros. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma alu_and3 : forall x, 0 <= x < 2^64 -> alu64 ALU_AND (Z_to_bv 64 x) (Z_to_bv 64 3) = Z_to_bv 64 (Z.land x 3).
Proof.
intros x Hx. pose proof (land3_mod x) as L. assert (R : 0 <= Z.land x 3 < 4) by (rewrite L; Z.div_mod_to_equations; lia).
apply bv_eq. unfold alu64, alu. cbn iota beta. rewrite bv_and_unsigned, !unsigned_lit by lia. reflexivity.
Qed.

Lemma swrap32_id : forall x, -2^31 <= x < 2^31 -> bv_swrap 32 x = x.
Proof.
intros. unfold bv_swrap, bv_wrap. replace (bv_half_modulus 32) with (2^31) by reflexivity.
replace (bv_modulus 32) with (2^32) by reflexivity. Z.div_mod_to_equations. lia.
Qed.

Lemma slliw1_small : forall x, 0 <= x < 2^30 -> Z_to_bv 64 (bv_swrap 32 (Z.shiftl x (1 mod 32))) = Z_to_bv 64 (2 * x).
Proof. intros x Hx. change (1 mod 32) with 1. rewrite Z.shiftl_mul_pow2 by lia. change (2^1) with 2. rewrite swrap32_id by lia. f_equal. lia. Qed.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsjA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsjA.
Ltac fold_mkR :=
lazymatch goal with
| |- context [MS (TNode (TNode (TNode (TNode (TNode (TNode TEmpty (Some ?x31) TEmpty) (Some ?x15) TEmpty) (Some ?x7) (TNode TEmpty (Some ?x23) TEmpty)) (Some ?x3) (TNode (TNode TEmpty (Some ?x19) TEmpty) (Some ?x11) (TNode TEmpty (Some ?x27) TEmpty))) (Some ?x1) (TNode (TNode (TNode TEmpty (Some ?x17) TEmpty) (Some ?x9) (TNode TEmpty (Some ?x25) TEmpty)) (Some ?x5) (TNode (TNode TEmpty (Some ?x21) TEmpty) (Some ?x13) (TNode TEmpty (Some ?x29) TEmpty)))) None (TNode (TNode (TNode (TNode TEmpty (Some ?x16) TEmpty) (Some ?x8) (TNode TEmpty (Some ?x24) TEmpty)) (Some ?x4) (TNode (TNode TEmpty (Some ?x20) TEmpty) (Some ?x12) (TNode TEmpty (Some ?x28) TEmpty))) (Some ?x2) (TNode (TNode (TNode TEmpty (Some ?x18) TEmpty) (Some ?x10) (TNode TEmpty (Some ?x26) TEmpty)) (Some ?x6) (TNode (TNode TEmpty (Some ?x22) TEmpty) (Some ?x14) (TNode TEmpty (Some ?x30) TEmpty))))) ?F ?pc ?fc ?rv ?m ?ro] =>
change (TNode (TNode (TNode (TNode (TNode (TNode TEmpty (Some x31) TEmpty) (Some x15) TEmpty) (Some x7) (TNode TEmpty (Some x23) TEmpty)) (Some x3) (TNode (TNode TEmpty (Some x19) TEmpty) (Some x11) (TNode TEmpty (Some x27) TEmpty))) (Some x1) (TNode (TNode (TNode TEmpty (Some x17) TEmpty) (Some x9) (TNode TEmpty (Some x25) TEmpty)) (Some x5) (TNode (TNode TEmpty (Some x21) TEmpty) (Some x13) (TNode TEmpty (Some x29) TEmpty)))) None (TNode (TNode (TNode (TNode TEmpty (Some x16) TEmpty) (Some x8) (TNode TEmpty (Some x24) TEmpty)) (Some x4) (TNode (TNode TEmpty (Some x20) TEmpty) (Some x12) (TNode TEmpty (Some x28) TEmpty))) (Some x2) (TNode (TNode (TNode TEmpty (Some x18) TEmpty) (Some x10) (TNode TEmpty (Some x26) TEmpty)) (Some x6) (TNode (TNode TEmpty (Some x22) TEmpty) (Some x14) (TNode TEmpty (Some x30) TEmpty)))))
with (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
| |- _ => idtac
end.
