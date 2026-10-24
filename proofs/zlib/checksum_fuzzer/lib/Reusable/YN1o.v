(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK0w YK0v.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP02 YP09 YH00 YH03 YH02 YN32.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0a YO0c YN2e YN05 YN04.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition PS_ZL' : Z := src0_A_alloc_slot + 0x438.
Definition PS_ZE' : Z := src0_A_alloc_slot + 0x448.
Lemma FZ_438 : fetch_word src0segs (Z_to_bv 64 (src0_A_alloc_slot + 0x438)) = Some (0x00060023%bv : bv 32).
Proof. ftac. Qed.
Lemma DZ_438 : decode_any (0x00060023%bv : bv 32) = Some (Store SZ1 12 0 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FZ_43c : fetch_word src0segs (Z_to_bv 64 (src0_A_alloc_slot + 0x43c)) = Some (0xfff58593%bv : bv 32).
Proof. ftac. Qed.
Lemma DZ_43c : decode_any (0xfff58593%bv : bv 32) = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FZ_440 : fetch_word src0segs (Z_to_bv 64 (src0_A_alloc_slot + 0x440)) = Some (0x01860633%bv : bv 32).
Proof. ftac. Qed.
Lemma DZ_440 : decode_any (0x01860633%bv : bv 32) = Some (Op ALU_ADD 12 12 24, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FZ_444 : fetch_word src0segs (Z_to_bv 64 (src0_A_alloc_slot + 0x444)) = Some (0xfe059ae3%bv : bv 32).
Proof. ftac. Qed.
Lemma DZ_444 : decode_any (0xfe059ae3%bv : bv 32) = Some (Branch BC_NE 11 0 8180, 4%Z).
Proof. vm_refl_bv. Qed.
Fixpoint zmem (mem : word -> option byte) (addr sz : Z) (c : nat) : word -> option byte :=
match c with
| O => mem
| S c' => zmem (wbytes mem (Z64 addr) [Z_to_bv 8 0]) (addr + sz) sz c'
end.
Lemma zmem_writable : forall c mem addr sz x, writable_at src0segs mem x -> writable_at src0segs (zmem mem addr sz c) x.
Proof. induction c as [|c IH]; intros mem addr sz x Hw; cbn [zmem]; [exact Hw|]. apply IH. apply wbytes_writable. exact Hw. Qed.
Lemma zmem_present : forall c mem addr sz a, mem a <> None -> zmem mem addr sz c a <> None.
Proof. induction c as [|c IH]; intros mem addr sz a Hp; cbn [zmem]; [exact Hp|]. apply IH. apply wbytes_present. exact Hp. Qed.
Lemma zmem_other : forall c mem addr sz x, 0 <= x < 2 ^ 64 -> 0 <= addr -> 0 <= sz -> addr + Z.of_nat c * sz < 2 ^ 64 ->
(forall i, (i < c)%nat -> x <> addr + Z.of_nat i * sz) -> zmem mem addr sz c (Z64 x) = mem (Z64 x).
Proof.
induction c as [|c IH]; intros mem addr sz x Hx Ha Hs Hb Hne; cbn [zmem]; [reflexivity|].
rewrite IH; [| exact Hx | lia | exact Hs | lia |].
- apply wbytes_other; cbn [length]; [lia | lia | exact Hx |]. pose proof (Hne 0%nat ltac:(lia)). cbn [Z.of_nat] in H. lia.
- intros i Hi. pose proof (Hne (S i) ltac:(lia)). rewrite Nat2Z.inj_succ in H. lia.
Qed.
Lemma zmem_at : forall c mem addr sz i, 0 <= addr -> 1 <= sz -> addr + Z.of_nat c * sz < 2 ^ 64 -> (i < c)%nat ->
zmem mem addr sz c (Z64 (addr + Z.of_nat i * sz)) = Some (Z_to_bv 8 0).
Proof.
induction c as [|c IH]; intros mem addr sz i Ha Hs Hb Hi; [lia|]. cbn [zmem].
destruct i as [|i].
- cbn [Z.of_nat]. rewrite Z.mul_0_l, Z.add_0_r. rewrite zmem_other; [| lia | lia | lia | lia |].
+ unfold wbytes. cbn. rewrite bv_eqb_refl. reflexivity.
+ intros i' Hi'. nia.
- replace (addr + Z.of_nat (S i) * sz) with (addr + sz + Z.of_nat i * sz) by (rewrite Nat2Z.inj_succ; lia). apply IH; lia.
Qed.
Theorem zero_loop : forall (c : nat) rom regs mem addr sz,
(0 < c)%nat ->
getr regs 11 = Z64 (Z.of_nat c) -> getr regs 12 = Z64 addr -> getr regs 24 = Z64 sz ->
0 <= addr -> 1 <= sz -> addr + Z.of_nat c * sz < 2 ^ 63 ->
(forall i, (i < c)%nat -> writable_at src0segs mem (addr + Z.of_nat i * sz)) ->
exists regs',
msteps src0segs (mkst regs (Z64 PS_ZL') mem rom) (mkst regs' (Z64 PS_ZE') (zmem mem addr sz c) rom) /\
getr regs' 11 = Z64 0 /\ getr regs' 12 = Z64 (addr + Z.of_nat c * sz) /\
(forall r : reg, r <> 11%bv -> r <> 12%bv -> getr regs' r = getr regs r).
Proof.
induction c as [|c IH]; intros rom regs mem addr sz Hc H11 H12 H24 Ha Hs Hb HW; [lia|].
assert (ONE : msteps src0segs (mkst regs (Z64 PS_ZL') mem rom)
(mkst (regupd (regupd regs 11 (Z64 (Z.of_nat c))) 12 (Z64 (addr + sz))) (Z64 (src0_A_alloc_slot + 0x444)) (wbytes mem (Z64 addr) [Z_to_bv 8 0]) rom)).
{ unfold PS_ZL'. norm_pc.
svsb FZ_438 DZ_438 (Z64 addr) (Z64 0) (Z_to_bv 8 0)
atac ltac:(gr; reflexivity) ltac:(reflexivity)
ltac:(apply store_ok_writable; [lia | cbn [length]; lia | intros x Hx; cbn [length] in Hx; replace x with (addr + Z.of_nat 0 * sz) by lia; apply HW; lia]).
sva FZ_43c DZ_43c step_addi (Z64 (Z.of_nat c)) ltac:(gr; rwH; imm_norm; rewrite v_addi_lit; f_equal; rewrite Nat2Z.inj_succ; lia).
sva FZ_440 DZ_440 step_add (Z64 (addr + sz)) ltac:(gr; rwH; rewrite v_add_lit; reflexivity).
seg_done. }
destruct c as [|c'].
-
exists (regupd (regupd regs 11 (Z64 0)) 12 (Z64 (addr + sz))). split; [| split; [gr; reflexivity | split; [gr; cbn [Z.of_nat]; f_equal; lia | intros r H1 H2; rewrite !getr_other by (exact H2 || exact H1); reflexivity]]].
eapply msteps_trans; [exact ONE|]. cbn [Z.of_nat]. unfold PS_ZE'. norm_pc.
stepbfz FZ_444 DZ_444.
seg_done.
-
assert (BR : msteps src0segs (mkst (regupd (regupd regs 11 (Z64 (Z.of_nat (S c')))) 12 (Z64 (addr + sz))) (Z64 (src0_A_alloc_slot + 0x444)) (wbytes mem (Z64 addr) [Z_to_bv 8 0]) rom)
(mkst (regupd (regupd regs 11 (Z64 (Z.of_nat (S c')))) 12 (Z64 (addr + sz))) (Z64 PS_ZL') (wbytes mem (Z64 addr) [Z_to_bv 8 0]) rom)).
{ unfold PS_ZL'. norm_pc. stepbtz FZ_444 DZ_444. seg_done. }
destruct (IH rom (regupd (regupd regs 11 (Z64 (Z.of_nat (S c')))) 12 (Z64 (addr + sz))) (wbytes mem (Z64 addr) [Z_to_bv 8 0]) (addr + sz) sz
ltac:(lia) ltac:(gr; reflexivity) ltac:(gr; reflexivity) ltac:(gr; exact H24) ltac:(lia) Hs ltac:(rewrite Nat2Z.inj_succ in Hb; lia))
as (regs' & MS & R11 & R12 & RO).
{ intros i Hi. apply wbytes_writable. replace (addr + sz + Z.of_nat i * sz) with (addr + Z.of_nat (S i) * sz) by (rewrite Nat2Z.inj_succ; lia). apply HW. lia. }
exists regs'. split; [| split; [exact R11 | split; [rewrite R12; f_equal; rewrite Nat2Z.inj_succ; lia | intros r H1 H2; rewrite (RO r H1 H2); rewrite !getr_other by (exact H2 || exact H1); reflexivity]]].
eapply msteps_trans; [exact ONE|]. eapply msteps_trans; [exact BR|]. cbn [zmem]. exact MS.
Qed.
End b.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
