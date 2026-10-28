(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0p YK0s YK15 YN06 YQ0b YQ04.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0c.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 YI00 YI02 UI1i
YI0x YL0e YI08 YI0c UI3h UI3d UI4y UI50.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section S.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Hypothesis NEWG : rgb_newgif_spec API.
Hypothesis CLOSE : forall fx', rgb_close_spec (fx:=fx') API.
Hypothesis ADDF : forall fx', rgb_addframe_spec (fx:=fx') API.
Definition rllvm_spec (pc empty : Z) : Prop :=
forall L A regs mem md p n,
fn_pre ubs2_msyms MR LIB_STACK_RGB L A regs mem md ->
st_init_done A = true ->
frm_zero fp_csr -> ubs2_rgb_rodata_ok mem ->
getr regs 10 = Z_to_bv 64 p -> getr regs 11 = Z_to_bv 64 n ->
((n = 0 /\ p = empty) \/ (0 < n /\ In (p, n) (blocks L A))) ->
SR ubs2segs (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom ubs2segs)) md) (rllvm_post API regs L A mem md).
Theorem ubs2_rllvm_spec : forall empty, rllvm_spec ubs2_A_LLVMFuzzerTestOneInput empty.
Proof.
intros empty L A regs mem md p n HPRE Hid HFZ HRO G10 G11 Hpn.
change (SR ubs2segs (mkCfg (mkst regs (Z_to_bv 64 RLLVM) mem (seg_rom ubs2segs)) md) (rllvm_post API regs L A mem md)).
set (p' := bv_unsigned (getr regs 10)).
assert (G10' : getr regs 10 = Z_to_bv 64 p') by (subst p'; symmetry; apply Z_to_bv_bv_unsigned).
assert (Hp' : 0 <= p' < 2 ^ 64) by (subst p'; pose proof (bv_unsigned_in_range 64 (getr regs 10)) as Hr; change (bv_modulus 64) with (2 ^ 64) in Hr; lia).
destruct Hpn as [[-> ->] | [Hn Hin]].
- exact (rlh_case_0 API IMG L A regs mem md p' 0 ltac:(lia) HFZ HPRE Hid G10' G11 Hp').
- assert (Hpp : p' = p).
{ subst p'. rewrite G10. destruct (blocks_range _ _ LAWS L A mem md p n (proj1 HPRE) Hin) as [H0 H1].
pose proof (proj1 alloc_ceiling_val). apply unsigned_lit_small. lia. }
rewrite Hpp in Hp'.
destruct (Z_lt_le_dec n 2) as [H0|H0]; [apply (rlh_case_0 API IMG L A regs mem md p n); try assumption; lia|].
destruct (Z_lt_le_dec n 4) as [H1|H1]; [apply (rlh_case_1 API IMG L A regs mem md p n); try assumption; lia|].
destruct (Z_lt_le_dec n 8) as [H2|H2]; [apply (rlh_case_2 API IMG L A regs mem md p n); try assumption; lia|].
destruct (Z_lt_le_dec n 12) as [H3|H3]; [apply (rlh_case_3 API IMG L A regs mem md p n); try assumption; lia|].
destruct (Z_lt_le_dec n 14) as [H4|H4]; [apply (rlh_case_4 API IMG L A regs mem md p n); try assumption; lia|].
apply (rlh_case_5 API IMG NEWG CLOSE ADDF L A regs mem md p n); try assumption; lia.
Qed.
End S.
End a.
