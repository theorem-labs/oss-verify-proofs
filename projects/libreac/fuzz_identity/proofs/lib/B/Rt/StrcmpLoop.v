(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-29: relocated from libreac/fuzz_grant lib/A/Rt/StrcmpLoop.v (a working branch 97c611eec86, owner a Theorem Labs lane, proved there on fuzz_grant.asan) to libreac/fuzz_identity image B (fuzz_identity.asan-ubsan, sha256 baf1a4d065e02f55521d39f05d8c8d9ed763a0ef798c70cc3eabe5816ffb3f66) by an address map recorded by the porting lane; module paths lib.A -> lib.B, GrantSyms -> TfibSyms, #[local] Zify override. The proof text is unchanged. *)
(* Written by Theorem Labs, 2026-10, for libreac/fuzz_identity's ASan+UBSan build (image B): the byte loop of ___interceptor_strcmp,
   as a plain machine walk (msteps), in the form of B/AE3a.v's byte loop (mc_tail). MEASURED on
   fuzz_identity.asan-ubsan (objdump + nm of the pinned binary):
     0x42810  add  a0,s2,s4      01490533
     0x42814  lbu  s9,0(a0)      00054c83
     0x42818  add  a0,s1,s4      01448533
     0x4281c  lbu  s10,0(a0)     00054d03
     0x42820  addi s4,s4,1       001a0a13
     0x42824  beqz s9,0x4282c    000c8463
     0x42828  beq  s9,s10,0x42810 ffac84e3
   with s2 = x (s1 of strcmp), s1 = y (s2 of strcmp), s4 = i. Loop invariant at 0x42810: s2 = x, s1 = y, s4 = i with
   0 <= i <= k, and the bytes x[j] = y[j] <> 0 for j < i (the bytes the earlier iterations compared); every other
   register but a0, s4, s9, s10 is the one at the first entry. The loop leaves at 0x4282c after the iteration
   i = k (x[k] = 0 or x[k] <> y[k]) with s4 = k + 1, s9 = x[k], s10 = y[k]. Memory is only read. *)
(* Modified by Theorem Labs, 2026-10-29: for a Theorem Labs lane's acceptance (a working branch), the record class is TfibSyms, not IdentTfibSyms, and the core modules are Required by full path at the applied B core's names: lib/B/A<x>.v -> lib/ReusableB/Y<x>.v (AB1v AB1w AE20 AE2y AE34 AE39 AE3a AE6y AF0l AF0m AF0x -> YB1v YB1w YE20 YE2y YE34 YE39 YE3a YE6y YF0l YF0m YF0x, qualified names included), lib/Reusable/YA0m, YE08, YE21. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v YG0d.
Require Import
  OSSVerify.Proofs.libreac.fuzz_identity.lib.ReusableB.YB1v
  OSSVerify.Proofs.libreac.fuzz_identity.lib.ReusableB.YE34
  OSSVerify.Proofs.libreac.fuzz_identity.lib.ReusableB.YF0l
  OSSVerify.Proofs.libreac.fuzz_identity.lib.ReusableB.YF0m
  OSSVerify.Proofs.libreac.fuzz_identity.lib.ReusableB.YF0x
  OSSVerify.Proofs.libreac.fuzz_identity.lib.ReusableB.YB1w
  OSSVerify.Proofs.libreac.fuzz_identity.lib.ReusableB.YE20
  OSSVerify.Proofs.libreac.fuzz_identity.lib.ReusableB.YE2y.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Rt Require Import StrcmpTbl.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Definition SL_HEAD : Z := 0x42810.
Definition SL_EXIT : Z := 0x4282c.
Section s. Context {fx : YK11.FPState}.
Variables (m rom : word -> option byte).
Lemma u64_lit : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia. Qed.
Lemma u8_lit : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. lia. Qed.
Lemma v_addi_0' : forall x : word, v_addi x (bv_signed (0%bv : bv 12)) = x.
Proof. intros x. change (bv_signed (0%bv : bv 12)) with 0. unfold v_addi. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
Lemma eqb_lit : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof. intros a b Ha Hb. unfold bv_eqb. rewrite !u64_lit by lia. reflexivity. Qed.
(* The seven instructions, each as one step from a literal pc. *)
Lemma sl_add_x : forall regs a b, getr regs 18 = Z_to_bv 64 a -> getr regs 20 = Z_to_bv 64 b ->
0 <= a -> 0 <= b -> a + b < 2 ^ 64 ->
RiscvSemantics.step tfibsegs (mkst regs (Z_to_bv 64 0x42810) m rom) =
MachineOk (mkst (regupd regs 10 (Z_to_bv 64 (a + b))) (Z_to_bv 64 0x42814) m rom).
Proof.
intros regs a b Ha Hb Ra Rb Rab.
rewrite (step_add_at tfibsegs regs _ m rom (Z_to_bv 32 0x01490533) 10 18 20 (Z_to_bv 64 (a + b))).
- f_equal; f_equal; apply bv_eq; vm_compute; reflexivity.
- exact (tbl_sc_ok 0x42810 0x01490533 ltac:(vm_compute; reflexivity)).
- vm_compute. reflexivity.
- vm_refl_bv.
- reflexivity.
- unfold v_add. rewrite Ha, Hb, !u64_lit by lia. reflexivity.
Qed.
Lemma sl_lbu_x : forall regs a v, getr regs 10 = Z_to_bv 64 a -> 0 <= v < 256 ->
rdn tfibsegs m (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v] ->
RiscvSemantics.step tfibsegs (mkst regs (Z_to_bv 64 0x42814) m rom) =
MachineOk (mkst (regupd regs 25 (Z_to_bv 64 v)) (Z_to_bv 64 0x42818) m rom).
Proof.
intros regs a v Ha Hv Hr.
rewrite (step_lbu tfibsegs regs _ m rom (Z_to_bv 32 0x00054c83) 25 10 0%bv (Z_to_bv 8 v)).
- replace (bv_eqb (25%bv : bv 5) 0%bv) with false by reflexivity. rewrite u8_lit by lia.
f_equal; f_equal; apply bv_eq; vm_compute; reflexivity.
- exact (tbl_sc_ok 0x42814 0x00054c83 ltac:(vm_compute; reflexivity)).
- vm_compute. reflexivity.
- vm_refl_bv.
- rewrite v_addi_0', Ha. exact Hr.
Qed.
Lemma sl_add_y : forall regs a b, getr regs 9 = Z_to_bv 64 a -> getr regs 20 = Z_to_bv 64 b ->
0 <= a -> 0 <= b -> a + b < 2 ^ 64 ->
RiscvSemantics.step tfibsegs (mkst regs (Z_to_bv 64 0x42818) m rom) =
MachineOk (mkst (regupd regs 10 (Z_to_bv 64 (a + b))) (Z_to_bv 64 0x4281c) m rom).
Proof.
intros regs a b Ha Hb Ra Rb Rab.
rewrite (step_add_at tfibsegs regs _ m rom (Z_to_bv 32 0x01448533) 10 9 20 (Z_to_bv 64 (a + b))).
- f_equal; f_equal; apply bv_eq; vm_compute; reflexivity.
- exact (tbl_sc_ok 0x42818 0x01448533 ltac:(vm_compute; reflexivity)).
- vm_compute. reflexivity.
- vm_refl_bv.
- reflexivity.
- unfold v_add. rewrite Ha, Hb, !u64_lit by lia. reflexivity.
Qed.
Lemma sl_lbu_y : forall regs a v, getr regs 10 = Z_to_bv 64 a -> 0 <= v < 256 ->
rdn tfibsegs m (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v] ->
RiscvSemantics.step tfibsegs (mkst regs (Z_to_bv 64 0x4281c) m rom) =
MachineOk (mkst (regupd regs 26 (Z_to_bv 64 v)) (Z_to_bv 64 0x42820) m rom).
Proof.
intros regs a v Ha Hv Hr.
rewrite (step_lbu tfibsegs regs _ m rom (Z_to_bv 32 0x00054d03) 26 10 0%bv (Z_to_bv 8 v)).
- replace (bv_eqb (26%bv : bv 5) 0%bv) with false by reflexivity. rewrite u8_lit by lia.
f_equal; f_equal; apply bv_eq; vm_compute; reflexivity.
- exact (tbl_sc_ok 0x4281c 0x00054d03 ltac:(vm_compute; reflexivity)).
- vm_compute. reflexivity.
- vm_refl_bv.
- rewrite v_addi_0', Ha. exact Hr.
Qed.
Lemma sl_inc : forall regs i, getr regs 20 = Z_to_bv 64 i -> 0 <= i -> i + 1 < 2 ^ 64 ->
RiscvSemantics.step tfibsegs (mkst regs (Z_to_bv 64 0x42820) m rom) =
MachineOk (mkst (regupd regs 20 (Z_to_bv 64 (i + 1))) (Z_to_bv 64 0x42824) m rom).
Proof.
intros regs i Hi Ri Ri1.
rewrite (step_addi_at tfibsegs regs _ m rom (Z_to_bv 32 0x001a0a13) 20 20 1%bv (Z_to_bv 64 (i + 1))).
- f_equal; f_equal; apply bv_eq; vm_compute; reflexivity.
- exact (tbl_sc_ok 0x42820 0x001a0a13 ltac:(vm_compute; reflexivity)).
- vm_compute. reflexivity.
- vm_refl_bv.
- reflexivity.
- rewrite Hi. change (bv_signed (1%bv : bv 12)) with 1. unfold v_addi. rewrite u64_lit by lia. reflexivity.
Qed.
Lemma sl_nul_tk : forall regs, getr regs 25 = Z_to_bv 64 0 ->
RiscvSemantics.step tfibsegs (mkst regs (Z_to_bv 64 0x42824) m rom) = MachineOk (mkst regs (Z_to_bv 64 SL_EXIT) m rom).
Proof.
intros regs H25.
rewrite (step_branch_tk_gen tfibsegs regs _ m rom (Z_to_bv 32 0x000c8463) BC_EQ 25 0 8%bv).
- f_equal; f_equal; apply bv_eq; vm_compute; reflexivity.
- exact (tbl_sc_ok 0x42824 0x000c8463 ltac:(vm_compute; reflexivity)).
- vm_compute. reflexivity.
- vm_refl_bv.
- cbn [branch_taken]. rewrite H25, getr_zero. reflexivity.
Qed.
Lemma sl_nul_ft : forall regs v, getr regs 25 = Z_to_bv 64 v -> 0 < v < 256 ->
RiscvSemantics.step tfibsegs (mkst regs (Z_to_bv 64 0x42824) m rom) = MachineOk (mkst regs (Z_to_bv 64 0x42828) m rom).
Proof.
intros regs v H25 Hv.
rewrite (step_branch_ft_gen tfibsegs regs _ m rom (Z_to_bv 32 0x000c8463) BC_EQ 25 0 8%bv).
- f_equal; f_equal; apply bv_eq; vm_compute; reflexivity.
- exact (tbl_sc_ok 0x42824 0x000c8463 ltac:(vm_compute; reflexivity)).
- vm_compute. reflexivity.
- vm_refl_bv.
- cbn [branch_taken]. rewrite H25, getr_zero, eqb_lit by lia. apply Z.eqb_neq. lia.
Qed.
Lemma sl_eq_tk : forall regs v, getr regs 25 = Z_to_bv 64 v -> getr regs 26 = Z_to_bv 64 v ->
RiscvSemantics.step tfibsegs (mkst regs (Z_to_bv 64 0x42828) m rom) = MachineOk (mkst regs (Z_to_bv 64 SL_HEAD) m rom).
Proof.
intros regs v H25 H26.
rewrite (step_branch_tk_gen tfibsegs regs _ m rom (Z_to_bv 32 0xffac84e3) BC_EQ 25 26 8168%bv).
- f_equal; f_equal; apply bv_eq; vm_compute; reflexivity.
- exact (tbl_sc_ok 0x42828 0xffac84e3 ltac:(vm_compute; reflexivity)).
- vm_compute. reflexivity.
- vm_refl_bv.
- cbn [branch_taken]. rewrite H25, H26. apply bv_eqb_refl.
Qed.
Lemma sl_eq_ft : forall regs v1 v2, getr regs 25 = Z_to_bv 64 v1 -> getr regs 26 = Z_to_bv 64 v2 ->
0 <= v1 < 256 -> 0 <= v2 < 256 -> v1 <> v2 ->
RiscvSemantics.step tfibsegs (mkst regs (Z_to_bv 64 0x42828) m rom) = MachineOk (mkst regs (Z_to_bv 64 SL_EXIT) m rom).
Proof.
intros regs v1 v2 H25 H26 R1 R2 Hne.
rewrite (step_branch_ft_gen tfibsegs regs _ m rom (Z_to_bv 32 0xffac84e3) BC_EQ 25 26 8168%bv).
- f_equal; f_equal; apply bv_eq; vm_compute; reflexivity.
- exact (tbl_sc_ok 0x42828 0xffac84e3 ltac:(vm_compute; reflexivity)).
- vm_compute. reflexivity.
- vm_refl_bv.
- cbn [branch_taken]. rewrite H25, H26, eqb_lit by lia. apply Z.eqb_neq. exact Hne.
Qed.
(* One pass of the five straight-line instructions from the loop head, comparing x[i] with y[i]. *)
Definition sl_regs (regs : bvmap 5 word) (x y i b1 b2 : Z) : bvmap 5 word :=
regupd (regupd (regupd (regupd (regupd regs 10 (Z_to_bv 64 (x + i))) 25 (Z_to_bv 64 b1)) 10 (Z_to_bv 64 (y + i)))
26 (Z_to_bv 64 b2)) 20 (Z_to_bv 64 (i + 1)).
Lemma sl_regs_get : forall regs x y i b1 b2,
getr (sl_regs regs x y i b1 b2) 20 = Z_to_bv 64 (i + 1) /\ getr (sl_regs regs x y i b1 b2) 25 = Z_to_bv 64 b1 /\
getr (sl_regs regs x y i b1 b2) 26 = Z_to_bv 64 b2 /\
(forall r : bv 5, r <> 10%bv -> r <> 20%bv -> r <> 25%bv -> r <> 26%bv -> getr (sl_regs regs x y i b1 b2) r = getr regs r).
Proof.
intros regs x y i b1 b2. unfold sl_regs.
split; [rewrite getr_same by discriminate; reflexivity|].
split; [rewrite getr_other by discriminate; rewrite getr_other by discriminate; rewrite getr_other by discriminate;
rewrite getr_same by discriminate; reflexivity|].
split; [rewrite getr_other by discriminate; rewrite getr_same by discriminate; reflexivity|].
intros r H10 H20 H25 H26. rewrite !getr_other by assumption. reflexivity.
Qed.
Lemma sl_pass : forall regs x y i b1 b2,
getr regs 18 = Z_to_bv 64 x -> getr regs 9 = Z_to_bv 64 y -> getr regs 20 = Z_to_bv 64 i ->
0 <= x -> 0 <= y -> 0 <= i -> x + i < 2 ^ 63 -> y + i < 2 ^ 63 ->
0 <= b1 < 256 -> 0 <= b2 < 256 ->
rdn tfibsegs m (Z_to_bv 64 (x + i)) 1 = Some [Z_to_bv 8 b1] -> rdn tfibsegs m (Z_to_bv 64 (y + i)) 1 = Some [Z_to_bv 8 b2] ->
msteps tfibsegs (mkst regs (Z_to_bv 64 SL_HEAD) m rom) (mkst (sl_regs regs x y i b1 b2) (Z_to_bv 64 0x42824) m rom).
Proof.
intros regs x y i b1 b2 G18 G9 G20 Hx Hy Hi Hxi Hyi Hb1 Hb2 R1 R2. unfold sl_regs.
eapply mst_step; [reflexivity | exact (sl_add_x regs x i G18 G20 Hx Hi ltac:(lia)) |].
eapply mst_step; [reflexivity | apply (sl_lbu_x _ (x + i) b1); [rewrite getr_same by discriminate; reflexivity | exact Hb1 | exact R1] |].
eapply mst_step; [reflexivity | apply (sl_add_y _ y i); [rewrite getr_other by discriminate; rewrite getr_other by discriminate; exact G9 |
rewrite getr_other by discriminate; rewrite getr_other by discriminate; exact G20 | lia | lia | lia] |].
eapply mst_step; [reflexivity | apply (sl_lbu_y _ (y + i) b2); [rewrite getr_same by discriminate; reflexivity | exact Hb2 | exact R2] |].
eapply mst_step; [reflexivity | apply (sl_inc _ i); [rewrite !getr_other by discriminate; exact G20 | lia | lia] |].
apply mst_refl.
Qed.
(* The loop, by induction on the number d = k - i of iterations left before the last one. *)
Lemma sl_loop : forall x y k c1 c2, 0 <= x -> 0 <= y -> x + k + 1 <= 2 ^ 63 -> y + k + 1 <= 2 ^ 63 ->
(forall j, 0 <= j < k -> exists b, 0 < b < 256 /\
  rdn tfibsegs m (Z_to_bv 64 (x + j)) 1 = Some [Z_to_bv 8 b] /\ rdn tfibsegs m (Z_to_bv 64 (y + j)) 1 = Some [Z_to_bv 8 b]) ->
0 <= c1 < 256 -> 0 <= c2 < 256 ->
rdn tfibsegs m (Z_to_bv 64 (x + k)) 1 = Some [Z_to_bv 8 c1] -> rdn tfibsegs m (Z_to_bv 64 (y + k)) 1 = Some [Z_to_bv 8 c2] ->
(c1 <> c2 \/ c1 = 0) ->
forall (d : nat) regs i, i + Z.of_nat d = k -> 0 <= i ->
getr regs 18 = Z_to_bv 64 x -> getr regs 9 = Z_to_bv 64 y -> getr regs 20 = Z_to_bv 64 i ->
exists regs', msteps tfibsegs (mkst regs (Z_to_bv 64 SL_HEAD) m rom) (mkst regs' (Z_to_bv 64 SL_EXIT) m rom) /\
getr regs' 20 = Z_to_bv 64 (k + 1) /\ getr regs' 25 = Z_to_bv 64 c1 /\ getr regs' 26 = Z_to_bv 64 c2 /\
(forall r : bv 5, r <> 10%bv -> r <> 20%bv -> r <> 25%bv -> r <> 26%bv -> getr regs' r = getr regs r).
Proof.
intros x y k c1 c2 Hx Hy Hxk Hyk Hbef Hc1 Hc2 Hr1 Hr2 Hstop.
induction d as [|d IH]; intros regs i Hd Hi G18 G9 G20.
- assert (Hik : i = k) by lia. subst i.
pose proof (sl_pass regs x y k c1 c2 G18 G9 G20 Hx Hy Hi ltac:(lia) ltac:(lia) Hc1 Hc2 Hr1 Hr2) as Hp.
pose proof (sl_regs_get regs x y k c1 c2) as (Q20 & Q25 & Q26 & QK).
exists (sl_regs regs x y k c1 c2). split; [|split; [exact Q20 | split; [exact Q25 | split; [exact Q26 | exact QK]]]].
eapply msteps_trans; [exact Hp|].
destruct (Z.eq_dec c1 0) as [Hz|Hnz].
+ eapply mst_step; [reflexivity | apply sl_nul_tk; rewrite Q25, Hz; reflexivity | apply mst_refl].
+ assert (Hne : c1 <> c2) by (destruct Hstop; [assumption | contradiction]).
eapply mst_step; [reflexivity | exact (sl_nul_ft _ c1 Q25 ltac:(lia)) |].
eapply mst_step; [reflexivity | exact (sl_eq_ft _ c1 c2 Q25 Q26 Hc1 Hc2 Hne) | apply mst_refl].
- destruct (Hbef i ltac:(lia)) as (b & Hb & Rx & Ry).
pose proof (sl_pass regs x y i b b G18 G9 G20 Hx Hy Hi ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Rx Ry) as Hp.
pose proof (sl_regs_get regs x y i b b) as (Q20 & Q25 & Q26 & QK).
destruct (IH (sl_regs regs x y i b b) (i + 1) ltac:(lia) ltac:(lia)) as (regs' & Hms & P20 & P25 & P26 & PK).
{ rewrite QK by discriminate. exact G18. }
{ rewrite QK by discriminate. exact G9. }
{ exact Q20. }
exists regs'. split; [|split; [exact P20 | split; [exact P25 | split; [exact P26 |]]]].
+ eapply msteps_trans; [exact Hp|].
eapply mst_step; [reflexivity | exact (sl_nul_ft _ b Q25 Hb) |].
eapply mst_step; [reflexivity | exact (sl_eq_tk _ b Q25 Q26) | exact Hms].
+ intros r H10 H20 H25 H26. rewrite (PK r H10 H20 H25 H26). exact (QK r H10 H20 H25 H26).
Qed.
Theorem strcmp_loop : forall x y k c1 c2, 0 <= x -> 0 <= y -> x + k + 1 <= 2 ^ 63 -> y + k + 1 <= 2 ^ 63 ->
(forall j, 0 <= j < k -> exists b, 0 < b < 256 /\
  rdn tfibsegs m (Z_to_bv 64 (x + j)) 1 = Some [Z_to_bv 8 b] /\ rdn tfibsegs m (Z_to_bv 64 (y + j)) 1 = Some [Z_to_bv 8 b]) ->
0 <= c1 < 256 -> 0 <= c2 < 256 ->
rdn tfibsegs m (Z_to_bv 64 (x + k)) 1 = Some [Z_to_bv 8 c1] -> rdn tfibsegs m (Z_to_bv 64 (y + k)) 1 = Some [Z_to_bv 8 c2] ->
(c1 <> c2 \/ c1 = 0) -> 0 <= k ->
forall regs, getr regs 18 = Z_to_bv 64 x -> getr regs 9 = Z_to_bv 64 y -> getr regs 20 = Z_to_bv 64 0 ->
exists regs', msteps tfibsegs (mkst regs (Z_to_bv 64 SL_HEAD) m rom) (mkst regs' (Z_to_bv 64 SL_EXIT) m rom) /\
getr regs' 20 = Z_to_bv 64 (k + 1) /\ getr regs' 25 = Z_to_bv 64 c1 /\ getr regs' 26 = Z_to_bv 64 c2 /\
(forall r : bv 5, r <> 10%bv -> r <> 20%bv -> r <> 25%bv -> r <> 26%bv -> getr regs' r = getr regs r).
Proof.
intros x y k c1 c2 Hx Hy Hxk Hyk Hbef Hc1 Hc2 Hr1 Hr2 Hstop Hk regs G18 G9 G20.
exact (sl_loop x y k c1 c2 Hx Hy Hxk Hyk Hbef Hc1 Hc2 Hr1 Hr2 Hstop (Z.to_nat k) regs 0 ltac:(lia) ltac:(lia) G18 G9 G20).
Qed.
End s.
