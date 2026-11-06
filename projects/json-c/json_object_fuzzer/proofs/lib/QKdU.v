(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbFI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZsi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZsi.Mq1.
Import ListNotations. Unset Keyed Unification.
Open Scope Z_scope.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition set_shadow_f5_entry : Z := 0x659d0.
Definition got_real_memset : Z := 0xe81d8.
Definition real_memset_cell : Z := 0xea1d0.

Lemma set_shadow_f5_raw : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (dst n : Z) (junk : list byte),
ro_cells asegs m got_real_memset [C8 (Z_to_bv 64 real_memset_cell)] ->
ro_cells asegs m real_memset_cell [C8 (Z_to_bv 64 memset_entry)] ->
a0 = Z_to_bv 64 dst -> a1 = Z_to_bv 64 n -> 0 <= dst -> dst + n < 2^64 -> 0 <= n ->
rw_cells asegs m dst [CB (Z.to_nat n) junk] -> mem_inv asegs m ->
evt asegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0 a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(dst, dst + n)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ rw_cells asegs m' dst [CB (Z.to_nat n) (repeat (Z_to_bv 8 245) (Z.to_nat n))])
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 set_shadow_f5_entry) fc None m (seg_rom asegs)).
Proof.
intros until junk; intros GOT CELL -> -> Hd Hdn Hn RC MI.
pose proof (rw_cells_bound asegs m dst _ RC) as B. cbn [cells_size csize Nat.add] in B.
unfold set_shadow_f5_entry, got_real_memset, real_memset_cell, memset_entry in *.
pose proof (munch_refl [(dst, dst + n)] m) as MU. pose proof (wmono_refl asegs m) as WM.
step. step. step. step. step. step.
eapply evt_mono.
- eapply (memset_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ junk); [| exact MI].
rewrite !unsigned_lit by lia. exact RC.
- cbv beta. unfold memset_post. intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU' & WM' & MI' & RC').
rewrite !unsigned_lit in MU', RC' by lia. change (245 mod 256) with 245 in RC'.
do 15 eexists. split; [reflexivity|]. split; [exact MU'|]. split; [exact WM'|]. split; [exact MI'|]. exact RC'.
Qed.

Lemma set_shadow_f5_A : forall (HIx : heap_iface_A A4L) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (Bu : bud)
(dst n : Z) (junk : list byte),
HEAPA A4L HIx A LB LM FRS Bu m md ->
a0 = Z_to_bv 64 dst -> a1 = Z_to_bv 64 n -> 0 <= dst -> dst + n < 2^64 -> 0 <= n ->
rw_cells asegs m dst [CB (Z.to_nat n) junk] ->
evt asegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0 a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(dst, dst + n)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ rw_cells asegs m' dst [CB (Z.to_nat n) (repeat (Z_to_bv 8 245) (Z.to_nat n))])
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 set_shadow_f5_entry) fc None m (seg_rom asegs)).
Proof.
intros until junk; intros HP Ha0 Ha1 Hd Hdn Hn RC.
pose proof (heapA_rtc A4L HIx _ _ _ _ _ _ _ HP) as RTC. rewrite Forall_forall in RTC.
assert (GOT : bytes_at asegs m got_real_memset (le8 (Z_to_bv 64 real_memset_cell))).
{ refine (RTC (0xe81d8, le8 (Z_to_bv 64 0xea1d0)) _). cbn [hl_rt_consts A4L]. unfold a4_rt_consts. repeat (first [left; reflexivity | right]). }
assert (CELL : bytes_at asegs m real_memset_cell (le8 (Z_to_bv 64 memset_entry))).
{ refine (RTC (0xea1d0, le8 (Z_to_bv 64 0xdde14)) _). cbn [hl_rt_consts A4L]. unfold a4_rt_consts. repeat (first [left; reflexivity | right]). }
eapply set_shadow_f5_raw; [apply ro_C8_of_bytes_at; exact GOT | apply ro_C8_of_bytes_at; exact CELL | exact Ha0 | exact Ha1 | exact Hd | exact Hdn | exact Hn | exact RC |].
exact (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP).
Qed.
End RC__1.
