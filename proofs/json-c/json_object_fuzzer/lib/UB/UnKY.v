(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq GwApply. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QROt.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QQRC.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QfYR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfYR. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QfcC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfcC.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.SepCache.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QnDM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnDM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9Ay.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ay.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U4l4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U4l4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UzHs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UzHs. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UuJ9.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UuJ9.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uoo0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Export Uoo0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
Import ListNotations. Unset Keyed Unification.
Open Scope Z_scope.
Open Scope bv_scope.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module GwI.
Definition segs := rsegs.
Definition base := 0x5b640%Z.
Definition w_71 := 0x0000a517%Z.
Definition w_72 := 0x27453903%Z.
Definition w_98 := 0x85df50ef%Z.
Definition hi_71 := (Z_to_bv 20 10).
Definition lo_72 := (Z_to_bv 12 628).
Definition joff_98 := (Z_to_bv 21 2054236).
Definition got_ssp := got_ssp.
Definition STRING_READ := STRING_READ.
Definition ssp_guard := ssp_guard.
Definition e_197bc := 0x51024%Z.
Definition e_memcpy := 0x5f438%Z.
Definition e_memchr := 0x5f33c%Z.
Lemma CODE : CodeAt.code_at rsegs 0x5b640 (QQRC.Mq3.shgetc_code 0x0000a517%Z 0x27453903%Z 0x85df50ef%Z).  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x5b640 mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x5b640 /\ 0x5b640 + 544 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.
End GwI.

Ltac hyp :=
lazymatch goal with
| |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
| |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
end.
Ltac hyp_cells :=
lazymatch goal with |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ m A ?cs' |- _ => replace cs with cs' by (repeat (reflexivity || f_equal); lia); exact H end
end.

Definition uflow_res (txt : list Z) (off p : Z) : Z := if (off <? p)%Z then znth txt off else -1.
Lemma gw_eq_uflow_res : @uflow_res = ltac:(GwInst.gw_term (@QROt.Mq2.uflow_res) (@uflow_res)). Proof. unfold uflow_res, QROt.Mq2.uflow_res; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_uflow_res : gw_eqs.

Definition uflow_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(Fp T p off : Z) (txt : list Z) (shend : Z) (shl shc canary : word) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (uflow_res txt off p)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(q - 128, q); (Fp, Fp + 232)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' (q - 128) (q)
/\ rw_cells rsegs m' Fp (ss_cells T (T + off + sread_len off p) (T + p) (Z_to_bv 64 M64) (T + p) shend shl shc)
/\ bytes_at rsegs m' T (zbytes txt)
/\ ssp_cells m' canary.
Lemma gw_eq_uflow_post : @uflow_post = ltac:(GwInst.gw_term (@QROt.Mq2.uflow_post rsegs got_ssp STRING_READ ssp_guard) (@uflow_post)). Proof. unfold uflow_post, QROt.Mq2.uflow_post; rewrite ?gw_eq_uflow_res; ltac2:(GwEq.gw_rw [[@gw_eq_M64__3; @gw_eq_M64__2; @gw_eq_M64]; [@gw_eq_sread_len__3; @gw_eq_sread_len__2; @gw_eq_sread_len]; [@gw_eq_ss_cells__3; @gw_eq_ss_cells__2; @gw_eq_ss_cells]; [@gw_eq_ssp_cells__3; @gw_eq_ssp_cells__2; @gw_eq_ssp_cells]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_uflow_post : gw_eqs.

Definition uflow_stmt : Prop :=
forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Fp T p off rpos rend shend : Z) (txt pre post : list Z) (mode shl shc canary : word),
rw_cells rsegs m Fp (ss_cells T rpos rend mode (T + off) shend shl shc) ->
(mode = Z_to_bv 64 0 \/ mode = Z_to_bv 64 M64) ->
rtext T txt pre post -> p = zlength pre -> (0 <= off <= p)%Z ->
bytes_at rsegs m T (zbytes txt) -> ssp_cells m canary ->
(4096 <= T)%Z -> (T + 2^41 <= 2^63)%Z -> (0 <= rpos < 2^64)%Z -> (0 <= rend < 2^64)%Z -> (0 <= shend < 2^64)%Z ->
(Fp + 232 <= T \/ T + zlength txt <= Fp)%Z ->
stk rsegs m (q - 128) (q) -> (4096 <= q - 128)%Z -> (q <= Fp)%Z -> (Fp + 232 <= 2^63)%Z ->
(T + zlength txt <= q - 128 \/ q <= T)%Z ->
(ssp_guard + 8 <= q - 128)%Z ->
(T + zlength txt <= got_ssp \/ got_ssp + 8 <= T)%Z -> (T + zlength txt <= ssp_guard \/ ssp_guard + 8 <= T)%Z ->
(0 <= q)%Z -> (q < 2^63)%Z ->
mem_inv rsegs m ->
evt rsegs (uflow_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp T p off txt shend shl shc canary m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 UFLOW) fc None m (seg_rom rsegs)).
Lemma gw_eq_uflow_stmt : @uflow_stmt = ltac:(GwInst.gw_term (@QROt.Mq2.uflow_stmt rsegs 0x5b640 got_ssp STRING_READ ssp_guard) (@uflow_stmt)). Proof. unfold uflow_stmt, QROt.Mq2.uflow_stmt; rewrite ?gw_eq_uflow_post; ltac2:(GwEq.gw_rw [[@gw_eq_M64__3; @gw_eq_M64__2; @gw_eq_M64]; [@gw_eq_UFLOW__3; @gw_eq_UFLOW__2; @gw_eq_UFLOW]; [@gw_eq_rtext__3; @gw_eq_rtext__2; @gw_eq_rtext]; [@gw_eq_ss_cells__3; @gw_eq_ss_cells__2; @gw_eq_ss_cells]; [@gw_eq_ssp_cells__3; @gw_eq_ssp_cells__2; @gw_eq_ssp_cells]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_uflow_stmt : gw_eqs.

Definition shgetc_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(Fp T p : Z) (f : shfile) (txt : list Z) (canary : word) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (fst (sh_getc f))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(q - 160, q); (Fp, Fp + 232)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' (q - 160) q
/\ rw_cells rsegs m' Fp (rf_cells T p true (snd (sh_getc f)) ssJ)
/\ bytes_at rsegs m' T (zbytes txt)
/\ ssp_cells m' canary.
Lemma gw_eq_shgetc_post : @shgetc_post = ltac:(GwInst.gw_term (@QROt.Mq2.shgetc_post rsegs got_ssp STRING_READ ssp_guard) (@shgetc_post)). Proof. unfold shgetc_post, QROt.Mq2.shgetc_post; ltac2:(GwEq.gw_rw [[@gw_eq_rf_cells__3; @gw_eq_rf_cells__2; @gw_eq_rf_cells]; [@gw_eq_ssJ__3; @gw_eq_ssJ__2; @gw_eq_ssJ]; [@gw_eq_ssp_cells__3; @gw_eq_ssp_cells__2; @gw_eq_ssp_cells]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_shgetc_post : gw_eqs.

Definition shgetc_stmt : Prop :=
forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Fp T p : Z) (w : bool) (f : shfile) (txt pre post : list Z) (canary : word),
rw_cells rsegs m Fp (rf_cells T p w f ssJ) ->
sh_stdio f = true -> sh_n f = p -> sh_buf f = txt ->
sh_rpos f = (if w then p else 0%Z) -> (w = false -> sh_cnt0 f = 0%Z /\ sh_shlim_neg f = false) -> (0 <= sh_cnt0 f <= sh_rpos f)%Z ->
rtext T txt pre post -> p = zlength pre -> bytes_at rsegs m T (zbytes txt) -> ssp_cells m canary ->
(4096 <= T)%Z -> (T + 2^41 <= 2^63)%Z -> (Fp + 232 <= T \/ T + zlength txt <= Fp)%Z ->
stk rsegs m (q - 160) q -> (4096 <= q - 160)%Z -> (q <= Fp)%Z -> (Fp + 232 <= 2^63)%Z ->
(T + zlength txt <= q - 160 \/ q <= T)%Z ->
(ssp_guard + 8 <= q - 160)%Z ->
(T + zlength txt <= got_ssp \/ got_ssp + 8 <= T)%Z -> (T + zlength txt <= ssp_guard \/ ssp_guard + 8 <= T)%Z ->
(0 <= q)%Z -> (q < 2^63)%Z ->
mem_inv rsegs m ->
evt rsegs (shgetc_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp T p f txt canary m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 SHGETC) fc None m (seg_rom rsegs)).
Lemma gw_eq_shgetc_stmt : @shgetc_stmt = ltac:(GwInst.gw_term (@QROt.Mq2.shgetc_stmt rsegs 0x5b640 got_ssp STRING_READ ssp_guard) (@shgetc_stmt)). Proof. unfold shgetc_stmt, QROt.Mq2.shgetc_stmt; rewrite ?gw_eq_shgetc_post; ltac2:(GwEq.gw_rw [[@gw_eq_SHGETC__3; @gw_eq_SHGETC__2; @gw_eq_SHGETC]; [@gw_eq_rf_cells__3; @gw_eq_rf_cells__2; @gw_eq_rf_cells]; [@gw_eq_rtext__3; @gw_eq_rtext__2; @gw_eq_rtext]; [@gw_eq_ssJ__3; @gw_eq_ssJ__2; @gw_eq_ssJ]; [@gw_eq_ssp_cells__3; @gw_eq_ssp_cells__2; @gw_eq_ssp_cells]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_shgetc_stmt : gw_eqs.

