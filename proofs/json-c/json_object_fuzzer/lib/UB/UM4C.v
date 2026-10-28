(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq GwEqH GwApply. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSsB.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qfw3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qc3B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc3B. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QlEo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QsjA.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QqdR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqdR. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QYTG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYTG.Mq2.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QnDM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnDM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UjdK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UjdK. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U4l4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U4l4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UxrO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UxrO. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Um2h.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Um2h. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UDgQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UDgQ.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q8Ie.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8Ie.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UzOj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UzOj.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSCw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSCw. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qbz7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qbz7.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UTru.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UTru. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U3Uw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U3Uw.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UrBC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UrBC. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UeSv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UeSv. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UwP2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UwP2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U0Ae.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U0Ae. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UTa4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UTa4.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qfw3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3.Mq1.
Import ListNotations.
Import QlEo.Mq0.Exc. Unset Keyed Unification. Local Ltac Q2qa.Mq0.sf_vocab ::= Q2qa.Mq0.mkr__sf_vocab_5. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Open Scope mspec_scope.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module GwI.
Definition segs := rsegs.
Definition base := 0x5514c%Z.
Definition w_4 := 0x00011897%Z.
Definition w_5 := 0x8748b403%Z.
Definition w_15 := 0x525040ef%Z.
Definition w_23 := 0xe7dfb0ef%Z.
Definition hi_4 := (Z_to_bv 20 17).
Definition lo_5 := (Z_to_bv 12 2164).
Definition joff_15 := (Z_to_bv 21 19748).
Definition joff_23 := (Z_to_bv 21 2080380).
Definition got_ssp := got_ssp.
Definition GLOBALS_TOP := GLOBALS_TOP.
Definition STATIC_SPLIT := STATIC_SPLIT.
Definition ssp_guard := ssp_guard.
Definition e_197bc := 0x51024%Z.
Definition e_vsnprintf := 0x59eac%Z.
Definition e_sn_write := 0x59f78%Z.
Definition e_memset := 0x5f9b8%Z.
Lemma CODE : CodeAt.code_at rsegs 0x5514c (QSsB.Mq5.snprintf_code 0x00011897%Z 0x8748b403%Z 0x525040ef%Z 0xe7dfb0ef%Z).  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x5514c mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x5514c /\ 0x5514c + 96 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.
Definition args_ok_nos := ltac:(pose proof (@args_ok_nos) as gw_h_; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_no_s__3; @gw_eq_no_s__2; @gw_eq_no_s]; [@gw_eq_VSN_FRAME__3; @gw_eq_VSN_FRAME__2; @gw_eq_VSN_FRAME]; [@gw_eq_VSN_DEPTH__3; @gw_eq_VSN_DEPTH__2; @gw_eq_VSN_DEPTH]; [@gw_eq_vsnprintf_post__3; @gw_eq_vsnprintf_post__2; @gw_eq_vsnprintf_post]; [@gw_eq_vsnprintf_stmt__3; @gw_eq_vsnprintf_stmt__2; @gw_eq_vsnprintf_stmt]]); exact gw_h_).
Definition vsnprintf_proof := ltac:(pose proof (@vsnprintf_proof) as gw_h_; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_no_s__3; @gw_eq_no_s__2; @gw_eq_no_s]; [@gw_eq_VSN_FRAME__3; @gw_eq_VSN_FRAME__2; @gw_eq_VSN_FRAME]; [@gw_eq_VSN_DEPTH__3; @gw_eq_VSN_DEPTH__2; @gw_eq_VSN_DEPTH]; [@gw_eq_vsnprintf_post__3; @gw_eq_vsnprintf_post__2; @gw_eq_vsnprintf_post]; [@gw_eq_vsnprintf_stmt__3; @gw_eq_vsnprintf_stmt__2; @gw_eq_vsnprintf_stmt]]); exact gw_h_).
End GwI.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs. Local Ltac mkr__transport_chunks_0 segs m a bs := transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs. Local Ltac mkr__footprint_after_store_1 segs m a bs := footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast. Local Ltac mkr__mem_after_store_2 := mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM. Local Ltac mkr__transport_after_call_3 segs m m' MU WM := transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= lia3. Local Ltac mkr__lia_4 := lia3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac fix_ret := lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.

Definition snprintf_entry : Z := 0x5514c.
Lemma gw_eq_snprintf_entry : @snprintf_entry = ltac:(GwInst.gw_term (@QSsB.Mq5.snprintf_entry 0x5514c) (@snprintf_entry)). Proof. unfold snprintf_entry, QSsB.Mq5.snprintf_entry; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_snprintf_entry : gw_eqs.

Definition SNPRINTF_DEPTH : Z := 5936.
Lemma gw_eq_SNPRINTF_DEPTH : @SNPRINTF_DEPTH = ltac:(GwInst.gw_term (@QSsB.Mq5.SNPRINTF_DEPTH) (@SNPRINTF_DEPTH)). Proof. unfold SNPRINTF_DEPTH, QSsB.Mq5.SNPRINTF_DEPTH; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_SNPRINTF_DEPTH : gw_eqs.

Definition snprintf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
(D : Z) (dn : nat) (o : list Z) (r : Z) (junkd : list byte) (lo : Z) (canary : word) (m : mem) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (ret_pc ra) fc' None m' (seg_rom rsegs)
/\ munch [(lo, bv_unsigned sp); (D, D + Z.of_nat dn)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ frm0 fc'
/\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
/\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' D [CB dn (zb o ++ Z_to_bv 8 0 :: skipn (S (length o)) junkd)]
/\ ssp_cells m' canary.
Lemma gw_eq_snprintf_post : @snprintf_post = ltac:(GwInst.gw_term (@QSsB.Mq5.snprintf_post rsegs got_ssp ssp_guard) (@snprintf_post)). Proof. unfold snprintf_post, QSsB.Mq5.snprintf_post; ltac2:(GwEq.gw_rw [[@gw_eq_ssp_cells__3; @gw_eq_ssp_cells__2; @gw_eq_ssp_cells]; [@gw_eq_zb__3; @gw_eq_zb__2; @gw_eq_zb]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_snprintf_post : gw_eqs.

Definition snprintf_gen_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(n A : Z) (dn : nat) (junkd : list byte) (fmt : list Z) (args : list parg)
(lo : Z) (canary : word) (r : Z) (o : list Z),
let q := bv_unsigned sp in let D := bv_unsigned a0 in
a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 A ->
rw_cells rsegs m D [CB dn junkd] ->
bytes_at rsegs m A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
Forall no_s args -> args_ok 0 0 0 m lo q 0 [a3; a4; a5; a6; a7] args ->
printf_model OUT_sn OUTFP_sn fmt args [] = QlEo.Mq0.Ret (Ok (r, o)) ->
Forall (fun c => let '(y, w, p, fl, t) := c in fmt_fp_facts y fl p t) (fp_calls (length fmt) fmt args) ->
(length o < dn)%nat -> (zlength o <= n - 1) -> (1 <= n < 2^63) ->
stk rsegs m lo q -> (lo <= q - SNPRINTF_DEPTH) -> (GLOBALS_TOP <= lo) -> (q < 2^63) ->
ssp_cells m canary -> mem_inv rsegs m -> frm0 fc ->
(65536 <= A) -> (A + zlength fmt <= STATIC_SPLIT) ->
(D + Z.of_nat dn <= lo \/ q <= D) -> (D + Z.of_nat dn <= 65536 \/ GLOBALS_TOP <= D) ->
evt rsegs (snprintf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F D dn o r junkd lo canary m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 snprintf_entry) fc None m (seg_rom rsegs)).
Lemma gw_eq_snprintf_gen_stmt : @snprintf_gen_stmt = ltac:(GwInst.gw_term (@QSsB.Mq5.snprintf_gen_stmt rsegs 0x5514c got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) (@snprintf_gen_stmt)). Proof. unfold snprintf_gen_stmt, QSsB.Mq5.snprintf_gen_stmt; rewrite ?gw_eq_snprintf_entry, ?gw_eq_SNPRINTF_DEPTH, ?gw_eq_snprintf_post; ltac2:(GwEq.gw_rw [[@gw_eq_OUTFP_sn__3; @gw_eq_OUTFP_sn__2; @gw_eq_OUTFP_sn]; [@gw_eq_OUT_sn__3; @gw_eq_OUT_sn__2; @gw_eq_OUT_sn]; [@gw_eq_args_ok__3; @gw_eq_args_ok__2; @gw_eq_args_ok]; [@gw_eq_fmt_fp_facts__3; @gw_eq_fmt_fp_facts__2; @gw_eq_fmt_fp_facts]; [@gw_eq_fp_calls__3; @gw_eq_fp_calls__2; @gw_eq_fp_calls]; [@gw_eq_no_s__3; @gw_eq_no_s__2; @gw_eq_no_s]; [@gw_eq_pass1_ok__3; @gw_eq_pass1_ok__2; @gw_eq_pass1_ok]; [@gw_eq_printf_model__3; @gw_eq_printf_model__2; @gw_eq_printf_model]; [@gw_eq_ssp_cells__3; @gw_eq_ssp_cells__2; @gw_eq_ssp_cells]; [@gw_eq_zb__3; @gw_eq_zb__2; @gw_eq_zb]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_snprintf_gen_stmt : gw_eqs.

Lemma rwc_eq' : forall m A A' cs, rw_cells rsegs m A cs -> A = A' -> rw_cells rsegs m A' cs.
Proof. first [GwApply.gw_by_name GwI.segs (@QSsB.Mq5.rwc_eq') | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QSsB.Mq5.rwc_eq')]. Qed.

Theorem snprintf_gen_proof : snprintf_gen_stmt.
Proof. rewrite ?gw_eq_snprintf_gen_stmt; first [GwApply.gw_by_name GwI.segs (@QSsB.Mq5.snprintf_gen_proof) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QSsB.Mq5.snprintf_gen_proof)]. Qed.
