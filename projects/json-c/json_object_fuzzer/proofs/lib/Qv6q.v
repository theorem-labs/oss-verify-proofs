(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEqH GwApply GwApply2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Hd.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QAyu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QC8c.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPIU.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEQM.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QC8c.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBpZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBpZ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QT7i.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QT7i.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QzWc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QzWc.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply GwApply2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module GwI.
Definition segs := rsegs.
Definition base := 0x23338%Z.
Definition w_14 := 0x2692b0ef%Z.
Definition w_47 := 0x3c52e0ef%Z.
Definition w_70 := 0x6643a0ef%Z.
Definition joff_14 := (Z_to_bv 21 178792).
Definition joff_47 := (Z_to_bv 21 191428).
Definition joff_70 := (Z_to_bv 21 239204).
Definition e_194bc := 0x4edd8%Z.
Definition e_memmove := 0x5dab4%Z.
Lemma CODE : CodeAt.code_at rsegs 0x23338 (QPIU.Mqe.pbmemappend_code 0x2692b0ef%Z 0x3c52e0ef%Z 0x6643a0ef%Z).  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x23338 mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x23338 /\ 0x23338 + 356 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.

Local Notation gw_RC := Q6q3.RunConsts (only parsing).
Local Ltac gw_lay t := let v := eval cbv beta iota delta [QC8c.Mq0.S4L QCcH.hl_malloc QCcH.hl_free QCcH.hl_calloc QCcH.hl_realloc QCcH.hl_malloc2 QCcH.hl_free2 QCcH.hl_tp QCcH.hl_got_guard QCcH.hl_guard QCcH.hl_auxv QCcH.hl_libc QCcH.hl_img_lo QCcH.hl_img_hi QCcH.hl_consts] in t in lazymatch v with (fun _ => ?n) => exact n end.
Local Ltac gw_hex k := let v := eval cbv beta iota delta [QC8c.Mq0.S4L QCcH.hl_consts] in (fun RC__ : gw_RC => @QCcH.hl_consts RC__ (@QC8c.Mq0.S4L RC__)) in
lazymatch v with (fun _ => cons (pair ?a (?f1 (?f2 ?b))) (cons (pair _ (?f3 (?f4 ?c))) nil)) => lazymatch k with 0%nat => exact a | 1%nat => exact b | _ => exact c end end.
Definition e_malloc : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_malloc RC__ (@QC8c.Mq0.S4L RC__))).
Definition e_free : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_free RC__ (@QC8c.Mq0.S4L RC__))).
Definition e_calloc : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_calloc RC__ (@QC8c.Mq0.S4L RC__))).
Definition e_realloc : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_realloc RC__ (@QC8c.Mq0.S4L RC__))).
Definition e_malloc2 : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_malloc2 RC__ (@QC8c.Mq0.S4L RC__))).
Definition e_free2 : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_free2 RC__ (@QC8c.Mq0.S4L RC__))).
Definition gTP : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_tp RC__ (@QC8c.Mq0.S4L RC__))).
Definition gGOTG : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_got_guard RC__ (@QC8c.Mq0.S4L RC__))).
Definition gGUARD : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_guard RC__ (@QC8c.Mq0.S4L RC__))).
Definition gAUXV : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_auxv RC__ (@QC8c.Mq0.S4L RC__))).
Definition gLIBC : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_libc RC__ (@QC8c.Mq0.S4L RC__))).
Definition gIMG_LO : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_img_lo RC__ (@QC8c.Mq0.S4L RC__))).
Definition gIMG_HI : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_img_hi RC__ (@QC8c.Mq0.S4L RC__))).
Definition gHEXGOT : Z := ltac:(gw_hex 0%nat).  Definition gHEXPTR : Z := ltac:(gw_hex 1%nat).  Definition gHEXCHARS : Z := ltac:(gw_hex 2%nat).
Definition gVOL := QC8c.Mq0.s4_volatile.  Definition gCS := QC8c.Mq0.s4_client_static.
Definition gH1 := fun RC__ : gw_RC => @QCcH.hl_static_in_img RC__ (@QC8c.Mq0.S4L RC__).
Definition gH2 := fun RC__ : gw_RC => @QCcH.hl_img_range RC__ (@QC8c.Mq0.S4L RC__).
Definition gH3 := fun RC__ : gw_RC => @QCcH.hl_scratch_in_img RC__ (@QC8c.Mq0.S4L RC__).
Definition gH4 := fun RC__ : gw_RC => @QCcH.hl_scratch_not_static RC__ (@QC8c.Mq0.S4L RC__).
Definition gH5 := fun RC__ : gw_RC => @QCcH.hl_consts_ok RC__ (@QC8c.Mq0.S4L RC__).
Definition e_fn_obj_to_json_string := Eval cbv beta iota delta [Q0Ek.fn_obj_to_json_string QC8c.Mq0.S4F] in (Q0Ek.fn_obj_to_json_string QC8c.Mq0.S4F).
Definition e_fn_arr_to_json_string := Eval cbv beta iota delta [Q0Ek.fn_arr_to_json_string QC8c.Mq0.S4F] in (Q0Ek.fn_arr_to_json_string QC8c.Mq0.S4F).
Definition e_fn_bool_to_json_string := Eval cbv beta iota delta [Q0Ek.fn_bool_to_json_string QC8c.Mq0.S4F] in (Q0Ek.fn_bool_to_json_string QC8c.Mq0.S4F).
Definition e_fn_dbl_to_json_string := Eval cbv beta iota delta [Q0Ek.fn_dbl_to_json_string QC8c.Mq0.S4F] in (Q0Ek.fn_dbl_to_json_string QC8c.Mq0.S4F).
Definition e_fn_int_to_json_string := Eval cbv beta iota delta [Q0Ek.fn_int_to_json_string QC8c.Mq0.S4F] in (Q0Ek.fn_int_to_json_string QC8c.Mq0.S4F).
Definition e_fn_str_to_json_string := Eval cbv beta iota delta [Q0Ek.fn_str_to_json_string QC8c.Mq0.S4F] in (Q0Ek.fn_str_to_json_string QC8c.Mq0.S4F).
Definition e_fn_ud_to_json_string := Eval cbv beta iota delta [Q0Ek.fn_ud_to_json_string QC8c.Mq0.S4F] in (Q0Ek.fn_ud_to_json_string QC8c.Mq0.S4F).
Definition e_fn_free_userdata := Eval cbv beta iota delta [Q0Ek.fn_free_userdata QC8c.Mq0.S4F] in (Q0Ek.fn_free_userdata QC8c.Mq0.S4F).
Definition e_fn_lh_entry_free := Eval cbv beta iota delta [Q0Ek.fn_lh_entry_free QC8c.Mq0.S4F] in (Q0Ek.fn_lh_entry_free QC8c.Mq0.S4F).
Definition e_fn_lh_char_hash := Eval cbv beta iota delta [Q0Ek.fn_lh_char_hash QC8c.Mq0.S4F] in (Q0Ek.fn_lh_char_hash QC8c.Mq0.S4F).
Definition e_fn_lh_char_equal := Eval cbv beta iota delta [Q0Ek.fn_lh_char_equal QC8c.Mq0.S4F] in (Q0Ek.fn_lh_char_equal QC8c.Mq0.S4F).
Definition e_fn_arr_entry_free := Eval cbv beta iota delta [Q0Ek.fn_arr_entry_free QC8c.Mq0.S4F] in (Q0Ek.fn_arr_entry_free QC8c.Mq0.S4F).
Lemma CODE_e_194bc : CodeAt.code_at rsegs e_194bc QAyu.Mq5.blk_194bc_code.  Proof. StepGen.code_at_vm. Qed.
Definition pS4L := Eval cbv beta delta [Q0Hd.gl segs e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI] in
(fun RC__ : gw_RC => @Q0Hd.gl RC__ segs e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI (gH1 RC__) (gH2 RC__) (gH3 RC__) (gH4 RC__) (gH5 RC__)).
Definition pS4F := Eval cbv beta delta [Q0Hd.gf e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free] in
(Q0Hd.gf e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free).
End GwI.

Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PbMemappendTop.
Variable HIx : heap_iface S4L.
Hypothesis MEMMOVE : memmove_stmt.

Definition printbuf_memappend_entry : Z := 0x23338.

#[using="Type"] Lemma memappend_efbig :
forall (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 t3 t4 t5 t6 : word)
(m0 m : word -> option byte) (md : Model) (A : AS S4L HIx) (LB : list blk)
(pb buf bpos cap n lo : Z) (content src : list byte) (errv : word) (framejunk : list byte) (T : TSet),
HEAP S4L HIx A ((pb, PB_SZ) :: (buf, cap) :: LB) m md ->
pbuf_core rsegs m pb buf bpos cap content ->
stk rsegs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp + -64 ->
bv_unsigned sp <= hi_top S4L HIx ->
rw_cells rsegs m (bv_unsigned sp + -64) [CB 8 framejunk; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells rsegs m 482764 [C4 errv] ->
bv_unsigned ra mod 2 = 0 ->
heap_pres S4L LB (bv_unsigned sp) m0 m ->
(forall ms' md', memappend_post_c HIx ra sp gp (Z_to_bv 64 0x75e70) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md LB pb buf bpos cap content src n lo ms' md' ->
realizes rsegs (mkCfg ms' md') T) ->
realizes rsegs (mkCfg (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 0x75e70) t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x23370) fc None m (seg_rom rsegs)) md) T.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QAyu.Mq5.memappend_efbig) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QAyu.Mq5.memappend_efbig)]. Qed.

#[using="MEMMOVE"] Lemma memappend_cps_c :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS S4L HIx) (LB : list blk) (pb buf bpos cap b n lo : Z) (content src : list byte) (errv : word),
HEAP S4L HIx A ((pb, PB_SZ) :: (buf, cap) :: LB) m md ->
pbuf_core rsegs m pb buf bpos cap content ->
0 <= n < 2^31 ->
bytes_at rsegs m b src -> Z.of_nat (length src) = n -> src_cls LB n (bv_unsigned sp) b src ->
0 <= b -> b + n < 2^64 ->
(b + n <= buf \/ buf + cap <= b) ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 - 8256 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
rw_cells rsegs m (0x75e70 - 164) [C4 errv] ->
tp = Z_to_bv 64 0x75e70 -> bv_unsigned ra mod 2 = 0 ->
a0 = Z_to_bv 64 pb -> a1 = Z_to_bv 64 b -> a2 = Z_to_bv 64 n ->
(forall ms' md', memappend_post_c HIx ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB pb buf bpos cap content src n lo ms' md' ->
realizes rsegs (mkCfg ms' md') T) ->
realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 printbuf_memappend_entry) fc None m (seg_rom rsegs)) md) T.
Proof. first [ (pose proof MEMMOVE as gw_h_; clear MEMMOVE; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_memmove_stmt__3; @gw_eq_memmove_stmt__2; @gw_eq_memmove_stmt]]); rename gw_h_ into MEMMOVE) | idtac ]; first [GwApply2.gw_by_name2 GwI.segs (@QAyu.Mq5.memappend_cps_c) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QAyu.Mq5.memappend_cps_c)]. Qed.

#[using="MEMMOVE"] Lemma memappend_cps :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS S4L HIx) (LB : list blk) (pb buf bpos cap b n lo : Z) (content src : list byte) (errv : word),
HEAP S4L HIx A ((pb, PB_SZ) :: (buf, cap) :: LB) m md ->
pbuf_core rsegs m pb buf bpos cap content ->
0 <= n < 2^31 ->
bytes_at rsegs m b src -> Z.of_nat (length src) = n -> src_cls LB n (bv_unsigned sp) b src ->
0 <= b -> b + n < 2^64 ->
(b + n <= buf \/ buf + cap <= b) ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 - 8256 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
rw_cells rsegs m (0x75e70 - 164) [C4 errv] ->
tp = Z_to_bv 64 0x75e70 -> bv_unsigned ra mod 2 = 0 ->
a0 = Z_to_bv 64 pb -> a1 = Z_to_bv 64 b -> a2 = Z_to_bv 64 n ->
(forall ms' md', memappend_post HIx ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB pb buf bpos cap content n lo ms' md' ->
realizes rsegs (mkCfg ms' md') T) ->
realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 printbuf_memappend_entry) fc None m (seg_rom rsegs)) md) T.
Proof. first [ (pose proof MEMMOVE as gw_h_; clear MEMMOVE; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_memmove_stmt__3; @gw_eq_memmove_stmt__2; @gw_eq_memmove_stmt]]); rename gw_h_ into MEMMOVE) | idtac ]; first [GwApply2.gw_by_name2 GwI.segs (@QAyu.Mq5.memappend_cps) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QAyu.Mq5.memappend_cps)]. Qed.
End PbMemappendTop.

End RC__1.
