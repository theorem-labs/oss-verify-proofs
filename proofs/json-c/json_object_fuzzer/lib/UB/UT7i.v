(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEqH GwApply GwApply2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Hd.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Pb Require PbMemappend.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC8c.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UPIU.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UC8c.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UBpZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UBpZ.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UzWc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UzWc.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply GwApply2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module GwI.
Definition segs := rsegs.
Definition base := 0x241a4%Z.
Definition w_14 := 0x1652c0ef%Z.
Definition w_47 := 0x2992f0ef%Z.
Definition w_70 := 0x5043b0ef%Z.
Definition joff_14 := (Z_to_bv 21 182628).
Definition joff_47 := (Z_to_bv 21 195224).
Definition joff_70 := (Z_to_bv 21 242948).
Definition e_194bc := 0x50b60%Z.
Definition e_memmove := 0x5f83c%Z.
Lemma CODE : CodeAt.code_at rsegs 0x241a4 (UPIU.Mqe.pbmemappend_code 0x1652c0ef%Z 0x2992f0ef%Z 0x5043b0ef%Z).  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x241a4 mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x241a4 /\ 0x241a4 + 532 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.

Local Notation gw_RC := Q6q3.RunConsts (only parsing).
Local Ltac gw_lay t := let v := eval cbv beta iota delta [UC8c.Mq0.S4L QCcH.hl_malloc QCcH.hl_free QCcH.hl_calloc QCcH.hl_realloc QCcH.hl_malloc2 QCcH.hl_free2 QCcH.hl_tp QCcH.hl_got_guard QCcH.hl_guard QCcH.hl_auxv QCcH.hl_libc QCcH.hl_img_lo QCcH.hl_img_hi QCcH.hl_consts] in t in lazymatch v with (fun _ => ?n) => exact n end.
Local Ltac gw_hex k := let v := eval cbv beta iota delta [UC8c.Mq0.S4L QCcH.hl_consts] in (fun RC__ : gw_RC => @QCcH.hl_consts RC__ (@UC8c.Mq0.S4L RC__)) in
lazymatch v with (fun _ => cons (pair ?a (?f1 (?f2 ?b))) (cons (pair _ (?f3 (?f4 ?c))) nil)) => lazymatch k with 0%nat => exact a | 1%nat => exact b | _ => exact c end end.
Definition e_malloc : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_malloc RC__ (@UC8c.Mq0.S4L RC__))).
Definition e_free : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_free RC__ (@UC8c.Mq0.S4L RC__))).
Definition e_calloc : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_calloc RC__ (@UC8c.Mq0.S4L RC__))).
Definition e_realloc : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_realloc RC__ (@UC8c.Mq0.S4L RC__))).
Definition e_malloc2 : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_malloc2 RC__ (@UC8c.Mq0.S4L RC__))).
Definition e_free2 : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_free2 RC__ (@UC8c.Mq0.S4L RC__))).
Definition gTP : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_tp RC__ (@UC8c.Mq0.S4L RC__))).
Definition gGOTG : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_got_guard RC__ (@UC8c.Mq0.S4L RC__))).
Definition gGUARD : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_guard RC__ (@UC8c.Mq0.S4L RC__))).
Definition gAUXV : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_auxv RC__ (@UC8c.Mq0.S4L RC__))).
Definition gLIBC : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_libc RC__ (@UC8c.Mq0.S4L RC__))).
Definition gIMG_LO : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_img_lo RC__ (@UC8c.Mq0.S4L RC__))).
Definition gIMG_HI : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_img_hi RC__ (@UC8c.Mq0.S4L RC__))).
Definition gHEXGOT : Z := ltac:(gw_hex 0%nat).  Definition gHEXPTR : Z := ltac:(gw_hex 1%nat).  Definition gHEXCHARS : Z := ltac:(gw_hex 2%nat).
Definition gVOL := UC8c.Mq0.s4_volatile.  Definition gCS := UC8c.Mq0.s4_client_static.
Definition gH1 := fun RC__ : gw_RC => @QCcH.hl_static_in_img RC__ (@UC8c.Mq0.S4L RC__).
Definition gH2 := fun RC__ : gw_RC => @QCcH.hl_img_range RC__ (@UC8c.Mq0.S4L RC__).
Definition gH3 := fun RC__ : gw_RC => @QCcH.hl_scratch_in_img RC__ (@UC8c.Mq0.S4L RC__).
Definition gH4 := fun RC__ : gw_RC => @QCcH.hl_scratch_not_static RC__ (@UC8c.Mq0.S4L RC__).
Definition gH5 := fun RC__ : gw_RC => @QCcH.hl_consts_ok RC__ (@UC8c.Mq0.S4L RC__).
Definition e_fn_obj_to_json_string := Eval cbv beta iota delta [Q0Ek.fn_obj_to_json_string UC8c.Mq0.S4F] in (Q0Ek.fn_obj_to_json_string UC8c.Mq0.S4F).
Definition e_fn_arr_to_json_string := Eval cbv beta iota delta [Q0Ek.fn_arr_to_json_string UC8c.Mq0.S4F] in (Q0Ek.fn_arr_to_json_string UC8c.Mq0.S4F).
Definition e_fn_bool_to_json_string := Eval cbv beta iota delta [Q0Ek.fn_bool_to_json_string UC8c.Mq0.S4F] in (Q0Ek.fn_bool_to_json_string UC8c.Mq0.S4F).
Definition e_fn_dbl_to_json_string := Eval cbv beta iota delta [Q0Ek.fn_dbl_to_json_string UC8c.Mq0.S4F] in (Q0Ek.fn_dbl_to_json_string UC8c.Mq0.S4F).
Definition e_fn_int_to_json_string := Eval cbv beta iota delta [Q0Ek.fn_int_to_json_string UC8c.Mq0.S4F] in (Q0Ek.fn_int_to_json_string UC8c.Mq0.S4F).
Definition e_fn_str_to_json_string := Eval cbv beta iota delta [Q0Ek.fn_str_to_json_string UC8c.Mq0.S4F] in (Q0Ek.fn_str_to_json_string UC8c.Mq0.S4F).
Definition e_fn_ud_to_json_string := Eval cbv beta iota delta [Q0Ek.fn_ud_to_json_string UC8c.Mq0.S4F] in (Q0Ek.fn_ud_to_json_string UC8c.Mq0.S4F).
Definition e_fn_free_userdata := Eval cbv beta iota delta [Q0Ek.fn_free_userdata UC8c.Mq0.S4F] in (Q0Ek.fn_free_userdata UC8c.Mq0.S4F).
Definition e_fn_lh_entry_free := Eval cbv beta iota delta [Q0Ek.fn_lh_entry_free UC8c.Mq0.S4F] in (Q0Ek.fn_lh_entry_free UC8c.Mq0.S4F).
Definition e_fn_lh_char_hash := Eval cbv beta iota delta [Q0Ek.fn_lh_char_hash UC8c.Mq0.S4F] in (Q0Ek.fn_lh_char_hash UC8c.Mq0.S4F).
Definition e_fn_lh_char_equal := Eval cbv beta iota delta [Q0Ek.fn_lh_char_equal UC8c.Mq0.S4F] in (Q0Ek.fn_lh_char_equal UC8c.Mq0.S4F).
Definition e_fn_arr_entry_free := Eval cbv beta iota delta [Q0Ek.fn_arr_entry_free UC8c.Mq0.S4F] in (Q0Ek.fn_arr_entry_free UC8c.Mq0.S4F).
Lemma CODE_e_194bc : CodeAt.code_at rsegs e_194bc PbMemappend.Mq6.blk_194bc_code.  Proof. StepGen.code_at_vm. Qed.
Definition pS4L := Eval cbv beta delta [Q0Hd.gl segs e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI] in
(fun RC__ : gw_RC => @Q0Hd.gl RC__ segs e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI (gH1 RC__) (gH2 RC__) (gH3 RC__) (gH4 RC__) (gH5 RC__)).
Definition pS4F := Eval cbv beta delta [Q0Hd.gf e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free] in
(Q0Hd.gf e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free).
End GwI.

Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma lor_ones64_r : forall x, 0 <= x < 2^64 -> Z.lor x 18446744073709551615 = 18446744073709551615.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@PbMemappend.Mq6.lor_ones64_r) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@PbMemappend.Mq6.lor_ones64_r)]. Qed.
#[using="Type"] Lemma lor_ones64_l : forall x, 0 <= x < 2^64 -> Z.lor 18446744073709551615 x = 18446744073709551615.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@PbMemappend.Mq6.lor_ones64_l) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@PbMemappend.Mq6.lor_ones64_l)]. Qed.
#[using="Type"] Lemma v_sltu_1 : forall x y : word, bv_unsigned x < bv_unsigned y -> v_sltu x y = Z_to_bv 64 1.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@PbMemappend.Mq6.v_sltu_1) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@PbMemappend.Mq6.v_sltu_1)]. Qed.
#[using="Type"] Lemma v_sltu_0 : forall x y : word, bv_unsigned y <= bv_unsigned x -> v_sltu x y = Z_to_bv 64 0.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@PbMemappend.Mq6.v_sltu_0) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@PbMemappend.Mq6.v_sltu_0)]. Qed.
#[using="Type"] Lemma unsigned_m1 : bv_unsigned (Z_to_bv 64 (-1)) = 18446744073709551615.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@PbMemappend.Mq6.unsigned_m1) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@PbMemappend.Mq6.unsigned_m1)]. Qed.

Section PbMemappendMain.
Variable HIx : heap_iface S4L.
Hypothesis MEMMOVE : memmove_stmt.
Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : Model) (LB : list blk) (lo : Z) (pb n : Z) (T : TSet).

Definition src_cls (SP b : Z) (src : list byte) : Prop :=
client_range S4L LB SP b n \/ ro_bytes rsegs b src.

Local Definition gwt_X : unit := (Q6nq.gwt_pat GwI.pS4L (@UC8c.Mq0.S4L) (Q6nq.gwt_pat GwI.pS4F UC8c.Mq0.S4F Q6nq.gwt_nil)).
#[using="Type"] Lemma src_cls_transport : ltac2:(Q6nq.ty2 'GwI.segs '(@PbMemappend.Mq6.src_cls_transport) [] '(@nil Z) '(Q6nq.gwt_def (@PbMemappend.Mq6.src_cls) (@src_cls) gwt_X)).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@PbMemappend.Mq6.src_cls_transport) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@PbMemappend.Mq6.src_cls_transport)]. Qed.

#[using="MEMMOVE"] Lemma memappend_rebase :
forall (buf0 bpos0 cap0 : Z) (content0 : list byte) (x1 t0 t1 t2 x9 a0 a2 a4 a5 a6 a7 x19 x20 x21 t3 t4 t5 t6 : word)
(m : word -> option byte) (md : Model) (A : AS S4L HIx)
(obuf ocap buf bpos cap b : Z) (content src : list byte) (errv : word) (framejunk : list byte),
HEAP S4L HIx A ((pb, PB_SZ) :: (buf, cap) :: LB) m md ->
pbufx m pb buf bpos cap content ->
bpos + n + 1 <= cap -> 0 <= n < 2^31 ->
bytes_at rsegs m b src -> Z.of_nat (length src) = n ->
0 <= b < 2^64 -> b + n <= 2^64 ->
(b + n <= obuf \/ obuf + ocap <= b) -> 0 <= obuf -> obuf + ocap <= 2^64 -> 0 < ocap < 2^31 ->
a0 = Z_to_bv 64 pb -> a2 = Z_to_bv 64 n ->
stk rsegs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp + -64 - 8256 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
rw_cells rsegs m (bv_unsigned sp + -64) [CB 8 framejunk; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells rsegs m (0x77c00 - 164) [C4 errv] ->
bv_unsigned ra mod 2 = 0 ->
model_vm_only md0 md -> heap_pres S4L LB (bv_unsigned sp) m0 m ->
bpos = bpos0 -> firstn (Z.to_nat bpos) content = firstn (Z.to_nat bpos0) content0 ->
(forall ms' md', memappend_post_c HIx ra sp gp (Z_to_bv 64 0x77c00) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB pb buf0 bpos0 cap0 content0 src n lo ms' md' ->
realizes rsegs (mkCfg ms' md') T) ->
realizes rsegs (mkCfg (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 0x77c00) t0 t1 t2 (Z_to_bv 64 obuf) x9 a0 (Z_to_bv 64 b) a2 (Z_to_bv 64 buf) a4 a5 a6 a7 (Z_to_bv 64 ocap) x19 x20 x21 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x242c8) fc None m (seg_rom rsegs)) md) T.
Proof. first [ (pose proof MEMMOVE as gw_h_; clear MEMMOVE; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_memmove_stmt__3; @gw_eq_memmove_stmt__2; @gw_eq_memmove_stmt]]); rename gw_h_ into MEMMOVE) | idtac ]; first [GwApply2.gw_by_name2 GwI.segs (@PbMemappend.Mq6.memappend_rebase) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@PbMemappend.Mq6.memappend_rebase)]. Qed.

#[using="MEMMOVE"] Lemma memappend_grow :
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
(m : word -> option byte) (md : Model) (A : AS S4L HIx)
(buf bpos cap ns b : Z) (content src : list byte) (errv : word) (framejunk : list byte),
HEAP S4L HIx A ((pb, PB_SZ) :: (buf, cap) :: LB) m md ->
pbufx m pb buf bpos cap content ->
bpos + n + 1 <= ns -> cap <= ns < 2^31 -> 0 <= n < 2^31 ->
bytes_at rsegs m b src -> Z.of_nat (length src) = n -> src_cls (bv_unsigned sp) b src ->
0 <= b < 2^64 -> b + n <= 2^64 ->
(b + n <= buf \/ buf + cap <= b) ->
stk rsegs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp + -64 - 8256 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
rw_cells rsegs m (bv_unsigned sp + -64) [CB 8 framejunk; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells rsegs m (0x77c00 - 164) [C4 errv] ->
bv_unsigned ra mod 2 = 0 ->
model_vm_only md0 md -> heap_pres S4L LB (bv_unsigned sp) m0 m ->
(forall ms' md', memappend_post_c HIx ra sp gp (Z_to_bv 64 0x77c00) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB pb buf bpos cap content src n lo ms' md' ->
realizes rsegs (mkCfg ms' md') T) ->
realizes rsegs (mkCfg (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 0x77c00) t0 t1 t2 (Z_to_bv 64 buf) (Z_to_bv 64 ns) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 cap) (Z_to_bv 64 b) (Z_to_bv 64 n) (Z_to_bv 64 pb) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x242a0) fc None m (seg_rom rsegs)) md) T.
Proof. first [ (pose proof MEMMOVE as gw_h_; clear MEMMOVE; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_memmove_stmt__3; @gw_eq_memmove_stmt__2; @gw_eq_memmove_stmt]]); rename gw_h_ into MEMMOVE) | idtac ]; first [GwApply2.gw_by_name2 GwI.segs (@PbMemappend.Mq6.memappend_grow) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@PbMemappend.Mq6.memappend_grow)]. Qed.
End PbMemappendMain.

End RC__1.
