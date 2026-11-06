(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply GwApply2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Hd.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRGY.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QC8c.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPZI.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qazd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qazd.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QC8c.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8tj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8tj.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSL3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSL3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnCn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnCn.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.

Module GwI.
Definition segs := usegs.
Definition base := 0x28330%Z.
Definition w_7 := 0x0003e597%Z.
Definition w_8 := 0x6ec5b903%Z.
Definition w_12 := 0x41d290ef%Z.
Definition w_21 := 0x3f9290ef%Z.
Definition w_26 := 0x0003d617%Z.
Definition w_27 := 0x54863603%Z.
Definition w_45 := 0x4d1290ef%Z.
Definition hi_7 := (Z_to_bv 20 62).
Definition hi_26 := (Z_to_bv 20 61).
Definition lo_8 := (Z_to_bv 12 1772).
Definition lo_27 := (Z_to_bv 12 1352).
Definition joff_12 := (Z_to_bv 21 171036).
Definition joff_21 := (Z_to_bv 21 171000).
Definition joff_45 := (Z_to_bv 21 171216).
Definition JG_CGT_P := Eval cbv in QPZI.Mq0.JG_CGT_U.
Lemma CODE : CodeAt.code_at usegs 0x28330 (QRGY.ulhnew_code 0x0003e597%Z 0x6ec5b903%Z 0x41d290ef%Z 0x3f9290ef%Z 0x0003d617%Z 0x54863603%Z 0x4d1290ef%Z).  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x28330 mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x28330 /\ 0x28330 + 220 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.

Local Notation gw_RC := Q6q3.RunConsts (only parsing).
Local Ltac gw_lay t := let v := eval cbv beta iota delta [QC8c.U4L QCcH.hl_malloc QCcH.hl_free QCcH.hl_calloc QCcH.hl_realloc QCcH.hl_malloc2 QCcH.hl_free2 QCcH.hl_tp QCcH.hl_got_guard QCcH.hl_guard QCcH.hl_auxv QCcH.hl_libc QCcH.hl_img_lo QCcH.hl_img_hi QCcH.hl_consts] in t in lazymatch v with (fun _ => ?n) => exact n end.
Local Ltac gw_hex k := let v := eval cbv beta iota delta [QC8c.U4L QCcH.hl_consts] in (fun RC__ : gw_RC => @QCcH.hl_consts RC__ (@QC8c.U4L RC__)) in
lazymatch v with (fun _ => cons (pair ?a (?f1 (?f2 ?b))) (cons (pair _ (?f3 (?f4 ?c))) nil)) => lazymatch k with 0%nat => exact a | 1%nat => exact b | _ => exact c end end.
Definition e_malloc : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_malloc RC__ (@QC8c.U4L RC__))).
Definition e_free : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_free RC__ (@QC8c.U4L RC__))).
Definition e_calloc : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_calloc RC__ (@QC8c.U4L RC__))).
Definition e_realloc : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_realloc RC__ (@QC8c.U4L RC__))).
Definition e_malloc2 : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_malloc2 RC__ (@QC8c.U4L RC__))).
Definition e_free2 : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_free2 RC__ (@QC8c.U4L RC__))).
Definition gTP : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_tp RC__ (@QC8c.U4L RC__))).
Definition gGOTG : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_got_guard RC__ (@QC8c.U4L RC__))).
Definition gGUARD : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_guard RC__ (@QC8c.U4L RC__))).
Definition gAUXV : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_auxv RC__ (@QC8c.U4L RC__))).
Definition gLIBC : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_libc RC__ (@QC8c.U4L RC__))).
Definition gIMG_LO : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_img_lo RC__ (@QC8c.U4L RC__))).
Definition gIMG_HI : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_img_hi RC__ (@QC8c.U4L RC__))).
Definition gHEXGOT : Z := ltac:(gw_hex 0%nat).  Definition gHEXPTR : Z := ltac:(gw_hex 1%nat).  Definition gHEXCHARS : Z := ltac:(gw_hex 2%nat).
Definition gVOL := QC8c.u4_volatile.  Definition gCS := QC8c.u4_client_static.
Definition gH1 := fun RC__ : gw_RC => @QCcH.hl_static_in_img RC__ (@QC8c.U4L RC__).
Definition gH2 := fun RC__ : gw_RC => @QCcH.hl_img_range RC__ (@QC8c.U4L RC__).
Definition gH3 := fun RC__ : gw_RC => @QCcH.hl_scratch_in_img RC__ (@QC8c.U4L RC__).
Definition gH4 := fun RC__ : gw_RC => @QCcH.hl_scratch_not_static RC__ (@QC8c.U4L RC__).
Definition gH5 := fun RC__ : gw_RC => @QCcH.hl_consts_ok RC__ (@QC8c.U4L RC__).
Definition e_fn_obj_to_json_string := Eval cbv beta iota delta [Q0Ek.fn_obj_to_json_string QC8c.U4F] in (Q0Ek.fn_obj_to_json_string QC8c.U4F).
Definition e_fn_arr_to_json_string := Eval cbv beta iota delta [Q0Ek.fn_arr_to_json_string QC8c.U4F] in (Q0Ek.fn_arr_to_json_string QC8c.U4F).
Definition e_fn_bool_to_json_string := Eval cbv beta iota delta [Q0Ek.fn_bool_to_json_string QC8c.U4F] in (Q0Ek.fn_bool_to_json_string QC8c.U4F).
Definition e_fn_dbl_to_json_string := Eval cbv beta iota delta [Q0Ek.fn_dbl_to_json_string QC8c.U4F] in (Q0Ek.fn_dbl_to_json_string QC8c.U4F).
Definition e_fn_int_to_json_string := Eval cbv beta iota delta [Q0Ek.fn_int_to_json_string QC8c.U4F] in (Q0Ek.fn_int_to_json_string QC8c.U4F).
Definition e_fn_str_to_json_string := Eval cbv beta iota delta [Q0Ek.fn_str_to_json_string QC8c.U4F] in (Q0Ek.fn_str_to_json_string QC8c.U4F).
Definition e_fn_ud_to_json_string := Eval cbv beta iota delta [Q0Ek.fn_ud_to_json_string QC8c.U4F] in (Q0Ek.fn_ud_to_json_string QC8c.U4F).
Definition e_fn_free_userdata := Eval cbv beta iota delta [Q0Ek.fn_free_userdata QC8c.U4F] in (Q0Ek.fn_free_userdata QC8c.U4F).
Definition e_fn_lh_entry_free := Eval cbv beta iota delta [Q0Ek.fn_lh_entry_free QC8c.U4F] in (Q0Ek.fn_lh_entry_free QC8c.U4F).
Definition e_fn_lh_char_hash := Eval cbv beta iota delta [Q0Ek.fn_lh_char_hash QC8c.U4F] in (Q0Ek.fn_lh_char_hash QC8c.U4F).
Definition e_fn_lh_char_equal := Eval cbv beta iota delta [Q0Ek.fn_lh_char_equal QC8c.U4F] in (Q0Ek.fn_lh_char_equal QC8c.U4F).
Definition e_fn_arr_entry_free := Eval cbv beta iota delta [Q0Ek.fn_arr_entry_free QC8c.U4F] in (Q0Ek.fn_arr_entry_free QC8c.U4F).
Definition GGOT4 := (0x658e0)%Z.
Definition GHASH4 := (0x66a38)%Z.
Definition GVDSO4 := (0x66f20)%Z.
Definition vdso_ok4 := fun (vf : Z) => (vf = 0x61050 \/ vf = 0).
Definition gRDATA_LO : Z := ltac:(let v := eval cbv delta [u4_client_static] in u4_client_static in lazymatch v with (fun a => (?lo <= a < _) /\ _) => exact lo end).
Definition pS4L := Eval cbv beta delta [Q0Hd.gl segs e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI] in
(fun RC__ : gw_RC => @Q0Hd.gl RC__ segs e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI (gH1 RC__) (gH2 RC__) (gH3 RC__) (gH4 RC__) (gH5 RC__)).
Definition pS4F := Eval cbv beta delta [Q0Hd.gf e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free] in
(Q0Hd.gf e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free).
End GwI.
Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply2.gw_side_extra ::= intros; unfold u4_client_static, u4_volatile; lia. Local Ltac mkr__gw_side_extra_0 := intros; unfold u4_client_static, u4_volatile; lia.

Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition GHASHU : Z := 0x66a38.
Definition GGOTU : Z := 0x658e0.
Definition GVDSOU : Z := 0x66f20.
Definition vdso_okU (vf : Z) : Prop := vf = 0x61050 \/ vf = 0.

Section ULhNew.
Variable HIx : heap_iface U4L.
Notation HEAPx := (HEAP U4L HIx).

Definition u_lh_kchar_table_new_entry : Z := 0x28330.

Local Definition gwt_X : unit := (Q6nq.gwt_pat GwI.pS4L (@QC8c.U4L) (Q6nq.gwt_pat GwI.pS4F QC8c.U4F Q6nq.gwt_nil)).
#[using="Type"] Lemma u_lh_init_loop : ltac2:(Q6nq.ty2 'GwI.segs '(@QRGY.u_lh_init_loop) [] '([164808; 164832; 18446744073709551615]%Z : list Z) '(Q6nq.gwt_unf (@LH_EMPTYv) (Q6nq.gwt_def (@QRGY.u_lh_kchar_table_new_entry) (@u_lh_kchar_table_new_entry) gwt_X))).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QRGY.u_lh_init_loop) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QRGY.u_lh_init_loop)]. Qed.

Notation lh_globU := (lh_glob usegs U4F GHASHU GGOTU GVDSOU vdso_okU).

#[using="Type"] Lemma u_lh_glob_client : forall LB SP m m', heap_pres U4L LB SP m m' -> lh_globU m -> lh_globU m'.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QRGY.u_lh_glob_client) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QRGY.u_lh_glob_client)]. Qed.

Definition u_lh_table_new_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : Model) (LB : list blk) (lo : Z)
(ms' : machine_state) (md' : Model) : Prop :=
exists m' (A' : AS U4L HIx) (r : Z) (errv' : word),
ret_statew U4L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
model_vm_only md md' /\
stk usegs m' lo (bv_unsigned sp) /\
heap_pres U4L LB (bv_unsigned sp) m m' /\
rw_cells usegs m' (0x77c00 - 164) [C4 errv'] /\
lh_globU m' /\
( (r = 0 /\ HEAPx A' LB m' md')
\/ (r <> 0 /\ exists BS, lhtab2 usegs U4F m' BS r [] /\ HEAPx A' (BS ++ LB) m' md') ).

#[using="Type"] Lemma u_lh_kchar_table_new_cps :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS U4L HIx) (LB : list blk) (lo : Z) (errv : word),
HEAPx A LB m md ->
lh_globU m ->
stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 - 8256 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top U4L HIx ->
rw_cells usegs m (0x77c00 - 164) [C4 errv] ->
tp = Z_to_bv 64 0x77c00 ->
bv_unsigned ra mod 2 = 0 ->
a0 = Z_to_bv 64 16 -> a1 = Z_to_bv 64 (fn_lh_entry_free U4F) ->
(forall ms' md', u_lh_table_new_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB lo ms' md' ->
realizes usegs (mkCfg ms' md') T) ->
realizes usegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 u_lh_kchar_table_new_entry) fc None m (seg_rom usegs)) md) T.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QRGY.u_lh_kchar_table_new_cps) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QRGY.u_lh_kchar_table_new_cps)]. Qed.
End ULhNew.

End RC__1.
