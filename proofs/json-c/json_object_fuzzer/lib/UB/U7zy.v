(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq GwApply GwApply2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Hd.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UPIU.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC8c.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.

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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UjdK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UjdK.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply GwApply2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module GwI.
Definition segs := rsegs.
Definition base := 0x243b8%Z.
Definition w_25 := 0x7402c0ef%Z.
Definition w_48 := 0x45c3b0ef%Z.
Definition w_56 := 0x4103b0ef%Z.
Definition w_80 := 0x0652f0ef%Z.
Definition joff_25 := (Z_to_bv 21 182080).
Definition joff_48 := (Z_to_bv 21 242780).
Definition joff_56 := (Z_to_bv 21 242704).
Definition joff_80 := (Z_to_bv 21 194660).
Definition e_194bc := 0x50b60%Z.
Definition e_memset := 0x5f9b8%Z.
Lemma CODE : CodeAt.code_at rsegs 0x243b8 (UPIU.Mqf.pbmemset_code 0x7402c0ef%Z 0x45c3b0ef%Z 0x4103b0ef%Z 0x0652f0ef%Z).  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x243b8 mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x243b8 /\ 0x243b8 + 532 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.

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
Lemma CODE_e_194bc : CodeAt.code_at rsegs e_194bc UPIU.Mqf.blk_194bc_code.  Proof. StepGen.code_at_vm. Qed.
Definition memset_spec := @memset_spec.
Definition pS4L := Eval cbv beta delta [Q0Hd.gl segs e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI] in
(fun RC__ : gw_RC => @Q0Hd.gl RC__ segs e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI (gH1 RC__) (gH2 RC__) (gH3 RC__) (gH4 RC__) (gH5 RC__)).
Definition pS4F := Eval cbv beta delta [Q0Hd.gf e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free] in
(Q0Hd.gf e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free).
End GwI.

Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PbMemset.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).

Definition printbuf_memset_entry : Z := 0x243b8.

Local Definition gwt_X : unit := (Q6nq.gwt_pat GwI.pS4L (@UC8c.Mq0.S4L) (Q6nq.gwt_pat GwI.pS4F UC8c.Mq0.S4F Q6nq.gwt_nil)).
#[using="Type"] Lemma memset_specZ : ltac2:(Q6nq.ty2 'GwI.segs '(@UPIU.Mqf.memset_specZ) [] '([256; 391608]%Z : list Z) '(Q6nq.gwt_unf (@memset_entry) (Q6nq.gwt_def (@UPIU.Mqf.printbuf_memset_entry) (@printbuf_memset_entry) gwt_X))).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@UPIU.Mqf.memset_specZ) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@UPIU.Mqf.memset_specZ)]. Qed.

Definition memset_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : Model) (LB : list blk) (pb buf bpos cap : Z) (content : list byte) (len lo : Z)
(ms' : machine_state) (md' : Model) : Prop :=
exists m' (A' : AS S4L HIx) (r : Z) (errv' : word) (buf' cap' : Z),
ret_statew S4L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
model_vm_only md md' /\
stk rsegs m' lo (bv_unsigned sp) /\
heap_pres S4L LB (bv_unsigned sp) m m' /\
rw_cells rsegs m' (0x77c00 - 164) [C4 errv'] /\
HEAPx A' ((pb, PB_SZ) :: (buf', cap') :: LB) m' md' /\
((r = 0 /\ exists content', pbuf_core rsegs m' pb buf' (bpos + len) cap' content')
\/ (r = 2^64 - 1 /\ buf' = buf /\ cap' = cap /\ pbuf_core rsegs m' pb buf bpos cap content)).

Section Blocks.
Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : Model) (LB : list blk) (lo : Z) (pb buf0 bpos0 cap0 len : Z) (content0 : list byte) (cv : word) (T : TSet).

#[using="Type"] Lemma pbmemset_efbig : ltac2:(Q6nq.ty2 'GwI.segs '(@UPIU.Mqf.pbmemset_efbig) [[@gw_eq_memset_post__3; @gw_eq_memset_post__2; @gw_eq_memset_post]] '([148512; 490332; 490496]%Z : list Z) '(Q6nq.gwt_def (@UPIU.Mqf.memset_post) (@memset_post) (Q6nq.gwt_def (@UPIU.Mqf.printbuf_memset_entry) (@printbuf_memset_entry) gwt_X))).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@UPIU.Mqf.pbmemset_efbig) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@UPIU.Mqf.pbmemset_efbig)]. Qed.

#[using="Type"] Lemma pbmemset_tail : ltac2:(Q6nq.ty2 'GwI.segs '(@UPIU.Mqf.pbmemset_tail) [[@gw_eq_memset_post__3; @gw_eq_memset_post__2; @gw_eq_memset_post]] '([(-8256); (-164); 148736; 490496]%Z : list Z) '(Q6nq.gwt_def (@UPIU.Mqf.memset_post) (@memset_post) (Q6nq.gwt_def (@UPIU.Mqf.printbuf_memset_entry) (@printbuf_memset_entry) gwt_X))).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@UPIU.Mqf.pbmemset_tail) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@UPIU.Mqf.pbmemset_tail)]. Qed.

#[using="Type"] Lemma pbmemset_grow : ltac2:(Q6nq.ty2 'GwI.segs '(@UPIU.Mqf.pbmemset_grow) [[@gw_eq_memset_post__3; @gw_eq_memset_post__2; @gw_eq_memset_post]] '([(-8256); (-164); 148692; 490496]%Z : list Z) '(Q6nq.gwt_def (@UPIU.Mqf.memset_post) (@memset_post) (Q6nq.gwt_def (@UPIU.Mqf.printbuf_memset_entry) (@printbuf_memset_entry) gwt_X))).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@UPIU.Mqf.pbmemset_grow) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@UPIU.Mqf.pbmemset_grow)]. Qed.
End Blocks.

#[using="Type"] Lemma lxor_ones31 : forall b, 0 <= b < 2^31 -> Z.lxor b 2147483647 = 2147483647 - b.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@UPIU.Mqf.lxor_ones31) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@UPIU.Mqf.lxor_ones31)]. Qed.

#[using="Type"] Lemma pbmemset_cps : ltac2:(Q6nq.ty2 'GwI.segs '(@UPIU.Mqf.pbmemset_cps) [[@gw_eq_memset_post__3; @gw_eq_memset_post__2; @gw_eq_memset_post]] '([(-8256); (-164); 490496]%Z : list Z) '(Q6nq.gwt_zc printbuf_memset_entry (Q6nq.gwt_def (@UPIU.Mqf.memset_post) (@memset_post) (Q6nq.gwt_def (@UPIU.Mqf.printbuf_memset_entry) (@printbuf_memset_entry) gwt_X)))).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_memset_post__3; @gw_eq_memset_post__2; @gw_eq_memset_post]]); first [GwApply2.gw_by_name2 GwI.segs (@UPIU.Mqf.pbmemset_cps) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@UPIU.Mqf.pbmemset_cps)]. Qed.
End PbMemset.

End RC__1.
