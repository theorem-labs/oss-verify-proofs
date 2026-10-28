(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply GwApply2.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UB45.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC8c.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UPZI.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UhI1.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Umd7.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qc3B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc3B.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q8tj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8tj.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSL3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSL3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UhI1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UhI1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U22i.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U22i. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U6us.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U6us. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require ULLZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import ULLZ. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UAIk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UAIk. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Ul9N.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ul9N. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Umd7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Umd7.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.

Module GwI.
Definition segs := rsegs.
Definition base := 0x2840c%Z.
Definition w_14 := 0x32d290ef%Z.
Definition w_21 := 0x309290ef%Z.
Definition w_53 := 0x3a5290ef%Z.
Definition w_75 := 0x341290ef%Z.
Definition w_77 := 0x339290ef%Z.
Definition joff_14 := (Z_to_bv 21 170796).
Definition joff_21 := (Z_to_bv 21 170760).
Definition joff_53 := (Z_to_bv 21 170916).
Definition joff_75 := (Z_to_bv 21 170816).
Definition joff_77 := (Z_to_bv 21 170808).
Definition GGOT4 := Eval cbv in GGOT4.
Definition GHASH4 := Eval cbv in GHASH4.
Definition GVDSO4 := Eval cbv in GVDSO4.
Definition JG_CGT_P := Eval cbv in UPZI.Mq0.JG_CGT_P.
Lemma CODE : CodeAt.code_at rsegs 0x2840c (UB45.lhresize_code 0x32d290ef%Z 0x309290ef%Z 0x3a5290ef%Z 0x341290ef%Z 0x339290ef%Z).  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x2840c mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x2840c /\ 0x2840c + 412 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.

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
Definition gRDATA_LO : Z := ltac:(let v := eval cbv delta [s4_client_static] in s4_client_static in lazymatch v with (fun a => (?lo <= a < _) /\ _) => exact lo end).
Definition lh_glob_client := @UhI1.lh_glob_client.
Definition lh_insert_small_cps := @Umd7.lh_insert_small_cps.
End GwI.
Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply2.gw_side_extra ::= intros; unfold s4_client_static, s4_volatile; lia. Local Ltac mkr__gw_side_extra_0 := intros; unfold s4_client_static, s4_volatile; lia.

Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition lh_char_hash_entry : Z := 0x27844.

#[using="Type"] Lemma firstn_S_nth : forall (A : Type) (l : list A) j x, nth_error l j = Some x -> firstn (S j) l = firstn j l ++ [x].
Proof. first [GwApply2.gw_by_name2 GwI.segs (@UB45.firstn_S_nth) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@UB45.firstn_S_nth)]. Qed.

#[using="Type"] Lemma strip_snoc : forall esn es j e g,
map strip esn = map strip (firstn j es) -> nth_error es j = Some e ->
map strip (esn ++ [LE g (le_k e) (le_kn e) (le_ks e) (le_v e)]) = map strip (firstn (S j) es).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@UB45.strip_snoc) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@UB45.strip_snoc)]. Qed.

#[using="Type"] Lemma perm_mid2 : forall (l1 : list blk) a b l2, Permutation (l1 ++ a :: b :: l2) (b :: l1 ++ a :: l2).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@UB45.perm_mid2) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@UB45.perm_mid2)]. Qed.

Section LhResize.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).
Notation lh_glob4 := (lh_glob rsegs S4F GHASH4 GGOT4 GVDSO4 vdso_ok4).
Hypothesis LF : lf_test_spec.
Variable MREL : Model -> Model -> Prop.
Hypothesis MREL_refl : forall md, MREL md md.
Hypothesis MREL_trans : forall a b c, MREL a b -> MREL b c -> MREL a c.
Hypothesis MREL_vm : forall a b, model_vm_only a b -> MREL a b.

Definition lh_hash_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : Model) (LB : list blk) (lo : Z)
(ms' : machine_state) (md' : Model) : Prop :=
exists m' (A' : AS S4L HIx) (h : Z) (errv' : word),
ret_statew S4L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 h) m' ms' /\ 0 <= h < 2^64 /\
MREL md md' /\ stk rsegs m' lo (bv_unsigned sp) /\ heap_presx S4L s4_volatile LB (bv_unsigned sp) m m' /\
rw_cells rsegs m' (0x77c00 - 164) [C4 errv'] /\ lh_glob4 m' /\ HEAPx A' LB m' md'.

Definition lh_char_hash_stmt (HD : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS S4L HIx) (LB : list blk) (lo : Z) (errv : word) (kp kn : Z) (ks : list byte),
HEAPx A LB m md -> In (kp, kn) LB -> cstr rsegs m kp kn ks -> lh_glob4 m ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - HD ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
rw_cells rsegs m (0x77c00 - 164) [C4 errv] -> tp = Z_to_bv 64 0x77c00 -> bv_unsigned ra mod 2 = 0 -> frm0 fc ->
a0 = Z_to_bv 64 kp ->
(forall ms' md', lh_hash_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB lo ms' md' ->
realizes rsegs (mkCfg ms' md') T) ->
realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 lh_char_hash_entry) fc None m (seg_rom rsegs)) md) T.

Variable HD : Z.
Hypothesis HD_ge : 8256 + 64 <= HD.
Hypothesis HASH : lh_char_hash_stmt HD.

Section Loop.
Variables (sp gp : word) (s7 s8 s9 s10 s11 : word) (F0 : bvmap 5 word) (fc0 : bv 32).
Variables (m0 : word -> option byte) (md0 : Model) (LB : list blk) (lo t tbl SZ NS nt ntbl : Z) (es : list lent) (svs : list slotv) (T : TSet).
Variables (rac s0c s1c s2c s3c s4c s5c s6c : word).
Variable j8 : list byte.

Definition rs_frame (m : word -> option byte) : Prop :=
rw_cells rsegs m (bv_unsigned sp + -64) [CB 8 j8; C8 s5c; C8 s4c; C8 s3c; C8 s2c; C8 s1c; C8 s0c; C8 rac].
Definition old_hdr (m : word -> option byte) : Prop :=
rw_cells rsegs m t (hdr_cells tbl (fn_lh_entry_free S4F) SZ (Z.of_nat (length es)) (hd_of tbl es) (tl_of tbl es)).

Definition rs_exit : Prop :=
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (errv : word) (esn : list lent) (svsn : list slotv),
HEAPx A (lh_blocks nt ntbl NS esn ++ (t, 56) :: (tbl, 40 * SZ) :: LB) m md ->
lh_openf rsegs S4F 0 m nt ntbl NS esn svsn -> map strip esn = map strip es ->
old_hdr m -> lh_glob4 m ->
stk rsegs m lo (bv_unsigned sp + -64) -> rs_frame m ->
rw_cells rsegs m (0x77c00 - 164) [C4 errv] -> frm0 fc -> QCcH.fsaved F0 F -> (QCcH.frm0 fc0 -> QCcH.frm0 fc) ->
MREL md0 md -> heap_presx S4L s4_volatile LB (bv_unsigned sp) m0 m ->
realizes rsegs (mkCfg (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 0x77c00) t0 t1 t2 (Z_to_bv 64 nt) (Z_to_bv 64 (-1))
a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 t) (Z_to_bv 64 NS) (Z_to_bv 64 0) (Z_to_bv 64 (fn_lh_char_equal S4F)) s6c s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x2850c) fc None m (seg_rom rsegs)) md) T.

Definition rs_K : Prop :=
forall ms' md', lh_resize_post HIx MREL rac sp gp (Z_to_bv 64 0x77c00) s0c s1c s2c s3c s4c s5c s6c s7 s8 s9 s10 s11 F0 fc0 m0 md0 LB lo t tbl SZ NS es svs ms' md' ->
realizes rsegs (mkCfg ms' md') T.

End Loop.

#[using="Type"] Lemma perm_resize : forall (q nt t tbl : Z) (a b c d : Z) (M LB : list blk),
Permutation ((q, a) :: (nt, b) :: (t, c) :: (tbl, d) :: M ++ LB) ((nt, b) :: (q, a) :: M ++ (t, c) :: (tbl, d) :: LB).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@UB45.perm_resize) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@UB45.perm_resize)]. Qed.

#[using="LF MREL_refl MREL_trans MREL_vm HD_ge HASH"] Lemma lh_resize_cps : lh_resize_stmt HIx MREL (64 + HD).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@UB45.lh_resize_cps) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@UB45.lh_resize_cps)]. Qed.
End LhResize.

End RC__1.
