(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.CodeAt Lib.StepGen Lib.GwInst Lib.GwEq Lib.GwEqH Lib.GwApply Lib.GwApply2 QGwP QC8c QCcH Q0Ek QPZI QhI1 QeL5.
From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Q5Rg QEQM Qc3B QRjH QHnV QfLs Qsw7 QJjn QRUw Q8tj QSL3 QLLZ QAIk QIX4 Q6q3 Q3CA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup Q5Rg.
Import QEQM.
Import Qc3B.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek.
Import QC8c.Mq0.
Import Qsw7 QJjn QRUw Q8tj.
Import QSL3.
Import QhI1 QeL5 QLLZ QAIk.
Import QIX4.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr.
Open Scope Z_scope.
Import Q6q3.
Import Q3CA.

Module GwI.
Definition segs := rsegs.
Definition base := 0x26d9c%Z.
Definition GGOT4 := Eval cbv in GGOT4.
Definition GHASH4 := Eval cbv in GHASH4.
Definition GVDSO4 := Eval cbv in GVDSO4.
Definition JG_CGT_P := Eval cbv in QPZI.Mq0.JG_CGT_P.
Lemma CODE : CodeAt.code_at rsegs 0x26d9c QGwP.Mq0.lhdelete_code.  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x26d9c mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x26d9c /\ 0x26d9c + 288 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.

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
Definition gRDATA_LO : Z := ltac:(let v := eval cbv delta [s4_client_static] in s4_client_static in lazymatch v with (fun a => (?lo <= a < _) /\ _) => exact lo end).
Definition lh_glob_client := @QhI1.lh_glob_client.
Definition lh_entry_free_cps := @QeL5.lh_entry_free_cps.
Lemma LAY_gIMG_LO : ltac2:(GwEq.gw_fact_ty 'segs '(@QGwP.Mq0.gw_all) @LAY_gIMG_LO). Proof. GwApply.gw_side. Qed.
Lemma LAY_TPLO : ltac2:(GwEq.gw_fact_ty 'segs '(@QGwP.Mq0.gw_all) @LAY_TPLO). Proof. GwApply.gw_side. Qed.
Lemma LAY_TPHI : ltac2:(GwEq.gw_fact_ty 'segs '(@QGwP.Mq0.gw_all) @LAY_TPHI). Proof. GwApply.gw_side. Qed.
Lemma LAY_GGOT4_GHASH4 : ltac2:(GwEq.gw_fact_ty 'segs '(@QGwP.Mq0.gw_all) @LAY_GGOT4_GHASH4). Proof. GwApply.gw_side. Qed.
Lemma LAY_GHASH4_GVDSO4 : ltac2:(GwEq.gw_fact_ty 'segs '(@QGwP.Mq0.gw_all) @LAY_GHASH4_GVDSO4). Proof. GwApply.gw_side. Qed.
Lemma LAY_IMG_GGOT4 : ltac2:(GwEq.gw_fact_ty 'segs '(@QGwP.Mq0.gw_all) @LAY_IMG_GGOT4). Proof. GwApply.gw_side. Qed.
Lemma LAY_GVDSO4_IMG : ltac2:(GwEq.gw_fact_ty 'segs '(@QGwP.Mq0.gw_all) @LAY_GVDSO4_IMG). Proof. GwApply.gw_side. Qed.
End GwI.
Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply2.gw_side_extra ::= intros; unfold s4_client_static, s4_volatile; lia. Local Ltac mkr__gw_side_extra_0 := intros; unfold s4_client_static, s4_volatile; lia.

Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition lh_delete_tail_entry : Z := 0x26d9c.

Definition del_slot (s : slotv) : slotv := SV LH_FREEDv (sv_kc s) (sv_pad s) 0 0 0.
Definition clr_nx (s : slotv) : slotv := SV (sv_k s) (sv_kc s) (sv_pad s) (sv_v s) 0 (sv_pv s).

#[using="Type"] Lemma snoc_inv : forall (l : list lent), l = [] \/ exists l' x, l = l' ++ [x].
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QGwP.Mq0.snoc_inv) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QGwP.Mq0.snoc_inv)]. Qed.

#[using="Type"] Lemma firstn_snoc_le : forall (A : Type) (l : list A) x n, (n <= length l)%nat -> firstn n (l ++ [x]) = firstn n l.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QGwP.Mq0.firstn_snoc_le) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QGwP.Mq0.firstn_snoc_le)]. Qed.

#[using="Type"] Lemma pv_of_snoc2 : forall tbl es1 el e, pv_of tbl ((es1 ++ [el]) ++ [e]) (length (es1 ++ [el])) = ent_addr tbl (le_ix el).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QGwP.Mq0.pv_of_snoc2) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QGwP.Mq0.pv_of_snoc2)]. Qed.
#[using="Type"] Lemma perm_key_front : forall t tbl size es0 e LB,
Permutation (lh_blocks t tbl size (es0 ++ [e]) ++ LB) (kblk e :: lh_blocks t tbl size es0 ++ LB).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QGwP.Mq0.perm_key_front) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QGwP.Mq0.perm_key_front)]. Qed.

Section Unsnoc.
Variables (tbl : Z) (es0 : list lent) (e : lent) (svs : list slotv) (se : slotv).
Hypothesis LINK : lh_link tbl (es0 ++ [e]) svs.
Hypothesis Ese : nth_error svs (le_ix e) = Some se.

#[using="LINK Ese"] Lemma lh_link_unsnoc_nil : es0 = [] -> lh_link tbl [] (upd svs (le_ix e) (del_slot se)).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QGwP.Mq0.lh_link_unsnoc_nil) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QGwP.Mq0.lh_link_unsnoc_nil)]. Qed.

#[using="LINK Ese"] Lemma lh_link_unsnoc_cons : forall es1 el sl,
es0 = es1 ++ [el] -> nth_error svs (le_ix el) = Some sl ->
lh_link tbl es0 (upd (upd svs (le_ix e) (del_slot se)) (le_ix el) (clr_nx sl)).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QGwP.Mq0.lh_link_unsnoc_cons) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QGwP.Mq0.lh_link_unsnoc_cons)]. Qed.
End Unsnoc.

Section LhDelete.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).
Notation lh_glob4 := (lh_glob rsegs S4F GHASH4 GGOT4 GVDSO4 vdso_ok4).

Section DelLoop.
Variables (sp gp : word) (s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : Model) (LB : list blk) (lo t tbl size : Z) (jf : nat) (ef : lent) (T : TSet).
Variables (rac s0c s1c s2c s3c s4c s5c s6c : word).
Variable errv : word.

Variable GI : (word -> option byte) -> Prop.
Hypothesis GI_munch : forall m m' W, GI m -> munch W m m' -> wmono rsegs m m' -> Forall (fun iv => 0x97000 <= fst iv \/ snd iv <= 0x10000) W -> GI m'.
Hypothesis GI_pres : forall m m' LB' SP, heap_pres S4L LB' SP m m' -> GI m -> GI m'.

Definition del_frame (m : word -> option byte) : Prop :=
rw_cells rsegs m (bv_unsigned sp + -64) [C8 s6c; C8 s5c; C8 s4c; C8 s3c; C8 s2c; C8 s1c; C8 s0c; C8 rac].

Definition del_exit (esf : list lent) : Prop :=
forall (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x18 x21 x22 t3 t4 t5 t6 : word)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (svsf : list slotv),
HEAPx A (lh_blocks t tbl size esf ++ LB) m md ->
lh_open rsegs S4F m t tbl size esf svsf -> GI m ->
stk rsegs m lo (bv_unsigned sp + -64) -> del_frame m ->
rw_cells rsegs m (0x75e70 - 164) [C4 errv] ->
model_vm_only md0 md -> heap_pres S4L LB (bv_unsigned sp) m0 m ->
realizes rsegs (mkCfg (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 0x75e70) t0 t1 t2 (Z_to_bv 64 (ent_addr tbl (le_ix ef))) (Z_to_bv 64 t)
(Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 x18 (Z_to_bv 64 (-3)) (Z_to_bv 64 (-2)) x21 x22 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x26e94) fc None m (seg_rom rsegs)) md) T.

End DelLoop.

Definition lh_delete_tail_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : Model) (LB : list blk) (lo : Z) (t tbl size : Z) (es : list lent) (jf : nat)
(ms' : machine_state) (md' : Model) : Prop :=
exists m' (A' : AS S4L HIx) (errv' : word) svs',
ret_state S4L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 0) m' ms' /\
model_vm_only md md' /\ stk rsegs m' lo (bv_unsigned sp) /\ heap_pres S4L LB (bv_unsigned sp) m m' /\
rw_cells rsegs m' (0x75e70 - 164) [C4 errv'] /\ lh_glob4 m' /\
lh_open rsegs S4F m' t tbl size (firstn jf es) svs' /\ HEAPx A' (lh_blocks t tbl size (firstn jf es) ++ LB) m' md'.

#[using="Type"] Lemma lh_delete_tail_cps2 : lh_delete_tail_stmt2 HIx.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QGwP.Mq0.lh_delete_tail_cps2) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QGwP.Mq0.lh_delete_tail_cps2)]. Qed.
End LhDelete.

End RC__1.
End Mq0.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply GwApply2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Hd.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QGwP.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QC8c.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QAyu.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEQM.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QC8c.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8tj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8tj.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSL3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSL3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q22i.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q22i. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6us.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6us. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLLZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLLZ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QAIk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QAIk.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr.
Open Scope Z_scope.

Module GwI.
Definition segs := rsegs.
Definition base := 0x26adc%Z.
Definition w_10 := 0xfffed897%Z.
Definition w_11 := 0x8fc8b787%Z.
Definition hi_10 := (Z_to_bv 20 1048557).
Definition lo_11 := (Z_to_bv 12 2300).
Definition G_10770 := 0x13400%Z.
Lemma CODE : CodeAt.code_at rsegs 0x26adc (QAyu.Mq3.lhprobe_code 0xfffed897%Z 0x8fc8b787%Z).  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x26adc mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x26adc /\ 0x26adc + 388 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.

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
Definition pS4L := Eval cbv beta delta [Q0Hd.gl segs e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI] in
(fun RC__ : gw_RC => @Q0Hd.gl RC__ segs e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI (gH1 RC__) (gH2 RC__) (gH3 RC__) (gH4 RC__) (gH5 RC__)).
Definition pS4F := Eval cbv beta delta [Q0Hd.gf e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free] in
(Q0Hd.gf e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free).
End GwI.

Section LhInsertTail.
Variables (sp gp tp : word) (s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (t tbl size k v : Z) (es : list lent) (svs : list slotv) (ffn : Z).
Variables (rac s0c s1c s2c s3c s4c s5c : word).

Definition ins_tail_post (cnt lo : Z) (x28 x29 x30 x31 : word) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists (g : nat) (sg : slotv) (ixl : nat) (sl : slotv) (x5 x6 x7 x11 x12 : word) m',
(g < length svs)%nat /\ nth_error svs g = Some sg /\ is_free sg /\ ~ In g (map le_ix es) /\
(es <> [] -> exists jl el, nth_error es jl = Some el /\ (S jl = length es)%nat /\ ixl = le_ix el /\ nth_error svs ixl = Some sl) /\
ms' = MS (mkR rac sp gp tp x5 x6 x7 s0c s1c (Z_to_bv 64 0)
x11 x12 (Z_to_bv 64 (Z.of_nat g)) (Z_to_bv 64 0) (Z_to_bv 64 tbl) (Z_to_bv 64 (cnt + 1)) (Z_to_bv 64 (tbl + 40 * Z.of_nat g))
s2c s3c s4c s5c s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (ret_pc rac) fc None m' (seg_rom rsegs)
/\ munch [(t, t + 56); (tbl, tbl + 40 * size)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rw_cells rsegs m' t (hdr_cells tbl ffn size (cnt + 1) (match es with [] => ent_addr tbl g | _ => hd_of tbl es end) (ent_addr tbl g))
/\ lh_slots rsegs m' tbl (ins_svs svs g sg k v (hd_of tbl es) (tl_of tbl es) ixl sl tbl)
/\ stk rsegs m' lo (bv_unsigned sp).

Local Definition gwt_X : unit := (Q6nq.gwt_def (@QAyu.Mq3.is_free) (@Q6us.is_free) (Q6nq.gwt_def (@QGwP.is_free) (@Q6us.is_free) (Q6nq.gwt_def (@Q7mx.ins_svs) (@QLLZ.ins_svs) (Q6nq.gwt_def (@QGwP.ins_svs) (@QLLZ.ins_svs) (Q6nq.gwt_def (@QAyu.Mq3.ins_regs) (@Q6us.ins_regs) (Q6nq.gwt_def (@QGwP.ins_regs) (@Q6us.ins_regs) (Q6nq.gwt_def (@Q7mx.ins_frame) (@QLLZ.ins_frame) (Q6nq.gwt_def (@QGwP.ins_frame) (@QLLZ.ins_frame) (Q6nq.gwt_def (@Q7mx.hdr_cells) (@QLLZ.hdr_cells) (Q6nq.gwt_def (@QGwP.hdr_cells) (@QLLZ.hdr_cells) (Q6nq.gwt_pat GwI.pS4L (@QC8c.Mq0.S4L) (Q6nq.gwt_pat GwI.pS4F QC8c.Mq0.S4F Q6nq.gwt_nil)))))))))))).
#[using="Type"] Lemma lh_insert_tail : ltac2:(Q6nq.ty2 'GwI.segs '(@QGwP.lh_insert_tail) [] '([158496]%Z : list Z) '(Q6nq.gwt_def (@QGwP.ins_tail_post) (@ins_tail_post) gwt_X)).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QGwP.lh_insert_tail) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QGwP.lh_insert_tail)]. Qed.
End LhInsertTail.
