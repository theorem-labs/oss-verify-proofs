(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Q5Rg QEQM Qc3B QZDE QRjH QgLo QHnV QCcH QfLs Q0Ek QC8c Qsw7 QJjn QRUw QSL3 QhI1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup Q5Rg.
Import QEQM.
Import Qc3B QZDE.
Import QRjH.
Import QgLo.
Import QHnV QCcH QfLs Q0Ek.
Import QC8c.Mq0.
Import Qsw7 QJjn QRUw QRUw.Mq2.
Import QSL3.
Import QhI1.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Ltac genregs SPV :=
repeat (match goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
match R with context [Some ?v] =>
tryif is_var v then fail else
lazymatch v with
| Z_to_bv _ ?z =>
match z with context [bv_unsigned ?x] => is_var x; tryif constr_eq x SPV then fail else (generalize v; intros ?w) end
| _ => generalize v; intros ?w
end end end).
Ltac hstep SPV := step; genregs SPV.

Section HashCore.
Variables (kp : Z) (ks slack : list byte) (m : word -> option byte).
Let full := ks ++ Z_to_bv 8 0 :: slack.
Let len := Z.of_nat (length ks).
Hypothesis STR : bytes_at rsegs m kp full.
Hypothesis MI : mem_inv rsegs m.
Hypothesis AL : kp mod 4 = 0.

#[using="slack full STR"] Lemma hash_loop :
forall (k : nat) (j : Z) (x1 sp gp tp t0 t1 t2 x9 a1 a2 a3 a5 a6 a7 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32),
(k = Z.to_nat (len - j))%nat -> 0 <= j -> 12 < len - j -> j mod 4 = 0 ->
evt rsegs (fun ms' => exists (j' : Z) (a1' a2' a3' a5' a6' a7' : word),
0 <= j' /\ 0 <= len - j' <= 12 /\ j' mod 4 = 0 /\
ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 (kp + j')) x9 (Z_to_bv 64 (len - j')) a1' a2' a3' (Z_to_bv 64 12) a5' a6' a7' x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x26564) fc None m (seg_rom rsegs))
(MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 (kp + j)) x9 (Z_to_bv 64 (len - j)) a1 a2 a3 (Z_to_bv 64 12) a5 a6 a7 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x2636c) fc None m (seg_rom rsegs)).
Proof.
induction k as [k IH] using lt_wf_ind; intros until fc; intros Hk Hj Hr Hal.
pose proof (bytes_at_bound _ _ _ _ STR) as AB. unfold full in AB. rewrite length_app in AB. cbn [length] in AB.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof (bytes_at_read rsegs m kp full j 4 STR ltac:(lia) ltac:(unfold full; rewrite length_app; cbn; lia)) as RD0.
pose proof (bytes_at_read rsegs m kp full (j + 4) 4 STR ltac:(lia) ltac:(unfold full; rewrite length_app; cbn; lia)) as RD1.
pose proof (bytes_at_read rsegs m kp full (j + 8) 4 STR ltac:(lia) ltac:(unfold full; rewrite length_app; cbn; lia)) as RD2.
do 45 (hstep sp).
replace (kp + j + 12) with (kp + (j + 12)) by lia. replace (len - j + -12) with (len - (j + 12)) by lia.
destruct (Z.lt_ge_cases 12 (len - (j + 12))) as [LT | GE].
- if_truex. eapply (IH (Z.to_nat (len - (j + 12)))); try lia; rewrite <- Zplus_mod_idemp_l, Hal; reflexivity.
- if_falsex. step. apply evt_done. exists (j + 12). do 6 eexists.
split; [lia|]. split; [lia|]. split; [rewrite <- Zplus_mod_idemp_l, Hal; reflexivity|]. reflexivity.
Qed.
Ltac step_to PC SPV :=
repeat (lazymatch goal with
| |- evt _ _ (MS _ _ (Z_to_bv 64 PC) _ _ _ _) => fail
| |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => hstep SPV
end).
Ltac rd j off n H :=
pose proof (bytes_at_read rsegs m kp full (j + off) n STR ltac:(lia) ltac:(unfold full; rewrite length_app; cbn; lia)) as H.

#[using="slack full STR MI"] Lemma hash_tail :
forall (j : Z) (x1 sp gp tp t0 t1 t2 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32),
0 <= j -> 0 <= len - j <= 12 -> j mod 4 = 0 ->
evt rsegs (fun ms' => exists (u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 : word),
ms' = MS (mkR x1 sp gp tp u0 u1 u2 (Z_to_bv 64 (kp + j)) x9 v0 v1 v2 v3 v4 v5 v6 v7 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 u3 u4 u5 u6)
F (Z_to_bv 64 0x2688c) fc None m (seg_rom rsegs))
(MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 (kp + j)) x9 (Z_to_bv 64 (len - j)) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x26564) fc None m (seg_rom rsegs)).
Proof.
intros until fc; intros Hj Hr Hal.
pose proof (bytes_at_bound _ _ _ _ STR) as AB. unfold full in AB. rewrite length_app in AB. cbn [length] in AB.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
assert (CASES : len - j = 0 \/ len - j = 1 \/ len - j = 2 \/ len - j = 3 \/ len - j = 4 \/ len - j = 5 \/ len - j = 6 \/
len - j = 7 \/ len - j = 8 \/ len - j = 9 \/ len - j = 10 \/ len - j = 11 \/ len - j = 12) by lia.
destruct CASES as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]]]]]; rewrite E.
- step_to 0x2688c sp. apply evt_done; do 15 eexists; reflexivity.
- rd j 0 1%nat RDa. step_to 0x2688c sp. apply evt_done; do 15 eexists; reflexivity.
- rd j 0 2%nat RDa. step_to 0x2688c sp. apply evt_done; do 15 eexists; reflexivity.
- rd j 0 4%nat RDa. step_to 0x2688c sp. apply evt_done; do 15 eexists; reflexivity.
- rd j 0 4%nat RDa. step_to 0x2688c sp. apply evt_done; do 15 eexists; reflexivity.
- rd j 0 4%nat RDa. rd j 4 1%nat RDb. step_to 0x2688c sp. apply evt_done; do 15 eexists; reflexivity.
- rd j 0 4%nat RDa. rd j 4 2%nat RDb. step_to 0x2688c sp. apply evt_done; do 15 eexists; reflexivity.
- rd j 0 4%nat RDa. rd j 4 4%nat RDb. step_to 0x2688c sp. apply evt_done; do 15 eexists; reflexivity.
- rd j 0 4%nat RDa. rd j 4 4%nat RDb. step_to 0x2688c sp. apply evt_done; do 15 eexists; reflexivity.
- rd j 0 4%nat RDa. rd j 4 4%nat RDb. rd j 8 1%nat RDc. step_to 0x2688c sp. apply evt_done; do 15 eexists; reflexivity.
- rd j 0 4%nat RDa. rd j 4 4%nat RDb. rd j 8 2%nat RDc. step_to 0x2688c sp. apply evt_done; do 15 eexists; reflexivity.
- rd j 0 4%nat RDa. rd j 4 4%nat RDb. rd j 8 4%nat RDc. step_to 0x2688c sp. apply evt_done; do 15 eexists; reflexivity.
- rd j 0 4%nat RDa. rd j 4 4%nat RDb. rd j 8 4%nat RDc. step_to 0x2688c sp. apply evt_done; do 15 eexists; reflexivity.
Qed.
End HashCore.

End Mq0.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply GwApply2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Hd.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXOI.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QC8c.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.

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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8tj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8tj.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSL3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSL3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9m8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9m8.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnCn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnCn.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.

Module GwI.
Definition segs := usegs.
Definition base := 0x2878c%Z.
Definition w_21 := 0x0d5290ef%Z.
Definition w_27 := 0x0bd2906f%Z.
Definition joff_21 := (Z_to_bv 21 170196).
Definition joff_27 := (Z_to_bv 21 170172).
Definition e_16ed0 := 0x24654%Z.
Lemma CODE : CodeAt.code_at usegs 0x2878c (QXOI.ulhfree_code 0x0d5290ef%Z 0x0bd2906f%Z).  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x2878c mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x2878c /\ 0x2878c + 112 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.

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
Definition wb17dac_14 := 0x9acff06f%Z.
Definition wb17dac_16 := 0x4052c0ef%Z.
Definition joffb17dac_14 := (Z_to_bv 21 2093484).
Definition joffb17dac_16 := (Z_to_bv 21 183300).
Lemma CODE_e_fn_lh_entry_free : CodeAt.code_at usegs e_fn_lh_entry_free (QXOI.blk_17dac_code 0x9acff06f%Z 0x4052c0ef%Z).  Proof. StepGen.code_at_vm. Qed.
Definition pS4L := Eval cbv beta delta [Q0Hd.gl segs e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI] in
(fun RC__ : gw_RC => @Q0Hd.gl RC__ segs e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI (gH1 RC__) (gH2 RC__) (gH3 RC__) (gH4 RC__) (gH5 RC__)).
Definition pS4F := Eval cbv beta delta [Q0Hd.gf e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free] in
(Q0Hd.gf e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free).
End GwI.

Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma ent_addr_mod8 : forall tbl i, tbl mod 16 = 0 -> (tbl + 40 * Z.of_nat i) mod 8 = 0.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QXOI.ent_addr_mod8) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QXOI.ent_addr_mod8)]. Qed.

Section ULhFree.
Variable HIx : heap_iface U4L.
Notation HEAPx := (HEAP U4L HIx).

Definition u_lh_entry_free_entry : Z := 0x25470.
Definition u_lh_table_free_entry : Z := 0x2878c.

Definition u_lh_entry_free_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : Model) (LB : list blk) (lo : Z) (errv : word)
(ms' : machine_state) (md' : Model) : Prop :=
exists m' (A' : AS U4L HIx) (r : word),
ret_state U4L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m' ms' /\
model_vm_only md md' /\
stk usegs m' lo (bv_unsigned sp) /\
heap_pres U4L LB (bv_unsigned sp) m m' /\
rw_cells usegs m' (0x77c00 - 164) [C4 errv] /\
HEAPx A' LB m' md'.

Local Definition gwt_X : unit := (Q6nq.gwt_pat GwI.pS4L (@QC8c.U4L) (Q6nq.gwt_pat GwI.pS4F QC8c.U4F Q6nq.gwt_nil)).
#[using="Type"] Lemma u_lh_entry_free_cps : ltac2:(Q6nq.ty2 'GwI.segs '(@QXOI.u_lh_entry_free_cps) [] '([(-8256); (-164); 65536; 490496; 626688]%Z : list Z) '(Q6nq.gwt_zc u_lh_entry_free_entry (Q6nq.gwt_def (@QXOI.u_lh_entry_free_post) (@u_lh_entry_free_post) (Q6nq.gwt_def (@QXOI.u_lh_table_free_entry) (@u_lh_table_free_entry) (Q6nq.gwt_def (@QXOI.u_lh_entry_free_entry) (@u_lh_entry_free_entry) gwt_X))))).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QXOI.u_lh_entry_free_cps) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QXOI.u_lh_entry_free_cps)]. Qed.

Variables (sp gp : word) (s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : Model) (LB : list blk) (lo t tbl size : Z) (es : list lent) (svs : list slotv) (T : TSet).
Variables (s0c s1c rac : word).

Definition u_free_frame (m : word -> option byte) (junk8 : list byte) : Prop :=
rw_cells usegs m (bv_unsigned sp + -32) [CB 8 junk8; C8 s1c; C8 s0c; C8 rac].

Definition u_free_exit (errv : word) (K0 : machine_state -> Model -> Prop) : Prop :=
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : word -> option byte) (md : Model) (A : AS U4L HIx) (junk8 : list byte)
(hsz hcnt hhd htl : Z),
HEAPx A ((t, 56) :: (tbl, 40 * size) :: LB) m md ->
rw_cells usegs m t [C4 (Z_to_bv 64 hsz); C4 (Z_to_bv 64 hcnt); C8 (Z_to_bv 64 hhd); C8 (Z_to_bv 64 htl); C8 (Z_to_bv 64 tbl);
C8 (Z_to_bv 64 (fn_lh_entry_free U4F)); C8 (Z_to_bv 64 (fn_lh_char_hash U4F)); C8 (Z_to_bv 64 (fn_lh_char_equal U4F))] ->
stk usegs m lo (bv_unsigned sp + -32) ->
u_free_frame m junk8 ->
rw_cells usegs m (0x77c00 - 164) [C4 errv] ->
model_vm_only md0 md -> heap_pres U4L LB (bv_unsigned sp) m0 m ->
K0 (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp (Z_to_bv 64 0x77c00) t0 t1 t2 (Z_to_bv 64 t) (Z_to_bv 64 0) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x287dc) fc None m (seg_rom usegs)) md.

#[using="Type"] Lemma u_ent_addr_pos : forall i, 0 < tbl -> 0 < ent_addr tbl i.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QXOI.u_ent_addr_pos) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QXOI.u_ent_addr_pos)]. Qed.

#[using="Type"] Lemma u_lh_free_loop : ltac2:(Q6nq.ty2 'GwI.segs '(@QXOI.u_lh_free_loop) [] '([(-8256); (-164); 165820; 490496]%Z : list Z) '(Q6nq.gwt_def (@QXOI.u_free_exit) (@u_free_exit) (Q6nq.gwt_def (@QXOI.u_free_frame) (@u_free_frame) (Q6nq.gwt_def (@QXOI.u_lh_entry_free_post) (@u_lh_entry_free_post) (Q6nq.gwt_def (@QXOI.u_lh_table_free_entry) (@u_lh_table_free_entry) (Q6nq.gwt_def (@QXOI.u_lh_entry_free_entry) (@u_lh_entry_free_entry) gwt_X)))))).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QXOI.u_lh_free_loop) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QXOI.u_lh_free_loop)]. Qed.

Definition u_lh_table_free_post (errv : word) (ms' : machine_state) (md' : Model) : Prop :=
exists m' (A' : AS U4L HIx) (r : word),
ret_statew U4L rac sp gp (Z_to_bv 64 0x77c00) s0c s1c s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m' ms' /\
model_vm_only md0 md' /\
stk usegs m' lo (bv_unsigned sp) /\
heap_pres U4L LB (bv_unsigned sp) m0 m' /\
rw_cells usegs m' (0x77c00 - 164) [C4 errv] /\
HEAPx A' LB m' md'.

#[using="Type"] Lemma u_lh_u_free_exit_ok : ltac2:(Q6nq.ty2 'GwI.segs '(@QXOI.u_lh_u_free_exit_ok) [] '([(-8256)]%Z : list Z) '(Q6nq.gwt_def (@QXOI.u_lh_table_free_post) (@u_lh_table_free_post) (Q6nq.gwt_def (@QXOI.u_free_exit) (@u_free_exit) (Q6nq.gwt_def (@QXOI.u_free_frame) (@u_free_frame) (Q6nq.gwt_def (@QXOI.u_lh_entry_free_post) (@u_lh_entry_free_post) (Q6nq.gwt_def (@QXOI.u_lh_table_free_entry) (@u_lh_table_free_entry) (Q6nq.gwt_def (@QXOI.u_lh_entry_free_entry) (@u_lh_entry_free_entry) gwt_X))))))).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QXOI.u_lh_u_free_exit_ok) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QXOI.u_lh_u_free_exit_ok)]. Qed.

#[using="Type"] Lemma u_lh_table_free_cps : ltac2:(Q6nq.ty2 'GwI.segs '(@QXOI.u_lh_table_free_cps) [] '([(-8256); (-164); 490496]%Z : list Z) '(Q6nq.gwt_zc u_lh_table_free_entry (Q6nq.gwt_def (@QXOI.u_lh_table_free_post) (@u_lh_table_free_post) (Q6nq.gwt_def (@QXOI.u_free_exit) (@u_free_exit) (Q6nq.gwt_def (@QXOI.u_free_frame) (@u_free_frame) (Q6nq.gwt_def (@QXOI.u_lh_entry_free_post) (@u_lh_entry_free_post) (Q6nq.gwt_def (@QXOI.u_lh_table_free_entry) (@u_lh_table_free_entry) (Q6nq.gwt_def (@QXOI.u_lh_entry_free_entry) (@u_lh_entry_free_entry) gwt_X)))))))).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QXOI.u_lh_table_free_cps) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QXOI.u_lh_table_free_cps)]. Qed.
End ULhFree.

End RC__1.
