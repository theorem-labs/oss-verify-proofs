(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.json_c.json_object_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QND5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QND5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsSk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsSk. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qt8n.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qt8n. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWtD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWtD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDlz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDlz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOTP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOTP. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1LT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1LT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpvH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpvH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYLF.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QyaF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QyaF. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXVi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXVi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQjP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQjP. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJQc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJQc.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q45h.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q45h.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS.
Open Scope Z_scope.
Set Default Proof Using "All".

Definition atopE (E : env) : Z := bv_unsigned (edenot E e_sp0) - 0x800000.

Lemma u_litE : forall E z, 0 <= z < 2^64 -> bv_unsigned (edenot E (ELit z)) = z.
Proof. intros E z Hz. cbn [edenot]. apply u64_lit. exact Hz. Qed.

Section Main.
Variable sp : word.
Variable rdraw : EntryDraw.
Variable brk0 : word.
Variable argv envp : list (list byte).
Variable fs : Fs.Fs.
Variables uid hw : word.
Hypothesis Hsp : valid_sp sp.
Variables (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (mo : Model).
Variable w : bool.
Variable ch : acs.
Hypothesis HCL : HSCLASS_S w ch.
Hypothesis CS : cs_ok JOB6SEGS BJO6 QVWI.Mq0.LIMIT (bv_unsigned sp) (SINV0 JOB6PH sp rdraw brk0 argv envp uid hw) (argH0 JOB6PH sp rdraw argv envp uid hw) fs E ch R FULL mo.

#[local] Notation h := (m_vmmaps mo).
#[local] Notation P f := (f _ _ _ _ _ _ _ _ _ _ _ _ CS) (only parsing).

Lemma main_sp0 : edenot E e_sp0 = sp.
Proof. apply bv_eq. exact (proj1 (P co_sp0)). Qed.

Lemma main_init_sp : vm_init_sp h = sp.
Proof. apply bv_eq. exact (P co_isp). Qed.

Lemma main_atop : atopE E = alloc_top h.
Proof. unfold atopE, alloc_top. rewrite main_init_sp, main_sp0. reflexivity. Qed.

Lemma main_atop_bounds : 0x7fff7f800000 <= atopE E <= 0x7fffff800000.
Proof. unfold atopE. rewrite main_sp0. destruct Hsp as (H1 & H2 & _). unfold sp_window_lo, sp_window_hi in *. lia. Qed.

Lemma main_vm_maps : vm_maps h = map (obj_e E) (OBJS_W w) ++ [e_high E; e_gap E; e_low E].
Proof. apply main_maps_S. rewrite <- (MAPS_W_eq w ch HCL). exact (P co_maps). Qed.

Lemma in_maps_obj : forall o, In o (OBJS_W w) -> In (obj_e E o) (vm_maps h).
Proof. intros o Ho. rewrite main_vm_maps. apply in_app_iff. left. apply in_map. exact Ho. Qed.
Lemma e_low_in : In (e_low E) (vm_maps h).  Proof. rewrite main_vm_maps. apply in_app_iff. right. cbn. tauto. Qed.
Lemma e_gap_in : In (e_gap E) (vm_maps h).  Proof. rewrite main_vm_maps. apply in_app_iff. right. cbn. tauto. Qed.
Lemma e_high_in : In (e_high E) (vm_maps h).  Proof. rewrite main_vm_maps. apply in_app_iff. right. cbn. tauto. Qed.

Lemma maps_pos : forall iv, In iv (vm_maps h) -> 0 < bv_unsigned (snd iv).
Proof. intros iv Hiv. pose proof (P co_bounds) as B. rewrite Forall_forall in B. exact (proj1 (B iv Hiv)). Qed.

Lemma maps_disj : forall p q, In p (vm_maps h) -> In q (vm_maps h) -> p <> q -> iv_disjoint p q.
Proof. intros p q Hp Hq Hne. exact (QYLF.Mq0.seps_In_disjoint _ p q (P co_seps) maps_pos Hp Hq Hne). Qed.

Lemma maps_below_atop : forall e, In e (vm_maps h) -> bv_unsigned (fst e) + bv_unsigned (snd e) <= alloc_top h.
Proof.
intros e He. pose proof (P co_bounds) as B. rewrite Forall_forall in B.
pose proof (proj2 (proj2 (proj2 (proj2 (B e He))))) as X. unfold ATOP, STACK_MAX in X.
unfold alloc_top, stack_max_size. rewrite main_init_sp. lia.
Qed.
End Main.
