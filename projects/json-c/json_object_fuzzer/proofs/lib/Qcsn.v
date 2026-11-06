(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply GwApply2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q91D.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXEH.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlEo_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfw3_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3_c1.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBpX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBpX.
Import ListNotations. Unset Keyed Unification. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope bv_scope.

Module GwI.
Definition segs := usegs.
Definition base := 0xcf0cc%Z.
Definition w_7 := 0x981ff0ef%Z.
Definition joff_7 := (Z_to_bv 21 2095488).
Definition RATP := QXEH.RATP.
Definition RDEBRUIJN := QXEH.RDEBRUIJN.
Definition RGOT_SSP := QXEH.RGOT_SSP.
Definition RIMG_HI := QXEH.RIMG_HI.
Definition RDATA_LO := QXEH.RDATA_LO.
Definition gw_RTEXT_LO := ltac:(let gw_v_ := eval cbv in (fst (nth 1 QXEH.ref_reserved (0%Z, 0%Z))) in exact gw_v_).
Definition gw_RDATA2_LO := ltac:(let gw_v_ := eval cbv in (fst (nth 3 QXEH.ref_reserved (0%Z, 0%Z))) in exact gw_v_).
Definition ref_reserved := QXEH.ref_reserved.
Definition rerrno_loc_entry := QXEH.rerrno_loc_entry.
Lemma CODE : CodeAt.code_at usegs 0xcf0cc (Q91D.Mq7.sysret_code 0x981ff0ef%Z).  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0xcf0cc mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0xcf0cc /\ 0xcf0cc + 56 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.
Lemma CODE_rerrno_loc_entry : CodeAt.code_at usegs rerrno_loc_entry Q91D.Mq7.errno_loc_code.  Proof. StepGen.code_at_vm. Qed.
Definition ref_find_segment_none := @QXEH.ref_find_segment_none.
Definition ref_ro_addr_false := @QXEH.ref_ro_addr_false.
Definition ref_memory_read_none := @QXEH.ref_memory_read_none.
Definition ref_wview_overlay := @QXEH.ref_wview_overlay.
Definition ref_seg_rom_none := @QXEH.ref_seg_rom_none.
Definition ref_mrd_overlay := @QXEH.ref_mrd_overlay.
End GwI.

Definition sysret_entry := 0xcf0cc%Z.
Lemma gw_eq_sysret_entry : @sysret_entry = ltac:(GwInst.gw_term (@Q91D.Mq7.sysret_entry 0xcf0cc) (@sysret_entry)). Proof. unfold sysret_entry, Q91D.Mq7.sysret_entry; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_sysret_entry : gw_eqs.

Definition sysret_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 r errv : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (sysret_val r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom usegs)
/\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m'
/\ wmono usegs m m' /\ mem_inv usegs m'
/\ stk usegs m' lo (bv_unsigned sp)
/\ rw_cells usegs m' (errno_addr tp) [C4 (sysret_errno r errv)].
Lemma gw_eq_sysret_post : @sysret_post = ltac:(GwInst.gw_term (@Q91D.Mq7.sysret_post usegs) (@sysret_post)). Proof. unfold sysret_post, Q91D.Mq7.sysret_post; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_sysret_post : gw_eqs.

Lemma sysret_spec : ltac2:(Q6nq.ty2 'GwI.segs '(@Q91D.Mq7.sysret_spec) [[@gw_eq_sysret_post]; [@gw_eq_sysret_entry__3; @gw_eq_sysret_entry__2; @gw_eq_sysret_entry]] '([164; 848076]%Z : list Z) '(Q6nq.gwt_unf (@sysret_entry) Q6nq.gwt_nil)).
Proof. rewrite ?gw_eq_sysret_post; first [GwApply2.gw_by_name2 GwI.segs (@Q91D.Mq7.sysret_spec) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q91D.Mq7.sysret_spec)]. Qed.

