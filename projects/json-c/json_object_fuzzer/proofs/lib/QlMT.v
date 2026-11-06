(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply GwApply2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qe1A.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKNz.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfw3_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3_c1.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.SepCache.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEQM.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnDM_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnDM_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QULt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QULt.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKNz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKNz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjdK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjdK.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.

Module GwI.
Definition segs := rsegs.
Definition base := 0x501f4%Z.
Definition w_7 := 0xbc9fe0ef%Z.
Definition w_19 := 0x22c000ef%Z.
Definition w_22 := 0x00046517%Z.
Definition w_23 := 0x34452503%Z.
Definition w_33 := 0x1b90d0ef%Z.
Definition w_40 := 0x19d0d0ef%Z.
Definition w_56 := 0x15d0d0ef%Z.
Definition w_67 := 0x1310d06f%Z.
Definition w_75 := 0x321010ef%Z.
Definition hi_22 := (Z_to_bv 20 70).
Definition lo_23 := (Z_to_bv 12 836).
Definition joff_7 := (Z_to_bv 21 2091976).
Definition joff_33 := (Z_to_bv 21 55736).
Definition joff_40 := (Z_to_bv 21 55708).
Definition joff_56 := (Z_to_bv 21 55644).
Definition joff_67 := (Z_to_bv 21 55600).
Definition joff_75 := (Z_to_bv 21 6944).
Definition e_memset := 0x5dc30%Z.
Definition RATP := QKNz.RATP.
Definition RDEBRUIJN := QKNz.RDEBRUIJN.
Definition RGOT_SSP := QKNz.RGOT_SSP.
Definition RIMG_HI := QKNz.RIMG_HI.
Definition RDATA_LO := QKNz.RDATA_LO.
Definition gw_RTEXT_LO := ltac:(let gw_v_ := eval cbv in (fst (nth 1 QKNz.ref_reserved (0%Z, 0%Z))) in exact gw_v_).
Definition gw_RDATA2_LO := ltac:(let gw_v_ := eval cbv in (fst (nth 3 QKNz.ref_reserved (0%Z, 0%Z))) in exact gw_v_).
Definition ref_reserved := QKNz.ref_reserved.
Definition rerrno_loc_entry := QKNz.rerrno_loc_entry.
Definition ris_allzero_entry := QKNz.ris_allzero_entry.
Lemma CODE : CodeAt.code_at rsegs 0x501f4 (Qe1A.Mq8.calloc_code 0xbc9fe0ef%Z 0x22c000ef%Z 0x00046517%Z 0x34452503%Z 0x1b90d0ef%Z 0x19d0d0ef%Z 0x15d0d0ef%Z 0x1310d06f%Z 0x321010ef%Z).  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x501f4 mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x501f4 /\ 0x501f4 + 312 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.
Lemma CODE_rerrno_loc_entry : CodeAt.code_at rsegs rerrno_loc_entry Qe1A.Mq8.errno_loc_code.  Proof. StepGen.code_at_vm. Qed.
Definition ref_find_segment_none := @QKNz.ref_find_segment_none.
Definition ref_ro_addr_false := @QKNz.ref_ro_addr_false.
Definition ref_memory_read_none := @QKNz.ref_memory_read_none.
Definition ref_wview_overlay := @QKNz.ref_wview_overlay.
Definition ref_seg_rom_none := @QKNz.ref_seg_rom_none.
Definition ref_mrd_overlay := @QKNz.ref_mrd_overlay.
Definition memset_spec := @memset_spec.
End GwI.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Abbreviation mem := (word -> option byte).

Definition ztail (m : mem) (p n k : Z) : Prop :=
exists junk, rw_cells rsegs m p [CB (Z.to_nat k) junk; CB (Z.to_nat (n - k)) (zeros (Z.to_nat (n - k)))].
Lemma gw_eq_ztail : @ztail = ltac:(GwInst.gw_term (@Qe1A.Mq8.ztail rsegs) (@ztail)). Proof. unfold ztail, Qe1A.Mq8.ztail; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_ztail : gw_eqs.

Lemma zeros_app a b : zeros a ++ zeros b = zeros (a + b).
Proof. first [GwInst.gw_exact (@Qe1A.Mq8.zeros_app) | autorewrite with gw_eqs; GwInst.gw_exact (@Qe1A.Mq8.zeros_app)]. Qed.

Lemma ztail_bound m p n k : ztail m p n k -> 0 <= k <= n -> 0 <= p /\ p + n <= 2^64.
Proof. rewrite ?gw_eq_ztail; first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mq8.ztail_bound) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mq8.ztail_bound)]. Qed.

Lemma ztail_init m p n junk : rw_cells rsegs m p [CB (Z.to_nat n) junk] -> 0 <= n -> ztail m p n n.
Proof. rewrite ?gw_eq_ztail; first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mq8.ztail_init) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mq8.ztail_init)]. Qed.

Lemma ztail_all m p n : ztail m p n 0 -> 0 <= n -> rw_cells rsegs m p [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))].
Proof. rewrite ?gw_eq_ztail; first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mq8.ztail_all) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mq8.ztail_all)]. Qed.

Local Definition gwt_X : unit := Q6nq.gwt_nil.
Lemma ztail_split : ltac2:(Q6nq.ty2 'GwI.segs '(@Qe1A.Mq8.ztail_split) [[@gw_eq_ztail]] '(@nil Z) 'gwt_X).
Proof. rewrite ?gw_eq_ztail; first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mq8.ztail_split) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mq8.ztail_split)]. Qed.

Lemma ztail_join : ltac2:(Q6nq.ty2 'GwI.segs '(@Qe1A.Mq8.ztail_join) [[@gw_eq_ztail]] '(@nil Z) 'gwt_X).
Proof. rewrite ?gw_eq_ztail; first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mq8.ztail_join) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mq8.ztail_join)]. Qed.

Definition zms_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 : word) (F : bvmap 5 word) (fc : bv 32)
(m : mem) (p n k' : Z) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(p, p + n)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ ztail m' p n k'.
Lemma gw_eq_zms_post : @zms_post = ltac:(GwInst.gw_term (@Qe1A.Mq8.zms_post rsegs) (@zms_post)). Proof. unfold zms_post, Qe1A.Mq8.zms_post; rewrite ?gw_eq_ztail; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_zms_post : gw_eqs.

Lemma zt_memset : ltac2:(Q6nq.ty2 'GwI.segs '(@Qe1A.Mq8.zt_memset) [[@gw_eq_ztail]; [@gw_eq_zms_post]] '([384048]%Z : list Z) '(Q6nq.gwt_unf (@memset_entry) gwt_X)).
Proof. rewrite ?gw_eq_ztail, ?gw_eq_zms_post; first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mq8.zt_memset) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mq8.zt_memset)]. Qed.

Lemma bytes_at_inj m a bs bs' : bytes_at rsegs m a bs -> bytes_at rsegs m a bs' -> length bs = length bs' -> bs = bs'.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mq8.bytes_at_inj) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mq8.bytes_at_inj)]. Qed.

Lemma bytes_at_sub : ltac2:(Q6nq.ty2 'GwI.segs '(@Qe1A.Mq8.bytes_at_sub) [[@gw_eq_ztail__3; @gw_eq_ztail__2; @gw_eq_ztail]; [@gw_eq_zms_post__3; @gw_eq_zms_post__2; @gw_eq_zms_post]] '(@nil Z) 'gwt_X).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mq8.bytes_at_sub) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mq8.bytes_at_sub)]. Qed.

Lemma ztail_read8 : ltac2:(Q6nq.ty2 'GwI.segs '(@Qe1A.Mq8.ztail_read8) [[@gw_eq_ztail]; [@gw_eq_zms_post__3; @gw_eq_zms_post__2; @gw_eq_zms_post]] '(@nil Z) 'gwt_X).
Proof. rewrite ?gw_eq_ztail; first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mq8.ztail_read8) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mq8.ztail_read8)]. Qed.

Lemma le8_zero_inv (w : word) : bv_unsigned w = 0 -> le8 w = zeros 8.
Proof. first [GwInst.gw_exact (@Qe1A.Mq8.le8_zero_inv) | autorewrite with gw_eqs; GwInst.gw_exact (@Qe1A.Mq8.le8_zero_inv)]. Qed.

Lemma ztail_learn16 : ltac2:(Q6nq.ty2 'GwI.segs '(@Qe1A.Mq8.ztail_learn16) [[@gw_eq_ztail]; [@gw_eq_zms_post__3; @gw_eq_zms_post__2; @gw_eq_zms_post]] '(@nil Z) 'gwt_X).
Proof. rewrite ?gw_eq_ztail; first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mq8.ztail_learn16) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mq8.ztail_learn16)]. Qed.

Definition zx_post (sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m0 : mem) (p n g : Z) : machine_state -> Prop :=
fun ms' => exists ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 p) (Z_to_bv 64 (g - p)) (Z_to_bv 64 g) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (if g - p <? 4096 then 0x502e4 else 0x502a4)) fc None m' (seg_rom rsegs)
/\ munch [(p, p + n)] m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m' /\ ztail m' p n (g - p).
Lemma gw_eq_zx_post : @zx_post = ltac:(GwInst.gw_term (@Qe1A.Mq8.zx_post rsegs 0x501f4) (@zx_post)). Proof. unfold zx_post, Qe1A.Mq8.zx_post; rewrite ?gw_eq_ztail; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_zx_post : gw_eqs.

Ltac st1 := step; try rewrite ?unsigned_lit by lia.

Lemma zt_inner : ltac2:(Q6nq.ty2 'GwI.segs '(@Qe1A.Mq8.zt_inner) [[@gw_eq_ztail]; [@gw_eq_zx_post]; [@gw_eq_zms_post__3; @gw_eq_zms_post__2; @gw_eq_zms_post]] '([256; 328368]%Z : list Z) 'gwt_X).
Proof. rewrite ?gw_eq_ztail, ?gw_eq_zx_post; first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mq8.zt_inner) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mq8.zt_inner)]. Qed.

Definition zdone_post (sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m0 : mem) (p n : Z) : machine_state -> Prop :=
fun ms' => exists k ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 p) (Z_to_bv 64 k) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x502e4) fc None m' (seg_rom rsegs)
/\ 0 <= k <= n /\ munch [(p, p + n)] m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m' /\ ztail m' p n k.
Lemma gw_eq_zdone_post : @zdone_post = ltac:(GwInst.gw_term (@Qe1A.Mq8.zdone_post rsegs 0x501f4) (@zdone_post)). Proof. unfold zdone_post, Qe1A.Mq8.zdone_post; rewrite ?gw_eq_ztail; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_zdone_post : gw_eqs.

Lemma zt_outer : ltac2:(Q6nq.ty2 'GwI.segs '(@Qe1A.Mq8.zt_outer) [[@gw_eq_ztail]; [@gw_eq_zdone_post]; [@gw_eq_zms_post__3; @gw_eq_zms_post__2; @gw_eq_zms_post]; [@gw_eq_zx_post__3; @gw_eq_zx_post__2; @gw_eq_zx_post]] '([4096; 328356]%Z : list Z) 'gwt_X).
Proof. rewrite ?gw_eq_ztail, ?gw_eq_zdone_post; first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mq8.zt_outer) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mq8.zt_outer)]. Qed.

Lemma zt_clear : ltac2:(Q6nq.ty2 'GwI.segs '(@Qe1A.Mq8.zt_clear) [[@gw_eq_zdone_post]; [@gw_eq_ztail__3; @gw_eq_ztail__2; @gw_eq_ztail]; [@gw_eq_zms_post__3; @gw_eq_zms_post__2; @gw_eq_zms_post]; [@gw_eq_zx_post__3; @gw_eq_zx_post__2; @gw_eq_zx_post]] '([328280]%Z : list Z) 'gwt_X).
Proof. rewrite ?gw_eq_zdone_post; first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mq8.zt_clear) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mq8.zt_clear)]. Qed.

Definition zfin_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m0 : mem) (p n : Z) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(p, p + n)] m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m'
/\ rw_cells rsegs m' p [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))].
Lemma gw_eq_zfin_post : @zfin_post = ltac:(GwInst.gw_term (@Qe1A.Mq8.zfin_post rsegs) (@zfin_post)). Proof. unfold zfin_post, Qe1A.Mq8.zfin_post; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_zfin_post : gw_eqs.

Lemma zt_tail : ltac2:(Q6nq.ty2 'GwI.segs '(@Qe1A.Mq8.zt_tail) [[@gw_eq_ztail]; [@gw_eq_zfin_post]; [@gw_eq_zms_post__3; @gw_eq_zms_post__2; @gw_eq_zms_post]; [@gw_eq_zx_post__3; @gw_eq_zx_post__2; @gw_eq_zx_post]; [@gw_eq_zdone_post__3; @gw_eq_zdone_post__2; @gw_eq_zdone_post]] '([328420]%Z : list Z) 'gwt_X).
Proof. rewrite ?gw_eq_ztail, ?gw_eq_zfin_post; first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mq8.zt_tail) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mq8.zt_tail)]. Qed.
