(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq GwApply. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q8l1.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq1.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QnDM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnDM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UjdK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UjdK. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U4l4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U4l4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UxrO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UxrO. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UDgQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UDgQ.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qfw3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3.Mq1.
Import ListNotations. Unset Keyed Unification. Local Ltac Q2qa.Mq0.sf_vocab ::= Q2qa.Mq0.mkr__sf_vocab_5. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Open Scope bv_scope.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module GwI.
Definition segs := rsegs.
Definition base := 0x59f78%Z.
Definition w_22 := 0x468050ef%Z.
Definition w_34 := 0x438050ef%Z.
Definition joff_22 := (Z_to_bv 21 21608).
Definition joff_34 := (Z_to_bv 21 21560).
Definition e_memcpy := 0x5f438%Z.
Lemma CODE : CodeAt.code_at rsegs 0x59f78 (Q8l1.Mq4.sn_write_code 0x468050ef%Z 0x438050ef%Z).  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x59f78 mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x59f78 /\ 0x59f78 + 220 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.
Definition memcpy_spec := @memcpy_spec.
End GwI.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs. Local Ltac mkr__transport_chunks_0 segs m a bs := transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs. Local Ltac mkr__footprint_after_store_1 segs m a bs := footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast. Local Ltac mkr__mem_after_store_2 := mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM. Local Ltac mkr__transport_after_call_3 segs m m' MU WM := transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= lia3. Local Ltac mkr__lia_4 := lia3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation mem := (word -> option byte).
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac fixK K := try (rewrite ?swrap32_small in K by lia); try (rewrite ?signed_of_Z in K by lia); try (rewrite ?Z.add_0_r in K).
Ltac brf K := if_cases K; zify_cond K; fixK K.
Ltac br K := brf K; try (exfalso; lia).
Ltac if_lit :=
lazymatch goal with
| |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let v := eval vm_compute in c in change c with v; cbv iota
end. Ltac mkr__if_lit_6 := lazymatch goal with
| |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let v := eval vm_compute in c in change c with v; cbv iota
end.

Lemma zb_length : forall l, length (zb l) = length l.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_zb__3; @gw_eq_zb__2; @gw_eq_zb]]); first [GwInst.gw_exact (@Q8l1.Mq4.zb_length) | autorewrite with gw_eqs; GwInst.gw_exact (@Q8l1.Mq4.zb_length)]. Qed.
Lemma rw_CB_length : forall m A n (bs : list byte), rw_cells rsegs m A [CB n bs] -> length bs = n.
Proof. first [GwApply.gw_by_name GwI.segs (@Q8l1.Mq4.rw_CB_length) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q8l1.Mq4.rw_CB_length)]. Qed.
Lemma le1_zero : le1 (Z_to_bv 64 0) = [Z_to_bv 8 0].
Proof. first [GwInst.gw_exact (@Q8l1.Mq4.le1_zero) | autorewrite with gw_eqs; GwInst.gw_exact (@Q8l1.Mq4.le1_zero)]. Qed.

Definition memcpy_postv (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(Dst Src N : Z) (src : list byte) (m : mem) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(Dst, Dst + N)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rw_cells rsegs m' Dst [CB (Z.to_nat N) src]
/\ bytes_at rsegs m' Src src.
Lemma gw_eq_memcpy_postv : @memcpy_postv = ltac:(GwInst.gw_term (@Q8l1.Mq4.memcpy_postv rsegs) (@memcpy_postv)). Proof. unfold memcpy_postv, Q8l1.Mq4.memcpy_postv; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_memcpy_postv : gw_eqs.

Local Definition gwt_X : unit := (Q6nq.gwt_def (@QQRC.Mq0.zb) (@UDgQ.zb) Q6nq.gwt_nil).
Lemma memcpy_callv : ltac2:(Q6nq.ty1 'GwI.segs '(@Q8l1.Mq4.memcpy_callv) [[@gw_eq_memcpy_postv]] '([390200]%Z : list Z) '(Q6nq.gwt_unf (@memcpy_entry) gwt_X)).
Proof. rewrite ?gw_eq_memcpy_postv; first [GwApply.gw_by_name GwI.segs (@Q8l1.Mq4.memcpy_callv) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q8l1.Mq4.memcpy_callv)]. Qed.

Definition sn_write_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(Fp CK D n B bufp : Z) (o : list Z) (dn : nat) (junk : list byte) (m : mem) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (CK, CK + 16); (D, D + Z.of_nat dn); (Fp + 40, Fp + 48); (Fp + 56, Fp + 64)]%Z m m'
/\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' (bv_unsigned sp - 64) (bv_unsigned sp)
/\ rw_cells rsegs m' CK [C8 (Z_to_bv 64 (D + zlength o)); C8 (Z_to_bv 64 (n - zlength o))]
/\ rw_cells rsegs m' D [CB dn (zb o ++ Z_to_bv 8 0 :: skipn (S (length o)) junk)]
/\ rw_cells rsegs m' (Fp + 40) [C8 (Z_to_bv 64 bufp)]
/\ rw_cells rsegs m' (Fp + 56) [C8 (Z_to_bv 64 bufp)]
/\ bytes_at rsegs m' B (zb o).
Lemma gw_eq_sn_write_post : @sn_write_post = ltac:(GwInst.gw_term (@Q8l1.Mq4.sn_write_post rsegs) (@sn_write_post)). Proof. unfold sn_write_post, Q8l1.Mq4.sn_write_post; ltac2:(GwEq.gw_rw [[@gw_eq_zb__3; @gw_eq_zb__2; @gw_eq_zb]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_sn_write_post : gw_eqs.

Lemma sn_write_spec : ltac2:(Q6nq.ty1 'GwI.segs '(@Q8l1.Mq4.sn_write_spec) [[@gw_eq_frame__3; @gw_eq_frame__2; @gw_eq_frame]; [@gw_eq_zb__3; @gw_eq_zb__2; @gw_eq_zb]; [@gw_eq_sn_write_post]; [@gw_eq_memcpy_postv__3; @gw_eq_memcpy_postv__2; @gw_eq_memcpy_postv]] '([88; 152; 160; 368504]%Z : list Z) 'gwt_X).
Proof. rewrite ?gw_eq_sn_write_post; ltac2:(GwEq.gw_rw [[@gw_eq_frame__3; @gw_eq_frame__2; @gw_eq_frame]; [@gw_eq_zb__3; @gw_eq_zb__2; @gw_eq_zb]]); first [GwApply.gw_by_name GwI.segs (@Q8l1.Mq4.sn_write_spec) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q8l1.Mq4.sn_write_spec)]. Qed.
