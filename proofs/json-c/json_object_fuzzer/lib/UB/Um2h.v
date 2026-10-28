(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QqdR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqdR.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QnDM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnDM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UjdK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UjdK. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U4l4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U4l4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UxrO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UxrO.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr.
Open Scope bv_scope.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q91D.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX.mkr__sg_step_core_3. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX.mkr__sg_zstep_4. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.

Definition pad_entry := 0x56588%Z.
Lemma gw_eq_pad_entry : @pad_entry = ltac:(GwInst.gw_term (@Q91D.Mq2.pad_entry 0x56588) (@pad_entry)). Proof. unfold pad_entry, Q91D.Mq2.pad_entry; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_pad_entry : gw_eqs.

Definition got_ssp := 0x659d0%Z.
Definition ssp_guard := 0x97e70%Z.

Module GwI.
Definition segs := rsegs.
Definition base := 0x56588%Z.
Definition w_7 := 0x0000f517%Z.
Definition w_8 := 0x42c53903%Z.
Definition w_21 := 0x3dc090ef%Z.
Definition w_33 := 0x915fe0ef%Z.
Definition w_41 := 0x8f5fe0ef%Z.
Definition w_52 := 0x9cdfa0ef%Z.
Definition hi_7 := (Z_to_bv 20 15).
Definition lo_8 := (Z_to_bv 12 1068).
Definition joff_21 := (Z_to_bv 21 37852).
Definition joff_33 := (Z_to_bv 21 2091284).
Definition joff_41 := (Z_to_bv 21 2091252).
Definition joff_52 := (Z_to_bv 21 2075084).
Definition got_ssp := got_ssp.
Definition ssp_guard := ssp_guard.
Definition e_197bc := 0x51024%Z.
Definition e_fwritex := 0x54f20%Z.
Definition e_memset := 0x5f9b8%Z.
Lemma CODE : CodeAt.code_at rsegs 0x56588 (Q91D.Mq2.pad_code 0x0000f517%Z 0x42c53903%Z 0x3dc090ef%Z 0x915fe0ef%Z 0x8f5fe0ef%Z 0x9cdfa0ef%Z).  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x56588 mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x56588 /\ 0x56588 + 212 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.
Definition memset_spec := @memset_spec.
Definition fwritex_call := @fwritex_call.
End GwI.

Definition ssp_cells (m : word -> option byte) (canary : word) : Prop :=
rw_cells rsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells rsegs m ssp_guard [C8 canary].

Definition pad_n (w l fl : Z) : Z :=
if negb (Z.land fl (Z.lor LEFT_ADJ ZERO_PAD) =? 0)%Z || (w <=? l)%Z then 0 else w - l.

Lemma pad_model : forall o c w l fl, (w - l < 256)%Z ->
pad o c w l fl = Some (o ++ zrepeat c (pad_n w l fl)).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@Q91D.Mq2.pad_model). Qed.

Definition memset_postZ (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(D C N : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(D, D + N)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rw_cells rsegs m' D [CB (Z.to_nat N) (repeat (Z_to_bv 8 (C mod 256)) (Z.to_nat N))].

Local Definition gwt_X : unit := (Q6nq.gwt_def (@Q91D.Mq2.wfile) (@UxrO.wfile) (Q6nq.gwt_def (@QQLG.Mq7.wfile) (@UxrO.wfile) (Q6nq.gwt_def (@Q91D.Mq2.memset_post) (@UjdK.memset_post) (Q6nq.gwt_def (@QVbl.Mq4.memset_post) (@UjdK.memset_post) (Q6nq.gwt_def (@Q91D.Mq2.fwritex_postZ) (@UxrO.fwritex_postZ) (Q6nq.gwt_def (@QQLG.Mq7.fwritex_postZ) (@UxrO.fwritex_postZ) Q6nq.gwt_nil)))))).
Lemma memset_callZ : ltac2:(Q6nq.ty1 'GwI.segs '(@Q91D.Mq2.memset_callZ) [[@gw_eq_pad_entry__3; @gw_eq_pad_entry__2; @gw_eq_pad_entry]] '([391608]%Z : list Z) '(Q6nq.gwt_unf (@memset_entry) (Q6nq.gwt_def (@Q91D.Mq2.memset_postZ) (@memset_postZ) (Q6nq.gwt_def (@Q91D.Mq2.pad_n) (@pad_n) (Q6nq.gwt_def (@Q91D.Mq2.ssp_cells) (@ssp_cells) gwt_X))))).
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q91D.Mq2.memset_callZ). Qed.

Lemma rw_cells_bytes_at' : forall segs m A cs, rw_cells segs m A cs -> bytes_at segs m A (cells_bytes cs).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@Q91D.Mq2.rw_cells_bytes_at'). Qed.

Definition pad_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(Fp : Z) (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (B : Z) (content junk : list byte) (canary : word)
(C n : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(bv_unsigned sp - 368, bv_unsigned sp);
(B + Z.of_nat (length content), B + Z.of_nat (length content) + n);
(Fp + 40, Fp + 48)]%Z m m'
/\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' (bv_unsigned sp - 368) (bv_unsigned sp)
/\ wfile m' Fp fl0 j1 j2 lbfw B (content ++ repeat (Z_to_bv 8 C) (Z.to_nat n)) (skipn (Z.to_nat n) junk)
/\ ssp_cells m' canary.

Ltac hyp := lazymatch goal with |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end end.

Lemma pad_spec : ltac2:(Q6nq.ty1 'GwI.segs '(@Q91D.Mq2.pad_spec) [[@gw_eq_pad_entry__3; @gw_eq_pad_entry__2; @gw_eq_pad_entry]; [@gw_eq_W__3; @gw_eq_W__2; @gw_eq_W]; [@gw_eq_ssp_cells__3; @gw_eq_ssp_cells__2; @gw_eq_ssp_cells]; [@gw_eq_wfile__3; @gw_eq_wfile__2; @gw_eq_wfile]] '([(-368); 256; 353672]%Z : list Z) '(Q6nq.gwt_unf (@pad_entry) (Q6nq.gwt_zc ssp_guard (Q6nq.gwt_def (@Q91D.Mq2.pad_post) (@pad_post) (Q6nq.gwt_def (@Q91D.Mq2.memset_postZ) (@memset_postZ) (Q6nq.gwt_def (@Q91D.Mq2.pad_n) (@pad_n) (Q6nq.gwt_def (@Q91D.Mq2.ssp_cells) (@ssp_cells) (Q6nq.gwt_pat (@ssp_guard) (@ssp_guard) (Q6nq.gwt_hdr GwI.ssp_guard (@ssp_guard) gwt_X))))))))).
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q91D.Mq2.pad_spec). Qed.

Definition pad_postZ (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(Fp : Z) (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (B : Z) (content junk : list byte) (canary : word)
(C n : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(q - 368, q);
(B + Z.of_nat (length content), B + Z.of_nat (length content) + n);
(Fp + 40, Fp + 48)]%Z m m'
/\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' (q - 368) q
/\ wfile m' Fp fl0 j1 j2 lbfw B (content ++ repeat (Z_to_bv 8 C) (Z.to_nat n)) (skipn (Z.to_nat n) junk)
/\ ssp_cells m' canary.

Lemma pad_call : ltac2:(Q6nq.ty1 'GwI.segs '(@Q91D.Mq2.pad_call) [[@gw_eq_pad_entry__3; @gw_eq_pad_entry__2; @gw_eq_pad_entry]; [@gw_eq_W__3; @gw_eq_W__2; @gw_eq_W]; [@gw_eq_ssp_cells__3; @gw_eq_ssp_cells__2; @gw_eq_ssp_cells]; [@gw_eq_wfile__3; @gw_eq_wfile__2; @gw_eq_wfile]] '([(-368); 256; 353672]%Z : list Z) '(Q6nq.gwt_unf (@pad_entry) (Q6nq.gwt_zc ssp_guard (Q6nq.gwt_def (@Q91D.Mq2.pad_postZ) (@pad_postZ) (Q6nq.gwt_def (@Q91D.Mq2.pad_post) (@pad_post) (Q6nq.gwt_def (@Q91D.Mq2.memset_postZ) (@memset_postZ) (Q6nq.gwt_def (@Q91D.Mq2.pad_n) (@pad_n) (Q6nq.gwt_def (@Q91D.Mq2.ssp_cells) (@ssp_cells) (Q6nq.gwt_pat (@ssp_guard) (@ssp_guard) (Q6nq.gwt_hdr GwI.ssp_guard (@ssp_guard) gwt_X)))))))))).
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q91D.Mq2.pad_call). Qed.
