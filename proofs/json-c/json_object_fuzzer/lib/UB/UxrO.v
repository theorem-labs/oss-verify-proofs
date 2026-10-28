(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QnDM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnDM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U4l4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U4l4.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
Import ListNotations. Unset Keyed Unification.
Open Scope bv_scope.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QQLG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr.

Module GwI.
Definition segs := rsegs.
Definition base := 0x54f20%Z.
Definition w_46 := 0xd51ff0ef%Z.
Definition w_64 := 0x4180a0ef%Z.
Definition joff_46 := (Z_to_bv 21 2096464).
Definition joff_64 := (Z_to_bv 21 42008).
Definition e_1cb6c := 0x54d28%Z.
Definition e_memcpy := 0x5f438%Z.
Lemma CODE : CodeAt.code_at rsegs 0x54f20 (QQLG.Mq7.fwritex_code 0xd51ff0ef%Z 0x4180a0ef%Z).  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x54f20 mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x54f20 /\ 0x54f20 + 312 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.
Definition memcpy_spec := @memcpy_spec.
End GwI.

Definition fwritex_entry := 0x54f20%Z.
Lemma gw_eq_fwritex_entry : @fwritex_entry = ltac:(GwInst.gw_term (@QQLG.Mq7.fwritex_entry 0x54f20) (@fwritex_entry)). Proof. unfold fwritex_entry, QQLG.Mq7.fwritex_entry; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_fwritex_entry : gw_eqs.

Definition FILE_cells (fl0 : byte) (j1 : list byte) (WEND WPOS : Z) (j2 : list byte) (lbfw : word) : list cell :=
[CB 1 [fl0]; CB 31 j1; C8 (Z_to_bv 64 WEND); C8 (Z_to_bv 64 WPOS); CB 96 j2; C4 lbfw].
Lemma gw_eq_FILE_cells : @FILE_cells = ltac:(GwInst.gw_term (@QQLG.Mq7.FILE_cells) (@FILE_cells)). Proof. unfold FILE_cells, QQLG.Mq7.FILE_cells; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_FILE_cells : gw_eqs.

Definition wfile (m : word -> option byte) (Fp : Z) (fl0 : byte) (j1 j2 : list byte) (lbfw : word)
(B : Z) (content junk : list byte) : Prop :=
rw_cells rsegs m Fp (FILE_cells fl0 j1 (B + Z.of_nat (length content) + Z.of_nat (length junk))
(B + Z.of_nat (length content)) j2 lbfw)
/\ rw_cells rsegs m B [CB (length content) content; CB (length junk) junk]
/\ Z.land (bv_unsigned fl0) 32 = 0%Z
/\ (2147483648 <= bv_unsigned lbfw mod 4294967296)%Z
/\ (0 < B)%Z /\ (B + Z.of_nat (length content) + Z.of_nat (length junk) < 2^64)%Z
/\ (Fp + 148 <= B \/ B + Z.of_nat (length content) + Z.of_nat (length junk) <= Fp)%Z.
Lemma gw_eq_wfile : @wfile = ltac:(GwInst.gw_term (@QQLG.Mq7.wfile rsegs) (@wfile)). Proof. unfold wfile, QQLG.Mq7.wfile; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_wfile : gw_eqs.

Definition fwritex_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(Fp : Z) (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (B : Z) (content junk : list byte)
(S : Z) (bs : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.of_nat (length bs))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(bv_unsigned sp - 64, bv_unsigned sp);
(B + Z.of_nat (length content), B + Z.of_nat (length content) + Z.of_nat (length bs));
(Fp + 40, Fp + 48)]%Z m m'
/\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' (bv_unsigned sp - 64) (bv_unsigned sp)
/\ wfile m' Fp fl0 j1 j2 lbfw B (content ++ bs) (skipn (length bs) junk)
/\ bytes_at rsegs m' S bs.
Lemma gw_eq_fwritex_post : @fwritex_post = ltac:(GwInst.gw_term (@QQLG.Mq7.fwritex_post rsegs) (@fwritex_post)). Proof. unfold fwritex_post, QQLG.Mq7.fwritex_post; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_fwritex_post : gw_eqs.

Local Definition gwt_X : unit := (Q6nq.gwt_def (@QVbl.Mq3.memcpy_post) (@U4l4.memcpy_post) (Q6nq.gwt_def (@QQLG.Mq7.memcpy_post) (@U4l4.memcpy_post) Q6nq.gwt_nil)).
Lemma wr_at_app : ltac2:(Q6nq.tyx '(@QQLG.Mq7.wr_at_app) [[@gw_eq_fwritex_entry__3; @gw_eq_fwritex_entry__2; @gw_eq_fwritex_entry]; [@gw_eq_FILE_cells__3; @gw_eq_FILE_cells__2; @gw_eq_FILE_cells]; [@gw_eq_wfile__3; @gw_eq_wfile__2; @gw_eq_wfile]; [@gw_eq_fwritex_post__3; @gw_eq_fwritex_post__2; @gw_eq_fwritex_post]] '(@nil Z) 'gwt_X).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QQLG.Mq7.wr_at_app). Qed.

Lemma rw_cells_app : ltac2:(Q6nq.tyx '(@QQLG.Mq7.rw_cells_app) [[@gw_eq_fwritex_entry__3; @gw_eq_fwritex_entry__2; @gw_eq_fwritex_entry]; [@gw_eq_FILE_cells__3; @gw_eq_FILE_cells__2; @gw_eq_FILE_cells]; [@gw_eq_wfile__3; @gw_eq_wfile__2; @gw_eq_wfile]; [@gw_eq_fwritex_post__3; @gw_eq_fwritex_post__2; @gw_eq_fwritex_post]] '(@nil Z) 'gwt_X).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QQLG.Mq7.rw_cells_app). Qed.

Lemma sx32_neg : ltac2:(Q6nq.tyx '(@QQLG.Mq7.sx32_neg) [[@gw_eq_fwritex_entry__3; @gw_eq_fwritex_entry__2; @gw_eq_fwritex_entry]; [@gw_eq_FILE_cells__3; @gw_eq_FILE_cells__2; @gw_eq_FILE_cells]; [@gw_eq_wfile__3; @gw_eq_wfile__2; @gw_eq_wfile]; [@gw_eq_fwritex_post__3; @gw_eq_fwritex_post__2; @gw_eq_fwritex_post]] '([2147483648; 4294967296; 9223372036854775808]%Z : list Z) '(Q6nq.gwt_unf (@SIGN64) gwt_X)).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QQLG.Mq7.sx32_neg). Qed.

Definition memcpy_postZ (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(D : Z) (a1 a2 : word) (src : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(D, D + bv_unsigned a2)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rw_cells rsegs m' D [CB (Z.to_nat (bv_unsigned a2)) src]
/\ bytes_at rsegs m' (bv_unsigned a1) src.
Lemma gw_eq_memcpy_postZ : @memcpy_postZ = ltac:(GwInst.gw_term (@QQLG.Mq7.memcpy_postZ rsegs) (@memcpy_postZ)). Proof. unfold memcpy_postZ, QQLG.Mq7.memcpy_postZ; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_memcpy_postZ : gw_eqs.
Lemma memcpy_callZ : ltac2:(Q6nq.ty1 'GwI.segs '(@QQLG.Mq7.memcpy_callZ) [[@gw_eq_fwritex_entry__3; @gw_eq_fwritex_entry__2; @gw_eq_fwritex_entry]; [@gw_eq_FILE_cells__3; @gw_eq_FILE_cells__2; @gw_eq_FILE_cells]; [@gw_eq_wfile__3; @gw_eq_wfile__2; @gw_eq_wfile]; [@gw_eq_fwritex_post__3; @gw_eq_fwritex_post__2; @gw_eq_fwritex_post]; [@gw_eq_memcpy_postZ__3; @gw_eq_memcpy_postZ__2; @gw_eq_memcpy_postZ]] '([390200]%Z : list Z) '(Q6nq.gwt_unf (@memcpy_entry) gwt_X)).
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QQLG.Mq7.memcpy_callZ). Qed.

Ltac unwrap_in K := rewrite ?land_W64 in K; change (2^64)%Z with 18446744073709551616%Z in K; rewrite ?Z.mod_small in K by lia.

Lemma fwritex_spec : ltac2:(Q6nq.ty1 'GwI.segs '(@QQLG.Mq7.fwritex_spec) [[@gw_eq_fwritex_entry__3; @gw_eq_fwritex_entry__2; @gw_eq_fwritex_entry]; [@gw_eq_FILE_cells__3; @gw_eq_FILE_cells__2; @gw_eq_FILE_cells]; [@gw_eq_wfile__3; @gw_eq_wfile__2; @gw_eq_wfile]; [@gw_eq_fwritex_post__3; @gw_eq_fwritex_post__2; @gw_eq_fwritex_post]; [@gw_eq_memcpy_postZ__3; @gw_eq_memcpy_postZ__2; @gw_eq_memcpy_postZ]] '([148; 347936]%Z : list Z) '(Q6nq.gwt_unf (@fwritex_entry) gwt_X)).
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QQLG.Mq7.fwritex_spec). Qed.

Definition fwritex_postZ (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(Fp : Z) (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (B : Z) (content junk : list byte)
(S : Z) (bs : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.of_nat (length bs))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(q - 64, q);
(B + Z.of_nat (length content), B + Z.of_nat (length content) + Z.of_nat (length bs));
(Fp + 40, Fp + 48)]%Z m m'
/\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' (q - 64) q
/\ wfile m' Fp fl0 j1 j2 lbfw B (content ++ bs) (skipn (length bs) junk)
/\ bytes_at rsegs m' S bs.
Lemma gw_eq_fwritex_postZ : @fwritex_postZ = ltac:(GwInst.gw_term (@QQLG.Mq7.fwritex_postZ rsegs) (@fwritex_postZ)). Proof. unfold fwritex_postZ, QQLG.Mq7.fwritex_postZ; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_fwritex_postZ : gw_eqs.

Lemma fwritex_call : ltac2:(Q6nq.ty1 'GwI.segs '(@QQLG.Mq7.fwritex_call) [[@gw_eq_fwritex_entry__3; @gw_eq_fwritex_entry__2; @gw_eq_fwritex_entry]; [@gw_eq_FILE_cells__3; @gw_eq_FILE_cells__2; @gw_eq_FILE_cells]; [@gw_eq_wfile__3; @gw_eq_wfile__2; @gw_eq_wfile]; [@gw_eq_fwritex_post__3; @gw_eq_fwritex_post__2; @gw_eq_fwritex_post]; [@gw_eq_memcpy_postZ__3; @gw_eq_memcpy_postZ__2; @gw_eq_memcpy_postZ]; [@gw_eq_fwritex_postZ__3; @gw_eq_fwritex_postZ__2; @gw_eq_fwritex_postZ]] '([148; 347936]%Z : list Z) '(Q6nq.gwt_unf (@fwritex_entry) gwt_X)).
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QQLG.Mq7.fwritex_call). Qed.
