(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxMem FxFold FxRgs FxFacts FxImg FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxLoop.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFold OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.

Module FxQChk.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition zeros8 : list byte := List.repeat (Z_to_bv 8 0) 8.
Lemma bytes_le_zeros8 : bytes_le_to_Z zeros8 = 0. Proof. reflexivity. Qed.

Ltac neq := first [assumption | apply not_eq_sym; assumption].
Ltac gsimp := repeat first [ rewrite getr_same by neq | rewrite getr_other by neq ].
Ltac nz_if := match goal with |- context [if bv_eqb ?r 0 then _ else _] =>
                replace (bv_eqb r 0%bv) with false by (symmetry; apply bv_eqb_neq; neq) end.

Section QC.
Context {fx : FPState}.
Variable segs : list Segment.
Variables (pc0 : Z) (rP rA rB rS rY rZ rW : reg) (ai : bv 20) (im1 : bv 12) (bim : bv 13) (beq : bool).
Hypothesis Hnz : rP <> 0%bv /\ rA <> 0%bv /\ rY <> 0%bv /\ rZ <> 0%bv /\ rW <> 0%bv.
Hypothesis Hd1 : rA <> rP /\ rY <> rP /\ rY <> rA /\ rZ <> rP /\ rZ <> rA /\ rZ <> rY /\ rW <> rP /\ rW <> rA /\ rW <> rY /\ rW <> rZ.
Hypothesis Hd2 : rB <> rP /\ rB <> rA /\ rB <> rY /\ rS <> rP.

Definition qpc (k : Z) : word := Z_to_bv 64 (pc0 + 4 * k).
Definition qins (k : Z) (i : instr) : Prop :=
  exists w, fetch_word segs (qpc k) = Some w /\ is_ecall w = false /\ decode_any w = Some (i, 4%Z).
Hypothesis I0 : qins 0 (Auipc rP ai).
Hypothesis I1 : qins 1 (Load SZ8 true rP rP im1).
Hypothesis I2 : qins 2 (Op ALU_ADD rA rB rS).
Hypothesis I3 : qins 3 (Load SZ8 true rY rP (Z_to_bv 12 0)).
Hypothesis I4 : qins 4 (ShiftImm ALU_SRL rP rB (Z_to_bv 6 3)).
Hypothesis I5 : qins 5 (OpImm ALU_ADD rA rA (Z_to_bv 12 (-1))).
Hypothesis I6 : qins 6 (ShiftImm ALU_SRL rZ rA (Z_to_bv 6 3)).
Hypothesis I7 : qins 7 (Op ALU_ADD rP rY rP).
Hypothesis I8 : qins 8 (Op ALU_ADD rY rY rZ).
Hypothesis I9 : qins 9 (OpImm ALU_AND rZ rP (Z_to_bv 12 (-8))).
Hypothesis I10 : qins 10 (OpImm ALU_AND rW rY (Z_to_bv 12 (-8))).
Hypothesis I11 : qins 11 (Load SZ8 true rZ rZ (Z_to_bv 12 0)).
Hypothesis I12 : qins 12 (Load SZ8 true rW rW (Z_to_bv 12 0)).
Hypothesis I13 : qins 13 (Op ALU_OR rZ rW rZ).
Hypothesis I14 : qins 14 (Branch (if beq then BC_EQ else BC_NE) rZ (Z_to_bv 5 0) bim).

(* [comment removed for export] *)
Definition qok : word := if beq then btgt (qpc 14) (bv_signed bim) else qpc 15.
(* [comment removed for export] *)
Definition qG : word := v_addi (v_auipc (qpc 0) (Z.shiftl (bv_signed ai) 12)) (bv_signed im1).
Definition qlast (b : word) (n : Z) : word := v_addi (v_add b (Z_to_bv 64 n)) (-1).
Definition qX (sh b : word) : word := v_add sh (v_srli b 3).
Definition qY (sh b : word) (n : Z) : word := v_add sh (v_srli (qlast b n) 3).
Definition qw1 (sh b : word) : word := v_andi (qX sh b) (-8).
Definition qw2 (sh b : word) (n : Z) : word := v_andi (qY sh b n) (-8).

#[using="Type"] Lemma qpc_succ : forall k, v_addi (qpc k) 4 = qpc (k + 1).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros k. unfold v_addi, qpc. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.
#[using="Type"] Lemma v_addi0 : forall x : word, v_addi x 0 = x.
Proof. LiaFast.lf_pins LiaFast.u0. intros x. unfold v_addi. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.



(* [comment removed for export] *)
#[using="Hnz Hd1 Hd2 I0 I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 I13 I14"] Theorem qc_isteps : forall regs mem rom (b : word) (n : Z) (P sh : word) bsG bsP,
  getr regs rB = b -> getr regs rS = Z_to_bv 64 n ->
  rdn segs mem qG 8 = Some bsG -> bytes_le_to_Z bsG = bv_unsigned P ->
  rdn segs mem P 8 = Some bsP -> bytes_le_to_Z bsP = bv_unsigned sh ->
  rdn segs mem (qw1 sh b) 8 = Some zeros8 -> rdn segs mem (qw2 sh b n) 8 = Some zeros8 ->
  exists regs',
    FxStep.isteps segs (mkst regs (qpc 0) mem rom) (mkst regs' qok mem rom) /\
    getr regs' rP = qX sh b /\ getr regs' rY = qY sh b n /\ getr regs' rA = qlast b n /\
    getr regs' rZ = Z_to_bv 64 0 /\ getr regs' rW = Z_to_bv 64 0 /\
    (forall r, r <> rP -> r <> rA -> r <> rY -> r <> rZ -> r <> rW -> getr regs' r = getr regs r).
Proof. LiaFast.lf_pins (fun (Hnz Hd1 Hd2 I0 I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 I13 I14 : LiaFast.U) => LiaFast.u0).
  intros regs mem rom b n P sh bsG bsP HB HS HG HGv HP HPv HW1 HW2.
  destruct Hnz as (NP & NA & NY & NZ & NW).
  destruct Hd1 as (DAP & DYP & DYA & DZP & DZA & DZY & DWP & DWA & DWY & DWZ).
  destruct Hd2 as (DBP & DBA & DBY & DSP).
  destruct I0 as (w0 & F0 & E0 & D0). destruct I1 as (w1 & F1 & E1 & D1). destruct I2 as (w2 & F2 & E2 & D2).
  destruct I3 as (w3 & F3 & E3 & D3). destruct I4 as (w4 & F4 & E4 & D4). destruct I5 as (w5 & F5 & E5 & D5).
  destruct I6 as (w6 & F6 & E6 & D6). destruct I7 as (w7 & F7 & E7 & D7). destruct I8 as (w8 & F8 & E8 & D8).
  destruct I9 as (w9 & F9 & E9 & D9). destruct I10 as (w10 & F10 & E10 & D10). destruct I11 as (w11 & F11 & E11 & D11).
  destruct I12 as (w12 & F12 & E12 & D12). destruct I13 as (w13 & F13 & E13 & D13). destruct I14 as (w14 & F14 & E14 & D14).
  (* [comment removed for export] *)
  set (r1 := regupd regs rP (v_auipc (qpc 0) (Z.shiftl (bv_signed ai) 12))).
  assert (S0 : RiscvSemantics.step segs (mkst regs (qpc 0) mem rom) = MachineOk (mkst r1 (qpc 1) mem rom)).
  { rewrite (step_auipc segs regs (qpc 0) mem rom w0 rP ai F0 E0 D0). nz_if. rewrite qpc_succ. reflexivity. }
  (* [comment removed for export] *)
  set (r2 := regupd r1 rP P).
  assert (S1 : RiscvSemantics.step segs (mkst r1 (qpc 1) mem rom) = MachineOk (mkst r2 (qpc 2) mem rom)).
  { rewrite (step_ld segs r1 (qpc 1) mem rom w1 rP rP im1 bsG P F1 E1 D1).
    - nz_if. rewrite qpc_succ. reflexivity.
    - unfold r1. gsimp. exact HG.
    - exact HGv. }
  (* [comment removed for export] *)
  set (r3 := regupd r2 rA (v_add b (Z_to_bv 64 n))).
  assert (S2 : RiscvSemantics.step segs (mkst r2 (qpc 2) mem rom) = MachineOk (mkst r3 (qpc 3) mem rom)).
  { rewrite (step_add segs r2 (qpc 2) mem rom w2 rA rB rS F2 E2 D2). nz_if. rewrite qpc_succ.
    unfold r3, r2, r1. gsimp. rewrite HB, HS. reflexivity. }
  (* [comment removed for export] *)
  set (r4 := regupd r3 rY sh).
  assert (S3 : RiscvSemantics.step segs (mkst r3 (qpc 3) mem rom) = MachineOk (mkst r4 (qpc 4) mem rom)).
  { rewrite (step_ld segs r3 (qpc 3) mem rom w3 rY rP (Z_to_bv 12 0) bsP sh F3 E3 D3).
    - nz_if. rewrite qpc_succ. reflexivity.
    - unfold r3, r2. gsimp. change (bv_signed (Z_to_bv 12 0)) with 0. rewrite v_addi0. exact HP.
    - exact HPv. }
  (* [comment removed for export] *)
  set (r5 := regupd r4 rP (v_srli b 3)).
  assert (S4 : RiscvSemantics.step segs (mkst r4 (qpc 4) mem rom) = MachineOk (mkst r5 (qpc 5) mem rom)).
  { rewrite (step_srli segs r4 (qpc 4) mem rom w4 rP rB (Z_to_bv 6 3) F4 E4 D4). nz_if. rewrite qpc_succ.
    unfold r5, r4, r3, r2, r1. gsimp. rewrite HB. reflexivity. }
  (* [comment removed for export] *)
  set (r6 := regupd r5 rA (qlast b n)).
  assert (S5 : RiscvSemantics.step segs (mkst r5 (qpc 5) mem rom) = MachineOk (mkst r6 (qpc 6) mem rom)).
  { rewrite (step_addi segs r5 (qpc 5) mem rom w5 rA rA (Z_to_bv 12 (-1)) F5 E5 D5). nz_if. rewrite qpc_succ.
    unfold r6, r5, r4, r3. gsimp. reflexivity. }
  (* [comment removed for export] *)
  set (r7 := regupd r6 rZ (v_srli (qlast b n) 3)).
  assert (S6 : RiscvSemantics.step segs (mkst r6 (qpc 6) mem rom) = MachineOk (mkst r7 (qpc 7) mem rom)).
  { rewrite (step_srli segs r6 (qpc 6) mem rom w6 rZ rA (Z_to_bv 6 3) F6 E6 D6). nz_if. rewrite qpc_succ.
    unfold r7, r6. gsimp. reflexivity. }
  (* [comment removed for export] *)
  set (r8 := regupd r7 rP (qX sh b)).
  assert (S7 : RiscvSemantics.step segs (mkst r7 (qpc 7) mem rom) = MachineOk (mkst r8 (qpc 8) mem rom)).
  { rewrite (step_add segs r7 (qpc 7) mem rom w7 rP rY rP F7 E7 D7). nz_if. rewrite qpc_succ.
    unfold r8, r7, r6, r5, r4. gsimp. reflexivity. }
  (* [comment removed for export] *)
  set (r9 := regupd r8 rY (qY sh b n)).
  assert (S8 : RiscvSemantics.step segs (mkst r8 (qpc 8) mem rom) = MachineOk (mkst r9 (qpc 9) mem rom)).
  { rewrite (step_add segs r8 (qpc 8) mem rom w8 rY rY rZ F8 E8 D8). nz_if. rewrite qpc_succ.
    unfold r9, r8, r7, r6, r5, r4. gsimp. reflexivity. }
  (* [comment removed for export] *)
  set (r10 := regupd r9 rZ (qw1 sh b)).
  assert (S9 : RiscvSemantics.step segs (mkst r9 (qpc 9) mem rom) = MachineOk (mkst r10 (qpc 10) mem rom)).
  { rewrite (step_andi segs r9 (qpc 9) mem rom w9 rZ rP (Z_to_bv 12 (-8)) F9 E9 D9). nz_if. rewrite qpc_succ.
    unfold r10, r9, r8. gsimp. reflexivity. }
  (* [comment removed for export] *)
  set (r11 := regupd r10 rW (qw2 sh b n)).
  assert (S10 : RiscvSemantics.step segs (mkst r10 (qpc 10) mem rom) = MachineOk (mkst r11 (qpc 11) mem rom)).
  { rewrite (step_andi segs r10 (qpc 10) mem rom w10 rW rY (Z_to_bv 12 (-8)) F10 E10 D10). nz_if. rewrite qpc_succ.
    unfold r11, r10, r9. gsimp. reflexivity. }
  (* [comment removed for export] *)
  set (r12 := regupd r11 rZ (Z_to_bv 64 0)).
  assert (S11 : RiscvSemantics.step segs (mkst r11 (qpc 11) mem rom) = MachineOk (mkst r12 (qpc 12) mem rom)).
  { rewrite (step_ld segs r11 (qpc 11) mem rom w11 rZ rZ (Z_to_bv 12 0) zeros8 (Z_to_bv 64 0) F11 E11 D11).
    - nz_if. rewrite qpc_succ. reflexivity.
    - unfold r11, r10. gsimp. change (bv_signed (Z_to_bv 12 0)) with 0. rewrite v_addi0. exact HW1.
    - reflexivity. }
  (* [comment removed for export] *)
  set (r13 := regupd r12 rW (Z_to_bv 64 0)).
  assert (S12 : RiscvSemantics.step segs (mkst r12 (qpc 12) mem rom) = MachineOk (mkst r13 (qpc 13) mem rom)).
  { rewrite (step_ld segs r12 (qpc 12) mem rom w12 rW rW (Z_to_bv 12 0) zeros8 (Z_to_bv 64 0) F12 E12 D12).
    - nz_if. rewrite qpc_succ. reflexivity.
    - unfold r12, r11. gsimp. change (bv_signed (Z_to_bv 12 0)) with 0. rewrite v_addi0. exact HW2.
    - reflexivity. }
  (* [comment removed for export] *)
  set (r14 := regupd r13 rZ (Z_to_bv 64 0)).
  assert (S13 : RiscvSemantics.step segs (mkst r13 (qpc 13) mem rom) = MachineOk (mkst r14 (qpc 14) mem rom)).
  { rewrite (step_or segs r13 (qpc 13) mem rom w13 rZ rW rZ F13 E13 D13). nz_if. rewrite qpc_succ.
    unfold r14, r13, r12. gsimp. reflexivity. }
  (* [comment removed for export] *)
  assert (Hz : getr r14 rZ = Z_to_bv 64 0) by (unfold r14; gsimp; reflexivity).
  assert (Hz0 : getr r14 (Z_to_bv 5 0) = Z_to_bv 64 0) by reflexivity.
  assert (S14 : RiscvSemantics.step segs (mkst r14 (qpc 14) mem rom) = MachineOk (mkst r14 qok mem rom)).
  { unfold qok. destruct beq.
    - rewrite (step_beq_tk segs r14 (qpc 14) mem rom w14 rZ (Z_to_bv 5 0) bim F14 E14 D14); [reflexivity|].
      rewrite Hz, Hz0. reflexivity.
    - rewrite (step_bne_ft segs r14 (qpc 14) mem rom w14 rZ (Z_to_bv 5 0) bim F14 E14 D14); [rewrite qpc_succ; reflexivity|].
      rewrite Hz, Hz0. reflexivity. }
  exists r14. split.
  - repeat (eapply FxStep.ist_step; [reflexivity | eassumption |]). apply FxStep.ist_refl.
  - unfold r14, r13, r12, r11, r10, r9, r8, r7, r6, r5, r4, r3, r2, r1.
    split; [gsimp; reflexivity|]. split; [gsimp; reflexivity|]. split; [gsimp; reflexivity|].
    split; [gsimp; reflexivity|]. split; [gsimp; reflexivity|].
    intros r H1 H2 H3 H4 H5. gsimp. reflexivity.
Qed.
End QC.

(* [comment removed for export] *)
Section QC2.
Context {fx : FPState}.
Variable segs : list Segment.
Variables (pc0 : Z) (rP rA rB rY rZ rW : reg) (ord : bool) (bim : bv 13) (beq : bool).
Hypothesis Hnz : rP <> 0%bv /\ rA <> 0%bv /\ rY <> 0%bv /\ rZ <> 0%bv /\ rW <> 0%bv.
Hypothesis Hd1 : rA <> rP /\ rY <> rP /\ rY <> rA /\ rZ <> rP /\ rZ <> rA /\ rZ <> rY /\ rW <> rP /\ rW <> rA /\ rW <> rY /\ rW <> rZ.
Hypothesis Hd2 : rB <> rP /\ rB <> rA /\ rB <> rY.
Hypothesis I0 : qins segs pc0 0 (Load SZ8 true rY rP (Z_to_bv 12 0)).
Hypothesis I1 : qins segs pc0 1 (if ord then ShiftImm ALU_SRL rP rB (Z_to_bv 6 3) else OpImm ALU_ADD rA rA (Z_to_bv 12 (-1))).
Hypothesis I2 : qins segs pc0 2 (if ord then OpImm ALU_ADD rA rA (Z_to_bv 12 (-1)) else ShiftImm ALU_SRL rP rB (Z_to_bv 6 3)).
Hypothesis I3 : qins segs pc0 3 (ShiftImm ALU_SRL rZ rA (Z_to_bv 6 3)).
Hypothesis I4 : qins segs pc0 4 (Op ALU_ADD rP rY rP).
Hypothesis I5 : qins segs pc0 5 (Op ALU_ADD rY rY rZ).
Hypothesis I6 : qins segs pc0 6 (OpImm ALU_AND rZ rP (Z_to_bv 12 (-8))).
Hypothesis I7 : qins segs pc0 7 (OpImm ALU_AND rW rY (Z_to_bv 12 (-8))).
Hypothesis I8 : qins segs pc0 8 (Load SZ8 true rZ rZ (Z_to_bv 12 0)).
Hypothesis I9 : qins segs pc0 9 (Load SZ8 true rW rW (Z_to_bv 12 0)).
Hypothesis I10 : qins segs pc0 10 (Op ALU_OR rZ rW rZ).
Hypothesis I11 : qins segs pc0 11 (Branch (if beq then BC_EQ else BC_NE) rZ (Z_to_bv 5 0) bim).

Definition qok2 : word := if beq then btgt (qpc pc0 11) (bv_signed bim) else qpc pc0 12.

#[using="ord Hnz Hd1 Hd2 I0 I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11"] Theorem qc2_isteps : forall regs mem rom (b : word) (n : Z) (P sh : word) bsP,
  getr regs rB = b -> getr regs rP = P -> getr regs rA = v_add b (Z_to_bv 64 n) ->
  rdn segs mem P 8 = Some bsP -> bytes_le_to_Z bsP = bv_unsigned sh ->
  rdn segs mem (qw1 sh b) 8 = Some zeros8 -> rdn segs mem (qw2 sh b n) 8 = Some zeros8 ->
  exists regs',
    FxStep.isteps segs (mkst regs (qpc pc0 0) mem rom) (mkst regs' qok2 mem rom) /\
    getr regs' rP = qX sh b /\ getr regs' rY = qY sh b n /\ getr regs' rA = qlast b n /\
    getr regs' rZ = Z_to_bv 64 0 /\ getr regs' rW = Z_to_bv 64 0 /\
    (forall r, r <> rP -> r <> rA -> r <> rY -> r <> rZ -> r <> rW -> getr regs' r = getr regs r).
Proof. LiaFast.lf_pins (fun (ord Hnz Hd1 Hd2 I0 I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 : LiaFast.U) => LiaFast.u0).
  intros regs mem rom b n P sh bsP HB HPr HA HP HPv HW1 HW2.
  destruct Hnz as (NP & NA & NY & NZ & NW).
  destruct Hd1 as (DAP & DYP & DYA & DZP & DZA & DZY & DWP & DWA & DWY & DWZ).
  destruct Hd2 as (DBP & DBA & DBY).
  destruct I0 as (w0 & F0 & E0 & D0). destruct I1 as (w1 & F1 & E1 & D1). destruct I2 as (w2 & F2 & E2 & D2).
  destruct I3 as (w3 & F3 & E3 & D3). destruct I4 as (w4 & F4 & E4 & D4). destruct I5 as (w5 & F5 & E5 & D5).
  destruct I6 as (w6 & F6 & E6 & D6). destruct I7 as (w7 & F7 & E7 & D7). destruct I8 as (w8 & F8 & E8 & D8).
  destruct I9 as (w9 & F9 & E9 & D9). destruct I10 as (w10 & F10 & E10 & D10). destruct I11 as (w11 & F11 & E11 & D11).
  (* [comment removed for export] *)
  set (r1 := regupd regs rY sh).
  assert (S0 : RiscvSemantics.step segs (mkst regs (qpc pc0 0) mem rom) = MachineOk (mkst r1 (qpc pc0 1) mem rom)).
  { rewrite (step_ld segs regs (qpc pc0 0) mem rom w0 rY rP (Z_to_bv 12 0) bsP sh F0 E0 D0).
    - nz_if. rewrite qpc_succ. reflexivity.
    - rewrite HPr. change (bv_signed (Z_to_bv 12 0)) with 0. rewrite v_addi0. exact HP.
    - exact HPv. }
  (* [comment removed for export] *)
  assert (S12 : exists r3, FxStep.isteps segs (mkst r1 (qpc pc0 1) mem rom) (mkst r3 (qpc pc0 3) mem rom) /\
            getr r3 rP = v_srli b 3 /\ getr r3 rA = qlast b n /\ (forall r, r <> rP -> r <> rA -> getr r3 r = getr r1 r)).
  { destruct ord.
    - set (ra1 := regupd r1 rP (v_srli b 3)). set (ra2 := regupd ra1 rA (qlast b n)).
      assert (Sa : RiscvSemantics.step segs (mkst r1 (qpc pc0 1) mem rom) = MachineOk (mkst ra1 (qpc pc0 2) mem rom)).
      { rewrite (step_srli segs r1 (qpc pc0 1) mem rom w1 rP rB (Z_to_bv 6 3) F1 E1 D1). nz_if. rewrite qpc_succ.
        unfold ra1, r1. gsimp. rewrite HB. reflexivity. }
      assert (Sb : RiscvSemantics.step segs (mkst ra1 (qpc pc0 2) mem rom) = MachineOk (mkst ra2 (qpc pc0 3) mem rom)).
      { rewrite (step_addi segs ra1 (qpc pc0 2) mem rom w2 rA rA (Z_to_bv 12 (-1)) F2 E2 D2). nz_if. rewrite qpc_succ.
        unfold ra2, ra1, r1. gsimp. rewrite HA. reflexivity. }
      exists ra2. split; [eapply FxStep.ist_step; [reflexivity | exact Sa|]; eapply FxStep.ist_step; [reflexivity | exact Sb|]; apply FxStep.ist_refl|].
      unfold ra2, ra1. split; [gsimp; reflexivity|]. split; [gsimp; reflexivity|]. intros r H1 H2. gsimp. reflexivity.
    - set (ra1 := regupd r1 rA (qlast b n)). set (ra2 := regupd ra1 rP (v_srli b 3)).
      assert (Sa : RiscvSemantics.step segs (mkst r1 (qpc pc0 1) mem rom) = MachineOk (mkst ra1 (qpc pc0 2) mem rom)).
      { rewrite (step_addi segs r1 (qpc pc0 1) mem rom w1 rA rA (Z_to_bv 12 (-1)) F1 E1 D1). nz_if. rewrite qpc_succ.
        unfold ra1, r1. gsimp. rewrite HA. reflexivity. }
      assert (Sb : RiscvSemantics.step segs (mkst ra1 (qpc pc0 2) mem rom) = MachineOk (mkst ra2 (qpc pc0 3) mem rom)).
      { rewrite (step_srli segs ra1 (qpc pc0 2) mem rom w2 rP rB (Z_to_bv 6 3) F2 E2 D2). nz_if. rewrite qpc_succ.
        unfold ra2, ra1, r1. gsimp. rewrite HB. reflexivity. }
      exists ra2. split; [eapply FxStep.ist_step; [reflexivity | exact Sa|]; eapply FxStep.ist_step; [reflexivity | exact Sb|]; apply FxStep.ist_refl|].
      unfold ra2, ra1. split; [gsimp; reflexivity|]. split; [gsimp; reflexivity|]. intros r H1 H2. gsimp. reflexivity. }
  destruct S12 as (r3 & Hs12 & G3P & G3A & G3o).
  assert (G3Y : getr r3 rY = sh) by (rewrite G3o by neq; unfold r1; gsimp; reflexivity).
  (* [comment removed for export] *)
  set (r4 := regupd r3 rZ (v_srli (qlast b n) 3)).
  assert (S3 : RiscvSemantics.step segs (mkst r3 (qpc pc0 3) mem rom) = MachineOk (mkst r4 (qpc pc0 4) mem rom)).
  { rewrite (step_srli segs r3 (qpc pc0 3) mem rom w3 rZ rA (Z_to_bv 6 3) F3 E3 D3). nz_if. rewrite qpc_succ. rewrite G3A. reflexivity. }
  (* [comment removed for export] *)
  set (r5 := regupd r4 rP (qX sh b)).
  assert (S4 : RiscvSemantics.step segs (mkst r4 (qpc pc0 4) mem rom) = MachineOk (mkst r5 (qpc pc0 5) mem rom)).
  { rewrite (step_add segs r4 (qpc pc0 4) mem rom w4 rP rY rP F4 E4 D4). nz_if. rewrite qpc_succ.
    unfold r5, r4. gsimp. rewrite G3Y, G3P. reflexivity. }
  set (r6 := regupd r5 rY (qY sh b n)).
  assert (S5 : RiscvSemantics.step segs (mkst r5 (qpc pc0 5) mem rom) = MachineOk (mkst r6 (qpc pc0 6) mem rom)).
  { rewrite (step_add segs r5 (qpc pc0 5) mem rom w5 rY rY rZ F5 E5 D5). nz_if. rewrite qpc_succ.
    unfold r6, r5, r4. gsimp. rewrite G3Y. reflexivity. }
  (* [comment removed for export] *)
  set (r7 := regupd r6 rZ (qw1 sh b)).
  assert (S6 : RiscvSemantics.step segs (mkst r6 (qpc pc0 6) mem rom) = MachineOk (mkst r7 (qpc pc0 7) mem rom)).
  { rewrite (step_andi segs r6 (qpc pc0 6) mem rom w6 rZ rP (Z_to_bv 12 (-8)) F6 E6 D6). nz_if. rewrite qpc_succ.
    unfold r7, r6, r5. gsimp. reflexivity. }
  set (r8 := regupd r7 rW (qw2 sh b n)).
  assert (S7 : RiscvSemantics.step segs (mkst r7 (qpc pc0 7) mem rom) = MachineOk (mkst r8 (qpc pc0 8) mem rom)).
  { rewrite (step_andi segs r7 (qpc pc0 7) mem rom w7 rW rY (Z_to_bv 12 (-8)) F7 E7 D7). nz_if. rewrite qpc_succ.
    unfold r8, r7, r6. gsimp. reflexivity. }
  (* [comment removed for export] *)
  set (r9 := regupd r8 rZ (Z_to_bv 64 0)).
  assert (S8 : RiscvSemantics.step segs (mkst r8 (qpc pc0 8) mem rom) = MachineOk (mkst r9 (qpc pc0 9) mem rom)).
  { rewrite (step_ld segs r8 (qpc pc0 8) mem rom w8 rZ rZ (Z_to_bv 12 0) zeros8 (Z_to_bv 64 0) F8 E8 D8).
    - nz_if. rewrite qpc_succ. reflexivity.
    - unfold r8, r7. gsimp. change (bv_signed (Z_to_bv 12 0)) with 0. rewrite v_addi0. exact HW1.
    - reflexivity. }
  set (r10 := regupd r9 rW (Z_to_bv 64 0)).
  assert (S9 : RiscvSemantics.step segs (mkst r9 (qpc pc0 9) mem rom) = MachineOk (mkst r10 (qpc pc0 10) mem rom)).
  { rewrite (step_ld segs r9 (qpc pc0 9) mem rom w9 rW rW (Z_to_bv 12 0) zeros8 (Z_to_bv 64 0) F9 E9 D9).
    - nz_if. rewrite qpc_succ. reflexivity.
    - unfold r9, r8. gsimp. change (bv_signed (Z_to_bv 12 0)) with 0. rewrite v_addi0. exact HW2.
    - reflexivity. }
  (* [comment removed for export] *)
  set (r11 := regupd r10 rZ (Z_to_bv 64 0)).
  assert (S10 : RiscvSemantics.step segs (mkst r10 (qpc pc0 10) mem rom) = MachineOk (mkst r11 (qpc pc0 11) mem rom)).
  { rewrite (step_or segs r10 (qpc pc0 10) mem rom w10 rZ rW rZ F10 E10 D10). nz_if. rewrite qpc_succ.
    unfold r11, r10, r9. gsimp. reflexivity. }
  assert (Hz : getr r11 rZ = Z_to_bv 64 0) by (unfold r11; gsimp; reflexivity).
  assert (Hz0 : getr r11 (Z_to_bv 5 0) = Z_to_bv 64 0) by reflexivity.
  assert (S11 : RiscvSemantics.step segs (mkst r11 (qpc pc0 11) mem rom) = MachineOk (mkst r11 qok2 mem rom)).
  { unfold qok2. destruct beq.
    - rewrite (step_beq_tk segs r11 (qpc pc0 11) mem rom w11 rZ (Z_to_bv 5 0) bim F11 E11 D11); [reflexivity|].
      rewrite Hz, Hz0. reflexivity.
    - rewrite (step_bne_ft segs r11 (qpc pc0 11) mem rom w11 rZ (Z_to_bv 5 0) bim F11 E11 D11); [rewrite qpc_succ; reflexivity|].
      rewrite Hz, Hz0. reflexivity. }
  exists r11. split.
  - eapply FxStep.ist_step; [reflexivity | exact S0|]. eapply FxStep.isteps_trans; [exact Hs12|].
    repeat (eapply FxStep.ist_step; [reflexivity | eassumption |]). apply FxStep.ist_refl.
  - unfold r11, r10, r9, r8, r7, r6, r5, r4.
    split; [gsimp; reflexivity|]. split; [gsimp; reflexivity|]. split; [gsimp; exact G3A|].
    split; [gsimp; reflexivity|]. split; [gsimp; reflexivity|].
    intros r H1 H2 H3 H4 H5. gsimp. rewrite (G3o r H1 H2). unfold r1. gsimp. reflexivity.
Qed.
End QC2.
End FxQChk.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint csuf_acc (a b : list fact) (acc : list fact) : list fact :=
  match a, b with
  | x :: a', y :: b' => if fact_eqb x y then csuf_acc a' b' acc else csuf_acc a' b' a'
  | _, _ => acc
  end.
Definition common_suffix (a b : list fact) : list fact :=
  let a' := skipn (length a - length b) a in
  let b' := skipn (length b - length a) b in
  csuf_acc a' b' a'.
(* [comment removed for export] *)
Fixpoint facts_eqb (a b : list fact) : bool :=
  match a, b with [], [] => true | x :: a', y :: b' => (fact_eqb x y && facts_eqb a' b')%bool | _, _ => false end.
Definition is_suffix (a b : list fact) : bool := facts_eqb a (skipn (length b - length a) b).

Definition rkind_eqb (a b : rkind) : bool :=
  match a, b with RW, RW | RO, RO | RZ, RZ | RI, RI | RT, RT => true | _, _ => false end.
Definition rsv_eqb (a b : rsv) : bool :=
  match a, b with RNone, RNone | RUnk, RUnk => true | RAt l, RAt l' => lin_eqb l l' | _, _ => false end.
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint cinter (t u : tree bval) : tree bval :=
  match t with
  | TEmpty => TEmpty
  | TNode l v r =>
      let '(ul, uv, ur) := tsplit u in
      TNode (cinter l ul) (match v, uv with Some x, Some y => if bval_eqb x y then Some x else None | _, _ => None end) (cinter r ur)
  end.
(* [comment removed for export] *)
Fixpoint teqb (t u : tree bval) : bool :=
  match t, u with
  | TEmpty, TEmpty => true
  | TNode l v r, TNode l' v' r' =>
      if (match v, v' with Some x, Some y => bval_eqb x y | None, None => true | _, _ => false end) then (if teqb l l' then teqb r r' else false) else false
  | _, _ => false
  end.
Definition gen_rg (R0 : region) (Rs : list region) : region :=
  let cont := List.fold_left (fun acc R => if teqb acc (rg_cont R) then acc else cinter acc (rg_cont R)) Rs (rg_cont R0) in
  let k0 := rg_kind R0 in
  let same := forallb (fun R => rkind_eqb (rg_kind R) k0) Rs in
  let P0 := RG (rg_base R0) (rg_size R0) k0 cont in
  let k := if same then (if forallb (fun R => rz_extra_ok R P0) (R0 :: Rs) then k0 else RW) else RW in
  RG (rg_base R0) (rg_size R0) k cont.
Fixpoint gen_rgs (r0 : list region) (rss : list (list region)) : list region :=
  match r0 with
  | [] => []
  | R0 :: r0' => gen_rg R0 (List.map (fun rs => List.hd R0 rs) rss) :: gen_rgs r0' (List.map (@List.tl region) rss)
  end.
Fixpoint gen_regs_n (Ls : list sst) (R0 : tree lin) (n0 : positive) (k : nat) (acc : tree lin) : tree lin :=
  match k with
  | O => acc
  | S k' => let key := Pos.of_succ_nat k in
            let v := rget R0 key in
            let v' := if forallb (fun L => lin_eqb (rget (s_regs L) key) v) Ls then v else lvar (n0 + key) in
            gen_regs_n Ls R0 n0 k' (rset acc key v')
  end.
Definition max_next (Ls : list sst) (n : positive) : positive := List.fold_left (fun m L => Pos.max m (s_next L)) Ls n.
(* [comment removed for export] *)
Fixpoint hull_facts (L0 : sst) (Ls : list sst) (n0 : positive) (k : nat) (acc : list fact) : list fact :=
  match k with
  | O => acc
  | S k' => let key := Pos.of_succ_nat k in let v := rget (s_regs L0) key in
            if forallb (fun L => lin_eqb (rget (s_regs L) key) v) Ls then hull_facts L0 Ls n0 k' acc
            else let r := List.fold_left (fun r L => let r' := irange (s_facts L) (rget (s_regs L) key) in
                                                    (Z.min (fst r) (fst r'), Z.max (snd r) (snd r'))) Ls (irange (s_facts L0) v) in
                 if (Z.eqb (fst r) 0 && Z.eqb (snd r) M64)%bool then hull_facts L0 Ls n0 k' acc
                 else hull_facts L0 Ls n0 k' (FRange (lvar (n0 + key)) (fst r) (snd r) :: acc)
  end.
(* [comment removed for export] *)
Definition gen2 (L0 : sst) (Ls : list sst) : sst * nat :=
  let n0 := max_next Ls (s_next L0) in
  let hf := hull_facts L0 Ls n0 31 [] in
  (SST (s_pc L0) (gen_regs_n Ls (s_regs L0) n0 31 TEmpty) (gen_rgs (s_rgs L0) (List.map s_rgs Ls))
      (hf ++ List.fold_left (fun fs L => common_suffix fs (s_facts L)) Ls (s_facts L0)) (n0 + 33)
      (if forallb (fun L => rsv_eqb (s_resv L) (s_resv L0)) Ls then s_resv L0 else RUnk), List.length hf).
Definition gen (L0 : sst) (Ls : list sst) : sst := fst (gen2 L0 Ls).
(* [comment removed for export] *)
Definition fixed_below (σ : tree lin) (n : positive) : bool := tforall (fun x l => (Pos.leb n x || lin_eqb l (lvar x))%bool) σ.
(* [comment removed for export] *)
Definition join_ent (L P : sst) (σ : tree lin) (n : positive) (k : nat) : bool :=
  (Z.eqb (s_pc L) (s_pc P) && regs_ent_n (s_regs L) (s_regs P) σ 31 && rgs_ent (s_rgs L) (s_rgs P) σ &&
   rsv_ent (s_resv L) (s_resv P) σ && facts_ent (s_facts L) (firstn k (s_facts P)) σ &&
   is_suffix (skipn k (s_facts P)) (s_facts L) && forallb (fwf n) (skipn k (s_facts P)) && fixed_below σ n)%bool.

(* [comment removed for export] *)
Fixpoint gen_w_regs (s0 s1 : sst) (n0 : positive) (k : nat) (acc : tree lin) : tree lin :=
  match k with
  | O => acc
  | S k' => let key := Pos.of_succ_nat k in let v := rget (s_regs s0) key in
            gen_w_regs s0 s1 n0 k' (rset acc key (if lin_eqb (rget (s_regs s1) key) v then v else lvar (n0 + key)))
  end.
(* [comment removed for export] *)
Fixpoint w_deltas (s0 s1 : sst) (k : nat) (acc : list (positive * Z)) : list (positive * Z) :=
  match k with
  | O => acc
  | S k' => let key := Pos.of_succ_nat k in
            let v0 := rget (s_regs s0) key in let v1 := rget (s_regs s1) key in
            if lin_eqb v1 v0 then w_deltas s0 s1 k' acc
            else match lin_off v1 v0 with Some d => w_deltas s0 s1 k' ((key, sgn64 d) :: acc) | None => w_deltas s0 s1 k' acc end
  end.
Definition w_rel (s0 : sst) (n0 z : positive) (dz lo hi : Z) (kd : positive * Z) : list fact :=
  let '(k, d) := kd in
  if Pos.eqb k z then []
  else let X := lvar (n0 + k) in let Zv := lvar (n0 + z) in
       let y0 := rget (s_regs s0) k in let z0 := rget (s_regs s0) z in
       if Z.eqb d (- dz) then [FRange (lsub (ladd X Zv) (ladd y0 z0)) 0 0]
       else if Z.eqb d dz then [FRange (lsub (lsub X Zv) (lsub y0 z0)) 0 0]
       else [].
Fixpoint pos_upto (k : nat) (acc : list positive) : list positive :=
  match k with O => acc | S k' => pos_upto k' (Pos.of_succ_nat k' :: acc) end.
(* [comment removed for export] *)
Fixpoint upto_asc (k : nat) (p : positive) : list positive := match k with O => [] | S k' => p :: upto_asc k' (Pos.succ p) end.
(* [comment removed for export] *)
Fixpoint w_delta_of (ds : list (positive * Z)) (k : positive) : option Z :=
  match ds with [] => None | (k', d) :: ds' => if Pos.eqb k k' then Some d else w_delta_of ds' k end.
Fixpoint gen_w_regs2 (s0 s1 : sst) (n0 z : positive) (dz : Z) (ds : list (positive * Z)) (k : nat) (acc : tree lin) : tree lin :=
  match k with
  | O => acc
  | S k' => let key := Pos.of_succ_nat k in let v := rget (s_regs s0) key in
            let zd := lsub (rget (s_regs s0) z) (lvar (n0 + z)) in
            let v' := if lin_eqb (rget (s_regs s1) key) v then v
                      else if Pos.eqb key z then lvar (n0 + z)
                      else match w_delta_of ds key with
                           | Some d => if Z.eqb d (- dz) then ladd v zd else if Z.eqb d dz then lsub v zd else lvar (n0 + key)
                           | None => lvar (n0 + key)
                           end in
            gen_w_regs2 s0 s1 n0 z dz ds k' (rset acc key v')
  end.
(* [comment removed for export] *)
Fixpoint w_end_c (s0 s1 : sst) (z0 : lin) (k : nat) (best : option (positive * Z)) : option (positive * Z) :=
  match k with
  | O => best
  | S k' => let key := Pos.of_succ_nat k in let v0 := rget (s_regs s0) key in
            if lin_eqb (rget (s_regs s1) key) v0 then
              match lin_off v0 z0 with
              | Some d => if (Z.ltb 0 d && Z.ltb d 4611686018427387904 &&
                              match best with Some (_, d') => Z.ltb d d' | None => true end)%bool
                          then w_end_c s0 s1 z0 k' (Some (key, d)) else w_end_c s0 s1 z0 k' best
              | None => w_end_c s0 s1 z0 k' best
              end
            else w_end_c s0 s1 z0 k' best
  end.
Fixpoint w_end_r (s0 s1 : sst) (z0 : lin) (k : nat) : option positive :=
  match k with
  | O => None
  | S k' => let key := Pos.of_succ_nat k in let v0 := rget (s_regs s0) key in
            if (lin_eqb (rget (s_regs s1) key) v0 && negb (Pos.eqb key 3))%bool then
              let '(lo, hi) := irange (s_facts s0) (lsub v0 z0) in
              if (Z.leb 1 lo && Z.ltb hi 4611686018427387904)%bool then Some key else w_end_r s0 s1 z0 k'
            else w_end_r s0 s1 z0 k'
  end.
Definition w_end (s0 s1 : sst) (z0 : lin) : option positive :=
  match w_end_c s0 s1 z0 31 None with Some (e, _) => Some e | None => w_end_r s0 s1 z0 31 end.

Definition widen (s0 s1 : sst) (fuel : nat) (wstops : list Z) : option loopspec :=
  let n0 := Pos.max (s_next s0) (s_next s1) in
  let ds := w_deltas s0 s1 31 [] in
  match List.find (fun '(_, d) => Z.ltb d 0) ds with
  | None =>
      (* [comment removed for export] *)
      match List.find (fun '(_, d) => Z.ltb 0 d) ds with
      | None => None
      | Some (z, dz) =>
          let z0 := rget (s_regs s0) z in
          match w_end s0 s1 z0 with
          | None => None
          | Some e =>
              let e0 := rget (s_regs s0) e in let Zv := lvar (n0 + z) in
              let '(lo0, hi) := irange (s_facts s0) (lsub e0 z0) in
              let fs := FRange (lsub e0 Zv) 1 hi :: FRange (lsub Zv z0) 0 (hi - 1) :: common_suffix (s_facts s0) (s_facts s1) in
              let P := SST (s_pc s0) (gen_w_regs2 s0 s1 n0 z dz ds 31 TEmpty) (gen_rgs (s_rgs s0) [s_rgs s1]) fs (n0 + 33)
                           (if rsv_eqb (s_resv s1) (s_resv s0) then s_resv s0 else RUnk) in
              Some (LS P (lsub e0 Zv) (upto_asc (Pos.to_nat (s_next s0) - 1) 1) fuel wstops)
          end
      end
  | Some (z, dz) =>
      let '(lo0, hi) := irange (s_facts s0) (rget (s_regs s0) z) in
      let lo := Z.min lo0 (- dz) in
      let m := Z.max (hi - lo) (snd (l_iv (s_facts s0) (rget (s_regs s0) z)) - lo) in
      let fs := FRange (lvar (n0 + z)) lo hi :: FRange (lsub (rget (s_regs s0) z) (lvar (n0 + z))) 0 m ::
                common_suffix (s_facts s0) (s_facts s1) in
      let P := SST (s_pc s0) (gen_w_regs2 s0 s1 n0 z dz ds 31 TEmpty) (gen_rgs (s_rgs s0) [s_rgs s1]) fs (n0 + 33)
                   (if rsv_eqb (s_resv s1) (s_resv s0) then s_resv s0 else RUnk) in
      Some (LS P (lvar (n0 + z)) (upto_asc (Pos.to_nat (s_next s0) - 1) 1) fuel wstops)
  end.

Inductive plan : Type :=
| PFin
| PRun (fuel : nat) (stops : list Z) (ks : list (Z * plan))
| PLoop (ls : loopspec) (ks : list (Z * plan))
| PJoin (fuel : nat) (stops : list Z) (jpc : Z) (pj : plan) (ks : list (Z * plan))
| PLoopW (fuel : nat) (wstops : list Z) (ks : list (Z * plan))
| PCases (x : lin) (lo hi : Z) (p : plan).

(* [comment removed for export] *)
Definition add_fact (s : sst) (f : fact) : sst := SST (s_pc s) (s_regs s) (s_rgs s) (f :: s_facts s) (s_next s) (s_resv s).
Fixpoint z_upto (k : nat) (lo : Z) (acc : list Z) : list Z :=
  match k with O => acc | S k' => z_upto k' lo ((lo + Z.of_nat k') :: acc) end.
(* [comment removed for export] *)
Fixpoint check_cases (chk : sst -> option (list sst)) (s : sst) (x : lin) (ks : list Z) : option (list sst) :=
  match ks with
  | [] => Some []
  | k :: ks' => match chk (add_fact s (FRange x k k)), check_cases chk s x ks' with
                | Some f1, Some f2 => Some (f1 ++ f2)
                | _, _ => None
                end
  end.

Section Check.
Variable t : tree xi.
Variable img : tree Z.
Variable ins : list positive.     (* [comment removed for export] *)

Fixpoint kfind (ks : list (Z * plan)) (pc : Z) : plan :=
  match ks with [] => PFin | (a, p) :: ks' => if Z.eqb a pc then p else kfind ks' pc end.

Definition ins_below (s : sst) : bool := forallb (fun x => Pos.ltb x (s_next s)) ins.
(* [comment removed for export] *)
Fixpoint shape_eqb (a b : list region) : bool :=
  match a, b with
  | [], [] => true
  | R :: a', R' :: b' => (lin_eqb (rg_base R) (rg_base R') && lin_eqb (rg_size R) (rg_size R') && shape_eqb a' b')%bool
  | _, _ => false
  end.
(* [comment removed for export] *)
Definition bases_params (ls : loopspec) : bool :=
  forallb (fun R => forallb (fun '(x, _) => existsb (Pos.eqb x) (ls_params ls)) (l_t (rg_base R) ++ l_t (rg_size R))) (s_rgs (ls_inv ls)).
Definition ins_in_params (ls : loopspec) : bool := forallb (fun x => existsb (Pos.eqb x) (ls_params ls)) ins.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition refine_ls (ls : loopspec) : loopspec :=
  let P := ls_inv ls in
  match List.find (fun L => Z.eqb (s_pc L) (s_pc P)) (loop_leaves t img ls) with
  | Some L => LS (SST (s_pc P) (s_regs P) (gen_rgs (s_rgs P) [s_rgs L]) (s_facts P) (s_next P) (s_resv P))
                 (ls_meas ls) (ls_params ls) (ls_fuel ls) (ls_stops ls)
  | None => ls
  end.
Fixpoint check_all (chk : plan -> sst -> option (list sst)) (ks : list (Z * plan)) (ls : list sst) : option (list sst) :=
  match ls with
  | [] => Some []
  | L :: ls' => match chk (kfind ks (s_pc L)) L with
                | Some f1 => match check_all chk ks ls' with Some f2 => Some (f1 ++ f2) | None => None end
                | None => None
                end
  end.

Fixpoint check (depth : nat) (p : plan) (s : sst) : option (list sst) :=
  match depth with
  | O => None
  | S d =>
      match p with
      | PFin => Some [s]
      | PRun fuel stops ks =>
          if ins_below s then check_all (check d) ks (fx_explore t img fuel stops s []) else None
      | PLoop ls ks =>
          let σ := match_st s (ls_inv ls) in
          if (entails s (ls_inv ls) σ && params_fixed σ ins && ins_in_params ls && bases_params ls && shape_eqb (s_rgs s) (s_rgs (ls_inv ls))
              && Pos.leb (s_next s) (s_next (ls_inv ls)))%bool then
            match loop_check t img ls with
            | Some exits => check_all (check d) ks exits
            | None => None
            end
          else None
      | PJoin fuel stops jpc pj ks =>
          if ins_below s then
            let Ls := fx_explore t img fuel (jpc :: stops) s [] in
            match check_all (check d) ks (List.filter (fun L => negb (Z.eqb (s_pc L) jpc)) Ls) with
            | Some fo =>
                let F := List.filter (fun L => negb (Z.eqb (s_pc L) jpc)) fo in
                match List.filter (fun L => Z.eqb (s_pc L) jpc) Ls ++ List.filter (fun L => Z.eqb (s_pc L) jpc) fo with
                | [] => Some F
                | L0 :: Lrs =>
                    let '(P, k) := gen2 L0 Lrs in
                    let n := max_next Lrs (s_next L0) in
                    if (state_wf P && forallb (fun L => let σ := match_st L P in (join_ent L P σ n k && params_fixed σ ins)%bool) (L0 :: Lrs)
                        && shape_eqb (s_rgs s) (s_rgs P) && Pos.leb (s_next s) (s_next P))%bool then
                      match check d pj P with
                      | Some f1 => Some (f1 ++ F)
                      | None => None
                      end
                    else None
                end
            | None => None
            end
          else None
      | PLoopW fuel wstops ks =>
          match List.find (fun L => Z.eqb (s_pc L) (s_pc s)) (fx_explore t img fuel (s_pc s :: wstops) s []) with
          | Some s1 => match widen s s1 fuel wstops with
                       | Some ls => match check d (PLoop ls ks) s with Some f => Some f | None => check d (PLoop (refine_ls ls) ks) s end
                       | None => None
                       end
          | None => None
          end
      | PCases x lo hi p =>
          let '(a, b) := irange (s_facts s) x in
          if (Z.leb lo a && Z.leb b hi && Z.leb (hi - lo) 255 && lwf (s_next s) x)%bool then
            check_cases (check d p) s x (z_upto (Z.to_nat (hi - lo + 1)) lo [])
          else None
      end
  end.
End Check.

Lemma check_all_sound : forall chk ks ls finals, check_all chk ks ls = Some finals ->
  forall L, In L ls -> exists f1, chk (kfind ks (s_pc L)) L = Some f1 /\ (forall x, In x f1 -> In x finals).
Proof.
  intros chk ks ls. induction ls as [|L0 ls IH]; intros finals H L HL; [destruct HL|].
  cbn [check_all] in H. destruct (chk (kfind ks (s_pc L0)) L0) as [f1|] eqn:H1; [|discriminate].
  destruct (check_all chk ks ls) as [f2|] eqn:H2; [|discriminate]. injection H as <-.
  destruct HL as [->|HL].
  - exists f1. split; [exact H1|]. intros x Hx. apply in_or_app. left. exact Hx.
  - destruct (IH f2 eq_refl L HL) as (f & Hf & Hsub). exists f. split; [exact Hf|]. intros x Hx. apply in_or_app. right. exact (Hsub x Hx).
Qed.

Lemma loop_check_wf : forall t img ls exits, loop_check t img ls = Some exits -> state_wf (ls_inv ls) = true.
Proof.
  intros t img ls exits H. unfold loop_check in H.
  destruct (state_wf (ls_inv ls) && lwf (s_next (ls_inv ls)) (ls_meas ls) && forallb (fun x => Pos.ltb x (s_next (ls_inv ls))) (ls_params ls))%bool eqn:Hw;
    [|discriminate].
  apply andb_prop in Hw as [Hw _]. apply andb_prop in Hw as [Hw _]. exact Hw.
Qed.

(* [comment removed for export] *)
Lemma facts_eqb_eq : forall a b, facts_eqb a b = true -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] H; cbn [facts_eqb] in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H1 H2]. rewrite (fact_eqb_eq _ _ H1), (IH _ H2). reflexivity.
Qed.
Lemma is_suffix_in : forall a b f, is_suffix a b = true -> In f a -> In f b.
Proof.
  intros a b f H Hf. unfold is_suffix in H. apply facts_eqb_eq in H. rewrite H in Hf.
  rewrite <- (firstn_skipn (length b - length a) b). apply in_or_app. right. exact Hf.
Qed.
Lemma fixed_below_agree : forall E σ n, fixed_below σ n = true -> agree n E (ecomp E σ).
Proof.
  intros E σ n H x Hx. unfold ecomp, svar. destruct (tget x σ) as [l|] eqn:Hg.
  - pose proof (tforall_spec _ _ H x l Hg) as Hl. cbn beta in Hl. apply orb_prop in Hl as [Hl|Hl].
    + apply Pos.leb_le in Hl. lia.
    + apply lin_eqb_eq in Hl. subst l. rewrite lden_lvar. reflexivity.
  - rewrite lden_lvar. reflexivity.
Qed.

Section WithSegs.
Variable segs : list Segment.

#[using="Type"] Theorem join_ent_sound : forall E L P σ n k ms, sden0 segs E L ms -> join_ent L P σ n k = true -> sden0 segs (ecomp E σ) P ms.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E L P σ n k ms (Hpc & Hsvc & Hresv & HR & HG & HD & HF & Hfrm) H. unfold join_ent in H.
  apply andb_prop in H as [H Hfix]. apply andb_prop in H as [H Hfw]. apply andb_prop in H as [H Hsuf].
  apply andb_prop in H as [H Hfe].
  apply andb_prop in H as [H Hv]. apply andb_prop in H as [H Hg]. apply andb_prop in H as [Hp Hr].
  apply Z.eqb_eq in Hp.
  split; [rewrite Hpc, Hp; reflexivity|]. split; [exact Hsvc|].
  split; [unfold rsv_ent in Hv; destruct (s_resv P) as [|l|]; destruct (s_resv L) as [|l'|]; cbn [rsv_ok] in *; try discriminate; try exact I;
          [exact Hresv | apply lin_eqb_eq in Hv; rewrite Hresv, Hv, lden_lsubst; reflexivity]|].
  split; [exact (regs_ent_ok _ _ _ _ _ HR Hr)|]. split; [exact (rgs_ent_ok segs _ _ _ _ _ HG Hg)|].
  split; [exact (rgs_ent_disj _ _ _ _ HD Hg)|]. split; [|exact Hfrm].
  rewrite <- (firstn_skipn k (s_facts P)). apply Forall_app. split; [exact (facts_ent_ok E (s_facts L) _ σ HF Hfe)|].
  apply Forall_forall. intros f Hf. rewrite Forall_forall in HF. pose proof (HF f (is_suffix_in _ _ _ Hsuf Hf)) as Hok.
  rewrite forallb_forall in Hfw. apply (fact_ok_agree n E (ecomp E σ) f (Hfw f Hf) (fixed_below_agree E σ n Hfix) Hok).
Qed.

#[using="Type"] Theorem check_sound_fp : forall t img ins depth p s finals,
  tbl_ok segs t -> img_ok segs img -> check t img ins depth p s = Some finals ->
  forall E ms, sden segs E s ms ->
  exists L ms' E', In L finals /\ isteps segs ms ms' /\ sden segs E' L ms' /\ (forall x, In x ins -> E' x = E x) /\ fpc t ms ms'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros t img ins depth. induction depth as [|d IH]; intros p s finals Ht Himg Hck E ms Hden; cbn [check] in Hck; [discriminate|].
  destruct p as [| fuel stops ks | ls ks | fuel stops jpc pj ks | fuel wstops ks | x lo hi p].
  - injection Hck as <-. exists s, ms, E. split; [left; reflexivity|]. split; [constructor|]. split; [exact Hden | split; [reflexivity | apply fpc_refl]].
  - destruct (ins_below ins s) eqn:Hins; [|discriminate].
    destruct (explore_sound_fp segs t img fuel stops s [] E ms Ht Himg Hden) as (L & ms1 & E1 & HL & Hst1 & Hd1 & Ha1 & Hfp1).
    destruct (check_all_sound _ _ _ _ Hck L HL) as (f1 & Hf1 & Hsub).
    destruct (IH _ _ _ Ht Himg Hf1 E1 ms1 Hd1) as (L2 & ms2 & E2 & HL2 & Hst2 & Hd2 & Hi2 & Hfp2).
    exists L2, ms2, E2. split; [exact (Hsub L2 HL2)|]. split; [eapply isteps_trans; [exact Hst1 | exact Hst2]|]. split; [exact Hd2|].
    split; [|exact (fpc_trans _ _ _ _ Hfp1 Hfp2)].
    intros x Hx. rewrite (Hi2 x Hx). symmetry. apply Ha1. unfold ins_below in Hins. rewrite forallb_forall in Hins.
    apply Pos.ltb_lt. exact (Hins x Hx).
  - set (σ := match_st s (ls_inv ls)) in Hck.
    destruct (entails s (ls_inv ls) σ && params_fixed σ ins && ins_in_params ins ls && bases_params ls && shape_eqb (s_rgs s) (s_rgs (ls_inv ls))
              && Pos.leb (s_next s) (s_next (ls_inv ls)))%bool eqn:He; [|discriminate].
    apply andb_prop in He as [He _]. apply andb_prop in He as [He _]. apply andb_prop in He as [He _]. apply andb_prop in He as [He Hpar]. apply andb_prop in He as [Hent Hfix].
    destruct (loop_check t img ls) as [exits|] eqn:Hlc; [|discriminate].
    pose proof (entails_sden segs E s (ls_inv ls) σ ms (sden_0 _ _ _ _ Hden) Hent (loop_check_wf _ _ _ _ Hlc)) as HdP.
    destruct (loop_sound_fp segs t img ls exits Ht Himg Hlc (ecomp E σ) ms HdP) as (L & ms1 & E1 & HL & Hst1 & Hd1 & Hp1 & Hfp1).
    destruct (check_all_sound _ _ _ _ Hck L HL) as (f1 & Hf1 & Hsub).
    destruct (IH _ _ _ Ht Himg Hf1 E1 ms1 Hd1) as (L2 & ms2 & E2 & HL2 & Hst2 & Hd2 & Hi2 & Hfp2).
    exists L2, ms2, E2. split; [exact (Hsub L2 HL2)|]. split; [eapply isteps_trans; [exact Hst1 | exact Hst2]|]. split; [exact Hd2|].
    split; [|exact (fpc_trans _ _ _ _ Hfp1 Hfp2)].
    intros x Hx. rewrite (Hi2 x Hx). unfold ins_in_params in Hpar. rewrite forallb_forall in Hpar.
    pose proof (Hpar x Hx) as Hxp. apply existsb_exists in Hxp as (y & Hy & Hxy). apply Pos.eqb_eq in Hxy. subst y.
    rewrite (Hp1 x Hy). apply (params_fixed_sound E σ ins x Hfix Hx).
  - (* [comment removed for export] *)
    destruct (ins_below ins s) eqn:Hins; [|discriminate].
    destruct (explore_sound_fp segs t img fuel (jpc :: stops) s [] E ms Ht Himg Hden) as (L & ms1 & E1 & HL & Hst1 & Hd1 & Ha1 & Hfp1).
    assert (Hin : forall x, In x ins -> E1 x = E x).
    { intros x Hx. symmetry. apply Ha1. unfold ins_below in Hins. rewrite forallb_forall in Hins. apply Pos.ltb_lt. exact (Hins x Hx). }
    set (Ls := fx_explore t img fuel (jpc :: stops) s []) in *.
    destruct (check_all (check t img ins d) ks (List.filter (fun L => negb (Z.eqb (s_pc L) jpc)) Ls)) as [fo|] eqn:Hfo; [|discriminate].
    (* [comment removed for export] *)
    assert (Hreach : exists L' ms' E', isteps segs ms ms' /\ sden segs E' L' ms' /\ (forall x, In x ins -> E' x = E x) /\ fpc t ms ms' /\
              ((Z.eqb (s_pc L') jpc = true /\ In L' (List.filter (fun L => Z.eqb (s_pc L) jpc) Ls ++ List.filter (fun L => Z.eqb (s_pc L) jpc) fo)) \/
               (Z.eqb (s_pc L') jpc = false /\ In L' fo))).
    { destruct (Z.eqb (s_pc L) jpc) eqn:Hpc.
      - exists L, ms1, E1. split; [exact Hst1|]. split; [exact Hd1|]. split; [exact Hin|]. split; [exact Hfp1|]. left. split; [exact Hpc|].
        apply in_or_app. left. apply filter_In. split; [exact HL | exact Hpc].
      - assert (HLo : In L (List.filter (fun L => negb (Z.eqb (s_pc L) jpc)) Ls)) by (apply filter_In; split; [exact HL | rewrite Hpc; reflexivity]).
        destruct (check_all_sound _ _ _ _ Hfo L HLo) as (f1 & Hf1 & Hsub).
        destruct (IH _ _ _ Ht Himg Hf1 E1 ms1 Hd1) as (L2 & ms2 & E2 & HL2 & Hst2 & Hd2 & Hi2 & Hfp2).
        exists L2, ms2, E2. split; [eapply isteps_trans; [exact Hst1 | exact Hst2]|]. split; [exact Hd2|].
        split; [intros x Hx; rewrite (Hi2 x Hx); exact (Hin x Hx)|]. split; [exact (fpc_trans _ _ _ _ Hfp1 Hfp2)|].
        destruct (Z.eqb (s_pc L2) jpc) eqn:Hpc2.
        + left. split; [reflexivity|]. apply in_or_app. right. apply filter_In. split; [exact (Hsub L2 HL2) | exact Hpc2].
        + right. split; [reflexivity | exact (Hsub L2 HL2)]. }
    destruct Hreach as (L' & ms' & E' & Hst' & Hd' & Hi' & Hfp' & Hcase).
    destruct (List.filter (fun L => Z.eqb (s_pc L) jpc) Ls ++ List.filter (fun L => Z.eqb (s_pc L) jpc) fo) as [|L0 Lrs] eqn:HJ.
    + injection Hck as <-. destruct Hcase as [(_ & Hn)|(Hpc' & Hfo')]; [destruct Hn|].
      exists L', ms', E'. split; [apply filter_In; split; [exact Hfo' | rewrite Hpc'; reflexivity]|]. split; [exact Hst'|]. split; [exact Hd' | split; [exact Hi' | exact Hfp']].
    + destruct (gen2 L0 Lrs) as [P k] eqn:Hgen. set (n := max_next Lrs (s_next L0)) in *.
      destruct (state_wf P && forallb (fun L => (join_ent L P (match_st L P) n k && params_fixed (match_st L P) ins)%bool) (L0 :: Lrs)
                && shape_eqb (s_rgs s) (s_rgs P) && Pos.leb (s_next s) (s_next P))%bool eqn:Hw;
        [|discriminate].
      apply andb_prop in Hw as [Hw _]. apply andb_prop in Hw as [Hw _].
      apply andb_prop in Hw as [Hwf Hall]. rewrite forallb_forall in Hall.
      destruct (check t img ins d pj P) as [f1|] eqn:Hf1; [|discriminate]. injection Hck as <-.
      destruct Hcase as [(Hpc' & HLJ)|(Hpc' & Hfo')].
      * pose proof (Hall L' HLJ) as HLe. apply andb_prop in HLe as [Hje Hfix].
        pose proof (sden0_sden segs P (ecomp E' (match_st L' P)) ms' Hwf (join_ent_sound E' L' P (match_st L' P) n k ms' (sden_0 _ _ _ _ Hd') Hje)) as HdP.
        destruct (IH _ _ _ Ht Himg Hf1 _ ms' HdP) as (L2 & ms2 & E2 & HL2 & Hst2 & Hd2 & Hi2 & Hfp2).
        exists L2, ms2, E2. split; [apply in_or_app; left; exact HL2|]. split; [eapply isteps_trans; [exact Hst' | exact Hst2]|].
        split; [exact Hd2|]. split; [|exact (fpc_trans _ _ _ _ Hfp' Hfp2)].
        intros x Hx. rewrite (Hi2 x Hx), (params_fixed_sound E' _ ins x Hfix Hx). exact (Hi' x Hx).
      * exists L', ms', E'. split; [apply in_or_app; right; apply filter_In; split; [exact Hfo' | rewrite Hpc'; reflexivity]|].
        split; [exact Hst'|]. split; [exact Hd' | split; [exact Hi' | exact Hfp']].
  - (* [comment removed for export] *)
    destruct (List.find (fun L => Z.eqb (s_pc L) (s_pc s)) (fx_explore t img fuel (s_pc s :: wstops) s [])) as [s1|]; [|discriminate].
    destruct (widen s s1 fuel wstops) as [ls|]; [|discriminate].
    destruct (check t img ins d (PLoop ls ks) s) as [f|] eqn:Hc1.
    + injection Hck as <-. exact (IH _ _ _ Ht Himg Hc1 E ms Hden).
    + exact (IH _ _ _ Ht Himg Hck E ms Hden).
  - (* [comment removed for export] *)
    destruct (irange (s_facts s) x) as [a b] eqn:Hir.
    destruct (Z.leb lo a && Z.leb b hi && Z.leb (hi - lo) 255 && lwf (s_next s) x)%bool eqn:Hc; [|discriminate].
    apply andb_prop in Hc as [Hc Hwx]. apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hla Hbh]. apply Z.leb_le in Hla, Hbh.
    pose proof (sden_0 _ _ _ _ Hden) as Hd0. destruct Hd0 as (_ & _ & _ & _ & _ & _ & HF & _).
    pose proof (irange_sound E (s_facts s) x HF) as Hr. rewrite Hir in Hr. cbn [fst snd] in Hr.
    set (k := bv_unsigned (lden E x)) in *.
    assert (Hk : In k (z_upto (Z.to_nat (hi - lo + 1)) lo [])).
    { assert (Hgen : forall n acc, In k acc \/ (lo <= k < lo + Z.of_nat n) -> In k (z_upto n lo acc)).
      { induction n as [|n IHn]; intros acc Hx; cbn [z_upto]; [destruct Hx as [Hx|Hx]; [exact Hx | lia]|].
        apply IHn. destruct Hx as [Hx|Hx]; [left; right; exact Hx|].
        destruct (Z.eq_dec k (lo + Z.of_nat n)) as [->|Hne]; [left; left; reflexivity | right; lia]. }
      apply Hgen. right. lia. }
    assert (Hcc : forall ks fin, check_cases (check t img ins d p) s x ks = Some fin -> In k ks ->
              exists f1, check t img ins d p (add_fact s (FRange x k k)) = Some f1 /\ (forall y, In y f1 -> In y fin)).
    { induction ks as [|k0 ks IHks]; intros fin Hf Hin; [destruct Hin|]. cbn [check_cases] in Hf.
      destruct (check t img ins d p (add_fact s (FRange x k0 k0))) as [f1|] eqn:H1; [|discriminate].
      destruct (check_cases (check t img ins d p) s x ks) as [f2|] eqn:H2; [|discriminate]. injection Hf as <-.
      destruct Hin as [->|Hin].
      - exists f1. split; [exact H1|]. intros y Hy. apply in_or_app. left. exact Hy.
      - destruct (IHks f2 eq_refl Hin) as (f & Hf & Hsub). exists f. split; [exact Hf|]. intros y Hy. apply in_or_app. right. exact (Hsub y Hy). }
    destruct (Hcc _ _ Hck Hk) as (f1 & Hf1 & Hsub).
    assert (Hd' : sden segs E (add_fact s (FRange x k k)) ms).
    { intros E' Ha'. destruct (Hden E' Ha') as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
      unfold sden0; cbn [s_pc s_regs s_rgs s_facts s_resv add_fact]. split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
      split; [exact H4|]. split; [exact H5|]. split; [exact H6|]. split; [|exact H8]. constructor; [|exact H7].
      cbn [fact_ok]. rewrite <- (lden_agree (s_next s) E E' x Hwx Ha'). unfold k. lia. }
    destruct (IH _ _ _ Ht Himg Hf1 E ms Hd') as (L2 & ms2 & E2 & HL2 & Hst2 & Hd2 & Hi2 & Hfp2).
    exists L2, ms2, E2. split; [exact (Hsub L2 HL2)|]. split; [exact Hst2|]. split; [exact Hd2 | split; [exact Hi2 | exact Hfp2]].
Qed.
#[using="Type"] Theorem check_sound : forall t img ins depth p s finals,
  tbl_ok segs t -> img_ok segs img -> check t img ins depth p s = Some finals ->
  forall E ms, sden segs E s ms ->
  exists L ms' E', In L finals /\ isteps segs ms ms' /\ sden segs E' L ms' /\ (forall x, In x ins -> E' x = E x).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros t img ins depth p s finals Ht Himg Hck E ms Hd.
  destruct (check_sound_fp t img ins depth p s finals Ht Himg Hck E ms Hd) as (L & ms' & E' & H1 & H2 & H3 & H4 & _).
  exists L, ms', E'. exact (conj H1 (conj H2 (conj H3 H4))).
Qed.

End WithSegs.

(* [comment removed for export] *)
Lemma tforall_acc_intro : forall {A} (f : positive -> A -> bool) t k,
  (forall p x, tget p t = Some x -> f (k p) x = true) -> tforall_acc f t k = true.
Proof.
  intros A f t. induction t as [|l IHl v r IHr]; intros k H; [reflexivity|]. cbn [tforall_acc].
  rewrite (IHl (fun p => k (xO p)) (fun p x Hp => H (xO p) x Hp)), (IHr (fun p => k (xI p)) (fun p x Hp => H (xI p) x Hp)).
  destruct v as [x|]; [rewrite (H xH x eq_refl)|]; reflexivity.
Qed.
Lemma terms_eqb_refl : forall x, terms_eqb x x = true.
Proof. induction x as [|[p k] x IH]; [reflexivity|]. cbn [terms_eqb]. rewrite Pos.eqb_refl, Z.eqb_refl. exact IH. Qed.
Lemma lin_eqb_refl : forall l, lin_eqb l l = true.
Proof. intros l. unfold lin_eqb. rewrite Z.eqb_refl. apply terms_eqb_refl. Qed.
Lemma pos_upto_In : forall k acc x, In x (pos_upto k acc) <-> (Pos.to_nat x <= k)%nat \/ In x acc.
Proof.
  induction k as [|k IH]; intros acc x; cbn [pos_upto].
  - pose proof (Pos2Nat.is_pos x) as Hpx. split; [intros H; right; exact H | intros [H|H]; [lia | exact H]].
  - rewrite IH. cbn [In]. split.
    + intros [H|[H|H]]; [left; lia | subst x; left; rewrite SuccNat2Pos.id_succ; lia | right; exact H].
    + intros [H|H]; [|right; right; exact H]. destruct (Nat.eq_dec (Pos.to_nat x) (S k)) as [He|Hne]; [|left; lia].
      right. left. apply Pos2Nat.inj. rewrite SuccNat2Pos.id_succ. symmetry. exact He.
Qed.
Lemma forallb_ext_l : forall {A} (f g : A -> bool) l, (forall x, f x = g x) -> forallb f l = forallb g l.
Proof. intros A f g l H. induction l as [|x l IH]; [reflexivity|]. cbn [forallb]. rewrite H, IH. reflexivity. Qed.
Lemma forallb_In_equiv : forall {A} (f : A -> bool) l l', (forall x, In x l <-> In x l') -> forallb f l = forallb f l'.
Proof. intros A f l l' H. apply eq_true_iff_eq. rewrite !forallb_forall. split; intros Hf x Hx; apply Hf; apply H; exact Hx. Qed.

Section CheckB.
Variable t : tree xi.
Variable img : tree Z.
Variable n0 : positive.           (* [comment removed for export] *)

(* [comment removed for export] *)
Definition ins_in_paramsR (ls : loopspec) : bool :=
  forallb (fun x => existsb (Pos.eqb x) (ls_params ls)) (pos_upto (Pos.to_nat n0 - 1) []).
(* [comment removed for export] *)
Fixpoint pfx_ok (l : list positive) (nx : positive) (k : nat) : bool :=
  match k with O => true | S k' => match l with x :: r => if Pos.eqb x nx then pfx_ok r (Pos.succ nx) k' else false | [] => false end end.
Definition ins_in_paramsB (ls : loopspec) : bool := if pfx_ok (ls_params ls) 1 (Pos.to_nat n0 - 1) then true else ins_in_paramsR ls.

Fixpoint checkB (depth : nat) (p : plan) (s : sst) : option (list sst) :=
  match depth with
  | O => None
  | S d =>
      match p with
      | PFin => Some [s]
      | PRun fuel stops ks =>
          if Pos.leb n0 (s_next s) then check_all (checkB d) ks (fx_explore t img fuel stops s []) else None
      | PLoop ls ks =>
          let σ := match_st s (ls_inv ls) in
          if (entails s (ls_inv ls) σ && fixed_below σ n0 && ins_in_paramsB ls && bases_params ls && shape_eqb (s_rgs s) (s_rgs (ls_inv ls))
              && Pos.leb (s_next s) (s_next (ls_inv ls)))%bool then
            match loop_check t img ls with
            | Some exits => check_all (checkB d) ks exits
            | None => None
            end
          else None
      | PJoin fuel stops jpc pj ks =>
          if Pos.leb n0 (s_next s) then
            let Ls := fx_explore t img fuel (jpc :: stops) s [] in
            match check_all (checkB d) ks (List.filter (fun L => negb (Z.eqb (s_pc L) jpc)) Ls) with
            | Some fo =>
                let F := List.filter (fun L => negb (Z.eqb (s_pc L) jpc)) fo in
                match List.filter (fun L => Z.eqb (s_pc L) jpc) Ls ++ List.filter (fun L => Z.eqb (s_pc L) jpc) fo with
                | [] => Some F
                | L0 :: Lrs =>
                    let '(P, k) := gen2 L0 Lrs in
                    let n := max_next Lrs (s_next L0) in
                    if (state_wf P && forallb (fun L => let σ := match_st L P in (join_ent L P σ n k && fixed_below σ n0)%bool) (L0 :: Lrs)
                        && shape_eqb (s_rgs s) (s_rgs P) && Pos.leb (s_next s) (s_next P))%bool then
                      match checkB d pj P with
                      | Some f1 => Some (f1 ++ F)
                      | None => None
                      end
                    else None
                end
            | None => None
            end
          else None
      | PLoopW fuel wstops ks =>
          match List.find (fun L => Z.eqb (s_pc L) (s_pc s)) (fx_explore t img fuel (s_pc s :: wstops) s []) with
          | Some s1 => match widen s s1 fuel wstops with
                       | Some ls => match checkB d (PLoop ls ks) s with Some f => Some f | None => checkB d (PLoop (refine_ls t img ls) ks) s end
                       | None => None
                       end
          | None => None
          end
      | PCases x lo hi p =>
          let '(a, b) := irange (s_facts s) x in
          if (Z.leb lo a && Z.leb b hi && Z.leb (hi - lo) 255 && lwf (s_next s) x)%bool then
            check_cases (checkB d p) s x (z_upto (Z.to_nat (hi - lo + 1)) lo [])
          else None
      end
  end.

Variable ins : list positive.
Hypothesis Hins : forall x, In x ins <-> (x < n0)%positive.

#[using="Hins"] Lemma ins_below_eq : forall s, ins_below ins s = Pos.leb n0 (s_next s).
Proof. LiaFast.lf_pins (fun (Hins : LiaFast.U) => LiaFast.u0).
  intros s. unfold ins_below. apply eq_true_iff_eq. rewrite forallb_forall, Pos.leb_le. split.
  - intros H. destruct (Pos.leb n0 (s_next s)) eqn:Hl; [apply Pos.leb_le; exact Hl|]. apply Pos.leb_gt in Hl.
    pose proof (H (s_next s) (proj2 (Hins _) Hl)) as Hx. apply Pos.ltb_lt in Hx. lia.
  - intros H x Hx. apply Pos.ltb_lt. apply Hins in Hx. lia.
Qed.
#[using="Hins"] Lemma params_fixed_eq : forall σ, params_fixed σ ins = fixed_below σ n0.
Proof. LiaFast.lf_pins (fun (Hins : LiaFast.U) => LiaFast.u0).
  intros σ. unfold params_fixed, fixed_below. apply eq_true_iff_eq. rewrite forallb_forall. split.
  - intros H. apply tforall_acc_intro. intros p l Hp. destruct (Pos.leb n0 p) eqn:Hl; [reflexivity|]. apply Pos.leb_gt in Hl.
    pose proof (H p (proj2 (Hins _) Hl)) as Hx. unfold svar in Hx. rewrite Hp in Hx. cbn [orb]. exact Hx.
  - intros H x Hx. apply Hins in Hx. unfold svar. destruct (tget x σ) as [l|] eqn:Hg; [|apply lin_eqb_refl].
    pose proof (tforall_spec _ _ H x l Hg) as Hl. cbn beta in Hl. apply orb_prop in Hl as [Hl|Hl]; [apply Pos.leb_le in Hl; lia | exact Hl].
Qed.
#[using="Type"] Lemma pfx_ok_In : forall k l p, pfx_ok l p k = true -> forall x, (Pos.to_nat p <= Pos.to_nat x < Pos.to_nat p + k)%nat -> In x l.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction k as [|k IH]; intros l p H x Hx; [lia|]. destruct l as [|y r]; cbn [pfx_ok] in H; [discriminate|].
  destruct (Pos.eqb y p) eqn:Hy; [|discriminate]. apply Pos.eqb_eq in Hy. subst y.
  destruct (Pos.eq_dec x p) as [->|Hne]; [left; reflexivity|]. right. apply (IH r (Pos.succ p) H x).
  rewrite Pos2Nat.inj_succ. assert (Pos.to_nat x <> Pos.to_nat p) by (intros E; apply Hne; apply Pos2Nat.inj; exact E). lia.
Qed.
#[using="Type"] Lemma ins_in_paramsB_R : forall ls, ins_in_paramsB ls = ins_in_paramsR ls.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ls. unfold ins_in_paramsB. destruct (pfx_ok (ls_params ls) 1 (Pos.to_nat n0 - 1)) eqn:H; [|reflexivity].
  symmetry. unfold ins_in_paramsR. apply forallb_forall. intros x Hx. apply pos_upto_In in Hx. destruct Hx as [Hx|[]].
  apply existsb_exists. exists x. split; [|apply Pos.eqb_refl].
  apply (pfx_ok_In _ _ _ H). pose proof (Pos2Nat.is_pos x). cbn. lia.
Qed.
#[using="Hins"] Lemma ins_in_params_eq : forall ls, ins_in_params ins ls = ins_in_paramsB ls.
Proof. LiaFast.lf_pins (fun (Hins : LiaFast.U) => LiaFast.u0).
  intros ls. rewrite ins_in_paramsB_R. unfold ins_in_params, ins_in_paramsR. apply forallb_In_equiv. intros x. rewrite Hins, pos_upto_In. cbn [In].
  pose proof (Pos2Nat.is_pos x) as Hpx. pose proof (Pos2Nat.is_pos n0) as Hpn. split; [intros Hx; left; apply Pos2Nat.inj_lt in Hx; lia | intros [Hx|[]]; apply Pos2Nat.inj_lt; lia].
Qed.

#[using="Type"] Lemma check_all_ext : forall (c1 c2 : plan -> sst -> option (list sst)) ks ls, (forall p s, c1 p s = c2 p s) -> check_all c1 ks ls = check_all c2 ks ls.
Proof. LiaFast.lf_pins LiaFast.u0. intros c1 c2 ks ls H. induction ls as [|L ls IH]; [reflexivity|]. cbn [check_all]. rewrite H, IH. reflexivity. Qed.
#[using="Type"] Lemma check_cases_ext : forall (c1 c2 : sst -> option (list sst)) s x ks, (forall s', c1 s' = c2 s') -> check_cases c1 s x ks = check_cases c2 s x ks.
Proof. LiaFast.lf_pins LiaFast.u0. intros c1 c2 s x ks H. induction ks as [|k ks IH]; [reflexivity|]. cbn [check_cases]. rewrite H, IH. reflexivity. Qed.

#[using="Hins"] Theorem checkB_eq : forall depth p s, checkB depth p s = check t img ins depth p s.
Proof. LiaFast.lf_pins (fun (Hins : LiaFast.U) => LiaFast.u0).
  induction depth as [|d IH]; intros p s; [reflexivity|]. destruct p as [|fuel stops ks|ls ks|fuel stops jpc pj ks|fuel wstops ks|x lo hi p]; cbn [checkB check].
  - reflexivity.
  - rewrite ins_below_eq. rewrite (check_all_ext _ _ ks _ IH). reflexivity.
  - rewrite params_fixed_eq, ins_in_params_eq. match goal with |- (if ?c then _ else _) = _ => destruct c end; [|reflexivity].
    destruct (loop_check t img ls) as [exits|]; [|reflexivity]. apply check_all_ext. exact IH.
  - rewrite ins_below_eq. destruct (Pos.leb n0 (s_next s)); [|reflexivity].
    rewrite (check_all_ext (checkB d) (check t img ins d)) by exact IH.
    destruct (check_all (check t img ins d) ks (List.filter (fun L => negb (Z.eqb (s_pc L) jpc)) (fx_explore t img fuel (jpc :: stops) s []))) as [fo|]; [|reflexivity].
    destruct (List.filter (fun L => Z.eqb (s_pc L) jpc) (fx_explore t img fuel (jpc :: stops) s []) ++ List.filter (fun L => Z.eqb (s_pc L) jpc) fo) as [|L0 Lrs]; [reflexivity|].
    destruct (gen2 L0 Lrs) as [P k].
    assert (Hf : forallb (fun L => (join_ent L P (match_st L P) (max_next Lrs (s_next L0)) k && fixed_below (match_st L P) n0)%bool) (L0 :: Lrs) =
                 forallb (fun L => (join_ent L P (match_st L P) (max_next Lrs (s_next L0)) k && params_fixed (match_st L P) ins)%bool) (L0 :: Lrs)).
    { apply forallb_ext_l. intros L. rewrite params_fixed_eq. reflexivity. }
    rewrite Hf, IH. reflexivity.
  - destruct (List.find (fun L => Z.eqb (s_pc L) (s_pc s)) (fx_explore t img fuel (s_pc s :: wstops) s [])) as [s1|]; [|reflexivity].
    destruct (widen s s1 fuel wstops) as [ls|]; [|reflexivity]. rewrite !IH. reflexivity.
  - destruct (irange (s_facts s) x) as [a b]. rewrite (check_cases_ext (checkB d p) (check t img ins d p)) by (intros s'; apply IH). reflexivity.
Qed.
End CheckB.
