(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Znumtheory List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxStep FxCall.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxQChk.

Module FxQcsChk.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxQChk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Abbreviation two64 := (2 ^ 64).
Lemma us64 : forall z, 0 <= z < two64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64. apply Z.mod_small. exact Hz. Qed.

Lemma bv_ltu_irrefl_z : forall x : word, bv_ltu x x = false.
Proof. intros x. unfold bv_ltu. apply Z.ltb_irrefl. Qed.
Lemma getr_x0 : forall regs : bvmap 5 word, getr regs (Z_to_bv 5 0) = Z_to_bv 64 0.
Proof. intros regs. reflexivity. Qed.

(* [comment removed for export] *)
Section QC2G.
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

(* [comment removed for export] *)
Definition qfail2 : word := if beq then qpc pc0 12 else btgt (qpc pc0 11) (bv_signed bim).

#[using="ord Hnz Hd1 Hd2 I0 I1 I2 I3 I4 I5 I6 I7 I8 I9 I10"] Theorem qc2g_isteps : forall regs mem rom (b : word) (n : Z) (P sh v1 v2 : word) bsP bs1 bs2,
  getr regs rB = b -> getr regs rP = P -> getr regs rA = v_add b (Z_to_bv 64 n) ->
  rdn segs mem P 8 = Some bsP -> bytes_le_to_Z bsP = bv_unsigned sh ->
  rdn segs mem (qw1 sh b) 8 = Some bs1 -> bytes_le_to_Z bs1 = bv_unsigned v1 ->
  rdn segs mem (qw2 sh b n) 8 = Some bs2 -> bytes_le_to_Z bs2 = bv_unsigned v2 ->
  exists regs',
    FxStep.isteps segs (mkst regs (qpc pc0 0) mem rom) (mkst regs' (qpc pc0 11) mem rom) /\
    getr regs' rP = qX sh b /\ getr regs' rY = qY sh b n /\ getr regs' rA = qlast b n /\
    getr regs' rZ = v_or v2 v1 /\ getr regs' rW = v2 /\
    (forall r, r <> rP -> r <> rA -> r <> rY -> r <> rZ -> r <> rW -> getr regs' r = getr regs r).
Proof. LiaFast.lf_pins (fun (ord Hnz Hd1 Hd2 I0 I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 : LiaFast.U) => LiaFast.u0).
  intros regs mem rom b n P sh v1 v2 bsP bs1 bs2 HB HPr HA HP HPv HW1 HV1 HW2 HV2.
  destruct Hnz as (NP & NA & NY & NZ & NW).
  destruct Hd1 as (DAP & DYP & DYA & DZP & DZA & DZY & DWP & DWA & DWY & DWZ).
  destruct Hd2 as (DBP & DBA & DBY).
  destruct I0 as (w0 & F0 & E0 & D0). destruct I1 as (w1 & F1 & E1 & D1). destruct I2 as (w2 & F2 & E2 & D2).
  destruct I3 as (w3 & F3 & E3 & D3). destruct I4 as (w4 & F4 & E4 & D4). destruct I5 as (w5 & F5 & E5 & D5).
  destruct I6 as (w6 & F6 & E6 & D6). destruct I7 as (w7 & F7 & E7 & D7). destruct I8 as (w8 & F8 & E8 & D8).
  destruct I9 as (w9 & F9 & E9 & D9). destruct I10 as (w10 & F10 & E10 & D10).
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
  set (r9 := regupd r8 rZ v1).
  assert (S8 : RiscvSemantics.step segs (mkst r8 (qpc pc0 8) mem rom) = MachineOk (mkst r9 (qpc pc0 9) mem rom)).
  { rewrite (step_ld segs r8 (qpc pc0 8) mem rom w8 rZ rZ (Z_to_bv 12 0) bs1 v1 F8 E8 D8).
    - nz_if. rewrite qpc_succ. reflexivity.
    - unfold r8, r7. gsimp. change (bv_signed (Z_to_bv 12 0)) with 0. rewrite v_addi0. exact HW1.
    - exact HV1. }
  set (r10 := regupd r9 rW v2).
  assert (S9 : RiscvSemantics.step segs (mkst r9 (qpc pc0 9) mem rom) = MachineOk (mkst r10 (qpc pc0 10) mem rom)).
  { rewrite (step_ld segs r9 (qpc pc0 9) mem rom w9 rW rW (Z_to_bv 12 0) bs2 v2 F9 E9 D9).
    - nz_if. rewrite qpc_succ. reflexivity.
    - unfold r9, r8. gsimp. change (bv_signed (Z_to_bv 12 0)) with 0. rewrite v_addi0. exact HW2.
    - exact HV2. }
  (* [comment removed for export] *)
  set (r11 := regupd r10 rZ (v_or v2 v1)).
  assert (S10 : RiscvSemantics.step segs (mkst r10 (qpc pc0 10) mem rom) = MachineOk (mkst r11 (qpc pc0 11) mem rom)).
  { rewrite (step_or segs r10 (qpc pc0 10) mem rom w10 rZ rW rZ F10 E10 D10). nz_if. rewrite qpc_succ.
    unfold r11, r10, r9. gsimp. reflexivity. }
  exists r11. split.
  - eapply FxStep.ist_step; [reflexivity | exact S0|]. eapply FxStep.isteps_trans; [exact Hs12|].
    repeat (eapply FxStep.ist_step; [reflexivity | eassumption |]). apply FxStep.ist_refl.
  - unfold r11, r10, r9, r8, r7, r6, r5, r4.
    split; [gsimp; reflexivity|]. split; [gsimp; reflexivity|]. split; [gsimp; exact G3A|].
    split; [gsimp; reflexivity|]. split; [gsimp; reflexivity|].
    intros r H1 H2 H3 H4 H5. gsimp. rewrite (G3o r H1 H2). unfold r1. gsimp. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="I11"] Lemma qc2g_branch : forall regs mem rom (v : word), getr regs rZ = v ->
  FxStep.isteps segs (mkst regs (qpc pc0 11) mem rom)
    (mkst regs (if Z.eqb (bv_unsigned v) 0 then qok2 pc0 bim beq else qfail2) mem rom).
Proof. LiaFast.lf_pins (fun (I11 : LiaFast.U) => LiaFast.u0).
  intros regs mem rom v Hv. destruct I11 as (w11 & F11 & E11 & D11).
  assert (Hz0 : getr regs (Z_to_bv 5 0) = Z_to_bv 64 0) by reflexivity.
  eapply FxStep.ist_step; [reflexivity | | apply FxStep.ist_refl].
  destruct (Z.eqb (bv_unsigned v) 0) eqn:Hvz.
  - apply Z.eqb_eq in Hvz. assert (Hv0 : v = Z_to_bv 64 0) by (apply bv_eq; rewrite Hvz; reflexivity).
    unfold qok2. destruct beq.
    + rewrite (step_beq_tk segs regs (qpc pc0 11) mem rom w11 rZ (Z_to_bv 5 0) bim F11 E11 D11); [reflexivity|].
      rewrite Hv, Hz0, Hv0. reflexivity.
    + rewrite (step_bne_ft segs regs (qpc pc0 11) mem rom w11 rZ (Z_to_bv 5 0) bim F11 E11 D11); [rewrite qpc_succ; reflexivity|].
      rewrite Hv, Hz0, Hv0. reflexivity.
  - apply Z.eqb_neq in Hvz.
    assert (Hne : c_eq v (Z_to_bv 64 0) = false).
    { unfold c_eq. apply bv_eqb_neq. intros Hc. apply Hvz. rewrite Hc. reflexivity. }
    unfold qfail2. destruct beq.
    + rewrite (step_beq_ft segs regs (qpc pc0 11) mem rom w11 rZ (Z_to_bv 5 0) bim F11 E11 D11); [rewrite qpc_succ; reflexivity|].
      rewrite Hv, Hz0. exact Hne.
    + rewrite (step_bne_tk segs regs (qpc pc0 11) mem rom w11 rZ (Z_to_bv 5 0) bim F11 E11 D11); [reflexivity|].
      rewrite Hv, Hz0. exact Hne.
Qed.
End QC2G.

(* [comment removed for export] *)
Section SLOW.
Context {fx : FPState}.
Variable segs : list Segment.
Variables (pcs : Z) (rP rY rA rV rT rU rF rL : reg) (bok : bv 13).
Hypothesis Hnz : rP <> 0%bv /\ rV <> 0%bv /\ rT <> 0%bv /\ rU <> 0%bv /\ rF <> 0%bv /\ rL <> 0%bv.
Hypothesis HdV : rV <> rY /\ rV <> rA /\ rV <> rP.
Hypothesis HdT : rT <> rY /\ rT <> rP /\ rT <> rV.
Hypothesis HdU : rU <> rY /\ rU <> rP /\ rU <> rV /\ rU <> rT.
Hypothesis HdF : rF <> rY /\ rF <> rP /\ rF <> rU.
Hypothesis HdL : rL <> rY /\ rL <> rP /\ rL <> rF.
Hypothesis HdPY : rP <> rY.
Hypothesis J0 : qins segs pcs 0 (Load SZ1 true rV rY (Z_to_bv 12 0)).
Hypothesis J1 : qins segs pcs 1 (OpImm ALU_AND rT rA (Z_to_bv 12 7)).
Hypothesis J2 : qins segs pcs 2 (Op ALU_SLTU rU (Z_to_bv 5 0) rV).
Hypothesis J3 : qins segs pcs 3 (Op ALU_SLT rF rT rV).
Hypothesis J4 : qins segs pcs 4 (OpImm ALU_XOR rF rF (Z_to_bv 12 1)).
Hypothesis J5 : qins segs pcs 5 (Op ALU_AND rF rU rF).
Hypothesis J6 : qins segs pcs 6 (Branch BC_GEU rP rY (Z_to_bv 13 20)).
Hypothesis J7 : qins segs pcs 7 (Load SZ1 false rL rP (Z_to_bv 12 0)).
Hypothesis J8 : qins segs pcs 8 (OpImm ALU_ADD rP rP (Z_to_bv 12 1)).
Hypothesis J9 : qins segs pcs 9 (Op ALU_OR rF rL rF).
Hypothesis J10 : qins segs pcs 10 (Branch BC_NE rP rY (Z_to_bv 13 8180)).
Hypothesis J11 : qins segs pcs 11 (OpImm ALU_AND rP rF (Z_to_bv 12 255)).
Hypothesis J12 : qins segs pcs 12 (Branch BC_EQ rP (Z_to_bv 5 0) bok).

Definition sok : word := btgt (qpc pcs 12) (bv_signed bok).

#[using="Type"] Lemma btgt_qpc : forall k d, btgt (qpc pcs k) (4 * d) = qpc pcs (k + d).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros k d. unfold btgt, v_addi, qpc. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

(* [comment removed for export] *)
#[using="rV rT rU Hnz HdF HdL HdPY J7 J8 J9 J10"] Lemma qslow_loop : forall k regs mem rom (X Y : Z),
  Z.of_nat k = Y - X -> 0 <= X -> X < Y -> Y < two64 ->
  getr regs rP = Z_to_bv 64 X -> getr regs rY = Z_to_bv 64 Y -> getr regs rF = Z_to_bv 64 0 ->
  (forall x, X <= x < Y -> rdn segs mem (Z_to_bv 64 x) 1 = Some [Z_to_bv 8 0]) ->
  exists regs', FxStep.isteps segs (mkst regs (qpc pcs 7) mem rom) (mkst regs' (qpc pcs 11) mem rom) /\
    getr regs' rF = Z_to_bv 64 0 /\ (forall r, r <> rP -> r <> rL -> r <> rF -> getr regs' r = getr regs r).
Proof. LiaFast.lf_pins (fun (rV rT rU Hnz HdF HdL HdPY J7 J8 J9 J10 : LiaFast.U) => LiaFast.u0).
  destruct Hnz as (NP & NV & NT & NU & NF & NL). destruct HdL as (DLY & DLP & DLF). destruct HdF as (DFY & DFP & DFU).
  destruct J7 as (w7 & F7 & E7 & D7). destruct J8 as (w8 & F8 & E8 & D8). destruct J9 as (w9 & F9 & E9 & D9).
  destruct J10 as (w10 & F10 & E10 & D10).
  induction k as [|k IH]; intros regs mem rom X Y Hk HX0 HXY HY GP GY GF Hz; [lia|].
  set (r1 := regupd regs rL (Z_to_bv 64 (bv_unsigned (Z_to_bv 8 0)))).
  assert (S7 : RiscvSemantics.step segs (mkst regs (qpc pcs 7) mem rom) = MachineOk (mkst r1 (qpc pcs 8) mem rom)).
  { rewrite (step_lbu segs regs (qpc pcs 7) mem rom w7 rL rP (Z_to_bv 12 0) (Z_to_bv 8 0) F7 E7 D7).
    - nz_if. rewrite qpc_succ. reflexivity.
    - rewrite GP. change (bv_signed (Z_to_bv 12 0)) with 0. rewrite v_addi0. apply Hz. lia. }
  set (r2 := regupd r1 rP (Z_to_bv 64 (X + 1))).
  assert (S8 : RiscvSemantics.step segs (mkst r1 (qpc pcs 8) mem rom) = MachineOk (mkst r2 (qpc pcs 9) mem rom)).
  { rewrite (step_addi segs r1 (qpc pcs 8) mem rom w8 rP rP (Z_to_bv 12 1) F8 E8 D8). nz_if. rewrite qpc_succ.
    unfold r2, r1. gsimp. rewrite GP. unfold v_addi. rewrite us64 by lia. reflexivity. }
  set (r3 := regupd r2 rF (Z_to_bv 64 0)).
  assert (S9 : RiscvSemantics.step segs (mkst r2 (qpc pcs 9) mem rom) = MachineOk (mkst r3 (qpc pcs 10) mem rom)).
  { rewrite (step_or segs r2 (qpc pcs 9) mem rom w9 rF rL rF F9 E9 D9). nz_if. rewrite qpc_succ.
    unfold r3, r2, r1. gsimp. rewrite GF. reflexivity. }
  assert (G3P : getr r3 rP = Z_to_bv 64 (X + 1)) by (unfold r3, r2; gsimp; reflexivity).
  assert (G3Y : getr r3 rY = Z_to_bv 64 Y) by (unfold r3, r2, r1; gsimp; exact GY).
  assert (G3F : getr r3 rF = Z_to_bv 64 0) by (unfold r3; gsimp; reflexivity).
  assert (G3o : forall r, r <> rP -> r <> rL -> r <> rF -> getr r3 r = getr regs r) by (intros r H1 H2 H3; unfold r3, r2, r1; gsimp; reflexivity).
  destruct (Z.eq_dec (X + 1) Y) as [He|Hne].
  - (* [comment removed for export] *)
    assert (S10 : RiscvSemantics.step segs (mkst r3 (qpc pcs 10) mem rom) = MachineOk (mkst r3 (qpc pcs 11) mem rom)).
    { rewrite (step_bne_ft segs r3 (qpc pcs 10) mem rom w10 rP rY (Z_to_bv 13 8180) F10 E10 D10); [rewrite qpc_succ; reflexivity|].
      rewrite G3P, G3Y, He. unfold c_eq. apply bv_eqb_refl. }
    exists r3. split; [|split; [exact G3F | exact G3o]].
    repeat (eapply FxStep.ist_step; [reflexivity | eassumption |]). apply FxStep.ist_refl.
  - assert (S10 : RiscvSemantics.step segs (mkst r3 (qpc pcs 10) mem rom) = MachineOk (mkst r3 (qpc pcs 7) mem rom)).
    { rewrite (step_bne_tk segs r3 (qpc pcs 10) mem rom w10 rP rY (Z_to_bv 13 8180) F10 E10 D10).
      - change (bv_signed (Z_to_bv 13 8180)) with (4 * (-3)). rewrite btgt_qpc. reflexivity.
      - rewrite G3P, G3Y. unfold c_eq. apply bv_eqb_neq. intros Hc. apply (f_equal bv_unsigned) in Hc.
        rewrite !us64 in Hc by lia. lia. }
    destruct (IH r3 mem rom (X + 1) Y ltac:(lia) ltac:(lia) ltac:(lia) HY G3P G3Y G3F ltac:(intros x Hx; apply Hz; lia))
      as (regs' & Hst & GF' & Go').
    exists regs'. split; [|split; [exact GF'|]].
    + repeat (eapply FxStep.ist_step; [reflexivity | eassumption |]). exact Hst.
    + intros r H1 H2 H3. rewrite (Go' r H1 H2 H3). exact (G3o r H1 H2 H3).
Qed.

#[using="Type"] Lemma vlb_pos : forall b1 : byte, bv_unsigned b1 <= 7 -> v_lb b1 = Z_to_bv 64 (bv_unsigned b1).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros b1 Hb. unfold v_lb. f_equal. unfold bv_signed. apply bv_swrap_small. change (bv_half_modulus 8) with 128.
  pose proof (bv_unsigned_in_range _ b1). lia.
Qed.

#[using="Hnz HdV HdT HdU HdF HdL HdPY J0 J1 J2 J3 J4 J5 J6 J7 J8 J9 J10 J11 J12"] Theorem qslow_isteps : forall regs mem rom (X Y : Z) (A : word) (b1 : byte),
  getr regs rP = Z_to_bv 64 X -> getr regs rY = Z_to_bv 64 Y -> getr regs rA = A ->
  0 <= X <= Y -> Y < two64 ->
  (forall x, X <= x < Y -> rdn segs mem (Z_to_bv 64 x) 1 = Some [Z_to_bv 8 0]) ->
  rdn segs mem (Z_to_bv 64 Y) 1 = Some [b1] ->
  (bv_unsigned b1 = 0 \/ bv_unsigned A mod 8 < bv_unsigned b1 <= 7) ->
  exists regs', FxStep.isteps segs (mkst regs (qpc pcs 0) mem rom) (mkst regs' sok mem rom) /\
    (forall r, r <> rP -> r <> rV -> r <> rT -> r <> rU -> r <> rF -> r <> rL -> getr regs' r = getr regs r).
Proof. LiaFast.lf_pins (fun (Hnz HdV HdT HdU HdF HdL HdPY J0 J1 J2 J3 J4 J5 J6 J7 J8 J9 J10 J11 J12 : LiaFast.U) => LiaFast.u0).
  intros regs mem rom X Y A b1 GP GY GA HXY HY Hz Hl1 Hb1.
  destruct Hnz as (NP & NV & NT & NU & NF & NL).
  destruct HdV as (DVY & DVA & DVP). destruct HdT as (DTY & DTP & DTV). destruct HdU as (DUY & DUP & DUV & DUT).
  destruct HdF as (DFY & DFP & DFU). destruct HdL as (DLY & DLP & DLF).
  destruct J0 as (w0 & F0 & E0 & D0). destruct J1 as (w1 & F1 & E1 & D1). destruct J2 as (w2 & F2 & E2 & D2).
  destruct J3 as (w3 & F3 & E3 & D3). destruct J4 as (w4 & F4 & E4 & D4). destruct J5 as (w5 & F5 & E5 & D5).
  destruct J6 as (w6 & F6 & E6 & D6). destruct J11 as (w11 & F11 & E11 & D11). destruct J12 as (w12 & F12 & E12 & D12).
  assert (Hb7 : bv_unsigned b1 <= 7) by (destruct Hb1; lia).
  pose proof (bv_unsigned_in_range _ b1) as Rb1.
  (* [comment removed for export] *)
  set (sv := Z_to_bv 64 (bv_unsigned b1)).
  set (r1 := regupd regs rV sv).
  assert (S0 : RiscvSemantics.step segs (mkst regs (qpc pcs 0) mem rom) = MachineOk (mkst r1 (qpc pcs 1) mem rom)).
  { rewrite (step_lb segs regs (qpc pcs 0) mem rom w0 rV rY (Z_to_bv 12 0) b1 F0 E0 D0).
    - nz_if. rewrite qpc_succ. rewrite (vlb_pos b1 Hb7). reflexivity.
    - rewrite GY. change (bv_signed (Z_to_bv 12 0)) with 0. rewrite v_addi0. exact Hl1. }
  (* [comment removed for export] *)
  set (t := v_andi A 7).
  set (r2 := regupd r1 rT t).
  assert (S1 : RiscvSemantics.step segs (mkst r1 (qpc pcs 1) mem rom) = MachineOk (mkst r2 (qpc pcs 2) mem rom)).
  { rewrite (step_andi segs r1 (qpc pcs 1) mem rom w1 rT rA (Z_to_bv 12 7) F1 E1 D1). nz_if. rewrite qpc_succ.
    unfold r2, r1. gsimp. rewrite GA. reflexivity. }
  assert (Ht : bv_unsigned t = bv_unsigned A mod 8).
  { unfold t, v_andi. change (bv_wrap 64 7) with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
    apply us64. pose proof (Z.mod_pos_bound (bv_unsigned A) 8 ltac:(lia)). lia. }
  (* [comment removed for export] *)
  set (u := v_sltu (Z_to_bv 64 0) sv).
  set (r3 := regupd r2 rU u).
  assert (S2 : RiscvSemantics.step segs (mkst r2 (qpc pcs 2) mem rom) = MachineOk (mkst r3 (qpc pcs 3) mem rom)).
  { rewrite (step_sltu segs r2 (qpc pcs 2) mem rom w2 rU (Z_to_bv 5 0) rV F2 E2 D2). nz_if. rewrite qpc_succ.
    rewrite getr_x0. unfold r3, r2, r1. gsimp. reflexivity. }
  (* [comment removed for export] *)
  set (f1 := v_slt t sv).
  set (r4 := regupd r3 rF f1).
  assert (S3 : RiscvSemantics.step segs (mkst r3 (qpc pcs 3) mem rom) = MachineOk (mkst r4 (qpc pcs 4) mem rom)).
  { rewrite (step_slt segs r3 (qpc pcs 3) mem rom w3 rF rT rV F3 E3 D3). nz_if. rewrite qpc_succ.
    unfold r4, r3, r2, r1. gsimp. reflexivity. }
  (* [comment removed for export] *)
  set (f2 := v_xori f1 1).
  set (r5 := regupd r4 rF f2).
  assert (S4 : RiscvSemantics.step segs (mkst r4 (qpc pcs 4) mem rom) = MachineOk (mkst r5 (qpc pcs 5) mem rom)).
  { rewrite (step_xori segs r4 (qpc pcs 4) mem rom w4 rF rF (Z_to_bv 12 1) F4 E4 D4). nz_if. rewrite qpc_succ.
    unfold r5, r4. gsimp. reflexivity. }
  (* [comment removed for export] *)
  set (r6 := regupd r5 rF (Z_to_bv 64 0)).
  assert (Hflag : v_and u f2 = Z_to_bv 64 0).
  { destruct Hb1 as [H0|H1].
    - assert (Hsv : sv = Z_to_bv 64 0) by (unfold sv; rewrite H0; reflexivity).
      unfold u. rewrite Hsv. unfold v_sltu, c_ltu. rewrite bv_ltu_irrefl_z. unfold v_and. change (bv_unsigned (Z_to_bv 64 0)) with 0.
      rewrite Z.land_0_l. reflexivity.
    - assert (Hlt : c_lts t sv = true).
      { unfold c_lts, bv_lts. unfold bv_signed. rewrite !bv_swrap_small.
        - apply Z.ltb_lt. rewrite Ht. unfold sv. rewrite us64 by (unfold two64; lia). lia.
        - change (bv_half_modulus 64) with (2 ^ 63). unfold sv. rewrite us64 by (unfold two64; lia). lia.
        - change (bv_half_modulus 64) with (2 ^ 63). rewrite Ht. pose proof (Z.mod_pos_bound (bv_unsigned A) 8 ltac:(lia)). lia. }
      unfold f2, f1, v_slt. rewrite Hlt. unfold v_xori, v_and. change (bv_unsigned (Z_to_bv 64 1)) with 1.
      change (bv_wrap 64 1) with 1. change (Z.lxor 1 1) with 0. change (bv_unsigned (Z_to_bv 64 0)) with 0.
      rewrite Z.land_0_r. reflexivity. }
  assert (S5 : RiscvSemantics.step segs (mkst r5 (qpc pcs 5) mem rom) = MachineOk (mkst r6 (qpc pcs 6) mem rom)).
  { rewrite (step_and segs r5 (qpc pcs 5) mem rom w5 rF rU rF F5 E5 D5). nz_if. rewrite qpc_succ.
    unfold r6, r5, r4, r3. gsimp. rewrite Hflag. reflexivity. }
  assert (G6P : getr r6 rP = Z_to_bv 64 X) by (unfold r6, r5, r4, r3, r2, r1; gsimp; exact GP).
  assert (G6Y : getr r6 rY = Z_to_bv 64 Y) by (unfold r6, r5, r4, r3, r2, r1; gsimp; exact GY).
  assert (G6F : getr r6 rF = Z_to_bv 64 0) by (unfold r6; gsimp; reflexivity).
  assert (G6o : forall r, r <> rV -> r <> rT -> r <> rU -> r <> rF -> getr r6 r = getr regs r)
    by (intros r H1 H2 H3 H4; unfold r6, r5, r4, r3, r2, r1; gsimp; reflexivity).
  (* [comment removed for export] *)
  assert (HL : exists r7, FxStep.isteps segs (mkst r6 (qpc pcs 6) mem rom) (mkst r7 (qpc pcs 11) mem rom) /\
             getr r7 rF = Z_to_bv 64 0 /\ (forall r, r <> rP -> r <> rL -> r <> rF -> getr r7 r = getr r6 r)).
  { destruct (Z.eq_dec X Y) as [He|Hne].
    - exists r6. split; [|split; [exact G6F | intros; reflexivity]].
      eapply FxStep.ist_step; [reflexivity | | apply FxStep.ist_refl].
      rewrite (step_bgeu_tk segs r6 (qpc pcs 6) mem rom w6 rP rY (Z_to_bv 13 20) F6 E6 D6).
      + change (bv_signed (Z_to_bv 13 20)) with (4 * 5). rewrite btgt_qpc. reflexivity.
      + rewrite G6P, G6Y, He. unfold c_ltu. apply bv_ltu_irrefl_z.
    - assert (S6 : RiscvSemantics.step segs (mkst r6 (qpc pcs 6) mem rom) = MachineOk (mkst r6 (qpc pcs 7) mem rom)).
      { rewrite (step_bgeu_ft segs r6 (qpc pcs 6) mem rom w6 rP rY (Z_to_bv 13 20) F6 E6 D6); [rewrite qpc_succ; reflexivity|].
        rewrite G6P, G6Y. unfold c_ltu, bv_ltu. apply Z.ltb_lt. rewrite !us64 by lia. lia. }
      destruct (qslow_loop (Z.to_nat (Y - X)) r6 mem rom X Y ltac:(lia) ltac:(lia) ltac:(lia) HY G6P G6Y G6F Hz) as (r7 & Hst & GF7 & Go7).
      exists r7. split; [|split; [exact GF7 | exact Go7]].
      eapply FxStep.ist_step; [reflexivity | exact S6 | exact Hst]. }
  destruct HL as (r7 & HstL & G7F & G7o).
  (* [comment removed for export] *)
  set (r8 := regupd r7 rP (Z_to_bv 64 0)).
  assert (S11 : RiscvSemantics.step segs (mkst r7 (qpc pcs 11) mem rom) = MachineOk (mkst r8 (qpc pcs 12) mem rom)).
  { rewrite (step_andi segs r7 (qpc pcs 11) mem rom w11 rP rF (Z_to_bv 12 255) F11 E11 D11). nz_if. rewrite qpc_succ.
    unfold r8. rewrite G7F. reflexivity. }
  assert (S12 : RiscvSemantics.step segs (mkst r8 (qpc pcs 12) mem rom) = MachineOk (mkst r8 sok mem rom)).
  { rewrite (step_beq_tk segs r8 (qpc pcs 12) mem rom w12 rP (Z_to_bv 5 0) bok F12 E12 D12); [reflexivity|].
    unfold r8. gsimp. reflexivity. }
  exists r8. split.
  - repeat (eapply FxStep.ist_step; [reflexivity | eassumption |]).
    eapply FxStep.isteps_trans; [exact HstL|].
    repeat (eapply FxStep.ist_step; [reflexivity | eassumption |]). apply FxStep.ist_refl.
  - intros r H1 H2 H3 H4 H5 H6. unfold r8. gsimp. rewrite (G7o r H1 H6 H5). exact (G6o r H2 H3 H4 H5).
Qed.
End SLOW.
(* [comment removed for export] *)
End FxQcsChk.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition MC_C : Z := 0x0101010101010100.
Definition MC_H : Z := 0x8080808080808080.
Definition xr (k : Z) : reg := Z_to_bv 5 k.

Section MC.
Context {fx : FPState}.
Variable segs : list Segment.
Variable pcw : Z.      (* [comment removed for export] *)
Hypothesis J0 : qins segs pcw 0 (Load SZ8 true (xr 17) (xr 10) (Z_to_bv 12 0)).
Hypothesis J1 : qins segs pcw 1 (Op ALU_XOR (xr 17) (xr 17) (xr 15)).
Hypothesis J2 : qins segs pcw 2 (Op ALU_SUB (xr 5) (xr 13) (xr 17)).
Hypothesis J3 : qins segs pcw 3 (Op ALU_OR (xr 17) (xr 5) (xr 17)).
Hypothesis J4 : qins segs pcw 4 (Op ALU_AND (xr 17) (xr 17) (xr 14)).
Hypothesis J5 : qins segs pcw 5 (Branch BC_NE (xr 17) (xr 14) (Z_to_bv 13 52)).
Hypothesis J18 : qins segs pcw 18 (OpImm ALU_ADD (xr 13) (xr 12) (Z_to_bv 12 0)).
Hypothesis J19 : qins segs pcw 19 (Load SZ1 false (xr 12) (xr 10) (Z_to_bv 12 0)).
Hypothesis J20 : qins segs pcw 20 (Branch BC_NE (xr 12) (xr 11) (Z_to_bv 13 8164)).
Hypothesis J13 : qins segs pcw 13 (OpImm ALU_ADD (xr 13) (xr 13) (Z_to_bv 12 4095)).
Hypothesis J14 : qins segs pcw 14 (OpImm ALU_ADD (xr 10) (xr 10) (Z_to_bv 12 1)).
Hypothesis J15 : qins segs pcw 15 (Branch BC_NE (xr 13) (xr 0) (Z_to_bv 13 8176)).
Hypothesis J11 : qins segs pcw 11 (Load SZ1 false (xr 12) (xr 10) (Z_to_bv 12 0)).
Hypothesis J12 : qins segs pcw 12 (Branch BC_EQ (xr 12) (xr 11) (Z_to_bv 13 20)).
Hypothesis J17 : qins segs pcw 17 (Jalr (xr 0) (xr 1) (Z_to_bv 12 0)).

#[using="Type"] Lemma lor_shift8 : forall x y, 0 <= x < 256 -> 0 <= y -> Z.lor x (Z.shiftl y 8) = x + y * 256.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros x y Hx Hy. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
  rewrite <- Z.lxor_lor.
  - rewrite Z.add_nocarry_lxor; [reflexivity|]. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 8) as [Hl|Hl].
    + rewrite Z.mul_pow2_bits_low with (n := 8) by lia. apply andb_false_r.
    + rewrite (Z_testbit_high 8 x i) by lia. reflexivity.
  - apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 8) as [Hl|Hl].
    + replace (y * 256) with (y * 2 ^ 8) by reflexivity. rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
    + rewrite (Z_testbit_high 8 x i) by lia. reflexivity.
Qed.

#[using="Type"] Lemma bytes_le_low16 : forall b0 b1 rest, bytes_le_to_Z (b0 :: b1 :: rest) mod 2 ^ 16 = bv_unsigned b0 + 256 * bv_unsigned b1.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros b0 b1 rest. cbn [bytes_le_to_Z].
  pose proof (bv_unsigned_in_range _ b0) as R0. pose proof (bv_unsigned_in_range _ b1) as R1.
  change (bv_modulus 8) with 256 in R0, R1. pose proof (bytes_le_to_Z_nonneg rest) as Rr.
  rewrite (lor_shift8 (bv_unsigned b1)) by lia.
  rewrite lor_shift8 by (try lia; apply Z.add_nonneg_nonneg; lia).
  replace (bv_unsigned b0 + (bv_unsigned b1 + bytes_le_to_Z rest * 256) * 256) with
          ((bv_unsigned b0 + 256 * bv_unsigned b1) + bytes_le_to_Z rest * 2 ^ 16) by (change (2 ^ 16) with 65536; lia).
  rewrite Z.mod_add by lia. apply Z.mod_small. change (2 ^ 16) with 65536. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma mc_haszero : forall b0 b1 rest, bv_unsigned b0 <> 0 -> bv_unsigned b1 = 0 ->
  c_eq (v_and (v_or (v_sub (Z_to_bv 64 MC_C) (v_xor (le_bytes_to_word (b0 :: b1 :: rest)) (Z_to_bv 64 0)))
                     (v_xor (le_bytes_to_word (b0 :: b1 :: rest)) (Z_to_bv 64 0))) (Z_to_bv 64 MC_H)) (Z_to_bv 64 MC_H) = false.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros b0 b1 rest Hb0 Hb1. set (v := le_bytes_to_word (b0 :: b1 :: rest)).
  assert (Hv16 : bv_unsigned v mod 2 ^ 16 = bv_unsigned b0).
  { unfold v, le_bytes_to_word. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
    rewrite (Z.mod_mod_divide (bytes_le_to_Z (b0 :: b1 :: rest)) (2 ^ 64) (2 ^ 16)) by (first [lia | exists (2 ^ 48); reflexivity]).
    rewrite bytes_le_low16, Hb1. lia. }
  pose proof (bv_unsigned_in_range _ b0) as R0. change (bv_modulus 8) with 256 in R0.
  unfold c_eq. apply not_true_iff_false. intros He. apply bv_eqb_eq in He. apply (f_equal (fun w => Z.testbit (bv_unsigned w) 15)) in He.
  assert (Hx0 : v_xor v (Z_to_bv 64 0) = v).
  { unfold v_xor. change (bv_unsigned (Z_to_bv 64 0)) with 0. rewrite Z.lxor_0_r. apply Z_to_bv_bv_unsigned. }
  rewrite Hx0 in He.
  unfold v_and, v_or, v_sub in He. rewrite !Z_to_bv_unsigned in He. unfold bv_wrap, bv_modulus in He. change (2 ^ Z.of_N 64) with (2 ^ 64) in He.
  change (bv_unsigned (Z_to_bv 64 MC_C)) with MC_C in He. change (bv_unsigned (Z_to_bv 64 MC_H)) with MC_H in He.
  repeat first [ rewrite Z.land_spec in He | rewrite Z.lor_spec in He | rewrite Z.mod_pow2_bits_low in He by lia ].
  change (Z.testbit MC_H 15) with true in He.
  assert (Hx : Z.testbit (bv_unsigned v) 15 = false).
  { rewrite <- (Z.mod_pow2_bits_low (bv_unsigned v) 16 15) by lia. rewrite Hv16. apply (Z_testbit_high 8); lia. }
  assert (Hs : Z.testbit (MC_C - bv_unsigned v) 15 = false).
  { rewrite <- (Z.mod_pow2_bits_low _ 16 15) by lia.
    rewrite Zminus_mod, Hv16. unfold MC_C.
    change (72340172838076672 mod 2 ^ 16) with 256.
    rewrite Z.mod_small by (change (2 ^ 16) with 65536; lia). apply (Z_testbit_high 8); lia. }
  change (MC_C mod 2 ^ 64) with MC_C in He. rewrite Hs, Hx in He. discriminate.
Qed.

#[using="Type"] Lemma qpc_btgt : forall k d, d mod 4 = 0 -> btgt (qpc pcw k) d = qpc pcw (k + d / 4).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros k d Hd. unfold btgt, v_addi, qpc. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite Zplus_mod_idemp_l. f_equal.
  pose proof (Z.div_mod d 4 ltac:(lia)). lia.
Qed.

#[using="Type"] Lemma getr_x0 : forall regs, getr regs (xr 0) = Z_to_bv 64 0.
Proof. LiaFast.lf_pins LiaFast.u0. intros regs. unfold getr. replace (bv_eqb (xr 0) 0%bv) with true by (vm_compute; reflexivity). reflexivity. Qed.

Ltac neqr := first [ assumption | apply not_eq_sym; assumption |
                     let Hc := fresh "Hc" in intro Hc; apply (f_equal bv_unsigned) in Hc; vm_compute in Hc; discriminate ].
Ltac gsimp := repeat first [ rewrite getr_same by neqr | rewrite getr_other by neqr ].
Ltac nzr := repeat match goal with |- context [bv_eqb (xr ?k) 0%bv] => replace (bv_eqb (xr k) 0%bv) with false by (vm_compute; reflexivity) end.

(* [comment removed for export] *)
#[using="J0 J1 J2 J3 J4 J5 J18 J19 J20 J13 J14 J15 J11 J12 J17"] Theorem mc_isteps : forall regs mem rom (s n ra : word) (b0 b1 : byte) (rest : list byte),
  getr regs (xr 10) = s -> getr regs (xr 11) = Z_to_bv 64 0 -> getr regs (xr 12) = n ->
  getr regs (xr 13) = Z_to_bv 64 MC_C -> getr regs (xr 14) = Z_to_bv 64 MC_H -> getr regs (xr 15) = Z_to_bv 64 0 ->
  getr regs (xr 1) = ra -> 2 <= bv_unsigned n -> bv_unsigned ra mod 2 = 0 -> bv_unsigned s + 8 < 2 ^ 64 ->
  rdn segs mem s 8 = Some (b0 :: b1 :: rest) -> bv_unsigned b0 <> 0 -> bv_unsigned b1 = 0 ->
  rdn segs mem (v_addi s 1) 1 = Some [b1] -> rdn segs mem s 1 = Some [b0] ->
  exists regs',
    FxStep.isteps segs (mkst regs (qpc pcw 0) mem rom) (mkst regs' ra mem rom) /\
    getr regs' (xr 10) = v_addi s 1 /\ getr regs' (xr 12) = Z_to_bv 64 0 /\ getr regs' (xr 13) = v_addi n (-1) /\
    (forall r, r <> xr 10 -> r <> xr 12 -> r <> xr 13 -> r <> xr 17 -> r <> xr 5 -> getr regs' r = getr regs r).
Proof. LiaFast.lf_pins (fun (J0 J1 J2 J3 J4 J5 J18 J19 J20 J13 J14 J15 J11 J12 J17 : LiaFast.U) => LiaFast.u0).
  intros regs mem rom s n ra b0 b1 rest H10 H11 H12 H13 H14 H15 H1 Hn Hra Hs HW Hb0 Hb1 HB1 HB0.
  destruct J0 as (w0 & F0 & E0 & D0). destruct J1 as (w1 & F1 & E1 & D1). destruct J2 as (w2 & F2 & E2 & D2).
  destruct J3 as (w3 & F3 & E3 & D3). destruct J4 as (w4 & F4 & E4 & D4). destruct J5 as (w5 & F5 & E5 & D5).
  destruct J18 as (w18 & F18 & E18 & D18). destruct J19 as (w19 & F19 & E19 & D19). destruct J20 as (w20 & F20 & E20 & D20).
  destruct J13 as (w13 & F13 & E13 & D13). destruct J14 as (w14 & F14 & E14 & D14). destruct J15 as (w15 & F15 & E15 & D15).
  destruct J11 as (w11 & F11 & E11 & D11). destruct J12 as (w12 & F12 & E12 & D12). destruct J17 as (w17 & F17 & E17 & D17).
  set (v := le_bytes_to_word (b0 :: b1 :: rest)).
  assert (Hlen : length (b0 :: b1 :: rest) = 8%nat) by exact (rdn_length _ _ _ _ _ HW).
  assert (Hv : bytes_le_to_Z (b0 :: b1 :: rest) = bv_unsigned v).
  { unfold v, le_bytes_to_word. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. symmetry. apply Z.mod_small.
    pose proof (bytes_le_to_Z_bound (b0 :: b1 :: rest)) as B. pose proof (bytes_le_to_Z_nonneg (b0 :: b1 :: rest)).
    rewrite Hlen in B. change (2 ^ Z.of_N 64) with (2 ^ (8 * Z.of_nat 8)). lia. }
  (* [comment removed for export] *)
  set (r1 := regupd regs (xr 17) v).
  assert (S0 : RiscvSemantics.step segs (mkst regs (qpc pcw 0) mem rom) = MachineOk (mkst r1 (qpc pcw 1) mem rom)).
  { rewrite (step_ld segs regs (qpc pcw 0) mem rom w0 (xr 17) (xr 10) (Z_to_bv 12 0) (b0 :: b1 :: rest) v F0 E0 D0); [| |exact Hv].
    - nzr. rewrite qpc_succ. reflexivity.
    - rewrite H10. change (bv_signed (Z_to_bv 12 0)) with 0. rewrite v_addi0. exact HW. }
  set (r2 := regupd r1 (xr 17) (v_xor v (Z_to_bv 64 0))).
  assert (S1 : RiscvSemantics.step segs (mkst r1 (qpc pcw 1) mem rom) = MachineOk (mkst r2 (qpc pcw 2) mem rom)).
  { rewrite (step_xor segs r1 (qpc pcw 1) mem rom w1 (xr 17) (xr 17) (xr 15) F1 E1 D1). nzr. rewrite qpc_succ.
    unfold r2, r1. gsimp. rewrite H15. reflexivity. }
  set (r3 := regupd r2 (xr 5) (v_sub (Z_to_bv 64 MC_C) (v_xor v (Z_to_bv 64 0)))).
  assert (S2 : RiscvSemantics.step segs (mkst r2 (qpc pcw 2) mem rom) = MachineOk (mkst r3 (qpc pcw 3) mem rom)).
  { rewrite (step_sub segs r2 (qpc pcw 2) mem rom w2 (xr 5) (xr 13) (xr 17) F2 E2 D2). nzr. rewrite qpc_succ.
    unfold r3, r2, r1. gsimp. rewrite H13. reflexivity. }
  set (r4 := regupd r3 (xr 17) (v_or (v_sub (Z_to_bv 64 MC_C) (v_xor v (Z_to_bv 64 0))) (v_xor v (Z_to_bv 64 0)))).
  assert (S3 : RiscvSemantics.step segs (mkst r3 (qpc pcw 3) mem rom) = MachineOk (mkst r4 (qpc pcw 4) mem rom)).
  { rewrite (step_or segs r3 (qpc pcw 3) mem rom w3 (xr 17) (xr 5) (xr 17) F3 E3 D3). nzr. rewrite qpc_succ.
    unfold r4, r3, r2. gsimp. reflexivity. }
  set (hz := v_and (v_or (v_sub (Z_to_bv 64 MC_C) (v_xor v (Z_to_bv 64 0))) (v_xor v (Z_to_bv 64 0))) (Z_to_bv 64 MC_H)).
  set (r5 := regupd r4 (xr 17) hz).
  assert (S4 : RiscvSemantics.step segs (mkst r4 (qpc pcw 4) mem rom) = MachineOk (mkst r5 (qpc pcw 5) mem rom)).
  { rewrite (step_and segs r4 (qpc pcw 4) mem rom w4 (xr 17) (xr 17) (xr 14) F4 E4 D4). nzr. rewrite qpc_succ.
    unfold r5, r4, r3, r2, r1. gsimp. rewrite H14. reflexivity. }
  (* [comment removed for export] *)
  assert (S5 : RiscvSemantics.step segs (mkst r5 (qpc pcw 5) mem rom) = MachineOk (mkst r5 (qpc pcw 18) mem rom)).
  { rewrite (step_bne_tk segs r5 (qpc pcw 5) mem rom w5 (xr 17) (xr 14) (Z_to_bv 13 52) F5 E5 D5).
    - rewrite qpc_btgt by reflexivity. reflexivity.
    - unfold r5, r4, r3, r2, r1. gsimp. rewrite H14. unfold hz. exact (mc_haszero b0 b1 rest Hb0 Hb1). }
  (* [comment removed for export] *)
  set (r6 := regupd r5 (xr 13) n).
  assert (S18 : RiscvSemantics.step segs (mkst r5 (qpc pcw 18) mem rom) = MachineOk (mkst r6 (qpc pcw 19) mem rom)).
  { rewrite (step_addi segs r5 (qpc pcw 18) mem rom w18 (xr 13) (xr 12) (Z_to_bv 12 0) F18 E18 D18). nzr. rewrite qpc_succ.
    unfold r6, r5, r4, r3, r2, r1. gsimp. rewrite H12. change (bv_signed (Z_to_bv 12 0)) with 0. rewrite v_addi0. reflexivity. }
  (* [comment removed for export] *)
  set (r7 := regupd r6 (xr 12) (Z_to_bv 64 (bv_unsigned b0))).
  assert (S19 : RiscvSemantics.step segs (mkst r6 (qpc pcw 19) mem rom) = MachineOk (mkst r7 (qpc pcw 20) mem rom)).
  { rewrite (step_lbu segs r6 (qpc pcw 19) mem rom w19 (xr 12) (xr 10) (Z_to_bv 12 0) b0 F19 E19 D19).
    - nzr. rewrite qpc_succ. reflexivity.
    - unfold r6, r5, r4, r3, r2, r1. gsimp. rewrite H10. change (bv_signed (Z_to_bv 12 0)) with 0. rewrite v_addi0. exact HB0. }
  (* [comment removed for export] *)
  assert (S20 : RiscvSemantics.step segs (mkst r7 (qpc pcw 20) mem rom) = MachineOk (mkst r7 (qpc pcw 13) mem rom)).
  { rewrite (step_bne_tk segs r7 (qpc pcw 20) mem rom w20 (xr 12) (xr 11) (Z_to_bv 13 8164) F20 E20 D20).
    - rewrite qpc_btgt by reflexivity. reflexivity.
    - unfold r7, r6, r5, r4, r3, r2, r1. gsimp. rewrite H11. unfold c_eq. apply not_true_iff_false. intros He. apply bv_eqb_eq in He.
      apply (f_equal bv_unsigned) in He. rewrite Z_to_bv_unsigned in He. change (bv_unsigned (Z_to_bv 64 0)) with 0 in He.
      pose proof (bv_unsigned_in_range _ b0) as R0. change (bv_modulus 8) with 256 in R0. unfold bv_wrap in He.
      rewrite Z.mod_small in He by (change (bv_modulus 64) with (2 ^ 64); lia). exact (Hb0 He). }
  (* [comment removed for export] *)
  set (r8 := regupd r7 (xr 13) (v_addi n (-1))).
  assert (S13 : RiscvSemantics.step segs (mkst r7 (qpc pcw 13) mem rom) = MachineOk (mkst r8 (qpc pcw 14) mem rom)).
  { rewrite (step_addi segs r7 (qpc pcw 13) mem rom w13 (xr 13) (xr 13) (Z_to_bv 12 4095) F13 E13 D13). nzr. rewrite qpc_succ.
    unfold r8, r7, r6. gsimp. reflexivity. }
  set (r9 := regupd r8 (xr 10) (v_addi s 1)).
  assert (S14 : RiscvSemantics.step segs (mkst r8 (qpc pcw 14) mem rom) = MachineOk (mkst r9 (qpc pcw 15) mem rom)).
  { rewrite (step_addi segs r8 (qpc pcw 14) mem rom w14 (xr 10) (xr 10) (Z_to_bv 12 1) F14 E14 D14). nzr. rewrite qpc_succ.
    unfold r9, r8, r7, r6, r5, r4, r3, r2, r1. gsimp. rewrite H10. reflexivity. }
  (* [comment removed for export] *)
  assert (S15 : RiscvSemantics.step segs (mkst r9 (qpc pcw 15) mem rom) = MachineOk (mkst r9 (qpc pcw 11) mem rom)).
  { rewrite (step_bne_tk segs r9 (qpc pcw 15) mem rom w15 (xr 13) (xr 0) (Z_to_bv 13 8176) F15 E15 D15).
    - rewrite qpc_btgt by reflexivity. reflexivity.
    - unfold r9, r8. gsimp. rewrite getr_x0.
      unfold c_eq. apply not_true_iff_false. intros He. apply bv_eqb_eq in He. apply (f_equal bv_unsigned) in He.
      unfold v_addi in He. rewrite Z_to_bv_unsigned in He. change (bv_unsigned (Z_to_bv 64 0)) with 0 in He. unfold bv_wrap in He.
      pose proof (bv_unsigned_in_range _ n) as Rn. change (bv_modulus 64) with (2 ^ 64) in *.
      rewrite Z.mod_small in He by lia. lia. }
  (* [comment removed for export] *)
  set (r10 := regupd r9 (xr 12) (Z_to_bv 64 (bv_unsigned b1))).
  assert (S11 : RiscvSemantics.step segs (mkst r9 (qpc pcw 11) mem rom) = MachineOk (mkst r10 (qpc pcw 12) mem rom)).
  { rewrite (step_lbu segs r9 (qpc pcw 11) mem rom w11 (xr 12) (xr 10) (Z_to_bv 12 0) b1 F11 E11 D11).
    - nzr. rewrite qpc_succ. reflexivity.
    - unfold r9. gsimp. change (bv_signed (Z_to_bv 12 0)) with 0. rewrite v_addi0. exact HB1. }
  assert (S12 : RiscvSemantics.step segs (mkst r10 (qpc pcw 12) mem rom) = MachineOk (mkst r10 (qpc pcw 17) mem rom)).
  { rewrite (step_beq_tk segs r10 (qpc pcw 12) mem rom w12 (xr 12) (xr 11) (Z_to_bv 13 20) F12 E12 D12).
    - rewrite qpc_btgt by reflexivity. reflexivity.
    - unfold r10, r9, r8, r7, r6, r5, r4, r3, r2, r1. gsimp. rewrite H11, Hb1. reflexivity. }
  (* [comment removed for export] *)
  assert (S17 : RiscvSemantics.step segs (mkst r10 (qpc pcw 17) mem rom) = MachineOk (mkst r10 ra mem rom)).
  { rewrite (step_jalr_gen segs r10 (qpc pcw 17) mem rom w17 (xr 0) (xr 1) (Z_to_bv 12 0) F17 E17 D17).
    replace (bv_eqb (xr 0) 0%bv) with true by (vm_compute; reflexivity). cbv beta iota.
    unfold r10, r9, r8, r7, r6, r5, r4, r3, r2, r1. gsimp. rewrite H1. f_equal. f_equal. change (bv_signed (Z_to_bv 12 0)) with 0.
    unfold jalr_tgt, jalr_tgtZ. rewrite Z.add_0_r. apply bv_eq. rewrite Z_to_bv_unsigned.
    rewrite land_m2_even.
    - unfold bv_wrap. apply Z.mod_small. exact (bv_unsigned_in_range _ ra).
    - change 1 with (Z.ones 1). rewrite Z.land_ones by lia. exact Hra. }
  exists r10. split.
  - repeat (eapply FxStep.ist_step; [reflexivity | eassumption |]). apply FxStep.ist_refl.
  - unfold r10, r9, r8, r7, r6, r5, r4, r3, r2, r1.
    split; [gsimp; reflexivity|]. split; [gsimp; rewrite Hb1; reflexivity|]. split; [gsimp; reflexivity|].
    intros r N10 N12 N13 N17 N5. gsimp. reflexivity.
Qed.
End MC.
(* [comment removed for export] *)
