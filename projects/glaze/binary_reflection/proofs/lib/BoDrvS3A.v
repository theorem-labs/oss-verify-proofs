(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia LinuxProcessSemantics.LinuxProcessSem.BvBase OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageBoth OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoDrvInstFactsA.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageBoth OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA.BoDrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA.BoDrvNodesP OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Definition PERM_A_lit : list (Z * Z) :=
  [(FILE1, FILE1 + 232); (FILE2, FILE2 + 232); (SBUF0, SBUF0 + 0x408); (COMPLETED, COMPLETED + 1); (INIT_BYTE, INIT_BYTE + 8);
   (NEWH_CELL, NEWH_CELL + 8); (ERRNO, ERRNO + 4); (ATEXIT_LO, ATEXIT_LO + 24); (EXIT_LOCK, EXIT_LOCK + 4);
   (READ_STAGE, READ_STAGE + 65536); (REG_FLAG, REG_FLAG + 8); (ATX_F1, ATX_F1 + 8); (ATX_A1, ATX_A1 + 8)].   (* [comment removed for export] *)
Lemma PERM_A_den : forall E, wins_den E PERM_A = PERM_A_lit.
Proof. intros E. reflexivity. Qed.

Lemma PERM_files_A : forall E a,
  (DNA.STDOUT_F <= a < DNA.STDOUT_F + 232 \/ DNA.STDERR_F <= a < DNA.STDERR_F + 232) -> in_wins (wins_den E PERM_A) a.
Proof.
  intros E a Ha. rewrite PERM_A_den. unfold in_wins, PERM_A_lit.
  destruct Ha as [Ha|Ha].
  - exists FILE1, (FILE1 + 232). split; [left; reflexivity|]. unfold FILE1. unfold DNA.STDOUT_F in Ha. lia.
  - exists FILE2, (FILE2 + 232). split; [right; left; reflexivity|]. unfold FILE2. unfold DNA.STDERR_F in Ha. lia.
Qed.

(* [comment removed for export] *)
Lemma PERM_flag_A : forall a, DNA.DTOR_FLAG <= a < DNA.DTOR_FLAG + 8 -> in_wins PERM_A_lit a.
Proof.
  intros a Ha. unfold in_wins, PERM_A_lit. exists REG_FLAG, (REG_FLAG + 8). split; [do 10 right; left; reflexivity|].
  unfold REG_FLAG. unfold DNA.DTOR_FLAG in Ha. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition wins_apart_b (W P : list (Z * Z)) : bool :=
  forallb (fun w => forallb (fun q => (Z.leb (snd w) (fst q) || Z.leb (snd q) (fst w))%bool) P) W.
Lemma wins_apart_b_sound : forall W P, wins_apart_b W P = true ->
  forall lo hi plo phi, In (lo, hi) W -> In (plo, phi) P -> hi <= plo \/ phi <= lo.
Proof.
  intros W P H lo hi plo phi Hw Hp. unfold wins_apart_b in H.
  pose proof (proj1 (forallb_forall _ _) (proj1 (forallb_forall _ _) H _ Hw) _ Hp) as X. cbn [fst snd] in X.
  apply orb_prop in X as [X|X]; apply Z.leb_le in X; [left | right]; exact X.
Qed.
Definition wins_in_b (W : list (Z * Z)) (lo hi : Z) : bool := forallb (fun w => (Z.leb lo (fst w) && Z.leb (snd w) hi)%bool) W.

Lemma SWIN_img_A : forall lo hi, In (lo, hi) PERM_A_lit ->
  g_ro_hi GBOTH <= lo /\ hi <= g_img_hi GBOTH /\ (forall plo phi, In (plo, phi) (g_priv GBOTH) -> hi <= plo \/ phi <= lo).
Proof.
  intros lo hi Hin.
  assert (HB : wins_in_b PERM_A_lit (g_ro_hi GBOTH) (g_img_hi GBOTH) = true) by (vm_compute; reflexivity).
  pose proof (proj1 (forallb_forall _ _) HB _ Hin) as X. cbn [fst snd] in X. apply andb_prop in X as [X1 X2].
  apply Z.leb_le in X1. apply Z.leb_le in X2. split; [exact X1|]. split; [exact X2|].
  intros plo phi Hp. exact (wins_apart_b_sound PERM_A_lit (g_priv GBOTH) ltac:(vm_compute; reflexivity) lo hi plo phi Hin Hp).
Qed.

Lemma SWIN_ok_A : AsVocab.as_wins_ok AsVocab.AsCells.both_addrs PERM_A_lit.
Proof.
  intros a (lo & hi & Hin & Ha).
  assert (HB : wins_in_b PERM_A_lit (ia_img_lo both_addrs) (ia_img_hi both_addrs) = true) by (vm_compute; reflexivity).
  pose proof (proj1 (forallb_forall _ _) HB _ Hin) as X. cbn [fst snd] in X. apply andb_prop in X as [X1 X2].
  apply Z.leb_le in X1. apply Z.leb_le in X2. split; [lia|].
  split; [|split].
  - intros (plo & phi & Hp & Hpa).
    destruct (wins_apart_b_sound PERM_A_lit (ia_priv both_addrs) ltac:(vm_compute; reflexivity) lo hi plo phi Hin Hp); lia.
  - intros Hr.
    destruct (wins_apart_b_sound PERM_A_lit [(ia_rtc_sb both_addrs, ia_rtc_sb both_addrs + 8); (ia_rtc_uar both_addrs, ia_rtc_uar both_addrs + 4)]
                ltac:(vm_compute; reflexivity) lo hi) with (plo := if Z.leb (ia_rtc_sb both_addrs) a && Z.ltb a (ia_rtc_sb both_addrs + 8) then ia_rtc_sb both_addrs else ia_rtc_uar both_addrs)
                (phi := if Z.leb (ia_rtc_sb both_addrs) a && Z.ltb a (ia_rtc_sb both_addrs + 8) then ia_rtc_sb both_addrs + 8 else ia_rtc_uar both_addrs + 4) as [Y|Y];
      try exact Hin;
      destruct (Z.leb (ia_rtc_sb both_addrs) a && Z.ltb a (ia_rtc_sb both_addrs + 8))%bool eqn:Hc;
      try (left; reflexivity); try (right; left; reflexivity);
      unfold AsVocab.in_rtc in Hr;
      try (apply andb_prop in Hc as [C1 C2]; apply Z.leb_le in C1; apply Z.ltb_lt in C2);
      try (apply andb_false_iff in Hc; rewrite Z.leb_gt, Z.ltb_ge in Hc); lia.
  - intros (plo & phi & Hp & Hpa).
    destruct (wins_apart_b_sound PERM_A_lit (ia_const both_addrs) ltac:(vm_compute; reflexivity) lo hi plo phi Hin Hp); lia.
Qed.
End BoDrvInstFactsA.
Require LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr OSSVerify.glaze.binary_reflection.images.AsanUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.AzDev OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoDrvS0A.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageBoth OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.AzDev OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA.BoDrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA.BoDrvNodesP OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pS_A : plan := X 1 (X 1 (W pEXIT)).
Definition pS_B : plan := X 1 (W (W pEXIT)).
Definition pS_C : plan := W (X 1 (W pEXIT)).
Definition pS3 (L : expr) (a b : Z) : plan := PSplit L a pS_A (PSplit L b pS_B pS_C).
(* [comment removed for export] *)
Definition planUn : plan :=
  X 68 (R (X 68 (X 71 (R (X 1 (X 1 (X 67 (X 73 (X 72 (X 1 (R (pS3 L0 66 73)))))))))))).
(* [comment removed for export] *)
Definition planUz : plan :=
  X 68 (R (X 68 (X 71 (R (X 1 (X 1 (X 67 (X 73 (X 72 (X 1 (R pS_A))))))))))).
Definition planU : plan := planUn.
(* [comment removed for export] *)
Definition pOPEN (id : nat) (k : plan) : plan := PRun SU (PExt id [STR1] k).
Definition pCOz : plan := X 68 (R (X 68 (X 71 (R (X 1 (X 1 (X 67 (X 73 (X 72 (X 1 (R pS_A))))))))))).   (* [comment removed for export] *)
Definition planCOa : plan := pOPEN 606 (X 68 (R (X 68 (X 71 (R (X 1 (X 1 (X 67 (X 73 (X 72 (X 1 (R (pS3 L1 62 63))))))))))))).
Definition planCOz : plan := pOPEN 606 pCOz.
Definition planCOt : plan := pOPEN 604 (X 68 (R (X 68 (X 71 (R (X 1 (X 1 (X 67 (X 73 (X 72 (X 1 pS_C))))))))))).
Definition FINFO : expr := EVar 4.      (* [comment removed for export] *)
Definition tMoa : acs := add_kn tMo [KRange L1 1 4095; KRange FINFO DNA.CLS_ABSENT DNA.CLS_ABSENT].
Definition tMod : acs := add_kn tMo [KRange L1 1 4095; KRange FINFO DNA.CLS_DIR DNA.CLS_DIR].       (* [comment removed for export] *)
(* [comment removed for export] *)
Definition tMu1n : acs := add_kn tMu1 [KRange L0 1 131071].
Definition tMu3n : acs := add_kn tMu3 [KRange L0 1 131071].
Definition tMu1z : acs := inst tMu1 3 (ELit 0).
Definition tMu3z : acs := inst tMu3 3 (ELit 0).
Definition tMoz : acs := add_kn (inst tMo 6 (ELit 0)) [KRange FINFO DNA.CLS_ABSENT DNA.CLS_ABSENT].
Definition shapeUz : shape := SEmitP 2 [SPLit [117; 115; 97; 103; 101; 58; 32; 32; 73; 78; 80; 85; 84; 10]] (SEmitP 1 [] (SExit 2)).   (* [comment removed for export] *)
Definition shapeCOz : shape := SEmitP 2 [SPLit [99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32; 10]] (SEmitP 1 [] (SExit 2)).   (* [comment removed for export] *)
Definition tMot : acs := add_kn tMo [KRange L1 4096 131071].
Definition MSG_CO : list Z := [99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32].   (* [comment removed for export] *)
Definition shapeCOa : shape :=
  SCase L1 62 (SEmitP 2 [SPLit MSG_CO; SPBlob 2; SPLit [10]] (SEmitP 1 [] (SExit 2)))
    (SCase L1 63 (SEmitP 2 [SPLit MSG_CO; SPBlob 2; SPLit [10]] (SEmitP 2 [] (SEmitP 1 [] (SExit 2))))
                 (SEmitP 2 [SPLit MSG_CO; SPBlob 2] (SEmitP 2 [SPLit [10]] (SEmitP 1 [] (SExit 2))))).
Definition shapeCOt : shape := SEmitP 2 [SPLit MSG_CO; SPBlob 2] (SEmitP 2 [SPLit [10]] (SEmitP 1 [] (SExit 2))).

Definition shapeU : shape :=
  SCase L0 66 (SEmitP 2 [SPLit [117; 115; 97; 103; 101; 58; 32]; SPBlob 1; SPLit [32; 73; 78; 80; 85; 84; 10]] (SEmitP 1 [] (SExit 2)))
    (SCase L0 73 (SEmitP 2 [SPLit [117; 115; 97; 103; 101; 58; 32]; SPBlob 1; SPLit [32; 73; 78; 80; 85; 84; 10]] (SEmitP 2 [] (SEmitP 1 [] (SExit 2))))
                 (SEmitP 2 [SPLit [117; 115; 97; 103; 101; 58; 32]; SPBlob 1] (SEmitP 2 [SPLit [32; 73; 78; 80; 85; 84; 10]] (SEmitP 1 [] (SExit 2))))).

(* [comment removed for export] *)
Definition pCO_err : plan := X 68 (R (X 68 (X 71 (R (X 1 (X 1 (X 67 (X 73 (X 72 (X 1 (R (pS3 L1 62 63)))))))))))).   (* [comment removed for export] *)
Definition planD1 : plan := PRun SU (PAlt2 603 [STR1] pCO_err (PRun SU (PHandoffW 1 []))).
Definition hM1d_def : acs := hole_of tMod (CHKa HS0 BF FUEL tMod planD1).      (* [comment removed for export] *)
Definition hM1d : acs := Eval vm_compute in hM1d_def.                           (* [comment removed for export] *)
Definition shapeD1 : shape := SAlt2 shapeCOa (SHole 1).
(* [comment removed for export] *)
Definition hN1d_def : acs := match M12 hM1d with Some (_, cb) => cb | None => hM1d end.
Definition hN1d : acs := Eval vm_compute in hN1d_def.
Definition MSG_RE : list Z := [99; 108; 105; 58; 32; 114; 101; 97; 100; 32; 101; 114; 114; 111; 114; 32; 111; 110; 32].   (* [comment removed for export] *)
Definition planD2 : plan := R (X 61 (X 68 (R (X 68 (X 71 (R (X 1 (X 1 (X 67 (X 73 (X 72 (X 1 (R (pS3 L1 60 61)))))))))))))).
Definition shapeD2 : shape :=
  SCase L1 60 (SEmitP 2 [SPLit MSG_RE; SPBlob 2; SPLit [10]] (SEmitP 1 [] (SExit 2)))
    (SCase L1 61 (SEmitP 2 [SPLit MSG_RE; SPBlob 2; SPLit [10]] (SEmitP 2 [] (SEmitP 1 [] (SExit 2))))
                 (SEmitP 2 [SPLit MSG_RE; SPBlob 2] (SEmitP 2 [SPLit [10]] (SEmitP 1 [] (SExit 2))))).

(* [comment removed for export] *)
Lemma certU1 : CHKa HS0 BF FUEL tMu1n planU = COk shapeU. Proof. vmc. Qed.
Lemma certU3 : CHKa HS0 BF FUEL tMu3n planU = COk shapeU. Proof. vmc. Qed.
Lemma certU1z : CHKa HS0 BF FUEL tMu1z planUz = COk shapeUz. Proof. vmc. Qed.
Lemma certU3z : CHKa HS0 BF FUEL tMu3z planUz = COk shapeUz. Proof. vmc. Qed.
Lemma gplanU : gplan_ok planU = true. Proof. vmc. Qed.
Lemma certCOa : CHKa HS0 BF FUEL tMoa planCOa = COk shapeCOa. Proof. vmc. Qed.
Lemma certCOz : CHKa HS0 BF FUEL tMoz planCOz = COk shapeCOz. Proof. vmc. Qed.
Lemma certCOt : CHKa HS0 BF FUEL tMot planCOt = COk shapeCOt. Proof. vmc. Qed.
Lemma certD1 : CHKz (HSof1 hM1d) BF FUEL tMod planD1 = COk shapeD1.   (* [comment removed for export] *) Proof. vmc. Qed.

Lemma certD2 : CHKz HS0 BF FUEL hN1d planD2 = COk shapeD2. Proof. vmc. Qed.
(* [comment removed for export] *)
End BoDrvS0A.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageBoth OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.AzDev OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageBoth OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.AzDev OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA.BoDrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA.BoDrvNodesP OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Definition P_AFTER_CLOSE : Z := 0x9d12c.

     (* [comment removed for export] *)
(* [comment removed for export] *)
Definition BUF : expr := EVar 1.
Definition CAP : expr := EVar 2.
Definition LEN : expr := EVar 3.
(* [comment removed for export] *)
Definition B0 : expr := EBlob false 3 0 1.
Definition B1sx : expr := EBlob true 3 1 1.
Definition B2 : expr := EBlob false 3 2 1.
Definition NXC : nat := 27.
Definition MTR : expr := EVar 5.             (* [comment removed for export] *)              (* [comment removed for export] *)
Definition BLEN : expr := K 16.             (* [comment removed for export] *)
Definition M63 : Z := 2 ^ 63 - 1.
(* [comment removed for export] *)
Definition CFGX : expr := EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 144115188075855872) B1sx) (ELit 49)) B0.
Definition PAYX : expr := esub LEN (eadd CFGX (ELit 6)).
Definition CALLSB : expr := eaddz (EAlu Instr.ALU_AND B2 (ELit 3)) 1.
Definition B1S : expr := B1sx.

(* [comment removed for export] *)
Definition regsC : list expr :=
  [ELit 0; K 0; eaddz SP0 (-80); ELit GP; ELit TP;
   K 1; K 2; K 3;
   ELit 2;                 (* [comment removed for export] *)
   BUF;                    (* [comment removed for export] *)
   ELit 0; K 4; K 5; K 6; K 7; K 8; K 9; K 10;   (* [comment removed for export] *)
   K 11;                   (* [comment removed for export] *)
   LEN;                    (* [comment removed for export] *)
   ELit 3;                 (* [comment removed for export] *)
   CAP;                    (* [comment removed for export] *)
   ELit READ_STAGE;        (* [comment removed for export] *)
   ELit 0;                 (* [comment removed for export] *)
   ELit 0; ELit 0; ELit 0; ELit 0;
   K 12; K 13; K 14; K 15].

(* [comment removed for export] *)
Definition FW_b : saddr := SA SP0 (- YLO).
Definition FW_n : expr := ELit (YLO + WSTK).
Definition blockA (h L : expr) (Llo : Z) : list kentry :=
  [KRange h 4112 (PTRHI - Llo); KRange (eadd h L) (4112 + Llo) PTRHI; KAlign h 16;
   KWr (SA h 0) L; KUnk (SA h 0) L; KShOk (SA h 0) L;
   KDisj (SA h 0) L FW_b FW_n; KDisj (SA h 0) L (SA (ELit 0) 0x10000) (ELit 0x653000);
   KDisj (SA h 0) L (SA (ELit 0) SHMAPLO) (ELit SHMAPLEN)]
  ++ map (fun w => KDisj (SA h 0) L (SA (fst w) 0) (snd w)) PERM_A.
(* [comment removed for export] *)
Definition KIMG_C : list kentry := List.filter (fun K : kentry => match K with KImg lo _ => negb (Z.eqb lo READ_STAGE) | _ => true end) KIMG_A.
(* [comment removed for export] *)
Definition knC : list kentry :=
  [ KRange SP0 (CEIL + YLO) (HI47 - 48); KAlign SP0 16;
    KRange MTR 0 DMTRHI; KRange LEN 0 (2 ^ 26 - 1); KRange CAP 65536 (2 ^ 26); KRange (esub CAP LEN) 0 (2 ^ 26); KRange CFGX 0 32767;   (* [comment removed for export] *)
    KRange B0 0 255; KRange B2 0 255; KRange B1S 0 (2 ^ 64 - 1); KRange TID 1 4194303;
    KRange BLEN 3 65536; KBlob (SA BUF 0) BLEN 3;                 (* [comment removed for export] *)
    KWord (SA (ELit 0) TID_CELL) 4 TID; KWord (SA (ELit 0) CANARY) 8 CAN;
    KWr (SA SP0 (- YLO)) (ELit YLO); KUnk (SA SP0 (- YLO)) (ELit YLO); KShOk (SA SP0 (- YLO)) (ELit (YLO + 48));
    KWord (SA SP0 (-8)) 8 (ELit RA_MAIN) ]
  ++ map (fun w => KWr (SA (fst w) 0) (snd w)) PERM_A
  ++ blockA BUF CAP 65536 ++ RTCELLS ++ LOWSH ++ GLZSH ++ KIMG_C.
Definition mkT (p : Z) (regs : list expr) (k : list kentry) (nx : nat) (vis : list (expr * expr)) : acs :=
  ACS (mk_ss p regs k nx) [] 0 YLO 0 vis PERM_A 0 (eaddz SP0 0) FdStd false MTR [] (ELit FMIN).
Definition tinC : acs := mkT P_AFTER_CLOSE regsC knC NXC [(BUF, CAP)].
(* [comment removed for export] *)
Definition tinC3 : acs := add_kn tinC [KRange LEN 6 (2 ^ 26 - 1); KRange PAYX 0 (2 ^ 26)].

(* [comment removed for export] *)
Definition planC3 : plan :=
  R (PSplit CFGX 0
    (R (PSplit PAYX 0 (R (PHandoffW 1 [])) (R (PHandoffW 2 []))))
    (R (PFact (KRange CALLSB 1 4) (PSplit PAYX 0 (R (PHandoffW 3 [])) (R (PHandoffW 4 [])))))).

(* [comment removed for export] *)
Definition CHKS (hs : nat -> option acs) : acs -> plan -> cres := CHKz hs BF FUEL.   (* [comment removed for export] *)
Definition holeEA_def : acs := hole_of tinC (CHKS HS0 tinC3 planC3).
Definition holeEA : acs := Eval vm_compute in holeEA_def.
Definition HS1 (h : nat) : option acs := match h with 1%nat => Some holeEA | _ => None end.
Definition holePA_def : acs := hole_of tinC (CHKS HS1 tinC3 planC3).
Definition holePA : acs := Eval vm_compute in holePA_def.
Definition HS2 (h : nat) : option acs := match h with 1%nat => Some holeEA | 2%nat => Some holePA | _ => None end.
Definition holeEB_def : acs := hole_of tinC (CHKS HS2 tinC3 planC3).
Definition holeEB : acs := Eval vm_compute in holeEB_def.
Definition HS3 (h : nat) : option acs := match h with 1%nat => Some holeEA | 2%nat => Some holePA | 3%nat => Some holeEB | _ => None end.
Definition holePB_def : acs := hole_of tinC (CHKS HS3 tinC3 planC3).
Definition holePB : acs := Eval vm_compute in holePB_def.
Definition HSC (h : nat) : option acs :=
  match h with 1%nat => Some holeEA | 2%nat => Some holePA | 3%nat => Some holeEB | 4%nat => Some holePB | _ => None end.

Definition shapeC3 : shape := SCase CFGX 0 (SCase PAYX 0 (SHole 1) (SHole 2)) (SCase PAYX 0 (SHole 3) (SHole 4)).

(* [comment removed for export] *)
Definition noblob (K : kentry) : bool := match K with KBlob _ _ _ => false | KRange e _ _ => negb (expr_eqb e BLEN) | _ => true end.
Definition tinC1n : acs := add_kn (set_kn tinC (filter noblob (kn tinC))) [KRange LEN 0 5].
(* [comment removed for export] *)
Definition OVX : expr := esub (eadd CFGX (ELit 5)) LEN.
Definition tinC2 : acs := add_kn tinC [KRange LEN 6 (2 ^ 26 - 1); KRange OVX 0 32767].
Definition planD : plan := W (X 11 pEXIT).
Definition shapeD (msg : list Z) : shape := SEmitP 2 [SPLit msg] (SEmitP 1 [] (SExit 2)).
Definition zmsg_short : list Z := [99; 108; 105; 58; 32; 105; 110; 112; 117; 116; 32; 115; 104; 111; 114; 116; 101; 114; 32; 116; 104; 97; 110; 32; 104; 101; 97; 100; 101; 114; 10].
Definition zmsg_overrun : list Z := [99; 108; 105; 58; 32; 99; 111; 110; 102; 105; 103; 95; 108; 101; 110; 32; 111; 118; 101; 114; 114; 117; 110; 115; 32; 105; 110; 112; 117; 116; 10].

(* [comment removed for export] *)
Lemma certC3 : CHKS HSC tinC3 planC3 = COk shapeC3. Proof. vmc. Qed.
Lemma planC3_ok : gplan_ok planC3 = true. Proof. reflexivity. Qed.

Lemma certC1n : CHKS HS0 tinC1n planD = COk (shapeD zmsg_short). Proof. vmc. Qed.
Lemma certC2 : CHKS HS0 tinC2 planD = COk (shapeD zmsg_overrun). Proof. vmc. Qed.
Lemma planD_ok : gplan_ok planD = true. Proof. reflexivity. Qed.
(* [comment removed for export] *)
