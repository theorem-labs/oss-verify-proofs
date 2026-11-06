(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia LinuxProcessSemantics.LinuxProcessSem.BvBase OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageAsan OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsDrvInstFactsA.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageAsan OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA.AsDrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA.AsDrvNodesP OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA.
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
  g_ro_hi GASAN <= lo /\ hi <= g_img_hi GASAN /\ (forall plo phi, In (plo, phi) (g_priv GASAN) -> hi <= plo \/ phi <= lo).
Proof.
  intros lo hi Hin.
  assert (HB : wins_in_b PERM_A_lit (g_ro_hi GASAN) (g_img_hi GASAN) = true) by (vm_compute; reflexivity).
  pose proof (proj1 (forallb_forall _ _) HB _ Hin) as X. cbn [fst snd] in X. apply andb_prop in X as [X1 X2].
  apply Z.leb_le in X1. apply Z.leb_le in X2. split; [exact X1|]. split; [exact X2|].
  intros plo phi Hp. exact (wins_apart_b_sound PERM_A_lit (g_priv GASAN) ltac:(vm_compute; reflexivity) lo hi plo phi Hin Hp).
Qed.

Lemma SWIN_ok_A : AsVocab.as_wins_ok AsVocab.AsCells.asan_addrs PERM_A_lit.
Proof.
  intros a (lo & hi & Hin & Ha).
  assert (HB : wins_in_b PERM_A_lit (ia_img_lo asan_addrs) (ia_img_hi asan_addrs) = true) by (vm_compute; reflexivity).
  pose proof (proj1 (forallb_forall _ _) HB _ Hin) as X. cbn [fst snd] in X. apply andb_prop in X as [X1 X2].
  apply Z.leb_le in X1. apply Z.leb_le in X2. split; [lia|].
  split; [|split].
  - intros (plo & phi & Hp & Hpa).
    destruct (wins_apart_b_sound PERM_A_lit (ia_priv asan_addrs) ltac:(vm_compute; reflexivity) lo hi plo phi Hin Hp); lia.
  - intros Hr.
    destruct (wins_apart_b_sound PERM_A_lit [(ia_rtc_sb asan_addrs, ia_rtc_sb asan_addrs + 8); (ia_rtc_uar asan_addrs, ia_rtc_uar asan_addrs + 4)]
                ltac:(vm_compute; reflexivity) lo hi) with (plo := if Z.leb (ia_rtc_sb asan_addrs) a && Z.ltb a (ia_rtc_sb asan_addrs + 8) then ia_rtc_sb asan_addrs else ia_rtc_uar asan_addrs)
                (phi := if Z.leb (ia_rtc_sb asan_addrs) a && Z.ltb a (ia_rtc_sb asan_addrs + 8) then ia_rtc_sb asan_addrs + 8 else ia_rtc_uar asan_addrs + 4) as [Y|Y];
      try exact Hin;
      destruct (Z.leb (ia_rtc_sb asan_addrs) a && Z.ltb a (ia_rtc_sb asan_addrs + 8))%bool eqn:Hc;
      try (left; reflexivity); try (right; left; reflexivity);
      unfold AsVocab.in_rtc in Hr;
      try (apply andb_prop in Hc as [C1 C2]; apply Z.leb_le in C1; apply Z.ltb_lt in C2);
      try (apply andb_false_iff in Hc; rewrite Z.leb_gt, Z.ltb_ge in Hc); lia.
  - intros (plo & phi & Hp & Hpa).
    destruct (wins_apart_b_sound PERM_A_lit (ia_const asan_addrs) ltac:(vm_compute; reflexivity) lo hi plo phi Hin Hp); lia.
Qed.
End AsDrvInstFactsA.
Require LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr OSSVerify.glaze.binary_reflection.images.Asan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.AzDev OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsDrvS0A.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageAsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.AzDev OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA.AsDrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA.AsDrvNodesP OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA.
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
End AsDrvS0A.
Module AsDrvS1A.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageAsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.AzDev OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA.AsDrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA.AsDrvNodesP OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA AsDrvS0A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Definition FLEN : expr := EVar 4.         (* [comment removed for export] *)
Definition FLENHI : Z := 2 ^ 26.
Definition P_ECALL : Z := 0xf5fb0.


(* [comment removed for export] *)
Definition tMf : acs := add_kn tMo [KRange L1 1 4095; KRange FLEN 0 FLENHI].

(* [comment removed for export] *)
Definition planF0 : plan := PRun SU (PAlt2 602 [STR1; FLEN] pCO_err (PRun SU (PHandoffW 1 []))).
Definition hM1f_def : acs := hole_of tMf (CHKa HS0 BF FUEL tMf planF0).
Definition hM1f : acs := Eval vm_compute in hM1f_def.
Definition shapeF0 : shape := SAlt2 shapeCOa (SHole 1).

(* [comment removed for export] *)
Definition hN1f_def : acs := match M12 hM1f with Some (_, cb) => cb | None => hM1f end.
Definition hN1f : acs := Eval vm_compute in hN1f_def.
Definition hZ1f_def : acs := match M12 hM1f with Some (ca, _) => ca | None => hM1f end.
Definition hZ1f : acs := Eval vm_compute in hZ1f_def.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition hZ1d_def : acs := match M12 hM1d with Some (ca, _) => ca | None => hM1d end.
Definition hZ1d : acs := Eval vm_compute in hZ1d_def.

(* [comment removed for export] *)
Lemma certF0 : CHKz (HSof1 hM1f) BF FUEL tMf planF0 = COk shapeF0.   (* [comment removed for export] *) Proof. vmc. Qed.

(* [comment removed for export] *)
End AsDrvS1A.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS3A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsDrvK0A.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageAsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.AzDev OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA.AsDrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA.AsDrvNodesP OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA AsDrvS0A OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS3A AsDrvS1A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition PAYXb : expr := esub FLEN (eadd CFGX (ELit 6)).
Definition OVXb : expr := esub (eadd CFGX (ELit 5)) FLEN.

Definition tK0s : acs := add_kn hN1f [KRange FLEN 0 5].
Definition tK0o : acs := add_kn hN1f [KRange FLEN 6 65535; KRange OVXb 0 32767; KRange CFGX 0 32767; KRange B0 0 255; KRange B2 0 255; KRange B1S 0 (2 ^ 64 - 1)].
Definition tK0c : acs := add_kn hN1f [KRange FLEN 6 65535; KRange PAYXb 0 (2 ^ 26); KRange CFGX 0 32767; KRange B0 0 255; KRange B2 0 255; KRange B1S 0 (2 ^ 64 - 1)].

(* [comment removed for export] *)
Definition SUC : list Z := P_AFTER_CLOSE :: SU.
Definition RC (k : plan) : plan := PRun SUC k.
Definition XC (id : nat) (k : plan) : plan := PRun SUC (PExt id [] k).
(* [comment removed for export] *)
Definition pREST (h : nat) : plan := XC 1 (XC 61 (XC 62 (RC (PHandoffW h [])))).
Definition pSHORT (h1 h2 : nat) : plan := PSplit FLEN 64 (pREST h1) (XC 69 (pREST h2)).
(* [comment removed for export] *)
Definition planK0s : plan := RC (PSplit FLEN 0 (XC 61 (XC 62 (RC (PHandoffW 1 [])))) (XC 61 (pSHORT 2 3))).   (* [comment removed for export] *)
Definition planK0 : plan := RC (XC 61 (pSHORT 1 2)).

(* [comment removed for export] *)
Definition HS12 (a b : acs) (h : nat) : option acs := match h with 1%nat => Some a | 2%nat => Some b | _ => None end.
Definition hK0s_def : acs := hole_of tK0s (CHKa HS0 BF FUEL tK0s planK0s).          (* [comment removed for export] *)
Definition hK0s : acs := Eval vm_compute in hK0s_def.
Definition hK0s2_def : acs := hole_of tK0s (CHKa (HSof1 hK0s) BF FUEL tK0s planK0s). (* [comment removed for export] *)
Definition hK0s2 : acs := Eval vm_compute in hK0s2_def.
Definition hK0o_def : acs := hole_of tK0o (CHKa HS0 BF FUEL tK0o planK0).           (* [comment removed for export] *)
Definition hK0o : acs := Eval vm_compute in hK0o_def.
Definition hK0o2_def : acs := hole_of tK0o (CHKa (HSof1 hK0o) BF FUEL tK0o planK0). (* [comment removed for export] *)
Definition hK0o2 : acs := Eval vm_compute in hK0o2_def.
Definition hK0c_def : acs := hole_of tK0c (CHKa HS0 BF FUEL tK0c planK0).
Definition hK0c : acs := Eval vm_compute in hK0c_def.
Definition hK0c2_def : acs := hole_of tK0c (CHKa (HSof1 hK0c) BF FUEL tK0c planK0).
Definition hK0c2 : acs := Eval vm_compute in hK0c2_def.
(* [comment removed for export] *)
Definition ENT (h T : acs) : bool := entails_tw AASAN 0 NXC [(25%nat, FLEN)] h T.

(* [comment removed for export] *)
Lemma certK0s : CHKz (HS12 hK0s hK0s2) BF FUEL tK0s planK0s = COk (SCase FLEN 0 (SHole 1) (SHole 2)). Proof. vmc. Qed.
Lemma certK0o : CHKz (HS12 hK0o hK0o2) BF FUEL tK0o planK0 = COk (SCase FLEN 64 (SHole 1) (SHole 2)). Proof. vmc. Qed.
Lemma certK0c : CHKz (HS12 hK0c hK0c2) BF FUEL tK0c planK0 = COk (SCase FLEN 64 (SHole 1) (SHole 2)). Proof. vmc. Qed.
(* [comment removed for export] *)
Lemma entK0s : ENT hK0s tinC1n = true. Proof. vmc. Qed.
Lemma entK0s2 : ENT hK0s2 tinC1n = true. Proof. vmc. Qed.
Lemma entK0o : ENT hK0o tinC2 = true. Proof. vmc. Qed.
Lemma entK0o2 : ENT hK0o2 tinC2 = true. Proof. vmc. Qed.
Lemma entK0c : ENT hK0c tinC3 = true. Proof. vmc. Qed.
Lemma entK0c2 : ENT hK0c2 tinC3 = true. Proof. vmc. Qed.
(* [comment removed for export] *)
End AsDrvK0A.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.glaze.binary_reflection.images Require Import Asan.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageAsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.AzDev OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS3A. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageAsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.AzDev OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA.AsDrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA.AsDrvNodesP OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA AsDrvS0A OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS3A AsDrvS1A AsDrvK0A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Definition NXR : nat := 28.

(* [comment removed for export] *)
Definition tR1F : acs := add_kn hN1f [KRange FLEN 65536 FLENHI].
(* [comment removed for export] *)
Definition planR1F : plan := RC (XC 61 (XC 69 (XC 1 (RC (PHandoffW 1 []))))).
Definition hG1_def : acs := hole_of tR1F (CHKa HS0 BF FUEL tR1F planR1F).
Definition hG1 : acs := Eval vm_compute in hG1_def.
(* [comment removed for export] *)
Lemma certR1F : CHKz (HSof1 hG1) BF FUEL tR1F planR1F = COk (SHole 1).   (* [comment removed for export] *) Proof. vmc. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition hG1ok : acs := Eval vm_compute in (match M12 hG1 with Some (_, cb) => cb | None => hG1 end).
Definition hG1z : acs := Eval vm_compute in (match M12 hG1 with Some (ca, _) => ca | None => hG1 end).
(* [comment removed for export] *)
Definition planG : plan := X 1 (X 11 (R (PHandoffW 1 []))).
Definition hRD2_def : acs := hole_of hG1ok (CHKa HS0 BF FUEL hG1ok planG).
Definition hRD2 : acs := Eval vm_compute in hRD2_def.
(* [comment removed for export] *)
Lemma certG1 : CHKz (HSof1 hRD2) BF FUEL hG1ok planG = COk (SHole 1). Proof. vmc. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition RA_ICPT : Z := 0x5e260.        (* [comment removed for export] *)
Definition RA_RDMAIN : Z := 0x9c6a8.      (* [comment removed for export] *)
Definition RA_CP : Z := 0xfaaf4.          (* [comment removed for export] *)
Definition regsTR : list expr :=
  [ELit 0; ELit RA_CP; eaddz SP0 (-2224); ELit GP; ELit TP;
   K 1; K 2; K 3;
   eaddz SP0 (-80); ELit READ_STAGE;                                  (* [comment removed for export] *)
   ELit 3; ELit READ_STAGE; ELit 65536; ELit 0; ELit 0; ELit 0; ELit 0; ELit 63;   (* [comment removed for export] *)
   ELit 65536; ELit 3; ELit 1; CAP; ELit READ_STAGE; K 4;             (* [comment removed for export] *)
   ELit 0; ELit 0; ELit 0; ELit 0;
   K 12; K 13; K 14; K 15].
(* [comment removed for export] *)
Definition frameTR : list kentry :=
  [KWord (SA SP0 (-2216)) 8 (ELit RA_ICPT); KWord (SA SP0 (-2224)) 8 (eaddz SP0 (-80));
   KWord (SA SP0 (-128)) 8 (ELit 3); KWord (SA SP0 (-120)) 8 LEN; KWord (SA SP0 (-112)) 8 (K 5); KWord (SA SP0 (-104)) 8 BUF;
   KWord (SA SP0 (-96)) 8 (ELit 2); KWord (SA SP0 (-88)) 8 (ELit RA_RDMAIN);
   KWord (SA SP0 (-8)) 8 (ELit RA_MAIN)].
Definition knTR : list kentry :=
  [ KRange SP0 (CEIL + YLO) (HI47 - 48); KAlign SP0 16; KRange TID 1 4194303;
    KRange CAP 131072 (2 ^ 26); KRange LEN 65536 (2 ^ 26 - 65536); KRange (esub CAP LEN) 65536 (2 ^ 26); KRange FLEN 0 FLENHI;
    KRange MTR 0 DMTRHI ] ++ drv_ladder CAP MTR ++ [          (* [comment removed for export] *)
    KWord (SA (ELit 0) TID_CELL) 4 TID; KWord (SA (ELit 0) CANARY) 8 CAN;
    KWr (SA SP0 (- YLO)) (ELit YLO); KUnk (SA SP0 (- YLO)) (ELit YLO); KShOk (SA SP0 (- YLO)) (ELit (YLO + 48));
    KAlign BUF 2048; KBlob (SA BUF 0) (ELit 65536) 3 ]      (* [comment removed for export] *)
  ++ frameTR ++ map (fun w => KWr (SA (fst w) 0) (snd w)) PERM_A
  ++ blockA BUF CAP 131072 ++ RTCELLS ++ LOWSH ++ GLZSH ++ KIMG_C.
Definition mkTR (k : list kentry) : acs :=
  ACS (mk_ss P_ECALL regsTR k NXR) [] 0 YLO 0 [(BUF, CAP)] PERM_A 0 (eaddz SP0 0) (FdFile 3%nat FLEN LEN) false MTR [] (ELit FMIN).
Definition TR : acs := mkTR knTR.
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition REMX : expr := esub FLEN LEN.          (* [comment removed for export] *)
Definition ROOMX : expr := esub CAP LEN.         (* [comment removed for export] *)
(* [comment removed for export] *)
Definition WANT : expr := K 16.                  (* [comment removed for export] *)
Definition regsTRw : list expr := sr_upd (sr_upd regsTR 12 WANT) 18 WANT.
Definition knTRw : list kentry :=
  [ KRange SP0 (CEIL + YLO) (HI47 - 48); KAlign SP0 16; KRange TID 1 4194303;
    KRange CAP 131072 (2 ^ 26); KRange LEN 65536 (2 ^ 26 - 1); KRange ROOMX 1 65535; KRange WANT 1 65535; KRange (esub WANT ROOMX) 0 0; KRange FLEN 0 FLENHI;
    KRange MTR 0 DMTRHI ] ++ drv_ladder CAP MTR ++ [          (* [comment removed for export] *)
    KWord (SA (ELit 0) TID_CELL) 4 TID; KWord (SA (ELit 0) CANARY) 8 CAN;
    KWr (SA SP0 (- YLO)) (ELit YLO); KUnk (SA SP0 (- YLO)) (ELit YLO); KShOk (SA SP0 (- YLO)) (ELit (YLO + 48));
    KAlign BUF 2048; KBlob (SA BUF 0) (ELit 65536) 3 ]
  ++ [KWord (SA SP0 (-2216)) 8 (ELit RA_ICPT); KWord (SA SP0 (-2224)) 8 (eaddz SP0 (-80));
      KWord (SA SP0 (-128)) 8 (ELit 3); KWord (SA SP0 (-120)) 8 LEN; KWord (SA SP0 (-112)) 8 (K 5); KWord (SA SP0 (-104)) 8 BUF;
      KWord (SA SP0 (-96)) 8 (ELit 2); KWord (SA SP0 (-88)) 8 (ELit RA_RDMAIN); KWord (SA SP0 (-8)) 8 (ELit RA_MAIN)]
  ++ map (fun w => KWr (SA (fst w) 0) (snd w)) PERM_A
  ++ blockA BUF CAP 131072 ++ RTCELLS ++ LOWSH ++ GLZSH ++ KIMG_C.
Definition TRw : acs := ACS (mk_ss P_ECALL regsTRw knTRw NXR) [] 0 YLO 0 [(BUF, CAP)] PERM_A 0 (eaddz SP0 0) (FdFile 3%nat FLEN LEN) false MTR [] (ELit FMIN).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition tVP : acs := add_kn TR [KRange REMX 65536 FLENHI; KRange ROOMX 65537 (2 ^ 26)].
Definition planVP : plan := PExt 61 [] (X 69 (X 1 (R (PBranch (R (PHandoffW 1 [])) (R (PHandoffW 2 [])))))).
(* [comment removed for export] *)
Definition LENX' : expr := eaddz LEN 65536.
Definition tVF : acs := add_kn TR [KRange REMX 65536 FLENHI; KRange ROOMX 65536 65536; KRange CAP 131072 (2 ^ 25)].
Definition planVF : plan := PExt 61 [] (X 69 (X 1 (PFactVia LENX' CAP 131072 (2 ^ 25) (R (PHandoffW 1 []))))).
(* [comment removed for export] *)
Definition tVR : acs := add_kn TR [KRange REMX 65536 FLENHI; KRange ROOMX 65536 65536; KRange CAP (2 ^ 26) (2 ^ 26)].
(* [comment removed for export] *)
Definition pRF : plan := X 68 (R (R (X 1 (X 1 (X 1 (X 1 (X 1 (W pEXIT)))))))).
Definition planVR : plan := PExt 61 [] (X 69 (X 1 (PFactVia LENX' CAP (2 ^ 26) (2 ^ 26) pRF))).
Definition MSG_RF : list Z := [99; 108; 105; 58; 32; 105; 110; 112; 117; 116; 32; 62; 61; 32; 54; 55; 49; 48; 56; 56; 54; 52; 32;
                              98; 121; 116; 101; 115; 44; 32; 114; 101; 102; 117; 115; 101; 100; 10].  (* [comment removed for export] *)
Definition shapeRF : shape := SEmitP 2 [SPLit MSG_RF] (SEmitP 1 [] (SExit 2)).
(* [comment removed for export] *)
Definition pSREST (h1 h2 : nat) : plan := XC 1 (RC (PBranch (XC 61 (XC 62 (RC (PHandoffW h1 [])))) (XC 61 (XC 62 (RC (PHandoffW h2 [])))))).
Definition planVS : plan := PExt 61 [] (PSplit REMX 64 (pSREST 1 2) (XC 69 (pSREST 3 4))).
Definition tVS : acs := add_kn TR [KRange REMX 1 65535].
(* [comment removed for export] *)
Definition tV0 : acs := add_kn TR [KRange REMX 0 0].
Definition planV0 : plan := PExt 61 [] (XC 62 (RC (PHandoffW 1 []))).
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition factsC : list kentry := [KRange PAYXb 0 (2 ^ 26); KRange CFGX 0 32767; KRange B0 0 255; KRange B2 0 255; KRange B1S 0 (2 ^ 64 - 1)].
Definition tVSc : acs := add_kn tVS factsC.
Definition tV0c : acs := add_kn tV0 factsC.

(* [comment removed for export] *)
Definition HS4 (a b c d : acs) (h : nat) : option acs := match h with 1%nat => Some a | 2%nat => Some b | 3%nat => Some c | 4%nat => Some d | _ => None end.
Definition CH (hs : nat -> option acs) (t : acs) (p : plan) : cres := CHKz hs BF FUEL t p.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition hVP1 : acs := Eval vm_compute in hole_of tVP (CH HS0 tVP planVP).
Definition hVP2 : acs := Eval vm_compute in hole_of tVP (CH (HSof1 hVP1) tVP planVP).
(* [comment removed for export] *)
Definition hVF : acs := Eval vm_compute in hole_of tVF (CH HS0 tVF planVF).
Definition hVFok : acs := Eval vm_compute in (match M12 hVF with Some (_, cb) => cb | None => hVF end).
Definition hVFz : acs := Eval vm_compute in (match M12 hVF with Some (ca, _) => ca | None => hVF end).
Definition hVG : acs := Eval vm_compute in hole_of hVFok (CH HS0 hVFok planG).
(* [comment removed for export] *)
Definition h4 (t : acs) (p : plan) : acs * acs * acs * acs :=
  let a := hole_of t (CH HS0 t p) in let b := hole_of t (CH (HSof1 a) t p) in
  let c := hole_of t (CH (HS4 a b a a) t p) in let d := hole_of t (CH (HS4 a b c a) t p) in (a, b, c, d).
Definition hVSc : acs * acs * acs * acs := Eval vm_compute in h4 tVSc planVS.
Definition hV0c : acs := Eval vm_compute in hole_of tV0c (CH HS0 tV0c planV0).
Definition HSq (q : acs * acs * acs * acs) : nat -> option acs := let '(a, b, c, d) := q in HS4 a b c d.

(* [comment removed for export] *)
Lemma certVP : CH (HS12 hVP1 hVP2) tVP planVP = COk (SHole 1). Proof. vmc. Qed.
Lemma certVF : CH (HSof1 hVF) tVF planVF = COk (SHole 1). Proof. vmc. Qed.
Lemma certVG : CH (HSof1 hVG) hVFok planG = COk (SHole 1). Proof. vmc. Qed.
Lemma certVR : CH HS0 tVR planVR = COk shapeRF. Proof. vmc. Qed.
Lemma certVSc : CH (HSq hVSc) tVSc planVS = COk (SCase REMX 64 (SHole 1) (SHole 3)). Proof. vmc. Qed.
Lemma certV0c : CH (HSof1 hV0c) tV0c planV0 = COk (SHole 1). Proof. vmc. Qed.
(* [comment removed for export] *)
Definition ENTR (h T : acs) : bool := entails_tw AASAN 0 NXR [] h T.   (* [comment removed for export] *)
Lemma entVP1 : ENTR hVP1 TR = true. Proof. vmc. Qed.
Lemma entVP2 : ENTR hVP2 TRw = true. Proof. vmc. Qed.
Lemma entVG : ENTR hVG TR = true. Proof. vmc. Qed.
Lemma entG1 : ENTR hRD2 TR = true. Proof. vmc. Qed.      (* [comment removed for export] *)
Definition ENTC (h T : acs) : bool := entails_tw AASAN 0 NXC [(25%nat, ELit 65536)] h T.   (* [comment removed for export] *)
Lemma entVSc : let '(a, b, c, d) := hVSc in (ENTC a tinC3 && ENTC b tinC3 && ENTC c tinC3 && ENTC d tinC3)%bool = true. Proof. vmc. Qed.
Lemma entV0c : ENTC hV0c tinC3 = true. Proof. vmc. Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
