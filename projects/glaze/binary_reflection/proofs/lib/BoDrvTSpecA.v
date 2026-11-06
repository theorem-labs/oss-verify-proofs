(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr OSSVerify.glaze.binary_reflection.images.AsanUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageBoth OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.AzDev OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvS3A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoDrvTA.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageBoth OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.AzDev OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA.BoDrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA.BoDrvNodesP OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvS3A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pEXITF (flush : bool) : plan := pEXIT.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_tail (flush : bool) : plan := PExt 11 [] (pEXITF flush).
(* [comment removed for export] *)
Definition p_after (flush : bool) : plan := PExt 11 [] (R (PCaseReg 21 M63 (R (p_tail flush)) (R (p_tail flush)))).   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_printf (first : bool) (k : plan) : plan :=
  X 68 (R (R (X 68 (R (R (X 1 (X 1 (X 2 (X 1
    (if first then X 1 (R (PExt 63 [] (W (X 1 k)))) else X 1 (X 1 k))))))))))).
Fixpoint p_calls (fz : nat) (n : nat) (first : bool) (flush : bool) : plan :=
  match n with
  | O => R (p_after flush)
  | Datatypes.S n' => X fz (p_printf first (p_calls fz n' false flush))
  end.
Definition split_calls (calls : expr) (k : nat -> plan) : plan :=
  PSplit calls 1 (k 1%nat) (PSplit calls 2 (k 2%nat) (PSplit calls 3 (k 3%nat) (k 4%nat))).
Definition planE (calls : expr) : plan := split_calls calls (fun n => p_calls 121 n true (Nat.ltb 1 n)).
Definition planN (calls : expr) : plan := split_calls calls (fun n => X 1 (p_calls 120 n true (Nat.ltb 1 n))).

(* [comment removed for export] *)
Fixpoint p_callsL (c : expr) (fz : nat) (more : nat) (j : Z) (first : bool) : plan :=
  match more with
  | O => X fz (p_printf first (R (p_after true)))
  | Datatypes.S m => X fz (p_printf first (PSplit c j (R (p_after (Z.ltb 1 j))) (p_callsL c fz m (j + 1) false)))
  end.
Definition planEL (calls : expr) : plan := p_callsL calls 121 3 1 true.
Definition planNL (calls : expr) : plan := X 1 (p_callsL calls 120 3 1 true).

(* [comment removed for export] *)
Definition tinEA : acs := holeEA.   Definition tinPA : acs := holePA.
Definition tinEB : acs := holeEB.   Definition tinPB : acs := holePB.
Definition okchild (h : acs) : acs := match M12 h with Some (_, cb) => cb | None => h end.
Definition nullchild (h : acs) : acs := match M12 h with Some (ca, _) => ca | None => h end.
Definition tinNA : acs := Eval vm_compute in okchild tinPA.   Definition tin0A : acs := Eval vm_compute in nullchild tinPA.
Definition tinNB : acs := Eval vm_compute in okchild tinPB.   Definition tin0B : acs := Eval vm_compute in nullchild tinPB.
Definition CALLSA : expr := ELit 1.

(* [comment removed for export] *)
Fixpoint zl (n : nat) : list Z := match n with O => [] | Datatypes.S k => 48 :: 10 :: zl k end.
Definition s_calls (n : nat) : shape :=
  SEmitP 1 [SPLit [48]; SPLit [10]] (SEmitP 1 (match n with 1%nat => [] | _ => [SPLit (zl (n - 1))] end) (SExit 0)).

Definition shapeA : shape := s_calls 1.


(* [comment removed for export] *)
Definition shapeL (calls : expr) : shape :=
  SEmitP 1 [SPLit [48]; SPLit [10]]
    (SCase calls 1 (SEmitP 1 [] (SExit 0))
      (SCase calls 2 (SEmitP 1 [SPLit (zl 1)] (SExit 0))
        (SCase calls 3 (SEmitP 1 [SPLit (zl 2)] (SExit 0)) (SEmitP 1 [SPLit (zl 3)] (SExit 0))))).
(* [comment removed for export] *)
Lemma planE_ok : forall e, gplan_ok (planE e) = true. Proof. reflexivity. Qed.
Lemma planN_ok : forall e, gplan_ok (planN e) = true. Proof. reflexivity. Qed.
Lemma planEL_ok : forall e, gplan_ok (planEL e) = true. Proof. reflexivity. Qed.
Lemma planNL_ok : forall e, gplan_ok (planNL e) = true. Proof. reflexivity. Qed.


End BoDrvTA.
Module BoDrvTAcertA.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvS3A BoDrvTA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Lemma certEA : CHKa HS0 BF FUEL tinEA (planE CALLSA) = COk shapeA. Proof. vmc. Qed.
Lemma certNA : CHKa HS0 BF FUEL tinNA (planN CALLSA) = COk shapeA. Proof. vmc. Qed.
End BoDrvTAcertA.
Module BoDrvTAcertEB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvS3A BoDrvTA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Lemma certEBL : CHKa HS0 BF FUEL tinEB (planEL CALLSB) = COk (shapeL CALLSB). Proof. vmc. Qed.
End BoDrvTAcertEB.
Module BoDrvTAcertNB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvS3A BoDrvTA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Lemma certNBL : CHKa HS0 BF FUEL tinNB (planNL CALLSB) = COk (shapeL CALLSB). Proof. vmc. Qed.
End BoDrvTAcertNB.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvS2A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoDrvZcertsA.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageBoth OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.AzDev OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA.BoDrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA.BoDrvNodesP OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvS3A.BoDrvS0A OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvS3A OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvS2A.BoDrvS1A OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvS2A.BoDrvK0A OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvS2A BoDrvTA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma M12_hM1f : M12 hM1f = Some (hZ1f, hN1f). Proof. vmc. Qed.
Lemma M12_hG1 : M12 hG1 = Some (hG1z, hG1ok). Proof. vmc. Qed.
Lemma M12_hVF : M12 hVF = Some (hVFz, hVFok). Proof. vmc. Qed.
Lemma M12_tinPA : M12 tinPA = Some (tin0A, tinNA). Proof. vmc. Qed.
Lemma M12_tinPB : M12 tinPB = Some (tin0B, tinNB). Proof. vmc. Qed.
(* [comment removed for export] *)
End BoDrvZcertsA.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageBoth OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvS3A OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvS2A OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvNodesSoundA5 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvS0SoundA OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvCertSoundZ OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvGlueA. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRel OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageBoth OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.FileSim OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA.BoDrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA.BoDrvNodesP OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvS3A.BoDrvS0A OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvS2A.BoDrvS1A OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvS3A BoDrvTA BoDrvTAcertA BoDrvTAcertNB BoDrvTAcertEB BoDrvZcertsA OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvNodesSoundA5.BoDrvNodesSoundA3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvS0SoundA.BoDrvNodesAllA OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvS0SoundA.BoDrvUinvA OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvS0SoundA.BoDrvCertSoundA OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvS0SoundA OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvCertSoundZ.BoDrvS0SpecA OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvCertSoundZ OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvNodesSoundA5.BoDrvGlueLibA OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvGlueA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import APS. Import GPS.
Open Scope Z_scope.
#[local] Notation RZ := (realizes BSEGS).

(* [comment removed for export] *)
Lemma zl_zero_lines : forall k, map (Z_to_bv 8) (zl k) = zero_lines k.
Proof. induction k as [|k IH]; [reflexivity|]. cbn [zl map zero_lines]. rewrite IH. reflexivity. Qed.

Lemma sd_s_calls : forall HOLES D E fs n, (1 <= n)%nat -> t_eq (GPS.sd HOLES D E fs (s_calls n)) (t_success n fs).
Proof.
  intros HOLES D E fs n Hn. unfold s_calls. destruct n as [|n]; [lia|]. cbn [GPS.sd].
  eapply t_eq_trans; [| apply t_eq_sym; apply t_success_S].
  unfold GPS.Wp, Spec4.W. apply Spec4.AgentLib.t_emit_congr.
  destruct n as [|n].
  - cbn [flat_map zero_lines map]. apply t_eq_refl.
  - cbn [flat_map GPS.piece_den]. rewrite app_nil_r. replace (Datatypes.S (Datatypes.S n) - 1)%nat with (Datatypes.S n) by lia.
    rewrite zl_zero_lines. apply t_eq_refl.
Qed.
(* [comment removed for export] *)
Lemma sd_shapeL : forall HOLES D E fs n, uE E CALLSB = Z.of_nat n -> (1 <= n <= 4)%nat -> t_eq (GPS.sd HOLES D E fs (shapeL CALLSB)) (t_success n fs).
Proof.
  intros HOLES D E fs n Hc Hn. eapply t_eq_trans; [|exact (sd_s_calls HOLES D E fs n (proj1 Hn))].
  unfold uE in Hc. unfold shapeL. cbn [GPS.sd]. rewrite Hc.
  assert (Hcases : n = 1%nat \/ n = 2%nat \/ n = 3%nat \/ n = 4%nat) by lia.
  destruct Hcases as [-> | [-> | [-> | ->]]]; cbn -[zl GPS.Wp]; apply t_eq_refl.
Qed.
Lemma gplanE : forall e, gplan_ok (planE e) = true. Proof. exact planE_ok. Qed.
Lemma gplanN : forall e, gplan_ok (planN e) = true. Proof. exact planN_ok. Qed.
Lemma gplanEL : forall e, gplan_ok (planEL e) = true. Proof. exact planEL_ok. Qed.
Lemma gplanNL : forall e, gplan_ok (planNL e) = true. Proof. exact planNL_ok. Qed.

Section TSpecA.
Context {RC : run_ceil}.
Context {SFL : stk_floor}.
Variable I : dinst.
Variables (a0 p : list byte) (fs : Fs.Fs) (data : list byte).
Hypothesis FHY : file_hyps I a0 p fs data.
#[local] Notation UX := (UXc data).
#[local] Notation cs1x := (cs1 I a0 p fs data UX).          (* [comment removed for export] *)
#[local] Notation csAx := (csA I a0 p fs data UX).          (* [comment removed for export] *)
#[local] Notation CM := (hdr_count_mode data).
#[local] Notation CALLS := (hdr_calls data).
#[local] Notation LD := (Z.of_nat (length data)).

Definition D0t (E : env) (fs' : Fs.Fs) : TSet := t_nil.
#[local] Notation RUN0 := (run_a I a0 p fs data FHY UX (UXc_a data) D0t (fun _ _ _ _ => eq_refl) (fun _ _ => eq_refl) HS0).
Lemma no_holes : forall h ch, HS0 h = Some ch -> forall E fx R M model, csAx E ch fx R M model -> RZ (cfgF BSEGS fx R (pc ch) M model) (D0t E fs).
Proof. intros h ch Hh. discriminate Hh. Qed.

Lemma blob3g : forall AINVH E cs fx R M model, csG I a0 p fs data AINVH UX E cs fx R M model -> eb E 3%nat = APS.chunk 0 data.
Proof. intros AINVH E cs fx R M model HC. destruct (co_uinv HC) as [HU [HX _]]. exact (blob3 a0 p fs data E HU HX). Qed.

(* [comment removed for export] *)
Lemma payx_val : forall E len cfg, uE E (EVar 3) = len -> uE E CFGX = cfg -> 0 <= cfg < 32768 -> uE E PAYX = (len - cfg - 6) mod 2 ^ 64.
Proof.
  intros E len cfg HL HCf Hc. unfold PAYX, LEN. rewrite uE_esub, uE_eadd, uE_lit, HL, HCf by lia.
  rewrite (Z.mod_small (cfg + 6)) by lia. f_equal. lia.
Qed.

(* [comment removed for export] *)
Definition fP1 : kentry := KRange PAYX 1 67108864.
Lemma pay_shape : (reg tinPA 10, a_meter tinPA, a_fake tinPA, DNA.has_fact (kn tinPA) fP1, reg tinPB 10, a_meter tinPB, a_fake tinPB, DNA.has_fact (kn tinPB) fP1)
                  = (PAYX, EVar 5, [], true, PAYX, EVar 5, [], true).
Proof. vmc. Qed.
Lemma pay_premises : forall E cs fx R M model, cs1x E cs fx R M model -> reg cs 10 = PAYX -> a_meter cs = EVar 5 -> DNA.has_fact (kn cs) fP1 = true ->
  1 <= uE E (reg cs 10) /\ (uE E (a_meter cs) <= EVT \/ 8193 <= uE E (reg cs 10)).
Proof.
  intros E cs fx R M model HC Hr Hm HF. rewrite Hr, Hm.
  pose proof (has_fact_sound E _ (kn cs) fP1 (co_know HC) HF) as [K1 K2]. cbn [kentry_ok fP1] in K1, K2.
  change (bv_unsigned (edenot E PAYX)) with (uE E PAYX) in K1, K2.
  split; [exact K1|].
  destruct (co_uinv HC) as [HU (HX & HL & HK)]. pose proof (blob3 a0 p fs data E HU HX) as HB.
  destruct (Z_lt_ge_dec LD 65536) as [Hs | Hb]; [left; exact (HK Hs) | right].
  pose proof (hdr_cfglen_range data) as Rc.
  rewrite (payx_val E LD (hdr_cfglen data) HL (cfgx_hdr data E HB) Rc) in K1, K2 |- *.
  assert (LD < 2 ^ 64) by (rewrite <- HL; unfold uE; pose proof (u64_range (edenot E (EVar 3))); lia).
  rewrite Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)
Theorem T_EA : forall E fx R M model, cs1x E tinEA fx R M model -> RZ (cfgF BSEGS fx R (pc tinEA) M model) (t_success 1 fs).
Proof.
  intros E fx R M model HC1. pose proof (fh_W1 I a0 p fs data FHY UX E tinEA fx R M model HC1) as HC.
  eapply RZ_conseq_rz; [exact (RUN0 (planE CALLSA) tinEA shapeA (gplanE _) certEA no_holes E fx R M model HC)|].
  exact (sd_s_calls _ _ E fs 1%nat ltac:(lia)).
Qed.
Theorem T_NA : forall E fx R M model, csAx E tinNA fx R M model -> RZ (cfgF BSEGS fx R (pc tinNA) M model) (t_success 1 fs).
Proof.
  intros E fx R M model HC. eapply RZ_conseq_rz; [exact (RUN0 (planN CALLSA) tinNA shapeA (gplanN _) certNA no_holes E fx R M model HC)|].
  exact (sd_s_calls _ _ E fs 1%nat ltac:(lia)).
Qed.
Theorem T_PA : forall E fx R M model, cs1x E tinPA fx R M model ->
  RZ (cfgF BSEGS fx R (pc tinPA) M model) (t_success 1 fs).
Proof.
  intros E fx R M model HC. pose proof pay_shape as PS.
  destruct (pay_premises E tinPA fx R M model HC ltac:(exact (f_equal (fun x => fst (fst (fst (fst (fst (fst (fst x))))))) PS))
              ltac:(exact (f_equal (fun x => snd (fst (fst (fst (fst (fst (fst x))))))) PS)) ltac:(exact (f_equal (fun x => snd (fst (fst (fst (fst x))))) PS))) as [Hn Hk].
  apply (m1gp I a0 p fs data FHY UX (UXc_a data) tinPA tin0A tinNA _ M12_tinPA ltac:(exact (f_equal (fun x => snd (fst (fst (fst (fst (fst x)))))) PS))
           (t_success_has_nil _ _) T_NA E fx R M model HC Hn Hk).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fCFGB : kentry := KRange CFGX 1 32767.
Lemma facts_EB : DNA.has_fact (kn tinEB) fCFGB = true. Proof. vmc. Qed.
Lemma facts_NB : DNA.has_fact (kn tinNB) fCFGB = true. Proof. vmc. Qed.

Lemma calls_of : forall AINVH E cs fx R M model, csG I a0 p fs data AINVH UX E cs fx R M model -> DNA.has_fact (kn cs) fCFGB = true ->
  uE E CALLSB = Z.of_nat CALLS /\ (1 <= CALLS <= 4)%nat.
Proof.
  intros AINVH E cs fx R M model HC HF. pose proof (has_fact_sound E _ (kn cs) fCFGB (co_know HC) HF) as [H1 _]. cbn [kentry_ok] in H1.
  pose proof (blob3g AINVH E cs fx R M model HC) as HB. change (bv_unsigned (edenot E CFGX)) with (uE E CFGX) in H1. rewrite (cfgx_hdr data E HB) in H1.
  split; [apply (callsb_hdr data E HB); lia | apply hdr_calls_range].
Qed.


Theorem T_EB : forall E fx R M model, cs1x E tinEB fx R M model -> RZ (cfgF BSEGS fx R (pc tinEB) M model) (t_success CALLS fs).
Proof.
  intros E fx R M model HC1. pose proof (fh_W1 I a0 p fs data FHY UX E tinEB fx R M model HC1) as HC. destruct (calls_of _ E tinEB fx R M model HC facts_EB) as [Hc Hr].
  eapply RZ_conseq_rz; [exact (RUN0 (planEL CALLSB) tinEB (shapeL CALLSB) (gplanEL _) certEBL no_holes E fx R M model HC)|].
  exact (sd_shapeL _ _ E fs CALLS Hc Hr).
Qed.
Theorem T_NB : forall E fx R M model, csAx E tinNB fx R M model -> RZ (cfgF BSEGS fx R (pc tinNB) M model) (t_success CALLS fs).
Proof.
  intros E fx R M model HC. destruct (calls_of _ E tinNB fx R M model HC facts_NB) as [Hc Hr].
  eapply RZ_conseq_rz; [exact (RUN0 (planNL CALLSB) tinNB (shapeL CALLSB) (gplanNL _) certNBL no_holes E fx R M model HC)|].
  exact (sd_shapeL _ _ E fs CALLS Hc Hr).
Qed.
Theorem T_PB : forall E fx R M model, cs1x E tinPB fx R M model ->
  RZ (cfgF BSEGS fx R (pc tinPB) M model) (t_success CALLS fs).
Proof.
  intros E fx R M model HC. pose proof pay_shape as PS.
  destruct (pay_premises E tinPB fx R M model HC ltac:(exact (f_equal (fun x => snd (fst (fst (fst x)))) PS))
              ltac:(exact (f_equal (fun x => snd (fst (fst x))) PS)) ltac:(exact (f_equal snd PS))) as [Hn Hk].
  apply (m1gp I a0 p fs data FHY UX (UXc_a data) tinPB tin0B tinNB _ M12_tinPB ltac:(exact (f_equal (fun x => snd (fst x)) PS))
           (t_success_has_nil _ _) T_NB E fx R M model HC Hn Hk).
Qed.
End TSpecA.
