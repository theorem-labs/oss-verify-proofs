(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.coturn.FuzzStunClient.images Require Import Plain.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Amb.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SymExec2 SymExec2Sound SymRun SymDrive SymDriveX.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import RefMemcpyLib.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import RefMainEntry LibStdioCall RefPilotOOM_defs.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SymXfer.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFast.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastK.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastS.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastM.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SumWalkFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.gres ::= gres_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.vnorm ::= vnorm_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StepTac.step_simpl ::= step_simpl_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.RefMemcpyLib.not_kept ::= not_kept_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StartupTac.in_list ::= in_list_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StartupTac.peel ::= peel_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StoreOk.store_ok_peel ::= store_ok_peel_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.SumWalkTac.rdn_peel1 ::= rdn_peel1_fast.
(* [comment removed for export] *)
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations. Import SX2. Import SX2S.

(* [comment removed for export] *)
Definition STOPS_W : list Z := 0x1c614%Z :: STOPS.
Definition runW (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS_W scr ss [].

Definition bx : expr := EVar 70.

(* [comment removed for export] *)
Definition sc_of (o : option stdio_res) : stdio_res :=
  match o with Some r => r | None => SCR_ 0 0 0 (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) [] [] end.

(* [comment removed for export] *)
Definition knW0 : list kentry := Eval vm_compute in
  (KZero (SA bx 0) (ELit 4096) :: KZero (SA bx 4096) (ELit 4096)
   :: KWr (SA bx 0) 4096 :: KWr (SA bx 4096) 4096
   :: kn_xfer knD2 bx 0 8192 true).
Definition srW0 : list expr := Eval vm_compute in sr_upd srD2 (ridx 10) (EAlu ALU_ADD bx (ELit 8192)).
Definition rW1 := Eval vm_compute in run scr0 (SS 0x1c5f4 srW0 [] knW0 71).
Definition srW1 : list expr := Eval vm_compute in s_regs (fst (fst rW1)).
Definition knW1 : list kentry := Eval vm_compute in kn_after rW1 knW0.

(* [comment removed for export] *)
Definition ENOMEMv : expr := ELit (2 ^ 64 - 12).
Definition srK0 := Eval vm_compute in sr_upd srW1 (ridx 10) ENOMEMv.
Definition rK := Eval vm_compute in runW scr0 (SS 0x1d704 srK0 [] knW1 71).
Definition srK1 : list expr := Eval vm_compute in s_regs (fst (fst rK)).
Definition knK1 : list kentry := Eval vm_compute in kn_after rK knW1.

Definition knU : list kentry := Eval vm_compute in kn_xfer knW1 bx 0 4096 false.
Definition srO0 := Eval vm_compute in sr_upd srW1 (ridx 10) bx.
Definition rO := Eval vm_compute in runW scr0 (SS 0x1d704 srO0 [] knU 71).
Definition srO1 : list expr := Eval vm_compute in s_regs (fst (fst rO)).
Definition knO1 : list kentry := Eval vm_compute in kn_after rO knU.

Definition rDd := Eval vm_compute in runW scr0 (SS 0x1d704 srK0 [] knU 71).
Definition srDd1 : list expr := Eval vm_compute in s_regs (fst (fst rDd)).
Definition knDd1 : list kentry := Eval vm_compute in kn_after rDd knU.


(* [comment removed for export] *)
Definition kn_inter3 (k1 k2 k3 : list kentry) : list kentry :=
  List.filter (fun K => existsb (kentry_eqb K) k2 && existsb (kentry_eqb K) k3) k1.
Definition srM : list expr := Eval vm_compute in sr_upd srO1 (ridx 10) (EVar 71).
Definition knM : list kentry := Eval vm_compute in kn_inter3 knO1 knK1 knDd1.

(* [comment removed for export] *)
Definition rW2 := Eval vm_compute in run scr0 (SS 0x1c614 srM [] knM 72).
Definition srW2 : list expr := Eval vm_compute in s_regs (fst (fst rW2)).
Definition knW2 : list kentry := Eval vm_compute in kn_after rW2 knM.


(* [comment removed for export] *)
Definition srN0 : list expr := Eval vm_compute in sr_upd srW2 (ridx 10) ENOMEMv.
Definition rN := Eval vm_compute in run scr0 (SS 0x1d704 srN0 [] knW2 72).
Definition srN : list expr := Eval vm_compute in s_regs (fst (fst rN)).
Definition knN : list kentry := Eval vm_compute in kn_after rN knW2.
(* [comment removed for export] *)
Definition resX : stdio_res := Eval vm_compute in sc_of (stdio_call 72 srN knN).
Lemma resX_eq : stdio_call 72 srN knN = Some resX.  Proof. vm_compute. reflexivity. Qed.
Definition srX0 : list expr := Eval vm_compute in sc_sr resX.
Definition knX0 : list kentry := Eval vm_compute in sc_kn resX.
Definition rX := Eval vm_compute in run scr0 (SS 0x1e330 srX0 [] knX0 104).
Definition srX : list expr := Eval vm_compute in s_regs (fst (fst rX)).
Definition knX : list kentry := Eval vm_compute in kn_after rX knX0.

(* [comment removed for export] *)
Definition gx : expr := EVar 72.
(* [comment removed for export] *)
Definition knG00 : list kentry :=
  KAlign gx 4096 :: KRange gx 0x58000 (0x800000000000 - 8388608 - 69632) :: KDisj (SA bx 4096) 4096 (SA gx 0) 69632
  :: KDisj (SA (EVar 0) (-8388608)) 2155872256 (SA gx 0) 69632   (* [comment removed for export] *)
  :: knW2.
Definition knG0 : list kentry := Eval vm_compute in
  (KZero (SA gx 0) (ELit 69632) :: KWr (SA gx 0) 69632 :: kn_xfer knG00 gx 0 69632 true).
Definition srG0 : list expr := Eval vm_compute in sr_upd srW2 (ridx 10) gx.
Definition scrG : scripts := SCR [true] [] [].   (* [comment removed for export] *)
Definition rG := Eval vm_compute in run scrG (SS 0x1d704 srG0 [] knG0 73).
Definition srG : list expr := Eval vm_compute in s_regs (fst (fst rG)).
Definition knG : list kentry := Eval vm_compute in kn_after rG knG0.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ax : expr := EVar 71.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition knP00 : list kentry :=
  KAlign ax 4096 :: KRange ax 0x1000 (0x800000000000 - 8388608 - 8192)
  :: KDisj (SA (ELit 0) 0x10000) 0x48000 (SA ax 0) 8192
  :: KDisj (SA (EVar 0) (-8388608)) 2155872256 (SA ax 0) 8192   (* [comment removed for export] *)
  :: knE.
Definition knP0 : list kentry := Eval vm_compute in kn_xfer knP00 ax 0 8192 false.
Definition srP0 : list expr := Eval vm_compute in sr_upd srE (ridx 10) ax.
Definition scrP : scripts := SCR [true] [] [].   (* [comment removed for export] *)
Definition rP := Eval vm_compute in run scrP (SS 0x1d704 srP0 [] knP0 72).
Definition srP : list expr := Eval vm_compute in s_regs (fst (fst rP)).
Definition knP : list kentry := Eval vm_compute in kn_after rP knP0.

(* [comment removed for export] *)
Definition srQ0 : list expr := Eval vm_compute in sr_upd srP (ridx 10) ENOMEMv.
Definition rQ := Eval vm_compute in run scr0 (SS 0x1d75c srQ0 [] knP 72).
Definition srQ : list expr := Eval vm_compute in s_regs (fst (fst rQ)).
Definition knQ : list kentry := Eval vm_compute in kn_after rQ knP.
Definition resQX : stdio_res := Eval vm_compute in sc_of (stdio_call 72 srQ knQ).
Lemma resQX_eq : stdio_call 72 srQ knQ = Some resQX.  Proof. vm_compute. reflexivity. Qed.
Definition srQX0 : list expr := Eval vm_compute in sc_sr resQX.
Definition knQX0 : list kentry := Eval vm_compute in sc_kn resQX.
Definition rQX := Eval vm_compute in run scr0 (SS 0x1e330 srQX0 [] knQX0 104).
Definition srQX : list expr := Eval vm_compute in s_regs (fst (fst rQX)).
Definition knQX : list kentry := Eval vm_compute in kn_after rQX knQX0.

(* [comment removed for export] *)
Definition knR0 : list kentry := Eval vm_compute in
  (KZero (SA ax 4096) (ELit 4096) :: KWr (SA ax 4096) 4096 :: kn_xfer knP ax 4096 4096 true).
Definition srR0 : list expr := Eval vm_compute in sr_upd srP (ridx 10) (ELit 0).
Definition rR := Eval vm_compute in run scr0 (SS 0x1d75c srR0 [] knR0 72).
Definition srR : list expr := Eval vm_compute in s_regs (fst (fst rR)).
Definition knR : list kentry := Eval vm_compute in kn_after rR knR0.

(* [comment removed for export] *)
Definition srS0 : list expr := Eval vm_compute in sr_upd srR (ridx 10) ENOMEMv.
Definition rS := Eval vm_compute in run scr0 (SS 0x1d704 srS0 [] knR 72).
Definition srS : list expr := Eval vm_compute in s_regs (fst (fst rS)).
Definition knS : list kentry := Eval vm_compute in kn_after rS knR.
Definition resSX : stdio_res := Eval vm_compute in sc_of (stdio_call 72 srS knS).
Lemma resSX_eq : stdio_call 72 srS knS = Some resSX.  Proof. vm_compute. reflexivity. Qed.
Definition srSX0 : list expr := Eval vm_compute in sc_sr resSX.
Definition knSX0 : list kentry := Eval vm_compute in sc_kn resSX.
Definition rSX := Eval vm_compute in run scr0 (SS 0x1e330 srSX0 [] knSX0 104).
Definition srSX : list expr := Eval vm_compute in s_regs (fst (fst rSX)).
Definition knSX : list kentry := Eval vm_compute in kn_after rSX knSX0.

(* [comment removed for export] *)
Definition knT00 : list kentry :=
  KAlign gx 4096 :: KRange gx 0x58000 (0x800000000000 - 8388608 - 69632) :: KDisj (SA ax 0) 8192 (SA gx 0) 69632
  :: KDisj (SA (EVar 0) (-8388608)) 2155872256 (SA gx 0) 69632   (* [comment removed for export] *)
  :: knR.
Definition knT0 : list kentry := Eval vm_compute in
  (KZero (SA gx 0) (ELit 69632) :: KWr (SA gx 0) 69632 :: kn_xfer knT00 gx 0 69632 true).
Definition srT0 : list expr := Eval vm_compute in sr_upd srR (ridx 10) gx.
Definition rT := Eval vm_compute in run scrG (SS 0x1d704 srT0 [] knT0 73).
Definition srT : list expr := Eval vm_compute in s_regs (fst (fst rT)).
Definition knT : list kentry := Eval vm_compute in kn_after rT knT0.


(* [comment removed for export] *)
Definition LOGE : list sentry :=
  [SE (SA gx 29) 1 (ELit 160); SE (SA gx 69624) 4 (ELit 4060); SE (SA gx 69623) 1 (ELit 0);
   SE (SA gx 65568) 1 (ELit 0); SE (SA gx 30) 2 (ELit 1); SE (SA gx 29) 1 (ELit 0);
   SE (SA gx 28) 1 (ELit 0); SE (SA gx 14) 2 (ELit 1); SE (SA gx 13) 1 (ELit 224)].
(* [comment removed for export] *)
Definition knZ : list kentry := Eval vm_compute in fst (fst (carry LOGE knG [])).
Definition srZ : list expr := Eval vm_compute in
  sr_upd (sr_after_call_j srG (map ridx callee_saved) 73) (ridx 10) (EAlu ALU_ADD gx (ELit 32)).
Definition knZm : list kentry := Eval vm_compute in fst (fst (carry LOGE knT [])).
Definition srZm : list expr := Eval vm_compute in
  sr_upd (sr_after_call_j srT (map ridx callee_saved) 73) (ridx 10) (EAlu ALU_ADD gx (ELit 32)).

(* [comment removed for export] *)
Lemma itinerary_w65 :
  (s_pc (fst (fst rW1)), snd (fst rW1)) = (0x1d700%Z, [])
  /\ (s_pc (fst (fst rK)), snd (fst rK)) = (0x1c614%Z, [])
  /\ (s_pc (fst (fst rO)), snd (fst rO)) = (0x1c614%Z, [])
  /\ (s_pc (fst (fst rDd)), snd (fst rDd)) = (0x1c614%Z, [])
  /\ (s_pc (fst (fst rW2)), snd (fst rW2)) = (0x1d700%Z, [])
  /\ (s_pc (fst (fst rN)), snd (fst rN)) = (0x1df28%Z, [])
  /\ (sc_ret resX, sc_f resX, sc_fd resX) = (0x1e330%Z, 0x26368%Z, 2%Z)
  /\ (s_pc (fst (fst rX)), snd (fst rX)) = (0x1baf8%Z, [])
  /\ (s_pc (fst (fst rG)), snd (fst rG)) = (0x1d374%Z, [SCBr true BC_NE (EAlu ALU_XOR gx (ELit (-1))) (ELit 0)])
  /\ (s_pc (fst (fst rP)), snd (fst rP)) = (0x1d758%Z, [SCBr true BC_NE (EAlu ALU_XOR ax (ELit (-1))) (ELit 0)])
  /\ (s_pc (fst (fst rQ)), snd (fst rQ)) = (0x1df28%Z, [])
  /\ (sc_ret resQX, sc_f resQX, sc_fd resQX) = (0x1e330%Z, 0x26368%Z, 2%Z)
  /\ (s_pc (fst (fst rQX)), snd (fst rQX)) = (0x1baf8%Z, [])
  /\ (s_pc (fst (fst rR)), snd (fst rR)) = (0x1d700%Z, [])
  /\ (s_pc (fst (fst rS)), snd (fst rS)) = (0x1df28%Z, [])
  /\ (sc_ret resSX, sc_f resSX, sc_fd resSX) = (0x1e330%Z, 0x26368%Z, 2%Z)
  /\ (s_pc (fst (fst rSX)), snd (fst rSX)) = (0x1baf8%Z, [])
  /\ (s_pc (fst (fst rT)), snd (fst rT)) = (0x1d374%Z, [SCBr true BC_NE (EAlu ALU_XOR gx (ELit (-1))) (ELit 0)]).
Proof. first [ wf_conj_vm | vm_compute; repeat split; reflexivity ]. Qed.

Lemma carry_LOGE_ok : snd (fst (carry LOGE knG [])) = [] /\ snd (fst (carry LOGE knT [])) = [].
Proof. vm_compute. split; reflexivity. Qed.
