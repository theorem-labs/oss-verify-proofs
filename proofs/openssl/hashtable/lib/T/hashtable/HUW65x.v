(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import ModelAmb.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require LedgerCfg.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import H0Lim.   (* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Prelude Instr.
From OssFuzzTheorems.openssl.hashtable.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require PropExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX RefMemcpyLib HUMainEntryDefs HULibStdioCall HUPilotOOM_defs.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require SymXfer.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg ShapeLaws Nodes MmapSim AllocSim FileSim AgentLib SpecConsts SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame HULibStdioCall Spec LibWritev RefNodes HUExitBase HUStdioDefs HUExit RefMemcpyLib HUMainEntryDefs Hoare Frame MallocDefs HUEnframeBase HUEnframe HUReadBase.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require HUPilotOOM_defs HUPilotOOM.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require SymXfer SymAbove SymAboveV ExistsRun RefNodesEx PhaseG RefNodesG.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg ShapeLaws Nodes MmapSim AllocSim FileSim AgentLib SpecConsts SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame HULibStdioCall Spec LibWritev RefNodes HUExitBase HUStdioDefs HUExit RefMemcpyLib HUMainEntryDefs Hoare Frame MallocDefs RefEnframeArith HUEnframeBase HUEnframe HUReadBase.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg Nodes MmapSim AllocSim FileSim AgentLib SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX Spec LibWritev RefNodes HUExitBase HUExit RefMemcpyLib RefLayout HUMainEntryDefs Hoare Frame MallocDefs HUEnframeBase HUEnframe HUReadBase HUWorld HUTargetPre.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import ConeCfg.   (* [comment removed for export] *)

(* [comment removed for export] *)
Module H0W65_defs.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.PropExec OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SymExec2 OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SymExec2Sound OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SymRun OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SymDrive OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SymDriveX OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.RefMemcpyLib HUMainEntryDefs HULibStdioCall HUPilotOOM_defs.
Import OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SymXfer.
Import ConeCfg.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import ListNotations. Import SX2. Import SX2S.
Import ConeCfg.

(* [comment removed for export] *)
Definition STOPS_W : list Z := 0x2b2494%Z :: STOPS.
Definition runW (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS_W scr ss [].

Definition bx : expr := EVar 73.

(* [comment removed for export] *)
Definition sc_of (o : option stdio_res) : stdio_res :=
  match o with Some r => r | None => SCR_ 0 0 0 (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) [] [] end.

(* [comment removed for export] *)
Definition knW0 : list kentry := Eval vm_compute in
  (KZero (SA bx 0) (ELit 4096) :: KZero (SA bx 4096) (ELit 4096)
   :: KWr (SA bx 0) 4096 :: KWr (SA bx 4096) 4096
   :: kn_xfer knD2 bx 0 8192 true).
Definition srW0 : list expr := Eval vm_compute in sr_upd srD2 (ridx 10) (EAlu ALU_ADD bx (ELit 8192)).
Definition rW1 := Eval vm_compute in run scr0 (SS 0x2b2474 srW0 [] knW0 74).
Definition srW1 : list expr := Eval vm_compute in s_regs (fst (fst rW1)).
Definition knW1 : list kentry := Eval vm_compute in kn_after rW1 knW0.

(* [comment removed for export] *)
Definition ENOMEMv : expr := ELit (2 ^ 64 - 12).
Definition srK0 := Eval vm_compute in sr_upd srW1 (ridx 10) ENOMEMv.
Definition rK := Eval vm_compute in runW scr0 (SS 0x2b3e24 srK0 [] knW1 74).
Definition srK1 : list expr := Eval vm_compute in s_regs (fst (fst rK)).
Definition knK1 : list kentry := Eval vm_compute in kn_after rK knW1.

Definition knU : list kentry := Eval vm_compute in kn_xfer knW1 bx 0 4096 false.
Definition srO0 := Eval vm_compute in sr_upd srW1 (ridx 10) bx.
Definition rO := Eval vm_compute in runW scr0 (SS 0x2b3e24 srO0 [] knU 74).
Definition srO1 : list expr := Eval vm_compute in s_regs (fst (fst rO)).
Definition knO1 : list kentry := Eval vm_compute in kn_after rO knU.

Definition rDd := Eval vm_compute in runW scr0 (SS 0x2b3e24 srK0 [] knU 74).
Definition srDd1 : list expr := Eval vm_compute in s_regs (fst (fst rDd)).
Definition knDd1 : list kentry := Eval vm_compute in kn_after rDd knU.


(* [comment removed for export] *)
Definition kn_inter3 (k1 k2 k3 : list kentry) : list kentry :=
  List.filter (fun K => existsb (kentry_eqb K) k2 && existsb (kentry_eqb K) k3) k1.
Definition srM : list expr := Eval vm_compute in sr_upd srO1 (ridx 10) (EVar 74).
Definition knM : list kentry := Eval vm_compute in kn_inter3 knO1 knK1 knDd1.

(* [comment removed for export] *)
Definition rW2 := Eval vm_compute in run scr0 (SS 0x2b2494 srM [] knM 75).
Definition srW2 : list expr := Eval vm_compute in s_regs (fst (fst rW2)).
Definition knW2 : list kentry := Eval vm_compute in kn_after rW2 knM.


(* [comment removed for export] *)
Definition srN0 : list expr := Eval vm_compute in sr_upd srW2 (ridx 10) ENOMEMv.
Definition rN := Eval vm_compute in run scr0 (SS 0x2b3e24 srN0 [] knW2 75).
Definition srN : list expr := Eval vm_compute in s_regs (fst (fst rN)).
Definition knN : list kentry := Eval vm_compute in kn_after rN knW2.
(* [comment removed for export] *)
Definition resX : stdio_res := Eval vm_compute in sc_of (stdio_call 75 srN knN).
Lemma resX_eq : stdio_call 75 srN knN = Some resX.  Proof. vm_compute. reflexivity. Qed.
Definition srX0 : list expr := Eval vm_compute in sc_sr resX.
Definition knX0 : list kentry := Eval vm_compute in sc_kn resX.
Definition rX := Eval vm_compute in run scr0 (SS 0x2b5f50 srX0 [] knX0 107).
Definition srX : list expr := Eval vm_compute in s_regs (fst (fst rX)).
Definition knX : list kentry := Eval vm_compute in kn_after rX knX0.

(* [comment removed for export] *)
Definition gx : expr := EVar 75.
(* [comment removed for export] *)
Definition knG00 : list kentry :=
  KAlign gx 4096 :: KRange gx 0x354000 (0x7fffff800000 - 69632) :: KDisj (SA (EVar 0) (-8388608)) 8388608 (SA gx 0) 69632
  :: KDisj (SA bx 4096) 4096 (SA gx 0) 69632 :: knW2.
Definition knG0 : list kentry := Eval vm_compute in
  (KZero (SA gx 0) (ELit 69632) :: KWr (SA gx 0) 69632 :: kn_xfer knG00 gx 0 69632 true).
Definition srG0 : list expr := Eval vm_compute in sr_upd srW2 (ridx 10) gx.
Definition scrG : scripts := SCR [true] [] [].   (* [comment removed for export] *)
Definition rG := Eval vm_compute in run scrG (SS 0x2b3e24 srG0 [] knG0 76).
Definition srG : list expr := Eval vm_compute in s_regs (fst (fst rG)).
Definition knG : list kentry := Eval vm_compute in kn_after rG knG0.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ax : expr := EVar 74.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition knP00 : list kentry :=
  KAlign ax 4096 :: KRange ax 0x1000 (0x7fffff800000 - 8192) :: KDisj (SA (EVar 0) (-8388608)) 8388608 (SA ax 0) 8192
  :: KDisj (SA (ELit 0) 0x10000) 0x344000 (SA ax 0) 8192 :: knE.
Definition knP0 : list kentry := Eval vm_compute in kn_xfer knP00 ax 0 8192 false.
Definition srP0 : list expr := Eval vm_compute in sr_upd srE (ridx 10) ax.
Definition scrP : scripts := SCR [true] [] [].   (* [comment removed for export] *)
Definition rP := Eval vm_compute in run scrP (SS 0x2b3e24 srP0 [] knP0 75).
Definition srP : list expr := Eval vm_compute in s_regs (fst (fst rP)).
Definition knP : list kentry := Eval vm_compute in kn_after rP knP0.

(* [comment removed for export] *)
Definition srQ0 : list expr := Eval vm_compute in sr_upd srP (ridx 10) ENOMEMv.
Definition rQ := Eval vm_compute in run scr0 (SS 0x2b3e7c srQ0 [] knP 75).
Definition srQ : list expr := Eval vm_compute in s_regs (fst (fst rQ)).
Definition knQ : list kentry := Eval vm_compute in kn_after rQ knP.
Definition resQX : stdio_res := Eval vm_compute in sc_of (stdio_call 75 srQ knQ).
Lemma resQX_eq : stdio_call 75 srQ knQ = Some resQX.  Proof. vm_compute. reflexivity. Qed.
Definition srQX0 : list expr := Eval vm_compute in sc_sr resQX.
Definition knQX0 : list kentry := Eval vm_compute in sc_kn resQX.
Definition rQX := Eval vm_compute in run scr0 (SS 0x2b5f50 srQX0 [] knQX0 107).
Definition srQX : list expr := Eval vm_compute in s_regs (fst (fst rQX)).
Definition knQX : list kentry := Eval vm_compute in kn_after rQX knQX0.

(* [comment removed for export] *)
Definition knR0 : list kentry := Eval vm_compute in
  (KZero (SA ax 4096) (ELit 4096) :: KWr (SA ax 4096) 4096 :: kn_xfer knP ax 4096 4096 true).
Definition srR0 : list expr := Eval vm_compute in sr_upd srP (ridx 10) (ELit 0).
Definition rR := Eval vm_compute in run scr0 (SS 0x2b3e7c srR0 [] knR0 75).
Definition srR : list expr := Eval vm_compute in s_regs (fst (fst rR)).
Definition knR : list kentry := Eval vm_compute in kn_after rR knR0.

(* [comment removed for export] *)
Definition srS0 : list expr := Eval vm_compute in sr_upd srR (ridx 10) ENOMEMv.
Definition rS := Eval vm_compute in run scr0 (SS 0x2b3e24 srS0 [] knR 75).
Definition srS : list expr := Eval vm_compute in s_regs (fst (fst rS)).
Definition knS : list kentry := Eval vm_compute in kn_after rS knR.
Definition resSX : stdio_res := Eval vm_compute in sc_of (stdio_call 75 srS knS).
Lemma resSX_eq : stdio_call 75 srS knS = Some resSX.  Proof. vm_compute. reflexivity. Qed.
Definition srSX0 : list expr := Eval vm_compute in sc_sr resSX.
Definition knSX0 : list kentry := Eval vm_compute in sc_kn resSX.
Definition rSX := Eval vm_compute in run scr0 (SS 0x2b5f50 srSX0 [] knSX0 107).
Definition srSX : list expr := Eval vm_compute in s_regs (fst (fst rSX)).
Definition knSX : list kentry := Eval vm_compute in kn_after rSX knSX0.

(* [comment removed for export] *)
Definition knT00 : list kentry :=
  KAlign gx 4096 :: KRange gx 0x354000 (0x7fffff800000 - 69632) :: KDisj (SA (EVar 0) (-8388608)) 8388608 (SA gx 0) 69632
  :: KDisj (SA ax 0) 8192 (SA gx 0) 69632 :: knR.
Definition knT0 : list kentry := Eval vm_compute in
  (KZero (SA gx 0) (ELit 69632) :: KWr (SA gx 0) 69632 :: kn_xfer knT00 gx 0 69632 true).
Definition srT0 : list expr := Eval vm_compute in sr_upd srR (ridx 10) gx.
Definition rT := Eval vm_compute in run scrG (SS 0x2b3e24 srT0 [] knT0 76).
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
  sr_upd (sr_after_call_j srG (map ridx callee_saved) 76) (ridx 10) (EAlu ALU_ADD gx (ELit 32)).
Definition knZm : list kentry := Eval vm_compute in fst (fst (carry LOGE knT [])).
Definition srZm : list expr := Eval vm_compute in
  sr_upd (sr_after_call_j srT (map ridx callee_saved) 76) (ridx 10) (EAlu ALU_ADD gx (ELit 32)).

(* [comment removed for export] *)
Lemma itinerary_w65 :
  (s_pc (fst (fst rW1)), snd (fst rW1)) = (0x2b3e20%Z, [])
  /\ (s_pc (fst (fst rK)), snd (fst rK)) = (0x2b2494%Z, [])
  /\ (s_pc (fst (fst rO)), snd (fst rO)) = (0x2b2494%Z, [])
  /\ (s_pc (fst (fst rDd)), snd (fst rDd)) = (0x2b2494%Z, [])
  /\ (s_pc (fst (fst rW2)), snd (fst rW2)) = (0x2b3e20%Z, [])
  /\ (s_pc (fst (fst rN)), snd (fst rN)) = (0x2b55ac%Z, [])
  /\ (sc_ret resX, sc_f resX, sc_fd resX) = (0x2b5f50%Z, 0x31ebd0%Z, 2%Z)
  /\ (s_pc (fst (fst rX)), snd (fst rX)) = (0x2b17ec%Z, [])
  /\ (s_pc (fst (fst rG)), snd (fst rG)) = (0x2b31f4%Z, [SCBr true BC_NE (EAlu ALU_XOR gx (ELit (-1))) (ELit 0)])
  /\ (s_pc (fst (fst rP)), snd (fst rP)) = (0x2b3e78%Z, [SCBr true BC_NE (EAlu ALU_XOR ax (ELit (-1))) (ELit 0)])
  /\ (s_pc (fst (fst rQ)), snd (fst rQ)) = (0x2b55ac%Z, [])
  /\ (sc_ret resQX, sc_f resQX, sc_fd resQX) = (0x2b5f50%Z, 0x31ebd0%Z, 2%Z)
  /\ (s_pc (fst (fst rQX)), snd (fst rQX)) = (0x2b17ec%Z, [])
  /\ (s_pc (fst (fst rR)), snd (fst rR)) = (0x2b3e20%Z, [])
  /\ (s_pc (fst (fst rS)), snd (fst rS)) = (0x2b55ac%Z, [])
  /\ (sc_ret resSX, sc_f resSX, sc_fd resSX) = (0x2b5f50%Z, 0x31ebd0%Z, 2%Z)
  /\ (s_pc (fst (fst rSX)), snd (fst rSX)) = (0x2b17ec%Z, [])
  /\ (s_pc (fst (fst rT)), snd (fst rT)) = (0x2b31f4%Z, [SCBr true BC_NE (EAlu ALU_XOR gx (ELit (-1))) (ELit 0)]).
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma carry_LOGE_ok : snd (fst (carry LOGE knG [])) = [] /\ snd (fst (carry LOGE knT [])) = [].
Proof. vm_compute. split; reflexivity. Qed.
End H0W65_defs.

(* [comment removed for export] *)
Module H0W65.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.PropExec OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.CatExec OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.CatSim OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SeqExec OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.StoreOk OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SimInv OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.ExitSim OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.ShapeAlg ShapeLaws OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.Nodes OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.MmapSim OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.AllocSim OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.FileSim OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.AgentLib OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SpecConsts OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SymExec OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SymExec2 OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SymExec2Sound OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SymRun OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SymDrive OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SymDriveX OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.LibKnowFrame HULibStdioCall Spec OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.LibWritev OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.RefNodes HUExitBase HUStdioDefs HUExit OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.RefMemcpyLib HUMainEntryDefs OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.Hoare OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.Frame OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.MallocDefs HUEnframeBase HUEnframe HUReadBase.
Import HUPilotOOM_defs HUPilotOOM.
Import OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SymXfer OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SymAbove OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SymAboveV
       OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.ExistsRun OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.PhaseG OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.RefNodesG H0W65_defs.
Import ConeCfg.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import ListNotations.
Import ConeCfg.
Open Scope bv_scope.
Import SX2. Import SX2S.
Import ConeCfg.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Tactic Notation "run_block" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX false.
Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX true.
Tactic Notation "run_blockW" constr(scr) constr(NX) := run_block_gen FUEL STOPS_W scr NX false.
Tactic Notation "run_blockW_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPS_W scr NX true.
(* [comment removed for export] *)
Tactic Notation "gg_block" constr(scr) constr(NX) := gg_block_gen FUEL STOPS scr NX false.
Tactic Notation "gg_block_keep" constr(scr) constr(NX) := gg_block_gen FUEL STOPS scr NX true.
Tactic Notation "gg_blockW" constr(scr) constr(NX) := gg_block_gen FUEL STOPS_W scr NX false.
Tactic Notation "gg_blockW_keep" constr(scr) constr(NX) := gg_block_gen FUEL STOPS_W scr NX true.
(* [comment removed for export] *)
Tactic Notation "any_block_keep" constr(scr) constr(NX) :=
  lazymatch goal with
  | |- realizes _ _ _ => run_block_gen FUEL STOPS scr NX true
  | |- GG _ _ _ _ _ => gg_block_gen FUEL STOPS scr NX true
  end.
Tactic Notation "any_blockW_keep" constr(scr) constr(NX) :=
  lazymatch goal with
  | |- realizes _ _ _ => run_block_gen FUEL STOPS_W scr NX true
  | |- GG _ _ _ _ _ => gg_block_gen FUEL STOPS_W scr NX true
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma bt_ne_not : forall (x : word), (bv_unsigned x < 2 ^ 64 - 1)%Z ->
  branch_taken BC_NE (alu64 ALU_XOR x (Z_to_bv 64 (-1))) (Z_to_bv 64 0) = true.
Proof.
  intros x Hx. cbn [branch_taken]. apply Bool.negb_true_iff. unfold bv_eqb. apply Z.eqb_neq.
  change (alu64 ALU_XOR x (Z_to_bv 64 (-1))) with (bv_xor x (Z_to_bv 64 (-1))).
  pose proof (u64_range x).
  rewrite bv_xor_unsigned. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  change ((-1) mod 2 ^ 64)%Z with (2 ^ 64 - 1)%Z. change (0 mod 2 ^ 64)%Z with 0%Z.
  intros E. apply Z.lxor_eq in E. lia.
Qed.

(* [comment removed for export] *)
Lemma regs_ok_set_have : forall E sr R (rd : reg) v e,
  regs_ok E sr R -> getr R rd = v -> edenot E e = v -> rd <> 0%bv ->
  regs_ok E (sr_upd sr (ridx rd) e) R.
Proof.
  intros E sr R rd v e HR Hv He Hrd r.
  pose proof (regs_ok_set E sr R rd v e HR Hrd He r) as H.
  rewrite <- H. destruct (decide (r = rd)) as [->|Hne].
  - rewrite getr_same by exact Hrd. exact Hv.
  - rewrite getr_other by exact Hne. reflexivity.
Qed.

Lemma callee_saved_no0 : ~ In (0%bv : reg) callee_saved.
Proof.
  unfold callee_saved. intros Hin.
  repeat (destruct Hin as [Hin|Hin]; [apply (f_equal bv_unsigned) in Hin; cbn in Hin; discriminate Hin|]).
  exact Hin.
Qed.

Definition is_kzero_cov (b : expr) (k n : Z) (K : kentry) : bool :=
  match K with
  | KZero (SA b' k') (ELit n') => expr_eqb b b' && Z.leb k' k && Z.leb (k + n) (k' + n')
  | _ => false
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac oom_exit_pre HL P0 MFS :=
  lazymatch goal with
  | HR : regs_ok ?E ?sr ?R, HK : know_ok _ _ ?M ?kn |- realizes _ (mkCfg _ ?model) _ =>
    apply (rz_conseq RSEGS _ (t_emit (W 1 []) (t_exit (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) (m_fs model))));
    [ | try rewrite MFS; apply exit_leaf_eq; lia ];
    apply ref_exit_Z;
    let Ktid := fresh "Ktid" in let Hst := fresh "Hst" in let Htc := fresh "Htc" in
    pose proof (know_nth RSEGS _ _ kn ltac:(let i := kidx kn (is_krange (EVar 5)) in exact i) _ HK eq_refl)
      as Ktid; cbn [kentry_ok edenot ev] in Ktid;
    lazymatch type of P0 with vals_ev _ 0 = ?sp0 =>
    exists (Z_to_bv 64 (bv_unsigned sp0 - 128)), (Z_to_bv 64 0x331ae8), (bv_unsigned (ev E 5)),
           (Z_to_bv 64 0x3521c0), (Z_to_bv 64 0);
    split; [|split; [first [reflexivity | assumption] | split; [first [reflexivity | assumption] |]]];
    [ constructor;
      [ regv HR (2 : reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev];
        rewrite P0; f_equal; lia
      | regv HR (4 : reg); reflexivity
      | regv HR (10 : reg); reflexivity
      | rewrite u_small by lia; lia
      | rewrite u_small by lia; lia
      | rewrite u_small by lia;
        pose proof (kwr_store_ok RSEGS E _ kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-272) 144) in exact i)
                      _ _ _ (-272) 144 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst;
        unfold adenot, v_addi in Hst; cbn [a_base a_off edenot ev] in Hst; rewrite P0 in Hst;
        replace (bv_unsigned sp0 - 128 - 144)%Z with (bv_unsigned sp0 + -272)%Z by lia; exact Hst
      | lit_u; lia
      | lit_u; lia
      | cbn [ev]; cbn [ev] in Ktid; lia
      | lit_u; change (3349224 - 168)%Z with 0x331a40%Z;
        krd HK 0x331a40%Z 4%nat Htc; rewrite Htc; cbn [ev];
        rewrite ext_val_zx_id by (change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z; cbn [ev] in Ktid; lia);
        rewrite Z_to_bv_bv_unsigned; reflexivity
      | krd_solve HK
      | krd_solve HK
      | krd_solve HK
      | krd_solve HK
      | krd_solve HK
      | krd_solve HK
      | krd_solve HK
      | repeat split; krd_solve HK
      | repeat split; krd_solve HK ]
    | left; split; [reflexivity|];
      exists (Z_to_bv 64 0), (Z_to_bv 64 0); repeat split; krd_solve HK ]
    end
  end.

Ltac oom_stdio_exit HL P0 RES_EQ FD2 MFS :=
  (* [comment removed for export] *)
  lazymatch goal with
  | HR : regs_ok ?E _ _, HK : know_ok _ _ _ _ |- _ =>
      let En := eval hnf in E in change E with En in HR; change E with En in HK end;
  lazymatch goal with
  | HR : regs_ok ?E ?sr ?R, HK : know_ok _ _ ?M ?kn |- realizes _ (mkCfg _ ?model) (t_die msg_oom ?fs) =>
    lazymatch type of HL with length ?vals = ?nv =>
    lazymatch type of P0 with vals_ev _ 0 = ?sp0 =>
    lazymatch type of RES_EQ with stdio_call _ _ _ = Some ?res =>
    lazymatch E with Env _ ?ebs =>
      unfold t_die, W;
      apply (stdio_call_sound vals ebs sr kn R M model res [] msg_oom
               (t_exit (exit_code 2) fs) HR HK (eq_trans (f_equal (fun n => stdio_call n sr kn) HL) RES_EQ));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn res];
      change (Z.of_nat (length msg_oom)) with 19%Z; change (Z.of_nat (@length byte [])) with 0%Z;
      [ cbn [edenot]; lia
      | cbn [edenot]; lit_u; lia
      | cbn [edenot]; lia
      | cbn [edenot]; lit_u; reflexivity
      | lia
      | left; rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev]; rewrite P0;
        rewrite (u_small (bv_unsigned _ + _)) by lia; lit_u; lia
      | left; rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev]; rewrite P0;
        rewrite (u_small (bv_unsigned _ + _)) by lia; lit_u; lia
      | cbn [edenot]; lit_u; lia
      | reflexivity
      | cbn [edenot]; change (length msg_oom) with 19%nat;
        rewrite (kimg_rdn RSEGS E _ kn ltac:(let i := kidx kn (is_kimg_cov 0x1950d 19) in exact i)
                   _ _ 0x1950d 19 HK eq_refl) by (cbn; lia);
        apply msg_oom_img
      | apply FD2
      | first [reflexivity | assumption]
      | first [reflexivity | assumption]
      | apply t_exit_has_nil
      | clear HR HK; try clear R M;
        let R2 := fresh "R" in let M2 := fresh "M" in
        intros R2 M2 HR HK;
        let srX := eval vm_compute in (sc_sr res) in change (sc_sr res) with srX in HR;
        let knX := eval vm_compute in (sc_kn res) in change (sc_kn res) with knX in HK;
        let ret := eval vm_compute in (sc_ret res) in change (sc_ret res) with ret;
        let vals2 := fresh "vals" in let HL2 := fresh "HL" in let Q0 := fresh "P0" in
        set (vals2 := vals ++ junk_vals R2) in *;
        assert (HL2 : length vals2 = (nv + 32)%nat) by (subst vals2; rewrite length_app, junk_vals_length, HL; reflexivity);
        cbn [Nat.add] in HL2;
        assert (Q0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0);
        clearbody vals2; clear HL P0;
        let NX := eval vm_compute in (nv + 32)%nat in
        run_block_gen FUEL STOPS scr0 NX false;
        oom_exit_pre HL2 Q0 MFS
      ] end end end end
  end.

Section World.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable uid : word.   (* [comment removed for export] *)
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Variable tid : word.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable brk : word.
  Variable mbase : word.
  Variable fs0 : Fs.
  Variable stdin0 : AmbIn.
  Variable fdata : list byte.
  Variable lim : Z.                              (* [comment removed for export] *)
  Hypothesis lim_ge : (LIM <= lim)%Z.
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  (* [comment removed for export] *)
  Hypothesis Hbrk : valid_brk RSEGS brk.
  Hypothesis Hfile : fs_lookup fs0 path = Some fdata.
  Hypothesis Hpne : path <> [].
  Hypothesis Hplen : (length path <= 4095)%nat.
  (* [comment removed for export] *)
  Variable mode : bool.
  Variable Q : config -> Prop.
  (* [comment removed for export] *)
  Ltac to_gg Hmode :=
    lazymatch goal with
    | |- realizes ?s ?c ?T =>
        let HG := fresh "HG" in
        enough (HG : GG s mode Q T c) by (rewrite Hmode in HG; exact HG)
    end.
  (* [comment removed for export] *)
  Variable fd3 : FdEntry.
  (* [comment removed for export] *)
  Variable SI : (word -> option byte) -> Prop.
  Hypothesis SI_step : forall M M' : word -> option byte,
    (forall a : word, (bv_unsigned sp0 <= bv_unsigned a)%Z -> M' a = M a) -> SI M -> SI M'.

  #[local] Notation ENVv := (ENV a0s path rdraw).
  (* [comment removed for export] *)
  #[local] Notation RES := (segments_reserved RSEGS).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition VB1 : list (nat * Z) := [(73%nat, 8192%Z)].
  Definition VB : list (nat * Z) := [(73%nat, 8192%Z); (75%nat, 69632%Z)].
  Ltac vb_side :=
    unfold VB1, VB, vb_ok; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd ev ENV]; pins;
    repeat match goal with g := _ : word |- _ => subst g end; lia.
  Ltac si_block HSI Rn Mn :=
    lazymatch goal with
    | EQM : ?M' = mem_denot ?E ?Mo ?log, HK : know_ok ?segs ?E ?M' ?kn, HR : regs_ok ?E _ ?R' |- _ =>
        let H := fresh "HSI" in
        assert (H : SI M');
        [ apply (SI_step Mo M'); [| exact HSI]; intros xa Hxa; rewrite EQM;
          first
          [ apply (mem_denot_above_vb E Mo VB1 log 0%nat 0x354000 xa);
            [ vb_side | vm_compute; reflexivity | cbn [ev ENV]; pins; lia | cbn [ev ENV]; pins; lia | lia ]
          | apply (mem_denot_above_vb E Mo VB log 0%nat 0x354000 xa);
            [ vb_side | vm_compute; reflexivity | cbn [ev ENV]; pins; lia | cbn [ev ENV]; pins; lia | lia ] ]
        | clear HSI EQM; try clear Mn; rename H into HSI; try rename M' into Mn; try clear Rn; try rename R' into Rn ]
    end.

  (* [comment removed for export] *)
  Ltac si_fill HSI :=
    lazymatch goal with
    | |- SI (zfill ?a ?n ?M) => apply (SI_step M); [| exact HSI]; intros xa Hxa; apply zfill_out; rewrite ?u64_lit by lia; lia
    | |- SI (unfill ?a ?n ?M) => apply (SI_step M); [| exact HSI]; intros xa Hxa; apply unfill_outside; rewrite ?u64_lit by lia; lia
    end.

  (* [comment removed for export] *)
  Definition fdsV : list (word * FdEntry) := fd_insert fds0 (Z_to_bv 64 3) fd3.
  Definition modelV (VM : VmMaps) : Model := mkModelA fdsV VM stdin0 fs0 None (Some tid) None.

  Lemma fdsV_2 : fd_lookup fdsV (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
  Proof. reflexivity. Qed.
  (* [comment removed for export] *)
  Lemma mV_vmmaps : forall VM, m_vmmaps (modelV VM) = VM.  Proof. reflexivity. Qed.
  Lemma mV_fs : forall VM, m_fs (modelV VM) = fs0.  Proof. reflexivity. Qed.
  Lemma mV_fds : forall VM, m_fds (modelV VM) = fdsV.  Proof. reflexivity. Qed.
  Lemma mV_fd2 : forall VM, fd_lookup (m_fds (modelV VM)) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
  Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition model1V : Model := mkModelA fdsV (mkVmMapsFull RES [] [] brk brk lim mbase sp0) stdin0 fs0 None (Some tid) None.

  (* [comment removed for export] *)
  Definition brk_ok_entry (KB : TSet) : Prop :=
    forall vals R M,
      length vals = 74%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 73 = brk ->
      vals_ev vals 1 = p0 sp0 a0s path envv -> vals_ev vals 2 = p1 sp0 a0s path envv ->
      vals_ev vals 5 = tid ->
      regs_ok (ENVv vals) srD2 R -> know_ok RSEGS (ENVv vals) M knD2 -> SI M ->
      GG RSEGS mode Q KB
        (mkCfg (mkst (regupd R 10 (Z_to_bv 64 (bv_unsigned brk + 8192))) (Z_to_bv 64 0x2b2474)
                     (zfill brk (Z_to_bv 64 8192) M) (seg_rom RSEGS))
               (mkModelA fdsV (mkVmMapsFull RES [(brk, Z_to_bv 64 8192)] [] brk
                                            (Z_to_bv 64 (bv_unsigned brk + 8192)) lim mbase sp0)
                        stdin0 fs0 None (Some tid) None)).

  Definition mmap_ok_entry (KB : TSet) : Prop :=
    forall vals R M (hint a : word),
      length vals = 74%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 73 = brk ->
      vals_ev vals 1 = p0 sp0 a0s path envv -> vals_ev vals 2 = p1 sp0 a0s path envv ->
      vals_ev vals 5 = tid ->
      regs_ok (ENVv vals) srE R -> know_ok RSEGS (ENVv vals) M knE -> SI M ->
      grant_ok_na hint model1V a 8192 = true ->
      realizes RSEGS (mkCfg (mkst (regupd R 10 a) (Z_to_bv 64 0x2b3e24)
                                    (unfill a (Z_to_bv 64 8192) M) (seg_rom RSEGS))
                              (noaccess_model a (Z_to_bv 64 8192) model1V)) KB.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma w65_oomN : forall vals R M VM,
    length vals = 75%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENVv vals) srN0 R -> know_ok RSEGS (ENVv vals) M knW2 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2b3e24) M (seg_rom RSEGS)) (modelV VM)) (t_die msg_oom fs0).
  Proof.
    intros vals R M VM HL P0 HR HK.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi.
    unfold sp_window_lo, sp_window_hi in *.
    run_block scr0 75%nat.
    oom_stdio_exit HL P0 resX_eq (mV_fd2 VM) (mV_fs VM).
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Variable K : TSet.

  (* [comment removed for export] *)
(* [comment removed for export] *)
  Definition w65_vm (VM : VmMaps) (mb gm : word) : Prop :=
    vm_reserved VM = RES /\ (LIM <= vm_limit VM)%Z /\ vm_init_sp VM = sp0 /\    (* [comment removed for export] *)
    (bv_unsigned gm + 69632 <= bv_unsigned sp0 - 8388608)%Z /\
    ((vm_maps VM = [(gm, Z_to_bv 64 69632); (mb, Z_to_bv 64 8192)]
      /\ (bv_unsigned gm + 69632 <= bv_unsigned mb \/ bv_unsigned mb + 8192 <= bv_unsigned gm)%Z)
     \/ (vm_maps VM = [(gm, Z_to_bv 64 69632); (Z_to_bv 64 (bv_unsigned mb + 4096), Z_to_bv 64 4096)]
      /\ (bv_unsigned gm + 69632 <= bv_unsigned mb + 4096 \/ bv_unsigned mb + 8192 <= bv_unsigned gm)%Z)).

  Definition exitG_branch : Prop :=
    forall vals R M VM,
      length vals = 108%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = p1 sp0 a0s path envv ->
      vals_ev vals 73 = brk -> vals_ev vals 5 = tid ->
      regs_ok (ENVv vals) srZ R -> know_ok RSEGS (ENVv vals) M knZ ->
      vm_pre VM sp0 brk (Z_to_bv 64 (bv_unsigned brk + 8192)) (vals_ev vals 75) -> w65_vm VM brk (vals_ev vals 75) -> SI M ->
      GG RSEGS mode Q K (mkCfg (mkst R (Z_to_bv 64 0xe19e0) M (seg_rom RSEGS)) (modelV VM)).

  Lemma w65_G : forall vals R M VM,
    exitG_branch ->
    length vals = 76%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = p1 sp0 a0s path envv ->
    vals_ev vals 73 = brk -> vals_ev vals 5 = tid ->
    regs_ok (ENVv vals) srG0 R -> know_ok RSEGS (ENVv vals) M knG0 ->
    vm_pre VM sp0 brk (Z_to_bv 64 (bv_unsigned brk + 8192)) (vals_ev vals 75) -> w65_vm VM brk (vals_ev vals 75) -> SI M ->
    GG RSEGS mode Q K (mkCfg (mkst R (Z_to_bv 64 0x2b3e24) M (seg_rom RSEGS)) (modelV VM)).
  Proof.
    intros vals R M VM EXIT HL P0 P2 P70 P5 HR HK HVM HVS HSI.
    assert (Gtop : (bv_unsigned (vals_ev vals 75) + 69632 <= bv_unsigned sp0 - 8388608)%Z) by exact (proj1 (proj2 (proj2 (proj2 HVS)))).
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi.
    unfold sp_window_lo, sp_window_hi in *.
    pose proof (brk_lo brk Hbrk) as Blo. pose proof (brk_hi path brk Hbrk Hplen) as Bhi. pose proof (brk_al brk Hbrk) as Bal.
    (* [comment removed for export] *)
    pose proof (know_nth RSEGS _ _ knG0 ltac:(let i := kidx knG0 (is_krange gx) in exact i) _ HK eq_refl)
      as Kgm; cbn [kentry_ok edenot ev ENV] in Kgm.
    pose proof (know_nth RSEGS _ _ knG0 ltac:(let i := kidx knG0 (is_kalign gx) in exact i) _ HK eq_refl)
      as Kga; cbn [kentry_ok edenot ev ENV] in Kga.
    pose proof (know_nth RSEGS _ _ knG0 ltac:(let i := kidx knG0 (is_kdisj bx gx) in exact i) _ HK eq_refl)
      as Kgd; cbn [kentry_ok] in Kgd; unfold estart in Kgd; cbn [a_base a_off edenot ev ENV] in Kgd; rewrite P70 in Kgd.
    set (gm := vals_ev vals 75) in *.
    (* [comment removed for export] *)
    gg_block_keep scrG 76%nat.
    { unfold sc_denot. cbn [edenot ev ENV]. apply bt_ne_not. subst gm. lia. }
    si_block HSI R M.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ ?E ?MG ?kn =>
      krdv HK 73%nat 4136%Z 8%nat Hmem; [apply flat_intro; cbn [edenot ev ENV]; rewrite ?P70; lia|];
      krdv HK 73%nat 4152%Z 8%nat Hmw; [apply flat_intro; cbn [edenot ev ENV]; rewrite ?P70; lia|];
      pose proof (know_nth RSEGS _ _ kn ltac:(let i := kidx kn (is_kzero_cov gx 9 8) in exact i) _ HK eq_refl) as Kz;
      cbn [kentry_ok] in Kz; unfold elenZ, estart in Kz; cbn [a_base a_off edenot ev ENV] in Kz;
      pose proof (kwr_store_ok RSEGS E _ kn ltac:(let i := kidx kn (is_kwr_cov gx 13 69615) in exact i)
                    _ _ _ 13 (Z.to_nat 69615) HK eq_refl ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as Hok;
      pose proof (know_nth RSEGS _ _ kn ltac:(let i := kidx kn (is_kimg_cov 467508 96) in exact i) _ HK eq_refl) as Kimg;
      cbn [kentry_ok] in Kimg
    end.
    fold gm in Kz, Hmem, Hmw, Hok.
    unfold adenot, v_addi in Hmem, Hmw, Hok. cbn [a_base a_off edenot ev ENV] in Hmem, Hmw, Hok.
    rewrite P70 in Hmem, Hmw. fold gm in Hok.
    change (bv_unsigned (Z_to_bv 64 69623)) with 69623%Z in Kz.
    assert (EF : efH M (Z_to_bv 64 1) (bv_unsigned brk + 4120) (bv_unsigned gm) 72480 0 65536 0 0 69616
                     (bv_unsigned gm + 16) 1).
    { constructor.
      - vm_compute. reflexivity.
      - unfold slot_start, UNIT. lia.
      - vm_compute. reflexivity.
      - pose proof (u64_range brk). lia.
      - pose proof (u64_range gm). lia.
      - lia.
      - lia.
      - lia.
      - intros _. vm_compute. reflexivity.
      - lia.
      - lia.
      - lia.
      - lia.
      - lia.
      - lia.
      - replace (bv_unsigned brk + 4120 + 16)%Z with (bv_unsigned brk + 4136)%Z by lia.
        rewrite Hmem. subst gm. rewrite Z_to_bv_bv_unsigned. reflexivity.
      - replace (bv_unsigned brk + 4120 + 32)%Z with (bv_unsigned brk + 4152)%Z by lia. exact Hmw.
      - replace (bv_unsigned gm + 16 - 4)%Z with (bv_unsigned gm + 9 + 3)%Z by lia. apply (proj2 Kz). lia.
      - replace (bv_unsigned gm + 16 - 3)%Z with (bv_unsigned gm + 9 + 4)%Z by lia. apply (proj2 Kz). lia.
      - intros C. exfalso. apply C. reflexivity.
      - replace (bv_unsigned gm + 16 - 3)%Z with (bv_unsigned gm + 13)%Z by lia.
        replace (Z.to_nat (69616 - 1)) with (Z.to_nat 69615) by reflexivity. exact Hok.
      - intros j Hj. unfold SCT. apply (proj2 (proj2 Kimg)). lia. }
    assert (RT : Hoare.ret_ok (Z_to_bv 64 0xe19e0)) by (apply bv_eq; vm_compute; reflexivity).
    assert (G1 : getr R 1 = Z_to_bv 64 0xe19e0) by (regv HR (1:reg); reflexivity).
    assert (G10 : getr R 10 = Z_to_bv 64 (bv_unsigned brk + 4120)).
    { regv HR (10:reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV].
      rewrite P70. reflexivity. }
    assert (G11 : getr R 11 = Z_to_bv 64 0) by (regv HR (11:reg); reflexivity).
    assert (G12 : getr R 12 = Z_to_bv 64 65536) by (regv HR (12:reg); reflexivity).
    assert (G13 : getr R 13 = Z_to_bv 64 1) by (regv HR (13:reg); reflexivity).
    destruct (enframe_run M (Z_to_bv 64 1) _ _ _ _ _ _ _ _ _ _ EF R (seg_rom RSEGS) (Z_to_bv 64 0xe19e0)
                G1 RT G10 G11 G12 G13) as (R2 & Hms & Hkeep & HA0).
    clear RT G1 G10 G11 G12 G13.
    replace (Z_to_bv 64 2830836) with (0x2b31f4 : word) by (apply bv_eq; vm_compute; reflexivity).
    eapply gg_msteps; [reflexivity | reflexivity | exact Hms |]. clear Hms.
    (* [comment removed for export] *)
    replace (memF M 0 65536 69616 (bv_unsigned gm + 16) 1) with (mem_denot (ENVv vals) M LOGE).
    2:{ unfold memF. cbv delta [mF mE mE1 mD] beta zeta.
        replace (69616 - 4 - 65536 - 16 * 1)%Z with 4060%Z by reflexivity.
        replace (69616 * 0 / 16 + 1)%Z with 1%Z by reflexivity.
        change (1 =? 0)%Z with false. change (4060 =? 0)%Z with false. change (4060 <? 5)%Z with false.
        cbv iota.
        replace (0 + 32 * res_code 4060)%Z with 160%Z by reflexivity.
        replace (bv_unsigned gm + 16 - 3)%Z with (bv_unsigned gm + 13)%Z by lia.
        replace (bv_unsigned gm + 16 - 2)%Z with (bv_unsigned gm + 14)%Z by lia.
        replace (bv_unsigned gm + 16 + 16 * 1 - 4)%Z with (bv_unsigned gm + 28)%Z by lia.
        replace (bv_unsigned gm + 16 + 16 * 1 - 3)%Z with (bv_unsigned gm + 29)%Z by lia.
        replace (bv_unsigned gm + 16 + 16 * 1 - 2)%Z with (bv_unsigned gm + 30)%Z by lia.
        replace (bv_unsigned gm + 16 + 16 * 1 + 65536)%Z with (bv_unsigned gm + 65568)%Z by lia.
        replace (bv_unsigned gm + 16 + 69616 - 4 - 5)%Z with (bv_unsigned gm + 69623)%Z by lia.
        replace (bv_unsigned gm + 16 + 69616 - 4 - 4)%Z with (bv_unsigned gm + 69624)%Z by lia.
        unfold LOGE. cbn [mem_denot]. unfold adenot. cbn [a_base a_off edenot gx ev ENV]. fold gm. unfold v_addi.
        change (word_to_le_bytes 1 (Z_to_bv 64 160)) with [Z_to_bv 8 160].
        change (word_to_le_bytes 1 (Z_to_bv 64 0)) with [Z_to_bv 8 0].
        change (word_to_le_bytes 1 (Z_to_bv 64 224)) with [Z_to_bv 8 224].
        reflexivity. }
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ ?E ?MG ?kn =>
      pose proof (carry_after RSEGS E MG LOGE kn [] knZ [] _ ltac:(vm_compute; reflexivity)
                    ltac:(cbn [log_flat LOGE]; unfold flat, estart; cbn [a_base a_off edenot gx ev ENV]; fold gm;
                          repeat split; lia)
                    HK ltac:(constructor)) as HK2
    end.
    (* [comment removed for export] *)
    assert (HSI2 : SI (mem_denot (ENVv vals) M LOGE)).
    { apply (SI_step M); [|exact HSI]. intros xa Hxa.
      apply (mem_denot_above_vb (ENVv vals) M VB LOGE 0%nat 0x354000 xa);
        [ unfold VB, vb_ok; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd ev ENV]; rewrite ?P0, ?P70; fold gm; lia
        | vm_compute; reflexivity | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia | lia]. }
    (* [comment removed for export] *)
    lazymatch type of HR with regs_ok _ ?sr _ =>
      pose proof (regs_after_keeps vals _ sr R R2 callee_saved ltac:(rewrite HL; vm_compute; reflexivity)
                    HR Hkeep callee_saved_no0) as HR2 end.
    rewrite HL in HR2. clear HR.
    set (vals2 := vals ++ junk_vals R2) in *.
    assert (HL2 : length vals2 = 108%nat) by (subst vals2; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (Q2 : vals_ev vals2 2 = p1 sp0 a0s path envv) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P2).
    assert (Q70 : vals_ev vals2 73 = brk) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P70).
    assert (Q5 : vals_ev vals2 5 = tid) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P5).
    assert (Q72 : vals_ev vals2 75 = gm) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); reflexivity).
    change (Env (vals_ev vals2) (blobs_ev (blobs0 a0s path rdraw))) with (ENVv vals2) in HR2.
    pose proof (regs_ok_set_have (ENVv vals2) _ R2 10 _ (EAlu ALU_ADD gx (ELit 32)) HR2 HA0
                  ltac:(rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot gx ev ENV];
                        rewrite Q72; f_equal; lia) ltac:(discriminate)) as HR3.
    clear HR2.
    lazymatch type of HR3 with regs_ok _ ?sr _ => replace sr with srZ in HR3 by (vm_compute; reflexivity) end.
    lazymatch type of HK2 with know_ok _ _ ?Mc ?kn =>
      pose proof (env_app_know RSEGS vals (junk_vals R2) _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK3 end.
    clear HK2 HK.
    change (Env (vals_ev (vals ++ junk_vals R2)) (blobs_ev (blobs0 a0s path rdraw))) with (ENVv vals2) in HK3.
    change (mem_denot (Env (vals_ev vals) (blobs_ev (blobs0 a0s path rdraw))) M LOGE) with (mem_denot (ENVv vals) M LOGE) in HSI2.
    apply (EXIT vals2 R2 _ VM HL2 Q0 Q2 Q70 Q5 HR3 HK3); [rewrite Q72; exact HVM | rewrite Q72; exact HVS | exact HSI2].
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition VMk : VmMaps :=
    mkVmMapsFull RES [(brk, Z_to_bv 64 8192)] [] brk (Z_to_bv 64 (bv_unsigned brk + 8192)) lim mbase sp0.
  Definition VMo : VmMaps :=
    mkVmMapsFull RES [(brk, Z_to_bv 64 8192)] [(brk, Z_to_bv 64 4096)] brk (Z_to_bv 64 (bv_unsigned brk + 8192)) lim mbase sp0.
  Definition VMd : VmMaps :=
    mkVmMapsFull RES [(Z_to_bv 64 (bv_unsigned brk + 4096), Z_to_bv 64 4096)] [] brk
                 (Z_to_bv 64 (bv_unsigned brk + 8192)) lim mbase sp0.
  Definition vm_mid (VM : VmMaps) : Prop := VM = VMk \/ VM = VMo \/ VM = VMd.

  Lemma RES_eq : RES = [(Z_to_bv 64 65536, Z_to_bv 64 856064); (Z_to_bv 64 921600, Z_to_bv 64 1966080);
                        (Z_to_bv 64 2887680, Z_to_bv 64 380928); (Z_to_bv 64 3268608, Z_to_bv 64 221184)].
  Proof. vm_compute. reflexivity. Qed.

  Lemma vm_mid_shape : forall VM, vm_mid VM ->
    vm_reserved VM = RES /\ vm_limit VM = lim /\ vm_init_sp VM = sp0
    /\ exists mp ms, vm_maps VM = [(mp, ms)]
       /\ (bv_unsigned ms = 8192 /\ mp = brk \/ bv_unsigned ms = 4096 /\ bv_unsigned mp = bv_unsigned brk + 4096)%Z.
  Proof.
    intros VM HV. pose proof (brk_lo brk Hbrk) as Blo. pose proof (brk_hi path brk Hbrk Hplen) as Bhi.
    destruct HV as [-> | [-> | ->]]; cbn [VMk VMo VMd vm_reserved vm_limit vm_init_sp vm_maps];
      (split; [reflexivity|]); (split; [reflexivity|]); (split; [reflexivity|]); eexists _, _; (split; [reflexivity|]);
      rewrite ?u64_lit by lia.
    - left. split; [reflexivity | reflexivity].
    - left. split; [reflexivity | reflexivity].
    - right. split; reflexivity.
  Qed.

  Lemma vm_mid_grant_exists : forall hint VM, vm_mid VM -> exists a, grant_ok hint (modelV VM) a (page_round_up_Z 69632) = true.
  Proof.
    intros hint VM HV. pose proof (brk_lo brk Hbrk) as Blo. pose proof (brk_hi path brk Hbrk Hplen) as Bhi.
    destruct (vm_mid_shape VM HV) as (Hr & Hl & Hsp & mp & ms & Hm & Hms).
    pose proof (proj1 Hvsp) as SPlo. unfold sp_window_lo in SPlo.
    change (page_round_up_Z 69632) with 69632%Z.
    apply grant_exists.
    - unfold init_sp_ok. rewrite mV_vmmaps, Hsp. unfold sp_window_lo. lia.
    - lia.
    - rewrite mV_vmmaps, Hr, Hm, RES_eq. repeat constructor; cbn [snd]; rewrite ?u64_lit by lia; lia.
    - rewrite mV_vmmaps, Hr, Hm, RES_eq. cbn [length app Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
    - apply grant_budget_intro; [reflexivity | reflexivity |]. rewrite mV_vmmaps.
      unfold vm_live_bytes. rewrite Hm, Hl. cbn [live_bytes]. pose proof LIM_ge. pose proof lim_ge. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma vm_mid_grant : forall hint VM a, vm_mid VM -> grant_ok hint (modelV VM) a 69632 = true ->
    (bv_unsigned a mod 4096 = 0 /\ 0x354000 <= bv_unsigned a /\ bv_unsigned a + 69632 <= bv_unsigned sp0 - 8388608
     /\ (bv_unsigned brk + 8192 <= bv_unsigned a \/ bv_unsigned a + 69632 <= bv_unsigned brk + 4096))%Z
    /\ (forall mp ms, vm_maps VM = [(mp, ms)] ->
          (bv_unsigned a + 69632 <= bv_unsigned mp \/ bv_unsigned mp + bv_unsigned ms <= bv_unsigned a)%Z).
  Proof.
    intros hint VM a HV Hg. pose proof (brk_lo brk Hbrk) as Blo. pose proof (brk_hi path brk Hbrk Hplen) as Bhi.
    destruct (vm_mid_shape VM HV) as (Hr & Hl & Hsp & mp & ms & Hm & Hms).
    destruct (grant_ok_unpack _ _ _ _ Hg) as (Hal & Hpos & Hce & Hrf & Hlive).
    rewrite mV_vmmaps in Hrf. rewrite Hr, Hm, RES_eq in Hrf. rewrite mV_vmmaps in Hce. unfold alloc_top in Hce. rewrite Hsp, stack_max_size_val in Hce.
    unfold page_size in Hal. pose proof (u64_range a) as Ha.
    assert (Hn : bv_unsigned (Z_to_bv 64 69632) = 69632%Z) by (apply u64_lit; lia).
    pose proof (region_free_In _ _ _ (Z_to_bv 64 65536) (Z_to_bv 64 856064) Hrf ltac:(cbn [In app]; tauto)) as D1.
    pose proof (region_free_In _ _ _ (Z_to_bv 64 921600) (Z_to_bv 64 1966080) Hrf ltac:(cbn [In app]; tauto)) as D2.
    pose proof (region_free_In _ _ _ (Z_to_bv 64 2887680) (Z_to_bv 64 380928) Hrf ltac:(cbn [In app]; tauto)) as D3.
    pose proof (region_free_In _ _ _ (Z_to_bv 64 3268608) (Z_to_bv 64 221184) Hrf ltac:(cbn [In app]; tauto)) as D4.
    pose proof (region_free_In _ _ _ mp ms Hrf ltac:(cbn [In app]; tauto)) as D5.
    rewrite Hn in D1, D2, D3, D4, D5. rewrite !u64_lit in D1 by lia. rewrite !u64_lit in D2 by lia. rewrite !u64_lit in D3 by lia. rewrite !u64_lit in D4 by lia.
    assert (Ha4096 : (4096 <= bv_unsigned a)%Z).
    { destruct (proj1 (Z.mod_divide (bv_unsigned a) 4096 ltac:(lia)) Hal) as [q Hq]. lia. }
    pose proof (u64_range mp).
    split.
    2:{ intros mp' ms' Hm'. rewrite Hm in Hm'. injection Hm' as <- <-. exact D5. }
    destruct Hms as [[Hms1 ->] | [Hms1 Hmp]]; rewrite ?Hms1, ?Hmp in D5; repeat split; lia.
  Qed.

  Lemma w65_mid : forall vals R M VM,
    exitG_branch ->
    length vals = 75%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = p1 sp0 a0s path envv ->
    vals_ev vals 73 = brk -> vals_ev vals 5 = tid ->
    regs_ok (ENVv vals) srM R -> know_ok RSEGS (ENVv vals) M knM -> VM = VMo -> SI M ->     (* [comment removed for export] *)
    GG RSEGS mode Q K     (* [comment removed for export] *)
       (mkCfg (mkst R (Z_to_bv 64 0x2b2494) M (seg_rom RSEGS)) (modelV VM)).
  Proof.
    intros vals R M VM EXIT HL P0 P2 P70 P5 HR HK HVo HSI.
    assert (HV : vm_mid VM) by (right; left; exact HVo).
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi.
    unfold sp_window_lo, sp_window_hi in *.
    pose proof (brk_lo brk Hbrk) as Blo. pose proof (brk_hi path brk Hbrk Hplen) as Bhi. pose proof (brk_al brk Hbrk) as Bal.
    (* [comment removed for export] *)
    gg_block_keep scr0 75%nat. si_block HSI R M.
    (* [comment removed for export] *)
    eapply (gg_mmap_anon RSEGS mode Q _ _ _ (modelV VM) ECALLW 69632).
    - vm_compute. reflexivity.
    - apply is_ecall_ECALLW.
    - reflexivity.
    - reflexivity.
    - regv HR (17 : reg). reflexivity.
    - regv HR (11 : reg). reflexivity.
    - lia.
    - regv HR (12 : reg). reflexivity.
    - regv HR (13 : reg). reflexivity.
    - regv HR (14 : reg). apply bv_eq. reflexivity.
    - regv HR (15 : reg). reflexivity.
    - apply vm_mid_grant_exists. exact HV.
    - (* [comment removed for export] *)
      intros Hmode e He. assert (e = ENOMEM) as -> by (destruct He as [<-|[]]; reflexivity).
      rewrite v_addi_pc4 by lia. change (0x2b3e20 + 4)%Z with 0x2b3e24%Z.
      lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
        pose proof (regs_set_a0 E sr Rc (errno_ret ENOMEM) ENOMEMv HR ltac:(apply bv_eq; reflexivity)) as HR2 end.
      eapply (w65_oomN vals); [exact HL | exact P0 | exact HR2 | exact HK].
    - (* [comment removed for export] *)
      intros a Hg. rewrite v_addi_pc4 by lia. change (0x2b3e20 + 4)%Z with 0x2b3e24%Z.
      change (page_round_up_Z 69632) with 69632%Z in Hg |- *.
      destruct (vm_mid_grant _ VM a HV Hg) as ((Gal & Glo & Ghi & Gdj) & Gsep).
      (* [comment removed for export] *)
      lazymatch type of HR with regs_ok _ ?sr ?Rc =>
        pose proof (env_app_regs vals [a] _ sr Rc ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR2 end.
      lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
        pose proof (env_app_know RSEGS vals [a] _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
      clear HR HK.
      set (vals2 := vals ++ [a]) in *.
      assert (HL2 : length vals2 = 76%nat) by (subst vals2; rewrite length_app, HL; reflexivity).
      assert (Q0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
      assert (Q2 : vals_ev vals2 2 = p1 sp0 a0s path envv) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P2).
      assert (Q70 : vals_ev vals2 73 = brk) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P70).
      assert (Q5 : vals_ev vals2 5 = tid) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P5).
      assert (Q72 : vals_ev vals2 75 = a).
      { subst vals2. rewrite <- HL. rewrite <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity. }
      clearbody vals2. clear HL P0 P2 P70 P5 vals. rename HL2 into HL.
      change (Env (vals_ev vals2) (blobs_ev (blobs0 a0s path rdraw))) with (ENVv vals2) in HR2, HK2.
      pose proof (regs_set_a0 (ENVv vals2) _ _ a gx HR2 ltac:(cbn [edenot gx ev ENV]; exact Q72)) as HR. clear HR2.
      (* [comment removed for export] *)
      lazymatch type of HK2 with know_ok _ _ ?Mc _ =>
        assert (HK3 : know_ok RSEGS (ENVv vals2) Mc knG00) end.
      { unfold knG00. apply know_ok_cons; [|apply know_ok_cons; [|apply know_ok_cons; [|apply know_ok_cons; [|exact HK2]]]].
        - apply kalign_intro; [lia|]. cbn [edenot gx ev ENV]. rewrite Q72. exact Gal.
        - apply krange_intro. cbn [edenot gx ev ENV]. rewrite Q72. lia.
        - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot gx ev ENV]. rewrite Q0, Q72. lia.
        - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot bx gx ev ENV]. rewrite Q70, Q72. lia. }
      clear HK2.
      pose proof (xfer_zfill RSEGS (ENVv vals2) _ knG00 gx 0 a 69632 HK3
                    ltac:(unfold estart; cbn [a_base a_off edenot gx ev ENV]; rewrite Q72; lia)
                    ltac:(lia) ltac:(lia)) as HK.
      clear HK3.
      lazymatch type of HK with know_ok _ _ _ ?kn => replace kn with knG0 in HK by (vm_compute; reflexivity) end.
      apply (w65_G vals2 _ _ _ EXIT HL Q0 Q2 Q70 Q5 HR HK).
      3:{ si_fill HSI. }
      2:{ rewrite Q72. destruct (vm_mid_shape VM HV) as (Hr & Hl & Hsp & mp & ms & Hm & Hms).
          unfold w65_vm, mmap_model. rewrite ?with_vmmaps_vm, ?mV_vmmaps. cbn [vm_reserved vm_limit vm_init_sp vm_maps]. rewrite Hr, Hl, Hsp, Hm.
          split; [reflexivity|]. split; [exact lim_ge|]. split; [reflexivity|]. split; [lia|].   (* [comment removed for export] *)
          specialize (Gsep mp ms Hm). pose proof (u64_range mp).
          destruct Hms as [[Hms1 ->] | [Hms1 Hmp]].
          - left. split; [rewrite <- (Z_to_bv_bv_unsigned 64 ms), Hms1; reflexivity | lia].
          - right. split; [rewrite <- (Z_to_bv_bv_unsigned 64 ms), Hms1, <- (Z_to_bv_bv_unsigned 64 mp), Hmp; reflexivity | lia]. }
      (* [comment removed for export] *)
      rewrite Q72. destruct (vm_mid_shape VM HV) as (Hr & Hl & Hsp & mp & ms & Hm & Hms).
      unfold vm_pre, mmap_model. rewrite ?with_vmmaps_vm, ?mV_vmmaps. cbn [vm_reserved vm_limit vm_init_sp vm_maps vm_noaccess vm_start_brk vm_brk].
      rewrite Hr, Hl, Hsp, Hm.
      assert (Hn : bv_unsigned (Z_to_bv 64 69632) = 69632%Z) by (apply u64_lit; lia).
      split; [reflexivity|]. split; [exact lim_ge|]. split; [reflexivity|]. split; [apply map_has_head|].   (* [comment removed for export] *)
      pose proof (u64_range mp) as Hmpr. pose proof (Gsep mp ms Hm) as Gsp.
      split.
      { constructor; [cbn [fst snd]; rewrite ?Hn; lia|]. constructor; [|constructor].
        cbn [fst snd]. destruct Hms as [[Hms1 ->] | [Hms1 Hmp]]; lia. }
      split; [cbn; lia|].
      split; [cbn [live_bytes]; rewrite Hn; lia|].
      split.
      { exists (mp, ms). split; [cbn [In]; tauto|]. cbn [fst snd].
        split; [intros Emp; apply (f_equal bv_unsigned) in Emp; destruct Hms as [[Hms1 ->] | [Hms1 Hmp]]; lia|].
        destruct Hms as [[Hms1 ->] | [Hms1 Hmp]]; lia. }
      (* [comment removed for export] *)
      split.
      { constructor; [|constructor; [constructor | constructor]].
        constructor; [|constructor]. unfold HUTargetPre.iv_disjoint. cbn [fst snd]. rewrite Hn. lia. }
      (* [comment removed for export] *)
      pose proof (brk_lo brk Hbrk) as Blo'. pose proof (brk_hi path brk Hbrk Hplen) as Bhi'. pose proof (brk_al brk Hbrk) as Bal'.
      split.
      { unfold HUTargetPre.vm_ledger. destruct HV as [-> | [-> | ->]]; cbn [VMk VMo VMd vm_start_brk vm_brk];
          rewrite !u64_lit by lia; (split; [lia | left; repeat split; try reflexivity; lia]). }
      (* [comment removed for export] *)
      unfold vm_exact. cbn [vm_maps vm_noaccess vm_start_brk vm_brk].
      assert (Emp : (mp, ms) = (brk, Z_to_bv 64 8192)) by (rewrite HVo in Hm; cbn [VMo vm_maps] in Hm; injection Hm as <- <-; reflexivity).
      rewrite Emp, HVo. cbn [VMo vm_noaccess vm_start_brk vm_brk].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [apply u64_lit; lia|]. split; [rewrite rtop; lia|].
      split; [exact Gal|]. split; [lia|]. split; [lia|].
      destruct (grant_ok_unpack _ _ _ _ Hg) as (_ & _ & _ & Hrf & _). rewrite mV_vmmaps, Hr in Hrf.
      rewrite LedgerCfg.region_free_app in Hrf. apply andb_prop in Hrf. split; [exact (proj1 Hrf)|].
      injection Emp as -> ->. rewrite (u64_lit 8192) in Gsp by lia.
      split; [lia | exact (proj1 (proj2 Hbrk))].     (* [comment removed for export] *)
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac guard_tail EXIT HL P0 P1 P2 P70 P5 VMX HSI Rn Mn :=
    any_blockW_keep scr0 74%nat; si_block HSI Rn Mn;
    lazymatch goal with
    | HR' : regs_ok _ ?sr ?R', HK' : know_ok _ _ ?M' ?kn |- _ =>
      (* [comment removed for export] *)
      pose proof (env_app_regs _ [getr R' 10] _ sr R' ltac:(rewrite HL; vm_compute; reflexivity) HR') as HR2;
      pose proof (env_app_know RSEGS _ [getr R' 10] _ M' kn ltac:(rewrite HL; vm_compute; reflexivity) HK') as HK2;
      clear HR' HK';
      lazymatch goal with
      | |- _ =>
        lazymatch type of HL with length ?vals = _ =>
        set (vals2 := vals ++ [getr R' 10]) in *;
        assert (HL2 : length vals2 = 75%nat) by (subst vals2; rewrite length_app, HL; reflexivity);
        assert (Q0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0);
        assert (Q2 : vals_ev vals2 2 = p1 sp0 a0s path envv) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P2);
        assert (Q70 : vals_ev vals2 73 = brk) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P70);
        assert (Q5 : vals_ev vals2 5 = tid) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P5);
        assert (Q71 : vals_ev vals2 74 = getr R' 10)
          by (subst vals2; rewrite <- HL; rewrite <- (Nat.add_0_r (length vals)); rewrite vals_ev_app_r; reflexivity);
        change (Env (vals_ev vals2) (blobs_ev (blobs0 a0s path rdraw))) with (ENVv vals2) in HR2, HK2;
        pose proof (regs_ok_set_have (ENVv vals2) _ R' 10 _ (EVar 74) HR2 eq_refl
                      ltac:(cbn [edenot ev ENV]; exact Q71) ltac:(discriminate)) as HR3;
        clear HR2;
        lazymatch type of HR3 with regs_ok _ ?sr3 _ => replace sr3 with srM in HR3 by (vm_compute; reflexivity) end;
        pose proof (know_ok_sub RSEGS (ENVv vals2) M' kn knM ltac:(vm_compute; reflexivity) HK2) as HK3;
        clear HK2;
        apply (w65_mid vals2 R' M' VMX EXIT HL2 Q0 Q2 Q70 Q5 HR3 HK3); [ | exact HSI ]
        end
      end
    end.

  Theorem brk_ok_worldV : exitG_branch -> brk_ok_entry K.     (* [comment removed for export] *)
  Proof.
    intros EXIT vals R M HL P0 P70 P1 P2 P5 HR HK HSI0.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi.
    unfold sp_window_lo, sp_window_hi in *.
    pose proof (brk_lo brk Hbrk) as Blo. pose proof (brk_hi path brk Hbrk Hplen) as Bhi. pose proof (brk_al brk Hbrk) as Bal.
    assert (HSI : SI (zfill brk (Z_to_bv 64 8192) M)) by si_fill HSI0. clear HSI0.
    (* [comment removed for export] *)
    pose proof (regs_set_a0 (ENVv vals) _ _ (Z_to_bv 64 (bv_unsigned brk + 8192)) (EAlu ALU_ADD bx (ELit 8192)) HR
                  ltac:(rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot bx ev ENV];
                        rewrite P70; reflexivity)) as HR1. clear HR.
    lazymatch type of HR1 with regs_ok _ ?sr _ => replace sr with srW0 in HR1 by (vm_compute; reflexivity) end.
    (* [comment removed for export] *)
    pose proof (xfer_zfill RSEGS (ENVv vals) M knD2 bx 0 brk 8192 HK
                  ltac:(unfold estart; cbn [a_base a_off edenot bx ev ENV]; rewrite P70; lia) ltac:(lia)
                  ltac:(pose proof (u64_range brk); lia)) as HK0. clear HK.
    pose proof (kderive_all_sound RSEGS (ENVv vals) _ _ knW0 HK0 ltac:(vm_compute; reflexivity)) as HK1. clear HK0.
    rename HR1 into HR. rename HK1 into HK.
    change (mkModelA fdsV (mkVmMapsFull RES [(brk, Z_to_bv 64 8192)] [] brk (Z_to_bv 64 (bv_unsigned brk + 8192)) lim mbase sp0)
                    stdin0 fs0 None (Some tid) None) with (modelV VMk).
    (* [comment removed for export] *)
    gg_block_keep scr0 74%nat. si_block HSI R M.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    eapply (gg_mmap_fixed_noaccess RSEGS mode Q _ _ _ (modelV VMk) ECALLW brk 4096).
    - vm_compute. reflexivity.
    - apply is_ecall_ECALLW.
    - reflexivity.
    - reflexivity.
    - regv HR (17 : reg). reflexivity.
    - regv HR (10 : reg). cbn [edenot bx ev ENV]. exact P70.
    - exact Bal.
    - lia.
    - regv HR (11 : reg). reflexivity.
    - lia.
    - change (page_round_up_Z 4096) with 4096%Z. rewrite mV_vmmaps. unfold alloc_top. cbn [VMk vm_init_sp]. rewrite stack_max_size_val. lia.
    - regv HR (12 : reg). reflexivity.
    - regv HR (13 : reg). reflexivity.
    - regv HR (14 : reg). apply bv_eq. reflexivity.
    - regv HR (15 : reg). reflexivity.
    - rewrite mV_vmmaps. cbn [VMk vm_reserved]. apply region_free_above_top. rewrite rtop. lia.
    - rewrite mV_vmmaps. cbn [VMk vm_maps]. change (page_round_up_Z 4096) with 4096%Z.
      apply map_contains_head; rewrite ?u64_lit by lia; lia.
    - (* [comment removed for export] *)
      rewrite v_addi_pc4 by lia. change (0x2b3e20 + 4)%Z with 0x2b3e24%Z.
      change (page_round_up_Z 4096) with 4096%Z.
      lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
        pose proof (regs_set_a0 E sr Rc brk bx HR ltac:(cbn [edenot bx ev ENV]; exact P70)) as HR1 end.
      clear HR. rename HR1 into HR.
      lazymatch type of HK with know_ok _ ?E ?Mc ?kn =>
        pose proof (xfer_unfill RSEGS E Mc kn bx 0 brk 4096 HK
                      ltac:(unfold estart; cbn [a_base a_off edenot bx ev ENV]; rewrite P70; lia) ltac:(lia)
                      ltac:(pose proof (u64_range brk); lia)) as HK1 end.
      clear HK. rename HK1 into HK.
      lazymatch type of HK with know_ok _ _ _ ?kn => replace kn with knU in HK by (vm_compute; reflexivity) end.
      change (fixed_noaccess_model brk (Z_to_bv 64 4096) (modelV VMk)) with (modelV VMo).
      lazymatch type of HK with know_ok _ _ ?Mc _ => assert (HSI2 : SI Mc) by si_fill HSI end.
      clear HSI. rename HSI2 into HSI.
      guard_tail EXIT HL P0 P1 P2 P70 P5 VMo HSI R M. reflexivity.
  Qed.
End World.

(* [comment removed for export] *)
Theorem brk_ok_world_g sp0 a0s path envv rdraw tid mem0 brk mbase fs0 stdin0 lim   (* [comment removed for export] *)
  (lim_ge : (LIM <= lim)%Z)
  (Hvsp : valid_sp sp0) (Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z) (Hbrk : valid_brk RSEGS brk)
  (Hplen : (length path <= 4095)%nat) mode Q fd3 K :
  exitG_branch sp0 a0s path envv rdraw tid brk fs0 stdin0 mode Q fd3 (above_eq sp0 mem0) K ->
  brk_ok_branch_G sp0 a0s path envv rdraw tid mem0 brk mbase fs0 stdin0 lim mode Q fd3 K.
Proof.
  intros EXIT. exact (brk_ok_worldV sp0 a0s path envv rdraw tid mem0 brk mbase fs0 stdin0 lim lim_ge Hvsp Htid Hbrk Hplen mode Q fd3
                        (above_eq sp0 mem0) (above_eq_step sp0 mem0) K EXIT).
Qed.

Theorem brk_ok_world sp0 a0s path envv rdraw tid mem0 brk mbase fs0 stdin0 lim   (* [comment removed for export] *)
  (lim_ge : (LIM <= lim)%Z)
  (Hvsp : valid_sp sp0) (Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z) (Hbrk : valid_brk RSEGS brk)
  (Hplen : (length path <= 4095)%nat) mode Q K :
  exitG_branch sp0 a0s path envv rdraw tid brk fs0 stdin0 mode Q (FdFile path (Z_to_bv 64 0)) (above_eq sp0 mem0) K ->
  brk_ok_branch_M sp0 a0s path envv rdraw tid mem0 brk mbase fs0 stdin0 lim mode Q K.
Proof. exact (brk_ok_world_g sp0 a0s path envv rdraw tid mem0 brk mbase fs0 stdin0 lim lim_ge Hvsp Htid Hbrk Hplen mode Q (FdFile path (Z_to_bv 64 0)) K). Qed.
End H0W65.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.PropExec OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.CatExec OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.CatSim OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SeqExec OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.StoreOk OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SimInv OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.ExitSim OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.ShapeAlg OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.Nodes OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.MmapSim OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.AllocSim OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.FileSim OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.AgentLib OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SymExec OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SymExec2 OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SymExec2Sound OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SymRun OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SymDrive OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SymDriveX Spec OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.LibWritev OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.RefNodes HUExitBase HUExit OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.RefMemcpyLib OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.RefLayout HUMainEntryDefs OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.Hoare OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.Frame OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.MallocDefs HUEnframeBase HUEnframe HUReadBase HUWorld HUTargetPre.
Import HUPilotOOM_defs HUPilotOOM.
Import OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SymXfer OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SymAbove OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SymAboveV
       OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.ExistsRun OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.PhaseG OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.RefNodesG H0W65_defs H0W65.
Import ConeCfg.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import ListNotations.
Import ConeCfg.
Open Scope bv_scope.
Import SX2. Import SX2S.
Import ConeCfg.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition off_image (x : Z) : Prop := (x + 1 <= 0x10000 \/ 0x354000 <= x)%Z.

Lemma find_segment_skip : forall seg rest a n,
  (0 < n)%Z ->
  (a < Z.of_N (seg_base seg) \/ Z.of_N (seg_base seg) + Z.of_N (seg_size seg) < a + n)%Z ->
  find_segment (seg :: rest) a n = find_segment rest a n.
Proof.
  intros seg rest a n Hn H. cbn [find_segment].
  destruct (Z.leb_spec (Z.of_N (seg_base seg)) a); destruct (Z.leb_spec (a + n) (Z.of_N (seg_base seg) + Z.of_N (seg_size seg)));
    cbn [andb]; try reflexivity. lia.
Qed.

Lemma find_segment_off : forall a n, (0 < n)%Z -> (a + n <= 0x10000 \/ 0x354000 <= a)%Z ->
  find_segment RSEGS a n = None.
Proof.
  intros a n Hn H. unfold Ubsan.M.loaded_segments, Ubsan_loaded_segments.
  rewrite 4 find_segment_skip; [reflexivity | exact Hn | | exact Hn | | exact Hn | | exact Hn |];
    cbn [seg_base seg_size Ubsan_segment_000 Ubsan_segment_001 Ubsan_segment_002 Ubsan_segment_003]; lia.
Qed.

Lemma seg_rom_off : forall x : word, off_image (bv_unsigned x) -> seg_rom RSEGS x = None.
Proof.
  intros x Hx. unfold seg_rom, memory_read. rewrite find_segment_off; [reflexivity | cbn; lia | unfold off_image in Hx; cbn; lia].
Qed.

Lemma wview_off : forall M (x : word), off_image (bv_unsigned x) -> wview RSEGS M x = M x.
Proof.
  intros M x Hx. unfold wview. destruct (M x); [reflexivity|].
  rewrite find_segment_off; [reflexivity | lia | unfold off_image in Hx; lia].
Qed.

Lemma rdn1_off : forall M (x : word) b, off_image (bv_unsigned x) ->
  rdn RSEGS M x 1 = Some [b] -> M x = Some b.
Proof.
  intros M x b Hx H. cbn [rdn] in H. rewrite (seg_rom_off x Hx) in H.
  destruct (M x) as [b0|]; [|discriminate]. injection H as ->. reflexivity.
Qed.

Lemma store_ok1_off : forall M (x : word), off_image (bv_unsigned x) ->
  store_ok RSEGS M x 1 = true -> M x <> None.
Proof.
  intros M x Hx H. cbn [store_ok] in H. rewrite (wview_off M x Hx) in H.
  destruct (M x); [discriminate | discriminate].
Qed.

Lemma u64_lit' : forall z, (0 <= z < 2 ^ 64)%Z -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. apply Z_to_bv_small. unfold bv_modulus. lia. Qed.

Lemma u0 : bv_unsigned (Z_to_bv 64 0) = 0%Z.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma cell_intro : forall M (x : word) n (v : word) (a z : Z),
  rdn RSEGS M x n = Some (word_to_le_bytes n v) ->
  x = Z_to_bv 64 a -> v = Z_to_bv 64 z -> cell M a n z.
Proof. intros M x n v a z H -> ->. exact H. Qed.

Lemma zero_bytes_intro : forall E M b k n a,
  kentry_ok RSEGS E M (KZero (SA b k) (ELit n)) -> (0 <= n < 2 ^ 64)%Z ->
  (bv_unsigned (edenot E b) + k)%Z = a -> zero_bytes M a n.
Proof.
  intros E M b k n a [Hf Hz] Hn Ha i Hi. unfold estart, elenZ in Hz. cbn [a_base a_off edenot] in Hz.
  rewrite u64_lit' in Hz by lia. rewrite <- Ha. apply Hz. lia.
Qed.

Lemma def_intro : forall E M b kk len a n,
  kentry_ok RSEGS E M (KWr (SA b kk) len) ->
  (bv_unsigned (edenot E b) + kk <= a)%Z -> (a + n <= bv_unsigned (edenot E b) + kk + len)%Z ->
  (a + n <= 0x10000 \/ 0x354000 <= a)%Z -> (0 <= a)%Z -> (a + n <= 2 ^ 64)%Z ->
  forall i, (0 <= i < n)%Z -> M (Z_to_bv 64 (a + i)) <> None.
Proof.
  intros E M b kk len a n [Hf Hst] H1 H2 Hoff H0 H64 i Hi.
  unfold estart in Hst. cbn [a_base a_off] in Hst.
  specialize (Hst (a + i - (bv_unsigned (edenot E b) + kk))%Z 1%nat ltac:(lia) ltac:(cbn; lia)).
  replace (bv_unsigned (edenot E b) + kk + (a + i - (bv_unsigned (edenot E b) + kk)))%Z with (a + i)%Z in Hst by lia.
  refine (store_ok1_off M _ _ Hst). unfold off_image; rewrite u64_lit' by lia; lia.
Qed.

Lemma byte_intro : forall M a v,
  cell M a 1 v -> word_to_le_bytes 1 (Z_to_bv 64 v) = [Z_to_bv 8 v] ->
  (0 <= a)%Z -> (a + 1 <= 2 ^ 64)%Z -> (a + 1 <= 0x10000 \/ 0x354000 <= a)%Z ->
  M (Z_to_bv 64 a) = Some (Z_to_bv 8 v).
Proof.
  intros M a v Hc Hw H0 H64 Hoff. unfold cell in Hc. rewrite Hw in Hc.
  apply rdn1_off; [unfold off_image; rewrite u64_lit' by lia; lia | exact Hc].
Qed.

Lemma img_clear_of_know : forall E M ivs,
  know_ok RSEGS E M (map (fun iv => KImg (fst iv) (snd iv)) ivs) ->
  Forall (fun iv => img_clear M (fst iv) (snd iv)) ivs.
Proof.
  intros E M ivs HK. unfold know_ok in HK. rewrite Forall_map in HK.
  eapply Forall_impl; [|exact HK]. intros [lo hi] (A & B & C). exact C.
Qed.

(* [comment removed for export] *)
Lemma errno_some : forall M, exists bs,
  rdn RSEGS M (Z_to_bv 64 0x331a44) 4 = Some bs /\ length bs = 4%nat.
Proof.
  intros M. cbn [rdn].
  repeat match goal with
  | |- context [match M ?x with _ => _ end] =>
      destruct (M x); [| let r := eval vm_compute in (seg_rom RSEGS x) in change (seg_rom RSEGS x) with r]
  end; eexists; split; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac addr_split a :=
  lazymatch a with
  | bv_unsigned ?x =>
      lazymatch x with
      | vals_ev _ ?i => constr:((EVar i, 0%Z))
      | _ => lazymatch goal with P : vals_ev _ ?i = x |- _ => constr:((EVar i, 0%Z)) end
      end
  | (?y + ?c)%Z =>
      lazymatch y with
      | context [bv_unsigned _] =>
          lazymatch addr_split y with (?b, ?k) => let k' := eval vm_compute in (k + c)%Z in constr:((b, k')) end
      | _ => let a' := eval vm_compute in a in constr:((ELit 0, a'))
      end
  | (?y - ?c)%Z =>
      lazymatch y with
      | context [bv_unsigned _] =>
          lazymatch addr_split y with (?b, ?k) => let k' := eval vm_compute in (k - c)%Z in constr:((b, k')) end
      | _ => let a' := eval vm_compute in a in constr:((ELit 0, a'))
      end
  | _ => let a' := eval vm_compute in a in constr:((ELit 0, a'))
  end.

(* [comment removed for export] *)
Ltac kside :=
  rewrite ?edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev ENV ENVr gx bx ax]; rewrite ?u0; pins;
  rewrite ?ext_val_zx_id by (cbn; lia);
  first [ reflexivity
        | symmetry; apply Z_to_bv_bv_unsigned
        | rewrite Z_to_bv_bv_unsigned; (reflexivity || assumption || (symmetry; assumption))
        | f_equal; lia
        | lia ].

(* [comment removed for export] *)
Ltac kcell HK :=
  lazymatch goal with |- cell ?M ?a ?n ?z =>
  lazymatch type of HK with know_ok ?segs ?E M ?kn =>
  lazymatch addr_split a with (?b, ?k) =>
    let r := eval vm_compute in (kread segs kn b k n) in
    lazymatch r with
    | Some ?v =>
        apply (cell_intro M (adenot E (SA b k)) n (edenot E v) a z);
        [ apply (kread_rdn segs E M kn b k n v HK); [vm_compute; reflexivity | cbn; lia | cbn; lia
          | apply flat_intro; cbn [edenot ev ENV ENVr gx bx ax]; rewrite ?u0; pins; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ]
        | kside
        | kside ]
    | None => fail "kcell: knowledge does not determine" b k n
    end end end end.

(* [comment removed for export] *)
Ltac krdn HK :=
  lazymatch goal with |- rdn _ ?M (Z_to_bv 64 ?a) ?n = Some (word_to_le_bytes _ (Z_to_bv 64 ?z)) =>
    change (cell M a n z); kcell HK end.

(* [comment removed for export] *)
Ltac kzero HK :=
  lazymatch goal with |- zero_bytes ?M ?a ?n =>
  lazymatch type of HK with know_ok ?segs ?E M ?kn =>
  lazymatch addr_split a with (?b, ?k) =>
    let n' := eval vm_compute in n in
    apply (zero_bytes_intro E M b k n' a);
    [ apply (kderive_sound segs E M kn (KZero (SA b k) (ELit n')) HK); vm_compute; reflexivity
    | lia
    | cbn [edenot ev ENV ENVr gx bx ax]; rewrite ?u0; pins; lia ]
  end end end.

(* [comment removed for export] *)
Ltac kbyte HK :=
  lazymatch goal with |- ?M (Z_to_bv 64 ?a) = Some (Z_to_bv 8 ?v) =>
    apply (byte_intro M a v); [kcell HK | reflexivity | pins; lia | pins; lia | pins; lia] end.

(* [comment removed for export] *)
Ltac kdef HK b kk len :=
  lazymatch type of HK with know_ok ?segs ?E ?M ?kn =>
    apply (def_intro E M b kk len);
    [ apply (kderive_sound segs E M kn (KWr (SA b kk) len) HK); vm_compute; reflexivity
    | cbn [edenot ev ENV ENVr gx bx ax]; pins; lia
    | cbn [edenot ev ENV ENVr gx bx ax]; pins; lia
    | cbn [edenot ev ENV ENVr gx bx ax]; pins; lia
    | cbn [edenot ev ENV ENVr gx bx ax]; pins; lia
    | cbn [edenot ev ENV ENVr gx bx ax]; pins; lia ]
  end.

(* [comment removed for export] *)
Lemma cell_join : forall M a n1 n2 v1 v2 v,
  cell M a n1 v1 -> cell M (a + Z.of_nat n1) n2 v2 ->
  word_to_le_bytes n1 (Z_to_bv 64 v1) ++ word_to_le_bytes n2 (Z_to_bv 64 v2) = word_to_le_bytes (n1 + n2) (Z_to_bv 64 v) ->
  (0 <= a)%Z -> (a + Z.of_nat n1 < 2 ^ 64)%Z -> cell M a (n1 + n2) v.
Proof.
  unfold cell. intros M a n1 n2 v1 v2 v H1 H2 Hw Ha Hn. rewrite <- Hw.
  apply rdn_app; [exact H1|]. rewrite w_add_nat, u_small by lia. exact H2.
Qed.

(* [comment removed for export] *)
Lemma kwr_window : forall E M kn b kk len base,
  know_ok RSEGS E M kn -> kderive RSEGS kn (KWr (SA b kk) len) = true ->
  (bv_unsigned (edenot E b) + kk)%Z = base ->
  forall d m, (0 <= d)%Z -> (d + Z.of_nat m <= len)%Z -> store_ok RSEGS M (Z_to_bv 64 (base + d)) m = true.
Proof.
  intros E M kn b kk len base HK Hd Hb d m H0 Hm.
  destruct (kderive_sound RSEGS E M kn _ HK Hd) as [Hf Hst]. unfold estart in Hst. cbn [a_base a_off] in Hst.
  rewrite Hb in Hst. apply Hst; assumption.
Qed.

(* [comment removed for export] *)
Definition fG (i : nat) : nat :=
  if Nat.eqb i 2 then 73%nat else if Nat.eqb i 3 then 75%nat else if Nat.eqb i 7 then 40%nat else 39%nat.
Definition fT (i : nat) : nat :=
  if Nat.eqb i 2 then 74%nat else if Nat.eqb i 3 then 75%nat else if Nat.eqb i 7 then 40%nat else 39%nat.

(* [comment removed for export] *)
Ltac kreg HR :=
  lazymatch goal with |- getr ?R ?r = _ =>
  lazymatch type of HR with regs_ok ?E ?sr R =>
    let e := eval vm_compute in (sr_get sr r) in
    rewrite (reg_val E sr R r HR); change (sr_get sr r) with e; kside
  end end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section World.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable uid : word.   (* [comment removed for export] *)
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Variable tid : word.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable brk : word.
  Variable mbase : word.
  Variable fs0 : Fs.
  Variable stdin0 : AmbIn.
  Variable fdata : list byte.
  Variable lim : Z.                              (* [comment removed for export] *)
  Hypothesis lim_ge : (LIM <= lim)%Z.
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis Hbrk : valid_brk RSEGS brk.
  Hypothesis Hfile : fs_lookup fs0 path = Some fdata.
  Hypothesis Hpne : path <> [].
  Hypothesis Hplen : (length path <= 4095)%nat.
  (* [comment removed for export] *)
  Variable mode : bool.
  Variable Q : config -> Prop.
  Variable fd3 : FdEntry.      (* [comment removed for export] *)
  Variable SI : (word -> option byte) -> Prop.   (* [comment removed for export] *)
  Hypothesis SI_step : forall M M' : word -> option byte,
    (forall a : word, (bv_unsigned sp0 <= bv_unsigned a)%Z -> M' a = M a) -> SI M -> SI M'.
  (* [comment removed for export] *)
  Hypothesis SI_hi : forall M : word -> option byte, SI M ->
    exists s : Z, (bv_unsigned sp0 + 192 <= s < 2 ^ 47 - 32)%Z /\ (s mod 8 = 0)%Z /\ M (Z_to_bv 64 s) = Some (Z_to_bv 8 0).

  #[local] Notation ENVv := (ENV a0s path rdraw).
  #[local] Notation modelV := (modelV tid fs0 stdin0 fd3).

  (* [comment removed for export] *)
  Definition vm_small (VM : VmMaps) (gm : word) : Prop :=
    vm_reserved VM = segments_reserved RSEGS /\ (LIM <= vm_limit VM)%Z   (* [comment removed for export] *)
    /\ (length (vm_maps VM) <= 4)%nat
    /\ In (gm, Z_to_bv 64 69632) (vm_maps VM)
    /\ Forall (fun p => (0 < bv_unsigned (snd p) <= 69632)%Z /\ (bv_unsigned (fst p) + bv_unsigned (snd p) <= 2 ^ 64)%Z) (vm_maps VM)
    /\ seps (vm_maps VM).

  (* [comment removed for export] *)
  Definition after_malloc (K : TSet) : Prop :=
    forall (R : bvmap 5 word) (M : word -> option byte) (VM : VmMaps) (mb bw gm can sec : word) (area brkv mas : Z),
      area = (bv_unsigned mb + 4096)%Z -> bv_unsigned bw = brkv ->
      read_pre sp0 (p1 sp0 a0s path envv) mb bw gm can sec R M ->
      world0 (bv_unsigned sp0) area (bv_unsigned gm) brkv mas (bv_unsigned tid) (bv_unsigned can) (bv_unsigned sec) M ->
      main_frame (bv_unsigned sp0) M ->
      vm_pre VM sp0 mb bw gm -> vm_small VM gm ->
      GG RSEGS mode Q K (mkCfg (mkst R (Z_to_bv 64 0xe19e0) M (seg_rom RSEGS))
                               (model_pre path VM stdin0 fs0 tid)).

  (* [comment removed for export] *)
  Definition after_malloc_gen (K : TSet) : Prop :=
    forall (R : bvmap 5 word) (M : word -> option byte) (VM : VmMaps) (mb bw gm can sec : word) (area brkv mas : Z),
      area = (bv_unsigned mb + 4096)%Z -> bv_unsigned bw = brkv ->
      read_pre sp0 (p1 sp0 a0s path envv) mb bw gm can sec R M ->
      world0 (bv_unsigned sp0) area (bv_unsigned gm) brkv mas (bv_unsigned tid) (bv_unsigned can) (bv_unsigned sec) M ->
      main_frame (bv_unsigned sp0) M ->
      vm_pre VM sp0 mb bw gm -> vm_small VM gm -> SI M ->
      GG RSEGS mode Q K (mkCfg (mkst R (Z_to_bv 64 0xe19e0) M (seg_rom RSEGS))
                               (mkModelA (fdsV fd3) VM stdin0 fs0 None (Some tid) None)).

  Lemma modelV_eq : forall VM, modelV VM = mkModelA (fdsV fd3) VM stdin0 fs0 None (Some tid) None.
  Proof. intros VM. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma p1_range : (0x7fff80000000 <= bv_unsigned (p1 sp0 a0s path envv) <= 0x800000400000)%Z.
  Proof.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi. unfold sp_window_lo, sp_window_hi in *.
    unfold p1. rewrite (u_cat_argv_ptr sp0 [a0s; path] envv Hva Hve) by (cbn; lia || (unfold sp_window_lo, sp_window_hi; cbn; lia)).
    pose proof (struct_av_bound [a0s; path] envv Hva Hve).
    pose proof (CatExec.total_arg_bytes_firstn_le 1 [a0s; path]). lia.
  Qed.

  Variable K : TSet.

  Lemma w65_exitG : after_malloc_gen K -> exitG_branch sp0 a0s path envv rdraw tid brk fs0 stdin0 mode Q fd3 SI K.
  Proof.
    intros AM vals R M VM HL P0 P2 P70 P5 HR HK HVM HVS HSI.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi. pose proof (proj2 (proj2 Hvsp)) as SPal.
    unfold sp_window_lo, sp_window_hi in *.
    pose proof (proj1 (proj2 (proj2 (proj2 HVS)))) as Gtop.
    pose proof (brk_lo brk Hbrk) as Blo. pose proof (brk_hi path brk Hbrk Hplen) as Bhi. pose proof (brk_al brk Hbrk) as Bal.
    pose proof (know_nth RSEGS _ _ knZ ltac:(let i := kidx knZ (is_krange gx) in exact i) _ HK eq_refl)
      as Kgm; cbn [kentry_ok edenot ev ENV ENVr gx bx ax] in Kgm.
    pose proof (know_nth RSEGS _ _ knZ ltac:(let i := kidx knZ (is_kalign gx) in exact i) _ HK eq_refl)
      as Kga; cbn [kentry_ok edenot ev ENV ENVr gx bx ax] in Kga.
    pose proof (know_nth RSEGS _ _ knZ ltac:(let i := kidx knZ (is_kdisj bx gx) in exact i) _ HK eq_refl)
      as Kgd; cbn [kentry_ok] in Kgd; unfold estart in Kgd; cbn [a_base a_off edenot ev ENV ENVr gx bx ax] in Kgd; rewrite P70 in Kgd.
    pose proof p1_range as P1r.
    pose proof (u64_range brk) as Bu. pose proof (u64_range sp0) as Su.
    rewrite modelV_eq.
    apply (AM R M VM brk (Z_to_bv 64 (bv_unsigned brk + 8192)) (vals_ev vals 75) (vals_ev vals 40) (vals_ev vals 39)
              (bv_unsigned brk + 4096)%Z (bv_unsigned brk + 8192)%Z 0%Z).
    - reflexivity.
    - apply u64_lit. lia.
    - (* [comment removed for export] *)
      constructor.
      + kreg HR.
      + kreg HR.
      + kreg HR.
      + kreg HR.
      + kreg HR.
      + kreg HR.
      + kreg HR.
      + kreg HR.
      + lia.
      + exact P1r.
      + lia.
      + lia.
      + lia.
      + lia.
      + unfold stack_writable. apply (kwr_window (ENVv vals) M knZ (EVar 0) (-8388608) 8388608); [exact HK | vm_compute; reflexivity | cbn [edenot ev ENV ENVr gx bx ax]; pins; lia].
      + unfold group_writable. apply (kwr_window (ENVv vals) M knZ gx 0 69632); [exact HK | vm_compute; reflexivity | cbn [edenot ev ENV ENVr gx bx ax]; pins; lia].
      + unfold meta_writable. apply (kwr_window (ENVv vals) M knZ bx 4096 4096); [exact HK | vm_compute; reflexivity | cbn [edenot ev ENV ENVr gx bx ax]; pins; lia].
      + destruct (errno_some M) as (bs & Hbs & Hlen). exists (Z_to_bv 64 (bytes_le_to_Z bs)).
        rewrite Hbs, word_to_le_bytes_of_lez by (assumption || lia). reflexivity.
      + (* [comment removed for export] *)
        unfold stage_writable. intros d m Hd Hm. unfold STAGE.
        replace (0x31ef09 + d)%Z with (0x31e000 + ((0x31ef09 - 0x31e000) + d))%Z by lia.   (* [comment removed for export] *)
        apply (kwr_window (ENVv vals) M knZ (ELit 0) 0x31e000 0x36000 0x31e000 HK ltac:(vm_compute; reflexivity)
                 ltac:(cbn [edenot ev ENV ENVr gx bx ax]; rewrite ?u0; lia)); lia.
      + intros x0 x1 x4 x5 x6 x9 extra ebs.
        apply (know_ok_ren RSEGS (ENVv vals) _ M fG [2;3;7;8]%nat kn_M1).
        * intros i Hi. destruct Hi as [<-|[<-|[<-|[<-|[]]]]]; cbn [ev ENV fG Nat.eqb vals_ev nth app]; pins; reflexivity.
        * vm_compute. reflexivity.
        * apply (kderive_all_sound RSEGS _ M knZ); [exact HK | vm_compute; reflexivity].
    - (* [comment removed for export] *)
      constructor.
      all: try kcell HK.
      all: try kzero HK.
      + apply (cell_join M _ 4 4 101 0); [kcell HK | kcell HK | reflexivity | lia | lia].
      + apply (cell_join M _ 4 4 0 0); [kcell HK | kcell HK | reflexivity | lia | lia].
      + kdef HK bx 4096%Z 4096%Z.
      + (* [comment removed for export] *)
        constructor; cbn zeta.
        * kbyte HK.
        * kbyte HK.
        * krdn HK.
        * intros _. kbyte HK.
        * intros _. kbyte HK.
        * intros _. krdn HK.
        * intros _. kbyte HK.
        * intros _. krdn HK.
        * change (69616 * 0 / 16 + 1)%Z with 1%Z. lia.
      + kdef HK gx 0%Z 69632%Z.
      + replace (bv_unsigned brk + 4096)%Z with (bv_unsigned brk + 1 * 4096)%Z by lia. rewrite Z_mod_plus_full. exact Bal.
      + exact (proj2 Kga).
      + lia.
      + lia.
      + lia.
      + lia.
      + lia.
      + lia.
      + lia.
      + exact Htid.
      + destruct (errno_some M) as (bs & Hbs & Hlen). exists (bytes_le_to_Z bs).
        pose proof (SX2S.bytes_le_to_Z_bound bs) as Hb. rewrite Hlen in Hb.
        split; [cbn in Hb; lia|]. unfold cell. rewrite Hbs, word_to_le_bytes_of_lez by (assumption || lia). reflexivity.
      + apply (img_clear_of_know (ENVv vals)). apply (kderive_all_sound RSEGS _ M knZ); [exact HK | vm_compute; reflexivity].
      + (* [comment removed for export] *) left. split; [lia | reflexivity].
    - (* [comment removed for export] *)
      constructor; [kcell HK .. | exact (SI_hi M HSI)].     (* [comment removed for export] *)
    - exact HVM.
    - (* [comment removed for export] *)
      destruct HVS as (Hr & Hl & Hsp & Gt & Hm). unfold vm_small. rewrite Hr.
      split; [reflexivity|]. split; [exact Hl|].   (* [comment removed for export] *)
      assert (U1 : bv_unsigned (Z_to_bv 64 69632) = 69632%Z) by reflexivity.
      assert (U2 : bv_unsigned (Z_to_bv 64 8192) = 8192%Z) by reflexivity.
      assert (U3 : bv_unsigned (Z_to_bv 64 4096) = 4096%Z) by reflexivity.
      destruct Hm as [[-> Hdj] | [-> Hdj]]; cbn [length In fst snd];
        (split; [lia|]); (split; [left; reflexivity|]); split;
        [ repeat constructor; cbn [fst snd]; rewrite ?U1, ?U2, ?U3, ?u64_lit' by lia; lia
        | apply seps_cons; [constructor; [unfold iv_disjoint; cbn [fst snd]; rewrite ?U1, ?U2, ?U3, ?u64_lit' by lia; lia | constructor]
                          | apply seps_cons; [constructor | apply seps_nil]]
        | repeat constructor; cbn [fst snd]; rewrite ?U1, ?U2, ?U3, ?u64_lit' by lia; lia
        | apply seps_cons; [constructor; [unfold iv_disjoint; cbn [fst snd]; rewrite ?U1, ?U2, ?U3, ?u64_lit' by lia; lia | constructor]
                          | apply seps_cons; [constructor | apply seps_nil]] ].
    - exact HSI.
  Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Theorem brk_ok_semV : after_malloc_gen K ->
    brk_ok_entry sp0 a0s path envv rdraw tid brk mbase fs0 stdin0 lim mode Q fd3 SI K.   (* [comment removed for export] *)
  Proof. intros AM. apply brk_ok_worldV; try assumption. apply w65_exitG, AM. Qed.

End World.

(* [comment removed for export] *)
Theorem brk_ok_sem_g sp0 a0s path envv rdraw tid mem0 brk mbase fs0 stdin0 lim   (* [comment removed for export] *)
  (lim_ge : (LIM <= lim)%Z)
  (Hva : valid_argv [a0s; path]) (Hve : valid_envp envv)
  (Hvsp : valid_sp sp0) (Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z) (Hbrk : valid_brk RSEGS brk)
  (Hplen : (length path <= 4095)%nat)
  (* [comment removed for export] *)
  (Hhi0 : exists s : Z, (bv_unsigned sp0 + 192 <= s < 2 ^ 47 - 32)%Z /\ (s mod 8 = 0)%Z /\ mem0 (Z_to_bv 64 s) = Some (Z_to_bv 8 0))
  mode Q fd3 K :
  after_malloc_gen sp0 a0s path envv tid fs0 stdin0 mode Q fd3 (above_eq sp0 mem0) K ->
  brk_ok_branch_G sp0 a0s path envv rdraw tid mem0 brk mbase fs0 stdin0 lim mode Q fd3 K.
Proof.
  intros AM.
  assert (SIhi : forall M : word -> option byte, above_eq sp0 mem0 M ->
            exists s : Z, (bv_unsigned sp0 + 192 <= s < 2 ^ 47 - 32)%Z /\ (s mod 8 = 0)%Z /\ M (Z_to_bv 64 s) = Some (Z_to_bv 8 0)).
  { intros M HA. destruct Hhi0 as (s & Hs & Hs8 & Hz). exists s. split; [exact Hs|]. split; [exact Hs8|].
    pose proof (u64_range sp0) as Us. rewrite (HA (Z_to_bv 64 s)); [exact Hz|]. rewrite u64_lit by lia. lia. }
  exact (brk_ok_semV sp0 a0s path envv rdraw tid mem0 brk mbase fs0 stdin0 lim lim_ge Hva Hve Hvsp Htid Hbrk Hplen mode Q fd3
                      (above_eq sp0 mem0) (above_eq_step sp0 mem0) SIhi K AM).
Qed.


(* [comment removed for export] *)
Theorem brk_ok_sem sp0 a0s path envv rdraw tid mem0 brk mbase fs0 stdin0 lim   (* [comment removed for export] *)
  (lim_ge : (LIM <= lim)%Z)
  (Hva : valid_argv [a0s; path]) (Hve : valid_envp envv)
  (Hvsp : valid_sp sp0) (Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z) (Hbrk : valid_brk RSEGS brk)
  (Hplen : (length path <= 4095)%nat)
  (Hhi0 : exists s : Z, (bv_unsigned sp0 + 192 <= s < 2 ^ 47 - 32)%Z /\ (s mod 8 = 0)%Z /\ mem0 (Z_to_bv 64 s) = Some (Z_to_bv 8 0))   (* [comment removed for export] *)
  mode Q K :
  after_malloc sp0 a0s path envv tid fs0 stdin0 mode Q K ->
  brk_ok_branch_M sp0 a0s path envv rdraw tid mem0 brk mbase fs0 stdin0 lim mode Q K.
Proof.
  intros AM. apply (brk_ok_sem_g sp0 a0s path envv rdraw tid mem0 brk mbase fs0 stdin0 lim lim_ge Hva Hve Hvsp Htid Hbrk Hplen Hhi0).
  intros R M VM mb bw gm can sec area brkv mas EA EB RP W MF VP VS _. exact (AM R M VM mb bw gm can sec area brkv mas EA EB RP W MF VP VS).
Qed.

