(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ModelAmb.
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Prelude Instr.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgU.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import UbStartupDefs.   (* [comment removed for export] *)
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require PropExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX RefMemcpyLib UbMainEntry UbLibStdioCall UbPilotOOM_defs.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require SymXfer.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require DispatchCompute.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg ShapeLaws Nodes MmapSim AllocSim FileSim AgentLib SpecConsts SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame UbLibStdioCall Spec LibWritev RefNodes UbExitBase UbStdioDefs UbExit RefMemcpyLib UbStartup UbMainEntry Hoare Frame MallocDefs UbEnframeBase UbEnframe UbReadBase.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require UbPilotOOM_defs UbPilotOOM.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require SymXfer SymAbove RefAbove.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg ShapeLaws Nodes MmapSim AllocSim FileSim AgentLib SpecConsts SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame UbLibStdioCall Spec LibWritev RefNodes UbExitBase UbStdioDefs UbExit RefMemcpyLib UbStartup UbMainEntry Hoare Frame MallocDefs RefEnframeArith UbEnframeBase UbEnframe UbReadBase.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg Nodes MmapSim AllocSim FileSim AgentLib SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX Spec LibWritev RefNodes UbExitBase UbExit RefMemcpyLib RefLayout UbStartup UbMainEntry Hoare Frame MallocDefs UbEnframeBase UbEnframe UbReadBase UbWorld UbTargetPre.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LiaFast LiaTier.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac Lia.lia ::= lia_fast2.

(* [comment removed for export] *)
Module RefW65_defs.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.PropExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymExec2 OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymExec2Sound OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymRun OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymDrive OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymDriveX OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.UbMainEntry OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.UbLibStdioCall OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.UbPilotOOM_defs.
Import OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymXfer.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import ListNotations. Import SX2. Import SX2S.

(* [comment removed for export] *)
Section FPW_1. Context {fx : PropExec.FPState}.

Definition STOPS_W : list Z := 0x99294%Z :: STOPS.
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
Definition rW1 := Eval vm_compute in run scr0 (SS 0x99274 srW0 [] knW0 71).
Definition srW1 : list expr := Eval vm_compute in s_regs (fst (fst rW1)).
Definition knW1 : list kentry := Eval vm_compute in kn_after rW1 knW0.

(* [comment removed for export] *)
Definition ENOMEMv : expr := ELit (2 ^ 64 - 12).
Definition srK0 := Eval vm_compute in sr_upd srW1 (ridx 10) ENOMEMv.
Definition rK := Eval vm_compute in runW scr0 (SS 0x9a8e8 srK0 [] knW1 71).
Definition srK1 : list expr := Eval vm_compute in s_regs (fst (fst rK)).
Definition knK1 : list kentry := Eval vm_compute in kn_after rK knW1.

Definition knU : list kentry := Eval vm_compute in kn_xfer knW1 bx 0 4096 false.
Definition srO0 := Eval vm_compute in sr_upd srW1 (ridx 10) bx.
Definition rO := Eval vm_compute in runW scr0 (SS 0x9a8e8 srO0 [] knU 71).
Definition srO1 : list expr := Eval vm_compute in s_regs (fst (fst rO)).
Definition knO1 : list kentry := Eval vm_compute in kn_after rO knU.

Definition rDd := Eval vm_compute in runW scr0 (SS 0x9a8e8 srK0 [] knU 71).
Definition srDd1 : list expr := Eval vm_compute in s_regs (fst (fst rDd)).
Definition knDd1 : list kentry := Eval vm_compute in kn_after rDd knU.


(* [comment removed for export] *)
Definition kn_inter3 (k1 k2 k3 : list kentry) : list kentry :=
  List.filter (fun K => existsb (kentry_eqb K) k2 && existsb (kentry_eqb K) k3) k1.
Definition srM : list expr := Eval vm_compute in sr_upd srO1 (ridx 10) (EVar 71).
Definition knM : list kentry := Eval vm_compute in kn_inter3 knO1 knK1 knDd1.

(* [comment removed for export] *)
Definition rW2 := Eval vm_compute in run scr0 (SS 0x99294 srM [] knM 72).
Definition srW2 : list expr := Eval vm_compute in s_regs (fst (fst rW2)).
Definition knW2 : list kentry := Eval vm_compute in kn_after rW2 knM.


(* [comment removed for export] *)
Definition srN0 : list expr := Eval vm_compute in sr_upd srW2 (ridx 10) ENOMEMv.
Definition rN := Eval vm_compute in run scr0 (SS 0x9a8e8 srN0 [] knW2 72).
Definition srN : list expr := Eval vm_compute in s_regs (fst (fst rN)).
Definition knN : list kentry := Eval vm_compute in kn_after rN knW2.
(* [comment removed for export] *)
Definition resX : stdio_res := Eval vm_compute in sc_of (stdio_call 72 srN knN).
#[using="Type"] Lemma resX_eq : stdio_call 72 srN knN = Some resX.  Proof. vm_compute. reflexivity. Qed.
Definition srX0 : list expr := Eval vm_compute in sc_sr resX.
Definition knX0 : list kentry := Eval vm_compute in sc_kn resX.
Definition rX := Eval vm_compute in run scr0 (SS 0x9bfcc srX0 [] knX0 104).
Definition srX : list expr := Eval vm_compute in s_regs (fst (fst rX)).
Definition knX : list kentry := Eval vm_compute in kn_after rX knX0.

(* [comment removed for export] *)
Definition gx : expr := EVar 72.
(* [comment removed for export] *)
Definition knG00 : list kentry :=   (* [comment removed for export] *)
  KAlign gx 4096 :: KRange gx 0xe6000 (0x7fffff800000 - 69632) :: KDisj (SA (EVar 0) (-8388608)) 281474976710656 (SA gx 0) 69632
  :: KDisj (SA bx 4096) 4096 (SA gx 0) 69632 :: knW2.
Definition knG0 : list kentry := Eval vm_compute in
  (KZero (SA gx 0) (ELit 69632) :: KWr (SA gx 0) 69632 :: kn_xfer knG00 gx 0 69632 true).
Definition srG0 : list expr := Eval vm_compute in sr_upd srW2 (ridx 10) gx.
Definition scrG : scripts := SCR [true] [] [].   (* [comment removed for export] *)
Definition rG := Eval vm_compute in run scrG (SS 0x9a8e8 srG0 [] knG0 73).
Definition srG : list expr := Eval vm_compute in s_regs (fst (fst rG)).
Definition knG : list kentry := Eval vm_compute in kn_after rG knG0.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ax : expr := EVar 71.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition knP00 : list kentry :=   (* [comment removed for export] *)
  KAlign ax 4096 :: KRange ax 0x1000 (0x7fffff800000 - 8192) :: KDisj (SA (EVar 0) (-8388608)) 281474976710656 (SA ax 0) 8192
  :: KDisj (SA (ELit 0) 0x10000) 0xd6000 (SA ax 0) 8192 :: knE.
Definition knP0 : list kentry := Eval vm_compute in kn_xfer knP00 ax 0 8192 false.
Definition srP0 : list expr := Eval vm_compute in sr_upd srE (ridx 10) ax.
Definition scrP : scripts := SCR [true] [] [].   (* [comment removed for export] *)
Definition rP := Eval vm_compute in run scrP (SS 0x9a8e8 srP0 [] knP0 72).
Definition srP : list expr := Eval vm_compute in s_regs (fst (fst rP)).
Definition knP : list kentry := Eval vm_compute in kn_after rP knP0.

(* [comment removed for export] *)
Definition srQ0 : list expr := Eval vm_compute in sr_upd srP (ridx 10) ENOMEMv.
Definition rQ := Eval vm_compute in run scr0 (SS 0x9a940 srQ0 [] knP 72).
Definition srQ : list expr := Eval vm_compute in s_regs (fst (fst rQ)).
Definition knQ : list kentry := Eval vm_compute in kn_after rQ knP.
Definition resQX : stdio_res := Eval vm_compute in sc_of (stdio_call 72 srQ knQ).
#[using="Type"] Lemma resQX_eq : stdio_call 72 srQ knQ = Some resQX.  Proof. vm_compute. reflexivity. Qed.
Definition srQX0 : list expr := Eval vm_compute in sc_sr resQX.
Definition knQX0 : list kentry := Eval vm_compute in sc_kn resQX.
Definition rQX := Eval vm_compute in run scr0 (SS 0x9bfcc srQX0 [] knQX0 104).
Definition srQX : list expr := Eval vm_compute in s_regs (fst (fst rQX)).
Definition knQX : list kentry := Eval vm_compute in kn_after rQX knQX0.

(* [comment removed for export] *)
Definition knR0 : list kentry := Eval vm_compute in
  (KZero (SA ax 4096) (ELit 4096) :: KWr (SA ax 4096) 4096 :: kn_xfer knP ax 4096 4096 true).
Definition srR0 : list expr := Eval vm_compute in sr_upd srP (ridx 10) (ELit 0).
Definition rR := Eval vm_compute in run scr0 (SS 0x9a940 srR0 [] knR0 72).
Definition srR : list expr := Eval vm_compute in s_regs (fst (fst rR)).
Definition knR : list kentry := Eval vm_compute in kn_after rR knR0.

(* [comment removed for export] *)
Definition srS0 : list expr := Eval vm_compute in sr_upd srR (ridx 10) ENOMEMv.
Definition rS := Eval vm_compute in run scr0 (SS 0x9a8e8 srS0 [] knR 72).
Definition srS : list expr := Eval vm_compute in s_regs (fst (fst rS)).
Definition knS : list kentry := Eval vm_compute in kn_after rS knR.
Definition resSX : stdio_res := Eval vm_compute in sc_of (stdio_call 72 srS knS).
#[using="Type"] Lemma resSX_eq : stdio_call 72 srS knS = Some resSX.  Proof. vm_compute. reflexivity. Qed.
Definition srSX0 : list expr := Eval vm_compute in sc_sr resSX.
Definition knSX0 : list kentry := Eval vm_compute in sc_kn resSX.
Definition rSX := Eval vm_compute in run scr0 (SS 0x9bfcc srSX0 [] knSX0 104).
Definition srSX : list expr := Eval vm_compute in s_regs (fst (fst rSX)).
Definition knSX : list kentry := Eval vm_compute in kn_after rSX knSX0.

(* [comment removed for export] *)
Definition knT00 : list kentry :=   (* [comment removed for export] *)
  KAlign gx 4096 :: KRange gx 0xe6000 (0x7fffff800000 - 69632) :: KDisj (SA (EVar 0) (-8388608)) 281474976710656 (SA gx 0) 69632
  :: KDisj (SA ax 0) 8192 (SA gx 0) 69632 :: knR.
Definition knT0 : list kentry := Eval vm_compute in
  (KZero (SA gx 0) (ELit 69632) :: KWr (SA gx 0) 69632 :: kn_xfer knT00 gx 0 69632 true).
Definition srT0 : list expr := Eval vm_compute in sr_upd srR (ridx 10) gx.
Definition rT := Eval vm_compute in run scrG (SS 0x9a8e8 srT0 [] knT0 73).
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
#[using="Type"] Lemma itinerary_w65 :
  (s_pc (fst (fst rW1)), snd (fst rW1)) = (0x9a8e4%Z, [])
  /\ (s_pc (fst (fst rK)), snd (fst rK)) = (0x99294%Z, [])
  /\ (s_pc (fst (fst rO)), snd (fst rO)) = (0x99294%Z, [])
  /\ (s_pc (fst (fst rDd)), snd (fst rDd)) = (0x99294%Z, [])
  /\ (s_pc (fst (fst rW2)), snd (fst rW2)) = (0x9a8e4%Z, [])
  /\ (s_pc (fst (fst rN)), snd (fst rN)) = (0x9c12c%Z, [])
  /\ (sc_ret resX, sc_f resX, sc_fd resX) = (0x9bfcc%Z, 0xb3398%Z, 2%Z)
  /\ (s_pc (fst (fst rX)), snd (fst rX)) = (0x9678c%Z, [])
  /\ (s_pc (fst (fst rG)), snd (fst rG)) = (0x99ff4%Z, [SCBr true BC_NE (EAlu ALU_XOR gx (ELit (-1))) (ELit 0)])
  /\ (s_pc (fst (fst rP)), snd (fst rP)) = (0x9a93c%Z, [SCBr true BC_NE (EAlu ALU_XOR ax (ELit (-1))) (ELit 0)])
  /\ (s_pc (fst (fst rQ)), snd (fst rQ)) = (0x9c12c%Z, [])
  /\ (sc_ret resQX, sc_f resQX, sc_fd resQX) = (0x9bfcc%Z, 0xb3398%Z, 2%Z)
  /\ (s_pc (fst (fst rQX)), snd (fst rQX)) = (0x9678c%Z, [])
  /\ (s_pc (fst (fst rR)), snd (fst rR)) = (0x9a8e4%Z, [])
  /\ (s_pc (fst (fst rS)), snd (fst rS)) = (0x9c12c%Z, [])
  /\ (sc_ret resSX, sc_f resSX, sc_fd resSX) = (0x9bfcc%Z, 0xb3398%Z, 2%Z)
  /\ (s_pc (fst (fst rSX)), snd (fst rSX)) = (0x9678c%Z, [])
  /\ (s_pc (fst (fst rT)), snd (fst rT)) = (0x99ff4%Z, [SCBr true BC_NE (EAlu ALU_XOR gx (ELit (-1))) (ELit 0)]).
Proof. vm_compute. repeat split; reflexivity. Qed.

#[using="Type"] Lemma carry_LOGE_ok : snd (fst (carry LOGE knG [])) = [] /\ snd (fst (carry LOGE knT [])) = [].
Proof. vm_compute. split; reflexivity. Qed.
End FPW_1.

End RefW65_defs.

(* [comment removed for export] *)
Module RefW65.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs.
Import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.DispatchCompute.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.PropExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.CatExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.CatSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SeqExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.StoreOk OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SimInv OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.ExitSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.ShapeAlg OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.ShapeLaws OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.Nodes OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.MmapSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.AllocSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.FileSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.AgentLib OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SpecConsts OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymExec2 OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymExec2Sound OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymRun OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymDrive OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymDriveX OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.LibKnowFrame OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.UbLibStdioCall OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.Spec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.LibWritev OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefNodes OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.UbExitBase OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.UbStdioDefs OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.UbExit OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.UbStartup OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.UbMainEntry OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.Hoare OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.Frame OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.MallocDefs OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.UbEnframeBase OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.UbEnframe OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.UbReadBase.
Import OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.UbPilotOOM_defs OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.UbPilotOOM.
Import OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymXfer OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymAbove OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefAbove RefW65_defs.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Tactic Notation "run_block" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX false.
Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX true.
Tactic Notation "run_blockW" constr(scr) constr(NX) := run_block_gen FUEL STOPS_W scr NX false.
Tactic Notation "run_blockW_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPS_W scr NX true.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section FPW_2. Context {fx : PropExec.FPState}.

#[using="Type"] Lemma bt_ne_not : forall (x : word), (bv_unsigned x < 2 ^ 64 - 1)%Z ->
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
#[using="Type"] Lemma regs_ok_set_have : forall E sr R (rd : reg) v e,
  regs_ok E sr R -> getr R rd = v -> edenot E e = v -> rd <> 0%bv ->
  regs_ok E (sr_upd sr (ridx rd) e) R.
Proof.
  intros E sr R rd v e HR Hv He Hrd r.
  pose proof (regs_ok_set E sr R rd v e HR Hrd He r) as H.
  rewrite <- H. destruct (decide (r = rd)) as [->|Hne].
  - rewrite getr_same by exact Hrd. exact Hv.
  - rewrite getr_other by exact Hne. reflexivity.
Qed.

#[using="Type"] Lemma callee_saved_no0 : ~ In (0%bv : reg) callee_saved.
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
End FPW_2.

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
    exists (Z_to_bv 64 (bv_unsigned sp0 - 128)), (Z_to_bv 64 0xc5018), (bv_unsigned (ev E 5)),   (* [comment removed for export] *)
           (Z_to_bv 64 0xe5800), (Z_to_bv 64 0);
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
      | lit_u; change (806936 - 168)%Z with 0xc4f70%Z;
        krd HK 0xc4f70%Z 4%nat Htc; rewrite Htc; cbn [ev];
        rewrite ext_val_zx_id by (change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z; cbn [ev] in Ktid; lia);
        rewrite Z_to_bv_bv_unsigned; reflexivity
      | krd_solve HK
      | krd_solve HK
      | krd_solve HK
      | krd_solve HK
      | krd_solve HK
      | krd_solve HK
      | krd_solve HK
      | krd_solve HK | krd_solve HK | krd_solve HK   (* [comment removed for export] *)
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
      | cbn [edenot]; lit_u; lia     (* [comment removed for export] *)
      | cbn [edenot]; lia
      | cbn [edenot]; lit_u; reflexivity
      | pose proof rw_bytes_max_ge17; lia
      | lia
      | left; rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev]; rewrite P0;
        rewrite (u_small (bv_unsigned _ + _)) by lia; lit_u; lia
      | left; rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev]; rewrite P0;
        rewrite (u_small (bv_unsigned _ + _)) by lia; lit_u; lia
      | cbn [edenot]; lit_u; lia
      | reflexivity
      | cbn [edenot]; change (length msg_oom) with 19%nat;
        rewrite (kimg_rdn RSEGS E _ kn ltac:(let i := kidx kn (is_kimg_cov 0x10c42 19) in exact i)
                   _ _ 0x10c42 19 HK eq_refl) by (cbn; lia);
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
Section FPW_3. Context {fx : PropExec.FPState}.


Section World.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable uid : word.   (* [comment removed for export] *)
  Variable hw : word.    (* [comment removed for export] *)
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Variable tid : word.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable brk : word.
  Variable mbase : word.
  Variable fs0 : Fs.
  Variable stdin0 : AmbIn.
  Variable fdata : list byte.
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 [a0s; path] envv uid hw rdraw tid regs0 mem0.
  Hypothesis Hbrk : valid_brk RSEGS brk.
  Hypothesis Hfile : fs_lookup fs0 path = Some fdata.
  Hypothesis Hpne : path <> [].
  Hypothesis Hpns : path_has_slash path = false.   (* [comment removed for export] *)
  Hypothesis Hpnd : path_is_dirref path = false.   (* [comment removed for export] *)
  Hypothesis Hplen : (length path <= 4095)%nat.
  (* [comment removed for export] *)
  Variable fd3 : FdEntry.
  (* [comment removed for export] *)
  Variable SI : (word -> option byte) -> Prop.
  Hypothesis SI_step : forall M M' : word -> option byte,
    (forall a : word, (bv_unsigned sp0 <= bv_unsigned a)%Z -> M' a = M a) -> SI M -> SI M'.

  #[local] Notation ENVv := (ENV a0s path).
  (* [comment removed for export] *)
  #[local] Notation RES := (segments_reserved RSEGS).

  (* [comment removed for export] *)
  Ltac si_block HSI Rn Mn :=
    lazymatch goal with
    | EQM : ?M' = mem_denot ?E ?Mo ?log, HK : know_ok ?segs ?E ?M' ?kn, HR : regs_ok ?E _ ?R' |- _ =>
        let H := fresh "HSI" in
        assert (H : SI M');
        [ apply (SI_step Mo M'); [| exact HSI]; intros xa Hxa; rewrite EQM;
          apply (mem_denot_above_kd segs E M' Mo kn log 0%nat 0xe6000 xa HK);   (* [comment removed for export] *)
          [ vm_compute; reflexivity | cbn [ev ENV]; pins; lia | cbn [ev ENV]; pins; lia | lia ]
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

  #[using="Type"] Lemma fdsV_2 : fd_lookup fdsV (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
  Proof. reflexivity. Qed.
  (* [comment removed for export] *)
  #[using="Type"] Lemma mV_vmmaps : forall VM, m_vmmaps (modelV VM) = VM.  Proof. reflexivity. Qed.
  #[using="Type"] Lemma mV_fs : forall VM, m_fs (modelV VM) = fs0.  Proof. reflexivity. Qed.
  #[using="Type"] Lemma mV_fds : forall VM, m_fds (modelV VM) = fdsV.  Proof. reflexivity. Qed.
  #[using="Type"] Lemma mV_fd2 : forall VM, fd_lookup (m_fds (modelV VM)) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
  Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition model1V : Model := mkModelA fdsV (mkVmMapsFull RES [] [] brk brk LIM mbase sp0) stdin0 fs0 None (Some tid) None.

  Definition brk_ok_entry (KB : TSet) : Prop :=
    forall vals R M,
      length vals = 71%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 70 = brk ->
      vals_ev vals 1 = p0 sp0 a0s path envv -> vals_ev vals 2 = p1 sp0 a0s path envv ->
      vals_ev vals 5 = tid -> vals_ev vals 6 = canary_w rdraw -> vals_ev vals 7 = secret_w rdraw ->
      regs_ok (ENVv vals) srD2 R -> know_ok RSEGS (ENVv vals) M knD2 -> SI M ->
      realizes RSEGS
        (mkCfg (mkst (regupd R 10 (Z_to_bv 64 (bv_unsigned brk + 8192))) (Z_to_bv 64 0x99274)
                     (zfill brk (Z_to_bv 64 8192) M) (seg_rom RSEGS))
               (mkModelA fdsV (mkVmMapsFull RES [(brk, Z_to_bv 64 8192)] [] brk
                                            (Z_to_bv 64 (bv_unsigned brk + 8192)) LIM mbase sp0)
                        stdin0 fs0 None (Some tid) None)) KB.

  Definition mmap_ok_entry (KB : TSet) : Prop :=
    forall vals R M (a : word),
      length vals = 71%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 70 = brk ->
      vals_ev vals 1 = p0 sp0 a0s path envv -> vals_ev vals 2 = p1 sp0 a0s path envv ->
      vals_ev vals 5 = tid -> vals_ev vals 6 = canary_w rdraw -> vals_ev vals 7 = secret_w rdraw ->
      regs_ok (ENVv vals) srE R -> know_ok RSEGS (ENVv vals) M knE -> SI M ->
      grant_ok_na_pin model1V a 8192 = true ->   (* [comment removed for export] *)
      realizes RSEGS (mkCfg (mkst (regupd R 10 a) (Z_to_bv 64 0x9a8e8)
                                    (unfill a (Z_to_bv 64 8192) M) (seg_rom RSEGS))
                              (noaccess_model a (Z_to_bv 64 8192) model1V)) KB.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="Hvsp Hplen"] Lemma w65_oomN : forall vals R M VM,
    length vals = 72%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENVv vals) srN0 R -> know_ok RSEGS (ENVv vals) M knW2 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x9a8e8) M (seg_rom RSEGS)) (modelV VM)) (t_die msg_oom fs0).
  Proof.
    intros vals R M VM HL P0 HR HK.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi.
    unfold sp_window_lo, sp_window_hi in *.
    run_block scr0 72%nat.
    oom_stdio_exit HL P0 resX_eq (mV_fd2 VM) (mV_fs VM).
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Variable K : TSet.

  (* [comment removed for export] *)
(* [comment removed for export] *)
  Definition w65_vm (VM : VmMaps) (mb gm : word) : Prop :=
    vm_reserved VM = RES /\ vm_limit VM = LIM /\
    ((vm_maps VM = [(gm, Z_to_bv 64 69632); (mb, Z_to_bv 64 8192)]
      /\ (bv_unsigned gm + 69632 <= bv_unsigned mb \/ bv_unsigned mb + 8192 <= bv_unsigned gm)%Z)
     \/ (vm_maps VM = [(gm, Z_to_bv 64 69632); (Z_to_bv 64 (bv_unsigned mb + 4096), Z_to_bv 64 4096)]
      /\ (bv_unsigned gm + 69632 <= bv_unsigned mb + 4096 \/ bv_unsigned mb + 8192 <= bv_unsigned gm)%Z)).

  Definition exitG_branch : Prop :=
    forall vals R M VM,
      length vals = 105%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = p1 sp0 a0s path envv ->
      vals_ev vals 70 = brk -> vals_ev vals 5 = tid -> vals_ev vals 6 = canary_w rdraw -> vals_ev vals 7 = secret_w rdraw ->
      regs_ok (ENVv vals) srZ R -> know_ok RSEGS (ENVv vals) M knZ ->
      vm_pre VM sp0 brk (vals_ev vals 72) -> w65_vm VM brk (vals_ev vals 72) -> SI M ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x32688) M (seg_rom RSEGS)) (modelV VM)) K.

  #[using="Hvsp Hbrk Hplen SI_step"] Lemma w65_G : forall vals R M VM,
    exitG_branch ->
    length vals = 73%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = p1 sp0 a0s path envv ->
    vals_ev vals 70 = brk -> vals_ev vals 5 = tid -> vals_ev vals 6 = canary_w rdraw -> vals_ev vals 7 = secret_w rdraw ->
    regs_ok (ENVv vals) srG0 R -> know_ok RSEGS (ENVv vals) M knG0 ->
    vm_pre VM sp0 brk (vals_ev vals 72) -> w65_vm VM brk (vals_ev vals 72) -> SI M ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x9a8e8) M (seg_rom RSEGS)) (modelV VM)) K.
  Proof.
    intros vals R M VM EXIT HL P0 P2 P70 P5 P6 P7 HR HK HVM HVS HSI.
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
    pose proof (know_nth RSEGS _ _ knG0 ltac:(let i := kidx knG0 (is_kdisj (EVar 0) gx) in exact i) _ HK eq_refl)   (* [comment removed for export] *)
      as Kgs; cbn [kentry_ok] in Kgs; unfold estart in Kgs; cbn [a_base a_off edenot ev ENV] in Kgs; rewrite P0 in Kgs.
    set (gm := vals_ev vals 72) in *.
    (* [comment removed for export] *)
    run_block_keep scrG 73%nat.
    { unfold sc_denot. cbn [edenot ev ENV]. apply bt_ne_not. subst gm. lia. }
    si_block HSI R M.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ ?E ?MG ?kn =>
      krdv HK 70%nat 4136%Z 8%nat Hmem; [apply flat_intro; cbn [edenot ev ENV]; rewrite ?P70; lia|];
      krdv HK 70%nat 4152%Z 8%nat Hmw; [apply flat_intro; cbn [edenot ev ENV]; rewrite ?P70; lia|];
      pose proof (know_nth RSEGS _ _ kn ltac:(let i := kidx kn (is_kzero_cov gx 9 8) in exact i) _ HK eq_refl) as Kz;
      cbn [kentry_ok] in Kz; unfold elenZ, estart in Kz; cbn [a_base a_off edenot ev ENV] in Kz;
      pose proof (kwr_store_ok RSEGS E _ kn ltac:(let i := kidx kn (is_kwr_cov gx 13 69615) in exact i)
                    _ _ _ 13 (Z.to_nat 69615) HK eq_refl ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as Hok;
      pose proof (know_nth RSEGS _ _ kn ltac:(let i := kidx kn (is_kimg_cov 109512 96) in exact i) _ HK eq_refl) as Kimg;
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
    assert (RT : Hoare.ret_ok (Z_to_bv 64 0x32688)) by (apply bv_eq; vm_compute; reflexivity).
    assert (G1 : getr R 1 = Z_to_bv 64 0x32688) by (regv HR (1:reg); reflexivity).
    assert (G10 : getr R 10 = Z_to_bv 64 (bv_unsigned brk + 4120)).
    { regv HR (10:reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV].
      rewrite P70. reflexivity. }
    assert (G11 : getr R 11 = Z_to_bv 64 0) by (regv HR (11:reg); reflexivity).
    assert (G12 : getr R 12 = Z_to_bv 64 65536) by (regv HR (12:reg); reflexivity).
    assert (G13 : getr R 13 = Z_to_bv 64 1) by (regv HR (13:reg); reflexivity).
    destruct (enframe_run M (Z_to_bv 64 1) _ _ _ _ _ _ _ _ _ _ EF R (seg_rom RSEGS) (Z_to_bv 64 0x32688)
                G1 RT G10 G11 G12 G13) as (R2 & Hms & Hkeep & HA0).
    clear RT G1 G10 G11 G12 G13.
    replace (Z_to_bv 64 630772) with (0x99ff4 : word) by (apply bv_eq; vm_compute; reflexivity).
    eapply rz_msteps; [reflexivity | reflexivity | exact Hms |]. clear Hms.
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
      apply (mem_denot_above_kd RSEGS (ENVv vals) _ M knZ LOGE 0%nat 0xe6000 xa HK2);
        [vm_compute; reflexivity | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia | lia]. }
    (* [comment removed for export] *)
    lazymatch type of HR with regs_ok _ ?sr _ =>
      pose proof (regs_after_keeps vals _ sr R R2 callee_saved ltac:(rewrite HL; vm_compute; reflexivity)
                    HR Hkeep callee_saved_no0) as HR2 end.
    rewrite HL in HR2. clear HR.
    set (vals2 := vals ++ junk_vals R2) in *.
    assert (HL2 : length vals2 = 105%nat) by (subst vals2; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (Q2 : vals_ev vals2 2 = p1 sp0 a0s path envv) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P2).
    assert (Q70 : vals_ev vals2 70 = brk) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P70).
    assert (Q5 : vals_ev vals2 5 = tid) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P5).
    assert (Q6 : vals_ev vals2 6 = canary_w rdraw) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P6).
    assert (Q7 : vals_ev vals2 7 = secret_w rdraw) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P7).
    assert (Q72 : vals_ev vals2 72 = gm) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); reflexivity).
    change (Env (vals_ev vals2) (blobs_ev (blobs0 a0s path))) with (ENVv vals2) in HR2.
    pose proof (regs_ok_set_have (ENVv vals2) _ R2 10 _ (EAlu ALU_ADD gx (ELit 32)) HR2 HA0
                  ltac:(rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot gx ev ENV];
                        rewrite Q72; f_equal; lia) ltac:(discriminate)) as HR3.
    clear HR2.
    lazymatch type of HR3 with regs_ok _ ?sr _ => replace sr with srZ in HR3 by (vm_compute; reflexivity) end.
    lazymatch type of HK2 with know_ok _ _ ?Mc ?kn =>
      pose proof (env_app_know RSEGS vals (junk_vals R2) _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK3 end.
    clear HK2 HK.
    change (Env (vals_ev (vals ++ junk_vals R2)) (blobs_ev (blobs0 a0s path))) with (ENVv vals2) in HK3.
    change (mem_denot (Env (vals_ev vals) (blobs_ev (blobs0 a0s path))) M LOGE) with (mem_denot (ENVv vals) M LOGE) in HSI2.
    apply (EXIT vals2 R2 _ VM HL2 Q0 Q2 Q70 Q5 Q6 Q7 HR3 HK3); [rewrite Q72; exact HVM | rewrite Q72; exact HVS | exact HSI2].
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition VMk : VmMaps :=
    mkVmMapsFull RES [(brk, Z_to_bv 64 8192)] [] brk (Z_to_bv 64 (bv_unsigned brk + 8192)) LIM mbase sp0.
  Definition VMo : VmMaps :=
    mkVmMapsFull RES [(brk, Z_to_bv 64 8192)] [(brk, Z_to_bv 64 4096)] brk (Z_to_bv 64 (bv_unsigned brk + 8192)) LIM mbase sp0.
  Definition VMd : VmMaps :=
    mkVmMapsFull RES [(Z_to_bv 64 (bv_unsigned brk + 4096), Z_to_bv 64 4096)] [] brk
                 (Z_to_bv 64 (bv_unsigned brk + 8192)) LIM mbase sp0.
  Definition vm_mid (VM : VmMaps) : Prop := VM = VMk \/ VM = VMo \/ VM = VMd.

  #[using="Type"] Lemma RES_eq : RES = [(Z_to_bv 64 65536, Z_to_bv 64 139264); (Z_to_bv 64 204800, Z_to_bv 64 499712);
                        (Z_to_bv 64 704512, Z_to_bv 64 28672); (Z_to_bv 64 733184, Z_to_bv 64 208896)].
  Proof. vm_compute. reflexivity. Qed.

  #[using="path Hbrk Hplen"] Lemma vm_mid_shape : forall VM, vm_mid VM ->
    vm_reserved VM = RES /\ vm_limit VM = LIM
    /\ exists mp ms, vm_maps VM = [(mp, ms)]
       /\ (bv_unsigned ms = 8192 /\ mp = brk \/ bv_unsigned ms = 4096 /\ bv_unsigned mp = bv_unsigned brk + 4096)%Z.
  Proof.
    intros VM HV. pose proof (brk_lo brk Hbrk) as Blo. pose proof (brk_hi path brk Hbrk Hplen) as Bhi.
    destruct HV as [-> | [-> | ->]]; cbn [VMk VMo VMd vm_reserved vm_limit vm_maps];
      (split; [reflexivity|]); (split; [reflexivity|]); eexists _, _; (split; [reflexivity|]);
      rewrite ?u64_lit by lia.
    - left. split; [reflexivity | reflexivity].
    - left. split; [reflexivity | reflexivity].
    - right. split; reflexivity.
  Qed.

  #[using="path Hvsp Hbrk Hplen"] Lemma vm_mid_grant_exists : forall hint VM, vm_mid VM -> exists a, grant_ok hint (modelV VM) a (page_round_up_Z 69632) = true.
  Proof.
    intros hint VM HV. pose proof (brk_lo brk Hbrk) as Blo. pose proof (brk_hi path brk Hbrk Hplen) as Bhi.
    destruct (vm_mid_shape VM HV) as (Hr & Hl & mp & ms & Hm & Hms).
    change (page_round_up_Z 69632) with 69632%Z.
    apply grant_exists.
    - lia.
    - rewrite mV_vmmaps, Hr, Hm, RES_eq. repeat constructor; cbn [snd]; rewrite ?u64_lit by lia; lia.
    - rewrite mV_vmmaps, Hr, Hm, RES_eq. cbn [length app Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
    - apply grant_budget_intro; [reflexivity | reflexivity |]. rewrite mV_vmmaps.
      unfold vm_live_bytes. rewrite Hm, Hl. cbn [live_bytes]. pose proof LIM_ge. lia.
    - (* [comment removed for export] *) unfold init_sp_ok, sp_window_lo. rewrite mV_vmmaps.
      pose proof (proj1 Hvsp) as SPlo. unfold sp_window_lo in SPlo.
      destruct HV as [-> | [-> | ->]]; cbn [VMk VMo VMd vm_init_sp]; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="path Htid Hbrk Hplen"] Lemma vm_mid_grant : forall hint VM a, vm_mid VM -> grant_ok hint (modelV VM) a 69632 = true ->
    (bv_unsigned a mod 4096 = 0 /\ 0xe6000 <= bv_unsigned a /\ bv_unsigned a + 69632 <= bv_unsigned sp0 - 8388608
     /\ (bv_unsigned brk + 8192 <= bv_unsigned a \/ bv_unsigned a + 69632 <= bv_unsigned brk + 4096))%Z   (* [comment removed for export] *)
    /\ (forall mp ms, vm_maps VM = [(mp, ms)] ->
          (bv_unsigned a + 69632 <= bv_unsigned mp \/ bv_unsigned mp + bv_unsigned ms <= bv_unsigned a)%Z).
  Proof.
    intros hint VM a HV Hg. pose proof (brk_lo brk Hbrk) as Blo. pose proof (brk_hi path brk Hbrk Hplen) as Bhi.
    destruct (vm_mid_shape VM HV) as (Hr & Hl & mp & ms & Hm & Hms).
    destruct (grant_ok_unpack _ _ _ _ Hg) as (Hal & Hpos & Hce & Hrf & Hlive).
    rewrite mV_vmmaps in Hrf. rewrite Hr, Hm, RES_eq in Hrf.
    unfold alloc_top, stack_max_size in Hce. rewrite mV_vmmaps in Hce.   (* [comment removed for export] *)
    assert (Hisp : vm_init_sp VM = sp0) by (destruct HV as [-> | [-> | ->]]; reflexivity). rewrite Hisp in Hce.
    unfold page_size in Hal. pose proof (u64_range a) as Ha.
    assert (Hn : bv_unsigned (Z_to_bv 64 69632) = 69632%Z) by (apply u64_lit; lia).
    pose proof (region_free_In _ _ _ (Z_to_bv 64 65536) (Z_to_bv 64 139264) Hrf ltac:(cbn [In app]; tauto)) as D1.
    pose proof (region_free_In _ _ _ (Z_to_bv 64 204800) (Z_to_bv 64 499712) Hrf ltac:(cbn [In app]; tauto)) as D2.
    pose proof (region_free_In _ _ _ (Z_to_bv 64 704512) (Z_to_bv 64 28672) Hrf ltac:(cbn [In app]; tauto)) as D3.
    pose proof (region_free_In _ _ _ (Z_to_bv 64 733184) (Z_to_bv 64 208896) Hrf ltac:(cbn [In app]; tauto)) as D4.
    rewrite !u64_lit in D2 by lia. rewrite !u64_lit in D3 by lia.
    pose proof (region_free_In _ _ _ mp ms Hrf ltac:(cbn [In app]; tauto)) as D5.
    rewrite Hn in D1, D4, D5. rewrite !u64_lit in D1 by lia. rewrite !u64_lit in D4 by lia.
    assert (Ha4096 : (4096 <= bv_unsigned a)%Z).
    { destruct (proj1 (Z.mod_divide (bv_unsigned a) 4096 ltac:(lia)) Hal) as [q Hq]. lia. }
    pose proof (u64_range mp).
    split.
    2:{ intros mp' ms' Hm'. rewrite Hm in Hm'. injection Hm' as <- <-. exact D5. }
    destruct Hms as [[Hms1 ->] | [Hms1 Hmp]]; rewrite ?Hms1, ?Hmp in D5; repeat split; lia.
  Qed.

  #[using="Hvsp Htid Hbrk Hplen SI_step"] Lemma w65_mid : forall vals R M VM,
    exitG_branch ->
    length vals = 72%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = p1 sp0 a0s path envv ->
    vals_ev vals 70 = brk -> vals_ev vals 5 = tid -> vals_ev vals 6 = canary_w rdraw -> vals_ev vals 7 = secret_w rdraw ->
    regs_ok (ENVv vals) srM R -> know_ok RSEGS (ENVv vals) M knM -> vm_mid VM -> SI M ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x99294) M (seg_rom RSEGS)) (modelV VM))
               (t_alt2 (t_die msg_oom fs0) K).
  Proof.
    intros vals R M VM EXIT HL P0 P2 P70 P5 P6 P7 HR HK HV HSI.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi.
    unfold sp_window_lo, sp_window_hi in *.
    pose proof (brk_lo brk Hbrk) as Blo. pose proof (brk_hi path brk Hbrk Hplen) as Bhi. pose proof (brk_al brk Hbrk) as Bal.
    (* [comment removed for export] *)
    run_block_keep scr0 72%nat. si_block HSI R M.
    (* [comment removed for export] *)
    eapply (rz_mmap_anon RSEGS _ _ _ (modelV VM) ECALLW 69632).
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
      intros e He. assert (e = ENOMEM) as -> by (destruct He as [<-|[]]; reflexivity).
      rewrite v_addi_pc4 by lia. change (0x9a8e4 + 4)%Z with 0x9a8e8%Z.
      lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
        pose proof (regs_set_a0 E sr Rc (errno_ret ENOMEM) ENOMEMv HR ltac:(apply bv_eq; reflexivity)) as HR2 end.
      eapply (w65_oomN vals); [exact HL | exact P0 | exact HR2 | exact HK].
    - (* [comment removed for export] *)
      intros a Hg. rewrite v_addi_pc4 by lia. change (0x9a8e4 + 4)%Z with 0x9a8e8%Z.
      change (page_round_up_Z 69632) with 69632%Z in Hg |- *.
      destruct (vm_mid_grant _ VM a HV Hg) as ((Gal & Glo & Ghi & Gdj) & Gsep).
      (* [comment removed for export] *)
      lazymatch type of HR with regs_ok _ ?sr ?Rc =>
        pose proof (env_app_regs vals [a] _ sr Rc ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR2 end.
      lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
        pose proof (env_app_know RSEGS vals [a] _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
      clear HR HK.
      set (vals2 := vals ++ [a]) in *.
      assert (HL2 : length vals2 = 73%nat) by (subst vals2; rewrite length_app, HL; reflexivity).
      assert (Q0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
      assert (Q2 : vals_ev vals2 2 = p1 sp0 a0s path envv) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P2).
      assert (Q70 : vals_ev vals2 70 = brk) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P70).
      assert (Q5 : vals_ev vals2 5 = tid) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P5).
      assert (Q6 : vals_ev vals2 6 = canary_w rdraw) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P6).
      assert (Q7 : vals_ev vals2 7 = secret_w rdraw) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P7).
      assert (Q72 : vals_ev vals2 72 = a).
      { subst vals2. rewrite <- HL. rewrite <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity. }
      clearbody vals2. clear HL P0 P2 P70 P5 P6 P7 vals. rename HL2 into HL.
      change (Env (vals_ev vals2) (blobs_ev (blobs0 a0s path))) with (ENVv vals2) in HR2, HK2.
      pose proof (regs_set_a0 (ENVv vals2) _ _ a gx HR2 ltac:(cbn [edenot gx ev ENV]; exact Q72)) as HR. clear HR2.
      (* [comment removed for export] *)
      lazymatch type of HK2 with know_ok _ _ ?Mc _ =>
        assert (HK3 : know_ok RSEGS (ENVv vals2) Mc knG00) end.
      { unfold knG00. apply know_ok_cons; [|apply know_ok_cons; [|apply know_ok_cons; [|apply know_ok_cons; [|exact HK2]]]].
        - apply kalign_intro; [lia|]. cbn [edenot gx ev ENV]. rewrite Q72. exact Gal.
        - apply krange_intro. cbn [edenot gx ev ENV]. rewrite Q72. lia.
        - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot gx ev ENV]. rewrite Q0, Q72. lia.   (* [comment removed for export] *)
        - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot bx gx ev ENV]. rewrite Q70, Q72. lia. }
      clear HK2.
      pose proof (xfer_zfill RSEGS (ENVv vals2) _ knG00 gx 0 a 69632 HK3
                    ltac:(unfold estart; cbn [a_base a_off edenot gx ev ENV]; rewrite Q72; lia)
                    ltac:(lia) ltac:(lia)) as HK.
      clear HK3.
      lazymatch type of HK with know_ok _ _ _ ?kn => replace kn with knG0 in HK by (vm_compute; reflexivity) end.
      apply (w65_G vals2 _ _ _ EXIT HL Q0 Q2 Q70 Q5 Q6 Q7 HR HK).
      3:{ si_fill HSI. }
      2:{ rewrite Q72. destruct (vm_mid_shape VM HV) as (Hr & Hl & mp & ms & Hm & Hms).
          unfold w65_vm, mmap_model. rewrite ?with_vmmaps_vm, ?mV_vmmaps. cbn [vm_reserved vm_limit vm_maps]. rewrite Hr, Hl, Hm.
          split; [reflexivity|]. split; [reflexivity|].
          specialize (Gsep mp ms Hm). pose proof (u64_range mp).
          destruct Hms as [[Hms1 ->] | [Hms1 Hmp]].
          - left. split; [rewrite <- (Z_to_bv_bv_unsigned 64 ms), Hms1; reflexivity | lia].
          - right. split; [rewrite <- (Z_to_bv_bv_unsigned 64 ms), Hms1, <- (Z_to_bv_bv_unsigned 64 mp), Hmp; reflexivity | lia]. }
      (* [comment removed for export] *)
      rewrite Q72. destruct (vm_mid_shape VM HV) as (Hr & Hl & mp & ms & Hm & Hms).
      assert (Hisp : vm_init_sp VM = sp0) by (destruct HV as [-> | [-> | ->]]; reflexivity).   (* [comment removed for export] *)
      unfold vm_pre, mmap_model. rewrite ?with_vmmaps_vm, ?mV_vmmaps. cbn [vm_reserved vm_limit vm_maps vm_noaccess vm_start_brk vm_brk vm_init_sp].
      rewrite Hr, Hl, Hm, Hisp.
      assert (Hn : bv_unsigned (Z_to_bv 64 69632) = 69632%Z) by (apply u64_lit; lia).
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [apply map_has_head|].
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
      constructor; [|constructor; [constructor | constructor]].
      constructor; [|constructor]. unfold UbTargetPre.iv_disjoint. cbn [fst snd]. rewrite Hn. lia.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac guard_tail EXIT HL P0 P1 P2 P70 P5 P6 P7 VMX HSI Rn Mn :=
    run_blockW_keep scr0 71%nat; si_block HSI Rn Mn;
    lazymatch goal with
    | HR' : regs_ok _ ?sr ?R', HK' : know_ok _ _ ?M' ?kn |- _ =>
      (* [comment removed for export] *)
      pose proof (env_app_regs _ [getr R' 10] _ sr R' ltac:(rewrite HL; vm_compute; reflexivity) HR') as HR2;
      pose proof (env_app_know RSEGS _ [getr R' 10] _ M' kn ltac:(rewrite HL; vm_compute; reflexivity) HK') as HK2;
      clear HR' HK';
      lazymatch goal with
      | |- realizes _ (mkCfg (mkst _ _ _ _) _) _ =>
        lazymatch type of HL with length ?vals = _ =>
        set (vals2 := vals ++ [getr R' 10]) in *;
        assert (HL2 : length vals2 = 72%nat) by (subst vals2; rewrite length_app, HL; reflexivity);
        assert (Q0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0);
        assert (Q2 : vals_ev vals2 2 = p1 sp0 a0s path envv) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P2);
        assert (Q70 : vals_ev vals2 70 = brk) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P70);
        assert (Q5 : vals_ev vals2 5 = tid) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P5);
        assert (Q6 : vals_ev vals2 6 = canary_w rdraw) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P6);
        assert (Q7 : vals_ev vals2 7 = secret_w rdraw) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P7);
        assert (Q71 : vals_ev vals2 71 = getr R' 10)
          by (subst vals2; rewrite <- HL; rewrite <- (Nat.add_0_r (length vals)); rewrite vals_ev_app_r; reflexivity);
        change (Env (vals_ev vals2) (blobs_ev (blobs0 a0s path))) with (ENVv vals2) in HR2, HK2;
        pose proof (regs_ok_set_have (ENVv vals2) _ R' 10 _ (EVar 71) HR2 eq_refl
                      ltac:(cbn [edenot ev ENV]; exact Q71) ltac:(discriminate)) as HR3;
        clear HR2;
        lazymatch type of HR3 with regs_ok _ ?sr3 _ => replace sr3 with srM in HR3 by (vm_compute; reflexivity) end;
        pose proof (know_ok_sub RSEGS (ENVv vals2) M' kn knM ltac:(vm_compute; reflexivity) HK2) as HK3;
        clear HK2;
        apply (w65_mid vals2 R' M' VMX EXIT HL2 Q0 Q2 Q70 Q5 Q6 Q7 HR3 HK3); [ | exact HSI ]
        end
      end
    end.

  #[using="Hvsp Htid Hbrk Hplen SI_step"] Theorem brk_ok_worldV : exitG_branch -> brk_ok_entry (t_alt2 (t_die msg_oom fs0) K).
  Proof.
    intros EXIT vals R M HL P0 P70 P1 P2 P5 P6 P7 HR HK HSI0.
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
    change (mkModelA fdsV (mkVmMapsFull RES [(brk, Z_to_bv 64 8192)] [] brk (Z_to_bv 64 (bv_unsigned brk + 8192)) LIM mbase sp0)
                    stdin0 fs0 None (Some tid) None) with (modelV VMk).
    (* [comment removed for export] *)
    run_block_keep scr0 71%nat. si_block HSI R M.
    (* [comment removed for export] *)
    apply (rz_conseq RSEGS _ (t_alt3 (t_alt2 (t_die msg_oom fs0) K) (t_alt2 (t_die msg_oom fs0) K) (t_alt2 (t_die msg_oom fs0) K)));
      [ | apply t_alt3_idem ].
    eapply (rz_mmap_fixed_noaccess RSEGS _ _ _ (modelV VMk) ECALLW brk 4096).
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
    - change (page_round_up_Z 4096) with 4096%Z. unfold alloc_top, stack_max_size. rewrite mV_vmmaps. cbn [VMk vm_init_sp]. lia.   (* [comment removed for export] *)
    - regv HR (12 : reg). reflexivity.
    - regv HR (13 : reg). reflexivity.
    - regv HR (14 : reg). apply bv_eq. reflexivity.
    - regv HR (15 : reg). reflexivity.
    - rewrite mV_vmmaps. cbn [VMk vm_reserved]. apply region_free_above_top. rewrite rtop. lia.
    - rewrite mV_vmmaps. cbn [VMk vm_maps]. change (page_round_up_Z 4096) with 4096%Z.
      apply map_contains_head; rewrite ?u64_lit by lia; lia.
    - (* [comment removed for export] *)
      intros e He. assert (e = ENOMEM) as -> by (destruct He as [<-|[]]; reflexivity).
      rewrite v_addi_pc4 by lia. change (0x9a8e4 + 4)%Z with 0x9a8e8%Z.
      lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
        pose proof (regs_set_a0 E sr Rc (errno_ret ENOMEM) ENOMEMv HR ltac:(apply bv_eq; reflexivity)) as HR1 end.
      clear HR. rename HR1 into HR.
      guard_tail EXIT HL P0 P1 P2 P70 P5 P6 P7 VMk HSI R M. left. reflexivity.
    - (* [comment removed for export] *)
      rewrite v_addi_pc4 by lia. change (0x9a8e4 + 4)%Z with 0x9a8e8%Z.
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
      guard_tail EXIT HL P0 P1 P2 P70 P5 P6 P7 VMo HSI R M. right. left. reflexivity.
    - (* [comment removed for export] *)
      intros e He. assert (e = ENOMEM) as -> by (destruct He as [<-|[]]; reflexivity).
      rewrite v_addi_pc4 by lia. change (0x9a8e4 + 4)%Z with 0x9a8e8%Z.
      change (page_round_up_Z 4096) with 4096%Z.
      lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
        pose proof (regs_set_a0 E sr Rc (errno_ret ENOMEM) ENOMEMv HR ltac:(apply bv_eq; reflexivity)) as HR1 end.
      clear HR. rename HR1 into HR.
      lazymatch type of HK with know_ok _ ?E ?Mc ?kn =>
        pose proof (xfer_unfill RSEGS E Mc kn bx 0 brk 4096 HK
                      ltac:(unfold estart; cbn [a_base a_off edenot bx ev ENV]; rewrite P70; lia) ltac:(lia)
                      ltac:(pose proof (u64_range brk); lia)) as HK1 end.
      clear HK. rename HK1 into HK.
      lazymatch type of HK with know_ok _ _ _ ?kn => replace kn with knU in HK by (vm_compute; reflexivity) end.
      (* [comment removed for export] *)
      rewrite fixed_destroyed_model_simple by reflexivity. rewrite mV_vmmaps.
      cbn [VMk vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit].
      rewrite maps_subtract_cons, !maps_subtract_nil, app_nil_r.
      rewrite (u64_lit 4096) by lia.
      rewrite iv_subtract_prefix by (rewrite ?u64_lit by lia; lia).
      rewrite u64_lit by lia.
      replace (bv_unsigned brk + 8192 - (bv_unsigned brk + 4096))%Z with 4096%Z by lia.
      change (with_vmmaps (mkVmMapsFull RES [(Z_to_bv 64 (bv_unsigned brk + 4096), Z_to_bv 64 4096)] [] brk
                       (Z_to_bv 64 (bv_unsigned brk + 8192)) LIM mbase sp0) (modelV VMk)) with (modelV VMd).
      lazymatch type of HK with know_ok _ _ ?Mc _ => assert (HSI2 : SI Mc) by si_fill HSI end.
      clear HSI. rename HSI2 into HSI.
      guard_tail EXIT HL P0 P1 P2 P70 P5 P6 P7 VMd HSI R M. right. right. reflexivity.
  Qed.
End World.

(* [comment removed for export] *)
#[using="Type"] Theorem brk_ok_world_g sp0 a0s path envv rdraw tid mem0 brk mbase fs0 stdin0
  (Hvsp : valid_sp sp0) (Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z) (Hbrk : valid_brk RSEGS brk)
  (Hplen : (length path <= 4095)%nat) fd3 K :
  exitG_branch sp0 a0s path envv rdraw tid brk fs0 stdin0 fd3 (above_eq sp0 mem0) K ->
  brk_ok_branch_g sp0 a0s path envv rdraw tid mem0 brk mbase fs0 stdin0 fd3 (t_alt2 (t_die msg_oom fs0) K).
Proof.
  intros EXIT. exact (brk_ok_worldV sp0 a0s path envv rdraw tid brk mbase fs0 stdin0 Hvsp Htid Hbrk Hplen fd3
                        (above_eq sp0 mem0) (above_eq_step sp0 mem0) K EXIT).
Qed.

#[using="Type"] Theorem brk_ok_world sp0 a0s path envv rdraw tid mem0 brk mbase fs0 stdin0
  (Hvsp : valid_sp sp0) (Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z) (Hbrk : valid_brk RSEGS brk)
  (Hplen : (length path <= 4095)%nat) K :
  exitG_branch sp0 a0s path envv rdraw tid brk fs0 stdin0 (FdFile path (Z_to_bv 64 0)) (above_eq sp0 mem0) K ->
  brk_ok_branch sp0 a0s path envv rdraw tid mem0 brk mbase fs0 stdin0 (t_alt2 (t_die msg_oom fs0) K).
Proof. exact (brk_ok_world_g sp0 a0s path envv rdraw tid mem0 brk mbase fs0 stdin0 Hvsp Htid Hbrk Hplen (FdFile path (Z_to_bv 64 0)) K). Qed.
End FPW_3.

End RefW65.

(* [comment removed for export] *)
Module RefW65m.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs.
Import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.DispatchCompute.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.PropExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.CatExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.CatSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SeqExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.StoreOk OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SimInv OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.ExitSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.ShapeAlg OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.ShapeLaws OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.Nodes OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.MmapSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.AllocSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.FileSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.AgentLib OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SpecConsts OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymExec2 OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymExec2Sound OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymRun OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymDrive OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymDriveX OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.LibKnowFrame OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.UbLibStdioCall OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.Spec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.LibWritev OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefNodes OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.UbExitBase OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.UbStdioDefs OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.UbExit OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.UbStartup OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.UbMainEntry OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.Hoare OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.Frame OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.MallocDefs OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefEnframeArith OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.UbEnframeBase OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.UbEnframe OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.UbReadBase.
Import OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.UbPilotOOM_defs OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.UbPilotOOM.
Import OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymXfer OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymAbove OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefAbove RefW65_defs RefW65.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Tactic Notation "run_block" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX false.
Tactic Notation "run_blockW" constr(scr) constr(NX) := run_block_gen FUEL STOPS_W scr NX false.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section FPW_4. Context {fx : PropExec.FPState}.

#[using="Type"] Lemma mprotect_len_val : forall (a : word),
  (bv_unsigned a mod 4096 = 0)%Z -> (bv_unsigned a + 12288 < 2 ^ 64)%Z ->
  alu64 ALU_ADD (alu64 ALU_ADD (mul_div M_MUL (Z_to_bv 64 (-1)) a)
                   (alu64 ALU_AND (alu64 ALU_ADD a (Z_to_bv 64 12287)) (Z_to_bv 64 18446744073709547520)))
        (Z_to_bv 64 (-4096)) = Z_to_bv 64 4096.
Proof.
  intros a Hal Hb. pose proof (u64_range a) as Ha.
  apply bv_eq. cbn [alu64 alu mul_div].
  rewrite ?bv_add_unsigned, ?bv_and_unsigned, ?bv_mul_unsigned, ?bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
  change ((-1) mod 2 ^ 64)%Z with (2 ^ 64 - 1)%Z.
  change (18446744073709547520 mod 2 ^ 64)%Z with (2 ^ 64 - 4096)%Z.
  change (12287 mod 2 ^ 64)%Z with 12287%Z. change (4096 mod 2 ^ 64)%Z with 4096%Z.
  rewrite (Z.mod_small (bv_unsigned a + 12287)) by lia.
  rewrite fld_hi by lia.
  destruct (proj1 (Z.mod_divide (bv_unsigned a) 4096 ltac:(lia)) Hal) as [q Hq].
  replace ((bv_unsigned a + 12287) / 4096)%Z with (q + 2)%Z by (rewrite Hq; lia).
  nia.
Qed.
End FPW_4.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Section FPW_5. Context {fx : PropExec.FPState}.

#[using="Type"] Lemma grant_ok_na_unpack : forall m a n,   (* [comment removed for export] *)
  grant_ok_na_pin m a n = true ->
  (bv_unsigned a mod page_size = 0)%Z /\ (0 < bv_unsigned a)%Z /\
  (bv_unsigned a + n <= alloc_top (m_vmmaps m))%Z /\
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n) = true.
Proof.
  intros m a n H. unfold grant_ok_na_pin in H.
  rewrite !andb_true_iff in H. destruct H as [[[H1 H2] H3] H4].
  apply Z.eqb_eq in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3. auto.
Qed.

Section World.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable uid : word.   (* [comment removed for export] *)
  Variable hw : word.    (* [comment removed for export] *)
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Variable tid : word.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable brk : word.
  Variable mbase : word.
  Variable fs0 : Fs.
  Variable stdin0 : AmbIn.
  Variable fdata : list byte.
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 [a0s; path] envv uid hw rdraw tid regs0 mem0.
  Hypothesis Hbrk : valid_brk RSEGS brk.
  Hypothesis Hfile : fs_lookup fs0 path = Some fdata.
  Hypothesis Hpne : path <> [].
  Hypothesis Hpns : path_has_slash path = false.   (* [comment removed for export] *)
  Hypothesis Hpnd : path_is_dirref path = false.   (* [comment removed for export] *)
  Hypothesis Hplen : (length path <= 4095)%nat.
  Variable fd3 : FdEntry.
  Variable SI : (word -> option byte) -> Prop.
  Hypothesis SI_step : forall M M' : word -> option byte,
    (forall a : word, (bv_unsigned sp0 <= bv_unsigned a)%Z -> M' a = M a) -> SI M -> SI M'.

  #[local] Notation ENVv := (ENV a0s path).
  (* [comment removed for export] *)
  #[local] Notation RES := (segments_reserved RSEGS).

  #[local] Notation modelV := (modelV tid fs0 stdin0 fd3).
  #[local] Notation model1V := (model1V sp0 tid brk mbase fs0 stdin0 fd3).   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac si_block HSI Rn Mn :=
    lazymatch goal with
    | EQM : ?M' = mem_denot ?E ?Mo ?log, HK : know_ok ?segs ?E ?M' ?kn, HR : regs_ok ?E _ ?R' |- _ =>
        let H := fresh "HSI" in
        assert (H : SI M');
        [ apply (SI_step Mo M'); [| exact HSI]; intros xa Hxa; rewrite EQM;
          apply (mem_denot_above_kd segs E M' Mo kn log 0%nat 0xe6000 xa HK);   (* [comment removed for export] *)
          [ vm_compute; reflexivity | cbn [ev ENV]; pins; lia | cbn [ev ENV]; pins; lia | lia ]
        | clear HSI EQM; try clear Mn; rename H into HSI; try rename M' into Mn; try clear Rn; try rename R' into Rn ]
    end.
  Ltac si_fill HSI :=
    lazymatch goal with
    | |- SI (zfill ?a ?n ?M) => apply (SI_step M); [| exact HSI]; intros xa Hxa; apply zfill_out; rewrite ?u64_lit by lia; lia
    | |- SI (unfill ?a ?n ?M) => apply (SI_step M); [| exact HSI]; intros xa Hxa; apply unfill_outside; rewrite ?u64_lit by lia; lia
    end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="Hvsp Hplen"] Lemma w65_oomQ : forall vals R M VM,
    length vals = 72%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENVv vals) srQ0 R -> know_ok RSEGS (ENVv vals) M knP ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x9a940) M (seg_rom RSEGS)) (modelV VM)) (t_die msg_oom fs0).
  Proof.
    intros vals R M VM HL P0 HR HK.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi.
    unfold sp_window_lo, sp_window_hi in *.
    run_block scr0 72%nat.
    oom_stdio_exit HL P0 resQX_eq (mV_fd2 tid fs0 stdin0 fd3 VM) (mV_fs tid fs0 stdin0 fd3 VM).
  Qed.

  (* [comment removed for export] *)
  #[using="Hvsp Hplen"] Lemma w65_oomS : forall vals R M VM,
    length vals = 72%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENVv vals) srS0 R -> know_ok RSEGS (ENVv vals) M knR ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x9a8e8) M (seg_rom RSEGS)) (modelV VM)) (t_die msg_oom fs0).
  Proof.
    intros vals R M VM HL P0 HR HK.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi.
    unfold sp_window_lo, sp_window_hi in *.
    run_block scr0 72%nat.
    oom_stdio_exit HL P0 resSX_eq (mV_fd2 tid fs0 stdin0 fd3 VM) (mV_fs tid fs0 stdin0 fd3 VM).
  Qed.
  Variable K : TSet.

  (* [comment removed for export] *)
  Definition exitT_branch : Prop :=
    forall vals R M VM,
      length vals = 105%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = p1 sp0 a0s path envv ->
      vals_ev vals 70 = brk -> vals_ev vals 5 = tid -> vals_ev vals 6 = canary_w rdraw -> vals_ev vals 7 = secret_w rdraw ->
      regs_ok (ENVv vals) srZm R -> know_ok RSEGS (ENVv vals) M knZm ->
      vm_pre VM sp0 (vals_ev vals 71) (vals_ev vals 72) -> w65_vm VM (vals_ev vals 71) (vals_ev vals 72) -> SI M ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x32688) M (seg_rom RSEGS)) (modelV VM)) K.

  #[using="Hvsp Hbrk Hplen SI_step"] Lemma w65_T : forall vals R M VM,
    exitT_branch ->
    length vals = 73%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = p1 sp0 a0s path envv ->
    vals_ev vals 70 = brk -> vals_ev vals 5 = tid -> vals_ev vals 6 = canary_w rdraw -> vals_ev vals 7 = secret_w rdraw ->
    regs_ok (ENVv vals) srT0 R -> know_ok RSEGS (ENVv vals) M knT0 ->
    vm_pre VM sp0 (vals_ev vals 71) (vals_ev vals 72) -> w65_vm VM (vals_ev vals 71) (vals_ev vals 72) -> SI M ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x9a8e8) M (seg_rom RSEGS)) (modelV VM)) K.
  Proof.
    intros vals R M VM EXIT HL P0 P2 P70 P5 P6 P7 HR HK HVM HVS HSI.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi.
    unfold sp_window_lo, sp_window_hi in *.
    pose proof (brk_lo brk Hbrk) as Blo. pose proof (brk_hi path brk Hbrk Hplen) as Bhi. pose proof (brk_al brk Hbrk) as Bal.
    (* [comment removed for export] *)
    pose proof (know_nth RSEGS _ _ knT0 ltac:(let i := kidx knT0 (is_krange gx) in exact i) _ HK eq_refl)
      as Kgm; cbn [kentry_ok edenot ev ENV] in Kgm.
    pose proof (know_nth RSEGS _ _ knT0 ltac:(let i := kidx knT0 (is_kalign gx) in exact i) _ HK eq_refl)
      as Kga; cbn [kentry_ok edenot ev ENV] in Kga.
    pose proof (know_nth RSEGS _ _ knT0 ltac:(let i := kidx knT0 (is_krange ax) in exact i) _ HK eq_refl)
      as Kar; cbn [kentry_ok edenot ev ENV] in Kar.
    pose proof (know_nth RSEGS _ _ knT0 ltac:(let i := kidx knT0 (is_kdisj ax gx) in exact i) _ HK eq_refl)
      as Kgd; cbn [kentry_ok] in Kgd; unfold estart in Kgd; cbn [a_base a_off edenot ax gx ev ENV] in Kgd.
    pose proof (know_nth RSEGS _ _ knT0 ltac:(let i := kidx knT0 (is_kdisj (EVar 0) gx) in exact i) _ HK eq_refl)   (* [comment removed for export] *)
      as Kgs; cbn [kentry_ok] in Kgs; unfold estart in Kgs; cbn [a_base a_off edenot gx ev ENV] in Kgs; rewrite P0 in Kgs.
    set (gm := vals_ev vals 72) in *. set (av := vals_ev vals 71) in *.
    (* [comment removed for export] *)
    run_block_keep scrG 73%nat.
    { unfold sc_denot. cbn [edenot ev ENV]. apply bt_ne_not. subst gm. lia. }
    si_block HSI R M.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ ?E ?MG ?kn =>
      krdv HK 71%nat 4136%Z 8%nat Hmem; [apply flat_intro; cbn [edenot ev ENV]; fold av; lia|];
      krdv HK 71%nat 4152%Z 8%nat Hmw; [apply flat_intro; cbn [edenot ev ENV]; fold av; lia|];
      pose proof (know_nth RSEGS _ _ kn ltac:(let i := kidx kn (is_kzero_cov gx 9 8) in exact i) _ HK eq_refl) as Kz;
      cbn [kentry_ok] in Kz; unfold elenZ, estart in Kz; cbn [a_base a_off edenot ev ENV] in Kz;
      pose proof (kwr_store_ok RSEGS E _ kn ltac:(let i := kidx kn (is_kwr_cov gx 13 69615) in exact i)
                    _ _ _ 13 (Z.to_nat 69615) HK eq_refl ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as Hok;
      pose proof (know_nth RSEGS _ _ kn ltac:(let i := kidx kn (is_kimg_cov 109512 96) in exact i) _ HK eq_refl) as Kimg;
      cbn [kentry_ok] in Kimg
    end.
    fold gm in Kz, Hmem, Hmw, Hok.
    unfold adenot, v_addi in Hmem, Hmw, Hok. cbn [a_base a_off edenot ev ENV] in Hmem, Hmw, Hok.
    fold av in Hmem, Hmw. fold gm in Hok.
    change (bv_unsigned (Z_to_bv 64 69623)) with 69623%Z in Kz.
    assert (EF : efH M (Z_to_bv 64 1) (bv_unsigned av + 4120) (bv_unsigned gm) 72480 0 65536 0 0 69616
                     (bv_unsigned gm + 16) 1).
    { constructor.
      - vm_compute. reflexivity.
      - unfold slot_start, UNIT. lia.
      - vm_compute. reflexivity.
      - pose proof (u64_range av). lia.
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
      - replace (bv_unsigned av + 4120 + 16)%Z with (bv_unsigned av + 4136)%Z by lia.
        rewrite Hmem. subst gm. rewrite Z_to_bv_bv_unsigned. reflexivity.
      - replace (bv_unsigned av + 4120 + 32)%Z with (bv_unsigned av + 4152)%Z by lia. exact Hmw.
      - replace (bv_unsigned gm + 16 - 4)%Z with (bv_unsigned gm + 9 + 3)%Z by lia. apply (proj2 Kz). lia.
      - replace (bv_unsigned gm + 16 - 3)%Z with (bv_unsigned gm + 9 + 4)%Z by lia. apply (proj2 Kz). lia.
      - intros C. exfalso. apply C. reflexivity.
      - replace (bv_unsigned gm + 16 - 3)%Z with (bv_unsigned gm + 13)%Z by lia.
        replace (Z.to_nat (69616 - 1)) with (Z.to_nat 69615) by reflexivity. exact Hok.
      - intros j Hj. unfold SCT. apply (proj2 (proj2 Kimg)). lia. }
    assert (RT : Hoare.ret_ok (Z_to_bv 64 0x32688)) by (apply bv_eq; vm_compute; reflexivity).
    assert (G1 : getr R 1 = Z_to_bv 64 0x32688) by (regv HR (1:reg); reflexivity).
    assert (G10 : getr R 10 = Z_to_bv 64 (bv_unsigned av + 4120)).
    { regv HR (10:reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV].
      reflexivity. }
    assert (G11 : getr R 11 = Z_to_bv 64 0) by (regv HR (11:reg); reflexivity).
    assert (G12 : getr R 12 = Z_to_bv 64 65536) by (regv HR (12:reg); reflexivity).
    assert (G13 : getr R 13 = Z_to_bv 64 1) by (regv HR (13:reg); reflexivity).
    destruct (enframe_run M (Z_to_bv 64 1) _ _ _ _ _ _ _ _ _ _ EF R (seg_rom RSEGS) (Z_to_bv 64 0x32688)
                G1 RT G10 G11 G12 G13) as (R2 & Hms & Hkeep & HA0).
    clear RT G1 G10 G11 G12 G13.
    replace (Z_to_bv 64 630772) with (0x99ff4 : word) by (apply bv_eq; vm_compute; reflexivity).
    eapply rz_msteps; [reflexivity | reflexivity | exact Hms |]. clear Hms.
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
      pose proof (carry_after RSEGS E MG LOGE kn [] knZm [] _ ltac:(vm_compute; reflexivity)
                    ltac:(cbn [log_flat LOGE]; unfold flat, estart; cbn [a_base a_off edenot gx ev ENV]; fold gm;
                          repeat split; lia)
                    HK ltac:(constructor)) as HK2
    end.
    assert (HSI2 : SI (mem_denot (ENVv vals) M LOGE)).
    { apply (SI_step M); [|exact HSI]. intros xa Hxa.
      apply (mem_denot_above_kd RSEGS (ENVv vals) _ M knZm LOGE 0%nat 0xe6000 xa HK2);
        [vm_compute; reflexivity | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia | lia]. }
    (* [comment removed for export] *)
    lazymatch type of HR with regs_ok _ ?sr _ =>
      pose proof (regs_after_keeps vals _ sr R R2 callee_saved ltac:(rewrite HL; vm_compute; reflexivity)
                    HR Hkeep callee_saved_no0) as HR2 end.
    rewrite HL in HR2. clear HR.
    set (vals2 := vals ++ junk_vals R2) in *.
    assert (HL2 : length vals2 = 105%nat) by (subst vals2; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (Q2 : vals_ev vals2 2 = p1 sp0 a0s path envv) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P2).
    assert (Q70 : vals_ev vals2 70 = brk) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P70).
    assert (Q5 : vals_ev vals2 5 = tid) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P5).
    assert (Q6 : vals_ev vals2 6 = canary_w rdraw) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P6).
    assert (Q7 : vals_ev vals2 7 = secret_w rdraw) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P7).
    assert (Q71 : vals_ev vals2 71 = av) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); reflexivity).
    assert (Q72 : vals_ev vals2 72 = gm) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); reflexivity).
    change (Env (vals_ev vals2) (blobs_ev (blobs0 a0s path))) with (ENVv vals2) in HR2.
    pose proof (regs_ok_set_have (ENVv vals2) _ R2 10 _ (EAlu ALU_ADD gx (ELit 32)) HR2 HA0
                  ltac:(rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot gx ev ENV];
                        rewrite Q72; f_equal; lia) ltac:(discriminate)) as HR3.
    clear HR2.
    lazymatch type of HR3 with regs_ok _ ?sr _ => replace sr with srZm in HR3 by (vm_compute; reflexivity) end.
    lazymatch type of HK2 with know_ok _ _ ?Mc ?kn =>
      pose proof (env_app_know RSEGS vals (junk_vals R2) _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK3 end.
    clear HK2 HK.
    change (Env (vals_ev (vals ++ junk_vals R2)) (blobs_ev (blobs0 a0s path))) with (ENVv vals2) in HK3.
    change (mem_denot (Env (vals_ev vals) (blobs_ev (blobs0 a0s path))) M LOGE) with (mem_denot (ENVv vals) M LOGE) in HSI2.
    apply (EXIT vals2 R2 _ VM HL2 Q0 Q2 Q70 Q5 Q6 Q7 HR3 HK3);
      [rewrite Q71, Q72; exact HVM | rewrite Q71, Q72; exact HVS | exact HSI2].
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition VMn (a : word) : VmMaps :=
    mkVmMapsFull RES [(a, Z_to_bv 64 8192)] [(a, Z_to_bv 64 8192)] brk brk LIM mbase sp0.
  Definition VMp (a : word) : VmMaps :=
    mkVmMapsFull RES [(a, Z_to_bv 64 8192)] [(a, Z_to_bv 64 4096)] brk brk LIM mbase sp0.
  Definition VMt (a gm : word) : VmMaps :=
    mkVmMapsFull RES [(gm, Z_to_bv 64 69632); (a, Z_to_bv 64 8192)] [(a, Z_to_bv 64 4096)] brk brk LIM mbase sp0.

  #[using="Type"] Lemma RES_eq' : RES = [(Z_to_bv 64 65536, Z_to_bv 64 139264); (Z_to_bv 64 204800, Z_to_bv 64 499712);
                         (Z_to_bv 64 704512, Z_to_bv 64 28672); (Z_to_bv 64 733184, Z_to_bv 64 208896)].
  Proof. vm_compute. reflexivity. Qed.

  #[using="path Hvsp Hplen"] Lemma VMp_grant_exists : forall hint a, exists g, grant_ok hint (modelV (VMp a)) g (page_round_up_Z 69632) = true.
  Proof.
    intros hint a. change (page_round_up_Z 69632) with 69632%Z.
    apply grant_exists.
    - lia.
    - rewrite mV_vmmaps. cbn [VMp vm_reserved vm_limit vm_maps]. rewrite ?RES_eq'.
      repeat constructor; cbn [snd]; rewrite ?u64_lit by lia; lia.
    - rewrite mV_vmmaps. cbn [VMp vm_reserved vm_limit vm_maps]. rewrite ?RES_eq'.
      cbn [length app Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
    - apply grant_budget_intro; [reflexivity | reflexivity |]. rewrite mV_vmmaps.
      unfold vm_live_bytes. cbn [VMp vm_maps vm_limit live_bytes]. rewrite ?u64_lit by lia. pose proof LIM_ge. lia.
    - (* [comment removed for export] *) unfold init_sp_ok, sp_window_lo. rewrite mV_vmmaps. cbn [VMp vm_init_sp].
      pose proof (proj1 Hvsp) as SPlo. unfold sp_window_lo in SPlo. lia.
  Qed.

  #[using="path Htid Hplen"] Lemma VMp_grant : forall hint a g, grant_ok hint (modelV (VMp a)) g 69632 = true ->
    (bv_unsigned g mod 4096 = 0 /\ 0xe6000 <= bv_unsigned g /\ bv_unsigned g + 69632 <= bv_unsigned sp0 - 8388608
     /\ (bv_unsigned a + 8192 <= bv_unsigned g \/ bv_unsigned g + 69632 <= bv_unsigned a))%Z.
  Proof.
    intros hint a g Hg.
    destruct (grant_ok_unpack _ _ _ _ Hg) as (Hal & Hpos & Hce & Hrf & Hlive).
    rewrite mV_vmmaps in Hrf. cbn [VMp vm_reserved vm_maps] in Hrf. rewrite RES_eq' in Hrf.
    unfold alloc_top, stack_max_size in Hce. rewrite mV_vmmaps in Hce. cbn [VMp vm_init_sp] in Hce.   (* [comment removed for export] *)
    unfold page_size in Hal. pose proof (u64_range g) as Hgr. pose proof (u64_range a) as Har.
    assert (Hn : bv_unsigned (Z_to_bv 64 69632) = 69632%Z) by (apply u64_lit; lia).
    pose proof (region_free_In _ _ _ (Z_to_bv 64 65536) (Z_to_bv 64 139264) Hrf ltac:(cbn [In app]; tauto)) as D1.
    pose proof (region_free_In _ _ _ (Z_to_bv 64 204800) (Z_to_bv 64 499712) Hrf ltac:(cbn [In app]; tauto)) as D2.
    pose proof (region_free_In _ _ _ (Z_to_bv 64 704512) (Z_to_bv 64 28672) Hrf ltac:(cbn [In app]; tauto)) as D3.
    pose proof (region_free_In _ _ _ (Z_to_bv 64 733184) (Z_to_bv 64 208896) Hrf ltac:(cbn [In app]; tauto)) as D4.
    rewrite !u64_lit in D2 by lia. rewrite !u64_lit in D3 by lia.
    pose proof (region_free_In _ _ _ a (Z_to_bv 64 8192) Hrf ltac:(cbn [In app]; tauto)) as D5.
    rewrite Hn in D1, D4, D5. rewrite !u64_lit in D1 by lia. rewrite !u64_lit in D4 by lia. rewrite !u64_lit in D5 by lia.
    assert (Hg4096 : (4096 <= bv_unsigned g)%Z).
    { destruct (proj1 (Z.mod_divide (bv_unsigned g) 4096 ltac:(lia)) Hal) as [q Hq]. lia. }
    repeat split; lia.
  Qed.

  #[using="Hvsp Htid Hbrk Hplen SI_step"] Lemma w65_R : forall vals R M,
    exitT_branch ->
    length vals = 72%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = p1 sp0 a0s path envv ->
    vals_ev vals 70 = brk -> vals_ev vals 5 = tid -> vals_ev vals 6 = canary_w rdraw -> vals_ev vals 7 = secret_w rdraw ->
    (0x1000 <= bv_unsigned (vals_ev vals 71))%Z -> (bv_unsigned (vals_ev vals 71) + 8192 <= bv_unsigned sp0 - 8388608)%Z ->   (* [comment removed for export] *)
    regs_ok (ENVv vals) srR0 R -> know_ok RSEGS (ENVv vals) M knR0 -> SI M ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x9a940) M (seg_rom RSEGS)) (modelV (VMp (vals_ev vals 71))))
               (t_alt2 (t_die msg_oom fs0) K).
  Proof.
    intros vals R M EXIT HL P0 P2 P70 P5 P6 P7 Alo Ahi HR HK HSI.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi.
    unfold sp_window_lo, sp_window_hi in *.
    set (av := vals_ev vals 71) in *.
    (* [comment removed for export] *)
    run_block_keep scr0 72%nat. si_block HSI R M.
    eapply (rz_mmap_anon RSEGS _ _ _ (modelV (VMp av)) ECALLW 69632).
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
    - apply VMp_grant_exists.
    - (* [comment removed for export] *)
      intros e He. assert (e = ENOMEM) as -> by (destruct He as [<-|[]]; reflexivity).
      rewrite v_addi_pc4 by lia. change (0x9a8e4 + 4)%Z with 0x9a8e8%Z.
      lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
        pose proof (regs_set_a0 E sr Rc (errno_ret ENOMEM) ENOMEMv HR ltac:(apply bv_eq; reflexivity)) as HR2 end.
      eapply (w65_oomS vals); [exact HL | exact P0 | exact HR2 | exact HK].
    - (* [comment removed for export] *)
      intros g Hg. rewrite v_addi_pc4 by lia. change (0x9a8e4 + 4)%Z with 0x9a8e8%Z.
      change (page_round_up_Z 69632) with 69632%Z in Hg |- *.
      destruct (VMp_grant _ av g Hg) as (Gal & Glo & Ghi & Gdj).
      lazymatch type of HR with regs_ok _ ?sr ?Rc =>
        pose proof (env_app_regs vals [g] _ sr Rc ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR2 end.
      lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
        pose proof (env_app_know RSEGS vals [g] _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
      clear HR HK.
      set (vals2 := vals ++ [g]) in *.
      assert (HL2 : length vals2 = 73%nat) by (subst vals2; rewrite length_app, HL; reflexivity).
      assert (Q0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
      assert (Q2 : vals_ev vals2 2 = p1 sp0 a0s path envv) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P2).
      assert (Q70 : vals_ev vals2 70 = brk) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P70).
      assert (Q5 : vals_ev vals2 5 = tid) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P5).
      assert (Q6 : vals_ev vals2 6 = canary_w rdraw) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P6).
      assert (Q7 : vals_ev vals2 7 = secret_w rdraw) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P7).
      assert (Q71 : vals_ev vals2 71 = av) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); reflexivity).
      assert (Q72 : vals_ev vals2 72 = g).
      { subst vals2. rewrite <- HL. rewrite <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity. }
      clearbody vals2. clearbody av. clear HL P0 P2 P70 P5 P6 P7 vals. rename HL2 into HL.
      change (Env (vals_ev vals2) (blobs_ev (blobs0 a0s path))) with (ENVv vals2) in HR2, HK2.
      pose proof (regs_set_a0 (ENVv vals2) _ _ g gx HR2 ltac:(cbn [edenot gx ev ENV]; exact Q72)) as HR. clear HR2.
      lazymatch type of HK2 with know_ok _ _ ?Mc _ =>
        assert (HK3 : know_ok RSEGS (ENVv vals2) Mc knT00) end.
      { unfold knT00. apply know_ok_cons; [|apply know_ok_cons; [|apply know_ok_cons; [|apply know_ok_cons; [|exact HK2]]]].
        - apply kalign_intro; [lia|]. cbn [edenot gx ev ENV]. rewrite Q72. exact Gal.
        - apply krange_intro. cbn [edenot gx ev ENV]. rewrite Q72. lia.
        - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot gx ev ENV]. rewrite Q0, Q72. lia.   (* [comment removed for export] *)
        - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot ax gx ev ENV]. rewrite Q71, Q72. lia. }
      clear HK2.
      pose proof (xfer_zfill RSEGS (ENVv vals2) _ knT00 gx 0 g 69632 HK3
                    ltac:(unfold estart; cbn [a_base a_off edenot gx ev ENV]; rewrite Q72; lia)
                    ltac:(lia) ltac:(lia)) as HK.
      clear HK3.
      lazymatch type of HK with know_ok _ _ _ ?kn => replace kn with knT0 in HK by (vm_compute; reflexivity) end.
      apply (w65_T vals2 _ _ (VMt av g) EXIT HL Q0 Q2 Q70 Q5 Q6 Q7 HR HK).
      3:{ si_fill HSI. }
      2:{ rewrite Q71, Q72. unfold w65_vm. cbn [vm_reserved vm_limit vm_maps VMt].
          split; [reflexivity|]. split; [reflexivity|]. left. split; [reflexivity | lia]. }
      rewrite Q71, Q72. pose proof (u64_range av).
      unfold vm_pre, mmap_model. rewrite ?with_vmmaps_vm, ?mV_vmmaps. cbn [VMt VMp vm_reserved vm_limit vm_maps vm_noaccess vm_start_brk vm_brk vm_init_sp].
      assert (Hn : bv_unsigned (Z_to_bv 64 69632) = 69632%Z) by (apply u64_lit; lia).
      assert (H8 : bv_unsigned (Z_to_bv 64 8192) = 8192%Z) by (apply u64_lit; lia).
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [apply map_has_head|].   (* [comment removed for export] *)
      split.
      { constructor; [cbn [fst snd]; rewrite ?Hn; lia|]. constructor; [|constructor]. cbn [fst snd]. rewrite ?H8. lia. }
      split; [cbn; lia|].
      split; [cbn [live_bytes]; rewrite Hn, H8; lia|].
      split.
      { exists (av, Z_to_bv 64 8192). split; [cbn [In]; tauto|]. cbn [fst snd]. rewrite H8.
        split; [intros Eav; apply (f_equal bv_unsigned) in Eav; lia | lia]. }
      (* [comment removed for export] *)
      constructor; [|constructor; [constructor | constructor]].
      constructor; [|constructor]. unfold UbTargetPre.iv_disjoint. cbn [fst snd]. rewrite Hn, H8. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  #[using="Hvsp Htid Hbrk Hplen SI_step"] Theorem mmap_ok_worldV : exitT_branch ->
    mmap_ok_entry sp0 a0s path envv rdraw tid brk mbase fs0 stdin0 fd3 SI (t_alt2 (t_die msg_oom fs0) (t_alt2 (t_die msg_oom fs0) K)).
  Proof.
    intros EXIT vals R M a HL P0 P70 P1 P2 P5 P6 P7 HR HK HSI0 Hg.   (* [comment removed for export] *)
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi.
    unfold sp_window_lo, sp_window_hi in *.
    pose proof (brk_lo brk Hbrk) as Blo. pose proof (brk_hi path brk Hbrk Hplen) as Bhi. pose proof (brk_al brk Hbrk) as Bal.
    (* [comment removed for export] *)
    destruct (grant_ok_na_unpack _ _ _ Hg) as (Hal & Hpos & Hce & Hrf).
    unfold RefW65.model1V in Hrf. rewrite m_vmmaps_mkModelA in Hrf. cbn [vm_reserved vm_maps] in Hrf.
    rewrite app_nil_r, RES_eq' in Hrf.
    unfold alloc_top, stack_max_size, RefW65.model1V in Hce. rewrite m_vmmaps_mkModelA in Hce. cbn [vm_init_sp] in Hce.   (* [comment removed for export] *)
    unfold page_size in Hal. pose proof (u64_range a) as Har.
    change (page_round_up_Z 8192) with 8192%Z in Hce, Hrf.
    assert (H8 : bv_unsigned (Z_to_bv 64 8192) = 8192%Z) by (apply u64_lit; lia).
    pose proof (region_free_In _ _ _ (Z_to_bv 64 65536) (Z_to_bv 64 139264) Hrf ltac:(cbn [In app]; tauto)) as D1.
    pose proof (region_free_In _ _ _ (Z_to_bv 64 204800) (Z_to_bv 64 499712) Hrf ltac:(cbn [In app]; tauto)) as D2.
    pose proof (region_free_In _ _ _ (Z_to_bv 64 704512) (Z_to_bv 64 28672) Hrf ltac:(cbn [In app]; tauto)) as D3.
    pose proof (region_free_In _ _ _ (Z_to_bv 64 733184) (Z_to_bv 64 208896) Hrf ltac:(cbn [In app]; tauto)) as D4.
    rewrite H8 in D1, D2, D3, D4.
    rewrite !u64_lit in D1 by lia. rewrite !u64_lit in D2 by lia. rewrite !u64_lit in D3 by lia. rewrite !u64_lit in D4 by lia.
    assert (Ha4096 : (4096 <= bv_unsigned a)%Z).
    { destruct (proj1 (Z.mod_divide (bv_unsigned a) 4096 ltac:(lia)) Hal) as [q Hq]. lia. }
    assert (Aimg : (bv_unsigned a + 8192 <= 0x10000 \/ 0xe6000 <= bv_unsigned a)%Z) by lia.
    clear D1 D2 D3 D4 Hrf.
    (* [comment removed for export] *)
    lazymatch type of HR with regs_ok _ ?sr ?Rc =>
      pose proof (env_app_regs vals [a] _ sr Rc ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR2 end.
    lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
      pose proof (env_app_know RSEGS vals [a] _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
    clear HR HK.
    set (vals2 := vals ++ [a]) in *.
    assert (HL2 : length vals2 = 72%nat) by (subst vals2; rewrite length_app, HL; reflexivity).
    assert (Q0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (Q2 : vals_ev vals2 2 = p1 sp0 a0s path envv) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P2).
    assert (Q70 : vals_ev vals2 70 = brk) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P70).
    assert (Q5 : vals_ev vals2 5 = tid) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P5).
    assert (Q6 : vals_ev vals2 6 = canary_w rdraw) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P6).
    assert (Q7 : vals_ev vals2 7 = secret_w rdraw) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P7).
    assert (Q71 : vals_ev vals2 71 = a).
    { subst vals2. rewrite <- HL. rewrite <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity. }
    clearbody vals2. clear HL P0 P2 P70 P1 P5 P6 P7 vals. rename HL2 into HL.
    change (Env (vals_ev vals2) (blobs_ev (blobs0 a0s path))) with (ENVv vals2) in HR2, HK2.
    pose proof (regs_set_a0 (ENVv vals2) _ _ a ax HR2 ltac:(cbn [edenot ax ev ENV]; exact Q71)) as HR. clear HR2.
    lazymatch type of HR with regs_ok _ ?sr _ => replace sr with srP0 in HR by (vm_compute; reflexivity) end.
    lazymatch type of HK2 with know_ok _ _ ?Mc _ =>
      assert (HK3 : know_ok RSEGS (ENVv vals2) Mc knP00) end.
    { unfold knP00. apply know_ok_cons; [|apply know_ok_cons; [|apply know_ok_cons; [|apply know_ok_cons; [|exact HK2]]]].
      - apply kalign_intro; [lia|]. cbn [edenot ax ev ENV]. rewrite Q71. exact Hal.
      - apply krange_intro. cbn [edenot ax ev ENV]. rewrite Q71. lia.
      - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot ax ev ENV]. rewrite Q0, Q71. lia.   (* [comment removed for export] *)
      - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot ax ev ENV]. rewrite Q71.
        change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. lia. }
    clear HK2.
    pose proof (xfer_unfill RSEGS (ENVv vals2) _ knP00 ax 0 a 8192 HK3
                  ltac:(unfold estart; cbn [a_base a_off edenot ax ev ENV]; rewrite Q71; lia) ltac:(lia) ltac:(lia)) as HK.
    clear HK3.
    lazymatch type of HK with know_ok _ _ _ ?kn => replace kn with knP0 in HK by (vm_compute; reflexivity) end.
    change (page_round_up_Z 8192) with 8192%Z.
    change (noaccess_model a (Z_to_bv 64 8192) model1V) with (modelV (VMn a)).
    assert (HSI : SI (unfill a (Z_to_bv 64 8192) M)) by si_fill HSI0. clear HSI0.
    (* [comment removed for export] *)
    run_block_keep scrP 72%nat.
    { unfold sc_denot. cbn [edenot ax ev ENV]. rewrite Q71. apply bt_ne_not. lia. }
    si_block HSI R M.
    (* [comment removed for export] *)
    eapply (rz_mprotect RSEGS _ _ _ (modelV (VMn a)) ECALLW (Z_to_bv 64 (bv_unsigned a + 4096)) 4096).
    - vm_compute. reflexivity.
    - apply is_ecall_ECALLW.
    - reflexivity.
    - reflexivity.
    - regv HR (17 : reg). reflexivity.
    - regv HR (10 : reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ax ev ENV].
      rewrite Q71. reflexivity.
    - unfold page_size. rewrite u64_lit by lia.
      replace (bv_unsigned a + 4096)%Z with (bv_unsigned a + 1 * 4096)%Z by lia. rewrite Z.mod_add by lia. exact Hal.
    - regv HR (11 : reg). cbn [edenot ax ev ENV]. rewrite Q71. apply mprotect_len_val; lia.
    - lia.
    - change (page_round_up_Z 4096) with 4096%Z. unfold two_pow_64. rewrite u64_lit by lia. lia.
    - regv HR (12 : reg). reflexivity.
    - rewrite mV_vmmaps. cbn [VMn vm_noaccess]. change (page_round_up_Z 4096) with 4096%Z.
      apply map_contains_head; rewrite ?u64_lit by lia; lia.
    - rewrite mV_vmmaps. cbn [VMn vm_maps]. change (page_round_up_Z 4096) with 4096%Z.
      apply map_contains_head; rewrite ?u64_lit by lia; lia.
    - (* [comment removed for export] *)
      apply mprotect_budget_ok_intro; [reflexivity | reflexivity |]. rewrite mV_vmmaps.
      unfold vm_live_bytes. cbn [VMn vm_maps vm_limit live_bytes]. rewrite H8. pose proof LIM_ge. lia.
    - (* [comment removed for export] *)
      intros e He. assert (e = ENOMEM) as -> by (destruct He as [<-|[]]; reflexivity).
      rewrite v_addi_pc4 by lia. change (0x9a93c + 4)%Z with 0x9a940%Z.
      lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
        pose proof (regs_set_a0 E sr Rc (errno_ret ENOMEM) ENOMEMv HR ltac:(apply bv_eq; reflexivity)) as HR2 end.
      eapply (w65_oomQ vals2); [exact HL | exact Q0 | exact HR2 | exact HK].
    - (* [comment removed for export] *)
      rewrite v_addi_pc4 by lia. change (0x9a93c + 4)%Z with 0x9a940%Z.
      change (page_round_up_Z 4096) with 4096%Z.
      lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
        pose proof (regs_set_a0 E sr Rc (Z_to_bv 64 0) (ELit 0) HR eq_refl) as HR2 end.
      clear HR. rename HR2 into HR.
      lazymatch type of HR with regs_ok _ ?sr _ => replace sr with srR0 in HR by (vm_compute; reflexivity) end.
      lazymatch type of HK with know_ok _ ?E ?Mc ?kn =>
        pose proof (xfer_zfill RSEGS E Mc kn ax 4096 (Z_to_bv 64 (bv_unsigned a + 4096)) 4096 HK
                      ltac:(unfold estart; cbn [a_base a_off edenot ax ev ENV]; rewrite Q71, u64_lit by lia; lia)
                      ltac:(lia) ltac:(rewrite u64_lit by lia; lia)) as HK2 end.
      clear HK. rename HK2 into HK.
      lazymatch type of HK with know_ok _ _ _ ?kn => replace kn with knR0 in HK by (vm_compute; reflexivity) end.
      (* [comment removed for export] *)
      unfold mprotect_model. rewrite mV_vmmaps.
      cbn [VMn vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit].
      rewrite maps_subtract_cons, maps_subtract_nil, app_nil_r.
      rewrite !u64_lit by lia.
      rewrite iv_subtract_suffix by (rewrite ?u64_lit, ?H8 by lia; lia).
      replace (bv_unsigned a + 4096 - bv_unsigned a)%Z with 4096%Z by lia.
      change (with_vmmaps (mkVmMapsFull RES [(a, Z_to_bv 64 8192)] [(a, Z_to_bv 64 4096)] brk brk LIM mbase sp0) (modelV (VMn a)))
        with (modelV (VMp a)).
      rewrite <- Q71.
      lazymatch type of HK with know_ok _ _ ?Mc _ => assert (HSI2 : SI Mc) by si_fill HSI end.
      apply (w65_R vals2 _ _ EXIT HL Q0 Q2 Q70 Q5 Q6 Q7); rewrite ?Q71; [lia | lia | exact HR | exact HK | exact HSI2].
  Qed.
End World.

(* [comment removed for export] *)
#[using="Type"] Theorem mmap_ok_world_g sp0 a0s path envv rdraw tid mem0 brk mbase fs0 stdin0
  (Hvsp : valid_sp sp0) (Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z) (Hbrk : valid_brk RSEGS brk)
  (Hplen : (length path <= 4095)%nat) fd3 K :
  exitT_branch sp0 a0s path envv rdraw tid brk fs0 stdin0 fd3 (above_eq sp0 mem0) K ->
  mmap_ok_branch_g sp0 a0s path envv rdraw tid mem0 brk mbase fs0 stdin0 fd3 (t_alt2 (t_die msg_oom fs0) (t_alt2 (t_die msg_oom fs0) K)).
Proof.
  intros EXIT. exact (mmap_ok_worldV sp0 a0s path envv rdraw tid brk mbase fs0 stdin0 Hvsp Htid Hbrk Hplen fd3
                        (above_eq sp0 mem0) (above_eq_step sp0 mem0) K EXIT).
Qed.

#[using="Type"] Theorem mmap_ok_world sp0 a0s path envv rdraw tid mem0 brk mbase fs0 stdin0
  (Hvsp : valid_sp sp0) (Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z) (Hbrk : valid_brk RSEGS brk)
  (Hplen : (length path <= 4095)%nat) K :
  exitT_branch sp0 a0s path envv rdraw tid brk fs0 stdin0 (FdFile path (Z_to_bv 64 0)) (above_eq sp0 mem0) K ->
  mmap_ok_branch sp0 a0s path envv rdraw tid mem0 brk mbase fs0 stdin0 (t_alt2 (t_die msg_oom fs0) (t_alt2 (t_die msg_oom fs0) K)).
Proof. exact (mmap_ok_world_g sp0 a0s path envv rdraw tid mem0 brk mbase fs0 stdin0 Hvsp Htid Hbrk Hplen (FdFile path (Z_to_bv 64 0)) K). Qed.
End FPW_5.

End RefW65m.

(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs.
Import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.DispatchCompute.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.PropExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.CatExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.CatSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SeqExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.StoreOk OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SimInv OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.ExitSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.ShapeAlg OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.Nodes OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.MmapSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.AllocSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.FileSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.AgentLib OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymExec2 OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymExec2Sound OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymRun OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymDrive OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymDriveX OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.Spec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.LibWritev OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefNodes OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.UbExitBase OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.UbExit OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefLayout OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.UbStartup OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.UbMainEntry OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.Hoare OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.Frame OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.MallocDefs OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.UbEnframeBase OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.UbEnframe OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.UbReadBase OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.UbWorld OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.UbTargetPre.
Import OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.UbPilotOOM_defs OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.UbPilotOOM.
Import OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymXfer OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymAbove OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefAbove RefW65_defs RefW65 RefW65m.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section FPW_6. Context {fx : PropExec.FPState}.

Definition off_image (x : Z) : Prop := (x + 1 <= 0x10000 \/ 0xe6000 <= x)%Z.

#[using="Type"] Lemma find_segment_skip : forall seg rest a n,
  (0 < n)%Z ->
  (a < Z.of_N (seg_base seg) \/ Z.of_N (seg_base seg) + Z.of_N (seg_size seg) < a + n)%Z ->
  find_segment (seg :: rest) a n = find_segment rest a n.
Proof.
  intros seg rest a n Hn H. cbn [find_segment].
  destruct (Z.leb_spec (Z.of_N (seg_base seg)) a); destruct (Z.leb_spec (a + n) (Z.of_N (seg_base seg) + Z.of_N (seg_size seg)));
    cbn [andb]; try reflexivity. lia.
Qed.

#[using="Type"] Lemma find_segment_off : forall a n, (0 < n)%Z -> (a + n <= 0x10000 \/ 0xe6000 <= a)%Z ->
  find_segment RSEGS a n = None.
Proof.
  intros a n Hn H. unfold ImgU.M.loaded_segments, ImgU_loaded_segments.
  rewrite 4 find_segment_skip; [reflexivity | exact Hn | | exact Hn | | exact Hn | | exact Hn |];
    cbn [seg_base seg_size ImgU_segment_000 ImgU_segment_001 ImgU_segment_002 ImgU_segment_003]; lia.
Qed.

#[using="Type"] Lemma seg_rom_off : forall x : word, off_image (bv_unsigned x) -> seg_rom RSEGS x = None.
Proof.
  intros x Hx. unfold seg_rom, memory_read. rewrite find_segment_off; [reflexivity | cbn; lia | unfold off_image in Hx; cbn; lia].
Qed.

#[using="Type"] Lemma wview_off : forall M (x : word), off_image (bv_unsigned x) -> wview RSEGS M x = M x.
Proof.
  intros M x Hx. unfold wview. destruct (M x); [reflexivity|].
  rewrite find_segment_off; [reflexivity | lia | unfold off_image in Hx; lia].
Qed.

#[using="Type"] Lemma rdn1_off : forall M (x : word) b, off_image (bv_unsigned x) ->
  rdn RSEGS M x 1 = Some [b] -> M x = Some b.
Proof.
  intros M x b Hx H. cbn [rdn] in H. rewrite (seg_rom_off x Hx) in H.
  destruct (M x) as [b0|]; [|discriminate]. injection H as ->. reflexivity.
Qed.

#[using="Type"] Lemma store_ok1_off : forall M (x : word), off_image (bv_unsigned x) ->
  store_ok RSEGS M x 1 = true -> M x <> None.
Proof.
  intros M x Hx H. cbn [store_ok] in H. rewrite (wview_off M x Hx) in H.
  destruct (M x); [discriminate | discriminate].
Qed.

#[using="Type"] Lemma u64_lit' : forall z, (0 <= z < 2 ^ 64)%Z -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. apply Z_to_bv_small. unfold bv_modulus. lia. Qed.

#[using="Type"] Lemma u0 : bv_unsigned (Z_to_bv 64 0) = 0%Z.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma cell_intro : forall M (x : word) n (v : word) (a z : Z),
  rdn RSEGS M x n = Some (word_to_le_bytes n v) ->
  x = Z_to_bv 64 a -> v = Z_to_bv 64 z -> cell M a n z.
Proof. intros M x n v a z H -> ->. exact H. Qed.

#[using="Type"] Lemma zero_bytes_intro : forall E M b k n a,
  kentry_ok RSEGS E M (KZero (SA b k) (ELit n)) -> (0 <= n < 2 ^ 64)%Z ->
  (bv_unsigned (edenot E b) + k)%Z = a -> zero_bytes M a n.
Proof.
  intros E M b k n a [Hf Hz] Hn Ha i Hi. unfold estart, elenZ in Hz. cbn [a_base a_off edenot] in Hz.
  rewrite u64_lit' in Hz by lia. rewrite <- Ha. apply Hz. lia.
Qed.

#[using="Type"] Lemma def_intro : forall E M b kk len a n,
  kentry_ok RSEGS E M (KWr (SA b kk) len) ->
  (bv_unsigned (edenot E b) + kk <= a)%Z -> (a + n <= bv_unsigned (edenot E b) + kk + len)%Z ->
  (a + n <= 0x10000 \/ 0xe6000 <= a)%Z -> (0 <= a)%Z -> (a + n <= 2 ^ 64)%Z ->
  forall i, (0 <= i < n)%Z -> M (Z_to_bv 64 (a + i)) <> None.
Proof.
  intros E M b kk len a n [Hf Hst] H1 H2 Hoff H0 H64 i Hi.
  unfold estart in Hst. cbn [a_base a_off] in Hst.
  specialize (Hst (a + i - (bv_unsigned (edenot E b) + kk))%Z 1%nat ltac:(lia) ltac:(cbn; lia)).
  replace (bv_unsigned (edenot E b) + kk + (a + i - (bv_unsigned (edenot E b) + kk)))%Z with (a + i)%Z in Hst by lia.
  refine (store_ok1_off M _ _ Hst). unfold off_image; rewrite u64_lit' by lia; lia.
Qed.

#[using="Type"] Lemma byte_intro : forall M a v,
  cell M a 1 v -> word_to_le_bytes 1 (Z_to_bv 64 v) = [Z_to_bv 8 v] ->
  (0 <= a)%Z -> (a + 1 <= 2 ^ 64)%Z -> (a + 1 <= 0x10000 \/ 0xe6000 <= a)%Z ->
  M (Z_to_bv 64 a) = Some (Z_to_bv 8 v).
Proof.
  intros M a v Hc Hw H0 H64 Hoff. unfold cell in Hc. rewrite Hw in Hc.
  apply rdn1_off; [unfold off_image; rewrite u64_lit' by lia; lia | exact Hc].
Qed.

#[using="Type"] Lemma img_clear_of_know : forall E M ivs,
  know_ok RSEGS E M (map (fun iv => KImg (fst iv) (snd iv)) ivs) ->
  Forall (fun iv => img_clear M (fst iv) (snd iv)) ivs.
Proof.
  intros E M ivs HK. unfold know_ok in HK. rewrite Forall_map in HK.
  eapply Forall_impl; [|exact HK]. intros [lo hi] (A & B & C). exact C.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma errno_some : forall M, exists bs,
  rdn RSEGS M (Z_to_bv 64 0xc4f74) 4 = Some bs /\ length bs = 4%nat.
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
End FPW_6.

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
Section FPW_7. Context {fx : PropExec.FPState}.

#[using="Type"] Lemma cell_join : forall M a n1 n2 v1 v2 v,
  cell M a n1 v1 -> cell M (a + Z.of_nat n1) n2 v2 ->
  word_to_le_bytes n1 (Z_to_bv 64 v1) ++ word_to_le_bytes n2 (Z_to_bv 64 v2) = word_to_le_bytes (n1 + n2) (Z_to_bv 64 v) ->
  (0 <= a)%Z -> (a + Z.of_nat n1 < 2 ^ 64)%Z -> cell M a (n1 + n2) v.
Proof.
  unfold cell. intros M a n1 n2 v1 v2 v H1 H2 Hw Ha Hn. rewrite <- Hw.
  apply rdn_app; [exact H1|]. rewrite w_add_nat, u_small by lia. exact H2.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma kwr_window : forall E M kn b kk len base,
  know_ok RSEGS E M kn -> kderive RSEGS kn (KWr (SA b kk) len) = true ->
  (bv_unsigned (edenot E b) + kk)%Z = base ->
  forall d m, (0 <= d)%Z -> (d + Z.of_nat m <= len)%Z -> store_ok RSEGS M (Z_to_bv 64 (base + d)) m = true.
Proof.
  intros E M kn b kk len base HK Hd Hb d m H0 Hm.
  destruct (kderive_sound RSEGS E M kn _ HK Hd) as [Hf Hst]. unfold estart in Hst. cbn [a_base a_off] in Hst.
  rewrite Hb in Hst. apply Hst; assumption.
Qed.

(* [comment removed for export] *)
Definition fG (i : nat) : nat := if Nat.eqb i 2 then 70%nat else if Nat.eqb i 3 then 72%nat else if Nat.eqb i 7 then 6%nat else 7%nat.
Definition fT (i : nat) : nat := if Nat.eqb i 2 then 71%nat else if Nat.eqb i 3 then 72%nat else if Nat.eqb i 7 then 6%nat else 7%nat.

(* [comment removed for export] *)
End FPW_7.

Ltac kreg HR :=
  lazymatch goal with |- getr ?R ?r = _ =>
  lazymatch type of HR with regs_ok ?E ?sr R =>
    let e := eval vm_compute in (sr_get sr r) in
    rewrite (reg_val E sr R r HR); change (sr_get sr r) with e; kside
  end end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FPW_8. Context {fx : PropExec.FPState}.


Section World.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable uid : word.   (* [comment removed for export] *)
  Variable hw : word.    (* [comment removed for export] *)
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Variable tid : word.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable brk : word.
  Variable mbase : word.
  Variable fs0 : Fs.
  Variable stdin0 : AmbIn.
  Variable fdata : list byte.
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 [a0s; path] envv uid hw rdraw tid regs0 mem0.
  Hypothesis Hbrk : valid_brk RSEGS brk.
  Hypothesis Hfile : fs_lookup fs0 path = Some fdata.
  Hypothesis Hpne : path <> [].
  Hypothesis Hpns : path_has_slash path = false.   (* [comment removed for export] *)
  Hypothesis Hpnd : path_is_dirref path = false.   (* [comment removed for export] *)
  Hypothesis Hplen : (length path <= 4095)%nat.
  Variable fd3 : FdEntry.      (* [comment removed for export] *)
  Variable SI : (word -> option byte) -> Prop.   (* [comment removed for export] *)
  Hypothesis SI_step : forall M M' : word -> option byte,
    (forall a : word, (bv_unsigned sp0 <= bv_unsigned a)%Z -> M' a = M a) -> SI M -> SI M'.

  #[local] Notation ENVv := (ENV a0s path).
  #[local] Notation modelV := (modelV tid fs0 stdin0 fd3).

  (* [comment removed for export] *)
  Definition vm_small (VM : VmMaps) (gm : word) : Prop :=
    vm_reserved VM = segments_reserved RSEGS /\ vm_limit VM = LIM
    /\ (length (vm_maps VM) <= 4)%nat
    /\ In (gm, Z_to_bv 64 69632) (vm_maps VM)
    /\ Forall (fun p => (0 < bv_unsigned (snd p) <= 69632)%Z /\ (bv_unsigned (fst p) + bv_unsigned (snd p) <= 2 ^ 64)%Z) (vm_maps VM)
    /\ seps (vm_maps VM).

  (* [comment removed for export] *)
  Definition after_malloc (K : TSet) : Prop :=
    forall (R : bvmap 5 word) (M : word -> option byte) (VM : VmMaps) (mb gm : word) (area brkv mas : Z),
      area = (bv_unsigned mb + 4096)%Z ->
      read_pre sp0 (p1 sp0 a0s path envv) mb gm (canary_w rdraw) (secret_w rdraw) R M ->   (* [comment removed for export] *)
      world0 (bv_unsigned sp0) area (bv_unsigned gm) brkv mas (bv_unsigned tid) (bv_unsigned (secret_w rdraw)) M ->
      main_frame (bv_unsigned sp0) M ->
      vm_pre VM sp0 mb gm -> vm_small VM gm ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x32688) M (seg_rom RSEGS))
                              (model_pre path VM stdin0 fs0 tid)) K.

  (* [comment removed for export] *)
  Definition after_malloc_gen (K : TSet) : Prop :=
    forall (R : bvmap 5 word) (M : word -> option byte) (VM : VmMaps) (mb gm : word) (area brkv mas : Z),
      area = (bv_unsigned mb + 4096)%Z ->
      read_pre sp0 (p1 sp0 a0s path envv) mb gm (canary_w rdraw) (secret_w rdraw) R M ->   (* [comment removed for export] *)
      world0 (bv_unsigned sp0) area (bv_unsigned gm) brkv mas (bv_unsigned tid) (bv_unsigned (secret_w rdraw)) M ->
      main_frame (bv_unsigned sp0) M ->
      vm_pre VM sp0 mb gm -> vm_small VM gm -> SI M ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x32688) M (seg_rom RSEGS))
                              (mkModelA (fdsV fd3) VM stdin0 fs0 None (Some tid) None)) K.

  #[using="Type"] Lemma modelV_eq : forall VM, modelV VM = mkModelA (fdsV fd3) VM stdin0 fs0 None (Some tid) None.
  Proof. intros VM. reflexivity. Qed.

  (* [comment removed for export] *)
  #[using="Hva Hve Hvsp Hplen"] Lemma p1_range : (0x7fff80000000 <= bv_unsigned (p1 sp0 a0s path envv) <= 0x800000400000)%Z.
  Proof.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi. unfold sp_window_lo, sp_window_hi in *.
    unfold p1. rewrite (u_cat_argv_ptr sp0 [a0s; path] envv Hva Hve) by (cbn; lia || (unfold sp_window_lo, sp_window_hi; cbn; lia)).
    pose proof (struct_av_bound [a0s; path] envv Hva Hve).
    pose proof (CatExec.total_arg_bytes_firstn_le 1 [a0s; path]). lia.
  Qed.

  Variable K : TSet.

  #[using="Hva Hve Hvsp Htid Hbrk Hplen"] Lemma w65_exitG : after_malloc_gen K -> exitG_branch sp0 a0s path envv rdraw tid brk fs0 stdin0 fd3 SI K.
  Proof.
    intros AM vals R M VM HL P0 P2 P70 P5 P6 P7 HR HK HVM HVS HSI.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi. pose proof (proj2 (proj2 Hvsp)) as SPal.
    unfold sp_window_lo, sp_window_hi in *.
    pose proof (brk_lo brk Hbrk) as Blo. pose proof (brk_hi path brk Hbrk Hplen) as Bhi. pose proof (brk_al brk Hbrk) as Bal.
    pose proof (know_nth RSEGS _ _ knZ ltac:(let i := kidx knZ (is_krange gx) in exact i) _ HK eq_refl)
      as Kgm; cbn [kentry_ok edenot ev ENV ENVr gx bx ax] in Kgm.
    pose proof (know_nth RSEGS _ _ knZ ltac:(let i := kidx knZ (is_kalign gx) in exact i) _ HK eq_refl)
      as Kga; cbn [kentry_ok edenot ev ENV ENVr gx bx ax] in Kga.
    pose proof (know_nth RSEGS _ _ knZ ltac:(let i := kidx knZ (is_kdisj bx gx) in exact i) _ HK eq_refl)
      as Kgd; cbn [kentry_ok] in Kgd; unfold estart in Kgd; cbn [a_base a_off edenot ev ENV ENVr gx bx ax] in Kgd; rewrite P70 in Kgd.
    pose proof (know_nth RSEGS _ _ knZ ltac:(let i := kidx knZ (is_kdisj (EVar 0) gx) in exact i) _ HK eq_refl)   (* [comment removed for export] *)
      as Kgs; cbn [kentry_ok] in Kgs; unfold estart in Kgs; cbn [a_base a_off edenot ev ENV ENVr gx bx ax] in Kgs; rewrite P0 in Kgs.
    pose proof p1_range as P1r.
    pose proof (u64_range brk) as Bu. pose proof (u64_range sp0) as Su.
    rewrite modelV_eq.
    apply (AM R M VM brk (vals_ev vals 72) (bv_unsigned brk + 4096)%Z (bv_unsigned brk + 8192)%Z 0%Z).
    - reflexivity.
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
      + intros x0 x1 x4 x5 x6 extra ebs.
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
      + lia.   (* [comment removed for export] *)
      + lia.   (* [comment removed for export] *)
      + lia.
      + lia.
      + lia.
      + pose proof (u64_range (secret_w rdraw)). lia.   (* [comment removed for export] *)
      + exact Htid.
      + destruct (errno_some M) as (bs & Hbs & Hlen). exists (bytes_le_to_Z bs).
        pose proof (SX2S.bytes_le_to_Z_bound bs) as Hb. rewrite Hlen in Hb.
        split; [cbn in Hb; lia|]. unfold cell. rewrite Hbs, word_to_le_bytes_of_lez by (assumption || lia). reflexivity.
      + exists (bv_unsigned (canary_w rdraw)). split; [exact (u64_range (canary_w rdraw)) | kcell HK].   (* [comment removed for export] *)
      + apply (img_clear_of_know (ENVv vals)). apply (kderive_all_sound RSEGS _ M knZ); [exact HK | vm_compute; reflexivity].
    - (* [comment removed for export] *)
      constructor. all: kcell HK.
    - exact HVM.
    - (* [comment removed for export] *)
      destruct HVS as (Hr & Hl & Hm). unfold vm_small. rewrite Hr, Hl.
      split; [reflexivity|]. split; [reflexivity|].
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

  #[using="Hva Hve Hvsp Htid Hbrk Hplen"] Lemma w65_exitT : after_malloc_gen K -> exitT_branch sp0 a0s path envv rdraw tid brk fs0 stdin0 fd3 SI K.
  Proof.
    intros AM vals R M VM HL P0 P2 P70 P5 P6 P7 HR HK HVM HVS HSI.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi. pose proof (proj2 (proj2 Hvsp)) as SPal.
    unfold sp_window_lo, sp_window_hi in *.
    pose proof (brk_lo brk Hbrk) as Blo. pose proof (brk_hi path brk Hbrk Hplen) as Bhi. pose proof (brk_al brk Hbrk) as Bal.
    pose proof (know_nth RSEGS _ _ knZm ltac:(let i := kidx knZm (is_krange gx) in exact i) _ HK eq_refl)
      as Kgm; cbn [kentry_ok edenot ev ENV ENVr gx bx ax] in Kgm.
    pose proof (know_nth RSEGS _ _ knZm ltac:(let i := kidx knZm (is_kalign gx) in exact i) _ HK eq_refl)
      as Kga; cbn [kentry_ok edenot ev ENV ENVr gx bx ax] in Kga.
    pose proof (know_nth RSEGS _ _ knZm ltac:(let i := kidx knZm (is_kdisj ax gx) in exact i) _ HK eq_refl)
      as Kgd; cbn [kentry_ok] in Kgd; unfold estart in Kgd; cbn [a_base a_off edenot ev ENV ENVr gx bx ax] in Kgd.
    pose proof (know_nth RSEGS _ _ knZm ltac:(let i := kidx knZm (is_kdisj (EVar 0) gx) in exact i) _ HK eq_refl)   (* [comment removed for export] *)
      as Kgs; cbn [kentry_ok] in Kgs; unfold estart in Kgs; cbn [a_base a_off edenot ev ENV ENVr gx bx ax] in Kgs; rewrite P0 in Kgs.
    pose proof (know_nth RSEGS _ _ knZm ltac:(let i := kidx knZm (is_kdisj (EVar 0) ax) in exact i) _ HK eq_refl)   (* [comment removed for export] *)
      as Kas; cbn [kentry_ok] in Kas; unfold estart in Kas; cbn [a_base a_off edenot ev ENV ENVr gx bx ax] in Kas; rewrite P0 in Kas.
    pose proof (know_nth RSEGS _ _ knZm ltac:(let i := kidx knZm (is_krange ax) in exact i) _ HK eq_refl)
      as Kam; cbn [kentry_ok edenot ev ENV ENVr gx bx ax] in Kam.
    pose proof (know_nth RSEGS _ _ knZm ltac:(let i := kidx knZm (is_kalign ax) in exact i) _ HK eq_refl)
      as Kaa; cbn [kentry_ok edenot ev ENV ENVr gx bx ax] in Kaa.
    pose proof (know_nth RSEGS _ _ knZm ltac:(let i := kidx knZm (is_kdisj (ELit 0) ax) in exact i) _ HK eq_refl)
      as Kai; cbn [kentry_ok] in Kai; unfold estart in Kai; cbn [a_base a_off edenot ev ENV ENVr gx bx ax] in Kai; rewrite u0 in Kai.
    pose proof (u64_range (vals_ev vals 71)) as Au.
    pose proof p1_range as P1r.
    pose proof (u64_range brk) as Bu. pose proof (u64_range sp0) as Su.
    rewrite modelV_eq.
    apply (AM R M VM (vals_ev vals 71) (vals_ev vals 72) (bv_unsigned (vals_ev vals 71) + 4096)%Z (2 ^ 64 - 1)%Z 1%Z).
    - reflexivity.
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
      + unfold stack_writable. apply (kwr_window (ENVv vals) M knZm (EVar 0) (-8388608) 8388608); [exact HK | vm_compute; reflexivity | cbn [edenot ev ENV ENVr gx bx ax]; pins; lia].
      + unfold group_writable. apply (kwr_window (ENVv vals) M knZm gx 0 69632); [exact HK | vm_compute; reflexivity | cbn [edenot ev ENV ENVr gx bx ax]; pins; lia].
      + unfold meta_writable. apply (kwr_window (ENVv vals) M knZm ax 4096 4096); [exact HK | vm_compute; reflexivity | cbn [edenot ev ENV ENVr gx bx ax]; pins; lia].
      + destruct (errno_some M) as (bs & Hbs & Hlen). exists (Z_to_bv 64 (bytes_le_to_Z bs)).
        rewrite Hbs, word_to_le_bytes_of_lez by (assumption || lia). reflexivity.
      + intros x0 x1 x4 x5 x6 extra ebs.
        apply (know_ok_ren RSEGS (ENVv vals) _ M fT [2;3;7;8]%nat kn_M1).
        * intros i Hi. destruct Hi as [<-|[<-|[<-|[<-|[]]]]]; cbn [ev ENV fT Nat.eqb vals_ev nth app]; pins; reflexivity.
        * vm_compute. reflexivity.
        * apply (kderive_all_sound RSEGS _ M knZm); [exact HK | vm_compute; reflexivity].
    - (* [comment removed for export] *)
      constructor.
      all: try kcell HK.
      all: try kzero HK.
      + apply (cell_join M _ 4 4 101 0); [kcell HK | kcell HK | reflexivity | pins; lia | pins; lia].
      + apply (cell_join M _ 4 4 0 0); [kcell HK | kcell HK | reflexivity | pins; lia | pins; lia].
      + kdef HK ax 4096%Z 4096%Z.
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
      + replace (bv_unsigned (vals_ev vals 71) + 4096)%Z with (bv_unsigned (vals_ev vals 71) + 1 * 4096)%Z by lia. rewrite Z_mod_plus_full. exact (proj2 Kaa).
      + exact (proj2 Kga).
      + lia.
      + lia.
      + lia.   (* [comment removed for export] *)
      + lia.   (* [comment removed for export] *)
      + lia.
      + lia.
      + lia.
      + pose proof (u64_range (secret_w rdraw)). lia.   (* [comment removed for export] *)
      + exact Htid.
      + destruct (errno_some M) as (bs & Hbs & Hlen). exists (bytes_le_to_Z bs).
        pose proof (SX2S.bytes_le_to_Z_bound bs) as Hb. rewrite Hlen in Hb.
        split; [cbn in Hb; lia|]. unfold cell. rewrite Hbs, word_to_le_bytes_of_lez by (assumption || lia). reflexivity.
      + exists (bv_unsigned (canary_w rdraw)). split; [exact (u64_range (canary_w rdraw)) | kcell HK].   (* [comment removed for export] *)
      + apply (img_clear_of_know (ENVv vals)). apply (kderive_all_sound RSEGS _ M knZm); [exact HK | vm_compute; reflexivity].
    - (* [comment removed for export] *)
      constructor. all: kcell HK.
    - exact HVM.
    - (* [comment removed for export] *)
      destruct HVS as (Hr & Hl & Hm). unfold vm_small. rewrite Hr, Hl.
      split; [reflexivity|]. split; [reflexivity|].
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
  #[using="Hva Hve Hvsp Htid Hbrk Hplen SI_step"] Theorem brk_ok_semV : after_malloc_gen K ->
    brk_ok_entry sp0 a0s path envv rdraw tid brk mbase fs0 stdin0 fd3 SI (t_alt2 (t_die msg_oom fs0) K).
  Proof. intros AM. apply brk_ok_worldV; try assumption. apply w65_exitG, AM. Qed.

  #[using="Hva Hve Hvsp Htid Hbrk Hplen SI_step"] Theorem mmap_ok_semV : after_malloc_gen K ->
    mmap_ok_entry sp0 a0s path envv rdraw tid brk mbase fs0 stdin0 fd3 SI (t_alt2 (t_die msg_oom fs0) (t_alt2 (t_die msg_oom fs0) K)).
  Proof. intros AM. apply mmap_ok_worldV; try assumption. apply w65_exitT, AM. Qed.
End World.

(* [comment removed for export] *)
#[using="Type"] Theorem brk_ok_sem_g sp0 a0s path envv rdraw tid mem0 brk mbase fs0 stdin0
  (Hva : valid_argv [a0s; path]) (Hve : valid_envp envv)
  (Hvsp : valid_sp sp0) (Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z) (Hbrk : valid_brk RSEGS brk)
  (Hplen : (length path <= 4095)%nat) fd3 K :
  after_malloc_gen sp0 a0s path envv rdraw tid fs0 stdin0 fd3 (above_eq sp0 mem0) K ->
  brk_ok_branch_g sp0 a0s path envv rdraw tid mem0 brk mbase fs0 stdin0 fd3 (t_alt2 (t_die msg_oom fs0) K).
Proof.
  intros AM. exact (brk_ok_semV sp0 a0s path envv rdraw tid brk mbase fs0 stdin0 Hva Hve Hvsp Htid Hbrk Hplen fd3
                      (above_eq sp0 mem0) (above_eq_step sp0 mem0) K AM).
Qed.

#[using="Type"] Theorem mmap_ok_sem_g sp0 a0s path envv rdraw tid mem0 brk mbase fs0 stdin0
  (Hva : valid_argv [a0s; path]) (Hve : valid_envp envv)
  (Hvsp : valid_sp sp0) (Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z) (Hbrk : valid_brk RSEGS brk)
  (Hplen : (length path <= 4095)%nat) fd3 K :
  after_malloc_gen sp0 a0s path envv rdraw tid fs0 stdin0 fd3 (above_eq sp0 mem0) K ->
  mmap_ok_branch_g sp0 a0s path envv rdraw tid mem0 brk mbase fs0 stdin0 fd3 (t_alt2 (t_die msg_oom fs0) (t_alt2 (t_die msg_oom fs0) K)).
Proof.
  intros AM. exact (mmap_ok_semV sp0 a0s path envv rdraw tid brk mbase fs0 stdin0 Hva Hve Hvsp Htid Hbrk Hplen fd3
                      (above_eq sp0 mem0) (above_eq_step sp0 mem0) K AM).
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem brk_ok_sem sp0 a0s path envv rdraw tid mem0 brk mbase fs0 stdin0
  (Hva : valid_argv [a0s; path]) (Hve : valid_envp envv)
  (Hvsp : valid_sp sp0) (Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z) (Hbrk : valid_brk RSEGS brk)
  (Hplen : (length path <= 4095)%nat) K :
  after_malloc sp0 a0s path envv rdraw tid fs0 stdin0 K ->
  brk_ok_branch sp0 a0s path envv rdraw tid mem0 brk mbase fs0 stdin0 (t_alt2 (t_die msg_oom fs0) K).
Proof.
  intros AM. apply (brk_ok_sem_g sp0 a0s path envv rdraw tid mem0 brk mbase fs0 stdin0 Hva Hve Hvsp Htid Hbrk Hplen).
  intros R M VM mb gm area brkv mas EA RP W MF VP VS _. exact (AM R M VM mb gm area brkv mas EA RP W MF VP VS).
Qed.

#[using="Type"] Theorem mmap_ok_sem sp0 a0s path envv rdraw tid mem0 brk mbase fs0 stdin0
  (Hva : valid_argv [a0s; path]) (Hve : valid_envp envv)
  (Hvsp : valid_sp sp0) (Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z) (Hbrk : valid_brk RSEGS brk)
  (Hplen : (length path <= 4095)%nat) K :
  after_malloc sp0 a0s path envv rdraw tid fs0 stdin0 K ->
  mmap_ok_branch sp0 a0s path envv rdraw tid mem0 brk mbase fs0 stdin0 (t_alt2 (t_die msg_oom fs0) (t_alt2 (t_die msg_oom fs0) K)).
Proof.
  intros AM. apply (mmap_ok_sem_g sp0 a0s path envv rdraw tid mem0 brk mbase fs0 stdin0 Hva Hve Hvsp Htid Hbrk Hplen).
  intros R M VM mb gm area brkv mas EA RP W MF VP VS _. exact (AM R M VM mb gm area brkv mas EA RP W MF VP VS).
Qed.

End FPW_8.
