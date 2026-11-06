(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require As0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HPropExec HSymExec2 HSymExec2Sound HSymRun HSymDrive HSymDriveX HRefMemcpyLib HSymDriveH4 HSymAux.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AsShadow AsPrintfFirst AsSxKit AsStdioCall.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_AsTail_usage_defs () := "I47Corelib4Init9Datatypes4list00K79OSSVerify5KrLib3bpA2HF9HSymExec23SX24expr02C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z03K79OSSVerify5KrLib3bpA2HF9HSymExec23SX24expr01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib3bpA2HF9HSymExec23SX24expr03C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02K79OSSVerify5KrLib3bpA2HF9HSymExec23SX28sidecond01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init5Logic2eq00I47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic3and01I47Corelib4Init9Datatypes4prod00C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC79OSSVerify5KrLib3bpA2HF9HSymExec23SX25s_logC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpA2HF9HSymExec23SX25carryC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2HF7HSymAux;log_coveredC1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib3bpA2HF9HSymExec23SX28sidecond00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05K4ELinuxProcessSemantics5Riscv5Instr5aluop06K4ELinuxProcessSemantics5Riscv5Instr5aluop01K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I79OSSVerify5KrLib3bpA2HF9HSymExec23SX29sym_state00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib3bpA2HF9HSymExec23SX27scripts00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs2rBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs4scsBC1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib3bpA2HF9HSymExec23SX26kentry00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs4knV0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs:ot_regionsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs2rCC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs4scsCC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs4knC0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs2rDC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs4scsDC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs3knCC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K79OSSVerify5KrLib3bpA2HF9HSymExec23SX24expr04C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib3bpA2HF9HSymExec23SX25saddr01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib3bpA2HF9HSymExec23SX28sidecond06C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03K47Corelib7Numbers7BinNums1Z01c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs2rEC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs4scsEC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs4knE0C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib3bpA2HF9HSymExec23SX24expr07C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond04c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs2rFC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs4scsFC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs5knF0_C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs3rF0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs5scsF0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs5knF00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs2rGC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs4scsGC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs4knG0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs2rHC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs4scsHC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs4knH0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs3rF4C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs5scsF4C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs5knF40C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs3rG4C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs5scsG4C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs5knG40C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs3rH4C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs5scsH4C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs5knH40C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs4rFs1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs6scsFs1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs5knFs0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs4rFs2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs6scsFs2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs6knFs20C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs4rFs3C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs6scsFs3C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs6knFs30C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs3rGsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs5scsGsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs5knGs0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs3rHsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs5scsHsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs5knHs0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs4rG3sC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs6scsG3sC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs6knG3s0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs4rH3sC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs6scsH3sC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs6knH3s0C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00K79OSSVerify5KrLib3bpA2HF9HSymExec23SX26kentry06C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib3bpA2HF9HSymExec23SX26kentry01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib3bpA2HF9HSymExec23SX26kentry05C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib3bpA2HF9HSymExec23SX26kentry07C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib3bpA2HF9HSymExec23SX26kentry04C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib3bpA3Drv;AsStdioCall9stdio_res01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib3bpA3Drv;AsStdioCall:stdio_callC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib3bpA2HF9HSymExec23SX26kentry02C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpA2HF9HSymExec23SX24s_pcC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I79OSSVerify5KrLib3bpA2HF9HSymExec23SX24expr00C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K4ELinuxProcessSemantics5Riscv5Instr5aluop07I69OSSVerify5KrLib3bpA3Drv;AsStdioCall9stdio_res00C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop02c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs4ARIPC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs7AMEMCPYC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs3rIsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs<ASTDIO_WRITEC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs8AMAINEPIC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs4rI3sC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs4srHsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs4knHsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs5scOFsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs5srG3sC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs5knG3sC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs5scG3sC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs5srH3sC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs5knH3sC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs5scH3sC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs;ASTRNLEN_TRC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs2rIC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs3rG3C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs3rH3C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs3rI3C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs3rI4C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs3srHC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs3knHC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs4scOFC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs4srG3C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs4knG3C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs4scG3C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs4srH3C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs4knH3C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs4scH3C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs4srF4C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs4knF4C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs4scF4C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs4srH4C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs4knH4C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_usage_defs4scH4C1?~~~~~~~~~~~~~~~".
Import ListNotations.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import SX2. Import SX2S.
Open Scope Z_scope.

Abbreviation RSEGS := Asan.M.loaded_segments.

Definition AMEMCPY : Z := 0x1750fc.
Definition AMEMCPY_RET : Z := 0xb9c38.
Definition ASTRNLEN_TR : Z := 0xa3a38.
Definition ASTRNLEN_RET : Z := 0xa3e9c.
Definition ASTDIO_WRITE : Z := 0x16b42c.
Definition AEXIT : Z := 0x163ad4.
Definition AMAINEPI : Z := 0xe89a8.
Definition ARIP : Z := 0xbc168.
Definition STOPT : list Z := [AMEMCPY; ASTRNLEN_TR; ASTDIO_WRITE; AEXIT; AMAINEPI; ARIP].
Definition FUELT : nat := 20000.
Definition scr0 : scripts := SCR [] [] [].
Definition runT (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUELT true STOPT scr ss [].
Definition kn_afterT (r : sym_state * list sidecond * scripts) (kn : list kentry) : list kentry :=
  fst (fst (carry (s_log (fst (fst r))) kn [])).
Definition sc_of (nv : nat) (sr : list expr) (kn : list kentry) : stdio_res :=
  match stdio_call nv sr kn with
  | Some r => r
  | None => SCR_ 0 0 0 (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) [] []
  end.
Definition KEPT_MC : list nat := map ridx callee_kept.

Definition KEPT_MCI : list nat := List.filter (fun i => negb (Nat.eqb i 19 || Nat.eqb i 20)) KEPT_MC.
Definition KEPT_CS : list nat := map ridx callee_saved.
Definition spx (k : Z) : expr := EAlu ALU_ADD (EVar 0) (ELit k).

Definition rip_clob (i : nat) : bool :=
  match i with 5 | 11 | 12 | 13 | 14 | 15 | 16 | 17 => true | _ => false end%nat.
Definition after_rip (base : nat) (sr : list expr) : list expr :=
  map (fun i => if rip_clob i then EVar (base + i) else match i with 10%nat => ELit 0 | _ => nth i sr (ELit 0) end) (seq 0 32).
Definition RIP_FR : Z := 80.
Definition OT_FR : Z := 6000.
Definition FMT : Z := 0x163a4.
Definition NPRE : Z := 7.
Definition NSUF : Z := 7.
Definition IHI : Z := 0x80000000.
Definition BUF_LO : Z := (-592).
Definition BUF_HI : Z := (-512).
Definition PX : expr := EVar 141.

Definition srV0 : list expr :=
  map (fun i => match i with
    | 0 => ELit 0 | 1 => ELit 0xa9018 | 2 => spx (-240) | 4 => ELit 0x6c3f18
    | 8 => ELit FMT | 9 => ELit 0x187f60 | 10 => ELit 0x187f60 | 11 => ELit FMT | 12 => spx (-176) | 18 => spx (-176)
    | _ => EVar (35 + i) end)%nat (seq 0 32).

Definition ot_cells : list (Z * nat * Z) :=
  [(0x185608, 8%nat, 0x16cadc); (0x185780, 8%nat, 0x1750fc); (0x185788, 8%nat, 0x175500); (0x185730, 8%nat, 0x175c80); (0x1855c0, 8%nat, 0x175000);
   (0x18f6f8, 8%nat, 0x7fff8000); (0x1903d8, 1%nat, 0x1); (0x1903d9, 1%nat, 0x1); (0x22127c, 1%nat, 0x1); (0x221323, 1%nat, 0x1);
   (0x187f60, 4%nat, 0x5); (0x187f80, 8%nat, 0x0); (0x187f88, 8%nat, 0x0); (0x187f98, 8%nat, 0x0); (0x187fa8, 8%nat, 0x16b42c);
   (0x187fb8, 8%nat, 0x6e4730); (0x187fc0, 8%nat, 0x0); (0x187fd8, 4%nat, 0x2); (0x187fe8, 4%nat, 0x0); (0x187fec, 4%nat, 0xffffffff); (0x187ff0, 4%nat, 0xffffffff);
   (0x7fffac70, 8%nat, 0x0); (0x7fffac78, 8%nat, 0x0)].

Definition OT_SHOFFS : list Z := [(-592); (-586)].
Definition OT_SHOFFS2 : list Z := [(-592); (-586); (-585)].
Definition OT_SHX : list expr := [(EAlu ALU_AND (EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EAlu ALU_ADD (EVar 2) (EVar 141)) (ELit (-1))) (ELit 3)) (ELit 2147450880)) (ELit (-8))); (EAlu ALU_AND (EAlu ALU_ADD (EAlu ALU_SRL (EVar 2) (ELit 3)) (ELit 2147450880)) (ELit (-8))); (EAlu ALU_AND (EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) (EVar 141)) (ELit (-586))) (ELit 3)) (ELit 2147450880)) (ELit (-8))); (EAlu ALU_AND (EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) (EVar 141)) (ELit (-585))) (ELit 3)) (ELit 2147450880)) (ELit (-8))); (EAlu ALU_AND (EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) (EVar 141)) (ELit (-579))) (ELit 3)) (ELit 2147450880)) (ELit (-8)))].
Fixpoint shxkn (l : list expr) : list kentry :=
  match l with [] => [] | e :: r => KRange e 0x20000000000 0x10007fff8000 :: KZero (SA e 0) (ELit 8) :: shxkn r end.

Definition knV0 : list kentry :=
  [KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000; KWr (SA (EVar 0) (-128 - OT_FR)) OT_FR;
   KRange (EVar 2) AHI_LO AAPP_HI;
   KImg 0x10000 0x91000; KImg 0x17c000 0x185000;
   KWord (SA (EVar 0) (-176)) 8 (EVar 2); KWord (SA (EVar 0) (-184)) 8 (ELit 0xe8960);
   KWord (SA (EVar 0) (-192)) 8 (EVar 11); KWord (SA (EVar 0) (-200)) 8 (EVar 12); KWord (SA (EVar 0) (-208)) 8 (EVar 21);
   KWord (SA (ELit 0) 0x6e3f58) 8 (EVar 1); KWr (SA (ELit 0) 0x187f60) 232]
  ++ shkn OT_SHOFFS
  ++ kn_cells ot_cells.

Definition not_px_range (k : kentry) : bool := match k with KRange (EVar 141) _ _ => false | _ => true end.
Definition px_range (lo hi : Z) (kn : list kentry) : list kentry := KRange PX lo hi :: List.filter not_px_range kn.

Definition kn_readd (plo phi : Z) (kn : list kentry) : list kentry := px_range plo phi (shxkn OT_SHX ++ shkn OT_SHOFFS2 ++ kn).

Definition ssB0 : sym_state := SS 0x16cadc srV0 [] knV0 67.
Definition rB := Eval vm_compute in runT (SCR [false] [] []) ssB0.
Definition srB : list expr := Eval vm_compute in s_regs (fst (fst rB)).
Definition knB : list kentry := Eval vm_compute in kn_afterT rB knV0.

Definition logM1 : list sentry := [SE (SA (EVar 0) (-586)) 1 (ELit 32);
   SE (SA (EVar 0) (-588)) 2 (ELit 14949);
   SE (SA (EVar 0) (-592)) 4 (ELit 1734439797)].
Definition knC0 : list kentry := Eval vm_compute in fst (fst (carry logM1 knB [])).
Definition srC0 : list expr := Eval vm_compute in sr_after_call_j srB KEPT_MC 67.

Definition ssC0 : sym_state := SS AMEMCPY_RET srC0 [] knC0 99.
Definition rC := Eval vm_compute in runT (SCR [] [] []) ssC0.
Definition srC : list expr := Eval vm_compute in s_regs (fst (fst rC)).
Definition knC : list kentry := Eval vm_compute in kn_afterT rC knC0.
Definition srD0 : list expr := Eval vm_compute in sr_after_call_j srC KEPT_MC 99.

Definition ssD0 : sym_state := SS AMEMCPY_RET srD0 [] knC 131.
Definition rD := Eval vm_compute in runT (SCR [] [] []) ssD0.
Definition srD : list expr := Eval vm_compute in s_regs (fst (fst rD)).
Definition knD : list kentry := Eval vm_compute in kn_afterT rD knC.

Definition knE0 : list kentry := Eval vm_compute in kn_readd 0 131071 (kn_cut 0 (-1152 - 4400) (-1152) IHI knD).
Definition srE0 : list expr := Eval vm_compute in sr_after_call_j srD KEPT_CS 131.

Definition ssE0 : sym_state := SS ASTRNLEN_RET srE0 [] knE0 163.
Definition rE := Eval vm_compute in runT (SCR [false] [ELit 0] []) ssE0.
Definition srE : list expr := Eval vm_compute in s_regs (fst (fst rE)).
Definition knE : list kentry := Eval vm_compute in kn_afterT rE knE0.
Definition srF0 : list expr := Eval vm_compute in sr_after_call_j srE KEPT_MC 163.

Definition FQMAX : Z := 64.
Definition knF0_ : list kentry := Eval vm_compute in px_range 1 FQMAX knE.
Definition ssF0 : sym_state := SS AMEMCPY_RET srF0 [] knF0_ 195.
Definition rF := Eval vm_compute in runT (SCR [true; false; true; false; false] [] []) ssF0.
Definition srF : list expr := Eval vm_compute in s_regs (fst (fst rF)).
Definition knF : list kentry := Eval vm_compute in kn_afterT rF knF0_.
Definition knG0 : list kentry := Eval vm_compute in kn_readd 0 66 (kn_cut 0 (BUF_LO + NPRE) BUF_HI IHI knF).
Definition srG0 : list expr := Eval vm_compute in sr_after_call_j srF KEPT_MCI 195.

Definition knF00 : list kentry := Eval vm_compute in px_range 0 0 knE.
Definition rF0 := Eval vm_compute in runT (SCR [false; true] [] []) (SS AMEMCPY_RET srF0 [] knF00 195).
Definition srF0' : list expr := Eval vm_compute in s_regs (fst (fst rF0)).
Definition knF0' : list kentry := Eval vm_compute in kn_afterT rF0 knF00.
Definition knG00 : list kentry := Eval vm_compute in kn_readd 0 66 (kn_cut 0 (BUF_LO + NPRE) BUF_HI IHI knF0').

Definition ssG0 : sym_state := SS AMEMCPY_RET srG0 [] knG0 227.
Definition rG := Eval vm_compute in runT (SCR [false] [] []) ssG0.
Definition srG : list expr := Eval vm_compute in s_regs (fst (fst rG)).
Definition knG : list kentry := Eval vm_compute in kn_afterT rG knG0.
Definition knH0 : list kentry := Eval vm_compute in kn_readd 0 66 (kn_cut 0 (BUF_LO + NPRE) BUF_HI IHI knG).
Definition srH0 : list expr := Eval vm_compute in sr_after_call_j srG KEPT_MC 227.

Definition ssH0 : sym_state := SS AMEMCPY_RET srH0 [] knH0 259.
Definition rH := Eval vm_compute in runT (SCR [] [] []) ssH0.
Definition srH : list expr := Eval vm_compute in s_regs (fst (fst rH)).
Definition knH : list kentry := Eval vm_compute in kn_afterT rH knH0.
Definition scOF : stdio_res := Eval vm_compute in sc_of 259 srH knH.
Definition srI0 : list expr := Eval vm_compute in sc_sr scOF.
Definition knI0 : list kentry := Eval vm_compute in sc_kn scOF.

Definition ssI0 : sym_state := SS 0x16cc04 srI0 [] knI0 291.
Definition rI := Eval vm_compute in runT (SCR [] [] []) ssI0.
Definition srI : list expr := Eval vm_compute in s_regs (fst (fst rI)).
Definition knI : list kentry := Eval vm_compute in kn_afterT rI knI0.

Definition knG30 : list kentry := Eval vm_compute in kn_readd (66 + 1) (66 + NSUF) (kn_cut 0 (BUF_LO + NPRE) BUF_HI IHI knF).
Definition ssG30 : sym_state := SS AMEMCPY_RET srG0 [] knG30 227.
Definition rG3 := Eval vm_compute in runT (SCR [] [] []) ssG30.
Definition srG3 : list expr := Eval vm_compute in s_regs (fst (fst rG3)).
Definition knG3 : list kentry := Eval vm_compute in kn_afterT rG3 knG30.
Definition scG3 : stdio_res := Eval vm_compute in sc_of 227 srG3 knG3.
Definition srH30 : list expr := Eval vm_compute in sc_sr scG3.
Definition knH30 : list kentry := Eval vm_compute in sc_kn scG3.

Definition ssH30 : sym_state := SS (sc_ret scG3) srH30 [] knH30 259.
Definition rH3 := Eval vm_compute in runT (SCR [] [] []) ssH30.
Definition srH3 : list expr := Eval vm_compute in s_regs (fst (fst rH3)).
Definition knH3 : list kentry := Eval vm_compute in kn_afterT rH3 knH30.
Definition scH3 : stdio_res := Eval vm_compute in sc_of 259 srH3 knH3.
Definition srI30 : list expr := Eval vm_compute in sc_sr scH3.
Definition knI30 : list kentry := Eval vm_compute in sc_kn scH3.

Definition ssI30 : sym_state := SS 0x16cc04 srI30 [] knI30 291.
Definition rI3 := Eval vm_compute in runT (SCR [] [] []) ssI30.
Definition srI3 : list expr := Eval vm_compute in s_regs (fst (fst rI3)).
Definition knI3 : list kentry := Eval vm_compute in kn_afterT rI3 knI30.

Definition knF40 : list kentry := Eval vm_compute in px_range (66 + NSUF + 1) 131071 knE.
Definition ssF40 : sym_state := SS AMEMCPY_RET srF0 [] knF40 195.
Definition rF4 := Eval vm_compute in runT (SCR [true] [] []) ssF40.
Definition srF4 : list expr := Eval vm_compute in s_regs (fst (fst rF4)).
Definition knF4 : list kentry := Eval vm_compute in kn_afterT rF4 knF40.
Definition scF4 : stdio_res := Eval vm_compute in sc_of 195 srF4 knF4.
Definition srG40 : list expr := Eval vm_compute in sc_sr scF4.
Definition knG40 : list kentry := Eval vm_compute in kn_readd (66 + NSUF + 1) 131071 (sc_kn scF4).

Definition ssG40 : sym_state := SS (sc_ret scF4) srG40 [] knG40 227.
Definition rG4 := Eval vm_compute in runT (SCR [false] [] []) ssG40.
Definition srG4 : list expr := Eval vm_compute in s_regs (fst (fst rG4)).
Definition knG4 : list kentry := Eval vm_compute in kn_afterT rG4 knG40.

Definition logNL : list sentry := [SE (SA (EVar 0) (-586)) 1 (ELit 10); SE (SA (EVar 0) (-588)) 2 (ELit 21589); SE (SA (EVar 0) (-592)) 4 (ELit 1347307808)].
Definition knH40 : list kentry := Eval vm_compute in fst (fst (carry logNL knG4 [])).
Definition srH40 : list expr := Eval vm_compute in sr_after_call_j srG4 KEPT_MC 227.

Definition ssH40 : sym_state := SS AMEMCPY_RET srH40 [] knH40 259.
Definition rH4 := Eval vm_compute in runT (SCR [] [] []) ssH40.
Definition srH4 : list expr := Eval vm_compute in s_regs (fst (fst rH4)).
Definition knH4 : list kentry := Eval vm_compute in kn_afterT rH4 knH40.
Definition scH4 : stdio_res := Eval vm_compute in sc_of 259 srH4 knH4.
Definition srI40 : list expr := Eval vm_compute in sc_sr scH4.
Definition knI40 : list kentry := Eval vm_compute in sc_kn scH4.

Definition ssI40 : sym_state := SS 0x16cc04 srI40 [] knI40 291.
Definition rI4 := Eval vm_compute in runT (SCR [] [] []) ssI40.
Definition srI4 : list expr := Eval vm_compute in s_regs (fst (fst rI4)).
Definition knI4 : list kentry := Eval vm_compute in kn_afterT rI4 knI40.

Definition knFs0 : list kentry := Eval vm_compute in px_range (FQMAX + 1) (66 + NSUF) knE.
Definition rFs1 := Eval vm_compute in runT (SCR [true; false; true; false] [] []) (SS AMEMCPY_RET srF0 [] knFs0 195).
Definition srFs1 : list expr := Eval vm_compute in s_regs (fst (fst rFs1)).
Definition knFs1 : list kentry := Eval vm_compute in kn_afterT rFs1 knFs0.

Definition RIPSP : Z := (-3376).
Definition srFs20 : list expr := Eval vm_compute in after_rip 195 srFs1.
Definition knFs20 : list kentry := Eval vm_compute in kn_readd (FQMAX + 1) (66 + NSUF) (kn_cut 0 (RIPSP - RIP_FR) RIPSP IHI knFs1).

Definition rFs2 := Eval vm_compute in runT (SCR [false] [] []) (SS 0xb9ee8 srFs20 [] knFs20 227).
Definition srFs2 : list expr := Eval vm_compute in s_regs (fst (fst rFs2)).
Definition knFs2 : list kentry := Eval vm_compute in kn_afterT rFs2 knFs20.
Definition srFs30 : list expr := Eval vm_compute in after_rip 227 srFs2.
Definition knFs30 : list kentry := Eval vm_compute in kn_readd (FQMAX + 1) (66 + NSUF) (kn_cut 0 (RIPSP - RIP_FR) RIPSP IHI knFs2).

Definition rFs3 := Eval vm_compute in runT (SCR [] [] []) (SS 0xb9fe4 srFs30 [] knFs30 259).
Definition srFs3 : list expr := Eval vm_compute in s_regs (fst (fst rFs3)).
Definition knFs3 : list kentry := Eval vm_compute in kn_afterT rFs3 knFs30.

Definition knGs0 : list kentry := Eval vm_compute in kn_readd (FQMAX + 1) 66 (kn_cut 0 (BUF_LO + NPRE) BUF_HI IHI knFs3).
Definition srGs0 : list expr := Eval vm_compute in sr_after_call_j srFs3 KEPT_MCI 259.
Definition rGs := Eval vm_compute in runT (SCR [false] [] []) (SS AMEMCPY_RET srGs0 [] knGs0 291).
Definition srGs : list expr := Eval vm_compute in s_regs (fst (fst rGs)).
Definition knGs : list kentry := Eval vm_compute in kn_afterT rGs knGs0.
Definition knHs0 : list kentry := Eval vm_compute in kn_readd (FQMAX + 1) 66 (kn_cut 0 (BUF_LO + NPRE) BUF_HI IHI knGs).
Definition srHs0 : list expr := Eval vm_compute in sr_after_call_j srGs KEPT_MC 291.
Definition rHs := Eval vm_compute in runT (SCR [] [] []) (SS AMEMCPY_RET srHs0 [] knHs0 323).
Definition srHs : list expr := Eval vm_compute in s_regs (fst (fst rHs)).
Definition knHs : list kentry := Eval vm_compute in kn_afterT rHs knHs0.
Definition scOFs : stdio_res := Eval vm_compute in sc_of 323 srHs knHs.
Definition srIs0 : list expr := Eval vm_compute in sc_sr scOFs.
Definition knIs0 : list kentry := Eval vm_compute in sc_kn scOFs.
Definition rIs := Eval vm_compute in runT (SCR [] [] []) (SS 0x16cc04 srIs0 [] knIs0 355).
Definition knG3s0 : list kentry := Eval vm_compute in kn_readd (66 + 1) (66 + NSUF) (kn_cut 0 (BUF_LO + NPRE) BUF_HI IHI knFs3).
Definition rG3s := Eval vm_compute in runT (SCR [] [] []) (SS AMEMCPY_RET srGs0 [] knG3s0 291).
Definition srG3s : list expr := Eval vm_compute in s_regs (fst (fst rG3s)).
Definition knG3s : list kentry := Eval vm_compute in kn_afterT rG3s knG3s0.
Definition scG3s : stdio_res := Eval vm_compute in sc_of 291 srG3s knG3s.
Definition srH3s0 : list expr := Eval vm_compute in sc_sr scG3s.
Definition knH3s0 : list kentry := Eval vm_compute in sc_kn scG3s.
Definition rH3s := Eval vm_compute in runT (SCR [] [] []) (SS (sc_ret scG3s) srH3s0 [] knH3s0 323).
Definition srH3s : list expr := Eval vm_compute in s_regs (fst (fst rH3s)).
Definition knH3s : list kentry := Eval vm_compute in kn_afterT rH3s knH3s0.
Definition scH3s : stdio_res := Eval vm_compute in sc_of 323 srH3s knH3s.
Definition srI3s0 : list expr := Eval vm_compute in sc_sr scH3s.
Definition knI3s0 : list kentry := Eval vm_compute in sc_kn scH3s.
Definition rI3s := Eval vm_compute in runT (SCR [] [] []) (SS 0x16cc04 srI3s0 [] knI3s0 355).

Definition ot_regions : list sregion := [(SA (EVar 0) (-128 - OT_FR), OT_FR); (SA (ELit 0) 0x187f60, 232)].
Definition scsB : list sidecond := Eval vm_compute in (snd (fst rB)).
Lemma factsB : snd (fst rB) = scsB /\ snd (fst (carry (s_log (fst (fst rB))) knV0 [])) = [] /\ log_covered ot_regions (s_log (fst (fst rB))) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_usage_defs ()) [] "p;1p;3p;4p;2g0000j14Tg000Pj1DTg001Pj10Tg0025j12Tg002Zj1=Tg0038j16Tg0048j3:Tg0058j1@Tg005Vj4?Tg006Zj19Tg007:j3>Tg007Zj31Tg0084j25Tg008Oj27Tg008ij4<Tg009Dj28Tg009dj33Tg00:Aj3;Tg00:^j1CTg00;]j3BTg00<\j2ATg00=[R0#4R1g00>_g00??g00@1g00@]g00AI#Dg00AhR2#0#0#2#0#2#0#0#0#0#=#63:%=2#63:%22#2#@#6C?%90R25>0R0;10A1122R3g00BMR4g00BmR5;15R6'51710P3P617121745C<C<g00CMR61861g00DRg00EU33R37;1g00FV511g00GY#4R01801%44A3613#CR3g00H[%943B337;1=112g00I^/A3=145'5'5do"). Qed.
Definition scsC : list sidecond := Eval vm_compute in (snd (fst rC)).
Lemma factsC : snd (fst rC) = scsC /\ snd (fst (carry (s_log (fst (fst rC))) knC0 [])) = [] /\ log_covered ot_regions (s_log (fst (fst rC))) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_usage_defs ()) [] "p;1p;3p;2p;4g0000j13Tg006Zj18Tg007Zj30Tg0084j21Tg008Oj27Tg008ij46Tg009Dj25Tg009dj32Tg00:Aj34Tg00:^j1;Tg00;]j3:Tg00<\j29Tg00=[R0#3R1%80R0;00R2g00BMR3g00BmR4;04R5,121710R6P2P5P61734C6C6g00CMR61561g00DRg00Jg32R5741g00Kh501g00GY#3R21521%33A2615#;R5g00Lk%833:32741=010g00I^/95=034'1'1do"). Qed.
Definition scsD : list sidecond := Eval vm_compute in (snd (fst rD)).
Lemma factsD : snd (fst rD) = scsD /\ snd (fst (carry (s_log (fst (fst rD))) knC [])) = [] /\ log_covered ot_regions (s_log (fst (fst rD))) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_usage_defs ()) [] "p;1p;3p;2p;4g0000j13Tg006Zj18Tg007Zj30Tg0084j21Tg008Oj27Tg008ij46Tg009Dj25Tg009dj32Tg00:Aj34Tg00:^j1;Tg00;]j3:Tg00<\j29Tg00=[R0#3R1%80R0;00R2g00BMR3g00BmR4;04R5,121710R6P2P5P61734C6C6g00CMR61561g00DRg00Mn32R5741g00No501g00GY#3R21521%33A2615#;R5g00P2%833:32741=010g00I^/95=034'1'1do"). Qed.
Definition scsE : list sidecond := Eval vm_compute in (snd (fst rE)).
Lemma factsE : snd (fst rE) = scsE /\ snd (fst (carry (s_log (fst (fst rE))) knE0 [])) = [] /\ log_covered ot_regions (s_log (fst (fst rE))) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_usage_defs ()) [] "p;1p;3p;4p;2g0000j14Tg00Q4j10Tg000Pj1;Tg0038j1GTg00QSj3BTg005Vj4ATg0048j3@Tg00RSj2>Tg00STj4=Tg006Zj17Tg007:j3<Tg007Zj32Tg0084j26Tg008Oj25Tg008ij48Tg009Dj29Tg009dj33Tg00:Aj3:Tg00:^j1FTg00;]j3DTg00<\j2ETf0R0#0#0p=C%00#0#0#0#0#0#0#0p=?%00#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=1g00=[R0#4R1g00>_R2g00TXg00@]R3g00AI#0R4#0R5#0#C#?#1#1#1#1#1#1#1#1#;R6g00UJR7#GR83BP6CA%;5=@36/>7P4P2P8C=%70R85<05<0R0;20A2188R2g00BMR4g00BmR7;27R6'61510P2P615181547C8C8g00CMR61961g00DRg00Uh33R27:1g00Vi521g00GY#4R01901%44A3612#FR2g00Wl%743D337:1=218g00I^/E2=247'6'6do"). Qed.
Definition scsF : list sidecond := Eval vm_compute in (snd (fst rF)).
Lemma factsF : snd (fst rF) = scsF /\ snd (fst (carry (s_log (fst (fst rF))) knF0_ [])) = [] /\ log_covered ot_regions (s_log (fst (fst rF))) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_usage_defs ()) [] "p;1p;3p;4p;2g0000j19Tg000Pj1=Tg001Pj13Tg0025j17Tg002Zj1DTg0038j1:Tg0048j36Tg00Q4j10Tg005Vj45Tg00Xoj4ETg00QSj3CTg006Zj1BTg007:j34Tg007Zj32Tg0084j2;Tg008Oj28Tg008ij4@Tg009Dj2ATg009dj3<Tg00:Aj3?Tg00:^j1ITg00;]j3HTg00<\j2GTf0R0#0#0p=>%00#0#0#0#0#0#0#0p=F%00#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=1g00=[R0#9R1g00>_R2g00??R3g00@1R4g00@]R5g00AIR6#=R7g00AhR8#3#3#7#3#3#7#3#3#7#D#:R936R:%D8#:R836%>6R;#>R<#0#F#1#1#1#1#1#1#1#1#=R=C5P2P3%=;R;=648P=C5g00BmR8g00YoP;A657==659C5P2g00ZaP:P;C5P8g00[SP8P6P<P=CEg00UJ#:R<9C5==C5<C5%B0R<540540540540540R0;20A21<<R5g00BMR=?288R6';1810P5P6181<18=8C@C@g00CMR61A61g00DRg00\E3<R57?1g00]F521g00GY#9R01A01%9=A<615#IR5g00^I%B=3H3<7?1=21<g00I^/G5=2=8';';do"). Qed.
Definition scsF0 : list sidecond := Eval vm_compute in (snd (fst rF0)).
Lemma factsF0 : snd (fst rF0) = scsF0 /\ snd (fst (carry (s_log (fst (fst rF0))) knF00 [])) = [] /\ log_covered ot_regions (s_log (fst (fst rF0))) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_usage_defs ()) [] "p;1p;3p;4p;2g0000j16Tg000Pj1:Tg00Q4j10Tg0048j37Tg001Pj12Tg0025j15Tg002Zj1CTg0038j1BTg005Vj4<Tg006Zj1;Tg007:j3@Tg007Zj33Tg0084j28Tg008Oj29Tg008ij4>Tg009Dj2?Tg009dj34Tg00:Aj3=Tg00:^j1FTg00;]j3ETg00<\j2DTf0R0#0#0p=A%00#0#0#0#0#0#0#0p=G%00#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=1g00=[R0#6R1g00BmR2g00Yog00AIR3#AR4#:R5g00@]R6%:3R3%04#A#G#1#1#1#1#1#1#1#1#:576g00Ah#2#2#5#2#2#5#2#2#5#C#BR437C<g00>_g00ZaA7634P5C<%;0R55@05@0R0;30A3155R4g00BMR3?322R6'81910P4P619151932C>C>g00CMR61?61g00DRg00_M34R47=1g00`O531g00GY#6R01?01%63A4614#FR4g00aS%;33E347=1=315g00I^/D4=332'8'8do"). Qed.
Definition scsG : list sidecond := Eval vm_compute in (snd (fst rG)).
Lemma factsG : snd (fst rG) = scsG /\ snd (fst (carry (s_log (fst (fst rG))) knG0 [])) = [] /\ log_covered ot_regions (s_log (fst (fst rG))) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_usage_defs ()) [] "p;1p;3p;4p;2g0000j1:Tg000Pj1?Tg00Q4j10Tg0048j36Tg001Pj13Tg0025j14Tg002Zj1<Tg0038j15Tg0058j1BTg005Vj4ATg006Zj1@Tg007:j3GTg007Zj32Tg0084j27Tg008Oj29Tg008ij4>Tg009Dj2=Tg009dj38Tg00:Aj3;Tg00:^j1ETg00;]j3DTg00<\j2FTf0R0#0#0#0#0p=C%00#0#0#0#0#0#0#0p=H%00#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=1g00=[R0#:R1g00>_g00??g00@1g00@]R2g00AIR3#?%03#C#H#1#1#1#1#1#1#1#1#?562g00AhR2#3#3#4#3#3#4#3#3#4#<#536%<2#536%42#4#B#5CA%@0R25G0R0;20A2122R3g00BMR4g00BmR5;25R6'71910P3P619121945C>C>g00CMR61=61g00DRg00bW38R37;1g00cX521g00GY#:R01=01%:4A8613#ER3g00d[%@43D387;1=212g00I^/F3=245'7'7do"). Qed.
Definition scsH : list sidecond := Eval vm_compute in (snd (fst rH)).
Lemma factsH : snd (fst rH) = scsH /\ snd (fst (carry (s_log (fst (fst rH))) knH0 [])) = [] /\ log_covered ot_regions (s_log (fst (fst rH))) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_usage_defs ()) [] "p;1p;3p;2p;4g0000j13Tg006Zj18Tg007Zj30Tg0084j21Tg008Oj27Tg008ij46Tg009Dj25Tg009dj32Tg00:Aj34Tg00:^j1;Tg00;]j3:Tg00<\j29Tg00=[R0#3R1%80R0;00R2g00BMR3g00BmR4;04R5,121710R6P2P5P61734C6C6g00CMR61561g00DRg00e^32R5741g00f_501g00GY#3R21521%33A2615#;R5g00gb%833:32741=010g00I^/95=034'1'1do"). Qed.
Definition scsI : list sidecond := Eval vm_compute in (snd (fst rI)).

Definition scsG3 : list sidecond := Eval vm_compute in (snd (fst rG3)).

Definition scsH3 : list sidecond := Eval vm_compute in (snd (fst rH3)).

Definition scsI3 : list sidecond := Eval vm_compute in (snd (fst rI3)).

Definition scsF4 : list sidecond := Eval vm_compute in (snd (fst rF4)).
Lemma factsF4 : snd (fst rF4) = scsF4 /\ snd (fst (carry (s_log (fst (fst rF4))) knF40 [])) = [] /\ log_covered ot_regions (s_log (fst (fst rF4))) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_usage_defs ()) [] "p;1p;4p;3p;2g0000j13Tg00Q4j10Tg000Pj1DTg00Xoj4CTg0038j1?Tg00QSj38Tg005Vj4>Tg006Zj17Tg007:j3<Tg007Zj32Tg0084j26Tg008Oj24Tg008ij4;Tg009Dj2:Tg009dj35Tg00:Aj39Tg00:^j1BTg00;]j3@Tg00<\j2ATf0R0#0#0#0#0p=E%00#0#0#0#0#0#0#0p==%00#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=1g00=[R0#3R1g00BmR2g00[SP2g00AIR3%E3R3%03#=#1#1#1#1#1#1#1#1#DR3CCg00@]R4g00UJ#?R59843;85C>%70R55<0R0;20A2155R4g00BMR3?222R6'61410P4P614151432C;C;g00CMR61:61g00DRg00he35R4791g00ig521g00GY#3R01:01%33A5614#BR4g00jk%733@35791=215g00I^/A4=232'6'6do"). Qed.
Definition scsG4 : list sidecond := Eval vm_compute in (snd (fst rG4)).
Lemma factsG4 : snd (fst rG4) = scsG4 /\ snd (fst (carry (s_log (fst (fst rG4))) knG40 [])) = [] /\ log_covered ot_regions (s_log (fst (fst rG4))) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_usage_defs ()) [] "p;1p;3p;4p;2g0000j14Tg000Pj1DTg001Pj10Tg0025j12Tg002Zj1=Tg0038j16Tg0048j3:Tg0058j1@Tg005Vj4?Tg006Zj19Tg007:j3>Tg007Zj31Tg0084j25Tg008Oj27Tg008ij4<Tg009Dj28Tg009dj33Tg00:Aj3;Tg00:^j1CTg00;]j3BTg00<\j2ATg00=[R0#4R1g00>_g00??g00@1g00@]g00AI#Dg00AhR2#0#0#2#0#2#0#0#0#0#=#63:%=2#63:%22#2#@#6C?%90R25>0R0;10A1122R3g00BMR4g00BmR5;15R6'51710P3P617121745C<C<g00CMR61861g00DRg00ko33R37;1g00m1511g00GY#4R01801%44A3613#CR3g00n5%943B337;1=112g00I^/A3=145'5'5do"). Qed.
Definition scsH4 : list sidecond := Eval vm_compute in (snd (fst rH4)).
Lemma factsH4 : snd (fst rH4) = scsH4 /\ snd (fst (carry (s_log (fst (fst rH4))) knH40 [])) = [] /\ log_covered ot_regions (s_log (fst (fst rH4))) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_usage_defs ()) [] "p;1p;3p;2p;4g0000j13Tg006Zj18Tg007Zj30Tg0084j21Tg008Oj27Tg008ij46Tg009Dj25Tg009dj32Tg00:Aj34Tg00:^j1;Tg00;]j3:Tg00<\j29Tg00=[R0#3R1%80R0;00R2g00BMR3g00BmR4;04R5,121710R6P2P5P61734C6C6g00CMR61561g00DRg00o932R5741g010;501g00GY#3R21521%33A2615#;R5g011?%833:32741=010g00I^/95=034'1'1do"). Qed.
Definition scsI4 : list sidecond := Eval vm_compute in (snd (fst rI4)).

Definition scsFs1 : list sidecond := Eval vm_compute in (snd (fst rFs1)).
Lemma factsFs1 : snd (fst rFs1) = scsFs1 /\ snd (fst (carry (s_log (fst (fst rFs1))) knFs0 [])) = [] /\ log_covered ot_regions (s_log (fst (fst rFs1))) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_usage_defs ()) [] "p;1p;3p;4p;2g0000j18Tg000Pj19Tg002Zj1>Tg0038j1=Tg0048j36Tg00Q4j10Tg005Vj44Tg001Pj12Tg0025j17Tg00Xoj4ETg00QSj3CTg006Zj1BTg007:j35Tg007Zj33Tg0084j2;Tg008Oj2:Tg008ij4@Tg009Dj2ATg009dj3<Tg00:Aj3?Tg00:^j1HTg00;]j3GTg00<\j2FTf0R0#0#0p=D%00#0#0#0#0#0#0#0p=I%00#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=1g00=[R0#8R1g00>_R2g00??g00@1g00AIR3#DR4#9R5g00AhR6#>#=36%D4R4#0#I#1#1#1#1#1#1#1#1#9R7C4g00BmR8g00YoP5g00@]R9%93R:=697%26#2#7#2#2#7#2#2#7#>#=R636C4P2g00ZaA69:6P5C4P8g00[SP8P3P4P7CEg00UJ#=R49C97=C94C4%B0R4550550550550R0;30A3144R9g00BMR7?388R3';1:10P9P31:141:78C@C@g00CMR31A31g00DRg012C3<R97?1g013F531g00GY#8R01A01%87A<319#HR9g014K%B73G3<7?1=314g00I^/F9=378';';do"). Qed.
Definition scsFs2 : list sidecond := Eval vm_compute in (snd (fst rFs2)).
Lemma factsFs2 : snd (fst rFs2) = scsFs2 /\ snd (fst (carry (s_log (fst (fst rFs2))) knFs20 [])) = [] /\ log_covered ot_regions (s_log (fst (fst rFs2))) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_usage_defs ()) [] "p;1p;3p;4p;2g0000j16Tg000Pj1@Tg001Pj13Tg0025j15Tg002Zj1?Tg0038j1=Tg0048j3;Tg00Q4j10Tg005Vj4ATg006Zj19Tg007:j3GTg007Zj32Tg0084j28Tg008Oj27Tg008ij4>Tg009Dj2:Tg009dj34Tg00:Aj3<Tg00:^j1FTg00;]j3ETg00<\j2DTf0R0#0#0#0#0p=C%00#0#0#0#0#0#0#0p=B%00#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=1g00=[R0#6R1g00>_g00??g00@1g00@]g00AIR2#@g00AhR3#3#3#5#3#3#5#3#3#5#?#=3;%?3#=3;%02#C#B#1#1#1#1#1#1#1#1#@CA%90R25G0R0;20A2122R3g00BMR4g00BmR5;25R6'81710P3P617121745C>C>g00CMR61:61g00DRg015O34R37<1g016R521g00GY#6R01:01%64A4613#FR3g017W%943E347<1=212g00I^/D3=245'8'8do"). Qed.
Definition scsFs3 : list sidecond := Eval vm_compute in (snd (fst rFs3)).
Lemma factsFs3 : snd (fst rFs3) = scsFs3 /\ snd (fst (carry (s_log (fst (fst rFs3))) knFs30 [])) = [] /\ log_covered ot_regions (s_log (fst (fst rFs3))) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_usage_defs ()) [] "p;1p;3p;2p;4g0000j13Tg006Zj18Tg007Zj30Tg0084j21Tg008Oj27Tg008ij46Tg009Dj25Tg009dj32Tg00:Aj34Tg00:^j1;Tg00;]j3:Tg00<\j29Tg00=[R0#3R1%80R0;00R2g00BMR3g00BmR4;04R5,121710R6P2P5P61734C6C6g00CMR61561g00DRg018\32R5741g019_501g00GY#3R21521%33A2615#;R5g01:d%833:32741=010g00I^/95=034'1'1do"). Qed.
Definition scsGs : list sidecond := Eval vm_compute in (snd (fst rGs)).
Lemma factsGs : snd (fst rGs) = scsGs /\ snd (fst (carry (s_log (fst (fst rGs))) knGs0 [])) = [] /\ log_covered ot_regions (s_log (fst (fst rGs))) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_usage_defs ()) [] "p;1p;3p;4p;2g0000j1:Tg000Pj1?Tg00Q4j10Tg0048j36Tg001Pj13Tg0025j14Tg002Zj1<Tg0038j15Tg0058j1BTg005Vj4ATg006Zj1@Tg007:j3GTg007Zj32Tg0084j27Tg008Oj29Tg008ij4>Tg009Dj2=Tg009dj38Tg00:Aj3;Tg00:^j1ETg00;]j3DTg00<\j2FTf0R0#0#0#0#0p=C%00#0#0#0#0#0#0#0p=H%00#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=1g00=[R0#:R1g00>_g00??g00@1g00@]R2g00AIR3#?%03#C#H#1#1#1#1#1#1#1#1#?562g00AhR2#3#3#4#3#3#4#3#3#4#<#536%<2#536%42#4#B#5CA%@0R25G0R0;20A2122R3g00BMR4g00BmR5;25R6'71910P3P619121945C>C>g00CMR61=61g00DRg01;i38R37;1g01<k521g00GY#:R01=01%:4A8613#ER3g01=o%@43D387;1=212g00I^/F3=245'7'7do"). Qed.
Definition scsHs : list sidecond := Eval vm_compute in (snd (fst rHs)).
Lemma factsHs : snd (fst rHs) = scsHs /\ snd (fst (carry (s_log (fst (fst rHs))) knHs0 [])) = [] /\ log_covered ot_regions (s_log (fst (fst rHs))) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_usage_defs ()) [] "p;1p;3p;2p;4g0000j13Tg006Zj18Tg007Zj30Tg0084j21Tg008Oj27Tg008ij46Tg009Dj25Tg009dj32Tg00:Aj34Tg00:^j1;Tg00;]j3:Tg00<\j29Tg00=[R0#3R1%80R0;00R2g00BMR3g00BmR4;04R5,121710R6P2P5P61734C6C6g00CMR61561g00DRg01?332R5741g01@5501g00GY#3R21521%33A2615#;R5g01A9%833:32741=010g00I^/95=034'1'1do"). Qed.
Definition scsIs : list sidecond := Eval vm_compute in (snd (fst rIs)).

Definition scsG3s : list sidecond := Eval vm_compute in (snd (fst rG3s)).
Lemma factsG3s : snd (fst rG3s) = scsG3s /\ snd (fst (carry (s_log (fst (fst rG3s))) knG3s0 [])) = [] /\ log_covered ot_regions (s_log (fst (fst rG3s))) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_usage_defs ()) [] "p;1p;3p;2p;4g0000j13Tg006Zj18Tg007Zj30Tg0084j21Tg008Oj27Tg008ij46Tg009Dj25Tg009dj32Tg00:Aj34Tg00:^j1;Tg00;]j3:Tg00<\j29Tg00=[R0#3R1%80R0;00R2g00BMR3g00BmR4;04R5,121710R6P2P5P61734C6C6g00CMR61561g00DRg01B=32R5741g01C@501g00GY#3R21521%33A2615#;R5g01DE%833:32741=010g00I^/95=034'1'1do"). Qed.
Definition scsH3s : list sidecond := Eval vm_compute in (snd (fst rH3s)).
Lemma factsH3s : snd (fst rH3s) = scsH3s /\ snd (fst (carry (s_log (fst (fst rH3s))) knH3s0 [])) = [] /\ log_covered ot_regions (s_log (fst (fst rH3s))) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_usage_defs ()) [] "p;1p;3p;2p;4g0000j13Tg006Zj18Tg007Zj30Tg0084j21Tg008Oj27Tg008ij46Tg009Dj25Tg009dj32Tg00:Aj34Tg00:^j1;Tg00;]j3:Tg00<\j29Tg00=[R0#3R1%80R0;00R2g00BMR3g00BmR4;04R5,121710R6P2P5P61734C6C6g00CMR61561g00DRg01EJ32R5741g01FM501g00GY#3R21521%33A2615#;R5g01GR%833:32741=010g00I^/95=034'1'1do"). Qed.
Definition scsI3s : list sidecond := Eval vm_compute in (snd (fst rI3s)).

Lemma ot_itinerary_s :
  (s_pc (fst (fst rFs1)), s_pc (fst (fst rFs2)), s_pc (fst (fst rFs3))) = (ARIP, ARIP, AMEMCPY)
  /\ (s_pc (fst (fst rGs)), s_pc (fst (fst rHs)), s_pc (fst (fst rIs))) = (AMEMCPY, ASTDIO_WRITE, AMAINEPI)
  /\ (s_pc (fst (fst rG3s)), s_pc (fst (fst rH3s)), s_pc (fst (fst rI3s))) = (ASTDIO_WRITE, ASTDIO_WRITE, AMAINEPI)
  /\ stdio_call 323 srHs knHs = Some scOFs /\ stdio_call 291 srG3s knG3s = Some scG3s /\ stdio_call 323 srH3s knH3s = Some scH3s.
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_usage_defs ()) [] "p%0p%1p&0p;2p;1p;3p;<p;4g009Dj2|Tg001Pj10Tg007Zj3ITg01HWk10<Tg0025j11Tg0058j1DTg000Pj16Tg002Zj19Tg00Q4j12Tg0038j1ATg00QSj3iTg006Zk104Tg01I9j3GTg01J;j3CTg00RSj2BTg01K=k20:Tg01L?k201Tg01MAk200Tg01NCl<{Tg01OGj2dTg0084j2OTg008Oj2eTg008ij4lTg0000k107Tg01Oij4YTg01PIj3zTg0048j3kTg007:j35Tg01QLk206Tg009dj3}Tg01RNk105Tf0R0#0#1#1#1p=Z%10#0#0#0p=@%00#0#1#0p=c%10#1#0#1p=U%00#0#0#Dp=;g01SLR1P1f1R2P0CYp=f%10#1p=F%10#0#1#0p=g%10#1#1#0p=\%00#Dp=jf2R3P1P2P0CYp=`%00#1#0#1p=h%00#0#0#1p=^%00#1#1#0p=E%00#0#1#1p=P%10#1#1#1p=T%00#0#0#0p=8%00#0p==g00@]R4%A07k2p=M%20#2p=~%20#2#2#2p=]%20#2#2p=s%20#2#2#2#2#2#2#2p=q%20#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2p=y%20#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2p=bAk420p=a%00#9p=p%D0#Ap=?%10#0#1#1p=_%10#1#0#0p=:%00#0#D#Ap=J%00#1p=K%10#0#0#1p=xg01SjR5%63%62=55035p=HA55209553p>03f4R6f3R7A55209553555555p=[%62=550p=w%00#0#0p=>1B73?C20p=v%10#1#1#1#1#1#1#1p=L%00#0#0#0#0#0#0#0p=Qg01Tjg01UV?k73=k42;k0p=Xg00UJR8,B20060p=W%03#9,B7?C20p=<%10#0p=o%00#0#9,B2p=u%00#9,B2p>0;%10#0#0p=R1B73%D0#A7C2p=n%00#1#0#0p=t%90,B2p>02g00GYR9%D7,B6?C32;50p=7A5920959395979596p=3AC732=590p>09%97,B6?C32=590p=4f6f5;C6AC732=590559p=rA59209593p=mA5920p>08%07#9,B6?C32=590p=N%17#0#0#0#9,B6?C32=590p=Vg00CMS00A}3207}7$05p=S1|11R7/|1R3g00AhR2#Z#@#c#U#;R0/f0%02#F#g#@#Z#\#jR05`7R6;I6%02#F#h#g#^#E#jR:,f0%U2#^#P#h#;R;5`7R<=I3<S011f::=`7;R;=I3;S02g01VBR=$0<R>%12R?#0S03#0R@#0S04#0S05#1S06#F#TRA#0#FS07#0S08#0#;RB%02RC#DRD%02#F#E#E#8#c#jREg00AIRF#6RG%0CRH#1RI#0RJ#1RK#0S09#=RL#0S0:#9S0;'MRM%2FRF#2RN#~RO#]RP#sS0<#2S0=#2#qS0>#2#yRQ#yS0?#2S0@#2S0A#2RR#2RS#2RT#2RU#2RV#2RW#s#]#q#b#bRX#6RY,aGRZ%0JRJ#0R[#0R\#1R]#p'MPM%1CRC#0R^#0R_#0R`#0Ra#?Rb%A8R8P8%1IRI#0Rc#0S0B#=S0C#pS0D,MGRd%~X#]#y#b#b#b#bRX#2#]S0E#2S0F#2S0G#]S0H#2S0I#2S0J#2S0K#2S0L#2S0M#2S0N#s#qS0O#2S0P#2S0Q#2S0R#2Re%AEPd%6QS0S%_2#8#T#:#E#JS0T%2e#]RQ%2QRQ%2QRQ%ABRf%1?Rg#?RhAi4Y8Ri9i48S0U=i4hRj5i4P8%]QRQ#6%2QRQ%2QRQ%2QRQ%2QRQ%2QRQ%2QRQ%12#K#:#Z#\#_#;S0V#AS0W%?2Rk%_2#x#^#:#:#JS0XP8%6RS0Y%6SS0Z%6TS0[%6US0\%6VS0]%6WS0^%sQ#qRQ%2QRQ%2QRQ%2Q&045S0_3H3H403D[D[3H3H3HD['w3HD['wS0`P8%1ARA#0R5#0RQ#0RW#0#;PP%0HRH#0RV#0RU#>S0a#0RT#9,MGS0bCvS0cP8%1W#;PPPMCvS0dP8%FQ#;PPPMCvS0e%1URQ#D%1VRW#0RS#D5GY%6NRR/aY%92'M%??R?%FgRl#1#F#LRm#0S0f#=#8#QRn#?Ro%9H#ARpCXRq%8TRT#>Rr#0#Q#Q#QRs#DRt%FTRT#1#T#LRu#1#8#Q#;Rv3GRw%?HRx,WqS0gPRP?PoPpCXRq?GtvRy1WqxS0h%1JRJ#0Rq#1#pS0i#ARz,aZP?PoPpCXR{?GtvR|1W{xS0j%0qRq#1#9#AR{,aZS0kP?PoPpCXR}?GtvR~1W}xS0l%1]#9,MZP?PoPpCXRZ?GtvRt1WZxS0mPMP?PoPpCXRZ%KT#T#_#\#L#E#;RT%0u#L#E#;Ru3GR]1WZxS0n1aGzP?PoPpCXRz?GTuRZ1WzxS0o1aG{P?PoPpCXRp?GTuRu1WpxS0pPG%@`S0qPPP8C<S0r%oa,uGS0s%1CR`#0S0t#0S0u#0Rp#1#URx#0RT#U#?R?7CP%=aRa#0S0v-0;GR{PPPh%1IRI#1Rz#o,uGR}PP%1x#K#JRxPG%>zS0wPPPfPG%0IRIPPP8PG%=IRI#0S0xPPP?PG%1cRcPPPhPG%>cS0yPPPfPGQ0BPP%K2#_#8#E#\#JPG%1KRcPPPxPG%>cS0BPPPfPGQ09PPPjPGQ0:PPg01WF%1m#F#T#LRm#?Rc;ijS0:PG%RJRzPPPcPG%=qPP%?KS09PG%@[R[PP%02#F#E#E#\#g#jS0z#AS0{PwPyP|P~PtP]PZPuPwPyP|P~PtP]PZPuPwPyP|P~PtP]PZPuPG%1HRH#1RK#1Rq#RPPP8C<S0|PG%0KRK#=S0}#0PPQ0UC<S0UPG%>qPPPYC<S0~PG%0\S10#0#pR\PP%1WRW#1Rq#1#^#@CnS11PG%RKPPP8C<S12PwPyP|P~PtP]PZPuPG%>QPPPRC<S13PGQ0DPP%1^R^#0S0D#=RK#9,MGCvS14PGQ0iPFPUCnS0iPG%9zPN%tgRg#1#o#hCnS15PGQ0;PO%1@R@#1RN#1#E#^#Z#P#Z#hCnS0;PG%0HRH#1Rz#RPP%1mRm#FRU#=#:#:#:#:#:#:#U#?C<S16PG%>zPP%1U#T#LRU#0#L#L#?C<S17PG%RQPP%PN#P#P#P#P#JC<RNPG%>WPP%@L#x#?C<RQPG%=SS18#0PPQ0WC<S19PG%RSPPP8C<S1:PG%=qPPPdC<S1;PG%0HRH#RPPQ0bC<S0bPG%=HRH#0PP%1^S1<#>S1=#9R^,MGC<RqP8Q07#1#8PPP8P8Q08#@PPP8P8%1ARA#1RS#KRz#>PO%1U#L#L#?P8%0ARA#0#8PPPbP8%15R5#1#@PPPM1B8BRUPO%?CS08202GaPPP8PG%1_R_#>RaPPP8PG%0KRKPPP81BG^PPP8202GIPPP8PGQ0BPP%0pRp#9RI,MGR^PGQ0CPP%6FRCPGPLPPQ0A#6PGQ10PPQ0@#6PGQ0}PPQ0?#6PGPHPPP^PGQ18PPPfPGQ0aPP%KT#JRTPG%>lPP%02#g#t#8#E#J%DV-0:G%0n#8#Q#;%>s#;Rs5GG%1`R`#FRn#:,uG%0`R`#\#;+01AGRvs%Dr%=[#8#;+00%>n#Q#;Q06#0#oRn#Q#;+001BGIPPPR1uG`PP%12#g#c#h#@#JPGQ05#=PPQ0<#6PG%>@R@PPQ0=#6PGQ03#1#8PPQ0>#6Q0V,B8PPPC%jg-01UP]PZP8%1nRn#1RU#=#^#;PP%E2#:#g#U#:CnP8%1URU#@Rg#8PP%A0P8%@gPP%K2#U#h#t#8#JP8%PU#8PP%K2#U#Z#c#8#JP8%Kn#:#8PP%K2#U#t#Q#JP8Q04#T#E#T#@PPPoP8%^@#\#:R@#0PFPkP8%1@PFPkP8%xHRH#0#Z#:PFPkP8%1H#c#PPFPkP8%05#@PP%A:P8%1A#@PO%ADP8%RzPO%?mRmP8%1S#8POPmP8Q0f#o#:#ZRm#8PPP8P8%@mPPP8&049D7D7D7D7D7D7D7D7D7D7D7D7D7D7D7D3H09D4D4D4Fr3mD3D4D4D4D4D4D4D4D4D4FrD4D4FrD7D7D7D7D7R9+083mD3D3D3D3D3D3RmD3D3D3D3D3D3D4D4DNDNDVDNDVDVDNDVDNDVDNFr3mD3D3D3D3D3M<{,d=RO;IORSPBPDQ0zPMQ0kPMPbP?Ph1MG\R\Q0{P\Q0SQ0TQ0EQ0FQ0GQ09PcPhQ0H#6Q0IQ0JQ0KQ0LQ0MQ0NQ0:PjPfPxPhP?P8Ai4i8Q0OQ0PQ0QQ0RQ0_3H3H:03hiD[D[3H3H3HD['w3HD[,wXQ0cQ0dQ0e%DW%DJ5GYRYPwQ0gPyQ0hP|Q0jP~Q0lPtQ0mP]Q0nPZQ0oPuQ0pPwPyP|P~PtP]PZPuPwPyP|P~PtP]PZPuQ0rQ0s?CPRRRAC{P8R{AC}P?R}Q0|Q0UQ0~Q11Q12PwPyP|P~PtP]PZPuQ13Q14Q0iQ15Q0;Q16Q17PGQ0t#1#8PPPCQ19Q1:Q1;Q0bPGQ0u#RPPQ0^C<PG%=pPPQ0]PGQ1<PPQ0\PGQ1=PPQ0[PGQ0DPPQ0ZPGPKPPQ0YPGP_PPQ08PGPaPPQ0XPGQ0qPPPkPGQ0vPPQ0WPGQ0wPPPTPGQ0xPPPfPGQ0yPP%K2#_#c#T#x#JP9D4D4D4D4D4DNDVDNDVDNDVD45mqD3D49mNQD3D3D3D3D3D3D3D3D3D3D3D3D3D3D3M<{,d=RQ=I>QRNPBPDPEPMPMPMPbP8P8PdQ0`Q0cQ0dQ0ePYPwQ0gPyQ0hP|Q0jP~Q0lPtQ0mP]Q0nPZQ0oPuQ0pPwPyP|P~PtP]PZPuPwPyP|P~PtP]PZPuQ0rPRP{P}PmD3D3D3D3D3D3D3D3D3D3M<{,d=Rm=I>mR}'OR{'ORR'ORu'O1e36Q01Pu1e3<Q02PR1e3;PSP{1e>OPNP}1e>Q1e>mClClClClClg00=[$07RmQ00/|mRQg00DRR}g012CCSPmPQP}g015OCS'fPmPQP}g018\CS5`7P7P1P1P1g01X2RNPNCYg01Y5RNCY5I3PmPQP}g01;iCSPmPQP}g01?3CS'fPmPQP}g01Z;CS5`7P7P1P1P1PNg01[=RNCYg01\HROCY5I3PmPQP}g01B=CSPmPQP}g01EJCS'fPmPQP}g01]OCS5`7P7P1P1P1PNPNCYPOCY5I3g01^Rg01_U5zeg01`X,d=5I>g01a\g01b`5zXg01cd,d=5I>g01dhg01el5zeg01g0,d=5I>'O'O'O'O'Odo"). Qed.

Lemma ot_itinerary :
  (s_pc (fst (fst rB)), s_pc (fst (fst rC)), s_pc (fst (fst rD)), s_pc (fst (fst rE))) = (AMEMCPY, AMEMCPY, ASTRNLEN_TR, AMEMCPY)
  /\ (s_pc (fst (fst rF)), s_pc (fst (fst rF0)), s_pc (fst (fst rG)), s_pc (fst (fst rH)), s_pc (fst (fst rI))) = (AMEMCPY, AMEMCPY, AMEMCPY, ASTDIO_WRITE, AMAINEPI)
  /\ (s_pc (fst (fst rG3)), s_pc (fst (fst rH3)), s_pc (fst (fst rI3))) = (ASTDIO_WRITE, ASTDIO_WRITE, AMAINEPI)
  /\ (s_pc (fst (fst rF4)), s_pc (fst (fst rG4)), s_pc (fst (fst rH4)), s_pc (fst (fst rI4))) = (ASTDIO_WRITE, AMEMCPY, ASTDIO_WRITE, AMAINEPI)
  /\ stdio_call 259 srH knH = Some scOF /\ stdio_call 227 srG3 knG3 = Some scG3 /\ stdio_call 259 srH3 knH3 = Some scH3
  /\ stdio_call 195 srF4 knF4 = Some scF4 /\ stdio_call 259 srH4 knH4 = Some scH4.
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_usage_defs ()) [] "p%0p%1p&0p;2p;3p;1p;<p;4g009Dj2rTg007Zj3NTg01HWk10CTg0025j11Tg001Pj10Tg0058j19Tg000Pj16Tg002Zj1>Tg00Q4j12Tg0038j1=Tg00QSj3lTg006Zk10=Tg01I9j3JTg01J;j3@Tg00RSj2FTg01K=k20BTg01L?k20;Tg01MAk20:Tg01NCl<pTg01OGj2OTg0084j2XTg008Ok207Tg0000k10@Tg01Oij4GTg01PIj3oTg0048j3tTg007:j34Tg01QLk20?Tg008ik40>Tg009dj3wTg01RNk103Tf0R0#0#1#1p=j%10#0#1#0p=a%10#0#0#0p=:%00#1#1#1p=`%10#1#1#0p=]%00#9p=hg01SLR1P1f1R2P0CGp=b%00#1#0#0p=c%00#0#0#9p=<f4R3P1f3R4P1f2R5P2CGP0CGp=gP5P1P2P0CGp>02%00#1#0#1p=u%00#0#0#1p=s%00#1#1#0p=I%10#1#0#1p=e%00#0#1#1p=_%10#1p=T%10#1#1#1p=R%00#0#0#0p=7%00#0#1#0p=[%00#0p=Dg00@]R6%=07t2p=Q%20#2p>04%20#2#2#2p=W%20#2#2p=n%20#2#2#2#2#2#2#2p=m%20#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2p=SAt620p=f%00#>p=v%90#=p=B%10#0#1#1p=M%10#1#0#0p=A%00#0#9#=p=H%00#1p=K%10#0#0#1p=kg01SjR7%62;40p>01%65%62=470547p=C%62=47094759474p=iA4720947594749473p=V%64A47209475547p>00%00#0#0p=?1F45?@20p=d%10#1#1#1#1#1#1#1p=P%00#0#0#0#0#0#0#0p=Ug01Tjg01UV?t45=t62;t0p=^g00UJR8,F200?0p=\%05#>,F4?@20p=;%10#0p=|%00#0#>,F2p={%>0,F2p=z%15#0#0#0#>,F4?@20p=L%10#0#0p=y%=09@52p=x%10#9p>0<g00GYR9%94,F3?@52;40p=8A4920949594949493p=3A@452=490p>0A%>4,F3?@52=490p=5f6f5;@3A@452=490549p=~A49209495p>09A4920p=q%92#=9@45=490p>08P3P420752P0H0>p=Yg00CMR3Aw5207w4$03p=EAw5209w34p>06P5P1P2&030CGp>05P2P1P0g01\HCGp=}AN452/X0p=Z1r11R0/r1R5/r1R4P5P0g00AhR2#j#a#:#`#]#hR:/b:R;%c2#`#c#`#<P:DgS00Q003N1r41S01P4P5B020;:%j2#u#a#s#I#hR;%e2#s#_#u#<R<DgR=;N=S021b;;>020<R>=N5>S03P5P01b;:P;P<DgR<=N4<S04g01VBR?$0CR@%12RA#0S05#0S06#0S07#0S08#1S09#T#RRB#jS0:#0S0;#0#<RC%02RD#9RE%j2#I#I#7#[#hRFg00AIRG#6RH%0DRI#1RJ#0RK#1RL#0RM#DRN#0S0<#>S0='QRO%2GRG#2RP$04RQ#WRR#nS0>#2S0?#2#mS0@#2#SRS#SS0A#2S0B#2S0C#2RT#2RU#2RV#2RW#2RX#2RY#n#W#m#S#S#S#SRZ#6R[,fHR\%0KRK#0S0D#0S0E#1R]#v'QPO%1DRD#0R^#0S0F#0R_#0R`#BRa%=8RbPb%1JS0G#0S0H#0S0I#DS0J#vS0K,QHRJ&04Z#W#S#S#SRZ#2#WS0L#2S0M#2S0N#WS0O#2S0P#2S0Q#2S0R#2S0S#2S0T#2S0U#n#mS0V#2S0W#2S0X#2S0Y#2Rc#2#WS0Z#2S0[#2S0\#WS0]#2S0^#2S0_#2S0`#2S0a#2S0b#2S0c#n#mS0d#2S0e#2S0f#2S0g#2Rd%=FPJ%6SS0h%M2#7#R#A#I#HS0i%2d#WRS%2SRS%2SRS%=CRe%1ARf#BRgAl6[bRh9l6bS0j=l6gRi5l6Pb%WSRS#6%2SRS%2SRS%2SRS%2SRS%2SRS%2SRS%12#K#A#`#]#M#<S0k#=S0l%B2Rj%M2#k#s#A#A#HS0mPb%6TS0n%6US0o%6VS0p%6WS0q%6XS0r%6YS0s%nS#mRS%2SRS%2SRS%2S&0=7R7+013CCiDVDV3C3C3CDV3CCiH00S0tPb%1BS0u#0S0v#0RB#0RS#0#<PR%0IRI#0RY#0RX#?S0w#0RW#>,QHS0xCdRVPb%1S#<PRPOCdRSPb%TB#<PRPOCdRB%1YRU#0RT#99J[8%6PR8/f[%>2'Q%BARA%TfS0y#1#T#PRk#0S0z#D#7#US0{#BRl%>I#=RmC^Rn%7WRW#?S0|#0#U#U#US0}#9Ro%TWRW#1#R#PRp#1#7#U#<Rq3JRr%BIRs,\nRnP8PAPlPmC^Rt?JoqRu1\tsRt%1KRK#0Rv#1#vS0~#=Rw,f\PAPlPmC^Rx?JoqRy1\xsRx%0vRv#1#>#=Rz,f\S10PAPlPmC^R{?JoqR|1\{sR{%1]#>,Q\PAPlPmC^R\?JoqRo1\\sR\POPAPlPmC^R]%KW#R#M#]#P#I#<RW%0p#P#I#<Rp3JR}1\]sR]1fHwPAPlPmC^Rw?JWpR~1\wsRw1fHzS11PAPlPmC^Rm?JWpRp1\msRmPH%:_S12PRPbC;R_%|`,{HS13%1DS14#0S15#0S16#0S17#1#eRs#0S18#e#BRW7@RS19%0`S1:#0S1;#0S1<#0,zHS1=?@RgS1>Q0G#1R`#1RA#|,{HS0G%1s#K#HS1?7@RS1@PH%?AS1APRPeC;S1BPH%0`R`PRPbCLS1CPH%D`S1D#0S1EPRPWC;S1FPHQ0H#1R`PRPgCLS0HPH%?`S1GPRPeC;S1HPHQ0IPR%K2#M#7#I#]#HCLS0IPH%1LR`PRQ1?CLS1IPH%?`S1JPRPeC;S1KPHPMPRPiCLS1LPHQ0<PRg01WF%1kS0<#T#R#PS1M#BRk;liS1NC;S1OPH%yKS1PPRPkC;S1QPH%0vPR%BLS1RC;S1SPHQ0D#:S0D#>PR%j2#I#I#]#a#hS1T#=S1UCdS1VPrPuPyP|PoP}P~PH%1IS1W#1RI#1RLPRPbCLRvPH%0IRI#DS1X#0PRQ0jC;R`PH%?LPRP[C;RLPHQ0E#0S0E#0#vS1YPR%1URU#1S1Z#y#I#HCdRAPHPIPRPbCLRIPrPuPyP|PoP}P~PpPH%1XS1[#?PRP8C;S1\PHQ0KPR%1^S0K#0S1]#DRs#>,QHCdRzQ0~,FHS0~%9X7xGS1^Q1P,zHS1P%cfS1_#T#[$0<7xPS1`Q0=,FHS0=Q06#1S06#1S1a#M#7#M#k#M#a$0<7xQS1bPHQ1W#0S1W#1RfPRQ1M#1S1M#TRX#D#A#A#A#A#A#A#e#BCLS1cPH%?fPR%1X#R#PS1d#0#P#P#BC;S1ePHQ1[PRQ1a#_#_#_#_#_#HCLS1aPH%?UPR%:N#k#BC;S1[PH%DTS1f#0PRQ0lC;S1gPHPTPRPbCLS1hPHQ1Z#DPRPJC;S1ZPHQ1W#0RTPRQ0xCLS0xPH%DTRT#0PRQ0K#1S0K#?S1W#>RX,QHC;S1iPbQ0:#1#7PRPbPbQ0;#:PRPbPbQ0u#1Rf#1S0u#KS0;#?PQQ1d#1#P#P#BPb%0fS1d#0#7PRPaPbQ0v#1S0v#1#:PRPO1FbCRfPQ%BDS0:Q1;,zHPRPbPHQ0F#1S0F#?S1;PRPbPH%0sS1jPRPb1FHXPRPbQ1D,zHPRPbPHQ1JPRQ17#0S17#>RX,QHRDPHQ0JPR%6GS0JPHPNPRQ0C#6PHQ0EPRQ0B#6PHQ1XPRQ0A#6PHPTPRPDPHQ1fPRPePHQ0wPRQ18#K#HS18PHQ0y#?PR%02#a#c#7#I#H%9Y-0BHQ0{#0#7#U#<Q0}#?#<RY5JHQ14#1RD#TRN#A,{H%0DRD#]#<+0;AJ8qYQ0|#9Q0D#D#7#<+0:%?N#U#<Q09#0#|RN#U#<+0:1FHXPRP81{HDPR%12#a#[#u#:#HPHQ08#DPRQ0>#6PHQ06#?RDPRQ0?#6PHQ05#1#7PRQ0@#6Q0k,FbPRQ0JQ1_#h-0;fP}P~Pb%1NRN#1Rf#D#s#<PR%K2#M#[#M#`#HCdPb%1fRf#:RX#7PR%=:Pb%:XPR%K2#e#u#c#7#HPb%_f#7PR%K2#e#`#[#7#HPb%KN#A#7PR%K2#e#c#U#HPbQ07#R#I#R#:PRPlPb%sD#]#ARD#0PGPjPb%1DPGPjPb%kTRT#0#`#APGPjPb%1T#[#_PGPjPbQ0v#0#:PR%=;PbQ1d#1#:PQ%=EPbQ0;#yPQQ1M#BR;PbQ0u#1#7PQP;PbQ0z#|#A#`R;#7PRPbPb%:;PRPb&0=9D8D8D8D8D8D8D8D8D8D8D8D8D8D8D8D3H0AD5D5D5F~409D3D5D5D5D5D5D5D5D5D5F~D5D5F~D8D8D8D8D8R9'qD3D3R;409D3D3D3D3RT,qpD3D3D3D3D3D3D3D3D3D3D3M<p,O?RD;NDRlPCPEQ1TPOQ10POPaPWPgQ1Y,QHRNPcQ1UPNQ0hQ0iQ0ZQ0[Q0\Q1RPkPgQ0]#6Q0^Q0_Q0`Q0aQ0bQ0cQ1NPiPeQ1?PgPWPbAl6hbR6PgPhQ0dQ0eQ0fQ0g00173CCiDVDV3C3C3CDV3CCiH00PVPSPB%9U%9K5J[RKPrPnPuPtPyPxP|P{PoP\P}P]P~PwPpPmP_Q13?@R8RUQ1=?@RbRiQ0G?@RWRfPvP`PLPAPIPrPuPyP|PoP}P~Q1\PzQ1^Q1`Q1bQ1cQ1eQ1aQ1[PHQ15#:PRQ0JC;Q1gQ1hQ1ZQ0xQ1iPHQ16PRQ0sCLPHQ17#DPRQ0rPHQ0K#:PRQ0qPHQ1W#0PRQ0pPHQ1]#:PRQ0oPHQ1j#0PRQ0nPHQ0F#:PRQ0:PHQ1;#0PRQ0mPHQ12PRPjPHQ1<PRQ0lPHQ1APRQ18PHQ1EPRPePHQ1GPR%K2#M#[#R#k#HP9D5D5D5D5D5D5D5D5D5D5D5D5D3D3D3D3R9,qpD3D3D3D3D3D3D3D3D3M<p,O?RR=N@RRHPCPEPFPOPOPOPaPbPbPJQ0tPVPSPBPKPrPnPuPtPyPxP|P{PoP\P}P]P~PwPpPmP_PUPiPfPTD3D3D3D3D3D3M<p,O?RT=N@TRKPCPE%j2#I#M#R#a#hR2POQ11POPaP8P[PNPZ%=2PNQ0hQ0iQ0LQ0MQ0NQ1RPkP[Q0O#6Q0PQ0QQ0RQ0SQ0TQ0UPbPgPePWPbP8PbP6Q0jPhQ0VQ0WQ0XQ0Y00173CCiDVDV3C3C3CDV3CCiH00PVPSPB%9MQ0<#95J[R[P_PUPiPfPvP`PLPAPIPrPnPuPtPyPxP|P{PoP\P}P]P~PwPp1qm9D3D3D3D3D3D3D3M<p,O?R9=N@9RfPCPEPFPOQ11POPaPbPbPJQ0tPVPSPBQ0~%9^7xGQ1PPP%1s#K#uQ0=PQQ1:#y#]#c#k#[#7P_Q19Q1>Q1@Q1BQ1CQ1FQ0HQ1HQ0IQ1IQ1KQ1LQ1OQ1QQ1SQ1VP[PrPnPuPtPyPxP|P{PoP\P}P]P~PwPpPmPvP`PLPAPIPrPnPuPtPyPxP|P{PoP\P}P]P~PwPpPmQ1\1qz;D3D3D3D3D3D3D3D3D3D3D3D3D3D3H08H08D3M<p,O?R;=N@;Rz'XRm'XRp'XRw'XR~'XR]'XR}'XP4Q00Q02P}Q01P=Q03P]P5P>Q04P~P4P<PlPwP@PDPHPpP@PRPKPmP@PTPfPzP@P9207@;DYDYDYDYDYDYDYDYP4P5P0g00=[$0@R;1r3;R3g00DRR9g00EUCEP;P3P9g00JgCE'bP;P3P9g00MnCEP;P3P9g00UhCEDgP5P1P0P1P1P1g01Y5RzPzCGRfg01h4CGPzCGQ01P4P5P;P3P9g00\ECEP;P3P9g00_MCE'bP;P3P9g00bWH066050P;P3P9g00e^CEP;P3P9g01i>CEDgP5P1P0P1PfPzCGg01[=RfCG,}4P5P;P3P9g01j?CEP;P3P9g01kACE'bP;P3P9g01lCH066050P1P1PfPfCG,}0P4P5P0P;P3P9g00heCEP;P3P9g00koCE'bP;P3P9g00o9CEP;P3P9g01mECEDgP0P1P1P1PfPzCGPfCG,}5P@g01nGg01oI5odg020K,O?P@g021Ng022Q5ocg023T,O?P@g024Wg025Z5odg026],O?P@g027`g028c5oZg029f,O?g02:ig02;l5odg02<o,O?5N@CZCZCZCZCZCZCZCZdo"). Qed.
