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
Ltac2 kr_t_AsTail_rderr_defs () := "I47Corelib4Init9Datatypes4list00K79OSSVerify5KrLib3bpA2HF9HSymExec23SX24expr02C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z03K79OSSVerify5KrLib3bpA2HF9HSymExec23SX24expr01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib3bpA2HF9HSymExec23SX24expr03C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02K79OSSVerify5KrLib3bpA2HF9HSymExec23SX28sidecond01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init5Logic2eq00I47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic3and01I47Corelib4Init9Datatypes4prod00C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC79OSSVerify5KrLib3bpA2HF9HSymExec23SX25s_logC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpA2HF9HSymExec23SX25carryC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2HF7HSymAux;log_coveredC1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib3bpA2HF9HSymExec23SX28sidecond00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05K4ELinuxProcessSemantics5Riscv5Instr5aluop06K4ELinuxProcessSemantics5Riscv5Instr5aluop01K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I79OSSVerify5KrLib3bpA2HF9HSymExec23SX29sym_state00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib3bpA2HF9HSymExec23SX27scripts00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_rderr_defs2rBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_rderr_defs4scsBC1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib3bpA2HF9HSymExec23SX26kentry00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_rderr_defs4knV0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_rderr_defs:ot_regionsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_rderr_defs2rCC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_rderr_defs4scsCC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_rderr_defs4knC0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_rderr_defs2rDC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_rderr_defs4scsDC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_rderr_defs3knCC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K79OSSVerify5KrLib3bpA2HF9HSymExec23SX24expr04C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib3bpA2HF9HSymExec23SX25saddr01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib3bpA2HF9HSymExec23SX28sidecond06C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03K47Corelib7Numbers7BinNums1Z01c69OSSVerify5KrLib3bpA3DrvAAsTail_rderr_defs2rEC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_rderr_defs4scsEC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_rderr_defs4knE0C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib3bpA2HF9HSymExec23SX24expr07C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond04c69OSSVerify5KrLib3bpA3DrvAAsTail_rderr_defs2rFC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_rderr_defs4scsFC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_rderr_defs5knF0_C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_rderr_defs3rF0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_rderr_defs5scsF0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_rderr_defs5knF00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_rderr_defs2rGC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_rderr_defs4scsGC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_rderr_defs4knG0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_rderr_defs2rHC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_rderr_defs4scsHC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_rderr_defs4knH0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_rderr_defs3rG3C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_rderr_defs5scsG3C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_rderr_defs5knG30C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_rderr_defs3rH3C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_rderr_defs5scsH3C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_rderr_defs5knH30C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_rderr_defs3rF4C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_rderr_defs5scsF4C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_rderr_defs5knF40C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_rderr_defs3rG4C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_rderr_defs5scsG4C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_rderr_defs5knG40C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_rderr_defs3rH4C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_rderr_defs5scsH4C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_rderr_defs5knH40C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00K79OSSVerify5KrLib3bpA2HF9HSymExec23SX26kentry06C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib3bpA2HF9HSymExec23SX26kentry02C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib3bpA2HF9HSymExec23SX26kentry01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib3bpA2HF9HSymExec23SX26kentry05C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib3bpA2HF9HSymExec23SX26kentry07C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib3bpA2HF9HSymExec23SX26kentry04C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib3bpA3Drv;AsStdioCall9stdio_res01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib3bpA3Drv;AsStdioCall:stdio_callC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpA2HF9HSymExec23SX24s_pcC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I79OSSVerify5KrLib3bpA2HF9HSymExec23SX24expr00C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5aluop0:c69OSSVerify5KrLib3bpA3DrvAAsTail_rderr_defs5AEXITC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib3bpA3Drv;AsStdioCall9stdio_res00C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop02c69OSSVerify5KrLib3bpA3DrvAAsTail_rderr_defs7AMEMCPYC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_rderr_defs;ASTRNLEN_TRC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_rderr_defs2rIC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_rderr_defs<ASTDIO_WRITEC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_rderr_defs3rI3C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_rderr_defs3rI4C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_rderr_defs3srHC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_rderr_defs3knHC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_rderr_defs4scOFC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_rderr_defs4srG3C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_rderr_defs4knG3C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_rderr_defs4scG3C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_rderr_defs4srH3C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_rderr_defs4knH3C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_rderr_defs4scH3C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_rderr_defs4srF4C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_rderr_defs4knF4C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_rderr_defs4scF4C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_rderr_defs4srH4C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_rderr_defs4knH4C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3DrvAAsTail_rderr_defs4scH4C1?~~~~~~~~~~~~~~~".
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
Definition FMT : Z := 0x201f4.
Definition NPRE : Z := 19.
Definition NSUF : Z := 1.
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
   (0x7fffc038, 8%nat, 0x0); (0x7fffc040, 8%nat, 0x0)].

Definition OT_SHOFFS : list Z := [(-592); (-574)].
Definition OT_SHOFFS2 : list Z := [(-592); (-574); (-573)].
Definition OT_SHX : list expr := [(EAlu ALU_AND (EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EAlu ALU_ADD (EVar 2) (EVar 141)) (ELit (-1))) (ELit 3)) (ELit 2147450880)) (ELit (-8))); (EAlu ALU_AND (EAlu ALU_ADD (EAlu ALU_SRL (EVar 2) (ELit 3)) (ELit 2147450880)) (ELit (-8))); (EAlu ALU_AND (EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) (EVar 141)) (ELit (-574))) (ELit 3)) (ELit 2147450880)) (ELit (-8))); (EAlu ALU_AND (EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) (EVar 141)) (ELit (-573))) (ELit 3)) (ELit 2147450880)) (ELit (-8)))].
Fixpoint shxkn (l : list expr) : list kentry :=
  match l with [] => [] | e :: r => KRange e 0x20000000000 0x10007fff8000 :: KZero (SA e 0) (ELit 8) :: shxkn r end.

Definition knV0 : list kentry :=
  [KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000; KWr (SA (EVar 0) (-128 - OT_FR)) OT_FR;
   KRange (EVar 2) AHI_LO AAPP_HI;
   KImg 0x10000 0x91000; KImg 0x17c000 0x185000;
   KWord (SA (EVar 0) (-176)) 8 (EVar 2); KWord (SA (EVar 0) (-184)) 8 (ELit 0xe8a10);
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

Definition logM1 : list sentry := [SE (SA (EVar 0) (-574)) 1 (ELit 32);
   SE (SA (EVar 0) (-576)) 2 (ELit 28271);
   SE (SA (EVar 0) (-584)) 8 (ELit 2338053693894893668);
   SE (SA (EVar 0) (-592)) 8 (ELit 7018141077071293539)].
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

Definition FQMAX : Z := 61.
Definition knF0_ : list kentry := Eval vm_compute in px_range 1 FQMAX knE.
Definition ssF0 : sym_state := SS AMEMCPY_RET srF0 [] knF0_ 195.
Definition rF := Eval vm_compute in runT (SCR [true; false; true; false; false] [] []) ssF0.
Definition srF : list expr := Eval vm_compute in s_regs (fst (fst rF)).
Definition knF : list kentry := Eval vm_compute in kn_afterT rF knF0_.
Definition knG0 : list kentry := Eval vm_compute in kn_readd 0 60 (kn_cut 0 (BUF_LO + NPRE) BUF_HI IHI knF).
Definition srG0 : list expr := Eval vm_compute in sr_after_call_j srF KEPT_MCI 195.

Definition knF00 : list kentry := Eval vm_compute in px_range 0 0 knE.
Definition rF0 := Eval vm_compute in runT (SCR [false; true] [] []) (SS AMEMCPY_RET srF0 [] knF00 195).
Definition srF0' : list expr := Eval vm_compute in s_regs (fst (fst rF0)).
Definition knF0' : list kentry := Eval vm_compute in kn_afterT rF0 knF00.
Definition knG00 : list kentry := Eval vm_compute in kn_readd 0 60 (kn_cut 0 (BUF_LO + NPRE) BUF_HI IHI knF0').

Definition ssG0 : sym_state := SS AMEMCPY_RET srG0 [] knG0 227.
Definition rG := Eval vm_compute in runT (SCR [false] [] []) ssG0.
Definition srG : list expr := Eval vm_compute in s_regs (fst (fst rG)).
Definition knG : list kentry := Eval vm_compute in kn_afterT rG knG0.
Definition knH0 : list kentry := Eval vm_compute in kn_readd 0 60 (kn_cut 0 (BUF_LO + NPRE) BUF_HI IHI knG).
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

Definition knG30 : list kentry := Eval vm_compute in kn_readd (60 + 1) (60 + NSUF) (kn_cut 0 (BUF_LO + NPRE) BUF_HI IHI knF).
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

Definition knF40 : list kentry := Eval vm_compute in px_range (60 + NSUF + 1) 131071 knE.
Definition ssF40 : sym_state := SS AMEMCPY_RET srF0 [] knF40 195.
Definition rF4 := Eval vm_compute in runT (SCR [true] [] []) ssF40.
Definition srF4 : list expr := Eval vm_compute in s_regs (fst (fst rF4)).
Definition knF4 : list kentry := Eval vm_compute in kn_afterT rF4 knF40.
Definition scF4 : stdio_res := Eval vm_compute in sc_of 195 srF4 knF4.
Definition srG40 : list expr := Eval vm_compute in sc_sr scF4.
Definition knG40 : list kentry := Eval vm_compute in kn_readd (60 + NSUF + 1) 131071 (sc_kn scF4).

Definition ssG40 : sym_state := SS (sc_ret scF4) srG40 [] knG40 227.
Definition rG4 := Eval vm_compute in runT (SCR [false] [] []) ssG40.
Definition srG4 : list expr := Eval vm_compute in s_regs (fst (fst rG4)).
Definition knG4 : list kentry := Eval vm_compute in kn_afterT rG4 knG40.

Definition logNL : list sentry := [SE (SA (EVar 0) (-592)) 1 (ELit 10)].
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

Definition ot_regions : list sregion := [(SA (EVar 0) (-128 - OT_FR), OT_FR); (SA (ELit 0) 0x187f60, 232)].
Definition scsB : list sidecond := Eval vm_compute in (snd (fst rB)).
Lemma factsB : snd (fst rB) = scsB /\ snd (fst (carry (s_log (fst (fst rB))) knV0 [])) = [] /\ log_covered ot_regions (s_log (fst (fst rB))) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_rderr_defs ()) [] "p;1p;3p;4p;2g0000j13Tg000Pj1DTg001Pj10Tg0025j15Tg002Zj1=Tg0038j16Tg0048j3:Tg0058j1@Tg005Vj4?Tg006Zj19Tg007:j3>Tg007Zj31Tg0084j24Tg008Oj27Tg008ij4<Tg009Dj28Tg009dj32Tg00:Aj3;Tg00:^j1CTg00;]j3BTg00<\j2ATg00=[R0#3R1g00>_g00??g00@1g00@]g00AI#Dg00AhR2#0#0#5R3#0#5#0#0#0#0#=#63:%=2#63:%53#@#6C?%90R35>0R0;10A1133R2g00BMR4g00BmR5;15R6'41710P2P617131745C<C<g00CMR61861g00DRg00EU32R27;1g00FV511g00GY#3R01801%34A2612#CR2g00H[%943B327;1=113g00I^/A2=145'4'4do"). Qed.
Definition scsC : list sidecond := Eval vm_compute in (snd (fst rC)).
Lemma factsC : snd (fst rC) = scsC /\ snd (fst (carry (s_log (fst (fst rC))) knC0 [])) = [] /\ log_covered ot_regions (s_log (fst (fst rC))) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_rderr_defs ()) [] "p;1p;3p;2p;4g0000j13Tg006Zj18Tg007Zj30Tg0084j21Tg008Oj27Tg008ij46Tg009Dj25Tg009dj32Tg00:Aj34Tg00:^j1;Tg00;]j3:Tg00<\j29Tg00=[R0#3R1%80R0;00R2g00BMR3g00BmR4;04R5,121710R6P2P5P61734C6C6g00CMR61561g00DRg00Jg32R5741g00Kh501g00GY#3R21521%33A2615#;R5g00Lk%833:32741=010g00I^/95=034'1'1do"). Qed.
Definition scsD : list sidecond := Eval vm_compute in (snd (fst rD)).
Lemma factsD : snd (fst rD) = scsD /\ snd (fst (carry (s_log (fst (fst rD))) knC [])) = [] /\ log_covered ot_regions (s_log (fst (fst rD))) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_rderr_defs ()) [] "p;1p;3p;2p;4g0000j13Tg006Zj18Tg007Zj30Tg0084j21Tg008Oj27Tg008ij46Tg009Dj25Tg009dj32Tg00:Aj34Tg00:^j1;Tg00;]j3:Tg00<\j29Tg00=[R0#3R1%80R0;00R2g00BMR3g00BmR4;04R5,121710R6P2P5P61734C6C6g00CMR61561g00DRg00Mn32R5741g00No501g00GY#3R21521%33A2615#;R5g00P2%833:32741=010g00I^/95=034'1'1do"). Qed.
Definition scsE : list sidecond := Eval vm_compute in (snd (fst rE)).
Lemma factsE : snd (fst rE) = scsE /\ snd (fst (carry (s_log (fst (fst rE))) knE0 [])) = [] /\ log_covered ot_regions (s_log (fst (fst rE))) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_rderr_defs ()) [] "p;1p;3p;4p;2g0000j14Tg00Q4j10Tg000Pj1;Tg0038j1GTg00QSj3BTg005Vj4ATg0048j3@Tg00RSj2>Tg00STj4=Tg006Zj17Tg007:j3<Tg007Zj32Tg0084j26Tg008Oj25Tg008ij48Tg009Dj29Tg009dj33Tg00:Aj3:Tg00:^j1FTg00;]j3DTg00<\j2ETf0R0#0#0p=C%00#0#0#0#0#0#0#0p=?%00#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=1g00=[R0#4R1g00>_R2g00TXg00@]R3g00AI#0R4#0R5#0#C#?#1#1#1#1#1#1#1#1#;R6g00UJR7#GR83BP6CA%;5=@36/>7P4P2P8C=%70R85<05<0R0;20A2188R2g00BMR4g00BmR7;27R6'61510P2P615181547C8C8g00CMR61961g00DRg00Uh33R27:1g00Vi521g00GY#4R01901%44A3612#FR2g00Wl%743D337:1=218g00I^/E2=247'6'6do"). Qed.
Definition scsF : list sidecond := Eval vm_compute in (snd (fst rF)).
Lemma factsF : snd (fst rF) = scsF /\ snd (fst (carry (s_log (fst (fst rF))) knF0_ [])) = [] /\ log_covered ot_regions (s_log (fst (fst rF))) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_rderr_defs ()) [] "p;1p;3p;4p;2g0000j18Tg000Pj1=Tg001Pj17Tg0025j15Tg002Zj1DTg0038j1:Tg0048j36Tg00Q4j10Tg005Vj44Tg00Xoj4ETg00QSj3CTg006Zj1BTg007:j33Tg007Zj32Tg0084j2;Tg008Oj29Tg008ij4@Tg009Dj2ATg009dj3<Tg00:Aj3?Tg00:^j1ITg00;]j3HTg00<\j2GTf0R0#0#0p=>%00#0#0#0#0#0#0#0p=F%00#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=1g00=[R0#8R1g00>_R2g00??R3g00@1R4g00@]R5g00AIR6#=R7g00AhR8#7#7#7#5#5#5#5#7#5#D#:R936R:%D8#:R836%>6R;#>R<#0#F#1#1#1#1#1#1#1#1#=R=C4P2P3%=;R;=648P=C4g00BmR8g00YoP;A657==659C4P2g00ZaP:P;C4P8g00[SP8P6P<P=CEg00UJ#:R<9C5==C5<C4%B0R<530530530530530R0;20A21<<R5g00BMR=?288R6';1910P5P6191<19=8C@C@g00CMR61A61g00DRg00\E3<R57?1g00]F521g00GY#8R01A01%8=A<615#IR5g00^I%B=3H3<7?1=21<g00I^/G5=2=8';';do"). Qed.
Definition scsF0 : list sidecond := Eval vm_compute in (snd (fst rF0)).
Lemma factsF0 : snd (fst rF0) = scsF0 /\ snd (fst (carry (s_log (fst (fst rF0))) knF00 [])) = [] /\ log_covered ot_regions (s_log (fst (fst rF0))) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_rderr_defs ()) [] "p;1p;3p;4p;2g0000j17Tg000Pj1:Tg00Q4j10Tg0048j36Tg001Pj14Tg0025j13Tg002Zj1CTg0038j1BTg005Vj4<Tg006Zj1;Tg007:j3@Tg007Zj32Tg0084j28Tg008Oj29Tg008ij4>Tg009Dj2?Tg009dj35Tg00:Aj3=Tg00:^j1FTg00;]j3ETg00<\j2DTf0R0#0#0p=A%00#0#0#0#0#0#0#0p=G%00#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=1g00=[R0#7R1g00BmR2g00Yog00AIR3#AR4#:R5g00@]R6%:3R3%04#A#G#1#1#1#1#1#1#1#1#:566g00Ah#4#4#4#3#3#3#3#4#3#C#BR436C<g00>_g00ZaA6634P5C<%;0R55@05@0R0;20A2155R4g00BMR3?222R6'81910P4P619151932C>C>g00CMR61?61g00DRg00_M35R47=1g00`O521g00GY#7R01?01%73A5614#FR4g00aS%;33E357=1=215g00I^/D4=232'8'8do"). Qed.
Definition scsG : list sidecond := Eval vm_compute in (snd (fst rG)).
Lemma factsG : snd (fst rG) = scsG /\ snd (fst (carry (s_log (fst (fst rG))) knG0 [])) = [] /\ log_covered ot_regions (s_log (fst (fst rG))) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_rderr_defs ()) [] "p;1p;3p;4p;2g0000j1:Tg000Pj1?Tg00Q4j10Tg0048j36Tg001Pj14Tg0025j13Tg002Zj1<Tg0038j15Tg0058j1BTg005Vj4ATg006Zj1@Tg007:j3GTg007Zj32Tg0084j27Tg008Oj29Tg008ij4>Tg009Dj2=Tg009dj38Tg00:Aj3;Tg00:^j1ETg00;]j3DTg00<\j2FTf0R0#0#0#0#0p=C%00#0#0#0#0#0#0#0p=H%00#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=1g00=[R0#:R1g00>_g00??g00@1g00@]R2g00AIR3#?%03#C#H#1#1#1#1#1#1#1#1#?562g00AhR2#4#4#4#3#3#3#3#4#3#<#536%<2#536%B2#5CA%@0R25G0R0;20A2122R3g00BMR4g00BmR5;25R6'71910P3P619121945C>C>g00CMR61=61g00DRg00bW38R37;1g00cX521g00GY#:R01=01%:4A8613#ER3g00d[%@43D387;1=212g00I^/F3=245'7'7do"). Qed.
Definition scsH : list sidecond := Eval vm_compute in (snd (fst rH)).
Lemma factsH : snd (fst rH) = scsH /\ snd (fst (carry (s_log (fst (fst rH))) knH0 [])) = [] /\ log_covered ot_regions (s_log (fst (fst rH))) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_rderr_defs ()) [] "p;1p;3p;2p;4g0000j13Tg006Zj18Tg007Zj30Tg0084j21Tg008Oj27Tg008ij46Tg009Dj25Tg009dj32Tg00:Aj34Tg00:^j1;Tg00;]j3:Tg00<\j29Tg00=[R0#3R1%80R0;00R2g00BMR3g00BmR4;04R5,121710R6P2P5P61734C6C6g00CMR61561g00DRg00e^32R5741g00f_501g00GY#3R21521%33A2615#;R5g00gb%833:32741=010g00I^/95=034'1'1do"). Qed.
Definition scsI : list sidecond := Eval vm_compute in (snd (fst rI)).

Definition scsG3 : list sidecond := Eval vm_compute in (snd (fst rG3)).
Lemma factsG3 : snd (fst rG3) = scsG3 /\ snd (fst (carry (s_log (fst (fst rG3))) knG30 [])) = [] /\ log_covered ot_regions (s_log (fst (fst rG3))) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_rderr_defs ()) [] "p;1p;3p;2p;4g0000j13Tg006Zj18Tg007Zj30Tg0084j21Tg008Oj27Tg008ij46Tg009Dj25Tg009dj32Tg00:Aj34Tg00:^j1;Tg00;]j3:Tg00<\j29Tg00=[R0#3R1%80R0;00R2g00BMR3g00BmR4;04R5,121710R6P2P5P61734C6C6g00CMR61561g00DRg00he32R5741g00ig501g00GY#3R21521%33A2615#;R5g00jk%833:32741=010g00I^/95=034'1'1do"). Qed.
Definition scsH3 : list sidecond := Eval vm_compute in (snd (fst rH3)).
Lemma factsH3 : snd (fst rH3) = scsH3 /\ snd (fst (carry (s_log (fst (fst rH3))) knH30 [])) = [] /\ log_covered ot_regions (s_log (fst (fst rH3))) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_rderr_defs ()) [] "p;1p;3p;2p;4g0000j13Tg006Zj18Tg007Zj30Tg0084j21Tg008Oj27Tg008ij46Tg009Dj25Tg009dj32Tg00:Aj34Tg00:^j1;Tg00;]j3:Tg00<\j29Tg00=[R0#3R1%80R0;00R2g00BMR3g00BmR4;04R5,121710R6P2P5P61734C6C6g00CMR61561g00DRg00ko32R5741g00m1501g00GY#3R21521%33A2615#;R5g00n5%833:32741=010g00I^/95=034'1'1do"). Qed.
Definition scsI3 : list sidecond := Eval vm_compute in (snd (fst rI3)).

Definition scsF4 : list sidecond := Eval vm_compute in (snd (fst rF4)).
Lemma factsF4 : snd (fst rF4) = scsF4 /\ snd (fst (carry (s_log (fst (fst rF4))) knF40 [])) = [] /\ log_covered ot_regions (s_log (fst (fst rF4))) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_rderr_defs ()) [] "p;1p;4p;3p;2g0000j13Tg00Q4j10Tg000Pj1DTg00Xoj4CTg0038j1?Tg00QSj38Tg005Vj4>Tg006Zj17Tg007:j3<Tg007Zj32Tg0084j26Tg008Oj24Tg008ij4;Tg009Dj2:Tg009dj35Tg00:Aj39Tg00:^j1BTg00;]j3@Tg00<\j2ATf0R0#0#0#0#0p=E%00#0#0#0#0#0#0#0p==%00#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=1g00=[R0#3R1g00BmR2g00[SP2g00AIR3%E3R3%03#=#1#1#1#1#1#1#1#1#DR3CCg00@]R4g00UJ#?R59843;85C>%70R55<0R0;20A2155R4g00BMR3?222R6'61410P4P614151432C;C;g00CMR61:61g00DRg00o935R4791g010;521g00GY#3R01:01%33A5614#BR4g011?%733@35791=215g00I^/A4=232'6'6do"). Qed.
Definition scsG4 : list sidecond := Eval vm_compute in (snd (fst rG4)).
Lemma factsG4 : snd (fst rG4) = scsG4 /\ snd (fst (carry (s_log (fst (fst rG4))) knG40 [])) = [] /\ log_covered ot_regions (s_log (fst (fst rG4))) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_rderr_defs ()) [] "p;1p;3p;4p;2g0000j13Tg000Pj1DTg001Pj10Tg0025j17Tg002Zj1=Tg0038j15Tg0048j3:Tg0058j1@Tg005Vj4?Tg006Zj19Tg007:j3>Tg007Zj31Tg0084j24Tg008Oj26Tg008ij4<Tg009Dj28Tg009dj32Tg00:Aj3;Tg00:^j1CTg00;]j3BTg00<\j2ATg00=[R0#3R1g00>_g00??g00@1g00@]g00AI#Dg00AhR2#0#0#7#0#7#0#0#0#0#=#53:%=2#53:%@2#5C?%90R25>0R0;10A1122R3g00BMR4g00BmR5;15R6'41610P3P616121645C<C<g00CMR61861g00DRg012C32R37;1g013E511g00GY#3R01801%34A2613#CR3g014I%943B327;1=112g00I^/A3=145'4'4do"). Qed.
Definition scsH4 : list sidecond := Eval vm_compute in (snd (fst rH4)).
Lemma factsH4 : snd (fst rH4) = scsH4 /\ snd (fst (carry (s_log (fst (fst rH4))) knH40 [])) = [] /\ log_covered ot_regions (s_log (fst (fst rH4))) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_rderr_defs ()) [] "p;1p;3p;2p;4g0000j13Tg006Zj18Tg007Zj30Tg0084j21Tg008Oj27Tg008ij46Tg009Dj25Tg009dj32Tg00:Aj34Tg00:^j1;Tg00;]j3:Tg00<\j29Tg00=[R0#3R1%80R0;00R2g00BMR3g00BmR4;04R5,121710R6P2P5P61734C6C6g00CMR61561g00DRg015M32R5741g016O501g00GY#3R21521%33A2615#;R5g017S%833:32741=010g00I^/95=034'1'1do"). Qed.
Definition scsI4 : list sidecond := Eval vm_compute in (snd (fst rI4)).

Lemma ot_itinerary :
  (s_pc (fst (fst rB)), s_pc (fst (fst rC)), s_pc (fst (fst rD)), s_pc (fst (fst rE))) = (AMEMCPY, AMEMCPY, ASTRNLEN_TR, AMEMCPY)
  /\ (s_pc (fst (fst rF)), s_pc (fst (fst rF0)), s_pc (fst (fst rG)), s_pc (fst (fst rH)), s_pc (fst (fst rI))) = (AMEMCPY, AMEMCPY, AMEMCPY, ASTDIO_WRITE, AEXIT)
  /\ (s_pc (fst (fst rG3)), s_pc (fst (fst rH3)), s_pc (fst (fst rI3))) = (ASTDIO_WRITE, ASTDIO_WRITE, AEXIT)
  /\ (s_pc (fst (fst rF4)), s_pc (fst (fst rG4)), s_pc (fst (fst rH4)), s_pc (fst (fst rI4))) = (ASTDIO_WRITE, AMEMCPY, ASTDIO_WRITE, AEXIT)
  /\ stdio_call 259 srH knH = Some scOF /\ stdio_call 227 srG3 knG3 = Some scG3 /\ stdio_call 259 srH3 knH3 = Some scH3
  /\ stdio_call 195 srF4 knF4 = Some scF4 /\ stdio_call 259 srH4 knH4 = Some scH4.
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_rderr_defs ()) [] "p%0p%1p&0p;2p;3p;1p;<p;4g009Dj2vTg007Zj3LTg018Wk10DTg0025j11Tg001Pj10Tg0058j1GTg000Pj16Tg002Zj1:Tg00Q4j12Tg0038j1@Tg00QSj3nTg006Zk10?Tg0199j3KTg01:;j2gTg01;=j3BTg00RSj2ITg01<?k20CTg01=Ak20<Tg01>Ck20;Tg01?El<pTg01@Ij2RTg0084j2]Tg008Ok207Tg0000k10ATg01@kj4HTg01AKj3qTg0048j3xTg007:j34Tg008ik40@Tg009dj3wTg01BNk104Tf0R0#0#1#1p=d%10#0#1#0p=a%10#0#0#0p=<%00#1#1#1p=U%10#1#1#0p=l%00#Gp=fg01CLR1P1f1R2P0CHp=e%00#1#0#0p=`%00#0#0#Gp=9f4R3P1f3R4P1f2R5P2CHP0CHp=kP5P1P2P0CHp>03%00#1#0#1p>02%00#0#0#1p=\%00#1#1#0p==%10#1#0#1p=X%10#1p=T%10#1#1#1p=D%00#0#0#0p=7%00#0#1#0p=N%00#0p=;g00@]R6%@07x2p=S%20#2p>05%20#2#2#2p=[%20#2#2p=r%20#2#2#2#2#2#2#2p=o%20#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2p=VAx620p=J%G0#@p=A%00#:p={%10#0#1#1p=Q%10#1#0#0p=C%00#0#G#@p=P%00#1p=O%10#0#0#1p=ug01CjR7%62;40p>01%65%62=470547p=E%62=47094759474p=mA4720947594749473p=Y%64A47209475547p>001I45?B20p=tg01Dj?x20p=j%10#1#1#1#1#1#1#1p=c%00#0#0p=?%00#0#0#0#0#0#0#0p=Wg01EV?x20p=ig00UJR8,I0p=h%05#:,I4?B20p=>%10#0p=z%00#0#:,I2p=y%:0,I2p=~%15#0#0#0#:,I4?B20p=M1I45%G0#@7B2p=s%00#0#1#1p=Z%10#Gp>0>%@09B52p>0=%10#0#0p>0:g00GYR9%G4,I3?B52;40p=8A4920949594949493p=3AB452=490p>0B%:4,I3?B52=490p=5f6R:f5R;;B3AB452=490549p=|A4920949594949493949;949:p=bA4920p>08P3P420752P0H0@p=_g00CMR3Aw5207w4$04p=FAw5209w34p>06P5P1P2&040CHp>09P2P1P0g01FBCHp=}AL452/]0p=^1v11R0/v1R5/v1R4P5P0g00AhR2#d#a#<#U#l#fR:/e:R;%`2#U#`#U#9P:DkR<;L<1v41S00P4P5B030;:%d2$02#a#\#=#fR;%d2#\#X#=#a#fR=DkR>;L>S011e;;>030=R?=L5?S02P5P01e;:P;P=DkR==L4=S03g01GFR@$0DRA%12RB#0S04#0S05#0S06#0S07#1S08#T#DRC#dS09#0S0:#0#9RD%02RE#GRF%d2#=#=#7#N#fRGg00AIRH#6RI%0ERJ#1RK#0RL#1RM#0RN#;RO#0S0;#:S0<'SRP%2HRH#2RQ$05RR#[RS#rS0=#2S0>#2#oS0?#2#VRT#VS0@#2S0A#2S0B#2RU#2RV#2RW#2RX#2RY#2RZ#r#[#o#V#V#V#VR[#6R\,JIR]%0JRJ#1S0C#1R^#1R_#1R`#0Ra#0S0D#:'SPP%1ERE#0Rb#0S0E#0Rc#0Rd#ARe%@8RfPf%1KRK#0Rg#0Rh#;S0F#{S0G,SIRi&05[#[#V#V#VR[#2#[S0H#2S0I#2S0J#[S0K#2S0L#2S0M#2S0N#2S0O#2S0P#2S0Q#r#oS0R#2S0S#2S0T#2S0U#2Rj#2#[S0V#2S0W#2S0X#[S0Y#2S0Z#2S0[#2S0\#2S0]#2S0^#2S0_#r#oS0`#2S0a#2S0b#2S0c#2Rk%@GPi%6TS0d%Q2#7#D#C#=#PS0e%2k#[RT%2TRT%2TRT%@DRl%A2RmAn6\fRn9n6fS0f%AKS0g5n6Ro5n6Pf%[TRT#6%2TRT%2TRT%2TRT%2TRT%2TRT%2TRT%12#O#C#U#l#Q#9S0h#@S0iPm%Q2#u#\#C#C#PS0jPf%6US0k%6VS0l%6WS0m%6XS0n%6YS0o%6ZS0p%rT#oRT%2TRT%2TRT%2T&0?7R7+013ECmDYDY3E3E3EDY3ECmH00S0qPf%1CS0r#0S0s#0RC#0RT#0#9PS%0JRZ#0RY#0S0t#0RX#0RW#0RV#:,SIS0uCtRUPf%1T#9PSPPCtRTPf%TC#9PSPPCtRC%1BS0v#1Rp#0S0w#f9K\8%6QR8/J\%:2'S%ABRB'j%1pS0x#1#T#cRp#?#7#WS0y#ARq'J%:J#@Rr'iRs%7VRV#?S0z#0#W#W#WS0{#GRt%TVRV#1#D#cRu#1#7#W#9Rv3KRw%hs%AJRJ'gRs1j8B/Jq/irRx?KtvRy%hx/gJRx%1`#{S0|#@R`,J]/jB/Jq/irRz?KtvR{%hz/gJRz%1a#:#@Ra,J]S0}/jB/Jq/irR]?KtvRt%h]/gJR]1jPB/Jq/irR|%0V#D#X#D#U#D#QRV#0#9%Uu#D#QRu#0#93KR}%h|/gJR|1JI`/jB/Jq/irR`%1V#9RV%1u#9Ru3KR~%h`/gJR`1JIaS0~/jB/Jq/irRr?KVuRu%hr/gJRJPI%<cS10PSPfC>Rc%zd,yIS11%<X#NRX#O#ARr7BSS12%;dS13#0S14#0,~IS15?BSmS16%1KRK#1Rd#z,yIS17%zX#AS187BSS19PI%?dS1:PSPlC>S1;PI%0KRKPSPfCMS1<PI%;KS1=#0S1>PSPrC>S1?PI%1gRgPSPmCMS1@PI%?gS1APSPlC>S1BPIPhPS%O2#Q#7#=#l#PCMS1CPI%1MRhPSQ18CMS1DPI%?hS1EPSPlC>S1FPIPNPSPoCMS1GPIQ0;PSg01HJ%1pRp#T#D#cRN#ARh;noS0;C>S1HPI%0LRL#1Rg#1S1I#;PSPhC>S1JPI%?gRgPS%AMS1KC>S1LPI%0LRL#<S1M#:PS%d2#=#=#l#a#fS1N#@S1OCtS1PPwPyP{PtP}P~PuPIQ0DPSPfC>RMPI%0^R^#;S0D#0PSQ0fC>RKPI%?_PSP\C>R_PI%;LS1Q#0RL#{S1RPS%1ZRd#1RX#1RV#1#\#<CsRBPIP^PSPfCMR^PwPyP{PtP}P~PuPI%1YS1S#?PSP8C>S1TPIQ0GPS%1bRa#0S0G#;S1U#:,SICtS1VPIQ0|PHPYCsS0|PI%:LPQQ04#1S04#1#z#=#DCsS1WPI%:gPSQ0t#1#T#N#=#D#U#N#U#N#=$02#N#7#=#`CsS0tQ0<,IIS0<Q08#ORg#1#N#Q#u#\#7#\#X#Z#`#Q#=#Z#\$0>80=SS08PIQ0C#0RQ#1RLPS%1NS0C#TRN#;#C#C#C#C#C#C#X#ACMS1XPI%?LPS%1N#D#cRN#0#c#c#AC>S1YPIQ1SPSQ05#1RL#1#Z#Z#Z#Z#Z#PCMS05PI%?XPS%<O#u#AC>S1SPI%0dRd#;S1Z#0PSQ0iC>S1[PIPdPSPfCMS1\PI%;VPSPiC>S1]PI%0QRQPSQ0uCMS0uPI%;QRQ#0PS%1aS1^#?S1_#:Ra,SIC>S1`PfQ09#1#7PSPfPfQ0:#<PSPfPfQ0r#1RV#1Rd#ORX#?PR%1N#c#c#APf%0VRV#0#7PSPePfQ0s#1RN#1#<PSPP1IfDRYPR%AES0sQ13,~IPSPfPIQ0E#1S0E#?S13PSPfPIQ1U#0S1UPSPf1IIaPSPfQ1=,~IPSPfPIQ1EPS%1ERE#0S1E#0S1=#;S0r#:Ra,SIS0:PIQ0FPS%6HS0FPIPOPSQ0B#6PIQ1QPSQ0A#6PIQ0DPSQ0@#6PIPQPSQ0:PIQ1ZPSPlPIPWPS%1W#T#X#PS1ZPIQ0x#0RW#;PS%02#a#`#7#=#P%GZ-0CIQ0y#0#7#W#9Q0{#?#9RZ5KI%1ERE#TRO#C,yI%0ERE#l#9+0<AK8vZQ0z#GQ1M#;#7#9+0;%?O#W#9%0gRg#W#9+0;1IIaPSP81yIEPS%12#a#N#<#`#PPIQ07#;PSQ0=#6PI%?LRLPSQ0>#6PIQ04#7PSQ0?#6Q0h,IfPSQ0FQ0v#O#9-0<YP}P~Pf%1gRg#1RY#;#\#9PS%=2#C#a#X#CCsPf%1YRY#<RE#7PS%@:Pf%<EPS%O2#X$02#`#7#PPf%ZY#7PS%O2#X#U#N#7#PPf%Og#C#7PS%O2#X#`#W#PPfQ06#D#=#D#<PSPqPf%\L#l#CRL#0PHPmPf%1LPHPmPf%uQRQ#0#U#CPHPmPf%1Q#N#ZPHPmPf%0N#<PS%@;Pf%1V#<PR%@FPf&0:XPRQ0C#ARXPf%1d#7PRPXPf%?p#7RX#d#<PSPfPf&0:X#7PSPf&0?9D8D8D8D8D8D8D8D8D8D8D8D8D8D8D8D3H0BD5D5D5F|FbD5D5D5D5D5D5D5D5D5F|D5D5F|D8D8D8D8D8R9+08D3D3RXFbD3D3D3RRFbD3D3D3D3D3D3D3D3D3M<p,R@Rd;LdRVPDPFQ1NPPQ0}PPPePrPmQ1R,SIR;PjQ1OP;Q0dQ0eQ0VQ0WQ0XQ1KPhPmQ0Y#6Q0ZQ0[Q0\Q0]Q0^Q0_Q0;PoPlQ18PmPrPfAn6nfR6PmPnQ0`Q0aQ0bQ0c00173ECmDYDY3E3E3EDY3ECmH00PUPTPCQ0w$0>Ro=K\oRoPwPsPyPxP{PzPtP]P}P|P~P`PuPJPcQ11?BS8RNQ15?BSfRQQ17?BSrRLPMPKP_PBP^PwPyP{PtP}P~PuQ1TQ1VQ0|Q1WQ0tQ08Q1XQ1YQ05Q1SPIQ1E#1#7PSQ0FQ1[Q1\Q1]Q0uQ1`PIQ1=PSQ0pCMPIQ0r#;PSQ0oPIQ1^#<PSQ0nPIQ1_#0PSQ0mPIQ0G#<PSQ0lPIQ1U#0PSQ0kPIQ0E#<PSQ0sPIQ13#0PSQ0jPIQ10PSPmPIQ14PSQ0iPIQ1:PSQ1ZPIQ1>PSPlPIQ1APS%O2#Q#N#D#u#PP9D5D5D5D5D5D5D5D5D5D5D5D5FbD5FbD3R9FbD3D3D3D3D3D3D3M<p,R@RS=LASRmPDPFPGPPPPPPPePfPfPiQ0qPUPTPCPoPwPsPyPxP{PzPtP]P}P|P~P`PuPJPcPNPQPLPRFbD3D3D3D3M<p,R@RR=LARRoPDPF%d2#=#Q#D#a#fR2PPQ0~PPPeP8P\P;P[%@2P;Q0dQ0eQ0HQ0IQ0JQ1KPhP\Q0K#6Q0LQ0MQ0NQ0OQ0PQ0QPfQ0gPlPrPfP8PfP6Q0fPnQ0RQ0SQ0TQ0U00173ECmDYDY3E3E3EDY3ECmH00PUPTPC%GW%Gp5K\R\PcPNPQPLPMPKP_PBP^PwPsPyPxP{PzPtP]P}P|P~P`Pu208J9FbD3D3D3D3D3M<p,R@R9=LA9RLPDPFPGPPQ1I#T#:,SIPPPePfPfPiQ0qPUPTPCQ0<%Gb80=HPcQ12Q16Q19Q1;Q1<Q1?Q1@Q1BQ1CQ1DQ1FQ1GQ1HQ1JQ1LQ1PP\PwPsPyPxP{PzPtP]P}P|P~P`PuPJPMPKP_PBP^PwPsPyPxP{PzPtP]P}P|P~P`PuPJQ1TQ1VQ0|Q1WQ0tPXD3D3D3D3D3D3D3D3D3D3D3D3D3D3D3M<p,R@RX=LAXRJ']Ru']R`']R~']R|']R}']R]']P4P<Q01P]Q00P>Q02P}P5P?Q03P|P4P=PVP~PAPdPmP`PAPSPoPuPAPRPLPJPAP9207AXD_D_D_D_D_D_D_D_P4P5P0g00=[$0ARX1v3XR3g00DRR9g00EUCFPXP3P9g00JgCF'ePXP3P9g00MnCFPXP3P9g00UhCFDkP5P1P0P1P1P1g01I6RJPJCHRLg01J<CHPJCHQ00P4P5PXP3P9g00\ECFPXP3P9g00_MCF'ePXP3P9g00bWH066090PXP3P9g00e^CFPXP3P9g01KFCFDkP5P1P0P1PLPJCHg01LGRLCH,}4P5PXP3P9g00heCFPXP3P9g00koCF'ePXP3P9g01MRH066090P1P1PLPLCH,}0P4P5P0PXP3P9g00o9CFPXP3P9g012CCF'ePXP3P9g015MCFPXP3P9g01NTCFDkP0P1P1P1PLPJCHPLCH,}5PAg01OVg01PX5qkg01QZ,R@PAg01R]g01S`5qjg01Tc,R@PAg01Ufg01Vi5qkg01Wl,R@PAg01Xog01Z25q[g01[5,R@g01\8g01];5qkg01^>,R@5LAC^C^C^C^C^C^C^C^do"). Qed.
