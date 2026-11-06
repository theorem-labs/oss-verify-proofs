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
Ltac2 kr_t_AsTail_open_defs () := "I47Corelib4Init9Datatypes4list00K79OSSVerify5KrLib3bpA2HF9HSymExec23SX24expr02C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z03K79OSSVerify5KrLib3bpA2HF9HSymExec23SX24expr01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib3bpA2HF9HSymExec23SX24expr03C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02K79OSSVerify5KrLib3bpA2HF9HSymExec23SX28sidecond01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init5Logic2eq00I47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic3and01I47Corelib4Init9Datatypes4prod00C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC79OSSVerify5KrLib3bpA2HF9HSymExec23SX25s_logC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpA2HF9HSymExec23SX25carryC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2HF7HSymAux;log_coveredC1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib3bpA2HF9HSymExec23SX28sidecond00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05K4ELinuxProcessSemantics5Riscv5Instr5aluop06K4ELinuxProcessSemantics5Riscv5Instr5aluop01K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I79OSSVerify5KrLib3bpA2HF9HSymExec23SX29sym_state00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib3bpA2HF9HSymExec23SX27scripts00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Drv@AsTail_open_defs2rBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Drv@AsTail_open_defs4scsBC1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib3bpA2HF9HSymExec23SX26kentry00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Drv@AsTail_open_defs4knV0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Drv@AsTail_open_defs:ot_regionsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Drv@AsTail_open_defs2rCC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Drv@AsTail_open_defs4scsCC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Drv@AsTail_open_defs4knC0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Drv@AsTail_open_defs2rDC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Drv@AsTail_open_defs4scsDC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Drv@AsTail_open_defs3knCC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K79OSSVerify5KrLib3bpA2HF9HSymExec23SX24expr04C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib3bpA2HF9HSymExec23SX25saddr01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib3bpA2HF9HSymExec23SX28sidecond06C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03K47Corelib7Numbers7BinNums1Z01c69OSSVerify5KrLib3bpA3Drv@AsTail_open_defs2rEC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Drv@AsTail_open_defs4scsEC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Drv@AsTail_open_defs4knE0C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib3bpA2HF9HSymExec23SX24expr07C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond04c69OSSVerify5KrLib3bpA3Drv@AsTail_open_defs2rFC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Drv@AsTail_open_defs4scsFC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Drv@AsTail_open_defs5knF0_C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Drv@AsTail_open_defs3rF0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Drv@AsTail_open_defs5scsF0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Drv@AsTail_open_defs5knF00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Drv@AsTail_open_defs2rGC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Drv@AsTail_open_defs4scsGC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Drv@AsTail_open_defs4knG0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Drv@AsTail_open_defs2rHC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Drv@AsTail_open_defs4scsHC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Drv@AsTail_open_defs4knH0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Drv@AsTail_open_defs3rG3C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Drv@AsTail_open_defs5scsG3C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Drv@AsTail_open_defs5knG30C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Drv@AsTail_open_defs3rH3C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Drv@AsTail_open_defs5scsH3C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Drv@AsTail_open_defs5knH30C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Drv@AsTail_open_defs3rF4C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Drv@AsTail_open_defs5scsF4C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Drv@AsTail_open_defs5knF40C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Drv@AsTail_open_defs3rG4C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Drv@AsTail_open_defs5scsG4C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Drv@AsTail_open_defs5knG40C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Drv@AsTail_open_defs3rH4C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Drv@AsTail_open_defs5scsH4C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Drv@AsTail_open_defs5knH40C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00K79OSSVerify5KrLib3bpA2HF9HSymExec23SX26kentry06C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib3bpA2HF9HSymExec23SX26kentry02C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib3bpA2HF9HSymExec23SX26kentry01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib3bpA2HF9HSymExec23SX26kentry05C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib3bpA2HF9HSymExec23SX26kentry07C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib3bpA2HF9HSymExec23SX26kentry04C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib3bpA3Drv;AsStdioCall9stdio_res01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib3bpA3Drv;AsStdioCall:stdio_callC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpA2HF9HSymExec23SX24s_pcC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I79OSSVerify5KrLib3bpA2HF9HSymExec23SX24expr00C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5aluop0:c69OSSVerify5KrLib3bpA3Drv@AsTail_open_defs5AEXITC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib3bpA3Drv;AsStdioCall9stdio_res00C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop02c69OSSVerify5KrLib3bpA3Drv@AsTail_open_defs7AMEMCPYC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Drv@AsTail_open_defs;ASTRNLEN_TRC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Drv@AsTail_open_defs2rIC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Drv@AsTail_open_defs<ASTDIO_WRITEC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Drv@AsTail_open_defs3rI3C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Drv@AsTail_open_defs3rI4C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Drv@AsTail_open_defs3srHC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Drv@AsTail_open_defs3knHC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Drv@AsTail_open_defs4scOFC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Drv@AsTail_open_defs4srG3C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Drv@AsTail_open_defs4knG3C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Drv@AsTail_open_defs4scG3C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Drv@AsTail_open_defs4srH3C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Drv@AsTail_open_defs4knH3C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Drv@AsTail_open_defs4scH3C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Drv@AsTail_open_defs4srF4C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Drv@AsTail_open_defs4knF4C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Drv@AsTail_open_defs4scF4C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Drv@AsTail_open_defs4srH4C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Drv@AsTail_open_defs4knH4C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Drv@AsTail_open_defs4scH4C1?~~~~~~~~~~~~~~~".
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
Definition FMT : Z := 0x201df.
Definition NPRE : Z := 17.
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

Definition OT_SHOFFS : list Z := [(-592); (-576)].
Definition OT_SHOFFS2 : list Z := [(-592); (-576); (-575)].
Definition OT_SHX : list expr := [(EAlu ALU_AND (EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EAlu ALU_ADD (EVar 2) (EVar 141)) (ELit (-1))) (ELit 3)) (ELit 2147450880)) (ELit (-8))); (EAlu ALU_AND (EAlu ALU_ADD (EAlu ALU_SRL (EVar 2) (ELit 3)) (ELit 2147450880)) (ELit (-8))); (EAlu ALU_AND (EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) (EVar 141)) (ELit (-576))) (ELit 3)) (ELit 2147450880)) (ELit (-8))); (EAlu ALU_AND (EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) (EVar 141)) (ELit (-575))) (ELit 3)) (ELit 2147450880)) (ELit (-8)))].
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

Definition logM1 : list sentry := [SE (SA (EVar 0) (-576)) 1 (ELit 32);
   SE (SA (EVar 0) (-584)) 8 (ELit 7954887939408031598);
   SE (SA (EVar 0) (-592)) 8 (ELit 7953747406983097443)].
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

Definition FQMAX : Z := 63.
Definition knF0_ : list kentry := Eval vm_compute in px_range 1 FQMAX knE.
Definition ssF0 : sym_state := SS AMEMCPY_RET srF0 [] knF0_ 195.
Definition rF := Eval vm_compute in runT (SCR [true; false; true; false; false] [] []) ssF0.
Definition srF : list expr := Eval vm_compute in s_regs (fst (fst rF)).
Definition knF : list kentry := Eval vm_compute in kn_afterT rF knF0_.
Definition knG0 : list kentry := Eval vm_compute in kn_readd 0 62 (kn_cut 0 (BUF_LO + NPRE) BUF_HI IHI knF).
Definition srG0 : list expr := Eval vm_compute in sr_after_call_j srF KEPT_MCI 195.

Definition knF00 : list kentry := Eval vm_compute in px_range 0 0 knE.
Definition rF0 := Eval vm_compute in runT (SCR [false; true] [] []) (SS AMEMCPY_RET srF0 [] knF00 195).
Definition srF0' : list expr := Eval vm_compute in s_regs (fst (fst rF0)).
Definition knF0' : list kentry := Eval vm_compute in kn_afterT rF0 knF00.
Definition knG00 : list kentry := Eval vm_compute in kn_readd 0 62 (kn_cut 0 (BUF_LO + NPRE) BUF_HI IHI knF0').

Definition ssG0 : sym_state := SS AMEMCPY_RET srG0 [] knG0 227.
Definition rG := Eval vm_compute in runT (SCR [false] [] []) ssG0.
Definition srG : list expr := Eval vm_compute in s_regs (fst (fst rG)).
Definition knG : list kentry := Eval vm_compute in kn_afterT rG knG0.
Definition knH0 : list kentry := Eval vm_compute in kn_readd 0 62 (kn_cut 0 (BUF_LO + NPRE) BUF_HI IHI knG).
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

Definition knG30 : list kentry := Eval vm_compute in kn_readd (62 + 1) (62 + NSUF) (kn_cut 0 (BUF_LO + NPRE) BUF_HI IHI knF).
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

Definition knF40 : list kentry := Eval vm_compute in px_range (62 + NSUF + 1) 131071 knE.
Definition ssF40 : sym_state := SS AMEMCPY_RET srF0 [] knF40 195.
Definition rF4 := Eval vm_compute in runT (SCR [true] [] []) ssF40.
Definition srF4 : list expr := Eval vm_compute in s_regs (fst (fst rF4)).
Definition knF4 : list kentry := Eval vm_compute in kn_afterT rF4 knF40.
Definition scF4 : stdio_res := Eval vm_compute in sc_of 195 srF4 knF4.
Definition srG40 : list expr := Eval vm_compute in sc_sr scF4.
Definition knG40 : list kentry := Eval vm_compute in kn_readd (62 + NSUF + 1) 131071 (sc_kn scF4).

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
ltac2:(KReplay.run1 (kr_t_AsTail_open_defs ()) [] "p;1p;3p;4p;2g0000j13Tg000Pj1DTg001Pj10Tg0025j15Tg002Zj1=Tg0038j16Tg0048j3:Tg0058j1@Tg005Vj4?Tg006Zj19Tg007:j3>Tg007Zj31Tg0084j24Tg008Oj27Tg008ij4<Tg009Dj28Tg009dj32Tg00:Aj3;Tg00:^j1CTg00;]j3BTg00<\j2ATg00=[R0#3R1g00>_g00??g00@1g00@]g00AI#Dg00AhR2#0#0R3#5#0#5#0#0#0#0#=#63:%=2#63:%03#5#@#6C?%90R35>0R0;10A1133R2g00BMR4g00BmR5;15R6'41710P2P617131745C<C<g00CMR61861g00DRg00EU32R27;1g00FU511g00GW#3R01801%34A2612#CR2g00HY%943B327;1=113g00I[/A2=145'4'4do"). Qed.
Definition scsC : list sidecond := Eval vm_compute in (snd (fst rC)).
Lemma factsC : snd (fst rC) = scsC /\ snd (fst (carry (s_log (fst (fst rC))) knC0 [])) = [] /\ log_covered ot_regions (s_log (fst (fst rC))) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_open_defs ()) [] "p;1p;3p;2p;4g0000j13Tg006Zj18Tg007Zj30Tg0084j21Tg008Oj27Tg008ij46Tg009Dj25Tg009dj32Tg00:Aj34Tg00:^j1;Tg00;]j3:Tg00<\j29Tg00=[R0#3R1%80R0;00R2g00BMR3g00BmR4;04R5,121710R6P2P5P61734C6C6g00CMR61561g00DRg00Jc32R5741g00Kc501g00GW#3R21521%33A2615#;R5g00Le%833:32741=010g00I[/95=034'1'1do"). Qed.
Definition scsD : list sidecond := Eval vm_compute in (snd (fst rD)).
Lemma factsD : snd (fst rD) = scsD /\ snd (fst (carry (s_log (fst (fst rD))) knC [])) = [] /\ log_covered ot_regions (s_log (fst (fst rD))) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_open_defs ()) [] "p;1p;3p;2p;4g0000j13Tg006Zj18Tg007Zj30Tg0084j21Tg008Oj27Tg008ij46Tg009Dj25Tg009dj32Tg00:Aj34Tg00:^j1;Tg00;]j3:Tg00<\j29Tg00=[R0#3R1%80R0;00R2g00BMR3g00BmR4;04R5,121710R6P2P5P61734C6C6g00CMR61561g00DRg00Mg32R5741g00Ng501g00GW#3R21521%33A2615#;R5g00Oi%833:32741=010g00I[/95=034'1'1do"). Qed.
Definition scsE : list sidecond := Eval vm_compute in (snd (fst rE)).
Lemma factsE : snd (fst rE) = scsE /\ snd (fst (carry (s_log (fst (fst rE))) knE0 [])) = [] /\ log_covered ot_regions (s_log (fst (fst rE))) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_open_defs ()) [] "p;1p;3p;4p;2g0000j14Tg00Pjj10Tg000Pj1;Tg0038j1GTg00QIj3BTg005Vj4ATg0048j3@Tg00RIj2>Tg00SJj4=Tg006Zj17Tg007:j3<Tg007Zj32Tg0084j26Tg008Oj25Tg008ij48Tg009Dj29Tg009dj33Tg00:Aj3:Tg00:^j1FTg00;]j3DTg00<\j2ETf0R0#0#0p=C%00#0#0#0#0#0#0#0p=?%00#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=1g00=[R0#4R1g00>_R2g00TNg00@]R3g00AI#0R4#0R5#0#C#?#1#1#1#1#1#1#1#1#;R6g00U@R7#GR83BP6CA%;5=@36/>7P4P2P8C=%70R85<05<0R0;20A2188R2g00BMR4g00BmR7;27R6'61510P2P615181547C8C8g00CMR61961g00DRg00U^33R27:1g00V^521g00GW#4R01901%44A3612#FR2g00W`%743D337:1=218g00I[/E2=247'6'6do"). Qed.
Definition scsF : list sidecond := Eval vm_compute in (snd (fst rF)).
Lemma factsF : snd (fst rF) = scsF /\ snd (fst (carry (s_log (fst (fst rF))) knF0_ [])) = [] /\ log_covered ot_regions (s_log (fst (fst rF))) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_open_defs ()) [] "p;1p;3p;4p;2g0000j17Tg000Pj1=Tg001Pj18Tg0025j13Tg002Zj1DTg0038j1:Tg0048j36Tg00Pjj10Tg005Vj45Tg00Xbj4ETg00QIj3CTg006Zj1BTg007:j34Tg007Zj32Tg0084j2;Tg008Oj29Tg008ij4@Tg009Dj2ATg009dj3<Tg00:Aj3?Tg00:^j1ITg00;]j3HTg00<\j2GTf0R0#0#0p=>%00#0#0#0#0#0#0#0p=F%00#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=1g00=[R0#7R1g00>_R2g00??R3g00@1R4g00@]R5g00AIR6#=R7g00AhR8#8#8#8#3#3#3#3#3#3#D#:R936R:%D8#:R836%>6R;#>R<#0#F#1#1#1#1#1#1#1#1#=R=C5P2P3%=;R;=648P=C5g00BmR8g00YbP;A657==659C5P2g00ZTP:P;C5P8g00[FP8P6P<P=CEg00U@#:R<9C5==C5<C5%B0R<540540540540540R0;20A21<<R5g00BMR=?288R6';1910P5P6191<19=8C@C@g00CMR61A61g00DRg00\83<R57?1g00]8521g00GW#7R01A01%7=A<615#IR5g00^:%B=3H3<7?1=21<g00I[/G5=2=8';';do"). Qed.
Definition scsF0 : list sidecond := Eval vm_compute in (snd (fst rF0)).
Lemma factsF0 : snd (fst rF0) = scsF0 /\ snd (fst (carry (s_log (fst (fst rF0))) knF00 [])) = [] /\ log_covered ot_regions (s_log (fst (fst rF0))) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_open_defs ()) [] "p;1p;3p;4p;2g0000j15Tg000Pj1:Tg00Pjj10Tg0048j37Tg001Pj16Tg0025j12Tg002Zj1CTg0038j1BTg005Vj4<Tg006Zj1;Tg007:j3@Tg007Zj33Tg0084j28Tg008Oj29Tg008ij4>Tg009Dj2?Tg009dj34Tg00:Aj3=Tg00:^j1FTg00;]j3ETg00<\j2DTf0R0#0#0p=A%00#0#0#0#0#0#0#0p=G%00#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=1g00=[R0#5R1g00BmR2g00Ybg00AIR3#AR4#:R5g00@]R6%:3R3%04#A#G#1#1#1#1#1#1#1#1#:576g00Ah#6#6#6#2#2#2#2#2#2#C#BR437C<g00>_g00ZTA7634P5C<%;0R55@05@0R0;30A3155R4g00BMR3?322R6'81910P4P619151932C>C>g00CMR61?61g00DRg00_=34R47=1g00`>531g00GW#5R01?01%53A4614#FR4g00aA%;33E347=1=315g00I[/D4=332'8'8do"). Qed.
Definition scsG : list sidecond := Eval vm_compute in (snd (fst rG)).
Lemma factsG : snd (fst rG) = scsG /\ snd (fst (carry (s_log (fst (fst rG))) knG0 [])) = [] /\ log_covered ot_regions (s_log (fst (fst rG))) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_open_defs ()) [] "p;1p;3p;4p;2g0000j1:Tg000Pj1?Tg00Pjj10Tg0048j35Tg001Pj16Tg0025j12Tg002Zj1<Tg0038j14Tg0058j1BTg005Vj4ATg006Zj1@Tg007:j3GTg007Zj33Tg0084j27Tg008Oj29Tg008ij4>Tg009Dj2=Tg009dj38Tg00:Aj3;Tg00:^j1ETg00;]j3DTg00<\j2FTf0R0#0#0#0#0p=C%00#0#0#0#0#0#0#0p=H%00#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=1g00=[R0#:R1g00>_g00??g00@1g00@]R2g00AIR3#?%03#C#H#1#1#1#1#1#1#1#1#?552g00AhR2#6#6#6#2#2#2#2#2#2#<#435%<2#435%B2#4CA%@0R25G0R0;30A3122R3g00BMR4g00BmR5;35R6'71910P3P619121945C>C>g00CMR61=61g00DRg00bD38R37;1g00cD531g00GW#:R01=01%:4A8613#ER3g00dF%@43D387;1=312g00I[/F3=345'7'7do"). Qed.
Definition scsH : list sidecond := Eval vm_compute in (snd (fst rH)).
Lemma factsH : snd (fst rH) = scsH /\ snd (fst (carry (s_log (fst (fst rH))) knH0 [])) = [] /\ log_covered ot_regions (s_log (fst (fst rH))) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_open_defs ()) [] "p;1p;3p;2p;4g0000j13Tg006Zj18Tg007Zj30Tg0084j21Tg008Oj27Tg008ij46Tg009Dj25Tg009dj32Tg00:Aj34Tg00:^j1;Tg00;]j3:Tg00<\j29Tg00=[R0#3R1%80R0;00R2g00BMR3g00BmR4;04R5,121710R6P2P5P61734C6C6g00CMR61561g00DRg00eH32R5741g00fH501g00GW#3R21521%33A2615#;R5g00gJ%833:32741=010g00I[/95=034'1'1do"). Qed.
Definition scsI : list sidecond := Eval vm_compute in (snd (fst rI)).

Definition scsG3 : list sidecond := Eval vm_compute in (snd (fst rG3)).
Lemma factsG3 : snd (fst rG3) = scsG3 /\ snd (fst (carry (s_log (fst (fst rG3))) knG30 [])) = [] /\ log_covered ot_regions (s_log (fst (fst rG3))) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_open_defs ()) [] "p;1p;3p;2p;4g0000j13Tg006Zj18Tg007Zj30Tg0084j21Tg008Oj27Tg008ij46Tg009Dj25Tg009dj32Tg00:Aj34Tg00:^j1;Tg00;]j3:Tg00<\j29Tg00=[R0#3R1%80R0;00R2g00BMR3g00BmR4;04R5,121710R6P2P5P61734C6C6g00CMR61561g00DRg00hL32R5741g00iM501g00GW#3R21521%33A2615#;R5g00jP%833:32741=010g00I[/95=034'1'1do"). Qed.
Definition scsH3 : list sidecond := Eval vm_compute in (snd (fst rH3)).
Lemma factsH3 : snd (fst rH3) = scsH3 /\ snd (fst (carry (s_log (fst (fst rH3))) knH30 [])) = [] /\ log_covered ot_regions (s_log (fst (fst rH3))) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_open_defs ()) [] "p;1p;3p;2p;4g0000j13Tg006Zj18Tg007Zj30Tg0084j21Tg008Oj27Tg008ij46Tg009Dj25Tg009dj32Tg00:Aj34Tg00:^j1;Tg00;]j3:Tg00<\j29Tg00=[R0#3R1%80R0;00R2g00BMR3g00BmR4;04R5,121710R6P2P5P61734C6C6g00CMR61561g00DRg00kS32R5741g00lT501g00GW#3R21521%33A2615#;R5g00mW%833:32741=010g00I[/95=034'1'1do"). Qed.
Definition scsI3 : list sidecond := Eval vm_compute in (snd (fst rI3)).

Definition scsF4 : list sidecond := Eval vm_compute in (snd (fst rF4)).
Lemma factsF4 : snd (fst rF4) = scsF4 /\ snd (fst (carry (s_log (fst (fst rF4))) knF40 [])) = [] /\ log_covered ot_regions (s_log (fst (fst rF4))) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_open_defs ()) [] "p;1p;4p;3p;2g0000j13Tg00Pjj10Tg000Pj1DTg00Xbj4CTg0038j1?Tg00QIj38Tg005Vj4>Tg006Zj17Tg007:j3<Tg007Zj32Tg0084j26Tg008Oj24Tg008ij4;Tg009Dj2:Tg009dj35Tg00:Aj39Tg00:^j1BTg00;]j3@Tg00<\j2ATf0R0#0#0#0#0p=E%00#0#0#0#0#0#0#0p==%00#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=1g00=[R0#3R1g00BmR2g00[FP2g00AIR3%E3R3%03#=#1#1#1#1#1#1#1#1#DR3CCg00@]R4g00U@#?R59843;85C>%70R55<0R0;20A2155R4g00BMR3?222R6'61410P4P614151432C;C;g00CMR61:61g00DRg00nZ35R4791g00o[521g00GW#3R01:01%33A5614#BR4g010^%733@35791=215g00I[/A4=232'6'6do"). Qed.
Definition scsG4 : list sidecond := Eval vm_compute in (snd (fst rG4)).
Lemma factsG4 : snd (fst rG4) = scsG4 /\ snd (fst (carry (s_log (fst (fst rG4))) knG40 [])) = [] /\ log_covered ot_regions (s_log (fst (fst rG4))) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_open_defs ()) [] "p;1p;3p;4p;2g0000j13Tg000Pj1DTg001Pj10Tg0025j17Tg002Zj1=Tg0038j15Tg0048j3:Tg0058j1@Tg005Vj4?Tg006Zj19Tg007:j3>Tg007Zj31Tg0084j24Tg008Oj26Tg008ij4<Tg009Dj28Tg009dj32Tg00:Aj3;Tg00:^j1CTg00;]j3BTg00<\j2ATg00=[R0#3R1g00>_g00??g00@1g00@]g00AI#Dg00AhR2#0#0#7#0#7#0#0#0#0#=#53:%=2#53:%@2#5C?%90R25>0R0;10A1122R3g00BMR4g00BmR5;15R6'41610P3P616121645C<C<g00CMR61861g00DRg011a32R37;1g012b511g00GW#3R01801%34A2613#CR3g013e%943B327;1=112g00I[/A3=145'4'4do"). Qed.
Definition scsH4 : list sidecond := Eval vm_compute in (snd (fst rH4)).
Lemma factsH4 : snd (fst rH4) = scsH4 /\ snd (fst (carry (s_log (fst (fst rH4))) knH40 [])) = [] /\ log_covered ot_regions (s_log (fst (fst rH4))) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_open_defs ()) [] "p;1p;3p;2p;4g0000j13Tg006Zj18Tg007Zj30Tg0084j21Tg008Oj27Tg008ij46Tg009Dj25Tg009dj32Tg00:Aj34Tg00:^j1;Tg00;]j3:Tg00<\j29Tg00=[R0#3R1%80R0;00R2g00BMR3g00BmR4;04R5,121710R6P2P5P61734C6C6g00CMR61561g00DRg014h32R5741g015i501g00GW#3R21521%33A2615#;R5g016l%833:32741=010g00I[/95=034'1'1do"). Qed.
Definition scsI4 : list sidecond := Eval vm_compute in (snd (fst rI4)).

Lemma ot_itinerary :
  (s_pc (fst (fst rB)), s_pc (fst (fst rC)), s_pc (fst (fst rD)), s_pc (fst (fst rE))) = (AMEMCPY, AMEMCPY, ASTRNLEN_TR, AMEMCPY)
  /\ (s_pc (fst (fst rF)), s_pc (fst (fst rF0)), s_pc (fst (fst rG)), s_pc (fst (fst rH)), s_pc (fst (fst rI))) = (AMEMCPY, AMEMCPY, AMEMCPY, ASTDIO_WRITE, AEXIT)
  /\ (s_pc (fst (fst rG3)), s_pc (fst (fst rH3)), s_pc (fst (fst rI3))) = (ASTDIO_WRITE, ASTDIO_WRITE, AEXIT)
  /\ (s_pc (fst (fst rF4)), s_pc (fst (fst rG4)), s_pc (fst (fst rH4)), s_pc (fst (fst rI4))) = (ASTDIO_WRITE, AMEMCPY, ASTDIO_WRITE, AEXIT)
  /\ stdio_call 259 srH knH = Some scOF /\ stdio_call 227 srG3 knG3 = Some scG3 /\ stdio_call 259 srH3 knH3 = Some scH3
  /\ stdio_call 195 srF4 knF4 = Some scF4 /\ stdio_call 259 srH4 knH4 = Some scH4.
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_open_defs ()) [] "p%0p%1p&0p;2p;3p;1p;<p;4g009Dj2uTg007Zj3LTg017ok10DTg0025j11Tg001Pj10Tg0058j1DTg000Pj16Tg002Zj1>Tg00Pjj12Tg0038j1@Tg00QIj3oTg006Zk10=Tg018Qj3KTg019Sj2dTg01:Uj3ETg00RIj2HTg01;Wk20BTg01<Yk20;Tg01=[k20:Tg01>]l<rTg01?aj2PTg0084j2[Tg008Ok207Tg0000k10@Tg01@Cj4ITg01@cj3tTg0048j3wTg007:j35Tg008ik40?Tg009dj3vTg01Afk104Tf0R0#0#1#1p=a%10#0#1#0p=_%10#0#0#0p=<%00#1#1#1p=S%10#1#1#0p=h%00#Dp=lg01BdR1P1f1R2P0CIp=c%00#1#0#0p=^%00#0#0#Dp=:f4R3P1f3R4P1f2R5P2CIP0CIp=jP5P1P2P0CIp>03%00#1#0#1p>0>%00#0#0#1p=Z%00#1#1#0p=B%10#1#0#1p=b%10#1p=R%10#1#1#1p=C%00#0#0#0p=7%00#0#1#0p=i%00#0p=8g00@]R6%@07w2p=Q%20#2p>05%20#2#2#2p=X%20#2#2p=q%20#2#2#2#2#2#2#2p=p%20#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2p=UAw620p=J%00#>p={%D0#@p=A%10#0#1#1p=O%10#1#0#0p==%00#0#D#@p=T%00#1p=N%10#0#0#1p=ng01CBR7%62;50p>02%65%62=570557p=F%62=57095759574p=mA5720957595749573p=W%64A57209575557p>011H45?E20p=sg01DB?w20p=g%10#1#1#1#1#1#1#1p=`%00#0#0p=?%00#0#0#0#0#0#0#0p=Vg01Dn?w20p=fg00U@R8,H0p=e%05#>,H4?E20p=;%10#0p>00%00#0#>,H2p=z%>0,H2p=~%15#0#0#0#>,H4?E20p=M1H45%D0#@7E2p=y%00#0#1#1p=Y%10#Dp>0C%@09E52p>0<%10#0#0p>09g00GWR9%D4,H3?E52;50p=9A5920959595949593p=3AE452=590p>0A%>4,H3?E52=590p=4f6f5;E3AE452=590559p=|A59209595p=kA5920p=xP3P420752P0H0?p=]g00CMR3Av5207v4$04p=GAv5209v34p>06P5P1P2&040CIp>08P2P1P0g01EZCIp=}AL452/[0p=\1u11R0/u1R5/u1R4P5P0g00AhR2#a#_#<#S#h#lR:/c:R;%^2#S#^#S#:P:DjR<;L<1u41S00P4P5B030;:%a2$0>#_#Z#B#lR;%a2#Z#b#B#_#lR=DjR>;L>S011c;;>030=R?=L5?S02P5P01c;:P;P=DjR==L4=S03g01F]R@$0DRA%12RB#0S04#0S05#0S06#0S07#1S08#R#CRC#aS09#0S0:#0#:RD%02RE#DRF%a2#B#B#7#i#lRGg00AIRH#6RI%0ERJ#1RK#0RL#1RM#0S0;#8RN#0S0<#>S0='QRO%2HRH#2RP$05RQ#XRR#qS0>#2S0?#2#pS0@#2#URS#US0A#2S0B#2S0C#2RT#2RU#2RV#2RW#2RX#2RY#q#X#p#U#U#U#URZ#6R[,JIR\%0JRJ#1R]#1R^#1R_#1R`#1Ra#{'QPO%1ERE#0Rb#0S0D#0Rc#0Rd#ARe%@8RfPf%1KRK#0Rg#0S0E#8S0F#{S0G,QIRh&05Z#X#U#U#URZ#2#XS0H#2S0I#2S0J#XS0K#2S0L#2S0M#2S0N#2S0O#2S0P#2S0Q#q#pS0R#2S0S#2S0T#2S0U#2Ri#2#XS0V#2S0W#2S0X#XS0Y#2S0Z#2S0[#2S0\#2S0]#2S0^#2S0_#q#pS0`#2S0a#2S0b#2S0c#2Rj%@GPh%6SS0d%O2#7#C#=#B#TS0e%2j#XRS%2SRS%2SRS%@DRk%A2RlAo6[fRm9o6fS0f%A]S0g5o6Rn5o6Pf%XSRS#6%2SRS%2SRS%2SRS%2SRS%2SRS%2SRS%12#N#=#S#h#O#:S0h#@S0iPl%O2#n#Z#=#=#TS0jPf%6TS0k%6US0l%6VS0m%6WS0n%6XS0o%6YS0p%qS#pRS%2SRS%2SRS%2S&0=7R7+023FCmDWDW3F3F3FDW3FCmH01S0qPf%1CS0r#0S0s#0RC#0RS#0#:PR%0JRY#0RX#0S0t#8RW#0RV#>,QIS0uCsRUPf%1S#:PRPOCsRSPf%RC#:PRPOCsRC%1BS0v#RRT#0S0w#D9K[8%6PRP/J[%>2'Q%ABRB'g%1TS0x#R#`RT#?#7#VS0y#AR8'J%>J#@Ro'fRp%7VRV#?S0z#0#V#V#VS0{#DRq%RVRV#1#C#`Rr#1#7#V#:Rs3KRt%ep%AJRJ'dRp1gPB/J8/foRu?KqsRv%eu/dJRu%0LRL#0Rw#8S0|#0Rx#>S0}#@Ry,J\/gB/J8/foRz?KqsR{%ez/dJRz%1a#>#@Ra,J\S0~/gB/J8/foR\?KqsRq%e\/dJR\1gOB/J8/foR|%0V#C#b#C#S#C#ORV#0#:%Sr#C#ORr#0#:R}3KR~%e|/dJR|1JIy/gB/J8/foRy%1V#:RV;K}R}%ey/dJRy1JIaS10/gB/J8/foRo%1r#:7KVRV%eo/dJRJPI%<cS11PRPfC;Rc&00d,zIS12%1W#RS13#1#nRo#0#ARr7ERS14%8dS15#0S16#0,~IS17?ERlS18%1KRK#1Rd$00,zIS19%1o#AS1:7ERS1;PI%?dS1<PRPkC;S1=PI%0KRKPRPfCMS1>PI%8KS1?#0S1@PRPrC;S1API%1gRgPRPlCMS1BPI%?gS1CPRPkC;S1DPIQ0EPR%N2#O#7#B#h#TCMS0EPI%1MRgPRQ1:CMS1EPI%?gS1FPRPkC;S1GPIQ0;PRPnCMS0;PIQ0<PRg01Ga%1TRT#R#C#`Rg#ARK;onS0<C;S1HPI%1LRL#1S1I#8PRPKC;S1JPI%?LRLPR%AMS1KC;S1LPI%<wS1M#>PR%a2#B#B#h#_#lS1N#@S1OCsS1PPtPvP{PqP~PI%8`PRPfC;R`PI%0^R^#8S1Q#0PRQ0fC;RwPI%?_PRP[C;R_PI%{xS1RPR%1YRx#1RM#1S1S#1#Z#<CyRdPIP^PRPfCMR^PtPvP{PqP~P}PVPI%1XS1T#?PRPPC;S1UPIQ0GPR%1bRo#0S0G#8S1V#>,QICsRBPIQ0}PHPXCyRXPI%>LPRQ04#1S04#=#=RL#1#N#S#7#B#C#i#7#S#^#B#C#B#hCyRaQ0=,HIS0=%8L#O#Z#n#7#Z#b#Y#^#O#B#Y#Z$0C80<RS0}PI%0]R]#1RLPR%1gS1W#RRg#8#=#=#=#=#=#=#b#ACMS1XPI%?LPR%1g#C#`Rg#0#`#`#AC;S1YPIQ1TPRQ05#1RL#1#Y#Y#Y#Y#Y#TCMS05PI%?MPR%<N#n#AC;S1TPI%0xRx#8S1Z#0PRQ0iC;S1[PIPxPRPfCMS1\PIQ1S#8PRPhC;S1SPI%0]R]PRQ0uCMS0uPI%8]R]#0PR%1oS1]#?S1^#>Ro,QIC;S1_PfQ09#1#7PRPfPfQ0:#<PRPfPfQ0r#1Rx#1S0r#NS0:#?PQ%1g#`#`#APf%0xRx#0#7PRPePfQ0s#1Rg#1#<PRPO1HfDRMPQ%AES0sQ15,~IPRPfPIQ0D#1S0D#?S15PRPfPIQ1V#0S1VPRPf1HIoPRPfQ1?,~IPRPfPIQ1FPR%1ERE#0S1F#0S1?#8S09#>Ro,QIS1`PIQ0FPR%6HS0FPIPNPRQ0C#6PIQ0|PRQ0B#6PIQ1QPRQ0A#6PIP]PRQ1`PIQ1ZPRPkPIPWPRQ13#N#C#ARWPIQ0w#8PR%02#_#^#7#B#T%DY-0BIQ0y#0#7#V#:Q0{#?#:RY5KI%1ERE#RRN#=,zI%0ERE#h#:+0;AKPsYQ0z#DQ1M#8#7#:+0:%?N#V#:Q08#0$00RN#V#:+0:1HIoPRPP1zIEPR%12#_#i#<#^#TPIQ07#8PRQ0>#6PI%?LRLPRQ0?#6PIQ04#7PRQ0@#6Q0h,HfPRQ0FQ0v#N#:-0;MP~P}Pf%1NRN#1RM#8#Z#:PR%B2#=#_#b#=CyPf%1MRM#<RE#7PR%@:Pf%<EPR%N2#b$0>#^#7#TPf%YM#7PR%N2#b#S#i#7#TPf%NN#=#7PR%N2#b#^#V#TPfQ06#C#B#C#<PRP8Pf%ZL#h#=RL#0PHPlPf%1LPHPlPf%n]R]#0#S#=PHPlPf%1]#i#YPHPlPf%0g#<PR%@;Pf%1x#<PQ%@FPfQ0:$09PQQ1W#ARxPfQ0r#1#7PQPxPf%?T#7Rx#a#<PRPfPf&09x#7PRPf&0=9D9D9D9D9D9D9D9D9D9D9D9D9D9D9D9D3H0AD4D4D4F|3kD3D4D4D4D4D4D4D4D4D4F|D4D4F|D9D9D9D9D9R9'xD3D3Rx'xD3D3D3D3RQ9k}VD3D3D3D3D3D3D3D3D3D3M<r,P@R;;L;RgPDPFQ1NPOQ0~POPePrPlQ1R,QIR]PiQ1OP]Q0dQ0eQ0VQ0WQ0XQ1KPKPlQ0Y#6Q0ZQ0[Q0\Q0]Q0^Q0_Q0<PnPkQ1:PlPrPfAo6mfR6PlPmQ0`Q0aQ0bQ0c00273FCmDWDW3F3F3FDW3FCmH01PUPSPCQ0x#DRn=K[nRnPtPpPvPuP{PzPqP\P~P|P}PyPVPJPcQ12?ERPRLQ17?ERfR8Q19?ERrRNP`PwP_PdP^PtPvP{PqP~Q1UPBPXPaQ0}Q1XQ1YQ05Q1TPIQ1F#<PRQ0FC;Q1[Q1\Q1SQ0uQ1_PIQ1?PRQ0pCMPIQ09#8PRQ0oPIQ1]#<PRQ0nPIQ1^#0PRQ0mPIQ0G#<PRQ0lPIQ1V#0PRQ0kPIQ0D#<PRQ0sPIQ15#0PRQ0jPIQ11PRPlPIQ16PRQ0iPIQ1<PRPWPIQ1@PRPkPIQ1CPR%N2#O#i#C#n#TP9D4D4D4D4D4D4D4D4D4D4D4D4D3D3D3D3R99k}VD3D3D3D3D3D3D3D3M<r,P@RR=LARRWPDPFPGPOPOPOPePfPfPhQ0qPUPSPCPnPtPpPvPuP{PzPqP\P~P|P}PyPVPJPcPLAk8NQD3D3D3D3D3M<r,P@RQ=LAQRnPDPF%a2#B#O#C#_#lR2POQ10POPePPP[P]PZ%@2P]Q0dQ0eQ0HQ0IQ0JQ1KPKP[Q0K#6Q0LQ0MQ0NQ0OQ0PQ0QPfQ0gPkPrPfPPPfP6Q0fPmQ0RQ0SQ0TQ0U00273FCmDWDW3F3F3FDW3FCmH01PUPSPCQ0t#D%DT5K[R[PcPLP8PNP`PwP_PdP^PtPpPvPuP{PzPqP\P~P|P}1xJ99kyVD3D3D3D3D3D3M<r,P@R9=LA9RNPDPFPGPOQ1I#R#>,QIPOPePfPfPhQ0qPUPSPCQ0=%Db80<HPcQ14Q18Q1;Q1=Q1>Q1AQ1BQ1DQ0EQ1EQ1GQ0;Q1HQ1JQ1LQ1PP[PtPpPvPuP{PzPqP\P~P|P}PyPVPJP`PwP_PdP^PtPpPvPuP{PzPqP\P~P|P}PyPVPJQ1U1xax9kBXD3D3D3D3D3D3D3D3D3D3D3D3D3D3M<r,P@RX=LAXRB'[Rx'[Ra'[RJ'[RV'[Ry'[R}'[P4P<Q01P}Q00P>Q02PyP5P?Q03PVP4P=PgPJPAP;PWPaPAPRPnPxPAPQPNPBPAP9207AXD]D]D]D]D]D]D]D]P4P5P0g00=[$0@RX1u3XR3g00DRR9g00EUCGPXP3P9g00JcCG'cPXP3P9g00MgCGPXP3P9g00U^CGDjP5P1P0P1P1P1g01HMRBPBCIRNg01IRCIPBCIQ00P4P5PXP3P9g00\8CGPXP3P9g00_=CG'cPXP3P9g00bDH066080PXP3P9g00eHCGPXP3P9g01J[CGDjP5P1P0P1PNPBCIg01K[RNCI,}4P5PXP3P9g00hLCGPXP3P9g00kSCG'cPXP3P9g01LeH066080P1P1PNPNCI,}0P4P5P0PXP3P9g00nZCGPXP3P9g011aCG'cPXP3P9g014hCGPXP3P9g01MfCGDjP0P1P1P1PNPBCIPNCI,}5PAg01Ngg01Oh5tjg01Pi,P@PAg01Qkg01Rm5tig01So,P@PAg01U1g01V35tjg01W5,P@PAg01X7g01Y95tZg01Z;,P@g01[=g01\?5tjg01]A,P@5LAC\C\C\C\C\C\C\C\do"). Qed.
