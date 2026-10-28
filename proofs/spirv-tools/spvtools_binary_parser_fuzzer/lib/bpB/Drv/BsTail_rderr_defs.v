(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Bs0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPropExec BSymExec2 BSymExec2Sound BSymRun BSymDrive BSymDriveX BRefMemcpyLib BSymDriveH4 BSymAux.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BsShadow BsPrintfFirst BsSxKit BsStdioCall.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_BsTail_rderr_defs () := "I47Corelib4Init9Datatypes4list00K7ARocqVerifyHarness?AgentSubmission3bpB2HF9BSymExec23SX24expr02K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z03K7ARocqVerifyHarness?AgentSubmission3bpB2HF9BSymExec23SX24expr01K7ARocqVerifyHarness?AgentSubmission3bpB2HF9BSymExec23SX24expr03K47Corelib7Numbers7BinNums1Z02K7ARocqVerifyHarness?AgentSubmission3bpB2HF9BSymExec23SX28sidecond01K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init5Logic2eq00I47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic3and01I47Corelib4Init9Datatypes4prod00C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC7ARocqVerifyHarness?AgentSubmission3bpB2HF9BSymExec23SX25s_logC7ARocqVerifyHarness?AgentSubmission3bpB2HF9BSymExec23SX25carryC6ARocqVerifyHarness?AgentSubmission3bpB2HF7BSymAux;log_coveredI7ARocqVerifyHarness?AgentSubmission3bpB2HF9BSymExec23SX28sidecond00K47Corelib4Init9Datatypes4bool02K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05K4ELinuxProcessSemantics5Riscv5Instr5aluop06K4ELinuxProcessSemantics5Riscv5Instr5aluop01K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I7ARocqVerifyHarness?AgentSubmission3bpB2HF9BSymExec23SX29sym_state00I7ARocqVerifyHarness?AgentSubmission3bpB2HF9BSymExec23SX27scripts00c6ARocqVerifyHarness?AgentSubmission3bpB3DrvABsTail_rderr_defs2rBc6ARocqVerifyHarness?AgentSubmission3bpB3DrvABsTail_rderr_defs4scsBI7ARocqVerifyHarness?AgentSubmission3bpB2HF9BSymExec23SX26kentry00c6ARocqVerifyHarness?AgentSubmission3bpB3DrvABsTail_rderr_defs4knV0c6ARocqVerifyHarness?AgentSubmission3bpB3DrvABsTail_rderr_defs:ot_regionsc6ARocqVerifyHarness?AgentSubmission3bpB3DrvABsTail_rderr_defs2rCc6ARocqVerifyHarness?AgentSubmission3bpB3DrvABsTail_rderr_defs4scsCc6ARocqVerifyHarness?AgentSubmission3bpB3DrvABsTail_rderr_defs4knC0c6ARocqVerifyHarness?AgentSubmission3bpB3DrvABsTail_rderr_defs2rDc6ARocqVerifyHarness?AgentSubmission3bpB3DrvABsTail_rderr_defs4scsDc6ARocqVerifyHarness?AgentSubmission3bpB3DrvABsTail_rderr_defs3knCK47Corelib4Init9Datatypes3nat02K7ARocqVerifyHarness?AgentSubmission3bpB2HF9BSymExec23SX24expr04K7ARocqVerifyHarness?AgentSubmission3bpB2HF9BSymExec23SX25saddr01K7ARocqVerifyHarness?AgentSubmission3bpB2HF9BSymExec23SX28sidecond06K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03K47Corelib7Numbers7BinNums1Z01c6ARocqVerifyHarness?AgentSubmission3bpB3DrvABsTail_rderr_defs2rEc6ARocqVerifyHarness?AgentSubmission3bpB3DrvABsTail_rderr_defs4scsEc6ARocqVerifyHarness?AgentSubmission3bpB3DrvABsTail_rderr_defs4knE0K7ARocqVerifyHarness?AgentSubmission3bpB2HF9BSymExec23SX24expr07K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond04c6ARocqVerifyHarness?AgentSubmission3bpB3DrvABsTail_rderr_defs2rFc6ARocqVerifyHarness?AgentSubmission3bpB3DrvABsTail_rderr_defs4scsFc6ARocqVerifyHarness?AgentSubmission3bpB3DrvABsTail_rderr_defs5knF0_c6ARocqVerifyHarness?AgentSubmission3bpB3DrvABsTail_rderr_defs3rF0c6ARocqVerifyHarness?AgentSubmission3bpB3DrvABsTail_rderr_defs5scsF0c6ARocqVerifyHarness?AgentSubmission3bpB3DrvABsTail_rderr_defs5knF00c6ARocqVerifyHarness?AgentSubmission3bpB3DrvABsTail_rderr_defs2rGc6ARocqVerifyHarness?AgentSubmission3bpB3DrvABsTail_rderr_defs4scsGc6ARocqVerifyHarness?AgentSubmission3bpB3DrvABsTail_rderr_defs4knG0c6ARocqVerifyHarness?AgentSubmission3bpB3DrvABsTail_rderr_defs2rHc6ARocqVerifyHarness?AgentSubmission3bpB3DrvABsTail_rderr_defs4scsHc6ARocqVerifyHarness?AgentSubmission3bpB3DrvABsTail_rderr_defs4knH0c6ARocqVerifyHarness?AgentSubmission3bpB3DrvABsTail_rderr_defs3rG3c6ARocqVerifyHarness?AgentSubmission3bpB3DrvABsTail_rderr_defs5scsG3c6ARocqVerifyHarness?AgentSubmission3bpB3DrvABsTail_rderr_defs5knG30c6ARocqVerifyHarness?AgentSubmission3bpB3DrvABsTail_rderr_defs3rH3c6ARocqVerifyHarness?AgentSubmission3bpB3DrvABsTail_rderr_defs5scsH3c6ARocqVerifyHarness?AgentSubmission3bpB3DrvABsTail_rderr_defs5knH30c6ARocqVerifyHarness?AgentSubmission3bpB3DrvABsTail_rderr_defs3rF4c6ARocqVerifyHarness?AgentSubmission3bpB3DrvABsTail_rderr_defs5scsF4c6ARocqVerifyHarness?AgentSubmission3bpB3DrvABsTail_rderr_defs5knF40c6ARocqVerifyHarness?AgentSubmission3bpB3DrvABsTail_rderr_defs3rG4c6ARocqVerifyHarness?AgentSubmission3bpB3DrvABsTail_rderr_defs5scsG4c6ARocqVerifyHarness?AgentSubmission3bpB3DrvABsTail_rderr_defs5knG40c6ARocqVerifyHarness?AgentSubmission3bpB3DrvABsTail_rderr_defs3rH4c6ARocqVerifyHarness?AgentSubmission3bpB3DrvABsTail_rderr_defs5scsH4c6ARocqVerifyHarness?AgentSubmission3bpB3DrvABsTail_rderr_defs5knH40I47Corelib4Init9Datatypes6option00K7ARocqVerifyHarness?AgentSubmission3bpB2HF9BSymExec23SX26kentry06K7ARocqVerifyHarness?AgentSubmission3bpB2HF9BSymExec23SX26kentry02K7ARocqVerifyHarness?AgentSubmission3bpB2HF9BSymExec23SX26kentry01K7ARocqVerifyHarness?AgentSubmission3bpB2HF9BSymExec23SX26kentry05K7ARocqVerifyHarness?AgentSubmission3bpB2HF9BSymExec23SX26kentry07K7ARocqVerifyHarness?AgentSubmission3bpB2HF9BSymExec23SX26kentry04K6ARocqVerifyHarness?AgentSubmission3bpB3Drv;BsStdioCall9stdio_res01K47Corelib4Init9Datatypes6option01K47Corelib4Init9Datatypes4prod01C6ARocqVerifyHarness?AgentSubmission3bpB3Drv;BsStdioCall:stdio_callC7ARocqVerifyHarness?AgentSubmission3bpB2HF9BSymExec23SX24s_pcI47Corelib7Numbers7BinNums1Z00I7ARocqVerifyHarness?AgentSubmission3bpB2HF9BSymExec23SX24expr00K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5aluop0:c6ARocqVerifyHarness?AgentSubmission3bpB3DrvABsTail_rderr_defs5AEXITI6ARocqVerifyHarness?AgentSubmission3bpB3Drv;BsStdioCall9stdio_res00K4ELinuxProcessSemantics5Riscv5Instr5aluop02c6ARocqVerifyHarness?AgentSubmission3bpB3DrvABsTail_rderr_defs7AMEMCPYc6ARocqVerifyHarness?AgentSubmission3bpB3DrvABsTail_rderr_defs;ASTRNLEN_TRc6ARocqVerifyHarness?AgentSubmission3bpB3DrvABsTail_rderr_defs2rIc6ARocqVerifyHarness?AgentSubmission3bpB3DrvABsTail_rderr_defs<ASTDIO_WRITEc6ARocqVerifyHarness?AgentSubmission3bpB3DrvABsTail_rderr_defs3rI3c6ARocqVerifyHarness?AgentSubmission3bpB3DrvABsTail_rderr_defs3rI4c6ARocqVerifyHarness?AgentSubmission3bpB3DrvABsTail_rderr_defs3srHc6ARocqVerifyHarness?AgentSubmission3bpB3DrvABsTail_rderr_defs3knHc6ARocqVerifyHarness?AgentSubmission3bpB3DrvABsTail_rderr_defs4scOFc6ARocqVerifyHarness?AgentSubmission3bpB3DrvABsTail_rderr_defs4srG3c6ARocqVerifyHarness?AgentSubmission3bpB3DrvABsTail_rderr_defs4knG3c6ARocqVerifyHarness?AgentSubmission3bpB3DrvABsTail_rderr_defs4scG3c6ARocqVerifyHarness?AgentSubmission3bpB3DrvABsTail_rderr_defs4srH3c6ARocqVerifyHarness?AgentSubmission3bpB3DrvABsTail_rderr_defs4knH3c6ARocqVerifyHarness?AgentSubmission3bpB3DrvABsTail_rderr_defs4scH3c6ARocqVerifyHarness?AgentSubmission3bpB3DrvABsTail_rderr_defs4srF4c6ARocqVerifyHarness?AgentSubmission3bpB3DrvABsTail_rderr_defs4knF4c6ARocqVerifyHarness?AgentSubmission3bpB3DrvABsTail_rderr_defs4scF4c6ARocqVerifyHarness?AgentSubmission3bpB3DrvABsTail_rderr_defs4srH4c6ARocqVerifyHarness?AgentSubmission3bpB3DrvABsTail_rderr_defs4knH4c6ARocqVerifyHarness?AgentSubmission3bpB3DrvABsTail_rderr_defs4scH4".
Import ListNotations.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import SX2. Import SX2S.
Open Scope Z_scope.

Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

Definition AMEMCPY : Z := 0x176aa0.
Definition AMEMCPY_RET : Z := 0xb9880.
Definition ASTRNLEN_TR : Z := 0xa3680.
Definition ASTRNLEN_RET : Z := 0xa3ae4.
Definition ASTDIO_WRITE : Z := 0x16cdd0.
Definition AEXIT : Z := 0x165478.
Definition AMAINEPI : Z := 0xe85f0.
Definition ARIP : Z := 0xbbdb0.
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
Definition FMT : Z := 0x1fb71.
Definition NPRE : Z := 19.
Definition NSUF : Z := 1.
Definition IHI : Z := 0x80000000.
Definition BUF_LO : Z := (-592).
Definition BUF_HI : Z := (-512).
Definition PX : expr := EVar 141.

Definition srV0 : list expr :=
  map (fun i => match i with
    | 0 => ELit 0 | 1 => ELit 0xa8c60 | 2 => spx (-240) | 4 => ELit 0x6c5858
    | 8 => ELit FMT | 9 => ELit 0x189920 | 10 => ELit 0x189920 | 11 => ELit FMT | 12 => spx (-176) | 18 => spx (-176)
    | _ => EVar (35 + i) end)%nat (seq 0 32).

Definition ot_cells : list (Z * nat * Z) :=
  [(0x186fc8, 8%nat, 0x16e480); (0x187140, 8%nat, 0x176aa0); (0x187148, 8%nat, 0x176ea4); (0x1870f0, 8%nat, 0x177624); (0x186f80, 8%nat, 0x1769a4);
   (0x191038, 8%nat, 0x7fff8000); (0x191d18, 1%nat, 0x1); (0x191d19, 1%nat, 0x1); (0x222bbc, 1%nat, 0x1); (0x222c63, 1%nat, 0x1);
   (0x189920, 4%nat, 0x5); (0x189940, 8%nat, 0x0); (0x189948, 8%nat, 0x0); (0x189958, 8%nat, 0x0); (0x189968, 8%nat, 0x16cdd0);
   (0x189978, 8%nat, 0x6e6070); (0x189980, 8%nat, 0x0); (0x189998, 4%nat, 0x2); (0x1899a8, 4%nat, 0x0); (0x1899ac, 4%nat, 0xffffffff); (0x1899b0, 4%nat, 0xffffffff);
   (0x7fffbf68, 8%nat, 0x0); (0x7fffbf70, 8%nat, 0x0)].

Definition OT_SHOFFS : list Z := [(-592); (-574)].
Definition OT_SHOFFS2 : list Z := [(-592); (-574); (-573)].
Definition OT_SHX : list expr := [(EAlu ALU_AND (EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EAlu ALU_ADD (EVar 2) (EVar 141)) (ELit (-1))) (ELit 3)) (ELit 2147450880)) (ELit (-8))); (EAlu ALU_AND (EAlu ALU_ADD (EAlu ALU_SRL (EVar 2) (ELit 3)) (ELit 2147450880)) (ELit (-8))); (EAlu ALU_AND (EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) (EVar 141)) (ELit (-574))) (ELit 3)) (ELit 2147450880)) (ELit (-8))); (EAlu ALU_AND (EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) (EVar 141)) (ELit (-573))) (ELit 3)) (ELit 2147450880)) (ELit (-8)))].
Fixpoint shxkn (l : list expr) : list kentry :=
  match l with [] => [] | e :: r => KRange e 0x20000000000 0x10007fff8000 :: KZero (SA e 0) (ELit 8) :: shxkn r end.

Definition knV0 : list kentry :=
  [KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000; KWr (SA (EVar 0) (-128 - OT_FR)) OT_FR;
   KRange (EVar 2) AHI_LO AAPP_HI;
   KImg 0x10000 0x91000; KImg 0x17e000 0x186000;
   KWord (SA (EVar 0) (-176)) 8 (EVar 2); KWord (SA (EVar 0) (-184)) 8 (ELit 0xe8658);
   KWord (SA (EVar 0) (-192)) 8 (EVar 11); KWord (SA (EVar 0) (-200)) 8 (EVar 12); KWord (SA (EVar 0) (-208)) 8 (EVar 21);
   KWord (SA (ELit 0) 0x6e5898) 8 (EVar 1); KWr (SA (ELit 0) 0x189920) 232]
  ++ shkn OT_SHOFFS
  ++ kn_cells ot_cells.

Definition not_px_range (k : kentry) : bool := match k with KRange (EVar 141) _ _ => false | _ => true end.
Definition px_range (lo hi : Z) (kn : list kentry) : list kentry := KRange PX lo hi :: List.filter not_px_range kn.

Definition kn_readd (plo phi : Z) (kn : list kentry) : list kentry := px_range plo phi (shxkn OT_SHX ++ shkn OT_SHOFFS2 ++ kn).

Definition ssB0 : sym_state := SS 0x16e480 srV0 [] knV0 67.
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

Definition ssI0 : sym_state := SS 0x16e5a8 srI0 [] knI0 291.
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

Definition ssI30 : sym_state := SS 0x16e5a8 srI30 [] knI30 291.
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

Definition ssI40 : sym_state := SS 0x16e5a8 srI40 [] knI40 291.
Definition rI4 := Eval vm_compute in runT (SCR [] [] []) ssI40.
Definition srI4 : list expr := Eval vm_compute in s_regs (fst (fst rI4)).
Definition knI4 : list kentry := Eval vm_compute in kn_afterT rI4 knI40.

Definition ot_regions : list sregion := [(SA (EVar 0) (-128 - OT_FR), OT_FR); (SA (ELit 0) 0x189920, 232)].
Definition scsB : list sidecond := Eval vm_compute in (snd (fst rB)).
Lemma factsB : snd (fst rB) = scsB /\ snd (fst (carry (s_log (fst (fst rB))) knV0 [])) = [] /\ log_covered ot_regions (s_log (fst (fst rB))) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_BsTail_rderr_defs ()) [] "p;1p;3p;4p;2g0000j13Tg000Pj1DTg001Pj10Tg0025j15Tg002Zj1=Tg0038j16Tg0048j3:Tg0058j1@Tg005Vj4?Tg006Zj19Tg007:j3>Tg007Zj31Tg0084j24Tg008Oj27Tg008ij4<Tg009Dj28Tg009dj32Tg00:Aj3;Tg00:^j1CTg00;]j3BTg00<\j2ATg00=[R0#3R1g00>_g00??g00@1g00@]g00AI#Dg00AhR2#0#0#5R3#0#5#0#0#0#0#=#63:%=2#63:%53#@#6C?%90R35>0R0;10A1133R2g00BMR4g00BmR5;15R6'41710P2P617131745C<C<g00CMR61861g00DRg00EU32R27;1g00FV511g00GY#3R01801%34A2612#CR2g00H[%943B327;1=113g00I^/A2=145'4'4do"). Qed.
Definition scsC : list sidecond := Eval vm_compute in (snd (fst rC)).
Lemma factsC : snd (fst rC) = scsC /\ snd (fst (carry (s_log (fst (fst rC))) knC0 [])) = [] /\ log_covered ot_regions (s_log (fst (fst rC))) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_BsTail_rderr_defs ()) [] "p;1p;3p;2p;4g0000j13Tg006Zj18Tg007Zj30Tg0084j21Tg008Oj27Tg008ij46Tg009Dj25Tg009dj32Tg00:Aj34Tg00:^j1;Tg00;]j3:Tg00<\j29Tg00=[R0#3R1%80R0;00R2g00BMR3g00BmR4;04R5,121710R6P2P5P61734C6C6g00CMR61561g00DRg00Jg32R5741g00Kh501g00GY#3R21521%33A2615#;R5g00Lk%833:32741=010g00I^/95=034'1'1do"). Qed.
Definition scsD : list sidecond := Eval vm_compute in (snd (fst rD)).
Lemma factsD : snd (fst rD) = scsD /\ snd (fst (carry (s_log (fst (fst rD))) knC [])) = [] /\ log_covered ot_regions (s_log (fst (fst rD))) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_BsTail_rderr_defs ()) [] "p;1p;3p;2p;4g0000j13Tg006Zj18Tg007Zj30Tg0084j21Tg008Oj27Tg008ij46Tg009Dj25Tg009dj32Tg00:Aj34Tg00:^j1;Tg00;]j3:Tg00<\j29Tg00=[R0#3R1%80R0;00R2g00BMR3g00BmR4;04R5,121710R6P2P5P61734C6C6g00CMR61561g00DRg00Mn32R5741g00No501g00GY#3R21521%33A2615#;R5g00P2%833:32741=010g00I^/95=034'1'1do"). Qed.
Definition scsE : list sidecond := Eval vm_compute in (snd (fst rE)).
Lemma factsE : snd (fst rE) = scsE /\ snd (fst (carry (s_log (fst (fst rE))) knE0 [])) = [] /\ log_covered ot_regions (s_log (fst (fst rE))) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_BsTail_rderr_defs ()) [] "p;1p;3p;4p;2g0000j14Tg00Q4j10Tg000Pj1;Tg0038j1GTg00QSj3BTg005Vj4ATg0048j3@Tg00RSj2>Tg00STj4=Tg006Zj17Tg007:j3<Tg007Zj32Tg0084j26Tg008Oj25Tg008ij48Tg009Dj29Tg009dj33Tg00:Aj3:Tg00:^j1FTg00;]j3DTg00<\j2ETf0R0#0#0p=C%00#0#0#0#0#0#0#0p=?%00#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=1g00=[R0#4R1g00>_R2g00TXg00@]R3g00AI#0R4#0R5#0#C#?#1#1#1#1#1#1#1#1#;R6g00UJR7#GR83BP6CA%;5=@36/>7P4P2P8C=%70R85<05<0R0;20A2188R2g00BMR4g00BmR7;27R6'61510P2P615181547C8C8g00CMR61961g00DRg00Uh33R27:1g00Vi521g00GY#4R01901%44A3612#FR2g00Wl%743D337:1=218g00I^/E2=247'6'6do"). Qed.
Definition scsF : list sidecond := Eval vm_compute in (snd (fst rF)).
Lemma factsF : snd (fst rF) = scsF /\ snd (fst (carry (s_log (fst (fst rF))) knF0_ [])) = [] /\ log_covered ot_regions (s_log (fst (fst rF))) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_BsTail_rderr_defs ()) [] "p;1p;3p;4p;2g0000j18Tg000Pj1=Tg001Pj17Tg0025j15Tg002Zj1DTg0038j1:Tg0048j36Tg00Q4j10Tg005Vj44Tg00Xoj4ETg00QSj3CTg006Zj1BTg007:j33Tg007Zj32Tg0084j2;Tg008Oj29Tg008ij4@Tg009Dj2ATg009dj3<Tg00:Aj3?Tg00:^j1ITg00;]j3HTg00<\j2GTf0R0#0#0p=>%00#0#0#0#0#0#0#0p=F%00#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=1g00=[R0#8R1g00>_R2g00??R3g00@1R4g00@]R5g00AIR6#=R7g00AhR8#7#7#7#5#5#5#5#7#5#D#:R936R:%D8#:R836%>6R;#>R<#0#F#1#1#1#1#1#1#1#1#=R=C4P2P3%=;R;=648P=C4g00BmR8g00YoP;A657==659C4P2g00ZaP:P;C4P8g00[SP8P6P<P=CEg00UJ#:R<9C5==C5<C4%B0R<530530530530530R0;20A21<<R5g00BMR=?288R6';1910P5P6191<19=8C@C@g00CMR61A61g00DRg00\E3<R57?1g00]F521g00GY#8R01A01%8=A<615#IR5g00^I%B=3H3<7?1=21<g00I^/G5=2=8';';do"). Qed.
Definition scsF0 : list sidecond := Eval vm_compute in (snd (fst rF0)).
Lemma factsF0 : snd (fst rF0) = scsF0 /\ snd (fst (carry (s_log (fst (fst rF0))) knF00 [])) = [] /\ log_covered ot_regions (s_log (fst (fst rF0))) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_BsTail_rderr_defs ()) [] "p;1p;3p;4p;2g0000j17Tg000Pj1:Tg00Q4j10Tg0048j36Tg001Pj14Tg0025j13Tg002Zj1CTg0038j1BTg005Vj4<Tg006Zj1;Tg007:j3@Tg007Zj32Tg0084j28Tg008Oj29Tg008ij4>Tg009Dj2?Tg009dj35Tg00:Aj3=Tg00:^j1FTg00;]j3ETg00<\j2DTf0R0#0#0p=A%00#0#0#0#0#0#0#0p=G%00#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=1g00=[R0#7R1g00BmR2g00Yog00AIR3#AR4#:R5g00@]R6%:3R3%04#A#G#1#1#1#1#1#1#1#1#:566g00Ah#4#4#4#3#3#3#3#4#3#C#BR436C<g00>_g00ZaA6634P5C<%;0R55@05@0R0;20A2155R4g00BMR3?222R6'81910P4P619151932C>C>g00CMR61?61g00DRg00_M35R47=1g00`O521g00GY#7R01?01%73A5614#FR4g00aS%;33E357=1=215g00I^/D4=232'8'8do"). Qed.
Definition scsG : list sidecond := Eval vm_compute in (snd (fst rG)).
Lemma factsG : snd (fst rG) = scsG /\ snd (fst (carry (s_log (fst (fst rG))) knG0 [])) = [] /\ log_covered ot_regions (s_log (fst (fst rG))) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_BsTail_rderr_defs ()) [] "p;1p;3p;4p;2g0000j1:Tg000Pj1?Tg00Q4j10Tg0048j36Tg001Pj14Tg0025j13Tg002Zj1<Tg0038j15Tg0058j1BTg005Vj4ATg006Zj1@Tg007:j3GTg007Zj32Tg0084j27Tg008Oj29Tg008ij4>Tg009Dj2=Tg009dj38Tg00:Aj3;Tg00:^j1ETg00;]j3DTg00<\j2FTf0R0#0#0#0#0p=C%00#0#0#0#0#0#0#0p=H%00#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=1g00=[R0#:R1g00>_g00??g00@1g00@]R2g00AIR3#?%03#C#H#1#1#1#1#1#1#1#1#?562g00AhR2#4#4#4#3#3#3#3#4#3#<#536%<2#536%B2#5CA%@0R25G0R0;20A2122R3g00BMR4g00BmR5;25R6'71910P3P619121945C>C>g00CMR61=61g00DRg00bW38R37;1g00cX521g00GY#:R01=01%:4A8613#ER3g00d[%@43D387;1=212g00I^/F3=245'7'7do"). Qed.
Definition scsH : list sidecond := Eval vm_compute in (snd (fst rH)).
Lemma factsH : snd (fst rH) = scsH /\ snd (fst (carry (s_log (fst (fst rH))) knH0 [])) = [] /\ log_covered ot_regions (s_log (fst (fst rH))) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_BsTail_rderr_defs ()) [] "p;1p;3p;2p;4g0000j13Tg006Zj18Tg007Zj30Tg0084j21Tg008Oj27Tg008ij46Tg009Dj25Tg009dj32Tg00:Aj34Tg00:^j1;Tg00;]j3:Tg00<\j29Tg00=[R0#3R1%80R0;00R2g00BMR3g00BmR4;04R5,121710R6P2P5P61734C6C6g00CMR61561g00DRg00e^32R5741g00f_501g00GY#3R21521%33A2615#;R5g00gb%833:32741=010g00I^/95=034'1'1do"). Qed.
Definition scsI : list sidecond := Eval vm_compute in (snd (fst rI)).

Definition scsG3 : list sidecond := Eval vm_compute in (snd (fst rG3)).
Lemma factsG3 : snd (fst rG3) = scsG3 /\ snd (fst (carry (s_log (fst (fst rG3))) knG30 [])) = [] /\ log_covered ot_regions (s_log (fst (fst rG3))) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_BsTail_rderr_defs ()) [] "p;1p;3p;2p;4g0000j13Tg006Zj18Tg007Zj30Tg0084j21Tg008Oj27Tg008ij46Tg009Dj25Tg009dj32Tg00:Aj34Tg00:^j1;Tg00;]j3:Tg00<\j29Tg00=[R0#3R1%80R0;00R2g00BMR3g00BmR4;04R5,121710R6P2P5P61734C6C6g00CMR61561g00DRg00he32R5741g00ig501g00GY#3R21521%33A2615#;R5g00jk%833:32741=010g00I^/95=034'1'1do"). Qed.
Definition scsH3 : list sidecond := Eval vm_compute in (snd (fst rH3)).
Lemma factsH3 : snd (fst rH3) = scsH3 /\ snd (fst (carry (s_log (fst (fst rH3))) knH30 [])) = [] /\ log_covered ot_regions (s_log (fst (fst rH3))) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_BsTail_rderr_defs ()) [] "p;1p;3p;2p;4g0000j13Tg006Zj18Tg007Zj30Tg0084j21Tg008Oj27Tg008ij46Tg009Dj25Tg009dj32Tg00:Aj34Tg00:^j1;Tg00;]j3:Tg00<\j29Tg00=[R0#3R1%80R0;00R2g00BMR3g00BmR4;04R5,121710R6P2P5P61734C6C6g00CMR61561g00DRg00ko32R5741g00m1501g00GY#3R21521%33A2615#;R5g00n5%833:32741=010g00I^/95=034'1'1do"). Qed.
Definition scsI3 : list sidecond := Eval vm_compute in (snd (fst rI3)).

Definition scsF4 : list sidecond := Eval vm_compute in (snd (fst rF4)).
Lemma factsF4 : snd (fst rF4) = scsF4 /\ snd (fst (carry (s_log (fst (fst rF4))) knF40 [])) = [] /\ log_covered ot_regions (s_log (fst (fst rF4))) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_BsTail_rderr_defs ()) [] "p;1p;4p;3p;2g0000j13Tg00Q4j10Tg000Pj1DTg00Xoj4CTg0038j1?Tg00QSj38Tg005Vj4>Tg006Zj17Tg007:j3<Tg007Zj32Tg0084j26Tg008Oj24Tg008ij4;Tg009Dj2:Tg009dj35Tg00:Aj39Tg00:^j1BTg00;]j3@Tg00<\j2ATf0R0#0#0#0#0p=E%00#0#0#0#0#0#0#0p==%00#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=1g00=[R0#3R1g00BmR2g00[SP2g00AIR3%E3R3%03#=#1#1#1#1#1#1#1#1#DR3CCg00@]R4g00UJ#?R59843;85C>%70R55<0R0;20A2155R4g00BMR3?222R6'61410P4P614151432C;C;g00CMR61:61g00DRg00o935R4791g010;521g00GY#3R01:01%33A5614#BR4g011?%733@35791=215g00I^/A4=232'6'6do"). Qed.
Definition scsG4 : list sidecond := Eval vm_compute in (snd (fst rG4)).
Lemma factsG4 : snd (fst rG4) = scsG4 /\ snd (fst (carry (s_log (fst (fst rG4))) knG40 [])) = [] /\ log_covered ot_regions (s_log (fst (fst rG4))) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_BsTail_rderr_defs ()) [] "p;1p;3p;4p;2g0000j13Tg000Pj1DTg001Pj10Tg0025j17Tg002Zj1=Tg0038j15Tg0048j3:Tg0058j1@Tg005Vj4?Tg006Zj19Tg007:j3>Tg007Zj31Tg0084j24Tg008Oj26Tg008ij4<Tg009Dj28Tg009dj32Tg00:Aj3;Tg00:^j1CTg00;]j3BTg00<\j2ATg00=[R0#3R1g00>_g00??g00@1g00@]g00AI#Dg00AhR2#0#0#7#0#7#0#0#0#0#=#53:%=2#53:%@2#5C?%90R25>0R0;10A1122R3g00BMR4g00BmR5;15R6'41610P3P616121645C<C<g00CMR61861g00DRg012C32R37;1g013E511g00GY#3R01801%34A2613#CR3g014I%943B327;1=112g00I^/A3=145'4'4do"). Qed.
Definition scsH4 : list sidecond := Eval vm_compute in (snd (fst rH4)).
Lemma factsH4 : snd (fst rH4) = scsH4 /\ snd (fst (carry (s_log (fst (fst rH4))) knH40 [])) = [] /\ log_covered ot_regions (s_log (fst (fst rH4))) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_BsTail_rderr_defs ()) [] "p;1p;3p;2p;4g0000j13Tg006Zj18Tg007Zj30Tg0084j21Tg008Oj27Tg008ij46Tg009Dj25Tg009dj32Tg00:Aj34Tg00:^j1;Tg00;]j3:Tg00<\j29Tg00=[R0#3R1%80R0;00R2g00BMR3g00BmR4;04R5,121710R6P2P5P61734C6C6g00CMR61561g00DRg015M32R5741g016O501g00GY#3R21521%33A2615#;R5g017S%833:32741=010g00I^/95=034'1'1do"). Qed.
Definition scsI4 : list sidecond := Eval vm_compute in (snd (fst rI4)).

Lemma ot_itinerary :
  (s_pc (fst (fst rB)), s_pc (fst (fst rC)), s_pc (fst (fst rD)), s_pc (fst (fst rE))) = (AMEMCPY, AMEMCPY, ASTRNLEN_TR, AMEMCPY)
  /\ (s_pc (fst (fst rF)), s_pc (fst (fst rF0)), s_pc (fst (fst rG)), s_pc (fst (fst rH)), s_pc (fst (fst rI))) = (AMEMCPY, AMEMCPY, AMEMCPY, ASTDIO_WRITE, AEXIT)
  /\ (s_pc (fst (fst rG3)), s_pc (fst (fst rH3)), s_pc (fst (fst rI3))) = (ASTDIO_WRITE, ASTDIO_WRITE, AEXIT)
  /\ (s_pc (fst (fst rF4)), s_pc (fst (fst rG4)), s_pc (fst (fst rH4)), s_pc (fst (fst rI4))) = (ASTDIO_WRITE, AMEMCPY, ASTDIO_WRITE, AEXIT)
  /\ stdio_call 259 srH knH = Some scOF /\ stdio_call 227 srG3 knG3 = Some scG3 /\ stdio_call 259 srH3 knH3 = Some scH3
  /\ stdio_call 195 srF4 knF4 = Some scF4 /\ stdio_call 259 srH4 knH4 = Some scH4.
Proof.
vm_compute. repeat split; reflexivity. Qed.
