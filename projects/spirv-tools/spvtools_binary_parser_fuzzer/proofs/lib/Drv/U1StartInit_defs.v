(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec3 SymExec3Sound SymRun3.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import SymExecA Overlay.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_U1StartInit_defs () := "I47Corelib4Init9Datatypes4list00K47Corelib4Init9Datatypes4list01K47Corelib4Init5Logic2eq01I59OSSVerify5KrLib8SymExec33SX28sidecond00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv7Overlay<log_split_okC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1N01c59OSSVerify5KrLib3Drv@U1StartInit_defs3SLOC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv@U1StartInit_defs3SHIC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv@U1StartInit_defs4DLIMC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv@U1StartInit_defs8init_logC1?~~~~~~~~~~~~~~~".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations. Open Scope bv_scope. Import SX2. Import SXA.
Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition CXX_INIT : Z := 0x94e14.
Definition MAIN : Z := 0x6583c.

Definition spx (k : Z) : expr := EAlu ALU_ADD (EVar 0) (ELit k).

Definition sr8 : list expr :=
  [ELit 0; ELit 0xd1748; spx (-80); ELit 0x10800; ELit 0x102418; EVar 8; EVar 9; EVar 10; ELit 0xe8c70; ELit 0xe8c60; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; ELit 0x6583c; EVar 2; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; EVar 31; EVar 32; EVar 33; EVar 34].

Definition kn8 : list kentry :=
  [ KRange (EVar 0) 0x7fff80000000 0x800000000000;
    KAlign (EVar 0) 16;
    KWr (SA (EVar 0) (-8388608)) (ELit 8388608);
    KWord (SA (EVar 0) (-56)) 8 (ELit 0xd17f8);
    KWord (SA (EVar 0) (-64)) 8 (spx 8);
    KWord (SA (EVar 0) (-72)) 8 (EVar 1);
    KWr (SA (ELit 0) 0xef000) (ELit 0x35000);
    KImg 0x10000 0xef000;
    KImg 0xef000 0x102348;
    KImg 0x102374 0x102378;
    KImg 0x10237c 0x1023c8;
    KImg 0x1023d0 0x1023e8;
    KImg 0x1023f0 0x102408;
    KImg 0x102418 0x102428;
    KImg 0x102430 0x122440;
    KImg 0x122458 0x122688;
    KImg 0x122690 0x122698;
    KImg 0x1226a9 0x1226b0;
    KImg 0x1226b8 0x1226c0;
    KImg 0x1226d0 0x1226d8;
    KImg 0x1226e0 0x122710;
    KImg 0x122718 0x124000;
    KWord (SA (ELit 0) 0x1023e8) 8 (ELit 0x1226e0);
    KWord (SA (ELit 0) 0x122688) 8 (EVar 40) ].

Definition init_run :=
  Eval vm_compute in sym_execA SEGS 20000 true [MAIN] (SCR [] [] []) (SS CXX_INIT sr8 [] kn8 41) [].

Definition init_pc : Z := Eval vm_compute in s_pc (fst (fst init_run)).
Definition init_scs : list sidecond := Eval vm_compute in snd (fst init_run).
Definition init_sr : list expr := Eval vm_compute in s_regs (fst (fst init_run)).
Definition init_log : list sentry := Eval vm_compute in s_log (fst (fst init_run)).

Definition SLO : Z := -4096. Definition SHI : Z := 0. Definition DLIM : Z := 0x100000000.
Definition init_runs : list run := Eval vm_compute in abs_runs 0 SLO SHI DLIM init_log.

Lemma init_scs_nil : init_scs = [].
Proof.
ltac2:(KReplay.run1 (kr_t_U1StartInit_defs ()) [] "p;1p;2g0000j12Tg000Pj11Tg0010j20Tg001JR0#2%10'0o"). Qed.
Lemma init_split_ok : log_split_ok 0 SLO SHI DLIM init_log = true.
Proof.
ltac2:(KReplay.run1 (kr_t_U1StartInit_defs ()) [] "p;2p;5p;3g0010j22Tg002Fj51Tg003Cj30Tg003]R0g004=R1'2g004]g005;g0068g0075g0083D1=001do"). Qed.
