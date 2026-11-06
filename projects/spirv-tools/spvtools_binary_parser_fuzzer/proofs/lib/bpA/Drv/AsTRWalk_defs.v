(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HAmb HPropExec HSymExec2 HSymExec2Sound HSymRun HSymDrive HSymDriveX MainWalk_defs.
Import ListNotations.
Import HPropExec.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import SX2. Import SX2S.

Abbreviation RSEGS := Asan.M.loaded_segments.

Definition ATR_ENTRY : Z := 0xe8a7c.
Definition ATR_POSTINIT : Z := 0xe8ac4.
Definition ATR_JMALLOC : Z := 0xe8ad8.
Definition ATR_RET_MALLOC : Z := 0xe8ae0.
Definition ATR_RET_MEMCPY : Z := 0xe8af4.
Definition ATR_CALLHEAD : Z := 0xe8b34.
Definition ATR_RET_LLVM : Z := 0xe8b48.
Definition ATR_RET_EMIT : Z := 0xe8b58.
Definition ATR_RET_FREE : Z := 0xe8b74.
Definition ATR_MAINRET : Z := 0xe8920.
Definition AEF_GUARD_A : Z := 0xe8bd4.
Definition ATEXIT_CALL_A : Z := 0x163a80.

Definition AINIT : Z := 0x6c1d50.
Definition AAEF : Z := 0x6c1d54.
Definition AEMPTY : Z := 0x6c1d60.
Definition AX_FIN : Z := 0x6e3f68.
Definition AX_SLOT : Z := 0x6e3f70.
Definition AX_HEAD : Z := 0x6e3f78.
Definition AX_BUILTIN : Z := 0x6e3f80.
Definition AX_F3 : Z := 0x6e3fa0.
Definition AX_A3 : Z := 0x6e40a0.
Definition ANEEDLOCKS : Z := 0x6e41ab.
Definition MINUS2 : Z := 0xfffffffffffffffe.

Definition STOPST : list Z := [0xba4c0; 0xba4bc; 0xb8938; 0xe8c4c; 0xe8c04; ATR_MAINRET; ATR_POSTINIT; ATR_JMALLOC; ATR_CALLHEAD; ATR_RET_FREE]%Z.
Definition runT (stops : list Z) (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUELM true stops scr ss [].

Definition knT : list kentry :=
  [KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff7f811000 0x7fffffffff80;
   KWr (SA (EVar 0) (-128)) 128;
   KWr (SA (ELit 0) AINIT) 16;
   KImg 0x10000 0x91000; KImg 0x17c000 0x185000]%Z.

Definition atx_cells0 : list (Z * nat * Z) :=
  [(ANEEDLOCKS, 1%nat, 0); (AX_FIN, 1%nat, 0); (AX_FIN + 4, 4%nat, 0); (AX_SLOT, 4%nat, 3); (AX_HEAD, 8%nat, AX_BUILTIN)]%Z.

Definition atx_cells1 : list (Z * nat * Z) :=
  [(AX_SLOT, 4%nat, 4); (AX_F3, 8%nat, ATEXIT_CALL_A); (AX_A3, 8%nat, AEF_GUARD_A); (AINIT, 1%nat, 1)]%Z.
Definition kn_cells (cs : list (Z * nat * Z)) : list kentry :=
  map (fun c => match c with (a, w, v) => KWord (SA (ELit 0) a) w (ELit v) end) cs.

Definition knT0 : list kentry := Eval cbv in (knT ++ [KWr (SA (ELit 0) AX_FIN) 0x140]%Z ++ kn_cells atx_cells0).

Definition knT8 : list kentry :=
  [KWord (SA (EVar 0) (-8)) 8 (ELit ATR_MAINRET); KWord (SA (EVar 0) (-16)) 8 (EVar 1); KWord (SA (EVar 0) (-24)) 8 (EVar 2);
   KWord (SA (EVar 0) (-32)) 8 (EVar 3); KWord (SA (EVar 0) (-40)) 8 (EVar 4); KWord (SA (EVar 0) (-48)) 8 (EVar 5);
   KWord (SA (EVar 0) (-56)) 8 (EVar 6); KWord (SA (EVar 0) (-64)) 8 (EVar 8); KWord (SA (EVar 0) (-72)) 8 (EVar 9)]%Z ++ knT.

Definition srT00 : list expr :=
  [ELit 0; ELit ATR_MAINRET; EVar 0; EVar 17; ELit 0x6c3f18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 9; EVar 2; EVar 8; EVar 3; EVar 28; EVar 29; EVar 30; EVar 31; EVar 32; EVar 33; EVar 34; EVar 35; EVar 36; EVar 37; EVar 38; EVar 39; EVar 40; EVar 41; EVar 42; EVar 43; EVar 44; EVar 45]%Z.
Definition scrT0b : scripts := SCR [true] [EVar 5] [].
Definition rT0b := Eval vm_compute in runT STOPST scrT0b (SS ATR_ENTRY srT00 [] knT0 46).
Definition srT0b : list expr := Eval vm_compute in s_regs (fst (fst rT0b)).

Definition srT10 : list expr :=
  [ELit 0; EVar 15; spx (-80); EVar 17; ELit 0x6c3f18; EVar 19; EVar 20; EVar 21; EVar 3; EVar 8; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31; EVar 2; EVar 9; ELit AINIT; EVar 35; EVar 36; EVar 37; EVar 38; EVar 39; EVar 40; EVar 41; EVar 42; EVar 43; EVar 44; EVar 45]%Z.
Definition scrT1a : scripts := SCR [false; false] [EVar 6] [].
Definition scrT1b : scripts := SCR [false; true] [EVar 6] [].
Definition scrT1c : scripts := SCR [true; true] [] [].
Definition scrT1d : scripts := SCR [true; false] [] [].
Definition rT1a := Eval vm_compute in runT STOPST scrT1a (SS ATR_POSTINIT srT10 [] knT 46).
Definition rT1b := Eval vm_compute in runT STOPST scrT1b (SS ATR_POSTINIT srT10 [] knT 46).
Definition rT1c := Eval vm_compute in runT STOPST scrT1c (SS ATR_POSTINIT srT10 [] knT 46).
Definition rT1d := Eval vm_compute in runT STOPST scrT1d (SS ATR_POSTINIT srT10 [] knT 46).
Definition srT1a : list expr := Eval vm_compute in s_regs (fst (fst rT1a)).
Definition srT1b : list expr := Eval vm_compute in s_regs (fst (fst rT1b)).
Definition srT1c : list expr := Eval vm_compute in s_regs (fst (fst rT1c)).
Definition srT1d : list expr := Eval vm_compute in s_regs (fst (fst rT1d)).

Definition srT20 : list expr :=
  [ELit 0; EVar 15; spx (-80); EVar 17; ELit 0x6c3f18; EVar 19; EVar 20; EVar 21; EVar 3; EVar 8; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31; EVar 2; EVar 9; ELit AINIT; EVar 7; EVar 36; EVar 37; EVar 38; EVar 39; EVar 40; EVar 41; EVar 42; EVar 43; EVar 44; EVar 45]%Z.
Definition rT2 := Eval vm_compute in runT STOPST noscr (SS ATR_JMALLOC srT20 [] knT 46).
Definition srT2 : list expr := Eval vm_compute in s_regs (fst (fst rT2)).

Definition srT30 : list expr :=
  [ELit 0; EVar 15; spx (-80); EVar 17; ELit 0x6c3f18; EVar 19; EVar 20; EVar 21; EVar 3; EVar 8; EVar 4; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31; EVar 2; EVar 9; ELit AINIT; EVar 7; EVar 36; EVar 37; EVar 38; EVar 39; EVar 40; EVar 41; EVar 42; EVar 43; EVar 44; EVar 45]%Z.
Definition scrT3 : scripts := SCR [false] [] [].
Definition rT3 := Eval vm_compute in runT STOPST scrT3 (SS ATR_RET_MALLOC srT30 [] knT 46).
Definition srT3 : list expr := Eval vm_compute in s_regs (fst (fst rT3)).

Definition srT40 : list expr :=
  [ELit 0; EVar 15; spx (-80); EVar 17; ELit 0x6c3f18; EVar 19; EVar 20; EVar 21; EVar 3; EVar 8; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31; EVar 4; EVar 9; ELit AINIT; EVar 7; EVar 36; EVar 37; EVar 38; EVar 39; EVar 40; EVar 41; EVar 42; EVar 43; EVar 44; EVar 45]%Z.
Definition rT4 := Eval vm_compute in runT STOPST noscr (SS ATR_RET_MEMCPY srT40 [] knT 46).
Definition srT4 : list expr := Eval vm_compute in s_regs (fst (fst rT4)).

Definition srT50 : list expr :=
  [ELit 0; EVar 15; spx (-80); EVar 17; ELit 0x6c3f18; EVar 19; EVar 20; EVar 21; EVar 3; EVar 4; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31; EVar 10; EVar 11; ELit AINIT; EVar 7; ELit 0; ELit MINUS2; EVar 38; EVar 39; EVar 40; EVar 41; EVar 42; EVar 43; EVar 44; EVar 45]%Z.
Definition rT5 := Eval vm_compute in runT STOPST noscr (SS ATR_CALLHEAD srT50 [] knT 46).
Definition srT5 : list expr := Eval vm_compute in s_regs (fst (fst rT5)).

Definition srT60 : list expr :=
  [ELit 0; EVar 15; spx (-80); EVar 17; ELit 0x6c3f18; EVar 19; EVar 20; EVar 21; EVar 3; EVar 4; ELit 0; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31; EVar 10; EVar 33; ELit AINIT; EVar 7; ELit 0; ELit MINUS2; EVar 38; EVar 39; EVar 40; EVar 41; EVar 42; EVar 43; EVar 44; EVar 45]%Z.
Definition rT6 := Eval vm_compute in runT STOPST noscr (SS ATR_RET_LLVM srT60 [] knT 46).
Definition srT6 : list expr := Eval vm_compute in s_regs (fst (fst rT6)).

Definition srT70 : list expr :=
  [ELit 0; EVar 15; spx (-80); EVar 17; ELit 0x6c3f18; EVar 19; EVar 20; EVar 21; EVar 3; EVar 4; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31; EVar 10; ELit 0; ELit AINIT; EVar 7; ELit 0; ELit MINUS2; EVar 38; EVar 39; EVar 40; EVar 41; EVar 42; EVar 43; EVar 44; EVar 45]%Z.
Definition scrT7a : scripts := SCR [true] [] [].
Definition scrT7b : scripts := SCR [false] [] [].
Definition rT7a := Eval vm_compute in runT STOPST scrT7a (SS ATR_RET_EMIT srT70 [] knT 46).
Definition rT7b := Eval vm_compute in runT STOPST scrT7b (SS ATR_RET_EMIT srT70 [] knT 46).
Definition srT7a : list expr := Eval vm_compute in s_regs (fst (fst rT7a)).
Definition srT7b : list expr := Eval vm_compute in s_regs (fst (fst rT7b)).

Definition srT80 : list expr :=
  [ELit 0; EVar 15; spx (-80); EVar 17; ELit 0x6c3f18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31; EVar 10; EVar 11; ELit AINIT; EVar 35; ELit 0; ELit MINUS2; EVar 38; EVar 39; EVar 40; EVar 41; EVar 42; EVar 43; EVar 44; EVar 45]%Z.
Definition rT8 := Eval vm_compute in runT STOPST noscr (SS ATR_RET_FREE srT80 [] knT8 46).
Definition srT8 : list expr := Eval vm_compute in s_regs (fst (fst rT8)).

Definition summaryT (r : sym_state * list sidecond * scripts) := (s_pc (fst (fst r)), snd (fst r), snd r).
