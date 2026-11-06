(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import AxSymExec3 AsanPlanCore.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegTmpl SegGhost SegProg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2.
Open Scope Z_scope.

Definition MBV (n : nat) : expr := EVar n.
Definition MB_dst : expr := EAlu ALU_ADD (MBV 16) (ELit (-400)).
Definition MB_SHOFF : Z := 0x7fff8000.
Definition MCB_pre_regs : list expr :=
  [ELit 0; MBV 0; MBV 1; MBV 2; MBV 3; MBV 18; MBV 19; MBV 20; MBV 4; MBV 5; MB_dst; ELit 0x27e00; ELit 256; MBV 21; MBV 22; MBV 23; MBV 24; MBV 25;
   MBV 6; MBV 7; MBV 8; MBV 9; MBV 10; MBV 11; MBV 12; MBV 13; MBV 14; MBV 15; MBV 26; MBV 27; MBV 28; MBV 29].
Definition MCB_pre_kn : list kentry :=
  [ KRange (MBV 0) 0x97700 0x97700; KRange (MBV 1) 0x10007fffa000 0x800000000000; KRange (MBV 16) 0x10007fffa000 0x800000000000; KAlign (MBV 16) 16;
    KRange (EAlu ALU_SUB (MBV 16) (MBV 1)) 400 8192;
    KRange (EAlu ALU_SUB (EMd M_MUL (ELit 8) (MBV 17)) (MBV 16)) (8 * MB_SHOFF - 8192) (8 * MB_SHOFF - 8192); KRange (MBV 17) 0 (2^60);
    KWr (SA (MBV 1) (-2224)) (ELit 2224); KUnk (SA (MBV 1) (-2224)) (ELit 2224);
    KWr (SA (MBV 16) (-400)) (ELit 256); KUnk (SA (MBV 16) (-400)) (ELit 256);
    KZero (SA (ELit 0) 0x7fffcfc0) (ELit 32); KWr (SA (ELit 0) 0x7fffcfc0) (ELit 32);
    KZero (SA (MBV 17) 974) (ELit 32); KWr (SA (MBV 17) 0) (ELit 1024) ].
Definition MCB_pre : ST.tmpl := ST.TM 0x6584c MCB_pre_regs MCB_pre_kn 30%nat (ELit 0) 0%nat.
Definition MCB_post_regs : list expr :=
  [ELit 0; MBV 0; MBV 1; MBV 2; MBV 3; MBV 30; MBV 31; MBV 32; MBV 4; MBV 5; MB_dst; MBV 33; MBV 34; MBV 35; MBV 36; MBV 37; MBV 38; MBV 39;
   MBV 6; MBV 7; MBV 8; MBV 9; MBV 10; MBV 11; MBV 12; MBV 13; MBV 14; MBV 15; MBV 40; MBV 41; MBV 42; MBV 43].
(* [comment removed for export] *)
Definition MCB_post : ST.tmpl := ST.TMG 0x97700 MCB_post_regs [KUnk (SA (MBV 16) (-400)) (ELit 256)] 44%nat (ELit 0) 0%nat [ST.GA 2 [MBV 16]].
Definition MCB_W : list SP.win := [(MBV 1, -2224, ELit 2224); (MBV 16, -400, ELit 256)].
Definition MCB_A : list SP.win :=
  [(MBV 1, -2224, ELit 2224); (MBV 16, -400, ELit 256); (ELit 0, 0x10000, ELit 0x661000); (ELit 0, 0x7fffcfc0, ELit 32); (MBV 17, 0, ELit 1024)].
Definition MCB : SP.summ := SP.SUMR 18 MCB_pre [MCB_post] MCB_W (Some MCB_A) None.
