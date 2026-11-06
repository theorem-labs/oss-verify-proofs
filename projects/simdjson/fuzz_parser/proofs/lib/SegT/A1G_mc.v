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

Definition MGV (n : nat) : expr := EVar n.
Definition MG_dst : expr := EAlu ALU_ADD (MGV 16) (ELit (-400)).
Definition MG_SHOFF : Z := 0x7fff8000.
Definition MCG_pre_regs : list expr :=
  [ELit 0; MGV 0; MGV 1; MGV 2; MGV 3; MGV 18; MGV 19; MGV 20; MGV 4; MGV 5; MG_dst; ELit 0x28140; ELit 256; MGV 21; MGV 22; MGV 23; MGV 24; MGV 25;
   MGV 6; MGV 7; MGV 8; MGV 9; MGV 10; MGV 11; MGV 12; MGV 13; MGV 14; MGV 15; MGV 26; MGV 27; MGV 28; MGV 29].
Definition MCG_pre_kn : list kentry :=
  [ KRange (MGV 0) 0x976c8 0x976c8; KRange (MGV 1) 0x10007fffa000 0x800000000000; KRange (MGV 16) 0x10007fffa000 0x800000000000; KAlign (MGV 16) 16;
    KRange (EAlu ALU_SUB (MGV 16) (MGV 1)) 400 8192;
    KRange (EAlu ALU_SUB (EMd M_MUL (ELit 8) (MGV 17)) (MGV 16)) (8 * MG_SHOFF - 8192) (8 * MG_SHOFF - 8192); KRange (MGV 17) 0 (2^60);
    KWr (SA (MGV 1) (-2224)) (ELit 2224); KUnk (SA (MGV 1) (-2224)) (ELit 2224);
    KWr (SA (MGV 16) (-400)) (ELit 256); KUnk (SA (MGV 16) (-400)) (ELit 256);
    KZero (SA (ELit 0) 0x7fffd028) (ELit 32); KWr (SA (ELit 0) 0x7fffd028) (ELit 32);
    KZero (SA (MGV 17) 974) (ELit 32); KWr (SA (MGV 17) 0) (ELit 1024) ].
Definition MCG_pre : ST.tmpl := ST.TM 0x65aa8 MCG_pre_regs MCG_pre_kn 30%nat (ELit 0) 0%nat.
Definition MCG_post_regs : list expr :=
  [ELit 0; MGV 0; MGV 1; MGV 2; MGV 3; MGV 30; MGV 31; MGV 32; MGV 4; MGV 5; MG_dst; MGV 33; MGV 34; MGV 35; MGV 36; MGV 37; MGV 38; MGV 39;
   MGV 6; MGV 7; MGV 8; MGV 9; MGV 10; MGV 11; MGV 12; MGV 13; MGV 14; MGV 15; MGV 40; MGV 41; MGV 42; MGV 43].
(* [comment removed for export] *)
Definition MCG_post : ST.tmpl := ST.TMG 0x976c8 MCG_post_regs [KUnk (SA (MGV 16) (-400)) (ELit 256)] 44%nat (ELit 0) 0%nat [ST.GA 2 [MGV 16]].
Definition MCG_W : list SP.win := [(MGV 1, -2224, ELit 2224); (MGV 16, -400, ELit 256)].
Definition MCG_A : list SP.win :=
  [(MGV 1, -2224, ELit 2224); (MGV 16, -400, ELit 256); (ELit 0, 0x10000, ELit 0x655000); (ELit 0, 0x7fffd028, ELit 32); (MGV 17, 0, ELit 1024)].
Definition MCG : SP.summ := SP.SUMR 18 MCG_pre [MCG_post] MCG_W (Some MCG_A) None.
