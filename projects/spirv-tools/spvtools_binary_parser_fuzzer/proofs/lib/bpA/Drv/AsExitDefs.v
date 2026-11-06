(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require As0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HPropExec HCatExec HCatSim HSeqExec HStoreOk HSymExec HSymExec2 HSymExec2Sound HSymRun HSymDrive HLibKnowFrame.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HRefExitBase HRefStdioDefs AsStdioCall AsPrintfFirst.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AsCarryKeep.
Import ListNotations.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Import SX2. Import SX2S.

Abbreviation RSEGS := Asan.M.loaded_segments.

Definition AEXIT : Z := 0x163ad4.
Definition AEXIT_ECALL : Z := 0x1637e4.
Definition AX_FR : Z := 400.
Definition XFUEL : nat := 20000.
Definition XSTOPS : list Z := [0x16b42c]%Z.

Definition x_sr : list expr :=
  Eval cbv in (map (fun i => match i with
                          | 0 => ELit 0%Z | 2 => EVar 0 | 4 => ELit 0x6c3f18%Z | 10 => EVar 2
                          | _ => EVar (8 + i) end)%nat (seq 0 32)).

Definition ax_lit_cells : list (Z * nat * Z) :=
  [(0x6e4188, 4%nat, 0);
   (0x6e41ab, 1%nat, 0);
   (0x6e3f6c, 4%nat, 0);
   (0x6e3f70, 4%nat, 3);
   (0x6e3f78, 8%nat, 0x6e3f80);
   (0x6e3f80, 8%nat, 0);
   (0x6e3f88, 8%nat, 0x163a80);
   (0x6e4088, 8%nat, 0xd820c);
   (0x2215a0, 1%nat, 0);
   (0x18c090, 1%nat, 0);
   (0x185580, 8%nat, 0x185580);
   (0x18c040, 8%nat, 1);
   (0x18ef5c, 1%nat, 1);
   (0x1903d8, 1%nat, 1);
   (0x18f6f8, 8%nat, 0x7fff8000);
   (0x18cfb0, 8%nat, 0);
   (0x18cf10, 4%nat, 1);
   (0x185788, 8%nat, 0x175500);
   (0x2212a0, 8%nat, 0xffffffffffffffff);
   (0x6e4720, 8%nat, 0);
   (0x187fec, 4%nat, 0xffffffff);
   (0x1881cc, 4%nat, 0xffffffff);

   (0x6e3f90, 8%nat, 0x1252fc); (0x6e3f98, 8%nat, 0xae744); (0x6e4090, 8%nat, 0x6c1fb8); (0x6e4098, 8%nat, 0)]%Z.

Definition ax_flush_cells : list (Z * nat * Z) :=
  [(0x188178, 8%nat, 0x6e4b40); (0x188188, 8%nat, 0x16b42c); (0x188198, 8%nat, 0x6e4b40); (0x1881a0, 8%nat, 1024); (0x1881b8, 4%nat, 1)]%Z.

Definition scr0 : scripts := SCR [] [] [].

Definition keep_nonshadow (K : kentry) : bool :=
  match K with
  | KWord (SA (ELit 0) a) _ _ => negb ((0x7fff0000 <=? a) && (a <? 0x900000000))%Z
  | _ => true
  end.
Definition kn_drop_shadow (kn : list kentry) : list kentry := List.filter keep_nonshadow kn.

Definition one_carry (a : Z) (w : nat) (v : expr) (kn : list kentry) : list kentry :=
  fst (fst (carry [SE (SA (ELit 0) a) w v] kn [])).
