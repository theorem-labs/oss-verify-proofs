(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSymExec2 BSymExec2Sound BSymRun BSymAux.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import DvB_ExitKit.
Import ListNotations.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Open Scope Z_scope.
Import SX2.

Definition ACUT : Z := 0xa1094.
Definition XNVT : nat := 80.
Definition XKEPT : list nat := Eval vm_compute in seq 1 29.

Definition x_regions_loop : list sregion :=
  [(SA (EVar 0) (-2560), 2560); (SA (ELit 0) 0x7fffa000, 0xdb000); (SA (ELit 0) 0x18e8f0, 8); (SA (ELit 0) 0x18d980, 8)].

Definition keep_ns (K : kentry) : bool :=
  match K with
  | KWord (SA (ELit 0) a) _ _ => negb ((0x7fff0000 <=? a) && (a <? 0x900000000))
  | _ => true
  end.

Definition LOOP_SEGS : list xseg :=
  [XCas 8] ++ repeat (XRun 1000%N [] [] keep_ns) 25 ++ [XCas 8; XRun 2000%N [] [] keep_ns].

Definition sr_T : list expr := [EVar 80; ELit 661084; EAlu ALU_ADD (EVar 0) (ELit (-256)); EVar 11; ELit 7100504; ELit 12682135451164737535; ELit 18446744073709551615; ELit 1; ELit 1500; ELit 1099511627776; ELit 0; ELit 18446744073709551615; ELit 0;
 ELit 1152921504606846976; ELit 1152921504606846976; ELit 0; ELit 1500; EAlu ALU_ADD (EVar 0) (ELit (-280)); ELit 1152921504606846976; ELit 1152921504607895551; ELit 16140901064495857663; ELit 2305843009213693952; ELit 1632432;
 ELit 245; ELit 1632496; ELit 1632312; EVar 34; EVar 35; ELit 6917529027642130431; ELit 16140901064495857663; EVar 110; EVar 111].

Definition kn_T : list kentry := [KWord {| a_base := EVar 0; a_off := -248 |} 8 (ELit 1632504); KWord {| a_base := EVar 0; a_off := -224 |} 8 (ELit 1612832); KWord {| a_base := EVar 0; a_off := -184 |} 8 (EVar 35); KWord {| a_base := EVar 0;
 a_off := -176 |} 8 (EVar 34); KWord {| a_base := EVar 0; a_off := -168 |} 8 (EVar 33); KWord {| a_base := EVar 0; a_off := -160 |} 8 (EVar 32); KWord {| a_base := EVar 0; a_off := -152 |} 8 (EVar 31); KWord {| a_base := EVar 0;
 a_off := -144 |} 8 (EVar 30); KWord {| a_base := EVar 0; a_off := -136 |} 8 (EVar 29); KWord {| a_base := EVar 0; a_off := -128 |} 8 (EVar 28); KWord {| a_base := EVar 0; a_off := -120 |} 8 (EVar 27); KWord {| a_base := EVar 0;
 a_off := -112 |} 8 (EVar 26); KWord {| a_base := EVar 0; a_off := -104 |} 8 (ELit 1566352); KWord {| a_base := EVar 0; a_off := -96 |} 8 (ELit 1628544); KWord {| a_base := EVar 0; a_off := -88 |} 8 (ELit 661084);
 KWord {| a_base := EVar 0; a_off := -80 |} 8 (ELit 1566352); KWord {| a_base := EVar 0; a_off := -72 |} 8 (ELit 958268); KWord {| a_base := EVar 0; a_off := -56 |} 8 (ELit 1463388); KWord {| a_base := ELit 0;
 a_off := 1628624 |} 1 (ELit 1); KWord {| a_base := EVar 0; a_off := -64 |} 8 (ELit 1566352); KWord {| a_base := EVar 0; a_off := -40 |} 8 (EVar 17); KWord {| a_base := EVar 0; a_off := -32 |} 8 (EVar 2); KWord {| a_base := EVar 0;
 a_off := -24 |} 8 (ELit 1463520); KWord {| a_base := EVar 0; a_off := -240 |} 1 (ELit 0); KWord {| a_base := EVar 0; a_off := -238 |} 1 (ELit 0); KWord {| a_base := EVar 0; a_off := -239 |} 1 (ELit 0); KWord {| a_base := EVar 0;
 a_off := -256 |} 8 (ELit 1612064); KWord {| a_base := ELit 0; a_off := 1612104 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1612096 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1612080 |} 8 (ELit 0);
 KWord {| a_base := ELit 0; a_off := 1612072 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1612120 |} 8 (ELit 0); KWord {| a_base := EVar 0; a_off := -232 |} 8 (EAlu ALU_ADD (EVar 0) (ELit (-184))); KWord {| a_base := EVar 0;
 a_off := -216 |} 8 (ELit 1210896); KWord {| a_base := ELit 0; a_off := 1612200 |} 4 (ELit 18446744073709551615); KWord {| a_base := EVar 0; a_off := -200 |} 8 (EAlu ALU_ADD (EVar 0) (ELit (-192))); KWord {| a_base := ELit 0;
 a_off := 1612584 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1612576 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1612560 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1612552 |} 8 (ELit 0);
 KWord {| a_base := ELit 0; a_off := 1612600 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1612680 |} 4 (ELit 18446744073709551615); KWord {| a_base := EVar 0; a_off := -48 |} 8 (EVar 26); KWord {| a_base := EVar 0;
 a_off := -16 |} 8 (EVar 16); KWord {| a_base := EVar 0; a_off := -8 |} 8 (EVar 9); KAlign (EVar 0) 16; KRange (EVar 0) 140735324094464 140737488355327; KWr {| a_base := EVar 0; a_off := -2560 |} 2560; KImg 65536 593920;
 KImg 1564672 1597440; KImg 1612296 1612544; KImg 1612776 1628544; KWord {| a_base := ELit 0; a_off := 2148337440 |} 8 (ELit 0); KWr {| a_base := ELit 0; a_off := 1612064 |} 232; KWr {| a_base := ELit 0; a_off := 1612544 |} 232;
 KWr {| a_base := ELit 0; a_off := 1628544 |} 8; KWr {| a_base := ELit 0; a_off := 1628624 |} 1; KWr {| a_base := ELit 0; a_off := 1632496 |} 8; KWr {| a_base := ELit 0; a_off := 2147459072 |} 897024; KWord {| a_base := ELit 0;
 a_off := 1601344 |} 8 (ELit 1601344); KWord {| a_base := ELit 0; a_off := 1601432 |} 8 (ELit 1498000); KWord {| a_base := ELit 0; a_off := 1601544 |} 8 (ELit 1491204); KWord {| a_base := ELit 0;
 a_off := 1601600 |} 8 (ELit 1495328); KWord {| a_base := ELit 0; a_off := 1601856 |} 8 (ELit 1534624); KWord {| a_base := ELit 0; a_off := 1601864 |} 8 (ELit 1535652); KWord {| a_base := ELit 0; a_off := 1612064 |} 4 (ELit 5);
 KWord {| a_base := ELit 0; a_off := 1612152 |} 8 (ELit 7233648); KWord {| a_base := ELit 0; a_off := 1612160 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1612204 |} 4 (ELit 4294967295); KWord {| a_base := ELit 0;
 a_off := 1612208 |} 4 (ELit 4294967295); KWord {| a_base := ELit 0; a_off := 1612296 |} 8 (ELit 1612064); KWord {| a_base := ELit 0; a_off := 1612312 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1612320 |} 8 (ELit 0);
 KWord {| a_base := ELit 0; a_off := 1612344 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1612360 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1612444 |} 4 (ELit 4294967295); KWord {| a_base := ELit 0;
 a_off := 1612536 |} 8 (ELit 1612304); KWord {| a_base := ELit 0; a_off := 1612544 |} 4 (ELit 5); KWord {| a_base := ELit 0; a_off := 1612632 |} 8 (ELit 7234688); KWord {| a_base := ELit 0; a_off := 1612640 |} 8 (ELit 1024);
 KWord {| a_base := ELit 0; a_off := 1612684 |} 4 (ELit 4294967295); KWord {| a_base := ELit 0; a_off := 1612776 |} 8 (ELit 1612544); KWord {| a_base := ELit 0; a_off := 1628544 |} 8 (ELit 1); KWord {| a_base := ELit 0;
 a_off := 1632336 |} 4 (ELit 1); KWord {| a_base := ELit 0; a_off := 1632340 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 1632496 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1640604 |} 1 (ELit 1);
 KWord {| a_base := ELit 0; a_off := 1642552 |} 8 (ELit 2147450880); KWord {| a_base := ELit 0; a_off := 1645848 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 1645849 |} 1 (ELit 1); KWord {| a_base := ELit 0;
 a_off := 2239456 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 2240224 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 7232235 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 7233632 |} 8 (ELit 0)].

Definition loop_end_chk (sr : list expr) : bool :=
  (expr_eqb (nth 17 sr (ELit 0)) (ELit 94) && expr_eqb (nth 10 sr (ELit 0)) (EVar 2))%bool.
