(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HSymExec2 HSymExec2Sound HSymRun HSymAux.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import DvA_ExitKit.
Import ListNotations.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Open Scope Z_scope.
Import SX2.

Definition ACUT : Z := 0xa144c.
Definition XNVT : nat := 80.
Definition XKEPT : list nat := Eval vm_compute in seq 1 29.

Definition x_regions_loop : list sregion :=
  [(SA (EVar 0) (-2560), 2560); (SA (ELit 0) 0x7fffa000, 0xdac00); (SA (ELit 0) 0x18cfb0, 8); (SA (ELit 0) 0x18c040, 8)].

Definition keep_ns (K : kentry) : bool :=
  match K with
  | KWord (SA (ELit 0) a) _ _ => negb ((0x7fff0000 <=? a) && (a <? 0x900000000))
  | _ => true
  end.

Definition LOOP_SEGS : list xseg :=
  [XCas 8] ++ repeat (XRun 1000%N [] [] keep_ns) 25 ++ [XCas 8; XRun 2000%N [] [] keep_ns].

Definition sr_T : list expr := [EVar 80; ELit 662036; EAlu ALU_ADD (EVar 0) (ELit (-256)); EVar 11; ELit 7094040; ELit 12682135451164737535; ELit 18446744073709551615; ELit 1; ELit 1500; ELit 1099511627776; ELit 0; ELit 18446744073709551615; ELit 0;
 ELit 1152921504606846976; ELit 1152921504606846976; ELit 0; ELit 1500; EAlu ALU_ADD (EVar 0) (ELit (-280)); ELit 1152921504606846976; ELit 1152921504607895551; ELit 16140901064495857663; ELit 2305843009213693952; ELit 1625968;
 ELit 247; ELit 1626032; ELit 1625848; EVar 34; EVar 35; ELit 6917529027642130431; ELit 16140901064495857663; EVar 110; EVar 111].

Definition kn_T : list kentry := [KWord {| a_base := EVar 0; a_off := -248 |} 8 (ELit 1626040); KWord {| a_base := EVar 0; a_off := -224 |} 8 (ELit 1606240); KWord {| a_base := EVar 0; a_off := -184 |} 8 (EVar 35); KWord {| a_base := EVar 0;
 a_off := -176 |} 8 (EVar 34); KWord {| a_base := EVar 0; a_off := -168 |} 8 (EVar 33); KWord {| a_base := EVar 0; a_off := -160 |} 8 (EVar 32); KWord {| a_base := EVar 0; a_off := -152 |} 8 (EVar 31); KWord {| a_base := EVar 0;
 a_off := -144 |} 8 (EVar 30); KWord {| a_base := EVar 0; a_off := -136 |} 8 (EVar 29); KWord {| a_base := EVar 0; a_off := -128 |} 8 (EVar 28); KWord {| a_base := EVar 0; a_off := -120 |} 8 (EVar 27); KWord {| a_base := EVar 0;
 a_off := -112 |} 8 (EVar 26); KWord {| a_base := EVar 0; a_off := -104 |} 8 (ELit 1559784); KWord {| a_base := EVar 0; a_off := -96 |} 8 (ELit 1622080); KWord {| a_base := EVar 0; a_off := -88 |} 8 (ELit 662036);
 KWord {| a_base := EVar 0; a_off := -80 |} 8 (ELit 1559784); KWord {| a_base := EVar 0; a_off := -72 |} 8 (ELit 957016); KWord {| a_base := EVar 0; a_off := -56 |} 8 (ELit 1456824); KWord {| a_base := ELit 0;
 a_off := 1622160 |} 1 (ELit 1); KWord {| a_base := EVar 0; a_off := -64 |} 8 (ELit 1559784); KWord {| a_base := EVar 0; a_off := -40 |} 8 (EVar 17); KWord {| a_base := EVar 0; a_off := -32 |} 8 (EVar 2); KWord {| a_base := EVar 0;
 a_off := -24 |} 8 (ELit 1456956); KWord {| a_base := EVar 0; a_off := -240 |} 1 (ELit 0); KWord {| a_base := EVar 0; a_off := -238 |} 1 (ELit 0); KWord {| a_base := EVar 0; a_off := -239 |} 1 (ELit 0); KWord {| a_base := EVar 0;
 a_off := -256 |} 8 (ELit 1605472); KWord {| a_base := ELit 0; a_off := 1605512 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1605504 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1605488 |} 8 (ELit 0);
 KWord {| a_base := ELit 0; a_off := 1605480 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1605528 |} 8 (ELit 0); KWord {| a_base := EVar 0; a_off := -232 |} 8 (EAlu ALU_ADD (EVar 0) (ELit (-184))); KWord {| a_base := EVar 0;
 a_off := -216 |} 8 (ELit 1204332); KWord {| a_base := ELit 0; a_off := 1605608 |} 4 (ELit 18446744073709551615); KWord {| a_base := EVar 0; a_off := -200 |} 8 (EAlu ALU_ADD (EVar 0) (ELit (-192))); KWord {| a_base := ELit 0;
 a_off := 1605992 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1605984 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1605968 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1605960 |} 8 (ELit 0);
 KWord {| a_base := ELit 0; a_off := 1606008 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1606088 |} 4 (ELit 18446744073709551615); KWord {| a_base := EVar 0; a_off := -48 |} 8 (EVar 26); KWord {| a_base := EVar 0;
 a_off := -16 |} 8 (EVar 16); KWord {| a_base := EVar 0; a_off := -8 |} 8 (EVar 9); KAlign (EVar 0) 16; KRange (EVar 0) 140735324094464 140737488355327; KWr {| a_base := EVar 0; a_off := -2560 |} 2560; KImg 65536 593920;
 KImg 1556480 1593344; KImg 1605704 1605952; KImg 1606184 1622080; KWord {| a_base := ELit 0; a_off := 2148336632 |} 8 (ELit 0); KWr {| a_base := ELit 0; a_off := 1605472 |} 232; KWr {| a_base := ELit 0; a_off := 1605952 |} 232;
 KWr {| a_base := ELit 0; a_off := 1622080 |} 8; KWr {| a_base := ELit 0; a_off := 1622160 |} 1; KWr {| a_base := ELit 0; a_off := 1626032 |} 8; KWr {| a_base := ELit 0; a_off := 2147459072 |} 896000; KWord {| a_base := ELit 0;
 a_off := 1594752 |} 8 (ELit 1594752); KWord {| a_base := ELit 0; a_off := 1594840 |} 8 (ELit 1491436); KWord {| a_base := ELit 0; a_off := 1594952 |} 8 (ELit 1484640); KWord {| a_base := ELit 0;
 a_off := 1595008 |} 8 (ELit 1488764); KWord {| a_base := ELit 0; a_off := 1595264 |} 8 (ELit 1528060); KWord {| a_base := ELit 0; a_off := 1595272 |} 8 (ELit 1529088); KWord {| a_base := ELit 0; a_off := 1605472 |} 4 (ELit 5);
 KWord {| a_base := ELit 0; a_off := 1605560 |} 8 (ELit 7227184); KWord {| a_base := ELit 0; a_off := 1605568 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1605612 |} 4 (ELit 4294967295); KWord {| a_base := ELit 0;
 a_off := 1605616 |} 4 (ELit 4294967295); KWord {| a_base := ELit 0; a_off := 1605704 |} 8 (ELit 1605472); KWord {| a_base := ELit 0; a_off := 1605720 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1605728 |} 8 (ELit 0);
 KWord {| a_base := ELit 0; a_off := 1605752 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1605768 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1605852 |} 4 (ELit 4294967295); KWord {| a_base := ELit 0;
 a_off := 1605944 |} 8 (ELit 1605712); KWord {| a_base := ELit 0; a_off := 1605952 |} 4 (ELit 5); KWord {| a_base := ELit 0; a_off := 1606040 |} 8 (ELit 7228224); KWord {| a_base := ELit 0; a_off := 1606048 |} 8 (ELit 1024);
 KWord {| a_base := ELit 0; a_off := 1606092 |} 4 (ELit 4294967295); KWord {| a_base := ELit 0; a_off := 1606184 |} 8 (ELit 1605952); KWord {| a_base := ELit 0; a_off := 1622080 |} 8 (ELit 1); KWord {| a_base := ELit 0;
 a_off := 1625872 |} 4 (ELit 1); KWord {| a_base := ELit 0; a_off := 1625876 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 1626032 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1634140 |} 1 (ELit 1);
 KWord {| a_base := ELit 0; a_off := 1636088 |} 8 (ELit 2147450880); KWord {| a_base := ELit 0; a_off := 1639384 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 1639385 |} 1 (ELit 1); KWord {| a_base := ELit 0;
 a_off := 2232992 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 2233760 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 7225771 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 7227168 |} 8 (ELit 0)].

Definition loop_end_chk (sr : list expr) : bool :=
  (expr_eqb (nth 17 sr (ELit 0)) (ELit 94) && expr_eqb (nth 10 sr (ELit 0)) (EVar 2))%bool.
