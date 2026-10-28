(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
Import ListNotations.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Ltac2 gd_tbl_AW_FakeDefs () : Init.string Init.list := ["Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "Corelib.Init.Datatypes.nil"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "ARUN_1.fsk_hint"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u8arr"; "ARUN_1.fsk_foff"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "ARUN_1.fsk_n"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Datatypes.option"; "Stdlib.Lists.List.nth_error"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Init.Datatypes.Some"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Logic.not"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "ARUN_1.fsk_frame"; "ARUN_1.fsk_bytes"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "Stdlib.Lists.List.NoDup"; "Corelib.Lists.ListDef.map"; "Corelib.Init.Datatypes.fst"].

Section ARUN_1. Context {hAR : arun}.
Definition fsk_flags (FS k : Z) : Z := FS + 4096 + (2^15 - 2^(15 - k)).
Definition fsk_frame (FS k pos : Z) : Z := FS + 36864 + k * 2^20 + pos * (64 * 2^k).
(* [comment removed for export] *)
Definition shd (p : Z) : Z := 2147450880 + Z.shiftr p 3.
Definition fsk_n (k : Z) : Z := 2^(14 - k).                       (* [comment removed for export] *)
Definition fsk_bytes (k : Z) : Z := 64 * 2^k.                     (* [comment removed for export] *)
Definition fsk_foff (k : Z) : Z := 4096 + (2^15 - 2^(15 - k)).    (* [comment removed for export] *)
Definition fsk_hint (FS k : Z) : Z := if Z.eqb k 0 then FS else FS + 8 * k.
Definition fsk_hint8 (FS k : Z) : Z := if Z.eqb k 0 then FS + 8 else FS + (8 * k + 8).

(* [comment removed for export] *)
Definition fake_rep (FS : Z) (LF : list blk) (m : mem) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_FakeDefs ()) "(0.(1.$2.O1.(3.O3.+58.)(4.$5.(6.(7.&40.+14.))(4.$5.(8.(7.&8.=))(9.$5.))))(0.Pk,$:.P,(0.(;.=R1.)(;.R1.+:.))(<.(=.&40.)Lh,(=.&40.)(>.$2.O1.(?.O3.R3.)(4.$5.(6.R1.)(9.$5.))))(0.Pk,$:.P,(0.(;.=R1.)(;.R1.+:.))(<.(10.(=.&8.))Lfl,(10.(=.&8.))(0.(11.$2.O1.(3.O3.(12.R3.))R1.)(0.(13.$:.(14.(15.(=.&8.)R1.))(16.R3.))Pi,$:.P,(0.(;.=R1.)(17.R1.(16.R4.)))(<.(=.&8.)Lb,(=.&8.)(0.(13.(18.(=.&8.))(19.(=.&8.)R4.(1:.R3.))(1;.(=.&8.)R1.))(0.P,(13.$:.(1<.&8.R1.)=)(1=.(1>.(1?.$:.$:.)(20.$:.$:.(21.O3.R7.R4.)(22.R7.))O2.))P,(1=.(13.$:.(1<.&8.R1.)=))(0.(1>.(1?.$:.$:.)(20.$:.$:.(21.O3.R7.R4.)(22.R7.))O2.)(1.$2.O1.(23.(3.(21.O3.R7.R4.)(22.R7.))+8.)(4.$5.(6.(7.&40.(3.(3.O3.(12.R7.))R4.)))(9.$5.))))))))))(0.Pfb,$24.P,(1>.$24.R1.O2.)(<.$:.Lk,$:.(<.$:.Li,$:.(0.(0.(;.=R2.)(;.R2.+:.))(0.(0.(;.=R1.)(17.R1.(16.R2.)))(13.$24.R4.(20.$:.$:.(21.O3.R2.R1.)(22.R2.)))))))(25.$:.(26.(1?.$:.$:.)$:.(27.$:.$:.)O2.))))))")
(* [comment removed for export] *).

End ARUN_1.
