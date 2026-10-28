(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import AsanUbsan.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Common Require Import ExitSim.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic ShapeX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Sys Require Import Nodes.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Export SumWalkTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Sys Require Export SysNodes.
Import ListNotations.
#[local] Existing Instance Lib.PropExec.fx0.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_exit_base () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.le"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.store_ok"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_both.M.loaded_segments"; "Corelib.Init.Datatypes.true"; "Corelib.Init.Logic.and"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.rdn"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.Some"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.nil"].


Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ref_wseg_1c : wseg_ok RSEGS (0x0fa360 : word) 4096%nat = true.
Proof. vm_compute. reflexivity. Qed.

Lemma store_ok_data : ltac2:(CDefT.buildp (gd_tbl_A_exit_base ()) "Pm,P,(0.&40.)(1.(0.&8.))Pa,(0.&40.)Pn,$2.P,(3.+?:360.(4.&40.R2.))P,(3.(5.(4.&40.R3.)(6.R2.))+?;360.)(7.$8.(9.$:.R5.R4.R3.)$;.)")
(* [comment removed for export] *).
Proof.
  intros m a n Hlo Hhi.
  eapply (store_ok_window RSEGS m (0x0fa360 : word) a 4096%nat n 0x0fa360 0x0fb360);
    [reflexivity | reflexivity | lia | exact ref_wseg_1c | exact Hlo | exact Hhi].
Qed.

(* [comment removed for export] *)
Ltac sok_data := store_ok_peel; apply store_ok_data; zsimp; lia.

(* [comment removed for export] *)
Ltac sok_frame SOK :=
  store_ok_peel;
  eapply (store_ok_sub _ _ _ _ 112%nat); [ | exact SOK | | ]; zsimp; lia.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition file_clean (mem : word -> option byte) (f : Z) (wp rp : word) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_exit_base ()) "(<.(7.(1.(=.(0.&8.)))(>.$:.O4.(?.&40.(5.O3.+8<.))#4.)(10.(=.(0.&8.))(11.#4.(?.&40.+????????.))))(<.(7.(1.(=.(0.&8.)))(>.$:.O4.(?.&40.(5.O3.+28.))#8.)(10.(=.(0.&8.))(11.#8.O2.)))(<.(7.(1.(=.(0.&8.)))(>.$:.O4.(?.&40.(5.O3.+38.))#8.)(10.(=.(0.&8.))(11.#8.O2.)))(<.(7.(1.(=.(0.&8.)))(>.$:.O4.(?.&40.(5.O3.+8.))#8.)(10.(=.(0.&8.))(11.#8.O1.)))(7.(1.(=.(0.&8.)))(>.$:.O4.(?.&40.(5.O3.+10.))#8.)(10.(=.(0.&8.))(11.#8.O1.)))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition stdio_globals (mem : word -> option byte) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_exit_base ()) "(<.(7.(1.(=.(0.&8.)))(>.$:.O1.(?.&40.+65<=23.)#1.)(10.(=.(0.&8.))(12.(0.&8.)(?.&8.=)(13.(0.&8.)))))(<.(7.(1.(=.(0.&8.)))(>.$:.O1.(?.&40.+65=188.)#8.)(10.(=.(0.&8.))(11.#8.(?.&40.=))))(<.(7.(1.(=.(0.&8.)))(>.$:.O1.(?.&40.+?:750.)#8.)(10.(=.(0.&8.))(11.#8.(?.&40.+?:668.))))(<.(7.(1.(=.(0.&8.)))(>.$:.O1.(?.&40.+?:660.)#8.)(10.(=.(0.&8.))(11.#8.(?.&40.+?:578.))))(7.(1.(=.(0.&8.)))(>.$:.O1.(?.&40.+?:570.)#8.)(10.(=.(0.&8.))(11.#8.(?.&40.+?:488.))))))))")
(* [comment removed for export] *). (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
