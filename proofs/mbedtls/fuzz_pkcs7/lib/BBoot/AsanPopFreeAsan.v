(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import PropExec CatExec CatSim SeqExec StoreOk. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require Import AsanPopFree.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AsanPopFreeAsan () : Init.string Init.list := ["LinuxProcessSemantics.Riscv.Prelude.bvmap"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.ABoot.PropExec.getr"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.sub"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.store_ok"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_both.M.loaded_segments"; "Corelib.Init.Datatypes.true"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.ABoot.CatSim.msteps"; "RocqVerifyHarness.AgentSubmission.ABoot.PropExec.mkst"; "asanreflect_fx"; "asan_popfree_head"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanPopFree.pf_mem"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Stdlib.ZArith.BinInt.Z.div"; "Corelib.Init.Logic.not"].


#[local] Notation ASEGS := AsanUbsan.M.loaded_segments (only parsing).

(* [comment removed for export] *)
Definition asan_popfree_head : Z := 0x4cd1c.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Lemma PF0 : fetch_word ASEGS (Z_to_bv 64 asan_popfree_head) = Some PW0. Proof. vm_refl. Qed.
Lemma PF1 : fetch_word ASEGS (Z_to_bv 64 (asan_popfree_head + 4)) = Some PW1. Proof. vm_refl. Qed.
Lemma PF2 : fetch_word ASEGS (Z_to_bv 64 (asan_popfree_head + 8)) = Some PW2. Proof. vm_refl. Qed.
Lemma PF3 : fetch_word ASEGS (Z_to_bv 64 (asan_popfree_head + 12)) = Some PW3. Proof. vm_refl. Qed.
Lemma PF4 : fetch_word ASEGS (Z_to_bv 64 (asan_popfree_head + 16)) = Some PW4. Proof. vm_refl. Qed.
Lemma PF5 : fetch_word ASEGS (Z_to_bv 64 (asan_popfree_head + 20)) = Some PW5. Proof. vm_refl. Qed.
Lemma PF6 : fetch_word ASEGS (Z_to_bv 64 (asan_popfree_head + 24)) = Some PW6. Proof. vm_refl. Qed.
Lemma PF7 : fetch_word ASEGS (Z_to_bv 64 (asan_popfree_head + 28)) = Some PW7. Proof. vm_refl. Qed.

Theorem asan_popfree_spec : popfree_spec AsanUbsan.M.loaded_segments asan_popfree_head.
Proof.
  apply popfree_spec_of_code; [unfold asan_popfree_head; lia | exact PF0 | exact PF1 | exact PF2 | exact PF3 | exact PF4 | exact PF5 | exact PF6 | exact PF7].
Qed.

(* [comment removed for export] *)
Theorem asan_popfree_loop_run : ltac2:(CDefT.buildp (gd_tbl_AsanPopFreeAsan ()) "Pregs,(0.&5.(1.&40.))Pmem,P,(1.&40.)(2.(1.&8.))Prom,P,(1.&40.)(2.(1.&8.))Pi,$3.Pe,$3.Pc,$3.Ps,$3.Pn,$3.P,(4.(1.&40.)(5.R8.(6.&5.+:.$7.))(8.&40.R5.))P,(4.(1.&40.)(5.R9.(6.&5.+;.$7.))(8.&40.R5.))P,(4.(1.&40.)(5.R:.(6.&5.+<.$7.))(8.&40.R5.))P,(4.(1.&40.)(5.R;.(6.&5.+15.$7.))(8.&40.R5.))P,(4.(1.&40.)(5.R<.(6.&5.+13.$7.))(8.&40.R5.))P,(9.=R:.)P,(:.R;.R7.)P,(9.(;.+4.R8.)R;.)P,(:.R<.(<.+2.+40.))P,(9.=R<.)P,(9.=R<.)P,(:.(=.R>.(;.(>.R<.R10.)R=.))(<.+2.+40.))P,Pd,$3.Pm,$?.P,(9.=R2.)P,(9.(=.R3.(10.R2.))(;.+4.(>.R10.R14.)))(4.$11.(12.$13.R17.(8.&40.(=.(>.R14.(;.+4.R11.))R4.))R3.)$14.)(15.(0.&5.(1.&40.))Lregs',(0.&5.(1.&40.))(16.(17.$13.(18.$19.R16.(8.&40.$1:.)R15.R14.)(18.$19.R1.(8.&40.(=.$1:.+20.))(1;.R15.R12.R11.R10.R13.(1<.(>.R?.R13.)))R14.))(16.(4.(1.&40.)(5.R1.(6.&5.+:.$7.))(8.&40.R?.))(16.(4.(1.&40.)(5.R1.(6.&5.+;.$7.))(8.&40.R12.))(16.(4.(1.&40.)(5.R1.(6.&5.+<.$7.))(8.&40.(=.R11.(;.(>.R?.R13.)R10.))))(16.(4.(1.&40.)(5.R1.(6.&5.+15.$7.))(8.&40.R10.))(16.(4.(1.&40.)(5.R1.(6.&5.+13.$7.))(8.&40.R?.))(16.(4.(1.&40.)(5.R1.(6.&5.+>.$7.))(8.&40.(1=.(=.R11.(;.(>.(>.R?.R13.)+1.)R10.))+10.)))(16.(4.(1.&40.)(5.R1.(6.&5.+?.$7.))(8.&40.(>.R12.(;.+4.R?.))))Pr,(1.&5.)P,(1>.(4.(1.&5.)R1.(6.&5.+:.$7.)))P,(1>.(4.(1.&5.)R2.(6.&5.+<.$7.)))P,(1>.(4.(1.&5.)R3.(6.&5.+>.$7.)))P,(1>.(4.(1.&5.)R4.(6.&5.+?.$7.)))(4.(1.&40.)(5.R6.R5.)(5.R1;.R5.)))))))))))")
(* [comment removed for export] *).
Proof.
  apply (popfree_loop_run ASEGS asan_popfree_head); [unfold asan_popfree_head; lia | exact PF0 | exact PF1 | exact PF2 | exact PF3 | exact PF4 | exact PF5 | exact PF6 | exact PF7].
Qed.
