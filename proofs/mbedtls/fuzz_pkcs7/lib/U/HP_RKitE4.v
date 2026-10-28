(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Image ZBridge SysStep.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import SFModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl MallocRep MallocTree.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_RMallocRep HP_RMallocTree.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_HP_RKitE4 () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.U.HP_RMallocTree.rfresh_addr"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.region"; "stdpp.base.lookup"; "Corelib.Numbers.BinNums.N"; "stdpp.gmap.gmap"; "stdpp.numbers.N.eq_dec"; "stdpp.countable.N_countable"; "stdpp.gmap.gmap_lookup"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_regions"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.lr_lo"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.r_base"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.round_up_pg"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.r_len"].


Section RP_1. Context {hRP : run_params}.

(* [comment removed for export] *)
#[using="Type"] Lemma rfresh_live_region st a rid r : ltac2:(CDefT.buildp (gd_tbl_HP_RKitE4 ()) "P,(0.VhRP,O4.O3.)P,(1.(2.$3.)(4.$5.$3.(6.$5.$7.$8.$3.)(9.$5.$7.$8.$3.)O2.(:.O4.))(;.$3.O1.))(<.(=.(>.O3.+1.)(?.O1.))(=.(>.(10.O1.)(11.(12.O1.)))O3.))")
(* [comment removed for export] *).
Proof.
  intros [_ FR] Hr. pose proof (In_live_ranges st rid r Hr) as HI.
  unfold region_live_range in HI. unfold lr_lo. unfold PGSZ in HI.
  destruct (r_kind r); (pose proof (ranges_free_In _ _ _ _ _ FR HI); lia).
Qed.

End RP_1.
