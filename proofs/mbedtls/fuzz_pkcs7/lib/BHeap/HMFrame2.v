(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModelX APop.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Unwind AW_Unwind2 AW_MmapFixed AW_MmapDie AW_DepotA AW_DepotB AW_DepotC AW_DepotF AW_DepotCfg AW_DepotInv AW_DepotTop
     AW_MallocA AW_AllocA AW_Poison AW_AllocB AW_MallocB AW_MallocC.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_ClassId AW_Combined AW_Refill AW_Populate AW_Large AW_CfgDefs.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Blist AW_FakeDefs AW_MmapFixedNR AW_PoisonBig AW_SFree5 AW_SMalloc HMLib HM AImgW HMFrame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_HMFrame2 () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.pcl"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.BHeap.HM.hm_pclass"; "Corelib.Init.Datatypes.false"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Refill.pc_old"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32s"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Refill.pc_new"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.PC"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.max_count"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.class_size"].


Section ARUN_1. Context {hAR : arun}.

(* [comment removed for export] *)
#[using="Type"] Lemma u32arr_CB : forall m A ws, u32arr asegs m A ws -> rw_cells asegs m A [CB (4 * length ws)%nat (u32s ws)].
Proof.
  intros m A ws [B W]. split; [split|].
  - cbn. rewrite u32s_length. split; [reflexivity| exact I].
  - cbn [cells_bytes cbytes app]. rewrite app_nil_r. exact B.
  - cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Nat2Z.inj_mul. exact W.
Qed.

#[using="Type"] Lemma CB_u32arr : forall m A ws k, rw_cells asegs m A [CB k (u32s ws)] -> u32arr asegs m A ws.
Proof.
  intros m A ws k [[WF B] W]. cbn in WF. destruct WF as [LEN _]. rewrite u32s_length in LEN.
  cbn [cells_bytes cbytes app] in B. rewrite app_nil_r in B. cbn [cells_size csize Nat.add] in W. rewrite Nat.add_0_r in W.
  split; [exact B|]. rewrite <- LEN, Nat2Z.inj_mul in W. exact W.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma pc_old_of_pclass : ltac2:(CDefT.buildp (gd_tbl_HMFrame2 ()) "Pm,P,(0.&40.)(1.(0.&8.))PT,$2.Pc,$2.Pp,$3.Pds,(4.(0.&40.))P,(5.R5.R4.$6.R3.R2.R1.)(7.R6.R5.L,$2.(8.&40.=)L,$2.(8.&40.=)L,$2.(8.&40.=)L,$2.(9.$:.(;.#40.(<.R3.))(=.$:.))R4.)")
(* [comment removed for export] *).
Proof.
  (intros m T c p ds dd_H; ddestruct dd_H as (PC & ARR & LEN & FST & (PM & PCS & PCH))). unfold pc_old.
  apply rw_cells_app. split.
  - unfold pc_count in PC. rewrite PCH, PM, PCS in PC. cbn [length Z.of_nat] in PC. exact PC.
  - cbn [cells_size csize Nat.add]. change (Z.of_nat 16) with 16.
    replace 64%nat with (4 * length ds)%nat by (rewrite LEN; reflexivity). exact (u32arr_CB m _ ds ARR).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma pclass_of_pc_new : ltac2:(CDefT.buildp (gd_tbl_HMFrame2 ()) "Pm,P,(0.&40.)(1.(0.&8.))PT,$2.Pc,$2.Pcnt,P,$2.(0.&40.)Prest,P,$2.(4.$:.)Pds,(4.(0.&40.))P,(>.R6.R5.R3.R2.R4.)P,(?.(0.&40.)A1.R4.R5.(8.&40.=))P,(?.(4.$:.)A1.R4.R6.(9.$:.(;.#40.(<.R3.))(=.$:.)))P,(?.$10.(11.(0.&40.)R4.)#10.)(5.R:.R9.$12.R8.(13.(14.R8.)(15.R8.)(=.$2.))R5.)")
(* [comment removed for export] *).
Proof.
  intros m T c cnt rest ds PN EC ER LEN. unfold pc_new in PN. rewrite EC, ER in PN.
  apply rw_cells_app in PN. destruct PN as [HD SL]. cbn [cells_size csize Nat.add] in SL. change (Z.of_nat 16) with 16 in SL.
  split; [| split; [| split; [exact LEN| split; [reflexivity| split; reflexivity]]]].
  - unfold pc_count. cbn [pc_chunks pc_max pc_csize length Z.of_nat]. exact HD.
  - exact (CB_u32arr m _ ds _ SL).
Qed.

Section G2I.
  Variables (m m' : mem).
  Hypothesis WM : wmono asegs m m'.

  (* [comment removed for export] *)
  #[using="WM"] Lemma hm_thread_frame_all : forall h c0 (P : pcl) ds0 (cnt : Z -> word) (rest : Z -> list cell) (dsF : Z -> list word),
    hm_thread h m -> h_cinit h = false -> 1 <= c0 <= 31 ->
    rw_cells asegs m' (l_T (h_L h) + 3168) [C1 (Z_to_bv 8 0)] ->
    kept m m' (l_T (h_L h) + 2768) 16 ->
    wr_at asegs m (l_T (h_L h)) 4096 -> Timg (l_T (h_L h)) ->
    hm_pclass m' (l_T (h_L h)) true c0 P ds0 ->
    (forall c, 1 <= c <= 31 -> c <> c0 -> pc_new m' (l_T (h_L h)) cnt rest c) ->
    (forall c, 1 <= c <= 31 -> c <> c0 -> cnt c = w64 0 /\ rest c = [CB 64%nat (u32s (dsF c))] /\ length (dsF c) = 16%nat) ->
    forall h', h_L h' = h_L h -> h_cinit h' = true ->
    (forall c, 1 <= c <= 31 -> h_cache h' c = if c =? c0 then P else PC (max_count c) (class_size c) []) ->
    hm_thread h' m'.
  Proof.
    (intros h c0 P ds0 cnt rest dsF dd_H; ddestruct dd_H as (UNW & (ds & PCL) & (j0 & j1 & J) & _); intros CI Hc0 K1 K2 WT HT NEW PN PF h' EL EI EC).
    unfold hm_thread. rewrite EL, EI. split; [| split; [| split]].
    - exact K1.
    - exists (fun c => if c =? c0 then ds0 else dsF c). intros c Hc. rewrite (EC c Hc).
      destruct (Z.eqb_spec c c0) as [->|NE]; [exact NEW|].
      ddestruct (PF c Hc NE) as (E1 & E2 & E3).
      exact (pclass_of_pc_new m' _ c cnt rest (dsF c) (PN c Hc NE) E1 E2 E3).
    - dexists j0, j1. eapply keep_rw; [exact J| exact K2| exact WM].
    - apply (hm_tstats_of_wr m'); [eapply wr_at_transport; [exact WT| exact WM]| exact HT].
  Qed.
End G2I.

End ARUN_1.
