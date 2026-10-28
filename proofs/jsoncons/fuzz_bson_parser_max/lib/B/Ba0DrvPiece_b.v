(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AsanAcct.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg Hoare AsanAcctShape SymExec2 SymExec2Sound SymRun SymDrive SymDriveX
  HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import DrvKitA DrvNodesLazyK As0DrvKitA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0DrvEntry_b Ba0Drv_defs_b Ba0DrvLib_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section Piece.
Variable scfg : SpuriousCfg.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable IL : icpt_layout.
Variable HI : asan_iface.
Hypothesis HIok : asan_iface_okB L ar C scfg HI.
Variable sp0 : word.
Hypothesis Hsp : 0x7fff80000000 <= bv_unsigned sp0 <= 2 ^ 47.
Hypothesis DL : drv_layoutA L ar IL sp0.
Variable M0 : word -> option byte.

#[local] Notation dinvA := (dinv ar HI sp0 M0).
#[local] Notation rom := (seg_rom ASEGS).

Theorem drv_piece : forall LB LK cr A M (model : Model) (fx fx' : PropExec.FPState) R (pc : word) R' (pc' : word) (MV' : word -> option byte) (W : Z -> Prop) K,
  dinvA LB LK cr A M model ->
  msteps ASEGS (@mkst fx R pc (mrestrict (ahid A model) M) rom) (@mkst fx' R' pc' MV' rom) ->
  (forall a : word, mrestrict (ahid A model) M a <> None -> MV' a <> None) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ W a -> MV' (Z_to_bv 64 a) = mrestrict (ahid A model) M (Z_to_bv 64 a)) ->
  (forall a, W a -> CWA sp0 LB a) ->
  (forall M1 (model1 : Model),
      dinvA LB LK cr A M1 model1 -> same_but_materialized model model1 ->
      mrestrict (ahid A model1) M1 = MV' ->
      (forall a, 0 <= a < 2 ^ 64 -> ~ W a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
      srealizes ASEGS scfg (mkCfg (@mkst fx' R' pc' M1 rom) model1) K) ->
  srealizes ASEGS scfg (mkCfg (@mkst fx R pc M rom) model) K.
Proof.
  intros LB LK cr A M model fx fx' R pc R' pc' MV' W K DI MS GR FZ WC KONT.
  pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ DI) as (HH & HL & HA & HM & Hh).
  set (H := ahid A model) in *.
  apply (srz_msteps_restricted_T ASEGS scfg H HH asegs_wx A (@mkst fx R pc M rom) (@mkst fx' R' pc' MV' rom) model K HL HA HM Hh MS).
  intros model1 MI1 SBM HC.
  change (unrestrict H (ms_mem (@mkst fx R pc M rom)) (@mkst fx' R' pc' MV' rom)) with (@mkst fx' R' pc' (munrestrict H M MV') rom).
  set (M1 := munrestrict H M MV').
  assert (VIS : mrestrict H M1 = MV') by (apply As0DrvKitA.mrestrict_munrestrict; intros a Ha; exact (HC a Ha)).
  assert (FR1 : forall a, 0 <= a < 2 ^ 64 -> ~ W a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha Hn. unfold M1, munrestrict. destruct (H (Z_to_bv 64 a)) eqn:E; [reflexivity|]. rewrite (FZ a Ha Hn). unfold mrestrict. rewrite E. reflexivity. }
  assert (AH : ahid A model1 = H) by (unfold H; apply (ahid_sbm A model model1 SBM)).
  apply (KONT M1 model1).
  - apply (dinv_frame scfg L ar C IL HI HIok sp0 Hsp DL M0 LB LK cr A M M1 model model1 DI).
    + intros a Ha Hn. apply FR1; [exact Ha|]. intros Hw. exact (Hn (WC a Hw)).
    + intros a Ha. unfold M1, munrestrict. destruct (H a) eqn:E; [exact Ha|]. apply GR. unfold mrestrict. rewrite E. exact Ha.
    + exact (sbm_vml _ _ SBM).
    + exact MI1.
    + rewrite (sbm_halted_eq _ _ SBM). exact Hh.
  - exact SBM.
  - rewrite AH. exact VIS.
  - exact FR1.
Qed.
End Piece.
