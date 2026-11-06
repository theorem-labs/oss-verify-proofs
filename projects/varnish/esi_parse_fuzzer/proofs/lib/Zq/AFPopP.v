(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Classical_Prop.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Tac Bytes SysStep.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict EvtAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ADepotM.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts ARtS4t2 ARtSb8o AMTac AMallocA AMalmys AMaldga ASecB1 ANodeA7 ANodl61 ATransp ATranspR AFreeRC.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeRK2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeRK2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeRW2 ABudget ACor4x6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require APopG1.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ATransp.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require APopG1 APopG2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require APopG5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require APopG5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require APopG5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require APopP.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require APopP.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtS4t2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSb8o OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMallocA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalmys OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMaldga OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASecB1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ANodeA7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ANodl61 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ATransp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ATranspR OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeRC OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeRK2.AFreeRK OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeRK2.AFreeRK3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeRW2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ABudget OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ACor4x6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APopG1.APopDefs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ATransp.APopCap OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APopG1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APopG2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APopG5.APopG3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APopG5.APopG4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APopG5 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APopP.APopK OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APopP.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeH AFreeH4w ARt2_lib.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AQWf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeB1 AFreeB3 AFreeB1F ACoresk.

Module AFPopK.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Classical_Prop FunctionalExtensionality.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Tac Bytes SysStep.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict Refund Lazyiq4 Fixej5z EvtAcct Divembc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ADepotM AClient.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts ARtS4t2 ARtSb8o AMTac AMallocA AMalmys AMaldga ASecB1 ANodeA7 ANodl61 ATransp ATranspR AFreeRC.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeRK2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeRK2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeRW2 ABudget ACor4x6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require APopG1.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ATransp.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require APopG1 APopG2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require APopG5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require APopG5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require APopG5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require APopP.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require APopP APopCtx.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtS4t2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSb8o OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMallocA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalmys OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMaldga OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASecB1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ANodeA7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ANodl61 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ATransp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ATranspR OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeRC OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeRK2.AFreeRK OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeRK2.AFreeRK3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeRW2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ABudget OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ACor4x6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APopG1.APopDefs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ATransp.APopCap OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APopG1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APopG2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APopG5.APopG3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APopG5.APopG4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APopG5 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APopP.APopK OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APopP OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APopCtx.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.solve_load_guarded | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image].
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Notation wz z := (Z_to_bv 64 z) (only parsing).
#[local] Notation WF := (WF AL_pboth).
Ltac kung_all := unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kShadowOffset, kRegionSize, kSpaceSize, kFreeArrayOffset,
                        kHighShadowMapBeg, kSpaceReserve, kMaxSize, kLowShadowMapBeg, kShadowGapBeg, kHighShadowMapSize,
                        kAuCap, kFreeArraySize, kUserMapSize, kFreeArrayMapSize in *.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition img_off_depot (W : list (Z * Z)) : Prop :=
  (forall a l, 0x10000 <= a -> a + l <= 0x186a88 -> disjoint_from W a l) /\
  (forall a l, 0x5d6aa8 <= a -> a + l <= 0x60a000 -> disjoint_from W a l).

Lemma thread_cells_munch2 {Clg : Ceiling} : forall W (m m' : mem) tp tsd ctx thr,
  thread_cells m tp tsd ctx thr -> munch W m m' -> tp = Z_to_bv 64 0x5e7bd8 -> 0x5e7b28 <= tsd /\ tsd + 8 <= 0x60a000 ->
  img_off_depot W -> disjoint_from W (ctx + 152) 8 ->
  thread_cells m' tp tsd ctx thr.
Proof.
  (intros W m m' tp tsd ctx thr; (first [ intro dR_1; dand6 dR_1 as X1 X2 X3 X4 X5 X6 | intros (X1 & X2 & X3 & X4 & X5 & X6) ]); intros MU TPE TSDL [LO HI] DC).
  assert (TPL : bv_unsigned tp = 0x5e7bd8) by (rewrite TPE; apply unsigned_lit; lia).
  eapply (ro_cells_transport rsegs _ m m') in X1; [| exact MU| apply LO; cbn; lia].
  eapply (ro_cells_transport rsegs _ m m') in X2; [| exact MU| apply LO; cbn; lia].
  eapply (ro_cells_transport rsegs _ m m') in X3; [| exact MU| apply HI; rewrite TPL; cbn; lia].
  eapply (ro_cells_transport rsegs _ m m') in X4; [| exact MU| apply HI; cbn; lia].
  eapply (ro_cells_transport rsegs _ m m') in X5; [| exact MU| exact DC].
  exact (conj X1 (conj X2 (conj X3 (conj X4 (conj X5 X6))))).
Qed.

Lemma poison_consts_munch2 : forall W (m m' : mem),
  poison_consts m -> munch W m m' -> img_off_depot W -> poison_consts m'.
Proof.
  (intros W m m'; (first [ intro dR_2; dand13 dR_2 as X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13 | intros (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13) ]); intros MU [LO _]).
  unfold poison_consts. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits;
    (eapply (ro_cells_transport rsegs _ m m'); [eassumption| exact MU| apply LO; cbn; lia]).
Qed.

Lemma pop_statics_munch2 {Clg : Ceiling} : forall W tsd ctx thr sb (w w' : mem),
  pop_statics tsd ctx thr sb w -> munch W w w' -> 0x5e7b28 <= tsd /\ tsd + 8 <= 0x60a000 ->
  img_off_depot W -> disjoint_from W (ctx + 152) 8 ->
  pop_statics tsd ctx thr sb w'.
Proof.
  (intros W tsd ctx thr sb w w'; (first [ intro dR_3; dand8 dR_3 as P1 P2 P3 P4 P5 P6 P7 P8 | intros (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8) ]); intros MU TS DJ DC). unfold pop_statics.
  split; [exact (poison_consts_munch2 W w w' P1 MU DJ)|].
  split; [apply (thread_cells_munch2 W w w' _ _ _ _ P2 MU); [reflexivity| exact TS| exact DJ| exact DC]|].
  destruct DJ as [LO _].
  OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; (eapply ro_cells_transport; [eassumption| exact MU| apply LO; unfold ANodeA7.CF; cbn; lia]).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition in_fpb (W : list (Z * Z)) (x : Z) : bool := existsb (fun iv => (fst iv <=? x) && (x <? snd iv)) W.

Lemma in_fpb_false : forall W x, in_fpb W x = false <-> outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros x; cbn [in_fpb existsb outside fst snd]; [tauto|].
  rewrite orb_false_iff, andb_false_iff, Z.leb_gt, Z.ltb_ge. fold (in_fpb W x). rewrite IH. split.
  - intros [H1 H2]. split; [lia| exact H2].
  - intros [H1 H2]. split; [lia| exact H2].
Qed.

Lemma fk_outside_app : forall W1 W2 x, outside (W1 ++ W2) x <-> outside W1 x /\ outside W2 x.
Proof. induction W1 as [|[lo hi] W1 IH]; intros W2 x; cbn [app outside]; [tauto|]. rewrite IH. tauto. Qed.

(* [comment removed for export] *)
Definition mhyb (W : list (Z * Z)) (v w : mem) : mem := fun a => if in_fpb W (bv_unsigned a) then v a else w a.

(* [comment removed for export] *)
Lemma mhyb_out : forall W (v w : mem) a, in_fpb W (bv_unsigned a) = false -> mhyb W v w a = w a.
Proof. intros W v w a H. unfold mhyb. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mhyb_munch_entry : forall W Wp (v w : mem), munch (W ++ Wp) v w -> munch Wp v (mhyb W v w).
Proof.
  intros W Wp v w MU x Hx. unfold mhyb. destruct (in_fpb W (bv_unsigned x)) eqn:E; [reflexivity|].
  apply MU. rewrite fk_outside_app. split; [apply in_fpb_false; exact E| exact Hx].
Qed.

Lemma wview_mhyb : forall W (v w : mem) x, wview rsegs (mhyb W v w) x = if in_fpb W (bv_unsigned x) then wview rsegs v x else wview rsegs w x.
Proof. intros W v w x. unfold wview, mhyb. destruct (in_fpb W (bv_unsigned x)); reflexivity. Qed.

(* [comment removed for export] *)
Lemma mhyb_wmono_cur : forall W (v w : mem), wmono rsegs v w -> wmono rsegs (mhyb W v w) w.
Proof. intros W v w WM x Hx. rewrite wview_mhyb in Hx. destruct (in_fpb W (bv_unsigned x)); [exact (WM x Hx)| exact Hx]. Qed.
(* [comment removed for export] *)
Lemma mhyb_clean : forall W (v w : mem) (Hd : word -> bool), (forall a, Hd a = true -> v a = None) -> (forall a, Hd a = true -> w a = None) ->
  forall a, Hd a = true -> mhyb W v w a = None.
Proof. intros W v w Hd Cv Cw a Ha. unfold mhyb. destruct (in_fpb W (bv_unsigned a)); [exact (Cv a Ha)| exact (Cw a Ha)]. Qed.
Lemma mhyb_NN : forall W (v w : mem) a, v a <> None -> (v a <> None -> w a <> None) -> mhyb W v w a <> None.
Proof. intros W v w a Hv Hw. unfold mhyb. destruct (in_fpb W (bv_unsigned a)); [exact Hv| exact (Hw Hv)]. Qed.

(* [comment removed for export] *)
Lemma bytes_at_agree : forall (m m' : mem) a bs, bytes_at rsegs m a bs ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> m' (wz x) = m (wz x)) -> bytes_at rsegs m' a bs.
Proof.
  (intros m m' a bs; (first [ intro dR_4; dand3 dR_4 as Ha Hl H | intros (Ha & Hl & H) ]); intros AG). split; [lia|]. split; [lia|]. intros i Hi. unfold mrd, wa. rewrite AG by lia. apply H. exact Hi.
Qed.
Lemma wr_at_agree : forall (m m' : mem) a n, wr_at rsegs m a n -> (forall x, a <= x < a + n -> m' (wz x) = m (wz x)) -> wr_at rsegs m' a n.
Proof.
  (intros m m' a n; (first [ intro dR_5; dand3 dR_5 as Ha Hl H | intros (Ha & Hl & H) ]); intros AG). split; [lia|]. split; [lia|]. intros i Hi. specialize (H i Hi). unfold wview, wa in *. rewrite AG by lia. exact H.
Qed.
Lemma rw_cells_agree : forall (m m' : mem) a cs, rw_cells rsegs m a cs ->
  (forall x, a <= x < a + Z.of_nat (cells_size cs) -> m' (wz x) = m (wz x)) -> rw_cells rsegs m' a cs.
Proof.
  intros m m' a cs [[Hwf Hb] Hw] AG. split; [split; [exact Hwf|]|].
  - apply (bytes_at_agree m m' a _ Hb). rewrite cells_bytes_length by assumption. exact AG.
  - exact (wr_at_agree m m' a _ Hw AG).
Qed.
Lemma ro_cells_agree : forall (m m' : mem) a cs, ro_cells rsegs m a cs ->
  (forall x, a <= x < a + Z.of_nat (cells_size cs) -> m' (wz x) = m (wz x)) -> ro_cells rsegs m' a cs.
Proof.
  intros m m' a cs [Hwf Hb] AG. split; [exact Hwf|]. apply (bytes_at_agree m m' a _ Hb). rewrite cells_bytes_length by assumption. exact AG.
Qed.
Lemma u32arr_agree : forall (m m' : mem) a ws, u32arr rsegs m a ws ->
  (forall x, a <= x < a + 4 * Z.of_nat (length ws) -> m' (wz x) = m (wz x)) -> u32arr rsegs m' a ws.
Proof.
  intros m m' a ws [Hb Hw] AG. split.
  - apply (bytes_at_agree m m' a _ Hb). rewrite u32s_length, Nat2Z.inj_mul. exact AG.
  - exact (wr_at_agree m m' a _ Hw AG).
Qed.

(* [comment removed for export] *)
Lemma mhyb_off : forall W (v w : mem) a n x, disjoint_from W a n -> a <= x < a + n -> 0 <= x < 2^64 -> mhyb W v w (wz x) = w (wz x).
Proof.
  intros W v w a n x DJ Hx X64. apply mhyb_out. rewrite unsigned_lit by exact X64. apply in_fpb_false. exact (disjoint_outside W a n x DJ Hx).
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rw_C8x2_inj : forall (mm : mem) a x y x' y', 0 <= x < 2^64 -> 0 <= y < 2^64 -> 0 <= x' < 2^64 -> 0 <= y' < 2^64 ->
  rw_cells rsegs mm a [C8 (wz x); C8 (wz y)] -> rw_cells rsegs mm a [C8 (wz x'); C8 (wz y')] -> x = x' /\ y = y'.
Proof.
  intros mm a x y x' y' Hx Hy Hx' Hy' [[_ B] _] [[_ B'] _]. cbn [cells_bytes cbytes] in B, B'. rewrite app_nil_r in B, B'.
  apply bytes_at_app in B as [B0 B1]. apply bytes_at_app in B' as [B0' B1']. rewrite !length_le8 in *.
  pose proof (bytes_at_inj mm a _ _ B0 B0' ltac:(rewrite !length_le8; reflexivity)) as E0.
  pose proof (bytes_at_inj mm _ _ _ B1 B1' ltac:(rewrite !length_le8; reflexivity)) as E1.
  apply AClient.le8_inj in E0. apply AClient.le8_inj in E1.
  apply (f_equal bv_unsigned) in E0. apply (f_equal bv_unsigned) in E1. rewrite !unsigned_lit in E0, E1 by assumption. split; assumption.
Qed.
Lemma rw_C1_snd_inj : forall (mm : mem) a (s0 : byte) x x' rest rest', 0 <= x < 256 -> 0 <= x' < 256 ->
  rw_cells rsegs mm a (C1 s0 :: C1 (Z_to_bv 8 x) :: rest) -> rw_cells rsegs mm a (C1 s0 :: C1 (Z_to_bv 8 x') :: rest') -> x = x'.
Proof.
  intros mm a s0 x x' rest rest' Hx Hx' [[_ B] _] [[_ B'] _]. cbn [cells_bytes cbytes] in B, B'.
  change (?b0 :: ?b1 :: ?r) with ([b0] ++ [b1] ++ r) in B, B'.
  apply bytes_at_app in B as [_ B]. apply bytes_at_app in B as [B _]. apply bytes_at_app in B' as [_ B']. apply bytes_at_app in B' as [B' _].
  pose proof (bytes_at_inj mm _ _ _ B B' eq_refl) as E. apply (f_equal (fun l => nth 0 l (Z_to_bv 8 0))) in E. cbn [nth] in E.
  apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_unsigned in E. unfold bv_wrap, bv_modulus in E. rewrite !Z.mod_small in E by (cbn; lia). exact E.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section FrameF.
Context {Clg : Ceiling}.
  Variables (O Og O' V : Z -> Prop) (hi win : Z) (v vg v' : mem).
  Let window (a : Z) : Prop := hi - win <= a < hi.
  Let errno (a : Z) : Prop := cl_errno LPA <= a < cl_errno LPA + 4.
  Hypothesis G_mono : forall a, O a -> Og a.
  Hypothesis G_new : forall a, 0 <= a < 2^64 -> Og a -> ~ O a -> v (wz a) = None /\ heap_zone LPA a.
  Hypothesis G_agree : forall a, 0 <= a < 2^64 -> ~ Og a -> ~ window a -> vg (wz a) = v (wz a).
  Hypothesis G_pres : forall a, 0 <= a < 2^64 -> ~ in_image LPA a -> v (wz a) <> None -> vg (wz a) <> None.
  (* [comment removed for export] *)
  Hypothesis RF : frame_ok LPA Og O' hi win V nowhere vg v'.

  Lemma frame_grow_free : frame_ok LPA O O' hi win V nowhere v v'.
  Proof.
    destruct RF as (F1 & F2 & F3 & F4 & F5 & F6 & F7). unfold frame_ok.
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits.
    - intros a Ha NO NO' NW NE NV NN. destruct (classic (Og a)) as [Hg|Ng].
      + destruct (G_new a Ha Hg NO) as [VN _]. destruct (F6 a Ha Hg NO') as [X|X]; [exfalso; exact (NN X)|]. rewrite X, VN. reflexivity.
      + rewrite (F1 a Ha Ng NO' NW NE NV NN). exact (G_agree a Ha Ng NW).
    - intros a Ha NI Hv. destruct (classic (Og a)) as [Hg|Ng].
      + destruct (classic (O a)) as [Ho|No]; [left; exact Ho|]. exfalso. destruct (G_new a Ha Hg No) as [VN _]. exact (Hv VN).
      + destruct (F2 a Ha NI (G_pres a Ha NI Hv)) as [X|[X|X]]; [exfalso; exact (Ng X)| right; left; exact X| right; right; exact X].
    - exact F3.
    - intros a Ha [].
    - intros a Ha Ho'. destruct (F5 a Ha Ho') as [Hg|[HV|[VN HZ]]].
      + destruct (classic (O a)) as [Ho|No]; [left; exact Ho|]. right. right. exact (G_new a Ha Hg No).
      + right. left. exact HV.
      + right. right. split; [| exact HZ]. destruct (v (wz a)) eqn:E; [| reflexivity]. exfalso.
        assert (NI : ~ in_image LPA a) by (destruct HZ as [_ NI]; exact NI).
        apply (G_pres a Ha NI); [rewrite E; discriminate| exact VN].
    - intros a Ha Ho NO'. exact (F6 a Ha (G_mono a Ho) NO').
    - exact F7.
  Qed.
End FrameF.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section NodeSpin.
Context {Clg : Ceiling}.
  Variables (A : AState) (m : mem) (md : Model).
  Hypothesis AI : @pa_ainv _ DepotRepL A m md.
  Variables (md1 : Model) (H0 HL0 : hull) (E0 : Z) (beg len : Z).   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variable A' : AState.
  Hypothesis EPL : a_pl A' = a_pl A.
  Hypothesis ESEC : a_sec A' = a_sec A.
  Hypothesis PM1 : pop_mod A' md md1.
  Hypothesis HI1 : MInv H0 HL0 E0 md1.
  Hypothesis RANGE : a_sb A <= beg /\ beg + len <= a_sb A + kSpaceSize + 4096 /\ beg mod 4096 = 0 /\ len mod 4096 = 0 /\ 0 < len.
  Hypothesis BR : E0 + len + hull_bytes HL0 <= p_tlim (a_pl A).   (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (M1 : mem) (T : TSet).

  Let W0 : WF A. Proof. exact (ai_wf _ _ _ _ _ _ _ AI). Qed.
  Let CE : 0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000. Proof. exact alloc_ceiling_val. Qed.
  Let SBF := sb_facts A W0.
  Let BEGW : bv_unsigned (wz beg) = beg. Proof. apply unsigned_lit. pose proof SBF. pose proof RANGE. kung_all. lia. Qed.
  Let LENW : bv_unsigned (wz len) = len. Proof. apply unsigned_lit. pose proof SBF. pose proof RANGE. kung_all. lia. Qed.
  Let PRU : page_round_up_Z len = len.
  Proof.
    unfold page_round_up_Z, page_size. destruct RANGE as (_ & _ & _ & L1 & L0).
    pose proof (Z_div_mod_eq_full len 4096) as E. rewrite L1 in E.
    replace (len + 4096 - 1) with ((len / 4096) * 4096 + 4095) by lia. rewrite Z.div_add_l by lia. replace (4095 / 4096) with 0 by reflexivity. lia.
  Qed.

  Theorem fpop_node :
    (* [comment removed for export] *)
    (let md2 := commit_model (wz 50) (wz beg) (wz len) false md1 in
     MInv H0 HL0 (E0 + len) md2 -> pop_mod A' md md2 -> lazy_free (m_vm_lazy md2) beg (beg + len) ->
     srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz beg) (wz len) (wz 3) (wz 50) (wz (-1)) (wz 0) a6 (wz 222)
                                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz mmap_after_pc) fc None (apply_zeros M1 [(wz beg, wz len)]) (seg_rom rsegs)) md2) T) ->
    srealizes rsegs (mkCfg (MSsvc (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz beg) (wz len) (wz 3) (wz 50) (wz (-1)) (wz 0) a6 (wz 222)
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz mmap_ecall_pc) (wz 222) fc None M1 (seg_rom rsegs)) md1) T.
  Proof.
    intros GRANT. destruct PM1 as (V1 & LED1 & COV1 & TOP1 & AMD1 & HH1). rewrite EPL, ESEC in LED1, COV1.
    match goal with |- srealizes _ (mkCfg ?ms _) _ => set (ms1 := ms) end.
    assert (A0E : ms_gpr ms1 0 = wz beg) by (subst ms1; rewrite ms_gpr_MSsvc; simp_regs; reflexivity).
    assert (A1E : ms_gpr ms1 1 = wz len) by (subst ms1; rewrite ms_gpr_MSsvc; simp_regs; reflexivity).
    assert (PRU1 : page_round_up_Z (bv_unsigned (ms_gpr ms1 1)) = len) by (rewrite A1E, LENW; exact PRU).
    eapply (srz_mmap_fixed_rw_contained_nf rsegs ms1 md1 (wz 222) (wz 50) T HH1 eq_refl eq_refl).
    - unfold mmap_fixed_args. subst ms1. rewrite !ms_gpr_MSsvc. simp_regs. split; [| OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity].
      intros E. apply (f_equal bv_unsigned) in E. rewrite LENW, unsigned_lit in E by lia. destruct RANGE as (_ & _ & _ & _ & L0). lia.
    - exact fixed_rw_shape_plain.
    - rewrite PRU1, A0E. eapply (c_gate A m md AI); eassumption.
    - unfold fixed_contained. rewrite PRU1, A0E. eapply (c_contained A m md AI); eassumption.
    - rewrite PRU1, A0E. eapply (c_budget A m md AI); eassumption.
    - rewrite !PRU1, !A0E. subst ms1.
      rewrite advance_apply_MSsvc, mkR_set_a0, lit_add_lit. change (mmap_ecall_pc + 4) with mmap_after_pc.
      cbn [apply_writes apply_unmaps].
      apply GRANT.
      + eapply (c_minv A m md AI); eassumption.
      + unfold pop_mod. rewrite EPL, ESEC. split; [eapply c_vm5; eassumption|]. split; [eapply (c_ledger A m md AI); eassumption|].
        split; [eapply (c_cover A m md AI); eassumption|]. split; [eapply (c_ceil A m md AI); eassumption|].
        split; [eapply c_amd; eassumption| eapply c_halted; eassumption].
      + eapply (c_lzfree_new A m md AI); eassumption.
  Qed.
End NodeSpin.
End AFPopK.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j.AFreeLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeH OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeH4w OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt2_lib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AQWf.AQOps OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeB1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeB3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeB1F OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ACoresk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFPopP.AFPopK.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac hot2_mid := match goal with H : context [Z.modulo _ _] |- _ => idtac | H : context [Z.div _ _] |- _ => idtac end;
  (repeat match goal with H : context [Z.modulo _ _] |- _ => clear H | H : context [Z.div _ _] |- _ => clear H end); Zify.zify; xlia zchecker.
Local Ltac lia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; Zify.zify; xlia zchecker | hot2_mid | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Notation wz z := (Z_to_bv 64 z) (only parsing).
#[local] Notation WF := (WF AL_pboth).
Ltac kung_all := unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kShadowOffset, kRegionSize, kSpaceSize, kFreeArrayOffset,
                        kHighShadowMapBeg, kSpaceReserve, kMaxSize, kLowShadowMapBeg, kShadowGapBeg, kHighShadowMapSize,
                        kAuCap, kFreeArraySize, kUserMapSize, kFreeArrayMapSize in *.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fpop_Wfo (thr p r8 n0d f0d : Z) : list (Z * Z) :=
  [(p + -16, p + -12); (p, p + 8); (thr + 2824, thr + 2840); (0x186a88, 0x5d6aa8); (n0d, n0d + 0x100000); (f0d, f0d + 0x800000); (sh p, sh p + r8)].

(* [comment removed for export] *)
Definition fpop_Wq (slo shi thr E R fa nf nc rb mu ums mfa fam : Z) (ci : bool) : list (Z * Z) :=
  [(slo, shi); (R, R + 8); (R + 16, R + 40); (R + 48, R + 56); (R + 68, R + 69);
   (fa + 4 * nf, fa + 4 * (nf + nc)); (thr + 2872, thr + 2888); (E, E + 80);
   (rb + mu, rb + mu + ums); (sh (rb + mu), sh (rb + mu) + ums / 8);
   (fa + mfa, fa + mfa + fam); (sh (fa + mfa), sh (fa + mfa) + fam / 8);
   (thr + 2792, thr + 2800); ((if ci then thr + 2768 else thr + 288), thr + 2768)].

Lemma fpop_Wq_sub_W : forall slo shi slo' shi' thr E R fa nf nc rb mu ums mfa fam ci, slo' <= slo -> shi <= shi' ->
  sub_fp (fpop_Wq slo shi thr E R fa nf nc rb mu ums mfa fam ci) (pop_W slo' shi' thr E R fa nf nc rb mu ums mfa fam ci).
Proof.
  intros. unfold sub_fp, fpop_Wq, pop_W. cbn [outside]. intros x Hx. destruct ci;
  repeat match goal with H : _ /\ _ |- _ => destruct H end; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try exact I; lia.
Qed.
Lemma fpop_Wq_mono : forall slo shi thr E R fa nf nc rb mu ums mfa fam ci nc' ums' fam',
  0 <= nc <= nc' -> 0 <= ums <= ums' -> 0 <= fam <= fam' ->
  sub_fp (fpop_Wq slo shi thr E R fa nf nc rb mu ums mfa fam ci) (fpop_Wq slo shi thr E R fa nf nc' rb mu ums' mfa fam' ci).
Proof.
  intros. unfold sub_fp, fpop_Wq. cbn [outside]. intros x Hx.
  pose proof (Z.div_le_mono ums ums' 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_mono fam fam' 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_pos ums 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_pos fam 8 ltac:(lia) ltac:(lia)).
  repeat match goal with H : _ /\ _ |- _ => destruct H end. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try lia.
Qed.
Lemma sub_fp_app_l : forall W1 W2, sub_fp W1 (W1 ++ W2).
Proof. intros W1 W2 x Hx. rewrite fk_outside_app in Hx. exact (proj1 Hx). Qed.
(* [comment removed for export] *)
Lemma sub_fp_app2 : forall W1 W1' W2, sub_fp W1 W1' -> sub_fp (W1 ++ W2) (W1' ++ W2).
Proof. intros W1 W1' W2 S x Hx. rewrite fk_outside_app in *. destruct Hx as [H1 H2]. split; [exact (S x H1)| exact H2]. Qed.
Lemma sub_fp_trans : forall W1 W2 W3, sub_fp W1 W2 -> sub_fp W2 W3 -> sub_fp W1 W3.
Proof. intros W1 W2 W3 S1 S2 x Hx. exact (S1 x (S2 x Hx)). Qed.

Section FPkg.
Context {Clg : Ceiling}.
  Variables (rac spd gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m : mem) (md : Model) (A : AState) (p n0 stkobj lo hi : Z) (key : list Z).
  Hypothesis PRE : dealloc_core_pre rac spd (cl_tp LPA) m md A p n0 stkobj lo hi key.
  Hypothesis HL : as_live A p = Some n0.
  Hypothesis NQ : n0 <= 2^28.
  Hypothesis EMP : pk_chunks (a_cache A 24) = [].
  Hypothesis SHORT : Z.of_nat (length (rg_free (a_reg A 24))) < refill_count 24.
  #[warnings="-notation-for-abbreviation"] Local Notation v := (aview_of (pa_hull A) m).
  #[warnings="-notation-for-abbreviation"] Local Notation usp := (bv_unsigned spd).
  #[warnings="-notation-for-abbreviation"] Local Notation sa := (bv_unsigned spd + -80 + 112).
  #[warnings="-notation-for-abbreviation"] Local Notation spaw := (Z_to_bv 64 (bv_unsigned spd + -80 + 112)).
  #[warnings="-notation-for-abbreviation"] Local Notation tp := (cl_tp LPA).
  #[warnings="-notation-for-abbreviation"] Local Notation thr := (p_thr (a_pl A)).
  #[warnings="-notation-for-abbreviation"] Local Notation ctx := (p_ctx (a_pl A)).
  #[warnings="-notation-for-abbreviation"] Local Notation sb := (a_sb A).
  #[warnings="-notation-for-abbreviation"] Local Notation ri := (a_ri A).
  #[warnings="-notation-for-abbreviation"] Local Notation n0d := (p_nodes0 (a_pl A)).
  #[warnings="-notation-for-abbreviation"] Local Notation f0d := (p_frames0 (a_pl A)).
  #[warnings="-notation-for-abbreviation"] Local Notation r8 := ((n0 + 7) / 8).
  #[warnings="-notation-for-abbreviation"] Local Notation R := (a_ri A + 128 * 24).
  #[warnings="-notation-for-abbreviation"] Local Notation C := (p_thr (a_pl A) + 208).
  #[warnings="-notation-for-abbreviation"] Local Notation E := (p_thr (a_pl A) + 208 + 80 * 24).
  #[warnings="-notation-for-abbreviation"] Local Notation uG := (bv_unsigned spd + -80 + 112 + -128 + -48 + -32 + -128).
  #[warnings="-notation-for-abbreviation"] Local Notation rb := (region_beg (a_sb A) 24).
  #[warnings="-notation-for-abbreviation"] Local Notation rbs := (a_sb A + 24 * 4294967296).
  #[warnings="-notation-for-abbreviation"] Local Notation fa := (region_beg (a_sb A) 24 + kFreeArrayOffset).
  #[warnings="-notation-for-abbreviation"] Local Notation mu := (rg_mapped_user (a_reg A 24)).
  #[warnings="-notation-for-abbreviation"] Local Notation au := (rg_allocated_user (a_reg A 24)).
  #[warnings="-notation-for-abbreviation"] Local Notation mfa := (rg_mapped_fa (a_reg A 24)).
  #[warnings="-notation-for-abbreviation"] Local Notation nf := (Z.of_nat (length (rg_free (a_reg A 24)))).
  #[warnings="-notation-for-abbreviation"] Local Notation kk := (refill_count 24).
  #[warnings="-notation-for-abbreviation"] Local Notation size := (class_size 24).
  #[warnings="-notation-for-abbreviation"] Local Notation U := (pop_ums A 24).
  #[warnings="-notation-for-abbreviation"] Local Notation N := (pop_nc A 24).
  #[warnings="-notation-for-abbreviation"] Local Notation Fm := (pop_fam A 24).
  #[warnings="-notation-for-abbreviation"] Local Notation D' := (fst (depot_putC (a_depot A) key)).
  #[warnings="-notation-for-abbreviation"] Local Notation fid := (snd (depot_putC (a_depot A) key)).

  Let AI : @pa_ainv _ DepotRepL A m md. Proof. exact (proj1 PRE). Qed.
  Let W0 : WF A. Proof. exact (ai_wf _ _ _ _ _ _ _ AI). Qed.
  Let CR : 1 <= 24 <= 30. Proof. lia. Qed.
  Let N7R : 1 <= 7000 <= kMaxPrimaryUser. Proof. unfold kMaxPrimaryUser. lia. Qed.
  Let CE : 0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000. Proof. exact alloc_ceiling_val. Qed.
  Let MIv : mem_inv rsegs v. Proof. exact (proj1 (proj2 PRE)). Qed.
  (* [comment removed for export] *)
  Let PREF : alloc_ceiling <= lo /\ lo <= usp - 4096 /\ usp <= hi /\ hi <= 2^47 /\ usp mod 16 = 0 /\ bv_unsigned rac mod 2 = 0 /\
             stk rsegs v lo usp /\ mapped v usp (hi - usp) /\ usp <= stkobj /\ stkobj + 2064 <= hi.
  Proof.
    destruct PRE as (_ & _ & _ & _ & _ & CLO & LOSA & SAHI & HI47 & SPA & RAC2 & ST & SM & SOLO & SOHI & _). cbn [cl_segs LPA] in ST.
    exact (conj CLO (conj LOSA (conj SAHI (conj HI47 (conj SPA (conj RAC2 (conj ST (conj SM (conj SOLO SOHI))))))))).
  Qed.
  Let SAE : bv_unsigned spaw = sa.
  Proof. destruct PREF as (_ & _ & SAHI & HI47 & _). pose proof (zr_word spd) as X. unfold inr64 in X. apply unsigned_lit. lia. Qed.
  Let CEIL : alloc_ceiling <= sa - 1024. Proof. destruct PREF as (CLO & LOSA & _). lia. Qed.
  Let CEILw : alloc_ceiling <= bv_unsigned spaw - 1024. Proof. rewrite SAE. exact CEIL. Qed.
  Let EMP7 : pk_chunks (a_cache A (class_of 7000)) = []. Proof. rewrite class_of_7000. exact EMP. Qed.
  Let SHORT7 : Z.of_nat (length (rg_free (a_reg A (class_of 7000)))) < refill_count (class_of 7000). Proof. rewrite class_of_7000. exact SHORT. Qed.
  Let KS : Z.shiftr (max_count 24) 1 = kk. Proof. exact (proj1 (proj2 (proj2 (ar_k A 24 CR)))). Qed.


  (* [comment removed for export] *)
  Definition fk_Wi (ums fam nc : Z) : list (Z * Z) := fpop_Wq (sa - 1024) (sa - 32) thr E R fa nf nc rb mu ums mfa fam (a_cache_inited A).
  Definition fk_Wfo : list (Z * Z) := fpop_Wfo thr p r8 n0d f0d.

  (* [comment removed for export] *)
  Definition fcells (wH : mem) : Prop :=
    exists (b1 fr fd nx bsz : Z) (statv : word),
      (0 <= b1 < 256 /\ Z.land b1 3 = 1 /\ 0 <= fr < 2^64 /\ 0 <= fd < 2^64) /\
      rw_cells rsegs v (p + -16) [C1 (Z_to_bv 8 CHUNK_ALLOCATED); C1 (Z_to_bv 8 b1); C2 (wz (size_hi n0)); C4 (wz n0)] /\
      rw_cells rsegs v (thr + 2824) [C8 (wz fr); C8 (wz fd)] /\
      rw_cells rsegs wH (thr + 2824) [C8 (wz (fr + 1)); C8 (wz (n0 + fd))] /\
      rw_cells rsegs wH (p + -16) [C1 (Z_to_bv 8 CHUNK_QUARANTINE); C1 (Z_to_bv 8 b1); C2 (wz (size_hi n0)); C4 (wz n0)] /\
      rw_cells rsegs wH p [C8 (wz fid)] /\
      bytes_at rsegs wH (sh p) (repeat (Z_to_bv 8 0xfd) (Z.to_nat r8)) /\
      depot_repL AL_pboth rsegs D' n0d f0d wH /\
      rw_cells rsegs wH (thr + 80) [C8 (wz (Z.of_nat (length (a_qthread A)))); C8 (wz (qc_first A (a_qthread A))); C8 (wz (qc_last A (a_qthread A))); C8 (wz (q_bytes (a_qthread A)))] /\
      (a_qthread A <> [] -> rw_cells rsegs wH (qc_last A (a_qthread A)) [C8 (wz nx); C8 (wz bsz); C8 (wz 1021)]) /\
      rw_cells rsegs wH (thr + 208 + 2576) [C8 statv].

  (* [comment removed for export] *)
  Definition carryF (junk0 pad scr : list byte) (ksc : list word) (ums fam nc : Z) (w : mem) : Prop :=
    munch (fk_Wi ums fam nc ++ fk_Wfo) v w /\ wmono rsegs v w /\ mem_inv rsegs w /\
    rw_cells rsegs w (usp + -80) [C8 (wz (thr + 208)); C8 (wz stkobj); C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 rac] /\
    rw_cells rsegs w (usp + -80 + -64) (enqueue_frame junk0 (wz (p + -16)) (wz (thr + 208)) (wz stkobj) (wz n0) (wz (thr + 80)) (wz QINST) (wz 0x3b60c)) /\
    rw_cells rsegs w (usp + -80 + -64 + -32) (refill_frame pad (wz (thr + 208)) (wz E) (wz enqueue_ret)) /\
    rw_cells rsegs w uG (gfa_frame scr s11 s10 s9 s8 s7 (wz (2^20)) (wz n0) (wz stkobj) (wz (thr + 80)) (wz (p + -16)) (wz 1) (wz E) (wz refill_ret)) /\
    rw_cells rsegs w R [C8 (wz kMutexWriter)] /\
    length ksc = 16%nat /\
    rw_cells rsegs w E [C4 (wz 0); C4 (wz 2); C8 (wz 8192); CB 64 (u32s ksc)] /\
    (a_cache_inited A = false -> forall i, 1 <= i <= 31 -> i <> 24 ->
       exists ks, length ks = 16%nat /\ rw_cells rsegs w (thr + 208 + 80 * i) [C4 (wz 0); C4 (wz (max_count i)); C8 (wz (class_size i)); CB 64 (u32s ks)]) /\
    (exists wH : mem, munch (fk_Wi ums fam nc) wH w /\ wmono rsegs wH w /\ fcells wH).

  (* [comment removed for export] *)
  Definition regwF (nfv mfav auv muv : Z) (w : mem) : Prop :=
    rw_cells rsegs w (R + 16) [C8 (wz nfv)] /\ rw_cells rsegs w (R + 24) [C8 (wz mfav)] /\
    rw_cells rsegs w (R + 32) [C8 (wz auv)] /\ rw_cells rsegs w (R + 40) [C8 (wz 0)] /\ rw_cells rsegs w (R + 48) [C8 (wz muv)] /\
    rw_cells rsegs w (R + 56) [C8 (wz 0)] /\ rw_cells rsegs w (R + 68) [C1 (Z_to_bv 8 0)].

  (* [comment removed for export] *)
  Lemma fk_UMS : 0 <= U /\ U mod kUserMapSize = 0 /\ mu + U < au + 9 * class_size 24 + kUserMapSize /\ au <= class_size 24 * (Z.of_nat (length (a_paid A 24)) + 7) + class_slack 24.   (* [comment removed for export] *)
  Proof. exact (proj1 (ar_ums A 24 W0 CR EMP SHORT)). Qed.
  Lemma fk_FAM : 0 <= Fm /\ Fm mod kFreeArrayMapSize = 0 /\ mfa + Fm <= 4 * (au / class_size 24) + kFreeArrayMapSize /\ mfa + Fm <= kFreeArraySize.   (* [comment removed for export] *)
  Proof. exact (proj1 (ar_fam A 24 W0 CR EMP SHORT)). Qed.
  Lemma fk_NC : 0 <= N /\ au + N * class_size 24 <= mu + U /\ 4 * (nf + N) <= mfa + Fm.
  Proof. (first [ pose proof ((ar_nc A 24 W0 CR EMP SHORT)) as dR_1; dand3 dR_1 as N1 N2 _ | pose proof (ar_nc A 24 W0 CR EMP SHORT) as (N1 & N2 & _) ]). (first [ pose proof ((ar_fam A 24 W0 CR EMP SHORT)) as dR_2; dand3 dR_2 as _ F2 _ | pose proof (ar_fam A 24 W0 CR EMP SHORT) as (_ & F2 & _) ]). OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption. Qed.
  Lemma fk_POS : mu + U = 0 -> Fm = 0 /\ N = 0.
  Proof.
    intros Z0. exfalso. (first [ pose proof ((ar_ums A 24 W0 CR EMP SHORT)) as dR_3; dand3 dR_3 as _ U4 _ | pose proof (ar_ums A 24 W0 CR EMP SHORT) as (_ & U4 & _) ]). (first [ pose proof ((ar_ks A 24 W0 CR SHORT)) as dR_4; dand4 dR_4 as _ _ K3 _ | pose proof (ar_ks A 24 W0 CR SHORT) as (_ & _ & K3 & _) ]).
    pose proof (ar_reg A 24 W0 CR) as ((R1 & _) & _). lia.
  Qed.
  Definition fk_GEO := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APopG5.APopG3.GEO A m md 24 U Fm N spaw AI CR CEILw fk_UMS fk_FAM fk_NC.
  Definition fk_SHG := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APopG5.APopG3.SHG A m md 24 U Fm N spaw AI CR CEILw fk_UMS fk_FAM fk_NC fk_POS.

  Lemma fk_Wi_mono : forall ums fam nc ums' fam' nc', 0 <= ums <= ums' -> 0 <= fam <= fam' -> 0 <= nc <= nc' -> sub_fp (fk_Wi ums fam nc) (fk_Wi ums' fam' nc').
  Proof. intros ums fam nc ums' fam' nc' H1 H2 H3. unfold fk_Wi. apply fpop_Wq_mono; assumption. Qed.
  Lemma fk_Wi_le : forall ums fam nc, 0 <= ums <= U -> 0 <= fam <= Fm -> 0 <= nc <= N -> sub_fp (fk_Wi ums fam nc) (fk_Wi U Fm N).
  Proof. intros ums fam nc H1 H2 H3. unfold fk_Wi. apply fpop_Wq_mono; assumption. Qed.

  (* [comment removed for export] *)
  Lemma fk_lin :
    alloc_ceiling <= sa - 1024 /\ sa < 2^64 /\
    (4096 <= thr /\ thr + 4096 <= alloc_ceiling /\ (thr + 4096 <= 65536 \/ 6332416 <= thr) /\ (thr + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= thr)) /\
    (0x10007fff8000 <= sb /\ sb + 137438953472 + 4096 <= alloc_ceiling /\ ri = sb + 137438953472 /\ rb = sb + 24 * 4294967296 /\ 1 <= 24 <= 30) /\
    (0 <= au <= mu /\ 0 <= U /\ mu + U <= 3750000000 /\ 0 <= mfa /\ 0 <= Fm /\ mfa + Fm <= 536870912 /\ 0 <= nf /\ 0 <= N /\ 4 * nf <= mfa /\ 4 * (nf + N) <= mfa + Fm) /\
    (0x02008fff7000 <= sh (rb + mu) /\ 0 <= U / 8 /\ sh (rb + mu) + U / 8 <= sh (fa + mfa) /\ 0 <= Fm / 8 /\ sh (fa + mfa) + Fm / 8 <= 0x10007fff8000).
  Proof.
    pose proof (pk_lin spaw m md A 7000 AI N7R EMP7 SHORT7 CEILw) as L. rewrite SAE in L. rewrite class_of_7000 in L. exact L.
  Qed.

  (* [comment removed for export] *)
  Lemma regwF_step : forall nfv mfav auv muv W (w w' : mem), regwF nfv mfav auv muv w -> munch W w w' -> wmono rsegs w w' ->
    disjoint_from W (R + 16) 64 -> regwF nfv mfav auv muv w'.
  Proof.
    (intros nfv mfav auv muv W w w'; (first [ intro dR_28; dand7 dR_28 as R1 R2 R3 R4 R5 R6 R7 | intros (R1 & R2 & R3 & R4 & R5 & R6 & R7) ]); intros MU WM DJ). unfold regwF.
    split; [apply (rw_xf W w w' _ _ _ _ R1 MU WM DJ); [lia| cbn; lia]|].
    split; [apply (rw_xf W w w' _ _ _ _ R2 MU WM DJ); [lia| cbn; lia]|].
    split; [apply (rw_xf W w w' _ _ _ _ R3 MU WM DJ); [lia| cbn; lia]|].
    split; [apply (rw_xf W w w' _ _ _ _ R4 MU WM DJ); [lia| cbn; lia]|].
    split; [apply (rw_xf W w w' _ _ _ _ R5 MU WM DJ); [lia| cbn; lia]|].
    split; [apply (rw_xf W w w' _ _ _ _ R6 MU WM DJ); [lia| cbn; lia]|].
    apply (rw_xf W w w' _ _ _ _ R7 MU WM DJ); [lia| cbn; lia].
  Qed.
  (* [comment removed for export] *)
  Lemma fk_region :
    rw_cells rsegs v R [C8 (wz 0)] /\ rw_cells rsegs v (R + 16) [C8 (wz nf)] /\ rw_cells rsegs v (R + 24) [C8 (wz mfa)] /\
    rw_cells rsegs v (R + 32) [C8 (wz au)] /\ rw_cells rsegs v (R + 40) [C8 (wz 0)] /\ rw_cells rsegs v (R + 48) [C8 (wz mu)] /\
    rw_cells rsegs v (R + 56) [C8 (wz 0)] /\ rw_cells rsegs v (R + 68) [C1 (Z_to_bv 8 0)] /\
    mapped v ri 4096 /\ mapped v fa mfa /\ mapped v rb mu.
  Proof. pose proof (pk_region A m md 7000 AI N7R) as X. rewrite class_of_7000 in X. exact X. Qed.
  Lemma regwF_entry : regwF nf mfa au mu v.
  Proof.
    (first [ pose proof (fk_region) as dR_5; dand9 dR_5 as _ R1 R2 R3 R4 R5 R6 R7 _ | pose proof fk_region as (_ & R1 & R2 & R3 & R4 & R5 & R6 & R7 & _) ]). unfold regwF.
    split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R5|]. split; [exact R6|]. exact R7.
  Qed.

  (* [comment removed for export] *)
  Lemma carryF_step : forall junk0 pad scr ksc ums fam nc ums' fam' nc' W (w w' : mem),
    carryF junk0 pad scr ksc ums fam nc w -> munch W w w' -> wmono rsegs w w' -> mem_inv rsegs w' ->
    sub_fp (fk_Wi ums fam nc) (fk_Wi ums' fam' nc') -> sub_fp W (fk_Wi ums' fam' nc') ->
    disjoint_from W (sa - 336) 336 -> disjoint_from W R 8 -> disjoint_from W (thr + 288) 2480 ->
    carryF junk0 pad scr ksc ums' fam' nc' w'.
  Proof.
    (intros junk0 pad scr ksc ums fam nc ums' fam' nc' W w w'; (first [ intro dR_29; dand12 dR_29 as MU0 WM0 _ FA FC FR FG MX LK LN LNS (wH & MUH & WMH & FCH) | intros (MU0 & WM0 & _ & FA & FC & FR & FG & MX & LK & LN & LNS & (wH & MUH & WMH & FCH)) ]); intros MU WM MI S1 S2 DF DR DL).
    unfold carryF.
    split; [exact (munch_trans _ _ _ _ (munch_weaken _ _ _ _ (sub_fp_app2 _ _ _ S1) MU0) (munch_weaken _ _ _ _ (sub_fp_trans _ _ _ S2 (sub_fp_app_l _ _)) MU))|].
    split; [exact (wmono_trans _ _ _ _ WM0 WM)|]. split; [exact MI|].
    split; [apply (rw_xf W w w' _ _ _ _ FA MU WM DF); [lia| cbn; lia]|].
    split; [apply (rw_xf W w w' _ _ _ _ FC MU WM DF); [lia| cbn; lia]|].
    split; [apply (rw_xf W w w' _ _ _ _ FR MU WM DF); [lia| cbn; lia]|].
    split; [apply (rw_xf W w w' _ _ _ _ FG MU WM DF); [lia| cbn; lia]|].
    split; [apply (rw_xf W w w' _ _ _ _ MX MU WM DR); [lia| cbn; lia]|].
    split; [exact LK|].
    split; [apply (rw_xf W w w' _ _ _ _ LN MU WM DL); [lia| cbn; lia]|].
    split.
    - intros CI i Hi NE. (first [ pose proof ((LNS CI i Hi NE)) as dR_6; dex1 dR_6 as ks; destruct dR_6 as [LKi RWi] | pose proof ((LNS CI i Hi NE)) as dR_6; dand3 dR_6 as ks LKi RWi | destruct (LNS CI i Hi NE) as (ks & LKi & RWi) ]). exists ks. split; [exact LKi|].
      apply (rw_xf W w w' _ _ _ _ RWi MU WM DL); [lia| cbn; lia].
    - exists wH. split; [exact (munch_trans _ _ _ _ (munch_weaken _ _ _ _ S1 MUH) (munch_weaken _ _ _ _ S2 MU))|]. split; [exact (wmono_trans _ _ _ _ WMH WM)| exact FCH].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma fk_plin :
    (0x60a000 <= p + -16 /\ p + 8 * r8 <= alloc_ceiling /\ 1 <= r8 /\ (p + 8 * r8 <= 0x7fff8000 \/ 0x10007fff8000 <= p + -16)) /\
    ((p + 8 * r8 <= rb + au \/ rb + 4294967296 <= p + -16) /\ (p + 8 * r8 <= ri \/ ri + 4096 <= p + -16) /\
     (p + 8 * r8 <= thr \/ thr + 4096 <= p + -16) /\ (p + 8 * r8 <= ctx \/ ctx + 0x10000 <= p + -16)) /\
    (0x7fff8200 <= sh p /\ sh p + r8 <= 0x10007fff8000 /\ (sh p + r8 <= sh (rb + mu) \/ sh (fa + mfa) + Fm / 8 <= sh p)) /\
    ((4096 <= n0d /\ n0d + 0x100000 <= alloc_ceiling /\ (n0d + 0x100000 <= 0x10000 \/ 0x60a000 <= n0d) /\ (n0d + 0x100000 <= 0x7fff8000 \/ 0x10007fff8000 <= n0d)) /\
     (n0d + 0x100000 <= thr \/ thr + 4096 <= n0d) /\ (n0d + 0x100000 <= sb \/ sb + 137438953472 + 4096 <= n0d) /\ (n0d + 0x100000 <= ctx \/ ctx + 0x10000 <= n0d)) /\
    ((4096 <= f0d /\ f0d + 0x800000 <= alloc_ceiling /\ (f0d + 0x800000 <= 0x10000 \/ 0x60a000 <= f0d) /\ (f0d + 0x800000 <= 0x7fff8000 \/ 0x10007fff8000 <= f0d)) /\
     (f0d + 0x800000 <= thr \/ thr + 4096 <= f0d) /\ (f0d + 0x800000 <= sb \/ sb + 137438953472 + 4096 <= f0d) /\ (f0d + 0x800000 <= ctx \/ ctx + 0x10000 <= f0d)) /\
    ((4096 <= ctx /\ ctx + 0x10000 <= alloc_ceiling /\ (ctx + 0x10000 <= 0x7fff8000 \/ 0x10007fff8000 <= ctx)) /\ (ctx + 0x10000 <= thr \/ thr + 4096 <= ctx) /\
     (ctx + 0x10000 <= sb \/ sb + 137438953472 + 4096 <= ctx) /\ 0x60a000 <= ctx).
  Proof.
    (first [ pose proof ((free_li A p n0 HL)) as dR_7; dex1 dR_7 as li; destruct dR_7 as [LU LN] | pose proof ((free_li A p n0 HL)) as dR_7; dand3 dR_7 as li LU LN | destruct (free_li A p n0 HL) as (li & LU & LN) ]).
    pose proof (conj W0 (ai_repr _ _ _ _ _ _ _ AI) : WF A /\ @arepr _ DepotRepL LPA AL_pboth [] A v) as AR.
    (first [ pose proof ((AFreeB3.GEO A v p n0 li spd AR LU LN)) as dR_8; dand17 dR_8 as PM CL1 L1 L2 CL2 NR R8' _ T1 T2 N1 N2 F1 F2 S1 S2 _ | pose proof (AFreeB3.GEO A v p n0 li spd AR LU LN) as (PM & CL1 & L1 & L2 & CL2 & NR & R8' & _ & T1 & T2 & N1 & N2 & F1 & F2 & S1 & S2 & _) ]).
    (first [ pose proof ((AFreeB3.GEOP A v p n0 li AR LU LN)) as dR_9; dand4 dR_9 as Gc Gt Gn Gf | pose proof (AFreeB3.GEOP A v p n0 li AR LU LN) as (Gc & Gt & Gn & Gf) ]). apply aobj_facts in Gc. apply aobj_facts in Gn. apply aobj_facts in Gf.
    pose proof (AFreeB3.GEOS A v p n0 li spd AR LU LN) as Gs.
    pose proof (free_sep A m md p n0 AI HL) as SEPp. cbv zeta in SEPp. (first [ dand4 SEPp as SEP_pc SEP_pt SEP_pn SEP_pf | destruct SEPp as (SEP_pc & SEP_pt & SEP_pn & SEP_pf) ]).
    (first [ pose proof ((hit_sep A m md AI)) as dR_11; dand10 dR_11 as SEP_thr SEP_ctx SEP_tc SEP_n0 SEP_f0 SEP_n0t SEP_f0t SEP_n0c SEP_f0c _ | pose proof (hit_sep A m md AI) as (SEP_thr & SEP_ctx & SEP_tc & SEP_n0 & SEP_f0 & SEP_n0t & SEP_f0t & SEP_n0c & SEP_f0c & _) ]).
    (first [ pose proof ((hit_place A m md AI)) as dR_12; dand6 dR_12 as _ _ _ CT1 CT2 _ | pose proof (hit_place A m md AI) as (_ & _ & _ & CT1 & CT2 & _) ]). apply aobj_facts in CT1.
    (first [ pose proof ((f24_sep A m md AI)) as dR_13; dand8 dR_13 as _ _ SEP_rc SEP_rn SEP_rf _ _ _ | pose proof (f24_sep A m md AI) as (_ & _ & SEP_rc & SEP_rn & SEP_rf & _ & _ & _) ]).
    pose proof (f24_ri A m md AI) as (RIE & _).
    (first [ pose proof (fk_lin) as dR_14; dand6 dR_14 as L1' L2' (Lt1 & Lt2 & Lt3 & Lt4) (B1 & B2 & B3 & B4 & B5) (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10) (H1 & H2 & H3 & H4 & H5) | pose proof fk_lin as (L1' & L2' & (Lt1 & Lt2 & Lt3 & Lt4) & (B1 & B2 & B3 & B4 & B5) & (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10) & (H1 & H2 & H3 & H4 & H5)) ]).
    pose proof (AFreeB3.KN A v p n0 li AR LU LN) as KNp. pose proof (ATransp.known_carved A v AR _ _ KNp) as CVp.
    (* [comment removed for export] *)
    assert (PG : (p + 8 * r8 <= rb + au \/ rb + 4294967296 <= p + -16) /\ (p + 8 * r8 <= ri \/ ri + 4096 <= p + -16)).
    { rewrite <- LN in *. destruct (li_chunk li) as [[c' k']|s] eqn:ECH.
      - pose proof CVp as [Hc' _]. pose proof (ATransp.carved_prim_where A v AR c' k' CVp) as W'. cbn [chunk_lo chunk_hi alloc_beg] in L1, L2.
        unfold region_beg in *. kung_all.
        destruct (Z.lt_trichotomy c' 24) as [LT|[EQ|GT]].
        + clear - L1 L2 W' LT B3 Hc' Q1. split; left; lia.
        + subst c'. clear - L1 L2 W' B3 Q1. split; left; lia.
        + clear - L1 L2 W' GT B3 Hc' Q1. split; [right| left]; lia.
      - unfold carved in CVp. pose proof (ATransp.sec_apart_b6 A v AR s CVp) as D6. destruct s as [mb n1]. cbn [chunk_lo chunk_hi cs_map cs_n] in L1, L2, D6.
        (first [ pose proof ((sb_facts A W0)) as dR_15; dand5 dR_15 as _ SBA HB6 RSB SCE | pose proof (sb_facts A W0) as (_ & SBA & HB6 & RSB & SCE) ]). unfold region_beg, a_b6, a_sb in *. kung_all.
        clear - L1 L2 D6 SBA HB6 RSB SCE B3 Q1 Q3. split; lia. }
    destruct PG as [PG1 PG2].
    assert (SHP : sh p + r8 <= sh (rb + mu) \/ sh (fa + mfa) + Fm / 8 <= sh p).
    { assert (E1 : sh (p + 8 * r8) = sh p + r8) by (unfold sh; rewrite (Z.mul_comm 8 r8), Z.div_add by lia; lia).
      destruct PG1 as [LE|GE].
      - left. rewrite <- E1. unfold sh. apply Z.add_le_mono_r. apply Z.div_le_mono; [lia| clear - LE Q1; lia].
      - right. assert (X : sh (fa + mfa) + Fm / 8 <= sh (rb + 4294967296)).
        { unfold sh, kFreeArrayOffset in *. pose proof (Z_div_mod_eq_full (rb + 3758096384 + mfa) 8) as X1. pose proof (Z.mod_pos_bound (rb + 3758096384 + mfa) 8 ltac:(lia)) as X2.
          pose proof (Z_div_mod_eq_full Fm 8) as X3. pose proof (Z.mod_pos_bound Fm 8 ltac:(lia)) as X4.
          pose proof (Z_div_mod_eq_full (rb + 4294967296) 8) as X5. pose proof (Z.mod_pos_bound (rb + 4294967296) 8 ltac:(lia)) as X6. clear - X1 X2 X3 X4 X5 X6 Q6 Q4 Q5. lia. }
        assert (Y : sh (rb + 4294967296) <= sh p) by (unfold sh; apply Z.add_le_mono_r; apply Z.div_le_mono; [lia| clear - GE; lia]). clear - X Y. lia. }
    unfold AMallocA.apart in *. unfold kDepotNodesBlock, kStackStoreBlockBytes, kLowShadowMapBeg, kHighShadowMapBeg, kHighMemBeg, kSpaceSize, REQ_MAX in *.
    (first [ dand5 Gc as Gc1 Gc2 Gc3 Gc4 Gc5 | destruct Gc as (Gc1 & Gc2 & Gc3 & Gc4 & Gc5) ]). (first [ dand5 Gn as Gn1 Gn2 Gn3 Gn4 Gn5 | destruct Gn as (Gn1 & Gn2 & Gn3 & Gn4 & Gn5) ]). (first [ dand5 Gf as Gf1 Gf2 Gf3 Gf4 Gf5 | destruct Gf as (Gf1 & Gf2 & Gf3 & Gf4 & Gf5) ]).
    (first [ dand5 CT1 as Ct1 Ct2 Ct3 Ct4 Ct5 | destruct CT1 as (Ct1 & Ct2 & Ct3 & Ct4 & Ct5) ]).
    split; [clear - L1 L2 CL1 CL2 R8' NR Gc5; lia|].
    split; [clear - PG1 PG2 SEP_pt SEP_pc; lia|].
    split; [clear - S1 S2 SHP; lia|].
    split; [clear - Gn1 Gn3 Gn4 Gn5 SEP_n0t SEP_n0 SEP_rn B3 SEP_n0c; lia|].
    split; [clear - Gf1 Gf3 Gf4 Gf5 SEP_f0t SEP_f0 SEP_rf B3 SEP_f0c; lia|].
    clear - Ct1 Ct3 Ct4 Ct5 SEP_tc SEP_ctx SEP_rc B3. lia.
  Qed.

  (* [comment removed for export] *)
  Ltac fw_open L P :=
    unfold fk_Wi, fk_Wfo, fpop_Wq, fpop_Wfo;
    destruct L as (L1 & L2 & (T1 & T2 & T3 & T4) & (B1 & B2 & B3 & B4 & B5) & (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10) & (H1 & H2 & H3 & H4 & H5));
    destruct P as ((P1 & P2 & P3 & P4) & (P5 & P6 & P7 & P8) & (S1 & S2 & S3) & ((N1 & N2 & N3 & N4) & N5 & N6 & N7) & ((F1 & F2 & F3 & F4) & F5 & F6 & F7) & ((C1 & C2 & C3) & C4 & C5 & C6));
    unfold kFreeArrayOffset in *;
    set (Sp := sh p) in *; set (Su := sh (rb + mu)) in *; set (Sf := sh (region_beg sb 24 + 3758096384 + mfa)) in *; set (u8 := U / 8) in *; set (f8 := Fm / 8) in *.
  Ltac fw_split := cbn [disjoint_from outside app]; try (destruct (a_cache_inited A)); OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; try exact I.

  Lemma fk_Wmax_img : img_off_depot (fk_Wi U Fm N ++ fk_Wfo).
  Proof.
    split; intros a l A1 A2; pose proof fk_lin as L; pose proof fk_plin as P; fw_open L P; fw_split;
      first [ solve [clear - A1 A2 CE L1 L2 T1 T2 T3 B1 B2 B3 B4 Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9 Q10 H1 H2 H3 H4 H5; lia]
            | solve [clear - A1 A2 P1; lia] | solve [clear - A1 A2 N1 N3; lia] | solve [clear - A1 A2 F1 F3; lia] | solve [clear - A1 A2 S1; lia] ].
  Qed.
  Lemma fk_Wmax_ctx : disjoint_from (fk_Wi U Fm N ++ fk_Wfo) (ctx + 152) 8.
  Proof.
    pose proof fk_lin as L. pose proof fk_plin as P. fw_open L P. fw_split;
      first [ solve [clear - CE L1 L2 C1 C2; lia]
            | solve [clear - C1 C2 C5 B1 B2 B3 B4 Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9 Q10; lia]
            | solve [clear - C1 C2 C4 T1 T2; lia]
            | solve [clear - C1 C2 C3 H1 H2 H3 H4 H5 S1 S2; lia]
            | solve [clear - C1 C2 P8 P3; lia] | solve [clear - C6; lia] | solve [clear - C1 C2 N7; lia] | solve [clear - C1 C2 F7; lia] ].
  Qed.
  (* [comment removed for export] *)
  Lemma fk_Wq_thr : forall a l, (thr + 80 <= a /\ a + l <= thr + 288) \/ (thr + 2768 <= a /\ a + l <= thr + 2792) \/ (thr + 2800 <= a /\ a + l <= thr + 2872) ->
    disjoint_from (fk_Wi U Fm N) a l.
  Proof.
    intros a l Hal. pose proof fk_lin as L. pose proof fk_plin as P. (first [ pose proof ((f24_sep A m md AI)) as dR_20; dand7 dR_20 as SEP_tr _ _ _ _ SEP_ts _ | pose proof (f24_sep A m md AI) as (SEP_tr & _ & _ & _ & _ & SEP_ts & _) ]). unfold apart, AMallocA.apart in *.
    fw_open L P. fw_split;
      first [ solve [clear - Hal CE L1 L2 T1 T2; lia]
            | solve [clear - Hal T1 T2 SEP_tr B3; lia]
            | solve [clear - Hal T1 T2 SEP_ts B1 B2 B4 Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9 Q10; lia]
            | solve [clear - Hal T1 T2 T4 H1 H2 H3 H4 H5; lia]
            | solve [clear - Hal; lia] ].
  Qed.
  Lemma fk_Wq_chunk : forall a l, p + -16 <= a -> a + l <= p + 8 * r8 -> disjoint_from (fk_Wi U Fm N) a l.
  Proof.
    intros a l A1 A2. pose proof fk_lin as L. pose proof fk_plin as P. fw_open L P. fw_split;
      first [ solve [clear - A1 A2 CE L1 L2 P2; lia]
            | solve [clear - A1 A2 P6 B3; lia]
            | solve [clear - A1 A2 P5 B1 B2 B4 Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9 Q10; lia]
            | solve [clear - A1 A2 P7 T1 T2; lia]
            | solve [clear - A1 A2 P1 P4 H1 H2 H3 H4 H5; lia] ].
  Qed.
  Lemma fk_Wq_shp : disjoint_from (fk_Wi U Fm N) (sh p) r8.
  Proof.
    pose proof fk_lin as L. pose proof fk_plin as P. fw_open L P. fw_split;
      first [ solve [clear - CE L1 L2 S1 S2; lia]
            | solve [clear - S1 S2 B1 B2 B3 B4 Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9 Q10; lia]
            | solve [clear - S1 S2 T1 T2 T4; lia]
            | solve [clear - S1 S2 S3 P3 H1 H2 H3 H4 H5; lia] ].
  Qed.
  Lemma fk_Wq_depot : forall a, depot_foot AL_pboth n0d f0d a -> 0 <= a < 2^64 /\ outside (fk_Wi U Fm N) a.
  Proof.
    intros a Ha. pose proof fk_lin as L. pose proof fk_plin as P.
    unfold depot_foot in Ha. cbn [al_stackStore al_depot_nodes_map1 AL_pboth] in Ha. unfold kDepotNodesL1, kDepotNodesBlock, kStackStoreBlockBytes in Ha.
    fw_open L P. split; [clear - Ha CE N1 N2 F1 F2; lia|].
    assert (IMG : 0x10000 <= a < 0x60a000 \/ (n0d <= a < n0d + 1048576) \/ (f0d <= a < f0d + 8388608)) by (clear - Ha; lia). clear Ha.
    fw_split; destruct IMG as [IMG|[IMG|IMG]];
      first [ solve [clear - IMG CE L1 L2 T1 T2 T3 B1 B2 B3 B4 Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9 Q10 H1 H2 H3 H4 H5; lia]
            | solve [clear - IMG CE L1 L2 N1 N2; lia] | solve [clear - IMG N6 B1 B2 B3 B4 Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9 Q10; lia]
            | solve [clear - IMG N5 T1 T2; lia] | solve [clear - IMG N1 N2 N4 H1 H2 H3 H4 H5; lia]
            | solve [clear - IMG CE L1 L2 F1 F2; lia] | solve [clear - IMG F6 B1 B2 B3 B4 Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9 Q10; lia]
            | solve [clear - IMG F5 T1 T2; lia] | solve [clear - IMG F1 F2 F4 H1 H2 H3 H4 H5; lia] ].
  Qed.
  (* [comment removed for export] *)
  Lemma fk_Wq_c24 : forall a l, rb <= a -> a + l <= rb + au -> disjoint_from (fk_Wi U Fm N) a l.
  Proof.
    intros a l A1 A2. pose proof fk_lin as L. pose proof fk_plin as P. (first [ pose proof ((f24_sep A m md AI)) as dR_21; dand7 dR_21 as _ _ _ _ _ SEP_ts _ | pose proof (f24_sep A m md AI) as (_ & _ & _ & _ & _ & SEP_ts & _) ]). unfold apart, AMallocA.apart in *.
    fw_open L P. fw_split;
      first [ solve [clear - A1 A2 CE L1 L2 B1 B2 B4 Q1 Q2 Q3; lia]
            | solve [clear - A1 A2 B1 B2 B3 B4 Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9 Q10; lia]
            | solve [clear - A1 A2 SEP_ts T1 T2 B1 B2 B4 Q1 Q2 Q3; lia]
            | solve [clear - A1 A2 B1 B4 Q1 H1 H2 H3 H4 H5; lia] ].
  Qed.

  (* [comment removed for export] *)
  Section At.
  Variables (junk0 pad scr : list byte) (ksc : list word) (ums fam nc : Z) (w : mem).
  Hypothesis CY : carryF junk0 pad scr ksc ums fam nc w.
  Hypothesis LE : sub_fp (fk_Wi ums fam nc) (fk_Wi U Fm N).
  Let MUx : munch (fk_Wi U Fm N ++ fk_Wfo) v w. Proof. destruct CY as (MU0 & _). exact (munch_weaken _ _ _ _ (sub_fp_app2 _ _ _ LE) MU0). Qed.
  Let WMx : wmono rsegs v w. Proof. destruct CY as (_ & WM0 & _). exact WM0. Qed.

  Lemma fcy_statics : pop_statics pa_tsd ctx thr sb w.
  Proof.
    apply (pop_statics_munch2 (fk_Wi U Fm N ++ fk_Wfo) _ _ _ _ v w (pk_statics A m md AI) MUx); [unfold pa_tsd; lia| exact fk_Wmax_img| exact fk_Wmax_ctx].
  Qed.
  (* [comment removed for export] *)
  Lemma fcy_seal : ro_cells rsegs w 0xa8bb0 [C8 (wz 1)] /\ ro_cells rsegs w 0xa8bb8 [C8 (wz 0x1466dc)] /\ ro_cells rsegs w 0x1466dc [C4 (wz 0)].
  Proof.
    pose proof (conj (WFT_of_WF A W0) (ai_repr _ _ _ _ _ _ _ AI) : WFT A /\ @arepr _ DepotRepL LPA AL_pboth [] A v) as ARt.
    destruct fk_Wmax_img as [LO _].
    split; [eapply ro_cells_transport; [exact (rk_SEAL A v [] ARt)| exact MUx| apply LO; cbn; lia]|].
    split; [eapply ro_cells_transport; [exact (rk_DYG A v [] ARt)| exact MUx| apply LO; cbn; lia]|].
    eapply ro_cells_transport; [exact (rk_DYF A v [] ARt)| exact MUx| apply LO; cbn; lia].
  Qed.
  Lemma fcy_mapped : forall a k, mapped v a k -> 0 <= a -> (a + k <= 0x10000 \/ 0x60a000 <= a) -> a + k <= 2^64 -> mapped w a k.
  Proof. intros a k M H0 H1 H2. exact (pk_mapped_wm v w a k WMx H0 H1 H2 M). Qed.
  Lemma fcy_NN : forall a, 0 <= a -> (a + 1 <= 0x10000 \/ 0x60a000 <= a) -> a < 2^64 -> v (wz a) <> None -> w (wz a) <> None.
  Proof. intros a H0 H1 H2. apply (pk_wmono_NN v w a WMx H1); lia. Qed.
  Lemma fcy_na : exists na, rw_cells rsegs w (R + 72) [C8 na].
  Proof.
    (first [ pose proof (fk_region) as dR_22; dand10 dR_22 as _ _ _ _ _ _ _ _ MRI _ | pose proof fk_region as (_ & _ & _ & _ & _ & _ & _ & _ & MRI & _) ]). (first [ pose proof (fk_lin) as dR_23; dand5 dR_23 as L1 L2 _ (B1 & B2 & B3 & B4 & B5) _ | pose proof fk_lin as (L1 & L2 & _ & (B1 & B2 & B3 & B4 & B5) & _) ]).
    apply mapped_C8_1; [| lia| lia]. apply fcy_mapped; [| lia| right; lia| lia].
    intros i Hi. replace (R + 72 + i) with (ri + (128 * 24 + 72 + i)) by lia. apply MRI. lia.
  Qed.
  Lemma fcy_thr_mapped : forall a k, thr <= a -> a + k <= thr + 4096 -> mapped w a k.
  Proof.
    intros a k H1 H2. (first [ pose proof (fk_lin) as dR_24; dand4 dR_24 as L1 L2 (T1 & T2 & T3 & T4) _ | pose proof fk_lin as (L1 & L2 & (T1 & T2 & T3 & T4) & _) ]).
    apply fcy_mapped; [| lia| lia| lia]. intros i Hi. replace (a + i) with (thr + (a - thr + i)) by lia. apply (pk_TM A m md AI). lia.
  Qed.
  Lemma fcy_tst : exists mm72 mm80, rw_cells rsegs w (thr + off_th_stats + 72) [C8 mm72; C8 mm80].
  Proof. (first [ pose proof (fk_lin) as dR_25; dand4 dR_25 as L1 L2 (T1 & T2 & T3 & T4) _ | pose proof fk_lin as (L1 & L2 & (T1 & T2 & T3 & T4) & _) ]). unfold off_th_stats. apply mapped_C8_2; [apply fcy_thr_mapped; lia| lia| lia]. Qed.
  Lemma fcy_stm : exists statm, rw_cells rsegs w (thr + 208 + 2560 + 24) [C8 statm].
  Proof. (first [ pose proof (fk_lin) as dR_26; dand4 dR_26 as L1 L2 (T1 & T2 & T3 & T4) _ | pose proof fk_lin as (L1 & L2 & (T1 & T2 & T3 & T4) & _) ]). apply mapped_C8_1; [apply fcy_thr_mapped; lia| lia| lia]. Qed.

  (* [comment removed for export] *)
  Lemma fcy_fcells : fcells w.
  Proof.
    destruct CY as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (wH & MUH & WMH & FC)).
    pose proof (munch_weaken _ _ _ _ LE MUH) as MUq. pose proof fk_plin as ((_ & _ & P3 & _) & _).
    (first [ dex6 FC as b1 fr fd nx bsz statv; dand11 FC as RG HDRe TSTe TST HDR CTXW SHD DR QC LBC STA | dand17 FC as b1 fr fd nx bsz statv RG HDRe TSTe TST HDR CTXW SHD DR QC LBC STA | destruct FC as (b1 & fr & fd & nx & bsz & statv & RG & HDRe & TSTe & TST & HDR & CTXW & SHD & DR & QC & LBC & STA) ]).
    exists b1, fr, fd, nx, bsz, statv. split; [exact RG|]. split; [exact HDRe|]. split; [exact TSTe|].
    split; [eapply rw_cells_transport; [exact TST| exact MUq| exact WMH| apply fk_Wq_thr; cbn; lia]|].
    split; [eapply rw_cells_transport; [exact HDR| exact MUq| exact WMH| apply fk_Wq_chunk; cbn; lia]|].
    split; [eapply rw_cells_transport; [exact CTXW| exact MUq| exact WMH| apply fk_Wq_chunk; cbn; lia]|].
    split; [eapply bytes_at_transport; [exact SHD| exact MUq|]; rewrite repeat_length, Z2Nat.id by lia; exact fk_Wq_shp|].
    split; [exact (depot_repL_munchW _ _ _ _ _ _ _ DR MUq fk_Wq_depot)|].
    split; [eapply rw_cells_transport; [exact QC| exact MUq| exact WMH| apply fk_Wq_thr; cbn; lia]|].
    split.
    - intros QNE. specialize (LBC QNE). eapply rw_cells_transport; [exact LBC| exact MUq| exact WMH|].
      (* [comment removed for export] *)
      pose proof (conj W0 (ai_repr _ _ _ _ _ _ _ AI) : WF A /\ @arepr _ DepotRepL LPA AL_pboth [] A v) as AR.
      assert (INl : In (last (a_qthread A) (BA 0 [])) (a_qthread A ++ a_qglobal A)).
      { apply in_or_app. left. rewrite <- (removelast_last_app (a_qthread A) (BA 0 []) QNE) at 2. apply in_or_app. right. left. reflexivity. }
      pose proof (ATransp.batch_carved A v AR _ INl) as CBL. pose proof (ATransp.carved_prim_where A v AR _ _ CBL) as WL. rewrite class_size_24 in WL.
      assert (QL : qc_last A (a_qthread A) = batch_addr sb (last (a_qthread A) (BA 0 []))) by (unfold qc_last; destruct (a_qthread A); [congruence| reflexivity]).
      rewrite QL. apply fk_Wq_c24; unfold batch_addr, kQuarantineBatchClass, kQuarantineBatchBytes in *; cbn [cells_size csize Nat.add]; lia.
    - eapply rw_cells_transport; [exact STA| exact MUq| exact WMH| apply fk_Wq_thr; cbn; lia].
  Qed.
  End At.
End FPkg.
