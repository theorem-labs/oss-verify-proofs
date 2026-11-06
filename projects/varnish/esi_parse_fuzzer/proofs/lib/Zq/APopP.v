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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts ARtS4t2 ARtSb8o AMTac AMallocA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AMalz1i.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AMalmys AMaldga AMalrrv ASecB1 ANodeA7 ANodl61 ATransp ATranspR AFreeRC.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeRK2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeRK2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeRW2 ABudget ACor4x6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require APopG1.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ATransp.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require APopG1 APopG2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require APopG5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require APopG5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require APopG5.

Module APopK.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts ARtS4t2 ARtSb8o AMallocA AMalmys AMaldga AMalrrv ASecB1 ANodeA7 ANodl61 ATransp ATranspR AFreeRC.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeRK2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeRK2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeRW2 ABudget ACor4x6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require APopG1.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ATransp.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require APopG1 APopG2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require APopG5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require APopG5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require APopG5.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtS4t2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSb8o OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMallocA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalmys OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMaldga OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalrrv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASecB1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ANodeA7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ANodl61 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ATransp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ATranspR OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeRC OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeRK2.AFreeRK OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeRK2.AFreeRK3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeRW2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ABudget OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ACor4x6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APopG1.APopDefs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ATransp.APopCap OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APopG1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APopG2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APopG5.APopG3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APopG5.APopG4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APopG5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.solve_load_guarded | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image].
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)

Notation wz z := (Z_to_bv 64 z) (only parsing).
#[local] Notation WF := (WF AL_pboth).
Ltac kung_all := unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kShadowOffset, kRegionSize, kSpaceSize, kFreeArrayOffset,
                        kHighShadowMapBeg, kSpaceReserve, kMaxSize, kLowShadowMapBeg, kShadowGapBeg, kHighShadowMapSize,
                        kAuCap, kFreeArraySize, kUserMapSize, kFreeArrayMapSize in *.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rw_cells_app_iff : forall (w : mem) a cs1 cs2,
  rw_cells rsegs w a (cs1 ++ cs2) <-> rw_cells rsegs w a cs1 /\ rw_cells rsegs w (a + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros w a cs1 cs2. unfold rw_cells, cells_at. rewrite cells_wf_app, cells_bytes_app, cells_size_app, bytes_at_app. split.
  - intros (((W1 & W2) & (B1 & B2)) & (A0 & A1 & WR)). rewrite (cells_bytes_length _ W1) in B2.
    pose proof (bytes_at_bound _ _ _ _ B2) as BB2. rewrite (cells_bytes_length _ W2) in BB2.
    split; (split; [split; assumption|]).
    + split; [lia|]. split; [lia|]. intros i Hi. apply WR. lia.
    + split; [lia|]. split; [lia|]. intros i Hi. replace (a + Z.of_nat (cells_size cs1) + i) with (a + (Z.of_nat (cells_size cs1) + i)) by lia. apply WR. lia.
  - intros (((W1 & B1) & (A0 & A1 & WR1)) & ((W2 & B2) & (C0 & C1 & WR2))). rewrite (cells_bytes_length _ W1).
    split; [split; [split; assumption| split; assumption]|].
    split; [lia|]. split; [lia|]. intros i Hi. destruct (Z_lt_le_dec i (Z.of_nat (cells_size cs1))) as [L|G]; [apply WR1; lia|].
    replace (a + i) with (a + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia. apply WR2. lia.
Qed.

(* [comment removed for export] *)
Lemma pk_wmono_NN : forall (w w' : mem) a, wmono rsegs w w' -> (a + 1 <= 0x10000 \/ 0x60a000 <= a) -> 0 <= a < 2^64 ->
  w (wz a) <> None -> w' (wz a) <> None.
Proof.
  intros w w' a WM Ha Hr Hv. specialize (WM (wz a)). unfold wview in WM.
  rewrite unsigned_lit in WM by lia. rewrite (pa_find_segment_none a 1 ltac:(lia) Ha) in WM.
  destruct (w (wz a)); [| congruence]. destruct (w' (wz a)); [congruence|]. exfalso. apply WM; [discriminate| reflexivity].
Qed.
Lemma pk_mapped_wm : forall (w w' : mem) a k, wmono rsegs w w' -> 0 <= a -> (a + k <= 0x10000 \/ 0x60a000 <= a) -> a + k <= 2^64 -> mapped w a k -> mapped w' a k.
Proof. intros w w' a k WM H0 H1 H2 M i Hi. apply (pk_wmono_NN w w' (a + i) WM); [lia| lia| apply M; exact Hi]. Qed.

(* [comment removed for export] *)
Lemma disjoint_from_sub : forall W a l a' l', disjoint_from W a l -> a <= a' -> a' + l' <= a + l -> disjoint_from W a' l'.
Proof. induction W as [|[lo hi] W IH]; cbn; intros a l a' l' D H1 H2; [exact I|]. destruct D as [D1 D2]. split; [lia| exact (IH _ _ _ _ D2 H1 H2)]. Qed.

(* [comment removed for export] *)
Lemma mapped_C8s : forall (w : mem) a (k : nat), mapped w a (8 * Z.of_nat k) -> 0 <= a -> a + 8 * Z.of_nat k <= 2^64 ->
  exists ws, length ws = k /\ rw_cells rsegs w a (map C8 ws).
Proof.
  intros w a k M A0 A1. assert (M' : mapped w a (Z.of_nat (8 * k))) by (rewrite Nat2Z.inj_mul; exact M).
  pose proof (rdbytes_bytes_at w a (8 * k) M' A0 ltac:(lia)) as B.
  exists (words8 (rdbytes w a (8 * k)) k). split; [apply words8_length|].
  apply ro_rw.
  - split; [apply CB8_wf|]. rewrite CB8_bytes, u64s_words8 by (apply rdbytes_length). exact B.
  - rewrite CB8_size, words8_length, Nat2Z.inj_mul. exact M.
Qed.
Lemma mapped_C8_1 : forall (w : mem) a, mapped w a 8 -> 0 <= a -> a + 8 <= 2^64 -> exists x, rw_cells rsegs w a [C8 x].
Proof.
  intros w a M A0 A1. (first [ pose proof ((mapped_C8s w a 1 M A0 A1)) as dR_1; dex1 dR_1 as ws; destruct dR_1 as [L RW] | pose proof ((mapped_C8s w a 1 M A0 A1)) as dR_1; dand3 dR_1 as ws L RW | destruct (mapped_C8s w a 1 M A0 A1) as (ws & L & RW) ]). destruct ws as [|x [|]]; cbn in L; try lia. exists x. exact RW.
Qed.
Lemma mapped_C8_2 : forall (w : mem) a, mapped w a 16 -> 0 <= a -> a + 16 <= 2^64 -> exists x y, rw_cells rsegs w a [C8 x; C8 y].
Proof.
  intros w a M A0 A1. (first [ pose proof ((mapped_C8s w a 2 M A0 A1)) as dR_2; dex1 dR_2 as ws; destruct dR_2 as [L RW] | pose proof ((mapped_C8s w a 2 M A0 A1)) as dR_2; dand3 dR_2 as ws L RW | destruct (mapped_C8s w a 2 M A0 A1) as (ws & L & RW) ]). destruct ws as [|x [|y [|]]]; cbn in L; try lia. exists x, y. exact RW.
Qed.
Lemma mapped_CB : forall (w : mem) a (k : nat), mapped w a (Z.of_nat k) -> 0 <= a -> a + Z.of_nat k <= 2^64 ->
  rw_cells rsegs w a [CB k (rdbytes w a k)].
Proof.
  intros w a k M A0 A1. pose proof (rdbytes_bytes_at w a k M A0 A1) as B. apply ro_rw.
  - split; [split; [apply rdbytes_length| exact I]|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact B.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact M.
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma carved_newfree : forall au size nc, 0 < size -> au mod size = 0 ->
  ARtSb8o.carved au size nc = map (fun k => wz (k * size / kCompactPtrScale)) (newfree (au / size) nc).
Proof.
  intros au size nc S0 AM. unfold ARtSb8o.carved, newfree. rewrite map_map. apply map_ext. intros j. f_equal. unfold kCompactPtrScale.
  pose proof (Z_div_mod_eq_full au size) as E. rewrite AM, Z.add_0_r in E. f_equal. rewrite E at 1. lia.
Qed.

(* [comment removed for export] *)
Lemma nodup_bounded_length : forall (l : list Z) N, 0 <= N -> List.NoDup l -> (forall k, In k l -> 0 <= k < N) -> Z.of_nat (length l) <= N.
Proof.
  intros l N HN ND B.
  assert (INCL : incl l (map Z.of_nat (seq 0 (Z.to_nat N)))).
  { intros k Hk. apply in_map_iff. exists (Z.to_nat k). pose proof (B k Hk). split; [lia| apply in_seq; lia]. }
  pose proof (NoDup_incl_length ND INCL) as L. rewrite length_map, length_seq in L. lia.
Qed.

(* [comment removed for export] *)
Fixpoint all_inside (W' W : list (Z * Z)) : Prop :=
  match W with [] => True | (lo, hi) :: r => (hi <= lo \/ inside W' lo (hi - lo)) /\ all_inside W' r end.
Lemma sub_fp_all_inside : forall W W', all_inside W' W -> sub_fp W W'.
Proof.
  induction W as [|[lo hi] W IH]; intros W' H x OUT; cbn; [exact I|]. destruct H as [H1 H2]. split; [| exact (IH W' H2 x OUT)].
  intros Hx. destruct H1 as [E|IN]; [lia|]. exact (inside_not_outside W' lo (hi - lo) x IN ltac:(lia) OUT).
Qed.
Ltac find_in := first [left; lia | right; find_in].

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Arith.
Context {Clg : Ceiling}.
  Variables (A : AState) (c : Z).
  Hypothesis W : WF A.
  Hypothesis CR : 1 <= c <= 30.
  Hypothesis EMP : pk_chunks (a_cache A c) = [].
  Hypothesis SHORT : Z.of_nat (length (rg_free (a_reg A c))) < refill_count c.
  #[warnings="-notation-for-abbreviation"] Local Notation mu := (rg_mapped_user (a_reg A c)).
  #[warnings="-notation-for-abbreviation"] Local Notation au := (rg_allocated_user (a_reg A c)).
  #[warnings="-notation-for-abbreviation"] Local Notation mfa := (rg_mapped_fa (a_reg A c)).
  #[warnings="-notation-for-abbreviation"] Local Notation nf := (Z.of_nat (length (rg_free (a_reg A c)))).
  #[warnings="-notation-for-abbreviation"] Local Notation kk := (refill_count c).
  #[warnings="-notation-for-abbreviation"] Local Notation size := (class_size c).

  (* [comment removed for export] *)
  Definition pop_ums : Z := if (au + (kk - nf) * size <=? mu) then 0 else round_up (au + (kk - nf) * size - mu) kUserMap.
  Definition pop_nc : Z := (mu + pop_ums - au) / size.
  Definition pop_fam : Z := if (4 * (nf + pop_nc) <=? mfa) then 0 else round_up (4 * (nf + pop_nc)) kFaMap - mfa.

  #[using="CR A"] Lemma ar_k : max_count c = 2 * kk /\ 1 <= kk <= 8 /\ Z.shiftr (max_count c) 1 = kk /\ 2 <= max_count c <= 16.
  Proof.
    (first [ pose proof ((max_count_range _ CR)) as dR_3; dand3 dR_3 as M1 M2 M3 | pose proof (max_count_range _ CR) as (M1 & M2 & M3) ]). rewrite Z.shiftr_div_pow2 by lia. change (2^1) with 2.
    assert (D : max_count c / 2 = kk) by (rewrite M2, Z.mul_comm, Z_div_mult by lia; reflexivity).
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia.
  Qed.
  #[using="CR"] Lemma ar_csr : 32 <= size <= 65536. Proof. pose proof (class_size_range c CR) as X. unfold kMaxSize in X. exact X. Qed.
  (* [comment removed for export] *)
  #[using="CR W Clg"] Lemma ar_reg : (0 <= au <= mu /\ mu < au + 9 * size + 262144) /\ mu <= kFreeArrayOffset /\ mu mod 262144 = 0 /\ au mod size = 0 /\
                 0 <= mfa <= kFreeArraySize /\ mfa mod 262144 = 0 /\ 4 * nf <= mfa /\ au <= kAuCap - 2^27 /\ mfa <= 4 * (au / size) + 262144 /\ 0 <= nf.
  Proof.
    (first [ pose proof ((wfR A W)) as dR_4; dand3 dR_4 as WR _ _ | destruct (wfR A W) as (WR & _ & _) ]). (first [ pose proof ((WR c CR)) as dR_5; dand12 dR_5 as A1 A2 A3 A4 A5 A6 A7 _ _ _ A11 A12 | destruct (WR c CR) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _ & _ & _ & A11 & A12) ]).
    pose proof (wf_au_cap A c W CR) as [AUC _].
    unfold kUserMapSize, kFreeArrayMapSize in *. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try tauto; try lia.
  Qed.
  #[using="CR W Clg"] Lemma ar_nfcc : nf <= au / size.
  Proof.
    (first [ pose proof ((wfR A W)) as dR_6; dand3 dR_6 as WR _ _ | destruct (wfR A W) as (WR & _ & _) ]). (first [ pose proof ((WR c CR)) as dR_7; dand10 dR_7 as A1 _ _ _ _ _ _ ND BD _ | destruct (WR c CR) as (A1 & _ & _ & _ & _ & _ & _ & ND & BD & _) ]).
    pose proof ar_csr as CSR. apply nodup_bounded_length; [apply Z.div_pos; lia| exact (proj1 (NoDup_ListNoDup _) ND)| exact BD].
  Qed.
  (* [comment removed for export] *)
  #[using="SHORT EMP CR W Clg"] Lemma ar_cap : au <= size * (Z.of_nat (length (a_paid A c)) + 7) + class_slack c.
  Proof. exact (pop_cap A c W CR EMP SHORT). Qed.
  #[using="SHORT CR W Clg"] Lemma ar_ks : 1 <= kk - nf <= 8 /\ (kk - nf) * size <= 8 * 65536 /\ 0 < (kk - nf) * size /\ (kk - nf) * size <= 8 * size.
  Proof. (first [ pose proof (ar_k) as dR_8; dand3 dR_8 as _ K _ | pose proof ar_k as (_ & K & _) ]). pose proof ar_csr as CSR. (first [ pose proof (ar_reg) as dR_9; dand10 dR_9 as _ _ _ _ _ _ _ _ _ NF0 | pose proof ar_reg as (_ & _ & _ & _ & _ & _ & _ & _ & _ & NF0) ]). split; [lia|]. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; nia. Qed.

  (* [comment removed for export] *)
  Lemma ar_ums_cases : (pop_ums = 0 /\ au + (kk - nf) * size <= mu) \/
                       (pop_ums = round_up (au + (kk - nf) * size - mu) kUserMap /\ mu < au + (kk - nf) * size).
  Proof. unfold pop_ums. destruct (Z.leb_spec (au + (kk - nf) * size) mu); [left| right]; split; try reflexivity; lia. Qed.
  #[using="SHORT EMP CR W Clg"] Lemma ar_ums : (0 <= pop_ums /\ pop_ums mod kUserMapSize = 0 /\ mu + pop_ums < au + 9 * size + kUserMapSize /\
                                                au <= size * (Z.of_nat (length (a_paid A c)) + 7) + class_slack c) /\
                 au + (kk - nf) * size <= mu + pop_ums /\ mu + pop_ums - au < 9 * size + 262144 /\
                 mu + pop_ums < au + (kk - nf) * size + 262144 + 9 * size /\ pop_ums < 2^21.
  Proof.
    (first [ pose proof (ar_reg) as dR_10; dand10 dR_10 as (R1 & R2) R3 R4 R5 R6 R7 R8 R9 R10 R11 | pose proof ar_reg as ((R1 & R2) & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11) ]). pose proof ar_cap as CAP. (first [ pose proof (ar_ks) as dR_11; dand4 dR_11 as K1 K2 K3 K4 | pose proof ar_ks as (K1 & K2 & K3 & K4) ]). pose proof ar_csr as CSR.
    unfold kUserMapSize.
    destruct ar_ums_cases as [[E F]|[E F]]; rewrite E.
    - rewrite Z.add_0_r. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try lia; try reflexivity.
    - pose proof (roundup_famap_range (au + (kk - nf) * size - mu) ltac:(lia)) as ((U1 & U2) & U3). unfold kUserMap. change 0x40000 with 262144.
      OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try lia; try exact U3.
  Qed.
  #[using="SHORT EMP CR W Clg"] Lemma ar_nc : 0 <= pop_nc /\ au + pop_nc * size <= mu + pop_ums /\ mu + pop_ums < au + pop_nc * size + size /\ kk - nf <= pop_nc /\ pop_nc < 9 + 8192.
  Proof.
    (first [ pose proof (ar_ums) as dR_12; dand5 dR_12 as (U1 & U2 & U3) U4 U5 U6 U7 | pose proof ar_ums as ((U1 & U2 & U3) & U4 & U5 & U6 & U7) ]). pose proof ar_csr as CSR. pose proof ar_reg as ((R1 & R2) & _).
    unfold pop_nc. set (x := mu + pop_ums - au) in *.
    pose proof (Z_div_mod_eq_full x size) as E. pose proof (Z.mod_pos_bound x size ltac:(lia)) as MB.
    assert (X0 : 0 <= x) by (unfold x; lia).
    assert (Q0 : 0 <= x / size) by (apply Z.div_pos; lia).
    assert (QK : kk - nf <= x / size) by (apply Z.div_le_lower_bound; [lia| unfold x; lia]).
    assert (QU : x / size < 9 + 8192) by (apply Z.div_lt_upper_bound; [lia| unfold x in *; nia]).
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try lia; unfold x in *; nia.
  Qed.
  (* [comment removed for export] *)
  Lemma ar_fam_cases : (pop_fam = 0 /\ 4 * (nf + pop_nc) <= mfa) \/
                       (pop_fam = round_up (4 * (nf + pop_nc)) kFaMap - mfa /\ mfa < 4 * (nf + pop_nc)).
  Proof. unfold pop_fam. destruct (Z.leb_spec (4 * (nf + pop_nc)) mfa); [left| right]; split; try reflexivity; lia. Qed.
  (* [comment removed for export] *)
  #[using="SHORT EMP CR W Clg"] Lemma ar_fam : (0 <= pop_fam /\ pop_fam mod kFreeArrayMapSize = 0 /\
                                                mfa + pop_fam <= 4 * (au / size) + kFreeArrayMapSize /\ mfa + pop_fam <= kFreeArraySize) /\
                                               4 * (nf + pop_nc) <= mfa + pop_fam /\ pop_fam <= 2^28.
  Proof.
    (first [ pose proof (ar_reg) as dR_13; dand10 dR_13 as (R1 & R2) R3 R4 R5 R6 R7 R8 R9 R10 R11 | pose proof ar_reg as ((R1 & R2) & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11) ]). pose proof ar_csr as CSR.
    (first [ pose proof (ar_nc) as dR_14; dand5 dR_14 as N1 N2 N3 N4 N5 | pose proof ar_nc as (N1 & N2 & N3 & N4 & N5) ]). pose proof ar_nfcc as NFC.
    (first [ pose proof (ar_k) as dR_15; dand3 dR_15 as _ KK _ | pose proof ar_k as (_ & KK & _) ]).
    assert (CC0 : 0 <= au / size) by (apply Z.div_pos; lia).
    unfold kFreeArrayMapSize, kFreeArraySize in *.
    destruct ar_fam_cases as [[E F]|[E F]]; rewrite E.
    - rewrite Z.add_0_r. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try lia; try reflexivity.
    - pose proof (roundup_famap_range (4 * (nf + pop_nc)) ltac:(lia)) as ((V1 & V2) & V3). unfold kFaMap in *.
      set (nm := round_up (4 * (nf + pop_nc)) 262144) in *.
      pose proof (Z_div_mod_eq_full nm 262144) as Q1. rewrite V3, Z.add_0_r in Q1.
      assert (NM : nm = 262144) by (clear - Q1 V1 V2 N5 R11 SHORT KK N4; lia).
      assert (FM : (nm - mfa) mod 262144 = 0).
      { pose proof (Z_div_mod_eq_full mfa 262144) as Q2. rewrite R7, Z.add_0_r in Q2.
        replace (nm - mfa) with ((nm / 262144 - mfa / 262144) * 262144) by lia. apply Z_mod_mult. }
      OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try lia. exact FM.
  Qed.
End Arith.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition pop_statics {Clg : Ceiling} (tsd ctx thr sb : Z) (w : mem) : Prop :=
  poison_consts w /\ thread_cells w (cl_tp LPA) tsd ctx thr /\
  ro_cells rsegs w 0xb1578 [C8 (wz sb)] /\ ro_cells rsegs w 0xb1580 [C4 (wz 4294967295)] /\ ro_cells rsegs w 0xb1590 [C1 (Z_to_bv 8 0)] /\
  ro_cells rsegs w (ANodeA7.CF + 260) [C1 (Z_to_bv 8 0)] /\ ro_cells rsegs w (ANodeA7.CF + 144) [C8 (wz 0)] /\
  ro_cells rsegs w 0x136e21 [C1 (Z_to_bv 8 1)].

Lemma pop_statics_munch {Clg : Ceiling} : forall W tsd ctx thr sb (w w' : mem),
  pop_statics tsd ctx thr sb w -> munch W w w' -> 0x5e7b28 <= tsd /\ tsd + 8 <= 0x60a000 ->
  (forall a l, 0x10000 <= a -> a + l <= 0x60a000 -> disjoint_from W a l) -> disjoint_from W (ctx + 152) 8 ->
  pop_statics tsd ctx thr sb w'.
Proof.
  (intros W tsd ctx thr sb w w'; (first [ intro dR_23; dand8 dR_23 as P1 P2 P3 P4 P5 P6 P7 P8 | intros (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8) ]); intros MU TS DJ DC). unfold pop_statics.
  split; [exact (poison_consts_munch W w w' P1 MU DJ)|].
  split; [apply (thread_cells_munch W w w' _ _ _ _ P2 MU); [reflexivity| exact TS| exact DJ| exact DC]|].
  OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; (eapply ro_cells_transport; [eassumption| exact MU| apply DJ; unfold ANodeA7.CF; cbn; lia]).
Qed.

Section Entry.
Context {Clg : Ceiling}.
  Variables (A : AState) (m : mem) (md : Model) (n : Z).
  Hypothesis AI : @pa_ainv _ DepotRepL A m md.
  Hypothesis NR : 1 <= n <= kMaxPrimaryUser.
  #[warnings="-notation-for-abbreviation"] Local Notation c := (class_of n).
  #[warnings="-notation-for-abbreviation"] Local Notation v := (aview_of (pa_hull A) m).
  #[warnings="-notation-for-abbreviation"] Local Notation thr := (p_thr (a_pl A)).
  #[warnings="-notation-for-abbreviation"] Local Notation sb := (a_sb A).
  #[warnings="-notation-for-abbreviation"] Local Notation ri := (a_ri A).
  #[warnings="-notation-for-abbreviation"] Local Notation R := (a_ri A + 128 * class_of n).
  #[warnings="-notation-for-abbreviation"] Local Notation rb := (region_beg (a_sb A) (class_of n)).
  #[warnings="-notation-for-abbreviation"] Local Notation fa := (region_beg (a_sb A) (class_of n) + kFreeArrayOffset).
  #[warnings="-notation-for-abbreviation"] Local Notation mu := (rg_mapped_user (a_reg A (class_of n))).
  #[warnings="-notation-for-abbreviation"] Local Notation au := (rg_allocated_user (a_reg A (class_of n))).
  #[warnings="-notation-for-abbreviation"] Local Notation mfa := (rg_mapped_fa (a_reg A (class_of n))).
  #[warnings="-notation-for-abbreviation"] Local Notation nf := (Z.of_nat (length (rg_free (a_reg A (class_of n))))).

  Let W0 : WF A. Proof. exact (ai_wf _ _ _ _ _ _ _ AI). Qed.
  Let RR : @arepr _ DepotRepL LPA AL_pboth [] A v. Proof. exact (ai_repr _ _ _ _ _ _ _ AI). Qed.
  Let ARt : WFT A /\ @arepr _ DepotRepL LPA AL_pboth [] A v. Proof. exact (conj (WFT_of_WF A W0) RR). Qed.
  Let CR : 1 <= c <= 30. Proof. exact (proj1 (hit_class n NR)). Qed.
  Let CE : 0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000. Proof. exact alloc_ceiling_val. Qed.

  #[using="ARt RR W0 AI md"] Lemma pk_statics : pop_statics pa_tsd (p_ctx (a_pl A)) thr sb v.
  Proof.
    unfold pop_statics. split; [exact (hit_PCo A m md AI)|]. split; [exact (hit_TC A m md AI)|]. split; [exact (hit_SBc A m md AI)|].
    split; [exact (rk_CITV A v [] ARt)|]. split; [exact (rk_CPMH A v [] ARt)|]. split; [exact (rk_CDMP A v [] ARt)|].
    split; [exact (rk_CML A v [] ARt)| exact (sec_MRN A m md AI)].
  Qed.

  (* [comment removed for export] *)
  #[using="CR RR NR AI md"] Lemma pk_region :
    rw_cells rsegs v R [C8 (wz 0)] /\ rw_cells rsegs v (R + 16) [C8 (wz nf)] /\ rw_cells rsegs v (R + 24) [C8 (wz mfa)] /\
    rw_cells rsegs v (R + 32) [C8 (wz au)] /\ rw_cells rsegs v (R + 40) [C8 (wz 0)] /\ rw_cells rsegs v (R + 48) [C8 (wz mu)] /\
    rw_cells rsegs v (R + 56) [C8 (wz 0)] /\ rw_cells rsegs v (R + 68) [C1 (Z_to_bv 8 0)] /\
    mapped v ri 4096 /\ mapped v fa mfa /\ mapped v rb mu.
  Proof.
    (first [ pose proof ((ref_ri A m md n AI)) as dR_15; dand7 dR_15 as RI RLO RHI RAL SBAL RIA FAE | pose proof (ref_ri A m md n AI) as (RI & RLO & RHI & RAL & SBAL & RIA & FAE) ]).
    pose proof (ar_regions _ _ _ _ _ RR c CR) as RG. unfold region_repr_ in RG. cbv zeta in RG.
    rewrite RIA in RG. (first [ dand13 RG as Hnf Hfa Hal Ham Hmu Hmm Hex _ _ _ _ MFA MUS | destruct RG as (Hnf & Hfa & Hal & Ham & Hmu & Hmm & Hex & _ & _ & _ & _ & MFA & MUS) ]).
    pose proof (ar_locks _ _ _ _ _ RR) as LK. unfold locks_repr_ in LK. cbv zeta in LK. destruct LK as (LK & _).
    destruct (LK c ltac:(lia)) as [MX0 _]. change (p_ri (a_pl A)) with ri in MX0. unfold kRegionInfoSize in MX0. rewrite Z.add_0_r in MX0.
    (first [ pose proof ((ar_maps _ _ _ _ _ RR)) as dR_17; dand3 dR_17 as _ MRI _ | pose proof (ar_maps _ _ _ _ _ RR) as (_ & MRI & _) ]). change (p_ri (a_pl A)) with ri in MRI.
    unfold off_ri_num_freed, off_ri_mapped_free_array, off_ri_allocated_user, off_ri_allocated_meta, off_ri_mapped_user, off_ri_mapped_meta, off_ri_exhausted in *.
    assert (TMi : forall a j, ri <= a -> a + j <= ri + 4096 -> mapped v a j).
    { intros a j H1 H2 i Hi. replace (a + i) with (ri + (a - ri + i)) by lia. apply MRI. lia. }
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits.
    - apply ro_rw; [apply u64_ro; exact MX0| apply TMi; cbn; lia].
    - apply ro_rw; [apply u64_ro; exact Hnf| apply TMi; cbn; lia].
    - apply ro_rw; [apply u64_ro; exact Hfa| apply TMi; cbn; lia].
    - apply ro_rw; [apply u64_ro; exact Hal| apply TMi; cbn; lia].
    - apply ro_rw; [apply u64_ro; exact Ham| apply TMi; cbn; lia].
    - apply ro_rw; [apply u64_ro; exact Hmu| apply TMi; cbn; lia].
    - apply ro_rw; [apply u64_ro; exact Hmm| apply TMi; cbn; lia].
    - apply ro_rw; [apply u8_ro; exact Hex| apply TMi; cbn; lia].
    - exact MRI.
    - unfold free_array_beg in MFA. exact MFA.
    - exact MUS.
  Qed.

  (* [comment removed for export] *)
  #[using="ARt RR W0 AI md"] Lemma pk_TM : mapped v thr 4096. Proof. exact (rk_TM A v [] ARt). Qed.

  (* [comment removed for export] *)
  Definition pk_ks0 (i : Z) : list word := words4 (rdbytes v (thr + 208 + 80 * i + 16) 64) 16.
  #[using="CE RR W0 AI md"] Lemma pk_lines0 : a_cache_inited A = false -> forall i, 1 <= i <= 31 ->
    length (pk_ks0 i) = 16%nat /\
    rw_cells rsegs v (thr + 208 + 80 * i) [C4 (wz 0); C4 (wz 0); C8 (wz 0); CB 64 (u32s (pk_ks0 i))].
  Proof.
    intros CI i Hi. split; [apply words4_length|].
    pose proof (ar_cache _ _ _ _ _ RR) as CC. unfold cache_repr_ in CC. cbv zeta in CC. (first [ dand5 CC as CL _ _ TM _ | destruct CC as (CL & _ & _ & TM & _) ]).
    (first [ pose proof ((CL i ltac:(lia))) as dR_19; dand5 dR_19 as _ Hcnt Hmax _ _ | destruct (CL i ltac:(lia)) as (_ & Hcnt & Hmax & _ & _) ]). rewrite CI in Hmax. cbn [andb] in Hmax. destruct Hmax as [Hmx Hcs].
    (first [ pose proof ((wfC A W0)) as dR_20; dand3 dR_20 as WC _ _ | destruct (wfC A W0) as (WC & _ & _) ]). (first [ pose proof ((WC i Hi)) as dR_21; dand4 dR_21 as _ _ _ EC | destruct (WC i Hi) as (_ & _ & _ & EC) ]). cbv zeta in EC. rewrite (EC CI) in Hcnt. cbn [length Z.of_nat] in Hcnt.
    unfold off_th_per_class, off_th_alloc_cache, kPerClassSize, off_pc_count, off_pc_max_count, off_pc_class_size in *.
    (first [ pose proof ((hit_place A m md AI)) as dR_22; dand3 dR_22 as TH1 TH2 _ | pose proof (hit_place A m md AI) as (TH1 & TH2 & _) ]). pose proof (aobj_facts _ _ TH1) as THF.
    assert (TMi : forall a j, thr <= a -> a + j <= thr + 4096 -> mapped v a j).
    { intros a j H1 H2 q Hq. replace (a + q) with (thr + (a - thr + q)) by lia. apply TM. lia. }
    assert (H0 : u32_at rsegs v (thr + 208 + 80 * i) 0) by (replace (thr + 208 + 80 * i) with (thr + (208 + 80 * i) + 0) by lia; exact Hcnt).
    assert (H4 : u32_at rsegs v (thr + 208 + 80 * i + 4) 0) by (replace (thr + 208 + 80 * i + 4) with (thr + (208 + 80 * i) + 4) by lia; exact Hmx).
    assert (H8 : u64_at rsegs v (thr + 208 + 80 * i + 4 + 4) 0) by (replace (thr + 208 + 80 * i + 4 + 4) with (thr + (208 + 80 * i) + 8) by lia; exact Hcs).
    change [C4 (wz 0); C4 (wz 0); C8 (wz 0); CB 64 (u32s (pk_ks0 i))] with ([C4 (wz 0)] ++ [C4 (wz 0)] ++ [C8 (wz 0)] ++ [CB 64 (u32s (pk_ks0 i))]).
    apply rw_cells_app_iff. split; [apply ro_rw; [apply u32_ro; exact H0| apply TMi; cbn; lia]|].
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
    apply rw_cells_app_iff. split; [apply ro_rw; [apply u32_ro; exact H4| apply TMi; cbn; lia]|].
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
    apply rw_cells_app_iff. split; [apply ro_rw; [apply u64_ro; exact H8| apply TMi; cbn; lia]|].
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
    unfold pk_ks0. rewrite u32s_words4 by (rewrite rdbytes_length; reflexivity).
    match goal with |- rw_cells _ _ ?a _ => replace a with (thr + 208 + 80 * i + 16) by (cbn; lia) end.
    apply (mapped_CB v (thr + 208 + 80 * i + 16) 64); [apply TMi; lia| lia| lia].
  Qed.
End Entry.
End APopK.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtS4t2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSb8o OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMallocA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalz1i.AMallocR OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalmys OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMaldga OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalrrv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASecB1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ANodeA7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ANodl61 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ATransp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ATranspR OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeRC OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeRK2.AFreeRK OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeRK2.AFreeRK3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeRW2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ABudget OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ACor4x6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APopG1.APopDefs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ATransp.APopCap OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APopG1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APopG2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APopG5.APopG3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APopG5.APopG4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APopG5 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APopP.APopK.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
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
Definition pop_Wi (slo shi thr E R fa nf nc rb mu ums mfa fam : Z) (ci : bool) : list (Z * Z) :=
  [(slo, shi); (R, R + 8); (R + 16, R + 40); (R + 48, R + 56); (R + 68, R + 69);
   (fa + 4 * nf, fa + 4 * (nf + nc)); ((if ci then thr + 2768 else thr + 288), thr + 3168); (E, E + 80);
   (rb + mu, rb + mu + ums); (sh (rb + mu), sh (rb + mu) + ums / 8);
   (fa + mfa, fa + mfa + fam); (sh (fa + mfa), sh (fa + mfa) + fam / 8)].
Lemma pop_Wi_sub_W : forall slo shi thr E R fa nf nc rb mu ums mfa fam ci,
  sub_fp (pop_Wi slo shi thr E R fa nf nc rb mu ums mfa fam ci) (pop_W slo shi thr E R fa nf nc rb mu ums mfa fam ci).
Proof. intros. unfold sub_fp, pop_Wi, pop_W. cbn [outside]. intros x Hx. tauto. Qed.
Lemma pop_Wi_mono : forall slo shi thr E R fa nf nc rb mu ums mfa fam ci nc' ums' fam',
  0 <= nc <= nc' -> 0 <= ums <= ums' -> 0 <= fam <= fam' ->
  sub_fp (pop_Wi slo shi thr E R fa nf nc rb mu ums mfa fam ci) (pop_Wi slo shi thr E R fa nf nc' rb mu ums' mfa fam' ci).
Proof.
  intros. unfold sub_fp, pop_Wi. cbn [outside]. intros x Hx.
  pose proof (Z.div_le_mono ums ums' 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_mono fam fam' 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_pos ums 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_pos fam 8 ltac:(lia) ltac:(lia)).
  repeat match goal with H : _ /\ _ |- _ => destruct H end. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try lia.
Qed.

Section Pkg.
Context {Clg : Ceiling}.
  Variables (rac spa s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : mem) (md : Model) (A : AState) (n canfill stkobj : Z).
  Hypothesis AI : @pa_ainv _ DepotRepL A m md.
  Hypothesis NR : 1 <= n <= kMaxPrimaryUser.
  Hypothesis EMP : pk_chunks (a_cache A (class_of n)) = [].
  Hypothesis SHORT : Z.of_nat (length (rg_free (a_reg A (class_of n)))) < refill_count (class_of n).
  Hypothesis CEIL : alloc_ceiling <= bv_unsigned spa - 1024.
  #[warnings="-notation-for-abbreviation"] Local Notation c := (class_of n).
  #[warnings="-notation-for-abbreviation"] Local Notation v := (aview_of (pa_hull A) m).
  #[warnings="-notation-for-abbreviation"] Local Notation sa := (bv_unsigned spa).
  #[warnings="-notation-for-abbreviation"] Local Notation thr := (p_thr (a_pl A)).
  #[warnings="-notation-for-abbreviation"] Local Notation sb := (a_sb A).
  #[warnings="-notation-for-abbreviation"] Local Notation ri := (a_ri A).
  #[warnings="-notation-for-abbreviation"] Local Notation R := (a_ri A + 128 * class_of n).
  #[warnings="-notation-for-abbreviation"] Local Notation E := (p_thr (a_pl A) + 208 + 80 * class_of n).
  #[warnings="-notation-for-abbreviation"] Local Notation rb := (region_beg (a_sb A) (class_of n)).
  #[warnings="-notation-for-abbreviation"] Local Notation fa := (region_beg (a_sb A) (class_of n) + kFreeArrayOffset).
  #[warnings="-notation-for-abbreviation"] Local Notation mu := (rg_mapped_user (a_reg A (class_of n))).
  #[warnings="-notation-for-abbreviation"] Local Notation au := (rg_allocated_user (a_reg A (class_of n))).
  #[warnings="-notation-for-abbreviation"] Local Notation mfa := (rg_mapped_fa (a_reg A (class_of n))).
  #[warnings="-notation-for-abbreviation"] Local Notation nf := (Z.of_nat (length (rg_free (a_reg A (class_of n))))).
  #[warnings="-notation-for-abbreviation"] Local Notation kk := (refill_count (class_of n)).
  #[warnings="-notation-for-abbreviation"] Local Notation U := (pop_ums A (class_of n)).
  #[warnings="-notation-for-abbreviation"] Local Notation N := (pop_nc A (class_of n)).
  #[warnings="-notation-for-abbreviation"] Local Notation Fm := (pop_fam A (class_of n)).

  Definition pk_Wi (ums fam nc : Z) : list (Z * Z) := pop_Wi (sa - 1024) sa thr E R fa nf nc rb mu ums mfa fam (a_cache_inited A).

  (* [comment removed for export] *)
  Definition carry (junk0 pad scr : list byte) (ksc : list word) (ums fam nc : Z) (w : mem) : Prop :=
    munch (pk_Wi ums fam nc) v w /\ wmono rsegs v w /\ mem_inv rsegs w /\
    rw_cells rsegs w (sa + -128) (alloc_s1a_frame spa canfill s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 rac junk0) /\
    rw_cells rsegs w (sa + -128 + -48) (comb_frameR n) /\
    rw_cells rsegs w (sa + -128 + -48 + -32) (refill_frame pad (wz E) (wz c) (wz comb_refill_ret)) /\
    rw_cells rsegs w (sa + -128 + -48 + -32 + -128) (gfa_frameR scr thr stkobj n (thr + 208) kk E) /\
    rw_cells rsegs w R [C8 (wz kMutexWriter)] /\
    length ksc = 16%nat /\
    rw_cells rsegs w E [C4 (wz 0); C4 (wz (max_count c)); C8 (wz (class_size c)); CB 64 (u32s ksc)] /\
    (a_cache_inited A = false -> forall i, 1 <= i <= 31 -> i <> c ->
       exists ks, length ks = 16%nat /\ rw_cells rsegs w (thr + 208 + 80 * i) [C4 (wz 0); C4 (wz (max_count i)); C8 (wz (class_size i)); CB 64 (u32s ks)]).

  (* [comment removed for export] *)
  Definition regw (nfv mfav auv muv : Z) (w : mem) : Prop :=
    rw_cells rsegs w (R + 16) [C8 (wz nfv)] /\ rw_cells rsegs w (R + 24) [C8 (wz mfav)] /\
    rw_cells rsegs w (R + 32) [C8 (wz auv)] /\ rw_cells rsegs w (R + 40) [C8 (wz 0)] /\ rw_cells rsegs w (R + 48) [C8 (wz muv)] /\
    rw_cells rsegs w (R + 56) [C8 (wz 0)] /\ rw_cells rsegs w (R + 68) [C1 (Z_to_bv 8 0)].

  Let W0 : WF A. Proof. exact (ai_wf _ _ _ _ _ _ _ AI). Qed.
  Let CR : 1 <= c <= 30. Proof. exact (proj1 (hit_class n NR)). Qed.
  Let CE : 0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000. Proof. exact alloc_ceiling_val. Qed.

  (* [comment removed for export] *)
  Lemma pk_UMS : 0 <= U /\ U mod kUserMapSize = 0 /\ mu + U < au + 9 * class_size c + kUserMapSize /\ au <= class_size c * (Z.of_nat (length (a_paid A c)) + 7) + class_slack c.   (* [comment removed for export] *)
  Proof. exact (proj1 (ar_ums A c W0 CR EMP SHORT)). Qed.
  Lemma pk_FAM : 0 <= Fm /\ Fm mod kFreeArrayMapSize = 0 /\ mfa + Fm <= 4 * (au / class_size c) + kFreeArrayMapSize /\ mfa + Fm <= kFreeArraySize.   (* [comment removed for export] *)
  Proof. exact (proj1 (ar_fam A c W0 CR EMP SHORT)). Qed.
  Lemma pk_NC : 0 <= N /\ au + N * class_size c <= mu + U /\ 4 * (nf + N) <= mfa + Fm.
  Proof. (first [ pose proof ((ar_nc A c W0 CR EMP SHORT)) as dR_1; dand3 dR_1 as N1 N2 _ | pose proof (ar_nc A c W0 CR EMP SHORT) as (N1 & N2 & _) ]). (first [ pose proof ((ar_fam A c W0 CR EMP SHORT)) as dR_2; dand3 dR_2 as _ F2 _ | pose proof (ar_fam A c W0 CR EMP SHORT) as (_ & F2 & _) ]). OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption. Qed.
  Lemma pk_POS : mu + U = 0 -> Fm = 0 /\ N = 0.
  Proof.
    intros Z0. exfalso. (first [ pose proof ((ar_ums A c W0 CR EMP SHORT)) as dR_3; dand3 dR_3 as _ U4 _ | pose proof (ar_ums A c W0 CR EMP SHORT) as (_ & U4 & _) ]). (first [ pose proof ((ar_ks A c W0 CR SHORT)) as dR_4; dand4 dR_4 as _ _ K3 _ | pose proof (ar_ks A c W0 CR SHORT) as (_ & _ & K3 & _) ]).
    pose proof (ar_reg A c W0 CR) as ((R1 & _) & _). lia.
  Qed.
  Definition pk_GEO := GEO A m md c U Fm N spa AI CR CEIL pk_UMS pk_FAM pk_NC.
  Definition pk_SHG := SHG A m md c U Fm N spa AI CR CEIL pk_UMS pk_FAM pk_NC pk_POS.

  Lemma pk_Wi_mono : forall ums fam nc ums' fam' nc', 0 <= ums <= ums' -> 0 <= fam <= fam' -> 0 <= nc <= nc' -> sub_fp (pk_Wi ums fam nc) (pk_Wi ums' fam' nc').
  Proof. intros ums fam nc ums' fam' nc' H1 H2 H3. unfold pk_Wi. apply pop_Wi_mono; assumption. Qed.
  (* [comment removed for export] *)
  Lemma pk_Wi_le : forall ums fam nc, 0 <= ums <= U -> 0 <= fam <= Fm -> 0 <= nc <= N -> sub_fp (pk_Wi ums fam nc) (pk_Wi U Fm N).
  Proof. intros ums fam nc H1 H2 H3. unfold pk_Wi. apply pop_Wi_mono; assumption. Qed.

  (* [comment removed for export] *)
  Lemma pk_lin :
    alloc_ceiling <= sa - 1024 /\ sa < 2^64 /\
    (4096 <= thr /\ thr + 4096 <= alloc_ceiling /\ (thr + 4096 <= 65536 \/ 6332416 <= thr) /\ (thr + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= thr)) /\
    (0x10007fff8000 <= sb /\ sb + 137438953472 + 4096 <= alloc_ceiling /\ ri = sb + 137438953472 /\ rb = sb + c * 4294967296 /\ 1 <= c <= 30) /\
    (0 <= au <= mu /\ 0 <= U /\ mu + U <= 3750000000 /\ 0 <= mfa /\ 0 <= Fm /\ mfa + Fm <= 536870912 /\ 0 <= nf /\ 0 <= N /\ 4 * nf <= mfa /\ 4 * (nf + N) <= mfa + Fm) /\
    (0x02008fff7000 <= sh (rb + mu) /\ 0 <= U / 8 /\ sh (rb + mu) + U / 8 <= sh (fa + mfa) /\ 0 <= Fm / 8 /\ sh (fa + mfa) + Fm / 8 <= 0x10007fff8000).
  Proof.
    (first [ pose proof (pk_GEO) as dR_5; dand32 dR_5 as G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 G28 G29 G30 G31 G32 | pose proof pk_GEO as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27 & G28 & G29 & G30 & G31 & G32) ]).
    (first [ pose proof (pk_SHG) as dR_6; dand14 dR_6 as S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 S12 S13 S14 | pose proof pk_SHG as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13 & S14) ]).
    (first [ pose proof ((GEOP A m md AI)) as dR_7; dand3 dR_7 as Gt _ _ | pose proof (GEOP A m md AI) as (Gt & _ & _) ]). apply aobj_facts in Gt. (first [ dand5 Gt as T1 T2 T3 T4 T5 | destruct Gt as (T1 & T2 & T3 & T4 & T5) ]).
    unfold region_beg in *. kung_all.
    assert (D1 : 0 <= U / 8) by (apply Z.div_pos; lia). assert (D2 : 0 <= Fm / 8) by (apply Z.div_pos; lia).
    assert (D3 : 0 <= mu / 8) by (apply Z.div_pos; lia). assert (D4 : 0 <= mfa / 8) by (apply Z.div_pos; lia).
    assert (D5 : (mu + U) / 8 <= 468750000) by (apply Z.div_le_upper_bound; lia).
    assert (D6 : (mfa + Fm) / 8 <= 67108864) by (apply Z.div_le_upper_bound; lia).
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; try assumption; try lia.
  Qed.

  (* [comment removed for export] *)
  Ltac wmax_tac L :=
    unfold pk_Wi, pop_Wi; cbn [disjoint_from];
    destruct L as (L1 & L2 & (T1 & T2 & T3 & T4) & (B1 & B2 & B3 & B4 & B5) & (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10) & (H1 & H2 & H3 & H4 & H5));
    unfold kFreeArrayOffset in *;
    set (S1 := sh (rb + mu)) in *; set (S2 := sh (region_beg sb c + 3758096384 + mfa)) in *; set (u8 := U / 8) in *; set (f8 := Fm / 8) in *;
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; try exact I; try (destruct (a_cache_inited A)); lia.
  Lemma pk_Wmax_img : forall a l, 0x10000 <= a -> a + l <= 0x60a000 -> disjoint_from (pk_Wi U Fm N) a l.
  Proof. intros a l A1 A2. pose proof pk_lin as L. wmax_tac L. Qed.
  Lemma pk_Wmax_hi : forall a l, sa <= a -> disjoint_from (pk_Wi U Fm N) a l.
  Proof. intros a l A1. pose proof pk_lin as L. wmax_tac L. Qed.
  Lemma pk_Wmax_ctx : disjoint_from (pk_Wi U Fm N) (p_ctx (a_pl A) + 152) 8.
  Proof.
    (first [ pose proof ((hit_place A m md AI)) as dR_9; dand6 dR_9 as _ _ _ CT1 CT2 _ | pose proof (hit_place A m md AI) as (_ & _ & _ & CT1 & CT2 & _) ]). apply aobj_facts in CT1. (first [ dand5 CT1 as C1 C2 C3 C4 C5 | destruct CT1 as (C1 & C2 & C3 & C4 & C5) ]).
    (first [ pose proof ((hit_sep A m md AI)) as dR_11; dand4 dR_11 as _ SEPc SEPtc _ | pose proof (hit_sep A m md AI) as (_ & SEPc & SEPtc & _) ]). (first [ pose proof ((ref_sep A m md n AI)) as dR_12; dand4 dR_12 as _ _ SEPcr _ | pose proof (ref_sep A m md n AI) as (_ & _ & SEPcr & _) ]). unfold apart in *.
    unfold kLowShadowMapBeg, kHighMemBeg in *. pose proof pk_lin as L. wmax_tac L.
  Qed.
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma rw_xf : forall W (w w' : mem) a cs a0 l0, rw_cells rsegs w a cs -> munch W w w' -> wmono rsegs w w' ->
    disjoint_from W a0 l0 -> a0 <= a -> a + Z.of_nat (cells_size cs) <= a0 + l0 -> rw_cells rsegs w' a cs.
  Proof. intros W w w' a cs a0 l0 H MU WM DJ H1 H2. eapply rw_cells_transport; [exact H| exact MU| exact WM| exact (disjoint_from_sub W a0 l0 _ _ DJ H1 H2)]. Qed.

  (* [comment removed for export] *)
  Lemma carry_step : forall junk0 pad scr ksc ums fam nc ums' fam' nc' W (w w' : mem),
    carry junk0 pad scr ksc ums fam nc w -> munch W w w' -> wmono rsegs w w' -> mem_inv rsegs w' ->
    sub_fp (pk_Wi ums fam nc) (pk_Wi ums' fam' nc') -> sub_fp W (pk_Wi ums' fam' nc') ->
    disjoint_from W (sa - 336) 336 -> disjoint_from W R 8 -> disjoint_from W (thr + 288) 2480 ->
    carry junk0 pad scr ksc ums' fam' nc' w'.
  Proof.
    (intros junk0 pad scr ksc ums fam nc ums' fam' nc' W w w'; (first [ intro dR_20; dand11 dR_20 as MU0 WM0 _ FA FC FR FG MX LK LN LNS | intros (MU0 & WM0 & _ & FA & FC & FR & FG & MX & LK & LN & LNS) ]); intros MU WM MI S1 S2 DF DR DL).
    unfold carry.
    split; [exact (munch_trans _ _ _ _ (munch_weaken _ _ _ _ S1 MU0) (munch_weaken _ _ _ _ S2 MU))|].
    split; [exact (wmono_trans _ _ _ _ WM0 WM)|]. split; [exact MI|].
    split; [apply (rw_xf W w w' _ _ _ _ FA MU WM DF); [lia| cbn; lia]|].
    split; [apply (rw_xf W w w' _ _ _ _ FC MU WM DF); [lia| cbn; lia]|].
    split; [apply (rw_xf W w w' _ _ _ _ FR MU WM DF); [lia| cbn; lia]|].
    split; [apply (rw_xf W w w' _ _ _ _ FG MU WM DF); [lia| cbn; lia]|].
    split; [apply (rw_xf W w w' _ _ _ _ MX MU WM DR); [lia| cbn; lia]|].
    split; [exact LK|].
    split; [apply (rw_xf W w w' _ _ _ _ LN MU WM DL); [lia| cbn; lia]|].
    intros CI i Hi NE. (first [ pose proof ((LNS CI i Hi NE)) as dR_13; dex1 dR_13 as ks; destruct dR_13 as [LKi RWi] | pose proof ((LNS CI i Hi NE)) as dR_13; dand3 dR_13 as ks LKi RWi | destruct (LNS CI i Hi NE) as (ks & LKi & RWi) ]). exists ks. split; [exact LKi|].
    apply (rw_xf W w w' _ _ _ _ RWi MU WM DL); [lia| cbn; lia].
  Qed.

  Lemma regw_step : forall nfv mfav auv muv W (w w' : mem), regw nfv mfav auv muv w -> munch W w w' -> wmono rsegs w w' ->
    disjoint_from W (R + 16) 64 -> regw nfv mfav auv muv w'.
  Proof.
    (intros nfv mfav auv muv W w w'; (first [ intro dR_21; dand7 dR_21 as R1 R2 R3 R4 R5 R6 R7 | intros (R1 & R2 & R3 & R4 & R5 & R6 & R7) ]); intros MU WM DJ). unfold regw.
    split; [apply (rw_xf W w w' _ _ _ _ R1 MU WM DJ); [lia| cbn; lia]|].
    split; [apply (rw_xf W w w' _ _ _ _ R2 MU WM DJ); [lia| cbn; lia]|].
    split; [apply (rw_xf W w w' _ _ _ _ R3 MU WM DJ); [lia| cbn; lia]|].
    split; [apply (rw_xf W w w' _ _ _ _ R4 MU WM DJ); [lia| cbn; lia]|].
    split; [apply (rw_xf W w w' _ _ _ _ R5 MU WM DJ); [lia| cbn; lia]|].
    split; [apply (rw_xf W w w' _ _ _ _ R6 MU WM DJ); [lia| cbn; lia]|].
    apply (rw_xf W w w' _ _ _ _ R7 MU WM DJ); [lia| cbn; lia].
  Qed.
  Lemma regw_entry : regw nf mfa au mu v.
  Proof.
    (first [ pose proof ((pk_region A m md n AI NR)) as dR_14; dand9 dR_14 as _ R1 R2 R3 R4 R5 R6 R7 _ | pose proof (pk_region A m md n AI NR) as (_ & R1 & R2 & R3 & R4 & R5 & R6 & R7 & _) ]). unfold regw.
    split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R5|]. split; [exact R6|]. exact R7.
  Qed.

  (* [comment removed for export] *)
  Section At.
  Variables (junk0 pad scr : list byte) (ksc : list word) (ums fam nc : Z) (w : mem).
  Hypothesis CY : carry junk0 pad scr ksc ums fam nc w.
  Hypothesis LE : sub_fp (pk_Wi ums fam nc) (pk_Wi U Fm N).
  Let MUx : munch (pk_Wi U Fm N) v w. Proof. destruct CY as (MU0 & _). exact (munch_weaken _ _ _ _ LE MU0). Qed.
  Let WMx : wmono rsegs v w. Proof. destruct CY as (_ & WM0 & _). exact WM0. Qed.

  Lemma carry_statics : pop_statics pa_tsd (p_ctx (a_pl A)) thr sb w.
  Proof.
    apply (pop_statics_munch (pk_Wi U Fm N) _ _ _ _ v w (pk_statics A m md AI) MUx); [unfold pa_tsd; lia| exact pk_Wmax_img| exact pk_Wmax_ctx].
  Qed.
  Lemma carry_ro_hi : forall a cs, ro_cells rsegs v a cs -> sa <= a -> ro_cells rsegs w a cs.
  Proof. intros a cs H Ha. eapply ro_cells_transport; [exact H| exact MUx| apply pk_Wmax_hi; exact Ha]. Qed.
  Lemma carry_bytes_hi : forall a bs, bytes_at rsegs v a bs -> sa <= a -> bytes_at rsegs w a bs.
  Proof. intros a bs H Ha. eapply bytes_at_transport; [exact H| exact MUx| apply pk_Wmax_hi; exact Ha]. Qed.
  Lemma carry_oom : exists oomb, rw_cells rsegs w 0x136e20 [C1 oomb].
  Proof.
    destruct (sec_OOM A m) as (oomb & OOM). exists oomb.
    eapply rw_cells_transport; [exact OOM| exact MUx| exact WMx| apply pk_Wmax_img; cbn; lia].
  Qed.
  Lemma carry_mapped : forall a k, mapped v a k -> 0 <= a -> (a + k <= 0x10000 \/ 0x60a000 <= a) -> a + k <= 2^64 -> mapped w a k.
  Proof. intros a k M H0 H1 H2. exact (pk_mapped_wm v w a k WMx H0 H1 H2 M). Qed.
  Lemma carry_NN : forall a, 0 <= a -> (a + 1 <= 0x10000 \/ 0x60a000 <= a) -> a < 2^64 -> v (wz a) <> None -> w (wz a) <> None.
  Proof. intros a H0 H1 H2. apply (pk_wmono_NN v w a WMx H1); lia. Qed.
  (* [comment removed for export] *)
  Lemma carry_na : exists na, rw_cells rsegs w (R + 72) [C8 na].
  Proof.
    (first [ pose proof ((pk_region A m md n AI NR)) as dR_15; dand10 dR_15 as _ _ _ _ _ _ _ _ MRI _ | pose proof (pk_region A m md n AI NR) as (_ & _ & _ & _ & _ & _ & _ & _ & MRI & _) ]). (first [ pose proof (pk_lin) as dR_16; dand5 dR_16 as L1 L2 _ (B1 & B2 & B3 & B4 & B5) _ | pose proof pk_lin as (L1 & L2 & _ & (B1 & B2 & B3 & B4 & B5) & _) ]).
    apply mapped_C8_1; [| lia| lia]. apply carry_mapped; [| lia| right; lia| lia].
    intros i Hi. replace (R + 72 + i) with (ri + (128 * c + 72 + i)) by lia. apply MRI. lia.
  Qed.
  Lemma carry_thr_mapped : forall a k, thr <= a -> a + k <= thr + 4096 -> mapped w a k.
  Proof.
    intros a k H1 H2. (first [ pose proof (pk_lin) as dR_17; dand4 dR_17 as L1 L2 (T1 & T2 & T3 & T4) _ | pose proof pk_lin as (L1 & L2 & (T1 & T2 & T3 & T4) & _) ]).
    apply carry_mapped; [| lia| lia| lia]. intros i Hi. replace (a + i) with (thr + (a - thr + i)) by lia. apply (pk_TM A m md AI). lia.
  Qed.
  Lemma carry_tst : exists mm72 mm80, rw_cells rsegs w (thr + off_th_stats + 72) [C8 mm72; C8 mm80].
  Proof. (first [ pose proof (pk_lin) as dR_18; dand4 dR_18 as L1 L2 (T1 & T2 & T3 & T4) _ | pose proof pk_lin as (L1 & L2 & (T1 & T2 & T3 & T4) & _) ]). unfold off_th_stats. apply mapped_C8_2; [apply carry_thr_mapped; lia| lia| lia]. Qed.
  Lemma carry_stm : exists statm, rw_cells rsegs w (thr + 208 + 2560 + 24) [C8 statm].
  Proof. (first [ pose proof (pk_lin) as dR_19; dand4 dR_19 as L1 L2 (T1 & T2 & T3 & T4) _ | pose proof pk_lin as (L1 & L2 & (T1 & T2 & T3 & T4) & _) ]). apply mapped_C8_1; [apply carry_thr_mapped; lia| lia| lia]. Qed.
  End At.
End Pkg.
