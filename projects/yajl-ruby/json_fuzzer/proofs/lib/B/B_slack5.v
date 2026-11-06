(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import base decidable list gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import LazyModel NodesA BackingAlgebraA.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import StdioBase STree.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState AsanOps AsanHoare AsanRep AsanFakeStack AsanPS AsanKern AsanBudget AsanBudget2 AsanGap AsanSlack.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import B_alloc_iface B_live B_budget5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition NMAXA : Z := 2^27 + 16384.
(* [comment removed for export] *)
Definition OPSLACK : Z := 2^32.
(* [comment removed for export] *)
Definition ADYN : Z := 2^43.
(* [comment removed for export] *)
Definition FOGW : Z := 2 * (8192 + NMAXA + 4095).

Lemma map_size_le_NMAXA : forall n, 0 <= n <= 2^27 -> map_size n <= NMAXA.
Proof. intros n Hn. pose proof (map_size_le n ltac:(lia)). unfold NMAXA. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mwf (l : list (word * word)) : Prop :=
  (forall i j e1 e2, nth_error l i = Some e1 -> nth_error l j = Some e2 -> i <> j -> ehi e1 <= elo e2 \/ ehi e2 <= elo e1)
  /\ Forall (fun e => 0 < bv_unsigned (snd e) /\ elo e mod 4096 = 0 /\ bv_unsigned (snd e) mod 4096 = 0
                     /\ 0 < elo e /\ ehi e <= alloc_ceiling) l.
(* [comment removed for export] *)
Definition shband_clear (e : word * word) : Prop :=
  (ehi e <= 0x7fff7000 \/ 0x8fff7000 <= elo e) /\ (ehi e <= 0x2008fff7000 \/ 0x10007fff8000 <= elo e).
(* [comment removed for export] *)
Definition nao (noacc maps : list (word * word)) : Prop :=
  forall e, In e noacc -> 0 < bv_unsigned (snd e) /\ exists m, In m maps /\ elo m <= elo e /\ ehi e <= ehi m /\ shband_clear e.
Lemma shband_clear_sub : forall e e', shband_clear e -> elo e <= elo e' -> ehi e' <= ehi e -> shband_clear e'.
Proof. intros e e' [H1 H2] A B. unfold shband_clear. lia. Qed.

Section KVM.
(* [comment removed for export] *)
Variables L0 RES0 : list (word * word).
Definition KVM (mo : Model) (a : astate) : Prop :=
  vm_reserved (m_vmmaps mo) = RES0
  /\ (exists fog, Permutation (vm_maps (m_vmmaps mo)) (L0 ++ fog ++ amaps a)
                 /\ Forall (fun e => bv_unsigned (snd e) <= 8192) fog /\ (length fog <= 2)%nat)
  /\ mwf (vm_maps (m_vmmaps mo))
  /\ model_ivs_wf mo
  /\ nao (vm_noaccess (m_vmmaps mo)) (vm_maps (m_vmmaps mo))
  /\ alloc_top (m_vmmaps mo) = alloc_ceiling.

Lemma KVM_magree : forall mo mo' a, KVM mo a -> magree mo mo' -> KVM mo' a.
Proof.
  intros mo mo' a (KR & KP & KW & KWF & KNA & KT) AG. unfold KVM. rewrite (magree_vmmaps _ _ AG).
  repeat (split; [assumption|]). split; [| split; [exact KNA| exact KT]].
  destruct AG as [M' ->]. unfold model_ivs_wf in *. destruct mo as [fd [maps lazy mat] io fs proc lim tm]. exact KWF.
Qed.
End KVM.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition PSL (R : Z) (h : VmMaps) : Prop :=
  4096 + NMAXA + gap_weight NMAXA (vm_reserved h ++ vm_maps h) + R <= alloc_top h.

Lemma PSL_PSA : forall R h, 0 <= R -> PSL R h -> PSA NMAXA h.
Proof. intros R h HR HP. unfold PSL, PSA in *. lia. Qed.
Lemma PSL_weaken : forall R R' h, R' <= R -> PSL R h -> PSL R' h.
Proof. intros R R' h LE HP. unfold PSL in *. lia. Qed.
Lemma PSL_same : forall R h h', vm_reserved h' = vm_reserved h -> vm_maps h' = vm_maps h -> alloc_top h' = alloc_top h -> PSL R h -> PSL R h'.
Proof. intros R h h' A B C HP. unfold PSL in *. rewrite A, B, C. exact HP. Qed.
(* [comment removed for export] *)
Lemma PSL_grant : forall R h h' a n,
  vm_reserved h' = vm_reserved h -> vm_maps h' = (a, n) :: vm_maps h -> alloc_top h' = alloc_top h ->
  PSL R h -> PSL (R - (bv_unsigned n + NMAXA + 4095)) h'.
Proof.
  intros R h h' a n A B C HP. unfold PSL in *. rewrite A, B, C. rewrite gap_weight_app in HP. rewrite gap_weight_app, gap_weight_cons. lia.
Qed.
Lemma PSL_remove : forall R h h' a,
  vm_reserved h' = vm_reserved h -> vm_maps h' = map_remove (vm_maps h) a -> alloc_top h' = alloc_top h -> PSL R h -> PSL R h'.
Proof.
  intros R h h' a A B C HP. unfold PSL in *. rewrite A, B, C. rewrite gap_weight_app in HP. rewrite gap_weight_app.
  pose proof (gap_weight_remove_le NMAXA (vm_maps h) a ltac:(unfold NMAXA; lia)). lia.
Qed.
(* [comment removed for export] *)
Theorem PSL_window : forall R h nZ, PSL R h -> 0 <= R -> 0 <= nZ <= NMAXA -> alloc_top h < 2^64 ->
  page_size + nZ + gap_weight nZ (vm_reserved h ++ vm_maps h) <= alloc_top h.
Proof.
  intros R h nZ HP HR HnZ HT. pose proof (PSA_mono NMAXA nZ h HnZ (PSL_PSA R h HR HP)) as X. unfold PSA, page_size in *. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section OPEN.
Variable E : aenv.

(* [comment removed for export] *)
Lemma aweight_cap : forall a,
  AWf E [] [] a -> binv a -> AQbound a -> depot_inv E a ->
  nbig_live a <= 8000 -> dep_live a <= kInitialCredit -> as_ndepot_ins a <= kInitialCredit ->
  zlen (ae_keys0 E) <= 1000 -> 0 <= ae_frames0 E <= 4096 ->
  aweight NMAXA a <= ADYN.
Proof.
  intros a WF HBI QB DI NB DL DI2 K0 FR.
  pose proof (aweight_bound E NMAXA a ltac:(unfold NMAXA; lia) WF HBI QB DI) as B.
  assert (NID : depot_n_ids E a <= 1000 + kInitialCredit).
  { destruct WF as (_ & _ & _ & _ & _ & _ & (_ & KI & _)). unfold depot_n_ids. unfold zlen in *. rewrite Nat2Z.inj_add. lia. }
  assert (D0 : 0 <= dep_live a).
  { unfold dep_live. clear. induction (live_blocks a) as [|b l IH]; cbn; [lia|]. pose proof (arefund_nonneg (snd b)). lia. }
  assert (N0 : 0 <= nbig_live a) by (unfold nbig_live; apply zlen_nonneg).
  assert (I0 : 0 <= depot_n_ids E a) by (unfold depot_n_ids; lia).
  destruct DI as (_ & _ & _ & INS0 & _).
  assert (Q1 : depot_n_ids E a / kDepotNodesPerBlock <= 1832) by (unfold kDepotNodesPerBlock, kInitialCredit in *; apply Z.div_le_upper_bound; lia).
  assert (Q2 : (ae_frames0 E + 64 * as_ndepot_ins a) / kStoreBlockFrames <= 7325) by (unfold kStoreBlockFrames, kInitialCredit in *; apply Z.div_le_upper_bound; lia).
  assert (Q1' : 0 <= depot_n_ids E a / kDepotNodesPerBlock) by (unfold kDepotNodesPerBlock; apply Z.div_pos; lia).
  assert (Q2' : 0 <= (ae_frames0 E + 64 * as_ndepot_ins a) / kStoreBlockFrames) by (unfold kStoreBlockFrames; apply Z.div_pos; lia).
  unfold ADYN, NMAXA, kDepotNodeBlockBytes, kStoreBlockBytes, kInitialCredit in *.
  clear WF HBI QB. nia.
Qed.

(* [comment removed for export] *)
Lemma fog_weight : forall fog, Forall (fun e => bv_unsigned (snd e) <= 8192) fog -> (length fog <= 2)%nat ->
  gap_weight NMAXA fog <= FOGW.
Proof.
  intros fog HF HL. rewrite gap_weight_sizes.
  assert (S : gw_sizes fog <= Z.of_nat (length fog) * 8192).
  { clear HL. induction HF as [|e l He _ IH]; cbn -[Z.of_nat]; [lia|]. rewrite Nat2Z.inj_succ. lia. }
  unfold FOGW, NMAXA. apply Nat2Z.inj_le in HL. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in HL. nia.
Qed.

(* [comment removed for export] *)
Theorem PSL_open : forall L0 RES0 mo a WS,
  KVM L0 RES0 mo a -> gap_weight NMAXA (RES0 ++ L0) <= WS ->
  AWf E [] [] a -> binv a -> AQbound a -> depot_inv E a ->
  nbig_live a <= 8000 -> dep_live a <= kInitialCredit -> as_ndepot_ins a <= kInitialCredit ->
  zlen (ae_keys0 E) <= 1000 -> 0 <= ae_frames0 E <= 4096 ->
  4096 + NMAXA + WS + FOGW + ADYN + OPSLACK <= alloc_ceiling ->
  PSL OPSLACK (m_vmmaps mo).
Proof.
  intros L0 RES0 mo a WS (KR & (fog & KP & FS & FL) & _ & _ & _ & KT) HS WF HBI QB DI NB DL DI2 NID FR NUM.
  pose proof (aweight_cap a WF HBI QB DI NB DL DI2 NID FR) as AW. pose proof (fog_weight fog FS FL) as FW.
  unfold PSL. rewrite KT, KR, gap_weight_app, (gap_weight_perm NMAXA _ _ KP), !gap_weight_app.
  rewrite gap_weight_app in HS. unfold aweight, amaps in AW. rewrite !gap_weight_app in AW. lia.
Qed.

(* [comment removed for export] *)
Corollary PSL_open_totals : forall L0 RES0 mo a SZ CNT,
  KVM L0 RES0 mo a -> gw_sizes (RES0 ++ L0) <= SZ -> Z.of_nat (length (RES0 ++ L0)) <= CNT -> 0 <= CNT ->
  AWf E [] [] a -> binv a -> AQbound a -> depot_inv E a ->
  nbig_live a <= 8000 -> dep_live a <= kInitialCredit -> as_ndepot_ins a <= kInitialCredit ->
  zlen (ae_keys0 E) <= 1000 -> 0 <= ae_frames0 E <= 4096 ->
  4096 + NMAXA + (SZ + CNT * (NMAXA + 4095)) + FOGW + ADYN + OPSLACK <= alloc_ceiling ->
  PSL OPSLACK (m_vmmaps mo).
Proof.
  intros L0 RES0 mo a SZ CNT KV HS HC HC0. apply (PSL_open L0 RES0 mo a (SZ + CNT * (NMAXA + 4095)) KV).
  apply gap_weight_of_totals; auto. unfold NMAXA; lia.
Qed.

(* [comment removed for export] *)
Corollary PSL_open_call : forall L0 RES0 mo (s : aps) LB SZ CNT,
  KVM L0 RES0 mo (aps_alloc s) -> gw_sizes (RES0 ++ L0) <= SZ -> Z.of_nat (length (RES0 ++ L0)) <= CNT -> 0 <= CNT ->
  aps_env s = E ->
  AWf E [] [] (aps_alloc s) -> binv (aps_alloc s) -> AQbound (aps_alloc s) -> depot_inv E (aps_alloc s) ->
  Permutation (map (fun b => (ab_addr b, ab_size b)) LB) (live_blocks (aps_alloc s)) -> BUDGET s LB -> nbig LB <= 8000 ->
  zlen (ae_keys0 E) <= 1000 -> 0 <= ae_frames0 E <= 4096 ->
  4096 + NMAXA + (SZ + CNT * (NMAXA + 4095)) + FOGW + ADYN + OPSLACK <= alloc_ceiling ->
  PSL OPSLACK (m_vmmaps mo).
Proof.
  intros L0 RES0 mo s LB SZ CNT KV HS HC HC0 HE WF HBI QB DI BM BU NB K0 FR NUM.
  pose proof (BUDGET_caps s LB BU) as (C1 & C2 & _ & _).
  apply (PSL_open_totals L0 RES0 mo (aps_alloc s) SZ CNT KV HS HC HC0 WF HBI QB DI); auto.
  - rewrite <- (nbigZ_live LB _ BM), <- nbig_nbigZ. exact NB.
  - rewrite <- (DEP_live LB _ BM). exact C1.
Qed.

(* [comment removed for export] *)
Example PSL_open_numerics : forall SZ CNT, SZ <= 2^44 + 2^42 -> 0 <= CNT <= 64 ->
  4096 + NMAXA + (SZ + CNT * (NMAXA + 4095)) + FOGW + ADYN + OPSLACK <= alloc_ceiling.
Proof. intros SZ CNT HS HC. pose proof alloc_ceiling_range. unfold FOGW, ADYN, OPSLACK in *. unfold NMAXA in *. nia. Qed.
End OPEN.
End RC__1.
