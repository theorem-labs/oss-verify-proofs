(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import base decidable list gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr NodesCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import AImages AImageFacts ExecA LazyModel NodesA ImplRzA Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import XB_mmap_fixed.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import StdioBase Malloc.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState AsanOps AsanFakeStack AsanPS AsanRep AsanKern AsanClient AsanBudget AsanBudget2 AsanRepFrame AsanDepot.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import B_iface BX_unreg BX_Exit BF_statics BF_fakestack_rep B_policy5 B_slack5 B_bundle B_init5 B_balloc5 B_rtok5 BF_alloc_iface BF_dput_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import LiaA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac lia ::= LiaA.liaA.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section AinvKit.
Variable E0 : aenv.
Variable FSB0 : Z.
Variable HR0 : list (Z * Z).
Variables L0 RES0 : list (word * word).
Variable EB0 : Z.
Variable PL0 : fs_plumb.
Hypothesis IC0 : ae_ic E0 = both_ic.
Hypothesis EB0_ok : 0 <= EB0 <= 2^32.

#[local] Notation RTOKc := (RTOK E0 FSB0 HR0 L0 RES0 EB0).
#[local] Notation AINVc := (AINV E0 FSB0 PL0).

(* [comment removed for export] *)
Lemma AINV_dput_statics : forall a m mo, AINVc a m mo -> dput_statics m.
Proof.
  intros a m mo (Hrep & _ & _ & _ & _ & _ & _ & _ & Hrt & _).
  destruct Hrt as (_ & [t XS] & _ & AMS & _).
  assert (US : unreg_statics m) by (unfold exit_statics in XS; decompose [and] XS; assumption).
  unreg_statics_open US.
  destruct AMS as (_ & _ & _ & GPAIR & MML & DPM & CFF & _).
  destruct Hrep as (_ & _ & _ & _ & _ & _ & _ & _ & Rglob & _).
  pose proof Rglob as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Gps & Gdy & _).
  rewrite IC0 in Gps, Gdy. cbn [aic_page_size_cached aic_dying_flag both_ic] in Gps, Gdy.
  split; [| exact CFF].
  unfold statics, GOT_PAGESIZE, GOT_CFLAGS, GOT_PAIR, V_PAGESIZE, V_CFLAGS, V_MMAP_LIMIT, V_DPM, V_ABORTFLAG.
  split; [exact GPSC|]. split; [exact GCF|]. split; [exact GPAIR|]. split; [exact Gps|]. split; [exact MML|]. split; [exact DPM| exact Gdy].
Qed.

(* [comment removed for export] *)
Lemma AINV_dput_mutexes : forall a m mo, AINVc a m mo -> dput_mutexes m.
Proof.
  intros a m mo (Hrep & _).
  destruct Hrep as (_ & _ & _ & _ & _ & _ & _ & [_ RH] & _). destruct RH as (_ & _ & _ & _ & _ & _ & _ & _ & _ & MU & MTX).
  rewrite IC0 in MU, MTX. cbn [aic_theDepot aic_stackStore both_ic] in MU, MTX.
  unfold dput_mutexes, dTD, dSS. split; [exact MU| exact MTX].
Qed.

(* [comment removed for export] *)
Lemma AINV_live_small : forall a m mo A n, AINVc a m mo -> In (A, n) (live_blocks a) -> n <= 2^27.
Proof.
  intros a m mo A n AIV Hin. destruct AIV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CS).
  destruct (live_blocks_chunk _ _ _ Hin) as (cb & cm & i & Hcm & _ & <- & _). exact (CS cb cm Hcm).
Qed.

Lemma regions_bytes_nonneg : forall a, AWf E0 [] [] a -> 0 <= regions_bytes a.
Proof.
  intros a WF. pose proof WF as (_ & [_ WR] & _). unfold regions_bytes.
  assert (H : forall l, Forall (fun c => 1 <= c <= kLargestClassID) l ->
             0 <= fold_right (fun c acc => rg_mapped_user (get_region a c) + rg_mapped_fa (get_region a c) + acc) 0 l).
  { induction l as [|c l IH]; intros F; cbn; [lia|]. inversion F; subst.
    destruct (WR c ltac:(assumption)) as (R1 & _ & _ & _ & R5 & _). unfold region_of in R1, R5. cbv zeta in R1. pose proof (IH ltac:(assumption)). clear -R1 R5 H. cbn. lia. }
  apply H. unfold classes30, kLargestClassID. repeat constructor; cbn; lia.
Qed.

Lemma sec_bytes_nonneg : forall a, AWf E0 [] [] a -> 0 <= AsanState.sec_bytes a.
Proof.
  intros a WF. pose proof WF as (_ & _ & _ & _ & _ & (_ & _ & WS3 & _) & _). unfold AsanState.sec_bytes.
  assert (H : forall l, (forall sc, In sc l -> 0 <= sc_map_size sc) -> 0 <= fold_right (fun c acc => sc_map_size c + acc) 0 l).
  { induction l as [|c l IH]; intros F; cbn; [lia|]. pose proof (F c ltac:(left; reflexivity)). pose proof (IH ltac:(intros; apply F; right; assumption)). lia. }
  apply H. intros sc Hsc. destruct (WS3 sc Hsc) as (_ & _ & _ & X & _). clear -X. lia.
Qed.

(* [comment removed for export] *)
Lemma AINV_dput_nums : forall s m mo C C',
  let a := aps_alloc s in
  AINVc a m mo -> RTOKc C C' s mo ->
  0 <= as_nprim_ever a -> 10000 * as_nprim_ever a + as_ndepot_ins a + 1 <= kInitialCredit ->
  zlen (ae_keys0 E0) <= 1000 /\ ae_frames0 E0 <= 4096 ->
  zlen (as_node_blocks a) <= 1832 /\ zlen (as_store_blocks a) <= 7400 /\ AsanState.sec_bytes a <= 2^39 /\ as_ndepot_ins a + 1 <= kInitialCredit.
Proof.
  intros s m mo C C'. cbv zeta. intros (Hrep & Hwf & Hkern & Hres & Hqb & Hdi & Hbinv & Hmi & Hrt & _) TOK NP BUD [K0 F0].
  pose proof Hdi as (D1 & D2 & D3 & D4 & D5 & D6 & D7).
  pose proof Hwf as (_ & _ & _ & _ & _ & _ & (_ & WD2 & WD3)).
  unfold depot_n_ids in D1, D5. unfold zlen in *. unfold kDepotNodesPerBlock, kStoreBlockFrames, kInitialCredit in *.
  split; [clear -D1 WD2 BUD K0 NP; nia|].
  split; [clear -D2 D3 BUD F0 NP; nia|].
  split; [| clear -BUD NP; lia].
  destruct (RTOK_elim E0 FSB0 HR0 L0 RES0 EB0 C C' s mo TOK) as (R & R' & ATK & _).
  pose proof ATK as ((HLI & _ & _) & [O1 O2] & _ & VL & _).
  pose proof (li_budget _ _ _ _ HLI) as LB. rewrite VL in LB.
  unfold aEB, B_policy5.aEB, aEBa, a_eager_bytes in LB.
  pose proof (regions_bytes_nonneg _ Hwf) as RB.
  assert (0 <= (if as_ptr_committed (aps_alloc s) =? 0 then 0 else kPtrArrayCommit)) by (unfold kPtrArrayCommit; destruct (as_ptr_committed (aps_alloc s) =? 0); lia).
  unfold kDepotNodeBlockBytes, page_size, zlen in LB. clear -LB RB H EB0_ok. lia.
Qed.
End AinvKit.
End RC__1.
