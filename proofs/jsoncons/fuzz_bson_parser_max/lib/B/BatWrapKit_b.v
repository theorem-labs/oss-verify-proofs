(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatSim StoreOk AsanAcct AsanPlanSoundSums HeapIface HeapIfaceA HeapIfaceABx As0Tables
     ArtMem ArtRuns ArtRunsMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatCls_b BatFp_b BatCellEx_b BatCARSpec_b BatDepot_b BatUnwind_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtBridge. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatAllocate3_b BatInv_b BatInvMallocFp_b BatInvMalloc_b BatLift_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Section Kit.
Variable FSG : Type.

#[using="Type"] Lemma art_stack_vis : forall rn (G : art_gs FSG) A lazy, art_run_ok rn -> art_lazy_ok FSG rn G A lazy ->
  forall x : word, rn_HI rn <= U x -> mkH lazy A x = false.
Proof.
  intros rn G A lazy ROK (LZ & _) x Hx. destruct (mkH lazy A x) eqn:E; [|reflexivity]. exfalso.
  unfold mkH in E. apply andb_prop in E as [E _]. specialize (LZ x E).
  rok_open ROK. geo_open GEO. unfold art_lazy_zone in LZ. destruct LZ as [Z|[Z|[[Z|Z] _]]]; lia.
Qed.

#[using="Type"] Lemma art_stack_wr : forall rn (G : art_gs FSG) A lazy (M : word -> option byte) Sp scr, art_run_ok rn -> art_lazy_ok FSG rn G A lazy ->
  rn_HI rn <= Sp - scr -> 0 <= scr -> Sp <= 2 ^ 47 ->
  (forall d (m : nat), 0 <= d -> d + Z.of_nat m <= scr -> store_ok ASEGS M (Z_to_bv 64 (Sp - scr + d)) m = true) ->
  wrA (mrestrict (mkH lazy A) M) (Sp - scr) scr.
Proof.
  intros rn G A lazy M Sp scr ROK LZ HHI Hscr HS W.
  pose proof ROK as ROK'. rok_open ROK'. geo_open GEO.
  apply (proj2 (art_wr_vis (mkH lazy A) M (Sp - scr) scr ltac:(lia) ltac:(lia) ltac:(intros x Hx; apply (art_stack_vis rn G A lazy ROK LZ); lia))).
  intros d k Hd Hk. apply W; assumption.
Qed.

#[using="Type"] Lemma art_stack_readable : forall rn (G : art_gs FSG) A lazy (M : word -> option byte) Sp top, art_run_ok rn -> art_lazy_ok FSG rn G A lazy ->
  rn_HI rn <= Sp -> top <= 2 ^ 47 + 4096 -> defined M Sp (top - Sp) -> readable8 (mrestrict (mkH lazy A) M) Sp top.
Proof.
  intros rn G A lazy M Sp top ROK LZ HHI Htop D a Ha Ha8 Hm.
  pose proof ROK as ROK'. rok_open ROK'. geo_open GEO.
  destruct (art_rdn_defined 8 (mrestrict (mkH lazy A) M) a ltac:(lia) ltac:(cbn; lia)) as (bs & Rd & Lb).
  { intros x Hx. cbn in Hx. rewrite art_byte_vis by (apply (art_stack_vis rn G A lazy ROK LZ); lia).
    pose proof (D (U x - Sp) ltac:(lia)) as Dx. replace (Sp + (U x - Sp)) with (U x) in Dx by lia. rewrite Z_to_bv_bv_unsigned in Dx. exact Dx. }
  exists (Z_to_bv 64 (bytes_le_to_Z bs)).
  pose proof (PropExec.bytes_le_to_Z_bound bs) as B. pose proof (PropExec.bytes_le_to_Z_nonneg bs) as B0. rewrite Lb in B.
  rewrite art_u_lit by (change (8 * Z.of_nat 8) with 64 in B; lia).
  unfold cell. rewrite Rd. f_equal. symmetry. apply APSX.word_to_le_bytes_of_bytes_n; [exact Lb|lia].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_live_of_binv : forall MAPS0 RESV0 NOACC0 BASE BUDGET rn log A M model,
  BInv ASEGS MAPS0 RESV0 NOACC0 (rn_HI rn) BASE BUDGET log A M model -> art_kn_ok MAPS0 RESV0 rn ->
  forall p, In p (art_live log) ->
    0 < fst p /\ 0 < snd p /\ fst p + snd p <= rn_HI rn /\ (fst p + snd p <= 0x7fff7000 \/ 0x10007fff8000 <= fst p)
    /\ (forall o, In o (art_objs rn) -> apart (fst p) (snd p) (fst o) (snd o)).
Proof.
  intros MAPS0 RESV0 NOACC0 BASE BUDGET rn log A M model B KN p Hp.
  destruct (bi_live _ _ _ _ _ _ _ _ _ _ _ B) as (LO & _). destruct (LO p Hp) as (P0 & P1 & _ & _ & P4 & P5 & P6).
  unfold SHLO, SHHI in P5. split; [exact P0|]. split; [exact P1|]. split; [exact P4|]. split; [exact P5|].
  intros o Ho. destruct (KN o Ho) as (q & Hq & Q1 & Q2). specialize (P6 q Hq). unfold apart. lia.
Qed.
End Kit.

(* [comment removed for export] *)
Lemma art_ca_events_in_fp : forall Sp t spb ris qs c km ab rz n rs l2 blk cl z, 1 <= c <= 30 -> art_cls_ok c cl -> cl_mu cl = 262144 * km ->
  (cl_cache cl = [] -> art_cls_needs_populate c cl = true -> art_cls_mfa' cl (Z.of_nat (length (cl_free cl)) + art_cls_new c cl) <= 536870912) ->
  in_ev_ranges (art_ca_events spb c cl) z -> art_malloc_fp Sp t spb ris qs c km ab rz n rs l2 blk z.
Proof.
  intros Sp t spb ris qs c km ab rz n rs l2 blk cl z Hc OK Emu Room (ev & Hev & Hz).
  pose proof OK as (_ & _ & _ & _ & _ & _ & _ & (Hmfa0 & _) & _).
  assert (RF : art_refill_fp (Sp - 2144 - 128 - 48) t spb ris qs c km z -> art_malloc_fp Sp t spb ris qs c km ab rz n rs l2 blk z).
  { intros F. right. unfold art_alloc3_fp. right. left. unfold art_ca_fp. right. left. exact F. }
  apply RF. unfold art_refill_fp. unfold art_ca_events, art_refill_events in Hev.
  destruct (cl_cache cl) eqn:Ec; [|destruct Hev]. destruct (art_cls_needs_populate c cl) eqn:NP; [|destruct Hev]. specialize (Room eq_refl eq_refl).
  destruct Hev as [<-|Hev].
  - cbn [art_ev_range fst snd] in Hz. do 5 right. left. lia.
  - match type of Hev with In _ (if ?b then _ else _) => destruct b end; [destruct Hev|]. destruct Hev as [<-|[]].
    cbn [art_ev_range fst snd] in Hz. do 6 right. left. lia.
Qed.

(* [comment removed for export] *)
Lemma art_lift_grows : forall {fx : PropExec.FPState} A0 A1 (M0 M1 : word -> option byte) model0 model1 log0 log1,
  bhist A0 M0 model0 log0 log1 A1 M1 model1 ->
  mem_grows (mrestrict (bhid A0 model0) M0) (mrestrict (bhid A1 model1) M1) ->
  (forall sfx, log1 = log0 ++ sfx -> forall x : word, in_ev_ranges sfx (U x) -> bhid A1 model1 x = false -> mrestrict (bhid A1 model1) M1 x <> None) ->
  mem_grows M0 M1.
Proof.
  intros fx A0 A1 M0 M1 model0 model1 log0 log1 (sfx & El & _ & B2 & B3 & _) GR DEF x Hx.
  destruct (bhid A1 model1 x) eqn:E1.
  - destruct (B2 x E1) as (_ & Eq). rewrite Eq. exact Hx.
  - destruct (bhid A0 model0 x) eqn:E0.
    + pose proof (DEF sfx El x (B3 x E0 E1) E1) as D. unfold mrestrict in D. rewrite E1 in D. exact D.
    + pose proof (GR x) as Gx. unfold mrestrict in Gx. rewrite E0, E1 in Gx. exact (Gx Hx).
Qed.
