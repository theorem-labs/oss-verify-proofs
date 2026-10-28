(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatSim StoreOk AsanAcct HeapIface HeapIfaceA HeapIfaceABx As0Tables
     ArtMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatPoison_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtRuns ArtRunsMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatCls_b BatFp_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtBridge. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatSecAllocPost_b BatSecRSpec_b BatAllocate3L_b BatMallocTop3L_b
     BatInv_b BatInvMallocPure_b BatInvMallocFp_b BatInvMalloc_b BatInvMallocL_b BatLift_b BatWrapPure_b BatWrapKit_b BatWrapMallocX_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Lemma art_gr_grant : forall MAPS0 RESV0 rn log (Mx : word -> option byte) msz r,
  art_run_ok rn -> art_kn_ok MAPS0 RESV0 rn -> 73721 <= msz ->
  art_GR (KN0 MAPS0 RESV0) (rn_HI rn) log Mx msz r ->
  art_sec_grant3 (rn_HI rn) (rn_t rn) (rn_ctx rn) (rn_parr rn) (rn_spb rn) (rn_l2 rn) (rn_blk rn) msz r
  /\ (forall p, In p (art_live log) -> apart r msz (fst p) (snd p))
  /\ apart r msz (ar_fs (rn_ar rn)) FS_BYTES /\ apart r msz (rn_dtls rn) 4096 /\ apart r msz (rn_kbase rn) 0x2000011000.
Proof.
  intros MAPS0 RESV0 rn log Mx msz r ROK KN Hmsz (R1 & R2 & R3 & R4 & R5 & GK & GL).
  assert (OBJ : forall o, In o (art_objs rn) -> apart r msz (fst o) (snd o)).
  { intros o Ho. destruct (KN o Ho) as (qq & Hq & Q1 & Q2). destruct (GK qq Hq) as [Z|Z]; unfold apart; lia. }
  pose proof (OBJ _ (or_introl eq_refl)) as At. pose proof (OBJ _ (or_intror (or_introl eq_refl))) as Ac.
  pose proof (OBJ _ (or_intror (or_intror (or_introl eq_refl)))) as Ak.
  pose proof (OBJ _ (or_intror (or_intror (or_intror (or_introl eq_refl))))) as Ap.
  pose proof (OBJ _ (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl)))))) as Al.
  pose proof (OBJ _ (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl))))))) as Ab.
  pose proof (OBJ _ (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl)))))))) as Af.
  pose proof (OBJ _ (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl))))))))) as Ai1.
  pose proof (OBJ _ (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl)))))))))) as Ai2.
  pose proof (OBJ _ (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl))))))))))) as Ai3.
  pose proof (OBJ _ (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl)))))))))))) as Ai4.
  pose proof (OBJ _ (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl))))))))))))) as Ad.
  cbn [fst snd] in At, Ac, Ak, Ap, Al, Ab, Af, Ai1, Ai2, Ai3, Ai4, Ad.
  rok_open ROK. geo_open GEO.
  assert (Hri : 0x696000 <= r) by (clear - Ai1 Ai2 Ai3 Ai4 R2 Hmsz; unfold apart in *; lia).
  split; [|split; [|split; [exact Af|split; [exact Ad|exact Ak]]]].
  - split; [|split; [|split; [exact Al|exact Ab]]].
    + unfold art_sec_grant. split; [exact R1|]. split; [exact R2|]. split; [exact Hri|]. split; [exact R3|].
      split; [clear - R5; unfold appmem, BatPoison_b.SB, BatPoison_b.kHighMemBeg, SHLO, SHHI in *; lia|]. split; [exact At|]. split; [exact Ac|exact Ap].
    + clear - Ak Kspb Kend Kal. unfold apart in *. lia.
  - intros p Hp. destruct (GL p Hp) as [Z|Z]; unfold apart; lia.
Qed.

Section Credit.
Variable FSG : Type.

#[using="Type"] Lemma art_cost_sec_events : forall msz r parr nch cm, 0 <= msz -> 0 <= art_cost_sum (art_sec_events msz r parr nch cm) <= msz + msz / 8 + 8192 + 131072.
Proof.
  intros msz r parr nch cm Hm. assert (0 <= msz / 8) by (apply Z.div_pos; lia).
  unfold art_sec_events, art_cost_sum. destruct cm; cbn [fold_right art_cost]; lia.
Qed.

#[using="Type"] Lemma art_wmlx_credit : forall BUDGET rn (G : art_gs FSG) LB cr msz r u n (kb : nat) kk cost,
  art_credit_ok FSG BUDGET rn G LB cr -> g_depot FSG G = Datatypes.S kb -> 0 <= msz ->
  3 <= kk <= fst cr -> msz + msz / 8 + 8192 + 131072 + 2 ^ 19 <= cost -> cost <= snd cr ->
  art_credit_ok FSG BUDGET rn (art_gs_malloc_sec G (rn_parr rn) msz r u n kb) ((u, n) :: LB) (fst cr - kk, snd cr - cost).
Proof.
  intros BUDGET rn G LB cr msz r u n kb kk cost (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8) Edep Hm Hkk Hcost Hcost'.
  pose proof (art_cost_sec_events msz r (rn_parr rn) (Z.of_nat (length (g_sec FSG G))) (g_sec_committed FSG G) Hm) as Hev.
  pose proof (art_nq_nonneg (g_qt FSG G ++ g_qg FSG G)) as Hnq.
  unfold art_credit_ok, art_nret in *. cbn [art_gs_malloc_sec g_log g_sec g_depot g_cls g_qt g_qg fst snd length] in *.
  rewrite Nat2Z.inj_succ. rewrite art_cost_sum_app, art_live_sec_events, length_app. cbn [length]. rewrite Nat2Z.inj_succ, Nat2Z.inj_add. cbn [Z.of_nat].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [rewrite Edep in C6; lia|]. split; [lia|].
  intros c0 Hc0. destruct (C8 c0 Hc0) as (D1 & D2). split; lia.
Qed.
End Credit.

Section Lazy.
Variable FSG : Type.

#[using="Type"] Lemma art_wmlx_lazy : forall rn (G : art_gs FSG) A lazy A' lazy' msz r u n (kb : nat),
  art_lazy_ok FSG rn G A lazy -> incl A A' ->
  (forall x : word, mkH lazy' A' x = true -> mkH lazy A x = true) ->
  (forall wd, In wd A' -> In wd A \/ wd = (art_shlo r, art_shhi r msz)) ->
  0x7fff7000 <= art_shlo r -> art_shhi r msz <= 0x10007fff8000 ->
  (forall x : word, page_in_ranges (page_base x) lazy' = true -> page_in_ranges (page_base x) lazy = true) ->
  (forall x : word, rn_parr rn <= U x < rn_parr rn + 131072 -> mkH lazy' A' x = false) ->
  art_lazy_ok FSG rn (art_gs_malloc_sec G (rn_parr rn) msz r u n kb) A' lazy'.
Proof.
  intros rn G A lazy A' lazy' msz r u n kb (L1 & L2 & L3 & L4) INC B2 B4 Wlo Whi B5 VIS.
  split; [|split; [|split]].
  - intros x Hlz. destruct (page_allowedb A' (page_base x)) eqn:EA.
    + unfold page_allowedb in EA. apply existsb_exists in EA. destruct EA as (iv & Hin & Hiv). apply andb_prop in Hiv as [I1 I2].
      apply Z.leb_le in I1. apply Z.leb_le in I2. unfold page_size in I2. pose proof (art_page_base_bounds x) as PB.
      destruct (B4 iv Hin) as [Hold|Enew].
      * destruct (L2 iv Hold) as [Z|[Z|NL]]; [left; lia|right; left; lia|]. exfalso. pose proof (B5 x Hlz) as E0. rewrite (NL x ltac:(lia)) in E0. discriminate E0.
      * subst iv. cbn [fst snd] in I1, I2. left. lia.
    + assert (Hh : mkH lazy' A' x = true) by (unfold mkH; rewrite Hlz, EA; reflexivity).
      pose proof (B2 x Hh) as Hh0. unfold mkH in Hh0. apply andb_prop in Hh0 as [Hl0 _].
      destruct (L1 x Hl0) as [Z|[Z|[Z NC]]]; [left; exact Z|right; left; exact Z|]. right; right. split; [exact Z|].
      intros [RI|[(c0 & Hc0 & Zc)|(_ & P)]]; apply NC.
      * left. exact RI.
      * right; left. exists c0. split; [exact Hc0|exact Zc].
      * exfalso. rewrite (VIS x P) in Hh. discriminate Hh.
  - intros wd Hwd. destruct (B4 wd Hwd) as [Hold|Enew].
    + destruct (L2 wd Hold) as [Z|[Z|NL]]; [left; exact Z|right; left; exact Z|right; right].
      intros x Hx. destruct (page_in_ranges (page_base x) lazy') eqn:E; [|reflexivity]. pose proof (B5 x E) as E0. rewrite (NL x Hx) in E0. discriminate E0.
    + subst wd. cbn [fst snd]. left. lia.
  - intros x Hx. apply (art_page_allowedb_incl A A' _ INC). exact (L3 x Hx).
  - intros x Hx. apply (art_page_allowedb_incl A A' _ INC). exact (L4 x Hx).
Qed.
End Lazy.

(* [comment removed for export] *)
Section Eager.
Variable FSG : Type.
#[using="Type"] Lemma art_wmlx_eager : forall rn (G' : art_gs FSG) LB A lazy A' lazy' msz r u n,
  art_eager_ok LB A lazy -> A_wf A' -> art_lazy_ok FSG rn G' A' lazy' ->
  (forall x : word, page_in_ranges (page_base x) lazy' = true -> page_in_ranges (page_base x) lazy = true) ->
  (r + msz <= 0x7fff7000 \/ 0x10007fff8000 <= r) -> apart r msz (rn_blk rn) (2 ^ 23) -> apart r msz (rn_kbase rn) 0x2000011000 -> apart r msz (rn_parr rn) (2 ^ 23) ->
  r <= u -> u + n <= r + msz ->
  art_eager_ok ((u, n) :: LB) A' lazy'.
Proof.
  intros rn G' LB A lazy A' lazy' msz r u n (AW & EG) AW' (L1 & _) B5 Hh Ab Ak Ap Hu1 Hu2. split; [exact AW'|].
  intros b x [<-|Hb] Hx; cbn [fst snd] in Hx; destruct (page_in_ranges (page_base x) lazy') eqn:E; try reflexivity; exfalso.
  - unfold apart in *. destruct (L1 x E) as [Z|[Z|[[Z|Z] _]]]; lia.
  - pose proof (B5 x E) as E0. rewrite (EG b x Hb Hx) in E0. discriminate E0.
Qed.
End Eager.

