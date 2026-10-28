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
     ArtMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatInitCache_b BatPopulate1_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtRuns ArtRunsMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatCls_b BatFp_b BatClsRep_b BatClsGfa2_b BatClsRefill_b BatCellEx_b BatCARSpec_b BatAlloc3Pure_b BatDepot_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtBridge. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatAllocate3_b
     BatInv_b BatInvMallocPure_b BatInvMallocFp_b BatInvMalloc_b BatLift_b BatWrapPure_b BatWrapKit_b BatWrapMallocX_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx ShadowRLawsB.      (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Lemma art_ca_events_no_null : forall spb c cl len r, ~ In (AMmapNull len r) (art_ca_events spb c cl).
Proof.
  intros spb c cl len r H. unfold art_ca_events, art_refill_events in H. destruct (cl_cache cl); [|exact H]. destruct (art_cls_needs_populate c cl); [|exact H].
  destruct H as [H|H]; [discriminate H|]. match type of H with In _ (if ?b then _ else _) => destruct b end; [exact H|]. destruct H as [H|[]]. discriminate H.
Qed.

Lemma art_ca_events_no_nr : forall spb c cl a l, ~ In (AMmapFixedNR a l) (art_ca_events spb c cl).
Proof.
  intros spb c cl a l H. unfold art_ca_events, art_refill_events in H. destruct (cl_cache cl); [|exact H]. destruct (art_cls_needs_populate c cl); [|exact H].
  destruct H as [H|H]; [discriminate H|]. match type of H with In _ (if ?b then _ else _) => destruct b end; [exact H|]. destruct H as [H|[]]. discriminate H.
Qed.

Lemma art_ca_pre_mfa_pop : forall c cl, cl_cache cl = [] -> art_cls_needs_populate c cl = true ->
  cl_mfa (art_ca_pre c cl) = art_cls_mfa' cl (Z.of_nat (length (cl_free cl)) + art_cls_new c cl).
Proof. intros c cl E NP. unfold art_ca_pre. rewrite E. rewrite art_cls_refill_eq. unfold art_cls_pre_take. rewrite NP. reflexivity. Qed.

Section ExitMem.
Variable FSG : Type.
Context {fx : PropExec.FPState}.

#[using="fx"] Lemma art_wmc_mem : forall rn (G : art_gs FSG) (A A' : list (Z * Z)) (M M1 : word -> option byte) (model model' : Model) (log' : list aev)
    (Sp n rz qz rs qr km : Z) (cl' : art_cls),
  let c := AsanTab.class_id (rs + rz) in
  let cl := g_cls FSG G c in
  let w := art_ca_cptr c cl in
  let ab := rn_spb rn + c * 2 ^ 32 + w * 16 in
  let FPL := art_malloc_fp_lin Sp (rn_t rn) (rn_spb rn) (rn_qs rn) c km w qz qr n (rn_l2 rn) (rn_blk rn) in
  art_run_ok rn -> 1 <= c <= 30 -> art_cls_ok c cl -> cl_mu cl = 262144 * km -> rz = 16 * qz -> rs = 8 * qr ->
  (cl_cache cl = [] -> art_cls_needs_populate c cl = true -> cl_mu cl + 262144 <= 3758096384
     /\ art_cls_mfa' cl (Z.of_nat (length (cl_free cl)) + art_cls_new c cl) <= 536870912) ->
  cl' = art_cls_pop (art_ca_pre c cl) ->
  log' = g_log FSG G ++ art_ca_events (rn_spb rn) c cl ->
  bhist A M model (g_log FSG G) log' A' M1 model' ->
  mem_grows (mrestrict (bhid A model) M) (mrestrict (bhid A' model') M1) ->
  (forall x : word, ~ FPL (U x) -> mrestrict (bhid A' model') M1 x = mrestrict (bhid A model) M x) ->
  wrA (mrestrict (bhid A' model') M1) (rn_spb rn + c * 2 ^ 32) (cl_mu cl') ->
  wrA (mrestrict (bhid A' model') M1) (rn_spb rn + c * 2 ^ 32 + 3758096384) (cl_mfa cl') ->
  (forall x : word, ~ FPL (U x) -> M1 x = M x)
  /\ mem_grows M M1
  /\ (forall x : word, (rn_spb rn + c * 2 ^ 32 <= U x < rn_spb rn + c * 2 ^ 32 + cl_mu cl'
                        \/ rn_spb rn + c * 2 ^ 32 + 3758096384 <= U x < rn_spb rn + c * 2 ^ 32 + 3758096384 + cl_mfa cl') -> bhid A' model' x = false).
Proof.
  intros rn G A A' M M1 model model' log' Sp n rz qz rs qr km cl' c cl w ab FPL ROK Hc OK Emu Erz16 Ers Room Ecl' Elog BH GR FR Wu Wfa.
  pose proof ROK as ROK'. rok_open ROK'. geo_open GEO.
  pose proof OK as (_ & (Hau0 & Haumu) & _ & _ & _ & Hmu3 & _ & (Hmfa0 & Hmfa1) & _).
  assert (OKp : art_cls_ok c (art_ca_pre c cl)) by (apply art_cls_ok_ca_pre; assumption).
  pose proof OKp as (_ & (Hau0' & Haumu') & _ & _ & _ & Hmu3' & _ & (Hmfa0' & Hmfa1') & _).
  assert (Emu' : cl_mu cl' = cl_mu (art_ca_pre c cl)) by (rewrite Ecl'; reflexivity).
  assert (Emfa' : cl_mfa cl' = cl_mfa (art_ca_pre c cl)) by (rewrite Ecl'; reflexivity).
  assert (VIS : forall x : word, (rn_spb rn + c * 2 ^ 32 <= U x < rn_spb rn + c * 2 ^ 32 + cl_mu cl'
                        \/ rn_spb rn + c * 2 ^ 32 + 3758096384 <= U x < rn_spb rn + c * 2 ^ 32 + 3758096384 + cl_mfa cl') -> bhid A' model' x = false).
  { intros x [Hx|Hx].
    - apply (art_vis_of_wr (bhid A' model') M1 (rn_spb rn + c * 2 ^ 32) (cl_mu cl') ltac:(lia) ltac:(rewrite Emu'; lia) ltac:(right; lia) Wu x Hx).
    - apply (art_vis_of_wr (bhid A' model') M1 (rn_spb rn + c * 2 ^ 32 + 3758096384) (cl_mfa cl') ltac:(lia) ltac:(rewrite Emfa'; lia) ltac:(right; lia) Wfa x Hx). }
  assert (EVR : forall sfx, log' = g_log FSG G ++ sfx -> forall z, in_ev_ranges sfx z ->
                  art_malloc_fp Sp (rn_t rn) (rn_spb rn) (rn_ris rn) (rn_qs rn) c km ab rz n rs (rn_l2 rn) (rn_blk rn) z).
  { intros sfx El z Hz. rewrite Elog in El. apply app_inv_head in El. subst sfx.
    apply (art_ca_events_in_fp Sp (rn_t rn) (rn_spb rn) (rn_ris rn) (rn_qs rn) c km ab rz n rs (rn_l2 rn) (rn_blk rn) cl z Hc OK Emu); [|exact Hz].
    intros E1 E2. exact (proj2 (Room E1 E2)). }
  assert (EVL : forall sfx, log' = g_log FSG G ++ sfx -> forall z, in_ev_ranges sfx z -> FPL z).
  { intros sfx El z Hz. apply (art_malloc_fp_cases Sp (rn_t rn) (rn_spb rn) (rn_ris rn) (rn_qs rn) c km ab rz n rs (rn_l2 rn) (rn_blk rn) w qz qr z Espb Eris eq_refl Erz16 Ers).
    exact (EVR sfx El z Hz). }
  split; [|split; [|exact VIS]].
  - exact (art_lift_frame A A' M M1 model model' (g_log FSG G) log' BH FPL FR EVL).
  - apply (art_lift_grows A A' M M1 model model' (g_log FSG G) log' BH GR). intros sfx El x Hz Hv.
    rewrite Elog in El. apply app_inv_head in El. subst sfx. destruct Hz as (ev & Hev & Hz).
    unfold art_ca_events, art_refill_events in Hev. destruct (cl_cache cl) eqn:Ec; [|destruct Hev]. destruct (art_cls_needs_populate c cl) eqn:NP; [|destruct Hev].
    destruct (Room eq_refl eq_refl) as (R1 & R2).
    pose proof (art_ca_pre_mu_pop c cl Ec NP) as Emp. pose proof (art_ca_pre_mfa_pop c cl Ec NP) as Emf.
    assert (D : forall a k, 0 <= a -> a + k < 2 ^ 64 -> 0x696000 <= a -> wrA (mrestrict (bhid A' model') M1) a k -> a <= U x < a + k -> mrestrict (bhid A' model') M1 x <> None).
    { intros a k Ha Hk Hoff Wr Hx. pose proof (art_wr_wview ASEGS _ a k Ha Hk Wr x Hx) as V. rewrite art_wview_off in V by lia. exact V. }
    destruct Hev as [<-|Hev].
    + cbn [art_ev_range fst snd] in Hz. apply (D (rn_spb rn + c * 2 ^ 32) (cl_mu cl') ltac:(lia) ltac:(rewrite Emu'; lia) ltac:(lia) Wu). rewrite Emu', Emp. lia.
    + match type of Hev with In _ (if ?b then _ else _) => destruct b end; [destruct Hev|]. destruct Hev as [<-|[]]. cbn [art_ev_range fst snd] in Hz.
      apply (D (rn_spb rn + c * 2 ^ 32 + 3758096384) (cl_mfa cl') ltac:(lia) ltac:(rewrite Emfa'; lia) ltac:(lia) Wfa). rewrite Emfa', Emf. lia.
Qed.
End ExitMem.

(* [comment removed for export] *)
Section ExitClient.
Variable L : asan_layout.
Hypothesis HLlo : hl_img_lo L = 0x10000.
Hypothesis HLhi : hl_img_hi L = 0x696000.
Hypothesis HLst : forall a, 0x211b08 <= a < 0x661b28 -> hl_rt_static L a.

#[using="HLlo HLhi HLst"] Lemma art_wmc_client : forall rn LB FF LK (A A' : list (Z * Z)) (M M1 : word -> option byte) (FPL : Z -> Prop) (Sp u n : Z),
  art_run_ok rn -> art_client_ok rn LB FF LK A M -> incl A A' -> mem_grows M M1 ->
  (forall x : word, ~ FPL (U x) -> M1 x = M x) ->
  blocks_apart u n LB ->
  (forall b a, In b LB -> (fst b <= a < fst b + snd b \/ in_shadow_of (fst b) (snd b) a) -> ~ FPL a) ->
  (forall a, 0 <= a < 2 ^ 64 -> art_out (art_mrep_W rn) a -> ~ FPL a) ->
  (forall a, rn_HI rn <= a -> ~ (Sp - 4096 <= a < Sp) -> ~ FPL a) ->
  (forall a, 0x10000 <= a < 0x696000 -> ~ (0x211b08 <= a < 0x661b28) -> ~ FPL a) ->
  (forall a k, ar_fs (rn_ar rn) <= a -> a + k <= ar_fs (rn_ar rn) + FS_BYTES -> art_gap (art_mrep_W rn) a k) ->
  (forall lo len a, 0 <= lo -> 0 < len -> lo + len <= 2 ^ 47 -> apart lo len (rn_spb rn) (2 ^ 37 + 4096) ->
        HeapIfaceA.S lo <= a <= HeapIfaceA.S (lo + len - 1) -> art_gap (art_mrep_W rn) a 1) ->
  (forall f, In f (FF ++ LK) -> ar_fs (rn_ar rn) <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= ar_fs (rn_ar rn) + FS_BYTES /\ 0 < ff_bytes (ff_class f)) ->
  (forall a, Sp - 4096 <= a < Sp -> M (Z_to_bv 64 a) <> None) ->
  (* [comment removed for export] *)
  rn_spb rn + 2 ^ 32 + 16 <= u -> u + n <= rn_spb rn + 2 ^ 37 -> u mod 16 = 0 -> 0 < n -> defined M1 u n -> shadow_blk M1 u n ->
  (forall x : word, 2147450880 + 8192 * rn_qs rn <= U x < 2147450880 + 8192 * rn_qs rn + 2 ^ 34 -> page_allowedb A' (page_base x) = true) ->
  art_client_ok rn ((u, n) :: LB) FF LK A' M1
  /\ ablock_range L (rn_ar rn) u n /\ fframes_apart u n (FF ++ LK) /\ aheap_pres L (rn_ar rn) LB FF Sp 4096 M M1.
Proof.
  intros rn LB FF LK A A' M M1 FPL Sp u n ROK CLI INC GRW FRF BA NFPB NFPW NFPS NFPI GFS GSH FSIN SCR Hu1 Hu2 Hu16 Hn DEFu SHu KSH.
  pose proof ROK as ROK'. rok_open ROK'. geo_open GEO.
  destruct CLI as (CB & CND & CSA1 & CSA2 & CS1 & CS2 & CS3 & CS4 & CS5 & CS6 & CSI & CSP & CS16).
  assert (EQ : forall a, 0 <= a < 2 ^ 64 -> ~ FPL a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha N. apply FRF. rewrite art_u_lit by lia. exact N. }
  assert (HIeq : ahl_ceil (rn_ar rn) = rn_HI rn) by reflexivity.
  assert (FFA : fframes_apart u n (FF ++ LK)).
  { intros f Hf. destruct (FSIN f Hf) as (F1 & F2 & _). unfold apart, FS_BYTES in *. clear - F1 F2 Afk Hu1 Hu2. lia. }
  assert (SHA : forall a0 n0, shadow_allowed A a0 n0 -> shadow_allowed A' a0 n0).
  { intros a0 n0 SA x Hx. apply (art_page_allowedb_incl A A' _ INC). exact (SA x Hx). }
  assert (SHB : forall b, In b LB -> 0 < snd b -> HAJ.shadow_blkR M (fst b) (snd b) -> HAJ.shadow_blkR M1 (fst b) (snd b)).
  { intros b Hb Hnb SB0.
    assert (T : forall j, 0 <= j -> (j < snd b / 8 \/ (j = snd b / 8 /\ snd b mod 8 <> 0)) -> forall v, byte_at M (HeapIfaceA.S (fst b) + j) v -> byte_at M1 (HeapIfaceA.S (fst b) + j) v).
    { intros j Hj0 Hj v B. destruct (CB b Hb) as (B1 & _ & _ & _ & B5 & _).
      pose proof (art_S_blk_hi (fst b) (snd b) j Hnb Hj) as H1. pose proof (art_S_ge (fst b) 0 ltac:(lia)) as H0. pose proof (art_S_lt (fst b + snd b - 1) (2 ^ 44) ltac:(rewrite HIeq in B5; lia)) as H2.
      apply (art_byte_at_eq M M1); [|exact B]. apply EQ; [lia|]. apply (NFPB b _ Hb). right. unfold in_shadow_of. lia. }
    exact (shadow_blkR_tby M M1 (fst b) (snd b) Hnb T SB0). }
  split; [|split; [|split; [exact FFA|]]].
  - (* [comment removed for export] *)
    unfold art_client_ok. split; [|split; [|split; [exact (SHA _ _ CSA1)|split; [exact (SHA _ _ CSA2)|repeat split; first [assumption|exact (SHA _ _ CSI)|lia]]]]].
    + intros b [Eb|Hb].
      * subst b. cbn [fst snd]. split; [lia|]. split; [right; lia|]. split; [exact Hu16|]. split; [exact Hn|]. split; [rewrite HIeq; lia|].
        split; [unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI; lia|]. split; [exact DEFu|]. split; [left; exact SHu|].
        split. { intros x Hx. unfold in_shadow_of in Hx. apply KSH.
                 pose proof (art_S_ge u (8192 * rn_qs rn) ltac:(lia)) as H0. pose proof (art_S_lt (u + n - 1) (8192 * rn_qs rn + 2 ^ 34) ltac:(lia)) as H2.
                 rewrite art_u_lit by lia. lia. }
        split. { cbn [lb_remove fst]. rewrite Z.eqb_refl. exact BA. }
        split; [exact FFA|]. split; [unfold apart, FS_BYTES in *; clear - Afk Hu1 Hu2; lia|]. intros _. clear - Hu1 G4. lia.
      * destruct (CB b Hb) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12).
        split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|]. split; [exact B5|]. split; [exact B6|].
        split. { intros i Hi. apply GRW. exact (B7 i Hi). }
        split; [exact (SHB b Hb B4 B8)|]. split; [exact (SHA _ _ B9)|].
        split. { cbn [lb_remove fst]. pose proof (BA b Hb) as AP. destruct (Z.eqb_spec u (fst b)) as [E|NE]; [exfalso; (clear - AP B1 B12 B4 CS1 CS6 E Flo Hn Hu1 Kspb Plo b n rn u; lia)|].
                 intros b' [Eb'|Hb']; [subst b'; cbn [fst snd]; lia|exact (B10 b' Hb')]. }
        split; [exact B11|exact B12].
    + cbn [map fst]. apply NoDup_ListNoDup. constructor; [|apply NoDup_ListNoDup; exact CND]. intros Hin. apply in_map_iff in Hin. destruct Hin as (b & Eb & Hb).
      destruct (CB b Hb) as (_ & _ & _ & B4 & _). pose proof (BA b Hb) as AP. lia.
  - (* [comment removed for export] *)
    unfold ablock_range. rewrite HLlo, HLhi. split; [lia|]. split; [right; lia|]. split; [exact Hu16|]. split; [exact Hn|]. split; [rewrite HIeq; lia|].
    unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI. lia.
  - (* [comment removed for export] *)
    split.
    + intros a Ha CLa. apply EQ; [exact Ha|]. unfold aclient, aclient_g in CLa.
      destruct CLa as [(b & Hb & Hr)|[((C1 & C2) & C3)|[((C1 & C2) & C3)|[(f & Hf & R1 & R2)|[SH|[(f & Hf & SH)|(b & Hb & SH)]]]]]].
      * apply (NFPB b a Hb). left. exact Hr.
      * apply NFPS; [rewrite <- HIeq; exact C1|exact C3].
      * rewrite HLlo in C1. rewrite HLhi in C2. apply NFPI; [lia|]. intros D. apply C3. apply HLst. exact D.
      * destruct (FSIN f (in_or_app _ _ _ (or_introl Hf))) as (F1 & F2 & _). apply NFPW; [exact Ha|]. apply (art_gap_out _ a 1); [|lia]. apply GFS; lia.
      * apply NFPW; [exact Ha|]. apply (art_gap_out _ a 1); [|lia].
        apply (GSH (ahl_ceil (rn_ar rn)) (2 ^ 47 - ahl_ceil (rn_ar rn)) a); [rewrite HIeq; lia|lia|lia|rewrite HIeq; unfold apart; lia|exact SH].
      * destruct (FSIN f (in_or_app _ _ _ (or_introl Hf))) as (F1 & F2 & F3). apply NFPW; [exact Ha|]. apply (art_gap_out _ a 1); [|lia].
        apply (GSH (ff_addr f) (ff_bytes (ff_class f)) a); [lia|exact F3|unfold FS_BYTES in *; lia|unfold apart, FS_BYTES in *; clear - F1 F2 Afk; lia|exact SH].
      * apply (NFPB b a Hb). right. exact SH.
    + intros a Ha. apply GRW. exact (SCR a Ha).
Qed.
End ExitClient.
