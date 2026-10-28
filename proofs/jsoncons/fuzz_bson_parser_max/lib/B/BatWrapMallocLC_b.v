(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatSim StoreOk Hoare AsanAcct HeapIface HeapIfaceA HeapIfaceABx As0Tables
     ArtMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatPoison_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtRuns ArtRunsMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatCls_b BatFp_b BatCellEx_b BatByteCell_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtBridge. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatSecAllocPost_b BatSecRSpec_b BatAllocate3L_b BatMallocTop3L_b
     BatInv_b BatInvMallocPure_b BatInvMallocFp_b BatInvMalloc_b BatInvMallocL_b BatLift_b BatWrapPure_b BatWrapKit_b BatWrapMallocX_b BatWrapMallocLX_b.
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

Lemma art_allowed_vis : forall lazy A (x : word), page_allowedb A (page_base x) = true -> mkH lazy A x = false.
Proof. intros lazy A x H. unfold mkH. rewrite H. cbn. apply andb_false_r. Qed.

Lemma art_in_sec_events : forall msz r parr nch cm z, in_ev_ranges (art_sec_events msz r parr nch cm) z ->
  art_shlo r <= z < art_shhi r msz \/ (cm = false /\ parr + 8 * nch <= z < parr + 8 * nch + 131072).
Proof.
  intros msz r parr nch cm z (ev & Hev & Hz). unfold art_sec_events in Hev. destruct Hev as [<-|Hev]; [left; exact Hz|].
  destruct cm; [destruct Hev|]. destruct Hev as [<-|[]]. right. split; [reflexivity|exact Hz].
Qed.

Section ExitMem.
Context {fx : PropExec.FPState}.

#[using="fx"] Lemma art_wmlc_mem : forall (A A' : list (Z * Z)) (M M1 : word -> option byte) (model model' : Model) (log log' : list aev)
    (Sp t parr nch r msz l2 blk : Z) (cm : bool),
  let WL := art_malloc3L_fp Sp t parr nch r msz l2 blk cm in
  log' = log ++ art_sec_events msz r parr nch cm ->
  bhist A M model log log' A' M1 model' ->
  (forall a : word, in_shadow_rw (U a) -> M1 a <> None) ->
  ((LSH_LO <= art_shlo r /\ art_shhi r msz <= LSH_HI) \/ (HSH_LO <= art_shlo r /\ art_shhi r msz <= HSH_HI)) ->
  0x696000 <= parr -> parr + 2 ^ 23 < 2 ^ 63 -> 0 <= nch <= 16384 -> (cm = false -> nch = 0) ->
  mem_grows (mrestrict (bhid A model) M) (mrestrict (bhid A' model') M1) ->
  art_agree WL (mrestrict (bhid A model) M) (mrestrict (bhid A' model') M1) ->
  (forall (x : word) b, art_shlo r <= U x < art_shhi r msz -> ~ (BatPoison_b.SB + r / 8 <= U x < BatPoison_b.SB + r / 8 + msz / 8) ->
       mrestrict (bhid A model) M x = Some b -> mrestrict (bhid A' model') M1 x = Some b) ->
  wrA (mrestrict (bhid A' model') M1) parr 131072 ->
  (forall x : word, art_out WL (U x) -> M1 x = M x)
  /\ (forall x : word, art_shlo r <= U x < art_shhi r msz -> ~ (BatPoison_b.SB + r / 8 <= U x < BatPoison_b.SB + r / 8 + msz / 8) ->
        bhid A model x = false -> M x <> None -> M1 x = M x)
  /\ mem_grows M M1
  /\ (forall x : word, parr <= U x < parr + 131072 -> bhid A' model' x = false).
Proof.
  intros A A' M M1 model model' log log' Sp t parr nch r msz l2 blk cm WL Elog BH SHD WOK Hparr Hparr' Hnch Hnch0 GRW AG WIN WP.
  assert (VISP : forall x : word, parr <= U x < parr + 131072 -> bhid A' model' x = false).
  { apply (art_vis_of_wr (bhid A' model') M1 parr 131072); [lia|lia|right; lia|exact WP]. }
  split; [|split; [|split; [|exact VISP]]].
  - (* [comment removed for export] *)
    intros x Ox. apply (art_lift_frame A A' M M1 model model' log log' BH (fun z => ~ art_out WL z)).
    + intros y NN. apply AG. unfold WL, art_malloc3L_fp in *. cbn [art_out fst snd] in *. repeat split; try exact I; intros IN; apply NN; intros O; tauto.
    + intros sfx Esfx z Hz. rewrite Elog in Esfx. apply app_inv_head in Esfx. subst sfx. intros O.
      destruct (art_in_sec_events _ _ _ _ _ _ Hz) as [Zw|(Ecm & Zp)]; unfold WL, art_malloc3L_fp in O; cbn [art_out fst snd] in O.
      * lia.
      * rewrite Ecm in O. lia.
    + intros NN. exact (NN Ox).
  - (* [comment removed for export] *)
    intros x Hx Nx Vx Dx. destruct (M x) as [b|] eqn:Eb; [|contradiction].
    assert (R0 : mrestrict (bhid A model) M x = Some b) by (unfold mrestrict; rewrite Vx; exact Eb).
    pose proof (WIN x b Hx Nx R0) as R1. unfold mrestrict in R1. destruct (bhid A' model' x); [discriminate R1|exact R1].
  - (* [comment removed for export] *)
    apply (art_lift_grows A A' M M1 model model' log log' BH GRW).
    intros sfx Esfx x Hz Vx. rewrite Elog in Esfx. apply app_inv_head in Esfx. subst sfx.
    unfold mrestrict. rewrite Vx.
    destruct (art_in_sec_events _ _ _ _ _ _ Hz) as [Zw|(Ecm & Zp)].
    + apply SHD. unfold in_shadow_rw. lia.
    + pose proof (art_wr_wview ASEGS (mrestrict (bhid A' model') M1) parr 131072 ltac:(lia) ltac:(lia) WP x) as V.
      rewrite (Hnch0 Ecm) in Zp. specialize (V ltac:(lia)). rewrite art_wview_off in V by (right; lia). unfold mrestrict in V. rewrite Vx in V. exact V.
Qed.
End ExitMem.

(* [comment removed for export] *)
Lemma art_sh_apart : forall r msz lo len a, 8 * (r / 8) = r -> 8 * (msz / 8) = msz -> 0 <= lo -> 0 < len -> apart r msz lo len ->
  in_shadow_of lo len a -> ~ (BatPoison_b.SB + r / 8 <= a < BatPoison_b.SB + r / 8 + msz / 8).
Proof.
  intros r msz lo len a E1 E2 Hlo Hlen AP (H1 & H2). unfold HeapIfaceA.S, HeapIfaceA.SB in *. unfold BatPoison_b.SB.
  pose proof (Z.mul_div_le lo 8 ltac:(lia)) as D1. pose proof (Z.mul_succ_div_gt lo 8 ltac:(lia)) as D2.
  pose proof (Z.mul_div_le (lo + len - 1) 8 ltac:(lia)) as D3. pose proof (Z.mul_succ_div_gt (lo + len - 1) 8 ltac:(lia)) as D4.
  unfold apart in AP. lia.
Qed.

Section ExitClient.
Variable L : asan_layout.
Hypothesis HLlo : hl_img_lo L = 0x10000.
Hypothesis HLhi : hl_img_hi L = 0x696000.
Hypothesis HLst : forall a, art_zone_statics a -> hl_rt_static L a.

#[using="HLlo HLhi HLst"] Lemma art_wmlc_client : forall rn LB FF LK (A A' : list (Z * Z)) (lazy : list (word * word)) (M M1 : word -> option byte) (Sp nch r msz u n : Z) (cm : bool),
  let WL := art_malloc3L_fp Sp (rn_t rn) (rn_parr rn) nch r msz (rn_l2 rn) (rn_blk rn) cm in
  art_run_ok rn -> art_client_ok rn LB FF LK A M -> incl A A' -> mem_grows M M1 ->
  (forall x : word, art_out WL (U x) -> M1 x = M x) ->
  (forall x : word, art_shlo r <= U x < art_shhi r msz -> ~ (BatPoison_b.SB + r / 8 <= U x < BatPoison_b.SB + r / 8 + msz / 8) ->
        mkH lazy A x = false -> M x <> None -> M1 x = M x) ->
  (forall a : word, in_shadow_rw (U a) -> M a <> None) ->
  rn_HI rn + 4096 <= Sp - 4096 -> Sp <= 2 ^ 47 -> 0 <= nch <= 16384 ->
  art_sec_grant3 (rn_HI rn) (rn_t rn) (rn_ctx rn) (rn_parr rn) (rn_spb rn) (rn_l2 rn) (rn_blk rn) msz r -> apart r msz (ar_fs (rn_ar rn)) FS_BYTES ->
  8 * (r / 8) = r -> 8 * (msz / 8) = msz -> 0 < msz ->
  ((LSH_LO <= art_shlo r /\ art_shhi r msz <= LSH_HI) \/ (HSH_LO <= art_shlo r /\ art_shhi r msz <= HSH_HI)) ->
  (forall b, In b LB -> apart r msz (fst b) (snd b)) ->
  (forall b a, In b LB -> fst b <= a < fst b + snd b -> art_out WL a) ->
  (forall f, In f (FF ++ LK) -> ar_fs (rn_ar rn) <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= ar_fs (rn_ar rn) + FS_BYTES /\ 0 < ff_bytes (ff_class f)) ->
  (forall a, Sp - 4096 <= a < Sp -> M (Z_to_bv 64 a) <> None) ->
  (* [comment removed for export] *)
  r + 4096 <= u -> u + n <= r + msz -> u mod 16 = 0 -> 4096 < n -> defined M1 u n -> shadow_blk M1 u n -> shadow_allowed A' u n ->
  art_client_ok rn ((u, n) :: LB) FF LK A' M1
  /\ ablock_range L (rn_ar rn) u n /\ blocks_apart u n LB /\ fframes_apart u n (FF ++ LK) /\ aheap_pres L (rn_ar rn) LB FF Sp 4096 M M1.
Proof.
  intros rn LB FF LK A A' lazy M M1 Sp nch r msz u n cm WL ROK CLI INC GRW FRF FRW SHD HS HS47 Hnch GRANT Arf E1 E2 Hmsz WOK BLK NFPB FSIN SCR Hu1 Hu2 Hu16 Hbig DEFu SHu SAu.
  assert (Hn : 0 < n) by lia.
  pose proof (art_run_ok_tail rn ROK) as (Il2 & Iblk & _).
  pose proof ROK as ROK'. rok_open ROK'. geo_open GEO.
  destruct GRANT as ((Hr4 & Hr & Hri & Hrm & APr & Art & Arc & Arp) & Ark & Arl2 & Arblk).
  destruct CLI as (CB & CND & CSA1 & CSA2 & CS1 & CS2 & CS3 & CS4 & CS5 & CS6 & CSI & CSP & CS16).
  assert (HIeq : ahl_ceil (rn_ar rn) = rn_HI rn) by reflexivity.
  unfold appmem, BatPoison_b.SB, BatPoison_b.kHighMemBeg in APr. unfold LSH_LO, LSH_HI, HSH_LO, HSH_HI in WOK.
  (* [comment removed for export] *)
  assert (SHEQ : forall lo len a, 0 <= lo -> 0 < len -> lo + len <= 2 ^ 47 -> apart r msz lo len -> in_shadow_of lo len a -> 0 <= a < 2 ^ 64 ->
                   page_allowedb A (page_base (Z_to_bv 64 a)) = true -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros lo len a Hlo Hlen Hhi AP SH Ha AL.
    assert (Ua : U (Z_to_bv 64 a : word) = a) by (apply art_u_lit; lia).
    pose proof (art_sh_apart r msz lo len a E1 E2 Hlo Hlen AP SH) as NE.
    destruct SH as (SH1 & SH2). pose proof (art_S_ge lo 0 ltac:(lia)) as B0. pose proof (art_S_lt (lo + len - 1) (2 ^ 44) ltac:(lia)) as B2.
    destruct (Z_le_dec (art_shlo r) a) as [L1|L1]; [destruct (Z_lt_dec a (art_shhi r msz)) as [L2|L2]|].
    - apply FRW; [rewrite Ua; clear - L1 L2; lia|rewrite Ua; exact NE|apply art_allowed_vis; exact AL|apply SHD; rewrite Ua; unfold in_shadow_rw, LSH_LO, LSH_HI, HSH_LO, HSH_HI; clear - CS1 CS6 Hr Hri Hmsz WOK Hu1 Plo Flo SH1 SH2 B0 B2 L1 L2; lia].
    - apply FRF. rewrite Ua. unfold WL, art_malloc3L_fp. destruct Papp as (_ & Pap & _). unfold BIGSHADOW_LO, BIGSHADOW_HI in Pap.
      set (wlo := art_shlo r) in *. set (whi := art_shhi r msz) in *.
      clear - B0 B2 SH1 SH2 L2 HS G1 G10 APr Pap Al2s Abs Hnch. unfold apart in *. cbn [art_out fst snd]. destruct cm; repeat split; try exact I; lia.
    - apply FRF. rewrite Ua. unfold WL, art_malloc3L_fp. destruct Papp as (_ & Pap & _). unfold BIGSHADOW_LO, BIGSHADOW_HI in Pap.
      set (wlo := art_shlo r) in *. set (whi := art_shhi r msz) in *.
      clear - B0 B2 SH1 SH2 L1 HS G1 G10 APr Pap Al2s Abs Hnch. unfold apart in *. cbn [art_out fst snd]. destruct cm; repeat split; try exact I; lia. }
  assert (EQ : forall a, 0 <= a < 2 ^ 64 -> art_out WL a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha O. apply FRF. rewrite art_u_lit by lia. exact O. }
  assert (BA : blocks_apart u n LB).
  { intros b Hb. pose proof (BLK b Hb) as AP. destruct (CB b Hb) as (_ & _ & _ & B4 & _). unfold apart in AP. clear - AP Hu1 Hu2 B4 Hn. lia. }
  assert (FFA : fframes_apart u n (FF ++ LK)).
  { intros f Hf. destruct (FSIN f Hf) as (F1 & F2 & _). unfold apart, FS_BYTES in *. clear - F1 F2 Arf Hu1 Hu2. lia. }
  assert (SHA : forall a0 n0, shadow_allowed A a0 n0 -> shadow_allowed A' a0 n0).
  { intros a0 n0 SA x Hx. apply (art_page_allowedb_incl A A' _ INC). exact (SA x Hx). }
  assert (SHB : forall b, In b LB -> HAJ.shadow_blkR M (fst b) (snd b) -> HAJ.shadow_blkR M1 (fst b) (snd b)).
  { intros b Hb SB0. destruct (CB b Hb) as (B1 & _ & _ & B4 & B5 & _ & _ & _ & B9 & _). rewrite HIeq in B5.
    assert (T : forall j, 0 <= j -> (j < snd b / 8 \/ (j = snd b / 8 /\ snd b mod 8 <> 0)) -> forall v, byte_at M (HeapIfaceA.S (fst b) + j) v -> byte_at M1 (HeapIfaceA.S (fst b) + j) v).
    { intros j Hj0 Hj v B. pose proof (art_S_blk_hi (fst b) (snd b) j B4 Hj) as H1. pose proof (art_S_ge (fst b) 0 ltac:(lia)) as H0. pose proof (art_S_lt (fst b + snd b - 1) (2 ^ 44) ltac:(lia)) as H2.
      apply (art_byte_at_eq M M1); [|exact B].
      apply (SHEQ (fst b) (snd b)); [lia|exact B4|lia|exact (BLK b Hb)|unfold in_shadow_of; lia|lia|apply B9; unfold in_shadow_of; lia]. }
    exact (shadow_blkR_tby M M1 (fst b) (snd b) B4 T SB0). }
  split; [|split; [|split; [exact BA|split; [exact FFA|]]]].
  - (* [comment removed for export] *)
    unfold art_client_ok. split; [|split; [|split; [exact (SHA _ _ CSA1)|split; [exact (SHA _ _ CSA2)|repeat split; first [assumption|exact (SHA _ _ CSI)|lia]]]]].
    + intros b [Eb|Hb].
      * subst b. cbn [fst snd]. split; [lia|]. split; [right; lia|]. split; [exact Hu16|]. split; [exact Hn|]. split; [rewrite HIeq; lia|].
        split; [unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI; clear - APr Hu1 Hu2 Hn Hr Hrm G2; lia|]. split; [exact DEFu|]. split; [left; exact SHu|]. split; [exact SAu|].
        split. { cbn [lb_remove fst]. rewrite Z.eqb_refl. exact BA. }
        split; [exact FFA|]. split; [unfold apart, FS_BYTES in *; clear - Arf Hu1 Hu2; lia|]. intros Hsmall. exfalso. clear - Hsmall Hbig. lia.
      * destruct (CB b Hb) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12).
        split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|]. split; [exact B5|]. split; [exact B6|].
        split. { intros i Hi. apply GRW. exact (B7 i Hi). }
        split; [exact (SHB b Hb B8)|]. split; [exact (SHA _ _ B9)|].
        split. { cbn [lb_remove fst]. pose proof (BA b Hb) as AP. destruct (Z.eqb_spec u (fst b)) as [E|NE]; [exfalso; clear - E AP B1 B2 B3 B4 B5 B6 Hn Hu1 Hu2 Hu16; lia|].
                 intros b' [Eb'|Hb']; [subst b'; cbn [fst snd]; lia|exact (B10 b' Hb')]. }
        split; [exact B11|exact B12].
    + cbn [map fst]. apply NoDup_ListNoDup. constructor; [|apply NoDup_ListNoDup; exact CND]. intros Hin. apply in_map_iff in Hin. destruct Hin as (b & Eb & Hb).
      destruct (CB b Hb) as (_ & _ & _ & B4 & _). pose proof (BA b Hb) as AP. clear - CS1 CS6 Hr Hri Hmsz Hu1 Hbig Plo Flo Eb B4 AP; lia.
  - (* [comment removed for export] *)
    unfold ablock_range. rewrite HLlo, HLhi. split; [lia|]. split; [right; lia|]. split; [exact Hu16|]. split; [exact Hn|]. split; [rewrite HIeq; lia|].
    unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI. clear - APr Hu1 Hu2 Hn Hr Hrm G2. lia.
  - (* [comment removed for export] *)
    split.
    + intros a Ha CLa. unfold aclient, aclient_g in CLa.
      destruct CLa as [(b & Hb & Hr')|[((C1 & C2) & C3)|[((C1 & C2) & C3)|[(f & Hf & R1 & R2)|[SH|[(f & Hf & SH)|(b & Hb & SH)]]]]]].
      * apply EQ; [exact Ha|]. exact (NFPB b a Hb Hr').
      * apply EQ; [exact Ha|]. rewrite HIeq in C1. unfold WL, art_malloc3L_fp. destruct Papp as (_ & Pap & _).
        set (wlo := art_shlo r) in *. set (whi := art_shhi r msz) in *.
        clear - C1 C2 C3 HS G1 G8 Hrm WOK Phi Dl2 Dblk Hnch. unfold apart in *. cbn [art_out fst snd]. destruct cm; repeat split; try exact I; lia.
      * apply EQ; [exact Ha|]. rewrite HLlo in C1. rewrite HLhi in C2.
        assert (NS : ~ art_zone_statics a) by (intros Z; apply C3; apply HLst; exact Z). unfold art_zone_statics in NS.
        unfold WL, art_malloc3L_fp. set (wlo := art_shlo r) in *. set (whi := art_shhi r msz) in *.
        clear - C1 C2 NS HS G1 G9 Hri WOK Plo Il2 Iblk Hnch. unfold apart in *. cbn [art_out fst snd]. destruct cm; repeat split; try exact I; lia.
      * apply EQ; [exact Ha|]. destruct (FSIN f (in_or_app _ _ _ (or_introl Hf))) as (F1 & F2 & _).
        unfold WL, art_malloc3L_fp. destruct Fapp as (_ & Fap & _). unfold BIGSHADOW_LO, BIGSHADOW_HI in Fap. set (wlo := art_shlo r) in *. set (whi := art_shhi r msz) in *.
        clear - R1 F1 F2 HS G1 Fhi Fimg Aft Arf Fap WOK Afp Afl Afb Hnch. unfold apart, FS_BYTES in *. cbn [art_out fst snd]. destruct cm; repeat split; try exact I; lia.
      * apply (SHEQ (ahl_ceil (rn_ar rn)) (2 ^ 47 - ahl_ceil (rn_ar rn))); [rewrite HIeq; lia|rewrite HIeq; lia|lia|rewrite HIeq; unfold apart; lia|exact SH|exact Ha|apply CSA1; exact SH].
      * destruct (FSIN f (in_or_app _ _ _ (or_introl Hf))) as (F1 & F2 & F3).
        apply (SHEQ (ff_addr f) (ff_bytes (ff_class f))); [lia|exact F3|unfold FS_BYTES in *; lia|unfold apart, FS_BYTES in *; clear - F1 F2 Arf; lia|exact SH|exact Ha|].
        apply CSA2. destruct SH as (S1 & S2). unfold in_shadow_of. split.
        -- eapply Z.le_trans; [apply (art_S_mono (ar_fs (rn_ar rn)) (ff_addr f)); lia|exact S1].
        -- eapply Z.le_trans; [exact S2|apply art_S_mono; lia].
      * destruct (CB b Hb) as (B1 & _ & _ & B4 & B5 & _ & _ & _ & B9 & _). rewrite HIeq in B5.
        apply (SHEQ (fst b) (snd b)); [lia|exact B4|lia|exact (BLK b Hb)|exact SH|exact Ha|apply B9; exact SH].
    + intros a Ha. apply GRW. exact (SCR a Ha).
Qed.
End ExitClient.
