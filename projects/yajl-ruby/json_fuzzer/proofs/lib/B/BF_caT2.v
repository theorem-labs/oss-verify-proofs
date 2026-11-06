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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr Nodes NodesCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import AImages AImageFacts ExecA LazyModel NodesA ImplRzA NodesA_mm NodesA_mmW SysStepA StepA StepA2 Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanHoare AsanPS AsanRep AsanKern AsanClient AsanWf1 AsanWf2 AsanWf3 AsanWf3b AsanWf4 AsanWf5 AsanBudget AsanBudget2 AsanDepot AsanRepFrame AsanRepFrame2 AsanHit AsanRepHitB AsanRepCaB AsanRepX AsanRealloc AsanRepRefillB AsanRefillMB AsanSlack.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import B_iface BF_place BF_fakestack_rep BF_kit BF_kit2 BF_kit3 BF_unwind B_policy5 B_slack5 B_budget5 B_live B_bundle B_benv5 B_init5 B_instD5 B_balloc5 B_bpolicy5 B_rtok5 B_bevents5 BF_alloc_iface BF_ca_iface BF_tkit BF_ainv_kit BF_caT BF_casT BF_primary1b BF_refill4 BF_refill_iface BF_refill_room BF_refillT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).
#[warnings="-notation-for-abbreviation"] Notation wz := (fun z : Z => Z_to_bv 64 z).

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import LiaA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac lia ::= LiaA.liaA.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma npc_keep : forall E c a, let a0 := upd_nprimc true c a in
     (csmall a -> csmall a0) /\ (sstats_ok a -> sstats_ok a0) /\ (res_ok a -> res_ok a0) /\ (AQbound a -> AQbound a0) /\ (depot_inv E a -> depot_inv E a0)
  /\ live_blocks a0 = live_blocks a /\ as_sec a0 = as_sec a
  /\ as_nprim_ever a0 = as_nprim_ever a + 1 /\ as_ndepot_ins a0 = as_ndepot_ins a /\ as_residue a0 = as_residue a
  /\ same_fp a a0 /\ gapR a0 = gapR a + 4096 * 160 /\ gapD a0 = gapD a
  /\ as_regions a0 = as_regions a /\ as_ptr_committed a0 = as_ptr_committed a
  /\ as_node_blocks a0 = as_node_blocks a /\ as_store_blocks a0 = as_store_blocks a
  /\ as_cache a0 = as_cache a /\ as_cache_inited a0 = as_cache_inited a /\ as_cache_allocated a0 = as_cache_allocated a.
Proof.
  intros E c a.
  assert (RB : regions_bytes (upd_nprimc true c a) = regions_bytes a) by (unfold regions_bytes, get_region; destruct a; reflexivity).
  assert (GR : gapR (upd_nprimc true c a) = gapR a + 4096 * 160) by (unfold gapR; rewrite RB; destruct a; cbn -[Z.add Z.mul Z.sub regions_bytes]; lia).
  destruct a. unfold same_fp, gapD. rewrite RB.
  repeat lazymatch goal with |- _ /\ _ => split end; first [intros H; exact H | reflexivity | exact GR].
Qed.

Lemma cp_keep : forall E c a, let a1 := cp_st E c a in
     (csmall a -> csmall a1) /\ (sstats_ok a -> sstats_ok a1) /\ (res_ok a -> res_ok a1) /\ (AQbound a -> AQbound a1) /\ (depot_inv E a -> depot_inv E a1)
  /\ live_blocks a1 = live_blocks a /\ as_sec a1 = as_sec a
  /\ as_nprim_ever a1 = as_nprim_ever a /\ as_ndepot_ins a1 = as_ndepot_ins a /\ as_residue a1 = as_residue a
  /\ same_fp a a1 /\ gapR a1 = gapR a /\ gapD a1 = gapD a
  /\ as_regions a1 = as_regions a /\ as_ptr_committed a1 = as_ptr_committed a
  /\ as_node_blocks a1 = as_node_blocks a /\ as_store_blocks a1 = as_store_blocks a
  /\ as_cache_inited a1 = as_cache_inited a /\ as_cache_allocated a1 = as_cache_allocated a + class_size c.
Proof.
  intros E c a.
  assert (RB : regions_bytes (cp_st E c a) = regions_bytes a) by (unfold regions_bytes, get_region; destruct a; reflexivity).
  assert (GR : gapR (cp_st E c a) = gapR a) by (unfold gapR; rewrite RB; destruct a; reflexivity).
  destruct a. unfold same_fp, gapD. rewrite RB.
  repeat lazymatch goal with |- _ /\ _ => split end; first [intros H; exact H | reflexivity | exact GR].
Qed.

Lemma pop_st_npc_cp : forall E n a, pop_st n a = upd_nprimc true (hc n) (cp_st E (hc n) a).
Proof. intros E n a. rewrite (pop_st_cp E). unfold cp_st. rewrite get_cache_nprimc. destruct a; reflexivity. Qed.

(* [comment removed for export] *)
Lemma ARep_npc : forall segs E b c a (m : mem), ARep segs E (DepotR segs E) a m -> ARep segs E (DepotR segs E) (upd_nprimc b c a) m.
Proof.
  intros segs E b c a m H. pose proof H as (RA & RB & RC & RD & RE & RF & RG & RH & RI & RJ).
  apply (ARep_thr_xfer segs E a (upd_nprimc b c a) m); [destruct a, b; reflexivity .. | | | | | | | | | | ];
    [exact RA| exact RB| exact RC| destruct a, b; exact RD| exact RE| exact RF| exact RG| exact RH| exact RI| exact RJ].
Qed.
Lemma ARep_npc' : forall segs E b c a (m : mem), ARep segs E (DepotR segs E) (upd_nprimc b c a) m -> ARep segs E (DepotR segs E) a m.
Proof.
  intros segs E b c a m H. pose proof H as (RA & RB & RC & RD & RE & RF & RG & RH & RI & RJ).
  apply (ARep_thr_xfer segs E (upd_nprimc b c a) a m); [destruct a, b; reflexivity .. | | | | | | | | | | ];
    [exact RA| exact RB| exact RC| destruct a, b; exact RD| exact RE| exact RF| exact RG| exact RH| exact RI| exact RJ].
Qed.

(* [comment removed for export] *)
Lemma cp_st_spec_ne : forall E c a, get_cache a c <> [] -> 1 <= c <= kLargestClassID -> AWf E [] [] a ->
  let ab := chunk_of_compact (ae_space_beg E) c (List.last (get_cache a c) 0) in
  AWf E [] [] (cp_st E c a) /\ pframe a (cp_st E c a)
  /\ as_cache_inited (cp_st E c a) = true /\ avail E [] (cp_st E c a) c ab
  /\ exists x, ab = chunk_of_compact (ae_space_beg E) c x /\ (16 * x) mod class_size c = 0.
Proof.
  intros E c a NE HC WF.
  pose proof (cache_pop_spec_ne E [] [] a c HC WF NE a eq_refl) as X.
  rewrite (cache_pop_hit_eval E c a NE) in X. cbn [sall leaf_ok] in X.
  destruct X as (W1 & PF & _ & _ & CI & AV & EX). split; [exact W1|]. split; [exact PF|]. split; [exact CI|]. split; [exact AV| exact EX].
Qed.

(* [comment removed for export] *)
Lemma arun_ca_op_miss : forall E n a fuel orc a2 evs orc', from_primary n = true -> get_cache a (malloc_class n) = [] ->
  arun fuel (refill E (hc n) (upd_nprimc true (hc n) a)) orc = Some (a2, ONorm true, evs, orc') ->
  get_cache a2 (hc n) <> [] ->
  arun fuel (ca_op E n a) orc
  = Some (cp_st E (hc n) a2, ONorm (Some (chunk_of_compact (ae_space_beg E) (hc n) (List.last (get_cache a2 (hc n)) 0))), evs, orc').
Proof.
  intros E n a fuel orc a2 evs orc' PR EMP RUN NE. unfold ca_op. rewrite PR. change (malloc_class n) with (hc n) in EMP |- *.
  unfold cache_pop. unfold abind at 1 2. cbn [aupd aget sbind snd fst]. rewrite get_cache_nprimc, EMP. unfold abind at 1. cbn [sbind aget fst snd].
  lazymatch goal with |- arun _ (sbind ?t ?k) _ = _ =>
    assert (X : arun (fuel + 0)%nat (sbind t k) orc = Some (cp_st E (hc n) a2, ONorm (Some (chunk_of_compact (ae_space_beg E) (hc n) (List.last (get_cache a2 (hc n)) 0))), evs ++ [], orc'));
    [eapply (arun_sbind t k fuel 0); [exact RUN|]|] end.
  { cbn [negb abind sbind aget aupd aret AsanOps.aret fst snd]. unfold cp_st. destruct (get_cache a2 (hc n)) as [|y l] eqn:EL; [exfalso; exact (NE eq_refl)|].
    cbn [negb abind sbind aget aupd aret AsanOps.aret fst snd arun]. reflexivity. }
  rewrite Nat.add_0_r, app_nil_r in X. exact X.
Qed.

Lemma sA_sA : forall a a' s, sA a (sA a' s) = sA a s.
Proof. intros a a' s. destruct s; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section AW.
Variable E0 : aenv.
Variable PL0 : fs_plumb.
Hypothesis ENV0 : env0_ok5 E0.
Hypothesis PL0OK : pl0_ok5 E0 PL0.

Lemma aw_ok_ceiling : forall P D P' D' (a a' : astate) lo sp iv z,
  aw_ok E0 a a' lo sp iv -> AWf E0 P D a -> AWf E0 P' D' a' -> blocks_sep E0 a' -> fst iv <= z < snd iv ->
  z < alloc_ceiling \/ (lo <= fst iv /\ snd iv <= sp).
Proof.
  intros P D P' D' a a' lo sp [x y] z H WF WF' BS Hz. pose proof alloc_ceiling_range as CR. unfold aw_ok in H. cbn [fst snd] in *.
  pose proof (proj1 WF) as WE.
  pose proof WE as (_ & _ & _ & _ & WEce & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & WEpa & _). change kResvLen with 137439023104 in *.
  pose proof PL0OK as (_ & _ & (_ & TR2 & _) & _). pose proof TR2 as (Tlo & Thi & _).
  pose proof ENV0 as (_ & _ & N3 & N4 & _). unfold placed, A_IMG_END in N3, N4.
  destruct H as [H|[(r & Hr & H1 & H2)|[(r & Hr & H1 & H2)|[H|[H|[(sc & Hsc & H1 & H2)|[(bb & Hb & H1 & H2)|[(bb & Hb & H1 & H2)|[H _]]]]]]]]].
  - right. exact H.
  - left. pose proof (img_mut_low r Hr) as X. clear -X H1 H2 Hz CR. lia.
  - left. unfold arep_thr_ranges in Hr. unfold kThrStackTop, kThrQCache, kThrCache, kPerClassSize, kNumClasses, kThrCacheStats, kThrStats, kThrUnwinding in Hr.
    repeat (destruct Hr as [<-|Hr]; [cbn [fst snd] in H1, H2; clear -H1 H2 Hz Thi; lia|]). destruct Hr.
  - left. clear -H Hz WEce. lia.
  - left. unfold kPtrArrayLen in *. clear -H Hz WEpa. lia.
  - left. destruct Hsc as [Hsc|Hsc];
      [pose proof WF as (_ & _ & _ & _ & _ & (_ & _ & S3 & _) & _)| pose proof WF' as (_ & _ & _ & _ & _ & (_ & _ & S3 & _) & _)];
      destruct (S3 sc Hsc) as (_ & _ & CE & _); clear -CE H1 H2 Hz; lia.
  - left. destruct (BS bb kDepotNodeBlockBytes (or_introl (conj Hb eq_refl))) as (_ & B2 & _). clear -B2 H1 H2 Hz. lia.
  - left. destruct (BS bb kStoreBlockBytes (or_intror (conj Hb eq_refl))) as (_ & B2 & _). clear -B2 H1 H2 Hz. lia.
  - left. unfold LSHI, B_base.A_SB in H. rewrite kHighMemBeg_val, kLowAppEnd_val in H. clear -H Hz CR. lia.
Qed.

(* [comment removed for export] *)
Lemma aw_outside_above : forall P D P' D' (a a' : astate) lo sp W z,
  Forall (aw_ok E0 a a' lo sp) W -> AWf E0 P D a -> AWf E0 P' D' a' -> blocks_sep E0 a' -> alloc_ceiling <= lo -> lo <= sp -> sp <= z -> outside W z.
Proof.
  intros P D P' D' a a' lo sp W z FW WF WF' BS LOC LO HZ.
  apply (outside_of_Forall (aw_ok E0 a a' lo sp) W z FW). intros iv Hiv Hz.
  destruct (aw_ok_ceiling P D P' D' a a' lo sp iv z Hiv WF WF' BS Hz) as [X|[X1 X2]]; [clear -X LOC LO HZ; lia| clear -X2 HZ Hz; lia].
Qed.

Lemma aw_ok_mono : forall (a b a' b' : astate) lo sp sp' iv,
  (forall sc, In sc (as_sec b) \/ In sc (as_sec b') -> In sc (as_sec a) \/ In sc (as_sec a')) ->
  (forall x, In x (as_node_blocks b') -> In x (as_node_blocks a')) -> (forall x, In x (as_store_blocks b') -> In x (as_store_blocks a')) ->
  sp <= sp' -> aw_ok E0 b b' lo sp iv -> aw_ok E0 a a' lo sp' iv.
Proof.
  intros a b a' b' lo sp sp' [x y] HS HN HT LE H. unfold aw_ok in *. cbn [fst snd] in *.
  destruct H as [H|[H|[H|[H|[H|[(sc & Hsc & H1 & H2)|[(bb & Hb & H1 & H2)|[(bb & Hb & H1 & H2)|H]]]]]]]].
  - left. clear -H LE. lia.
  - right; left; exact H.
  - do 2 right; left; exact H.
  - do 3 right; left; exact H.
  - do 4 right; left; exact H.
  - do 5 right; left. exists sc. split; [exact (HS sc Hsc)| clear -H1 H2; lia].
  - do 6 right; left. exists bb. split; [destruct Hb as [<-|Hb]; [left; reflexivity| right; exact (HN _ Hb)]| clear -H1 H2; lia].
  - do 7 right; left. exists bb. split; [destruct Hb as [<-|Hb]; [left; reflexivity| right; exact (HT _ Hb)]| clear -H1 H2; lia].
  - do 8 right. exact H.
Qed.

(* [comment removed for export] *)
Lemma ARep_high_agree : forall P D (ax : astate) (m m' : mem) lo,
  ARep bsegs E0 (DepotR bsegs E0) ax m -> AWf E0 P D ax -> blocks_sep E0 ax ->
  (forall r, In r (arep_img_ranges E0 ++ depot_static E0) -> fst (ae_img E0) <= fst r /\ fst r + snd r <= fst (ae_img E0) + snd (ae_img E0)) ->
  0x10000 <= fst (ae_img E0) ->
  alloc_ceiling <= lo ->
  wmono bsegs m m' -> (forall z, 0 <= z < 2^64 -> z < lo -> m' (wa z) = m (wa z)) ->
  ARep bsegs E0 (DepotR bsegs E0) ax m'.
Proof.
  intros P D ax m m' lo REP WF BS IMG_IN IMG_LO LOC WM AG. pose proof alloc_ceiling_range as CR.
  eapply (ARep_frame_client bsegs _ _ (DepotFP E0)); [| exact REP| exact WM|].
  - intros a0 mm mm' DD W' A'. eapply DepotR_frame; [exact DD| exact W'| exact A'].
  - intros x FPx.
    pose proof (fp_below_ceiling _ _ P D IMG_IN (DepotFP_where E0) _ _ WF BS FPx) as UB.
    assert (Hx : 0 <= x < 2^64).
    { destruct (fp_locate _ _ P D IMG_IN (DepotFP_where E0) _ _ WF BS FPx) as [(r & Hr & R)|[[R _]|[R _]]].
      - pose proof (IMG_IN r Hr). clear -H R IMG_LO UB CR. lia.
      - unfold sh_band, kLowShadowBeg, kShadowBase in R. rewrite kHighShadowBeg_val in R. clear -UB CR R. lia.
      - unfold app_addr in R. rewrite kHighMemBeg_val in R. clear -UB CR R. lia. }
    apply AG; [exact Hx| clear -UB LOC; lia].
Qed.
End AW.


(* [comment removed for export] *)
(* [comment removed for export] *)
Section CaT2.
Variable E0 : aenv.
Variable FSB0 : Z.
Variable HR0 : list (Z * Z).
Variables L0 RES0 : list (word * word).
Variable EB0 : Z.
Variable PL0 : fs_plumb.
Hypothesis HR0_ok : Forall (fun iv => fst iv <= snd iv) HR0 /\ A0_pages HR0 <= 8192.
Hypothesis EB0_ok : 0 <= EB0 <= 2^32.
Hypothesis ENV_depot : zlen (ae_keys0 E0) <= 1000 /\ 0 <= ae_frames0 E0 <= 4096.
Hypothesis ENV0 : env0_ok5 E0.
Hypothesis PL0OK : pl0_ok5 E0 PL0.
Hypothesis L0OK : l0_ok5 E0 L0 RES0.

#[local] Notation RTOKc := (RTOK E0 FSB0 HR0 L0 RES0 EB0).
#[local] Notation ATOKc := (ATOK E0 FSB0 HR0 L0 RES0 EB0).
#[local] Notation aSc := (B_bundle.aS E0 FSB0 HR0).
#[local] Notation aNc := (B_bundle.aN E0 FSB0 HR0).
#[local] Notation aEBc := (B_bundle.aEB EB0).
#[local] Notation SB := (ae_space_beg E0).
#[local] Notation T := (ae_thread E0).
#[local] Notation CA := (ae_thread E0 + 208).
#[local] Notation PP := (BF_caT.PP E0 FSB0 HR0).

Definition SIDE_miss (s : aps) (n : Z) : Prop := from_primary n = true /\ get_cache (aps_alloc s) (malloc_class n) = [].

Theorem ca_srz_miss : ca_srz_case E0 FSB0 HR0 L0 RES0 EB0 PL0 SIDE_miss.
Proof.
  intro. intros until K. cbv zeta. intros [PR EMP] KN TOK CHG GC AIV ABUD Hn NBIG SK LOC LO SPA SPH TP CONT.
  pose proof alloc_ceiling_range as CR. pose proof B_bundle.kHighMemBeg_val as KHB. pose proof kLowAppEnd_val as KLE.
  destruct AIV as (Hrep & Hwf & Hkern & Hres & Hqb & Hdi & Hbinv & Hmi & Hrt & Hss & Hcs).
  destruct (RTOK_elim _ _ _ _ _ _ _ _ _ _ TOK) as (R0 & R0' & ATK & HCR & HCR' & RLE).
  assert (ENV : ENVOK E0 FSB0 s) by exact (ATOK_ENVOK _ _ _ _ _ _ _ _ _ _ ATK).
  assert (EE : aps_env s = E0) by (destruct ENV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & EE & _); exact EE).
  set (a := aps_alloc s) in *.
  remember (bv_unsigned sp) as usp eqn:Husp.
  assert (Esp : sp = Z_to_bv 64 usp) by (rewrite Husp; symmetry; apply Z_to_bv_bv_unsigned).
  assert (USPR : 0 <= usp < 2^64) by (rewrite Husp; pose proof (bv_unsigned_in_range 64 sp) as BR; unfold bv_modulus in BR; clear -BR; lia).
  rewrite Esp in CONT |- *. clear Esp Husp. unfold K_CA in LO.
  set (c := hc n). assert (Ec : malloc_class n = c) by reflexivity. rewrite Ec in EMP.
  assert (N64 : 0 <= n <= 64512) by (pose proof (proj1 (from_primary_iff n ltac:(clear -Hn; lia)) PR); clear -H Hn; lia).
  pose proof (malloc_class_ok n N64) as [HCc NEEDc]. rewrite Ec in HCc, NEEDc.
  pose proof HCc as HC30. unfold kLargestClassID in HC30. pose proof (hint_range c HC30) as HR.
  assert (NEED : needed n = needed1 n) by (unfold needed; rewrite PR; reflexivity).
  pose proof (needed1_ge n) as NG.
  pose proof (class_size_mod c HCc) as [CSM CSZ].
  assert (SZ : 1 <= needed n <= 65536) by (rewrite NEED; clear -NG NEEDc CSZ Hn; lia).
  assert (Ecc : class_id (needed n) = c) by (rewrite NEED; reflexivity).
  (* [comment removed for export] *)
  pose proof ENV0 as ENV0'. destruct ENV0' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IMGR & _ & _ & _ & _ & _ & IC0 & TDN & DNP).
  pose proof ENV as ENV'. destruct ENV' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [EI1 EI2]). rewrite EE in EI1, EI2.
  pose proof Hrep as (Rins & Rri & Rrm & Rthr & Rsec & Rch & Rbat & Rdep & Rglob & Rsh).
  pose proof Rthr as (Ttop & T40 & Tq & Tcache & Tcst & Tst & Tby & Tunw).
  pose proof Hwf as (WE & WR & WC & _).
  pose proof WE as (WE1 & WE2 & WE3 & WE4 & WE5 & _).
  destruct PL0OK as (_ & _ & (TR1 & TR2 & _) & _). pose proof TR2 as (Tlo & Thi & Timg & Tband). unfold A_IMG_END, A_LOWAPP_END, A_HIGH_BEG in Timg, Tband.
  pose proof (rt_misc5_fsenv _ _ _ _ Hrt) as FSE.
  assert (T8 : T mod 8 = 0) by (unfold FSEnv in FSE; decompose [and] FSE; assumption).
  assert (HCA : (0x1000 <= CA /\ (CA + 2584 <= 0x10000 \/ 0x603000 <= CA)) /\ CA + 2584 <= alloc_ceiling /\ CA mod 8 = 0).
  { clear -Tlo Thi Timg T8. split; [| split; [lia| Z.div_mod_to_equations; lia]]. lia. }
  (* [comment removed for export] *)
  assert (ISB : rw_cells bsegs m 0xaaf78 [C8 (Z_to_bv 64 SB)]).
  { pose proof Rins as (Iin & _). unfold ae_instance in Iin. rewrite IC0 in Iin. cbn [aic_instance both_ic kInsSpaceBeg Z.add] in Iin.
    apply (rwc_split bsegs m _ [C8 (Z_to_bv 64 SB)] [C4 (Z_to_bv 64 4294967295); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 (ae_region_info E0)); C1 (Z_to_bv 8 0)]) in Iin.
    exact (proj1 Iin). }
  destruct (Tcache c ltac:(unfold kNumClasses; clear -HC30; lia)) as [PCR0 _].
  unfold percls_cells in PCR0. rewrite EMP in PCR0. change (zlen []) with 0 in PCR0. unfold kThrCache, kPerClassSize in PCR0.
  (* [comment removed for export] *)
  set (P := PP s mo).
  assert (PSTK : forall y k, lo <= y -> y + Z.of_nat k <= usp -> P (Z_to_bv 64 y, k)).
  { intros y k H1 H2. unfold P, BF_caT.PP. apply (pol_stack' E0 FSB0 HR0 s mo Hkern WE ENV0); clear -H1 H2 LOC SPH CR; lia. }
  assert (PCA : forall y k, CA <= y -> y + Z.of_nat k <= CA + 2584 -> P (Z_to_bv 64 y, k)).
  { intros y k H1 H2. unfold P, BF_caT.PP. apply (pol_thread' E0 FSB0 HR0 s mo Hkern WE); clear -H1 H2; lia. }
  pose proof (BF_caT.PP_KIP E0 FSB0 HR0 L0 RES0 EB0 s mo R0 R0' ATK) as KIP0.
  eapply (rzA_seg_cfg bsegs (aSc s) (aNc s) (aEBc s) P).
  { unfold A_CA, A_INST, kThrCache.
    eapply (ca_front_miss P ra (Z_to_bv 64 usp) gp tp F fc lo SB CA (needed n) LOC);
      rewrite ?unsigned_lit by exact USPR; rewrite ?Ecc;
      [ clear -LO; lia | clear -SPH; lia | exact SZ | clear -WE2 WE3 WE4 WE5 CR KHB; unfold kSpaceSize in *; lia | exact HCA
      | exact PSTK | exact PCA | exact SK | exact Hmi | exact ISB | exact PCR0 ]. }
  { exact KIP0. }
  intros ms1 mo1 HQ1 AG1 KIP1.
  destruct HQ1 as (yt0 & yt1 & ya4 & ya5 & ya6 & ya7 & m1 & -> & MU1 & WM1 & MI1 & SK1 & FR1).
  rewrite ?unsigned_lit in MU1, SK1, FR1 |- * by exact USPR. rewrite ?Ecc in FR1 |- *.
  pose proof (magree_frame _ _ AG1) as (Ffds1 & Fvm1 & Flz1 & Ffs1 & Fh1 & Ftid1 & _).
  destruct KIP1 as [KIA1 _].
  pose proof (RTOK_magree _ _ _ _ _ _ _ _ _ _ _ TOK AG1 KIA1) as TOK1.
  pose proof (AKern_frame _ _ _ _ Fvm1 Flz1 Hkern) as AK1.
  assert (AGm1 : forall z, 0 <= z < 2^64 -> z < usp - 48 -> m1 (wa z) = m (wa z)).
  { intros z Hz Zlo. apply MU1. rewrite wa_unsigned by exact Hz. cbn [outside]. clear -Zlo. split; [lia| exact I]. }
  rewrite ?Ecc.
  (* [comment removed for export] *)
  set (a0 := upd_nprimc true c a).
  pose proof (npc_keep E0 c a) as NK. cbv zeta in NK. fold a0 in NK.
  destruct NK as (Kcs & Ksst & Kres & Kqb & Kdi & Klive & Ksec & Knp & Knd & Kresd & Ksfp & KgR & KgD & Kreg & Kptr & Knb & Ksb & Kca & Kci & Kcal).
  destruct ABUD as (BU1 & BU2 & BU3).
  assert (ACH : acharge n = kCmPrim) by (unfold acharge; rewrite PR; reflexivity). unfold kCmPrim in ACH.
  assert (NP12 : 0 <= as_nprim_ever a /\ as_nprim_ever a + 1 <= 12000) by (unfold kInitialCredit in BU3; clear -BU1 BU2 BU3 ACH; lia).
  assert (WF0 : AWf E0 [] [] a0) by (eapply AWf_same_core; [| exact Hwf]; subst a0; destruct a; repeat split; reflexivity).
  assert (AK0 : AKern E0 a0 mo1) by (eapply AKern_ext; [exact Kreg| exact Kptr| exact Ksec| exact Knb| exact Ksb| exact AK1]).
  assert (BS0 : blocks_sep E0 a0) by exact (blocks_sep_of E0 a0 mo1 ENV0 WF0 AK0).
  assert (REP0 : ARep bsegs E0 (DepotR bsegs E0) a0 m1).
  { apply ARep_npc. eapply (ARep_high_agree E0 [] [] a m m1 lo Hrep Hwf (blocks_sep_of E0 a mo ENV0 Hwf Hkern)); [| | exact LOC| exact WM1|].
    - intros r Hr. pose proof (IMGR r Hr) as X. rewrite EI1. clear -X EI2. lia.
    - rewrite EI1. clear; lia.
    - intros z Hz Zlo. apply AGm1; [exact Hz| clear -Zlo LO; lia]. }
  pose proof PL0OK as ((c0 & cl & CR0 & CC1 & CC2) & (d0 & dl & DR0 & DD1 & DD2) & _ & CT & DT & _).
  pose proof CR0 as (_ & (CP1 & CP2 & _) & _). pose proof DR0 as (_ & (DP1 & DP2 & _) & _).
  assert (RTlow : forall z, rt_fpc E0 FSB0 PL0 z -> 0 <= z < alloc_ceiling).
  { intros z Hz. destruct (rt_fpc_where E0 FSB0 PL0 z Hz) as [(Z1 & _)|RH]; [clear -Z1 CR; lia|].
    unfold rt_high2 in RH. clear -RH CR Tlo Thi CT DT CP1 CP2 CC1 CC2 DP1 DP2 DD1 DD2. lia. }
  assert (RT1 : rt_misc5 FSB0 PL0 E0 m1).
  { apply (rt_misc5_agree E0 FSB0 PL0 m m1 Hrt). intros z Hz. pose proof (RTlow z Hz) as X. apply AGm1; clear -X LOC LO CR; lia. }
  assert (RINV0 : RINV E0 FSB0 PL0 [] [] a0 m1 mo1).
  { split; [exact REP0|]. split; [exact WF0|]. split; [exact AK0|]. split; [exact (Kres Hres)|]. split; [exact (Kqb Hqb)|]. split; [exact (Kdi Hdi)|].
    split; [exact MI1|]. split; [exact RT1|]. split; [exact (Ksst Hss)| exact (Kcs Hcs)]. }
  (* [comment removed for export] *)
  assert (TOK0 : RTOKc (C - 160) C' (sA a0 s) mo1).
  { rewrite <- (sA_self s) in TOK1. fold a in TOK1.
    apply (RTOK_same_fp_pay E0 FSB0 HR0 L0 RES0 EB0 C C' (C - 160) s a a0 mo1 TOK1 Ksfp); clear -KgR KgD CHG ACH; lia. }
  (* [comment removed for export] *)
  assert (ROOM : refill_room a0 c).
  { pose proof (refill_room_of_binv E0 [] [] a c Hwf Hbinv HCc ltac:(clear -NP12; lia)) as [RM _].
    unfold refill_room in RM |- *. cbv zeta in RM |- *. unfold get_region in RM |- *. rewrite Kreg, KgR.
    destruct RM as (RM1 & RM2 & RM3 & RM4 & RM5). clear -RM1 RM2 RM3 RM4 RM5. repeat split; try assumption. lia. }
  (* [comment removed for export] *)
  pose proof (refill_srz E0 FSB0 HR0 L0 RES0 EB0 PL0 HR0_ok ENV0 PL0OK L0OK) as RS. unfold refill_srz_stmt in RS.
  unfold A_REFILL, A_INST, kThrCache, kPerClassSize in RS.
  eapply (RS (Z_to_bv 64 226140) (Z_to_bv 64 (usp + -48)) gp tp yt0 yt1 t2 (Z_to_bv 64 c) (Z_to_bv 64 (CA + 80 * c)) ya4 ya5 ya6 ya7
             (Z_to_bv 64 8) (Z_to_bv 64 CA) (Z_to_bv 64 700248) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 mo1 (sA a0 s) [] [] c lo (C - 160) C' K KN);
    rewrite ?aps_alloc_sA, ?unsigned_lit by (clear -USPR SPA LO LOC CR; lia);
    [ exact TOK0 | exact RINV0 | exact HCc | subst a0; rewrite get_cache_nprimc; exact EMP | exact ROOM | rewrite Knp; clear -NP12; lia
    | exact SK1 | exact LOC | unfold K_REFILL; clear -LO; lia | clear -SPA; Z.div_mod_to_equations; lia | clear -SPH; lia | exact TP | ].
  clear RS.
  intros zt0 zt1 zt2 za1 za2 za3 za4 za5 za6 za7 zt3 zt4 zt5 zt6 m2 mo2 a2 POST.
  rewrite ?aps_alloc_sA, ?sA_sA in POST.
  destruct POST as (SK2 & WM12 & (Wr & MU12 & AWr & LBr) & RUNr & RINV2 & TOK2 & Ffs2 & Ffds2 & Ftid2 & SAME & OTH & CI2 & ZL2).
  destruct RINV2 as (REP2 & WF2 & AK2 & Hres2 & Hqb2 & Hdi2 & MI2 & RT2 & Hss2 & Hcs2).
  rewrite sA_sA in TOK2. rewrite Ffs1 in Ffs2. rewrite Ffds1 in Ffds2. rewrite Ftid1 in Ftid2.
  destruct SAME as (Sch & Sdd & Stq & Sgq & Ssec & Ssst & Ssstat & Sptr & Sky & Sfr & Snd & Snp & Srs & Snb & Ssb & Ssto & Sia & Scal & Sev & Sga & Sgm & Soom).
  assert (BS2 : blocks_sep E0 a2) by exact (blocks_sep_of E0 a2 mo2 ENV0 WF2 AK2).
  pose proof REP2 as (Rins2 & Rri2 & Rrm2 & Rthr2 & Rsec2 & Rch2 & Rbat2 & Rdep2 & Rglob2 & Rsh2).
  pose proof Rthr2 as (_ & _ & _ & Tcache2 & Tcst2 & _).
  pose proof WF2 as (WE' & WR2 & WC2' & _). pose proof WC2' as (_ & _ & WC23).
  set (l2 := get_cache a2 c) in *. set (x := List.last l2 0). set (ab := chunk_of_compact SB c x).
  assert (NE2 : l2 <> []) by (intros X; unfold zlen in ZL2; rewrite X in ZL2; cbn in ZL2; clear -ZL2 HR; lia).
  assert (LLEN : (1 <= length l2)%nat) by (clear -NE2; destruct l2; [exfalso; exact (NE2 eq_refl)| cbn; lia]).
  (* [comment removed for export] *)
  assert (FR2 : rw_cells bsegs m2 (usp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { eapply rw_cells_agree; [| exact FR1]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add]. intros z Hz.
    apply MU12. rewrite wa_unsigned by (clear -Hz USPR LO LOC CR; lia).
    eapply (aw_outside_above E0 PL0 ENV0 PL0OK [] [] [] [] a0 a2 lo (usp + -48) Wr z AWr WF0 WF2 BS2 LOC); clear -Hz LO; lia. }
  assert (ISB2 : rw_cells bsegs m2 0xaaf78 [C8 (Z_to_bv 64 SB)]).
  { pose proof Rins2 as (Iin & _). unfold ae_instance in Iin. rewrite IC0 in Iin. cbn [aic_instance both_ic kInsSpaceBeg Z.add] in Iin.
    apply (rwc_split bsegs m2 _ [C8 (Z_to_bv 64 SB)] [C4 (Z_to_bv 64 4294967295); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 (ae_region_info E0)); C1 (Z_to_bv 8 0)]) in Iin.
    exact (proj1 Iin). }
  destruct (Tcache2 c ltac:(unfold kNumClasses; clear -HC30; lia)) as [PCR2 (cjunk2 & CARR2 & CLEN2)].
  unfold percls_cells in PCR2. fold l2 in PCR2, CARR2, CLEN2. rewrite CI2, ZL2 in PCR2. rewrite (row_max_count_reg E0 c HCc), (row_class_size_reg E0 c HCc) in PCR2.
  unfold kThrCache, kPerClassSize in PCR2, CARR2.
  set (cws2 := map (fun z : Z => Z_to_bv 64 z) l2 ++ cjunk2) in CARR2.
  assert (CLEN : length cws2 = 16%nat) by (subst cws2; rewrite length_app, length_map; exact CLEN2).
  assert (CNTH : nth_error cws2 (Z.to_nat (hint c - 1)) = Some (Z_to_bv 64 x)).
  { subst cws2 x. rewrite <- ZL2. unfold zlen. replace (Z.to_nat (Z.of_nat (length l2) - 1)) with (Nat.pred (length l2)) by (clear -LLEN; lia).
    apply nth_error_map_app. apply last_nth_error. exact NE2. }
  assert (INx : In x l2) by (subst x; rewrite (app_removelast_last 0 NE2) at 2; apply in_app_iff; right; left; reflexivity).
  destruct (WC23 c HCc) as (_ & _ & WCx). destruct (WCx x INx) as (CARVED & XAL & XNF).
  destruct (proj2 WR2 c HCc) as (RG1 & RG2 & RG3 & _). cbv zeta in RG1, RG2, RG3. unfold region_of in RG1, RG2, RG3.
  pose proof CARVED as (kx & Kx0 & KxE & KxB). unfold chunk_of_compact, region_beg in KxE. unfold region_of in KxB.
  assert (XR : 0 <= x < 2^28) by (unfold kFreeArrayOffset in RG3; unfold kRegionSize in KxE; clear -Kx0 KxE KxB RG1 RG3 CSZ; nia).
  assert (Eab : ab = SB + c * 2^32 + 16 * x) by (subst ab; unfold chunk_of_compact, region_beg, kRegionSize; reflexivity).
  assert (CST2 : rw_cells bsegs m2 (CA + 2576) [C8 (Z_to_bv 64 (as_cache_allocated a2))]).
  { unfold kThrCacheStats in Tcst2. apply (rwc_split bsegs m2 _ [C8 (Z_to_bv 64 (as_cache_allocated a2))] [C8 (Z_to_bv 64 (as_cache_mapped a2))]) in Tcst2.
    replace (CA + 2576) with (T + (208 + 2560) + 16) by (clear; lia). exact (proj1 Tcst2). }
  (* [comment removed for export] *)
  destruct (RTOK_elim _ _ _ _ _ _ _ _ _ _ TOK2) as (R2 & R2' & ATK2 & _).
  assert (ENV2 : ENVOK E0 FSB0 (sA a2 s)) by exact (ATOK_ENVOK _ _ _ _ _ _ _ _ _ _ ATK2).
  assert (AK2' : AKern E0 (aps_alloc (sA a2 s)) mo2) by (rewrite aps_alloc_sA; exact AK2).
  set (P2 := PP (sA a2 s) mo2).
  assert (PSTK2 : forall y k, lo <= y -> y + Z.of_nat k <= usp -> P2 (Z_to_bv 64 y, k)).
  { intros y k H1 H2. unfold P2, BF_caT.PP. apply (pol_stack' E0 FSB0 HR0 (sA a2 s) mo2 AK2' WE ENV0); clear -H1 H2 LOC SPH CR; lia. }
  assert (PDAT2 : forall y k, 0xa5000 <= y -> y + Z.of_nat k <= 0x603000 -> P2 (Z_to_bv 64 y, k)).
  { intros y k H1 H2. unfold P2, BF_caT.PP. apply (pol_img' E0 FSB0 HR0 (sA a2 s) mo2 AK2' WE ENV2 ENV0); clear -H1 H2; lia. }
  assert (PCA2 : forall y k, CA <= y -> y + Z.of_nat k <= CA + 2584 -> P2 (Z_to_bv 64 y, k)).
  { intros y k H1 H2. unfold P2, BF_caT.PP. apply (pol_thread' E0 FSB0 HR0 (sA a2 s) mo2 AK2' WE); clear -H1 H2; lia. }
  pose proof (BF_caT.PP_KIP E0 FSB0 HR0 L0 RES0 EB0 (sA a2 s) mo2 R2 R2' ATK2) as KIP2.
  eapply (rzA_seg_cfg bsegs (aSc (sA a2 s)) (aNc (sA a2 s)) (aEBc (sA a2 s)) P2).
  { replace (ret_pc (Z_to_bv 64 226140)) with (Z_to_bv 64 0x3735c) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    pose proof (ca_back_ok P2 ra (Z_to_bv 64 usp) gp tp F fc lo SB CA (needed n) LOC) as CB.
    rewrite !unsigned_lit in CB by exact USPR. rewrite !Ecc in CB.
    eapply CB; clear CB;
      [ clear -LO; lia | exact SZ | clear -WE2 WE3 WE4 WE5 CR KHB; unfold kSpaceSize in *; lia | exact HCA
      | exact PSTK2 | exact PDAT2 | exact PCA2 | exact MI2 | exact SK2 | exact FR2 | exact ISB2 | exact PCR2 | exact CARR2 | exact CLEN | exact CNTH
      | clear -XR; lia | exact CST2 ]. }
  { exact KIP2. }
  intros ms3 mo3 HQ3 AG3 KIP3. unfold ca_ret_ok in HQ3. rewrite ?unsigned_lit in HQ3 by exact USPR. rewrite ?Ecc in HQ3.
  destruct HQ3 as (xt0 & xt1 & xt2 & xa1 & xa2 & xa3 & xa4 & xa5 & xa6 & xa7 & xt3 & xt4 & xt5 & xt6 & m3 & -> & MU23 & WM23 & MI3 & SK3 & ROW3 & _ & CST3).
  pose proof (magree_frame _ _ AG3) as (Ffds3 & Fvm3 & Flz3 & Ffs3 & Fh3 & Ftid3 & _).
  destruct KIP3 as [KIA3 _].
  pose proof (RTOK_magree _ _ _ _ _ _ _ _ _ _ _ TOK2 AG3 KIA3) as TOK3.
  pose proof (AKern_frame _ _ _ _ Fvm3 Flz3 AK2) as AK3.
  (* [comment removed for export] *)
  destruct (cp_st_spec_ne E0 c a2 NE2 HCc WF2) as (WF3 & PF3 & CI3 & AV3 & EXX). fold l2 x in AV3, EXX. fold ab in AV3, EXX.
  set (a3 := cp_st E0 c a2) in *.
  pose proof (cp_keep E0 c a2) as CK. cbv zeta in CK. fold a3 in CK.
  destruct CK as (Ccs & Csst & Cres & Cqb & Cdi & Clive & Csec & Cnp & Cnd & Cresd & Csfp & CgR & CgD & Creg & Cptr & Cnb & Csb & Cci & Ccal).
  assert (AK3' : AKern E0 a3 mo3) by (eapply AKern_ext; [exact Creg| exact Cptr| exact Csec| exact Cnb| exact Csb| exact AK3]).
  (* [comment removed for export] *)
  assert (OUT : forall z, z < usp - 48 -> (z < CA + 80 * c \/ CA + 80 * c + 4 <= z) -> (z < CA + 2576 \/ CA + 2584 <= z) -> 0 <= z -> m3 (wa z) = m2 (wa z)).
  { intros z Z1 Z2 Z3 Z0. apply MU23. rewrite wa_unsigned by (clear -Z0 Z1 SPH; lia). cbn [outside]. clear -Z1 Z2 Z3. repeat split; try exact I; lia. }
  (* [comment removed for export] *)
  assert (REP3 : ARep bsegs E0 (DepotR bsegs E0) a3 m3).
  { apply (ARep_npc' bsegs E0 true c). subst a3. rewrite <- (pop_st_npc_cp E0 n a2).
    eapply (ARep_capop bsegs E0 n a2 m2 m3 (usp - 48) WM23).
    - intros z Hz NF. unfold FPWca in NF. unfold kThrCache, kPerClassSize, kThrCacheStats in NF. fold c in NF. apply OUT; clear -Hz NF; lia.
    - clear -LOC LO; lia.
    - exact REP2.
    - exact WF2.
    - exact BS2.
    - clear -Tlo Thi Timg. repeat split; lia.
    - intros r Hr. pose proof (IMGR r Hr) as X. rewrite EI1. clear -X EI2. lia.
    - rewrite EI1. clear; lia.
    - exact IMGR.
    - unfold kNumClasses, kLargestClassID in *. clear -HCc. lia.
    - exact NE2.
    - exact CI2.
    - unfold kThrCache, kPerClassSize. fold c. fold l2. rewrite ZL2.
      apply (rwc_split bsegs m3 _ [C4 (Z_to_bv 64 (hint c - 1))] [C4 (AsanRep.zw (max_count c)); C8 (Z_to_bv 64 (class_size c))]) in ROW3.
      replace (T + 208 + 80 * c) with (CA + 80 * c) by reflexivity. exact (proj1 ROW3).
    - unfold kThrCacheStats. replace (T + 2768 + 16) with (CA + 2576) by (clear; lia). exact CST3.
    - exists mo3. exact AK3.
    - exact TDN. }
  assert (RT3 : rt_misc5 FSB0 PL0 E0 m3).
  { apply (rt_misc5_agree E0 FSB0 PL0 m2 m3 RT2). intros z Hz. destruct (rt_fpc_where E0 FSB0 PL0 z Hz) as [(Z1 & _)|RH].
    - apply OUT; clear -Z1 LOC LO CR Timg HCc; unfold kLargestClassID in *; lia.
    - unfold rt_high2 in RH. apply OUT; clear -RH LOC LO CR Tlo Thi CT DT CP1 CP2 CC1 CC2 DP1 DP2 DD1 DD2 HCc; unfold kLargestClassID in *; lia. }
  (* [comment removed for export] *)
  assert (TOK4 : RTOKc (C - ca_cost n) (C' - ca_gcost n) (sA a3 s) mo3).
  { unfold ca_cost, ca_gcost. rewrite PR. replace (C' - 0) with C' by (clear; lia).
    exact (RTOK_same_fp E0 FSB0 HR0 L0 RES0 EB0 (C - 160) C' s a2 a3 mo3 TOK3 Csfp Cnp Cnd). }
  (* [comment removed for export] *)
  assert (AB8 : ab = 8 * (ab / 8)) by (rewrite Eab; clear -WE1; Z.div_mod_to_equations; lia).
  assert (CS8 : class_size c = 8 * (class_size c / 8)) by (clear -CSM; Z.div_mod_to_equations; lia).
  assert (ABR : kHighMemBeg <= ab /\ ab + class_size c <= alloc_ceiling).
  { pose proof (carved_in_space E0 a2 c _ HCc WR2 CARVED) as [I1 I2]. fold x in I1, I2. fold ab in I1, I2.
    unfold kRegionSize, kSpaceSize in *. clear -I1 I2 WE2 WE3 WE4 WE5 Eab. lia. }
  assert (SHm : rw_cells bsegs m2 (kShadowBase + ab / 8) [CB (Z.to_nat (class_size c / 8)) (repeat (Z_to_bv 8 250) (Z.to_nat (class_size c / 8)))]).
  { apply shadow_join; [| clear -CSZ CS8; lia]. intros g Hg. apply (Rsh2 g kAsanHeapLeftRedzoneMagic).
    apply (Sh_cache_block E0 [] [] a2 c x); [exact WF2| exact HCc| exact INx|]. fold ab. clear -Hg AB8 CS8. lia. }
  assert (SH3 : rw_cells bsegs m3 (kShadowBase + ab / 8) [CB (Z.to_nat (class_size c / 8)) (repeat (Z_to_bv 8 250) (Z.to_nat (class_size c / 8)))]).
  { eapply (BF_unwind.rw_cells_agree bsegs m2 m3); [| exact SHm]. intros z Hz. cbn [cells_size csize Nat.add] in Hz. rewrite Nat.add_0_r, Z2Nat.id in Hz by (clear -CSZ CS8; lia).
    pose proof WE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & WE14 & _).
    unfold app_mem in WE14. rewrite KHB, kLowAppEnd_val in WE14. unfold kShadowBase in Hz. rewrite KHB in ABR.
    apply OUT; clear -Hz WE14 ABR CR LOC LO AB8 CS8 HCc; unfold kLargestClassID in *; lia. }
  (* [comment removed for export] *)
  apply CONT with (a1 := a3) (ab := ab). unfold ca_post.
  split; [exact SK3|]. split; [exact (wmono_trans _ _ _ _ WM1 (wmono_trans _ _ _ _ WM12 WM23))|].
  split.
  { exists ([(usp - 48, usp)] ++ Wr ++ [(usp - 48, usp); (CA + 80 * c, CA + 80 * c + 4); (CA + 2576, CA + 2584)]).
    split; [exact (munch_app _ _ _ _ _ MU1 (munch_app _ _ _ _ _ MU12 MU23))|]. split.
    - apply Forall_app. split; [| apply Forall_app; split].
      + apply Forall_cons; [| apply Forall_nil]. left. cbn [fst snd]. clear -LO; lia.
      + eapply Forall_impl; [| exact AWr]. intros iv Hiv. eapply (aw_ok_mono E0 a a0 a3 a2 lo (usp + -48) usp iv); [| | | clear; lia| exact Hiv].
        * intros sc. rewrite Csec, Ssec, Ksec. clear; tauto.
        * intros y. rewrite Cnb. exact (fun H => H).
        * intros y. rewrite Csb. exact (fun H => H).
      + repeat (apply Forall_cons; [unfold aw_ok; cbn [fst snd]|]); [.. | apply Forall_nil].
        * left. clear -LO; lia.
        * right; right; left. exists (T + kThrCache, kPerClassSize * kNumClasses). split; [unfold arep_thr_ranges; do 3 right; left; reflexivity|]. cbn [fst snd]. unfold kThrCache, kPerClassSize, kNumClasses, kLargestClassID in *. clear -HCc. lia.
        * right; right; left. exists (T + kThrCacheStats + 16, 16). split; [unfold arep_thr_ranges; do 4 right; left; reflexivity|]. cbn [fst snd]. unfold kThrCacheStats. clear. lia.
    - apply Forall_app. split; [| apply Forall_app; split].
      + apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. intros blo bsz LIVE. destruct (live_block_off_thread E0 a blo bsz Hwf LIVE) as [LB1 LB2]. right; right. clear -LB1 LOC LO; lia.
      + rewrite Klive in LBr. exact LBr.
      + repeat (apply Forall_cons; [cbn [fst snd]; intros blo bsz LIVE; destruct (live_block_off_thread E0 a blo bsz Hwf LIVE) as [LB1 LB2]|]); [.. | apply Forall_nil].
        * right; right. clear -LB1 LOC LO; lia.
        * right. unfold kLargestClassID in HCc. clear -LB2 HCc. lia.
        * right. clear -LB2. lia. }
  split.
  { destruct RUNr as (fuelr & orcr & evsr & orcr' & RUNr). exists fuelr, orcr, evsr, orcr'. subst a3 ab x l2.
    exact (arun_ca_op_miss E0 n a fuelr orcr a2 evsr orcr' PR EMP RUNr NE2). }
  split; [split; [exact WF3| split; [exact AK3'| split; [exact (Cres Hres2)| split; [exact (Cqb Hqb2)| split; [exact (Cdi Hdi2)| split; [exact MI3| split; [exact RT3| split; [exact (Csst Hss2)| exact (Ccs Hcs2)]]]]]]]]|].
  split; [exact TOK4|].
  split; [rewrite Ffs3; exact Ffs2|]. split; [rewrite Ffds3; exact Ffds2|]. split; [rewrite Ftid3; exact Ftid2|].
  split; [rewrite Eab; reflexivity|].
  split; [apply ARep_ARepX; exact REP3|].
  unfold ca_span. rewrite PR, Ec. split.
  { exists (repeat (Z_to_bv 8 250) (Z.to_nat (class_size c / 8))). split; [exact SH3| intros _; reflexivity]. }
  split; [exact CI3|]. split; [exact AV3| exact EXX].
Qed.
(* [comment removed for export] *)
Theorem ca_srz : ca_srz_stmt E0 FSB0 HR0 L0 RES0 EB0 PL0.
Proof.
  unfold ca_srz_stmt.
  apply (ca_srz_case_join E0 FSB0 HR0 L0 RES0 EB0 PL0 (fun s n => from_primary n = true) SIDE_sec).
  { intros s n _. unfold SIDE_sec. destruct (from_primary n); [left| right]; reflexivity. }
  - apply (ca_srz_case_join E0 FSB0 HR0 L0 RES0 EB0 PL0 (SIDE_hit) SIDE_miss).
    { intros s n PR. unfold SIDE_hit, SIDE_miss. destruct (get_cache (aps_alloc s) (malloc_class n)) eqn:G; [right| left]; split; try exact PR; [reflexivity| discriminate]. }
    + exact (ca_srz_hit E0 FSB0 HR0 L0 RES0 EB0 PL0 ENV0 PL0OK).
    + exact ca_srz_miss.
  - exact (ca_srz_sec E0 FSB0 HR0 L0 RES0 EB0 PL0 HR0_ok EB0_ok ENV_depot ENV0 PL0OK L0OK).
Qed.
End CaT2.
End RC__1.
