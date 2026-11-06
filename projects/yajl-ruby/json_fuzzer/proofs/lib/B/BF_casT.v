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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanHoare AsanPS AsanRep AsanKern AsanClient AsanWf1 AsanWf2 AsanWf3 AsanWf4 AsanWf5 AsanBudget AsanBudget2 AsanDepot AsanRepFrame AsanRepFrame2 AsanHit AsanRepHitB AsanRepCaB AsanRepX AsanRepSecB AsanSecCount AsanSlack.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import B_iface BF_place BF_fakestack_rep BF_kit BF_kit2 BF_kit3 BF_unwind BF_casec BF_lalloc2 BF_lalloc3 B_policy5 B_slack5 B_budget5 B_live B_bundle B_benv5 B_init5 B_instD5 B_balloc5 B_bpolicy5 B_rtok5 B_bevents5 BF_alloc_iface BF_ca_iface BF_tkit BF_ainv_kit BF_caT BX_unreg BX_Exit BF_statics BF_poison BF_premap2.
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

Lemma upd_nprimc_false : forall c a, upd_nprimc false c a = a.
Proof. intros c a. destruct a; reflexivity. Qed.

Lemma lal_state_sec_st : forall a mb msz need, lal_state a mb msz need = sec_st a mb msz need.
Proof. intros. reflexivity. Qed.

Lemma lal_msz_map_size : forall n, lal_msz (needed n) = map_size n.
Proof. intros n. reflexivity. Qed.

(* [comment removed for export] *)
Lemma needed_sec : forall n, 0 < n <= 2^27 -> from_primary n = false ->
  0x10000 < needed n /\ needed n mod 8 = 0 /\ needed n <= 2^27 + 2^12 /\ needed n <= 2^40.
Proof.
  intros n Hn PR. unfold needed. rewrite PR.
  assert (N1 : kMaxSize < needed1 n) by (unfold from_primary in PR; apply Z.leb_gt in PR; exact PR). unfold kMaxSize in N1.
  pose proof (needed1_mod8 n) as M8. pose proof (rz_size_mod16 n) as R16. pose proof (rz_size_pos n) as RP.
  assert (UB : needed1 n <= 2^27 + 2048).
  { unfold needed1, rounded, round_up. unfold kChunkHeader2Size. change (2^27) with (8 * 2^24) in *. clear -Hn RP. Z.div_mod_to_equations. lia. }
  split; [clear -N1 RP; lia|]. split; [| clear -UB RP Hn; lia].
  rewrite Z.add_mod by (clear; lia). rewrite M8. replace (rz_size n mod 8) with 0; [reflexivity|]. clear -R16. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma arun_ca_op_sec : forall E n a mb,
  from_primary n = false ->
  (mb mod kPageSize =? 0) && (0 <? mb) && (mb + map_size n <=? alloc_ceiling) && ranges_free (known_ranges E a) mb (map_size n) = true ->
  app_mem_b mb (map_size n) && negb (in_primary (ae_space_beg E) mb) && negb (in_primary (ae_space_beg E) (mb + map_size n - 1)) && (mb + map_size n <=? kHighMemEnd + 1) = true ->
  n_chunks a < 2^20 ->
  exists evs, arun 2%nat (ca_op E n a) (AnsOk mb :: (if n_chunks a =? as_ptr_committed a then [AnsOk (ae_ptr_array E + 8 * as_ptr_committed a)] else []))
              = Some (sec_st a mb (map_size n) (needed n), ONorm (Some (mb + kPageSize)), evs, []).
Proof.
  intros E n a mb PR V1 V2 NCH.
  assert (NC1 : n_chunks (upd_ts (ts_on_mmap (map_size n)) a) = n_chunks a) by (destruct a; reflexivity).
  assert (PC1 : as_ptr_committed (upd_ts (ts_on_mmap (map_size n)) a) = as_ptr_committed a) by (destruct a; reflexivity).
  unfold sec_st, sec_commit. rewrite NC1, PC1.
  unfold ca_op. rewrite PR. unfold abind at 1. cbn [aupd sbind snd fst]. rewrite upd_nprimc_false.
  unfold sec_alloc. change (round_up (needed n) kPageSize + kPageSize) with (map_size n).
  unfold call_mmap_anon. unfold abind at 1 2. cbn [aget sbind snd fst]. unfold abind at 1. unfold acall. cbn [sbind].
  destruct (n_chunks a =? as_ptr_committed a) eqn:FIRST;
    eexists; cbn [arun sbind fst snd]; rewrite V1, V2; cbn [aret sbind snd fst];
    unfold abind at 1; cbn [aupd sbind snd fst]; unfold abind at 1; cbn [aget sbind snd fst]; rewrite !NC1, !PC1;
    unfold abind at 1; unfold acheck; replace (n_chunks a <? 2^20) with true by (symmetry; apply Z.ltb_lt; exact NCH); cbn [aret sbind snd fst];
    rewrite FIRST.
  - unfold abind at 1. cbn [sbind snd fst]. unfold abind at 1. unfold call_mmap_fixed. unfold abind at 1. unfold acall. cbn [arun sbind snd fst].
    rewrite Z.eqb_refl. cbn [aret sbind snd fst aupd]. unfold abind at 1. cbn [aupd aret sbind snd fst]. reflexivity.
  - unfold abind at 1. cbn [aret sbind snd fst]. unfold abind at 1. cbn [aupd aret sbind snd fst]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sec_keep : forall E a mb msz need,
     (csmall a -> csmall (sec_st a mb msz need)) /\ (AQbound a -> AQbound (sec_st a mb msz need)) /\ (depot_inv E a -> depot_inv E (sec_st a mb msz need))
  /\ live_blocks (sec_st a mb msz need) = live_blocks a
  /\ as_nprim_ever (sec_st a mb msz need) = as_nprim_ever a /\ as_ndepot_ins (sec_st a mb msz need) = as_ndepot_ins a
  /\ gapR (sec_st a mb msz need) = gapR a /\ gapD (sec_st a mb msz need) = gapD a
  /\ as_regions (sec_st a mb msz need) = as_regions a /\ as_node_blocks (sec_st a mb msz need) = as_node_blocks a
  /\ as_store_blocks (sec_st a mb msz need) = as_store_blocks a.
Proof.
  intros E a mb msz need. unfold gapR, gapD, regions_bytes, get_region, sec_st, sec_commit.
  destruct (n_chunks _ =? _); destruct a; repeat lazymatch goal with |- _ /\ _ => split end; first [intros H; exact H | reflexivity].
Qed.

Lemma res_ok_sec : forall a mb msz need, res_ok a -> res_ok (sec_st a mb msz need).
Proof.
  intros a mb msz need RO sc Hsc. rewrite sec_sec in Hsc. rewrite sec_residue. apply in_app_iff in Hsc as [Hsc|[<-|[]]].
  - intros p Hp. apply in_or_app. left. exact (RO sc Hsc p Hp).
  - intros p Hp. apply in_or_app. right. exact Hp.
Qed.

Lemma sstats_sec : forall a mb msz need, sstats_ok a -> 0 <= msz -> sec_bytes a + msz < 2^62 -> sstats_ok (sec_st a mb msz need).
Proof.
  intros a mb msz need [S1 S2] M0 UB. unfold sstats_ok. rewrite sec_stats. cbn [ss_cur ss_max].
  unfold sec_bytes in *. rewrite sec_sec, fold_right_app. cbn [fold_right sc_map_size].
  assert (FR : forall l z, fold_right (fun c acc => sc_map_size c + acc) z l = fold_right (fun c acc => sc_map_size c + acc) 0 l + z).
  { induction l as [|c l IH]; intros z; cbn; [lia|]. rewrite IH. lia. }
  rewrite FR. split; [clear -S1; lia| clear -S1 S2 M0 UB; lia].
Qed.

(* [comment removed for export] *)
Lemma ca_op_sec : forall E n a, from_primary n = false -> ca_op E n a = sec_alloc E (needed n) a.
Proof.
  intros E n a PR. unfold ca_op. rewrite PR. unfold abind at 1. cbn [aupd sbind snd fst]. rewrite upd_nprimc_false. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma cost2_le_acharge : forall n, from_primary n = false -> cost2 (map_size n) <= acharge n /\ 0 <= cost2 (map_size n).
Proof.
  intros n PR. unfold cost2, acharge. rewrite PR. pose proof (map_size_facts n) as (_ & _ & M2). unfold kPageSize in M2.
  destruct (kBigMapSize <=? map_size n) eqn:B1; destruct (map_size n <? kBigMapSize) eqn:B2;
    first [apply Z.leb_le in B1| apply Z.leb_gt in B1]; first [apply Z.ltb_lt in B2| apply Z.ltb_ge in B2]; try lia;
    split; Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
Lemma region_free_point' : forall l (r : word) (L b n x : Z),
  region_free l r (Z_to_bv 64 L) = true -> In (Z_to_bv 64 b, Z_to_bv 64 n) l ->
  0 <= b -> 0 <= n -> b + n < 2^64 -> 0 <= L -> bv_unsigned r + L < 2^64 ->
  b <= x < b + n -> bv_unsigned r <= x < bv_unsigned r + L -> False.
Proof.
  intros l r L b n x RF IN Hb Hn Hbn HL HrL [X1 X2] [Y1 Y2].
  pose proof (region_free_In _ _ _ _ _ RF IN) as OV.
  pose proof (bv_unsigned_in_range 64 r) as UR. change (bv_modulus 64) with (2^64) in UR.
  rewrite ?unsigned_lit in OV by lia.
  first [ lia | unfold iv_overlap in OV; rewrite ?unsigned_lit in OV by lia; apply andb_false_iff in OV; destruct OV as [OV|OV]; apply Z.ltb_ge in OV; lia ].
Qed.

(* [comment removed for export] *)
Lemma fresh_shadow_of : forall E a m mo,
  ARep bsegs E (DepotR bsegs E) a m -> AWf E [] [] a -> AKern E a mo -> fst (ae_img E) = 0x10000 -> fresh_shadow_ok E m mo.
Proof.
  intros E0 a m mo Hrep WF Hkern EI1 mo1 r L Hag RF PL RSV Ral Lal Lpos.
  pose proof (magree_frame _ _ Hag) as (_ & Fvm & _). rewrite Fvm in RF.
  pose proof alloc_ceiling_range as CR. pose proof alloc_ceiling_le_high_end as CH. unfold kHighMemEnd in CH.
  pose proof PL as (P1 & P2 & P3). unfold A_IMG_END, A_LOWAPP_END, A_HIGH_BEG in P1, P2, P3.
  set (ur := bv_unsigned r) in *.
  pose proof (bv_unsigned_in_range 64 r) as URR. change (bv_modulus 64) with (2^64) in URR. fold ur in URR.
  assert (UR8 : ur = 8 * (ur / 8)) by (clear -Ral; Z.div_mod_to_equations; lia).
  assert (L8 : L = 8 * (L / 8)) by (clear -Lal; Z.div_mod_to_equations; lia).
  assert (NORES : forall b n x, In (b, n) (ae_reserved E0) -> b <= x < b + n -> ur <= x < ur + L -> False).
  { intros b n x IN BX RX. pose proof (RSV (b, n) IN) as AP. cbn [fst snd] in AP. fold ur in AP. clear -AP BX RX. lia. }
  assert (NOMAP : forall b n x, In (went b n) (vm_maps (m_vmmaps mo)) -> 0 <= b -> 0 <= n -> b + n <= alloc_ceiling -> b <= x < b + n -> ur <= x < ur + L -> False).
  { intros b n x IN B0 N0 BN BX RX. unfold went, kwz in IN.
    eapply (region_free_point' _ r L b n x RF); [apply in_app_iff; right; exact IN| exact B0| exact N0| clear -BN CR; lia| clear -Lpos; lia
      | subst ur; clear -P2 CR; lia| exact BX| exact RX]. }
  pose proof WF as WF0. destruct WF as (WE & _ & _ & _ & _ & WS & _).
  pose proof WE as (WE1 & WE2 & WE3 & WE4 & WE5 & WE6 & WE7 & WE8 & WE9 & WE10 & WE11 & WE12 & WE13 & WE14 & WE15 & WE16 & WE17 & WE18 &
                    WE19 & WE20 & WE21 & WE22 & WE23 & WE24 & WE25 & WE26 & WE27 & WE28 & WE29 & WE30 & WE31 & WE32 & WE33 & WE34 & WE35rest).
  destruct WS as (_ & _ & S3 & _).
  destruct (ae_img E0) as [ib il] eqn:EIMG. cbn [fst snd] in EI1. subst ib.
  assert (SHZ : forall g, ur / 8 <= g < ur / 8 + L / 8 -> Sh E0 a (8 * g) = Some 0).
  { intros g Hg. set (x := 8 * g).
    assert (RX : ur <= x < ur + L) by (subst x; clear -Hg UR8 L8; lia).
    unfold Sh.
    replace (in_some_region_map E0 a x) with false.
    2:{ symmetry. destruct (in_some_region_map E0 a x) eqn:RM; [| reflexivity]. exfalso.
        pose proof (region_map_in_space E0 [] [] a x WF0 RM) as SP.
        apply (NORES _ _ x WE7); [| exact RX]. change kSpaceSize with 0x2000000000 in *. clear -SP WE3 WE4. lia. }
    replace (in_some_sec_map a x) with false.
    2:{ symmetry. destruct (in_some_sec_map a x) eqn:SM; [| reflexivity]. exfalso.
        unfold in_some_sec_map in SM. apply existsb_exists in SM as (sc & Hsc & Hb).
        apply andb_true_iff in Hb as [B1 B2]. apply Z.leb_le in B1. apply Z.ltb_lt in B2.
        destruct (S3 sc Hsc) as (_ & SC2 & SC3 & SC4 & _). unfold app_mem in SC2. rewrite kHighMemBeg_val, kLowAppEnd_val in SC2.
        destruct (ak_sec _ _ _ Hkern sc Hsc) as [INM _].
        apply (NOMAP _ _ x INM); [clear -SC2; lia| clear -SC4; lia| exact SC3| clear -B1 B2; lia| exact RX]. }
    cbn [orb].
    unfold sh_default_dom, sh_excluded, in_img. rewrite EIMG. cbn [fst snd].
    replace (in_fakestack E0 x) with false.
    2:{ symmetry. unfold in_fakestack. destruct (Z.leb_spec (ae_fs_beg E0) x); destruct (Z.ltb_spec x (ae_fs_beg E0 + ae_fs_len E0)); cbn; try reflexivity.
        exfalso. apply (NORES _ _ x WE9); clear -H H0 RX; lia. }
    replace (in_iarena E0 x) with false.
    2:{ symmetry. unfold in_iarena. destruct (Z.leb_spec (ae_iarena E0) x); destruct (Z.ltb_spec x (ae_iarena E0 + kIArenaLen)); cbn; try reflexivity.
        exfalso. apply (NORES _ _ x WE24); clear -H H0 RX; lia. }
    replace (in_reginfo E0 x) with false.
    2:{ symmetry. unfold in_reginfo. destruct (Z.leb_spec (ae_space_beg E0 + kSpaceSize) x); destruct (Z.ltb_spec x (ae_space_beg E0 + kSpaceSize + kPageSize)); cbn; try reflexivity.
        exfalso. apply (NORES _ _ x WE7); [| exact RX]. change kSpaceSize with 0x2000000000 in *. change kPageSize with 4096 in *. clear -WE3 WE4 H H0. lia. }
    replace ((65536 <=? x) && (x <? 65536 + il)) with false.
    2:{ symmetry. destruct (Z.leb_spec 65536 x); destruct (Z.ltb_spec x (65536 + il)); cbn; try reflexivity.
        exfalso. apply (NORES _ _ x WE29); [cbn; clear -H H0; lia| exact RX]. }
    cbn [negb andb orb].
    rewrite kHighMemBeg_val, kLowAppEnd_val. unfold kHighMemEnd.
    destruct P3 as [LOW|HIGH].
    - replace (0 <=? x) with true by (symmetry; apply Z.leb_le; clear -RX P1; lia).
      replace (x <? 2147446784) with true by (symmetry; apply Z.ltb_lt; clear -RX LOW; lia). reflexivity.
    - replace (17594333495296 <=? x) with true by (symmetry; apply Z.leb_le; clear -RX HIGH; lia).
      replace (x <=? 2^47 - 1) with true by (symmetry; apply Z.leb_le; subst ur; clear -RX P2 CH; lia).
      rewrite Bool.orb_true_r. reflexivity. }
  apply (shadow_join m kShadowBase (ur / 8) (Z.to_nat (L / 8)) 0); [| clear -Lpos L8; lia].
  intros g Hg. eapply (ARep_shadow_cells E0 bsegs); [exact Hrep|]. apply SHZ. clear -Hg Lpos L8. lia.
Qed.

Lemma u64arr_nil : forall m A, 0 <= A -> A <= 2^64 -> u64arr bsegs m A [].
Proof. intros m A H0 H1. split; (split; [exact H0| split; [cbn; lia| intros i Hi; cbn in Hi; lia]]). Qed.

Lemma upd_app_mid : forall {X} (l1 : list X) (x : X) (l2 : list X) (v : X), upd (l1 ++ x :: l2) (length l1) v = l1 ++ v :: l2.
Proof. intros X l1. induction l1 as [|y l1 IH]; intros x l2 v; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma zw_mod_add : forall x k, Z_to_bv 64 (x mod 2^64 + k) = Z_to_bv 64 (x + k).
Proof.
  intros x k. rewrite <- (ZBridge.Z_to_bv_mod64 (x mod 2^64 + k)), <- (ZBridge.Z_to_bv_mod64 (x + k)).
  rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma live_block_where : forall E a blo bsz, AWf E [] [] a -> In (blo, bsz) (live_blocks a) ->
  1 <= bsz /\ blo + bsz <= alloc_ceiling /\ (blo + bsz <= kLowAppEnd \/ kHighMemBeg <= blo)
  /\ ((ae_space_beg E <= blo /\ blo + bsz <= ae_space_beg E + kSpaceSize)
      \/ (exists sc, In sc (as_sec a) /\ sc_map_beg sc <= blo /\ blo + bsz <= sc_map_beg sc + sc_map_size sc)).
Proof.
  intros E a blo bsz WF LIVE. pose proof WF as (WE & WR & _ & _ & _ & (_ & _ & WS3 & _) & _).
  destruct (live_block_loc E [] [] a blo bsz WF LIVE) as (k & cm & Hk & _ & _ & POS & L1 & L2 & LOC).
  pose proof WE as (E1 & E2 & E3 & E4 & E5 & _).
  destruct (cm_prim cm) as [c'|].
  - destruct LOC as (Hc' & R1 & R2). unfold region_beg in R1, R2.
    destruct (proj2 WR c' Hc') as ((_ & _) & _ & R3 & _). unfold region_of in R3.
    unfold kFreeArrayOffset, kRegionSize, kSpaceSize, kLargestClassID in *. rewrite kHighMemBeg_val in *.
    split; [exact POS|]. split; [clear -L1 L2 R1 R2 R3 Hc' E3 E4 E5; nia|]. split; [right; clear -L1 R1 R2 R3 Hc' E2 E3; nia|].
    left. clear -L1 L2 R1 R2 R3 Hc' E3 E4. split; nia.
  - destruct LOC as (sc & Hsc & R1 & R2). destruct (WS3 sc Hsc) as (_ & AM & CE & _). unfold app_mem in AM.
    split; [exact POS|]. split; [clear -L2 R2 CE; lia|]. split; [unfold kPageSize in R1; clear -L1 L2 R1 R2 AM POS; lia|].
    right. exists sc. split; [exact Hsc|]. unfold kPageSize in R1. clear -L1 L2 R1 R2. lia.
Qed.

(* [comment removed for export] *)
Section CaS.
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
#[local] Notation PA := (ae_ptr_array E0).
#[local] Notation PP := (BF_caT.PP E0 FSB0 HR0).

(* [comment removed for export] *)
Definition SIDE_sec (s : aps) (n : Z) : Prop := from_primary n = false.

Theorem ca_srz_sec : ca_srz_case E0 FSB0 HR0 L0 RES0 EB0 PL0 SIDE_sec.
Proof.
  intro. intros until K. cbv zeta. intros PR KN TOK CHG GC AIV ABUD Hn NBIG SK LOC LO SPA SPH TP CONT. unfold SIDE_sec in PR.
  pose proof alloc_ceiling_range as CR. pose proof B_bundle.kHighMemBeg_val as KHB. pose proof kLowAppEnd_val as KLE.
  pose proof AIV as AIV0. destruct AIV as (Hrep & Hwf & Hkern & Hres & Hqb & Hdi & Hbinv & Hmi & Hrt & Hss & Hcs).
  destruct (RTOK_elim _ _ _ _ _ _ _ _ _ _ TOK) as (R0 & R0' & ATK & HCR & HCR' & GR0 & GD0 & RLE).
  assert (ENV : ENVOK E0 FSB0 s) by exact (ATOK_ENVOK _ _ _ _ _ _ _ _ _ _ ATK).
  pose proof ENV as ENV'. destruct ENV' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & EE & EFS & [EI1 EI2]).
  pose proof L0OK as (LS_L0 & GS_L0 & HS_L0 & RES0_low & RES0_cover & RSVD & RSVD_pos).
  set (a := aps_alloc s) in *.
  rewrite EE in EI1, EI2.
  destruct (needed_sec n Hn PR) as (N1 & N8 & N2 & N40).
  pose proof (map_size_facts n) as (MS4 & MSG & MS2). unfold kPageSize in MS4, MSG, MS2.
  assert (MSU : map_size n <= needed n + 8192) by (unfold map_size, round_up, kPageSize; clear; Z.div_mod_to_equations; lia).
  set (need := needed n) in *. set (msz := map_size n) in *.
  (* [comment removed for export] *)
  pose proof ENV0 as ENV0'. destruct ENV0' as (D0a & D0b & _ & _ & _ & _ & _ & _ & _ & _ & _ & IMGR & _ & _ & _ & _ & _ & IC0 & TDN & DNP).
  pose proof Hrep as (Rins & Rri & Rrm & Rthr & Rsec & Rch & Rbat & Rdep & Rglob & Rsh).
  pose proof Rthr as (Ttop & T40 & Tq & Tcache & Tcst & Tst & Tby & Tunw).
  pose proof Rins as (I1 & I2 & I3 & I4 & (bsl & I5 & L5) & I6 & I7 & _).
  unfold ae_instance in I2, I3, I4, I5, I6, I7. rewrite IC0 in I2, I3, I4, I5, I6, I7.
  cbn [aic_instance both_ic kInsSecondary kInsNReserved kInsSecStats kInsSecMutex kInsGlobalStats Z.add] in I2, I3, I4, I5, I6, I7.
  pose proof Hwf as (WE & WR & WC & WK & WQ & WS & WD). pose proof WS as (WS1 & WS2 & WS3 & WS4 & WS5).
  pose proof WE as (WE1 & WE2 & WE3 & WE4 & WE5 & WE6 & WE7 & WE8 & WE9 & WE10 & WE11 & WE12 & WE13 & WE14 & WE15 & WE16 & WE17 & WE18 & WE19 & WE20 &
                    WE21 & WE22 & WE23 & WE24 & WE25 & WE26 & _).
  unfold app_mem in WE14, WE16. rewrite KHB, KLE in WE14, WE16.
  (* [comment removed for export] *)
  pose proof PL0OK as ((c0 & cl & CR0 & CC1 & CC2) & (d0 & dl & DR0 & DD1 & DD2) & TR & CT & DT & CD & CIA).
  pose proof TR as (TR1 & TR2 & _). pose proof TR2 as (Tlo & Thi & Timg & Tband). unfold A_IMG_END, A_LOWAPP_END, A_HIGH_BEG in Timg, Tband.
  pose proof (rt_misc5_fsenv _ _ _ _ Hrt) as FSE.
  assert (T8 : T mod 8 = 0) by (unfold FSEnv in FSE; decompose [and] FSE; assumption).
  (* [comment removed for export] *)
  pose proof Hrt as (_ & [tX XS] & _ & AMS & _).
  assert (US : unreg_statics m) by (unfold exit_statics in XS; decompose [and] XS; assumption). unreg_statics_open US.
  pose proof AMS as (_ & _ & _ & GPAIR & MML & DPM & _ & _ & _ & _ & GSN1 & GSN2 & _).
  pose proof FSE as FSE'. unfold FSEnv in FSE'. pose proof FSE' as (_ & _ & _ & _ & _ & _ & FKI & FKEY & FTSD & FTSD0 & FCTXT & _). clear FSE'.
  pose proof Rglob as (Gfl & Gfu & Gth & Gdd & Gsh & Ghe & Gcp & Gai & Gmcs & Gps & Gdy & Ganc & Grm & _).
  rewrite IC0 in Ghe, Grm. cbn [aic_kHighMemEnd aic_REAL_memcpy_var aic_musl_memcpy aic_musl_memset both_ic] in Ghe, Grm.
  assert (TC : thread_cells m tp 0x6028f8 (fp_ctx PL0) T).
  { split; [exact FKI|]. split; [exact FKEY|]. split; [| split; [exact FTSD0| exact FCTXT]].
    rewrite TP. rewrite unsigned_lit by (clear; lia). exact FTSD. }
  assert (LST : lal_statics m).
  { split; [exact (proj1 (AINV_dput_statics E0 FSB0 PL0 IC0 a m mo AIV0))|]. split; [| split; [exact GSN1| exact GSN2]].
    unfold poison_globals. split.
    { pose proof (rwc_join_at bsegs m _ _ _ _ GHE GRSP ltac:(reflexivity)) as X4.
      pose proof (rwc_join_at bsegs m _ _ _ _ GME X4 ltac:(reflexivity)) as X3.
      pose proof (rwc_join_at bsegs m _ _ _ _ GMB X3 ltac:(reflexivity)) as X2.
      pose proof (rwc_join_at bsegs m _ _ _ _ GSBP X2 ltac:(reflexivity)) as X1. cbn [app] in X1. exact X1. }
    split; [exact GCF|]. split; [exact GSB|]. split; [exact Ghe|]. split; [exact Grm|]. split; [exact GCPM| exact GTHR]. }
  (* [comment removed for export] *)
  assert (NCH : n_chunks a < kChunksBlockCount).
  { pose proof (n_chunks_bound E0 a Hwf Hqb Hbinv) as X. unfold nbig_live in NBIG. unfold zlen in X. unfold kChunksBlockCount. clear -X NBIG. lia. }
  destruct ABUD as (BU1 & BU2 & BU3).
  pose proof (cost2_le_acharge n PR) as [C2A C20]. fold msz in C2A, C20.
  assert (ACH25 : 25 <= acharge n).
  { unfold acharge; rewrite PR; fold msz. destruct (Z.ltb_spec msz kBigMapSize) as [BB|BB]; unfold kBigMapSize in BB; clear -MS2 BB; Z.div_mod_to_equations; lia. }
  assert (BUX : 10000 * as_nprim_ever a + as_ndepot_ins a + 1 <= kInitialCredit) by (clear -BU3 ACH25; lia).
  destruct (AINV_dput_nums E0 FSB0 HR0 L0 RES0 EB0 PL0 EB0_ok s m mo C C' AIV0 TOK BU1 BUX (conj (proj1 ENV_depot) (proj2 (proj2 ENV_depot))))
    as (_ & _ & SECB & _). fold a in SECB.
  pose proof Hss as [SS1 SS2]. pose proof (sec_bytes_nonneg E0 a Hwf) as SB0.
  (* [comment removed for export] *)
  set (P := PP s mo).
  assert (PSTK : forall y k, lo <= y -> y + Z.of_nat k <= bv_unsigned sp -> P (Z_to_bv 64 y, k)).
  { intros y k H1 H2. unfold P, BF_caT.PP. apply (pol_stack' E0 FSB0 HR0 s mo Hkern WE ENV0); clear -H1 H2 LOC SPH CR; lia. }
  pose proof (PP_KIP E0 FSB0 HR0 L0 RES0 EB0 s mo R0 R0' ATK) as KIP0.
  eapply (rzA_seg_cfg bsegs (aSc s) (aNc s) (aEBc s) P).
  { eapply (ca_sec_front P ra sp gp tp F fc lo (T + kThrCache) need LOC ltac:(clear -LO; unfold K_CA in LO; lia) ltac:(clear -SPH; lia) ltac:(clear -N1 N40; lia) PSTK);
      [exact SK| exact Hmi]. }
  { exact KIP0. }
  intros ms1 mo1 HQ1 AG1 KIP1.
  destruct HQ1 as (m1 & -> & MU1 & WM1 & MI1 & SK1 & CFR1).
  pose proof (magree_frame _ _ AG1) as (Ffds1 & Fvm1 & Flz1 & Ffs1 & Fh1 & Ftid1 & _).
  destruct KIP1 as [KIA1 _].
  pose proof (ATOK_magree _ _ _ _ _ _ _ _ _ _ _ ATK AG1 KIA1) as ATK1.
  pose proof (AKern_frame _ _ _ _ Fvm1 Flz1 Hkern) as AK1.
  set (usp := bv_unsigned sp) in *.
  assert (AGB : forall z, 0 <= z < usp - 48 -> m1 (wa z) = m (wa z)).
  { intros z Hz. apply MU1. rewrite wa_unsigned by (clear -Hz SPH; lia). cbn [outside]. clear -Hz. repeat split; try exact I; lia. }
  Ltac below AGB := eapply rw_cells_agree; [| eassumption]; cbn; intros; apply AGB.
  (* [comment removed for export] *)
  set (SS := as_sec_stats a) in *.
  assert (SEC1 : rw_cells bsegs m1 0xaaf98 [C8 (Z_to_bv 64 4096); C8 (Z_to_bv 64 PA); C8 (Z_to_bv 64 PA); C8 (Z_to_bv 64 (2^23))])
    by (eapply rw_cells_agree; [| exact I2]; cbn; intros; apply AGB; clear -H LOC LO CR; unfold K_CA in *; lia).
  assert (NRS1 : rw_cells bsegs m1 0xaafc8 [C8 (Z_to_bv 64 (as_ptr_committed a)); C8 (Z_to_bv 64 (n_chunks a)); C1 (Z_to_bv 8 0)])
    by (eapply rw_cells_agree; [| exact I3]; cbn; intros; apply AGB; clear -H LOC LO CR; unfold K_CA in *; lia).
  assert (SST1 : rw_cells bsegs m1 0xaafe0 [C8 (Z_to_bv 64 (ss_n_allocs SS mod 2^64)); C8 (Z_to_bv 64 (ss_n_frees SS mod 2^64)); C8 (Z_to_bv 64 (ss_cur SS)); C8 (Z_to_bv 64 (ss_max SS))]).
  { rewrite !ZBridge.Z_to_bv_mod64. eapply rw_cells_agree; [| exact I4]; cbn; intros; apply AGB; clear -H LOC LO CR; unfold K_CA in *; lia. }
  assert (BSL1 : u64arr bsegs m1 0xab000 bsl) by (eapply u64arr_agree; [| exact I5]; rewrite L5; intros z Hz; apply AGB; clear -Hz LOC LO CR; unfold K_CA in *; lia).
  assert (MTX1 : rw_cells bsegs m1 0xab200 [C4 (Z_to_bv 64 0)]) by (eapply rw_cells_agree; [| exact I6]; cbn; intros; apply AGB; clear -H LOC LO CR; unfold K_CA in *; lia).
  assert (GST1 : rw_cells bsegs m1 0xab218 [C8 (Z_to_bv 64 (as_glob_allocated a mod 2^64)); C8 (Z_to_bv 64 (as_glob_mapped a mod 2^64))]).
  { rewrite !ZBridge.Z_to_bv_mod64. eapply rw_cells_agree; [| exact I7]; cbn; intros; apply AGB; clear -H LOC LO CR; unfold K_CA in *; lia. }
  (* [comment removed for export] *)
  assert (PTR : exists ws, u64arr bsegs m PA ws /\ length ws = Z.to_nat (as_ptr_committed a)
                 /\ ((as_ptr_committed a = 0 /\ as_sec a = [] /\ ws = [])
                     \/ (as_ptr_committed a = kChunksBlockCount /\ exists junk, ws = map (fun c => zw (sc_map_beg c)) (as_sec a) ++ junk))).
  { destruct Rsec as [[[P0 S0]|(P1 & junk & U & L)] _].
    - exists []. rewrite P0. split; [apply u64arr_nil; clear -WE16 WE17 CR; lia| split; [reflexivity| left; auto]].
    - exists (map (fun c => zw (sc_map_beg c)) (as_sec a) ++ junk). split; [exact U|].
      split; [rewrite P1, length_app, length_map; unfold kChunksBlockCount in L |- *; clear -L; lia| right; split; [exact P1| exists junk; reflexivity]]. }
  destruct PTR as (ws & ARR & LWS & WSC).
  assert (PCB : 0 <= as_ptr_committed a <= kChunksBlockCount) by (destruct WSC as [(P0 & _)|(P1 & _)]; rewrite ?P0, ?P1; unfold kChunksBlockCount; clear; lia).
  assert (ARR1 : u64arr bsegs m1 PA ws).
  { eapply u64arr_agree; [| exact ARR]. rewrite LWS, Z2Nat.id by (clear -PCB; lia). intros z Hz. apply AGB.
    unfold kChunksBlockCount in *. clear -Hz WE16 WE17 PCB LOC LO CR; unfold K_CA in *; lia. }
  (* [comment removed for export] *)
  pose proof (resv_range_num E0 c0 cl CR0 ltac:(clear -CC1 CC2; lia)) as (CQ1 & CQ2 & CQ3 & CQ4).
  assert (TC1 : thread_cells m1 tp 0x6028f8 (fp_ctx PL0) T).
  { destruct TC as (X1 & X2 & X3 & X4 & X5). unfold thread_cells. rewrite TP in X3 |- *. rewrite unsigned_lit in X3 |- * by (clear; lia).
    split; [below AGB; clear -H LOC LO CR; unfold K_CA in *; lia|]. split; [below AGB; clear -H LOC LO CR; unfold K_CA in *; lia|].
    split; [below AGB; clear -H LOC LO CR; unfold K_CA in *; lia|]. split; [below AGB; clear -H LOC LO CR; unfold K_CA in *; lia|].
    below AGB; clear -H LOC LO CR CQ1 CQ2 CC1 CC2; unfold K_CA in *; lia. }
  set (ts := as_ts a) in *.
  assert (TST1 : rw_cells bsegs m1 (T + 2872) [C8 (Z_to_bv 64 (ts_mmaps ts mod 2^64)); C8 (Z_to_bv 64 (ts_mmaped ts mod 2^64))]).
  { rewrite !ZBridge.Z_to_bv_mod64.
    pose proof (BF_tkit.u64arr_cell m _ _ 9 _ Tst eq_refl) as X9. pose proof (BF_tkit.u64arr_cell m _ _ 10 _ Tst eq_refl) as X10.
    unfold kThrStats in X9, X10. cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Pos.mul Pos.add] in X9, X10.
    pose proof (rwc_join_at bsegs m _ _ _ _ X9 X10 ltac:(cbn; clear; lia)) as X. cbn [app] in X.
    replace (T + 2872) with (T + 2800 + 72) by (clear; lia).
    eapply rw_cells_agree; [| exact X]. cbn. intros z Hz. apply AGB. clear -Hz WE15 Tlo LOC LO CR; unfold K_CA in *; lia. }
  assert (LST1 : lal_statics m1) by (apply (lal_statics_agree s need ws bsl LWS L5 m m1 LST); intros z Hz; apply AGB; clear -Hz LOC LO CR; unfold K_CA in *; lia).
  pose proof (fresh_shadow_of E0 a m mo Hrep Hwf Hkern EI1) as FSH0.
  assert (FSH1 : fresh_shadow_ok E0 m1 mo1).
  { intros mo2 r L Hag2 RF PL RSV' Ral Lal Lpos.
    pose proof (FSH0 mo2 r L (magree_trans _ _ _ AG1 Hag2) RF PL RSV' Ral Lal Lpos) as X.
    pose proof (placed_num _ _ PL ltac:(clear -Lpos; lia)) as (Q1 & Q2 & Q3).
    eapply rw_cells_agree; [| exact X]. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by (clear -Lpos Lal; Z.div_mod_to_equations; lia).
    intros z Hz. apply AGB. unfold kShadowBase in Hz. clear -Hz Q1 Q2 LOC LO CR Lpos; unfold K_CA in *. lia. }
  (* [comment removed for export] *)
  assert (HV : 0 <= ss_n_allocs SS mod 2^64 < 2^64 /\ 0 <= ss_n_frees SS mod 2^64 < 2^64 /\ 0 <= ss_cur SS /\ ss_cur SS + lal_msz need < 2^64
               /\ 0 <= ss_max SS < 2^64 /\ 0 <= as_glob_allocated a mod 2^64 < 2^64 /\ 0 <= as_glob_mapped a mod 2^64 < 2^64).
  { rewrite lal_msz_map_size. fold msz.
    pose proof (Z.mod_pos_bound (ss_n_allocs SS) (2^64) ltac:(clear; lia)). pose proof (Z.mod_pos_bound (ss_n_frees SS) (2^64) ltac:(clear; lia)).
    pose proof (Z.mod_pos_bound (as_glob_allocated a) (2^64) ltac:(clear; lia)). pose proof (Z.mod_pos_bound (as_glob_mapped a) (2^64) ltac:(clear; lia)).
    clear -H H0 H1 H2 SS1 SS2 SECB SB0 MSU N2. lia. }
  assert (HVT : 0 <= ts_mmaps ts mod 2^64 < 2^64 /\ 0 <= ts_mmaped ts mod 2^64 < 2^64).
  { pose proof (Z.mod_pos_bound (ts_mmaps ts) (2^64) ltac:(clear; lia)). pose proof (Z.mod_pos_bound (ts_mmaped ts) (2^64) ltac:(clear; lia)). clear -H H0. lia. }
  assert (HC4 : fp_ctx PL0 + 4096 <= alloc_ceiling) by (clear -CIA WE26; lia).
  assert (RC : cost2 (lal_msz need) + (if n_chunks a =? as_ptr_committed a then 32 else 0) <= R0).
  { rewrite lal_msz_map_size. fold msz. unfold gapP in RLE. pose proof WSC as [(P0 & S0 & _)|(P1 & _)].
    - rewrite P0 in RLE. cbn [Z.eqb] in RLE. unfold n_chunks. rewrite S0, P0. replace (Z.of_nat (length (@nil secchunk)) =? 0) with true by reflexivity. unfold kPtrArrayCommit in RLE. clear -RLE CHG C2A GR0 GD0. lia.
    - rewrite P1 in RLE |- *. cbn [kChunksBlockCount Z.eqb] in RLE. replace (n_chunks a =? kChunksBlockCount) with false by (symmetry; apply Z.eqb_neq; clear -NCH; lia).
      clear -RLE CHG C2A GR0 GD0. lia. }
  assert (RG : lal_gcost need <= R0') by (unfold lal_gcost; rewrite lal_msz_map_size; unfold ca_gcost in GC; rewrite PR in GC; fold msz in GC |- *; clear -GC HCR'; lia).
  change (Z_to_bv 64 (700248 + 64)) with (Z_to_bv 64 0xaaf98). change (Z_to_bv 64 (700248 + 688)) with (Z_to_bv 64 0xab208).
  change (Z_to_bv 64 226180) with (Z_to_bv 64 LAL_ENTRY).
  eapply (lalloc_srz E0 FSB0 HR0 L0 RES0 EB0 HR0_ok ENV0 LS_L0 GS_L0 HS_L0 RES0_low RES0_cover RSVD RSVD_pos s [] [] need Hwf Hres
            (conj N1 (conj N8 N2)) NCH ws bsl (ss_n_allocs SS mod 2^64) (ss_n_frees SS mod 2^64) (ss_cur SS) (ss_max SS)
            (as_glob_allocated a mod 2^64) (as_glob_mapped a mod 2^64) (ts_mmaps ts mod 2^64) (ts_mmaped ts mod 2^64)
            0x6028f8 (fp_ctx PL0) c0 cl LWS L5 HV HVT ltac:(clear; lia) ltac:(clear; lia) (conj CR0 (conj CC1 CC2)) HC4 TR2
            _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 mo1 (usp + -48) lo R0 R0' K KN ATK1 AK1 RC RG);
    [ clear -SPA; Z.div_mod_to_equations; lia | exact SK1 | exact LOC | clear -LO; unfold K_CA in LO; lia | clear -SPH; lia | exact MI1
    | rewrite TP; apply unsigned_lit; clear; lia
    | exact SEC1 | exact NRS1 | exact SST1 | exact BSL1 | exact MTX1 | exact GST1 | exact ARR1 | exact TC1 | exact TST1 | exact LST1 | exact FSH1 | ].
  (* [comment removed for export] *)
  intros ms2 mo2 POST.
  destruct POST as (xt0 & xt1 & xt2 & xa1 & xa2 & xa3 & xa4 & xa5 & xa6 & xa7 & xt3 & xt4 & xt5 & xt6 & m2 & mb & hj' & bsl' & ws' & -> & MI2 & SK2 & MU2 & WM2
                    & MB4K & PLm & RSVm & RFm & NP1 & NP2 & VAL1 & VAL2 & MTX2 & NRS2 & SST2 & BSL2 & LBSL2 & GST2 & ARR2 & EWS & HDR2 & BODY2
                    & SHH2 & SHU2 & SHT2 & TST2 & LST2 & ATK2 & AK2 & Ffs2 & Ffds2 & Ftid2).
  assert (USP48 : bv_unsigned (Z_to_bv 64 (usp + -48)) = usp + -48) by (apply unsigned_lit; clear -LOC LO CR SPH; unfold K_CA in *; lia).
  rewrite USP48 in *.
  change (lal_msz need) with msz in *. fold a in MU2, RFm, VAL1, VAL2, NRS2, EWS, HDR2, ATK2, AK2. change (lal_state a mb msz need) with (sec_st a mb msz need) in *.
  set (a1 := sec_st a mb msz need) in *.
  pose proof (placed_num _ _ PLm ltac:(clear -MSG N1; lia)) as (Q1 & Q2 & Q3). pose proof PLm as (_ & CEm0 & _).
  assert (MSZ : msz = round_up need 4096 + 4096) by (subst msz need; unfold map_size, kPageSize; reflexivity).
  assert (MBP : mb mod 4096 = 0 /\ 0 < mb) by (clear -Q1 MB4K; lia).
  pose proof (msz_facts mb msz need (conj N1 N8) MSZ MBP) as (_ & MS4K & _ & MB8 & MS8).
  assert (AGB2 : forall z, 0 <= z < 2^64 -> ~ (usp - 768 <= z < usp - 48) -> ~ (0xaafc8 <= z < 0xaafd9) -> ~ (0xaafe0 <= z < 0xab204) -> ~ (0xab218 <= z < 0xab228) ->
                 ~ (T + 2872 <= z < T + 2888) -> ~ (mb <= z < mb + msz) ->
                 ~ (kShadowBase + mb / 8 <= z < kShadowBase + mb / 8 + msz / 8) -> ~ (PA <= z < PA + 8 * kChunksBlockCount) -> m2 (wa z) = m1 (wa z)).
  { intros z Hz N0' N1' N1b N1c N2' N3' N4' N5'. apply MU2. rewrite wa_unsigned by (clear -Hz; lia).
    assert (LG : 0 <= Z.log2 msz < 63) by (split; [apply Z.log2_nonneg| apply (proj1 (Z.log2_lt_pow2 msz 63 ltac:(clear -MSG N1; lia))); clear -MSU N2; lia]).
    unfold lal_W. change (lal_msz need) with msz. fold a. unfold kChunksBlockCount, kPtrArrayCommit in *.
    pose proof WSC as [(P0 & S0 & _)|(P1 & _)].
    - unfold n_chunks. rewrite S0, P0. replace (Z.of_nat (@length secchunk []) =? 0) with true by reflexivity. cbn [app outside].
      clear -Hz N0' N1' N1b N1c N2' N3' N4' N5' LG. repeat split; try exact I; lia.
    - rewrite P1. replace (n_chunks a =? 16384) with false by (symmetry; apply Z.eqb_neq; clear -NCH; lia).
      cbn [app outside]. unfold n_chunks in NCH |- *. clear -Hz N0' N1' N1b N1c N2' N3' N4' N5' LG NCH. repeat split; try exact I; lia. }
  (* [comment removed for export] *)
  assert (CFR2 : rw_cells bsegs m2 (usp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { eapply rw_cells_agree; [| exact CFR1]. cbn. intros z Hz.
    apply AGB2; clear -Hz LOC LO CR SPH Q1 Q2 CEm0 Thi WE17 Timg; unfold K_CA, kShadowBase, kChunksBlockCount in *; Z.div_mod_to_equations; lia. }
  (* [comment removed for export] *)
  set (P2 := PP (sA a1 s) mo2).
  assert (AK2' : AKern E0 (aps_alloc (sA a1 s)) mo2) by (rewrite aps_alloc_sA; exact AK2).
  assert (PSTK2 : forall y k, lo <= y -> y + Z.of_nat k <= usp -> P2 (Z_to_bv 64 y, k)).
  { intros y k H1 H2. unfold P2, BF_caT.PP. apply (pol_stack' E0 FSB0 HR0 (sA a1 s) mo2 AK2' WE ENV0); clear -H1 H2 LOC SPH CR; lia. }
  pose proof (PP_KIP E0 FSB0 HR0 L0 RES0 EB0 (sA a1 s) mo2 _ _ ATK2) as KIP2.
  eapply (rzA_seg_cfg bsegs (aSc (sA a1 s)) (aNc (sA a1 s)) (aEBc (sA a1 s)) P2).
  { replace (ret_pc (Z_to_bv 64 0x37154)) with (Z_to_bv 64 0x37154) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    eapply (ca_sec_back P2 ra sp gp tp F fc lo LOC ltac:(clear -LO; unfold K_CA in LO; lia) PSTK2); [exact MI2| exact SK2| exact CFR2| clear -Q1 Q2 MSG N1 CR; lia]. }
  { exact KIP2. }
  intros ms3 mo3 HQ3 AG3 KIP3.
  destruct HQ3 as (yt0 & yt1 & yt2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & yt3 & yt4 & yt5 & yt6 & m3 & -> & MU3 & WM3 & MI3 & SK3).
  pose proof (magree_frame _ _ AG3) as (Ffds3 & Fvm3 & Flz3 & Ffs3 & Fh3 & Ftid3 & _).
  destruct KIP3 as [KIA3 _].
  pose proof (ATOK_magree _ _ _ _ _ _ _ _ _ _ _ ATK2 AG3 KIA3) as ATK3.
  pose proof (AKern_frame _ _ _ _ Fvm3 Flz3 AK2) as AK3.
  assert (AGB3 : forall z, 0 <= z < usp - 48 -> m3 (wa z) = m2 (wa z)).
  { intros z Hz. apply MU3. rewrite wa_unsigned by (clear -Hz SPH; lia). cbn [outside]. clear -Hz. repeat split; try exact I; lia. }
  (* [comment removed for export] *)
  assert (NCH20 : n_chunks a < 2^20) by (unfold kChunksBlockCount in NCH; clear -NCH; lia).
  destruct (arun_ca_op_sec E0 n a mb PR VAL1 VAL2 NCH20) as [evs RUN]. fold msz need a1 in RUN.
  assert (RUN' : arun 2%nat (sec_alloc E0 (needed n) a) (AnsOk mb :: (if n_chunks a =? as_ptr_committed a then [AnsOk (PA + 8 * as_ptr_committed a)] else []))
                 = Some (a1, ONorm (Some (mb + kPageSize)), evs, [])) by (rewrite <- (ca_op_sec E0 n a PR); exact RUN).
  pose proof (hoare_arun _ _ _ a 2%nat _ _ _ _ _ (sec_alloc_spec E0 [] [] a n Hwf NCH) eq_refl RUN') as HQ.
  cbv beta in HQ. destruct HQ as (WF1 & _ & _ & _ & _ & _ & _ & _ & (r0 & ER0 & ESEC & SFRESH)).
  assert (ER : r0 = mb) by (unfold kPageSize in ER0; clear -ER0; lia). subst r0. fold msz need in ESEC, SFRESH.
  pose proof SFRESH as (_ & APPm & CEm & SPm & SECm & RESm).
  pose proof (sec_keep E0 a mb msz need) as (Kcs & Kqb & Kdi & Klive & Knp & Knd & KgR & KgD & Kreg & Knb & Ksb). fold a1 in Kcs, Kqb, Kdi, Klive, Knp, Knd, KgR, KgD, Kreg, Knb, Ksb.
  (* [comment removed for export] *)
  assert (OUT : forall z, rt_fpc E0 FSB0 PL0 z -> m3 (wa z) = m (wa z)).
  { intros z Hz. pose proof (resv_range_num E0 d0 dl DR0 ltac:(clear -DD1 DD2; lia)) as (DQ1 & DQ2 & DQ3 & DQ4).
    pose proof CR0 as (CRin & _ & _ & _ & _ & _ & CRpa & _). pose proof DR0 as (DRin & _ & _ & _ & _ & _ & DRpa & _).
    pose proof (placed_s_num _ _ TR2 ltac:(clear; lia)) as (TQ1 & TQ2 & TQ3 & TQ4).
    destruct (rt_fpc_where E0 FSB0 PL0 z Hz) as [(Z1 & _ & _ & NM)|RH].
    - rewrite AGB3 by (clear -Z1 LOC LO CR; unfold K_CA in *; lia).
      rewrite AGB2; [apply AGB; clear -Z1 LOC LO CR; unfold K_CA in *; lia| clear -Z1 LOC LO CR; unfold K_CA in *; lia| clear -Z1 LOC LO CR; unfold K_CA in *; lia| | | | clear -Z1 Timg; lia| clear -Z1 Q1; lia
                   | unfold kShadowBase; clear -Z1 Q1; lia| ].
      + intros R. apply NM. exists (aic_instance both_ic, 3632). split; [left; reflexivity| cbn [fst snd aic_instance both_ic]; clear -R; lia].
      + intros R. apply NM. exists (aic_instance both_ic, 3632). split; [left; reflexivity| cbn [fst snd aic_instance both_ic]; clear -R; lia].
      + intros R. apply NM. exists (aic_instance both_ic, 3632). split; [left; reflexivity| cbn [fst snd aic_instance both_ic]; clear -R; lia].
      + intros R. unfold img_sep in *. pose proof WE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E33 & _).
        unfold img_sep in E33. rewrite EI1 in E33. unfold kChunksBlockCount in R. clear -Z1 R E33 EI2. lia.
    - unfold rt_high2 in RH.
      assert (ZB : 0 <= z < usp - 768) by (clear -RH Tlo Thi CQ1 CQ2 DQ1 DQ2 CC1 CC2 DD1 DD2 LOC LO CR; unfold K_CA in *; lia).
      rewrite AGB3 by (clear -ZB; lia). rewrite AGB2; [apply AGB; clear -ZB; lia| clear -ZB SPH; lia| clear -ZB; lia| | | | | | |].
      + clear -RH TQ3 CQ3 DQ3 CC1 CC2 DD1 DD2. lia.
      + clear -RH TQ3 CQ3 DQ3 CC1 CC2 DD1 DD2. lia.
      + clear -RH TQ3 CQ3 DQ3 CC1 CC2 DD1 DD2. lia.
      + clear -RH CT DT. lia.
      + intros R. destruct RH as [RH|[RH|RH]].
        * pose proof (RSVm _ WE13) as X. cbn [fst snd] in X. clear -RH R X. lia.
        * pose proof (RSVm _ CRin) as X. cbn [fst snd] in X. clear -RH R X CC1 CC2. lia.
        * pose proof (RSVm _ DRin) as X. cbn [fst snd] in X. clear -RH R X DD1 DD2. lia.
      + intros R. unfold kShadowBase in R. clear -RH R TQ4 CQ4 DQ4 CC1 CC2 DD1 DD2 Q1 Q2. Z.div_mod_to_equations. lia.
      + unfold kChunksBlockCount, kPtrArrayLen in *. clear -RH WE23 CRpa DRpa CC1 CC2 DD1 DD2. lia. }
  assert (RT3 : rt_misc5 FSB0 PL0 E0 m3) by (apply (rt_misc5_agree E0 FSB0 PL0 m m3 Hrt); exact OUT).
  (* [comment removed for export] *)
  assert (PC1 : as_ptr_committed a1 = kChunksBlockCount).
  { subst a1. rewrite sec_ptr. pose proof WSC as [(P0 & S0 & _)|(P1 & _)].
    - unfold n_chunks. rewrite S0, P0. reflexivity.
    - rewrite P1. replace (n_chunks a =? kChunksBlockCount) with false by (symmetry; apply Z.eqb_neq; clear -NCH; lia). reflexivity. }
  assert (TOK3 : RTOKc (C - ca_cost n) (C' - ca_gcost n) (sA a1 s) mo3).
  { apply (RTOK_intro E0 FSB0 HR0 L0 RES0 EB0 (C - ca_cost n) (C' - ca_gcost n) (sA a1 s) mo3 _ _ ATK3); rewrite ?aps_alloc_sA.
    - unfold ca_cost. rewrite PR. fold msz. clear -CHG C2A. lia.
    - rewrite KgR. exact GR0.
    - rewrite KgD. exact GD0.
    - unfold ca_cost. rewrite PR. fold msz. rewrite KgR, KgD. unfold gapP at 1. rewrite PC1. cbn [kChunksBlockCount Z.eqb].
      unfold gapP in RLE. pose proof WSC as [(P0 & S0 & _)|(P1 & _)].
      + rewrite P0 in RLE. cbn [Z.eqb] in RLE. unfold n_chunks. rewrite S0, P0. replace (Z.of_nat (length (@nil secchunk)) =? 0) with true by reflexivity. unfold kPtrArrayCommit in RLE. clear -RLE CHG C2A. lia.
      + rewrite P1 in RLE |- *. cbn [kChunksBlockCount Z.eqb] in RLE. replace (n_chunks a =? kChunksBlockCount) with false by (symmetry; apply Z.eqb_neq; clear -NCH; lia).
        clear -RLE CHG C2A. lia.
    - unfold lal_gcost. change (lal_msz need) with msz. unfold ca_gcost in GC |- *. rewrite PR in GC |- *. fold msz in GC |- *. clear -GC HCR'. lia. }
  (* [comment removed for export] *)
  Ltac to3 AGB3 H := eapply rw_cells_agree; [| exact H]; cbn -[Z.add Z.mul Z.sub Z.div]; intros; apply AGB3.
  assert (INST3632 : ae_instance E0 = 0xaaf58) by (unfold ae_instance; rewrite IC0; reflexivity).
  (* [comment removed for export] *)
  assert (REPX : ARepX bsegs E0 (DepotR bsegs E0) a1 m3 (mb + 4096) (mb + msz)).
  { subst a1. eapply (ARepX_sec bsegs E0 a m m3 (usp - 768) mb msz need).
    - eapply wmono_trans; [exact WM1| eapply wmono_trans; [exact WM2| exact WM3]].
    - intros z Hz NF. unfold FPWsec in NF. rewrite INST3632 in NF.
      assert (Z1 : z < usp - 768) by (clear -NF; lia).
      rewrite AGB3 by (clear -Hz Z1; lia). rewrite AGB2; [apply AGB; clear -Hz Z1; lia| clear -Hz Z1; lia| clear -Hz Z1; lia| | | | | | |]; clear -NF Hz; unfold kThrStats in *; lia.
    - clear -LOC LO; unfold K_CA in LO; lia.
    - exact Hrep.
    - exact Hwf.
    - exact (blocks_sep_of E0 a mo ENV0 Hwf Hkern).
    - clear -Tlo Thi Timg. repeat split; lia.
    - intros r Hr. pose proof (IMGR r Hr) as X. rewrite EI1. clear -X EI2. lia.
    - rewrite EI1. clear; lia.
    - exact IMGR.
    - intros r Hr. rewrite INST3632. unfold arep_img_ranges, depot_static in Hr. rewrite IC0 in Hr.
      cbn -[Z.add Z.mul Z.le] in Hr. repeat (destruct Hr as [<-|Hr]; [cbn; clear; lia|]). destruct Hr.
    - exists mo. exact Hkern.
    - exact TDN.
    - split; [exact D0a| exact D0b].
    - split; [exact N1| exact N8].
    - exact MSZ.
    - exact MBP.
    - split; [exact APPm| split; [exact CEm|]].
      pose proof WE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E29 & _).
      unfold img_sep. pose proof (RSVm _ E29) as X. exact X.
    - exact RSVm.
    - exact RFm.
    - (* [comment removed for export] *)
      rewrite INST3632. unfold kInsNReserved.
      replace (as_ptr_committed (sec_st a mb msz need)) with (as_ptr_committed (lal_a3 a mb msz need))
        by (unfold lal_a3, lal_a2, sec_st, sec_commit; destruct (n_chunks _ =? _) eqn:Eb; rewrite ?Eb; destruct a; cbn in Eb |- *; rewrite ?Eb; reflexivity).
      to3 AGB3 NRS2. clear -H LOC LO CR; unfold K_CA in *; lia.
    - rewrite INST3632. unfold kInsSecStats, AsanRep.zw. fold SS. rewrite <- (zw_mod_add (ss_n_allocs SS) 1), <- (ZBridge.Z_to_bv_mod64 (ss_n_frees SS)).
      to3 AGB3 SST2. clear -H LOC LO CR; unfold K_CA in *; lia.
    - exists bsl'. split; [| exact LBSL2]. rewrite INST3632. unfold kInsSecStats.
      eapply u64arr_agree; [| exact BSL2]. rewrite LBSL2. intros z Hz. apply AGB3. clear -Hz LOC LO CR; unfold K_CA in *; lia.
    - rewrite INST3632. unfold kInsSecMutex. to3 AGB3 MTX2. clear -H LOC LO CR; unfold K_CA in *; lia.
    - rewrite INST3632. unfold kInsGlobalStats, AsanRep.zw. rewrite <- (zw_mod_add (as_glob_allocated a) msz), <- (zw_mod_add (as_glob_mapped a) msz).
      to3 AGB3 GST2. clear -H LOC LO CR; unfold K_CA in *; lia.
    - unfold AsanRep.zw. fold ts. rewrite <- (zw_mod_add (ts_mmaps ts) 1), <- (zw_mod_add (ts_mmaped ts) msz). unfold kThrStats. replace (T + 2800 + 72) with (T + 2872) by (clear; lia).
      to3 AGB3 TST2. clear -H WE15 Tlo LOC LO CR; unfold K_CA in *; lia.
    - (* [comment removed for export] *)
      assert (ARR3 : u64arr bsegs m3 PA ws').
      { eapply u64arr_agree; [| exact ARR2]. rewrite EWS, upd_length.
        assert (LL : (length (if (n_chunks a =? as_ptr_committed a)%Z then repeat (Z_to_bv 64 0) (Z.to_nat kChunksBlockCount) else ws) <= Z.to_nat kChunksBlockCount)%nat).
        { destruct (n_chunks a =? as_ptr_committed a); [rewrite repeat_length; clear; lia| rewrite LWS; clear -PCB; lia]. }
        intros z Hz. apply AGB3. unfold kChunksBlockCount in *. clear -Hz LL WE16 WE17 LOC LO CR; unfold K_CA in *; lia. }
      rewrite EWS in ARR3. pose proof WSC as [(P0 & S0 & W0)|(P1 & junk & EW)].
      + unfold n_chunks in ARR3 |- *. rewrite S0 in ARR3 |- *. rewrite P0 in ARR3.
        change (Z.of_nat (@length secchunk [])) with 0 in ARR3. change (Z.to_nat 0) with 0%nat in ARR3. replace (0 =? 0) with true in ARR3 by reflexivity.
        exists (repeat (Z_to_bv 64 0) (Z.to_nat kChunksBlockCount - 1)%nat). split.
        * cbn [map app sc_map_beg]. replace (Z.to_nat kChunksBlockCount) with (Datatypes.S (Z.to_nat kChunksBlockCount - 1))%nat in ARR3 by (clear; unfold kChunksBlockCount; lia).
          cbn [repeat upd] in ARR3. exact ARR3.
        * rewrite repeat_length. cbn [length]. unfold kChunksBlockCount. clear; lia.
      + rewrite P1 in ARR3. replace (n_chunks a =? kChunksBlockCount) with false in ARR3 by (symmetry; apply Z.eqb_neq; clear -NCH; lia).
        rewrite EW in ARR3. destruct junk as [|j0 junk'].
        { exfalso. rewrite EW, length_app, length_map in LWS. cbn [length] in LWS. rewrite P1 in LWS. unfold n_chunks, kChunksBlockCount in NCH, LWS. clear -NCH LWS. lia. }
        exists junk'. split.
        * unfold n_chunks in ARR3. rewrite Nat2Z.id in ARR3. rewrite <- (length_map (fun c => zw (sc_map_beg c)) (as_sec a)) in ARR3 at 1 || idtac.
          replace (Z.to_nat (Z.of_nat (length (as_sec a)))) with (length (map (fun c : secchunk => zw (sc_map_beg c)) (as_sec a))) in ARR3 by (rewrite length_map; clear; lia).
          rewrite upd_app_mid in ARR3. rewrite map_app. cbn [map sc_map_beg]. rewrite <- app_assoc. cbn [app]. exact ARR3.
        * rewrite EW, length_app, length_map in LWS. cbn [length] in LWS |- *. rewrite P1 in LWS. clear -LWS. lia.
    - to3 AGB3 HDR2. clear -H Q1 CEm0 MSG N1 LOC LO CR; unfold K_CA in *; lia.
    - (* [comment removed for export] *)
      pose proof (rwc_join_at bsegs m2 _ _ _ _ HDR2 BODY2 ltac:(cbn; clear; lia)) as HB.
      eapply wr_at_transport; [| exact WM3]. eapply rw_cells_wr_at; [exact HB|].
      cbn [cells_size csize app]. rewrite ?Nat.add_0_r, !Nat2Z.inj_add, Z2Nat.id by (clear -MSG N1; lia). clear; cbn; lia.
    - to3 AGB3 SHH2. unfold kShadowBase in *. clear -H Q1 Q2 MSG N1 LOC LO CR; unfold K_CA in *; Z.div_mod_to_equations; lia.
    - exact DNP.
    - exact NCH. }
  (* [comment removed for export] *)
  pose proof WE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & WE29 & _ & _ & _ & WE33 & _).
  apply CONT with (a1 := a1) (ab := mb + 4096). unfold ca_post.
  split; [exact SK3|]. split; [eapply wmono_trans; [exact WM1| eapply wmono_trans; [exact WM2| exact WM3]]|].
  split.
  { set (W := [(usp - 768, usp); (0xaafc8, 0xab228); (T + 2872, T + 2888); (mb, mb + msz); (kShadowBase + mb / 8, kShadowBase + mb / 8 + msz / 8); (PA, PA + 8 * kChunksBlockCount)]).
    exists W. split; [| split].
    - (* [comment removed for export] *)
      intros x Hx. pose proof (bv_unsigned_in_range 64 x) as XR. change (bv_modulus 64) with (2^64) in XR.
      rewrite <- (Nodes.wa_unsigned_id x). cbn [W outside] in Hx. destruct Hx as (O1 & O2 & O3 & O4 & O5 & O6 & _).
      destruct (Z_lt_le_dec (bv_unsigned x) (usp - 768)) as [LT|GE].
      + rewrite AGB3 by (clear -LT XR; lia). rewrite AGB2; [apply AGB; clear -LT XR; lia| clear -LT XR; lia| clear -LT XR; lia| clear -O2; lia| clear -O2; lia| clear -O2; lia| exact O3| exact O4| exact O5| exact O6].
      + assert (UP : usp <= bv_unsigned x) by (clear -O1 GE; lia).
        assert (LG : 0 <= Z.log2 msz < 63) by (split; [apply Z.log2_nonneg| apply (proj1 (Z.log2_lt_pow2 msz 63 ltac:(clear -MSG N1; lia))); clear -MSU N2; lia]).
        rewrite (Nodes.wa_unsigned_id x).
        rewrite (MU3 x) by (cbn [outside]; clear -UP; split; [lia| exact I]).
        rewrite (MU2 x).
        2:{ assert (NC0 : 0 <= n_chunks a) by (unfold n_chunks; clear; lia).
            unfold lal_W. change (lal_msz need) with msz. fold a. destruct (n_chunks a =? as_ptr_committed a); cbn [outside app];
            unfold kChunksBlockCount, kPtrArrayCommit, kShadowBase, K_CA in *; clear -UP XR Q1 CEm0 LOC LO CR Thi WE17 MSG N1 LG NC0 NCH;
            repeat split; try exact I; Z.div_mod_to_equations; lia. }
        apply MU1. cbn [outside]. clear -UP. split; [lia| exact I].
    - (* [comment removed for export] *)
      subst W. repeat (apply Forall_cons; [unfold aw_ok; cbn [fst snd]|]); [.. | apply Forall_nil].
      + left. clear -LO; unfold K_CA in LO; lia.
      + right; left. exists (aic_instance both_ic, 3632). split; [left; reflexivity| cbn [fst snd aic_instance both_ic]; clear; lia].
      + right; right; left. exists (T + kThrStats, 112 + 8 * 32). split; [unfold arep_thr_ranges; do 5 right; left; reflexivity|]. cbn [fst snd]. unfold kThrStats. clear. lia.
      + do 5 right; left. exists (mkSec mb msz need). split; [right; subst a1; rewrite sec_sec; apply in_app_iff; right; left; reflexivity|]. cbn [sc_map_beg sc_map_size]. clear; lia.
      + do 8 right. split.
        * unfold LSHI, B_base.A_SB, kShadowBase. rewrite ?KHB, ?KLE. destruct Q3 as [LOW|HIGH]; [left; clear -LOW Q1 Q2 MB8 MS8 CR| right; clear -HIGH Q1 Q2 CEm0 MB8 MS8 CR]; Z.div_mod_to_equations; lia.
        * intros z Hz. unfold B_base.A_SB, kShadowBase in *.
          assert (GR : mb <= 8 * (z - 2147450880) < mb + msz) by (clear -Hz MB8 MS8; Z.div_mod_to_equations; lia).
          unfold sh_excluded. pose proof WE as (_ & _ & WE3' & WE4' & _ & _ & WE7' & _ & WE9' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & WE24' & _).
          replace (in_fakestack E0 (8 * (z - 2147450880))) with false by (symmetry; unfold in_fakestack; apply Bool.andb_false_iff; pose proof (RSVm _ WE9') as X; cbn [fst snd] in X; destruct X; [left; apply Z.leb_gt| right; apply Z.ltb_ge]; clear -H GR; lia).
          replace (in_iarena E0 (8 * (z - 2147450880))) with false by (symmetry; unfold in_iarena; apply Bool.andb_false_iff; pose proof (RSVm _ WE24') as X; cbn [fst snd] in X; destruct X; [left; apply Z.leb_gt| right; apply Z.ltb_ge]; clear -H GR; lia).
          replace (in_reginfo E0 (8 * (z - 2147450880))) with false by (symmetry; unfold in_reginfo; apply Bool.andb_false_iff; pose proof (RSVm _ WE7') as X; cbn [fst snd] in X; unfold kSpaceSize, kPageSize in *; destruct X; [left; apply Z.leb_gt| right; apply Z.ltb_ge]; clear -H GR WE3' WE4'; lia).
          reflexivity.
      + do 4 right; left. unfold kPtrArrayLen, kChunksBlockCount. clear; lia.
    - (* [comment removed for export] *)
      subst W. repeat (apply Forall_cons; [cbn [fst snd]; intros blo bsz LIVE; destruct (live_block_where E0 a blo bsz Hwf LIVE) as (B0 & B1 & B2 & B3)|]); [.. | apply Forall_nil].
      + right; right. clear -B1 LOC LO; unfold K_CA in LO; lia.
      + right. destruct B3 as [[S1 S2]|(sc & Hsc & S1 & S2)]; [rewrite KHB in WE2; clear -S1 WE2 WE3; lia|].
        destruct (WS3 sc Hsc) as (_ & _ & _ & _ & _ & _ & SR). pose proof (SR _ WE29) as X. rewrite EI1 in X. clear -X S1 S2 EI2. lia.
      + destruct (live_block_off_thread E0 a blo bsz Hwf LIVE) as [_ [X|X]]; [right; right| right; left]; clear -X; lia.
      + right. destruct B3 as [[S1 S2]|(sc & Hsc & S1 & S2)].
        * destruct SPm as [X|X]; [left| right]; clear -X S1 S2; lia.
        * destruct (SECm sc Hsc) as [X|X]; [left| right]; clear -X S1 S2; lia.
      + right. unfold kShadowBase. rewrite KHB, KLE in B2. clear -B0 B2 Q1 Q2. Z.div_mod_to_equations. lia.
      + right. destruct B3 as [[S1 S2]|(sc & Hsc & S1 & S2)].
        * unfold kChunksBlockCount. pose proof WE as (_ & _ & WE3' & WE4' & _). unfold kSpaceSize in *. clear -S1 S2 WE20 B0 WE3' WE4'. lia.
        * destruct (WS3 sc Hsc) as (_ & _ & _ & _ & _ & _ & SR). pose proof (SR _ WE8) as X. cbn [fst snd] in X. unfold kChunksBlockCount. clear -X S1 S2 B0. lia. }
  split; [exists 2%nat, (AnsOk mb :: (if n_chunks a =? as_ptr_committed a then [AnsOk (PA + 8 * as_ptr_committed a)] else [])), evs, []; exact RUN|].
  split.
  { split; [exact WF1|]. split; [exact AK3|]. split; [exact (res_ok_sec a mb msz need Hres)|]. split; [exact (Kqb Hqb)|]. split; [exact (Kdi Hdi)|].
    split; [exact MI3|]. split; [exact RT3|]. split; [apply (sstats_sec a mb msz need Hss); clear -MSG N1 SECB MSU N2; lia| exact (Kcs Hcs)]. }
  split; [exact TOK3|].
  split; [rewrite Ffs3, Ffs2, Ffs1; reflexivity|]. split; [rewrite Ffds3, Ffds2, Ffds1; reflexivity|]. split; [rewrite Ftid3, Ftid2, Ftid1; reflexivity|].
  split; [reflexivity|].
  split; [unfold ca_span; rewrite PR; fold need; replace (mb + 4096 + round_up need kPageSize) with (mb + msz) by (subst msz need; unfold map_size, kPageSize; clear; lia); exact REPX|].
  unfold ca_span. rewrite PR. fold need. split.
  { (* [comment removed for export] *)
    exists (hj' ++ repeat (Z_to_bv 8 250) (Z.to_nat ((msz - 4096 - need) / 8))).
    split; [| intros X; discriminate].
    pose proof (rwc_join_at bsegs m2 _ _ _ _ SHU2 SHT2) as J.
    assert (LJ : length hj' = Z.to_nat (need / 8)) by (destruct SHU2 as [[WFc _] _]; cbn in WFc; destruct WFc as [WFc _]; exact WFc).
    specialize (J ltac:(cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by (clear -N1; lia); unfold kShadowBase; clear -MB8 N8 N1; Z.div_mod_to_equations; lia)).
    replace (kShadowBase + (mb + 4096) / 8) with (kShadowBase + mb / 8 + 512) by (clear -MB8; Z.div_mod_to_equations; lia).
    eapply rw_cells_agree.
    2:{ eapply (rw_cells_reshape bsegs m2); [| | exact J].
        - cbn. rewrite length_app, repeat_length, LJ. split; [| exact I]. replace (round_up need kPageSize) with (msz - 4096) by (rewrite MSZ; unfold kPageSize; clear; lia).
          clear -N1 N8 MS8 MSG MS4K; Z.div_mod_to_equations; lia.
        - cbn [cells_bytes cbytes app]. rewrite !app_nil_r. reflexivity. }
    intros z Hz. apply AGB3. cbn [cells_size csize Nat.add] in Hz. replace (round_up need kPageSize) with (msz - 4096) in Hz by (rewrite MSZ; unfold kPageSize; clear; lia).
    rewrite Nat.add_0_r, Z2Nat.id in Hz by (clear -N1 MSG; Z.div_mod_to_equations; lia).
    unfold kShadowBase in *. clear -Hz Q1 Q2 MSG N1 LOC LO CR; unfold K_CA in *; Z.div_mod_to_equations; lia. }
  exists mb. split; [reflexivity|]. split; [subst a1; rewrite sec_sec; reflexivity| exact SFRESH].
Qed.

End CaS.

End RC__1.
