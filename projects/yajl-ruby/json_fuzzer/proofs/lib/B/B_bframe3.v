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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling PropExec MState Mem Cells Frame Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import LiaA AImages AImageFacts LazyModel NodesA Shadow BackingAlgebraA.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import StdioBase STree.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanHoare AsanRep AsanFakeStack AsanPS AsanKern AsanClient AsanDepot AsanBudget AsanBudget2 AsanGap AsanSlack.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import B_base B_alloc_iface B_iface B_live B_policy5 B_budget5 B_slack5 BI_shadow BI_lowshadow BI_lowshadow_ay BI_iface BYajlRep BYajl_iface BF_place BF_fakestack_rep B_bundle B_benv5 B_bframe B_bframe2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).

Ltac lia ::= LiaA.liaA.

Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.

(* [comment removed for export] *)
Lemma page_base_of_al8 : forall z, 0 <= z -> page_base_of (al8 z) = page_base_of z.
Proof.
  intros z Hz. unfold page_base_of, al8. rewrite B_bframe.page_size_val. f_equal. Z.div_mod_to_equations. nia.
Qed.

Lemma pages_budgeted_octets : forall S lo hi lo' hi',
  pages_budgeted S lo hi -> 0 <= lo -> lo < hi -> al8 lo <= lo' -> hi' <= al8 (hi - 1) + 8 -> pages_budgeted S lo' hi'.
Proof.
  intros S lo hi lo' hi' PB Hlo Hlt H1 H2 z Hz.
  pose proof (al8_le lo). pose proof (al8_gt lo). pose proof (al8_le (hi - 1)). pose proof (al8_gt (hi - 1)).
  pose proof (al8_mod lo). pose proof (al8_mod (hi - 1)).
  destruct (Z_lt_dec z lo) as [L|L].
  - rewrite <- (page_base_of_al8 z) by lia.
    replace (al8 z) with (al8 lo) by (unfold al8 in *; Z.div_mod_to_equations; lia).
    rewrite (page_base_of_al8 lo) by lia. apply PB. lia.
  - destruct (Z_lt_dec z hi) as [R|R]; [apply PB; lia|].
    rewrite <- (page_base_of_al8 z) by lia.
    replace (al8 z) with (al8 (hi - 1)) by (unfold al8 in *; Z.div_mod_to_equations; lia).
    rewrite (page_base_of_al8 (hi - 1)) by lia. apply PB. lia.
Qed.

Lemma C_SB_val : C_SB = 0x7fff8000. Proof. reflexivity. Qed.
Lemma kShadowBase_val : kShadowBase = 0x7fff8000. Proof. reflexivity. Qed.
Lemma kHighMemEnd_val : kHighMemEnd = 2^47 - 1. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma NoDup_map_inj : forall {A B} (f : A -> B) (l : list A),
  List.NoDup l -> (forall x y, In x l -> In y l -> f x = f y -> x = y) -> List.NoDup (map f l).
Proof.
  intros A B f l ND INJ. induction ND as [|x l NI ND IH]; cbn; constructor.
  - intros Hin. apply in_map_iff in Hin as (y & E & Hy). apply NI. rewrite (INJ x y (or_introl eq_refl) (or_intror Hy) (eq_sym E)). exact Hy.
  - apply IH. intros a b Ha Hb E. apply INJ; [right; exact Ha| right; exact Hb| exact E].
Qed.

Section Bundle.
(* [comment removed for export] *)
Variable StdioRep : stdout_st -> mem -> Prop.
Variable RTMisc : aenv -> mem -> Prop.
Variable E0 : aenv.
Variable FSB0 : Z.
Variable HR0 : list (Z * Z).
Variables L0 RES0 : list (word * word).
Variable EB0 : Z.
#[local] Notation AHKc := (AHK StdioRep RTMisc E0 FSB0 HR0 L0 RES0 EB0).
#[local] Notation aSc := (aS E0 FSB0 HR0).
#[local] Notation aNc := (aN E0 FSB0 HR0).
#[local] Notation aEBc := (aEB EB0).
Variable PL0 : fs_plumb.
Hypothesis ENV0 : env0_ok5 E0.
Hypothesis PL0OK : pl0_ok5 E0 PL0.
Hypothesis StdioRep_buf : forall so m, StdioRep so m -> Z.of_nat (length (so_buf so)) <= 1024.
Ltac clear_all_hyps := clear StdioRep_buf PL0OK ENV0.

Ltac zground :=
  repeat match goal with
    | |- context [?a ^ ?e] => let v := eval vm_compute in (a ^ e) in change (a ^ e) with v
    | |- context [Z.shiftl ?a ?b] => let v := eval vm_compute in (Z.shiftl a b) in change (Z.shiftl a b) with v
    | H : context [?a ^ ?e] |- _ => let v := eval vm_compute in (a ^ e) in change (a ^ e) with v in H
    | H : context [Z.shiftl ?a ?b] |- _ => let v := eval vm_compute in (Z.shiftl a b) in change (Z.shiftl a b) with v in H
    end.
(* [comment removed for export] *)
#[local] Notation live_block_geom := (B_bframe.live_block_geom E0 FSB0).
#[local] Notation live_block_fs_sep := (B_bframe.live_block_fs_sep E0 FSB0).
#[local] Notation lazy_disjoint_img := (B_bframe.lazy_disjoint_img E0 FSB0 ENV0).
#[local] Notation lazy_disjoint_stack := (B_bframe.lazy_disjoint_stack E0 FSB0).
#[local] Notation lazy_disjoint_block := (B_bframe.lazy_disjoint_block E0 FSB0).
#[local] Notation pages_budgeted_block := (B_bframe.pages_budgeted_block E0 FSB0 HR0).
#[local] Notation pages_budgeted_A0 := (B_bframe.pages_budgeted_A0 E0 FSB0 HR0).
#[local] Notation In_A0_S0 := (B_bframe.In_A0_S0 E0 FSB0 HR0).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma live_block_img_sep : forall {P D} s mo A n,
  AWf (aps_env s) P D (aps_alloc s) -> AKern (aps_env s) (aps_alloc s) mo -> ENVOK E0 FSB0 s ->
  In (A, n) (live_blocks (aps_alloc s)) ->
  A + n <= fst (ae_img (aps_env s)) \/ fst (ae_img (aps_env s)) + snd (ae_img (aps_env s)) + 4096 <= A.
Proof.
  clear_all_hyps.
  intros P D s mo A n WF K EV Hin. pose proof B_bframe.ceil_range as CR.
  destruct (live_blocks_chunk _ _ _ Hin) as (cb & cm & i & Hcm & HA & Hn & Hst).
  pose proof (chunk_user_in_block _ _ _ _ _ _ WF Hcm) as (U1 & U2 & U3).
  pose proof (chunk_block_committed _ _ _ _ _ _ WF Hcm) as BC.
  unfold user_lo, user_hi, blk_lo in *. rewrite HA, Hn in *.
  destruct WF as (WE & WR & WC & WK & WQ & WS & WD). unfold blk_hi in *.
  pose proof (B_bframe.wf_env_img _ WE) as (WI1 & WI2 & WI3). rewrite kLowAppEnd_val in WI3.
  destruct (cm_prim cm) as [c|].
  - destruct BC as (Hc & B1 & B2).
    destruct WR as [_ WR]. destruct (WR c Hc) as (R1 & R2 & R3 & _).
    pose proof (B_bframe.wf_env_resv _ WE) as (WE2 & WE3 & _). rewrite kHighMemBeg_val in WE2.
    unfold region_of, region_beg in *.
    change kRegionSize with 4294967296 in *. change kLargestClassID with 30 in Hc.
    assert (0 <= c * 4294967296) by nia.
    right. lia.
  - destruct BC as (sc & Hsc & B1 & B2).
    destruct WS as (_ & _ & WS3 & _). destruct (WS3 sc Hsc) as (M1 & M2 & M3 & M4 & M5 & M6 & M7).
    destruct (M7 _ WI1) as [X|X]; cbn [fst snd] in X; change kPageSize with 4096 in *; [left| right]; lia.
Qed.

(* [comment removed for export] *)
Lemma shadow_window_dom : forall s LB LF m mo lo hi,
  AHKc s LB LF m mo -> 0x7fff8000 <= lo -> lo <= hi -> hi <= 2^64 ->
  (forall g, lo <= 0x7fff8000 + g < hi ->
     sh_default_dom (aps_env s) (8 * g) = true /\ sh_excluded (aps_env s) (8 * g) = false) ->
  exists ws, bytes_at bsegs m lo ws /\ Z.of_nat (length ws) = hi - lo
             /\ (forall g v, lo <= 0x7fff8000 + g < hi -> Sh (aps_env s) (aps_alloc s) (8 * g) = Some v ->
                   nth_error ws (Z.to_nat (0x7fff8000 + g - lo)) = Some (AsanRep.zb v))
             /\ stk bsegs m lo hi.
Proof.
  clear_all_hyps.
  intros s LB LF m mo lo hi H Hlo Hle Hhi HG. pose proof H as H0. ahk_open H.
  assert (CELL : forall g, lo <= 0x7fff8000 + g < hi -> exists v, Sh (aps_env s) (aps_alloc s) (8 * g) = Some v
                   /\ rw_cells bsegs m (0x7fff8000 + g) [C1 (AsanRep.zb v)]).
  { intros g Hg. destruct (HG g Hg) as [G1 G2].
    destruct (Sh_total_dom (aps_env s) (aps_alloc s) (8 * g) G1 G2) as [v Hv].
    exists v. split; [exact Hv|]. pose proof (ARep_shadow_cells _ _ _ _ _ g v Hrep Hv) as C. rewrite kShadowBase_val in C. exact C. }
  assert (STK : stk bsegs m lo hi).
  { split; [lia|]. split; [exact Hhi|].
    intros a Ha. destruct (CELL (a - 0x7fff8000) ltac:(lia)) as (v & _ & R).
    replace (0x7fff8000 + (a - 0x7fff8000)) with a in R by lia.
    pose proof (stk_of_rw_cells bsegs m a _ R) as (S1 & S2 & S3). cbn [cells_size csize] in S3. apply S3. lia. }
  destruct (stk_bytes bsegs m lo hi STK Hle) as (ws & Hlen & BA).
  exists ws. split; [exact BA|]. split; [lia|]. split; [| exact STK].
  intros g v Hg Hv. destruct (CELL g Hg) as (v' & Hv' & R). rewrite Hv in Hv'. injection Hv' as <-.
  destruct BA as (_ & _ & BA). rewrite <- (BA (Z.to_nat (0x7fff8000 + g - lo))) by lia.
  destruct R as [[_ (_ & _ & RB)] _]. cbn [cells_bytes cbytes app length] in RB.
  specialize (RB 0%nat ltac:(cbn; lia)). cbn [nth_error] in RB. rewrite <- RB. f_equal. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma AHK_icp_block_shadow : forall s LB LF m mo b A n,
  AHKc s LB LF m mo -> In b LB -> ab_addr b <= A -> 1 <= n -> A + n <= ab_addr b + ab_size b ->
  exists ws, shadow_window bsegs m C_SB A n ws /\ range_clean C_SB A n ws /\ app_mem (ab_addr b) (ab_size b).
Proof.
  intros s LB LF m mo b A n H Hb HA Hn HAn. pose proof H as H0. ahk_open H. pose proof B_bframe.ceil_range as CR.
  clear Hkvm Hqb Hdi Hbinv Hicp Hyst Hlow Hrt Hso Hkm Hli Hbud Hmi Hycl Hss Hcs.
  pose proof (blocks_match_In _ _ _ Hbm Hb) as HIN.
  pose proof (live_block_geom s mo b Hwf Hkern Henv HIN) as ((G1 & G2 & G3) & GA & _).
  unfold A_IMG_END in G1. unfold A_LOWAPP_END, A_HIGH_BEG in G3.
  pose proof (live_block_fs_sep s mo _ _ Hwf Hkern Henv HIN) as FSS.
  pose proof (live_block_img_sep s mo _ _ Hwf Hkern Henv HIN) as IMS.
  pose proof (live_block_iarena_sep s mo _ _ Hwf Hkern HIN) as IAS. change kIArenaLen with 65536 in IAS.
  pose proof (live_block_reginfo_sep s mo _ _ Hwf Hkern HIN) as (RIS & SBA & _).
  change kSpaceSize with 137438953472 in RIS. change kPageSize with 4096 in RIS.
  destruct (live_blocks_chunk _ _ _ HIN) as (cb & cm & i & Hcm & HB & Hsz & Hst).
  pose proof Henv as Henv0. destruct Henv as (V1 & V2 & V3 & V4 & V5 & V6 & EIN & EF1 & EF2 & EE & EFS & EI1 & EI2).
  destruct Hfs as (P1 & _).
  pose proof (shw_geom C_SB A n ltac:(rewrite C_SB_val; lia) ltac:(lia) Hn) as SG. cbv zeta in SG.
  rewrite C_SB_val in *.
  pose proof (shr3_bounds A ltac:(lia)) as R1. pose proof (shr3_bounds (A + n + -1) ltac:(lia)) as R2.
  set (g1 := Z.shiftr A 3) in *. set (g2 := Z.shiftr (A + n + -1) 3) in *.
  set (lo := shw_lo 0x7fff8000 A) in *. set (hi := shw_hi 0x7fff8000 A n) in *.
  destruct (shadow_window_dom s LB LF m mo lo hi H0 ltac:(lia) ltac:(lia) ltac:(clear -SG R2 HAn G2 CR; lia)) as (ws & BA & LEN & NTH & _).
  { intros g Hg. unfold sh_default_dom, sh_excluded, in_fakestack, in_iarena, in_reginfo, in_img. rewrite EF1, EF2, EI1.
    rewrite kHighMemBeg_val, kHighMemEnd_val, kLowAppEnd_val.
    change kIArenaLen with 65536. change kSpaceSize with 137438953472. change kPageSize with 4096.
    pose proof (B_bframe.wf_env_iarena _ (proj1 Hwf)) as (_ & _ & _ & _ & IA5).
    (* [comment removed for export] *)
    rewrite EI1 in IMS. clear - Hg SG R1 R2 HA Hn HAn G1 G2 G3 GA FSS P1 IAS IA5 RIS SBA IMS CR EI2.
    split.
    - apply Bool.orb_true_iff. destruct G3 as [LOW|HIGH].
      + left. apply andb_true_iff. split.
        * apply andb_true_iff. split; [apply Z.leb_le| apply Z.ltb_lt]; clear -Hg SG R1 R2 HA Hn HAn LOW G1; Z.div_mod_to_equations; lia.
        * apply Bool.negb_true_iff. apply Bool.andb_false_iff. right. apply Z.ltb_ge.
          destruct IMS as [X|X]; [exfalso; clear -X G1 EI2 Hn HA HAn; lia|]. clear -Hg SG R1 R2 HA Hn HAn X. Z.div_mod_to_equations; lia.
      + right. apply andb_true_iff. split; apply Z.leb_le; clear -Hg SG R1 R2 HA Hn HAn HIGH G2 CR; Z.div_mod_to_equations; lia.
    - apply Bool.orb_false_iff. split; [apply Bool.orb_false_iff; split|].
      + apply Bool.andb_false_iff. unfold kFsBytes.
        destruct FSS as [X|X]; [left; apply Z.leb_gt| right; apply Z.ltb_ge]; clear -Hg SG R1 R2 HA Hn HAn X P1; Z.div_mod_to_equations; lia.
      + apply Bool.andb_false_iff. destruct IAS as [X|X]; [left; apply Z.leb_gt| right; apply Z.ltb_ge]; clear -Hg SG R1 R2 HA Hn HAn X IA5; Z.div_mod_to_equations; lia.
      + apply Bool.andb_false_iff. destruct RIS as [X|X]; [left; apply Z.leb_gt| right; apply Z.ltb_ge]; clear -Hg SG R1 R2 HA Hn HAn X SBA; Z.div_mod_to_equations; lia. }
  exists ws. split; [split; [exact BA| exact LEN]|]. split.
  - intros g Hg. subst g1 g2.
    assert (HGA : ab_addr b <= 8 * g < ab_addr b + ab_size b) by lia.
    pose proof (live_block_Sh _ _ _ _ cb cm i g Hwf Hcm Hst ltac:(rewrite HB, Hsz; exact HGA)) as HSH.
    rewrite HB, Hsz in HSH.
    exists (AsanRep.zb (if 8 * g + 8 <=? ab_addr b + ab_size b then 0 else ab_size b mod 8)). split.
    + apply NTH; [lia| exact HSH].
    + destruct (Z.leb_spec (8 * g + 8) (ab_addr b + ab_size b)) as [LE|GT].
      * left. reflexivity.
      * right.
        clear NTH BA LEN HSH Hrep Hkern Hres Hbm Hwf Hcm Hst Henv0 FSS EIN IMS IAS RIS.
        assert (HM : 0 < ab_size b mod 8 < 8) by (clear -GT HGA GA; Z.div_mod_to_equations; lia).
        replace (bv_signed (AsanRep.zb (ab_size b mod 8))) with (ab_size b mod 8).
        2:{ unfold AsanRep.zb. rewrite Z_to_bv_signed. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn -[Z.modulo Z.add Z.sub Z.lt Z.le].
            symmetry. rewrite Z.mod_small; lia. }
        split; clear -HM GT HGA GA Hg HAn HA Hn R1 R2; Z.div_mod_to_equations; lia.
  - unfold app_mem. rewrite kLowAppEnd_val, kHighMemBeg_val. clear -G1 G2 G3. lia.
Qed.

(* [comment removed for export] *)
Lemma AHK_icp_regions : forall s LB LF m mo, AHKc s LB LF m mo ->
     lazy_disjoint mo alloc_ceiling (2^47)
  /\ lazy_disjoint mo 0x10000 0x603000
  /\ (forall b, In b LB -> lazy_disjoint mo (ab_addr b) (ab_addr b + ab_size b))
  /\ (forall b A n, In b LB -> ab_addr b <= A -> 1 <= n -> A + n <= ab_addr b + ab_size b ->
        pages_budgeted (aSc s) (shw_lo C_SB A) (shw_hi C_SB A n)).
Proof.
  intros s LB LF m mo H. pose proof H as H0. ahk_open H. pose proof B_bframe.ceil_range as CR.
  split; [| split; [| split]].
  - apply (lazy_disjoint_stack s mo _ _ Hkern Hwf Henv). lia.
  - apply (lazy_disjoint_img s mo _ _ Hkern Hwf Henv). lia.
  - intros b Hb. eapply lazy_disjoint_sub; [exact (lazy_disjoint_block s mo _ _ Hkern Hwf Henv (blocks_match_In _ _ _ Hbm Hb))| lia| lia].
  - intros b A n Hb HA Hn HAn.
    pose proof (live_block_geom s mo b Hwf Hkern Henv (blocks_match_In _ _ _ Hbm Hb)) as ((G1 & G2 & G3) & GA & _).
    unfold A_IMG_END in G1.
    pose proof (pages_budgeted_block s mo b Hwf Hkern Henv Hres (blocks_match_In _ _ _ Hbm Hb) ltac:(lia)) as PB.
    unfold oshw_lo, oshw_hi in PB. rewrite A_SB_val in PB.
    pose proof (shr3_bounds A ltac:(lia)) as R1. pose proof (shr3_bounds (A + n + -1) ltac:(lia)) as R2.
    unfold shw_lo, shw_hi. rewrite C_SB_val.
    clear Hrep Hwf Hkern Hkvm Hres Hqb Hdi Hbinv Hbm Hfs Hicp Hyst Hlow Hrt Hso Hkm Hli Hbud Hmi Henv Hycl Hss Hcs H0.
    eapply pages_budgeted_octets; [exact PB| lia| Z.div_mod_to_equations; lia| |].
    + apply al8_mono. Z.div_mod_to_equations. lia.
    + assert (E : 2147450880 + ab_addr b / 8 + (ab_size b + 7) / 8 - 1 = 2147450880 + (ab_addr b + ab_size b - 1) / 8) by (clear -GA Hn HA HAn; Z.div_mod_to_equations; lia).
      rewrite E. pose proof (al8_mono (2147450880 + Z.shiftr (A + n + -1) 3) (2147450880 + (ab_addr b + ab_size b - 1) / 8)).
      assert (Z.shiftr (A + n + -1) 3 <= (ab_addr b + ab_size b - 1) / 8) by (Z.div_mod_to_equations; lia).
      lia.
Qed.

(* [comment removed for export] *)
Lemma stack_granule_dom : forall {P D} s a,
  AWf (aps_env s) P D (aps_alloc s) -> ENVOK E0 FSB0 s -> aps_fsbase s mod 4096 = 0 ->
  (forall X, X mod 4096 = 0 -> X <= alloc_ceiling -> X <= a) -> a <= kHighMemEnd ->
  sh_default_dom (aps_env s) a = true /\ sh_excluded (aps_env s) a = false
  /\ in_some_region_map (aps_env s) (aps_alloc s) a = false /\ in_some_sec_map (aps_alloc s) a = false.
Proof.
  clear_all_hyps.
  intros P D s a WF Henv FSA PG Hhi. pose proof B_bframe.ceil_range as CR.
  destruct Henv as (V1 & V2 & V3 & V4 & V5 & V6 & EIN & EF1 & EF2 & EE & EFS & _).
  pose proof WF as (WE & _ & _ & _ & _ & WS & _).
  pose proof (B_bframe.wf_env_resv _ WE) as (E1 & E2 & E3 & E4 & _). rewrite kHighMemBeg_val in E1.
  pose proof (B_bframe.wf_env_iarena _ WE) as (_ & _ & IA3 & _ & IA5). change kIArenaLen with 65536 in IA3.
  pose proof (B_bframe.wf_env_stack _ WE) as [_ SBA].
  rewrite kFsBytes_val in *. change kSpaceSize with 137438953472 in *.
  assert (HB : 0x10007fff8000 <= a) by (apply PG; [reflexivity| clear -CR; lia]).
  assert (PC : alloc_ceiling - 4095 <= a).
  { assert (X1 : (4096 * (alloc_ceiling / 4096)) mod 4096 = 0) by (clear; Z.div_mod_to_equations; lia).
    assert (X2 : 4096 * (alloc_ceiling / 4096) <= alloc_ceiling) by (clear; Z.div_mod_to_equations; lia).
    pose proof (PG _ X1 X2) as X. clear -X. Z.div_mod_to_equations; lia. }
  split; [| split; [| split]].
  - apply sh_default_dom_high. rewrite kHighMemBeg_val. clear -HB Hhi. lia.
  - unfold sh_excluded, in_fakestack, in_iarena, in_reginfo. rewrite EF1, EF2. change kIArenaLen with 65536.
    change kSpaceSize with 137438953472. change kPageSize with 4096 in *.
    apply Bool.orb_false_iff. split; [apply Bool.orb_false_iff; split|]; apply Bool.andb_false_iff; right; apply Z.ltb_ge.
    + apply PG; [clear -FSA; Z.div_mod_to_equations; lia| exact V4].
    + apply PG; [clear -IA5; Z.div_mod_to_equations; lia| exact IA3].
    + apply PG; [clear -SBA; change (2^16) with 65536 in SBA; Z.div_mod_to_equations; lia| clear -E2 E3 E4; lia].
  - destruct (in_some_region_map (aps_env s) (aps_alloc s) a) eqn:RM; [| reflexivity].
    pose proof (region_map_in_space _ P D _ a WF RM). change kSpaceSize with 137438953472 in *. exfalso. clear -H E2 E3 E4 PC. lia.
  - unfold in_some_sec_map. apply Bool.not_true_iff_false. intros X. apply existsb_exists in X as (sc & Hsc & B).
    apply andb_true_iff in B as [B1 B2]. apply Z.leb_le in B1. apply Z.ltb_lt in B2.
    destruct WS as (_ & _ & WS3 & _). destruct (WS3 sc Hsc) as (M1 & _ & M3 & _ & M5 & _). change kPageSize with 4096 in *.
    pose proof (PG (sc_map_beg sc + sc_map_size sc) ltac:(clear -M1 M5; Z.div_mod_to_equations; lia) M3). clear -H B2. lia.
Qed.

Lemma Sh_stack_zero : forall {P D} s a,
  AWf (aps_env s) P D (aps_alloc s) -> ENVOK E0 FSB0 s -> aps_fsbase s mod 4096 = 0 ->
  (forall X, X mod 4096 = 0 -> X <= alloc_ceiling -> X <= a) -> a <= kHighMemEnd ->
  Sh (aps_env s) (aps_alloc s) a = Some 0.
Proof.
  intros P D s a WF Henv FSA PG Hhi. destruct (stack_granule_dom s a WF Henv FSA PG Hhi) as (D1 & D2 & D3 & D4).
  exact (Sh_outside_zero_dom _ _ a D1 D2 D3 D4).
Qed.

Lemma AHK_icp_stack_shadow0 : forall s LB LF m mo A n,
  AHKc s LB LF m mo -> alloc_ceiling <= A -> 1 <= n -> A + n <= 2^47 ->
  exists ws, shadow_window bsegs m C_SB A n ws /\ range_clean C_SB A n ws
             /\ pages_budgeted (aSc s) (shw_lo C_SB A) (shw_hi C_SB A n)
             /\ ws = repeat (Z_to_bv 8 0) (length ws).
Proof.
  intros s LB LF m mo A n H HA Hn HAn. pose proof H as H0. ahk_open H. pose proof B_bframe.ceil_range as CR.
  clear Hkvm Hqb Hdi Hbinv Hicp Hyst Hlow Hrt Hso Hkm Hli Hbud Hmi Hycl Hss Hcs Hbm Hres Hrep Hkern.
  pose proof Henv as Henv0. pose proof Hfs as (FSA & _).
  pose proof (shw_geom C_SB A n ltac:(rewrite C_SB_val; lia) ltac:(lia) Hn) as SG. cbv zeta in SG.
  rewrite C_SB_val in *.
  pose proof (shr3_bounds A ltac:(lia)) as R1. pose proof (shr3_bounds (A + n + -1) ltac:(lia)) as R2.
  set (g1 := Z.shiftr A 3) in *. set (g2 := Z.shiftr (A + n + -1) 3) in *.
  set (lo := shw_lo 0x7fff8000 A) in *. set (hi := shw_hi 0x7fff8000 A n) in *.
  assert (GR : forall g, lo <= 0x7fff8000 + g < hi -> (forall X, X mod 4096 = 0 -> X <= alloc_ceiling -> X <= 8 * g) /\ 8 * g + 8 <= 2^47).
  { intros g Hg. split.
    - intros X XA XC. clear -Hg SG R1 HA Hn XA XC. Z.div_mod_to_equations; lia.
    - clear -Hg SG R1 R2 HA Hn HAn. Z.div_mod_to_equations; lia. }
  assert (Z0 : forall g, lo <= 0x7fff8000 + g < hi -> Sh (aps_env s) (aps_alloc s) (8 * g) = Some 0).
  { intros g Hg. destruct (GR g Hg) as [X1 X2]. apply (Sh_stack_zero s _ Hwf Henv0 FSA X1). rewrite kHighMemEnd_val. clear -X2; lia. }
  destruct (shadow_window_dom s LB LF m mo lo hi H0 ltac:(lia) ltac:(lia) ltac:(clear -SG R2 HAn; lia)) as (ws & BA & LEN & NTH & _).
  { intros g Hg. destruct (GR g Hg) as [X1 X2].
    destruct (stack_granule_dom s (8 * g) Hwf Henv0 FSA X1 ltac:(rewrite kHighMemEnd_val; clear -X2; lia)) as (D1 & D2 & _). split; [exact D1| exact D2]. }
  exists ws. split; [split; [exact BA| exact LEN]|]. split.
  - intros g Hg. exists (AsanRep.zb 0). split; [| left; reflexivity].
    apply NTH; [clear -Hg SG; subst g1 g2; lia|]. apply Z0. clear -Hg SG; subst g1 g2; lia.
  - split.
    + (* [comment removed for export] *)
      eapply (pages_budgeted_A0 s (pgdn (sh alloc_ceiling)) kHighMemBeg); rewrite ?kHighMemBeg_val.
      * apply In_A0_S0. unfold S0_ivs5. do 2 right. left. reflexivity.
      * apply pgdn_mod.
      * unfold pgdn, sh. rewrite A_SB_val. clear -CR. Z.div_mod_to_equations; lia.
      * clear; lia.
      * unfold pgdn, sh. rewrite A_SB_val. clear -SG R1 HA CR. Z.div_mod_to_equations; lia.
      * clear -SG R2 HAn Hn HA CR. Z.div_mod_to_equations; lia.
    + (* [comment removed for export] *)
      apply nth_error_ext. intros i.
      destruct (Nat.lt_ge_cases i (length ws)) as [LT|GE].
      * rewrite nth_error_repeat by exact LT.
        set (g := lo - 0x7fff8000 + Z.of_nat i).
        replace i with (Z.to_nat (0x7fff8000 + g - lo)) by (subst g; lia).
        apply NTH; [subst g; clear -LT LEN SG; lia|]. apply Z0. subst g; clear -LT LEN SG; lia.
      * rewrite (proj2 (nth_error_None _ _) GE). symmetry. apply (proj2 (nth_error_None _ _)). rewrite repeat_length. exact GE.
Qed.

Lemma AHK_icp_stack_shadow : forall s LB LF m mo A n,
  AHKc s LB LF m mo -> alloc_ceiling <= A -> 1 <= n -> A + n <= 2^47 ->
  exists ws, shadow_window bsegs m C_SB A n ws /\ range_clean C_SB A n ws
             /\ pages_budgeted (aSc s) (shw_lo C_SB A) (shw_hi C_SB A n).
Proof.
  intros s LB LF m mo A n H HA Hn HAn. destruct (AHK_icp_stack_shadow0 s LB LF m mo A n H HA Hn HAn) as (ws & W1 & W2 & W3 & _).
  exists ws. auto.
Qed.

(* [comment removed for export] *)
Lemma AHK_icp_musl_statics_shadow : forall s LB LF m mo A n,
  AHKc s LB LF m mo -> 0x5d0810 <= A -> 1 <= n -> A + n <= 0x603000 ->
  exists ws, shadow_window bsegs m C_SB A n ws /\ range_clean C_SB A n ws
             /\ pages_budgeted (aSc s) (shw_lo C_SB A) (shw_hi C_SB A n).
Proof.
  clear_all_hyps.
  intros s LB LF m mo A n H HA Hn HAn. pose proof (AHK_low_shadow _ _ _ _ _ _ _ _ _ _ _ _ _ H) as Hlow.
  destruct (musl_statics_shadow_clean m A n Hlow HA Hn HAn) as (ws & W1 & W2).
  exists ws. rewrite C_SB_val. split; [exact W1|]. split; [exact W2|].
  pose proof (shw_geom 0x7fff8000 A n ltac:(lia) ltac:(lia) Hn) as SG. cbv zeta in SG.
  pose proof (shr3_bounds A ltac:(lia)) as R1. pose proof (shr3_bounds (A + n + -1) ltac:(lia)) as R2.
  eapply (pages_budgeted_A0 s 0x7fff7000 0x8fff7000); [| reflexivity| lia| lia| |].
  - apply In_A0_S0. unfold S0_ivs5. left. reflexivity.
  - clear -SG R1 HA. lia.
  - clear -SG R2 HAn Hn HA. lia.
Qed.

(* [comment removed for export] *)
Lemma AHK_icp_rodata_shadow : forall s LB LF m mo A n,
  AHKc s LB LF m mo -> 0x10000 <= A -> 1 <= n -> A + n <= 0x21060 ->
  exists ws, shadow_window bsegs m C_SB A n ws /\ range_clean C_SB A n ws
             /\ pages_budgeted (aSc s) (shw_lo C_SB A) (shw_hi C_SB A n).
Proof.
  clear_all_hyps.
  intros s LB LF m mo A n H HA Hn HAn. pose proof (AHK_low_shadow _ _ _ _ _ _ _ _ _ _ _ _ _ H) as Hlow.
  destruct (rodata_shadow_clean m A n Hlow HA Hn HAn) as (ws & W1 & W2).
  exists ws. rewrite C_SB_val. split; [exact W1|]. split; [exact W2|].
  pose proof (shw_geom 0x7fff8000 A n ltac:(lia) ltac:(lia) Hn) as SG. cbv zeta in SG.
  pose proof (shr3_bounds A ltac:(lia)) as R1. pose proof (shr3_bounds (A + n + -1) ltac:(lia)) as R2.
  eapply (pages_budgeted_A0 s 0x7fff7000 0x8fff7000); [| reflexivity| lia| lia| |].
  - apply In_A0_S0. unfold S0_ivs5. left. reflexivity.
  - clear -SG R1 HA. lia.
  - clear -SG R2 HAn Hn HA. lia.
Qed.

(* [comment removed for export] *)
Lemma AHK_low_pages_budgeted : forall s LB LF m mo lo hi,
  AHKc s LB LF m mo -> 0x7fff7000 <= lo -> hi <= 0x8fff7000 -> pages_budgeted (aSc s) lo hi.
Proof.
  clear_all_hyps.
  intros s LB LF m mo lo hi H H1 H2.
  eapply (pages_budgeted_A0 s 0x7fff7000 0x8fff7000); [| reflexivity| lia| lia| lia| lia].
  apply In_A0_S0. unfold S0_ivs5. left. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rodata_oshadow_clt : forall m, low_shadow_ok m -> oshadow m 0x21540 256.
Proof.
  clear_all_hyps. intros m H. unfold oshadow, block_shadow. split; [reflexivity|]. split; [lia|].
  replace (blk_shadow 256) with (low_shadow_bytes 0x7fffc2a8 32) by (vm_compute; reflexivity).
  apply low_shadow_u8arr; [exact H| lia | cbn; lia].
Qed.
Lemma rodata_oshadow_rue : forall m, low_shadow_ok m -> oshadow m 0x214c0 4.
Proof.
  clear_all_hyps. intros m H. unfold oshadow, block_shadow. split; [reflexivity|]. split; [lia|].
  replace (blk_shadow 4) with (low_shadow_bytes 0x7fffc298 1) by (vm_compute; reflexivity).
  apply low_shadow_u8arr; [exact H| lia | cbn; lia].
Qed.
Lemma rodata_oshadow_alse : forall m, low_shadow_ok m -> oshadow m 0x214e0 5.
Proof.
  clear_all_hyps. intros m H. unfold oshadow, block_shadow. split; [reflexivity|]. split; [lia|].
  replace (blk_shadow 5) with (low_shadow_bytes 0x7fffc29c 1) by (vm_compute; reflexivity).
  apply low_shadow_u8arr; [exact H| lia | cbn; lia].
Qed.
Lemma rodata_oshadow_ull : forall m, low_shadow_ok m -> oshadow m 0x21500 4.
Proof.
  clear_all_hyps. intros m H. unfold oshadow, block_shadow. split; [reflexivity|]. split; [lia|].
  replace (blk_shadow 4) with (low_shadow_bytes 0x7fffc2a0 1) by (vm_compute; reflexivity).
  apply low_shadow_u8arr; [exact H| lia | cbn; lia].
Qed.

(* [comment removed for export] *)
Lemma AHK_y_globals_shadow : forall s LB LF m mo, AHKc s LB LF m mo ->
  oshadow m AY_CALLBACKS 88 /\ oshadow m AY_NOOP_ALLOCS 32 /\ oshadow m AY_BUF_ALLOC_ERROR 32
  /\ oshadow m 0x21540 256 /\ oshadow m 0x214c0 4 /\ oshadow m 0x214e0 5 /\ oshadow m 0x21500 4.
Proof.
  clear_all_hyps.
  intros s LB LF m mo H. pose proof (AHK_low_shadow _ _ _ _ _ _ _ _ _ _ _ _ _ H) as Hlow.
  split; [exact (callbacks_oshadow m Hlow)|]. split; [exact (noop_allocs_oshadow m Hlow)|]. split; [exact (buf_alloc_error_oshadow m Hlow)|].
  split; [exact (rodata_oshadow_clt m Hlow)|]. split; [exact (rodata_oshadow_rue m Hlow)|].
  split; [exact (rodata_oshadow_alse m Hlow)| exact (rodata_oshadow_ull m Hlow)].
Qed.

(* [comment removed for export] *)
Lemma AHK_reginfo_budgeted : forall s LB LF m mo, AHKc s LB LF m mo ->
  pages_budgeted (aSc s) (ae_space_beg (aps_env s) + 2^37) (ae_space_beg (aps_env s) + 2^37 + 4096).
Proof.
  clear_all_hyps.
  intros s LB LF m mo H. pose proof B_bframe.ceil_range as CR. ahk_open H.
  destruct Henv as (_ & _ & _ & _ & _ & _ & _ & _ & _ & EE & _).
  pose proof (B_bframe.wf_env_resv _ (proj1 Hwf)) as (W1 & W2 & W3 & W4 & _). rewrite kHighMemBeg_val in W1.
  pose proof (B_bframe.wf_env_stack _ (proj1 Hwf)) as [_ AL].
  change kSpaceSize with (2^37) in W3. rewrite EE in *.
  eapply (pages_budgeted_A0 s (ae_space_beg E0 + 2^37) (ae_space_beg E0 + 2^37 + 4096)); [| | lia| lia| lia| lia].
  - apply In_A0_S0. unfold S0_ivs5. do 5 right. left. reflexivity.
  - clear -AL. change (2^16) with 65536 in AL. change (2^37) with 137438953472. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma AHK_so : forall s LB LF m mo, AHKc s LB LF m mo -> Z.of_nat (length (so_buf (aps_so s))) <= 1024.
Proof. intros s LB LF m mo H. ahk_open H. exact (StdioRep_buf _ _ Hso). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma AHK_y_aflsep : forall s LB LF m mo f1 f2,
  AHKc s LB LF m mo -> In f1 LF -> In f2 LF -> snd f1 <> snd f2 ->
  aflagB E0 FSB0 (fst f1) (snd f1) + 1 <= snd f2 \/ snd f2 + ff_bytes (fst f2) <= aflagB E0 FSB0 (fst f1) (snd f1).
Proof.
  clear_all_hyps.
  intros s LB LF m mo [N1 ff1] [N2 ff2] H I1 I2 NE. cbn [fst snd] in *. left.
  ahk_open H. clear - Henv Hfs I1 I2 NE.
  destruct Henv as (_ & _ & _ & _ & _ & _ & _ & _ & _ & EE & EF & _). rewrite EE, EF in Hfs.
  destruct Hfs as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RL).
  destruct (RL N1 ff1 I1) as (pos1 & [PC1 PP1] & ->). destruct (RL N2 ff2 I2) as (pos2 & [PC2 PP2] & ->). clear RL.
  rewrite aflagB_frame by lia.
  unfold fs_frame_addr, fs_frames_base, fs_flag_addr, fs_flags_base, fs_flags_off, fs_frame_bytes, fs_nframes,
         kFsFlagsOffset, kFsLog, kFsMinFrameLog in *.
  assert (HN1 : N1 = 0 \/ N1 = 1) by lia. assert (HN2 : N2 = 0 \/ N2 = 1) by lia.
  destruct HN1 as [-> | ->]; destruct HN2 as [-> | ->]; zground; cbn in *; lia.
Qed.

(* [comment removed for export] *)
Lemma AHK_y_flag_cell : forall s LB LF m mo f,
  AHKc s LB LF m mo -> In f LF ->
  (exists fl, rw_cells bsegs m (aflagB E0 FSB0 (fst f) (snd f)) [C1 fl])
  /\ (aflagB E0 FSB0 (fst f) (snd f) + 1 <= snd f \/ snd f + ff_bytes (fst f) <= aflagB E0 FSB0 (fst f) (snd f)).
Proof.
  clear_all_hyps.
  intros s LB LF m mo [N ff] H Hin. cbn [fst snd].
  ahk_open H. clear - Henv Hfs Hin.
  destruct Henv as (_ & _ & _ & _ & _ & _ & _ & _ & _ & EE & EF & _). rewrite EE, EF in Hfs.
  pose proof Hfs as (_ & _ & _ & _ & _ & _ & _ & FL & _ & _ & RL).
  destruct (RL N ff Hin) as (pos & POK & ->).
  rewrite aflagB_frame by (destruct POK; lia). split.
  - exists (flag_byte LF FSB0 N pos). exact (FL N pos POK).
  - left. destruct POK as [PC PP].
    unfold fs_frame_addr, fs_frames_base, fs_flag_addr, fs_flags_base, fs_flags_off, fs_frame_bytes, fs_nframes,
           kFsFlagsOffset, kFsLog, kFsMinFrameLog in *.
    assert (HN : N = 0 \/ N = 1) by lia. destruct HN as [-> | ->]; zground; cbn in *; lia.
Qed.

(* [comment removed for export] *)
Lemma AHK_y_fnodup : forall s LB LF m mo, AHKc s LB LF m mo -> List.NoDup (map snd LF).
Proof.
  clear_all_hyps.
  intros s LB LF m mo H. ahk_open H. clear - Henv Hfs.
  destruct Henv as (_ & _ & _ & _ & _ & _ & _ & _ & _ & EE & EF & _). rewrite EE, EF in Hfs.
  pose proof Hfs as (_ & _ & _ & _ & _ & _ & _ & _ & _ & ND & RL).
  apply (NoDup_map_inj snd LF ND). intros [N1 f1] [N2 f2] I1 I2 E. cbn [snd] in E. subst f2.
  destruct (RL N1 f1 I1) as (p1 & [PC1 PP1] & E1). destruct (RL N2 f1 I2) as (p2 & [PC2 PP2] & E2).
  assert (HN : N1 = N2); [| subst N2; reflexivity].
  rewrite E1 in E2. revert E2.
  unfold fs_frame_addr, fs_frames_base, fs_frame_bytes, fs_nframes, kFsFlagsOffset, kFsLog, kFsMinFrameLog in *.
  assert (H1 : N1 = 0 \/ N1 = 1) by lia. assert (H2 : N2 = 0 \/ N2 = 1) by lia.
  destruct H1 as [-> | ->]; destruct H2 as [-> | ->]; zground; cbn in *; intros E2; lia.
Qed.

End Bundle.
End RC__1.
