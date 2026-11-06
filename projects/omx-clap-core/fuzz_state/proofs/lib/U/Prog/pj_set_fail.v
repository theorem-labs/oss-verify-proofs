From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require YL01 YO0x YO0u.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Contract Img0 KindBGlue.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require MemNorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import Ledger ReaderRes parse_items_shape.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import pj_set_runs pj_set_shape pj_set_kb.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import pj_free_c pj_set_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import pj_set_tail pj_set_post.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require strtod_c.
Module YK11 := YK11.
Module YK0s := YK0s.
Module YM05 := YM05.
Module YL01 := U.Reusable.YL01.
Module MemNorm := U.MemNorm.
Module strtod_c := U.Prog.strtod_c.
Import YM05.
Import ListNotations.
Local Open Scope Z_scope.

Lemma st_len3 : forall n cap kl, (length (set_trace n cap kl) <= 3)%nat.
Proof. intros n cap kl. unfold set_trace. destruct (n =? cap); cbn; lia. Qed.

Lemma fl_disj : forall (l1 l2 l3 : list (Z * Z)) b, List.NoDup (l1 ++ l2 ++ l3) -> In b l1 -> ~ In b l2.
Proof.
  intros l1 l2 l3 b H H1 H2. apply NoDup_ListNoDup in H.
  apply (pis_nodup_app_disj _ l1 (l2 ++ l3) b H H1). apply in_or_app. left. exact H2.
Qed.

Section FA.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Hypothesis HFREE : pj_free_contract B API F.

Local Notation getr := YK11.getr.

Lemma g_rplace_carry : forall Lx Ax Lamx regsx memx mdx S v r rk lo,
  aa_MR API Lx Ax memx mdx -> vplace Lx Ax Lamx S v r rk -> alloc_ceiling <= spZ regsx -> spZ regsx <= S ->
  (forall i, 0 <= i < 56 -> ~ static_owned B (v + i) /\ ~ alloc_statics (v + i) /\
     ~ (errno_addr B <= v + i < errno_addr B + 4) /\ ~ in_img B (v + i)) ->
  (S <= v -> v + 56 <= lo) -> (st_init_done Ax = false -> auxv_pre B (ly_sec Lx) lo memx) ->
  rplace B Lx Ax Lamx regsx memx v.
Proof.
  intros Lx Ax Lamx regsx memx mdx S v r rk lo HM HV Hc Hs Hv Hlo Hax.
  pose proof alloc_ceiling_value as Hcv.
  split; [exact (g_place_of Lx Ax Lamx S (spZ regsx) v r rk HV Hs)|].
  split.
  - intros Hsv Hd. apply (auxv_pre_mono B (ly_sec Lx) lo (v + 56) memx); [|exact (Hax Hd)].
    destruct HV as [[(HS & _ & _ & _)|(Hin & H1 & H2 & _)] _]; [exact (Hlo HS)|].
    pose proof (g_blk_range B API Lx Ax memx mdx r rk HM Hin). lia.
  - intros i Hi. destruct (Hv i Hi) as (V1 & V2 & V3 & V4).
    split; [|split; [exact V2 | split; [exact V3 | exact V4]]].
    apply (vloc_own B API Lx Ax Lamx memx mdx S v r rk (v + i) (proj1 HV) HM); [lia | lia | exact V1].
Qed.

Lemma fail_arm : forall L A regs mem md Lam peak cnt fail b o k w ms tv D Dw kids keys n cap kname (dd : nat) lo
    Lx Ax regs1 mem1 md1 Lam1 junk ro rko rw rkw (c : nat) Lr Do Dold Dnew Dr (d : nat),
  reader_env B API (PJ_SET_K dd) L A regs mem md ->
  rplace B L A Lam regs mem o -> rplace B L A Lam regs mem w ->
  (forall x, w <= x < w + 56 -> ~ pj_foot o D x) -> pj_apart Dw o ->
  Frame.disjoint_from [(o, o + 56); (w, w + 56); (k, k + Z.of_nat (length kname) + 1)]
    (spZ regs - PJ_SET_K dd) (PJ_SET_K dd) ->
  spZ regs <= lo -> (st_init_done A = false -> auxv_pre B (ly_sec L) lo mem) ->
  (forall x, pj_set_writes o w D Dw x -> x < lo) -> (spZ regs <= w -> w + 56 <= lo) ->
  ~ In (zb kname) (map fst ms) -> Permutation Lam (D ++ Dw ++ Lr) ->
  rpost B API (PJ_SET_K dd) L A regs mem md (pj_set_writes o w D Dw) (freed (D ++ Dw)) Lx Ax regs mem1 md1 ->
  ledger B Lx Ax mem1 Lam1 (Z.max peak (lsum Lam1)) (cnt + Z.of_nat c) (2 ^ 64 - 1) ->
  rf_ok F Ax (rf_run F b (firstn (c - 1)%nat (set_trace n cap (Z.of_nat (length kname))))) ->
  rd_cells B mem1 ->
  rw_cells (ms_segs B) mem1 (spZ regs - 48)
    [CB 8 junk; C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)] ->
  getr regs1 1 = Z_to_bv 64 PS_FREEW_RET -> getr regs1 2 = Z_to_bv 64 (spZ regs - 48) ->
  getr regs1 10 = Z_to_bv 64 w ->
  (forall r, r = 3 \/ r = 4 \/ 20 <= r <= 27 -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
  w <> 0 -> pj_fd (ms_segs B) mem1 (lin Lam1) dd w Dw ->
  vplace Lx Ax Lam1 (spZ regs) w rw rkw -> vplace Lx Ax Lam1 (spZ regs) o ro rko ->
  Permutation Lam1 (Do ++ Dw ++ Lr) ->
  pj_fd (ms_segs B) mem1 (lin Lam1) d o Do ->
  (Z.of_nat c = Z.of_nat (length (set_trace n cap (Z.of_nat (length kname)))) ->
     pj_node (ms_segs B) mem1 (lin Lam1) o (JObj ms) Do) ->
  pj_apart Do w ->
  cnt <= fail < cnt + Z.of_nat (length (set_trace n cap (Z.of_nat (length kname)))) ->
  Z.of_nat c = fail - cnt + 1 ->
  Z.of_nat (length Do) = Z.of_nat (length D) + nlive (firstn (c - 1)%nat (set_trace n cap (Z.of_nat (length kname)))) ->
  lsum Do = lsum D + held (firstn (c - 1)%nat (set_trace n cap (Z.of_nat (length kname)))) ->
  Permutation D (Dold ++ Dr) -> Permutation Do (Dnew ++ Dr) -> new_blks L A Dnew ->
  (c = 1%nat /\ Dold = [] /\ Dnew = [] \/
   n = cap /\ c = 2%nat /\ Dold = kids_blk kids cap /\ (exists k', Dnew = [(k', 56 * cap2 cap)]) \/
   n = cap /\ c = 3%nat /\ Dold = kids_blk kids cap ++ keys_blk 6 keys cap /\
     exists k' y', Dnew = [(k', 56 * cap2 cap); (y', 8 * cap2 cap)]) ->
  SR (ms_segs B) (mkCfg (YK11.mkst regs1 (Z_to_bv 64 PS_PJ_FREE) mem1 (YK11.seg_rom (ms_segs B))) md1)
    (set_post B API F dd L A regs mem md Lam peak cnt fail b o w ms tv D Dw kids keys n cap kname).
Proof.
  intros L A regs mem md Lam peak cnt fail b o k w ms tv D Dw kids keys n cap kname dd lo Lx Ax regs1 mem1 md1 Lam1
    junk ro rko rw rkw c Lr Do Dold Dnew Dr d HE HPo HPw HWD HAw HDJ Hlo Hax HElo Hlw Hnin HPL HR1 HL1 Hres1 Hrd1 FR
    G1 G2 G10 Gk Hw0 Hfd HVw HVo HPL1 Hfdo HNo HADo Hfc Hc Hlen Hsum HPD HPDo Hnew Hcase.
  pose proof HE as HE0.
  destruct HE as (HSEG & Htp & Herrno & Hgot & Hguard & Hpre & Hsp47 & Hglob & Hfrm & HRD).
  pose proof Hpre as (HMR & HWF & Hbd & Hra & Hsp16 & Hspc & Hsp63 & Hstk & Htpr & Herr & Haux).
  pose proof alloc_ceiling_value as Hceil.
  pose proof (t_sk dd) as (Kf & Kg & Ks & K96 & Kf0).
  unfold strtod_c.STRTOD_GLOBALS_TOP in Hglob.
  cbn [Frame.disjoint_from] in HDJ.
  pose proof HR1 as (HMR1 & _).
  assert (Hs1 : spZ regs1 = spZ regs - 48) by (unfold spZ at 1; rewrite G2, unsigned_lit by lia; reflexivity).
  assert (Herr4 : errno_addr B + 4 <= spZ regs - PJ_SET_K dd) by (rewrite Herrno; unfold strtod_c.STRTOD_ERRNO; lia).
  assert (HNDL1 : List.NoDup (map fst Lam1)).
  { pose proof HL1 as (_ & _ & _ & _ & HND & _). first [exact HND | apply NoDup_ListNoDup; exact HND]. }
  pose proof (Permutation_NoDup HPL1 (List.NoDup_map_inv _ _ HNDL1)) as HND3.
  assert (HDoL : forall a k0, In (a, k0) Do -> In (a, k0) Lam1).
  { intros a k0 Hb. apply (Permutation_in _ (Permutation_sym HPL1)). apply in_or_app. left. exact Hb. }
  assert (HDwL : forall a k0, In (a, k0) Dw -> In (a, k0) Lam1).
  { intros a k0 Hb. apply (Permutation_in _ (Permutation_sym HPL1)). apply in_or_app. right. apply in_or_app.
    left. exact Hb. }
  assert (HDoDw : forall bk, In bk Do -> ~ In bk Dw) by (intros bk Hb; exact (fl_disj Do Dw Lr bk HND3 Hb)).
  assert (Hax1 : st_init_done Ax = false -> auxv_pre B (ly_sec Lx) lo mem1).
  { apply (g_aux_rp B API (PJ_SET_K dd) L A regs mem md _ _ Lx Ax regs mem1 md1 lo lo HR1); first [lia | assumption]. }
  assert (Hpl : rplace B Lx Ax Lam1 regs1 mem1 w).
  { apply (g_rplace_carry Lx Ax Lam1 regs1 mem1 md1 (spZ regs) w rw rkw lo HMR1 HVw ltac:(lia) ltac:(lia));
      [|exact Hlw | exact Hax1].
    intros i Hi. pose proof HPw as (_ & _ & Hw3). destruct (Hw3 i Hi) as (W1 & W2 & W3 & W4).
    split; [intros Hs; exact (W1 (or_intror Hs))|]. split; [exact W2|]. split; [exact W3 | exact W4]. }
  assert (HD : Frame.disjoint_from [(w, w + 56)] (spZ regs - PJ_SET_K dd) (PJ_SET_K dd))
    by (cbn [Frame.disjoint_from]; lia).
  assert (HWE : forall x, pj_free_writes w Dw x -> pj_set_writes o w D Dw x).
  { intros x (_ & [Hx|[(a & k0 & Hb & Hx)|Hx]]).
    - right; left; exact Hx.
    - right; right; left. exists a, k0. split; [apply in_or_app; right; exact Hb | exact Hx].
    - right; right; right; exact Hx. }
  assert (HWG : forall a n0, freed Dw a n0 -> freed (D ++ Dw) a n0)
    by (intros a n0 Hf; apply in_or_app; right; exact Hf).
  assert (HGE : forall p n0 i0, In (p, n0) (user_blocks A) -> 0 <= i0 < n0 -> freed (D ++ Dw) (ptr_addr L p) n0 ->
      pj_set_writes o w D Dw (ptr_addr L p + i0))
    by (intros p n0 i0 _ Hi0 Hf; exact (st_gone _ _ _ o w D Dw Hi0 Hf)).
  change (Z_to_bv 64 PS_PJ_FREE) with (Z_to_bv 64 PJ_FREE).
  apply (tail_w B API F HFREE L A regs mem md dd _ _ Lx Ax mem1 md1 regs1 Lam1 (Z.max peak (lsum Lam1))
    (cnt + Z.of_nat c) (2 ^ 64 - 1) _ w Dw junk lo _ HE0 HR1 Hlo Hax HElo HGE G1 G2 G10 Gk FR HL1 Hres1 Hrd1 Hw0 Hfd
    Hpl HDwL HD HWE HWG).
  intros L' A' regs' mem' md' Lam' regs2 HR2e HR2 Hrd2 G2' HL2 HRF HP2 Hz2.
  assert (HLL : forall a k0, In (a, k0) Do -> lin Lam' a k0).
  { intros a k0 Hb. unfold lin. pose proof (Permutation_in _ HP2 (HDoL a k0 Hb)) as H1.
    apply in_app_or in H1. destruct H1 as [H1|H1]; [exact (False_ind _ (HDoDw _ Hb H1)) | exact H1]. }
  pose proof HPo as (_ & _ & Ho3).
  assert (HS : forall x, pj_foot o Do x -> pis_same (ms_segs B) mem1 mem' x).
  { intros x [Hx|((a & k0) & Hb & Hx)].
    - destruct (Ho3 (x - o) ltac:(lia)) as (O1 & O2 & O3 & O4).
      replace (o + (x - o)) with x in O1, O2, O3, O4 by lia.
      apply (vloc_same B API Lx Ax Lam1 (spZ regs) o ro rko (PJ_FREE_K dd) regs1 mem1 md1 (pj_free_writes w Dw)
        (freed Dw) L' A' regs2 mem' md' x (proj1 HVo) HR2); [| lia | lia | exact O3 | exact Hx |].
      + exact (g_vloc_nf B API Lx Ax Lam1 mem1 md1 _ _ _ (spZ regs) o ro rko Dw (proj1 HVo) HMR1 HL1 ltac:(lia)
          HAw HDwL).
      + intros (_ & [Hw|[Hbs|Hs]]).
        * exact (HWD x Hw (or_introl Hx)).
        * exact (g_vloc_nblk B API Lx Ax Lam1 mem1 md1 _ _ _ (spZ regs) o ro rko Dw (proj1 HVo) HMR1 HL1 ltac:(lia)
            HAw HDwL x Hx Hbs).
        * exact (O2 Hs).
    - unfold pj_holds in Hx; cbn [fst snd] in Hx.
      pose proof (HDoL a k0 Hb) as HinL.
      pose proof HL1 as (_ & _ & _ & _ & _ & HF). rewrite Forall_forall in HF.
      destruct (HF _ HinL) as (_ & Hblk & _). cbn [fst snd] in Hblk.
      apply (rp_same_blk B API _ _ _ _ _ _ _ _ _ _ _ _ _ (a - 16) (k0 + 16) x HR2 Hblk); [| lia |].
      + unfold freed. replace (a - 16 + 16) with a by lia. replace (k0 + 16 - 16) with k0 by lia.
        exact (HDoDw _ Hb).
      + intros (_ & [Hw|[(a' & k' & Hin' & Hx')|Hs]]).
        * exact (HADo (a, k0) x Hb ltac:(unfold pj_holds; cbn [fst snd]; lia) Hw).
        * assert (Hne : (a, k0) <> (a', k')) by (intros E; rewrite E in Hb; exact (HDoDw _ Hb Hin')).
          destruct (g_lam_disj B API Lx Ax mem1 md1 Lam1 _ _ _ a k0 a' k' HMR1 HL1 HinL (HDwL a' k' Hin') Hne); lia.
        * apply (ledger_block_not_img B Lx Ax mem1 Lam1 _ _ _ a k0 (x - a) HL1 HinL ltac:(lia)).
          replace (a + (x - a)) with x by lia. exact (g_img_consts B HSEG Herrno x (or_introl Hs)). }
  assert (Hl3 : Z.of_nat (length (set_trace n cap (Z.of_nat (length kname)))) <= 3)
    by (pose proof (st_len3 n cap (Z.of_nat (length kname))); lia).
  unfold set_post.
  exists L', A', regs', mem', md', Lam', (Z.max peak (lsum Lam1)), (2 ^ 64 - 1), (-1), c, Lr, Do.
  split; [reflexivity|]. split; [exact HR2e|]. split; [exact Hrd2|]. split; [exact G2'|]. split; [exact HL2|].
  split; [unfold fail_after; split; intros; lia|].
  split; [exact HPL|].
  split.
  { apply (Permutation_app_inv_l Dw). apply (Permutation_trans (Permutation_sym HP2)).
    apply (Permutation_trans HPL1). rewrite !app_assoc. apply Permutation_app_tail. apply Permutation_app_comm. }
  split; [exact Hz2|].
  split; [intros H; lia|].
  right; right.
  split; [exact Hnin|]. split; [exact Hfc|]. split; [exact Hc|]. split; [reflexivity|].
  split; [rewrite (g_lsum_perm _ _ HP2), g_lsum_app; f_equal; lia|].
  split; [exact HRF|]. split; [exact Hlen|]. split; [exact Hsum|].
  split; [exists Dold, Dnew, Dr; split; [exact HPD|]; split; [exact HPDo|]; split; [exact Hnew | exact Hcase]|].
  split.
  { exists d. apply (pis_fd_frame (ms_segs B) d mem1 (lin Lam1) mem' (lin Lam') o Do Hfdo); [|exact HS].
    intros a k0 Hb _. exact (HLL a k0 Hb). }
  intros Hcl. apply (pis_node_frame (ms_segs B) (JObj ms) mem1 (lin Lam1) mem' (lin Lam') o Do (HNo Hcl) HLL HS).
Qed.

End FA.
