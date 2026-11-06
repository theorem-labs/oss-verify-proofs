From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YL01 YO0x YO0u.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Contract Img0 KindBGlue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require MemNorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import Ledger PjStruct ReaderRes parse_items_shape.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import pj_set_runs pj_set_shape pj_set_kb.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import pj_free_c fuzz_strdup_c memcpy_c memset_c pj_set_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import pj_set_tail pj_set_post pj_set_fail.
Import YM05.
Import ListNotations.
Local Open Scope Z_scope.

Definition hid (P : Prop) : Prop := P.

Section OK.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Hypothesis HFREE : pj_free_contract B API F.
Hypothesis HSD : fuzz_strdup_contract B API F.
Hypothesis AX : YL01.AllocExtra B (aa_MR API).
Hypothesis HMC : memcpy_contract.
Hypothesis HMS : memset_contract.

Local Notation getr := YK11.getr.

Lemma cp_same_blk : forall K1 L1 A1 regs1 mem1 md1 E1 L2 A2 regs2 mem2 md2 a k x,
  call_post_k B (aa_MR API) K1 L1 A1 regs1 mem1 md1 E1 L2 A2 regs2 mem2 md2 ->
  keeps B L1 A1 mem1 mem2 0 -> ublocks_kept L1 A1 A2 (0, 0) -> In (a, k) (blocks L1 A1) -> a <> 0 ->
  a <= x < a + k -> pis_same (ms_segs B) mem1 mem2 x.
Proof.
  intros K1 L1 A1 regs1 mem1 md1 E1 L2 A2 regs2 mem2 md2 a k x HP HK Hub Hin Ha0 Hx. split.
  - pose proof (HK a k (x - a) Hin Ha0 ltac:(lia)) as E. replace (a + (x - a)) with x in E by lia. exact E.
  - intros _.
    assert (Hne : (a, k) <> (0, 0)) by (intros E; injection E; lia).
    pose proof (g_kept_blk B API K1 L1 A1 regs1 mem1 md1 E1 L2 A2 regs2 mem2 md2 (0, 0) a k HP Hub Hin Hne) as Hin2.
    destruct (g_blocks_user L2 A2 a k Hin2) as (q & Hq & Eq). pose proof HP as (HM2 & _).
    destruct (mr_blocks _ _ (aa_laws API) _ _ _ _ q k (x - a) HM2 Hq ltac:(lia)) as (P & _).
    rewrite Eq in P. replace (a + (x - a)) with x in P by lia. exact (present_writable B mem2 x P).
Qed.

Lemma g_newblk : forall K L A regs mem md E G Lx Ax regsx memx mdx a kk x,
  rpost B API K L A regs mem md E G Lx Ax regsx memx mdx -> In (a, kk) (blocks Lx Ax) -> ~ In (a, kk) (blocks L A) ->
  a <= x < a + kk -> forall p n, In (p, n) (user_blocks A) -> In (p, n) (user_blocks Ax) ->
  ~ (ptr_addr L p <= x < ptr_addr L p + n).
Proof.
  intros K L A regs mem md E G Lx Ax regsx memx mdx a kk x HR Hin Hn Hx p n Hp Hp' Hx'.
  pose proof HR as (HM & _ & _ & _ & _ & _ & _ & _ & H9 & _).
  pose proof (g_user_blocks Lx Ax p n Hp') as Hb. rewrite (H9 p n Hp Hp') in Hb.
  destruct (Z.eq_dec (ptr_addr L p) a) as [Ea|Ea]; [destruct (Z.eq_dec n kk) as [Ek|Ek]|].
  - apply Hn. rewrite <- Ea, <- Ek. exact (g_user_blocks L A p n Hp).
  - assert (Hne : (ptr_addr L p, n) <> (a, kk)) by (intros E0; injection E0; lia).
    destruct (g_disj B API Lx Ax memx mdx _ _ _ _ HM Hb Hin Hne); lia.
  - assert (Hne : (ptr_addr L p, n) <> (a, kk)) by (intros E0; injection E0; lia).
    destruct (g_disj B API Lx Ax memx mdx _ _ _ _ HM Hb Hin Hne); lia.
Qed.

Lemma g_body_w : forall K L A regs mem md (E : Z -> Prop) G Lx Ax regsx memx mdx Lamx peak cnt fail a kk y,
  rpost B API K L A regs mem md E G Lx Ax regsx memx mdx -> ledger B Lx Ax memx Lamx peak cnt fail ->
  In (a, kk) Lamx -> ((forall z, a - 16 <= z < a + kk -> E z) \/ ~ In (a - 16, kk + 16) (blocks L A)) ->
  a <= y < a + kk ->
  ~ owned B Lx Ax y /\ (E y \/ (y < alloc_ceiling /\ ~ in_img B y /\
    forall p n, In (p, n) (user_blocks A) -> In (p, n) (user_blocks Ax) -> ~ (ptr_addr L p <= y < ptr_addr L p + n))).
Proof.
  intros K L A regs mem md E G Lx Ax regsx memx mdx Lamx peak cnt fail a kk y HR HL Hin Hor Hy.
  pose proof HR as (HM & _).
  pose proof HL as (_ & _ & _ & _ & _ & HF). rewrite Forall_forall in HF.
  destruct (HF _ Hin) as (Hk & Hb & _). cbn [fst snd] in Hk, Hb.
  destruct (ledger_block_range B API Lx Ax memx mdx Lamx peak cnt fail a kk HM HL Hin) as (R1 & R2 & _).
  split.
  - destruct (g_blocks_user Lx Ax _ _ Hb) as (q & Hq & Eq).
    destruct (mr_blocks _ _ (aa_laws API) _ _ _ _ q (kk + 16) (y - (a - 16)) HM Hq ltac:(lia)) as (_ & _ & _ & Hno).
    rewrite Eq in Hno. replace (a - 16 + (y - (a - 16))) with y in Hno by lia. exact Hno.
  - destruct Hor as [HE|Hn]; [left; apply HE; lia|]. right.
    split; [lia|]. split.
    + replace y with (a + (y - a)) by lia. apply (ledger_block_not_img B Lx Ax memx Lamx peak cnt fail a kk (y - a) HL Hin).
      lia.
    + exact (g_newblk K L A regs mem md E G Lx Ax regsx memx mdx (a - 16) (kk + 16) y HR Hb Hn ltac:(lia)).
Qed.

Lemma g_fresh1 : forall L1 A1 L2 A2 mem2 md2 b1 b2 x,
  aa_MR API L2 A2 mem2 md2 -> blocks L2 A2 = b1 ++ x :: b2 -> blocks L1 A1 = b1 ++ b2 -> 0 < snd x ->
  ~ In x (blocks L1 A1) /\ In x (blocks L2 A2).
Proof.
  intros L1 A1 L2 A2 mem2 md2 b1 b2 x HM E2 E1 Hx.
  pose proof (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ HM) as PW. fold (blocks L2 A2) in PW. rewrite E2 in PW.
  split; [|rewrite E2; apply in_or_app; right; left; reflexivity].
  intros Hin. rewrite E1 in Hin. pose proof (g_pw_dup b1 b2 x PW Hin). lia.
Qed.

Lemma vloc_ne0 : forall L A Lam mem md S v r rk, vloc L A Lam S v r rk -> aa_MR API L A mem md -> (r, rk) <> (0, 0).
Proof.
  intros L A Lam mem md S v r rk [(_ & _ & _ & Hr)|(Hin & _)] HM E; injection E as E1 E2; [lia|].
  subst. pose proof (g_blk_range B API L A mem md 0 0 HM Hin). lia.
Qed.

Lemma g_nout4 : forall a1 b1 a2 b2 a3 b3 a4 b4 x,
  ~ Frame.outside [(a1, b1); (a2, b2); (a3, b3); (a4, b4)] x ->
  a1 <= x < b1 \/ a2 <= x < b2 \/ a3 <= x < b3 \/ a4 <= x < b4.
Proof.
  intros a1 b1 a2 b2 a3 b3 a4 b4 x H.
  destruct (Z_le_gt_dec a1 x), (Z_lt_ge_dec x b1); try (left; lia);
  destruct (Z_le_gt_dec a2 x), (Z_lt_ge_dec x b2); try (right; left; lia);
  destruct (Z_le_gt_dec a3 x), (Z_lt_ge_dec x b3); try (right; right; left; lia);
  destruct (Z_le_gt_dec a4 x), (Z_lt_ge_dec x b4); try (right; right; right; lia);
  exfalso; apply H; cbn; refine (conj _ (conj _ (conj _ (conj _ I)))); lia.
Qed.

Lemma ok_arm : forall L A regs mem md Lam peak cnt fail b o k w ms tv D Dw num kids keys n cap kname slack
    (dd : nat) lo Lg Ag regsg memg mdg Lamg junk (g : nat) kg yg capg Di Lr Dold Dnew Dr ro rko rw rkw,
  reader_env B API (PJ_SET_K dd) L A regs mem md ->
  rplace B L A Lam regs mem o -> w <> 0 -> rplace B L A Lam regs mem w ->
  (forall x, w <= x < w + 56 -> ~ pj_foot o D x) -> pj_apart Dw o ->
  (depth tv <= dd)%nat -> ~ In (Z_to_bv 8 0) kname ->
  (- (k + Z.of_nat (length kname) + 1)) mod 8 <= Z.of_nat (length slack) ->
  cstr_ok B Lam k (Z.of_nat (length kname) + 1) ->
  (forall x, k <= x < k + Z.of_nat (length kname) + 1 -> ~ pj_foot o D x /\ ~ pj_foot w Dw x) ->
  Frame.disjoint_from [(o, o + 56); (w, w + 56); (k, k + Z.of_nat (length kname) + 1)]
    (spZ regs - PJ_SET_K dd) (PJ_SET_K dd) ->
  cnt + 3 < 2 ^ 64 - 1 ->
  spZ regs <= lo -> (st_init_done A = false -> auxv_pre B (ly_sec L) lo mem) ->
  (forall x, pj_set_writes o w D Dw x -> x < lo) -> (spZ regs <= w -> w + 56 <= lo) ->
  (forall nm u, In (nm, u) ms -> nm <> zb kname) ->
  Permutation Lam (D ++ Dw ++ Lr) -> (forall bk, In bk Dw -> ~ In bk D) ->
  rpost B API (PJ_SET_K dd) L A regs mem md (pj_set_writes o w D Dw) (freed (D ++ Dw)) Lg Ag regs memg mdg ->
  ledger B Lg Ag memg Lamg (Z.max peak (lsum Lamg)) (cnt + Z.of_nat g) fail ->
  ~ (cnt <= fail < cnt + Z.of_nat g) ->
  rf_ok F Ag (rf_run F b (firstn g (set_trace n cap (Z.of_nat (length kname))))) ->
  rd_cells B memg ->
  rw_cells (ms_segs B) memg (spZ regs - 48)
    [CB 8 junk; C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)] ->
  getr regsg 1 = Z_to_bv 64 PS_SD_RET -> getr regsg 2 = Z_to_bv 64 (spZ regs - 48) ->
  getr regsg 10 = Z_to_bv 64 k -> getr regsg 8 = Z_to_bv 64 w -> getr regsg 9 = Z_to_bv 64 o ->
  (forall r, r = 3 \/ r = 4 \/ 20 <= r <= 27 -> getr regsg (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
  Mem.bytes_at (ms_segs B) memg k (kname ++ Z_to_bv 8 0 :: slack) ->
  pj_node (ms_segs B) memg (lin Lamg) w tv Dw ->
  vplace Lg Ag Lamg (spZ regs) w rw rkw -> vplace Lg Ag Lamg (spZ regs) o ro rko ->
  pis_open (ms_segs B) memg (lin Lamg) o true num kg yg capg n (map snd ms) (map fst ms) Di ->
  n = Z.of_nat (length ms) -> n < capg ->
  Permutation Lamg (Dnew ++ Dr ++ Dw ++ Lr) -> Dnew ++ Dr = pis_slots true kg yg capg ++ Di ->
  Permutation D (Dold ++ Dr) -> new_blks L A Dnew ->
  (forall a kk, In (a, kk) (pis_slots true kg yg capg) ->
     (forall z, a - 16 <= z < a + kk -> pj_set_writes o w D Dw z) \/ ~ In (a - 16, kk + 16) (blocks L A)) ->
  pj_apart (pis_slots true kg yg capg ++ Di) w ->
  (n < cap /\ g = 0%nat /\ Dold = [] /\ Dnew = [] \/
   n = cap /\ g = 2%nat /\ Dold = kids_blk kids cap ++ keys_blk 6 keys cap /\
     exists k' y', Dnew = [(k', 56 * cap2 cap); (y', 8 * cap2 cap)]) ->
  Z.of_nat (length (Dnew ++ Dr)) =
    Z.of_nat (length D) + nlive (firstn g (set_trace n cap (Z.of_nat (length kname)))) ->
  lsum (Dnew ++ Dr) = lsum D + held (firstn g (set_trace n cap (Z.of_nat (length kname)))) ->
  length (set_trace n cap (Z.of_nat (length kname))) = S g ->
  rf_run F b (set_trace n cap (Z.of_nat (length kname))) =
    rf_malloc F (rf_run F b (firstn g (set_trace n cap (Z.of_nat (length kname))))) (Z.of_nat (length kname) + 17) ->
  nlive (set_trace n cap (Z.of_nat (length kname))) =
    nlive (firstn g (set_trace n cap (Z.of_nat (length kname)))) + 1 ->
  held (set_trace n cap (Z.of_nat (length kname))) =
    held (firstn g (set_trace n cap (Z.of_nat (length kname)))) + Z.of_nat (length kname) + 1 ->
  rf_room F (rf_run F b (firstn g (set_trace n cap (Z.of_nat (length kname))))) (Z.of_nat (length kname) + 17) ->
  Z.of_nat (length kname) + 17 <= 2 ^ 28 ->
  SR (ms_segs B) (mkCfg (YK11.mkst regsg (Z_to_bv 64 PS_STRDUP) memg (YK11.seg_rom (ms_segs B))) mdg)
    (set_post B API F dd L A regs mem md Lam peak cnt fail b o w ms tv D Dw kids keys n cap kname).
Proof.
  intros L A regs mem md Lam peak cnt fail b o k w ms tv D Dw num kids keys n cap kname slack dd lo Lg Ag regsg memg
    mdg Lamg junk g kg yg capg Di Lr Dold Dnew Dr ro rko rw rkw HE HPo Hw0 HPw HWD HAw Hdt Hkn Hsl Hcs HKD HDJ Hcnt
    Hlo Hax HElo Hlw Hnin HPL HDD HRg HLg Hfg Hresg Hrdg FRg G1g G2g G10g G8g G9g Gkg HKg HNwg HVwg HVog HOg En Hncap
    HPLg HDg HPD Hnew HSE HAPw Hcase Hlenh Hsumh Hltr Hrun Hnl Hhd Hroomg Hsz.
  pose proof HE as HE0. pose proof HDJ as HDJ0.
  destruct HE as (HSEG & Htp & Herrno & Hgot & Hguard & Hpre & Hsp47 & Hglob & Hfrm & HRD).
  pose proof Hpre as (HMR & HWF & Hbd & Hra & Hsp16 & Hspc & Hsp63 & Hstk & Htpr & Herr & Haux).
  pose proof alloc_ceiling_value as Hceil.
  pose proof (t_sk dd) as (Kf & Kg & Ks & K96 & Kf0).
  assert (HK1 : 48 + (ALLOC_STACK + 64) <= PJ_SET_K dd) by (unfold STRDUP_K in Ks; lia).
  unfold strtod_c.STRTOD_GLOBALS_TOP in Hglob.
  clear HDJ. pose proof (Hcase : hid _) as HcaseH. clear Hcase. pose proof (Hfg : hid _) as HfgH. clear Hfg.
  pose proof (g_img B HSEG) as HIL.
  pose proof HRg as (HMRg & HWFg & _).
  assert (HSP : bv_unsigned (getr regs 2) = spZ regs) by reflexivity.
  assert (Hsg : spZ regsg = spZ regs - 48) by (unfold spZ at 1; rewrite G2g, unsigned_lit by lia; reflexivity).
  assert (Herr4 : errno_addr B + 4 <= spZ regs - PJ_SET_K dd) by (rewrite Herrno; unfold strtod_c.STRTOD_ERRNO; lia).
  pose proof HOg as (HNDg & HAPg & HHg & HSLg & _ & _).
  pose proof HHg as ((Ho8 & HoS) & _ & _ & _ & (Hkg64 & BKg) & (Hyg64 & BYg) & (Hnn64 & BNg) & _).
  pose proof HoS as (Ho0 & Ho1 & HoSt).
  destruct HSLg as (_ & (Hn1 & Hc54) & _ & Hcpg).
  assert (Hcp0 : 0 < capg) by lia.
  destruct (Hcpg Hcp0) as (Hkgl & Hygl'). pose proof (Hygl' eq_refl) as Hygl. unfold lin in Hkgl, Hygl.
  assert (ES : pis_slots true kg yg capg = [(kg, 56 * capg); (yg, 8 * capg)]).
  { rewrite ps_slots_eq. rewrite (proj2 (Z.eqb_neq capg 0)) by lia. reflexivity. }
  assert (Hks : In (kg, 56 * capg) (pis_slots true kg yg capg ++ Di)) by (rewrite ES; left; reflexivity).
  assert (Hys : In (yg, 8 * capg) (pis_slots true kg yg capg ++ Di)) by (rewrite ES; right; left; reflexivity).
  assert (Hks0 : In (kg, 56 * capg) (pis_slots true kg yg capg)) by (rewrite ES; left; reflexivity).
  assert (Hys0 : In (yg, 8 * capg) (pis_slots true kg yg capg)) by (rewrite ES; right; left; reflexivity).
  destruct (ledger_block_range B API Lg Ag memg mdg Lamg _ _ _ kg (56 * capg) HMRg HLg Hkgl) as (Kg1 & Kg2 & _).
  destruct (ledger_block_range B API Lg Ag memg mdg Lamg _ _ _ yg (8 * capg) HMRg HLg Hygl) as (Yg1 & Yg2 & _).
  pose proof (ledger_block_aligned B API Lg Ag memg mdg Lamg _ _ _ kg (56 * capg) HMRg HLg Hkgl : hid _) as Hkg16.
  assert (Hneky : (kg, 56 * capg) <> (yg, 8 * capg)) by (intros E0; injection E0; lia).
  pose proof (pis_node_rw (ms_segs B) memg (lin Lamg) w tv Dw HNwg) as (Hw8 & HwS).
  pose proof HwS as (Hw0' & Hw1' & HwSt).
  pose proof (pis_node_apart (ms_segs B) memg (lin Lamg) w tv Dw HNwg) as HADw.
  assert (HDwLg : forall a k0, In (a, k0) Dw -> In (a, k0) Lamg)
    by (intros a k0 Hb; exact (pis_node_lblk (ms_segs B) tv memg (lin Lamg) w Dw HNwg (a, k0) Hb)).
  assert (HSLL : forall a k0, In (a, k0) (pis_slots true kg yg capg ++ Di) -> In (a, k0) Lamg)
    by (intros a k0 Hb; exact (pis_open_lblk (ms_segs B) memg (lin Lamg) o true num kg yg capg n _ _ Di HOg a k0 Hb)).
  assert (HNDLg : List.NoDup (map fst Lamg)).
  { pose proof HLg as (_ & _ & _ & _ & HND & _). first [exact HND | apply NoDup_ListNoDup; exact HND]. }
  assert (HND4 : List.NoDup ((pis_slots true kg yg capg ++ Di) ++ Dw ++ Lr)).
  { rewrite <- HDg, <- app_assoc. exact (Permutation_NoDup HPLg (List.NoDup_map_inv _ _ HNDLg)). }
  assert (HDwS : forall bk, In bk Dw -> ~ In bk (pis_slots true kg yg capg ++ Di)).
  { intros bk Hb Hs. exact (fl_disj _ Dw Lr bk HND4 Hs Hb). }
  pose proof HPo as (_ & _ & Ho3). pose proof HPw as (_ & _ & Hw3).
  assert (Hnin' : ~ In (zb kname) (map fst ms)).
  { intros H. apply in_map_iff in H as ((nm & u) & E0 & Hin). cbn [fst] in E0. exact (Hnin nm u Hin E0). }
  assert (HSUB : forall a kk, In (a, kk) (pis_slots true kg yg capg ++ Di) -> forall x, a <= x < a + kk ->
      ~ (w <= x < w + 56) /\ ~ (o <= x < o + 56)).
  { intros a kk Hb x Hx. split; [exact (HAPw (a, kk) x Hb ltac:(unfold pj_holds; cbn [fst snd]; lia)) |].
    exact (HAPg (a, kk) x Hb ltac:(unfold pj_holds; cbn [fst snd]; lia)). }
  assert (Hpreg : call_pre_k B (aa_MR API) (ALLOC_STACK + 64) Lg Ag regsg memg mdg).
  { apply (g_pre_k B API (PJ_SET_K dd) L A regs mem md _ _ Lg Ag memg mdg regsg (ALLOC_STACK + 64) lo Hpre HRg).
    - rewrite G1g. unfold YK0s.ret_ok. apply bv_eq. vm_compute. reflexivity.
    - rewrite Hsg. replace (spZ regs - 48) with (spZ regs + (-3) * 16) by lia. rewrite Z_mod_plus_full. exact Hsp16.
    - lia.
    - lia.
    - unfold ALLOC_STACK. lia.
    - exact (Gkg 4 ltac:(lia)).
    - lia.
    - exact Hlo.
    - exact Hax.
    - exact HElo. }
  clear Hsp16.
  assert (Hkb : forall a, k <= a < k + Z.of_nat (length kname) + 1 ->
      bv_unsigned (getr regsg 2) <= a \/ Mem.ro_addr (ms_segs B) (Z_to_bv 64 a) = true \/
      exists p kk, In (p, kk) (blocks Lg Ag) /\ p <= a < p + kk).
  { intros a Ha. destruct Hcs as [Hro|(a0 & kk & Hl & H1 & H2)]; [right; left; replace a with (k + (a - k)) by lia;
      apply Hro; lia|].
    right; right. unfold lin in Hl.
    assert (HnD : ~ In (a0, kk) D).
    { intros Hb. apply (proj1 (HKD k ltac:(lia))). right. exists (a0, kk). split; [exact Hb | unfold pj_holds; cbn; lia]. }
    assert (HnDw : ~ In (a0, kk) Dw).
    { intros Hb. apply (proj2 (HKD k ltac:(lia))). right. exists (a0, kk). split; [exact Hb | unfold pj_holds; cbn; lia]. }
    assert (HinG : In (a0, kk) Lamg).
    { pose proof (Permutation_in _ HPL Hl) as H3. apply in_app_or in H3. destruct H3 as [H3|H3]; [exact (False_ind _ (HnD H3))|].
      apply in_app_or in H3. destruct H3 as [H3|H3]; [exact (False_ind _ (HnDw H3))|].
      apply (Permutation_in _ (Permutation_sym HPLg)). apply in_or_app. right. apply in_or_app. right. apply in_or_app.
      right. exact H3. }
    pose proof HLg as (_ & _ & _ & _ & _ & HF). rewrite Forall_forall in HF.
    destruct (HF _ HinG) as (_ & Hb & _). cbn [fst snd] in Hb.
    exists (a0 - 16), (kk + 16). split; [exact Hb | lia]. }
  assert (Hkst : forall a, k <= a < k + Z.of_nat (length kname) + 1 ->
      ~ (bv_unsigned (getr regsg 2) - (ALLOC_STACK + 64) <= a < bv_unsigned (getr regsg 2))).
  { intros a Ha. change (bv_unsigned (getr regsg 2)) with (spZ regsg). rewrite Hsg.
    pose proof HDJ0 as HDJ. cbn [Frame.disjoint_from] in HDJ. lia. }
  eapply SR_bind; [apply (HSD Lg Ag regsg memg mdg k kname slack _ Lamg _ _ fail Hpreg G10g HKg Hkn Hsl Hkst Hkb HLg
    (proj1 Hrdg) Hresg Hroomg ltac:(lia)) |].
  intros cc3 HC3. clear Hsl.
  destruct HC3 as (L3 & A3 & regs3 & m3 & md3 & res & -> & Hro3 & _ & Hin3 & Hav3 & Hpost3 & Hlen3 & G310 & Hkeep3 &
    Hub3 & ARM3).
  pose proof Hpost3 as (HMR3 & HWF3 & Hbd3 & Hle3 & Hptr3 & Hp3 & (vm3 & Emd3) & Hfr3 & Hblk3 & Hscr3).
  assert (Hresr : res = 0 \/ (4112 <= res /\ res + Z.of_nat (length kname) + 1 <= alloc_ceiling /\
      (forall i, 0 <= i < Z.of_nat (length kname) + 1 + 16 -> ~ in_img B (res - 16 + i)))).
  { destruct ARM3 as [(_ & Hr0 & _)|(_ & _ & _ & _ & _ & Himg & _ & _ & _ & HL3)]; [left; exact Hr0|].
    right. pose proof (ledger_block_range B API L3 A3 m3 md3 _ _ _ _ res (Z.of_nat (length kname) + 1) HMR3 HL3
      (in_eq _ _)) as (R1 & R2 & _).
    split; [lia|]. split; [lia | exact Himg]. }
  pose proof (ARM3 : hid _) as ARM3H. clear ARM3.
  assert (HE1 : forall a, strdup_writes res a -> a < alloc_ceiling /\ (in_img B a -> pj_set_writes o w D Dw a)).
  { intros a [Ha|(Hr0 & Ha)].
    - split; [unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Ha; lia|]. intros _. right; right; right; exact Ha.
    - destruct Hresr as [Hr00|(R1 & R2 & Ri)]; [lia|]. split; [lia|]. intros Hi. exfalso.
      apply (Ri (a - res + 16)); [lia|]. replace (res - 16 + (a - res + 16)) with a by lia. exact Hi. }
  assert (HGE : forall p n0 i0, In (p, n0) (user_blocks A) -> 0 <= i0 < n0 -> freed (D ++ Dw) (ptr_addr L p) n0 ->
      pj_set_writes o w D Dw (ptr_addr L p + i0))
    by (intros p n0 i0 _ Hi0 Hf; exact (st_gone _ _ _ o w D Dw Hi0 Hf)).
  assert (HR3 : rpost B API (PJ_SET_K dd) L A regs mem md (pj_set_writes o w D Dw) (freed (D ++ Dw)) L3 A3 regs m3 md3).
  { apply (rp_call B API HIL (PJ_SET_K dd) L A regs mem md _ _ Lg Ag memg mdg (ALLOC_STACK + 64) regsg _ (0, 0)
      L3 A3 regs3 m3 md3 HMR HWF ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HRg Hpost3 Hin3 Hav3 Hlen3 Hub3 HE1).
    - intros p n0 Hp Heq. destruct (mr_blocks_range _ _ (aa_laws API) _ _ _ _ p n0 HMR Hp) as (P1 & P2).
      injection Heq as E1 E2. lia.
    - exact HGE. }
  assert (HE1c : forall a, strdup_writes res a -> a < alloc_ceiling) by (intros a Ha; exact (proj1 (HE1 a Ha))).
  pose proof (vloc_ne0 Lg Ag Lamg memg mdg (spZ regs) o ro rko (proj1 HVog) HMRg) as Hne0o.
  pose proof (vloc_ne0 Lg Ag Lamg memg mdg (spZ regs) w rw rkw (proj1 HVwg) HMRg) as Hne0w.
  assert (HOS : forall x, o <= x < o + 56 -> pis_same (ms_segs B) memg m3 x).
  { intros x Hx. destruct (Ho3 (x - o) ltac:(lia)) as (_ & _ & O3 & _). replace (o + (x - o)) with x in O3 by lia.
    exact (vloc_bytes B API Lg Ag Lamg (spZ regs) o ro rko (ALLOC_STACK + 64) regsg memg mdg (strdup_writes res) L3 A3
      regs3 m3 md3 (0, 0) x (proj1 HVog) HMRg Hpost3 Hub3 Hne0o ltac:(lia) ltac:(lia) HE1c O3 Hx). }
  assert (HWS : forall x, w <= x < w + 56 -> pis_same (ms_segs B) memg m3 x).
  { intros x Hx. destruct (Hw3 (x - w) ltac:(lia)) as (_ & _ & W3 & _). replace (w + (x - w)) with x in W3 by lia.
    exact (vloc_bytes B API Lg Ag Lamg (spZ regs) w rw rkw (ALLOC_STACK + 64) regsg memg mdg (strdup_writes res) L3 A3
      regs3 m3 md3 (0, 0) x (proj1 HVwg) HMRg Hpost3 Hub3 Hne0w ltac:(lia) ltac:(lia) HE1c W3 Hx). }
  assert (HBS : forall a kk x, In (a, kk) Lamg -> a <= x < a + kk -> pis_same (ms_segs B) memg m3 x).
  { intros a kk x Hin Hx. pose proof HLg as (_ & _ & _ & _ & _ & HF). rewrite Forall_forall in HF.
    destruct (HF _ Hin) as (_ & Hb & _). cbn [fst snd] in Hb.
    destruct (ledger_block_range B API Lg Ag memg mdg Lamg _ _ _ a kk HMRg HLg Hin) as (R1 & R2 & _).
    exact (cp_same_blk (ALLOC_STACK + 64) Lg Ag regsg memg mdg (strdup_writes res) L3 A3 regs3 m3 md3 (a - 16) (kk + 16)
      x Hpost3 Hkeep3 Hub3 Hb ltac:(lia) ltac:(lia)). }
  assert (Hwr_blk : forall a kk x, In (a, kk) Lamg -> a <= x < a + kk -> writable_at (ms_segs B) m3 x).
  { intros a kk x Hin Hx. apply (proj2 (HBS a kk x Hin Hx)).
    replace x with (a + (x - a)) by lia. apply (present_writable B memg).
    exact (ledger_block_present B API Lg Ag memg mdg Lamg _ _ _ a kk (x - a) HMRg HLg Hin ltac:(lia)). }
  assert (Hpr_blk : forall a kk x, In (a, kk) Lamg -> a <= x < a + kk -> mbyte (ms_segs B) m3 x <> None).
  { intros a kk x Hin Hx. rewrite (proj1 (HBS a kk x Hin Hx)). replace x with (a + (x - a)) by lia.
    destruct (ledger_block_present B API Lg Ag memg mdg Lamg _ _ _ a kk (x - a) HMRg HLg Hin ltac:(lia)) as (bb & Hbb).
    unfold mbyte. rewrite Hbb. discriminate. }
  assert (Hwr_o : forall x, o <= x < o + 56 -> writable_at (ms_segs B) m3 x)
    by (intros x Hx; exact (proj2 (HOS x Hx) (proj1 (HoSt x Hx)))).
  assert (Hwr_w : forall x, w <= x < w + 56 -> writable_at (ms_segs B) m3 x)
    by (intros x Hx; exact (proj2 (HWS x Hx) (proj1 (HwSt x Hx)))).
  assert (G3_2 : getr regs3 2 = Z_to_bv 64 (spZ regs - 48)) by (rewrite <- G2g; apply (Hp3 2); unfold callee_saved; lia).
  assert (G3_8 : getr regs3 8 = Z_to_bv 64 w) by (rewrite <- G8g; apply (Hp3 8); unfold callee_saved; lia).
  assert (G3_9 : getr regs3 9 = Z_to_bv 64 o) by (rewrite <- G9g; apply (Hp3 9); unfold callee_saved; lia).
  assert (G3k : forall r, r = 3 \/ r = 4 \/ 20 <= r <= 27 -> getr regs3 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
  { intros r Hr. rewrite <- (Gkg r Hr). apply (Hp3 r). unfold callee_saved. lia. }
  assert (FR3m : rw_cells (ms_segs B) m3 (spZ regs - 48)
    [CB 8 junk; C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)]).
  { apply (g_rw_cells B memg); [exact FRg|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx.
    assert (No1 : ~ owned B Lg Ag x) by (intros Ho; pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HMRg Ho); lia).
    assert (No2 : ~ owned B L3 A3 x) by (intros Ho; pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HMR3 Ho); lia).
    destruct (Hfr3 x ltac:(left; lia) No1 No2
      ltac:(unfold scratch_k; rewrite Hsg, Herrno; unfold strtod_c.STRTOD_ERRNO; lia)
      ltac:(intros HE'; pose proof (HE1c x HE'); lia)) as [E1 E2].
    split; [exact E1 | apply E2]. }
  destruct (g_bytes_old B m3 w 56 ltac:(lia) ltac:(lia) ltac:(lia)) as (bs & Hbsl & WB3).
  { intros i Hi. rewrite (proj1 (HWS (w + i) ltac:(lia))). destruct (HwSt (w + i) ltac:(lia)) as (_ & bb & Hb).
    assert (Eb : mbyte (ms_segs B) memg (w + i) = Some bb) by exact Hb. rewrite Eb. discriminate. }
  assert (Hbsl' : length bs = 56%nat) by lia.
  destruct (g_bytes_old B m3 (kg + 56 * n) 56 ltac:(lia) ltac:(lia) ltac:(lia)) as (jd & Hjdl & JD3).
  { intros i Hi. apply (Hpr_blk kg (56 * capg)); [exact Hkgl | lia]. }
  assert (Hjdl' : length jd = 56%nat) by lia.
  assert (RD3m : rw_cells (ms_segs B) m3 (kg + 56 * n) [CB 56 jd]).
  { apply (g_rw56 B m3 _ jd Hjdl' JD3). intros i Hi. apply (Hwr_blk kg (56 * capg)); [exact Hkgl | lia]. }
  assert (RW3m : rw_cells (ms_segs B) m3 w [CB 56 bs]).
  { apply (g_rw56 B m3 _ bs Hbsl' WB3). intros i Hi. apply Hwr_w. lia. }
  assert (Hni_blk : forall a kk x, In (a, kk) Lamg -> a - 16 <= x < a + kk -> ~ in_img B x).
  { intros a kk x Hin Hx. replace x with (a + (x - a)) by lia.
    exact (ledger_block_not_img B Lg Ag memg Lamg _ _ _ a kk (x - a) HLg Hin ltac:(lia)). }
  assert (Hro_o : forall x, o <= x < o + 56 -> ~ in_img B x).
  { intros x Hx. destruct (Ho3 (x - o) ltac:(lia)) as (_ & _ & _ & O4). replace (o + (x - o)) with x in O4 by lia.
    exact O4. }
  assert (Hro_w : forall x, w <= x < w + 56 -> ~ in_img B x).
  { intros x Hx. destruct (Hw3 (x - w) ltac:(lia)) as (_ & _ & _ & W4). replace (w + (x - w)) with x in W4 by lia.
    exact W4. }
  assert (HRR : 0 <= res < 2 ^ 64) by (destruct Hresr as [->|(R1 & R2 & _)]; lia).
  clear Hresr.
  rewrite G1g.
  destruct (kb_md B API L3 A3 m3 md3 HMR3) as (Hh3 & Hz3).
  apply (kb_run B regs3 _ m3 md3
    (fun R pc' mem' => K_sdx (getr regs 1) (getr regs 2) (getr regs3 3) (getr regs3 4) (getr regs 8) (getr regs 9)
       (getr regs 18) (getr regs 19) (getr regs3 20) (getr regs3 21) (getr regs3 22) (getr regs3 23) (getr regs3 24)
       (getr regs3 25) (getr regs3 26) (getr regs3 27) (getr regs3 2) (getr regs3 8) (getr regs3 9) (getr regs3 18)
       (getr regs3 19) m3 o w res n yg kg bs R pc' mem') _ Hh3 Hz3).
  { assert (Hro3r : MemNorm.ro_agree rsegs m3) by (rewrite <- HSEG; exact Hro3).
    pose proof HDJ0 as HDJ. cbn [Frame.disjoint_from] in HDJ.
    pose proof (g_lam_disj B API Lg Ag memg mdg Lamg _ _ _ kg (56 * capg) yg (8 * capg) HMRg HLg Hkgl Hygl Hneky) as KY.
  assert (DW : w + 56 <= kg + 56 * n \/ kg + 56 * n + 56 <= w).
  { destruct (Z_le_gt_dec (w + 56) (kg + 56 * n)) as [h|h]; [left; exact h|].
    destruct (Z_le_gt_dec (kg + 56 * n + 56) w) as [h'|h']; [right; exact h'|].
    exfalso. exact (proj1 (HSUB kg (56 * capg) Hks (Z.max w (kg + 56 * n)) ltac:(lia)) ltac:(lia)). }
  assert (KW : yg + 8 * n + 8 <= w \/ w + 56 <= yg + 8 * n).
  { destruct (Z_le_gt_dec (yg + 8 * n + 8) w) as [h|h]; [left; exact h|].
    destruct (Z_le_gt_dec (w + 56) (yg + 8 * n)) as [h'|h']; [right; exact h'|].
    exfalso. exact (proj1 (HSUB yg (8 * capg) Hys (Z.max w (yg + 8 * n)) ltac:(lia)) ltac:(lia)). }
  assert (OW : o + 56 <= w \/ w + 56 <= o).
  { destruct (Z_le_gt_dec (o + 56) w) as [h|h]; [left; exact h|].
    destruct (Z_le_gt_dec (w + 56) o) as [h'|h']; [right; exact h'|].
    exfalso. apply (HWD (Z.max o w) ltac:(lia)). left. lia. }
  assert (OK : o + 56 <= kg + 56 * n \/ kg + 56 * n + 56 <= o).
  { destruct (Z_le_gt_dec (o + 56) (kg + 56 * n)) as [h|h]; [left; exact h|].
    destruct (Z_le_gt_dec (kg + 56 * n + 56) o) as [h'|h']; [right; exact h'|].
    exfalso. exact (proj2 (HSUB kg (56 * capg) Hks (Z.max o (kg + 56 * n)) ltac:(lia)) ltac:(lia)). }
  assert (KO : yg + 8 * n + 8 <= o \/ o + 56 <= yg + 8 * n).
  { destruct (Z_le_gt_dec (yg + 8 * n + 8) o) as [h|h]; [left; exact h|].
    destruct (Z_le_gt_dec (o + 56) (yg + 8 * n)) as [h'|h']; [right; exact h'|].
    exfalso. exact (proj2 (HSUB yg (8 * capg) Hys (Z.max o (yg + 8 * n)) ltac:(lia)) ltac:(lia)). }
    assert (G3_2r : getr regs3 2 = Z_to_bv 64 (bv_unsigned (getr regs 2) + -48))
      by (rewrite G3_2; f_equal; rewrite HSP; lia).
    rewrite HSEG in BNg, BYg, BKg, FR3m, WB3, RD3m, RW3m.
    apply (run_sdx B HMC HMS regs3 m3 (getr regs 2) (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18)
      (getr regs 19) junk o w res n yg kg bs jd bs HSEG Hro3r G3_2r G310 HRR G3_8 G3_9).
    - rewrite <- HSEG. apply (g_bytes B memg); [rewrite HSEG; exact BNg|]. intros x Hx. rewrite length_le8 in Hx.
      exact (proj1 (HOS x ltac:(lia))).
    - rewrite <- HSEG. apply (g_bytes B memg); [rewrite HSEG; exact BYg|]. intros x Hx. rewrite length_le8 in Hx.
      exact (proj1 (HOS x ltac:(lia))).
    - rewrite <- HSEG. apply (g_bytes B memg); [rewrite HSEG; exact BKg|]. intros x Hx. rewrite length_le8 in Hx.
      exact (proj1 (HOS x ltac:(lia))).
    - rewrite <- HSEG. apply (g_wr B); [lia | lia|]. intros i Hi. apply (Hwr_blk yg (8 * capg)); [exact Hygl | lia].
    - rewrite <- HSEG. apply (g_wr B); [lia | lia|]. intros i Hi. apply Hwr_o. lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - exact KO.
    - rewrite HSP. replace (spZ regs + -48) with (spZ regs - 48) by lia. exact FR3m.
    - exact Hbsl'.
    - exact WB3.
    - exact RD3m.
    - exact RW3m.
    - exact DW.
    - rewrite HSP. lia.
    - rewrite HSP. lia.
    - rewrite HSP. lia.
    - rewrite HSP. lia.
    - exact KW.
    - exact OW.
    - lia.
    - exact OK.
    - rewrite HSP. lia.
    - intros i Hi. unfold wa. rewrite <- HSEG. apply (g_ro_low B HIL). rewrite HSP. lia.
    - intros i Hi. unfold wa. rewrite <- HSEG. apply (g_ro_notimg B HSEG); [lia|].
      apply (Hni_blk yg (8 * capg)); [exact Hygl | lia].
    - intros i Hi. unfold wa. rewrite <- HSEG. apply (g_ro_notimg B HSEG); [lia|]. apply Hro_o. lia.
    - intros i Hi. unfold wa. rewrite <- HSEG. apply (g_ro_notimg B HSEG); [lia|].
      apply (Hni_blk kg (56 * capg)); [exact Hkgl | lia].
    - intros i Hi. unfold wa. rewrite <- HSEG. apply (g_ro_notimg B HSEG); [lia|]. apply Hro_w. lia. }
  intros R pc4 m4 regs4 HK4 Hg4. unfold K_sdx in HK4.
  destruct HK4 as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & WM4 & RS4 &
    [(Hr0 & MU4 & BK4 & ER & EP)|(Hrn & MU4 & BK4 & BN4 & DB4 & WZ4 & ER & EP)]); subst R pc4;
    rewrite <- HSEG in WM4, BK4; pose proof HLg as (_ & _ & Hcr & _);
    assert (Hg2 : (g <= 2)%nat) by (unfold hid in HcaseH; destruct HcaseH as [(_ & -> & _)|(_ & -> & _)]; lia).
  - unfold hid in ARM3H.
    destruct ARM3H as [(Hcf & _ & EL3 & EA3 & Emd & Hrf3 & _ & _ & HL3)|(_ & Hrn' & _)]; [|lia].
    clear Emd3. subst L3 A3 md3 res.
    assert (HnS4 : forall x, ~ Frame.outside [(yg + 8 * n, yg + 8 * n + 8)] x -> yg + 8 * n <= x < yg + 8 * n + 8)
      by (intros x Ho; exact (g_nout1 _ _ _ Ho)).
    assert (HR4 : rpost B API (PJ_SET_K dd) L A regs mem md (pj_set_writes o w D Dw) (freed (D ++ Dw)) Lg Ag regs m4 mdg).
    { apply (rp_A2 B API HIL (PJ_SET_K dd) L A regs mem md _ _ Lg Ag m3 mdg m4 _ HMR ltac:(lia) HR3 MU4 WM4).
      - intros x Hx Ho _. pose proof (HnS4 x Ho) as Hx'.
        apply (g_present_wr B HSEG m4 x ltac:(lia)); [apply (Hni_blk yg (8 * capg)); [exact Hygl | lia]|].
        exact (WM4 _ (Hwr_blk yg (8 * capg) x Hygl ltac:(lia))).
      - intros x Ho. pose proof (HnS4 x Ho) as Hx'.
        destruct (g_body_w (PJ_SET_K dd) L A regs mem md _ _ Lg Ag regs m3 mdg Lamg _ _ _ yg (8 * capg) x HR3 HL3 Hygl
          (HSE yg (8 * capg) Hys0) ltac:(lia)) as (Hno & Hor).
        split; [exact Hno | right; exact Hor]. }
    pose proof HR4 as (HM4 & _).
    assert (HL4 : ledger B Lg Ag m4 Lamg (Z.max peak (lsum Lamg)) (cnt + Z.of_nat (S g)) (2 ^ 64 - 1)).
    { replace (cnt + Z.of_nat (S g)) with ((cnt + Z.of_nat g + 1) mod 2 ^ 64) by (rewrite Z.mod_small by lia; lia).
      apply (g_ledger_munch B API Lg Ag m3 mdg m4 _ _ _ _ _ HMR3 HL3 MU4).
      intros x Ho. pose proof (HnS4 x Ho) as Hx'. split.
      - intros Hs. apply (Hni_blk yg (8 * capg) x Hygl ltac:(lia)). exact (g_img_consts B HSEG Herrno x (or_introl Hs)).
      - intros a kk Hin Ha. destruct (Z.eq_dec a yg) as [->|Ha']; [lia|].
        assert (Hne : (a, kk) <> (yg, 8 * capg)) by (intros E0; injection E0; lia).
        assert (Hkk : 0 <= kk) by (pose proof HL3 as (_ & _ & _ & _ & _ & HF3); rewrite Forall_forall in HF3;
          exact (proj1 (HF3 _ Hin))).
        destruct (g_lam_disj B API Lg Ag m3 mdg Lamg _ _ _ a kk yg (8 * capg) HMR3 HL3 Hin Hygl Hne); lia. }
    assert (Hrd4 : rd_cells B m4).
    { split.
      - apply (g_ro_munch B _ m3 m4 Hro3 MU4). intros a Ha Ho. pose proof (HnS4 a Ho) as Hx'.
        apply (g_ro_notimg B HSEG); [lia|]. apply (Hni_blk yg (8 * capg)); [exact Hygl | lia].
      - destruct (YL01.ax_statics AX Lg Ag m4 mdg HM4) as (Hgg & (gg & _ & Hggw) & _).
        split; [exact Hgg | exists gg; exact Hggw]. }
    assert (FR4 : rw_cells (ms_segs B) m4 (spZ regs - 48)
      [CB 8 junk; C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)]).
    { apply (g_rw_cells B m3); [exact FR3m|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx.
      split; [apply (mbyte_munch (ms_segs B) _ m3 m4 x MU4 ltac:(lia)); cbn [Frame.outside]; split; [lia | exact I]|].
      intros Hw'. exact (WM4 _ Hw'). }
    assert (G4_1 : getr regs4 1 = Z_to_bv 64 PS_FREEW_RET) by (rewrite Hg4; reflexivity).
    assert (G4_2 : getr regs4 2 = Z_to_bv 64 (spZ regs - 48))
      by (transitivity (getr regs3 2); [rewrite Hg4; reflexivity | exact G3_2]).
    assert (G4_10 : getr regs4 10 = Z_to_bv 64 w) by (rewrite Hg4; reflexivity).
    assert (G4k : forall r, r = 3 \/ r = 4 \/ 20 <= r <= 27 -> getr regs4 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
    { intros r Hr. rewrite <- (G3k r Hr).
      assert (Hr' : r = 3 \/ r = 4 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27)
        by lia.
      destruct Hr' as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]; rewrite Hg4; reflexivity. }
    assert (HS4 : forall x, 0 <= x < 2 ^ 64 -> ~ (yg + 8 * n <= x < yg + 8 * n + 8) -> pis_same (ms_segs B) m3 m4 x).
    { intros x Hx Hn0. apply (g_same_munch (ms_segs B) _ m3 m4 x MU4 WM4 Hx). cbn [Frame.outside].
      split; [lia | exact I]. }
    pose proof (g_lam_disj B API Lg Ag memg mdg Lamg _ _ _ kg (56 * capg) yg (8 * capg) HMRg HLg Hkgl Hygl Hneky) as KY.
    assert (HOg4 : pis_open (ms_segs B) m4 (lin Lamg) o true num kg yg capg n (map snd ms) (map fst ms) Di).
    { apply (pis_frame (ms_segs B) memg (lin Lamg) m4 (lin Lamg) o true num kg yg capg n (map snd ms) (map fst ms) Di
        num n HOg).
      - apply (pis_hdr_frame (ms_segs B) memg m4 o _ num 0 kg yg n capg HHg). intros x Hx.
        apply (g_same_trans (ms_segs B) memg m3 m4 x (HOS x Hx)). apply HS4; [lia|].
        intros Hk. exact (proj2 (HSUB yg (8 * capg) Hys x ltac:(lia)) Hx).
      - lia.
      - exact (pis_open_lblk (ms_segs B) memg (lin Lamg) o true num kg yg capg n _ _ Di HOg).
      - rewrite length_map. intros x [Hx|[(_ & Hx)|((a & kk) & Hb & Hx)]].
        + apply (g_same_trans (ms_segs B) memg m3 m4 x (HBS kg (56 * capg) x Hkgl ltac:(lia))). apply HS4; lia.
        + apply (g_same_trans (ms_segs B) memg m3 m4 x (HBS yg (8 * capg) x Hygl ltac:(lia))). apply HS4; lia.
        + unfold pj_holds in Hx; cbn [fst snd] in Hx.
          assert (HinL : In (a, kk) Lamg) by (apply HSLL; apply in_or_app; right; exact Hb).
          assert (Hne : (a, kk) <> (yg, 8 * capg)).
          { intros E0. rewrite E0 in Hb. exact (pis_nodup_app_disj _ _ _ _ HNDg Hys0 Hb). }
          destruct (ledger_block_range B API Lg Ag memg mdg Lamg _ _ _ a kk HMRg HLg HinL) as (R1 & R2 & _).
          apply (g_same_trans (ms_segs B) memg m3 m4 x (HBS a kk x HinL Hx)). apply HS4; [lia|].
          destruct (g_lam_disj B API Lg Ag memg mdg Lamg _ _ _ a kk yg (8 * capg) HMRg HLg HinL Hygl Hne); lia. }
    pose proof (ps_obj_node (ms_segs B) m4 (lin Lamg) o ms Di num kg yg n capg HOg4 En) as HNo4.
    assert (HNw4 : pj_node (ms_segs B) m4 (lin Lamg) w tv Dw).
    { apply (pis_node_frame (ms_segs B) tv memg (lin Lamg) m4 (lin Lamg) w Dw HNwg);
        [intros a kk Hb; exact (HDwLg a kk Hb)|].
      intros x [Hx|((a & kk) & Hb & Hx)].
      - apply (g_same_trans (ms_segs B) memg m3 m4 x (HWS x Hx)). apply HS4; [lia|].
        intros Hk. exact (proj1 (HSUB yg (8 * capg) Hys x ltac:(lia)) Hx).
      - unfold pj_holds in Hx; cbn [fst snd] in Hx.
        pose proof (HDwLg a kk Hb) as HinL.
        assert (Hne : (a, kk) <> (yg, 8 * capg)) by (intros E0; rewrite E0 in Hb; exact (HDwS _ Hb Hys)).
        destruct (ledger_block_range B API Lg Ag memg mdg Lamg _ _ _ a kk HMRg HLg HinL) as (R1 & R2 & _).
        apply (g_same_trans (ms_segs B) memg m3 m4 x (HBS a kk x HinL Hx)). apply HS4; [lia|].
        destruct (g_lam_disj B API Lg Ag memg mdg Lamg _ _ _ a kk yg (8 * capg) HMRg HLg HinL Hygl Hne); lia. }
    unfold hid in HcaseH.
    apply (fail_arm B API F HFREE L A regs mem md Lam peak cnt fail b o k w ms tv D Dw kids keys n cap kname dd lo
      Lg Ag regs4 m4 mdg Lamg junk ro rko rw rkw (S g) Lr (pis_slots true kg yg capg ++ Di) Dold Dnew Dr
      (depth (JObj ms)) HE0 HPo HPw HWD HAw HDJ0 Hlo Hax HElo Hlw Hnin' HPL HR4 HL4).
    + replace (S g - 1)%nat with g by lia. exact Hrf3.
    + exact Hrd4.
    + exact FR4.
    + exact G4_1.
    + exact G4_2.
    + exact G4_10.
    + exact G4k.
    + exact Hw0.
    + exact (pj_fd_mono (ms_segs B) m4 (lin Lamg) (depth tv) dd w Dw Hdt
        (pj_node_fd (ms_segs B) tv m4 (lin Lamg) w Dw HNw4)).
    + exact HVwg.
    + exact HVog.
    + rewrite <- HDg, <- app_assoc. exact HPLg.
    + exact (pj_node_fd (ms_segs B) (JObj ms) m4 (lin Lamg) o _ HNo4).
    + intros _. exact HNo4.
    + exact HAPw.
    + rewrite Hltr. lia.
    + lia.
    + replace (S g - 1)%nat with g by lia. rewrite <- HDg. exact Hlenh.
    + replace (S g - 1)%nat with g by lia. rewrite <- HDg. exact Hsumh.
    + exact HPD.
    + rewrite HDg. apply Permutation_refl.
    + exact Hnew.
    + destruct HcaseH as [(Hlt & -> & HO1 & HN1)|(Heq & -> & HO1 & HN1)];
        [left; split; [reflexivity | split; assumption]|].
      right; right. split; [exact Heq|]. split; [reflexivity|]. split; assumption.
  - unfold hid in ARM3H.
    destruct ARM3H as [(_ & Hr0' & _)|(Hcf & _ & Hr16 & Hrf3 & Hnst & Hnimg & Hnin3 & BS3 & (b1 & b2 & Eb3 & Eb2) &
      HL3)]; [lia|].
    rewrite <- HSEG in BN4, DB4, WZ4.
    pose proof (ledger_block_range B API L3 A3 m3 md3 _ _ _ _ res (Z.of_nat (length kname) + 1) HMR3 HL3 (in_eq _ _))
      as (Rr1 & Rr2 & _).
    destruct (g_fresh1 Lg Ag L3 A3 m3 md3 b1 b2 _ HMR3 Eb3 Eb2 ltac:(cbn [snd]; lia)) as (Hfr1 & Hfr1').
    assert (HinL3 : forall a kk, In (a, kk) Lamg -> In (a, kk) ((res, Z.of_nat (length kname) + 1) :: Lamg))
      by (intros a kk H; right; exact H).
    assert (Hsub3 : forall a kk, In (a, kk) ((res, Z.of_nat (length kname) + 1) :: Lamg) ->
        In (a, kk) Lamg \/ ~ In (a - 16, kk + 16) (blocks Lg Ag)).
    { intros a kk [E0|Hin]; [|left; exact Hin]. injection E0 as <- <-. right.
      replace (Z.of_nat (length kname) + 1 + 16) with (Z.of_nat (length kname) + 17) by lia. exact Hfr1. }
    pose proof (vplace_call B API Lg Ag Lamg (spZ regs) o ro rko (ALLOC_STACK + 64) regsg memg mdg _ L3 A3 regs3 m3 md3
      (0, 0) _ _ _ _ HVog Hpost3 Hub3 Hne0o HL3 Hsub3) as HVo3.
    pose proof (vplace_call B API Lg Ag Lamg (spZ regs) w rw rkw (ALLOC_STACK + 64) regsg memg mdg _ L3 A3 regs3 m3 md3
      (0, 0) _ _ _ _ HVwg Hpost3 Hub3 Hne0w HL3 Hsub3) as HVw3.
    assert (HRk : forall x, res <= x < res + Z.of_nat (length kname) + 1 ->
        ~ (yg + 8 * n <= x < yg + 8 * n + 8) /\ ~ (kg + 56 * n <= x < kg + 56 * n + 56)).
    { intros x Hx.
      assert (Hne1 : (res, Z.of_nat (length kname) + 1) <> (yg, 8 * capg)).
      { intros E0. injection E0 as E1 E2. apply Hnin3. apply in_map_iff. exists (yg, 8 * capg).
        split; [cbn [fst]; lia | exact Hygl]. }
      assert (Hne2 : (res, Z.of_nat (length kname) + 1) <> (kg, 56 * capg)).
      { intros E0. injection E0 as E1 E2. apply Hnin3. apply in_map_iff. exists (kg, 56 * capg).
        split; [cbn [fst]; lia | exact Hkgl]. }
      pose proof (g_lam_disj B API L3 A3 m3 md3 _ _ _ _ res (Z.of_nat (length kname) + 1) yg (8 * capg) HMR3 HL3
        (in_eq _ _) (HinL3 _ _ Hygl) Hne1) as D1.
      pose proof (g_lam_disj B API L3 A3 m3 md3 _ _ _ _ res (Z.of_nat (length kname) + 1) kg (56 * capg) HMR3 HL3
        (in_eq _ _) (HinL3 _ _ Hkgl) Hne2) as D2.
      split; lia. }
    assert (HRo : forall x, res - 16 <= x < res + Z.of_nat (length kname) + 1 -> x < o \/ o + 56 <= x).
    { intros x Hx.
      apply (vloc_disj B API L3 A3 _ m3 md3 (spZ regs) o ro rko (res - 16) (Z.of_nat (length kname) + 17) x
        (proj1 HVo3) HMR3 ltac:(lia) Hfr1'); [|lia].
      intros E0. apply (vloc_ne Lg Ag Lamg (spZ regs) o ro rko (res - 16) (Z.of_nat (length kname) + 17) (proj1 HVog)
        Hfr1 ltac:(lia)). symmetry. exact E0. }
    assert (HRw : forall x, res - 16 <= x < res + Z.of_nat (length kname) + 1 -> x < w \/ w + 56 <= x).
    { intros x Hx.
      apply (vloc_disj B API L3 A3 _ m3 md3 (spZ regs) w rw rkw (res - 16) (Z.of_nat (length kname) + 17) x
        (proj1 HVw3) HMR3 ltac:(lia) Hfr1'); [|lia].
      intros E0. apply (vloc_ne Lg Ag Lamg (spZ regs) w rw rkw (res - 16) (Z.of_nat (length kname) + 17) (proj1 HVwg)
        Hfr1 ltac:(lia)). symmetry. exact E0. }
    assert (HR4 : rpost B API (PJ_SET_K dd) L A regs mem md (pj_set_writes o w D Dw) (freed (D ++ Dw)) L3 A3 regs m4 md3).
    { apply (rp_A2 B API HIL (PJ_SET_K dd) L A regs mem md _ _ L3 A3 m3 md3 m4 _ HMR ltac:(lia) HR3 MU4 WM4).
      - intros x Hx Ho _. destruct (g_nout4 _ _ _ _ _ _ _ _ x Ho) as [Hx'|[Hx'|[Hx'|Hx']]].
        + apply (g_present_wr B HSEG m4 x ltac:(lia)); [apply (Hni_blk yg (8 * capg)); [exact Hygl | lia]|].
          exact (WM4 _ (Hwr_blk yg (8 * capg) x Hygl ltac:(lia))).
        + apply (g_present_wr B HSEG m4 x ltac:(lia)); [apply Hro_o; lia|]. exact (WM4 _ (Hwr_o x ltac:(lia))).
        + apply (g_present_wr B HSEG m4 x ltac:(lia)); [apply (Hni_blk kg (56 * capg)); [exact Hkgl | lia]|].
          exact (WM4 _ (Hwr_blk kg (56 * capg) x Hkgl ltac:(lia))).
        + apply (g_present_wr B HSEG m4 x ltac:(lia)); [apply Hro_w; lia|]. exact (WM4 _ (Hwr_w x ltac:(lia))).
      - intros x Ho. destruct (g_nout4 _ _ _ _ _ _ _ _ x Ho) as [Hx'|[Hx'|[Hx'|Hx']]].
        + destruct (g_body_w (PJ_SET_K dd) L A regs mem md _ _ L3 A3 regs m3 md3 _ _ _ _ yg (8 * capg) x HR3 HL3
            (HinL3 _ _ Hygl) (HSE yg (8 * capg) Hys0) ltac:(lia)) as (Hno & Hor).
          split; [exact Hno | right; exact Hor].
        + destruct (Ho3 (x - o) ltac:(lia)) as (O1 & _). replace (o + (x - o)) with x in O1 by lia.
          split; [|right; left; unfold pj_set_writes; left; lia].
          apply (vloc_own B API L3 A3 _ m3 md3 (spZ regs) o ro rko x (proj1 HVo3) HMR3 ltac:(lia) ltac:(lia)).
          intros Hs. exact (O1 (or_intror Hs)).
        + destruct (g_body_w (PJ_SET_K dd) L A regs mem md _ _ L3 A3 regs m3 md3 _ _ _ _ kg (56 * capg) x HR3 HL3
            (HinL3 _ _ Hkgl) (HSE kg (56 * capg) Hks0) ltac:(lia)) as (Hno & Hor).
          split; [exact Hno | right; exact Hor].
        + destruct (Hw3 (x - w) ltac:(lia)) as (W1 & _). replace (w + (x - w)) with x in W1 by lia.
          split; [|right; left; unfold pj_set_writes; right; left; lia].
          apply (vloc_own B API L3 A3 _ m3 md3 (spZ regs) w rw rkw x (proj1 HVw3) HMR3 ltac:(lia) ltac:(lia)).
          intros Hs. exact (W1 (or_intror Hs)). }
    pose proof HR4 as (HM4 & _).
    assert (HL4 : ledger B L3 A3 m4 ((res, Z.of_nat (length kname) + 1) :: Lamg)
        (Z.max (Z.max peak (lsum Lamg)) (lsum Lamg + Z.of_nat (length kname) + 1)) (cnt + Z.of_nat (S g)) fail).
    { replace (cnt + Z.of_nat (S g)) with ((cnt + Z.of_nat g + 1) mod 2 ^ 64) by (rewrite Z.mod_small by lia; lia).
      apply (g_ledger_munch B API L3 A3 m3 md3 m4 _ _ _ _ _ HMR3 HL3 MU4).
      intros x Ho. destruct (g_nout4 _ _ _ _ _ _ _ _ x Ho) as [Hx'|[Hx'|[Hx'|Hx']]].
      + split; [intros Hs; apply (Hni_blk yg (8 * capg) x Hygl ltac:(lia));
          exact (g_img_consts B HSEG Herrno x (or_introl Hs))|].
        intros a kk Hin Ha. destruct (Z.eq_dec a yg) as [->|Ha']; [lia|].
        assert (Hne : (a, kk) <> (yg, 8 * capg)) by (intros E0; injection E0; lia).
        assert (Hkk : 0 <= kk) by (pose proof HL3 as (_ & _ & _ & _ & _ & HF3); rewrite Forall_forall in HF3;
          exact (proj1 (HF3 _ Hin))).
        destruct (g_lam_disj B API L3 A3 m3 md3 _ _ _ _ a kk yg (8 * capg) HMR3 HL3 Hin (HinL3 _ _ Hygl) Hne); lia.
      + destruct (Ho3 (x - o) ltac:(lia)) as (_ & O2 & _). replace (o + (x - o)) with x in O2 by lia.
        split; [exact O2|]. intros a kk Hin Ha.
        destruct (vloc_heads B API L3 A3 _ m3 md3 _ _ _ (spZ regs) o ro rko a kk (proj1 HVo3) HMR3 HL3 ltac:(lia) Hin);
          lia.
      + split; [intros Hs; apply (Hni_blk kg (56 * capg) x Hkgl ltac:(lia));
          exact (g_img_consts B HSEG Herrno x (or_introl Hs))|].
        intros a kk Hin Ha. destruct (Z.eq_dec a kg) as [->|Ha']; [lia|].
        assert (Hne : (a, kk) <> (kg, 56 * capg)) by (intros E0; injection E0; lia).
        assert (Hkk : 0 <= kk) by (pose proof HL3 as (_ & _ & _ & _ & _ & HF3); rewrite Forall_forall in HF3;
          exact (proj1 (HF3 _ Hin))).
        destruct (g_lam_disj B API L3 A3 m3 md3 _ _ _ _ a kk kg (56 * capg) HMR3 HL3 Hin (HinL3 _ _ Hkgl) Hne); lia.
      + destruct (Hw3 (x - w) ltac:(lia)) as (_ & W2 & _). replace (w + (x - w)) with x in W2 by lia.
        split; [exact W2|]. intros a kk Hin Ha.
        destruct (vloc_heads B API L3 A3 _ m3 md3 _ _ _ (spZ regs) w rw rkw a kk (proj1 HVw3) HMR3 HL3 ltac:(lia) Hin);
          lia. }
    assert (Hrd4 : rd_cells B m4).
    { split.
      - apply (g_ro_munch B _ m3 m4 Hro3 MU4). intros a Ha Ho. apply (g_ro_notimg B HSEG); [lia|].
        destruct (g_nout4 _ _ _ _ _ _ _ _ a Ho) as [Hx'|[Hx'|[Hx'|Hx']]].
        + apply (Hni_blk yg (8 * capg)); [exact Hygl | lia].
        + apply Hro_o; lia.
        + apply (Hni_blk kg (56 * capg)); [exact Hkgl | lia].
        + apply Hro_w; lia.
      - destruct (YL01.ax_statics AX L3 A3 m4 md3 HM4) as (Hgg & (gg & _ & Hggw) & _).
        split; [exact Hgg | exists gg; exact Hggw]. }
    assert (HPL3 : Permutation ((res, Z.of_nat (length kname) + 1) :: Lamg)
        ((pis_slots true kg yg capg ++ Di ++ (res, Z.of_nat (length kname) + 1) :: Dw) ++ Lr)).
    { assert (EDo : (pis_slots true kg yg capg ++ Di ++ (res, Z.of_nat (length kname) + 1) :: Dw) ++ Lr =
          (pis_slots true kg yg capg ++ Di) ++ (res, Z.of_nat (length kname) + 1) :: Dw ++ Lr)
        by (rewrite <- !app_assoc; reflexivity).
      rewrite EDo. apply Permutation_cons_app. rewrite <- HDg, <- app_assoc. exact HPLg. }
    assert (HS4 : forall x, 0 <= x < 2 ^ 64 -> ~ (yg + 8 * n <= x < yg + 8 * n + 8) -> ~ (o + 40 <= x < o + 48) ->
        ~ (kg + 56 * n <= x < kg + 56 * n + 56) -> ~ (w <= x < w + 56) -> pis_same (ms_segs B) m3 m4 x).
    { intros x Hx H1 H2 H3 H4. apply (g_same_munch (ms_segs B) _ m3 m4 x MU4 WM4 Hx). cbn [Frame.outside].
      refine (conj _ (conj _ (conj _ (conj _ I)))); lia. }
    rewrite (kb_ret_pc _ Hra). apply SR_ret. unfold set_post.
    exists L3, A3, regs4, m4, md3, ((res, Z.of_nat (length kname) + 1) :: Lamg),
      (Z.max (Z.max peak (lsum Lamg)) (lsum Lamg + Z.of_nat (length kname) + 1)), fail, 0, (S g), Lr,
      (pis_slots true kg yg capg ++ Di ++ (res, Z.of_nat (length kname) + 1) :: Dw).
    split; [reflexivity|].
    split.
    { eapply rp_regs; [exact HR4|].
      cs_cases ltac:(rewrite Hg4; first
        [ reflexivity
        | match goal with |- getr _ (Z_to_bv 5 ?k) = _ =>
            transitivity (getr regs3 (Z_to_bv 5 k)); [reflexivity|]; exact (G3k k ltac:(lia)) end ]). }
    split; [exact Hrd4|]. split; [rewrite Hg4; reflexivity|]. split; [exact HL4|].
    split; [unfold hid in HfgH; unfold fail_after; split; intros; lia|].
    split; [exact HPL|]. split; [exact HPL3|].
    split.
    { split; [split; [exact Hw8|] |].
      - replace (w + 56) with (w + Z.of_nat (cells_size [CB 56 (repeat (Z_to_bv 8 0) 56)])) by reflexivity.
        exact (g_stk_rw B m4 w _ WZ4).
      - pose proof (proj2 (proj1 WZ4)) as HB. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB. exact HB. }
    split; [intros _; reflexivity|].
    right; left.
    split; [exact Hnin'|]. split; [rewrite Hltr; unfold hid in HfgH; lia|].
    split; [symmetry; exact Hltr|]. split; [reflexivity|]. split; [cbn [lsum]; lia|].
    split; [rewrite Hrun; exact Hrf3|].
    split.
    { rewrite Hnl, (app_assoc (pis_slots true kg yg capg) Di), <- HDg.
      rewrite !length_app in Hlenh. rewrite !length_app. cbn [length]. lia. }
    split.
    { rewrite Hhd, (app_assoc (pis_slots true kg yg capg) Di), <- HDg.
      rewrite !g_lsum_app in Hsumh. rewrite !g_lsum_app. cbn [lsum]. lia. }
    split.
    { exists Dold, Dnew, Dr, res. split; [exact HPD|]. split.
      { rewrite (app_assoc (pis_slots true kg yg capg) Di), <- HDg, <- app_assoc. apply Permutation_app_head.
        apply Permutation_sym. apply Permutation_middle. }
      split.
      { intros a' k' Hin. apply in_app_or in Hin. destruct Hin as [Hin|[E0|[]]]; [right; exact (Hnew a' k' Hin)|].
        injection E0 as <- <-.
        assert (Hdec : forall x y : Z * Z, {x = y} + {x <> y}).
        { intros [x1 x2] [y1 y2]. destruct (Z.eq_dec x1 y1); destruct (Z.eq_dec x2 y2);
            [left; congruence | right; congruence | right; congruence | right; congruence]. }
        destruct (in_dec Hdec (res, Z.of_nat (length kname) + 1) Dold) as [Hd|Hd]; [left; exact Hd|right]. intros Hb.
        destruct (in_dec Hdec (res, Z.of_nat (length kname) + 1) (D ++ Dw)) as [HiD|HiD].
        - apply Hnin3. apply in_map_iff. exists (res, Z.of_nat (length kname) + 1). split; [reflexivity|].
          apply (Permutation_in _ (Permutation_sym HPLg)). apply in_app_or in HiD. destruct HiD as [HiD|HiD].
          + pose proof (Permutation_in _ HPD HiD) as H3. apply in_app_or in H3.
            destruct H3 as [H3|H3]; [exact (False_ind _ (Hd H3))|]. apply in_or_app. right. apply in_or_app. left.
            exact H3.
          + apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact HiD.
        - destruct (g_blocks_user L A _ _ Hb) as (q & Hq & Eq).
          pose proof HRg as (_ & _ & _ & _ & _ & _ & _ & H8 & H9 & _).
          assert (Hng : ~ freed (D ++ Dw) (ptr_addr L q) (Z.of_nat (length kname) + 1 + 16)).
          { unfold freed. rewrite Eq. replace (res - 16 + 16) with res by lia.
            replace (Z.of_nat (length kname) + 1 + 16 - 16) with (Z.of_nat (length kname) + 1) by lia. exact HiD. }
          pose proof (H8 q _ Hq Hng) as Hq'. apply Hfr1.
          pose proof (g_user_blocks Lg Ag q _ Hq') as Hb'. rewrite (H9 q _ Hq Hq'), Eq in Hb'.
          replace (Z.of_nat (length kname) + 17) with (Z.of_nat (length kname) + 1 + 16) by lia. exact Hb'. }
      unfold hid in HcaseH. destruct HcaseH as [(Hlt & _ & HO1 & HN1)|(Heq & _ & HO1 & HN1)];
        [left; split; [exact Hlt | split; assumption] | right; split; [exact Heq|]; split; assumption]. }
    rewrite (ps_set_miss ms (zb kname) tv Hnin).
    assert (HH4 : pj_hdr (ms_segs B) m4 o (5 + pis_oz true) num 0 kg yg (n + 1) capg).
    { apply (pis_hdr_n (ms_segs B) memg m4 o _ num 0 kg yg n capg (n + 1) HHg ltac:(lia) BN4).
      - intros x Hx Hn0.
        assert (H1 : ~ (yg + 8 * n <= x < yg + 8 * n + 8))
          by (intros Hk; exact (proj2 (HSUB yg (8 * capg) Hys x ltac:(lia)) Hx)).
        assert (H3 : ~ (kg + 56 * n <= x < kg + 56 * n + 56))
          by (intros Hk; exact (proj2 (HSUB kg (56 * capg) Hks x ltac:(lia)) Hx)).
        assert (H4 : ~ (w <= x < w + 56)) by (intros Hk; exact (HWD x Hk (or_introl Hx))).
        rewrite (proj1 (HS4 x ltac:(lia) H1 Hn0 H3 H4)). exact (proj1 (HOS x Hx)).
      - intros x Hx Hw'. exact (WM4 _ (proj2 (HOS x Hx) Hw')). }
    assert (HS4b : forall a kk x, In (a, kk) (pis_slots true kg yg capg ++ Di) -> a <= x < a + kk ->
        ~ (yg + 8 * n <= x < yg + 8 * n + 8) -> ~ (kg + 56 * n <= x < kg + 56 * n + 56) ->
        pis_same (ms_segs B) memg m4 x).
    { intros a kk x Hb Hx H1 H3. destruct (HSUB a kk Hb x Hx) as (Hnw & Hno).
      pose proof (HSLL a kk Hb) as HinL.
      destruct (ledger_block_range B API Lg Ag memg mdg Lamg _ _ _ a kk HMRg HLg HinL) as (R1 & R2 & _).
      apply (g_same_trans (ms_segs B) memg m3 m4 x (HBS a kk x HinL Hx)).
      apply HS4; [lia | exact H1 | lia | exact H3 | exact Hnw]. }
    pose proof (g_lam_disj B API Lg Ag memg mdg Lamg _ _ _ kg (56 * capg) yg (8 * capg) HMRg HLg Hkgl Hygl Hneky) as KY.
    assert (HO4 : pis_open (ms_segs B) m4 (lin ((res, Z.of_nat (length kname) + 1) :: Lamg)) o true num kg yg capg
        (n + 1) (map snd ms) (map fst ms) Di).
    { apply (pis_frame (ms_segs B) memg (lin Lamg) m4 _ o true num kg yg capg n (map snd ms) (map fst ms) Di num
        (n + 1) HOg HH4 ltac:(lia)).
      - intros a kk Hb. right. exact (HSLL a kk Hb).
      - rewrite length_map. intros x [Hx|[(_ & Hx)|((a & kk) & Hb & Hx)]].
        + apply (HS4b kg (56 * capg) x Hks); lia.
        + apply (HS4b yg (8 * capg) x Hys); lia.
        + unfold pj_holds in Hx; cbn [fst snd] in Hx.
          assert (Hb' : In (a, kk) (pis_slots true kg yg capg ++ Di)) by (apply in_or_app; right; exact Hb).
          pose proof (HSLL a kk Hb') as HinL.
          assert (Hne1 : (a, kk) <> (yg, 8 * capg)).
          { intros E0. rewrite E0 in Hb. exact (pis_nodup_app_disj _ _ _ _ HNDg Hys0 Hb). }
          assert (Hne2 : (a, kk) <> (kg, 56 * capg)).
          { intros E0. rewrite E0 in Hb. exact (pis_nodup_app_disj _ _ _ _ HNDg Hks0 Hb). }
          pose proof (g_lam_disj B API Lg Ag memg mdg Lamg _ _ _ a kk yg (8 * capg) HMRg HLg HinL Hygl Hne1) as D1.
          pose proof (g_lam_disj B API Lg Ag memg mdg Lamg _ _ _ a kk kg (56 * capg) HMRg HLg HinL Hkgl Hne2) as D2.
          apply (HS4b a kk x Hb'); lia. }
    assert (HNmem : pj_node (ms_segs B) m4 (lin ((res, Z.of_nat (length kname) + 1) :: Lamg))
        (kg + 56 * Z.of_nat (length (map snd ms))) tv Dw).
    { rewrite length_map. replace (Z.of_nat (length ms)) with n by lia.
      apply (pis_node_xfer (ms_segs B) tv memg (lin Lamg) m4 _ w (kg + 56 * n) Dw HNwg).
      - intros a kk Hb. right. exact (HDwLg a kk Hb).
      - intros x ((a & kk) & Hb & Hx). unfold pj_holds in Hx; cbn [fst snd] in Hx.
        pose proof (HDwLg a kk Hb) as HinL.
        assert (Hne1 : (a, kk) <> (yg, 8 * capg)) by (intros E0; rewrite E0 in Hb; exact (HDwS _ Hb Hys)).
        assert (Hne2 : (a, kk) <> (kg, 56 * capg)) by (intros E0; rewrite E0 in Hb; exact (HDwS _ Hb Hks)).
        destruct (ledger_block_range B API Lg Ag memg mdg Lamg _ _ _ a kk HMRg HLg HinL) as (R1 & R2 & _).
        pose proof (g_lam_disj B API Lg Ag memg mdg Lamg _ _ _ a kk yg (8 * capg) HMRg HLg HinL Hygl Hne1) as D1.
        pose proof (g_lam_disj B API Lg Ag memg mdg Lamg _ _ _ a kk kg (56 * capg) HMRg HLg HinL Hkgl Hne2) as D2.
        apply (g_same_trans (ms_segs B) memg m3 m4 x (HBS a kk x HinL Hx)).
        apply HS4; [lia | lia | | lia |].
        + intros H'. exact (HAw (a, kk) x Hb ltac:(unfold pj_holds; cbn [fst snd]; lia) ltac:(lia)).
        + intros H'. exact (HADw (a, kk) x Hb ltac:(unfold pj_holds; cbn [fst snd]; lia) H').
      - unfold hid in Hkg16. lia.
      - lia.
      - lia.
      - intros j Hj. rewrite <- (g_bytes_eq B m3 m4 w (kg + 56 * n) bs WB3 DB4 j ltac:(rewrite Hbsl'; simpl; lia)).
        exact (proj1 (HWS (w + j) ltac:(lia))).
      - intros j Hj _. exact (WM4 _ (Hwr_blk kg (56 * capg) (kg + 56 * n + j) Hkgl ltac:(lia))).
      - intros (a & kk) x Hb Hx Hx'. unfold pj_holds in Hx; cbn [fst snd] in Hx.
        pose proof (HDwLg a kk Hb) as HinL.
        assert (Hne2 : (a, kk) <> (kg, 56 * capg)) by (intros E0; rewrite E0 in Hb; exact (HDwS _ Hb Hks)).
        destruct (g_lam_disj B API Lg Ag memg mdg Lamg _ _ _ a kk kg (56 * capg) HMRg HLg HinL Hkgl Hne2); lia. }
    assert (Hkey : exists x kk, [(res, Z.of_nat (length kname) + 1)] = [(x, kk)] /\
        pj_u64 (ms_segs B) m4 (yg + 8 * Z.of_nat (length (map snd ms))) x /\
        pj_cstr (ms_segs B) m4 (lin ((res, Z.of_nat (length kname) + 1) :: Lamg)) x kk (zb kname)).
    { exists res, (Z.of_nat (length kname) + 1). split; [reflexivity|].
      rewrite length_map. replace (Z.of_nat (length ms)) with n by lia.
      split; [split; [lia | exact BK4]|].
      split; [left; reflexivity|]. split; [unfold zb; rewrite length_map; lia|].
      split; [exact (g_zb_pos kname Hkn)|]. rewrite map_app, g_zb_map. cbn [map].
      apply (g_bytes B m3 m4 res _ BS3). intros x Hx. rewrite length_app in Hx. cbn [length] in Hx.
      destruct (HRk x ltac:(lia)) as (H1 & H3).
      apply (mbyte_munch (ms_segs B) _ m3 m4 x MU4 ltac:(lia)). cbn [Frame.outside].
      destruct (HRo x ltac:(lia)); destruct (HRw x ltac:(lia)); refine (conj _ (conj _ (conj _ (conj _ I)))); lia. }
    assert (HND5 : NoDup (pis_slots true kg yg capg ++ Di ++ [(res, Z.of_nat (length kname) + 1)] ++ Dw)).
    { pose proof HL4 as (_ & _ & _ & _ & HND & _).
      assert (HN5 : List.NoDup (map fst ((res, Z.of_nat (length kname) + 1) :: Lamg)))
        by (first [exact HND | apply NoDup_ListNoDup; exact HND]).
      pose proof (Permutation_NoDup HPL3 (List.NoDup_map_inv _ _ HN5)) as H6.
      apply NoDup_ListNoDup in H6. exact (pis_nodup_l _ _ Lr H6). }
    assert (HAp5 : pj_apart ([(res, Z.of_nat (length kname) + 1)] ++ Dw) o).
    { intros bk x Hb Hx Hxo. apply in_app_or in Hb. destruct Hb as [[E0|[]]|Hb].
      - subst bk. unfold pj_holds in Hx; cbn [fst snd] in Hx. destruct (HRo x ltac:(lia)); lia.
      - exact (HAw bk x Hb Hx Hxo). }
    pose proof (pis_snoc (ms_segs B) m4 _ o true num kg yg capg (n + 1) (map snd ms) (map fst ms) Di tv (zb kname)
      [(res, Z.of_nat (length kname) + 1)] Dw HO4 HNmem Hkey HND5 HAp5) as HO5.
    pose proof (ps_obj_node (ms_segs B) m4 (lin ((res, Z.of_nat (length kname) + 1) :: Lamg)) o
      (ms ++ [(zb kname, tv)]) (Di ++ [(res, Z.of_nat (length kname) + 1)] ++ Dw) num kg yg (n + 1) capg) as HOB.
    rewrite !map_app in HOB. cbn [map fst snd] in HOB.
    exact (HOB HO5 ltac:(rewrite length_app; cbn [length]; lia)).
Qed.

End OK.
