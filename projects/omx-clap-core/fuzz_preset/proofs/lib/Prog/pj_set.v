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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import pj_get_c pj_free_c fuzz_strdup_c memcpy_c
  memset_c grow_c pj_set_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import pj_set_tail pj_set_post pj_set_hit pj_set_grow.
Import YM05.
Import ListNotations.
Local Open Scope Z_scope.

Section P.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable RF : ResForm.

Local Notation getr := YK11.getr.

Lemma m_ro_word : ms_segs B = rsegs -> forall x : word, ~ in_img B (bv_unsigned x) -> ro_addr rsegs x = false.
Proof.
  intros HSEG x Hn. unfold ro_addr. destruct (find_segment rsegs (bv_unsigned x) 1) as [seg|] eqn:Fs; [|reflexivity].
  exfalso. apply Hn. apply (g_seg_img B HSEG (bv_unsigned x) seg). rewrite HSEG. exact Fs.
Qed.

Theorem pj_set_holds : YL01.AllocExtra B (aa_MR API) -> pj_get_contract -> memcpy_contract -> memset_contract ->
  pj_free_contract B API RF -> grow_contract B API RF -> fuzz_strdup_contract B API RF -> pj_set_contract B API RF.
Proof.
  intros AX HGET HMC HMS HFREE HGROW HSD. unfold pj_set_contract.
  intros L A regs mem md Lam peak cnt fail b o k w ms tv D Dw num str kids keys n cap kname slack dd HE HL Hres
    G10 G11 G12 Ho0 HN HH Hcap HPo Hw0 HNw HPw HDD HWD HAw Hdo Hdt HKB Hkn Hsl Hcs HKD HDJ Hcnt Hroom.
  pose proof HE as HE0. pose proof HDJ as HDJ0.
  destruct HE as (HSEG & Htp & Herrno & Hgot & Hguard & Hpre & Hsp47 & Hglob & Hfrm & HRD).
  pose proof Hpre as (HMR & HWF & Hbd & Hra & Hsp16 & Hspc & Hsp63 & Hstk & Htpr & Herr & Haux).
  pose proof alloc_ceiling_value as Hceil.
  pose proof (t_sk dd) as (Kf & Kg & Ks & K96 & Kf0).
  unfold strtod_c.STRTOD_GLOBALS_TOP in Hglob.
  cbn [Frame.disjoint_from] in HDJ.
  pose proof (g_img B HSEG) as HIL.
  assert (Herr4 : errno_addr B + 4 <= spZ regs - PJ_SET_K dd) by (rewrite Herrno; unfold strtod_c.STRTOD_ERRNO; lia).
  assert (HDL : forall a k0, In (a, k0) D -> In (a, k0) Lam)
    by (intros a k0 Hb; exact (pis_node_lblk (ms_segs B) (JObj ms) mem (lin Lam) o D HN (a, k0) Hb)).
  pose proof HPo as (HPo1 & HPo2 & Ho3). pose proof HPw as (HPw1 & HPw2 & Hw3).
  pose proof (pis_node_rw (ms_segs B) mem (lin Lam) o (JObj ms) D HN) as (Ho8 & (Ho0' & Ho1' & _)).
  pose proof (pis_node_rw (ms_segs B) mem (lin Lam) w tv Dw HNw) as (Hw8 & (Hw0' & Hw1' & _)).
  pose proof (kb_stk B API HIL _ L A regs mem md Hpre ltac:(lia)) as SSTK.
  destruct (Frame.stk_split _ mem _ (spZ regs - 96) (spZ regs) SSTK ltac:(lia)) as [_ SSTK96].
  assert (HCB : pj_cbytes rsegs mem k (zb kname)).
  { pose proof HKB as HKB'.
    replace (kname ++ Z_to_bv 8 0 :: slack) with ((kname ++ [Z_to_bv 8 0]) ++ slack) in HKB'
      by (rewrite <- app_assoc; reflexivity).
    split; [exact (g_zb_pos kname Hkn)|]. rewrite map_app, g_zb_map. cbn [map]. rewrite <- HSEG.
    exact (proj1 (proj1 (bytes_at_app _ _ _ _ _) HKB')). }
  assert (Hzl : Z.of_nat (length (zb kname)) = Z.of_nat (length kname)) by (unfold zb; rewrite length_map; reflexivity).
  eapply (kb_run B regs (Z_to_bv 64 PJ_SET) mem md (K_sa regs mem o k w kids ms (zb kname))).
  { exact (proj1 (kb_md B API _ _ _ _ HMR)). }
  { exact (proj2 (kb_md B API _ _ _ _ HMR)). }
  { apply (run_sa B HGET regs mem (spZ regs - 96) o k w (lin Lam) ms D num str kids keys n cap (zb kname) HSEG).
    - rewrite <- HSEG. exact (proj1 HRD).
    - exact G10.
    - exact G11.
    - exact G12.
    - exact Ho0.
    - rewrite <- HSEG. exact HN.
    - rewrite <- HSEG. exact HH.
    - exact HCB.
    - intros a nn Hin. unfold lin in Hin.
      destruct (ledger_block_range B API L A mem md Lam peak cnt fail a nn HMR HL Hin) as (R1 & R2 & R3).
      pose proof (ledger_block_aligned B API L A mem md Lam peak cnt fail a nn HMR HL Hin) as Hal.
      split; [lia|]. split; [lia|]. split; [lia|]. cbn [disjoint_from]. lia.
    - exact Hsp16.
    - rewrite <- HSEG. exact SSTK96.
    - lia.
    - cbn [disjoint_from]. rewrite Hzl. lia.
    - intros x Hx. pose proof (bv_unsigned_in_range 64 x) as Hxr. unfold bv_modulus in Hxr.
      apply (m_ro_word HSEG x). destruct Hx as [Hx|((a & k0) & Hb & Hx)].
      + destruct (Ho3 (bv_unsigned x - o) ltac:(lia)) as (_ & _ & _ & O4).
        replace (o + (bv_unsigned x - o)) with (bv_unsigned x) in O4 by lia. exact O4.
      + unfold pj_holds in Hx; cbn [fst snd] in Hx.
        replace (bv_unsigned x) with (a + (bv_unsigned x - a)) by lia.
        exact (ledger_block_not_img B L A mem Lam peak cnt fail a k0 (bv_unsigned x - a) HL (HDL a k0 Hb) ltac:(lia)).
    - intros a Ha. unfold wa. rewrite <- HSEG. apply (g_ro_low B HIL). lia. }
  intros R pc' m1 regs1 HK Hg1.
  destruct HK as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & junk & MU & WM & RS & FR & CASES).
  rewrite <- HSEG in WM, FR.
  replace (spZ regs + -96) with (spZ regs - 96) in MU by lia.
  replace (spZ regs + -48) with (spZ regs - 48) in FR by lia.
  assert (HR1 : rpost B API (PJ_SET_K dd) L A regs mem md (pj_set_writes o w D Dw) (freed (D ++ Dw)) L A regs m1 md).
  { apply (rp_A B API HIL (PJ_SET_K dd) L A regs mem md _ _ L A mem md m1 [(spZ regs - 96, spZ regs)] HMR ltac:(lia)
      (rp_refl B API _ L A regs mem md _ _ Hpre) MU WM).
    - intros x Hx Ho _. exfalso. pose proof (g_nout1 _ _ _ Ho). lia.
    - intros x Ho. pose proof (g_nout1 _ _ _ Ho) as Hx. split; [left; lia|].
      intros Hown. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HMR Hown). lia. }
  pose proof HR1 as (HMR1 & _).
  assert (HL1 : ledger B L A m1 Lam peak cnt fail).
  { apply (g_ledger_munch B API L A mem md m1 Lam peak cnt fail _ HMR HL MU).
    intros x Ho. pose proof (g_nout1 _ _ _ Ho) as Hx. split.
    - unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL. lia.
    - intros a kk Hin Ha.
      destruct (ledger_block_range B API L A mem md Lam peak cnt fail a kk HMR HL Hin) as (R1 & R2 & _).
      pose proof HL as (_ & _ & _ & _ & _ & HF). rewrite Forall_forall in HF.
      destruct (HF _ Hin) as (Hkk & _). cbn [fst snd] in Hkk. lia. }
  assert (Hrd1 : rd_cells B m1).
  { split.
    - apply (MemNorm.ro_agree_same _ mem m1 (proj1 HRD)). rewrite HSEG. exact RS.
    - destruct (YL01.ax_statics AX L A m1 md HMR1) as (Hgg & (gg & _ & Hggw) & _).
      split; [exact Hgg | exists gg; exact Hggw]. }
  destruct (g_vplace0 B API L A mem md Lam peak cnt fail (spZ regs) o HMR HL ltac:(lia) HPo1) as (ro & rko & HVo).
  destruct (g_vplace0 B API L A mem md Lam peak cnt fail (spZ regs) w HMR HL ltac:(lia) HPw1) as (rw & rkw & HVw).
  destruct (g_lo2 (spZ regs) o w (fun lo => st_init_done A = false -> auxv_pre B (ly_sec L) lo mem) Haux
    (fun Hs => HPo2 Hs) (fun Hs => HPw2 Hs)) as (lo & Hlo & Hax & Hlo_o & Hlo_w).
  assert (HElo : forall x, pj_set_writes o w D Dw x -> x < lo).
  { intros x [Hx|[Hx|[(a & kk & Hin & Hx)|Hx]]].
    - destruct (Z_le_gt_dec (spZ regs) o); [pose proof (Hlo_o ltac:(lia)); lia | lia].
    - destruct (Z_le_gt_dec (spZ regs) w); [pose proof (Hlo_w ltac:(lia)); lia | lia].
    - assert (HinL : In (a, kk) Lam).
      { apply in_app_or in Hin. destruct Hin as [Hin|Hin]; [exact (HDL a kk Hin)|].
        exact (pis_node_lblk (ms_segs B) tv mem (lin Lam) w Dw HNw (a, kk) Hin). }
      destruct (ledger_block_range B API L A mem md Lam peak cnt fail a kk HMR HL HinL) as (R1 & R2 & _). lia.
    - unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Hx. lia. }
  assert (G2a : getr regs1 2 = Z_to_bv 64 (spZ regs + -48)).
  { destruct CASES as [(_ & ER & _)|(i & vi & _ & _ & ER & _)]; subst R; rewrite Hg1; reflexivity. }
  assert (G2 : getr regs1 2 = Z_to_bv 64 (spZ regs - 48)) by (rewrite G2a; f_equal; lia).
  destruct CASES as [(Hnin & ER & EP)|(i & vi & Hi & Hfirst & ER & EP)]; subst R pc'.
  -
    assert (G1 : getr regs1 1 = Z_to_bv 64 PS_GROW_RET) by (rewrite Hg1; reflexivity).
    assert (G10' : getr regs1 10 = Z_to_bv 64 o) by (rewrite Hg1; reflexivity).
    assert (G8 : getr regs1 8 = Z_to_bv 64 w) by (rewrite Hg1; reflexivity).
    assert (G9 : getr regs1 9 = Z_to_bv 64 o) by (rewrite Hg1; reflexivity).
    assert (G18 : getr regs1 18 = Z_to_bv 64 k) by (rewrite Hg1; reflexivity).
    assert (Gk : forall r, r = 3 \/ r = 4 \/ 20 <= r <= 27 -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
    { intros r Hr.
      assert (Hc : r = 3 \/ r = 4 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
      destruct Hc as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]; rewrite Hg1; reflexivity. }
    exact (miss_arm B API RF HFREE HSD HGROW AX HMC HMS L A regs mem md Lam peak cnt fail b o k w ms tv D Dw num str
      kids keys n cap kname slack dd lo m1 regs1 junk ro rko rw rkw HE0 HL Hres Ho0 HN HH Hcap HPo Hw0 HNw HPw HDD HWD
      HAw Hdo Hdt HKB Hkn Hsl Hcs HKD HDJ0 Hcnt Hroom HVo HVw Hlo Hax HElo Hlo_w HR1 MU WM HL1 Hrd1 FR G1 G2 G10' G8 G9
      G18 Gk Hnin).
  -
    assert (G1 : getr regs1 1 = Z_to_bv 64 PS_FREE_RET) by (rewrite Hg1; reflexivity).
    assert (G10' : getr regs1 10 = Z_to_bv 64 (kids + 56 * Z.of_nat i)) by (rewrite Hg1; reflexivity).
    assert (G8 : getr regs1 8 = Z_to_bv 64 w) by (rewrite Hg1; reflexivity).
    assert (G19 : getr regs1 19 = Z_to_bv 64 (kids + 56 * Z.of_nat i)) by (rewrite Hg1; reflexivity).
    assert (Gk : forall r, r = 3 \/ r = 4 \/ 20 <= r <= 27 -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
    { intros r Hr.
      assert (Hc : r = 3 \/ r = 4 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
      destruct Hc as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]; rewrite Hg1; reflexivity. }
    exact (hit_arm B API RF HFREE AX HMC HMS L A regs mem md Lam peak cnt fail b o k w ms tv D Dw num str kids keys n cap
      kname dd lo m1 regs1 junk ro rko rw rkw i vi HE0 HL Hres HN HH Hcap HPo HNw HPw HDD HWD HAw Hdo HDJ0 HVo HVw Hlo
      Hax HElo HR1 MU WM HL1 Hrd1 FR G1 G2 G10' G8 G19 Gk Hi Hfirst).
Qed.

End P.
