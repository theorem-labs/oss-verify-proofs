From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YL01 YO0x YO0u.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import Contract Img0 KindBGlue.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require MemNorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import Ledger PjStruct ReaderRes parse_items_shape.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import pj_set_runs pj_set_shape pj_set_sh.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog.CF Require Import pj_set_kb.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import memcpy_c memset_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog.CF Require Import pj_free_c pj_set_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog.CF Require Import pj_set_tail pj_set_post.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog.CF Require Import CFS ContractCF KindBGlueCF FrameCF ReaderResCF.
Import YM05.
Import ListNotations.
Local Open Scope Z_scope.

Section H.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Hypothesis HFREE : pj_free_contract B API F.
Hypothesis AX : YL01.AllocExtra B (aa_MR API).
Hypothesis HMC : memcpy_contract.
Hypothesis HMS : memset_contract.

Local Notation getr := YK11.getr.

Lemma hit_arm : forall L A regs mem md Lam peak cnt fail b o k w ms tv D Dw num str kids keys n cap kname (dd : nat)
    lo m1 regs1 junk ro rko rw rkw i vi,
  reader_env B API (PJ_SET_K dd) L A regs mem md ->
  ledger B L A mem Lam peak cnt fail -> rf_ok F A b ->
  pj_node (ms_segs B) mem (lin Lam) o (JObj ms) D -> pj_hdr (ms_segs B) mem o 6 num str kids keys n cap ->
  cap <= 2 ^ 54 -> rplace B L A Lam regs mem o ->
  pj_node (ms_segs B) mem (lin Lam) w tv Dw -> rplace B L A Lam regs mem w ->
  (forall bk, In bk Dw -> ~ In bk D) -> (forall x, w <= x < w + 56 -> ~ pj_foot o D x) -> pj_apart Dw o ->
  (depth (JObj ms) <= S dd)%nat ->
  Frame.disjoint_from [(o, o + 56); (w, w + 56); (k, k + Z.of_nat (length kname) + 1)]
    (spZ regs - PJ_SET_K dd) (PJ_SET_K dd) ->
  vplace L A Lam (spZ regs) o ro rko -> vplace L A Lam (spZ regs) w rw rkw ->
  spZ regs <= lo -> (st_init_done A = false -> auxv_pre B (ly_sec L) lo mem) ->
  (forall x, pj_set_writes o w D Dw x -> x < lo) ->
  rpost B API (PJ_SET_K dd) L A regs mem md (pj_set_writes o w D Dw) (freed (D ++ Dw)) L A regs m1 md ->
  Frame.munch [(spZ regs - 96, spZ regs)] mem m1 -> Frame.wmono (ms_segs B) mem m1 ->
  ledger B L A m1 Lam peak cnt fail -> rd_cells B m1 ->
  rw_cells (ms_segs B) m1 (spZ regs - 48)
    [CB 8 junk; C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)] ->
  getr regs1 1 = Z_to_bv 64 PS_FREE_RET -> getr regs1 2 = Z_to_bv 64 (spZ regs - 48) ->
  getr regs1 10 = Z_to_bv 64 (kids + 56 * Z.of_nat i) -> getr regs1 8 = Z_to_bv 64 w ->
  getr regs1 19 = Z_to_bv 64 (kids + 56 * Z.of_nat i) ->
  (forall r, r = 3 \/ r = 4 \/ 20 <= r <= 27 -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
  nth_error ms i = Some (zb kname, vi) ->
  (forall j nm u, (j < i)%nat -> nth_error ms j = Some (nm, u) -> nm <> zb kname) ->
  SR (ms_segs B) (mkCfg (YK11.mkst regs1 (Z_to_bv 64 PS_PJ_FREE) m1 (YK11.seg_rom (ms_segs B))) md)
    (set_post B API F dd L A regs mem md Lam peak cnt fail b o w ms tv D Dw kids keys n cap kname).
Proof.
  intros L A regs mem md Lam peak cnt fail b o k w ms tv D Dw num str kids keys n cap kname dd lo m1 regs1 junk
    ro rko rw rkw i vi HE HL Hres HN HH Hcap HPo HNw HPw HDD HWD HAw Hdo HDJ HVo HVw Hlo Hax HElo HR1 HMU1 HWM1
    HL1 Hrd1 FR G1 G2 G10 G8 G19 Gk Hi Hfirst.
  pose proof HE as HE0.
  destruct HE as (HSEG & Htp & Herrno & Hgot & Hguard & Hpre & Hsp47 & Hglob & Hfrm & HRD).
  pose proof Hpre as (HMR & HWF & Hbd & Hra & Hsp16 & Hspc & Hsp63 & Hstk & Htpr & Herr & Haux).
  pose proof alloc_ceiling_value as Hceil.
  pose proof (t_sk dd) as (Kf & Kg & Ks & K96 & Kf0).
  unfold strtod_c.STRTOD_GLOBALS_TOP in Hglob.
  cbn [Frame.disjoint_from] in HDJ.
  pose proof HR1 as (HMR1 & _).
  assert (Hs1 : spZ regs1 = spZ regs - 48) by (unfold spZ at 1; rewrite G2, unsigned_lit by lia; reflexivity).
  destruct (ps_node_open (ms_segs B) mem (lin Lam) o ms D num str kids keys n cap HN HH Hcap) as (Di0 & ED & Es & En & HO).
  pose proof HO as (_ & _ & _ & HSL & _ & _).
  destruct HSL as (_ & (Hnc & _) & _ & Hcp).
  assert (Hil : (i < length ms)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
  assert (Hicap : Z.of_nat i < cap) by lia.
  destruct (Hcp ltac:(lia)) as (Hkid & _). unfold lin in Hkid.
  assert (HkD : In (kids, 56 * cap) D).
  { rewrite ED. apply in_or_app. left. rewrite ps_slots_eq. rewrite (proj2 (Z.eqb_neq cap 0)) by lia. left. reflexivity. }
  destruct (ledger_block_range B API L A mem md Lam peak cnt fail kids (56 * cap) HMR HL Hkid) as (Kr1 & Kr2 & Kr3).
  destruct (sh_hit (ms_segs B) mem Lam o ms D num str kids keys n cap i (zb kname) vi w tv Dw HN HH Hcap Hi HNw HDD HAw)
    as (Du & Dr & HPD & HNz & HKs).
  assert (Hdv : (depth vi <= dd)%nat).
  { pose proof (ps_depth_items ms dd Hdo) as HF. rewrite Forall_forall in HF. apply HF. apply in_map_iff.
    exists (zb kname, vi). split; [reflexivity | exact (nth_error_In ms i Hi)]. }
  assert (HDuD : forall bk, In bk Du -> In bk D)
    by (intros bk Hb; apply (Permutation_in _ (Permutation_sym HPD)); apply in_or_app; left; exact Hb).
  assert (HDL : forall a k0, In (a, k0) D -> In (a, k0) Lam)
    by (intros a k0 Hb; exact (pis_node_lblk (ms_segs B) (JObj ms) mem (lin Lam) o D HN (a, k0) Hb)).
  assert (HDwL : forall a k0, In (a, k0) Dw -> In (a, k0) Lam)
    by (intros a k0 Hb; exact (pis_node_lblk (ms_segs B) tv mem (lin Lam) w Dw HNw (a, k0) Hb)).
  assert (HDuL : forall a k0, In (a, k0) Du -> In (a, k0) Lam) by (intros a k0 Hb; exact (HDL a k0 (HDuD _ Hb))).
  pose proof (pis_node_apart (ms_segs B) mem (lin Lam) _ vi Du HNz) as HADz.
  pose proof (pis_node_apart (ms_segs B) mem (lin Lam) o (JObj ms) D HN) as HAD.
  pose proof (pis_node_apart (ms_segs B) mem (lin Lam) w tv Dw HNw) as HADw.
  assert (HADuo : pj_apart Du o) by (intros bk x Hb; exact (HAD bk x (HDuD _ Hb))).
  assert (HADuw : pj_apart Du w).
  { intros bk x Hb Hx Hxw. apply (HWD x Hxw). right. exists bk. split; [exact (HDuD _ Hb) | exact Hx]. }
  pose proof (pis_node_rw (ms_segs B) mem (lin Lam) o (JObj ms) D HN) as (Ho8 & (Ho0 & Ho1 & _)).
  pose proof (pis_node_rw (ms_segs B) mem (lin Lam) w tv Dw HNw) as (Hw8 & HSw).
  pose proof HSw as (Hw0' & Hw1' & _).
  assert (HZK : forall a k0 y, In (a, k0) Lam -> (a, k0) <> (kids, 56 * cap) -> a <= y < a + k0 ->
      ~ (kids + 56 * Z.of_nat i <= y < kids + 56 * Z.of_nat i + 56)).
  { intros a k0 y Hin Hne Hy Hz.
    destruct (g_lam_disj B API L A mem md Lam peak cnt fail a k0 kids (56 * cap) HMR HL Hin Hkid Hne); lia. }
  assert (HNz1 : pj_node (ms_segs B) m1 (lin Lam) (kids + 56 * Z.of_nat i) vi Du).
  { apply (pj_node_munch (ms_segs B) [(spZ regs - 96, spZ regs)] mem (lin Lam) m1 (lin Lam) _ vi Du HNz);
      [intros a k0 Hb; exact (HDuL a k0 Hb) | exact HMU1 |].
    intros y Hy. cbn [Frame.outside]. split; [|exact I].
    destruct Hy as [Hy|((a & k0) & Hb & Hy)]; [lia|].
    unfold pj_holds in Hy; cbn [fst snd] in Hy.
    destruct (ledger_block_range B API L A mem md Lam peak cnt fail a k0 HMR HL (HDuL a k0 Hb)) as (R1 & R2 & _). lia. }
  pose proof (pj_fd_mono (ms_segs B) m1 (lin Lam) (depth vi) dd _ Du Hdv
    (pj_node_fd (ms_segs B) vi m1 (lin Lam) _ Du HNz1)) as Hfd.
  destruct (g_vplace0 B API L A m1 md Lam peak cnt fail (spZ regs) (kids + 56 * Z.of_nat i) HMR1 HL1 ltac:(lia))
    as (rz & rkz & HVz).
  { right; right. exists kids, (56 * cap). split; [exact Hkid | lia]. }
  pose proof (g_rplace_blk B API HSEG Herrno L A Lam regs1 m1 md peak cnt fail (kids + 56 * Z.of_nat i) kids (56 * cap)
    HMR1 HL1 Hkid ltac:(lia) ltac:(lia) ltac:(lia)) as Hpl.
  pose proof (g_vloc_nf B API L A Lam m1 md peak cnt fail (spZ regs) (kids + 56 * Z.of_nat i) rz rkz Du (proj1 HVz)
    HMR1 HL1 ltac:(lia) HADz HDuL) as Hgz.
  pose proof (g_vloc_nf B API L A Lam m1 md peak cnt fail (spZ regs) w rw rkw Du (proj1 HVw)
    HMR1 HL1 ltac:(lia) HADuw HDuL) as Hgw.
  pose proof (g_vloc_nf B API L A Lam m1 md peak cnt fail (spZ regs) o ro rko Du (proj1 HVo)
    HMR1 HL1 ltac:(lia) HADuo HDuL) as Hgo.
  assert (Hwx : forall x, w <= x < w + 56 -> ~ pj_free_writes (kids + 56 * Z.of_nat i) Du x /\
      pj_set_writes o w D Dw x /\ ~ in_img B x /\ ~ static_owned B x /\ ~ alloc_statics x /\
      ~ (errno_addr B <= x < errno_addr B + 4)).
  { intros x Hx. pose proof HPw as (_ & _ & Hw3). destruct (Hw3 (x - w) ltac:(lia)) as (W1 & W2 & W3 & W4).
    replace (w + (x - w)) with x in W1, W2, W3, W4 by lia.
    split.
    - intros (_ & [Hz|[Hb|Hs]]).
      + apply (HWD x Hx). right. exists (kids, 56 * cap). split; [exact HkD | unfold pj_holds; cbn [fst snd]; lia].
      + exact (g_vloc_nblk B API L A Lam m1 md peak cnt fail (spZ regs) w rw rkw Du (proj1 HVw) HMR1 HL1 ltac:(lia)
          HADuw HDuL x Hx Hb).
      + exact (W2 Hs).
    - split; [right; left; exact Hx|]. split; [exact W4|]. split; [intros Hs; exact (W1 (or_intror Hs))|].
      split; [exact W2 | exact W3]. }
  assert (HDzw : w + 56 <= kids + 56 * Z.of_nat i \/ kids + 56 * Z.of_nat i + 56 <= w).
  { destruct (Z_le_gt_dec (w + 56) (kids + 56 * Z.of_nat i)) as [h|h]; [left; exact h|].
    destruct (Z_le_gt_dec (kids + 56 * Z.of_nat i + 56) w) as [h'|h']; [right; exact h'|].
    exfalso. apply (HWD (Z.max w (kids + 56 * Z.of_nat i)) ltac:(lia)). right. exists (kids, 56 * cap).
    split; [exact HkD | unfold pj_holds; cbn [fst snd]; lia]. }
  assert (Hwstk : stk (ms_segs B) m1 w (w + 56)).
  { apply (pj_stk_eq (ms_segs B) mem m1 w (w + 56) HSw). intros x Hx. apply HMU1. cbn [Frame.outside].
    split; [lia | exact I]. }
  assert (HWE : forall x, pj_free_writes (kids + 56 * Z.of_nat i) Du x -> pj_set_writes o w D Dw x).
  { intros x (_ & [Hx|[(a & k0 & Hb & Hx)|Hx]]).
    - right; right; left. exists kids, (56 * cap). split; [apply in_or_app; left; exact HkD | lia].
    - right; right; left. exists a, k0. split; [apply in_or_app; left; exact (HDuD _ Hb) | exact Hx].
    - right; right; right; exact Hx. }
  assert (HWG : forall a n0, freed Du a n0 -> freed (D ++ Dw) a n0)
    by (intros a n0 Hf; apply in_or_app; left; exact (HDuD _ Hf)).
  assert (HGE : forall p n0 i0, In (p, n0) (user_blocks A) -> 0 <= i0 < n0 -> freed (D ++ Dw) (ptr_addr L p) n0 ->
      pj_set_writes o w D Dw (ptr_addr L p + i0))
    by (intros p n0 i0 _ Hi0 Hf; exact (st_gone _ _ _ o w D Dw Hi0 Hf)).
  assert (HDz : Frame.disjoint_from [(kids + 56 * Z.of_nat i, kids + 56 * Z.of_nat i + 56)]
      (spZ regs - PJ_SET_K dd) (PJ_SET_K dd)) by (cbn [Frame.disjoint_from]; lia).
  assert (HDw : Frame.disjoint_from [(w, w + 56)] (spZ regs - PJ_SET_K dd) (PJ_SET_K dd))
    by (cbn [Frame.disjoint_from]; lia).
  change (Z_to_bv 64 PS_PJ_FREE) with (Z_to_bv 64 PJ_FREE).
  apply (tail_hit B API F HFREE AX HMC HMS L A regs mem md dd (pj_set_writes o w D Dw) (freed (D ++ Dw)) L A m1 md
    regs1 Lam peak cnt fail b (kids + 56 * Z.of_nat i) Du w junk lo rz rkz rw rkw _ HE0 HR1 Hlo Hax HElo HGE
    G1 G2 G10 G8 G19 Gk FR HL1 Hres Hrd1 ltac:(lia) Hfd Hpl HDuL HDz HWE HWG (proj1 HVz) Hgz (proj1 HVw) Hgw Hwx
    HDw HDzw Hwstk).
  intros L2 A2 regs2 mem2 md2 Lam2 regs3 mem3 bs HR3 HR2 HMU3 HWM3 Hbl WB1 ZB3 WZ HZW Hrd3 G3 HL3 HRF HP2.
  assert (HNDL : List.NoDup (map fst Lam)).
  { pose proof HL as (_ & _ & _ & _ & HND & _). first [exact HND | apply NoDup_ListNoDup; exact HND]. }
  assert (HND1 : List.NoDup (D ++ Dw)).
  { apply NoDup_ListNoDup. apply pis_nodup_app;
      [exact (sh_node_nodup (ms_segs B) mem (lin Lam) o (JObj ms) D HN)
      | exact (sh_node_nodup (ms_segs B) mem (lin Lam) w tv Dw HNw)
      | intros a Ha Hw'; exact (HDD a Hw' Ha)]. }
  assert (HIN1 : incl (D ++ Dw) Lam).
  { intros (a & k0) Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [exact (HDL a k0 Hb) | exact (HDwL a k0 Hb)]. }
  destruct (g_perm_sub (D ++ Dw) Lam HND1 HIN1 (List.NoDup_map_inv _ _ HNDL)) as (Lr & HLr).
  assert (HPL : Permutation Lam (D ++ Dw ++ Lr)) by (rewrite app_assoc; exact HLr).
  assert (HPL2 : Permutation Lam2 (Dr ++ Dw ++ Lr)).
  { apply (Permutation_app_inv_l Du). apply (Permutation_trans (Permutation_sym HP2)).
    apply (Permutation_trans HPL). apply (Permutation_trans (Permutation_app_tail (Dw ++ Lr) HPD)).
    rewrite <- app_assoc. apply Permutation_refl. }
  assert (HS1 : forall y, 0 <= y < 2 ^ 64 -> (y < spZ regs - 96 \/ spZ regs <= y) -> pis_same (ms_segs B) mem m1 y).
  { intros y Hy Hy'. apply (g_same_munch (ms_segs B) _ mem m1 y HMU1 HWM1 Hy). cbn [Frame.outside].
    split; [lia | exact I]. }
  assert (HS3 : forall y, 0 <= y < 2 ^ 64 -> ~ (kids + 56 * Z.of_nat i <= y < kids + 56 * Z.of_nat i + 56) ->
      ~ (w <= y < w + 56) -> pis_same (ms_segs B) mem2 mem3 y).
  { intros y Hy H1 H2. apply (g_same_munch (ms_segs B) _ mem2 mem3 y HMU3 HWM3 Hy). cbn [Frame.outside].
    refine (conj _ (conj _ I)); lia. }
  assert (HNW : forall a k0 y, In (a, k0) Lam -> ~ In (a, k0) Du -> a <= y < a + k0 ->
      ~ (kids + 56 * Z.of_nat i <= y < kids + 56 * Z.of_nat i + 56) ->
      ~ pj_free_writes (kids + 56 * Z.of_nat i) Du y).
  { intros a k0 y Hin Hn Hy Hz (_ & [Hx|[(a' & k' & Hin' & Hx)|Hx]]).
    - exact (Hz Hx).
    - assert (Hne : (a, k0) <> (a', k')) by (intros E; rewrite E in Hn; exact (Hn Hin')).
      destruct (g_lam_disj B API L A mem md Lam peak cnt fail a k0 a' k' HMR HL Hin (HDuL a' k' Hin') Hne); lia.
    - apply (ledger_block_not_img B L A mem Lam peak cnt fail a k0 (y - a) HL Hin ltac:(lia)).
      replace (a + (y - a)) with y by lia. exact (g_img_consts B HSEG Herrno y (or_introl Hx)). }
  assert (HSB : forall a k0 y, In (a, k0) Lam -> ~ In (a, k0) Du -> a <= y < a + k0 ->
      ~ pj_free_writes (kids + 56 * Z.of_nat i) Du y -> pis_same (ms_segs B) m1 mem2 y).
  { intros a k0 y Hin Hn Hy HnW.
    pose proof HL1 as (_ & _ & _ & _ & _ & HF). rewrite Forall_forall in HF.
    destruct (HF _ Hin) as (_ & Hb & _). cbn [fst snd] in Hb.
    apply (rp_same_blk B API _ _ _ _ _ _ _ _ _ _ _ _ _ (a - 16) (k0 + 16) y HR2 Hb); [| lia | exact HnW].
    unfold freed. replace (a - 16 + 16) with a by lia. replace (k0 + 16 - 16) with k0 by lia. exact Hn. }
  destruct (HKs mem3 Lam2) as (Do & HPDo & HNo).
  - intros y Hy. pose proof HPo as (_ & _ & Ho3). destruct (Ho3 (y - o) ltac:(lia)) as (O1 & O2 & O3 & O4).
    replace (o + (y - o)) with y in O1, O2, O3, O4 by lia.
    assert (Hzy : ~ (kids + 56 * Z.of_nat i <= y < kids + 56 * Z.of_nat i + 56)).
    { intros Hz. exact (HAD (kids, 56 * cap) y HkD ltac:(unfold pj_holds; cbn [fst snd]; lia) Hy). }
    apply (g_same_trans (ms_segs B) mem m1 mem3 y); [apply HS1; lia|].
    apply (g_same_trans (ms_segs B) m1 mem2 mem3 y).
    + apply (vloc_same B API L A Lam (spZ regs) o ro rko (PJ_FREE_K dd) regs1 m1 md
        (pj_free_writes (kids + 56 * Z.of_nat i) Du) (freed Du) L2 A2 regs2 mem2 md2 y (proj1 HVo) HR2 Hgo);
        [lia | lia | exact O3 | exact Hy |].
      intros (_ & [Hx|[Hx|Hx]]); [exact (Hzy Hx) | | exact (O2 Hx)].
      exact (g_vloc_nblk B API L A Lam m1 md peak cnt fail (spZ regs) o ro rko Du (proj1 HVo) HMR1 HL1 ltac:(lia)
        HADuo HDuL y Hy Hx).
    + apply HS3; [lia | exact Hzy | intros Hw; exact (HWD y Hw (or_introl Hy))].
  - intros (a & k0) y Hb Hn Hy Hor. unfold pj_holds in Hy; cbn [fst snd] in Hy.
    pose proof (HDL a k0 Hb) as HinL.
    destruct (ledger_block_range B API L A mem md Lam peak cnt fail a k0 HMR HL HinL) as (R1 & R2 & _).
    assert (Hzy : ~ (kids + 56 * Z.of_nat i <= y < kids + 56 * Z.of_nat i + 56))
      by (destruct Hor as [Hne|Hz]; [exact (HZK a k0 y HinL Hne Hy) | exact Hz]).
    apply (g_same_trans (ms_segs B) mem m1 mem3 y); [apply HS1; lia|].
    apply (g_same_trans (ms_segs B) m1 mem2 mem3 y); [exact (HSB a k0 y HinL Hn Hy (HNW a k0 y HinL Hn Hy Hzy))|].
    apply HS3; [lia | exact Hzy|]. intros Hw. apply (HWD y Hw). right. exists (a, k0).
    split; [exact Hb | unfold pj_holds; cbn [fst snd]; lia].
  - intros y ((a & k0) & Hb & Hy). unfold pj_holds in Hy; cbn [fst snd] in Hy.
    pose proof (HDwL a k0 Hb) as HinL.
    assert (Hn : ~ In (a, k0) Du) by (intros H; exact (HDD _ Hb (HDuD _ H))).
    assert (Hne : (a, k0) <> (kids, 56 * cap)) by (intros E; rewrite E in Hb; exact (HDD _ Hb HkD)).
    destruct (ledger_block_range B API L A mem md Lam peak cnt fail a k0 HMR HL HinL) as (R1 & R2 & _).
    pose proof (HZK a k0 y HinL Hne Hy) as Hzy.
    apply (g_same_trans (ms_segs B) mem m1 mem3 y); [apply HS1; lia|].
    apply (g_same_trans (ms_segs B) m1 mem2 mem3 y); [exact (HSB a k0 y HinL Hn Hy (HNW a k0 y HinL Hn Hy Hzy))|].
    apply HS3; [lia | exact Hzy|]. intros Hw. exact (HADw (a, k0) y Hb ltac:(unfold pj_holds; cbn [fst snd]; lia) Hw).
  - intros j Hj.
    rewrite <- (g_bytes_eq B m1 mem3 w (kids + 56 * Z.of_nat i) bs WB1 ZB3 j ltac:(rewrite Hbl; simpl; lia)).
    exact (proj1 (HS1 (w + j) ltac:(lia) ltac:(lia))).
  - intros j Hj. exact (HZW j Hj).
  - intros a k0 Hb Hn. unfold lin. pose proof (Permutation_in _ HP2 (HDL a k0 Hb)) as H1.
    apply in_app_or in H1. destruct H1 as [H1|H1]; [exact (False_ind _ (Hn H1)) | exact H1].
  - intros a k0 Hb. unfold lin. pose proof (Permutation_in _ HP2 (HDwL a k0 Hb)) as H1.
    apply in_app_or in H1. destruct H1 as [H1|H1]; [exact (False_ind _ (HDD _ Hb (HDuD _ H1))) | exact H1].
  - intros (a & k0) y Hb Hy Hz. unfold pj_holds in Hy; cbn [fst snd] in Hy.
    assert (Hne : (a, k0) <> (kids, 56 * cap)) by (intros E; rewrite E in Hb; exact (HDD _ Hb HkD)).
    exact (HZK a k0 y (HDwL a k0 Hb) Hne Hy Hz).
  - unfold set_post.
    exists L2, A2, regs3, mem3, md2, Lam2, peak, fail, 0, 0%nat, Lr, Do.
    split; [reflexivity|]. split; [exact HR3|]. split; [exact Hrd3|]. split; [exact G3|].
    split; [replace (cnt + Z.of_nat 0) with cnt by lia; exact HL3|].
    split; [unfold fail_after; split; intros; lia|].
    split; [exact HPL|].
    split.
    { apply (Permutation_trans HPL2). rewrite app_assoc. apply Permutation_app_tail. apply Permutation_sym. exact HPDo. }
    split.
    { split; [split; [exact Hw8|] |].
      - replace (w + 56) with (w + Z.of_nat (cells_size [CB 56 (repeat (Z_to_bv 8 0) 56)])) by reflexivity.
        exact (g_stk_rw B mem3 w _ WZ).
      - pose proof (proj2 (proj1 WZ)) as HB. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB. exact HB. }
    split; [intros _; reflexivity|].
    left. split; [apply in_map_iff; exists (zb kname, vi); split; [reflexivity | exact (nth_error_In ms i Hi)]|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split.
    { exists i, vi, Du, Dr. split; [exact Hi|]. split; [exact Hfirst|]. split; [exact HNz|]. split; [exact HPD|].
      split; [exact HPDo|]. split; [exact HRF|]. split.
      - rewrite (Permutation_length HPDo), !length_app, (Permutation_length HPD), length_app. lia.
      - rewrite (g_lsum_perm _ _ HPDo), !g_lsum_app, (g_lsum_perm _ _ HPD), g_lsum_app. lia. }
    rewrite (ps_set_hit ms i (zb kname) vi tv Hi Hfirst). exact HNo.
Qed.

End H.
