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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import pj_set_runs pj_set_shape pj_set_sh.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog.CF Require Import pj_set_kb.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import memcpy_c memset_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog.CF Require Import pj_free_c fuzz_strdup_c grow_c pj_set_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog.CF Require Import pj_set_tail pj_set_post pj_set_fail pj_set_ok pj_set_miss.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require strtod_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog.CF Require Import CFS ContractCF KindBGlueCF FrameCF ReaderResCF.
Module YK11 := YK11.
Module YK0s := YK0s.
Module YM05 := YM05.
Module YL01 := U.Reusable.YL01.
Module MemNorm := U.MemNorm.
Module strtod_c := U.Prog.strtod_c.
Import YM05.
Import ListNotations.
Local Open Scope Z_scope.

Section G2.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Hypothesis HFREE : pj_free_contract B API F.
Hypothesis HSD : fuzz_strdup_contract B API F.
Hypothesis HGROW : grow_contract B API F.
Hypothesis AX : YL01.AllocExtra B (aa_MR API).
Hypothesis HMC : memcpy_contract.
Hypothesis HMS : memset_contract.

Local Notation getr := YK11.getr.

Lemma miss_arm : forall L A regs mem md Lam peak cnt fail b o k w ms tv D Dw num str kids keys n cap kname slack
    (dd : nat) lo m1 regs1 junk ro rko rw rkw,
  reader_env B API (PJ_SET_K dd) L A regs mem md ->
  ledger B L A mem Lam peak cnt fail -> rf_ok F A b ->
  o <> 0 -> pj_node (ms_segs B) mem (lin Lam) o (JObj ms) D ->
  pj_hdr (ms_segs B) mem o 6 num str kids keys n cap -> cap <= 2 ^ 54 ->
  rplace B L A Lam regs mem o ->
  w <> 0 -> pj_node (ms_segs B) mem (lin Lam) w tv Dw -> rplace B L A Lam regs mem w ->
  (forall bk, In bk Dw -> ~ In bk D) -> (forall x, w <= x < w + 56 -> ~ pj_foot o D x) -> pj_apart Dw o ->
  (depth (JObj ms) <= S dd)%nat -> (depth tv <= dd)%nat ->
  Mem.bytes_at (ms_segs B) mem k (kname ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) kname ->
  (- (k + Z.of_nat (length kname) + 1)) mod 8 <= Z.of_nat (length slack) ->
  cstr_ok B Lam k (Z.of_nat (length kname) + 1 + Z.of_nat (length slack)) ->
  (forall x, k <= x < k + Z.of_nat (length kname) + 1 -> ~ pj_foot o D x /\ ~ pj_foot w Dw x) ->
  Frame.disjoint_from [(o, o + 56); (w, w + 56); (k, k + Z.of_nat (length kname) + 1)]
    (spZ regs - PJ_SET_K dd) (PJ_SET_K dd) ->
  cnt + 3 < 2 ^ 64 - 1 ->
  room_run F b (set_trace n cap (Z.of_nat (length kname))) ->
  vplace L A Lam (spZ regs) o ro rko -> vplace L A Lam (spZ regs) w rw rkw ->
  spZ regs <= lo -> (st_init_done A = false -> auxv_pre B (ly_sec L) lo mem) ->
  (forall x, pj_set_writes o w D Dw x -> x < lo) -> (spZ regs <= w -> w + 56 <= lo) ->
  rpost B API (PJ_SET_K dd) L A regs mem md (pj_set_writes o w D Dw) (freed (D ++ Dw)) L A regs m1 md ->
  Frame.munch [(spZ regs - 128, spZ regs)] mem m1 -> Frame.wmono (ms_segs B) mem m1 ->
  ledger B L A m1 Lam peak cnt fail -> rd_cells B m1 ->
  rw_cells (ms_segs B) m1 (spZ regs - 48)
    [CB 8 junk; C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)] ->
  getr regs1 1 = Z_to_bv 64 PS_GROW_RET -> getr regs1 2 = Z_to_bv 64 (spZ regs - 48) ->
  getr regs1 10 = Z_to_bv 64 o -> getr regs1 8 = Z_to_bv 64 w -> getr regs1 9 = Z_to_bv 64 o ->
  getr regs1 18 = Z_to_bv 64 k ->
  (forall r, r = 3 \/ r = 4 \/ 20 <= r <= 27 -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
  (forall nm u, In (nm, u) ms -> nm <> zb kname) ->
  SR (ms_segs B) (mkCfg (YK11.mkst regs1 (Z_to_bv 64 PS_GROW) m1 (YK11.seg_rom (ms_segs B))) md)
    (set_post B API F dd L A regs mem md Lam peak cnt fail b o w ms tv D Dw kids keys n cap kname).
Proof.
  intros L A regs mem md Lam peak cnt fail b o k w ms tv D Dw num str kids keys n cap kname slack dd lo m1 regs1 junk
    ro rko rw rkw HE HL Hres Ho0 HN HH Hcap HPo Hw0 HNw HPw HDD HWD HAw Hdo Hdt HKB Hkn Hsl Hcs HKD HDJ Hcnt Hroom
    HVo HVw Hlo Hax HElo Hlw HR1 HMU1 HWM1 HL1 Hrd1 FR G1 G2 G10 G8 G9 G18 Gk Hnin.
  pose proof HE as HE0. pose proof HDJ as HDJ0.
  destruct HE as (HSEG & Htp & Herrno & Hgot & Hguard & Hpre & Hsp47 & Hglob & Hfrm & HRD).
  pose proof Hpre as (HMR & HWF & Hbd & Hra & Hsp16 & Hspc & Hsp63 & Hstk & Htpr & Herr & Haux).
  pose proof alloc_ceiling_value as Hceil.
  pose proof (t_sk dd) as (Kf & Kg & Ks & K96 & Kf0).
  assert (HGK : 0 <= GROW_K) by (unfold GROW_K, GROW_F, REALLOC_K, REALLOC_STACK, ALLOC_STACK; lia).
  unfold strtod_c.STRTOD_GLOBALS_TOP in Hglob.
  cbn [Frame.disjoint_from] in HDJ.
  clear Haux. let T := type of Hax in change (hid T) in Hax. let T := type of Hlw in change (hid T) in Hlw.
  pose proof (g_img B HSEG) as HIL.
  pose proof HR1 as (HMR1 & _).
  assert (Hs1 : spZ regs1 = spZ regs - 48) by (unfold spZ at 1; rewrite G2, unsigned_lit by lia; reflexivity).
  assert (Herr4 : errno_addr B + 4 <= spZ regs - PJ_SET_K dd) by (rewrite Herrno; unfold strtod_c.STRTOD_ERRNO; lia).
  assert (HDL : forall a k0, In (a, k0) D -> In (a, k0) Lam)
    by (intros a k0 Hb; exact (pis_node_lblk (ms_segs B) (JObj ms) mem (lin Lam) o D HN (a, k0) Hb)).
  assert (HDwL : forall a k0, In (a, k0) Dw -> In (a, k0) Lam)
    by (intros a k0 Hb; exact (pis_node_lblk (ms_segs B) tv mem (lin Lam) w Dw HNw (a, k0) Hb)).
  pose proof (pis_node_rw (ms_segs B) mem (lin Lam) w tv Dw HNw) as (Hw8 & HwS).
  pose proof HwS as (Hw0' & Hw1' & HwSt).
  pose proof (pis_node_rw (ms_segs B) mem (lin Lam) o (JObj ms) D HN) as (Ho8 & HoS).
  pose proof HoS as (Ho0' & Ho1' & HoSt).
  pose proof HPo as (_ & _ & Ho3). pose proof HPw as (_ & _ & Hw3).
  assert (Hnin' : ~ In (zb kname) (map fst ms)).
  { intros H. apply in_map_iff in H as ((nm & u) & E0 & Hin). cbn [fst] in E0. exact (Hnin nm u Hin E0). }
  assert (Hcs1 : cstr_ok B Lam k (Z.of_nat (length kname) + 1)).
  { destruct Hcs as [Hro|(a & kk & Hl & H1 & H2)]; [left; intros i Hi; apply Hro; lia|].
    right. exists a, kk. split; [exact Hl | lia]. }
  assert (HS01 : forall x, 0 <= x < 2 ^ 64 -> (x < spZ regs - 128 \/ spZ regs <= x) -> pis_same (ms_segs B) mem m1 x).
  { intros x Hx Hx'. apply (g_same_munch (ms_segs B) _ mem m1 x HMU1 HWM1 Hx). cbn [Frame.outside].
    split; [lia | exact I]. }
  assert (HFo : forall x, pj_foot o D x -> pis_same (ms_segs B) mem m1 x).
  { intros x [Hx|((a & k0) & Hb & Hx)]; [apply HS01; lia|].
    unfold pj_holds in Hx; cbn [fst snd] in Hx.
    destruct (ledger_block_range B API L A mem md Lam peak cnt fail a k0 HMR HL (HDL a k0 Hb)) as (R1 & R2 & _).
    apply HS01; lia. }
  assert (HFw : forall x, pj_foot w Dw x -> pis_same (ms_segs B) mem m1 x).
  { intros x [Hx|((a & k0) & Hb & Hx)]; [apply HS01; lia|].
    unfold pj_holds in Hx; cbn [fst snd] in Hx.
    destruct (ledger_block_range B API L A mem md Lam peak cnt fail a k0 HMR HL (HDwL a k0 Hb)) as (R1 & R2 & _).
    apply HS01; lia. }
  pose proof (pis_node_frame (ms_segs B) (JObj ms) mem (lin Lam) m1 (lin Lam) o D HN
    (fun a k0 Hb => HDL a k0 Hb) HFo) as HN1.
  pose proof (pis_node_frame (ms_segs B) tv mem (lin Lam) m1 (lin Lam) w Dw HNw
    (fun a k0 Hb => HDwL a k0 Hb) HFw) as HNw1.
  pose proof (pis_hdr_frame (ms_segs B) mem m1 o 6 num str kids keys n cap HH
    (fun x Hx => HFo x (or_introl Hx))) as HH1.
  destruct (ps_node_open (ms_segs B) m1 (lin Lam) o ms D num str kids keys n cap HN1 HH1 Hcap)
    as (Di0 & ED & Es & En & HO1).
  subst str.
  pose proof HO1 as (HND1 & HAP1 & _ & HSL1 & _ & _).
  pose proof HSL1 as (_ & (Hnc & Hc54) & Hc00 & Hcp).
  clear Hc00. let T := type of Hcp in change (hid T) in Hcp.
  assert (ED' : D = (kids_blk kids cap ++ keys_blk 6 keys cap) ++ Di0) by exact ED.
  assert (HKsD : forall bk, In bk (kids_blk kids cap ++ keys_blk 6 keys cap) -> In bk D)
    by (intros bk Hb; rewrite ED'; apply in_or_app; left; exact Hb).
  assert (HDi0D : forall bk, In bk Di0 -> In bk D) by (intros bk Hb; rewrite ED'; apply in_or_app; right; exact Hb).
  assert (HkkL : forall a k0, In (a, k0) (kids_blk kids cap ++ keys_blk 6 keys cap) -> In (a, k0) Lam)
    by (intros a k0 Hb; exact (HDL a k0 (HKsD _ Hb))).
  assert (HAPk : pj_apart (kids_blk kids cap ++ keys_blk 6 keys cap) o).
  { intros bb x Hb Hx. apply (HAP1 bb x); [apply in_or_app; left; exact Hb | exact Hx]. }
  assert (HAPkw : pj_apart (kids_blk kids cap ++ keys_blk 6 keys cap) w).
  { intros bb x Hb Hx Hxw. apply (HWD x Hxw). right. exists bb. split; [exact (HKsD _ Hb) | exact Hx]. }
  assert (HDiS : forall bk, In bk Di0 -> ~ In bk (kids_blk kids cap ++ keys_blk 6 keys cap)).
  { intros bk Hb Hs. exact (pis_nodup_app_disj _ _ _ bk HND1 Hs Hb). }
  assert (Hlc : Z.of_nat (length (map snd ms)) <= cap) by (rewrite length_map; lia).
  assert (HNDL : List.NoDup (map fst Lam)).
  { pose proof HL as (_ & _ & _ & _ & HND & _). first [exact HND | apply NoDup_ListNoDup; exact HND]. }
  assert (HND0 : List.NoDup (D ++ Dw)).
  { apply NoDup_ListNoDup. apply pis_nodup_app;
      [exact (sh_node_nodup (ms_segs B) mem (lin Lam) o (JObj ms) D HN)
      | exact (sh_node_nodup (ms_segs B) mem (lin Lam) w tv Dw HNw)
      | intros a Ha Hw'; exact (HDD a Hw' Ha)]. }
  assert (HIN0 : incl (D ++ Dw) Lam).
  { intros (a & k0) Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [exact (HDL a k0 Hb) | exact (HDwL a k0 Hb)]. }
  destruct (g_perm_sub (D ++ Dw) Lam HND0 HIN0 (List.NoDup_map_inv _ _ HNDL)) as (Lr & HLr).
  assert (HPL : Permutation Lam (D ++ Dw ++ Lr)) by (rewrite app_assoc; exact HLr).
  assert (Hax1 : st_init_done A = false -> auxv_pre B (ly_sec L) lo m1)
    by (apply (g_aux_rp B API (PJ_SET_K dd) L A regs mem md _ _ L A regs m1 md lo lo HR1); first [lia | assumption]).
  assert (Hlo_o : spZ regs <= o -> o + 56 <= lo) by (intros _; pose proof (HElo (o + 55) ltac:(left; lia)); lia).
  assert (HPo1 : rplace B L A Lam regs1 m1 o).
  { apply (g_rplace_carry B API L A Lam regs1 m1 md (spZ regs) o ro rko lo HMR1 HVo ltac:(lia) ltac:(lia));
      [|exact Hlo_o | exact Hax1].
    intros i Hi. destruct (Ho3 i Hi) as (O1 & O2 & O3 & O4).
    split; [intros Hs; exact (O1 (or_intror Hs))|]. split; [exact O2|]. split; [exact O3 | exact O4]. }
  clear Hlo_o Hax1.
  assert (Hpreg : call_pre_k B (aa_MR API) GROW_K L A regs1 m1 md).
  { apply (g_pre_k B API (PJ_SET_K dd) L A regs mem md _ _ L A m1 md regs1 GROW_K lo Hpre HR1).
    - rewrite G1. unfold YK0s.ret_ok. apply bv_eq. vm_compute. reflexivity.
    - rewrite Hs1. replace (spZ regs - 48) with (spZ regs + (-3) * 16) by lia. rewrite Z_mod_plus_full. exact Hsp16.
    - lia.
    - lia.
    - exact HGK.
    - exact (Gk 4 ltac:(lia)).
    - lia.
    - exact Hlo.
    - exact Hax.
    - exact HElo. }
  assert (HEg : reader_env B API GROW_K L A regs1 m1 md).
  { split; [exact HSEG|]. split; [exact Htp|]. split; [exact Herrno|]. split; [exact Hgot|]. split; [exact Hguard|].
    split; [exact Hpreg|]. split; [lia|]. split; [unfold strtod_c.STRTOD_GLOBALS_TOP; lia|].
    split; [exact Hfrm | exact Hrd1]. }
  assert (HDgr : Frame.disjoint_from [(o, o + 56)] (spZ regs1 - GROW_K) GROW_K) by (cbn [Frame.disjoint_from]; lia).
  assert (Hrmg : n = cap -> rf_room F b (56 * cap2 cap + 16) /\ 56 * cap2 cap + 16 <= 2 ^ 28 /\
      (6 = 6 -> rf_room F (rf_grow F b (56 * cap) (56 * cap2 cap)) (8 * cap2 cap + 16))).
  { intros Hnc'. rewrite Hnc' in Hroom.
    destruct (st_eq_room F b cap (Z.of_nat (length kname)) ltac:(lia) ltac:(lia) Hroom) as (R1 & R2 & R3 & _).
    split; [exact R1|]. split; [exact R2 | intros _; exact R3]. }
  change (Z_to_bv 64 PS_GROW) with (Z_to_bv 64 GROW).
  eapply SR_bind; [apply (HGROW L A regs1 m1 md Lam peak cnt fail b o 6 num 0 kids keys n cap HEg HL1 Hres G10 Ho0 HH1
    HSL1 HAPk HPo1 HDgr ltac:(lia) Hrmg) |].
  intros cc2 HC2.
  destruct HC2 as (L2 & A2 & regs2 & mem2 & md2 & Lam2 & peak2 & cnt2 & fail2 & b2 & res & -> & HR2 & Hrd2 & G2_10 &
    HL2 & Hrf2 & ARMS).
  pose proof HR2 as (HMR2 & HWF2 & _ & _ & _ & _ & _ & _ & _ & Hp12 & _).
  let T := type of ARMS in change (hid T) in ARMS. clear Hrmg.
  assert (HGW : forall x, grow_writes o 6 kids keys n cap x -> pj_set_writes o w D Dw x).
  { intros x (_ & [Hx|[Hx|[(a0 & k0 & Hb & Hx)|Hx]]]).
    - left; lia.
    - left; lia.
    - right; right; left. exists a0, k0. split; [apply in_or_app; left; exact (HKsD _ Hb) | exact Hx].
    - right; right; right; exact Hx. }
  assert (HGG : forall a s, grow_gone 6 kids keys n cap a s -> freed (D ++ Dw) a s).
  { intros a s (_ & Hf). unfold freed in *. apply in_or_app. left. exact (HKsD _ Hf). }
  assert (HGWl : forall x, grow_writes o 6 kids keys n cap x -> o <= x < o + 56 \/ 0 <= x < alloc_ceiling).
  { intros x (_ & [Hx|[Hx|[(a0 & k0 & Hb & Hx)|Hx]]]); [left; lia | left; lia | right | right].
    - destruct (ledger_block_range B API L A mem md Lam peak cnt fail a0 k0 HMR HL (HkkL a0 k0 Hb)) as (R1 & R2 & _).
      lia.
    - unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Hx. lia. }
  assert (HR3 : rpost B API (PJ_SET_K dd) L A regs mem md (pj_set_writes o w D Dw) (freed (D ++ Dw)) L2 A2 regs mem2 md2).
  { apply (rp_rec B API (PJ_SET_K dd) L A regs mem md _ _ L A m1 md GROW_K regs1 (grow_writes o 6 kids keys n cap)
      (grow_gone 6 kids keys n cap) L2 A2 regs2 mem2 md2 HWF ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HR1 HR2).
    - intros a _ _ Ha. exact (HGW a Ha).
    - intros a _ _ Ha. exact (HGW a Ha).
    - intros p n0 i0 _ _ _ Ha. exact (HGW _ Ha).
    - intros p n0 _ _ Hg. exact (HGG _ _ Hg).
    - intros p n0 i0 _ Hi0 Hf. exact (st_gone _ _ _ o w D Dw Hi0 Hf).
    - intros a Ha _ Hw. destruct (HGWl a Hw); lia. }
  assert (FR2 : rw_cells (ms_segs B) mem2 (spZ regs - 48)
    [CB 8 junk; C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)]).
  { apply (g_rw_cells B m1); [exact FR|].
    intros x Hx. cbn [cells_size csize Nat.add] in Hx.
    refine (rp_same_hi B API _ _ _ _ _ _ _ _ _ _ _ _ _ x HR2 ltac:(lia) _ _).
    - unfold scratch_k. rewrite Hs1. lia.
    - intros Hw. destruct (HGWl x Hw); lia. }
  clear HDJ.
  assert (G2_8 : getr regs2 8 = Z_to_bv 64 w)
    by (transitivity (getr regs1 (Z_to_bv 5 8)); [apply (Hp12 8); unfold callee_saved; lia | exact G8]).
  assert (G2_18 : getr regs2 18 = Z_to_bv 64 k)
    by (transitivity (getr regs1 (Z_to_bv 5 18)); [apply (Hp12 18); unfold callee_saved; lia | exact G18]).
  assert (HREG : forall regs3, (forall r, r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ 18 <= r <= 27 ->
        getr regs3 (Z_to_bv 5 r) = getr regs2 (Z_to_bv 5 r)) ->
      getr regs3 2 = Z_to_bv 64 (spZ regs - 48) /\ getr regs3 8 = Z_to_bv 64 w /\ getr regs3 9 = Z_to_bv 64 o /\
      (forall r, r = 3 \/ r = 4 \/ 20 <= r <= 27 -> getr regs3 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r))).
  { intros regs3 G3k.
    assert (T : forall r, r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ 18 <= r <= 27 ->
        getr regs3 (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r)).
    { intros r Hr. rewrite (G3k r Hr). apply (Hp12 r). unfold callee_saved. lia. }
    split; [transitivity (getr regs1 (Z_to_bv 5 2)); [exact (T 2 ltac:(lia)) | exact G2]|].
    split; [transitivity (getr regs1 (Z_to_bv 5 8)); [exact (T 8 ltac:(lia)) | exact G8]|].
    split; [transitivity (getr regs1 (Z_to_bv 5 9)); [exact (T 9 ltac:(lia)) | exact G9]|].
    intros r Hr. transitivity (getr regs1 (Z_to_bv 5 r)); [exact (T r ltac:(lia)) | exact (Gk r Hr)]. }
  assert (Hngo : ~ grow_gone 6 kids keys n cap ro rko).
  { intros (_ & Hf).
    exact (g_vloc_nf B API L A Lam m1 md peak cnt fail (spZ regs) o ro rko _ (proj1 HVo) HMR1 HL1 ltac:(lia) HAPk HkkL Hf). }
  assert (Hngw : ~ grow_gone 6 kids keys n cap rw rkw).
  { intros (_ & Hf).
    exact (g_vloc_nf B API L A Lam m1 md peak cnt fail (spZ regs) w rw rkw _ (proj1 HVw) HMR1 HL1 ltac:(lia) HAPkw HkkL Hf). }
  assert (HSB1 : forall a kk x, In (a, kk) Lam -> ~ In (a, kk) (kids_blk kids cap ++ keys_blk 6 keys cap) ->
      a <= x < a + kk -> ~ (o <= x < o + 56) -> pis_same (ms_segs B) m1 mem2 x).
  { intros a kk x Hin Hn Hx Hxo.
    pose proof HL1 as (_ & _ & _ & _ & _ & HF). rewrite Forall_forall in HF.
    destruct (HF _ Hin) as (Hkk & Hb & _). cbn [fst snd] in Hkk, Hb.
    apply (rp_same_blk B API _ _ _ _ _ _ _ _ _ _ _ _ _ (a - 16) (kk + 16) x HR2 Hb); [| lia |].
    - intros (_ & Hf). unfold freed in Hf. replace (a - 16 + 16) with a in Hf by lia.
      replace (kk + 16 - 16) with kk in Hf by lia. exact (Hn Hf).
    - intros (_ & [H1|[H1|[(a0 & k0 & Hb0 & H1)|H1]]]); [lia | lia | |].
      + assert (Hne : (a, kk) <> (a0, k0)) by (intros E; rewrite <- E in Hb0; exact (Hn Hb0)).
        destruct (g_lam_disj B API L A m1 md Lam peak cnt fail a kk a0 k0 HMR1 HL1 Hin (HkkL a0 k0 Hb0) Hne); lia.
      + apply (ledger_block_not_img B L A m1 Lam peak cnt fail a kk (x - a) HL1 Hin ltac:(lia)).
        replace (a + (x - a)) with x by lia. exact (g_img_consts B HSEG Herrno x (or_introl H1)). }
  assert (HGWw : forall x, w <= x < w + 56 -> ~ grow_writes o 6 kids keys n cap x).
  { intros x Hx (_ & [H1|[H1|[(a0 & k0 & Hb0 & H1)|H1]]]).
    - apply (HWD x Hx). left. lia.
    - apply (HWD x Hx). left. lia.
    - pose proof (HkkL a0 k0 Hb0) as HinL.
      pose proof HL1 as (_ & _ & _ & _ & _ & HF). rewrite Forall_forall in HF.
      destruct (HF _ HinL) as (Hkk & Hbb & _). cbn [fst snd] in Hkk, Hbb.
      assert (Hne : (a0 - 16, k0 + 16) <> (rw, rkw)).
      { intros E. injection E as E1 E2.
        apply (g_vloc_nf B API L A Lam m1 md peak cnt fail (spZ regs) w rw rkw _ (proj1 HVw) HMR1 HL1 ltac:(lia)
          HAPkw HkkL).
        unfold freed. rewrite <- E1, <- E2. replace (a0 - 16 + 16) with a0 by lia.
        replace (k0 + 16 - 16) with k0 by lia. exact Hb0. }
      destruct (vloc_disj B API L A Lam m1 md (spZ regs) w rw rkw (a0 - 16) (k0 + 16) x (proj1 HVw) HMR1 ltac:(lia)
        Hbb Hne ltac:(lia)); lia.
    - destruct (Hw3 (x - w) ltac:(lia)) as (_ & W2 & _). replace (w + (x - w)) with x in W2 by lia. exact (W2 H1). }
  assert (HWS1 : forall x, w <= x < w + 56 -> pis_same (ms_segs B) m1 mem2 x).
  { intros x Hx. destruct (Hw3 (x - w) ltac:(lia)) as (_ & _ & W3 & _). replace (w + (x - w)) with x in W3 by lia.
    exact (vloc_same B API L A Lam (spZ regs) w rw rkw GROW_K regs1 m1 md _ _ L2 A2 regs2 mem2 md2 x (proj1 HVw) HR2 Hngw
      ltac:(lia) ltac:(lia) W3 Hx (HGWw x Hx)). }
  assert (HNw2_of : (forall a k0, In (a, k0) Dw -> In (a, k0) Lam2) -> pj_node (ms_segs B) mem2 (lin Lam2) w tv Dw).
  { intros HDwL2. apply (pis_node_frame (ms_segs B) tv m1 (lin Lam) mem2 (lin Lam2) w Dw HNw1);
      [intros a k0 Hb; exact (HDwL2 a k0 Hb)|].
    intros x [Hx|((a & k0) & Hb & Hx)].
    - exact (HWS1 x Hx).
    - unfold pj_holds in Hx; cbn [fst snd] in Hx.
      apply (HSB1 a k0 x (HDwL a k0 Hb)); [| exact Hx | exact (HAw (a, k0) x Hb ltac:(unfold pj_holds; cbn [fst snd]; lia))].
      intros Hkk. exact (HDD _ Hb (HKsD _ Hkk)). }
  let T := type of HNw2_of in change (hid T) in HNw2_of.
  assert (HDi : forall x, (exists bb, In bb Di0 /\ pj_holds bb x) -> pis_same (ms_segs B) m1 mem2 x).
  { intros x ((a & kk) & Hb & Hx). unfold pj_holds in Hx; cbn [fst snd] in Hx.
    apply (HSB1 a kk x (HDL a kk (HDi0D _ Hb)) (HDiS _ Hb) Hx).
    apply (HAP1 (a, kk) x); [apply in_or_app; right; exact Hb | unfold pj_holds; cbn [fst snd]; lia]. }
  assert (HNEW : forall v r rk a kk x, vloc L A Lam (spZ regs) v r rk -> vloc L2 A2 Lam2 (spZ regs) v r rk ->
      In (a, kk) Lam2 -> ~ In (a - 16, kk + 16) (blocks L A) -> a <= x < a + kk -> x < v \/ v + 56 <= x).
  { intros v r rk a kk x HV1 HV2 Hin Hn Hx.
    pose proof HL2 as (_ & _ & _ & _ & _ & HF2). rewrite Forall_forall in HF2.
    destruct (HF2 _ Hin) as (Hkk & Hb & _). cbn [fst snd] in Hkk, Hb.
    apply (vloc_disj B API L2 A2 Lam2 mem2 md2 (spZ regs) v r rk (a - 16) (kk + 16) x HV2 HMR2 ltac:(lia) Hb); [|lia].
    intros E. apply (vloc_ne L A Lam (spZ regs) v r rk (a - 16) (kk + 16) HV1 Hn ltac:(lia)). symmetry. exact E. }
  rewrite G1.
  unfold hid in ARMS. destruct ARMS as [ARM|[ARM|[ARM|[ARM|ARM]]]].
  -
    destruct ARM as (Hlt & Er & EL & EA & ELm & Ep & Ec & Ef & Eb & HHm2).
    subst L2 A2 Lam2 peak2 cnt2 fail2 b2 res.
    apply (sc_go B API L A regs2 mem2 md2 0 k w _ HSEG HMR2 G2_10 (or_introl eq_refl) G2_8 G2_18); [|intros E; lia].
    intros _ regs3 G3_1 G3_10 G3k.
    destruct (HREG regs3 G3k) as (G3_2 & G3_8 & G3_9 & Gk3).
    destruct (st_lt_facts F b n cap (Z.of_nat (length kname)) Hlt ltac:(lia))
      as (Tl & Trun & Tnl & Thd & Trun0 & Tnl0 & Thd0 & Troom).
    destruct (g_str_after B API L A regs mem md Lam peak cnt fail o w D Dw (PJ_SET_K dd) L A regs mem2 md2 k kname slack
      HSEG Herrno HMR HL HRD Hrd2 HR3 HDL HDwL HKB Hcs HKD) as (slack' & Hsl'l & HKg).
    assert (HSBa : forall a kk x, In (a, kk) Lam -> a <= x < a + kk -> pis_same (ms_segs B) m1 mem2 x).
    { intros a kk x Hin Hx.
      pose proof HL1 as (_ & _ & _ & _ & _ & HF). rewrite Forall_forall in HF.
      destruct (HF _ Hin) as (Hkk & Hb & _). cbn [fst snd] in Hkk, Hb.
      apply (rp_same_blk B API _ _ _ _ _ _ _ _ _ _ _ _ _ (a - 16) (kk + 16) x HR2 Hb);
        [intros (Hc' & _); lia | lia | intros (Hc' & _); lia]. }
    assert (HLg : ledger B L A mem2 Lam (Z.max peak (lsum Lam)) (cnt + Z.of_nat 0) fail).
    { pose proof HL2 as (_ & Hpk & _). replace (Z.max peak (lsum Lam)) with peak by lia.
      replace (cnt + Z.of_nat 0) with cnt by lia. exact HL2. }
    assert (Hfg : ~ (cnt <= fail < cnt + Z.of_nat 0)) by lia.
    assert (Hresg : rf_ok F A (rf_run F b (firstn 0 (set_trace n cap (Z.of_nat (length kname))))))
      by (rewrite Trun0; exact Hrf2).
    assert (HOg : pis_open (ms_segs B) mem2 (lin Lam) o true num kids keys cap n (map snd ms) (map fst ms) Di0).
    { apply (pis_grow_kept (ms_segs B) m1 mem2 (lin Lam) o true num kids keys cap n (map snd ms) (map fst ms) Di0 HO1
        HHm2).
      - intros i Hi. exact (proj1 (HSBa kids (56 * cap) (kids + i) (proj1 (Hcp ltac:(lia))) ltac:(lia))).
      - intros _ i Hi. exact (proj1 (HSBa keys (8 * cap) (keys + i) (proj2 (Hcp ltac:(lia)) eq_refl) ltac:(lia))).
      - intros i Hi Hw'. rewrite length_map in Hi.
        exact (proj2 (HSBa kids (56 * cap) (kids + i) (proj1 (Hcp ltac:(lia))) ltac:(lia)) Hw').
      - intros x ((a & kk) & Hb & Hx). unfold pj_holds in Hx; cbn [fst snd] in Hx.
        exact (HSBa a kk x (HDL a kk (HDi0D _ Hb)) Hx).
      - exact Hlc. }
    assert (HNw2 : pj_node (ms_segs B) mem2 (lin Lam) w tv Dw) by exact (HNw2_of HDwL).
    assert (HSE : forall a kk, In (a, kk) (pis_slots true kids keys cap) ->
        (forall z, a - 16 <= z < a + kk -> pj_set_writes o w D Dw z) \/ ~ In (a - 16, kk + 16) (blocks L A)).
    { intros a kk Hb. left. intros z Hz. right; right; left. exists a, kk.
      split; [apply in_or_app; left; rewrite ED; apply in_or_app; left; exact Hb | lia]. }
    assert (HAPw : pj_apart (pis_slots true kids keys cap ++ Di0) w).
    { rewrite <- ED. intros bb x Hb Hx Hxw. apply (HWD x Hxw). right. exists bb. split; [exact Hb | exact Hx]. }
    assert (Hlenh : Z.of_nat (length ([] ++ D)) =
        Z.of_nat (length D) + nlive (firstn 0 (set_trace n cap (Z.of_nat (length kname)))))
      by (rewrite Tnl0; cbn [app]; lia).
    assert (Hsumh : lsum ([] ++ D) = lsum D + held (firstn 0 (set_trace n cap (Z.of_nat (length kname)))))
      by (rewrite Thd0; cbn [app]; lia).
    assert (Hrun : rf_run F b (set_trace n cap (Z.of_nat (length kname))) =
        rf_malloc F (rf_run F b (firstn 0 (set_trace n cap (Z.of_nat (length kname))))) (Z.of_nat (length kname) + 17))
      by (rewrite Trun, Trun0; reflexivity).
    assert (Hnl : nlive (set_trace n cap (Z.of_nat (length kname))) =
        nlive (firstn 0 (set_trace n cap (Z.of_nat (length kname)))) + 1) by (rewrite Tnl, Tnl0; reflexivity).
    assert (Hhd : held (set_trace n cap (Z.of_nat (length kname))) =
        held (firstn 0 (set_trace n cap (Z.of_nat (length kname)))) + Z.of_nat (length kname) + 1)
      by (rewrite Thd, Thd0; lia).
    assert (Hroomg : rf_room F (rf_run F b (firstn 0 (set_trace n cap (Z.of_nat (length kname)))))
        (Z.of_nat (length kname) + 17)) by (rewrite Trun0; exact (proj1 (Troom Hroom))).
    exact (ok_arm B API F HFREE HSD AX HMC HMS L A regs mem md Lam peak cnt fail b o k w ms tv D Dw num kids keys n cap
      kname slack' dd lo L A regs3 mem2 md2 Lam junk 0%nat kids keys cap Di0 Lr [] [] D ro rko rw rkw HE0 HPo Hw0 HPw HWD
      HAw Hdt Hkn ltac:(rewrite Hsl'l; exact Hsl) Hcs1 HKD HDJ0 Hcnt Hlo Hax HElo Hlw Hnin HPL HDD HR3 HLg Hfg Hresg Hrd2
      FR2 G3_1 G3_2 G3_10 G3_8 G3_9 Gk3 HKg HNw2 HVw HVo HOg En Hlt HPL ED (Permutation_refl D)
      (fun a kk (H : In (a, kk) []) => False_ind _ H) HSE HAPw
      (or_introl (conj Hlt (conj eq_refl (conj eq_refl eq_refl)))) Hlenh Hsumh Tl Hrun Hnl Hhd Hroomg
      (proj2 (Troom Hroom)) Ho0).
  -
    destruct ARM as (Heq & Ecf & Er & ELm & Ep & Ec & Ef & Eb & HHm2 & Hmk & Hmy).
    subst Lam2 peak2 cnt2 fail2 b2 res. rewrite Heq in *. clear Heq.
    apply (sc_go B API L2 A2 regs2 mem2 md2 (-1) k w _ HSEG HMR2 G2_10 (or_intror eq_refl) G2_8 G2_18);
      [intros E; lia|].
    intros _ regs3 G3_1 G3_10 G3k.
    destruct (HREG regs3 G3k) as (G3_2 & G3_8 & G3_9 & Gk3).
    destruct (st_eq_run F b cap (Z.of_nat (length kname)) ltac:(lia) ltac:(lia))
      as (Tl3 & Tr0 & Tr1 & Tr2 & Trf & Th0 & Th1 & Th2 & Thf).
    destruct (st_eq_nl cap (Z.of_nat (length kname)) kids keys ltac:(lia)) as (z0 & Lk & Ly & N0 & N1 & N2 & Nf).
    pose proof (vplace_rp B API L A Lam (spZ regs) w rw rkw GROW_K regs1 m1 md _ _ L2 A2 regs2 mem2 md2 Lam _ _ _
      HVw HR2 Hngw HL2 (fun a kk H => or_introl H)) as HVw2.
    pose proof (vplace_rp B API L A Lam (spZ regs) o ro rko GROW_K regs1 m1 md _ _ L2 A2 regs2 mem2 md2 Lam _ _ _
      HVo HR2 Hngo HL2 (fun a kk H => or_introl H)) as HVo2.
    assert (HL1' : ledger B L2 A2 mem2 Lam (Z.max peak (lsum Lam)) (cnt + Z.of_nat 1) (2 ^ 64 - 1)).
    { pose proof HL2 as (_ & Hpk & _). replace (Z.max peak (lsum Lam)) with peak by lia.
      replace (cnt + Z.of_nat 1) with (cnt + 1) by lia. exact HL2. }
    assert (Hres1 : rf_ok F A2 (rf_run F b (firstn (1 - 1) (set_trace cap cap (Z.of_nat (length kname))))))
      by (change (1 - 1)%nat with 0%nat; rewrite Tr0; exact Hrf2).
    pose proof (HNw2_of HDwL) as HNw2.
    pose proof (pj_fd_mono (ms_segs B) mem2 (lin Lam) (depth tv) dd w Dw Hdt
      (pj_node_fd (ms_segs B) tv mem2 (lin Lam) w Dw HNw2)) as Hfdw.
    assert (HOo2 : pis_open (ms_segs B) mem2 (lin Lam) o true num kids keys cap cap (map snd ms) (map fst ms) Di0).
    { apply (pis_grow_kept (ms_segs B) m1 mem2 (lin Lam) o true num kids keys cap cap (map snd ms) (map fst ms) Di0 HO1
        HHm2 Hmk (fun _ => Hmy eq_refl)).
      - intros i Hi _. rewrite length_map in Hi.
        assert (Hkid : In (kids, 56 * cap) Lam) by exact (proj1 (Hcp ltac:(lia))).
        destruct (ledger_block_range B API L A m1 md Lam peak cnt fail kids (56 * cap) HMR1 HL1 Hkid) as (R1 & R2 & _).
        apply (g_wr_of_mbyte B HSEG mem2 (kids + i) ltac:(lia)).
        + replace (kids + i) with (kids + i) by lia.
          exact (ledger_block_not_img B L A m1 Lam peak cnt fail kids (56 * cap) i HL1 Hkid ltac:(lia)).
        + rewrite (Hmk i ltac:(lia)).
          destruct (ledger_block_present B API L A m1 md Lam peak cnt fail kids (56 * cap) i HMR1 HL1 Hkid ltac:(lia))
            as (bb & Hbb).
          unfold mbyte. rewrite Hbb. discriminate.
      - exact HDi.
      - exact Hlc. }
    assert (HNo2 : pj_node (ms_segs B) mem2 (lin Lam) o (JObj ms) D)
      by (rewrite ED; exact (ps_obj_node (ms_segs B) mem2 (lin Lam) o ms Di0 num kids keys cap cap HOo2 En)).
    assert (HADo : pj_apart D w).
    { intros bb x Hb Hx Hxw. apply (HWD x Hxw). right. exists bb. split; [exact Hb | exact Hx]. }
    assert (Hlen : Z.of_nat (length D) =
        Z.of_nat (length D) + nlive (firstn (1 - 1) (set_trace cap cap (Z.of_nat (length kname)))))
      by (change (1 - 1)%nat with 0%nat; rewrite N0; lia).
    assert (Hsum : lsum D = lsum D + held (firstn (1 - 1) (set_trace cap cap (Z.of_nat (length kname)))))
      by (change (1 - 1)%nat with 0%nat; rewrite Th0; lia).
    exact (fail_arm B API F HFREE L A regs mem md Lam peak cnt fail b o k w ms tv D Dw kids keys cap cap kname dd lo
      L2 A2 regs3 mem2 md2 Lam junk ro rko rw rkw 1%nat Lr D [] [] D (depth (JObj ms)) HE0 HPo HPw HWD HAw HDJ0 Hlo Hax
      HElo Hlw Hnin' HPL HR3 HL1' Hres1 Hrd2 FR2 G3_1 G3_2 G3_10 Gk3 Hw0 Hfdw HVw2 HVo2 HPL
      (pj_node_fd (ms_segs B) (JObj ms) mem2 (lin Lam) o D HNo2) (fun _ => HNo2) HADo
      ltac:(rewrite Tl3; lia) ltac:(lia) Hlen Hsum (Permutation_refl D) (Permutation_refl D)
      (fun a kk (H : In (a, kk) []) => False_ind _ H) (or_introl (conj eq_refl (conj eq_refl eq_refl)))).
  -
    destruct ARM as (_ & _ & Hty & _). exfalso. exact (Hty eq_refl).
  -
    destruct ARM as (Heq & Hcf & _ & Hc1 & Er & (k' & Lam0 & Hk'0 & Hk'16 & Hnew' & HP0 & HP0' & Ep & Ec & Ef & Eb & Hmk &
      HHm2 & Hmy)).
    subst peak2 cnt2 fail2 b2 res. rewrite Heq in *. clear Heq.
    apply (sc_go B API L2 A2 regs2 mem2 md2 (-1) k w _ HSEG HMR2 G2_10 (or_intror eq_refl) G2_8 G2_18);
      [intros E; lia|].
    intros _ regs3 G3_1 G3_10 G3k.
    destruct (HREG regs3 G3k) as (G3_2 & G3_8 & G3_9 & Gk3).
    destruct (st_eq_run F b cap (Z.of_nat (length kname)) ltac:(lia) ltac:(lia))
      as (Tl3 & Tr0 & Tr1 & Tr2 & Trf & Th0 & Th1 & Th2 & Thf).
    destruct (st_eq_nl cap (Z.of_nat (length kname)) kids keys ltac:(lia)) as (z0 & Lk & Ly & N0 & N1 & N2 & Nf).
    pose proof (st_cap2 cap ltac:(lia)) as (C1 & C2).
    assert (HL0 : Permutation Lam0 (keys_blk 6 keys cap ++ Di0 ++ Dw ++ Lr)).
    { apply (Permutation_app_inv_l (kids_blk kids cap)). apply (Permutation_trans (Permutation_sym HP0)).
      apply (Permutation_trans HPL). rewrite ED'. rewrite <- !app_assoc. apply Permutation_refl. }
    assert (Lam0Lam2 : forall a kk, In (a, kk) Lam0 -> In (a, kk) Lam2)
      by (intros a kk H; apply (Permutation_in _ (Permutation_sym HP0')); right; exact H).
    assert (HK2 : In (k', 56 * cap2 cap) Lam2) by (apply (Permutation_in _ (Permutation_sym HP0')); left; reflexivity).
    assert (DwLam0 : forall a kk, In (a, kk) Dw -> In (a, kk) Lam0).
    { intros a kk Hb. apply (Permutation_in _ (Permutation_sym HL0)). apply in_or_app; right. apply in_or_app; right.
      apply in_or_app; left. exact Hb. }
    assert (DiLam0 : forall a kk, In (a, kk) Di0 -> In (a, kk) Lam0).
    { intros a kk Hb. apply (Permutation_in _ (Permutation_sym HL0)). apply in_or_app; right. apply in_or_app; left.
      exact Hb. }
    assert (Hsub : forall a kk, In (a, kk) Lam2 -> In (a, kk) Lam \/ ~ In (a - 16, kk + 16) (blocks L A)).
    { intros a kk Hin. apply (Permutation_in _ HP0') in Hin. destruct Hin as [E|Hin].
      - right. injection E as <- <-. exact (Hnew' k' (56 * cap2 cap) (or_introl eq_refl)).
      - left. apply (Permutation_in _ (Permutation_sym HP0)). apply in_or_app. right. exact Hin. }
    pose proof (vplace_rp B API L A Lam (spZ regs) w rw rkw GROW_K regs1 m1 md _ _ L2 A2 regs2 mem2 md2 Lam2 _ _ _
      HVw HR2 Hngw HL2 Hsub) as HVw2.
    pose proof (vplace_rp B API L A Lam (spZ regs) o ro rko GROW_K regs1 m1 md _ _ L2 A2 regs2 mem2 md2 Lam2 _ _ _
      HVo HR2 Hngo HL2 Hsub) as HVo2.
    assert (HL1' : ledger B L2 A2 mem2 Lam2 (Z.max peak (lsum Lam2)) (cnt + Z.of_nat 2) (2 ^ 64 - 1))
      by (replace (cnt + Z.of_nat 2) with (cnt + 2) by lia; exact HL2).
    assert (Hres1 : rf_ok F A2 (rf_run F b (firstn (2 - 1) (set_trace cap cap (Z.of_nat (length kname))))))
      by (change (2 - 1)%nat with 1%nat; rewrite Tr1; exact Hrf2).
    pose proof (HNw2_of (fun a kk Hb => Lam0Lam2 a kk (DwLam0 a kk Hb))) as HNw2.
    pose proof (pj_fd_mono (ms_segs B) mem2 (lin Lam2) (depth tv) dd w Dw Hdt
      (pj_node_fd (ms_segs B) tv mem2 (lin Lam2) w Dw HNw2)) as Hfdw.
    destruct (ledger_block_range B API L2 A2 mem2 md2 Lam2 _ _ _ k' (56 * cap2 cap) HMR2 HL2 HK2) as (KR1 & KR2 & _).
    assert (HN2c : NoDup (map fst Lam2)).
    { pose proof HL2 as (_ & _ & _ & _ & HND & _).
      first [exact HND | apply NoDup_ListNoDup; exact HND | apply NoDup_ListNoDup in HND; exact HND]. }
    assert (Hfdo : pj_fd (ms_segs B) mem2 (lin Lam2) (S dd) o ((k', 56 * cap2 cap) :: keys_blk 6 keys cap ++ Di0)).
    { assert (HO1' : pis_open (ms_segs B) m1 (lin Lam) o true num kids keys cap (Z.of_nat (length (map snd ms)))
          (map snd ms) (map fst ms) Di0) by (rewrite length_map, <- En; exact HO1).
      assert (HHm2' : pj_hdr (ms_segs B) mem2 o 6 num 0 k' keys (Z.of_nat (length (map snd ms))) cap)
        by (rewrite length_map, <- En; exact HHm2).
      apply (pis_grow_half_fd (ms_segs B) m1 mem2 Lam Lam2 Lam0 o num kids keys cap (map snd ms) (map fst ms) Di0 k' dd
        HO1' (ps_depth_items ms dd Hdo) HP0 HP0' HN2c Hmk Hmy HHm2').
      - lia.
      - lia.
      - rewrite length_map. lia.
      - intros i Hi. rewrite length_map in Hi. apply (present_writable B).
        exact (ledger_block_present B API L2 A2 mem2 md2 Lam2 _ _ _ k' (56 * cap2 cap) i HMR2 HL2 HK2 ltac:(lia)).
      - exact HDi.
      - intros bb x Hb Hx Hx'. rewrite length_map in Hx'. destruct bb as (a & kk).
        unfold pj_holds in Hx; cbn [fst snd] in Hx.
        assert (Hne : (a, kk) <> (k', 56 * cap2 cap)).
        { intros E. injection E as E1 E2. subst a kk.
          pose proof HL as (_ & _ & _ & _ & _ & HF0). rewrite Forall_forall in HF0.
          destruct (HF0 _ (HDL _ _ (HDi0D _ Hb))) as (_ & Hbb & _). cbn [fst snd] in Hbb.
          exact (Hnew' k' (56 * cap2 cap) (or_introl eq_refl) Hbb). }
        destruct (g_lam_disj B API L2 A2 mem2 md2 Lam2 _ _ _ a kk k' (56 * cap2 cap) HMR2 HL2
          (Lam0Lam2 a kk (DiLam0 a kk Hb)) HK2 Hne); lia.
      - intros bb x Hb Hx Hxo. cbn [In] in Hb. destruct Hb as [E|[]]. subst bb.
        unfold pj_holds in Hx; cbn [fst snd] in Hx.
        destruct (HNEW o ro rko k' (56 * cap2 cap) x (proj1 HVo) (proj1 HVo2) HK2
          (Hnew' k' (56 * cap2 cap) (or_introl eq_refl)) Hx); lia. }
    assert (HADo : pj_apart ((k', 56 * cap2 cap) :: keys_blk 6 keys cap ++ Di0) w).
    { intros bb x Hb Hx Hxw. destruct Hb as [E|Hb].
      - subst bb. unfold pj_holds in Hx; cbn [fst snd] in Hx.
        destruct (HNEW w rw rkw k' (56 * cap2 cap) x (proj1 HVw) (proj1 HVw2) HK2
          (Hnew' k' (56 * cap2 cap) (or_introl eq_refl)) Hx); lia.
      - apply (HWD x Hxw). right. exists bb. split; [|exact Hx]. rewrite ED'.
        apply in_app_or in Hb. destruct Hb as [Hb|Hb]; apply in_or_app;
          [left; apply in_or_app; right; exact Hb | right; exact Hb]. }
    assert (HPL2 : Permutation Lam2 (((k', 56 * cap2 cap) :: keys_blk 6 keys cap ++ Di0) ++ Dw ++ Lr)).
    { apply (Permutation_trans HP0'). cbn [app]. apply perm_skip. rewrite <- app_assoc. exact HL0. }
    assert (Hlen : Z.of_nat (length ((k', 56 * cap2 cap) :: keys_blk 6 keys cap ++ Di0)) =
        Z.of_nat (length D) + nlive (firstn (2 - 1) (set_trace cap cap (Z.of_nat (length kname))))).
    { change (2 - 1)%nat with 1%nat. rewrite N1, ED'. cbn [length]. rewrite !length_app. lia. }
    assert (Hsum : lsum ((k', 56 * cap2 cap) :: keys_blk 6 keys cap ++ Di0) =
        lsum D + held (firstn (2 - 1) (set_trace cap cap (Z.of_nat (length kname))))).
    { change (2 - 1)%nat with 1%nat. rewrite Th1, ED'. cbn [lsum]. rewrite !g_lsum_app.
      rewrite (st_kids_lsum kids cap ltac:(lia)). lia. }
    exact (fail_arm B API F HFREE L A regs mem md Lam peak cnt fail b o k w ms tv D Dw kids keys cap cap kname dd lo
      L2 A2 regs3 mem2 md2 Lam2 junk ro rko rw rkw 2%nat Lr ((k', 56 * cap2 cap) :: keys_blk 6 keys cap ++ Di0)
      (kids_blk kids cap) [(k', 56 * cap2 cap)] (keys_blk 6 keys cap ++ Di0) (S dd) HE0 HPo HPw HWD HAw HDJ0 Hlo Hax
      HElo Hlw Hnin' HPL HR3 HL1' Hres1 Hrd2 FR2 G3_1 G3_2 G3_10 Gk3 Hw0 Hfdw HVw2 HVo2 HPL2 Hfdo
      ltac:(rewrite Tl3; intros E; exfalso; lia) HADo ltac:(rewrite Tl3; lia) ltac:(lia) Hlen Hsum
      ltac:(rewrite ED'; rewrite <- app_assoc; apply Permutation_refl) (Permutation_refl _) Hnew'
      (or_intror (or_introl (conj eq_refl (conj eq_refl (conj eq_refl (ex_intro _ k' eq_refl))))))).
  -
    destruct ARM as (Heq & Hcf & _ & Hc1 & Er & (k' & y' & Lam0 & Hk'0 & Hk'16 & Hy'0 & Hy'16 & Hnew' & HP0 & HP0' &
      Ep & Ec & Ef & Eb & Hmk & Hmy & HHm2 & HSL2)).
    subst peak2 cnt2 fail2 b2 res. rewrite Heq in *. clear Heq.
    apply (sc_go B API L2 A2 regs2 mem2 md2 0 k w _ HSEG HMR2 G2_10 (or_introl eq_refl) G2_8 G2_18); [|intros E; lia].
    intros _ regs3 G3_1 G3_10 G3k.
    destruct (HREG regs3 G3k) as (G3_2 & G3_8 & G3_9 & Gk3).
    destruct (st_eq_run F b cap (Z.of_nat (length kname)) ltac:(lia) ltac:(lia))
      as (Tl3 & Tr0 & Tr1 & Tr2 & Trf & Th0 & Th1 & Th2 & Thf).
    destruct (st_eq_nl cap (Z.of_nat (length kname)) kids keys ltac:(lia)) as (z0 & Lk & Ly & N0 & N1 & N2 & Nf).
    pose proof (st_cap2 cap ltac:(lia)) as (C1 & C2).
    destruct (st_eq_room F b cap (Z.of_nat (length kname)) ltac:(lia) ltac:(lia) Hroom) as (R1 & R2 & R3 & R4 & R5).
    assert (HL0 : Permutation Lam0 (Di0 ++ Dw ++ Lr)).
    { assert (E0 : Permutation ((kids_blk kids cap ++ keys_blk 6 keys cap) ++ Lam0)
          ((kids_blk kids cap ++ keys_blk 6 keys cap) ++ Di0 ++ Dw ++ Lr)).
      { rewrite <- !app_assoc. apply (Permutation_trans (Permutation_sym HP0)). apply (Permutation_trans HPL).
        rewrite ED'. rewrite <- !app_assoc. apply Permutation_refl. }
      exact (Permutation_app_inv_l _ _ _ E0). }
    assert (Lam0Lam2 : forall a kk, In (a, kk) Lam0 -> In (a, kk) Lam2)
      by (intros a kk H; apply (Permutation_in _ (Permutation_sym HP0')); right; right; exact H).
    assert (HK2 : In (k', 56 * cap2 cap) Lam2)
      by (apply (Permutation_in _ (Permutation_sym HP0')); right; left; reflexivity).
    assert (HY2 : In (y', 8 * cap2 cap) Lam2)
      by (apply (Permutation_in _ (Permutation_sym HP0')); left; reflexivity).
    assert (DwLam0 : forall a kk, In (a, kk) Dw -> In (a, kk) Lam0).
    { intros a kk Hb. apply (Permutation_in _ (Permutation_sym HL0)). apply in_or_app; right. apply in_or_app; left.
      exact Hb. }
    assert (DiLam0 : forall a kk, In (a, kk) Di0 -> In (a, kk) Lam0).
    { intros a kk Hb. apply (Permutation_in _ (Permutation_sym HL0)). apply in_or_app; left. exact Hb. }
    assert (Hnk : ~ In (k' - 16, 56 * cap2 cap + 16) (blocks L A))
      by exact (Hnew' k' (56 * cap2 cap) (or_intror (or_introl eq_refl))).
    assert (Hny : ~ In (y' - 16, 8 * cap2 cap + 16) (blocks L A)) by exact (Hnew' y' (8 * cap2 cap) (or_introl eq_refl)).
    assert (Hsub : forall a kk, In (a, kk) Lam2 -> In (a, kk) Lam \/ ~ In (a - 16, kk + 16) (blocks L A)).
    { intros a kk Hin. apply (Permutation_in _ HP0') in Hin. destruct Hin as [E|[E|Hin]].
      - right. injection E as <- <-. exact Hny.
      - right. injection E as <- <-. exact Hnk.
      - left. apply (Permutation_in _ (Permutation_sym HP0)). apply in_or_app. right. apply in_or_app. right. exact Hin. }
    pose proof (vplace_rp B API L A Lam (spZ regs) w rw rkw GROW_K regs1 m1 md _ _ L2 A2 regs2 mem2 md2 Lam2 _ _ _
      HVw HR2 Hngw HL2 Hsub) as HVw2.
    pose proof (vplace_rp B API L A Lam (spZ regs) o ro rko GROW_K regs1 m1 md _ _ L2 A2 regs2 mem2 md2 Lam2 _ _ _
      HVo HR2 Hngo HL2 Hsub) as HVo2.
    assert (HLg : ledger B L2 A2 mem2 Lam2 (Z.max peak (lsum Lam2)) (cnt + Z.of_nat 2) fail).
    { assert (E1 : lsum Lam = 56 * cap + 8 * cap + lsum Lam0).
      { rewrite (g_lsum_perm _ _ HP0), !g_lsum_app.
        rewrite (st_kids_lsum kids cap ltac:(lia)), (st_keys_lsum keys cap ltac:(lia)). lia. }
      assert (E2 : lsum Lam2 = 8 * cap2 cap + 56 * cap2 cap + lsum Lam0)
        by (rewrite (g_lsum_perm _ _ HP0'); cbn [lsum]; lia).
      replace (Z.max peak (lsum Lam2)) with (Z.max peak (Z.max (lsum Lam + 56 * (cap2 cap - cap)) (lsum Lam2))) by lia.
      replace (cnt + Z.of_nat 2) with (cnt + 2) by lia. exact HL2. }
    assert (Hfg : ~ (cnt <= fail < cnt + Z.of_nat 2)) by lia.
    assert (Hresg : rf_ok F A2 (rf_run F b (firstn 2 (set_trace cap cap (Z.of_nat (length kname))))))
      by (rewrite Tr2; exact Hrf2).
    destruct (g_str_after B API L A regs mem md Lam peak cnt fail o w D Dw (PJ_SET_K dd) L2 A2 regs mem2 md2 k kname
      slack HSEG Herrno HMR HL HRD Hrd2 HR3 HDL HDwL HKB Hcs HKD) as (slack' & Hsl'l & HKg).
    pose proof (HNw2_of (fun a kk Hb => Lam0Lam2 a kk (DwLam0 a kk Hb))) as HNw2.
    destruct (ledger_block_range B API L2 A2 mem2 md2 Lam2 _ _ _ k' (56 * cap2 cap) HMR2 HL2 HK2) as (KR1 & KR2 & _).
    destruct (ledger_block_range B API L2 A2 mem2 md2 Lam2 _ _ _ y' (8 * cap2 cap) HMR2 HL2 HY2) as (YR1 & YR2 & _).
    assert (HN2c : NoDup (map fst Lam2)).
    { pose proof HL2 as (_ & _ & _ & _ & HND & _).
      first [exact HND | apply NoDup_ListNoDup; exact HND | apply NoDup_ListNoDup in HND; exact HND]. }
    assert (HOg : pis_open (ms_segs B) mem2 (lin Lam2) o true num k' y' (cap2 cap) cap (map snd ms) (map fst ms) Di0).
    { apply (pis_grow_obj (ms_segs B) m1 mem2 Lam Lam2 Lam0 o num kids keys cap cap (map snd ms) (map fst ms) Di0 k' y'
        HO1 HP0 HP0' HN2c Hmk Hmy HHm2 HSL2 Hlc).
      - lia.
      - lia.
      - rewrite length_map. lia.
      - intros i Hi. rewrite length_map in Hi. apply (present_writable B).
        exact (ledger_block_present B API L2 A2 mem2 md2 Lam2 _ _ _ k' (56 * cap2 cap) i HMR2 HL2 HK2 ltac:(lia)).
      - lia.
      - rewrite length_map. lia.
      - exact HDi.
      - intros bb x Hb Hx Hx'. rewrite length_map in Hx'. destruct bb as (a & kk).
        unfold pj_holds in Hx; cbn [fst snd] in Hx.
        assert (Hne : (a, kk) <> (k', 56 * cap2 cap)).
        { intros E. injection E as E1 E2. subst a kk.
          pose proof HL as (_ & _ & _ & _ & _ & HF0). rewrite Forall_forall in HF0.
          destruct (HF0 _ (HDL _ _ (HDi0D _ Hb))) as (_ & Hbb & _). cbn [fst snd] in Hbb. exact (Hnk Hbb). }
        destruct (g_lam_disj B API L2 A2 mem2 md2 Lam2 _ _ _ a kk k' (56 * cap2 cap) HMR2 HL2
          (Lam0Lam2 a kk (DiLam0 a kk Hb)) HK2 Hne); lia.
      - intros bb x Hb Hx Hxo. cbn [In] in Hb. destruct Hb as [E|[E|[]]]; subst bb;
          unfold pj_holds in Hx; cbn [fst snd] in Hx.
        + destruct (HNEW o ro rko k' (56 * cap2 cap) x (proj1 HVo) (proj1 HVo2) HK2 Hnk Hx); lia.
        + destruct (HNEW o ro rko y' (8 * cap2 cap) x (proj1 HVo) (proj1 HVo2) HY2 Hny Hx); lia. }
    assert (HPLg : Permutation Lam2 ([(k', 56 * cap2 cap); (y', 8 * cap2 cap)] ++ Di0 ++ Dw ++ Lr)).
    { apply (Permutation_trans HP0'). cbn [app]. eapply Permutation_trans; [apply perm_swap|].
      apply perm_skip. apply perm_skip. exact HL0. }
    assert (HDg : [(k', 56 * cap2 cap); (y', 8 * cap2 cap)] ++ Di0 = pis_slots true k' y' (cap2 cap) ++ Di0).
    { rewrite ps_slots_eq. rewrite (proj2 (Z.eqb_neq (cap2 cap) 0)) by lia. reflexivity. }
    assert (Hnew5 : new_blks L A [(k', 56 * cap2 cap); (y', 8 * cap2 cap)]).
    { intros a kk Hb. cbn [In] in Hb. destruct Hb as [E|[E|[]]]; injection E as <- <-; [exact Hnk | exact Hny]. }
    assert (HSE : forall a kk, In (a, kk) (pis_slots true k' y' (cap2 cap)) ->
        (forall z, a - 16 <= z < a + kk -> pj_set_writes o w D Dw z) \/ ~ In (a - 16, kk + 16) (blocks L A)).
    { intros a kk Hb. right. apply Hnew5. rewrite ps_slots_eq in Hb.
      rewrite (proj2 (Z.eqb_neq (cap2 cap) 0)) in Hb by lia. exact Hb. }
    assert (HAPw : pj_apart (pis_slots true k' y' (cap2 cap) ++ Di0) w).
    { rewrite <- HDg. intros bb x Hb Hx Hxw. cbn [app In] in Hb. destruct Hb as [E|[E|Hb]].
      - subst bb. unfold pj_holds in Hx; cbn [fst snd] in Hx.
        destruct (HNEW w rw rkw k' (56 * cap2 cap) x (proj1 HVw) (proj1 HVw2) HK2 Hnk Hx); lia.
      - subst bb. unfold pj_holds in Hx; cbn [fst snd] in Hx.
        destruct (HNEW w rw rkw y' (8 * cap2 cap) x (proj1 HVw) (proj1 HVw2) HY2 Hny Hx); lia.
      - apply (HWD x Hxw). right. exists bb. split; [exact (HDi0D _ Hb) | exact Hx]. }
    assert (Hlenh : Z.of_nat (length ([(k', 56 * cap2 cap); (y', 8 * cap2 cap)] ++ Di0)) =
        Z.of_nat (length D) + nlive (firstn 2 (set_trace cap cap (Z.of_nat (length kname))))).
    { rewrite N2, ED'. rewrite !length_app. cbn [length]. lia. }
    assert (Hsumh : lsum ([(k', 56 * cap2 cap); (y', 8 * cap2 cap)] ++ Di0) =
        lsum D + held (firstn 2 (set_trace cap cap (Z.of_nat (length kname))))).
    { rewrite Th2, ED'. rewrite !g_lsum_app. cbn [lsum].
      rewrite (st_kids_lsum kids cap ltac:(lia)), (st_keys_lsum keys cap ltac:(lia)). lia. }
    exact (ok_arm B API F HFREE HSD AX HMC HMS L A regs mem md Lam peak cnt fail b o k w ms tv D Dw num kids keys cap cap
      kname slack' dd lo L2 A2 regs3 mem2 md2 Lam2 junk 2%nat k' y' (cap2 cap) Di0 Lr
      (kids_blk kids cap ++ keys_blk 6 keys cap) [(k', 56 * cap2 cap); (y', 8 * cap2 cap)] Di0 ro rko rw rkw HE0 HPo Hw0
      HPw HWD HAw Hdt Hkn ltac:(rewrite Hsl'l; exact Hsl) Hcs1 HKD HDJ0 Hcnt Hlo Hax HElo Hlw Hnin HPL HDD HR3 HLg Hfg
      Hresg Hrd2 FR2 G3_1 G3_2 G3_10 G3_8 G3_9 Gk3 HKg HNw2 HVw2 HVo2 HOg En ltac:(lia) HPLg HDg
      ltac:(rewrite ED'; apply Permutation_refl) Hnew5 HSE HAPw
      (or_intror (conj eq_refl (conj eq_refl (conj eq_refl (ex_intro _ k' (ex_intro _ y' eq_refl)))))) Hlenh Hsumh
      Tl3 ltac:(rewrite Trf, Tr2; reflexivity) ltac:(rewrite Nf, N2; reflexivity) ltac:(rewrite Thf, Th2; lia)
      ltac:(rewrite Tr2; exact R4) R5 Ho0).
Qed.

End G2.
