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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog.CF Require Import pj_free_c fuzz_strdup_c grow_c pj_set_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog.CF Require Import pj_set_tail pj_set_post pj_set_fail pj_set_ok.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog.CF Require Import CFS ContractCF KindBGlueCF FrameCF ReaderResCF.
Import YM05.
Import ListNotations.
Local Open Scope Z_scope.

Section M.
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

Lemma g_wr_of_mbyte : ms_segs B = rsegs -> forall m x, 0 <= x < 2 ^ 64 -> ~ in_img B x ->
  mbyte (ms_segs B) m x <> None -> writable_at (ms_segs B) m x.
Proof.
  intros HSEG m x Hx Hn H. unfold mbyte in H. destruct (m (Z_to_bv 64 x)) as [bb|] eqn:E.
  - apply (present_writable B). exists bb. exact E.
  - exfalso. apply H. apply MemNorm.seg_rom_unmapped. rewrite unsigned_lit by lia.
    destruct (find_segment (ms_segs B) x 1) as [seg|] eqn:Fs; [|reflexivity].
    exfalso. exact (Hn (g_seg_img B HSEG x seg Fs)).
Qed.

Lemma g_blk_mbyte : forall L A mem md a k x, aa_MR API L A mem md -> In (a, k) (blocks L A) -> a <= x < a + k ->
  mbyte (ms_segs B) mem x <> None.
Proof.
  intros L A mem md a k x HM Hin Hx. destruct (g_blocks_user L A a k Hin) as (q & Hq & Eq).
  destruct (mr_blocks _ _ (aa_laws API) _ _ _ _ q k (x - a) HM Hq ltac:(lia)) as ((bb & Hb) & _).
  rewrite Eq in Hb. replace (a + (x - a)) with x in Hb by lia. unfold mbyte. rewrite Hb. discriminate.
Qed.

Lemma g_bytes_some : forall m a bs x, Mem.bytes_at (ms_segs B) m a bs -> a <= x < a + Z.of_nat (length bs) ->
  mbyte (ms_segs B) m x <> None.
Proof.
  intros m a bs x (_ & _ & H) Hx.
  pose proof (H (Z.to_nat (x - a)) ltac:(lia)) as Hn.
  replace (a + Z.of_nat (Z.to_nat (x - a))) with x in Hn by lia.
  rewrite <- t_mbyte_mrd in Hn. rewrite Hn. intros E. apply nth_error_None in E. lia.
Qed.

Lemma g_str_after : forall L A regs mem md Lam peak cnt fail o w D Dw K L2 A2 regs2 mem2 md2 k kname slack,
  ms_segs B = rsegs -> errno_addr B = strtod_c.STRTOD_ERRNO ->
  aa_MR API L A mem md -> ledger B L A mem Lam peak cnt fail -> rd_cells B mem -> rd_cells B mem2 ->
  rpost B API K L A regs mem md (pj_set_writes o w D Dw) (freed (D ++ Dw)) L2 A2 regs2 mem2 md2 ->
  (forall a k0, In (a, k0) D -> In (a, k0) Lam) -> (forall a k0, In (a, k0) Dw -> In (a, k0) Lam) ->
  Mem.bytes_at (ms_segs B) mem k (kname ++ Z_to_bv 8 0 :: slack) ->
  cstr_ok B Lam k (Z.of_nat (length kname) + 1 + Z.of_nat (length slack)) ->
  (forall x, k <= x < k + Z.of_nat (length kname) + 1 -> ~ pj_foot o D x /\ ~ pj_foot w Dw x) ->
  exists slack', length slack' = length slack /\ Mem.bytes_at (ms_segs B) mem2 k (kname ++ Z_to_bv 8 0 :: slack').
Proof.
  intros L A regs mem md Lam peak cnt fail o w D Dw K L2 A2 regs2 mem2 md2 k kname slack HSEG Herrno HM HL HRD HRD2
    HR HDL HDwL HKB Hcs HKD.
  pose proof HR as (HM2 & _).
  pose proof HKB as (Hk0 & Hk1 & _). rewrite length_app in Hk1. cbn [length] in Hk1.
  pose proof HKB as HKB0.
  replace (kname ++ Z_to_bv 8 0 :: slack) with ((kname ++ [Z_to_bv 8 0]) ++ slack) in HKB
    by (rewrite <- app_assoc; reflexivity).
  apply bytes_at_app in HKB. destruct HKB as (HK1 & _).
  assert (HE : forall x, k <= x < k + Z.of_nat (length kname) + 1 + Z.of_nat (length slack) ->
      mbyte (ms_segs B) mem2 x <> None /\
      (x < k + Z.of_nat (length kname) + 1 -> mbyte (ms_segs B) mem2 x = mbyte (ms_segs B) mem x)).
  { intros x Hx. destruct Hcs as [Hro|(a & kk & Hl & H1 & H2)].
    - assert (Hrx : ro_addr (ms_segs B) (Z_to_bv 64 x) = true)
        by (replace x with (k + (x - k)) by lia; apply Hro; lia).
      assert (Eq : mbyte (ms_segs B) mem2 x = mbyte (ms_segs B) mem x).
      { pose proof (proj1 HRD2 _ Hrx) as E2. pose proof (proj1 HRD _ Hrx) as E1.
        transitivity (seg_rom (ms_segs B) (Z_to_bv 64 x)); [exact E2 | symmetry; exact E1]. }
      split; [|intros _; exact Eq]. rewrite Eq.
      apply (g_bytes_some mem k _ x HKB0). rewrite length_app. cbn [length]. lia.
    - unfold lin in Hl.
      assert (HnD : ~ In (a, kk) D).
      { intros Hb. apply (proj1 (HKD k ltac:(lia))). right. exists (a, kk). split; [exact Hb|].
        unfold pj_holds; cbn [fst snd]; lia. }
      assert (HnDw : ~ In (a, kk) Dw).
      { intros Hb. apply (proj2 (HKD k ltac:(lia))). right. exists (a, kk). split; [exact Hb|].
        unfold pj_holds; cbn [fst snd]; lia. }
      pose proof HL as (_ & _ & _ & _ & _ & HF). rewrite Forall_forall in HF.
      destruct (HF _ Hl) as (Hkk & Hb & _). cbn [fst snd] in Hkk, Hb.
      assert (Hng : ~ freed (D ++ Dw) (a - 16) (kk + 16)).
      { unfold freed. replace (a - 16 + 16) with a by lia. replace (kk + 16 - 16) with kk by lia.
        intros Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin]; [exact (HnD Hin) | exact (HnDw Hin)]. }
      pose proof (rp_blk_kept B API _ _ _ _ _ _ _ _ _ _ _ _ _ (a - 16) (kk + 16) HR Hb Hng) as Hb2.
      split; [exact (g_blk_mbyte L2 A2 mem2 md2 (a - 16) (kk + 16) x HM2 Hb2 ltac:(lia))|].
      intros Hx'.
      refine (proj1 (rp_same_blk B API _ _ _ _ _ _ _ _ _ _ _ _ _ (a - 16) (kk + 16) x HR Hb Hng ltac:(lia) _)).
      intros [Ho|[Hw|[(a0 & k0 & Hin0 & Hx0)|Hs]]].
      + exact (proj1 (HKD x ltac:(lia)) (or_introl Ho)).
      + exact (proj2 (HKD x ltac:(lia)) (or_introl Hw)).
      + assert (HinL0 : In (a0, k0) Lam).
        { apply in_app_or in Hin0. destruct Hin0 as [H0|H0]; [exact (HDL _ _ H0) | exact (HDwL _ _ H0)]. }
        assert (Hne : (a, kk) <> (a0, k0)).
        { intros E. apply in_app_or in Hin0. rewrite <- E in Hin0.
          destruct Hin0 as [H0|H0]; [exact (HnD H0) | exact (HnDw H0)]. }
        destruct (g_lam_disj B API L A mem md Lam peak cnt fail a kk a0 k0 HM HL Hl HinL0 Hne); lia.
      + apply (ledger_block_not_img B L A mem Lam peak cnt fail a kk (x - a) HL Hl ltac:(lia)).
        replace (a + (x - a)) with x by lia. exact (g_img_consts B HSEG Herrno x (or_introl Hs)). }
  destruct (g_bytes_old B mem2 (k + Z.of_nat (length kname) + 1) (Z.of_nat (length slack)) ltac:(lia) ltac:(lia)
    ltac:(lia)) as (bs & Hbl & BS).
  { intros i Hi. exact (proj1 (HE (k + Z.of_nat (length kname) + 1 + i) ltac:(lia))). }
  exists bs. split; [lia|].
  replace (kname ++ Z_to_bv 8 0 :: bs) with ((kname ++ [Z_to_bv 8 0]) ++ bs) by (rewrite <- app_assoc; reflexivity).
  apply bytes_at_app. split.
  - apply (g_bytes B mem mem2 k _ HK1). intros x Hx. rewrite length_app in Hx. cbn [length] in Hx.
    exact (proj2 (HE x ltac:(lia)) ltac:(lia)).
  - rewrite length_app. cbn [length].
    replace (k + Z.of_nat (length kname + 1)) with (k + Z.of_nat (length kname) + 1) by lia. exact BS.
Qed.

Lemma sc_go : forall L2 A2 regs2 mem2 md2 res k w (P : config -> Prop),
  ms_segs B = rsegs -> aa_MR API L2 A2 mem2 md2 ->
  getr regs2 10 = Z_to_bv 64 res -> (res = 0 \/ res = -1) -> getr regs2 8 = Z_to_bv 64 w ->
  getr regs2 18 = Z_to_bv 64 k ->
  (res = 0 -> forall regs3, getr regs3 1 = Z_to_bv 64 PS_SD_RET -> getr regs3 10 = Z_to_bv 64 k ->
     (forall r, r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ 18 <= r <= 27 ->
        getr regs3 (Z_to_bv 5 r) = getr regs2 (Z_to_bv 5 r)) ->
     SR (ms_segs B) (mkCfg (YK11.mkst regs3 (Z_to_bv 64 PS_STRDUP) mem2 (YK11.seg_rom (ms_segs B))) md2) P) ->
  (res = -1 -> forall regs3, getr regs3 1 = Z_to_bv 64 PS_FREEW_RET -> getr regs3 10 = Z_to_bv 64 w ->
     (forall r, r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ 18 <= r <= 27 ->
        getr regs3 (Z_to_bv 5 r) = getr regs2 (Z_to_bv 5 r)) ->
     SR (ms_segs B) (mkCfg (YK11.mkst regs3 (Z_to_bv 64 PS_PJ_FREE) mem2 (YK11.seg_rom (ms_segs B))) md2) P) ->
  SR (ms_segs B) (mkCfg (YK11.mkst regs2 (Z_to_bv 64 PS_GROW_RET) mem2 (YK11.seg_rom (ms_segs B))) md2) P.
Proof.
  intros L2 A2 regs2 mem2 md2 res k w P HSEG HM G10 HR G8 G18 K0 K1.
  destruct (kb_md B API L2 A2 mem2 md2 HM) as (Hh & Hz).
  apply (kb_run B regs2 _ mem2 md2
    (fun R pc' mem' => sc_post (getr regs2 2) (getr regs2 3) (getr regs2 4) (getr regs2 8) (getr regs2 9)
       (getr regs2 18) (getr regs2 19) (getr regs2 20) (getr regs2 21) (getr regs2 22) (getr regs2 23) (getr regs2 24)
       (getr regs2 25) (getr regs2 26) (getr regs2 27) fp_regs fp_csr mem2 res k w
       (MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs))) _ Hh Hz).
  { unfold rmk. rewrite HSEG. eapply evt_mono.
    - apply (ps_sc (getr regs2 1) (getr regs2 2) (getr regs2 3) (getr regs2 4) (getr regs2 5) (getr regs2 6)
        (getr regs2 7) (getr regs2 8) (getr regs2 9) (getr regs2 10) (getr regs2 11) (getr regs2 12) (getr regs2 13)
        (getr regs2 14) (getr regs2 15) (getr regs2 16) (getr regs2 17) (getr regs2 18) (getr regs2 19)
        (getr regs2 20) (getr regs2 21) (getr regs2 22) (getr regs2 23) (getr regs2 24) (getr regs2 25)
        (getr regs2 26) (getr regs2 27) (getr regs2 28) (getr regs2 29) (getr regs2 30) (getr regs2 31)
        fp_regs fp_csr mem2 res k w G10 HR G8 G18).
    - intros ms Hp. pose proof Hp as Hp'.
      destruct Hp' as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & [(_ & ->)|(_ & ->)]);
        (do 3 eexists; split; [reflexivity | exact Hp]). }
  intros R pc3 mem3 regs3 HK3 Hg3.
  destruct HK3 as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & [(Hr & E3)|(Hr & E3)]);
    pose proof (f_equal ms_regs E3) as ER; pose proof (f_equal ms_pc_val E3) as EP; pose proof (f_equal ms_mem E3) as EM;
    cbn [ms_regs ms_pc_val ms_mem MS] in ER, EP, EM; subst R pc3 mem3; clear E3.
  - apply (K0 Hr regs3); [rewrite Hg3; reflexivity | rewrite Hg3; reflexivity |].
    intros r Hr'.
    assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
      r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct Hc as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]]; rewrite Hg3; reflexivity.
  - apply (K1 Hr regs3); [rewrite Hg3; reflexivity | rewrite Hg3; reflexivity |].
    intros r Hr'.
    assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
      r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct Hc as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]]; rewrite Hg3; reflexivity.
Qed.

End M.
