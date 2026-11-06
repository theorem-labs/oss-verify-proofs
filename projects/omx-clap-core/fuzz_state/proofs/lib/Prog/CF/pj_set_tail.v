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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import pj_set_runs pj_set_shape.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog.CF Require Import pj_set_kb.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import memcpy_c memset_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog.CF Require Import pj_free_c pj_set_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog.CF Require Import CFS ContractCF KindBGlueCF FrameCF ReaderResCF.
Import YM05.
Import ListNotations.
Local Open Scope Z_scope.

Lemma t_sk : forall dd, 48 + PJ_FREE_K dd <= PJ_SET_K dd /\ 48 + GROW_K <= PJ_SET_K dd /\
  48 + STRDUP_K <= PJ_SET_K dd /\ 96 <= PJ_SET_K dd /\ 0 <= PJ_FREE_K dd.
Proof.
  intros dd. unfold PJ_SET_K, PJ_FREE_K, PJ_GET_K, PJ_SET_F, PJ_FREE_F, PJ_GET_F, GROW_K, GROW_F, REALLOC_K,
    STRDUP_K, FREE_K, REALLOC_STACK, ALLOC_STACK. lia.
Qed.

Lemma se_shape : forall ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m ms,
  se_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m ms ->
  exists R pc' m', ms = MS R F pc' fc None m' (seg_rom rsegs).
Proof. intros until ms. intros (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & ->). do 3 eexists. reflexivity. Qed.

Section T.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Hypothesis HFREE : pj_free_contract B API F.
Hypothesis AX : YL01.AllocExtra B (aa_MR API).
Hypothesis HMC : memcpy_contract.
Hypothesis HMS : memset_contract.

Local Notation getr := YK11.getr.

Lemma tail_w : forall L A regs mem md (dd : nat) E G L1 A1 mem1 md1 regs1 Lam1 peak1 cnt1 fail1 b1 w Dw junk lo
    (P : config -> Prop),
  reader_env B API (PJ_SET_K dd) L A regs mem md ->
  rpost B API (PJ_SET_K dd) L A regs mem md E G L1 A1 regs mem1 md1 ->
  spZ regs <= lo -> (st_init_done A = false -> auxv_pre B (ly_sec L) lo mem) -> (forall x, E x -> x < lo) ->
  (forall p n i, In (p, n) (user_blocks A) -> 0 <= i < n -> G (ptr_addr L p) n -> E (ptr_addr L p + i)) ->
  getr regs1 1 = Z_to_bv 64 PS_FREEW_RET -> getr regs1 2 = Z_to_bv 64 (spZ regs - 48) ->
  getr regs1 10 = Z_to_bv 64 w ->
  (forall r, r = 3 \/ r = 4 \/ 20 <= r <= 27 -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
  rw_cells (ms_segs B) mem1 (spZ regs - 48)
    [CB 8 junk; C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)] ->
  ledger B L1 A1 mem1 Lam1 peak1 cnt1 fail1 -> rf_ok F A1 b1 -> rd_cells B mem1 ->
  w <> 0 -> pj_fd (ms_segs B) mem1 (lin Lam1) dd w Dw -> rplace B L1 A1 Lam1 regs1 mem1 w ->
  (forall a k, In (a, k) Dw -> In (a, k) Lam1) ->
  Frame.disjoint_from [(w, w + 56)] (spZ regs - PJ_SET_K dd) (PJ_SET_K dd) ->
  (forall x, pj_free_writes w Dw x -> E x) -> (forall a n, freed Dw a n -> G a n) ->
  (forall L' A' regs' mem' md' Lam' regs2,
     rpost B API (PJ_SET_K dd) L A regs mem md E G L' A' regs' mem' md' ->
     rpost B API (PJ_FREE_K dd) L1 A1 regs1 mem1 md1 (pj_free_writes w Dw) (freed Dw) L' A' regs2 mem' md' ->
     rd_cells B mem' -> getr regs' 10 = Z_to_bv 64 (-1) ->
     ledger B L' A' mem' Lam' peak1 cnt1 fail1 -> (exists D', Permutation Dw D' /\ rf_ok F A' (rf_frees F b1 D')) ->
     Permutation Lam1 (Dw ++ Lam') -> pj_zero (ms_segs B) mem' w ->
     P (mkCfg (YK11.mkst regs' (getr regs 1) mem' (YK11.seg_rom (ms_segs B))) md')) ->
  SR (ms_segs B) (mkCfg (YK11.mkst regs1 (Z_to_bv 64 PJ_FREE) mem1 (YK11.seg_rom (ms_segs B))) md1) P.
Proof.
  intros L A regs mem md dd E G L1 A1 mem1 md1 regs1 Lam1 peak1 cnt1 fail1 b1 w Dw junk lo P
    HE HR1 Hlo Hax HElo HGE G1 G2 G10 Gk FR HL1 Hres1 Hrd1 Hw0 Hfd Hpl HDL HD HWE HWG HK.
  destruct HE as (HSEG & Htp & Herrno & Hgot & Hguard & Hpre & Hsp47 & Hglob & Hfrm & HRD).
  pose proof (g_img B HSEG) as HIL.
  pose proof Hpre as (HMR & HWF & Hbd & Hra & Hsp16 & Hspc & Hsp63 & Hstk & Htpr & Herr & Haux).
  pose proof alloc_ceiling_value as Hceil.
  pose proof (t_sk dd) as (Kf & Kg & Ks & K96 & Kf0).
  unfold strtod_c.STRTOD_GLOBALS_TOP in Hglob.
  pose proof (bv_unsigned_in_range 64 (getr regs 2)) as HSPr. unfold bv_modulus in HSPr.
  assert (HSP : bv_unsigned (getr regs 2) = spZ regs) by reflexivity.
  assert (Hs1 : spZ regs1 = spZ regs - 48) by (unfold spZ at 1; rewrite G2, unsigned_lit by lia; reflexivity).
  assert (Herr4 : errno_addr B + 4 <= spZ regs - PJ_SET_K dd) by (rewrite Herrno; unfold strtod_c.STRTOD_ERRNO; lia).
  cbn [Frame.disjoint_from] in HD.
  assert (HDw : forall x, blk_set Dw x -> 0 <= x < alloc_ceiling).
  { intros x (a & k & Hin & Hx). pose proof (HDL a k Hin) as HinL.
    pose proof HR1 as (HM1 & _).
    pose proof (ledger_block_range B API L1 A1 mem1 md1 Lam1 peak1 cnt1 fail1 a k HM1 HL1 HinL). lia. }
  assert (HW1 : forall x, pj_free_writes w Dw x -> w <= x < w + 56 \/ 0 <= x < alloc_ceiling).
  { intros x (_ & [Hx|[Hx|Hx]]); [left; exact Hx | right; exact (HDw x Hx) |].
    right. unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Hx. lia. }
  assert (Hpre1 : call_pre_k B (aa_MR API) (PJ_FREE_K dd) L1 A1 regs1 mem1 md1).
  { apply (g_pre_k B API _ L A regs mem md E G L1 A1 mem1 md1 regs1 _ lo Hpre HR1).
    - rewrite G1. unfold YK0s.ret_ok. apply bv_eq. vm_compute. reflexivity.
    - rewrite Hs1. replace (spZ regs - 48) with (spZ regs + (-3) * 16) by lia. rewrite Z_mod_plus_full. exact Hsp16.
    - lia.
    - lia.
    - lia.
    - exact (Gk 4 ltac:(lia)).
    - lia.
    - exact Hlo.
    - exact Hax.
    - exact HElo. }
  assert (HE1 : reader_env B API (PJ_FREE_K dd) L1 A1 regs1 mem1 md1).
  { split; [exact HSEG|]. split; [exact Htp|]. split; [exact Herrno|]. split; [exact Hgot|]. split; [exact Hguard|].
    split; [exact Hpre1|]. split; [lia|]. split; [unfold strtod_c.STRTOD_GLOBALS_TOP; lia|].
    split; [exact Hfrm | exact Hrd1]. }
  eapply SR_bind; [apply (HFREE L1 A1 regs1 mem1 md1 Lam1 peak1 cnt1 fail1 b1 w dd Dw HE1 HL1 Hres1 G10) |].
  { right. split; [exact Hw0|]. split; [exact Hfd|]. split; [exact Hpl|].
    cbn [Frame.disjoint_from]. lia. }
  intros cc2 HC2.
  destruct HC2 as (L2 & A2 & regs2 & mem2 & md2 & Lam2 & -> & HR2 & Hrd2 & HP2 & HL2 & Hres2 & _ & Hz2).
  pose proof HR2 as (HMR2 & _ & _ & _ & _ & _ & _ & _ & _ & Hp12 & _).
  assert (HR3 : rpost B API (PJ_SET_K dd) L A regs mem md E G L2 A2 regs mem2 md2).
  { apply (rp_rec B API (PJ_SET_K dd) L A regs mem md E G L1 A1 mem1 md1 (PJ_FREE_K dd) regs1 (pj_free_writes w Dw) (freed Dw)
      L2 A2 regs2 mem2 md2 HWF ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HR1 HR2).
    - intros a _ _ Ha. exact (HWE a Ha).
    - intros a _ _ Ha. exact (HWE a Ha).
    - intros p n i _ _ _ Ha. exact (HWE _ Ha).
    - intros p n _ _ Hg. exact (HWG _ _ Hg).
    - exact HGE.
    - intros a Ha _ Hw. destruct (HW1 a Hw); lia. }
  assert (FR2 : rw_cells (ms_segs B) mem2 (spZ regs - 48)
    [CB 8 junk; C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)]).
  { apply (g_rw_cells B mem1); [exact FR|].
    intros x Hx. cbn [cells_size csize Nat.add] in Hx.
    refine (rp_same_hi B API _ _ _ _ _ _ _ _ _ _ _ _ _ x HR2 ltac:(lia) _ _).
    - unfold scratch_k. lia.
    - intros Hw. destruct (HW1 x Hw); lia. }
  assert (G2' : getr regs2 2 = Z_to_bv 64 (bv_unsigned (getr regs 2) + -48)).
  { transitivity (getr regs1 (Z_to_bv 5 2)); [apply (Hp12 2); unfold callee_saved; lia|].
    transitivity (Z_to_bv 64 (spZ regs - 48)); [exact G2 | f_equal; rewrite HSP; lia]. }
  rewrite G1.
  destruct (kb_md B API L2 A2 mem2 md2 HMR2) as (Hh2 & Hz2').
  apply (kb_run B regs2 _ mem2 md2
    (fun R pc' mem' => se_post (getr regs 1) (getr regs 2) (getr regs2 3) (getr regs2 4) (getr regs 8) (getr regs 9)
       (getr regs 18) (getr regs 19) (getr regs2 20) (getr regs2 21) (getr regs2 22) (getr regs2 23) (getr regs2 24)
       (getr regs2 25) (getr regs2 26) (getr regs2 27) fp_regs fp_csr mem2
       (MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs))) _ Hh2 Hz2').
  { unfold rmk. rewrite HSEG. eapply evt_mono.
    - apply (ps_se (getr regs2 1) (getr regs2 2) (getr regs 2) (getr regs2 3) (getr regs2 4) (getr regs2 5)
        (getr regs2 6) (getr regs2 7) (getr regs2 8) (getr regs2 9) (getr regs2 10) (getr regs2 11) (getr regs2 12)
        (getr regs2 13) (getr regs2 14) (getr regs2 15) (getr regs2 16) (getr regs2 17) (getr regs2 18)
        (getr regs2 19) (getr regs2 20) (getr regs2 21) (getr regs2 22) (getr regs2 23) (getr regs2 24)
        (getr regs2 25) (getr regs2 26) (getr regs2 27) (getr regs2 28) (getr regs2 29) (getr regs2 30)
        (getr regs2 31) fp_regs fp_csr mem2 (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
        junk G2').
      + rewrite HSP. replace (spZ regs + -48) with (spZ regs - 48) by lia. rewrite <- HSEG. exact FR2.
      + rewrite HSP. lia.
    - intros ms Hp. pose proof Hp as Hp'. apply se_shape in Hp'. destruct Hp' as (R & pc' & mm & ->).
      exists R, pc', mm. split; [reflexivity | exact Hp]. }
  intros R pc3 mem3 regs3 HK3 Hg3. unfold se_post in HK3.
  destruct HK3 as (y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & E3).
  pose proof (f_equal ms_regs E3) as ER; pose proof (f_equal ms_pc_val E3) as EP; pose proof (f_equal ms_mem E3) as EM;
    cbn [ms_regs ms_pc_val ms_mem MS] in ER, EP, EM; subst R pc3 mem3; clear E3.
  rewrite (kb_ret_pc _ Hra). apply SR_ret.
  apply (HK L2 A2 regs3 mem2 md2 Lam2 regs2).
  - eapply rp_regs; [exact HR3|].
    cs_cases ltac:(rewrite Hg3; first
      [ reflexivity
      | match goal with |- getr _ (Z_to_bv 5 ?k) = _ =>
          transitivity (getr regs2 (Z_to_bv 5 k)); [reflexivity|];
          rewrite (Hp12 k ltac:(unfold callee_saved; lia)); exact (Gk k ltac:(lia)) end ]).
  - exact HR2.
  - exact Hrd2.
  - rewrite Hg3. reflexivity.
  - exact HL2.
  - exact Hres2.
  - exact HP2.
  - exact (Hz2 Hw0).
Qed.

Lemma tail_hit : forall L A regs mem md (dd : nat) E G L1 A1 mem1 md1 regs1 Lam1 peak1 cnt1 fail1 b1 z Dz w junk lo
    rz rkz rw rkw (P : config -> Prop),
  reader_env B API (PJ_SET_K dd) L A regs mem md ->
  rpost B API (PJ_SET_K dd) L A regs mem md E G L1 A1 regs mem1 md1 ->
  spZ regs <= lo -> (st_init_done A = false -> auxv_pre B (ly_sec L) lo mem) -> (forall x, E x -> x < lo) ->
  (forall p n i, In (p, n) (user_blocks A) -> 0 <= i < n -> G (ptr_addr L p) n -> E (ptr_addr L p + i)) ->
  getr regs1 1 = Z_to_bv 64 PS_FREE_RET -> getr regs1 2 = Z_to_bv 64 (spZ regs - 48) ->
  getr regs1 10 = Z_to_bv 64 z -> getr regs1 8 = Z_to_bv 64 w -> getr regs1 19 = Z_to_bv 64 z ->
  (forall r, r = 3 \/ r = 4 \/ 20 <= r <= 27 -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
  rw_cells (ms_segs B) mem1 (spZ regs - 48)
    [CB 8 junk; C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)] ->
  ledger B L1 A1 mem1 Lam1 peak1 cnt1 fail1 -> rf_ok F A1 b1 -> rd_cells B mem1 ->
  z <> 0 -> pj_fd (ms_segs B) mem1 (lin Lam1) dd z Dz -> rplace B L1 A1 Lam1 regs1 mem1 z ->
  (forall a k, In (a, k) Dz -> In (a, k) Lam1) ->
  Frame.disjoint_from [(z, z + 56)] (spZ regs - PJ_SET_K dd) (PJ_SET_K dd) ->
  (forall x, pj_free_writes z Dz x -> E x) -> (forall a n, freed Dz a n -> G a n) ->
  vloc L1 A1 Lam1 (spZ regs) z rz rkz -> ~ freed Dz rz rkz ->
  vloc L1 A1 Lam1 (spZ regs) w rw rkw -> ~ freed Dz rw rkw ->
  (forall x, w <= x < w + 56 -> ~ pj_free_writes z Dz x /\ E x /\ ~ in_img B x /\ ~ static_owned B x /\
     ~ alloc_statics x /\ ~ (errno_addr B <= x < errno_addr B + 4)) ->
  Frame.disjoint_from [(w, w + 56)] (spZ regs - PJ_SET_K dd) (PJ_SET_K dd) ->
  (w + 56 <= z \/ z + 56 <= w) -> stk (ms_segs B) mem1 w (w + 56) ->
  (forall L2 A2 regs2 mem2 md2 Lam2 regs3 mem3 bs,
     rpost B API (PJ_SET_K dd) L A regs mem md E G L2 A2 regs3 mem3 md2 ->
     rpost B API (PJ_FREE_K dd) L1 A1 regs1 mem1 md1 (pj_free_writes z Dz) (freed Dz) L2 A2 regs2 mem2 md2 ->
     Frame.munch [(z, z + 56); (w, w + 56)] mem2 mem3 -> Frame.wmono (ms_segs B) mem2 mem3 ->
     length bs = 56%nat -> bytes_at (ms_segs B) mem1 w bs -> bytes_at (ms_segs B) mem3 z bs ->
     rw_cells (ms_segs B) mem3 w [CB 56 (repeat (Z_to_bv 8 0) 56)] ->
     (forall j, 0 <= j < 56 -> writable_at (ms_segs B) mem3 (z + j)) -> rd_cells B mem3 ->
     getr regs3 10 = Z_to_bv 64 0 ->
     ledger B L2 A2 mem3 Lam2 peak1 cnt1 fail1 -> (exists D', Permutation Dz D' /\ rf_ok F A2 (rf_frees F b1 D')) ->
     Permutation Lam1 (Dz ++ Lam2) ->
     P (mkCfg (YK11.mkst regs3 (getr regs 1) mem3 (YK11.seg_rom (ms_segs B))) md2)) ->
  SR (ms_segs B) (mkCfg (YK11.mkst regs1 (Z_to_bv 64 PJ_FREE) mem1 (YK11.seg_rom (ms_segs B))) md1) P.
Proof.
  intros L A regs mem md dd E G L1 A1 mem1 md1 regs1 Lam1 peak1 cnt1 fail1 b1 z Dz w junk lo rz rkz rw rkw P
    HE HR1 Hlo Hax HElo HGE G1 G2 G10 G8 G19 Gk FR HL1 Hres1 Hrd1 Hz0 Hfd Hpl HDL HDz HWE HWG HVz Hgz HVw Hgw Hwx
    HDw HDzw Hwstk HK.
  destruct HE as (HSEG & Htp & Herrno & Hgot & Hguard & Hpre & Hsp47 & Hglob & Hfrm & HRD).
  pose proof (g_img B HSEG) as HIL.
  pose proof Hpre as (HMR & HWF & Hbd & Hra & Hsp16 & Hspc & Hsp63 & Hstk & Htpr & Herr & Haux).
  pose proof alloc_ceiling_value as Hceil.
  pose proof (t_sk dd) as (Kf & Kg & Ks & K96 & Kf0).
  unfold strtod_c.STRTOD_GLOBALS_TOP in Hglob.
  pose proof (bv_unsigned_in_range 64 (getr regs 2)) as HSPr. unfold bv_modulus in HSPr.
  assert (HSP : bv_unsigned (getr regs 2) = spZ regs) by reflexivity.
  assert (Hs1 : spZ regs1 = spZ regs - 48) by (unfold spZ at 1; rewrite G2, unsigned_lit by lia; reflexivity).
  assert (Herr4 : errno_addr B + 4 <= spZ regs - PJ_SET_K dd) by (rewrite Herrno; unfold strtod_c.STRTOD_ERRNO; lia).
  cbn [Frame.disjoint_from] in HDz, HDw.
  pose proof Hpl as (_ & _ & Hzx).
  pose proof Hwstk as (Hw0 & Hw1 & Hwst).
  assert (HDB : forall x, blk_set Dz x -> 0 <= x < alloc_ceiling).
  { intros x (a & k & Hin & Hx). pose proof (HDL a k Hin) as HinL.
    pose proof HR1 as (HM1 & _).
    pose proof (ledger_block_range B API L1 A1 mem1 md1 Lam1 peak1 cnt1 fail1 a k HM1 HL1 HinL). lia. }
  assert (HW1 : forall x, pj_free_writes z Dz x -> z <= x < z + 56 \/ 0 <= x < alloc_ceiling).
  { intros x (_ & [Hx|[Hx|Hx]]); [left; exact Hx | right; exact (HDB x Hx) |].
    right. unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Hx. lia. }
  assert (Hpre1 : call_pre_k B (aa_MR API) (PJ_FREE_K dd) L1 A1 regs1 mem1 md1).
  { apply (g_pre_k B API _ L A regs mem md E G L1 A1 mem1 md1 regs1 _ lo Hpre HR1).
    - rewrite G1. unfold YK0s.ret_ok. apply bv_eq. vm_compute. reflexivity.
    - rewrite Hs1. replace (spZ regs - 48) with (spZ regs + (-3) * 16) by lia. rewrite Z_mod_plus_full. exact Hsp16.
    - lia.
    - lia.
    - lia.
    - exact (Gk 4 ltac:(lia)).
    - lia.
    - exact Hlo.
    - exact Hax.
    - exact HElo. }
  assert (HE1 : reader_env B API (PJ_FREE_K dd) L1 A1 regs1 mem1 md1).
  { split; [exact HSEG|]. split; [exact Htp|]. split; [exact Herrno|]. split; [exact Hgot|]. split; [exact Hguard|].
    split; [exact Hpre1|]. split; [lia|]. split; [unfold strtod_c.STRTOD_GLOBALS_TOP; lia|].
    split; [exact Hfrm | exact Hrd1]. }
  eapply SR_bind; [apply (HFREE L1 A1 regs1 mem1 md1 Lam1 peak1 cnt1 fail1 b1 z dd Dz HE1 HL1 Hres1 G10) |].
  { right. split; [exact Hz0|]. split; [exact Hfd|]. split; [exact Hpl|].
    cbn [Frame.disjoint_from]. lia. }
  intros cc2 HC2.
  destruct HC2 as (L2 & A2 & regs2 & mem2 & md2 & Lam2 & -> & HR2 & Hrd2 & HP2 & HL2 & Hres2 & _ & Hz2).
  pose proof HR2 as (HMR2 & _ & _ & _ & _ & _ & _ & _ & _ & Hp12 & _).
  pose proof (Hz2 Hz0) as ((Hz8 & Hzs) & Hzb).
  pose proof Hzs as (Hzs0 & Hzs1 & Hzst).
  assert (HR3 : rpost B API (PJ_SET_K dd) L A regs mem md E G L2 A2 regs mem2 md2).
  { apply (rp_rec B API (PJ_SET_K dd) L A regs mem md E G L1 A1 mem1 md1 (PJ_FREE_K dd) regs1 (pj_free_writes z Dz)
      (freed Dz) L2 A2 regs2 mem2 md2 HWF ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HR1 HR2).
    - intros a _ _ Ha. exact (HWE a Ha).
    - intros a _ _ Ha. exact (HWE a Ha).
    - intros p n i _ _ _ Ha. exact (HWE _ Ha).
    - intros p n _ _ Hg. exact (HWG _ _ Hg).
    - exact HGE.
    - intros a Ha _ Hw. destruct (HW1 a Hw); lia. }
  assert (FR2 : rw_cells (ms_segs B) mem2 (spZ regs - 48)
    [CB 8 junk; C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)]).
  { apply (g_rw_cells B mem1); [exact FR|].
    intros x Hx. cbn [cells_size csize Nat.add] in Hx.
    refine (rp_same_hi B API _ _ _ _ _ _ _ _ _ _ _ _ _ x HR2 ltac:(lia) _ _).
    - unfold scratch_k. lia.
    - intros Hw. destruct (HW1 x Hw); lia. }
  assert (G2' : getr regs2 2 = Z_to_bv 64 (bv_unsigned (getr regs 2) + -48)).
  { transitivity (getr regs1 (Z_to_bv 5 2)); [apply (Hp12 2); unfold callee_saved; lia|].
    transitivity (Z_to_bv 64 (spZ regs - 48)); [exact G2 | f_equal; rewrite HSP; lia]. }
  assert (G8' : getr regs2 8 = Z_to_bv 64 w).
  { transitivity (getr regs1 (Z_to_bv 5 8)); [apply (Hp12 8); unfold callee_saved; lia | exact G8]. }
  assert (G19' : getr regs2 19 = Z_to_bv 64 z).
  { transitivity (getr regs1 (Z_to_bv 5 19)); [apply (Hp12 19); unfold callee_saved; lia | exact G19]. }
  pose proof Hrd2 as (ROA2 & _).
  assert (HWS : forall x, w <= x < w + 56 -> pis_same (ms_segs B) mem1 mem2 x).
  { intros x Hx. destruct (Hwx x Hx) as (Hn1 & _ & _ & _ & _ & Hne).
    exact (vloc_same B API L1 A1 Lam1 (spZ regs) w rw rkw _ regs1 mem1 md1 _ (freed Dz) L2 A2 regs2 mem2 md2 x
      HVw HR2 Hgw ltac:(lia) ltac:(lia) Hne Hx Hn1). }
  destruct (g_bytes_old B mem2 w 56 ltac:(lia) ltac:(lia) ltac:(lia)) as (bs & Hbl & WB2).
  { intros i Hi. rewrite (proj1 (HWS (w + i) ltac:(lia))). destruct (Hwst (w + i) ltac:(lia)) as (_ & bb & Hb).
    assert (Eb : mbyte (ms_segs B) mem1 (w + i) = Some bb) by exact Hb. rewrite Eb. discriminate. }
  assert (Hbl' : length bs = 56%nat) by lia.
  assert (WB1 : bytes_at (ms_segs B) mem1 w bs).
  { apply (g_bytes B mem2); [exact WB2|]. intros x Hx. rewrite Hbl' in Hx. exact (eq_sym (proj1 (HWS x ltac:(lia)))). }
  assert (Hww2 : forall i, 0 <= i < 56 -> writable_at (ms_segs B) mem2 (w + i)).
  { intros i Hi. apply (proj2 (HWS (w + i) ltac:(lia))). exact (proj1 (Hwst (w + i) ltac:(lia))). }
  assert (Hzw2 : forall i, 0 <= i < 56 -> writable_at (ms_segs B) mem2 (z + i)).
  { intros i Hi. exact (proj1 (Hzst (z + i) ltac:(lia))). }
  assert (RZ : rw_cells rsegs mem2 z [CB 56 (repeat (Z_to_bv 8 0) 56)]).
  { rewrite <- HSEG. apply (g_rw56 B); [apply repeat_length | exact Hzb | exact Hzw2]. }
  assert (RW : rw_cells rsegs mem2 w [CB 56 bs]).
  { rewrite <- HSEG. apply (g_rw56 B); [exact Hbl' | exact WB2 | exact Hww2]. }
  assert (WB2' : bytes_at rsegs mem2 w bs) by (rewrite <- HSEG; exact WB2).
  assert (FR2' : rw_cells rsegs mem2 (bv_unsigned (getr regs 2) + -48)
    [CB 8 junk; C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)]).
  { rewrite HSP. replace (spZ regs + -48) with (spZ regs - 48) by lia. rewrite <- HSEG. exact FR2. }
  assert (ROA2' : MemNorm.ro_agree rsegs mem2) by (rewrite <- HSEG; exact ROA2).
  assert (RF : forall i, 0 <= i < 48 -> ro_addr rsegs (wa (bv_unsigned (getr regs 2) + -48 + i)) = false).
  { intros i Hi. unfold wa. rewrite <- HSEG. apply (g_ro_low B HIL). lia. }
  assert (RZro : forall i, 0 <= i < 56 -> ro_addr rsegs (wa (z + i)) = false).
  { intros i Hi. unfold wa. rewrite <- HSEG. apply (g_ro_notimg B HSEG); [lia|].
    exact (proj2 (proj2 (proj2 (Hzx i Hi)))). }
  assert (RWro : forall i, 0 <= i < 56 -> ro_addr rsegs (wa (w + i)) = false).
  { intros i Hi. unfold wa. rewrite <- HSEG. apply (g_ro_notimg B HSEG); [lia|].
    exact (proj1 (proj2 (proj2 (Hwx (w + i) ltac:(lia))))). }
  rewrite G1.
  destruct (kb_md B API L2 A2 mem2 md2 HMR2) as (Hh2 & Hz2').
  apply (kb_run B regs2 _ mem2 md2
    (fun R pc' mem' => K_ret (getr regs 1) (getr regs 2) (getr regs2 3) (getr regs2 4) (getr regs 8) (getr regs 9)
       (getr regs 18) (getr regs 19) (getr regs2 20) (getr regs2 21) (getr regs2 22) (getr regs2 23) (getr regs2 24)
       (getr regs2 25) (getr regs2 26) (getr regs2 27) mem2 z w bs R pc' mem') _ Hh2 Hz2'
    (run_sb B HMC HMS regs2 mem2 (getr regs 2) (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
       junk z w bs (repeat (Z_to_bv 8 0) 56) bs HSEG ROA2' G2' G8' G19' FR2' Hbl' WB2' RZ RW
       ltac:(lia) ltac:(rewrite HSP; lia) ltac:(rewrite HSP; lia) ltac:(rewrite HSP; lia) RF RZro RWro)).
  intros R pc3 mem3 regs3 HK3 Hg3. unfold K_ret in HK3.
  destruct HK3 as (y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & ER & EP & MU & WM & RS &
    DB & WZ).
  subst R pc3.
  rewrite <- HSEG in WM, DB, WZ.
  assert (HVz2 : vloc L2 A2 Lam2 (spZ regs) z rz rkz).
  { apply (vloc_rp B API L1 A1 Lam1 (spZ regs) z rz rkz _ regs1 mem1 md1 _ (freed Dz) L2 A2 regs2 mem2 md2 Lam2
      peak1 cnt1 fail1 HVz HR2 Hgz HL2).
    intros a k Hin. left. apply (Permutation_in _ (Permutation_sym HP2)). apply in_or_app. right. exact Hin. }
  assert (HVw2 : vloc L2 A2 Lam2 (spZ regs) w rw rkw).
  { apply (vloc_rp B API L1 A1 Lam1 (spZ regs) w rw rkw _ regs1 mem1 md1 _ (freed Dz) L2 A2 regs2 mem2 md2 Lam2
      peak1 cnt1 fail1 HVw HR2 Hgw HL2).
    intros a k Hin. left. apply (Permutation_in _ (Permutation_sym HP2)). apply in_or_app. right. exact Hin. }
  assert (HWo : forall x, ~ Frame.outside [(z, z + 56); (w, w + 56)] x -> z <= x < z + 56 \/ w <= x < w + 56).
  { intros x Ho. exact (g_nout2 _ _ _ _ _ Ho). }
  assert (HR4 : rpost B API (PJ_SET_K dd) L A regs mem md E G L2 A2 regs mem3 md2).
  { apply (rp_A B API HIL (PJ_SET_K dd) L A regs mem md E G L2 A2 mem2 md2 mem3 _ HMR ltac:(lia) HR3 MU WM).
    - intros x Hx Ho Hn0. destruct (HWo x Ho) as [Hx'|Hx'].
      + apply (g_present_wr B HSEG mem3 x ltac:(lia)).
        * pose proof (proj2 (proj2 (proj2 (Hzx (x - z) ltac:(lia))))) as Hn.
          replace (z + (x - z)) with x in Hn by lia. exact Hn.
        * pose proof (Hzw2 (x - z) ltac:(lia)) as Hw2. replace (z + (x - z)) with x in Hw2 by lia. exact (WM _ Hw2).
      + apply (g_present_wr B HSEG mem3 x ltac:(lia)); [exact (proj1 (proj2 (proj2 (Hwx x Hx'))))|].
        pose proof (Hww2 (x - w) ltac:(lia)) as Hw2. replace (w + (x - w)) with x in Hw2 by lia. exact (WM _ Hw2).
    - intros x Ho. destruct (HWo x Ho) as [Hx'|Hx'].
      + split; [right; apply HWE; split; [exact Hz0 | left; exact Hx']|].
        apply (vloc_own B API L2 A2 Lam2 mem2 md2 (spZ regs) z rz rkz x HVz2 HMR2 ltac:(lia) Hx').
        intros Hs. apply (proj1 (Hzx (x - z) ltac:(lia))). replace (z + (x - z)) with x by lia. right. exact Hs.
      + split; [right; exact (proj1 (proj2 (Hwx x Hx')))|].
        apply (vloc_own B API L2 A2 Lam2 mem2 md2 (spZ regs) w rw rkw x HVw2 HMR2 ltac:(lia) Hx').
        exact (proj1 (proj2 (proj2 (proj2 (Hwx x Hx'))))). }
  rewrite (kb_ret_pc _ Hra). apply SR_ret.
  apply (HK L2 A2 regs2 mem2 md2 Lam2 regs3 mem3 bs).
  - eapply rp_regs; [exact HR4|].
    cs_cases ltac:(rewrite Hg3; first
      [ reflexivity
      | match goal with |- getr _ (Z_to_bv 5 ?k) = _ =>
          transitivity (getr regs2 (Z_to_bv 5 k)); [reflexivity|];
          rewrite (Hp12 k ltac:(unfold callee_saved; lia)); exact (Gk k ltac:(lia)) end ]).
  - exact HR2.
  - exact MU.
  - exact WM.
  - exact Hbl'.
  - exact WB1.
  - exact DB.
  - exact WZ.
  - intros j Hj. exact (WM _ (Hzw2 j Hj)).
  - split; [rewrite <- HSEG in RS; exact (MemNorm.ro_agree_same _ mem2 mem3 ROA2 RS)|].
    pose proof HR4 as (HM4 & _).
    destruct (YL01.ax_statics AX L2 A2 mem3 md2 HM4) as (Hgg & (gg & _ & Hggw) & _).
    split; [exact Hgg | exists gg; exact Hggw].
  - rewrite Hg3. reflexivity.
  - apply (g_ledger_munch B API L2 A2 mem2 md2 mem3 Lam2 peak1 cnt1 fail1 _ HMR2 HL2 MU).
    intros x Ho. destruct (HWo x Ho) as [Hx'|Hx'].
    + split; [intros Hs; apply (proj1 (proj2 (Hzx (x - z) ltac:(lia)))); replace (z + (x - z)) with x by lia; exact Hs|].
      intros a k Hin Ha.
      destruct (vloc_heads B API L2 A2 Lam2 mem2 md2 peak1 cnt1 fail1 (spZ regs) z rz rkz a k HVz2 HMR2 HL2
        ltac:(lia) Hin); lia.
    + split; [exact (proj1 (proj2 (proj2 (proj2 (proj2 (Hwx x Hx'))))))|].
      intros a k Hin Ha.
      destruct (vloc_heads B API L2 A2 Lam2 mem2 md2 peak1 cnt1 fail1 (spZ regs) w rw rkw a k HVw2 HMR2 HL2
        ltac:(lia) Hin); lia.
  - exact Hres2.
  - exact HP2.
Qed.

End T.
