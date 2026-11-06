From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib Require Import Contract Img0 FrameAPI KindBGlue SlotAgree.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_identity.lib Require MemNorm.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec SlotModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import URzP.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg Require Import Tac_sa Tac_sj.
Import ListNotations.
Open Scope Z_scope.

Lemma early_cond : forall u, 2 ^ 26 <= u < 2 ^ 64 ->
  negb (bv_eqb (Z_to_bv 64 (Z.shiftr u 26)) (Z_to_bv 64 0)) = true.
Proof.
  intros u Hu. rewrite Z.shiftr_div_pow2 by lia.
  assert (H1 : 1 <= u / 2 ^ 26) by (apply Z.div_le_lower_bound; lia).
  assert (H2 : u / 2 ^ 26 < 2 ^ 38) by (apply Z.div_lt_upper_bound; lia).
  rewrite (sj_bv_eqb (u / 2 ^ 26) 0) by lia.
  destruct (Z.eqb_spec (u / 2 ^ 26) 0); [lia | reflexivity].
Qed.

Lemma early_evt :
  forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S lo : Z),
    stk rsegs m lo S -> lo + 368 <= S -> S < 2 ^ 64 -> mem_inv rsegs m ->
    2 ^ 26 <= bv_unsigned a1 ->
    evt rsegs
      (fun ms' => exists (sp' a1' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp' gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1' a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         sp' = Z_to_bv 64 S /\
         munch [(S - 368, S)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo S)
      (MS (mkR ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12e9c) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m S lo ST LO HS MI Ha1.
  pose proof (munch_refl [(S - 368, S)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 a1) as Ra1. unfold bv_modulus in Ra1. change (2 ^ Z.of_N 64) with (2 ^ 64) in Ra1.
  assert (S0 : 0 <= lo) by (destruct ST as [H _]; exact H).
  carve_frame 368%nat ST.
  do 16 step.
  step.
  if_true_by (early_cond (bv_unsigned a1) ltac:(lia)).
  do 16 step.
  release_frame FR ST S.
  finish.
  all: try (f_equal; lia).
Qed.

Section Bridge.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Let API := APIf rc.
Context {RzCi : RzC} {RzAi : RzA B API}.

Lemma slot_ff_libk : forall pl fs K, @LIBK LS pl fs K = K (LL 0 fs []).
Proof.
  destruct FF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & _ & H & _). exact H.
Qed.

Lemma slot_ff_delta : forall n b, @lib_delta LS n b = b.
Proof.
  destruct FF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & _ & _ & H & _). exact H.
Qed.

Lemma slot_early : forall g,
  YK11.getr (g_regs g) 2 = Z_to_bv 64 (g_S g) -> spZ (g_regs g) = g_S g -> 2 ^ 26 <= g_n g ->
  lib_pre B API SLOT_STACK empty (g_L g) (g_A g) (g_regs g) (g_mem g) (g_md g) ra (g_p g) (g_n g) ->
  sink_none B (g_mem g) (g_md g) -> ro_agree (ms_segs B) (g_mem g) -> res_ok_slots (g_A g) (g_b g) ->
  Rz (ms_segs B) (mkCfg (YK11.mkst (g_regs g) (Z_to_bv 64 ENTRY) (g_mem g) (YK11.seg_rom (ms_segs B))) (g_md g))
    (Post B APIf ra g).
Proof.
  intros g Hsp Hspz Hn Hpre Hsn HMI Hres.
  pose proof (sa_segs B APIf ra empty FF) as SEGS.
  pose proof (sj_ra B APIf ra empty FF) as HRA.
  pose proof Hpre as (HM & HW & HB & HID & Hra & Hal & Hceil & H63 & Hstw & Htp & Herr & Hp & Hnn & Hpp & Hrod).
  pose proof alloc_ceiling_value as Hac.
  unfold SLOT_STACK in *.
  assert (Esp : spZ (g_regs g) = g_S g) by exact Hspz.
  destruct Hpp as [[Hn0 _] | [Hnpos (q & Hq & Eq)]]; [lia|].
  pose proof (mr_blocks_range _ _ (aa_laws API) _ _ _ _ q (g_n g) HM Hq) as [Hq1 Hq2].
  assert (En : bv_unsigned (YK11.getr (g_regs g) 11) = g_n g) by (rewrite Hnn; apply MState.unsigned_lit; lia).
  rewrite SEGS in HMI.
  destruct (mr_model B _ (aa_laws (APIf rc)) _ _ _ _ HM) as (Hh & Hl & _).
  rewrite SEGS.
  eapply (sa_run (g_regs g) (Z_to_bv 64 ENTRY) (g_mem g) (g_md g)); [exact Hh | exact Hl | exact HMI | | |].
  - rewrite sa_mkR_of. unfold ENTRY. rewrite Hsp.
    apply (early_evt) with (lo := g_S g - 65536).
    + apply sa_stk_norm; [exact HMI | unfold SA_TOP; lia | lia |].
      intros a Ha. rewrite <- SEGS. apply Hstw. rewrite Esp. exact Ha.
    + lia.
    + lia.
    + exact (MemNorm.mem_inv_normalize rsegs (g_mem g)).
    + rewrite En. lia.
  - intros ms (? & ? & ? & -> & _). do 3 eexists. reflexivity.
  - intros R pc' m0' HQ regs' m' Hx Hrel' Hsame.
    destruct HQ as (sp' & a1' & m'' & HE & Esp' & MU & WM & MI' & ST').
    injection HE; intros; subst.
    pose proof (MemNorm.mem_rel_normalize rsegs (g_mem g) HMI) as HR0.
    assert (MU' : Frame.munch [(g_S g - 368, g_S g)] (g_mem g) m')
      by exact (MemNorm.munch_rel rsegs _ (g_mem g) (MemNorm.normalize rsegs (g_mem g)) m' m'' HR0 Hrel' Hsame MU).
    assert (WM' : Frame.wmono rsegs (g_mem g) m')
      by exact (MemNorm.wmono_rel rsegs (g_mem g) (MemNorm.normalize rsegs (g_mem g)) m' m'' HR0 Hrel' Hsame WM).
    assert (Hro' : ro_agree rsegs m') by exact (MemNorm.ro_agree_same rsegs (g_mem g) m' HMI Hsame).
    assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ (g_S g - 368 <= a < g_S g) ->
                 m' (Z_to_bv 64 a) = g_mem g (Z_to_bv 64 a)).
    { apply (sa_unch _ _ _ (g_S g - 368) (g_S g) MU').
      intros x Hx0 O. destruct (Z_le_dec (g_S g - 368) x); destruct (Z_lt_dec x (g_S g)); try lia;
        exfalso; apply O; cbn [Frame.outside]; (split; [lia | exact I]). }
    assert (LOW : forall a, 0 <= a < YM05.alloc_ceiling -> m' (Z_to_bv 64 a) = g_mem g (Z_to_bv 64 a)).
    { intros a Ha. apply UN; lia. }
    apply rz_ret. unfold Post. rewrite SEGS.
    exists (g_L g), (g_A g), regs', m', (g_md g).
    split; [rewrite Hra, (sj_ret_pc_ra ra HRA); reflexivity|].
    split.
    + unfold lib_post. rewrite SEGS.
      split.
      { apply (kb_MR_A B API (g_L g) (g_A g) (g_mem g) m' (g_md g) [(g_S g - 368, g_S g)] HM).
        - intros x Hx0. apply MU'. exact Hx0.
        - intros x Hx1 _. cbn [Frame.outside]. split; [lia | exact I]. }
      split; [exact HW|]. split; [exact HB|]. split; [exact HID|].
      split; [rewrite (sa_getr_eqv _ _ _ Hx); reflexivity|].
      split.
      { intros r Hr. unfold callee_saved in Hr. rewrite (sa_getr_eqv _ _ _ Hx).
        assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
          r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
        destruct Hr' as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
          first [reflexivity | symmetry; exact Hsp]. }
      split; [exists (m_vmmaps (g_md g)); apply with_vmmaps_self|].
      split; [intros q0 k Hq0; exists q0; split; [exact Hq0 | reflexivity]|].
      split.
      { intros a Ha Hns. unfold lib_scratch in Hns. rewrite Esp in Hns. apply sa_eq_at. apply UN; [lia|].
        intros Hin. apply Hns. left. unfold SLOT_STACK. lia. }
      split.
      { intros a Himg _ _ _ _. pose proof (sj_img_lt B APIf ra empty FF a Himg) as Hl0.
        apply sa_eq_at. apply LOW. exact Hl0. }
      split.
      { intros q0 k i Hq0 _ Hi. pose proof (mr_blocks_range _ _ (aa_laws API) _ _ _ _ q0 k HM Hq0) as [R1 R2].
        exact (proj1 (sa_eq_at _ _ _ (LOW (ptr_addr (g_L g) q0 + i) ltac:(lia)))). }
      intros a Hs.
      assert (Hw : writable_at rsegs (g_mem g) a)
        by (rewrite <- SEGS; destruct Hs as [Hs|Hs]; [apply Hstw; exact Hs | apply Herr; exact Hs]).
      unfold writable_at in *. apply WM'. exact Hw.
    + split.
      { apply (sj_sink_frame B APIf ra empty FF (g_mem g) m' (g_md g) (g_md g)); [| reflexivity | exact Hsn].
        intros a Ha. try rewrite SEGS. refine (proj1 (sa_eq_at _ _ _ (LOW a _))).
        pose proof (sj_sink_addr B APIf ra empty FF a Ha) as (Hi & _).
        exact (sj_img_lt B APIf ra empty FF a Hi). }
      split; [unfold MI; try rewrite SEGS; exact Hro'|].
      split; [exact Hres|].
      intros i Hi. try rewrite SEGS.
      exact (proj1 (sa_eq_at _ _ _ (LOW (g_p g + i) ltac:(rewrite <- Eq; lia)))).
Qed.

Lemma slot_post_g : forall g c', Post B APIf ra g c' -> Fs.fs_sorted (m_fs (g_md g)) = true -> frm_zero fp_csr ->
  exists (fx' : FPState) L' A' regs' mem' md',
    c' = mkCfg (@YK11.mkst fx' regs' (Z_to_bv 64 ra) mem' (YK11.seg_rom (ms_segs B))) md' /\
    frm_zero (@fp_csr fx') /\
    lib_post_g B API [] SLOT_STACK (g_L g) (g_A g) (g_regs g) (g_mem g) (g_md g) (g_p g) (g_n g) (g_b g)
      (LL 0 (m_fs (g_md g)) []) L' A' regs' mem' md' /\ True.
Proof.
  intros g c' (L' & A' & regs' & mem' & md' & -> & HLP & HSN & HMI & HRE & HPAY) Hsorted Hfrm.
  exists fx, L', A', regs', mem', md'. split; [reflexivity|]. split; [exact Hfrm|]. split; [|exact I].
  destruct HLP as (H1 & H2 & H3 & H4 & H5 & H6 & (vm' & Hmd) & H8 & H9 & H10 & H11 & H12).
  unfold lib_post_g. cbn [ll_ret ll_out ll_fs].
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
  split; [exact H6|].
  split; [exists vm', (m_fds (g_md g)), (m_statpins (g_md g)); split; [rewrite Hmd; apply with_vmmaps_os_upd |
          intros k; reflexivity]|].
  split; [exact H8|]. split; [exact H9|]. split; [exact H10|].
  split; [intros a (lo & len & [] & _)|].
  split; [exact H11|]. split; [exact H12|].
  split; [reflexivity|]. split; [reflexivity|]. split; [exact Hsorted|].
  split; [exact HSN|]. split; [exact HMI|].
  split; [rewrite slot_ff_delta; exact HRE|].
  exact HPAY.
Qed.

Lemma slot_rz : (forall b n, @lib_room LS b n -> rz_sroom b) ->
  Hcut B APIf ra (Inv_ENTRY B APIf ra empty) ->
  forall L A regs mem md p n pl b,
  lib_pre_x B API SLOT_STACK empty L A regs mem md ra p n pl b -> ro_agree (ms_segs B) mem ->
  G_img_c B frame_RELRO mem ->
  Rz (ms_segs B) (mkCfg (YK11.mkst regs (Z_to_bv 64 ENTRY) mem (YK11.seg_rom (ms_segs B))) md)
    (Post B APIf ra (Ghost pl p (spZ regs) regs L A mem md b)).
Proof.
  intros HROOM HE L A regs mem md p n pl b Hpre HRO HR.
  destruct Hpre as (HP0 & HLEN & HD & Hres & Hroom & HSink & Hfd & Hsorted & Hchan & Hsp47).
  pose proof HP0 as (HM & HW & HB & HID & Hra & Hal & Hceil & H63 & Hstw & Htp & Herr & Hp & Hnn & Hpp & Hrod).
  set (g := Ghost pl p (spZ regs) regs L A mem md b).
  assert (Hsp : YK11.getr regs 2 = Z_to_bv 64 (spZ regs)).
  { apply bv_eq. rewrite Z_to_bv_unsigned. unfold spZ. symmetry. apply bv_wrap_small. apply bv_unsigned_in_range. }
  assert (Egn : g_n g = n) by (unfold g_n, nlen; cbn [g_in g]; lia).
  destruct (Z_lt_le_dec n (2 ^ 26)) as [Hsm|Hbig].
  - assert (HEN : Inv_ENTRY B APIf ra empty g
                    (mkCfg (YK11.mkst regs (Z_to_bv 64 ENTRY) mem (YK11.seg_rom (ms_segs B))) md)).
    { unfold SLOT_K, SLOT_STACK in *.
      split; [reflexivity|].
      split.
      { split; [rewrite Egn; lia|]. split.
        { destruct Hpp as [[-> ->] | [Hn0 (q & Hq & <-)]]; [left; rewrite Egn; split; reflexivity|].
          right. rewrite Egn. split; [exact Hn0|]. apply sj_blocks_in. exact Hq. }
        split; [exact HD|]. split; [exact Hal|]. split; [exact Hceil|]. split; [exact Hsp47|].
        split; [exact (HROOM b n Hroom)|]. split; [exact Hsp|]. exact Htp. }
      split; [rewrite Egn; exact HP0|].
      split; [exact Hsp|]. split; [exact HSink|]. split; [exact HRO|]. split; [exact HR|]. exact Hres. }
    exact (HE g _ HEN).
  - exact (slot_early g Hsp eq_refl ltac:(rewrite Egn; exact Hbig) ltac:(rewrite Egn; exact HP0) HSink HRO Hres).
Qed.

Lemma slot_lib : (forall segs c Q T, Rz segs c Q -> (forall c', Q c' -> realizes segs c' T) -> realizes segs c T) ->
  (forall b n, @lib_room LS b n -> rz_sroom b) ->
  Hcut B APIf ra (Inv_ENTRY B APIf ra empty) ->
  forall j, lib_contract_g B API [] frame_RELRO (fun _ _ => True) j ENTRY ra empty SLOT_STACK.
Proof.
  intros RZR HROOM HE j L A regs mem md p n pl b K Hpre _ HR HRO _ Hfrm HK.
  rewrite slot_ff_libk.
  pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & Hsorted & _).
  apply (RZR _ _ _ _ (slot_rz HROOM HE L A regs mem md p n pl b Hpre HRO HR)).
  intros c' Hc'. apply HK.
  destruct (slot_post_g _ c' Hc' Hsorted Hfrm) as (fx' & L' & A' & regs' & mem' & md' & E & F0 & LP & _).
  exists fx', L', A', regs', mem', md'. split; [exact E|]. split; [exact F0|]. split; [|exact I].
  replace n with (g_n (Ghost pl p (spZ regs) regs L A mem md b)) by (unfold g_n, nlen; cbn [g_in]; destruct Hpre as (_ & HLEN & _); lia).
  exact LP.
Qed.

Lemma slot_lib_cg : (forall segs c Q T, Rz segs c Q -> (forall c', Q c' -> realizes segs c' T /\ cut_free segs c') ->
    realizes segs c T /\ cut_free segs c) ->
  (forall b n, @lib_room LS b n -> rz_sroom b) ->
  Hcut B APIf ra (Inv_ENTRY B APIf ra empty) ->
  forall j, lib_contract_cg B API [] frame_RELRO (fun _ _ => True) j ENTRY ra empty SLOT_STACK.
Proof.
  intros RZR HROOM HE j L A regs mem md p n pl b K Hpre _ HR HRO _ Hfrm HK.
  rewrite slot_ff_libk.
  pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & Hsorted & _).
  apply (RZR _ _ _ _ (slot_rz HROOM HE L A regs mem md p n pl b Hpre HRO HR)).
  intros c' Hc'. apply HK.
  destruct (slot_post_g _ c' Hc' Hsorted Hfrm) as (fx' & L' & A' & regs' & mem' & md' & E & F0 & LP & _).
  exists fx', L', A', regs', mem', md'. split; [exact E|]. split; [exact F0|]. split; [|exact I].
  replace n with (g_n (Ghost pl p (spZ regs) regs L A mem md b)) by (unfold g_n, nlen; cbn [g_in]; destruct Hpre as (_ & HLEN & _); lia).
  exact LP.
Qed.

End Bridge.
