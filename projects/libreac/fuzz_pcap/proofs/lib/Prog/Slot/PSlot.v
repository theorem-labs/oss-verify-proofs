From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK0i YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YL01 YL00 YL0g YI04 YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import Contract Img0 FrameAPI OutForm KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require MemNorm.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot Require Import PInv PTac PEarly.
Import ListNotations.
Open Scope Z_scope.

(* The output invariant reads only bytes of frame_G, and the image holds 0 at the mode field. *)
Lemma GI_local : forall B, ms_segs B = rsegs -> G_local_c B frame_G GI.
Proof.
  intros B SEG j m m' Heq [H|H]; [left|right]; apply (ss_bytes_mbyte rsegs m m'); try exact H;
    intros i Hi; rewrite <- SEG; apply Heq; exists (symaddr (Symbols.Plain.s___stderr_FILE + 0x88)%Z), 4;
    (split; [unfold frame_G; cbn [In]; left; reflexivity | rewrite length_le4 in Hi; lia]).
Qed.

Lemma GI_img : forall B mem, ms_segs B = rsegs -> G_img_c B frame_G mem -> GI 0 mem.
Proof.
  intros B mem SEG H. left. split; [lia|]. split; [rewrite length_le4; lia|].
  intros i Hi. change (mbyte rsegs mem ((symaddr (Symbols.Plain.s___stderr_FILE + 0x88)%Z) + Z.of_nat i) = nth_error (le4 (Z_to_bv 64 0)) i).
  rewrite <- SEG. rewrite H.
  2: { exists (symaddr (Symbols.Plain.s___stderr_FILE + 0x88)%Z), 4. split; [unfold frame_G; cbn [In]; left; reflexivity|]. rewrite length_le4 in Hi. lia. }
  rewrite SEG.
  exact (ss_rel_chk_ok (le4 (Z_to_bv 64 0)) (symaddr (Symbols.Plain.s___stderr_FILE + 0x88)%Z) ltac:(vm_compute; reflexivity) i Hi).
Qed.

Section Bridge.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf SH SK ra empty.
Let API := APIf rc.

Lemma slot_img_lt : forall a, in_img B a -> 0 <= a < YM05.alloc_ceiling.
Proof.
  intros a H. pose proof (ss_img_lt B APIf ra empty FF a H) as Hl. pose proof alloc_ceiling_value as Hac.
  unfold IMG_LO, IMG_HI in Hl. lia.
Qed.

Lemma slot_sink_keep : forall (m m' : word -> option byte) md,
  (forall a, 0 <= a < SS_TOP -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)) ->
  sink_none B m md -> sink_none B m' md.
Proof.
  intros m m' md HK (Henv & Hhead & Hn). destruct (ss_sink B APIf ra empty FF) as (E1 & E2 & E3).
  assert (HM : forall a, 0 <= a < SS_TOP -> mbyte (ms_segs B) m' a = mbyte (ms_segs B) m a).
  { intros a Ha. unfold mbyte. rewrite (HK a Ha). reflexivity. }
  destruct Henv as [Ht Hl]. split; [split|split; [|exact Hn]].
  - eapply val_mem_frame; [|exact Ht]. intros x Hx. apply HM. rewrite E3 in Hx. cbn in Hx. unfold SS_TOP. lia.
  - eapply val_mem_frame; [|exact Hl]. intros x Hx. apply HM. rewrite E2 in Hx. cbn in Hx. unfold SS_TOP. lia.
  - apply (val_mem_word_mem (ms_segs B)). apply (val_mem_word_mem (ms_segs B)) in Hhead.
    eapply val_mem_frame; [|exact Hhead]. intros x Hx. apply HM. rewrite E1 in Hx. cbn in Hx. unfold SS_TOP. lia.
Qed.

(* The path for a payload of 2^26 bytes or more. *)
Lemma slot_early : forall g,
  YK11.getr (g_regs g) 2 = Z_to_bv 64 (g_S g) -> spZ (g_regs g) = g_S g -> 2 ^ 26 <= g_n g ->
  lib_pre B API SLOT_STACK empty (g_L g) (g_A g) (g_regs g) (g_mem g) (g_md g) ra (g_p g) (g_n g) ->
  sink_none B (g_mem g) (g_md g) -> ro_agree (ms_segs B) (g_mem g) -> res_ok_slots (g_A g) (g_b g) ->
  Fs.fs_sorted (m_fs (g_md g)) = true -> GI 0 (g_mem g) -> frm_zero (@fp_csr fx) ->
  SR (ms_segs B) (mkCfg (YK11.mkst (g_regs g) (Z_to_bv 64 ENTRY) (g_mem g) (YK11.seg_rom (ms_segs B))) (g_md g))
    (Post_o B APIf ra g).
Proof.
  intros g Hsp Hspz Hn Hpre Hsn HMI Hres Hsorted HGI Hfrm.
  pose proof pcap_early_holds as HE0. unfold pcap_early in HE0.
  pose proof (ss_segs B APIf ra empty FF) as SEGS.
  pose proof (ss_ra B APIf ra empty FF) as HRA.
  pose proof Hpre as (HM & HW & HB & HID & Hra & Hal & Hceil & H63 & Hstw & Htp & Herr & Hp & Hnn & Hpp & Hrod).
  pose proof alloc_ceiling_value as Hac.
  assert (HK : SLOT_STACK = 65536) by reflexivity.
  assert (Esp : spZ (g_regs g) = g_S g) by exact Hspz.
  destruct Hpp as [[Hn0 _] | [Hnpos (q & Hq & Eq)]]; [lia|].
  pose proof (mr_blocks_range _ _ (aa_laws API) _ _ _ _ q (g_n g) HM Hq) as [Hq1 Hq2].
  assert (En : bv_unsigned (YK11.getr (g_regs g) 11) = g_n g) by (rewrite Hnn; apply MState.unsigned_lit; lia).
  rewrite SEGS in HMI.
  destruct (mr_model B _ (aa_laws (APIf rc)) _ _ _ _ HM) as (Hh & Hl & _).
  rewrite SEGS.
  eapply (ss_run (g_regs g) (Z_to_bv 64 ENTRY) (g_mem g) (g_md g)); [exact Hh | exact Hl | exact HMI | | |].
  - rewrite ss_mkR_of. rewrite Hsp.
    apply HE0 with (lo := g_S g - SLOT_STACK).
    + apply ss_stk_norm; [exact HMI | unfold SS_TOP; lia | lia |].
      intros a Ha. rewrite <- SEGS. apply Hstw. rewrite Esp. exact Ha.
    + unfold SLOT_FRAME. lia.
    + lia.
    + exact (MemNorm.mem_inv_normalize rsegs (g_mem g)).
    + rewrite En. lia.
  - intros ms (sp1 & t01 & t11 & t21 & a11 & a21 & a31 & a41 & a51 & a61 & a71 & t31 & t41 & t51 & t61 & m1 & -> & _).
    do 3 eexists. reflexivity.
  - intros R pc' m0' HQ regs' m' Hx Hrel' Hsame.
    destruct HQ as (sp' & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m'' & HE &
      Esp' & MU & WM & MI' & ST').
    injection HE; intros; subst.
    pose proof (MemNorm.mem_rel_normalize rsegs (g_mem g) HMI) as HR0.
    assert (MU' : Frame.munch [(g_S g - SLOT_FRAME, g_S g)] (g_mem g) m')
      by exact (MemNorm.munch_rel rsegs _ (g_mem g) (MemNorm.normalize rsegs (g_mem g)) m' m'' HR0 Hrel' Hsame MU).
    assert (WM' : Frame.wmono rsegs (g_mem g) m')
      by exact (MemNorm.wmono_rel rsegs (g_mem g) (MemNorm.normalize rsegs (g_mem g)) m' m'' HR0 Hrel' Hsame WM).
    assert (Hro' : ro_agree rsegs m') by exact (MemNorm.ro_agree_same rsegs (g_mem g) m' HMI Hsame).
    assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ (g_S g - SLOT_FRAME <= a < g_S g) ->
                 m' (Z_to_bv 64 a) = g_mem g (Z_to_bv 64 a)).
    { apply (ss_unch _ _ _ (g_S g - SLOT_FRAME) (g_S g) MU').
      intros x Hx0 O. destruct (Z_le_dec (g_S g - SLOT_FRAME) x); destruct (Z_lt_dec x (g_S g)); try lia;
        exfalso; apply O; cbn [Frame.outside]; (split; [lia | exact I]). }
    assert (LOW : forall a, 0 <= a < YM05.alloc_ceiling -> m' (Z_to_bv 64 a) = g_mem g (Z_to_bv 64 a)).
    { intros a Ha. apply UN; [lia|]. unfold SLOT_FRAME. lia. }
    apply SR_ret. unfold Post_o.
    exists fx, (g_L g), (g_A g), regs', m', (g_md g).
    split; [rewrite Hra, (ss_ret_pc_ra ra HRA), SEGS; reflexivity|].
    split; [exact Hfrm|].
    split.
    + unfold lib_post_g. rewrite SEGS.
      split.
      { apply (kb_MR_A B API (g_L g) (g_A g) (g_mem g) m' (g_md g) [(g_S g - SLOT_FRAME, g_S g)] HM).
        - intros x Hx0. apply MU'. exact Hx0.
        - intros x Hx1 _. cbn [Frame.outside]. unfold SLOT_FRAME. split; [lia | exact I]. }
      split; [exact HW|]. split; [exact HB|]. split; [exact HID|].
      split; [rewrite (ss_getr_eqv _ _ _ Hx); reflexivity|].
      split.
      { intros r Hr. unfold callee_saved in Hr. rewrite (ss_getr_eqv _ _ _ Hx).
        assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
          r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
        destruct Hr' as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
          first [reflexivity | symmetry; exact Hsp]. }
      split.
      { exists (m_vmmaps (g_md g)), (m_fds (g_md g)), (m_statpins (g_md g)). cbn [ll_fs].
        split; [rewrite <- with_vmmaps_os_upd; apply with_vmmaps_self | intros k; reflexivity]. }
      split; [intros q0 k Hq0; exists q0; split; [exact Hq0 | reflexivity]|].
      split.
      { intros a Ha Hns. unfold lib_scratch in Hns. rewrite Esp in Hns. apply ss_eq_at. apply UN; [lia|].
        intros Hin. apply Hns. left. unfold SLOT_FRAME in Hin. lia. }
      split.
      { intros a Himg _ _ _ _. pose proof (slot_img_lt a Himg) as Hl0.
        apply ss_eq_at. apply LOW. exact Hl0. }
      split.
      { intros a HG. destruct (ss_glob_img B APIf ra empty FF a HG) as (Hi & _).
        exact (proj2 (ss_eq_at _ _ _ (LOW a (slot_img_lt a Hi)))). }
      split.
      { intros q0 k i Hq0 _ Hi. pose proof (mr_blocks_range _ _ (aa_laws API) _ _ _ _ q0 k HM Hq0) as [R1 R2].
        exact (proj1 (ss_eq_at _ _ _ (LOW (ptr_addr (g_L g) q0 + i) ltac:(lia)))). }
      split.
      { intros a Hs.
        assert (Hw : writable_at rsegs (g_mem g) a)
          by (rewrite <- SEGS; destruct Hs as [Hs|Hs]; [apply Hstw; exact Hs | apply Herr; exact Hs]).
        unfold writable_at in *. apply WM'. exact Hw. }
      split; [reflexivity|]. split; [reflexivity|]. split; [exact Hsorted|].
      split.
      { refine (slot_sink_keep (g_mem g) m' (g_md g) _ Hsn).
        intros a Ha. apply LOW. pose proof ss_top_ceil as Ht. lia. }
      split; [exact Hro'|].
      split; [exact Hres|].
      intros i Hi.
      exact (proj1 (ss_eq_at _ _ _ (LOW (g_p g + i) ltac:(rewrite <- Eq; lia)))).
    + refine (GI_local B SEGS 0%nat (g_mem g) m' _ HGI).
      intros a HG. destruct (ss_glob_img B APIf ra empty FF a HG) as (Hi & _). rewrite SEGS.
      exact (proj1 (ss_eq_at _ _ _ (LOW a (slot_img_lt a Hi)))).
Qed.

(* The slot from its first cut: generic in the output function f and in the shape LS (output f to stderr, the
   bound unchanged, a cap between 128 and CAPMAX): the halts frame's out_shape f and the agreement out shape. *)
Lemma slot_lib_ols : forall (LS : lib_shape) f,
  (forall pl fs K, @LIBK LS pl fs K = wr ch_stderr (f pl) (K (LL 0 fs (f pl)))) ->
  (forall n b, @lib_delta LS n b = b) ->
  (forall b n, @lib_room LS b n -> sb_live b <= 64 /\ 0 <= sb_bytes b <= 2 ^ 28 /\ 128 <= sb_cap b <= CAPMAX) ->
  Hcut_o B APIf ra (Inv_ENTRY B APIf ra empty) (fun g => f (g_in g)) ->
  (forall pl, 2 ^ 26 <= Z.of_nat (length pl) -> f pl = []) ->
  forall j, lib_slot_o (LS:=LS) B API f frame_G frame_RELRO GI j ENTRY ra empty SLOT_STACK.
Proof.
  intros LS f HLIBK HDELTA HROOM HE HBIG j L A regs mem md p n pl b Hpre Hfd HGI HR HRO Hfrm.
  destruct Hpre as (HP0 & HLEN & HD & Hres & Hroom & HSink & Hfa & Hsorted & Hfd' & Hsp47).
  pose proof HP0 as (HM & HW & HB & HID & Hra & Hal & Hceil & H63 & Hstw & Htp & Herr & Hp & Hnn & Hpp & Hrod).
  set (g := Ghost pl p (spZ regs) regs L A mem md b).
  assert (Hsp : YK11.getr regs 2 = Z_to_bv 64 (spZ regs)).
  { apply bv_eq. rewrite Z_to_bv_unsigned. unfold spZ. symmetry. apply bv_wrap_small. apply bv_unsigned_in_range. }
  assert (Egn : g_n g = n) by (unfold g_n; cbn [g_in g]; lia).
  apply (SRO_mono (ms_segs B) _ (f pl) (Post_o B APIf ra g)).
  2: { intros c' (fx' & L' & A' & regs' & mem' & md' & Hc & Hf & Hpost & HGI').
       exists fx', L', A', regs', mem', md'. split; [exact Hc|]. split; [exact Hf|]. split; [|exact HGI'].
       rewrite Egn in Hpost. unfold lib_post_g in Hpost |- *. rewrite HDELTA.
       cbn [lib_delta LS_P out_shape] in Hpost. exact Hpost. }
  destruct (Z_lt_le_dec n (2 ^ 26)) as [Hsm|Hbig].
  - assert (HEN : Inv_ENTRY B APIf ra empty g
                    (mkCfg (YK11.mkst regs (Z_to_bv 64 ENTRY) mem (YK11.seg_rom (ms_segs B))) md)).
    { unfold SLOT_K, SLOT_STACK in *.
      exists fx. split; [reflexivity|]. split; [exact Hfrm|].
      split.
      { split; [rewrite Egn; lia|]. split.
        { destruct Hpp as [[-> ->] | [Hn0 (q & Hq & <-)]]; [left; rewrite Egn; split; reflexivity|].
          right. rewrite Egn. split; [exact Hn0|]. apply ss_blocks_in. exact Hq. }
        split; [exact HD|]. split; [exact Hal|]. split; [exact Hceil|]. split; [exact Hsp47|].
        split; [destruct (HROOM b n Hroom) as (R1 & R2 & R3); split; [exact R1|]; split; [exact R2|];
          change (sb_cap (g_b g)) with (sb_cap b); exact R3|].
        split; [exact Hsp|]. split; [exact Htp|].
        split; [exact HR|]. split; [exact HSink|]. split; [exact Hsorted|]. exact Hfd. }
      split; [rewrite Egn; exact HP0|].
      split; [exact HRO|]. split; [exact Hres|]. split; [exact HGI|]. exact Hfa. }
    exact (HE g _ HEN).
  - rewrite (HBIG pl ltac:(rewrite <- HLEN; exact Hbig)).
    apply SR_to_SRO.
    refine (slot_early g Hsp eq_refl ltac:(rewrite Egn; exact Hbig) ltac:(rewrite Egn; exact HP0) HSink HRO Hres
      Hsorted HGI Hfrm).
Qed.

Lemma slot_lib_o : forall f,
  Hcut_o B APIf ra (Inv_ENTRY B APIf ra empty) (fun g => f (g_in g)) ->
  (forall pl, 2 ^ 26 <= Z.of_nat (length pl) -> f pl = []) ->
  forall j, lib_slot_o (LS:=out_shape f) B API f frame_G frame_RELRO GI j ENTRY ra empty SLOT_STACK.
Proof.
  intros f. apply (slot_lib_ols (out_shape f) f); [intros; reflexivity | intros; reflexivity |].
  intros b n (R1 & R2 & R3). rewrite R3. unfold CAPMAX. lia.
Qed.

Lemma slot_contract_ols : forall (LS : lib_shape) f,
  (forall pl fs K, @LIBK LS pl fs K = wr ch_stderr (f pl) (K (LL 0 fs (f pl)))) ->
  (forall n b, @lib_delta LS n b = b) ->
  (forall b n, @lib_room LS b n -> sb_live b <= 64 /\ 0 <= sb_bytes b <= 2 ^ 28 /\ 128 <= sb_cap b <= CAPMAX) ->
  Hcut_o B APIf ra (Inv_ENTRY B APIf ra empty) (fun g => f (g_in g)) ->
  (forall pl, 2 ^ 26 <= Z.of_nat (length pl) -> f pl = []) ->
  forall j, lib_contract_o (LS:=LS) B API f frame_G frame_RELRO GI j ENTRY ra empty SLOT_STACK.
Proof.
  intros LS f HLIBK HDELTA HROOM HE HBIG j L A regs mem md p n pl b K Hpre Hfd HGI HR Hro Hfrm HK.
  rewrite HLIBK.
  refine (slot_lib_ols LS f HLIBK HDELTA HROOM HE HBIG j L A regs mem md p n pl b Hpre Hfd HGI HR Hro Hfrm
    (K (LL 0 (m_fs md) (f pl))) _).
  intros c' (fx' & L' & A' & regs' & mem' & md' & Hc & Hf & Hpost & HGI').
  apply HK. exists fx', L', A', regs', mem', md'.
  split; [exact Hc |]. split; [exact Hf |]. split; [| exact HGI'].
  unfold lib_post_o. split; [exact Hpost | reflexivity].
Qed.

Lemma slot_contract_o : forall f,
  Hcut_o B APIf ra (Inv_ENTRY B APIf ra empty) (fun g => f (g_in g)) ->
  (forall pl, 2 ^ 26 <= Z.of_nat (length pl) -> f pl = []) ->
  forall j, lib_contract_o (LS:=out_shape f) B API f frame_G frame_RELRO GI j ENTRY ra empty SLOT_STACK.
Proof.
  intros f HE HBIG j. apply lib_contract_o_of_slot. exact (slot_lib_o f HE HBIG j).
Qed.

End Bridge.
