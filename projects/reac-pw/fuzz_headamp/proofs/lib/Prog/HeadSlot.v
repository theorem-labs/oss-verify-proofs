(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/LLVMFuzzerTestOneInput_fr.v, with its module paths and module names changed; 456 of its 574 lines of code are new or changed and 409 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/Prog/Seg/Tac_slot.v, with its module paths and module names changed; 184 of its 213 lines of code are new or changed and 545 lines of the source are left out. *)
(* The slot of reac-pw/fuzz_headamp LLVMFuzzerTestOneInput (plain build) from its segment lemmas, and plain_halts from
   the frame. Taken from reac-pw/fuzz_role's Prog/RoleSlot.v (itself reac-pw/fuzz_pin's Prog/PinSlot.v and
   libreac/fuzz_ctrl's released Prog/Seg/Slot.v and Prog/Seg/SlotLink.v), with headamp's code and cuts:
   - the n >= 2^26 run: Prog/LLVMFuzzerTestOneInput_c.v's headamp_early_contract (proved in Prog/headamp_early.v),
     taken here as the Section hypothesis EARLY; the run passes no cut (GV bounds n below 2^26 at the cuts), so the
     slot runs it as one evt from ENTRY to ra (slot_early). Its epilogue's `fld` write fs0 .. fs2, so the run ends
     at its own FP registers F' with the entry fcsr: slot_early runs it by Tac_slot.sl_run_fp and closes Post at
     the FP state mkFP F' fcsr (Post takes any FP state with rounding mode 0);
   - Section Bridge: slot_lib: H(ENTRY) -> the slot obligation lib_contract_g for every j, under
     FrameAPI.frame_facts_plain and EARLY (Post -> lib_post_g is Tac_slot.sl_post_g, at Post's own FP state);
   - Section Slot: the six segment statements S_E01, S_M01, S_M02, S_M03, S_M04, S_X01 of
     Prog/LLVMFuzzerTestOneInput_c.v as hypotheses, H(ENTRY) through the cuts K13044, K1404c, K14080, K14168, K141b4
     (slot_entry) and slot_holds : slot_goal;
   - Section Bundle: slot_of_lemmas (frame_facts_plain, headamp_early_contract and seg_lemmas give slot_goal);
   - Section Link: plain_halts from frame_plain (FrameAPI.frame_plain_split), headamp_early_contract and the segment
     lemmas as a hypothesis SEGS, stated as each segment file states its lemma once its Section closes.
   rule 24: proves no function by itself (kind: segment lemma of LLVMFuzzerTestOneInput's walk: the composition of
   the segment lemmas with the slot, and the n >= 2^26 run). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require KindBGlue.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog Require Import SlotFR SlotInv LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.Seg Require Import Tac_slot.
From OSSVerify.reac_pw.fuzz_headamp Require Statements.
Import ListNotations.
Open Scope Z_scope.

Lemma hs_ret_pc_ra : forall z, z mod 2 = 0 -> ret_pc (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. assert (E : Z_to_bv 64 z = Z_to_bv 64 (z mod 2 ^ 64)).
  { apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
    rewrite Zmod_mod. reflexivity. }
  rewrite E. apply ret_pc_even; [apply Z.mod_pos_bound; lia | rewrite KindBGlue.kb_mod2_land; exact Hz].
Qed.

Lemma hs_blocks_in : forall L A p n, In (p, n) (user_blocks A) -> In (ptr_addr L p, n) (blocks L A).
Proof. intros L A p n H. unfold blocks. apply in_map_iff. exists (p, n). split; [reflexivity | exact H]. Qed.

(* ---- H(ENTRY) -> the slot obligation ---- *)
Section Bridge.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts_plain B APIf LS SH SK ra empty.
Hypothesis EARLY : headamp_early_contract.
Let API := APIf rc.

Lemma slot_early : forall g,
  YK11.getr (g_regs g) 2 = Z_to_bv 64 (g_S g) -> spZ (g_regs g) = g_S g -> 2 ^ 26 <= g_n g ->
  lib_pre B API SLOT_STACK empty (g_L g) (g_A g) (g_regs g) (g_mem g) (g_md g) ra (g_p g) (g_n g) ->
  sink_none B (g_mem g) (g_md g) -> ro_agree (ms_segs B) (g_mem g) -> res_ok_slots (g_A g) (g_b g) ->
  frm_zero fp_csr ->
  SR (ms_segs B) (mkCfg (YK11.mkst (g_regs g) (Z_to_bv 64 ENTRY) (g_mem g) (YK11.seg_rom (ms_segs B))) (g_md g))
    (Post B APIf ra g).
Proof using fx rc B APIf LS SH SK ra empty FF EARLY.
  intros g Hsp Hspz Hn Hpre Hsn HMI Hres Hfrm.
  pose proof (sl_segs B APIf ra empty FF) as SEGS.
  pose proof (ff_ra B APIf ra empty FF) as HRA.
  pose proof Hpre as (HM & HW & HB & HID & Hra & Hal & Hceil & H63 & Hstw & Htp & Herr & Hp & Hnn & Hpp & Hrod).
  pose proof alloc_ceiling_value as Hac.
  pose proof alloc_ceiling_lt as Hac47.
  pose proof sl_ceil as HTOP.
  unfold SLOT_STACK in *.
  assert (Esp : spZ (g_regs g) = g_S g) by exact Hspz.
  destruct Hpp as [[Hn0 _] | [Hnpos (q & Hq & Eq)]]; [lia|].
  pose proof (mr_blocks_range _ _ (aa_laws API) _ _ _ _ q (g_n g) HM Hq) as [Hq1 Hq2].
  assert (En : bv_unsigned (YK11.getr (g_regs g) 11) = g_n g) by (rewrite Hnn; apply MState.unsigned_lit; lia).
  rewrite SEGS in HMI.
  destruct (mr_model B _ (aa_laws (APIf rc)) _ _ _ _ HM) as (Hh & Hl & _).
  rewrite SEGS.
  eapply (sl_run_fp (g_regs g) (Z_to_bv 64 ENTRY) (g_mem g) (g_md g)); [exact Hh | exact Hl | exact HMI | | |].
  - rewrite sl_mkR_of. rewrite Hsp.
    apply EARLY with (lo := g_S g - 65536).
    + apply sl_stk_norm; [exact HMI | unfold SL_TOP in *; lia | lia |].
      intros a Ha. rewrite <- SEGS. apply Hstw. rewrite Esp. exact Ha.
    + lia.
    + lia.
    + exact (mem_inv_normalize rsegs (g_mem g)).
    + rewrite En. lia.
  - intros ms (? & ? & ? & ? & -> & _). do 5 eexists. reflexivity.
  - intros R F' pc' fc' m0' HQ regs' m' Hx Hrel' Hsame.
    destruct HQ as (sp' & a2' & F'' & m'' & HE & Esp' & MU & WM & MI' & ST').
    injection HE; intros; subst.
    pose proof (mem_rel_normalize rsegs (g_mem g) HMI) as HR0.
    assert (MU' : Frame.munch [(g_S g - 560, g_S g)] (g_mem g) m')
      by exact (munch_rel rsegs _ (g_mem g) (normalize rsegs (g_mem g)) m' m'' HR0 Hrel' Hsame MU).
    assert (WM' : Frame.wmono rsegs (g_mem g) m')
      by exact (wmono_rel rsegs (g_mem g) (normalize rsegs (g_mem g)) m' m'' HR0 Hrel' Hsame WM).
    assert (Hro' : ro_agree rsegs m') by exact (ro_agree_same rsegs (g_mem g) m' HMI Hsame).
    assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ (g_S g - 560 <= a < g_S g) ->
                 m' (Z_to_bv 64 a) = g_mem g (Z_to_bv 64 a)).
    { apply (sl_unch _ _ _ (g_S g - 560) (g_S g) MU').
      intros x Hx0 O. destruct (Z_le_dec (g_S g - 560) x); destruct (Z_lt_dec x (g_S g)); try lia;
        exfalso; apply O; cbn [Frame.outside]; (split; [lia | exact I]). }
    assert (LOW : forall a, 0 <= a < YM05.alloc_ceiling -> m' (Z_to_bv 64 a) = g_mem g (Z_to_bv 64 a)).
    { intros a Ha. apply UN; lia. }
    apply SR_ret. unfold Post. rewrite SEGS.
    exists (mkFP F'' fp_csr), (g_L g), (g_A g), regs', m', (g_md g).
    split; [rewrite Hra, (hs_ret_pc_ra ra HRA); reflexivity|].
    split; [exact Hfrm|].
    split.
    + unfold lib_post. rewrite SEGS.
      split.
      { apply (KindBGlue.kb_MR_A B API (g_L g) (g_A g) (g_mem g) m' (g_md g) [(g_S g - 560, g_S g)] HM).
        - intros x Hx0. apply MU'. exact Hx0.
        - intros x Hx1 _. cbn [Frame.outside]. split; [lia | exact I]. }
      split; [exact HW|]. split; [exact HB|]. split; [exact HID|].
      split; [rewrite (sl_getr_eqv _ _ _ Hx); reflexivity|].
      split.
      { intros r Hr. unfold callee_saved in Hr. rewrite (sl_getr_eqv _ _ _ Hx).
        assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
          r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
        destruct Hr' as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
          first [reflexivity | symmetry; exact Hsp]. }
      split; [exists (m_vmmaps (g_md g)); apply with_vmmaps_self|].
      split; [intros q0 k Hq0; exists q0; split; [exact Hq0 | reflexivity]|].
      split.
      { intros a Ha Hns. unfold lib_scratch in Hns. rewrite Esp in Hns. apply sl_eq_at. apply UN; [lia|].
        intros Hin. apply Hns. left. unfold SLOT_STACK. lia. }
      split.
      { intros a Himg _ _ _ _. pose proof (sl_in_img_top B a SEGS Himg) as Hl0.
        apply sl_eq_at. apply LOW. lia. }
      split.
      { intros q0 k i Hq0 _ Hi. pose proof (mr_blocks_range _ _ (aa_laws API) _ _ _ _ q0 k HM Hq0) as [R1 R2].
        exact (proj1 (sl_eq_at _ _ _ (LOW (ptr_addr (g_L g) q0 + i) ltac:(lia)))). }
      intros a Hs.
      assert (Hw : writable_at rsegs (g_mem g) a)
        by (rewrite <- SEGS; destruct Hs as [Hs|Hs]; [apply Hstw; exact Hs | apply Herr; exact Hs]).
      unfold writable_at in *. apply WM'. exact Hw.
    + split.
      { apply (sl_sink_keep B APIf ra empty FF (g_mem g) m' (g_md g)); [| exact Hsn].
        intros a Ha. apply LOW. lia. }
      split; [unfold MI; try rewrite SEGS; exact Hro'|].
      split; [exact Hres|].
      intros i Hi. try rewrite SEGS.
      exact (proj1 (sl_eq_at _ _ _ (LOW (g_p g + i) ltac:(rewrite <- Eq; lia)))).
Qed.

Lemma slot_lib : Hcut B APIf ra (Inv_ENTRY B APIf ra empty) ->
  forall j, lib_contract_g B API [] frame_RELRO (fun _ _ => True) j ENTRY ra empty SLOT_STACK.
Proof using fx rc B APIf LS SH SK ra empty FF EARLY.
  intros HE j L A regs mem md p n pl b K Hpre _ HR HRO _ Hfrm HK.
  rewrite (ff_libk B APIf ra empty FF).
  destruct Hpre as (HP0 & HLEN & HD & Hres & Hroom & HSink & Hfd & Hsorted & Hfdc & Hsp47).
  pose proof HP0 as (HM & HW & HB & HID & Hra & Hal & Hceil & H63 & Hstw & Htp & Herr & Hp & Hnn & Hpp & Hrod).
  set (g := Ghost pl p (spZ regs) regs L A mem md b).
  assert (Hsp : YK11.getr regs 2 = Z_to_bv 64 (spZ regs)).
  { apply bv_eq. rewrite Z_to_bv_unsigned. unfold spZ. symmetry. apply bv_wrap_small. apply bv_unsigned_in_range. }
  assert (Egn : g_n g = n) by (unfold g_n; cbn [g_in g]; lia).
  assert (HKg : forall c', Post B APIf ra g c' -> realizes (ms_segs B) c' (K (LL 0 (m_fs md) []))).
  { intros c' Hc'. apply HK.
    destruct (sl_post_g B APIf ra empty FF g c' Hc' Hsorted) as (fx' & L' & A' & regs' & mem' & md' & E & F0 & LP).
    exists fx', L', A', regs', mem', md'. split; [exact E|]. split; [exact F0|]. split; [|exact I].
    rewrite Egn in LP. exact LP. }
  destruct (Z_lt_le_dec n (2 ^ 26)) as [Hsm|Hbig].
  - assert (HEN : Inv_ENTRY B APIf ra empty g
                    (mkCfg (YK11.mkst regs (Z_to_bv 64 ENTRY) mem (YK11.seg_rom (ms_segs B))) md)).
    { unfold SLOT_K, SLOT_STACK in *.
      split; [reflexivity|].
      split.
      { split; [rewrite Egn; lia|]. split.
        { destruct Hpp as [[-> ->] | [Hn0 (q & Hq & <-)]]; [left; rewrite Egn; split; reflexivity|].
          right. rewrite Egn. split; [exact Hn0|]. apply hs_blocks_in. exact Hq. }
        split; [exact HD|]. split; [exact Hal|]. split; [exact Hceil|]. split; [exact Hsp47|].
        split; [exact (ff_room B APIf ra empty FF b n Hroom)|]. split; [exact Hsp|]. exact Htp. }
      split; [rewrite Egn; exact HP0|].
      split; [exact Hsp|]. split; [exact HSink|]. split; [exact HRO|]. split; [exact HR|].
      split; [exact Hres|]. exact Hfrm. }
    exact (SR_realizes (ms_segs B) _ _ _ (HE g _ HEN) HKg).
  - exact (SR_realizes (ms_segs B) _ _ _ (slot_early g Hsp eq_refl ltac:(rewrite Egn; exact Hbig)
             ltac:(rewrite Egn; exact HP0) HSink HRO Hres Hfrm) HKg).
Qed.

End Bridge.

(* ---- The composition: ENTRY -> K13044 -> K1404c -> K14080 -> K14168 -> K141b4 -> RET ---- *)
Section Slot.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts_plain B APIf LS SH SK ra empty.
Hypothesis EARLY : headamp_early_contract.

Hypothesis seg_E01 : S_E01 B APIf ra empty.
Hypothesis seg_M01 : S_M01 B APIf ra empty.
Hypothesis seg_M02 : S_M02 B APIf ra empty.
Hypothesis seg_M03 : S_M03 B APIf ra empty.
Hypothesis seg_M04 : S_M04 B APIf ra empty.
Hypothesis seg_X01 : S_X01 B APIf ra empty.

Lemma slot_entry : Hcut B APIf ra (Inv_ENTRY B APIf ra empty).
Proof using fx rc B APIf LS SH SK ra empty seg_E01 seg_M01 seg_M02 seg_M03 seg_M04 seg_X01.
  exact (seg_E01 (seg_M01 (seg_M02 (seg_M03 (seg_M04 seg_X01))))).
Qed.

(* The slot obligation, n >= 2^26 included. *)
Theorem slot_holds : slot_goal B APIf ra empty.
Proof using fx rc B APIf LS SH SK ra empty FF EARLY seg_E01 seg_M01 seg_M02 seg_M03 seg_M04 seg_X01.
  intros j _. exact (slot_lib B APIf ra empty FF EARLY slot_entry j).
Qed.

End Slot.

Section Bundle.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.

Theorem slot_of_lemmas : frame_facts_plain B APIf LS SH SK ra empty -> headamp_early_contract ->
  seg_lemmas B APIf ra empty -> slot_goal B APIf ra empty.
Proof.
  intros FF EARLY (HE01 & HM01 & HM02 & HM03 & HM04 & HX01).
  exact (slot_holds B APIf ra empty FF EARLY HE01 HM01 HM02 HM03 HM04 HX01).
Qed.

End Bundle.

(* ---- plain_halts from frame_plain ---- *)
Section Link.
Hypothesis EARLY : headamp_early_contract.
(* The segment lemmas, as the segment files state them once their Sections close (the callee contracts each
   segment takes as a premise are discharged there or by the caller of plain_halts_of_frame). *)
Hypothesis SEGS : forall (fx : FPState) (rc : RunCeil) (B : malloc_syms) (APIf : forall rc : RunCeil, AllocAPI B)
    (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
  frame_facts_plain B APIf LS SH SK ra empty -> seg_lemmas B APIf ra empty.

Theorem plain_halts_of_frame : frame_plain -> Statements.plain_halts.
Proof using EARLY SEGS.
  intros HF. destruct (frame_plain_split HF) as (B & API & LS & SH & SK & ra & empty & FF & OBL).
  apply (OBL [] (fun _ _ => True)).
  - intros a Ha. exact Ha.
  - intros j m m' _ _. exact I.
  - intros mem _. exact I.
  - intros rc fx j Hj.
    exact (slot_of_lemmas B API ra empty FF EARLY (SEGS fx rc B API LS SH SK ra empty FF) j Hj).
Qed.

End Link.
