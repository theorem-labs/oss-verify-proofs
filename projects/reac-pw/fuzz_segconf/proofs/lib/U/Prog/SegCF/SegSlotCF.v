(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/LLVMFuzzerTestOneInput_fr.v, with its module paths and module names changed; 457 of its 575 lines of code are new or changed and 409 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/U/Prog/SegCF/Tac_slot.v, with its module paths and module names changed; 229 of its 265 lines of code are new or changed and 539 lines of the source are left out. *)
(* The cut-free (agreement) slot of reac-pw/fuzz_segconf LLVMFuzzerTestOneInput (UBSan build): lib/U/Prog/SegSlot.v
   copied over U/Prog/SlotInvCF.v, as reac-pw/fuzz_pin's U/Prog/SegCF/PinSlotCF.v copies its U/Prog/PinSlot.v
   (commit a2a7540da98): the same text with SlotInvCF imported after SlotFR / SlotInv, the
   segment statements from SegCF/StmtsCF.v, Seg -> SegCF for Tac_slot, frame_facts_ubsan ->
   SlotInvCF.frame_facts_cf; slot_lib proves lib_contract_cg (crealizes B, by SR_realizes_ms) for lib_contract_g;
   frame_facts_concrete and Section Link (ubsan_halts) are dropped (the agreement top, AgreeSeg.v, takes the
   concrete instance). What is kept:
   - the n >= 2^26 run (early_evt, slot_early: 0x13888 .. 0x138c4 `bnez a2` taken to 0x1420c and the epilogue);
   - Section Bridge: slot_lib: H(ENTRY) -> lib_contract_cg with G = frame_G and GI = GI_SLOT for every j;
   - Section Slot: the eight CF segment statements as hypotheses, the file loop by downward induction over the
     turn f (vac_K139e4, turn_file, loop_files), H(ENTRY) (slot_entry) and slot_holds : SlotInvCF.slot_goal;
   - Section Bundle: slot_of_lemmas (frame_facts_cf and StmtsCF.seg_lemmas give slot_goal).
   Proves no function by itself (kind: segment lemma of LLVMFuzzerTestOneInput's agreement walk: the
   composition of the cut-free segment lemmas with the cut-free slot, the loop induction and the n >= 2^26 run). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import YH02 YI5b YI5c YL0s YN2b.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Contract Img0 FrameAPI SlotAgree.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require KindBGlue FrameSlotG FrameProof.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import ZAllocator ZTraceSpec SlotTopG.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import SlotFR SlotInv LLVMFuzzerTestOneInput_c SlotInvCF.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog.SegCF Require Import StmtsCF.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog.SegCF Require Import Tac_slot.
From OSSVerify.reac_pw.fuzz_segconf Require Statements.
Import ListNotations.
Open Scope Z_scope.

(* ---- n >= 2^26: [0x13888, 0x138c4] then the branch to 0x1420c and the epilogue [0x1420c, 0x14248] ---- *)
Lemma top_bv_eqb : forall a b, -2 ^ 63 <= a < 2 ^ 63 -> -2 ^ 63 <= b < 2 ^ 63 ->
  bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof.
  intros a b Ha Hb. unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with 18446744073709551616.
  destruct (Z.eqb_spec a b) as [->|Hn]; [apply Z.eqb_refl|]. apply Z.eqb_neq.
  intros E. apply Hn. Z.div_mod_to_equations. lia.
Qed.

(* 0x138c4 `bnez a2, 0x1420c` with a2 = n >> 26 <> 0: taken. *)
Lemma early_cond : forall u, 2 ^ 26 <= u < 2 ^ 64 ->
  negb (bv_eqb (Z_to_bv 64 (Z.shiftr u 26)) (Z_to_bv 64 0)) = true.
Proof.
  intros u Hu. rewrite Z.shiftr_div_pow2 by lia.
  assert (H1 : 1 <= u / 2 ^ 26) by (apply Z.div_le_lower_bound; lia).
  assert (H2 : u / 2 ^ 26 < 2 ^ 38) by (apply Z.div_lt_upper_bound; lia).
  rewrite (top_bv_eqb (u / 2 ^ 26) 0) by lia.
  destruct (Z.eqb_spec (u / 2 ^ 26) 0); [lia | reflexivity].
Qed.

Lemma early_evt :
  forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S lo : Z),
    stk rsegs m lo S -> lo + 240 <= S -> S < 2 ^ 64 -> mem_inv rsegs m ->
    2 ^ 26 <= bv_unsigned a1 ->
    evt rsegs
      (fun ms' => exists (sp' a2' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp' gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2' a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         sp' = Z_to_bv 64 S /\
         munch [(S - 240, S)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo S)
      (MS (mkR ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13888) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m S lo ST LO HS MI Ha1.
  pose proof (munch_refl [(S - 240, S)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 a1) as Ra1. unfold bv_modulus in Ra1. change (2 ^ Z.of_N 64) with (2 ^ 64) in Ra1.
  assert (S0 : 0 <= lo) by (destruct ST as [H _]; exact H).
  carve_frame 240%nat ST.
  do 16 step.
  if_true_by (early_cond (bv_unsigned a1) ltac:(lia)).
  do 16 step.
  release_frame FR ST S.
  finish.
  all: try (f_equal; lia).
Qed.

Lemma top_ret_pc_ra : forall z, z mod 2 = 0 -> ret_pc (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. assert (E : Z_to_bv 64 z = Z_to_bv 64 (z mod 2 ^ 64)).
  { apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
    rewrite Zmod_mod. reflexivity. }
  rewrite E. apply ret_pc_even; [apply Z.mod_pos_bound; lia | rewrite KindBGlue.kb_mod2_land; exact Hz].
Qed.

Lemma top_blocks_in : forall L A p n, In (p, n) (user_blocks A) -> In (ptr_addr L p, n) (blocks L A).
Proof. intros L A p n H. unfold blocks. apply in_map_iff. exists (p, n). split; [reflexivity | exact H]. Qed.

(* ---- H(ENTRY) -> the slot obligation ---- *)
Section Bridge.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts_cf B APIf LS SH SK ra empty.
Let API := APIf rc.

Lemma slot_early : forall g,
  YK11.getr (g_regs g) 2 = Z_to_bv 64 (g_S g) -> spZ (g_regs g) = g_S g -> 2 ^ 26 <= g_n g ->
  lib_pre B API SLOT_STACK empty (g_L g) (g_A g) (g_regs g) (g_mem g) (g_md g) ra (g_p g) (g_n g) ->
  sink_none B (g_mem g) (g_md g) -> ro_agree (ms_segs B) (g_mem g) -> res_ok_slots (g_A g) (g_b g) ->
  frm_zero fp_csr -> GIb (ms_segs B) (g_mem g) ->
  SR (ms_segs B) (mkCfg (YK11.mkst (g_regs g) (Z_to_bv 64 ENTRY) (g_mem g) (YK11.seg_rom (ms_segs B))) (g_md g))
    (Post B APIf ra g).
Proof.
  intros g Hsp Hspz Hn Hpre Hsn HMI Hres Hfrm HGI.
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
  eapply (sl_run (g_regs g) (Z_to_bv 64 ENTRY) (g_mem g) (g_md g)); [exact Hh | exact Hl | exact HMI | | |].
  - rewrite sl_mkR_of. unfold ENTRY. rewrite Hsp.
    apply early_evt with (lo := g_S g - 65536).
    + apply sl_stk_norm; [exact HMI | unfold SL_TOP in *; lia | lia |].
      intros a Ha. rewrite <- SEGS. apply Hstw. rewrite Esp. exact Ha.
    + lia.
    + lia.
    + exact (mem_inv_normalize rsegs (g_mem g)).
    + rewrite En. lia.
  - intros ms (? & ? & ? & -> & _). do 3 eexists. reflexivity.
  - intros R pc' m0' HQ regs' m' Hx Hrel' Hsame.
    destruct HQ as (sp' & a2' & m'' & HE & Esp' & MU & WM & MI' & ST').
    injection HE; intros; subst.
    pose proof (mem_rel_normalize rsegs (g_mem g) HMI) as HR0.
    assert (MU' : Frame.munch [(g_S g - 240, g_S g)] (g_mem g) m')
      by exact (munch_rel rsegs _ (g_mem g) (normalize rsegs (g_mem g)) m' m'' HR0 Hrel' Hsame MU).
    assert (WM' : Frame.wmono rsegs (g_mem g) m')
      by exact (wmono_rel rsegs (g_mem g) (normalize rsegs (g_mem g)) m' m'' HR0 Hrel' Hsame WM).
    assert (Hro' : ro_agree rsegs m') by exact (ro_agree_same rsegs (g_mem g) m' HMI Hsame).
    assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ (g_S g - 240 <= a < g_S g) ->
                 m' (Z_to_bv 64 a) = g_mem g (Z_to_bv 64 a)).
    { apply (sl_unch _ _ _ (g_S g - 240) (g_S g) MU').
      intros x Hx0 O. destruct (Z_le_dec (g_S g - 240) x); destruct (Z_lt_dec x (g_S g)); try lia;
        exfalso; apply O; cbn [Frame.outside]; (split; [lia | exact I]). }
    assert (LOW : forall a, 0 <= a < YM05.alloc_ceiling -> m' (Z_to_bv 64 a) = g_mem g (Z_to_bv 64 a)).
    { intros a Ha. apply UN; lia. }
    apply SR_ret. unfold Post. rewrite SEGS.
    exists fx, (g_L g), (g_A g), regs', m', (g_md g).
    split; [rewrite Hra, (top_ret_pc_ra ra HRA); reflexivity|].
    split; [exact Hfrm|].
    split.
    + unfold lib_post. rewrite SEGS.
      split.
      { apply (KindBGlue.kb_MR_A B API (g_L g) (g_A g) (g_mem g) m' (g_md g) [(g_S g - 240, g_S g)] HM).
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
      split.
      { intros i Hi. try rewrite SEGS.
        exact (proj1 (sl_eq_at _ _ _ (LOW (g_p g + i) ltac:(rewrite <- Eq; lia)))). }
      unfold GIb in *. rewrite SEGS in HGI.
      rewrite <- HGI. exact (proj1 (sl_eq_at _ _ _ (LOW (LONGL + LONGL_W) ltac:(unfold SL_TOP, LONGL, LONGL_W in *; lia)))).
Qed.

Lemma slot_lib : Hcut B APIf ra (Inv_ENTRY B APIf ra empty) ->
  forall j, lib_contract_cg B API frame_G frame_RELRO (GI_SLOT (ms_segs B)) j ENTRY ra empty SLOT_STACK.
Proof.
  intros HE j L A regs mem md p n pl b K Hpre HGI HR HRO _ Hfrm HK.
  rewrite (ff_libk B APIf ra empty FF).
  destruct Hpre as (HP0 & HLEN & HD & Hres & Hroom & HSink & Hfd & Hsorted & Hfdc & Hsp47).
  pose proof HP0 as (HM & HW & HB & HID & Hra & Hal & Hceil & H63 & Hstw & Htp & Herr & Hp & Hnn & Hpp & Hrod).
  set (g := Ghost pl p (spZ regs) regs L A mem md b).
  assert (Hsp : YK11.getr regs 2 = Z_to_bv 64 (spZ regs)).
  { apply bv_eq. rewrite Z_to_bv_unsigned. unfold spZ. symmetry. apply bv_wrap_small. apply bv_unsigned_in_range. }
  assert (Egn : g_n g = n) by (unfold g_n; cbn [g_in g]; lia).
  assert (HKg : forall c', Post B APIf ra g c' -> crealizes B c' (K (LL 0 (m_fs md) []))).
  { intros c' Hc'. apply HK.
    destruct (sl_post_g B APIf ra empty FF g c' Hc' Hsorted) as (fx' & L' & A' & regs' & mem' & md' & E & F0 & LP & HG').
    exists fx', L', A', regs', mem', md'. split; [exact E|]. split; [exact F0|]. split; [|exact HG'].
    rewrite Egn in LP. exact LP. }
  destruct (Z_lt_le_dec n (2 ^ 26)) as [Hsm|Hbig].
  - assert (HEN : Inv_ENTRY B APIf ra empty g
                    (mkCfg (YK11.mkst regs (Z_to_bv 64 ENTRY) mem (YK11.seg_rom (ms_segs B))) md)).
    { unfold SLOT_K, SLOT_STACK in *.
      split; [reflexivity|].
      split.
      { split; [rewrite Egn; lia|]. split.
        { destruct Hpp as [[-> ->] | [Hn0 (q & Hq & <-)]]; [left; rewrite Egn; split; reflexivity|].
          right. rewrite Egn. split; [exact Hn0|]. apply top_blocks_in. exact Hq. }
        split; [exact HD|]. split; [exact Hal|]. split; [exact Hceil|]. split; [exact Hsp47|].
        split; [exact (ff_room B APIf ra empty FF b n Hroom)|]. split; [exact Hsp|]. split; [exact Htp|].
        exact HGI. }
      split; [rewrite Egn; exact HP0|].
      split; [exact Hsp|]. split; [exact HSink|]. split; [exact HRO|]. split; [exact HR|].
      split; [exact Hres|]. exact Hfrm. }
    exact (SR_realizes_ms B (ms_segs B) eq_refl _ _ _ (HE g _ HEN) HKg).
  - exact (SR_realizes_ms B (ms_segs B) eq_refl _ _ _ (slot_early g Hsp eq_refl ltac:(rewrite Egn; exact Hbig)
             ltac:(rewrite Egn; exact HP0) HSink HRO Hres Hfrm HGI) HKg).
Qed.

End Bridge.

(* ---- The composition: ENTRY -> K13984 -> K139e4 0 -> (turns f: K13aac f -> K13c34 f -> K139e4 (S f) | K13c3c)
        -> K13e90 -> K141ec -> RET ---- *)
Section Slot.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Variable CP : cut_preds.
Hypothesis FF : frame_facts_cf B APIf LS SH SK ra empty.

Hypothesis seg_E01 : S_E01 B APIf ra empty CP.
Hypothesis seg_M01 : S_M01 B APIf ra empty CP.
Hypothesis seg_L01 : S_L01 B APIf ra empty CP.
Hypothesis seg_L02 : S_L02 B APIf ra empty CP.
Hypothesis seg_L03 : S_L03 B APIf ra empty CP.
Hypothesis seg_M02 : S_M02 B APIf ra empty CP.
Hypothesis seg_V01 : S_V01 B APIf ra empty CP.
Hypothesis seg_X01 : S_X01 B APIf ra empty CP.

(* Past the last turn the loop head holds no state: f < 4 (Inv_K139e4's bound; nfiles = 1 + u8 % 4 <= 4). *)
Lemma vac_K139e4 : forall f, (4 <= f)%nat -> Hat B APIf ra (Inv_K139e4 B APIf ra empty CP) f.
Proof. intros f Hf g c (Hf' & _). lia. Qed.

(* One file turn: L01 (to malloc(text)'s return), L02 (to free(text)), L03 (free(text) and the back edge). *)
Lemma turn_file : forall f, Hcut B APIf ra (Inv_K13c3c B APIf ra empty CP) ->
  Hat B APIf ra (Inv_K139e4 B APIf ra empty CP) (S f) -> Hat B APIf ra (Inv_K139e4 B APIf ra empty CP) f.
Proof. intros f Hae0 HS. exact (seg_L01 f (seg_L02 f (seg_L03 f HS Hae0))). Qed.

(* The file loop: H(K139e4 f) for every turn f, by induction down from the bound (ctrl's loop_frames). *)
Lemma loop_files : Hcut B APIf ra (Inv_K13c3c B APIf ra empty CP) ->
  forall f, Hat B APIf ra (Inv_K139e4 B APIf ra empty CP) f.
Proof.
  intros Hae0.
  assert (IND : forall k f, (4 <= f + k)%nat -> Hat B APIf ra (Inv_K139e4 B APIf ra empty CP) f).
  { induction k as [|k IH]; intros f Hk.
    - exact (vac_K139e4 f ltac:(lia)).
    - destruct (Nat.lt_ge_cases f 4) as [Hf|Hf]; [|exact (vac_K139e4 f Hf)].
      exact (turn_file f Hae0 (IH (S f) ltac:(lia))). }
  intros f. exact (IND 4%nat f ltac:(lia)).
Qed.

Lemma slot_entry : Hcut B APIf ra (Inv_ENTRY B APIf ra empty).
Proof. exact (seg_E01 (seg_M01 (loop_files (seg_M02 (seg_V01 seg_X01)) 0%nat))). Qed.

(* The slot obligation, n >= 2^26 included. *)
Theorem slot_holds : slot_goal B APIf ra empty.
Proof. intros j _. exact (slot_lib B APIf ra empty FF slot_entry j). Qed.

End Slot.

Section Bundle.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Variable CP : cut_preds.

Theorem slot_of_lemmas : frame_facts_cf B APIf LS SH SK ra empty -> seg_lemmas B APIf ra empty CP ->
  slot_goal B APIf ra empty.
Proof.
  intros FF (HE01 & HM01 & HL01 & HL02 & HL03 & HM02 & HV01 & HX01).
  exact (slot_holds B APIf ra empty CP FF HE01 HM01 HL01 HL02 HL03 HM02 HV01 HX01).
Qed.

End Bundle.
