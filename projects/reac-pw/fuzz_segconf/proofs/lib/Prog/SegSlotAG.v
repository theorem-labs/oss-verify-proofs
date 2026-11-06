(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/LLVMFuzzerTestOneInput_fr.v, with its module paths and module names changed; 486 of its 603 lines of code are new or changed and 410 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/Prog/Seg/Tac_slot.v, with its module paths and module names changed; 67 of its 106 lines of code are new or changed and 564 lines of the source are left out. *)
(* The plain slot of reac-pw/fuzz_segconf LLVMFuzzerTestOneInput at the agreement frame's shape, for ubsan_agrees
   (AgreeSeg.v). Prog/SegSlot.v proves the slot obligation under FrameAPI.frame_facts_plain, whose room conjunct is
   the halts frame's (lib_room -> sb_cap = CAPMAX); the agreement shape AgreeShape.ag_shape has sb_cap = CAP_AG
   (1024), so frame_facts_plain does not hold at it. The slot itself needs only SlotFR.slot_room
   (128 <= sb_cap <= CAPMAX), which ag_shape's room gives (AgreeShape.ag_room_g). Neither the segment statements
   (LLVMFuzzerTestOneInput_c.seg_lemmas) nor SegSlot.slot_early mention the shape, so both are taken at a halts shape
   LSh (any shape with frame_facts_plain); SegSlot's Section Bridge (slot_lib, with Tac_slot.sl_post_g) is restated
   here, word for word, at a shape LS with frame_facts_plain's LIBK and lib_delta conjuncts and
   lib_room LS b n -> slot_room b. This is reac-pw/fuzz_pin's Prog/PinSlotAG.v (commit
   a2a7540da98) for segconf's slot (G = frame_G = longl, GI = GI_SLOT, Post at its own FP state with frm_zero).
   Proves no function by itself (kind: segment lemma of LLVMFuzzerTestOneInput's agreement walk: the composition of
   the plain segment lemmas with the slot at the agreement shape). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import SlotFR SlotInv LLVMFuzzerTestOneInput_c SegSlot.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.Seg Require Import Tac_slot.
Import ListNotations.
Open Scope Z_scope.

Section BridgeAG.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
(* A halts shape: the frame facts of every conjunct that does not mention the shape. lib_shape is a class: every
   use of the shape below names LS, so that resolution does not pick LSh. *)
Variable LSh : lib_shape.
Hypothesis FF : frame_facts_plain B APIf LSh SH SK ra empty.
(* The shape's own conjuncts, with the slot's room. *)
Hypothesis AG_LIBK : forall pl fs K, @LIBK LS pl fs K = K (LL 0 fs []).
Hypothesis AG_DELTA : forall n b, @lib_delta LS n b = b.
Hypothesis AG_ROOM : forall b n, @lib_room LS b n -> slot_room b.
Let API := APIf rc.

(* Tac_slot.sl_post_g at the shape LS. *)
Lemma slot_post_g_ag : forall g c', Post B APIf ra g c' -> Fs.fs_sorted (m_fs (g_md g)) = true ->
  exists (fx' : FPState) L' A' regs' mem' md',
    c' = mkCfg (@YK11.mkst fx' regs' (Z_to_bv 64 ra) mem' (YK11.seg_rom (ms_segs B))) md' /\
    frm_zero (@fp_csr fx') /\
    lib_post_g (LS := LS) B API frame_G SLOT_STACK (g_L g) (g_A g) (g_regs g) (g_mem g) (g_md g) (g_p g) (g_n g)
      (g_b g) (LL 0 (m_fs (g_md g)) []) L' A' regs' mem' md' /\
    GIb (ms_segs B) mem'.
Proof.
  intros g c' (fx' & L' & A' & regs' & mem' & md' & -> & Hfrm & HLP & HSN & HMI & HRE & HPAY & HGI) Hsorted.
  pose proof (sl_segs (LS := LSh) B APIf ra empty FF) as SEGS.
  exists fx', L', A', regs', mem', md'. split; [reflexivity|]. split; [exact Hfrm|].
  split; [|exact HGI].
  destruct HLP as (H1 & H2 & H3 & H4 & H5 & H6 & (vm' & Hmd) & H8 & H9 & H10 & H11 & H12).
  unfold lib_post_g. cbn [ll_ret ll_out ll_fs].
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
  split; [exact H6|].
  split; [exists vm', (m_fds (g_md g)), (m_statpins (g_md g)); split; [rewrite Hmd; apply with_vmmaps_os_upd |
          intros k; reflexivity]|].
  split; [exact H8|]. split; [exact H9|]. split; [exact H10|].
  split; [intros a Ha; rewrite SEGS; split; intros _; apply sl_longl_writable; exact Ha|].
  split; [exact H11|]. split; [exact H12|].
  split; [reflexivity|]. split; [reflexivity|]. split; [exact Hsorted|].
  split; [exact HSN|]. split; [exact HMI|].
  split; [rewrite AG_DELTA; exact HRE|].
  exact HPAY.
Qed.

(* SegSlot.slot_lib at the shape LS (slot_early at LSh). *)
Lemma slot_lib_ag : Hcut B APIf ra (Inv_ENTRY B APIf ra empty) ->
  forall j, lib_contract_g (LS := LS) B API frame_G frame_RELRO (GI_SLOT (ms_segs B)) j ENTRY ra empty SLOT_STACK.
Proof.
  intros HE j L A regs mem md p n pl b K Hpre HGI HR HRO _ Hfrm HK.
  rewrite AG_LIBK.
  destruct Hpre as (HP0 & HLEN & HD & Hres & Hroom & HSink & Hfd & Hsorted & Hfdc & Hsp47).
  pose proof HP0 as (HM & HW & HB & HID & Hra & Hal & Hceil & H63 & Hstw & Htp & Herr & Hp & Hnn & Hpp & Hrod).
  set (g := Ghost pl p (spZ regs) regs L A mem md b).
  assert (Hsp : YK11.getr regs 2 = Z_to_bv 64 (spZ regs)).
  { apply bv_eq. rewrite Z_to_bv_unsigned. unfold spZ. symmetry. apply bv_wrap_small. apply bv_unsigned_in_range. }
  assert (Egn : g_n g = n) by (unfold g_n; cbn [g_in g]; lia).
  assert (HKg : forall c', Post B APIf ra g c' -> realizes (ms_segs B) c' (K (LL 0 (m_fs md) []))).
  { intros c' Hc'. apply HK.
    destruct (slot_post_g_ag g c' Hc' Hsorted) as (fx' & L' & A' & regs' & mem' & md' & E & F0 & LP & HG').
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
        split; [exact (AG_ROOM b n Hroom)|]. split; [exact Hsp|]. split; [exact Htp|].
        exact HGI. }
      split; [rewrite Egn; exact HP0|].
      split; [exact Hsp|]. split; [exact HSink|]. split; [exact HRO|]. split; [exact HR|].
      split; [exact Hres|]. exact Hfrm. }
    exact (SR_realizes (ms_segs B) _ _ _ (HE g _ HEN) HKg).
  - exact (SR_realizes (ms_segs B) _ _ _
             (slot_early (LS := LSh) B APIf ra empty FF g Hsp eq_refl ltac:(rewrite Egn; exact Hbig)
                ltac:(rewrite Egn; exact HP0) HSink HRO Hres Hfrm HGI) HKg).
Qed.

End BridgeAG.

Section BundleAG.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Variable CP : cut_preds.

(* SegSlot.slot_of_lemmas at a shape LS with the slot's room, the other frame facts at a halts shape LSh. *)
Theorem slot_of_lemmas_ag : forall LSh : lib_shape, frame_facts_plain B APIf LSh SH SK ra empty ->
  (forall pl fs K, @LIBK LS pl fs K = K (LL 0 fs [])) -> (forall n b, @lib_delta LS n b = b) ->
  (forall b n, @lib_room LS b n -> slot_room b) ->
  seg_lemmas B APIf ra empty CP -> slot_goal (LS := LS) B APIf ra empty.
Proof.
  intros LSh FF HK HD HR (HE01 & HM01 & HL01 & HL02 & HL03 & HM02 & HV01 & HX01) j _.
  apply (slot_lib_ag B APIf ra empty LSh FF HK HD HR).
  eapply slot_entry; eassumption.
Qed.

End BundleAG.
