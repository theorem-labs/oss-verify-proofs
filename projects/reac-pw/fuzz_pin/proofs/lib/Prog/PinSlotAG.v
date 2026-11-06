(* The plain slot of reac-pw/fuzz_pin LLVMFuzzerTestOneInput at the agreement frame's shape, for ubsan_agrees
   (AgreePin.v). Prog/PinSlot.v proves the slot obligation under FrameAPI.frame_facts_plain, whose room
   conjunct is the halts frame's (lib_room -> sb_cap = CAPMAX); the agreement frame's shape AgreeShape.ag_shape has
   sb_cap = CAP_AG (1024), so frame_facts_plain does not hold at it. libreac/fuzz_ctrl's released plain slot carried
   the weaker room 128 <= sb_cap <= CAPMAX in its own frame_facts for this reason (Prog/SlotInv.v:71 at
   origin/ossv/recipes 25e3d17bdb50); pin's Prog/SlotInv.slot_room is that bound. Neither the segment statements
   (LLVMFuzzerTestOneInput_c.seg_lemmas) nor PinSlot.slot_early mention the shape, so both are taken at a halts
   shape LSh (any shape with frame_facts_plain), and PinSlot's Section Bridge (slot_post_g, slot_lib) is restated
   here, word for word, at a shape LS with frame_facts_plain's LIBK and lib_delta conjuncts and
   lib_room LS b n -> slot_room b.
   Proves no function by itself (kind: segment lemma of LLVMFuzzerTestOneInput's agreement walk: the composition of
   the plain segment lemmas with the slot at the agreement shape). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c PinSlot.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Prog.Seg Require Import Tac_slot.
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

Lemma slot_post_g_ag : forall g c', Post B APIf ra g c' -> Fs.fs_sorted (m_fs (g_md g)) = true -> frm_zero fp_csr ->
  exists (fx' : FPState) L' A' regs' mem' md',
    c' = mkCfg (@YK11.mkst fx' regs' (Z_to_bv 64 ra) mem' (YK11.seg_rom (ms_segs B))) md' /\
    frm_zero (@fp_csr fx') /\
    lib_post_g (LS := LS) B API [] SLOT_STACK (g_L g) (g_A g) (g_regs g) (g_mem g) (g_md g) (g_p g) (g_n g) (g_b g)
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
  split; [rewrite AG_DELTA; exact HRE|].
  exact HPAY.
Qed.

Lemma slot_lib_ag : Hcut B APIf ra (Inv_ENTRY B APIf ra empty) ->
  forall j, lib_contract_g (LS := LS) B API [] frame_RELRO (fun _ _ => True) j ENTRY ra empty SLOT_STACK.
Proof.
  intros HE j L A regs mem md p n pl b K Hpre _ HR HRO _ Hfrm HK.
  rewrite AG_LIBK.
  destruct Hpre as (HP0 & HLEN & HD & Hres & Hroom & HSink & Hfd & Hsorted & Hfdc & Hsp47).
  pose proof HP0 as (HM & HW & HB & HID & Hra & Hal & Hceil & H63 & Hstw & Htp & Herr & Hp & Hnn & Hpp & Hrod).
  set (g := Ghost pl p (spZ regs) regs L A mem md b).
  assert (Hsp : YK11.getr regs 2 = Z_to_bv 64 (spZ regs)).
  { apply bv_eq. rewrite Z_to_bv_unsigned. unfold spZ. symmetry. apply bv_wrap_small. apply bv_unsigned_in_range. }
  assert (Egn : g_n g = n) by (unfold g_n; cbn [g_in g]; lia).
  assert (HKg : forall c', Post B APIf ra g c' -> realizes (ms_segs B) c' (K (LL 0 (m_fs md) []))).
  { intros c' Hc'. apply HK.
    destruct (slot_post_g_ag g c' Hc' Hsorted Hfrm) as (fx' & L' & A' & regs' & mem' & md' & E & F0 & LP & _).
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
          right. rewrite Egn. split; [exact Hn0|]. apply top_blocks_in. exact Hq. }
        split; [exact HD|]. split; [exact Hal|]. split; [exact Hceil|]. split; [exact Hsp47|].
        split; [exact (AG_ROOM b n Hroom)|]. split; [exact Hsp|]. exact Htp. }
      split; [rewrite Egn; exact HP0|].
      split; [exact Hsp|]. split; [exact HSink|]. split; [exact HRO|]. split; [exact HR|]. exact Hres. }
    exact (SR_realizes (ms_segs B) _ _ _ (HE g _ HEN) HKg).
  - exact (SR_realizes (ms_segs B) _ _ _
             (slot_early (LS := LSh) B APIf ra empty FF g Hsp eq_refl ltac:(rewrite Egn; exact Hbig)
                ltac:(rewrite Egn; exact HP0) HSink HRO Hres) HKg).
Qed.

End BridgeAG.

Section BundleAG.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.

(* PinSlot.slot_of_lemmas at a shape LS with the slot's room, the other frame facts at a halts shape LSh. *)
Theorem slot_of_lemmas_ag : forall LSh : lib_shape, frame_facts_plain B APIf LSh SH SK ra empty ->
  (forall pl fs K, @LIBK LS pl fs K = K (LL 0 fs [])) -> (forall n b, @lib_delta LS n b = b) ->
  (forall b n, @lib_room LS b n -> slot_room b) ->
  seg_lemmas B APIf ra empty -> slot_goal (LS := LS) B APIf ra empty.
Proof.
  intros LSh FF HK HD HR (HE01 & HM01 & HX01) j _.
  exact (slot_lib_ag B APIf ra empty LSh FF HK HD HR (HE01 (HM01 HX01)) j).
Qed.

End BundleAG.
