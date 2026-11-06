(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/LLVMFuzzerTestOneInput_fr.v, with its module paths and module names changed; 457 of its 575 lines of code are new or changed and 409 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/U/Prog/SegCF/Tac_slot.v, with its module paths and module names changed; 145 of its 169 lines of code are new or changed and 551 lines of the source are left out. *)
(* Cut-free (agreement) copy of lib/U/Prog/Seg/M03.v, over U/Prog/SlotInvCF.v (SR := SRcf). Model:
   reac-pw/fuzz_role's U/Prog/SegCF/*.v copies (role has no M03), as libreac/fuzz_ctrl's released
   U/Prog/SegCF/*.v copy its U/Prog/Seg/*.v: the same text with SlotFR, SlotInv -> SlotInvCF, Seg -> SegCF, the
   segment statements from SegCF/StmtsCF.v, frame_facts_ubsan -> SlotInvCF.frame_facts_cf and the allocator
   contracts in their cut-free forms (frame_allocator_cf, malloc_contract_cfg, free_contract_cf); SlotInvSat.sat_len_bound and sat_bl_bound,
   stated over U/Prog/SlotInv.v's ghost, are read from their copies in SlotInvCF.v.
   The text of the original follows. *)
(* Segment M03 of reac-pw/fuzz_rate LLVMFuzzerTestOneInput (UBSan): [0x14614, 0x14660), K14614 -> K14660
   (U/Prog/LLVMFuzzerTestOneInput_c.v's S_M03). The plain file lib/Prog/Seg/M03.v with the UBSan numbers.
   The cut is at its own FP state (Tac_b8.b8_cut_open). 0x14614 `ld s0,0x30(sp)` (the cut's cell
   S - 592 + 0x30 = buflen), 0x14618 `seqz s5,s0`, 0x1461c `add s5,s0,s5`, 0x14620 `mv a0,s5`: s0 = buflen,
   s5 = a0 = bl = buflen + (buflen = 0) (kM03a); 0x14624 `jal malloc` (ra 0x14628; malloc at 0x16a7c) through
   Tac_b1.b1_malloc_call from hb = hb_pod g pod pp with the request g_bl g in [1, 23] (SlotInvSat.sat_bl_bound;
   hb_bytes <= 5440 + 19744 by SlotInvSat.sat_len_bound), whose continuation gives FR at
   (buf, g_bl g) :: hb_pod g pod pp = hb_buf g buf pod pp, buf <> 0, buf mod 16 = 0, the callee-saved registers and
   the bytes of [S - 592, S) unchanged (the cell S - 592 + 0xd8 = pp).
   Then rate_csv_contract's evt (memset, reac_rate_drivable_csv, check_csv; no trap in [0x14628, 0x14660)), taken
   as a Section hypothesis, runs on MemNorm.normalize_cj of the post-malloc memory through Tac_fp.sl_mid_fp_blk
   with the block (buf, g_bl g): the buf block's cells (Tac_fp.sl_blk_cj, Tac_slot.sl_rw_of_stk), outside the
   image (Tac_b1.b1_blk_rom), below lo = S - 65536; the stack [lo, S - 592) from FR's window (Tac_fp.sl_stk_cj);
   the stack guard's GOT slot 0x1ee78 and the guard 0x50460 from the allocator's AllocExtra.ax_statics
   (Tac_b1.b1_ax) on the post-malloc memory, as bytes by KindBGlue.word_mem_le8 and on the CJ memory by
   MemNorm.bytes_at_normalize_cj_low; mem_inv and task_mem from MemNorm.mem_inv_cj_normalize; frm0 from the cut.
   The evt writes [S - 592 - 8192, S - 592) and the buf block and ends at 0x14660 with s4 = buf, s3 = pod at its
   own FP state (F', fc') with rounding mode 0, which is the FP state of K14660; the cell S - 592 + 0xd8 = pp is
   outside its writes (MemNorm.munch_rel_cj, Tac_b8.b8_ba_munch). Templates: reac-pw/fuzz_role's
   U/Prog/Seg/M01.v and U/Prog/Seg/M02.v.
   No function is proved here. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require Import Contract Img0 FrameAPI KindBGlue.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac FP.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog Require Import LLVMFuzzerTestOneInput_c SlotInvCF.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog.SegCF Require Import StmtsCF.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog.SegCF Require Import Tac_slot Tac_b1 Tac_b8 Tac_fp.
Import ListNotations.
Open Scope Z_scope.

(* `seqz` (sltiu rd, rs, 1) of a word value b: 1 when b = 0, else 0; so `add` makes bl = b + (b = 0). *)
Lemma m03_seqz : forall b, 0 <= b < 2 ^ 64 ->
  bv_unsigned (v_sltiu (Z_to_bv 64 b) 1) = (if b =? 0 then 1 else 0).
Proof.
  intros b Hb. unfold v_sltiu. rewrite (MState.unsigned_lit b) by lia.
  replace (bv_wrap 64 1) with 1 by reflexivity.
  destruct (Z.ltb_spec b 1) as [L|L]; destruct (Z.eqb_spec b 0) as [E|E]; try lia;
    apply MState.unsigned_lit; lia.
Qed.

(* 0x14614 `ld s0,0x30(sp)`; 0x14618 `seqz s5,s0`; 0x1461c `add s5,s0,s5`; 0x14620 `mv a0,s5`;
   0x14624 `jal malloc`. *)
Lemma kM03a : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte) (b sp0 : Z),
  x2 = Z_to_bv 64 sp0 -> 0 <= sp0 -> sp0 + 592 < 2 ^ 64 ->
  ov_read_bytes rsegs m (wa (sp0 + 0x30)) 8 = Some (le8 (Z_to_bv 64 b)) -> 0 <= b < 24 ->
  Exec.evt rsegs
    (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x14628) x2 x3 x4 x5 x6 x7 (Z_to_bv 64 b) x9 (Z_to_bv 64 (rate_bl b))
                           x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 (rate_bl b)) x22 x23 x24 x25 x26
                           x27 x28 x29 x30 x31) F (Z_to_bv 64 0x16a7c) fc None m ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31) F (Z_to_bv 64 0x14614) fc None m ro).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 F fc m ro b sp0 E2 H0 H1 HR Hb.
  subst x2.
  step. step. step. step. step.
  rewrite (m03_seqz b) by lia.
  apply evt_done. reflexivity.
Qed.

(* A header byte value is a byte. *)
Lemma m03_u8_rng : forall g i, 0 <= g_u8 g i < 256.
Proof.
  intros g i. unfold g_u8. destruct (nth_error (g_in g) i) as [b|]; [exact (b1_byte_rng b) | lia].
Qed.

Lemma m03_buflen_rng : forall g, 0 <= g_buflen g < 24.
Proof. intros g. unfold g_buflen. apply Z.mod_pos_bound. lia. Qed.

Section M03.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts_cf B APIf LS SH SK ra empty.
Hypothesis CSV : rate_csv_contract.

Lemma seg_M03 : S_M03 B APIf ra empty.
(* The cut carries its own FP state, so this walk does not read the Section's fx; the slot composition takes the
   five segment lemmas at one binder list, so fx is kept in the statement. *)
Proof using fx rc B APIf LS SH SK ra empty FF CSV.
  unfold S_M03. intros H1 g c (pp & pod & HC).
  eapply (b8_cut_open B APIf ra empty); [exact HC|].
  intros fx' L A regs mem md Hfrm HFR HP (H19 & H26 & HB30 & HBd8).
  pose proof (sl_segs B APIf ra empty FF) as SEGS.
  pose proof (sat_len_bound g) as Hlen.
  pose proof (sat_bl_bound g) as Hbl.
  pose proof (m03_buflen_rng g) as Hbuf.
  pose proof alloc_ceiling_value as HAC.
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & Hsp16 & HSKb & HS47 & HMI).
  destruct (b8_FR_sp B APIf ra empty _ _ _ _ _ _ _ HFR) as (_ & _ & HSKc & _).
  unfold SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME in *.
  (* 0x14614 .. 0x14624: buflen into s0, bl into s5 and a0, then the call. *)
  eapply (b8_run_to B APIf ra empty FF);
    [exact HFR | unfold rmk; apply (kM03a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                     (g_buflen g) (g_S g - 592));
                 [exact Hsp | lia | lia | apply b8_bytes_le8; exact HB30 | exact Hbuf] | intros regs_c HG].
  apply (b1_malloc_call B APIf ra empty FF g (hb_pod g pod pp) L A regs mem md regs_c (g_bl g));
    [exact HFR | exact HP | unfold hb_pod; cbn [length]; lia
     | unfold hb_bytes, hb_pod; cbn [map fold_right snd]; unfold POD_PROPS; lia
     | b8rg HG | b8rg HG | b8rg HG
     | rewrite HG; apply ret_ok_even; reflexivity
     | rewrite HG; reflexivity | lia |].
  intros L' A' regs2 mem2 md2 res HF2 HP2 RP H10' Hres0 Hres16 HKF HKB.
  replace (YK11.getr regs_c 1) with (Z_to_bv 64 0x14628) by (rewrite HG; reflexivity).
  assert (Hinbuf : In (res, g_bl g) (hb_buf g res pod pp)) by (left; reflexivity).
  destruct (b1_hb B APIf ra empty FF g (hb_buf g res pod pp) res (g_bl g) L' A' regs2 mem2 md2 HF2 HP2 Hinbuf)
    as (_ & Hres4096 & Hresc).
  pose proof (b1_blk_rom B APIf ra empty FF g (hb_buf g res pod pp) res (g_bl g) L' A' regs2 mem2 md2 HF2 HP2
                Hinbuf) as HROMbuf.
  pose proof HF2 as (_ & _ & _ & _ & _ & _ & _ & _ & HM2 & _).
  pose proof HF2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hwin2).
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HF2) as (Hsp2 & _ & _ & _ & HMI2).
  unfold fsp, SLOT_FRAME in Hsp2.
  assert (Hspu : bv_unsigned (YK11.getr regs2 2) = g_S g - 592).
  { rewrite Hsp2. apply MState.unsigned_lit. lia. }
  (* The buf block's cells on the CJ-normalized memory. *)
  assert (STbuf : stk rsegs (MemNorm.normalize_cj rsegs mem2) res (res + g_bl g))
    by exact (sl_blk_cj B APIf ra empty FF L' A' mem2 md2 res (g_bl g) HM2 (b1_in_hb _ _ _ _ HP2 Hinbuf)).
  destruct (sl_rw_of_stk _ _ _ res (Z.to_nat (g_bl g)) STbuf ltac:(lia) ltac:(lia)) as (junk & HRWcj).
  (* The stack guard's GOT slot and the guard, from the allocator's static words. *)
  destruct (ax_statics (b1_ax B APIf ra empty FF) L' A' mem2 md2 HM2) as (Hgot & (gv & Hgv & Hguard) & _).
  rewrite (ff_got_guard B APIf ra empty FF), (ff_guard B APIf ra empty FF) in Hgot.
  rewrite (ff_guard B APIf ra empty FF) in Hguard.
  apply KindBGlue.word_mem_le8 in Hgot; [|lia | lia | lia].
  apply KindBGlue.word_mem_le8 in Hguard; [|exact Hgv | lia | lia].
  rewrite SEGS in Hgot, Hguard.
  (* The cell S - 592 + 0xd8 = pp on the post-malloc memory. *)
  assert (HBd8' : bytes_at rsegs mem2 (g_S g - 592 + 0xd8) (le8 (Z_to_bv 64 pp))).
  { apply (b1_ba_mbyte mem mem2 _ _ HBd8). intros i Hi. rewrite length_le8 in Hi.
    apply HKF. unfold fsp, SLOT_FRAME. lia. }
  eapply (sl_mid_fp_blk B APIf ra empty FF fx' g (hb_buf g res pod pp) res (g_bl g) L' A' regs2 mem2 md2
            (Z_to_bv 64 0x14628) _ _ HF2 HP2 Hinbuf).
  - rewrite sl_mkR_of.
    apply CSV with (junk := junk) (mask := g_mask g) (buflen := g_buflen g) (cb := res) (pod := pod)
      (lo := g_S g - 65536) (canary := Z_to_bv 64 gv).
    + exact H10'.
    + exact Hres0.
    + exact Hres16.
    + etransitivity; [exact (RP 21 ltac:(unfold callee_saved; lia))|]. rewrite HG. reflexivity.
    + etransitivity; [exact (RP 8 ltac:(unfold callee_saved; lia))|]. rewrite HG. reflexivity.
    + etransitivity; [exact (RP 26 ltac:(unfold callee_saved; lia))|]. rewrite HG.
      transitivity (getr regs 26); [reflexivity | exact H26].
    + etransitivity; [exact (RP 19 ltac:(unfold callee_saved; lia))|]. rewrite HG.
      transitivity (getr regs 19); [reflexivity | exact H19].
    + exact (m03_u8_rng g 1).
    + exact Hbuf.
    + exact HRWcj.
    + exact HROMbuf.
    + change (rate_bl (g_buflen g)) with (g_bl g). lia.
    + rewrite Hspu. apply sl_stk_cj; [exact HMI2 | unfold SL_TOP; lia | unfold TASK_SIZE; lia |].
      intros a Ha. rewrite <- SEGS. apply Hwin2. unfold SLOT_K, SLOT_STACK. lia.
    + rewrite Hspu. unfold CSV_STACK. lia.
    + rewrite Hspu. Z.div_mod_to_equations. lia.
    + unfold STACK_LO_MIN. lia.
    + rewrite Hspu. lia.
    + rewrite Hspu. intros a Ha. apply (b8_seg_rom_hi B APIf ra empty FF). lia.
    + apply MemNorm.bytes_at_normalize_cj_low;
        [exact HMI2 | rewrite length_le8; unfold RATE_GOT_GUARD, TASK_SIZE; lia | exact Hgot].
    + apply MemNorm.bytes_at_normalize_cj_low;
        [exact HMI2 | rewrite length_le8; unfold RATE_GUARD, TASK_SIZE; lia | exact Hguard].
    + exact Hfrm.
    + exact (MemNorm.mem_inv_cj_inv rsegs _ (MemNorm.mem_inv_cj_normalize rsegs mem2)).
    + exact (MemNorm.mem_inv_cj_task rsegs _ (MemNorm.mem_inv_cj_normalize rsegs mem2)).
  - intros ms (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? &
               ? & F0 & fc0 & m0 & -> & Hfrm0 & MU & WM & _ & _).
    do 5 eexists. split; [reflexivity|]. split; [exact Hfrm0|].
    split.
    + exists [(bv_unsigned (YK11.getr regs2 2) - CSV_STACK, bv_unsigned (YK11.getr regs2 2));
              (res, res + rate_bl (g_buflen g))].
      split; [exact MU|]. split; [exact WM|].
      intros xw Hxw HO. rewrite Hspu in HO. unfold CSV_STACK in HO. cbn [Frame.outside] in HO.
      change (rate_bl (g_buflen g)) with (g_bl g) in HO. unfold SLOT_K, SLOT_STACK.
      destruct (Z_lt_le_dec xw res) as [Hl|Hl]; [left; lia|].
      destruct (Z_lt_le_dec xw (res + g_bl g)) as [Hr|Hr]; [right; lia | left; lia].
    + split; [reflexivity|]. split; reflexivity.
  - intros R F' pc' fc' m0' regs3 m3 HQ Hx Hrel Hsame Hfrm' HF3.
    destruct HQ as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? &
                    ? & ? & F0 & fc0 & m'' & HE & _ & MU & _ & _ & _).
    injection HE; intros; subst.
    pose proof (MemNorm.mem_rel_cj_normalize rsegs mem2 HMI2) as HR0.
    pose proof (MemNorm.munch_rel_cj rsegs _ mem2 (MemNorm.normalize_cj rsegs mem2) m3 _ HR0 Hrel Hsame MU) as MU'.
    apply H1. exists pp, pod, res, (mkFP F0 fc0), L', A', regs3, m3, md2.
    split; [reflexivity|]. split; [exact Hfrm'|]. split; [exact HF3|]. split; [exact HP2|].
    unfold rg. split; [|split].
    + rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
    + rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
    + unfold fsp, SLOT_FRAME.
      apply (b8_ba_munch rsegs _ mem2 m3 _ _ HBd8' MU'). intros i Hi. rewrite length_le8 in Hi.
      rewrite Hspu. unfold CSV_STACK. cbn [Frame.outside].
      change (rate_bl (g_buflen g)) with (g_bl g).
      split; [lia | split; [lia | exact I]].
Qed.

End M03.
