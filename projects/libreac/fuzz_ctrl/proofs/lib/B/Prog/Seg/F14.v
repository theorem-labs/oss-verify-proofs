(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths and module names changed; 748 of its 797 lines of code are new or changed and 962 lines of the source are left out. *)
(* Segment F14 of fuzz_ctrl LLVMFuzzerTestOneInput (asan-ubsan, image B), libreac v1.9.0: 0x8235c-0x82374, the
   call of the bcmp wrapper (0x42aac) at 0x82374; no trap row, no shadow row.  The segment starts at the post-call
   cut 0x8235c (the exit cut of F13), tests the sum flag s9 and, on the zero arm, runs through the bcmp call to the
   return point 0x82378 (the entry cut of F15):

     0x8235c  bltz a0,82fa4     -- NOT taken: a0 = fg_ret of the fragment class, 0 or 1 here (the record, the
                                   record buffer and the three output cells are all non-zero, so the class is not
                                   FgRefuse).
     0x82360  mv   s7,a0        -- s7 := the fragment result (F15 reads it at 0x8237c `bne s7,s6`).
     0x82364  bnez s9,8237c     -- s9 = b2z (t_sum_ok j) (FM) <> 0: land at the split cut 0x8237c.
     0x82368  li   a2,72
     0x8236c  ld   a0,200(s1)   -- a0 := [A + 200] = fr + 336, the before-call copy of the record (FLI's spill).
     0x82370  ld   a1,208(s1)   -- a1 := [A + 208] = fragb fr, the record itself (FLI's spill).
     0x82374  jal  wrapper_bcmp -- compares the two 72-byte records; returns to the exit cut 0x82378.

   v1.8 (0x822ec-0x82308) loaded the sum flag from the spill [s1+288] (`ld a0,288(s1); bnez a0`) and the record
   pointer from [s1+240]; v1.9.0 keeps the flag in s9 and the record pointer in [s1+208].  Image B holds the spill
   base A in s1 (reg 9), the record buffer Phi in s2 (reg 18), the declared length in s4 (reg 20), and moves the
   fragment result into s7 (reg 23).

   The entry cut is SlotInv's Inv_B8235c_at (v1.9 pc 0x8235c; the exit cut of F13) and the two exit cuts are
   SlotInv's Inv_B8237c_at (0x8237c) / Inv_B82378_at (0x82378) (the entry cuts of F15; cut names are still v1.8's):
   LK / FLV / FM / FSj on FCUTP plus s7 = the fragment result, and at 0x82378 also t_sum_ok j = false and a0 = the
   compare result.  FLV is derived here: its five
   pointer spills are FLI's (carried by LK), and when the turn opens a record (t_rf j = 1) the class is FgClose, so
   the fragment's post memory fg_mem (carried by the entry cut) gives [fr + 272] = fragb fr + 19 and
   [fr + 304] = f_pll.

   The bcmp wrapper is the Section Hypothesis HBCMP.  Its contract asks for mem_inv, which push 5c keeps out of
   the cut: the call runs on the normalized memory through MemNorm.evt_normalize (f14_evt_0c wraps f14_evt_0c_n).
   The wrapper writes only its own stack window [sp - 4560, sp), which FRA's placement (fra_frame) keeps clear of
   the frame, of the spill area at or above sp and of the low image, so FRA crosses the call with
   F13.fra_mem_call plus Tac_slot.sl_fra_move, with the entry-anchored slot window rebuilt from the call's stack
   post on [sp - FN_STACK, sp); ENT crosses it with Tac_slot.ent_store / ent_mat. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Fpu Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Spec Require StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcRec RcFrag RcFragLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv memcmp_c bcmp_wrap_c
  reac_ctrl_identity_fragment_c RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot F13.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.FrameAPI.
Module SF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Spec.StrFun.
Module MN := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.MemNorm.

Local Notation memcmp_model := SF.memcmp_model.

(* ---- the fragment class at this call site. ---- *)

(* fg_ret is 0 or 1 unless the call refuses (one of the five pointers is 0). *)
Lemma f14_ret_range : forall f fr pa pp pn len st g, f <> 0 -> fr <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 ->
  0 <= fg_ret (fg_class f fr pa pp pn len st g) <= 1.
Proof.
  intros f fr pa pp pn len st g H1 H2 H3 H4 H5. rewrite rf_class_nn by assumption.
  destruct (fg_fr len g); cbn [negb].
  - destruct (bat g 19 =? 1); cbn [fg_ret].
    + lia.
    + destruct (fg_keep st g); cbn [negb].
      * destruct (fg_close st g); cbn [negb fg_ret]; lia.
      * cbn [fg_ret]; lia.
  - cbn [fg_ret]; lia.
Qed.

Lemma f14_ret1_close : forall c, fg_ret c = 1 -> c = FgClose.
Proof. intros c H. destruct c; cbn [fg_ret] in H; try discriminate; reflexivity. Qed.

(* At this call site the class is the model's class of the turn: the five pointers are non-zero, and past the
   refusal test the class reads only len / st / g. *)
Lemma f14_frcl_fcls : forall g j fr phi, fragb fr <> 0 -> phi <> 0 ->
  fr + 256 <> 0 -> fr + 272 <> 0 -> fr + 304 <> 0 ->
  frcl g j fr phi = fcls (flen g j) (t_FG (g_in g) j) (t_g (g_in g) j).
Proof.
  intros g j fr phi H1 H2 H3 H4 H5. unfold frcl, fcls.
  rewrite (rf_class_nn (fragb fr) phi (fr + 256) (fr + 272) (fr + 304)) by assumption.
  rewrite (rf_class_nn 1 1 1 1 1) by lia. reflexivity.
Qed.

Lemma f14_trf_of_frcl : forall g j fr phi, fragb fr <> 0 -> phi <> 0 ->
  fr + 256 <> 0 -> fr + 272 <> 0 -> fr + 304 <> 0 ->
  t_rf (g_in g) j = fg_ret (frcl g j fr phi).
Proof.
  intros g j fr phi H1 H2 H3 H4 H5. unfold t_rf, fg_rf.
  rewrite (f14_frcl_fcls g j fr phi) by assumption. unfold flen. reflexivity.
Qed.

(* A carried bytes_at of 8 bytes in the form the load tactic consumes. *)
Lemma f14_rd8 : forall m a bs, bytes_at rsegs m a bs -> length bs = 8%nat ->
  ov_read_bytes rsegs m (wa a) 8 = Some bs.
Proof.
  intros m a bs H Hl.
  pose proof (bytes_at_ov_read rsegs m a bs 0 8 H ltac:(lia)) as HH.
  change (Z.of_nat 0) with 0%Z in HH. rewrite Z.add_0_r, skipn_O, firstn_all2 in HH by lia. exact HH.
Qed.

(* A run that writes nothing. *)
Lemma munch_self : forall W (m : word -> option byte), munch W m m.
Proof. intros W m a _. reflexivity. Qed.

(* FLV across a run that keeps s1 and misses the save area and the two output cells it names. *)
Lemma flv_keep : forall g fr j (regs regs' : bvmap 5 word) (m m' : word -> option byte) (W : list (Z * Z)) (A : Z),
  FLV g fr j regs m -> rg regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 ->
  getr regs' 9 = getr regs 9 -> munch W m m' -> (forall x, A <= x < A + 448 -> outside W x) ->
  (forall x, fr + 272 <= x < fr + 280 -> outside W x) -> (forall x, fr + 304 <= x < fr + 312 -> outside W x) ->
  FLV g fr j regs' m'.
Proof.
  intros g fr j regs regs' m m' W A (S120 & S128 & S256 & S304 & S296 & Hc) H9 HA0 HA1 E9 MU Hout Hpp Hpn.
  assert (K : forall off v, 0 <= off -> off + 8 <= 448 -> spill regs m off v -> spill regs' m' off v).
  { intros off v Ho0 Ho1 Hs.
    eapply spill_keep;
      [exact Hs | exact H9 | exact HA0 | exact HA1 | exact Ho0 | exact Ho1 | exact E9 | exact MU |].
    intros x Hx. apply Hout. lia. }
  split; [apply K; [lia | lia | exact S120]|].
  split; [apply K; [lia | lia | exact S128]|].
  split; [apply K; [lia | lia | exact S256]|].
  split; [apply K; [lia | lia | exact S304]|].
  split; [apply K; [lia | lia | exact S296]|].
  intros Hrf. destruct (Hc Hrf) as (Hq1 & Hq2). unfold q64 in *. split.
  - eapply fl_bytes; [exact Hq1 | exact MU |]. rewrite length_le8. intros x Hx. apply Hpp. lia.
  - eapply fl_bytes; [exact Hq2 | exact MU |]. rewrite length_le8. intros x Hx. apply Hpn. lia.
Qed.

(* a Theorem Labs lane's record bundles (SlotInv's FRB / FRX) and the turn's records across a run of this segment: the bcmp
   wrapper writes only its stack scratch, which misses the save area, the frame, Phi's record block and the two
   6-byte compare operands (FRB states those against the wrapper's scratch itself). *)
Lemma f14_frb_keep : forall g j fr phi A kp (regs regs' : bvmap 5 word) (m m' : word -> option byte)
    (W : list (Z * Z)),
  FRB g j fr phi A kp regs m -> munch W m m' -> meta_kept m m' ->
  AC.aspZ regs' = AC.aspZ regs ->
  (forall x, A <= x < A + 448 -> outside W x) ->
  (forall x, phi <= x < phi + 50 -> outside W x) ->
  (forall x, in_shadow x -> outside W x) ->
  (forall x, kp + 20 <= x < kp + 22 -> outside W x) ->
  (forall L x, (L + 6 <= AC.aspZ regs - BW.BCMP_WRAP_K \/ AC.aspZ regs <= L) -> L <= x < L + 6 ->
     outside W x) ->
  FRB g j fr phi A kp regs' m'.
Proof.
  intros g j fr phi A kp regs regs' m m' W
    (Hw112 & (w272 & Hq272 & Hw272b & Hw272t & Hw272f) & Hkp112 & HkpBC & Hkp2688 & HphiG & H8819)
    MU Hmeta Easp OA Ophi Osh Okp OL.
  unfold FRB. rewrite Easp.
  split; [exact Hw112|].
  split.
  { exists w272. split; [|split; [exact Hw272b | split; [exact Hw272t | exact Hw272f]]].
    unfold q64 in *. eapply fl_bytes; [exact Hq272 | exact MU |].
    rewrite length_le8. intros x Hx. apply OA. lia. }
  split; [exact Hkp112|]. split; [exact HkpBC|]. split; [exact Hkp2688|].
  split; [exact HphiG|].
  intros H8.
  destruct (H8819 H8) as (HRI &
    (L & ls & rs & QL & HBL1 & HLl & HBR1 & HLr & Hmm1 & HAL1 & Hap6 & Hap7 & HLBC & HLA & HL2688) &
    (L2 & ls2 & rs2 & QL2 & HBL2 & HLl2 & HBR2 & HLr2 & Hmm2 & HAL2 & Hap62 & Hap72 & HL2BC & HL2A & HL22688)).
  split.
  { apply (rec_inv_keep g j phi A kp m m' W HRI MU Ophi); [intros x Hx; apply OA; lia | exact Osh | exact Okp]. }
  split.
  { exists L, ls, rs.
    split.
    { unfold q64 in *. eapply fl_bytes; [exact QL | exact MU |]. rewrite length_le8. intros x Hx. apply OA. lia. }
    split.
    { eapply fl_bytes; [exact HBL1 | exact MU |]. rewrite HLl. intros x Hx. apply (OL L x HLBC). lia. }
    split; [exact HLl|].
    split.
    { eapply fl_bytes; [exact HBR1 | exact MU |]. rewrite HLr. intros x Hx. apply Ophi. lia. }
    split; [exact HLr|]. split; [exact Hmm1|].
    split; [eapply addressable_kept; [exact HAL1 | exact Hmeta]|].
    split; [exact Hap6|]. split; [exact Hap7|].
    split; [exact HLBC|]. split; [exact HLA | exact HL2688]. }
  { exists L2, ls2, rs2.
    split.
    { unfold q64 in *. eapply fl_bytes; [exact QL2 | exact MU |]. rewrite length_le8. intros x Hx. apply OA. lia. }
    split.
    { eapply fl_bytes; [exact HBL2 | exact MU |]. rewrite HLl2. intros x Hx. apply (OL L2 x HL2BC). lia. }
    split; [exact HLl2|].
    split.
    { eapply fl_bytes; [exact HBR2 | exact MU |]. rewrite HLr2. intros x Hx. apply Ophi. lia. }
    split; [exact HLr2|]. split; [exact Hmm2|].
    split; [eapply addressable_kept; [exact HAL2 | exact Hmeta]|].
    split; [exact Hap62|]. split; [exact Hap72|].
    split; [exact HL2BC|]. split; [exact HL2A | exact HL22688]. }
Qed.
Lemma f14_frx_keep : forall g j fr phi (m m' : word -> option byte) (W : list (Z * Z)),
  FRX g j fr phi m -> munch W m m' -> meta_kept m m' -> wmono rsegs m m' ->
  (forall x, phi <= x < phi + 50 -> outside W x) ->
  (forall x, fr <= x < fr + 3136 -> outside W x) ->
  FRX g j fr phi m'.
Proof.
  intros g j fr phi m m' W (Hlong & Hrec & Harec & (idb & Lid & Hidc) & Haid & Hrf) MU Hmeta WM Ophi Ofr.
  split.
  { intros Hl. destruct (Hlong Hl) as (Hg & Ha & Hp). split.
    - eapply fl_bytes; [exact Hg | exact MU |]. rewrite t_g_length. intros x Hx. apply Ophi. lia.
    - split; [eapply addressable_kept; [exact Ha | exact Hmeta] | exact Hp]. }
  split.
  { eapply fl_bytes; [exact Hrec | exact MU |]. rewrite frrec_length. intros x Hx. apply Ofr. unfold fragb in *. lia. }
  split; [eapply addressable_kept; [exact Harec | exact Hmeta]|].
  split.
  { exists idb. split; [exact Lid|].
    destruct Hidc as ((Hwf & Hb) & (Hw0 & Hw1 & Hw)).
    split; [split; [exact Hwf|]|].
    - eapply fl_bytes; [exact Hb | exact MU |].
      cbn [LCl.cells_bytes LCl.cbytes]. rewrite app_nil_r, Lid. intros x Hx. apply Ofr. lia.
    - split; [exact Hw0|]. split; [exact Hw1|]. intros i Hi. exact (WM _ (Hw i Hi)). }
  split; [eapply addressable_kept; [exact Haid | exact Hmeta]|].
  intros H1. destruct (Hrf H1) as (Hb1 & Hb2 & Hb3 & Hb4 & Hb5 & AD & HU & HADb & HAD).
  split; [exact Hb1|]. split; [exact Hb2|]. split; [exact Hb3|]. split; [exact Hb4|]. split; [exact Hb5|].
  exists AD. split.
  { unfold u16 in *. eapply fl_bytes; [exact HU | exact MU |]. rewrite length_le2. intros x Hx. apply Ofr. lia. }
  split; [exact HADb | exact HAD].
Qed.
Lemma f14_recf_keep : forall g fr j (m m' : word -> option byte) (W : list (Z * Z)),
  RECF g fr j m -> munch W m m' -> (forall x, fr <= x < fr + 3136 -> outside W x) -> RECF g fr j m'.
Proof.
  intros g fr j m m' W ((Hid & Hidok) & (Hfg & Hfgok)) MU Ofr.
  split; [split; [|exact Hidok] | split; [|exact Hfgok]].
  - unfold IDBe in *. eapply fl_bytes; [exact Hid | exact MU |]. rewrite t_IDr_length.
    intros x Hx. apply Ofr. lia.
  - unfold FGBe in *. eapply fl_bytes; [exact Hfg | exact MU |]. rewrite t_FG_length.
    intros x Hx. apply Ofr. lia.
Qed.

(* ---- the s9 <> 0 arm (t_sum_ok j): three instructions, no memory change, landing at 0x8237c. ---- *)
Lemma f14_evt_10 :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r v : Z),
    a0v = Z_to_bv 64 r -> 0 <= r <= 1 ->
    s9 = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> v <> 0 ->
    evt rsegs
      (fun ms' => ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0v
                                a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 r) s8 s9 s10 s11 t3 t4 t5 t6)
                             Fr (Z_to_bv 64 0x8237c) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x8235c) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m r v -> Hr -> Hvb Hvnz.
  assert (Hbltz : bv_lts (Z_to_bv 64 r) (Z_to_bv 64 0) = false).
  { unfold bv_lts. rewrite (signed_lit r) by lia. rewrite (signed_lit 0) by lia. apply Z.ltb_ge. lia. }
  step.
  replace (bv_lts (Z_to_bv 64 r) (Z_to_bv 64 0)) with false by (symmetry; exact Hbltz). cbv iota.
  step. step.
  assert (EV : bv_unsigned (Z_to_bv 64 v) = v) by (apply unsigned_lit; lia).
  replace (negb (bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0))) with true
    by (symmetry; apply Bool.negb_true_iff; unfold bv_eqb; rewrite EV;
        change (bv_unsigned (Z_to_bv 64 0)) with 0; apply Z.eqb_neq; exact Hvnz).
  cbv iota.
  apply evt_done. reflexivity.
Qed.

(* ---- the s9 = 0 arm against the wrapper contract as stated (mem_inv): the two record loads and the bcmp
   call, landing at 0x82378. ---- *)
Lemma f14_evt_0c_n :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A r L R vcmp lo : Z) (ls rs : list byte),
    bcmp_wrap_contract ->
    s1v = Z_to_bv 64 A -> a0v = Z_to_bv 64 r -> 0 <= r <= 1 ->
    0 <= L < 2 ^ 64 -> 0 <= R < 2 ^ 64 ->
    s9 = Z_to_bv 64 0 ->
    bytes_at rsegs m (A + 200) (le8 (Z_to_bv 64 L)) ->
    bytes_at rsegs m (A + 208) (le8 (Z_to_bv 64 R)) ->
    bytes_at rsegs m L ls -> length ls = 72%nat ->
    bytes_at rsegs m R rs -> length rs = 72%nat ->
    memcmp_model ls rs 72 = Some vcmp ->
    mem_inv rsegs m -> addressable m L 72 -> addressable m R 72 ->
    app_mem (L + 72) -> app_mem (L + 7) -> app_mem (R + 72) -> app_mem (R + 7) ->
    (L + 72 <= bv_unsigned sp - BCMP_WRAP_K \/ bv_unsigned sp <= L) ->
    (R + 72 <= bv_unsigned sp - BCMP_WRAP_K \/ bv_unsigned sp <= R) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + BCMP_WRAP_K <= bv_unsigned sp ->
    HIGHMEM_BEG <= lo -> bv_unsigned sp <= APPMEM_END ->
    asan_cells m -> shadow_rw m ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    evt rsegs
      (fun ms' => exists (ra' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 A) (Z_to_bv 64 vcmp)
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 (Z_to_bv 64 r) s8 s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x82378) fc None m' (seg_rom rsegs)
         /\ munch [(bv_unsigned sp - BCMP_WRAP_K, bv_unsigned sp)] m m'
         /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
         /\ asan_cells m' /\ shadow_rw m'
         /\ bytes_at rsegs m' L ls /\ bytes_at rsegs m' R rs)
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x8235c) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A r L R vcmp lo ls rs HB -> -> Hr HLb HRb -> H200 H240 HbL Lls HbR Lrs Hmm
    HMI HADL HADR HaL72 HaL7 HaR72 HaR7 HdjL HdjR HST Hlo1 Hlo2 Hspa HAC0 HSW0 HRB HRM HGC HC254 HC255.
  pose proof (f14_rd8 m (A + 200) (le8 (Z_to_bv 64 L)) H200 ltac:(apply length_le8)) as RD200.
  pose proof (f14_rd8 m (A + 208) (le8 (Z_to_bv 64 R)) H240 ltac:(apply length_le8)) as RD240.
  assert (Hbltz : bv_lts (Z_to_bv 64 r) (Z_to_bv 64 0) = false).
  { unfold bv_lts. rewrite (signed_lit r) by lia. rewrite (signed_lit 0) by lia. apply Z.ltb_ge. lia. }
  step.
  replace (bv_lts (Z_to_bv 64 r) (Z_to_bv 64 0)) with false by (symmetry; exact Hbltz). cbv iota.
  step. step.
  replace (negb (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0))) with false by reflexivity. cbv iota.
  step. step. step. step.
  assert (EL : bv_unsigned (Z_to_bv 64 L) = L) by (apply unsigned_lit; lia).
  assert (ER : bv_unsigned (Z_to_bv 64 R) = R) by (apply unsigned_lit; lia).
  assert (E72 : bv_unsigned (Z_to_bv 64 72) = 72) by reflexivity.
  pose proof HB as HBc. unfold bcmp_wrap_contract, BCMP_WRAP_K in HBc. cbv zeta in HBc.
  eapply evt_cut.
  { eapply HBc with (ls := ls) (rs := rs) (v := vcmp) (lo := lo).
    all: rewrite ?EL, ?ER, ?E72.
    - exact HbL.
    - exact HbR.
    - change (Z.to_nat 72) with 72%nat; exact Hmm.
    - exact HMI.
    - clear; lia.
    - exact HADL.
    - exact HADR.
    - right; exact HaL72.
    - right; exact HaR72.
    - right; exact HaL7.
    - right; exact HaR7.
    - exact HdjL.
    - exact HdjR.
    - exact HST.
    - exact Hlo1.
    - exact Hlo2.
    - exact Hspa.
    - exact HAC0.
    - exact HSW0.
    - exact HRB.
    - exact HRM.
    - exact HGC.
    - exact HC254.
    - exact HC255. }
  intros ms' Hp.
  unfold bcmp_wrap_post in Hp.
  destruct Hp as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
    E & MU & WM & MI' & ST' & AC' & SW' & HbL' & HbR').
  subst ms'.
  replace (ret_pc (Z_to_bv 64 533368)) with (Z_to_bv 64 533368)
    by (symmetry; apply ret_pc_even; [clear; lia | reflexivity]).
  apply evt_done.
  exists (Z_to_bv 64 533368), a1', a2', a3', a4', a5', a6', a7', t0', t1', t2', t3', t4', t5', t6', m'.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|].
  split; [exact AC'|]. split; [exact SW'|].
  rewrite EL, E72 in HbL'. rewrite ER, E72 in HbR'. change (Z.to_nat 72) with 72%nat in HbL', HbR'.
  rewrite firstn_all2 in HbL' by lia. rewrite firstn_all2 in HbR' by lia.
  split; [exact HbL' | exact HbR'].
Qed.

(* ---- The same run from a cut that carries ro_agree instead of mem_inv: the body runs on the normalized memory
   and MemNorm.evt_normalize carries it back (the normalized-memory transfer lemmas are F13's). ---- *)
Lemma f14_evt_0c :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A r L R vcmp lo : Z) (ls rs : list byte),
    bcmp_wrap_contract ->
    s1v = Z_to_bv 64 A -> a0v = Z_to_bv 64 r -> 0 <= r <= 1 ->
    0 <= L < 2 ^ 64 -> 0 <= R < 2 ^ 64 ->
    s9 = Z_to_bv 64 0 ->
    bytes_at rsegs m (A + 200) (le8 (Z_to_bv 64 L)) ->
    bytes_at rsegs m (A + 208) (le8 (Z_to_bv 64 R)) ->
    bytes_at rsegs m L ls -> length ls = 72%nat ->
    bytes_at rsegs m R rs -> length rs = 72%nat ->
    memcmp_model ls rs 72 = Some vcmp ->
    MN.ro_agree rsegs m -> addressable m L 72 -> addressable m R 72 ->
    app_mem (L + 72) -> app_mem (L + 7) -> app_mem (R + 72) -> app_mem (R + 7) ->
    (L + 72 <= bv_unsigned sp - BCMP_WRAP_K \/ bv_unsigned sp <= L) ->
    (R + 72 <= bv_unsigned sp - BCMP_WRAP_K \/ bv_unsigned sp <= R) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + BCMP_WRAP_K <= bv_unsigned sp ->
    HIGHMEM_BEG <= lo -> bv_unsigned sp <= APPMEM_END ->
    asan_cells m -> shadow_rw m ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    evt rsegs
      (fun ms' => exists (ra' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 A) (Z_to_bv 64 vcmp)
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 (Z_to_bv 64 r) s8 s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x82378) fc None m' (seg_rom rsegs)
         /\ munch [(bv_unsigned sp - BCMP_WRAP_K, bv_unsigned sp)] m m'
         /\ wmono rsegs m m' /\ MN.ro_agree rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
         /\ asan_cells m' /\ shadow_rw m'
         /\ bytes_at rsegs m' L ls /\ bytes_at rsegs m' R rs)
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x8235c) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A r L R vcmp lo ls rs HBc Es1 Ea0 Hr HLb HRb Es9 H200 H240 HbL Lls HbR Lrs Hmm
    HRO HADL HADR HaL72 HaL7 HaR72 HaR7 HdjL HdjR HST Hlo1 Hlo2 Hspa HAC0 HSW0 HRB HRM HGC HC254 HC255.
  pose proof (MN.mem_rel_normalize rsegs m HRO) as REL.
  eapply evt_mono.
  { eapply MN.evt_normalize; [vm_compute; reflexivity | exact HRO |].
    eapply f14_evt_0c_n with (A := A) (r := r) (L := L) (R := R) (vcmp := vcmp) (lo := lo) (ls := ls) (rs := rs).
    - exact HBc.
    - exact Es1.
    - exact Ea0.
    - exact Hr.
    - exact HLb.
    - exact HRb.
    - exact Es9.
    - apply MN.bytes_at_normalize; [exact HRO | exact H200].
    - apply MN.bytes_at_normalize; [exact HRO | exact H240].
    - apply MN.bytes_at_normalize; [exact HRO | exact HbL].
    - exact Lls.
    - apply MN.bytes_at_normalize; [exact HRO | exact HbR].
    - exact Lrs.
    - exact Hmm.
    - apply MN.mem_inv_normalize.
    - exact (addr_rel m _ L 72 REL HADL).
    - exact (addr_rel m _ R 72 REL HADR).
    - exact HaL72.
    - exact HaL7.
    - exact HaR72.
    - exact HaR7.
    - exact HdjL.
    - exact HdjR.
    - apply stk_norm; [exact HRO | exact HST | apply not_ro_hi; unfold AC.GT, HIGHMEM_BEG, APPMEM_END in *; lia].
    - exact Hlo1.
    - exact Hlo2.
    - exact Hspa.
    - exact (acells_rel m _ REL HAC0).
    - exact (shrw_rel m _ REL HSW0).
    - apply MN.bytes_at_normalize; [exact HRO | exact HRB].
    - apply MN.bytes_at_normalize; [exact HRO | exact HRM].
    - apply MN.bytes_at_normalize; [exact HRO | exact HGC].
    - apply MN.bytes_at_normalize; [exact HRO | exact HC254].
    - apply MN.bytes_at_normalize; [exact HRO | exact HC255]. }
  intros msx (msx0 & Pn & MR & RS).
  destruct Pn as (ra' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t0' & t1' & t2' & t3' & t4' & t5' & t6' & m0'
                 & E & MU & WM & MI' & ST' & AC' & SW' & HbL' & HbR').
  subst msx0.
  destruct msx as [regs1 fregs1 pcv1 svc1 resv1 fcsr1 mem1 rom1].
  destruct MR as (Hr1 & Hf1 & Hpc1 & Hsvc1 & Hres1 & Hfc1 & Hrom1 & Hmem).
  cbn in Hr1, Hf1, Hpc1, Hsvc1, Hres1, Hfc1, Hrom1, Hmem, RS.
  exists ra', a1', a2', a3', a4', a5', a6', a7', t0', t1', t2', t3', t4', t5', t6', mem1.
  split; [unfold MS; subst; reflexivity|].
  split; [exact (MN.munch_rel rsegs _ m _ mem1 m0' REL Hmem RS MU)|].
  split; [exact (MN.wmono_rel rsegs m _ mem1 m0' REL Hmem RS WM)|].
  split; [exact (MN.ro_agree_same rsegs m mem1 HRO RS)|].
  split; [exact (stk_back mem1 m0' _ _ Hmem ST')|].
  split; [exact (acells_back mem1 m0' Hmem AC')|].
  split; [exact (shrw_back mem1 m0' Hmem SW')|].
  split; [exact (ba_back mem1 m0' _ _ Hmem HbL') | exact (ba_back mem1 m0' _ _ Hmem HbR')].
Qed.

Section S.
Context {fx : YK11.FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

(* The callee contract (lib/B/Prog/bcmp_wrap_c.v), taken as a Section Hypothesis. *)
Hypothesis HBCMP : bcmp_wrap_contract.

Lemma seg_F14 : forall j : nat,
  Hat B APIf ra (Inv_B8237c_at B APIf ra) j -> Hat B APIf ra (Inv_B82378_at B APIf ra) j ->
  Hat B APIf ra (Inv_B8235c_at B APIf ra) j.
Proof.
  intros j H10 H0c g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hj & HHB & H18 & H20 & Hturn &
    (HLK & HFM & HFS) & Ha0 & Hlong & HbL & HaL & HbR & HaR & HFGM & HRECF & HFRBA & HFRX & HFS9).
  subst c. rewrite SEGS.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (fra_win B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs mem md HFRA) as (Hwlo & Hwstk).
  pose proof (fra_frame B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs mem md HFRA)
    as (Hplace & HfrA & Hfsmeta & Hfrwr).
  pose proof (fra_app B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs mem md HFRA) as (HGT & Happ).
  rewrite ?FRAME_SHADOW_val in *. unfold FRAME_BYTES in *.
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspillq & Hselq & Hfr56q & Hloc & Hhdr1 & Hhdr2 & Hshf & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (rt_cells sp mem md HRT) as (HAC0 & HSW0 & HB1 & HB2 & HB3 & HB4 & HB5).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (HwinB : 0 <= g_S g - AF.SLOT_STACK /\ g_S g <= 2 ^ 64)
    by (unfold stk in Hwin; split; [apply (proj1 Hwin) | apply (proj1 (proj2 Hwin))]).
  assert (HAb : 0 <= A < 2 ^ 64) by lia.
  assert (HA0 : 0 <= A) by lia.
  assert (HA1 : A + 448 <= 2 ^ 64) by (unfold APPMEM_END in *; lia).
  assert (Hhigh : HIGHMEM_BEG <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md)
    by (apply (AC.a_laws_stack_high _ _ _ _ _ LAWS (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md HAH)).
  assert (HbvA : bv_unsigned (getr regs 9) = A)
    by (unfold rg in Hr9; rewrite Hr9; apply MState.unsigned_lit; lia).
  rewrite HbvA in HfrA.
  assert (HspA : AC.aspZ regs <= A) by lia.
  assert (HaspE : AC.aspZ regs <= APPMEM_END) by lia.
  assert (HaspH : HIGHMEM_BEG <= AC.aspZ regs - BCMP_WRAP_K) by (unfold BCMP_WRAP_K in *; lia).
  assert (HwGT : 6283264 <= AC.aspZ regs - BCMP_WRAP_K) by (unfold HIGHMEM_BEG in HaspH; lia).
  assert (HKb : 0 <= BCMP_WRAP_K <= FN_STACK) by (unfold BCMP_WRAP_K; lia).
  pose proof (Hplace BCMP_WRAP_K HKb) as Hfrsep.
  (* the frame's pointers: in range and non-zero *)
  assert (Hfb : 0 <= fragb fr < 2 ^ 64).
  { assert (Ha : app_mem (fr + 2768)) by (apply Happ; lia).
    unfold fragb, app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG, AC.GT in *. lia. }
  assert (HLb : 0 <= fr + 336 < 2 ^ 64).
  { assert (Ha : app_mem (fr + 336)) by (apply Happ; lia).
    unfold app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG, AC.GT in *. lia. }
  assert (Hfnz : fragb fr <> 0) by (unfold fragb, AC.GT in *; lia).
  assert (Hphinz : phi <> 0) by (destruct HHB as (HH & _); exact HH).
  assert (Hrr : 0 <= fg_ret (frcl g j fr phi) <= 1).
  { unfold frcl. apply f14_ret_range; solve [exact Hfnz | exact Hphinz | unfold AC.GT in *; lia]. }
  (* the values the segment reads: FLI's [A+200] / [A+208] and FM's sum flag s9 *)
  pose proof HLK as HLK2. destruct HLK2 as (_ & _ & _ & HFLI).
  destruct HFLI as (F27 & F168 & F96 & F112 & F120 & F128 & F136 & F144 & F152 & F280 & F160 & F176 &
    F192 & F200 & F216 & F208 & F104 & F256 & F264 & F288 & F296 & F304 & F2624 & Ffrstk & _).
  pose proof HFM as HFM2. destruct HFM2 as (_ & _ & _ & H25s & _).
  pose proof (spill_at regs mem A 200 (fr + 336) F200 Hr9 HA0 HA1 ltac:(lia) ltac:(lia)) as H200.
  pose proof (spill_at regs mem A 208 (fragb fr) F208 Hr9 HA0 HA1 ltac:(lia) ltac:(lia)) as H240.
  (* FLV at the entry: the five pointer spills are FLI's; the two output cells when the turn opens a record *)
  assert (HFLV : FLV g fr j regs mem).
  { split; [exact F120|]. split; [exact F128|]. split; [exact F256|]. split; [exact F304|].
    split; [exact F296|].
    intros Hrf.
    rewrite (f14_trf_of_frcl g j fr phi) in Hrf
      by solve [exact Hfnz | exact Hphinz | unfold AC.GT in *; lia].
    pose proof HFGM as HFGM'. rewrite (f14_ret1_close _ Hrf) in HFGM'. cbn [fg_mem] in HFGM'.
    destruct HFGM' as (_ & _ & Hpp & Hpn). unfold q64. split; [exact Hpp|].
    unfold f_pll. exact Hpn. }
  assert (Hsd : t_sum_ok (g_in g) j = true \/ t_sum_ok (g_in g) j = false)
    by (destruct (t_sum_ok (g_in g) j); [left | right]; reflexivity).
  destruct Hsd as [Hsum | Hsum].
  - (* s9 = 1: the branch at 0x82364 is taken, landing at 0x8237c with memory unchanged *)
    rewrite Hsum in H25s. change (b2z true) with 1 in H25s.
    apply (sl_run_lib regs (Z_to_bv 64 0x8235c) mem md
      (fun R0 pc' mem' =>
         pc' = Z_to_bv 64 0x8237c /\ mem' = mem /\
         getr R0 2 = getr regs 2 /\ getr R0 3 = getr regs 3 /\ getr R0 4 = getr regs 4 /\
         getr R0 8 = getr regs 8 /\ getr R0 9 = getr regs 9 /\ getr R0 18 = getr regs 18 /\
         getr R0 19 = getr regs 19 /\ getr R0 20 = getr regs 20 /\ getr R0 21 = getr regs 21 /\
         getr R0 22 = getr regs 22 /\ getr R0 24 = getr regs 24 /\ getr R0 25 = getr regs 25 /\
         getr R0 26 = getr regs 26 /\
         getr R0 27 = getr regs 27 /\
         getr R0 23 = Z_to_bv 64 (fg_ret (frcl g j fr phi)))
      (Post B APIf ra g)).
    + exact Hhalt.
    + eapply evt_mono.
      { unfold Regs6ss.mkR_of.
        eapply f14_evt_10 with (r := fg_ret (frcl g j fr phi)) (v := 1).
        - unfold rg in Ha0; exact Ha0.
        - exact Hrr.
        - unfold rg in H25s; exact H25s.
        - lia.
        - lia. }
      { intros ms' E.
        eexists _, (Z_to_bv 64 0x8237c), mem. split; [exact E|].
        do 16 (split; [reflexivity|]).
        reflexivity. }
    + intros R0 pc' mem' regs' md' (Hpc & Hmem & Er2 & Er3 & Er4 & Er8 & Er9 & Er18 & Er19 & Er20 & Er21 &
        Er22 & Er24 & Er25 & Er26 & Er27 & Er23) Hreg Hmat.
      subst pc' mem'.
      assert (Fr2 : getr regs' 2 = getr regs 2) by (rewrite Hreg; exact Er2).
      assert (Fr3 : getr regs' 3 = getr regs 3) by (rewrite Hreg; exact Er3).
      assert (Fr4 : getr regs' 4 = getr regs 4) by (rewrite Hreg; exact Er4).
      assert (Fr8 : getr regs' 8 = getr regs 8) by (rewrite Hreg; exact Er8).
      assert (Fr9 : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact Er9).
      assert (Fr18 : getr regs' 18 = getr regs 18) by (rewrite Hreg; exact Er18).
      assert (Fr19 : getr regs' 19 = getr regs 19) by (rewrite Hreg; exact Er19).
      assert (Fr20 : getr regs' 20 = getr regs 20) by (rewrite Hreg; exact Er20).
      assert (Fr21 : getr regs' 21 = getr regs 21) by (rewrite Hreg; exact Er21).
      assert (Fr22 : getr regs' 22 = getr regs 22) by (rewrite Hreg; exact Er22).
      assert (Fr24 : getr regs' 24 = getr regs 24) by (rewrite Hreg; exact Er24).
      assert (Fr25 : getr regs' 25 = getr regs 25) by (rewrite Hreg; exact Er25).
      assert (Fr26 : getr regs' 26 = getr regs 26) by (rewrite Hreg; exact Er26).
      assert (Fr27 : getr regs' 27 = getr regs 27) by (rewrite Hreg; exact Er27).
      assert (Fr23 : getr regs' 23 = Z_to_bv 64 (fg_ret (frcl g j fr phi))) by (rewrite Hreg; exact Er23).
      assert (HFRA'' : FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs' mem md').
      { apply (Tac_slot.sl_fra_move B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs regs' mem md md' HFRA);
          [exact Fr2 | exact Fr3 | exact Fr4 | exact Fr8 | exact Fr9 | exact Fr19 | exact Fr26 | exact Hmat]. }
      assert (HENT'' : ENT APIf g (hb1 phi (AC.a_size (flen g j))) mem md')
        by (exact (Tac_slot.ent_mat APIf g (hb1 phi (AC.a_size (flen g j))) mem md md' HENT Hmat)).
      assert (MU0 : munch [] mem mem) by (apply munch_self).
      assert (Hnone : forall x, A <= x < A + 448 -> outside [] x) by (intros x Hx; exact I).
      assert (HIexit : Inv_B8237c_at B APIf ra g j
                         (mkCfg (mkst regs' (Z_to_bv 64 0x8237c) mem (seg_rom rsegs)) md')).
      { exists phi, regs', mem, md', fr. rewrite SEGS. split; [reflexivity|].
        split; [exact HFRA''|].
        split; [exact HENT''|].
        split; [exact Hgn|].
        split; [exact Hj|].
        split; [exact HHB|].
        split; [unfold rg in *; exact (eq_trans Fr18 H18)|].
        split; [unfold rg in *; exact (eq_trans Fr20 H20)|].
        split.
        { destruct Hturn as (T216 & T224 & Tphi & Tlen).
          split; [eapply spill_keep; [exact T216 | exact Hr9 | exact HA0 | exact HA1 | lia | lia | exact Fr9
                                     | exact MU0 | intros x Hx; exact I]|].
          split; [eapply spill_keep; [exact T224 | exact Hr9 | exact HA0 | exact HA1 | lia | lia | exact Fr9
                                     | exact MU0 | intros x Hx; exact I]|].
          split; [exact Tphi | exact Tlen]. }
        split.
        { eapply lk_keep; [exact HLK | exact Hr9 | exact HA0 | exact HA1 | exact Fr9 | exact Fr27 | exact MU0
                           | intros a Ha; exact Ha | cbn [all_app]; exact I | exact Hnone | | |].
          - intros x Hx. exact I.
          - intros x Hx. exact I.
          - intros x _ Ho. exfalso. apply Ho. exact I. }
        split.
        { eapply flv_keep; [exact HFLV | exact Hr9 | exact HA0 | exact HA1 | exact Fr9 | exact MU0 | exact Hnone | |].
          - intros x Hx. exact I.
          - intros x Hx. exact I. }
        split.
        { eapply fm_keep; [exact HFM | exact Hr9 | exact HA0 | exact HA1 | exact Fr9 | exact Fr22 | exact Fr24
                           | exact Fr25 | exact MU0 | exact Hnone]. }
        split.
        { eapply fsj_keep; [exact HFS | exact MU0 | cbn [all_app]; exact I | intros x Hx; exact I]. }
        split; [unfold rg; exact Fr23|].
        (* no memory changes on this arm: the record bundles move with the registers they name *)
        split; [exact HRECF|].
        split.
        { destruct HFRBA as (A0 & H9b & HA0b & HFRB). exists A0.
          split; [unfold rg in *; rewrite Fr9; exact H9b|]. split; [exact HA0b|].
          assert (Easp : AC.aspZ regs' = AC.aspZ regs) by (unfold AC.aspZ; rewrite Fr2; reflexivity).
          unfold FRB in *. rewrite Easp. exact HFRB. }
        split; [exact HFRX|].
        eapply fs9_keep; [exact HFS9 | exact Hr9 | exact HA0 | exact HA1 | exact Fr9 | exact MU0 | exact Hnone]. }
      pose proof (H10 g _ HIexit) as HSR. rewrite SEGS in HSR. exact HSR.
  - (* s9 = 0: the bcmp call, landing at 0x82378 *)
    rewrite Hsum in H25s. change (b2z false) with 0 in H25s.
    destruct (SF.memcmp_model_total (t_FG (g_in g) j) (frrec g j fr phi) 72
                ltac:(rewrite t_FG_length; lia) ltac:(rewrite frrec_length; lia)) as (vcmp & Hmm).
    apply (sl_run_lib regs (Z_to_bv 64 0x8235c) mem md
      (fun R0 pc' mem' =>
         pc' = Z_to_bv 64 0x82378 /\
         getr R0 2 = getr regs 2 /\ getr R0 3 = getr regs 3 /\ getr R0 4 = getr regs 4 /\
         getr R0 8 = getr regs 8 /\ getr R0 9 = getr regs 9 /\ getr R0 18 = getr regs 18 /\
         getr R0 19 = getr regs 19 /\ getr R0 20 = getr regs 20 /\ getr R0 21 = getr regs 21 /\
         getr R0 22 = getr regs 22 /\ getr R0 24 = getr regs 24 /\ getr R0 25 = getr regs 25 /\
         getr R0 26 = getr regs 26 /\
         getr R0 27 = getr regs 27 /\
         getr R0 10 = Z_to_bv 64 vcmp /\ getr R0 23 = Z_to_bv 64 (fg_ret (frcl g j fr phi)) /\
         munch [(AC.aspZ regs - BCMP_WRAP_K, AC.aspZ regs)] mem mem' /\
         wmono rsegs mem mem' /\ MN.ro_agree rsegs mem' /\
         stk rsegs mem' (AC.aspZ regs - FN_STACK) (AC.aspZ regs))
      (Post B APIf ra g)).
    + exact Hhalt.
    + eapply evt_mono.
      { unfold Regs6ss.mkR_of.
        eapply f14_evt_0c with (A := A) (r := fg_ret (frcl g j fr phi)) (L := fr + 336) (R := fragb fr)
          (vcmp := vcmp) (lo := AC.aspZ regs - FN_STACK)
          (ls := t_FG (g_in g) j) (rs := frrec g j fr phi).
        - exact HBCMP.
        - unfold rg in Hr9; exact Hr9.
        - unfold rg in Ha0; exact Ha0.
        - exact Hrr.
        - exact HLb.
        - exact Hfb.
        - unfold rg in H25s; exact H25s.
        - unfold q64 in H200; exact H200.
        - unfold q64 in H240; exact H240.
        - exact HbL.
        - apply t_FG_length.
        - exact HbR.
        - apply frrec_length.
        - exact Hmm.
        - exact Hro.
        - exact HaL.
        - exact HaR.
        - apply Happ; lia.
        - apply Happ; lia.
        - apply Happ; unfold fragb in *; lia.
        - apply Happ; unfold fragb in *; lia.
        - fold_sp regs. unfold BCMP_WRAP_K in *. lia.
        - fold_sp regs. unfold fragb, BCMP_WRAP_K in *. lia.
        - fold_sp regs. exact Hwstk.
        - fold_sp regs. unfold BCMP_WRAP_K in *. lia.
        - unfold BCMP_WRAP_K in *. lia.
        - fold_sp regs. exact HaspE.
        - exact HAC0.
        - exact HSW0.
        - exact HB1.
        - exact HB2.
        - exact HB3.
        - exact HB4.
        - exact HB5. }
      { intros ms' (ra' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t0' & t1' & t2' & t3' & t4' & t5' & t6' & m'
                    & E & MU & WM & HRO' & ST' & AC' & SW' & _ & _).
        eexists _, (Z_to_bv 64 0x82378), m'. split; [exact E|].
        split; [reflexivity|].
        split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        split; [reflexivity|]. split; [unfold rg in Hr9; exact (eq_sym Hr9)|].
        do 9 (split; [reflexivity|]).
        split; [reflexivity|]. split; [reflexivity|].
        match type of ST' with context [bv_unsigned ?s] => change (bv_unsigned s) with (AC.aspZ regs) in MU, ST' end.
        split; [exact MU|]. split; [exact WM|]. split; [exact HRO' | exact ST']. }
    + intros R0 pc' mem' regs' md' (Hpc & Er2 & Er3 & Er4 & Er8 & Er9 & Er18 & Er19 & Er20 & Er21 & Er22 &
        Er24 & Er25 & Er26 & Er27 & Er10 & Er23 & MU & WM & HROM & ST') Hreg Hmat.
      subst pc'.
      assert (Fr2 : getr regs' 2 = getr regs 2) by (rewrite Hreg; exact Er2).
      assert (Fr3 : getr regs' 3 = getr regs 3) by (rewrite Hreg; exact Er3).
      assert (Fr4 : getr regs' 4 = getr regs 4) by (rewrite Hreg; exact Er4).
      assert (Fr8 : getr regs' 8 = getr regs 8) by (rewrite Hreg; exact Er8).
      assert (Fr9 : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact Er9).
      assert (Fr18 : getr regs' 18 = getr regs 18) by (rewrite Hreg; exact Er18).
      assert (Fr19 : getr regs' 19 = getr regs 19) by (rewrite Hreg; exact Er19).
      assert (Fr20 : getr regs' 20 = getr regs 20) by (rewrite Hreg; exact Er20).
      assert (Fr21 : getr regs' 21 = getr regs 21) by (rewrite Hreg; exact Er21).
      assert (Fr22 : getr regs' 22 = getr regs 22) by (rewrite Hreg; exact Er22).
      assert (Fr24 : getr regs' 24 = getr regs 24) by (rewrite Hreg; exact Er24).
      assert (Fr25 : getr regs' 25 = getr regs 25) by (rewrite Hreg; exact Er25).
      assert (Fr26 : getr regs' 26 = getr regs 26) by (rewrite Hreg; exact Er26).
      assert (Fr27 : getr regs' 27 = getr regs 27) by (rewrite Hreg; exact Er27).
      assert (Fr10 : getr regs' 10 = Z_to_bv 64 vcmp) by (rewrite Hreg; exact Er10).
      assert (Fr23 : getr regs' 23 = Z_to_bv 64 (fg_ret (frcl g j fr phi))) by (rewrite Hreg; exact Er23).
      (* the wrapper's write set, and the data that lies outside it *)
      assert (Hallapp : all_app [(AC.aspZ regs - BCMP_WRAP_K, AC.aspZ regs)]).
      { cbn [all_app]. split; [|exact I]. intros a Ha. unfold app_mem. right. lia. }
      assert (Hrtdj : rt_disjoint [(AC.aspZ regs - BCMP_WRAP_K, AC.aspZ regs)]).
      { unfold rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
          RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG,
          RT_AGLOB, RT_AGLOB_LEN.
        cbn [disjoint_from]. repeat split; first [left; lia | exact I]. }
      assert (Hout : forall x, (x < AC.aspZ regs - BCMP_WRAP_K \/ AC.aspZ regs <= x) ->
                outside [(AC.aspZ regs - BCMP_WRAP_K, AC.aspZ regs)] x)
        by (intros x Hx; apply out1; exact Hx).
      assert (HoutA : forall x, A <= x -> outside [(AC.aspZ regs - BCMP_WRAP_K, AC.aspZ regs)] x)
        by (intros x Hx; apply Hout; right; lia).
      assert (HoutA' : forall x, A <= x < A + 448 -> outside [(AC.aspZ regs - BCMP_WRAP_K, AC.aspZ regs)] x)
        by (intros x Hx; apply HoutA; lia).
      assert (Hfrout : forall x, fr <= x < fr + 3136 ->
                outside [(AC.aspZ regs - BCMP_WRAP_K, AC.aspZ regs)] x).
      { intros x Hx. apply Hout. destruct Hfrsep as [Hd|Hd]; [left; lia | right; lia]. }
      assert (Hmeta : meta_kept mem mem') by (apply (munch_meta _ mem mem' MU Hallapp)).
      (* the record block [phi, phi + a_size len) lies below stklo (the heap list's block law), so far below the
         wrapper's scratch *)
      destruct (f13_blk APIf (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md phi (AC.a_size (flen g j)) HAH
                  ltac:(apply in_or_app; left; unfold hb1; cbn [In]; left; reflexivity))
        as (Hblkend & _).
      assert (HOphi : forall x, phi <= x < phi + AC.a_size (flen g j) + 50 ->
                outside [(AC.aspZ regs - BCMP_WRAP_K, AC.aspZ regs)] x).
      { intros x Hx. apply Hout. left. unfold BCMP_WRAP_K in *. lia. }
      (* AH, ownership and the stack bounds across the wrapper's store *)
      assert (HstoreC : forall a, 0 <= a < 2 ^ 64 ->
        ~ AC.a_store_ok (hb1 phi (AC.a_size (flen g j)) ++ g_H g)
            (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
        mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
      { intros a Ha Hns. apply MU. rewrite MState.unsigned_lit by lia.
        cbn [Frame.outside]. split; [|exact I]. intros [HH1 HH2]. apply Hns.
        unfold AC.a_store_ok. right; left. rewrite Haspz in *.
        unfold BCMP_WRAP_K, AF.SLOT_STACK in *. split; lia. }
      assert (Hwmon : forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a)
        by (intros a Ha Hw; exact (WM (Z_to_bv 64 a) Hw)).
      destruct (f13_store APIf (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem mem' md
                  HAH HstoreC Hwmon) as (HAH' & Hown' & HSTKeq & HSTKH').
      (* the entry-anchored slot window on mem': outside the wrapper's scratch from mem, inside it from the call's
         stack post on [sp - FN_STACK, sp) *)
      assert (HSTKS : stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g)).
      { destruct (stk_split rsegs mem (g_S g - AF.SLOT_STACK) (AC.aspZ regs - BCMP_WRAP_K) (g_S g) Hwin
                    ltac:(rewrite Haspz; unfold BCMP_WRAP_K, AF.SLOT_STACK in *; lia)) as (Hw1 & Hw2).
        destruct (stk_split rsegs mem (AC.aspZ regs - BCMP_WRAP_K) (AC.aspZ regs) (g_S g) Hw2
                    ltac:(rewrite Haspz; unfold BCMP_WRAP_K; lia)) as (_ & Hw3).
        destruct (stk_split rsegs mem' (AC.aspZ regs - FN_STACK) (AC.aspZ regs - BCMP_WRAP_K) (AC.aspZ regs) ST'
                    ltac:(unfold BCMP_WRAP_K, FN_STACK, AF.SLOT_STACK; lia)) as (_ & HwW).
        assert (Hw1' : stk rsegs mem' (g_S g - AF.SLOT_STACK) (AC.aspZ regs - BCMP_WRAP_K)).
        { eapply (stk_transport rsegs _ mem mem'); [exact Hw1 | exact MU | exact WM |].
          intros x Hx. left. apply out1. lia. }
        assert (Hw3' : stk rsegs mem' (AC.aspZ regs) (g_S g)).
        { eapply (stk_transport rsegs _ mem mem'); [exact Hw3 | exact MU | exact WM |].
          intros x Hx. left. apply out1. lia. }
        apply (stk_merge rsegs mem' _ (AC.aspZ regs) _);
          [| exact Hw3' | rewrite Haspz; unfold BCMP_WRAP_K, AF.SLOT_STACK in *; lia].
        apply (stk_merge rsegs mem' _ (AC.aspZ regs - BCMP_WRAP_K) _); [exact Hw1' | exact HwW |].
        rewrite Haspz; unfold BCMP_WRAP_K, AF.SLOT_STACK in *; lia. }
      (* FRA across the call (F13.fra_mem_call on the wrapper's write set), then to regs' / md' *)
      assert (HFRA1 : FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs mem' md).
      { apply (fra_mem_call B APIf ra empty FF g fr (hb1 phi (AC.a_size (flen g j))) regs mem mem' md
                 [(AC.aspZ regs - BCMP_WRAP_K, AC.aspZ regs)] HFRA MU WM Hallapp Hrtdj HROM HAH' HSTKeq HSTKS).
        - intros x Hx. apply Hfrout. lia.
        - intros A' HA'b HA' x Hx. apply HoutA.
          assert (EA' : A' = A) by (exact (rg9_eq regs A A' Hr9 HA' HAb HA'b)).
          lia.
        - intros x Hx. apply Hout. right. lia.
        - intros x Hx. apply Hout. left.
          assert (Hin : in_shadow x).
          { assert (Hdiv : (fr + 8 * (x - Sfr fr)) / 8 = fr / 8 + (x - Sfr fr)).
            { replace (8 * (x - Sfr fr)) with ((x - Sfr fr) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
            assert (Hinfr : fr <= fr + 8 * (x - Sfr fr) < fr + 3136) by lia.
            pose proof (shadow_of_app (fr + 8 * (x - Sfr fr)) (Happ _ Hinfr)) as His.
            replace (shadow_addr (fr + 8 * (x - Sfr fr))) with x in His; [exact His|].
            unfold shadow_addr. rewrite Hdiv. unfold Sfr, shadow_addr. lia. }
          unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hin, HaspH. lia.
        - intros x Hx. apply Hout. left. unfold AC.GT in Hx. lia.
        - intros x Hxlo _. apply Hout. left. unfold BCMP_WRAP_K in *. lia. }
      assert (HFRA'' : FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs' mem' md').
      { apply (Tac_slot.sl_fra_move B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs regs' mem' md md' HFRA1);
          [exact Fr2 | exact Fr3 | exact Fr4 | exact Fr8 | exact Fr9 | exact Fr19 | exact Fr26 | exact Hmat]. }
      (* ENT: the wrapper wrote only its scratch inside the slot window *)
      assert (HWcases : forall x, 0 <= x < 2 ^ 64 ->
                outside [(AC.aspZ regs - BCMP_WRAP_K, AC.aspZ regs)] x \/
                (g_S g - AF.SLOT_STACK <= x < g_S g) \/ (fr <= x < fr + 3136) \/
                (Sfr fr <= x < Sfr fr + 392)).
      { intros x Hx.
        destruct (Z_lt_le_dec x (AC.aspZ regs - BCMP_WRAP_K)) as [H1|H1]; [left; apply Hout; left; exact H1|].
        destruct (Z_lt_le_dec x (AC.aspZ regs)) as [H2|H2]; [|left; apply Hout; right; exact H2].
        right; left. unfold BCMP_WRAP_K in *. lia. }
      assert (HENT' : ENT APIf g (hb1 phi (AC.a_size (flen g j))) mem' md).
      { apply (Tac_slot.ent_store B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs mem mem' md
                 [(AC.aspZ regs - BCMP_WRAP_K, AC.aspZ regs)] HENT HFRA MU HWcases HSTKeq HSTKH').
        intros a Hia Ho. exact (proj2 (Hown' a) Ho). }
      assert (HENT'' : ENT APIf g (hb1 phi (AC.a_size (flen g j))) mem' md')
        by (exact (Tac_slot.ent_mat APIf g (hb1 phi (AC.a_size (flen g j))) mem' md md' HENT' Hmat)).
      assert (HIexit : Inv_B82378_at B APIf ra g j
                         (mkCfg (mkst regs' (Z_to_bv 64 0x82378) mem' (seg_rom rsegs)) md')).
      { exists phi, regs', mem', md', fr. rewrite SEGS. split; [reflexivity|].
        split; [exact HFRA''|].
        split; [exact HENT''|].
        split; [exact Hgn|].
        split; [exact Hj|].
        split.
        { destruct HHB as (Hphinz2 & Hphiad). split; [exact Hphinz2|].
          eapply addressable_kept; [exact Hphiad | exact Hmeta]. }
        split; [unfold rg in *; exact (eq_trans Fr18 H18)|].
        split; [unfold rg in *; exact (eq_trans Fr20 H20)|].
        split.
        { destruct Hturn as (T216 & T224 & Tphi & Tlen).
          split.
          { eapply spill_keep; [exact T216 | exact Hr9 | exact HA0 | exact HA1 | lia | lia | exact Fr9 | exact MU |].
            intros x Hx. apply HoutA. lia. }
          split.
          { eapply spill_keep; [exact T224 | exact Hr9 | exact HA0 | exact HA1 | lia | lia | exact Fr9 | exact MU |].
            intros x Hx. apply HoutA. lia. }
          split; [|exact Tlen].
          eapply fl_bytes; [exact Tphi | exact MU |]. intros x Hx. apply HOphi. unfold flen, AC.a_size in *. lia. }
        split.
        { eapply lk_keep; [exact HLK | exact Hr9 | exact HA0 | exact HA1 | exact Fr9 | exact Fr27 | exact MU
                           | exact WM | exact Hallapp | exact HoutA' | | |].
          - intros x Hx. apply Hfrout. lia.
          - intros x Hx. apply Hout. left. unfold AC.GT, HIGHMEM_BEG, BCMP_WRAP_K in *. lia.
          - intros x Hx Ho. exfalso. apply Ho. apply Hfrout. exact Hx. }
        split.
        { eapply flv_keep; [exact HFLV | exact Hr9 | exact HA0 | exact HA1 | exact Fr9 | exact MU | exact HoutA' | |].
          - intros x Hx. apply Hfrout. lia.
          - intros x Hx. apply Hfrout. lia. }
        split.
        { eapply fm_keep; [exact HFM | exact Hr9 | exact HA0 | exact HA1 | exact Fr9 | exact Fr22 | exact Fr24
                           | exact Fr25 | exact MU | exact HoutA']. }
        split.
        { eapply fsj_keep; [exact HFS | exact MU | exact Hallapp |]. intros x Hx. apply Hfrout. lia. }
        split; [unfold rg; exact Fr23|].
        split; [exact Hsum|].
        split; [exists vcmp; split; [exact Hmm | unfold rg; exact Fr10]|].
        (* the record bundles: the wrapper's scratch misses the frame, Phi's block and the save area *)
        split; [exact (f14_recf_keep g fr j mem mem' _ HRECF MU Hfrout)|].
        split.
        { destruct HFRBA as (A0 & H9b & HA0b & HFRB). exists A0.
          split; [unfold rg in *; rewrite Fr9; exact H9b|]. split; [exact HA0b|].
          assert (EA0 : A0 = A) by (exact (rg9_eq regs A A0 Hr9 H9b HAb HA0b)). subst A0.
          apply (f14_frb_keep g j fr phi A (fr + 176) regs regs' mem mem' _ HFRB MU Hmeta
                   ltac:(unfold AC.aspZ; rewrite Fr2; reflexivity)).
          - exact HoutA'.
          - intros x Hx. apply HOphi. unfold AC.a_size in *. lia.
          - intros x Hx. apply (Hout x). left. unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG,
              HIGHMEM_BEG, BCMP_WRAP_K in *. lia.
          - intros x Hx. apply Hfrout. lia.
          - intros L x HL Hx. apply Hout. destruct HL as [Hd|Hd]; [left | right]; unfold BW.BCMP_WRAP_K,
              BCMP_WRAP_K in *; lia. }
        split.
        { apply (f14_frx_keep g j fr phi mem mem' _ HFRX MU Hmeta WM).
          - intros x Hx. apply HOphi. unfold AC.a_size in *. lia.
          - exact Hfrout. }
        eapply fs9_keep; [exact HFS9 | exact Hr9 | exact HA0 | exact HA1 | exact Fr9 | exact MU | exact HoutA']. }
      pose proof (H0c g _ HIexit) as HSR. rewrite SEGS in HSR. exact HSR.
Qed.

End S.
