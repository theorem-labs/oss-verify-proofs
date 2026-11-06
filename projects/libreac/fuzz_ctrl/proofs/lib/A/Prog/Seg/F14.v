(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3060 of its 3101 lines of code are new or changed and 207 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/reac_box_catalogue_match.v, with its module paths, module names, addresses and numbers changed; 2488 of its 3291 lines of code are new or changed and 2298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/reac_box_catalogue_match.v, with its module paths and module names changed; 2419 of its 2557 lines of code are new or changed and 3153 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/Tac_slot.v, with its module paths and module names changed; 789 of its 844 lines of code are new or changed and 2502 lines of the source are left out. *)
(* Segment F14 (plan-asan 2 / section 2 row F14 = 0x82154-0x82170, call BCMP@0x82170), in the slot framework
   (CUTST / FRA / LK / FLV), against the push-5 cut set.  From the shared entry cut Inv_A82154_at (SlotInv):
     0x82154  bltz a0,82b34     -- NOT taken: a0 = fg_ret of the fragment class, 0 or 1 here (the five pointers
                                   are non-zero, so the class is not FgRefuse).
     0x82158  mv   s9,a0
     0x8215c  ld   a0,280(s1)   -- a0 := [A+280].
     0x82160  bnez a0,820e0     -- [A+280] <> 0: land at the exit cut 0x82178.
     0x82164  li   a2,72
     0x82168  ld   a0,184(s1)   -- a0 := [A+184] = fr + 336, the before-call copy of the record.
     0x8216c  ld   a1,192(s1)   -- a1 := [A+192] = fragb fr, the record itself.
     0x82170  jal  wrapper_bcmp -- compares the two 72-byte records; returns to the exit cut 0x82174.
   Both exit cuts carry the shared conjuncts (g_n, j, HB, LK, FLV) and the data seg_F15 reads.  FLV's conditional
   part is derived here: when the turn opens a record (t_rf j = 1) the class is FgClose, and the fragment's post
   (fg_mem, carried by the entry cut) gives [fr + 272] = fragb fr + 19 and [fr + 304] = f_pll.  The bcmp wrapper
   is the Section Hypothesis HBCMP; it writes only its own stack window [sp - BCMP_WRAP_K, sp), which FRA's
   placement (fra_frame) keeps clear of the frame, so FRA is rebuilt by Tac_slot.sl_fr_cl. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Fpu Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI RoAdapt.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcRec RcFrag RcFragLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv memcmp_c bcmp_wrap_c
  reac_ctrl_identity_fragment_c RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import F13.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Tac_slot.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.

(* fg_ret is 0 or 1 unless the call refuses (one of the five pointers is 0). *)
Lemma fg_ret_range : forall f fr pa pp pn len st g, f <> 0 -> fr <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 ->
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

Lemma ret1_close : forall c, fg_ret c = 1 -> c = FgClose.
Proof. intros c H. destruct c; cbn [fg_ret] in H; try discriminate; reflexivity. Qed.

Lemma trf_of_frcl : forall g j fr phi, fragb fr <> 0 -> phi <> 0 ->
  fr + 256 <> 0 -> fr + 272 <> 0 -> fr + 304 <> 0 ->
  t_rf (g_in g) j = fg_ret (frcl g j fr phi).
Proof.
  intros g j fr phi H1 H2 H3 H4 H5. unfold t_rf, fg_rf.
  rewrite (frcl_fcls g j fr phi) by assumption. unfold flen. reflexivity.
Qed.

(* A carried bytes_at of 8 bytes in the form the load tactic consumes. *)
Lemma rd8 : forall m a bs, bytes_at rsegs m a bs -> length bs = 8%nat ->
  ov_read_bytes rsegs m (wa a) 8 = Some bs.
Proof.
  intros m a bs H Hl.
  pose proof (bytes_at_ov_read rsegs m a bs 0 8 H ltac:(lia)) as HH.
  change (Z.of_nat 0) with 0%Z in HH. rewrite Z.add_0_r, skipn_O, firstn_all2 in HH by lia. exact HH.
Qed.

(* ---- the [A+280] <> 0 arm: four instructions, no memory change, landing at 0x82178. ---- *)
Lemma f14_evt_e0 :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A r v280 : Z),
    s1v = Z_to_bv 64 A -> a0v = Z_to_bv 64 r -> 0 <= r <= 1 ->
    0 <= v280 < 2 ^ 64 -> v280 <> 0 ->
    bytes_at rsegs m (A + 280) (le8 (Z_to_bv 64 v280)) ->
    evt rsegs
      (fun ms' => ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 v280)
                                a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 r) s10 s11 t3 t4 t5 t6)
                             Fr (Z_to_bv 64 0x82178) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82154) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A r v280 -> -> Hr Hv280b Hv280nz H280.
  pose proof (rd8 m (A + 280) (le8 (Z_to_bv 64 v280)) H280 ltac:(apply length_le8)) as RD280.
  assert (Hbltz : bv_lts (Z_to_bv 64 r) (Z_to_bv 64 0) = false).
  { unfold bv_lts. rewrite (signed_lit r) by lia. rewrite (signed_lit 0) by lia. apply Z.ltb_ge. lia. }
  step.
  replace (bv_lts (Z_to_bv 64 r) (Z_to_bv 64 0)) with false by (symmetry; exact Hbltz). cbv iota.
  step. step. step.
  assert (EV : bv_unsigned (Z_to_bv 64 v280) = v280) by (apply unsigned_lit; lia).
  replace (negb (bv_eqb (Z_to_bv 64 v280) (Z_to_bv 64 0))) with true
    by (symmetry; apply Bool.negb_true_iff; unfold bv_eqb; rewrite EV;
        change (bv_unsigned (Z_to_bv 64 0)) with 0; apply Z.eqb_neq; exact Hv280nz).
  cbv iota.
  apply evt_done. reflexivity.
Qed.

(* ---- the [A+280] = 0 arm: the two record loads and the bcmp call, landing at 0x82174. ---- *)
Lemma f14_evt_dc :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A r L R vcmp lo : Z) (ls rs : list byte),
    bcmp_wrap_contract ->
    s1v = Z_to_bv 64 A -> a0v = Z_to_bv 64 r -> 0 <= r <= 1 ->
    0 <= L < 2 ^ 64 -> 0 <= R < 2 ^ 64 ->
    bytes_at rsegs m (A + 280) (le8 (Z_to_bv 64 0)) ->
    bytes_at rsegs m (A + 184) (le8 (Z_to_bv 64 L)) ->
    bytes_at rsegs m (A + 192) (le8 (Z_to_bv 64 R)) ->
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
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 r) s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x82174) fc None m' (seg_rom rsegs)
         /\ munch [(bv_unsigned sp - BCMP_WRAP_K, bv_unsigned sp)] m m'
         /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
         /\ asan_cells m' /\ shadow_rw m'
         /\ bytes_at rsegs m' L ls /\ bytes_at rsegs m' R rs)
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82154) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A r L R vcmp lo ls rs HB -> -> Hr HLb HRb H280 H184 H208 HbL Lls HbR Lrs Hmm
    HMI HADL HADR HaL72 HaL7 HaR72 HaR7 HdjL HdjR HST Hlo1 Hlo2 Hspa HAC0 HSW0 HRB HRM HGC HC254 HC255.
  pose proof (rd8 m (A + 280) (le8 (Z_to_bv 64 0)) H280 ltac:(apply length_le8)) as RD280.
  pose proof (rd8 m (A + 184) (le8 (Z_to_bv 64 L)) H184 ltac:(apply length_le8)) as RD184.
  pose proof (rd8 m (A + 192) (le8 (Z_to_bv 64 R)) H208 ltac:(apply length_le8)) as RD208.
  assert (Hbltz : bv_lts (Z_to_bv 64 r) (Z_to_bv 64 0) = false).
  { unfold bv_lts. rewrite (signed_lit r) by lia. rewrite (signed_lit 0) by lia. apply Z.ltb_ge. lia. }
  step.
  replace (bv_lts (Z_to_bv 64 r) (Z_to_bv 64 0)) with false by (symmetry; exact Hbltz). cbv iota.
  step. step. step.
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
  replace (ret_pc (Z_to_bv 64 532852)) with (Z_to_bv 64 532852)
    by (symmetry; apply ret_pc_even; [clear; lia | reflexivity]).
  apply evt_done.
  exists (Z_to_bv 64 532852), a1', a2', a3', a4', a5', a6', a7', t0', t1', t2', t3', t4', t5', t6', m'.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|].
  split; [exact AC'|]. split; [exact SW'|].
  rewrite EL, E72 in HbL'. rewrite ER, E72 in HbR'. change (Z.to_nat 72) with 72%nat in HbL', HbR'.
  rewrite firstn_all2 in HbL' by lia. rewrite firstn_all2 in HbR' by lia.
  split; [exact HbL' | exact HbR'].
Qed.

(* The same run on the memory the cut carries (ro_agree, not mem_inv, push 5b): every premise crosses
   MemNorm.mem_rel to the normalized memory, and the post comes back across mem_rel / ro_same.  The wrapper's
   window lies above HIGHMEM_BEG, so none of its bytes is read-only. *)
Lemma f14_evt_dc_ro :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A r L R vcmp lo : Z) (ls rs : list byte),
    bcmp_wrap_contract ->
    s1v = Z_to_bv 64 A -> a0v = Z_to_bv 64 r -> 0 <= r <= 1 ->
    0 <= L < 2 ^ 64 -> 0 <= R < 2 ^ 64 ->
    bytes_at rsegs m (A + 280) (le8 (Z_to_bv 64 0)) ->
    bytes_at rsegs m (A + 184) (le8 (Z_to_bv 64 L)) ->
    bytes_at rsegs m (A + 192) (le8 (Z_to_bv 64 R)) ->
    bytes_at rsegs m L ls -> length ls = 72%nat ->
    bytes_at rsegs m R rs -> length rs = 72%nat ->
    memcmp_model ls rs 72 = Some vcmp ->
    ro_agree rsegs m -> addressable m L 72 -> addressable m R 72 ->
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
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 r) s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x82174) fc None m' (seg_rom rsegs)
         /\ munch [(bv_unsigned sp - BCMP_WRAP_K, bv_unsigned sp)] m m'
         /\ wmono rsegs m m' /\ ro_agree rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
         /\ asan_cells m' /\ shadow_rw m'
         /\ bytes_at rsegs m' L ls /\ bytes_at rsegs m' R rs)
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82154) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A r L R vcmp lo ls rs HB E1 E10 Hr HLb HRb H280 H184 H208 HbL Lls HbR Lrs Hmm
    HRO HADL HADR HaL72 HaL7 HaR72 HaR7 HdjL HdjR HST Hlo1 Hlo2 Hspa HAC0 HSW0 HRB HRM HGC HC254 HC255.
  pose proof (mem_rel_normalize rsegs m HRO) as REL.
  assert (Hrostk : forall x, lo <= x < bv_unsigned sp -> ro_addr rsegs (wa x) = false).
  { intros x Hx. apply RoAdapt.ro_addr_false_hi. unfold HIGHMEM_BEG, APPMEM_END in *. lia. }
  pose proof (f14_evt_dc ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    t3 t4 t5 t6 Fr fc (normalize rsegs m) A r L R vcmp lo ls rs HB E1 E10 Hr HLb HRb
    (proj1 (bytes_at_rel rsegs m _ _ _ REL) H280) (proj1 (bytes_at_rel rsegs m _ _ _ REL) H184)
    (proj1 (bytes_at_rel rsegs m _ _ _ REL) H208)
    (proj1 (bytes_at_rel rsegs m _ _ _ REL) HbL) Lls (proj1 (bytes_at_rel rsegs m _ _ _ REL) HbR) Lrs Hmm
    (mem_inv_normalize rsegs m) (RoAdapt.rel_addr_norm m _ _ _ REL HADL) (RoAdapt.rel_addr_norm m _ _ _ REL HADR)
    HaL72 HaL7 HaR72 HaR7 HdjL HdjR (RoAdapt.rel_stk_norm m _ _ _ REL Hrostk HST) Hlo1 Hlo2 Hspa
    (RoAdapt.rel_ac_norm m _ REL HAC0) (RoAdapt.rel_sw_norm m _ REL HSW0)
    (proj1 (bytes_at_rel rsegs m _ _ _ REL) HRB) (proj1 (bytes_at_rel rsegs m _ _ _ REL) HRM)
    (proj1 (bytes_at_rel rsegs m _ _ _ REL) HGC) (proj1 (bytes_at_rel rsegs m _ _ _ REL) HC254)
    (proj1 (bytes_at_rel rsegs m _ _ _ REL) HC255)) as HC.
  pose proof (evt_normalize rsegs _ _ _ _ _ _ m (seg_rom rsegs) ltac:(vm_compute; reflexivity) HRO HC) as HN.
  eapply evt_mono; [exact HN|].
  intros ms (s0' & (ra' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t0' & t1' & t2' & t3' & t4' & t5' & t6' & m0'
              & E & MU & WM & MI' & ST' & AC' & SW' & HbL' & HbR') & Hrel & Hros).
  subst s0'.
  destruct ms as [regsX frX pcX svcX rvX fcX memX romX].
  destruct Hrel as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hrom & Hmr).
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom MS]
    in HR, HF, Hpc, Hsvc, Hres, Hfc, Hrom, Hmr, Hros.
  subst regsX frX pcX svcX rvX fcX romX.
  exists ra', a1', a2', a3', a4', a5', a6', a7', t0', t1', t2', t3', t4', t5', t6', memX.
  split; [reflexivity|].
  split; [exact (munch_rel rsegs _ m (normalize rsegs m) memX m0' REL Hmr Hros MU)|].
  split; [exact (wmono_rel rsegs m (normalize rsegs m) memX m0' REL Hmr Hros WM)|].
  split; [exact (ro_agree_of_mem_rel rsegs memX m0' Hmr)|].
  split; [exact (RoAdapt.rel_stk_back memX m0' _ _ Hmr ST')|].
  split; [exact (RoAdapt.rel_ac_back memX m0' Hmr AC')|].
  split; [exact (RoAdapt.rel_sw_back memX m0' Hmr SW')|].
  split; [exact (proj2 (bytes_at_rel rsegs memX m0' _ _ Hmr) HbL')
        | exact (proj2 (bytes_at_rel rsegs memX m0' _ _ Hmr) HbR')].
Qed.

(* FLSI names memory and register 9 only (its spills are read through s1), so it moves with s1. *)
Lemma flsi_regs : forall g j fr regs regs' m,
  FLSI g j fr regs m -> getr regs' 9 = getr regs 9 -> FLSI g j fr regs' m.
Proof.
  intros g j fr regs regs' m H E9. unfold FLSI, FLSH in *.
  destruct H as ((HP & S128 & Hs & S144 & Ho17) & S216 & S224 & S248 & Hin & HC).
  assert (K : forall off v, spill regs m off v -> spill regs' m off v)
    by (unfold spill; intros off v (A & HA & Hq); exists A; split; [unfold rg in *; rewrite E9; exact HA | exact Hq]).
  exact (conj (conj (pro_regs g fr regs regs' m HP E9) (conj (K _ _ S128) (conj Hs (conj (K _ _ S144) Ho17))))
           (conj (K _ _ S216) (conj (K _ _ S224) (conj (K _ _ S248) (conj Hin (flc_regs fr regs regs' m HC E9)))))).
Qed.

Section S.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis HBCMP : bcmp_wrap_contract.

(* The Lib-evt -> SR bridge (the callee contracts live in Lib.Exec, so the run is a Lib evt). *)
Lemma sl_run_lib : forall regs pc mem md
  (K : bvmap 5 word -> word -> (word -> option byte) -> Prop) (P : config -> Prop),
  m_halted md = None ->
  evt rsegs
    (fun ms => exists R pc' mem', ms = MState.MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs) /\ K R pc' mem')
    (MState.MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None mem (seg_rom rsegs)) ->
  (forall R pc' mem' regs' md', K R pc' mem' -> (forall r, getr regs' r = getr R r) -> AsanLift.mat_le md md' ->
     SR rsegs (mkCfg (mkst regs' pc' mem' (seg_rom rsegs)) md') P) ->
  SR rsegs (mkCfg (mkst regs pc mem (seg_rom rsegs)) md) P.
Proof.
  intros regs pc mem md K P Hh HE HK.
  eapply (AsanLift.evt_SR_canon_lazy rsegs (mkst regs pc mem (seg_rom rsegs)) _ md P); [exact HE | exact Hh |].
  intros ms' md' (can & (R & pc' & mem' & -> & HKR) & Heq) Hmat.
  destruct Heq as (HR & HF' & Hpc & Hsvc & Hres & Hfc & Hm & Hrom).
  destruct ms' as [regs' fr' pcv' svc' rv' fc' m' ro'].
  cbn in HR, HF', Hpc, Hsvc, Hres, Hfc, Hm, Hrom. subst.
  apply (HK R _ _ regs' md' HKR); [apply kb_getr_eqv; exact HR | exact Hmat].
Qed.

(* ---- seg_F14 : the entry cut Inv_A82154_at (0x82154) to the exit cuts Inv_A82178_at ([A+280] <> 0: the bcmp
   is skipped) and Inv_A82174_at (the bcmp fall-through), with their shared tail f14_tail, all SlotInv's (aslot
   push 11B). ---- *)
Lemma seg_F14 : forall j : nat,
  Hat B APIf ra (Inv_A82178_at B APIf ra) j -> Hat B APIf ra (Inv_A82174_at B APIf ra) j ->
  Hat B APIf ra (Inv_A82154_at B APIf ra) j.
Proof.
  intros j He0 Hdc g c HInv.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hj & HHB & HFLSI & HLK &
    A & v280 & H9 & H10 & HAb & Hv280b & Hv280s & Hphifr & Hphisep &
    H184 & H208 & H280 & HbL & HaL & HbR & HaR &
    HB1 & HB2 & HB3 & HB4 & HB5 & HAC0 & HSW0 & Hc256 &
    H64 & H72 & H80 & H272 & H264 & HFGM & HCAR & HIFS2).
  subst c. rewrite SEGS.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (fra_win B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs mem md HFRA) as (Hwlo & Hwstk).
  pose proof (fra_frame B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs mem md HFRA)
    as (Hplace & HfrA & Hfsmeta & Hfrwr).
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (A2 & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspillq & Hselq & Hfr24q & Hloc & Hhdr1 & Hhdr2 & Hshf & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (HwinB : 0 <= g_S g - AF.SLOT_STACK /\ g_S g <= 2 ^ 64)
    by (unfold stk in Hwin; split; [apply (proj1 Hwin) | apply (proj1 (proj2 Hwin))]).
  assert (HA2b : 0 <= A2 < 2 ^ 64) by lia.
  assert (HA2 : A2 = A).
  { assert (E : Z_to_bv 64 A2 = Z_to_bv 64 A) by (unfold rg in *; rewrite <- Hr9; exact H9).
    apply (f_equal (bv_unsigned (n := 64))) in E.
    rewrite !MState.unsigned_lit in E by lia. exact E. }
  subst A2.
  assert (HSPu : bv_unsigned (getr regs 2) = AC.aspZ regs) by (unfold AC.aspZ; reflexivity).
  assert (Hhigh : HIGHMEM_BEG <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md)
    by (apply (AC.a_laws_stack_high _ _ _ _ _ LAWS (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md HAH)).
  assert (HKf : 0 <= REAC_CTRL_IDENTITY_FRAGMENT_K <= FN_STACK)
    by (unfold REAC_CTRL_IDENTITY_FRAGMENT_K; lia).
  pose proof (Hplace REAC_CTRL_IDENTITY_FRAGMENT_K HKf) as Hfrsep.
  assert (HbvA : bv_unsigned (getr regs 9) = A)
    by (unfold rg in H9; rewrite H9; apply MState.unsigned_lit; lia).
  rewrite HbvA in HfrA.
  assert (HaspH : HIGHMEM_BEG <= AC.aspZ regs - REAC_CTRL_IDENTITY_FRAGMENT_K)
    by (unfold REAC_CTRL_IDENTITY_FRAGMENT_K in *; lia).
  assert (HaspE : AC.aspZ regs <= APPMEM_END) by lia.
  (* the frame body is app memory, on both arms *)
  assert (Happ : forall a, fr <= a < fr + FRAME_BYTES -> app_mem a).
  { destruct Hloc as [[_ [_ Hreal]]|[_ [_ [Hfs _]]]].
    - intros a Ha. destruct (Hreal a Ha) as (Hlo2 & Hhi2).
      right. unfold APPMEM_END, HIGHMEM_BEG in *. lia.
    - intros a Ha. destruct (Hfs a Ha) as (FSa & HFSr & Hw & Hlo2 & Hhi2).
      pose proof (lw_fs_place (APIf rc) (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md FSa HAH Hw HFSr) as LWr1.
      pose proof (lwf_gt _ _ _ _ LWr1) as HG.
      pose proof (lwf_end _ _ _ _ LWr1) as Hend.
      pose proof (lwf_app _ _ _ _ LWr1) as Happ2.
      exact (Happ2 a ltac:(lia)). }
  assert (Hfb : 0 <= fragb fr < 2 ^ 64).
  { assert (Ha : app_mem (fr + 2768)) by (apply Happ; lia).
    unfold fragb, app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG in *. lia. }
  assert (HLb : 0 <= fr + 336 < 2 ^ 64).
  { assert (Ha : app_mem (fr + 336)) by (apply Happ; lia).
    unfold app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG in *. lia. }
  assert (HGT : AC.GT <= fr).
  { destruct Hloc as [[_ [_ Hreal]]|[_ [_ [Hfs _]]]].
    - destruct (Hreal fr ltac:(lia)) as (Hlo2 & _). unfold AC.GT, HIGHMEM_BEG in *. lia.
    - destruct (Hfs fr ltac:(lia)) as (FSa & HFSr & Hw & Hlo2 & Hhi2).
      pose proof (lw_fs_place (APIf rc) (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md FSa HAH Hw HFSr) as LWr2.
      pose proof (lwf_gt _ _ _ _ LWr2) as HG. lia. }
  assert (Hfnz : fragb fr <> 0) by (unfold fragb, AC.GT in *; lia).
  assert (Hphinz : phi <> 0) by (destruct HHB as (HH & _); exact HH).
  assert (Hrr : 0 <= fg_ret (frcl g j fr phi) <= 1).
  { unfold frcl. apply fg_ret_range; solve [exact Hfnz | exact Hphinz | unfold AC.GT in *; lia]. }
  (* the callee's stack window *)
  assert (Hstkc : stk rsegs mem (AC.aspZ regs - REAC_CTRL_IDENTITY_FRAGMENT_K) (AC.aspZ regs)).
  { destruct (stk_split rsegs mem (AC.aspZ regs - FN_STACK)
                (AC.aspZ regs - REAC_CTRL_IDENTITY_FRAGMENT_K) (AC.aspZ regs) Hwstk
                ltac:(unfold REAC_CTRL_IDENTITY_FRAGMENT_K in *; lia)) as (_ & Hs2). exact Hs2. }
  (* FLV: the five spill pointers, and the two output cells when the turn opens a record *)
  assert (HFLV : FLV g fr j regs mem).
  { unfold FLV, spill. split; [exists A; split; [exact H9 | exact H64]|].
    split; [exists A; split; [exact H9 | exact H72]|].
    split; [exists A; split; [exact H9 | exact H80]|].
    split; [exists A; split; [exact H9 | exact H272]|].
    split; [exists A; split; [exact H9 | exact H264]|].
    intros Hrf.
    rewrite (trf_of_frcl g j fr phi) in Hrf
      by solve [exact Hfnz | exact Hphinz | unfold AC.GT in *; lia].
    rewrite (ret1_close _ Hrf) in HFGM. cbn [fg_mem] in HFGM.
    destruct HFGM as (_ & _ & Hpp & Hpn). unfold q64. split; [exact Hpp|].
    unfold f_pll. exact Hpn. }
  destruct (Z.eq_dec v280 0) as [Hv0 | Hvn].
  - (* [A+280] = 0: the bcmp call, landing at 0x82174 *)
    rewrite Hv0 in H280, Hv280b, Hv280s.
    destruct (memcmp_model_total (t_FG (g_in g) j) (frrec g j fr phi) 72
                ltac:(rewrite t_FG_length; lia) ltac:(rewrite frrec_length; lia)) as (vcmp & Hmm).
    apply (sl_run_lib regs (Z_to_bv 64 0x82154) mem md
      (fun R0 pc' mem' =>
         pc' = Z_to_bv 64 0x82174 /\
         getr R0 2 = getr regs 2 /\ getr R0 3 = getr regs 3 /\ getr R0 4 = getr regs 4 /\
         getr R0 8 = getr regs 8 /\ getr R0 9 = getr regs 9 /\ getr R0 19 = getr regs 19 /\
         getr R0 21 = getr regs 21 /\ getr R0 26 = getr regs 26 /\ getr R0 18 = getr regs 18 /\
         getr R0 22 = getr regs 22 /\ getr R0 23 = getr regs 23 /\ getr R0 24 = getr regs 24 /\
         getr R0 10 = Z_to_bv 64 vcmp /\ getr R0 25 = Z_to_bv 64 (fg_ret (frcl g j fr phi)) /\
         getr R0 20 = getr regs 20 /\
         munch [(AC.aspZ regs - BCMP_WRAP_K, AC.aspZ regs)] mem mem' /\
         wmono rsegs mem mem' /\ ro_agree rsegs mem' /\
         stk rsegs mem' (AC.aspZ regs - REAC_CTRL_IDENTITY_FRAGMENT_K) (AC.aspZ regs) /\
         asan_cells mem' /\ shadow_rw mem' /\
         bytes_at rsegs mem' (fr + 336) (t_FG (g_in g) j) /\
         bytes_at rsegs mem' (fragb fr) (frrec g j fr phi))
      (Post B APIf ra g)).
    + exact Hhalt.
    + eapply evt_mono.
      { unfold Regs6ss.mkR_of.
        eapply f14_evt_dc_ro with (A := A) (r := fg_ret (frcl g j fr phi)) (L := fr + 336) (R := fragb fr)
          (vcmp := vcmp) (lo := AC.aspZ regs - REAC_CTRL_IDENTITY_FRAGMENT_K)
          (ls := t_FG (g_in g) j) (rs := frrec g j fr phi).
        - exact HBCMP.
        - unfold rg in H9; exact H9.
        - unfold rg in H10; exact H10.
        - exact Hrr.
        - exact HLb.
        - exact Hfb.
        - unfold q64 in H280; exact H280.
        - unfold q64 in H184; exact H184.
        - unfold q64 in H208; exact H208.
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
        - fold_sp regs. unfold BCMP_WRAP_K, REAC_CTRL_IDENTITY_FRAGMENT_K in *. lia.
        - fold_sp regs. unfold fragb, BCMP_WRAP_K, REAC_CTRL_IDENTITY_FRAGMENT_K in *. lia.
        - fold_sp regs. exact Hstkc.
        - fold_sp regs. unfold BCMP_WRAP_K, REAC_CTRL_IDENTITY_FRAGMENT_K in *. lia.
        - exact HaspH.
        - fold_sp regs. exact HaspE.
        - exact HAC0.
        - exact HSW0.
        - exact HB1.
        - exact HB2.
        - exact HB3.
        - exact HB4.
        - exact HB5. }
      { intros ms' (ra' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t0' & t1' & t2' & t3' & t4' & t5' & t6' & m'
                    & E & MU & WM & RO' & ST' & AC' & SW' & HbL' & HbR').
        eexists _, (Z_to_bv 64 0x82174), m'. split; [exact E|].
        split; [reflexivity|].
        split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        split; [reflexivity|]. split; [unfold rg in H9; rewrite H9; reflexivity|].
        split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        split; [reflexivity|].
        match type of ST' with context [bv_unsigned ?s] => change (bv_unsigned s) with (AC.aspZ regs) in MU, ST' end.
        split; [exact MU|]. split; [exact WM|]. split; [exact RO'|]. split; [exact ST'|].
        split; [exact AC'|]. split; [exact SW'|].
        split; [exact HbL' | exact HbR']. }
    + intros R0 pc' mem' regs' md' (Hpc & Er2 & Er3 & Er4 & Er8 & Er9 & Er19 & Er21 & Er26 & Er18 & Er22 & Er23 &
        Er24 & Er10 & Er25 & Er20 &
        MU & WM & HroM & ST' & AC' & SW' & TbL & TbR) Hreg Hmat.
      subst pc'.
      assert (Fr2 : getr regs' 2 = getr regs 2) by (rewrite Hreg; exact Er2).
      assert (Fr3 : getr regs' 3 = getr regs 3) by (rewrite Hreg; exact Er3).
      assert (Fr4 : getr regs' 4 = getr regs 4) by (rewrite Hreg; exact Er4).
      assert (Fr8 : getr regs' 8 = getr regs 8) by (rewrite Hreg; exact Er8).
      assert (Fr9 : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact Er9).
      assert (Fr19 : getr regs' 19 = getr regs 19) by (rewrite Hreg; exact Er19).
      assert (Fr21 : getr regs' 21 = getr regs 21) by (rewrite Hreg; exact Er21).
      assert (Fr26 : getr regs' 26 = getr regs 26) by (rewrite Hreg; exact Er26).
      assert (Fr18 : getr regs' 18 = getr regs 18) by (rewrite Hreg; exact Er18).
      assert (Fr22 : getr regs' 22 = getr regs 22) by (rewrite Hreg; exact Er22).
      assert (Fr23 : getr regs' 23 = getr regs 23) by (rewrite Hreg; exact Er23).
      assert (Fr24 : getr regs' 24 = getr regs 24) by (rewrite Hreg; exact Er24).
      assert (Fr20 : getr regs' 20 = getr regs 20) by (rewrite Hreg; exact Er20).
      assert (Fr10 : getr regs' 10 = Z_to_bv 64 vcmp) by (rewrite Hreg; exact Er10).
      assert (Fr25 : getr regs' 25 = Z_to_bv 64 (fg_ret (frcl g j fr phi))) by (rewrite Hreg; exact Er25).
      assert (HaspEq : AC.aspZ regs' = AC.aspZ regs) by (unfold AC.aspZ; rewrite Fr2; reflexivity).
      (* the wrapper's write set *)
      assert (Hallapp : all_app [(AC.aspZ regs - BCMP_WRAP_K, AC.aspZ regs)]).
      { cbn [all_app]. split; [|exact I]. intros a Ha. unfold app_mem. right.
        unfold APPMEM_END, HIGHMEM_BEG, BCMP_WRAP_K, REAC_CTRL_IDENTITY_FRAGMENT_K in *. lia. }
      assert (Hrtdj : rt_disjoint [(AC.aspZ regs - BCMP_WRAP_K, AC.aspZ regs)]).
      { unfold rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
          RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG,
          RT_AGLOB, RT_AGLOB_LEN, BCMP_WRAP_K, REAC_CTRL_IDENTITY_FRAGMENT_K, HIGHMEM_BEG in *.
        cbn [disjoint_from]. repeat split; first [left; lia | exact I]. }
      assert (Hout : forall x, (x < AC.aspZ regs - BCMP_WRAP_K \/ AC.aspZ regs <= x) ->
                outside [(AC.aspZ regs - BCMP_WRAP_K, AC.aspZ regs)] x)
        by (intros x Hx; cbn [outside]; split; [lia | exact I]).
      assert (Hwmon : forall q, 0 <= q < 2 ^ 64 -> writable_at rsegs mem q -> writable_at rsegs mem' q)
        by (intros q Hq Hw; exact (WM (Z_to_bv 64 q) Hw)).
      assert (Hmc : forall q, 0 <= q < 2 ^ 64 ->
                ~ AC.a_store_ok (hb1 phi (AC.a_size (flen g j)) ++ g_H g)
                    (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) q ->
                mem' (Z_to_bv 64 q) = mem (Z_to_bv 64 q)).
      { intros q Hq Hns. apply MU. rewrite MState.unsigned_lit by exact Hq.
        apply Hout. destruct (Z_lt_le_dec q (AC.aspZ regs - BCMP_WRAP_K)) as [Hl|Hl]; [left; lia|].
        destruct (Z_lt_le_dec q (AC.aspZ regs)) as [Hh|Hh]; [|right; lia].
        exfalso. apply Hns. right. left.
        unfold APPMEM_END, BCMP_WRAP_K, FN_STACK in *. lia. }
      pose proof (lw_store (APIf rc) (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem mem' md HAH Hmc Hwmon) as LWr3.
      pose proof (lws_ah _ _ _ _ _ LWr3) as HAH'.
      pose proof (lws_own _ _ _ _ _ LWr3) as Hown'.
      pose proof (lws_lo _ _ _ _ _ LWr3) as HSTK'.
      pose proof (lws_hi _ _ _ _ _ LWr3) as HSTKH'.
      assert (HshIS : forall x, Sfr fr <= x < Sfr fr + FRAME_SHADOW -> in_shadow x).
      { intros x Hx.
        assert (Hdiv : (fr + 8 * (x - Sfr fr)) / 8 = fr / 8 + (x - Sfr fr)).
        { replace (8 * (x - Sfr fr)) with ((x - Sfr fr) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
        assert (Hin : fr <= fr + 8 * (x - Sfr fr) < fr + FRAME_BYTES) by lia.
        pose proof (shadow_of_app (fr + 8 * (x - Sfr fr)) (Happ _ Hin)) as His.
        replace (shadow_addr (fr + 8 * (x - Sfr fr))) with x in His; [exact His|].
        unfold shadow_addr. rewrite Hdiv. unfold Sfr, shadow_addr. lia. }
      pose proof (Hplace BCMP_WRAP_K ltac:(unfold BCMP_WRAP_K; lia)) as Hfrsep2.
      assert (Hfrout : forall x, fr <= x < fr + FRAME_BYTES ->
                outside [(AC.aspZ regs - BCMP_WRAP_K, AC.aspZ regs)] x)
        by (intros x Hx; apply Hout; unfold BCMP_WRAP_K in *; lia).
      assert (HoutA : forall x, A + 32 <= x < A + 312 ->
                outside [(AC.aspZ regs - BCMP_WRAP_K, AC.aspZ regs)] x)
        by (intros x Hx; apply Hout; right; unfold AC.aspZ in *; lia).
      assert (HSTKW : stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g)).
      { apply (F13.stk_keep [(AC.aspZ regs - BCMP_WRAP_K, AC.aspZ regs)] mem mem'
                 (g_S g - AF.SLOT_STACK) (g_S g));
          [exact Hwin | exact MU | exact WM |].
        intros x Hx Ho. destruct ST' as (_ & _ & HS).
        assert (Hin : AC.aspZ regs - REAC_CTRL_IDENTITY_FRAGMENT_K <= x < AC.aspZ regs).
        { destruct (Z_lt_le_dec x (AC.aspZ regs - BCMP_WRAP_K)) as [Hl|Hl];
            [exfalso; apply Ho; apply Hout; left; lia|].
          destruct (Z_lt_le_dec x (AC.aspZ regs)) as [Hh|Hh];
            [|exfalso; apply Ho; apply Hout; right; lia].
          unfold BCMP_WRAP_K, REAC_CTRL_IDENTITY_FRAGMENT_K in *. lia. }
        destruct (HS x Hin) as (_ & b & Hb). exists b. exact Hb. }
      assert (HFRA' : FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs mem' md).
      { apply (Tac_slot.sl_fr_cl B APIf ra empty FF g fr (hb1 phi (AC.a_size (flen g j))) regs regs mem mem' md
                 [(AC.aspZ regs - BCMP_WRAP_K, AC.aspZ regs)] HFRA MU WM HroM Hallapp Hrtdj HAH' HSTK');
          try reflexivity.
        - intros x Hx. apply Hout. left.
          unfold AC.GT, BCMP_WRAP_K, REAC_CTRL_IDENTITY_FRAGMENT_K, HIGHMEM_BEG in *. lia.
        - intros x Hx. apply Hfrout. lia.
        - intros A' HA' HA'b x Hx. apply Hout.
          assert (EA' : A' = A).
          { assert (E : Z_to_bv 64 A' = Z_to_bv 64 A) by (unfold rg in H9; rewrite <- HA'; exact H9).
            apply (f_equal (bv_unsigned (n := 64))) in E.
            rewrite !MState.unsigned_lit in E by lia. exact E. }
          subst A'. right. unfold AC.aspZ in *. lia.
        - intros x Hx. apply Hout. right. unfold AC.aspZ in *. lia.
        - intros x Hx. apply Hout. pose proof (HshIS x Hx) as His.
          unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG,
            BCMP_WRAP_K, REAC_CTRL_IDENTITY_FRAGMENT_K in *. lia.
        - intros A' HA' HA'b x Hx. apply Hout.
          assert (EA' : A' = A).
          { assert (E : Z_to_bv 64 A' = Z_to_bv 64 A) by (unfold rg in H9; rewrite <- HA'; exact H9).
            apply (f_equal (bv_unsigned (n := 64))) in E.
            rewrite !MState.unsigned_lit in E by lia. exact E. }
          subst A'. right. unfold AC.aspZ in *. lia.
        - exact HSTKW.
        - intros HR.
          eapply Tac_slot.fsrec_munch_lo with (W := [(AC.aspZ regs - BCMP_WRAP_K, AC.aspZ regs)]);
            [exact HR | exact HAH | exact MU | |].
          + intros x Hx. apply Hout. left.
            unfold BCMP_WRAP_K, REAC_CTRL_IDENTITY_FRAGMENT_K, HIGHMEM_BEG in *. lia.
          + intros x Hxa Hxf Hxs. apply Hout. left. unfold BCMP_WRAP_K, AC.aspZ in *. lia. }
      assert (HFRA'' : FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs' mem' md').
      { apply (Tac_slot.sl_fra_move B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs regs' mem' md md' HFRA');
          [exact Fr2 | exact Fr3 | exact Fr4 | exact Fr8 | exact Fr9 | exact Fr19 | exact Fr26 | exact Hmat]. }
      (* ENT: the wrapper wrote only its own 4560 stack bytes, which lie inside the slot window below the entry
         sp, so no byte the entry relation speaks of changed; then the model step of sl_run_lib. *)
      assert (HWcases : forall x, 0 <= x < 2 ^ 64 ->
                outside [(AC.aspZ regs - BCMP_WRAP_K, AC.aspZ regs)] x \/
                (g_S g - AF.SLOT_STACK <= x < g_S g) \/ (fr <= x < fr + FRAME_BYTES) \/
                (Sfr fr <= x < Sfr fr + FRAME_SHADOW)).
      { intros x Hx.
        destruct (Z_lt_le_dec x (AC.aspZ regs - BCMP_WRAP_K)) as [Hd|Hd]; [left; apply Hout; left; lia|].
        destruct (Z_lt_le_dec x (AC.aspZ regs)) as [Hd2|Hd2]; [|left; apply Hout; right; lia].
        right; left. unfold BCMP_WRAP_K in *. lia. }
      assert (HENT' : ENT APIf g (hb1 phi (AC.a_size (flen g j))) mem' md).
      { apply (Tac_slot.ent_store B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs mem mem' md
                 [(AC.aspZ regs - BCMP_WRAP_K, AC.aspZ regs)] HENT HFRA MU HWcases HSTK' HSTKH').
        intros a Hia Ho. exact (proj2 (Hown' a) Ho). }
      assert (HENT'' : ENT APIf g (hb1 phi (AC.a_size (flen g j))) mem' md').
      { exact (Tac_slot.ent_mat APIf g (hb1 phi (AC.a_size (flen g j))) mem' md md' HENT' Hmat). }
      assert (Hmeta : meta_kept mem mem') by (apply (munch_meta _ mem mem' MU Hallapp)).
      assert (HR9' : rg regs' 9 A) by (unfold rg; rewrite Fr9; unfold rg in H9; exact H9).
      (* a live block of the heap list ends below stklo, a megabyte below the wrapper's window *)
      assert (Hblkw : forall q n x, In (q, n) (hb1 phi (AC.a_size (flen g j)) ++ g_H g) -> q <= x < q + n ->
                outside [(AC.aspZ regs - BCMP_WRAP_K, AC.aspZ regs)] x).
      { intros q n x Hin Hx.
        pose proof (lw_blocks (APIf rc) (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md q n HAH Hin) as LWr4.
        pose proof (lwb_end _ _ _ _ _ _ LWr4) as Hend.
        apply Hout. left. unfold BCMP_WRAP_K, AC.aspZ in *. lia. }
      assert (HIexit : Inv_A82174_at B APIf ra g j (mkCfg (mkst regs' (Z_to_bv 64 0x82174) mem' (seg_rom rsegs)) md')).
      { exists phi, regs', mem', md', fr. rewrite SEGS. split; [reflexivity|].
        split; [exact HFRA''|].
        split; [exact HENT''|].
        split; [exact Hgn|].
        split; [exact Hj|].
        split.
        { destruct HHB as (Hphinz2 & Hphiad). split; [exact Hphinz2|].
          eapply addressable_kept; [exact Hphiad | exact Hmeta]. }
        split.
        { destruct HFLSI as ((HPRO & F128 & Fstk & F144 & Fid17) & F216 & F224 & F248 & (Fin1 & Fin2 & Fin3) &
            HFLC).
          assert (Hsp : forall off v, 32 <= off -> off + 8 <= 312 -> spill regs mem off v ->
                    spill regs' mem' off v).
          { intros off v Ho1 Ho2 Hs. eapply spill_keep;
              [exact Hs | exact H9 | lia | unfold APPMEM_END in *; lia | lia | lia | exact Fr9 | exact MU |].
            intros x Hx. apply HoutA. lia. }
          split.
          { split.
            { eapply pro_keep; [exact HPRO | exact H9 | lia | unfold APPMEM_END in *; lia | exact Fr9 | exact MU
                               | exact Hmeta | |].
              - intros x Hx. apply HoutA. lia.
              - intros Hn x Hx. apply (Hblkw (g_p g) (g_n g) x); [|exact Hx].
                apply in_or_app. right. apply Fin1. exact Hn. }
            split; [apply Hsp; [lia | lia | exact F128]|].
            split.
            { apply (F13.stk_keep [(AC.aspZ regs - BCMP_WRAP_K, AC.aspZ regs)] mem mem' fr (fr + FRAME_BYTES));
                [exact Fstk | exact MU | exact WM |].
              intros x Hx Ho. exfalso. apply Ho. apply Hfrout. lia. }
            split; [apply Hsp; [lia | lia | exact F144]|].
            eapply addressable_kept; [exact Fid17 | exact Hmeta]. }
          split; [apply Hsp; [lia | lia | exact F216]|].
          split; [apply Hsp; [lia | lia | exact F224]|].
          split; [apply Hsp; [lia | lia | exact F248]|].
          split.
          { split; [exact Fin1|].
            split; [eapply addressable_kept; [exact Fin2 | exact Hmeta]|].
            eapply fl_bytes; [exact Fin3 | exact MU |].
            intros x Hx. apply (Hblkw (g_p g) (g_n g) x); [|unfold g_n, nlen; lia].
            apply in_or_app. right. apply Fin1. unfold g_n, nlen in *. lia. }
          (* push 14D / 14E: FLC *)
          eapply flc_keep; [exact HFLC | exact H9 | lia | unfold APPMEM_END in *; lia | exact Fr9 | exact MU
                           | exact Hmeta |].
          intros x Hx. apply HoutA. lia. }
        split.
        { destruct HLK as (Hj' & Hs5j & HOURb). split; [exact Hj'|]. split.
          - unfold rg in *. rewrite Fr21. exact Hs5j.
          - unfold OURb in *. eapply fl_bytes; [exact HOURb | exact MU |].
            rewrite OUR_length. intros x Hx. apply Hfrout. lia. }
        split.
        { destruct HFLV as (_ & _ & _ & _ & _ & Fcond).
          unfold FLV, spill.
          assert (T80 : q64 mem' (A + 80) (fragb fr + 15)).
          { unfold q64 in *. eapply fl_bytes; [exact H64 | exact MU |].
            rewrite length_le8. intros x Hx. apply HoutA. lia. }
          assert (T88 : q64 mem' (A + 88) (fragb fr + 19)).
          { unfold q64 in *. eapply fl_bytes; [exact H72 | exact MU |].
            rewrite length_le8. intros x Hx. apply HoutA. lia. }
          assert (T96 : q64 mem' (A + 96) (fragb fr + 8)).
          { unfold q64 in *. eapply fl_bytes; [exact H80 | exact MU |].
            rewrite length_le8. intros x Hx. apply HoutA. lia. }
          assert (T272 : q64 mem' (A + 272) (fr + 272)).
          { unfold q64 in *. eapply fl_bytes; [exact H272 | exact MU |].
            rewrite length_le8. intros x Hx. apply HoutA. lia. }
          assert (T264 : q64 mem' (A + 264) (fr + 304)).
          { unfold q64 in *. eapply fl_bytes; [exact H264 | exact MU |].
            rewrite length_le8. intros x Hx. apply HoutA. lia. }
          split; [exists A; split; [exact HR9' | exact T80]|].
          split; [exists A; split; [exact HR9' | exact T88]|].
          split; [exists A; split; [exact HR9' | exact T96]|].
          split; [exists A; split; [exact HR9' | exact T272]|].
          split; [exists A; split; [exact HR9' | exact T264]|].
          intros Hrf. destruct (Fcond Hrf) as (Hpp & Hpn). unfold q64 in *. split.
          - eapply fl_bytes; [exact Hpp | exact MU |]. rewrite length_le8. intros x Hx. apply Hfrout. lia.
          - eapply fl_bytes; [exact Hpn | exact MU |]. rewrite length_le8. intros x Hx. apply Hfrout. lia. }
        exists vcmp, A.
        split; [exact Hmm|].
        (* push 12: IFS2 is clear of the wrapper's window (the frame bytes and the spills [A+104, A+120)) *)
        split; cycle 1.
        { eapply ifs2_keep; [exact HIFS2 | exact H9 | lia | unfold APPMEM_END in *; lia | exact Fr9 | exact MU
                            | exact Hmeta | | |].
          - intros x Hx. apply Hfrout. lia.
          - intros x Hx. apply HoutA. lia.
          - intros x Hx. apply Hfrout. lia. }
        unfold f14_tail.
        split; [exact HR9'|].
        split; [unfold rg; exact Fr25|].
        split; [unfold rg; exact Fr10|].
        split; [exact AC'|].
        split; [exact SW'|].
        split; [exact HAb|].
        split; [lia|].
        split; [exact Hv280s|].
        split; [exact Hphifr|].
        split; [rewrite HaspEq; exact Hphisep|].
        split; [rewrite HaspEq; exact ST'|].
        split.
        { unfold q64 in *. eapply fl_bytes; [exact H184 | exact MU |].
          rewrite length_le8. intros x Hx. apply HoutA. lia. }
        split.
        { unfold q64 in *. eapply fl_bytes; [exact H208 | exact MU |].
          rewrite length_le8. intros x Hx. apply HoutA. lia. }
        split.
        { unfold q64 in *. eapply fl_bytes; [exact H280 | exact MU |].
          rewrite length_le8. intros x Hx. apply HoutA. lia. }
        split; [exact TbL|].
        split; [eapply addressable_kept; [exact HaL | exact Hmeta]|].
        split; [exact TbR|].
        split; [eapply addressable_kept; [exact HaR | exact Hmeta]|].
        split.
        { eapply fl_bytes; [exact HB1 | exact MU |]. rewrite length_le8. intros x Hx. apply Hout. left.
          unfold REAL_BCMP, BCMP_WRAP_K, REAC_CTRL_IDENTITY_FRAGMENT_K, HIGHMEM_BEG in *. lia. }
        split.
        { eapply fl_bytes; [exact HB2 | exact MU |]. rewrite length_le8. intros x Hx. apply Hout. left.
          unfold REAL_MEMCMP, BCMP_WRAP_K, REAC_CTRL_IDENTITY_FRAGMENT_K, HIGHMEM_BEG in *. lia. }
        split.
        { eapply fl_bytes; [exact HB3 | exact MU |]. rewrite length_le8. intros x Hx. apply Hout. left.
          unfold GOT_CF, BCMP_WRAP_K, REAC_CTRL_IDENTITY_FRAGMENT_K, HIGHMEM_BEG in *. lia. }
        split.
        { eapply fl_bytes; [exact HB4 | exact MU |]. cbn [length]. intros x Hx. apply Hout. left.
          unfold CF, BCMP_WRAP_K, REAC_CTRL_IDENTITY_FRAGMENT_K, HIGHMEM_BEG in *. lia. }
        split.
        { eapply fl_bytes; [exact HB5 | exact MU |]. cbn [length]. intros x Hx. apply Hout. left.
          unfold CF, BCMP_WRAP_K, REAC_CTRL_IDENTITY_FRAGMENT_K, HIGHMEM_BEG in *. lia. }
        split.
        { eapply rw_cells_transport; [exact Hc256 | exact MU | exact WM |].
          change (Z.of_nat (cells_size [C8 (Z_to_bv 64 (fr + 256)); C8 (Z_to_bv 64 (fr + 304));
                                        C8 (Z_to_bv 64 (fr + 272))])) with 24.
          cbn [disjoint_from]. split; [|exact I]. right. unfold AC.aspZ in *. lia. }
        (* the carried bundle: spills, record bytes and frame bytes clear of the wrapper's window *)
        split; cycle 1.
        { eapply f16carry_keep; [exact HCAR | exact MU | exact Hallapp | exact H9 | unfold AC.GT in *; lia | lia
                                | unfold APPMEM_END in *; lia
                                | exact Fr9 | exact Fr18 | exact Fr20 | exact Fr22 | exact Fr23 | exact Fr24
                                | exact HoutA | | | |].
          - intros Hl x Hx. apply (Hblkw phi (AC.a_size (flen g j)) x);
              [apply in_or_app; left; unfold hb1; cbn [In]; left; reflexivity | unfold AC.a_size; lia].
          - intros x Hx. apply Hfrout. lia.
          - intros x Hx. apply Hfrout. lia.
          - intros x Hx. apply Hfrout. lia. }
        (* fg_mem survives: every cell it names is in the frame body *)
        assert (Hreclen : length (fg_next (t_FG (g_in g) j) (t_g (g_in g) j) (frcl g j fr phi)) = 72%nat)
          by apply frrec_length.
        destruct (frcl g j fr phi) eqn:EC; try (rewrite EC in HFGM); try (rewrite EC in Hreclen);
          cbn [fg_mem fg_next] in HFGM, Hreclen |- *.
        - exact I.
        - exact I.
        - eapply fl_bytes; [exact HFGM | exact MU |]. rewrite Hreclen. intros x Hx. apply Hfrout.
          unfold fragb in *. lia.
        - eapply fl_bytes; [exact HFGM | exact MU |]. rewrite Hreclen. intros x Hx. apply Hfrout.
          unfold fragb in *. lia.
        - eapply fl_bytes; [exact HFGM | exact MU |]. rewrite Hreclen. intros x Hx. apply Hfrout.
          unfold fragb in *. lia.
        - destruct HFGM as (Hf0 & Hpa0 & Hpp0 & Hpn0).
          split.
          { eapply fl_bytes; [exact Hf0 | exact MU |]. rewrite Hreclen. intros x Hx. apply Hfrout.
            unfold fragb in *. lia. }
          split.
          { eapply fl_bytes; [exact Hpa0 | exact MU |]. rewrite length_le2. intros x Hx. apply Hfrout. lia. }
          split.
          { eapply fl_bytes; [exact Hpp0 | exact MU |]. rewrite length_le8. intros x Hx. apply Hfrout. lia. }
          eapply fl_bytes; [exact Hpn0 | exact MU |]. rewrite length_le8. intros x Hx. apply Hfrout. lia. }
      pose proof (Hdc g _ HIexit) as HSR. rewrite SEGS in HSR. exact HSR.
  - (* [A+280] <> 0: the branch at 0x82160 is taken, landing at 0x82178 with memory unchanged *)
    apply (sl_run_lib regs (Z_to_bv 64 0x82154) mem md
      (fun R0 pc' mem' =>
         pc' = Z_to_bv 64 0x82178 /\ mem' = mem /\
         getr R0 2 = getr regs 2 /\ getr R0 3 = getr regs 3 /\ getr R0 4 = getr regs 4 /\
         getr R0 8 = getr regs 8 /\ getr R0 9 = getr regs 9 /\ getr R0 19 = getr regs 19 /\
         getr R0 21 = getr regs 21 /\ getr R0 26 = getr regs 26 /\ getr R0 18 = getr regs 18 /\
         getr R0 22 = getr regs 22 /\ getr R0 23 = getr regs 23 /\ getr R0 24 = getr regs 24 /\
         getr R0 10 = Z_to_bv 64 v280 /\ getr R0 25 = Z_to_bv 64 (fg_ret (frcl g j fr phi)) /\
         getr R0 20 = getr regs 20)
      (Post B APIf ra g)).
    + exact Hhalt.
    + eapply evt_mono.
      { unfold Regs6ss.mkR_of.
        eapply f14_evt_e0 with (A := A) (r := fg_ret (frcl g j fr phi)) (v280 := v280).
        - unfold rg in H9; exact H9.
        - unfold rg in H10; exact H10.
        - exact Hrr.
        - exact Hv280b.
        - exact Hvn.
        - unfold q64 in H280; exact H280. }
      { intros ms' E.
        eexists _, (Z_to_bv 64 0x82178), mem. split; [exact E|].
        split; [reflexivity|]. split; [reflexivity|].
        split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        split; [reflexivity|]. split; [unfold rg in H9; rewrite H9; reflexivity|].
        split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity | reflexivity]. }
    + intros R0 pc' mem' regs' md' (Hpc & Hmem & Er2 & Er3 & Er4 & Er8 & Er9 & Er19 & Er21 & Er26 & Er18 &
        Er22 & Er23 & Er24 & Er10 & Er25 & Er20) Hreg Hmat.
      subst pc' mem'.
      assert (Fr2 : getr regs' 2 = getr regs 2) by (rewrite Hreg; exact Er2).
      assert (Fr3 : getr regs' 3 = getr regs 3) by (rewrite Hreg; exact Er3).
      assert (Fr4 : getr regs' 4 = getr regs 4) by (rewrite Hreg; exact Er4).
      assert (Fr8 : getr regs' 8 = getr regs 8) by (rewrite Hreg; exact Er8).
      assert (Fr9 : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact Er9).
      assert (Fr19 : getr regs' 19 = getr regs 19) by (rewrite Hreg; exact Er19).
      assert (Fr21 : getr regs' 21 = getr regs 21) by (rewrite Hreg; exact Er21).
      assert (Fr26 : getr regs' 26 = getr regs 26) by (rewrite Hreg; exact Er26).
      assert (Fr18 : getr regs' 18 = getr regs 18) by (rewrite Hreg; exact Er18).
      assert (Fr22 : getr regs' 22 = getr regs 22) by (rewrite Hreg; exact Er22).
      assert (Fr23 : getr regs' 23 = getr regs 23) by (rewrite Hreg; exact Er23).
      assert (Fr24 : getr regs' 24 = getr regs 24) by (rewrite Hreg; exact Er24).
      assert (Fr20 : getr regs' 20 = getr regs 20) by (rewrite Hreg; exact Er20).
      assert (Fr10 : getr regs' 10 = Z_to_bv 64 v280) by (rewrite Hreg; exact Er10).
      assert (Fr25 : getr regs' 25 = Z_to_bv 64 (fg_ret (frcl g j fr phi))) by (rewrite Hreg; exact Er25).
      assert (HaspEq : AC.aspZ regs' = AC.aspZ regs) by (unfold AC.aspZ; rewrite Fr2; reflexivity).
      assert (HR9' : rg regs' 9 A) by (unfold rg; rewrite Fr9; unfold rg in H9; exact H9).
      assert (HFRA'' : FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs' mem md').
      { apply (Tac_slot.sl_fra_move B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs regs' mem md md' HFRA);
          [exact Fr2 | exact Fr3 | exact Fr4 | exact Fr8 | exact Fr9 | exact Fr19 | exact Fr26 | exact Hmat]. }
      assert (HENT' : ENT APIf g (hb1 phi (AC.a_size (flen g j))) mem md')
        by exact (Tac_slot.ent_mat APIf g (hb1 phi (AC.a_size (flen g j))) mem md md' HENT Hmat).
      assert (HIexit : Inv_A82178_at B APIf ra g j (mkCfg (mkst regs' (Z_to_bv 64 0x82178) mem (seg_rom rsegs)) md')).
      { exists phi, regs', mem, md', fr. rewrite SEGS. split; [reflexivity|].
        split; [exact HFRA''|].
        split; [exact HENT'|].
        split; [exact Hgn|].
        split; [exact Hj|].
        split; [exact HHB|].
        split; [exact (flsi_regs g j fr regs regs' mem HFLSI Fr9)|].
        split.
        { destruct HLK as (Hj' & Hs5j & HOURb). split; [exact Hj'|]. split; [|exact HOURb].
          unfold rg in *. rewrite Fr21. exact Hs5j. }
        split.
        { destruct HFLV as (F64 & F72 & F80 & F272 & F264 & Fcond).
          unfold FLV, spill in *.
          split; [exists A; split; [exact HR9' | exact H64]|].
          split; [exists A; split; [exact HR9' | exact H72]|].
          split; [exists A; split; [exact HR9' | exact H80]|].
          split; [exists A; split; [exact HR9' | exact H272]|].
          split; [exists A; split; [exact HR9' | exact H264]|].
          exact Fcond. }
        split; [|exact (ifs2_regs g fr j regs regs' mem HIFS2 Fr9)].
        exists A, v280, v280.
        unfold f14_tail.
        split; [exact HR9'|].
        split; [unfold rg; exact Fr25|].
        split; [unfold rg; exact Fr10|].
        split; [exact HAC0|].
        split; [exact HSW0|].
        split; [exact HAb|].
        split; [exact Hv280b|].
        split; [exact Hv280s|].
        split; [exact Hphifr|].
        split; [rewrite HaspEq; exact Hphisep|].
        split; [rewrite HaspEq; exact Hstkc|].
        split; [exact H184|].
        split; [exact H208|].
        split; [exact H280|].
        split; [exact HbL|].
        split; [exact HaL|].
        split; [exact HbR|].
        split; [exact HaR|].
        split; [exact HB1|].
        split; [exact HB2|].
        split; [exact HB3|].
        split; [exact HB4|].
        split; [exact HB5|].
        split; [exact Hc256|].
        split; [exact HFGM|].
        eapply f16carry_keep with (W := []);
          [exact HCAR | apply munch_refl | exact I | exact H9 | unfold AC.GT in *; lia | lia
          | unfold APPMEM_END in *; lia
          | exact Fr9 | exact Fr18 | exact Fr20 | exact Fr22 | exact Fr23 | exact Fr24 | intros; exact I
          | intros; exact I
          | intros; exact I | intros; exact I | intros; exact I]. }
      pose proof (He0 g _ HIexit) as HSR. rewrite SEGS in HSR. exact HSR.
Qed.

End S.
