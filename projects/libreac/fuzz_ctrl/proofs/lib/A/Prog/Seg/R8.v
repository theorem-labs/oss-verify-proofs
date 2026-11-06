(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3060 of its 3101 lines of code are new or changed and 207 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/reac_box_catalogue_match.v, with its module paths, module names, addresses and numbers changed; 2488 of its 3291 lines of code are new or changed and 2298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/reac_box_catalogue_match.v, with its module paths and module names changed; 2419 of its 2557 lines of code are new or changed and 3153 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/Tac_slot.v, with its module paths and module names changed; 698 of its 763 lines of code are new or changed and 2492 lines of the source are left out. *)
(* Segment R8 of fuzz_ctrl LLVMFuzzerTestOneInput (asan, image A): [0x81640, 0x81654], cut Inv_A81640_at -> cut
   Inv_A81658_at (aslot push 13: the cut body with PRO /\ X81640, resp. /\ X81658). rule 24: no function proved (a slot
   segment; the callee checked_memcpy is the Section hypothesis MCPY on its contract asan_memcpy_c.v).

   The code tests the fresh buffer Phi returned by wrapper_malloc (0x81640 bnez a0,0x81648; the fall-through
   0x81644 `j 0x82bf4` is the abort edge, not taken because the cut's HB gives Phi <> 0), keeps Phi in s8
   (0x81648 mv s8,a0), reloads the serialized box address [A + 128] = fr + 544 (0x8164c ld a1,128(s1)), sets the
   count a2 = s2 = n_b (0x81650 mv a2,s2) and calls checked_memcpy (0x81654), which copies the n_b source bytes of
   out[] into Phi.

   r8_evt is the Lib-level run of the five instructions with the call taken on its contract; the contract needs
   mem_inv, so the call runs on `normalize rsegs mem` (MemNorm.evt_normalize, from FRA's ro_agree) and its post comes
   back to the real memory by mem_rel. The write set W is the fresh block [Phi, Phi + n_b) and the callee's window
   [sp - 2224, sp). Every memcpy premise comes from the cut, FRA and the allocator laws: the destination cell from
   the block's bytes (a_laws_blocks: writable, off the image, so readable), the block above GT (a_laws_block_high and
   the image's pages, r8_on_page), below stklo <= sp - FN_STACK and apart from the frame on both frame arms.
   r8_core is the run on the official body (without the X block): it hands the exit body and r8_keep (s8 = Phi,
   s2 = n_b, Phi's bytes = the copied source, the frame bytes, the spills [A + off] and every addressable range kept)
   to the continuation. PRO's input block crosses the run because it is an entry block of g_H: apart from the fresh
   block (a_laws_disjoint) and below stklo, so apart from the callee window. seg_R8 reads X81640, builds X81658 from
   r8_keep (rt_F has n_b bytes, r8_rtn; the turn-b records have 38 / 72 bytes, r8_rec_len) and closes the cut. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require asan_memcpy_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import MemNorm.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require BzBridge KindBGlue.
Import ListNotations.
Open Scope Z_scope.

Module MCC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_memcpy_c.

(* The malloc result is not zero, so 0x81640 takes the branch to 0x81648 and the abort edge 0x81644 is not taken. *)
Lemma r8_neqb0 : forall x, 0 < x < 2 ^ 64 -> negb (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 0)) = true.
Proof.
  intros x Hx. unfold bv_eqb. rewrite !MState.unsigned_lit by lia.
  rewrite (proj2 (Z.eqb_neq x 0)) by lia. reflexivity.
Qed.

(* ---- The memcpy contract's mem_inv premise from ro_agree: its premises cross mem_rel forward and its post
   crosses it back. Every byte the call reads or writes is at or above 0x5fe000, where no byte is read-only
   (r8_ro_hi), or is a byte of the fresh block, which the caller shows is not read-only. ---- *)

(* Every segment of the image ends below 0x5fe000. *)
Lemma r8_segs_below : BzBridge.seg_tops_below rsegs 0x5fe000 = true.
Proof. vm_compute. reflexivity. Qed.

(* Above the image there is no read-only byte. *)
Lemma r8_ro_hi : forall a, 0x5fe000 <= a < 2 ^ 64 -> ro_addr rsegs (wa a) = false.
Proof.
  intros a Ha. unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.ro_addr.
  match goal with |- context [find_segment ?sg ?x ?n] =>
    destruct (find_segment sg x n) as [s|] eqn:E; [|reflexivity];
    destruct (BzBridge.find_segment_below sg 0x5fe000 x n s r8_segs_below E ltac:(cbn; lia)) as [L|L];
    [exfalso; rewrite MState.unsigned_lit in L by lia; lia | cbn in L; lia] end.
Qed.

Lemma r8_wv : forall m m0 a, mem_rel rsegs m m0 -> 0x5fe000 <= a < 2 ^ 64 ->
  (wview rsegs m0 (wa a) <> None <-> wview rsegs m (wa a) <> None).
Proof. intros m m0 a HR Ha. rewrite (wview_rel_rw rsegs m m0 (wa a) HR (r8_ro_hi a Ha)). tauto. Qed.

Lemma r8_rel_stk : forall m m0 lo hi, mem_rel rsegs m m0 -> 0x5fe000 <= lo -> hi <= 2 ^ 64 ->
  (stk rsegs m lo hi <-> stk rsegs m0 lo hi).
Proof.
  intros m m0 lo hi HR Hlo Hhi.
  split; intros (H0 & H1 & H); (split; [lia|]); (split; [lia|]); intros a Ha;
    destruct (H a Ha) as (Hw & b & Hb); (split; [apply (r8_wv m m0 a HR ltac:(lia)); exact Hw|]);
    exists b; [rewrite <- (mrd_rel rsegs m m0 (wa a) HR) | rewrite (mrd_rel rsegs m m0 (wa a) HR)]; exact Hb.
Qed.

Lemma r8_rel_sw : forall m m0, mem_rel rsegs m m0 -> (shadow_rw m <-> shadow_rw m0).
Proof.
  intros m m0 HR. split; intros H a Ha; pose proof (in_shadow_range a Ha) as Hr;
    assert (Hhi : 0x5fe000 <= a < 2 ^ 64)
      by (unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Ha; lia);
    destruct (H a Ha) as (Hw & b & Hb); (split; [apply (r8_wv m m0 a HR Hhi); exact Hw|]);
    exists b; [rewrite <- (mrd_rel rsegs m m0 (wa a) HR) | rewrite (mrd_rel rsegs m m0 (wa a) HR)]; exact Hb.
Qed.

Lemma r8_rel_ad : forall m m0 p n, mem_rel rsegs m m0 -> (addressable m p n <-> addressable m0 p n).
Proof.
  intros m m0 p n HR.
  split; intros (H0 & H1 & H2 & H); (split; [exact H0|]); (split; [exact H1|]); (split; [exact H2|]);
    intros i Hi; destruct (H i Hi) as (Hap & b & Hb & Hok); (split; [exact Hap|]); exists b;
    [rewrite <- (mrd_rel rsegs m m0 _ HR) | rewrite (mrd_rel rsegs m m0 _ HR)]; split; assumption.
Qed.

Lemma r8_cells_gen : forall m m1, (forall a bs, bytes_at rsegs m a bs -> bytes_at rsegs m1 a bs) ->
  asan_cells m -> asan_cells m1.
Proof.
  intros m m1 Fb H. unfold asan_cells in *.
  repeat match goal with H' : _ /\ _ |- _ => destruct H' end.
  repeat match goal with |- _ /\ _ => split end;
    match goal with |- bytes_at _ _ ?a ?bs => apply Fb; assumption end.
Qed.

Lemma r8_rel_cells : forall m m0, mem_rel rsegs m m0 -> (asan_cells m <-> asan_cells m0).
Proof.
  intros m m0 HR. split; apply r8_cells_gen; intros a bs Hb;
    [exact (proj1 (bytes_at_rel rsegs m m0 a bs HR) Hb) | exact (proj2 (bytes_at_rel rsegs m m0 a bs HR) Hb)].
Qed.

(* A one-block cell list crosses mem_rel forward when no byte of it is read-only, and back always. *)
Lemma r8_rel_rwcb : forall m m0 a k bs, mem_rel rsegs m m0 ->
  (forall i, 0 <= i < Z.of_nat k -> ro_addr rsegs (wa (a + i)) = false) ->
  rw_cells rsegs m a [CB k bs] -> rw_cells rsegs m0 a [CB k bs].
Proof.
  intros m m0 a k bs HR Hro ((Hwf & Hb) & Hw).
  split; [split; [exact Hwf | exact (proj1 (bytes_at_rel rsegs m m0 _ _ HR) Hb)]|].
  apply (wr_at_norm rsegs m m0 a _ HR Hw). intros i Hi. apply Hro. cbn [cells_size csize] in Hi. lia.
Qed.

Lemma r8_rel_rwcb_back : forall m m0 a k bs, mem_rel rsegs m m0 ->
  rw_cells rsegs m0 a [CB k bs] -> rw_cells rsegs m a [CB k bs].
Proof.
  intros m m0 a k bs HR ((Hwf & Hb) & Hw).
  split; [split; [exact Hwf | exact (proj2 (bytes_at_rel rsegs m m0 _ _ HR) Hb)]|].
  exact (wr_at_rel rsegs m m0 a _ HR Hw).
Qed.

(* A machine state with no pending supervisor call is its MS. *)
Lemma r8_ms_eta : forall s, ms_svc_pending s = None ->
  s = MS (ms_regs s) (ms_fregs s) (ms_pc_val s) (ms_fcsr s) (ms_resv s) (ms_mem s) (ms_rom s).
Proof. intros [] H; cbn in H; subst; reflexivity. Qed.

(* ---- the run: bnez a0 ; mv s8,a0 ; ld a1,128(s1) ; mv a2,s2 ; jal checked_memcpy by its contract ---- *)
Lemma r8_evt : MCC.asan_memcpy_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv A S N phi lo : Z) (src junk : list byte),
    sp = Z_to_bv 64 spv -> s1 = Z_to_bv 64 A -> a0 = Z_to_bv 64 phi -> s2 = Z_to_bv 64 N ->
    0 < phi < 2 ^ 64 -> phi + N <= 2 ^ 64 -> 0 <= A < 2 ^ 64 -> 0 <= S < 2 ^ 64 -> 0 <= N -> 0 <= spv < 2 ^ 64 ->
    ro_cells rsegs m (A + 128) [C8 (Z_to_bv 64 S)] ->
    bytes_at rsegs m S src -> length src = Z.to_nat N ->
    rw_cells rsegs m phi [CB (Z.to_nat N) junk] ->
    (phi = S \/ S + N <= phi \/ phi + N <= S) ->
    N <= 2 ^ 40 ->
    addressable m S N -> addressable m phi N -> end_in_app S N -> end_in_app phi N ->
    (N = 0 \/ app_mem (S + 7) /\ app_mem (phi + 7)) ->
    (phi + N <= RT_LO \/ RT_HI <= phi) ->
    (phi + N <= spv - MCC.ASAN_MEMCPY_K \/ spv <= phi) -> (S + N <= spv - MCC.ASAN_MEMCPY_K \/ spv <= S) ->
    stk rsegs m lo spv -> lo + MCC.ASAN_MEMCPY_K <= spv -> HIGHMEM_BEG <= lo -> spv <= APPMEM_END ->
    asan_cells m -> shadow_rw m -> ro_agree rsegs m ->
    (forall i, 0 <= i < N -> ro_addr rsegs (wa (phi + i)) = false) ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81658) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 21 = s5 /\ getr R 22 = s6 /\ getr R 23 = s7 /\ getr R 25 = s9 /\ getr R 26 = s10 /\
         getr R 10 = Z_to_bv 64 phi /\ getr R 24 = Z_to_bv 64 phi /\ getr R 18 = Z_to_bv 64 N /\
         munch [(phi, phi + N); (spv - MCC.ASAN_MEMCPY_K, spv)] m m' /\ wmono rsegs m m' /\
         ro_agree rsegs m' /\ stk rsegs m' lo spv /\ asan_cells m' /\ shadow_rw m' /\
         rw_cells rsegs m' phi [CB (Z.to_nat N) src] /\ bytes_at rsegs m' S src)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81640) fc None m (seg_rom rsegs)).
Proof.
  intros MCPY ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv A S N phi lo src junk -> -> -> -> Hphi0 HphiN HA HS HN Hspv
    RO HbS HLsrc RWd HAL HNb AS AD ES ED APP HRT HSEPd HSEPs ST HLO HHM HAE HAC HSW HRO HROphi.
  unfold MCC.asan_memcpy_contract in MCPY.
  assert (HHMv : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  (* the call's premises on the normalized memory *)
  pose proof (mem_rel_normalize rsegs m HRO) as REL.
  assert (HbS0 : bytes_at rsegs (normalize rsegs m) S src) by exact (proj1 (bytes_at_rel rsegs m _ _ _ REL) HbS).
  assert (RWd0 : rw_cells rsegs (normalize rsegs m) phi [CB (Z.to_nat N) junk]).
  { apply (r8_rel_rwcb m _ phi (Z.to_nat N) junk REL); [|exact RWd]. intros i Hi. apply HROphi. lia. }
  assert (AS0 : addressable (normalize rsegs m) S N) by exact (proj1 (r8_rel_ad m _ _ _ REL) AS).
  assert (AD0 : addressable (normalize rsegs m) phi N) by exact (proj1 (r8_rel_ad m _ _ _ REL) AD).
  assert (ST0 : stk rsegs (normalize rsegs m) lo spv)
    by exact (proj1 (r8_rel_stk m _ lo spv REL ltac:(lia) ltac:(lia)) ST).
  assert (HAC0 : asan_cells (normalize rsegs m)) by exact (proj1 (r8_rel_cells m _ REL) HAC).
  assert (HSW0 : shadow_rw (normalize rsegs m)) by exact (proj1 (r8_rel_sw m _ REL) HSW).
  step. if_true_by (r8_neqb0 phi ltac:(lia)).
  step. step. step. step.
  eapply evt_cut.
  { eapply (evt_normalize rsegs _ _ _ _ _ _ _ _ BzBridge.wx_apart_asan HRO).
    eapply MCPY with (src := src) (junk := junk) (lo := lo).
    - rewrite !MState.unsigned_lit by lia. exact HbS0.
    - rewrite !MState.unsigned_lit by lia. exact HLsrc.
    - rewrite !MState.unsigned_lit by lia. exact RWd0.
    - rewrite !MState.unsigned_lit by lia. exact HAL.
    - rewrite !MState.unsigned_lit by lia. exact HNb.
    - rewrite !MState.unsigned_lit by lia. exact AS0.
    - rewrite !MState.unsigned_lit by lia. exact AD0.
    - rewrite !MState.unsigned_lit by lia. exact ES.
    - rewrite !MState.unsigned_lit by lia. exact ED.
    - rewrite !MState.unsigned_lit by lia. exact APP.
    - rewrite !MState.unsigned_lit by lia. exact HRT.
    - rewrite !MState.unsigned_lit by lia. exact HSEPd.
    - rewrite !MState.unsigned_lit by lia. exact HSEPs.
    - rewrite !MState.unsigned_lit by lia. exact ST0.
    - rewrite !MState.unsigned_lit by lia. exact HLO.
    - exact HHM.
    - rewrite !MState.unsigned_lit by lia. exact HAE.
    - exact HAC0.
    - exact HSW0.
    - exact (mem_inv_normalize rsegs m). }
  intros ms' (s0' & PO & HREL & HROS). unfold MCC.asan_memcpy_post in PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                  E & MU & WM & MI' & STc & RWc & HBc & AC' & SW').
  subst s0'.
  destruct HREL as (ER & EF & EP & Esv & EV & EC & ERo & HMR).
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem MS] in ER, EF, EP, Esv, EV, EC, ERo,
    HMR.
  pose proof (r8_ms_eta ms' Esv) as Ems.
  rewrite ER, EF, EP, EC, EV, ERo in Ems.
  rewrite Ems.
  assert (Ephi : bv_unsigned (Z_to_bv 64 phi) = phi) by (apply MState.unsigned_lit; lia).
  assert (EN : bv_unsigned (Z_to_bv 64 N) = N) by (apply MState.unsigned_lit; lia).
  assert (Esp : bv_unsigned (Z_to_bv 64 spv) = spv) by (apply MState.unsigned_lit; lia).
  assert (ESv : bv_unsigned (Z_to_bv 64 S) = S) by (apply MState.unsigned_lit; lia).
  rewrite Ephi in MU, RWc. rewrite EN in MU, RWc. rewrite Esp in MU, STc. rewrite ESv in HBc.
  replace (ret_pc (Z_to_bv 64 0x81658)) with (Z_to_bv 64 0x81658)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply evt_done. do 2 eexists. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|].
  (* the post on the real memory *)
  split; [exact (munch_rel rsegs _ m _ _ m' REL HMR HROS MU)|].
  split; [exact (wmono_rel rsegs m _ _ m' REL HMR HROS WM)|].
  split; [exact (ro_agree_same rsegs m _ HRO HROS)|].
  split; [exact (proj2 (r8_rel_stk _ m' lo spv HMR ltac:(lia) ltac:(lia)) STc)|].
  split; [exact (proj2 (r8_rel_cells _ m' HMR) AC')|].
  split; [exact (proj2 (r8_rel_sw _ m' HMR) SW')|].
  split; [exact (r8_rel_rwcb_back _ m' phi _ src HMR RWc) | exact (proj2 (bytes_at_rel rsegs _ m' _ _ HMR) HBc)].
Qed.

(* ---- the segment on the cuts ---- *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge Image.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import AsanRTInv PContract MemNorm AsanLift BzBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcEmit RcEmitLib RcSynth RcSynthLib RcLay RcFin
  RcFinLib reac_ctrl_build_as_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_b5 B3Rtm.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.

Module ACw := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AFw := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
Module LF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module LImg := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Image.
Module REm := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcEmit.
Module REmL := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcEmitLib.
Module RSy := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcSynth.
Module RSyL := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcSynthLib.
Module RLy := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcLay.
Module RFinL := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcFinLib.
Module RBA := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.reac_ctrl_build_as_c.
Open Scope Z_scope.

(* ---- Lengths of the round-trip model: a catalogue row has 296 bytes, X_b 32, F_b n_b (n_b <> 0), and the turn-b
   identity / fragment records 38 / 72 (b <= 6, computed per row by B3Rtm's a_rows / a_fin). ---- *)
Lemma r8_row_len : forall i, length (rowb i) = 296%nat.
Proof.
  intros i. unfold rowb, img. destruct (LImg.image_bytes rsegs (CAT + CAT_ROW * i) 296) eqn:E.
  - exact (LImg.image_bytes_length rsegs 296 _ _ E).
  - apply repeat_length.
Qed.

Lemma r8_rtX_len : forall inp b, length (rt_X inp b) = 32%nat.
Proof.
  intros inp b. unfold rt_X, RBA.ba_X, RLy.ly_Z.
  assert (HZ : length (if mrow inp =? 0 then RLy.ly_zero
                       else if RSy.rc (rt_mb inp) b =? 1 then RSy.synth (rt_mb inp) b (rt_nb inp)
                       else RLy.ly_zero) = 32%nat).
  { destruct (mrow inp =? 0); [reflexivity|].
    destruct (RSy.rc (rt_mb inp) b =? 1); [|reflexivity].
    apply RSyL.rs_synth_len. apply r8_row_len. }
  destruct (b <=? 1); [apply RFinL.rcf_stamp32_len; exact HZ | exact HZ].
Qed.

(* n_b <> 0: E(b), 124 <= n_b <= 1492, and F_b has n_b bytes. *)
Lemma r8_rtn : forall inp b, rt_n inp b <> 0 ->
  rt_E inp b = true /\ 124 <= rt_n inp b <= 1492 /\ length (rt_F inp b) = Z.to_nat (rt_n inp b).
Proof.
  intros inp b H. unfold rt_n in *. destruct (rt_E inp b) eqn:E; [|congruence].
  pose proof E as E'. unfold rt_E, RBA.ba_E in E'. apply andb_true_iff in E' as [Ew _].
  destruct (REmL.em_wok_range _ Ew) as [R _].
  split; [reflexivity|]. split; [lia|].
  unfold rt_F, REm.em_fr, REm.em_hdr, box6. unfold rt_n. rewrite E.
  rewrite !length_app, OUR_length, length_map, r8_rtX_len, repeat_length. cbn [length]. lia.
Qed.

Lemma r8_rec_len : forall inp (b : nat), (b <= 6)%nat ->
  length (RID inp b) = 38%nat /\ length (RFG inp b) = 72%nat.
Proof.
  intros inp b Hb.
  assert (E : (b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6)%nat) by lia.
  destruct E as [->|[->|[->|[->|[->|[->| ->]]]]]]; a_rows inp; a_fin.
Qed.

(* ---- The image's four LOAD segments map, page-rounded, one run of pages: the last one alone covers
   [2^21, GT). So an address of that range lies on an image page, and a heap block (off the image's pages, at or
   above 2^21) lies at or above GT. ---- *)
Definition r8_pages_b : bool :=
  existsb (fun s => (Z.of_N (seg_base s) / 4096 * 4096 <=? 2 ^ 21) &&
                    (0x5fe000 <=? (Z.of_N (seg_base s) + Z.of_N (seg_size s) + 4095) / 4096 * 4096)) rsegs.

Lemma r8_pages_true : r8_pages_b = true.
Proof. vm_compute. reflexivity. Qed.

Lemma r8_on_page : forall a, 2 ^ 21 <= a < 0x5fe000 -> ACw.a_on_img_page a.
Proof.
  intros a Ha. pose proof r8_pages_true as H. unfold r8_pages_b in H.
  apply existsb_exists in H. destruct H as (s & Hin & Hs).
  apply andb_prop in Hs. destruct Hs as (H1 & H2). apply Z.leb_le in H1. apply Z.leb_le in H2.
  exists s. split; [exact Hin|]. lia.
Qed.

(* ---- Byte and cell helpers ---- *)

(* Off the image a writable byte is a raw byte of the overlay, so it reads: wview has no segment to fall back on. *)
Lemma r8_rd_of_w : forall (m : word -> option byte) (a : Z), 0 <= a < 2 ^ 64 ->
  ~ ACw.a_in_img a -> writable_at rsegs m a -> exists bb, mrd rsegs m (wa a) = Some bb.
Proof.
  intros m a Ha Hni Hw.
  assert (Efs : find_segment rsegs (bv_unsigned (wa a)) 1 = None).
  { destruct (find_segment rsegs (bv_unsigned (wa a)) 1) as [s|] eqn:Es; [|reflexivity].
    exfalso. apply Hni. destruct (KindBGlue.kb_find_segment _ _ _ _ Es) as (Hin & Hlo & Hhi).
    rewrite wa_unsigned in Hlo, Hhi by lia.
    exists s. split; [exact Hin|]. lia. }
  destruct (m (wa a)) as [bb|] eqn:E.
  - exists bb. unfold mrd. rewrite E. reflexivity.
  - exfalso. apply Hw. unfold wview. change (Z_to_bv 64 a) with (wa a). rewrite E, Efs. reflexivity.
Qed.

Lemma r8_wr_stk : forall m lo hi, stk rsegs m lo hi -> wr_at rsegs m lo (hi - lo).
Proof.
  intros m lo hi (H0 & H1 & H). split; [lia|]. split; [lia|]. intros i Hi. exact (proj1 (H (lo + i) ltac:(lia))).
Qed.

Lemma r8_rw_CB : forall m A l, bytes_at rsegs m A l -> wr_at rsegs m A (Z.of_nat (length l)) ->
  rw_cells rsegs m A [CB (length l) l].
Proof.
  intros m A l Hb Hw. split; [split|].
  - cbn [cells_wf cell_wf]. split; [reflexivity | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact Hw.
Qed.

Lemma r8_ro8 : forall m a v, bytes_at rsegs m a (le8 v) -> ro_cells rsegs m a [C8 v].
Proof.
  intros m a v H. split; [split; [exact I | exact I]|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact H.
Qed.

(* Two byte lists of one length at one address of one memory are equal. *)
Lemma r8_bytes_det : forall m a bs bs', bytes_at rsegs m a bs -> bytes_at rsegs m a bs' ->
  length bs = length bs' -> bs = bs'.
Proof.
  intros m a bs bs' H H' HL.
  exact (fl_bytes_eq [] m m a bs bs' H H' (LF.munch_refl [] m) HL (fun _ _ => I)).
Qed.

(* A one-block cell list at bytes the run does not write stays: its bytes by fl_bytes, writability by wmono. *)
Lemma r8_rwcb_keep : forall W m m' a n bs, rw_cells rsegs m a [CB n bs] -> LF.munch W m m' ->
  LF.wmono rsegs m m' -> (forall x, a <= x < a + Z.of_nat n -> LF.outside W x) -> rw_cells rsegs m' a [CB n bs].
Proof.
  intros W m m' a n bs ((Hwf & Hb) & (Hw0 & Hw1 & Hw)) MU WM HO.
  split; [split|].
  - exact Hwf.
  - eapply fl_bytes; [exact Hb | exact MU |].
    cbn [cells_bytes cbytes]. rewrite app_nil_r. destruct Hwf as (Hl & _). cbn [cell_wf] in Hl.
    rewrite Hl. exact HO.
  - split; [exact Hw0|]. split; [exact Hw1|]. intros i Hi. apply WM. exact (Hw i Hi).
Qed.

(* The spill base named by a spill at offset off < 416 is the register-9 value A of the cut. *)
Lemma r8_spill_A : forall (regs : bvmap 5 word) m off v A A',
  rg regs 9 A -> rg regs 9 A' -> q64 m (A' + off) v -> 0 <= A -> A + 416 <= 2 ^ 64 ->
  0 <= off -> off + 8 <= 416 -> A' = A.
Proof.
  intros regs m off v A A' HA HA' Hq H0 H1 Ho1 Ho2.
  pose proof (rg_eq64 regs 9 A' A HA' HA) as Hm.
  unfold q64 in Hq. destruct Hq as (Hq0 & Hq1 & _). rewrite length_le8 in Hq1.
  rewrite (Z.mod_small A) in Hm by lia.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  rewrite HP64 in *. revert Hm. Z.div_mod_to_equations. lia.
Qed.

(* A spill of the spill base A (register 9) is kept by a run that keeps register 9 and writes no byte of the
   416-byte save area [A, A + 416). *)
Lemma r8_spill_keep : forall (regs regs' : bvmap 5 word) (m m' : word -> option byte) W A off v,
  spill regs m off v -> rg regs 9 A -> 0 <= A -> A + 416 <= 2 ^ 64 -> 0 <= off -> off + 8 <= 416 ->
  getr regs' 9 = getr regs 9 -> LF.munch W m m' -> (forall x, A <= x < A + 416 -> LF.outside W x) ->
  spill regs' m' off v.
Proof.
  intros regs regs' m m' W A off v (A1 & HA1 & Hq) HA H0 H416 Hoff Hoff8 E9 MU HO.
  assert (E : A1 = A) by exact (r8_spill_A regs m off v A A1 HA HA1 Hq H0 H416 Hoff Hoff8).
  subst A1. exists A. split; [unfold rg in *; rewrite E9; exact HA|].
  unfold q64 in *. eapply fl_bytes; [exact Hq | exact MU |]. rewrite length_le8.
  intros x Hx. apply HO. lia.
Qed.

(* FSREC (the side-arm FakeStack frame record) moves across a run that writes no byte below GT (the tp word is an
   image-area word below GT) and no byte of the FakeStack [FS, FS + FS_SIZE) (the class-6 flag byte and the slot's
   last word fr + 4088 are inside it). The R8 write set is the fresh heap block, whose bytes a_laws_blocks puts
   outside the FakeStack, and the callee window, above stklo >= FS + FS_SIZE. *)
Lemma r8_fsrec : forall mem mem' W fr, FSREC fr mem -> LF.munch W mem mem' ->
  (forall x, 0 <= x < ACw.GT -> LF.outside W x) ->
  (forall x, ACw.a_in_fs ACw.ASYMS mem x -> LF.outside W x) ->
  FSREC fr mem'.
Proof.
  intros mem mem' W fr (FS & j & Htp & HFSr & Hj & Hfr & Hflag & Htail) MU Hlow Hinfs.
  assert (HB6 : SMC.fs_B 6 = 4096) by reflexivity.
  assert (HM6 : SMC.fs_M 6 = 256) by reflexivity.
  assert (Hfl : SMC.fs_flag FS 6 j = FS + 36352 + j) by (unfold SMC.fs_flag; cbn; lia).
  assert (HFSZ : ACw.FS_SIZE = 11571200) by reflexivity.
  assert (Hfrv : fr = FS + 6328320 + j * 4096) by (rewrite Hfr; unfold SMC.fs_frame, SMC.fs_B; cbn; lia).
  rewrite HM6 in Hj.
  assert (Hin : forall x, FS <= x < FS + ACw.FS_SIZE -> LF.outside W x).
  { intros x Hx. apply Hinfs. exists FS. split; [exact HFSr|]. split; [exact Htp | exact Hx]. }
  exists FS, j.
  split.
  { intros k Hk.
    assert (Hx : 0 <= ACw.as_tp ACw.ASYMS + Z.of_nat k < 6283264)
      by (unfold ACw.as_tp, ACw.ASYMS; cbn; lia).
    assert (Hm : mem' (Z_to_bv 64 (ACw.as_tp ACw.ASYMS + Z.of_nat k))
                 = mem (Z_to_bv 64 (ACw.as_tp ACw.ASYMS + Z.of_nat k))).
    { apply MU. rewrite MState.unsigned_lit by lia. apply Hlow. unfold ACw.GT. lia. }
    unfold mbyte. rewrite Hm. exact (Htp k Hk). }
  split; [exact HFSr|].
  split; [rewrite HM6; exact Hj|].
  split; [exact Hfr|].
  split.
  { eapply fl_bytes; [exact Hflag | exact MU |]. cbn [length]. intros x Hx. apply Hin. lia. }
  { eapply fl_bytes; [exact Htail | exact MU |]. rewrite length_le8. intros x Hx. apply Hin.
    rewrite HB6 in Hx. lia. }
Qed.

(* The official push-13 bodies of Inv_A81640_at (entry) and Inv_A81658_at (exit), verbatim; the cuts are these
   bodies /\ X81640 resp. /\ X81658. *)
Definition r8_in (g : ghost) (b : nat) (phi fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  g_n g < 2 ^ 26 /\ (b <= 6)%nat /\ rnb g b <> 0 /\
    a0v regs phi /\ HB m phi (rnb g b) /\ rg regs 18 (rnb g b) /\ spill regs m 128 (fr + 544) /\
    addressable m (fr + 544) (rnb g b) /\
    (exists src, bytes_at rsegs m (fr + 544) src /\ Z.of_nat (length src) = rnb g b) /\
    rg regs 23 (Z.of_nat b) /\ OURb g fr m /\ OUTA fr m /\ CUR g 7 regs /\
    spill regs m 112 (mrow (g_in g)) /\ PRO g fr regs m /\
    spill regs m 104 0x21140 /\ spill regs m 96 0x1234 /\ spill regs m 64 0xe38f0000 /\
    spill regs m 144 (fr + 2688) /\ spill regs m 192 (fr + 2768) /\
    (exists idb, rw_cells rsegs m (fr + 2688) [CB 38 idb]) /\ (exists junk, rw_cells rsegs m (fr + 2768) [CB 72 junk]) /\
    spill regs m 280 (fr + 3040) /\ spill regs m 240 (fr + 3056) /\
    (exists jy, rw_cells rsegs m (fr + 3040) [CB 1 jy]) /\ (exists junk, rw_cells rsegs m (fr + 3056) [CB 32 junk]) /\
    spill regs m 152 (Sfr fr + 68) /\ rg regs 21 (fr + 2176) /\
    addressable m (fr + 2176) 38.

Definition r8_out (g : ghost) (b : nat) (phi fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  g_n g < 2 ^ 26 /\ (b <= 6)%nat /\ HB m phi (rnb g b) /\ rg regs 23 (Z.of_nat b) /\ OURb g fr m /\ OUTA fr m /\ CUR g 7 regs /\
    spill regs m 112 (mrow (g_in g)) /\ spill regs m 128 (fr + 544) /\ PRO g fr regs m /\
    spill regs m 104 0x21140 /\ spill regs m 96 0x1234 /\ spill regs m 64 0xe38f0000 /\
    spill regs m 144 (fr + 2688) /\ spill regs m 192 (fr + 2768) /\
    (exists idb, rw_cells rsegs m (fr + 2688) [CB 38 idb]) /\ (exists junk, rw_cells rsegs m (fr + 2768) [CB 72 junk]) /\
    spill regs m 280 (fr + 3040) /\ spill regs m 240 (fr + 3056) /\
    (exists jy, rw_cells rsegs m (fr + 3040) [CB 1 jy]) /\ (exists junk, rw_cells rsegs m (fr + 3056) [CB 32 junk]) /\
    spill regs m 152 (Sfr fr + 68) /\ rg regs 21 (fr + 2176) /\
    addressable m (fr + 2176) 38.

(* What the run keeps beyond the exit body, for X81658: s8 = Phi (0x81648), s2 = n_b, Phi holds the copied source
   bytes of out[] (any n_b-byte list read there), every byte list inside the frame, every spill [A + off] of the save
   area, and every addressable range (W is app memory, so no shadow byte changes). *)
Definition r8_keep (g : ghost) (b : nat) (phi fr : Z) (regs : bvmap 5 word) (mem : word -> option byte)
    (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
  rg regs' 24 phi /\ rg regs' 18 (rnb g b) /\
  (forall src, bytes_at rsegs mem (fr + 544) src -> Z.of_nat (length src) = rnb g b ->
     bytes_at rsegs mem' phi src) /\
  (forall a bs, fr <= a -> a + Z.of_nat (length bs) <= fr + FRAME_BYTES ->
     bytes_at rsegs mem a bs -> bytes_at rsegs mem' a bs) /\
  (forall off v, 0 <= off -> off + 8 <= 416 -> spill regs mem off v -> spill regs' mem' off v) /\
  (forall p n, addressable mem p n -> addressable mem' p n).

Section R8.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
(* The ending callee checked_memcpy (0x81654), taken on its contract (asan_memcpy_c.v), never on its code. *)
Hypothesis MCPY : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_memcpy_c.asan_memcpy_contract.

(* The run from the official entry body to the official exit body, with the keep facts. *)
Lemma r8_core : forall g b phi regs mem md fr,
  FRA B APIf ra g fr (hb1 phi (rnb g b)) regs mem md ->
  ENT APIf g (hb1 phi (rnb g b)) mem md ->
  r8_in g b phi fr regs mem ->
  (forall regs' mem' md',
     FRA B APIf ra g fr (hb1 phi (rnb g b)) regs' mem' md' ->
     ENT APIf g (hb1 phi (rnb g b)) mem' md' ->
     r8_out g b phi fr regs' mem' ->
     r8_keep g b phi fr regs mem regs' mem' ->
     SR (ms_segs B) (mkCfg (mkst regs' (Z_to_bv 64 0x81658) mem' (seg_rom (ms_segs B))) md') (Post B APIf ra g)) ->
  SR (ms_segs B) (mkCfg (mkst regs (Z_to_bv 64 0x81640) mem (seg_rom (ms_segs B))) md) (Post B APIf ra g).
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros g b phi regs mem md fr HFRA HENT HP Hk.
  pose proof (proj1 FF) as SEGS.
  pose proof HP as (Hgn & Hb6 & Hnz & Ha0 & HHB & Hr18 & H128 & HADs & Hsrcx & Hr23 & HOUR & HOUTA & HCUR &
    H112 & HPRO & H104 & H96 & H64 & H144 & H208 & HRW38 & HRW72 & H280 & H240 & HRW1 & HRW32 &
    H152 & Hr21 & HAD38).
  destruct Hsrcx as (src & Hsrcb & Hsrcl).
  destruct (fra_win B APIf ra g fr (hb1 phi (rnb g b)) regs mem md HFRA) as (Hwlo & Hstkw).
  destruct (fra_frame B APIf ra g fr (hb1 phi (rnb g b)) regs mem md HFRA) as (Hplace & HfrA & HfsS & Hfrw).
  destruct (fra_app B APIf ra g fr (hb1 phi (rnb g b)) regs mem md HFRA) as (HGTfr & Happ).
  pose proof HFRA as HFRA0.
  destruct HFRA0 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (ACw.aa_laws ACw.ASYMS AsanRTInv.RT (APIf rc)) as ALAWS.
  pose proof (ACw.a_laws_stack_high _ _ _ _ _ ALAWS (hb1 phi (rnb g b) ++ g_H g) mem md HAH) as Hhigh.
  assert (HSS : AFw.SLOT_STACK = 1048576) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (HKm : MCC.ASAN_MEMCPY_K = 2224) by reflexivity.
  assert (HGTv : ACw.GT = 6283264) by reflexivity.
  assert (HHMv : HIGHMEM_BEG = 17594333495296) by reflexivity.
  assert (HAEv : APPMEM_END = 140737488355328) by reflexivity.
  assert (HLMv : LOWMEM_END = 2147450880) by reflexivity.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HP40 : 2 ^ 40 = 1099511627776) by reflexivity.
  assert (HFSZ : ACw.FS_SIZE = 11571200) by reflexivity.
  rewrite Haspz in Hwlo, Hstkw, Hplace.
  pose proof (Hplace 2224 ltac:(lia)) as Hsep.
  assert (HA64 : 0 <= A < 2 ^ 64) by (pose proof Hwin as (Hw0 & Hw1 & _); lia).
  assert (Hfrhi : fr + FRAME_BYTES <= APPMEM_END).
  { pose proof (Happ (fr + FRAME_BYTES - 1) ltac:(lia)) as X. unfold app_mem in X. lia. }
  assert (HA9 : forall A0, getr regs 9 = Z_to_bv 64 A0 -> 0 <= A0 < 2 ^ 64 -> A0 = A).
  { intros A0 HA0 HA0r. pose proof (rg_eq64 regs 9 A0 A HA0 Hr9) as Hm.
    rewrite !Z.mod_small in Hm by lia. exact Hm. }
  (* n_b: 124 <= n_b <= 1492, and the serialized box F_b has n_b bytes *)
  destruct (r8_rtn (g_in g) (Z.of_nat b) Hnz) as (_ & HNr & _).
  change (rt_n (g_in g) (Z.of_nat b)) with (rnb g b) in HNr.
  (* the fresh block (Phi, n_b) of the cut's hb *)
  assert (HInblk : In (phi, rnb g b) (hb1 phi (rnb g b) ++ g_H g)) by (unfold hb1; cbn [app]; left; reflexivity).
  destruct (ACw.a_laws_blocks _ _ _ _ _ ALAWS (hb1 phi (rnb g b) ++ g_H g) mem md phi (rnb g b) HAH HInblk)
    as (Hp16 & Hp4096 & Hpstklo & HEDd & Hblkb).
  pose proof (ACw.a_laws_block_high _ _ _ _ _ ALAWS (hb1 phi (rnb g b) ++ g_H g) mem md phi (rnb g b) HAH HInblk)
    as Hp21.
  assert (HGTphi : ACw.GT <= phi).
  { destruct (Z_lt_le_dec phi 0x5fe000) as [Hlt|Hge]; [|lia].
    exfalso. destruct (Hblkb phi ltac:(lia)) as (_ & _ & _ & Hpg & _).
    apply Hpg. apply r8_on_page. lia. }
  (* the block is apart from the frame on both arms *)
  assert (Hfrdj : forall x, fr <= x < fr + FRAME_BYTES -> ~ (phi <= x < phi + rnb g b)).
  { intros x Hx Hin. destruct (Hblkb x Hin) as (_ & _ & _ & _ & Hfsx).
    destruct Hloc as [[_ [_ Hreal]] | [_ [_ [Hfs _]]]].
    - pose proof (Hreal x Hx) as Hr. lia.
    - apply Hfsx. exact (Hfs x Hx). }
  (* the write set W = [(Phi, Phi + n_b); (sp - 2224, sp)] and what lies outside it *)
  assert (Hout : forall x, ~ (phi <= x < phi + rnb g b) -> ~ (sp - MCC.ASAN_MEMCPY_K <= x < sp) ->
            LF.outside [(phi, phi + rnb g b); (sp - MCC.ASAN_MEMCPY_K, sp)] x).
  { intros x H1 H2. cbn [LF.outside]. split; [exact H1 | split; [exact H2 | exact I]]. }
  assert (Hout_napp : forall x, ~ app_mem x -> LF.outside [(phi, phi + rnb g b); (sp - MCC.ASAN_MEMCPY_K, sp)] x).
  { intros x Hx. apply Hout.
    - intros Hin. apply Hx. exact (proj1 (Hblkb x Hin)).
    - intros Hin. apply Hx. unfold app_mem. right. lia. }
  assert (Hfrout : forall x, fr <= x < fr + FRAME_BYTES ->
            LF.outside [(phi, phi + rnb g b); (sp - MCC.ASAN_MEMCPY_K, sp)] x).
  { intros x Hx. apply Hout; [exact (Hfrdj x Hx) | lia]. }
  assert (HAout : forall x, A <= x < A + 416 ->
            LF.outside [(phi, phi + rnb g b); (sp - MCC.ASAN_MEMCPY_K, sp)] x).
  { intros x Hx. apply Hout; lia. }
  assert (HAW : all_app [(phi, phi + rnb g b); (sp - MCC.ASAN_MEMCPY_K, sp)]).
  { cbn [all_app]. split; [intros a Ha; exact (proj1 (Hblkb a Ha))|].
    split; [intros a Ha; unfold app_mem; right; lia | exact I]. }
  (* the memcpy premises *)
  assert (Hphi0 : 0 < phi < 2 ^ 64) by lia.
  assert (HphiN : phi + rnb g b <= 2 ^ 64) by lia.
  assert (HSb : 0 <= fr + 544 < 2 ^ 64) by lia.
  assert (HN0 : 0 <= rnb g b) by lia.
  assert (Hspb : 0 <= sp < 2 ^ 64) by lia.
  assert (HLsrc : length src = Z.to_nat (rnb g b)) by lia.
  assert (RO : ro_cells rsegs mem (A + 128) [C8 (Z_to_bv 64 (fr + 544))]).
  { pose proof H128 as (A2 & HA2 & Hq128).
    assert (E2 : A2 = A) by exact (r8_spill_A regs mem 128 (fr + 544) A A2 Hr9 HA2 Hq128 ltac:(lia) ltac:(lia)
                                    ltac:(lia) ltac:(lia)).
    subst A2. apply r8_ro8. exact Hq128. }
  assert (Hblkrd : forall a, phi <= a < phi + rnb g b -> exists bb, mrd rsegs mem (wa a) = Some bb).
  { intros a Ha. destruct (Hblkb a Ha) as (_ & Hw & Hni & _ & _). exact (r8_rd_of_w mem a ltac:(lia) Hni Hw). }
  assert (Hblkstk : stk rsegs mem phi (phi + rnb g b)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    split; [exact (proj1 (proj2 (Hblkb a Ha))) | exact (Hblkrd a Ha)]. }
  destruct (stk_bytes rsegs mem phi (phi + rnb g b) Hblkstk ltac:(lia)) as (junk & Hjl & Hjb).
  assert (RWd : rw_cells rsegs mem phi [CB (Z.to_nat (rnb g b)) junk]).
  { replace (Z.to_nat (rnb g b)) with (length junk) by lia. apply r8_rw_CB; [exact Hjb|].
    replace (Z.of_nat (length junk)) with (phi + rnb g b - phi) by lia.
    exact (r8_wr_stk mem _ _ Hblkstk). }
  assert (HAL : phi = fr + 544 \/ fr + 544 + rnb g b <= phi \/ phi + rnb g b <= fr + 544).
  { destruct (Z_le_gt_dec (fr + 544 + rnb g b) phi) as [H|H]; [right; left; lia|].
    destruct (Z_le_gt_dec (phi + rnb g b) (fr + 544)) as [H2|H2]; [right; right; lia|].
    exfalso. exact (Hfrdj (Z.max phi (fr + 544)) ltac:(lia) ltac:(lia)). }
  assert (HNb40 : rnb g b <= 2 ^ 40) by lia.
  assert (HszN : rnb g b <= ACw.a_size (rnb g b)) by (unfold ACw.a_size; lia).
  assert (ADm : addressable mem phi (rnb g b)).
  { replace phi with (phi + 0) by lia.
    exact (addressable_sub mem phi (ACw.a_size (rnb g b)) 0 (rnb g b) (proj2 HHB) ltac:(lia) ltac:(lia)
             ltac:(lia)). }
  assert (ES : end_in_app (fr + 544) (rnb g b)) by (unfold end_in_app; right; apply Happ; lia).
  assert (APP : rnb g b = 0 \/ app_mem (fr + 544 + 7) /\ app_mem (phi + 7)).
  { right. split; [apply Happ; lia | exact (proj1 (Hblkb (phi + 7) ltac:(lia)))]. }
  assert (HRTd : phi + rnb g b <= RT_LO \/ RT_HI <= phi) by (right; unfold RT_HI; lia).
  assert (HSEPd : phi + rnb g b <= sp - MCC.ASAN_MEMCPY_K \/ sp <= phi) by (left; lia).
  assert (HSEPs : fr + 544 + rnb g b <= sp - MCC.ASAN_MEMCPY_K \/ sp <= fr + 544) by lia.
  assert (HLOw : sp - FN_STACK + MCC.ASAN_MEMCPY_K <= sp) by lia.
  assert (HHM : HIGHMEM_BEG <= sp - FN_STACK) by lia.
  assert (HAE : sp <= APPMEM_END) by lia.
  assert (HAC : asan_cells mem) by exact (AsanRTInv.RT_cells _ _ _ HRT).
  assert (HSW : shadow_rw mem) by exact (AsanRTInv.RT_shadow_rw _ _ _ HRT).
  assert (HROphi : forall i, 0 <= i < rnb g b -> ro_addr rsegs (wa (phi + i)) = false)
    by (intros i Hi; apply r8_ro_hi; lia).
  (* the run, lifted to SR *)
  rewrite SEGS.
  apply (sl_run_lib regs (Z_to_bv 64 0x81640) mem md
    (fun R pc' mem' => pc' = Z_to_bv 64 0x81658 /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\ getr R 8 = getr regs 8 /\
       getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\ getr R 21 = getr regs 21 /\
       getr R 22 = getr regs 22 /\ getr R 23 = getr regs 23 /\ getr R 25 = getr regs 25 /\
       getr R 26 = getr regs 26 /\ getr R 24 = Z_to_bv 64 phi /\ getr R 18 = Z_to_bv 64 (rnb g b) /\
       LF.munch [(phi, phi + rnb g b); (sp - MCC.ASAN_MEMCPY_K, sp)] mem mem' /\ LF.wmono rsegs mem mem' /\
       ro_agree rsegs mem' /\ stk rsegs mem' (sp - FN_STACK) sp /\
       rw_cells rsegs mem' phi [CB (Z.to_nat (rnb g b)) src])
    (Post B APIf ra g)).
  - exact Hhalt.
  - unfold Regs6ss.mkR_of. eapply evt_mono.
    + apply (r8_evt MCPY) with (spv := sp) (A := A) (S := fr + 544) (N := rnb g b) (phi := phi)
        (lo := sp - FN_STACK) (src := src) (junk := junk).
      all: try assumption.
    + intros ms' (R & m' & Hms & P2 & P3 & P4 & P8 & P9 & P19 & P21 & P22 & P23 & P25 & P26 & P10 & P24 & P18 &
                  MUq & WMq & ROq & STq & ACq & SWq & RWq & HBq).
      exists R, (Z_to_bv 64 0x81658), m'. split; [exact Hms|].
      split; [reflexivity|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P8|].
      split; [exact P9|]. split; [exact P19|]. split; [exact P21|]. split; [exact P22|]. split; [exact P23|].
      split; [exact P25|]. split; [exact P26|]. split; [exact P24|]. split; [exact P18|].
      split; [exact MUq|]. split; [exact WMq|]. split; [exact ROq|]. split; [exact STq | exact RWq].
  - intros R pc' mem' regs'' md'
      (Hpc & K2 & K3 & K4 & K8 & K9 & K19 & K21 & K22 & K23 & K25 & K26 & K24 & K18 & MU & WM & HRO' & STq & RWq)
      Hreg Hmat.
    subst pc'.
    assert (E2 : getr regs'' 2 = getr regs 2) by (rewrite Hreg; exact K2).
    assert (E3 : getr regs'' 3 = getr regs 3) by (rewrite Hreg; exact K3).
    assert (E4 : getr regs'' 4 = getr regs 4) by (rewrite Hreg; exact K4).
    assert (E8 : getr regs'' 8 = getr regs 8) by (rewrite Hreg; exact K8).
    assert (E9 : getr regs'' 9 = getr regs 9) by (rewrite Hreg; exact K9).
    assert (E19 : getr regs'' 19 = getr regs 19) by (rewrite Hreg; exact K19).
    assert (E21 : getr regs'' 21 = getr regs 21) by (rewrite Hreg; exact K21).
    assert (E22 : getr regs'' 22 = getr regs 22) by (rewrite Hreg; exact K22).
    assert (E23 : getr regs'' 23 = getr regs 23) by (rewrite Hreg; exact K23).
    assert (E25 : getr regs'' 25 = getr regs 25) by (rewrite Hreg; exact K25).
    assert (E26 : getr regs'' 26 = getr regs 26) by (rewrite Hreg; exact K26).
    (* the run's munch in the UL engine's flavour, which sl_addr_keep / outa_run / ent_munch take *)
    pose proof (proj1 (fr_munch_ul _ _ _) MU) as MUu.
    (* AH, ownership and the stack bounds after the run: both write ranges are a_store_ok (the block is a block of
       hb ++ H, the callee window is at or above stklo) *)
    assert (Hwrit : forall x, 0 <= x < 2 ^ 64 -> writable_at rsegs mem x -> writable_at rsegs mem' x)
      by (intros x _ Hx; exact (WM (Z_to_bv 64 x) Hx)).
    assert (Hmc : forall x, 0 <= x < 2 ^ 64 ->
              ~ ACw.a_store_ok (hb1 phi (rnb g b) ++ g_H g)
                  (ACw.aa_stklo ACw.ASYMS AsanRTInv.RT (APIf rc) mem md) x ->
              mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
    { intros x Hx Hnok. apply MU. rewrite MState.unsigned_lit by exact Hx. apply Hout.
      - intros Hin. apply Hnok. left. exists phi, (rnb g b). split; [exact HInblk | lia].
      - intros Hin. apply Hnok. right; left. lia. }
    destruct (ACw.a_laws_store _ _ _ _ _ ALAWS (hb1 phi (rnb g b) ++ g_H g) mem mem' md HAH Hmc Hwrit)
      as (HAH' & HOWN' & HSTK' & HHI').
    (* the write set is rt_disjoint (every runtime cell is below GT) *)
    assert (HDJ : rt_disjoint [(phi, phi + rnb g b); (sp - MCC.ASAN_MEMCPY_K, sp)]).
    { unfold rt_disjoint. cbn [disjoint_from].
      unfold RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF, RT_TSDI, RT_TSDK, RT_PGSZ,
        RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB, RT_AGLOB_LEN.
      repeat split; left; lia. }
    (* the slot window after the run: outside W it is kept, the callee window is the post's stk *)
    assert (HWIN' : stk rsegs mem' (g_S g - AFw.SLOT_STACK) (g_S g)).
    { destruct (stk_split rsegs mem (g_S g - AFw.SLOT_STACK) (sp - FN_STACK) (g_S g) Hwin ltac:(lia))
        as (Hlo1 & Hrest).
      destruct (stk_split rsegs mem (sp - FN_STACK) sp (g_S g) Hrest ltac:(lia)) as (_ & Hhi1).
      assert (Hlo1' : stk rsegs mem' (g_S g - AFw.SLOT_STACK) (sp - FN_STACK)).
      { apply (stk_transport rsegs _ mem mem' _ _ Hlo1 MU WM). intros x Hx. left. apply Hout; lia. }
      assert (Hhi1' : stk rsegs mem' sp (g_S g)).
      { apply (stk_transport rsegs _ mem mem' _ _ Hhi1 MU WM). intros x Hx. left. apply Hout; lia. }
      exact (stk_merge rsegs mem' _ sp _ (stk_merge rsegs mem' _ (sp - FN_STACK) _ Hlo1' STq ltac:(lia))
               Hhi1' ltac:(lia)). }
    (* FSREC (side arm): the block is off the FakeStack and above GT, the window is above stklo *)
    assert (HFSR : FSREC fr mem -> FSREC fr mem').
    { intros Hf. apply (r8_fsrec mem mem' [(phi, phi + rnb g b); (sp - MCC.ASAN_MEMCPY_K, sp)] fr Hf MU).
      - intros x Hx. apply Hout; lia.
      - intros x Hfsx. pose proof Hfsx as (b0 & Hb0 & Hw0 & Hx0).
        destruct (ACw.a_laws_fs_place _ _ _ _ _ ALAWS (hb1 phi (rnb g b) ++ g_H g) mem md b0 HAH Hw0 Hb0)
          as (_ & Hend & _ & _).
        apply Hout; [|lia].
        intros Hin. destruct (Hblkb x Hin) as (_ & _ & _ & _ & Hnfs). exact (Hnfs Hfsx). }
    (* FRA at mem' md, then at md' *)
    assert (HFRAm : FRA B APIf ra g fr (hb1 phi (rnb g b)) regs'' mem' md).
    { apply (sl_fr_cl B APIf ra empty FF g fr (hb1 phi (rnb g b)) regs regs'' mem mem' md
               [(phi, phi + rnb g b); (sp - MCC.ASAN_MEMCPY_K, sp)] HFRA MU WM HRO' HAW HDJ HAH' HSTK').
      - intros x Hx. apply Hout; lia.
      - intros x Hx. apply Hfrout. lia.
      - intros A0 HA0 HA0r x Hx. rewrite (HA9 A0 HA0 HA0r) in Hx. apply HAout. lia.
      - intros x Hx. apply Hout; lia.
      - intros x Hx. apply Hout_napp. unfold Sfr, shadow_addr, ASAN_K in Hx.
        pose proof (Z.div_mod fr 8 ltac:(lia)). pose proof (Z.mod_pos_bound fr 8 ltac:(lia)).
        unfold app_mem. lia.
      - intros A0 HA0 HA0r x Hx. rewrite (HA9 A0 HA0 HA0r) in Hx. apply HAout. lia.
      - exact HWIN'.
      - exact HFSR.
      - exact E2.
      - exact E3.
      - exact E4.
      - exact E8.
      - exact E9.
      - exact E19.
      - exact E26. }
    assert (HFRA' : FRA B APIf ra g fr (hb1 phi (rnb g b)) regs'' mem' md').
    { apply (sl_fra_move B APIf ra g fr (hb1 phi (rnb g b)) regs'' regs'' mem' md md' HFRAm);
        try reflexivity. exact Hmat. }
    (* ENT across the run: W holds no entry-block byte (a_laws_disjoint; both below stklo), no image byte (below
       GT), no byte at or above S, and no shadow byte (W is app memory) *)
    assert (HKEPT : forall x, ent_kept g x -> LF.outside [(phi, phi + rnb g b); (sp - MCC.ASAN_MEMCPY_K, sp)] x).
    { intros x Hkx.
      destruct Hkx as [(q & k & i & Hin & Hni & Hi & ->) | [Hik | [Habk | [(bq & Hor & ->) |
                       (q5 & k5 & i5 & Hin5 & _ & Hi5 & ->)]]]].
      - pose proof (ACw.a_laws_disjoint _ _ _ _ _ ALAWS [] (g_H g) mem md phi (rnb g b) q k HAH Hin) as Hdj.
        destruct (ACw.a_laws_blocks _ _ _ _ _ ALAWS (hb1 phi (rnb g b) ++ g_H g) mem md q k HAH
                    (in_or_app _ _ _ (or_intror Hin))) as (_ & _ & Hqk & _ & _).
        apply Hout; lia.
      - pose proof (img_below_GT x Hik) as Hxg. apply Hout; lia.
      - apply Hout; lia.
      - assert (Happb : app_mem bq).
        { destruct Hor as [Hib|Hrb].
          - pose proof (img_below_GT bq Hib) as Hbg. unfold app_mem. left. lia.
          - unfold app_mem. right. lia. }
        apply Hout_napp. intro Hx. exact (app_not_shadow _ Hx (shadow_of_app bq Happb)).
      - (* frame batch 2 item 9: the shadow byte of an entry block byte (app memory), so no app byte *)
        destruct (ACw.a_laws_blocks _ _ _ _ _ ALAWS (hb1 phi (rnb g b) ++ g_H g) mem md q5 k5 HAH
                    (in_or_app _ _ _ (or_intror Hin5))) as (_ & _ & _ & _ & Hall5).
        destruct (Hall5 (q5 + i5) ltac:(lia)) as (Happq5 & _).
        apply Hout_napp. intro Hx. exact (app_not_shadow _ Hx (shadow_of_app (q5 + i5) Happq5)). }
    assert (HENT' : ENT APIf g (hb1 phi (rnb g b)) mem' md).
    { eapply ent_munch;
        [exact HENT | exact HAH | apply (proj1 (fr_munch_ul _ _ _)); exact MU |
         intros x Hx; apply (proj2 (fr_outside_lib _ _)); exact (HKEPT x Hx) | exact HSTK' | exact HHI' |].
      intros a _ Ho. exact (proj2 (HOWN' a) Ho). }
    assert (HENT'' : ENT APIf g (hb1 phi (rnb g b)) mem' md').
    { eapply ent_mat; [exact HENT' | exact Hmat]. }
    (* the keeps *)
    assert (KSP : forall off v, 0 <= off -> off + 8 <= 416 -> spill regs mem off v -> spill regs'' mem' off v).
    { intros off v Ho1 Ho2 Hs.
      exact (r8_spill_keep regs regs'' mem mem' _ A off v Hs Hr9 ltac:(lia) ltac:(lia) Ho1 Ho2 E9 MU HAout). }
    assert (KAD : forall p n, addressable mem p n -> addressable mem' p n)
      by (intros p n Hpn; exact (sl_addr_keep mem mem' _ p n Hpn MUu HAW)).
    assert (KFR : forall a bs, fr <= a -> a + Z.of_nat (length bs) <= fr + FRAME_BYTES ->
              bytes_at rsegs mem a bs -> bytes_at rsegs mem' a bs).
    { intros a bs Ha Hab Hb. eapply fl_bytes; [exact Hb | exact MU |]. intros x Hx. apply Hfrout. lia. }
    (* the input block (an entry block of g_H when n > 0): apart from the fresh block (a_laws_disjoint) and below
       stklo <= sp - FN_STACK, so apart from the callee window *)
    assert (KIN : bytes_at rsegs mem (g_p g) (g_in g) -> (0 < g_n g -> In (g_p g, g_n g) (g_H g)) ->
              bytes_at rsegs mem' (g_p g) (g_in g)).
    { intros Hb Hin. eapply fl_bytes; [exact Hb | exact MU |]. intros x Hx.
      rewrite <- g_n_len in Hx.
      specialize (Hin ltac:(lia)).
      pose proof (ACw.a_laws_disjoint _ _ _ _ _ ALAWS [] (g_H g) mem md phi (rnb g b) (g_p g) (g_n g) HAH Hin)
        as Hdj.
      destruct (ACw.a_laws_blocks _ _ _ _ _ ALAWS (hb1 phi (rnb g b) ++ g_H g) mem md (g_p g) (g_n g) HAH
                  (in_or_app _ _ _ (or_intror Hin))) as (_ & _ & Hqk & _ & _).
      apply Hout; lia. }
    rewrite <- SEGS. apply Hk.
    + exact HFRA'.
    + exact HENT''.
    + (* the official exit body *)
      split; [exact Hgn|]. split; [exact Hb6|].
      split; [split; [exact (proj1 HHB) | exact (KAD _ _ (proj2 HHB))]|].
      split; [unfold rg; rewrite E23; exact Hr23|].
      split; [unfold OURb; apply KFR; [lia | rewrite OUR_length; lia | exact HOUR]|].
      split; [exact (outa_run fr mem mem' _ HOUTA MUu HAW)|].
      split.
      { destruct HCUR as (Hc0 & Hc22 & Hc25).
        split; [exact Hc0|]. split; [unfold rg; rewrite E22; exact Hc22 | unfold rg; rewrite E25; exact Hc25]. }
      split; [exact (KSP 112 _ ltac:(lia) ltac:(lia) H112)|].
      split; [exact (KSP 128 _ ltac:(lia) ltac:(lia) H128)|].
      split.
      { destruct HPRO as (P40 & P120 & P136 & P160 & P168 & P176 & P200 & P248 & PA6 & PIN & PINB &
                          P184 & P256 & P264 & P272 & P32).
        split; [exact (KSP 40 _ ltac:(lia) ltac:(lia) P40)|].
        split; [exact (KSP 120 _ ltac:(lia) ltac:(lia) P120)|].
        split; [exact (KSP 136 _ ltac:(lia) ltac:(lia) P136)|].
        split; [exact (KSP 160 _ ltac:(lia) ltac:(lia) P160)|].
        split; [exact (KSP 168 _ ltac:(lia) ltac:(lia) P168)|].
        split; [exact (KSP 176 _ ltac:(lia) ltac:(lia) P176)|].
        split; [exact (KSP 208 _ ltac:(lia) ltac:(lia) P200)|].
        split; [exact (KSP 248 _ ltac:(lia) ltac:(lia) P248)|].
        split; [exact (KAD _ _ PA6)|].
        split; [apply KIN; [exact PIN | intros Hn; exact (proj1 (PINB Hn))]|].
        split.
        { intros Hn. destruct (PINB Hn) as (Hi & Ha). split; [exact Hi | exact (KAD _ _ Ha)]. }
        split; [exact (KSP 184 _ ltac:(lia) ltac:(lia) P184)|].
        split; [exact (KSP 256 _ ltac:(lia) ltac:(lia) P256)|].
        split; [exact (KSP 264 _ ltac:(lia) ltac:(lia) P264)|].
        split; [exact (KSP 272 _ ltac:(lia) ltac:(lia) P272)|].
        exact (KSP 32 _ ltac:(lia) ltac:(lia) P32). }
      split; [exact (KSP 104 _ ltac:(lia) ltac:(lia) H104)|].
      split; [exact (KSP 96 _ ltac:(lia) ltac:(lia) H96)|].
      split; [exact (KSP 64 _ ltac:(lia) ltac:(lia) H64)|].
      split; [exact (KSP 144 _ ltac:(lia) ltac:(lia) H144)|].
      split; [exact (KSP 192 _ ltac:(lia) ltac:(lia) H208)|].
      split.
      { destruct HRW38 as (idb & Hc). exists idb.
        apply (r8_rwcb_keep _ mem mem' _ _ _ Hc MU WM). intros x Hx. apply Hfrout. lia. }
      split.
      { destruct HRW72 as (jk & Hc). exists jk.
        apply (r8_rwcb_keep _ mem mem' _ _ _ Hc MU WM). intros x Hx. apply Hfrout. lia. }
      split; [exact (KSP 280 _ ltac:(lia) ltac:(lia) H280)|].
      split; [exact (KSP 240 _ ltac:(lia) ltac:(lia) H240)|].
      split.
      { destruct HRW1 as (jy & Hc). exists jy.
        apply (r8_rwcb_keep _ mem mem' _ _ _ Hc MU WM). intros x Hx. apply Hfrout. lia. }
      split.
      { destruct HRW32 as (jk & Hc). exists jk.
        apply (r8_rwcb_keep _ mem mem' _ _ _ Hc MU WM). intros x Hx. apply Hfrout. lia. }
      split; [exact (KSP 152 _ ltac:(lia) ltac:(lia) H152)|].
      split; [unfold rg; rewrite E21; exact Hr21|].
      exact (KAD _ _ HAD38).
    + (* r8_keep *)
      split; [unfold rg; rewrite Hreg; exact K24|].
      split; [unfold rg; rewrite Hreg; exact K18|].
      split.
      { intros src' Hs' Hl'.
        assert (Esrc : src' = src) by (apply (r8_bytes_det mem (fr + 544) src' src Hs' Hsrcb); lia).
        subst src'. destruct RWq as ((_ & Hb) & _). cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
        exact Hb. }
      split; [exact KFR|].
      split; [exact KSP | exact KAD].
Qed.

(* S_R8 on the push-10 official cuts. *)
Lemma seg_R8 : forall b : nat,
  Hat B APIf ra (Inv_A81658_at (fx := fx) B APIf ra) b -> Hat B APIf ra (Inv_A81640_at (fx := fx) B APIf ra) b.
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros b Hexit g c HInv.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & HP & HX).
  subst c.
  pose proof HP as (_ & Hb6 & Hnz & _).
  destruct HX as (HID & HFG & HF & HRXS).
  destruct (r8_rtn (g_in g) (Z.of_nat b) Hnz) as (_ & HNr & HLF).
  change (rt_n (g_in g) (Z.of_nat b)) with (rnb g b) in HNr, HLF.
  destruct (r8_rec_len (g_in g) b Hb6) as (HLID & HLFG).
  apply (r8_core g b phi regs mem md fr HFRA HENT HP).
  intros regs' mem' md' HFRA' HENT' HP' HK.
  pose proof HP' as (_ & _ & _ & H23' & HOUR' & _ & HCUR' & _).
  destruct HK as (K24 & K18 & Ksrc & Kfr & Ksp & Kad).
  apply Hexit. exists phi, regs', mem', md', fr.
  split; [reflexivity|]. split; [exact HFRA'|]. split; [exact HENT'|].
  split; [exact HP'|].
  split.
  - (* RF: the turn-b records kept, s8 = Phi, Phi's bytes = rt_F, s2 = n_b *)
    split; [|exact K18].
    split.
    + split; [exact Hb6|]. split; [exact HCUR'|]. split; [exact HOUR'|]. split; [exact H23'|].
      split.
      * unfold IDBr in *. apply Kfr; [lia | rewrite HLID; lia | exact HID].
      * unfold FGBr in *. apply Kfr; [lia | rewrite HLFG; lia | exact HFG].
    + split; [exact Hnz|]. split; [exact K24|].
      apply Ksrc; [exact HF | rewrite HLF; lia].
  - (* RXS: the spills and the fragment record's addressability *)
    destruct HRXS as (S48 & S56 & S88 & S80 & S72 & S16 & S8 & S192 & S216 & HA72).
    split; [exact (Ksp 48 _ ltac:(lia) ltac:(lia) S48)|].
    split; [exact (Ksp 56 _ ltac:(lia) ltac:(lia) S56)|].
    split; [exact (Ksp 88 _ ltac:(lia) ltac:(lia) S88)|].
    split; [exact (Ksp 80 _ ltac:(lia) ltac:(lia) S80)|].
    split; [exact (Ksp 72 _ ltac:(lia) ltac:(lia) S72)|].
    split; [exact (Ksp 8 _ ltac:(lia) ltac:(lia) S16)|].
    split; [exact (Ksp 0 _ ltac:(lia) ltac:(lia) S8)|].
    split; [exact (Ksp 200 _ ltac:(lia) ltac:(lia) S192)|].
    split; [exact (Ksp 216 _ ltac:(lia) ltac:(lia) S216)|].
    exact (Kad _ _ HA72).
Qed.

End R8.
