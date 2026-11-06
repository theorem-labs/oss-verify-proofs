(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names and numbers changed; 877 of its 987 lines of code are new or changed and 901 lines of the source are left out. *)
(* Segment R8 of fuzz_ctrl LLVMFuzzerTestOneInput (asan-ubsan, image B, libreac v1.9.0): [0x81764, 0x81778],
   6 instructions, cut Inv_B81764 -> cut Inv_B8177c (plan-asan-ubsan.md section 2, row R8; section 4, MCPY =
   checked_memcpy, 0x52164).
   rule 24: no function proved (a slot segment).  The code tests the fresh buffer Phi returned by wrapper_malloc
   (0x81764 bnez a0,0x8176c; the fall-through 0x81768 `j 0x82fa4` is the abort branch of section 1.5 row 6, shown
   not taken because the cut's HB gives Phi <> 0), keeps it in s4 (0x8176c mv s4,a0), reloads the serialized box
   address [A + 312] = fr + 544 (0x81770 ld a1,312(s1); spilled at 0x814a4/0x814a8), sets the count a2 = s2 = n_b
   (0x81774 mv a2,s2; v1.8 had s9) and calls checked_memcpy (MCPY@0x81778), which copies the n_b source bytes into
   Phi.  The range owns no instrumented shadow check of section 1.6 and no UBSan trap branch of section 1.7.

   r8_evt is the Lib-level run of the 6 instructions with the call taken on its lib/B contract asan_memcpy_c.v (a
   Section hypothesis, never its code); seg_R8 lifts it to the cuts.  The contract needs mem_inv, so the run is
   stepped on the normalized memory (MemNorm) and carried back to the real memory by evt_normalize +
   AsanLift.evt_SR_canon_lazy (r4_run), as in R3 / R4.  The write set is the heap block [Phi, Phi + n_b) and
   the callee's stack window [sp - 2224, sp); both are a_store_ok in BOTH frame arms (the block is a live block of
   H = hb1 Phi n_b ++ g_H g, the window is at or above stklo), so the AH re-derivation is one AC.a_laws_store, with
   no FakeStack case.  The frame, the frame shadow, the spills and the saved registers are outside the write set:
   the block is above GT (r8_on_page: every address of [2^21, GT) lies on an image page, and a block byte does
   not), below stklo (a_laws_blocks) and apart from the frame on both arms (real: the frame is at or above stklo;
   side: a block byte is never a_in_fs).

   The official Inv_B81764_at (SlotInv.v) carries the source window's shadow addressability that the
   checked_memcpy contract needs; everything else the contract asks of the destination (its cell, its bounds, its
   separations) is derived here from HB and the allocator laws.  ENT (the entry-state relation of the cut) moves
   across the run by ent_munch: the write set is the fresh block (a block of hb, apart from every entry block by
   a_laws_disjoint, below stklo) and the callee window (below sp), so it holds none of the addresses ENT reads.
   RBE (its 21 spills, PRA, [A + 152], [A + 112], [A + 160], out[] / identity record / our[] / row-name /
   fragment record addressability and the image bytes), s5 = 36, s2 = n_b and s11 = 32 are kept and s4 = Phi is
   set (the spills are at or above A >= sp, the image bytes below GT, and the write set is app memory, so no
   shadow byte changes: r8_RBE_keep; checked_memcpy keeps s2, s4, s5 and s11); FSREC moves by r8_fsrec; FRA's
   input facts move by fra_in_keep (the input block is an entry block below stklo, apart from the fresh block by
   a_laws_disjoint).

   Adopt 10 of a working branch: the entry carries out[]'s frame bytes rt_F (n_b of them, r8_rtn), the copy's source, so the
   copy's post gives the exit's frame bytes rt_F at Phi; the turn-b records lie in the frame, outside the write
   set, and are carried.  Both cuts are SlotInv.v's official Inv_B81764_at / Inv_B8177c_at: no side-stack package
   is carried (the R9 call site builds reac_ctrl_parse's from FRA with Tac_fsfree's fra_fp), and checked_memcpy
   takes none, so the segment has no local cut.  The r4_* helpers below are a local copy of seg R4's, re-fitted
   to the v1.9 FRA / PRA (Seg/R4.v is re-fitted elsewhere); R9 reads them from here. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require asan_memcpy_c.
Import ListNotations.
Open Scope Z_scope.

Module MCC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.asan_memcpy_c.

(* The malloc result is not zero, so 0x81764 takes the branch to 0x8176c and the abort edge 0x81768 is not taken. *)
Lemma r8_neqb0 : forall x, 0 < x < 2 ^ 64 -> negb (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 0)) = true.
Proof.
  intros x Hx. unfold bv_eqb. rewrite !MState.unsigned_lit by lia.
  rewrite (proj2 (Z.eqb_neq x 0)) by lia. reflexivity.
Qed.

(* ---- the run: bnez a0 ; mv s4,a0 ; ld a1,312(s1) ; mv a2,s2 ; jal checked_memcpy by its contract ---- *)
Lemma r8_evt : MCC.asan_memcpy_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv A S N phi lo : Z) (src junk : list byte),
    sp = Z_to_bv 64 spv -> s1 = Z_to_bv 64 A -> a0 = Z_to_bv 64 phi -> s2 = Z_to_bv 64 N ->
    0 < phi < 2 ^ 64 -> phi + N <= 2 ^ 64 -> 0 <= A < 2 ^ 64 -> A + 320 <= 2 ^ 64 -> 0 <= S < 2 ^ 64 -> 0 <= N ->
    0 <= spv < 2 ^ 64 ->
    ro_cells rsegs m (A + 312) [C8 (Z_to_bv 64 S)] ->
    bytes_at rsegs m S src -> length src = Z.to_nat N ->
    rw_cells rsegs m phi [CB (Z.to_nat N) junk] ->
    (phi = S \/ S + N <= phi \/ phi + N <= S) ->
    N <= 2 ^ 40 ->
    addressable m S N -> addressable m phi N -> end_in_app S N -> end_in_app phi N ->
    (N = 0 \/ app_mem (S + 7) /\ app_mem (phi + 7)) ->
    (phi + N <= RT_LO \/ RT_HI <= phi) ->
    (phi + N <= spv - 2224 \/ spv <= phi) -> (S + N <= spv - 2224 \/ spv <= S) ->
    stk rsegs m lo spv -> lo + 2224 <= spv -> HIGHMEM_BEG <= lo -> spv <= APPMEM_END ->
    asan_cells m -> shadow_rw m -> mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x8177c) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\ getr R 18 = s2 /\
         getr R 19 = s3 /\ getr R 20 = a0 /\ getr R 21 = s5 /\ getr R 22 = s6 /\ getr R 23 = s7 /\
         getr R 24 = s8 /\ getr R 25 = s9 /\ getr R 26 = s10 /\ getr R 27 = s11 /\
         munch [(phi, phi + N); (spv - 2224, spv)] m m' /\ wmono rsegs m m' /\
         mem_inv rsegs m' /\ stk rsegs m' lo spv /\ asan_cells m' /\ shadow_rw m' /\
         rw_cells rsegs m' phi [CB (Z.to_nat N) src] /\ bytes_at rsegs m' S src)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81764) fc None m (seg_rom rsegs)).
Proof.
  intros MCPY ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv A S N phi lo src junk -> -> -> -> Hphi0 HphiN HA HA320 HS HN Hspv
    RO HbS HLsrc RWd HAL HNb AS AD ES ED APP HRT HSEPd HSEPs ST HLO HHM HAE HAC HSW HMI.
  unfold MCC.asan_memcpy_contract in MCPY. cbv zeta in MCPY.
  assert (Ephi : bv_unsigned (Z_to_bv 64 phi) = phi) by (apply MState.unsigned_lit; lia).
  assert (EN : bv_unsigned (Z_to_bv 64 N) = N) by (apply MState.unsigned_lit; lia).
  assert (Esp : bv_unsigned (Z_to_bv 64 spv) = spv) by (apply MState.unsigned_lit; lia).
  assert (ESv : bv_unsigned (Z_to_bv 64 S) = S) by (apply MState.unsigned_lit; lia).
  step. if_true_by (r8_neqb0 phi ltac:(lia)).
  step. step. step. step.
  eapply evt_cut.
  { eapply MCPY with (src := src) (junk := junk) (lo := lo).
    - rewrite ?Ephi, ?EN, ?Esp, ?ESv. exact HbS.
    - rewrite ?Ephi, ?EN, ?Esp, ?ESv. exact HLsrc.
    - rewrite ?Ephi, ?EN, ?Esp, ?ESv. exact RWd.
    - rewrite ?Ephi, ?EN, ?Esp, ?ESv. exact HAL.
    - rewrite ?Ephi, ?EN, ?Esp, ?ESv. exact HNb.
    - rewrite ?Ephi, ?EN, ?Esp, ?ESv. exact AS.
    - rewrite ?Ephi, ?EN, ?Esp, ?ESv. exact AD.
    - rewrite ?Ephi, ?EN, ?Esp, ?ESv. exact ES.
    - rewrite ?Ephi, ?EN, ?Esp, ?ESv. exact ED.
    - rewrite ?Ephi, ?EN, ?Esp, ?ESv. exact APP.
    - rewrite ?Ephi, ?EN, ?Esp, ?ESv. exact HRT.
    - rewrite ?Ephi, ?EN, ?Esp, ?ESv. unfold MCC.ASAN_MEMCPY_K. exact HSEPd.
    - rewrite ?Ephi, ?EN, ?Esp, ?ESv. unfold MCC.ASAN_MEMCPY_K. exact HSEPs.
    - rewrite ?Ephi, ?EN, ?Esp, ?ESv. exact ST.
    - rewrite ?Ephi, ?EN, ?Esp, ?ESv. unfold MCC.ASAN_MEMCPY_K. exact HLO.
    - exact HHM.
    - rewrite ?Ephi, ?EN, ?Esp, ?ESv. exact HAE.
    - exact HAC.
    - exact HSW.
    - exact HMI. }
  intros ms' PO. unfold MCC.asan_memcpy_post in PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                  E & MU & WM & MI' & STc & RWc & HBc & AC' & SW').
  subst ms'.
  unfold MCC.ASAN_MEMCPY_K in MU.
  rewrite ?Ephi, ?EN, ?Esp in MU. rewrite ?Esp in STc. rewrite ?Ephi, ?EN in RWc. rewrite ?ESv in HBc.
  replace (ret_pc (Z_to_bv 64 0x8177c)) with (Z_to_bv 64 0x8177c)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply evt_done. do 2 eexists. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact STc|].
  split; [exact AC'|]. split; [exact SW'|]. split; [exact RWc | exact HBc].
Qed.

(* ---- byte, stack and cell helpers: a local copy of seg R4's (Seg/R4.v is re-fitted to v1.9 elsewhere); R9
   reads them from here ---- *)

Lemma r4_ba_rd : forall m A bs x, bytes_at rsegs m A bs -> A <= x < A + Z.of_nat (length bs) ->
  exists b, mrd rsegs m (wa x) = Some b.
Proof.
  intros m A bs x (H0 & H1 & H) Hx.
  pose proof (H (Z.to_nat (x - A)) ltac:(lia)) as E.
  replace (A + Z.of_nat (Z.to_nat (x - A))) with x in E by lia.
  destruct (nth_error bs (Z.to_nat (x - A))) as [b|] eqn:En; [exists b; exact E|].
  apply nth_error_None in En. lia.
Qed.

Lemma r4_addr_keep : forall W m m' p n, addressable m p n -> munch W m m' ->
  (forall i, 0 <= i < n -> outside W (shadow_addr (p + i))) -> addressable m' p n.
Proof.
  intros W m m' p n (H1 & H2 & H3 & H) MU HO. split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hk). split; [exact Ha|]. exists b. split; [|exact Hk].
  pose proof (in_shadow_range _ (shadow_of_app _ Ha)) as Hr.
  unfold mrd in *. rewrite (MU (wa (shadow_addr (p + i)))); [exact Hb|].
  rewrite wa_unsigned by lia. apply HO. exact Hi.
Qed.

Lemma r4_stk_tr : forall W m m' lo hi, stk rsegs m lo hi -> munch W m m' -> wmono rsegs m m' ->
  (forall x, lo <= x < hi -> outside W x \/ exists b, mrd rsegs m' (wa x) = Some b) -> stk rsegs m' lo hi.
Proof.
  intros W m m' lo hi (H1 & H2 & H) MU WM Hc. split; [lia|]. split; [lia|].
  intros a Ha. destruct (H a Ha) as (Hw & b & Hb). split; [exact (WM _ Hw)|].
  destruct (Hc a Ha) as [Ho|Hr]; [|exact Hr].
  exists b. unfold mrd in *. rewrite (MU (wa a)); [exact Hb|]. rewrite wa_unsigned by lia. exact Ho.
Qed.

Lemma r4_wr_stk : forall m lo hi, stk rsegs m lo hi -> wr_at rsegs m lo (hi - lo).
Proof. intros m lo hi (H0 & H1 & H). split; [lia|]. split; [lia|]. intros i Hi. exact (proj1 (H (lo + i) ltac:(lia))). Qed.

Lemma r4_rw_CB : forall m A l, bytes_at rsegs m A l -> wr_at rsegs m A (Z.of_nat (length l)) ->
  rw_cells rsegs m A [CB (length l) l].
Proof.
  intros m A l Hb Hw. split; [split|].
  - cbn [cells_wf cell_wf]. split; [reflexivity | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact Hw.
Qed.

(* A spilled word read by `ld`: its 8 bytes as one read-only cell. *)
Lemma r4_ro8 : forall m a v, bytes_at rsegs m a (le8 v) -> ro_cells rsegs m a [C8 v].
Proof. intros m a v H. split; [exact (conj I I)|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact H. Qed.

Lemma r4_out_dec : forall W x, outside W x \/ ~ outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros x; cbn [outside]; [left; exact I|].
  destruct (IH x) as [H|H]; [|right; tauto].
  destruct (Z_lt_le_dec x lo) as [H1|H1]; [left; split; [lia | exact H]|].
  destruct (Z_lt_le_dec x hi) as [H2|H2]; [right; intros (H3 & _); lia | left; split; [lia | exact H]].
Qed.

Lemma r4_not_out : forall lo1 hi1 lo2 hi2 x, ~ outside [(lo1, hi1); (lo2, hi2)] x ->
  lo1 <= x < hi1 \/ lo2 <= x < hi2.
Proof. intros lo1 hi1 lo2 hi2 x H. cbn [outside] in H. lia. Qed.

(* The start register map of the run, written with mkR so the engine reads it. *)
Lemma r4_mkR_of : forall regs, Regs6ss.mkR_of regs =
  mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7)
      (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14)
      (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
      (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28)
      (getr regs 29) (getr regs 30) (getr regs 31).
Proof. intros regs. reflexivity. Qed.

(* ---- seg_R8 on the cuts ---- *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import AsanRTInv PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcPortsLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcLay RcEmit RcEmitLib RcSynth RcSynthLib RcFinLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcIdentModel RcFrag RcFragLib reac_ctrl_build_as_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.FrameAPI.
Module LF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module RBAP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.reac_ctrl_build_as_c.
Open Scope Z_scope.

(* ---- frame-shadow, image and spill helpers (local copy of seg R4's, re-fitted to the v1.9 frame of
   FRAME_BYTES = 3136 bytes and FRAME_SHADOW = 392 shadow bytes, and to the v1.9 PRA) ---- *)

Lemma r4_sh8 : forall fr k, shadow_addr (fr + 8 * k) = Sfr fr + k.
Proof. intros fr k. unfold Sfr, shadow_addr. replace (fr + 8 * k) with (fr + k * 8) by lia. rewrite Z.div_add by lia. lia. Qed.

Lemma r4_sf8 : forall fr, fr mod 32 = 0 -> 8 * (Sfr fr - ASAN_K) = fr.
Proof. intros fr H. unfold Sfr, shadow_addr. Z.div_mod_to_equations. lia. Qed.

Lemma r4_fsh : forall fr k, (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) -> 0 <= k < FRAME_SHADOW ->
  in_shadow (Sfr fr + k).
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros fr k Happ Hk. rewrite <- r4_sh8. apply shadow_of_app. apply Happ. lia.
Qed.

(* The instrumented globals of the image lie below GT = 0x5fe000, so their shadow bytes are the first 785408 bytes
   of the low shadow. *)
Lemma r4_ag_ok : forallb (fun p => (0 <=? fst p) && (fst p + snd p <=? 0x5fe000)) AF.frame_AG = true.
Proof. vm_compute. reflexivity. Qed.

Lemma r4_ag_lo : forall a, in_globals AF.frame_AG a -> 0 <= a < 0x5fe000.
Proof.
  intros a (lo & len & Hin & Hr).
  pose proof (proj1 (forallb_forall _ _) r4_ag_ok (lo, len) Hin) as H. cbn [fst snd] in H.
  apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1, H2. lia.
Qed.

Lemma r4_sa_lo : forall a, 0 <= a < 0x5fe000 -> ASAN_K <= shadow_addr a < ASAN_K + 785408.
Proof. intros a Ha. unfold shadow_addr. Z.div_mod_to_equations. lia. Qed.

(* The spill base named by a spill conjunct is the A of register 9. *)
Lemma r4_spill_A : forall (regs : bvmap 5 word) m off v A A1,
  rg regs 9 A1 -> q64 m (A1 + off) v -> rg regs 9 A -> 0 <= A -> A + off + 8 <= 2 ^ 64 -> 0 <= off -> A1 = A.
Proof.
  intros regs m off v A A1 H1 Hq H2 HA0 HAe Hoff.
  unfold q64 in Hq. apply bytes_at_bound in Hq. rewrite length_le8 in Hq. change (Z.of_nat 8) with 8 in Hq.
  pose proof (rg_eq64 regs 9 A1 A H1 H2) as Hm. change (2 ^ 64) with 18446744073709551616 in *.
  Z.div_mod_to_equations. lia.
Qed.

(* PRA (the v1.9 frame-loop pointer spills, 11 conjuncts) is carried by any map that carries each of its
   spills. *)
Lemma r4_pra : forall fr (regs regs' : bvmap 5 word) m m',
  (forall off v, In off [136; 280; 168; 192; 200; 216; 104; 288; 296; 304] ->
     spill regs m off v -> spill regs' m' off v) ->
  PRA fr regs m -> PRA fr regs' m'.
Proof.
  intros fr regs regs' m m' K (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11). unfold PRA.
  split; [apply K; [cbn [In]; lia | exact H1]|]. split; [apply K; [cbn [In]; lia | exact H2]|].
  split; [apply K; [cbn [In]; lia | exact H3]|]. split; [apply K; [cbn [In]; lia | exact H4]|].
  split; [apply K; [cbn [In]; lia | exact H5]|]. split; [apply K; [cbn [In]; lia | exact H6]|].
  split; [apply K; [cbn [In]; lia | exact H7]|]. split; [apply K; [cbn [In]; lia | exact H8]|].
  split; [apply K; [cbn [In]; lia | exact H9]|]. split; [apply K; [cbn [In]; lia | exact H10]|].
  apply K; [cbn [In]; lia | exact H11].
Qed.

(* ---- the normalized memory: every address at or above GT is read-write in the image ---- *)

Lemma r4_wx : wx_apart rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma r4_img_top : forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 0x5fe000) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma r4_ro_false : forall x : word, 0x5fe000 <= bv_unsigned x -> Lib.Mem.ro_addr rsegs x = false.
Proof.
  intros x Hx. unfold Lib.Mem.ro_addr.
  destruct (find_segment rsegs (bv_unsigned x) 1) as [s|] eqn:E; [|reflexivity].
  destruct (KindBGlue.kb_find_segment _ _ _ _ E) as (Hin & Hlo & Hhi).
  pose proof (proj1 (forallb_forall _ _) r4_img_top s Hin) as Hs. cbv beta in Hs. apply Z.leb_le in Hs.
  pose proof (N2Z.is_nonneg (seg_size s)). exfalso. lia.
Qed.

Lemma r4_ro_wa : forall a, 0x5fe000 <= a < 2 ^ 64 -> Lib.Mem.ro_addr rsegs (wa a) = false.
Proof. intros a Ha. apply r4_ro_false. rewrite wa_unsigned by lia. lia. Qed.

Lemma r4_shadow_gt : forall a, in_shadow a -> 0x5fe000 <= a < 2 ^ 64.
Proof. intros a Ha. unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Ha. lia. Qed.

Lemma r4_srw_rel : forall m m0, mem_rel rsegs m m0 -> shadow_rw m -> shadow_rw m0.
Proof.
  intros m m0 HR H a Ha. destruct (H a Ha) as (Hw & b & Hb). pose proof (r4_shadow_gt a Ha) as Hr. split.
  - rewrite (wview_rel_rw rsegs m m0 (wa a) HR (r4_ro_wa a Hr)). exact Hw.
  - exists b. rewrite <- (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma r4_srw_back : forall m m0, mem_rel rsegs m m0 -> shadow_rw m0 -> shadow_rw m.
Proof.
  intros m m0 HR H a Ha. destruct (H a Ha) as (Hw & b & Hb). pose proof (r4_shadow_gt a Ha) as Hr. split.
  - rewrite <- (wview_rel_rw rsegs m m0 (wa a) HR (r4_ro_wa a Hr)). exact Hw.
  - exists b. rewrite (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma r4_stk_rel : forall m m0 lo hi, mem_rel rsegs m m0 -> 0x5fe000 <= lo -> stk rsegs m lo hi -> stk rsegs m0 lo hi.
Proof.
  intros m m0 lo hi HR Hlo (H1 & H2 & H). split; [lia|]. split; [lia|]. intros a Ha.
  destruct (H a Ha) as (Hw & b & Hb). split.
  - rewrite (wview_rel_rw rsegs m m0 (wa a) HR (r4_ro_wa a ltac:(lia))). exact Hw.
  - exists b. rewrite <- (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma r4_stk_back : forall m m0 lo hi, mem_rel rsegs m m0 -> 0x5fe000 <= lo -> stk rsegs m0 lo hi -> stk rsegs m lo hi.
Proof.
  intros m m0 lo hi HR Hlo (H1 & H2 & H). split; [lia|]. split; [lia|]. intros a Ha.
  destruct (H a Ha) as (Hw & b & Hb). split.
  - rewrite <- (wview_rel_rw rsegs m m0 (wa a) HR (r4_ro_wa a ltac:(lia))). exact Hw.
  - exists b. rewrite (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma r4_cells_rel : forall m m0, mem_rel rsegs m m0 -> asan_cells m -> asan_cells m0.
Proof.
  intros m m0 HR H. unfold asan_cells in *.
  assert (TB : forall a bs, bytes_at rsegs m a bs -> bytes_at rsegs m0 a bs)
    by (intros a bs Hb; exact (proj1 (bytes_at_rel rsegs m m0 a bs HR) Hb)).
  repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
  repeat match goal with |- _ /\ _ => split end; apply TB; assumption.
Qed.

(* addressable reads only shadow bytes through mrd, which mem_rel keeps. *)
Lemma r4_addr_rel : forall m m0 p n, mem_rel rsegs m m0 -> addressable m p n -> addressable m0 p n.
Proof.
  intros m m0 p n HR (H1 & H2 & H3 & H). split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hk). split; [exact Ha|]. exists b. split; [|exact Hk].
  rewrite <- (mrd_rel rsegs m m0 _ HR). exact Hb.
Qed.

(* ---- the run lemma: an evt on the normalized memory, lifted to SR on the real configuration ---- *)
Section Run.
Context {fx : FPState}.

Lemma r4_run : forall regs pc mem md (K : bvmap 5 word -> word -> (word -> option byte) -> Prop) (P : config -> Prop),
  m_halted md = None -> ro_agree rsegs mem ->
  evt rsegs (fun ms => exists R pc' m0', ms = MS R fp_regs pc' fp_csr None m0' (seg_rom rsegs) /\ K R pc' m0')
    (MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None (normalize rsegs mem) (seg_rom rsegs)) ->
  (forall R pc' m0' regs' m' md', K R pc' m0' -> (forall r, getr regs' r = getr R r) ->
     mem_rel rsegs m' m0' -> ro_same rsegs mem m' -> AsanLift.mat_le md md' ->
     SR rsegs (mkCfg (mkst regs' pc' m' (seg_rom rsegs)) md') P) ->
  SR rsegs (mkCfg (mkst regs pc mem (seg_rom rsegs)) md) P.
Proof.
  intros regs pc mem md K P Hh Hro HE HK.
  pose proof (evt_normalize rsegs _ (Regs6ss.mkR_of regs) fp_regs pc fp_csr None mem (seg_rom rsegs) r4_wx Hro HE)
    as HE'.
  eapply (AsanLift.evt_SR_canon_lazy rsegs (mkst regs pc mem (seg_rom rsegs)) _ md P); [exact HE' | exact Hh |].
  intros ms' md' (can & (s0 & (R & pc' & m0' & Es0 & HKR) & Hrel & Hsame) & Heq) Hmat.
  subst s0.
  destruct can as [cr cf cp cs cv cc cm co].
  destruct ms' as [regs' fr' pcv' svc' rv' fc' m' ro'].
  destruct Hrel as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
  destruct Heq as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hm & Hrom).
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom MS] in *.
  subst.
  apply (HK _ _ _ regs' _ md' HKR); [apply KindBGlue.kb_getr_eqv; exact HR | exact E8 | exact Hsame | exact Hmat].
Qed.

End Run.

Section R4h.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

(* FRA across a run whose write set W avoids the cells FRA reads outside the frame (low image, frame header, the
   spills [A + 40, A + 56) / [A + 336], the saved registers) and keeps every shadow byte readable (so
   RT_meta_write), given the new frame-shadow list, the run's heap invariant / stklo, the S-anchored window still
   backed, and the frame_AG globals still addressable (R4's r4_fra on the v1.9 FRA).  W may contain frame bytes,
   frame shadow bytes and the callee window. *)
Lemma r4_fra : forall g fr hb regs regs' mem mem' md W,
  FRA B APIf ra g fr hb regs mem md ->
  LF.munch W mem mem' -> LF.wmono rsegs mem mem' -> ro_agree rsegs mem' -> rt_disjoint W ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md ->
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md ->
  (forall a, in_shadow a -> exists b, mrd rsegs mem' (wa a) = Some b) ->
  (exists sh, bytes_at rsegs mem' (Sfr fr) sh /\ length sh = Z.to_nat FRAME_SHADOW) ->
  (forall x, 0 <= x < 6283264 -> LF.outside W x) ->
  (forall x, fr <= x < fr + 24 -> LF.outside W x) ->
  (forall x, bv_unsigned (getr regs 9) + 40 <= x < bv_unsigned (getr regs 9) + 56 -> LF.outside W x) ->
  (forall x, bv_unsigned (getr regs 9) + 336 <= x < bv_unsigned (getr regs 9) + 344 -> LF.outside W x) ->
  (forall x, g_S g - 104 <= x < g_S g -> LF.outside W x) ->
  (forall x, g_S g - AF.SLOT_STACK <= x < g_S g -> LF.outside W x \/ exists b, mrd rsegs mem' (wa x) = Some b) ->
  (forall a, in_globals AF.frame_AG a -> addressable mem' a 1) ->
  (forall a, g_S g - AF.SLOT_STACK <= a < g_S g -> ~ (fr <= a < fr + FRAME_BYTES) -> addressable mem' a 1) ->
  (FSREC fr mem -> FSREC fr mem') ->
  bytes_at rsegs mem' (g_p g) (g_in g) ->
  (0 < g_n g -> In (g_p g, g_n g) (g_H g) /\ addressable mem' (g_p g) (g_n g)) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  FRA B APIf ra g fr hb regs' mem' md.
Proof.
  intros g fr hb regs regs' mem mem' md W HFRA MU WM HRO HD HAH' HSTK HshR Hshnew HWlo HWhdr HWsel HWspill
    HWsaved HWwin HAG' HWA' HFSR HIN1' HIN2' E2 E3 E4 E8 E9 E19 E26.
  pose proof FF as (SEGS & _ & _ & _ & Hhead & Hlock & Hthr & _).
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HA64 : 0 <= A < 2 ^ 64).
  { unfold stk in Hwin. destruct Hwin as (Hw0 & Hw1 & _). lia. }
  assert (HbvA : bv_unsigned (getr regs 9) = A).
  { unfold rg in Hr9. rewrite Hr9. apply MState.unsigned_lit. exact HA64. }
  rewrite HbvA in HWsel, HWspill.
  assert (KBlo : forall (sg : list Segment) x, 0 <= x -> x < 6283264 -> mbyte sg mem' x = mbyte sg mem x).
  { intros sg x H0 H1. unfold mbyte. rewrite (MU (Z_to_bv 64 x)); [reflexivity|].
    rewrite MState.unsigned_lit by lia. exact (HWlo x ltac:(lia)). }
  exists A, sp, s5.
  split; [exact (AsanRTInv.RT_meta_write sp sp mem mem' md md W HRT MU WM HD HshR)|].
  split; [exact HAH'|].
  split; [exact HRO|].
  split.
  { destruct Hsn as (Hcse & Hohd & Hfd). split; [|split; [|exact Hfd]].
    - destruct Hcse as (Hthrm & Hlockm). split.
      + eapply YI14.val_mem_frame; [|exact Hthrm]. intros x Hx. apply KBlo.
        * lia.
        * rewrite Hthr in Hx. cbn in Hx. lia.
      + eapply YI14.val_mem_frame; [|exact Hlockm]. intros x Hx. apply KBlo.
        * lia.
        * rewrite Hlock in Hx. cbn in Hx. lia.
    - intros k Hk. rewrite KBlo.
      + exact (Hohd k Hk).
      + rewrite Hhead. lia.
      + rewrite Hhead. lia. }
  split; [exact Hhalt|].
  split.
  { intros a Hin. rewrite KBlo.
    - exact (Hgimg a Hin).
    - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
      destruct Hil as [E|[]]; injection E as <- <-; lia.
    - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
      destruct Hil as [E|[]]; injection E as <- <-; lia. }
  split; [rewrite E2; exact Hr2|].
  split; [exact Hspm|].
  split; [unfold AC.aspZ in *; rewrite E2; exact Haspz|].
  split; [rewrite HSTK; exact Hstklo|].
  split; [rewrite E4; exact Hr4|].
  split; [unfold rg in *; rewrite E8; exact Hr8|].
  split; [unfold rg in *; rewrite E9; exact Hr9|].
  split; [rewrite E3; exact Hr3|].
  split; [unfold rg in *; rewrite E19; exact Hr19|].
  split; [unfold rg in *; rewrite E26; exact Hr26|].
  split; [exact Hfrm|]. split; [exact Hs5|]. split; [exact HAm|]. split; [exact HAS|]. split; [exact Hspa|].
  split; [exact Hfa|]. split; [exact HA448|]. split; [exact HS4|]. split; [exact HAPP|].
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hspill | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWspill x ltac:(lia)). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hsel | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWsel x ltac:(lia)). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hfr56 | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWsel x ltac:(lia)). }
  split.
  { destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0 [Hfsb [Hfs Hfsrec]]]].
    - left. split; [exact H0|]. split; [exact Hspfr|].
      intros a Ha. rewrite HSTK. exact (Hreal a Ha).
    - right. split; [exact Hfr0|]. split; [|split].
      + intros FS Hw HFSr. apply (Hfsb FS); [| exact HFSr].
        intros k Hk. rewrite <- KBlo.
        * exact (Hw k Hk).
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
      + intros a Ha. destruct (Hfs a Ha) as (FSb & HFSr & Hw & Hlo & Hhi).
        exists FSb. split; [exact HFSr|]. split; [|split; [exact Hlo | exact Hhi]].
        intros k Hk. rewrite KBlo.
        * exact (Hw k Hk).
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
      + exact (HFSR Hfsrec). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr1 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWhdr. lia. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr2 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWhdr. lia. }
  split; [exact Hshnew|].
  split; [exact (r4_stk_tr W mem mem' _ _ Hwin MU WM HWwin)|].
  split.
  { eapply fl_bytes; [exact Hsaved | exact MU |]. intros x Hx.
    apply HWsaved. unfold saved_bytes in Hx. rewrite !length_app, !length_le8 in Hx. cbn in Hx. lia. }
  split; [intros a Ha; exact (WM (Z_to_bv 64 a) (Herrno a Ha))|].
  split; [exact HAG'|].
  split; [exact HWA'|].
  split; [exact HSHI1|].
  split; [exact HSHI2|].
  split; [exact HSHI3|].
  split; [exact Hhb|]. split; [exact Hlive|]. split; [exact HIN1' | exact HIN2'].
Qed.

End R4h.

(* The image's four LOAD segments map, page-rounded, one run of pages: the last one alone covers
   [2^21, GT).  So an address of that range lies on an image page. *)
Definition r8_pages_b : bool :=
  existsb (fun s => (Z.of_N (seg_base s) / 4096 * 4096 <=? 2 ^ 21) &&
                    (0x5fe000 <=? (Z.of_N (seg_base s) + Z.of_N (seg_size s) + 4095) / 4096 * 4096)) rsegs.

Lemma r8_pages_true : r8_pages_b = true.
Proof. vm_compute. reflexivity. Qed.

Lemma r8_on_page : forall a, 2 ^ 21 <= a < 0x5fe000 -> AC.a_on_img_page a.
Proof.
  intros a Ha. pose proof r8_pages_true as H. unfold r8_pages_b in H.
  apply existsb_exists in H. destruct H as (s & Hin & Hs).
  apply andb_prop in Hs. destruct Hs as (H1 & H2). apply Z.leb_le in H1. apply Z.leb_le in H2.
  exists s. split; [exact Hin|]. lia.
Qed.

(* Off the image a writable byte is a raw byte of the overlay, so it reads: wview has no segment to fall back on. *)
Lemma r8_rd_of_w : forall (m : word -> option byte) (a : Z), 0 <= a < 2 ^ 64 ->
  ~ AC.a_in_img a -> writable_at rsegs m a -> exists bb, mrd rsegs m (wa a) = Some bb.
Proof.
  intros m a Ha Hni Hw.
  assert (Efs : find_segment rsegs (bv_unsigned (wa a)) 1 = None).
  { destruct (find_segment rsegs (bv_unsigned (wa a)) 1) as [s|] eqn:Es; [|reflexivity].
    exfalso. apply Hni. destruct (KindBGlue.kb_find_segment _ _ _ _ Es) as (Hin & Hlo & Hhi).
    rewrite wa_unsigned in Hlo, Hhi by lia.
    exists s. split; [exact Hin|]. lia. }
  unfold YP09.writable_at in Hw. change (Z_to_bv 64 a) with (wa a) in Hw.
  destruct (m (wa a)) as [bb|] eqn:E.
  - exists bb. unfold mrd. rewrite E. reflexivity.
  - exfalso. apply Hw. unfold wview. rewrite E, Efs. reflexivity.
Qed.

(* A spill of the spill base A (register 9) is kept by a run that keeps register 9 and writes no byte of the
   448-byte save area [A, A + 448). *)
Lemma r8_spill_keep : forall (regs regs' : bvmap 5 word) (m m' : word -> option byte) W A off v,
  spill regs m off v -> rg regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 -> 0 <= off -> off + 8 <= 448 ->
  getr regs' 9 = getr regs 9 -> LF.munch W m m' -> (forall x, A <= x < A + 448 -> LF.outside W x) ->
  spill regs' m' off v.
Proof.
  intros regs regs' m m' W A off v (A1 & HA1 & Hq) HA H0 H448 Hoff Hoff8 E9 MU HO.
  assert (E : A1 = A) by (apply (r4_spill_A regs m off v A A1 HA1 Hq HA); lia).
  subst A1. exists A. split; [unfold rg in *; rewrite E9; exact HA|].
  unfold q64 in *. eapply fl_bytes; [exact Hq | exact MU |]. rewrite length_le8.
  intros x Hx. apply HO. lia.
Qed.

(* The catalogue row the round trip passes: one of the 11 rows of BOX_CATALOGUE (R6's r6_mrow_rng). *)
Lemma r8_mrow_rng : forall inp, CAT <= mrow inp <= CAT + 296 * 10.
Proof.
  intros inp. unfold mrow, istar, CAT_ROW, CAT_N, CAT.
  pose proof (Z.mod_pos_bound (mode inp / 2) 11 ltac:(lia)) as Hb. lia.
Qed.

Lemma r8_mb_len : forall inp, length (rt_mb inp) = 296%nat.
Proof.
  intros inp. unfold rt_mb, rowb, img.
  destruct (Lib.Image.image_bytes rsegs (CAT + CAT_ROW * istar inp) 296) eqn:Ei;
    [exact (Lib.Image.image_bytes_length rsegs 296 _ _ Ei) | apply repeat_length].
Qed.

(* ---- the model's lengths (R9's r9_rtX_len / r9_rtn, R6's r6_rid_len / r6_fgst_len / r6_rfg_len) ---- *)

Lemma r8_rtX_len : forall inp b, length (rt_X inp b) = 32%nat.
Proof.
  intros inp b. unfold rt_X, RBAP.ba_X, RcLay.ly_Z.
  assert (HZ : length (if mrow inp =? 0 then RcLay.ly_zero
                       else if RcSynth.rc (rt_mb inp) b =? 1 then RcSynth.synth (rt_mb inp) b (rt_nb inp)
                       else RcLay.ly_zero) = 32%nat).
  { destruct (mrow inp =? 0); [reflexivity|].
    destruct (RcSynth.rc (rt_mb inp) b =? 1); [|reflexivity].
    apply RcSynthLib.rs_synth_len. apply r8_mb_len. }
  destruct (b <=? 1); [apply RcFinLib.rcf_stamp32_len; exact HZ | exact HZ].
Qed.

(* n_b <> 0: 124 <= n_b <= 1492 and the emitted frame F_b has n_b bytes. *)
Lemma r8_rtn : forall inp b, rt_n inp b <> 0 ->
  124 <= rt_n inp b <= 1492 /\ length (rt_F inp b) = Z.to_nat (rt_n inp b).
Proof.
  intros inp b H. unfold rt_n in *. destruct (rt_E inp b) eqn:E; [|congruence].
  pose proof E as E'. unfold rt_E, RBAP.ba_E in E'. apply andb_true_iff in E' as [Ew _].
  destruct (RcEmitLib.em_wok_range _ Ew) as [R _].
  split; [lia|].
  unfold rt_F, RcEmit.em_fr, RcEmit.em_hdr, box6. unfold rt_n. rewrite E.
  rewrite !length_app, OUR_length, length_map, r8_rtX_len, repeat_length. cbn [length]. lia.
Qed.

(* The turn records: the identity record RID is 38 bytes and the fragment record RFG 72 bytes at every turn
   (ID0 / z72, kept by ING and by each fragment case), so both lie inside the frame. *)
Lemma r8_rid_len : forall inp b, length (RID inp b) = 38%nat.
Proof.
  intros inp b. unfold RID. induction b as [|b IH]; [reflexivity|].
  cbn [rt_st]. unfold rp_id, fg_id.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; cbn [fst];
    first [exact IH | apply RcIdentModel.ING_length; exact IH].
Qed.

Lemma r8_rtg_len : forall inp x, length (rt_g inp x) = 50%nat.
Proof. intros inp x. unfold rt_g, fr50. rewrite length_firstn, length_app, repeat_length. lia. Qed.

Lemma r8_fgst_len : forall len st g, length st = 72%nat -> length g = 50%nat -> length (fg_st len st g) = 72%nat.
Proof.
  intros len st g Hs Hg. unfold fg_st, fcls, RcFrag.fg_class. cbn [Z.eqb orb].
  destruct (RcFrag.fg_fr len g) eqn:Efr; cbn [negb fg_next]; [|exact Hs].
  assert (Hn : 1 <= RcFrag.fg_n g <= 22).
  { unfold RcFrag.fg_fr in Efr.
    apply andb_prop in Efr as [Efr _]. apply andb_prop in Efr as [Efr H22]. apply andb_prop in Efr as [_ H1].
    apply Z.leb_le in H22. apply Z.leb_le in H1. lia. }
  destruct (RcFrag.bat g 19 =? 1).
  - cbn [fg_next]. unfold RcFrag.fg_first, RcFrag.fg_body, RcFrag.bsl.
    rewrite !length_app, !length_firstn, !length_skipn, Hs, Hg. cbn [length]. lia.
  - destruct (RcFrag.fg_keep st g) eqn:Ek; cbn [negb].
    + assert (HT : RcFrag.fg_T st g <= 64).
      { unfold RcFrag.fg_keep in Ek. apply andb_prop in Ek as [_ HT]. apply Z.leb_le in HT. exact HT. }
      destruct (RcFrag.fg_close st g); cbn [negb fg_next];
        apply RcFragLib.rf_clear_length; apply RcFragLib.rf_fg_join_length; assumption.
    + cbn [fg_next]. apply RcFragLib.rf_clear_length. exact Hs.
Qed.

Lemma r8_rfg_len : forall inp b, length (RFG inp b) = 72%nat.
Proof.
  intros inp b. unfold RFG. induction b as [|b IH]; [reflexivity|].
  cbn [rt_st]. unfold rp_id, fg_id.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; cbn [snd];
    first [exact IH | apply r8_fgst_len; [exact IH | apply r8_rtg_len]].
Qed.

(* RBE across a run whose write set is app memory (so no shadow byte changes: out[], the identity record, our[],
   the row name and the fragment record stay addressable), misses the save area [A, A + 448) (the 21 spills, PRA,
   [A + 152], [A + 112] and [A + 160]) and misses everything below GT (the row table, the box bytes, the
   catalogue row and the row name are image bytes). *)
Lemma r8_RBE_keep : forall g fr regs regs' W m m' A,
  RBE g fr regs m -> LF.munch W m m' -> all_app W ->
  rg regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 -> getr regs' 9 = getr regs 9 ->
  (forall x, A <= x < A + 448 -> LF.outside W x) ->
  (forall x, 0 <= x < AC.GT -> LF.outside W x) ->
  RBE g fr regs' m'.
Proof.
  intros g fr regs regs' W m m' A H MU HAW H9 HA0 HA1 E9 HWA HWlo.
  destruct H as (S128 & S312 & S272 & S264 & S256 & S248 & S56 & S184 & S144 & S8 & S32 & S24 & S16 &
    S96 & S120 & S240 & S232 & S224 & S176 & S208 & S64 & HOUT & HA2176 & HNM & HOUR & HTBL & HBOX & HMROW &
    HPRA & S152 & S112 & HA2256 & S160).
  assert (K : forall off v, 0 <= off -> off + 8 <= 448 -> spill regs m off v -> spill regs' m' off v).
  { intros off v Ho0 Ho1 Hs. exact (r8_spill_keep regs regs' m m' W A off v Hs H9 HA0 HA1 Ho0 Ho1 E9 MU HWA). }
  assert (KB : forall a bs, 0 <= a -> a + Z.of_nat (length bs) <= AC.GT ->
            bytes_at rsegs m a bs -> bytes_at rsegs m' a bs).
  { intros a bs H0 H1 Hb. eapply fl_bytes; [exact Hb | exact MU |]. intros x Hx. apply HWlo. lia. }
  pose proof (r8_mrow_rng (g_in g)) as Hmr.
  assert (HGTv : AC.GT = 6283264) by reflexivity.
  assert (HCATv : CAT = 652832) by reflexivity.
  unfold RBE.
  do 21 (split; [apply K; [lia | lia | assumption]|]).
  split; [unfold OUTA in *; exact (sl_addr_keep m m' W (fr + 544) 1492 HOUT MU HAW)|].
  split; [exact (sl_addr_keep m m' W (fr + 2176) 38 HA2176 MU HAW)|].
  split.
  { intros Hc. destruct (HNM Hc) as (Hok & Hbytes & Haddr & Hpos & Hhi).
    split; [exact Hok|]. split; [apply KB; [lia | lia | exact Hbytes]|].
    split; [exact (sl_addr_keep m m' W _ _ Haddr MU HAW)|]. split; [exact Hpos | exact Hhi]. }
  split; [exact (sl_addr_keep m m' W (fr + 2624) 6 HOUR MU HAW)|].
  split; [apply KB; [apply Z.leb_le; vm_compute; reflexivity | apply Z.leb_le; vm_compute; reflexivity
                    | exact HTBL]|].
  split; [apply KB; [apply Z.leb_le; vm_compute; reflexivity | apply Z.leb_le; vm_compute; reflexivity
                    | exact HBOX]|].
  split; [apply KB; [lia | rewrite r8_mb_len; lia | exact HMROW]|].
  (* adopt 9 / 10 of a working branch: PRA, [A + 152], [A + 112] (in the save area), the fragment record's 72 bytes and
     [A + 160] *)
  split.
  { apply (r4_pra fr regs regs' m m'); [|exact HPRA].
    intros off v Hin Hs. apply K; [clear -Hin; cbn [In] in Hin; lia | clear -Hin; cbn [In] in Hin; lia | exact Hs]. }
  split; [apply K; [lia | lia | exact S152]|].
  split; [apply K; [lia | lia | exact S112]|].
  split; [exact (sl_addr_keep m m' W (fr + 2256) 72 HA2256 MU HAW)|].
  apply K; [lia | lia | exact S160].
Qed.

Section R8.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
(* The ending callee checked_memcpy (MCPY@0x81778), taken on its lib/B contract (asan_memcpy_c.v), never on its
   code. *)
Hypothesis MCPY : MCC.asan_memcpy_contract.

(* The allocator-law fields this file reads, in the shape its use sites take, read through SlotInv's LawFields
   (lw_*: each generated law is taken apart once there, so a later generation changes no line here). *)
Lemma r8_blocks : forall H mem md p n,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md -> In (p, n) H ->
  p mod 16 = 0 /\ 4096 <= p /\ p + n <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\ end_in_app p n /\
  (forall a, p <= a < p + n -> app_mem a /\ writable_at rsegs mem a /\ ~ AC.a_in_img a /\
     ~ AC.a_on_img_page a /\ ~ AC.a_in_fs AC.ASYMS mem a).
Proof.
  intros H mem md p n HAH Hin.
  destruct (lw_blocks (APIf rc) H mem md p n HAH Hin) as [H1 H2 H3 H4 H5].
  exact (conj H1 (conj H2 (conj H3 (conj H4 H5)))).
Qed.

Lemma r8_fs_place : forall H mem md FS,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md -> word_mem rsegs mem (AC.as_tp AC.ASYMS) FS ->
  0 <= FS < 2 ^ 64 ->
  AC.GT <= FS /\ FS + AC.FS_SIZE <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\ FS mod 4096 = 0 /\
  (forall a, FS <= a < FS + AC.FS_SIZE -> app_mem a).
Proof.
  intros H mem md FS HAH Hw HFS.
  destruct (lw_fs_place (APIf rc) H mem md FS HAH Hw HFS) as [H1 H2 H3 H4].
  exact (conj H1 (conj H2 (conj H3 H4))).
Qed.

Lemma r8_store : forall H mem mem' md,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ AC.a_store_ok H (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
     mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a) ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem' md /\
  (forall a, AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem' md a <->
     AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem md a) /\
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md.
Proof.
  intros H mem mem' md HAH Hmc Hwr.
  destruct (lw_store (APIf rc) H mem mem' md HAH Hmc Hwr) as [H1 H2 H3 H4].
  exact (conj H1 (conj H2 (conj H3 H4))).
Qed.

(* FSREC (the side-arm FakeStack frame record) moves across a run that writes no byte below GT (the tp word is
   an image-area word below GT) and no byte of the FakeStack [FS, FS + FS_SIZE) (the class-6 flag byte and the
   slot's last word fr + 4088 are inside it). The R8 write set is the fresh heap block, whose bytes a_laws_blocks
   puts above GT and outside the FakeStack, and the callee window, above stklo >= FS + FS_SIZE. *)
Lemma r8_fsrec : forall H mem mem' md W fr,
  FSREC fr mem -> AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md -> LF.munch W mem mem' ->
  (forall x, 0 <= x < AC.GT -> LF.outside W x) ->
  (forall x, AC.a_in_fs AC.ASYMS mem x -> LF.outside W x) ->
  FSREC fr mem'.
Proof.
  intros H mem mem' md W fr (FS & j & Htp & HFSr & Hj & Hfr & Hflag & Htail) HAH MU Hlow Hinfs.
  assert (HB6 : SMC.fs_B 6 = 4096) by reflexivity.
  assert (HM6 : SMC.fs_M 6 = 256) by reflexivity.
  assert (Hfl : SMC.fs_flag FS 6 j = FS + 36352 + j) by (unfold SMC.fs_flag; cbn; lia).
  assert (Hfrv : fr = FS + 6328320 + j * 4096) by (rewrite Hfr; unfold SMC.fs_frame, SMC.fs_B; cbn; lia).
  assert (HFSZ : AC.FS_SIZE = 11571200) by reflexivity.
  rewrite HM6 in Hj.
  assert (Hin : forall x, FS <= x < FS + AC.FS_SIZE -> LF.outside W x).
  { intros x Hx. apply Hinfs. exists FS. split; [exact HFSr|]. split; [exact Htp | exact Hx]. }
  exists FS, j.
  split.
  { intros k Hk.
    assert (Hx : 0 <= AC.as_tp AC.ASYMS + Z.of_nat k < AC.GT)
      by (unfold AC.as_tp, AC.ASYMS, AC.GT; cbn; lia).
    assert (Hm : mem' (Z_to_bv 64 (AC.as_tp AC.ASYMS + Z.of_nat k))
                 = mem (Z_to_bv 64 (AC.as_tp AC.ASYMS + Z.of_nat k))).
    { apply MU. rewrite MState.unsigned_lit by (unfold AC.GT in Hx; lia). apply Hlow. exact Hx. }
    unfold mbyte. rewrite Hm. exact (Htp k Hk). }
  split; [exact HFSr|].
  split; [rewrite HM6; exact Hj|].
  split; [exact Hfr|].
  split.
  { eapply fl_bytes; [exact Hflag | exact MU |]. cbn [length]. intros x Hx. apply Hin. lia. }
  { eapply fl_bytes; [exact Htail | exact MU |]. rewrite length_le8. intros x Hx. apply Hin.
    rewrite HB6 in Hx. lia. }
Qed.

Lemma seg_R8 : forall b : nat,
  Hat B APIf ra (Inv_B8177c_at B APIf ra) b -> Hat B APIf ra (Inv_B81764_at B APIf ra) b.
Proof.
  intros b Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hb6 & Hnz & Ha0 & HHB & HrN & HRBE &
                    Hr21 & HIDB & HFGB & Hsrcb & Hr22 & HOUR & HCUR & HADRs & Hr27).
  subst c.
  pose proof HRBE as (_ & Hsp312 & _).
  (* the copy's source: out[]'s frame bytes rt_F (adopt 10 of a working branch), n_b of them since n_b <> 0 *)
  assert (Hsrcl : Z.of_nat (length (rt_F (g_in g) (Z.of_nat b))) = rnb g b).
  { destruct (r8_rtn (g_in g) (Z.of_nat b) Hnz) as (Hrn & HL). rewrite HL.
    rewrite Z2Nat.id; [reflexivity | clear -Hrn; lia]. }
  set (src := rt_F (g_in g) (Z.of_nat b)) in Hsrcb, Hsrcl.
  destruct (fra_win B APIf ra g fr (hb1 phi (rnb g b)) regs mem md HFRA) as (Hlo & Hstkw).
  destruct (fra_frame B APIf ra g fr (hb1 phi (rnb g b)) regs mem md HFRA) as (Hplace & HfrA & HfsS & Hfrw).
  pose proof HFRA as HFRA0.
  destruct HFRA0 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as ALAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ ALAWS (hb1 phi (rnb g b) ++ g_H g) mem md HAH) as Hhigh.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  rewrite Haspz in Hlo, Hstkw.
  pose proof (Hplace 2224 ltac:(lia)) as Hsep. rewrite Haspz in Hsep.
  assert (HA64 : 0 <= A < 2 ^ 64) by (destruct Hwin as (Hw0 & Hw1 & _); lia).
  assert (HbvA : bv_unsigned (getr regs 9) = A)
    by (unfold rg in Hr9; rewrite Hr9; apply MState.unsigned_lit; exact HA64).
  (* the spill names the spill base A of register 9 *)
  destruct Hsp312 as (A2 & HA2 & Hq312).
  assert (HA2e : A2 = A)
    by (apply (r4_spill_A regs mem 312 (fr + 544) A A2 HA2 Hq312 Hr9); unfold APPMEM_END in HAPP; lia).
  subst A2.
  (* the frame is application memory above the image *)
  assert (Happ : forall a, fr <= a < fr + FRAME_BYTES -> app_mem a /\ AC.GT <= a).
  { intros a Ha. destruct Hloc as [[_ [Hspfr Hreal]] | [_ [_ [Hfs _]]]].
    - pose proof (Hreal a Ha). unfold app_mem, AC.GT, HIGHMEM_BEG, APPMEM_END, LOWMEM_END in *. lia.
    - destruct (Hfs a Ha) as (FSb & HFSr & Hw & Hlo2 & Hhi2).
      destruct (r8_fs_place (hb1 phi (rnb g b) ++ g_H g) mem md FSb HAH Hw HFSr)
        as (HGTb & _ & _ & HFapp).
      split; [apply HFapp; lia | lia]. }
  assert (Happ' : forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) by (intros a Ha; exact (proj1 (Happ a Ha))).
  assert (Hfre : 0 <= fr /\ fr + FRAME_BYTES <= APPMEM_END).
  { destruct (Happ fr ltac:(lia)) as (H1 & _). destruct (Happ (fr + FRAME_BYTES - 1) ltac:(lia)) as (H2 & _).
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia. }
  assert (HGT : AC.GT <= fr) by exact (proj2 (Happ fr ltac:(lia))).
  assert (HLH : fr + FRAME_BYTES <= LOWMEM_END \/ HIGHMEM_BEG <= fr).
  { destruct (Happ fr ltac:(lia)) as (H1 & _). destruct (Happ (fr + FRAME_BYTES - 1) ltac:(lia)) as (H2 & _).
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia. }
  pose proof (r4_sf8 fr Hfrm) as HSf8.
  (* the live heap block (Phi, n_b) of the cut's hb *)
  assert (HInblk : In (phi, rnb g b) (hb1 phi (rnb g b) ++ g_H g)).
  { unfold hb1. cbn [app]. left. reflexivity. }
  destruct (r8_blocks (hb1 phi (rnb g b) ++ g_H g) mem md phi (rnb g b) HAH HInblk)
    as (Hp16 & Hp4096 & Hpstklo & HEDd & Hblkb).
  pose proof (AC.a_laws_block_high _ _ _ _ _ ALAWS (hb1 phi (rnb g b) ++ g_H g) mem md phi (rnb g b) HAH HInblk)
    as Hp21.
  (* n_b is the serialized box length: 0 or 52 + 36 * uw with 2 <= uw <= 40 *)
  assert (HNb : 0 <= rnb g b <= 1492).
  { unfold rnb, rt_n. destruct (rt_E (g_in g) (Z.of_nat b)); [|lia].
    pose proof (RcPortsLib.bm_uw_range (mrow (g_in g)) (firstn 8 (skipn 16 (rt_mb (g_in g))))) as HU.
    unfold rt_uw. lia. }
  assert (HN1 : 1 <= rnb g b) by lia.
  (* the block is above the image: a block byte is on no image page *)
  assert (HGTphi : AC.GT <= phi).
  { destruct (Z_lt_le_dec phi 0x5fe000) as [Hlt|Hge]; [|unfold AC.GT; lia].
    exfalso. destruct (Hblkb phi ltac:(lia)) as (_ & _ & _ & Hpg & _).
    apply Hpg. apply r8_on_page. lia. }
  unfold AC.GT, ASAN_K, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in HGT, HSf8, HLH, Hfre, Hhigh.
  unfold AC.GT in HGTphi.
  assert (HAPPv : APPMEM_END = 140737488355328) by reflexivity.
  assert (HHMv : HIGHMEM_BEG = 17592186044416 + 2147450880) by reflexivity.
  assert (HLMv : LOWMEM_END = 2147450880) by reflexivity.
  (* the block's bytes: readable (writable off the image), app memory *)
  assert (Hblk64 : phi + rnb g b <= 2 ^ 64) by lia.
  assert (Hblkrd : forall a, phi <= a < phi + rnb g b -> exists bb, mrd rsegs mem (wa a) = Some bb).
  { intros a Ha. destruct (Hblkb a Ha) as (_ & Hw & Hni & _ & _).
    exact (r8_rd_of_w mem a ltac:(lia) Hni Hw). }
  assert (Hblkstk : stk rsegs mem phi (phi + rnb g b)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    split; [exact (proj1 (proj2 (Hblkb a Ha))) | exact (Hblkrd a Ha)]. }
  (* the write set and its pointwise separations *)
  assert (Hout_napp : forall x, ~ app_mem x -> LF.outside [(phi, phi + rnb g b); (sp - 2224, sp)] x).
  { intros x Hx. cbn [LF.outside]. split.
    - intros Hin. apply Hx. exact (proj1 (Hblkb x Hin)).
    - split; [|exact I]. intros Hin. apply Hx. unfold app_mem. right. lia. }
  assert (Hfrdj : forall x, fr <= x < fr + FRAME_BYTES -> ~ (phi <= x < phi + rnb g b)).
  { intros x Hx Hin. destruct (Hblkb x Hin) as (_ & _ & _ & _ & Hfsx).
    destruct Hloc as [[_ [_ Hreal]] | [_ [_ [Hfs _]]]].
    - pose proof (Hreal x Hx) as Hr. lia.
    - apply Hfsx. exact (Hfs x Hx). }
  assert (Hfrout : forall x, fr <= x < fr + FRAME_BYTES -> LF.outside [(phi, phi + rnb g b); (sp - 2224, sp)] x).
  { intros x Hx. cbn [LF.outside]. split; [exact (Hfrdj x Hx)|]. split; [lia | exact I]. }
  assert (HAW : all_app [(phi, phi + rnb g b); (sp - 2224, sp)]).
  { cbn [all_app]. split; [intros a Ha; exact (proj1 (Hblkb a Ha))|].
    split; [intros a Ha; unfold app_mem; right; lia | exact I]. }
  (* the normalized memory the run is stepped on *)
  pose proof (mem_rel_normalize rsegs mem Hro) as HR0.
  pose proof (mem_inv_normalize rsegs mem) as HMI0.
  pose proof (r4_srw_rel mem (normalize rsegs mem) HR0 (AsanRTInv.RT_shadow_rw _ _ _ HRT)) as HSW0.
  pose proof (r4_cells_rel mem (normalize rsegs mem) HR0 (AsanRTInv.RT_cells _ _ _ HRT)) as HAC0.
  pose proof (r4_stk_rel mem (normalize rsegs mem) (sp - FN_STACK) sp HR0 ltac:(lia) Hstkw) as ST0.
  pose proof (r4_stk_rel mem (normalize rsegs mem) phi (phi + rnb g b) HR0 ltac:(lia) Hblkstk) as Hblkstk0.
  (* the destination cell, the source bytes and the spilled source pointer on the normalized memory *)
  destruct (stk_bytes rsegs (normalize rsegs mem) phi (phi + rnb g b) Hblkstk0 ltac:(lia)) as (junk & Hjl & Hjb).
  replace (phi + rnb g b - phi) with (rnb g b) in Hjl by lia.
  assert (RWd : rw_cells rsegs (normalize rsegs mem) phi [CB (Z.to_nat (rnb g b)) junk]).
  { replace (Z.to_nat (rnb g b)) with (length junk) by lia. apply r4_rw_CB; [exact Hjb|].
    replace (Z.of_nat (length junk)) with (phi + rnb g b - phi) by lia.
    exact (r4_wr_stk _ _ _ Hblkstk0). }
  assert (HbS : bytes_at rsegs (normalize rsegs mem) (fr + 544) src)
    by exact (proj1 (bytes_at_rel rsegs mem (normalize rsegs mem) _ _ HR0) Hsrcb).
  assert (HLsrc : length src = Z.to_nat (rnb g b)) by lia.
  assert (RO : ro_cells rsegs (normalize rsegs mem) (A + 312) [C8 (Z_to_bv 64 (fr + 544))]).
  { apply r4_ro8. unfold q64 in Hq312.
    exact (proj1 (bytes_at_rel rsegs mem (normalize rsegs mem) _ _ HR0) Hq312). }
  (* the addressability of both windows on the normalized memory *)
  assert (AS : addressable (normalize rsegs mem) (fr + 544) (rnb g b))
    by exact (r4_addr_rel mem (normalize rsegs mem) (fr + 544) (rnb g b) HR0 HADRs).
  assert (HszN : rnb g b <= AC.a_size (rnb g b)) by (unfold AC.a_size; lia).
  assert (ADm : addressable mem phi (rnb g b)).
  { replace phi with (phi + 0) by lia.
    exact (addressable_sub mem phi (AC.a_size (rnb g b)) 0 (rnb g b) (proj2 HHB)
             ltac:(lia) ltac:(lia) ltac:(lia)). }
  assert (AD : addressable (normalize rsegs mem) phi (rnb g b))
    by exact (r4_addr_rel mem (normalize rsegs mem) phi (rnb g b) HR0 ADm).
  (* the arithmetic premises of the contract *)
  assert (Hphi0 : 0 < phi < 2 ^ 64) by lia.
  assert (HphiN : phi + rnb g b <= 2 ^ 64) by lia.
  assert (HAb : 0 <= A < 2 ^ 64) by lia.
  assert (HA320 : A + 320 <= 2 ^ 64) by lia.
  assert (HSb : 0 <= fr + 544 < 2 ^ 64) by lia.
  assert (HN0 : 0 <= rnb g b) by lia.
  assert (Hspvb : 0 <= sp < 2 ^ 64) by lia.
  assert (HAL : phi = fr + 544 \/ fr + 544 + rnb g b <= phi \/ phi + rnb g b <= fr + 544).
  { destruct (Z_le_gt_dec (fr + 544 + rnb g b) phi) as [H|H]; [right; left; lia|].
    destruct (Z_le_gt_dec (phi + rnb g b) (fr + 544)) as [H2|H2]; [right; right; lia|].
    exfalso. exact (Hfrdj (Z.max phi (fr + 544)) ltac:(lia) ltac:(lia)). }
  assert (HNb40 : rnb g b <= 2 ^ 40) by lia.
  assert (ES : end_in_app (fr + 544) (rnb g b)).
  { unfold end_in_app. right. apply Happ'. lia. }
  assert (ED : end_in_app phi (rnb g b)) by exact HEDd.
  assert (APP : rnb g b = 0 \/ app_mem (fr + 544 + 7) /\ app_mem (phi + 7)).
  { right. split; [apply Happ'; lia|].
    destruct (Z_lt_le_dec (rnb g b) 8) as [Hsm|Hbg]; [|exact (proj1 (Hblkb (phi + 7) ltac:(lia)))].
    destruct (proj1 (Hblkb phi ltac:(lia))) as [Hl|Hh]; unfold app_mem.
    - left. split; [lia|]. revert Hp16. Z.div_mod_to_equations. lia.
    - right. lia. }
  assert (HRTd : phi + rnb g b <= RT_LO \/ RT_HI <= phi) by (right; unfold RT_HI; lia).
  assert (HSEPd : phi + rnb g b <= sp - 2224 \/ sp <= phi) by (left; lia).
  assert (HSEPs : fr + 544 + rnb g b <= sp - 2224 \/ sp <= fr + 544) by lia.
  assert (HLOw : sp - FN_STACK + 2224 <= sp) by lia.
  assert (HHM : HIGHMEM_BEG <= sp - FN_STACK) by lia.
  assert (HAE : sp <= APPMEM_END) by lia.
  unfold rg in Hr9, HrN. unfold a0v, rg in Ha0.
  rewrite SEGS.
  apply (r4_run regs (Z_to_bv 64 0x81764) mem md
    (fun R pc' m0' => pc' = Z_to_bv 64 0x8177c /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\ getr R 8 = getr regs 8 /\
       getr R 9 = getr regs 9 /\ getr R 18 = getr regs 18 /\ getr R 19 = getr regs 19 /\ getr R 20 = getr regs 10 /\
       getr R 21 = getr regs 21 /\ getr R 22 = getr regs 22 /\
       getr R 23 = getr regs 23 /\ getr R 24 = getr regs 24 /\ getr R 25 = getr regs 25 /\
       getr R 26 = getr regs 26 /\ getr R 27 = getr regs 27 /\
       LF.munch [(phi, phi + rnb g b); (sp - 2224, sp)] (normalize rsegs mem) m0' /\
       LF.wmono rsegs (normalize rsegs mem) m0' /\ stk rsegs m0' (sp - FN_STACK) sp /\ shadow_rw m0' /\
       bytes_at rsegs m0' phi src)
    (Post B APIf ra g)).
  - exact Hhalt.
  - exact Hro.
  - rewrite r4_mkR_of.
    eapply evt_mono.
    + apply (r8_evt MCPY) with (spv := sp) (A := A) (S := fr + 544) (N := rnb g b) (phi := phi)
        (lo := sp - FN_STACK) (src := src) (junk := junk).
      all: try assumption.
    + intros ms' (R & m' & Hms & P2' & P3' & P4' & P8' & P9' & P18' & P19' & P20' & P21' & P22' & P23' & P24' &
                  P25' & P26' & P27' & MUq & WMq & MIq & STq & ACq & SWq & RWq & HBq).
      exists R, (Z_to_bv 64 0x8177c), m'. split; [exact Hms|].
      split; [reflexivity|]. split; [exact P2'|]. split; [exact P3'|]. split; [exact P4'|].
      split; [exact P8'|]. split; [exact P9'|]. split; [exact P18'|]. split; [exact P19'|]. split; [exact P20'|].
      split; [exact P21'|]. split; [exact P22'|]. split; [exact P23'|]. split; [exact P24'|].
      split; [exact P25'|]. split; [exact P26'|]. split; [exact P27'|].
      split; [exact MUq|]. split; [exact WMq|]. split; [exact STq|]. split; [exact SWq|].
      destruct RWq as ((_ & Hb) & _). cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb.
  - intros R pc' m0' regs'' mem' md'
      (Hpc & K2 & K3 & K4 & K8 & K9 & K18 & K19 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27 & MU0 & WM0 & ST0' &
       SW0' & HB0')
      Hreg HRel Hsame Hmat.
    subst pc'.
    assert (E2 : getr regs'' 2 = getr regs 2) by (rewrite Hreg; exact K2).
    assert (E3 : getr regs'' 3 = getr regs 3) by (rewrite Hreg; exact K3).
    assert (E4 : getr regs'' 4 = getr regs 4) by (rewrite Hreg; exact K4).
    assert (E8 : getr regs'' 8 = getr regs 8) by (rewrite Hreg; exact K8).
    assert (E9 : getr regs'' 9 = getr regs 9) by (rewrite Hreg; exact K9).
    assert (E18 : getr regs'' 18 = getr regs 18) by (rewrite Hreg; exact K18).
    assert (E19 : getr regs'' 19 = getr regs 19) by (rewrite Hreg; exact K19).
    assert (E20 : getr regs'' 20 = getr regs 10) by (rewrite Hreg; exact K20).
    assert (E21 : getr regs'' 21 = getr regs 21) by (rewrite Hreg; exact K21).
    assert (E25 : getr regs'' 25 = getr regs 25) by (rewrite Hreg; exact K25).
    assert (E22 : getr regs'' 22 = getr regs 22) by (rewrite Hreg; exact K22).
    assert (E23 : getr regs'' 23 = getr regs 23) by (rewrite Hreg; exact K23).
    assert (E24 : getr regs'' 24 = getr regs 24) by (rewrite Hreg; exact K24).
    assert (E26 : getr regs'' 26 = getr regs 26) by (rewrite Hreg; exact K26).
    assert (E27 : getr regs'' 27 = getr regs 27) by (rewrite Hreg; exact K27).
    (* back from the normalized memory to the real one *)
    pose proof (munch_rel rsegs _ mem (normalize rsegs mem) mem' m0' HR0 HRel Hsame MU0) as MU.
    pose proof (wmono_rel rsegs mem (normalize rsegs mem) mem' m0' HR0 HRel Hsame WM0) as WM.
    pose proof (ro_agree_same rsegs mem mem' Hro Hsame) as HRO'.
    pose proof (r4_stk_back mem' m0' (sp - FN_STACK) sp HRel ltac:(lia) ST0') as ST'.
    pose proof (r4_srw_back mem' m0' HRel SW0') as SW'.
    assert (HcopyR : bytes_at rsegs mem' phi src)
      by exact (proj2 (bytes_at_rel rsegs mem' m0' _ _ HRel) HB0').
    (* every written byte is readable after the run *)
    assert (RDW : forall x, ~ LF.outside [(phi, phi + rnb g b); (sp - 2224, sp)] x ->
              exists bb, mrd rsegs mem' (wa x) = Some bb).
    { intros x Hx. apply r4_not_out in Hx. destruct Hx as [Hx|Hx].
      - apply (r4_ba_rd mem' phi src x HcopyR). rewrite HLsrc. lia.
      - destruct ST' as (_ & _ & Hs). exact (proj2 (Hs x ltac:(lia))). }
    (* the heap invariant and stklo after the run: both arms by a_laws_store (the block is a block of H, the
       callee window is at or above stklo) *)
    assert (Hwrit : forall x, 0 <= x < 2 ^ 64 -> writable_at rsegs mem x -> writable_at rsegs mem' x)
      by (intros x _ Hx; exact (WM (Z_to_bv 64 x) Hx)).
    assert (Hmc : forall x, 0 <= x < 2 ^ 64 ->
              ~ AC.a_store_ok (hb1 phi (rnb g b) ++ g_H g)
                  (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) x ->
              mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
    { intros x Hx Hnok.
      destruct (r4_out_dec [(phi, phi + rnb g b); (sp - 2224, sp)] x) as [Ho|Hno].
      - apply MU. rewrite MState.unsigned_lit by exact Hx. exact Ho.
      - exfalso. apply Hnok. apply r4_not_out in Hno. destruct Hno as [Hx1|Hx1].
        + left. exists phi, (rnb g b). split; [exact HInblk | lia].
        + right; left. lia. }
    destruct (r8_store (hb1 phi (rnb g b) ++ g_H g) mem mem' md HAH Hmc Hwrit)
      as (HAH' & HOWN' & HSTK' & HHI').
    (* FRA at mem' *)
    assert (HDJ : rt_disjoint [(phi, phi + rnb g b); (sp - 2224, sp)]).
    { unfold AsanRTInv.rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
        RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB,
        RT_AGLOB_LEN.
      cbn [disjoint_from]. repeat split; first [exact I | lia]. }
    assert (Hshnew : exists sh', bytes_at rsegs mem' (Sfr fr) sh' /\ length sh' = Z.to_nat FRAME_SHADOW).
    { assert (Hst : stk rsegs mem' (Sfr fr) (Sfr fr + FRAME_SHADOW)).
      { split; [lia|]. split; [lia|].
        intros a Ha. apply SW'.
        replace a with (Sfr fr + (a - Sfr fr)) by lia. apply r4_fsh; [exact Happ' | lia]. }
      destruct (stk_bytes rsegs mem' _ _ Hst ltac:(lia)) as (bs & Hl & Hb).
      exists bs. split; [exact Hb|]. rewrite Hl. replace (Sfr fr + FRAME_SHADOW - Sfr fr) with FRAME_SHADOW by lia.
      reflexivity. }
    assert (HAG' : forall a, in_globals AF.frame_AG a -> addressable mem' a 1).
    { intros a Ha. pose proof (r4_sa_lo a (r4_ag_lo a Ha)) as Hsa. unfold ASAN_K in Hsa.
      apply (r4_addr_keep [(phi, phi + rnb g b); (sp - 2224, sp)] mem mem' a 1 (HAG a Ha) MU).
      intros i Hi. replace (a + i) with a by lia.
      apply Hout_napp. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END. lia. }
    (* the slot window outside the frame is still addressable: no shadow byte is written *)
    assert (HWA' : forall a, g_S g - AF.SLOT_STACK <= a < g_S g -> ~ (fr <= a < fr + FRAME_BYTES) ->
              addressable mem' a 1).
    { intros a Ha1 Ha2.
      assert (Happa : app_mem a) by (unfold app_mem; right; lia).
      apply (r4_addr_keep [(phi, phi + rnb g b); (sp - 2224, sp)] mem mem' a 1 (HWA a Ha1 Ha2) MU).
      intros i Hi. replace (a + i) with a by lia.
      apply Hout_napp. intro Hx. exact (app_not_shadow _ Hx (shadow_of_app a Happa)). }
    (* ENT across the run: the write set (the fresh block of hb and the callee window) holds no address ENT
       reads (an entry block's byte, an image byte, the stack at or above S, the shadow of an image or stack byte,
       or the shadow of an entry block's byte) *)
    assert (HKEPT : forall x, ent_kept g x -> LF.outside [(phi, phi + rnb g b); (sp - 2224, sp)] x).
    { intros x Hk.
      destruct Hk as [(q & k & i & Hin & Hni & Hi & ->) |
                      [Hik | [Habk | [(bq & Hor & ->) | (q & k & i & Hin & Hni & Hi & ->)]]]].
      - pose proof (AC.a_laws_disjoint _ _ _ _ _ ALAWS [] (g_H g) mem md phi (rnb g b) q k HAH Hin) as Hdj.
        destruct (r8_blocks (hb1 phi (rnb g b) ++ g_H g) mem md q k HAH
                    (in_or_app _ _ _ (or_intror Hin))) as (_ & _ & Hqk & _ & _).
        cbn [LF.outside]. split; [lia | split; [lia | exact I]].
      - pose proof (img_below_GT x Hik) as Hxg. unfold AC.GT in Hxg.
        cbn [LF.outside]. split; [lia | split; [lia | exact I]].
      - cbn [LF.outside]. split; [lia | split; [lia | exact I]].
      - assert (Happb : app_mem bq).
        { destruct Hor as [Hib|Hrb].
          - pose proof (img_below_GT bq Hib) as Hbg. unfold AC.GT in Hbg. unfold app_mem. left. lia.
          - unfold app_mem. right. lia. }
        apply Hout_napp. intro Hx. exact (app_not_shadow _ Hx (shadow_of_app bq Happb)).
      - destruct (r8_blocks (hb1 phi (rnb g b) ++ g_H g) mem md q k HAH (in_or_app _ _ _ (or_intror Hin)))
          as (_ & _ & _ & _ & Hall).
        destruct (Hall (q + i) ltac:(lia)) as (Happq & _).
        apply Hout_napp. intro Hx. exact (app_not_shadow _ Hx (shadow_of_app (q + i) Happq)). }
    assert (HOWNk : forall a, AC.a_in_img a ->
              AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb1 phi (rnb g b) ++ g_H g) mem md a ->
              AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb1 phi (rnb g b) ++ g_H g) mem' md a)
      by (intros a _ Ho; exact (proj2 (HOWN' a) Ho)).
    assert (HENT' : ENT APIf g (hb1 phi (rnb g b)) mem' md).
    { eapply ent_munch with (W := [(phi, phi + rnb g b); (sp - 2224, sp)]);
        [exact HENT | exact HAH | apply (proj1 (fr_munch_ul _ _ _)); exact MU |
         intros x Hk; apply (proj2 (fr_outside_lib _ _)); exact (HKEPT x Hk) |
         exact HSTK' | exact HHI' | exact HOWNk]. }
    assert (HENT'' : ENT APIf g (hb1 phi (rnb g b)) mem' md').
    { eapply ent_mat; [exact HENT' | exact Hmat]. }
    (* the save area [A, A + 448) is above sp and above the block, so the run writes none of it *)
    assert (HAout : forall x, A <= x < A + 448 -> LF.outside [(phi, phi + rnb g b); (sp - 2224, sp)] x).
    { intros x Hx. cbn [LF.outside]. split; [lia | split; [lia | exact I]]. }
    (* FSREC (side arm): the block is above GT and off the FakeStack, the window is above stklo *)
    assert (HFSR : FSREC fr mem -> FSREC fr mem').
    { intros Hf. apply (r8_fsrec _ mem mem' md [(phi, phi + rnb g b); (sp - 2224, sp)] fr Hf HAH MU).
      - intros x Hx. unfold AC.GT in Hx. cbn [LF.outside]. split; [lia | split; [lia | exact I]].
      - intros x Hfsx. pose proof Hfsx as (b0 & Hb0 & Hw0 & Hx0).
        destruct (r8_fs_place (hb1 phi (rnb g b) ++ g_H g) mem md b0 HAH Hw0 Hb0)
          as (_ & Hend & _ & _).
        cbn [LF.outside]. split; [|split; [lia | exact I]].
        intros Hin. destruct (Hblkb x Hin) as (_ & _ & _ & _ & Hnfs). exact (Hnfs Hfsx). }
    (* FRA's input facts: the input block is an entry block below stklo (fra_in_apart) and apart from the fresh
       block (a_laws_disjoint), so the run writes none of its bytes; the write set is app memory (fra_in_keep) *)
    assert (HINo : forall x, g_p g <= x < g_p g + g_n g -> LF.outside [(phi, phi + rnb g b); (sp - 2224, sp)] x).
    { intros x Hx.
      destruct (Hinblk ltac:(lia)) as (Hin & _).
      pose proof (AC.a_laws_disjoint _ _ _ _ _ ALAWS [] (g_H g) mem md phi (rnb g b) (g_p g) (g_n g) HAH Hin)
        as Hdj.
      destruct (fra_in_apart B APIf ra g fr (hb1 phi (rnb g b)) regs mem md HFRA x Hx) as (_ & Hxlo & _ & _).
      cbn [LF.outside]. split; [lia | split; [lia | exact I]]. }
    destruct (fra_in_keep g mem mem' [(phi, phi + rnb g b); (sp - 2224, sp)] Hinb Hinblk MU HAW
                (fun x Hx => proj2 (fr_outside_lib _ _) (HINo x Hx))) as (HIN1' & HIN2').
    assert (HFRAm : FRA B APIf ra g fr (hb1 phi (rnb g b)) regs'' mem' md).
    { apply (r4_fra B APIf ra empty FF g fr (hb1 phi (rnb g b)) regs regs'' mem mem' md
               [(phi, phi + rnb g b); (sp - 2224, sp)]
               HFRA MU WM HRO' HDJ HAH' HSTK' (fun a Ha => proj2 (SW' a Ha)) Hshnew);
        try assumption.
      - intros x Hx. cbn [LF.outside]. split; [lia | split; [lia | exact I]].
      - intros x Hx. apply Hfrout. lia.
      - intros x Hx. rewrite HbvA in Hx. cbn [LF.outside]. split; [lia | split; [lia | exact I]].
      - intros x Hx. rewrite HbvA in Hx. cbn [LF.outside]. split; [lia | split; [lia | exact I]].
      - intros x Hx. cbn [LF.outside]. split; [lia | split; [lia | exact I]].
      - intros x Hx.
        destruct (r4_out_dec [(phi, phi + rnb g b); (sp - 2224, sp)] x) as [Ho|Hno];
          [left; exact Ho | right; exact (RDW x Hno)]. }
    assert (HFRA' : FRA B APIf ra g fr (hb1 phi (rnb g b)) regs'' mem' md').
    { apply (sl_fra_move B APIf ra g fr (hb1 phi (rnb g b)) regs'' regs'' mem' md md' HFRAm);
        try reflexivity. exact Hmat. }
    assert (HRBE' : RBE g fr regs'' mem').
    { apply (r8_RBE_keep g fr regs regs'' [(phi, phi + rnb g b); (sp - 2224, sp)] mem mem' A HRBE MU HAW Hr9);
        [lia | lia | exact E9 | exact HAout |].
      intros x Hx. unfold AC.GT in Hx. cbn [LF.outside]. split; [lia | split; [lia | exact I]]. }
    (* the exit cut *)
    rewrite <- SEGS. apply Hexit. exists phi, regs'', mem', md', fr.
    split; [reflexivity|]. split; [exact HFRA'|]. split; [exact HENT''|].
    split; [exact Hgn|]. split; [exact Hb6|].
    split.
    { split; [exact (proj1 HHB)|].
      exact (sl_addr_keep mem mem' [(phi, phi + rnb g b); (sp - 2224, sp)] phi (AC.a_size (rnb g b))
               (proj2 HHB) MU HAW). }
    split.
    { unfold rg in *. rewrite E22. exact Hr22. }
    split.
    { unfold OURb in *. eapply fl_bytes; [exact HOUR | exact MU |]. rewrite OUR_length.
      intros x Hx. apply Hfrout. lia. }
    split.
    { destruct HCUR as (Hc0 & Hc23 & Hc25). unfold CUR, rg in *.
      split; [exact Hc0|]. split; [rewrite E23; exact Hc23 | rewrite E25; exact Hc25]. }
    split; [exact HRBE'|].
    split; [unfold rg in *; rewrite E21; exact Hr21|].
    split; [exact Hnz|].
    split; [unfold rg; rewrite E20; exact Ha0|].
    split; [unfold rg in *; rewrite E18; exact HrN|].
    destruct HRBE as (_ & _ & _ & _ & _ & _ & _ & H184 & _).
    split; [exact (r8_spill_keep regs regs'' mem mem' _ A 184 _ H184 Hr9 ltac:(lia) ltac:(lia)
                     ltac:(lia) ltac:(lia) E9 MU HAout)|].
    (* adopt 10 of a working branch: the turn-b records (frame bytes, outside the write set), the frame bytes rt_F at Phi (the
       copy's post), the fragment record's 72 addressable bytes (RBE's) and s11 = 32 (checked_memcpy keeps s11) *)
    split.
    { unfold IDBr in *. eapply fl_bytes; [exact HIDB | exact MU |]. rewrite r8_rid_len.
      intros x Hx. apply Hfrout. lia. }
    split.
    { unfold FGBr in *. eapply fl_bytes; [exact HFGB | exact MU |]. rewrite r8_rfg_len.
      intros x Hx. apply Hfrout. lia. }
    split; [exact HcopyR|].
    split.
    { destruct HRBE' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
        _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HA2256' & _).
      exact HA2256'. }
    unfold rg; rewrite E27; exact Hr27.
Qed.

End R8.
