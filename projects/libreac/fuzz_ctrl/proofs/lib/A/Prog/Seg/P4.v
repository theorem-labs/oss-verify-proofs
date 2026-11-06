(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v, with its addresses and numbers changed; 554 of its 653 lines of code are new or changed and 297 lines of the source are left out. *)
(* Segment P4 of fuzz_ctrl LLVMFuzzerTestOneInput (asan, libreac v1.9.0 image A): [0x81b80, 0x81b8c],
   Inv_A81b80 -> Inv_A81b90 (v1.8 [0x81b00, 0x81b0c], IDENTICAL-RENUMBER: every pc +0x80, and the spill v1.8 read
   at s1+208 is s1+192 in v1.9; it holds D = fr + 2768 in both).
   rule 24: no function proved (a slot segment).  The call checked_memset([s1+192], 0, 72) (MSET@0x81b8c) fills
   with 0 the 72 bytes at the pointer spilled at s1+192 (the fragment scratch buffer D = fr + 2768, set at
   0x813c0-0x813c4).  p4_evt is the Lib-level run of the four instructions (li a2,72 ; ld a0,192(s1) ; li a1,0 ;
   jal checked_memset) and the memset call by its asan contract; the destination and the stack scratch [sp-K,sp)
   are the only writes.  Both cuts are SlotInv's: the entry Inv_A81b80 and the exit Inv_A81b90 (aslot push 9 put
   D = fr + 2768, the spills [A+280] = fr+3040 / [A+240] = fr+3056 and the cells at fr+3040 / fr+3056 in
   Inv_A81b80).  No cut carries mem_inv: the memset contract's mem_inv premise is met by p4_evt_ro, which runs
   p4_evt on the normalized memory (MemNorm.evt_normalize from FRA's ro_agree) and carries its post back to the
   real memory.  FRA moves by Tac_slot.sl_fr_cl (AH by a_laws_store / a_laws_fs_store per frame arm, FSREC by
   fra_fsrec_stklo), ENT by ent_store then ent_mat.  Gap 4 (aslot push 11): CUR is kept (the call keeps s6 / s9),
   IDBe (the 38 bytes at fr + 2688, below D) by fl_bytes, and FGBe g fr z72 is MADE from the memset's post on
   D = fr + 2768.  Push 12: the spill [A + 144] = fr + 2688 is kept (s1 unchanged, the cell is above the frame and
   above sp) and the 17 bytes at fr + 2691 stay addressable (sl_addr_keep: W is application memory).  Push 13:
   PRO moves by P1's pro_fra (W is the 72 frame bytes at D and the callee window, at or above stklo, below A). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_memset_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_memset_c_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOn.
Import ListNotations.
Open Scope Z_scope.

Lemma p4_evt : asan_memset_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv A D lo : Z) (junk : list byte),
    sp = Z_to_bv 64 spv -> s1 = Z_to_bv 64 A -> 0 <= A < 2 ^ 64 -> 0 <= D < 2 ^ 64 -> 0 <= spv < 2 ^ 64 ->
    rw_cells rsegs m (A + 192) [C8 (Z_to_bv 64 D)] ->
    rw_cells rsegs m D [CB 72 junk] -> addressable m D 72 -> end_in_app D 72 ->
    app_mem (D + 7) -> (D + 72 <= RT_LO \/ RT_HI <= D) -> (D + 72 <= spv - ASAN_MEMSET_K \/ spv <= D) ->
    stk rsegs m lo spv -> lo + ASAN_MEMSET_K <= spv -> HIGHMEM_BEG <= lo -> spv <= APPMEM_END ->
    asan_cells m -> shadow_rw m -> mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81b90) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\ getr R 19 = s3 /\
         getr R 26 = s10 /\ getr R 22 = s6 /\ getr R 25 = s9 /\
         munch [(D, D + 72); (spv - ASAN_MEMSET_K, spv)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' lo spv /\ asan_cells m' /\ shadow_rw m' /\
         rw_cells rsegs m' D [CB 72 (repeat (Z_to_bv 8 0) 72)])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81b80) fc None m (seg_rom rsegs)).
Proof.
  intros MSET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv A D lo junk -> -> HA HD Hspv HLD RW HAD HE HA7 HRT HSEP ST HLO HHM HAE HAC HSW HMI.
  unfold asan_memset_contract in MSET. cbv zeta in MSET.
  step. step. step. step.
  eapply evt_cut.
  { eapply MSET with (junk := junk) (lo := lo).
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.unsigned_lit by lia. exact RW.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.unsigned_lit by lia. lia.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.unsigned_lit by lia. exact HAD.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.unsigned_lit by lia. exact HE.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.unsigned_lit by lia. right. exact HA7.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.unsigned_lit by lia. exact HRT.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.unsigned_lit by lia. exact HSEP.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.unsigned_lit by lia. exact ST.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.unsigned_lit by lia. exact HLO.
    - exact HHM.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.unsigned_lit by lia. exact HAE.
    - exact HAC.
    - exact HSW.
    - exact HMI. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
              E & MUc & WMc & MIc & STc & RWc & HAC' & HSW').
  subst ms'.
  assert (ED : bv_unsigned (Z_to_bv 64 D) = D) by (apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.unsigned_lit; lia).
  assert (E72 : bv_unsigned (Z_to_bv 64 72) = 72) by (apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.unsigned_lit; lia).
  assert (Esp : bv_unsigned (Z_to_bv 64 spv) = spv) by (apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.unsigned_lit; lia).
  rewrite ED in MUc, RWc. rewrite E72 in MUc, RWc. rewrite Esp in MUc, STc.
  fold_lit_ux_in RWc.
  replace (ret_pc (Z_to_bv 64 0x81b90)) with (Z_to_bv 64 0x81b90)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply evt_done. do 2 eexists. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|].
  split; [exact MUc|]. split; [exact WMc|]. split; [exact MIc|].
  split; [exact STc|]. split; [exact HAC'|]. split; [exact HSW' | exact RWc].
Qed.

(* Route (C) (a Theorem Labs lane's frozen form; the 09:58Z ruling for a run with a callee contract: p4_evt stays as it is).
   The run reads and stores no shadow byte of its own (0x81b80 li, 0x81b84 ld 192(s1), 0x81b88 li); the shadow it
   needs is the memset's, asan_memset_shadow_R at the call (a0 = D, a2 = 72). *)
Definition p4_evt_shadow_R (D : Z) : Z -> Prop := fun a => asan_memset_shadow_R (Z_to_bv 64 D) (Z_to_bv 64 72) a.

Lemma p4_evt_on : asan_memset_contract_on ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv A D lo : Z) (junk : list byte),
    sp = Z_to_bv 64 spv -> s1 = Z_to_bv 64 A -> 0 <= A < 2 ^ 64 -> 0 <= D < 2 ^ 64 -> 0 <= spv < 2 ^ 64 ->
    rw_cells rsegs m (A + 192) [C8 (Z_to_bv 64 D)] ->
    rw_cells rsegs m D [CB 72 junk] -> addressable m D 72 -> end_in_app D 72 ->
    app_mem (D + 7) -> (D + 72 <= RT_LO \/ RT_HI <= D) -> (D + 72 <= spv - ASAN_MEMSET_K \/ spv <= D) ->
    stk rsegs m lo spv -> lo + ASAN_MEMSET_K <= spv -> HIGHMEM_BEG <= lo -> spv <= APPMEM_END ->
    asan_cells m -> A.ShadowRwOn.shadow_rw_on (p4_evt_shadow_R D) m -> mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81b90) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\ getr R 19 = s3 /\
         getr R 26 = s10 /\ getr R 22 = s6 /\ getr R 25 = s9 /\
         munch [(D, D + 72); (spv - ASAN_MEMSET_K, spv)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' lo spv /\ asan_cells m' /\
         (forall P, A.ShadowRwOn.shadow_rw_on P m -> A.ShadowRwOn.shadow_rw_on P m') /\
         rw_cells rsegs m' D [CB 72 (repeat (Z_to_bv 8 0) 72)])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81b80) fc None m (seg_rom rsegs)).
Proof.
  intros MSET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv A D lo junk -> -> HA HD Hspv HLD RW HAD HE HA7 HRT HSEP ST HLO HHM HAE HAC HSW HMI.
  unfold asan_memset_contract_on in MSET. cbv zeta in MSET.
  step. step. step. step.
  eapply evt_cut.
  { eapply MSET with (junk := junk) (lo := lo).
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.unsigned_lit by lia. exact RW.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.unsigned_lit by lia. lia.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.unsigned_lit by lia. exact HAD.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.unsigned_lit by lia. exact HE.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.unsigned_lit by lia. right. exact HA7.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.unsigned_lit by lia. exact HRT.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.unsigned_lit by lia. exact HSEP.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.unsigned_lit by lia. exact ST.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.unsigned_lit by lia. exact HLO.
    - exact HHM.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.unsigned_lit by lia. exact HAE.
    - exact HAC.
    - exact HSW.
    - exact HMI. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
              E & MUc & WMc & MIc & STc & RWc & HAC' & HSW').
  subst ms'.
  assert (ED : bv_unsigned (Z_to_bv 64 D) = D) by (apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.unsigned_lit; lia).
  assert (E72 : bv_unsigned (Z_to_bv 64 72) = 72) by (apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.unsigned_lit; lia).
  assert (Esp : bv_unsigned (Z_to_bv 64 spv) = spv) by (apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.unsigned_lit; lia).
  rewrite ED in MUc, RWc. rewrite E72 in MUc, RWc. rewrite Esp in MUc, STc.
  fold_lit_ux_in RWc.
  replace (ret_pc (Z_to_bv 64 0x81b90)) with (Z_to_bv 64 0x81b90)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply evt_done. do 2 eexists. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|].
  split; [exact MUc|]. split; [exact WMc|]. split; [exact MIc|].
  split; [exact STc|]. split; [exact HAC'|]. split; [exact HSW' | exact RWc].
Qed.

(* ---- The segment lemma seg_P4. ---- *)
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06 YN2e.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import AsanRTInv PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOnT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_fs Tac_b5 P1.
Import ListNotations.
(* FRA's FPState and getr are those of the image-A YK11; import it last (as P1.v does). *)
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
(* The write-set predicates, cells and run predicates of p4_evt and of SlotInv's cuts are lib.Lib's. *)
Module LFr := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module LStep := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.
Module LCells := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.

(* mkR_of made concrete, so that the run lemma's register file is p4_evt's mkR (Seg/P1.v p1_mkR_of). *)
Lemma p4_mkR_of : forall regs, Regs6ss.mkR_of regs = LFr.mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4)
  (getr regs 5) (getr regs 6) (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12)
  (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19)
  (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26)
  (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31).
Proof. intros regs. reflexivity. Qed.

(* ---- The normalized-memory transports (Seg/P6.v p6_*, Seg/P1.v p1_*, lib/RoAdapt.v). ---- *)

Definition p4_tops (segs : list Segment) (top : Z) : bool :=
  forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? top) segs.

Lemma p4_rsegs_below_gt : p4_tops rsegs 0x5fe000 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma p4_find_below : forall segs top x n s,
  p4_tops segs top = true -> find_segment segs x n = Some s -> 0 <= n -> x < top \/ n = 0.
Proof.
  induction segs as [|s0 r IH]; intros top x n s Hb H Hn; cbn in H; [discriminate H|].
  unfold p4_tops in Hb. cbn [forallb] in Hb. apply andb_prop in Hb as [H0 Hr].
  apply Z.leb_le in H0.
  destruct (Z.leb (Z.of_N (seg_base s0)) x && Z.leb (x + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0))) eqn:E.
  - apply andb_prop in E as [_ E]. apply Z.leb_le in E. lia.
  - exact (IH top x n s Hr H Hn).
Qed.

(* No byte at or above the image's top (0x5fe000) is read-only. *)
Lemma p4_ro_addr_hi : forall a, 0x5fe000 <= a < 2 ^ 64 -> ro_addr rsegs (wa a) = false.
Proof.
  intros a Ha. unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.ro_addr.
  match goal with |- context [find_segment ?sg ?x ?n] =>
    destruct (find_segment sg x n) as [s|] eqn:E; [|reflexivity];
    destruct (p4_find_below sg 0x5fe000 x n s p4_rsegs_below_gt E ltac:(cbn; lia)) as [L|L];
    [exfalso; rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit in L by lia; lia | cbn in L; lia] end.
Qed.

Lemma p4_wview_rel_hi : forall m m0 a, MemNorm.mem_rel rsegs m m0 -> 0x5fe000 <= a < 2 ^ 64 ->
  (wview rsegs m0 (wa a) <> None <-> wview rsegs m (wa a) <> None).
Proof.
  intros m m0 a HR Ha. rewrite (MemNorm.wview_rel_rw rsegs m m0 (wa a) HR (p4_ro_addr_hi a Ha)). split; auto.
Qed.

Lemma p4_stk_rel : forall m m0 lo hi, MemNorm.mem_rel rsegs m m0 -> 0x5fe000 <= lo -> hi <= 2 ^ 64 ->
  stk rsegs m lo hi -> stk rsegs m0 lo hi.
Proof.
  intros m m0 lo hi HR Hlo Hhi (H0 & H1 & H). split; [lia|]. split; [lia|]. intros a Ha.
  destruct (H a Ha) as (Hw & b & Hb). split.
  - apply (proj2 (p4_wview_rel_hi m m0 a HR ltac:(lia))). exact Hw.
  - exists b. rewrite <- (MemNorm.mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma p4_stk_rel_back : forall m m0 lo hi, MemNorm.mem_rel rsegs m m0 -> 0x5fe000 <= lo -> hi <= 2 ^ 64 ->
  stk rsegs m0 lo hi -> stk rsegs m lo hi.
Proof.
  intros m m0 lo hi HR Hlo Hhi (H0 & H1 & H). split; [lia|]. split; [lia|]. intros a Ha.
  destruct (H a Ha) as (Hw & b & Hb). split.
  - apply (proj1 (p4_wview_rel_hi m m0 a HR ltac:(lia))). exact Hw.
  - exists b. rewrite (MemNorm.mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma p4_addressable_rel : forall m m0 p n, MemNorm.mem_rel rsegs m m0 -> addressable m p n -> addressable m0 p n.
Proof.
  intros m m0 p n HR (H0 & H1 & H2 & H). split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. destruct (H i Hi) as (Hap & b & Hb & Hok). split; [exact Hap|].
  exists b. rewrite <- (MemNorm.mrd_rel rsegs m m0 _ HR). split; [exact Hb | exact Hok].
Qed.

(* MemNorm.normalize drops only read-only image bytes; no shadow byte and no runtime cell is one. *)
Lemma p4_shadow_rw_norm : forall m m0, MemNorm.mem_rel rsegs m m0 -> shadow_rw m -> shadow_rw m0.
Proof.
  intros m m0 REL HSW a Ha. pose proof (sl_shadow_not_ro a Ha) as Hro.
  destruct (HSW a Ha) as (Hw & b & Hb). split.
  - rewrite (MemNorm.wview_rel_rw rsegs m m0 (wa a) REL Hro). exact Hw.
  - exists b. rewrite <- (MemNorm.mrd_rel rsegs m m0 (wa a) REL). exact Hb.
Qed.

Lemma p4_cells_norm : forall m m0, MemNorm.mem_rel rsegs m m0 -> asan_cells m -> asan_cells m0.
Proof.
  intros m m0 REL HAC. unfold asan_cells in HAC |- *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat match goal with |- _ /\ _ => split end;
    apply (proj1 (MemNorm.bytes_at_rel rsegs m m0 _ _ REL)); assumption.
Qed.

(* Writable cells above the image's top move to the normalized memory (lib/RoAdapt.v rw_cells_norm, with the
   not-read-only side condition discharged by p4_ro_addr_hi), and back (RoAdapt.rw_cells_back). *)
Lemma p4_rw_cells_rel : forall m m0 a cs, MemNorm.mem_rel rsegs m m0 -> 0x5fe000 <= a ->
  LStep.rw_cells rsegs m a cs -> LStep.rw_cells rsegs m0 a cs.
Proof.
  intros m m0 a cs REL Ha [[Hwf Hb] Hw]. split; [split; [exact Hwf|]|].
  - exact (proj1 (MemNorm.bytes_at_rel rsegs m m0 _ _ REL) Hb).
  - pose proof Hw as (Hw0 & Hw1 & _).
    apply (MemNorm.wr_at_norm rsegs m m0 _ _ REL Hw). intros i Hi. apply p4_ro_addr_hi. lia.
Qed.

Lemma p4_rw_cells_back : forall m m0 a cs, MemNorm.mem_rel rsegs m m0 ->
  LStep.rw_cells rsegs m0 a cs -> LStep.rw_cells rsegs m a cs.
Proof.
  intros m m0 a cs REL [[Hwf Hb] Hw]. split; [split; [exact Hwf|]|].
  - exact (proj2 (MemNorm.bytes_at_rel rsegs m m0 _ _ REL) Hb).
  - exact (MemNorm.wr_at_rel rsegs m m0 _ _ REL Hw).
Qed.

(* p4_evt from ro_agree instead of mem_inv (no cut carries mem_inv): the run is taken on the normalized memory,
   where mem_inv holds (MemNorm.mem_inv_normalize), and carried back by MemNorm.evt_normalize (Seg/P1.v p1_evt_ro,
   Seg/P6.v p6_evt_ro). Its post is about the real memory: munch / wmono by munch_rel / wmono_rel, ro_agree by
   ro_agree_same, the stack window and the zeroed destination cells back across mem_rel. *)
Lemma p4_evt_ro : asan_memset_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv A D lo : Z) (junk : list byte),
    sp = Z_to_bv 64 spv -> s1 = Z_to_bv 64 A -> 0 <= A < 2 ^ 64 -> 0 <= D < 2 ^ 64 -> 0 <= spv < 2 ^ 64 ->
    0x5fe000 <= A -> 0x5fe000 <= D ->
    LStep.rw_cells rsegs m (A + 192) [LCells.C8 (Z_to_bv 64 D)] ->
    LStep.rw_cells rsegs m D [LCells.CB 72 junk] -> addressable m D 72 -> end_in_app D 72 ->
    app_mem (D + 7) -> (D + 72 <= RT_LO \/ RT_HI <= D) -> (D + 72 <= spv - ASAN_MEMSET_K \/ spv <= D) ->
    stk rsegs m lo spv -> lo + ASAN_MEMSET_K <= spv -> HIGHMEM_BEG <= lo -> spv <= APPMEM_END ->
    asan_cells m -> shadow_rw m -> MemNorm.ro_agree rsegs m ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81b90) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\ getr R 19 = s3 /\
         getr R 26 = s10 /\ getr R 22 = s6 /\ getr R 25 = s9 /\
         LFr.munch [(D, D + 72); (spv - ASAN_MEMSET_K, spv)] m m' /\ LFr.wmono rsegs m m' /\
         MemNorm.ro_agree rsegs m' /\ stk rsegs m' lo spv /\
         LStep.rw_cells rsegs m' D [LCells.CB 72 (repeat (Z_to_bv 8 0) 72)])
      (MS (LFr.mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81b80) fc None m (seg_rom rsegs)).
Proof.
  intros MSET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv A D lo junk E1 E2 HA HD Hspv HAg HDg HLD RW HAD HE HA7 HRT HSEP ST HLO HHM HAE HAC HSW HRO.
  pose proof (MemNorm.mem_rel_normalize rsegs m HRO) as REL.
  assert (HHB : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  eapply evt_mono.
  - eapply MemNorm.evt_normalize; [vm_compute; reflexivity | exact HRO |].
    apply (p4_evt MSET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc (MemNorm.normalize rsegs m) spv A D lo junk E1 E2 HA HD Hspv).
    + exact (p4_rw_cells_rel m _ (A + 192) _ REL ltac:(lia) HLD).
    + exact (p4_rw_cells_rel m _ D _ REL ltac:(lia) RW).
    + exact (p4_addressable_rel m _ _ _ REL HAD).
    + exact HE.
    + exact HA7.
    + exact HRT.
    + exact HSEP.
    + exact (p4_stk_rel m _ lo spv REL ltac:(lia) ltac:(lia) ST).
    + exact HLO.
    + exact HHM.
    + exact HAE.
    + exact (p4_cells_norm m _ REL HAC).
    + exact (p4_shadow_rw_norm m _ REL HSW).
    + exact (MemNorm.mem_inv_normalize rsegs m).
  - intros s (s0' & (R & m0' & -> & P2 & P3 & P4 & P8 & P9 & P19 & P26 & P22 & P25 & MU0 & WM0 & _ & ST0 & _ & _
              & RW0)
              & MR & RS).
    destruct MR as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hrom & Hmem).
    destruct s as [Rs Fs pcs svcs rvs fcs ms ros].
    cbn in HR, HF, Hpc, Hsvc, Hres, Hfc, Hrom, Hmem, RS. subst Rs Fs pcs svcs rvs fcs ros.
    exists R, ms. split; [reflexivity|].
    split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P8|].
    split; [exact P9|]. split; [exact P19|]. split; [exact P26|]. split; [exact P22|]. split; [exact P25|].
    split; [exact (MemNorm.munch_rel rsegs _ m _ ms m0' REL Hmem RS MU0)|].
    split; [exact (MemNorm.wmono_rel rsegs m _ ms m0' REL Hmem RS WM0)|].
    split; [exact (MemNorm.ro_agree_same rsegs m ms HRO RS)|].
    split; [exact (p4_stk_rel_back ms m0' lo spv Hmem ltac:(lia) ltac:(lia) ST0)|].
    exact (p4_rw_cells_back ms m0' _ _ Hmem RW0).
Qed.

(* The shadow bytes p4_evt_ro needs: p4_evt's, on the normalized memory (normalize keeps every shadow byte). *)
Definition p4_evt_ro_shadow_R (D : Z) : Z -> Prop := fun a => p4_evt_shadow_R D a.

(* p4_evt_ro with the region premise (route (C); p4_evt_ro stays as it is, the 09:58Z ruling). *)
Lemma p4_evt_ro_on : asan_memset_contract_on ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv A D lo : Z) (junk : list byte),
    sp = Z_to_bv 64 spv -> s1 = Z_to_bv 64 A -> 0 <= A < 2 ^ 64 -> 0 <= D < 2 ^ 64 -> 0 <= spv < 2 ^ 64 ->
    0x5fe000 <= A -> 0x5fe000 <= D ->
    LStep.rw_cells rsegs m (A + 192) [LCells.C8 (Z_to_bv 64 D)] ->
    LStep.rw_cells rsegs m D [LCells.CB 72 junk] -> addressable m D 72 -> end_in_app D 72 ->
    app_mem (D + 7) -> (D + 72 <= RT_LO \/ RT_HI <= D) -> (D + 72 <= spv - ASAN_MEMSET_K \/ spv <= D) ->
    stk rsegs m lo spv -> lo + ASAN_MEMSET_K <= spv -> HIGHMEM_BEG <= lo -> spv <= APPMEM_END ->
    asan_cells m -> A.ShadowRwOn.shadow_rw_on (p4_evt_ro_shadow_R D) m -> MemNorm.ro_agree rsegs m ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81b90) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\ getr R 19 = s3 /\
         getr R 26 = s10 /\ getr R 22 = s6 /\ getr R 25 = s9 /\
         LFr.munch [(D, D + 72); (spv - ASAN_MEMSET_K, spv)] m m' /\ LFr.wmono rsegs m m' /\
         MemNorm.ro_agree rsegs m' /\ stk rsegs m' lo spv /\
         LStep.rw_cells rsegs m' D [LCells.CB 72 (repeat (Z_to_bv 8 0) 72)])
      (MS (LFr.mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81b80) fc None m (seg_rom rsegs)).
Proof.
  intros MSET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv A D lo junk E1 E2 HA HD Hspv HAg HDg HLD RW HAD HE HA7 HRT HSEP ST HLO HHM HAE HAC HSW HRO.
  pose proof (MemNorm.mem_rel_normalize rsegs m HRO) as REL.
  assert (HHB : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  eapply evt_mono.
  - eapply MemNorm.evt_normalize; [vm_compute; reflexivity | exact HRO |].
    apply (p4_evt_on MSET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4
             t5 t6 F fc (MemNorm.normalize rsegs m) spv A D lo junk E1 E2 HA HD Hspv).
    + exact (p4_rw_cells_rel m _ (A + 192) _ REL ltac:(lia) HLD).
    + exact (p4_rw_cells_rel m _ D _ REL ltac:(lia) RW).
    + exact (p4_addressable_rel m _ _ _ REL HAD).
    + exact HE.
    + exact HA7.
    + exact HRT.
    + exact HSEP.
    + exact (p4_stk_rel m _ lo spv REL ltac:(lia) ltac:(lia) ST).
    + exact HLO.
    + exact HHM.
    + exact HAE.
    + exact (p4_cells_norm m _ REL HAC).
    + exact (A.ShadowRwOnT.shadow_rw_on_rel _ m _ REL HSW).
    + exact (MemNorm.mem_inv_normalize rsegs m).
  - intros s (s0' & (R & m0' & -> & P2 & P3 & P4 & P8 & P9 & P19 & P26 & P22 & P25 & MU0 & WM0 & _ & ST0 & _ & _
              & RW0)
              & MR & RS).
    destruct MR as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hrom & Hmem).
    destruct s as [Rs Fs pcs svcs rvs fcs ms ros].
    cbn in HR, HF, Hpc, Hsvc, Hres, Hfc, Hrom, Hmem, RS. subst Rs Fs pcs svcs rvs fcs ros.
    exists R, ms. split; [reflexivity|].
    split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P8|].
    split; [exact P9|]. split; [exact P19|]. split; [exact P26|]. split; [exact P22|]. split; [exact P25|].
    split; [exact (MemNorm.munch_rel rsegs _ m _ ms m0' REL Hmem RS MU0)|].
    split; [exact (MemNorm.wmono_rel rsegs m _ ms m0' REL Hmem RS WM0)|].
    split; [exact (MemNorm.ro_agree_same rsegs m ms HRO RS)|].
    split; [exact (p4_stk_rel_back ms m0' lo spv Hmem ltac:(lia) ltac:(lia) ST0)|].
    exact (p4_rw_cells_back ms m0' _ _ Hmem RW0).
Qed.

(* ---- The write set W = [(D, D + 72); (sp - K, sp)] of the call. ---- *)

Lemma p4_out : forall D spv x, ~ (D <= x < D + 72) -> ~ (spv - ASAN_MEMSET_K <= x < spv) ->
  LFr.outside [(D, D + 72); (spv - ASAN_MEMSET_K, spv)] x.
Proof. intros D spv x H1 H2. cbn [LFr.outside]. split; [exact H1|]. split; [exact H2 | exact I]. Qed.

(* Every byte is outside W, in the destination, or in the stack scratch. *)
Lemma p4_cases : forall D spv x,
  LFr.outside [(D, D + 72); (spv - ASAN_MEMSET_K, spv)] x \/ (D <= x < D + 72) \/
  (spv - ASAN_MEMSET_K <= x < spv).
Proof.
  intros D spv x.
  destruct (Z.lt_ge_cases x D) as [H1|H1]; [|destruct (Z.lt_ge_cases x (D + 72)) as [H2|H2]].
  all: destruct (Z.lt_ge_cases x (spv - ASAN_MEMSET_K)) as [H3|H3];
    [|destruct (Z.lt_ge_cases x spv) as [H4|H4]].
  all: first [ right; left; lia | right; right; lia | left; apply p4_out; lia ].
Qed.

(* Two word_mem values at the same address agree mod 2^64 (Seg/P2.v p2_wm_congr). *)
Lemma p4_wm_congr : forall (m : word -> option byte) a v1 v2,
  word_mem rsegs m a v1 -> word_mem rsegs m a v2 -> v1 mod 2^64 = v2 mod 2^64.
Proof.
  intros m a v1 v2 H1 H2.
  assert (Hb : forall k, (k < 8)%nat -> le_byte v1 8 k = le_byte v2 8 k).
  { intros k Hk. pose proof (H1 k Hk) as E1. pose proof (H2 k Hk) as E2.
    rewrite E1 in E2.
    assert (E2' : Z_to_bv 8 (le_byte v1 8 k) = Z_to_bv 8 (le_byte v2 8 k)) by congruence.
    apply (f_equal (@bv_unsigned 8)) in E2'. rewrite !kb_byte_unsigned in E2'. exact E2'. }
  apply Z.bits_inj'. intros j Hj.
  destruct (Z.ltb_spec j 64) as [Hlt|Hge].
  - set (k := Z.to_nat (j / 8)).
    assert (Hk8 : (k < 8)%nat) by (unfold k; apply Nat2Z.inj_lt; rewrite Z2Nat.id by (apply Z.div_pos; lia);
      apply Z.div_lt_upper_bound; lia).
    pose proof (Hb k Hk8) as Hbk.
    assert (Hoff : 8 * Z.of_nat k + (j - 8 * Z.of_nat k) = j) by lia.
    assert (Hjk : j - 8 * Z.of_nat k = j mod 8) by (unfold k; rewrite Z2Nat.id by (apply Z.div_pos; lia);
      rewrite (Z.div_mod j 8) at 1 by lia; lia).
    assert (Hoff8 : 0 <= j - 8 * Z.of_nat k < 8) by (rewrite Hjk; apply Z.mod_pos_bound; lia).
    assert (HT : Z.testbit (le_byte v1 8 k) (j - 8 * Z.of_nat k)
               = Z.testbit (le_byte v2 8 k) (j - 8 * Z.of_nat k)) by (rewrite Hbk; reflexivity).
    rewrite !le_byte_testbit in HT by lia.
    rewrite (proj2 (Z.ltb_lt _ 8)) in HT by lia.
    rewrite (proj2 (Z.ltb_lt _ _)) in HT by lia.
    rewrite Hoff in HT.
    rewrite !Z.testbit_mod_pow2 by lia.
    rewrite (proj2 (Z.ltb_lt j 64)) by lia. exact HT.
  - rewrite !Z.testbit_mod_pow2 by lia. rewrite (proj2 (Z.ltb_ge j 64)) by lia. reflexivity.
Qed.

(* Every side-stack metadata cell lies in [FS, FS + 36864) (Seg/P2.v p2_fs_meta_range). *)
Lemma p4_fs_meta_range : forall FS q, fs_meta FS q -> FS <= q < FS + 36864.
Proof.
  intros FS q H. split; [|exact (fs_meta_below FS q H)].
  destruct H as [H | [H | [ [c [Hc Hr]] | [c [j [Hc [Hj Heq]]]] ]]].
  - lia.
  - lia.
  - unfold AC.a_fs_hint in Hr. lia.
  - subst q. exact (proj1 (a_fs_flag_range FS c j Hc Hj)).
Qed.

(* A spill witness A of s1 is s1's in-range value A0: they agree mod 2^64 and the 8-byte cell at A + off lies in
   [0, 2^64), which leaves only A = A0 when A0 + off < 2^64. *)
Lemma p4_spill_base : forall (regs : bvmap 5 word) (m : word -> option byte) A A0 off v,
  rg regs 9 A0 -> 0 <= A0 -> 0 <= off -> A0 + off < 2 ^ 64 ->
  rg regs 9 A -> q64 m (A + off) v -> A = A0.
Proof.
  intros regs m A A0 off v H0 HA0 Hoff HA0hi H Hq.
  unfold q64 in Hq. apply bytes_at_bound in Hq. rewrite length_le8 in Hq.
  unfold rg in *. rewrite H0 in H.
  apply (f_equal (@bv_unsigned 64)) in H.
  rewrite (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit A0) in H by lia.
  rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit_wrap in H.
  change (2 ^ 64) with 18446744073709551616 in *.
  revert H Hq. Z.div_mod_to_equations. lia.
Qed.

Section P4W.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

(* Both cuts are SlotInv's. The memset writes the 72 frame bytes at D = fr + 2768 (frame body, past the header)
   and its stack scratch [sp - K, sp) (above stklo, inside the entry-anchored slot window, apart from the frame by
   fra_frame); the spills at A + 280 / A + 240 and the cells at fr + 3040 / fr + 3056 are outside both. *)
Lemma seg_P4 : asan_memset_contract ->
  Hcut B APIf ra (Inv_A81b90 B APIf ra) -> Hcut B APIf ra (Inv_A81b80 B APIf ra).
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros MSET Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (regs & mem & md & fr & Ec & HFRA & HENT & Hgn & HOUR & (Hc0 & Hr22 & Hr25) & HPRO & HSP &
    HADR & HADF & HADI &
    HIDB &
    (D & spv & A & junk & Hr2 & Hr9 & HAb & HDb & Hspvb & RW208 & RWd & HAD & HE & HA7 & HRTd & HSEP &
     HWlo & HWhdr & HWspill & HWsel & HWsaved & HWsh & HWour & HAW & HDJ & HDfr & H280 & H240 &
     (jy & junk2 & RWy & RWj) & HAF)).
  subst c D.
  rewrite SEGS.
  pose proof HFRA as HFRA0.
  destruct HFRA0 as (A0 & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2f & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9f & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 &
    Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS ([] ++ g_H g) mem md HAH) as Hstkhigh.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HKv : ASAN_MEMSET_K = 2208) by reflexivity.
  assert (HHB : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  assert (HAE : APPMEM_END = 0x800000000000) by reflexivity.
  assert (HGTv : AC.GT = 0x5fe000) by reflexivity.
  assert (HFSZ : AC.FS_SIZE = 11571200) by reflexivity.
  (* the cut's sp and s1 values are FRA's *)
  assert (Esp : sp = spv).
  { unfold AC.aspZ in Haspz. rewrite Hr2 in Haspz. rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit in Haspz by lia. lia. }
  revert Esp. intros ->.
  assert (EA : A = A0).
  { unfold rg in Hr9f. pose proof (f_equal (@bv_unsigned 64) (eq_trans (eq_sym Hr9) Hr9f)) as E0.
    rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit in E0 by lia. exact E0. }
  revert EA. intros <-.
  (* the frame is app memory above the image; it is apart from the memset scratch *)
  pose proof (fra_app B APIf ra g fr [] regs mem md HFRA) as (HGT & Happfr).
  pose proof (fra_frame B APIf ra g fr [] regs mem md HFRA) as (Hfrsp & _ & _ & _).
  assert (Hapart : fr + FRAME_BYTES <= spv - ASAN_MEMSET_K \/ spv <= fr).
  { destruct (Hfrsp ASAN_MEMSET_K ltac:(unfold FN_STACK; lia)) as [H|H]; rewrite Haspz in H;
      [left | right]; exact H. }
  (* the memset's premises *)
  pose proof (AsanRTInv.RT_cells _ _ _ HRT) as HAC.
  pose proof (AsanRTInv.RT_shadow_rw _ _ _ HRT) as HSW.
  assert (HSTw : stk rsegs mem (g_S g - AF.SLOT_STACK) spv).
  { destruct Hwin as (Hw0 & Hw1 & Hw). split; [lia|]. split; [lia|]. intros x Hx. apply Hw. lia. }
  (* run the segment *)
  apply (sl_run_lib regs (Z_to_bv 64 0x81b80) mem md
    (fun R pc' mem' => pc' = Z_to_bv 64 0x81b90 /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\ getr R 8 = getr regs 8 /\
       getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\ getr R 26 = getr regs 26 /\
       getr R 22 = getr regs 22 /\ getr R 25 = getr regs 25 /\
       LFr.munch [(fr + 2768, fr + 2768 + 72); (spv - ASAN_MEMSET_K, spv)] mem mem' /\
       LFr.wmono rsegs mem mem' /\ ro_agree rsegs mem' /\ stk rsegs mem' (g_S g - AF.SLOT_STACK) spv /\
       LStep.rw_cells rsegs mem' (fr + 2768) [LCells.CB 72 (repeat (Z_to_bv 8 0) 72)])
    (Post B APIf ra g)).
  - exact Hhalt.
  - rewrite p4_mkR_of.
    eapply evt_mono.
    + apply (p4_evt_ro MSET) with (spv := spv) (A := A) (D := fr + 2768) (lo := g_S g - AF.SLOT_STACK)
        (junk := junk).
      all: first [assumption | lia].
    + intros ms' (R & m' & Hms & P2 & P3 & P4 & P8 & P9 & P19 & P26 & P22 & P25 & MUq & WMq & ROq & STq & RWq).
      exists R, (Z_to_bv 64 0x81b90), m'. split; [exact Hms|].
      split; [reflexivity|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P8|].
      split; [exact P9|]. split; [exact P19|]. split; [exact P26|]. split; [exact P22|]. split; [exact P25|].
      split; [exact MUq|]. split; [exact WMq|].
      split; [exact ROq|]. split; [exact STq | exact RWq].
  - intros R pc' mem' regs'' md'
      (Hpc & K2 & K3 & K4 & K8 & K9 & K19 & K26 & K22 & K25 & MU & WM & HRO' & STk & RWk)
      Hreg Hmat.
    subst pc'.
    assert (E2 : getr regs'' 2 = getr regs 2) by (rewrite Hreg; exact K2).
    assert (E3 : getr regs'' 3 = getr regs 3) by (rewrite Hreg; exact K3).
    assert (E4 : getr regs'' 4 = getr regs 4) by (rewrite Hreg; exact K4).
    assert (E8 : getr regs'' 8 = getr regs 8) by (rewrite Hreg; exact K8).
    assert (E9 : getr regs'' 9 = getr regs 9) by (rewrite Hreg; exact K9).
    assert (E19 : getr regs'' 19 = getr regs 19) by (rewrite Hreg; exact K19).
    assert (E26 : getr regs'' 26 = getr regs 26) by (rewrite Hreg; exact K26).
    (* the destination's bytes are present and writable after the run *)
    pose proof (LFr.stk_of_rw_cells rsegs mem' (fr + 2768) [LCells.CB 72 (repeat (Z_to_bv 8 0) 72)] RWk) as HDst.
    change (Z.of_nat (LCells.cells_size [LCells.CB 72 (repeat (Z_to_bv 8 0) 72)])) with 72 in HDst.
    (* AH, the runtime's ownership and the stack bounds across the two writes, by frame arm *)
    assert (AHSTK : AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) ([] ++ g_H g) mem' md /\
                    (forall a, AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) ([] ++ g_H g) mem' md a <->
                               AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) ([] ++ g_H g) mem md a) /\
                    AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md
                      = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
                    AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md
                      = AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md).
    { assert (Hwrit : forall x, 0 <= x < 2^64 -> writable_at rsegs mem x -> writable_at rsegs mem' x).
      { intros x Hx Hwx. exact (WM (Z_to_bv 64 x) Hwx). }
      destruct Hloc as [[Hs50 [Hspfr Hreal]]|[Hs5fr [Hfsb [Hfs Hrec]]]].
      - (* real arm: the destination is a frame byte and the scratch a stack byte, both in [stklo, APPMEM_END) *)
        assert (Hmc : forall x, 0 <= x < 2^64 ->
                  ~ AC.a_store_ok ([] ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) x ->
                  mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
        { intros x Hx Hnok. apply MU. rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by exact Hx.
          destruct (p4_cases (fr + 2768) spv x) as [Ho|[Hd|Hsc]]; [exact Ho| |].
          - exfalso. apply Hnok. right. left. specialize (Hreal x ltac:(lia)). lia.
          - exfalso. apply Hnok. right. left. lia. }
        exact (p1_laws_store APIf ([] ++ g_H g) mem mem' md HAH Hmc Hwrit).
      - (* side arm: the destination lies in the side stack FS, the scratch in [stklo, APPMEM_END) *)
        destruct (Hfs fr ltac:(lia)) as (FS & HFSr & HFSw & HFSlo & HFShi).
        destruct (p1_laws_fs_place APIf ([] ++ g_H g) mem md FS HAH HFSw HFSr) as (HGTFS & HFSend & HFSmod & HFSapp).
        pose proof (p1_fs_ok_of_state APIf ([] ++ g_H g) mem md FS HAH HFSw HFSr) as Hfsok0.
        pose proof (Hfsb FS HFSw HFSr) as HFSfr.
        assert (HinFS : forall a, fr <= a < fr + FRAME_BYTES -> FS <= a < FS + AC.FS_SIZE).
        { intros a Ha. destruct (Hfs a Ha) as (b & Hbr & Hbw & Hb1 & Hb2).
          pose proof (p4_wm_congr mem _ b FS Hbw HFSw) as X. rewrite !Z.mod_small in X by lia.
          subst b. lia. }
        (* every present byte stays present: outside W by munch, in W by the post's cells and window *)
        assert (Hpres : forall q, 0 <= q < 2 ^ 64 -> (exists b, mbyte rsegs mem q = Some b) ->
                  exists b, mbyte rsegs mem' q = Some b).
        { intros q Hq (b & Hb).
          destruct (p4_cases (fr + 2768) spv q) as [Ho|[Hd|Hsc]].
          - exists b. unfold mbyte in Hb |- *. rewrite MU; [exact Hb|].
            rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by exact Hq. exact Ho.
          - destruct HDst as (_ & _ & HDs). destruct (HDs q Hd) as (_ & b' & Hb').
            exists b'. unfold mbyte. unfold mrd, wa in Hb'. exact Hb'.
          - destruct STk as (_ & _ & HSs). destruct (HSs q ltac:(lia)) as (_ & b' & Hb').
            exists b'. unfold mbyte. unfold mrd, wa in Hb'. exact Hb'. }
        (* the side stack's metadata is below the frames and below stklo, so W misses it *)
        assert (Hmeta : forall q, fs_meta FS q ->
                  LFr.outside [(fr + 2768, fr + 2768 + 72); (spv - ASAN_MEMSET_K, spv)] q).
        { intros q Hq. pose proof (p4_fs_meta_range _ _ Hq) as Hqr. apply p4_out; lia. }
        assert (Hfsok' : AC.a_fs_ok mem' FS).
        { apply (a_fs_ok_pres _ mem mem' FS Hfsok0 MU Hwrit Hpres Hmeta); lia. }
        assert (Hmc : forall x, 0 <= x < 2^64 ->
                  ~ AC.a_store_ok ([] ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) x ->
                  ~ (FS <= x < FS + AC.FS_SIZE) ->
                  ~ (exists b, FS <= b < FS + AC.FS_SIZE /\ x = shadow_addr b) ->
                  mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
        { intros x Hx Hnok Hnfs Hnsh. apply MU. rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by exact Hx.
          destruct (p4_cases (fr + 2768) spv x) as [Ho|[Hd|Hsc]]; [exact Ho| |].
          - exfalso. apply Hnfs. apply HinFS. lia.
          - exfalso. apply Hnok. right. left. lia. }
        exact (p1_laws_fs_store APIf ([] ++ g_H g) mem mem' md FS HAH HFSw HFSr Hmc Hwrit Hfsok'). }
    destruct AHSTK as (HAH' & Hown' & HSTK' & HSTKhi').
    (* the entry-anchored slot window after the run *)
    assert (HSTKwin : stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g)).
    { apply (fl_stk _ mem mem' (g_S g - AF.SLOT_STACK) (g_S g) Hwin MU WM).
      intros x Hx. destruct (p4_cases (fr + 2768) spv x) as [Ho|[Hd|Hsc]].
      - left. exact Ho.
      - right. destruct HDst as (_ & _ & HDs). exact (proj2 (HDs x Hd)).
      - right. destruct STk as (_ & _ & HSs). exact (proj2 (HSs x ltac:(lia))). }
    (* FSREC: W writes nothing below stklo outside the frame body *)
    assert (HRECK : FSREC fr mem -> FSREC fr mem').
    { intros Hrec0.
      eapply fra_fsrec_stklo;
        [exact HFRA
        | first [exact MU | exact (proj1 (fr_munch_ul _ _ _) MU) | exact (proj2 (fr_munch_ul _ _ _) MU)]
        | | exact Hrec0].
      intros x Hx Hnb.
      first [apply p4_out | apply (proj2 (fr_outside_lib _ _)); apply p4_out | apply (proj1 (fr_outside_lib _ _)); apply p4_out];
        lia. }
    (* FRA across the run (at md), then the model step *)
    assert (HFRAm : FRA B APIf ra g fr [] regs'' mem' md).
    { apply (sl_fr_cl B APIf ra empty FF g fr [] regs regs'' mem mem' md
        [(fr + 2768, fr + 2768 + 72); (spv - ASAN_MEMSET_K, spv)] HFRA);
        first [assumption | exact (proj1 (fr_munch_ul _ _ _) MU) | exact (proj2 (fr_munch_ul _ _ _) MU)]. }
    assert (HFRA' : FRA B APIf ra g fr [] regs'' mem' md').
    { apply (sl_fra_move B APIf ra g fr [] regs'' regs'' mem' md md' HFRAm); try reflexivity. exact Hmat. }
    (* ENT: the run writes only the frame body and the slot window below S (ent_store), then ent_mat *)
    assert (HENT1 : ENT APIf g [] mem' md).
    { eapply ent_store;
        [exact HENT | exact HFRA
        | first [exact MU | exact (proj1 (fr_munch_ul _ _ _) MU) | exact (proj2 (fr_munch_ul _ _ _) MU)]
        | | exact HSTK' | exact HSTKhi' | exact (fun a _ Ho => proj2 (Hown' a) Ho)].
      intros x Hx. destruct (p4_cases (fr + 2768) spv x) as [Ho|[Hd|Hsc]].
      - left. first [exact Ho | exact (proj2 (fr_outside_lib _ _) Ho) | exact (proj1 (fr_outside_lib _ _) Ho)].
      - right. right. left. lia.
      - right. left. lia. }
    assert (HENT' : ENT APIf g [] mem' md') by (eapply ent_mat; [exact HENT1 | exact Hmat]).
    (* the exit cut Inv_A81b90 *)
    rewrite <- SEGS. apply Hexit.
    exists regs'', mem', md', fr.
    split; [reflexivity|].
    split; [exact HFRA'|]. split; [exact HENT'|]. split; [exact Hgn|].
    split.
    { (* our[] at fr + 2624 is below the destination and apart from the scratch *)
      unfold OURb in *. eapply fl_bytes; [exact HOUR | exact MU |].
      rewrite OUR_length. intros x Hx. apply p4_out; [lia | destruct Hapart; lia]. }
    split.
    { (* CUR: the call keeps s6 and s9 *)
      split; [exact Hc0|]. unfold rg in *.
      split; [rewrite Hreg, K22; exact Hr22 | rewrite Hreg, K25; exact Hr25]. }
    split.
    { (* push 13: PRO (W is the 72 frame bytes at fr + 2768 and the callee window, at or above stklo and below
         A: P1's pro_fra) *)
      apply (pro_fra B APIf ra g fr [] regs regs'' mem mem' md _ A HFRA HPRO Hr9 HAb MU E9).
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold pro_iv; cbn [fst snd]; lia. }
    split.
    { (* the spill [A + 144] = fr + 2688: s1 is kept and the cell is above the frame and above sp *)
      destruct HSP as (A' & HA' & Hq).
      assert (EA' : A' = A)
        by (apply (p4_spill_base regs mem A' A 144 (fr + 2688) Hr9 ltac:(lia) ltac:(lia)
                     ltac:(unfold APPMEM_END in HAPP; lia) HA' Hq)).
      subst A'. exists A. split; [unfold rg; rewrite E9; exact Hr9|].
      unfold q64 in *. eapply fl_bytes; [exact Hq | exact MU |].
      rewrite length_le8. intros x Hx. apply p4_out; lia. }
    split.
    { (* the 17 bytes at fr + 2691: W is application memory, so no shadow byte changes *)
      first [ exact (sl_addr_keep mem mem' _ (fr + 2691) 17 HADR MU HAW)
            | exact (sl_addr_keep mem mem' _ (fr + 2691) 17 HADR (proj1 (fr_munch_ul _ _ _) MU) HAW)
            | exact (sl_addr_keep mem mem' _ (fr + 2691) 17 HADR (proj2 (fr_munch_ul _ _ _) MU) HAW) ]. }
    split.
    { (* push 14D: the spill [A + 192] = fragb fr (the cut's cell at A + 192), above the frame and above sp *)
      exists A. split; [unfold rg; rewrite E9; exact Hr9|].
      destruct RW208 as [[_ H208] _]. cbn [LCells.cells_bytes LCells.cbytes] in H208. rewrite app_nil_r in H208.
      unfold q64, fragb. eapply fl_bytes; [exact H208 | exact MU |].
      rewrite length_le8. intros x Hx. apply p4_out; lia. }
    split.
    { (* push 14D: the record ranges (fragb fr, 72) / (fr + 2688, 38): W is application memory *)
      first [ exact (sl_addr_keep mem mem' _ (fragb fr) 72 HADF MU HAW)
            | exact (sl_addr_keep mem mem' _ (fragb fr) 72 HADF (proj1 (fr_munch_ul _ _ _) MU) HAW)
            | exact (sl_addr_keep mem mem' _ (fragb fr) 72 HADF (proj2 (fr_munch_ul _ _ _) MU) HAW) ]. }
    split.
    { first [ exact (sl_addr_keep mem mem' _ (fr + 2688) 38 HADI MU HAW)
            | exact (sl_addr_keep mem mem' _ (fr + 2688) 38 HADI (proj1 (fr_munch_ul _ _ _) MU) HAW)
            | exact (sl_addr_keep mem mem' _ (fr + 2688) 38 HADI (proj2 (fr_munch_ul _ _ _) MU) HAW) ]. }
    split.
    { (* IDBe: the 38 identity bytes [fr + 2688, fr + 2726) are below the destination, apart from the scratch *)
      unfold IDBe in *. eapply fl_bytes; [exact HIDB | exact MU |].
      unfold RcIdentModel.ID0. rewrite repeat_length. unfold RcIdentModel.ID_SIZE.
      intros x Hx. apply p4_out; [lia | destruct Hapart; lia]. }
    split.
    { (* FGBe: the memset leaves 72 zero bytes at D = fr + 2768 *)
      unfold FGBe, z72. destruct RWk as [[_ HFGb] _].
      cbn [LCells.cells_bytes LCells.cbytes] in HFGb. rewrite app_nil_r in HFGb. exact HFGb. }
    exists A, jy, junk2.
    split; [unfold rg; rewrite E9; exact Hr9|].
    split; [lia|].
    split.
    { (* the spill [A + 280] is above the frame and above sp *)
      unfold q64 in *. eapply fl_bytes; [exact H280 | exact MU |].
      rewrite length_le8. intros x Hx. apply p4_out; lia. }
    split.
    { unfold q64 in *. eapply fl_bytes; [exact H240 | exact MU |].
      rewrite length_le8. intros x Hx. apply p4_out; lia. }
    split.
    { (* the code cell fr + 3040 is past the destination [fr + 2768, fr + 2840) and apart from the scratch *)
      eapply LFr.rw_cells_transport; [exact RWy | exact MU | exact WM |].
      simpl. destruct Hapart; repeat match goal with |- _ /\ _ => split end; try exact I; lia. }
    split.
    { eapply LFr.rw_cells_transport; [exact RWj | exact MU | exact WM |].
      simpl. destruct Hapart; repeat match goal with |- _ /\ _ => split end; try exact I; lia. }
    (* round 4: first.sroa.7's 35 bytes at fr + 2880: W is application memory, so no shadow byte changes *)
    first [ exact (sl_addr_keep mem mem' _ (fr + 2880) 35 HAF MU HAW)
          | exact (sl_addr_keep mem mem' _ (fr + 2880) 35 HAF (proj1 (fr_munch_ul _ _ _) MU) HAW)
          | exact (sl_addr_keep mem mem' _ (fr + 2880) 35 HAF (proj2 (fr_munch_ul _ _ _) MU) HAW) ].
Qed.

End P4W.
