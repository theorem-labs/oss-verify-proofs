(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3060 of its 3101 lines of code are new or changed and 207 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/reac_box_catalogue_match.v, with its module paths, module names, addresses and numbers changed; 2488 of its 3291 lines of code are new or changed and 2298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/reac_box_catalogue_match.v, with its module paths and module names changed; 2419 of its 2557 lines of code are new or changed and 3153 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/Tac_slot.v, with its module paths, module names and numbers changed; 927 of its 1102 lines of code are new or changed and 2382 lines of the source are left out. *)
(* Segment F18 of fuzz_ctrl LLVMFuzzerTestOneInput (asan, image A): the range 0x823e8-0x823fc.
   ld a0,240(s1); beqz a0,826b0; li a2,6; ld a0,56(s1); mv a1,s7; jal wrapper_bcmp@0x823fc. Per turn j, from the
   official entry cut Inv_A823e8_at, two exits: [s1+240] <> 0 (t_8819) runs the bcmp to the official Inv_A82400_at
   (F19 entry); [s1+240] = 0 (t_8819 false: the short arm flen < 50 and the long arm without the 0x88 0x19 bytes)
   takes the beqz to 0x8275c (F30 entry, the official Inv_A8275c_at). The wrapper_bcmp shadow check on [s1+56]
   and s7 passes from their addressability. Both exits carry LT = IFS g fr (S j) (aslot push 12B): the entry cut
   gives it and neither arm writes the frame records at fr + 2688 / fr + 2768 or the four first-fragment spills
   (the bcmp call writes only its own stack scratch [sp - K, sp), which lies below the spill base and apart from
   the frame). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Spec Require StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require memcmp_c bcmp_wrap_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcFragLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcIdentModel RcReply.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
Module BW := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.bcmp_wrap_c.
Module MC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.memcmp_c.
Module SF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Spec.StrFun.
Module RF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcFrag.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.

(* The wrapper_bcmp / memcmp constants are the callee contracts' own (a Theorem Labs lane's v1.9 relocation of the _c.v
   files), so the cells this file states and the ones the contracts expect are the same terms. *)
Local Notation BCMP_WRAP_K := BW.BCMP_WRAP_K.
Local Notation BCMP := BW.BCMP.
Local Notation REAL_BCMP := BW.REAL_BCMP.
Local Notation REAL_MEMCMP := BW.REAL_MEMCMP.
Local Notation GOT_CF := BW.GOT_CF.
Local Notation CF := BW.CF.
Local Notation MEMCMP := MC.MEMCMP.
Local Notation memcmp_model := SF.memcmp_model.

Section F18.
Context {fx : YK11.FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis HBC : BW.bcmp_wrap_contract.

Lemma f18_evt :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7v s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A L R : Z) (ls rs : list byte) (w240 vcmp lo : Z),
    s1v = Z_to_bv 64 A -> s7v = Z_to_bv 64 R ->
    0 <= L < 2 ^ 64 -> 0 <= R < 2 ^ 64 ->
    bytes_at rsegs m (A + 240) (le8 (Z_to_bv 64 w240)) -> w240 <> 0 -> 0 <= w240 < 2 ^ 64 ->
    bytes_at rsegs m (A + 72) (le8 (Z_to_bv 64 L)) ->
    bytes_at rsegs m L ls -> (6 <= length ls)%nat ->
    bytes_at rsegs m R rs -> (6 <= length rs)%nat ->
    memcmp_model ls rs 6 = Some vcmp ->
    mem_inv rsegs m -> addressable m L 6 -> addressable m R 6 ->
    app_mem (L + 6) -> app_mem (L + 7) -> app_mem (R + 6) -> app_mem (R + 7) ->
    (L + 6 <= bv_unsigned sp - BCMP_WRAP_K \/ bv_unsigned sp <= L) ->
    (R + 6 <= bv_unsigned sp - BCMP_WRAP_K \/ bv_unsigned sp <= R) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + BCMP_WRAP_K <= bv_unsigned sp ->
    HIGHMEM_BEG <= lo -> bv_unsigned sp <= APPMEM_END ->
    asan_cells m -> shadow_rw m ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    LE.evt rsegs
      (fun ms' => exists (ra' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 vcmp) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 (Z_to_bv 64 R) s8 s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x82400) fc None m' (seg_rom rsegs)
         /\ munch [(bv_unsigned sp - BCMP_WRAP_K, bv_unsigned sp)] m m'
         /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
         /\ asan_cells m' /\ shadow_rw m')
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7v s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x823e8) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7v s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A L R ls rs w240 vcmp lo -> -> HLb HRb H240 Hw240nz Hw240b H72 HBL HLls HBR HLrs Hmm HMI HADL HADR
    HaL6 HaL7 HaR6 HaR7 HdjL HdjR HST Hlo1 Hlo2 Hspa HAC HSW HRB HRM HGC HC254 HC255.
  assert (HL240 : ov_read_bytes rsegs m (wa (A + 240)) 8 = Some (le8 (Z_to_bv 64 w240))).
  { pose proof (bytes_at_ov_read rsegs m (A + 240) (le8 (Z_to_bv 64 w240)) 0 8 H240 ltac:(rewrite length_le8; lia)) as HH.
    cbn [Z.of_nat] in HH. rewrite Z.add_0_r, skipn_O in HH.
    rewrite firstn_all2 in HH by (rewrite length_le8; lia). exact HH. }
  assert (HL72 : ov_read_bytes rsegs m (wa (A + 72)) 8 = Some (le8 (Z_to_bv 64 L))).
  { pose proof (bytes_at_ov_read rsegs m (A + 72) (le8 (Z_to_bv 64 L)) 0 8 H72 ltac:(rewrite length_le8; lia)) as HH.
    cbn [Z.of_nat] in HH. rewrite Z.add_0_r, skipn_O in HH.
    rewrite firstn_all2 in HH by (rewrite length_le8; lia). exact HH. }
  step.
  step.
  replace (bv_eqb (Z_to_bv 64 w240) (Z_to_bv 64 0)) with false
    by (symmetry; apply bv_eqb_neq; intro Eq; apply Hw240nz;
        apply (f_equal bv_unsigned) in Eq; rewrite !unsigned_lit in Eq by lia; exact Eq).
  cbv iota.
  step. step. step. step.
  pose proof HBC as HB. unfold BW.bcmp_wrap_contract, BW.BCMP_WRAP_K in HB. cbv zeta in HB.
  assert (EL : bv_unsigned (Z_to_bv 64 L) = L) by (apply unsigned_lit; lia).
  assert (ER : bv_unsigned (Z_to_bv 64 R) = R) by (apply unsigned_lit; lia).
  assert (E6 : bv_unsigned (Z_to_bv 64 6) = 6) by reflexivity.
  eapply evt_cut.
  { eapply HB with (ls := ls) (rs := rs) (v := vcmp) (lo := lo).
    all: rewrite ?EL, ?ER, ?E6.
    - exact HBL.
    - exact HBR.
    - change (Z.to_nat 6) with 6%nat; exact Hmm.
    - exact HMI.
    - clear; lia.
    - exact HADL.
    - exact HADR.
    - right; exact HaL6.
    - right; exact HaR6.
    - right; exact HaL7.
    - right; exact HaR7.
    - exact HdjL.
    - exact HdjR.
    - exact HST.
    - exact Hlo1.
    - exact Hlo2.
    - exact Hspa.
    - exact HAC.
    - exact HSW.
    - exact HRB.
    - exact HRM.
    - exact HGC.
    - exact HC254.
    - exact HC255. }
  intros ms' (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m'
              & E & MU & WM & MI' & ST' & AC' & SW' & HBpl & HBpr).
  subst ms'.
  replace (ret_pc (Z_to_bv 64 0x82400)) with (Z_to_bv 64 0x82400)
    by (symmetry; apply ret_pc_even; [clear; lia | reflexivity]).
  apply evt_done.
  exists (Z_to_bv 64 0x82400), a1'', a2'', a3'', a4'', a5'', a6'', a7'', t0'', t1'', t2'', t3'', t4'', t5'', t6'', m'.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|].
  split; [exact AC' | exact SW'].
Qed.

(* The [s1+240] = 0 arm: `ld a0,240(s1)` reads 0 and `beqz a0,826b0` is taken. Only a0 changes; memory is kept. *)
Lemma f18_evt0 :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7v s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A : Z),
    s1v = Z_to_bv 64 A ->
    bytes_at rsegs m (A + 240) (le8 (Z_to_bv 64 0)) ->
    LE.evt rsegs
      (fun ms' => ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7v
                              s8 s9 s10 s11 t3 t4 t5 t6)
                           Fr (Z_to_bv 64 0x8275c) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7v s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x823e8) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7v s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A -> H240.
  assert (HL240 : ov_read_bytes rsegs m (wa (A + 240)) 8 = Some (le8 (Z_to_bv 64 0))).
  { pose proof (bytes_at_ov_read rsegs m (A + 240) (le8 (Z_to_bv 64 0)) 0 8 H240 ltac:(rewrite length_le8; lia)) as HH.
    cbn [Z.of_nat] in HH. rewrite Z.add_0_r, skipn_O in HH.
    rewrite firstn_all2 in HH by (rewrite length_le8; lia). exact HH. }
  step.
  step.
  rewrite ?bv_eqb_refl. cbv iota.
  apply evt_done. reflexivity.
Qed.

(* The wrapper_bcmp contract needs mem_inv of its memory, which the cut does not carry (it carries ro_agree only),
   so the call is run on the normalized memory (MemNorm.evt_normalize): every premise is a bytes_at / stk /
   addressable / runtime-cell fact, each of which crosses mem_rel, and the post comes back with ms_rel and ro_same.
   The transfer lemmas below are those of lib/A/Prog/Seg/A1.v (a Theorem Labs lane). *)
Definition seg_tops_below (segs : list Segment) (top : Z) : bool :=
  forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? top) segs.

Lemma rsegs_below_gt : seg_tops_below rsegs AC.GT = true.
Proof. vm_compute. reflexivity. Qed.

Lemma find_segment_below : forall segs top x n s,
  seg_tops_below segs top = true -> find_segment segs x n = Some s -> 0 <= n -> x < top \/ n = 0.
Proof.
  induction segs as [|s0 r IH]; intros top x n s Hb H Hn; cbn in H; [discriminate H|].
  unfold seg_tops_below in Hb. cbn [forallb] in Hb. apply andb_prop in Hb as [H0 Hr].
  apply Z.leb_le in H0.
  destruct (Z.leb (Z.of_N (seg_base s0)) x && Z.leb (x + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0))) eqn:E.
  - apply andb_prop in E as [_ E]. apply Z.leb_le in E. lia.
  - exact (IH top x n s Hr H Hn).
Qed.

(* Above the image there is no read-only byte, so normalizing changes nothing there. *)
Lemma ro_addr_hi : forall a, AC.GT <= a < 2 ^ 64 -> ro_addr rsegs (wa a) = false.
Proof.
  intros a Ha. unfold AC.GT in *. unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.ro_addr.
  match goal with |- context [find_segment ?sg ?x ?n] =>
    destruct (find_segment sg x n) as [s|] eqn:E; [|reflexivity];
    destruct (find_segment_below sg 6283264 x n s rsegs_below_gt E ltac:(cbn; lia)) as [L|L];
    [exfalso; rewrite MState.unsigned_lit in L by lia; lia | cbn in L; lia] end.
Qed.

Lemma wview_rel_hi : forall m m0 a, mem_rel rsegs m m0 -> AC.GT <= a < 2 ^ 64 ->
  (wview rsegs m0 (wa a) <> None <-> wview rsegs m (wa a) <> None).
Proof.
  intros m m0 a HR Ha. rewrite (wview_rel_rw rsegs m m0 (wa a) HR (ro_addr_hi a Ha)). split; auto.
Qed.

Lemma stk_rel_hi : forall m m0 lo hi, mem_rel rsegs m m0 -> AC.GT <= lo -> hi <= 2 ^ 64 ->
  stk rsegs m lo hi -> stk rsegs m0 lo hi.
Proof.
  intros m m0 lo hi HR Hlo Hhi (H0 & H1 & H). unfold AC.GT in *.
  split; [lia|]. split; [lia|]. intros a Ha.
  destruct (H a Ha) as (Hw & b & Hb). split.
  - apply (proj2 (wview_rel_hi m m0 a HR ltac:(unfold AC.GT; lia))). exact Hw.
  - exists b. rewrite <- (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma stk_rel_hi_back : forall m m0 lo hi, mem_rel rsegs m m0 -> AC.GT <= lo -> hi <= 2 ^ 64 ->
  stk rsegs m0 lo hi -> stk rsegs m lo hi.
Proof.
  intros m m0 lo hi HR Hlo Hhi (H0 & H1 & H). unfold AC.GT in *.
  split; [lia|]. split; [lia|]. intros a Ha.
  destruct (H a Ha) as (Hw & b & Hb). split.
  - apply (proj1 (wview_rel_hi m m0 a HR ltac:(unfold AC.GT; lia))). exact Hw.
  - exists b. rewrite (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma shadow_rw_rel : forall m m0, mem_rel rsegs m m0 -> shadow_rw m -> shadow_rw m0.
Proof.
  intros m m0 HR H a Ha. pose proof (in_shadow_range a Ha) as Hr.
  unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Ha.
  destruct (H a Ha) as (Hw & b & Hb). split.
  - apply (proj2 (wview_rel_hi m m0 a HR ltac:(unfold AC.GT; lia))). exact Hw.
  - exists b. rewrite <- (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma addressable_rel : forall m m0 p n, mem_rel rsegs m m0 -> addressable m p n -> addressable m0 p n.
Proof.
  intros m m0 p n HR (H0 & H1 & H2 & H). split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. destruct (H i Hi) as (Hap & b & Hb & Hok). split; [exact Hap|].
  exists b. rewrite <- (mrd_rel rsegs m m0 _ HR). split; [exact Hb | exact Hok].
Qed.

Lemma ba_rel1 : forall m m0 a bs, mem_rel rsegs m m0 -> bytes_at rsegs m a bs -> bytes_at rsegs m0 a bs.
Proof. intros m m0 a bs R H. exact (proj1 (bytes_at_rel rsegs m m0 a bs R) H). Qed.

Lemma asan_cells_rel : forall m m0, mem_rel rsegs m m0 -> asan_cells m -> asan_cells m0.
Proof.
  intros m m0 R H. unfold asan_cells in H |- *.
  repeat match goal with H' : _ /\ _ |- _ => destruct H' end.
  repeat match goal with |- _ /\ _ => split end;
    match goal with |- bytes_at _ _ ?a ?bs => exact (ba_rel1 m m0 a bs R ltac:(assumption)) end.
Qed.

(* f18_evt on the cut's memory, through the normalized memory: ro_agree in place of mem_inv, and the post's
   memory facts carried back across mem_rel / ro_same (the runtime cells of the post are not needed). *)
Lemma f18_evt_ro :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7v s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A L R : Z) (ls rs : list byte) (w240 vcmp lo : Z),
    s1v = Z_to_bv 64 A -> s7v = Z_to_bv 64 R ->
    0 <= L < 2 ^ 64 -> 0 <= R < 2 ^ 64 ->
    bytes_at rsegs m (A + 240) (le8 (Z_to_bv 64 w240)) -> w240 <> 0 -> 0 <= w240 < 2 ^ 64 ->
    bytes_at rsegs m (A + 72) (le8 (Z_to_bv 64 L)) ->
    bytes_at rsegs m L ls -> (6 <= length ls)%nat ->
    bytes_at rsegs m R rs -> (6 <= length rs)%nat ->
    memcmp_model ls rs 6 = Some vcmp ->
    ro_agree rsegs m -> addressable m L 6 -> addressable m R 6 ->
    app_mem (L + 6) -> app_mem (L + 7) -> app_mem (R + 6) -> app_mem (R + 7) ->
    (L + 6 <= bv_unsigned sp - BCMP_WRAP_K \/ bv_unsigned sp <= L) ->
    (R + 6 <= bv_unsigned sp - BCMP_WRAP_K \/ bv_unsigned sp <= R) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + BCMP_WRAP_K <= bv_unsigned sp ->
    HIGHMEM_BEG <= lo -> bv_unsigned sp <= APPMEM_END ->
    asan_cells m -> shadow_rw m ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    LE.evt rsegs
      (fun ms' => exists (ra' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 vcmp) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 (Z_to_bv 64 R) s8 s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x82400) fc None m' (seg_rom rsegs)
         /\ munch [(bv_unsigned sp - BCMP_WRAP_K, bv_unsigned sp)] m m'
         /\ wmono rsegs m m' /\ ro_agree rsegs m' /\ ro_same rsegs m m' /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7v s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x823e8) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7v s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A L R ls rs w240 vcmp lo E1 E7 HLb HRb H240 Hw240nz Hw240b H72 HBL HLls HBR HLrs Hmm HRO HADL HADR
    HaL6 HaL7 HaR6 HaR7 HdjL HdjR HST Hlo1 Hlo2 Hspa HAC HSW HRB HRM HGC HC254 HC255.
  pose proof (mem_rel_normalize rsegs m HRO) as REL.
  assert (Hlo0 : AC.GT <= lo) by (unfold AC.GT, HIGHMEM_BEG in *; lia).
  assert (Hsp64 : bv_unsigned sp <= 2 ^ 64) by (unfold APPMEM_END in Hspa; lia).
  pose proof (f18_evt ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7v s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc (normalize rsegs m) A L R ls rs w240 vcmp lo E1 E7 HLb HRb
    (ba_rel1 m _ _ _ REL H240) Hw240nz Hw240b (ba_rel1 m _ _ _ REL H72) (ba_rel1 m _ _ _ REL HBL) HLls
    (ba_rel1 m _ _ _ REL HBR) HLrs Hmm (mem_inv_normalize rsegs m)
    (addressable_rel m _ _ _ REL HADL) (addressable_rel m _ _ _ REL HADR)
    HaL6 HaL7 HaR6 HaR7 HdjL HdjR (stk_rel_hi m _ lo _ REL Hlo0 Hsp64 HST) Hlo1 Hlo2 Hspa
    (asan_cells_rel m _ REL HAC) (shadow_rw_rel m _ REL HSW)
    (ba_rel1 m _ _ _ REL HRB) (ba_rel1 m _ _ _ REL HRM) (ba_rel1 m _ _ _ REL HGC)
    (ba_rel1 m _ _ _ REL HC254) (ba_rel1 m _ _ _ REL HC255)) as HC.
  pose proof (evt_normalize rsegs _ _ _ _ _ _ m (seg_rom rsegs) ltac:(vm_compute; reflexivity) HRO HC) as HN.
  eapply LE.evt_mono; [exact HN|].
  intros ms (s0' & (ra' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t0' & t1' & t2' & t3' & t4' & t5' & t6' & m0'
              & E & MU & WM & MI' & ST' & AC' & SW') & Hrel & Hros).
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
  split; [exact Hros|].
  exact (stk_rel_hi_back memX m0' lo _ Hmr Hlo0 Hsp64 ST').
Qed.

(* Lib-evt -> SR bridge (sl_run for a Lib.Exec.evt run; sl_run in Tac_slot takes the UL evt and applies ul_entry,
   but the bcmp wrapper contract lives in Lib.Exec, so this segment's run is a Lib.Exec.evt and feeds
   evt_SR_canon_lazy directly). *)
Lemma sl_run_lib : forall regs pc mem md
  (K : bvmap 5 word -> word -> (word -> option byte) -> Prop) (P : config -> Prop),
  m_halted md = None ->
  LE.evt rsegs
    (fun ms => exists R pc' mem', ms = MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs) /\ K R pc' mem')
    (MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None mem (seg_rom rsegs)) ->
  (forall R pc' mem' regs' md', K R pc' mem' -> (forall r, getr regs' r = getr R r) -> AsanLift.mat_le md md' ->
     SR rsegs (mkCfg (mkst regs' pc' mem' (seg_rom rsegs)) md') P) ->
  SR rsegs (mkCfg (mkst regs pc mem (seg_rom rsegs)) md) P.
Proof.
  intros regs pc mem md K P Hh HE HK.
  eapply (AsanLift.evt_SR_canon_lazy rsegs (mkst regs pc mem (seg_rom rsegs)) _ md P); [exact HE | exact Hh |].
  intros ms' md' (can & (R & pc' & mem' & -> & HKR) & Heq) Hmat.
  destruct Heq as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hm & Hrom).
  destruct ms' as [regs' fr' pcv' svc' rv' fc' m' ro'].
  cbn in HR, HF, Hpc, Hsvc, Hres, Hfc, Hm, Hrom. subst.
  apply (HK R _ _ regs' md' HKR); [apply kb_getr_eqv; exact HR | exact Hmat].
Qed.

(* FRA across a run that writes only W (the wrapper_bcmp main-stack scratch, disjoint from the frame body, the
   380 frame shadow bytes, the A-spill cells and the saved window): push 6b dropped mem_inv from FRA and added
   FSREC, so this is now a thin wrapper of Tac_slot's canonical rebuild sl_fr_cl (the callee reaches its own
   mem_inv premise through MemNorm.evt_normalize from ro_agree). *)
Lemma sl_stk_run : forall g fr hb regs regs' mem mem' md W,
  FRA B APIf ra g fr hb regs mem md ->
  Frame.munch W mem mem' -> Frame.wmono rsegs mem mem' -> ro_agree rsegs mem' ->
  all_app W -> rt_disjoint W ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md ->
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md ->
  stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g) ->
  (FSREC fr mem -> FSREC fr mem') ->
  (forall x, fr <= x < fr + FRAME_BYTES -> Frame.outside W x) ->
  (forall x, 0 <= x < HIGHMEM_BEG -> Frame.outside W x) ->
  (forall A, getr regs 9 = Z_to_bv 64 A -> forall x, A + 304 <= x < A + 312 -> Frame.outside W x) ->
  (forall A, getr regs 9 = Z_to_bv 64 A -> forall x, A + 16 <= x < A + 32 -> Frame.outside W x) ->
  (forall x, g_S g - 104 <= x < g_S g -> Frame.outside W x) ->
  (forall x, Sfr fr <= x < Sfr fr + FRAME_SHADOW -> Frame.outside W x) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  FRA B APIf ra g fr hb regs' mem' md.
Proof.
  intros g fr hb regs regs' mem mem' md W HFRA MU WM HRO HAW HD HAH' HSTK HSTKW Hrec' HWframe HWimg HWspill HWsel
    HWsaved HWsh E2 E3 E4 E8 E9 E19 E26.
  apply (sl_fr_cl B APIf ra empty FF g fr hb regs regs' mem mem' md W HFRA MU WM HRO HAW HD HAH' HSTK
    ltac:(intros x Hx; apply HWimg; unfold HIGHMEM_BEG in *; lia)
    ltac:(intros x Hx; apply HWframe; unfold FRAME_BYTES; lia)
    ltac:(intros A' HA' HA'r x Hx; exact (HWspill A' HA' x Hx))
    HWsaved HWsh
    ltac:(intros A' HA' HA'r x Hx; exact (HWsel A' HA' x Hx))
    HSTKW Hrec' E2 E3 E4 E8 E9 E19 E26).
Qed.

(* bytes_at sub-range (local copy of lib.Prog.RcBoxLib.bytes_at_sub, imported qualified would shadow the step engine). *)
Lemma ba_sub : forall m A bs k jj, bytes_at rsegs m A bs -> (k + jj <= length bs)%nat ->
  bytes_at rsegs m (A + Z.of_nat k) (firstn jj (skipn k bs)).
Proof.
  intros m A bs k jj (HA & HL & H) Hkj.
  assert (Lf : length (firstn jj (skipn k bs)) = jj) by (rewrite firstn_length, skipn_length; lia).
  split; [lia|]. split; [rewrite Lf; lia|].
  intros i Hi. rewrite Lf in Hi.
  replace (A + Z.of_nat k + Z.of_nat i) with (A + Z.of_nat (k + i)) by lia.
  rewrite H by lia. rewrite nth_error_firstn. destruct (Nat.ltb_spec0 i jj) as [_|C]; [|lia].
  rewrite nth_error_skipn. reflexivity.
Qed.

(* The first 6 bytes of a carried byte list (the bcmp operands: only these are compared, and only these lie
   outside the wrapper's stack scratch by the cut's disjointness). *)
Lemma ba_first6 : forall m a bs, bytes_at rsegs m a bs -> (6 <= length bs)%nat ->
  bytes_at rsegs m a (firstn 6 bs) /\ length (firstn 6 bs) = 6%nat.
Proof.
  intros m a bs H Hl. split.
  - pose proof (ba_sub m a bs 0 6 H ltac:(lia)) as Hs. cbn [Z.of_nat skipn] in Hs.
    rewrite Z.add_0_r in Hs. exact Hs.
  - rewrite firstn_length. lia.
Qed.

Lemma memcmp_firstn : forall n l r, memcmp_model (firstn n l) (firstn n r) n = memcmp_model l r n.
Proof.
  induction n as [|n IH]; intros [|a l] [|b r]; cbn; try reflexivity.
  destruct (bv_unsigned a =? bv_unsigned b); [apply IH | reflexivity].
Qed.

Lemma out1 : forall lo hi x, (x < lo \/ hi <= x) -> Frame.outside [(lo, hi)] x.
Proof. intros lo hi x H. cbn [Frame.outside]. split; [lia | exact I]. Qed.

(* The a7 is_8819/record invariant at phi (= s7), spills at A (= s1); carried through F18/F19 (the record part of
   a Theorem Labs lane's Inv_A82418_loc, a name not in this delivery), re-assembled at each exit. The parsed-struct pointer kp spilled at [s1+248] is the frame
   address fr + 176 (0x81340 addi a0,s6,176; 0x81344 sd a0,248(s1), s6 = fr), so its field [kp+20, kp+22) is a
   frame byte pair. *)
Lemma bsl_len_le : forall bs k n, (length (RF.bsl bs k n) <= Z.to_nat n)%nat.
Proof. intros bs k n. unfold RF.bsl. rewrite firstn_length. apply Nat.le_min_l. Qed.

(* rec_inv is SlotInv's (identical to the old local copy); use it directly so the official cuts' rec_inv is the
   same constant. rec_inv_kept below is now stated over SlotInv.rec_inv. *)

(* Carry a spill `exists A, rg regs 9 A /\ q64 m (A+off) v` across a munch W that keeps register 9 and misses the
   8 bytes at A+off. Used to thread FLSI across a segment's write window. *)
Lemma spill_keep : forall (regs regs' : bvmap 5 word) (m m' : word -> option byte) (W : list (Z*Z)) off v,
  spill regs m off v -> getr regs' 9 = getr regs 9 -> Frame.munch W m m' ->
  (forall A, rg regs 9 A -> forall x, A + off <= x < A + off + 8 -> Frame.outside W x) ->
  spill regs' m' off v.
Proof.
  intros regs regs' m m' W off v (A & HA & Hq) E9 MU HW.
  exists A. split; [unfold rg in *; rewrite E9; exact HA|].
  unfold q64 in *. eapply fl_bytes; [exact Hq | exact MU |].
  rewrite length_le8. intros x Hx. exact (HW A HA x ltac:(lia)).
Qed.

(* A spill transported across a register change that keeps register 9, on the same memory. *)
Lemma spill_reg : forall (regs regs' : bvmap 5 word) m off v,
  spill regs m off v -> getr regs' 9 = getr regs 9 -> spill regs' m off v.
Proof. intros regs regs' m off v (A & HA & Hq) E9. exists A. split; [unfold rg in *; rewrite E9; exact HA | exact Hq]. Qed.

(* FLSI depends on the register file only through register 9 (the spill base), so a register change that keeps
   register 9 keeps FLSI on the same memory (the 0x8275c arm, where the beqz writes no memory). *)
Lemma flsi_reg : forall g j fr (regs regs' : bvmap 5 word) m,
  FLSI g j fr regs m -> getr regs' 9 = getr regs 9 -> FLSI g j fr regs' m.
Proof.
  intros g j fr regs regs' m HFLSI E9.
  assert (Hsr : forall off v, spill regs m off v -> spill regs' m off v).
  { intros off v (A & HA & Hq). exists A. split; [unfold rg in *; rewrite E9; exact HA | exact Hq]. }
  unfold FLSI, FLSH, PRO, f1_IN, FLC in HFLSI |- *.
  destruct HFLSI as (((Fs40 & Fs120 & Fs136 & Fs160 & Fs168 & Fs176 & Fs208 & Fs248p & Fad & Fpb & Fph &
                       P184 & P256 & P264 & P272 & P32) &
                      Fs128 & Fstk & Fs144 & Fad2691) &
                     Fs216 & Fs224 & Fs248 & (Finp & Finad & Finb) &
                     (Cs256 & Cs184 & Cs192 & Cs80 & Cs88 & Cs96 & Cs272 & Cs264 & Cad1 & Cad2 &
                      Cs72 & Cs64 & Cs56 & Cs48)).
  split.
  { split.
    { split; [exact (Hsr _ _ Fs40)|]. split; [exact (Hsr _ _ Fs120)|]. split; [exact (Hsr _ _ Fs136)|].
      split; [exact (Hsr _ _ Fs160)|]. split; [exact (Hsr _ _ Fs168)|]. split; [exact (Hsr _ _ Fs176)|].
      split; [exact (Hsr _ _ Fs208)|]. split; [exact (Hsr _ _ Fs248p)|]. split; [exact Fad|].
      split; [exact Fpb|]. split; [exact Fph|].
      split; [exact (Hsr _ _ P184)|]. split; [exact (Hsr _ _ P256)|].
      split; [exact (Hsr _ _ P264)|]. split; [exact (Hsr _ _ P272) | exact (Hsr _ _ P32)]. }
    split; [exact (Hsr _ _ Fs128)|]. split; [exact Fstk|].
    split; [exact (Hsr _ _ Fs144) | exact Fad2691]. }
  split; [exact (Hsr _ _ Fs216)|]. split; [exact (Hsr _ _ Fs224)|]. split; [exact (Hsr _ _ Fs248)|].
  split; [split; [exact Finp|]; split; [exact Finad | exact Finb]|].
  split; [exact (Hsr _ _ Cs256)|]. split; [exact (Hsr _ _ Cs184)|]. split; [exact (Hsr _ _ Cs192)|].
  split; [exact (Hsr _ _ Cs80)|]. split; [exact (Hsr _ _ Cs88)|]. split; [exact (Hsr _ _ Cs96)|].
  split; [exact (Hsr _ _ Cs272)|]. split; [exact (Hsr _ _ Cs264)|].
  split; [exact Cad1|]. split; [exact Cad2|].
  split; [exact (Hsr _ _ Cs72)|]. split; [exact (Hsr _ _ Cs64)|].
  split; [exact (Hsr _ _ Cs56) | exact (Hsr _ _ Cs48)].
Qed.

(* FLSI across a write window W that keeps register 9, misses the spill cells [A+32, A+280) (FLSH's, FLSI's and
   FLC's: the lowest is PRO's v1.9 [A + 32] = fr + 2880, the highest [A + 272, A + 280)), the frame body
   [fr, fr + FRAME_BYTES) (for stk and FLC's ranges) and the harness block's bytes (for f1_IN). The caller gives
   the harness-block-outside premise, discharged from a_laws_blocks (`g_p + g_n <= stklo`, g_n = length (g_in g)
   by definition). *)
Lemma flsi_keep : forall g j fr (regs regs' : bvmap 5 word) m m' (W : list (Z*Z)),
  FLSI g j fr regs m -> getr regs' 9 = getr regs 9 ->
  Frame.munch W m m' -> all_app W -> Frame.wmono rsegs m m' ->
  (forall A, rg regs 9 A -> forall x, A + 32 <= x < A + 280 -> Frame.outside W x) ->
  (forall x, fr <= x < fr + FRAME_BYTES -> Frame.outside W x) ->
  (forall x, g_p g <= x < g_p g + Z.of_nat (length (g_in g)) -> Frame.outside W x) ->
  FLSI g j fr regs' m'.
Proof.
  intros g j fr regs regs' m m' W HFLSI E9 MU HAW WM HWsp HWfr HWin.
  assert (HSK : forall off v, 32 <= off <= 272 -> spill regs m off v -> spill regs' m' off v).
  { intros off v Hoff Hsp. apply (spill_keep regs regs' m m' W off v Hsp E9 MU).
    intros A HA x Hx. apply (HWsp A HA x). lia. }
  unfold FLSI, FLSH, PRO, f1_IN, FLC in HFLSI |- *.
  destruct HFLSI as (((Fs40 & Fs120 & Fs136 & Fs160 & Fs168 & Fs176 & Fs208 & Fs248p & Fad & Fpb & Fph &
                       P184 & P256 & P264 & P272 & P32) &
                      Fs128 & Fstk & Fs144 & Fad2691) &
                     Fs216 & Fs224 & Fs248 & (Finp & Finad & Finb) &
                     (Cs256 & Cs184 & Cs192 & Cs80 & Cs88 & Cs96 & Cs272 & Cs264 & Cad1 & Cad2 &
                      Cs72 & Cs64 & Cs56 & Cs48)).
  split.
  { split.
    { split; [exact (HSK 40 _ ltac:(lia) Fs40)|].
      split; [exact (HSK 120 _ ltac:(lia) Fs120)|].
      split; [exact (HSK 136 _ ltac:(lia) Fs136)|].
      split; [exact (HSK 160 _ ltac:(lia) Fs160)|].
      split; [exact (HSK 168 _ ltac:(lia) Fs168)|].
      split; [exact (HSK 176 _ ltac:(lia) Fs176)|].
      split; [exact (HSK 208 _ ltac:(lia) Fs208)|].
      split; [exact (HSK 248 _ ltac:(lia) Fs248p)|].
      split; [eapply sl_addr_keep; [exact Fad | exact MU | exact HAW]|].
      split; [apply (fl_bytes W m m' (g_p g) (g_in g) Fpb MU); exact HWin|].
      split.
      { intros Hn. destruct (Fph Hn) as (Fin & Fad2). split; [exact Fin|].
        eapply sl_addr_keep; [exact Fad2 | exact MU | exact HAW]. }
      split; [exact (HSK 184 _ ltac:(lia) P184)|]. split; [exact (HSK 256 _ ltac:(lia) P256)|].
      split; [exact (HSK 264 _ ltac:(lia) P264)|].
      split; [exact (HSK 272 _ ltac:(lia) P272) | exact (HSK 32 _ ltac:(lia) P32)]. }
    split; [exact (HSK 128 _ ltac:(lia) Fs128)|].
    split.
    { eapply (Frame.stk_transport rsegs _ m m'); [exact Fstk | exact MU | exact WM |].
      intros x Hx. left. apply HWfr. lia. }
    split; [exact (HSK 144 _ ltac:(lia) Fs144)|].
    eapply sl_addr_keep; [exact Fad2691 | exact MU | exact HAW]. }
  split; [exact (HSK 216 _ ltac:(lia) Fs216)|].
  split; [exact (HSK 224 _ ltac:(lia) Fs224)|].
  split; [exact (HSK 248 _ ltac:(lia) Fs248)|].
  split.
  { split; [exact Finp|].
    split; [eapply sl_addr_keep; [exact Finad | exact MU | exact HAW]|].
    apply (fl_bytes W m m' (g_p g) (g_in g) Finb MU). exact HWin. }
  split; [exact (HSK 256 _ ltac:(lia) Cs256)|]. split; [exact (HSK 184 _ ltac:(lia) Cs184)|].
  split; [exact (HSK 192 _ ltac:(lia) Cs192)|]. split; [exact (HSK 80 _ ltac:(lia) Cs80)|].
  split; [exact (HSK 88 _ ltac:(lia) Cs88)|]. split; [exact (HSK 96 _ ltac:(lia) Cs96)|].
  split; [exact (HSK 272 _ ltac:(lia) Cs272)|]. split; [exact (HSK 264 _ ltac:(lia) Cs264)|].
  split; [eapply sl_addr_keep; [exact Cad1 | exact MU | exact HAW]|].
  split; [eapply sl_addr_keep; [exact Cad2 | exact MU | exact HAW]|].
  split; [exact (HSK 72 _ ltac:(lia) Cs72)|]. split; [exact (HSK 64 _ ltac:(lia) Cs64)|].
  split; [exact (HSK 56 _ ltac:(lia) Cs56) | exact (HSK 48 _ ltac:(lia) Cs48)].
Qed.

Lemma rec_inv_kept : forall g j fr phi A m m' W,
  rec_inv g j fr phi A m -> Frame.munch W m m' ->
  (forall x, phi <= x < phi + 50 -> Frame.outside W x) ->
  (forall x, A + 200 <= x < A + 288 -> Frame.outside W x) ->
  (forall x, 0 <= x < HIGHMEM_BEG -> Frame.outside W x) ->
  (forall x, fr + 196 <= x < fr + 198 -> Frame.outside W x) ->
  rec_inv g j fr phi A m'.
Proof.
  intros g j fr phi A m m' W (Hp0 & Hp50 & Hfl & Htk & Hpap & H192 & H18 & H34 &
     field16 & v14 & v15 & v16 & v17 & Hkp & H280 & Hf16 & Hb14 & Hb15 & Hb16 & Hb17 &
     Rv14 & Rv15 & Rv16 & Rv17 & Hs14 & Hs15 & Hs16 & Hs17 & Heq1 & Heq2)
    MU OWphi OWspill OWimg OWkp.
  assert (SHlo : forall t, 14 <= t <= 17 -> 0 <= Z.shiftr (phi + t) 3 + ASAN_K < HIGHMEM_BEG).
  { intros t Ht. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    pose proof (shadow_of_app (phi + t) (Hpap (phi + t) ltac:(lia))) as His.
    unfold shadow_addr, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG, ASAN_K in *.
    destruct His as [His|His]; lia. }
  unfold rec_inv.
  split; [exact Hp0|]. split; [exact Hp50|]. split; [exact Hfl|]. split; [exact Htk|]. split; [exact Hpap|].
  split; [unfold q64 in *; eapply fl_bytes; [exact H192 | exact MU | rewrite length_le8; intros x Hx; apply OWspill; lia]|].
  split; [eapply fl_bytes; [exact H18 | exact MU | intros x Hx; apply OWphi; unfold t_blk in Hx;
            pose proof (bsl_len_le (t_g (g_in g) j) 18 32) as BL; change (Z.to_nat 32) with 32%nat in BL; lia]|].
  split; [eapply fl_bytes; [exact H34 | exact MU | intros x Hx; apply OWphi;
            pose proof (bsl_len_le (t_g (g_in g) j) 34 6) as BL; change (Z.to_nat 6) with 6%nat in BL; lia]|].
  exists field16, v14, v15, v16, v17.
  split; [unfold q64 in *; eapply fl_bytes; [exact Hkp | exact MU | rewrite length_le8; intros x Hx; apply OWspill; lia]|].
  split; [unfold q64 in *; eapply fl_bytes; [exact H280 | exact MU | rewrite length_le8; intros x Hx; apply OWspill; lia]|].
  split; [unfold u16 in *; eapply fl_bytes; [exact Hf16 | exact MU | rewrite length_le2; intros x Hx; apply OWkp; lia]|].
  split; [unfold b8 in *; eapply fl_bytes; [exact Hb14 | exact MU | cbn [length]; intros x Hx; apply OWphi; lia]|].
  split; [unfold b8 in *; eapply fl_bytes; [exact Hb15 | exact MU | cbn [length]; intros x Hx; apply OWphi; lia]|].
  split; [unfold b8 in *; eapply fl_bytes; [exact Hb16 | exact MU | cbn [length]; intros x Hx; apply OWphi; lia]|].
  split; [unfold b8 in *; eapply fl_bytes; [exact Hb17 | exact MU | cbn [length]; intros x Hx; apply OWphi; lia]|].
  split; [exact Rv14|]. split; [exact Rv15|]. split; [exact Rv16|]. split; [exact Rv17|].
  split; [unfold b8 in *; eapply fl_bytes; [exact Hs14 | exact MU | cbn [length]; intros x Hx; apply OWimg; pose proof (SHlo 14 ltac:(lia)); lia]|].
  split; [unfold b8 in *; eapply fl_bytes; [exact Hs15 | exact MU | cbn [length]; intros x Hx; apply OWimg; pose proof (SHlo 15 ltac:(lia)); lia]|].
  split; [unfold b8 in *; eapply fl_bytes; [exact Hs16 | exact MU | cbn [length]; intros x Hx; apply OWimg; pose proof (SHlo 16 ltac:(lia)); lia]|].
  split; [unfold b8 in *; eapply fl_bytes; [exact Hs17 | exact MU | cbn [length]; intros x Hx; apply OWimg; pose proof (SHlo 17 ltac:(lia)); lia]|].
  split; [exact Heq1|]. exact Heq2.
Qed.

(* The two halves of rec_inv (push 15) across a write window: rec_inv0 names the record bytes at phi + 18 /
   phi + 34 and the spills [A + 200] / [A + 248] / [A + 280]; rec_parse names the bytes phi + 14 .. phi + 17, their
   shadow bytes (low memory, as phi is app memory) and the u16 at fr + 196. *)
Lemma rec_inv0_kept : forall g j fr phi A m m' W,
  rec_inv0 g j fr phi A m -> Frame.munch W m m' ->
  (forall x, phi <= x < phi + 50 -> Frame.outside W x) ->
  (forall x, A + 200 <= x < A + 288 -> Frame.outside W x) ->
  rec_inv0 g j fr phi A m'.
Proof.
  intros g j fr phi A m m' W (Hp0 & Hp50 & Hfl & Htk & Hpap & H192 & H18 & H34 & Hkp & H280) MU OWphi OWspill.
  unfold rec_inv0.
  split; [exact Hp0|]. split; [exact Hp50|]. split; [exact Hfl|]. split; [exact Htk|]. split; [exact Hpap|].
  split; [unfold q64 in *; eapply fl_bytes; [exact H192 | exact MU | rewrite length_le8; intros x Hx; apply OWspill; lia]|].
  split; [eapply fl_bytes; [exact H18 | exact MU | intros x Hx; apply OWphi; unfold t_blk in Hx;
            pose proof (bsl_len_le (t_g (g_in g) j) 18 32) as BL; change (Z.to_nat 32) with 32%nat in BL; lia]|].
  split; [eapply fl_bytes; [exact H34 | exact MU | intros x Hx; apply OWphi;
            pose proof (bsl_len_le (t_g (g_in g) j) 34 6) as BL; change (Z.to_nat 6) with 6%nat in BL; lia]|].
  split; [unfold q64 in *; eapply fl_bytes; [exact Hkp | exact MU | rewrite length_le8; intros x Hx; apply OWspill; lia]|].
  unfold q64 in *; eapply fl_bytes; [exact H280 | exact MU | rewrite length_le8; intros x Hx; apply OWspill; lia].
Qed.

Lemma rec_parse_kept : forall g j fr phi m m' W,
  rec_parse g j fr phi m -> (forall a, phi <= a < phi + 50 -> app_mem a) -> Frame.munch W m m' ->
  (forall x, phi <= x < phi + 50 -> Frame.outside W x) ->
  (forall x, 0 <= x < HIGHMEM_BEG -> Frame.outside W x) ->
  (forall x, fr + 196 <= x < fr + 198 -> Frame.outside W x) ->
  rec_parse g j fr phi m'.
Proof.
  intros g j fr phi m m' W (field16 & v14 & v15 & v16 & v17 & Hf16 & Hb14 & Hb15 & Hb16 & Hb17 &
     Rv14 & Rv15 & Rv16 & Rv17 & Hs14 & Hs15 & Hs16 & Hs17 & Heq1 & Heq2) Hpap MU OWphi OWimg OWkp.
  assert (SHlo : forall t, 14 <= t <= 17 -> 0 <= Z.shiftr (phi + t) 3 + ASAN_K < HIGHMEM_BEG).
  { intros t Ht. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    pose proof (shadow_of_app (phi + t) (Hpap (phi + t) ltac:(lia))) as His.
    unfold shadow_addr, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG, ASAN_K in *.
    destruct His as [His|His]; lia. }
  exists field16, v14, v15, v16, v17.
  split; [unfold u16 in *; eapply fl_bytes; [exact Hf16 | exact MU | rewrite length_le2; intros x Hx; apply OWkp; lia]|].
  split; [unfold b8 in *; eapply fl_bytes; [exact Hb14 | exact MU | cbn [length]; intros x Hx; apply OWphi; lia]|].
  split; [unfold b8 in *; eapply fl_bytes; [exact Hb15 | exact MU | cbn [length]; intros x Hx; apply OWphi; lia]|].
  split; [unfold b8 in *; eapply fl_bytes; [exact Hb16 | exact MU | cbn [length]; intros x Hx; apply OWphi; lia]|].
  split; [unfold b8 in *; eapply fl_bytes; [exact Hb17 | exact MU | cbn [length]; intros x Hx; apply OWphi; lia]|].
  split; [exact Rv14|]. split; [exact Rv15|]. split; [exact Rv16|]. split; [exact Rv17|].
  split; [unfold b8 in *; eapply fl_bytes; [exact Hs14 | exact MU | cbn [length]; intros x Hx; apply OWimg; pose proof (SHlo 14 ltac:(lia)); lia]|].
  split; [unfold b8 in *; eapply fl_bytes; [exact Hs15 | exact MU | cbn [length]; intros x Hx; apply OWimg; pose proof (SHlo 15 ltac:(lia)); lia]|].
  split; [unfold b8 in *; eapply fl_bytes; [exact Hs16 | exact MU | cbn [length]; intros x Hx; apply OWimg; pose proof (SHlo 16 ltac:(lia)); lia]|].
  split; [unfold b8 in *; eapply fl_bytes; [exact Hs17 | exact MU | cbn [length]; intros x Hx; apply OWimg; pose proof (SHlo 17 ltac:(lia)); lia]|].
  split; [exact Heq1|]. exact Heq2.
Qed.

(* ---- The model lengths of the two frame records and the transport of LT = IFS g fr (S j).
   Both records sit in the frame body: the identity record is 38 bytes at fr + 2688 and the fragment record 72
   bytes at fr + 2768, at EVERY turn, because each model step keeps the length (the ingest by ING_length, the
   fragment record by fg_next_length). A run that writes only outside [fr + 2688, fr + 2840) and outside the
   first-fragment spill window [A + 88, A + 120) therefore keeps LT whole; the four spills move with the spill
   base s1 and FI is a pure model fact. *)
Lemma f18_rp_id_length : forall idb len g, length idb = 38%nat -> length (rp_id idb len g) = 38%nat.
Proof.
  intros idb len g H. unfold rp_id.
  destruct (RcReply.ir len g); [apply RcIdentModel.ING_length; exact H | exact H].
Qed.

Lemma f18_fg_id_length : forall idb len st g, length idb = 38%nat -> length (fg_id idb len st g) = 38%nat.
Proof.
  intros idb len st g H. unfold fg_id.
  destruct (fg_rf len st g =? 1); [apply RcIdentModel.ING_length; exact H | exact H].
Qed.

Lemma f18_t_ID_length : forall inp j, length (t_ID inp j) = 38%nat.
Proof.
  intros inp j. induction j as [|j IH].
  - reflexivity.
  - unfold t_ID in *. rewrite fst_at_S. unfold turn.
    destruct (f_opens (t_len inp j) (t_g inp j)); cbn [fs_id];
      apply f18_fg_id_length, f18_rp_id_length; exact IH.
Qed.

Lemma f18_first_length : forall st g, length st = 72%nat -> length g = 50%nat -> 1 <= RF.fg_n g <= 22 ->
  length (RF.fg_first st g) = 72%nat.
Proof.
  intros st g HL HG Hn. unfold RF.fg_first, RF.fg_body.
  rewrite !length_app, length_skipn, (rf_bsl_length g 6 6), (rf_bsl_length g 27 (RF.fg_n g)) by lia.
  cbn [length]. lia.
Qed.

Lemma f18_fr_fg_n : forall len g, RF.fg_fr len g = true -> 1 <= RF.fg_n g <= 22.
Proof.
  intros len g H. unfold RF.fg_fr in H. rewrite !andb_true_iff in H.
  destruct H as (H & _). destruct H as (H & Hn2). destruct H as (_ & Hn1).
  apply Z.leb_le in Hn1. apply Z.leb_le in Hn2. lia.
Qed.

Lemma f18_keep_T : forall st g, RF.fg_keep st g = true -> RF.fg_T st g <= 64.
Proof.
  intros st g H. unfold RF.fg_keep in H. rewrite !andb_true_iff in H.
  destruct H as (_ & H). apply Z.leb_le in H. lia.
Qed.

Lemma f18_fg_next_length : forall f fr pa pp pn len st g, length st = 72%nat -> length g = 50%nat ->
  length (fg_next st g (RF.fg_class f fr pa pp pn len st g)) = 72%nat.
Proof.
  intros f fr pa pp pn len st g HL HG. unfold RF.fg_class.
  destruct ((f =? 0) || (fr =? 0) || (pa =? 0) || (pp =? 0) || (pn =? 0)); [cbn [fg_next]; exact HL|].
  destruct (RF.fg_fr len g) eqn:FR; cbn [negb]; [|cbn [fg_next]; exact HL].
  destruct (RF.bat g 19 =? 1).
  - cbn [fg_next]. apply f18_first_length; [exact HL | exact HG | apply (f18_fr_fg_n len); exact FR].
  - destruct (RF.fg_keep st g) eqn:KEEP; cbn [negb]; [|cbn [fg_next]; apply rf_clear_length; exact HL].
    destruct (RF.fg_close st g); cbn [negb fg_next]; apply rf_clear_length, rf_fg_join_length;
      solve [exact HL | exact HG | apply (f18_fr_fg_n len); exact FR | apply f18_keep_T; exact KEEP].
Qed.

Lemma f18_t_g_length : forall inp j, length (t_g inp j) = 50%nat.
Proof. intros inp j. unfold t_g. apply fr50_length. Qed.

Lemma f18_t_FG_length : forall inp j, length (t_FG inp j) = 72%nat.
Proof.
  intros inp j. induction j as [|j IH].
  - reflexivity.
  - unfold t_FG in *. rewrite fst_at_S. unfold turn.
    destruct (f_opens (t_len inp j) (t_g inp j)); cbn [fs_fg]; unfold fg_st, fcls;
      apply (f18_fg_next_length 1 1 1 1 1); solve [exact IH | apply f18_t_g_length].
Qed.

(* The first fragment's body never exceeds the 35 bytes of `first.sroa.7`: a turn that opens the record stores
   `firstn (bat gg 26) (skipn 27 gg)` with 1 <= bat gg 26 <= 22 (fg_fr, which f_opens requires), and every other
   turn keeps the previous body. *)
Lemma f18_fsbody_length : forall inp j, (length (fs_body (fst_at inp j)) <= 35)%nat.
Proof.
  intros inp j. induction j as [|j IH].
  - cbn [fst_at fs0 fs_body length]. lia.
  - rewrite fst_at_S. unfold turn.
    destruct (f_opens (t_len inp j) (t_g inp j)) eqn:EOP; cbn [fs_body]; [|exact IH].
    rewrite length_firstn.
    assert (HFR : RF.fg_fr (t_len inp j) (t_g inp j) = true)
      by (unfold f_opens in EOP; apply andb_prop in EOP; exact (proj1 EOP)).
    pose proof (f18_fr_fg_n _ _ HFR) as Hn. unfold RF.fg_n in Hn. lia.
Qed.

(* LT across a register change that keeps the spill base s1 (memory unchanged): the 0x8275c arm. *)
Lemma f18_lt_reg : forall g fr j (regs regs' : bvmap 5 word) m,
  LT g fr j regs m -> getr regs' 9 = getr regs 9 -> LT g fr j regs' m.
Proof.
  intros g fr j regs regs' m HLT E9.
  destruct HLT as ((Hid & Hidok) & (Hfg & Hfgok) & H104 & H112 & Hbody & Hbad & HFI).
  split; [split; [exact Hid | exact Hidok]|].
  split; [split; [exact Hfg | exact Hfgok]|].
  split; [exact (spill_reg regs regs' m _ _ H104 E9)|].
  split; [exact (spill_reg regs regs' m _ _ H112 E9)|].
  split; [exact Hbody|]. split; [exact Hbad | exact HFI].
Qed.

(* LT across a run that keeps s1 and writes only outside the frame records and the two first-fragment spills:
   the bcmp arm. The frame window covers the identity record (fr + 2688, 38 bytes), the fragment record
   (fr + 2768, 72) and the first fragment's body (fr + 2880, at most 35), whose shadow the addressability
   names; v1.9's FSb holds the body in the frame, not in two spill words. *)
Lemma f18_lt_keep : forall g fr j (regs regs' : bvmap 5 word) m m' (W : list (Z*Z)),
  LT g fr j regs m -> getr regs' 9 = getr regs 9 -> Frame.munch W m m' -> all_app W ->
  (forall x, fr + 2688 <= x < fr + 2915 -> Frame.outside W x) ->
  (forall A, rg regs 9 A -> forall x, A + 104 <= x < A + 120 -> Frame.outside W x) ->
  LT g fr j regs' m'.
Proof.
  intros g fr j regs regs' m m' W HLT E9 MU HAW Hfrw HAw.
  destruct HLT as ((Hid & Hidok) & (Hfg & Hfgok) & H104 & H112 & Hbody & Hbad & HFI).
  split.
  { split; [|exact Hidok].
    eapply fl_bytes; [exact Hid | exact MU |].
    rewrite f18_t_ID_length. intros x Hx. apply Hfrw. lia. }
  split.
  { split; [|exact Hfgok].
    eapply fl_bytes; [exact Hfg | exact MU |].
    rewrite f18_t_FG_length. intros x Hx. apply Hfrw. lia. }
  split; [apply (spill_keep regs regs' m m' W 104 _ H104 E9 MU);
          intros A HA x Hx; apply (HAw A HA x); lia|].
  split; [apply (spill_keep regs regs' m m' W 112 _ H112 E9 MU);
          intros A HA x Hx; apply (HAw A HA x); lia|].
  split.
  { eapply fl_bytes; [exact Hbody | exact MU |].
    intros x Hx. apply Hfrw.
    pose proof (f18_fsbody_length (g_in g) (S j)) as HB. lia. }
  split; [|exact HFI].
  eapply sl_addr_keep; [exact Hbad | exact MU | exact HAW].
Qed.

(* FRA and ENT across one wrapper_bcmp call from a FRA cut: the call writes only its main-stack scratch
   W = [sp - K, sp) (disjoint from the frame by fra_frame, below the spill base A, above the low image
   and the shadow), keeps the FRA registers, keeps the entry-anchored slot window (outside W from mem, inside W
   from the call's stk post on [sp - FN_STACK, sp)), and materializes pages (mat_le). W lies inside the slot
   window, so ENT crosses it with ent_store (the stack bounds and the runtime's ownership are kept by
   a_laws_store) and then ent_mat. mem_inv of mem' is FRA's own, moved by the call's ro_same. Shared by seg_F18
   and seg_F19. *)
Lemma bcmp_fra : forall g fr hb regs regs' mem mem' md md' A,
  FRA B APIf ra g fr hb regs mem md -> ENT APIf g hb mem md ->
  rg regs 9 A -> 0 <= A < 2 ^ 64 -> AC.aspZ regs <= A ->
  Frame.munch [(AC.aspZ regs - BCMP_WRAP_K, AC.aspZ regs)] mem mem' ->
  Frame.wmono rsegs mem mem' -> ro_agree rsegs mem' -> ro_same rsegs mem mem' ->
  stk rsegs mem' (AC.aspZ regs - FN_STACK) (AC.aspZ regs) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  AsanLift.mat_le md md' ->
  FRA B APIf ra g fr hb regs' mem' md' /\ ENT APIf g hb mem' md'.
Proof.
  intros g fr hb regs regs' mem mem' md md' A HFRA HENT Hs1 HAb HspA MU WM HroM Hros HSTKW
    Fr2 Fr3 Fr4 Fr8 Fr9 Fr19 Fr26 Hmat.
  pose proof (eq_refl : FRAME_BYTES = 3136) as HFB. pose proof (eq_refl : FRAME_SHADOW = 392) as HFS.
  destruct (fra_frame B APIf ra g fr hb regs mem md HFRA) as (Hfrw & _ & _ & _).
  destruct (fra_app B APIf ra g fr hb regs mem md HFRA) as (HGTfr & Hfrapp).
  assert (Hdisjfr : fr + FRAME_BYTES <= AC.aspZ regs - BCMP_WRAP_K \/ AC.aspZ regs <= fr)
    by (apply Hfrw; unfold FN_STACK, BCMP_WRAP_K, AF.SLOT_STACK; lia).
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (A2 & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspillq & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hshf & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS (hb ++ g_H g) mem md HAH) as Hstkhi.
  assert (Hsphi : HIGHMEM_BEG + AF.SLOT_STACK - 4096 < sp) by lia.
  assert (HSTKS : stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g)).
  { destruct (stk_split rsegs mem (g_S g - AF.SLOT_STACK) (AC.aspZ regs - BCMP_WRAP_K) (g_S g) Hwin
                ltac:(rewrite Haspz; unfold BCMP_WRAP_K, AF.SLOT_STACK in *; lia)) as (Hw1 & Hw2).
    destruct (stk_split rsegs mem (AC.aspZ regs - BCMP_WRAP_K) (AC.aspZ regs) (g_S g) Hw2
                ltac:(rewrite Haspz; unfold BCMP_WRAP_K; lia)) as (_ & Hw3).
    destruct (stk_split rsegs mem' (AC.aspZ regs - FN_STACK) (AC.aspZ regs - BCMP_WRAP_K) (AC.aspZ regs) HSTKW
                ltac:(unfold BCMP_WRAP_K, FN_STACK, AF.SLOT_STACK; lia)) as (_ & HwW).
    assert (Hw1' : stk rsegs mem' (g_S g - AF.SLOT_STACK) (AC.aspZ regs - BCMP_WRAP_K)).
    { eapply (Frame.stk_transport rsegs _ mem mem'); [exact Hw1 | exact MU | exact WM |].
      intros x Hx. left. apply out1. lia. }
    assert (Hw3' : stk rsegs mem' (AC.aspZ regs) (g_S g)).
    { eapply (Frame.stk_transport rsegs _ mem mem'); [exact Hw3 | exact MU | exact WM |].
      intros x Hx. left. apply out1. lia. }
    apply (stk_merge rsegs mem' _ (AC.aspZ regs) _); [| exact Hw3' | rewrite Haspz; unfold BCMP_WRAP_K, AF.SLOT_STACK in *; lia].
    apply (stk_merge rsegs mem' _ (AC.aspZ regs - BCMP_WRAP_K) _); [exact Hw1' | exact HwW |].
    rewrite Haspz; unfold BCMP_WRAP_K, AF.SLOT_STACK in *; lia. }
  assert (Hwlo : AC.GT <= AC.aspZ regs - BCMP_WRAP_K)
    by (rewrite Haspz in *; unfold AC.GT, BCMP_WRAP_K, HIGHMEM_BEG, AF.SLOT_STACK in *; lia).
  set (W := [(AC.aspZ regs - BCMP_WRAP_K, AC.aspZ regs)]).
  assert (HWin : forall x, 0 <= x < 2 ^ 64 -> Frame.outside W x \/ (g_S g - AF.SLOT_STACK <= x < g_S g) \/
            (fr <= x < fr + FRAME_BYTES) \/ (Sfr fr <= x < Sfr fr + FRAME_SHADOW)).
  { intros x Hx. subst W.
    destruct (Z_le_gt_dec (AC.aspZ regs - BCMP_WRAP_K) x) as [D1|D1];
      [destruct (Z_lt_ge_dec x (AC.aspZ regs)) as [D2|D2]|].
    - right; left. rewrite Haspz in *. unfold BCMP_WRAP_K, AF.SLOT_STACK in *. lia.
    - left. apply out1. right. lia.
    - left. apply out1. left. lia. }
  assert (Hallapp : all_app W).
  { subst W. cbn [all_app]. split; [|exact I]. intros a Ha. unfold app_mem. right.
    rewrite Haspz in *. unfold BCMP_WRAP_K, HIGHMEM_BEG, APPMEM_END, AF.SLOT_STACK in *. lia. }
  assert (Hrtdj : rt_disjoint W).
  { subst W. unfold rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
      RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB,
      RT_AGLOB_LEN, AC.GT, BCMP_WRAP_K in *.
    rewrite Haspz in *. cbn [disjoint_from]. repeat split; first [left; lia | exact I]. }
  assert (HstoreC : forall a, 0 <= a < 2 ^ 64 ->
    ~ AC.a_store_ok (hb ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
    mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
  { intros a Ha Hns. apply MU. rewrite MState.unsigned_lit by lia.
    cbn [Frame.outside]. split; [|exact I]. intros [HH1 HH2]. apply Hns.
    unfold AC.a_store_ok. right; left. rewrite Haspz in *.
    unfold BCMP_WRAP_K, AF.SLOT_STACK in *. split; lia. }
  assert (HwmL : forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a)
    by (intros a Ha Hw; exact (WM (Z_to_bv 64 a) Hw)).
  pose proof (lw_store (APIf rc) (hb ++ g_H g) mem mem' md HAH HstoreC HwmL) as LWS.
  pose proof (lws_ah _ _ _ _ _ LWS) as HAH'. pose proof (lws_own _ _ _ _ _ LWS) as Hown'.
  pose proof (lws_lo _ _ _ _ _ LWS) as HSTKeq. pose proof (lws_hi _ _ _ _ _ LWS) as HSTKHI.
  assert (HA9 : forall A', getr regs 9 = Z_to_bv 64 A' -> forall x, A' <= x < A' + 416 -> Frame.outside W x).
  { intros A' HA' x Hx. subst W. cbn [Frame.outside]. split; [|exact I]. intros [HH1 HH2].
    assert (Hb' : 0 <= A' < 2 ^ 64)
      by (rewrite Haspz in *; unfold BCMP_WRAP_K, HIGHMEM_BEG, APPMEM_END, AF.SLOT_STACK in *; lia).
    assert (EA' : A' = A).
    { assert (E : Z_to_bv 64 A' = Z_to_bv 64 A) by (unfold rg in Hs1; rewrite <- HA'; exact Hs1).
      apply (f_equal (bv_unsigned (n:=64))) in E. rewrite !MState.unsigned_lit in E by lia. exact E. }
    subst A'. lia. }
  assert (Hrec' : FSREC fr mem -> FSREC fr mem').
  { intro HF. eapply fsrec_munch_lo; [exact HF | exact HAH | exact MU | |].
    - intros x Hx. subst W. apply out1. left.
      unfold AC.GT, BCMP_WRAP_K, HIGHMEM_BEG, AF.SLOT_STACK in *. rewrite Haspz in *. lia.
    - intros x Hxapp Hxnfr Hxlo. subst W. apply out1. left.
      rewrite Haspz in *. unfold BCMP_WRAP_K, AF.SLOT_STACK in *. lia. }
  assert (HFRA' : FRA B APIf ra g fr hb regs' mem' md).
  { apply (sl_stk_run g fr hb regs regs' mem mem' md W HFRA MU WM HroM Hallapp Hrtdj HAH' HSTKeq HSTKS Hrec').
    - intros x Hx. subst W. cbn [Frame.outside]. split; [|exact I]. intros [HH1 HH2].
      rewrite Haspz in *. destruct Hdisjfr as [Hd|Hd]; unfold BCMP_WRAP_K in *; lia.
    - intros x Hx. subst W. cbn [Frame.outside]. split; [|exact I]. intros [HH1 HH2].
      rewrite Haspz in *. unfold BCMP_WRAP_K, HIGHMEM_BEG, AF.SLOT_STACK in *. lia.
    - intros A' HA' x Hx. apply (HA9 A' HA' x). lia.
    - intros A' HA' x Hx. apply (HA9 A' HA' x). lia.
    - intros x Hx. subst W. cbn [Frame.outside]. split; [|exact I]. intros [HH1 HH2].
      rewrite Haspz in *. unfold BCMP_WRAP_K in *. lia.
    - intros x Hx. subst W. cbn [Frame.outside]. split; [|exact I]. intros [HH1 HH2].
      assert (Hin : in_shadow x).
      { assert (Hdiv : (fr + 8 * (x - Sfr fr)) / 8 = fr / 8 + (x - Sfr fr)).
        { replace (8 * (x - Sfr fr)) with ((x - Sfr fr) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
        assert (Hinfr : fr <= fr + 8 * (x - Sfr fr) < fr + FRAME_BYTES) by (unfold FRAME_SHADOW, FRAME_BYTES in *; lia).
        pose proof (shadow_of_app (fr + 8 * (x - Sfr fr)) (Hfrapp _ Hinfr)) as His.
        replace (shadow_addr (fr + 8 * (x - Sfr fr))) with x in His; [exact His|].
        unfold shadow_addr. rewrite Hdiv. unfold Sfr, shadow_addr. lia. }
      unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hin.
      rewrite Haspz in *. unfold BCMP_WRAP_K, HIGHMEM_BEG, AF.SLOT_STACK in *. lia.
    - exact Fr2.
    - exact Fr3.
    - exact Fr4.
    - exact Fr8.
    - exact Fr9.
    - exact Fr19.
    - exact Fr26. }
  assert (HENT' : ENT APIf g hb mem' md).
  { eapply ent_store;
      [exact HENT | exact HFRA | exact MU | exact HWin | exact HSTKeq | exact HSTKHI |].
    intros a Hia Ho. exact (proj2 (Hown' a) Ho). }
  split.
  - apply (sl_fra_move B APIf ra g fr hb regs' regs' mem' md md' HFRA'); try reflexivity; exact Hmat.
  - eapply ent_mat; [exact HENT' | exact Hmat].
Qed.

(* The runtime cells the wrapper_bcmp contract reads, from the FRA runtime invariant. *)
Lemma bcmp_cells : forall sp mem md, AsanRTInv.RT sp mem md ->
  asan_cells mem /\ shadow_rw mem /\
  bytes_at rsegs mem REAL_BCMP (le8 (wa BCMP)) /\ bytes_at rsegs mem REAL_MEMCMP (le8 (wa MEMCMP)) /\
  bytes_at rsegs mem GOT_CF (le8 (wa CF)) /\
  bytes_at rsegs mem (CF + 254) [Z_to_bv 8 1] /\ bytes_at rsegs mem (CF + 255) [Z_to_bv 8 1].
Proof.
  intros sp mem md HRT.
  destruct HRT as (HAC0 & HSW0 & _ & HCF0 & _ & HREAL0 & _).
  destruct HCF0 as (HGOTCF & _ & _ & _ & _ & _ & HCF240 & _).
  split; [exact HAC0|]. split; [exact HSW0|].
  split; [apply (real_cell_of mem REAL_BCMP BCMP HREAL0); vm_compute; reflexivity|].
  split; [apply (real_cell_of mem REAL_MEMCMP MEMCMP HREAL0); vm_compute; reflexivity|].
  split; [exact HGOTCF|].
  split.
  { pose proof (ba_sub mem (RT_CF + 240) (cf_b [0;0;0;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0]) 14 1 HCF240 ltac:(cbn; lia)) as Hs.
    replace (RT_CF + 240 + Z.of_nat 14) with (CF + 254) in Hs by (unfold CF, RT_CF; lia).
    replace (firstn 1 (skipn 14 (cf_b [0;0;0;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0]))) with [Z_to_bv 8 1] in Hs
      by (vm_compute; reflexivity).
    exact Hs. }
  { pose proof (ba_sub mem (RT_CF + 240) (cf_b [0;0;0;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0]) 15 1 HCF240 ltac:(cbn; lia)) as Hs.
    replace (RT_CF + 240 + Z.of_nat 15) with (CF + 255) in Hs by (unfold CF, RT_CF; lia).
    replace (firstn 1 (skipn 15 (cf_b [0;0;0;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0]))) with [Z_to_bv 8 1] in Hs
      by (vm_compute; reflexivity).
    exact Hs. }
Qed.

(* Both arms of `beqz [s1+240]` at 0x823ec, per turn j, from the official entry cut Inv_A823e8_at. t_8819 false
   ([s1+240] = 0): the beqz is taken to 0x8275c with memory and every register but a0 kept, into the official
   Inv_A8275c_at; its FLS comes from the 6c8 facts the entry carries (s2 = len, s9 = fr + 64, the guarded record
   bytes, [A+152], [A+280]) and rec_inv's phi range, and its LT from the entry's LT (f18_lt_reg). t_8819 true
   ([s1+240] <> 0, so t_big and 50 <= flen, s6 = phi + 18 and the record facts hold): the first wrapper_bcmp runs
   to 0x82400, into the official Inv_A82400_at, whose push-12D facts (s2, [A+152], the record bytes at phi and
   their length bound) are the entry's unguarded on this arm and whose LT crosses the call by f18_lt_keep. FLSI
   crosses the call by flsi_keep (the call writes only its stack scratch W). *)
Lemma seg_F18 : forall j : nat,
  Hat B APIf ra (Inv_A82400_at B APIf ra) j -> Hat B APIf ra (Inv_A8275c_at B APIf ra) j ->
  Hat B APIf ra (Inv_A823e8_at B APIf ra) j.
Proof.
  intros j Hexit Hexit0 g c HInv.
  pose proof (proj1 FF) as SEGS.
  (* the v1.9 frame size, for lia: FRAME_BYTES is a named constant in the cuts *)
  pose proof (eq_refl : FRAME_BYTES = 3136) as HFB. pose proof (eq_refl : FRAME_SHADOW = 392) as HFS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hj & HHB & HFLSI & HLK &
    (A & w240 & Hs1 & HAb & HspA & Hs23 & Hs24 & Hs22 & Hrec8233 & Hq136 & Hq120 & Hq176 &
     H240q & H240rng & H240f & H240t) & Hr18 & Hr25 & Hrecb & Hsp152 & Hsp280 & HLT).
  subst c. rewrite SEGS.
  destruct (t_8819 (g_in g) j) eqn:E8819.
  2:{ (* t_8819 = false: [s1+240] = 0, `ld a0,240(s1); beqz a0,826b0` taken; memory and all registers but a0 kept *)
    assert (Hw0 : w240 = 0) by (apply H240f; first [exact E8819 | reflexivity]).
    assert (H240z : q64 mem (A + 240) 0) by (rewrite <- Hw0; exact H240q).
    clear H240t H240f.
    pose proof HFRA as HFRA2.
    destruct HFRA2 as (A2 & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & _).
    apply (sl_run_lib regs (Z_to_bv 64 0x823e8) mem md
      (fun R0 pc' mem' =>
         pc' = Z_to_bv 64 0x8275c /\
         getr R0 2 = getr regs 2 /\ getr R0 3 = getr regs 3 /\ getr R0 4 = getr regs 4 /\
         getr R0 8 = getr regs 8 /\ getr R0 9 = getr regs 9 /\ getr R0 18 = getr regs 18 /\
         getr R0 19 = getr regs 19 /\ getr R0 21 = getr regs 21 /\ getr R0 22 = getr regs 22 /\
         getr R0 23 = getr regs 23 /\ getr R0 24 = getr regs 24 /\ getr R0 25 = getr regs 25 /\
         getr R0 26 = getr regs 26 /\ mem' = mem)
      (Post B APIf ra g)).
    - exact Hhalt.
    - eapply LE.evt_mono.
      { unfold Regs6ss.mkR_of.
        eapply f18_evt0; [unfold rg in Hs1; exact Hs1 | unfold q64 in H240z; exact H240z]. }
      { intros ms' E. eexists _, (Z_to_bv 64 0x8275c), mem. split; [exact E|].
        split; [reflexivity|].
        do 13 (split; [reflexivity|]). reflexivity. }
    - intros R0 pc' mem' regs' md' (Hpc & Er2 & Er3 & Er4 & Er8 & Er9 & Er18 & Er19 & Er21 & Er22 & Er23 &
        Er24 & Er25 & Er26 & Hm) Hreg Hmat.
      subst pc' mem'.
      assert (Fr2 : getr regs' 2 = getr regs 2) by (rewrite Hreg; exact Er2).
      assert (Fr3 : getr regs' 3 = getr regs 3) by (rewrite Hreg; exact Er3).
      assert (Fr4 : getr regs' 4 = getr regs 4) by (rewrite Hreg; exact Er4).
      assert (Fr8 : getr regs' 8 = getr regs 8) by (rewrite Hreg; exact Er8).
      assert (Fr9 : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact Er9).
      assert (Fr18 : getr regs' 18 = getr regs 18) by (rewrite Hreg; exact Er18).
      assert (Fr19 : getr regs' 19 = getr regs 19) by (rewrite Hreg; exact Er19).
      assert (Fr21 : getr regs' 21 = getr regs 21) by (rewrite Hreg; exact Er21).
      assert (Fr22 : getr regs' 22 = getr regs 22) by (rewrite Hreg; exact Er22).
      assert (Fr23 : getr regs' 23 = getr regs 23) by (rewrite Hreg; exact Er23).
      assert (Fr24 : getr regs' 24 = getr regs 24) by (rewrite Hreg; exact Er24).
      assert (Fr25 : getr regs' 25 = getr regs 25) by (rewrite Hreg; exact Er25).
      assert (Fr26 : getr regs' 26 = getr regs 26) by (rewrite Hreg; exact Er26).
      pose proof (flsi_reg g j fr regs regs' mem HFLSI Fr9) as HFLSI'.
      assert (HIexit0 : Inv_A8275c_at B APIf ra g j
                          (mkCfg (mkst regs' (Z_to_bv 64 0x8275c) mem (seg_rom rsegs)) md')).
      { exists phi, regs', mem, md', fr. rewrite SEGS. split; [reflexivity|].
        split; [exact (sl_fra_move B APIf ra g fr _ regs regs' mem md md' HFRA Fr2 Fr3 Fr4 Fr8 Fr9 Fr19 Fr26 Hmat)|].
        split; [eapply ent_mat; [exact HENT | exact Hmat]|].
        split; [exact Hgn|]. split; [exact Hj|]. split; [exact HHB|]. split; [exact HFLSI'|].
        split.
        { destruct HLK as (Hj' & Hs5j & HOURb). split; [exact Hj'|].
          split; [unfold rg in *; rewrite Fr21; exact Hs5j | exact HOURb]. }
        split.
        { unfold FLS. split; [exact HFLSI'|].
          split; [unfold rg in *; rewrite Fr18; exact Hr18|].
          split; [unfold rg in *; rewrite Fr22; exact Hs22|].
          split; [unfold rg in *; rewrite Fr23; exact Hs23|].
          split; [unfold rg in *; rewrite Fr24; exact Hs24|].
          split; [unfold rg in *; rewrite Fr25; exact Hr25|].
          split.
          { intro HfL. pose proof (Hrec8233 HfL) as (Hp0 & Hp50 & _).
            destruct (Hrecb HfL) as (Hbtg & Hbtphi & Hblen).
            split; [exact Hp0|]. split; [exact Hp50|]. split; [exact Hbtg|].
            split; [exact Hbtphi | exact Hblen]. }
          split; [exact (spill_reg regs regs' mem 152 _ Hsp152 Fr9)
                | exact (spill_reg regs regs' mem 280 _ Hsp280 Fr9)]. }
        exact (f18_lt_reg g fr j regs regs' mem HLT Fr9). }
      pose proof (Hexit0 g _ HIexit0) as HSR. rewrite SEGS in HSR. exact HSR. }
  (* t_8819 = true: t_big holds (so 50 <= flen and s6 = phi + 18), [s1+240] <> 0, the record facts and the two
     6-byte compare operands hold *)
  assert (Htbig : t_big (g_in g) j = true).
  { pose proof E8819 as E0. unfold t_8819 in E0. apply andb_prop in E0 as [E1 _].
    apply andb_prop in E1 as [Eb _]. exact Eb. }
  assert (HfL : 50 <= flen g j) by (unfold t_big in Htbig; apply Z.leb_le in Htbig; unfold flen; exact Htbig).
  destruct (H240t ltac:(first [exact E8819 | reflexivity])) as (Hw240nz & HRP & ls & rs & ls2 & rs2 & H72 & HBL &
    HLls & HBR & HLrs & Hmm & HADL & HADR & Hdj50 & H48 & HBL2 & HLls2 & HBR2 & HLrs2 & Hmm2 & HADL2 & HADR2).
  clear H240t H240f.
  (* push 15: on the 8819 arm both halves hold, so the full rec_inv of Inv_A82400_at is rebuilt here *)
  pose proof (rec_inv_of_split g j fr phi A mem (Hrec8233 HfL) HRP) as HRI.
  rewrite Htbig in Hs22.
  pose proof HRI as (Hphi0 & Hphi50 & _ & _ & Hpap & _).
  destruct (fra_frame B APIf ra g fr _ regs mem md HFRA) as (Hfrw & _ & _ & _).
  destruct (fra_app B APIf ra g fr _ regs mem md HFRA) as (HGTfr & Hfrapp).
  assert (Hdisjfr : fr + FRAME_BYTES <= AC.aspZ regs - BCMP_WRAP_K \/ AC.aspZ regs <= fr)
    by (apply Hfrw; unfold FN_STACK, BCMP_WRAP_K, AF.SLOT_STACK; lia).
  destruct (fra_win B APIf ra g fr _ regs mem md HFRA) as (Hlow & HW0).
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (A2 & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspillq & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hshf & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  assert (Hfrlo : 0 <= fr /\ fr + FRAME_BYTES <= APPMEM_END).
  { pose proof (Hfrapp fr ltac:(unfold FRAME_BYTES; lia)) as X1.
    pose proof (Hfrapp (fr + FRAME_BYTES - 1) ltac:(unfold FRAME_BYTES; lia)) as X2.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in X1, X2. lia. }
  assert (HLb : 0 <= fr + 186 < 2 ^ 64) by (unfold APPMEM_END in Hfrlo; lia).
  assert (HdjL : fr + 186 + 6 <= AC.aspZ regs - BCMP_WRAP_K \/ AC.aspZ regs <= fr + 186)
    by (destruct Hdisjfr as [Hd|Hd]; lia).
  assert (HdjR : phi + 6 <= AC.aspZ regs - BCMP_WRAP_K \/ AC.aspZ regs <= phi)
    by (destruct Hdj50 as [Hd|Hd]; unfold BW.BCMP_WRAP_K, BCMP_WRAP_K in *; lia).
  destruct (bcmp_cells sp mem md HRT) as (HAC0 & HSW0 & HRBc & HRMc & HGC & HC254 & HC255).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md HAH) as Hstkhi.
  assert (Hsphi : HIGHMEM_BEG + AF.SLOT_STACK - 4096 < sp) by lia.
  assert (HaspB : AC.aspZ regs <= APPMEM_END) by lia.
  assert (HK1 : AC.aspZ regs - FN_STACK + BCMP_WRAP_K <= AC.aspZ regs)
    by (unfold FN_STACK, AF.SLOT_STACK, BCMP_WRAP_K; lia).
  assert (HK2 : HIGHMEM_BEG <= AC.aspZ regs - FN_STACK) by lia.
  set (W := [(AC.aspZ regs - BCMP_WRAP_K, AC.aspZ regs)]).
  apply (sl_run_lib regs (Z_to_bv 64 0x823e8) mem md
    (fun R0 pc' mem' =>
       pc' = Z_to_bv 64 0x82400 /\
       getr R0 2 = getr regs 2 /\ getr R0 3 = getr regs 3 /\ getr R0 4 = getr regs 4 /\
       getr R0 8 = getr regs 8 /\ getr R0 9 = getr regs 9 /\ getr R0 19 = getr regs 19 /\
       getr R0 21 = getr regs 21 /\ getr R0 26 = getr regs 26 /\
       getr R0 23 = getr regs 23 /\ getr R0 24 = getr regs 24 /\ getr R0 10 = Z_to_bv 64 0 /\
       getr R0 22 = getr regs 22 /\ getr R0 18 = getr regs 18 /\
       Frame.munch W mem mem' /\ Frame.wmono rsegs mem mem' /\ ro_agree rsegs mem' /\ ro_same rsegs mem mem' /\
       stk rsegs mem' (AC.aspZ regs - FN_STACK) (AC.aspZ regs))
    (Post B APIf ra g)).
  - exact Hhalt.
  - eapply LE.evt_mono.
    { unfold Regs6ss.mkR_of.
      eapply f18_evt_ro with (A := A) (L := fr + 186) (R := phi) (ls := ls) (rs := rs) (w240 := w240) (vcmp := 0)
        (lo := AC.aspZ regs - FN_STACK).
      - unfold rg in Hs1; exact Hs1.
      - unfold rg in Hs23; exact Hs23.
      - exact HLb.
      - lia.
      - unfold q64 in H240q; exact H240q.
      - exact Hw240nz.
      - exact H240rng.
      - unfold q64 in H72; exact H72.
      - exact HBL.
      - exact HLls.
      - exact HBR.
      - exact HLrs.
      - exact Hmm.
      - exact Hro.
      - exact HADL.
      - exact HADR.
      - apply Hfrapp; lia.
      - apply Hfrapp; lia.
      - apply Hpap; lia.
      - apply Hpap; lia.
      - exact HdjL.
      - exact HdjR.
      - exact HW0.
      - exact HK1.
      - exact HK2.
      - exact HaspB.
      - exact HAC0.
      - exact HSW0.
      - exact HRBc.
      - exact HRMc.
      - exact HGC.
      - exact HC254.
      - exact HC255. }
    { intros ms' (ra' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t0' & t1' & t2' & t3' & t4' & t5' & t6' & m'
                  & E & MU & WM & RO' & ROS & ST').
      eexists _, (Z_to_bv 64 0x82400), m'. split; [exact E|].
      split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [unfold rg in Hs1; rewrite Hs1; reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|].
      split; [unfold rg in Hs23; rewrite Hs23; reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact RO'|]. split; [exact ROS|]. exact ST'. }
  - intros R0 pc' mem' regs' md' (Hpc & Er2 & Er3 & Er4 & Er8 & Er9 & Er19 & Er21 & Er26 & Er23 & Er24 & Er10 &
      Er22 & Er18 & MU & WM & RO' & ROS & ST') Hreg Hmat.
    subst pc'.
    assert (Fr2 : getr regs' 2 = getr regs 2) by (rewrite Hreg; exact Er2).
    assert (Fr3 : getr regs' 3 = getr regs 3) by (rewrite Hreg; exact Er3).
    assert (Fr4 : getr regs' 4 = getr regs 4) by (rewrite Hreg; exact Er4).
    assert (Fr8 : getr regs' 8 = getr regs 8) by (rewrite Hreg; exact Er8).
    assert (Fr9 : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact Er9).
    assert (Fr19 : getr regs' 19 = getr regs 19) by (rewrite Hreg; exact Er19).
    assert (Fr21 : getr regs' 21 = getr regs 21) by (rewrite Hreg; exact Er21).
    assert (Fr26 : getr regs' 26 = getr regs 26) by (rewrite Hreg; exact Er26).
    assert (Fr23 : getr regs' 23 = getr regs 23) by (rewrite Hreg; exact Er23).
    assert (Fr24 : getr regs' 24 = getr regs 24) by (rewrite Hreg; exact Er24).
    assert (Fr10 : getr regs' 10 = Z_to_bv 64 0) by (rewrite Hreg; exact Er10).
    assert (Fr22 : getr regs' 22 = getr regs 22) by (rewrite Hreg; exact Er22).
    assert (Fr18 : getr regs' 18 = getr regs 18) by (rewrite Hreg; exact Er18).
    assert (HaspEq : AC.aspZ regs' = AC.aspZ regs) by (unfold AC.aspZ; rewrite Fr2; reflexivity).
    destruct (bcmp_fra g fr (hb1 phi (AC.a_size (flen g j))) regs regs' mem mem' md md' A HFRA HENT Hs1 HAb HspA
                MU WM RO' ROS ST' Fr2 Fr3 Fr4 Fr8 Fr9 Fr19 Fr26 Hmat) as (HFRA'' & HENT'').
    assert (Hallapp : all_app W).
    { subst W. cbn [all_app]. split; [|exact I]. intros a Ha. unfold app_mem. right.
      rewrite Haspz in *. unfold BCMP_WRAP_K, HIGHMEM_BEG, APPMEM_END, AF.SLOT_STACK in *. lia. }
    assert (HOW : forall x, (x < AC.aspZ regs - BCMP_WRAP_K \/ AC.aspZ regs <= x) -> Frame.outside W x)
      by (intros x Hx; subst W; apply out1; exact Hx).
    assert (HRI' : rec_inv g j fr phi A mem').
    { apply (rec_inv_kept g j fr phi A mem mem' W HRI MU).
      - intros x Hx. apply HOW. destruct Hdj50 as [Hd|Hd]; unfold BW.BCMP_WRAP_K, BCMP_WRAP_K in *; lia.
      - intros x Hx. apply HOW. lia.
      - intros x Hx. apply HOW. rewrite Haspz. unfold BCMP_WRAP_K, AF.SLOT_STACK in *. lia.
      - intros x Hx. apply HOW. destruct Hdisjfr as [Hd|Hd]; lia. }
    (* FLSI across the call: the spills sit at A + off >= A >= sp (above W), [fr, fr + FRAME_BYTES) is apart
       from W, and the harness block ends at or below stklo <= S - SLOT_STACK < sp - K (a_laws_blocks). *)
    assert (HFLSI' : FLSI g j fr regs' mem').
    { apply (flsi_keep g j fr regs regs' mem mem' W HFLSI Fr9 MU Hallapp WM).
      - intros A' HA' x Hx. subst W. cbn [Frame.outside]. split; [|exact I]. intros [HH1 HH2].
        assert (Hb' : 0 <= A' < 2 ^ 64)
          by (rewrite Haspz in *; unfold BCMP_WRAP_K, HIGHMEM_BEG, APPMEM_END, AF.SLOT_STACK in *; lia).
        assert (EA' : A' = A).
        { assert (Ez : Z_to_bv 64 A' = Z_to_bv 64 A) by (unfold rg in HA', Hs1; rewrite <- HA'; exact Hs1).
          apply (f_equal (bv_unsigned (n:=64))) in Ez. rewrite !MState.unsigned_lit in Ez by lia. exact Ez. }
        subst A'. lia.
      - intros x Hx. apply HOW. destruct Hdisjfr as [Hd|Hd]; lia.
      - intros x Hx. apply HOW. left.
        pose proof HFLSI as HF1. unfold FLSI, f1_IN in HF1. destruct HF1 as (_ & _ & _ & _ & (Finp & _ & _) & _).
        assert (Hnp : 0 < g_n g) by (rewrite g_n_len; lia).
        assert (Hin : In (g_p g, g_n g) (hb1 phi (AC.a_size (flen g j)) ++ g_H g))
          by (apply in_or_app; right; exact (Finp Hnp)).
        pose proof (lwb_end _ _ _ _ _ _ (lw_blocks (APIf rc) _ mem md (g_p g) (g_n g) HAH Hin)) as Hpn.
        rewrite g_n_len in Hpn.
        rewrite Haspz in *. unfold BCMP_WRAP_K, AF.SLOT_STACK in *. lia. }
    destruct (ba_first6 mem (fr + 180) ls2 HBL2 HLls2) as (HBL2f & HLf2).
    destruct (ba_first6 mem (phi + 6) rs2 HBR2 HLrs2) as (HBR2f & HRf2).
    assert (HKq : forall off v, 0 <= off -> q64 mem (A + off) v -> q64 mem' (A + off) v).
    { intros off v Hoff Hq. unfold q64 in *. eapply (fl_bytes W); [exact Hq | exact MU |].
      rewrite length_le8. intros x Hx. apply HOW. lia. }
    (* the record block [phi, phi + len_j) is a live heap block, so it ends at or below stklo, below the call's
       scratch [sp - K, sp): the call writes no byte of the record *)
    assert (Hblk : forall x, phi <= x < phi + flen g j -> Frame.outside W x).
    { intros x Hx. apply HOW. left.
      assert (Hin : In (phi, AC.a_size (flen g j)) (hb1 phi (AC.a_size (flen g j)) ++ g_H g))
        by (unfold hb1; apply in_or_app; left; left; reflexivity).
      pose proof (lwb_end _ _ _ _ _ _ (lw_blocks (APIf rc) _ mem md phi (AC.a_size (flen g j)) HAH Hin)) as Hend.
      unfold AC.a_size in Hend.
      rewrite Haspz in *. unfold BCMP_WRAP_K, AF.SLOT_STACK in *. lia. }
    assert (HA9span : forall lo hi, 0 <= lo -> hi <= 512 -> forall A', rg regs 9 A' ->
              forall x, A' + lo <= x < A' + hi -> Frame.outside W x).
    { intros lo hi Hlo Hhi A' HA' x Hx. subst W. cbn [Frame.outside]. split; [|exact I]. intros [HH1 HH2].
      assert (Hb' : 0 <= A' < 2 ^ 64)
        by (rewrite Haspz in *; unfold BCMP_WRAP_K, HIGHMEM_BEG, APPMEM_END, AF.SLOT_STACK in *; lia).
      assert (EA' : A' = A).
      { assert (Ez : Z_to_bv 64 A' = Z_to_bv 64 A) by (unfold rg in HA', Hs1; rewrite <- HA'; exact Hs1).
        apply (f_equal (bv_unsigned (n:=64))) in Ez. rewrite !MState.unsigned_lit in Ez by lia. exact Ez. }
      subst A'. lia. }
    assert (HIexit : Inv_A82400_at B APIf ra g j (mkCfg (mkst regs' (Z_to_bv 64 0x82400) mem' (seg_rom rsegs)) md')).
    { exists phi, regs', mem', md', fr. rewrite SEGS. split; [reflexivity|].
      split; [exact HFRA''|]. split; [exact HENT''|]. split; [exact Hgn|]. split; [exact Hj|].
      split.
      { destruct HHB as (Hphinz & Hphiad). split; [exact Hphinz|].
        eapply sl_addr_keep; [exact Hphiad | exact MU | exact Hallapp]. }
      split; [exact HFLSI'|].
      split.
      { destruct HLK as (Hj' & Hs5j & HOURb). split; [exact Hj|]. split.
        - unfold rg in *. rewrite Fr21. exact Hs5j.
        - unfold OURb in *. apply (fl_bytes W mem mem' (fr + 2624) (OUR (g_in g)) HOURb MU).
          rewrite OUR_length. intros x Hx. apply HOW. destruct Hdisjfr as [Hd|Hd]; lia. }
      split.
      { exists A, (firstn 6 ls2), (firstn 6 rs2).
      split; [unfold rg; rewrite Fr9; exact Hs1|].
      split; [exact HAb|].
      split; [rewrite HaspEq; exact HspA|].
      split; [unfold rg; rewrite Fr23; exact Hs23|].
      split; [unfold rg; rewrite Fr24; exact Hs24|].
      split; [unfold rg; exact Fr10|].
      split; [unfold rg; rewrite Fr22; exact Hs22|].
      split; [exact HRI'|].
      split; [exact (HKq 136 _ ltac:(lia) Hq136)|].
      split; [exact (HKq 120 _ ltac:(lia) Hq120)|].
      split; [exact (HKq 176 _ ltac:(lia) Hq176)|].
      split; [exact (HKq 64 _ ltac:(lia) H48)|].
      split.
      { eapply (fl_bytes W); [exact HBL2f | exact MU |]. rewrite HLf2. intros x Hx. apply HOW.
        destruct Hdisjfr as [Hd|Hd]; lia. }
      split; [rewrite HLf2; lia|].
      split.
      { eapply (fl_bytes W); [exact HBR2f | exact MU |]. rewrite HRf2. intros x Hx. apply HOW.
        destruct Hdj50 as [Hd|Hd]; unfold BW.BCMP_WRAP_K, BCMP_WRAP_K in *; lia. }
      split; [rewrite HRf2; lia|].
      split; [rewrite memcmp_firstn; exact Hmm2|].
      split; [eapply sl_addr_keep; [exact HADL2 | exact MU | exact Hallapp]|].
      split; [eapply sl_addr_keep; [exact HADR2 | exact MU | exact Hallapp]|].
        rewrite HaspEq. exact Hdj50. }
      (* push 12D: s2 = len_j, [A+152], the record bytes at phi and their length bound; then LT (push 12B) *)
      destruct (Hrecb HfL) as (Hbtg & Hbtphi & Hblen).
      split; [unfold rg in *; rewrite Fr18; exact Hr18|].
      split; [apply (spill_keep regs regs' mem mem' W 152 _ Hsp152 Fr9 MU);
              intros A' HA' x Hx; exact (HA9span 152 160 ltac:(lia) ltac:(lia) A' HA' x ltac:(lia))|].
      split.
      { eapply (fl_bytes W); [exact Hbtg | exact MU |].
        rewrite f18_t_g_length. intros x Hx. apply Hblk. lia. }
      split.
      { eapply (fl_bytes W); [exact Hbtphi | exact MU |].
        intros x Hx. apply Hblk. lia. }
      split; [exact Hblen|].
      apply (f18_lt_keep g fr j regs regs' mem mem' W HLT Fr9 MU Hallapp).
      - intros x Hx. apply HOW. destruct Hdisjfr as [Hd|Hd]; lia.
      - exact (HA9span 104 120 ltac:(lia) ltac:(lia)). }
    pose proof (Hexit g _ HIexit) as HSR. rewrite SEGS in HSR. exact HSR.
Qed.
End F18.
