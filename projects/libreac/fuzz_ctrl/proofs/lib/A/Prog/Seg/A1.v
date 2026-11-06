(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 1137 of its 1175 lines of code are new or changed and 210 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/reac_box_model_block.v; 1090 of its 1202 lines of code are new or changed and 1063 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P5.v, with its module paths, module names and addresses changed; 1348 of its 1450 lines of code are new or changed and 1100 lines of the source are left out. *)
(* Segment A1 of fuzz_ctrl LLVMFuzzerTestOneInput (asan, image A): the prologue 0x80edc-0x80f50 (plan-asan FP.1),
   from the slot pre Inv_ENTRY to the cut Inv_A80f54 (after the class-6 frame request at 0x80f50). The form's
   second exit Inv_A80f88 (the `beqz a2,0x80f5c` branch at 0x80f44, then the real-stack probe 0x80f68-0x80f84) is
   not reached: the switch word at UAR is 1 (RT's asan_cells).
   This file holds the runs of the segment:
   - a1_store_evt (0x80edc-0x80f14): sp = S - 416, `sd zero,0(sp)` and the 13 callee-saved registers at
     sp + 312 .. sp + 408 ([S - 104, S)); the only writes are inside [S - 416, S).
   - a1_tail_evt (0x80f18-0x80f4c): s0 = S, sp = A = (S - 416) & -32, s1 = A, s8 = n, s7 = p, the two GOT loads
     (0x9fb28 -> UAR, 0x9fad0 -> CELL_K), the switch word D = 1 at UAR and K = ASAN_K at CELL_K (asan_cells), the
     branch `beqz a2,0x80f5c` NOT taken, and a0 = 0x1000 - 960 = 3136 for the request. No memory is written.
   - a1_req_evt (0x80f50): the request on its contract (Sm6.stack_malloc_6), run on the normalized memory.
   seg_A1 composes them and builds Inv_A80f54: PREF, ENT, the request result r (0, or a class-6 FakeStack frame
   with its FSREC record), and the input facts of the entry pre carried across the prologue and the request. *)
(* libreac v1.9.0 (S_A1 IDENTICAL-RENUMBER, a Theorem Labs lane's table v190-segment-table.md (a working note, not in this delivery)): pcs +0x20 (0x80ebc -> 0x80edc),
   cut names per v190-cutnames-A.tsv (a working note, not in this delivery), the frame request size 0x1000 - 960 = 3136 = FRAME_BYTES (0x80f4c), the GOT
   cells of AsanRT (UAR, CELL_K) and the callee __asan_stack_malloc_6 by their names. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_stack_malloc_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.AW Require Sm6.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Spec Require StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_fs Tac_fsfree.

(* Proof speed (common.md (a working note, not in this delivery)): hide disjunctions and mod facts from lia in the slow
   post-run goals of seg_A1 (measured 362 s / 35 s / 11 s on three lia calls before). *)
Local Definition rs_hold (A : Prop) : Prop := A.
Local Lemma rs_hide : forall A : Prop, A -> rs_hold A. Proof. intros A H. exact H. Qed.
Local Ltac rs_hide_all := repeat match goal with
  | H : _ \/ _ |- _ => apply rs_hide in H
  | H : _ mod _ = _ |- _ => apply rs_hide in H end.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
Module SF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Spec.StrFun.

(* mkR_of regs is definitionally the explicit 31-slot register map. *)
Lemma mkR_of_expand : forall regs, Regs6ss.mkR_of regs =
  Frame.mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6)
  (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12)
  (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18)
  (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
  (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31).
Proof. intros regs. reflexivity. Qed.

(* One `sd` of the prologue: the store is inside the 416-byte window the carried wr_at covers, so store_ok holds;
   after it the window is still writable (wr_at_write). *)
Ltac stw addr :=
  let HS := fresh "HS" in
  lazymatch goal with
  | HW : wr_at rsegs ?m ?base ?n |- _ =>
      assert (HS : store_ok rsegs m (wa addr) 8 = true)
        by (replace addr with (base + (addr - base)) by lia;
            apply (wr_at_store_ok rsegs m base n (addr - base) 8%nat HW); lia);
      step; clear HS;
      lazymatch goal with
      | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m2 ?c ?bs) _) =>
          apply (wr_at_write rsegs m2 base n c bs) in HW
      end
  end.


(* One saved word of the prologue frame: peel the later stores (all at other addresses), then the store itself. *)
Ltac ba_one :=
  repeat first [ (apply bytes_at_write_same; [lia | rewrite ?length_le8; lia])
               | (eapply bytes_at_write_other; [ | lia | rewrite ?length_le8; lia | rewrite ?length_le8; lia ]) ].

Lemma le8_of_bytes : forall bs : list byte, length bs = 8%nat -> le8 (Z_to_bv 64 (bytes_le_to_Z bs)) = bs.
Proof.
  intros bs L. unfold le8, word_to_le_bytes. rewrite Z_to_bv_unsigned.
  change (bv_wrap 64 (bytes_le_to_Z bs)) with (bytes_le_to_Z bs mod 2^64).
  rewrite (Z_to_le_bytes_mod 8 _ 64) by lia. rewrite <- L. apply SF.Z_to_le_bytes_to_Z.
Qed.

(* A word cell determines its value. *)
Lemma word_mem_unique : forall mem a v1 v2, word_mem rsegs mem a v1 -> word_mem rsegs mem a v2 ->
  0 <= v1 < 2 ^ 64 -> 0 <= v2 < 2 ^ 64 -> v1 = v2.
Proof.
  intros mem a v1 v2 H1 H2 R1 R2.
  assert (D : forall k, (k < 8)%nat -> le_byte v1 8 k = le_byte v2 8 k).
  { intros k Hk. pose proof (H1 k Hk) as E1. pose proof (H2 k Hk) as E2. rewrite E1 in E2.
    injection E2 as E2.
    pose proof (kb_byte_unsigned v1 8 k) as K1. pose proof (kb_byte_unsigned v2 8 k) as K2.
    unfold bv_unsigned in K1, K2. rewrite K1, K2 in E2. exact E2. }
  pose proof (kb_le8_digits v1 R1) as G1. pose proof (kb_le8_digits v2 R2) as G2.
  rewrite (D 0%nat ltac:(lia)), (D 1%nat ltac:(lia)), (D 2%nat ltac:(lia)), (D 3%nat ltac:(lia)),
          (D 4%nat ltac:(lia)), (D 5%nat ltac:(lia)), (D 6%nat ltac:(lia)), (D 7%nat ltac:(lia)) in G1.
  lia.
Qed.

Section S.
Context {fx : FPState}.

Lemma a1_store_evt :
  forall (ra0 gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (mem : word -> option byte) (S : Z),
  HIGHMEM_BEG <= S - 1048576 -> S < APPMEM_END ->
  stk rsegs mem (S - 1048576) S ->
  evt rsegs
    (fun ms => exists mem',
       ms = MS (Frame.mkR ra0 (Z_to_bv 64 (S - 416)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               fp_regs (Z_to_bv 64 0x80f18) fp_csr None mem' (seg_rom rsegs) /\
       munch [(S - 416, S)] mem mem' /\ wmono rsegs mem mem' /\
       stk rsegs mem' (S - 1048576) S /\
       bytes_at rsegs mem' (S - 104)
         (le8 s11 ++ le8 s10 ++ le8 s9 ++ le8 s8 ++ le8 s7 ++ le8 s6 ++ le8 s5 ++ le8 s4 ++ le8 s3 ++ le8 s2 ++
          le8 s1 ++ le8 s0 ++ le8 ra0))
    (MS (Frame.mkR ra0 (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        fp_regs (Z_to_bv 64 0x80edc) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros ra0 gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 mem S
    HS1 HS2 HST.
  unfold HIGHMEM_BEG, APPMEM_END in HS1, HS2.
  assert (HW : wr_at rsegs mem (S - 416) 416).
  { destruct HST as (H0 & H1 & H). split; [lia|]. split; [lia|]. intros i Hi. exact (proj1 (H (S - 416 + i) ltac:(lia))). }
  unfold Frame.mkR.
  step.
  stw (S - 416).
  stw (S - 8).
  stw (S - 16).
  stw (S - 24).
  stw (S - 32).
  stw (S - 40).
  stw (S - 48).
  stw (S - 56).
  stw (S - 64).
  stw (S - 72).
  stw (S - 80).
  stw (S - 88).
  stw (S - 96).
  stw (S - 104).
  apply evt_done. eexists. split; [reflexivity|].
  split.
  { repeat (apply munch_write; [ | lia | rewrite ?length_le8; lia | cbn [inside]; left; rewrite ?length_le8; lia ]).
    apply munch_refl. }
  split.
  { repeat apply wmono_write. apply wmono_refl. }
  split.
  { repeat (apply stk_write; [ | lia | rewrite ?length_le8; lia ]). exact HST. }
  apply (proj2 (bytes_at_app rsegs _ (S - 104) _ _)); split; [ba_one|].
  rewrite length_le8. replace (S - 104 + Z.of_nat 8) with (S - 96) by (cbn; lia).
  apply (proj2 (bytes_at_app rsegs _ (S - 96) _ _)); split; [ba_one|].
  rewrite length_le8. replace (S - 96 + Z.of_nat 8) with (S - 88) by (cbn; lia).
  apply (proj2 (bytes_at_app rsegs _ (S - 88) _ _)); split; [ba_one|].
  rewrite length_le8. replace (S - 88 + Z.of_nat 8) with (S - 80) by (cbn; lia).
  apply (proj2 (bytes_at_app rsegs _ (S - 80) _ _)); split; [ba_one|].
  rewrite length_le8. replace (S - 80 + Z.of_nat 8) with (S - 72) by (cbn; lia).
  apply (proj2 (bytes_at_app rsegs _ (S - 72) _ _)); split; [ba_one|].
  rewrite length_le8. replace (S - 72 + Z.of_nat 8) with (S - 64) by (cbn; lia).
  apply (proj2 (bytes_at_app rsegs _ (S - 64) _ _)); split; [ba_one|].
  rewrite length_le8. replace (S - 64 + Z.of_nat 8) with (S - 56) by (cbn; lia).
  apply (proj2 (bytes_at_app rsegs _ (S - 56) _ _)); split; [ba_one|].
  rewrite length_le8. replace (S - 56 + Z.of_nat 8) with (S - 48) by (cbn; lia).
  apply (proj2 (bytes_at_app rsegs _ (S - 48) _ _)); split; [ba_one|].
  rewrite length_le8. replace (S - 48 + Z.of_nat 8) with (S - 40) by (cbn; lia).
  apply (proj2 (bytes_at_app rsegs _ (S - 40) _ _)); split; [ba_one|].
  rewrite length_le8. replace (S - 40 + Z.of_nat 8) with (S - 32) by (cbn; lia).
  apply (proj2 (bytes_at_app rsegs _ (S - 32) _ _)); split; [ba_one|].
  rewrite length_le8. replace (S - 32 + Z.of_nat 8) with (S - 24) by (cbn; lia).
  apply (proj2 (bytes_at_app rsegs _ (S - 24) _ _)); split; [ba_one|].
  rewrite length_le8. replace (S - 24 + Z.of_nat 8) with (S - 16) by (cbn; lia).
  apply (proj2 (bytes_at_app rsegs _ (S - 16) _ _)); split; [ba_one|].
  rewrite length_le8. replace (S - 16 + Z.of_nat 8) with (S - 8) by (cbn; lia).
  ba_one.
Qed.

(* bytes_at -> the ov_read_bytes form solve_load consumes. *)
Lemma rd8 : forall m a bs, bytes_at rsegs m a bs -> length bs = 8%nat ->
  ov_read_bytes rsegs m (wa a) 8 = Some bs.
Proof.
  intros m a bs H Hl.
  pose proof (bytes_at_ov_read rsegs m a bs 0 8 H ltac:(lia)) as HH.
  change (Z.of_nat 0) with 0%Z in HH. rewrite Z.add_0_r, skipn_O, firstn_all2 in HH by lia. exact HH.
Qed.
Lemma rd4 : forall m a bs, bytes_at rsegs m a bs -> length bs = 4%nat ->
  ov_read_bytes rsegs m (wa a) 4 = Some bs.
Proof.
  intros m a bs H Hl.
  pose proof (bytes_at_ov_read rsegs m a bs 0 4 H ltac:(lia)) as HH.
  change (Z.of_nat 0) with 0%Z in HH. rewrite Z.add_0_r, skipn_O, firstn_all2 in HH by lia. exact HH.
Qed.

Lemma land_align32 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551584 = x / 32 * 32.
Proof.
  intros x Hx.
  replace 18446744073709551584 with (Z.land (Z.lnot (Z.ones 5)) (Z.ones 64)) by reflexivity.
  rewrite Z.land_assoc, (Z.land_comm x), <- Z.land_assoc, (Z.land_ones x 64) by lia.
  rewrite Z.mod_small by lia. rewrite Z.land_comm, <- Z.ldiff_land, Z.ldiff_ones_r by lia.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma a1_tail_evt :
  forall (ra0 gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (mem : word -> option byte) (S A : Z),
  HIGHMEM_BEG <= S - 1048576 -> S < APPMEM_END -> A = (S - 416) / 32 * 32 ->
  bytes_at rsegs mem GOT_UAR (le8 (wa UAR)) ->
  bytes_at rsegs mem GOT_CELL_K (le8 (wa CELL_K)) ->
  bytes_at rsegs mem UAR (le4 (wa 1)) ->
  bytes_at rsegs mem CELL_K (le8 (wa ASAN_K)) ->
  evt rsegs
    (fun ms => exists a1' a2',
       ms = MS (Frame.mkR ra0 (Z_to_bv 64 A) gp tp t0 t1 t2 (Z_to_bv 64 S) (Z_to_bv 64 A)
                          (Z_to_bv 64 3136) a1' a2' a3 a4 a5 a6 a7
                          s2 s3 s4 s5 s6 a0 a1 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
               fp_regs (Z_to_bv 64 0x80f50) fp_csr None mem (seg_rom rsegs))
    (MS (Frame.mkR ra0 (Z_to_bv 64 (S - 416)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        fp_regs (Z_to_bv 64 0x80f18) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros ra0 gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 mem S A
    HS1 HS2 HA HG1 HG2 HU HK.
  unfold HIGHMEM_BEG, APPMEM_END in HS1, HS2.
  pose proof (rd8 mem _ _ HG1 ltac:(apply length_le8)) as RG1.
  pose proof (rd8 mem _ _ HG2 ltac:(apply length_le8)) as RG2.
  pose proof (rd4 mem _ _ HU ltac:(apply length_le4)) as RU.
  pose proof (rd8 mem _ _ HK ltac:(apply length_le8)) as RK.
  unfold GOT_UAR, GOT_CELL_K, UAR, CELL_K in RG1, RG2, RU, RK.
  unfold Frame.mkR.
  step. step.
  replace (S - 416 + 416) with S by lia.
  rewrite (MState.unsigned_lit (S - 416)) by lia.
  rewrite (land_align32 (S - 416)) by lia.
  rewrite <- HA.
  step. step. step. step. step. step. step. step. step.
  assert (E1 : sx32 (Z_to_bv 64 1) = Z_to_bv 64 1) by (apply bv_eq; vm_compute; reflexivity).
  step. rewrite E1. if_false.
  step. step.
  apply evt_done. eexists. eexists. reflexivity.
Qed.

End S.

(* A run of present bytes is a bytes_at (asan_memcpy.v:118's helper). *)
Lemma bytes_exist : forall m k A, 0 <= A -> A + Z.of_nat k <= 2^64 ->
  (forall j, 0 <= j < Z.of_nat k -> exists b, mrd rsegs m (wa (A + j)) = Some b) ->
  exists bs, length bs = k /\ bytes_at rsegs m A bs.
Proof.
  intros m k. induction k as [|k IH]; intros A H0 H1 H.
  - exists []. split; [reflexivity|]. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - destruct (H 0 ltac:(lia)) as [b Hb]. rewrite Z.add_0_r in Hb.
    destruct (IH (A + 1) ltac:(lia) ltac:(lia)) as (bs & L & Bb).
    { intros j Hj. replace (A + 1 + j) with (A + (j + 1)) by lia. apply H. lia. }
    exists (b :: bs). split; [cbn; lia|]. destruct Bb as (_ & _ & Bb).
    split; [lia|]. split; [cbn [length]; lia|]. intros i Hi. destruct i as [|i].
    + rewrite Z.add_0_r. exact Hb.
    + cbn [nth_error]. rewrite <- (Bb i ltac:(cbn [length] in Hi; lia)).
      replace (A + Z.of_nat (S i)) with (A + 1 + Z.of_nat i) by lia. reflexivity.
Qed.

(* Every GNU_RELRO block of FrameAPI lies below GT = 0x5fe000 (computed over the list, whatever its entries). *)
Lemma relro_blk_below : forall lo len, In (lo, len) AF.frame_RELRO -> 0 <= lo /\ lo + len <= 6283264.
Proof.
  intros lo len Hil.
  assert (HR : forallb (fun p => (0 <=? fst p) && (fst p + snd p <=? 6283264)) AF.frame_RELRO = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in HR. specialize (HR _ Hil). apply andb_true_iff in HR as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. cbn [fst snd] in H1, H2. lia.
Qed.

(* The image's segments all end at or below ASAN_GT = 0x5fe000 (A/BzBridge.v's seg_tops_below, for that top). *)
Definition seg_tops_below (segs : list Segment) (top : Z) : bool :=
  forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? top) segs.

Lemma rsegs_below_gt : seg_tops_below rsegs 0x5fe000 = true.
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
Lemma ro_addr_hi : forall a, 0x5fe000 <= a < 2 ^ 64 -> ro_addr rsegs (wa a) = false.
Proof.
  intros a Ha. unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.ro_addr.
  match goal with |- context [find_segment ?sg ?x ?n] =>
    destruct (find_segment sg x n) as [s|] eqn:E; [|reflexivity];
    destruct (find_segment_below sg 0x5fe000 x n s rsegs_below_gt E ltac:(cbn; lia)) as [L|L];
    [exfalso; rewrite MState.unsigned_lit in L by lia; lia | cbn in L; lia] end.
Qed.

Lemma wview_rel_hi : forall m m0 a, mem_rel rsegs m m0 -> 0x5fe000 <= a < 2 ^ 64 ->
  (wview rsegs m0 (wa a) <> None <-> wview rsegs m (wa a) <> None).
Proof.
  intros m m0 a HR Ha. rewrite (wview_rel_rw rsegs m m0 (wa a) HR (ro_addr_hi a Ha)). split; auto.
Qed.

Lemma stk_rel_hi : forall m m0 lo hi, mem_rel rsegs m m0 -> 0x5fe000 <= lo -> hi <= 2 ^ 64 ->
  stk rsegs m lo hi -> stk rsegs m0 lo hi.
Proof.
  intros m m0 lo hi HR Hlo Hhi (H0 & H1 & H). split; [lia|]. split; [lia|]. intros a Ha.
  destruct (H a Ha) as (Hw & b & Hb). split.
  - apply (proj2 (wview_rel_hi m m0 a HR ltac:(lia))). exact Hw.
  - exists b. rewrite <- (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma stk_rel_hi_back : forall m m0 lo hi, mem_rel rsegs m m0 -> 0x5fe000 <= lo -> hi <= 2 ^ 64 ->
  stk rsegs m0 lo hi -> stk rsegs m lo hi.
Proof.
  intros m m0 lo hi HR Hlo Hhi (H0 & H1 & H). split; [lia|]. split; [lia|]. intros a Ha.
  destruct (H a Ha) as (Hw & b & Hb). split.
  - apply (proj1 (wview_rel_hi m m0 a HR ltac:(lia))). exact Hw.
  - exists b. rewrite (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma shadow_rw_rel : forall m m0, mem_rel rsegs m m0 -> shadow_rw m -> shadow_rw m0.
Proof.
  intros m m0 HR H a Ha. pose proof (in_shadow_range a Ha) as Hr.
  unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Ha.
  destruct (H a Ha) as (Hw & b & Hb). split.
  - apply (proj2 (wview_rel_hi m m0 a HR ltac:(lia))). exact Hw.
  - exists b. rewrite <- (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma addressable_rel : forall m m0 p n, mem_rel rsegs m m0 -> addressable m p n -> addressable m0 p n.
Proof.
  intros m m0 p n HR (H0 & H1 & H2 & H). split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. destruct (H i Hi) as (Hap & b & Hb & Hok). split; [exact Hap|].
  exists b. rewrite <- (mrd_rel rsegs m m0 _ HR). split; [exact Hb | exact Hok].
Qed.

Lemma addressable_rel_back : forall m m0 p n, mem_rel rsegs m m0 -> addressable m0 p n -> addressable m p n.
Proof.
  intros m m0 p n HR (H0 & H1 & H2 & H). split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. destruct (H i Hi) as (Hap & b & Hb & Hok). split; [exact Hap|].
  exists b. rewrite (mrd_rel rsegs m m0 _ HR). split; [exact Hb | exact Hok].
Qed.

Lemma fs_place_rel : forall m m0 FS, mem_rel rsegs m m0 -> 0x5fe000 <= FS -> FS + FS_SIZE <= 2 ^ 64 ->
  fs_place m FS -> fs_place m0 FS.
Proof.
  intros m m0 FS HR Hlo Hhi (P1 & P2 & P3 & P4 & P5). split; [exact P1|]. split; [exact P2|]. split; [exact P3|].
  split; [exact P4|]. exact (stk_rel_hi m m0 FS (FS + FS_SIZE) HR Hlo Hhi P5).
Qed.

Lemma fs_place_rel_back : forall m m0 FS, mem_rel rsegs m m0 -> 0x5fe000 <= FS -> FS + FS_SIZE <= 2 ^ 64 ->
  fs_place m0 FS -> fs_place m FS.
Proof.
  intros m m0 FS HR Hlo Hhi (P1 & P2 & P3 & P4 & P5). split; [exact P1|]. split; [exact P2|]. split; [exact P3|].
  split; [exact P4|]. exact (stk_rel_hi_back m m0 FS (FS + FS_SIZE) HR Hlo Hhi P5).
Qed.

(* A run whose writes W are all at or above 0x5fe000 keeps every read-only byte, so it keeps ro_agree. *)
Lemma ro_agree_hi : forall W mem mem', ro_agree rsegs mem -> munch W mem mem' ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ outside W x -> 0x5fe000 <= x) -> ro_agree rsegs mem'.
Proof.
  intros W mem mem' Hro MU HW a Hra.
  pose proof (bv_unsigned_in_range 64 a) as Hrange. change (bv_modulus 64) with (2 ^ 64) in Hrange.
  destruct (Z.lt_ge_cases (bv_unsigned a) 0x5fe000) as [L|L].
  - unfold mrd. rewrite MU; [exact (Hro a Hra)|].
    destruct (kb_outside_dec W (bv_unsigned a)) as [Ho|Ho]; [exact Ho|].
    exfalso. pose proof (HW (bv_unsigned a) Hrange Ho). lia.
  - exfalso. pose proof (ro_addr_hi (bv_unsigned a) ltac:(lia)) as X. unfold wa in X.
    rewrite Z_to_bv_bv_unsigned in X. rewrite X in Hra. discriminate Hra.
Qed.

Lemma flag_bounds : forall FS c j, (c <= 10)%nat -> 0 <= j < AC.a_fs_M c ->
  FS + 4096 <= AC.a_fs_flag FS c j < FS + 36864.
Proof.
  intros FS c j Hc Hj.
  unfold AC.a_fs_flag, AC.a_fs_M in *.
  assert (He : 0 <= Z.of_nat c <= 10) by lia.
  assert (P2 : 2 ^ (15 - Z.of_nat c) <= 2 ^ 15) by (apply Z.pow_le_mono_r; lia).
  assert (P3 : 0 < 2 ^ (14 - Z.of_nat c)) by (apply Z.pow_pos_nonneg; lia).
  assert (P4 : 2 ^ (15 - Z.of_nat c) = 2 * 2 ^ (14 - Z.of_nat c)).
  { replace (15 - Z.of_nat c) with (Z.succ (14 - Z.of_nat c)) by lia.
    rewrite Z.pow_succ_r by lia. reflexivity. }
  change (2 ^ 15) with 32768 in *.
  lia.
Qed.

(* addressable at one byte depends only on the byte's shadow byte. *)
Lemma addressable1_keep : forall m m' a, addressable m a 1 ->
  m' (wa (shadow_addr a)) = m (wa (shadow_addr a)) -> addressable m' a 1.
Proof.
  intros m m' a (H0 & H1 & H2 & H) E. split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. destruct (H i Hi) as (Hap & b & Hb & Hok). split; [exact Hap|].
  exists b. split; [|exact Hok]. replace (a + i) with a in * by lia.
  unfold mrd in *. rewrite E. exact Hb.
Qed.

Lemma shadow_le : forall x y, x <= y -> shadow_addr x <= shadow_addr y.
Proof. intros x y H. unfold shadow_addr. pose proof (Z.div_le_mono x y 8 ltac:(lia) H). lia. Qed.

(* The shadow of a byte below / above the FakeStack FS is below the shadow of its class-6 frames / above them
   (fs6_shadow: S(fs_frame FS 6 0) = FS / 8 + 791040 + K, S(fs_frame FS 6 256) = FS / 8 + 922112 + K). *)
Lemma shadow_below_fs : forall a FS, 0 <= a -> a < FS -> shadow_addr a < FS / 8 + 791040 + ASAN_K.
Proof. intros a FS H0 H. unfold shadow_addr. pose proof (Z.div_le_mono a FS 8 ltac:(lia) ltac:(lia)). lia. Qed.

Lemma shadow_above_fs : forall a FS, FS mod 8 = 0 -> 0 <= FS -> FS + 11571200 <= a ->
  FS / 8 + 922112 + ASAN_K <= shadow_addr a.
Proof. intros a FS Hm H0 H. unfold shadow_addr. Z.div_mod_to_equations. lia. Qed.

Lemma shadow_of_frame : forall b, 0 <= b ->
  (exists y, 0 <= y /\ b = shadow_addr y) <-> ASAN_K <= b.
Proof.
  intros b Hb. split.
  - intros (y & Hy & ->). unfold shadow_addr. pose proof (Z.div_pos y 8 Hy ltac:(lia)). lia.
  - intros H. exists (8 * (b - ASAN_K)). split; [lia|]. unfold shadow_addr.
    replace (8 * (b - ASAN_K)) with ((b - ASAN_K) * 8) by lia. rewrite Z.div_mul by lia. lia.
Qed.

Definition Aof (S : Z) : Z := (S - 416) / 32 * 32.

(* Arithmetic of the class-6 side-stack layout, kept out of the segment proof's large context. *)
Lemma fs6_layout : forall FS j,
  fs_hint FS 6 = FS + 48 /\ fs_flag FS 6 j = FS + 36352 + j /\ fs_frame FS 6 j = FS + 6328320 + j * 4096.
Proof. intros FS j. unfold fs_hint, fs_flag, fs_frame, fs_B. cbn. lia. Qed.

Lemma fs6_shadow : forall FS j, 0 <= FS -> FS mod 4096 = 0 -> 0 <= j ->
  FS mod 8 = 0 /\ fs_frame FS 6 j mod 32 = 0 /\
  shadow_addr (fs_frame FS 6 j) = FS / 8 + 791040 + 512 * j + ASAN_K.
Proof.
  intros FS j H0 H1 Hj. destruct (fs6_layout FS j) as (_ & _ & E). rewrite E. unfold shadow_addr.
  split; [|split]; Z.div_mod_to_equations; lia.
Qed.

Lemma shadow_inv8 : forall FS a, FS mod 8 = 0 ->
  FS / 8 + 791040 + ASAN_K <= a < FS / 8 + 922112 + ASAN_K ->
  FS <= 8 * (a - ASAN_K) < FS + 11571200 /\ a = shadow_addr (8 * (a - ASAN_K)).
Proof.
  intros FS a H Ha. split.
  - Z.div_mod_to_equations. lia.
  - unfold shadow_addr. replace (8 * (a - ASAN_K)) with ((a - ASAN_K) * 8) by lia. rewrite Z.div_mul by lia. lia.
Qed.

Lemma div8_lo : forall FS, 6283264 <= FS -> 785408 <= FS / 8.
Proof. intros FS H. apply Z.div_le_lower_bound; lia. Qed.

Lemma Aof_bounds : forall S, S mod 16 = 0 -> S - 432 <= Aof S <= S - 416 /\ Aof S mod 32 = 0 /\ Aof S mod 16 = 0.
Proof. intros S H. unfold Aof. split; [|split]; Z.div_mod_to_equations; lia. Qed.

Lemma mod4096_32 : forall x, x mod 4096 = 0 -> x mod 32 = 0.
Proof. intros x H. Z.div_mod_to_equations. lia. Qed.

Lemma ba_rel1 : forall m m0 a bs, mem_rel rsegs m m0 -> bytes_at rsegs m a bs -> bytes_at rsegs m0 a bs.
Proof. intros m m0 a bs R H. exact (proj1 (bytes_at_rel rsegs m m0 a bs R) H). Qed.

Lemma asan_cells_rel : forall m m0, mem_rel rsegs m m0 -> asan_cells m -> asan_cells m0.
Proof.
  intros m m0 R H. unfold asan_cells in H |- *.
  repeat match goal with H' : _ /\ _ |- _ => destruct H' end.
  repeat match goal with |- _ /\ _ => split end;
    match goal with |- bytes_at _ _ ?a ?bs => exact (ba_rel1 m m0 a bs R ltac:(assumption)) end.
Qed.

Lemma asan_tls_cells_rel : forall m m0 TP DT TS C T DB k, mem_rel rsegs m m0 ->
  asan_tls_cells m TP DT TS C T DB k -> asan_tls_cells m0 TP DT TS C T DB k.
Proof.
  intros m m0 TP DT TS C T DB k R H.
  destruct H as (H1 & H2 & H3 & H4 & H5 & Hk & H7 & H8 & H9 & H10 & (tb & te & H11) & H12 & H13 & H14 & H15
                 & H16 & H17 & HDB & H19).
  unfold asan_tls_cells.
  split; [apply (ba_rel1 m m0 _ _ R); exact H1|].
  split; [apply (ba_rel1 m m0 _ _ R); exact H2|].
  split; [apply (ba_rel1 m m0 _ _ R); exact H3|].
  split; [apply (ba_rel1 m m0 _ _ R); exact H4|].
  split; [apply (ba_rel1 m m0 _ _ R); exact H5|].
  split; [exact Hk|].
  split; [apply (ba_rel1 m m0 _ _ R); exact H7|].
  split; [apply (ba_rel1 m m0 _ _ R); exact H8|].
  split; [apply (ba_rel1 m m0 _ _ R); exact H9|].
  split; [apply (ba_rel1 m m0 _ _ R); exact H10|].
  split; [exists tb, te; apply (ba_rel1 m m0 _ _ R); exact H11|].
  split; [apply (ba_rel1 m m0 _ _ R); exact H12|].
  split; [apply (ba_rel1 m m0 _ _ R); exact H13|].
  split; [apply (ba_rel1 m m0 _ _ R); exact H14|].
  split; [apply (ba_rel1 m m0 _ _ R); exact H15|].
  split; [apply (ba_rel1 m m0 _ _ R); exact H16|].
  split; [apply (ba_rel1 m m0 _ _ R); exact H17|].
  split; [exact HDB|].
  apply (ba_rel1 m m0 _ _ R); exact H19.
Qed.

Section T.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

(* The heap laws this file reads (Contract.a_laws), each taken apart once, here: a Theorem Labs lane's generations append
   conjuncts at every level, so a position is read only in these lemmas. *)


Lemma a1_mat : forall H mem md md', AsanLift.mat_le md md' ->
  (AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md -> AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md') /\
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md' = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md.
Proof.
  intros H mem md md' Hm. destruct (lw_mat_le (APIf rc) H mem md md' Hm) as [X _ Y _].
  split; [exact X | exact Y].
Qed.

Lemma a1_store : forall H mem mem' md, AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ AC.a_store_ok H (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a -> mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a) ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem' md /\
  (forall a, AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem' md a <-> AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem md a) /\
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\ AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md.
Proof.
  intros H mem mem' md HAH Hst Hw. destruct (lw_store (APIf rc) H mem mem' md HAH Hst Hw) as [X O Y Z].
  split; [exact X | split; [exact O | split; [exact Y | exact Z]]].
Qed.

Lemma a1_blocks : forall H mem md p n, AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md -> In (p, n) H ->
  p + n <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  (forall a, p <= a < p + n -> app_mem a /\ ~ AC.a_in_img a /\ ~ AC.a_in_fs AC.ASYMS mem a).
Proof.
  intros H mem md p n HAH Hin. destruct (lw_blocks (APIf rc) H mem md p n HAH Hin) as [_ _ X _ Y].
  split; [exact X|].
  intros a Ha. destruct (Y a Ha) as (Y1 & _ & Y3 & _ & Y5). split; [exact Y1 | split; [exact Y3 | exact Y5]].
Qed.

Lemma a1_fs_place : forall H mem md b, AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  word_mem rsegs mem (AC.as_tp AC.ASYMS) b -> 0 <= b < 2 ^ 64 ->
  AC.GT <= b /\ b + AC.FS_SIZE <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\ b mod 4096 = 0 /\ (forall a, b <= a < b + AC.FS_SIZE -> app_mem a).
Proof.
  intros H mem md b HAH Hw Hb. destruct (lw_fs_place (APIf rc) H mem md b HAH Hw Hb) as [X1 X2 X3 X4].
  split; [exact X1 | split; [exact X2 | split; [exact X3 | exact X4]]].
Qed.


Lemma a1_not_owned : forall H mem md a, AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  (AC.in_blocks H a \/ AC.in_slack H a \/ AC.a_in_fs AC.ASYMS mem a \/ AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md <= a < APPMEM_END) ->
  ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem md a /\ ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem md (shadow_addr a).
Proof.
  intros H mem md a HAH Ha. destruct (lw_not_owned (APIf rc) H mem md a HAH Ha) as [X Y].
  split; [exact X | exact Y].
Qed.

Lemma a1_fs_store : forall H mem mem' md FS, AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  word_mem rsegs mem (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ AC.a_store_ok H (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a -> ~ (FS <= a < FS + AC.FS_SIZE) ->
     ~ (exists b, FS <= b < FS + AC.FS_SIZE /\ a = shadow_addr b) -> mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a) ->
  AC.a_fs_ok mem' FS ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem' md /\ (forall a, AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem' md a <-> AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem md a) /\
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\ AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md.
Proof.
  intros H mem mem' md FS HAH Hw HFS Hst Hwr Hok.
  decompose [and] (AC.a_laws_fs_store _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) H mem mem' md FS HAH Hw HFS
                     Hst Hwr Hok).
  split; [assumption|]. split; [assumption|]. split; assumption.
Qed.

Lemma a1_fs_state : forall H mem md FS, AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  word_mem rsegs mem (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 ->
  AC.a_fs_ok mem FS /\
  (exists DB, 0 <= DB < 2 ^ 64 /\ word_mem rsegs mem (AC.as_tp AC.ASYMS + 8) DB /\ DB <> 0 /\
     word_mem rsegs mem (DB + 24) (AC.as_tp AC.ASYMS) /\
     forall a, DB + 24 <= a < DB + 32 -> app_mem a /\ a < AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) /\
  (forall C T, word_mem rsegs mem RT_TSDMAIN C -> 0 <= C < 2 ^ 64 -> word_mem rsegs mem (C + 152) T -> 0 <= T < 2 ^ 64 ->
     forall i, 0 <= i < 16 -> app_mem (T + 48 + i)).
Proof.
  intros H mem md FS HAH Hw HFS.
  destruct (fsf_fs_state_fields (APIf rc) H mem md FS HAH Hw HFS) as (DB & [Hok Dw Dr Dnz D24 Dc X]).
  split; [exact Hok|]. split; [|exact X].
  exists DB. split; [exact Dr|]. split; [exact Dw|]. split; [exact Dnz|]. split; [exact D24|].
  intros a Ha. destruct (Dc a Ha) as (Y1 & Y2 & _). split; [exact Y1 | exact Y2].
Qed.

Lemma a1_fs_ok_to : forall mem FS, AC.a_fs_ok mem FS ->
  (forall a, FS <= a < FS + AC.FS_SIZE -> writable_at rsegs mem a /\ exists b, mbyte rsegs mem a = Some b) /\
  word_mem rsegs mem (FS + 88) 20 /\ mbyte rsegs mem (FS + 96) = Some (Z_to_bv 8 0) /\
  (forall c, (c <= 10)%nat -> exists h, word_mem rsegs mem (AC.a_fs_hint FS c) h) /\
  (forall c j, (c <= 10)%nat -> 0 <= j < AC.a_fs_M c ->
     mbyte rsegs mem (AC.a_fs_flag FS c j) = Some (Z_to_bv 8 0) \/ mbyte rsegs mem (AC.a_fs_flag FS c j) = Some (Z_to_bv 8 1)).
Proof. intros mem FS H. exact H. Qed.
Lemma a1_fs_ok_of : forall mem FS,
  (forall a, FS <= a < FS + AC.FS_SIZE -> writable_at rsegs mem a /\ exists b, mbyte rsegs mem a = Some b) /\
  word_mem rsegs mem (FS + 88) 20 /\ mbyte rsegs mem (FS + 96) = Some (Z_to_bv 8 0) /\
  (forall c, (c <= 10)%nat -> exists h, word_mem rsegs mem (AC.a_fs_hint FS c) h) /\
  (forall c j, (c <= 10)%nat -> 0 <= j < AC.a_fs_M c ->
     mbyte rsegs mem (AC.a_fs_flag FS c j) = Some (Z_to_bv 8 0) \/ mbyte rsegs mem (AC.a_fs_flag FS c j) = Some (Z_to_bv 8 1)) ->
  AC.a_fs_ok mem FS.
Proof. intros mem FS H. exact H. Qed.

Lemma a1_thread : forall H mem md, AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  exists C T, word_mem rsegs mem RT_TSDMAIN C /\ 0 < C < 2 ^ 64 /\ 0 < T < 2 ^ 64 /\ word_mem rsegs mem (C + 152) T /\
    (forall i, 0 <= i < 8 -> AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem md (C + 152 + i) /\ app_mem (C + 152 + i)) /\
    (forall i, 0 <= i < 16 -> AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem md (T + 48 + i) /\ exists b, mbyte rsegs mem (T + 48 + i) = Some b).
Proof.
  intros H mem md HAH.
  destruct (fsf_thread_fields (APIf rc) H mem md HAH) as (C & T & [_ Hw HwT HC HT Hcell Ht48]).
  exists C, T. exact (conj Hw (conj HC (conj HT (conj HwT (conj Hcell Ht48))))).
Qed.

(* The thread-local cells __asan_stack_malloc_c reads (asan_stack_malloc_c.v:38-51), from RT and the heap laws:
   the TLS index / __tls_get_addr / the dtv and its slot and the pthread TSD chain, the control-flags and verbosity
   cells. DT, TS and k are fixed by RT (asan_uw_cells / asan_fs_cells); C and T come from the thread-record law
   AH9 (Contract.v a_laws_thread), which also gives the 16 bytes at T + 48 and their ownership, and DB from
   a_laws_fs_state. The ownership facts travel with the bundle: the stack-request premise needs the thread cells
   apart from the callee's window, and the allocator never owns a byte of the real stack (a_laws_not_owned). *)
Lemma a1_tls : forall (Hh : list (Z * Z)) mem md sp,
  AsanRTInv.RT sp mem md ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) Hh mem md ->
  exists DT TS C T DB k,
    asan_tls_cells mem (AC.as_tp AC.ASYMS) DT TS C T DB k /\
    bv_unsigned DT = AC.as_tp AC.ASYMS + 32 /\ bv_unsigned TS = RT_TSDMAIN /\ k = 0 /\
    (forall q, bv_unsigned C + 152 <= q < bv_unsigned C + 160 \/ bv_unsigned T + 48 <= q < bv_unsigned T + 64 ->
       AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) Hh mem md q) /\
    (forall q, bv_unsigned DB + 24 <= q < bv_unsigned DB + 32 ->
       q < AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md).
Proof.
  intros Hh mem md sp HRT HAH.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof HRT as (HC & HSW & HOPT & HCF & HUW & HREAL & HIM & HEX & HFS).
  destruct HOPT as (HO1 & HO2 & HO3 & HO4).
  destruct HCF as (HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8).
  destruct HUW as (HU1 & HU2 & HU3 & HU4 & Cw & HU5).
  destruct HFS as (HS1 & HS2 & HS3 & HS4 & (FSw & HS5 & HS5ok) & (DBw & HS6 & HS6nz)).
  (* the thread record: C, T and the 16 bytes at T + 48 *)
  destruct (a1_thread Hh mem md HAH) as (C & T & HwC & HCr & HTr & HwT & HCown & HT48).
  (* the dtv-base record DB *)
  destruct (a1_fs_state Hh mem md (bv_unsigned FSw) HAH
              (bytes_at_le8_word rsegs mem (AC.as_tp AC.ASYMS) FSw HS5)
              (bv_unsigned_in_range 64 FSw)) as (_ & (DB & HDBr & HwDB & HDBnz & HwDB24 & HDBlo) & HT48app).
  exists (Z_to_bv 64 (AC.as_tp AC.ASYMS + 32)), (Z_to_bv 64 RT_TSDMAIN), Cw, (Z_to_bv 64 T), DBw, 0.
  assert (ETP : AC.as_tp AC.ASYMS = RT_TP) by reflexivity.
  assert (ECw : bv_unsigned Cw = C).
  { apply (word_mem_unique mem RT_TSDMAIN); [exact (bytes_at_le8_word rsegs mem RT_TSDMAIN Cw HU5) | exact HwC
      | apply bv_unsigned_in_range | lia]. }
  assert (EDBw : bv_unsigned DBw = DB).
  { apply (word_mem_unique mem (AC.as_tp AC.ASYMS + 8));
      [ exact (bytes_at_le8_word rsegs mem (AC.as_tp AC.ASYMS + 8) DBw ltac:(rewrite ETP; exact HS6))
      | exact HwDB | apply bv_unsigned_in_range | lia]. }
  assert (HCapp : forall i, 0 <= i < 8 -> app_mem (C + 152 + i)) by (intros i Hi; exact (proj2 (HCown i Hi))).
  pose proof (HCapp 0 ltac:(lia)) as HCa0. pose proof (HCapp 7 ltac:(lia)) as HCa7.
  unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in HCa0, HCa7.
  assert (HTapp : forall i, 0 <= i < 16 -> app_mem (T + 48 + i))
    by (intros i Hi; exact (HT48app C T HwC ltac:(lia) HwT ltac:(lia) i Hi)).
  pose proof (HTapp 0 ltac:(lia)) as HTa0. pose proof (HTapp 15 ltac:(lia)) as HTa15.
  unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in HTa0, HTa15.
  pose proof (HDBlo (DB + 24) ltac:(lia)) as HDB0. pose proof (HDBlo (DB + 31) ltac:(lia)) as HDB7.
  destruct HDB0 as (HDBa0 & _). destruct HDB7 as (HDBa7 & _).
  unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in HDBa0, HDBa7.
  assert (EDT : bv_unsigned (Z_to_bv 64 (AC.as_tp AC.ASYMS + 32)) = AC.as_tp AC.ASYMS + 32)
    by (rewrite ETP; apply MState.unsigned_lit; unfold RT_TP; lia).
  assert (ETS : bv_unsigned (Z_to_bv 64 RT_TSDMAIN) = RT_TSDMAIN)
    by (apply MState.unsigned_lit; unfold RT_TSDMAIN; lia).
  assert (ETw : bv_unsigned (Z_to_bv 64 T) = T) by (apply MState.unsigned_lit; lia).
  (* the 16 bytes at T + 48, as two words *)
  destruct (bytes_exist mem 16 (T + 48) ltac:(lia) ltac:(cbn; lia)) as (bs & Lbs & Bbs).
  { intros j Hj. cbn in Hj. destruct (HT48 j ltac:(lia)) as (_ & b & Hb). exists b. exact Hb. }
  split.
  { unfold asan_tls_cells.
    split; [change TLS_INDEX with RT_TLSIDX; exact HS1|].
    split; [apply (real_cell_of mem REAL_TLS_GET_ADDR MUSL_TLS_GET_ADDR HREAL); vm_compute; reflexivity|].
    split; [rewrite ETP; exact HS3|].
    split; [rewrite EDT, ETP; replace (RT_TP + 32 + 8) with (RT_TP + 40) by lia; exact HS4|].
    split; [unfold TSD_KEY_INITED; exact HU1|].
    split; [unfold TSD_KEY; lia|].
    split; [unfold TSD_KEY; exact HU2|].
    split; [rewrite ETP; exact HU4|].
    split; [rewrite ETS; replace (RT_TSDMAIN + 8 * 0) with RT_TSDMAIN by lia; exact HU5|].
    split; [rewrite ECw; exact (word_mem_le8 rsegs mem (C + 152) T HwT ltac:(lia) ltac:(lia) ltac:(lia))|].
    split.
    { exists (Z_to_bv 64 (bytes_le_to_Z (firstn 8 bs))), (Z_to_bv 64 (bytes_le_to_Z (skipn 8 bs))).
      rewrite ETw.
      rewrite (le8_of_bytes (firstn 8 bs) ltac:(rewrite firstn_length; lia)).
      rewrite (le8_of_bytes (skipn 8 bs) ltac:(rewrite skipn_length; lia)).
      rewrite firstn_skipn. exact Bbs. }
    split; [unfold GOT_CF; exact HF1|].
    split; [unfold CF; exact HF6|].
    split; [unfold GOT_VERBOSITY; exact HO3|].
    split; [unfold VERBOSITY; exact HO4|].
    split; [unfold DTLS_TPOFF; exact HS2|].
    split; [rewrite ETP; exact HS6|].
    split; [rewrite EDBw; lia|].
    rewrite EDBw.
    exact (word_mem_le8 rsegs mem (DB + 24) (AC.as_tp AC.ASYMS) HwDB24 ltac:(unfold AC.as_tp, AC.ASYMS; cbn; lia)
             ltac:(lia) ltac:(lia)). }
  split; [exact EDT|].
  split; [exact ETS|].
  split; [reflexivity|].
  split.
  { intros q [Hq|Hq].
    - rewrite ECw in Hq. replace q with (C + 152 + (q - (C + 152))) by lia.
      exact (proj1 (HCown (q - (C + 152)) ltac:(lia))).
    - rewrite ETw in Hq. destruct (HT48 (q - (T + 48)) ltac:(lia)) as (Ho & _).
      replace q with (T + 48 + (q - (T + 48))) by lia. exact Ho. }
  intros q Hq. rewrite EDBw in Hq. exact (proj2 (HDBlo q Hq)).
Qed.

(* The FakeStack premises of the frame request (asan_stack_malloc_c.v:92-96), from RT's asan_fs_cells (the base
   word at tp and fs_value_ok) and the heap law a_laws_fs_state (a_fs_ok: the region present and writable, the
   header word 20 at FS + 88, the needs_gc byte 0 at FS + 96, a hint word per class and the 0/1 flag bytes).
   fs_place's `stk` is a_fs_ok's first conjunct. *)
Lemma a1_fs : forall (Hh : list (Z * Z)) mem md sp,
  AsanRTInv.RT sp mem md ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) Hh mem md ->
  exists FS,
    bytes_at rsegs mem (AC.as_tp AC.ASYMS) (le8 (Z_to_bv 64 FS)) /\
    word_mem rsegs mem (AC.as_tp AC.ASYMS) FS /\
    fs_place mem FS /\
    bytes_at rsegs mem (FS + 88) (le8 (Z_to_bv 64 20)) /\
    bytes_at rsegs mem (FS + 96) [Z_to_bv 8 0] /\
    (exists h : word, bytes_at rsegs mem (fs_hint FS 6) (le8 h)) /\
    (exists flags, bytes_at rsegs mem (fs_flag FS 6 0) flags /\ Z.of_nat (length flags) = fs_M 6 /\
       Forall (fun b => b = Z_to_bv 8 0 \/ b = Z_to_bv 8 1) flags) /\
    0 < FS /\ AC.GT <= FS /\ FS + FS_SIZE <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md.
Proof.
  intros Hh mem md sp HRT HAH.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof HRT as (_ & _ & _ & _ & _ & _ & _ & _ & HFS).
  destruct HFS as (_ & _ & _ & _ & (FSw & HS5 & HS5ok) & _).
  set (FS := bv_unsigned FSw) in *.
  assert (HwFS : word_mem rsegs mem (AC.as_tp AC.ASYMS) FS)
    by exact (bytes_at_le8_word rsegs mem (AC.as_tp AC.ASYMS) FSw HS5).
  pose proof (bv_unsigned_in_range 64 FSw) as HFSr.
  change (bv_modulus 64) with (2 ^ 64) in HFSr.
  destruct (a1_fs_place Hh mem md FS HAH HwFS HFSr) as (HGT & Hlo & Hal & Happ).
  destruct (a1_fs_state Hh mem md FS HAH HwFS HFSr) as (Hok & _ & _).
  destruct HS5ok as (HFS0 & _ & _ & _).
  destruct (a1_fs_ok_to mem FS Hok) as (Hpres & H88 & H96 & Hhint & Hflag).
  assert (HSZ : AC.FS_SIZE = FS_SIZE) by reflexivity.
  assert (Hbound : FS + FS_SIZE <= 2 ^ 64).
  { pose proof (Happ (FS + FS_SIZE - 1) ltac:(unfold AC.FS_SIZE, FS_SIZE in *; lia)) as Ha.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Ha. unfold FS_SIZE in *. lia. }
  assert (Hprs : forall q, FS <= q < FS + FS_SIZE -> exists b, mrd rsegs mem (wa q) = Some b).
  { intros q Hq. destruct (Hpres q ltac:(unfold AC.FS_SIZE, FS_SIZE in *; lia)) as (_ & b & Hb).
    exists b. exact Hb. }
  exists FS.
  split; [unfold FS; rewrite (Z_to_bv_bv_unsigned FSw); exact HS5|].
  split; [exact HwFS|].
  split.
  { split; [lia|]. split; [exact Hal|]. split; [unfold ASAN_GT; unfold AC.GT in HGT; lia|].
    split; [intros a Ha; exact (Happ a ltac:(unfold AC.FS_SIZE, FS_SIZE in *; lia))|].
    split; [lia|]. split; [lia|]. intros a Ha. destruct (Hpres a ltac:(unfold AC.FS_SIZE, FS_SIZE in *; lia)) as (Hw & Hb).
    split; [exact Hw | exact Hb]. }
  split; [exact (word_mem_le8 rsegs mem (FS + 88) 20 H88 ltac:(lia) ltac:(lia) ltac:(unfold FS_SIZE in *; lia))|].
  split.
  { split; [lia|]. split; [cbn [length]; lia|]. intros i Hi. cbn [length] in Hi.
    destruct i as [|i]; [|lia]. rewrite Z.add_0_r. exact H96. }
  split.
  { destruct (bytes_exist mem 8 (fs_hint FS 6) ltac:(unfold fs_hint; lia)
                ltac:(unfold fs_hint, FS_SIZE in *; cbn; lia)) as (bs & Lbs & Bbs).
    { intros j Hj. cbn in Hj. apply Hprs. unfold fs_hint, FS_SIZE in *; cbn; lia. }
    exists (Z_to_bv 64 (bytes_le_to_Z bs)). rewrite (le8_of_bytes bs Lbs). exact Bbs. }
  split.
  { destruct (bytes_exist mem 256 (fs_flag FS 6 0) ltac:(unfold fs_flag; cbn; lia)
                ltac:(unfold fs_flag, FS_SIZE in *; cbn; lia)) as (bs & Lbs & Bbs).
    { intros j Hj. cbn in Hj. apply Hprs. unfold fs_flag, FS_SIZE in *; cbn; lia. }
    exists bs. split; [exact Bbs|]. split; [rewrite Lbs; unfold fs_M; cbn; reflexivity|].
    apply Forall_forall. intros b Hb. apply In_nth_error in Hb. destruct Hb as (n & Hn).
    assert (Hnl : (n < 256)%nat) by (rewrite <- Lbs; apply (proj1 (nth_error_Some bs n)); rewrite Hn; discriminate).
    destruct Bbs as (_ & _ & Bb). pose proof (Bb n ltac:(lia)) as Eb. rewrite Hn in Eb.
    pose proof (Hflag 6%nat (Z.of_nat n) ltac:(lia) ltac:(unfold AC.a_fs_M; cbn; lia)) as Hf.
    assert (Eaddr : AC.a_fs_flag FS 6 (Z.of_nat n) = fs_flag FS 6 0 + Z.of_nat n)
      by (unfold AC.a_fs_flag, fs_flag; cbn; lia).
    rewrite Eaddr in Hf.
    destruct Hf as [Hf|Hf];
      [ left; assert (Ex : Some b = Some (Z_to_bv 8 0)) by (rewrite <- Eb; exact Hf)
      | right; assert (Ex : Some b = Some (Z_to_bv 8 1)) by (rewrite <- Eb; exact Hf) ];
      injection Ex as Ex; exact Ex. }
  split; [lia|].
  split; [exact HGT|].
  rewrite HSZ in Hlo. exact Hlo.
Qed.

Lemma mkR_set1 : forall (v x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
                         x24 x25 x26 x27 x28 x29 x30 x31 : word),
  bvmap_set 1 v (Frame.mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
                           x24 x25 x26 x27 x28 x29 x30 x31) =
  Frame.mkR v x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
              x24 x25 x26 x27 x28 x29 x30 x31.
Proof. intros. reflexivity. Qed.

(* The class-6 frame request at 0x80f50 (`jal frame_alloc_6`), on its contract (Sm6.stack_malloc_6). The contract
   needs mem_inv, which the slot pre does not give (the frame gives ro_agree only), so the call is run on the
   normalized memory (MemNorm.evt_normalize): every premise is a bytes_at / stk / fs_place / app_mem fact, each of
   which crosses mem_rel, and the post comes back with ms_rel and ro_same. *)
Lemma a1_req_evt :
  forall (ra0 gp tp0 t0 t1 t2 s0v s1v a1v a2v a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7v s8v s9 s10v s11 t3 t4 t5 t6 : word)
         (mem : word -> option byte) (A lo FS : Z) (h : word) (flags : list byte)
         (DT TS C T DB : word) (k : Z),
  bv_unsigned tp0 = AC.as_tp AC.ASYMS ->
  0 <= A < 2 ^ 64 ->
  ro_agree rsegs mem ->
  asan_cells mem -> shadow_rw mem ->
  asan_tls_cells mem (AC.as_tp AC.ASYMS) DT TS C T DB k ->
  bytes_at rsegs mem (AC.as_tp AC.ASYMS) (le8 (Z_to_bv 64 FS)) ->
  fs_place mem FS -> 0x5fe000 <= FS -> FS + FS_SIZE <= 2 ^ 64 ->
  bytes_at rsegs mem (FS + 88) (le8 (Z_to_bv 64 20)) ->
  bytes_at rsegs mem (FS + 96) [Z_to_bv 8 0] ->
  bytes_at rsegs mem (fs_hint FS 6) (le8 h) ->
  bytes_at rsegs mem (fs_flag FS 6 0) flags -> Z.of_nat (length flags) = fs_M 6 ->
  Forall (fun b => b = Z_to_bv 8 0 \/ b = Z_to_bv 8 1) flags ->
  stk rsegs mem lo A -> 0x5fe000 <= lo -> lo + ASAN_STACK_MALLOC_K <= A ->
  FS + FS_SIZE <= A - ASAN_STACK_MALLOC_K ->
  (forall a, A - ASAN_STACK_MALLOC_K <= a < A -> app_mem a) ->
  disjoint_from [(AC.as_tp AC.ASYMS - 88, AC.as_tp AC.ASYMS - 80);
                 (AC.as_tp AC.ASYMS - 8, AC.as_tp AC.ASYMS + 16);
                 (bv_unsigned DT + 8, bv_unsigned DT + 16);
                 (bv_unsigned TS + 8 * k, bv_unsigned TS + 8 * k + 8);
                 (bv_unsigned C + 152, bv_unsigned C + 160);
                 (bv_unsigned T + 48, bv_unsigned T + 64);
                 (bv_unsigned DB + 24, bv_unsigned DB + 32)] (A - ASAN_STACK_MALLOC_K) ASAN_STACK_MALLOC_K ->
  evt rsegs
    (fun ms => exists s0,
       asan_stack_malloc_post 6 ASAN_STACK_MALLOC_K (Z_to_bv 64 0x80f54) (Z_to_bv 64 A) gp tp0 s0v s1v
         s2 s3 s4 s5 s6 s7v s8v s9 s10v s11 fp_regs fp_csr 3136 FS h flags lo (normalize rsegs mem) s0 /\
       ms_rel rsegs ms s0 /\ ro_same rsegs mem (ms_mem ms))
    (MS (Frame.mkR ra0 (Z_to_bv 64 A) gp tp0 t0 t1 t2 s0v s1v (Z_to_bv 64 3136) a1v a2v a3 a4 a5 a6 a7
                   s2 s3 s4 s5 s6 s7v s8v s9 s10v s11 t3 t4 t5 t6)
        fp_regs (Z_to_bv 64 0x80f50) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros ra0 gp tp0 t0 t1 t2 s0v s1v a1v a2v a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7v s8v s9 s10v s11 t3 t4 t5 t6
    mem A lo FS h flags DT TS C T DB k
    HTP HAr HRO HAC HSW HTLS HFSw HFSp HFSlo HFShi H88 H96 Hh Hfl Hfll Hfl01 HST HLOlo HLOK HROOM HAPP HDJ.
  step. change (bvmap_set 1 (Z_to_bv 64 0x80f54) (Frame.mkR ra0 (Z_to_bv 64 A) gp tp0 t0 t1 t2 s0v s1v (Z_to_bv 64 3136) a1v a2v a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7v s8v s9 s10v s11 t3 t4 t5 t6)) with (Frame.mkR (Z_to_bv 64 0x80f54) (Z_to_bv 64 A) gp tp0 t0 t1 t2 s0v s1v (Z_to_bv 64 3136) a1v a2v a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7v s8v s9 s10v s11 t3 t4 t5 t6).
  pose proof (mem_rel_normalize rsegs mem HRO) as REL.
  assert (HC : evt rsegs
      (asan_stack_malloc_post 6 ASAN_STACK_MALLOC_K (Z_to_bv 64 0x80f54) (Z_to_bv 64 A) gp tp0 s0v s1v
         s2 s3 s4 s5 s6 s7v s8v s9 s10v s11 fp_regs fp_csr (bv_unsigned (Z_to_bv 64 3136)) FS h flags lo
         (normalize rsegs mem))
      (MS (Frame.mkR (Z_to_bv 64 0x80f54) (Z_to_bv 64 A) gp tp0 t0 t1 t2 s0v s1v (Z_to_bv 64 3136)
                     a1v a2v a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7v s8v s9 s10v s11 t3 t4 t5 t6)
          fp_regs (Z_to_bv 64 ASAN_STACK_MALLOC_6) fp_csr None (normalize rsegs mem) (seg_rom rsegs))).
  { apply (Sm6.stack_malloc_6 (Z_to_bv 64 0x80f54) (Z_to_bv 64 A) gp tp0 t0 t1 t2 s0v s1v (Z_to_bv 64 3136)
             a1v a2v a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7v s8v s9 s10v s11 t3 t4 t5 t6 fp_regs fp_csr
             (normalize rsegs mem) lo FS h DT TS C T DB k flags).
    all: rewrite ?(MState.unsigned_lit 3136), ?(MState.unsigned_lit A), ?HTP by lia.
    - unfold fs_B. cbn. lia.
    - reflexivity.
    - exact (asan_cells_rel mem _ REL HAC).
    - exact (shadow_rw_rel mem _ REL HSW).
    - apply mem_inv_normalize.
    - exact (asan_tls_cells_rel mem _ _ _ _ _ _ _ _ REL HTLS).
    - intros Hc. lia.
    - apply (ba_rel1 mem _ _ _ REL); exact HFSw.
    - exact (fs_place_rel mem _ FS REL HFSlo HFShi HFSp).
    - apply (ba_rel1 mem _ _ _ REL); exact H88.
    - apply (ba_rel1 mem _ _ _ REL); exact H96.
    - apply (ba_rel1 mem _ _ _ REL); exact Hh.
    - apply (ba_rel1 mem _ _ _ REL); exact Hfl.
    - exact Hfll.
    - exact Hfl01.
    - exact (stk_rel_hi mem _ lo A REL HLOlo ltac:(lia) HST).
    - exact HLOK.
    - exact HROOM.
    - exact HAPP.
    - exact HDJ. }
  rewrite (MState.unsigned_lit 3136 ltac:(lia)) in HC.
  exact (evt_normalize rsegs _ _ fp_regs _ fp_csr None mem (seg_rom rsegs) ltac:(vm_compute; reflexivity) HRO HC).
Qed.

(* Lib-evt -> SR bridge (sl_run for a Lib.Exec.evt run, as A/Prog/Seg F18's sl_run_lib). *)
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

(* The entry-state facts of the slot pre that the prologue run and the request need. *)
Lemma a1_entry : forall g,
  AF.alib_pre B AsanRTInv.RT (APIf rc) AF.SLOT_STACK empty (g_H g) (g_regs g) (g_mem g) (g_md g)
    ra (g_p g) (g_n g) (g_in g) ->
  let S := AC.aspZ (g_regs g) in
  AsanRTInv.RT S (g_mem g) (g_md g) /\
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (g_H g) (g_mem g) (g_md g) /\
  ro_agree rsegs (g_mem g) /\ m_halted (g_md g) = None /\
  getr (g_regs g) 2 = Z_to_bv 64 S /\ S mod 16 = 0 /\
  getr (g_regs g) 4 = Z_to_bv 64 (AC.as_tp AC.ASYMS) /\
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) (g_mem g) (g_md g) <= S - AF.SLOT_STACK /\
  HIGHMEM_BEG <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) (g_mem g) (g_md g) /\
  S < APPMEM_END /\
  stk rsegs (g_mem g) (S - AF.SLOT_STACK) S /\
  (forall a, S - AF.SLOT_STACK <= a < S -> app_mem a).
Proof.
  intros g Hpre S.
  destruct Hpre as (Hcp & _).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  (* a_call_pre by its named projections (generated conjunction: never by position) *)
  pose proof Hcp as Hrt; apply AC.a_call_pre_rt in Hrt.
  pose proof Hcp as Hah; apply AC.a_call_pre_ah in Hah.
  pose proof Hcp as Hal; apply AC.a_call_pre_sp_align in Hal.
  pose proof Hcp as Hlo; apply AC.a_call_pre_stklo in Hlo.
  pose proof Hcp as Hsa; apply AC.a_call_pre_sp_app in Hsa.
  assert (Hwin : forall a, AC.a_window AF.SLOT_STACK (g_regs g) a ->
            writable_at rsegs (g_mem g) a /\ addressable (g_mem g) a 1 /\ ~ AC.in_blocks (g_H g) a)
    by (eapply AC.a_call_pre_window; exact Hcp).
  pose proof Hcp as Htp; apply AC.a_call_pre_tp in Htp.
  pose proof Hcp as Hro; apply AC.a_call_pre_ro in Hro.
  pose proof Hcp as Hlv; apply AC.a_call_pre_live in Hlv.
  assert (Hwp : forall a, AC.a_window AF.SLOT_STACK (g_regs g) a -> exists b, mbyte rsegs (g_mem g) a = Some b)
    by (eapply AC.a_call_pre_win_present; exact Hcp).
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS (g_H g) (g_mem g) (g_md g) Hah) as Hhigh.
  assert (Hsp2 : getr (g_regs g) 2 = Z_to_bv 64 S).
  { unfold S, AC.aspZ. rewrite (Z_to_bv_bv_unsigned (getr (g_regs g) 2)). reflexivity. }
  assert (HAPP : forall a, S - AF.SLOT_STACK <= a < S -> app_mem a).
  { intros a Ha. destruct (Hwin a ltac:(unfold AC.a_window; unfold S in *; lia)) as (_ & Had & _).
    destruct Had as (_ & _ & _ & Hb). destruct (Hb 0 ltac:(lia)) as (Hap & _). rewrite Z.add_0_r in Hap. exact Hap. }
  split; [exact Hrt|]. split; [exact Hah|]. split; [exact Hro|]. split; [exact Hlv|].
  split; [exact Hsp2|]. split; [exact Hal|]. split; [exact Htp|]. split; [exact Hlo|].
  split; [exact Hhigh|]. split; [exact Hsa|].
  split; [|exact HAPP].
  split; [unfold HIGHMEM_BEG, AF.SLOT_STACK in *; lia|].
  split; [unfold APPMEM_END in Hsa; lia|].
  intros a Ha. destruct (Hwin a ltac:(unfold AC.a_window; unfold S in *; lia)) as (Hw & _ & _).
  destruct (Hwp a ltac:(unfold AC.a_window; unfold S in *; lia)) as (b & Hb).
  split; [exact Hw | exists b; exact Hb].
Qed.


Lemma in_globals_bound : forall G top a,
  forallb (fun p => fst p + snd p <=? top) G = true -> in_globals G a -> a < top.
Proof.
  intros G top a Hb (lo & len & Hin & Hr). rewrite forallb_forall in Hb.
  pose proof (Hb _ Hin) as H. cbn in H. apply Z.leb_le in H. lia.
Qed.

Lemma frame_AG_low : forall a, in_globals AF.frame_AG a -> a < 0x5fe000.
Proof. intros a. apply in_globals_bound. vm_compute. reflexivity. Qed.

(* PREF moves across a register change that keeps sp, gp, tp, s0, s1, s10 and across lazy-page materialization. *)
Lemma pref_move : forall g A sp regs regs' mem md md',
  PREF B APIf ra g A sp regs mem md ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 26 = getr regs 26 ->
  AsanLift.mat_le md md' ->
  PREF B APIf ra g A sp regs' mem md'.
Proof.
  intros g A sp regs regs' mem md md' HP E2 E3 E4 E8 E9 E26 Hmat.
  destruct HP as (HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz & Hstklo & Hr4 & Hr8 & Hr9 & Hr3 &
    Hr26 & HAm & HAS & HS432 & Hspa & HA416 & HS4096 & HSapp & Hstk & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & HnMax & Hlive).
  destruct (a1_mat (g_H g) mem md md' Hmat) as (HAHm & Hstklo_eq).
  split; [exact (AsanRTInv.RT_any sp sp mem md md' HRT)|].
  split; [exact (HAHm HAH)|].
  split; [exact Hro|].
  split; [destruct Hsn as (He & Hh & Hf); split; [exact He|];
          split; [exact Hh|]; rewrite (sl_mat_fds md md' Hmat); exact Hf|].
  split; [rewrite (AsanLift.mat_le_halted md md' Hmat); exact Hhalt|].
  split; [exact Hgimg|].
  split; [rewrite E2; exact Hr2|].
  split; [exact Hspm|].
  split; [unfold AC.aspZ in *; rewrite E2; exact Haspz|].
  split; [rewrite Hstklo_eq; exact Hstklo|].
  split; [rewrite E4; exact Hr4|].
  split; [unfold rg in *; rewrite E8; exact Hr8|].
  split; [unfold rg in *; rewrite E9; exact Hr9|].
  split; [rewrite E3; exact Hr3|].
  split; [unfold rg in *; rewrite E26; exact Hr26|].
  repeat (split; [assumption|]). exact Hlive.
Qed.

(* The input facts of the entry pre at a later memory m that keeps the bytes of every entry block the target does
   not keep (ENT) and, for n > 0, the shadow bytes of the input block: the input bytes at p, and for n > 0 the block
   (p, n) live in H and addressable. For n = 0, p is the empty buffer (FF: empty = 0x5daee0). *)
Lemma a1_input : forall g m,
  AF.alib_pre B AsanRTInv.RT (APIf rc) AF.SLOT_STACK empty (g_H g) (g_regs g) (g_mem g) (g_md g)
    ra (g_p g) (g_n g) (g_in g) ->
  (0 < g_n g -> ~ In (g_p g, g_n g) (g_T g)) ->
  (forall q k i, In (q, k) (g_H g) -> ~ In (q, k) (g_T g) -> 0 <= i < k ->
     mbyte rsegs m (q + i) = mbyte rsegs (g_mem g) (q + i)) ->
  (0 < g_n g -> forall i, 0 <= i < g_n g ->
     m (wa (shadow_addr (g_p g + i))) = g_mem g (wa (shadow_addr (g_p g + i)))) ->
  bytes_at rsegs m (g_p g) (g_in g) /\
  (0 < g_n g -> In (g_p g, g_n g) (g_H g) /\ addressable m (g_p g) (g_n g)).
Proof.
  intros g m Hpre HnT Hblk Hsh.
  pose proof (proj1 FF) as SEGS.
  pose proof FF as (_ & _ & _ & _ & _ & _ & _ & Hempty & _).
  destruct Hpre as (_ & _ & _ & _ & Hbuf & Hlen & _ & Hbd & _).
  destruct Hbuf as [(Hn0 & Hpe) | (Hn0 & Hin & Had)].
  - assert (Hnil : g_in g = []).
    { destruct (g_in g) as [|b l] eqn:E; [reflexivity|]. exfalso. try rewrite E in Hlen. cbn [length] in Hlen. lia. }
    split.
    + rewrite Hnil, Hpe, Hempty. split; [lia|]. split; [cbn [length]; lia|]. intros i Hi. cbn [length] in Hi. lia.
    + intros H. lia.
  - pose proof Had as (Hp0 & _ & Hpn & _).
    split.
    + split; [exact Hp0|]. split; [rewrite <- Hlen; unfold APPMEM_END in Hpn; lia|].
      intros i Hi.
      pose proof (Hbd (Z.of_nat i) ltac:(lia)) as E. try rewrite SEGS in E. rewrite Nat2Z.id in E. rewrite <- E.
      exact (Hblk _ _ (Z.of_nat i) Hin (HnT Hn0) ltac:(lia)).
    + intros _. split; [exact Hin|].
      destruct Had as (Hp0' & Hn0' & Hpn' & Hab). split; [exact Hp0'|]. split; [exact Hn0'|]. split; [exact Hpn'|].
      intros i Hi. destruct (Hab i Hi) as (Hap & b & Hb & Hok). split; [exact Hap|].
      exists b. split; [|exact Hok]. unfold mrd in Hb |- *. rewrite (Hsh Hn0 i Hi). exact Hb.
Qed.

(* seg_A1 builds ENT at its exit from the entry (Tac_slot.ent_entry), and ENT's 14th conjunct at the entry is the
   slot's named premise ENTRY_CLASS (Tac_slot's Section EntryClass): the entry heap's per-class bound, which
   FrameAPI.alib_pre does not give (it gives only a_live_bytes H <= 5 * 2 ^ 30). seg_A1 takes the same premise, in
   a one-lemma section with the same text, so that the slot proof passes one ENTRY_CLASS to both. *)
Section EntryClassA1.
Hypothesis ENTRY_CLASS : forall g c, Inv_ENTRY B APIf ra empty g c ->
  exists BE : Z -> Z,
    (forall cl, 0 <= cl < AsanCtrl.K_NUM_CLASSES -> ClassConsDef.a_class_bytes (g_H g) cl <= BE cl) /\
    (forall cl, 0 <= cl < AsanCtrl.K_NUM_CLASSES -> BE cl + BC_ctrl cl <= 2 ^ 22).

Lemma seg_A1 : Hcut B APIf ra (Inv_A80f54 B APIf ra) -> Hcut B APIf ra (Inv_A80f88 B APIf ra) ->
  Hcut B APIf ra (Inv_ENTRY B APIf ra empty).
Proof.
  (* The UAR switch word is 1 (RT's asan_cells), so `beqz a2,0x80f5c` at 0x80f44 is never taken: the run always
     reaches the request's return 0x80f54, and the exit 0x80f88 (via 0x80f5c and the stack probe) is not used. *)
  intros Hexit _ g c HInv.
  pose proof (proj1 FF) as SEGS.
  pose proof FRAME_BYTES_val as HFBv.
  pose proof HInv as HInv0.
  destruct HInv as (Ec & Hpre & HT1 & HT2 & Hgimg & Hasp & Hfrm). subst c.
  pose proof Hpre as Hpre2.
  destruct (a1_entry g Hpre2) as (HRT0 & HAH0 & Hro0 & Hhalt0 & Hsp2 & Hal & Htp & Hstklo0 & Hhigh & HSapp &
    HST0 & HAPP0).
  pose proof Hpre as Hpre3.
  destruct Hpre3 as (Hcp3 & Hra & Hp & Hn & Hbuf & Hlen & Hnmax & Hbd & HAGe & Hlvb & Herrno0 & Hsn0 & Hfd & Hfs & Himge).
  pose proof Hcp3 as (_ & _ & Hret & _ & _ & _ & Hshi & Hshia & Hpres & Hwin & _ & _ & _ & _).
  set (S := AC.aspZ (g_regs g)) in *.
  set (A := Aof S) in *.
  rewrite SEGS.
  apply (sl_run_lib (g_regs g) (Z_to_bv 64 AF.ENTRY) (g_mem g) (g_md g)
    (fun R pc' mem' => pc' = Z_to_bv 64 0x80f54 /\
       exists r, PREF B APIf ra g A A R mem' (g_md g) /\ ENT APIf g [] mem' (g_md g) /\
         rg R 10 r /\ 0 <= r < 2 ^ 64 /\ rg R 23 (g_p g) /\ rg R 24 (g_n g) /\
         (r = 0 \/ (r mod 32 = 0 /\
            (forall FS, word_mem rsegs mem' (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 -> FS + 6328320 <= r) /\
            (forall a, r <= a < r + FRAME_BYTES -> AC.a_in_fs AC.ASYMS mem' a) /\ FSREC r mem')) /\
         bytes_at rsegs mem' (g_p g) (g_in g) /\
         (0 < g_n g -> In (g_p g, g_n g) (g_H g) /\ addressable mem' (g_p g) (g_n g))) (Post B APIf ra g)).
  - exact Hhalt0.
  - rewrite mkR_of_expand, Hsp2.
    unfold AF.SLOT_STACK in HST0, Hstklo0. unfold HIGHMEM_BEG in Hhigh. unfold APPMEM_END in HSapp.
    eapply LE.evt_cut.
    { apply a1_store_evt; [unfold HIGHMEM_BEG; lia | unfold APPMEM_END; lia | exact HST0]. }
    intros ms1 (mem1 & E1 & MU1 & WM1 & ST1 & SAV1). subst ms1.
    assert (HAW0 : all_app [(S - 416, S)]).
    { cbn [all_app]. split; [|exact I]. intros a Ha. unfold app_mem. right.
      unfold HIGHMEM_BEG, APPMEM_END. lia. }
    assert (HD0 : rt_disjoint [(S - 416, S)]).
    { unfold rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
        RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB,
        RT_AGLOB_LEN. cbn [disjoint_from]. repeat split; first [left; lia | exact I]. }
    pose proof (AsanRTInv.RT_store S S (g_mem g) mem1 (g_md g) (g_md g) _ HRT0 MU1 WM1 HAW0 HD0) as HRT1.
    pose proof HRT1 as (HC1 & _).
    destruct HC1 as (HKc & HGK & _ & _ & _ & HUc & HGU & _).
    eapply LE.evt_cut.
    { apply a1_tail_evt with (S := S) (A := A);
        [unfold HIGHMEM_BEG; lia | unfold APPMEM_END; lia | reflexivity
         | unfold GOT_UAR, UAR; exact HGU
         | unfold GOT_CELL_K, CELL_K; exact HGK
         | unfold UAR; exact HUc
         | unfold CELL_K; exact HKc]. }
    intros ms2 (a1' & a2' & E2). subst ms2.
    (* the request's premises on mem1 *)
    assert (HstoreC0 : forall a, 0 <= a < 2 ^ 64 ->
      ~ AC.a_store_ok (g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) (g_mem g) (g_md g)) a ->
      mem1 (Z_to_bv 64 a) = g_mem g (Z_to_bv 64 a)).
    { intros a Ha Hns. apply MU1. rewrite MState.unsigned_lit by lia.
      destruct (kb_outside_dec [(S - 416, S)] a) as [Ho|Ho]; [exact Ho|].
      exfalso. apply Hns. unfold AC.a_store_ok. right; left. split.
      - destruct (Z.le_gt_cases (S - 416) a); [lia|]. exfalso; apply Ho; cbn; split; [lia | exact I].
      - destruct (Z.lt_ge_cases a S); [unfold APPMEM_END; lia|]. exfalso; apply Ho; cbn; split; [lia | exact I]. }
    pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
    destruct (a1_store (g_H g) (g_mem g) mem1 (g_md g) HAH0 HstoreC0
                (fun a _ Hw => WM1 (Z_to_bv 64 a) Hw)) as (HAH1 & HOWN1 & HSTK1 & HSTKhi1).
    destruct (a1_tls (g_H g) mem1 (g_md g) S HRT1 HAH1)
      as (DT & TS & C & T & DB & k & HTLS & EDT & ETS & Ek & HOWNtc & HDBlo).
    destruct (a1_fs (g_H g) mem1 (g_md g) S HRT1 HAH1)
      as (FS & HFSb & HFSw & HFSp & H88 & H96 & (h & Hh) & (flags & Hfl & Hfll & Hfl01) & HFS0 & HGT & HFSlo).
    assert (HstkloEq : AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem1 (g_md g) =
                       AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) (g_mem g) (g_md g)) by exact HSTK1.
    assert (HAr : S - 432 <= A <= S - 416 /\ A mod 32 = 0)
      by (unfold A; destruct (Aof_bounds S Hal) as (X & Y & _); split; [exact X | exact Y]).
    assert (HNO : forall q, AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (g_H g) mem1 (g_md g) q ->
              q < AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem1 (g_md g) \/ 140737488355328 <= q).
    { intros q Hq. destruct (Z.lt_ge_cases q (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem1 (g_md g)))
        as [Hl|Hl]; [left; exact Hl|].
      destruct (Z.lt_ge_cases q 140737488355328) as [Hu|Hu]; [|right; exact Hu].
      exfalso. exact (proj1 (a1_not_owned (g_H g) mem1 (g_md g) q HAH1
                               (or_intror (or_intror (or_intror (conj Hl Hu))))) Hq). }
    assert (HC0 := HOWNtc (bv_unsigned C + 152) ltac:(left; lia)).
    assert (HC7 := HOWNtc (bv_unsigned C + 159) ltac:(left; lia)).
    assert (HT0 := HOWNtc (bv_unsigned T + 48) ltac:(right; lia)).
    assert (HT15 := HOWNtc (bv_unsigned T + 63) ltac:(right; lia)).
    apply HNO in HC0, HC7, HT0, HT15. rewrite HstkloEq in HC0, HC7, HT0, HT15.
    pose proof (HDBlo (bv_unsigned DB + 31) ltac:(lia)) as HDB7. rewrite HstkloEq in HDB7.
    rewrite HstkloEq in HFSlo.
    destruct (stk_split rsegs mem1 (S - 1048576) A S ST1 ltac:(lia)) as (STlo & _).
    assert (Hro1 : ro_agree rsegs mem1).
    { apply (ro_agree_hi [(S - 416, S)] (g_mem g) mem1 Hro0 MU1). intros x Hx Ho.
      destruct (Z.le_gt_cases (S - 416) x); [unfold HIGHMEM_BEG in *; lia|].
      exfalso; apply Ho; cbn; split; [lia | exact I]. }
    eapply LE.evt_mono.
    { eapply a1_req_evt with (A := A) (lo := S - 1048576) (FS := FS) (h := h) (flags := flags)
        (DT := DT) (TS := TS) (C := C) (T := T) (DB := DB) (k := k).
      - rewrite Htp. apply MState.unsigned_lit. unfold AC.as_tp, AC.ASYMS; cbn; lia.
      - lia.
      - exact Hro1.
      - exact (AsanRTInv.RT_cells _ _ _ HRT1).
      - exact (AsanRTInv.RT_shadow_rw _ _ _ HRT1).
      - exact HTLS.
      - exact HFSb.
      - exact HFSp.
      - unfold AC.GT in HGT. lia.
      - unfold FS_SIZE in *. lia.
      - exact H88.
      - exact H96.
      - exact Hh.
      - exact Hfl.
      - exact Hfll.
      - exact Hfl01.
      - exact STlo.
      - lia.
      - unfold ASAN_STACK_MALLOC_K. lia.
      - unfold ASAN_STACK_MALLOC_K, FS_SIZE in *. lia.
      - intros a Ha. apply HAPP0. unfold ASAN_STACK_MALLOC_K in Ha. unfold AF.SLOT_STACK. lia.
      - rewrite EDT, ETS, Ek. unfold ASAN_STACK_MALLOC_K, AC.as_tp, AC.ASYMS, RT_TSDMAIN. cbn [disjoint_from].
        cbn. repeat split; lia. }
    intros ms3 (s0 & HQ & Hrel & Hsame).
    destruct HQ as (t0' & t1' & t2' & a0' & a1'' & a2'' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0'
                    & Es0 & WM0 & MI0 & ST0' & FSP0 & (h' & Hh') & Hcase).
    subst s0.
    destruct ms3 as [R3 F3 pc3 sv3 rv3 fc3 m3 ro3].
    destruct Hrel as (ER & EF & Epc & Esv & Erv & Efc & Erom & Erel).
    cbn in ER, EF, Epc, Esv, Erv, Efc, Erom, Erel. subst.
    replace (ret_pc (Z_to_bv 64 0x80f54)) with (Z_to_bv 64 0x80f54) by (apply bv_eq; vm_compute; reflexivity).
    eexists _, _, m3. split; [reflexivity|].
    split; [reflexivity|].
    match goal with |- exists r, PREF _ _ _ _ _ _ ?RR _ _ /\ _ => set (R := RR) end.
    (* ---- transports of the request's post from the normalized run *)
    pose proof (mem_rel_normalize rsegs mem1 Hro1) as REL1.
    assert (MUrel : forall W, munch W (normalize rsegs mem1) m0' -> munch W mem1 m3)
      by (intros W HW; exact (munch_rel rsegs W mem1 (normalize rsegs mem1) m3 m0' REL1 Erel Hsame HW)).
    pose proof (wmono_rel rsegs mem1 (normalize rsegs mem1) m3 m0' REL1 Erel Hsame WM0) as WM3.
    rewrite (MState.unsigned_lit A) in ST0' by lia.
    pose proof (stk_rel_hi_back m3 m0' (S - 1048576) A Erel ltac:(lia) ltac:(lia) ST0') as ST3.
    pose proof (fs_place_rel_back m3 m0' FS Erel ltac:(unfold AC.GT in HGT; lia) ltac:(unfold FS_SIZE in *; lia) FSP0)
      as FSP3.
    pose proof (proj2 (bytes_at_rel rsegs m3 m0' _ _ Erel) Hh') as Hh3.
    rewrite (MState.unsigned_lit A) in Hcase by lia.
    pose proof FSP3 as (HFS0' & HFSal & HFSgt & HFSapp & _).
    assert (HKsz : ASAN_STACK_MALLOC_K = 208) by reflexivity.
    assert (HFSz : FS_SIZE = 11571200) by reflexivity.
    assert (Hstk1 : AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) (g_mem g) (g_md g) <= S - 1048576) by exact Hstklo0.
    (* mem1's FakeStack state *)
    destruct (a1_fs_state (g_H g) mem1 (g_md g) FS HAH1 HFSw ltac:(unfold FS_SIZE in *; lia))
      as (Hok1 & _ & _).
    destruct (a1_fs_ok_to mem1 FS Hok1) as (Hpres1 & H881 & H961 & Hhint1 & Hflag1).
    (* the frame bytes and their shadow *)
    assert (Hfrapp : forall jj, 0 <= jj < 256 -> forall x, fs_frame FS 6 jj <= x < fs_frame FS 6 jj + 4096 ->
              app_mem x).
    { intros jj Hjj x Hx. apply HFSapp. destruct (fs6_layout FS jj) as (_ & _ & E). rewrite E in Hx.
      unfold FS_SIZE in HFSlo |- *. lia. }
    assert (Hflapp : forall c jj, (c <= 10)%nat -> 0 <= jj < AC.a_fs_M c -> app_mem (AC.a_fs_flag FS c jj)).
    { intros c jj Hc Hjj. pose proof (a_fs_flag_range FS c jj Hc Hjj). apply HFSapp. unfold FS_SIZE. lia. }
    assert (Hhapp : forall x, fs_hint FS 6 <= x < fs_hint FS 6 + 8 -> app_mem x).
    { intros x Hx. apply HFSapp. destruct (fs6_layout FS 0) as (E & _ & _). rewrite E in Hx.
      unfold FS_SIZE in HFSlo |- *. lia. }
    assert (Hwapp : forall x, A - 208 <= x < A -> app_mem x).
    { intros x Hx. apply HAPP0. unfold AF.SLOT_STACK. lia. }
    (* side-stack layout of class 6 *)
    destruct (fs6_layout FS 0) as (Ehint6 & Eflag6' & Efr0').
    assert (Eflag6 : fs_flag FS 6 0 = FS + 36352) by lia.
    assert (Efr0 : fs_frame FS 6 0 = FS + 6328320) by lia.
    assert (Efr256 : fs_frame FS 6 256 = FS + 7376896) by (destruct (fs6_layout FS 256) as (_ & _ & E); lia).
    clear Eflag6' Efr0'.
    unfold AC.GT in HGT.
    assert (HKv : ASAN_K = 2147450880) by reflexivity.
    assert (Hsh0 : ASAN_K + 785408 <= shadow_addr (fs_frame FS 6 0)).
    { destruct (fs6_shadow FS 0 ltac:(lia) HFSal ltac:(lia)) as (_ & _ & E). rewrite E.
      pose proof (div8_lo FS HGT). lia. }
    assert (Hsh256 : shadow_addr (fs_frame FS 6 256) <= shadow_addr (S - 1048576)) by (apply shadow_le; lia).
    assert (HshS : forall y, 0 <= y < 140737488355328 -> ASAN_K <= shadow_addr y < 17594333495296).
    { intros y Hy. unfold shadow_addr. split; [pose proof (Z.div_pos y 8 ltac:(lia) ltac:(lia)); lia|].
      assert (y / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia). lia. }
    pose proof (HshS (S - 1048576) ltac:(lia)) as HshS0.
    pose proof (AsanRTInv.RT_shadow_rw _ _ _ HRT1) as HSW1.
    assert (Happ_ns : forall x, app_mem x -> in_shadow x -> False) by exact app_not_shadow.
    (* the case-uniform facts of the request's post *)
    assert (HU : exists r, a0' = Z_to_bv 64 r /\ 0 <= r < 2 ^ 64 /\
       munch [(fs_hint FS 6, fs_hint FS 6 + 8); (fs_flag FS 6 0, fs_flag FS 6 0 + 256);
              (fs_frame FS 6 0, fs_frame FS 6 256);
              (shadow_addr (fs_frame FS 6 0), shadow_addr (fs_frame FS 6 256)); (A - 208, A)] mem1 m3 /\
       (forall x, in_shadow x -> exists b, mrd rsegs m3 (wa x) = Some b) /\
       (forall c jj, (c <= 10)%nat -> 0 <= jj < AC.a_fs_M c ->
          mbyte rsegs m3 (AC.a_fs_flag FS c jj) = Some (Z_to_bv 8 0) \/
          mbyte rsegs m3 (AC.a_fs_flag FS c jj) = Some (Z_to_bv 8 1)) /\
       (r = 0 \/ (r mod 32 = 0 /\ FS + 6328320 <= r /\ r + 4096 <= FS + FS_SIZE /\ FS <= r /\
          exists j, 0 <= j < 256 /\ r = fs_frame FS 6 j /\ bytes_at rsegs m3 (fs_flag FS 6 j) [Z_to_bv 8 1] /\
            bytes_at rsegs m3 (r + 4096 - 8) (le8 (Z_to_bv 64 (fs_flag FS 6 j)))))).
    { destruct Hcase as [(_ & Ea0 & MUr) | (i0 & Hi0 & _ & _ & FR)].
      - (* refusal: a0 = 0; only the class-6 hint word and the callee window are written *)
        apply MUrel in MUr. rewrite HKsz in MUr.
        exists 0. split; [exact Ea0|]. split; [lia|].
        split.
        { refine (munch_weaken _ _ mem1 m3 _ MUr).
          intros x Ho. cbn [outside] in Ho |- *. destruct Ho as (H1 & _ & _ & _ & H5 & _).
          split; [exact H1|]. split; [exact H5 | exact I]. }
        split.
        { intros x Hx. pose proof (in_shadow_range x Hx) as Hxr.
          destruct (HSW1 x Hx) as (_ & b1 & Hb1). exists b1.
          assert (Ho : outside [(fs_hint FS 6, fs_hint FS 6 + 8); (A - 208, A)] x).
          { cbn [outside]. split; [intro Hh0; exact (Happ_ns x (Hhapp x Hh0) Hx)|].
            split; [intro Hw0; exact (Happ_ns x (Hwapp x Hw0) Hx) | exact I]. }
          pose proof (mbyte_munch rsegs _ mem1 m3 x MUr ltac:(lia) Ho) as E.
          change (mbyte rsegs m3 x = Some b1). rewrite E. exact Hb1. }
        split.
        { intros c jj Hc Hjj. pose proof (flag_bounds FS c jj Hc Hjj) as Hq.
          rewrite (mbyte_munch rsegs _ mem1 m3 (AC.a_fs_flag FS c jj) MUr ltac:(unfold FS_SIZE in *; lia)).
          - exact (Hflag1 c jj Hc Hjj).
          - cbn [outside]. rewrite Ehint6. split; [lia|]. split; [unfold FS_SIZE in *; lia | exact I]. }
        left; reflexivity.
      - (* frame j0 *)
        unfold asan_stack_malloc_frame in FR. cbv zeta in FR.
        rewrite (MState.unsigned_lit A) in FR by lia. rewrite HKsz in FR.
        replace (fs_B 6) with 4096 in FR by reflexivity.
        replace (Z.to_nat (fs_shadow_n 6 3136)) with 512%nat in FR by reflexivity.
        replace (fs_shadow_n 6 3136) with 512 in FR by reflexivity.
        destruct FR as (Ea0 & Hm64 & H4096 & Hflj & H24 & HBm8 & Hshz & Hadd & Hstkf & Happf & HFSle & Hfrhi &
                        HGTfr & Hfrsp & Hapart & MUf).
        apply MUrel in MUf.
        set (j0 := (bv_unsigned h + i0) mod fs_M 6) in *.
        assert (Hj0 : 0 <= j0 < 256) by (unfold j0; change (fs_M 6) with 256; apply Z.mod_pos_bound; lia).
        set (fr := fs_frame FS 6 j0) in *.
        destruct (fs6_layout FS j0) as (_ & Eflj & Efr).
        fold fr in Efr.
        destruct (fs6_shadow FS j0 ltac:(lia) HFSal ltac:(lia)) as (_ & Efr32 & Eshfr').
        destruct (fs6_shadow FS 0 ltac:(lia) HFSal ltac:(lia)) as (_ & _ & Esh0').
        destruct (fs6_shadow FS 256 ltac:(lia) HFSal ltac:(lia)) as (_ & _ & Esh256').
        fold fr in Efr32, Eshfr'.
        assert (Eshfr : shadow_addr fr = shadow_addr (fs_frame FS 6 0) + 512 * j0) by lia.
        assert (Eshfr256 : shadow_addr (fs_frame FS 6 256) = shadow_addr (fs_frame FS 6 0) + 131072) by lia.
        clear Esh0' Esh256' Eshfr'.
        exists fr. split; [exact Ea0|]. split; [unfold FS_SIZE in *; lia|].
        split.
        { refine (munch_weaken _ _ mem1 m3 _ MUf).
          intros x Ho. cbn [outside] in Ho |- *. destruct Ho as (H1 & H2 & H3 & H4 & H5 & _).
          split; [exact H1|].
          split; [intro Hin; apply H2; rewrite Eflag6; rewrite Eflj in Hin; lia|].
          split; [intro Hin; apply H3; rewrite Efr0, Efr256; rewrite Efr in Hin; lia|].
          split; [intro Hin; apply H3; rewrite Efr0, Efr256; rewrite Efr in Hin; lia|].
          split; [intro Hin; apply H4; rewrite Eshfr256; rewrite Eshfr in Hin; lia|].
          split; [exact H5 | exact I]. }
        split.
        { intros x Hx. pose proof (in_shadow_range x Hx) as Hxr.
          destruct (Z_lt_le_dec x (shadow_addr fr)) as [Lx|Lx];
            [|destruct (Z_lt_le_dec x (shadow_addr fr + 512)) as [Ux|Ux]].
          2:{ pose proof (proj2 (bytes_at_rel rsegs m3 m0' _ _ Erel) Hshz) as Hsh3.
              destruct Hsh3 as (_ & _ & Hb).
              specialize (Hb (Z.to_nat (x - shadow_addr fr)) ltac:(rewrite repeat_length; lia)).
              rewrite nth_error_repeat in Hb by lia.
              replace (shadow_addr fr + Z.of_nat (Z.to_nat (x - shadow_addr fr))) with x in Hb by lia.
              exists (Z_to_bv 8 0). exact Hb. }
          all: destruct (HSW1 x Hx) as (_ & b1 & Hb1); exists b1.
          all: assert (Ho : outside [(fs_hint FS 6, fs_hint FS 6 + 8); (fs_flag FS 6 j0, fs_flag FS 6 j0 + 1);
                                     (fr + 24, fr + 32); (fr + 4096 - 8, fr + 4096);
                                     (shadow_addr fr, shadow_addr fr + 512); (A - 208, A)] x)
            by (cbn [outside];
                split; [intro Hh0; exact (Happ_ns x (Hhapp x Hh0) Hx)|];
                split; [intro Hh0; apply (Happ_ns x); [rewrite Eflj in Hh0; replace x with (AC.a_fs_flag FS 6 j0)
                         by (unfold AC.a_fs_flag; cbn; lia); apply Hflapp; [lia | unfold AC.a_fs_M; cbn; lia] | exact Hx]|];
                split; [intro Hh0; exact (Happ_ns x (Happf x ltac:(lia)) Hx)|];
                split; [intro Hh0; exact (Happ_ns x (Happf x ltac:(lia)) Hx)|];
                split; [lia|];
                split; [intro Hw0; exact (Happ_ns x (Hwapp x Hw0) Hx) | exact I]).
          all: pose proof (mbyte_munch rsegs _ mem1 m3 x MUf ltac:(lia) Ho) as E.
          all: change (mbyte rsegs m3 x = Some b1); rewrite E; exact Hb1. }
        split.
        { intros c jj Hc Hjj. pose proof (flag_bounds FS c jj Hc Hjj) as Hq.
          pose proof (Hflapp c jj Hc Hjj) as Hqa.
          destruct (Z.eq_dec (AC.a_fs_flag FS c jj) (fs_flag FS 6 j0)) as [Eq|Nq].
          - right. pose proof (proj2 (bytes_at_rel rsegs m3 m0' _ _ Erel) Hflj) as Hflj3.
            destruct Hflj3 as (_ & _ & Hb). specialize (Hb 0%nat ltac:(cbn; lia)). cbn [nth_error] in Hb.
            rewrite Z.add_0_r in Hb. rewrite Eq. exact Hb.
          - rewrite (mbyte_munch rsegs _ mem1 m3 (AC.a_fs_flag FS c jj) MUf ltac:(unfold FS_SIZE in *; lia)).
            + exact (Hflag1 c jj Hc Hjj).
            + assert (Hshb : ASAN_K <= shadow_addr fr /\ shadow_addr fr + 512 <= 17594333495296) by lia.
              cbn [outside]. rewrite Ehint6.
              split; [lia|]. split; [lia|]. split; [rewrite Efr; lia|]. split; [rewrite Efr; lia|].
              split; [rs_hide_all; unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hqa; unfold ASAN_K in *; lia|].
              split; [unfold FS_SIZE in *; lia | exact I]. }
        right. split; [exact Efr32|].
        split; [rewrite Efr; lia|]. split; [unfold FS_SIZE in *; lia|]. split; [lia|].
        exists j0. split; [exact Hj0|]. split; [reflexivity|].
        split; [exact (proj2 (bytes_at_rel rsegs m3 m0' _ _ Erel) Hflj)|].
        exact (proj2 (bytes_at_rel rsegs m3 m0' _ _ Erel) HBm8). }
    destruct HU as (r & Ea0 & Hr & MUc & HSH3 & HFL3 & Hsel).
    assert (HFSr : 0 <= FS < 2 ^ 64) by (unfold FS_SIZE in *; lia).
    destruct (fs6_shadow FS 0 ltac:(lia) HFSal ltac:(lia)) as (EFS8 & _ & Esh0').
    destruct (fs6_shadow FS 256 ltac:(lia) HFSal ltac:(lia)) as (_ & _ & Esh256').
    assert (Esh0 : shadow_addr (fs_frame FS 6 0) = FS / 8 + 791040 + ASAN_K) by lia.
    assert (Esh256 : shadow_addr (fs_frame FS 6 256) = FS / 8 + 922112 + ASAN_K) by lia.
    clear Esh0' Esh256'.
    (* what the request's writes Wc miss *)
    assert (HWco : forall x, (x < FS \/ FS + FS_SIZE <= x) ->
              (x < shadow_addr (fs_frame FS 6 0) \/ shadow_addr (fs_frame FS 6 256) <= x) ->
              (x < A - 208 \/ A <= x) ->
              outside [(fs_hint FS 6, fs_hint FS 6 + 8); (fs_flag FS 6 0, fs_flag FS 6 0 + 256);
                       (fs_frame FS 6 0, fs_frame FS 6 256);
                       (shadow_addr (fs_frame FS 6 0), shadow_addr (fs_frame FS 6 256)); (A - 208, A)] x).
    { intros x H1 H2 H3. rs_hide_all. unfold rs_hold in H1, H2, H3. cbn [outside]. unfold FS_SIZE in H1.
      repeat split; try exact I; lia. }
    assert (HnotFS : forall x, in_shadow x -> x < FS \/ FS + FS_SIZE <= x).
    { intros x Hx. destruct (Z_lt_le_dec x FS) as [L|L]; [left; exact L|].
      destruct (Z_lt_le_dec x (FS + FS_SIZE)) as [U|U]; [|right; exact U].
      exfalso. exact (Happ_ns x (HFSapp x ltac:(unfold FS_SIZE in *; lia)) Hx). }
    assert (HnotW : forall x, in_shadow x -> x < A - 208 \/ A <= x).
    { intros x Hx. destruct (Z_lt_le_dec x (A - 208)) as [L|L]; [left; exact L|].
      destruct (Z_lt_le_dec x A) as [U|U]; [|right; exact U].
      exfalso. exact (Happ_ns x (Hwapp x ltac:(lia)) Hx). }
    assert (HnotW0 : forall x, in_shadow x -> outside [(S - 416, S)] x).
    { intros x Hx. cbn [outside]. split; [|exact I]. intro Hin.
      exact (Happ_ns x (HAPP0 x ltac:(unfold AF.SLOT_STACK; lia)) Hx). }
    (* the bytes below GT are those of the entry *)
    assert (Hlow : forall (sg : list Segment) x, 0 <= x -> x < 6283264 -> mbyte sg m3 x = mbyte sg (g_mem g) x).
    { intros sg x H0 H1.
      assert (E1 : m3 (Z_to_bv 64 x) = mem1 (Z_to_bv 64 x)).
      { apply MUc. rewrite MState.unsigned_lit by lia. apply HWco; lia. }
      assert (E0 : mem1 (Z_to_bv 64 x) = g_mem g (Z_to_bv 64 x)).
      { apply MU1. rewrite MState.unsigned_lit by lia. cbn [outside]. split; [lia | exact I]. }
      unfold mbyte. rewrite E1, E0. reflexivity. }
    (* a shadow byte of the image or of the slot window is the entry's *)
    assert (Hshkeep : forall a, 0 <= a -> (a < 6283264 \/ S - 1048576 <= a < S) ->
              m3 (wa (shadow_addr a)) = g_mem g (wa (shadow_addr a))).
    { intros a Ha0 Ha.
      assert (Hap : app_mem a).
      { destruct Ha as [Ha|Ha]; [unfold app_mem, LOWMEM_END; lia | apply HAPP0; unfold AF.SLOT_STACK; lia]. }
      pose proof (shadow_of_app a Hap) as Hsx.
      pose proof (in_shadow_range _ Hsx) as Hsr.
      assert (E1 : m3 (wa (shadow_addr a)) = mem1 (wa (shadow_addr a))).
      { apply MUc. rewrite wa_unsigned by lia. apply HWco; [exact (HnotFS _ Hsx) | | exact (HnotW _ Hsx)].
        destruct Ha as [Ha|Ha].
        - left. assert (a / 8 < 785408) by (apply Z.div_lt_upper_bound; lia). unfold shadow_addr. lia.
        - right. pose proof (shadow_le (S - 1048576) a ltac:(lia)). lia. }
      rewrite E1. apply MU1. rewrite wa_unsigned by lia. exact (HnotW0 _ Hsx). }
    (* a shadow byte of an app byte outside FS is the entry's (the input block's, for its addressability) *)
    assert (Hshkeep2 : forall a, app_mem a -> (a < FS \/ FS + FS_SIZE <= a) ->
              m3 (wa (shadow_addr a)) = g_mem g (wa (shadow_addr a))).
    { intros a Hap HaFS.
      assert (Ha0 : 0 <= a) by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hap; lia).
      pose proof (shadow_of_app a Hap) as Hsx.
      pose proof (in_shadow_range _ Hsx) as Hsr.
      assert (E1 : m3 (wa (shadow_addr a)) = mem1 (wa (shadow_addr a))).
      { apply MUc. rewrite wa_unsigned by lia. apply HWco; [exact (HnotFS _ Hsx) | | exact (HnotW _ Hsx)].
        destruct HaFS as [L|U].
        - left. rewrite Esh0. exact (shadow_below_fs a FS Ha0 L).
        - right. rewrite Esh256. apply shadow_above_fs; [exact EFS8 | lia | lia]. }
      rewrite E1. apply MU1. rewrite wa_unsigned by lia. exact (HnotW0 _ Hsx). }
    assert (HshUp : shadow_addr (fs_frame FS 6 256) <= 17594333495296) by lia.
    assert (HWco_meta : forall x, FS <= x < FS + 36352 -> ~ (FS + 48 <= x < FS + 56) ->
              outside [(fs_hint FS 6, fs_hint FS 6 + 8); (fs_flag FS 6 0, fs_flag FS 6 0 + 256);
                       (fs_frame FS 6 0, fs_frame FS 6 256);
                       (shadow_addr (fs_frame FS 6 0), shadow_addr (fs_frame FS 6 256)); (A - 208, A)] x).
    { intros x H1 H2. rs_hide_all. pose proof (HFSapp x ltac:(unfold FS_SIZE; lia)) as Hxa.
      unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hxa. unfold ASAN_K in *.
      cbn [outside]. repeat split; try exact I; unfold FS_SIZE in *; lia. }
    assert (Hok3 : AC.a_fs_ok m3 FS).
    { apply a1_fs_ok_of. split.
      { intros a Ha. destruct FSP3 as (_ & _ & _ & _ & (_ & _ & Hst)).
        destruct (Hst a ltac:(unfold AC.FS_SIZE, FS_SIZE in *; lia)) as (Hw & b & Hb).
        split; [exact Hw | exists b; exact Hb]. }
      split.
      { apply (kb_word_munch rsegs mem1 m3 _ (FS + 88) 20 H881 MUc). intros kk Hk.
        split; [unfold FS_SIZE in *; lia|]. apply HWco_meta; lia. }
      split.
      { rewrite (mbyte_munch rsegs _ mem1 m3 (FS + 96) MUc ltac:(unfold FS_SIZE in *; lia)
                   ltac:(apply HWco_meta; lia)). exact H961. }
      split.
      { intros c Hc. destruct (Nat.eq_dec c 6) as [->|Hc6].
        - exists (bv_unsigned h'). change (AC.a_fs_hint FS 6) with (fs_hint FS 6).
          exact (bytes_at_le8_word rsegs m3 _ h' Hh3).
        - destruct (Hhint1 c Hc) as (hv & Hhv). exists hv.
          apply (kb_word_munch rsegs mem1 m3 _ _ hv Hhv MUc). intros kk Hk.
          assert (Hc' : Z.of_nat c <= 10 /\ Z.of_nat c <> 6) by lia.
          unfold AC.a_fs_hint. split; [unfold FS_SIZE in *; lia|]. apply HWco_meta; lia. }
      exact HFL3. }
    assert (Hagree : forall a, 0 <= a < 2 ^ 64 ->
      ~ AC.a_store_ok (g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem1 (g_md g)) a ->
      ~ (FS <= a < FS + AC.FS_SIZE) -> ~ (exists b, FS <= b < FS + AC.FS_SIZE /\ a = shadow_addr b) ->
      m3 (Z_to_bv 64 a) = mem1 (Z_to_bv 64 a)).
    { intros a Ha Hns Hnf Hnsh. apply MUc. rewrite MState.unsigned_lit by lia.
      apply HWco.
      - unfold AC.FS_SIZE, FS_SIZE in *. lia.
      - destruct (Z_lt_le_dec a (shadow_addr (fs_frame FS 6 0))) as [L|L]; [left; exact L|].
        destruct (Z_lt_le_dec a (shadow_addr (fs_frame FS 6 256))) as [U|U]; [|right; exact U].
        exfalso. apply Hnsh. exists (8 * (a - ASAN_K)). split.
        + unfold AC.FS_SIZE. rewrite Esh0 in L. rewrite Esh256 in U.
          destruct (shadow_inv8 FS a EFS8 ltac:(lia)) as (X & _). lia.
        + unfold shadow_addr. replace (8 * (a - ASAN_K)) with ((a - ASAN_K) * 8) by lia.
          rewrite Z.div_mul by lia. lia.
      - destruct (Z_lt_le_dec a (A - 208)) as [L|L]; [left; exact L|].
        destruct (Z_lt_le_dec a A) as [U|U]; [|right; exact U].
        exfalso. apply Hns. unfold AC.a_store_ok. right; left. rewrite HstkloEq. unfold APPMEM_END. lia. }
    destruct (a1_fs_store (g_H g) mem1 m3 (g_md g) FS HAH1 HFSw HFSr Hagree
                (fun a _ Hw => WM3 (Z_to_bv 64 a) Hw) Hok3) as (HAH3 & HOWN3 & HSTK3 & HSTKhi3).
    (* ENT: from the entry, across the prologue stores, across the request *)
    assert (HENT0 : ENT APIf g [] (g_mem g) (g_md g)) by (eapply ent_entry; eassumption).
    assert (HENT1 : ENT APIf g [] mem1 (g_md g)).
    { apply (ent_munch APIf g [] (g_mem g) mem1 (g_md g) [(S - 416, S)] HENT0 HAH0 MU1).
      - intros x Hk. cbn [outside]. split; [|exact I]. intros [Hx1 Hx2].
        unfold ent_kept in Hk. rewrite <- Hasp in Hk.
        destruct Hk as [(q & kk & i & Hin & _ & Hi & ->) | [Himg | [Habv | [(b & Hb & ->) | (q & kk & i & Hin & _ & Hi & ->)]]]].
        + destruct (a1_blocks (g_H g) (g_mem g) (g_md g) q kk HAH0 Hin) as (Hqk & _). lia.
        + pose proof (img_below_GT x Himg) as X. unfold AC.GT in X. lia.
        + lia.
        + assert (Hb0 : 0 <= b < 140737488355328).
          { destruct Hb as [Hb|Hb]; [pose proof (img_below_GT b Hb) as X; unfold AC.GT in X; lia
                                    | unfold APPMEM_END in Hb; lia]. }
          pose proof (HshS b Hb0). lia.
        + (* the shadow byte of an entry block byte (frame batch 2): a shadow byte, below the stack *)
          destruct (a1_blocks (g_H g) (g_mem g) (g_md g) q kk HAH0 Hin) as (_ & Hall).
          destruct (Hall (q + i) ltac:(lia)) as (Hap & _ & _).
          unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hap.
          pose proof (HshS (q + i) ltac:(lia)). lia.
      - exact HSTK1.
      - exact HSTKhi1.
      - intros a Hia Ho. exact (proj2 (HOWN1 a) Ho). }
    assert (HENT3 : ENT APIf g [] m3 (g_md g)).
    { apply (ent_munch APIf g [] mem1 m3 (g_md g)
               [(fs_hint FS 6, fs_hint FS 6 + 8); (fs_flag FS 6 0, fs_flag FS 6 0 + 256);
                (fs_frame FS 6 0, fs_frame FS 6 256);
                (shadow_addr (fs_frame FS 6 0), shadow_addr (fs_frame FS 6 256)); (A - 208, A)]
               HENT1 HAH1 MUc).
      - intros x Hk. unfold ent_kept in Hk. rewrite <- Hasp in Hk.
        destruct Hk as [(q & kk & i & Hin & _ & Hi & ->) | [Himg | [Habv | [(b & Hb & ->) | (q & kk & i & Hin & _ & Hi & ->)]]]].
        + destruct (a1_blocks (g_H g) mem1 (g_md g) q kk HAH1 Hin) as (Hqk & Hall).
          destruct (Hall (q + i) ltac:(lia)) as (Hap & _ & Hnfs).
          rewrite HstkloEq in Hqk.
          apply HWco.
          * destruct (Z_lt_le_dec (q + i) FS) as [L|L]; [left; exact L|].
            destruct (Z_lt_le_dec (q + i) (FS + FS_SIZE)) as [U|U]; [|right; exact U].
            exfalso. apply Hnfs. exact (a_fs_in AC.ASYMS mem1 FS (q + i) HFSw HFSr ltac:(unfold AC.FS_SIZE, FS_SIZE in *; lia)).
          * unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hap. unfold ASAN_K in *. lia.
          * left. lia.
        + pose proof (img_below_GT x Himg) as X. unfold AC.GT in X. apply HWco; lia.
        + unfold APPMEM_END in Habv. apply HWco; lia.
        + assert (Hb0 : 0 <= b < 140737488355328).
          { destruct Hb as [Hb|Hb]; [pose proof (img_below_GT b Hb) as X; unfold AC.GT in X; lia
                                    | unfold APPMEM_END in Hb; lia]. }
          assert (Hbap : app_mem b).
          { destruct Hb as [Hb|Hb]; [pose proof (img_below_GT b Hb) as X; unfold AC.GT in X;
                                     unfold app_mem, LOWMEM_END; lia
                                    | unfold app_mem, HIGHMEM_BEG, APPMEM_END in *; lia]. }
          pose proof (shadow_of_app b Hbap) as Hsx.
          apply HWco; [exact (HnotFS _ Hsx) | | exact (HnotW _ Hsx)].
          destruct Hb as [Hb|Hb].
          * left. pose proof (img_below_GT b Hb) as X. unfold AC.GT in X.
            assert (b / 8 < 785408) by (apply Z.div_lt_upper_bound; lia). unfold shadow_addr. lia.
          * right. pose proof (shadow_le (S - 1048576) b ltac:(lia)). lia.
        + (* the shadow byte of an entry block byte (frame batch 2): the block byte is not in FS (a_laws_blocks), so
             its shadow byte is apart from the FS frames' shadow; a shadow byte is neither FS nor the stack window *)
          destruct (a1_blocks (g_H g) mem1 (g_md g) q kk HAH1 Hin) as (_ & Hall).
          destruct (Hall (q + i) ltac:(lia)) as (Hap & _ & Hnfs).
          pose proof (shadow_of_app (q + i) Hap) as Hsx.
          pose proof Hap as Hap'. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hap'.
          apply HWco; [exact (HnotFS _ Hsx) | | exact (HnotW _ Hsx)].
          destruct (Z_lt_le_dec (q + i) FS) as [L|L].
          * left. rewrite Esh0. exact (shadow_below_fs (q + i) FS ltac:(lia) L).
          * destruct (Z_lt_le_dec (q + i) (FS + FS_SIZE)) as [U|U].
            -- exfalso. apply Hnfs.
               exact (a_fs_in AC.ASYMS mem1 FS (q + i) HFSw HFSr ltac:(unfold AC.FS_SIZE, FS_SIZE in *; lia)).
            -- right. rewrite Esh256. apply shadow_above_fs; [exact EFS8 | lia | unfold FS_SIZE in U; lia].
      - exact HSTK3.
      - exact HSTKhi3.
      - intros a Hia Ho. exact (proj2 (HOWN3 a) Ho). }
    assert (ER2 : getr R 2 = Z_to_bv 64 A) by reflexivity.
    exists r.
    split.
    { unfold PREF. rewrite <- Hasp.
      split.
      { apply (AsanRTInv.RT_meta_write S A mem1 m3 (g_md g) (g_md g) _ HRT1 MUc WM3); [|exact HSH3].
        unfold rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
          RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB,
          RT_AGLOB_LEN. cbn [disjoint_from]. unfold ASAN_K in *. repeat split; try (left; lia). }
      split; [exact HAH3|].
      split; [exact (ro_agree_same rsegs mem1 m3 Hro1 Hsame)|].
      split.
      { pose proof FF as (_ & _ & _ & _ & Hhead & Hlock & Hthr & _).
        destruct Hsn0 as (Hcse & Hohd & Hfd0). split; [|split; [|exact Hfd0]].
        - destruct Hcse as (Hthrm & Hlockm). split.
          + eapply YI14.val_mem_frame; [|exact Hthrm]. intros x Hx. apply Hlow; [lia | rewrite Hthr in Hx; cbn in Hx; lia].
          + eapply YI14.val_mem_frame; [|exact Hlockm]. intros x Hx. apply Hlow; [lia | rewrite Hlock in Hx; cbn in Hx; lia].
        - intros kk Hk. rewrite Hlow; [exact (Hohd kk Hk) | rewrite Hhead; lia | rewrite Hhead; lia]. }
      split; [exact Hhalt0|].
      split.
      { intros a Hin. rewrite Hlow.
        - exact (Hgimg a Hin).
        - destruct Hin as (lo & len & Hil & Hr0). pose proof (relro_blk_below lo len Hil). lia.
        - destruct Hin as (lo & len & Hil & Hr0). pose proof (relro_blk_below lo len Hil). lia. }
      split; [exact ER2|].
      split; [unfold A; exact (proj2 (proj2 (Aof_bounds S Hal)))|].
      split; [unfold AC.aspZ; rewrite ER2; apply MState.unsigned_lit; lia|].
      split; [rewrite HSTK3, HstkloEq; unfold AF.SLOT_STACK; lia|].
      split; [exact Htp|].
      split; [unfold rg; reflexivity|].
      split; [unfold rg; reflexivity|].
      split; [reflexivity|].
      split; [unfold rg; reflexivity|].
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; [unfold APPMEM_END; lia|].
      split.
      { unfold AF.SLOT_STACK. apply (stk_merge rsegs m3 (S - 1048576) A S ST3); [|lia].
        destruct (stk_split rsegs mem1 (S - 1048576) A S ST1 ltac:(lia)) as (_ & SThi).
        apply (stk_transport_disjoint rsegs _ mem1 m3 A S SThi MUc WM3).
        cbn [disjoint_from]. unfold FS_SIZE in *. repeat split; try (right; lia). }
      split.
      { unfold saved_bytes. rewrite <- Hra.
        apply (bytes_at_transport rsegs _ mem1 m3 (S - 104) _ SAV1 MUc).
        rewrite ?length_app, ?length_le8. cbn [disjoint_from Z.of_nat Nat.add Pos.of_succ_nat Pos.succ].
        unfold FS_SIZE in *. repeat split; try (right; lia). }
      split.
      { intros a Ha. pose proof (Herrno0 a Ha) as Hwe. rewrite SEGS in Hwe.
        exact (WM3 (Z_to_bv 64 a) (WM1 (Z_to_bv 64 a) Hwe)). }
      split.
      { intros a Ha. pose proof (frame_AG_low a Ha) as HAGl. pose proof (HAGe a Ha) as Had.
        apply (addressable1_keep (g_mem g) m3 a Had).
        destruct Had as (Ha0 & _). exact (Hshkeep a Ha0 (or_introl HAGl)). }
      split.
      { intros a Ha.
        destruct (Hwin a ltac:(unfold AC.a_window; unfold S in *; lia))
          as (_ & Had & _).
        apply (addressable1_keep (g_mem g) m3 a Had).
        apply (Hshkeep a); [unfold AF.SLOT_STACK in *; lia | right; unfold AF.SLOT_STACK in *; lia]. }
      split; [exact Hshi|].
      split; [exact Hshia|].
      split; [exact Hpres|].
      split; [exact Hnmax | exact Hlvb]. }
    split; [exact HENT3|].
    split; [unfold rg; exact Ea0|].
    split; [exact Hr|].
    split; [unfold rg; exact Hp|].
    split; [unfold rg; exact Hn|].
    split.
    { destruct Hsel as [-> | (Hr32 & Hr36 & Hr4096 & HrFS & (j & Hj & Erj & Hflj3 & Hlast3))];
        [left; reflexivity | right].
      assert (Hw3 : word_mem rsegs m3 (AC.as_tp AC.ASYMS) FS).
      { apply (kb_word_munch rsegs mem1 m3 _ _ FS HFSw MUc). intros kk Hk.
        replace (AC.as_tp AC.ASYMS) with RT_TP by reflexivity. unfold RT_TP.
        split; [lia|]. apply HWco; unfold ASAN_K in *; lia. }
      split; [exact Hr32|].
      split.
      { intros FS' HwFS' HFSr'. rewrite (word_mem_unique m3 _ FS' FS HwFS' Hw3 HFSr' HFSr). exact Hr36. }
      split.
      { intros a Ha. exists FS. split; [exact HFSr|]. split; [exact Hw3|]. unfold AC.FS_SIZE. unfold FS_SIZE in *. lia. }
      exists FS, j. split; [exact Hw3|]. split; [exact HFSr|]. split; [change (SMC.fs_M 6) with 256; lia|].
      split; [exact Erj|]. split; [exact Hflj3|].
      change (SMC.fs_B 6) with 4096. exact Hlast3. }
    (* the input facts: the input block is an entry block the target does not keep (ENT), and its shadow is
       outside every write of the prologue and the request *)
    apply (a1_input g m3 Hpre HT2).
    { pose proof HENT3 as (_ & _ & _ & _ & _ & _ & _ & _ & Hblk3 & _). exact Hblk3. }
    intros Hn0 i Hi.
    destruct Hbuf as [(Hz & _) | (_ & Hin & _)]; [lia|].
    destruct (a1_blocks (g_H g) mem1 (g_md g) _ _ HAH1 Hin) as (_ & Hall).
    destruct (Hall (g_p g + i) ltac:(lia)) as (Hap & _ & Hnfs).
    apply (Hshkeep2 (g_p g + i) Hap).
    destruct (Z_lt_le_dec (g_p g + i) FS) as [L|L]; [left; exact L|].
    destruct (Z_lt_le_dec (g_p g + i) (FS + FS_SIZE)) as [U|U]; [|right; exact U].
    exfalso. apply Hnfs.
    exact (a_fs_in AC.ASYMS mem1 FS (g_p g + i) HFSw HFSr ltac:(unfold AC.FS_SIZE, FS_SIZE in *; lia)).
  - intros R pc' mem' regs' md' (Hpc & r & HP & HE & H10 & Hr & H23 & H24 & Hsel & Hin1 & Hin2) Hreg Hmat.
    subst pc'. rewrite <- SEGS. apply Hexit.
    exists regs', mem', md', A, r.
    split; [reflexivity|].
    split; [apply (pref_move g A A R regs' mem' (g_md g) md' HP); first [rewrite Hreg; reflexivity | exact Hmat]|].
    split; [exact (ent_mat APIf g [] mem' (g_md g) md' HE Hmat)|].
    split; [unfold rg in *; rewrite Hreg; exact H10|].
    split; [exact Hr|].
    split; [unfold rg in *; rewrite Hreg; exact H23|].
    split; [unfold rg in *; rewrite Hreg; exact H24|].
    split; [exact Hsel|].
    split; [exact Hin1 | exact Hin2].
Qed.
End EntryClassA1.

End T.
