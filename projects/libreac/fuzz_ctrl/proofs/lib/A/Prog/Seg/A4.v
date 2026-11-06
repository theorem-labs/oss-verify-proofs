(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3060 of its 3101 lines of code are new or changed and 207 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/reac_box_catalogue_match.v, with its module paths, module names, addresses and numbers changed; 2488 of its 3291 lines of code are new or changed and 2298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/reac_box_catalogue_match.v, with its module paths and module names changed; 2419 of its 2557 lines of code are new or changed and 3153 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/Tac_slot.v, with its module paths changed; 842 of its 961 lines of code are new or changed and 2438 lines of the source are left out. *)
(* Segment A4 of fuzz_ctrl LLVMFuzzerTestOneInput (asan, image A, libreac v1.9.0): 0x810e4-0x813fc,
   Inv_A810e4 -> Inv_A81400_at turn 0 (n < 2^26) | Inv_Jrel (n >= 2^26, the early edge 0x81314).  rule 24: no
   function proved (a slot segment).
   a4_evt is the UL-engine run of the 198 instructions: the 137 tail shadow stores S(fr)+255 .. S(fr)+391 of FP.4,
   the n test of FP.5 (`srli a1,s8,26` / `beqz a1`) and, on the fall-through, the A-spill block 0x81318-0x813fc
   (the selector at [A+24] and fr at [A+16], the record pointers s5 = fr + 2176 (0x81388), t3 .. t6 / ra
   (0x81390 .. 0x813a0), s2 = fr + 2656, s11 = fr + 2688, a4 = fr + 2624, the spills [A+144] / [A+152] / [A+168] /
   [A+192] / [A+200] / [A+216] / [A+240] / [A+280], PRO's frame-pointer spills [A+40] / [A+120] / [A+136] /
   [A+160] / [A+176] / [A+208] / [A+248] and [A+184] / [A+256] / [A+264] / [A+272], PRO's v1.9 spill
   [A+32] = fr + 2880 = &first.sroa.7 (0x813c8 / 0x813cc), a2 = 6, a3 = 7, and the our[] shadow byte
   S(fr)+328 = 6 (0x8138c)).  a4_fras moves the frame invariant (FRAS) and the entry relation (ENT) across the
   run's write set [S(fr)+255, S(fr)+392) u [A+16, A+288) (AH by a_laws_store on the real arm, a_fs_ok_store_AH on
   the side arm; ENT by ent_munch); seg_A4 rebuilds FRA at 0x81400 with FRA_of_FRAS and reads every other conjunct
   of Inv_A81400_at at t = 0 off the run: PRO from the thirteen spills, our[]'s six bytes addressable by the shadow
   byte 6 (a4_our_addr) and the input facts; the frame records at fr + 2688 / 2768 / 3040 / 3056 and our[] are
   frame bytes the run does not write (readable and writable on both arms), and the input block is a live heap
   block below stklo, so neither its bytes nor its shadow are in the write set.
   v1.9 re-walk (table of record S_A4 (v190-segment-table.md (a working note, not in this delivery)), CHANGED code / register;
   section 7a slot moves): the poison stores swap s2 (0xf8) and s4 (0xf2) at several shadow bytes and gain the
   twelve stores of S(fr)+380 .. S(fr)+391 (the frame grew to FRAME_BYTES = 3136 / FRAME_SHADOW = 392); the spill
   moves [A+32] -> [A+24] (selector), [A+24] -> [A+16] (fr), [A+200] -> [A+208] (fr + 448), [A+192] -> [A+200]
   (decl_slot fr = fr + 2560), [A+208] -> [A+192] (fr + 2768); the frame offsets of code / blk move +80 (fr + 3040
   / fr + 3056 at [A+280] / [A+240]); the new [A+32] = fr + 2880 is PRO's last conjunct. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Cells Step.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL Require Import Exec Step Tac Cells.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.AW Require Import SmLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_fs.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
Module LMem := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
(* The cell vocabulary of the cut texts (SlotInv.v imports lib/Lib's Cells / Step / Frame; the UL engine brings
   its own copies, which the run below uses). *)
Module LibC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.
Module LibS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.
Module LibF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.

(* The engine's norm_lit_store_bytes normalizes a 1-byte store of a literal with `change`, which needs the
   conversion le1 (Z_to_bv 64 z) == [Z_to_bv 8 z]; prove it as a rewrite instead. *)
Lemma le1_lit : forall z : Z, le1 (Z_to_bv 64 z) = [Z_to_bv 8 z].
Proof.
  intros z. unfold le1. rewrite Z_to_bv_unsigned.
  change (bv_wrap 64 z) with (z mod 2 ^ 64)%Z.
  rewrite (Z_to_le_bytes_mod 1 z 64 ltac:(cbn; lia)). reflexivity.
Qed.

#[local] Ltac norm_lit_store_bytes ::=
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) => rewrite (le1_lit z)
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
           is_Zlit z; change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z))
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (zxb ?b))) _) => rewrite (le1_zxb b)
       end).

(* The n test at 0x812e8-0x81310: a1 = n >> 26, beqz a1. *)
Lemma srli26_t : forall N, 0 <= N < 2 ^ 26 ->
  bv_eqb (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 N)) 26)) (Z_to_bv 64 0) = true.
Proof.
  intros N H. rewrite MState.unsigned_lit by lia. rewrite Z.shiftr_div_pow2 by lia.
  rewrite Z.div_small by lia. apply bv_eqb_refl.
Qed.

Lemma srli26_f : forall N, 2 ^ 26 <= N < 2 ^ 64 ->
  bv_eqb (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 N)) 26)) (Z_to_bv 64 0) = false.
Proof.
  intros N H. rewrite MState.unsigned_lit by lia. rewrite Z.shiftr_div_pow2 by lia.
  assert (Hpos : 0 < N / 2 ^ 26) by (apply Z.div_str_pos; lia).
  assert (Hle : N / 2 ^ 26 <= N) by (apply Z.div_le_upper_bound; [lia | nia]).
  rewrite bv_eqb_lit by lia. apply Z.eqb_neq. lia.
Qed.

(* a1 after the test, on the fall-through: n >> 26 = 0. *)
Lemma srli26_0 : forall N, 0 <= N < 2 ^ 26 ->
  Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 N)) 26) = Z_to_bv 64 0.
Proof.
  intros N H. rewrite MState.unsigned_lit by lia. rewrite Z.shiftr_div_pow2 by lia.
  rewrite Z.div_small by lia. reflexivity.
Qed.

(* A cell of a cells_at block, as bytes. *)
Lemma cells_bytes_at : forall m A cs k c, cells_at rsegs m A cs -> cell_at cs k = Some c ->
  bytes_at rsegs m (A + Z.of_nat k) (cbytes c).
Proof.
  intros m A cs k c [Hwf Hb] Hk.
  destruct (cell_at_split cs k c c Hk) as (pre & post & Ecs & Hsz & _).
  subst cs. apply cells_wf_app in Hwf. destruct Hwf as [Hpre _].
  rewrite cells_bytes_app in Hb. cbn [cells_bytes] in Hb.
  apply (proj1 (bytes_at_app rsegs m A _ _)) in Hb. destruct Hb as [_ Hb].
  apply (proj1 (bytes_at_app rsegs m _ _ _)) in Hb. destruct Hb as [Hb _].
  rewrite (cells_bytes_length pre Hpre), Hsz in Hb. exact Hb.
Qed.

(* A word cell holding Z_to_bv 64 v is the spill fact q64 of the cut texts. *)
Lemma cell8_q64 : forall m A cs k w v, cells_at rsegs m A cs -> cell_at cs k = Some (C8 w) ->
  w = Z_to_bv 64 v -> q64 m (A + Z.of_nat k) v.
Proof.
  intros m A cs k w v H Hk ->. unfold q64.
  exact (cells_bytes_at m A cs k (C8 (Z_to_bv 64 v)) H Hk).
Qed.

(* A byte cell holding Z_to_bv 8 v is the b8 fact of the cut texts. *)
Lemma cell1_b8 : forall m A cs k b v, cells_at rsegs m A cs -> cell_at cs k = Some (C1 b) ->
  b = Z_to_bv 8 v -> b8 m (A + Z.of_nat k) v.
Proof.
  intros m A cs k b v H Hk ->. unfold b8.
  exact (cells_bytes_at m A cs k (C1 (Z_to_bv 8 v)) H Hk).
Qed.

(* What the fall-through of the run sets (0x81318-0x813fc), on the register file R and the memory m at 0x81400:
   fr = s6, S3 = s3 = S(fr), A = s1, s5v the selector, s7 / s8 the input cursor and size (untouched). *)
Definition a4_exit (fr S3 A s5v : Z) (s7 s8 : word) (R : bvmap 5 word) (m : word -> option byte) : Prop :=
  getr R 1 = Z_to_bv 64 (fr + 2496) /\ getr R 7 = Z_to_bv 64 (fr + 544) /\ getr R 11 = Z_to_bv 64 0 /\
  getr R 12 = Z_to_bv 64 6 /\ getr R 13 = Z_to_bv 64 7 /\ getr R 14 = Z_to_bv 64 (fr + 2624) /\
  getr R 18 = Z_to_bv 64 (fr + 2656) /\ getr R 21 = Z_to_bv 64 (fr + 2176) /\
  getr R 23 = s7 /\ getr R 24 = s8 /\ getr R 27 = Z_to_bv 64 (fr + 2688) /\
  getr R 28 = Z_to_bv 64 (fr + 2256) /\ getr R 29 = Z_to_bv 64 (fr + 2368) /\
  getr R 30 = Z_to_bv 64 (fr + 2448) /\ getr R 31 = Z_to_bv 64 (fr + 2464) /\
  b8 m (S3 + 328) 6 /\
  q64 m (A + 16) fr /\ q64 m (A + 24) s5v /\ q64 m (A + 144) (fr + 2688) /\ q64 m (A + 152) (S3 + 68) /\
  q64 m (A + 168) (fr + 2624) /\ q64 m (A + 200) (fr + 2560) /\ q64 m (A + 192) (fr + 2768) /\
  q64 m (A + 216) (fr + 2528) /\ q64 m (A + 240) (fr + 3056) /\ q64 m (A + 280) (fr + 3040) /\
  q64 m (A + 40) (fr + 32) /\ q64 m (A + 120) (fr + 160) /\ q64 m (A + 136) (fr + 128) /\
  q64 m (A + 160) (fr + 528) /\ q64 m (A + 176) (fr + 64) /\ q64 m (A + 208) (fr + 448) /\
  q64 m (A + 248) (fr + 176) /\
  q64 m (A + 184) (fr + 336) /\ q64 m (A + 256) (fr + 256) /\ q64 m (A + 264) (fr + 304) /\
  q64 m (A + 272) (fr + 272) /\
  q64 m (A + 32) (fr + 2880).

(* A spill [A + o] of the run, from the spill block's cells at A + 16. *)
Ltac a4_q64 :=
  lazymatch goal with
  | H : rw_cells rsegs ?mm (?A + 16) ?cs |- q64 _ (?A + ?o) _ =>
      let k := eval vm_compute in (Z.to_nat (o - 16)) in
      replace (A + o) with (A + 16 + Z.of_nat k) by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia);
      eapply (cell8_q64 mm (A + 16) cs k);
      [ exact (proj1 H) | cells_cbv; reflexivity | first [reflexivity | f_equal; lia] ]
  end.

(* The our[] shadow byte S(fr) + 328, from the shadow block's cells at S(fr) + 255. *)
Ltac a4_b8 :=
  lazymatch goal with
  | H : rw_cells rsegs ?mm (?S3 + 255) ?cs |- b8 _ (?S3 + 328) _ =>
      replace (S3 + 328) with (S3 + 255 + Z.of_nat 73) by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia);
      eapply (cell1_b8 mm (S3 + 255) cs 73);
      [ exact (proj1 H) | cells_cbv; reflexivity | first [reflexivity | vm_compute; reflexivity] ]
  end.

Ltac a4_fin :=
  first
    [ simp_regs; first [ reflexivity | f_equal; lia | apply srli26_0; lia ]
    | a4_q64
    | a4_b8 ].

Lemma a4_evt :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A S3 N fr s5v lo hi : Z) (jsh jsp : list byte),
    s1 = Z_to_bv 64 A -> s2 = Z_to_bv 64 (-8) -> s3 = Z_to_bv 64 S3 -> s4 = Z_to_bv 64 (-14) ->
    s5 = Z_to_bv 64 s5v -> s6 = Z_to_bv 64 fr -> s8 = Z_to_bv 64 N -> s9 = Z_to_bv 64 (S3 + 68) ->
    0 <= N < 2 ^ 64 -> 0 <= S3 -> S3 + 392 <= A -> A + 288 <= 2 ^ 64 ->
    rw_cells rsegs m (S3 + 255) [CB 137 jsh] ->
    rw_cells rsegs m (A + 16) [CB 272 jsp] ->
    stk rsegs m lo hi -> stk rsegs m (S3 + 255) (S3 + 392) ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (pc' : word) (m' : word -> option byte),
         ms' = MS R F pc' fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 22 = s6 /\ getr R 26 = s10 /\
         munch [(S3 + 255, S3 + 392); (A + 16, A + 288)] m m' /\ wmono rsegs m m' /\
         stk rsegs m' lo hi /\ stk rsegs m' (S3 + 255) (S3 + 392) /\
         (exists sh, bytes_at rsegs m' (S3 + 255) sh /\ length sh = 137%nat) /\
         ((N < 2 ^ 26 /\ pc' = Z_to_bv 64 0x81400 /\ a4_exit fr S3 A s5v s7 s8 R m') \/
          (2 ^ 26 <= N /\ pc' = Z_to_bv 64 0x82b80 /\ getr R 21 = s5)))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x810e4) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A S3 N fr s5v lo hi jsh jsp -> -> -> -> -> -> -> -> HN HS3 HSA HA RWsh RWsp ST1 ST2.
  pose proof (munch_refl [(S3 + 255, S3 + 392); (A + 16, A + 288)] m) as MU.
  assert (WM : wmono rsegs m m) by (intros x Hx; exact Hx).
  (* 0x810e4 .. 0x8130c (139 instructions) and the beqz at 0x81310 *)
  do 140 step.
  destruct (Z_lt_ge_dec N (2 ^ 26)) as [Hlt|Hge].
  - if_true_by (srli26_t N ltac:(lia)).
    (* 0x81318 .. 0x813fc *)
    do 58 step.
    apply evt_done. do 3 eexists. split; [reflexivity|].
    split; [simp_regs; reflexivity|]. split; [simp_regs; reflexivity|].
    split; [simp_regs; reflexivity|]. split; [simp_regs; reflexivity|].
    split; [simp_regs; reflexivity|]. split; [simp_regs; reflexivity|].
    split; [simp_regs; reflexivity|]. split; [simp_regs; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact ST1|]. split; [exact ST2|].
    split.
    { match goal with
      | H : rw_cells rsegs ?mm (S3 + 255) ?cs |- _ =>
          exists (cells_bytes cs); pose proof H as HH; destruct HH as [[Hwf Hb] _]; split;
            [exact Hb | rewrite (cells_bytes_length cs Hwf); cbn [cells_size csize Nat.add]; reflexivity]
      end. }
    left. split; [lia|]. split; [reflexivity|].
    unfold a4_exit.
    do 37 (split; [a4_fin|]). a4_fin.
  - if_false_by (srli26_f N ltac:(lia)).
    step.
    apply evt_done. do 3 eexists. split; [reflexivity|].
    split; [simp_regs; reflexivity|]. split; [simp_regs; reflexivity|].
    split; [simp_regs; reflexivity|]. split; [simp_regs; reflexivity|].
    split; [simp_regs; reflexivity|]. split; [simp_regs; reflexivity|].
    split; [simp_regs; reflexivity|]. split; [simp_regs; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact ST1|]. split; [exact ST2|].
    split.
    { match goal with
      | H : rw_cells rsegs ?mm (S3 + 255) ?cs |- _ =>
          exists (cells_bytes cs); pose proof H as HH; destruct HH as [[Hwf Hb] _]; split;
            [exact Hb | rewrite (cells_bytes_length cs Hwf); cbn [cells_size csize Nat.add]; reflexivity]
      end. }
    right. split; [lia|]. split; [reflexivity|].
    simp_regs; reflexivity.
Qed.

(* Every byte of the image lies below LOWMEM_END, so no read-only byte is in the frame or its shadow. *)
Definition tops_below (sg : list Segment) (top : Z) : bool :=
  forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? top) sg.

Lemma find_seg_below : forall (sg : list Segment) top x n s,
  tops_below sg top = true -> find_segment sg x n = Some s -> 0 <= n -> x < top \/ n = 0.
Proof.
  induction sg as [|s0 r IH]; intros top x n s Hb H Hn; cbn in H; [discriminate H|].
  unfold tops_below in Hb. cbn [forallb] in Hb. apply andb_prop in Hb as [H0 Hr].
  apply Z.leb_le in H0.
  destruct (Z.leb (Z.of_N (seg_base s0)) x && Z.leb (x + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0))) eqn:E.
  - apply andb_prop in E as [_ E]. apply Z.leb_le in E. lia.
  - exact (IH top x n s Hr H Hn).
Qed.

Lemma ro_low : forall a, LMem.ro_addr rsegs a = true -> bv_unsigned a < LOWMEM_END.
Proof.
  intros a H. unfold LMem.ro_addr in H.
  destruct (find_segment rsegs (bv_unsigned a) 1) as [s|] eqn:E; [|discriminate H].
  destruct (find_seg_below rsegs LOWMEM_END (bv_unsigned a) 1 s ltac:(vm_compute; reflexivity) E ltac:(lia))
    as [L|L]; [exact L | discriminate L].
Qed.

Lemma ro_agree_keep : forall (W : list ivl) m m',
  ro_agree rsegs m -> munch W m m' ->
  (forall x, 0 <= x < LOWMEM_END -> outside W x) ->
  ro_agree rsegs m'.
Proof.
  intros W m m' Hro MU Hout. apply (ro_agree_same rsegs m m' Hro).
  intros a Hr. apply MU. apply Hout.
  pose proof (ro_low a Hr) as Hb. pose proof (bv_unsigned_in_range 64 a) as Hr64.
  unfold bv_modulus in Hr64. lia.
Qed.

Lemma mbyte_keep_low : forall (W : list ivl) m m' (sg : list Segment) x,
  munch W m m' -> (forall y, 0 <= y < LOWMEM_END -> outside W y) -> 0 <= x < LOWMEM_END ->
  mbyte sg m' x = mbyte sg m x.
Proof.
  intros W m m' sg x MU Hout Hx.
  assert (Hm : m' (Z_to_bv 64 x) = m (Z_to_bv 64 x)).
  { apply MU. rewrite MState.unsigned_lit by (unfold LOWMEM_END in Hx; lia). apply Hout; exact Hx. }
  unfold mbyte. rewrite Hm. reflexivity.
Qed.

Lemma stk_shadow : forall m x n, shadow_rw m -> 0 < n ->
  (forall i, 0 <= i < n -> in_shadow (x + i)) -> stk rsegs m x (x + n).
Proof.
  intros m x n HS Hn Hin.
  pose proof (in_shadow_range (x + 0) (Hin 0 ltac:(lia))) as H0.
  pose proof (in_shadow_range (x + (n - 1)) (Hin (n - 1) ltac:(lia))) as H1.
  split; [lia|]. split; [lia|].
  intros a Ha.
  assert (Hi : in_shadow a) by (replace a with (x + (a - x)) by lia; apply Hin; lia).
  exact (HS a Hi).
Qed.

(* A word cell pins its value: two readings of the word at a agree. *)
Lemma word_mem_uniq : forall m a v w, word_mem rsegs m a v -> word_mem rsegs m a w ->
  0 <= v < 2 ^ 64 -> 0 <= w < 2 ^ 64 -> 0 <= a -> a + 8 <= 2 ^ 64 -> v = w.
Proof.
  intros m a v w Hv Hw Hvr Hwr Ha0 Ha8.
  pose proof (word_mem_le8 rsegs m a v Hv Hvr Ha0 Ha8) as Bv.
  pose proof (word_mem_le8 rsegs m a w Hw Hwr Ha0 Ha8) as Bw.
  assert (E : LMem.le8 (Z_to_bv 64 v) = LMem.le8 (Z_to_bv 64 w)).
  { eapply (fl_bytes_eq [] m m a _ _ Bv Bw (munch_refl [] m));
      [rewrite !LMem.length_le8; reflexivity | intros x _; exact I]. }
  apply (f_equal le_bytes_to_word) in E. rewrite !LMem.le_bytes_to_word_le8 in E.
  apply (f_equal bv_unsigned) in E. rewrite !MState.unsigned_lit in E by lia. exact E.
Qed.

(* Every FakeStack metadata cell lies in [FS, FS + 36864). *)
Lemma fs_meta_in : forall FS q, fs_meta FS q -> FS <= q < FS + 36864.
Proof.
  intros FS q H. pose proof (fs_meta_below FS q H) as Hhi. split; [|exact Hhi].
  unfold fs_meta in H. destruct H as [H | [H | [ (c & Hc & Hr) | (c & j & Hc & Hj & Heq) ]]].
  - lia.
  - lia.
  - unfold AC.a_fs_hint in Hr. assert (0 <= Z.of_nat c) by lia. lia.
  - subst q. exact (proj1 (a_fs_flag_range FS c j Hc Hj)).
Qed.

(* The bound on the registered globals of frame_AG: every one is an image address below GT. *)
Lemma in_globals_below : forall (G : list (Z * Z)) top a,
  forallb (fun p => fst p + snd p <=? top) G = true -> in_globals G a -> a < top.
Proof.
  intros G top a Hf (lo & len & Hin & Hlo & Hhi).
  rewrite forallb_forall in Hf. pose proof (Hf (lo, len) Hin) as E. cbn in E.
  apply Z.leb_le in E. lia.
Qed.

Lemma frame_AG_below : forall a, in_globals AF.frame_AG a -> a < AC.GT.
Proof.
  intros a H. apply (in_globals_below AF.frame_AG AC.GT a ltac:(vm_compute; reflexivity) H).
Qed.

(* frame_RELRO's ranges lie in [0, GT), read off the list by computation, so the bound holds whatever the number of
   its ranges (FrameAPI frame batch 2 has one GNU_RELRO range, v1.8 had three). *)
Lemma frame_RELRO_lo : forall a, in_globals AF.frame_RELRO a -> 0 <= a < AC.GT.
Proof.
  intros a (lo & len & Hin & Ha).
  assert (HB : forallb (fun p => (0 <=? fst p) && (fst p + snd p <=? AC.GT)) AF.frame_RELRO = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in HB. specialize (HB (lo, len) Hin). cbn [fst snd] in HB.
  apply andb_prop in HB as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

(* A byte of a bytes_at block is present. *)
Lemma bytes_present : forall m a bs x, bytes_at rsegs m a bs -> a <= x < a + Z.of_nat (length bs) ->
  exists b, mrd rsegs m (wa x) = Some b.
Proof.
  intros m a bs x (H0 & H1 & H) Hx.
  assert (Hk : (Z.to_nat (x - a) < length bs)%nat) by lia.
  pose proof (H (Z.to_nat (x - a)) Hk) as E.
  replace (a + Z.of_nat (Z.to_nat (x - a))) with x in E by lia.
  destruct (nth_error bs (Z.to_nat (x - a))) as [b|] eqn:En; [exists b; rewrite E; reflexivity|].
  exfalso. apply nth_error_None in En. lia.
Qed.

Lemma mrd_keep : forall (W : list ivl) m m' a b,
  munch W m m' -> outside W a -> 0 <= a < 2 ^ 64 -> mrd rsegs m (wa a) = Some b ->
  mrd rsegs m' (wa a) = Some b.
Proof.
  intros W m m' a b MU Ho Ha H. unfold mrd, wa in *.
  rewrite (MU (Z_to_bv 64 a) ltac:(rewrite MState.unsigned_lit by lia; exact Ho)). exact H.
Qed.

(* A shadow byte of the frame's 392 is the shadow byte of a frame byte (fr mod 8 = 0). *)
Lemma sh_in_frame : forall fr y, fr mod 8 = 0 -> 0 <= fr -> 0 <= y ->
  Sfr fr <= shadow_addr y < Sfr fr + 392 -> fr <= y < fr + 3136.
Proof. intros fr y H8 H0 Hy H. unfold Sfr, shadow_addr in H. Z.div_mod_to_equations. lia. Qed.

(* A readable and writable window of n bytes is a single CB cell block of the cut texts' vocabulary. *)
Lemma lib_rw_stk : forall m lo (n : nat), LibF.stk rsegs m lo (lo + Z.of_nat n) ->
  exists bs, LibS.rw_cells rsegs m lo [LibC.CB n bs].
Proof.
  intros m lo n Hs.
  destruct (LibF.stk_bytes rsegs m lo (lo + Z.of_nat n) Hs ltac:(lia)) as (bs & Hl & Hb).
  exists bs. split; [split|].
  - cbn [LibC.cells_wf LibC.cell_wf]. split; [lia | exact I].
  - cbn [LibC.cells_bytes LibC.cbytes]. rewrite app_nil_r. exact Hb.
  - cbn [LibC.cells_size LibC.csize]. rewrite Nat.add_0_r.
    destruct Hs as (H0 & H1 & H). split; [lia|]. split; [lia|].
    intros i Hi. exact (proj1 (H (lo + i) ltac:(lia))).
Qed.

(* The empty byte list sits at any address in range. *)
Lemma bytes_at_nil : forall m a, 0 <= a <= 2 ^ 64 -> LMem.bytes_at rsegs m a [].
Proof.
  intros m a H. split; [lia|]. split; [change (Z.of_nat (length (@nil byte))) with 0; lia|].
  intros i Hi. cbn [length] in Hi. lia.
Qed.

(* our[]'s six bytes [fr + 2624, fr + 2630) are addressable when their shadow byte S(fr) + 328 is 06
   (fr mod 8 = 0, so the six bytes are the first six of the granule fr + 2624). *)
Lemma a4_our_addr : forall m fr, 0 <= fr -> fr mod 8 = 0 -> fr + 3136 <= APPMEM_END ->
  (forall a, fr <= a < fr + 3136 -> app_mem a) ->
  b8 m (Sfr fr + 328) 6 -> addressable m (fr + 2624) 6.
Proof.
  intros m fr H0 H8 HE Happ Hb. unfold b8 in Hb. destruct Hb as (_ & _ & Hb).
  pose proof (Hb 0%nat ltac:(cbn [length]; lia)) as Hb0.
  change (Z.of_nat 0) with 0 in Hb0. rewrite Z.add_0_r in Hb0. cbn [nth_error] in Hb0.
  split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. split; [apply Happ; lia|].
  exists (Z_to_bv 8 6). split.
  - replace (shadow_addr (fr + 2624 + i)) with (Sfr fr + 328); [exact Hb0|].
    unfold Sfr, shadow_addr. Z.div_mod_to_equations. lia.
  - right. replace (bv_signed (Z_to_bv 8 6)) with 6 by (vm_compute; reflexivity).
    split; [Z.div_mod_to_equations; lia | lia].
Qed.

(* An addressable range stays addressable across a run that writes none of its shadow bytes. The statement and
   proof of reac_box_model_block.v:80 (addr_munch); stated here so that this segment does not import that callee's
   walk file, which needs the callee's own v1.9 re-walk before it builds on the v1.9 image. *)
Lemma a4_addr_munch : forall W m m' p n, addressable m p n -> LibF.munch W m m' ->
  (forall i, 0 <= i < n -> LibF.outside W (shadow_addr (p + i))) -> addressable m' p n.
Proof.
  intros W m m' p n (H0 & Hn & He & HA) Hm HW. split; [exact H0|]. split; [exact Hn|]. split; [exact He|].
  intros i Hi. destruct (HA i Hi) as (Hap & b & Hb & Hok). split; [exact Hap|]. exists b. split; [|exact Hok].
  pose proof (in_shadow_range _ (shadow_of_app (p + i) Hap)) as Hbd.
  unfold LMem.mrd in *. rewrite Hm; [exact Hb|]. rewrite LMem.wa_unsigned by lia. apply HW, Hi.
Qed.

(* Contract.v's a_store_ok (generated), built in ONE place per case this file needs: a real-stack byte, and the
   shadow byte of a real-stack byte. Every site below goes through these two lemmas. *)
Lemma a4_store_ok_stk : forall H lo a, lo <= a < APPMEM_END -> AC.a_store_ok H lo a.
Proof. intros H lo a Ha. unfold AC.a_store_ok. right; left. exact Ha. Qed.

Lemma a4_store_ok_stk_shadow : forall H lo b, lo <= b < APPMEM_END -> AC.a_store_ok H lo (shadow_addr b).
Proof.
  intros H lo b Hb. unfold AC.a_store_ok. right; right; right. exists b. split; [reflexivity|]. right; left. exact Hb.
Qed.

Section A4.
Context {fx : YK11.FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

(* The generated laws of Contract.v, read ONCE each in this file and only through SlotInv's LawFields records
   (lw_fs_place / lw_fs_ok + lw_fs_bytes / lw_store / lw_mat_le / lw_blocks, which match each field to the law by
   statement): no positional destruct of a generated conclusion is left here. Every site below goes through these
   five lemmas. *)
Lemma a4_fs_place : forall H mem md b, AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  YO0d.word_mem rsegs mem (AC.as_tp AC.ASYMS) b -> 0 <= b < 2 ^ 64 ->
  AC.GT <= b /\ b + AC.FS_SIZE <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  (forall a, b <= a < b + AC.FS_SIZE -> app_mem a).
Proof.
  intros H mem md b HAH Hw Hb.
  destruct (lw_fs_place (APIf rc) H mem md b HAH Hw Hb) as [Hgt Hlo _ Happ].
  exact (conj Hgt (conj Hlo Happ)).
Qed.

Lemma a4_fs_rw : forall H mem md FS, AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  YO0d.word_mem rsegs mem (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 ->
  forall a, FS <= a < FS + AC.FS_SIZE -> YP09.writable_at rsegs mem a /\ exists b, YP09.mbyte rsegs mem a = Some b.
Proof.
  intros H mem md FS HAH Hw HFS.
  exact (lw_fs_bytes mem FS (lw_fs_ok (APIf rc) H mem md FS HAH Hw HFS)).
Qed.

Lemma a4_store : forall H mem mem' md, AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ AC.a_store_ok H (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
     mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < 2 ^ 64 -> YP09.writable_at rsegs mem a -> YP09.writable_at rsegs mem' a) ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem' md /\
  (forall a, AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem' md a <->
             AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem md a) /\
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md.
Proof.
  intros H mem mem' md HAH Hk Hw.
  destruct (lw_store (APIf rc) H mem mem' md HAH Hk Hw) as [H1 H2 H3 H4].
  exact (conj H1 (conj H2 (conj H3 H4))).
Qed.

Lemma a4_mat_le : forall H mem md md', AsanLift.mat_le md md' ->
  (AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md -> AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md') /\
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md' = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md.
Proof.
  intros H mem md md' Hm.
  destruct (lw_mat_le (APIf rc) H mem md md' Hm) as [H1 _ H3 _].
  exact (conj H1 H3).
Qed.

Lemma a4_blocks : forall H mem md p n, AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md -> In (p, n) H ->
  p + n <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  forall a, p <= a < p + n -> app_mem a /\ ~ AC.a_in_fs AC.ASYMS mem a.
Proof.
  intros H mem md p n HAH Hin.
  destruct (lw_blocks (APIf rc) H mem md p n HAH Hin) as [_ _ Hend _ Hall].
  split; [exact Hend|]. intros a Ha.
  destruct (Hall a Ha) as (Happ & _ & _ & _ & Hnfs). exact (conj Happ Hnfs).
Qed.

(* FRAS and ENT across the run of a4_evt: the run writes the last 137 shadow bytes of the frame and the spill
   block [A + 16, A + 288) of the prologue save area, nothing else. *)
Lemma a4_fras : forall g fr regs regs' mem mem' md md' s5 A0 shn,
  FRAS B APIf ra g fr [] regs mem md s5 -> ENT APIf g [] mem md -> rg regs 9 A0 -> 0 <= A0 < 2 ^ 64 ->
  munch [(Sfr fr + 255, Sfr fr + 392); (A0 + 16, A0 + 288)] mem mem' -> wmono rsegs mem mem' ->
  stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g) ->
  bytes_at rsegs mem' (Sfr fr + 255) shn -> length shn = 137%nat ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  AsanLift.mat_le md md' ->
  FRAS B APIf ra g fr [] regs' mem' md' s5 /\ ENT APIf g [] mem' md'.
Proof.
  intros g fr regs regs' mem mem' md md' s5 A0 shn HFRAS HENT HrA HA0 MU WM STw' Hshn Hshnl
    K2 K3 K4 K8 K9 K19 K26 Hmat.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  pose proof FF as (_ & _ & _ & _ & Hhead & Hlock & Hthr & _).
  pose proof HFRAS as HF2.
  destruct HF2 as (A & sp & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz & Hstklo & Hr4 & Hr8 & Hr9 &
    Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & HfrA & HA416 & HS4 & HSapp & Hspill & Hloc & Hhdr1 & Hhdr2 &
    HshF & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HFSsz : AC.FS_SIZE = 11571200) by reflexivity.
  assert (HGT : AC.GT = 6283264) by reflexivity.
  assert (HA64 : 0 <= A < 2 ^ 64).
  { pose proof Hwin as Hw. destruct Hw as (Hw0 & Hw1 & _). lia. }
  assert (EA : A0 = A).
  { pose proof (rg_eq64 regs 9 A0 A HrA Hr9) as Hm. rewrite !Z.mod_small in Hm by lia. exact Hm. }
  subst A0.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) ([] ++ g_H g) mem md HAH)
    as Hhigh.
  (* the frame's bytes are application memory, and the frame sits above the image *)
  assert (Happ : forall a, fr <= a < fr + 3136 -> app_mem a).
  { destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0 [Hfsb [Hfs Hrec]]]].
    - intros a Ha. destruct (Hreal a Ha) as (Hlo & Hhi). right.
      unfold HIGHMEM_BEG in *. lia.
    - intros a Ha. destruct (Hfs a Ha) as (b & Hbr & Hwb & Hba).
      destruct (a4_fs_place ([] ++ g_H g) mem md b HAH Hwb Hbr) as (_ & _ & Hfsapp).
      apply Hfsapp. lia. }
  assert (HfrGT : AC.GT <= fr).
  { destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0 [Hfsb [Hfs Hrec]]]].
    - destruct (Hreal fr ltac:(lia)) as (Hlo & _). unfold HIGHMEM_BEG in Hhigh. lia.
    - destruct (Hfs fr ltac:(lia)) as (b & Hbr & Hwb & Hba).
      destruct (a4_fs_place ([] ++ g_H g) mem md b HAH Hwb Hbr) as (Hgt & _ & _). lia. }
  assert (HfrB : 0 <= fr /\ fr + 3136 <= APPMEM_END).
  { pose proof (Happ fr ltac:(lia)) as H1. pose proof (Happ (fr + 3135) ltac:(lia)) as H2.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in H1, H2. unfold APPMEM_END. lia. }
  assert (Hfr8 : fr mod 8 = 0).
  { pose proof (Z.mod_eq fr 32 ltac:(lia)) as X. rewrite Hfrm in X.
    replace fr with ((4 * (fr / 32)) * 8) by lia. apply Z_mod_mult. }
  (* the 392 shadow bytes of the frame *)
  assert (HshB : forall x, Sfr fr <= x < Sfr fr + 392 ->
            x = shadow_addr (fr + 8 * (x - Sfr fr)) /\ fr <= fr + 8 * (x - Sfr fr) < fr + 3136).
  { intros x Hx. split; [|lia].
    assert (Hdiv : (fr + 8 * (x - Sfr fr)) / 8 = fr / 8 + (x - Sfr fr)).
    { replace (8 * (x - Sfr fr)) with ((x - Sfr fr) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
    unfold shadow_addr. rewrite Hdiv. unfold Sfr, shadow_addr. lia. }
  assert (HshIS : forall x, Sfr fr <= x < Sfr fr + 392 -> in_shadow x).
  { intros x Hx. destruct (HshB x Hx) as (Hx1 & Hx2). rewrite Hx1. apply shadow_of_app. apply Happ. exact Hx2. }
  assert (HSfr0 : 0 <= Sfr fr).
  { pose proof (in_shadow_range _ (HshIS (Sfr fr) ltac:(lia))). lia. }
  assert (HSfrH : Sfr fr + 392 <= HIGHMEM_BEG).
  { pose proof (HshIS (Sfr fr + 391) ltac:(lia)) as His.
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in His. unfold HIGHMEM_BEG. lia. }
  assert (HSfrL : LOWMEM_END <= Sfr fr).
  { pose proof (HshIS (Sfr fr) ltac:(lia)) as His.
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in His. unfold LOWMEM_END. lia. }
  assert (HAhigh : HIGHMEM_BEG <= A + 16) by lia.
  assert (HSfrA : Sfr fr + 392 <= A) by lia.
  assert (HA288 : A + 288 <= 2 ^ 64) by (unfold APPMEM_END in HSapp; lia).
  (* the write set of the run *)
  assert (Hout : forall x, 0 <= x < LOWMEM_END ->
            outside [(Sfr fr + 255, Sfr fr + 392); (A + 16, A + 288)] x).
  { intros x Hx.
    unfold LOWMEM_END in Hx, HSfrL. cbn [outside]. unfold HIGHMEM_BEG in HAhigh.
    split; [lia|]. split; [lia | exact I]. }
  assert (Hwm : forall q, 0 <= q < 2 ^ 64 -> writable_at rsegs mem q -> writable_at rsegs mem' q)
    by (intros q _ H; exact (WM (Z_to_bv 64 q) H)).
  assert (Hpres : forall q, 0 <= q < 2 ^ 64 ->
            (exists b, mbyte rsegs mem q = Some b) -> (exists b, mbyte rsegs mem' q = Some b)).
  { intros q Hq Hb.
    destruct (Z_le_gt_dec (Sfr fr + 255) q) as [H1|H1];
      [destruct (Z_lt_ge_dec q (Sfr fr + 392)) as [H2|H2]|].
    - apply (bytes_present mem' (Sfr fr + 255) shn q Hshn ltac:(lia)).
    - destruct (Z_le_gt_dec (A + 16) q) as [H3|H3];
        [destruct (Z_lt_ge_dec q (A + 288)) as [H4|H4]|].
      + destruct STw' as (_ & _ & Hst). exact (proj2 (Hst q ltac:(lia))).
      + destruct Hb as (b & Hb). exists b. rewrite <- Hb.
        unfold mbyte. rewrite (MU (Z_to_bv 64 q) ltac:(rewrite MState.unsigned_lit by lia;
          cbn [outside]; split; [lia|]; split; [lia | exact I])). reflexivity.
      + destruct Hb as (b & Hb). exists b. rewrite <- Hb.
        unfold mbyte. rewrite (MU (Z_to_bv 64 q) ltac:(rewrite MState.unsigned_lit by lia;
          cbn [outside]; split; [lia|]; split; [lia | exact I])). reflexivity.
    - destruct (Z_le_gt_dec (A + 16) q) as [H3|H3];
        [destruct (Z_lt_ge_dec q (A + 288)) as [H4|H4]|].
      + destruct STw' as (_ & _ & Hst). exact (proj2 (Hst q ltac:(lia))).
      + destruct Hb as (b & Hb). exists b. rewrite <- Hb.
        unfold mbyte. rewrite (MU (Z_to_bv 64 q) ltac:(rewrite MState.unsigned_lit by lia;
          cbn [outside]; split; [lia|]; split; [lia | exact I])). reflexivity.
      + destruct Hb as (b & Hb). exists b. rewrite <- Hb.
        unfold mbyte. rewrite (MU (Z_to_bv 64 q) ltac:(rewrite MState.unsigned_lit by lia;
          cbn [outside]; split; [lia|]; split; [lia | exact I])). reflexivity. }
  (* the heap invariant, ownership and the stack bounds after the run *)
  assert (HAHt : AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) ([] ++ g_H g) mem' md /\
            (forall a, AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) ([] ++ g_H g) mem' md a <->
                       AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) ([] ++ g_H g) mem md a) /\
            AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md
              = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
            AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md
              = AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md).
  { destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0 [Hfsb [Hfs Hrec]]]].
    - assert (Hag : forall a, 0 <= a < 2 ^ 64 ->
                ~ AC.a_store_ok ([] ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
                mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
      { intros a Ha Hns. apply MU. rewrite MState.unsigned_lit by lia.
        cbn [outside]. split; [|split; [|exact I]]; intros (Hl & Hh); apply Hns.
        - rewrite (proj1 (HshB a ltac:(lia))). apply a4_store_ok_stk_shadow. apply Hreal. lia.
        - apply a4_store_ok_stk. split; lia. }
      exact (a4_store ([] ++ g_H g) mem mem' md HAH Hag Hwm).
    - destruct (Hfs fr ltac:(lia)) as (FS & HFSr & HwFS & HFSa).
      pose proof (Hfsb FS HwFS HFSr) as HFSfr.
      destruct (a4_fs_place ([] ++ g_H g) mem md FS HAH HwFS HFSr) as (HFSgt & HFSlo & HFSapp).
      assert (HfrFS : fr + 3136 <= FS + AC.FS_SIZE).
      { destruct (Hfs (fr + 3135) ltac:(lia)) as (FS2 & HFS2r & HwFS2 & HFS2a).
        assert (FS2 = FS).
        { apply (word_mem_uniq mem (AC.as_tp AC.ASYMS) FS2 FS HwFS2 HwFS HFS2r HFSr);
            unfold AC.as_tp, AC.ASYMS; cbn; lia. }
        subst FS2. lia. }
      assert (Hmeta : forall q, fs_meta FS q -> outside [(Sfr fr + 255, Sfr fr + 392); (A + 16, A + 288)] q).
      { intros q Hq. destruct (fs_meta_in FS q Hq) as (Hq1 & Hq2).
        assert (Happq : app_mem q) by (apply HFSapp; lia).
        cbn [outside]. split; [|split; [|exact I]]; intros (Hl & Hh).
        - exact (app_not_shadow q Happq (HshIS q ltac:(lia))).
        - lia. }
      assert (Hag : forall q, 0 <= q < 2 ^ 64 ->
                ~ AC.a_store_ok ([] ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) q ->
                ~ (FS <= q < FS + AC.FS_SIZE) ->
                ~ (exists b, FS <= b < FS + AC.FS_SIZE /\ q = shadow_addr b) ->
                mem' (Z_to_bv 64 q) = mem (Z_to_bv 64 q)).
      { intros q Hq Hns HnFS Hnsh. apply MU. rewrite MState.unsigned_lit by lia.
        cbn [outside]. split; [|split; [|exact I]]; intros (Hl & Hh).
        - apply Hnsh. exists (fr + 8 * (q - Sfr fr)).
          split; [lia | exact (proj1 (HshB q ltac:(lia)))].
        - apply Hns. apply a4_store_ok_stk. split; lia. }
      exact (a_fs_ok_store_AH AC.ASYMS (AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc))
               (AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc)) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc))
               (AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc))
               [(Sfr fr + 255, Sfr fr + 392); (A + 16, A + 288)] ([] ++ g_H g) mem mem' md FS
               (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) HAH HwFS HFSr ltac:(unfold APPMEM_END in HSapp; lia)
               MU Hwm Hpres Hmeta Hag). }
  destruct HAHt as (HAH' & HOWN & HSTK' & HSTKhi').
  (* the runtime after the run *)
  assert (HshR : forall a, in_shadow a -> exists b, mrd rsegs mem' (wa a) = Some b).
  { intros a Hin.
    destruct (Z_le_gt_dec (Sfr fr + 255) a) as [H1|H1];
      [destruct (Z_lt_ge_dec a (Sfr fr + 392)) as [H2|H2]|].
    - apply (bytes_present mem' (Sfr fr + 255) shn a Hshn ltac:(lia)).
    - destruct (AsanRTInv.RT_shadow_rw sp mem md HRT a Hin) as (_ & b & Hb).
      pose proof (in_shadow_range a Hin) as Hr.
      unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hin.
      unfold HIGHMEM_BEG in HAhigh.
      exists b. apply (mrd_keep _ mem mem' a b MU); [split; [lia|]; split; [lia | exact I] | lia | exact Hb].
    - destruct (AsanRTInv.RT_shadow_rw sp mem md HRT a Hin) as (_ & b & Hb).
      pose proof (in_shadow_range a Hin) as Hr.
      unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hin.
      unfold HIGHMEM_BEG in HAhigh.
      exists b. apply (mrd_keep _ mem mem' a b MU); [split; [lia|]; split; [lia | exact I] | lia | exact Hb]. }
  assert (HRT' : AsanRTInv.RT sp mem' md).
  { apply (AsanRTInv.RT_meta_write sp sp mem mem' md md [(Sfr fr + 255, Sfr fr + 392); (A + 16, A + 288)]
             HRT MU WM); [|exact HshR].
    unfold rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF,
      RT_CF, RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG,
      RT_AGLOB, RT_AGLOB_LEN.
    unfold LOWMEM_END in HSfrL. unfold HIGHMEM_BEG in HAhigh.
    cbn. repeat split; lia. }
  (* the image-level facts after the run *)
  assert (Hro' : ro_agree rsegs mem')
    by (apply (ro_agree_keep _ mem mem' Hro MU Hout)).
  assert (Hkl : forall (sg : list Segment) x, 0 <= x < LOWMEM_END -> mbyte sg mem' x = mbyte sg mem x)
    by (intros sg x Hx; exact (mbyte_keep_low _ mem mem' sg x MU Hout Hx)).
  assert (Hsn' : sink_none B mem' md).
  { destruct Hsn as (Hcse & Hohd & Hfd). split; [|split; [|exact Hfd]].
    - destruct Hcse as (Hthrm & Hlockm). split.
      + eapply YI14.val_mem_frame; [|exact Hthrm]. intros x Hx. apply Hkl.
        rewrite Hthr in Hx. cbn in Hx. unfold LOWMEM_END. lia.
      + eapply YI14.val_mem_frame; [|exact Hlockm]. intros x Hx. apply Hkl.
        rewrite Hlock in Hx. cbn in Hx. unfold LOWMEM_END. lia.
    - intros k Hk. rewrite Hkl.
      + exact (Hohd k Hk).
      + rewrite Hhead. unfold LOWMEM_END. lia. }
  assert (Hgimg' : G_img_c B AF.frame_RELRO mem').
  { intros a Hin. rewrite Hkl.
    - exact (Hgimg a Hin).
    - pose proof (frame_RELRO_lo a Hin) as Ra. unfold AC.GT in Ra. unfold LOWMEM_END. lia. }
  (* the frame / spill / saved bytes after the run *)
  assert (Hspill' : q64 mem' (A + 304) fr).
  { unfold q64 in *.
    apply (fl_bytes [(Sfr fr + 255, Sfr fr + 392); (A + 16, A + 288)] mem mem' _ _ Hspill MU).
    rewrite LMem.length_le8. intros x Hx. split; [lia|]. split; [lia | exact I]. }
  assert (Hhdr1' : q64 mem' fr 0x41b58ab3).
  { unfold q64 in *.
    apply (fl_bytes [(Sfr fr + 255, Sfr fr + 392); (A + 16, A + 288)] mem mem' _ _ Hhdr1 MU).
    rewrite LMem.length_le8. intros x Hx. split.
    { intros (Hl & Hh). exact (app_not_shadow x (Happ x ltac:(cbn in Hx; lia)) (HshIS x ltac:(lia))). }
    split; [cbn in Hx; lia | exact I]. }
  assert (Hhdr2' : q64 mem' (fr + 16) AF.ENTRY).
  { unfold q64 in *.
    apply (fl_bytes [(Sfr fr + 255, Sfr fr + 392); (A + 16, A + 288)] mem mem' _ _ Hhdr2 MU).
    rewrite LMem.length_le8. intros x Hx. split.
    { intros (Hl & Hh). exact (app_not_shadow x (Happ x ltac:(cbn in Hx; lia)) (HshIS x ltac:(lia))). }
    split; [cbn in Hx; lia | exact I]. }
  assert (Hsaved' : LMem.bytes_at rsegs mem' (g_S g - 104) (saved_bytes ra g)).
  { apply (fl_bytes [(Sfr fr + 255, Sfr fr + 392); (A + 16, A + 288)] mem mem' _ _ Hsaved MU).
    intros x Hx. unfold saved_bytes in Hx. rewrite !length_app, !LMem.length_le8 in Hx. cbn in Hx.
    split; [lia|]. split; [lia | exact I]. }
  assert (Herrno' : forall a, AC.a_errno AC.ASYMS <= a < AC.a_errno AC.ASYMS + 4 -> writable_at rsegs mem' a)
    by (intros a Ha; exact (WM (Z_to_bv 64 a) (Herrno a Ha))).
  assert (HAG' : forall a, in_globals AF.frame_AG a -> addressable mem' a 1).
  { intros a Hin. pose proof (frame_AG_below a Hin) as Hb.
    assert (Ha0 : 0 <= a) by (destruct (HAG a Hin) as (Ha & _); exact Ha).
    apply (a4_addr_munch [(Sfr fr + 255, Sfr fr + 392); (A + 16, A + 288)] mem mem' a 1 (HAG a Hin) MU).
    intros i Hi. replace (a + i) with a by lia.
    assert (Hdm : a / 8 <= fr / 8) by (apply Z.div_le_mono; lia).
    assert (HSfrd : Sfr fr = fr / 8 + ASAN_K) by reflexivity.
    unfold shadow_addr. unfold HIGHMEM_BEG in HAhigh.
    split; [lia|]. split; [lia | exact I]. }
  (* the slot window outside the frame stays addressable: its shadow bytes are outside the frame's 392 and are
     not app memory *)
  assert (HWA' : forall a, g_S g - AF.SLOT_STACK <= a < g_S g -> ~ (fr <= a < fr + FRAME_BYTES) -> addressable mem' a 1).
  { intros a H1 H2.
    pose proof (HWA a H1 H2) as HadA.
    pose proof (addr1_app mem a HadA) as Happa.
    assert (Ha0 : 0 <= a) by (destruct HadA as (H0 & _); exact H0).
    pose proof (shadow_of_app a Happa) as Hsa.
    pose proof Hsa as Hsa'. unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hsa'.
    apply (addr1_munch [(Sfr fr + 255, Sfr fr + 392); (A + 16, A + 288)] mem mem' a MU); [|exact HadA].
    split; [|split; [|exact I]].
    - intros Hin. apply H2. apply (sh_in_frame fr a Hfr8 ltac:(lia) Ha0). lia.
    - unfold HIGHMEM_BEG in HAhigh. lia. }
  (* the 392 shadow bytes after the run: the first 255 kept, the last 137 rewritten *)
  assert (HshF' : exists sh, LMem.bytes_at rsegs mem' (Sfr fr) sh /\ length sh = Z.to_nat FRAME_SHADOW).
  { destruct HshF as (sh & Hsh & Hl).
    assert (Hfl : length (firstn 255 sh) = 255%nat) by (rewrite length_firstn, Hl; reflexivity).
    exists (firstn 255 sh ++ shn). split.
    - apply (proj2 (LMem.bytes_at_app rsegs mem' (Sfr fr) (firstn 255 sh) shn)). split.
      + apply (fl_bytes [(Sfr fr + 255, Sfr fr + 392); (A + 16, A + 288)] mem mem').
        * apply (proj1 (LMem.bytes_at_app rsegs mem (Sfr fr) (firstn 255 sh) (skipn 255 sh))).
          rewrite firstn_skipn. exact Hsh.
        * exact MU.
        * rewrite Hfl. change (Z.of_nat 255) with 255. intros x Hx.
          split; [lia|]. split; [lia | exact I].
      + rewrite Hfl. change (Z.of_nat 255) with 255. exact Hshn.
    - rewrite length_app, Hfl, Hshnl. reflexivity. }
  (* ENT across the run: no byte ENT speaks of is in the write set *)
  assert (HENT1 : ENT APIf g [] mem' md).
  { eapply ent_munch with (W := [(Sfr fr + 255, Sfr fr + 392); (A + 16, A + 288)]);
      [exact HENT | exact HAH | apply (proj2 (fr_munch_ul _ _ _)); exact MU | | exact HSTK' | exact HSTKhi' |].
    - (* ent_kept taken apart once, here: the only ENT transport of this file *)
      intros x Hk.
      unfold HIGHMEM_BEG in Hhigh, HSfrH, HAhigh. unfold LOWMEM_END in HSfrL. unfold AC.GT in HfrGT.
      destruct Hk as [Hblkk | [Hik | [Habk | [(b & Hor & ->) | Hbsh]]]].
      + destruct Hblkk as (q & k & i & Hin & Hni & Hi & ->).
        destruct (a4_blocks ([] ++ g_H g) mem md q k HAH (in_or_app _ _ _ (or_intror Hin))) as (Hend & Hall).
        destruct (Hall (q + i) ltac:(lia)) as (Happq & _).
        split; [|split; [|exact I]].
        * intros Hs. exact (app_not_shadow (q + i) Happq (HshIS (q + i) ltac:(lia))).
        * lia.
      + pose proof (img_below_GT x Hik) as Hxg. unfold AC.GT in Hxg.
        split; [|split; [|exact I]]; lia.
      + split; [|split; [|exact I]]; lia.
      + assert (Hb0 : 0 <= b)
          by (destruct Hor as [Hi|Hr]; [pose proof (img_below_GT b Hi) as X; unfold AC.GT in X|]; lia).
        assert (Hnb : ~ (fr <= b < fr + 3136))
          by (destruct Hor as [Hi|Hr]; [pose proof (img_below_GT b Hi) as X; unfold AC.GT in X|]; lia).
        assert (Happb : app_mem b).
        { destruct Hor as [Hi|Hr];
            [pose proof (img_below_GT b Hi) as X; unfold AC.GT, app_mem, LOWMEM_END in *; left; lia
            |unfold app_mem, HIGHMEM_BEG, APPMEM_END in *; right; lia]. }
        pose proof (shadow_of_app b Happb) as Hsb.
        pose proof Hsb as Hsb'. unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hsb'.
        split; [|split; [|exact I]].
        * intros Hin. apply Hnb. apply (sh_in_frame fr b Hfr8 ltac:(lia) Hb0). lia.
        * lia.
      + (* batch 2 item 9: the shadow byte of an entry block byte, an app byte off the frame (real arm: the block is
           below stklo and the frame at or above it; side arm: the frame is in the FakeStack, which no block meets) *)
        destruct Hbsh as (q & k & i & Hin & Hni & Hi & ->).
        destruct (a4_blocks ([] ++ g_H g) mem md q k HAH (in_or_app _ _ _ (or_intror Hin))) as (Hend & Hall).
        destruct (Hall (q + i) ltac:(lia)) as (Happq & Hnfs).
        assert (Hq0 : 0 <= q + i)
          by (pose proof Happq as X; unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in X; lia).
        assert (Hnb : ~ (fr <= q + i < fr + 3136)).
        { intros Hf. destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0 [Hfsb [Hfs Hrec]]]].
          - destruct (Hreal (q + i) ltac:(lia)) as (Hr1 & _). lia.
          - exact (Hnfs (Hfs (q + i) ltac:(lia))). }
        pose proof (shadow_of_app (q + i) Happq) as Hsb.
        pose proof Hsb as Hsb'. unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hsb'.
        split; [|split; [|exact I]].
        * intros Hin'. apply Hnb. apply (sh_in_frame fr (q + i) Hfr8 ltac:(lia) Hq0). lia.
        * lia.
    - intros a _ Ho. exact (proj2 (HOWN a) Ho). }
  (* move the model along the lazy materialization *)
  destruct (a4_mat_le ([] ++ g_H g) mem' md md' Hmat) as (HAHm & Hstklo_eq).
  split; [|eapply ent_mat; [exact HENT1 | exact Hmat]].
  (* FRAS at the exit *)
  exists A, sp.
  split; [exact (AsanRTInv.RT_any sp sp mem' md md' HRT')|].
  split; [exact (HAHm HAH')|].
  split; [exact Hro'|].
  split; [destruct Hsn' as (He & Hh & Hf); split; [exact He|];
          split; [exact Hh|]; rewrite (sl_mat_fds md md' Hmat); exact Hf|].
  split; [rewrite (AsanLift.mat_le_halted md md' Hmat); exact Hhalt|].
  split; [exact Hgimg'|].
  split; [rewrite K2; exact Hr2|].
  split; [exact Hspm|].
  split; [unfold AC.aspZ in *; rewrite K2; exact Haspz|].
  split; [rewrite Hstklo_eq, HSTK'; exact Hstklo|].
  split; [rewrite K4; exact Hr4|].
  split; [unfold rg in *; rewrite K8; exact Hr8|].
  split; [unfold rg in *; rewrite K9; exact Hr9|].
  split; [rewrite K3; exact Hr3|].
  split; [unfold rg in *; rewrite K19; exact Hr19|].
  split; [unfold rg in *; rewrite K26; exact Hr26|].
  split; [exact Hfrm|].
  split; [exact Hs5|].
  split; [exact HAm|].
  split; [exact HAS|].
  split; [exact Hspa|].
  split; [exact HfrA|].
  split; [exact HA416|].
  split; [exact HS4|].
  split; [exact HSapp|].
  split; [exact Hspill'|].
  split.
  { destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0 [Hfsb [Hfs Hrec]]]].
    - left. split; [exact H0|]. split; [exact Hspfr|].
      intros a Ha. rewrite Hstklo_eq, HSTK'. exact (Hreal a Ha).
    - right. split; [exact Hfr0|]. split; [|split].
      + intros FS HwFS HFSr. apply (Hfsb FS); [|exact HFSr].
        eapply KindBGlue.word_mem_frame; [exact HwFS|].
        intros k Hk. symmetry. apply Hkl. unfold AC.as_tp, AC.ASYMS. cbn. unfold LOWMEM_END. lia.
      + intros a Ha. destruct (Hfs a Ha) as (b & Hb64 & Hwb & Hba).
        exists b. split; [exact Hb64|]. split; [|exact Hba].
        eapply KindBGlue.word_mem_frame; [exact Hwb|].
        intros k Hk. apply Hkl. unfold AC.as_tp, AC.ASYMS. cbn. unfold LOWMEM_END. lia.
      + (* the FakeStack record cells are below stklo and app memory: neither the spill block (at or above
           stklo) nor the frame's shadow bytes *)
        eapply fsrec_munch_lo with (W := [(Sfr fr + 255, Sfr fr + 392); (A + 16, A + 288)]);
          [exact Hrec | exact HAH | apply (proj2 (fr_munch_ul _ _ _)); exact MU | |].
        * intros x Hx. unfold LOWMEM_END in HSfrL. unfold AC.GT in HfrGT.
          split; [|split; [|exact I]]; lia.
        * intros x Hap Hnb Hlo. split; [|split; [|exact I]].
          -- intros Hs. exact (app_not_shadow x Hap (HshIS x ltac:(lia))).
          -- lia. }
  split; [exact Hhdr1'|].
  split; [exact Hhdr2'|].
  split; [exact HshF'|].
  split; [exact STw'|].
  split; [exact Hsaved'|].
  split; [exact Herrno'|].
  split; [exact HAG'|].
  split; [exact HWA'|].
  split; [exact HSHI1|].
  split; [exact HSHI2|].
  split; [exact HSHI3|].
  split; [exact Hhb | exact Hlive].
Qed.

(* Segment A4 (0x810e4-0x813fc, plan-asan 2 / FP.4-FP.5): the entry cut is Inv_A810e4 (FRAS: the selector is not
   spilled yet); the exits are Inv_A81400_at turn 0 (n < 2^26, FRA rebuilt by FRA_of_FRAS from the 0x8131c /
   0x8137c spills) and Inv_Jrel (n >= 2^26, the early edge 0x81314 `j 0x82b80`, which keeps FRAS and the selector
   in register 21). *)
Lemma seg_A4 :
  Hat B APIf ra (Inv_A81400_at B APIf ra) 0 ->
  Hcut B APIf ra (Inv_Jrel B APIf ra) ->
  Hcut B APIf ra (Inv_A810e4 B APIf ra).
Proof.
  intros H813 Hjr g c HInv.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (regs & mem & md & fr & s5 & Ec & HFRAS & HENT & Hnmax & R18 & R20 & R21 & R22 & R23 & R24 & R25 &
    HINB & HIN).
  subst c. rewrite SEGS.
  pose proof HFRAS as HF2.
  destruct HF2 as (A & sp & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz & Hstklo & Hr4 & Hr8 & Hr9 &
    Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & HfrA & HA416 & HS4 & HSapp & Hspill & Hloc & Hhdr1 & Hhdr2 &
    HshF & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HFSsz : AC.FS_SIZE = 11571200) by reflexivity.
  assert (HGT : AC.GT = 6283264) by reflexivity.
  assert (Hn0 : 0 <= g_n g) by (unfold g_n, nlen; lia).
  assert (HANM : AC.ANMAX = 1073741824) by reflexivity.
  assert (HA64 : 0 <= A < 2 ^ 64).
  { pose proof Hwin as Hw. destruct Hw as (Hw0 & Hw1 & _). lia. }
  pose proof (AC.a_laws_stack_high _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) ([] ++ g_H g) mem md HAH)
    as Hhigh.
  (* the frame's bytes are application memory, and the frame sits above the image *)
  assert (Happ : forall a, fr <= a < fr + 3136 -> app_mem a).
  { destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0 [Hfsb [Hfs Hrec]]]].
    - intros a Ha. destruct (Hreal a Ha) as (Hlo & Hhi). right.
      unfold HIGHMEM_BEG in *. lia.
    - intros a Ha. destruct (Hfs a Ha) as (b & Hbr & Hwb & Hba).
      destruct (a4_fs_place ([] ++ g_H g) mem md b HAH Hwb Hbr) as (_ & _ & Hfsapp).
      apply Hfsapp. lia. }
  assert (HfrGT : AC.GT <= fr).
  { destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0 [Hfsb [Hfs Hrec]]]].
    - destruct (Hreal fr ltac:(lia)) as (Hlo & _). unfold HIGHMEM_BEG in Hhigh. lia.
    - destruct (Hfs fr ltac:(lia)) as (b & Hbr & Hwb & Hba).
      destruct (a4_fs_place ([] ++ g_H g) mem md b HAH Hwb Hbr) as (Hgt & _ & _). lia. }
  assert (HfrB : 0 <= fr /\ fr + 3136 <= APPMEM_END).
  { pose proof (Happ fr ltac:(lia)) as H1. pose proof (Happ (fr + 3135) ltac:(lia)) as H2.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in H1, H2. unfold APPMEM_END. lia. }
  assert (Hfr8 : fr mod 8 = 0).
  { pose proof (Z.mod_eq fr 32 ltac:(lia)) as X. rewrite Hfrm in X.
    replace fr with ((4 * (fr / 32)) * 8) by lia. apply Z_mod_mult. }
  (* the 392 shadow bytes of the frame *)
  assert (HshB : forall x, Sfr fr <= x < Sfr fr + 392 ->
            x = shadow_addr (fr + 8 * (x - Sfr fr)) /\ fr <= fr + 8 * (x - Sfr fr) < fr + 3136).
  { intros x Hx. split; [|lia].
    assert (Hdiv : (fr + 8 * (x - Sfr fr)) / 8 = fr / 8 + (x - Sfr fr)).
    { replace (8 * (x - Sfr fr)) with ((x - Sfr fr) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
    unfold shadow_addr. rewrite Hdiv. unfold Sfr, shadow_addr. lia. }
  assert (HshIS : forall x, Sfr fr <= x < Sfr fr + 392 -> in_shadow x).
  { intros x Hx. destruct (HshB x Hx) as (Hx1 & Hx2). rewrite Hx1. apply shadow_of_app. apply Happ. exact Hx2. }
  assert (HSfr0 : 0 <= Sfr fr).
  { pose proof (in_shadow_range _ (HshIS (Sfr fr) ltac:(lia))). lia. }
  assert (HSfrH : Sfr fr + 392 <= HIGHMEM_BEG).
  { pose proof (HshIS (Sfr fr + 391) ltac:(lia)) as His.
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in His. unfold HIGHMEM_BEG. lia. }
  assert (HAhigh : HIGHMEM_BEG <= A + 16) by lia.
  assert (HSfrA : Sfr fr + 392 <= A) by lia.
  assert (HA288 : A + 288 <= 2 ^ 64) by (unfold APPMEM_END in HSapp; lia).
  (* the frame's bytes are readable and writable: on the real arm they are a sub-window of the slot window, on
     the side arm FakeStack bytes (a_fs_ok) *)
  assert (Hfstk : stk rsegs mem fr (fr + 3136)).
  { destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0 [Hfsb [Hfs Hrec]]]].
    - destruct (stk_split rsegs mem (g_S g - AF.SLOT_STACK) fr (g_S g) Hwin ltac:(lia)) as (_ & X).
      destruct (stk_split rsegs mem fr (fr + 3136) (g_S g) X ltac:(lia)) as (Y & _). exact Y.
    - split; [lia|]. split; [unfold APPMEM_END in HfrB; lia|].
      intros a Ha. destruct (Hfs a Ha) as (FS & HFSr & Hw & HFSa).
      exact (a4_fs_rw ([] ++ g_H g) mem md FS HAH Hw HFSr a ltac:(lia)). }
  (* the two cell blocks the run writes *)
  destruct (stk_junk mem (g_S g - AF.SLOT_STACK) (g_S g) (A + 16) 272 Hwin ltac:(lia) ltac:(cbn; lia))
    as (jsp & RWsp).
  assert (STsh : stk rsegs mem (Sfr fr + 255) (Sfr fr + 392)).
  { replace (Sfr fr + 392) with (Sfr fr + 255 + 137) by lia.
    apply (stk_shadow mem (Sfr fr + 255) 137 (AsanRTInv.RT_shadow_rw sp mem md HRT) ltac:(lia)).
    intros i Hi. apply HshIS. lia. }
  destruct (stk_junk mem (Sfr fr + 255) (Sfr fr + 392) (Sfr fr + 255) 137 STsh ltac:(lia) ltac:(cbn; lia))
    as (jsh & RWsh).
  (* the run *)
  apply (sl_run regs (Z_to_bv 64 0x810e4) mem md
    (fun R pc' mem' =>
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\ getr R 8 = getr regs 8 /\
       getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\ getr R 22 = getr regs 22 /\ getr R 26 = getr regs 26 /\
       munch [(Sfr fr + 255, Sfr fr + 392); (A + 16, A + 288)] mem mem' /\ wmono rsegs mem mem' /\
       stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g) /\
       (exists sh, bytes_at rsegs mem' (Sfr fr + 255) sh /\ length sh = 137%nat) /\
       ((g_n g < 2 ^ 26 /\ pc' = Z_to_bv 64 0x81400 /\
         a4_exit fr (Sfr fr) A s5 (getr regs 23) (getr regs 24) R mem') \/
        (2 ^ 26 <= g_n g /\ pc' = Z_to_bv 64 0x82b80 /\ getr R 21 = getr regs 21)))
    (Post B APIf ra g)).
  - exact Hhalt.
  - cbn [Regs6ss.mkR_of].
    eapply evt_mono.
    { eapply a4_evt with (A := A) (S3 := Sfr fr) (N := g_n g) (fr := fr) (s5v := s5)
        (lo := g_S g - AF.SLOT_STACK) (hi := g_S g).
      - exact Hr9.
      - exact R18.
      - exact Hr19.
      - exact R20.
      - exact R21.
      - exact R22.
      - exact R24.
      - exact R25.
      - unfold AC.ANMAX in Hnmax. lia.
      - exact HSfr0.
      - exact HSfrA.
      - exact HA288.
      - exact RWsh.
      - exact RWsp.
      - exact Hwin.
      - exact STsh. }
    intros ms' (R & pc' & mem' & Hms & P2 & P3 & P4 & P8 & P9 & P19 & P22 & P26 & MU & WM & STw' & STs' & Hs137 & Hbr).
    exists R, pc', mem'. split; [exact Hms|].
    split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P8|].
    split; [exact P9|]. split; [exact P19|]. split; [exact P22|]. split; [exact P26|].
    split; [exact MU|]. split; [exact WM|]. split; [exact STw'|]. split; [exact Hs137|].
    destruct Hbr as [(Hlt & Hpc & HX)|(Hge & Hpc & P21)].
    + left. split; [exact Hlt|]. split; [exact Hpc | exact HX].
    + right. split; [exact Hge|]. split; [exact Hpc | exact P21].
  - intros R pc' mem' regs' md' (K2 & K3 & K4 & K8 & K9 & K19 & K22 & K26 & MU & WM & STw' & Hs137 & Hbr) Hreg Hmat.
    destruct Hs137 as (shn & Hshn & Hshnl).
    destruct (a4_fras g fr regs regs' mem mem' md md' s5 A shn HFRAS HENT Hr9 HA64 MU WM STw' Hshn Hshnl
                (eq_trans (Hreg _) K2) (eq_trans (Hreg _) K3) (eq_trans (Hreg _) K4) (eq_trans (Hreg _) K8)
                (eq_trans (Hreg _) K9) (eq_trans (Hreg _) K19) (eq_trans (Hreg _) K26) Hmat)
      as (HFRAS' & HENT').
    assert (Hr9' : rg regs' 9 A) by (unfold rg in *; rewrite Hreg, K9; exact Hr9).
    rewrite <- SEGS.
    destruct Hbr as [(Hlt & Hpc & HX)|(Hge & Hpc & P21)]; subst pc'.
    + destruct HX as (X1 & X7 & X11 & X12 & X13 & X14 & X18 & X21 & X23 & X24 & X27 & X28 & X29 & X30 & X31 &
        Xsh & Xfr16 & Xsel24 & X144 & X152 & X168 & Xdecl200 & Xfrag192 & X216 & X240 & X280 &
        X40 & X120 & X136 & X160 & X176 & X448 & X248 & X184 & X256 & X264 & X272 & Xfirst32).
      (* the frame's bytes after the run: the run writes none of them *)
      assert (Hfstk' : stk rsegs mem' fr (fr + 3136)).
      { apply (stk_transport rsegs _ mem mem' fr (fr + 3136) Hfstk MU WM). intros x Hx. left.
        split; [|split; [|exact I]].
        - intros Hs. exact (app_not_shadow x (Happ x Hx) (HshIS x ltac:(lia))).
        - lia. }
      assert (Hrec : forall o len, 0 <= o -> 0 <= len -> o + len <= 3136 ->
                exists bs, LibS.rw_cells rsegs mem' (fr + o) [LibC.CB (Z.to_nat len) bs]).
      { intros o len H1 H2 H3. apply lib_rw_stk. rewrite Z2Nat.id by lia.
        destruct (stk_split rsegs mem' fr (fr + o) (fr + 3136) Hfstk' ltac:(lia)) as (_ & X).
        destruct (stk_split rsegs mem' (fr + o) (fr + o + len) (fr + 3136) X ltac:(lia)) as (Y & _).
        exact Y. }
      assert (Hsp : forall off v, q64 mem' (A + off) v -> spill regs' mem' off v)
        by (intros off v Hq; exists A; split; [exact Hr9' | exact Hq]).
      (* the input block: a live heap block below stklo, so neither its bytes nor its shadow bytes are written *)
      assert (Hinout : 0 < g_n g -> forall i, 0 <= i < g_n g ->
                app_mem (g_p g + i) /\ g_p g + i < AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
                ~ (fr <= g_p g + i < fr + 3136)).
      { intros Hn0' i Hi. destruct (HIN Hn0') as (HInH & _).
        destruct (a4_blocks ([] ++ g_H g) mem md (g_p g) (g_n g) HAH (in_or_app _ _ _ (or_intror HInH)))
          as (Hend & Hall).
        destruct (Hall (g_p g + i) ltac:(lia)) as (Happi & Hnfs).
        split; [exact Happi|]. split; [lia|].
        intros Hf. destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0 [Hfsb [Hfs Hrec']]]].
        - destruct (Hreal (g_p g + i) Hf) as (Hr1 & _). lia.
        - exact (Hnfs (Hfs (g_p g + i) Hf)). }
      apply H813. exists regs', mem', md', fr.
      split; [reflexivity|].
      split; [exact (FRA_of_FRAS B APIf ra g fr [] regs' mem' md' s5 A HFRAS' Hr9' Xsel24 Xfr16)|].
      split; [exact HENT'|].
      cbv beta. unfold rg.
      split; [exact Hlt|]. split; [lia|].
      split; [rewrite Hreg, X23; rewrite Z.min_l by lia; rewrite Z.add_0_r; exact R23|].
      split; [rewrite Hreg, X24; rewrite Z.min_l by lia; rewrite Z.sub_0_r; exact R24|].
      split.
      { apply bytes_at_nil. unfold APPMEM_END in HfrB. lia. }
      split; [rewrite Hreg; exact X21|]. split; [rewrite Hreg; exact X28|].
      split; [exact (Hsp _ _ X152)|].
      split; [rewrite Hreg; exact X18|].
      split.
      { (* PRO: the thirteen spills of the run, our[]'s six bytes addressable by the shadow byte 6, and the input
           facts: neither the input block's bytes nor its shadow bytes are in the write set *)
        unfold PRO.
        split; [exact (Hsp _ _ X40)|]. split; [exact (Hsp _ _ X120)|]. split; [exact (Hsp _ _ X136)|].
        split; [exact (Hsp _ _ X160)|]. split; [exact (Hsp _ _ X168)|]. split; [exact (Hsp _ _ X176)|].
        split; [exact (Hsp _ _ X448)|]. split; [exact (Hsp _ _ X248)|].
        split; [exact (a4_our_addr mem' fr (proj1 HfrB) Hfr8 (proj2 HfrB) Happ Xsh)|].
        split.
        { destruct (Z_le_gt_dec (g_n g) 0) as [Hz|Hz].
          - (* the empty input: the byte list is nil, so the fact is the same in any memory *)
            assert (Hnil : g_in g = []).
            { unfold g_n, nlen in Hz. destruct (g_in g) as [|b0 l]; [reflexivity | cbn [length] in Hz; lia]. }
            destruct HINB as (HB1 & HB2 & HB3). split; [exact HB1|]. split; [exact HB2|].
            intros i Hi. rewrite Hnil in Hi. cbn [length] in Hi. lia.
          - apply (fl_bytes [(Sfr fr + 255, Sfr fr + 392); (A + 16, A + 288)] mem mem' _ _ HINB MU).
            intros x Hx. rewrite <- g_n_len in Hx.
            destruct (Hinout ltac:(lia) (x - g_p g) ltac:(lia)) as (Happx & Hlox & _).
            replace (g_p g + (x - g_p g)) with x in Happx, Hlox by lia.
            split; [|split; [|exact I]].
            + intros Hs. exact (app_not_shadow x Happx (HshIS x ltac:(lia))).
            + lia. }
        split.
        { intros Hn0'. destruct (HIN Hn0') as (HInH & HADp). split; [exact HInH|].
          apply (a4_addr_munch [(Sfr fr + 255, Sfr fr + 392); (A + 16, A + 288)] mem mem' (g_p g) (g_n g) HADp MU).
          intros i Hi.
          destruct (Hinout Hn0' i Hi) as (Happi & _ & Hnfi).
          assert (Hpi0 : 0 <= g_p g + i)
            by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Happi; lia).
          pose proof (shadow_of_app (g_p g + i) Happi) as Hsi.
          pose proof Hsi as Hsi'. unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hsi'.
          split; [|split; [|exact I]].
          - intros Hin. apply Hnfi. apply (sh_in_frame fr (g_p g + i) Hfr8 ltac:(lia) Hpi0). lia.
          - unfold HIGHMEM_BEG in HAhigh. lia. }
        split; [exact (Hsp _ _ X184)|]. split; [exact (Hsp _ _ X256)|].
        split; [exact (Hsp _ _ X264)|]. split; [exact (Hsp _ _ X272)|].
        (* v1.9: [A + 32] = fr + 2880 (0x813c8 `addi a0,s5,704`, 0x813cc `sd a0,32(s1)`) *)
        exact (Hsp _ _ Xfirst32). }
      split; [rewrite Hreg; exact X7|]. split; [rewrite Hreg; exact X1|].
      split; [rewrite Hreg; exact X11|]. split; [rewrite Hreg; exact X12|].
      split; [rewrite Hreg; exact X13|]. split; [rewrite Hreg; exact X14|].
      split; [rewrite Hreg; exact X29|]. split; [rewrite Hreg; exact X30|].
      split; [rewrite Hreg; exact X31|].
      split; [exact Xsh|]. split; [rewrite Hreg; exact X27|].
      split; [exact (Hsp _ _ X144)|]. split; [exact (Hsp _ _ Xfrag192)|].
      split; [exact (Hrec 2688 38 ltac:(lia) ltac:(lia) ltac:(lia))|].
      split; [exact (Hrec 2768 72 ltac:(lia) ltac:(lia) ltac:(lia))|].
      split; [exact (Hsp _ _ X280)|]. split; [exact (Hsp _ _ X240)|].
      split; [exact (Hrec 3040 1 ltac:(lia) ltac:(lia) ltac:(lia))|].
      split; [exact (Hrec 3056 32 ltac:(lia) ltac:(lia) ltac:(lia))|].
      split; [unfold decl_slot; exact (Hsp _ _ Xdecl200)|]. split; [exact (Hsp _ _ X216)|].
      { destruct (stk_split rsegs mem' fr (fr + 2624) (fr + 3136) Hfstk' ltac:(lia)) as (_ & X).
        destruct (stk_split rsegs mem' (fr + 2624) (fr + 2630) (fr + 3136) X ltac:(lia)) as (Y & _).
        destruct (stk_bytes rsegs mem' (fr + 2624) (fr + 2630) Y ltac:(lia)) as (junk & Hjl & Hjb).
        exists junk. split; [rewrite Hjl; f_equal; lia|].
        first [exact Hjb | change (firstn (Z.to_nat 0) (OUR (g_in g)) ++ junk) with junk; exact Hjb]. }
    + apply Hjr. exists regs', mem', md', fr, s5.
      split; [reflexivity|].
      split; [exact HFRAS'|].
      split; [exact HENT'|].
      split; [unfold rg in *; rewrite Hreg, P21; exact R21
             |unfold rg in *; rewrite Hreg, K22; exact R22].
Qed.

End A4.
