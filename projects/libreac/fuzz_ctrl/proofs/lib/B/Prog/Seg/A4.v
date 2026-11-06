(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Segment A4 of fuzz_ctrl LLVMFuzzerTestOneInput (asan-ubsan, image B, libreac v1.9.0): v1.9 [0x81220, 0x81544]
   (cut Inv_B81220), the last 137 of the 392 entry shadow bytes, the size test `srli a1,s2,26; beqz a1`
   and the our[]/cursor init. Two exits: the n >= 2^26 early exit `j 0x82f2c` (Inv_Jrel, plan FP.5 / slot_early)
   and the fall-through to the our[] loop head 0x81548 with t = 0 (Inv_B81548_at). The run writes exactly the
   shadow bytes [S(fr) + 255, S(fr) + 392) and the spill bytes [A + 56, A + 320) (A = s1); FRA, with its input
   facts, is carried across that write set by a4_frah. On the fall-through the shadow byte S(fr) + 328 of our[] at
   fr + 2624 ends as 6 (0x81354 `sb s4,328(s3)`, then 0x814b0 `li a0,6` / 0x814b8 `sb a0,328(s3)`), so our[]'s
   6 bytes are addressable (a4_our_addr). The exit Inv_B81548_at is LOOPB at t = 0 (the spills and loop registers
   of turn 0 set in the run, s2 = n and s6 = p untouched, the input facts (a4_frah_in) and our[]'s six present
   bytes, which the run does not write) and PRA (the run's frame-loop pointer spills 0x81460-0x81510). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.UL Require Import Exec Step Tac Cells.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.AW Require Import SmLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Tac_fs.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.FrameAPI.

(* A byte store of a register whose value is not a literal (the shadow stores `sb s4/s5,k(s3)`): the engine's
   norm_lit_store_bytes turns only a literal byte store into a one-byte cell. le1 v is [Z_to_bv 8 (bv_unsigned v)]
   by conversion, so one branch serves both a register value and a literal. *)
Local Ltac norm_lit_store_bytes ::=
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
           is_Zlit z; change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z))
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
           is_Zlit z; change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z))
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?z)) _) =>
           is_Zlit z; change (Z_to_le_bytes 2 z) with (le2 (Z_to_bv 64 z))
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) =>
           is_Zlit z; change (Z_to_le_bytes 1 z) with [Z_to_bv 8 z]
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?v)) _) =>
           change (le1 v) with [Z_to_bv 8 (bv_unsigned v)]
       end).

(* The register file of the slot cuts, in the engine's concrete form (the image-B twin of the ubsan sl_mkR_of). *)
Lemma a4_mkR_of : forall regs,
  Regs6ss.mkR_of regs =
  mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7)
      (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14)
      (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
      (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28)
      (getr regs 29) (getr regs 30) (getr regs 31).
Proof. intros regs. reflexivity. Qed.

(* The size test 0x81424 `srli a1,s2,0x1a` / 0x8144c `beqz a1`: a1 = 0 exactly when n < 2 ^ 26. *)
Lemma a4_cond_lt : forall u, 0 <= u < 2 ^ 26 ->
  bv_eqb (Z_to_bv 64 (Z.shiftr u 26)) (Z_to_bv 64 0) = true.
Proof.
  intros u Hu. unfold bv_eqb. rewrite Z.shiftr_div_pow2 by lia.
  rewrite Z.div_small by lia. apply Z.eqb_refl.
Qed.

Lemma a4_cond_ge : forall u, 2 ^ 26 <= u < 2 ^ 64 ->
  bv_eqb (Z_to_bv 64 (Z.shiftr u 26)) (Z_to_bv 64 0) = false.
Proof.
  intros u Hu. unfold bv_eqb. rewrite Z.shiftr_div_pow2 by lia.
  assert (Hq : 1 <= u / 2 ^ 26).
  { rewrite <- (Z.div_same (2 ^ 26)) by lia. apply Z.div_le_mono; lia. }
  assert (Hq2 : u / 2 ^ 26 < 2 ^ 64).
  { apply Z.div_lt_upper_bound; [lia|]. assert (2 ^ 64 <= 2 ^ 64 * 2 ^ 26) by nia. lia. }
  rewrite (MState.unsigned_lit (u / 2 ^ 26)) by lia.
  change (bv_unsigned (Z_to_bv 64 0)) with 0. apply Z.eqb_neq. lia.
Qed.

(* One cell of a block of cells, read as a byte block at its own offset. *)
Lemma a4_cell_bytes : forall m A cs k c bs,
  rw_cells rsegs m A cs -> cell_at cs k = Some c -> cbytes c = bs ->
  bytes_at rsegs m (A + Z.of_nat k) bs.
Proof.
  intros m A cs k c bs [[Hwf Hb] _] Hat <-.
  destruct (cell_at_split cs k c c Hat) as (pre & post & -> & Hsz & _).
  apply cells_wf_app in Hwf. destruct Hwf as [Hwfp Hwfc]. cbn in Hwfc. destruct Hwfc as [Hwfc Hwfs].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb. destruct Hb as [_ Hb].
  rewrite (cells_bytes_length pre Hwfp), Hsz in Hb.
  cbn [cells_bytes] in Hb. apply bytes_at_app in Hb. exact (proj1 Hb).
Qed.

(* A register value of the run against its closed form. *)
Local Ltac a4_bv :=
  first [ reflexivity
        | apply bv_eq; rewrite ?Z_to_bv_unsigned; unfold bv_wrap; cbn; lia
        | apply bv_eq; rewrite ?Z_to_bv_unsigned; unfold bv_wrap; cbn; Z.div_mod_to_equations; lia ].

(* A word (or byte) of the run, read off the block FR at byte offset k. *)
Local Ltac a4_spill FR k :=
  apply (a4_cell_bytes _ _ _ k _ _ FR ltac:(cells_cbv; reflexivity));
  first [ reflexivity
        | cbn [cbytes]; f_equal; apply bv_eq; rewrite ?Z_to_bv_unsigned; unfold bv_wrap; cbn; lia
        | cbn [cbytes]; f_equal; apply bv_eq; rewrite ?Z_to_bv_unsigned; unfold bv_wrap; cbn;
          Z.div_mod_to_equations; lia ].

(* The same, with k read off the goal's address `bv_unsigned s + off` (the block FR starts at s + base). *)
Local Ltac a4_at FR base :=
  lazymatch goal with
  | |- bytes_at _ _ (bv_unsigned ?s + ?off) _ =>
      let k := eval vm_compute in (Z.to_nat (off - base)) in
      let kz := eval vm_compute in (Z.of_nat k) in
      replace (bv_unsigned s + off) with (bv_unsigned s + base + Z.of_nat k)
        by (change (Z.of_nat k) with kz; lia);
      a4_spill FR k
  end.

(* The run of the segment (v1.9 0x81220 .. 0x81544). s3 (reg 19) = S(fr), s1 (reg 9) = A, s2 (reg 18) = n, s9
   (reg 25) = fr. The 137 shadow bytes [s3 + 255, s3 + 392) and the 264 spill bytes [s1 + 56, s1 + 320) are the
   whole write set; the shadow block lies below the spill block (the shadow map is below HighMem, the spill base is
   the real stack). On the fall-through the loop registers of turn 0 are set: a0 = 6 (0x814b0), a1 = 1 (0x81540),
   a2 = s9 + 2624 (0x814f4, a3 = s9 + 2176 from 0x814ac / 0x814b4), a6 = s9 + 32 (0x81454), a7 = s9 + 64
   (0x81458) and s4 = s9 + 2656 (0x814f8); the shadow byte s3 + 328 is 6 (0x814b8); and the spills of LOOPB
   ([s1 + 144 / 112 / 312 / 264 / 56 / 184 / 176 / 208 / 96 / 120 / 240 / 232 / 224 / 64] = s9 + 2176 / 2256 / 544 /
   2624 / 3040 / 2368 / 2688 / 2768 / 2560 / 2528 / 2448 / 2464 / 2496 / 3056) and of PRA ([s1 + 136 / 280 / 168 /
   192 / 200 / 216 / 104 / 288 / 296 / 304] = s9 + 160 / 176 / 2880 / 528 / 336 / 448 / 128 / 256 / 304 / 272),
   stored at 0x81460-0x81544. s2, s6, s9 and s11 are not written. *)
Lemma a4_evt :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (junk1 junk2 : list byte),
    rw_cells rsegs m (bv_unsigned s3 + 255) [CB 137 junk1] ->
    rw_cells rsegs m (bv_unsigned s1 + 56) [CB 264 junk2] ->
    bv_unsigned s3 + 392 <= bv_unsigned s1 + 56 ->
    evt rsegs
      (fun ms' => exists (a0' a1' a2' a3' a6' a7' s4' pc' : word) (m' : word -> option byte) (cs1 cs2 : list cell),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4 a5 a6' a7' s2 s3 s4' s5 s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6)
                  F pc' fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned s3 + 255, bv_unsigned s3 + 392); (bv_unsigned s1 + 56, bv_unsigned s1 + 320)] m m' /\
         wmono rsegs m m' /\
         rw_cells rsegs m' (bv_unsigned s3 + 255) cs1 /\ cells_size cs1 = 137%nat /\
         rw_cells rsegs m' (bv_unsigned s1 + 56) cs2 /\ cells_size cs2 = 264%nat /\
         ((pc' = Z_to_bv 64 0x82f2c /\ 2 ^ 26 <= bv_unsigned s2) \/
          (pc' = Z_to_bv 64 0x81548 /\ bv_unsigned s2 < 2 ^ 26 /\
           bytes_at rsegs m' (bv_unsigned s3 + 328) [Z_to_bv 8 6] /\
           s4' = Z_to_bv 64 (bv_unsigned s9 + 2656) /\
           a0' = Z_to_bv 64 6 /\ a1' = Z_to_bv 64 1 /\ a2' = Z_to_bv 64 (bv_unsigned s9 + 2624) /\
           a6' = Z_to_bv 64 (bv_unsigned s9 + 32) /\ a7' = Z_to_bv 64 (bv_unsigned s9 + 64) /\
           bytes_at rsegs m' (bv_unsigned s1 + 144) (le8 (Z_to_bv 64 (bv_unsigned s9 + 2176))) /\
           bytes_at rsegs m' (bv_unsigned s1 + 112) (le8 (Z_to_bv 64 (bv_unsigned s9 + 2256))) /\
           bytes_at rsegs m' (bv_unsigned s1 + 312) (le8 (Z_to_bv 64 (bv_unsigned s9 + 544))) /\
           bytes_at rsegs m' (bv_unsigned s1 + 264) (le8 (Z_to_bv 64 (bv_unsigned s9 + 2624))) /\
           bytes_at rsegs m' (bv_unsigned s1 + 56) (le8 (Z_to_bv 64 (bv_unsigned s9 + 3040))) /\
           bytes_at rsegs m' (bv_unsigned s1 + 184) (le8 (Z_to_bv 64 (bv_unsigned s9 + 2368))) /\
           bytes_at rsegs m' (bv_unsigned s1 + 176) (le8 (Z_to_bv 64 (bv_unsigned s9 + 2688))) /\
           bytes_at rsegs m' (bv_unsigned s1 + 208) (le8 (Z_to_bv 64 (bv_unsigned s9 + 2768))) /\
           bytes_at rsegs m' (bv_unsigned s1 + 96) (le8 (Z_to_bv 64 (bv_unsigned s9 + 2560))) /\
           bytes_at rsegs m' (bv_unsigned s1 + 120) (le8 (Z_to_bv 64 (bv_unsigned s9 + 2528))) /\
           bytes_at rsegs m' (bv_unsigned s1 + 240) (le8 (Z_to_bv 64 (bv_unsigned s9 + 2448))) /\
           bytes_at rsegs m' (bv_unsigned s1 + 232) (le8 (Z_to_bv 64 (bv_unsigned s9 + 2464))) /\
           bytes_at rsegs m' (bv_unsigned s1 + 224) (le8 (Z_to_bv 64 (bv_unsigned s9 + 2496))) /\
           bytes_at rsegs m' (bv_unsigned s1 + 64) (le8 (Z_to_bv 64 (bv_unsigned s9 + 3056))) /\
           bytes_at rsegs m' (bv_unsigned s1 + 136) (le8 (Z_to_bv 64 (bv_unsigned s9 + 160))) /\
           bytes_at rsegs m' (bv_unsigned s1 + 280) (le8 (Z_to_bv 64 (bv_unsigned s9 + 176))) /\
           bytes_at rsegs m' (bv_unsigned s1 + 168) (le8 (Z_to_bv 64 (bv_unsigned s9 + 2880))) /\
           bytes_at rsegs m' (bv_unsigned s1 + 192) (le8 (Z_to_bv 64 (bv_unsigned s9 + 528))) /\
           bytes_at rsegs m' (bv_unsigned s1 + 200) (le8 (Z_to_bv 64 (bv_unsigned s9 + 336))) /\
           bytes_at rsegs m' (bv_unsigned s1 + 216) (le8 (Z_to_bv 64 (bv_unsigned s9 + 448))) /\
           bytes_at rsegs m' (bv_unsigned s1 + 104) (le8 (Z_to_bv 64 (bv_unsigned s9 + 128))) /\
           bytes_at rsegs m' (bv_unsigned s1 + 288) (le8 (Z_to_bv 64 (bv_unsigned s9 + 256))) /\
           bytes_at rsegs m' (bv_unsigned s1 + 296) (le8 (Z_to_bv 64 (bv_unsigned s9 + 304))) /\
           bytes_at rsegs m' (bv_unsigned s1 + 304) (le8 (Z_to_bv 64 (bv_unsigned s9 + 272))))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81220) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m junk1 junk2 FRsh FRsp HD.
  pose proof (munch_refl [(bv_unsigned s3 + 255, bv_unsigned s3 + 392);
                          (bv_unsigned s1 + 56, bv_unsigned s1 + 320)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 s3) as R3. change (bv_modulus 64) with (2^64) in R3.
  pose proof (bv_unsigned_in_range 64 s1) as R1. change (bv_modulus 64) with (2^64) in R1.
  pose proof (bv_unsigned_in_range 64 s2) as R2. change (bv_modulus 64) with (2^64) in R2.
  pose proof (rw_cells_bound _ _ _ _ FRsh) as HBsh. cbn [cells_size csize Nat.add] in HBsh.
  pose proof (rw_cells_bound _ _ _ _ FRsp) as HBsp. cbn [cells_size csize Nat.add] in HBsp.
  (* 0x81220-0x8141c: 128 shadow stores; 0x81420 li a0,-13; 0x81424 srli a1,s2,26; 0x81428-0x81448: 9 more *)
  do 139 step.
  destruct (Z_lt_ge_dec (bv_unsigned s2) (2 ^ 26)) as [Hlt|Hge].
  - (* 0x8144c beqz a1 taken; 0x81454-0x81544 *)
    step. if_true_by (a4_cond_lt (bv_unsigned s2) ltac:(lia)).
    do 61 step.
    apply evt_done. cbn beta.
    eexists _, _, _, _, _, _, _, _, _, _, _.
    split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|].
    split; [exact FRsh|]. split; [cbn [cells_size csize]; reflexivity|].
    split; [exact FRsp|]. split; [cbn [cells_size csize]; reflexivity|].
    right. split; [reflexivity|]. split; [exact Hlt|].
    split; [a4_at FRsh 255|].
    do 6 (split; [a4_bv|]).
    do 23 (split; [a4_at FRsp 56|]).
    a4_at FRsp 56.
  - (* 0x8144c beqz a1 not taken; 0x81450 j 0x82f2c *)
    step. if_false_by (a4_cond_ge (bv_unsigned s2) ltac:(lia)).
    step.
    apply evt_done. cbn beta.
    eexists _, _, _, _, _, _, _, _, _, _, _.
    split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|].
    split; [exact FRsh|]. split; [cbn [cells_size csize]; reflexivity|].
    split; [exact FRsp|]. split; [cbn [cells_size csize]; reflexivity|].
    left. split; [reflexivity | lia].
Qed.

(* ---- memory helpers ---- *)

(* A sub-range of a byte block. *)
Lemma a4_bytes_mid : forall m a bs k n,
  bytes_at rsegs m a bs -> (k + n <= length bs)%nat ->
  bytes_at rsegs m (a + Z.of_nat k) (firstn n (skipn k bs)).
Proof.
  intros m a bs k n Hb Hkn.
  rewrite <- (firstn_skipn k bs) in Hb.
  apply bytes_at_app in Hb. destruct Hb as [_ Hb].
  rewrite firstn_length_le in Hb by lia.
  rewrite <- (firstn_skipn n (skipn k bs)) in Hb.
  apply bytes_at_app in Hb. exact (proj1 Hb).
Qed.

(* A prefix of a byte block. *)
Lemma a4_bytes_pre : forall m a bs n,
  bytes_at rsegs m a bs -> (n <= length bs)%nat -> bytes_at rsegs m a (firstn n bs).
Proof.
  intros m a bs n Hb Hn. rewrite <- (firstn_skipn n bs) in Hb.
  apply bytes_at_app in Hb. exact (proj1 Hb).
Qed.

(* Every byte of a byte block is present. *)
Lemma a4_pres : forall m a bs x,
  bytes_at rsegs m a bs -> a <= x < a + Z.of_nat (length bs) ->
  exists b, mbyte rsegs m x = Some b.
Proof.
  intros m a bs x Hb Hx. destruct Hb as (H0 & H1 & H).
  assert (Hi : (Z.to_nat (x - a) < length bs)%nat) by lia.
  pose proof (H (Z.to_nat (x - a)) Hi) as E.
  rewrite Z2Nat.id in E by lia. replace (a + (x - a)) with x in E by lia.
  destruct (nth_error bs (Z.to_nat (x - a))) as [b|] eqn:Eb.
  - exists b. unfold mbyte. unfold mrd, wa in E. exact E.
  - apply nth_error_None in Eb. lia.
Qed.

(* A present and writable byte block is a one-cell rw block. *)
Lemma a4_rw_of_bytes : forall m a bs,
  bytes_at rsegs m a bs ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> wview rsegs m (wa x) <> None) ->
  rw_cells rsegs m a [CB (length bs) bs].
Proof.
  intros m a bs Hb Hw. pose proof (bytes_at_bound _ _ _ _ Hb) as (H0 & H1).
  split.
  - split; [cbn; split; [reflexivity | exact I]|].
    cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
  - split; [lia|]. split; [cbn [cells_size csize]; rewrite ?Nat.add_0_r; lia|].
    intros i Hi. cbn [cells_size csize] in Hi. rewrite ?Nat.add_0_r in Hi. apply Hw. lia.
Qed.

(* The same with the cell's length given. *)
Lemma a4_rw_of_bytes_n : forall m a bs n,
  bytes_at rsegs m a bs -> length bs = n ->
  (forall x, a <= x < a + Z.of_nat n -> wview rsegs m (wa x) <> None) ->
  rw_cells rsegs m a [CB n bs].
Proof.
  intros m a bs n Hb Hn Hw. subst n. apply a4_rw_of_bytes; [exact Hb | exact Hw].
Qed.

(* The word at an address determines its value: one side-stack base word for every byte of a frame. *)
Lemma a4_word_uniq : forall m a v w, 0 <= v < 2 ^ 64 -> 0 <= w < 2 ^ 64 ->
  word_mem rsegs m a v -> word_mem rsegs m a w -> v = w.
Proof.
  intros m a v w Hv Hw H1 H2.
  assert (D : forall k, (k < 8)%nat -> le_byte v 8 k = le_byte w 8 k).
  { intros k Hk. pose proof (H1 k Hk) as E1. pose proof (H2 k Hk) as E2.
    rewrite E1 in E2.
    assert (E : Z_to_bv 8 (le_byte v 8 k) = Z_to_bv 8 (le_byte w 8 k)) by congruence.
    transitivity (bv_unsigned (Z_to_bv 8 (le_byte v 8 k))); [symmetry; apply kb_byte_unsigned|].
    rewrite E. apply kb_byte_unsigned. }
  rewrite (kb_le8_digits v Hv), (kb_le8_digits w Hw).
  rewrite (D 0%nat ltac:(lia)), (D 1%nat ltac:(lia)), (D 2%nat ltac:(lia)), (D 3%nat ltac:(lia)),
          (D 4%nat ltac:(lia)), (D 5%nat ltac:(lia)), (D 6%nat ltac:(lia)), (D 7%nat ltac:(lia)).
  reflexivity.
Qed.

(* Every byte of the image lies below 6283264 (GT, the end of its writable data rounded up to a page). *)
Lemma a4_img_low : forall s, In s rsegs -> Z.of_N (seg_base s) + Z.of_N (seg_size s) <= 6283264.
Proof.
  intros s Hin.
  assert (Hb : forallb (fun s => Z.leb (Z.of_N (seg_base s) + Z.of_N (seg_size s)) 6283264) rsegs = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in Hb. apply Z.leb_le. exact (Hb s Hin).
Qed.

(* A read-only address of the image is one of those bytes. *)
Lemma a4_ro_low : forall a, ro_addr rsegs a = true -> bv_unsigned a < 6283264.
Proof.
  intros a Ha. unfold ro_addr in Ha.
  destruct (find_segment rsegs (bv_unsigned a) 1) as [s|] eqn:Es; [|discriminate].
  destruct (KindBGlue.kb_find_segment rsegs (bv_unsigned a) 1 s Es) as (Hin & H1 & H2).
  pose proof (a4_img_low s Hin). lia.
Qed.

(* The registered globals are image bytes too. *)
Lemma a4_ag_low : forall a, in_globals AF.frame_AG a -> 0 <= a < 6283264.
Proof.
  intros a (lo & len & Hin & Hr).
  assert (Hb : forallb (fun p => andb (Z.leb 0 (fst p)) (Z.leb (fst p + snd p) 6283264)) AF.frame_AG = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in Hb. pose proof (Hb (lo, len) Hin) as Hp. cbn in Hp.
  apply andb_true_iff in Hp. destruct Hp as [Hp1 Hp2]. apply Z.leb_le in Hp1. apply Z.leb_le in Hp2. lia.
Qed.

(* A read through a cell the run did not change. *)
Lemma a4_mrd_eq : forall m m' (a : word) b, m' a = m a -> mrd rsegs m a = Some b -> mrd rsegs m' a = Some b.
Proof. intros m m' a b E H. unfold mrd in *. rewrite E. exact H. Qed.

(* A byte off the frame has its shadow byte off the frame's 392 (the frame covers whole granules). *)
Lemma a4_shadow_off : forall fr b, fr mod 8 = 0 -> 0 <= fr -> 0 <= b -> ~ (fr <= b < fr + 3136) ->
  ~ (Sfr fr <= shadow_addr b < Sfr fr + 392).
Proof.
  intros fr b Hfr8 Hfr0 Hb0 Hnb Hin. apply Hnb. unfold Sfr, shadow_addr in Hin.
  Z.div_mod_to_equations. lia.
Qed.

(* our[]'s 6 bytes at fr + 2624 (fr mod 8 = 0) are addressable once their one shadow byte S(fr) + 328 is 6:
   the granule fr + 2624 .. fr + 2631 has its first 6 bytes addressable (offset i < 6). *)
Lemma a4_our_addr : forall m fr, 0 <= fr -> fr mod 8 = 0 -> fr + 2630 <= APPMEM_END ->
  (forall i, 0 <= i < 6 -> app_mem (fr + 2624 + i)) ->
  bytes_at rsegs m (Sfr fr + 328) [Z_to_bv 8 6] -> addressable m (fr + 2624) 6.
Proof.
  intros m fr H0 H8 He Happ (_ & _ & H).
  split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. split; [exact (Happ i Hi)|]. exists (Z_to_bv 8 6). split.
  - assert (Hs : shadow_addr (fr + 2624 + i) = Sfr fr + 328)
      by (unfold Sfr, shadow_addr; Z.div_mod_to_equations; lia).
    rewrite Hs. pose proof (H 0%nat ltac:(cbn; lia)) as E. cbn [Z.of_nat nth_error] in E.
    rewrite Z.add_0_r in E. exact E.
  - right. assert (Hb : bv_signed (Z_to_bv 8 6) = 6) by reflexivity. rewrite Hb.
    assert (Hm : (fr + 2624 + i) mod 8 = i) by (Z.div_mod_to_equations; lia). lia.
Qed.

Section A4.
Context {fx : YK11.FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

(* The heap invariant survives a run whose writes are the frame's shadow bytes [S(fr), S(fr) + 392) and app
   bytes of the real stack [P, Q): a shadow byte is the metadata byte of a frame byte (a_store_ok's fourth
   disjunct on the real arm, the side stack's Shadow on the side arm) and an app byte is above stklo (its
   second disjunct). The side stack's metadata cells are app bytes below stklo, so outside both. *)
Lemma a4_AH : forall (H : list (Z * Z)) (mem mem' : word -> option byte) (md : Model) (fr P Q : Z)
                     (W : list Frame.ivl),
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  Frame.munch W mem mem' -> Frame.wmono rsegs mem mem' ->
  ((forall a, fr <= a < fr + 3136 ->
      AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md <= a < APPMEM_END) \/
   (forall a, fr <= a < fr + 3136 -> AC.a_in_fs AC.ASYMS mem a)) ->
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md <= P -> Q <= APPMEM_END ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x ->
     (exists k, 0 <= k < 392 /\ x = Sfr fr + k) \/ P <= x < Q) ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x -> exists b, mbyte rsegs mem' x = Some b) ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem' md /\
  (forall a, AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem' md a <->
             AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem md a) /\
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md =
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md =
  AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md.
Proof.
  intros H mem mem' md fr P Q W HAH MU WM Hloc HP HQ HW HPres.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as laws.
  assert (Hsh : forall k, 0 <= k < 392 -> Sfr fr + k = shadow_addr (fr + 8 * k)).
  { intros k Hk. unfold Sfr, shadow_addr.
    replace (fr + 8 * k) with (fr + k * 8) by lia. rewrite Z.div_add by lia. lia. }
  assert (Hwr : forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a)
    by (intros a Ha Hw; exact (WM (Z_to_bv 64 a) Hw)).
  destruct Hloc as [Hreal|Hfs].
  - assert (Hagree : forall a, 0 <= a < 2 ^ 64 ->
      ~ AC.a_store_ok H (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
      mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
    { intros a Ha Hns.
      destruct (KindBGlue.kb_outside_dec W a) as [Ho|Ho].
      - apply MU. rewrite MState.unsigned_lit by exact Ha. exact Ho.
      - exfalso. apply Hns. destruct (HW a Ha Ho) as [(k & Hk & Heq)|Hin].
        + right. right. right. exists (fr + 8 * k). split; [rewrite Heq; exact (Hsh k Hk)|].
          right. left. apply Hreal. lia.
        + right. left. lia. }
    destruct (lw_store _ H mem mem' md HAH Hagree Hwr) as [L1 L2 L3 L4].
    exact (conj L1 (conj L2 (conj L3 L4))).
  - destruct (Hfs fr ltac:(lia)) as (FS & HFS64 & Hwm & Hrng).
    assert (Hfrend : fr + 3136 <= FS + AC.FS_SIZE).
    { destruct (Hfs (fr + 3135) ltac:(lia)) as (FS' & HFS64' & Hwm' & Hrng').
      assert (FS' = FS) by exact (a4_word_uniq mem (AC.as_tp AC.ASYMS) FS' FS HFS64' HFS64 Hwm' Hwm).
      lia. }
    destruct (lw_fs_place _ H mem md FS HAH Hwm HFS64) as [Hgt Hfslo _ Hfsapp].
    assert (HFSend : FS + AC.FS_SIZE <= APPMEM_END).
    { pose proof (Hfsapp (FS + AC.FS_SIZE - 1) ltac:(unfold AC.FS_SIZE; lia)) as Hap.
      unfold app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG in Hap |- *. unfold AC.FS_SIZE in *. lia. }
    assert (Hframe_app : forall a, fr <= a < fr + 3136 -> app_mem a)
      by (intros a Ha; apply Hfsapp; unfold AC.FS_SIZE in *; lia).
    assert (HFSmeta : forall q, Tac_fs.fs_meta FS q -> Frame.outside W q).
    { intros q Hm. pose proof (Tac_fs.fs_meta_below FS q Hm) as Hqhi.
      assert (Hqlo : FS <= q).
      { unfold Tac_fs.fs_meta in Hm.
        destruct Hm as [Hc | [Hc | [ (c & Hc & Hr) | (c & j & Hc & Hj & Heq) ]]].
        - lia.
        - lia.
        - unfold AC.a_fs_hint in Hr. lia.
        - subst q. exact (proj1 (Tac_fs.a_fs_flag_range FS c j Hc Hj)). }
      assert (Hqapp : app_mem q) by (apply Hfsapp; unfold AC.FS_SIZE in *; lia).
      assert (Hq64 : 0 <= q < 2 ^ 64)
        by (unfold app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG in Hqapp; lia).
      destruct (KindBGlue.kb_outside_dec W q) as [Ho|Ho]; [exact Ho|exfalso].
      destruct (HW q Hq64 Ho) as [(k & Hk & Heq)|Hin].
      - apply (app_not_shadow q Hqapp). rewrite Heq, (Hsh k Hk). apply shadow_of_app.
        apply Hframe_app. lia.
      - unfold AC.FS_SIZE in *. lia. }
    assert (Hagree : forall q, 0 <= q < 2 ^ 64 ->
      ~ AC.a_store_ok H (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) q ->
      ~ (FS <= q < FS + AC.FS_SIZE) ->
      ~ (exists b, FS <= b < FS + AC.FS_SIZE /\ q = shadow_addr b) ->
      mem' (Z_to_bv 64 q) = mem (Z_to_bv 64 q)).
    { intros q Hq Hns Hnfs Hnsh.
      destruct (KindBGlue.kb_outside_dec W q) as [Ho|Ho].
      - apply MU. rewrite MState.unsigned_lit by exact Hq. exact Ho.
      - exfalso. destruct (HW q Hq Ho) as [(k & Hk & Heq)|Hin].
        + apply Hnsh. exists (fr + 8 * k). split; [lia | rewrite Heq; exact (Hsh k Hk)].
        + apply Hns. right. left. lia. }
    assert (HPresG : forall q, 0 <= q < 2 ^ 64 -> (exists b, mbyte rsegs mem q = Some b) ->
                       exists b, mbyte rsegs mem' q = Some b).
    { intros q Hq Hp. destruct (KindBGlue.kb_outside_dec W q) as [Ho|Ho].
      - rewrite (KindBGlue.mbyte_munch rsegs W mem mem' q MU Hq Ho). exact Hp.
      - exact (HPres q Hq Ho). }
    exact (Tac_fs.a_fs_ok_store_AH AC.ASYMS _ _ _ _ W H mem mem' md FS laws HAH Hwm HFS64
                ltac:(unfold APPMEM_END in HFSend; lia) MU Hwr HPresG HFSmeta Hagree).
Qed.

(* FRAH survives the A4 run. The write set W is the frame's shadow tail [S(fr) + 255, S(fr) + 392) and the spill
   bytes [A + 56, A + 320): the runtime's metadata map is rebuilt from the caller's new 392-byte shadow list
   (RT_meta_write); the slot window holds W's bytes again (the caller's presence fact); the frame header, the fr
   spill, the saved caller registers, the sink words, RELRO, the runtime's cells and the registered globals'
   metadata bytes all lie outside W (the frame body ends at or below A, the shadow map is below HighMem, the
   image is below GT <= fr). *)
Lemma a4_frah : forall g fr hb regs regs' mem mem' md sel hdr (W : list Frame.ivl),
  FRAH B APIf ra g fr hb regs mem md sel hdr ->
  Frame.munch W mem mem' -> Frame.wmono rsegs mem mem' -> rt_disjoint W ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md ->
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md =
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md ->
  (forall A, getr regs 9 = Z_to_bv 64 A -> 0 <= A < 2 ^ 64 -> forall x, 0 <= x < 2 ^ 64 ->
     ~ Frame.outside W x -> (Sfr fr + 255 <= x < Sfr fr + 392) \/ (A + 56 <= x < A + 320)) ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x -> exists b, mbyte rsegs mem' x = Some b) ->
  (exists sh, bytes_at rsegs mem' (Sfr fr) sh /\ length sh = 392%nat) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  FRAH B APIf ra g fr hb regs' mem' md sel hdr.
Proof.
  intros g fr hb regs regs' mem mem' md sel hdr W HF MU WM HD HAH' HSTK HW HPres Hsh'
    E2 E3 E4 E8 E9 E19 E26.
  pose proof FF as (SEGS & _ & _ & _ & Hhead & Hlock & Hthr & _).
  destruct HF as (A & sp & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hsel0 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWin2 & HShi1 & HShi2 & HShi3 &
    Hhb & Hlive & Hinb & Hinblk).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  pose proof FRAME_BYTES_val as HFBv.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc))
                (hb ++ g_H g) mem md HAH) as Hhm.
  assert (HAhm : HIGHMEM_BEG <= A) by lia.
  assert (HA64 : 0 <= A < 2 ^ 64) by (unfold HIGHMEM_BEG in HAhm; unfold APPMEM_END in HAPP; lia).
  pose proof (HW A Hr9 HA64) as HWA.
  assert (HAapp : forall x, A <= x < g_S g -> app_mem x) by (intros x Hx; unfold app_mem; right; lia).
  assert (Hfrapp : forall a, fr <= a < fr + 3136 -> app_mem a).
  { pose proof Hloc as Hl2. destruct Hl2 as [[_ [_ Hreal]]|[_ [_ [Hfs _]]]].
    - intros a Ha. unfold app_mem. right. pose proof (Hreal a Ha). lia.
    - intros a Ha. destruct (Hfs a Ha) as (b & Hb64 & Hwm & Hlo & Hhi).
      destruct (lw_fs_place _ (hb ++ g_H g) mem md b HAH Hwm Hb64) as [_ _ _ Happ].
      apply Happ. lia. }
  assert (Hgt : AC.GT <= fr).
  { pose proof Hloc as Hl2. destruct Hl2 as [[_ [_ Hreal]]|[_ [Hfsb [Hfs _]]]].
    - pose proof (Hreal fr ltac:(lia)). unfold AC.GT. unfold HIGHMEM_BEG in Hhm. lia.
    - destruct (Hfs fr ltac:(lia)) as (b & Hb64 & Hwm & Hlo & Hhi).
      destruct (lw_fs_place _ (hb ++ g_H g) mem md b HAH Hwm Hb64) as [Hgt _ _ _].
      pose proof (Hfsb b Hwm Hb64). lia. }
  assert (Hfr8 : fr mod 8 = 0) by (pose proof (Z.mod_eq fr 32 ltac:(lia)) as X; rewrite Hfrm in X;
                                   replace fr with ((4 * (fr / 32)) * 8) by lia; apply Z_mod_mult).
  assert (HshIS : forall x, Sfr fr <= x < Sfr fr + 392 -> in_shadow x).
  { intros x Hx.
    assert (Hdiv : (fr + 8 * (x - Sfr fr)) / 8 = fr / 8 + (x - Sfr fr)).
    { replace (8 * (x - Sfr fr)) with ((x - Sfr fr) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
    assert (Hin : fr <= fr + 8 * (x - Sfr fr) < fr + 3136) by lia.
    pose proof (shadow_of_app (fr + 8 * (x - Sfr fr)) (Hfrapp _ Hin)) as His.
    replace (shadow_addr (fr + 8 * (x - Sfr fr))) with x in His; [exact His|].
    unfold shadow_addr. rewrite Hdiv. unfold Sfr, shadow_addr. lia. }
  assert (HSfrlo : 785408 + ASAN_K <= Sfr fr).
  { unfold Sfr, shadow_addr. unfold AC.GT in Hgt.
    assert (785408 <= fr / 8) by (replace 785408 with (6283264 / 8) by reflexivity; apply Z.div_le_mono; lia).
    lia. }
  assert (Hout : forall x, app_mem x -> ~ (A + 56 <= x < A + 320) -> Frame.outside W x).
  { intros x Hap Hnb. destruct (KindBGlue.kb_outside_dec W x) as [Ho|Ho]; [exact Ho|exfalso].
    assert (Hx64 : 0 <= x < 2 ^ 64)
      by (unfold app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG in Hap; destruct Hap; lia).
    destruct (HWA x Hx64 Ho) as [Hin|Hin]; [|lia].
    exact (app_not_shadow x Hap (HshIS x ltac:(lia))). }
  assert (KBmb : forall sg x, app_mem x -> ~ (A + 56 <= x < A + 320) -> mbyte sg mem' x = mbyte sg mem x).
  { intros sg x Hap Hnb.
    assert (Hx64 : 0 <= x < 2 ^ 64)
      by (unfold app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG in Hap; destruct Hap; lia).
    assert (Hm : mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x))
      by (apply MU; rewrite MState.unsigned_lit by exact Hx64; exact (Hout x Hap Hnb)).
    unfold mbyte. rewrite Hm. reflexivity. }
  assert (Houtlo : forall x, 0 <= x -> x < 6283264 -> Frame.outside W x).
  { intros x H0 H1. apply Hout; [unfold app_mem, LOWMEM_END; left; lia|].
    unfold HIGHMEM_BEG in HAhm. lia. }
  assert (KBlo : forall sg x, 0 <= x -> x < 6283264 -> mbyte sg mem' x = mbyte sg mem x).
  { intros sg x H0 H1. apply KBmb; [unfold app_mem, LOWMEM_END; left; lia|].
    unfold HIGHMEM_BEG in HAhm. lia. }
  assert (HAGout : forall x, 0 <= x <= 785407 + ASAN_K -> Frame.outside W x).
  { intros x Hx. destruct (KindBGlue.kb_outside_dec W x) as [Ho|Ho]; [exact Ho|exfalso].
    assert (Hx64 : 0 <= x < 2 ^ 64) by (unfold ASAN_K in *; lia).
    destruct (HWA x Hx64 Ho) as [Hin|Hin]; [lia|].
    unfold HIGHMEM_BEG in HAhm. unfold ASAN_K in Hx. lia. }
  assert (HRO : ro_agree rsegs mem').
  { apply (ro_agree_same rsegs mem mem' Hro). intros a Ha. pose proof (a4_ro_low a Ha) as Hb.
    pose proof (bv_unsigned_in_range 64 a) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
    apply MU. apply Houtlo; lia. }
  assert (HshR : forall a, in_shadow a -> exists b, mrd rsegs mem' (wa a) = Some b).
  { intros a Hin.
    pose proof (in_shadow_range a Hin) as Har.
    destruct (Z_le_gt_dec (Sfr fr + 255) a) as [Hge|Hlt];
      [destruct (Z_lt_ge_dec a (Sfr fr + 392)) as [Hlt2|Hge2]|].
    - destruct Hsh' as (sh2 & (Hb0 & Hb1 & Hb2) & Hl).
      assert (Hj : (Z.to_nat (a - Sfr fr) < length sh2)%nat) by (rewrite Hl; lia).
      pose proof (Hb2 (Z.to_nat (a - Sfr fr)) Hj) as HmE.
      rewrite Z2Nat.id in HmE by lia. replace (Sfr fr + (a - Sfr fr)) with a in HmE by lia.
      destruct (nth_error sh2 (Z.to_nat (a - Sfr fr))) as [b|] eqn:Eb; [exists b; exact HmE|].
      exfalso. apply nth_error_None in Eb. rewrite Hl in Eb. lia.
    - assert (Ho : Frame.outside W a).
      { destruct (KindBGlue.kb_outside_dec W a) as [Ho|Ho]; [exact Ho|exfalso].
        destruct (HWA a ltac:(lia) Ho) as [Hin2|Hin2]; [lia|].
        exact (app_not_shadow a (HAapp a ltac:(lia)) Hin). }
      destruct (AsanRTInv.RT_shadow_rw sp mem md HRT a Hin) as (_ & b & Hmr).
      assert (Hmem : mem' (wa a) = mem (wa a))
        by (apply MU; rewrite Mem.wa_unsigned by lia; exact Ho).
      exists b. unfold mrd in *. rewrite Hmem. exact Hmr.
    - assert (Ho : Frame.outside W a).
      { destruct (KindBGlue.kb_outside_dec W a) as [Ho|Ho]; [exact Ho|exfalso].
        destruct (HWA a ltac:(lia) Ho) as [Hin2|Hin2]; [lia|].
        exact (app_not_shadow a (HAapp a ltac:(lia)) Hin). }
      destruct (AsanRTInv.RT_shadow_rw sp mem md HRT a Hin) as (_ & b & Hmr).
      assert (Hmem : mem' (wa a) = mem (wa a))
        by (apply MU; rewrite Mem.wa_unsigned by lia; exact Ho).
      exists b. unfold mrd in *. rewrite Hmem. exact Hmr. }
  exists A, sp.
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
      destruct Hil as [Ei|[]]; injection Ei as <- <-; lia.
    - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
      destruct Hil as [Ei|[]]; injection Ei as <- <-; lia. }
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
  split; [exact Hfrm|].
  split; [exact Hsel0|].
  split; [exact HAm|].
  split; [exact HAS|].
  split; [exact Hspa|].
  split; [exact Hfa|].
  split; [exact HA448|].
  split; [exact HS4|].
  split; [exact HAPP|].
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hspill | exact MU |].
    rewrite length_le8. intros x Hx. apply Hout; [apply HAapp; lia | lia]. }
  split.
  { destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0 [Hfsb [Hfs Hrec]]]].
    - left. split; [exact H0|]. split; [exact Hspfr|].
      intros a Ha. rewrite HSTK. exact (Hreal a Ha).
    - right. split; [exact Hfr0|]. split.
      + intros FS Hw HFSr. apply (Hfsb FS); [| exact HFSr].
        intros k Hk. rewrite <- KBlo.
        * exact (Hw k Hk).
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
      + split.
        * intros a Ha. destruct (Hfs a Ha) as (FSb & HFSr & Hw & Hlo & Hhi).
          exists FSb. split; [exact HFSr|]. split; [|split; [exact Hlo | exact Hhi]].
          intros k Hk. rewrite KBlo.
          -- exact (Hw k Hk).
          -- unfold AC.as_tp, AC.ASYMS. cbn. lia.
          -- unfold AC.as_tp, AC.ASYMS. cbn. lia.
        * (* the frame record: an app byte below stklo is neither a frame shadow byte nor a spill byte
             (Tac_slot's fsrec_keep_app_lo states the UL engine's munch / outside: fr_munch_ul /
             fr_outside_lib convert) *)
          eapply (fsrec_keep_app_lo APIf (hb ++ g_H g) mem mem' md W fr);
            [exact Hrec | exact HAH | exact (proj1 (fr_munch_ul W mem mem') MU) |].
          intros x Hap Hxlo Hxf. apply (proj2 (fr_outside_lib W x)).
          destruct (KindBGlue.kb_outside_dec W x) as [Ho|Ho]; [exact Ho|exfalso].
          assert (Hx64 : 0 <= x < 2 ^ 64)
            by (unfold app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG in Hap; destruct Hap; lia).
          destruct (HWA x Hx64 Ho) as [Hin|Hin].
          -- exact (app_not_shadow x Hap (HshIS x ltac:(lia))).
          -- lia. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr1 | exact MU |].
    rewrite length_le8. intros x Hx. apply Hout; [apply Hfrapp; lia | lia]. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr2 | exact MU |].
    rewrite length_le8. intros x Hx. apply Hout; [apply Hfrapp; lia | lia]. }
  split; [destruct Hsh' as (sh2 & Hb2 & Hl2); exists sh2; split; [exact Hb2 | rewrite FRAME_SHADOW_val; exact Hl2]|].
  split.
  { destruct Hwin as (Hw0 & Hw1 & Hwv). split; [exact Hw0|]. split; [exact Hw1|].
    intros x Hx. destruct (Hwv x Hx) as (Hwx & b & Hb). split; [exact (WM (wa x) Hwx)|].
    destruct (KindBGlue.kb_outside_dec W x) as [Ho|Ho].
    - exists b. apply (a4_mrd_eq mem mem' (wa x) b); [|exact Hb].
      apply MU. rewrite Mem.wa_unsigned by lia. exact Ho.
    - destruct (HPres x ltac:(lia) Ho) as (b' & Hb'). exists b'. exact Hb'. }
  split.
  { eapply fl_bytes; [exact Hsaved | exact MU |]. intros x Hx.
    unfold saved_bytes in Hx. rewrite !length_app, !length_le8 in Hx. cbn in Hx.
    apply Hout; [unfold app_mem; right; lia | lia]. }
  split.
  { intros a Ha. exact (WM (Z_to_bv 64 a) (Herrno a Ha)). }
  split.
  { intros a Hin. pose proof (a4_ag_low a Hin) as Halo.
    destruct (HAG a Hin) as (H0 & H1 & H2 & H3). split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
    intros i Hi. destruct (H3 i Hi) as (Hap & b & Hb & Hok).
    split; [exact Hap|]. exists b. split; [|exact Hok].
    assert (Hsa : 0 <= shadow_addr (a + i) <= 785407 + ASAN_K).
    { unfold shadow_addr. split.
      - assert (0 <= (a + i) / 8) by (apply Z.div_pos; lia). unfold ASAN_K. lia.
      - assert ((a + i) / 8 <= 785407)
          by (replace 785407 with ((6283264 - 1) / 8) by reflexivity; apply Z.div_le_mono; lia).
        lia. }
    assert (Hm : mem' (wa (shadow_addr (a + i))) = mem (wa (shadow_addr (a + i)))).
    { apply MU. rewrite Mem.wa_unsigned by (unfold ASAN_K in Hsa; lia). exact (HAGout _ Hsa). }
    exact (a4_mrd_eq mem mem' _ b Hm Hb). }
  split.
  { intros a Ha Hnfr.
    pose proof (HWin2 a Ha Hnfr) as Hada.
    pose proof (addr1_app mem a Hada) as Happa.
    apply (addr1_munch W mem mem' a MU); [| exact Hada].
    assert (Ha0 : 0 <= a) by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Happa; lia).
    pose proof (shadow_of_app a Happa) as Hsa.
    pose proof (in_shadow_range (shadow_addr a) Hsa) as Hsr.
    pose proof Hsa as Hsa'.
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hsa'.
    destruct (KindBGlue.kb_outside_dec W (shadow_addr a)) as [Ho|Ho]; [exact Ho|exfalso].
    destruct (HWA (shadow_addr a) ltac:(lia) Ho) as [Hin|Hin].
    - apply (a4_shadow_off fr a Hfr8 ltac:(unfold AC.GT in Hgt; lia) Ha0 Hnfr). lia.
    - unfold HIGHMEM_BEG in HAhm. lia. }
  split; [exact HShi1|].
  split; [exact HShi2|].
  split; [exact HShi3|].
  split; [exact Hhb|].
  split; [exact Hlive|].
  (* the input facts (de2516edf5): for n > 0 the input block is a live entry block, so each of its bytes is
     app memory below stklo <= S - SLOT_STACK < A + 56 and off the frame (real arm: stklo <= fr; side arm: not in
     the FakeStack, which holds the frame); neither it nor its shadow byte is written (fra_in_keep_sh). *)
  apply (fra_in_keep_sh g mem mem' W Hinb Hinblk MU).
  intros x Hx.
  destruct (Hinblk ltac:(lia)) as (Hin & _).
  destruct (lw_blocks _ (hb ++ g_H g) mem md (g_p g) (g_n g) HAH (in_or_app _ _ _ (or_intror Hin)))
    as [_ _ Hend _ Hall].
  destruct (Hall x Hx) as (Happx & _ & _ & _ & Hnfs).
  assert (Hx0 : 0 <= x) by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Happx; lia).
  assert (Hnb : ~ (fr <= x < fr + 3136)).
  { destruct Hloc as [[_ [_ Hreal]]|[_ [_ [Hfs _]]]].
    - pose proof (Hreal fr ltac:(lia)). lia.
    - intro Hf. exact (Hnfs (Hfs x Hf)). }
  split.
  - apply Hout; [exact Happx | lia].
  - pose proof (shadow_of_app x Happx) as Hsx.
    pose proof (in_shadow_range (shadow_addr x) Hsx) as Hsr.
    pose proof Hsx as Hsx'.
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hsx'.
    destruct (KindBGlue.kb_outside_dec W (shadow_addr x)) as [Ho|Ho]; [exact Ho|exfalso].
    destruct (HWA (shadow_addr x) ltac:(lia) Ho) as [Hin2|Hin2].
    + apply (a4_shadow_off fr x Hfr8 ltac:(unfold AC.GT in Hgt; lia) Hx0 Hnb). lia.
    + unfold HIGHMEM_BEG in HAhm. lia.
Qed.

(* FRAH's input facts, projected (SlotInv's fra_in for FRAH). *)
Lemma a4_frah_in : forall g fr hb regs mem md sel hdr,
  FRAH B APIf ra g fr hb regs mem md sel hdr ->
  bytes_at rsegs mem (g_p g) (g_in g) /\
  (0 < g_n g -> In (g_p g, g_n g) (g_H g) /\ addressable mem (g_p g) (g_n g)).
Proof.
  intros g fr hb regs mem md sel hdr HF.
  destruct HF as (A & sp & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hsel0 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWin2 & HShi1 & HShi2 & HShi3 &
    Hhb & Hlive & Hinb & Hinblk).
  split; [exact Hinb | exact Hinblk].
Qed.

(* A4: the 198 instructions v1.9 0x81220 .. 0x81544, over FRAS (the selector sel in s8 = reg 24, not yet spilled).
   The n >= 2 ^ 26 arm ends at the release join (Inv_Jrel, v1.9 pc 0x82f2c); the n < 2 ^ 26 arm reaches the our[]
   loop head at turn t = 0 (Inv_B81548_at g 0, v1.9 pc 0x81548): LOOPB at t = 0 (no OUR byte stored yet) and PRA
   (the stores 0x81460-0x81510). Neither arm writes s9 = fr (reg 25), s8 = sel (reg 24) or s11 = S(fr) + 68
   (reg 27). *)
Lemma seg_A4 :
  Hat B APIf ra (Inv_B81548_at B APIf ra) 0 -> Hcut B APIf ra (Inv_Jrel B APIf ra) -> Hcut B APIf ra (Inv_B81220 B APIf ra).
Proof.
  intros H5 HJ g c HInv.
  pose proof (proj1 FF) as SEGS.
  pose proof FRAME_BYTES_val as HFBv.
  destruct HInv as (regs & mem & md & fr & sel & Ec & HFS & HENT & Hnmax & Hr20 & Hr21 & Hr24 & Hr25 & Hr22 &
                    Hr18 & Hr27).
  subst c.
  rewrite SEGS.
  pose proof HFS as HF0. unfold FRAS in HF0.
  destruct HF0 as (A & sp & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hsel0 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWin2 & HShi1 & HShi2 & HShi3 &
    Hhb & Hlive & _ & _).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc))
                ([] ++ g_H g) mem md HAH) as Hhm.
  assert (HAhm : HIGHMEM_BEG <= A) by lia.
  assert (HA64 : 0 <= A < 2 ^ 64) by (unfold HIGHMEM_BEG in HAhm; unfold APPMEM_END in HAPP; lia).
  assert (HAPPv : APPMEM_END = 140737488355328) by reflexivity.
  assert (HHBv : HIGHMEM_BEG = 17594333495296) by reflexivity.
  assert (Hgt : AC.GT <= fr).
  { pose proof Hloc as Hl2. destruct Hl2 as [[_ [_ Hreal]]|[_ [Hfsb [Hfs _]]]].
    - pose proof (Hreal fr ltac:(lia)). unfold AC.GT. unfold HIGHMEM_BEG in Hhm. lia.
    - destruct (Hfs fr ltac:(lia)) as (b & Hb64 & Hwm & Hlo & Hhi).
      destruct (lw_fs_place _ ([] ++ g_H g) mem md b HAH Hwm Hb64) as [Hgt _ _ _].
      pose proof (Hfsb b Hwm Hb64). lia. }
  assert (Hfr8 : fr mod 8 = 0) by (pose proof (Z.mod_eq fr 32 ltac:(lia)) as X; rewrite Hfrm in X;
                                   replace fr with ((4 * (fr / 32)) * 8) by lia; apply Z_mod_mult).
  (* the segment's two written ranges, as an outside-W test *)
  assert (HW2 : forall x, 0 <= x < 2 ^ 64 -> ~ (Sfr fr + 255 <= x < Sfr fr + 392) ->
            ~ (A + 56 <= x < A + 320) ->
            Frame.outside [(Sfr fr + 255, Sfr fr + 392); (A + 56, A + 320)] x).
  { intros x Hx H1 H2. cbn [Frame.outside]. split; [lia|]. split; [lia | exact I]. }
  assert (Hfrapp : forall a, fr <= a < fr + 3136 -> app_mem a).
  { pose proof Hloc as Hl2. destruct Hl2 as [[_ [_ Hreal]]|[_ [_ [Hfs _]]]].
    - intros a Ha. unfold app_mem. right. pose proof (Hreal a Ha). lia.
    - intros a Ha. destruct (Hfs a Ha) as (b & Hb64 & Hwm & Hlo & Hhi).
      destruct (lw_fs_place _ ([] ++ g_H g) mem md b HAH Hwm Hb64) as [_ _ _ Happ].
      apply Happ. lia. }
  assert (HshIS : forall x, Sfr fr <= x < Sfr fr + 392 -> in_shadow x).
  { intros x Hx.
    assert (Hdiv : (fr + 8 * (x - Sfr fr)) / 8 = fr / 8 + (x - Sfr fr)).
    { replace (8 * (x - Sfr fr)) with ((x - Sfr fr) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
    assert (Hin : fr <= fr + 8 * (x - Sfr fr) < fr + 3136) by lia.
    pose proof (shadow_of_app (fr + 8 * (x - Sfr fr)) (Hfrapp _ Hin)) as His.
    replace (shadow_addr (fr + 8 * (x - Sfr fr))) with x in His; [exact His|].
    unfold shadow_addr. rewrite Hdiv. unfold Sfr, shadow_addr. lia. }
  assert (HSfrhi : Sfr fr + 392 <= HIGHMEM_BEG).
  { pose proof (HshIS (Sfr fr + 391) ltac:(lia)) as Hin.
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hin.
    unfold HIGHMEM_BEG. lia. }
  assert (HSlo : LOWMEM_END <= Sfr fr).
  { pose proof (HshIS (Sfr fr) ltac:(lia)) as Hin.
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hin.
    unfold LOWMEM_END. lia. }
  assert (HSfr64 : 0 <= Sfr fr < 2 ^ 64)
    by (unfold HIGHMEM_BEG in HSfrhi; unfold LOWMEM_END in HSlo; lia).
  assert (Hn64 : 0 <= g_n g < 2 ^ 64)
    by (unfold g_n, nlen in *; unfold AC.ANMAX in Hnmax; lia).
  assert (E19 : bv_unsigned (getr regs 19) = Sfr fr)
    by (unfold rg in Hr19; rewrite Hr19; apply MState.unsigned_lit; lia).
  assert (E9 : bv_unsigned (getr regs 9) = A)
    by (unfold rg in Hr9; rewrite Hr9; apply MState.unsigned_lit; lia).
  assert (E18 : bv_unsigned (getr regs 18) = g_n g)
    by (unfold rg in Hr18; rewrite Hr18; apply MState.unsigned_lit; lia).
  assert (Hfr64 : 0 <= fr < 2 ^ 64).
  { pose proof (Hfrapp fr ltac:(lia)) as Hfa0.
    unfold app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG in Hfa0. lia. }
  assert (E25 : bv_unsigned (getr regs 25) = fr)
    by (unfold rg in Hr25; rewrite Hr25; apply MState.unsigned_lit; lia).
  (* the two writable blocks the run stores into *)
  pose proof Hsh as Hsh0. destruct Hsh0 as (sh & Hshb & Hshlen).
  change (Z.to_nat FRAME_SHADOW) with 392%nat in Hshlen.
  assert (Hlen1 : length (firstn 137 (skipn 255 sh)) = 137%nat)
    by (rewrite firstn_length_le; [reflexivity | rewrite length_skipn; lia]).
  assert (FRsh : rw_cells rsegs mem (Sfr fr + 255) [CB 137 (firstn 137 (skipn 255 sh))]).
  { apply (a4_rw_of_bytes_n mem (Sfr fr + 255) (firstn 137 (skipn 255 sh)) 137%nat).
    - replace (Sfr fr + 255) with (Sfr fr + Z.of_nat 255)
        by (change (Z.of_nat 255) with 255%Z; lia).
      apply a4_bytes_mid; [exact Hshb | lia].
    - exact Hlen1.
    - intros x Hx. change (Z.of_nat 137) with 137%Z in Hx.
      exact (proj1 (AsanRTInv.RT_shadow_rw sp mem md HRT x (HshIS x ltac:(lia)))). }
  destruct (Frame.stk_split rsegs mem (g_S g - AF.SLOT_STACK) (A + 56) (g_S g) Hwin ltac:(lia)) as (_ & ST1).
  destruct (Frame.stk_split rsegs mem (A + 56) (A + 320) (g_S g) ST1 ltac:(lia)) as (ST2 & _).
  destruct (Frame.stk_carve rsegs mem (A + 56) (A + 320) 264 ST2
              ltac:(change (Z.of_nat 264) with 264%Z; lia)) as (_ & junk2 & FRsp0).
  replace (A + 320 - Z.of_nat 264) with (A + 56) in FRsp0
    by (change (Z.of_nat 264) with 264%Z; lia).
  (* the write set *)
  assert (HWchar : forall x, 0 <= x < 2 ^ 64 ->
    ~ Frame.outside [(Sfr fr + 255, Sfr fr + 392); (A + 56, A + 320)] x ->
    (Sfr fr + 255 <= x < Sfr fr + 392) \/ (A + 56 <= x < A + 320)).
  { intros x Hx Ho.
    destruct (Z_le_gt_dec (Sfr fr + 255) x) as [H1|H1];
      [destruct (Z_lt_ge_dec x (Sfr fr + 392)) as [H2|H2]; [left; lia|]|];
      (destruct (Z_le_gt_dec (A + 56) x) as [H3|H3];
       [destruct (Z_lt_ge_dec x (A + 320)) as [H4|H4]; [right; lia|]|]);
      exfalso; apply Ho; cbn [Frame.outside]; (split; [lia|]); (split; [lia | exact I]). }
  assert (HDj : rt_disjoint [(Sfr fr + 255, Sfr fr + 392); (A + 56, A + 320)]).
  { unfold LOWMEM_END in HSlo. unfold HIGHMEM_BEG in HAhm.
    unfold rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
      RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM,
      RT_MUG, RT_AGLOB, RT_AGLOB_LEN.
    cbn [OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.disjoint_from Frame.disjoint_from].
    repeat split; first [ exact I | left; lia ]. }
  (* our[]'s six bytes at fr + 2624 are present: the frame lies in the slot window on the real arm (sp = fr) and
     in the FakeStack on the side arm (a_fs_ok); at the loop head of turn 0 they are LOOPB's six unread bytes. *)
  assert (Hour0 : exists ob, length ob = 6%nat /\ bytes_at rsegs mem (fr + 2624) ob).
  { assert (Hfstk : Frame.stk rsegs mem fr (fr + 3136)).
    { split; [lia|]. split; [lia|]. intros a Ha.
      destruct Hloc as [[_ [Hspfr _]]|[_ [_ [Hfs _]]]].
      - destruct Hwin as (_ & _ & Hwv). apply Hwv. lia.
      - destruct (Hfs a ltac:(lia)) as (FSa & HFSar & Hwa & Hloa & Hhia).
        destruct (lw_fs_bytes mem FSa (lw_fs_ok _ ([] ++ g_H g) mem md FSa HAH Hwa HFSar) a ltac:(lia))
          as (Hw & bb & Hb).
        split; [exact Hw|]. exists bb. exact Hb. }
    destruct (Frame.stk_split rsegs mem fr (fr + 2624) (fr + 3136) Hfstk ltac:(lia)) as (_ & Hs1).
    destruct (Frame.stk_split rsegs mem (fr + 2624) (fr + 2630) (fr + 3136) Hs1 ltac:(lia)) as (Hs2 & _).
    destruct (Frame.stk_bytes rsegs mem (fr + 2624) (fr + 2630) Hs2 ltac:(lia)) as (ob & Hobl & Hob).
    exists ob. split; [|exact Hob].
    rewrite Hobl. replace (fr + 2630 - (fr + 2624)) with 6 by lia. reflexivity. }
  (* the run *)
  apply (sl_run regs (Z_to_bv 64 0x81220) mem md
    (fun R pc' mm =>
       Frame.munch [(Sfr fr + 255, Sfr fr + 392); (A + 56, A + 320)] mem mm /\
       Frame.wmono rsegs mem mm /\
       (exists cs1, rw_cells rsegs mm (Sfr fr + 255) cs1 /\ cells_size cs1 = 137%nat) /\
       (exists cs2, rw_cells rsegs mm (A + 56) cs2 /\ cells_size cs2 = 264%nat) /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
       getr R 26 = getr regs 26 /\ getr R 24 = getr regs 24 /\ getr R 25 = getr regs 25 /\
       getr R 27 = getr regs 27 /\ getr R 18 = getr regs 18 /\ getr R 22 = getr regs 22 /\
       (pc' = Z_to_bv 64 0x82f2c \/
        (pc' = Z_to_bv 64 0x81548 /\ g_n g < 2 ^ 26 /\
         bytes_at rsegs mm (Sfr fr + 328) [Z_to_bv 8 6] /\
         getr R 20 = Z_to_bv 64 (fr + 2656) /\
         getr R 10 = Z_to_bv 64 6 /\ getr R 11 = Z_to_bv 64 1 /\ getr R 12 = Z_to_bv 64 (fr + 2624) /\
         getr R 16 = Z_to_bv 64 (fr + 32) /\ getr R 17 = Z_to_bv 64 (fr + 64) /\
         q64 mm (A + 144) (fr + 2176) /\ q64 mm (A + 112) (fr + 2256) /\
         q64 mm (A + 312) (fr + 544) /\ q64 mm (A + 264) (fr + 2624) /\
         q64 mm (A + 56) (fr + 3040) /\ q64 mm (A + 184) (fr + 2368) /\
         q64 mm (A + 176) (fr + 2688) /\ q64 mm (A + 208) (fr + 2768) /\
         q64 mm (A + 96) (decl_slot fr) /\ q64 mm (A + 120) (fr + 2528) /\
         q64 mm (A + 240) (fr + 2448) /\ q64 mm (A + 232) (fr + 2464) /\ q64 mm (A + 224) (fr + 2496) /\
         q64 mm (A + 64) (fr + 3056) /\
         q64 mm (A + 136) (fr + 160) /\ q64 mm (A + 280) (fr + 176) /\ q64 mm (A + 168) (fr + 2880) /\
         q64 mm (A + 192) (fr + 528) /\ q64 mm (A + 200) (fr + 336) /\ q64 mm (A + 216) (fr + 448) /\
         q64 mm (A + 104) (fr + 128) /\ q64 mm (A + 288) (fr + 256) /\ q64 mm (A + 296) (fr + 304) /\
         q64 mm (A + 304) (fr + 272))))
    (Post B APIf ra g)).
  - exact Hhalt.
  - rewrite a4_mkR_of.
    eapply evt_mono.
    + apply a4_evt with (junk1 := firstn 137 (skipn 255 sh)) (junk2 := junk2).
      * rewrite E19. exact FRsh.
      * rewrite E9. exact FRsp0.
      * rewrite E19, E9. unfold HIGHMEM_BEG in HSfrhi, HAhm. lia.
    + intros ms' HP.
      destruct HP as (a0' & a1' & a2' & a3' & a6' & a7' & s4' & pc' & m' & cs1 & cs2 &
        Hms & MU & WM & Hc1 & Hn1 & Hc2 & Hn2 & Hexit).
      rewrite E19 in MU, Hc1. rewrite E9 in MU, Hc2. rewrite E18, E9, E25, E19 in Hexit.
      do 3 eexists. split; [exact Hms|].
      split; [exact MU|]. split; [exact WM|].
      split; [exists cs1; split; [exact Hc1 | exact Hn1]|].
      split; [exists cs2; split; [exact Hc2 | exact Hn2]|].
      do 12 (split; [reflexivity|]).
      destruct Hexit as [(Hpc & _)|Hexit]; [left; exact Hpc | right; exact Hexit].
  - intros R pc' mm regs'' md' HK Hreg Hmat.
    destruct HK as (MU & WM & (cs1 & Hc1 & Hn1) & (cs2 & Hc2 & Hn2) &
      G2 & G3 & G4 & G8 & G9 & G19 & G26 & G24 & G25 & G27 & G18 & G22 & Hexit).
    assert (Hsh' : exists sh2, bytes_at rsegs mm (Sfr fr) sh2 /\ length sh2 = 392%nat).
    { destruct Hc1 as [(Hwf1 & Hb1) Hw1].
      assert (Hpre : bytes_at rsegs mem (Sfr fr) (firstn 255 sh))
        by (apply a4_bytes_pre; [exact Hshb | lia]).
      exists (firstn 255 sh ++ cells_bytes cs1). split.
      - apply bytes_at_app. split.
        + apply (fl_bytes [(Sfr fr + 255, Sfr fr + 392); (A + 56, A + 320)] mem mm
                   (Sfr fr) (firstn 255 sh) Hpre MU).
          intros x Hx. rewrite firstn_length_le in Hx by lia.
          change (Z.of_nat 255) with 255%Z in Hx.
          cbn [Frame.outside]. split; [lia|]. split; [unfold HIGHMEM_BEG in HSfrhi, HAhm; lia | exact I].
        + rewrite firstn_length_le by lia. change (Z.of_nat 255) with 255%Z. exact Hb1.
      - rewrite length_app, firstn_length_le by lia.
        rewrite (cells_bytes_length cs1 Hwf1), Hn1. reflexivity. }
    assert (HPresW : forall x, 0 <= x < 2 ^ 64 ->
      ~ Frame.outside [(Sfr fr + 255, Sfr fr + 392); (A + 56, A + 320)] x ->
      exists b, mbyte rsegs mm x = Some b).
    { intros x Hx Ho. destruct (HWchar x Hx Ho) as [Hin|Hin].
      - destruct Hc1 as [(Hwf1 & Hb1) _].
        apply (a4_pres mm (Sfr fr + 255) (cells_bytes cs1) x Hb1).
        rewrite (cells_bytes_length cs1 Hwf1), Hn1. lia.
      - destruct Hc2 as [(Hwf2 & Hb2) _].
        apply (a4_pres mm (A + 56) (cells_bytes cs2) x Hb2).
        rewrite (cells_bytes_length cs2 Hwf2), Hn2. lia. }
    destruct (a4_AH ([] ++ g_H g) mem mm md fr (A + 56) (A + 320)
                [(Sfr fr + 255, Sfr fr + 392); (A + 56, A + 320)] HAH MU WM
                ltac:(destruct Hloc as [[_ [_ Hl]]|[_ [_ [Hl _]]]]; [left|right]; exact Hl)
                ltac:(lia) ltac:(lia)
                ltac:(intros x Hx Ho; destruct (HWchar x Hx Ho) as [Hin|Hin];
                      [left; exists (x - Sfr fr); split; [lia | lia] | right; exact Hin])
                HPresW) as (HAH' & HOWN & HSTK & HSTKHI).
    assert (HFS1 : FRAS B APIf ra g fr [] regs'' mm md sel).
    { unfold FRAS. apply (a4_frah g fr [] regs regs'' mem mm md sel 0x41b58ab3
               [(Sfr fr + 255, Sfr fr + 392); (A + 56, A + 320)] HFS MU WM HDj HAH' HSTK).
      - intros A0 HA0 HA064 x Hx Ho.
        assert (A0 = A).
        { unfold rg in Hr9. rewrite Hr9 in HA0.
          pose proof (f_equal (@bv_unsigned 64) HA0) as Hq.
          rewrite !MState.unsigned_lit in Hq by lia. lia. }
        subst A0. exact (HWchar x Hx Ho).
      - exact HPresW.
      - exact Hsh'.
      - rewrite Hreg; exact G2.
      - rewrite Hreg; exact G3.
      - rewrite Hreg; exact G4.
      - rewrite Hreg; exact G8.
      - rewrite Hreg; exact G9.
      - rewrite Hreg; exact G19.
      - rewrite Hreg; exact G26. }
    assert (HFS2 : FRAS B APIf ra g fr [] regs'' mm md' sel).
    { unfold FRAS, FRAH in HFS1 |- *.
      destruct HFS1 as (A1 & sp1 & HRT1 & HAH1 & Hro1 & Hsn1 & Hhalt1 & Hrest1).
      destruct (lw_mat_le (APIf rc) ([] ++ g_H g) mm md md' Hmat) as [HAHm _ Hstklo_eq _].
      destruct Hrest1 as (Hgimg1 & Hr21' & Hspm1 & Haspz1 & Hstklo1 & Hrest1).
      destruct Hrest1 as (Hr41 & Hr81 & Hr91 & Hr31 & Hr191 & Hr261 & Hfrm1 & Hsel1 & HAm1 & HAS1 & Hspa1 &
        Hfa1 & HA4481 & HS41 & HAPP1 & Hspill1 & Hloc1 & Hrest1).
      exists A1, sp1.
      split; [exact (AsanRTInv.RT_any sp1 sp1 mm md md' HRT1)|].
      split; [exact (HAHm HAH1)|].
      split; [exact Hro1|].
      split; [destruct Hsn1 as (He & Hh & Hf); split; [exact He|];
              split; [exact Hh|]; rewrite (sl_mat_fds md md' Hmat); exact Hf|].
      split; [rewrite (AsanLift.mat_le_halted md md' Hmat); exact Hhalt1|].
      split; [exact Hgimg1|]. split; [exact Hr21'|]. split; [exact Hspm1|]. split; [exact Haspz1|].
      split; [rewrite Hstklo_eq; exact Hstklo1|].
      split; [exact Hr41|]. split; [exact Hr81|]. split; [exact Hr91|]. split; [exact Hr31|].
      split; [exact Hr191|]. split; [exact Hr261|]. split; [exact Hfrm1|]. split; [exact Hsel1|].
      split; [exact HAm1|]. split; [exact HAS1|]. split; [exact Hspa1|]. split; [exact Hfa1|].
      split; [exact HA4481|]. split; [exact HS41|]. split; [exact HAPP1|]. split; [exact Hspill1|].
      split; [|exact Hrest1].
      destruct Hloc1 as [[H0 [Hspfr Hreal]]|[Hfr0 Hfs]].
      - left. split; [exact H0|]. split; [exact Hspfr|]. intros a Ha. rewrite Hstklo_eq. exact (Hreal a Ha).
      - right. split; [exact Hfr0 | exact Hfs]. }
    (* ENT across the run: none of the addresses the entry relation speaks of (the bytes of an entry block the
       target does not keep, the image, the stack at or above S, the shadow bytes of those, and the shadow bytes of
       those entry blocks) is one of the segment's two written ranges. *)
    assert (HENT1 : ENT APIf g [] mm md).
    { eapply ent_munch with (W := [(Sfr fr + 255, Sfr fr + 392); (A + 56, A + 320)]) (mem := mem).
      - exact HENT.
      - exact HAH.
      - exact MU.
      - intros x Hk. destruct Hk as [Hblkk | [Hik | [Habk | [(b & Hor & ->) | Hshk]]]].
        + destruct Hblkk as (q & k & i & Hin & Hni & Hi & ->).
          destruct (lw_blocks _ ([] ++ g_H g) mem md q k HAH Hin) as [_ Hq4 Hend _ Hall].
          destruct (Hall (q + i) ltac:(lia)) as (Happq & _).
          assert (Hqr : 0 <= q + i < 2 ^ 64)
            by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Happq; lia).
          apply HW2; [exact Hqr | | lia].
          intro Hs. exact (app_not_shadow (q + i) Happq (HshIS (q + i) ltac:(lia))).
        + pose proof (img_below_GT x Hik) as Hxg. unfold AC.GT in Hxg.
          assert (Happx : app_mem x) by (unfold app_mem, LOWMEM_END; left; lia).
          apply HW2; [lia | | lia].
          intro Hs. exact (app_not_shadow x Happx (HshIS x ltac:(lia))).
        + assert (Happx : app_mem x) by (unfold app_mem; right; lia).
          apply HW2; [lia | | lia].
          intro Hs. exact (app_not_shadow x Happx (HshIS x ltac:(lia))).
        + assert (Hb0 : 0 <= b)
            by (destruct Hor as [Hi|Hr]; [pose proof (img_below_GT b Hi) as X; unfold AC.GT in X|]; lia).
          assert (Hnb : ~ (fr <= b < fr + 3136))
            by (unfold AC.GT in Hgt;
                destruct Hor as [Hi|Hr]; [pose proof (img_below_GT b Hi) as X; unfold AC.GT in X|]; lia).
          assert (Happb : app_mem b).
          { destruct Hor as [Hi|Hr];
              [pose proof (img_below_GT b Hi) as X; unfold AC.GT in X; unfold app_mem, LOWMEM_END; left; lia
              |unfold app_mem; right; lia]. }
          pose proof (shadow_of_app b Happb) as Hsb.
          pose proof (in_shadow_range (shadow_addr b) Hsb) as Hsr.
          pose proof Hsb as Hsb'.
          unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hsb'.
          apply HW2.
          * lia.
          * intro Hs. apply (a4_shadow_off fr b Hfr8 ltac:(unfold AC.GT in Hgt; lia) Hb0 Hnb). lia.
          * lia.
        + (* the shadow byte of a byte of an entry block the target does not keep: that byte is app memory below
             stklo and off the frame *)
          destruct Hshk as (q & k & i & Hin & Hni & Hi & ->).
          destruct (lw_blocks _ ([] ++ g_H g) mem md q k HAH Hin) as [_ Hq4 Hend _ Hall].
          destruct (Hall (q + i) ltac:(lia)) as (Happq & _ & _ & _ & Hnfs).
          assert (Hb0 : 0 <= q + i) by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Happq; lia).
          assert (Hnb : ~ (fr <= q + i < fr + 3136)).
          { destruct Hloc as [[_ [_ Hreal]]|[_ [_ [Hfs _]]]].
            - intro Hf. pose proof (Hreal (q + i) ltac:(lia)). lia.
            - intro Hf. exact (Hnfs (Hfs (q + i) ltac:(lia))). }
          pose proof (shadow_of_app (q + i) Happq) as Hsq.
          pose proof Hsq as Hsq'.
          unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hsq'.
          apply HW2; [lia | | lia].
          intro Hs. apply (a4_shadow_off fr (q + i) Hfr8 ltac:(unfold AC.GT in Hgt; lia) Hb0 Hnb). lia.
      - exact HSTK.
      - exact HSTKHI.
      - intros a Hia Ho. exact (proj2 (HOWN a) Ho). }
    assert (HENT2 : ENT APIf g [] mm md') by (eapply ent_mat; [exact HENT1 | exact Hmat]).
    rewrite <- SEGS.
    destruct Hexit as [Hpc|(Hpc & Hn26 & Hb328 & Hs4 & Ha0 & Ha1 & Ha2 & Ha6 & Ha7 &
                            Hq144 & Hq112 & Hq312 & Hq264 & Hq56 & Hq184 & Hq176 & Hq208 & Hq96 & Hq120 &
                            Hq240 & Hq232 & Hq224 & Hq64 &
                            Hp136 & Hp280 & Hp168 & Hp192 & Hp200 & Hp216 & Hp104 & Hp288 & Hp296 & Hp304)];
      subst pc'.
    + apply HJ. exists regs'', mm, md', fr, sel.
      split; [reflexivity|]. split; [exact HFS2|]. split; [exact HENT2|]. cbv beta.
      unfold rg in *. rewrite !Hreg, G24, G25. split; [exact Hr24 | exact Hr25].
    + (* turn 0 of the our[] loop: LOOPB (the loop registers and record spills A4 set, the input facts FRAS
         carries, our[]'s six bytes unread) and PRA (A4's frame-loop pointer spills) *)
      apply H5. exists regs'', mm, md', fr, sel.
      split; [reflexivity|]. split; [exact HFS2|]. split; [exact HENT2|]. cbv beta.
      assert (HA9 : rg regs'' 9 A) by (unfold rg in Hr9 |- *; rewrite Hreg, G9; exact Hr9).
      assert (Hsp : forall off v, q64 mm (A + off) v -> spill regs'' mm off v)
        by (intros off v Hq; unfold spill; exists A; split; [exact HA9 | exact Hq]).
      split.
      2:{ unfold PRA.
          split; [exact (Hsp _ _ Hp136)|]. split; [exact (Hsp _ _ Hp280)|].
          split; [exact (Hsp _ _ Hp168)|]. split; [exact (Hsp _ _ Hp192)|].
          split; [exact (Hsp _ _ Hp200)|]. split; [exact (Hsp _ _ Hp216)|].
          split; [exact (Hsp _ _ Hp104)|]. split; [exact (Hsp _ _ Hp288)|].
          split; [exact (Hsp _ _ Hp296)|]. split; [exact (Hsp _ _ Hp304) | exact (Hsp _ _ Hp168)]. }
      unfold LOOPB.
      destruct (a4_frah_in g fr [] regs'' mm md' sel 0x41b58ab3 HFS2) as (Hinb' & Hinblk').
      rewrite (Z.min_l 0 (g_n g)) by lia.
      rewrite !Z.sub_0_r, !Z.add_0_r.
      split; [exact Hn26|]. split; [lia|].
      split; [unfold rg in Hr24 |- *; rewrite Hreg, G24; exact Hr24|].
      split; [unfold rg in Hr25 |- *; rewrite Hreg, G25; exact Hr25|].
      split; [exact (Hsp _ _ Hq144)|].
      split; [exact (Hsp _ _ Hq112)|].
      split; [exact (Hsp _ _ Hq312)|].
      split; [exact (Hsp _ _ Hq264)|].
      split; [unfold rg; rewrite Hreg; exact Hs4|].
      split; [unfold rg; rewrite Hreg; exact Ha0|].
      split; [unfold rg; rewrite Hreg; exact Ha1|].
      split; [unfold rg; rewrite Hreg; exact Ha2|].
      split; [unfold rg; rewrite Hreg; exact Ha7|].
      split; [unfold rg in Hr18 |- *; rewrite Hreg, G18; exact Hr18|].
      split; [unfold rg in Hr22 |- *; rewrite Hreg, G22; exact Hr22|].
      split; [unfold rg in Hr27 |- *; rewrite Hreg, G27; exact Hr27|].
      split; [exact (Hsp _ _ Hq56)|].
      split; [exact (Hsp _ _ Hq184)|].
      split; [exact (Hsp _ _ Hq176)|].
      split; [exact (Hsp _ _ Hq208)|].
      split.
      { (* our[]: its shadow byte S(fr) + 328 is 6 (0x814b8) *)
        apply a4_our_addr; [lia | exact Hfr8 | | intros i Hi; apply Hfrapp; lia | exact Hb328].
        pose proof (Hfrapp (fr + 2629) ltac:(lia)) as Hx.
        unfold app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG in Hx |- *. lia. }
      split; [exact (Hsp _ _ Hq96)|].
      split; [exact (Hsp _ _ Hq120)|].
      split; [exact (Hsp _ _ Hq240)|].
      split; [exact (Hsp _ _ Hq232)|].
      split; [exact (Hsp _ _ Hq224)|].
      split; [exact (Hsp _ _ Hq64)|].
      split; [exact Hinb'|].
      split; [exact Hinblk'|].
      split.
      { (* our[]'s six bytes: app memory below A + 56 and not a shadow byte, so the run keeps them *)
        destruct Hour0 as (ob & Hobl & Hob).
        exists ob. split; [rewrite Hobl; reflexivity|].
        change (firstn (Z.to_nat 0) (OUR (g_in g)) ++ ob) with ob.
        apply (fl_bytes [(Sfr fr + 255, Sfr fr + 392); (A + 56, A + 320)] mem mm (fr + 2624) ob Hob MU).
        rewrite Hobl. intros x Hx. change (Z.of_nat 6) with 6%Z in Hx.
        apply (proj1 (fr_outside_lib _ _)).
        apply HW2; [lia | | lia].
        intro Hs. exact (app_not_shadow x (Hfrapp x ltac:(lia)) (HshIS x ltac:(lia))). }
      unfold rg; rewrite Hreg; exact Ha6.
Qed.

End A4.
