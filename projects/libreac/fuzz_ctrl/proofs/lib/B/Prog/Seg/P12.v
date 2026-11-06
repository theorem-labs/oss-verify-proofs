(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v, with its module paths and module names changed; 754 of its 794 lines of code are new or changed and 356 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/F31.v, with its module paths, module names and addresses changed; 496 of its 556 lines of code are new or changed and 734 lines of the source are left out. *)
(* Segment P12 of fuzz_ctrl LLVMFuzzerTestOneInput (asan-ubsan, libreac v1.9.0 image B): 0x81e08-0x81ec0 (no
   call), ending at the frame-loop head 0x81ec4 (turn 0) or, for a short input, at the epilogue cut 0x82eac.
   The v1.9.0 move of the patched-image seg_P12 (a working branch 509cbbd9bd1).
   0x81e08-0x81e4c: the two instrumented checks of the name bytes at QMARK = 0x211e0 (a0, the reac_ctrl_kind_name
     result of P11, which Inv_B81e08 records). Each loads the shadow byte k of QMARK at (QMARK >> 3) + s10 and
     branches on it: k = 0 skips the slow block, otherwise the code goes to 0x82fb0 / 0x82fc0, which compare
     (a0 mod 8) with k and come back; the error path (0x82fbc / 0x82fcc, a call of __asan_report_load1) is not
     reached. QMARK is the registered global (0x211e0, 2), so FRA's registered-globals clause gives
     `addressable m QMARK 1` and `addressable m (QMARK + 1) 1`, hence k = 0 or 2 <= k <= 7. The name bytes are
     read-only image bytes (FRA's ro_agree): 63 ('?') and 0, so the jumps 0x81e28 / 0x81e4c to the trap block 0x82fa4 are
     not taken.
   0x81e50-0x81ec0: the frame-loop prologue: a3 = 0 (the turn index), s11 = -8, the spills [A+256] = fragb fr + 8,
     [A+128] = fragb fr + 19, [A+120] = fragb fr + 15 from [A+208] = fragb fr (PL0), [A+88] = fr + 2885 (the body of
     the local `first`) from [A+168] = fr + 2880 (PRA), [A+112] = fr + 186, [A+96] = fr + 180 from [A+280] =
     fr + 176 (PRA), [A+144] = fr + 452 from [A+216] = fr + 448 (PRA), s6 = 1, and eight 1-byte stores of -8 into
     the frame's shadow bytes S(fr) + 370 .. 385. The patched prologue's four zero stores of the first-fragment
     spills and its overflow flag [A+72] have no v1.9.0 counterpart: the turn-0 first-fragment state is the local
     `first` that P3 zeroed (PL0's FSj g fr 0), which this run does not write.
   0x81ec4 `bnez s9` is the frame-loop head, with s9 = left_0 = n - c0 (PL0's cursor): left_0 >= 1 stops the run
     at the head, where it meets Inv_B81ec4_at g 0 (FLI from PRO, PL0, fra_stk, the entry's KNT and the prologue's
     stores; IFS 0 from PL0's all-zero records and its FSj g fr 0; s6 = 1 from 0x81ea0; [A+280] = fr + 176 from
     PRA); left_0 = 0 (n <= 7) runs on through 0x81ec8 `j 82eac` to Inv_B82eac (x1_entry_of_pl0), which is why
     seg_P12 has that cut as a second exit premise (S_P12).
   FRA and ENT move across the write set [A+88, A+104) u [A+112, A+136) u [A+144, A+152) u [A+256, A+264) u
   [S(fr)+370, S(fr)+386) by Tac_p12.tp_fra_ent. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge Image.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.UL Require Import Exec Step Tac Cells.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.UL Require Frame Mem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.AW Require Import SmLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot Tac_fs Tac_p12.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Tac_ro.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcIdentModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import reac_ctrl_kind_name_c.
Import ListNotations.
(* Tac_p12's lib/Lib chain loads lib/Reusable/YK11.v, so the short name YK11 could resolve to that copy; the
   registers and FPState here must be image B's, as SlotInv's are (lib/B/Prog/Seg/Tac_f23.v). *)
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.FrameAPI.
Module LFr := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module LMm := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module LMs := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Module UFr := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.UL.Frame.
Module UMm := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.UL.Mem.
Module UPE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.UL.PropExec.

(* A shadow byte that the instrumented 1-byte checks at offset 0 and at offset 1 of its granule both pass is 0 or
   between 2 and 7 (shadow_ok), hence one of seven literal bytes. *)
Lemma p12_byte_cases : forall b : byte, bv_signed b = 0 \/ 2 <= bv_signed b <= 7 ->
  b = Z_to_bv 8 0 \/ b = Z_to_bv 8 2 \/ b = Z_to_bv 8 3 \/ b = Z_to_bv 8 4 \/ b = Z_to_bv 8 5 \/
  b = Z_to_bv 8 6 \/ b = Z_to_bv 8 7.
Proof.
  intros b H.
  assert (Hu : bv_unsigned b = bv_signed b).
  { pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R.
    unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in H |- *.
    change (2 ^ Z.of_N 8 / 2) with 128 in H |- *. change (2 ^ Z.of_N 8) with 256 in H |- *.
    Z.div_mod_to_equations. lia. }
  assert (Hv : bv_unsigned b = 0 \/ bv_unsigned b = 2 \/ bv_unsigned b = 3 \/ bv_unsigned b = 4 \/
               bv_unsigned b = 5 \/ bv_unsigned b = 6 \/ bv_unsigned b = 7) by lia.
  destruct Hv as [Hv|[Hv|[Hv|[Hv|[Hv|[Hv|Hv]]]]]];
    [left | right; left | right; right; left | right; right; right; left
    | right; right; right; right; left | right; right; right; right; right; left
    | right; right; right; right; right; right];
    apply bv_eq; rewrite Hv; reflexivity.
Qed.

(* The name bytes at QMARK, "?" and its terminating 0, are read-only image bytes. *)
Lemma p12_ro_at : forall m a bs, ro_agree rsegs m -> 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  Image.ro_bytes_b rsegs a bs = true -> LMm.bytes_at rsegs m a bs.
Proof.
  intros m a bs Hro Ha Hl Hb. split; [lia|]. split; [lia|].
  intros i Hi. destruct (nth_error bs i) as [b|] eqn:E; [|apply nth_error_None in E; lia].
  destruct (LMm.ro_bytes_nth rsegs bs a i b (Image.ro_bytes_b_sound rsegs bs a Hb) E) as (Hrom & Hra).
  rewrite (Hro _ Hra). exact Hrom.
Qed.

Lemma p12_qmark : forall m, ro_agree rsegs m -> LMm.bytes_at rsegs m QMARK [Z_to_bv 8 63; Z_to_bv 8 0].
Proof.
  intros m Hro. apply p12_ro_at; [exact Hro | unfold QMARK; lia | cbn; unfold QMARK; lia |].
  vm_compute. reflexivity.
Qed.

(* The turn-0 fragment record is all-zero, so its model invariant holds. *)
Lemma p12_frag_ok_z72 : frag_ok z72.
Proof.
  unfold frag_ok. split; [left; vm_compute; reflexivity | intros H; vm_compute in H; discriminate H].
Qed.

(* A word cell of a cell list: its 8 bytes at its offset. *)
Lemma p12_q64_at : forall m A cs k w z a, rw_cells rsegs m A cs -> cell_at cs k = Some (C8 w) ->
  w = Z_to_bv 64 z -> a = A + Z.of_nat k -> q64 m a z.
Proof.
  intros m A cs k w z a ((Hwf & Hb) & _) Hk -> ->.
  destruct (cell_at_split cs k (C8 (Z_to_bv 64 z)) (C8 (Z_to_bv 64 z)) Hk) as (pre & post & -> & Hsz & _).
  rewrite cells_bytes_app in Hb. cbn [cells_bytes cbytes] in Hb.
  apply UMm.bytes_at_app in Hb. destruct Hb as (_ & Hb).
  apply cells_wf_app in Hwf. destruct Hwf as (Hwf1 & _).
  rewrite cells_bytes_length in Hb by exact Hwf1. rewrite Hsz in Hb.
  apply UMm.bytes_at_app in Hb. destruct Hb as (Hb & _). exact Hb.
Qed.

(* Every byte of a cell list is readable. *)
Lemma p12_rw_rd : forall m A cs q, rw_cells rsegs m A cs -> A <= q < A + Z.of_nat (cells_size cs) ->
  exists b, LMm.mrd rsegs m (LMm.wa q) = Some b.
Proof.
  intros m A cs q ((Hwf & Hb) & _) Hq. rewrite <- cells_bytes_length in Hq by exact Hwf.
  destruct Hb as (HA & HL & H).
  assert (Hi : (Z.to_nat (q - A) < length (cells_bytes cs))%nat) by lia.
  pose proof (H (Z.to_nat (q - A)) Hi) as HH. rewrite Z2Nat.id in HH by lia.
  replace (A + (q - A)) with q in HH by lia.
  destruct (nth_error (cells_bytes cs) (Z.to_nat (q - A))) as [b|] eqn:E; [exists b; exact HH|].
  exfalso. apply nth_error_None in E. lia.
Qed.

(* A word cell k bytes into a cell block, read as the spill fact q64 the post states. *)
Ltac p12_q H kk :=
  eapply p12_q64_at with (k := kk); [exact H | reflexivity | try unfold fragb; f_equal; lia | cbn; lia].

Section P12.
Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

(* ---- the two instrumented checks, 0x81e08 -> 0x81e50. *)

(* The first check: 0x81e08-0x81e18 (and the compare block 0x82fb0-0x82fb8 when the shadow byte is not 0). *)
Lemma p12_ck1 :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (kb : byte),
    a0 = Z_to_bv 64 135648 -> s10 = Z_to_bv 64 2147450880 ->
    ov_read_bytes rsegs m (wa 2147467836) 1 = Some [kb] ->
    (bv_signed kb = 0 \/ 2 <= bv_signed kb <= 7) ->
    evt rsegs
      (fun ms' => exists a1' a2' : word,
         ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 135648) a1' a2' a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 2147450880) s11 t3 t4 t5 t6)
                  Fr (Z_to_bv 64 0x81e1c) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81e08) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m kb -> -> HR Hk.
  destruct (p12_byte_cases kb Hk) as [->|[->|[->|[->|[->|[-> | -> ]]]]]];
    [ do 4 step; if_true
    | do 4 step; if_false; do 3 step; if_false; step .. ];
  apply evt_done; do 2 eexists; reflexivity.
Qed.

(* The second check: 0x81e2c-0x81e40 (and 0x82fc0-0x82fc8), then the second name byte 0 at 0x81e44. *)
Lemma p12_ck2 :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (kb : byte),
    a0 = Z_to_bv 64 135648 -> s10 = Z_to_bv 64 2147450880 ->
    ov_read_bytes rsegs m (wa 2147467836) 1 = Some [kb] ->
    ov_read_bytes rsegs m (wa 135649) 1 = Some [Z_to_bv 8 0] ->
    (bv_signed kb = 0 \/ 2 <= bv_signed kb <= 7) ->
    evt rsegs
      (fun ms' => exists a1' a2' : word,
         ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1' a2' a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 2147450880) s11 t3 t4 t5 t6)
                  Fr (Z_to_bv 64 0x81e50) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81e2c) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m kb -> -> HRs HR1 Hk.
  destruct (p12_byte_cases kb Hk) as [->|[->|[->|[->|[->|[-> | -> ]]]]]];
    [ do 5 step; if_true
    | do 5 step; if_false; do 3 step; if_false; step .. ];
  do 2 step; if_true; apply evt_done; do 2 eexists; reflexivity.
Qed.

(* The whole check block 0x81e08 -> 0x81e50: the two checks and the two name bytes 63, 0. *)
Lemma p12_chk :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (kb : byte),
    a0 = Z_to_bv 64 135648 -> s10 = Z_to_bv 64 2147450880 ->
    ov_read_bytes rsegs m (wa 2147467836) 1 = Some [kb] ->
    ov_read_bytes rsegs m (wa 135648) 1 = Some [Z_to_bv 8 63] ->
    ov_read_bytes rsegs m (wa 135649) 1 = Some [Z_to_bv 8 0] ->
    (bv_signed kb = 0 \/ 2 <= bv_signed kb <= 7) ->
    evt rsegs
      (fun ms' => exists a1' a2' : word,
         ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1' a2' a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 2147450880) s11 t3 t4 t5 t6)
                  Fr (Z_to_bv 64 0x81e50) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81e08) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m kb -> -> HRs HR0 HR1 Hk.
  eapply evt_cut; [eapply p12_ck1; [reflexivity | reflexivity | exact HRs | exact Hk]|].
  intros ms' (a1' & a2' & ->).
  do 3 step. if_true.
  eapply evt_cut; [eapply p12_ck2; [reflexivity | reflexivity | exact HRs | exact HR1 | exact Hk]|].
  intros ms'' (a1'' & a2'' & ->).
  apply evt_done. do 2 eexists. reflexivity.
Qed.

(* ---- the frame-loop prologue 0x81e50 -> 0x81ec4 (left_0 >= 1) or 0x82eac (left_0 = 0). Touched address ranges:
   reads [A+168, A+176), [A+208, A+224), [A+280, A+288); writes [A+88, A+104), [A+112, A+136), [A+144, A+152),
   [A+256, A+264) and the shadow bytes [S(fr)+370, S(fr)+386) (A = s1, S(fr) = s3). *)
Definition p12_W (Ab Sh : Z) : list (Z * Z) :=
  [(Ab + 88, Ab + 104); (Ab + 112, Ab + 136); (Ab + 144, Ab + 152); (Ab + 256, Ab + 264); (Sh + 370, Sh + 386)].

Lemma p12_body :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (nl Ab Sh fr : Z)
         (j88 j112 j144 j256 jsh : list byte),
    s9 = Z_to_bv 64 nl -> 0 <= nl < 2 ^ 64 -> s1 = Z_to_bv 64 Ab -> s3 = Z_to_bv 64 Sh ->
    0 <= Sh -> Sh + FRAME_SHADOW <= Ab -> Ab + 448 <= 2 ^ 64 -> 0 <= fr -> fr + FRAME_BYTES <= Ab ->
    rw_cells rsegs m (Ab + 88) [CB 16 j88] ->
    rw_cells rsegs m (Ab + 112) [CB 24 j112] ->
    rw_cells rsegs m (Ab + 144) [CB 8 j144] ->
    rw_cells rsegs m (Ab + 256) [CB 8 j256] ->
    ro_cells rsegs m (Ab + 168) [C8 (Z_to_bv 64 (fr + 2880))] ->
    ro_cells rsegs m (Ab + 208) [C8 (Z_to_bv 64 (fr + 2768))] ->
    ro_cells rsegs m (Ab + 216) [C8 (Z_to_bv 64 (fr + 448))] ->
    ro_cells rsegs m (Ab + 280) [C8 (Z_to_bv 64 (fr + 176))] ->
    rw_cells rsegs m (Sh + 370) [CB 16 jsh] ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (pc' : Z) (m' : word -> option byte),
         ms' = MS R Fr (Z_to_bv 64 pc') fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 26 = Z_to_bv 64 2147450880 /\ getr R 23 = s7 /\ getr R 25 = s9 /\
         getr R 13 = Z_to_bv 64 0 /\ getr R 27 = Z_to_bv 64 (-8) /\ getr R 22 = Z_to_bv 64 1 /\
         (pc' = 0x81ec4 /\ nl <> 0 \/ pc' = 0x82eac /\ nl = 0) /\
         UFr.munch (p12_W Ab Sh) m m' /\ UFr.wmono rsegs m m' /\
         q64 m' (Ab + 88) (fr + 2885) /\ q64 m' (Ab + 96) (fr + 180) /\
         q64 m' (Ab + 112) (fr + 186) /\ q64 m' (Ab + 120) (fragb fr + 15) /\ q64 m' (Ab + 128) (fragb fr + 19) /\
         q64 m' (Ab + 144) (fr + 452) /\ q64 m' (Ab + 256) (fragb fr + 8) /\
         (forall q, ~ UFr.outside (p12_W Ab Sh) q -> exists b, LMm.mrd rsegs m' (LMm.wa q) = Some b))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 2147450880) s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81e50) fc None m (seg_rom rsegs)).
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6
    Fr fc m nl Ab Sh fr j88 j112 j144 j256 jsh -> Hnl -> -> HSh HShA HA Hfr0 HfrA C88 C112 C144 C256
    R168 R208 R216 R280 CSH.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  pose proof (UFr.munch_refl (p12_W Ab Sh) m) as MU. unfold p12_W in MU.
  pose proof (UFr.wmono_refl rsegs m) as WM.
  do 2 step.                     (* 81e50 li a3,0; 81e54 li s11,-8 *)
  do 3 step.                     (* 81e58 ld a0,208(s1); 81e5c addi a1,a0,8; 81e60 sd a1,256(s1) *)
  do 2 step.                     (* 81e64 addi a1,a0,19; 81e68 sd a1,128(s1) *)
  do 2 step.                     (* 81e6c addi a0,a0,15; 81e70 sd a0,120(s1) *)
  do 3 step.                     (* 81e74 ld a0,168(s1); 81e78 addi a0,a0,5; 81e7c sd a0,88(s1) *)
  do 3 step.                     (* 81e80 ld a1,280(s1); 81e84 addi a0,a1,10; 81e88 sd a0,112(s1) *)
  do 2 step.                     (* 81e8c addi a0,a1,4; 81e90 sd a0,96(s1) *)
  do 3 step.                     (* 81e94 ld a0,216(s1); 81e98 addi a0,a0,4; 81e9c sd a0,144(s1) *)
  step.                          (* 81ea0 li s6,1 *)
  (* the shadow byte -8 as a non-negative literal, so the 1-byte stores below normalize *)
  replace (Z_to_bv 64 (-8)) with (Z_to_bv 64 18446744073709551608)
    by (apply bv_eq; vm_compute; reflexivity).
  do 8 step.                     (* 81ea4-81ec0 sb s11,382/383/384/385/370/372/376/380(s3) *)
  assert (HRD : forall q, ~ UFr.outside (p12_W Ab Sh) q -> exists b, LMm.mrd rsegs m0 (LMm.wa q) = Some b).
  { intros q Hq. unfold p12_W in Hq. cbn [UFr.outside] in Hq.
    destruct (Z_lt_le_dec q (Ab + 88)) as [L1|L1].
    - destruct (Z_lt_le_dec q (Sh + 370)) as [L2|L2]; [exfalso; apply Hq; lia|].
      destruct (Z_lt_le_dec q (Sh + 386)) as [L3|L3]; [|exfalso; apply Hq; lia].
      apply (p12_rw_rd m0 (Sh + 370) _ q CSH). cbn [cells_size csize Nat.add]. lia.
    - destruct (Z_lt_le_dec q (Ab + 104)) as [L2|L2].
      + apply (p12_rw_rd m0 (Ab + 88) _ q C88). cbn [cells_size csize Nat.add]. lia.
      + destruct (Z_lt_le_dec q (Ab + 112)) as [L3|L3]; [exfalso; apply Hq; lia|].
        destruct (Z_lt_le_dec q (Ab + 136)) as [L4|L4].
        * apply (p12_rw_rd m0 (Ab + 112) _ q C112). cbn [cells_size csize Nat.add]. lia.
        * destruct (Z_lt_le_dec q (Ab + 144)) as [L5|L5]; [exfalso; apply Hq; lia|].
          destruct (Z_lt_le_dec q (Ab + 152)) as [L6|L6].
          -- apply (p12_rw_rd m0 (Ab + 144) _ q C144). cbn [cells_size csize Nat.add]. lia.
          -- destruct (Z_lt_le_dec q (Ab + 256)) as [L7|L7]; [exfalso; apply Hq; lia|].
             destruct (Z_lt_le_dec q (Ab + 264)) as [L8|L8]; [|exfalso; apply Hq; lia].
             apply (p12_rw_rd m0 (Ab + 256) _ q C256). cbn [cells_size csize Nat.add]. lia. }
  destruct (Z.eq_dec nl 0) as [->|Hne].
  - step. if_false. step.        (* 81ec4 bnez s9 (not taken); 81ec8 j 82eac *)
    apply evt_done. eexists _, 0x82eac, _. split; [reflexivity|].
    do 10 (split; [reflexivity|]).
    split; [apply bv_eq; vm_compute; reflexivity|].
    split; [reflexivity|].
    split; [right; split; reflexivity|].
    split; [exact MU|]. split; [exact WM|].
    split; [p12_q C88 0%nat|]. split; [p12_q C88 8%nat|].
    split; [p12_q C112 0%nat|]. split; [p12_q C112 8%nat|]. split; [p12_q C112 16%nat|].
    split; [p12_q C144 0%nat|]. split; [p12_q C256 0%nat|].
    exact HRD.
  - apply evt_done. eexists _, 0x81ec4, _. split; [reflexivity|].
    do 10 (split; [reflexivity|]).
    split; [apply bv_eq; vm_compute; reflexivity|].
    split; [reflexivity|].
    split; [left; split; [reflexivity | exact Hne]|].
    split; [exact MU|]. split; [exact WM|].
    split; [p12_q C88 0%nat|]. split; [p12_q C88 8%nat|].
    split; [p12_q C112 0%nat|]. split; [p12_q C112 8%nat|]. split; [p12_q C112 16%nat|].
    split; [p12_q C144 0%nat|]. split; [p12_q C256 0%nat|].
    exact HRD.
Qed.
(* An address below or above each of the five intervals of the segment's write set. *)
Ltac p12_out := cbn [p12_W LFr.outside]; repeat split; first [lia | exact I].


(* S_P12: Hat (Inv_B81ec4_at) 0 -> Hcut Inv_B82eac -> Hcut Inv_B81e08, over the official v1.9 cuts. *)
Lemma seg_P12 : Hat B APIf ra (Inv_B81ec4_at B APIf ra) 0%nat -> Hcut B APIf ra (Inv_B82eac B APIf ra) ->
  Hcut B APIf ra (Inv_B81e08 B APIf ra).
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros Hloop Hepi g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (regs & mem & md & fr & Ec & HFRA & HENT & Hn & HOUR & HPRO & HPL & Ha0 & HKNT).
  subst c. rewrite SEGS.
  pose proof (fra_app B APIf ra g fr [] regs mem md HFRA) as (HGTfr & Happ).
  pose proof HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr40 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  pose proof HRT as (HAC0 & HSW0 & _).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS _ mem md HAH) as Hhigh.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HHM : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  assert (HAPPv : APPMEM_END = 140737488355328) by reflexivity.
  assert (HGTv : AC.GT = 0x5fe000) by reflexivity.
  pose proof Hwin as (Hw0 & Hw1 & _).
  assert (HA64 : HIGHMEM_BEG <= A /\ A + 448 <= APPMEM_END) by lia.
  assert (Hfr0 : 0 <= fr) by lia.
  assert (Hfr8 : fr mod 8 = 0) by (Z.div_mod_to_equations; lia).
  (* the frame's FRAME_SHADOW shadow bytes are shadow addresses, below the high application memory *)
  assert (HshIS : forall x, Sfr fr <= x < Sfr fr + FRAME_SHADOW -> in_shadow x).
  { intros x Hx.
    assert (Hdiv : (fr + 8 * (x - Sfr fr)) / 8 = fr / 8 + (x - Sfr fr)).
    { replace (8 * (x - Sfr fr)) with ((x - Sfr fr) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
    assert (Hin : fr <= fr + 8 * (x - Sfr fr) < fr + FRAME_BYTES) by lia.
    pose proof (shadow_of_app (fr + 8 * (x - Sfr fr)) (Happ _ Hin)) as His.
    replace (shadow_addr (fr + 8 * (x - Sfr fr))) with x in His; [exact His|].
    unfold shadow_addr. rewrite Hdiv. unfold Sfr, shadow_addr. lia. }
  assert (HK3b : LOWMEM_END <= Sfr fr /\ Sfr fr + FRAME_SHADOW <= HIGHMEM_BEG).
  { pose proof (HshIS (Sfr fr) ltac:(lia)) as H1. pose proof (HshIS (Sfr fr + FRAME_SHADOW - 1) ltac:(lia)) as H2.
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in H1, H2.
    unfold LOWMEM_END, HIGHMEM_BEG. lia. }
  assert (HLM : LOWMEM_END = 2147450880) by reflexivity.
  assert (HbvA : bv_unsigned (getr regs 9) = A) by (unfold rg in Hr9; rewrite Hr9; apply MState.unsigned_lit; lia).
  destruct HPRO as (HPRA & H152 & H264 & HAD6 & H160).
  pose proof HPRA as (H136 & H280 & H168 & H192 & H200 & H216 & H104 & H288 & H296 & H304 & _).
  pose proof HPL as ((Hc0 & H23 & H25) & HID & HFG & HRAD & H176 & H208 & HFS0).
  (* the cells the prologue reads and writes *)
  destruct (stk_junk mem (g_S g - AF.SLOT_STACK) (g_S g) (A + 88) 16 Hwin ltac:(lia) ltac:(lia)) as (j88 & C88).
  destruct (stk_junk mem (g_S g - AF.SLOT_STACK) (g_S g) (A + 112) 24 Hwin ltac:(lia) ltac:(lia)) as (j112 & C112).
  destruct (stk_junk mem (g_S g - AF.SLOT_STACK) (g_S g) (A + 144) 8 Hwin ltac:(lia) ltac:(lia)) as (j144 & C144).
  destruct (stk_junk mem (g_S g - AF.SLOT_STACK) (g_S g) (A + 256) 8 Hwin ltac:(lia) ltac:(lia)) as (j256 & C256).
  assert (R168 : ro_cells rsegs mem (A + 168) [C8 (Z_to_bv 64 (fr + 2880))])
    by (apply ro8; exact (tp_spill_q regs mem A 168 (fr + 2880) Hr9 ltac:(lia) ltac:(lia) H168)).
  assert (R208 : ro_cells rsegs mem (A + 208) [C8 (Z_to_bv 64 (fr + 2768))])
    by (apply ro8; exact (tp_spill_q regs mem A 208 (fragb fr) Hr9 ltac:(lia) ltac:(lia) H208)).
  assert (R216 : ro_cells rsegs mem (A + 216) [C8 (Z_to_bv 64 (fr + 448))])
    by (apply ro8; exact (tp_spill_q regs mem A 216 (fr + 448) Hr9 ltac:(lia) ltac:(lia) H216)).
  assert (R280 : ro_cells rsegs mem (A + 280) [C8 (Z_to_bv 64 (fr + 176))])
    by (apply ro8; exact (tp_spill_q regs mem A 280 (fr + 176) Hr9 ltac:(lia) ltac:(lia) H280)).
  assert (HstkSh : stk rsegs mem (Sfr fr) (Sfr fr + FRAME_SHADOW)).
  { unfold Sfr. apply (shadow_stk mem fr FRAME_SHADOW HSW0); [lia | exact Hfr8 | lia |].
    intros x Hx. apply Happ. lia. }
  destruct (stk_junk mem (Sfr fr) (Sfr fr + FRAME_SHADOW) (Sfr fr + 370) 16 HstkSh ltac:(lia) ltac:(lia))
    as (jsh & CSH).
  (* the two name bytes and their shadow byte *)
  pose proof (p12_qmark mem Hro) as Hq.
  assert (HQ0 : ov_read_bytes rsegs mem (wa 135648) 1 = Some [Z_to_bv 8 63]).
  { pose proof (UMm.bytes_at_ov_read rsegs mem QMARK [Z_to_bv 8 63; Z_to_bv 8 0] 0 1 Hq ltac:(cbn; lia)) as HH.
    cbn [Z.of_nat firstn skipn] in HH. rewrite Z.add_0_r in HH. exact HH. }
  assert (HQ1 : ov_read_bytes rsegs mem (wa 135649) 1 = Some [Z_to_bv 8 0]).
  { pose proof (UMm.bytes_at_ov_read rsegs mem QMARK [Z_to_bv 8 63; Z_to_bv 8 0] 1 1 Hq ltac:(cbn; lia)) as HH.
    cbn [Z.of_nat firstn skipn] in HH. exact HH. }
  assert (HinQ0 : in_globals AF.frame_AG QMARK).
  { exists QMARK, 2. split; [unfold AF.frame_AG, QMARK; cbn; tauto|]. lia. }
  assert (HinQ1 : in_globals AF.frame_AG (QMARK + 1)).
  { exists QMARK, 2. split; [unfold AF.frame_AG, QMARK; cbn; tauto|]. lia. }
  destruct (HAG QMARK HinQ0) as (_ & _ & _ & HAD0).
  destruct (HAG (QMARK + 1) HinQ1) as (_ & _ & _ & HAD1).
  destruct (HAD0 0 ltac:(lia)) as (_ & kb & Hkb0 & Hok0).
  destruct (HAD1 0 ltac:(lia)) as (_ & kb' & Hkb1 & Hok1).
  rewrite Z.add_0_r in Hkb0, Hok0, Hkb1, Hok1.
  assert (Hsame : shadow_addr (QMARK + 1) = shadow_addr QMARK)
    by (unfold shadow_addr, QMARK; reflexivity).
  rewrite Hsame in Hkb1.
  assert (Hkbe : kb' = kb) by (rewrite Hkb0 in Hkb1; injection Hkb1 as ->; reflexivity).
  subst kb'.
  assert (Hk : bv_signed kb = 0 \/ 2 <= bv_signed kb <= 7).
  { unfold shadow_ok, QMARK in Hok0, Hok1. cbn in Hok0, Hok1. lia. }
  assert (HRs : ov_read_bytes rsegs mem (wa 2147467836) 1 = Some [kb]).
  { apply mrd_read1; [| lia | lia].
    replace 2147467836 with (shadow_addr QMARK) by (unfold shadow_addr, QMARK, ASAN_K; reflexivity).
    exact Hkb0. }
  (* the registers the checks and the prologue read *)
  assert (Ha0r : getr regs 10 = Z_to_bv 64 135648)
    by (unfold a0v, rg in Ha0; rewrite Ha0; unfold QMARK; reflexivity).
  assert (Hs10 : getr regs 26 = Z_to_bv 64 2147450880) by (unfold rg in Hr26; exact Hr26).
  assert (Hnl : 0 <= g_n g - c0 (g_in g) < 2 ^ 64) by lia.
  apply (sl_run regs (Z_to_bv 64 0x81e08) mem md
    (fun R pc' mem' => (pc' = Z_to_bv 64 0x81ec4 /\ g_n g - c0 (g_in g) <> 0 \/
                        pc' = Z_to_bv 64 0x82eac /\ g_n g - c0 (g_in g) = 0) /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
       getr R 26 = getr regs 26 /\ getr R 23 = getr regs 23 /\ getr R 25 = getr regs 25 /\
       getr R 13 = Z_to_bv 64 0 /\ getr R 27 = Z_to_bv 64 (-8) /\ getr R 22 = Z_to_bv 64 1 /\
       UFr.munch (p12_W A (Sfr fr)) mem mem' /\ UFr.wmono rsegs mem mem' /\
       q64 mem' (A + 88) (fr + 2885) /\ q64 mem' (A + 96) (fr + 180) /\
       q64 mem' (A + 112) (fr + 186) /\ q64 mem' (A + 120) (fragb fr + 15) /\
       q64 mem' (A + 128) (fragb fr + 19) /\ q64 mem' (A + 144) (fr + 452) /\ q64 mem' (A + 256) (fragb fr + 8) /\
       (forall q, ~ UFr.outside (p12_W A (Sfr fr)) q -> exists b, LMm.mrd rsegs mem' (LMm.wa q) = Some b))
    (Post B APIf ra g)).
  - exact Hhalt.
  - eapply evt_mono.
    { unfold Regs6ss.mkR_of.
      eapply evt_cut.
      { eapply p12_chk; [exact Ha0r | exact Hs10 | exact HRs | exact HQ0 | exact HQ1 | exact Hk]. }
      intros ms' (a1' & a2' & ->).
      eapply p12_body with (fr := fr);
        [exact H25 | exact Hnl | exact Hr9 | exact Hr19 | lia | lia | lia | lia | lia
        | exact C88 | exact C112 | exact C144 | exact C256 | exact R168 | exact R208 | exact R216 | exact R280
        | exact CSH]. }
    { intros ms' (R & pc' & m' & E & K2 & K3 & K4 & K8 & K9 & K19 & K26 & K23 & K25 & K13 & K27 & K22 &
        Hpc & MU & WM & Q88 & Q96 & Q112 & Q120 & Q128 & Q144 & Q256 & HRD).
      exists R, (Z_to_bv 64 pc'), m'. split; [exact E|].
      split.
      { destruct Hpc as [(-> & Hne)|(-> & He)]; [left; split; [reflexivity | exact Hne]
                                                | right; split; [reflexivity | exact He]]. }
      split; [exact K2|]. split; [exact K3|]. split; [exact K4|]. split; [exact K8|].
      split; [exact K9|]. split; [exact K19|].
      split; [transitivity (Z_to_bv 64 2147450880); [exact K26 | symmetry; exact Hs10]|].
      split; [exact K23|]. split; [exact K25|]. split; [exact K13|]. split; [exact K27|].
      split; [exact K22|].
      split; [exact MU|]. split; [exact WM|].
      split; [exact Q88|]. split; [exact Q96|]. split; [exact Q112|]. split; [exact Q120|].
      split; [exact Q128|]. split; [exact Q144|]. split; [exact Q256 | exact HRD]. }
  - intros R pc' mem' regs' md'
      (Hpc & K2 & K3 & K4 & K8 & K9 & K19 & K26 & K23 & K25 & K13 & K27 & K22 & MU & WM &
       Q88 & Q96 & Q112 & Q120 & Q128 & Q144 & Q256 & HRD)
      Hreg Hmat.
    assert (E2 : getr regs' 2 = getr regs 2) by (rewrite Hreg; exact K2).
    assert (E3 : getr regs' 3 = getr regs 3) by (rewrite Hreg; exact K3).
    assert (E4 : getr regs' 4 = getr regs 4) by (rewrite Hreg; exact K4).
    assert (E8 : getr regs' 8 = getr regs 8) by (rewrite Hreg; exact K8).
    assert (E9 : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact K9).
    assert (E19 : getr regs' 19 = getr regs 19) by (rewrite Hreg; exact K19).
    assert (E26 : getr regs' 26 = getr regs 26) by (rewrite Hreg; exact K26).
    (* the shadow bytes the run writes lie below the spill base *)
    assert (HShA : Sfr fr + FRAME_SHADOW <= A) by lia.
    (* an address (p12_W A (Sfr fr)) holds is a frame shadow byte or a spill of the save area *)
    assert (HCL : forall q, ~ LFr.outside (p12_W A (Sfr fr)) q ->
              (fr + 24 <= q < fr + FRAME_BYTES) \/ (Sfr fr <= q < Sfr fr + FRAME_SHADOW) \/
              (AC.aspZ regs - FN_STACK <= q < AC.aspZ regs) \/
              (bv_unsigned (getr regs 9) + 72 <= q < bv_unsigned (getr regs 9) + 336)).
    { intros q Hqo. unfold p12_W in Hqo. cbn [LFr.outside] in Hqo. rewrite HbvA.
      destruct (Z_lt_le_dec q (Sfr fr)) as [L1|L1]; [exfalso; apply Hqo; lia|].
      destruct (Z_lt_le_dec q (Sfr fr + FRAME_SHADOW)) as [L2|L2]; [right; left; lia|].
      right; right; right. lia. }
    assert (HRDl : forall q, ~ LFr.outside (p12_W A (Sfr fr)) q -> exists b, LMm.mrd rsegs mem' (LMm.wa q) = Some b).
    { intros q Hqo. apply HRD. intro Hc. apply Hqo. apply (fr_outside_lib (p12_W A (Sfr fr)) q). exact Hc. }
    assert (MUl : LFr.munch (p12_W A (Sfr fr)) mem mem') by exact MU.
    assert (WMl : LFr.wmono rsegs mem mem') by exact WM.
    assert (HD : rt_disjoint (p12_W A (Sfr fr))).
    { unfold p12_W, rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
        RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG,
        RT_AGLOB, RT_AGLOB_LEN.
      cbn [disjoint_from]. repeat split; first [left; lia | exact I]. }
    assert (HROm : ro_agree rsegs mem').
    { apply (sl_ro_keep (p12_W A (Sfr fr)) mem mem' Hro MUl). intros x Hx. unfold AC.GT in Hx. p12_out. }
    destruct (tp_fra_ent B APIf ra empty FF g fr [] regs mem mem' md (p12_W A (Sfr fr)) HFRA HENT MUl WMl HD HROm HCL HRDl)
      as (HFRAm & HENTm).
    assert (HFRA' : FRA B APIf ra g fr [] regs' mem' md').
    { apply (sl_fra_move B APIf ra g fr [] regs regs' mem' md md' HFRAm
               E2 E3 E4 E8 E9 E19 E26 Hmat). }
    assert (HENT' : ENT APIf g [] mem' md') by (eapply ent_mat; [exact HENTm | exact Hmat]).
    (* the frame body and its records are outside the write set *)
    assert (HWfr : forall x, fr <= x < fr + FRAME_BYTES -> LFr.outside (p12_W A (Sfr fr)) x).
    { intros x Hx. unfold p12_W. cbn [LFr.outside].
      pose proof (app_not_shadow x (Happ x Hx)) as Hns.
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [|exact I].
      intros Hb. apply Hns. apply HshIS. lia. }
    (* a frame shadow byte below S(fr) + 370 is outside every interval of (p12_W A (Sfr fr)) *)
    assert (HWsh : forall off, 0 <= off < 370 -> LFr.outside (p12_W A (Sfr fr)) (Sfr fr + off)).
    { intros off Hoff. p12_out. }
    assert (HOUR' : OURb g fr mem').
    { unfold OURb in *. eapply fl_bytes; [exact HOUR | exact MUl |].
      rewrite OUR_length. intros x Hx. change (Z.of_nat 6) with 6 in Hx. apply HWfr; lia. }
    assert (HID' : IDBe g fr RcIdentModel.ID0 mem').
    { unfold IDBe in *. eapply fl_bytes; [exact HID | exact MUl |].
      unfold RcIdentModel.ID0. rewrite repeat_length. unfold RcIdentModel.ID_SIZE.
      intros x Hx. change (Z.of_nat 38) with 38 in Hx. apply HWfr; lia. }
    assert (HFG' : FGBe g fr z72 mem').
    { unfold FGBe in *. eapply fl_bytes; [exact HFG | exact MUl |].
      unfold z72. rewrite repeat_length.
      intros x Hx. change (Z.of_nat 72) with 72 in Hx. apply HWfr; lia. }
    (* the addressable ranges: their shadow bytes are frame shadow bytes below S(fr) + 370 *)
    assert (HADsh : forall p n i, fr <= p -> p + n <= fr + 2960 -> 0 <= i < n ->
              LFr.outside (p12_W A (Sfr fr)) (shadow_addr (p + i))).
    { intros p n i Hp Hpn Hi.
      assert (Hlo : Sfr fr <= shadow_addr (p + i))
        by (pose proof (tp_sh_ge fr (p + i) 0 Hfr8 ltac:(lia) ltac:(lia)) as HH; lia).
      assert (Hhi : shadow_addr (p + i) < Sfr fr + 370) by (apply (tp_sh_lt fr (p + i) 370); lia).
      replace (shadow_addr (p + i)) with (Sfr fr + (shadow_addr (p + i) - Sfr fr)) by lia.
      apply HWsh. lia. }
    assert (HAD6' : addressable mem' (fr + 2624) 6).
    { apply (addr_run (p12_W A (Sfr fr)) mem mem' (fr + 2624) 6 HAD6 MUl).
      intros i Hi. exact (HADsh (fr + 2624) 6 i ltac:(lia) ltac:(lia) Hi). }
    destruct HRAD as (HRAD1 & HRAD2 & HRAD3).
    assert (HRAD1' : addressable mem' (fr + 2688) 38).
    { apply (addr_run (p12_W A (Sfr fr)) mem mem' (fr + 2688) 38 HRAD1 MUl).
      intros i Hi. exact (HADsh (fr + 2688) 38 i ltac:(lia) ltac:(lia) Hi). }
    assert (HRAD2' : addressable mem' (fragb fr) 72).
    { apply (addr_run (p12_W A (Sfr fr)) mem mem' (fragb fr) 72 HRAD2 MUl). unfold fragb.
      intros i Hi. exact (HADsh (fr + 2768) 72 i ltac:(lia) ltac:(lia) Hi). }
    assert (HRAD3' : addressable mem' (fr + 2880) 40).
    { apply (addr_run (p12_W A (Sfr fr)) mem mem' (fr + 2880) 40 HRAD3 MUl).
      intros i Hi. exact (HADsh (fr + 2880) 40 i ltac:(lia) ltac:(lia) Hi). }
    (* the kind-name table (KNT, adopt 11): its bytes and their shadow bytes are image addresses below GT <= fr *)
    assert (HKNv : KIND_NAME = 652672) by reflexivity.
    assert (HKNlen : length kind_name_bytes = 112%nat) by reflexivity.
    assert (HKNT' : KNT mem').
    { destruct HKNT as (HKb & HKa). split.
      - eapply fl_bytes; [exact HKb | exact MUl |].
        intros x Hx. rewrite HKNlen, HKNv in Hx. cbn [Z.of_nat] in Hx. p12_out.
      - apply (addr_run (p12_W A (Sfr fr)) mem mem' KIND_NAME 112 HKa MUl).
        intros i Hi.
        assert (Hlt : shadow_addr (KIND_NAME + i) < Sfr fr)
          by (pose proof (tp_sh_lt fr (KIND_NAME + i) 0 Hfr8 ltac:(lia) ltac:(lia) ltac:(lia)) as HH; lia).
        p12_out. }
    assert (HstkF : stk rsegs mem' fr (fr + FRAME_BYTES)) by exact (fra_stk B APIf ra g fr [] regs' mem' md' HFRA').
    (* the turn-0 first-fragment state (the local `first`, frame body bytes above fr + 2880) is not written *)
    assert (HFS0' : FSj g fr 0 regs' mem').
    { apply (Tac_ro.fsj_keep g fr 0 regs regs' mem mem' HFS0); [|exact HRAD3'].
      intros a bs Ha Hab Hb. eapply fl_bytes; [exact Hb | exact MUl |].
      intros x Hx. apply HWfr. lia. }
    (* the spills the run does not write *)
    assert (HSPkeep : forall off v, (off = 104 \/ off = 136 \/ off = 152 \/ off = 160 \/ off = 168 \/
                       off = 176 \/ off = 192 \/ off = 200 \/ off = 208 \/ off = 216 \/ off = 264 \/
                       off = 280 \/ off = 288 \/ off = 296 \/ off = 304) ->
              spill regs mem off v -> spill regs' mem' off v).
    { intros off v Hoff Hs.
      apply (tp_spill_keep regs regs' mem mem' (p12_W A (Sfr fr)) A off v Hr9 E9 ltac:(unfold APPMEM_END; lia) ltac:(lia) Hs MUl).
      intros x Hx. p12_out. }
    (* the spills the run wrote, at the base register 9 holds *)
    assert (HQ : forall off v, q64 mem' (A + off) v -> spill regs' mem' off v)
      by (intros off v Hq'; exists A; split; [unfold rg; rewrite E9; exact Hr9 | exact Hq']).
    assert (HFLI : FLI g fr regs' mem').
    { unfold FLI.
      split; [unfold rg; rewrite Hreg; exact K27|].
      split; [exact (HSPkeep 168 (fr + 2880) ltac:(tauto) H168)|].
      split; [exact (HQ 96 (fr + 180) Q96)|].
      split; [exact (HQ 112 (fr + 186) Q112)|].
      split; [exact (HQ 120 (fragb fr + 15) Q120)|].
      split; [exact (HQ 128 (fragb fr + 19) Q128)|].
      split; [exact (HSPkeep 136 (fr + 160) ltac:(tauto) H136)|].
      split; [exact (HQ 144 (fr + 452) Q144)|].
      split; [exact (HSPkeep 152 (fr + 64) ltac:(tauto) H152)|].
      split; [exact (HSPkeep 280 (fr + 176) ltac:(tauto) H280)|].
      split; [exact (HSPkeep 160 (fr + 32) ltac:(tauto) H160)|].
      split; [exact (HSPkeep 176 (fr + 2688) ltac:(tauto) H176)|].
      split; [exact (HSPkeep 192 (fr + 528) ltac:(tauto) H192)|].
      split; [exact (HSPkeep 200 (fr + 336) ltac:(tauto) H200)|].
      split; [exact (HSPkeep 216 (fr + 448) ltac:(tauto) H216)|].
      split; [exact (HSPkeep 208 (fragb fr) ltac:(tauto) H208)|].
      split; [exact (HSPkeep 104 (fr + 128) ltac:(tauto) H104)|].
      split; [exact (HQ 256 (fragb fr + 8) Q256)|].
      split; [exact (HSPkeep 264 (fr + 2624) ltac:(tauto) H264)|].
      split; [exact (HSPkeep 288 (fr + 256) ltac:(tauto) H288)|].
      split; [exact (HSPkeep 296 (fr + 304) ltac:(tauto) H296)|].
      split; [exact (HSPkeep 304 (fr + 272) ltac:(tauto) H304)|].
      split; [exact HAD6'|]. split; [exact HstkF|].
      split; [split; [exact HRAD1' | split; [exact HRAD2' | exact HRAD3']]|].
      split; [exact HKNT'|].
      split; [exact (HSPkeep 168 (fr + 2880) ltac:(tauto) H168) | exact (HQ 88 (fr + 2885) Q88)]. }
    assert (HCUR' : CUR g (c0 (g_in g)) regs').
    { unfold CUR, rg in *. rewrite !Hreg, K23, K25. split; [lia|]. split; [exact H23 | exact H25]. }
    assert (HPL' : PL0 g fr regs' mem').
    { unfold PL0. split; [exact HCUR'|]. split; [exact HID'|]. split; [exact HFG'|].
      split; [split; [exact HRAD1' | split; [exact HRAD2' | exact HRAD3']]|].
      split; [exact (HSPkeep 176 (fr + 2688) ltac:(tauto) H176)|].
      split; [exact (HSPkeep 208 (fragb fr) ltac:(tauto) H208) | exact HFS0']. }
    destruct Hpc as [(-> & Hne)|(-> & He)].
    + (* left_0 >= 1: the frame-loop head at turn 0 *)
      assert (HI : Inv_B81ec4_at B APIf ra g 0%nat
                     (mkCfg (mkst regs' (Z_to_bv 64 0x81ec4) mem' (seg_rom rsegs)) md')).
      { exists regs', mem', md', fr. rewrite SEGS. split; [reflexivity|].
        split; [exact HFRA'|]. split; [exact HENT'|]. split; [exact Hn|].
        assert (Et : t_c (g_in g) 0 = c0 (g_in g)) by reflexivity.
        assert (El : t_left (g_in g) 0 = g_n g - c0 (g_in g)) by reflexivity.
        assert (Eid : t_ID (g_in g) 0 = RcIdentModel.ID0) by reflexivity.
        assert (Efg : t_FG (g_in g) 0 = z72) by reflexivity.
        split.
        { unfold LI, IFS, IDj, FGj, IDb, FGb. rewrite Et, El, Eid, Efg.
          split; [lia|].
          split; [unfold rg; rewrite Hreg; exact K13|].
          split; [exact HOUR'|].
          split; [exact HCUR'|].
          split; [lia|].
          split.
          { split; [split; [exact HID' | exact id_ok_ID0]|].
            split; [split; [exact HFG' | exact p12_frag_ok_z72] | exact HFS0']. }
          exact HFLI. }
        split; [exact (fra_f1_in B APIf ra g fr [] regs' mem' md' HFRA' ltac:(unfold c0, nlen in *; lia))|].
        split; [exact (HSPkeep 280 (fr + 176) ltac:(tauto) H280) | unfold rg; rewrite Hreg; exact K22]. }
      pose proof (Hloop g _ HI) as HSR. rewrite SEGS in HSR. exact HSR.
    + (* left_0 = 0 (n <= 7): the epilogue cut *)
      destruct (x1_entry_of_pl0 g fr regs' mem' HPL') as (X176 & Xnm & Xad).
      assert (HI : Inv_B82eac B APIf ra g (mkCfg (mkst regs' (Z_to_bv 64 0x82eac) mem' (seg_rom rsegs)) md')).
      { exists regs', mem', md', fr. rewrite SEGS. split; [reflexivity|].
        split; [exact HFRA'|]. split; [exact HENT'|]. split; [exact Hn|].
        split; [exact HOUR'|]. split; [exact X176|]. split; [exact Xnm | exact Xad]. }
      pose proof (Hepi g _ HI) as HSR. rewrite SEGS in HSR. exact HSR.
Qed.

End P12.
