(* WireCmSegsRel: cm_seg8_F, the piece 0x80568 -> the `ret` at 0x80608 of the footprint (lib/Lib/ExecF.v evtF) walk of
   check_meter (fuzz_wire.asan 0x80340), stepped by lib/Lib/StepF.v. The list of the walk's pieces is the header of
   lib/A/Prog/WireCmSegs.v; its cm_seg1_F leaves the thirteen saved words as the block cm_frhi at entry sp - 0x60 and
   its cm_seg2_F the fake frame FA with its eight shadow bytes. Form: reac-repacer/fuzz_uci lib/A/Prog/UciCvSegs.v.
   The piece (s0 = the entry sp, s2 = s6 = FA, s7 = the shadow address of FA):
     0x80568 `li a0, -8`, 0x8056c `sb a0, 4(s7)`: the shadow byte of the local at FA + 0x20 := 0xf8 (poisoned again);
     0x80570 `lui a0, 0x45e03`, 0x80574 `addiw a0, a0, 1550`: a0 := 0x45e0360e;
     0x80578 `sd a0, 0(s6)`: the first header word of the fake frame := 0x45e0360e (the frame is retired);
     0x8057c `beqz s2` to 0x805b0: not taken, FA >= 4096;
     0x80580 `li a0, -11`, 0x80584 .. 0x805a0 eight `sb a0`: the shadow bytes 4, 5, 6, 7, 0, 1, 2, 3 of FA := 0xf5;
     0x805a4 `ld a0, 56(s2)`: a0 := FL, the flag pointer the word at FA + 56 holds;
     0x805a8 `sb zero, 0(a0)`: the flag byte at FL := 0 (the fake frame is given back); 0x805ac `j 0x805d0`;
     0x805d0 `addi sp, s0, -128`, 0x805d4 .. 0x80600 the twelve `ld` of ra, s0 .. s10 from the cells of cm_frhi,
     0x80604 `addi sp, sp, 128`: sp := the entry sp; 0x80608 `ret`.
   Memory is written only in [FA, FA + 64), its eight shadow bytes and the flag byte at FL. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import
PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import AsanKA AsanKAProof.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import ExecF StepF.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require rp_meter_counter_c check_meter.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import WireCmSegs.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module PMC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_meter_counter_c.

(* A 64-byte block whose bytes at offset 56 are the word v, kept as 56 bytes and the cell C8 v, so that the `ld` of
   offset 56 reads v out of the cell. *)
Lemma cm_c8_at56 : forall m A j v,
  rw_cells rsegs m A [CB 64 j] -> bytes_at rsegs m (A + 56) (le8 v) ->
  exists j1, rw_cells rsegs m A [CB 56 j1; C8 v].
Proof.
  intros m A j v [[Hwf Hb] Hw] B.
  cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [Hl _].
  cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
  rewrite <- (firstn_skipn 56 j) in Hb.
  apply bytes_at_app in Hb. destruct Hb as [Hb1 Hb2].
  assert (L1 : length (firstn 56 j) = 56%nat) by (rewrite length_firstn; lia).
  assert (L2 : length (skipn 56 j) = 8%nat) by (rewrite length_skipn; lia).
  rewrite L1 in Hb2. change (Z.of_nat 56) with 56 in Hb2.
  assert (E : skipn 56 j = le8 v).
  { pose proof (bytes_at_ov_read rsegs m (A + 56) _ 0 8 Hb2 ltac:(rewrite L2; lia)) as R1.
    pose proof (bytes_at_ov_read rsegs m (A + 56) _ 0 8 B ltac:(rewrite length_le8; lia)) as R2.
    assert (F1 : firstn 8 (skipn 56 j) = skipn 56 j) by (apply firstn_all2; lia).
    assert (F2 : firstn 8 (le8 v) = le8 v) by (apply firstn_all2; rewrite length_le8; lia).
    rewrite skipn_O, F1 in R1. rewrite skipn_O, F2 in R2.
    rewrite R1 in R2. congruence. }
  exists (firstn 56 j). split; [split|].
  - cbn [cells_wf cell_wf]. split; [exact L1|]. split; exact I.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_at_app. split; [exact Hb1|].
    rewrite L1, <- E. exact Hb2.
  - exact Hw.
Qed.

(* ------------------------------------------------------------------ *)
(* cm_seg8_F : 0x80568 -> the `ret` at 0x80608                         *)
(* ------------------------------------------------------------------ *)

Lemma cm_seg8_F :
  forall (RNG : ExecF.footprint)
         (ra0 a00 gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s11 t3 t4 t5 t6 : word)
         (c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (SP SP1 FA FL f n eo want : Z) (jF jsh : list byte) (fb : byte),
    SP - 144 <= SP1 <= SP - 128 -> 0 <= SP - 144 -> SP <= 2 ^ 47 ->
    4096 <= FA -> FA + 64 <= 2 ^ 47 -> 4096 <= FL -> FL + 1 <= 2 ^ 47 ->
    FA + 64 <= SP - 144 -> FA / 8 + ASAN_K + 8 <= SP - 144 ->
    FA / 8 + ASAN_K + 8 <= FA \/ FA + 64 <= FA / 8 + ASAN_K ->
    (FL + 1 <= FA \/ FA + 64 <= FL) ->
    (FL + 1 <= FA / 8 + ASAN_K \/ FA / 8 + ASAN_K + 8 <= FL) ->
    FL + 1 <= SP - 144 ->
    rw_cells rsegs m (SP - 96) (cm_frhi c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra) ->
    rw_cells rsegs m FA [CB 64 jF] ->
    rw_cells rsegs m (shadow_addr FA) [CB 8 jsh] ->
    rw_cells rsegs m FL [C1 fb] ->
    bytes_at rsegs m (FA + 56) (le8 (wa FL)) ->
    ExecF.rng RNG (SP - 144) 144 -> ExecF.rng RNG FA 64 -> ExecF.rng RNG (shadow_addr FA) 8 ->
    ExecF.rng RNG FL 1 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists m1,
         ms' = MS (mkR cra (Z_to_bv 64 SP) gp tp t0 t1 t2 c0 c1 (Z_to_bv 64 FL) a1 a2 a3 a4 a5 a6 a7
                     c2 c3 c4 c5 c6 c7 c8 c9 c10 s11 t3 t4 t5 t6)
                  F (ret_pc cra) fc None m1 (seg_rom rsegs) /\
         munch [(FA, FA + 64); (shadow_addr FA, shadow_addr FA + 8); (FL, FL + 1)] m m1 /\
         wmono rsegs m m1 /\
         bytes_at rsegs m1 FL [Z_to_bv 8 0])
      (MS (mkR ra0 (Z_to_bv 64 SP1) gp tp t0 t1 t2 (Z_to_bv 64 SP) (Z_to_bv 64 SP1)
             a00 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 FA) (Z_to_bv 64 f) (Z_to_bv 64 n) (Z_to_bv 64 (FA + 32)) (Z_to_bv 64 FA)
             (Z_to_bv 64 (shadow_addr FA)) (Z_to_bv 64 ASAN_K) (Z_to_bv 64 eo) (Z_to_bv 64 want)
             s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x80568) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 a00 gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s11 t3 t4 t5 t6
    c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra F fc m SP SP1 FA FL f n eo want jF jsh fb
    HSP1 HSP0 HSP2 HFA0 HFA1 HFL0 HFL1 HDF HDS HD HDL HDLS HDLF FRH FRF FRS FRL BFL RFR RFF RFS RFL.
  (* the flag pointer at FA + 56 as its own cell of the frame block *)
  destruct (cm_c8_at56 m FA jF (Z_to_bv 64 FL) FRF BFL) as [j1 FRF1]. clear FRF BFL.
  unfold shadow_addr, ASAN_K in *.
  (* the reloads address sp + 120 - 128 .. as entry sp - 8 .. entry sp - 96: the block's base in that shape *)
  unfold cm_frhi in FRH. change (SP - 96) with (SP + -96) in FRH.
  pose proof (munch_refl [(FA, FA + 64); (FA / 8 + 2147450880, FA / 8 + 2147450888); (FL, FL + 1)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (HFA8 : 0 <= FA / 8) by (apply Z.div_pos; lia).
  assert (B0 : bv_eqb (Z_to_bv 64 FA) (Z_to_bv 64 0) = false).
  { unfold bv_eqb. rewrite (unsigned_lit FA) by lia. fold_lit_ux. apply Z.eqb_neq. lia. }
  (* 0x80568 `li a0, -8`, 0x8056c `sb a0, 4(s7)`: the local's shadow byte := 0xf8 *)
  step. step.
  (* 0x80570 `lui`, 0x80574 `addiw`: a0 := 0x45e0360e; 0x80578 `sd a0, 0(s6)`: the header word retired *)
  step. step. step.
  (* 0x8057c `beqz s2`: s2 = FA <> 0, not taken *)
  step. rewrite B0; cbv iota.
  (* 0x80580 `li a0, -11` and the eight `sb a0, k(s7)`: the frame's shadow bytes := 0xf5 *)
  do 9 step.
  (* 0x805a4 `ld a0, 56(s2)`: a0 := FL; 0x805a8 `sb zero, 0(a0)`: the flag byte := 0; 0x805ac `j 0x805d0` *)
  step. step. step.
  (* 0x805d0 `addi sp, s0, -128`, the twelve reloads out of cm_frhi, 0x80604 `addi sp, sp, 128`, 0x80608 `ret` *)
  do 15 step.
  apply evtF_done. eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|].
  match goal with H : rw_cells rsegs _ FL [C1 _] |- _ => exact (proj2 (proj1 H)) end.
Qed.
