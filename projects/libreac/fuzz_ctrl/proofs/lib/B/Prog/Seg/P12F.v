(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v, with its module paths and module names changed; 754 of its 794 lines of code are new or changed and 356 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/F31.v, with its module paths, module names and addresses changed; 496 of its 556 lines of code are new or changed and 734 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/P12.v, with its module paths and module names changed; 165 of its 295 lines of code are new or changed and 426 lines of the source are left out. *)
(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
   source runs: lib/B/Prog/Seg/P12.v p12_ck1, p12_ck2, p12_chk, p12_body at
     a working branch 3803efccea0 (blob 1951f14dd81a0e7fcdf95fde352d190a617a57eb);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
         lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
   compare: the source runs are UL-engine evts (lib/B/Tk/UL/Exec.v), which the footprint kit has no twin of,
     so each _F lemma is re-stepped with lib.Lib StepF (runF-common brief) and p12_ul_evt bridges the
     lib.Lib msteps chain back to the UL one: p12_ck1_of_F, p12_ck2_of_F, p12_chk_of_F, p12_body_of_F
     re-derive the source statements of p12_ck1 (P12.v:143), p12_ck2 (:167), p12_chk (:192) and p12_body
     (:225) verbatim, checked by p12_ck1_same / p12_ck2_same / p12_chk_same / p12_body_same.  p12_body_F
     re-runs P12.v lines 263-314 (0x81e50 .. 0x81ec8); its cells premises are the lib.Lib ones
     (lib/Lib/Step.v rw_cells / ro_cells, the kit the footprint walk uses) in place of the UL copies of the
     source statement, and its munch / outside are the lib.Lib ones (lib/Lib/Frame.v), because the lib.Lib
     StepF store machinery carries those; p12_body_of_F crosses both back with the shared bridge
     lib/B/Tk/UL/CellBridge.v (rw_cells_ul_lib, ro_cells_ul_lib, munch_lib_ul, outside_lib_ul). *)
(* rule 24: no function proved. *)
(* Regions.  p12_ck1_F: the shadow byte of the name at QMARK, [2147467836, 2147467837).
   p12_ck2_F: that shadow byte and the second name byte [135649, 135650).
   p12_chk_F: both of those and the first name byte [135648, 135649).
   p12_body_F: reads [Ab + 168, Ab + 176), [Ab + 208, Ab + 224), [Ab + 280, Ab + 288); writes
   [Ab + 88, Ab + 104), [Ab + 112, Ab + 136), [Ab + 144, Ab + 152), [Ab + 256, Ab + 264) and the frame-shadow
   bytes [Sh + 370, Sh + 386).  The two instrumented checks load the shadow byte named above; the error path
   (the report entry) is not reached. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge Image.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.UL Require Exec Frame Mem Cells Step.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import reac_ctrl_kind_name_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require P12.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.UL Require CellBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.
Open Scope Z_scope.

Module LMm := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
Module UE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.UL.Exec.
Module UFr := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.UL.Frame.
Module UCe := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.UL.Cells.
Module USt := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.UL.Step.
Module CBR := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.UL.CellBridge.

(* The two engines step the same RiscvSemantics.step, so a lib.Lib run is a UL run. *)
Lemma p12_ul_msteps : forall ms ms', LE.msteps rsegs ms ms' -> UE.msteps rsegs ms ms'.
Proof.
  intros ms ms' H. induction H as [ms | ms ms1 ms2 H1 _ IH].
  - apply UE.msteps_refl.
  - eapply UE.msteps_cons; [| exact IH]. destruct H1 as (Hs & He). split; [exact Hs | exact He].
Qed.

Lemma p12_ul_evt : forall (RNG : footprint) Q ms, evtF rsegs RNG Q ms -> UE.evt rsegs Q ms.
Proof.
  intros RNG Q ms (ms' & Hs & HQ). exists ms'.
  split; [apply p12_ul_msteps; apply (mstepsF_msteps rsegs RNG); exact Hs | exact HQ].
Qed.

(* ---- the first instrumented check: 0x81e08-0x81e18 (and the compare block 0x82fb0-0x82fb8) ---- *)
Lemma p12_ck1_F :
  forall (RNG : footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (kb : byte),
    a0 = Z_to_bv 64 135648 -> s10 = Z_to_bv 64 2147450880 ->
    ov_read_bytes rsegs m (wa 2147467836) 1 = Some [kb] ->
    (bv_signed kb = 0 \/ 2 <= bv_signed kb <= 7) ->
    rng RNG 2147467836 1 ->
    evtF rsegs RNG
      (fun ms' => exists a1' a2' : word,
         ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 135648) a1' a2' a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 2147450880) s11 t3 t4 t5 t6)
                  Fr (Z_to_bv 64 0x81e1c) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81e08) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m kb -> -> HR Hk G.
  destruct (P12.p12_byte_cases kb Hk) as [->|[->|[->|[->|[->|[-> | -> ]]]]]];
    [ do 4 step; if_true
    | do 4 step; if_false; do 3 step; if_false; step .. ];
  apply evtF_done; do 2 eexists; reflexivity.
Qed.

(* ---- the second check: 0x81e2c-0x81e40 (and 0x82fc0-0x82fc8), then the second name byte at 0x81e44 ---- *)
Lemma p12_ck2_F :
  forall (RNG : footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (kb : byte),
    a0 = Z_to_bv 64 135648 -> s10 = Z_to_bv 64 2147450880 ->
    ov_read_bytes rsegs m (wa 2147467836) 1 = Some [kb] ->
    ov_read_bytes rsegs m (wa 135649) 1 = Some [Z_to_bv 8 0] ->
    (bv_signed kb = 0 \/ 2 <= bv_signed kb <= 7) ->
    rng RNG 2147467836 1 -> rng RNG 135649 1 ->
    evtF rsegs RNG
      (fun ms' => exists a1' a2' : word,
         ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1' a2' a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 2147450880) s11 t3 t4 t5 t6)
                  Fr (Z_to_bv 64 0x81e50) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81e2c) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m kb -> -> HRs HR1 Hk Gs G1.
  destruct (P12.p12_byte_cases kb Hk) as [->|[->|[->|[->|[->|[-> | -> ]]]]]];
    [ do 5 step; if_true
    | do 5 step; if_false; do 3 step; if_false; step .. ];
  do 2 step; if_true; apply evtF_done; do 2 eexists; reflexivity.
Qed.

(* ---- the whole check block 0x81e08 -> 0x81e50 ---- *)
Lemma p12_chk_F :
  forall (RNG : footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (kb : byte),
    a0 = Z_to_bv 64 135648 -> s10 = Z_to_bv 64 2147450880 ->
    ov_read_bytes rsegs m (wa 2147467836) 1 = Some [kb] ->
    ov_read_bytes rsegs m (wa 135648) 1 = Some [Z_to_bv 8 63] ->
    ov_read_bytes rsegs m (wa 135649) 1 = Some [Z_to_bv 8 0] ->
    (bv_signed kb = 0 \/ 2 <= bv_signed kb <= 7) ->
    rng RNG 2147467836 1 -> rng RNG 135648 1 -> rng RNG 135649 1 ->
    evtF rsegs RNG
      (fun ms' => exists a1' a2' : word,
         ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1' a2' a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 2147450880) s11 t3 t4 t5 t6)
                  Fr (Z_to_bv 64 0x81e50) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81e08) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m kb -> -> HRs HR0 HR1 Hk Gs G0 G1.
  eapply evtF_cut; [eapply p12_ck1_F; [reflexivity | reflexivity | exact HRs | exact Hk | exact Gs]|].
  intros ms' (a1' & a2' & ->).
  do 3 step. if_true.
  eapply evtF_cut;
    [eapply p12_ck2_F; [reflexivity | reflexivity | exact HRs | exact HR1 | exact Hk | exact Gs | exact G1]|].
  intros ms'' (a1'' & a2'' & ->).
  apply evtF_done. do 2 eexists. reflexivity.
Qed.

(* ---- the compare lemmas for the three check runs: the source statements, back through the UL bridge ---- *)
Lemma p12_ck1_of_F : ltac:(let T := type of P12.p12_ck1 in exact T).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m kb E0 E10 HR Hk.
  apply (p12_ul_evt RNG_all).
  apply p12_ck1_F with (kb := kb); try assumption.
  apply rng_all; lia.
Qed.

Lemma p12_ck2_of_F : ltac:(let T := type of P12.p12_ck2 in exact T).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m kb E0 E10 HRs HR1 Hk.
  apply (p12_ul_evt RNG_all).
  apply p12_ck2_F with (kb := kb); try assumption; apply rng_all; lia.
Qed.

Lemma p12_chk_of_F : ltac:(let T := type of P12.p12_chk in exact T).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m kb E0 E10 HRs HR0 HR1 Hk.
  apply (p12_ul_evt RNG_all).
  apply p12_chk_F with (kb := kb); try assumption; apply rng_all; lia.
Qed.

(* ---- the frame-loop prologue 0x81e50 -> 0x81ec4 (nl <> 0) or 0x82eac (nl = 0) ---- *)

(* P12.p12_q64_at and P12.p12_rw_rd over the lib.Lib cells this file's premises use. *)
Lemma p12f_q64_at : forall m A cs k w z a, rw_cells rsegs m A cs -> cell_at cs k = Some (C8 w) ->
  w = Z_to_bv 64 z -> a = A + Z.of_nat k -> q64 m a z.
Proof.
  intros m A cs k w z a ((Hwf & Hb) & _) Hk -> ->.
  destruct (cell_at_split cs k (C8 (Z_to_bv 64 z)) (C8 (Z_to_bv 64 z)) Hk) as (pre & post & -> & Hsz & _).
  rewrite cells_bytes_app in Hb. cbn [cells_bytes cbytes] in Hb.
  apply bytes_at_app in Hb. destruct Hb as (_ & Hb).
  apply cells_wf_app in Hwf. destruct Hwf as (Hwf1 & _).
  rewrite cells_bytes_length in Hb by exact Hwf1. rewrite Hsz in Hb.
  apply bytes_at_app in Hb. destruct Hb as (Hb & _). exact Hb.
Qed.

Lemma p12f_rw_rd : forall m A cs q, rw_cells rsegs m A cs -> A <= q < A + Z.of_nat (cells_size cs) ->
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

Ltac p12f_q H kk :=
  eapply p12f_q64_at with (k := kk); [exact H | reflexivity | try unfold fragb; f_equal; lia | cbn; lia].

Lemma p12_body_F :
  forall (RNG : footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word)
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
    rng RNG (Ab + 88) 16 -> rng RNG (Ab + 112) 24 -> rng RNG (Ab + 144) 8 -> rng RNG (Ab + 256) 8 ->
    rng RNG (Ab + 168) 8 -> rng RNG (Ab + 208) 16 -> rng RNG (Ab + 280) 8 -> rng RNG (Sh + 370) 16 ->
    evtF rsegs RNG
      (fun ms' => exists (R : bvmap 5 word) (pc' : Z) (m' : word -> option byte),
         ms' = MS R Fr (Z_to_bv 64 pc') fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 26 = Z_to_bv 64 2147450880 /\ getr R 23 = s7 /\ getr R 25 = s9 /\
         getr R 13 = Z_to_bv 64 0 /\ getr R 27 = Z_to_bv 64 (-8) /\ getr R 22 = Z_to_bv 64 1 /\
         (pc' = 0x81ec4 /\ nl <> 0 \/ pc' = 0x82eac /\ nl = 0) /\
         munch (P12.p12_W Ab Sh) m m' /\ wmono rsegs m m' /\
         q64 m' (Ab + 88) (fr + 2885) /\ q64 m' (Ab + 96) (fr + 180) /\
         q64 m' (Ab + 112) (fr + 186) /\ q64 m' (Ab + 120) (fragb fr + 15) /\ q64 m' (Ab + 128) (fragb fr + 19) /\
         q64 m' (Ab + 144) (fr + 452) /\ q64 m' (Ab + 256) (fragb fr + 8) /\
         (forall q, ~ outside (P12.p12_W Ab Sh) q -> exists b, LMm.mrd rsegs m' (LMm.wa q) = Some b))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 2147450880) s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81e50) fc None m (seg_rom rsegs)).
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6
    Fr fc m nl Ab Sh fr j88 j112 j144 j256 jsh -> Hnl -> -> HSh HShA HA Hfr0 HfrA C88 C112 C144 C256
    R168 R208 R216 R280 CSH G88 G112 G144 G256 G168 G208 G280 GSH.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  pose proof (munch_refl (P12.p12_W Ab Sh) m) as MU. unfold P12.p12_W in MU.
  pose proof (wmono_refl rsegs m) as WM.
  do 2 step.
  do 3 step.
  do 2 step.
  do 2 step.
  do 3 step.
  do 3 step.
  do 2 step.
  do 3 step.
  step.
  replace (Z_to_bv 64 (-8)) with (Z_to_bv 64 18446744073709551608)
    by (apply bv_eq; vm_compute; reflexivity).
  do 8 step.
  assert (HRD : forall q, ~ outside (P12.p12_W Ab Sh) q ->
            exists b, LMm.mrd rsegs m0 (LMm.wa q) = Some b).
  { intros q Hq. unfold P12.p12_W in Hq. cbn [outside] in Hq.
    destruct (Z_lt_le_dec q (Ab + 88)) as [L1|L1].
    - destruct (Z_lt_le_dec q (Sh + 370)) as [L2|L2]; [exfalso; apply Hq; lia|].
      destruct (Z_lt_le_dec q (Sh + 386)) as [L3|L3]; [|exfalso; apply Hq; lia].
      apply (p12f_rw_rd m0 (Sh + 370) _ q CSH). cbn [cells_size csize Nat.add]. lia.
    - destruct (Z_lt_le_dec q (Ab + 104)) as [L2|L2].
      + apply (p12f_rw_rd m0 (Ab + 88) _ q C88). cbn [cells_size csize Nat.add]. lia.
      + destruct (Z_lt_le_dec q (Ab + 112)) as [L3|L3]; [exfalso; apply Hq; lia|].
        destruct (Z_lt_le_dec q (Ab + 136)) as [L4|L4].
        * apply (p12f_rw_rd m0 (Ab + 112) _ q C112). cbn [cells_size csize Nat.add]. lia.
        * destruct (Z_lt_le_dec q (Ab + 144)) as [L5|L5]; [exfalso; apply Hq; lia|].
          destruct (Z_lt_le_dec q (Ab + 152)) as [L6|L6].
          -- apply (p12f_rw_rd m0 (Ab + 144) _ q C144). cbn [cells_size csize Nat.add]. lia.
          -- destruct (Z_lt_le_dec q (Ab + 256)) as [L7|L7]; [exfalso; apply Hq; lia|].
             destruct (Z_lt_le_dec q (Ab + 264)) as [L8|L8]; [|exfalso; apply Hq; lia].
             apply (p12f_rw_rd m0 (Ab + 256) _ q C256). cbn [cells_size csize Nat.add]. lia. }
  destruct (Z.eq_dec nl 0) as [->|Hne].
  - step. if_false. step.
    apply evtF_done. eexists _, 0x82eac, _. split; [reflexivity|].
    do 10 (split; [reflexivity|]).
    split; [apply bv_eq; vm_compute; reflexivity|].
    split; [reflexivity|].
    split; [right; split; reflexivity|].
    split; [exact MU|]. split; [exact WM|].
    split; [p12f_q C88 0%nat|]. split; [p12f_q C88 8%nat|].
    split; [p12f_q C112 0%nat|]. split; [p12f_q C112 8%nat|]. split; [p12f_q C112 16%nat|].
    split; [p12f_q C144 0%nat|]. split; [p12f_q C256 0%nat|].
    exact HRD.
  - apply evtF_done. eexists _, 0x81ec4, _. split; [reflexivity|].
    do 10 (split; [reflexivity|]).
    split; [apply bv_eq; vm_compute; reflexivity|].
    split; [reflexivity|].
    split; [left; split; [reflexivity | exact Hne]|].
    split; [exact MU|]. split; [exact WM|].
    split; [p12f_q C88 0%nat|]. split; [p12f_q C88 8%nat|].
    split; [p12f_q C112 0%nat|]. split; [p12f_q C112 8%nat|]. split; [p12f_q C112 16%nat|].
    split; [p12f_q C144 0%nat|]. split; [p12f_q C256 0%nat|].
    exact HRD.
Qed.

(* ---- the compare lemma for the prologue: the source statement, over the UL copies ----
   lib/Lib/Cells.v and lib/B/Tk/UL/Cells.v declare the same `cell` inductive with the same `csize` /
   `cbytes` / `cell_wf` / `cells_wf` / `cells_bytes` bodies, and lib/Lib/Mem.v and lib/B/Tk/UL/Mem.v the
   same `mrd` / `bytes_at` / `wr_at` / `le8`, so only the identity of the inductive separates a UL cells
   fact from the lib.Lib one; the shared file lib/B/Tk/UL/CellBridge.v (module CBR below) carries it
   across, together with `outside` / `munch`, which are a second copy of the same fixpoint in
   lib/B/Tk/UL/Frame.v. `wmono` is stated through the semantics' own `wview`, so the two copies are the
   same statement and need no lemma. *)

Lemma p12_body_of_F : ltac:(let T := type of P12.p12_body in exact T).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6
    Fr fc m nl Ab Sh fr j88 j112 j144 j256 jsh
    E9 Hnl E1 E3 HSh HShA HA Hfr0 HfrA C88 C112 C144 C256 R168 R208 R216 R280 CSH.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  apply (p12_ul_evt RNG_all).
  eapply evtF_mono.
  - apply (p12_body_F RNG_all ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 Fr fc m nl Ab Sh fr j88 j112 j144 j256 jsh
             E9 Hnl E1 E3 HSh HShA HA Hfr0 HfrA
             (CBR.rw_cells_ul_lib rsegs m (Ab + 88) _ C88)
             (CBR.rw_cells_ul_lib rsegs m (Ab + 112) _ C112)
             (CBR.rw_cells_ul_lib rsegs m (Ab + 144) _ C144)
             (CBR.rw_cells_ul_lib rsegs m (Ab + 256) _ C256)
             (CBR.ro_cells_ul_lib rsegs m (Ab + 168) _ R168)
             (CBR.ro_cells_ul_lib rsegs m (Ab + 208) _ R208)
             (CBR.ro_cells_ul_lib rsegs m (Ab + 216) _ R216)
             (CBR.ro_cells_ul_lib rsegs m (Ab + 280) _ R280)
             (CBR.rw_cells_ul_lib rsegs m (Sh + 370) _ CSH));
      apply rng_all; lia.
  - intros ms' (R & pc' & m' & Hms & G2 & G3 & G4 & G8 & G9 & G19 & G26 & G23 & G25 & G13 & G27 & G22
                  & Hpc & MU & WM & QA & QB & QC & QD & QE & QF & QG & HRD).
    exists R, pc', m'.
    split; [exact Hms|].
    split; [exact G2|]. split; [exact G3|]. split; [exact G4|]. split; [exact G8|].
    split; [exact G9|]. split; [exact G19|]. split; [exact G26|]. split; [exact G23|].
    split; [exact G25|]. split; [exact G13|]. split; [exact G27|]. split; [exact G22|].
    split; [exact Hpc|].
    split; [apply CBR.munch_lib_ul; exact MU|].
    split; [exact WM|].
    split; [exact QA|]. split; [exact QB|]. split; [exact QC|]. split; [exact QD|].
    split; [exact QE|]. split; [exact QF|]. split; [exact QG|].
    intros q Hq. apply HRD. intros Hc. apply Hq. apply CBR.outside_lib_ul. exact Hc.
Qed.

(* The four run lemmas have exactly the statements of the source lemmas. *)
Definition p12_ck1_same : ltac:(let T := type of P12.p12_ck1 in exact T) := p12_ck1_of_F.
Definition p12_ck2_same : ltac:(let T := type of P12.p12_ck2 in exact T) := p12_ck2_of_F.
Definition p12_chk_same : ltac:(let T := type of P12.p12_chk in exact T) := p12_chk_of_F.
Definition p12_body_same : ltac:(let T := type of P12.p12_body in exact T) := p12_body_of_F.
