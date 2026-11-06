(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names, addresses and numbers changed; 1684 of its 1797 lines of code are new or changed and 898 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/R6.v, with its module paths, module names and numbers changed; 1340 of its 1484 lines of code are new or changed and 1653 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F1.v; 78 of its 128 lines of code are new or changed and 1434 lines of the source are left out. *)
(* lib/A/Prog/Seg/F1Fs.v -- the NARROWED footprint run of segment F1 of fuzz_ctrl image A's LLVMFuzzerTestOneInput
   (libreac v1.9.0), written by the stage's glue owner (a Theorem Labs lane) under a Theorem Labs lane's split /
   narrowed-stretch convention (a Theorem Labs lane 04:01Z / 04:23Z: the stage owner writes <S>Fs.v, Requiring only a Theorem Labs lane's
   <S>F.v and the sources, never editing them).  rule 24: no function proved (a re-cut of an already-proved run).

   PROVENANCE. Image A = fuzz_ctrl.asan, libreac v1.9.0, pinned
   (internal path) (sha256 aac16e1f...135704d), FACTS
   ed6b6b7b0ab, PAU pau-libreac-v190.  Sources: Seg/F1.v 0f7557862644 (the blob this tree had at release c5e779efe8c) and a Theorem Labs lane's Seg/F1F.v (an earlier version, blob c4287e871a45, not in this delivery),
   both unchanged since that release apart from comment text; F1F.v's code differs from that earlier version only by fully qualified names.

   WHY. F1F.f1_evt_F (F1F.v (at head lib/A/Prog/Seg/F1F.v:165)) states its two footprint regions of the HIGH length byte, [q + 1, q + 2) and its
   shadow byte (q + 1) >> 3 + ASAN_K, UNCONDITIONALLY, although the run reads them only when left >= 2 (its own
   premise H2 is guarded by `2 <= left ->`, and the segment-F table says "read only when left >= 2").  At the cut
   A81d40_at the walk has q = p + c, left = n - c for the input block (p, n); at left = 1 the byte q + 1 = p + n is
   the first byte after the block, which no visibility fact of the core's world covers (ProgWorldVisHeap.heap_vis
   covers [p, p + req_size n) only), so the glue could not supply those two regions to the lift's footprint
   RNG_W (w_H W) (its fp_avoids needs every footprint range visible).  f1_evt_Fs is f1_evt_F with exactly those two
   premises guarded by `2 <= left ->`, nothing else changed.

   HOW. left >= 2: f1_evt_F itself.  left = 1: the left = 1 path of f1_evt_F's own proof (F1F.v (at head lib/A/Prog/Seg/F1F.v:199-228)),
   verbatim with left substituted: f1_chk0_F, four steps, the not-taken branch, three steps, f1_tail_F.

   THE PIN. f1_evt_F_of_Fs re-derives a Theorem Labs lane's f1_evt_F from f1_evt_Fs (the guarded premises from the
   unguarded ones), and f1_evt_F_of_Fs_verbatim checks by constr_eq that its type is F1F.f1_evt_F's: f1_evt_Fs is
   the same stretch with a weaker premise list.

   Footprint table: F1Fs.rng.tsv. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcIdentModel RcFrag.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcReply.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import reac_ctrl_parse_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_b5.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Tac_cls.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import F1.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import F1F.
(* Last but YK11, as F1F.v: StepF's step / if_false / finish (evtF goals) shadow the evt engine's. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
Open Scope Z_scope.

(* ---- the whole run 0x81d40 -> the allocator entry 0x5337c, the high-byte regions guarded by 2 <= left. ---- *)
Lemma f1_evt_Fs :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A q left : Z) (b0 b1 k0 k1 : byte),
    s1 = Z_to_bv 64 A -> s6 = Z_to_bv 64 q -> s9 = Z_to_bv 64 left -> s10 = Z_to_bv 64 ASAN_K ->
    0 <= q -> q + left < 2 ^ 63 -> 1 <= left < 2 ^ 26 -> 0 <= A -> A + 232 <= 2 ^ 64 ->
    ov_read_bytes rsegs m (wa (Z.shiftr q 3 + ASAN_K)) 1 = Some [k0] ->
    (bv_signed k0 = 0 \/ q mod 8 < bv_signed k0) ->
    ov_read_bytes rsegs m (wa q) 1 = Some [b0] ->
    (2 <= left ->
       ov_read_bytes rsegs m (wa (Z.shiftr (q + 1) 3 + ASAN_K)) 1 = Some [k1] /\
       (bv_signed k1 = 0 \/ (q + 1) mod 8 < bv_signed k1) /\
       ov_read_bytes rsegs m (wa (q + 1)) 1 = Some [b1]) ->
    store_ok rsegs m (wa (A + 224)) 8 = true ->
    ExecF.rng RNG (Z.shiftr q 3 + ASAN_K) 1 ->
    ExecF.rng RNG q 1 ->
    (2 <= left -> ExecF.rng RNG (Z.shiftr (q + 1) 3 + ASAN_K) 1) ->
    (2 <= left -> ExecF.rng RNG (q + 1) 1) ->
    ExecF.rng RNG (A + 224) 8 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists a1' a2' : word,
         ms' = MS (mkR (Z_to_bv 64 0x81da4) sp gp tp t0 t1 t2 s0 s1
                       (Z_to_bv 64 (Z.min (bv_unsigned b0 + (if 2 <=? left then 256 * bv_unsigned b1 else 0))
                                          (left - Z.min 2 left)))
                       a1' a2' a3 a4 a5 a6 a7
                       (Z_to_bv 64 (Z.min (bv_unsigned b0 + (if 2 <=? left then 256 * bv_unsigned b1 else 0))
                                          (left - Z.min 2 left)))
                       s3 (Z_to_bv 64 (q + Z.min 2 left)) s5 s6 s7 s8 (Z_to_bv 64 (left - Z.min 2 left)) s10 s11
                       t3 t4 t5 t6)
                  F (Z_to_bv 64 0x5337c) fc None
                  (write_to_mem m (wa (A + 224)) (le8 (Z_to_bv 64 (left - Z.min 2 left)))) (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81d40) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A q left b0 b1 k0 k1 E1 E6 E9 E10 Hq0 Hq1 Hl HA0 HA1 HK0 Hk0 HB0 H2 HS RSH0 RQ0 RSH1 RQ1 RSP.
  destruct (Z_lt_le_dec left 2) as [Hl1|Hl2].
  2: { exact (f1_evt_F RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                t3 t4 t5 t6 F fc m A q left b0 b1 k0 k1 E1 E6 E9 E10 Hq0 Hq1 Hl HA0 HA1 HK0 Hk0 HB0 H2 HS
                RSH0 RQ0 (RSH1 Hl2) (RQ1 Hl2) RSP). }
  (* left = 1: F1F.v:198-227, the left = 1 path of f1_evt_F's own proof *)
  assert (EL : left = 1) by lia. subst s1 s6 s9 s10 left. clear RSH1 RQ1 H2 Hl1.
  pose proof (bv_unsigned_in_range 8 b0) as Hb0. pose proof (bv_unsigned_in_range 8 b1) as Hb1.
  change (bv_modulus 8) with 256 in Hb0, Hb1.
  assert (RQ0' : ExecF.rng RNG (bv_unsigned (Z_to_bv 64 q)) 1)
    by (rewrite MState.unsigned_lit by lia; exact RQ0).
  apply (f1_chk0_F RNG ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 q) s7 s8
           (Z_to_bv 64 1) (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6 F fc m _ q k0 eq_refl eq_refl ltac:(lia) HK0 Hk0);
    [| exact RSH0].
  intros a0' a1'.
  step. step. step. step.
  if_false_by (eq_refl : negb (bv_eqb (Z_to_bv 64 1) (Z_to_bv 64 1)) = false).
  step. step. step.
  eapply ExecF.evtF_mono.
  { eapply f1_tail_F with (A := A) (lo := bv_unsigned b0) (hi := 0) (rest := 0);
      [reflexivity | reflexivity | reflexivity | reflexivity | lia | lia | lia | lia | | lia | exact HS
       | exact RSP].
    rewrite Z.lor_0_l. lia. }
  intros ms' ->. do 2 eexists.
  replace (Z.min (bv_unsigned b0 + (if 2 <=? 1 then 256 * bv_unsigned b1 else 0)) (1 - Z.min 2 1))
    with (Z.min (Z.lor 0 (bv_unsigned b0)) 0) by (rewrite Z.lor_0_l; cbn; lia).
  replace (1 - Z.min 2 1) with 0 by lia.
  replace (q + Z.min 2 1) with (q + 1) by lia.
  reflexivity.
Qed.

(* ---- The pin: a Theorem Labs lane's f1_evt_F from f1_evt_Fs, and its type is F1F.f1_evt_F's term for term. ---- *)
Lemma f1_evt_F_of_Fs :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A q left : Z) (b0 b1 k0 k1 : byte),
    s1 = Z_to_bv 64 A -> s6 = Z_to_bv 64 q -> s9 = Z_to_bv 64 left -> s10 = Z_to_bv 64 ASAN_K ->
    0 <= q -> q + left < 2 ^ 63 -> 1 <= left < 2 ^ 26 -> 0 <= A -> A + 232 <= 2 ^ 64 ->
    ov_read_bytes rsegs m (wa (Z.shiftr q 3 + ASAN_K)) 1 = Some [k0] ->
    (bv_signed k0 = 0 \/ q mod 8 < bv_signed k0) ->
    ov_read_bytes rsegs m (wa q) 1 = Some [b0] ->
    (2 <= left ->
       ov_read_bytes rsegs m (wa (Z.shiftr (q + 1) 3 + ASAN_K)) 1 = Some [k1] /\
       (bv_signed k1 = 0 \/ (q + 1) mod 8 < bv_signed k1) /\
       ov_read_bytes rsegs m (wa (q + 1)) 1 = Some [b1]) ->
    store_ok rsegs m (wa (A + 224)) 8 = true ->
    ExecF.rng RNG (Z.shiftr q 3 + ASAN_K) 1 ->
    ExecF.rng RNG q 1 ->
    ExecF.rng RNG (Z.shiftr (q + 1) 3 + ASAN_K) 1 ->
    ExecF.rng RNG (q + 1) 1 ->
    ExecF.rng RNG (A + 224) 8 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists a1' a2' : word,
         ms' = MS (mkR (Z_to_bv 64 0x81da4) sp gp tp t0 t1 t2 s0 s1
                       (Z_to_bv 64 (Z.min (bv_unsigned b0 + (if 2 <=? left then 256 * bv_unsigned b1 else 0))
                                          (left - Z.min 2 left)))
                       a1' a2' a3 a4 a5 a6 a7
                       (Z_to_bv 64 (Z.min (bv_unsigned b0 + (if 2 <=? left then 256 * bv_unsigned b1 else 0))
                                          (left - Z.min 2 left)))
                       s3 (Z_to_bv 64 (q + Z.min 2 left)) s5 s6 s7 s8 (Z_to_bv 64 (left - Z.min 2 left)) s10 s11
                       t3 t4 t5 t6)
                  F (Z_to_bv 64 0x5337c) fc None
                  (write_to_mem m (wa (A + 224)) (le8 (Z_to_bv 64 (left - Z.min 2 left)))) (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81d40) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A q left b0 b1 k0 k1 E1 E6 E9 E10 Hq0 Hq1 Hl HA0 HA1 HK0 Hk0 HB0 H2 HS RSH0 RQ0 RSH1 RQ1 RSP.
  exact (f1_evt_Fs RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
           t3 t4 t5 t6 F fc m A q left b0 b1 k0 k1 E1 E6 E9 E10 Hq0 Hq1 Hl HA0 HA1 HK0 Hk0 HB0 H2 HS
           RSH0 RQ0 (fun _ => RSH1) (fun _ => RQ1) RSP).
Qed.

Example f1_evt_F_of_Fs_verbatim : True.
Proof. let A := type of F1F.f1_evt_F in let B := type of f1_evt_F_of_Fs in constr_eq A B; exact I. Qed.
