(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names and addresses changed; 2105 of its 2257 lines of code are new or changed and 859 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A5.v, with its addresses changed; 20 of its 66 lines of code are new or changed and 2211 lines of the source are left out. *)
(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
   source run: lib/B/Prog/Seg/R1.v seg_R1 :38 states no run lemma and steps no instruction itself: it applies
     A5.b_turn_gen at pc0 = 0x81550 (the R1 cut Inv_B81550), whose Exec.evt run from that pc is
     A5.b_any_ld_evt's 0x81550 arm, i.e. A5.b_ld_evt (A5.v:156-222: T01 0x81550, the cursor's instrumented check
     0x81560, the byte copy 0x81568 .. 0x8157c and the latch, ending at the head 0x81548 or, after turn 5, at the
     loop exit 0x815a0).  seg_R1_F is that stretch cut out of seg_R1; the exit after turn 5 is A5's b_tail_evt /
     b_mode_evt / b_cat_evt, whose twins are A5F.b_tail_evt_F / b_mode_evt_F / b_cat_evt_pre_F / b_cat_evt_post_F.
     R1.v and A5.v are not in a working branch 3803efccea0: they are a Theorem Labs lane's WIP d574f6c66de
     (R1.v blob 0a6ebab204bf5ba8aa6492283fb98f0c06b01066 (the blob this tree had at release c5e779efe8c), A5.v blob 0e65829571e0303b907755eee8035d04c36236c7), taken
     by path onto 3803efccea0 on a working branch f9a9f80d79e (unchanged, same blobs) and built there
     (scratch -s ours type-check rc=0);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
     lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
   compare: seg_R1_of_F (evtF_evt + rng_all) re-derives the source statement of the run seg_R1 uses
     (A5.b_ld_evt, checked by conversion, seg_R1_src_check).
   The stretch has no call.  This file states no callee contract. *)
(* rule 24: no function proved. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require R1 A5 A5F.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* ---- seg_R1_F: the R1 stretch from the body cut 0x81550 (left <> 0, a3 = q + 1 the bumped cursor) to the head
   0x81548 (cnt > 1) or the loop exit 0x815a0 (cnt = 1).  Accesses: the cursor's shadow byte [q / 8 + K], the
   input byte [q] and the store our[t] at [d]. ---- *)
Lemma seg_R1_F :
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cnt d q v K : Z) (b kq : byte),
    a0 = Z_to_bv 64 cnt -> a1 = Z_to_bv 64 1 -> a2 = Z_to_bv 64 d -> a3 = Z_to_bv 64 (q + 1) ->
    s2 = Z_to_bv 64 v -> s6 = Z_to_bv 64 q -> s10 = Z_to_bv 64 K ->
    1 <= cnt <= 6 -> 0 <= d -> d + 1 < 2 ^ 64 -> 1 <= q -> q + 2 < 2 ^ 64 -> 1 <= v -> v + 1 < 2 ^ 64 ->
    0 <= K -> q / 8 + K + 1 < 2 ^ 64 ->
    ov_read_bytes rsegs m (wa (q / 8 + K)) 1 = Some [kq] ->
    (bv_signed kq = 0 \/ q mod 8 < bv_signed kq) ->
    ov_read_bytes rsegs m (wa q) 1 = Some [b] ->
    store_ok rsegs m (wa d) 1 = true ->
    rng RNG (q / 8 + K) 1 -> rng RNG q 1 -> rng RNG d 1 ->
    evtF rsegs RNG
      (fun ms' => exists (x4 x5 : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (cnt - 1)) (Z_to_bv 64 1) (Z_to_bv 64 (d + 1))
                       (Z_to_bv 64 (q + 1)) x4 x5 a6 a7 (Z_to_bv 64 (v - 1)) s3 s4 s5
                       (Z_to_bv 64 (q + 1)) s7 s8 s9 (Z_to_bv 64 K) s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 (if cnt =? 1 then 0x815a0 else 0x81548)) fc None m' (seg_rom rsegs) /\
         munch [(d, d + 1)] m m' /\ wmono rsegs m m' /\ bytes_at rsegs m' d [b])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81550) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m cnt d q v K b kq E0 E1 E2 E3 E4 E5 E6 Hcnt Hd0 Hd Hq0 Hq Hv0 Hv HK Hsh HRq HOKq HRb HS Rsh Rq Rd.
  (* seg_R1 -> A5.b_turn_gen at pc0 = 0x81550 -> b_any_ld_evt's 0x81550 arm *)
  exact (A5F.b_any_ld_evt_F RNG 0x81550 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
           s10 s11 t3 t4 t5 t6 F fc m cnt d q v K b kq (or_intror (conj eq_refl E3)) E0 E1 E2 E4 E5 E6
           Hcnt Hd0 Hd Hq0 Hq Hv0 Hv HK Hsh HRq HOKq HRb HS Rsh Rq Rd).
Qed.

Lemma seg_R1_of_F :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cnt d q v K : Z) (b kq : byte),
    a0 = Z_to_bv 64 cnt -> a1 = Z_to_bv 64 1 -> a2 = Z_to_bv 64 d -> a3 = Z_to_bv 64 (q + 1) ->
    s2 = Z_to_bv 64 v -> s6 = Z_to_bv 64 q -> s10 = Z_to_bv 64 K ->
    1 <= cnt <= 6 -> 0 <= d -> d + 1 < 2 ^ 64 -> 1 <= q -> q + 2 < 2 ^ 64 -> 1 <= v -> v + 1 < 2 ^ 64 ->
    0 <= K -> q / 8 + K + 1 < 2 ^ 64 ->
    ov_read_bytes rsegs m (wa (q / 8 + K)) 1 = Some [kq] ->
    (bv_signed kq = 0 \/ q mod 8 < bv_signed kq) ->
    ov_read_bytes rsegs m (wa q) 1 = Some [b] ->
    store_ok rsegs m (wa d) 1 = true ->
    evt rsegs
      (fun ms' => exists (x4 x5 : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (cnt - 1)) (Z_to_bv 64 1) (Z_to_bv 64 (d + 1))
                       (Z_to_bv 64 (q + 1)) x4 x5 a6 a7 (Z_to_bv 64 (v - 1)) s3 s4 s5
                       (Z_to_bv 64 (q + 1)) s7 s8 s9 (Z_to_bv 64 K) s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 (if cnt =? 1 then 0x815a0 else 0x81548)) fc None m' (seg_rom rsegs) /\
         munch [(d, d + 1)] m m' /\ wmono rsegs m m' /\ bytes_at rsegs m' d [b])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81550) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m cnt d q v K b kq E0 E1 E2 E3 E4 E5 E6 Hcnt Hd0 Hd Hq0 Hq Hv0 Hv HK Hsh HRq HOKq HRb HS.
  apply (evtF_evt rsegs RNG_all).
  apply (seg_R1_F RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
           t3 t4 t5 t6 F fc m cnt d q v K b kq E0 E1 E2 E3 E4 E5 E6 Hcnt Hd0 Hd Hq0 Hq Hv0 Hv HK Hsh HRq HOKq HRb HS);
    apply rng_all; pose proof (Z.div_pos q 8 ltac:(lia) ltac:(lia)); lia.
Qed.
Definition seg_R1_src_check : ltac:(let t := type of seg_R1_of_F in exact t) := A5.b_ld_evt.
