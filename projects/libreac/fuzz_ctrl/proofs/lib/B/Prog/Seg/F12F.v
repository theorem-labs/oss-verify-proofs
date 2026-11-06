(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module names and numbers changed; 1592 of its 1709 lines of code are new or changed and 894 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/F12.v; 137 of its 323 lines of code are new or changed and 1523 lines of the source are left out. *)
(* rule 24: no function proved. *)
(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17; measured against this image only;
   source runs: lib/B/Prog/Seg/F12.v f12_evt (:633; the run of BOTH segment rows S_F12 and S_F12_298, which enter
     at pc = 0x82304 and at pc = 0x82308) at a working branch 3803efccea0
     (blob 00a442384dd51240c922c0e15640c08fabaff84f);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
         lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
   split (parent 23:50Z: split at EVERY call, never state a callee contract locally): f12_evt calls __asan_memcpy
     (0x52164) at 0x8233c.  f12_pre_F re-runs F12.v lines 686-848 (pc -> the callee entry 0x52164, ra = 0x82340):
     the branch bltz a0 at 0x82304 not taken, the nine shadow stores 0x82308-0x82328, the count, the two spill
     loads and the argument move.  Its Q carries the memory facts the proved run held at the call (F12.v:762-846:
     MU9, WM9, MI9, ST9, BS9, RW9, AD9, AS9, AC9, SW9, SH9), which are exactly the premises asan_memcpy_contract
     takes there; the contract itself is NOT stated here.  The callee's return pc 0x82340 IS the exit cut
     (Inv_B82340_at), so the post stretch is empty and there is no f12_post_F.
   compare: no <run>_of_F (the source statement f12_evt runs through the callee; the split stretch is cited
     above). *)
(* Route (C) (a Theorem Labs lane 09:38Z, amendment 10:34Z; a Theorem Labs lane, 2026-10-29): f12_pre_F_on carries the proof; f12_pre_F
   keeps its statement as a corollary.  Measured from the run: the only shadow bytes it touches are the nine it
   stores into, [K3 + 42, K3 + 51) (the `rng RNG (K3 + 42) 9` row; the stores 0x82308-0x82328), and their store_ok
   comes from `wr_at rsegs m (K3 + 42) 9`, not from `shadow_rw m`; the stretch reads no shadow byte.  `shadow_rw m`
   only fed the runtime clause its every-shadow-byte-present hypothesis.  So in f12_pre_F_on:
   - the premise `shadow_rw m` is dropped (the run reads and stores no shadow byte through it);
   - the runtime clause `forall mm, munch .. -> wmono .. -> (forall a, in_shadow a -> present) ->
     asan_cells mm /\ shadow_rw mm` asks presence only of the bytes the run stores into (f12_pre_F_shadow_R K3,
     which the run supplies from the stored zeros) and gives `asan_cells mm` only (the run does not use the clause's
     `shadow_rw mm`);
   - the post `shadow_rw m1` is `forall P, shadow_rw_on P m -> shadow_rw_on P m1` (the stores keep every present
     byte, B.Prog.MemMono.rd_mono, and every writable byte, wmono). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Fpu Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcRec RcParse RcFrag RcFragLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv asan_memcpy_c
  reac_ctrl_identity_fragment_c RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot Tac_fs F12.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Tac_ro.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require MemMono.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require ShadowRwOn ShadowRwOnT.
Import ListNotations.
(* Tac_ro's chain loads other modules named YK11 (lib.Reusable.YK11), so the short name would resolve to that copy;
   this file's registers and getr must be image B's, as F12.v does. *)
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.
Open Scope Z_scope.
(* F12.v's own Local Ltac lia; the StepF tactics keep the Lia one, which they bound at their definition. *)
Local Ltac lia := pose proof FRAME_BYTES_val; pose proof FRAME_SHADOW_val; Lia.lia.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.FrameAPI.

(* The shadow bytes the run stores into: the nine shadow bytes of [D, D+72), [K3+42, K3+51). *)
Definition f12_pre_F_shadow_R (K3 : Z) : Z -> Prop := fun a => K3 + 42 <= a < K3 + 51.

(* The footprint twin of the pre-call stretch of f12_evt, in its binders and premises.
   Regions: [K3+42, K3+51) written (the nine shadow bytes of [D, D+72)), [A+200, +8) and [A+208, +8) read (the two
   spills).  The stretch has no instrumented check (segment table: no shadow row). *)
Lemma f12_pre_F_on :
  forall (RNG : footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7v s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A r K3 D S0 lo pc : Z) (src junk : list byte),
    s1v = Z_to_bv 64 A -> s3v = Z_to_bv 64 K3 ->
    (pc = 0x82308 \/ (pc = 0x82304 /\ a0v = Z_to_bv 64 r /\ 0 <= r < 2 ^ 63)) ->
    0 <= K3 -> K3 + 51 <= 2 ^ 64 ->
    0 <= D -> 0 <= S0 < 2 ^ 64 -> D + 72 <= S0 ->
    D mod 8 = 0 -> D / 8 + ASAN_K = K3 + 42 ->
    S0 mod 8 = 0 -> S0 / 8 + ASAN_K = K3 + 346 ->
    (forall t, 0 <= t <= 72 -> app_mem (D + t)) ->
    app_mem (S0 + 7) -> app_mem (S0 + 72) ->
    K3 + 51 <= A -> K3 + 51 <= lo ->
    (K3 + 51 <= D \/ D + 72 <= K3 + 42) ->
    (K3 + 51 <= S0 \/ S0 + 72 <= K3 + 42) ->
    wr_at rsegs m (K3 + 42) 9 ->
    (forall mm, munch [(K3 + 42, K3 + 51)] m mm -> wmono rsegs m mm ->
       (forall a, f12_pre_F_shadow_R K3 a -> in_shadow a -> exists b, mrd rsegs mm (wa a) = Some b) ->
       asan_cells mm) ->
    bytes_at rsegs m (A + 200) (le8 (Z_to_bv 64 D)) ->
    bytes_at rsegs m (A + 208) (le8 (Z_to_bv 64 S0)) ->
    bytes_at rsegs m S0 src -> length src = 72%nat ->
    rw_cells rsegs m D [CB 72 junk] ->
    addressable m S0 72 ->
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) -> lo + ASAN_MEMCPY_K <= bv_unsigned sp ->
    HIGHMEM_BEG <= lo -> bv_unsigned sp <= APPMEM_END ->
    RT_HI <= D ->
    (D + 72 <= bv_unsigned sp - ASAN_MEMCPY_K \/ bv_unsigned sp <= D) ->
    (S0 + 72 <= bv_unsigned sp - ASAN_MEMCPY_K \/ bv_unsigned sp <= S0) ->
    rng RNG (K3 + 42) 9 -> rng RNG (A + 200) 8 -> rng RNG (A + 208) 8 ->
    evtF rsegs RNG
      (fun ms' => exists m1 : word -> option byte,
         ms' = MS (mkR (Z_to_bv 64 0x82340) sp gp tp t0 t1 t2 s0 s1v (Z_to_bv 64 D) (Z_to_bv 64 S0)
                       (Z_to_bv 64 72) a3 a4 a5 a6 a7 s2 s3v s4 (Z_to_bv 64 S0) s6 s7v s8 s9 s10 s11
                       t3 t4 t5 t6)
                  Fr (Z_to_bv 64 0x52164) fc None m1 (seg_rom rsegs)
         /\ munch [(K3 + 42, K3 + 51)] m m1
         /\ wmono rsegs m m1 /\ mem_inv rsegs m1
         /\ stk rsegs m1 lo (bv_unsigned sp)
         /\ asan_cells m1 /\ (forall P, B.ShadowRwOn.shadow_rw_on P m -> B.ShadowRwOn.shadow_rw_on P m1)
         /\ bytes_at rsegs m1 S0 src /\ rw_cells rsegs m1 D [CB 72 junk]
         /\ addressable m1 D 72 /\ addressable m1 S0 72
         /\ (forall k, 0 <= k < 9 -> b8 m1 (K3 + 42 + k) 0))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7v s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7v s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A r K3 D S0 lo pc src junk -> -> Hpc HK0 HK1 HD0 HS0b HDS HD8 HDK HS8 HSK HappD HapS7 HapS72
    HKA HKlo HdjD HdjS HWR HRT H200 H240 HbS Lsrc HRWD HADS HMI HST Hlo1 Hlo2 Hspa HRTD HdjDW HdjSW
    Rsh9 R200 R208.
  assert (HDE : D + 72 <= APPMEM_END).
  { pose proof (HappD 72 ltac:(lia)) as Ha.
    unfold app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG in Ha. unfold APPMEM_END. lia. }
  (* the FAIL branch at 0x82304 is not taken, so both entries reach the first shadow store at 0x82308 *)
  cut (evtF rsegs RNG
         (fun ms' => exists m1 : word -> option byte,
            ms' = MS (mkR (Z_to_bv 64 0x82340) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 D)
                          (Z_to_bv 64 S0) (Z_to_bv 64 72) a3 a4 a5 a6 a7 s2 (Z_to_bv 64 K3) s4
                          (Z_to_bv 64 S0) s6 s7v s8 s9 s10 s11 t3 t4 t5 t6)
                     Fr (Z_to_bv 64 0x52164) fc None m1 (seg_rom rsegs)
            /\ munch [(K3 + 42, K3 + 51)] m m1
            /\ wmono rsegs m m1 /\ mem_inv rsegs m1
            /\ stk rsegs m1 lo (bv_unsigned sp)
            /\ asan_cells m1 /\ (forall P, B.ShadowRwOn.shadow_rw_on P m -> B.ShadowRwOn.shadow_rw_on P m1)
            /\ bytes_at rsegs m1 S0 src /\ rw_cells rsegs m1 D [CB 72 junk]
            /\ addressable m1 D 72 /\ addressable m1 S0 72
            /\ (forall k, 0 <= k < 9 -> b8 m1 (K3 + 42 + k) 0))
         (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0v a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 K3) s4 s5 s6
                  s7v s8 s9 s10 s11 t3 t4 t5 t6)
             Fr (Z_to_bv 64 0x82308) fc None m (seg_rom rsegs))).
  { intros E298. destruct Hpc as [->|(-> & -> & Hr)]; [exact E298|].
    assert (Hbltz : bv_lts (Z_to_bv 64 r) (Z_to_bv 64 0) = false).
    { unfold bv_lts. rewrite (signed_lit r) by lia. rewrite (signed_lit 0) by lia. apply Z.ltb_ge. lia. }
    step.
    replace (bv_lts (Z_to_bv 64 r) (Z_to_bv 64 0)) with false by (symmetry; exact Hbltz). cbv iota.
    exact E298. }
  (* the nine shadow stores 0x82308-0x82328, in program order 46 47 48 49 42 43 44 45 50 *)
  assert (HS46 : store_ok rsegs m (wa (K3 + 46)) 1 = true).
  { replace (K3 + 46) with (K3 + 42 + 4) by lia.
    apply (wr_at_store_ok rsegs m (K3 + 42) 9 4 1%nat HWR); [lia | cbn; lia]. }
  step.
  match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (HS47 : store_ok rsegs mm (wa (K3 + 47)) 1 = true) by
      (replace (K3 + 47) with (K3 + 42 + 5) by lia;
       apply (wr_at_store_ok rsegs mm (K3 + 42) 9 5 1%nat); [repeat apply wr_at_write; exact HWR | lia | cbn; lia])
  end.
  step.
  match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (HS48 : store_ok rsegs mm (wa (K3 + 48)) 1 = true) by
      (replace (K3 + 48) with (K3 + 42 + 6) by lia;
       apply (wr_at_store_ok rsegs mm (K3 + 42) 9 6 1%nat); [repeat apply wr_at_write; exact HWR | lia | cbn; lia])
  end.
  step.
  match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (HS49 : store_ok rsegs mm (wa (K3 + 49)) 1 = true) by
      (replace (K3 + 49) with (K3 + 42 + 7) by lia;
       apply (wr_at_store_ok rsegs mm (K3 + 42) 9 7 1%nat); [repeat apply wr_at_write; exact HWR | lia | cbn; lia])
  end.
  step.
  match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (HS42 : store_ok rsegs mm (wa (K3 + 42)) 1 = true) by
      (replace (K3 + 42) with (K3 + 42 + 0) by lia;
       apply (wr_at_store_ok rsegs mm (K3 + 42) 9 0 1%nat); [repeat apply wr_at_write; exact HWR | lia | cbn; lia])
  end.
  step.
  match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (HS43 : store_ok rsegs mm (wa (K3 + 43)) 1 = true) by
      (replace (K3 + 43) with (K3 + 42 + 1) by lia;
       apply (wr_at_store_ok rsegs mm (K3 + 42) 9 1 1%nat); [repeat apply wr_at_write; exact HWR | lia | cbn; lia])
  end.
  step.
  match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (HS44 : store_ok rsegs mm (wa (K3 + 44)) 1 = true) by
      (replace (K3 + 44) with (K3 + 42 + 2) by lia;
       apply (wr_at_store_ok rsegs mm (K3 + 42) 9 2 1%nat); [repeat apply wr_at_write; exact HWR | lia | cbn; lia])
  end.
  step.
  match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (HS45 : store_ok rsegs mm (wa (K3 + 45)) 1 = true) by
      (replace (K3 + 45) with (K3 + 42 + 3) by lia;
       apply (wr_at_store_ok rsegs mm (K3 + 42) 9 3 1%nat); [repeat apply wr_at_write; exact HWR | lia | cbn; lia])
  end.
  step.
  match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (HS50 : store_ok rsegs mm (wa (K3 + 50)) 1 = true) by
      (replace (K3 + 50) with (K3 + 42 + 8) by lia;
       apply (wr_at_store_ok rsegs mm (K3 + 42) 9 8 1%nat); [repeat apply wr_at_write; exact HWR | lia | cbn; lia])
  end.
  step.
  (* the memory after the nine stores: the write set, the readable cells and the new shadow bytes *)
  match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (MU9 : munch [(K3 + 42, K3 + 51)] m mm) by
      (repeat (apply munch_write; [ | lia | simpl_sizes; lia | cbn [inside]; simpl_sizes; slia ]);
       apply munch_refl);
    assert (WM9 : wmono rsegs m mm) by (repeat apply wmono_write; apply wmono_refl);
    assert (ST9 : stk rsegs mm lo (bv_unsigned sp)) by
      (repeat (apply stk_write; [ | lia | simpl_sizes; lia ]); exact HST);
    assert (MI9 : mem_inv rsegs mm) by
      (apply mem_inv_store; [|simpl_sizes; exact HS50];
       apply mem_inv_store; [|simpl_sizes; exact HS45];
       apply mem_inv_store; [|simpl_sizes; exact HS44];
       apply mem_inv_store; [|simpl_sizes; exact HS43];
       apply mem_inv_store; [|simpl_sizes; exact HS42];
       apply mem_inv_store; [|simpl_sizes; exact HS49];
       apply mem_inv_store; [|simpl_sizes; exact HS48];
       apply mem_inv_store; [|simpl_sizes; exact HS47];
       apply mem_inv_store; [|simpl_sizes; exact HS46]; exact HMI);
    assert (B46 : b8 mm (K3 + 46) 0) by
      (repeat (apply f12_wother; [f12_zb | | lia | lia | lia]); apply f12_wsame; [f12_zb | lia | lia]);
    assert (B47 : b8 mm (K3 + 47) 0) by
      (repeat (apply f12_wother; [f12_zb | | lia | lia | lia]); apply f12_wsame; [f12_zb | lia | lia]);
    assert (B48 : b8 mm (K3 + 48) 0) by
      (repeat (apply f12_wother; [f12_zb | | lia | lia | lia]); apply f12_wsame; [f12_zb | lia | lia]);
    assert (B49 : b8 mm (K3 + 49) 0) by
      (repeat (apply f12_wother; [f12_zb | | lia | lia | lia]); apply f12_wsame; [f12_zb | lia | lia]);
    assert (B42 : b8 mm (K3 + 42) 0) by
      (repeat (apply f12_wother; [f12_zb | | lia | lia | lia]); apply f12_wsame; [f12_zb | lia | lia]);
    assert (B43 : b8 mm (K3 + 43) 0) by
      (repeat (apply f12_wother; [f12_zb | | lia | lia | lia]); apply f12_wsame; [f12_zb | lia | lia]);
    assert (B44 : b8 mm (K3 + 44) 0) by
      (repeat (apply f12_wother; [f12_zb | | lia | lia | lia]); apply f12_wsame; [f12_zb | lia | lia]);
    assert (B45 : b8 mm (K3 + 45) 0) by
      (repeat (apply f12_wother; [f12_zb | | lia | lia | lia]); apply f12_wsame; [f12_zb | lia | lia]);
    assert (B50 : b8 mm (K3 + 50) 0) by
      (apply f12_wsame; [f12_zb | lia | lia]);
    assert (SH9 : forall k, 0 <= k < 9 -> b8 mm (K3 + 42 + k) 0) by
      (intros k Hk;
       assert (Hk9 : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8) by lia;
       decompose [or] Hk9; subst k;
       first [ replace (K3 + 42 + 0) with (K3 + 42) by lia; exact B42
             | replace (K3 + 42 + 1) with (K3 + 43) by lia; exact B43
             | replace (K3 + 42 + 2) with (K3 + 44) by lia; exact B44
             | replace (K3 + 42 + 3) with (K3 + 45) by lia; exact B45
             | replace (K3 + 42 + 4) with (K3 + 46) by lia; exact B46
             | replace (K3 + 42 + 5) with (K3 + 47) by lia; exact B47
             | replace (K3 + 42 + 6) with (K3 + 48) by lia; exact B48
             | replace (K3 + 42 + 7) with (K3 + 49) by lia; exact B49
             | replace (K3 + 42 + 8) with (K3 + 50) by lia; exact B50 ]);
    assert (RD200 : ov_read_bytes rsegs mm (wa (A + 200)) 8 = Some (le8 (Z_to_bv 64 D))) by
      (apply f12_rd8; [ repeat (apply bytes_at_write_other; [ | lia | simpl_sizes; lia | simpl_sizes; lia ]);
                        exact H200 | apply length_le8 ]);
    assert (RD240 : ov_read_bytes rsegs mm (wa (A + 208)) 8 = Some (le8 (Z_to_bv 64 S0))) by
      (apply f12_rd8; [ repeat (apply bytes_at_write_other; [ | lia | simpl_sizes; lia | simpl_sizes; lia ]);
                        exact H240 | apply length_le8 ]);
    assert (BS9 : bytes_at rsegs mm S0 src) by
      (repeat (apply bytes_at_write_other; [ | lia | simpl_sizes; lia | rewrite Lsrc; simpl_sizes; lia ]);
       exact HbS);
    assert (RW9 : rw_cells rsegs mm D [CB 72 junk]) by
      (repeat (apply rw_cells_frame; [ | lia | simpl_sizes; lia | simpl_sizes; lia ]); exact HRWD);
    assert (AD9 : addressable mm D 72) by
      (apply (f12_addr72 mm D (K3 + 42)); [lia | lia | exact HD8 | exact HDK | intros t Ht; apply HappD; lia
                                          | exact SH9]);
    assert (AS9 : addressable mm S0 72) by
      (apply (f12_addr_munch [(K3 + 42, K3 + 51)] m mm S0 72 HADS MU9);
       intros i Hi; apply f12_out1;
       assert (Ei : shadow_addr (S0 + i) = K3 + 346 + i / 8) by
         (unfold shadow_addr; rewrite <- HSK;
          replace (S0 + i) with (i + (S0 / 8) * 8) by (Z.div_mod_to_equations; lia);
          rewrite Z.div_add by lia; lia);
       rewrite Ei; right; Z.div_mod_to_equations; lia);
    assert (AC9 : asan_cells mm) by
      (apply (HRT mm MU9 WM9); intros a Hin _; unfold f12_pre_F_shadow_R in Hin;
       destruct (SH9 (a - K3 - 42) ltac:(lia)) as (_ & _ & Hrd);
       pose proof (Hrd 0%nat ltac:(cbn; lia)) as Hb;
       change (Z.of_nat 0) with 0 in Hb; rewrite Z.add_0_r in Hb; cbn [nth_error] in Hb;
       replace (K3 + 42 + (a - K3 - 42)) with a in Hb by lia; exists (Z_to_bv 8 0); exact Hb);
    assert (RD9 : B.Prog.MemMono.rd_mono m mm) by
      (repeat apply B.Prog.MemMono.rd_mono_write; apply B.Prog.MemMono.rd_mono_refl)
  end.
  (* 0x8232c .. 0x8233c: the count, the two spill loads, the argument move and the call *)
  do 5 step.
  replace (ret_pc (Z_to_bv 64 0x82340)) with (Z_to_bv 64 0x82340)
    by (symmetry; apply ret_pc_even; [clear; lia | reflexivity]).
  apply evtF_done.
  eexists.
  split; [reflexivity|].
  split; [exact MU9|]. split; [exact WM9|]. split; [exact MI9|]. split; [exact ST9|].
  split; [exact AC9|]. split; [intros P HP; exact (B.ShadowRwOnT.shadow_rw_on_mem_mono P m _ HP WM9 RD9)|].
  split; [exact BS9|]. split; [exact RW9|].
  split; [exact AD9|]. split; [exact AS9 | exact SH9].
Qed.

(* Every shadow byte is present in mm: outside the nine stored bytes from shadow_rw m (munch), inside them from the
   clause's hypothesis.  This turns f12_pre_F's runtime clause into f12_pre_F_on's. *)
Lemma f12f_present : forall (m mm : word -> option byte) K3, shadow_rw m -> munch [(K3 + 42, K3 + 51)] m mm ->
  (forall a, f12_pre_F_shadow_R K3 a -> in_shadow a -> exists b, mrd rsegs mm (wa a) = Some b) ->
  forall a, in_shadow a -> exists b, mrd rsegs mm (wa a) = Some b.
Proof.
  intros m mm K3 HSW MU HW a Hin.
  assert (Hab : 0 <= a < 2 ^ 64)
    by (unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hin; lia).
  destruct (Z_lt_le_dec a (K3 + 42)) as [Hlo|Hge]; [|destruct (Z_lt_le_dec a (K3 + 51)) as [Hhi|Hge2]].
  - destruct (HSW a Hin) as (_ & b & Hb). exists b. unfold mrd in *.
    rewrite (MU (wa a)); [exact Hb | rewrite wa_unsigned by lia; apply f12_out1; left; exact Hlo].
  - apply HW; [unfold f12_pre_F_shadow_R; lia | exact Hin].
  - destruct (HSW a Hin) as (_ & b & Hb). exists b. unfold mrd in *.
    rewrite (MU (wa a)); [exact Hb | rewrite wa_unsigned by lia; apply f12_out1; right; exact Hge2].
Qed.

(* The old statement, from the narrowed one (the runtime clause through f12f_present; the post at P := fun _ => True,
   B.ShadowRwOn.shadow_rw_on_of_shadow_rw and B.ShadowRwOn.shadow_rw_of_on_all). *)
Lemma f12_pre_F :
  forall (RNG : footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7v s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A r K3 D S0 lo pc : Z) (src junk : list byte),
    s1v = Z_to_bv 64 A -> s3v = Z_to_bv 64 K3 ->
    (pc = 0x82308 \/ (pc = 0x82304 /\ a0v = Z_to_bv 64 r /\ 0 <= r < 2 ^ 63)) ->
    0 <= K3 -> K3 + 51 <= 2 ^ 64 ->
    0 <= D -> 0 <= S0 < 2 ^ 64 -> D + 72 <= S0 ->
    D mod 8 = 0 -> D / 8 + ASAN_K = K3 + 42 ->
    S0 mod 8 = 0 -> S0 / 8 + ASAN_K = K3 + 346 ->
    (forall t, 0 <= t <= 72 -> app_mem (D + t)) ->
    app_mem (S0 + 7) -> app_mem (S0 + 72) ->
    K3 + 51 <= A -> K3 + 51 <= lo ->
    (K3 + 51 <= D \/ D + 72 <= K3 + 42) ->
    (K3 + 51 <= S0 \/ S0 + 72 <= K3 + 42) ->
    wr_at rsegs m (K3 + 42) 9 ->
    shadow_rw m ->
    (forall mm, munch [(K3 + 42, K3 + 51)] m mm -> wmono rsegs m mm ->
       (forall a, in_shadow a -> exists b, mrd rsegs mm (wa a) = Some b) ->
       asan_cells mm /\ shadow_rw mm) ->
    bytes_at rsegs m (A + 200) (le8 (Z_to_bv 64 D)) ->
    bytes_at rsegs m (A + 208) (le8 (Z_to_bv 64 S0)) ->
    bytes_at rsegs m S0 src -> length src = 72%nat ->
    rw_cells rsegs m D [CB 72 junk] ->
    addressable m S0 72 ->
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) -> lo + ASAN_MEMCPY_K <= bv_unsigned sp ->
    HIGHMEM_BEG <= lo -> bv_unsigned sp <= APPMEM_END ->
    RT_HI <= D ->
    (D + 72 <= bv_unsigned sp - ASAN_MEMCPY_K \/ bv_unsigned sp <= D) ->
    (S0 + 72 <= bv_unsigned sp - ASAN_MEMCPY_K \/ bv_unsigned sp <= S0) ->
    rng RNG (K3 + 42) 9 -> rng RNG (A + 200) 8 -> rng RNG (A + 208) 8 ->
    evtF rsegs RNG
      (fun ms' => exists m1 : word -> option byte,
         ms' = MS (mkR (Z_to_bv 64 0x82340) sp gp tp t0 t1 t2 s0 s1v (Z_to_bv 64 D) (Z_to_bv 64 S0)
                       (Z_to_bv 64 72) a3 a4 a5 a6 a7 s2 s3v s4 (Z_to_bv 64 S0) s6 s7v s8 s9 s10 s11
                       t3 t4 t5 t6)
                  Fr (Z_to_bv 64 0x52164) fc None m1 (seg_rom rsegs)
         /\ munch [(K3 + 42, K3 + 51)] m m1
         /\ wmono rsegs m m1 /\ mem_inv rsegs m1
         /\ stk rsegs m1 lo (bv_unsigned sp)
         /\ asan_cells m1 /\ shadow_rw m1
         /\ bytes_at rsegs m1 S0 src /\ rw_cells rsegs m1 D [CB 72 junk]
         /\ addressable m1 D 72 /\ addressable m1 S0 72
         /\ (forall k, 0 <= k < 9 -> b8 m1 (K3 + 42 + k) 0))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7v s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7v s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A r K3 D S0 lo pc src junk E1 E3 Hpc HK0 HK1 HD0 HS0b HDS HD8 HDK HS8 HSK HappD HapS7 HapS72
    HKA HKlo HdjD HdjS HWR HSWm HRTnew H200 H240 HbS Lsrc HRWD HADS HMI HST Hlo1 Hlo2 Hspa HRTD HdjDW HdjSW
    Rsh9 R200 R208.
  eapply evtF_mono;
    [exact (f12_pre_F_on RNG ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7v s8 s9 s10 s11
              t3 t4 t5 t6 Fr fc m A r K3 D S0 lo pc src junk E1 E3 Hpc HK0 HK1 HD0 HS0b HDS HD8 HDK HS8 HSK HappD
              HapS7 HapS72 HKA HKlo HdjD HdjS HWR
              (fun mm MU WM HW => proj1 (HRTnew mm MU WM (f12f_present m mm K3 HSWm MU HW)))
              H200 H240 HbS Lsrc HRWD HADS HMI HST Hlo1 Hlo2 Hspa HRTD HdjDW HdjSW Rsh9 R200 R208)|].
  intros ms' (m1 & Ems & MU & WM & MI & ST & AC & SW & BS & RW & AD & AS & SH).
  exists m1. do 6 (split; [assumption|]).
  split; [exact (B.ShadowRwOn.shadow_rw_of_on_all m1 (SW _ (B.ShadowRwOn.shadow_rw_on_of_shadow_rw _ m HSWm)))|].
  do 4 (split; [assumption|]). exact SH.
Qed.
