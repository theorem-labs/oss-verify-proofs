(* rule 24: no function proved. *)
(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17; measured against this image only;
   source run: lib/B/Prog/Seg/F11.v, segment S_F11 0x8226c -> 0x82304.  F11.v states no run lemma for it (its only
     run lemma, f11_lu_evt :93, is the engine bridge lib.Lib Exec.evt -> UL evt, which records no address and has
     no footprint twin); the run is stepped INLINE inside seg_F11 under Tac_slot.sl_run (F11.v:800-948), so these
     two lemmas are cut mechanically out of the segment proof's own steps, as the brief prescribes for an inline
     stretch.  Source at a working branch 3803efccea0
     (blob 6235924c49ee6a73221a4ddd9042982052e3ea53);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
         lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
   split (parent 23:50Z: split at EVERY call, never state a callee contract locally): the stretch calls
     record_sum_closes (0x83614) at 0x82284 and reac_identity_ingest (0x87e0c) at 0x82300.
     seg_F11_pre_F  re-runs F11.v lines 816-819 (0x8226c -> 0x83614, ra = 0x82288);
     seg_F11_pre2_F re-runs F11.v lines 886-906 (0x82288, the return pc of the first call, -> 0x87e0c,
       ra = 0x82304).
     The second callee's return pc 0x82304 IS the segment's exit cut (Inv_B82304_at), so no post stretch exists.
     The UL engine of the source proof and lib.Lib have the same MS / mkR bodies (F11.v f11_MS_ul / f11_mkR_ul),
     so the same script runs on the lib.Lib footprint goal with StepF's `step`.
   compare: no <run>_of_F (the source states no run lemma; the stretches re-run the lines cited above). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI BzBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require record_sum_closes_c reac_identity_ingest_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcFrag RcParse RcReply RcRec RcIdentModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot F11.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.
Open Scope Z_scope.

(* A carried byte range in the `ov_read_bytes _ _ _ n = Some bs` form the step tactic consumes, over lib.Lib's
   Mem.wa (F11.v's own f11_rd1 / f11_rd2 / f11_rd8 state it over the UL copy of wa). *)
Lemma f11F_rd : forall m a (bs : list byte) (n : nat),
  bytes_at rsegs m a bs -> length bs = n -> ov_read_bytes rsegs m (wa a) n = Some bs.
Proof.
  intros m a bs n H Hl.
  pose proof (bytes_at_ov_read rsegs m a bs 0 n H ltac:(lia)) as HH.
  change (Z.of_nat 0) with 0 in HH. rewrite Z.add_0_r, skipn_O in HH.
  rewrite firstn_all2 in HH by lia. exact HH.
Qed.

(* F11.v's f11_zx16 / f11_cmp16, restated over lib.Lib's zx16 / zxb (F11.v states them over the UL copies, which
   are different constants, so its rewrites miss this goal).  The bodies are F11.v's. *)
Lemma f11F_zx16 : forall v, 0 <= v < 65536 -> zx16 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof.
  intros v Hv. unfold zx16. rewrite (unsigned_lit v) by lia.
  rewrite Z.mod_small by (change (2 ^ 16) with 65536; lia). reflexivity.
Qed.
Lemma f11F_cmp16 : forall b36 b37 : byte,
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb b36)) 8))) (bv_unsigned (zxb b37)))
  = Z_to_bv 64 (bv_unsigned b37 + 256 * bv_unsigned b36).
Proof.
  intros b36 b37. pose proof (f11_ubv b36) as R6. pose proof (f11_ubv b37) as R7.
  unfold zxb. rewrite (unsigned_lit (bv_unsigned b36)), (unsigned_lit (bv_unsigned b37)) by lia.
  rewrite (unsigned_lit (Z.shiftl (bv_unsigned b36) 8)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  rewrite Z.lor_comm, lor_shiftl8_add by lia. reflexivity.
Qed.

(* ---- Stretch 1: 0x8226c -> the record_sum_closes entry 0x83614 (ra = 0x82288).
     0x8226c li a0,-17 ; 0x82270 ld a2,312(s1) ; 0x82274 bltu a0,a2 (T23, not taken: blk + 16 does not wrap)
     0x82278 ld a0,312(s1) ; 0x8227c addi a0,a0,16 ; 0x82280 addi a1,a1,5 ; 0x82284 jal 0x83614
   Region: [A+312, A+320) read twice (the block spill).  No instrumented check in this stretch. ---- *)
Lemma seg_F11_pre_F :
  forall (RNG : footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1v a2v a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10v s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A phi L : Z),
    s1v = Z_to_bv 64 A -> a1v = Z_to_bv 64 L -> s10v = Z_to_bv 64 ASAN_K ->
    0 <= phi -> phi + 50 <= 2 ^ 64 ->
    bytes_at rsegs m (A + 312) (le8 (Z_to_bv 64 (phi + 18))) ->
    rng RNG (A + 312) 8 ->
    evtF rsegs RNG
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x82288) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A)
                                (Z_to_bv 64 (phi + 34)) (Z_to_bv 64 (L + 5)) (Z_to_bv 64 (phi + 18))
                                a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
                           Fr (Z_to_bv 64 0x83614) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1v a2v a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10v s11
               t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x8226c) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1v a2v a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10v s11 t3 t4 t5 t6
    Fr fc m A phi L -> -> -> Hphi0 Hphi1 H312 R312.
  pose proof (f11F_rd m (A + 312) _ 8%nat H312 ltac:(apply length_le8)) as RD312.
  (* 0x8226c li a0,-17 ; 0x82270 ld a2,312(s1) ; 0x82274 bltu a0,a2 (T23) *)
  step. step. step. rewrite (f11_ltu_false _ (phi + 18)) by f11_mlia. cbv iota.
  (* 0x82278 ld a0,312(s1) ; 0x8227c addi a0,a0,16 ; 0x82280 addi a1,a1,5 ; 0x82284 jal record_sum_closes *)
  step. step. step. step.
  apply evtF_done. reflexivity.
Qed.

(* ---- Stretch 2: 0x82288 (the return pc of record_sum_closes) -> the reac_identity_ingest entry 0x87e0c
   (ra = 0x82304).
     0x82288 beqz a0 (a0 = 1, the sum closes: not taken)
     0x8228c-0x822a0 T24 / T25: blk + 18 / blk + 19 do not wrap, not taken
     0x822a4-0x822b4 a4 = blk ; a0 = phi + 36 ; lb a2 = the shadow byte of phi + 36 (0)
     0x822b8-0x822c0 a1 = the u16 at [A+288] = fr + 256 ; bnez a2 not taken
     0x822c4-0x822d8 the same for phi + 37 ; a0 = G[36]
     0x822dc-0x822e8 a0 = G[36] << 8 | G[37] ; bne a0,a1 not taken (the reply address agrees)
     0x822ec-0x82300 a2 = [[A+304]] = phi + 38 ; a3 = [[A+296]] = L ; a0 = [A+176] = id ; jal 0x87e0c
   Regions (all reads): [A+312, +8) three times, [A+288, +8), [A+304, +8), [A+296, +8), [A+176, +8),
   [fr+256, +2), [fr+272, +8), [fr+304, +8), [phi+36, +1), [phi+37, +1), and the two shadow bytes
   (phi + 36) >> 3 + ASAN_K and (phi + 37) >> 3 + ASAN_K, which the two instrumented checks load. ---- *)
Lemma seg_F11_pre2_F :
  forall (RNG : footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1v a2v a3v a4v a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10v s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A phi L fr AD : Z) (b36 b37 : byte),
    s1v = Z_to_bv 64 A -> s10v = Z_to_bv 64 ASAN_K -> a0v = Z_to_bv 64 1 ->
    0 <= phi -> phi + 50 <= 2 ^ 64 ->
    AD = bv_unsigned b37 + 256 * bv_unsigned b36 ->
    bytes_at rsegs m (A + 312) (le8 (Z_to_bv 64 (phi + 18))) ->
    bytes_at rsegs m (A + 288) (le8 (Z_to_bv 64 (fr + 256))) ->
    bytes_at rsegs m (A + 304) (le8 (Z_to_bv 64 (fr + 272))) ->
    bytes_at rsegs m (A + 296) (le8 (Z_to_bv 64 (fr + 304))) ->
    bytes_at rsegs m (A + 176) (le8 (Z_to_bv 64 (fr + 2688))) ->
    bytes_at rsegs m (fr + 256) (le2 (Z_to_bv 64 (bv_unsigned b37 + 256 * bv_unsigned b36))) ->
    bytes_at rsegs m (fr + 272) (le8 (Z_to_bv 64 (phi + 38))) ->
    bytes_at rsegs m (fr + 304) (le8 (Z_to_bv 64 L)) ->
    bytes_at rsegs m (phi + 36) [b36] -> bytes_at rsegs m (phi + 37) [b37] ->
    bytes_at rsegs m (Z.shiftr (phi + 36) 3 + ASAN_K) [Z_to_bv 8 0] ->
    bytes_at rsegs m (Z.shiftr (phi + 37) 3 + ASAN_K) [Z_to_bv 8 0] ->
    rng RNG (A + 312) 8 -> rng RNG (A + 288) 8 -> rng RNG (A + 304) 8 -> rng RNG (A + 296) 8 ->
    rng RNG (A + 176) 8 ->
    rng RNG (fr + 256) 2 -> rng RNG (fr + 272) 8 -> rng RNG (fr + 304) 8 ->
    rng RNG (phi + 36) 1 -> rng RNG (phi + 37) 1 ->
    rng RNG (Z.shiftr (phi + 36) 3 + ASAN_K) 1 -> rng RNG (Z.shiftr (phi + 37) 3 + ASAN_K) 1 ->
    evtF rsegs RNG
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x82304) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A)
                                (Z_to_bv 64 (fr + 2688)) (Z_to_bv 64 AD) (Z_to_bv 64 (phi + 38))
                                (Z_to_bv 64 L) (Z_to_bv 64 (phi + 18)) a5 a6 a7
                                s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
                           Fr (Z_to_bv 64 0x87e0c) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1v a2v a3v a4v a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10v s11
               t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82288) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1v a2v a3v a4v a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10v s11 t3 t4 t5 t6
    Fr fc m A phi L fr AD b36 b37 -> -> -> Hphi0 Hphi1 EAD H312 H288 H304 H296 H176 Hpa Hpp Hpn Hb36 Hb37
    Hsh36 Hsh37 R312 R288 R304 R296 R176 Rpa Rpp Rpn Rb36 Rb37 Rsh36 Rsh37.
  subst AD.
  assert (HADb : 0 <= bv_unsigned b37 + 256 * bv_unsigned b36 < 65536)
    by (pose proof (f11_ubv b36); pose proof (f11_ubv b37); lia).
  pose proof (f11F_rd m (A + 312) _ 8%nat H312 ltac:(apply length_le8)) as RD312.
  pose proof (f11F_rd m (A + 288) _ 8%nat H288 ltac:(apply length_le8)) as RD288.
  pose proof (f11F_rd m (A + 304) _ 8%nat H304 ltac:(apply length_le8)) as RD304.
  pose proof (f11F_rd m (A + 296) _ 8%nat H296 ltac:(apply length_le8)) as RD296.
  pose proof (f11F_rd m (A + 176) _ 8%nat H176 ltac:(apply length_le8)) as RD176.
  pose proof (f11F_rd m (fr + 256) _ 2%nat Hpa ltac:(apply length_le2)) as RDpa.
  pose proof (f11F_rd m (fr + 272) _ 8%nat Hpp ltac:(apply length_le8)) as RDpp.
  pose proof (f11F_rd m (fr + 304) _ 8%nat Hpn ltac:(apply length_le8)) as RDpn.
  pose proof (f11F_rd m (phi + 36) _ 1%nat Hb36 ltac:(reflexivity)) as RDb36.
  pose proof (f11F_rd m (phi + 37) _ 1%nat Hb37 ltac:(reflexivity)) as RDb37.
  pose proof (f11F_rd m _ _ 1%nat Hsh36 ltac:(reflexivity)) as RDsh36.
  pose proof (f11F_rd m _ _ 1%nat Hsh37 ltac:(reflexivity)) as RDsh37.
  (* 0x82288 beqz a0 : a0 = 1, not taken *)
  step. if_false.
  (* 0x8228c li a0,-19 ; ld a1,312(s1) ; bltu (T24) and 0x82298 li a0,-20 ; ld ; bltu (T25): not taken *)
  step. step. step. rewrite (f11_ltu_false _ (phi + 18)) by f11_mlia. cbv iota.
  step. step. step. rewrite (f11_ltu_false _ (phi + 18)) by f11_mlia. cbv iota.
  (* 0x822a4 ld a4,312(s1) ; addi a0,a4,18 ; srli a1,a0,3 ; add a1,a1,s10 ; lb a2 = shadow(phi + 36) = 0 *)
  step. step. step. step. rewrite (unsigned_lit (phi + 36)) by lia.
  step.
  (* 0x822b8 ld a1,288(s1) ; 0x822bc lhu a1,0(a1) ; 0x822c0 bnez a2 (= 0) not taken *)
  step. step. step. if_false.
  (* 0x822c4 addi a2,a4,19 ; srli a3,a2,3 ; add a3,a3,s10 ; lb a3 = shadow(phi + 37) = 0 *)
  step. step. step. rewrite (unsigned_lit (phi + 37)) by lia.
  step.
  (* 0x822d4 lbu a0,0(a0) = G[36] ; 0x822d8 bnez a3 (= 0) not taken ; 0x822dc lbu a2,0(a2) = G[37] *)
  step. step. if_false. step.
  (* 0x822e0 slli a0,a0,8 ; 0x822e4 or a0,a0,a2 ; 0x822e8 bne a0,a1 : the two addresses agree, not taken *)
  step. step. step.
  rewrite (f11F_cmp16 b36 b37), (f11F_zx16 _ HADb).
  rewrite bv_eqb_refl; cbn [negb]; cbv iota.
  (* 0x822ec-0x822fc: a2 = pl = phi + 38, a3 = pll = L, a0 = id = fr + 2688 ; 0x82300 jal ingest *)
  step. step. step. step. step. step.
  apply evtF_done. reflexivity.
Qed.
