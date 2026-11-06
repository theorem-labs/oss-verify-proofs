(* rule 24: no function proved. *)
(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
   source run: lib/B/Prog/Seg/F16.v, the inline bullet of seg_F16 (:1138) stepped under f16_run_lib (:957),
     proof lines 1324-1579, at a working branch 3803efccea0
     (blob 547556a873af3b64417785a3a0cd6e4e29c6b5a3);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
     lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
   compare: no <run>_of_F (an inline stretch, not a stated run). The stretch 0x823d8 -> 0x82464 has FOUR calls
     (record_sum_closes 0x823dc, joined_byte 0x82414, joined_byte 0x82438, reac_identity_ingest 0x82460), so the
     split rule (parent 23:50Z) gives four lemmas, each stopping AT a callee entry; no callee contract is stated
     here, the walk (a Theorem Labs lane) composes the callees itself:
       seg_F16_pre_F   re-runs F16.v:1381-1382  (0x823d8 ld a0,120(s1); 0x823dc jal record_sum_closes)
       seg_F16_pre2_F  re-runs F16.v:1423-1430  (0x823e0 .. 0x82414 jal joined_byte; = post1)
       seg_F16_pre3_F  re-runs F16.v:1472       (0x82418 .. 0x82438 jal joined_byte; = post2)
       seg_F16_pre4_F  re-runs F16.v:1528-1535  (0x8243c .. 0x82460 jal reac_identity_ingest; = post3)
     The post stretch of call k is the pre stretch of call k+1; the fourth callee returns to 0x82464, which IS
     the stretch's exit cut (Inv_B82464_at), so there is no _post4_F.
   There is no instrumented check in 0x823d8 .. 0x82464 (F16.v:26-27), so no shadow range appears below. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Fpu Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI BzBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Spec Require StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require record_sum_closes_c reac_identity_ingest_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require joined_byte_c joined_byte.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcFrag RcFragLib RcRec RcIdentModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import F16.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.
Open Scope Z_scope.

(* ---- stretch 1: 0x823d8 ld a0,120(s1) ; 0x823dc jal record_sum_closes (0x83614).
   The only access is the spill load [A + 120, A + 128). ---- *)
Lemma seg_F16_pre_F : forall (RNG : footprint)
  (ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A P : Z),
  s1v = Z_to_bv 64 A -> 0 <= A -> A + 448 <= 2 ^ 64 -> 0 <= P < 2 ^ 64 ->
  q64 m (A + 120) P ->
  rng RNG (A + 120) 8 ->
  evtF rsegs RNG
    (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x823e0) sp gp tp t0 t1 t2 s0 s1v (Z_to_bv 64 P)
                              a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         Fr (Z_to_bv 64 RSC.RECORD_SUM_CLOSES) fc None m (seg_rom rsegs))
    (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        Fr (Z_to_bv 64 0x823d8) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A P -> HA0 HA1 HPb Q120 R120.
  pose proof (f16_rd8 m _ _ Q120 ltac:(apply LMem.length_le8)) as RD120.
  step. step.
  apply evtF_done. reflexivity.
Qed.

(* ---- stretch 2 (= the post stretch of the record_sum_closes call): 0x823e0 .. 0x82414 jal joined_byte
   (0x836ac).  a0 = 1 is the callee's result (the record's window sums to 0 mod 128, F16.v:1397), and the
   `first` record's have field is 1 (F16.v:1217).  Accesses: [A + 168, A + 176), [FST, FST + 4),
   [A + 288, A + 296), [AP, AP + 2), [A + 312, A + 320). ---- *)
Lemma seg_F16_pre2_F : forall (RNG : footprint)
  (ra0 sp gp tp t0 t1 t2 s0 s1v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A FST AP ad Q : Z),
  s1v = Z_to_bv 64 A -> 0 <= A -> A + 448 <= 2 ^ 64 ->
  0 <= FST < 2 ^ 64 -> 0 <= AP < 2 ^ 64 -> 0 <= Q < 2 ^ 64 -> 0 <= ad < 65536 ->
  q64 m (A + 168) FST -> u32 m FST 1 ->
  q64 m (A + 288) AP -> u16 m AP ad ->
  q64 m (A + 312) Q ->
  rng RNG (A + 168) 8 -> rng RNG FST 4 -> rng RNG (A + 288) 8 -> rng RNG AP 2 -> rng RNG (A + 312) 8 ->
  evtF rsegs RNG
    (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x82418) sp gp tp t0 t1 t2 s0 s1v (Z_to_bv 64 FST)
                              (Z_to_bv 64 Q) (Z_to_bv 64 9) a3 a4 a5 a6 a7 s2 s3 s4
                              (Z_to_bv 64 ad) (Z_to_bv 64 FST) s7 s9 (Z_to_bv 64 Q) s10 s8 t3 t4 t5 t6)
                         Fr (Z_to_bv 64 JBC.JOINED_BYTE) fc None m (seg_rom rsegs))
    (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        Fr (Z_to_bv 64 0x823e0) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A FST AP ad Q -> HA0 HA1 HFSTb HAPb HQb Hadb Q168 Hhv Q288 HU Q312
    R168 Rhv R288 Rad R312.
  pose proof (f16_rd8 m _ _ Q168 ltac:(apply LMem.length_le8)) as RD168.
  pose proof (f16_rd4 m _ _ Hhv ltac:(apply LMem.length_le4)) as RDhv.
  pose proof (f16_rd8 m _ _ Q288 ltac:(apply LMem.length_le8)) as RD288.
  pose proof (f16_rd2 m _ _ HU ltac:(apply LMem.length_le2)) as RDad.
  pose proof (f16_rd8 m _ _ Q312 ltac:(apply LMem.length_le8)) as RD312.
  step. if_false.
  step. step. step. if_false.
  step. step. step. step. step. step. step. step. step. step.
  rewrite (f16_zx16 ad Hadb).
  apply evtF_done. reflexivity.
Qed.

(* ---- stretch 3 (= the post stretch of the first joined_byte call): 0x82418 .. 0x82438 jal joined_byte.
   a0 = the first joined byte (0 <= jb9 < 256, F16.v:1453).  No memory access at all. ---- *)
Lemma seg_F16_pre3_F : forall (RNG : footprint)
  (ra0 sp gp tp t0 t1 t2 s0 s1v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6v s7 s8v s9v s10 s11v t3 t4 t5 t6 : word)
  (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (jb9 : Z),
  0 <= jb9 < 256 ->
  evtF rsegs RNG
    (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x8243c) sp gp tp t0 t1 t2 s0 s1v s6v
                              s9v (Z_to_bv 64 10) a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 1)
                              (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 jb9)) 8))
                              s11v s8v s10 (Z_to_bv 64 (-8)) t3 t4 t5 t6)
                         Fr (Z_to_bv 64 JBC.JOINED_BYTE) fc None m (seg_rom rsegs))
    (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v (Z_to_bv 64 jb9) a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6v s7 s8v s9v s10 s11v t3 t4 t5 t6)
        Fr (Z_to_bv 64 0x82418) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6v s7 s8v s9v s10 s11v t3 t4 t5 t6
    Fr fc m jb9 Hjb9.
  step. step. step. step. step. step. step. step. step.
  apply evtF_done. reflexivity.
Qed.

(* ---- stretch 4 (= the post stretch of the second joined_byte call): 0x8243c .. 0x82460 jal
   reac_identity_ingest (0x87e0c).  a0 = the second joined byte; the two bytes join to the address cell's value
   ad (joined_close, F16.v:1267-1271), so `bne a0,s5` is not taken.  Accesses: [A + 288, A + 296), [AP, AP + 2),
   [A + 304, A + 312), [PPC, PPC + 8), [A + 296, A + 304), [PNC, PNC + 8), [A + 176, A + 184). ---- *)
Lemma seg_F16_pre4_F : forall (RNG : footprint)
  (ra0 sp gp tp t0 t1 t2 s0 s1v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A AP ad PPC PNC ID jb9 jb10 p len : Z),
  s1v = Z_to_bv 64 A -> 0 <= A -> A + 448 <= 2 ^ 64 ->
  0 <= jb9 < 256 -> 0 <= jb10 < 256 -> 0 <= ad < 65536 -> ad = jb10 + 256 * jb9 ->
  0 <= AP < 2 ^ 64 -> 0 <= PPC < 2 ^ 64 -> 0 <= PNC < 2 ^ 64 -> 0 <= ID < 2 ^ 64 ->
  0 <= p < 2 ^ 64 -> 0 <= len < 2 ^ 64 ->
  q64 m (A + 288) AP -> u16 m AP ad ->
  q64 m (A + 304) PPC -> q64 m PPC p ->
  q64 m (A + 296) PNC -> q64 m PNC len ->
  q64 m (A + 176) ID ->
  rng RNG (A + 288) 8 -> rng RNG AP 2 -> rng RNG (A + 304) 8 -> rng RNG PPC 8 ->
  rng RNG (A + 296) 8 -> rng RNG PNC 8 -> rng RNG (A + 176) 8 ->
  evtF rsegs RNG
    (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x82464) sp gp tp t0 t1 t2 s0 s1v (Z_to_bv 64 ID)
                              (Z_to_bv 64 ad) (Z_to_bv 64 p) (Z_to_bv 64 len) a4 a5 a6 a7
                              s2 s3 s4 (Z_to_bv 64 ad) s6
                              (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 jb9)) 8))
                              s8 s9 s10 s11 t3 t4 t5 t6)
                         Fr (Z_to_bv 64 IGC.REAC_IDENTITY_INGEST) fc None m (seg_rom rsegs))
    (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v (Z_to_bv 64 jb10) a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 (Z_to_bv 64 ad) s6 (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 jb9)) 8))
             s8 s9 s10 s11 t3 t4 t5 t6)
        Fr (Z_to_bv 64 0x8243c) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A AP ad PPC PNC ID jb9 jb10 p len -> HA0 HA1 Hjb9 Hjb10 Hadb Ead
    HAPb HPPCb HPNCb HIDb Hpb Hlenb Q288 HU Q304 Qpp Q296 Qpn Q176
    R288 Rad R304 Rpp R296 Rpn R176.
  pose proof (f16_rd8 m _ _ Q288 ltac:(apply LMem.length_le8)) as RD288.
  pose proof (f16_rd2 m _ _ HU ltac:(apply LMem.length_le2)) as RDad.
  pose proof (f16_rd8 m _ _ Q304 ltac:(apply LMem.length_le8)) as RD304.
  pose proof (f16_rd8 m _ _ Qpp ltac:(apply LMem.length_le8)) as RDpp.
  pose proof (f16_rd8 m _ _ Q296 ltac:(apply LMem.length_le8)) as RD296.
  pose proof (f16_rd8 m _ _ Qpn ltac:(apply LMem.length_le8)) as RDpn.
  pose proof (f16_rd8 m _ _ Q176 ltac:(apply LMem.length_le8)) as RD176.
  step.
  rewrite (f16_or8 jb10 jb9 Hjb10 Hjb9), <- Ead.
  rewrite ?(f16_zx16 ad Hadb).
  step. if_false.
  step. step. step. step. step. step. step. step.
  rewrite ?(f16_zx16 ad Hadb).
  apply evtF_done. reflexivity.
Qed.
