(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names and numbers changed; 1539 of its 1674 lines of code are new or changed and 876 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/R14.v; 75 of its 176 lines of code are new or changed and 1573 lines of the source are left out. *)
(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
   source runs: lib/B/Prog/Seg/R14.v r14_loop :621 and r14_evt :703 at
     a working branch 3803efccea0 (blob 144a433a8bfcc24fbf9f6d273a2037d6e2ac66a5);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
         lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
   compare: r14_evt calls reac_box_catalogue_match, so it is split and there is no r14_evt_of_F.
     r14_loop_F re-runs R14.v:626-678 (the 32-turn block-sum loop) under an evtF EXIT hypothesis; the source
     r14_loop cannot be re-derived from it (its EXIT is an evt, which no evtF follows from), so it has no
     `_of_F`.  r14_pre_F re-runs R14.v:738-781 up to the callee entry 0x84e40 (the loop, then 0x818dc j,
     0x81990 zext.b, 0x81994 beqz, 0x8199c mv a0,s4, 0x819a0 mv a1,s2, 0x819a4 jal), and r14_post_F re-runs
     R14.v:764-777 (the run's post r14_post from the callee post facts; no instruction follows the return
     point 0x819a8, which is the run's exit cut).  No `_F` steps through the callee, and this file states no
     callee contract. *)
(* rule 24: no function proved. *)
(* Memory the pre stretch touches, per loop turn i (R14.v:648-677): the shadow byte of p + 18 + i at
   off + (p + 18 + i) / 8 (0x818bc lb, the instrumented check) and the block byte at p + 18 + i (0x818c4 lbu).
   Over the 32 turns that is [p + 18, p + 50) and the shadow bytes
   [off + (p + 18) / 8, off + (p + 49) / 8]; the block is not 8-aligned in general, so the shadow length is
   the unaligned form (p + 49) / 8 - (p + 18) / 8 + 1.  Nothing is stored, and the five instructions between the
   loop exit and the jal touch no memory. *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcBox RcLay RcEmit RcPorts RcFin.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcFinLib RcSynthLib RcLib RcAsan RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcMatch RcRecLib RcFragLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcSynth RcIdentModel RcFrag.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import RcAsanRT asan_stack_malloc_c RcAsanFP RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require reac_box_catalogue_match_c reac_ctrl_parse_c bcmp_wrap_c memcmp_c
  reac_ctrl_build_as_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_fs.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require R14.
Import ListNotations.
Import YK11.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Open Scope Z_scope.

Module CMC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_box_catalogue_match_c.

(* ---- the footprint twin of the 32-turn block-sum loop 0x818a8 .. 0x818dc (no memory write) ---- *)

Section LoopF.
  Variables (ra0 sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p off : Z) (bs : list byte)
    (W : list ivl) (Q : machine_state -> Prop) (RNG : footprint).
  Hypothesis Hp : 4096 <= p.
  Hypothesis Hp50 : p + 50 <= APPMEM_END.
  Hypothesis Hlen : length bs = 32%nat.
  Hypothesis HB : bytes_at rsegs m (p + 18) bs.
  Hypothesis HSR : asan_shadow_rd rsegs m off (p + 18) 32 W.
  Hypothesis HAD : asan_addressable rsegs m off (p + 18) 32.
  Hypothesis Gdat : rng RNG (p + 18) 32.
  Hypothesis Gsh : rng RNG (off + (p + 18) / 8) ((p + 49) / 8 - (p + 18) / 8 + 1).

  Abbreviation ST pc x10 x11 x12 x14 x15 x16 :=
    (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 x10 x11 x12 (Z_to_bv 64 (18446744073709551598 - p)) x14 x15 x16 a7
             s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 off) (Z_to_bv 64 32) t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

  Hypothesis EXIT : forall x10 x12 x14 x15 x16,
    evtF rsegs RNG Q (ST 0x818dc x10 (Z_to_bv 64 (psum bs 32)) x12 x14 x15 x16).

  Lemma r14_loop_F : forall n i x15 x16,
    (i + n = 32)%nat -> (0 < n)%nat ->
    evtF rsegs RNG Q (ST 0x818a8 (Z_to_bv 64 (p + 18 + Z.of_nat i)) (Z_to_bv 64 (psum bs i))
                         (Z_to_bv 64 (p + 18 + Z.of_nat i)) (Z_to_bv 64 (32 - Z.of_nat i)) x15 x16).
  Proof using Hp Hp50 Hlen HB HSR HAD Gdat Gsh EXIT.
    assert (HAPPv : APPMEM_END = 140737488355328) by reflexivity.
    induction n as [|n IH]; intros i x15 x16 Hin Hn; [lia|].
    assert (BODY : forall y15 y16,
      evtF rsegs RNG Q (ST 0x818c4 (Z_to_bv 64 (p + 18 + Z.of_nat i)) (Z_to_bv 64 (psum bs i))
                           (Z_to_bv 64 (p + 18 + Z.of_nat i)) (Z_to_bv 64 (32 - Z.of_nat i)) y15 y16)).
    { intros y15 y16.
      pose proof (rd_byte rsegs m (p + 18) bs i HB ltac:(lia)) as RD.
      pose proof (psum_range bs i) as PR.
      step. step. step. step.
      rewrite psum_S_zxb.
      step. step.
      rewrite (rc_eqb0 (32 - Z.of_nat i + -1)) by lia.
      destruct n as [|n].
      - replace (32 - Z.of_nat i + -1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
        cbn [negb].
        replace i with 31%nat in * by lia.
        apply EXIT.
      - replace (32 - Z.of_nat i + -1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
        cbn [negb].
        replace (32 - Z.of_nat i + -1) with (32 - Z.of_nat (S i)) by lia.
        replace (p + 18 + Z.of_nat i + 1) with (p + 18 + Z.of_nat (S i)) by lia.
        apply (IH (S i)); lia. }
    (* 0x818a8 add a5,a3,a4 ; 0x818ac bne a5,s11 -- the UBSan trap test, not taken *)
    step. step.
    lazymatch goal with
    | |- context [bv_eqb (Z_to_bv 64 ?E) (Z_to_bv 64 32)] =>
        rewrite (eqb_le64 E 32) by lia;
        replace (E =? 32) with false by (symmetry; apply Z.eqb_neq; lia)
    end.
    cbn [negb].
    (* 0x818b4 srli / 0x818b8 add / 0x818bc lb -- the instrumented check, error path not reached *)
    destruct (asan_shadow_read rsegs m off (p + 18) 32 W (Z.of_nat i) HSR ltac:(lia)) as (k & RK & BK).
    pose proof (HAD (Z.of_nat i) k ltac:(lia) BK) as OK.
    pose proof (rc_byte_signed k) as KR.
    clear BK.
    step.
    rewrite (unsigned_lit (p + 18 + Z.of_nat i)) by lia. rewrite rc_shr3.
    step.
    step.
    clear RK.
    step.
    unfold sxb. rewrite (rc_eqb0_signed (bv_signed k)) by lia.
    destruct (Z.eqb_spec (bv_signed k) 0) as [K0|K0]; cbn [negb].
    - apply BODY.
    - step.
      rewrite (unsigned_lit (p + 18 + Z.of_nat i)) by lia. rewrite rc_land7.
      step.
      rewrite (rc_lts_signed ((p + 18 + Z.of_nat i) mod 8) (bv_signed k))
        by (pose proof (Z.mod_pos_bound (p + 18 + Z.of_nat i) 8 ltac:(lia)); lia).
      replace ((p + 18 + Z.of_nat i) mod 8 <? bv_signed k) with true
        by (symmetry; apply Z.ltb_lt; destruct OK; lia).
      apply BODY.
  Qed.
End LoopF.

(* ---- the pre stretch: 0x818a8 .. 0x819a4, stopping AT the catalogue-match entry 0x84e40 ---- *)

Lemma r14_pre_F :
  forall (RNG : footprint)
         (ra0 gp tp t0 t1 t2 s0 s1 a5 a6 a7 s3 s5 s6 s7 s8 s9 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (p Sp len : Z) (i : nat) (bs : list byte),
    4096 <= p -> p + 50 <= APPMEM_END -> 0 <= len < 2 ^ 64 -> (i < 32)%nat ->
    length bs = 32%nat -> bytes_at rsegs m (p + 18) bs -> psum bs 32 mod 256 = 0 ->
    addressable m (p + 50 - 50) 50 ->
    rng RNG (p + 18) 32 ->
    rng RNG (ASAN_K + (p + 18) / 8) ((p + 49) / 8 - (p + 18) / 8 + 1) ->
    evtF rsegs RNG
      (fun ms' => exists (a0' a1' a2' a4' a5' a6' : word),
         ms' = MS (mkR (Z_to_bv 64 0x819a8) (Z_to_bv 64 Sp) gp tp t0 t1 t2 s0 s1
                       a0' a1' a2' (Z_to_bv 64 (18446744073709551598 - p)) a4' a5' a6' a7
                       (Z_to_bv 64 len) s3 (Z_to_bv 64 p) s5 s6 s7 s8 s9 (Z_to_bv 64 ASAN_K) (Z_to_bv 64 32)
                       t3 t4 t5 t6)
                  F (Z_to_bv 64 CMC.REAC_BOX_CATALOGUE_MATCH) fc None m (seg_rom rsegs) /\
         a0' = Z_to_bv 64 p /\ a1' = Z_to_bv 64 len)
      (MS (mkR ra0 (Z_to_bv 64 Sp) gp tp t0 t1 t2 s0 s1
               (Z_to_bv 64 (p + 18 + Z.of_nat i)) (Z_to_bv 64 (psum bs i)) (Z_to_bv 64 (p + 18 + Z.of_nat i))
               (Z_to_bv 64 (18446744073709551598 - p)) (Z_to_bv 64 (32 - Z.of_nat i)) a5 a6 a7
               (Z_to_bv 64 len) s3 (Z_to_bv 64 p) s5 s6 s7 s8 s9 (Z_to_bv 64 ASAN_K) (Z_to_bv 64 32)
               t3 t4 t5 t6)
          F (Z_to_bv 64 0x818a8) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 gp tp t0 t1 t2 s0 s1 a5 a6 a7 s3 s5 s6 s7 s8 s9 t3 t4 t5 t6 F fc m p Sp len i bs
    Hp Hp50 Hlen64 Hi Hbsl Hbsat Hsum HADp Gdat Gsh.
  assert (HAPPv : APPMEM_END = 140737488355328) by reflexivity.
  replace (p + 50 - 50) with p in HADp by lia.
  pose proof (addressable_sub m p 50 18 32 HADp ltac:(lia) ltac:(lia) ltac:(lia)) as HAD18.
  pose proof (rt_shadow_rd m (p + 18) 32 [] HAD18 (fun x _ => I)) as HSRd.
  pose proof (rt_addressable m (p + 18) 32 HAD18) as HADr.
  refine (r14_loop_F ra0 (Z_to_bv 64 Sp) gp tp t0 t1 t2 s0 s1 a7 (Z_to_bv 64 len) s3 (Z_to_bv 64 p) s5 s6 s7 s8
           s9 t3 t4 t5 t6 F fc m p ASAN_K bs [] _ RNG
           Hp Hp50 Hbsl Hbsat HSRd HADr Gdat Gsh _ (32 - i)%nat i a5 a6 ltac:(lia) ltac:(lia)).
  intros x10 x12 x14 x15 x16.
  pose proof (psum_range bs 32) as PR32. change (Z.of_nat 32) with 32 in PR32.
  (* 0x818dc j 81990 ; 0x81990 zext.b a0,a1 ; 0x81994 beqz a0,8199c -- the sum closes *)
  step. step. step.
  rewrite rf_land255 by lia.
  rewrite Hsum. change (0 =? 0) with true. cbn [negb]. cbv iota.
  (* 0x8199c mv a0,s4 ; 0x819a0 mv a1,s2 ; 0x819a4 jal reac_box_catalogue_match *)
  step. step.
  rewrite ?(Z.add_0_r p), ?(Z.add_0_r len), ?(Z.add_0_l p), ?(Z.add_0_l len).
  step.
  apply evtF_done. do 6 eexists.
  split; [reflexivity|]. split; first [reflexivity | f_equal; lia].
Qed.

(* ---- the post stretch: the run's post r14_post at the return point 0x819a8, from the callee post facts
   R14.v:764-777.  No instruction lies between the return point and the run's exit cut, so this stretch steps
   nothing: it is the packaging the proved run does after its evt_cut. ---- *)

Lemma r14_post_F :
  forall (RNG : footprint)
         (gp tp t0' t1' t2' s0 s1 a1' a2' a3' a4' a5' a6' a7' s3 s5 s6 s7 s8 s9 t3' t4' t5' t6' : word)
         (F : bvmap 5 word) (fc : bv 32) (m m' : word -> option byte)
         (p Sp FS len : Z) (fb : list byte),
    munch ([(Sp - CMC.CM_K, Sp)] ++ fp_w [0%nat; 1%nat; 2%nat] FS ++
           [(shadow_addr (Sp - CMC.CM_K), shadow_addr Sp)]) m m' ->
    wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' (Sp - CMC.CM_K) Sp ->
    asan_cells m' -> shadow_rw m' -> addressable m' (Sp - CMC.CM_K) CMC.CM_K ->
    fp [0%nat; 1%nat; 2%nat] m' (bv_unsigned tp) FS (Sp - CMC.CM_K) Sp
      (CMC.reac_box_catalogue_match_W Sp) (CMC.reac_box_catalogue_match_D p len) ->
    CMC.reac_box_catalogue_match_tls m' (bv_unsigned tp) FS (Sp - CMC.CM_K) Sp ->
    evtF rsegs RNG
      (R14.r14_post F fc m (Z_to_bv 64 Sp) gp tp s0 s1 s3 s5 s6 s7 s8 s9 p Sp FS len fb)
      (MS (mkR (Z_to_bv 64 0x819a8) (Z_to_bv 64 Sp) gp tp t0' t1' t2' s0 s1
               (Z_to_bv 64 (want CMC.CM_T len fb)) a1' a2' a3' a4' a5' a6' a7'
               (Z_to_bv 64 len) s3 (Z_to_bv 64 p) s5 s6 s7 s8 s9 (Z_to_bv 64 ASAN_K) (Z_to_bv 64 32)
               t3' t4' t5' t6')
          F (Z_to_bv 64 0x819a8) fc None m' (seg_rom rsegs)).
Proof.
  intros RNG gp tp t0' t1' t2' s0 s1 a1' a2' a3' a4' a5' a6' a7' s3 s5 s6 s7 s8 s9 t3' t4' t5' t6'
    F fc m m' p Sp FS len fb MU WM MI ST AC' SW' AW FP' TLS'.
  apply evtF_done. unfold R14.r14_post. do 2 eexists. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
  split; [exact AC'|]. split; [exact SW'|]. split; [exact AW|]. split; [exact FP' | exact TLS'].
Qed.
