(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* reloc14 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.cks Require Import CkTables CkModel CkMathCrc CkWalk.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.CkA Require Import CrcAGlue CrcAMirror.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.CkB Require Import CkBImg CkBTables CkBShadow CkBIface CkBKit CrcBGlue CrcBMirror CrcB_zkit CrcB_zbraid.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.LibA Require Import StepF.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_hint ::= crcz_acc_hint.

Section P.
  Variables (RNG : footprint)
            (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : amem) (lo A : Z) (bs : list Z).
  Hypothesis LOS : lo <= bv_unsigned sp - 144.
  Hypothesis KLO : KHIGH <= lo.
  Hypothesis CKSH : ck_sh m.
  Hypothesis BUF : ck_buf RNG m A bs.
  Hypothesis A1 : 1 <= A.
  Hypothesis ALO : A + Z.of_nat (length bs) <= lo.
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RISH : rng_aimg_sh RNG.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).

  Notation SP := (bv_unsigned sp).
  Notation LEN := (Z.of_nat (length bs)).

  Section L.
    Variables (v0 wa2 ws6 : word) (i0 : Z).
    Hypothesis Hi0 : 0 <= i0 <= LEN.
    Notation INVB mm v24 v32 := (crcz_invb ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 SP lo A bs v0 (Z_to_bv 64 135136) (Z_to_bv 64 0) v24 v32 m mm).

    Definition biter_post (ib cnt x0 x1 x2 x3 x4 : Z) : machine_state -> Prop := fun ms' => exists (mm3 : amem) (w24 w32 : word) (q_ra q_t0 q_t1 q_s0 q_s1 q_a0 q_a4 q_s7 q_s8 q_s9 q_s10 q_s11 q_t3 q_t5 q_t6 : word),
      ms' = (MS (mkR q_ra (Z_to_bv 64 (SP + -144)) gp tp q_t0 q_t1 (Z_to_bv 64 (cnt + -1)) q_s0 q_s1 q_a0 (Z_to_bv 64 (A + ib + 20)) wa2 (Z_to_bv 64 (A + ib + 20)) q_a4 (Z_to_bv 64 (dLaneM (dY0 (wdp bs ib) x0))) (Z_to_bv 64 (dLaneM (dY0 (wdp bs (ib + 16)) x4))) (Z_to_bv 64 2147450880) (Z_to_bv 64 (135136)) (Z_to_bv 64 136416) (Z_to_bv 64 (dLaneM (dY0 (wdp bs (ib + 8)) x2))) (Z_to_bv 64 (dLaneM (dY0 (wdp bs (ib + 4)) x1))) ws6 q_s7 q_s8 q_s9 q_s10 q_s11 q_t3 (Z_to_bv 64 (dLaneM (dY0 (wdp bs (ib + 12)) x3))) q_t5 q_t6) F (Z_to_bv 64 0x80dfc) fc None mm3 (seg_rom asegs))
      /\ INVB mm3 w24 w32.

    Lemma braid_iter : forall (mm : amem) (v24 v32 : word) (ib cnt x0 x1 x2 x3 x4 : Z) (p_ra p_t0 p_t1 p_s0 p_s1 p_a0 p_a4 p_s2 p_s7 p_s8 p_s9 p_s10 p_s11 p_t3 p_t5 p_t6 : word),
      INVB mm v24 v32 -> 0 <= ib -> ib + 20 <= LEN -> (A + ib) mod 4 = 0 -> 1 <= cnt < 2^64 ->
      0 <= x0 < 2^64 -> 0 <= x1 < 2^64 -> 0 <= x2 < 2^64 -> 0 <= x3 < 2^64 -> 0 <= x4 < 2^64 ->
      evtF asegs RNG (biter_post ib cnt x0 x1 x2 x3 x4)
        (MS (mkR p_ra (Z_to_bv 64 (SP + -144)) gp tp p_t0 p_t1 (Z_to_bv 64 (cnt)) p_s0 p_s1 p_a0 (Z_to_bv 64 (A + ib)) wa2 (Z_to_bv 64 (A + ib)) p_a4 (Z_to_bv 64 (x0)) (Z_to_bv 64 (x4)) (Z_to_bv 64 2147450880) p_s2 (Z_to_bv 64 136416) (Z_to_bv 64 (x2)) (Z_to_bv 64 (x1)) ws6 p_s7 p_s8 p_s9 p_s10 p_s11 p_t3 (Z_to_bv 64 (x3)) p_t5 p_t6) F (Z_to_bv 64 0x809f8) fc None mm (seg_rom asegs)).
    Proof.
      intros mm v24 v32 ib cnt x0 x1 x2 x3 x4 p_ra p_t0 p_t1 p_s0 p_s1 p_a0 p_a4 p_s2 p_s7 p_s8 p_s9 p_s10 p_s11 p_t3 p_t5 p_t6 HINV Hib Hl Hal Rc R0 R1 R2 R3 R4.
      pose proof BUF as (_ & BF & _).
      pose proof (dY0_range (wdp bs ib) x0 R0) as DY0. pose proof (dY0_range (wdp bs (ib + 4)) x1 R1) as DY1.
      pose proof (dY0_range (wdp bs (ib + 8)) x2 R2) as DY2. pose proof (dY0_range (wdp bs (ib + 12)) x3 R3) as DY3.
      pose proof (dY0_range (wdp bs (ib + 16)) x4 R4) as DY4.
      eapply evtF_cut; [eapply (bseg1 RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo A bs) with (v0 := v0) (wa2 := wa2) (ws6 := ws6); eassumption|].
      cbv beta. intros ms1 P1. unfold bseg1_post in P1. destruct_exs P1. subst ms1.
      eapply evtF_cut; [eapply (bseg2 RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo A bs) with (v0 := v0) (wa2 := wa2) (ws6 := ws6); eassumption|].
      cbv beta. intros ms2 P2. unfold bseg2_post in P2. destruct_exs P2. subst ms2.
      eapply evtF_cut; [eapply (bseg3 RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo A bs) with (v0 := v0) (wa2 := wa2) (ws6 := ws6); eassumption|].
      cbv beta. intros ms3 P3. unfold bseg3_post in P3. destruct_exs P3. subst ms3.
      eapply evtF_cut; [eapply (bseg4 RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo A bs) with (v0 := v0) (wa2 := wa2) (ws6 := ws6); eassumption|].
      cbv beta. intros ms4 P4. unfold bseg4_post in P4. destruct_exs P4. destruct P4 as [-> HINV3].
      eapply evtF_cut; [eapply (bseg5 RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo A bs) with (v0 := v0) (wa2 := wa2) (ws6 := ws6); eassumption|].
      cbv beta. intros ms5 P5. unfold bseg5_post in P5. destruct_exs P5. subst ms5.
      eapply evtF_cut; [eapply (bseg6 RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo A bs) with (v0 := v0) (wa2 := wa2) (ws6 := ws6); eassumption|].
      cbv beta. intros ms6 P6. unfold bseg6_post in P6. destruct_exs P6. subst ms6.
      apply evtF_done. unfold biter_post. eexists. eexists. eexists. do 15 eexists. split; [reflexivity| exact HINV3].
    Qed.

    Definition bloop_post (c nb : Z) : machine_state -> Prop := fun ms' => exists (mm3 : amem) (w24 w32 : word) (X0 X1 X2 X3 X4 : Z) (q_ra q_t0 q_t1 q_t2 q_s0 q_s1 q_a0 q_a1 q_a3 q_a4 q_s7 q_s8 q_s9 q_s10 q_s11 q_t3 q_t5 q_t6 : word),
      ms' = (MS (mkR q_ra (Z_to_bv 64 (SP + -144)) gp tp q_t0 q_t1 q_t2 q_s0 q_s1 q_a0 q_a1 wa2 q_a3 q_a4 (Z_to_bv 64 (X0)) (Z_to_bv 64 (X4)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (135136)) (Z_to_bv 64 136416) (Z_to_bv 64 (X2)) (Z_to_bv 64 (X1)) ws6 q_s7 q_s8 q_s9 q_s10 q_s11 q_t3 (Z_to_bv 64 (X3)) q_t5 q_t6) F (Z_to_bv 64 0x80f98) fc None mm3 (seg_rom asegs))
      /\ INVB mm3 w24 w32
      /\ (0 <= X0 < 2^64 /\ 0 <= X1 < 2^64 /\ 0 <= X2 < 2^64 /\ 0 <= X3 < 2^64 /\ 0 <= X4 < 2^64)
      /\ [X0 mod 2^32; X1 mod 2^32; X2 mod 2^32; X3 mod 2^32; X4 mod 2^32]
           = braid_state [c; 0; 0; 0; 0] (Z.to_nat nb) (skipn (Z.to_nat i0) bs).

    Lemma braid_loop : forall (k : nat) (c nb : Z) (mm : amem) (v24 v32 : word) (t ib cnt x0 x1 x2 x3 x4 : Z) (p_ra p_t0 p_t1 p_s0 p_s1 p_a0 p_a4 p_s2 p_s7 p_s8 p_s9 p_s10 p_s11 p_t3 p_t5 p_t6 : word),
      INVB mm v24 v32 -> ib = i0 + 20 * t -> cnt = nb - t -> Z.of_nat (S k) = nb - t -> 0 <= t -> i0 + 20 * nb + 20 <= LEN -> (A + i0) mod 4 = 0 ->
      0 <= x0 < 2^64 -> 0 <= x1 < 2^64 -> 0 <= x2 < 2^64 -> 0 <= x3 < 2^64 -> 0 <= x4 < 2^64 ->
      [x0 mod 2^32; x1 mod 2^32; x2 mod 2^32; x3 mod 2^32; x4 mod 2^32]
        = braid_state [c; 0; 0; 0; 0] (Z.to_nat t) (skipn (Z.to_nat i0) bs) ->
      evtF asegs RNG (bloop_post c nb)
        (MS (mkR p_ra (Z_to_bv 64 (SP + -144)) gp tp p_t0 p_t1 (Z_to_bv 64 (cnt)) p_s0 p_s1 p_a0 (Z_to_bv 64 (A + ib)) wa2 (Z_to_bv 64 (A + ib)) p_a4 (Z_to_bv 64 (x0)) (Z_to_bv 64 (x4)) (Z_to_bv 64 2147450880) p_s2 (Z_to_bv 64 136416) (Z_to_bv 64 (x2)) (Z_to_bv 64 (x1)) ws6 p_s7 p_s8 p_s9 p_s10 p_s11 p_t3 (Z_to_bv 64 (x3)) p_t5 p_t6) F (Z_to_bv 64 0x809f8) fc None mm (seg_rom asegs)).
    Proof.
      induction k as [|k IH]; intros c nb mm v24 v32 t ib cnt x0 x1 x2 x3 x4 p_ra p_t0 p_t1 p_s0 p_s1 p_a0 p_a4 p_s2 p_s7 p_s8 p_s9 p_s10 p_s11 p_t3 p_t5 p_t6 HINV Eib Ecnt Hk Ht Hl Hal R0 R1 R2 R3 R4 EL; subst ib cnt;
        pose proof BUF as (_ & BF & _); pose proof KLO as KLO'; unfold KHIGH in KLO'; pose_sp_range sp;
        pose proof (braid_lanes_step c bs i0 t x0 x1 x2 x3 x4 BF ltac:(lia) Ht ltac:(lia) EL) as EL';
        (eapply evtF_cut; [eapply (braid_iter mm v24 v32 (i0 + 20 * t) (nb - t) x0 x1 x2 x3 x4); first [eassumption | lia | (Z.div_mod_to_equations; lia)]|]);
        cbv beta; intros ms1 P1; unfold biter_post in P1; destruct_exs P1; destruct P1 as [-> HINV3];
        zstep; if_cases K; zify_cond K.
      - exfalso. lia.
      - zstep. apply evtF_done. unfold bloop_post. eexists. eexists. eexists.
        eexists (dLaneM (dY0 (wdp bs (i0 + 20 * t)) x0)), (dLaneM (dY0 (wdp bs (i0 + 20 * t + 4)) x1)), (dLaneM (dY0 (wdp bs (i0 + 20 * t + 8)) x2)),
                (dLaneM (dY0 (wdp bs (i0 + 20 * t + 12)) x3)), (dLaneM (dY0 (wdp bs (i0 + 20 * t + 16)) x4)).
        do 18 eexists. split; [reflexivity|]. split; [exact HINV3|].
        split; [repeat split; apply dLaneM_range|].
        replace nb with (t + 1) by lia. exact EL'.
      - setreg 11 (Z_to_bv 64 (A + (i0 + 20 * (t + 1)))) ltac:(f_equal; lia).
        setreg 13 (Z_to_bv 64 (A + (i0 + 20 * (t + 1)))) ltac:(f_equal; lia).
        setreg 7 (Z_to_bv 64 (nb - (t + 1))) ltac:(f_equal; lia).
        eapply (IH c nb _ _ _ (t + 1) (i0 + 20 * (t + 1)) (nb - (t + 1))); first [exact HINV3 | exact EL' | apply dLaneM_range | reflexivity | lia].
      - exfalso. lia.
    Qed.
  End L.
End P.
