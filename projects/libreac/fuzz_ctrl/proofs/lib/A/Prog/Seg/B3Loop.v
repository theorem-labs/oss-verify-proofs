(* Batch B3 of fuzz_ctrl LLVMFuzzerTestOneInput (asan, image A): the two 32-byte sum loops of the round trip, for the
   segment lemmas R14 (head 0x81768) and R16 (head 0x817ec), and the low-byte test that follows each loop
   (0x81824 / 0x81910: `zext.b a0,a1 ; beqz a0`).
   Loop body (both heads, same words): before the 1-byte load at a2 = q + i the code loads the shadow byte k at
   (a0 >> 3) + s10 (s10 = ASAN_K) and goes on when k = 0 or (a0 & 7) < k (signed); else it jumps to the error path
   (0x82d44 / 0x82d48). With the 32 bytes at q addressable (AsanRT.addressable, via RcAsanRT.rt_shadow_rd /
   rt_addressable) every check passes. Then a1 += byte, a0 += 1, a2 += 1, a3 -= 1, and `bnez a3` back to the head.
   The sum is RcModel.psum (the image-U twin's form, lib/U/Prog/Seg/R13.v r13_loop): at turn i, a1 = psum xs i;
   at the exit a1 = psum xs 32. The low-byte test is taken (beqz to 0x81830 / 0x8191c) when psum xs 32 mod 256 = 0,
   which is blocksum xs = 0: for the round-trip frame bytes xs = skipn 18 (rt_g inp b), the model fact that the
   image-U twin uses as u2_rtm_sum (blocksum (skipn 18 (rt_g inp b)) = 0) is the premise of b3_run1 / b3_run2. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcAsan RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import RcAsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require SlotModel.
Import ListNotations.
Open Scope Z_scope.

(* ---- Loop 1: head 0x81768, body 0x81778, check arm 0x81794, exit 0x81790 ---- *)

Section Loop1.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (q off : Z) (xs : list byte) (W : list lib.Lib.Frame.ivl)
    (Q : machine_state -> Prop).
  Hypothesis Hq : 0 <= q.
  Hypothesis Hq32 : q + 32 <= 2^64.
  Hypothesis Hlen : length xs = 32%nat.
  Hypothesis HB : lib.Lib.Mem.bytes_at rsegs m q xs.
  Hypothesis HSR : asan_shadow_rd rsegs m off q 32 W.
  Hypothesis HAD : asan_addressable rsegs m off q 32.

  Abbreviation ST1 pc x10 x11 x12 x13 x14 x15 :=
    (lib.Lib.MState.MS (lib.Lib.Frame.mkR ra sp gp tp t0 t1 t2 s0 s1 x10 x11 x12 x13 x14 x15 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 off) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (lib.Lib.PropExec.seg_rom rsegs)).

  Hypothesis EXIT : forall x14 x15,
    lib.Lib.Exec.evt rsegs Q (ST1 0x81790 (Z_to_bv 64 (q + 32)) (Z_to_bv 64 (psum xs 32)) (Z_to_bv 64 (q + 32))
                    (Z_to_bv 64 0) x14 x15).

  Lemma b3_loop1_ind : forall n i x14 x15, (i + n = 32)%nat -> (0 < n)%nat ->
    lib.Lib.Exec.evt rsegs Q (ST1 0x81768 (Z_to_bv 64 (q + Z.of_nat i)) (Z_to_bv 64 (psum xs i))
                    (Z_to_bv 64 (q + Z.of_nat i)) (Z_to_bv 64 (32 - Z.of_nat i)) x14 x15).
  Proof using Hq Hq32 Hlen HB HSR HAD EXIT.
    induction n as [|n IH]; intros i x14 x15 Hin Hn; [lia|].
    assert (BODY : forall y14 y15,
      lib.Lib.Exec.evt rsegs Q (ST1 0x81778 (Z_to_bv 64 (q + Z.of_nat i)) (Z_to_bv 64 (psum xs i))
                      (Z_to_bv 64 (q + Z.of_nat i)) (Z_to_bv 64 (32 - Z.of_nat i)) y14 y15)).
    { intros y14 y15.
      pose proof (rd_byte rsegs m q xs i HB ltac:(lia)) as RD.
      pose proof (psum_range xs i) as PR.
      lib.Lib.Step.step. lib.Lib.Step.step. lib.Lib.Step.step. lib.Lib.Step.step. lib.Lib.Step.step.
      rewrite psum_S_zxb.
      lib.Lib.Step.step.
      rewrite (rc_eqb0_signed (32 - Z.of_nat i + -1)) by lia.
      destruct n as [|n].
      - replace (32 - Z.of_nat i + -1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
        cbn [negb].
        replace i with 31%nat in * by lia.
        replace (q + Z.of_nat 31 + 1) with (q + 32) by lia.
        replace (32 - Z.of_nat 31 + -1) with 0 by lia.
        apply EXIT.
      - replace (32 - Z.of_nat i + -1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
        cbn [negb].
        replace (q + Z.of_nat i + 1) with (q + Z.of_nat (S i)) by lia.
        replace (32 - Z.of_nat i + -1) with (32 - Z.of_nat (S i)) by lia.
        apply (IH (S i)); lia. }
    destruct (asan_shadow_read rsegs m off q 32 W (Z.of_nat i) HSR ltac:(lia)) as (k & RK & BK).
    pose proof (HAD (Z.of_nat i) k ltac:(lia) BK) as OK.
    pose proof (rc_byte_signed k) as KR.
    clear BK.
    lib.Lib.Step.step.
    rewrite (lib.Lib.MState.unsigned_lit (q + Z.of_nat i)) by lia. rewrite rc_shr3.
    lib.Lib.Step.step.
    lib.Lib.Step.step.
    clear RK.
    lib.Lib.Step.step.
    unfold lib.Lib.Mem.sxb. rewrite (rc_eqb0_signed (bv_signed k)) by lia.
    destruct (Z.eqb_spec (bv_signed k) 0) as [K0|K0]; cbn [negb].
    - apply BODY.
    - lib.Lib.Step.step.
      rewrite (lib.Lib.MState.unsigned_lit (q + Z.of_nat i)) by lia. rewrite rc_land7.
      lib.Lib.Step.step.
      rewrite (rc_lts_signed ((q + Z.of_nat i) mod 8) (bv_signed k))
        by (pose proof (Z.mod_pos_bound (q + Z.of_nat i) 8 ltac:(lia)); lia).
      replace ((q + Z.of_nat i) mod 8 <? bv_signed k) with true
        by (symmetry; apply Z.ltb_lt; destruct OK; lia).
      apply BODY.
  Qed.
End Loop1.

(* ---- Loop 2: head 0x817ec, body 0x817fc, check arm 0x81818, exit 0x81814 ---- *)

Section Loop2.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (q off : Z) (xs : list byte) (W : list lib.Lib.Frame.ivl)
    (Q : machine_state -> Prop).
  Hypothesis Hq : 0 <= q.
  Hypothesis Hq32 : q + 32 <= 2^64.
  Hypothesis Hlen : length xs = 32%nat.
  Hypothesis HB : lib.Lib.Mem.bytes_at rsegs m q xs.
  Hypothesis HSR : asan_shadow_rd rsegs m off q 32 W.
  Hypothesis HAD : asan_addressable rsegs m off q 32.

  Abbreviation ST2 pc x10 x11 x12 x13 x14 x15 :=
    (lib.Lib.MState.MS (lib.Lib.Frame.mkR ra sp gp tp t0 t1 t2 s0 s1 x10 x11 x12 x13 x14 x15 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 off) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (lib.Lib.PropExec.seg_rom rsegs)).

  Hypothesis EXIT : forall x14 x15,
    lib.Lib.Exec.evt rsegs Q (ST2 0x81814 (Z_to_bv 64 (q + 32)) (Z_to_bv 64 (psum xs 32)) (Z_to_bv 64 (q + 32))
                    (Z_to_bv 64 0) x14 x15).

  Lemma b3_loop2_ind : forall n i x14 x15, (i + n = 32)%nat -> (0 < n)%nat ->
    lib.Lib.Exec.evt rsegs Q (ST2 0x817ec (Z_to_bv 64 (q + Z.of_nat i)) (Z_to_bv 64 (psum xs i))
                    (Z_to_bv 64 (q + Z.of_nat i)) (Z_to_bv 64 (32 - Z.of_nat i)) x14 x15).
  Proof using Hq Hq32 Hlen HB HSR HAD EXIT.
    induction n as [|n IH]; intros i x14 x15 Hin Hn; [lia|].
    assert (BODY : forall y14 y15,
      lib.Lib.Exec.evt rsegs Q (ST2 0x817fc (Z_to_bv 64 (q + Z.of_nat i)) (Z_to_bv 64 (psum xs i))
                      (Z_to_bv 64 (q + Z.of_nat i)) (Z_to_bv 64 (32 - Z.of_nat i)) y14 y15)).
    { intros y14 y15.
      pose proof (rd_byte rsegs m q xs i HB ltac:(lia)) as RD.
      pose proof (psum_range xs i) as PR.
      lib.Lib.Step.step. lib.Lib.Step.step. lib.Lib.Step.step. lib.Lib.Step.step. lib.Lib.Step.step.
      rewrite psum_S_zxb.
      lib.Lib.Step.step.
      rewrite (rc_eqb0_signed (32 - Z.of_nat i + -1)) by lia.
      destruct n as [|n].
      - replace (32 - Z.of_nat i + -1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
        cbn [negb].
        replace i with 31%nat in * by lia.
        replace (q + Z.of_nat 31 + 1) with (q + 32) by lia.
        replace (32 - Z.of_nat 31 + -1) with 0 by lia.
        apply EXIT.
      - replace (32 - Z.of_nat i + -1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
        cbn [negb].
        replace (q + Z.of_nat i + 1) with (q + Z.of_nat (S i)) by lia.
        replace (32 - Z.of_nat i + -1) with (32 - Z.of_nat (S i)) by lia.
        apply (IH (S i)); lia. }
    destruct (asan_shadow_read rsegs m off q 32 W (Z.of_nat i) HSR ltac:(lia)) as (k & RK & BK).
    pose proof (HAD (Z.of_nat i) k ltac:(lia) BK) as OK.
    pose proof (rc_byte_signed k) as KR.
    clear BK.
    lib.Lib.Step.step.
    rewrite (lib.Lib.MState.unsigned_lit (q + Z.of_nat i)) by lia. rewrite rc_shr3.
    lib.Lib.Step.step.
    lib.Lib.Step.step.
    clear RK.
    lib.Lib.Step.step.
    unfold lib.Lib.Mem.sxb. rewrite (rc_eqb0_signed (bv_signed k)) by lia.
    destruct (Z.eqb_spec (bv_signed k) 0) as [K0|K0]; cbn [negb].
    - apply BODY.
    - lib.Lib.Step.step.
      rewrite (lib.Lib.MState.unsigned_lit (q + Z.of_nat i)) by lia. rewrite rc_land7.
      lib.Lib.Step.step.
      rewrite (rc_lts_signed ((q + Z.of_nat i) mod 8) (bv_signed k))
        by (pose proof (Z.mod_pos_bound (q + Z.of_nat i) 8 ltac:(lia)); lia).
      replace ((q + Z.of_nat i) mod 8 <? bv_signed k) with true
        by (symmetry; apply Z.ltb_lt; destruct OK; lia).
      apply BODY.
  Qed.
End Loop2.

(* ---- The loop lemmas in the segment form: turn i (i < 32) at the head -> the exit pc ---- *)

Lemma b3_loop1 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (q : Z) (xs : list byte) (i : nat),
    a0 = Z_to_bv 64 (q + Z.of_nat i) -> a1 = Z_to_bv 64 (psum xs i) -> a2 = Z_to_bv 64 (q + Z.of_nat i) ->
    a3 = Z_to_bv 64 (32 - Z.of_nat i) -> s10 = Z_to_bv 64 ASAN_K -> (i < 32)%nat ->
    length xs = 32%nat -> lib.Lib.Mem.bytes_at rsegs m q xs -> addressable m q 32 ->
    lib.Lib.Exec.evt rsegs
      (fun ms' => exists a4' a5' : word,
         ms' = lib.Lib.MState.MS (lib.Lib.Frame.mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (q + 32)) (Z_to_bv 64 (psum xs 32))
                       (Z_to_bv 64 (q + 32)) (Z_to_bv 64 0) a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6)
                  F (Z_to_bv 64 0x81790) fc None m (lib.Lib.PropExec.seg_rom rsegs))
      (lib.Lib.MState.MS (lib.Lib.Frame.mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81768) fc None m (lib.Lib.PropExec.seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m q xs i -> -> -> -> -> Hi Hlen HB AD.
  destruct (rt_addressable_bound m q 32 AD) as (Hq & _ & Hq32).
  pose proof (rt_shadow_rd m q 32 [] AD (fun x _ => I)) as HSR.
  pose proof (rt_addressable m q 32 AD) as HAD.
  refine (b3_loop1_ind ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m q ASAN_K
            xs [] _ Hq ltac:(lia) Hlen HB HSR HAD _ (32 - i)%nat i a4 a5 ltac:(lia) ltac:(lia)).
  intros x14 x15. apply lib.Lib.Exec.evt_done. cbv beta. exists x14, x15. reflexivity.
Qed.

Lemma b3_loop2 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (q : Z) (xs : list byte) (i : nat),
    a0 = Z_to_bv 64 (q + Z.of_nat i) -> a1 = Z_to_bv 64 (psum xs i) -> a2 = Z_to_bv 64 (q + Z.of_nat i) ->
    a3 = Z_to_bv 64 (32 - Z.of_nat i) -> s10 = Z_to_bv 64 ASAN_K -> (i < 32)%nat ->
    length xs = 32%nat -> lib.Lib.Mem.bytes_at rsegs m q xs -> addressable m q 32 ->
    lib.Lib.Exec.evt rsegs
      (fun ms' => exists a4' a5' : word,
         ms' = lib.Lib.MState.MS (lib.Lib.Frame.mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (q + 32)) (Z_to_bv 64 (psum xs 32))
                       (Z_to_bv 64 (q + 32)) (Z_to_bv 64 0) a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6)
                  F (Z_to_bv 64 0x81814) fc None m (lib.Lib.PropExec.seg_rom rsegs))
      (lib.Lib.MState.MS (lib.Lib.Frame.mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x817ec) fc None m (lib.Lib.PropExec.seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m q xs i -> -> -> -> -> Hi Hlen HB AD.
  destruct (rt_addressable_bound m q 32 AD) as (Hq & _ & Hq32).
  pose proof (rt_shadow_rd m q 32 [] AD (fun x _ => I)) as HSR.
  pose proof (rt_addressable m q 32 AD) as HAD.
  refine (b3_loop2_ind ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m q ASAN_K
            xs [] _ Hq ltac:(lia) Hlen HB HSR HAD _ (32 - i)%nat i a4 a5 ltac:(lia) ltac:(lia)).
  intros x14 x15. apply lib.Lib.Exec.evt_done. cbv beta. exists x14, x15. reflexivity.
Qed.

(* ---- The low-byte test after each loop: `j` ; zext.b a0,a1 ; beqz a0 taken when a1 mod 256 = 0 ---- *)

Lemma b3_land255 : forall S, S mod 256 = 0 -> Z.land S 255 = 0.
Proof. intros S H. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. exact H. Qed.

(* 0x81790 `j 81824` ; 0x81824 zext.b a0,a1 ; 0x81828 beqz a0,81830 (0x8182c `j 82bf4` not taken). *)
Lemma b3_tail1 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S : Z),
    a1 = Z_to_bv 64 S -> 0 <= S < 2 ^ 64 -> S mod 256 = 0 ->
    lib.Lib.Exec.evt rsegs
      (fun ms' => ms' = lib.Lib.MState.MS (lib.Lib.Frame.mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x81830) fc None m (lib.Lib.PropExec.seg_rom rsegs))
      (lib.Lib.MState.MS (lib.Lib.Frame.mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81790) fc None m (lib.Lib.PropExec.seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m S -> HS H0.
  lib.Lib.Step.step. lib.Lib.Step.step.
  rewrite (lib.Lib.MState.unsigned_lit S) by lia. rewrite (b3_land255 S H0).
  lib.Lib.Step.step. try lib.Lib.Step.if_true.
  apply lib.Lib.Exec.evt_done. cbv beta. reflexivity.
Qed.

(* 0x81814 `j 81910` ; 0x81910 zext.b a0,a1 ; 0x81914 beqz a0,8191c (0x81918 `j 82bf4` not taken). *)
Lemma b3_tail2 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S : Z),
    a1 = Z_to_bv 64 S -> 0 <= S < 2 ^ 64 -> S mod 256 = 0 ->
    lib.Lib.Exec.evt rsegs
      (fun ms' => ms' = lib.Lib.MState.MS (lib.Lib.Frame.mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x8191c) fc None m (lib.Lib.PropExec.seg_rom rsegs))
      (lib.Lib.MState.MS (lib.Lib.Frame.mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81814) fc None m (lib.Lib.PropExec.seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m S -> HS H0.
  lib.Lib.Step.step. lib.Lib.Step.step.
  rewrite (lib.Lib.MState.unsigned_lit S) by lia. rewrite (b3_land255 S H0).
  lib.Lib.Step.step. try lib.Lib.Step.if_true.
  apply lib.Lib.Exec.evt_done. cbv beta. reflexivity.
Qed.

(* ---- The bridge to the round-trip model: the 32 bytes summed are bytes 18 .. 49 of the frame Phi_r holds
   (RFb: lib.Lib.Mem.bytes_at Phi_r (rt_F inp b)), i.e. skipn 18 (rt_g inp b) with rt_g = fr50 rt_F; their block sum is 0 by
   the model fact blocksum (skipn 18 (rt_g inp b)) = 0 (image U: Tac_u2.u2_rtm_sum), so zext.b a1 = 0. ---- *)

Lemma b3_fr50_eq : forall bs, (50 <= length bs)%nat -> SlotModel.fr50 bs = firstn 50 bs.
Proof.
  intros bs H. unfold SlotModel.fr50. rewrite firstn_app. replace (50 - length bs)%nat with 0%nat by lia.
  rewrite firstn_O, app_nil_r. reflexivity.
Qed.

Lemma b3_blk_at : forall m phi Fb, lib.Lib.Mem.bytes_at rsegs m phi Fb -> (50 <= length Fb)%nat ->
  lib.Lib.Mem.bytes_at rsegs m (phi + 18) (skipn 18 (SlotModel.fr50 Fb)) /\ length (skipn 18 (SlotModel.fr50 Fb)) = 32%nat.
Proof.
  intros m phi Fb H L. rewrite (b3_fr50_eq Fb L).
  split; [| rewrite length_skipn, length_firstn; lia].
  rewrite <- (firstn_skipn 50 Fb) in H.
  apply (proj1 (lib.Lib.Mem.bytes_at_app rsegs _ _ _ _)) in H. destruct H as [H _].
  rewrite <- (firstn_skipn 18 (firstn 50 Fb)) in H.
  apply (proj1 (lib.Lib.Mem.bytes_at_app rsegs _ _ _ _)) in H. destruct H as [_ H].
  replace (phi + 18) with (phi + Z.of_nat (length (firstn 18 (firstn 50 Fb)))) by (rewrite !length_firstn; lia).
  exact H.
Qed.

(* By rewriting over a variable list only: a conversion between blocksum and psum .. mod 256 at the concrete
   frame bytes would make the kernel compute the model (rt_F) through Z.modulo. *)
Lemma b3_blocksum : forall bs, psum bs 32 mod 256 = blocksum bs.
Proof. intros bs. unfold blocksum. reflexivity. Qed.

Lemma b3_sum_low : forall xs, blocksum xs = 0 -> psum xs 32 mod 256 = 0.
Proof. intros xs H. rewrite b3_blocksum. exact H. Qed.

Lemma b3_rt_g : forall inp b, SlotModel.rt_g inp b = SlotModel.fr50 (SlotModel.rt_F inp b).
Proof. intros inp b. reflexivity. Qed.

(* R14's run from the loop head (turn 0: a0 = a2 = Phi_r + 18, a1 = 0, a3 = 32) to 0x81830 (a0 = 0). *)
Lemma b3_run1 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (phi : Z) (inp : list byte) (b : Z),
    a0 = Z_to_bv 64 (phi + 18) -> a1 = Z_to_bv 64 0 -> a2 = Z_to_bv 64 (phi + 18) -> a3 = Z_to_bv 64 32 ->
    s10 = Z_to_bv 64 ASAN_K ->
    lib.Lib.Mem.bytes_at rsegs m phi (SlotModel.rt_F inp b) -> (50 <= length (SlotModel.rt_F inp b))%nat ->
    addressable m (phi + 18) 32 ->
    blocksum (skipn 18 (SlotModel.rt_g inp b)) = 0 ->
    lib.Lib.Exec.evt rsegs
      (fun ms' => exists a4' a5' : word,
         ms' = lib.Lib.MState.MS (lib.Lib.Frame.mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0)
                       (Z_to_bv 64 (psum (skipn 18 (SlotModel.rt_g inp b)) 32))
                       (Z_to_bv 64 (phi + 50)) (Z_to_bv 64 0) a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6)
                  F (Z_to_bv 64 0x81830) fc None m (lib.Lib.PropExec.seg_rom rsegs))
      (lib.Lib.MState.MS (lib.Lib.Frame.mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81768) fc None m (lib.Lib.PropExec.seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m phi inp b E0 E1 E2 E3 E10 HF HL AD HS.
  destruct (b3_blk_at m phi _ HF HL) as (HB & Hlen).
  rewrite <- (b3_rt_g inp b) in HB, Hlen.
  pose proof (psum_range (skipn 18 (SlotModel.rt_g inp b)) 32) as PR. change (Z.of_nat 32) with 32 in PR.
  eapply lib.Lib.Exec.evt_cut.
  { apply (b3_loop1 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc m (phi + 18) (skipn 18 (SlotModel.rt_g inp b)) 0%nat);
      [ rewrite E0; f_equal; lia | exact E1 | rewrite E2; f_equal; lia | exact E3 | exact E10 | lia
      | exact Hlen | exact HB | exact AD ]. }
  intros ms' (a4' & a5' & ->).
  replace (phi + 18 + 32) with (phi + 50) by lia.
  eapply lib.Lib.Exec.evt_cut.
  { apply (b3_tail1 ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (phi + 50))
             (Z_to_bv 64 (psum (skipn 18 (SlotModel.rt_g inp b)) 32)) (Z_to_bv 64 (phi + 50)) (Z_to_bv 64 0)
             a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
             (psum (skipn 18 (SlotModel.rt_g inp b)) 32) eq_refl ltac:(lia) (b3_sum_low _ HS)). }
  intros ms' ->. apply lib.Lib.Exec.evt_done. cbv beta. exists a4', a5'. reflexivity.
Qed.

(* R16's run from the loop head (turn 0) to 0x8191c (a0 = 0). *)
Lemma b3_run2 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (phi : Z) (inp : list byte) (b : Z),
    a0 = Z_to_bv 64 (phi + 18) -> a1 = Z_to_bv 64 0 -> a2 = Z_to_bv 64 (phi + 18) -> a3 = Z_to_bv 64 32 ->
    s10 = Z_to_bv 64 ASAN_K ->
    lib.Lib.Mem.bytes_at rsegs m phi (SlotModel.rt_F inp b) -> (50 <= length (SlotModel.rt_F inp b))%nat ->
    addressable m (phi + 18) 32 ->
    blocksum (skipn 18 (SlotModel.rt_g inp b)) = 0 ->
    lib.Lib.Exec.evt rsegs
      (fun ms' => exists a4' a5' : word,
         ms' = lib.Lib.MState.MS (lib.Lib.Frame.mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0)
                       (Z_to_bv 64 (psum (skipn 18 (SlotModel.rt_g inp b)) 32))
                       (Z_to_bv 64 (phi + 50)) (Z_to_bv 64 0) a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6)
                  F (Z_to_bv 64 0x8191c) fc None m (lib.Lib.PropExec.seg_rom rsegs))
      (lib.Lib.MState.MS (lib.Lib.Frame.mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x817ec) fc None m (lib.Lib.PropExec.seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m phi inp b E0 E1 E2 E3 E10 HF HL AD HS.
  destruct (b3_blk_at m phi _ HF HL) as (HB & Hlen).
  rewrite <- (b3_rt_g inp b) in HB, Hlen.
  pose proof (psum_range (skipn 18 (SlotModel.rt_g inp b)) 32) as PR. change (Z.of_nat 32) with 32 in PR.
  eapply lib.Lib.Exec.evt_cut.
  { apply (b3_loop2 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc m (phi + 18) (skipn 18 (SlotModel.rt_g inp b)) 0%nat);
      [ rewrite E0; f_equal; lia | exact E1 | rewrite E2; f_equal; lia | exact E3 | exact E10 | lia
      | exact Hlen | exact HB | exact AD ]. }
  intros ms' (a4' & a5' & ->).
  replace (phi + 18 + 32) with (phi + 50) by lia.
  eapply lib.Lib.Exec.evt_cut.
  { apply (b3_tail2 ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (phi + 50))
             (Z_to_bv 64 (psum (skipn 18 (SlotModel.rt_g inp b)) 32)) (Z_to_bv 64 (phi + 50)) (Z_to_bv 64 0)
             a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
             (psum (skipn 18 (SlotModel.rt_g inp b)) 32) eq_refl ltac:(lia) (b3_sum_low _ HS)). }
  intros ms' ->. apply lib.Lib.Exec.evt_done. cbv beta. exists a4', a5'. reflexivity.
Qed.
