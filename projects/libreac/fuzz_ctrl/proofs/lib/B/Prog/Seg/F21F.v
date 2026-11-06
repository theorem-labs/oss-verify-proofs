(* rule 24: no function proved. *)
(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
   source run: lib/B/Prog/Seg/F21.v lu_evt (:66) and seg_F21's own inline stretch 0x82728 -> 0x827f8 / 0x8283c
     (:662-766) at a working branch 3803efccea0 (blob 20a1f323863a72a3bec516c73f1ef2b8e6eb3995);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
         lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
   compare: lu_evt is the UL bridge that carries the head-amp callee contract into seg_F21's UL run; an _F
     stretch never runs a callee, so the bridge has no footprint twin.  seg_F21_F re-runs F21.v:664-766 and
     STOPS at the call site 0x8283c on the arm that reaches it (F21.v:712-714 / 738-739); the call itself is
     F22F.seg_F22t_pre_F / seg_F22t_post_F, which start at that same pc.  The other arm ends at the loop head
     0x827f8, which is F22F.seg_F22_F's entry. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require F21.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.
Open Scope Z_scope.

(* An access at exactly a region we carry: close it from that region without arithmetic on the shadow address
   (Z.shiftr is opaque to lia; pilot note (b)). *)
Local Ltac acc_hint ::=
  lazymatch goal with
  | |- acc_in ?RNG (Z_to_bv 64 ?E, ?n) =>
      match goal with
      | H : rng RNG E _ |- _ =>
          eapply rng_acc_litZ; [exact H | reflexivity | lia | split; lia]
      end
  end.

(* The one-byte read facts in the lib.Lib form StepF consumes, and the two value normalisations the run needs
   (F21.rd1 / F21.ush / F21.zx speak the UL engine's). *)
Lemma f21_rd1_lib : forall m a b, bytes_at rsegs m a [b] -> ov_read_bytes rsegs m (wa a) 1 = Some [b].
Proof.
  intros m a b H.
  pose proof (bytes_at_ov_read rsegs m a [b] 0 1 H ltac:(cbn; lia)) as HH.
  change (Z.of_nat 0) with 0%Z in HH. rewrite Z.add_0_r in HH. cbn [firstn skipn] in HH. exact HH.
Qed.
Lemma f21_zxb8_lib : forall v, 0 <= v < 256 -> zxb (Z_to_bv 8 v) = Z_to_bv 64 v.
Proof.
  intros v Hv. unfold zxb. f_equal. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  unfold bv_modulus. cbn. lia.
Qed.
Ltac f21_ush := match goal with
  | |- context [Z.shiftr (bv_unsigned (Z_to_bv 64 ?X)) 3] => rewrite (unsigned_lit X) by lia
  end.
Ltac f21_zx := match goal with
  | |- context [zxb (Z_to_bv 8 ?v)] => rewrite (f21_zxb8_lib v) by lia
  end.

(* The footprint twin of seg_F21's inline stretch (F21.v:662-766): from the F21 entry cut at 0x82728 to either
   the sum-loop head 0x827f8 (the record bytes Phi[18] / Phi[19] are 4 / 3) or the head-amp call site 0x8283c
   (they are not).  It reads the two record bytes and their shadow bytes; it writes no memory and makes no call.
   The two exits are given as premises on Q, as F22.f22_loop gives its exit. *)
Lemma seg_F21_F : forall (RNG : footprint) (Q : _ -> Prop)
  (ra sp gp tp t0 t1 t2 s0 s1 a0v a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (phi k sv y0 y1 : Z),
  a0v = Z_to_bv 64 (sv + -1) ->
  0 < phi -> phi + 50 <= 2 ^ 64 -> 0 <= k < 2 ^ 64 -> 0 <= sv <= 1 ->
  0 <= y0 < 256 -> 0 <= y1 < 256 -> (k = 6 -> y0 = 4 /\ y1 = 3) ->
  bytes_at rsegs m (phi + 18) [Z_to_bv 8 y0] -> bytes_at rsegs m (phi + 19) [Z_to_bv 8 y1] ->
  b8 m (Z.shiftr (phi + 18) 3 + ASAN_K) 0 -> b8 m (Z.shiftr (phi + 19) 3 + ASAN_K) 0 ->
  rng RNG (phi + 18) 1 -> rng RNG (phi + 19) 1 ->
  rng RNG (Z.shiftr (phi + 18) 3 + ASAN_K) 1 -> rng RNG (Z.shiftr (phi + 19) 3 + ASAN_K) 1 ->
  (y0 = 4 -> y1 = 3 ->
     Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (phi + 34))
            (Z_to_bv 64 (2 ^ 64 - (phi + 35))) a4 a5 a6 (Z_to_bv 64 6) (Z_to_bv 64 phi) s3 s4 s5 s6
            (Z_to_bv 64 (-1)) (Z_to_bv 64 k) (Z_to_bv 64 sv) (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
         F (Z_to_bv 64 0x827f8) fc None m (seg_rom rsegs))) ->
  (forall a0' a1' : word, (y0 <> 4 \/ y1 <> 3) ->
     Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3 a4 a5 a6 a7 (Z_to_bv 64 phi) s3 s4 s5 s6
            (Z_to_bv 64 (-1)) (Z_to_bv 64 k) (Z_to_bv 64 sv) (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
         F (Z_to_bv 64 0x8283c) fc None m (seg_rom rsegs))) ->
  evtF rsegs RNG Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0v a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 phi) s3 s4 s5 s6 s7
         (Z_to_bv 64 k) (Z_to_bv 64 sv) (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x82728) fc None m (seg_rom rsegs)).
Proof.
  intros RNG Q ra sp gp tp t0 t1 t2 s0 s1 a0v a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s11 t3 t4 t5 t6
    F fc m phi k sv y0 y1 -> Hphi0 Hphi50 Hk Hsv Hy0 Hy1 Hk6 HB18 HB19 HS18 HS19 R18 R19 RS18 RS19 HQ1 HQ2.
  pose proof (f21_rd1_lib m _ _ HB18) as RY0.
  pose proof (f21_rd1_lib m _ _ HB19) as RY1.
  pose proof (f21_rd1_lib m _ _ HS18) as RSH18.
  pose proof (f21_rd1_lib m _ _ HS19) as RSH19.
  assert (Uphi : bv_unsigned (Z_to_bv 64 phi) = phi) by (apply unsigned_lit; lia).
  assert (Uk : bv_unsigned (Z_to_bv 64 k) = k) by (apply unsigned_lit; lia).
  (* 0x82728 addi a1,s9,-1 ; 0x8272c bne a0,a1,82fa4 (equal: not taken) *)
  step. step. if_false.
  (* 0x82730 li a0,6 ; 0x82734 bne s8,a0,82788 *)
  step. step.
  destruct (Z.eq_dec k 6) as [Ek6|Nk6].
  - (* k = 6: the record bytes are 4 / 3 *)
    destruct (Hk6 Ek6) as [E4 E3]. rewrite E4 in RY0. rewrite E3 in RY1.
    (* the `bne s8,a0,82788` is not taken: k = 6.  Rewrite only inside the condition, so that the s8 slot keeps
       its carried form Z_to_bv 64 k. *)
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
        replace c with false by (symmetry; rewrite Ek6, bv_eqb_refl; reflexivity)
    end; cbv iota.
    (* 0x82738 li a0,-19 ; bltu a0,s2 : not taken (Phi + 18 < 2 ^ 64) *)
    step. step. if_false.
    (* addi a0,s2,18 ; srli ; add ; lb = the shadow byte of Phi + 18 (0) ; bnez (not taken) *)
    step. step. f21_ush. step. step. step. if_false.
    (* lbu a0 = 4 ; li a1,4 ; bne a0,a1,82fa4 (not taken) *)
    step. f21_zx. step. step. if_false.
    (* 0x82760 li a0,-20 ; bltu a0,s2 : not taken (Phi + 19 < 2 ^ 64) *)
    step. step. if_false.
    step. step. f21_ush. step. step. step. if_false.
    (* lbu a0 = 3 ; li a1,3 ; bne a0,a1,82fa4 (not taken) *)
    step. f21_zx. step. step. if_false.
    (* 0x82788 li a0,-19 ; bltu a0,s2 : not taken *)
    step. step. if_false.
    step. step. f21_ush. step. step. step. if_false.
    (* lbu a0 = 4 ; li s7,-1 ; li a1,4 ; bne a0,a1,8283c (not taken) *)
    step. f21_zx. step. step. step. if_false.
    (* 0x827b4 li a0,-20 ; bltu a0,s2 : not taken *)
    step. step. if_false.
    step. step. f21_ush. step. step. step. if_false.
    (* lbu a0 = 3 ; li a1,3 ; bne a0,a1,8283c (not taken) *)
    step. f21_zx. step. step. if_false.
    (* 0x827dc li a0,-35 ; bltu a0,s2 : not taken (Phi + 34 < 2 ^ 64) *)
    step. step. if_false.
    (* li a0,0 ; li a1,0 ; addi a2,s2,34 ; not a3,a2 ; li a7,6 : the loop head 0x827f8 *)
    step. step. step. step. step.
    apply evtF_done.
    replace (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 (phi + 34))) 18446744073709551615))
      with (Z_to_bv 64 (2 ^ 64 - (phi + 35)))
      by (rewrite F21.f21_not by lia; f_equal; lia).
    exact (HQ1 E4 E3).
  - (* k <> 6 *)
    if_true.
    (* 0x82788 li a0,-19 ; bltu a0,s2 : not taken (Phi + 18 < 2 ^ 64) *)
    step. step. if_false.
    step. step. f21_ush. step. step. step. if_false.
    (* lbu a0 = y0 ; li s7,-1 ; li a1,4 ; bne a0,a1,8283c *)
    step. f21_zx. step. step. step.
    destruct (Z.eq_dec y0 4) as [E4|N4].
    2: { lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
             replace c with true by
               (symmetry; apply Bool.negb_true_iff, bv_eqb_neq; intro HC; apply N4;
                apply (f_equal (bv_unsigned (n:=64))) in HC; rewrite !unsigned_lit in HC by lia; exact HC)
         end; cbv iota.
         apply evtF_done. apply HQ2. left; exact N4. }
    rewrite E4. if_false.
    (* 0x827b4 li a0,-20 ; bltu a0,s2 : not taken (Phi + 19 < 2 ^ 64) *)
    step. step. if_false.
    step. step. f21_ush. step. step. step. if_false.
    (* lbu a0 = y1 ; li a1,3 ; bne a0,a1,8283c *)
    step. f21_zx. step. step.
    destruct (Z.eq_dec y1 3) as [E3|N3].
    2: { lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
             replace c with true by
               (symmetry; apply Bool.negb_true_iff, bv_eqb_neq; intro HC; apply N3;
                apply (f_equal (bv_unsigned (n:=64))) in HC; rewrite !unsigned_lit in HC by lia; exact HC)
         end; cbv iota.
         apply evtF_done. apply HQ2. right; exact N3. }
    rewrite E3. if_false.
    (* 0x827dc li a0,-35 ; bltu a0,s2 : not taken (Phi + 34 < 2 ^ 64) *)
    step. step. if_false.
    (* li a0,0 ; li a1,0 ; addi a2,s2,34 ; not a3,a2 ; li a7,6 : the loop head 0x827f8 *)
    step. step. step. step. step.
    apply evtF_done.
    replace (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 (phi + 34))) 18446744073709551615))
      with (Z_to_bv 64 (2 ^ 64 - (phi + 35)))
      by (rewrite F21.f21_not by lia; f_equal; lia).
    exact (HQ1 E4 E3).
Qed.
