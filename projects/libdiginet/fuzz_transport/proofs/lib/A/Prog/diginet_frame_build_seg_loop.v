(* diginet_frame_build_seg_loop: proof of lib/A/Prog/diginet_frame_build_iface.v fb_loop_stmt, the piece
   FB_SUM (0x827ec) .. FB_H2 (0x82840) of diginet_frame_build in fuzz_frame.asan (image A) as a footprint run
   (lib/Lib/ExecF.v evtF, stepped by lib/Lib/StepF.v step).
   The code, from the neutral listing:
     0x827ec `beqz s1` and 0x827f0 `bnez s4` go to 0x82840 when body_len = 0 or mode = 1; a1 and a2 are 0 there.
     0x827f4 .. 0x82800 a1 := 0, a2 := body, a0 := body, a3 := body_len.
     0x82804 .. 0x82810 the instrumented check of the byte at a0: the shadow byte k at (a0 >> 3) + s10 into a4; when
            k <> 0, 0x82830 a5 := a0 & 7 and `blt a5,a4` back to 0x82814 (else the error path at 0x82838).
     0x82814 .. 0x82828 a4 := the byte at a2; a3 -= 1; a0 += 1; a1 += a4; a2 += 1; `bnez a3` back to 0x82804.
     0x8282c `j 0x8283c`; 0x8283c a2 := (a1 mod 2^32) >> 8, sign-extended from 32 bits.
   Each shadow byte is 0 or above (a0 mod 8), by fb_ck_of_addressable on the addressable range of the body, so the
   error path is not reached. The loop is one invariant, fb_loop_inv, by induction on the bytes left, with the exit
   as a continuation. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportSyms DgnTransportAddr AsanKA AsanKAProof.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_frame_build_iface.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* ---------------- sums and bounds ---------------- *)

Lemma sum_bytes_nonneg : forall l : list byte, 0 <= sum_bytes l.
Proof.
  induction l as [|x l IH]; cbn [sum_bytes]; [lia|]. pose proof (bz_range x). lia.
Qed.

Lemma sum_firstn_S : forall (l : list byte) i, (i < length l)%nat ->
  sum_bytes (firstn (S i) l) = sum_bytes (firstn i l) + bz (nth i l (Z_to_bv 8 0)).
Proof.
  induction l as [|x l IH]; intros i Hi; cbn [length] in Hi; [lia|].
  destruct i as [|i]; cbn [firstn sum_bytes nth].
  - rewrite firstn_O. cbn [sum_bytes]. lia.
  - rewrite IH by lia. lia.
Qed.

Lemma sum_firstn_bounds : forall (l : list byte) i, (i <= length l)%nat ->
  0 <= sum_bytes (firstn i l) <= 255 * Z.of_nat i.
Proof.
  intros l i Hi. split; [apply sum_bytes_nonneg|].
  pose proof (sum_bytes_le (firstn i l)) as H. rewrite length_firstn, Nat.min_l in H by lia. exact H.
Qed.

(* `srliw _,_,8` of a value below 2^31: the 32-bit logical shift, sign-extended, is the quotient by 2^8. *)
Lemma srliw8_small : forall s, 0 <= s < 2 ^ 31 -> bv_swrap 32 (Z.shiftr (bv_wrap 32 s) 8) = s / 2 ^ 8.
Proof.
  intros s Hs.
  rewrite (bv_wrap_small 32%N s) by (change (bv_modulus 32%N) with 4294967296; lia).
  rewrite Z.shiftr_div_pow2 by lia.
  assert (Hq : 0 <= s / 2 ^ 8 < 2147483648)
    by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  unfold bv_swrap. change (bv_half_modulus 32%N) with 2147483648.
  rewrite (bv_wrap_small 32%N) by (change (bv_modulus 32%N) with 4294967296; lia).
  lia.
Qed.

(* The shadow byte of a + i, 0 <= i < n, lies in the shadow range of [a, a + n). *)
Lemma fb_sh_rng : forall RNG a n i, 0 <= i < n ->
  ExecF.rng RNG (shadow_addr a) (shadow_addr (a + n - 1) - shadow_addr a + 1) ->
  ExecF.rng RNG (shadow_addr (a + i)) 1.
Proof.
  intros RNG a n i Hi H. eapply rng_sub'; [exact H|]. unfold shadow_addr. Z.div_mod_to_equations. lia.
Qed.

(* ---------------- tactics ---------------- *)

(* the pcs of the statement as numerals, so that step runs on them *)
Local Ltac fb_lits :=
  repeat match goal with
  | |- context [FB_SUM] => let v := eval vm_compute in FB_SUM in change FB_SUM with v
  | |- context [FB_H2] => let v := eval vm_compute in FB_H2 in change FB_H2 with v
  end.

(* rewrite each word w of the goal by a fact bv_unsigned w = _ *)
Local Ltac fb_wsub :=
  repeat match goal with
  | H : bv_unsigned ?w = _ |- context [bv_unsigned ?w] => is_var w; rewrite H
  end.

(* a branch condition, decided from the register facts *)
Local Ltac fb_cond :=
  unfold bv_eqb, bv_ltu, bv_lts, bv_leu; zsimp; fb_wsub; zsimp; decide_tests; reflexivity.

(* take branch b of the pc (nothing to do when the pc is already a numeral) *)
Local Ltac br b :=
  lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with b; [cbv iota | symmetry; fb_cond]
  | |- _ => idtac
  end.

(* name the register value Z_to_bv 64 e (e mentions bv_unsigned x) by w, with U : bv_unsigned w = e *)
Local Ltac gen_reg x w U :=
  match goal with
  | |- context [Some (Z_to_bv 64 ?e)] =>
      lazymatch e with
      | context [bv_unsigned x] =>
          let Ew := fresh "Ew" in
          assert (U : bv_unsigned (Z_to_bv 64 e) = e)
            by (apply unsigned_lit; first [lia | Z.div_mod_to_equations; lia]);
          remember (Z_to_bv 64 e) as w eqn:Ew; clear Ew
      end
  end.

(* a register fact bv_unsigned (Z_to_bv 64 e) = _ *)
Local Ltac fb_fact :=
  rewrite ?firstn_O; cbn [sum_bytes]; cbv delta [zxb]; fb_wsub; rewrite ?unsigned_lit_wrap; Z.div_mod_to_equations;
  lia.

(* ---------------- the instrumented check of the byte at a0 ---------------- *)

(* 0x82804 -> 0x82814: a4 := (a0 >> 3) + s10, a4 := sign-extended shadow byte k at a4; `bnez a4`; when k <> 0,
   a5 := a0 & 7 and `blt a5,a4` to 0x82814. s10 holds 0x7fff8000. *)
Lemma fb_ck_F : forall (RNG : ExecF.footprint)
  (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (kk : byte) (A : Z),
  bv_unsigned a0 = A -> A < 2 ^ 63 ->
  mrd rsegs mm (wa (A / 8 + 2147450880)) = Some kk ->
  (bv_signed kk = 0 \/ A mod 8 < bv_signed kk) ->
  ExecF.rng RNG (A / 8 + 2147450880) 1 ->
  (forall y14 y15 : word,
     ExecF.evtF rsegs RNG Q
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 y14 y15 a6 a7
                s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 2147450880) s11 t3 t4 t5 t6)
           F (Z_to_bv 64 573072) fc None mm (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 2147450880) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 573056) fc None mm (seg_rom rsegs)).
Proof.
  intros until A. intros EA RA M SK RK CONT.
  pose proof (u64_range a0) as R0.
  (* 0x82804 srli a4,a0,3 *)
  step. gen_shr a0 g G. rewrite EA in G.
  (* 0x82808 add a4,a4,s10 *)
  step. gen_addi g h H.
  assert (RH : ExecF.rng RNG (bv_unsigned h) 1) by (rewrite H, G; exact RK).
  (* 0x8280c lb a4,0(a4) *)
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  (* 0x82810 bnez a4 *)
  step.
  pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb].
    apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed kk) 0) ltac:(lia)); cbn [negb].
    (* 0x82830 andi a5,a0,7; 0x82834 blt a5,a4 *)
    step. step.
    rewrite land7, EA, (lts_low (A mod 8) kk MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    apply CONT.
Qed.

(* ---------------- the loop ---------------- *)

Section FbLoop.
Variables (ra sp gp tp t0 t1 t2 a6 a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (out body : Z) (bb : list byte)
  (RNG : ExecF.footprint) (Q : machine_state -> Prop).
Hypothesis HB : 0 < body.
Hypothesis HBN : body + Z.of_nat (length bb) <= 2 ^ 63.
Hypothesis HLEN : (length bb <= 1484)%nat.
Hypothesis BA : bytes_at rsegs m body bb.
Hypothesis AD : addressable m body (Z.of_nat (length bb)).
Hypothesis RB : ExecF.rng RNG body (Z.of_nat (length bb)).
Hypothesis RS : ExecF.rng RNG (shadow_addr body)
  (shadow_addr (body + Z.of_nat (length bb) - 1) - shadow_addr body + 1).

(* the state of the loop: s0 = out, s1 = body_len, s2 = body, s4 = mode = 0, s10 = 0x7fff8000 *)
Local Abbreviation FbS pc a0 a1 a2 a3 a4 a5 :=
  (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 out) (Z_to_bv 64 (Z.of_nat (length bb))) a0 a1 a2 a3 a4 a5 a6 a7
           (Z_to_bv 64 body) s3 (Z_to_bv 64 0) s5 s6 s7 s8 s9 (Z_to_bv 64 2147450880) s11 t3 t4 t5 t6)
      F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

(* one turn at index i: 0x82804 .. 0x82828, then back to 0x82804 or through 0x8282c to 0x8283c *)
Lemma fb_body : forall i (a0 a1 a2 a3 a4 a5 : word),
  (i < length bb)%nat ->
  bv_unsigned a0 = body + Z.of_nat i -> bv_unsigned a2 = body + Z.of_nat i ->
  bv_unsigned a3 = Z.of_nat (length bb) - Z.of_nat i ->
  bv_unsigned a1 = sum_bytes (firstn i bb) ->
  (forall a0' a1' a2' a3' a4' a5' : word, (S i < length bb)%nat ->
     bv_unsigned a0' = body + Z.of_nat (S i) -> bv_unsigned a2' = body + Z.of_nat (S i) ->
     bv_unsigned a3' = Z.of_nat (length bb) - Z.of_nat (S i) ->
     bv_unsigned a1' = sum_bytes (firstn (S i) bb) ->
     ExecF.evtF rsegs RNG Q (FbS 573056 a0' a1' a2' a3' a4' a5')) ->
  (forall a0' a1' a2' a3' a4' a5' : word, S i = length bb -> bv_unsigned a1' = sum_bytes bb ->
     ExecF.evtF rsegs RNG Q (FbS 573112 a0' a1' a2' a3' a4' a5')) ->
  ExecF.evtF rsegs RNG Q (FbS 573056 a0 a1 a2 a3 a4 a5).
Proof.
  intros i a0 a1 a2 a3 a4 a5 Hi Ha0 Ha2 Ha3 Ha1 KC KE.
  pose proof (sum_firstn_bounds bb i ltac:(lia)) as SB.
  destruct (fb_ck_of_addressable m body (Z.of_nat (length bb)) (body + Z.of_nat i) 1 AD
              ltac:(lia) ltac:(lia) ltac:(lia)) as (kk & M & SK).
  pose proof (fb_sh_rng RNG body (Z.of_nat (length bb)) (Z.of_nat i) ltac:(lia) RS) as RK.
  unfold shadow_addr, ASAN_K in M, RK.
  eapply (fb_ck_F RNG) with (A := body + Z.of_nat i) (kk := kk).
  - exact Ha0.
  - lia.
  - exact M.
  - destruct SK as [C | [C _]]; [left; exact C | right; lia].
  - exact RK.
  - intros y14 y15.
    pose proof (bytes_nth m body bb i BA Hi) as MB.
    pose proof (sum_firstn_S bb i Hi) as SF.
    revert MB SF. generalize (nth i bb (Z_to_bv 8 0)) as b. intros b MB SF.
    unfold bz in SF.
    pose proof (byte_range b) as BR.
    assert (RW : ExecF.rng RNG (bv_unsigned a2) 1) by (rewrite Ha2; eapply rng_sub'; [exact RB | lia]).
    (* 0x82814 lbu a4,0(a2) *)
    pose proof (rdw0 m a2 _ _ MB Ha2) as R. step. clear R.
    assert (U4 : bv_unsigned (zxb b) = bv_unsigned b) by exact (zxb_u b).
    (* 0x82818 addi a3,a3,-1 *)
    step. gen_reg a3 n3 U3.
    (* 0x8281c addi a0,a0,1 *)
    step. gen_reg a0 n0 U0.
    (* 0x82820 add a1,a1,a4 *)
    step. gen_reg a1 n1 U1.
    (* 0x82824 addi a2,a2,1 *)
    step. gen_reg a2 n2 U2.
    (* 0x82828 bnez a3 *)
    step.
    destruct (Nat.eq_dec (S i) (length bb)) as [Ee|Ee].
    + br false.
      (* 0x8282c j 0x8283c *)
      step.
      assert (Fa : firstn (S i) bb = bb) by (apply firstn_all2; lia).
      rewrite Fa in SF.
      apply KE; [exact Ee | lia].
    + br true.
      apply KC; lia.
Qed.

(* the loop from index i to the exit at 0x8283c, with a1 = the sum of the whole body *)
Lemma fb_loop_inv : forall k i (a0 a1 a2 a3 a4 a5 : word),
  (i + S k = length bb)%nat ->
  bv_unsigned a0 = body + Z.of_nat i -> bv_unsigned a2 = body + Z.of_nat i ->
  bv_unsigned a3 = Z.of_nat (length bb) - Z.of_nat i ->
  bv_unsigned a1 = sum_bytes (firstn i bb) ->
  (forall a0' a1' a2' a3' a4' a5' : word, bv_unsigned a1' = sum_bytes bb ->
     ExecF.evtF rsegs RNG Q (FbS 573112 a0' a1' a2' a3' a4' a5')) ->
  ExecF.evtF rsegs RNG Q (FbS 573056 a0 a1 a2 a3 a4 a5).
Proof.
  induction k as [|k IH]; intros i a0 a1 a2 a3 a4 a5 Hk Ha0 Ha2 Ha3 Ha1 KX.
  - apply (fb_body i a0 a1 a2 a3 a4 a5 ltac:(lia) Ha0 Ha2 Ha3 Ha1).
    + intros a0' a1' a2' a3' a4' a5' Hlt. exfalso. lia.
    + intros a0' a1' a2' a3' a4' a5' _ H1. apply KX. exact H1.
  - apply (fb_body i a0 a1 a2 a3 a4 a5 ltac:(lia) Ha0 Ha2 Ha3 Ha1).
    + intros a0' a1' a2' a3' a4' a5' _ H0 H2 H3 H1.
      apply (IH (S i) a0' a1' a2' a3' a4' a5'); [lia | exact H0 | exact H2 | exact H3 | exact H1 | exact KX].
    + intros a0' a1' a2' a3' a4' a5' Ee _. exfalso. lia.
Qed.

End FbLoop.

(* ---------------- the piece ---------------- *)

Theorem fb_loop_F : fb_loop_stmt.
Proof.
  unfold fb_loop_stmt.
  intros RNG ra sp gp tp t0 t1 t2 a0 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m out body mode bb
    HLEN HMODE HBODY.
  fb_lits. unfold ASAN_K.
  destruct (Nat.eq_dec (length bb) 0) as [E0|E0].
  { (* body_len = 0: 0x827ec beqz s1 goes to 0x82840 *)
    apply length_zero_iff_nil in E0. subst bb.
    replace (fb_sum [] mode) with 0 by (unfold fb_sum; destruct (mode =? 0); reflexivity).
    step. br true.
    apply evtF_done. cbv beta. exists a0, a3, a4, a5. reflexivity. }
  destruct (HBODY ltac:(lia)) as (HB & HBN & BA & AD & RB & RS). clear HBODY.
  destruct HMODE as [-> | ->].
  2: { (* mode = 1: 0x827ec beqz s1 falls through, 0x827f0 bnez s4 goes to 0x82840 *)
    replace (fb_sum bb 1) with 0 by reflexivity.
    step. br false. step. br true.
    apply evtF_done. cbv beta. exists a0, a3, a4, a5. reflexivity. }
  (* mode = 0, body_len <> 0: both branches fall through; 0x827f4 li a1,0; mv a2,s2; mv a0,s2; mv a3,s1 *)
  step. br false. step. br false.
  step. step. step. step.
  eapply fb_loop_inv with (k := (length bb - 1)%nat) (i := 0%nat).
  all: try assumption.
  all: lazymatch goal with
       | |- @eq nat _ _ => lia
       | |- @eq Z (bv_unsigned _) _ => first [reflexivity | fb_fact]
       | |- forall _ : word, _ => idtac
       end.
  (* 0x8283c srliw a2,a1,0x8, then 0x82840 *)
  intros a0' a1' a2' a3' a4' a5' Ha1'.
  pose proof (sum_bytes_le bb) as SL. pose proof (sum_bytes_nonneg bb) as SN.
  step.
  match goal with
  | |- context [Some (Z_to_bv 64 ?e)] =>
      lazymatch e with
      | context [bv_unsigned a1'] =>
          replace (Z_to_bv 64 e) with (Z_to_bv 64 (fb_sum bb 0 / 2 ^ 8))
            by (f_equal; change (fb_sum bb 0) with (sum_bytes bb); rewrite Ha1';
                symmetry; apply srliw8_small; lia)
      end
  end.
  replace a1' with (Z_to_bv 64 (fb_sum bb 0))
    by (change (fb_sum bb 0) with (sum_bytes bb); rewrite <- Ha1'; apply Z_to_bv_lit_self).
  apply evtF_done. cbv beta. exists a0', a3', a4', a5'. reflexivity.
Qed.
