(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: new for LPS 727298f3: musl's plain strcmp, walked (rstrcmp_holds), for the nine calls __vdsosym makes while resolving __vdso_clock_gettime, ported from projects/omx-clap-core/fuzz_state/proofs/lib/Prog/strcmp_c.v and Prog/strcmp.v. *)
(* PORTED, not written: the statement and the proof come from
   omx-clap-core/fuzz_state's Prog/strcmp_c.v and Prog/strcmp.v (theorem
   strcmp_holds, green whole-unit in an earlier proof round, 1360/1360).  The
   same statement exists over six images --
   libdiginet/fuzz_codec 0x1dcc4, omx fuzz_state 0x20c20 and fuzz_preset
   0x21f64, libreac fuzz_identity 0x1c9b8, fuzz_pcap 0x1c318 and fuzz_ctrl
   0x1d8d4 -- so it is a family, and this is its seventh instance.

   WHY THIS DONOR AND NOT THE SIGNED ONE.  coturn's RefStrcmp.v concludes the
   signed result and its body is byte-identical to ours (56 bytes, measured),
   but it is an [msteps] statement and ours is [evt], and more to the point
   __vdsosym NEVER READS THE SIGN.  Measured over the function's own
   disassembly: the only consumers of strcmp's a0 are `beqz a0` at 0x27dcb0
   and `bnez a0` at 0x27dd18 -- zero sign-sensitive consumers, against
   firing controls of 40 branch instructions and 2 sign/compare ops
   elsewhere in the same function.  So `r = 0 <-> sx = sy` is exactly and
   only what the caller can observe, and the signed statement would be
   strictly more than is needed at a layer-port cost.

   WHY THE PORT IS A RE-ADDRESSING.  Our strcmp is 14 instructions at
   0x27a050 with the loop head at 0x27a068 and the exit at 0x27a080 -- the
   same +0x00 / +0x18 / +0x30 layout every member of the family has.  The
   helper lemmas below are address-independent and are transcribed; only
   the three literals and the segment list change. *)

From Stdlib Require Import ZArith Arith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import PropExec MState Mem Exec Frame Step Tac Bytes Arr.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import RSegs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* The three addresses, and nothing else in this file is image-specific. *)
Definition RSTRCMP : Z := 0x27a050.        (* entry            *)
Definition RSTRCMP_LOOP : Z := 0x27a068.   (* loop head, +0x18 *)
Definition RSTRCMP_EXIT : Z := 0x27a080.   (* `sub a0,a2,a3`, +0x30 *)

(* FOR WHOEVER WRITES THE Ub TWIN: THESE THREE ADDRESSES ARE THE PLAIN
   IMAGE'S AND DO NOT CARRY OVER.  A TWIN IN TEXT IS NOT A TWIN IN
   ADDRESSES -- plain and ubsan are different binaries.  Measured by
   searching the ubsan image for this body's exact 56 bytes:

     plain  0x27a050
     ubsan  0x2c0c84        delta +0x46c34, EXACTLY ONE occurrence
     control: a fabricated 56-byte needle is not found (-1)

   So UStrcmp's constants are 0x2c0c84 / 0x2c0c9c / 0x2c0cb4, keeping the
   +0x18 and +0x30 offsets, which hold because the body is byte-identical.
   Copying 0x27a050 into the Ub twin would fetch another function's
   instructions and the walk would fail somewhere unrelated to its cause.

   The asan image is a THIRD case and not a re-addressing at all: its
   __vdsosym reaches strcmp indirectly (auipc ra,0xffc78 + jalr) through a
   thunk slot at 0x1ad7d8 into a 2032-byte-frame ASan interceptor at
   0x1addfc, whose bytes are NOT this body.  The As/Both-As twins need an
   interceptor donor, not this one. *)

Definition rstrcmp_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (sx sy : list byte),
    bytes_at rsegs m (bv_unsigned a0) (sx ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) sx ->
    bytes_at rsegs m (bv_unsigned a1) (sy ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) sy ->
    evt rsegs
      (fun ms' => exists r x11 x12 x13 : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 r x11 x12 x13 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m (seg_rom rsegs)
         /\ (r = Z_to_bv 64 0 <-> sx = sy))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RSTRCMP) fc None m (seg_rom rsegs)).

(* ---- address-independent helpers, transcribed from the donor ---- *)

Lemma u_zxb : forall b : byte, bv_unsigned (zxb b) = bv_unsigned b.
Proof.
  intros b. unfold zxb. apply unsigned_lit.
  pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R. lia.
Qed.

Lemma u_byte : forall b : byte, bv_unsigned (Z_to_bv 64 (bv_unsigned b)) = bv_unsigned b.
Proof. exact u_zxb. Qed.

Lemma sub_bytes_zero : forall b1 b2 : byte,
  Z_to_bv 64 (bv_unsigned (zxb b1) - bv_unsigned (zxb b2)) = Z_to_bv 64 0 <-> bv_unsigned b1 = bv_unsigned b2.
Proof.
  intros b1 b2. rewrite !u_zxb.
  pose proof (bv_unsigned_in_range 8 b1) as R1. pose proof (bv_unsigned_in_range 8 b2) as R2.
  unfold bv_modulus in R1, R2. change (2 ^ Z.of_N 8) with 256 in R1, R2.
  split; intros H.
  - apply (f_equal bv_unsigned) in H. rewrite !unsigned_lit_wrap in H.
    rewrite Z.mod_0_l in H by lia. Z.div_mod_to_equations. nia.
  - rewrite H, Z.sub_diag. reflexivity.
Qed.

Lemma list_ext_nth : forall {A} (l l' : list A), (forall n, nth_error l n = nth_error l' n) -> l = l'.
Proof.
  induction l as [|x l IH]; intros [|y l'] H.
  - reflexivity.
  - specialize (H 0%nat). discriminate.
  - specialize (H 0%nat). discriminate.
  - pose proof (H 0%nat) as H0. cbn in H0. inversion H0; subst. f_equal. apply IH. intros n. exact (H (S n)).
Qed.

Lemma nth_full : forall (s : list byte) i, (i <= length s)%nat -> exists b, nth_error (s ++ [Z_to_bv 8 0]) i = Some b.
Proof.
  intros s i H. destruct (nth_error (s ++ [Z_to_bv 8 0]) i) as [b|] eqn:E; [eauto|].
  apply nth_error_None in E. rewrite length_app in E. cbn in E. lia.
Qed.

Lemma nth_full_zero : forall (s : list byte) i b, ~ In (Z_to_bv 8 0) s ->
  nth_error (s ++ [Z_to_bv 8 0]) i = Some b -> (i <= length s)%nat ->
  (bv_unsigned b = 0 <-> i = length s).
Proof.
  intros s i b NZ E Hi. destruct (Nat.eq_dec i (length s)) as [->|NE].
  - rewrite nth_error_app2, Nat.sub_diag in E by lia. cbn in E. inversion E; subst. split; reflexivity.
  - rewrite nth_error_app1 in E by lia. split; [|intros; lia]. intros Hb. exfalso. apply NZ.
    replace (Z_to_bv 8 0) with b; [eapply nth_error_In; eauto|]. apply bv_eq. rewrite Hb. reflexivity.
Qed.

(* ---- the walk ---- *)

Section Strcmp.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (sx sy : list byte) (X Y : Z).
  Hypothesis HX : bytes_at rsegs m X (sx ++ [Z_to_bv 8 0]).
  Hypothesis NX : ~ In (Z_to_bv 8 0) sx.
  Hypothesis HY : bytes_at rsegs m Y (sy ++ [Z_to_bv 8 0]).
  Hypothesis NY : ~ In (Z_to_bv 8 0) sy.

  Notation fx := (sx ++ [Z_to_bv 8 0]).
  Notation fy := (sy ++ [Z_to_bv 8 0]).
  Notation POST := (fun ms' : machine_state => exists r x11 x12 x13 : word,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 r x11 x12 x13 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom rsegs)
    /\ (r = Z_to_bv 64 0 <-> sx = sy)).
  Notation ST pc x10 x11 x12 x13 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 x11 x12 x13 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

  Lemma prefix_result : forall k b1 b2,
    (k <= length sx)%nat -> (k <= length sy)%nat ->
    (forall j, (j < k)%nat -> nth_error fx j = nth_error fy j) ->
    nth_error fx k = Some b1 -> nth_error fy k = Some b2 ->
    (bv_unsigned b1 = 0 \/ bv_unsigned b1 <> bv_unsigned b2) ->
    (bv_unsigned b1 = bv_unsigned b2 <-> sx = sy).
  Proof.
    intros k b1 b2 Kx Ky P E1 E2 D. split.
    - intros Heq. assert (Z1 : bv_unsigned b1 = 0) by (destruct D; [assumption|contradiction]).
      assert (Z2 : bv_unsigned b2 = 0) by lia.
      apply (nth_full_zero sx k b1 NX E1 Kx) in Z1. apply (nth_full_zero sy k b2 NY E2 Ky) in Z2.
      apply list_ext_nth. intros n. destruct (Nat.lt_ge_cases n k) as [Hn|Hn].
      + specialize (P n Hn). rewrite !nth_error_app1 in P by lia. exact P.
      + rewrite !(proj2 (nth_error_None _ _)) by lia. reflexivity.
    - intros ->. rewrite E1 in E2. inversion E2. reflexivity.
  Qed.

  Lemma exit_ok : forall k b1 b2 x10 x11,
    (k <= length sx)%nat -> (k <= length sy)%nat ->
    (forall j, (j < k)%nat -> nth_error fx j = nth_error fy j) ->
    nth_error fx k = Some b1 -> nth_error fy k = Some b2 ->
    (bv_unsigned b1 = 0 \/ bv_unsigned b1 <> bv_unsigned b2) ->
    evt rsegs POST (ST 0x27a080 x10 x11 (zxb b1) (zxb b2)).
  Proof.
    intros k b1 b2 x10 x11 Kx Ky P E1 E2 D.
    step. step.
    apply evt_done. eexists _, _, _, _. split; [reflexivity|].
    rewrite <- (prefix_result k b1 b2 Kx Ky P E1 E2 D).
    apply sub_bytes_zero.
  Qed.

  Lemma loop : forall n i x12 x13,
    (length sx - i = n)%nat -> (1 <= i)%nat -> (i <= length sx)%nat -> (i <= length sy)%nat ->
    (forall j, (j < i)%nat -> nth_error fx j = nth_error fy j) ->
    evt rsegs POST (ST 0x27a068 (Z_to_bv 64 (X + Z.of_nat i)) (Z_to_bv 64 (Y + Z.of_nat i)) x12 x13).
  Proof.
    induction n as [n IH] using lt_wf_ind. intros i x12 x13 Hn H1 Kx Ky P.
    destruct (nth_full sx i Kx) as [b1 E1]. destruct (nth_full sy i Ky) as [b2 E2].
    pose proof (u8ro_read rsegs m X fx (Z.of_nat i) b1 _ HX ltac:(rewrite Nat2Z.id; exact E1) ltac:(lia) eq_refl) as RD1.
    pose proof (u8ro_read rsegs m Y fy (Z.of_nat i) b2 _ HY ltac:(rewrite Nat2Z.id; exact E2) ltac:(lia) eq_refl) as RD2.
    pose proof (nth_full_zero sx i b1 NX E1 Kx) as Z1. pose proof (nth_full_zero sy i b2 NY E2 Ky) as Z2.
    step. step. step. if_cases K; zify_cond K; rewrite ?u_zxb, ?u_byte in K; cbv iota.
    - eapply exit_ok with (k := i); [exact Kx | exact Ky | exact P | exact E1 | exact E2 | left; exact K].
    - step. step. step. if_cases K2; zify_cond K2; rewrite ?u_zxb, ?u_byte in K2; cbv iota.
      + assert (Eb : b1 = b2) by (apply bv_eq; exact K2). subst b2.
        assert (Ix : (i < length sx)%nat) by (destruct (Nat.eq_dec i (length sx)); [apply Z1 in e; lia | lia]).
        assert (Iy : (i < length sy)%nat) by (destruct (Nat.eq_dec i (length sy)); [apply Z2 in e; lia | lia]).
        replace (X + Z.of_nat i + 1) with (X + Z.of_nat (S i)) by lia.
        replace (Y + Z.of_nat i + 1) with (Y + Z.of_nat (S i)) by lia.
        apply (IH (length sx - S i)%nat); try lia.
        intros j Hj. destruct (Nat.eq_dec j i) as [->|NE]; [rewrite E1, E2; reflexivity|]. apply P. lia.
      + eapply exit_ok with (k := i); [exact Kx | exact Ky | exact P | exact E1 | exact E2 | right; exact K2].
  Qed.

  Lemma entry : forall a0 a1 a2 a3, bv_unsigned a0 = X -> bv_unsigned a1 = Y ->
    evt rsegs POST (ST 0x27a050 a0 a1 a2 a3).
  Proof.
    intros a0 a1 a2 a3 HA0 HA1.
    destruct (nth_full sx 0 ltac:(lia)) as [b1 E1]. destruct (nth_full sy 0 ltac:(lia)) as [b2 E2].
    assert (RD1 : ov_read_bytes rsegs m a0 1 = Some [b1]).
    { apply (u8ro_read rsegs m X fx 0 b1 a0 HX E1); [lia|].
      unfold wa. rewrite Z.add_0_r, <- HA0. symmetry. apply Z_to_bv_lit_self. }
    assert (RD2 : ov_read_bytes rsegs m a1 1 = Some [b2]).
    { apply (u8ro_read rsegs m Y fy 0 b2 a1 HY E2); [lia|].
      unfold wa. rewrite Z.add_0_r, <- HA1. symmetry. apply Z_to_bv_lit_self. }
    pose proof (nth_full_zero sx 0 b1 NX E1 ltac:(lia)) as Z1. pose proof (nth_full_zero sy 0 b2 NY E2 ltac:(lia)) as Z2.
    step. step. step. if_cases K; zify_cond K; rewrite ?u_zxb, ?u_byte in K; cbv iota.
    - eapply exit_ok with (k := 0%nat); [lia | lia | intros j Hj; lia | exact E1 | exact E2 | left; exact K].
    - step. if_cases K2; zify_cond K2; rewrite ?u_zxb, ?u_byte in K2; cbv iota.
      + eapply exit_ok with (k := 0%nat); [lia | lia | intros j Hj; lia | exact E1 | exact E2 | right; exact K2].
      + assert (Eb : b1 = b2) by (apply bv_eq; lia). subst b2.
        assert (Ix : (0 < length sx)%nat) by (destruct (Nat.eq_dec 0 (length sx)); [apply Z1 in e; lia | lia]).
        assert (Iy : (0 < length sy)%nat) by (destruct (Nat.eq_dec 0 (length sy)); [apply Z2 in e; lia | lia]).
        step. step.
        rewrite HA0, HA1.
        apply (loop (length sx - 1)%nat 1%nat); try lia.
        intros j Hj. replace j with 0%nat by lia. rewrite E1, E2. reflexivity.
  Qed.
End Strcmp.

Theorem rstrcmp_holds : rstrcmp_contract.
Proof.
  unfold rstrcmp_contract, RSTRCMP.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m sx sy
         HX NX HY NY.
  exact (entry ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m sx sy
           (bv_unsigned a0) (bv_unsigned a1) HX NX HY NY a0 a1 a2 a3 eq_refl eq_refl).
Qed.
