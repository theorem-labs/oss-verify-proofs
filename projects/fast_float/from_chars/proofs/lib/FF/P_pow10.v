(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Bigint_defs Bigint_shl ImgFacts P_pow5_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_pow5_stmt.

Module P_shl_bits_stmt.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Bigint_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.

Notation PSEGS := Plain.M.loaded_segments.

Definition shl_bits_entry : Z := 0x268c8.

Definition shl_bits_W (A : Z) : list ivl := [(A, A + 498)]%Z.

Definition shl_bits_post
    (ra sp gp tp t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (A n : Z) (ws : list word) (len : Z)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (b : Z) (t0 t1 a1 a2 a3 a4 a5 a6 a7 : word) (m' : word -> option byte)
                    (ws' : list word) (len' : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 b) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom PSEGS)
    /\ munch (shl_bits_W A) m m'
    /\ wmono PSEGS m m'
    /\ u64arr PSEGS m' A ws'
    /\ length ws' = 62%nat
    /\ rw_cells PSEGS m' (A + 496) [C2 (Z_to_bv 64 len')]
    /\ (0 <= len' <= 62)%Z
    /\ (0 <= b <= 1)%Z
    /\ (b = 1%Z -> bval ws' (Z.to_nat len') = (bval ws (Z.to_nat len) * 2 ^ n)%Z
                   /\ (len <= len' <= len + 1)%Z
                   /\ (bnorm ws (Z.to_nat len) -> bnorm ws' (Z.to_nat len')))
    /\ ((bval ws (Z.to_nat len) * 2 ^ n < BIG_CAP)%Z -> b = 1%Z).

Definition shl_bits_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (ws : list word) (len : Z),
    u64arr PSEGS m (bv_unsigned a0) ws -> length ws = 62%nat ->
    rw_cells PSEGS m (bv_unsigned a0 + 496) [C2 (Z_to_bv 64 len)] ->
    (0 <= len <= 62)%Z ->
    (1 <= bv_unsigned a1 <= 63)%Z ->
    evt PSEGS (shl_bits_post ra sp gp tp t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                 F fc (bv_unsigned a0) (bv_unsigned a1) ws len m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x268c8) fc None m (seg_rom PSEGS)).
End P_shl_bits_stmt.

Module P_shl_bits.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Bigint_defs Bigint_shl.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.Bigint_defs OSSVerify.Proofs.fast_float.from_chars.lib.FF.Bigint_shl OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_pow10.P_shl_bits_stmt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section Loop.
  Variables (ra sp gp tp t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word).
  Variables (vec nw : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte).
  Variables (ws : list word) (len : Z).
  Hypothesis Hlen : length ws = 62%nat.
  Hypothesis LEN : (0 < len <= 62)%Z.
  Hypothesis Hn : (1 <= bv_unsigned nw <= 63)%Z.

  Notation A := (bv_unsigned vec).
  Notation r := (bv_unsigned nw).
  Notation POST := (shl_bits_post ra sp gp tp t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc A r ws len m0).

  Definition loop_ok (k : nat) : Prop :=
    forall (i : nat) (p prev t0 t1 : word) (cur : list word) (m : word -> option byte),
      (Z.to_nat len - i = k)%nat -> (i < Z.to_nat len)%nat ->
      bv_unsigned p = (A + 8 * Z.of_nat i)%Z ->
      u64arr PSEGS m A cur -> length cur = 62%nat ->
      rw_cells PSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      shl_inv ws cur r i (bv_unsigned prev) ->
      (i <> 0%nat -> prev = nth (i - 1) ws w0) ->
      munch (shl_bits_W A) m0 m -> wmono PSEGS m0 m ->
      evt PSEGS POST
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) nw vec (Z_to_bv 64 len) (Z_to_bv 64 (A + 8 * len)) prev
                 (Z_to_bv 64 (64 - r)) p
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x268f0) fc None m (seg_rom PSEGS)).

  #[using="Hlen LEN Hn"] Lemma loop_body : forall k, loop_ok k -> loop_ok (S k).
  Proof. LiaFast.lf_pins (fun (Hlen LEN Hn : LiaFast.U) => LiaFast.u0).
    intros k IH. unfold loop_ok. intros i p prev t0 t1 cur m Hk Hi Hp CUR Hcur LC INV PREV MU WM.
    pose proof (bv_unsigned_in_range 64 vec) as RA. unfold bv_modulus in RA.
    cbv delta [shl_bits_W] in MU.
    pose proof (u64arr_bound _ _ _ _ CUR) as Bd. rewrite Hcur in Bd.
    pose proof (bv_unsigned_in_range 64 prev) as Rp. unfold bv_modulus in Rp.
    destruct INV as (Hv & Hag & Hpr & Hlc).
    pose proof (Hag i ltac:(lia)) as Hnth.
    destruct (nth_error cur i) as [w|] eqn:Hnw. 2:{ exfalso. apply nth_error_None in Hnw. lia. }
    assert (Hw : w = nth i ws w0). { rewrite <- Hnth. symmetry. apply nth_error_nth. exact Hnw. }
    pose proof (bv_unsigned_in_range 64 w) as Rw. unfold bv_modulus in Rw.
    step. (* [comment removed for export] *)
    pose proof (u64arr_read PSEGS m A cur (Z.of_nat i) w p CUR ltac:(rewrite Nat2Z.id; exact Hnw) ltac:(lia) ltac:(symmetry; apply wa_of_var; lia)) as RD.
    step. (* [comment removed for export] *)
    clear RD.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite (unsigned_lit (64 - r)) by lia.
    rewrite (Z.mod_small (64 - r) 64) by lia. rewrite (Z.mod_small r 64) by lia.
    rewrite (shlb_limb_word (bv_unsigned w) (bv_unsigned prev) r) by lia.
    pose proof (shlb_limb_range (bv_unsigned w) (bv_unsigned prev) r Rw Rp Hn) as Rz.
    pose proof (u64arr_store_ok PSEGS m A cur (Z.of_nat i) p CUR ltac:(lia) ltac:(symmetry; apply wa_of_var; lia)) as SOK.
    step. (* [comment removed for export] *)
    pose proof (u64arr_write PSEGS m A cur (Z.of_nat i) (Z_to_bv 64 (shlb_limb (bv_unsigned w) (bv_unsigned prev) r)) CUR ltac:(lia)) as CUR'.
    replace (A + 8 * Z.of_nat i)%Z with (bv_unsigned p + 0)%Z in CUR' by lia. rewrite Nat2Z.id in CUR'.
    store_done.
    step. (* [comment removed for export] *)
    assert (INV' : shl_inv ws (upd cur i (Z_to_bv 64 (shlb_limb (bv_unsigned w) (bv_unsigned prev) r))) r (S i) (bv_unsigned w)).
    { replace (bv_unsigned w) with (limbZ ws i) by (unfold limbZ; rewrite <- Hw; reflexivity).
      apply (shl_inv_step ws _ (bv_unsigned nw) i (bv_unsigned prev)); [split; [exact Hv| split; [exact Hag| split; [exact Hpr| exact Hlc]]] | rewrite Hlen; lia | exact Hn |].
      rewrite unsigned_lit by (unfold limbZ; rewrite <- Hw; lia). reflexivity. }
    step. (* [comment removed for export] *)
    if_cases Hb.
    - (* [comment removed for export] *)
      cond_cleanup Hb.
      eapply (IH (S i) (Z_to_bv 64 (bv_unsigned p + 8)) w); try eassumption; try lia.
      + rewrite unsigned_lit by lia. lia.
      + rewrite upd_length. exact Hcur.
      + intros _. rewrite Hw. f_equal. lia.
    - (* [comment removed for export] *)
      cond_cleanup Hb.
      assert (Hil : S i = Z.to_nat len) by lia.
      step. (* [comment removed for export] *)
      rewrite (unsigned_lit (64 - r)) by lia. rewrite (Z.mod_small (64 - r) 64) by lia.
      pose proof (shr_small (bv_unsigned w) r Rw Hn) as Rc.
      assert (R2r : (2 ^ r <= 2 ^ 63)%Z) by (apply Z.pow_le_mono_r; lia).
      rewrite Z.shiftr_div_pow2 by lia.
      remember (bv_unsigned w / 2 ^ (64 - r))%Z as c eqn:Ec.
      step. (* [comment removed for export] *)
      if_cases Hcz.
      + (* [comment removed for export] *)
        cond_cleanup Hcz.
        step. (* [comment removed for export] *)
        unfold shl_bits_post. finish.
        { exact CUR'. } { rewrite upd_length. exact Hcur. } { exact LC. } all: try lia.
        * intros _. split; [| split; [lia|]].
          -- rewrite <- Hil. apply (shl_inv_finish_nocarry ws _ r (S i) (bv_unsigned w)); [exact INV'| lia].
          -- intros BN. rewrite <- Hil in BN |- *. right. cbn [Nat.sub]. rewrite Nat.sub_0_r.
             unfold limbZ. rewrite nth_upd_same by (rewrite Hcur; lia). rewrite unsigned_lit by lia.
             apply shlb_top_nonzero; try lia.
             destruct BN as [BN|BN]; [lia|]. cbn [Nat.sub] in BN. rewrite Nat.sub_0_r in BN. unfold limbZ in BN. rewrite <- Hw in BN. lia.
      + (* [comment removed for export] *)
        cond_cleanup Hcz.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases Hroom.
        * (* [comment removed for export] *)
          cond_cleanup Hroom.
          step. step. (* [comment removed for export] *)
          unfold shl_bits_post. finish.
          { exact CUR'. } { rewrite upd_length. exact Hcur. } { exact LC. } all: try lia.
          intros CAP. exfalso.
          pose proof (shl_carry_room ws _ r (S i) (bv_unsigned w) INV' Hn ltac:(lia)) as ROOM. rewrite Hil in ROOM. lia.
        * cond_cleanup Hroom.
          pose proof (u64arr_store_ok PSEGS m1 A _ len (Z_to_bv 64 (A + 8 * len)) CUR' ltac:(rewrite upd_length; lia) eq_refl) as SOK2.
          step. (* [comment removed for export] *)
          pose proof (u64arr_write PSEGS m1 A _ len (Z_to_bv 64 c) CUR' ltac:(rewrite upd_length; lia)) as CUR''.
          store_done.
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          unfold shl_bits_post. finish.
          { exact CUR''. } { rewrite !upd_length. exact Hcur. } { exact LC. } all: try lia.
          intros _. split; [| split; [lia|]].
          -- replace (Z.to_nat (len + 1)) with (S (Z.to_nat len)) by lia. rewrite <- Hil. subst c.
             apply (shl_inv_finish_carry ws _ r (S i) (bv_unsigned w)); [exact INV'| rewrite Hlen; lia | exact Hn].
          -- intros BN. replace (Z.to_nat (len + 1)) with (S (Z.to_nat len)) by lia.
             apply bnorm_push; [rewrite upd_length, Hcur; lia|]. rewrite unsigned_lit by lia. lia.
  Qed.
End Loop.

Section Loop2.
  Context (ra sp gp tp t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
          (vec nw : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte)
          (ws : list word) (len : Z)
          (Hlen : length ws = 62%nat) (LEN : (0 < len <= 62)%Z) (Hn : (1 <= bv_unsigned nw <= 63)%Z).
  #[using="Hlen LEN Hn"] Lemma sb_loop : forall k, loop_ok ra sp gp tp t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 vec nw F fc m0 ws len k.
  Proof. LiaFast.lf_pins (fun (Hlen LEN Hn : LiaFast.U) => LiaFast.u0).
    induction k as [|k IH].
    - unfold loop_ok. intros. exfalso. lia.
    - apply loop_body; assumption.
  Qed.
End Loop2.

Lemma shl_bits_spec : shl_bits_stmt.
Proof.
  unfold shl_bits_stmt. intros until len. intros LIMBS L62 LENC Hlen Hn.
  pose proof (bv_unsigned_in_range 64 a0) as RA. unfold bv_modulus in RA.
  pose proof (u64arr_bound _ _ _ _ LIMBS) as Bd. rewrite L62 in Bd.
  pose proof (munch_refl (shl_bits_W (bv_unsigned a0)) m) as MU.
  pose proof (wmono_refl PSEGS m) as WM.
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  rewrite zx16_lit_small by lia.
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  if_cases Hz.
  - cond_cleanup Hz. step. (* [comment removed for export] *)
    unfold shl_bits_post. finish.
    { exact LIMBS. } { exact L62. } { exact LENC. } all: try lia.
    intros _. subst len. change (Z.to_nat 0) with 0%nat. rewrite !bval_0. split; [lia| split; [lia| intros B; exact B]].
  - cond_cleanup Hz.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite Z.shiftl_mul_pow2 by lia. replace (bv_unsigned a0 + len * 2 ^ 3)%Z with (bv_unsigned a0 + 8 * len)%Z by lia.
    eapply (sb_loop ra sp gp tp t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a0 a1 F fc m ws len
              L62 ltac:(lia) Hn (Z.to_nat len) 0%nat a0); try eassumption; try lia.
    rewrite unsigned_lit by lia. apply shl_inv_init. exact Hn.
Qed.
End P_shl_bits.

Module P_memmove_stmt.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.

Notation PSEGS := Plain.M.loaded_segments.

Definition memmove_entry : Z := 0x5e6f4.

Definition memmove_post
    (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (n : Z) (bs : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom PSEGS)
    /\ munch [(bv_unsigned a0, bv_unsigned a0 + n)]%Z m m'
    /\ wmono PSEGS m m'
    /\ u8arr PSEGS m' (bv_unsigned a0) bs.

Definition memmove_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs old : list byte),
    bytes_at PSEGS m (bv_unsigned a1) bs ->
    u8arr PSEGS m (bv_unsigned a0) old ->
    length old = length bs ->
    Z.of_nat (length bs) = bv_unsigned a2 ->
    (bv_unsigned a0 mod 8 = 0)%Z -> (bv_unsigned a1 mod 8 = 0)%Z -> (bv_unsigned a2 mod 8 = 0)%Z ->
    (bv_unsigned a2 < 2^63)%Z ->
    (bv_unsigned a0 + bv_unsigned a2 < 2^64)%Z ->
    (bv_unsigned a1 + bv_unsigned a2 < 2^64)%Z ->
    (bv_unsigned ra mod 2 = 0)%Z ->
    evt PSEGS (memmove_post ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a2) bs m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x5e6f4) fc None m (seg_rom PSEGS)).
End P_memmove_stmt.

Module P_memmove.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_memcpy_stmt P_memcpy.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_memcpy_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_memcpy OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_pow10.P_memmove_stmt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma mm_disj : forall D S N, (0 <= D -> 0 <= S -> 0 <= N < 2^63 -> D + N < 2^64 -> S + N < 2^64 -> D <> S ->
  (S - (N + D)) mod 2^64 <= (0 - (Z.shiftl N 1) mod 2^64) mod 2^64 -> D + N <= S \/ S + N <= D)%Z.
Proof.
  intros D S N HD HS HN H1 H2 H3 H. rewrite Z.shiftl_mul_pow2 in H by lia. change (2^1)%Z with 2%Z in H.
  Z.div_mod_to_equations. lia.
Qed.

Lemma land7_lxor_aligned : forall S D, (0 <= S < 2^64 -> 0 <= D < 2^64 -> S mod 8 = 0 -> D mod 8 = 0 ->
  Z.land (bv_unsigned (Z_to_bv 64 (Z.lxor S D))) 7 = 0)%Z.
Proof.
  intros S D HS HD H1 H2. rewrite unsigned_lit by (apply Z_lxor_range; lia).
  assert (E : forall x, (0 <= x -> x mod 8 = 0 -> forall i, 0 <= i < 3 -> Z.testbit x i = false)%Z).
  { intros x Hx Hm i Hi. replace x with ((x / 8) * 2^3)%Z by lia. apply Z.mul_pow2_bits_low. lia. }
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.lxor_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i 3).
  - rewrite (E S), (E D) by lia. reflexivity.
  - replace (Z.testbit 7 i) with false; [apply andb_false_r|]. symmetry. change 7%Z with (Z.ones 3). apply Z.ones_spec_high. lia.
Qed.

Lemma land7_aligned : forall D, (0 <= D -> D mod 8 = 0 -> Z.land D 7 = 0)%Z.
Proof. intros D HD H. change 7%Z with (Z.ones 3). rewrite Z.land_ones by lia. exact H. Qed.

(* [comment removed for export] *)
Lemma split8_front : forall {A} (l : list A), (8 <= length l)%nat ->
  exists b0 b1 b2 b3 b4 b5 b6 b7 l', l = [b0;b1;b2;b3;b4;b5;b6;b7] ++ l'.
Proof.
  intros A l H. destruct l as [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 [|b6 [|b7 l']]]]]]]]; cbn in H; try lia.
  exists b0, b1, b2, b3, b4, b5, b6, b7, l'. reflexivity.
Qed.

Lemma split8_back : forall {A} (l : list A), (8 <= length l)%nat ->
  exists l' b0 b1 b2 b3 b4 b5 b6 b7, l = l' ++ [b0;b1;b2;b3;b4;b5;b6;b7] /\ length l' = (length l - 8)%nat.
Proof.
  intros A l H.
  pose proof (firstn_skipn (length l - 8) l) as E.
  assert (L : length (skipn (length l - 8) l) = 8%nat) by (rewrite skipn_length; lia).
  destruct (skipn (length l - 8) l) as [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 [|b6 [|b7 [|x l']]]]]]]]]; cbn in L; try lia.
  exists (firstn (length l - 8) l), b0, b1, b2, b3, b4, b5, b6, b7. split; [symmetry; exact E|].
  rewrite firstn_length. lia.
Qed.

Section Proof.
  Let memcpy_spec : memcpy_stmt := P_memcpy.memcpy_spec.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte).
  Notation D := (bv_unsigned a0). Notation S := (bv_unsigned a1). Notation N := (bv_unsigned a2).
  Notation POST := (memmove_post ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc N bs m).
  Hypothesis LBS : Z.of_nat (length bs) = N.
  Hypothesis BD : (0 <= D /\ D + N < 2^64)%Z.
  Hypothesis BS : (0 <= S /\ S + N < 2^64)%Z.
  Hypothesis AL2 : (N mod 8 = 0)%Z.

  (* [comment removed for export] *)
  #[using="LBS BD BS AL2"] Lemma loopF : forall (k : nat) (K : Z) (mq : word -> option byte) (done todo rest : list byte) (a5 a6 a7 : word),
    (Z.to_nat (N - K) <= k)%nat ->
    u8arr PSEGS mq D done -> u8arr PSEGS mq (D + K) todo -> bytes_at PSEGS mq (S + K) rest ->
    Z.of_nat (length done) = K -> length todo = length rest -> done ++ rest = bs ->
    munch [(D, D + N)]%Z m mq -> wmono PSEGS m mq ->
    (D + 8 <= S)%Z -> (0 <= K)%Z -> (K + 8 <= N)%Z -> (K mod 8 = 0)%Z ->
    forall (w2 w3 w4 : word), w2 = Z_to_bv 64 (N - K) -> w3 = Z_to_bv 64 (D + K) -> w4 = Z_to_bv 64 (S + K) ->
    evt PSEGS POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 7) w2 w3 w4 a5 a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x5e854) fc None mq (seg_rom PSEGS)).
  Proof. LiaFast.lf_pins (fun (LBS BD BS AL2 : LiaFast.U) => LiaFast.u0).
    induction k as [|k IH]; intros K mq done todo rest a5 a6 a7 Hk DONE TODO SRCR Ld Lt Hbs MU WM DS K0 K8 KAL w2 w3 w4 -> -> ->; [lia|].
    pose proof (bytes_at_bound _ _ _ _ SRCR) as Br.
    assert (Lr : (8 <= length rest)%nat).
    { apply (f_equal (@length byte)) in Hbs. rewrite app_length in Hbs. lia. }
    destruct (split8_front rest Lr) as (b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & rest' & ->).
    destruct (split8_front todo ltac:(lia)) as (c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & todo' & ->).
    (* [comment removed for export] *)
    pose proof (bytes_at_read PSEGS mq (S + K) _ 0 8 SRCR ltac:(lia) ltac:(cbn; lia)) as RD.
    change (firstn 8 (skipn (Z.to_nat 0) ([b0; b1; b2; b3; b4; b5; b6; b7] ++ rest'))) with [b0; b1; b2; b3; b4; b5; b6; b7] in RD.
    rewrite Z.add_0_r in RD.
    rewrite <- (le8_le_bytes_to_word8 b0 b1 b2 b3 b4 b5 b6 b7) in RD.
    step. (* [comment removed for export] *)
    clear RD.
    step. (* [comment removed for export] *)
    (* [comment removed for export] *)
    apply (proj1 (u8arr_app PSEGS mq (D + K) [c0; c1; c2; c3; c4; c5; c6; c7] todo')) in TODO.
    destruct TODO as [HEAD TODO]. cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in TODO.
    pose proof (u8arr_store_ok PSEGS mq (D + K) _ 0 _ HEAD ltac:(cbn; lia) eq_refl) as SOK0.
    pose proof (wr_at_store_ok PSEGS mq (D + K) 8 0 8 (proj2 HEAD) ltac:(lia) ltac:(lia)) as SOK.
    clear SOK0. rewrite Z.add_0_r in SOK.
    step. (* [comment removed for export] *)
    rewrite le8_le_bytes_to_word8.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem mq ?a ?l8) _) =>
      change (write_to_mem mq a l8) with (write_to_mem mq (wa (D + K)) l8);
      pose proof (u8arr_write_all PSEGS mq (D + K) _ l8 HEAD eq_refl) as HEAD';
      apply (u8arr_frame PSEGS mq D done (D + K) l8) in DONE; [| lia | cbn; lia | cbn; lia];
      apply (u8arr_frame PSEGS mq _ todo' (D + K) l8) in TODO; [| lia | cbn; lia | cbn; lia];
      apply bytes_at_app in SRCR; destruct SRCR as [_ SRCR]; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in SRCR;
      apply (bytes_at_write_other PSEGS mq (D + K) l8) in SRCR; [| lia | cbn; lia | cbn; lia];
      apply (munch_write _ m mq (D + K) l8) in MU; [| lia | cbn; lia | cbn; lia];
      apply (wmono_write PSEGS m mq (wa (D + K)) l8) in WM;
      remember (write_to_mem mq (wa (D + K)) l8) as mq' eqn:Heqm; clear Heqm HEAD SOK; try clear mq
    end.
    (* [comment removed for export] *)
    rewrite <- Ld in HEAD'.
    pose proof (proj2 (u8arr_app PSEGS mq' D done [b0; b1; b2; b3; b4; b5; b6; b7]) (conj DONE HEAD')) as DONE'.
    clear DONE HEAD'. rename DONE' into DONE.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hc.
    - cond_cleanup Hc.
      replace (N - K + -8)%Z with (N - (K + 8))%Z by lia.
      replace (D + K + 8)%Z with (D + (K + 8))%Z by lia.
      replace (S + K + 8)%Z with (S + (K + 8))%Z by lia.
      eapply (IH (K + 8)%Z mq' (done ++ [b0; b1; b2; b3; b4; b5; b6; b7]) todo' rest'); try lia; try reflexivity.
      all: try (Z.div_mod_to_equations; lia).
      + exact DONE.
      + replace (D + (K + 8))%Z with (D + K + Z.of_nat 8)%Z by lia. exact TODO.
      + replace (S + (K + 8))%Z with (S + K + Z.of_nat 8)%Z by lia. exact SRCR.
      + rewrite app_length. cbn [length]. lia.
      + cbn in Lt. lia.
      + rewrite <- app_assoc. exact Hbs.
      + exact MU.
      + exact WM.
    - (* [comment removed for export] *)
      cond_cleanup Hc.
      assert (K8N : (K + 8 = N)%Z) by (Z.div_mod_to_equations; lia).
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hz. 2:{ cond_cleanup Hz. exfalso; lia. }
      step. (* [comment removed for export] *)
      assert (Hr : rest' = []).
      { apply (f_equal (@length byte)) in Hbs. rewrite !app_length in Hbs. cbn [length] in Hbs.
        destruct rest'; [reflexivity| cbn [length] in Hbs; lia]. }
      subst rest'. rewrite app_nil_r in Hbs. subst bs.
      apply evt_done. unfold memmove_post.
      do 15 eexists. split; [reflexivity|].
      split. { exact MU. }
      split. { exact WM. }
      exact DONE.
  Qed.


  (* [comment removed for export] *)
  #[using="LBS BD AL2"] Lemma loopB : forall (k : nat) (rem : Z) (mq : word -> option byte) (todo done rest : list byte) (a3 a7 : word),
    (Z.to_nat rem <= k)%nat ->
    u8arr PSEGS mq D todo -> u8arr PSEGS mq (D + rem) done -> bytes_at PSEGS mq S rest ->
    Z.of_nat (length rest) = rem -> length todo = length rest -> rest ++ done = bs ->
    munch [(D, D + N)]%Z m mq -> wmono PSEGS m mq ->
    (S + 8 <= D)%Z -> (8 <= rem <= N)%Z -> (rem mod 8 = 0)%Z ->
    forall (w2 : word), w2 = Z_to_bv 64 rem ->
    evt PSEGS POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 w2 a3 (Z_to_bv 64 (S + -8)) (Z_to_bv 64 (D + -8)) (Z_to_bv 64 7) a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x5e820) fc None mq (seg_rom PSEGS)).
  Proof. LiaFast.lf_pins (fun (LBS BD AL2 : LiaFast.U) => LiaFast.u0).
    induction k as [|k IH]; intros rem mq todo done rest a3 a7 Hk TODO DONE SRCR Lr Lt Hbs MU WM DS R8 RAL w2 ->; [lia|].
    pose proof (bytes_at_bound _ _ _ _ SRCR) as Br.
    destruct (split8_back rest ltac:(lia)) as (rest' & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & -> & Lr').
    destruct (split8_back todo ltac:(lia)) as (todo' & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & -> & Lt').
    rewrite ?app_length in Lr'. rewrite ?app_length in Lt'. rewrite ?app_length in Lr. rewrite ?app_length in Lt. rewrite ?app_length in Lt.
    cbn [length] in Lr', Lt', Lr, Lt.
    (* [comment removed for export] *)
    pose proof (proj1 (bytes_at_app PSEGS mq S rest' [b0; b1; b2; b3; b4; b5; b6; b7]) SRCR) as [SRCR' RDW].
    pose proof (bytes_at_read PSEGS mq (S + Z.of_nat (length rest')) _ 0 8 RDW ltac:(lia) ltac:(cbn; lia)) as RD.
    change (firstn 8 (skipn (Z.to_nat 0) [b0; b1; b2; b3; b4; b5; b6; b7])) with [b0; b1; b2; b3; b4; b5; b6; b7] in RD.
    rewrite Z.add_0_r in RD.
    rewrite <- (le8_le_bytes_to_word8 b0 b1 b2 b3 b4 b5 b6 b7) in RD.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    clear RD RDW.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    (* [comment removed for export] *)
    apply (proj1 (u8arr_app PSEGS mq D todo' [c0; c1; c2; c3; c4; c5; c6; c7])) in TODO.
    destruct TODO as [TODO HEAD].
    pose proof (wr_at_store_ok PSEGS mq (D + Z.of_nat (length todo')) 8 0 8 (proj2 HEAD) ltac:(lia) ltac:(lia)) as SOK.
    rewrite Z.add_0_r in SOK.
    assert (LT : Z.of_nat (length todo') = (rem - 8)%Z) by lia.
    replace (D + Z.of_nat (length todo'))%Z with (D + -8 + rem)%Z in SOK by lia.
    step. (* [comment removed for export] *)
    rewrite le8_le_bytes_to_word8.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem mq ?a ?l8) _) =>
      replace (write_to_mem mq a l8) with (write_to_mem mq (wa (D + Z.of_nat (length todo'))) l8) by (f_equal; unfold wa; f_equal; lia);
      pose proof (u8arr_write_all PSEGS mq (D + Z.of_nat (length todo')) _ l8 HEAD eq_refl) as HEAD';
      apply (u8arr_frame PSEGS mq D todo' (D + Z.of_nat (length todo')) l8) in TODO; [| lia | cbn; lia | cbn; lia];
      apply (u8arr_frame PSEGS mq _ done (D + Z.of_nat (length todo')) l8) in DONE; [| lia | cbn; lia | cbn; lia];
      apply (bytes_at_write_other PSEGS mq (D + Z.of_nat (length todo')) l8) in SRCR'; [| lia | cbn; lia | cbn; lia];
      apply (munch_write _ m mq (D + Z.of_nat (length todo')) l8) in MU; [| lia | cbn; lia | cbn; lia];
      apply (wmono_write PSEGS m mq (wa (D + Z.of_nat (length todo'))) l8) in WM;
      clear SRCR; remember (write_to_mem mq (wa (D + Z.of_nat (length todo'))) l8) as mq' eqn:Heqm; clear Heqm HEAD SOK; try clear mq
    end.
    (* [comment removed for export] *)
    replace (D + rem)%Z with (D + Z.of_nat (length todo') + Z.of_nat (length [b0; b1; b2; b3; b4; b5; b6; b7]))%Z in DONE by (cbn [length]; lia).
    pose proof (proj2 (u8arr_app PSEGS mq' _ [b0; b1; b2; b3; b4; b5; b6; b7] done) (conj HEAD' DONE)) as DONE'.
    clear DONE HEAD'. rename DONE' into DONE.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hc.
    - cond_cleanup Hc.
      replace (rem + -8)%Z with (rem - 8)%Z by lia.
      eapply (IH (rem - 8)%Z mq' todo' ([b0; b1; b2; b3; b4; b5; b6; b7] ++ done) rest'); try lia; try reflexivity.
      all: try (Z.div_mod_to_equations; lia).
      + exact TODO.
      + replace (D + (rem - 8))%Z with (D + Z.of_nat (length todo'))%Z by lia. exact DONE.
      + exact SRCR'.
      + rewrite <- app_assoc in Hbs. exact Hbs.
      + exact MU.
      + exact WM.
    - cond_cleanup Hc.
      assert (R8e : rem = 8%Z) by (Z.div_mod_to_equations; lia).
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hz. 2:{ cond_cleanup Hz. exfalso; lia. }
      step. (* [comment removed for export] *)
      assert (Hr : rest' = []) by (destruct rest'; [reflexivity| cbn [length] in Lr; lia]).
      assert (Ht : todo' = []) by (destruct todo'; [reflexivity| cbn [length] in LT; lia]).
      subst rest' todo'. cbn [app] in Hbs. subst bs.
      cbn [length] in DONE. change (Z.of_nat 0) with 0%Z in DONE. rewrite Z.add_0_r in DONE.
      apply evt_done. unfold memmove_post.
      do 15 eexists. split; [reflexivity|].
      split. { exact MU. }
      split. { exact WM. }
      exact DONE.
  Qed.

  #[using="memcpy_spec LBS BD BS AL2"] Lemma memmove_main : forall (a3 a4 a5 a6 a7 : word) (old : list byte),
    bytes_at PSEGS m S bs -> u8arr PSEGS m D old -> length old = length bs ->
    (D mod 8 = 0)%Z -> (S mod 8 = 0)%Z -> (N < 2^63)%Z -> (bv_unsigned ra mod 2 = 0)%Z ->
    evt PSEGS POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x5e6f4) fc None m (seg_rom PSEGS)).
  Proof. LiaFast.lf_pins (fun (memcpy_spec LBS BD BS AL2 : LiaFast.U) => LiaFast.u0).
    intros a3 a4 a5 a6 a7 old SRC DST LEN AL0 AL1 N63 RA.
    pose proof (munch_refl [(D, D + N)]%Z m) as MU. pose proof (wmono_refl PSEGS m) as WM.
    pose proof (bv_unsigned_in_range 64 a2) as R2. unfold bv_modulus in R2.
    step. (* [comment removed for export] *)
    if_cases Heq.
    { (* [comment removed for export] *)
      cond_cleanup Heq. step.
      apply evt_done. unfold memmove_post. do 15 eexists. split; [reflexivity|].
      split. { exact MU. } split. { exact WM. }
      destruct DST as [_ W]. rewrite LEN, LBS in W. split; [rewrite Heq; exact SRC | rewrite LBS; exact W]. }
    cond_cleanup Heq.
    step. step. step. step.
    step. (* [comment removed for export] *)
    if_cases Hmc.
    { cond_cleanup Hmc.
      pose proof (mm_disj D S N ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Heq Hmc) as DISJ.
      clear Hmc.
      step. (* [comment removed for export] *)
      call memcpy_spec.
      1:{ exact SRC. } 1:{ exact DST. } 1:{ exact LEN. } 1:{ exact LBS. } 1:{ exact DISJ. } 1:{ lia. } 1:{ lia. } 1:{ exact RA. }
      apply evt_done. unfold memmove_post. do 15 eexists. split; [reflexivity|].
      split. { exact MU. } split. { exact WM. } assumption. }
    clear Hmc.
    step. step. (* [comment removed for export] *)
    rewrite (land7_lxor_aligned S D) by lia.
    step. (* [comment removed for export] *)
    if_cases Hdir.
    - (* [comment removed for export] *)
      cond_cleanup Hdir.
      step. (* [comment removed for export] *)
      if_cases Hz; [clear Hz| cond_cleanup Hz; exfalso; lia].
      step. step. (* [comment removed for export] *)
      rewrite (unsigned_lit (D + N)) by lia. rewrite (land7_aligned (D + N)) by (try lia; Z.div_mod_to_equations; lia).
      step. (* [comment removed for export] *)
      if_cases Hz; [clear Hz| cond_cleanup Hz; exfalso; lia].
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases H8.
      + cond_cleanup H8. assert (N0 : N = 0%Z) by (Z.div_mod_to_equations; lia).
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases Hz; [clear Hz| cond_cleanup Hz; exfalso; lia].
        step. (* [comment removed for export] *)
        assert (Hb : bs = []) by (destruct bs; [reflexivity| cbn [length] in LBS; lia]).
        assert (Ho : old = []) by (destruct old; [reflexivity| rewrite Hb in LEN; cbn [length] in LEN; lia]).
        subst old.
        apply evt_done. unfold memmove_post. do 15 eexists. split; [reflexivity|].
        split. { exact MU. } split. { exact WM. } rewrite Hb. exact DST.
      + cond_cleanup H8.
        step. step. step. (* [comment removed for export] *)
        eapply (loopB (Z.to_nat N) N m old [] bs); try eassumption; try lia.
        all: try (symmetry; apply Z_to_bv_bv_unsigned).
        all: try (rewrite app_nil_r; reflexivity).
        split. { apply bytes_at_nil. lia. } { split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia. }
    - (* [comment removed for export] *)
      cond_cleanup Hdir.
      step. (* [comment removed for export] *)
      if_cases Hz; [clear Hz| cond_cleanup Hz; exfalso; lia].
      step. (* [comment removed for export] *)
      rewrite (land7_aligned D) by lia.
      step. (* [comment removed for export] *)
      if_cases Hz; [clear Hz| cond_cleanup Hz; exfalso; lia].
      step. step. step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases H8.
      + cond_cleanup H8. assert (N0 : N = 0%Z) by (Z.div_mod_to_equations; lia).
        step. (* [comment removed for export] *)
        if_cases Hz; [clear Hz| cond_cleanup Hz; exfalso; lia].
        step. (* [comment removed for export] *)
        assert (Hb : bs = []) by (destruct bs; [reflexivity| cbn [length] in LBS; lia]).
        assert (Ho : old = []) by (destruct old; [reflexivity| rewrite Hb in LEN; cbn [length] in LEN; lia]).
        subst old.
        apply evt_done. unfold memmove_post. do 15 eexists. split; [reflexivity|].
        split. { exact MU. } split. { exact WM. } rewrite Hb. exact DST.
      + cond_cleanup H8.
        step. (* [comment removed for export] *)
        eapply (loopF (Z.to_nat N) 0%Z m [] old bs); try lia.
        all: try (rewrite ?Z.add_0_r, ?Z.sub_0_r; symmetry; apply Z_to_bv_bv_unsigned).
        all: try (rewrite Z.add_0_r; eassumption).
        all: try eassumption. all: try reflexivity.
        (* [comment removed for export] *)
        split. { apply bytes_at_nil. lia. } { split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia. }
  Qed.
End Proof.

Lemma memmove_spec : memmove_stmt.
Proof.
  unfold memmove_stmt. intros until old. intros SRC DST LEN N AL0 AL1 AL2 N63 NW0 NW1 RA.
  pose proof (bytes_at_bound _ _ _ _ SRC) as Bs. pose proof (u8arr_bound _ _ _ _ DST) as Bd. rewrite LEN in Bd.
  eapply memmove_main; try eassumption; lia.
Qed.
End P_memmove.

Module P_shl.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Bigint_defs Bigint_shl.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_memset_stmt P_memset.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_pow5_stmt.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.Bigint_defs OSSVerify.Proofs.fast_float.from_chars.lib.FF.Bigint_shl OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_pow10.P_shl_bits_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_pow10.P_shl_bits OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_pow10.P_memmove_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_pow10.P_memmove OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_memset_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_memset OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_pow5_stmt.P_shl_stmt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac name_mem X := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into X end.

Section From58.
  Variables (ra sp gp tp t2 s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
            (ws : list word) (len : Z) (junk : list byte).
  Notation A := (bv_unsigned a0).
  Notation n := (bv_unsigned a1).
  Notation POST := (shl_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A n ws len m).
  Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -32)).
  Hypothesis L62 : length ws = 62%nat.
  Hypothesis Hlen : (0 <= len <= 62)%Z.
  Hypothesis A8 : (A mod 8 = 0)%Z.
  Hypothesis AL : (bv_unsigned sp mod 16 = 0)%Z.
  Hypothesis SEP : (A + 498 <= bv_unsigned sp + -32 \/ bv_unsigned sp <= A)%Z.
  Hypothesis Rsp : (0 <= bv_unsigned sp < 2 ^ 64)%Z.
  Hypothesis Bl : (0 <= A /\ A + 8 * Z.of_nat 62 <= 2 ^ 64)%Z.

  (* [comment removed for export] *)
  #[using="L62 Hlen A8 SEP Rsp Bl"] Lemma shl_from_58 : forall (x1 t0 t1 x10 x11 a2 a3 a4 a5 a6 a7 : word) (m1 : word -> option byte) (ws1 : list word) (len1 : Z),
    u64arr PSEGS m1 A ws1 -> length ws1 = 62%nat ->
    rw_cells PSEGS m1 (A + 496) [C2 (Z_to_bv 64 len1)] -> (0 <= len1 <= 62)%Z ->
    stk PSEGS m1 (bv_unsigned sp + -32) (bv_unsigned sp + -32) ->
    rw_cells PSEGS m1 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
    munch (shl_W (bv_unsigned sp) A) m m1 -> wmono PSEGS m m1 ->
    bval ws1 (Z.to_nat len1) = (bval ws (Z.to_nat len) * 2 ^ (n mod 64))%Z ->
    (bnorm ws (Z.to_nat len) -> bnorm ws1 (Z.to_nat len1)) ->
    evt PSEGS POST (MS (mkR x1 SP' gp tp t0 t1 t2 a0 a1 x10 x11 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x26848) fc None m1 (seg_rom PSEGS)).
  Proof. LiaFast.lf_pins (fun (L62 Hlen A8 SEP Rsp Bl : LiaFast.U) => LiaFast.u0).
    intros x1 t0 t1 x10 x11 a2 a3 a4 a5 a6 a7 m1 ws1 len1 CUR L1 LENC Hlen1 ST FR MU WM VAL BN.
    cbv delta [shl_W] in MU.
    pose proof (bv_unsigned_in_range 64 a1) as Rn. unfold bv_modulus in Rn.
    pose proof (rw_cells_bound _ _ _ _ LENC) as Bc. cbn [cells_size csize Nat.add] in Bc.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases H64.
    - (* [comment removed for export] *)
      cond_cleanup H64.
      step. (* [comment removed for export] *)
      do 6 step.
      release_frame FR ST (bv_unsigned sp).
      unfold shl_post. finish.
      { exact CUR. } { exact L1. } { exact LENC. } all: try lia.
      intros BN0 CAP _. split; [reflexivity|]. split; [| apply BN; exact BN0].
      rewrite VAL. rewrite Z.mod_small by lia. reflexivity.
    - cond_cleanup H64.
      step. (* [comment removed for export] *)
      rewrite zx16_lit_small by lia.
      zstep. (* [comment removed for export] *)
      rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 6)%Z with 64%Z.
      zstep. (* [comment removed for export] *)
      remember (n / 64)%Z as d eqn:Dd.
      assert (Hd : (1 <= d < 2 ^ 58)%Z). { subst d. split. { apply Z.div_le_lower_bound; lia. } apply Z.div_lt_upper_bound; lia. }
      step. (* [comment removed for export] *)
      if_cases Hz.
      + cond_cleanup Hz. subst len1.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases Hov.
        * cond_cleanup Hov.
          step. step. (* [comment removed for export] *)
          do 6 step.
          release_frame FR ST (bv_unsigned sp).
          unfold shl_post. finish.
          { exact CUR. } { exact L1. } { exact LENC. } all: try lia.
          intros BN0 CAP SMALL. exfalso.
          (* [comment removed for export] *)
          change (Z.to_nat 0) with 0%nat in VAL. rewrite bval_0 in VAL.
          assert (Hp : (0 < 2 ^ (n mod 64))%Z) by (apply Z.pow_pos_nonneg; [lia| apply Z.mod_pos_bound; lia]).
          assert (B0 : bval ws (Z.to_nat len) = 0%Z) by nia.
          destruct BN0 as [BN0|BN0].
          -- assert (len = 0)%Z by lia. destruct SMALL as [|SMALL]; [lia|].
             assert (n / 64 < 63)%Z by (apply Z.div_lt_upper_bound; lia). lia.
          -- pose proof (bnorm_lower ws (Z.to_nat len) (or_intror BN0) ltac:(lia)) as LO.
             pose proof (pow64_pos (Z.to_nat len - 1)). lia.
        * cond_cleanup Hov.
          step. (* [comment removed for export] *)
          do 6 step.
          release_frame FR ST (bv_unsigned sp).
          unfold shl_post. finish.
          { exact CUR. } { exact L1. } { exact LENC. } all: try lia.
          intros BN0 CAP _. change (Z.to_nat 0) with 0%nat in VAL |- *. rewrite bval_0 in VAL |- *.
          assert (Hp : (0 < 2 ^ (n mod 64))%Z) by (apply Z.pow_pos_nonneg; [lia| apply Z.mod_pos_bound; lia]).
          assert (B0 : bval ws (Z.to_nat len) = 0%Z) by nia.
          split; [reflexivity|]. split; [rewrite B0; lia| apply bnorm_0].
      + cond_cleanup Hz.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases Hov.
        * cond_cleanup Hov.
          step. step. (* [comment removed for export] *)
          if_taken.
          step. step. (* [comment removed for export] *)
          do 6 step.
          release_frame FR ST (bv_unsigned sp).
          unfold shl_post. finish.
          { exact CUR. } { exact L1. } { exact LENC. } all: try lia.
          intros BN0 CAP SMALL. exfalso.
          pose proof (BN BN0) as BN1.
          pose proof (bnorm_lower ws1 (Z.to_nat len1) BN1 ltac:(lia)) as LO.
          (* [comment removed for export] *)
          unfold BIG_CAP in CAP.
          rewrite (pow2_split64 n) in CAP by lia. rewrite <- Dd in CAP.
          assert (E1 : (2 ^ (64 * 62) <= 2 ^ (64 * Z.of_nat (Z.to_nat len1 - 1)) * 2 ^ (64 * d))%Z).
          { rewrite <- Z.pow_add_r by lia. apply Z.pow_le_mono_r; lia. }
          pose proof (pow64_pos (Z.to_nat len1 - 1)). assert (0 < 2 ^ (64 * d))%Z by (apply Z.pow_pos_nonneg; lia).
          pose proof (bval_nonneg ws (Z.to_nat len)). nia.
        * cond_cleanup Hov.
          zstep. (* [comment removed for export] *)
          rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3)%Z with 8%Z.
          zstep. (* [comment removed for export] *)
          zstep. (* [comment removed for export] *)
          rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3)%Z with 8%Z.
          step. (* [comment removed for export] *)
          (* [comment removed for export] *)
          destruct (Z_of_nat_complete d ltac:(lia)) as [dn Ed].
          destruct (Z_of_nat_complete len1 ltac:(lia)) as [ln El].
          (* [comment removed for export] *)
          pose proof (u64arr_prefix_bytes PSEGS m1 A ws1 ln ltac:(rewrite L1; lia) CUR) as SRC.
          destruct (u64arr_split3 PSEGS m1 A ws1 dn ln ltac:(rewrite L1; lia) CUR) as (U1 & U2 & U3).
          pose proof (u8arr_of_u64arr PSEGS _ _ _ U2) as DST.
          destruct (u64arr_len_split3 ws1 dn ln ltac:(rewrite L1; lia)) as (Ews & Ld & Ll & Lr). rewrite L1 in Lr.
          clear CUR U2.
          pose proof (unsigned_lit (A + d * 8) ltac:(lia)) as UL1. pose proof (unsigned_lit (len1 * 8) ltac:(lia)) as UL2.
          step. (* [comment removed for export] *)
          call memmove_spec.
          1:{ exact SRC. }
          1:{ rewrite UL1. replace (A + d * 8)%Z with (A + 8 * Z.of_nat dn)%Z by lia. exact DST. }
          1:{ rewrite !u64s_length, Ll, firstn_length, L1. lia. }
          1:{ rewrite UL2, u64s_length, firstn_length, L1. lia. }
          1:{ rewrite UL1. rewrite Z_mod_plus_full. exact A8. }
          1:{ exact A8. }
          1:{ rewrite UL2. apply Z_mod_mult. }
          1:{ rewrite UL2. lia. }
          1:{ rewrite UL1, UL2. lia. }
          1:{ rewrite UL2. lia. }
          1:{ rewrite unsigned_lit by lia. reflexivity. }
          name_mem m2. rewrite UL1 in MI, POST.
          pose proof (u64arr_of_u8arr PSEGS m2 (A + d * 8) ln (u64s (firstn ln ws1)) (conj MI POST)
                        ltac:(rewrite u64s_length, firstn_length, L1; lia)) as MID.
          rewrite words_of_bytes_u64s in MID. replace (A + d * 8)%Z with (A + 8 * Z.of_nat dn)%Z in MID by lia.
          clear MI POST.
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          pose proof (unsigned_lit (d * 8) ltac:(lia)) as UL3.
          pose proof (u8arr_of_u64arr PSEGS _ _ _ U1) as DST0.
          step. (* [comment removed for export] *)
          call memset_spec.
          1:{ reflexivity. }
          1:{ exact DST0. }
          1:{ rewrite UL3, u64s_length, Ld. lia. }
          1:{ exact A8. }
          name_mem m3. rewrite UL3 in MI, POST.
          pose proof (u64arr_of_u8arr PSEGS m3 A dn _ (conj MI POST) ltac:(rewrite repeat_length; lia)) as Z1.
          replace (Z.to_nat (d * 8)) with (8 * dn)%nat in Z1 by lia. rewrite words_of_bytes_zero in Z1.
          clear MI POST.
          assert (Lm : length (firstn ln ws1) = ln) by (rewrite firstn_length, L1; lia).
          pose proof (u64arr_join3 PSEGS m3 A _ _ _ dn ln (repeat_length _ _) Lm Z1 MID U3) as CUR2.
          set (ws2 := repeat (Z_to_bv 64 0) dn ++ firstn ln ws1 ++ skipn (dn + ln) ws1) in CUR2.
          assert (L2 : length ws2 = 62%nat). { subst ws2. rewrite !app_length, repeat_length, Lm, Lr. lia. }
          clear Z1 MID U3.
          step. (* [comment removed for export] *)
          rewrite sx16_lit_small by lia.
          zstep. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          do 6 step.
          release_frame FR ST (bv_unsigned sp).
          unfold shl_post. finish.
          { exact CUR2. } { exact L2. } { exact LENC. } all: try lia.
          intros BN0 CAP _. split; [reflexivity|].
          assert (Hhi : forall j, (j < ln)%nat -> nth (dn + j) ws2 w0 = nth j ws1 w0).
          { intros j Hj. subst ws2. rewrite nth_repeat_app_hi. rewrite app_nth1 by (rewrite Lm; exact Hj).
            rewrite <- (firstn_skipn ln ws1) at 2. rewrite app_nth1 by (rewrite Lm; exact Hj). reflexivity. }
          split.
          -- replace (Z.to_nat (len1 + d)) with (dn + ln)%nat by lia.
             rewrite (bval_shift_limbs ws1 ws2 ln dn).
             ++ replace ln with (Z.to_nat len1) by lia. rewrite VAL.
                rewrite (pow2_split64 n) by lia. rewrite <- Dd, Ed. ring.
             ++ intros j Hj. unfold limbZ. subst ws2. rewrite nth_repeat_app_lo by exact Hj. apply unsigned_lit. lia.
             ++ exact Hhi.
          -- right. replace (Z.to_nat (len1 + d) - 1)%nat with (dn + (ln - 1))%nat by lia.
             unfold limbZ. rewrite Hhi by lia.
             pose proof (bnorm_top ws1 (Z.to_nat len1) ltac:(lia) (BN BN0)) as T. unfold limbZ in T.
             replace (Z.to_nat len1 - 1)%nat with (ln - 1)%nat in T by lia. exact T.
  Qed.
End From58.

Lemma shl_spec : shl_stmt.
Proof.
  unfold shl_stmt. intros until len. intros ST AL LIMBS L62 LENC Hlen A8 SEP.
  pose proof (munch_refl (shl_W (bv_unsigned sp) (bv_unsigned a0)) m) as MU.
  pose proof (wmono_refl PSEGS m) as WM.
  cbv delta [shl_W] in MU.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof (bv_unsigned_in_range 64 a1) as Rn. unfold bv_modulus in Rn.
  pose proof (u64arr_bound _ _ _ _ LIMBS) as Bl. rewrite L62 in Bl.
  carve_frame 32%nat ST.
  do 5 step. (* [comment removed for export] *)
  name_mem m0.
  step. (* [comment removed for export] *)
  zstep. (* [comment removed for export] *)
  change 63%Z with (Z.ones 6). rewrite Z.land_ones by lia. change (2 ^ 6)%Z with 64%Z.
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  if_cases Hrem.
  - (* [comment removed for export] *)
    cond_cleanup Hrem.
    eapply shl_from_58; try eassumption; try lia.
    all: lazymatch goal with
         | |- bval _ _ = _ => rewrite Hrem, Z.pow_0_r; lia
         | |- bnorm _ _ -> bnorm _ _ => intros B; exact B
         | |- munch _ _ _ => cbv delta [shl_W]; exact MU
         end.
  - cond_cleanup Hrem.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    call shl_bits_spec.
    1:{ exact LIMBS. } 1:{ exact L62. } 1:{ exact LENC. } 1:{ exact Hlen. }
    1:{ rewrite unsigned_lit by lia. pose proof (Z.mod_pos_bound (bv_unsigned a1) 64 ltac:(lia)). lia. }
    (* [comment removed for export] *)
    rename x into b.
    step. (* [comment removed for export] *)
    if_cases Hb.
    + (* [comment removed for export] *)
      cond_cleanup Hb.
      do 6 step.
      release_frame FR ST (bv_unsigned sp).
      unfold shl_post. finish. all: try eassumption. all: try lia.
      intros BN0 CAP _. exfalso.
      rewrite unsigned_lit in * by lia.
      match goal with H : (_ < BIG_CAP)%Z -> b = 1%Z |- _ =>
        enough (b = 1%Z) by lia; apply H end.
      eapply Z.le_lt_trans; [| exact CAP]. apply Z.mul_le_mono_nonneg_l; [apply bval_nonneg|].
      apply Z.pow_le_mono_r; [lia|]. apply Z.mod_le; lia.
    + cond_cleanup Hb.
      rewrite unsigned_lit in * by lia.
      match goal with H : b = 1%Z -> _ |- _ => destruct (H ltac:(lia)) as (VAL1 & LB1 & BN1) end.
      eapply shl_from_58; try eassumption; try lia.
      all: lazymatch goal with
           | |- bval _ _ = _ => exact VAL1
           | |- bnorm _ _ -> bnorm _ _ => exact BN1
           | |- munch _ _ _ => cbv delta [shl_W]; assumption
           end.
Qed.
End P_shl.

From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_pow10_stmt.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.Bigint_defs OSSVerify.Proofs.fast_float.from_chars.lib.FF.Bigint_shl OSSVerify.Proofs.fast_float.from_chars.lib.FF.ImgFacts OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_pow5_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_pow5_stmt.P_shl_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_pow10.P_shl OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_pow10_stmt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac post_call segs m ::=
  let ms' := fresh "ms'" in let PO := fresh "POST" in
  intros ms' PO;
  destruct_exs PO;
  let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
  destruct PO as [E [MUc [WMc PO]]];
  first [ destruct PO as [MIc PO] | rename PO into MIc ];
  subst ms';
  lazymatch type of MUc with
  | munch ?W m ?m' =>
      let W' := eval hnf in W in change (munch W' m m') in MUc;
      transport_after_call segs m m' MUc WMc;
      clear MUc WMc;
      try match goal with H : mem_inv segs m |- _ => clear H end;
      try clear m
  end;
  try destruct_ands PO;
  try (lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end).

Ltac name_mem X := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into X end.

Section Main.
  Hypothesis pow5_spec : pow5_stmt.

  #[using="pow5_spec"] Lemma pow10_spec : pow10_stmt.
  Proof. LiaFast.lf_pins (fun (pow5_spec : LiaFast.U) => LiaFast.u0).
    unfold pow10_stmt. intros until len. intros ST AL SPLO PR LIMBS L62 LENC Hlen A8 NORM He CAP SEP.
    pose proof (munch_refl (pow10_W (bv_unsigned sp) (bv_unsigned a0)) m) as MU.
    cbv delta [pow10_W] in MU.
    pose proof (wmono_refl PSEGS m) as WM.
    pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
    pose proof (bv_unsigned_in_range 64 a1) as Re. unfold bv_modulus in Re.
    pose proof (u64arr_bound _ _ _ _ LIMBS) as Bl. rewrite L62 in Bl.
    pose proof (rw_cells_bound _ _ _ _ LENC) as Bc. cbn [cells_size csize Nat.add] in Bc.
    pose proof (u64arr_outside_rodata_P m _ _ PR LIMBS ltac:(rewrite L62; lia)) as AROD. rewrite L62 in AROD.
    pose proof (rw_cells_outside_rodata_P m _ _ PR LENC ltac:(cbn; lia)) as CROD. cbn [cells_size csize Nat.add] in CROD.
    assert (HA : (0 <= bv_unsigned a0 /\ bv_unsigned a0 + 498 <= 2 ^ 64)%Z) by lia.
    assert (AROD' : (bv_unsigned a0 + 498 <= 0x10000 \/ 0x22000 <= bv_unsigned a0)%Z) by lia.
    clear Bl Bc AROD CROD. rename AROD' into AROD.
    pose proof (bval_nonneg ws (Z.to_nat len)) as X0.
    assert (CAP5 : (bval ws (Z.to_nat len) * 5 ^ bv_unsigned a1 < BIG_CAP)%Z).
    { rewrite pow10_split in CAP by lia. pose proof (Z.pow_pos_nonneg 2 (bv_unsigned a1) ltac:(lia) ltac:(lia)).
      pose proof (Z.pow_nonneg 5 (bv_unsigned a1) ltac:(lia)). nia. }
    carve_frame 32%nat ST.
    do 4 step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    pose proof (unsigned_lit (bv_unsigned sp + -32) ltac:(lia)) as ULs.
    step. (* [comment removed for export] *)
    call pow5_spec.
    1:{ rewrite ULs. replace (bv_unsigned sp + -32 - 1232)%Z with (bv_unsigned sp - 1264)%Z by lia. exact ST. }
    1:{ rewrite ULs. Z.div_mod_to_equations. lia. }
    1:{ rewrite ULs. lia. }
    1:{ exact PR. } 1:{ exact LIMBS. } 1:{ exact L62. } 1:{ exact LENC. } 1:{ exact Hlen. } 1:{ exact A8. } 1:{ exact NORM. }
    1:{ lia. } 1:{ exact CAP5. }
    1:{ rewrite ULs. lia. }
    rewrite ?ULs in *.
    match goal with H : u64arr PSEGS _ (bv_unsigned a0) ?w |- _ => rename H into XA5; rename w into ws5 end.
    match goal with H : rw_cells PSEGS _ (bv_unsigned a0 + 496) [C2 (Z_to_bv 64 ?l)] |- _ => rename H into LENC5; rename l into len5 end.
    match goal with H : bval ws5 _ = _ |- _ => rename H into VAL5 end.
    match goal with H : bnorm ws5 _ |- _ => rename H into BN5 end.
    match goal with H : stk PSEGS _ _ _ |- _ => rename H into ST5 end.
    step. (* [comment removed for export] *)
    if_not_taken.
    zstep. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    rewrite ?shl32_shr32m, ?shl32_shr32 by lia.
    try rewrite (Z.mod_small (bv_unsigned a1) 4294967296) by lia. rewrite ?(Z_to_bv_bv_unsigned a1).
    step. (* [comment removed for export] *)
    do 4 step. (* [comment removed for export] *)
    replace (bv_unsigned sp + -32 - 1232)%Z with (bv_unsigned sp - 1264)%Z in ST5 by lia.
    release_frame FR ST5 (bv_unsigned sp).
    step. (* [comment removed for export] *)
    (* [comment removed for export] *)
    destruct (stk_split PSEGS _ _ (bv_unsigned sp - 32) _ ST5 ltac:(lia)) as [STlo SThi].
    clear ST5.
    name_mem m5.
    call shl_spec.
    1:{ exact SThi. } 1:{ exact AL. } 1:{ exact XA5. } 1:{ assumption. } 1:{ exact LENC5. } 1:{ lia. } 1:{ exact A8. } 1:{ lia. }
    match goal with H : bnorm ws5 _ -> _ |- _ => rename H into COND end.
    destruct (COND BN5) as (Hb & VAL' & BN').
    { rewrite VAL5. rewrite <- Z.mul_assoc, <- pow10_split by lia. exact CAP. }
    { lia. }
    subst.
    match goal with H : stk PSEGS _ (bv_unsigned sp - 32) _ |- _ => rename H into SThi' end.
    pose proof (stk_merge PSEGS _ _ _ _ STlo SThi' ltac:(lia)) as STall.
    unfold pow10_post. finish.
    all: try eassumption. all: try lia.
    rewrite VAL', VAL5. rewrite <- Z.mul_assoc, <- pow10_split by lia. reflexivity.
  Qed.
End Main.
