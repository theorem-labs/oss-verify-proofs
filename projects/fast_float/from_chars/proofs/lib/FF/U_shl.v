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
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Bigint_defs Bigint_shl Ubsan_chk.

Module U_shl_bits_stmt.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Bigint_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.

Notation USEGS := Ubsan.M.loaded_segments.

Definition shl_bits_entry : Z := 0x27964.

Definition shl_bits_W (A : Z) : list ivl := [(A, A + 498)]%Z.

Definition shl_bits_post
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (A n : Z) (ws : list word) (len : Z)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (b : Z) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 : word) (m' : word -> option byte)
                    (ws' : list word) (len' : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 b) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom USEGS)
    /\ munch (shl_bits_W A) m m'
    /\ wmono USEGS m m'
    /\ u64arr USEGS m' A ws'
    /\ length ws' = 62%nat
    /\ rw_cells USEGS m' (A + 496) [C2 (Z_to_bv 64 len')]
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
    u64arr USEGS m (bv_unsigned a0) ws -> length ws = 62%nat ->
    rw_cells USEGS m (bv_unsigned a0 + 496) [C2 (Z_to_bv 64 len)] ->
    (0 <= len <= 62)%Z ->
    (1 <= bv_unsigned a1 <= 63)%Z ->
    evt USEGS (shl_bits_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6
                 F fc (bv_unsigned a0) (bv_unsigned a1) ws len m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x27964) fc None m (seg_rom USEGS)).
End U_shl_bits_stmt.


Module U_shl_limbs_stmt.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Bigint_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.

Notation USEGS := Ubsan.M.loaded_segments.

Definition shl_limbs_entry : Z := 0x27a0c.

Definition shl_limbs_W (sp A : Z) : list ivl := [(sp - 112, sp); (A, A + 498)]%Z.

Definition shl_limbs_post
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (A n : Z) (ws : list word) (len : Z)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (b : Z) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte)
                    (ws' : list word) (len' : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 b) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom USEGS)
    /\ munch (shl_limbs_W (bv_unsigned sp) A) m m'
    /\ wmono USEGS m m'
    /\ stk USEGS m' (bv_unsigned sp - 112) (bv_unsigned sp)
    /\ u64arr USEGS m' A ws'
    /\ length ws' = 62%nat
    /\ rw_cells USEGS m' (A + 496) [C2 (Z_to_bv 64 len')]
    /\ (0 <= len' <= 62)%Z
    /\ (0 <= b <= 1)%Z
    /\ (b = 1%Z -> bval ws' (Z.to_nat len') = (bval ws (Z.to_nat len) * 2 ^ (64 * n))%Z
                   /\ (bnorm ws (Z.to_nat len) -> bnorm ws' (Z.to_nat len')))
    /\ ((n + len <= 62)%Z -> b = 1%Z).

Definition shl_limbs_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (ws : list word) (len : Z),
    stk USEGS m (bv_unsigned sp - 112) (bv_unsigned sp) ->
    u64arr USEGS m (bv_unsigned a0) ws -> length ws = 62%nat ->
    rw_cells USEGS m (bv_unsigned a0 + 496) [C2 (Z_to_bv 64 len)] ->
    (0 <= len <= 62)%Z -> (bv_unsigned a0 mod 8 = 0)%Z -> (0 < bv_unsigned a0)%Z ->
    (bv_unsigned a1 < 2 ^ 58)%Z ->
    (bv_unsigned a0 + 498 <= bv_unsigned sp - 112 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
    evt USEGS (shl_limbs_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                 F fc (bv_unsigned a0) (bv_unsigned a1) ws len m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x27a0c) fc None m (seg_rom USEGS)).
End U_shl_limbs_stmt.

From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_shl_stmt.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.Bigint_defs OSSVerify.Proofs.fast_float.from_chars.lib.FF.Bigint_shl OSSVerify.Proofs.fast_float.from_chars.lib.FF.Ubsan_chk OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_shl.U_shl_bits_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_shl.U_shl_limbs_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_shl_stmt.
Import ListNotations.

Module U_shl_bits.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Bigint_defs Bigint_shl.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.Bigint_defs OSSVerify.Proofs.fast_float.from_chars.lib.FF.Bigint_shl OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_shl.U_shl_bits_stmt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section Loop.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 : word).
  Variables (vec nw : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte).
  Variables (ws : list word) (len : Z).
  Hypothesis Hlen : length ws = 62%nat.
  Hypothesis LEN : (0 <= len <= 62)%Z.
  Hypothesis Hn : (1 <= bv_unsigned nw <= 63)%Z.

  Notation A := (bv_unsigned vec).
  Notation r := (bv_unsigned nw).
  Notation POST := (shl_bits_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 F fc A r ws len m0).

  (* [comment removed for export] *)
  #[using="Hlen LEN Hn"] Lemma sb_tail : forall (prev t0 t1 a5 a6 a7 t3 : word) (cur : list word) (m : word -> option byte),
    u64arr USEGS m A cur -> length cur = 62%nat ->
    rw_cells USEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
    shl_inv ws cur r (Z.to_nat len) (bv_unsigned prev) ->
    ((0 < len)%Z -> prev = nth (Z.to_nat len - 1) ws w0) ->
    munch (shl_bits_W A) m0 m -> wmono USEGS m0 m ->
    evt USEGS POST
      (MS (mkR ra sp gp tp t0 t1 prev s0 s1 vec nw (Z_to_bv 64 len) (Z_to_bv 64 (64 - r)) (Z_to_bv 64 64) a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x279c8) fc None m (seg_rom USEGS)).
  Proof. LiaFast.lf_pins (fun (Hlen LEN Hn : LiaFast.U) => LiaFast.u0).
    intros prev t0 t1 a5 a6 a7 t3 cur m CUR Hcur LC INV PREV MU WM.
    pose proof (bv_unsigned_in_range 64 vec) as RA. unfold bv_modulus in RA.
    pose proof (bv_unsigned_in_range 64 prev) as Rp. unfold bv_modulus in Rp.
    pose proof (u64arr_bound _ _ _ _ CUR) as Bd. rewrite Hcur in Bd.
    pose proof (rw_cells_bound _ _ _ _ LC) as Bc. cbn [cells_size csize Nat.add] in Bc.
    cbv delta [shl_bits_W] in MU.
    step. (* [comment removed for export] *)
    rewrite (unsigned_lit (64 - r)) by lia. rewrite (Z.mod_small (64 - r) 64) by lia.
    pose proof (shr_small (bv_unsigned prev) r Rp Hn) as Rc.
    assert (R2r : (2 ^ r <= 2 ^ 63)%Z) by (apply Z.pow_le_mono_r; lia).
    rewrite Z.shiftr_div_pow2 by lia.
    remember (bv_unsigned prev / 2 ^ (64 - r))%Z as c eqn:Ec.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hcz.
    - cond_cleanup Hcz.
      step. step. (* [comment removed for export] *)
      unfold shl_bits_post. finish.
      { exact CUR. } { exact Hcur. } { exact LC. } all: try lia.
      intros _. split; [| split; [lia|]].
      + apply (shl_inv_finish_nocarry ws _ r _ (bv_unsigned prev)); [exact INV| lia].
      + intros BN.
        destruct (Nat.eq_dec (Z.to_nat len) 0) as [E0|NE]. { left; exact E0. }
        apply bnorm_of_value; [lia|].
        pose proof (bnorm_lower ws (Z.to_nat len) BN ltac:(lia)) as LO.
        rewrite (shl_inv_finish_nocarry ws _ r _ _ INV) by lia.
        assert (1 <= 2 ^ r)%Z by (pose proof (Z.pow_le_mono_r 2 0 r); lia).
        pose proof (bval_nonneg ws (Z.to_nat len)). nia.
    - cond_cleanup Hcz.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hroom.
      + cond_cleanup Hroom.
        step. step. step. (* [comment removed for export] *)
        unfold shl_bits_post. finish.
        { exact CUR. } { exact Hcur. } { exact LC. } all: try lia.
        intros CAP. exfalso.
        pose proof (shl_carry_room ws _ r (Z.to_nat len) (bv_unsigned prev) INV Hn ltac:(lia) CAP) as ROOM. lia.
      + cond_cleanup Hroom.
        zstep. (* [comment removed for export] *)
        rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3)%Z with 8%Z.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_not_taken.
        zstep. (* [comment removed for export] *)
        replace (A + len * 8)%Z with (A + 8 * len)%Z by lia.
        zstep. (* [comment removed for export] *)
        pose proof (u64arr_store_ok USEGS m A _ len (Z_to_bv 64 (A + 8 * len)) CUR ltac:(rewrite Hcur; lia) eq_refl) as SOK.
        step. (* [comment removed for export] *)
        pose proof (u64arr_write USEGS m A _ len (Z_to_bv 64 c) CUR ltac:(rewrite Hcur; lia)) as CUR'.
        store_done.
        step. (* [comment removed for export] *)
        step. step. step. (* [comment removed for export] *)
        unfold shl_bits_post. finish.
        { exact CUR'. } { rewrite upd_length. exact Hcur. } { exact LC. } all: try lia.
        intros _. split; [| split; [lia|]].
        * replace (Z.to_nat (len + 1)) with (S (Z.to_nat len)) by lia. subst c.
          apply (shl_inv_finish_carry ws _ r _ (bv_unsigned prev)); [exact INV| rewrite Hlen; lia | exact Hn].
        * intros BN. replace (Z.to_nat (len + 1)) with (S (Z.to_nat len)) by lia.
          apply bnorm_push; [rewrite Hcur; lia|]. rewrite unsigned_lit by lia. lia.
  Qed.

  Definition loop_ok (k : nat) : Prop :=
    forall (i : nat) (cnt rem : Z) (p prev t2 t3 : word) (cur : list word) (m : word -> option byte),
      (Z.to_nat len - i = k)%nat -> (i < Z.to_nat len)%nat ->
      (cnt = 63 - Z.of_nat i)%Z -> (rem = len - Z.of_nat i)%Z ->
      bv_unsigned p = (A + 8 * Z.of_nat i)%Z ->
      u64arr USEGS m A cur -> length cur = 62%nat ->
      rw_cells USEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      shl_inv ws cur r i (bv_unsigned prev) ->
      munch (shl_bits_W A) m0 m -> wmono USEGS m0 m ->
      evt USEGS POST
        (MS (mkR ra sp gp tp p prev t2 s0 s1 vec nw (Z_to_bv 64 len) (Z_to_bv 64 (64 - r)) (Z_to_bv 64 64)
                 (Z_to_bv 64 (Z.lor (64 - r) r)) (Z_to_bv 64 cnt) (Z_to_bv 64 rem)
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x27988) fc None m (seg_rom USEGS)).

  #[using="Hlen LEN Hn"] Lemma loop_body : forall k, loop_ok k -> loop_ok (S k).
  Proof. LiaFast.lf_pins (fun (Hlen LEN Hn : LiaFast.U) => LiaFast.u0).
    intros k IH. unfold loop_ok. intros i cnt rem p prev t2 t3 cur m Hk Hi Hcnt Hrem Hp CUR Hcur LC INV MU WM. subst cnt rem.
    pose proof (bv_unsigned_in_range 64 vec) as RA. unfold bv_modulus in RA.
    cbv delta [shl_bits_W] in MU.
    pose proof (u64arr_bound _ _ _ _ CUR) as Bd. rewrite Hcur in Bd.
    pose proof (bv_unsigned_in_range 64 prev) as Rp. unfold bv_modulus in Rp.
    pose proof (lor_lt_64 (64 - r) r ltac:(lia) ltac:(lia)) as Hlor.
    destruct INV as (Hv & Hag & Hpr & Hlc).
    pose proof (Hag i ltac:(lia)) as Hnth.
    destruct (nth_error cur i) as [w|] eqn:Hnw. 2:{ exfalso. apply nth_error_None in Hnw. lia. }
    assert (Hw : w = nth i ws w0). { rewrite <- Hnth. symmetry. apply nth_error_nth. exact Hnw. }
    pose proof (bv_unsigned_in_range 64 w) as Rw. unfold bv_modulus in Rw.
    step. (* [comment removed for export] *)
    if_not_taken.
    step. (* [comment removed for export] *)
    if_not_taken.
    pose proof (u64arr_read USEGS m A cur (Z.of_nat i) w p CUR ltac:(rewrite Nat2Z.id; exact Hnw) ltac:(lia) ltac:(symmetry; apply wa_of_var; lia)) as RD.
    step. (* [comment removed for export] *)
    clear RD.
    step. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit (64 - r)) by lia.
    rewrite ?(Z.mod_small (64 - r) 64) by lia. rewrite ?(Z.mod_small r 64) by lia.
    rewrite (shlb_limb_word (bv_unsigned w) (bv_unsigned prev) r) by lia.
    pose proof (shlb_limb_range (bv_unsigned w) (bv_unsigned prev) r Rw Rp Hn) as Rz.
    pose proof (u64arr_store_ok USEGS m A cur (Z.of_nat i) p CUR ltac:(lia) ltac:(symmetry; apply wa_of_var; lia)) as SOK.
    step. (* [comment removed for export] *)
    pose proof (u64arr_write USEGS m A cur (Z.of_nat i) (Z_to_bv 64 (shlb_limb (bv_unsigned w) (bv_unsigned prev) r)) CUR ltac:(lia)) as CUR'.
    replace (A + 8 * Z.of_nat i)%Z with (bv_unsigned p + 0)%Z in CUR' by lia. rewrite Nat2Z.id in CUR'.
    store_done.
    step. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    assert (INV' : shl_inv ws (upd cur i (Z_to_bv 64 (shlb_limb (bv_unsigned w) (bv_unsigned prev) r))) r (S i) (bv_unsigned w)).
    { replace (bv_unsigned w) with (limbZ ws i) by (unfold limbZ; rewrite <- Hw; reflexivity).
      apply (shl_inv_step ws _ r i (bv_unsigned prev)); [split; [exact Hv| split; [exact Hag| split; [exact Hpr| exact Hlc]]] | rewrite Hlen; lia | exact Hn |].
      rewrite unsigned_lit by (unfold limbZ; rewrite <- Hw; lia). reflexivity. }
    step. (* [comment removed for export] *)
    if_cases Hb.
    - cond_cleanup Hb.
      eapply (IH (S i) _ _ (Z_to_bv 64 (bv_unsigned p + 8)) w); try eassumption; try lia.
      + rewrite unsigned_lit by lia. lia.
      + rewrite upd_length. exact Hcur.
    - cond_cleanup Hb.
      assert (Hil : S i = Z.to_nat len) by lia.
      step. (* [comment removed for export] *)
      if_taken.
      eapply sb_tail; try eassumption.
      all: first [ rewrite upd_length; exact Hcur
                 | rewrite <- Hil; exact INV'
                 | intros _; rewrite <- Hil; replace (S i - 1)%nat with i by lia; exact Hw
                 | cbv delta [shl_bits_W]; exact MU ].
  Qed.
End Loop.

Section Loop2.
  Context (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 : word)
          (vec nw : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte)
          (ws : list word) (len : Z)
          (Hlen : length ws = 62%nat) (LEN : (0 <= len <= 62)%Z) (Hn : (1 <= bv_unsigned nw <= 63)%Z).
  #[using="Hlen LEN Hn"] Lemma sb_loop : forall k, loop_ok ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 vec nw F fc m0 ws len k.
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
  pose proof (wmono_refl USEGS m) as WM.
  step. (* [comment removed for export] *)
  rewrite zx16_lit_small by lia.
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  if_cases Hz.
  - cond_cleanup Hz.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_not_taken.
    eapply (sb_tail ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 a0 a1 F fc m ws len L62 ltac:(lia) Hn
              (Z_to_bv 64 0)); try eassumption; try lia.
    all: first [ rewrite Hz; rewrite unsigned_lit by lia; apply shl_inv_init; exact Hn | intros H; exfalso; lia ].
  - cond_cleanup Hz.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite (unsigned_lit (64 - bv_unsigned a1)) by lia.
    eapply (sb_loop ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 a0 a1 F fc m ws len
              L62 ltac:(lia) Hn (Z.to_nat len) 0%nat 63%Z len a0 (Z_to_bv 64 0)); try eassumption; try lia.
    all: try (rewrite unsigned_lit by lia; apply shl_inv_init; exact Hn).
Qed.
End U_shl_bits.

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

Section Main.
  Hypothesis shl_bits_spec : shl_bits_stmt.
  Hypothesis shl_limbs_spec : shl_limbs_stmt.

  Section Fixed.
  Variables (ra sp gp tp a0 a1 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (ws : list word) (len : Z) (j5 : list byte).
  Notation A := (bv_unsigned a0).
  Notation n := (bv_unsigned a1).
  Notation POST := (shl_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A n ws len m).
  Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -32)).
  Hypothesis L62 : length ws = 62%nat.
  Hypothesis Hlen : (0 <= len <= 62)%Z.
  Hypothesis A8 : (A mod 8 = 0)%Z.
  Hypothesis A0p : (0 < A)%Z.
  Hypothesis SEP : (A + 498 <= bv_unsigned sp - 144 \/ bv_unsigned sp <= A)%Z.
  Hypothesis Rsp : (0 <= bv_unsigned sp < 2 ^ 64)%Z.
  Hypothesis SPB : (0 <= bv_unsigned sp - 144)%Z.
  Hypothesis HA : (0 <= A /\ A + 498 <= 2 ^ 64)%Z.

  (* [comment removed for export] *)
  #[using="shl_limbs_spec L62 Hlen A8 A0p SEP Rsp SPB"] Lemma shl_from_80 : forall (x1 t0 t1 t2 x10 x11 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m1 : word -> option byte) (ws1 : list word) (len1 : Z),
    u64arr USEGS m1 A ws1 -> length ws1 = 62%nat ->
    rw_cells USEGS m1 (A + 496) [C2 (Z_to_bv 64 len1)] -> (0 <= len1 <= 62)%Z ->
    stk USEGS m1 (bv_unsigned sp - 144) (bv_unsigned sp + -32) ->
    rw_cells USEGS m1 (bv_unsigned sp + -32) [CB 8 j5; C8 s1; C8 s0; C8 ra] ->
    munch (shl_W (bv_unsigned sp) A) m m1 -> wmono USEGS m m1 ->
    bval ws1 (Z.to_nat len1) = (bval ws (Z.to_nat len) * 2 ^ (n mod 64))%Z ->
    (bnorm ws (Z.to_nat len) -> bnorm ws1 (Z.to_nat len1)) ->
    (len1 <= len + 1)%Z -> ((0 < len)%Z -> (0 < len1)%Z) ->
    evt USEGS POST (MS (mkR x1 SP' gp tp t0 t1 t2 a1 a0 x10 x11 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x27934) fc None m1 (seg_rom USEGS)).
  Proof. LiaFast.lf_pins (fun (shl_limbs_spec L62 Hlen A8 A0p SEP Rsp SPB : LiaFast.U) => LiaFast.u0).
    intros * CUR L1 LENC Hlen1 ST FR MU WM VAL BN LB LP.
    cbv delta [shl_W] in MU.
    pose proof (bv_unsigned_in_range 64 a1) as Rn. unfold bv_modulus in Rn.
    pose proof (bval_nonneg ws (Z.to_nat len)) as X0.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases H64.
    - cond_cleanup H64.
      step. (* [comment removed for export] *)
      do 5 step.
      release_frame FR ST (bv_unsigned sp).
      unfold shl_post. finish.
      { exact CUR. } { exact L1. } { exact LENC. } all: try lia.
      intros BN0 CAP _. split; [reflexivity|]. split; [| apply BN; exact BN0].
      rewrite VAL. rewrite Z.mod_small by lia. reflexivity.
    - cond_cleanup H64.
      zstep. (* [comment removed for export] *)
      rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 6)%Z with 64%Z.
      step. (* [comment removed for export] *)
      pose proof (unsigned_lit (bv_unsigned sp + -32) ltac:(lia)) as ULs.
      pose proof (unsigned_lit (n / 64) ltac:(split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia])) as ULd.
      step. (* [comment removed for export] *)
      call shl_limbs_spec.
      1:{ rewrite ULs. replace (bv_unsigned sp + -32 - 112)%Z with (bv_unsigned sp - 144)%Z by lia. exact ST. }
      1:{ exact CUR. } 1:{ exact L1. } 1:{ exact LENC. } 1:{ exact Hlen1. } 1:{ exact A8. } 1:{ exact A0p. }
      1:{ rewrite ULd. apply Z.div_lt_upper_bound; lia. }
      1:{ rewrite ULs. lia. }
      rewrite ?ULs, ?ULd in *.
      rename x into b.
      step. (* [comment removed for export] *)
      if_cases Hb.
      + (* [comment removed for export] *)
        cond_cleanup Hb.
        do 5 step.
        match goal with H : stk USEGS _ _ _ |- _ => rename H into ST' end.
        replace (bv_unsigned sp + -32 - 112)%Z with (bv_unsigned sp - 144)%Z in ST' by lia.
        release_frame FR ST' (bv_unsigned sp).
        unfold shl_post. finish. all: try eassumption. all: try lia.
        intros BN0 CAP SMALL. exfalso.
        rewrite ?unsigned_lit in Hb by lia.
        match goal with H : (_ <= 62)%Z -> b = 1%Z |- _ => enough (n / 64 + len1 <= 62)%Z by lia end.
        (* [comment removed for export] *)
        destruct (Z.eq_dec len 0) as [L0|L0].
        * (* [comment removed for export] *)
          destruct SMALL as [|SMALL]; [lia|].
          assert (n / 64 < 63)%Z by (apply Z.div_lt_upper_bound; lia).
          destruct (Z.eq_dec len1 0) as [|L1nz]; [lia|]. exfalso.
          pose proof (bnorm_lower ws1 (Z.to_nat len1) (BN BN0) ltac:(lia)) as LO.
          rewrite VAL, L0 in LO. change (Z.to_nat 0) with 0%nat in LO. rewrite bval_0, Z.mul_0_l in LO.
          pose proof (pow64_pos (Z.to_nat len1 - 1)). lia.
        * pose proof (BN BN0) as BN1. specialize (LP ltac:(lia)).
          pose proof (bnorm_lower ws1 (Z.to_nat len1) BN1 ltac:(lia)) as LO.
          unfold BIG_CAP in CAP. rewrite (pow2_split64 n) in CAP by lia.
          rewrite VAL in LO.
          assert (E1 : (2 ^ (64 * Z.of_nat (Z.to_nat len1 - 1)) * 2 ^ (64 * (n / 64)) < 2 ^ 3968)%Z).
          { eapply Z.le_lt_trans; [| exact CAP].
            replace (bval ws (Z.to_nat len) * (2 ^ (n mod 64) * 2 ^ (64 * (n / 64))))%Z
               with (bval ws (Z.to_nat len) * 2 ^ (n mod 64) * 2 ^ (64 * (n / 64)))%Z by ring.
            apply Z.mul_le_mono_nonneg_r; [apply Z.pow_nonneg; lia| exact LO]. }
          rewrite <- Z.pow_add_r in E1 by lia. apply Z.pow_lt_mono_r_iff in E1; lia.
      + cond_cleanup Hb. rewrite ?unsigned_lit in Hb by lia.
        match goal with H : b = 1%Z -> _ |- _ => destruct (H ltac:(lia)) as [VAL2 BN2] end.
        step. (* [comment removed for export] *)
        do 5 step.
        match goal with H : stk USEGS _ _ _ |- _ => rename H into ST' end.
        replace (bv_unsigned sp + -32 - 112)%Z with (bv_unsigned sp - 144)%Z in ST' by lia.
        release_frame FR ST' (bv_unsigned sp).
        unfold shl_post. finish. all: try eassumption. all: try lia.
        intros BN0 CAP _. split; [reflexivity|]. split.
        * rewrite VAL2, VAL. rewrite <- Z.mul_assoc, <- Z.pow_add_r by (try apply Z.mul_nonneg_nonneg; try apply Z.div_pos; try apply Z.mod_pos_bound; lia).
          f_equal. f_equal. pose proof (Z.div_mod n 64 ltac:(lia)). lia.
        * apply BN2. apply BN. exact BN0.
  Qed.
  End Fixed.

  #[using="shl_bits_spec shl_limbs_spec"] Lemma shl_spec : shl_stmt.
  Proof. LiaFast.lf_pins (fun (shl_bits_spec shl_limbs_spec : LiaFast.U) => LiaFast.u0).
    unfold shl_stmt. intros until len. intros ST AL LIMBS L62 LENC Hlen A8 A0p SEP.
    pose proof (munch_refl (shl_W (bv_unsigned sp) (bv_unsigned a0)) m) as MU.
    cbv delta [shl_W] in MU.
    pose proof (wmono_refl USEGS m) as WM.
    pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
    pose proof (bv_unsigned_in_range 64 a1) as Rn. unfold bv_modulus in Rn.
    pose proof (u64arr_bound _ _ _ _ LIMBS) as Bl. rewrite L62 in Bl.
    pose proof (rw_cells_bound _ _ _ _ LENC) as Bc. cbn [cells_size csize Nat.add] in Bc.
    assert (HA : (0 <= bv_unsigned a0 /\ bv_unsigned a0 + 498 <= 2 ^ 64)%Z) by lia. clear Bl Bc.
    assert (SPB : (0 <= bv_unsigned sp - 144)%Z) by (destruct ST as (? & ? & ?); lia).
    carve_frame 32%nat ST.
    do 4 step. (* [comment removed for export] *)
    match type of FR with context [CB 8 ?j] => remember j as j5 eqn:E5 in FR; clear E5 end.
    step. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    change 63%Z with (Z.ones 6). rewrite Z.land_ones by lia. change (2 ^ 6)%Z with 64%Z.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hrem.
    - cond_cleanup Hrem.
      eapply shl_from_80; try eassumption; try lia.
      all: first [ rewrite Hrem, Z.pow_0_r; lia | intros B; exact B | idtac ].
    - cond_cleanup Hrem.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      call shl_bits_spec.
      1:{ exact LIMBS. } 1:{ exact L62. } 1:{ exact LENC. } 1:{ exact Hlen. }
      1:{ rewrite unsigned_lit by lia. pose proof (Z.mod_pos_bound (bv_unsigned a1) 64 ltac:(lia)). lia. }
      rename x into b.
      step. (* [comment removed for export] *)
      if_cases Hb.
      + cond_cleanup Hb.
        do 5 step.
        release_frame FR ST (bv_unsigned sp).
        unfold shl_post. finish. all: try eassumption. all: try lia.
        intros BN0 CAP _. exfalso.
        rewrite unsigned_lit in * by lia.
        match goal with H : (_ < BIG_CAP)%Z -> b = 1%Z |- _ => enough (b = 1%Z) by lia; apply H end.
        eapply Z.le_lt_trans; [| exact CAP]. apply Z.mul_le_mono_nonneg_l; [apply bval_nonneg|].
        apply Z.pow_le_mono_r; [lia|]. apply Z.mod_le; lia.
      + cond_cleanup Hb.
        rewrite unsigned_lit in * by lia.
        match goal with H : b = 1%Z -> _ |- _ => destruct (H ltac:(lia)) as (VAL1 & LB1 & BN1) end.
        eapply shl_from_80; try eassumption; try lia.
  Qed.
End Main.
