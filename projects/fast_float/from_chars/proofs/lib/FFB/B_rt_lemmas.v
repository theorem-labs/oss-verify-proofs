(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require Import B_rt_stmt.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.

Module B_copy_bwd_impl_stmt.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require Import B_rt_stmt.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.

Notation BSEGS := AsanUbsan.M.loaded_segments.

Notation COPY_BWD_IMPL_ENTRY := 0x988fc%Z.
Notation COPY_BWD_IMPL_NEED := 2256%Z.

Definition copy_bwd_impl_entry : Z := COPY_BWD_IMPL_ENTRY.
Definition copy_bwd_impl_need : Z := COPY_BWD_IMPL_NEED.

Definition copy_bwd_impl_W (sp D n : Z) : list ivl := [(sp - COPY_BWD_IMPL_NEED, sp); (D, D + n)]%Z.

Definition copy_bwd_impl_post
    (ra sp gp tp s0 s1 a0 a1 a2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (bs : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a1
                 (Z_to_bv 64 (bv_unsigned a2 - (bv_unsigned a1 - bv_unsigned a0))) a2' a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom BSEGS)
    /\ munch (copy_bwd_impl_W (bv_unsigned sp) (bv_unsigned a2 - (bv_unsigned a1 - bv_unsigned a0))
                              (bv_unsigned a1 - bv_unsigned a0)) m m'
    /\ wmono BSEGS m m'
    /\ u8arr BSEGS m' (bv_unsigned a2 - (bv_unsigned a1 - bv_unsigned a0)) bs
    /\ stk BSEGS m' (bv_unsigned sp - COPY_BWD_IMPL_NEED) (bv_unsigned sp).

Definition copy_bwd_impl_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (v : rt_vals) (n D : Z) (bs old : list byte) (shlo shn shlo2 shn2 : Z),
    stk BSEGS m (bv_unsigned sp - COPY_BWD_IMPL_NEED) (bv_unsigned sp) ->
    (bv_unsigned a1 = bv_unsigned a0 + n)%Z ->
    (bv_unsigned a2 = D + n)%Z ->
    (0 <= n < 2 ^ 40)%Z -> (n mod 8 = 0)%Z ->
    bytes_at BSEGS m (bv_unsigned a0) bs -> Z.of_nat (length bs) = n ->
    u8arr BSEGS m D old -> length old = length bs ->
    (bv_unsigned a0 mod 8 = 0)%Z -> (D mod 8 = 0)%Z ->
    (bv_unsigned ra mod 2 = 0)%Z ->
    (* [comment removed for export] *)
    (app2r (D) (D + n + 8))%Z -> (D + n + 8 <= KTOP)%Z ->
    (app2r (bv_unsigned a0) (bv_unsigned a0 + n + 8))%Z -> (bv_unsigned a0 + n + 8 <= KTOP)%Z ->
    shz BSEGS m (ASAN_B + D / 8) (n / 8) ->
    shz BSEGS m (ASAN_B + bv_unsigned a0 / 8) (n / 8) ->
    rdbl BSEGS m shlo shn ->
    (shlo + 8 <= ASAN_B + D / 8)%Z -> (ASAN_B + (D + n) / 8 + 8 <= shlo + shn)%Z ->
    rdbl BSEGS m shlo2 shn2 ->
    (shlo2 + 8 <= ASAN_B + bv_unsigned a0 / 8)%Z -> (ASAN_B + (bv_unsigned a0 + n) / 8 + 8 <= shlo2 + shn2)%Z ->
    (* [comment removed for export] *)
    (IMG_END <= bv_unsigned sp - COPY_BWD_IMPL_NEED)%Z -> (KHI <= bv_unsigned sp - COPY_BWD_IMPL_NEED)%Z ->
    (bv_unsigned sp <= KTOP)%Z -> (bv_unsigned sp mod 16 = 0)%Z ->
    (D + n <= bv_unsigned sp - COPY_BWD_IMPL_NEED \/ bv_unsigned sp <= D)%Z ->
    (bv_unsigned a0 + n <= bv_unsigned sp - COPY_BWD_IMPL_NEED \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
    (* [comment removed for export] *)
    pristine m RELRO_LO RELRO_HI -> pristine m REALTAB_LO REALTAB_HI ->
    RT m v -> rt_disj v (bv_unsigned sp - COPY_BWD_IMPL_NEED) (bv_unsigned sp) ->
    rt_disj v D (D + n) ->
    evt BSEGS (copy_bwd_impl_post ra sp gp tp s0 s1 a0 a1 a2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc bs m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 COPY_BWD_IMPL_ENTRY) fc None m (seg_rom BSEGS)).
End B_copy_bwd_impl_stmt.

Module B_copy_bwd_stmt.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require Import B_rt_stmt.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.

Notation BSEGS := AsanUbsan.M.loaded_segments.

Notation COPY_BWD_ENTRY := 0x98880%Z.
Notation COPY_BWD_NEED := 2288%Z.

Definition copy_bwd_entry : Z := COPY_BWD_ENTRY.
Definition copy_bwd_need : Z := COPY_BWD_NEED.

Definition copy_bwd_W (sp D n : Z) : list ivl := [(sp - COPY_BWD_NEED, sp); (D, D + n)]%Z.

Definition copy_bwd_post
    (ra sp gp tp s0 s1 a0 a1 a2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (bs : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a1
                 (Z_to_bv 64 (bv_unsigned a2 - (bv_unsigned a1 - bv_unsigned a0))) a2' a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom BSEGS)
    /\ munch (copy_bwd_W (bv_unsigned sp) (bv_unsigned a2 - (bv_unsigned a1 - bv_unsigned a0))
                              (bv_unsigned a1 - bv_unsigned a0)) m m'
    /\ wmono BSEGS m m'
    /\ u8arr BSEGS m' (bv_unsigned a2 - (bv_unsigned a1 - bv_unsigned a0)) bs
    /\ stk BSEGS m' (bv_unsigned sp - COPY_BWD_NEED) (bv_unsigned sp).

Definition copy_bwd_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (v : rt_vals) (n D : Z) (bs old : list byte) (shlo shn shlo2 shn2 : Z),
    stk BSEGS m (bv_unsigned sp - COPY_BWD_NEED) (bv_unsigned sp) ->
    (bv_unsigned a1 = bv_unsigned a0 + n)%Z ->
    (bv_unsigned a2 = D + n)%Z ->
    (0 <= n < 2 ^ 40)%Z -> (n mod 8 = 0)%Z ->
    bytes_at BSEGS m (bv_unsigned a0) bs -> Z.of_nat (length bs) = n ->
    u8arr BSEGS m D old -> length old = length bs ->
    (bv_unsigned a0 mod 8 = 0)%Z -> (D mod 8 = 0)%Z ->
    (bv_unsigned ra mod 2 = 0)%Z ->
    (* [comment removed for export] *)
    (app2r (D) (D + n + 8))%Z -> (D + n + 8 <= KTOP)%Z ->
    (app2r (bv_unsigned a0) (bv_unsigned a0 + n + 8))%Z -> (bv_unsigned a0 + n + 8 <= KTOP)%Z ->
    shz BSEGS m (ASAN_B + D / 8) (n / 8) ->
    shz BSEGS m (ASAN_B + bv_unsigned a0 / 8) (n / 8) ->
    rdbl BSEGS m shlo shn ->
    (shlo + 8 <= ASAN_B + D / 8)%Z -> (ASAN_B + (D + n) / 8 + 8 <= shlo + shn)%Z ->
    rdbl BSEGS m shlo2 shn2 ->
    (shlo2 + 8 <= ASAN_B + bv_unsigned a0 / 8)%Z -> (ASAN_B + (bv_unsigned a0 + n) / 8 + 8 <= shlo2 + shn2)%Z ->
    (* [comment removed for export] *)
    (IMG_END <= bv_unsigned sp - COPY_BWD_NEED)%Z -> (KHI <= bv_unsigned sp - COPY_BWD_NEED)%Z ->
    (bv_unsigned sp <= KTOP)%Z -> (bv_unsigned sp mod 16 = 0)%Z ->
    (D + n <= bv_unsigned sp - COPY_BWD_NEED \/ bv_unsigned sp <= D)%Z ->
    (bv_unsigned a0 + n <= bv_unsigned sp - COPY_BWD_NEED \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
    (* [comment removed for export] *)
    pristine m RELRO_LO RELRO_HI -> pristine m REALTAB_LO REALTAB_HI ->
    RT m v -> rt_disj v (bv_unsigned sp - COPY_BWD_NEED) (bv_unsigned sp) ->
    rt_disj v D (D + n) ->
    evt BSEGS (copy_bwd_post ra sp gp tp s0 s1 a0 a1 a2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc bs m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 COPY_BWD_ENTRY) fc None m (seg_rom BSEGS)).
End B_copy_bwd_stmt.

Module B_memiszero.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require Import B_rt_stmt.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
Local Ltac lia ::= lia_tc.  (* [comment removed for export] *)
Local Ltac step ::=
  app2_lin_all;
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) => step_core segs R F pc fc rv m ro; try decide_lit_if
  | |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail "pc is not a literal:" pc
  end.  (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation BSEGS := AsanUbsan.M.loaded_segments.
Tactic Notation "show" string(tag) := match goal with |- ?g => idtac tag g end.

Notation B_MEMISZERO := 0x73964%Z.
Notation MIZ_NEED := 16%Z.

Definition memiszero_post
    (ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (a1 a2 a3 a4 a5 a6 : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom BSEGS)
    /\ munch [(bv_unsigned sp - MIZ_NEED, bv_unsigned sp)]%Z m m'
    /\ wmono BSEGS m m'
    /\ stk BSEGS m' (bv_unsigned sp - MIZ_NEED) (bv_unsigned sp).

Definition memiszero_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    shz BSEGS m (bv_unsigned a0) (bv_unsigned a1) ->
    (0 < bv_unsigned a1 <= 2^40)%Z ->
    (bv_unsigned a0 + bv_unsigned a1 <= KHI)%Z ->
    stk BSEGS m (bv_unsigned sp - MIZ_NEED) (bv_unsigned sp) ->
    (KHI <= bv_unsigned sp - MIZ_NEED)%Z -> (bv_unsigned sp <= KTOP)%Z ->
    (bv_unsigned ra mod 2 = 0)%Z ->
    evt BSEGS (memiszero_post ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 B_MEMISZERO) fc None m (seg_rom BSEGS)).

(* [comment removed for export] *)
Lemma land_m8w : forall x, (0 <= x < 2^64)%Z -> Z.land x 18446744073709551608 = (x - x mod 8)%Z.
Proof.
  intros x Hx.
  change 18446744073709551608%Z with (Z.ldiff (Z.ones 64) (Z.ones 3)).
  rewrite Z.ldiff_land. rewrite Z.land_assoc. rewrite Z.land_ones by lia.
  rewrite <- Z.ldiff_land. rewrite Z.ldiff_ones_r by lia.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  rewrite (Z.mod_small x (2^64)) by lia.
  change (2^3)%Z with 8%Z. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Ltac fold_or0 :=
  repeat match goal with
  | |- context [Z_to_bv 64 (Z.lor 0 0)] => change (Z_to_bv 64 (Z.lor 0 0)) with (Z_to_bv 64 0)
  | |- context [bv_unsigned (Z_to_bv 64 0)] => rewrite (unsigned_lit 0) by lia
  end.

Section Proof.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0w a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m m1 : word -> option byte)
            (b n e ab ae : Z) (junk : list byte).
  Hypothesis Hb : b = bv_unsigned a0w.
  Hypothesis Hb0 : (0 <= b)%Z.
  Hypothesis Hn : (0 < n <= 2^40)%Z.
  Hypothesis He : e = (b + n)%Z.
  Hypothesis Hhi : (e <= KHI)%Z.
  Hypothesis Hab : (ab mod 8 = 0 /\ b <= ab <= b + 7)%Z.
  Hypothesis Hae : (ae mod 8 = 0 /\ e - 8 < ae <= e)%Z.
  Hypothesis SH : shz BSEGS m1 b n.
  Hypothesis FR : rw_cells BSEGS m1 (bv_unsigned sp + -16) [CB 8 junk; C8 ra].
  Hypothesis ST : stk BSEGS m1 (bv_unsigned sp + -16) (bv_unsigned sp + -16).
  Hypothesis MU : munch [(bv_unsigned sp - MIZ_NEED, bv_unsigned sp)]%Z m m1.
  Hypothesis WM : wmono BSEGS m m1.
  Hypothesis SP1 : (KHI <= bv_unsigned sp - MIZ_NEED)%Z.
  Hypothesis SP2 : (bv_unsigned sp <= KTOP)%Z.
  Hypothesis RA : (bv_unsigned ra mod 2 = 0)%Z.

  Notation POST := (memiszero_post ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m).
  Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -16)).
  (* [comment removed for export] *)
  Notation ST8 xa0 xa2 xa3 xa5 xa6 pc :=
    (MS (mkR ra SP' gp tp t0 t1 t2 s0 s1 xa0 (Z_to_bv 64 0) xa2 xa3 (Z_to_bv 64 e) xa5 xa6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m1 (seg_rom BSEGS)).

  Ltac ranges := pose proof (bv_unsigned_in_range 64 sp) as Rsp; unfold bv_modulus in Rsp;
                 pose proof (shz_bound _ _ _ _ SH) as Bsh.

  (* [comment removed for export] *)
  #[using="b n ab ae junk SH FR ST MU WM"] Lemma fin : forall x10 x12 x13 x14 x15 x16,
    evt BSEGS POST
      (MS (mkR ra SP' gp tp t0 t1 t2 s0 s1 x10 (Z_to_bv 64 0) x12 x13 x14 x15 x16 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x739f0) fc None m1 (seg_rom BSEGS)).
  Proof. LiaFast.lf_pins (fun (b n ab ae junk SH FR ST MU WM : LiaFast.U) => LiaFast.u0).
    intros. ranges.
    step. (* [comment removed for export] *)
    replace (v_sltiu (Z_to_bv 64 0) 1) with (Z_to_bv 64 1) by (vm_compute; reflexivity).
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    pose proof FR as FR'. pose proof ST as ST'.
    release_frame FR' ST' (bv_unsigned sp).
    unfold memiszero_post. finish.
  Qed.

  (* [comment removed for export] *)
  Definition l3_ok (k : nat) : Prop :=
    forall (r : Z) x10 x13 x15 x16, (Z.to_nat (e - r) <= k)%nat -> (b <= r < e)%Z ->
      evt BSEGS POST
        (MS (mkR ra SP' gp tp t0 t1 t2 s0 s1 x10 (Z_to_bv 64 0) (Z_to_bv 64 r) x13 (Z_to_bv 64 (e - r)) x15 x16 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x739dc) fc None m1 (seg_rom BSEGS)).
  #[using="n ab ae junk Hn He Hab Hae SH FR ST MU WM"] Lemma l3 : forall k, l3_ok k.
  Proof. LiaFast.lf_pins (fun (n ab ae junk Hn He Hab Hae SH FR ST MU WM : LiaFast.U) => LiaFast.u0).
    induction k as [|k IH]; unfold l3_ok; intros r x10 x13 x15 x16 Hk Hr; [lia|]. ranges.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *) fold_or0.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hc.
    - cond_cleanup Hc.
      replace (Z_to_bv 64 (e - r + -1)) with (Z_to_bv 64 (e - (r + 1)))%Z by (f_equal; lia).
      eapply (IH (r + 1)%Z); lia.
    - cond_cleanup Hc. eapply fin.
  Qed.

  (* [comment removed for export] *)
  #[using="b n ab junk Hb Hn He Hhi Hab Hae SH FR ST MU WM"] Lemma from604 : forall x13 x15 x16,
    evt BSEGS POST (ST8 a0w (Z_to_bv 64 ae) x13 x15 x16 0x739d0).
  Proof. LiaFast.lf_pins (fun (b n ab junk Hb Hn He Hhi Hab Hae SH FR ST MU WM : LiaFast.U) => LiaFast.u0).
    intros. ranges.
    step. (* [comment removed for export] *)
    if_cases H1.
    - clear H1. eapply fin.
    - cond_cleanup H1.
      step. (* [comment removed for export] *)
      if_cases H2.
      + clear H2. eapply fin.
      + cond_cleanup H2.
        step. (* [comment removed for export] *)
        rewrite (unsigned_lit e), (unsigned_lit ae) by lia.
        eapply (l3 (Z.to_nat (e - ae)) ae); lia.
  Qed.

  (* [comment removed for export] *)
  Definition l2_ok (k : nat) : Prop :=
    forall (w : Z) x13 x16, (Z.to_nat (ae - w) <= k)%nat -> (ab <= w < ae)%Z -> (w mod 8 = 0)%Z ->
      evt BSEGS POST (ST8 a0w (Z_to_bv 64 ae) x13 (Z_to_bv 64 w) x16 0x739c0).
  #[using="b n junk Hb Hb0 Hn He Hhi Hab Hae SH FR ST MU WM"] Lemma l2 : forall k, l2_ok k.
  Proof. LiaFast.lf_pins (fun (b n junk Hb Hb0 Hn He Hhi Hab Hae SH FR ST MU WM : LiaFast.U) => LiaFast.u0).
    induction k as [|k IH]; unfold l2_ok; intros w x13 x16 Hk Hw Hw8; [lia|]. ranges.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *) fold_or0.
    step. (* [comment removed for export] *)
    if_cases Hc.
    - cond_cleanup Hc. eapply (IH (w + 8)%Z); try lia.
    - cond_cleanup Hc. eapply from604.
  Qed.

  (* [comment removed for export] *)
  #[using="b n junk Hb Hb0 Hn He Hhi Hab Hae SH FR ST MU WM"] Lemma from5f0 : forall x13 x16,
    evt BSEGS POST (ST8 a0w (Z_to_bv 64 ae) x13 (Z_to_bv 64 ab) x16 0x739bc).
  Proof. LiaFast.lf_pins (fun (b n junk Hb Hb0 Hn He Hhi Hab Hae SH FR ST MU WM : LiaFast.U) => LiaFast.u0).
    intros. ranges.
    step. (* [comment removed for export] *)
    if_cases Hc.
    - clear Hc. eapply from604.
    - cond_cleanup Hc. eapply (l2 (Z.to_nat (ae - ab)) ab); lia.
  Qed.

  (* [comment removed for export] *)
  Definition l1_ok (k : nat) : Prop :=
    forall (q : Z) x16, (Z.to_nat (ab - q) <= k)%nat -> (b <= q < ab)%Z -> (q < e)%Z ->
      evt BSEGS POST (ST8 a0w (Z_to_bv 64 ae) (Z_to_bv 64 (q + 1)) (Z_to_bv 64 ab) x16 0x739a4).
  #[using="n junk Hb Hb0 Hn He Hhi Hab Hae SH FR ST MU WM"] Lemma l1 : forall k, l1_ok k.
  Proof. LiaFast.lf_pins (fun (n junk Hb Hb0 Hn He Hhi Hab Hae SH FR ST MU WM : LiaFast.U) => LiaFast.u0).
    induction k as [|k IH]; unfold l1_ok; intros q x16 Hk Hq Hqe; [lia|]. ranges.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *) fold_or0.
    step. (* [comment removed for export] *)
    if_cases H1.
    - clear H1. eapply from5f0.
    - cond_cleanup H1.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases H2.
      + cond_cleanup H2.
        replace (Z_to_bv 64 (q + 2)) with (Z_to_bv 64 ((q + 1) + 1))%Z by (f_equal; lia).
        eapply (IH (q + 1)%Z); lia.
      + cond_cleanup H2. eapply from5f0.
  Qed.
End Proof.

Lemma memiszero_spec : memiszero_stmt.
Proof.
  unfold memiszero_stmt. intros until m. intros SH Hn Hhi ST SP1 SP2 RA.
  pose proof (munch_refl [(bv_unsigned sp - MIZ_NEED, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl BSEGS m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof (bv_unsigned_in_range 64 a0) as Ra0. unfold bv_modulus in Ra0.
  pose proof (bv_unsigned_in_range 64 a1) as Ra1. unfold bv_modulus in Ra1.
  pose proof (shz_bound _ _ _ _ SH) as Bsh.
  unfold memiszero_post.
  carve_frame 16%nat ST.
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  if_not_taken.
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  rewrite (unsigned_lit (bv_unsigned a0 + 7)) by lia. rewrite (land_m8w (bv_unsigned a0 + 7)) by lia.
  step. (* [comment removed for export] *)
  rewrite (unsigned_lit (bv_unsigned a0 + bv_unsigned a1)) by lia. rewrite (land_m8w (bv_unsigned a0 + bv_unsigned a1)) by lia.
  set (ab := (bv_unsigned a0 + 7 - (bv_unsigned a0 + 7) mod 8)%Z) in *.
  set (ae := (bv_unsigned a0 + bv_unsigned a1 - (bv_unsigned a0 + bv_unsigned a1) mod 8)%Z) in *.
  assert (Hab : (ab mod 8 = 0 /\ bv_unsigned a0 <= ab <= bv_unsigned a0 + 7)%Z) by (subst ab; Z.div_mod_to_equations; lia).
  assert (Hae : (ae mod 8 = 0 /\ bv_unsigned a0 + bv_unsigned a1 - 8 < ae <= bv_unsigned a0 + bv_unsigned a1)%Z) by (subst ae; Z.div_mod_to_equations; lia).
  clearbody ab ae.
  step. (* [comment removed for export] *)
  if_cases H1.
  - cond_cleanup H1.
    eapply from5f0 with (b := bv_unsigned a0) (n := bv_unsigned a1) (ab := ab) (m := m);
      try eassumption; try reflexivity; try lia.
  - cond_cleanup H1.
    step. (* [comment removed for export] *)
    if_not_taken.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    eapply l1 with (b := bv_unsigned a0) (n := bv_unsigned a1) (ab := ab) (m := m)
                    (k := Z.to_nat (ab - bv_unsigned a0)) (q := bv_unsigned a0);
      try eassumption; try reflexivity; try lia.
Qed.
End B_memiszero.

Module B_rt_m2s.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require Import B_rt_stmt.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
Local Ltac lia ::= lia_tc.  (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation BSEGS := AsanUbsan.M.loaded_segments.

Definition m2s_cells (m : word -> option byte) : Prop :=
     ro_cells BSEGS m 943736 [C8 (Z_to_bv 64 ASAN_B); C4 (Z_to_bv 64 1)]
  /\ ro_cells BSEGS m 947040 [C8 (Z_to_bv 64 (KTOP - 1)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].

Lemma m2s_cells_of_RT : forall m v, RT m v -> m2s_cells m.
Proof. intros m v H. unfold RT in H. split; tauto. Qed.

Definition m2s_post (entry : Z)
    (ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (p : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 a2 a3 a4 a5 a6 a7 : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (ASAN_B + p / 8)) (Z_to_bv 64 ASAN_B) a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom BSEGS)
    /\ munch [] m m
    /\ wmono BSEGS m m
    /\ True.

Definition m2s_stmt (entry : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    m2s_cells m ->
    pristine m RELRO_LO RELRO_HI ->
    ((4096 <= bv_unsigned a0 /\ bv_unsigned a0 < SH_LO) \/ (KHI <= bv_unsigned a0 /\ bv_unsigned a0 < KTOP))%Z ->
    (bv_unsigned ra mod 2 = 0)%Z ->
    evt BSEGS (m2s_post entry ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc (bv_unsigned a0) m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 entry) fc None m (seg_rom BSEGS)).

Ltac m2s_prep :=
  intros until m; intros M2C PRG K12 RA;
  destruct M2C as [C1 C4];
  lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ ?m _) =>
    pose proof (munch_refl ([] : list ivl) m) as MU;
    pose proof (wmono_refl BSEGS m) as WM;
    let a0 := eval vm_compute in (reg_get R 10) in
    pose proof (bv_unsigned_in_range 64 a0) as Ra0; unfold bv_modulus in Ra0
  end.
Ltac m2s_walk :=
  step; step; (* [comment removed for export] *)
  step; (* [comment removed for export] *)
  step; (* [comment removed for export] *)
  step; (* [comment removed for export] *)
  replace (v_sltu (Z_to_bv 64 ASAN_B) (Z_to_bv 64 2147450879)) with (Z_to_bv 64 0) by (vm_compute; reflexivity);
  step; (* [comment removed for export] *)
  step; (* [comment removed for export] *)
  step; (* [comment removed for export] *)
  if_not_taken;
  step; step; (* [comment removed for export] *)
  step; step; (* [comment removed for export] *)
  step; (* [comment removed for export] *)
  step; (* [comment removed for export] *)
  step; (* [comment removed for export] *)
  step; (* [comment removed for export] *)
  if_taken;
  step; step; (* [comment removed for export] *)
  step; (* [comment removed for export] *)
  step; (* [comment removed for export] *)
  step; (* [comment removed for export] *)
  step; (* [comment removed for export] *)
  if_not_taken;
  step; (* [comment removed for export] *)
  if_not_taken;
  step; (* [comment removed for export] *) shr3;
  step; (* [comment removed for export] *)
  step; (* [comment removed for export] *)
  unfold m2s_post; finish; try exact I.

(* [comment removed for export] *)
Ltac m2s_walk_low :=
  step; step; (* [comment removed for export] *)
  step; (* [comment removed for export] *)
  step; (* [comment removed for export] *)
  step; (* [comment removed for export] *)
  replace (v_sltu (Z_to_bv 64 ASAN_B) (Z_to_bv 64 2147450879)) with (Z_to_bv 64 0) by (vm_compute; reflexivity);
  step; (* [comment removed for export] *)
  step; (* [comment removed for export] *)
  step; (* [comment removed for export] *)
  if_taken;
  step; (* [comment removed for export] *) shr3;
  step; (* [comment removed for export] *)
  step; (* [comment removed for export] *)
  unfold m2s_post; finish; try exact I.

Lemma m2s_spec : m2s_stmt 0x4b690.
Proof. unfold m2s_stmt. m2s_prep. destruct K12 as [[K1 K2]|[K1 K2]]; [m2s_walk_low | m2s_walk]. Qed.

Lemma m2s_spec_d9c4c : m2s_stmt 0x63548.
Proof. unfold m2s_stmt. m2s_prep. destruct K12 as [[K1 K2]|[K1 K2]]; [m2s_walk_low | m2s_walk]. Qed.
End B_rt_m2s.

Local Ltac lia ::= lia_tc.  (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope bv_scope.

Notation BSEGS := AsanUbsan.M.loaded_segments.

(* [comment removed for export] *)
Definition W_ok_rt (v : rt_vals) (W : list ivl) : Prop :=
  Forall (fun iv => (IMG_END <= fst iv)%Z /\ (rt_disj v (fst iv) (snd iv) \/ (SH_LO <= fst iv /\ snd iv <= KHI))%Z) W.

Lemma disjoint_from_Forall : forall (P : ivl -> Prop) (W : list ivl) (A n : Z),
  Forall P W ->
  (forall lo hi, P (lo, hi)%Z -> (A + n <= lo \/ hi <= A)%Z) ->
  disjoint_from W A n.
Proof.
  intros P W A n HF HP. induction HF as [| [lo hi] W Hiv HF IH]; cbn; [exact I|].
  split; [| exact IH]. apply (HP lo hi). exact Hiv.
Qed.

Lemma rt_disj_sub : forall v lo hi lo' hi',
  rt_disj v lo hi -> (lo <= lo')%Z -> (hi' <= hi)%Z -> rt_disj v lo' hi'.
Proof. unfold rt_disj. intros v lo hi lo' hi' (A & B & C) H1 H2. repeat split; lia. Qed.

Lemma RT_transport : forall m m' v W,
  RT m v -> munch W m m' -> W_ok_rt v W -> RT m' v.
Proof.
  intros m m' v W RTH MU WOK.
  assert (DI : forall A n, (A + n <= IMG_END)%Z -> disjoint_from W A n).
  { intros A n HA. eapply disjoint_from_Forall; [exact WOK|]. cbn [fst snd]. intros lo hi [Hlo _]. lia. }
  pose proof RTH as RTX. unfold RT in RTX.
  destruct RTX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & _ & Ac & _ & At & _ & Ab & _)).
  unfold rt_app in Ac, At, Ab.
  assert (DC : disjoint_from W (rt_ctx v + 152) 8).
  { eapply disjoint_from_Forall; [exact WOK|]. cbn [fst snd]. unfold rt_disj. intros lo hi [_ [(H & _ & _)|[H1 H2]]]; lia. }
  assert (DT : disjoint_from W (rt_thr v + 48) 16).
  { eapply disjoint_from_Forall; [exact WOK|]. cbn [fst snd]. unfold rt_disj. intros lo hi [_ [(_ & H & _)|[H1 H2]]]; lia. }
  assert (DB : disjoint_from W (rt_blk v + 24) 8).
  { eapply disjoint_from_Forall; [exact WOK|]. cbn [fst snd]. unfold rt_disj. intros lo hi [_ [(_ & _ & H)|[H1 H2]]]; lia. }
  clear Ac At Ab.
  unfold RT in RTH |- *.
  destruct RTH as (RT1 & RT2 & RT2b & RT3 & RT4 & (fb & RT5 & Hfb) & RT6 & RT7 & RT8 & RT9 & RT10 & RT11 & RT12 & RT13 & RT14 & RTP).
  destruct RTP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14).
  repeat match goal with |- _ /\ _ => split end;
  try (eapply ro_cells_transport; [eassumption | exact MU | first [apply DI; cbn; lia | assumption]]);
  try (exists fb; split; [| exact Hfb]; eapply ro_cells_transport; [eassumption | exact MU | apply DI; cbn; lia]);
  first [ assumption | lia ].
Qed.

(* [comment removed for export] *)
Ltac open_RT RTH :=
  unfold RT in RTH;
  let fb := fresh "fb" in let Hfb := fresh "Hfb" in
  destruct RTH as (?RT1 & ?RT2 & ?RT2b & ?RT3 & ?RT4 & (fb & ?RT5 & Hfb) & ?RT6 & ?RT7 & ?RT8 & ?RT9 & ?RT10 & ?RT11 & ?RT12 & ?RT13 & ?RT14 & ?RTP).

Tactic Notation "open_RT_keep" hyp(RTH) :=
  let X := fresh "RTcopy" in
  pose proof RTH as X; unfold RT in X;
  destruct X as (RT1 & RT2 & RT2b & RT3 & RT4 & (fb & RT5 & Hfb) & RT6 & RT7 & RT8 & RT9 & RT10 & RT11 & RT12 & RT13 & RT14 & RTP).

Ltac close_RT :=
  lazymatch goal with
  | |- RT _ _ =>
      unfold RT; repeat match goal with |- _ /\ _ => split end;
      first [ eassumption | lia | eexists; split; [eassumption | first [assumption | lia]] | idtac ]
  end.

(* [comment removed for export] *)
Ltac solve_W_iv :=
  split; [ lia
         | lazymatch goal with
           | |- rt_disj _ ?lo _ \/ _ =>
               lazymatch lo with
               | context [2147450880%Z] => right; split; lia
               | _ => left; first [ match goal with H : rt_disj _ _ _ |- _ => eapply rt_disj_sub; [exact H | lia | lia] end
                                 | unfold rt_disj in *; repeat match goal with |- _ /\ _ => split end; lia ]
               end
           end ].
Ltac solve_W_rt :=
  unfold W_ok_rt; repeat (apply Forall_cons; [ cbn [fst snd]; solve_W_iv | ]); apply Forall_nil.
