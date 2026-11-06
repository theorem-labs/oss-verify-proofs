(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_rt_stmt.

Module B_rpoison.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Perf.   (* [comment removed for export] *)
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_rt_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_rt_lemmas.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_rt_lemmas.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_rt_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_rt_lemmas.B_rt_m2s OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_rt_lemmas.B_memiszero.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
Local Ltac lia ::= lia_tc.  (* [comment removed for export] *)
Local Ltac lia4 ::= first [ lia_t1 | lia_t2 | lia_d1 | lia_app2 | lia_t3 ].  (* [comment removed for export] *)
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

Notation B_RPOISON := 0x639d4%Z.
Notation RP_NEED := 80%Z.     (* [comment removed for export] *)

Definition rpoison_post
    (ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 a1 a2 a3 a4 a5 a6 a7 : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom BSEGS)
    /\ munch [(bv_unsigned sp - RP_NEED, bv_unsigned sp)]%Z m m'
    /\ wmono BSEGS m m'
    /\ stk BSEGS m' (bv_unsigned sp - RP_NEED) (bv_unsigned sp).

Definition rpoison_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    let p := bv_unsigned a0 in let n := bv_unsigned a1 in
    (0 < n <= 2^40)%Z ->
    ((IMG_END <= p /\ p + n + 8 <= SH_LO) \/ (KHI <= p /\ p + n + 8 <= KTOP))%Z ->
    shz BSEGS m (ASAN_B + p / 8) ((p + n - 1) / 8 - p / 8 + 1) ->
    m2s_cells m ->
    pristine m RELRO_LO RELRO_HI ->
    stk BSEGS m (bv_unsigned sp - RP_NEED) (bv_unsigned sp) ->
    (KHI <= bv_unsigned sp - RP_NEED)%Z -> (bv_unsigned sp <= KTOP)%Z ->
    (bv_unsigned ra mod 2 = 0)%Z ->
    evt BSEGS (rpoison_post ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 B_RPOISON) fc None m (seg_rom BSEGS)).

Section Proof.
  Hypothesis M2S : m2s_stmt 0x63548.
  Hypothesis MIZ : memiszero_stmt.

  (* [comment removed for export] *)
  Ltac fold_sltu_B :=
    replace (v_sltu (Z_to_bv 64 ASAN_B) (Z_to_bv 64 2147450879)) with (Z_to_bv 64 0) by (vm_compute; reflexivity).

  (* [comment removed for export] *)
  Ltac addr_is_in_mem :=
    step; (* [comment removed for export] *)
    idtac.

  #[using="M2S MIZ"] Lemma rpoison_spec_hi : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    let p := bv_unsigned a0 in let n := bv_unsigned a1 in
    (0 < n <= 2^40)%Z -> (KHI <= p)%Z -> (p + n + 8 <= KTOP)%Z ->
    shz BSEGS m (ASAN_B + p / 8) ((p + n - 1) / 8 - p / 8 + 1) -> m2s_cells m -> pristine m RELRO_LO RELRO_HI ->
    stk BSEGS m (bv_unsigned sp - RP_NEED) (bv_unsigned sp) -> (KHI <= bv_unsigned sp - RP_NEED)%Z -> (bv_unsigned sp <= KTOP)%Z ->
    (bv_unsigned ra mod 2 = 0)%Z ->
    evt BSEGS (rpoison_post ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 B_RPOISON) fc None m (seg_rom BSEGS)).
  Proof. LiaFast.lf_pins (fun (M2S MIZ : LiaFast.U) => LiaFast.u0).
    intros until m. cbv zeta. intros Hn K1 K2 SH M2C PRG ST SP1 SP2 RA.
    unfold rpoison_post.
    pose proof (munch_refl [(bv_unsigned sp - RP_NEED, bv_unsigned sp)]%Z m) as MU.
    pose proof (wmono_refl BSEGS m) as WM.
    pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
    pose proof (bv_unsigned_in_range 64 a0) as Ra0. unfold bv_modulus in Ra0.
    pose proof (bv_unsigned_in_range 64 a1) as Ra1. unfold bv_modulus in Ra1.
    pose proof (shz_bound _ _ _ _ SH) as Bsh.
    pose proof M2C as M2C'. destruct M2C' as [C1 C4].
    carve_frame 64%nat ST.
    do 8 step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_not_taken.
    step. step. (* [comment removed for export] *)
    step. step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *) fold_sltu_B.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_not_taken.
    step. step. step. step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_taken.
    step. step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_not_taken.
    step. (* [comment removed for export] *)
    if_not_taken.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_not_taken.
    step. step. step. step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_taken.
    step. step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_not_taken.
    step. (* [comment removed for export] *)
    if_not_taken.
    step. (* [comment removed for export] *)
    if_not_taken.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite (unsigned_lit (bv_unsigned a0 + 7)) by lia. rewrite (land_m8w (bv_unsigned a0 + 7)) by lia.
    step. (* [comment removed for export] *)
    rewrite (unsigned_lit (bv_unsigned a1 + bv_unsigned a0)) by lia. rewrite (land_m8w (bv_unsigned a1 + bv_unsigned a0)) by lia.
    set (ab := (bv_unsigned a0 + 7 - (bv_unsigned a0 + 7) mod 8)%Z) in *.
    set (ae := (bv_unsigned a1 + bv_unsigned a0 - (bv_unsigned a1 + bv_unsigned a0) mod 8)%Z) in *.
    assert (Hab : (ab mod 8 = 0 /\ bv_unsigned a0 <= ab <= bv_unsigned a0 + 7)%Z) by (subst ab; Z.div_mod_to_equations; lia).
    assert (Hae : (ae mod 8 = 0 /\ bv_unsigned a0 + bv_unsigned a1 - 8 < ae <= bv_unsigned a0 + bv_unsigned a1)%Z) by (subst ae; Z.div_mod_to_equations; lia).
    clearbody ab ae.
    step. (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => eapply evt_cut; [ eapply M2S | post_call BSEGS mc ] end.
    1:{ split; assumption. } 1:{ assumption. }
    1:{ rewrite unsigned_lit by lia. lia. }
    1:{ rewrite unsigned_lit by lia. reflexivity. }
    rewrite (unsigned_lit ab) by lia.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => eapply evt_cut; [ eapply M2S | post_call BSEGS mc ] end.
    1:{ split; assumption. } 1:{ assumption. }
    1:{ rewrite unsigned_lit by lia. lia. }
    1:{ rewrite unsigned_lit by lia. reflexivity. }
    rewrite (unsigned_lit ae) by lia.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *) shr3.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *) shr3.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hse.
    - (* [comment removed for export] *)
      clear Hse.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      do 8 step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      release_frame FR ST (bv_unsigned sp).
      finish.
    - cond_cleanup Hse.
      step. (* [comment removed for export] *)
      rewrite (unsigned_lit (ASAN_B + ae / 8)), (unsigned_lit (ASAN_B + ab / 8)) by lia.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      pose proof (unsigned_lit (bv_unsigned sp + -64) ltac:(lia)) as Usp.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => eapply evt_cut; [ eapply MIZ | post_call BSEGS mc ] end.
      1:{ rewrite !unsigned_lit by (Z.div_mod_to_equations; lia).
          eapply shz_sub; [eassumption | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia]. }
      1:{ rewrite !unsigned_lit by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations; lia. }
      1:{ rewrite !unsigned_lit by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations; lia. }
      1:{ rewrite Usp. replace (bv_unsigned sp + -64 - MIZ_NEED)%Z with (bv_unsigned sp + -80)%Z by lia. exact ST. }
      1:{ rewrite Usp. lia. } 1:{ rewrite Usp. lia. }
      1:{ rewrite unsigned_lit by lia. reflexivity. }
      rewrite ?Usp in *. clear Usp.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      do 8 step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      lazymatch goal with H : stk _ _ (bv_unsigned sp + -64 - MIZ_NEED)%Z _ |- _ =>
        replace (bv_unsigned sp + -64 - MIZ_NEED)%Z with (bv_unsigned sp + -80)%Z in H by lia; rename H into ST' end.
      release_frame FR ST' (bv_unsigned sp).
      finish.
  Qed.

  #[using="M2S MIZ"] Lemma rpoison_spec_lo : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    let p := bv_unsigned a0 in let n := bv_unsigned a1 in
    (0 < n <= 2^40)%Z -> (IMG_END <= p)%Z -> (p + n + 8 <= SH_LO)%Z ->
    shz BSEGS m (ASAN_B + p / 8) ((p + n - 1) / 8 - p / 8 + 1) -> m2s_cells m -> pristine m RELRO_LO RELRO_HI ->
    stk BSEGS m (bv_unsigned sp - RP_NEED) (bv_unsigned sp) -> (KHI <= bv_unsigned sp - RP_NEED)%Z -> (bv_unsigned sp <= KTOP)%Z ->
    (bv_unsigned ra mod 2 = 0)%Z ->
    evt BSEGS (rpoison_post ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 B_RPOISON) fc None m (seg_rom BSEGS)).
  Proof. LiaFast.lf_pins (fun (M2S MIZ : LiaFast.U) => LiaFast.u0).
    intros until m. cbv zeta. intros Hn K1 K2 SH M2C PRG ST SP1 SP2 RA.
    unfold rpoison_post.
    pose proof (munch_refl [(bv_unsigned sp - RP_NEED, bv_unsigned sp)]%Z m) as MU.
    pose proof (wmono_refl BSEGS m) as WM.
    pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
    pose proof (bv_unsigned_in_range 64 a0) as Ra0. unfold bv_modulus in Ra0.
    pose proof (bv_unsigned_in_range 64 a1) as Ra1. unfold bv_modulus in Ra1.
    pose proof (shz_bound _ _ _ _ SH) as Bsh.
    pose proof M2C as M2C'. destruct M2C' as [C1 C4].
    carve_frame 64%nat ST.
    do 8 step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_not_taken.
    step. step. (* [comment removed for export] *)
    step. step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *) fold_sltu_B.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_taken.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_taken.
    step. (* [comment removed for export] *)
    if_not_taken.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite (unsigned_lit (bv_unsigned a0 + 7)) by lia. rewrite (land_m8w (bv_unsigned a0 + 7)) by lia.
    step. (* [comment removed for export] *)
    rewrite (unsigned_lit (bv_unsigned a1 + bv_unsigned a0)) by lia. rewrite (land_m8w (bv_unsigned a1 + bv_unsigned a0)) by lia.
    set (ab := (bv_unsigned a0 + 7 - (bv_unsigned a0 + 7) mod 8)%Z) in *.
    set (ae := (bv_unsigned a1 + bv_unsigned a0 - (bv_unsigned a1 + bv_unsigned a0) mod 8)%Z) in *.
    assert (Hab : (ab mod 8 = 0 /\ bv_unsigned a0 <= ab <= bv_unsigned a0 + 7)%Z) by (subst ab; Z.div_mod_to_equations; lia).
    assert (Hae : (ae mod 8 = 0 /\ bv_unsigned a0 + bv_unsigned a1 - 8 < ae <= bv_unsigned a0 + bv_unsigned a1)%Z) by (subst ae; Z.div_mod_to_equations; lia).
    clearbody ab ae.
    step. (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => eapply evt_cut; [ eapply M2S | post_call BSEGS mc ] end.
    1:{ split; assumption. } 1:{ assumption. }
    1:{ rewrite unsigned_lit by lia. lia. }
    1:{ rewrite unsigned_lit by lia. reflexivity. }
    rewrite (unsigned_lit ab) by lia.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => eapply evt_cut; [ eapply M2S | post_call BSEGS mc ] end.
    1:{ split; assumption. } 1:{ assumption. }
    1:{ rewrite unsigned_lit by lia. lia. }
    1:{ rewrite unsigned_lit by lia. reflexivity. }
    rewrite (unsigned_lit ae) by lia.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *) shr3.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *) shr3.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hse.
    - (* [comment removed for export] *)
      clear Hse.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      do 8 step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      release_frame FR ST (bv_unsigned sp).
      finish.
    - cond_cleanup Hse.
      step. (* [comment removed for export] *)
      rewrite (unsigned_lit (ASAN_B + ae / 8)), (unsigned_lit (ASAN_B + ab / 8)) by lia.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      pose proof (unsigned_lit (bv_unsigned sp + -64) ltac:(lia)) as Usp.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => eapply evt_cut; [ eapply MIZ | post_call BSEGS mc ] end.
      1:{ rewrite !unsigned_lit by (Z.div_mod_to_equations; lia).
          eapply shz_sub; [eassumption | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia]. }
      1:{ rewrite !unsigned_lit by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations; lia. }
      1:{ rewrite !unsigned_lit by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations; lia. }
      1:{ rewrite Usp. replace (bv_unsigned sp + -64 - MIZ_NEED)%Z with (bv_unsigned sp + -80)%Z by lia. exact ST. }
      1:{ rewrite Usp. lia. } 1:{ rewrite Usp. lia. }
      1:{ rewrite unsigned_lit by lia. reflexivity. }
      rewrite ?Usp in *. clear Usp.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      do 8 step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      lazymatch goal with H : stk _ _ (bv_unsigned sp + -64 - MIZ_NEED)%Z _ |- _ =>
        replace (bv_unsigned sp + -64 - MIZ_NEED)%Z with (bv_unsigned sp + -80)%Z in H by lia; rename H into ST' end.
      release_frame FR ST' (bv_unsigned sp).
      finish.
  Qed.

  #[using="M2S MIZ"] Lemma rpoison_spec : rpoison_stmt.
  Proof. LiaFast.lf_pins (fun (M2S MIZ : LiaFast.U) => LiaFast.u0).
    unfold rpoison_stmt. intros until m. cbv zeta. intros Hn K12.
    destruct K12 as [[K1 K2]|[K1 K2]]; [exact (rpoison_spec_lo ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Hn K1 K2)
                                       | exact (rpoison_spec_hi ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Hn K1 K2)].
  Qed.
End Proof.
End B_rpoison.

From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_imemmove.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_shl_limbs.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_long_mul_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_pow10.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_shl_bits_stmt B_shl_limbs_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_rt_lemmas.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_rt_lemmas.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_shl_stmt B_pow5_stmt B_pow10_stmt B_nonzero_stmt B_hi64_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_hi64_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_positive_digit_comp_d_stmt B_positive_digit_comp_f_stmt.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_rt_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_D1_closed.B_rpoison OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_imemmove.B_imemmove_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_shl_limbs.B_asan_memmove2_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_long_mul_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_pow10.B_large_mul_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_shl_bits_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_shl_limbs_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_rt_lemmas.B_copy_bwd_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_rt_lemmas.B_copy_bwd_impl_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_shl_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_pow5_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_pow10_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_nonzero_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_hi64_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_hi64_stmt.B_ctlz_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_positive_digit_comp_d_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_positive_digit_comp_f_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_rt_lemmas.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_rt_lemmas.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_imemmove.

Module B_asan_memmove2.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Perf.   (* [comment removed for export] *)
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_rt_stmt B_rt_lemmas.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_rt_lemmas.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_rt_lemmas.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_imemmove.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_shl_limbs.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_rt_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_rt_lemmas OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_rt_lemmas.B_rt_m2s OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_rt_lemmas.B_memiszero OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_D1_closed.B_rpoison OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_imemmove.B_imemmove_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_shl_limbs.B_asan_memmove2_stmt.
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

(* [comment removed for export] *)
Ltac fold_snez0 :=
  replace (bv_unsigned (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 0))) with 0%Z by (vm_compute; reflexivity);
  rewrite Z.land_0_l.

(* [comment removed for export] *)
Lemma big65_true : forall x, (0 <= x < 2^64)%Z ->
  negb (bv_ltu (Z_to_bv 64 (-65)) (Z_to_bv 64 (x + -65))) = true -> (x = 0 \/ 65 <= x)%Z.
Proof.
  intros x Hx H. apply (proj1 (Bool.negb_true_iff _)) in H. unfold bv_ltu in H. apply Z.ltb_ge in H.
  rewrite !Z_to_bv_unsigned in H. unfold bv_wrap in H. change (bv_modulus 64) with (2^64)%Z in H.
  Z.div_mod_to_equations. lia.
Qed.
Lemma big65_false : forall x, (0 <= x < 2^64)%Z ->
  negb (bv_ltu (Z_to_bv 64 (-65)) (Z_to_bv 64 (x + -65))) = false -> (1 <= x <= 64)%Z.
Proof.
  intros x Hx H. apply (proj1 (Bool.negb_false_iff _)) in H. unfold bv_ltu in H. apply Z.ltb_lt in H.
  rewrite !Z_to_bv_unsigned in H. unfold bv_wrap in H. change (bv_modulus 64) with (2^64)%Z in H.
  Z.div_mod_to_equations. lia.
Qed.

Section Proof.
  Hypothesis RP : rpoison_stmt.
  Hypothesis IMM : imemmove_stmt.

  Section Tail.
    Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (d sr nw : word)
              (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs old : list byte) (shlo shn shlo2 shn2 : Z).
    Hypothesis LEN1 : length old = length bs.
    Hypothesis LEN2 : Z.of_nat (length bs) = bv_unsigned nw.
    Hypothesis KD1 : (app2r (bv_unsigned d) (bv_unsigned d + bv_unsigned nw + 8))%Z.
    Hypothesis KD2 : (bv_unsigned d + bv_unsigned nw + 8 <= KTOP)%Z.
    Hypothesis KS1 : (app2r (bv_unsigned sr) (bv_unsigned sr + bv_unsigned nw + 8))%Z.
    Hypothesis KS2 : (bv_unsigned sr + bv_unsigned nw + 8 <= KTOP)%Z.
    Hypothesis N40 : (bv_unsigned nw <= 2^40)%Z.
    Hypothesis RDL1 : (shlo + 8 <= ASAN_B + bv_unsigned d / 8)%Z.
    Hypothesis RDL2 : (ASAN_B + (bv_unsigned d + bv_unsigned nw) / 8 + 8 <= shlo + shn)%Z.
    Hypothesis RDL3 : (shlo2 + 8 <= ASAN_B + bv_unsigned sr / 8)%Z.
    Hypothesis RDL4 : (ASAN_B + (bv_unsigned sr + bv_unsigned nw) / 8 + 8 <= shlo2 + shn2)%Z.
    Hypothesis SP1 : (IMG_END <= bv_unsigned sp - IMEMMOVE_NEED)%Z.
    Hypothesis SP2 : (KHI <= bv_unsigned sp - IMEMMOVE_NEED)%Z.
    Hypothesis SP3 : (bv_unsigned sp <= KTOP)%Z.
    Hypothesis SEPD : (bv_unsigned sp <= bv_unsigned d \/ bv_unsigned d + bv_unsigned nw <= bv_unsigned sp - IMEMMOVE_NEED)%Z.
    Hypothesis SEPS : (bv_unsigned sp <= bv_unsigned sr \/ bv_unsigned sr + bv_unsigned nw <= bv_unsigned sp - IMEMMOVE_NEED)%Z.
    Hypothesis RA : (bv_unsigned ra mod 2 = 0)%Z.

    Notation POST := (asan_memmove_post ra sp gp tp s0 s1 d s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned nw) bs m).
    Notation FRC := [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
    Notation SPX := (Z_to_bv 64 (bv_unsigned sp + -2144)).
    Notation S0V := (Z_to_bv 64 (bv_unsigned sp + 0)).

    (* [comment removed for export] *)
    Definition cur (m' : word -> option byte) : Prop :=
         rw_cells BSEGS m' (bv_unsigned sp + -64) FRC
      /\ u8arr BSEGS m' (bv_unsigned d) old
      /\ bytes_at BSEGS m' (bv_unsigned sr) bs
      /\ stk BSEGS m' (bv_unsigned sp + -2224) (bv_unsigned sp + -64)
      /\ pristine m' RELRO_LO RELRO_HI /\ pristine m' REALTAB_LO REALTAB_HI
      /\ shz BSEGS m' (ASAN_B + bv_unsigned d / 8) ((bv_unsigned d + bv_unsigned nw - 1) / 8 - bv_unsigned d / 8 + 1)
      /\ shz BSEGS m' (ASAN_B + bv_unsigned sr / 8) ((bv_unsigned sr + bv_unsigned nw - 1) / 8 - bv_unsigned sr / 8 + 1)
      /\ rdbl BSEGS m' shlo shn
      /\ rdbl BSEGS m' shlo2 shn2
      /\ m2s_cells m'
      /\ munch (asan_memmove_W sp d (bv_unsigned nw)) m m' /\ wmono BSEGS m m'.

    Ltac open_cur H := destruct H as (FR & ARR & SRC & ST & PRG & PRT & SHD & SHS & RD & RDs & M2C & MU & WM);
                       pose proof M2C as M2C'; destruct M2C' as [C1 C4]; cbv delta [asan_memmove_W] in MU.
    Ltac close_cur := unfold cur; repeat match goal with |- _ /\ _ => split end; try assumption;
                      try (lazymatch goal with |- m2s_cells _ => split; assumption end).
    Ltac ranges :=
      pose proof (bv_unsigned_in_range 64 sp) as Rsp; unfold bv_modulus in Rsp;
      pose proof (bv_unsigned_in_range 64 d) as Rd; unfold bv_modulus in Rd;
      pose proof (bv_unsigned_in_range 64 sr) as Rsr; unfold bv_modulus in Rsr;
      pose proof (bv_unsigned_in_range 64 nw) as Rn; unfold bv_modulus in Rn.

    (* [comment removed for export] *)
    #[using="IMM LEN1 LEN2 KD1 KD2 KS1 KS2 N40 SP2 SP3 SEPD SEPS"] Lemma tail : forall (x1 x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31 : word) (m' : word -> option byte),
      cur m' ->
      evt BSEGS POST
        (MS (mkR x1 SPX gp tp x5 x6 x7 x8 x9 d sr nw x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x60964) fc None m' (seg_rom BSEGS)).
    Proof. LiaFast.lf_pins (fun (IMM LEN1 LEN2 KD1 KD2 KS1 KS2 N40 SP2 SP3 SEPD SEPS : LiaFast.U) => LiaFast.u0).
      intros until m'. intros CUR. open_cur CUR. ranges.
      step. (* [comment removed for export] *)
      call IMM.
      1:{ exact SRC. } 1:{ exact ARR. } 1:{ exact LEN1. } 1:{ exact LEN2. } 1:{ lia. } 1:{ lia. } 1:{ lia. }
      step. (* [comment removed for export] *)
      do 9 step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      release_frame FR ST (bv_unsigned sp).
      unfold asan_memmove_post. finish.
    Qed.

    (* [comment removed for export] *)
    Notation SHDF := (2147450880 + bv_unsigned d / 8)%Z.
    Notation SHDL := (2147450880 + (bv_unsigned d + bv_unsigned nw + -1) / 8)%Z.
    Definition dloop_ok (k : nat) : Prop :=
      forall (c : Z) (x1 x5 x6 x7 x8 x9 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31 : word) (m' : word -> option byte),
        (Z.to_nat (SHDL - c) <= k)%nat -> (SHDF <= c < SHDL)%Z -> (1 <= bv_unsigned nw)%Z -> cur m' ->
        evt BSEGS POST
          (MS (mkR x1 SPX gp tp x5 x6 x7 x8 x9 d sr nw (Z_to_bv 64 c) (Z_to_bv 64 SHDL) (Z_to_bv 64 0) x16 x17 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
              F (Z_to_bv 64 0x60b70) fc None m' (seg_rom BSEGS)).
    #[using="IMM LEN1 LEN2 KD1 KD2 KS1 KS2 N40 SP2 SP3 SEPD SEPS"] Lemma dloop : forall k, dloop_ok k.
    Proof. LiaFast.lf_pins (fun (IMM LEN1 LEN2 KD1 KD2 KS1 KS2 N40 SP2 SP3 SEPD SEPS : LiaFast.U) => LiaFast.u0).
      induction k as [|k IH]; unfold dloop_ok; intros until m'; intros Hk Hc Hn CUR; [lia|].
      pose proof CUR as CUR'. open_cur CUR'. ranges. pose proof (shz_bound _ _ _ _ SHD) as Bsh.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hb.
      - cond_cleanup Hb. eapply (IH (c + 1)%Z); try eassumption; lia.
      - cond_cleanup Hb.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        eapply tail; eassumption.
    Qed.

    (* [comment removed for export] *)
    #[using="RP IMM LEN1 LEN2 KD1 KD2 KS1 KS2 N40 RDL1 RDL2 SP1 SP2 SP3 SEPD SEPS"] Lemma from_dchk : forall (x1 x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x20 x21 x22 x28 x29 x30 x31 : word) (m' : word -> option byte),
      cur m' ->
      evt BSEGS POST
        (MS (mkR x1 SPX gp tp x5 x6 x7 x8 x9 d sr nw x13 x14 x15 x16 x17 x18
                 (Z_to_bv 64 (bv_unsigned nw + -65)) x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x60918) fc None m' (seg_rom BSEGS)).
    Proof. LiaFast.lf_pins (fun (RP IMM LEN1 LEN2 KD1 KD2 KS1 KS2 N40 RDL1 RDL2 SP1 SP2 SP3 SEPD SEPS : LiaFast.U) => LiaFast.u0).
      intros until m'. intros CUR. pose proof CUR as CUR'. open_cur CUR'. ranges. pose proof (shz_bound _ _ _ _ SHD) as Bsh.
      pose proof RD as RD'. destruct RD' as (Brd1 & Brd2 & _).
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hov. { exfalso. cond_cleanup Hov. rewrite ?zb_lxor_ones in Hov by lia. lia. } clear Hov.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hbig.
      - (* [comment removed for export] *)
        apply big65_true in Hbig; [ | lia ].
        step. (* [comment removed for export] *)
        if_cases Hz.
        + cond_cleanup Hz.
          step. step. step. step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          match goal with H : stk _ ?mc ?lo (bv_unsigned sp + -64) |- _ =>
            destruct (stk_split BSEGS mc _ (bv_unsigned sp + -2144) _ H ltac:(lia)) as [STlo SThi]; clear H end.
          pose proof (unsigned_lit (bv_unsigned sp + -2144) ltac:(lia)) as Usp.
          call RP.
          1:{ rewrite ?unsigned_lit by lia. Z.div_mod_to_equations. lia. }
          1:{ rewrite ?unsigned_lit by lia. lia. }
          1:{ exact SHD. }
          1:{ exact M2C. } 1:{ exact PRG. }
          1:{ rewrite Usp. replace (bv_unsigned sp + -2144 - 80)%Z with (bv_unsigned sp + -2224)%Z by lia. exact STlo. }
          1:{ rewrite Usp. lia. } 1:{ rewrite Usp. lia. }
          1:{ rewrite unsigned_lit by lia. reflexivity. }
          clear Usp.
          step. step. step. step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          match goal with H1 : stk _ ?mc ?lo (bv_unsigned sp + -2144), H2 : stk _ ?mc (bv_unsigned sp + -2144) _ |- _ =>
            pose proof (stk_merge BSEGS mc _ _ _ H1 H2 ltac:(lia)) as ST'; clear H1 H2;
            replace lo with (bv_unsigned sp + -2224)%Z in ST' by lia end.
          eapply tail. close_cur.
        + (* [comment removed for export] *)
          cond_cleanup Hz.
          step. (* [comment removed for export] *)
          eapply tail. exact CUR.
      - (* [comment removed for export] *)
        apply big65_false in Hbig; [ | lia ]. rename Hbig into Hn.
        step. step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *) shr3.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *) shr3.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        rewrite (unsigned_lit SHDF) by lia. rewrite (land_m8w SHDF) by lia.
        step. (* [comment removed for export] *)
        rewrite (unsigned_lit SHDL) by (Z.div_mod_to_equations; lia). rewrite (land_m8w SHDL) by (Z.div_mod_to_equations; lia).
        assert (Hsh : (ASAN_B <= SHDF <= SHDL /\ SHDL <= KHI)%Z) by (Z.div_mod_to_equations; lia).
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
          destruct (rdbl_read BSEGS mc shlo shn (SHDF - SHDF mod 8)%Z 8 RD ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia)) as (w1 & Lw1 & R1) end.
        step. (* [comment removed for export] *)
        clear R1.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
          destruct (rdbl_read BSEGS mc shlo shn (SHDL - SHDL mod 8)%Z 8 RD ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia)) as (w2 & Lw2 & R2) end.
        step. (* [comment removed for export] *)
        clear R2.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases Hq.
        + clear Hq.
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          fold_snez0.
          step. (* [comment removed for export] *)
          if_cases Hge.
          * cond_cleanup Hge.
            step. (* [comment removed for export] *)
            step. (* [comment removed for export] *)
            eapply tail. exact CUR.
          * cond_cleanup Hge.
            eapply (dloop (Z.to_nat (SHDL - SHDF)) SHDF); try eassumption; try lia.
        + clear Hq. eapply tail. exact CUR.
    Qed.

    (* [comment removed for export] *)
    Notation SHSF := (2147450880 + bv_unsigned sr / 8)%Z.
    Notation SHSL := (2147450880 + (bv_unsigned sr + bv_unsigned nw + -1) / 8)%Z.
    Definition sloop_ok (k : nat) : Prop :=
      forall (c : Z) (x1 x5 x6 x7 x8 x9 x16 x17 x18 x20 x21 x22 x28 x29 x30 x31 : word) (m' : word -> option byte),
        (Z.to_nat (SHSL - c) <= k)%nat -> (SHSF <= c < SHSL)%Z -> (1 <= bv_unsigned nw)%Z -> cur m' ->
        evt BSEGS POST
          (MS (mkR x1 SPX gp tp x5 x6 x7 x8 x9 d sr nw (Z_to_bv 64 c) (Z_to_bv 64 SHSL) (Z_to_bv 64 0) x16 x17 x18
                   (Z_to_bv 64 (bv_unsigned nw + -65)) x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
              F (Z_to_bv 64 0x60acc) fc None m' (seg_rom BSEGS)).
    #[using="RP IMM LEN1 LEN2 KD1 KD2 KS1 KS2 N40 RDL1 RDL2 SP1 SP2 SP3 SEPD SEPS"] Lemma sloop : forall k, sloop_ok k.
    Proof. LiaFast.lf_pins (fun (RP IMM LEN1 LEN2 KD1 KD2 KS1 KS2 N40 RDL1 RDL2 SP1 SP2 SP3 SEPD SEPS : LiaFast.U) => LiaFast.u0).
      induction k as [|k IH]; unfold sloop_ok; intros until m'; intros Hk Hc Hn CUR; [lia|].
      pose proof CUR as CUR'. open_cur CUR'. ranges. pose proof (shz_bound _ _ _ _ SHS) as Bsh.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hb.
      - cond_cleanup Hb. eapply (IH (c + 1)%Z); try eassumption; lia.
      - cond_cleanup Hb.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        eapply from_dchk; eassumption.
    Qed.
  End Tail.

  Ltac prove_cur :=
    try (progress unfold cur; repeat match goal with |- _ /\ _ => split end;
         first [ eassumption | split; eassumption | idtac ]).

  #[using="RP IMM"] Lemma asan_memmove2_spec : asan_memmove2_stmt.
  Proof. LiaFast.lf_pins (fun (RP IMM : LiaFast.U) => LiaFast.u0).
    unfold asan_memmove2_stmt. intros until shn2.
    intros SRC ARR LEN1 LEN2 ALD ALS ALN KD1 KD2 KS1 KS2 N40 SHD SHS RD RDL1 RDL2 RDs RDL3 RDL4 ST SP1 SP2 SP3 AL16 SEPD SEPS PRG PRT RTH RDJ1 RDJ2 RA.
    pose proof (munch_refl (asan_memmove_W sp a0 (bv_unsigned a2)) m) as MU.
    pose proof (wmono_refl BSEGS m) as WM.
    pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
    pose proof (bv_unsigned_in_range 64 a0) as Ra0. unfold bv_modulus in Ra0.
    pose proof (bv_unsigned_in_range 64 a1) as Ra1. unfold bv_modulus in Ra1.
    pose proof (bv_unsigned_in_range 64 a2) as Ra2. unfold bv_modulus in Ra2.
    pose proof RDs as RD'. destruct RD' as (Brd1 & Brd2 & _).
    open_RT_keep RTH.
    destruct RTP as (Hbeg & Hblk & Hblk1 & Hctx & Hthr & HFS1 & HFS2 & HFS3 & Hc1 & Hc2 & Ht1 & Ht2 & Hb1 & Hb2).
    clear RT2 RT2b RT5 RT6 RT7 RT8 RT9 RT10 RT11 RT12 RT13 RT14 Hfb fb.
    cbv delta [asan_memmove_W] in MU.
    (* [comment removed for export] *)
    replace (bv_unsigned a2 / 8)%Z with ((bv_unsigned a0 + bv_unsigned a2 - 1) / 8 - bv_unsigned a0 / 8 + 1)%Z in SHD
      by (Z.div_mod_to_equations; lia).
    replace (bv_unsigned a2 / 8)%Z with ((bv_unsigned a1 + bv_unsigned a2 - 1) / 8 - bv_unsigned a1 / 8 + 1)%Z in SHS
      by (Z.div_mod_to_equations; lia).
    pose proof (shz_bound _ _ _ _ SHS) as Bsh.
    carve_frame 64%nat ST.
    do 9 step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hov. { exfalso. cond_cleanup Hov. rewrite ?zb_lxor_ones in Hov by lia. lia. } clear Hov.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    match goal with H : stk _ _ ?lo (bv_unsigned sp + -64) |- _ => replace lo with (bv_unsigned sp + -2224)%Z in H by lia end.
    step. (* [comment removed for export] *)
    if_cases Hbig.
    - (* [comment removed for export] *)
      apply big65_true in Hbig; [ | lia ].
      step. (* [comment removed for export] *)
      if_cases Hz.
      + cond_cleanup Hz.
        do 5 step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        match goal with H : stk _ ?mc ?lo (bv_unsigned sp + -64) |- _ =>
          destruct (stk_split BSEGS mc _ (bv_unsigned sp + -2144) _ H ltac:(lia)) as [STlo SThi]; clear H end.
        pose proof (unsigned_lit (bv_unsigned sp + -2144) ltac:(lia)) as Usp.
        call RP.
        1:{ rewrite ?unsigned_lit by lia. Z.div_mod_to_equations. lia. }
        1:{ rewrite ?unsigned_lit by lia. lia. }
        1:{ exact SHS. }
        1:{ split; assumption. } 1:{ exact PRG. }
        1:{ rewrite Usp. replace (bv_unsigned sp + -2144 - 80)%Z with (bv_unsigned sp + -2224)%Z by lia. exact STlo. }
        1:{ rewrite Usp. lia. } 1:{ rewrite Usp. lia. }
        1:{ rewrite unsigned_lit by lia. reflexivity. }
        clear Usp.
        step. step. step. step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        match goal with H1 : stk _ ?mc ?lo (bv_unsigned sp + -2144), H2 : stk _ ?mc (bv_unsigned sp + -2144) _ |- _ =>
          pose proof (stk_merge BSEGS mc _ _ _ H1 H2 ltac:(lia)) as ST'; clear H1 H2;
          replace lo with (bv_unsigned sp + -2224)%Z in ST' by lia end.
        eapply (@from_dchk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 a2 F fc m bs old shlo shn shlo2 shn2); try eassumption; try lia.
        all: prove_cur.
      + cond_cleanup Hz.
        step. (* [comment removed for export] *)
        eapply (@from_dchk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 a2 F fc m bs old shlo shn shlo2 shn2); try eassumption; try lia.
        all: prove_cur.
    - (* [comment removed for export] *)
      apply big65_false in Hbig; [ | lia ]. rename Hbig into Hn.
      step. step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *) shr3.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *) shr3.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      rewrite (unsigned_lit (2147450880 + bv_unsigned a1 / 8)) by lia. rewrite (land_m8w (2147450880 + bv_unsigned a1 / 8)) by lia.
      step. (* [comment removed for export] *)
      rewrite (unsigned_lit (2147450880 + (bv_unsigned a1 + bv_unsigned a2 + -1) / 8)) by (Z.div_mod_to_equations; lia).
      rewrite (land_m8w (2147450880 + (bv_unsigned a1 + bv_unsigned a2 + -1) / 8)) by (Z.div_mod_to_equations; lia).
      assert (Hsh : (ASAN_B <= 2147450880 + bv_unsigned a1 / 8 <= 2147450880 + (bv_unsigned a1 + bv_unsigned a2 + -1) / 8
                     /\ 2147450880 + (bv_unsigned a1 + bv_unsigned a2 + -1) / 8 <= KHI)%Z) by (Z.div_mod_to_equations; lia).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
        destruct (rdbl_read BSEGS mc shlo2 shn2 (2147450880 + bv_unsigned a1 / 8 - (2147450880 + bv_unsigned a1 / 8) mod 8)%Z 8 RDs
                    ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia)) as (w1 & Lw1 & R1) end.
      step. (* [comment removed for export] *)
      clear R1.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
        destruct (rdbl_read BSEGS mc shlo2 shn2 (2147450880 + (bv_unsigned a1 + bv_unsigned a2 + -1) / 8
                                              - (2147450880 + (bv_unsigned a1 + bv_unsigned a2 + -1) / 8) mod 8)%Z 8 RDs
                    ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia)) as (w2 & Lw2 & R2) end.
      step. (* [comment removed for export] *)
      clear R2.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hq.
      + clear Hq.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        fold_snez0.
        step. (* [comment removed for export] *)
        if_cases Hge.
        * cond_cleanup Hge.
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          eapply (@from_dchk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 a2 F fc m bs old shlo shn shlo2 shn2); try eassumption; try lia.
          all: prove_cur.
        * cond_cleanup Hge.
          eapply (@sloop ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 a2 F fc m bs old shlo shn shlo2 shn2)
            with (k := Z.to_nat ((2147450880 + (bv_unsigned a1 + bv_unsigned a2 + -1) / 8) - (2147450880 + bv_unsigned a1 / 8)))
                 (c := (2147450880 + bv_unsigned a1 / 8)%Z); try eassumption; try lia.
          all: prove_cur.
      + clear Hq.
        eapply (@from_dchk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 a2 F fc m bs old shlo shn shlo2 shn2); try eassumption; try lia.
        all: prove_cur.
  Qed.
End Proof.
End B_asan_memmove2.

From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_shl_bits.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_shl_limbs.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_shl_limbs.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_shl_limbs B_shl B_nonzero B_hi64.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_positive_digit_comp_d.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_pow10.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_pow10.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_pow10 B_positive_digit_comp_d B_positive_digit_comp_f.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition B_rpoison_closed : rpoison_stmt :=
  B_rpoison.rpoison_spec OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_rt_lemmas.B_rt_m2s.m2s_spec_d9c4c OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_rt_lemmas.B_memiszero.memiszero_spec.
Definition B_asan_memmove2_closed : asan_memmove2_stmt :=
  B_asan_memmove2.asan_memmove2_spec B_rpoison_closed B_imemmove.imemmove_spec.
Definition B_shl_closed : shl_stmt :=
  B_shl.shl_spec B_shl_bits.shl_bits_spec
    (B_shl_limbs.shl_limbs_spec (OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_shl_limbs.B_copy_bwd.copy_bwd_spec (OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_shl_limbs.B_copy_bwd_impl.copy_bwd_impl_spec B_asan_memmove2_closed))).
Definition B_hi64_closed : hi64_stmt := B_hi64.hi64_spec B_nonzero.nonzero_spec.

Section WithLongMul.
  Hypothesis long_mul_spec : long_mul_stmt.
  Definition B_large_mul_closed : large_mul_stmt := OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_pow10.B_large_mul.large_mul_spec long_mul_spec.
  Definition B_pow5_closed : pow5_stmt := OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_pow10.B_pow5.pow5_spec B_large_mul_closed.
  Definition B_pow10_closed : pow10_stmt := B_pow10.pow10_spec B_pow5_closed B_shl_closed.
  Definition B_pos_dc_d_closed : positive_digit_comp_d_stmt :=
    B_positive_digit_comp_d.positive_digit_comp_d_spec B_pow10_closed B_hi64_closed OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_positive_digit_comp_d.B_ctlz.ctlz_spec.
  Definition B_pos_dc_f_closed : positive_digit_comp_f_stmt :=
    B_positive_digit_comp_f.positive_digit_comp_f_spec B_pow10_closed B_hi64_closed OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_positive_digit_comp_d.B_ctlz.ctlz_spec.
End WithLongMul.
