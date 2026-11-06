(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Perf.   (* [comment removed for export] *)
From OSSVerify.Proofs.fast_float.from_chars.lib.FFA Require A_rt_stmt A_rt_m2s.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFA Require A_rt_m2s.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FFA.A_rt_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFA.A_rt_m2s OSSVerify.Proofs.fast_float.from_chars.lib.FFA.A_rt_m2s.A_memiszero.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
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
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation ASEGS := Asan.M.loaded_segments.
Tactic Notation "show" string(tag) := match goal with |- ?g => idtac tag g end.

Notation A_RPOISON := 0x639e0%Z.
Notation RP_NEED := 80%Z.     (* [comment removed for export] *)

Definition rpoison_post
    (ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 a1 a2 a3 a4 a5 a6 a7 : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ASEGS)
    /\ munch [(bv_unsigned sp - RP_NEED, bv_unsigned sp)]%Z m m'
    /\ wmono ASEGS m m'
    /\ stk ASEGS m' (bv_unsigned sp - RP_NEED) (bv_unsigned sp).

Definition rpoison_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    let p := bv_unsigned a0 in let n := bv_unsigned a1 in
    (0 < n <= 2^40)%Z ->
    ((IMG_END <= p /\ p + n + 8 <= SH_LO) \/ (KHI <= p /\ p + n + 8 <= KTOP))%Z ->
    shz ASEGS m (ASAN_B + p / 8) ((p + n - 1) / 8 - p / 8 + 1) ->
    m2s_cells m ->
    pristine m RELRO_LO RELRO_HI ->
    stk ASEGS m (bv_unsigned sp - RP_NEED) (bv_unsigned sp) ->
    (KHI <= bv_unsigned sp - RP_NEED)%Z -> (bv_unsigned sp <= KTOP)%Z ->
    (bv_unsigned ra mod 2 = 0)%Z ->
    evt ASEGS (rpoison_post ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 A_RPOISON) fc None m (seg_rom ASEGS)).

Section Proof.
  Hypothesis M2S : m2s_stmt 0x63554.
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
    shz ASEGS m (ASAN_B + p / 8) ((p + n - 1) / 8 - p / 8 + 1) -> m2s_cells m -> pristine m RELRO_LO RELRO_HI ->
    stk ASEGS m (bv_unsigned sp - RP_NEED) (bv_unsigned sp) -> (KHI <= bv_unsigned sp - RP_NEED)%Z -> (bv_unsigned sp <= KTOP)%Z ->
    (bv_unsigned ra mod 2 = 0)%Z ->
    evt ASEGS (rpoison_post ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 A_RPOISON) fc None m (seg_rom ASEGS)).
  Proof. LiaFast.lf_pins (fun (M2S MIZ : LiaFast.U) => LiaFast.u0).
    intros until m. cbv zeta. intros Hn K1 K2 SH M2C PRG ST SP1 SP2 RA.
    unfold rpoison_post.
    pose proof (munch_refl [(bv_unsigned sp - RP_NEED, bv_unsigned sp)]%Z m) as MU.
    pose proof (wmono_refl ASEGS m) as WM.
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
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => eapply evt_cut; [ eapply M2S | post_call ASEGS mc ] end.
    1:{ split; assumption. } 1:{ assumption. }
    1:{ rewrite unsigned_lit by lia. lia. }
    1:{ rewrite unsigned_lit by lia. reflexivity. }
    rewrite (unsigned_lit ab) by lia.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => eapply evt_cut; [ eapply M2S | post_call ASEGS mc ] end.
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
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => eapply evt_cut; [ eapply MIZ | post_call ASEGS mc ] end.
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
    shz ASEGS m (ASAN_B + p / 8) ((p + n - 1) / 8 - p / 8 + 1) -> m2s_cells m -> pristine m RELRO_LO RELRO_HI ->
    stk ASEGS m (bv_unsigned sp - RP_NEED) (bv_unsigned sp) -> (KHI <= bv_unsigned sp - RP_NEED)%Z -> (bv_unsigned sp <= KTOP)%Z ->
    (bv_unsigned ra mod 2 = 0)%Z ->
    evt ASEGS (rpoison_post ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 A_RPOISON) fc None m (seg_rom ASEGS)).
  Proof. LiaFast.lf_pins (fun (M2S MIZ : LiaFast.U) => LiaFast.u0).
    intros until m. cbv zeta. intros Hn K1 K2 SH M2C PRG ST SP1 SP2 RA.
    unfold rpoison_post.
    pose proof (munch_refl [(bv_unsigned sp - RP_NEED, bv_unsigned sp)]%Z m) as MU.
    pose proof (wmono_refl ASEGS m) as WM.
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
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => eapply evt_cut; [ eapply M2S | post_call ASEGS mc ] end.
    1:{ split; assumption. } 1:{ assumption. }
    1:{ rewrite unsigned_lit by lia. lia. }
    1:{ rewrite unsigned_lit by lia. reflexivity. }
    rewrite (unsigned_lit ab) by lia.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => eapply evt_cut; [ eapply M2S | post_call ASEGS mc ] end.
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
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => eapply evt_cut; [ eapply MIZ | post_call ASEGS mc ] end.
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
