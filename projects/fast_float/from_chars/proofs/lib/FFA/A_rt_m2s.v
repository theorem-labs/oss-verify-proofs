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
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFA Require Import A_rt_stmt.
From OSSVerify.fast_float.from_chars.images Require Import Asan.

Module A_memiszero.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFA Require Import A_rt_stmt.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
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

Notation ASEGS := Asan.M.loaded_segments.
Tactic Notation "show" string(tag) := match goal with |- ?g => idtac tag g end.

Notation A_MEMISZERO := 0x73970%Z.
Notation MIZ_NEED := 16%Z.

Definition memiszero_post
    (ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (a1 a2 a3 a4 a5 a6 : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ASEGS)
    /\ munch [(bv_unsigned sp - MIZ_NEED, bv_unsigned sp)]%Z m m'
    /\ wmono ASEGS m m'
    /\ stk ASEGS m' (bv_unsigned sp - MIZ_NEED) (bv_unsigned sp).

Definition memiszero_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    shz ASEGS m (bv_unsigned a0) (bv_unsigned a1) ->
    (0 < bv_unsigned a1 <= 2^40)%Z ->
    (bv_unsigned a0 + bv_unsigned a1 <= KHI)%Z ->
    stk ASEGS m (bv_unsigned sp - MIZ_NEED) (bv_unsigned sp) ->
    (KHI <= bv_unsigned sp - MIZ_NEED)%Z -> (bv_unsigned sp <= KTOP)%Z ->
    (bv_unsigned ra mod 2 = 0)%Z ->
    evt ASEGS (memiszero_post ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 A_MEMISZERO) fc None m (seg_rom ASEGS)).

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
  Hypothesis SH : shz ASEGS m1 b n.
  Hypothesis FR : rw_cells ASEGS m1 (bv_unsigned sp + -16) [CB 8 junk; C8 ra].
  Hypothesis ST : stk ASEGS m1 (bv_unsigned sp + -16) (bv_unsigned sp + -16).
  Hypothesis MU : munch [(bv_unsigned sp - MIZ_NEED, bv_unsigned sp)]%Z m m1.
  Hypothesis WM : wmono ASEGS m m1.
  Hypothesis SP1 : (KHI <= bv_unsigned sp - MIZ_NEED)%Z.
  Hypothesis SP2 : (bv_unsigned sp <= KTOP)%Z.
  Hypothesis RA : (bv_unsigned ra mod 2 = 0)%Z.

  Notation POST := (memiszero_post ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m).
  Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -16)).
  (* [comment removed for export] *)
  Notation ST8 xa0 xa2 xa3 xa5 xa6 pc :=
    (MS (mkR ra SP' gp tp t0 t1 t2 s0 s1 xa0 (Z_to_bv 64 0) xa2 xa3 (Z_to_bv 64 e) xa5 xa6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m1 (seg_rom ASEGS)).

  Ltac ranges := pose proof (bv_unsigned_in_range 64 sp) as Rsp; unfold bv_modulus in Rsp;
                 pose proof (shz_bound _ _ _ _ SH) as Bsh.

  (* [comment removed for export] *)
  #[using="b n ab ae junk SH FR ST MU WM"] Lemma fin : forall x10 x12 x13 x14 x15 x16,
    evt ASEGS POST
      (MS (mkR ra SP' gp tp t0 t1 t2 s0 s1 x10 (Z_to_bv 64 0) x12 x13 x14 x15 x16 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x739fc) fc None m1 (seg_rom ASEGS)).
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
      evt ASEGS POST
        (MS (mkR ra SP' gp tp t0 t1 t2 s0 s1 x10 (Z_to_bv 64 0) (Z_to_bv 64 r) x13 (Z_to_bv 64 (e - r)) x15 x16 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x739e8) fc None m1 (seg_rom ASEGS)).
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
    evt ASEGS POST (ST8 a0w (Z_to_bv 64 ae) x13 x15 x16 0x739dc).
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
      evt ASEGS POST (ST8 a0w (Z_to_bv 64 ae) x13 (Z_to_bv 64 w) x16 0x739cc).
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
    evt ASEGS POST (ST8 a0w (Z_to_bv 64 ae) x13 (Z_to_bv 64 ab) x16 0x739c8).
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
      evt ASEGS POST (ST8 a0w (Z_to_bv 64 ae) (Z_to_bv 64 (q + 1)) (Z_to_bv 64 ab) x16 0x739b0).
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
  pose proof (wmono_refl ASEGS m) as WM.
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
End A_memiszero.

Local Ltac lia ::= lia_tc.  (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation ASEGS := Asan.M.loaded_segments.

Definition m2s_cells (m : word -> option byte) : Prop :=
     ro_cells ASEGS m 937400 [C8 (Z_to_bv 64 ASAN_B); C4 (Z_to_bv 64 1)]
  /\ ro_cells ASEGS m 940704 [C8 (Z_to_bv 64 (KTOP - 1)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].

Lemma m2s_cells_of_RT : forall m v, RT m v -> m2s_cells m.
Proof. intros m v H. unfold RT in H. split; tauto. Qed.

Definition m2s_post (entry : Z)
    (ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (p : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 a2 a3 a4 a5 a6 a7 : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (ASAN_B + p / 8)) (Z_to_bv 64 ASAN_B) a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom ASEGS)
    /\ munch [] m m
    /\ wmono ASEGS m m
    /\ True.

Definition m2s_stmt (entry : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    m2s_cells m ->
    pristine m RELRO_LO RELRO_HI ->
    ((4096 <= bv_unsigned a0 /\ bv_unsigned a0 < SH_LO) \/ (KHI <= bv_unsigned a0 /\ bv_unsigned a0 < KTOP))%Z ->
    (bv_unsigned ra mod 2 = 0)%Z ->
    evt ASEGS (m2s_post entry ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc (bv_unsigned a0) m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 entry) fc None m (seg_rom ASEGS)).

Ltac m2s_prep :=
  intros until m; intros M2C PRG K12 RA;
  destruct M2C as [C1 C4];
  lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ ?m _) =>
    pose proof (munch_refl ([] : list ivl) m) as MU;
    pose proof (wmono_refl ASEGS m) as WM;
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

Lemma m2s_spec : m2s_stmt 0x4b200.
Proof. unfold m2s_stmt. m2s_prep. destruct K12 as [[K1 K2]|[K1 K2]]; [m2s_walk_low | m2s_walk]. Qed.

Lemma m2s_spec_d9950 : m2s_stmt 0x63554.
Proof. unfold m2s_stmt. m2s_prep. destruct K12 as [[K1 K2]|[K1 K2]]; [m2s_walk_low | m2s_walk]. Qed.
