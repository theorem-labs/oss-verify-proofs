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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA AImages.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import AM_kit AI_shadow.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.lf_ceil_hook.   (* [comment removed for export] *)
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition mem_is_zero_entry : Z := 0x6594c.

(* [comment removed for export] *)
Lemma firstn8_zero : forall (ws : list byte) (k : nat),
  (forall j, (j < 8)%nat -> nth_error ws (k + j)%nat = Some (Z_to_bv 8 0)) ->
  firstn 8 (skipn k ws) = repeat (Z_to_bv 8 0) 8.
Proof.
  intros ws k H. apply nth_error_ext. intros i.
  rewrite nth_error_firstn, nth_error_skipn.
  destruct (Nat.ltb_spec i 8).
  - rewrite H by lia. symmetry. apply nth_error_repeat. lia.
  - symmetry. apply (proj2 (nth_error_None _ _)). rewrite repeat_length. lia.
Qed.

Lemma load8_zero : bv_extract 0 64 (le_bytes_to_word (repeat (Z_to_bv 8 0) 8)) = Z_to_bv 64 0.
Proof. vm_compute. reflexivity. Qed.

Definition mem_is_zero_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp).

Section Walk.
Variable P : acc -> Prop.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
          (F : bvmap 5 word) (fc : bv 32) (m : mem) (B N WLO : Z) (ws : list byte) (lo : Z).
Hypothesis LOC : (Z.max 0x7fff80000000 (Z.min 0x800000000000 rc_sp) - 8388608) <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 16.
Hypothesis HN : 1 <= N <= 2^40.
Hypothesis HB : 0 <= WLO <= B.
Hypothesis HBN : B + N <= WLO + Z.of_nat (length ws).
Hypothesis HW64 : WLO + Z.of_nat (length ws) < 2^46.
Hypothesis ZB : forall i, B <= i < B + N -> nth_error ws (Z.to_nat (i - WLO)) = Some (Z_to_bv 8 0).
Hypothesis PSTK : forall a k, bv_unsigned sp - 16 <= a -> a + Z.of_nat k <= bv_unsigned sp -> P (Z_to_bv 64 a, k).
Hypothesis PRNG : forall a k, B <= a -> a + Z.of_nat k <= B + N -> P (Z_to_bv 64 a, k).

Notation POST := (mem_is_zero_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo).
Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -16)).
Notation AB := (al8 (B + 7)).       (* [comment removed for export] *)
Notation AE := (al8 (B + N)).       (* [comment removed for export] *)
Notation ST pc mm x10 x11 x12 x13 x14 x15 x16 :=
  (MS (mkR ra SP' gp tp t0 t1 t2 s0 s1 x10 x11 x12 x13 x14 x15 x16 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

Lemma AB_facts : B <= AB < B + 8 /\ AB mod 8 = 0 /\ AE <= B + N /\ B + N - 8 < AE /\ AE mod 8 = 0.
Proof.
  pose proof (al8_le (B + 7)). pose proof (al8_gt (B + 7)). pose proof (al8_mod (B + 7)).
  pose proof (al8_le (B + N)). pose proof (al8_gt (B + N)). pose proof (al8_mod (B + N)). lia.
Qed.

(* [comment removed for export] *)
Lemma zb_read : forall mm i a, bytes_at asegs mm WLO ws -> B <= i < B + N -> a = wa (WLO + (i - WLO)) ->
  ov_read_bytes asegs mm a 1 = Some [Z_to_bv 8 0].
Proof.
  intros mm i a WB Hi ->. eapply (u8ro_read asegs mm WLO ws (i - WLO)); [exact WB | apply ZB; lia | lia | reflexivity].
Qed.

(* [comment removed for export] *)
Lemma zw_read : forall mm q, bytes_at asegs mm WLO ws -> B <= q -> q + 8 <= B + N ->
  ov_read_bytes asegs mm (wa (WLO + (q - WLO))) 8 = Some (repeat (Z_to_bv 8 0) 8).
Proof.
  intros mm q WB H1 H2.
  rewrite (bytes_at_read asegs mm WLO ws (q - WLO) 8 WB ltac:(lia) ltac:(lia)).
  f_equal. apply firstn8_zero. intros j Hj.
  replace (Z.to_nat (q - WLO) + j)%nat with (Z.to_nat (q + Z.of_nat j - WLO)) by lia. apply ZB. lia.
Qed.

(* [comment removed for export] *)
Lemma miz_l3 : forall k (Q : machine_state -> Prop) mm cur x10 x13 x15 x16,
  Z.to_nat (B + N - cur) = k -> B <= cur < B + N -> bytes_at asegs mm WLO ws ->
  (forall x10' x12' x14', evtA asegs P Q (ST 0x659d8 mm x10' (Z_to_bv 64 0) x12' x13 x14' x15 x16)) ->
  evtA asegs P Q (ST 0x659c4 mm x10 (Z_to_bv 64 0) (Z_to_bv 64 cur) x13 (Z_to_bv 64 (B + N - cur)) x15 x16).
Proof.
  induction k as [|k IH]; intros Q mm cur x10 x13 x15 x16 Hk Hc WB CONT; [lia|].
  pose proof (zb_read mm cur (Z_to_bv 64 cur) WB ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
  zstepA. clear RD. (* [comment removed for export] *)
  zstepA. zstepA. zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *) if_cases K; zify_cond K.
  - replace (B + N - cur + -1) with (B + N - (cur + 1)) by lia. eapply IH; try lia; try assumption.
  - apply CONT.
Qed.

(* [comment removed for export] *)
Lemma miz_from_424c : forall mm j8 x13 x15 x16,
  mem_inv asegs mm -> munch [(bv_unsigned sp - 16, bv_unsigned sp)] m mm -> wmono asegs m mm ->
  stk asegs mm lo (bv_unsigned sp + -16) ->
  rw_cells asegs mm (bv_unsigned sp + -16) [CB 8 j8; C8 ra] ->
  bytes_at asegs mm WLO ws ->
  evtA asegs P POST (ST 0x659b8 mm (Z_to_bv 64 B) (Z_to_bv 64 0) (Z_to_bv 64 AE) x13 (Z_to_bv 64 (B + N)) x15 x16).
Proof.
  intros mm j8 x13 x15 x16 MI MU WM SK FR WB. pose proof AB_facts as ABF.
  assert (FIN : forall x10' x12' x14', evtA asegs P POST (ST 0x659d8 mm x10' (Z_to_bv 64 0) x12' x13 x14' x15 x16)).
  { intros x10' x12' x14'. zstepA. (* [comment removed for export] *) stepA. (* [comment removed for export] *) stepA. (* [comment removed for export] *) stepA. (* [comment removed for export] *)
    release_frame FR SK (bv_unsigned sp). finishA. }
  zstepA. (* [comment removed for export] *) if_cases K1; zify_cond K1. { apply FIN. }
  zstepA. (* [comment removed for export] *) if_cases K2; zify_cond K2. { apply FIN. }
  zstepA. (* [comment removed for export] *)
  eapply (miz_l3 (Z.to_nat (B + N - AE))); [reflexivity | lia | exact WB | exact FIN].
Qed.

(* [comment removed for export] *)
Lemma miz_l2 : forall k mm j8 cur x13 x16,
  Z.to_nat (AE - cur) = k -> AB <= cur < AE -> cur mod 8 = 0 ->
  mem_inv asegs mm -> munch [(bv_unsigned sp - 16, bv_unsigned sp)] m mm -> wmono asegs m mm ->
  stk asegs mm lo (bv_unsigned sp + -16) ->
  rw_cells asegs mm (bv_unsigned sp + -16) [CB 8 j8; C8 ra] ->
  bytes_at asegs mm WLO ws ->
  evtA asegs P POST (ST 0x659a8 mm (Z_to_bv 64 B) (Z_to_bv 64 0) (Z_to_bv 64 AE) x13 (Z_to_bv 64 (B + N)) (Z_to_bv 64 cur) x16).
Proof.
  induction k as [k IH] using lt_wf_ind; intros mm j8 cur x13 x16 Hk Hc Hal MI MU WM SK FR WB.
  pose proof AB_facts as ABF.
  assert (cur + 8 <= AE) by (Z.div_mod_to_equations; lia).
  pose proof (zw_read mm cur WB ltac:(lia) ltac:(lia)) as RD.
  replace (WLO + (cur - WLO)) with cur in RD by lia.
  stepA. clear RD. rewrite load8_zero. (* [comment removed for export] *)
  zstepA. zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *) if_cases K; zify_cond K.
  - eapply (IH (Z.to_nat (AE - (cur + 8)))); try eassumption; try lia.
    all: rewrite <- Zplus_mod_idemp_l, Hal; reflexivity.
  - replace (cur + 8) with AE by lia. eapply miz_from_424c; eassumption.
Qed.

(* [comment removed for export] *)
Lemma miz_from_4238 : forall mm j8 x13 x16,
  mem_inv asegs mm -> munch [(bv_unsigned sp - 16, bv_unsigned sp)] m mm -> wmono asegs m mm ->
  stk asegs mm lo (bv_unsigned sp + -16) ->
  rw_cells asegs mm (bv_unsigned sp + -16) [CB 8 j8; C8 ra] ->
  bytes_at asegs mm WLO ws ->
  evtA asegs P POST (ST 0x659a4 mm (Z_to_bv 64 B) (Z_to_bv 64 0) (Z_to_bv 64 AE) x13 (Z_to_bv 64 (B + N)) (Z_to_bv 64 AB) x16).
Proof.
  intros mm j8 x13 x16 MI MU WM SK FR WB. pose proof AB_facts as ABF.
  zstepA. (* [comment removed for export] *) if_cases K; zify_cond K.
  - (* [comment removed for export] *)
    (* [comment removed for export] *)
    eapply miz_from_424c; eassumption.
  - eapply (miz_l2 (Z.to_nat (AE - AB))); try eassumption; try lia.
Qed.

(* [comment removed for export] *)
Lemma miz_l1 : forall k mm j8 i x16,
  Z.to_nat (AB - (B + i)) = k -> 0 <= i -> B + i < AB -> B + i < B + N ->
  mem_inv asegs mm -> munch [(bv_unsigned sp - 16, bv_unsigned sp)] m mm -> wmono asegs m mm ->
  stk asegs mm lo (bv_unsigned sp + -16) ->
  rw_cells asegs mm (bv_unsigned sp + -16) [CB 8 j8; C8 ra] ->
  bytes_at asegs mm WLO ws ->
  evtA asegs P POST (ST 0x6598c mm (Z_to_bv 64 B) (Z_to_bv 64 0) (Z_to_bv 64 AE) (Z_to_bv 64 (B + i + 1)) (Z_to_bv 64 (B + N)) (Z_to_bv 64 AB) x16).
Proof.
  induction k as [|k IH]; intros mm j8 i x16 Hk Hi H1 H2 MI MU WM SK FR WB; pose proof AB_facts as ABF; [lia|].
  zstepA. (* [comment removed for export] *)
  pose proof (zb_read mm (B + i) (Z_to_bv 64 (B + i + 1 + -1)) WB ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
  zstepA. clear RD. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *) if_cases K1; zify_cond K1.
  { eapply miz_from_4238; eassumption. }
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *) if_cases K2; zify_cond K2.
  - replace (B + i + 2) with (B + (i + 1) + 1) by lia. eapply IH; try eassumption; try lia.
  - (* [comment removed for export] *) eapply miz_from_4238; eassumption.
Qed.

Lemma mem_is_zero_body : forall x10 x11 x12 x13 x14 x15 x16,
  stk asegs m lo (bv_unsigned sp) -> mem_inv asegs m -> bytes_at asegs m WLO ws ->
  x10 = Z_to_bv 64 B -> x11 = Z_to_bv 64 N ->
  evtA asegs P POST
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 x11 x12 x13 x14 x15 x16 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 mem_is_zero_entry) fc None m (seg_rom asegs)).
Proof.
  intros until x16. intros SK MI WB -> ->. unfold mem_is_zero_entry. pose proof AB_facts as ABF.
  assert (MU : munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m) by apply munch_refl.
  assert (WM : wmono asegs m m) by apply wmono_refl.
  carve_frame 16%nat SK.
  stepA. stepA. (* [comment removed for export] *)
  zstepA. zstepA. zstepA. zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *) if_cases K0; zify_cond K0. { exfalso. revert K0. cbn. lia. }
  zstepA. zstepA. zstepA. zstepA. zstepA. (* [comment removed for export] *)
  rewrite ?land_m8, ?land_m8' by lia.
  zstepA. (* [comment removed for export] *) if_cases K1; zify_cond K1.
  { (* [comment removed for export] *) eapply miz_from_4238; eassumption. }
  zstepA. (* [comment removed for export] *) if_cases K2; zify_cond K2. { exfalso. lia. }
  zstepA. zstepA. (* [comment removed for export] *)
  replace (B + 1) with (B + 0 + 1) by lia.
  eapply (miz_l1 (Z.to_nat (AB - (B + 0)))); try eassumption; try lia.
Qed.
End Walk.

Lemma mem_is_zero_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (B N WLO : Z) (ws : list byte) (lo : Z) (P : acc -> Prop),
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 16 -> mem_inv asegs m ->
  a0 = Z_to_bv 64 B -> a1 = Z_to_bv 64 N -> 1 <= N <= 2^40 ->
  bytes_at asegs m WLO ws -> 0 <= WLO <= B -> B + N <= WLO + Z.of_nat (length ws) -> WLO + Z.of_nat (length ws) < 2^46 ->
  (forall i, B <= i < B + N -> nth_error ws (Z.to_nat (i - WLO)) = Some (Z_to_bv 8 0)) ->
  (forall a k, bv_unsigned sp - 16 <= a -> a + Z.of_nat k <= bv_unsigned sp -> P (Z_to_bv 64 a, k)) ->
  (forall a k, B <= a -> a + Z.of_nat k <= B + N -> P (Z_to_bv 64 a, k)) ->
  evtA asegs P (mem_is_zero_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 mem_is_zero_entry) fc None m (seg_rom asegs)).
Proof.
  intros until P. intros ST LOC LO MI HA0 HA1 HN WB HB HBN HW ZB PSTK PRNG.
  unfold alloc_ceiling, sp_window_lo, stack_max_size in LOC.
  eapply mem_is_zero_body; eassumption.
Qed.
End RC__1.
