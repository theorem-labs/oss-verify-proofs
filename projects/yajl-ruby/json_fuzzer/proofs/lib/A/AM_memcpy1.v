(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import AM_strw.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA AImages.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import AM_kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
(* [comment removed for export] *)

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition memcpy_entry := 0x9dcdc%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition memcpy_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 a2 : word) (src : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) src]
    /\ bytes_at asegs m' (bv_unsigned a1) src.

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (src : list byte).
  Notation S := (bv_unsigned a1).
  Notation D := (bv_unsigned a0).
  Notation n := (bv_unsigned a2).
  Notation W := [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z.
  Hypothesis LEN : length src = Z.to_nat n.
  Hypothesis AB : (0 <= S /\ S + n <= 2^64 /\ 0 <= D /\ D + n <= 2^64 /\ 0 <= n < 2^64)%Z.
  Hypothesis SEP : (S + n <= D \/ D + n <= S)%Z.
  (* [comment removed for export] *)
  Variable Pol : acc -> Prop.
  Hypothesis PSRC : forall a k, (bv_unsigned a1 <= a)%Z -> (a + Z.of_nat k <= bv_unsigned a1 + bv_unsigned a2)%Z -> Pol (Z_to_bv 64 a, k).
  Hypothesis PDST : forall a k, (bv_unsigned a0 <= a)%Z -> (a + Z.of_nat k <= bv_unsigned a0 + bv_unsigned a2)%Z -> Pol (Z_to_bv 64 a, k).

  Notation POST := (memcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 src m).
  (* [comment removed for export] *)
  Notation ST pc mm x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 :=
    (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 a0 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition INV (m1 : word -> option byte) (bs : list byte) (P : Z) : Prop :=
    bytes_at asegs m1 S src /\ u8arr asegs m1 D bs /\ copied src bs (Z.to_nat P) /\
    mem_inv asegs m1 /\ munch W m m1 /\ wmono asegs m m1.

  Ltac open_inv H := destruct H as (SRC & DST & CP & MI & MU & WM).
  Ltac inv_tac :=
    lazymatch goal with
    | |- INV _ _ _ => split; [eassumption | split; [eassumption | split; [ | repeat split; eassumption ]]];
        lazymatch goal with CP : copied _ _ (Z.to_nat ?P) |- copied _ _ (Z.to_nat ?P') =>
          first [ exact CP | replace (Z.to_nat P') with (Z.to_nat P) by lia; exact CP ] end
    end.

  (* [comment removed for export] *)
  Ltac fin :=
    lazymatch goal with
    | DST : u8arr _ ?m1 _ ?bs, CP : copied _ ?bs (Z.to_nat ?P) |- _ =>
        let E := fresh "E" in
        pose proof (copied_all _ _ _ CP ltac:(lia)) as E; rewrite E in DST; clear E CP;
        apply rw_cells_of_u8arr in DST; rewrite LEN in DST
    end;
    finishA2.

  (* [comment removed for export] *)
  Tactic Notation "use" uconstr(L) :=
    eapply L; first [ inv_tac | idtac ]; try (f_equal; lia); try lia;
    try (rewrite ?unsigned_lit by lia; Z.div_mod_to_equations; lia);
    try (rewrite ?Z.add_0_r, ?Z.sub_0_r; symmetry; apply Z_to_bv_bv_unsigned).

  (* [comment removed for export] *)
  Lemma mc_a8c : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
    INV m1 bs P -> (0 <= P)%Z -> (P + bv_unsigned r mod 4 = n)%Z ->
    xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
    evtA asegs Pol POST (ST 0x9e09c m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
  Proof using AB LEN SEP PSRC PDST.
    intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
    pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
    zstep. rewrite land_bit_2 by lia.
    zstep. if_cases K2; zify_cond K2.
    - (* [comment removed for export] *)
      destruct (Z.ltb_spec0 (bv_unsigned r mod 4) 2) as [Hl4|Hl4]; [exfalso; cbn in K2; lia|]; apply (proj1 (Z.nlt_ge _ _)) in Hl4.
      window P 2%nat HW.
      ld1 HW 0%nat. ld1 HW 1%nat. zstep. zstep.
      st1 HW 0%nat. st1 HW 1%nat.
      zstep. zstep. rewrite land_1.
      zstep. if_cases K1; zify_cond K1.
      + zstep. fin.
      + window (P + 2)%Z 1%nat HW1.
        ld1 HW1 0%nat. st1 HW1 0%nat. zstep. fin.
    - destruct (Z.ltb_spec0 (bv_unsigned r mod 4) 2) as [Hl4|Hl4]; [|exfalso; cbn in K2; lia].
      zstep. rewrite land_1.
      zstep. if_cases K1; zify_cond K1.
      + window P 1%nat HW. ld1 HW 0%nat. st1 HW 0%nat. zstep. fin.
      + zstep. fin.
  Qed.

  (* [comment removed for export] *)
  Lemma mc_a60 : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
    INV m1 bs P -> (0 <= P)%Z -> (P + 4 + bv_unsigned r mod 4 = n)%Z ->
    xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
    evtA asegs Pol POST (ST 0x9e070 m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
  Proof using AB LEN SEP PSRC PDST.
    intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
    pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
    window P 4%nat HW.
    ld1 HW 0%nat. ld1 HW 1%nat. ld1 HW 2%nat. ld1 HW 3%nat. zstep. zstep.
    st1 HW 0%nat. st1 HW 1%nat. st1 HW 2%nat. st1 HW 3%nat. zstep.
    use (mc_a8c _ _ (P + 4)%Z).
  Qed.

  (* [comment removed for export] *)
  Lemma mc_a58 : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
    INV m1 bs P -> (0 <= P)%Z -> (P + bv_unsigned r mod 8 = n)%Z ->
    xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
    evtA asegs Pol POST (ST 0x9e068 m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
  Proof using AB LEN SEP PSRC PDST.
    intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
    pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
    zstep. rewrite land_bit_4 by lia.
    zstep. if_cases K; zify_cond K; destruct (Z.ltb_spec0 (bv_unsigned r mod 8) 4) as [Hl|Hl]; try (exfalso; cbn in K; lia); try (lazymatch type of Hl with not _ => apply (proj1 (Z.nlt_ge _ _)) in Hl end).
    - use (mc_a8c m1 bs P).
    - use (mc_a60 m1 bs P).
  Qed.

  (* [comment removed for export] *)
  Lemma mc_a0c : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
    INV m1 bs P -> (0 <= P)%Z -> (P + 8 + bv_unsigned r mod 8 = n)%Z ->
    xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
    evtA asegs Pol POST (ST 0x9e01c m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
  Proof using AB LEN SEP PSRC PDST.
    intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
    pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
    window P 8%nat HW.
    ld1 HW 0%nat. ld1 HW 1%nat. ld1 HW 2%nat. ld1 HW 3%nat. ld1 HW 4%nat. ld1 HW 5%nat. ld1 HW 6%nat. ld1 HW 7%nat.
    zstep.
    st1 HW 0%nat. st1 HW 1%nat. st1 HW 2%nat. st1 HW 3%nat. zstep.
    st1 HW 4%nat. st1 HW 5%nat. st1 HW 6%nat. st1 HW 7%nat. zstep.
    use (mc_a58 _ _ (P + 8)%Z).
  Qed.

  (* [comment removed for export] *)
  Lemma mc_734 : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
    INV m1 bs P -> (0 <= P)%Z -> (P + bv_unsigned r mod 8 = n)%Z ->
    xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
    evtA asegs Pol POST (ST 0x9dd44 m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
  Proof using AB LEN SEP PSRC PDST.
    intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
    pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
    zstep. rewrite land_bit_4 by lia.
    zstep. if_cases K; zify_cond K; destruct (Z.ltb_spec0 (bv_unsigned r mod 8) 4) as [Hl|Hl]; try (exfalso; cbn in K; lia); try (lazymatch type of Hl with not _ => apply (proj1 (Z.nlt_ge _ _)) in Hl end).
    - use (mc_a60 m1 bs P).
    - zstep. use (mc_a8c m1 bs P).
  Qed.

  (* [comment removed for export] *)
  Lemma mc_a04 : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
    INV m1 bs P -> (0 <= P)%Z -> (P + bv_unsigned r mod 16 = n)%Z ->
    xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
    evtA asegs Pol POST (ST 0x9e014 m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
  Proof using AB LEN SEP PSRC PDST.
    intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
    pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
    zstep. rewrite land_bit_8 by lia.
    zstep. if_cases K; zify_cond K; destruct (Z.ltb_spec0 (bv_unsigned r mod 16) 8) as [Hl|Hl]; try (exfalso; cbn in K; lia); try (lazymatch type of Hl with not _ => apply (proj1 (Z.nlt_ge _ _)) in Hl end).
    - use (mc_734 m1 bs P).
    - use (mc_a0c m1 bs P).
  Qed.

  (* [comment removed for export] *)
  Lemma mc_72c : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
    INV m1 bs P -> (0 <= P)%Z -> (P + bv_unsigned r mod 16 = n)%Z ->
    xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
    evtA asegs Pol POST (ST 0x9dd3c m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
  Proof using AB LEN SEP PSRC PDST.
    intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
    pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
    zstep. rewrite land_bit_8 by lia.
    zstep. if_cases K; zify_cond K; destruct (Z.ltb_spec0 (bv_unsigned r mod 16) 8) as [Hl|Hl]; try (exfalso; cbn in K; lia); try (lazymatch type of Hl with not _ => apply (proj1 (Z.nlt_ge _ _)) in Hl end).
    - use (mc_a0c m1 bs P).
    - use (mc_734 m1 bs P).
  Qed.

  (* [comment removed for export] *)
  Lemma mc_978 : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
    INV m1 bs P -> (0 <= P)%Z -> (P + 16 + bv_unsigned r mod 16 = n)%Z ->
    xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
    evtA asegs Pol POST (ST 0x9df88 m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
  Proof using AB LEN SEP PSRC PDST.
    intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
    pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
    window P 16%nat HW.
    ld1 HW 0%nat. ld1 HW 1%nat. ld1 HW 2%nat. ld1 HW 3%nat. ld1 HW 4%nat. ld1 HW 5%nat. ld1 HW 6%nat. ld1 HW 7%nat.
    st1 HW 0%nat. st1 HW 1%nat. st1 HW 2%nat. st1 HW 3%nat.
    ld1 HW 8%nat. ld1 HW 9%nat. ld1 HW 10%nat. ld1 HW 11%nat.
    st1 HW 4%nat. st1 HW 5%nat. st1 HW 6%nat. st1 HW 7%nat.
    ld1 HW 12%nat. ld1 HW 13%nat. ld1 HW 14%nat. ld1 HW 15%nat.
    zstep.
    st1 HW 8%nat. st1 HW 9%nat. st1 HW 10%nat. st1 HW 11%nat.
    zstep.
    st1 HW 12%nat. st1 HW 13%nat. st1 HW 14%nat. st1 HW 15%nat.
    zstep.
    use (mc_a04 _ _ (P + 16)%Z).
  Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma mc_848 : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
    INV m1 bs P -> (0 <= P)%Z -> (P + bv_unsigned r mod 8 = n)%Z ->
    xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
    evtA asegs Pol POST (ST 0x9de58 m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
  Proof using AB LEN SEP PSRC PDST.
    intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
    pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
    zstep. rewrite land_bit_4 by lia.
    zstep. if_cases K; zify_cond K; destruct (Z.ltb_spec0 (bv_unsigned r mod 8) 4) as [Hl|Hl]; try (exfalso; cbn in K; lia); try (lazymatch type of Hl with not _ => apply (proj1 (Z.nlt_ge _ _)) in Hl end).
    - use (mc_a8c m1 bs P).
    - window P 4%nat HW. ld4 HW 0%nat q0. zstep. st4 HW 0%nat. zstep. zstep.
      use (mc_a8c _ _ (P + 4)%Z).
  Qed.

  (* [comment removed for export] *)
  Lemma mc_828 : forall m1 bs (P r : Z) xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
    INV m1 bs P -> (0 <= P)%Z -> (P + r = n)%Z -> (0 <= r < 16)%Z ->
    xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 r -> xa3 = Z_to_bv 64 (D + P) ->
    evtA asegs Pol POST (ST 0x9de38 m1 x5 x6 x7 xa1 xa2 xa3 x14 x15 x16 x17 x28).
  Proof using AB LEN SEP PSRC PDST.
    intros m1 bs P r xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr Rr -> -> ->; open_inv I.
    zstep. zstep. if_cases K8; zify_cond K8.
    - use (mc_848 m1 bs P (Z_to_bv 64 r)).
    - window P 8%nat HW. ld4 HW 0%nat q0. ld4 HW 4%nat q1. st4 HW 0%nat. st4 HW 4%nat. zstep. zstep.
      use (mc_848 _ _ (P + 8)%Z (Z_to_bv 64 r)).
  Qed.

  (* [comment removed for export] *)
  Lemma mc_7f8 : forall (K : nat) m1 bs (P : Z) xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28,
    Z.to_nat (n - P) = K -> INV m1 bs P -> (0 <= P)%Z -> (16 <= n - P)%Z ->
    xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
    evtA asegs Pol POST (ST 0x9de08 m1 x5 x6 x7 xa1 xa2 xa3 (Z_to_bv 64 15) x15 x16 x17 x28).
  Proof using AB LEN SEP PSRC PDST.
    induction K as [K IH] using lt_wf_ind;
      intros m1 bs P xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28 HK I HP Hr -> -> ->; open_inv I.
    window P 16%nat HW.
    ld4 HW 0%nat q0. ld4 HW 4%nat q1. ld4 HW 8%nat q2. ld4 HW 12%nat q3.
    zstep. zstep.
    st4 HW 0%nat. st4 HW 4%nat. st4 HW 8%nat. st4 HW 12%nat.
    zstep. zstep. if_cases Kl; zify_cond Kl.
    - use (IH (Z.to_nat (n - (P + 16))) ltac:(lia) _ _ (P + 16)%Z).
    - use (mc_828 _ _ (P + 16)%Z (n - (P + 16))%Z).
  Qed.

  (* [comment removed for export] *)
  Lemma mc_7ec : forall m1 bs (P : Z) xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
    INV m1 bs P -> (0 <= P <= n)%Z ->
    xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
    evtA asegs Pol POST (ST 0x9ddfc m1 x5 x6 x7 xa1 xa2 xa3 x14 x15 x16 x17 x28).
  Proof using AB LEN SEP PSRC PDST.
    intros m1 bs P xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP -> -> ->; open_inv I.
    zstep. zstep. if_cases K16; zify_cond K16.
    - use (mc_828 m1 bs P (n - P)%Z).
    - zstep. use (mc_7f8 (Z.to_nat (n - P)) m1 bs P).
  Qed.

  (* [comment removed for export] *)
  Notation LW w := (sext 64 (bv_extract 0 32 (le_bytes_to_word w))).

  (* [comment removed for export] *)
  Lemma mc_770 : forall (K : nat) m1 bs (P : Z) (w : list byte) xa1 xa2 xa3 x5 x6 x7 x16 x17 x28,
    Z.to_nat (n - P) = K -> INV m1 bs P -> (2 <= P)%Z -> (18 <= n - P)%Z ->
    w = firstn 4 (skipn (Z.to_nat (P - 2)) src) ->
    xa1 = Z_to_bv 64 (S + P + 14) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
    evtA asegs Pol POST (ST 0x9dd80 m1 x5 x6 x7 xa1 xa2 xa3 (LW w) (Z_to_bv 64 17) x16 x17 x28).
  Proof using AB LEN SEP PSRC PDST.
    induction K as [K IH] using lt_wf_ind;
      intros m1 bs P w xa1 xa2 xa3 x5 x6 x7 x16 x17 x28 HK I HP Hr Hw -> -> ->; open_inv I.
    window (P - 2)%Z 20%nat HW.
    pose proof (window_sub src _ (P - 2)%Z 20 0 4 (P - 2)%Z HW ltac:(lia) ltac:(lia) ltac:(lia)) as Ew.
    cbn [firstn skipn] in Ew. rewrite <- Hw in Ew. clear Hw.
    assert (Lw : length w = 4%nat) by (rewrite Ew; reflexivity).
    zstep.
    ld4 HW 4%nat q1. ld4 HW 8%nat q2. ld4 HW 12%nat q3. ld4 HW 16%nat q4.
    do 11 zstep. zstep.
    st HW 2%nat 4%nat ltac:(by_le 16%Z). st HW 6%nat 4%nat ltac:(by_le 16%Z).
    st HW 10%nat 4%nat ltac:(by_le 16%Z). st HW 14%nat 4%nat ltac:(by_le 16%Z).
    zstep. zstep. zstep. if_cases Kl; zify_cond Kl.
    - use (IH (Z.to_nat (n - (P + 16))) ltac:(lia) _ _ (P + 16)%Z q4). by_win HW 16%nat.
    - zstep. zstep. zstep. if_cases K16; zify_cond K16.
      + use (mc_72c _ _ (P + 16)%Z).
      + zstep. use (mc_978 _ _ (P + 16)%Z).
  Qed.

End Proofs.
End RC__1.
