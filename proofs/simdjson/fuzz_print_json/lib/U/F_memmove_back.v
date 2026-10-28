(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Str_tac Sj_num_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import F_memcpy F_memmove_t2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Definition right1_bytes (src : list byte) (bl : byte) : list byte := nth 0 src bl :: src.

Lemma right1_bytes_length : forall src bl, length (right1_bytes src bl) = S (length src).
Proof. reflexivity. Qed.

Definition memmove_right1_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (S : Z) (src : list byte) (bl : byte) : machine_state -> Prop :=
  fun ms' => exists x5 x6 x7 xa1 xa2 xa3 xa4 xa5 xa6 xa7 x28 x29 x30 x31 m',
    ms' = MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 (S + 1)) xa1 xa2 xa3 xa4 xa5 xa6 xa7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(S + 1, S + 1 + Z.of_nat (length src))]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ u8arr usegs m' S (right1_bytes src bl).

Section Right1.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S : Z) (src : list byte) (bl : byte).
  Notation n := (Z.of_nat (length src)).
  Notation W := [(S + 1, S + 1 + n)]%Z.
  Notation POST := (memmove_right1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m S src bl).

  Hypothesis ARR : u8arr usegs m S (src ++ [bl]).
  Hypothesis MI : mem_inv usegs m.
  Hypothesis HN2 : (2 <= n)%Z.
  Hypothesis HN : (n < 2^62)%Z.
  Hypothesis HS2 : (S + n + 1 <= 2^64)%Z.

  Notation ST pc mm xa1 xa2 xa3 xa4 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (S + 1)) xa1 xa2 xa3 xa4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  Definition RINV (i : Z) (mm : word -> option byte) : Prop :=
    exists bs, u8arr usegs mm S bs /\ length bs = Datatypes.S (length src)
      /\ (forall j, (j <= length src - Z.to_nat i)%nat -> nth_error bs j = nth_error (src ++ [bl]) j)
      /\ (forall j, (length src - Z.to_nat i < j)%nat -> (j <= length src)%nat -> nth_error bs j = nth_error src (j - 1))
      /\ mem_inv usegs mm /\ munch W m mm /\ wmono usegs m mm.

  Lemma RINV0 : RINV 0 m.
  Proof using ARR MI HN2.
    exists (src ++ [bl]). split; [exact ARR|]. split; [rewrite length_app; cbn [length]; lia|].
    split; [intros; reflexivity|]. split; [intros j H1 H2; cbn in H1; lia|].
    split; [exact MI|]. split; [apply munch_refl | apply wmono_refl].
  Qed.

  Lemma RINV_fin : forall mm, RINV n mm -> u8arr usegs mm S (right1_bytes src bl) /\ mem_inv usegs mm /\ munch W m mm /\ wmono usegs m mm.
  Proof using HN2.
    intros mm (bs & UA & L & P1 & P2 & MI' & MU & WM). split; [|tauto].
    replace (right1_bytes src bl) with bs; [exact UA|].
    apply (nth_ext bs (right1_bytes src bl) bl bl); [rewrite right1_bytes_length; exact L|].
    intros j Hj. unfold right1_bytes.
    destruct j as [|j].
    - cbn [nth]. apply nth_error_nth. rewrite (P1 0%nat) by lia.
      rewrite nth_error_app1 by lia. apply nth_error_nth'. lia.
    - cbn [nth]. apply nth_error_nth. rewrite (P2 (Datatypes.S j)) by lia.
      replace (Datatypes.S j - 1)%nat with j by lia. apply nth_error_nth'. lia.
  Qed.

  Lemma mm_BB : forall (f : nat) (i : Z) xa4 mm,
    RINV i mm -> (0 <= i < n)%Z -> (n - i <= Z.of_nat f)%Z -> (0 <= S)%Z ->
    evt usegs POST (ST 0xd02f0 mm (Z_to_bv 64 (S + n - 1 - i)) (Z_to_bv 64 (i - n)) (Z_to_bv 64 (S + n - i)) xa4).
  Proof using HN HN2 HS2.
    induction f as [|f IH]; intros i xa4 mm INV Hi Hf S0; [exfalso; lia|].
    destruct INV as (bs & UA & L & P1 & P2 & MI' & MU & WM).

    destruct (nth_error src (Z.to_nat (n - 1 - i))) as [b|] eqn:EB; [|apply nth_error_None in EB; lia].
    assert (EBS : nth_error bs (Z.to_nat (n - 1 - i)) = Some b).
    { rewrite (P1 (Z.to_nat (n - 1 - i))) by lia. rewrite nth_error_app1 by lia. exact EB. }
    assert (RD : ov_read_bytes usegs mm (wa (S + (n - 1 - i))) 1 = Some [b]).
    { eapply u8arr_read; [exact UA | exact EBS | lia | reflexivity]. }
    replace (wa (S + (n - 1 - i))) with (Z_to_bv 64 (S + n - 1 - i)) in RD by (unfold wa; f_equal; lia).
    zstep. zstep.
    u8_store UA (n - i)%Z 1%nat.
    replace (le1 (Z_to_bv 64 (bv_unsigned b))) with [b] in UA by (symmetry; apply le1_zxb).
    num_cur_mem ltac:(fun mm' => assert (NEXT : RINV (i + 1) mm')).
    { exists (upd_bytes bs (Z.to_nat (n - i)) [b]). split; [exact UA|].
      assert (LU : length (upd_bytes bs (Z.to_nat (n - i)) [b]) = Datatypes.S (length src))
        by (rewrite upd_bytes_length by (cbn [length]; lia); exact L).
      split; [exact LU|]. split; [|split; [|split; [assumption| split; assumption]]].
      * intros j Hj. rewrite upd_bytes_nth by (cbn [length]; lia). cbn [length].
        replace (Nat.leb (Z.to_nat (n - i)) j && Nat.ltb j (Z.to_nat (n - i) + 1))%bool with false.
        2:{ symmetry. destruct (Nat.leb_spec0 (Z.to_nat (n - i)) j); [|reflexivity]. exfalso. lia. }
        apply P1. lia.
      * intros j Hj1 Hj2. rewrite upd_bytes_nth by (cbn [length]; lia). cbn [length].
        destruct (Nat.eq_dec j (Z.to_nat (n - i))) as [->|NE].
        -- replace (Nat.leb (Z.to_nat (n - i)) (Z.to_nat (n - i)) && Nat.ltb (Z.to_nat (n - i)) (Z.to_nat (n - i) + 1))%bool with true
             by (symmetry; apply andb_true_intro; split; [apply Nat.leb_refl | apply Nat.ltb_lt; lia]).
           rewrite Nat.sub_diag. cbn [nth_error].
           replace (Z.to_nat (n - i) - 1)%nat with (Z.to_nat (n - 1 - i)) by lia. symmetry. exact EB.
        -- replace (Nat.leb (Z.to_nat (n - i)) j && Nat.ltb j (Z.to_nat (n - i) + 1))%bool with false.
           2:{ symmetry. destruct (Nat.leb_spec0 (Z.to_nat (n - i)) j); [|reflexivity]. cbn [andb]. apply Nat.ltb_ge. lia. }
           apply P2; lia. }
    zstep. zstep.
    zstep. if_cases K; zify_cond K.
    -
      eapply evt_eq; [| eapply (IH (i + 1)%Z); [exact NEXT | Z.div_mod_to_equations; lia | lia | lia]].
      num_st_eq.
    -
      assert (EI : (i + 1 = n)%Z) by (Z.div_mod_to_equations; lia).
      rewrite EI in NEXT.
      destruct (RINV_fin _ NEXT) as (UA' & MI2 & MU2 & WM2).
      zstep.
      apply evt_done. unfold memmove_right1_post.
      do 15 eexists. split; [reflexivity|]. split; [exact MU2|]. split; [exact WM2|]. split; [exact MI2| exact UA'].
  Qed.

  Lemma memmove_right1_body :
    evt usegs POST (ST 0xd027c m (Z_to_bv 64 S) (Z_to_bv 64 n) a3 a4).
  Proof using ARR MI HN HN2 HS2.
    pose proof (u8arr_bound _ _ _ _ ARR) as AB. rewrite length_app in AB. cbn [length] in AB.
    pose proof RINV0 as INV.
    zstep. if_cases K0; zify_cond K0; [exfalso; Z.div_mod_to_equations; lia|].
    zstep. zstep. zstep. zstep.
    zstep. if_cases K; zify_cond K; rewrite Z.shiftl_mul_pow2 in K by lia; change (2 ^ 1)%Z with 2%Z in K.
    { exfalso. Z.div_mod_to_equations. lia. }
    zstep. zstep.
    zstep. if_cases KB; zify_cond KB; [|exfalso; Z.div_mod_to_equations; lia].
    zstep. if_cases KA; zify_cond KA.
    { exfalso. rewrite Z.lxor_comm in KA. exact (xor_succ_land7_nz S ltac:(lia) KA). }
    zstep.
    zstep. if_cases KZ; zify_cond KZ; [exfalso; Z.div_mod_to_equations; lia|].
    zstep. zstep. zstep. zstep.
    eapply evt_eq; [| eapply (mm_BB (length src) 0%Z); [exact INV | lia | lia | lia]].
    num_st_eq.
  Qed.
End Right1.

Lemma memmove_right1_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (S : Z) (src : list byte) (bl : byte),
  a0 = Z_to_bv 64 (S + 1) -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 (Z.of_nat (length src)) ->
  u8arr usegs m S (src ++ [bl]) -> mem_inv usegs m ->
  (2 <= Z.of_nat (length src))%Z -> (Z.of_nat (length src) < 2^62)%Z -> (S + Z.of_nat (length src) + 1 <= 2^64)%Z ->
  evt usegs (memmove_right1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m S src bl)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 MEMMOVE_T2) fc None m (seg_rom usegs)).
Proof.
  intros until bl. intros -> -> -> ARR MI HN2 HN HS2. unfold MEMMOVE_T2.
  exact (memmove_right1_body ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m S src bl ARR MI HN2 HN HS2).
Qed.
