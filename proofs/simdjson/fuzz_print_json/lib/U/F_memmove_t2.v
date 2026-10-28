(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Str_tac Sj_num_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import F_memcpy.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Definition MEMMOVE_T2 : Z := 0xd027c.

Section Far.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (D S n : Z) (src junk : list byte).

  Lemma memmove_far_body :
    bytes_at usegs m S src ->
    length src = Z.to_nat n ->
    rw_cells usegs m D [CB (Z.to_nat n) junk] ->
    (S + n <= D \/ D + n <= S)%Z -> (1 <= n < 2^64)%Z ->
    mem_inv usegs m ->
    evt usegs (memcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 n) src m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 MEMMOVE_T2) fc None m (seg_rom usegs)).
  Proof.
    intros SRC LEN DST SEP N1 MI.
    pose proof (rw_cells_bound _ _ _ _ DST) as B. cbn [cells_size csize Nat.add] in B.
    pose proof (bytes_at_bound _ _ _ _ SRC) as B2. rewrite LEN in B2.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold MEMMOVE_T2.
    zstep. if_cases K0; zify_cond K0; [exfalso; lia|].
    zstep. zstep. zstep. zstep.
    zstep. if_cases K; zify_cond K.
    -
      zstep.
      eapply memcpy_spec; rewrite ?unsigned_lit by lia; try eassumption.
    - exfalso.
      rewrite Z.shiftl_mul_pow2 in K by lia. change (2 ^ 1)%Z with 2%Z in K.
      Z.div_mod_to_equations. lia.
  Qed.
End Far.

Lemma memmove_far_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (src junk : list byte),
  bytes_at usegs m (bv_unsigned a1) src ->
  length src = Z.to_nat (bv_unsigned a2) ->
  rw_cells usegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
  (bv_unsigned a1 + bv_unsigned a2 <= bv_unsigned a0 \/ bv_unsigned a0 + bv_unsigned a2 <= bv_unsigned a1)%Z ->
  (1 <= bv_unsigned a2)%Z ->
  mem_inv usegs m ->
  evt usegs (memcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 src m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 MEMMOVE_T2) fc None m (seg_rom usegs)).
Proof.
  intros until junk. intros SRC LEN DST SEP N1 MI.
  pose proof (bv_unsigned_in_range 64 a2) as R2. unfold bv_modulus in R2.
  rewrite <- (Z_to_bv_bv_unsigned a0), <- (Z_to_bv_bv_unsigned a1), <- (Z_to_bv_bv_unsigned a2).
  apply memmove_far_body with (junk := junk); try assumption. cbn [Z.of_N Z.pow_pos Pos.iter Z.mul] in R2. lia.
Qed.

Lemma xor_succ_land7_nz : forall D : Z, (0 <= D)%Z -> Z.land (Z.lxor (D + 1) D) 7 <> 0%Z.
Proof.
  intros D HD E.
  assert (B : Z.testbit (Z.land (Z.lxor (D + 1) D) 7) 0 = true).
  { rewrite Z.land_spec, Z.lxor_spec, !Z.bit0_odd. change (Z.odd 7) with true.
    rewrite Z.add_1_r, Z.odd_succ, <- Z.negb_odd. destruct (Z.odd D); reflexivity. }
  rewrite E in B. cbn in B. discriminate.
Qed.

Section Left1.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (D : Z) (b0 : byte) (src : list byte).
  Notation n := (Z.of_nat (length src)).
  Notation W := [(D, D + n)]%Z.

  Definition left1_bytes : list byte := src ++ [nth (length src) (b0 :: src) b0].

  Definition memmove_left1_post : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 xa1 xa2 xa3 xa4 xa5 xa6 xa7 x28 x29 x30 x31 m',
      ms' = MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 D) xa1 xa2 xa3 xa4 xa5 xa6 xa7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
               F (ret_pc ra) fc None m' (seg_rom usegs)
      /\ munch W m m' /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ u8arr usegs m' D left1_bytes.

  Hypothesis ARR : u8arr usegs m D (b0 :: src).
  Hypothesis MI : mem_inv usegs m.
  Hypothesis HN : (n < 2^62)%Z.
  Hypothesis HD2 : (D + n + 2 <= 2^64)%Z.

  Notation ST pc mm xa1 xa2 xa3 xa4 xa5 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) xa1 xa2 xa3 xa4 xa5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  Definition LINV (i : Z) (mm : word -> option byte) : Prop :=
    exists bs, u8arr usegs mm D bs /\ length bs = S (length src)
      /\ (forall j, (j < Z.to_nat i)%nat -> nth_error bs j = nth_error src j)
      /\ (forall j, (Z.to_nat i <= j)%nat -> (j <= length src)%nat -> nth_error bs j = nth_error (b0 :: src) j)
      /\ mem_inv usegs mm /\ munch W m mm /\ wmono usegs m mm.

  Lemma LINV0 : LINV 0 m.
  Proof using ARR MI.
    exists (b0 :: src). split; [exact ARR|]. split; [reflexivity|]. split; [intros j Hj; lia|]. split; [intros; reflexivity|].
    split; [exact MI|]. split; [apply munch_refl | apply wmono_refl].
  Qed.

  Lemma left1_bytes_length : length left1_bytes = S (length src).
  Proof. unfold left1_bytes. rewrite length_app. cbn [length]. lia. Qed.

  Lemma LINV_fin : forall mm, LINV n mm -> u8arr usegs mm D left1_bytes /\ mem_inv usegs mm /\ munch W m mm /\ wmono usegs m mm.
  Proof.
    intros mm (bs & UA & L & P1 & P2 & MI' & MU & WM). split; [|tauto].
    replace left1_bytes with bs; [exact UA|].
    apply (nth_ext bs left1_bytes b0 b0); [rewrite left1_bytes_length; exact L|].
    intros j Hj. unfold left1_bytes.
    destruct (Nat.lt_ge_cases j (length src)) as [Hl|Hg].
    - rewrite app_nth1 by lia. apply nth_error_nth. rewrite (P1 j) by lia. apply nth_error_nth'. lia.
    - assert (j = length src) by lia. subst j. rewrite app_nth2 by lia. rewrite Nat.sub_diag.
      change (nth 0 [nth (length src) (b0 :: src) b0] b0) with (nth (length src) (b0 :: src) b0).
      apply nth_error_nth. rewrite (P2 (length src)) by lia. apply nth_error_nth'. cbn [length]. lia.
  Qed.

  Lemma mm_BL : forall (f : nat) (i : Z) xa1 xa5 mm,
    LINV i mm -> (0 <= i < n)%Z -> (n - i <= Z.of_nat f)%Z -> (D + n + 1 <= 2^64)%Z -> (0 <= D)%Z ->
    evt usegs memmove_left1_post (ST 0xd02b4 mm xa1 (Z_to_bv 64 (D + n)) (Z_to_bv 64 (D + i)) (Z_to_bv 64 (D + 1 + i)) xa5).
  Proof using HN HD2.
    induction f as [|f IH]; intros i xa1 xa5 mm INV Hi Hf HD D0; [exfalso; lia|].
    destruct INV as (bs & UA & L & P1 & P2 & MI' & MU & WM).

    destruct (nth_error src (Z.to_nat i)) as [b|] eqn:EB; [|apply nth_error_None in EB; lia].
    assert (EBS : nth_error bs (Z.to_nat (1 + i)) = Some b).
    { rewrite (P2 (Z.to_nat (1 + i))) by lia. replace (Z.to_nat (1 + i)) with (S (Z.to_nat i)) by lia. cbn [nth_error]. exact EB. }
    assert (RD : ov_read_bytes usegs mm (wa (D + (1 + i))) 1 = Some [b]).
    { eapply u8arr_read; [exact UA | exact EBS | lia | reflexivity]. }
    replace (wa (D + (1 + i))) with (Z_to_bv 64 (D + 1 + i)) in RD by (unfold wa; f_equal; lia).
    zstep. zstep. zstep.
    u8_store UA i 1%nat.
    replace (le1 (Z_to_bv 64 (bv_unsigned b))) with [b] in UA by (symmetry; apply le1_zxb).
    zstep.
    zstep. if_cases K; zify_cond K.
    -
      eapply evt_eq; [| eapply (IH (i + 1)%Z); [ | lia | lia | lia | lia]].
      + num_st_eq.
      + exists (upd_bytes bs (Z.to_nat i) [b]). split; [exact UA|].
        assert (LU : length (upd_bytes bs (Z.to_nat i) [b]) = S (length src)) by (rewrite upd_bytes_length by (cbn [length]; lia); exact L).
        split; [exact LU|]. split; [|split; [|split; [assumption| split; assumption]]].
        * intros j Hj. rewrite upd_bytes_nth by (cbn [length]; lia). cbn [length].
          destruct (Nat.eq_dec j (Z.to_nat i)) as [->|NE].
          -- replace (Nat.leb (Z.to_nat i) (Z.to_nat i) && Nat.ltb (Z.to_nat i) (Z.to_nat i + 1))%bool with true
               by (symmetry; apply andb_true_intro; split; [apply Nat.leb_refl | apply Nat.ltb_lt; lia]).
             rewrite Nat.sub_diag. cbn [nth_error]. symmetry. exact EB.
          -- replace (Nat.leb (Z.to_nat i) j && Nat.ltb j (Z.to_nat i + 1))%bool with false.
             2:{ symmetry. destruct (Nat.leb_spec0 (Z.to_nat i) j); [|reflexivity]. cbn [andb]. apply Nat.ltb_ge. lia. }
             apply P1. lia.
        * intros j Hj1 Hj2. rewrite upd_bytes_nth by (cbn [length]; lia). cbn [length].
          replace (Nat.leb (Z.to_nat i) j && Nat.ltb j (Z.to_nat i + 1))%bool with false.
          2:{ symmetry. destruct (Nat.leb_spec0 (Z.to_nat i) j); [|reflexivity]. cbn [andb]. apply Nat.ltb_ge. lia. }
          apply P2; lia.
    -
      assert (EI : (i + 1 = n)%Z) by (Z.div_mod_to_equations; lia).
      zstep. zstep.
      apply evt_done. unfold memmove_left1_post.
      lazymatch goal with |- context [MS _ _ _ _ _ ?mm' _] =>
      assert (FIN : LINV n mm'); [|] end.
      { exists (upd_bytes bs (Z.to_nat i) [b]). split; [exact UA|].
        split; [rewrite upd_bytes_length by (cbn [length]; lia); exact L|].
        split; [|split; [|split; [assumption| split; assumption]]].
        * intros j Hj. rewrite upd_bytes_nth by (cbn [length]; lia). cbn [length].
          destruct (Nat.eq_dec j (Z.to_nat i)) as [->|NE].
          -- replace (Nat.leb (Z.to_nat i) (Z.to_nat i) && Nat.ltb (Z.to_nat i) (Z.to_nat i + 1))%bool with true
               by (symmetry; apply andb_true_intro; split; [apply Nat.leb_refl | apply Nat.ltb_lt; lia]).
             rewrite Nat.sub_diag. cbn [nth_error]. symmetry. exact EB.
          -- replace (Nat.leb (Z.to_nat i) j && Nat.ltb j (Z.to_nat i + 1))%bool with false.
             2:{ symmetry. destruct (Nat.leb_spec0 (Z.to_nat i) j); [|reflexivity]. cbn [andb]. apply Nat.ltb_ge. lia. }
             apply P1. lia.
        * intros j Hj1 Hj2. rewrite upd_bytes_nth by (cbn [length]; lia). cbn [length].
          replace (Nat.leb (Z.to_nat i) j && Nat.ltb j (Z.to_nat i + 1))%bool with false.
          2:{ symmetry. destruct (Nat.leb_spec0 (Z.to_nat i) j); [|reflexivity]. cbn [andb]. apply Nat.ltb_ge. lia. }
          apply P2; lia. }
      destruct (LINV_fin _ FIN) as (UA' & MI2 & MU2 & WM2).
      do 15 eexists. split; [reflexivity|]. split; [exact MU2|]. split; [exact WM2|]. split; [exact MI2| exact UA'].
  Qed.

  Lemma memmove_left1_body :
    evt usegs memmove_left1_post (ST 0xd027c m (Z_to_bv 64 (D + 1)) (Z_to_bv 64 n) a3 a4 a5).
  Proof using ARR MI HN HD2.
    pose proof (u8arr_bound _ _ _ _ ARR) as AB. cbn [length] in AB.
    pose proof LINV0 as INV.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl usegs m) as WM.
    zstep. if_cases K0; zify_cond K0; [exfalso; Z.div_mod_to_equations; lia|].
    zstep. zstep. zstep. zstep.
    zstep. if_cases K; zify_cond K; rewrite Z.shiftl_mul_pow2 in K by lia; change (2 ^ 1)%Z with 2%Z in K.
    -
      assert (N1 : n = 1%Z) by (Z.div_mod_to_equations; lia).
      unfold memmove_left1_post, left1_bytes.
      destruct src as [|b1 [|? ?]]; cbn [length] in N1; [lia| |lia]. clear N1.
      zstep.

      destruct ARR as [HB HW]. cbn [length] in HW.
      change (bytes_at usegs m D ([b0] ++ [b1])) in HB.
      apply (proj1 (bytes_at_app _ _ _ _ _)) in HB. destruct HB as [HB1 HB2]. cbn [length] in HB2.
      replace (D + Z.of_nat 1)%Z with (D + 1)%Z in HB2 by lia.
      destruct (wr_at_split usegs m D _ 1 HW ltac:(lia)) as [HW1 HW2].
      pose proof (rw_cells_of_u8arr usegs m D [b0] (conj HB1 HW1)) as DST. cbn [length] in DST.
      eapply evt_mono.
      { eapply memcpy_spec with (src := [b1]) (junk := [b0]); rewrite ?unsigned_lit by (cbn; lia);
          [ exact HB2 | reflexivity | exact DST | cbn; lia | exact MI ]. }
      intros ms' (x5 & x6 & x7 & xa1 & xa2 & xa3 & xa4 & xa5 & xa6 & xa7 & x28 & x29 & x30 & x31 & m' & -> & MU' & WM' & MI' & DST' & SRC').
      rewrite !unsigned_lit in MU' by (cbn; lia). rewrite !unsigned_lit in DST' by (cbn; lia). rewrite !unsigned_lit in SRC' by (cbn; lia).
      do 15 eexists. split; [reflexivity|].
      split; [exact MU'|]. split; [exact WM'|]. split; [exact MI'|].
      change ([b1] ++ [nth (length [b1]) [b0; b1] b0]) with ([b1] ++ [b1]).
      apply (u8arr_app usegs m' D [b1] [b1]); [exact (u8arr_of_rw_cells usegs m' D _ [b1] DST')|].
      cbn [length]. replace (D + Z.of_nat 1)%Z with (D + 1)%Z by lia.
      split; [exact SRC'|]. cbn [length]. eapply wr_at_transport; [| exact WM'].
      replace 1%Z with (Z.of_nat 2 - 1)%Z by lia. exact HW2.
    -
      zstep. zstep.
      zstep. if_cases KB; zify_cond KB; [exfalso; Z.div_mod_to_equations; lia|].
      zstep. if_cases KA; zify_cond KA.
      { exfalso. exact (xor_succ_land7_nz D ltac:(lia) KA). }
      zstep. zstep.
      zstep. if_cases KZ; zify_cond KZ.
      +
        assert (N0 : n = 0%Z) by (Z.div_mod_to_equations; lia).
        unfold memmove_left1_post, left1_bytes. clear INV.
        destruct src; cbn [length] in N0; [|lia].
        zstep.
        apply evt_done. do 15 eexists. split; [reflexivity|].
        split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. cbn [length nth app]. exact ARR.
      + zstep.
        eapply evt_eq; [| eapply (mm_BL (length src) 0%Z); [exact INV | Z.div_mod_to_equations; lia | lia | lia | lia]].
        num_st_eq.
  Qed.
End Left1.

Lemma memmove_left1_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (D : Z) (b0 : byte) (src : list byte),
  a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 (D + 1) -> a2 = Z_to_bv 64 (Z.of_nat (length src)) ->
  u8arr usegs m D (b0 :: src) -> mem_inv usegs m -> (Z.of_nat (length src) < 2^62)%Z -> (D + Z.of_nat (length src) + 2 <= 2^64)%Z ->
  evt usegs (memmove_left1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m D b0 src)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 MEMMOVE_T2) fc None m (seg_rom usegs)).
Proof.
  intros until src. intros -> -> -> ARR MI HN HD2. unfold MEMMOVE_T2.
  exact (memmove_left1_body ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m D b0 src ARR MI HN HD2).
Qed.
