(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Bigint_defs.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFA Require Import A_cap.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_rt_stmt B_rt_lemmas.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_negative_digit_comp_d_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_long_mul_stmt B_parse_mantissa_stmt B_negative_digit_comp_d_stmt B_positive_digit_comp_f_stmt B_negative_digit_comp_f_stmt B_dcf_f_stmt.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_rt_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_rt_lemmas OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_negative_digit_comp_d_stmt.B_fakestack OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_long_mul_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_parse_mantissa_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_negative_digit_comp_d_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_positive_digit_comp_f_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_negative_digit_comp_f_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_dcf_f_stmt.
Local Ltac lia ::= lia_tc.  (* [comment removed for export] *)
Local Ltac step ::=
  app2_lin_all;
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) => step_core segs R F pc fc rv m ro; try decide_lit_if
  | |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail "pc is not a literal:" pc
  end.  (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Ltac post_keep :=
  let ms' := fresh "ms'" in let PO := fresh "POST" in
  intros ms' PO; destruct_exs PO;
  let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in
  destruct PO as [E [MUc [WMc PO]]]; subst ms'; try destruct_ands PO;
  try (lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end).

Lemma zeros504 : forall m A, u8arr BSEGS m A (repeat (Z_to_bv 8 0) (Z.to_nat 504)) ->
  u64arr BSEGS m A (repeat (Z_to_bv 64 0) 62) /\ rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 0)] /\
  u8arr BSEGS m (A + 498) (repeat (Z_to_bv 8 0) 6).
Proof.
  intros m A H. change (Z.to_nat 504) with (496 + 2 + 6)%nat in H. rewrite !repeat_app in H.
  apply u8arr_app in H as (H1 & H3). apply u8arr_app in H1 as (H1 & H2).
  rewrite ?length_app, ?repeat_length in H2, H3. change (A + Z.of_nat 496)%Z with (A + 496)%Z in H2.
  change (A + Z.of_nat (496 + 2))%Z with (A + 498)%Z in H3.
  split; [|split; [|exact H3]].
  - destruct H1 as (B1 & W1). split.
    + replace (u64s (repeat (Z_to_bv 64 0) 62)) with (repeat (Z_to_bv 8 0) 496) by (vm_compute; reflexivity). exact B1.
    + rewrite repeat_length in W1. exact W1.
  - destruct H2 as (B2 & W2). split; [split; [cbn; tauto|]|].
    + replace (cells_bytes [C2 (Z_to_bv 64 0)]) with (repeat (Z_to_bv 8 0) 2) by (vm_compute; reflexivity). exact B2.
    + rewrite repeat_length in W2. exact W2.
Qed.

Lemma shiftr_small_0 : forall dg n, (0 <= dg < 2^32)%Z -> (32 <= n)%Z -> Z.shiftr dg n = 0%Z.
Proof.
  intros dg n H Hn. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. split; [lia|].
  eapply Z.lt_le_trans; [apply (proj2 H)|]. apply Z.pow_le_mono_r; lia.
Qed.
Lemma c8_as_c4s : forall m A dg, (0 <= dg < 2^32)%Z ->
  rw_cells BSEGS m A [C8 (Z_to_bv 64 dg)] -> rw_cells BSEGS m A [C4 (Z_to_bv 64 dg); C4 (Z_to_bv 64 0)].
Proof.
  intros m A dg Hdg [[Hwf Hb] Hw]. split; [split|]; [cbn; tauto | | exact Hw].
  revert Hb. cbn [cells_bytes cbytes app]. unfold le8, le4, word_to_le_bytes.
  rewrite !unsigned_lit by lia. cbn [Z_to_le_bytes app].
  rewrite !Z.shiftr_shiftr by lia.
  rewrite (shiftr_small_0 dg (8+8+8+8)) by lia. rewrite (shiftr_small_0 dg (8+8+8+8+8)) by lia.
  rewrite (shiftr_small_0 dg (8+8+8+8+8+8)) by lia. rewrite (shiftr_small_0 dg (8+8+8+8+8+8+8)) by lia.
  rewrite !Z.shiftr_0_l. exact (fun H => H).
Qed.

Ltac swrap_unfold :=
  unfold bv_swrap, bv_wrap in *;
  replace (bv_half_modulus 32) with (2^31)%Z in * by reflexivity;
  replace (bv_modulus 32) with (2^32)%Z in * by reflexivity.
Lemma dc_e : forall se dg, (-342 <= se <= 358)%Z -> (0 <= dg <= 770)%Z ->
  bv_swrap 32 (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 se) - bv_unsigned (sx32 (Z_to_bv 64 dg))))) + 1)
  = (se - dg + 1)%Z.
Proof.
  intros se dg Hse Hdg. unfold sx32. rewrite !unsigned_lit_wrap. swrap_unfold.
  Z.div_mod_to_equations; lia.
Qed.
Lemma lts_e : forall e, (-2^62 <= e <= 2^62)%Z -> bv_lts (Z_to_bv 64 e) (Z_to_bv 64 0) = Z.ltb e 0.
Proof.
  intros e He. rewrite bv_lts_zero_r, unsigned_lit_wrap. apply eq_true_iff_eq. rewrite Z.leb_le, Z.ltb_lt.
  Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma bsw : forall se k, (-342 <= se <= 358)%Z -> (0 <= k <= 1)%Z -> bv_swrap 32 (bv_unsigned (Z_to_bv 64 se) + k) = (se + k)%Z.
Proof. intros se k Hse Hk. rewrite !unsigned_lit_wrap. swrap_unfold. Z.div_mod_to_equations; lia. Qed.
Lemma lts_lit : forall a b, (-2^62 <= a <= 2^62)%Z -> (-2^62 <= b <= 2^62)%Z -> bv_lts (Z_to_bv 64 a) (Z_to_bv 64 b) = Z.ltb a b.
Proof.
  intros a b Ha Hb. unfold bv_lts. rewrite !zb_signed, !unsigned_lit_wrap.
  destruct (Z.ltb (a mod 2^64) (2^63)) eqn:E1; destruct (Z.ltb (b mod 2^64) (2^63)) eqn:E2;
    apply eq_true_iff_eq; rewrite ?Z.ltb_lt, ?Z.ltb_ge in *; Z.div_mod_to_equations; lia.
Qed.

Lemma dcb1 : forall se dg, (-342 <= se <= 358)%Z -> (0 <= dg <= 770)%Z ->
  bv_swrap 32 (bv_unsigned (Z_to_bv 64 (se + 1)) - bv_unsigned (sx32 (Z_to_bv 64 dg))) = (se + 1 - dg)%Z.
Proof. intros se dg Hse Hdg. unfold sx32. rewrite !unsigned_lit_wrap. swrap_unfold. Z.div_mod_to_equations; lia. Qed.
Lemma dcb2 : forall se dg, (-342 <= se <= 358)%Z -> (0 <= dg <= 770)%Z ->
  Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (se + 1)) - bv_unsigned (sx32 (Z_to_bv 64 dg))) = Z_to_bv 64 (se + 1 - dg).
Proof.
  intros se dg Hse Hdg. apply bv_eq. rewrite !unsigned_lit_wrap. unfold sx32. rewrite !unsigned_lit_wrap. swrap_unfold.
  Z.div_mod_to_equations; lia.
Qed.
Lemma negb_eqb_same : forall x : word, negb (bv_eqb x x) = false.
Proof. intros x. unfold bv_eqb. rewrite Z.eqb_refl. reflexivity. Qed.

(* [comment removed for export] *)
Lemma fk4_transport : forall W m m' FS h4 pos0, fk4_nest m FS h4 pos0 -> munch W m m' -> wmono BSEGS m m' ->
  disjoint_from W (FS + 88) 9 -> disjoint_from W (FS + FK4_HINT) 8 -> disjoint_from W (FS + FK4_FLAGS) 1024 ->
  disjoint_from W (FS + FK4_LO) (pos0 * 1024) -> disjoint_from W (FS + FK4_LO + pos0 * 1024 + 1024) (FK4_HI - (FK4_LO + pos0 * 1024 + 1024)) ->
  disjoint_from W (ASAN_B + FS / 8 + FK4_SLO) (pos0 * 128) ->
  disjoint_from W (ASAN_B + FS / 8 + FK4_SLO + pos0 * 128 + 128) (FK4_SHI - (FK4_SLO + pos0 * 128 + 128)) ->
  fk4_nest m' FS h4 pos0.
Proof.
  intros W m m' FS h4 pos0 (F1 & F2 & F3 & F4 & F5 & F6 & F7) MU WM D1 D2 D3 D4 D5 D6 D7.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
  - unfold fs_cells_ok in *. apply (ro_cells_transport BSEGS W m m' _ _ F1 MU). exact D1.
  - apply (rw_cells_transport BSEGS W m m' _ _ F2 MU WM). exact D2.
  - apply (u8arr_transport BSEGS W m m' _ _ F3 MU WM). rewrite upd_length, zeros_length. exact D3.
  - apply (stk_transport_disjoint BSEGS W m m' _ _ F4 MU WM). replace (FS + FK4_LO + pos0 * 1024 - (FS + FK4_LO))%Z with (pos0 * 1024)%Z by lia. exact D4.
  - apply (stk_transport_disjoint BSEGS W m m' _ _ F5 MU WM). replace (FS + FK4_HI - (FS + FK4_LO + pos0 * 1024 + 1024))%Z with (FK4_HI - (FK4_LO + pos0 * 1024 + 1024))%Z by lia. exact D5.
  - apply (stk_transport_disjoint BSEGS W m m' _ _ F6 MU WM). replace (ASAN_B + FS / 8 + FK4_SLO + pos0 * 128 - (ASAN_B + FS / 8 + FK4_SLO))%Z with (pos0 * 128)%Z by lia. exact D6.
  - apply (stk_transport_disjoint BSEGS W m m' _ _ F7 MU WM).
    replace (ASAN_B + FS / 8 + FK4_SHI - (ASAN_B + FS / 8 + FK4_SLO + pos0 * 128 + 128))%Z with (FK4_SHI - (FK4_SLO + pos0 * 128 + 128))%Z by lia. exact D7.
Qed.

Lemma fk5_transport : forall W m m' FS h5, fk5_inv m FS h5 -> munch W m m' -> wmono BSEGS m m' ->
  disjoint_from W (FS + 88) 9 -> disjoint_from W (FS + FK5_HINT) 8 -> disjoint_from W (FS + FK5_FLAGS) 512 ->
  disjoint_from W (FS + FK5_LO) (FK5_HI - FK5_LO) -> disjoint_from W (ASAN_B + FS / 8 + FK5_SLO) (FK5_SHI - FK5_SLO) ->
  fk5_inv m' FS h5.
Proof.
  intros W m m' FS h5 (F1 & F2 & F3 & F4 & F5) MU WM D1 D2 D3 D4 D5.
  refine (conj _ (conj _ (conj _ (conj _ _)))).
  - unfold fs_cells_ok in *. apply (ro_cells_transport BSEGS W m m' _ _ F1 MU). exact D1.
  - apply (rw_cells_transport BSEGS W m m' _ _ F2 MU WM). exact D2.
  - apply (u8arr_transport BSEGS W m m' _ _ F3 MU WM). rewrite zeros_length. exact D3.
  - apply (stk_transport_disjoint BSEGS W m m' _ _ F4 MU WM). replace (FS + FK5_HI - (FS + FK5_LO))%Z with (FK5_HI - FK5_LO)%Z by lia. exact D4.
  - apply (stk_transport_disjoint BSEGS W m m' _ _ F5 MU WM).
    replace (ASAN_B + FS / 8 + FK5_SHI - (ASAN_B + FS / 8 + FK5_SLO))%Z with (FK5_SHI - FK5_SLO)%Z by lia. exact D5.
Qed.

Lemma dc_p2 : forall (s11 : word) p2, (bv_unsigned s11 mod 2 ^ 32 = (p2 - 32768) mod 2 ^ 32)%Z ->
  bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (bv_unsigned s11 + 32768))) (bv_unsigned (Z_to_bv 64 4294967295))))
  = (p2 mod 2 ^ 32)%Z.
Proof.
  intros s11 p2 H. change (bv_unsigned (Z_to_bv 64 4294967295)) with (Z.ones 32). rewrite Z.land_ones by lia.
  rewrite !unsigned_lit_wrap.
  rewrite (Z.mod_small (_ mod 2 ^ 32) (2 ^ 64)) by (pose proof (Z.mod_pos_bound ((bv_unsigned s11 + 32768) mod 2 ^ 64) (2^32) ltac:(lia)); lia).
  rewrite <- Znumtheory.Zmod_div_mod; [| lia | lia | exists (2 ^ 32)%Z; reflexivity].
  rewrite <- Zplus_mod_idemp_l, H, Zplus_mod_idemp_l. replace (p2 - 32768 + 32768)%Z with p2 by ring. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma dc_p2b : forall (s9 : word) p2, (bv_unsigned s9 mod 2 ^ 32 = (p2 - 32768) mod 2 ^ 32)%Z ->
  bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (bv_unsigned s9 + 32768))) 32))) 32))
  = (p2 mod 2 ^ 32)%Z.
Proof.
  intros s9 p2 H. rewrite !unsigned_lit_wrap. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.shiftr_div_pow2 by lia.
  set (x := ((bv_unsigned s9 + 32768) mod 2 ^ 64)%Z).
  assert (Hx : (x mod 2 ^ 32 = p2 mod 2 ^ 32)%Z).
  { subst x. rewrite <- Znumtheory.Zmod_div_mod; [| lia | lia | exists (2 ^ 32)%Z; reflexivity].
    rewrite <- Zplus_mod_idemp_l, H, Zplus_mod_idemp_l. replace (p2 - 32768 + 32768)%Z with p2 by ring. reflexivity. }
  assert (E : ((x * 2 ^ 32) mod 2 ^ 64 = (x mod 2 ^ 32) * 2 ^ 32)%Z).
  { change (2 ^ 64)%Z with (2 ^ 32 * 2 ^ 32)%Z. apply Z.mul_mod_distr_r; lia. }
  rewrite E, Z.div_mul by lia. rewrite Hx. apply Z.mod_small. pose proof (Z.mod_pos_bound p2 (2 ^ 32) ltac:(lia)). lia.
Qed.

Lemma stk_of_u64arr : forall m A ws, u64arr BSEGS m A ws -> stk BSEGS m A (A + 8 * Z.of_nat (length ws)).
Proof.
  intros m A ws ((B1 & B2 & B) & (W1 & W2 & W)). rewrite u64s_length in B2. split; [lia|]. split; [lia|].
  intros a Ha. split; [replace a with (A + (a - A))%Z by lia; apply W; lia|].
  pose proof (B (Z.to_nat (a - A)) ltac:(rewrite u64s_length; lia)) as X. rewrite Z2Nat.id in X by lia.
  replace (A + (a - A))%Z with a in X by lia. destruct (nth_error (u64s ws) (Z.to_nat (a - A))) as [b|] eqn:Hb.
  - exists b. exact X.
  - apply nth_error_None in Hb. rewrite u64s_length in Hb. lia.
Qed.
Lemma stk_of_rw_cells : forall m A cs, rw_cells BSEGS m A cs -> stk BSEGS m A (A + Z.of_nat (cells_size cs)).
Proof.
  intros m A cs ((Hwf & B1 & B2 & B) & (W1 & W2 & W)). rewrite (cells_bytes_length cs Hwf) in B2. split; [lia|]. split; [lia|].
  intros a Ha. split; [replace a with (A + (a - A))%Z by lia; apply W; lia|].
  pose proof (B (Z.to_nat (a - A)) ltac:(rewrite (cells_bytes_length cs Hwf); lia)) as X. rewrite Z2Nat.id in X by lia.
  replace (A + (a - A))%Z with a in X by lia. destruct (nth_error (cells_bytes cs) (Z.to_nat (a - A))) as [b|] eqn:Hb.
  - exists b. exact X.
  - apply nth_error_None in Hb. rewrite (cells_bytes_length cs Hwf) in Hb. lia.
Qed.
Lemma stk_of_u8arr : forall m A bs, u8arr BSEGS m A bs -> stk BSEGS m A (A + Z.of_nat (length bs)).
Proof.
  intros m A bs ((B1 & B2 & B) & (W1 & W2 & W)). split; [lia|]. split; [lia|].
  intros a Ha. split; [replace a with (A + (a - A))%Z by lia; apply W; lia|].
  pose proof (B (Z.to_nat (a - A)) ltac:(lia)) as X. rewrite Z2Nat.id in X by lia.
  replace (A + (a - A))%Z with a in X by lia. destruct (nth_error bs (Z.to_nat (a - A))) as [b|] eqn:Hb.
  - exists b. exact X.
  - apply nth_error_None in Hb. lia.
Qed.

Section Frag.
  Hypothesis AMS : asan_memset_stmt.
  Hypothesis PMS : parse_mantissa_stmt.
  Hypothesis PDC : positive_digit_comp_f_stmt.
  Hypothesis NDC : negative_digit_comp_f_stmt.

  #[using="AMS PMS PDC NDC"] Lemma dcf_f_spec : dcf_f_stmt.
  Proof. LiaFast.lf_pins (fun (AMS PMS PDC NDC : LiaFast.U) => LiaFast.u0).
    unfold dcf_f_stmt. intros until p2. cbv zeta.
    intros TP S1 S9 Hse S6 Hp2 ST AL SPLO KSP KTP SHW DGC SHD XB Xlen XAL XF1 XF2 XSP SHX RBX NUM SHN
           IBS INZ IEND ILEN FBS FEND FLEN FNULL KTLO TLI1 TLI2 TLF TXT TXS SHI GI1 GI2 SHF PR PRG PRT RTH RDW RDA RDF
           SHT SHP RBF FK4 Hpos Hh4 FK5 SFS RTX0.
    rename m into m0.
    pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
    pose proof (bv_unsigned_in_range 64 s8) as Rs7. unfold bv_modulus in Rs7.
    subst tp s1.
    open_RT_keep RTH.
    destruct RTP as (Hbeg & Hblk & Hblk1 & Hctx & Hthr & HFS1 & HFS2 & HFS3 & Kc1 & Kc2 & Kt1 & Kt2 & Kb1 & Kb2).
    assert (BC : ro_cells BSEGS m0 943736 [C8 (Z_to_bv 64 ASAN_B)]).
    { change [C8 (Z_to_bv 64 ASAN_B); C4 (Z_to_bv 64 1)] with ([C8 (Z_to_bv 64 ASAN_B)] ++ [C4 (Z_to_bv 64 1)]) in RT1.
      apply (proj1 (proj1 (ro_cells_app BSEGS m0 943736 _ _) RT1)). }
    clear RT1 RT2 RT2b RT3 RT4 RT5 RT6 RT7 RT8 RT9 RT10 RT11 RT12 RT13 RT14 Hfb fb.
    assert (Z0 : (KHI <= bv_unsigned sp - 2768 /\ bv_unsigned sp + 152 <= KTOP /\ bv_unsigned s8 + 512 <= bv_unsigned sp - 2768 /\ (app2r (bv_unsigned s8) (bv_unsigned s8 + 512)) /\ THI <= bv_unsigned sp - 2768)%Z).
    { clear -KSP KTP XSP XF1 XF2 HFS1 Hpos TXS SFS. repeat split; lia. }
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    eapply evt_cut; [ eapply AMS with (v := v) (old := old) (c := 0%Z) (shlo := (ASAN_B + bv_unsigned s8 / 8 - 8)%Z) (shn := 79%Z)
                    | post_keep ].
    1:{ reflexivity. } 1:{ lia. } 1:{ exact XB. } 1:{ rewrite Xlen. reflexivity. } 1:{ exact XAL. }
    1:{ change (bv_unsigned (Z_to_bv 64 504)) with 504%Z. clear -XF1 XF2 HFS1 Hpos. lia. }
    1:{ change (bv_unsigned (Z_to_bv 64 504)) with 504%Z. clear -XSP KTP. lia. }
    1:{ change (bv_unsigned (Z_to_bv 64 504)) with 504%Z. lia. }
    1:{ change (bv_unsigned (Z_to_bv 64 504)) with 504%Z. exact SHX. }
    1:{ exact RBX. }
    1:{ clear. pose proof (Z.mod_pos_bound (ASAN_B + bv_unsigned s8 / 8) 8 ltac:(lia)). lia. }
    1:{ change (bv_unsigned (Z_to_bv 64 504)) with 504%Z. clear -XAL Rs7. Z.div_mod_to_equations. lia. }
    1:{ destruct (stk_split BSEGS _ _ (bv_unsigned sp - 2208) _ ST ltac:(clear; lia)) as (_ & X). exact X. }
    1:{ clear -SPLO. lia. } 1:{ clear -KSP. lia. } 1:{ clear -KTP. lia. } 1:{ exact AL. }
    1:{ change (bv_unsigned (Z_to_bv 64 504)) with 504%Z. clear -XSP. lia. }
    1:{ exact PRG. } 1:{ exact PRT. } 1:{ exact RTH. }
    1:{ eapply rt_disj_sub; [exact RDW | clear; lia | clear; lia]. }
    1:{ change (bv_unsigned (Z_to_bv 64 504)) with 504%Z. exact RDA. }
    1:{ reflexivity. }
    (* [comment removed for export] *)
    lazymatch goal with H : munch _ m0 ?m' |- _ => rename m' into m1; rename H into MU1 end.
    lazymatch goal with H : wmono _ m0 m1 |- _ => rename H into WM1 end.
    change (bv_unsigned (Z_to_bv 64 504)) with 504%Z in *.
    unfold asan_memset_W in MU1. cbn [List.map] in MU1.
    rename PC into ZX. rename POST into ST1.
    destruct (zeros504 _ _ ZX) as (ZX1 & ZX2 & ZX3). clear ZX.
    Ltac dj Z0 := cbn [disjoint_from]; clear - Z0; Z.div_mod_to_equations; lia.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    assert (UD : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + 144)) = (bv_unsigned sp + 144)%Z) by (apply unsigned_lit; clear -Z0; lia).
    assert (UN : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + 72)) = (bv_unsigned sp + 72)%Z) by (apply unsigned_lit; clear -Z0; lia).
    eapply evt_cut; [ eapply PMS with (ws := repeat (Z_to_bv 64 0) 62) (iptr := iptr) (fptr := fptr) (ibs := ibs) (fbs := fbs) (dg := dg)
                                       (FS := TLO) (THI := THI) (GLO := rt_FS v) (gi := gi) (gin := gin) (gf := gf) (gfn := gfn)
                    | post_keep ].
    (* [comment removed for export] *) 1:{ destruct (stk_split BSEGS _ _ (bv_unsigned sp - 176) _ ST1 ltac:(clear; lia)) as (_ & X). exact X. }
    (* [comment removed for export] *) 1:{ exact AL. }
    (* [comment removed for export] *) 1:{ apply (pristine_transport _ m0 m1 _ _ PR MU1). dj Z0. }
    (* [comment removed for export] *) 1:{ exact ZX1. } 1:{ apply repeat_length. } 1:{ exact ZX2. } 1:{ exact XAL. }
    (* [comment removed for export] *) 1:{ rewrite UN. replace (bv_unsigned sp + 72 + 32)%Z with (bv_unsigned sp + 104)%Z by (clear; lia).
                  apply (rw_cells_transport BSEGS _ m0 m1 _ _ NUM MU1 WM1). cbn [cells_size csize Nat.add]. dj Z0. }
    (* [comment removed for export] *) 1:{ apply (bytes_at_transport BSEGS _ m0 m1 _ _ IBS MU1). cbn [disjoint_from].
                  clear -Z0 TXT TLI1 TLI2. lia. }
    1:{ exact INZ. } 1:{ exact IEND. } 1:{ exact ILEN. }
    (* [comment removed for export] *) 1:{ destruct (Z.eq_dec (bv_unsigned fptr) 0) as [F0|F0].
                  - pose proof (FNULL F0) as L0. destruct fbs; [|discriminate]. rewrite F0. apply bytes_at_nil. lia.
                  - destruct (TLF F0) as (TF1 & TF2). apply (bytes_at_transport BSEGS _ m0 m1 _ _ FBS MU1). cbn [disjoint_from].
                    clear -Z0 TXT TF1 TF2. lia. }
    1:{ exact FEND. } 1:{ exact FLEN. } 1:{ exact FNULL. }
    1:{ change (bv_unsigned (Z_to_bv 64 114)) with 114%Z. lia. }
    (* [comment removed for export] *) 1:{ rewrite UD. apply (rw_cells_transport BSEGS _ m0 m1 _ _ DGC MU1 WM1). cbn [cells_size csize Nat.add]. dj Z0. }
    1:{ apply (pristine_transport _ m0 m1 _ _ PRG MU1). dj Z0. }
    1:{ apply (ro_cells_transport BSEGS _ m0 m1 _ _ BC MU1). cbn [cells_size csize Nat.add]. dj Z0. }
    1:{ clear -SPLO. lia. } 1:{ clear -KSP. lia. } 1:{ rewrite UD. lia. } 1:{ rewrite UD. clear -Z0. lia. }
    1:{ exact KTLO. } 1:{ clear -XF1 HFS1 HFS2 Hpos. lia. } 1:{ exact TLI1. } 1:{ exact TLI2. } 1:{ exact TLF. }
    1:{ rewrite UN. clear. lia. } 1:{ rewrite UN, UD. clear. lia. } 1:{ clear -XF1 XF2 Hpos HFS1 HFS2. lia. } 1:{ rewrite UN. clear -AL. Z.div_mod_to_equations. lia. }
    1:{ clear -Z0 TXT SFS. split; [destruct TXT; [left|right]; lia | split; lia]. }
    1:{ apply (shz_transport BSEGS _ m0 m1 _ _ SHX MU1). dj Z0. }
    1:{ rewrite UD. apply (shz_transport BSEGS _ m0 m1 _ _ SHD MU1). dj Z0. }
    1:{ rewrite UN. replace (bv_unsigned sp + 72 + 32)%Z with (bv_unsigned sp + 104)%Z by (clear; lia).
        apply (shz_transport BSEGS _ m0 m1 _ _ SHN MU1). dj Z0. }
    1:{ apply (shz_transport BSEGS _ m0 m1 _ _ SHI MU1). cbn [disjoint_from]. clear -Z0 GI1 GI2. Z.div_mod_to_equations. lia. }
    1:{ exact GI1. } 1:{ exact GI2. }
    1:{ intros F0. destruct (SHF F0) as (S0 & G1 & G2). split; [|split; [exact G1|exact G2]].
        apply (shz_transport BSEGS _ m0 m1 _ _ S0 MU1). cbn [disjoint_from]. clear -Z0 G1 G2. Z.div_mod_to_equations. lia. }
    1:{ apply (shz_transport BSEGS _ m0 m1 _ _ SHT MU1). dj Z0. }
    (* [comment removed for export] *)
    lazymatch goal with H : munch _ m1 ?m' |- _ => rename m' into m2; rename H into MU2 end.
    lazymatch goal with H : wmono _ m1 m2 |- _ => rename H into WM2 end.
    lazymatch goal with H : u64arr BSEGS m2 _ ?ws |- _ => rename ws into ws2; rename H into X2 end.
    lazymatch goal with H : rw_cells BSEGS m2 (bv_unsigned s8 + 496) [C2 (Z_to_bv 64 ?l)] |- _ => rename l into len2; rename H into LC2 end.
    lazymatch goal with H : rw_cells BSEGS m2 _ [C8 (Z_to_bv 64 ?d)] |- _ => rename d into dg2; rename H into DG2 end.
    rename PC into ST2. rename PC1 into L2. rename PC4 into Hl2. rename PC5 into Hd2. rename PC6 into BN2. rename POST into BV2.
    change (bv_unsigned (Z_to_bv 64 114)) with 114%Z in Hd2. rewrite UD in DG2, MU2. unfold parse_mantissa_W in MU2.
    (* [comment removed for export] *)
    assert (MU : munch (dcf_f_W (bv_unsigned sp) (bv_unsigned s8) (rt_FS v) pos0) m0 m2).
    { apply (munch_trans _ m0 m1 m2).
      - eapply munch_weaken; [|exact MU1]. unfold dcf_f_W. clear. sub_fp_fast.
      - eapply munch_weaken; [|exact MU2]. unfold dcf_f_W. clear. sub_fp_fast. }
    pose proof (wmono_trans BSEGS _ _ _ WM1 WM2) as WM.
    assert (MU12 : munch [(bv_unsigned sp - 2208, bv_unsigned sp); (bv_unsigned s8, bv_unsigned s8 + 504); (bv_unsigned sp + 144, bv_unsigned sp + 152)]%Z m0 m2).
    { apply (munch_trans _ m0 m1 m2).
      - eapply munch_weaken; [|exact MU1]. clear. sub_fp_fast.
      - eapply munch_weaken; [|exact MU2]. clear. sub_fp_fast. }
    (* [comment removed for export] *)
    assert (ZF : (17594333495296 <= bv_unsigned sp - 2768 /\ rt_FS v + 11571200 <= bv_unsigned sp - 2768 /\ rt_FS v + 4231168 + pos0 * 1024 + 32 <= bv_unsigned s8 /\ bv_unsigned s8 + 504 <= rt_FS v + 4231168 + pos0 * 1024 + 1024 /\ 0 <= pos0 < 1024 /\ app2r (rt_FS v) (rt_FS v + 11571200) /\ rt_FS v mod 4096 = 0)%Z) by (clear -KSP SFS XF1 XF2 Hpos HFS1 HFS3; repeat split; lia).
    assert (FK42 : fk4_nest m2 (rt_FS v) h4 pos0).
    { apply (fk4_transport _ m0 m2 _ _ _ FK4 MU12 WM); cbn [disjoint_from]; clear -ZF Z0; Z.div_mod_to_equations; lia. }
    assert (FK52 : fk5_inv m2 (rt_FS v) h5).
    { apply (fk5_transport _ m0 m2 _ _ FK5 MU12 WM); cbn [disjoint_from]; clear -ZF Z0; Z.div_mod_to_equations; lia. }
    assert (RT2 : RT m2 v).
    { apply (RT_transport m0 m2 v _ RTH MU12). unfold W_ok_rt. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
      - split; [clear -SPLO; lia|]. left. eapply rt_disj_sub; [exact RDW | clear; lia | clear; lia].
      - split; [clear -Z0 SPLO; lia | left; exact RDA].
      - split; [clear -SPLO; lia|]. left. eapply rt_disj_sub; [exact RDW | clear; lia | clear; lia]. }
    assert (PR2 : pristine m2 IMG_LO ROD_HI) by (apply (pristine_transport _ m0 m2 _ _ PR MU12); dj Z0).
    assert (PRG2 : pristine m2 RELRO_LO RELRO_HI) by (apply (pristine_transport _ m0 m2 _ _ PRG MU12); dj Z0).
    assert (PRT2 : pristine m2 REALTAB_LO REALTAB_HI) by (apply (pristine_transport _ m0 m2 _ _ PRT MU12); dj Z0).
    assert (SHX2 : shz BSEGS m2 (ASAN_B + bv_unsigned s8 / 8) 63) by (apply (shz_transport BSEGS _ m0 m2 _ _ SHX MU12); dj Z0).
    assert (SHP2 : shz BSEGS m2 POW5TAB_SH POW5TAB_SHN) by (apply (shz_transport BSEGS _ m0 m2 _ _ SHP MU12); dj Z0).
    assert (SHW2 : shz BSEGS m2 (ASAN_B + (bv_unsigned sp - 2768) / 8) 346) by (apply (shz_transport BSEGS _ m0 m2 _ _ SHW MU12); dj Z0).
    assert (SHS2 : shz BSEGS m2 (ASAN_B + (bv_unsigned sp - 2672) / 8) 334) by (eapply shz_sub; [exact SHW2 | clear; Z.div_mod_to_equations; lia | clear; lia | clear; Z.div_mod_to_equations; lia]).
    assert (RBF2 : rdbl BSEGS m2 (ASAN_B + rt_FS v / 8 + FK_SH_LO) FK_SH_N) by (exact (rdbl_mono BSEGS _ _ _ _ RBF WM)).
    assert (RBX2 : rdbl BSEGS m2 (ASAN_B + bv_unsigned s8 / 8 - 8) 79) by (exact (rdbl_mono BSEGS _ _ _ _ RBX WM)).
    (* [comment removed for export] *)
    assert (ST02 : stk BSEGS m2 (bv_unsigned sp - 2768) (bv_unsigned sp)).
    { destruct (stk_split BSEGS _ _ (bv_unsigned sp - 2208) _ ST ltac:(clear; lia)) as (STa & _).
      pose proof (stk_transport_disjoint BSEGS _ m0 m1 _ _ STa MU1 WM1 ltac:(dj Z0)) as STa1.
      pose proof (stk_transport_disjoint BSEGS _ m1 m2 _ _ STa1 MU2 WM2 ltac:(dj Z0)) as STa2.
      destruct (stk_split BSEGS _ _ (bv_unsigned sp - 176) _ ST1 ltac:(clear; lia)) as (STb & _).
      pose proof (stk_transport_disjoint BSEGS _ m1 m2 _ _ STb MU2 WM2 ltac:(dj Z0)) as STb2.
      clear STa STa1 STb.
      apply (stk_merge BSEGS _ _ _ _ STa2 (stk_merge BSEGS _ _ _ _ STb2 ST2 ltac:(clear; lia)) ltac:(clear; lia)). }
    clear ZX1 ZX2 ST1.
    apply c8_as_c4s in DG2; [|clear -Hd2; lia].
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite S9, (bsw se 1 Hse ltac:(lia)), (bsw se 0 Hse ltac:(lia)). rewrite Z.add_0_r.
    step. (* [comment removed for export] *)
    rewrite (lts_lit (se + 1) se ltac:(clear -Hse; lia) ltac:(clear -Hse; lia)).
    replace (Z.ltb (se + 1) se) with false by (symmetry; apply Z.ltb_ge; clear -Hse; lia). cbv iota.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite (dcb1 se dg2 Hse ltac:(clear -Hd2; lia)), (dcb2 se dg2 Hse ltac:(clear -Hd2; lia)), negb_eqb_same. cbv iota.
    step. (* [comment removed for export] *)
    rewrite lts_e by (clear -Hse Hd2; lia). replace (se + 1 - dg2)%Z with (se - dg2 + 1)%Z by (clear; lia).
    destruct (Z.ltb_spec (se - dg2 + 1) 0) as [Hneg|Hpos'].
    - (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      eapply evt_cut; [ eapply NDC with (ws := ws2) (len := len2) (p2 := p2) (e := (se - dg2 + 1)%Z) (v := v) (h4 := h4) (h5 := h5) (pos0 := pos0)
                      | post_keep ].
      1:{ exact ST02. } 1:{ exact AL. } 1:{ exact SPLO. } 1:{ exact PR2. } 1:{ exact X2. } 1:{ exact L2. } 1:{ exact LC2. }
      1:{ exact Hl2. } 1:{ exact XAL. } 1:{ exact BN2. } 1:{ exact (dc_p2b s6 p2 S6). } 1:{ exact Hp2. }
      1:{ reflexivity. } 1:{ clear -Hse Hd2 Hneg. lia. } 1:{ reflexivity. }
      1:{ exact PRG2. } 1:{ exact PRT2. } 1:{ exact RT2. } 1:{ exact FK42. } 1:{ exact Hpos. } 1:{ exact Hh4. } 1:{ exact FK52. }
      1:{ exact KSP. } 1:{ clear -KTP. lia. } 1:{ clear -ZF. lia. } 1:{ exact XF1. } 1:{ clear -XF2. lia. }
      1:{ eapply rt_disj_sub; [exact RDW | clear; lia | clear; lia]. } 1:{ exact RDF. }
      1:{ exact SHX2. } 1:{ exact SHP2. } 1:{ exact RBF2. } 1:{ exact RTX0. } 1:{ exact SHW2. }
      (* [comment removed for export] *)
      lazymatch goal with H : munch _ m2 ?m' |- _ => rename m' into m3; rename H into MU3 end.
      lazymatch goal with H : wmono _ m2 m3 |- _ => rename H into WM3 end.
      unfold negative_digit_comp_f_W in MU3.
      apply evt_done. unfold dcf_f_post.
      do 16 eexists. exists m3. do 2 eexists.
      split; [reflexivity|].
      lazymatch goal with H : u64arr BSEGS m3 (bv_unsigned s8) ?ws |- _ => rename H into X3; rename ws into ws3 end.
      lazymatch goal with H : length ws3 = 62%nat |- _ => rename H into L3 end.
      lazymatch goal with H : rw_cells BSEGS m3 (bv_unsigned s8 + 496) _ |- _ => rename H into LC3 end.
      lazymatch goal with H : stk BSEGS m3 _ _ |- _ => rename H into ST3 end.
      lazymatch goal with H : pristine m3 _ _ |- _ => rename H into PR3 end.
      lazymatch goal with H : RT m3 v |- _ => rename H into RT3 end.
      lazymatch goal with H : fk4_nest m3 _ _ _ |- _ => rename H into FK43 end.
      lazymatch goal with H : fk5_inv m3 _ _ |- _ => rename H into FK53 end.
      refine (conj _ (conj _ (conj ST3 (conj _ (conj _ (conj PR3 (conj RT3 (conj FK43 FK53)))))))).
      + apply (munch_trans _ m0 m2 m3); [exact MU|]. eapply munch_weaken; [|exact MU3]. unfold dcf_f_W. clear. sub_fp_fast.
      + exact (wmono_trans BSEGS _ _ _ WM WM3).
      + pose proof (rw_cells_transport BSEGS _ m2 m3 _ _ DG2 MU3 WM3 ltac:(cbn [cells_size csize Nat.add]; dj ZF)) as DG3.
        pose proof (stk_of_rw_cells _ _ _ DG3) as X. cbn [cells_size csize Nat.add] in X.
        replace (bv_unsigned sp + 152)%Z with (bv_unsigned sp + 144 + Z.of_nat 8)%Z by (clear; lia). exact X.
      + pose proof (u8arr_transport BSEGS _ m1 m2 _ _ ZX3 MU2 WM2 ltac:(rewrite repeat_length; dj Z0)) as ZX32.
        pose proof (u8arr_transport BSEGS _ m2 m3 _ _ ZX32 MU3 WM3 ltac:(rewrite repeat_length; dj ZF)) as ZX33.
        pose proof (stk_of_u64arr _ _ _ X3) as SA. rewrite L3 in SA.
        pose proof (stk_of_rw_cells _ _ _ LC3) as SB. cbn [cells_size csize Nat.add] in SB.
        pose proof (stk_of_u8arr _ _ _ ZX33) as SC. rewrite repeat_length in SC.
        apply (stk_merge BSEGS _ _ (bv_unsigned s8 + 496) _); [|apply (stk_merge BSEGS _ _ (bv_unsigned s8 + 498) _) | clear; lia].
        * replace (bv_unsigned s8 + 496)%Z with (bv_unsigned s8 + 8 * Z.of_nat 62)%Z by (clear; lia). exact SA.
        * replace (bv_unsigned s8 + 498)%Z with (bv_unsigned s8 + 496 + Z.of_nat 2)%Z by (clear; lia). exact SB.
        * replace (bv_unsigned s8 + 504)%Z with (bv_unsigned s8 + 498 + Z.of_nat 6)%Z by (clear; lia). exact SC.
        * clear; lia.
    - (* [comment removed for export] *)
      assert (Hlen2 : (len2 <= dg2 / 19 + 3)%Z).
      { pose proof (bnorm_len_le ws2 (Z.to_nat len2) (Z.to_nat (dg2 / 19 + 3)) BN2) as X.
        rewrite Z2Nat.id in X by (clear -Hd2; Z.div_mod_to_equations; lia). specialize (X BV2). clear -X Hl2 Hd2. Z.div_mod_to_equations. lia. }
      assert (CAP : (len2 + pow5_growth (se - dg2 + 1) <= LM_T /\ 64 * (len2 + pow5_growth (se - dg2 + 1)) + (se - dg2 + 1) <= 3968)%Z).
      { pose proof (pow5_growth_bound (se - dg2 + 1) ltac:(clear -Hpos'; lia)) as PG.
        assert ((se - dg2 + 1) / 27 < 14)%Z by (apply Z.div_lt_upper_bound; clear -Hse Hd2; lia).
        assert (dg2 / 19 < 19)%Z by (apply Z.div_lt_upper_bound; clear -Hse Hd2 Hpos'; lia).
        assert ((se - dg2 + 1) / 135 < 3)%Z by (apply Z.div_lt_upper_bound; clear -Hse Hd2; lia).
        clear -PG Hlen2 Hse Hd2 Hpos' H H0 H1. lia. }
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      assert (UE : bv_unsigned (Z_to_bv 64 (se - dg2 + 1)) = (se - dg2 + 1)%Z) by (apply unsigned_lit; clear -Hse Hd2 Hpos'; lia).
      eapply evt_cut; [ eapply PDC with (ws := ws2) (len := len2) (v := v) (h5 := h5) | post_keep ].
      1:{ destruct (stk_split BSEGS _ _ (bv_unsigned sp - 2672) _ ST02 ltac:(clear; lia)) as (_ & X). exact X. }
      1:{ exact AL. } 1:{ clear -SPLO. lia. } 1:{ exact PR2. } 1:{ exact X2. } 1:{ exact L2. } 1:{ exact LC2. } 1:{ exact Hl2. }
      1:{ exact XAL. } 1:{ exact BN2. }
      1:{ rewrite UE. clear -Hse Hd2. lia. } 1:{ rewrite UE. exact (proj1 CAP). } 1:{ rewrite UE. exact (proj2 CAP). }
      1:{ left. clear -Z0. lia. } 1:{ reflexivity. }
      1:{ exact PRG2. } 1:{ exact PRT2. } 1:{ exact RT2. } 1:{ exact FK52. }
      1:{ clear -KSP. lia. } 1:{ clear -KTP. lia. } 1:{ clear -Z0. lia. } 1:{ clear -Z0. lia. }
      1:{ clear -ZF. lia. } 1:{ clear -XF1 XF2 Hpos HFS1. lia. }
      1:{ eapply rt_disj_sub; [exact RDW | clear; lia | clear; lia]. }
      1:{ eapply rt_disj_sub; [exact RDA | clear; lia | clear; lia]. } 1:{ exact RDF. }
      1:{ exact SHX2. } 1:{ exact SHP2. } 1:{ exact RBX2. } 1:{ exact RBF2. } 1:{ exact SHS2. } 1:{ exact RTX0. }
      (* [comment removed for export] *)
      lazymatch goal with H : munch _ m2 ?m' |- _ => rename m' into m3; rename H into MU3 end.
      lazymatch goal with H : wmono _ m2 m3 |- _ => rename H into WM3 end.
      unfold positive_digit_comp_f_W in MU3.
      step. (* [comment removed for export] *)
      apply evt_done. unfold dcf_f_post.
      do 16 eexists. exists m3. do 2 eexists.
      split; [reflexivity|].
      lazymatch goal with H : u64arr BSEGS m3 (bv_unsigned s8) ?ws |- _ => rename H into X3; rename ws into ws3 end.
      lazymatch goal with H : length ws3 = 62%nat |- _ => rename H into L3 end.
      lazymatch goal with H : rw_cells BSEGS m3 (bv_unsigned s8 + 496) _ |- _ => rename H into LC3 end.
      lazymatch goal with H : stk BSEGS m3 _ _ |- _ => rename H into ST3 end.
      lazymatch goal with H : pristine m3 _ _ |- _ => rename H into PR3 end.
      lazymatch goal with H : RT m3 v |- _ => rename H into RT3 end.
      lazymatch goal with H : fk5_inv m3 _ _ |- _ => rename H into FK53 end.
      assert (FK43 : fk4_nest m3 (rt_FS v) h4 pos0).
      { apply (fk4_transport _ m2 m3 _ _ _ FK42 MU3 WM3); cbn [disjoint_from]; clear -ZF Z0; Z.div_mod_to_equations; lia. }
      refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj PR3 (conj RT3 (conj FK43 FK53)))))))).
      + apply (munch_trans _ m0 m2 m3); [exact MU|]. eapply munch_weaken; [|exact MU3]. unfold dcf_f_W. clear -Hpos. sub_fp_fast.
      + exact (wmono_trans BSEGS _ _ _ WM WM3).
      +
        destruct (stk_split BSEGS _ _ (bv_unsigned sp - 2672) _ ST02 ltac:(clear; lia)) as (STl & _).
        pose proof (stk_transport_disjoint BSEGS _ m2 m3 _ _ STl MU3 WM3 ltac:(dj ZF)) as STl3.
        exact (stk_merge BSEGS _ _ _ _ STl3 ST3 ltac:(clear; lia)).
      + pose proof (rw_cells_transport BSEGS _ m2 m3 _ _ DG2 MU3 WM3 ltac:(cbn [cells_size csize Nat.add]; dj ZF)) as DG3.
        pose proof (stk_of_rw_cells _ _ _ DG3) as X. cbn [cells_size csize Nat.add] in X.
        replace (bv_unsigned sp + 152)%Z with (bv_unsigned sp + 144 + Z.of_nat 8)%Z by (clear; lia). exact X.
      + pose proof (u8arr_transport BSEGS _ m1 m2 _ _ ZX3 MU2 WM2 ltac:(rewrite repeat_length; dj Z0)) as ZX32.
        pose proof (u8arr_transport BSEGS _ m2 m3 _ _ ZX32 MU3 WM3 ltac:(rewrite repeat_length; dj ZF)) as ZX33.
        pose proof (stk_of_u64arr _ _ _ X3) as SA. rewrite L3 in SA.
        pose proof (stk_of_rw_cells _ _ _ LC3) as SB. cbn [cells_size csize Nat.add] in SB.
        pose proof (stk_of_u8arr _ _ _ ZX33) as SC. rewrite repeat_length in SC.
        apply (stk_merge BSEGS _ _ (bv_unsigned s8 + 496) _); [|apply (stk_merge BSEGS _ _ (bv_unsigned s8 + 498) _) | clear; lia].
        * replace (bv_unsigned s8 + 496)%Z with (bv_unsigned s8 + 8 * Z.of_nat 62)%Z by (clear; lia). exact SA.
        * replace (bv_unsigned s8 + 498)%Z with (bv_unsigned s8 + 496 + Z.of_nat 2)%Z by (clear; lia). exact SB.
        * replace (bv_unsigned s8 + 504)%Z with (bv_unsigned s8 + 498 + Z.of_nat 6)%Z by (clear; lia). exact SC.
        * clear; lia.
  Qed.
End Frag.

