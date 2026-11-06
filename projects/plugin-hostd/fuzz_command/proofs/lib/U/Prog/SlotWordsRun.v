(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cjson/cjson_read_fuzzer/lib/A/RTW_q_rec2.v, with its module paths and module names changed; 648 of its 746 lines of code are new or changed and 1953 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/Prog/check_round_trip_runs.v, with its module paths, module names and addresses changed; 219 of its 261 lines of code are new or changed and 704 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/SlotSpec.v, with its addresses changed; 444 of its 464 lines of code are new or changed and 241 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/SlotRuns.v; 353 of its 386 lines of code are new or changed and 431 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import CommandModel rec_code_declared_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import memcpy_c strspn_c strcspn_c SlotSpec CommandTac SlotWords.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* The inlined words_of of LLVMFuzzerTestOneInput (ubsan) from the third malloc's return (0x14200) to the splitter
   loop: the null checks, the copy of the message's first line into text, the trim loop, the copy into copy. *)


Lemma swr_upd_bytes1 : forall (C : list byte) j b, (j < length C)%nat -> upd_bytes C j [b] = upd C j b.
Proof.
  intros C j b H. unfold upd_bytes. rewrite upd_firstn_skipn by exact H. cbn [length app].
  replace (j + 1)%nat with (S j) by lia. reflexivity.
Qed.

(* The text buffer during the trim loop: the first j bytes of the line, then zeros. *)
Definition tz (U : list byte) (j : nat) : list byte := firstn j U ++ repeat (Z_to_bv 8 0) (length U - j + 1).

Lemma tz_len : forall U j, (j <= length U)%nat -> length (tz U j) = S (length U).
Proof. intros U j H. unfold tz. rewrite length_app, firstn_length_le, repeat_length by lia. lia. Qed.

Lemma tz_nth_lt : forall U j j', (j' < j)%nat -> (j <= length U)%nat -> nth_error (tz U j) j' = nth_error U j'.
Proof.
  intros U j j' H1 H2. unfold tz. rewrite nth_error_app1 by (rewrite firstn_length_le by lia; lia).
  apply sw_nth_firstn. exact H1.
Qed.

Lemma tz_upd : forall U j, (1 <= j <= length U)%nat -> upd (tz U j) (j - 1) (Z_to_bv 8 0) = tz U (j - 1).
Proof.
  intros U j H. unfold tz.
  destruct (nth_error U (j - 1)) as [x|] eqn:Ex; [|apply nth_error_None in Ex; lia].
  replace j with (S (j - 1)) at 1 by lia. rewrite (sw_firstn_snoc U (j - 1) x Ex), <- app_assoc. cbn [app].
  replace (j - 1)%nat with (length (firstn (j - 1) U)) at 2 by (rewrite firstn_length_le by lia; reflexivity).
  rewrite sw_upd_at. replace (length U - (j - 1) + 1)%nat with (S (length U - j + 1)) by lia. reflexivity.
Qed.

Lemma tz_full : forall U, tz U (length U) = U ++ [Z_to_bv 8 0].
Proof. intros U. unfold tz. rewrite firstn_all, Nat.sub_diag. reflexivity. Qed.

Lemma tz_firstn : forall U j, (j <= length U)%nat -> firstn (j + 1) (tz U j) = firstn j U ++ [Z_to_bv 8 0].
Proof.
  intros U j H. unfold tz. rewrite firstn_app, firstn_length_le by lia.
  rewrite firstn_all2 by (rewrite firstn_length_le by lia; lia).
  replace (j + 1 - j)%nat with 1%nat by lia. replace (length U - j + 1)%nat with (S (length U - j)) by lia.
  reflexivity.
Qed.

Lemma sw_cells_split : forall m A cs1 cs2, rw_cells rsegs m A (cs1 ++ cs2) ->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2 [[Hwf Hb] Hw].
  apply cells_wf_app in Hwf. destruct Hwf as [W1 W2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb. destruct Hb as [B1 B2].
  rewrite cells_bytes_length in B2 by exact W1.
  destruct Hw as (Ha & Hn & Hw). rewrite cells_size_app in Hn, Hw.
  split.
  - split; [split; assumption|]. split; [lia|]. split; [lia|]. intros i Hi. apply Hw. lia.
  - split; [split; assumption|]. split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia. apply Hw. lia.
Qed.

Lemma sw_trim_line : forall U j x, nth_error U j = Some x -> Verbs.is_trail x = false ->
  Verbs.trim (firstn (S j) U) = firstn (S j) U.
Proof. intros U j x Ex Hx. rewrite (sw_firstn_snoc U j x Ex), sw_trim_snoc, Hx. reflexivity. Qed.

Lemma sw_trim_step : forall U j x, nth_error U j = Some x -> Verbs.is_trail x = true ->
  Verbs.trim (firstn (S j) U) = Verbs.trim (firstn j U).
Proof. intros U j x Ex Hx. rewrite (sw_firstn_snoc U j x Ex), sw_trim_snoc, Hx. reflexivity. Qed.

Ltac sw_eqv2 :=
  unfold wa;
  first [ reflexivity | f_equal; lia | apply bv_eq; repeat rewrite unsigned_lit by lia; lia ].


(* Simplify the 64-bit literals whose range lia proves, then decide a branch or slt/sltu condition by lia (the UBSan
   checks of the splitter). *)
Ltac sw_zsm := repeat first [
    match goal with |- context [sx32 (Z_to_bv 64 ?z)] => rewrite (sw_sx32_small z) by lia end
  | match goal with |- context [bv_wrap 64 ?z] => rewrite (sw_wrap_small z) by lia end
  | match goal with |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) by lia end
  | match goal with |- context [bv_signed (Z_to_bv 64 ?z)] => rewrite (sw_signed_small z) by lia end
  | match goal with |- context [bv_swrap 32 ?z] => rewrite (sw_swrap_small z) by lia end
  | match goal with |- context [Z.lxor ?x 18446744073709551615] => rewrite (zb_lxor_ones x) by lia end
  | match goal with |- context [Z.land ?x 7] => rewrite (sw_land7 x) by lia end
  | match goal with |- context [Z.shiftl ?x 3] => rewrite (sw_shl3 x) end
  | rewrite Z.lxor_0_r | rewrite Z.lxor_0_l ].
Ltac sw_bc := unfold c_ltu, c_eq, c_lts, bv_ltu, bv_eqb, bv_lts, bv_leu, zsig; cbn [negb]; sw_zsm; fold_lit_ux;
  solve_cond_rec.
Ltac sw_fix_ifs := unfold v_sltiu, v_sltu, v_slt, v_slti;
  repeat match goal with |- context [if ?c then _ else _] =>
    first [ replace c with true by (symmetry; sw_bc) | replace c with false by (symmetry; sw_bc) ]; cbv iota end.
Ltac sw_st := step; sw_zsm; sw_fix_ifs.

Section Run.
Variables (sp gp tp s2 s3 s5 s6 s7 s10 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte)
  (lo src len text copy arr : Z) (M : list byte) (can : word) (jsv : list byte).

Notation SP := (bv_unsigned sp).
Notation L0 := (strnlen_res len M).
Notation ws := (Verbs.words (Verbs.line M)).
Notation LN := (Verbs.line M).
Notation U := (Verbs.upto0 M).
Notation W0 := [(text, text + strnlen_res len M + 1); (copy, copy + strnlen_res len M + 1);
                (arr, arr + arr_size (strnlen_res len M)); (bv_unsigned sp - 96, bv_unsigned sp + 56)].
Notation POST := (sw_post sp gp tp s2 s3 s5 s6 s7 s10 F fc m0 lo src len text copy arr M jsv).

Hypothesis H_lo : 0x54f98 <= lo.
Hypothesis H_LOS : lo + 96 <= SP.
Hypothesis H_SPH : SP + 160 <= 2 ^ 64.
Hypothesis H_len : 0 <= len <= 8192.
Hypothesis H_src : 0 <= src /\ src + len <= lo.
Hypothesis H_L0 : 0 <= L0 <= len.
Hypothesis H_tx : 0 < text /\ text + L0 + 1 <= lo.
Hypothesis H_cp : 0 < copy /\ copy + L0 + 1 <= lo.
Hypothesis H_ar : 0 < arr /\ arr + arr_size L0 <= lo.
Hypothesis H_AS : arr_size L0 = 8 * (L0 / 2) + 16.
Hypothesis SSPN : strspn_contract.
Hypothesis SCSPN : strcspn_contract.
Hypothesis MEMC : memcpy_contract.
Hypothesis H_M : Z.of_nat (length M) = len.
Hypothesis H_txi : text + L0 + 1 <= 0x10000 \/ 0x54f98 <= text.
Hypothesis H_cpi : copy + L0 + 1 <= 0x10000 \/ 0x54f98 <= copy.
Hypothesis H_ari : arr + arr_size L0 <= 0x10000 \/ 0x54f98 <= arr.
Hypothesis H_d1 : text + L0 + 1 <= copy \/ copy + L0 + 1 <= text.
Hypothesis H_d2 : arr + arr_size L0 <= text \/ text + L0 + 1 <= arr.
Hypothesis H_d3 : arr + arr_size L0 <= copy \/ copy + L0 + 1 <= arr.
Hypothesis H_d4 : src + len <= text \/ text + L0 + 1 <= src.
(* The pointer array is 8-aligned (the check at 0x14334): malloc's results are 16-aligned (U Contract.v,
   malloc_contract: res mod 16 = 0). *)
Hypothesis H_al : arr mod 8 = 0.

Lemma swr_L0 : L0 = Z.of_nat (length U).
Proof. rewrite <- H_M. apply sw_strnlen_upto0. Qed.

(* 0x142b0: copy the trimmed line (and its 0) into copy, w.n := 0, then the splitter. *)
Lemma sw_tail : forall m1 ra' t0' t1' t2' a0' a1' a2v a3' a4' a5' a6' a7' s4' t3' t4' t5' t6' T jc ja j2 j3,
  a2v = Z_to_bv 64 (Z.of_nat (length LN) + 1) ->
  munch W0 m0 m1 -> wmono rsegs m0 m1 -> mem_inv rsegs m1 -> stk rsegs m1 lo SP ->
  rw_cells rsegs m1 SP (LOC0 jsv) ->
  rw_cells rsegs m1 (SP + 24) [C8 (Z_to_bv 64 text); C8 (Z_to_bv 64 copy); C8 (Z_to_bv 64 arr); CB 4 j2; CB 4 j3] ->
  u8arr rsegs m1 text T -> length T = Z.to_nat (L0 + 1) -> firstn (length LN + 1) T = LN ++ [Z_to_bv 8 0] ->
  u8arr rsegs m1 copy jc -> length jc = Z.to_nat (L0 + 1) ->
  u8arr rsegs m1 arr ja -> length ja = Z.to_nat (arr_size L0) ->
  bytes_at rsegs m1 strspn_c.SSP_GOT (le8 (Z_to_bv 64 strspn_c.SSP_GUARD)) ->
  bytes_at rsegs m1 strspn_c.SSP_GUARD (le8 can) ->
  evt rsegs POST (MS (mkR ra' sp gp tp t0' t1' t2' (Z_to_bv 64 src) (Z_to_bv 64 len) a0' a1' a2v a3' a4' a5' a6' a7'
       s2 s3 s4' s5 s6 s7 (Z_to_bv 64 MASK) (Z_to_bv 64 32) s10 (Z_to_bv 64 (2 ^ 64 - 1))
       t3' t4' t5' t6') F (Z_to_bv 64 0x142b0) fc None m1 (seg_rom rsegs)).
Proof.
  intros m1 ra' t0' t1' t2' a0' a1' a2v a3' a4' a5' a6' a7' s4' t3' t4' t5' t6' T jc ja j2 j3
    -> MU WM MI ST FR0 FR1 TX LT FT CPc LCc AR LA G1 G2.
  pose proof swr_L0 as EL0. pose proof (sw_line_le M) as HLL.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold strspn_c.SSP_GOT, strspn_c.SSP_GUARD in G1, G2. unfold LOC0 in FR0.
  assert (NZL : forall b, In b LN -> bv_unsigned b <> 0) by (intros b Hb; exact (sw_line_nz M b Hb)).
  (* the source: the first length LN + 1 bytes of text *)
  assert (BT : bytes_at rsegs m1 text (LN ++ [Z_to_bv 8 0])).
  { rewrite <- FT. pose proof (proj1 TX) as TB. rewrite <- (firstn_skipn (length LN + 1) T) in TB.
    apply bytes_at_app in TB. exact (proj1 TB). }
  (* the destination: the first length LN + 1 bytes of copy *)
  assert (CPs : u8arr rsegs m1 copy (firstn (length LN + 1) jc ++ skipn (length LN + 1) jc))
    by (rewrite firstn_skipn; exact CPc).
  clear CPc. apply sw_u8arr_app in CPs as [CPa CPb].
  rewrite firstn_length_le in CPb by lia.
  apply rw_cells_of_u8arr in CPa. rewrite firstn_length_le in CPa by lia.
  assert (CPa' : rw_cells rsegs m1 copy [CB (Z.to_nat (Z.of_nat (length LN) + 1)) (firstn (length LN + 1) jc)])
    by (replace (Z.to_nat (Z.of_nat (length LN) + 1)) with (length LN + 1)%nat by lia; exact CPa).
  clear CPa.
  do 3 step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply (MEMC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                (LN ++ [Z_to_bv 8 0]) (firstn (length LN + 1) jc));
      rewrite ?unsigned_lit by lia;
      [ exact BT | rewrite length_app; cbn [length]; lia | exact CPa' | lia | assumption ]
    | let ms' := fresh "ms'" in let PO := fresh "PO" in
      intros ms' PO; unfold memcpy_post in PO; rewrite ?unsigned_lit in PO by lia; revert ms' PO;
      post_call rsegs mm ]
  end.
  try (match goal with H : stk _ _ _ _ |- _ => rename H into ST end).
  (* copy holds the line, its 0, then the rest of jc *)
  set (C := (LN ++ [Z_to_bv 8 0]) ++ skipn (length LN + 1) jc).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (CP : u8arr rsegs mm copy C)
  end.
  { unfold C. apply sw_u8arr_app. split.
    - match goal with H : rw_cells _ _ copy [CB _ _] |- _ => eapply u8arr_of_rw_cells; exact H end.
    - rewrite length_app. cbn [length]. exact CPb. }
  assert (LC : length C = Z.to_nat (L0 + 1)).
  { unfold C. rewrite !length_app, length_skipn. cbn [length]. lia. }
  assert (CF : forall j, (0 <= j <= length LN)%nat -> nth_error C j = nth_error (LN ++ [Z_to_bv 8 0]) j).
  { intros j Hj. unfold C. apply nth_error_app1. rewrite length_app. cbn [length]. lia. }
  clearbody C.
  (* 0x142bc: s4 := copy, w.n := 0, the null check of copy at 0x142c4, its first byte *)
  step. step. sw_st.
  destruct (sw_nth_z LN 0 NZL ltac:(lia)) as (b0 & Eb0 & Hb0).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (RD : ov_read_bytes rsegs mm (wa (copy + Z.of_nat 0)) 1 = Some [b0])
      by (apply (u8arr_read rsegs mm copy C (Z.of_nat 0) b0);
          [assumption | rewrite Nat2Z.id, CF by lia; exact Eb0 | lia | reflexivity])
  end.
  step. clear RD.
  pose proof (bv_unsigned_in_range 8 b0) as RB0. unfold bv_modulus in RB0. cbn in RB0.
  step. if_cases HZ0; zify_cond HZ0; rewrite ?unsigned_lit in HZ0 by lia.
  - (* an empty line: no words, the exit at 0x14378 *)
    assert (EL : LN = []) by (apply length_zero_iff_nil; symmetry; apply Hb0; exact HZ0).
    assert (EW : length ws = 0%nat) by (rewrite EL; reflexivity).
    eapply sw_fin0 with (wp := []); try eassumption; [rewrite EW; eassumption|].
    split; [rewrite EW; reflexivity|]. split; [rewrite EW; reflexivity|].
    intros k p w Ep. destruct k; discriminate.
  - (* the splitter loop from the line's start *)
    eapply (sw_loop sp gp tp s2 s3 s5 s6 s7 s10 F fc m0 lo src len text copy arr M can jsv H_lo H_LOS H_SPH H_len
              H_src H_L0 H_tx H_cp H_ar H_AS SSPN SCSPN H_M H_txi H_cpi H_ari H_d1 H_d2 H_d3 H_d4 H_al
              (length LN) 0 0 _ _ C _ []);
      [ lia | lia | lia | reflexivity | sw_eqv2 | try eassumption .. ].
    all: try reflexivity.
    all: try lia.
    all: try (intros j Hj; apply CF; lia).
    all: try (intros k' p w Ep; destruct k'; discriminate).
Qed.

(* 0x14254: the trim loop at byte j - 1 of the line (text holds tz U j, s4 = j - 1). *)
Lemma sw_trim : forall (j : nat) m1 ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4v t3' t4' t5' t6' jc ja j2 j3,
  (1 <= j <= length U)%nat -> Verbs.trim U = Verbs.trim (firstn j U) ->
  s4v = Z_to_bv 64 (Z.of_nat j - 1) ->
  munch W0 m0 m1 -> wmono rsegs m0 m1 -> mem_inv rsegs m1 -> stk rsegs m1 lo SP ->
  rw_cells rsegs m1 SP (LOC0 jsv) ->
  rw_cells rsegs m1 (SP + 24) [C8 (Z_to_bv 64 text); C8 (Z_to_bv 64 copy); C8 (Z_to_bv 64 arr); CB 4 j2; CB 4 j3] ->
  u8arr rsegs m1 text (tz U j) ->
  u8arr rsegs m1 copy jc -> length jc = Z.to_nat (L0 + 1) ->
  u8arr rsegs m1 arr ja -> length ja = Z.to_nat (arr_size L0) ->
  bytes_at rsegs m1 strspn_c.SSP_GOT (le8 (Z_to_bv 64 strspn_c.SSP_GUARD)) ->
  bytes_at rsegs m1 strspn_c.SSP_GUARD (le8 can) ->
  evt rsegs POST (MS (mkR ra' sp gp tp t0' t1' t2' (Z_to_bv 64 src) (Z_to_bv 64 len) a0' a1' a2' a3' a4' a5' a6' a7'
       s2 s3 s4v s5 s6 s7 (Z_to_bv 64 MASK) (Z_to_bv 64 32) s10 (Z_to_bv 64 (2 ^ 64 - 1))
       t3' t4' t5' t6') F (Z_to_bv 64 0x14254) fc None m1 (seg_rom rsegs)).
Proof.
  induction j as [|j IH];
    intros m1 ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4v t3' t4' t5' t6' jc ja j2 j3
      Hj HT -> MU WM MI ST FR0 FR1 TX CP LC AR LA G1 G2; [lia|].
  pose proof swr_L0 as EL0.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold strspn_c.SSP_GOT, strspn_c.SSP_GUARD in G1, G2. unfold LOC0 in FR0.
  pose proof (tz_len U (S j) ltac:(lia)) as LT.
  destruct (nth_error U j) as [x|] eqn:Ex; [|apply nth_error_None in Ex; lia].
  (* 0x14254: &text[j], the pointer checks at 0x1425c .. 0x14270 *)
  do 8 sw_st.
  assert (RD : ov_read_bytes rsegs m1 (wa (text + Z.of_nat j)) 1 = Some [x])
    by (apply (u8arr_read rsegs m1 text (tz U (S j)) (Z.of_nat j) x);
        [assumption | rewrite Nat2Z.id, tz_nth_lt by lia; exact Ex | lia | reflexivity]).
  step. clear RD.
  pose proof (bv_unsigned_in_range 8 x) as RX. unfold bv_modulus in RX. cbn in RX.
  step. if_cases HB; zify_cond HB; rewrite ?unsigned_lit in HB by lia.
  - (* above 32: not a trailing byte, the line is the first j + 1 bytes *)
    assert (Hnt : Verbs.is_trail x = false) by (rewrite sw_is_trail_z; apply sw_trail_big; lia).
    assert (ELN : LN = firstn (S j) U) by (unfold Verbs.line; rewrite HT; exact (sw_trim_line U j x Ex Hnt)).
    step. step.
    eapply sw_tail; [ | try eassumption .. ].
    all: try (rewrite ELN, firstn_length_le by lia; sw_eqv2).
    all: try (rewrite LT, EL0; lia).
    all: try (rewrite ELN, firstn_length_le by lia; apply tz_firstn; lia).
  - step. step. step. if_cases HM; zify_cond HM;
      replace (MASK mod 18446744073709551616) with 4294977024 in HM by (unfold MASK; reflexivity);
      rewrite sw_trail_mask in HM by lia.
    + (* not a trailing byte *)
      assert (Hnt : Verbs.is_trail x = false).
      { rewrite sw_is_trail_z. destruct (sw_trail_z (bv_unsigned x)); [discriminate | reflexivity]. }
      assert (ELN : LN = firstn (S j) U) by (unfold Verbs.line; rewrite HT; exact (sw_trim_line U j x Ex Hnt)).
      step. step.
      eapply sw_tail; [ | try eassumption .. ].
      all: try (rewrite ELN, firstn_length_le by lia; sw_eqv2).
      all: try (rewrite LT, EL0; lia).
      all: try (rewrite ELN, firstn_length_le by lia; apply tz_firstn; lia).
    + (* a trailing byte: zero it and go down (the null check at 0x14288) *)
      assert (Htr : Verbs.is_trail x = true).
      { rewrite sw_is_trail_z. destruct (sw_trail_z (bv_unsigned x)); [reflexivity | exfalso; apply HM; reflexivity]. }
      assert (HT' : Verbs.trim U = Verbs.trim (firstn j U)) by (rewrite HT; exact (sw_trim_step U j x Ex Htr)).
      sw_st. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (SOK : store_ok rsegs mm (wa (text + Z.of_nat j)) 1 = true)
          by (apply (u8arr_store_ok_n rsegs mm text (tz U (S j)) (Z.of_nat j) 1);
              [assumption | lia | rewrite LT; lia | reflexivity])
      end.
      step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm ?a ?bs) _) =>
        replace a with (wa (text + Z.of_nat j)) by (unfold wa; f_equal; lia);
        assert (EB0 : bs = [Z_to_bv 8 0]) by (apply StrFun.map_unsigned_inj; vm_compute; reflexivity);
        pose proof (u8arr_write_bytes rsegs mm text (tz U (S j)) (Z.of_nat j) bs ltac:(assumption) ltac:(lia)
                      ltac:(rewrite EB0, LT; cbn [length]; lia)) as TX2;
        rewrite EB0 in TX2 |- *
      end.
      store_done.
      assert (TZ : upd_bytes (tz U (S j)) (Z.to_nat (Z.of_nat j)) [Z_to_bv 8 0] = tz U j).
      { rewrite Nat2Z.id. pose proof (tz_upd U (S j) ltac:(lia)) as TU. replace (S j - 1)%nat with j in TU by lia.
        transitivity (upd (tz U (S j)) j (Z_to_bv 8 0)); [apply swr_upd_bytes1; rewrite LT; lia | exact TU]. }
      rewrite TZ in TX2. clear TZ.
      destruct j as [|j'].
      * (* the whole line was trailing bytes: s4 = -1 ends the loop (0x14294) *)
        assert (ELN : LN = []) by (unfold Verbs.line; rewrite HT'; reflexivity).
        pose proof (tz_len U 0 ltac:(lia)) as LT0.
        step.
        lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
          replace c with false by (vm_compute; reflexivity); cbv iota
        end.
        step. step. step.
        eapply sw_tail; [ | try eassumption .. ].
        all: try (rewrite ELN; sw_eqv2).
        all: try (rewrite LT0, EL0; lia).
        all: try (rewrite ELN; apply (tz_firstn U 0); lia).
      * (* more bytes: the next round *)
        sw_st.
        eapply IH; [lia | exact HT' | sw_eqv2 | try eassumption ..].
        all: try lia.
Qed.

(* 0x14200 (the third malloc returned arr): w.words := arr, the null checks of text, copy, arr (to stop_fn at
   0x1443c), text := the line up to its 0, the trim loop, copy, the splitter: the run ends at check_reply's call
   (sw_post). *)
Lemma sw_run : forall ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' jt jc ja jw,
  mem_inv rsegs m0 -> stk rsegs m0 lo SP ->
  bytes_at rsegs m0 src M ->
  u8arr rsegs m0 text jt -> length jt = Z.to_nat (L0 + 1) ->
  u8arr rsegs m0 copy jc -> length jc = Z.to_nat (L0 + 1) ->
  u8arr rsegs m0 arr ja -> length ja = Z.to_nat (arr_size L0) ->
  bytes_at rsegs m0 strspn_c.SSP_GOT (le8 (Z_to_bv 64 strspn_c.SSP_GUARD)) ->
  bytes_at rsegs m0 strspn_c.SSP_GUARD (le8 can) ->
  rw_cells rsegs m0 SP (LOC0 jsv) ->
  rw_cells rsegs m0 (SP + 24) [C8 (Z_to_bv 64 text); C8 (Z_to_bv 64 copy); CB 16 jw] ->
  evt rsegs POST (MS (mkR ra' sp gp tp t0' t1' t2' (Z_to_bv 64 src) (Z_to_bv 64 len) (Z_to_bv 64 arr) a1' a2' a3' a4'
       a5' a6' a7' s2 s3 (Z_to_bv 64 L0) s5 s6 s7 (Z_to_bv 64 MASK) (Z_to_bv 64 32) s10 (Z_to_bv 64 (2 ^ 64 - 1))
       t3' t4' t5' t6') F (Z_to_bv 64 0x14200) fc None m0 (seg_rom rsegs)).
Proof.
  intros ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' jt jc ja jw
    MI ST SRC TX LT CP LC AR LA G1 G2 FR0 FR1.
  pose proof swr_L0 as EL0.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold strspn_c.SSP_GOT, strspn_c.SSP_GUARD in G1, G2. unfold LOC0 in FR0.
  pose proof (munch_refl W0 m0) as MU. pose proof (wmono_refl rsegs m0) as WM.
  apply (rw_cells_split_CB rsegs m0 (SP + 24) [C8 (Z_to_bv 64 text); C8 (Z_to_bv 64 copy)] 16 jw [] [8; 4; 4]%nat)
    in FR1; [| reflexivity].
  cbn [mk_CB_cells app] in FR1.
  (* the message's line: its bytes up to the first 0 *)
  assert (EU : firstn (length U) M = U) by (unfold Verbs.upto0; symmetry; apply sw_upto_prefix).
  assert (BS : bytes_at rsegs m0 src U).
  { pose proof SRC as S0. rewrite <- (firstn_skipn (length U) M) in S0. apply bytes_at_app in S0.
    rewrite EU in S0. exact (proj1 S0). }
  assert (HUM : (length U <= length M)%nat) by (pose proof (length_firstn (length U) M) as HF; rewrite EU in HF; lia).
  assert (TXs : u8arr rsegs m0 text (firstn (length U) jt ++ skipn (length U) jt)) by (rewrite firstn_skipn; exact TX).
  clear TX. apply sw_u8arr_app in TXs as [TXa TXb].
  rewrite firstn_length_le in TXb by lia. replace (text + Z.of_nat (length U)) with (text + L0) in TXb by lia.
  assert (Hsk : exists z, skipn (length U) jt = [z]).
  { destruct (skipn (length U) jt) as [|z [|z' r]] eqn:Esk.
    - apply (f_equal (@length _)) in Esk. rewrite length_skipn in Esk. cbn [length] in Esk. lia.
    - exists z. reflexivity.
    - apply (f_equal (@length _)) in Esk. rewrite length_skipn in Esk. cbn [length] in Esk. lia. }
  destruct Hsk as [z Esk]. rewrite Esk in TXb.
  apply rw_cells_of_u8arr in TXa. rewrite firstn_length_le in TXa by lia.
  assert (TXa' : rw_cells rsegs m0 text [CB (Z.to_nat L0) (firstn (length U) jt)])
    by (replace (Z.to_nat L0) with (length U) by lia; exact TXa).
  clear TXa.
  (* 0x14200: a1 := text, w.words := arr; the null checks 0x14208, 0x14210, 0x14214 *)
  step. step.
  step. if_cases HZ1; zify_cond HZ1; rewrite ?unsigned_lit in HZ1 by lia; [exfalso; lia|].
  step. step. if_cases HZ2; zify_cond HZ2; rewrite ?unsigned_lit in HZ2 by lia; [exfalso; lia|].
  step. if_cases HZ3; zify_cond HZ3; rewrite ?unsigned_lit in HZ3 by lia; [exfalso; lia|].
  do 4 step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply (MEMC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ U (firstn (length U) jt));
      rewrite ?unsigned_lit by lia;
      [ exact BS | lia | exact TXa' | lia | assumption ]
    | let ms' := fresh "ms'" in let PO := fresh "PO" in
      intros ms' PO; unfold memcpy_post in PO; rewrite ?unsigned_lit in PO by lia; revert ms' PO;
      post_call rsegs mm ]
  end.
  try (match goal with H : stk _ _ _ _ |- _ => rename H into ST end).
  (* 0x14228: &text[L0], the pointer checks 0x14230 .. 0x14244, text[L0] := 0 *)
  do 8 sw_st.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (SOK : store_ok rsegs mm (wa (text + L0)) 1 = true)
      by (apply (u8arr_store_ok_n rsegs mm (text + L0) [z] 0 1);
          [assumption | lia | cbn [length]; lia | unfold wa; f_equal; lia])
  end.
  step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm ?a ?bs) _) =>
    replace a with (wa (text + L0 + 0)) by (unfold wa; f_equal; lia);
    assert (EB0 : bs = [Z_to_bv 8 0]) by (apply StrFun.map_unsigned_inj; vm_compute; reflexivity);
    pose proof (u8arr_write_bytes rsegs mm (text + L0) [z] 0 bs ltac:(assumption)
                  ltac:(lia) ltac:(rewrite EB0; cbn [length]; lia)) as TX0;
    rewrite EB0 in TX0 |- *
  end.
  store_done.
  assert (E1 : upd_bytes [z] (Z.to_nat 0) [Z_to_bv 8 0] = [Z_to_bv 8 0]) by reflexivity.
  rewrite E1 in TX0. clear E1. rewrite EL0 in TX0.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (TX : u8arr rsegs mm text (tz U (length U)))
  end.
  { rewrite tz_full. apply sw_u8arr_app. split; [| exact TX0].
    match goal with H : rw_cells _ _ text [CB _ _] |- _ => eapply u8arr_of_rw_cells; exact H end. }
  clear TX0.
  pose proof (tz_len U (length U) ltac:(lia)) as LTz.
  step. if_cases HZ4; zify_cond HZ4; rewrite ?unsigned_lit in HZ4 by lia.
  - (* an empty line (0x142a0) *)
    assert (HU0 : U = []) by (apply length_zero_iff_nil; lia).
    assert (ELN : LN = []) by (unfold Verbs.line; rewrite HU0; reflexivity).
    step. step.
    eapply sw_tail; [ | try eassumption .. ].
    all: try (rewrite ELN; sw_eqv2).
    all: try (rewrite LTz, EL0; lia).
    all: try (rewrite ELN, HU0; reflexivity).
  - (* the trim loop from the line's last byte *)
    step.
    eapply (sw_trim (length U)); [ | | | try eassumption .. ].
    + lia.
    + rewrite firstn_all. reflexivity.
    + f_equal. lia.
Qed.

End Run.
