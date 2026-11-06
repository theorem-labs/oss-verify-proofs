From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts CommandModel rec_code_declared_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import memcpy_c strspn_c strcspn_c SlotSpec CommandTac
  SlotWords.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* The inlined words_of from the third malloc's return (0x141c8) to the splitter loop: the copy of the message's
   first line into text, the trim loop, the copy into copy. *)

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

Section Run.
Variables (ra sp gp tp s2 s3 s6 s8 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte)
  (lo src len text copy arr : Z) (M : list byte) (can : word).

Notation SP := (bv_unsigned sp).
Notation L0 := (strnlen_res len M).
Notation ws := (Verbs.words (Verbs.line M)).
Notation LN := (Verbs.line M).
Notation U := (Verbs.upto0 M).
Notation W0 := [(text, text + strnlen_res len M + 1); (copy, copy + strnlen_res len M + 1);
                (arr, arr + arr_size (strnlen_res len M)); (bv_unsigned sp - 96, bv_unsigned sp + 72)].
Notation POST := (sw_post sp gp tp s2 s3 s6 s8 F fc m0 lo src len text copy arr M).

Hypothesis H_lo : 0x54cb8 <= lo.
Hypothesis H_LOS : lo + 96 <= SP.
Hypothesis H_SPH : SP + 176 <= 2 ^ 64.
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
Hypothesis H_txi : text + L0 + 1 <= 0x10000 \/ 0x54cb8 <= text.
Hypothesis H_cpi : copy + L0 + 1 <= 0x10000 \/ 0x54cb8 <= copy.
Hypothesis H_ari : arr + arr_size L0 <= 0x10000 \/ 0x54cb8 <= arr.
Hypothesis H_d1 : text + L0 + 1 <= copy \/ copy + L0 + 1 <= text.
Hypothesis H_d2 : arr + arr_size L0 <= text \/ text + L0 + 1 <= arr.
Hypothesis H_d3 : arr + arr_size L0 <= copy \/ copy + L0 + 1 <= arr.
Hypothesis H_d4 : src + len <= text \/ text + L0 + 1 <= src.

Lemma swr_L0 : L0 = Z.of_nat (length U).
Proof. rewrite <- H_M. apply sw_strnlen_upto0. Qed.

(* 0x1422c: copy the trimmed line (and its 0) into copy, then the splitter. *)
Lemma sw_tail : forall m1 ra' t0' t1' t2' a0' a1' a2v a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' T jc ja jsv j2 j3,
  a2v = Z_to_bv 64 (Z.of_nat (length LN) + 1) ->
  munch W0 m0 m1 -> wmono rsegs m0 m1 -> mem_inv rsegs m1 -> stk rsegs m1 lo SP ->
  rw_cells rsegs m1 SP (LOC0 jsv) ->
  rw_cells rsegs m1 (SP + 40) [C8 (Z_to_bv 64 text); C8 (Z_to_bv 64 copy); C8 (Z_to_bv 64 arr); CB 4 j2; CB 4 j3] ->
  u8arr rsegs m1 text T -> length T = Z.to_nat (L0 + 1) -> firstn (length LN + 1) T = LN ++ [Z_to_bv 8 0] ->
  u8arr rsegs m1 copy jc -> length jc = Z.to_nat (L0 + 1) ->
  u8arr rsegs m1 arr ja -> length ja = Z.to_nat (arr_size L0) ->
  bytes_at rsegs m1 strspn_c.SSP_GOT (le8 (Z_to_bv 64 strspn_c.SSP_GUARD)) ->
  bytes_at rsegs m1 strspn_c.SSP_GUARD (le8 can) ->
  evt rsegs POST (MS (mkR ra' sp gp tp t0' t1' t2' (Z_to_bv 64 src) (Z_to_bv 64 len) a0' a1' a2v a3' a4' a5' a6' a7'
       s2 s3 (Z_to_bv 64 text) (Z_to_bv 64 copy) s6 s7' s8 (Z_to_bv 64 MASK) (Z_to_bv 64 arr) (Z_to_bv 64 32)
       t3' t4' t5' t6') F (Z_to_bv 64 0x1422c) fc None m1 (seg_rom rsegs)).
Proof.
  intros m1 ra' t0' t1' t2' a0' a1' a2v a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' T jc ja jsv j2 j3
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
  destruct (sw_nth_z LN 0 NZL ltac:(lia)) as (b0 & Eb0 & Hb0).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (RD : ov_read_bytes rsegs mm (wa (copy + Z.of_nat 0)) 1 = Some [b0])
      by (apply (u8arr_read rsegs mm copy C (Z.of_nat 0) b0);
          [assumption | rewrite Nat2Z.id, CF by lia; exact Eb0 | lia | reflexivity])
  end.
  step. clear RD.
  step.
  pose proof (bv_unsigned_in_range 8 b0) as RB0. unfold bv_modulus in RB0. cbn in RB0.
  step. if_cases HZ0; zify_cond HZ0; rewrite ?unsigned_lit in HZ0 by lia.
  - (* an empty line: no words *)
    assert (EL : LN = []) by (apply length_zero_iff_nil; symmetry; apply Hb0; exact HZ0).
    assert (EW : length ws = 0%nat) by (rewrite EL; reflexivity).
    eapply sw_fin0 with (wp := []); try eassumption.
    all: try (unfold LOC0; eassumption).
    all: try (rewrite EW; eassumption).
    all: try (split; [rewrite EW; reflexivity|]; split; [rewrite EW; reflexivity|];
              intros k p w Ep; destruct k; discriminate).
  - (* the splitter loop from the line's start *)
    match goal with H : rw_cells _ _ SP [C8 _; C8 _; C8 _; CB 16 _] |- _ =>
      apply (rw_cells_split_CB rsegs _ SP [C8 (Z_to_bv 64 58); C8 (Z_to_bv 64 REC_CODES); C8 (Z_to_bv 64 G_REC)]
               16 _ [] [8; 8]%nat) in H; [| reflexivity];
      cbn [mk_CB_cells app] in H
    end.
    step. step. step. step. step.
    eapply (sw_loop sp gp tp s2 s3 s6 s8 F fc m0 lo src len text copy arr M can H_lo H_LOS H_SPH H_len H_src H_L0
              H_tx H_cp H_ar H_AS SSPN SCSPN H_M H_txi H_cpi H_ari H_d1 H_d2 H_d3 (length LN) 0 0 _ _ C _ []);
      [ lia | lia | lia | reflexivity | sw_eqv2 | sw_eqv2 | sw_eqv2 | try eassumption .. ].
    all: try (intros j Hj; apply CF; lia).
    all: try reflexivity.
    all: try lia.
    all: try (intros j Hj; apply CF; lia).
    all: try (intros k' p w Ep; destruct k'; discriminate).
Qed.

(* 0x141fc: the trim loop at byte j - 1 of the line (text holds tz U j). *)
Lemma sw_trim : forall (j : nat) m1 ra' t0' t1' t2' a0v a1' a2' a3' a4' a5' a6' a7' s7v t3' t4' t5' t6' jc ja jsv j2 j3,
  (1 <= j <= length U)%nat -> Verbs.trim U = Verbs.trim (firstn j U) ->
  a0v = Z_to_bv 64 (text + Z.of_nat j - 1) -> s7v = Z_to_bv 64 (Z.of_nat j) ->
  munch W0 m0 m1 -> wmono rsegs m0 m1 -> mem_inv rsegs m1 -> stk rsegs m1 lo SP ->
  rw_cells rsegs m1 SP (LOC0 jsv) ->
  rw_cells rsegs m1 (SP + 40) [C8 (Z_to_bv 64 text); C8 (Z_to_bv 64 copy); C8 (Z_to_bv 64 arr); CB 4 j2; CB 4 j3] ->
  u8arr rsegs m1 text (tz U j) ->
  u8arr rsegs m1 copy jc -> length jc = Z.to_nat (L0 + 1) ->
  u8arr rsegs m1 arr ja -> length ja = Z.to_nat (arr_size L0) ->
  bytes_at rsegs m1 strspn_c.SSP_GOT (le8 (Z_to_bv 64 strspn_c.SSP_GUARD)) ->
  bytes_at rsegs m1 strspn_c.SSP_GUARD (le8 can) ->
  evt rsegs POST (MS (mkR ra' sp gp tp t0' t1' t2' (Z_to_bv 64 src) (Z_to_bv 64 len) a0v a1' a2' a3' a4' a5' a6' a7'
       s2 s3 (Z_to_bv 64 text) (Z_to_bv 64 copy) s6 s7v s8 (Z_to_bv 64 MASK) (Z_to_bv 64 arr) (Z_to_bv 64 32)
       t3' t4' t5' t6') F (Z_to_bv 64 0x141fc) fc None m1 (seg_rom rsegs)).
Proof.
  induction j as [|j IH];
    intros m1 ra' t0' t1' t2' a0v a1' a2' a3' a4' a5' a6' a7' s7v t3' t4' t5' t6' jc ja jsv j2 j3
      Hj HT -> -> MU WM MI ST FR0 FR1 TX CP LC AR LA G1 G2; [lia|].
  pose proof swr_L0 as EL0.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold strspn_c.SSP_GOT, strspn_c.SSP_GUARD in G1, G2. unfold LOC0 in FR0.
  pose proof (tz_len U (S j) ltac:(lia)) as LT.
  destruct (nth_error U j) as [x|] eqn:Ex; [|apply nth_error_None in Ex; lia].
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
    + (* a trailing byte: zero it and go down *)
      assert (Htr : Verbs.is_trail x = true).
      { rewrite sw_is_trail_z. destruct (sw_trail_z (bv_unsigned x)); [reflexivity | exfalso; apply HM; reflexivity]. }
      assert (HT' : Verbs.trim U = Verbs.trim (firstn j U)) by (rewrite HT; exact (sw_trim_step U j x Ex Htr)).
      step.
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
      step. step. if_cases HJ; zify_cond HJ; rewrite ?unsigned_lit in HJ by lia.
      * (* more bytes: the next round *)
        eapply IH; [lia | exact HT' | sw_eqv2 | sw_eqv2 | try eassumption ..].
        all: try lia.
      * (* the whole line was trailing bytes *)
        assert (Ej : j = 0%nat) by lia. subst j.
        assert (ELN : LN = []) by (unfold Verbs.line; rewrite HT'; reflexivity).
        pose proof (tz_len U 0 ltac:(lia)) as LT0.
        step. step.
        eapply sw_tail; [ | try eassumption .. ].
        all: try (rewrite ELN; sw_eqv2).
        all: try (rewrite LT0, EL0; lia).
        all: try (rewrite ELN; apply (tz_firstn U 0); lia).
Qed.
(* 0x141c8 (the third malloc returned arr): the null checks, text := the line up to its 0, the trim loop, copy,
   the splitter: the run ends at check_reply's call (sw_post). *)
Lemma sw_run : forall ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s10' t3' t4' t5' t6' jt jc ja jsv jw,
  mem_inv rsegs m0 -> stk rsegs m0 lo SP ->
  bytes_at rsegs m0 src M ->
  u8arr rsegs m0 text jt -> length jt = Z.to_nat (L0 + 1) ->
  u8arr rsegs m0 copy jc -> length jc = Z.to_nat (L0 + 1) ->
  u8arr rsegs m0 arr ja -> length ja = Z.to_nat (arr_size L0) ->
  bytes_at rsegs m0 strspn_c.SSP_GOT (le8 (Z_to_bv 64 strspn_c.SSP_GUARD)) ->
  bytes_at rsegs m0 strspn_c.SSP_GUARD (le8 can) ->
  rw_cells rsegs m0 SP (LOC0 jsv) ->
  rw_cells rsegs m0 (SP + 40) [C8 (Z_to_bv 64 text); C8 (Z_to_bv 64 copy); CB 16 jw] ->
  evt rsegs POST (MS (mkR ra' sp gp tp t0' t1' t2' (Z_to_bv 64 src) (Z_to_bv 64 len) (Z_to_bv 64 arr) a1' a2' a3' a4'
       a5' a6' a7' s2 s3 (Z_to_bv 64 text) (Z_to_bv 64 copy) s6 (Z_to_bv 64 L0) s8 (Z_to_bv 64 MASK) s10'
       (Z_to_bv 64 32) t3' t4' t5' t6') F (Z_to_bv 64 0x141c8) fc None m0 (seg_rom rsegs)).
Proof.
  intros ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s10' t3' t4' t5' t6' jt jc ja jsv jw
    MI ST SRC TX LT CP LC AR LA G1 G2 FR0 FR1.
  pose proof swr_L0 as EL0.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold strspn_c.SSP_GOT, strspn_c.SSP_GUARD in G1, G2. unfold LOC0 in FR0.
  pose proof (munch_refl W0 m0) as MU. pose proof (wmono_refl rsegs m0) as WM.
  apply (rw_cells_split_CB rsegs m0 (SP + 40) [C8 (Z_to_bv 64 text); C8 (Z_to_bv 64 copy)] 16 jw [] [8; 4; 4]%nat)
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
  step.
  step. if_cases HZ1; zify_cond HZ1; rewrite ?unsigned_lit in HZ1 by lia; [exfalso; lia|].
  step. if_cases HZ2; zify_cond HZ2; rewrite ?unsigned_lit in HZ2 by lia; [exfalso; lia|].
  step. step. if_cases HZ3; zify_cond HZ3; rewrite ?unsigned_lit in HZ3 by lia; [exfalso; lia|].
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
  step.
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
  - (* an empty line *)
    assert (HU0 : U = []) by (apply length_zero_iff_nil; lia).
    assert (ELN : LN = []) by (unfold Verbs.line; rewrite HU0; reflexivity).
    step.
    eapply sw_tail; [ | try eassumption .. ].
    all: try (rewrite ELN; sw_eqv2).
    all: try (rewrite LTz, EL0; lia).
    all: try (rewrite ELN, HU0; reflexivity).
  - (* the trim loop from the line's last byte *)
    step.
    eapply (sw_trim (length U)); [ | | | | try eassumption .. ].
    + lia.
    + rewrite firstn_all. reflexivity.
    + unfold wa. rewrite unsigned_lit by lia. f_equal. lia.
    + f_equal. lia.
Qed.

End Run.
