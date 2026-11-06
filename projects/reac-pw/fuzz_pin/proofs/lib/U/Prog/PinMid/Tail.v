(** pin_mid_contract (UBSan), the tail: from 0x12dbc (the two cells zeroed, reac_box_pin_parse's arguments, the call
    at 0x12df8) through check_known (0x12e04) and, when rc = 0, check_row (0x12e14) and check_label (0x12e20), to the
    join 0x12e24. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Image.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Prog Require Import pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Prog Require Import fuzz_catalogue_row_c reac_box_pin_parse_c
  check_known_c check_row_c check_label_c LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Prog.PinMid Require Import Facts.
Import ListNotations.
Open Scope Z_scope.

Section Tail.
Variables (sp gp tp s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte)
          (s slack : list byte) (fl phi K lo : Z) (can : word).
Hypothesis HK : Z.of_nat (length s) = K.
Hypothesis HPHI : 0 < phi.
Hypothesis HFL : 0 <= fl < 256.
Hypothesis HNUL : ~ In NUL s.
Hypothesis HSLM : (- (phi + K + 1)) mod 8 <= Z.of_nat (length slack).
Hypothesis HPB : phi + K + 1 + Z.of_nat (length slack) <= 2^64.
Hypothesis HLO0 : 0 <= lo.
Hypothesis HLO : lo + 224 <= bv_unsigned sp.
Hypothesis HSP : bv_unsigned sp + 24 <= 2^64.
Hypothesis HSPA : bv_unsigned sp mod 16 = 0.
Hypothesis HSN : forall a, lo <= a < bv_unsigned sp + 24 -> seg_rom rsegs (wa a) = None.
Hypothesis HDJ : phi + K + 1 + Z.of_nat (length slack) <= lo \/ bv_unsigned sp + 24 <= phi.
Hypothesis HRO : rom_out sp phi K.
Hypothesis PARSE : reac_box_pin_parse_contract.
Hypothesis CK : check_known_contract.
Hypothesis CR : check_row_contract.
Hypothesis CL : check_label_contract.

Local Abbreviation Q := (Qpost sp gp tp s6 s7 s8 s9 s10 s11 F fc m0 phi K lo).

(** 0x12dfc, back from reac_box_pin_parse with rc in a0: check_known(rc, want); on rc = 0 check_row(model, want)
    and check_label(label, want_label), the two cells read from sp + 16 and sp + 8. *)
Lemma tail_checks : forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 : word)
    (m : word -> option byte) (want wl : Z),
  s0 = Z_to_bv 64 phi -> s1 = Z_to_bv 64 want -> s2 = Z_to_bv 64 wl -> 0 <= want < 2^64 ->
  (bv_unsigned a0 = 0 <-> want <> 0) ->
  (bv_unsigned a0 = 0 -> bytes_at rsegs m (bv_unsigned sp + 16) (le8 (Z_to_bv 64 want)) /\
                         bytes_at rsegs m (bv_unsigned sp + 8) (le8 (Z_to_bv 64 wl))) ->
  munch (mid_fp sp phi K) m0 m -> wmono rsegs m0 m -> mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x12dfc) fc None m (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 m want wl -> -> -> Hw Hrc Hcells MU WM MI ST.
  step. step. step.
  eapply evt_cut.
  { eapply CK. rewrite unsigned_lit by lia. exact Hrc. }
  intros ms' (a0' & a1' & ->). fix_ret.
  step.
  if_cases E.
  - qfin.
  - zify_cond E.
    destruct (Hcells E) as [H16 H8].
    pose proof (bytes_at_read8 m _ _ H16) as HR16. pose proof (bytes_at_read8 m _ _ H8) as HR8.
    clear H16 H8 Hcells.
    step. step. step.
    eapply evt_cut.
    { eapply CR. reflexivity. }
    intros ms' ->. fix_ret.
    step. step. step.
    eapply evt_cut.
    { eapply CL. reflexivity. }
    intros ms' ->. fix_ret.
    qfin.
Qed.

Ltac stack_st A HM HS HOK HM' HS' m' :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm ?a ?bs) _) =>
    change a with (wa A);
    destruct (stack_store _ _ _ _ _ _ mm _ A bs HRO HM HS) as [HM' HS'];
    [ unfold MID_STACK in *; lia
    | unfold MID_STACK in *; lia
    | rewrite ?length_le8, ?length_Z_to_le_bytes; unfold MID_OUT in *; lia
    | rewrite ?length_app; cbn [length]; unfold MID_STACK, MID_OUT in *; lia
    | rewrite ?length_le8, ?length_Z_to_le_bytes; exact HOK
    | ];
    clear HM HS HOK;
    remember (write_to_mem mm (wa A) bs) as m' eqn:Em'; clear Em'
  end.

(** 0x12dbc: model and label zeroed, the arguments selected by the flag bits, reac_box_pin_parse, then
    [tail_checks]. *)
Lemma parse_call : forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 : word)
    (m : word -> option byte),
  s0 = Z_to_bv 64 phi -> s1 = Z_to_bv 64 (want_ptr FUZZ_CATALOGUE fl s) ->
  s2 = Z_to_bv 64 (want_label phi fl s) -> s3 = Z_to_bv 64 fl ->
  minv sp phi K lo can m0 m -> bytes_at rsegs m phi (s ++ NUL :: slack) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x12dbc) fc None m (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 m -> -> -> -> HM HS.
  pose proof (bytes_at_bound rsegs m phi _ HS) as BS. rewrite length_app in BS. cbn [length] in BS.
  assert (HOK1 : store_ok rsegs m (wa (bv_unsigned sp + 16)) 8 = true).
  { pose proof HM as (_ & _ & _ & _ & _ & _ & _ & WR). eapply wr_store_ok; [exact WR | lia | cbn; lia]. }
  step.
  stack_st (bv_unsigned sp + 16) HM HS HOK1 HM0 HS0 m1.
  assert (HOK2 : store_ok rsegs m1 (wa (bv_unsigned sp + 8)) 8 = true).
  { pose proof HM0 as (_ & _ & _ & _ & _ & _ & _ & WR). eapply wr_store_ok; [exact WR | lia | cbn; lia]. }
  step.
  stack_st (bv_unsigned sp + 8) HM0 HS0 HOK2 HM1 HS1 m2.
  do 13 zstep.
  zstep.
  destruct (flag_bits fl HFL) as (FB0 & FB1 & FB2). rewrite FB0, FB1, FB2.
  rewrite !mask_sel by lia.
  pose proof (rc_iff fl s phi HFL HNUL) as RC.
  pose proof (want_ptr_range fl s) as WPR.
  eapply evt_cut.
  { eapply PARSE with (str := s) (slack := slack) (lo := lo) (can := can).
    - rewrite parse_live_fl by lia. intros Hlive. destruct (fl_live_bits fl Hlive) as (B0 & B1 & B2).
      rewrite !unsigned_ite by lia. rewrite B0, B1, B2.
      pose proof HM1 as (_ & _ & _ & _ & _ & _ & _ & WR).
      unfold parse_args. rewrite HK.
      split; [exact HS1|]. split; [exact HNUL|]. split; [exact HSLM|].
      split; [lia|].
      split; [replace (bv_unsigned sp + 16) with (bv_unsigned sp + 8 + 8) by lia;
              apply (wr_at_sub _ _ 16); [exact WR | lia | lia | lia]|].
      split; [replace (bv_unsigned sp + 8) with (bv_unsigned sp + 8 + 0) by lia;
              apply (wr_at_sub _ _ 16); [exact WR | lia | lia | lia]|].
      split; [lia|]. split; [lia|]. split; [lia|].
      split; Z.div_mod_to_equations; lia.
    - exact (proj1 (proj2 (proj2 (proj2 HM1)))).
    - unfold PARSE_STACK, MID_STACK in *. lia.
    - exact HSPA.
    - intros a Ha. apply HSN. lia.
    - exact (minv_cat _ _ _ _ _ _ _ HM1).
    - exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HM1)))))).
    - exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HM1))))))).
    - exact (proj1 (proj2 (proj2 HM1))). }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m3 & -> &
              WM3 & MI3 & ST3 & PM).
  fix_ret.
  rewrite parse_live_fl in PM |- * by lia.
  rewrite (unsigned_ite (Z.testbit fl 0) phi) in PM |- * by lia.
  rewrite parse_out_fl in PM |- *.
  rewrite !unsigned_ite in PM by lia.
  destruct (parse_out FUZZ_CATALOGUE phi (fl_live fl) s) as [[row lab]|] eqn:Eo.
  - pose proof (parse_some_live _ _ _ _ _ Eo) as Hlive. destruct (fl_live_bits fl Hlive) as (B0 & B1 & B2).
    rewrite B1, B2 in PM. cbn [parse_mem] in PM. destruct PM as (MU3 & HR3 & HL3).
    destruct (harness_row_label FUZZ_CATALOGUE phi fl s row lab HFL HNUL Eo) as [-> ->].
    assert (HM3 : minv sp phi K lo can m0 m3)
      by (eapply minv_call; [exact HRO | exact HM1 | exact MU3 | fp_tac | exact WM3 | exact MI3 | exact ST3]).
    destruct HM3 as (MU' & WM' & MI' & ST' & _).
    eapply tail_checks; [reflexivity | reflexivity | reflexivity | exact WPR | exact RC | | exact MU' | exact WM'
                        | exact MI' | exact ST'].
    intros _. split; assumption.
  - cbn [parse_mem] in PM.
    assert (HM3 : minv sp phi K lo can m0 m3)
      by (eapply minv_call; [exact HRO | exact HM1 | exact PM | fp_tac | exact WM3 | exact MI3 | exact ST3]).
    destruct HM3 as (MU' & WM' & MI' & ST' & _).
    eapply tail_checks; [reflexivity | reflexivity | reflexivity | exact WPR | exact RC | | exact MU' | exact WM'
                        | exact MI' | exact ST'].
    intros Hc. exfalso. cbn [parse_rc] in Hc. rewrite unsigned_lit_wrap in Hc.
    change ((-1) mod 2^64) with 18446744073709551615 in Hc. lia.
Qed.

End Tail.
