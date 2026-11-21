(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import
  PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import
  SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux DSLayout ZSLayout FillWinMem TreeMem BitsModel BitsModel2
  RomRead TreesRod FlushBlockModel BitsLib DeflM.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import
  ZIface DeflateState Trees TreesTab TreeModel SendModel DeflateLz DeflateBlk LmatchModel FillWinModel DeflFastModel DeflSlowModel DeflateInvKeep.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6S Require Import Segs6 DS6 Callee6 TreesRod6 TreesApi6 DeflBlkApi6 FillWin6D Lmatch6_run
  DeflSlow6_1 DeflSlow6_2 DeflSlow6_3 DeflSlow6_4 DeflSlow6_5 DeflSlow6_5b DeflSlow6_6 DeflSlow6_7 DeflSlow6_8 DeflSlow6_M DeflSlow6_9.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Section Walk.
Variable ROM : (word -> option byte) -> Prop.
Variables (mem : word -> option byte) (S : Z) (p : ds_ptrs) (zp : zs_ptrs) (ds : deflate_state) (flush : Z) (ra : word) (sp : Z).
Variable FBSAFE : deflate_state -> option Z -> Z -> Z -> Prop.
Hypothesis MEMCPY : memcpy_run6.
Hypothesis MEMSET : memset_run6.
Hypothesis ADLER : adler32_run6 ROM.
Hypothesis TFBITS : tr_flush_bits_run6.
Hypothesis TFB : tr_flush_block_run6 FBSAFE.
Local Abbreviation W := (p_window p).
Local Abbreviation PV := (p_prev p).
Local Abbreviation HD := (p_head p).
Local Abbreviation PB := (p_pending_buf p).
Local Abbreviation strm := (p_strm p).
Local Abbreviation INP := (zp_in zp).
Local Abbreviation OUTB := (zp_out zp).
Local Abbreviation ws := (ds_w_size ds).
Local Abbreviation hs := (ds_hash_size ds).
Local Abbreviation lbs := (ds_lit_bufsize ds).
Local Abbreviation PBL := (ds_lit_bufsize ds * 4).
Local Abbreviation OLEN0 := (Z.of_nat (length (cs_out_rev (ds_strm ds)))).
Local Abbreviation AV0 := (cs_avail_out (ds_strm ds)).
Local Abbreviation SP := (sp - 128).
Hypothesis HH : DSH ROM mem S p zp ds flush ra sp.
Local Abbreviation DI := (DeflSlow6_1.DI ROM mem S p zp ds sp).
Local Abbreviation HREGS := (DeflSlow6_1.HREGS S sp).
Local Abbreviation TREGS := (DeflSlow6_7.TREGS S sp).
Local Abbreviation LOC := (DeflSlow6_2.LOC4 sp).
Local Abbreviation FPR := (DeflSlow6_6.FPR S p).
Local Abbreviation flush_ok := (flush_ok6 FBSAFE).

Let HWF : DWF ds := dsh_wf _ _ _ _ _ _ _ _ _ HH.

Local Abbreviation KEEP := (DeflSlow6_9.KEEP).
Local Abbreviation FW := (FillWin6D.fill_window_correct).

Local Ltac keep_via HK Hfr := apply (DeflSlow6_9.KEEP_via _ _ _ _ HK Hfr); reflexivity.
Local Ltac hregs_via HRG Hfr := apply (DeflSlow6_1.HREGS_via S sp _ _ _ HRG Hfr); reflexivity.
Local Ltac tregs_via HRG Hfr := apply (DeflSlow6_7.TREGS_via S sp _ _ _ HRG Hfr); reflexivity.
Local Ltac retok := apply ret_ok_even; reflexivity.
Local Ltac via1 Hfr := lazymatch goal with |- getr _ ?r = _ => rewrite (Hfr r eq_refl) end.

Local Abbreviation avail_bound := (DeflSlow6_9.avail_bound ROM mem S p zp ds flush ra sp HH).
Local Abbreviation di_sizes := (DeflSlow6_9.di_sizes ROM mem S p zp ds sp).
Local Abbreviation sdist_ok := (DeflSlow6_M.sdist_ok FBSAFE).
Local Abbreviation slit_ok := (DeflSlow6_M.slit_ok6 FBSAFE ws).
Local Abbreviation sdec_ok := (DeflSlow6_M.sdec_ok FBSAFE ws).
Local Abbreviation shash_ok := (DeflSlow6_M.shash_ok FBSAFE ws).
Local Abbreviation strip_ok := (DeflSlow6_M.strip_ok FBSAFE ws hs).
Local Abbreviation ILS := (DeflSlow6_5.ILS).
Local Abbreviation PLR := (DeflSlow6_2.PLR).


Definition EXITS (regs : bvmap 5 word) (pc : word) (m : word -> option byte)
           (R : bvmap 5 word) (M : word -> option byte) (r : deflate_state * loop_out) : Prop :=
  match snd r with
  | LCont => HREGS R /\ msteps s6_segs (mkst regs pc m s6_rom) (mkst R (0x19600 : word) M s6_rom)
  | LBreak => HREGS R /\ msteps s6_segs (mkst regs pc m s6_rom) (mkst R (0x19b14 : word) M s6_rom)
  | LRet bs => getr R 10 = zw (bs_code bs) /\ getr R 2 = zw SP
               /\ msteps s6_segs (mkst regs pc m s6_rom) (mkst R (0x19d64 : word) M s6_rom)
  end.

Lemma EXITS_pre : forall regs regs' (pc pc' : word) m m' R M r,
  msteps s6_segs (mkst regs pc m s6_rom) (mkst regs' pc' m' s6_rom) ->
  EXITS regs' pc' m' R M r -> EXITS regs pc m R M r.
Proof using.
  intros regs regs' pc pc' m m' R M [X o] Hms HE. unfold EXITS in *. cbn [fst snd] in *.
  destruct o as [| |bs].
  - destruct HE as (A & B). split; [exact A | eapply msteps_trans; [exact Hms | exact B]].
  - destruct HE as [A B]. split; [exact A | eapply msteps_trans; [exact Hms | exact B]].
  - destruct HE as (A & A' & B). split; [exact A|]. split; [exact A' | eapply msteps_trans; [exact Hms | exact B]].
Qed.

Lemma st_bflush_false : forall s, st_bflush s false = (s, LCont).
Proof using. reflexivity. Qed.

Lemma st_bflush_true : forall s,
  st_bflush s true = (fst (flush_block s 0), match snd (flush_block s 0) with Some bs => LRet bs | None => LCont end).
Proof using. intros s. unfold st_bflush. destruct (flush_block s 0) as [s' [bs|]]; reflexivity. Qed.


Definition ILIS (X : deflate_state) : Prop :=
  0 <= ds_strstart X /\ 0 <= ds_ins_h X < 2 ^ 31 /\ ds_hash_mask X = hs - 1 /\ ds_w_mask X = ws - 1 /\ 0 <= ds_hash_shift X < 32
  /\ (forall j, 0 <= j < 2 * ws -> 0 <= arr_get (ds_window X) j < 256)
  /\ (forall j, 0 <= j < hs -> 0 <= arr_get (ds_head X) j < 65536)
  /\ arr_len (ds_head X) = hs.

Lemma ILIS_step : forall X mi, ILIS X ->
  ILIS (insl_st X mi) /\ ds_strstart (insl_st X mi) = ds_strstart X + 1 /\ ds_prev_length (insl_st X mi) = ds_prev_length X - 1
  /\ ds_sym_next (insl_st X mi) = ds_sym_next X /\ ds_sym_end (insl_st X mi) = ds_sym_end X
  /\ ds_lookahead (insl_st X mi) = ds_lookahead X /\ ds_window (insl_st X mi) = ds_window X.
Proof using HWF HH sp ra flush zp p S mem ROM.
  intros X mi (Hs & Hih & Hhm & Hwm & Hsh & Hwb & Hhb & Lh). pose proof (wf_hsz _ HWF) as Whs.
  unfold ILIS, insl_st, DeflSlow6_2.ins_str. destruct (ds_strstart X + 1 <=? mi); dsred.
  - pose proof (update_hash_range (set_strstart X (ds_strstart X + 1)) (ds_ins_h X) (arr_get (ds_window X) (ds_strstart X + 1 + 2)) ltac:(dsred; lia)) as Hh.
    dsred in Hh. rewrite Hhm in Hh.
    set (h := update_hash _ _ _) in *.
    repeat match goal with |- _ /\ _ => split end; try assumption; try lia; try reflexivity.
    + intros j Hj; rewrite arr_get_set; destruct (_ && _); [pose proof (wrap16_range (ds_strstart X + 1)); lia | apply Hhb; exact Hj].
    + rewrite arr_len_set; exact Lh.
  - repeat match goal with |- _ /\ _ => split end; try assumption; try lia; try reflexivity.
Qed.

Lemma ins_loop : forall n regs0 regs m1 m X mi sn se,
  DI m1 m X -> HREGS regs -> ILS regs (ds_strstart X + 1) mi (ds_prev_length X - 1) sn se -> KEEP regs0 regs -> ILIS X ->
  ds_prev_length X = Z.of_nat n -> (1 <= n)%nat -> Z.of_nat n <= 258 -> ds_strstart X + Z.of_nat n + 2 < 2 ^ 31 ->
  0 <= mi < 2 ^ 32 -> mi + 3 <= 2 * ws -> 0 <= sn < 2 ^ 32 -> 0 <= se < 2 ^ 32 ->
  exists R M,
    msteps s6_segs (mkst regs (0x19850 : word) m s6_rom) (mkst R (0x19968 : word) M s6_rom)
    /\ DI m1 M (deflate_slow_insert n X mi) /\ HREGS R
    /\ ILS R (ds_strstart (deflate_slow_insert n X mi) + 1) mi (ds_prev_length (deflate_slow_insert n X mi) - 1) sn se
    /\ KEEP regs0 R /\ ILIS (deflate_slow_insert n X mi)
    /\ ds_prev_length (deflate_slow_insert n X mi) = 0 /\ ds_strstart (deflate_slow_insert n X mi) = ds_strstart X + Z.of_nat n
    /\ ds_sym_next (deflate_slow_insert n X mi) = ds_sym_next X /\ ds_sym_end (deflate_slow_insert n X mi) = ds_sym_end X
    /\ ds_lookahead (deflate_slow_insert n X mi) = ds_lookahead X.
Proof using HWF HH ra flush.
  induction n as [|n IH]; intros regs0 regs m1 m X mi sn se HDI HRG HIL HK HILI Hpl Hn Hn8 Hroom Hmi Hmi3 Hsn Hse; [lia|].
  pose proof HILI as (Hs & Hih & Hhm & Hwm & Hsh & Hwb & Hhb & Lh).
  destruct (insl_blk _ _ _ _ _ _ _ _ _ HH regs m1 m X mi sn se HDI HRG HIL ltac:(lia) Hs ltac:(lia) ltac:(lia) Hmi Hih Hhm Hwm Hsh Hsn Hse Hwb Hhb)
    as (R1 & M1 & Hms1 & HDI1 & HRG1 & HIL1 & Hfr1).
  assert (HK1 : KEEP regs0 R1) by (keep_via HK Hfr1).
  destruct (ILIS_step X mi HILI) as (HILI1 & E1s & E1m & E1n & E1e & E1l & E1w).
  rewrite deflate_slow_insert_step. cbv zeta. rewrite E1m, Hpl.
  unfold insl_pc in Hms1. rewrite Hpl in Hms1.
  destruct n as [|n'].
  - replace (Z.of_nat 1 =? 1) with true in Hms1 by reflexivity.
    replace (Z.of_nat 1 - 1 =? 0) with true by reflexivity. cbn [negb].
    exists R1, M1. split; [exact Hms1|]. split; [exact HDI1|]. split; [exact HRG1|]. split; [exact HIL1|]. split; [exact HK1|].
    split; [exact HILI1|]. rewrite E1m, E1s, E1n, E1e, E1l, Hpl. repeat split; lia.
  - replace (Z.of_nat (Datatypes.S (Datatypes.S n')) =? 1) with false in Hms1 by (symmetry; apply Z.eqb_neq; lia).
    replace (Z.of_nat (Datatypes.S (Datatypes.S n')) - 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb].
    destruct (IH regs0 R1 m1 M1 (insl_st X mi) mi sn se HDI1 HRG1 HIL1 HK1 HILI1 ltac:(rewrite E1m, Hpl; lia) ltac:(lia) ltac:(lia) ltac:(rewrite E1s; lia) Hmi Hmi3 Hsn Hse)
      as (R2 & M2 & Hms2 & HDI2 & HRG2 & HIL2 & HK2 & HILI2 & E2m & E2s & E2n & E2e & E2l).
    exists R2, M2. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
    split; [exact HDI2|]. split; [exact HRG2|]. split; [exact HIL2|]. split; [exact HK2|]. split; [exact HILI2|].
    rewrite E2m, E2s, E2n, E2e, E2l, E1s, E1n, E1e, E1l. repeat split; lia.
Qed.


Lemma from_dist : forall regs0 regs m1 m X,
  DI m1 m X -> HREGS regs -> PLR regs X -> KEEP regs0 regs -> LOC m1 ->
  strip_inv X -> 1 <= ds_lookahead X <= 2 * ws -> dist_cond X = true -> sdist_ok X ->
  exists R M, DI m1 M (fst (st_bflush (fst (st_sdist X)) (snd (st_sdist X)))) /\ KEEP regs0 R
    /\ EXITS regs (0x19738 : word) m R M (st_bflush (fst (st_sdist X)) (snd (st_sdist X))).
Proof using HWF HH TFB TFBITS MEMSET MEMCPY ra.
  intros regs0 regs m1 m X HDI HRG HPL HK HL1 HTI Hlk Hdc (Dpl & Dsl & DD & Dfl7).
  pose proof (di_sizes _ _ _ HDI) as (Ews & Ehs & Elbs). pose proof (wf_wsz _ HWF) as Wws. pose proof (wf_hsz _ HWF) as Whs. pose proof (wf_lbs _ HWF) as Wlbs.
  unfold dist_cond in Hdc. apply andb_prop in Hdc. destruct Hdc as [Hdc1 Hdc2]. apply Z.leb_le in Hdc1. apply Z.leb_le in Hdc2.
  destruct HTI as [Tstr Tsl Tlook Tih Thm Twm Ths Tml Tms Tpl Tpm Tma Tstrat Tlazy Tsn Tse Twb Thb Tpb Tlh Tlfc Tdfc].
  rewrite Ews in *. rewrite Ehs in *. rewrite Elbs in *.
  destruct (sdist_eq X ltac:(lia) Dpl ltac:(lia) Dsl ltac:(lia)) as [E1 E2]. rewrite E1, E2 in *. clear E1 E2.
  destruct (dist_blk _ _ _ _ _ _ _ _ _ HH regs m1 m X HDI HRG HPL ltac:(lia) ltac:(lia) Tpm ltac:(lia) Dsl Dpl ltac:(lia) ltac:(lia) Tse Tlfc Tdfc DD)
    as (R1 & M1 & Hms1 & HDI1 & HRG1 & HIL1 & Hfr1).
  assert (HK1 : KEEP regs0 R1) by (keep_via HK Hfr1).
  assert (V1 : (ds_prev_length (dist_st X), ds_strstart (dist_st X), ds_lookahead (dist_st X), ds_sym_next (dist_st X), ds_sym_end (dist_st X),
                ds_ins_h (dist_st X), ds_hash_mask (dist_st X), ds_w_mask (dist_st X), ds_hash_shift (dist_st X), ds_window (dist_st X), ds_head (dist_st X))
               = (ds_prev_length X - 2, ds_strstart X, ds_lookahead X + 1 - ds_prev_length X, ds_sym_next X + 3, ds_sym_end X,
                  ds_ins_h X, ds_hash_mask X, ds_w_mask X, ds_hash_shift X, ds_window X, ds_head X)).
  { unfold dist_st. dsred. reflexivity. }
  revert HDI1 V1 Dfl7. generalize (dist_st X). intros U HDI1 V1 Dfl7.
  injection V1 as Upl Ustr Ulk Usn Use Uih Uhm Uwm Ush Uw Uhd.
  assert (HILI1 : ILIS U).
  { unfold ILIS. rewrite Ustr, Uih, Uhm, Uwm, Ush, Uw, Uhd.
    repeat match goal with |- _ /\ _ => split end; first [exact Tih | exact Twb | exact Thb | exact Tlh | lia]. }
  set (n := Z.to_nat (ds_prev_length X - 2)) in *.
  replace (ds_strstart X + 1) with (ds_strstart U + 1) in HIL1 by lia.
  replace (ds_prev_length X - 3) with (ds_prev_length U - 1) in HIL1 by lia.
  destruct (ins_loop n regs0 R1 m1 M1 U _ _ _ HDI1 HRG1 HIL1 HK1 HILI1
              ltac:(subst n; rewrite Upl; lia) ltac:(subst n; lia) ltac:(subst n; lia) ltac:(subst n; rewrite Ustr; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
    as (R4 & M4 & Hms4 & HDI4 & HRG4 & HIL4 & HK4 & HILI4 & E4m & E4s & E4n & E4e & E4l).
  rewrite Ustr, Usn, Use, Ulk in *.
  revert HDI4 HIL4 HILI4 E4m E4s E4n E4e E4l Dfl7 Hms4. generalize (deflate_slow_insert n U (ds_strstart X + ds_lookahead X - 3)).
  intros XL HDI4 HIL4 HILI4 E4m E4s E4n E4e E4l Dfl7 Hms4.
  destruct (exit_blk _ _ _ _ _ _ _ _ _ HH R4 m1 M4 XL (ds_strstart X + ds_lookahead X - 3) (ds_sym_next X + 3) (ds_sym_end X)
              HDI4 HRG4 HIL4 ltac:(rewrite E4s; lia) ltac:(rewrite E4s; subst n; lia) ltac:(lia) ltac:(lia))
    as (R5 & M5 & Hms5 & HDI5 & HRG5 & B10 & Hfr5).
  assert (HK5 : KEEP regs0 R5) by (keep_via HK4 Hfr5).
  assert (V5 : ds_strstart (exit_st XL) = ds_strstart XL + 1) by (unfold exit_st; dsred; reflexivity).
  revert HDI5 Dfl7 V5. generalize (exit_st XL). intros X8 HDI5 Dfl7 V5.
  rewrite <- V5 in B10.
  assert (Hms15 : msteps s6_segs (mkst regs (0x19738 : word) m s6_rom) (mkst R5 (exit_pc (ds_sym_next X + 3) (ds_sym_end X)) M5 s6_rom)).
  { eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms4 | exact Hms5]. }
  clear Hms1 Hms4 Hms5. unfold exit_pc in Hms15.
  destruct (ds_sym_next X + 3 =? ds_sym_end X).
  -
    rewrite st_bflush_true.
    destruct (from_fb1 _ _ _ _ _ _ _ _ _ FBSAFE MEMCPY MEMSET TFBITS TFB HH regs0 R5 m1 M5 X8 HDI5 HRG5 HK5 HL1 B10 (Dfl7 eq_refl)) as (R6 & M6 & HDI6 & HK6 & HX6).
    revert HDI6 HX6. generalize (fst (flush_block X8 0)). intros X9 HDI6 HX6.
    exists R6, M6. split; [exact HDI6|]. split; [exact HK6|].
    unfold EXITS. cbn [fst snd]. destruct (snd (flush_block X8 0)) as [bs|].
    + destruct HX6 as (Hms6 & A10 & A2). split; [exact A10|]. split; [exact A2|]. eapply msteps_trans; [exact Hms15 | exact Hms6].
    + destruct HX6 as (Hms6 & HRG6). split; [exact HRG6|]. eapply msteps_trans; [exact Hms15 | exact Hms6].
  - rewrite st_bflush_false.
    exists R5, M5. split; [exact HDI5|]. split; [exact HK5|]. unfold EXITS. cbn [fst snd]. split; [exact HRG5 | exact Hms15].
Qed.


Lemma ltail_avail : forall X, cs_avail_out (ds_strm (ltail_st X)) = cs_avail_out (ds_strm X).
Proof using. intros X. unfold ltail_st. dsred. reflexivity. Qed.

Lemma from_mavail : forall regs0 regs m1 m X,
  DI m1 m X -> HREGS regs -> KEEP regs0 regs -> LOC m1 ->
  strip_inv X -> 1 <= ds_lookahead X <= 2 * ws -> (ds_match_available X <> 0 -> slit_ok X) ->
  let r := if negb (ds_match_available X =? 0) then st_slit X else st_avail X in
  exists R M, DI m1 M (fst r) /\ KEEP regs0 R /\ EXITS regs (0x198c0 : word) m R M r.
Proof using HWF HH TFB TFBITS MEMSET MEMCPY ra.
  intros regs0 regs m1 m X HDI HRG HK HL1 HTI Hlk HLO.
  pose proof (di_sizes _ _ _ HDI) as (Ews & Ehs & Elbs). pose proof (wf_wsz _ HWF) as Wws. pose proof (wf_lbs _ HWF) as Wlbs.
  destruct HTI as [Tstr Tsl Tlook Tih Thm Twm Ths Tml Tms Tpl Tpm Tma Tstrat Tlazy Tsn Tse Twb Thb Tpb Tlh Tlfc Tdfc].
  rewrite Ews in *. rewrite Ehs in *. rewrite Elbs in *.
  destruct (mavail_blk _ _ _ _ _ _ _ _ _ HH regs m1 m X HDI HRG Tma) as (R1 & Hms1 & HRG1 & Hfr1).
  assert (HK1 : KEEP regs0 R1) by (keep_via HK Hfr1).
  unfold mavail_pc in Hms1. cbv zeta.
  destruct (Z.eqb_spec (ds_match_available X) 0) as [Hz|Hnz]; cbn [negb].
  -
    rewrite st_avail_eq.
    destruct (avail0_blk _ _ _ _ _ _ _ _ _ HH R1 m1 m X HDI HRG1 Tstr ltac:(lia) Tsl) as (R2 & M2 & Hms2 & HDI2 & HRG2 & Hfr2).
    exists R2, M2. split; [exact HDI2|]. split; [keep_via HK1 Hfr2|].
    unfold EXITS. cbn [fst snd]. split; [exact HRG2 | eapply msteps_trans; [exact Hms1 | exact Hms2]].
  -
    destruct (HLO Hnz) as (Ls1 & Lfl & Ls2 & Ll2 & Lsl2). clear HLO.
    rewrite st_slit_eq. cbv zeta.
    destruct (slit_blk _ _ _ _ _ _ _ _ _ HH R1 m1 m X HDI HRG1 ltac:(lia) ltac:(lia) ltac:(lia) Tse Twb Tlfc) as (R2 & M2 & Hms2 & HDI2 & HRG2 & Hfr2).
    assert (HK2 : KEEP regs0 R2) by (keep_via HK1 Hfr2).
    unfold slit_pc in Hms2.
    revert HDI2 Lfl Ls2 Ll2 Lsl2. generalize (slit1 X). intros X1 HDI2 Lfl Ls2 Ll2 Lsl2.
    assert (MID : exists R3 M3,
              msteps s6_segs (mkst regs (0x198c0 : word) m s6_rom) (mkst R3 (0x195dc : word) M3 s6_rom)
              /\ DI m1 M3 (if ds_sym_next X + 3 =? ds_sym_end X then flush_block_only X1 0 else X1)
              /\ HREGS R3 /\ KEEP regs0 R3).
    { destruct (ds_sym_next X + 3 =? ds_sym_end X).
      - destruct (from_fb2 _ _ _ _ _ _ _ _ _ FBSAFE MEMCPY MEMSET TFBITS TFB HH regs0 R2 m1 M2 X1 HDI2 HRG2 HK2 HL1 (Lfl eq_refl)) as (R3 & M3 & HDI3 & HK3 & HRG3 & Hms3).
        exists R3, M3. split; [eapply msteps_trans; [exact Hms1|]; eapply msteps_trans; [exact Hms2 | exact Hms3]|].
        split; [exact HDI3|]. split; [exact HRG3 | exact HK3].
      - exists R2, M2. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
        split; [exact HDI2|]. split; [exact HRG2 | exact HK2]. }
    destruct MID as (R3 & M3 & Hms3 & HDI3 & HRG3 & HK3).
    revert HDI3 Ls2 Ll2 Lsl2. generalize (if ds_sym_next X + 3 =? ds_sym_end X then flush_block_only X1 0 else X1). intros X2 HDI3 Ls2 Ll2 Lsl2.
    pose proof (avail_bound _ _ _ HDI3) as Hav2.
    destruct (ltail_blk _ _ _ _ _ _ _ _ _ HH R3 m1 M3 X2 HDI3 HRG3 Ls2 Ll2 Lsl2 ltac:(lia)) as (R4 & M4 & Hms4 & HDI4 & HRG4 & Z10 & Hfr4).
    assert (HK4 : KEEP regs0 R4) by (keep_via HK3 Hfr4).
    rewrite ltail_avail. unfold ltail_pc in Hms4.
    exists R4, M4. split; [exact HDI4|]. split; [exact HK4|].
    unfold EXITS. destruct (Z.eqb_spec (cs_avail_out (ds_strm X2)) 0) as [Az|Anz]; cbn [fst snd bs_code].
    + split; [exact (Z10 Az)|]. split; [destruct HRG4 as (_ & W2 & _); exact W2|].
      eapply msteps_trans; [exact Hms3 | exact Hms4].
    + split; [exact HRG4 | eapply msteps_trans; [exact Hms3 | exact Hms4]].
Qed.


Lemma from_dec : forall regs0 regs m1 m X,
  DI m1 m X -> HREGS regs -> PLR regs X -> KEEP regs0 regs -> LOC m1 -> sdec_ok X ->
  exists R M, DI m1 M (fst (st_decide X)) /\ KEEP regs0 R /\ EXITS regs (0x19730 : word) m R M (st_decide X).
Proof using HWF HH TFB TFBITS MEMSET MEMCPY ra.
  intros regs0 regs m1 m X HDI HRG HPL HK HL1 (HTI & Hlk & HD).
  pose proof HTI as [_ _ _ _ _ _ _ Tml _ Tpl _ _ _ _ _ _ _ _ _ _ _ _].
  destruct (dec_blk _ _ _ _ _ _ _ _ _ HH regs m X HRG HPL Tpl Tml) as (R1 & Hms1 & HRG1 & HPL1 & Hfr1).
  assert (HK1 : KEEP regs0 R1) by (keep_via HK Hfr1).
  unfold dec_pc, dec_cond in Hms1. unfold st_decide. change (DeflSlow6_M.dist_cond X) with ((3 <=? ds_prev_length X) && (ds_match_length X <=? ds_prev_length X))%bool in *.
  destruct ((3 <=? ds_prev_length X) && (ds_match_length X <=? ds_prev_length X))%bool eqn:Edc.
  - destruct (from_dist regs0 R1 m1 m X HDI HRG1 HPL1 HK1 HL1 HTI Hlk Edc HD) as (R & M & A & B & C).
    exists R, M. split; [exact A|]. split; [exact B|]. exact (EXITS_pre _ _ _ _ _ _ _ _ _ Hms1 C).
  - edestruct (from_mavail regs0 R1 m1 m X HDI HRG1 HK1 HL1 HTI Hlk) as (R & M & A & B & C).
    { intros Hnz. destruct (Z.eqb_spec (ds_match_available X) 0); [lia|]. exact HD. }
    exists R, M. split; [exact A|]. split; [exact B|]. exact (EXITS_pre _ _ _ _ _ _ _ _ _ Hms1 C).
Qed.


Lemma HREGS_lm : forall R R',
  HREGS R -> getr R' 2 = zw SP -> getr R' 8 = getr R 8 -> getr R' 20 = getr R 20 -> getr R' 21 = getr R 21 -> getr R' 22 = getr R 22 ->
  (forall r : reg, reg_in r lmatch_clob = false -> getr R' r = getr R r) -> HREGS R'.
Proof using.
  intros R R' (A8 & A2 & A21 & A22 & A27 & A20 & A23 & A24 & A26) B2 B8 B20 B21 B22 Hfr. unfold DeflSlow6_1.HREGS.
  rewrite B2, B8, B20, B21, B22, (Hfr 27%bv eq_refl), (Hfr 23%bv eq_refl), (Hfr 24%bv eq_refl), (Hfr 26%bv eq_refl).
  repeat split; assumption.
Qed.

Lemma HREGS_fw : forall R R',
  HREGS R -> getr R' 2 = zw SP ->
  (forall r : reg, reg_in r c_clob = false -> getr R' r = getr R r) -> HREGS R'.
Proof using.
  intros R R' (A8 & A2 & A21 & A22 & A27 & A20 & A23 & A24 & A26) B2 Hfr. unfold DeflSlow6_1.HREGS.
  rewrite B2, (Hfr 8%bv eq_refl), (Hfr 21%bv eq_refl), (Hfr 22%bv eq_refl), (Hfr 27%bv eq_refl), (Hfr 20%bv eq_refl), (Hfr 23%bv eq_refl), (Hfr 24%bv eq_refl), (Hfr 26%bv eq_refl).
  repeat split; assumption.
Qed.


Lemma from_pl : forall regs0 regs m1 m X,
  DI m1 m X -> HREGS regs -> getr regs 10 = zw (ds_match_length X) -> KEEP regs0 regs -> LOC m1 -> sdec_ok X ->
  exists R M, DI m1 M (fst (st_decide X)) /\ KEEP regs0 R /\ EXITS regs (0x1972c : word) m R M (st_decide X).
Proof using HWF HH TFB TFBITS MEMSET MEMCPY ra.
  intros regs0 regs m1 m X HDI HRG Q10 HK HL1 HSD.
  pose proof HSD as ([_ _ _ _ _ _ _ Tml _ Tpl _ _ _ _ _ _ _ _ _ _ _ _] & _).
  destruct (pl_blk _ _ _ _ _ _ _ _ _ HH regs m1 m X HDI HRG Q10 Tpl) as (R1 & Hms1 & HRG1 & HPL1 & Hfr1).
  destruct (from_dec regs0 R1 m1 m X HDI HRG1 HPL1 ltac:(keep_via HK Hfr1) HL1 HSD) as (R & M & A & B & C).
  exists R, M. split; [exact A|]. split; [exact B|]. exact (EXITS_pre _ _ _ _ _ _ _ _ _ Hms1 C).
Qed.


Lemma from_lm : forall regs0 regs m1 m X3 hh,
  DI m1 m X3 -> HREGS regs -> getr regs 10 = zw S -> getr regs 11 = zw hh -> getr regs 1 = (0x196ec%bv : word) -> KEEP regs0 regs -> LOC m1 ->
  0 <= hh < 65536 -> 0 <= ds_strstart X3 <= 2 * ws -> 0 <= ds_strategy X3 <= 4 ->
  sl_lm_cond X3 hh = true -> lm_ok6 X3 hh -> sdec_ok (st_lm X3 hh) ->
  exists R M, DI m1 M (fst (st_decide (st_lm X3 hh))) /\ KEEP regs0 R /\ EXITS regs (0x19da0%bv : word) m R M (st_decide (st_lm X3 hh)).
Proof using HWF HH TFB TFBITS MEMSET MEMCPY ra.
  intros regs0 regs m1 m X3 hh HDI HRG A10 A11 A1 HK HL1 Hhh Hstr Hstrat Hc HLM HSD.
  pose proof (di_sizes _ _ _ HDI) as (Ews & Ehs & Elbs). pose proof (wf_wsz _ HWF) as Wws.
  rewrite (st_lm_true X3 hh Hc) in HSD |- *. cbv zeta in HSD. cbv zeta.
  destruct HLM as (Lwb & Lpb & Ls0 & Ls258 & Lwm & Lpl & Lnice & Llook & Lgood & Lchain & Lch1 & Lcur & Lvis & Lml).
  rewrite Ews in *.
  destruct HRG as (P8 & P2 & Prest).
  destruct (call_lm _ _ _ _ _ _ _ _ _ HH regs m1 m X3 hh (0x196ec%bv : word) HDI ltac:(retok) Lwb Lpb Ls0 Ls258 Lwm Lpl Lnice Llook Lgood Lchain Lch1 ltac:(lia) Lvis
              A1 P2 A10 A11)
    as (R2 & M2 & ms & Hms2 & Ems & HDI2 & C10 & C2 & C8 & C9 & C18 & C19 & C20 & C21 & C22 & Hfr2).
  assert (HK2 : KEEP regs0 R2). { destruct HK as (K3 & K4 & K9). unfold DeflSlow6_9.KEEP. rewrite (Hfr2 3%bv eq_refl), (Hfr2 4%bv eq_refl), C9. repeat split; assumption. }
  assert (HRG2 : HREGS R2) by (apply (HREGS_lm regs R2 (conj P8 (conj P2 Prest)) C2 C8 C20 C21 C22 Hfr2)).
  rewrite Ems in HSD |- *.
  revert HSD C10 Lml. generalize (snd (longest_match X3 hh)). intros ml HSD C10 Lml.
  rewrite sl_filter_eq in HSD |- *.
  assert (Hms32 : 0 <= ms < 2 ^ 32).
  { destruct (_ && _) in HSD; destruct HSD as ([_ _ _ _ _ _ _ _ Tms _ _ _ _ _ _ _ _ _ _ _ _ _] & _); exact Tms. }
  assert (Vst : ds_strategy (set_match_start X3 ms) = ds_strategy X3) by reflexivity.
  destruct (lmret_blk _ _ _ _ _ _ _ _ _ HH R2 m1 M2 (set_match_start X3 ms) ml HDI2 HRG2 HL1 C10 Lml ltac:(rewrite Vst; exact Hstrat)
              ltac:(dsred; exact Hstr) ltac:(dsred; exact Hms32))
    as (R3 & M3 & Hms3 & HDI3 & HRG3 & D10 & Hfr3).
  assert (HK3 : KEEP regs0 R3) by (keep_via HK2 Hfr3).
  unfold lmret_pc, lm_filter in Hms3, D10. rewrite Vst in Hms3, D10.
  replace (ds_strstart (set_match_start X3 ms)) with (ds_strstart X3) in Hms3, D10 by reflexivity.
  replace (ds_match_start (set_match_start X3 ms)) with ms in Hms3, D10 by reflexivity.
  set (XM := set_match_length (set_match_start X3 ms) ml) in *.
  assert (VMml : ds_match_length XM = ml) by reflexivity.
  assert (Hms13 : msteps s6_segs (mkst regs (0x19da0%bv : word) m s6_rom)
                    (mkst R3 (if (ml <=? 5) && ((ds_strategy X3 =? 1) || (ml =? 3) && (4096 <? wrap32 (ds_strstart X3 - ms)))
                              then (0x19704%bv : word) else (0x1972c%bv : word)) M3 s6_rom))
    by (eapply msteps_trans; [exact Hms2 | exact Hms3]).
  clear Hms2 Hms3. clearbody XM.
  destruct ((ml <=? 5) && ((ds_strategy X3 =? 1) || (ml =? 3) && (4096 <? wrap32 (ds_strstart X3 - ms))))%bool.
  -
    destruct (lm2_blk _ _ _ _ _ _ _ _ _ HH R3 m1 M3 XM HDI3 HRG3) as (R4 & M4 & Hms4 & HDI4 & HRG4 & G10 & Hfr4).
    destruct (from_pl regs0 R4 m1 M4 (set_match_length XM 2) HDI4 HRG4 G10 ltac:(keep_via HK3 Hfr4) HL1 HSD) as (R & M & A & B & C).
    exists R, M. split; [exact A|]. split; [exact B|].
    exact (EXITS_pre _ _ _ _ _ _ _ _ _ ltac:(eapply msteps_trans; [exact Hms13 | exact Hms4]) C).
  - destruct (from_pl regs0 R3 m1 M3 XM HDI3 HRG3 ltac:(rewrite VMml; exact (D10 eq_refl)) HK3 HL1 HSD) as (R & M & A & B & C).
    exists R, M. split; [exact A|]. split; [exact B|]. exact (EXITS_pre _ _ _ _ _ _ _ _ _ Hms13 C).
Qed.


Lemma from_hash : forall regs0 regs m1 m X1,
  DI m1 m X1 -> HREGS regs -> getr regs 12 = zw (ds_match_length X1) -> getr regs 13 = zw (szwrap 32 (ds_match_start X1)) ->
  KEEP regs0 regs -> LOC m1 -> 3 <= ds_lookahead X1 -> shash_ok X1 ->
  exists R M, DI m1 M (fst (st_srest X1)) /\ KEEP regs0 R /\ EXITS regs (0x1964c%bv : word) m R M (st_srest X1).
Proof using HWF HH TFB TFBITS MEMSET MEMCPY ra.
  intros regs0 regs m1 m X1 HDI HRG Q12 Q13 HK HL1 Hl3 HSH.
  pose proof (di_sizes _ _ _ HDI) as (Ews & Ehs & Elbs). pose proof (wf_wsz _ HWF) as Wws. pose proof (wf_hsz _ HWF) as Whs.
  destruct (shash_ok_hi _ _ X1 HSH Hl3) as (HTI & Hlk & HLM & HSD). clear HSH.
  rewrite (st_srest_hi X1 Hl3).
  pose proof HTI as [Tstr Tsl Tlook Tih Thm Twm Ths Tml Tms Tpl Tpm Tma Tstrat Tlazy Tsn Tse Twb Thb Tpb Tlh Tlfc Tdfc].
  rewrite Ews, Ehs in *.
  destruct (hash_blk _ _ _ _ _ _ _ _ _ HH regs m1 m X1 HDI HRG Q12 Q13 Tstr ltac:(lia) Tih Thm Twm Ths Twb Thb Tml Tms Tlazy)
    as (R1 & M1 & Hms1 & HDI1 & HRG1 & A11 & ALM & ANLM & A12 & A2 & Hfr1).
  cbv zeta in Hms1, HDI1, A11, ALM, ANLM, A12.
  assert (HK1 : KEEP regs0 R1) by (keep_via HK Hfr1).
  fold (hash_hh X1) in *.
  assert (Ehx : hash_pc ds X1 (ds_strstart X1) (hash_hh X1)
                = (if sl_lm_cond (hash_st X1) (hash_hh X1) then (0x19da0%bv : word)
                   else if hash_hh X1 =? 0 then (0x19730%bv : word) else (0x1972c%bv : word))).
  { unfold hash_pc, sl_lm_cond. replace (ds_prev_length (hash_st X1)) with (ds_match_length X1) by reflexivity.
    replace (ds_max_lazy_match (hash_st X1)) with (ds_max_lazy_match X1) by reflexivity.
    replace (ds_strstart (hash_st X1)) with (ds_strstart X1) by reflexivity.
    replace (ds_w_size (hash_st X1)) with (ds_w_size X1) by reflexivity. rewrite Ews.
    destruct (Z.eqb_spec (hash_hh X1) 0); cbn [negb andb]; [reflexivity|].
    destruct (Z.leb_spec (ds_max_lazy_match X1) (ds_match_length X1)); destruct (Z.ltb_spec (ds_match_length X1) (ds_max_lazy_match X1)); cbn [andb]; try lia; [reflexivity|].
    destruct (wrap32 (ds_strstart X1 - hash_hh X1) <=? ws - 262); reflexivity. }
  rewrite Ehx in Hms1, ALM, ANLM.
  assert (Hhh : 0 <= hash_hh X1 < 65536).
  { unfold hash_hh. apply Thb. pose proof (update_hash_range X1 (ds_ins_h X1) (arr_get (ds_window X1) (ds_strstart X1 + 2)) ltac:(rewrite Thm; lia)) as Hu. rewrite Thm in Hu. lia. }
  destruct (Bool.bool_dec (sl_lm_cond (hash_st X1) (hash_hh X1)) true) as [Ec|Ec]; [| apply Bool.not_true_is_false in Ec]; rewrite Ec in Hms1, ALM, ANLM.
  -
    destruct (ALM eq_refl) as [B10 B1].
    destruct (from_lm regs0 R1 m1 M1 (hash_st X1) (hash_hh X1) HDI1 HRG1 B10 A11 B1 HK1 HL1 Hhh
                ltac:(change (ds_strstart (hash_st X1)) with (ds_strstart X1); lia)
                ltac:(change (ds_strategy (hash_st X1)) with (ds_strategy X1); exact Tstrat) Ec (HLM Ec) HSD)
      as (R & M & A & B & C).
    exists R, M. split; [exact A|]. split; [exact B|]. exact (EXITS_pre _ _ _ _ _ _ _ _ _ Hms1 C).
  - rewrite (st_lm_false _ _ Ec) in HSD |- *.
    assert (B10 : getr R1 10 = zw 2) by (apply ANLM; destruct (hash_hh X1 =? 0); discriminate).
    destruct (Z.eqb_spec (hash_hh X1) 0) as [Hz|Hnz].
    +
      assert (HPL1 : PLR R1 (hash_st X1)) by (split; [exact B10 | exact (A12 Hz)]).
      destruct (from_dec regs0 R1 m1 M1 (hash_st X1) HDI1 HRG1 HPL1 HK1 HL1 HSD) as (R & M & A & B & C).
      exists R, M. split; [exact A|]. split; [exact B|]. exact (EXITS_pre _ _ _ _ _ _ _ _ _ Hms1 C).
    + destruct (from_pl regs0 R1 m1 M1 (hash_st X1) HDI1 HRG1 B10 HK1 HL1 HSD) as (R & M & A & B & C).
      exists R, M. split; [exact A|]. split; [exact B|]. exact (EXITS_pre _ _ _ _ _ _ _ _ _ Hms1 C).
Qed.


Lemma trip : forall regs0 regs m1 m X,
  DI m1 m X -> HREGS regs -> KEEP regs0 regs -> LOC m1 -> getr regs 9 = zw flush ->
  strip_ok X flush ->
  exists R M, DI m1 M (fst (st_sbody X flush)) /\ KEEP regs0 R /\ EXITS regs (0x19600 : word) m R M (st_sbody X flush).
Proof using HWF HH TFB TFBITS ADLER MEMSET MEMCPY ra.
  intros regs0 regs m1 m X HDI HRG HK HL1 H9 (Hlk0 & Hfw & Hlk1 & HSH).
  pose proof (di_sizes _ _ _ HDI) as (Ews & Ehs & Elbs). pose proof (wf_wsz _ HWF) as Wws.
  pose proof (dsh_flush _ _ _ _ _ _ _ _ _ HH) as Hfl.
  unfold st_sbody in *.
  destruct (head_blk _ _ _ _ _ _ _ _ _ HH regs m1 m X HDI HRG Hlk0) as (R1 & Hms1 & HRG1 & HLO & HHI & A2 & Hfr1).
  assert (HK1 : KEEP regs0 R1) by (keep_via HK Hfr1).
  unfold head_pc in Hms1.
  assert (REST : forall R m' X1 (pc : word),
            DI m1 m' X1 -> HREGS R -> KEEP regs0 R -> 1 <= ds_lookahead X1 -> shash_ok X1 ->
            ((3 <= ds_lookahead X1 /\ pc = (0x1964c%bv : word) /\ getr R 12 = zw (ds_match_length X1) /\ getr R 13 = zw (szwrap 32 (ds_match_start X1)))
             \/ (ds_lookahead X1 < 3 /\ pc = (0x19620%bv : word) /\ getr R 10 = zw (ds_lookahead X1))) ->
            exists R' M, DI m1 M (fst (st_srest X1)) /\ KEEP regs0 R' /\ EXITS R pc m' R' M (st_srest X1)).
  { intros R m' X1 pc HDIa HRGa HKa Hl1 HSHa [(Hl3 & -> & Q12 & Q13)|(Hl3 & -> & Q10)].
    - exact (from_hash regs0 R m1 m' X1 HDIa HRGa Q12 Q13 HKa HL1 Hl3 HSHa).
    - destruct (shash_ok_lo _ _ X1 HSHa Hl3) as (HTI & Hlk & _ & HSD).
      rewrite (st_srest_lo X1 Hl3). rewrite st_lm_false in HSD |- * by apply sl_lm_cond_0.
      pose proof HTI as [Tstr Tsl Tlook Tih Thm Twm Ths Tml Tms Tpl Tpm Tma Tstrat Tlazy Tsn Tse Twb Thb Tpb Tlh Tlfc Tdfc].
      pose proof (di_sizes _ _ _ HDIa) as (Ews1 & _ & _). rewrite Ews1 in Tsl.
      destruct (short_blk _ _ _ _ _ _ _ _ _ HH R m1 m' X1 HDIa HRGa Q10 ltac:(lia) Tml Tms) as (R2 & M2 & Hms2 & _ & HLO2 & HRG2 & Hfr2).
      destruct (HLO2 ltac:(lia)) as [HDI2 HPL2].
      unfold short_pc in Hms2. replace (2 <? ds_lookahead X1) with false in Hms2 by (symmetry; apply Z.ltb_ge; lia).
      destruct (from_dec regs0 R2 m1 M2 (prev_st X1) HDI2 HRG2 HPL2 ltac:(keep_via HKa Hfr2) HL1 HSD) as (R' & M & A & B & C).
      exists R', M. split; [exact A|]. split; [exact B|]. exact (EXITS_pre _ _ _ _ _ _ _ _ _ Hms2 C). }
  destruct (Z.ltb_spec (ds_lookahead X) 262) as [Hlo|Hhi].
  -
    rewrite (st_fill_lo X flush Hlo) in Hlk1, HSH |- *. cbn [fst snd] in Hlk1, HSH |- *.
    destruct (HLO Hlo) as [B10 B1]. destruct (Hfw ltac:(rewrite MIN_LOOKAHEAD_eq; lia)) as [Hfwf Hwrap].
    destruct (call_fw _ _ _ _ _ _ _ _ _ MEMCPY MEMSET ADLER HH R1 m1 m X (0x19610%bv : word) HDI ltac:(retok) Hfwf ltac:(rewrite MIN_LOOKAHEAD_eq; lia) Hwrap B1 A2 B10)
      as (R2 & M2 & Hms2 & HDI2 & _ & C2 & _ & Hfr2).
    assert (HK2 : KEEP regs0 R2). { keep_via HK1 Hfr2. }
    assert (HRG2 : HREGS R2) by (exact (HREGS_fw R1 R2 HRG1 C2 Hfr2)).
    revert Hlk1 HSH HDI2. generalize (fill_window X). intros X1 Hlk1 HSH HDI2.
    assert (H92 : getr R2 9 = zw flush) by (rewrite (Hfr2 9%bv eq_refl), (Hfr1 9%bv eq_refl); exact H9).
    destruct (fillr_blk _ _ _ _ _ _ _ _ _ HH R2 m1 M2 X1 HDI2 HRG2 H92 Hlk1) as (R3 & Hms3 & HRG3 & Q10 & Hfr3).
    assert (HK3 : KEEP regs0 R3) by (keep_via HK2 Hfr3).
    unfold fillr_pc in Hms3. unfold fill_out.
    assert (HSH' : ((ds_lookahead X1 <? 262) && (flush =? 0))%bool = false -> ds_lookahead X1 <> 0 -> shash_ok X1).
    { intros E1 E2. apply HSH. unfold fill_out. rewrite E1. replace (ds_lookahead X1 =? 0) with false by (symmetry; apply Z.eqb_neq; exact E2). reflexivity. }
    assert (Hms13 : forall pc, msteps s6_segs (mkst R2 (0x19610 : word) M2 s6_rom) (mkst R3 pc M2 s6_rom) ->
                    msteps s6_segs (mkst regs (0x19600 : word) m s6_rom) (mkst R3 pc M2 s6_rom)).
    { intros pc H. eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2 | exact H]. }
    destruct ((ds_lookahead X1 <? 262) && (flush =? 0))%bool eqn:Enm.
    +
      cbn [fst snd].
      destruct HRG3 as (_ & W2 & _).
      destruct (ret0_blk _ _ _ _ _ _ _ _ _ HH R3 M2 W2) as (R4 & Hms4 & Z10 & Z2 & Hfr4).
      exists R4, M2. split; [exact HDI2|]. split; [keep_via HK3 Hfr4|].
      unfold EXITS. cbn [fst snd bs_code]. split; [exact Z10|]. split; [exact Z2|].
      eapply msteps_trans; [apply Hms13; exact Hms3 | exact Hms4].
    + destruct (Z.eqb_spec (ds_lookahead X1) 0) as [Hl0|Hl0].
      *
        cbn [fst snd]. exists R3, M2. split; [exact HDI2|]. split; [exact HK3|].
        unfold EXITS. cbn [fst snd]. split; [exact HRG3 | apply Hms13; exact Hms3].
      *
        cbn [fst snd].
        destruct (Z.ltb_spec 2 (ds_lookahead X1)) as [Hl3|Hl3].
        -- pose proof (HSH' eq_refl Hl0) as HSHa.
           destruct (shash_ok_hi _ _ X1 HSHa ltac:(lia)) as (HTI & _).
           pose proof HTI as [Tstr Tsl Tlook Tih Thm Twm Ths Tml Tms Tpl Tpm Tma Tstrat Tlazy Tsn Tse Twb Thb Tpb Tlh Tlfc Tdfc].
           destruct (short_blk _ _ _ _ _ _ _ _ _ HH R3 m1 M2 X1 HDI2 HRG3 Q10 Hlk1 Tml Tms) as (R4 & M4 & Hms4 & HHI4 & _ & HRG4 & Hfr4).
           destruct (HHI4 ltac:(lia)) as (-> & Q12 & Q13).
           unfold short_pc in Hms4. replace (2 <? ds_lookahead X1) with true in Hms4 by (symmetry; apply Z.ltb_lt; lia).
           destruct (REST R4 M2 X1 (0x1964c%bv : word) HDI2 HRG4 ltac:(keep_via HK3 Hfr4) ltac:(lia) HSHa ltac:(left; repeat split; try assumption; lia))
             as (R' & M & A & B & C).
           exists R', M. split; [exact A|]. split; [exact B|].
           exact (EXITS_pre _ _ _ _ _ _ _ _ _ ltac:(eapply msteps_trans; [apply Hms13; exact Hms3 | exact Hms4]) C).
        -- destruct (REST R3 M2 X1 (0x19620%bv : word) HDI2 HRG3 HK3 ltac:(lia) (HSH' eq_refl Hl0) ltac:(right; repeat split; try assumption; lia))
             as (R' & M & A & B & C).
           exists R', M. split; [exact A|]. split; [exact B|].
           exact (EXITS_pre _ _ _ _ _ _ _ _ _ ltac:(apply Hms13; exact Hms3) C).
  -
    rewrite (st_fill_hi X flush Hhi) in Hlk1, HSH |- *. cbn [fst snd] in Hlk1, HSH |- *.
    pose proof (HSH eq_refl) as HSHa.
    destruct (shash_ok_hi _ _ X HSHa ltac:(lia)) as (HTI & _).
    pose proof HTI as [Tstr Tsl Tlook Tih Thm Twm Ths Tml Tms Tpl Tpm Tma Tstrat Tlazy Tsn Tse Twb Thb Tpb Tlh Tlfc Tdfc].
    destruct (h45c_blk _ _ _ _ _ _ _ _ _ HH R1 m1 m X HDI HRG1 Tml Tms) as (R2 & Hms2 & HRG2 & Q12 & Q13 & Hfr2).
    destruct (REST R2 m X (0x1964c%bv : word) HDI HRG2 ltac:(keep_via HK1 Hfr2) ltac:(lia) HSHa ltac:(left; repeat split; try assumption; lia))
      as (R' & M & A & B & C).
    exists R', M. split; [exact A|]. split; [exact B|].
    exact (EXITS_pre _ _ _ _ _ _ _ _ _ ltac:(eapply msteps_trans; [exact Hms1 | exact Hms2]) C).
Qed.

End Walk.
End FXG.
