(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import
  PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import
  SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux DSLayout ZSLayout FillWinMem TreeMem BitsModel BitsModel2
  RomRead TreesRod FlushBlockModel BitsLib DeflM.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import
  ZIface DeflateState Trees TreesTab TreeModel SendModel DeflateLz DeflateBlk LmatchModel FillWinModel DeflFastModel DeflSlowModel DeflateInvKeep.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6S Require Import Segs6 DS6 Callee6 TreesRod6 TreesApi6 DeflBlkApi6 FillWin6D Lmatch6_run
  DeflSlow6_1 DeflSlow6_2 DeflSlow6_3 DeflSlow6_4 DeflSlow6_5 DeflSlow6_5b DeflSlow6_6 DeflSlow6_7 DeflSlow6_8 DeflSlow6_M DeflSlow6_9 DeflSlow6_10.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

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
Local Ltac keep3_via HK Hfr := apply (DeflSlow6_9.KEEP3_via _ _ _ _ HK Hfr); reflexivity.
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

Local Abbreviation sloop_ok := (DeflSlow6_M.sloop_ok FBSAFE ws hs).
Local Abbreviation stail_ok := (DeflSlow6_M.stail_ok FBSAFE ws).
Local Abbreviation EXITS := (DeflSlow6_10.EXITS S sp).
Local Abbreviation Fd := (DeflSlow6_1.Fd S p zp ds sp).


Definition LEXIT (regs : bvmap 5 word) (pc : word) (m : word -> option byte)
           (R : bvmap 5 word) (M : word -> option byte) (r : deflate_state * option block_state) : Prop :=
  match snd r with
  | None => HREGS R /\ ds_wrap (fst r) = 1 /\ msteps s6_segs (mkst regs pc m s6_rom) (mkst R (0x19b14 : word) M s6_rom)
  | Some bs => getr R 10 = zw (bs_code bs) /\ getr R 2 = zw SP
               /\ msteps s6_segs (mkst regs pc m s6_rom) (mkst R (0x19d64 : word) M s6_rom)
  end.

Lemma fill_wrap : forall X, ds_wrap (fill_window X) = ds_wrap X.
Proof using.
  intros X. pose proof (fw_rest_fill_window X) as EK. unfold fw_rest in EK. injection EK. intros.
  match goal with H : ds_wrap _ = ds_wrap _ |- _ => first [exact H | exact (eq_sym H)] end.
Qed.

Lemma tl_wrap : forall s c, ds_wrap (fst (tr_tally_lit s c)) = ds_wrap s.
Proof using. intros s c. unfold tr_tally_lit. destruct s; reflexivity. Qed.

Lemma wrap_break1 : forall X, ds_wrap (break1_st X) = ds_wrap X.
Proof using.
  intros X. unfold break1_st, slit1.
  pose proof (tl_wrap X (arr_get (ds_window X) (ds_strstart X - 1))) as H.
  revert H. generalize (fst (tr_tally_lit X (arr_get (ds_window X) (ds_strstart X - 1)))). intros s H. destruct s; first [exact H | (cbn in H |- *; exact H) | (unfold set_match_available; cbn in H |- *; exact H) | (cbn -[ds_wrap] in *; congruence) | (cbv [set_match_available] in *; cbn in *; congruence)].
Qed.

Lemma srest_nb : forall s, snd (st_srest s) <> LBreak.
Proof using.
  intros s. unfold st_srest, st_decide.
  generalize (st_lm (prev_st (fst (st_hash s))) (snd (st_hash s))) as t. intros t.
  destruct (dist_cond t).
  - unfold st_bflush. destruct (snd (st_sdist t)).
    + match goal with |- context[flush_block ?a ?b] => destruct (flush_block a b) as [s' r] end.
      destruct r as [bs|]; cbn; intro H; discriminate H.
    + cbn. intro H; discriminate H.
  - destruct (negb (ds_match_available t =? 0)).
    + unfold st_slit.
      match goal with |- context[tr_tally_lit ?a ?b] => destruct (tr_tally_lit a b) as [s1 b0] end.
      cbn. match goal with |- context[if ?c then _ else _] => destruct c end; intro H; discriminate H.
    + unfold st_avail. cbn. intro H; discriminate H.
Qed.

Lemma brk_wrap : forall X fl, strip_ok X fl -> snd (st_sbody X fl) = LBreak -> ds_wrap (fst (st_sbody X fl)) = 1.
Proof using.
  intros X fl (Hlk0 & Hfw & Hlk1 & HSH) H. unfold st_sbody in H |- *.
  destruct (Z.ltb_spec (ds_lookahead X) 262) as [Hlo|Hhi].
  - rewrite (st_fill_lo X fl Hlo) in H |- *. cbn [fst snd] in H |- *.
    destruct (fill_out (fill_window X) fl) as [o|]; cbn [fst snd] in H |- *.
    + rewrite fill_wrap. exact (proj2 (Hfw ltac:(rewrite MIN_LOOKAHEAD_eq; lia))).
    + exfalso. exact (srest_nb _ H).
  - rewrite (st_fill_hi X fl Hhi) in H |- *. cbn [fst snd] in H |- *.
    exfalso. exact (srest_nb _ H).
Qed.

Lemma loop_run : forall n regs0 regs m1 m X,
  DI m1 m X -> HREGS regs -> KEEP regs0 regs -> LOC m1 -> getr regs0 9 = zw flush -> sloop_ok n X flush ->
  exists R M, DI m1 M (fst (deflate_slow_loop n X flush)) /\ KEEP regs0 R
    /\ LEXIT regs (0x19600 : word) m R M (deflate_slow_loop n X flush).
Proof using HH TFB TFBITS ADLER MEMSET MEMCPY ra.
  induction n as [|n IH]; intros regs0 regs m1 m X HDI HRG HK HL1 H90 HLO; [destruct HLO|].
  rewrite sloop_ok_S in HLO. destruct HLO as [HTO HLO]. rewrite sloop_step'.
  destruct (trip _ _ _ _ _ _ _ _ _ FBSAFE MEMCPY MEMSET ADLER TFBITS TFB HH regs0 regs m1 m X HDI HRG HK HL1 ltac:(destruct HK as (_ & _ & HK9); rewrite HK9; exact H90) HTO) as (R1 & M1 & HDI1 & HK1 & HX1).
  unfold DeflSlow6_10.EXITS in HX1. pose proof (brk_wrap X flush HTO) as Hbw.
  revert HLO HDI1 HX1 Hbw. generalize (fst (st_sbody X flush)). intros X' HLO HDI1 HX1 Hbw.
  destruct (snd (st_sbody X flush)) as [| |bs].
  - destruct HX1 as (HRG1 & Hms1).
    destruct (IH regs0 R1 m1 M1 X' HDI1 HRG1 HK1 HL1 H90 HLO) as (R & M & HDI' & HK' & HX').
    exists R, M. split; [exact HDI'|]. split; [exact HK'|].
    unfold LEXIT in *. destruct (snd (deflate_slow_loop n X' flush)) as [bs|].
    + destruct HX' as (A & B & C). split; [exact A|]. split; [exact B|]. eapply msteps_trans; [exact Hms1 | exact C].
    + destruct HX' as (A & W & C). split; [exact A|]. split; [exact W|]. eapply msteps_trans; [exact Hms1 | exact C].
  - exists R1, M1. split; [exact HDI1|]. split; [exact HK1|]. unfold LEXIT. cbn [fst snd]. split; [exact (proj1 HX1)|]. split; [exact (Hbw eq_refl)|exact (proj2 HX1)].
  - exists R1, M1. split; [exact HDI1|]. split; [exact HK1|]. exact HX1.
Qed.


Lemma deflate_tail_fin : forall s fl, fl = Z_FINISH ->
  deflate_tail s fl = (fst (flush_block s 1), match snd (flush_block s 1) with Some bs => bs | None => finish_done end).
Proof using.
  intros s fl ->. unfold deflate_tail. cbn [Z.eqb Z_FINISH Pos.eqb].
  destruct (flush_block s 1) as [s' [bs|]]; reflexivity.
Qed.

Lemma deflate_tail_none : forall s fl, fl <> Z_FINISH -> ds_sym_next s = 0 ->
  deflate_tail s fl = (s, block_done).
Proof using.
  intros s fl Hf Hs. unfold deflate_tail. destruct (Z.eqb_spec fl Z_FINISH); [lia|].
  rewrite Hs. reflexivity.
Qed.

Lemma deflate_tail_fbt : forall s fl, fl <> Z_FINISH -> ds_sym_next s <> 0 ->
  deflate_tail s fl = (fst (flush_block s 0), match snd (flush_block s 0) with Some bs => bs | None => block_done end).
Proof using.
  intros s fl Hf Hs. unfold deflate_tail. destruct (Z.eqb_spec fl Z_FINISH); [lia|].
  destruct (Z.eqb_spec (ds_sym_next s) 0); [lia|]. cbn [negb].
  destruct (flush_block s 0) as [s' [bs|]]; reflexivity.
Qed.

Lemma tail_break1 : forall regs0 regs m1 m X,
  DI m1 m X -> HREGS regs -> KEEP regs0 regs -> strip_inv X -> ds_w_size X = ws -> ds_lit_bufsize X = lbs ->
  (ds_match_available X <> 0 -> 1 <= ds_strstart X) ->
  exists R1 M1, msteps s6_segs (mkst regs (0x19b14 : word) m s6_rom) (mkst R1 (0x19b98 : word) M1 s6_rom)
    /\ DI m1 M1 (if negb (ds_match_available X =? 0) then break1_st X else X) /\ HREGS R1 /\ KEEP regs0 R1.
Proof using HWF HH ra flush.
  intros regs0 regs m1 m X HDI HRG HK HTI Ews Elbs Hma1.
  pose proof (wf_wsz _ HWF) as Wws.
  destruct HTI as [Tstr Tsl Tlook Tih Thm Twm Ths Tml Tms Tpl Tpm Tma Tstrat Tlazy Tsn Tse Twb Thb Tpb Tlh Tlfc Tdfc].
  rewrite Ews in Tsl, Twb, Tpb. rewrite Elbs in Tsn.
  destruct (Z.eqb_spec (ds_match_available X) 0) as [Hz|Hnz]; cbn [negb].
  - destruct (break1a_blk _ _ _ _ _ _ _ _ _ HH regs m1 m X HDI HRG Hz) as (R1 & Hms1 & HRG1 & Hfr1).
    exists R1, m. split; [exact Hms1|]. split; [exact HDI|]. split; [exact HRG1 | keep_via HK Hfr1].
  - destruct (break1b_blk _ _ _ _ _ _ _ _ _ HH regs m1 m X HDI HRG ltac:(lia) ltac:(pose proof (Hma1 Hnz); lia) ltac:(lia) ltac:(lia) Twb Tlfc)
      as (R1 & M1 & Hms1 & HDI1 & HRG1 & Hfr1).
    exists R1, M1. split; [exact Hms1|]. split; [exact HDI1|]. split; [exact HRG1 | keep_via HK Hfr1].
Qed.

Lemma code_fin : forall (R : bvmap 5 word) (o : option block_state),
  getr R 10 = zw (match o with Some bs => bs_code bs | None => 3 end) ->
  getr R 10 = zw (bs_code (match o with Some bs => bs | None => finish_done end)).
Proof using. intros R [bs|] H; exact H. Qed.
Lemma code_blk : forall (R : bvmap 5 word) (o : option block_state),
  getr R 10 = zw (match o with Some bs => bs_code bs | None => 1 end) ->
  getr R 10 = zw (bs_code (match o with Some bs => bs | None => block_done end)).
Proof using. intros R [bs|] H; exact H. Qed.

Lemma tail_fin4 : forall regs0 R3 M3 m1 XB,
  DI m1 M3 XB -> TREGS R3 -> KEEP3 regs0 R3 -> flush = 4 ->
  getr R3 10 = zw S -> getr R3 11 = zw (DeflSlow6_6.fb_bufp p XB) -> getr R3 12 = zw (DeflSlow6_6.fb_len XB) -> getr R3 13 = zw 1 ->
  getr R3 1 = (0x19c0c%bv : word) -> ds_wrap XB = 1 -> flush_ok XB 1 ->
  exists R M, DI m1 M (fst (deflate_tail XB flush)) /\ KEEP3 regs0 R
    /\ msteps s6_segs (mkst R3 (0x1af98 : word) M3 s6_rom) (mkst R (0x19d64 : word) M s6_rom)
    /\ getr R 10 = zw (bs_code (snd (deflate_tail XB flush))) /\ getr R 2 = zw SP.
Proof using HH TFB TFBITS MEMSET MEMCPY ra.
  intros regs0 R3 M3 m1 XB HDI3 HRG3 HK3 F4 A10 A11 A12 A13 A1 HWR HFIN.
  rewrite (deflate_tail_fin XB flush F4).
  destruct (from_fbt _ _ _ _ _ _ _ _ _ FBSAFE MEMCPY MEMSET TFBITS TFB HH regs0 R3 m1 M3 XB HDI3 HRG3 HK3 A10 A11 A12 A13 A1 ltac:(lia) HFIN)
    as (R & M & HDI' & HK' & Hms' & B10 & B2).
  revert HDI' B10. generalize (flush_block XB 1). intros [X9 o] HDI' B10. cbn [fst snd] in HDI', B10 |- *.
  exists R, M. split; [exact HDI'|]. split; [exact HK'|]. split; [exact Hms'|]. split; [| exact B2].
  exact (code_fin _ _ B10).
Qed.

Lemma tail_nf : forall regs0 R3 M3 m1 XB,
  DI m1 M3 XB -> TREGS R3 -> KEEP3 regs0 R3 -> LOC m1 -> flush <> 4 ->
  getr R3 10 = zw (ds_strstart XB) ->
  0 <= ds_strstart XB < 2 ^ 31 -> - 2 ^ 63 <= ds_block_start XB < 2 ^ 63 -> 0 <= ds_sym_next XB < 2 ^ 31 ->
  (ds_sym_next XB <> 0 -> flush_ok XB 0) ->
  exists R M, DI m1 M (fst (deflate_tail XB flush)) /\ KEEP3 regs0 R
    /\ msteps s6_segs (mkst R3 (0x19bd4 : word) M3 s6_rom) (mkst R (0x19d64 : word) M s6_rom)
    /\ getr R 10 = zw (bs_code (snd (deflate_tail XB flush))) /\ getr R 2 = zw SP.
Proof using HH TFB TFBITS MEMSET MEMCPY ra.
  intros regs0 R3 M3 m1 XB HDI3 HRG3 HK3 HL1 F4 Q10 Hstr2 Hbs2 Hsn2 HFBT.
  pose proof (LOC_keep _ _ _ _ _ _ _ _ _ HH _ _ _ HL1 HDI3) as HLM3.
  destruct (fina_blk _ _ _ _ _ _ _ _ _ HH R3 m1 M3 XB HDI3 HRG3 HLM3 Q10 Hstr2 Hbs2 Hsn2) as (R4 & Hms4 & HRG4 & Hargs & Hfr4).
  assert (HK4 : KEEP3 regs0 R4) by (keep3_via HK3 Hfr4).
  unfold fina_pc in Hms4.
  revert Hms4. destruct (Z.eqb_spec (ds_sym_next XB) 0) as [N0|N0]; intros Hms4.
  - rewrite (deflate_tail_none XB flush F4 N0). cbn [fst snd bs_code].
    destruct (b84_blk _ _ _ _ _ _ _ _ _ HH R4 M3 HRG4) as (R5 & Hms5 & HRG5 & Z1 & Hfr5).
    exists R5, M3. split; [exact HDI3|]. split; [keep3_via HK4 Hfr5|].
    split; [eapply msteps_trans; [exact Hms4 | exact Hms5]|].
    split; [exact Z1 | destruct HRG5 as (_ & W2 & _); exact W2].
  - rewrite (deflate_tail_fbt XB flush F4 N0).
    destruct (Hargs N0) as (A10 & A11 & A12 & A13 & A1).
    destruct (from_fin _ _ _ _ _ _ _ _ _ FBSAFE MEMCPY MEMSET TFBITS TFB HH regs0 R4 m1 M3 XB HDI3 HRG4 HK4 A10 A11 A12 A13 A1 (HFBT N0))
      as (R & M & HDI' & HK' & Hms' & B10 & B2).
    revert HDI' B10. generalize (flush_block XB 0). intros [X9 o] HDI' B10. cbn [fst snd] in HDI', B10 |- *.
    exists R, M. split; [exact HDI'|]. split; [exact HK'|].
    split; [eapply msteps_trans; [exact Hms4 | exact Hms']|]. split; [| exact B2].
    exact (code_blk _ _ B10).
Qed.

Lemma tail_disp : forall regs0 regs R3 m M3 m1 XB,
  DI m1 M3 XB -> TREGS R3 -> KEEP3 regs0 R3 -> LOC m1 ->
  (flush = 4 -> getr R3 10 = zw S /\ getr R3 11 = zw (DeflSlow6_6.fb_bufp p XB) /\ getr R3 12 = zw (DeflSlow6_6.fb_len XB) /\ getr R3 13 = zw 1
               /\ getr R3 1 = (0x19c0c%bv : word)) ->
  (flush <> 4 -> getr R3 10 = zw (ds_strstart XB)) ->
  0 <= ds_strstart XB < 2 ^ 31 -> - 2 ^ 63 <= ds_block_start XB < 2 ^ 63 -> 0 <= ds_sym_next XB < 2 ^ 31 ->
  (flush = 4 -> flush_ok XB 1) -> (flush <> 4 -> ds_sym_next XB <> 0 -> flush_ok XB 0) -> ds_wrap XB = 1 ->
  msteps s6_segs (mkst regs (0x19b14 : word) m s6_rom) (mkst R3 (DeflSlow6_7.break2_pc flush) M3 s6_rom) ->
  exists R M, DI m1 M (fst (deflate_tail XB flush)) /\ KEEP3 regs0 R
    /\ msteps s6_segs (mkst regs (0x19b14 : word) m s6_rom) (mkst R (0x19d64 : word) M s6_rom)
    /\ getr R 10 = zw (bs_code (snd (deflate_tail XB flush))) /\ getr R 2 = zw SP.
Proof using HH TFB TFBITS MEMSET MEMCPY ra.
  intros regs0 regs R3 m M3 m1 XB HDI3 HRG3 HK3 HL1 Hfin Hnf Hstr2 Hbs2 Hsn2 HFIN HFBT HWR Hms3.
  unfold break2_pc in Hms3.
  revert Hms3. destruct (Z.eqb_spec flush 4) as [F4|F4]; intros Hms3.
  - destruct (Hfin F4) as (A10 & A11 & A12 & A13 & A1).
    destruct (tail_fin4 regs0 R3 M3 m1 XB HDI3 HRG3 HK3 F4 A10 A11 A12 A13 A1 HWR (HFIN F4)) as (R & M & A & B & C & D & E).
    exists R, M. split; [exact A|]. split; [exact B|]. split; [eapply msteps_trans; [exact Hms3 | exact C]|]. split; [exact D | exact E].
  - destruct (tail_nf regs0 R3 M3 m1 XB HDI3 HRG3 HK3 HL1 F4 (Hnf F4) Hstr2 Hbs2 Hsn2 (HFBT F4)) as (R & M & A & B & C & D & E).
    exists R, M. split; [exact A|]. split; [exact B|]. split; [eapply msteps_trans; [exact Hms3 | exact C]|]. split; [exact D | exact E].
Qed.

Lemma tail_run : forall regs0 regs m1 m X,
  DI m1 m X -> HREGS regs -> KEEP regs0 regs -> LOC m1 -> getr regs0 9 = zw flush -> ds_wrap X = 1 -> stail_ok X flush ->
  let X2 := if negb (ds_match_available X =? 0) then break1_st X else X in
  exists R M, DI m1 M (fst (deflate_tail (tail_st X2) flush)) /\ KEEP3 regs0 R
    /\ msteps s6_segs (mkst regs (0x19b14 : word) m s6_rom) (mkst R (0x19d64 : word) M s6_rom)
    /\ getr R 10 = zw (bs_code (snd (deflate_tail (tail_st X2) flush))) /\ getr R 2 = zw SP.
Proof using HWF HH TFB TFBITS MEMSET MEMCPY ra.
  intros regs0 regs m1 m X HDI HRG HK HL1 H90 HW1 (HTI & Hstr & Hma1 & HT2).
  pose proof (di_sizes _ _ _ HDI) as (Ews & Ehs & Elbs).
  cbv zeta.
  destruct (tail_break1 regs0 regs m1 m X HDI HRG HK HTI Ews Elbs Hma1) as (R1 & M1 & Hms1 & HDI1 & HRG1 & HK1).
  assert (HW2 : ds_wrap (if negb (ds_match_available X =? 0) then break1_st X else X) = 1).
  { destruct (negb (ds_match_available X =? 0)); [rewrite wrap_break1|]; exact HW1. }
  revert HDI1 HT2 HW2. generalize (if negb (ds_match_available X =? 0) then break1_st X else X). intros X2 HDI1 (Hstr2 & Hbs2 & Hsn2 & HFIN & HFBT) HW2.
  pose proof (LOC_keep _ _ _ _ _ _ _ _ _ HH _ _ _ HL1 HDI1) as HLM1.
  destruct (break2_blk _ _ _ _ _ _ _ _ _ HH R1 m1 M1 X2 HDI1 HRG1 HLM1 ltac:(destruct HK1 as (_ & _ & HK9); rewrite HK9; exact H90) Hstr2 Hbs2) as (R3 & M3 & Hms3 & HDI3 & HRG3 & Hfin & Hnf & Hfr3).
  assert (HK3 : KEEP3 regs0 R3) by (keep3_via (DeflSlow6_9.KEEP_3 _ _ HK1) Hfr3).
  rewrite break2_tail in HDI3.
  assert (Vs : ds_strstart (tail_st X2) = ds_strstart X2) by reflexivity.
  assert (Vn : ds_sym_next (tail_st X2) = ds_sym_next X2) by reflexivity.
  assert (Vb : ds_block_start (tail_st X2) = ds_block_start X2) by reflexivity.
  assert (Vbufp : DeflSlow6_6.fb_bufp p (tail_st X2) = DeflSlow6_6.fb_bufp p X2) by reflexivity.
  assert (Vlen : DeflSlow6_6.fb_len (tail_st X2) = DeflSlow6_6.fb_len X2) by reflexivity.
  rewrite <- Vbufp, <- Vlen in Hfin. rewrite <- Vs in Hnf.
  rewrite <- Vs in Hstr2. rewrite <- Vn in Hsn2, HFBT. rewrite <- Vb in Hbs2.
  unfold Z_FINISH in HFIN, HFBT.
  exact (tail_disp regs0 regs R3 m M3 m1 (tail_st X2) HDI3 HRG3 HK3 HL1 Hfin Hnf Hstr2 Hbs2 Hsn2 HFIN HFBT ltac:(unfold tail_st; destruct X2; exact HW2)
           ltac:(eapply msteps_trans; [exact Hms1 | exact Hms3])).
Qed.


Lemma DI_fin : forall m1 m X, DI m1 m X -> agree_out [(sp - 128, 128)] mem m1 ->
  ZR6 m S p zp X /\ agree_out (ZRFo DSLOW_FRAME6 S sp p zp ds (Z.of_nat (length (cs_out_rev (ds_strm X))))) mem m /\ rod6 m /\ ROM m
  /\ (forall x, mem x <> None -> m x <> None)
  /\ lzk ds X.
Proof using.
  intros m1 m X (HB & HR & HS3) Hag1.
  pose proof (BR_out _ _ _ _ _ _ _ _ _ _ _ HB) as (Hsc & Har & Hlens & Hpend & HagF & MS & MP & HGR0).
  pose proof HR as (Cw & Cp & Ch & Zs & Zi & Zo & (HRC & HRD & HAG & MF & HGR) & HC).
  assert (HagO : agree_out (ZRFo DSLOW_FRAME6 S sp p zp ds (Z.of_nat (length (cs_out_rev (ds_strm X))))) mem m).
  { eapply agree_out_trans.
    - eapply agree_out_weaken; [exact Hag1|]. unfold ZRFo, DSLOW_FRAME6. cbn [in_franges]. intros x Hx. lia.
    - eapply agree_out_weaken; [exact HAG|]. unfold DeflSlow6_1.GDo, ZRFo, DSLOW_FRAME6, ds6_SIZE, zsl_SIZE. cbn [in_franges]. intros x Hx. lia. }
  split; [| split; [exact HagO | split; [exact HRC | split; [exact HRD | split; [exact HGR0|]]]]].
  - unfold ZR6, ds6_windowA, ds6_prevA, ds6_headA, ds6_arrays. repeat (split; [assumption|]). exact Zo.
  - destruct HS3 as (E1 & E2 & E3). destruct HC as (Lw & Lp & Lh & Ein & Eout & Hao & Hol).
    pose proof HB as (_ & _ & _ & _ & Epbl & _). unfold lzk.
    repeat (split; [first [assumption | lia]|]). exact Hol.
Qed.

Lemma bvneq' : forall (r k : reg) (z : Z), (bv_unsigned r =? bv_unsigned k) = false -> bv_unsigned k = z -> bv_unsigned r <> z.
Proof using. intros r k z H <-. apply Z.eqb_neq. exact H. Qed.

Local Ltac bvlits :=
  repeat match goal with H : (_ || _)%bool = false |- _ => apply Bool.orb_false_elim in H; destruct H end;
  repeat match goal with H : (bv_unsigned ?r =? bv_unsigned ?k) = false |- _ =>
    let z := eval vm_compute in (bv_unsigned k) in pose proof (bvneq' r k z H eq_refl); clear H end.

Lemma reg_frame_fin : forall (R4 R3 regs : bvmap 5 word),
  getr R4 2 = getr regs 2 ->
  (forall r : reg, reg_in r [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv = true -> getr R4 r = getr regs r) ->
  (forall r : reg, reg_in r [1; 2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv = false -> getr R4 r = getr R3 r) ->
  (getr R3 3 = getr regs 3 /\ getr R3 4 = getr regs 4) ->
  forall r : reg, reg_in r LZ_CLOB = false -> getr R4 r = getr regs r.
Proof using.
  intros R4 R3 regs H2 Hrest Hfr [K3 K4] r Hr.
  pose proof (u5_range r) as Ur.
  destruct (reg_in r [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv) eqn:E1; [exact (Hrest r E1)|].
  destruct (bv_eqb r 2) eqn:E2.
  { assert (Er : r = 2%bv) by (apply bv_eq; unfold bv_eqb in E2; apply Z.eqb_eq in E2; exact E2). subst r. exact H2. }
  assert (E3 : reg_in r [1; 2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv = false).
  { cbn [reg_in] in E1 |- *. rewrite E2. rewrite Bool.orb_false_l. exact E1. }
  rewrite (Hfr r E3).
  destruct (bv_eqb r 0) eqn:E0.
  { assert (Er : r = 0%bv) by (apply bv_eq; unfold bv_eqb in E0; apply Z.eqb_eq in E0; exact E0). subst r. reflexivity. }
  destruct (bv_eqb r 3) eqn:E3'.
  { assert (Er : r = 3%bv) by (apply bv_eq; unfold bv_eqb in E3'; apply Z.eqb_eq in E3'; exact E3'). subst r. exact K3. }
  destruct (bv_eqb r 4) eqn:E4'.
  { assert (Er : r = 4%bv) by (apply bv_eq; unfold bv_eqb in E4'; apply Z.eqb_eq in E4'; exact E4'). subst r. exact K4. }
  exfalso. unfold LZ_CLOB in Hr. cbn [reg_in] in Hr, E1, E3. unfold bv_eqb in *.
  bvlits. lia.
Qed.


Theorem deflate_slow_run : forall regs,
  slow_safe6 FBSAFE ds flush ->
  getr regs 10 = zw S -> getr regs 11 = zw flush -> getr regs 2 = zw sp -> getr regs 1 = ra ->
  exists R m',
    msteps s6_segs (mkst regs (0x19558 : word) mem s6_rom) (mkst R ra m' s6_rom)
    /\ ZR6 m' S p zp (fst (deflate_slow ds flush))
    /\ getr R 10 = zw (bs_code (snd (deflate_slow ds flush)))
    /\ getr R 2 = zw sp
    /\ (forall r : reg, reg_in r LZ_CLOB = false -> getr R r = getr regs r)
    /\ agree_out (ZRFo DSLOW_FRAME6 S sp p zp ds (Z.of_nat (length (cs_out_rev (ds_strm (fst (deflate_slow ds flush))))))) mem m'
    /\ rod6 m'
    /\ ROM m'
    /\ (forall x, mem x <> None -> m' x <> None)
    /\ lzk ds (fst (deflate_slow ds flush)).
Proof using HWF HH TFB TFBITS ADLER MEMSET MEMCPY.
  intros regs (HLO & HTL) P10 P11 P2 P1.
  pose proof (wf_wsz _ HWF) as Wws.
  rewrite deflate_slow_eq.
  revert HLO HTL. generalize (lz_fuel ds). intros n HLO HTL.
  destruct (pro_blk _ _ _ _ _ _ _ _ _ HH regs P10 P11 P2 P1) as (R0 & M0 & Hms0 & HDI0 & HFRM & HL0 & HRG0 & H90 & Hfr0 & Hag0).
  assert (HK0 : KEEP R0 R0) by (unfold DeflSlow6_9.KEEP; repeat split; reflexivity).
  assert (HK0r : getr R0 3 = getr regs 3 /\ getr R0 4 = getr regs 4) by (rewrite (Hfr0 3%bv eq_refl), (Hfr0 4%bv eq_refl); split; reflexivity).
  destruct (loop_run n R0 R0 M0 M0 ds HDI0 HRG0 HK0 HL0 H90 HLO) as (R3 & M3 & HDI3 & HK3 & HX3).
  unfold LEXIT in HX3.
  revert HTL HDI3 HX3. generalize (fst (deflate_slow_loop n ds flush)). intros XL HTL HDI3 HX3.
  assert (FIN : forall R M X (code : Z),
            DI M0 M X -> DeflSlow6_9.KEEP3 R0 R -> getr R 10 = zw code -> getr R 2 = zw SP ->
            msteps s6_segs (mkst regs (0x19558 : word) mem s6_rom) (mkst R (0x19d64 : word) M s6_rom) ->
            exists R' m',
              msteps s6_segs (mkst regs (0x19558 : word) mem s6_rom) (mkst R' ra m' s6_rom)
              /\ ZR6 m' S p zp X /\ getr R' 10 = zw code /\ getr R' 2 = zw sp
              /\ (forall r : reg, reg_in r LZ_CLOB = false -> getr R' r = getr regs r)
              /\ agree_out (ZRFo DSLOW_FRAME6 S sp p zp ds (Z.of_nat (length (cs_out_rev (ds_strm X))))) mem m' /\ rod6 m' /\ ROM m'
              /\ (forall x, mem x <> None -> m' x <> None)
              /\ lzk ds X).
  { intros R M X code HDI HK A10 A2 Hms.
    destruct (epi_blk _ _ _ _ _ _ _ _ _ HH R regs M0 M X HDI (FRM_keep _ _ _ _ _ _ _ _ _ HH M0 M X regs HDI HFRM) P1 A2)
      as (R9 & Hms9 & B2 & B10 & Hrest & Hfr9).
    destruct (DI_fin M0 M X HDI Hag0) as (HZ & Hag & Hrc & Hrd & Hgr & Hk).
    exists R9, M. split; [eapply msteps_trans; [exact Hms | exact Hms9]|].
    split; [exact HZ|]. split; [rewrite B10; exact A10|]. split; [exact B2|].
    split; [apply (reg_frame_fin R9 R regs); [rewrite B2, P2; reflexivity | exact Hrest | exact Hfr9 | destruct HK as (a & b); split; [rewrite a; exact (proj1 HK0r) | rewrite b; exact (proj2 HK0r)]]|].
    split; [exact Hag|]. split; [exact Hrc|]. split; [exact Hrd|]. split; [exact Hgr | exact Hk]. }
  destruct (snd (deflate_slow_loop n ds flush)) as [bs|].
  - destruct HX3 as (A10 & A2 & Hms3). cbn [fst snd].
    exact (FIN R3 M3 XL (bs_code bs) HDI3 (DeflSlow6_9.KEEP_3 _ _ HK3) A10 A2 ltac:(eapply msteps_trans; [exact Hms0 | exact Hms3])).
  - destruct HX3 as (HRG3 & Hwr3 & Hms3). cbv zeta.
    destruct (tail_run R0 R3 M0 M3 XL HDI3 HRG3 HK3 HL0 H90 Hwr3 HTL) as (R4 & M4 & HDI4 & HK4 & Hms4 & A10 & A2).
    exact (FIN R4 M4 _ _ HDI4 HK4 A10 A2 ltac:(eapply msteps_trans; [exact Hms0|]; eapply msteps_trans; [exact Hms3 | exact Hms4])).
Qed.

End Walk.


Theorem deflate_slow_run6_ok :
  forall (ROM : (word -> option byte) -> Prop) (FBSAFE : deflate_state -> option Z -> Z -> Z -> Prop),
    memcpy_run6 -> memset_run6 -> adler32_run6 ROM -> tr_flush_bits_run6 -> tr_flush_block_run6 FBSAFE ->
    rom_local6 ROM ->
    deflate_slow_run6 ROM (fun ds flush => DWF ds /\ slow_safe6 FBSAFE ds flush).
Proof using.
  intros ROM FBSAFE MEMCPY MEMSET ADLER TFBITS TFB HRL.
  unfold deflate_slow_run6, lz_contract6.
  intros mem S p zp ds flush ra sp regs HL Hret HZR HROM [HWF HSAFE] Hfl P10 P11 P2 P1.
  destruct (deflate_slow_run ROM mem S p zp ds flush ra sp FBSAFE MEMCPY MEMSET ADLER TFBITS TFB
              {| dsh_L := HL; dsh_ret := Hret; dsh_zr := HZR; dsh_flush := Hfl; dsh_wf := HWF; dsh_rom := HROM; dsh_roml := HRL |}
              regs HSAFE P10 P11 P2 P1)
    as (R & m' & Hms & HZ & A10 & A2 & Hfr & Hag & Hrc & Hrd & Hgr & Hk).
  exists R, m'. unfold A6_DEFLATE_SLOW. replace (zw 0x19558) with (0x19558%bv : word) by (apply bv_eq; reflexivity).
  split; [exact Hms|]. split; [exact HZ|]. split; [exact A10|]. split; [exact A2|]. split; [exact Hfr|].
  split; [exact Hag|]. split; [exact Hrc|]. split; [exact Hrd|]. split; [exact Hgr | exact Hk].
Qed.
End FXG.
