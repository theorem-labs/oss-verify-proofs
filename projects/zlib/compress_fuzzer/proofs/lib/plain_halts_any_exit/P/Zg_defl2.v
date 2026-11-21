(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_kit Z_defl_model Z_defl_kit
  Z_defl_path Z_defl_entry Z_defl_arms Z_defl_pend Z_defl_hdr Z_defl_blocks Z_defl_fin
  Z_adler32 Zg_adler32_iface Zg_defl_iface Zg_defl_iface2 Zg_defl_path Zg_defl_path2 Zg_defl_entry Zg_defl_pend Zg_defl_hdr Zg_defl_blocks Zg_defl_blocks2 Zg_defl_fin Zg_defl.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface DeflateState Trees DeflateLz DeflateBlk Deflate SendModel FillWinModel RefDeflFast6 RefDeflSlow6 RefDeflSafeS DeflateSafe.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Section ASMG2.
Variables (L : dlay) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : defl_ctx L inp rest0 lo r me.
Hypothesis HSTO : deflate_stored_stmt.
Hypothesis HFAST : deflate_fast_stmtg.
Hypothesis HSLOW : deflate_slow_stmtg.
Hypothesis HTFB : tr_flush_bits_stmt.
Hypothesis HFL : flush = 0 \/ flush = 4 \/ flush = 5.

Variables (R : deflate_state * Z) (Q : machine_state -> Prop).
Hypothesis EXIT : forall X rc, R = (X, rc) -> DKE L rest0 lo r F fc me Q (wz rc) X.
Hypothesis ROOMR : (length (cs_out_rev (ds_strm (fst R))) <= length rest0)%nat.

Lemma room_of_oleg2 : forall X, ole R X -> Box (length (cs_out_rev (ds_strm X)) <= length rest0)%nat.
Proof. intros X [OL _]. apply box. lia. Qed.

Lemma asmg2_lf : forall X, R = (set_last_flush X (-1), 0) -> DKL L flush rest0 lo r F fc me Q X.
Proof. intros X ER. apply (defl_lf L flush inp rest0 lo r F fc me CTX). exact (EXIT _ _ ER). Qed.

Lemma asmg2_fin : forall X, fin_path flush R X -> DK L flush rest0 lo r F fc me Q 0x17b88 X.
Proof.
  intros X (OL & RW & W2 & E0 & E1 & TR).
  apply (defl_fing L flush inp rest0 lo r F fc me CTX HTFB Q X HFL RW W2).
  - intros F4 WP. destruct (TR F4 WP) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & _).
    split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|]. split; [exact A6|].
    split; [exact A7|]. split; [exact A8|]. exact (room_of_oleg2 _ A9).
  - intros F4. exact (EXIT _ _ (E0 F4)).
  - intros F4 WN. exact (EXIT _ _ (E1 F4 WN)).
  - intros F4 WP P0. destruct (TR F4 WP) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & T1 & _). exact (EXIT _ _ (T1 P0)).
  - intros F4 WP PN. destruct (TR F4 WP) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & T0). exact (EXIT _ _ (T0 PN)).
Qed.

Lemma asmg2_run : forall X, blocks_pathg2 inp flush R X -> blk_cond X flush = true -> DK L flush rest0 lo r F fc me Q 0x17a10 X.
Proof.
  intros X (OL & RAI & RLA & RST & PT & _) HC.
  destruct (PT HC) as (LV & SG & TIE & WS & HS & LBS & W1 & RAO & SE & SAFEF & SAFES & OL1 & RAO2 & ENM0 & ENM1 & EFS0 & EFS1 & KF & KBD).
  assert (W2 : ds_wrap X <> 2) by lia. assert (W0 : ds_wrap X <> 0) by lia. assert (WRG : - 2 <= ds_wrap X <= 2) by lia.
  apply (defl_rung2 L flush inp rest0 lo r F fc me CTX HTFB HSTO HFAST HSLOW Q X HFL LV SG TIE WS HS LBS W2 W0 WRG (proj2 RAI) RAO SE SAFEF SAFES (room_of_oleg2 _ OL1) RAO2).
  - intros Hb A0. exact (asmg2_lf _ (ENM0 Hb A0)).
  - intros Hb AN. exact (EXIT _ _ (ENM1 Hb AN)).
  - intros Hb A0. exact (asmg2_lf _ (EFS0 Hb A0)).
  - intros Hb AN. exact (EXIT _ _ (EFS1 Hb AN)).
  - intros Hb. exact (asmg2_fin _ (KF Hb)).
  - intros Hb. destruct (KBD Hb) as (F5 & FP & LB1 & OLF & RAOF & E0 & E1).
    split; [exact F5|]. split; [exact FP|]. split; [exact LB1|]. split; [exact (room_of_oleg2 _ OLF)|]. split; [exact RAOF|].
    split; [intros A0; exact (EXIT _ _ (E0 A0))| intros AN; exact (asmg2_fin _ (E1 AN))].
Qed.

Lemma asmg2_blk98 : forall X, blocks_pathg2 inp flush R X -> cs_avail_in (ds_strm X) = 0 -> DK L flush rest0 lo r F fc me Q 0x17a08 X.
Proof.
  intros X BP A0. pose proof BP as (OL & RAI & RLA & RST & PT & PF).
  assert (EC : blk_cond X flush = negb (ds_lookahead X =? 0) || (negb (flush =? Z_NO_FLUSH) && negb (ds_status X =? FINISH_STATE)))
    by (unfold blk_cond; rewrite A0; reflexivity).
  apply (defl_blk98g L flush rest0 lo r F fc me Q X HFL A0 RLA RST).
  - intros C. apply (asmg2_run X BP). rewrite EC. exact C.
  - intros C F0. destruct (PF ltac:(rewrite EC; exact C)) as (_ & _ & _ & E0 & _). exact (EXIT _ _ (E0 ltac:(lia))).
  - intros C FN. apply asmg2_fin. apply PF. rewrite EC. exact C.
Qed.

Lemma asmg2_blk90 : forall X, blocks_pathg2 inp flush R X -> DK L flush rest0 lo r F fc me Q 0x17a00 X.
Proof.
  intros X BP. pose proof BP as (OL & RAI & _).
  apply (defl_blk90g L flush rest0 lo r F fc me Q X RAI).
  - intros AN. apply (asmg2_run X BP). unfold blk_cond.
    replace (cs_avail_in (ds_strm X) =? 0) with false by (symmetry; apply Z.eqb_neq; exact AN). reflexivity.
  - intros A0. exact (asmg2_blk98 X BP A0).
Qed.

Lemma asmg2_body : forall X, body_pathg2 inp flush R X -> DKB L flush rest0 lo r F fc me Q X.
Proof.
  intros X (OL & HST & RAI & EERR & B98 & B90 & HDR).
  apply (defl_dispg L flush inp rest0 lo r F fc me CTX Q X HST RAI).
  - intros E42. pose proof (HDR E42) as HH. cbv zeta in HH.
    destruct HH as (W1 & WB & LV & SG & RSS & RP0 & RP6 & LBS & RAD & RAO & FPOK & ST5 & RP5 & OL5 & E5 & B5).
    apply (defl_hdrg L flush inp rest0 lo r F fc me CTX HTFB Q X W1 WB LV SG RSS RP0 RP6 LBS RAD RAO FPOK ST5 RP5 (room_of_oleg2 _ OL5)).
    + intros PN. exact (asmg2_lf _ (E5 PN)).
    + intros P0. exact (asmg2_blk90 _ (B5 P0)).
  - intros E113. exact (asmg2_blk90 _ (B90 E113)).
  - intros E666 A0. exact (asmg2_blk98 _ (B98 E666 A0) A0).
  - intros E666 AN. exact (EXIT _ _ (EERR E666 AN)).
Qed.

Lemma asmg2_top : forall (d : deflate_state) (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  defl_pathg2 inp flush R d -> DREP me L d -> dout me L rest0 (ds_strm d) -> stk psegs me lo (bv_unsigned (r_sp r)) -> mem_inv psegs me ->
  evt psegs Q (MS (mkR (r_ra r) (r_sp r) (r_gp r) (r_tp r) t0 t1 t2 (r_s0 r) (r_s1 r) (wz (dl_S L)) (wz flush) a2 a3 a4 a5 a6 a7
                       (r_s2 r) (r_s3 r) (r_s4 r) (r_s5 r) (r_s6 r) (r_s7 r) (r_s8 r) (r_s9 r) (r_s10 r) (r_s11 r) t3 t4 t5 t6)
                  F (wz Z_DEFLATE_PC) fc None me (seg_rom psegs)).
Proof.
  intros until t6. intros PATH DR DOUT STK MI. cbv zeta in PATH. destruct PATH as (OL & HST & RAI & RNI & PERR & POK).
  apply (defl_entryg L inp rest0 lo r F fc me CTX Q d flush t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 DR DOUT (room_of_oleg2 _ OL) STK MI HST ltac:(lia) RAI RNI).
  - intros C. exact (EXIT _ _ (PERR C)).
  - intros NE. destruct (POK NE) as (RAO & RLF & RP & LBS & EBUF & PGO).
    intros y1 y5 y6 y7 y9 y12 y15 y16 y17 y28 y29 y30 y31 m' DI.
    apply (defl_pendg L flush inp rest0 lo r F fc me CTX HTFB Q d y1 y5 y6 y7 y9 y12 y15 y16 y17 y28 y29 y30 y31 m' DI HFL RAO RAI RLF RP LBS).
    + intros AN PN. exact (proj1 (proj1 (PGO AN) PN)).
    + intros AN PN. exact (proj1 (proj2 (proj1 (PGO AN) PN))).
    + intros AN PN. exact (room_of_oleg2 _ (proj1 (proj2 (proj2 (proj1 (PGO AN) PN))))).
    + intros A0. exact (EXIT _ _ (EBUF A0)).
    + intros AN PN A2. exact (asmg2_lf _ (proj1 (proj2 (proj2 (proj2 (proj1 (PGO AN) PN)))) A2)).
    + intros AN PN A2. exact (asmg2_body _ (proj2 (proj2 (proj2 (proj2 (proj1 (PGO AN) PN)))) A2)).
    + intros AN P0 RK. exact (EXIT _ _ (proj1 (proj2 (PGO AN) P0) RK)).
    + intros AN P0 NRK. exact (asmg2_body _ (proj2 (proj2 (PGO AN) P0) NRK)).
Qed.
End ASMG2.

Section DEFLG2.
Hypothesis HSTO : deflate_stored_stmt.
Hypothesis HFAST : deflate_fast_stmtg.
Hypothesis HSLOW : deflate_slow_stmtg.
Hypothesis HTFB : tr_flush_bits_stmt.

Theorem deflate_in_specg2 : deflate_in_stmtg2.
Proof.
  unfold deflate_in_stmtg2. intros until m. intros DR DIN DOUT MI RL STK LO SP16 BEL IO HFL PATH ROOM -> ->.
  set (r := mkSR ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
  assert (CTX : defl_ctx L inp rest0 lo r m).
  { constructor; [exact LO| exact SP16| exact (st_lay _ _ _ _ (proj2 DR))| exact BEL| exact IO| exact RL| exact DIN]. }
  revert PATH ROOM. generalize (deflate_core d flush). intros R PATH ROOM.
  assert (EXIT : forall X rc, R = (X, rc) ->
            DKE L rest0 lo r F fc m (deflate_in_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L (fst R) (snd R) inp rest0 lo m) (wz rc) X).
  { intros X rc ER. subst R. cbn [fst snd]. unfold DKE.
    intros y1 y5 y6 y7 y8 y9 y10 y11 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y28 y29 y30 y31 m' DI.
    eapply evt_mono; [exact (defl_epi L inp rest0 lo r F fc m CTX X (wz rc) y1 y5 y6 y7 y8 y9 y10 y11 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y28 y29 y30 y31 m' DI)|].
    intros ms' P. unfold deflate_in_post. rewrite Z_to_bv_mod64. exact P. }
  unfold Z_NO_FLUSH, Z_FINISH, Z_BLOCK in HFL.
  exact (asmg2_top L flush inp rest0 lo r F fc m CTX HSTO HFAST HSLOW HTFB HFL R _ EXIT ROOM d t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 PATH DR DOUT STK MI).
Qed.
End DEFLG2.
