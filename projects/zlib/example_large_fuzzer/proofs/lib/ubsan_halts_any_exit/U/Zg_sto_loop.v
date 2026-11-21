(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import InitMem Z_kit Zg_sto_model.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.U Require Import Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_kit Z_tr_kit Z_ukit Z_adler32
     Zg_adler32_iface Zg_defl_iface Zg_sto_ole Zg_sto_kit Zg_sto_head Zg_sto_emit Zg_sto_copy Zg_sto_rdo.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface DeflateState Trees DeflateLz DeflateBlk SendModel FillWinModel ZChkAdl AdlerModel
     RefDeflFast1 RefDeflFastM RefDeflStored2 RefDeflStored4 RefDeflStored5 RefDeflStored6 RefDeflStored7 RefDeflStored8 RefDeflSafeS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition Z_STO_EXIT1 : Z := 0x189f0.

Section LOOP.
Variables (L : dlay) (flush ai0 : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : sto_ctx L inp rest0 lo r me.
Hypothesis HFL : 0 <= flush <= 5.
Hypothesis HTSB : tr_stored_block_stmt.
Hypothesis HTFB : tr_flush_bits_stmt.
Hypothesis HADL : adler32_stmt.
Hypothesis TIEB : Forall (fun b => 0 <= b < 256) inp.

Record TS (X : deflate_state) : Prop := mkTS {
  ts_ti : st_entry X;
  ts_ws : ds_w_size X = 32768;
  ts_lbs : ds_lit_bufsize X = 16384;
  ts_wrap : ds_wrap X <> 2;
  ts_inp : cs_input (ds_strm X) = arr_of_list inp;
  ts_ai : cs_avail_in (ds_strm X) < 2^31;
  ts_ao : cs_avail_out (ds_strm X) < 2^31 }.

Lemma sto_latch : forall (Q : machine_state -> Prop) (last : Z) (X6 : deflate_state),
  (last = 0 -> TK L flush ai0 0 rest0 lo r F fc me Q Z_STO_HEAD X6) ->
  (last = 1 -> TK10 L flush ai0 0 rest0 lo r F fc me Q Z_STO_BREAK (dl_S L) X6) ->
  0 <= last <= 1 ->
  KLATCH L flush ai0 rest0 lo r F fc me Q last X6.
Proof using CTX inp.
  intros Q last X6 KH KB RL. unfold KLATCH. intros until m'. intros INV.
  pose proof INV as (DR & DOUT & RM & FR & STK & MU & WM & MI). unfold sto_frame in FR. unfold Z_STO_LATCH, stoR.
  pose proof (tc_lo _ _ _ _ _ _ CTX) as LOsp. unfold Z_STORED_STACK in LOsp.
  pose proof (bv_unsigned_in_range 64 (r_sp r)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  zstep. br_cases K.
  -
    destruct DR as [ZS ST]. pose proof (st_lay _ _ _ _ ST) as LAY. lay_open LAY.
    pose proof ST as STc. open_DST STc. open_A GA.
    zs. zstep.
    unfold TK10 in KB. replace last with 1 by lia. eapply (KB ltac:(lia)). exact INV.
  -
    unfold TK in KH. replace last with 0 by lia. eapply (KH ltac:(lia)). exact INV.
Qed.

Lemma sto_loop : forall (f : nat) (Q : machine_state -> Prop) (X : deflate_state),
  TS X -> cs_avail_out (ds_strm X) + 1 <= Z.of_nat f ->
  Box (length (cs_out_rev (ds_strm (fst (deflate_stored_loop f X flush 32768)))) <= length rest0)%nat ->
  TK10 L flush ai0 (1 - snd (deflate_stored_loop f X flush 32768)) rest0 lo r F fc me Q Z_STO_BREAK (dl_S L) (fst (deflate_stored_loop f X flush 32768)) ->
  forall lz, TK L flush ai0 lz rest0 lo r F fc me Q Z_STO_HEAD X.
Proof using TIEB HADL HTFB HTSB HFL CTX.
  induction f as [|f IH]; intros Q X TSX FUEL RM KB lz.
  { exfalso. pose proof (se_ao _ (ts_ti _ TSX)). lia. }
  pose proof TSX as [TI WS LBS WRAP INP AI AO].
  pose proof TI as [HV Hp Hpo Hbb Hpbs Hao]. pose proof (vi_bv _ HV) as Vbv. pose proof (vi_ai _ HV) as Vai. pose proof (vi_bs _ HV) as Vbs. pose proof (vi_str _ HV) as Vstr.
  rewrite WS in Vstr.
  rewrite sloop_S' in RM, KB.
  eapply (sto_head L flush ai0 inp rest0 lo r F fc me CTX HFL Q X); [exact Vbv| clear - Hao AO; lia| clear - Vai AI; lia| exact Vbs| clear - Vstr; lia| |].
  { intros Hbr. rewrite Hbr in KB. cbv iota in KB. rewrite fst_pr, snd_pr in KB. exact KB. }
  intros Hbr. rewrite Hbr in RM, KB.
  assert (HH : sb_hdr X <= cs_avail_out (ds_strm X)).
  { unfold sb_broke in Hbr. apply Bool.orb_false_elim in Hbr. destruct Hbr as [Hbr' _]. apply Z.ltb_ge in Hbr'. exact Hbr'. }
  destruct (so_trip_ok_TI X flush 32768 TI ltac:(lia)) as [_ HT]. destruct (HT Hbr) as (EOK & COK & ROK & HVT). clear HT.
  pose proof (sb_left_eq X HV ltac:(lia)) as Eleft.
  pose proof (sb_len_range X ltac:(lia) HH) as (RL1 & RL2 & RL3).
  pose proof (emit1_facts X flush TI HH) as E4. cbv zeta in E4. destruct E4 as (S4 & I4 & P4 & PO4 & BV4 & BB4 & AO4 & TO4 & OL4 & Hhr).
  pose proof S4 as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12). pose proof I4 as (B1 & B2 & B3 & B4 & B5).
  assert (HV4 : so_inv (st_emit1 X flush)) by (apply (so_inv_transport X _ HV S4 I4 TO4); rewrite BV4; lia).
  unfold so_copy_ok in COK. cbv zeta in COK. rewrite Eleft in COK.
  unfold so_rdo_ok in ROK. cbv zeta in ROK. rewrite Eleft in ROK. destruct ROK as [_ ROK].
  pose proof (copy_facts (st_emit1 X flush) (ds_strstart X - ds_block_start X) (sb_len X) HV4 ltac:(lia) ltac:(rewrite A5, A6; reflexivity) ltac:(lia)) as C5. cbv zeta in C5.
  destruct C5 as (HV5 & I5 & P5 & PO5 & BV5 & BB5 & AO5 & OL5 & Hn2 & Hz & Hnz & Hbs5 & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11).
  pose proof I5 as (D1 & D2 & D3 & D4 & D5).
  assert (ETRIP : st_trip X flush = st_rdo (fst (st_copy (st_emit1 X flush) (ds_strstart X - ds_block_start X) (sb_len X)))
                                          (snd (st_copy (st_emit1 X flush) (ds_strstart X - ds_block_start X) (sb_len X)))).
  { unfold st_trip. rewrite Eleft. reflexivity. }
  assert (OLR : (length (cs_out_rev (ds_strm (st_trip X flush))) <= length rest0)%nat).
  { pose proof (unbox _ RM) as R. destruct (sb_lastv X flush =? 0); [| cbv iota in R; rewrite fst_pr in R; exact R].
    cbv iota in R. eapply Nat.le_trans; [apply ole_loop| exact R]. }
  rewrite ETRIP in OLR.
  assert (OLc : (length (cs_out_rev (ds_strm (fst (st_copy (st_emit1 X flush) (ds_strstart X - ds_block_start X) (sb_len X))))) <= length rest0)%nat)
    by (eapply Nat.le_trans; [apply ole_rdo| exact OLR]).
  assert (OLe : (length (cs_out_rev (ds_strm (st_emit1 X flush))) <= length rest0)%nat)
    by (eapply Nat.le_trans; [apply ole_copy| exact OLc]).
  assert (RAO : 0 <= cs_avail_out (ds_strm X) < 2^31) by (clear - Hao AO; lia).
  assert (RAI : 0 <= cs_avail_in (ds_strm X) < 2^31) by (clear - Vai AI; lia).
  assert (RSTR : ds_strstart X <= 65536) by (clear - Vstr; lia).
  refine (sto_emit L flush ai0 inp rest0 lo r F fc me CTX HFL HTSB HTFB Q X RAO RAI Vbs RSTR LBS HH EOK ltac:(constructor; exact OLe) _).
  assert (RAO4 : 0 <= cs_avail_out (ds_strm (st_emit1 X flush)) < 2^31) by (rewrite AO4; clear - RAO HH Hhr; lia).
  assert (RN1 : ds_strstart X - ds_block_start X <> 0 -> lc_len (ds_strstart X - ds_block_start X) (sb_len X) <= cs_avail_out (ds_strm (st_emit1 X flush))).
  { intros NL. destruct (COK NL) as (_ & _ & Hn1 & _). exact Hn1. }
  refine (sto_copy L flush ai0 inp rest0 lo r F fc me CTX Q X (st_emit1 X flush) Vbs RSTR RL1 A6 RAO4 RN1 ltac:(constructor; exact OLc) _).
  revert HV5 I5 P5 PO5 BV5 BB5 AO5 OL5 Hn2 Hz Hnz Hbs5 C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 D1 D2 D3 D4 D5 ROK ETRIP OLR OLc.
  generalize (snd (st_copy (st_emit1 X flush) (ds_strstart X - ds_block_start X) (sb_len X))) as n2.
  generalize (fst (st_copy (st_emit1 X flush) (ds_strstart X - ds_block_start X) (sb_len X))) as X5.
  intros X5 n2. intros.
  pose proof (vi_wrap _ HV5) as Vwr5. pose proof (vi_ad _ HV5) as Vad5. pose proof (vi_ni _ HV5) as Vni5. pose proof (vi_inlen _ HV5) as Vinl5.
  pose proof (vi_ti _ HV5) as Vti5. pose proof (vi_ai _ HV5) as Vai5.
  rewrite D3, B3, INP, arr_len_of_list in Vinl5.
  assert (TIE5 : din_tie inp X5) by (split; [rewrite D3, B3; exact INP| exact TIEB]).
  assert (WR5 : ds_wrap X5 <> 2) by (rewrite C10, A11; exact WRAP).
  assert (RAI5 : 0 <= cs_avail_in (ds_strm X5) < 2^31) by (rewrite D1, B1; clear - RAI; lia).
  assert (RAO5 : 0 <= cs_avail_out (ds_strm X5) < 2^31).
  { rewrite AO5. destruct (Z.eq_dec (ds_strstart X - ds_block_start X) 0) as [E0|E0].
    - rewrite (Hz E0). clear - RAO4. lia.
    - destruct (Hnz E0) as [En2 _]. pose proof (RN1 E0) as Hn1. clear - RAO4 En2 Hn1 Hn2 RL1. lia. }
  assert (RN : n2 = 0 \/ (0 < n2 <= cs_avail_in (ds_strm X5) /\ n2 <= cs_avail_out (ds_strm X5))).
  { destruct (Z.eq_dec n2 0) as [En|En]; [left; exact En| right]. exact (ROK En). }
  refine (sto_rdo L flush ai0 inp rest0 lo r F fc me CTX HADL Q (sb_lastv X flush) X5 n2 TIE5 WR5 Vwr5 Vad5 RAI5 RAO5 Vni5 Vinl5 Vti5 RN ltac:(constructor; exact OLR) _).
  rewrite <- ETRIP.
  pose proof (trip_facts X flush TI ltac:(lia) HH) as T. cbv zeta in T. destruct T as (TI' & S' & BS' & IN' & AN' & AI' & AO' & OLAO' & BV').
  pose proof S' as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11 & W12). dsred in W4. dsred in W2. dsred in W11.
  pose proof (sb_lastv_range X flush) as Rlv.
  refine (sto_latch Q (sb_lastv X flush) (st_trip X flush) _ _ Rlv).
  -
    intros Hl0. rewrite Hl0 in RM, KB. change (0 =? 0) with true in RM, KB. cbv iota in RM, KB.
    assert (TS' : TS (st_trip X flush)).
    { constructor; [exact TI'| rewrite W4; exact WS| rewrite W2; exact LBS| rewrite W11; exact WRAP| rewrite IN'; exact INP| clear - AI AI'; lia| clear - AO AO'; lia]. }
    refine (IH Q (st_trip X flush) TS' ltac:(clear - FUEL AO'; lia) RM KB 0).
  -
    intros Hl1. rewrite Hl1 in KB. change (1 =? 0) with false in KB. cbv iota in KB. rewrite fst_pr, snd_pr in KB. change (1 - 1) with 0 in KB. exact KB.
Qed.
End LOOP.
