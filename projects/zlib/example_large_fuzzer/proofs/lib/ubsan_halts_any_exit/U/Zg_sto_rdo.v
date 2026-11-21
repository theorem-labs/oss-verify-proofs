(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import InitMem Z_kit Zg_sto_model.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.U Require Import Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_kit Z_tr_kit Z_ukit Z_fw_model Zg_fw_model
     Z_readbuf Zg_adler32_iface Zg_readbuf Zg_defl_iface Zg_sto_kit Zg_sto_head Zg_sto_emit Zg_sto_copy.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface DeflateState Trees DeflateLz DeflateBlk SendModel FillWinModel ZChkAdl AdlerModel
     RefDeflFast1 RefDeflFastM RefDeflStored1 RefDeflStored2 RefDeflStored4 RefDeflStored5 RefDeflStored6 RefDeflStored7 RefDeflStored8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).


Definition rdo_strm (s : deflate_state) (l : list Z) (n : Z) : cstrm :=
  let st := rbo_strm s l n in cset_total_out (cset_avail_out st (cs_avail_out st - n)) (wrap64 (cs_total_out st + n)).

Lemma st_rdo_set : forall s n, 0 < n <= cs_avail_in (ds_strm s) -> ds_wrap s <> 2 ->
  st_rdo s n = set_strm s (rdo_strm s (arr_slice (cs_input (ds_strm s)) (cs_next_in (ds_strm s)) n) n).
Proof.
  intros s n Hn W2. unfold st_rdo. replace (negb (n =? 0)) with true by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; lia).
  rewrite (read_buf_eqo s n n) by (first [unfold rb_len; symmetry; apply rb_len_eq; exact Hn | lia | exact W2]).
  reflexivity.
Qed.

Lemma rdo_cells : forall L s l n p1 p2 p3 resv,
  zs_call_cells L (rdo_strm s l n) p1 p2 p3 resv =
  [C8 (wz (dl_NI L + (cs_next_in (ds_strm s) + n))); C4 (wz (cs_avail_in (ds_strm s) - n)); CB 4 p1;
   C8 (wz (wrap64 (cs_total_in (ds_strm s) + n)));
   C8 (wz (dl_NO L + Z.of_nat (length (rev_append l (cs_out_rev (ds_strm s)))))); C4 (wz (cs_avail_out (ds_strm s) - n)); CB 4 p2;
   C8 (wz (wrap64 (cs_total_out (ds_strm s) + n)));
   C8 (wz (msg_ptr (cs_msg (ds_strm s)))); C8 (wz (dl_As L)); C8 (wz Z_ZCALLOC); C8 (wz Z_ZCFREE); C8 (wz 0);
   C4 (wz (cs_data_type (ds_strm s))); CB 4 p3; C8 (wz (rbn_adler s l)); C8 resv].
Proof.
  intros. unfold zs_call_cells, zs_priv_cells, rdo_strm, rbo_strm, rbn_adler, cs_emit. destruct (ds_wrap s =? 1); reflexivity.
Qed.

Lemma rdo_out : forall s l n, cs_out_rev (rdo_strm s l n) = rev_append l (cs_out_rev (ds_strm s)).
Proof. intros. unfold rdo_strm, rbo_strm, cs_emit. destruct (ds_wrap s =? 1); reflexivity. Qed.

Section RDO.
Variables (L : dlay) (flush ai0 : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : sto_ctx L inp rest0 lo r me.
Hypothesis HADL : adler32_stmt.

Definition KLATCH (Q : machine_state -> Prop) (last : Z) (X6 : deflate_state) : Prop :=
  forall (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y20 y21 y28 y29 y30 y31 : word) (m' : mem),
    STOINV L flush rest0 lo r me X6 m' ->
    evt usegs Q (MS (stoR L flush ai0 last r y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y20 y21 y28 y29 y30 y31)
                    F (wz Z_STO_LATCH) fc None m' (seg_rom usegs)).

Variables (Q : machine_state -> Prop) (last : Z) (X5 : deflate_state) (n : Z).
Hypothesis TIE : din_tie inp X5.
Hypothesis HV5 : so_inv X5.
Hypothesis WRAP : ds_wrap X5 <> 2.
Hypothesis RWR : 0 <= ds_wrap X5 <= 2.
Hypothesis RAD : 1 <= ds_wrap X5 -> 0 <= cs_adler (ds_strm X5) < 2^64.
Hypothesis RAI : 0 <= cs_avail_in (ds_strm X5) < 2^31.
Hypothesis RAO : 0 <= cs_avail_out (ds_strm X5) < 2^31.
Hypothesis RNI : 0 <= cs_next_in (ds_strm X5).
Hypothesis RINL : cs_next_in (ds_strm X5) + cs_avail_in (ds_strm X5) <= zlength inp.
Hypothesis RTI : 0 <= cs_total_in (ds_strm X5) < 2^64.
Hypothesis RN : n = 0 \/ (0 < n <= cs_avail_in (ds_strm X5) /\ n <= cs_avail_out (ds_strm X5)).
Hypothesis RM6 : Box (length (cs_out_rev (ds_strm (st_rdo X5 n))) <= length rest0)%nat.
Hypothesis KL : KLATCH Q last (st_rdo X5 n).

Lemma sto_rdo : KRDO L flush ai0 rest0 lo r F fc me Q last X5 n.
Proof using KL RM6 RN RTI RINL RNI RAO RAI RAD RWR WRAP TIE HADL CTX inp.
  unfold KRDO. intros until m'. intros INV.
  pose proof INV as (DR & DOUT & RM & FR & STK & MU & WM & MI). unfold sto_frame in FR. unfold Z_STO_RDO, stoR.
  pose proof (tc_lo _ _ _ _ _ _ CTX) as LOsp. unfold Z_STORED_STACK in LOsp.
  pose proof (tc_sp16 _ _ _ _ _ _ CTX) as SP16.
  pose proof (bv_unsigned_in_range 64 (r_sp r)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  destruct DR as [ZS ST]. pose proof (st_lay _ _ _ _ ST) as LAY. lay_open LAY.
  pose proof (tc_bel _ _ _ _ _ _ CTX) as BEL. pose proof BEL as BEL'. below_open BEL'.
  pose proof (tc_io _ _ _ _ _ _ CTX) as IO. pose proof IO as IO'. io_open IO'.
  pose proof (lo_S _ LAY) as BKS. unfold blk_ok in BKS.
  unfold KLATCH in KL. pose proof TIE as [TIE1 TIE2].
  assert (RNz : 0 <= n < 2^31) by lia.
  zstep. br_cases K.
  {
    assert (En : n = 0) by lia. rewrite En, st_rdo_0 in KL. eapply KL. exact INV. }
  assert (RN' : 0 < n <= cs_avail_in (ds_strm X5) /\ n <= cs_avail_out (ds_strm X5)) by lia. clear RN.
  assert (KLn : (length (cs_out_rev (ds_strm X5)) + Z.to_nat n <= length rest0)%nat).
  { pose proof (unbox _ RM6) as R6. rewrite (st_rdo_set X5 n) in R6 by first [lia| exact WRAP]. dsred in R6. rewrite rdo_out, rev_append_rev, length_app, length_rev, arr_slice_length' in R6. lia. }
  pose proof (sto_din _ _ _ _ _ _ CTX m' MU) as DIN.
  pose proof ST as STc. open_DST STc. open_A GA. pose proof ZS as ZSc. open_zs ZSc.
  zs. gF. zstep. al8 (dl_S L). gF. zs. zstep.
  assert (ESP : bv_unsigned (wz (bv_unsigned (r_sp r) + -112)) = bv_unsigned (r_sp r) + -112) by (apply unsigned_lit; lia).
  clear GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY0 ZSc. unfold sto_W, slow_W in MU.
  zstep. call (read_buf_out_spec HADL L X5 inp rest0 lo n (dl_NO L + Z.of_nat (length (cs_out_rev (ds_strm X5))))).
  1:{ split; [exact ZS| exact ST]. } 1:{ exact DIN. } 1:{ exact TIE. } 1:{ exact DOUT. } 1:{ exact MI. }
  1:{ rewrite ESP. exact STK. } 1:{ unfold Z_READBUF_STACK. rewrite ESP. lia. } 1:{ rewrite ESP. clear - SP16 RSP LOsp. Z.div_mod_to_equations. lia. }
  1:{ rewrite ESP. eapply dlay_below_lower; [exact BEL| lia]. } 1:{ exact IO. } 1:{ lia. } 1:{ lia. } 1:{ exact RWR. } 1:{ exact WRAP. }
  1:{ intros W1. apply RAD. lia. } 1:{ exact RNI. } 1:{ exact RAI. } 1:{ exact RINL. } 1:{ exact RTI. } 1:{ reflexivity. }
  name_mem m2. rewrite ESP in PC. rename PC into STK2. rename PC1 into ST2. clear DIN ZS ST.
  assert (Erb : rb_len X5 n = n) by (unfold rb_len; apply rb_len_eq; lia). rewrite Erb in *.
  rewrite (proj2 (Z.eqb_neq n 0)) in PC0, POST by lia.
  destruct PC0 as (q1 & q2 & q3 & qr & ZS2). unfold rbo_zs in ZS2.
  remember (arr_slice (cs_input (ds_strm X5)) (cs_next_in (ds_strm X5)) n) as l eqn:El.
  assert (Ll : length l = Z.to_nat n) by (rewrite El; apply arr_slice_length').
  remember (length (cs_out_rev (ds_strm X5))) as k eqn:Ek.
  unfold dout in POST. pose proof (outv_length rest0 (cs_emit (ds_strm X5) l) ltac:(rewrite cs_emit_out_len, Ll, <- Ek; lia)) as OL2.
  pose proof ST2 as STc. open_DST STc. open_A GA. clear GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY0.
  pose proof (munch_refl [(dl_S L, dl_S L + 112)] m2) as MUf. pose proof (wmono_refl usegs m2) as WMf.
  zs. gF. zstep. al8 (dl_S L). gF.
  zs. zstep. zstep. rewrite ?Z.mod_small by lia. zstep. gF. gF. gF.
  zs. zs. zs. zstep. zs. zs. zs. name_mem m3.
  zstep. eapply KL.
  rewrite (st_rdo_set X5 n) by first [lia| exact WRAP]. rewrite <- El.
  split; [split|].
  - exists q1, q2, q3, qr. dsred. rewrite rdo_cells. rewrite rev_append_rev, length_app, length_rev, Ll. close_cells ZS2.
  - apply DST_set_strm; [intros HB; exact HB|]. eapply DST_agree; [exact ST2|].
    eapply ag_blocks_munch; [exact LAY| exact MUf| exact WMf| cbn [disjoint_from]; slia| cbn [disjoint_from]; slia| cbn [disjoint_from]; slia| cbn [disjoint_from]; slia| cbn [disjoint_from]; slia].
  - split; [unfold dout; dsred; replace (outv rest0 (rdo_strm X5 l n)) with (outv rest0 (cs_emit (ds_strm X5) l)) by (unfold outv; rewrite rdo_out; reflexivity); exact POST|].
    split; [constructor; dsred; rewrite rdo_out, rev_append_rev, length_app, length_rev, Ll, <- Ek; clear - KLn; lia|].
    split; [exact FR|]. split; [exact STK2|]. split; [exact MU|]. split; [exact WM| assumption].
Qed.
End RDO.
