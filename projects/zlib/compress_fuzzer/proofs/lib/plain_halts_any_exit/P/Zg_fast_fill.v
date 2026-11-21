(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_model Z_slow_kit Zg_defl_iface Zg_fast_kit.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface DeflateState Trees DeflateLz DeflateBlk FillWinModel
  RefDeflFast1 RefDeflFastM RefDeflFast6 RefDeflSafeW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Section FFILL.
Variables (L : dlay) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : slow_ctx L inp rest0 lo r me.
Hypothesis HFW : fill_window_stmtg.

Lemma fast_fill : forall (Q : machine_state -> Prop) (X : deflate_state),
  trip_ok 32768 32768 X flush -> 0 <= flush <= 5 ->
  ds_wrap X <> 2 -> cs_avail_in (ds_strm X) < 2^31 -> din_tie inp X ->
  (forall X1, st_fill X flush = (X1, Some (LRet need_more)) -> FKret L flush rest0 lo r F fc me Q 0 X1) ->
  (forall X1, st_fill X flush = (X1, Some LBreak) -> FK L flush rest0 lo r F fc me Q Z_FAST_TAIL X1) ->
  (forall X1, st_fill X flush = (X1, None) -> 3 <= ds_lookahead X1 -> FK L flush rest0 lo r F fc me Q Z_FAST_HASH X1) ->
  (forall X1, st_fill X flush = (X1, None) -> ds_lookahead X1 < 3 -> FK L flush rest0 lo r F fc me Q Z_FAST_MTEST X1) ->
  FK L flush rest0 lo r F fc me Q Z_FAST_HEAD X.
Proof.
  intros Q X (RLA & FWOK & RLA1 & _) HFL WRAP AIN TIE KRET KBRK KHASH KLO.
  unfold FK. intros until m'. intros (DR & DOUT & ROOM & (j0 & FR) & STK & MU & WM & MI). rename m' into m.
  destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_SLOW_STACK in LOsp. apply box in SP16.
  pose proof DR as DR0. destruct DR as [ZS ST]. open_DST ST. open_A GA. lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  unfold fastR, Z_FAST_HEAD. unfold fast_frame in FR. unfold slow_W in MU.
  change MIN_LOOKAHEAD with 262 in *.
  unfold FKret, FK, fastR, Z_FAST_EPI, Z_FAST_TAIL, Z_FAST_HASH, Z_FAST_MTEST in KRET, KBRK, KHASH, KLO.
  zs. zstep.
  if_cases KLA; zify_cond KLA; rewrite ?unsigned_lit in KLA by lia.
  -
    assert (EF : st_fill X flush = (X, None)).
    { unfold st_fill. change MIN_LOOKAHEAD with 262. replace (ds_lookahead X <? 262) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
    eapply (KHASH X EF ltac:(lia)).
    split; [exact DR0|]. split; [exact DOUT|]. split; [exact ROOM|]. split; [exists j0; exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| exact MI].
  -
    assert (ESP : bv_unsigned (wz (bv_unsigned (r_sp r) + -128)) = bv_unsigned (r_sp r) + -128) by (apply unsigned_lit; lia).
    pose proof (fill_window_keep X) as KEEP. unfold fw_keep in KEEP.
    assert (EO : cs_out_rev (ds_strm (fill_window X)) = cs_out_rev (ds_strm X)) by (decompose [and] KEEP; assumption).
    clear KEEP.
    pose proof (unbox _ ROOM) as OL0.
    unfold dout in DOUT. pose proof (outv_length rest0 (ds_strm X) OL0) as OL.
    clear GA ZS GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend.
    zs. zs.
    call (HFW L X inp (Z.of_nat (length rest0)) lo).
    1:{ exact DR0. } 1:{ apply (slow_din L inp rest0 lo r me CTX). unfold slow_W. exact MU. } 1:{ exact TIE. } 1:{ exact MI. }
    1:{ rewrite ESP. exact STK. } 1:{ unfold Z_FILLWIN_STACKG. lia. } 1:{ rewrite ESP. pose proof (unbox _ SP16). Z.div_mod_to_equations. lia. }
    1:{ unfold dlay_below. lia. } 1:{ exact IO. } 1:{ apply FWOK. lia. } 1:{ exact WRAP. } 1:{ exact AIN. } 1:{ reflexivity. }
    name_mem mA. rewrite ESP in PC.
    lazymatch goal with H : DREP _ _ (fill_window X) |- _ => rename H into DR1 end.
    assert (SI1 : FINV L flush rest0 lo r me (fill_window X) mA).
    { split; [exact DR1|]. split; [unfold dout, outv; rewrite EO; exact DOUT|]. split; [rewrite EO; exact ROOM|].
      split; [exists j0; exact FR|]. split; [exact PC|]. split; [exact MU|]. split; [exact WM| eassumption]. }
    remember (fill_window X) as X1 eqn:EX1.
    assert (EFm : st_fill X flush = (X1, if (ds_lookahead X1 <? 262) && (flush =? Z_NO_FLUSH) then Some (LRet need_more)
                                        else if ds_lookahead X1 =? 0 then Some LBreak else None)).
    { unfold st_fill. change MIN_LOOKAHEAD with 262. replace (ds_lookahead X <? 262) with true by (symmetry; apply Z.ltb_lt; lia).
      rewrite <- EX1. destruct (_ && _); [reflexivity|]. destruct (_ =? 0); reflexivity. }
    rewrite EFm, fst_prf in RLA1.
    destruct DR1 as [ZS ST]. open_DST ST. open_A GA.
    clear DR0 DOUT OL OL0 EO.
    zs. zs.
    unfold Z_NO_FLUSH, Z_FINISH in *.

    assert (CONT : (ds_lookahead X1 <? 262) && (flush =? 0) = false ->
      forall a1 a5 a6 a7 a11 a12 a13 a14 a15 a16 a17 a18 a19 a28 a29 a30 a31,
      evt psegs Q (MS (fastR L r a1 a5 a6 a7 (wz (ds_lookahead X1)) a11 a12 a13 a14 a15 a16 a17 a18 a19 a28 a29 a30 a31)
          F (wz 0x19048) fc None mA (seg_rom psegs))).
    { intros EC. intros. unfold fastR. rewrite EC in EFm.
      zstep. if_cases KZ; zify_cond KZ; rewrite ?unsigned_lit in KZ by lia.
      -
        replace (ds_lookahead X1 =? 0) with true in EFm by (symmetry; apply Z.eqb_eq; lia).
        eapply (KBRK X1 EFm). exact SI1.
      - replace (ds_lookahead X1 =? 0) with false in EFm by (symmetry; apply Z.eqb_neq; lia).
        zstep. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia.
        +
          eapply (KLO X1 EFm ltac:(lia)). exact SI1.
        + eapply (KHASH X1 EFm ltac:(lia)). exact SI1. }
    zstep. if_cases KF; zify_cond KF; rewrite ?unsigned_lit in KF by lia.
    +
      eapply CONT. replace (flush =? 0) with false by (symmetry; apply Z.eqb_neq; lia). apply andb_false_r.
    + zs. zstep. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
      *
        replace (flush =? 0) with true in EFm by (symmetry; apply Z.eqb_eq; lia).
        replace (ds_lookahead X1 <? 262) with true in EFm by (symmetry; apply Z.ltb_lt; lia).
        zs. zs. eapply (KRET X1 EFm). exact SI1.
      * eapply CONT. replace (ds_lookahead X1 <? 262) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.
End FFILL.
