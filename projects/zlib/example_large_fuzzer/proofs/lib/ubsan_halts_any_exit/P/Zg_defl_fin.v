(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_model Z_slow_kit Z_defl_model Z_defl_kit Z_defl_put4 Z_flushpend.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface DeflateState Trees DeflateLz DeflateBlk Deflate SendModel FillWinModel DeflateSafe.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Section FING.
Variables (L : dlay) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : defl_ctx L inp rest0 lo r me.
Hypothesis HTFB : tr_flush_bits_stmt.

Lemma defl_fing : forall (Q : machine_state -> Prop) (X : deflate_state),
  (flush = 0 \/ flush = 4 \/ flush = 5) -> - 2 <= ds_wrap X <= 2 -> ds_wrap X <> 2 ->
  (flush = 4 -> 0 < ds_wrap X ->
   0 <= ds_pending X /\ ds_pending X + 4 <= 65536 /\ 0 <= cs_adler (ds_strm X) < 2^64 /\ ds_lit_bufsize X = 16384
   /\ 0 <= cs_avail_out (ds_strm X) < 2^31 /\ fp_ok (put_adler X)
   /\ ds_wrap (flush_pending (put_adler X)) = ds_wrap X /\ 0 <= ds_pending (flush_pending (put_adler X)) < 2^64
   /\ Box (length (cs_out_rev (ds_strm (flush_pending (put_adler X)))) <= length rest0)%nat) ->
  (flush <> 4 -> DKE L rest0 lo r F fc me Q (wz 0) X) ->
  (flush = 4 -> ds_wrap X <= 0 -> DKE L rest0 lo r F fc me Q (wz 1) X) ->
  (flush = 4 -> 0 < ds_wrap X -> ds_pending (flush_pending (put_adler X)) = 0 ->
   DKE L rest0 lo r F fc me Q (wz 1) (set_wrap (flush_pending (put_adler X)) (- ds_wrap (flush_pending (put_adler X))))) ->
  (flush = 4 -> 0 < ds_wrap X -> ds_pending (flush_pending (put_adler X)) <> 0 ->
   DKE L rest0 lo r F fc me Q (wz 0) (set_wrap (flush_pending (put_adler X)) (- ds_wrap (flush_pending (put_adler X))))) ->
  DK L flush rest0 lo r F fc me Q 0x17d24 X.
Proof.
  intros Q X HFL RW W2 TRL KOK KEND KT1 KT0. unfold DK. intros until m'. intros DI.
  destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_DEFLATE_IN_STACK, Z_SLOW_STACK in LOsp. apply box in SP16.
  unfold deflR.
  zs. zstep. if_cases KF; zify_cond KF; rewrite ?unsigned_lit in KF by lia.
  -
    assert (F4 : flush = 4) by lia. specialize (KEND F4). specialize (KT1 F4). specialize (KT0 F4). specialize (TRL F4). clear KOK.
    pose proof DI as DI0. destruct DI as (DR & DOUT & ROOM & FR & STK & MU & WM & MI).
    destruct DR as [ZS ST]. destruct ST as [GA _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY1]. open_zs ZS. open_A GA.
    lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
    assert (HW : ds_wrap X = -2 \/ ds_wrap X = -1 \/ ds_wrap X = 0 \/ ds_wrap X = 1) by lia.
    zs.
    destruct HW as [EW|[EW|[EW|EW]]]; rewrite EW; zstep; closed_br.
    1,2,3: zs; zs; eapply (KEND ltac:(lia)); exact DI0.
    assert (WP : 0 < ds_wrap X) by lia. specialize (KT1 WP). specialize (KT0 WP). destruct (TRL WP) as (RP0 & RP4 & RAD & LBS & RAO & FPOK & EWR & RPF & ROOMF).
    clear KEND TRL.
    zs. zs. zstep. closed_br.
    clear GA ZS.
    assert (ESP : bv_unsigned (wz (bv_unsigned (r_sp r) + -64)) = bv_unsigned (r_sp r) + -64) by (apply unsigned_lit; lia).
    eapply (defl_put4 L flush inp rest0 lo r F fc me CTX Q X 0x17e30); [right; reflexivity| exact DI0| exact RP0| exact RP4| exact RAD|].
    intros z1 z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z18 z19 z21 z22 z28 z29 z30 z31 mm (DR4 & DOUT4 & ROOM4 & FR4 & STK4 & MU4 & WM4 & MI4).
    change (wz (97840 + 112)) with (wz 97952). unfold deflR. unfold defl_frame in FR4. unfold defl_W in MU4.
    zs.
    call (flush_pending_spec HTFB L (put_adler X) rest0 (zlength inp) lo).
    1:{ exact DR4. } 1:{ exact DOUT4. } 1:{ exact MI4. } 1:{ rewrite ESP. exact STK4. } 1:{ rewrite ESP. lia. } 1:{ rewrite ESP. unfold dlay_below. lia. }
    1:{ exact IO. } 1:{ exact FPOK. } 1:{ unfold put_adler, putShortMSB, put_byte. dsred. rewrite LBS. reflexivity. }
    1:{ unfold put_adler, putShortMSB, put_byte. dsred. exact RAO. } 1:{ exact (unbox _ ROOMF). } 1:{ reflexivity. }
    name_mem mD.
    lazymatch goal with H : stk psegs mD _ _ |- _ => rename H into STKF end. rewrite ESP in STKF.
    lazymatch goal with H : DREP mD L _ |- _ => rename H into DRF end.
    lazymatch goal with H : dout mD L _ _ |- _ => rename H into DOF end.
    revert DRF DOF EWR RPF ROOMF KT1 KT0. generalize (flush_pending (put_adler X)). intros s2 DRF DOF EWR RPF ROOMF KT1 KT0.

    destruct DRF as [ZSF STF]. destruct STF as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENSF LAYF]. open_A GA.
    pose proof (munch_refl [(dl_As L, dl_As L + 212)] mD) as MUf. pose proof (wmono_refl psegs mD) as WMf.
    assert (RW2 : - 2^31 <= ds_wrap s2 < 2^31) by lia.
    zs. rewrite EWR, EW. zstep. closed_br. zs. zs. name_mem mE. zs.
    tr_groups MUf WMf.
    assert (DIE : DINV L rest0 lo r me (set_wrap s2 (- ds_wrap s2)) mE).
    { split; [split|].
      - exact ZSF.
      - constructor; [do 5 eexists; unfold dsA_cells; dsred; close_cells GA| exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                     | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENSF | exact LAYF].
      - split; [dsred; apply (dout_munch _ mD mE L rest0 _ DOF ROOMF MUf WMf); cbn [disjoint_from]; slia|].
        split; [exact ROOMF|]. split; [exact FR4|]. split; [exact STKF|]. split; [exact MU4|]. split; [exact WM4| eassumption]. }
    destruct (Z.eq_dec (ds_pending s2) 0) as [P0|PN].
    + rewrite P0. zs. zs. eapply (KT1 P0). exact DIE.
    + zs. replace (ds_pending s2 <? 1) with false by (symmetry; apply Z.ltb_ge; lia). change (Z.b2z false) with 0.
      zs. eapply (KT0 PN). exact DIE.
  - zs. zs. eapply (KOK ltac:(lia)). exact DI.
Qed.
End FING.
