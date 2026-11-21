(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import
  Prog ZIface InflateState Inftrees InflateFast InflateArms Inflate InflateGarbBase InflateGarbFast InflateGarb ItCovIface ItCovRep InftreesCoverage.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateInv InflateInvRun InflateInvTab InflateInvDec InflateInvKit InflateInvCov InflateInvArms1 InflateInvArms3 InflateInvArms4 InflateInvArms5 InflateInvArms6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateInvTbl.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S Require Import Callee6i InflA_ClS.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem cl_pinv : forall (NI NO WN TOT0 : Z) s c r,
  pinv NI NO WN TOT0 (mkW s c r) -> is_mode s = CODELENS -> is_nlen s + is_ndist s <= is_have s -> ir_ret r = 0 ->
  arr_get (is_lens s) 256 <> 0 -> it_ret (cd_call1 s) = 0 -> it_ret (cd_call2 (cd_S1 s (cd_call1 s))) = 0 ->
  pinv NI NO WN TOT0 (mkW (iset_mode (cd_S2 (cd_S1 s (cd_call1 s)) (cd_call2 (cd_S1 s (cd_call1 s)))) LEN_) c (irset_ret r 0)).
  Proof.
    intros NI NO WN TOT0 s c r PI Hm HV R0 E256 R1 R2.
    pose proof PI as ([NI32 NO32] & _).
    remember (cd_call1 s) as q1 eqn:EQ1. destruct q1 as [[[[ret1 tbl1] next1] lb1] work1]. cbn [it_ret fst snd] in R1. subst ret1.
    remember (cd_call2 (cd_S1 s (0, tbl1, next1, lb1, work1))) as q2 eqn:EQ2. destruct q2 as [[[[ret2 tbl2] next2] db2] work2]. cbn [it_ret fst snd] in R2. subst ret2.
    unfold cd_call1 in EQ1. unfold cd_call2, cd_S1 in EQ2. unfold cd_S2, cd_S1.
    cbn [it_tbl it_table it_bits it_work fst snd iset_work iset_lenbits iset_next iset_lencode iset_codes iset_distbits iset_distcode is_lens is_nlen is_ndist is_codes is_next is_work] in EQ2 |- *.
    pose (w := mkW s c r). change (mkW s c r) with w in PI. change s with (w_s w) in Hm, HV, E256, EQ1, EQ2 |- *. change c with (w_c w). change r with (w_r w) in R0 |- *.
    clearbody w. clear s c r.
    dworld w. cbn [w_s w_c w_r is_mode is_nlen is_ndist is_have is_lens ir_ret is_codes is_work is_next] in Hm, HV, E256, R0, EQ1, EQ2 |- *. pinv_open PI.
    subst f_mode. sinv_triage. destruct Qcodelens as (QN & QD & QH & QCT & QL15).
    wred. wred in EQ2.
    pose proof (inflate_table_lengths LENS f_lens 0 f_nlen f_codes 0 9 f_work) as LEN1. cbv zeta in LEN1. rewrite <- EQ1 in LEN1. cbn [fst snd] in LEN1.
    pose proof (tab_ok_of_shape LENS f_lens 0 f_nlen f_codes 0 9 f_work ltac:(clear - QN; lia)
                  ltac:(intros s Hs; rewrite Z.add_0_l; apply QL15; clear - Hs HV QD QN; lia)
                  ltac:(intros X; discriminate X) ltac:(intros X; discriminate X) ltac:(clear; lia) ltac:(clear; lia)
                  ltac:(cbn [it_room]; unfold ENOUGH_LENS; rewrite Acodes; clear; lia) ltac:(rewrite Awork; clear - QN; lia)) as TS1.
    rewrite <- EQ1 in TS1. cbn [fst snd] in TS1.
    pose proof (ARRB_table LENS f_lens 0 f_nlen f_codes 0 9 f_work Sarrb Acodes Awork) as AR1. rewrite <- EQ1 in AR1. cbn [fst snd] in AR1.
    pose proof (rep_ok_of_shape LENS f_lens 0 f_nlen f_codes 0 9 f_work ltac:(clear - QN; lia)
                  ltac:(intros s Hs; rewrite Z.add_0_l; apply QL15; clear - Hs HV QD QN; lia)
                  ltac:(intros X; discriminate X) ltac:(intros X; discriminate X) ltac:(clear; lia) ltac:(clear; lia)
                  ltac:(cbn [it_room]; unfold ENOUGH_LENS; rewrite Acodes; clear; lia) ltac:(rewrite Awork; clear - QN; lia)) as RS1.
    rewrite <- EQ1 in RS1. cbn [fst snd] in RS1. specialize (RS1 eq_refl).
    destruct LEN1 as [LT1 LW1]. destruct AR1 as (AR1 & _ & _ & _).
    destruct (TS1 eq_refl) as (TL1 & BL1 & NX1 & _ & OUT1). cbn [it_room] in NX1. unfold ENOUGH_LENS in NX1.
    pose proof (inflate_table_lengths DISTS f_lens f_nlen f_ndist tbl1 next1 6 work1) as LEN2. cbv zeta in LEN2. rewrite <- EQ2 in LEN2. cbn [fst snd] in LEN2.
    pose proof (tab_ok_of_shape DISTS f_lens f_nlen f_ndist tbl1 next1 6 work1 ltac:(clear - QD; lia)
                  ltac:(intros s Hs; apply QL15; clear - Hs HV QD QN; lia)
                  ltac:(intros X; discriminate X) ltac:(intros _; clear - QD; lia) ltac:(clear; lia) ltac:(clear - NX1 BL1; lia)
                  ltac:(cbn [it_room]; unfold ENOUGH_DISTS; rewrite LT1, Acodes; clear - NX1 BL1; lia) ltac:(rewrite LW1, Awork; clear - QD; lia)) as TS2.
    rewrite <- EQ2 in TS2. cbn [fst snd] in TS2.
    pose proof (ARRB_table DISTS f_lens f_nlen f_ndist tbl1 next1 6 work1 AR1 ltac:(rewrite LT1; exact Acodes) ltac:(rewrite LW1; exact Awork)) as AR2.
    rewrite <- EQ2 in AR2. cbn [fst snd] in AR2.
    pose proof (rep_ok_of_shape DISTS f_lens f_nlen f_ndist tbl1 next1 6 work1 ltac:(clear - QD; lia)
                  ltac:(intros s Hs; apply QL15; clear - Hs HV QD QN; lia)
                  ltac:(intros X; discriminate X) ltac:(intros _; clear - QD; lia) ltac:(clear; lia) ltac:(clear - NX1 BL1; lia)
                  ltac:(cbn [it_room]; unfold ENOUGH_DISTS; rewrite LT1, Acodes; clear - NX1 BL1; lia) ltac:(rewrite LW1, Awork; clear - QD; lia)) as RS2.
    rewrite <- EQ2 in RS2. cbn [fst snd] in RS2. specialize (RS2 eq_refl).
    destruct LEN2 as [LT2 LW2]. destruct AR2 as (AR2 & _ & _ & _).
    destruct (TS2 eq_refl) as (TD2 & BD2 & NX2 & _ & OUT2). cbn [it_room] in NX2. unfold ENOUGH_DISTS in NX2.
    assert (TL2 : tab_ok LENS (cat tbl2 (CDyn 0)) lb1 next1 = true).
    { apply (tab_ok_ext LENS (cat tbl1 (CDyn 0))). 2:{ replace next1 with (next1 - 0) by lia. exact TL1. }
      intros i Hi. cbn [cat]. Transparent cat. unfold cat. apply OUT2. lia. }
    assert (TOK : tables_okf (CDyn 0) (CDyn next1) lb1 db2 next2 tbl2 = true).
    { apply tables_okf_dyn_intro; [clear - NX1 NX2 BL1 BD2; lia | clear - NX1 NX2 BL1 BD2; lia | exact TL2 | exact TD2]. }
    assert (RL2 : rep_ok (cat tbl2 (CDyn 0)) lb1).
    { apply (rep_ok_ext LENS (cat tbl1 (CDyn 0)) _ lb1 (next1 - 0) TL1); [| exact RS1].
      intros i Hi. unfold cat. apply OUT2. lia. }
    assert (TREP : rep_ok (cat tbl2 (CDyn 0)) lb1 /\ rep_ok (cat tbl2 (CDyn next1)) db2) by (split; [exact RL2 | exact RS2]).
    pinv_auto. all: intros; first [exact TOK | exact TREP].
  Qed.
