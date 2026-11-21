(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge Tac InitMem StoreFast.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.BothW Require Import BImg RtCells ABase ABytes.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState Inftrees InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AArr U2AKit ItAKit IfAPure IfAStore.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AObj.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U1B Require Import U2BObj IfBTac IfB_base IfBKit IfB_pro.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_base | solve_load_sh0 | solve_load_image ].
Local Ltac acc_hint ::= first [ acc_hint_sh | acc_hint_var ].

Lemma srliw3_small : forall b, 0 <= b < 2147483648 -> bv_swrap 32 (Z.shiftr (bv_wrap 32 b) 3) = b / 8.
Proof.
  intros b H. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32) with 4294967296. rewrite Z.mod_small by lia.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. apply swrap32_small. Z.div_mod_to_equations. lia.
Qed.

Lemma lxor_signflip : forall x, 0 <= x < 9223372036854775808 -> Z.lxor x 9223372036854775808 = x + 9223372036854775808.
Proof.
  intros x H. rewrite <- Z.add_nocarry_lxor; [reflexivity|].
  apply Z.bits_inj'. intros k Hk. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.eq_dec k 63) as [->|NE].
  - replace (Z.testbit x 63) with false; [reflexivity|]. symmetry.
    destruct (Z.eq_dec x 0) as [->|NZ]; [apply Z.bits_0|]. apply Z.bits_above_log2; [lia|]. apply Z.log2_lt_pow2; lia.
  - replace (Z.testbit 9223372036854775808 k) with false; [apply Bool.andb_false_r|]. symmetry.
    change 9223372036854775808 with (2 ^ 63). apply Z.pow2_bits_false. lia.
Qed.
Ltac flag_dec :=
  repeat match goal with
  | |- context [Z.b2z (?a <? ?b)] =>
      first [ replace (a <? b) with true by (symmetry; apply Z.ltb_lt; lia) | replace (a <? b) with false by (symmetry; apply Z.ltb_ge; lia) ];
      change (Z.b2z true) with 1; change (Z.b2z false) with 0
  end.

Ltac join_set okpc n1 n2 n3 nS vS :=
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS ?R ?F _ ?fc ?rv ?m ?ro) =>
      let p1 := eval vm_compute in (bv_key (Z_to_bv 5 n1)) in
      let p2 := eval vm_compute in (bv_key (Z_to_bv 5 n2)) in
      let p3 := eval vm_compute in (bv_key (Z_to_bv 5 n3)) in
      let pS := eval vm_compute in (bv_key (Z_to_bv 5 nS)) in
      let H := fresh "CONT" in
      enough (H : forall y1 y2 y3 : word, evtF segs RNG Q (MS (tset pS vS (tset p3 y3 (tset p2 y2 (tset p1 y1 R)))) F (Z_to_bv 64 okpc) fc rv m ro));
      [ | let y1 := fresh "y" in let y2 := fresh "y" in let y3 := fresh "y" in intros y1 y2 y3;
          let g := lazymatch goal with |- ?g => g end in
          let g' := eval cbv beta iota delta [tset mkR] in g in change g' ]
  end.
Ltac join_done n1 n2 n3 :=
  lazymatch goal with
  | CONT : forall y1 y2 y3 : word, evtF _ _ _ _ |- _ =>
      let v1 := reg_val n1 in let v2 := reg_val n2 in let v3 := reg_val n3 in exact (CONT v1 v2 v3)
  end.

Section CANSEC1. Context {rc : runConstT}.
Section P.
  Variables (RNG : footprint) (FR : bvmap 5 word) (fc : bv 32) (gp tp : word).
  Variables (ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word).
  Notation SP := (bv_unsigned sp).
  Variables (lo Zs S D n OB osz Wd wsz whave wnext lb db la na da nd bo : Z) (rdL rdD fw : Z -> Z) (payload : list Z) (m1 : amem).
  Variables (sd : sdc) (id : idc) (ni ai no ao hw bw : word).
  Hypothesis CX : if_ctx RNG SP lo Zs S D n OB osz Wd wsz whave wnext lb db la na da nd bo rdL rdD fw payload m1.
  Notation ST := (fms SP Zs S D n OB osz la da gp tp FR fc).
  Notation OST := (oms SP Zs S D n OB osz la da gp tp FR fc).
  Notation INVM m msg mode fo := (if_inv SP Zs S OB osz bo wsz whave wnext Wd la da lb db m1 m sd id ni ai no ao msg mode hw bw fo).

  Lemma if_latch : forall (m : amem) (x5 x7 x10 x11 x14 x15 x19 x24 x28 x29 x30 : word) (ci co hold bits : Z) (POST : machine_state -> Prop),
    0 <= ci <= n -> 0 <= co <= osz ->
    (ci + 6 <= n -> co + 258 <= osz ->
       evtF bsegs RNG POST (ST (Z_to_bv 64 (OB + co)) x7 x10 x11 x14 x15 x24 x28 x29 x30 ci co hold bits 0x97e1c m)) ->
    (forall y5 y19 : word, evtF bsegs RNG POST (OST y5 x7 x10 x11 x14 x15 y19 x24 x28 x29 x30 ci co hold bits 0x989f8 m)) ->
    evtF bsegs RNG POST (OST x5 x7 x10 x11 x14 x15 x19 x24 x28 x29 x30 ci co hold bits 0x97f98 m).
  Proof using CX.
    intros until POST. intros CI CO KH KE.
    open_fctx CX. unfold fms, gms, oms, xms in *.
    clear ZSD ZOD SOD WSZ WNX WIN TOKL TOKD SANE FWR WH WN DB LB D8 PAYB PAYR PAYN UNP DJD DJP RD RSD
          TLB TL4 TL0 TLN0 TLHI RTL TLR DJTL SHTL RSTL DJSTL TLS1 TLS2 TDB TD4 TD0 TDN0 TDHI RTD TDR DJTD SHTD RSTD DJSTD TDS1 TDS2
          SHZ DJZ SHS DJS RZ RSZ RS RSS SHO DJO ROB RSOB.
    zs. zs. zbr K.
    - apply KE.
    - zs. zs. zbr K2.
      + apply KH; lia.
      + zs. apply KE.
  Qed.

  Definition exit_post (ci co hold bits : Z) (mode : word) : machine_state -> Prop :=
    fun ms' => exists (m' : amem) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 msg' : word) (fo' : Z -> Z),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               FR (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ mem_inv bsegs m' /\ munch (ifW SP Zs S OB osz ++ [(SP - 104, SP)]) m1 m' /\ wmono bsegs m1 m' /\ stk bsegs m' lo SP
      /\ rw_cells bsegs m' Zs (if_sc S sd (Z_to_bv 64 (D + (ci - bits / 8))) (Z_to_bv 64 (n - (ci - bits / 8))) (Z_to_bv 64 (OB + co))
                                     (Z_to_bv 64 (osz - co)) msg')
      /\ rw_cells bsegs m' S (if_ic wsz whave wnext Wd la da lb db id mode (Z_to_bv 64 (hold mod 2 ^ (bits mod 8))) (Z_to_bv 64 (bits mod 8)))
      /\ f8arr bsegs m' OB (Z.to_nat osz) fo' /\ (forall i, 0 <= i < osz -> 0 <= fo' i < 256).

  Lemma if_exit : forall (m : amem) (msg mode : word) (fo : Z -> Z) (x5 x7 x10 x11 x14 x15 x19 x24 x28 x29 x30 : word) (ci co hold bits : Z),
    INVM m msg mode fo ->
    rw_cells bsegs m1 (SP + -104) (if_SAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) -> stk bsegs m1 lo (SP + -272) ->
    0 <= ci <= n -> 0 <= co <= osz -> 0 <= bits <= 40 -> bits <= 8 * ci -> 0 <= hold < 2 ^ bits ->
    evtF bsegs RNG (exit_post ci co hold bits mode) (OST x5 x7 x10 x11 x14 x15 x19 x24 x28 x29 x30 ci co hold bits 0x989f8 m).
  Proof using All.
    intros until bits. intros INV0 SAV1 STK1 CI CO BITS B8 HOLD.
    open_fctx CX. open_finv INV0. unfold oms, xms, exit_post.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    assert (SAVC : rw_cells bsegs m (SP + -104) (if_SAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
    { eapply rw_cells_transport; [exact SAV1| exact MU| exact WM|]. unfold if_SAVED. cbn [disjoint_from cells_size csize Nat.add]. repeat split; try exact I; lia. }
    assert (STKC : stk bsegs m lo (SP + -272)).
    { eapply stk_transport_disjoint; [exact STK1| exact MU| exact WM|]. cbn [disjoint_from]. repeat split; try exact I; lia. }
    unfold if_SAVED in SAVC.
    clear WSZ WNX WIN TOKL TOKD SANE FWR WH WN DB LB D8 PAYB PAYR PAYN UNP DJD DJP RD RSD SAV1 STK1
          TLB TL4 TL0 TLN0 TLHI RTL TLR DJTL SHTL RSTL DJSTL TLS1 TLS2 TDB TD4 TD0 TDN0 TDHI RTD TDR DJTD SHTD RSTD DJSTD TDS1 TDS2
          SHO DJO ROB RSOB.
    pose proof (pow2_40 bits BITS) as P40.
    zs. rewrite srliw3_small by lia.
    assert (Q8 : 0 <= bits / 8 <= ci /\ 0 <= bits mod 8 < 8 /\ bits = 8 * (bits / 8) + bits mod 8) by (Z.div_mod_to_equations; lia).
    remember (bits / 8) as q eqn:EQ. remember (bits mod 8) as r eqn:ER.
    zrunu [0x98a24].
    setreg 13 (Z_to_bv 64 (D + (ci - q))) ltac:(f_equal; lia).
    zs.
    zrunu [0x98a38]. zs.
    join_set 0x98a68 10 11 12 13 (Z_to_bv 64 (n - (ci - q))).
    { zs. zbr KA.
      -
        zs. zs. zs. rewrite lxor_signflip by lia. zs. zs. rewrite lxor_signflip by lia.
        destruct (Z_lt_le_dec (D + n - 5) (D + (ci - q))) as [DQ|DQ]; flag_dec; zs;
          (setreg 13 (Z_to_bv 64 (n - (ci - q))) ltac:(f_equal; lia)); join_done 10 11 12.
      - zs. zs. zs. if_cases KB; [| exfalso; zify_lts KB; lia].
        setreg 13 (Z_to_bv 64 (n - (ci - q))) ltac:(f_equal; lia).
        join_done 10 11 12. }
    zrunu [0x98a78]. zs.
    join_set 0x98aa8 11 12 14 10 (Z_to_bv 64 (osz - co)).
    { zs. zbr KO.
      - zs. zs. zs. rewrite lxor_signflip by lia. zs. zs. rewrite lxor_signflip by lia.
        destruct (Z_lt_le_dec (OB + osz - 257) (OB + co)) as [DQ|DQ]; flag_dec; zs;
          (setreg 10 (Z_to_bv 64 (osz - co)) ltac:(f_equal; lia)); join_done 11 12 14.
      - zs. zs. zs. if_cases KB; [| exfalso; zify_lts KB; lia].
        setreg 10 (Z_to_bv 64 (osz - co)) ltac:(f_equal; lia).
        join_done 11 12 14. }
    zrunu [0x98ab8]. zs.
    zrunu [0x98ad8]. rewrite land_7_mod by lia. rewrite <- ER.
    pose proof (pow2_15 r ltac:(lia)) as PR.
    zs. zs. zs. rewrite mask_sllw by lia. zs. rewrite ?(Z.mod_small (2 ^ r - 1)) by lia. rewrite land_mask_mod by lia.
    zs.
    zrunu [0x98af4]. zs.
    do 13 zs. zs. zs.
    lazymatch goal with H : rw_cells bsegs _ (SP + -272) _ |- _ => rename H into FRM2 end.
    lazymatch goal with H : rw_cells bsegs _ (SP + -104) _ |- _ => rename H into SAV2 end.
    lazymatch goal with H : stk bsegs _ lo (SP + -272) |- _ => rename H into STK2 end.
    eapply stk_release in FRM2; [| exact STK2| lia]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FRM2.
    change (Z.of_nat 168) with 168 in FRM2. replace (SP + -272 + 168) with (SP + -104) in FRM2 by lia.
    release_frame SAV2 FRM2 (bv_unsigned sp).
    rewrite ?Z_to_bv_bv_unsigned.
    apply evtF_done. subst q r. eexists. do 16 eexists. exists fo.
    split; [reflexivity|]. split; [eassumption|].
    split; [eapply munch_weaken; [| eassumption]; unfold ifW; intros a Ha; cbn [outside app] in *; tauto|].
    split; [eassumption|]. split; [exact FRM2|].
    split; [unfold if_sc, strm_cells; eassumption|]. split; [unfold if_ic, istate_cells; eassumption|].
    split; [eassumption| exact FOR].
  Qed.
End P.
End CANSEC1.
