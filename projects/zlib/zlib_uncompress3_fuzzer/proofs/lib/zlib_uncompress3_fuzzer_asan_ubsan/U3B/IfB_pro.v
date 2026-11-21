(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.Lib Require Import Arr Bytes ZBridge Tac InitMem StoreFast.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.BothW Require Import BImg RtCells ABase ABytes.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.U2A Require Import U2AShadow U2AArr U2AKit U2ABlob ItAKit IfAPure.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.U2A Require Import U2AObj.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.U3B Require Import U2BObj IfB_base.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.U2A Require Import UbFit2.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.U3B Require Import IfBTac.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.Common Require Import StrFun RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_sh0 | solve_load_shlit | solve_load_base | solve_load_image ].
Local Ltac acc_hint ::= acc_hint_sh.

Section CANSEC1. Context {rc : runConstT}.
Section S.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32).
  Variables (lo : Z) (RNG : footprint).
  Notation SP := (bv_unsigned sp).
  Variables (Zs S : Z).
  Hypothesis LOS : lo <= SP - 272.
  Hypothesis LOC : KHIGH <= lo.
  Hypothesis SPT : SP + 16 < KEND.
  Hypothesis RSTK : rng RNG lo (SP - lo).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis Z8 : Zs mod 8 = 0.
  Hypothesis S16 : S mod 16 = 0.
  Hypothesis ZL : 0 < Zs /\ Zs + 112 <= lo.
  Hypothesis SL : 0 < S /\ S + 7176 <= lo.
  Hypothesis RZ : rng RNG Zs 112.
  Hypothesis RSZ : rng RNG (Z.shiftr Zs 3 + 2147450880) 14.
  Hypothesis RS : rng RNG S 7176.
  Hypothesis RSS : rng RNG (Z.shiftr S 3 + 2147450880) 897.

  Definition if_SAVED : list cell :=
    [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Lemma if_pro : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m
      (D OB n osz ci co start hold bits whave wnext Wd wsz lb db la da bo : Z)
      (zti zto zmsg zalloc zfree zopq zdt zadl zres zp1 zp2 zp3 : word)
      (strm mode last wrap havedict flags dmax check total head wbits length_ offset extra ncode nlen ndist have next : word),
    let scells := strm_cells (Z_to_bv 64 (D + ci)) (Z_to_bv 64 (n - ci)) zti (Z_to_bv 64 (OB + co)) (Z_to_bv 64 (osz - co))
                             zto zmsg (Z_to_bv 64 S) zalloc zfree zopq zdt zadl zres zp1 zp2 zp3 in
    let icells := istate_cells strm mode last wrap havedict flags dmax check total head wbits
                               (Z_to_bv 64 wsz) (Z_to_bv 64 whave) (Z_to_bv 64 wnext) (Z_to_bv 64 Wd)
                               (Z_to_bv 64 hold) (Z_to_bv 64 bits) length_ offset extra (Z_to_bv 64 la) (Z_to_bv 64 da)
                               (Z_to_bv 64 lb) (Z_to_bv 64 db) ncode nlen ndist have next in
    stk bsegs m lo SP -> mem_inv bsegs m ->
    rt_got m -> rt_shbase m ->
    rw_cells bsegs m Zs scells -> rw_cells bsegs m S icells ->
    shadow_bytes m (Z.shiftr Zs 3 + 2147450880) (Z.shiftr Zs 3 + 2147450880 + 14) (fun _ => 0) ->
    shadow_bytes m (Z.shiftr S 3 + 2147450880) (Z.shiftr S 3 + 2147450880 + 897) (fun _ => 0) ->
    6 <= n - ci -> n < 67108864 -> 0 <= ci -> 258 <= osz - co -> osz <= 262144 -> 0 <= co ->
    osz - co <= start <= osz -> bo = co - (start - (osz - co)) ->
    0 <= bits <= 40 -> 0 <= hold < 2 ^ bits ->
    0 <= whave <= 32768 -> 0 <= wnext <= 32768 -> 0 <= wsz <= 32768 -> 1 <= lb <= 15 -> 1 <= db <= 15 ->
    1 <= D -> D + n <= lo -> 0 < OB -> OB + osz <= lo -> 0 < la < 2 ^ 47 -> 0 < da < 2 ^ 47 -> 0 <= Wd < 2 ^ 47 ->
    evtF bsegs RNG (fun ms' => exists m1 (x6 x7 x10 x11 x14 x15 x24 x28 x29 x30 : word),
        ms' = fms SP Zs S D n OB osz la da gp tp FR fc x6 x7 x10 x11 x14 x15 x24 x28 x29 x30 ci co hold bits 0x981a8 m1
        /\ munch [(SP - 272, SP)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
        /\ stk bsegs m1 lo (SP + -272)
        /\ rw_cells bsegs m1 (SP + -104) if_SAVED
        /\ rw_cells bsegs m1 (SP + -272) (if_frm Zs S OB bo wsz whave wnext Wd lb db)
        /\ rw_cells bsegs m1 Zs scells /\ rw_cells bsegs m1 S icells)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Zs) (Z_to_bv 64 start) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 A_IFAST) fc None m (seg_rom bsegs)).
  Proof using All.
    intros until next. intros scells icells ST MI GOT SHB STRM SSC SHZ SHS NCI NR CI0 OCO OSZ CO0 START EBO BITS HOLD WH WN WS LB DB D0 DL O0 OL LA DA WD.
    subst scells icells. unfold A_IFAST, strm_cells, istate_cells, if_SAVED in *.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. unfold KEND in SPT. unfold KHIGH in LOC.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (pow2_40 bits BITS) as P40.
    pose (W := [(SP - 272, SP)]).
    assert (DJZ : disjoint_from W (Z.shiftr Zs 3 + 2147450880) (Z.shiftr Zs 3 + 2147450880 + 14 - (Z.shiftr Zs 3 + 2147450880))).
    { subst W. cbn [disjoint_from]. rewrite ?Z.shiftr_div_pow2 by lia. change (2^3) with 8. repeat split; try exact I; Z.div_mod_to_equations; lia. }
    assert (DJS : disjoint_from W (Z.shiftr S 3 + 2147450880) (Z.shiftr S 3 + 2147450880 + 897 - (Z.shiftr S 3 + 2147450880))).
    { subst W. cbn [disjoint_from]. rewrite ?Z.shiftr_div_pow2 by lia. change (2^3) with 8. repeat split; try exact I; Z.div_mod_to_equations; lia. }
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl bsegs m) as WM. subst W.
    zstep.
    carve_frame 104%nat ST. carve_frame 168%nat ST.
    do 13 zstep.
    lazymatch goal with H : rw_cells bsegs _ (SP + -272) [CB 168 ?j] |- _ =>
      apply (rw_cells_chop bsegs _ (SP + -272) 168 j (repeat SH8 21)) in H; [| reflexivity];
      cbn [chop chop1 shape_size repeat] in H; chop_names H end.
    zrunu [0x981a8].
    lazymatch goal with H : rw_cells bsegs _ (SP + -272) _ |- _ => rename H into FRM end.
    rewrite !mask_sllw by lia. rewrite !mask_sllw in FRM by lia.
    rewrite !(Z.mod_small _ 4294967296) by lia. rewrite !(Z.mod_small _ 4294967296) in FRM by lia.
    setreg 18 (Z_to_bv 64 (D + n - 5)) ltac:(f_equal; lia).
    setreg 16 (Z_to_bv 64 (OB + osz - 257)) ltac:(f_equal; lia).
    replace (OB + co - (start - (osz - co))) with (OB + bo) in FRM by lia.
    apply evtF_done. eexists. do 10 eexists. split; [unfold fms, gms, xms; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|].
    split; [eassumption|]. split; [unfold if_frm, if_locals; exact FRM|]. split; eassumption.
  Qed.

End S.
End CANSEC1.
