(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* inflate_state arrays at their 1.4 offsets (lens 168, work 808, codes 1384, sane 7160; 1.3.1: 152, 792, 1368, 7144) *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.AsanW Require Import AImg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState Inftrees ItableModel.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AArr U2AKit ItAKit ItAPure ItA_base.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_base | solve_load_sh0 | solve_load_image ].
Local Ltac acc_hint ::= acc_hint_sh.

Section CANSEC1. Context {rc : runConstT}.
Section P.
  Variables (RNG : footprint) (FR : bvmap 5 word) (fc : bv 32) (gp tp : word).
  Variables (SP SPA S F PB top : Z) (m1 : amem).
  Variables (ty : codetype) (lf wf cf : Z -> Z) (lo codes bits : Z).
  Hypothesis CX : itb_ctx RNG SP SPA S F PB top m1.
  Hypothesis Hcodes : 0 <= codes <= 288.
  Hypothesis Hbits : 1 <= bits <= 15.

  Notation LP := (S + 168 + 2 * lo).
  Notation ST := (bst SP SPA S F PB LP gp tp FR fc).
  Notation cntAr := (cntA lf lo codes).
  Notation cA := (arr_get (cntA lf lo codes)).
  Notation mx := (mxA lf lo codes).
  Notation mn := (mnA lf lo codes).
  Notation rt := (rootA lf lo codes bits).
  Notation L k := (LZ (cntA lf lo codes) k).
  Notation SHPB := (Z_to_bv 64 (Z.shiftr PB 3 + 2147450880)).

  Lemma cA_range2 : forall j, 0 <= cA j <= codes.
  Proof. intros j. rewrite cntA_eq. apply cntK_le; lia. Qed.
  Lemma cty_codes : (cty ty =? 0) = codetype_eqb ty CODES.
  Proof. destruct ty; reflexivity. Qed.

  Definition left_post (m : amem) (x1 x6 x7 x25 x28 x29 x30 x31 : word) : machine_state -> Prop :=
    fun ms' =>
      (exists (q5 q10 q11 q16 q17 : word),
         ms' = ST x1 q5 x6 x7 q10 q11 SHPB (Z_to_bv 64 rt) (Z_to_bv 64 mx) (Z_to_bv 64 mn) q16 q17 (Z_to_bv 64 (cty ty)) x25 x28 x29 x30 x31 0x95f48 m
         /\ itm_reject ty mx (it_left_check cntAr) = false)
      \/ (exists (q5 q11 q16 q17 : word),
            ms' = ST x1 q5 x6 x7 (Z_to_bv 64 (-1)) q11 SHPB (Z_to_bv 64 rt) (Z_to_bv 64 mx) (Z_to_bv 64 mn) q16 q17 (Z_to_bv 64 (cty ty)) x25 x28 x29 x30 x31 0x965f4 m
            /\ itm_reject ty mx (it_left_check cntAr) = true).

  Ltac left_neg k PP K :=
    apply evtF_done; unfold left_post; right; do 4 eexists; split; [reflexivity|];
    unfold itm_reject; rewrite (left_check_none cntAr k); [reflexivity | lia | intros; apply PP; lia | lia].
  Ltac left_pos k PP K :=
    let PP' := fresh "PP" in
    assert (PP' : forall j, 1 <= j <= k -> 0 <= L j)
      by (let j := fresh "j" in let Hj := fresh "Hj" in intros j Hj; destruct (Z.eq_dec j k) as [->|]; [lia | apply PP; lia]);
    clear PP; rename PP' into PP;
    let P := fresh "P" in assert (P : 0 <= L k < 65536) by lia.

  Lemma it_left : forall (m : amem)
      (v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 : word) (offs : Z -> Z) (next bitsw : word)
      (x1 x5 x6 x7 x10 x16 x17 x25 x28 x29 x30 x31 : word),
    1 <= mx ->
    itb_inv SPA S F PB m1 m v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 cA offs lf wf cf next bitsw ->
    evtF asegs RNG (left_post m x1 x6 x7 x25 x28 x29 x30 x31)
      (ST x1 x5 x6 x7 x10 (Z_to_bv 64 (if mx =? 1 then 1 else 0)) SHPB (Z_to_bv 64 rt) (Z_to_bv 64 mx) (Z_to_bv 64 mn)
          x16 x17 (Z_to_bv 64 (cty ty)) x25 x28 x29 x30 x31 0x95e44 m).
  Proof using All.
    intros until x31. intros Hmx INV. open_ctx CX. open_inv INV. unfold bst.
    pose proof (f16arr_to_cells asegs m (F + 32) 16 _ CNT) as CC.
    cbv [fws map seq Z.of_nat Pos.of_succ_nat Pos.succ] in CC.
    assert (HRa : forall j, 0 <= cA j <= codes) by apply cA_range2.
    assert (LB : forall j, 0 <= j <= 15 -> -18874368 <= L j <= 32768).
    { intros j Hj. pose proof (LZ_bound cntAr j codes ltac:(lia) HRa Hj). lia. }
    pose proof (HRa 1) as HR1. pose proof (HRa 15) as HR15.
    zs. rewrite (zx16_small (cA 1)) by lia. zs. zs. zs. zbr0 K1.
    { apply evtF_done. unfold left_post. right. do 4 eexists. split; [reflexivity|].
      unfold itm_reject. rewrite (left_check_none cntAr 1); [reflexivity | lia | intros; lia | rewrite LZ_1; lia]. }
    assert (PP1 : forall j, 1 <= j <= 1 -> 0 <= L j) by (intros j Hj; replace j with 1 by lia; rewrite LZ_1; lia).
    pose proof (LB 1 ltac:(lia)) as LB1. pose proof (LB 2 ltac:(lia)) as LB2. pose proof (HRa 2) as HR2.
    zs. rewrite (zx16_small (cA 2)) by lia. zs. zs. zs. zs.
    setreg 16 (Z_to_bv 64 (L 2)) ltac:(rewrite shl1_2x, zbv_sub_mod, (LZ_S' cntAr 2), LZ_1 by lia; f_equal; lia).
    zs. zbr0 K2. { left_neg 2 PP1 K2. }
    left_pos 2 PP1 K2.
    pose proof (LB 3 ltac:(lia)) as LB3. pose proof (HRa 3) as HR3.
    zs. rewrite (zx16_small (cA 3)) by lia. zs. zs.
    setreg 16 (Z_to_bv 64 (L 3)) ltac:(rewrite shl1_2x, zbv_sub_mod_l, (LZ_S' cntAr 3) by lia; f_equal; lia).
    zs. zbr0 K3. { left_neg 3 PP1 K3. }
    left_pos 3 PP1 K3.
    pose proof (LB 4 ltac:(lia)) as LB4. pose proof (HRa 4) as HR4.
    zs. rewrite (zx16_small (cA 4)) by lia. zs. zs.
    setreg 16 (Z_to_bv 64 (L 4)) ltac:(rewrite shl1_2x, zbv_sub_mod_l, (LZ_S' cntAr 4) by lia; f_equal; lia).
    zs. zbr0 K4. { left_neg 4 PP1 K4. }
    left_pos 4 PP1 K4.
    pose proof (LB 5 ltac:(lia)) as LB5. pose proof (HRa 5) as HR5.
    zs. rewrite (zx16_small (cA 5)) by lia. zs. zs.
    setreg 16 (Z_to_bv 64 (L 5)) ltac:(rewrite shl1_2x, zbv_sub_mod_l, (LZ_S' cntAr 5) by lia; f_equal; lia).
    zs. zbr0 K5. { left_neg 5 PP1 K5. }
    left_pos 5 PP1 K5.
    pose proof (LB 6 ltac:(lia)) as LB6. pose proof (HRa 6) as HR6.
    zs. rewrite (zx16_small (cA 6)) by lia. zs. zs.
    setreg 16 (Z_to_bv 64 (L 6)) ltac:(rewrite shl1_2x, zbv_sub_mod_l, (LZ_S' cntAr 6) by lia; f_equal; lia).
    zs. zbr0 K6. { left_neg 6 PP1 K6. }
    left_pos 6 PP1 K6.
    pose proof (LB 7 ltac:(lia)) as LB7. pose proof (HRa 7) as HR7.
    zs. rewrite (zx16_small (cA 7)) by lia. zs. zs.
    setreg 16 (Z_to_bv 64 (L 7)) ltac:(rewrite shl1_2x, zbv_sub_mod_l, (LZ_S' cntAr 7) by lia; f_equal; lia).
    zs. zbr0 K7. { left_neg 7 PP1 K7. }
    left_pos 7 PP1 K7.
    pose proof (LB 8 ltac:(lia)) as LB8. pose proof (HRa 8) as HR8.
    zs. rewrite (zx16_small (cA 8)) by lia. zs. zs.
    setreg 16 (Z_to_bv 64 (L 8)) ltac:(rewrite shl1_2x, zbv_sub_mod_l, (LZ_S' cntAr 8) by lia; f_equal; lia).
    zs. zbr0 K8. { left_neg 8 PP1 K8. }
    left_pos 8 PP1 K8.
    pose proof (LB 9 ltac:(lia)) as LB9. pose proof (HRa 9) as HR9.
    zs. rewrite (zx16_small (cA 9)) by lia. zs. zs.
    setreg 16 (Z_to_bv 64 (L 9)) ltac:(rewrite shl1_2x, (Z.mod_small (2 * L 8)) by lia; rewrite swrap32_small by lia; rewrite (LZ_S' cntAr 9) by lia; f_equal; lia).
    zs. zbr0 K9. { left_neg 9 PP1 K9. }
    left_pos 9 PP1 K9.
    pose proof (LB 10 ltac:(lia)) as LB10. pose proof (HRa 10) as HR10.
    zs. rewrite (zx16_small (cA 10)) by lia. zs. zs.
    setreg 16 (Z_to_bv 64 (L 10)) ltac:(rewrite shl1_2x, (Z.mod_small (2 * L 9)) by lia; rewrite swrap32_small by lia; rewrite (LZ_S' cntAr 10) by lia; f_equal; lia).
    zs. zbr0 K10. { left_neg 10 PP1 K10. }
    left_pos 10 PP1 K10.
    pose proof (LB 11 ltac:(lia)) as LB11. pose proof (HRa 11) as HR11.
    zs. rewrite (zx16_small (cA 11)) by lia. zs. zs.
    setreg 16 (Z_to_bv 64 (L 11)) ltac:(rewrite shl1_2x, (Z.mod_small (2 * L 10)) by lia; rewrite swrap32_small by lia; rewrite (LZ_S' cntAr 11) by lia; f_equal; lia).
    zs. zbr0 K11. { left_neg 11 PP1 K11. }
    left_pos 11 PP1 K11.
    pose proof (LB 12 ltac:(lia)) as LB12. pose proof (HRa 12) as HR12.
    zs. rewrite (zx16_small (cA 12)) by lia. zs. zs.
    setreg 16 (Z_to_bv 64 (L 12)) ltac:(rewrite shl1_2x, (Z.mod_small (2 * L 11)) by lia; rewrite swrap32_small by lia; rewrite (LZ_S' cntAr 12) by lia; f_equal; lia).
    zs. zbr0 K12. { left_neg 12 PP1 K12. }
    left_pos 12 PP1 K12.
    pose proof (LB 13 ltac:(lia)) as LB13. pose proof (HRa 13) as HR13.
    zs. rewrite (zx16_small (cA 13)) by lia. zs. zs.
    setreg 16 (Z_to_bv 64 (L 13)) ltac:(rewrite shl1_2x, (Z.mod_small (2 * L 12)) by lia; rewrite swrap32_small by lia; rewrite (LZ_S' cntAr 13) by lia; f_equal; lia).
    zs. zbr0 K13. { left_neg 13 PP1 K13. }
    left_pos 13 PP1 K13.
    pose proof (LB 14 ltac:(lia)) as LB14. pose proof (HRa 14) as HR14.
    zs. rewrite (zx16_small (cA 14)) by lia. zs. zs.
    setreg 16 (Z_to_bv 64 (L 14)) ltac:(rewrite shl1_2x, (Z.mod_small (2 * L 13)) by lia; rewrite swrap32_small by lia; rewrite (LZ_S' cntAr 14) by lia; f_equal; lia).
    zs. zbr0 K14. { left_neg 14 PP1 K14. }
    left_pos 14 PP1 K14.
    pose proof (LB 15 ltac:(lia)) as LB15.
    assert (E15 : L 15 = 2 * L 14 - cA 15) by (rewrite (LZ_S' cntAr 15) by lia; change (15 - 1) with 14; reflexivity).
    zs. rewrite (zx16_small (cA 15)) by lia. zs.
    setreg 16 (Z_to_bv 64 (2 * L 14)) ltac:(rewrite shl1_2x; rewrite swrap32_small by lia; reflexivity).
    zs. zbr0 K15. { left_neg 15 PP1 K15. }
    assert (PP15 : forall j, 1 <= j <= 15 -> 0 <= L j) by (intros j Hj; destruct (Z.eq_dec j 15) as [->|]; [lia | apply PP1; lia]).
    assert (HLC : it_left_check cntAr = Some (L 15)) by (apply left_check_some; exact PP15).
    zs. zbr0 KE.
    { apply evtF_done. unfold left_post. left. do 5 eexists. split; [reflexivity|].
      unfold itm_reject. rewrite HLC. replace (0 <? L 15) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
    assert (L15P : 0 < L 15) by lia.
    zs. zs.
    assert (EA : Z.land (Z.b2z (0 <? cty ty mod 18446744073709551616)) (if mx =? 1 then 1 else 0)
                 = Z.b2z (negb (codetype_eqb ty CODES || negb (mx =? 1)))) by (destruct ty; destruct (mx =? 1); reflexivity).
    rewrite EA. clear EA.
    destruct (codetype_eqb ty CODES || negb (mx =? 1)) eqn:RJ; cbn [negb Z.b2z].
    - zs. apply evtF_done. unfold left_post. right. do 4 eexists. split; [reflexivity|].
      unfold itm_reject. rewrite HLC, RJ. replace (0 <? L 15) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
    - zs. apply evtF_done. unfold left_post. left. do 5 eexists. split; [reflexivity|].
      unfold itm_reject. rewrite HLC, RJ. apply Bool.andb_false_r.
  Qed.
End P.
End CANSEC1.
