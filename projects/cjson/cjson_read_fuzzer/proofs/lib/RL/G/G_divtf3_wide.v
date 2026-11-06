(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SFModel.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_f128_mul.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_sf_helpers3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_scan_calls.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_fmt_fp_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_divtf3.
From Stdlib Require Zify.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require RProgAt.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require ProgAt3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require RegFold.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require JunkAbs.
Module G_divtf3_core.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_f128_mul.F_f128_mul_core1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_sf_helpers3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_f128_div_wide OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_f128_div_core1.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmt_fp_lib.G_multf3_core OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_divtf3.

(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.ProgAt3.Prog_divtf3.   Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.ProgAt3.ProgAt. 
(* [comment removed for export] *)

Import ListNotations.

(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.step2_with rp rpm vh ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2_with rp rpm vh.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep.step_ecall ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep_ecall.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.asolve_load.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.solve_cond ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.asolve_cond.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.step ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.stepz ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.stepz_fast ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2_fast.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep.sys_nret ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.asys_nret.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac.post_call segs m ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.apost_call segs m.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.simp_regs ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RegFold.simp_regs_f.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.find_t_eval k t ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.find_t_eval_at k t.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.JunkAbs.split_for_access_abs H segs m A cs kn n.
Section Img.
  Context {IMG : RImg}.
  Context {CODE_divtf3_core : CodeAtT img_segs (sym 0x1c6b0) (divtf3_prog_at IMG)}.
  Context {RB_divtf3_core : RelCode (sym 0x1c6b0) 2308}.
  Collection ImgHyps := IMG CODE_divtf3_core RB_divtf3_core.


Local Ltac Lia.lia ::= Zify.zify; xlia zchecker.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac flia ::= flia_fast.
Local Ltac unfold_sf_in H ::= unfold_sf_in_recast H.
Local Ltac blia ::= blia_fast.
(* [comment removed for export] *)
Local Ltac step ::= step_fast. Local Ltac stepz ::= stepz_fast.
Local Ltac zsimp ::= zsimp_fast.

Definition divtf3_core_pc := (sym 0x1c6b0 + 136)%Z.
Definition divtf3_mid1_pc := (sym 0x1c6b0 + 536)%Z.

(* [comment removed for export] *)
Lemma shl_shr_32 : forall x, 0 <= x -> Z.shiftr (Z.land (Z.shiftl x 32) 18446744073709551615) 32 = Z.land x 4294967295.
Proof. intros. rewrite zb_shl_shr_land by lia. reflexivity. Qed.

(* [comment removed for export] *)
Definition E_aSigHiI (aSigHi : Z) := Z.lor aSigHi 281474976710656.
Definition E_bSigHiI (bSigHi : Z) := Z.lor bSigHi 281474976710656.
Definition E_aLoTop (aLo : Z) := Z.shiftr aLo 63.
Definition E_a2Lo (aLo : Z) := Z.land (Z.shiftl aLo 1) 18446744073709551615.
Definition E_aHi2n (aSigHi : Z) := Z.land (Z.shiftl aSigHi 1) 18446744073709551615.
Definition E_aHi2 (aSigHi : Z) := Z.land (Z.shiftl (E_aSigHiI aSigHi) 1) 18446744073709551615.
Definition E_A1 (aSigHi : Z) := Z.shiftr (E_aHi2 aSigHi) 32.
Definition E_A2 (aSigHi aLo : Z) := Z.land (Z.lor (E_aLoTop aLo) (E_aHi2n aSigHi)) 4294967295.
Definition E_A2sh (aSigHi aLo : Z) := Z.shiftl (Z.lor (E_aLoTop aLo) (E_aHi2n aSigHi)) 32.
Definition E_A3 (aLo : Z) := Z.shiftr (E_a2Lo aLo) 32.
Definition E_A4 (aLo : Z) := Z.land (E_a2Lo aLo) 4294967294.
Definition E_X3 (x_lo : Z) := Z.shiftr x_lo 32.
Definition E_X4sh (x_lo : Z) := Z.land (Z.shiftl x_lo 32) 18446744073709551615.
Definition E_X4 (x_lo : Z) := Z.shiftr (E_X4sh x_lo) 32.
Definition E_p3 (x_lo A : Z) := Z.land (E_X3 x_lo * A) 18446744073709551615.
Definition E_p42 (x_lo aSigHi aLo : Z) := Z.land (E_X4 x_lo * E_A2 aSigHi aLo) 18446744073709551615.
Definition E_expM1 (scale ea eb : Z) := scale + 16382 + (ea - eb).
Definition E_blo (bLo : Z) := Z.land (Z.shiftl bLo 15) 18446744073709551615.
Definition E_bhw (bSigHi bLo : Z) := Z.lor (Z.shiftr bLo 49) (Z.land (Z.shiftl (E_bSigHiI bSigHi) 15) 18446744073709551615).
Definition E_x0 (bSigHi bLo : Z) := Z.land (8432131802713292800 - E_bhw bSigHi bLo) 18446744073709551615.

(* [comment removed for export] *)
Definition DCW (sgn ea eb aSigHi aLo bSigHi bLo scale x_hi x_lo : Z) : Z :=
  let '(q_hi, q_lo) := divc_wide x_hi x_lo (E_A1 aSigHi) (E_A2 aSigHi aLo) (E_A3 aLo) (E_A4 aLo) in
  divc_tail sgn (E_expM1 scale ea eb) q_hi q_lo aLo (E_aSigHiI aSigHi) (E_bSigHiI bSigHi) bLo (E_aHi2 aSigHi) (E_aLoTop aLo) (E_a2Lo aLo).

(* [comment removed for export] *)
Ltac half_block b_hw xp xn h corr lo hi r :=
  zstep; model_reg 22 h (Z.shiftr (xp * b_hw) 64); mulhu_rng h;
  zstep; model_reg 22 corr (Z.land (0 - h) 18446744073709551615);
  zstep; model_reg 23 lo (Z.land (corr * xp) 18446744073709551615);
  zstep; model_reg 21 hi (Z.shiftr (corr * xp) 64); mulhu_rng hi;
  do 3 zstep; model_reg 21 r (Z.lor (Z.shiftr lo 63) (Z.land (Z.shiftl hi 1) 18446744073709551615));
  replace (Z_to_bv 64 r) with (Z_to_bv 64 (half_iter xp b_hw)) by (f_equal; subst r hi lo corr h; reflexivity);
  name_as xn (half_iter xp b_hw); hi_rng xn.

(* [comment removed for export] *)
Definition divtf3_mid1 (ra sp gp tp w4 sgw w6 a5 a6 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (ea eb aSigHi bSigHi scale : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists x_hi x_lo y21 y22,
    (forall sgn, div_core sgn ea eb aSigHi (bv_unsigned w4) bSigHi (bv_unsigned w6) scale
                 = DCW sgn ea eb aSigHi (bv_unsigned w4) bSigHi (bv_unsigned w6) scale x_hi x_lo)
    /\ (0 <= x_hi < 2^64)%Z /\ (0 <= x_lo < 2^64)%Z
    /\ ms' = MS (mkR ra sp gp tp (Z_to_bv 64 (E_expM1 scale ea eb)) (Z_to_bv 64 (E_aLoTop (bv_unsigned w4))) (Z_to_bv 64 (E_aHi2 aSigHi))
                 (Z_to_bv 64 (E_A1 aSigHi)) (Z_to_bv 64 (E_A2sh aSigHi (bv_unsigned w4)))
                 w4 sgw w6 (Z_to_bv 64 (E_bSigHiI bSigHi)) (Z_to_bv 64 (E_a2Lo (bv_unsigned w4))) a5 a6 (Z_to_bv 64 (E_aSigHiI aSigHi))
                 (Z_to_bv 64 (E_A2 aSigHi (bv_unsigned w4))) (Z_to_bv 64 (E_p42 x_lo aSigHi (bv_unsigned w4))) (Z_to_bv 64 (E_X4 x_lo)) y21 y22
                 (Z_to_bv 64 (E_p3 x_lo (E_A3 (bv_unsigned w4)))) (Z_to_bv 64 (E_p3 x_lo (E_A4 (bv_unsigned w4)))) (Z_to_bv 64 x_hi) s10 s11
                 (Z_to_bv 64 (E_A4 (bv_unsigned w4))) (Z_to_bv 64 (E_p3 x_lo (E_A1 aSigHi))) (Z_to_bv 64 (E_p3 x_lo (E_A2 aSigHi (bv_unsigned w4)))) (Z_to_bv 64 (E_A3 (bv_unsigned w4))))
             F (Z_to_bv 64 (sym 0x1c6b0 + 536)) fc None m (seg_rom img_segs).

Section Core1.
  Variables (w3 w4 w5 w6 : word) (ea eb scale : Z).
  Notation aSigHi := (bv_unsigned w3). Notation aLo := (bv_unsigned w4).
  Notation bSigHi := (bv_unsigned w5). Notation bLo := (bv_unsigned w6).

  Lemma divtf3_core1 : forall (ra sp gp tp s0 s1 sgw a3 a4 a5 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 : word)
      (F : bvmap 5 word) fc (m : word -> option byte),
    mem_inv img_segs m ->
    (0 <= ea < 32768)%Z -> (0 <= eb < 32768)%Z -> (-1024 <= scale <= 1024)%Z ->
    evt img_segs (divtf3_mid1 ra sp gp tp w4 sgw w6 a5 a6 s10 s11 F fc ea eb aSigHi bSigHi scale m)
      (MS (mkR ra sp gp tp w5 (Z_to_bv 64 ea) (Z_to_bv 64 eb) s0 s1 w4 sgw w6 a3 a4 a5 a6 w3
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 scale) t4 t5 t6)
          F (Z_to_bv 64 (sym 0x1c6b0 + 136)) fc None m (seg_rom img_segs)).
  Proof.
    intros until m. intros MI Ra Rb Rsc.
    pose_word_ranges.
    set (aExp := ea) in *. set (bExp := eb) in *.
    (* [comment removed for export] *)
    do 3 zstep. model_reg 7 expDiff (aExp - bExp).
    do 1 zstep. model_reg 30 blo (Z.land (Z.shiftl bLo 15) 18446744073709551615).
    do 4 zstep. model_reg 6 aLoTop (Z.shiftr aLo 63).
    do 1 zstep. model_reg 14 a2Lo (Z.land (Z.shiftl aLo 1) 18446744073709551615).
    do 1 zstep. model_reg 18 aHi2n (Z.land (Z.shiftl aSigHi 1) 18446744073709551615).
    do 7 zstep. model_reg 31 A3 (Z.shiftr a2Lo 32).
    do 2 zstep. model_reg 17 aSigHiI (Z.lor aSigHi 281474976710656).
    do 1 zstep. model_reg 13 bSigHiI (Z.lor bSigHi 281474976710656).
    do 5 zstep. model_reg 5 expM1 ((scale + 16382) + expDiff).
    do 2 zstep. model_reg 7 aHi2 (Z.land (Z.shiftl aSigHiI 1) 18446744073709551615).
    do 1 zstep. model_reg 18 A2 (Z.land (Z.lor aLoTop aHi2n) 4294967295).
    do 1 zstep. model_reg 28 A4 (Z.land a2Lo 4294967294).
    do 1 zstep. model_reg 20 b_hw (Z.lor (Z.shiftr bLo 49) (Z.land (Z.shiftl bSigHiI 15) 18446744073709551615)).
    do 1 zstep. model_reg 8 A1 (Z.shiftr aHi2 32).
    do 1 zstep. model_reg 21 x0 (Z.land (8432131802713292800 - b_hw) 18446744073709551615).
    (* [comment removed for export] *)
    half_block b_hw x0 hx1 h1 k1 lo1 hi1 r1.
    half_block b_hw hx1 hx2 h2 k2 lo2 hi2 r2.
    half_block b_hw hx2 hx3 h3 k3 lo3 hi3 r3.
    half_block b_hw hx3 hx4 h4 k4 lo4 hi4 r4.
    do 1 zstep. model_reg 21 xh (Z.land (hx4 - 1) 18446744073709551615).
    do 1 zstep. model_reg 22 pHhi (Z.shiftr (b_hw * xh) 64). mulhu_rng pHhi.
    do 1 zstep. model_reg 20 pHlo (Z.land (b_hw * xh) 18446744073709551615).
    do 1 zstep. model_reg 30 pLhi (Z.shiftr (blo * xh) 64). mulhu_rng pLhi.
    do 1 zstep. model_reg 30 sumlo (Z.land (pHlo + pLhi) 18446744073709551615).
    do 1 zstep. model_reg 20 c0 (Z.b2z (sumlo <? pHlo)).
    do 1 zstep. model_reg 23 lt2 (Z.b2z (sumlo <? 2)).
    do 1 zstep. model_reg 29 lo_corr (Z.land (1 - sumlo) 18446744073709551615).
    do 1 zstep. model_reg 20 hiP (Z.land (pHhi + c0) 18446744073709551615).
    do 1 zstep. model_reg 30 ge2 (Z.lxor lt2 1).
    do 1 zstep. model_reg 22 m1lo (Z.land (lo_corr * xh) 18446744073709551615).
    do 1 zstep. model_reg 29 m1hi (Z.shiftr (lo_corr * xh) 64). mulhu_rng m1hi.
    do 1 zstep. model_reg 30 negHi (Z.land (hiP + ge2) 18446744073709551615).
    do 3 zstep. model_reg 29 Bhi (Z.shiftr m1hi 63).
    do 1 zstep. model_reg 30 hi_corr (Z.land (0 - negHi) 18446744073709551615).
    do 1 zstep. model_reg 20 Blo (Z.lor (Z.shiftr m1lo 63) (Z.land (Z.shiftl m1hi 1) 18446744073709551615)).
    do 1 zstep. model_reg 22 m2lo (Z.land (xh * hi_corr) 18446744073709551615).
    do 1 zstep. model_reg 30 m2hi (Z.shiftr (xh * hi_corr) 64). mulhu_rng m2hi.
    do 3 zstep. model_reg 22 Alo (Z.land (Z.shiftl m2lo 1) 18446744073709551615).
    do 1 zstep. model_reg 30 Ahi (Z.lor (Z.land (Z.shiftl m2hi 1) 18446744073709551615) (Z.shiftr m2lo 63)).
    do 1 zstep. model_reg 20 sLo (Z.land (Alo + Blo) 18446744073709551615).
    do 1 zstep. model_reg 29 sHi (Z.land (Ahi + Bhi) 18446744073709551615).
    do 1 zstep. model_reg 30 cs1 (Z.b2z (sLo <? Alo)).
    do 1 zstep. model_reg 19 x_lo (Z.land (sLo + 18446744073709537689) 18446744073709551615).
    do 1 zstep. model_reg 29 sHi1 (Z.land (sHi + cs1) 18446744073709551615).
    do 1 zstep. model_reg 30 cs2 (Z.b2z (x_lo <? sLo)).
    do 1 zstep. model_reg 20 X3 (Z.shiftr x_lo 32).
    do 1 zstep. model_reg 19 X4sh (Z.land (Z.shiftl x_lo 32) 18446744073709551615).
    do 1 zstep. model_reg 21 sHi2 (Z.land (sHi1 + cs2) 18446744073709551615).
    do 1 zstep. model_reg 29 p31 (Z.land (X3 * A1) 18446744073709551615).
    do 1 zstep. model_reg 30 p32 (Z.land (X3 * A2) 18446744073709551615).
    do 1 zstep. model_reg 23 p33 (Z.land (X3 * A3) 18446744073709551615).
    do 1 zstep. model_reg 24 p34 (Z.land (X3 * A4) 18446744073709551615).
    do 1 zstep. model_reg 20 X4 (Z.shiftr X4sh 32).
    do 1 zstep. cbv delta [X4sh]. rewrite mulhu_shl32 by zrange_nonneg. replace (Z.land x_lo 4294967295) with X4 by (cbv delta [X4 X4sh]; apply shl_shr_32; zrange_nonneg). change (Z.land (Z.lor aLoTop aHi2n) 4294967295) with A2. change (Z.land (Z.shiftl x_lo 32) 18446744073709551615) with X4sh.
    do 0 zstep. model_reg 19 p42 (Z.land (X4 * A2) 18446744073709551615).
    do 1 zstep. model_reg 25 x_hi (Z.land (sHi2 - 1) 18446744073709551615).
    (* [comment removed for export] *)
    apply evt_done. unfold divtf3_mid1.
    exists x_hi, x_lo. eexists. eexists.
    split.
    { intros sg. cbv beta delta [DCW].
      change (E_A1 aSigHi) with A1. change (E_A2 aSigHi aLo) with A2. change (E_A3 aLo) with A3. change (E_A4 aLo) with A4.
      change (E_expM1 scale aExp bExp) with expM1. change (E_aSigHiI aSigHi) with aSigHiI. change (E_bSigHiI bSigHi) with bSigHiI.
      change (E_aHi2 aSigHi) with aHi2. change (E_aLoTop aLo) with aLoTop. change (E_a2Lo aLo) with a2Lo.
      cbv beta delta [div_core].
      change (divc_setup aExp bExp aSigHi aLo bSigHi bLo scale) with (expM1, blo, b_hw, A1, A2, A3, A4, aSigHiI, bSigHiI, aHi2, aLoTop, a2Lo, x0).
      cbv beta iota.
      assert (HN : divc_newton x0 b_hw = xh).
      { cbv delta [divc_newton]. sf_vocab. fold_model_lets. folded_check. reflexivity. }
      rewrite HN. cbv beta iota zeta.
      assert (HF : divc_full xh b_hw blo = (x_hi, x_lo)).
      { cbv delta [divc_full]. sf_vocab. fold_model_lets. folded_check. reflexivity. }
      rewrite HF. cbv beta iota. reflexivity. }
    split. { exact Rx_hi. } split. { exact Rx_lo. }
    (* [comment removed for export] *)
    change (E_A3 aLo) with A3; change (E_A4 aLo) with A4; change (E_A1 aSigHi) with A1; change (E_A2 aSigHi aLo) with A2;
    change (E_p3 x_lo A3) with p33; change (E_p3 x_lo A4) with p34; change (E_p3 x_lo A1) with p31; change (E_p3 x_lo A2) with p32;
    change (E_p42 x_lo aSigHi aLo) with p42; change (E_X4 x_lo) with X4; change (E_expM1 scale aExp bExp) with expM1;
    change (E_aLoTop aLo) with aLoTop; change (E_aHi2 aSigHi) with aHi2; change (E_A2sh aSigHi aLo) with (Z.shiftl (Z.lor aLoTop aHi2n) 32);
    change (E_bSigHiI bSigHi) with bSigHiI; change (E_a2Lo aLo) with a2Lo; change (E_aSigHiI aSigHi) with aSigHiI.
    reflexivity.
  Time Qed.
End Core1.

End Img.
(* [comment removed for export] *)
Ltac half_block b_hw xp xn h corr lo hi r :=
  zstep; model_reg 22 h (Z.shiftr (xp * b_hw) 64); mulhu_rng h;
  zstep; model_reg 22 corr (Z.land (0 - h) 18446744073709551615);
  zstep; model_reg 23 lo (Z.land (corr * xp) 18446744073709551615);
  zstep; model_reg 21 hi (Z.shiftr (corr * xp) 64); mulhu_rng hi;
  do 3 zstep; model_reg 21 r (Z.lor (Z.shiftr lo 63) (Z.land (Z.shiftl hi 1) 18446744073709551615));
  replace (Z_to_bv 64 r) with (Z_to_bv 64 (half_iter xp b_hw)) by (f_equal; subst r hi lo corr h; reflexivity);
  name_as xn (half_iter xp b_hw); hi_rng xn.
End G_divtf3_core.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import SFModel.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_f128_mul.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_f128_mul.F_f128_mul_core1.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import F_sf_helpers3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_scan_calls.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_f128_div_wide.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_scan_calls.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_f128_div_core1.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_fmt_fp_lib.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmt_fp_lib.G_multf3_core.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require Import G_divtf3.
Import G_divtf3_core.

(* [comment removed for export] *)
From Stdlib Require Import Zify Lia.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require RProgAt.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require ProgAt3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.ProgAt3.Prog_divtf3. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require RegFold. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require RProgAt. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require ProgAt3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.ProgAt3.ProgAt. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require JunkAbs.
(* [comment removed for export] *)

Import ListNotations.

(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.step2_with rp rpm vh ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2_with rp rpm vh.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep.step_ecall ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep_ecall.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.asolve_load.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.solve_cond ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.asolve_cond.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.step ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.stepz ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.stepz_fast ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2_fast.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep.sys_nret ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.asys_nret.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac.post_call segs m ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.apost_call segs m.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.simp_regs ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RegFold.simp_regs_f.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.find_t_eval k t ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.find_t_eval_at k t.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.JunkAbs.split_for_access_abs H segs m A cs kn n.
Section Img.
  Context {IMG : RImg}.
  Context {CODE_divtf3_wide : CodeAtT img_segs (sym 0x1c6b0) (divtf3_prog_at IMG)}.
  Context {RB_divtf3_wide : RelCode (sym 0x1c6b0) 2308}.
  Collection ImgHyps := IMG CODE_divtf3_wide RB_divtf3_wide.


Local Ltac Lia.lia ::= Zify.zify; xlia zchecker.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac flia ::= flia_fast.
Local Ltac unfold_sf_in H ::= unfold_sf_in_recast H.
Local Ltac blia ::= blia_fast.
(* [comment removed for export] *)
Local Ltac step ::= step_fast. Local Ltac stepz ::= stepz_fast.
Local Ltac zsimp ::= zsimp_fast.

Definition divtf3_mid2_pc := (sym 0x1c6b0 + 856)%Z.

Lemma ltb1_eqb0 : forall x, 0 <= x -> (x <? 1) = (x =? 0).
Proof. intros. destruct (Z.ltb_spec0 x 1); destruct (Z.eqb_spec x 0); try reflexivity; lia. Qed.

(* [comment removed for export] *)
Definition divtf3_mid2 (sp gp tp w4 sgw w6 a6 : word) (F : bvmap 5 word) (fc : bv 32)
    (ea eb aSigHi bSigHi scale x_hi x_lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists q_hi q_lo y1 y8 y9 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y31,
    divc_wide x_hi x_lo (E_A1 aSigHi) (E_A2 aSigHi (bv_unsigned w4)) (E_A3 (bv_unsigned w4)) (E_A4 (bv_unsigned w4)) = (q_hi, q_lo)
    /\ (0 <= q_hi < 2^64)%Z /\ (0 <= q_lo < 2^64)%Z
    /\ ms' = MS (mkR y1 sp gp tp (Z_to_bv 64 (E_expM1 scale ea eb)) (Z_to_bv 64 (E_aLoTop (bv_unsigned w4))) (Z_to_bv 64 (E_aHi2 aSigHi))
                 y8 y9 w4 sgw w6 (Z_to_bv 64 (E_bSigHiI bSigHi)) (Z_to_bv 64 (E_a2Lo (bv_unsigned w4))) (Z_to_bv 64 (Z.shiftr q_hi 49)) a6 (Z_to_bv 64 (E_aSigHiI aSigHi))
                 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27
                 (Z_to_bv 64 q_hi) (Z_to_bv 64 (E_expM1 scale ea eb + 1)) (Z_to_bv 64 q_lo) y31)
             F (Z_to_bv 64 (sym 0x1c6b0 + 856)) fc None m (seg_rom img_segs).

Section Core2.
  Variables (w3 w4 w5 w6 : word) (ea eb scale : Z).
  Notation aSigHi := (bv_unsigned w3). Notation aLo := (bv_unsigned w4).
  Notation bSigHi := (bv_unsigned w5). Notation bLo := (bv_unsigned w6).

  Lemma divtf3_core2 : forall (x_hi x_lo : Z) (ra sp gp tp sgw a5 a6 y21 y22 s10 s11 : word)
      (F : bvmap 5 word) fc (m : word -> option byte),
    mem_inv img_segs m ->
    (0 <= ea < 32768)%Z -> (0 <= eb < 32768)%Z -> (-1024 <= scale <= 1024)%Z ->
    (0 <= x_hi < 2^64)%Z -> (0 <= x_lo < 2^64)%Z ->
    evt img_segs (divtf3_mid2 sp gp tp w4 sgw w6 a6 F fc ea eb aSigHi bSigHi scale x_hi x_lo m)
      (MS (mkR ra sp gp tp (Z_to_bv 64 (E_expM1 scale ea eb)) (Z_to_bv 64 (E_aLoTop (bv_unsigned w4))) (Z_to_bv 64 (E_aHi2 aSigHi))
                 (Z_to_bv 64 (E_A1 aSigHi)) (Z_to_bv 64 (E_A2sh aSigHi (bv_unsigned w4)))
                 w4 sgw w6 (Z_to_bv 64 (E_bSigHiI bSigHi)) (Z_to_bv 64 (E_a2Lo (bv_unsigned w4))) a5 a6 (Z_to_bv 64 (E_aSigHiI aSigHi))
                 (Z_to_bv 64 (E_A2 aSigHi (bv_unsigned w4))) (Z_to_bv 64 (E_p42 x_lo aSigHi (bv_unsigned w4))) (Z_to_bv 64 (E_X4 x_lo)) y21 y22
                 (Z_to_bv 64 (E_p3 x_lo (E_A3 (bv_unsigned w4)))) (Z_to_bv 64 (E_p3 x_lo (E_A4 (bv_unsigned w4)))) (Z_to_bv 64 x_hi) s10 s11
                 (Z_to_bv 64 (E_A4 (bv_unsigned w4))) (Z_to_bv 64 (E_p3 x_lo (E_A1 aSigHi))) (Z_to_bv 64 (E_p3 x_lo (E_A2 aSigHi (bv_unsigned w4)))) (Z_to_bv 64 (E_A3 (bv_unsigned w4))))
          F (Z_to_bv 64 (sym 0x1c6b0 + 536)) fc None m (seg_rom img_segs)).
  Proof.
    intros until m. intros MI Ra Rb Rsc Rx_hi Rx_lo.
    pose_word_ranges.
    (* [comment removed for export] *)
    cbv beta delta [E_p3 E_p42 E_X4 E_X4sh E_X3 E_A2sh E_A1 E_A2 E_A3 E_A4 E_aLoTop E_aHi2n E_aHi2 E_aSigHiI E_bSigHiI E_a2Lo E_expM1].
    name_as aSigHiI (Z.lor aSigHi 281474976710656). name_as bSigHiI (Z.lor bSigHi 281474976710656).
    name_as aLoTop (Z.shiftr aLo 63). name_as a2Lo (Z.land (Z.shiftl aLo 1) 18446744073709551615).
    name_as aHi2n (Z.land (Z.shiftl aSigHi 1) 18446744073709551615). name_as aHi2 (Z.land (Z.shiftl aSigHiI 1) 18446744073709551615).
    name_as A1 (Z.shiftr aHi2 32). name_as A2 (Z.land (Z.lor aLoTop aHi2n) 4294967295).
    name_as A3 (Z.shiftr a2Lo 32). name_as A4 (Z.land a2Lo 4294967294).
    name_as X3 (Z.shiftr x_lo 32). name_as X4sh (Z.land (Z.shiftl x_lo 32) 18446744073709551615). name_as X4 (Z.shiftr X4sh 32).
    name_as p31 (Z.land (X3 * A1) 18446744073709551615). name_as p32 (Z.land (X3 * A2) 18446744073709551615).
    name_as p33 (Z.land (X3 * A3) 18446744073709551615). name_as p34 (Z.land (X3 * A4) 18446744073709551615).
    name_as p42 (Z.land (X4 * A2) 18446744073709551615).
    (* [comment removed for export] *)
    do 1 zstep. model_reg 22 p41 (Z.land (X4 * A1) 18446744073709551615).
    do 1 zstep. model_reg 26 p43 (Z.land (X4 * A3) 18446744073709551615).
    do 1 zstep. model_reg 27 p44 (Z.land (X4 * A4) 18446744073709551615).
    do 1 zstep. model_reg 21 s2a (Z.land (p42 + p33) 18446744073709551615).
    do 1 zstep. model_reg 23 X1 (Z.shiftr x_hi 32).
    do 1 zstep. model_reg 25 X2sh (Z.land (Z.shiftl x_hi 32) 18446744073709551615).
    do 1 zstep. model_reg 26 sum1 (Z.land (p34 + p43) 18446744073709551615).
    do 1 zstep. model_reg 19 c2a (Z.b2z (s2a <? p42)).
    do 1 zstep. model_reg 20 p11 (Z.land (X1 * A1) 18446744073709551615).
    do 1 zstep. model_reg 18 p12 (Z.land (A2 * X1) 18446744073709551615).
    do 1 zstep. model_reg 1 p13 (Z.land (A3 * X1) 18446744073709551615).
    do 1 zstep. model_reg 23 p14 (Z.land (A4 * X1) 18446744073709551615).
    do 1 zstep. model_reg 15 X2 (Z.shiftr X2sh 32).
    do 1 zstep. cbv delta [X2sh]. rewrite mulhu_shl32 by zrange_nonneg. replace (Z.land x_hi 4294967295) with X2 by (cbv delta [X2 X2sh]; apply shl_shr_32; zrange_nonneg). change (Z.land (Z.lor aLoTop aHi2n) 4294967295) with A2. change (Z.land (Z.shiftl x_hi 32) 18446744073709551615) with X2sh.
    do 0 zstep. model_reg 9 p22 (Z.land (X2 * A2) 18446744073709551615).
    do 1 zstep. model_reg 24 c1 (Z.b2z (sum1 <? p34)).
    do 1 zstep. model_reg 25 sum1Shr32 (Z.shiftr sum1 32).
    do 1 zstep. model_reg 26 sum1Shl32 (Z.land (Z.shiftl sum1 32) 18446744073709551615).
    do 1 zstep. model_reg 8 p21 (Z.land (X2 * A1) 18446744073709551615).
    do 1 zstep. model_reg 31 p23 (Z.land (X2 * A3) 18446744073709551615).
    do 1 zstep. model_reg 15 p24 (Z.land (X2 * A4) 18446744073709551615).
    do 1 zstep. model_reg 23 s3a (Z.land (p41 + p14) 18446744073709551615).
    do 1 zstep. model_reg 24 c1Shl32 (Z.land (Z.shiftl c1 32) 18446744073709551615).
    do 1 zstep. model_reg 27 lo_lo (Z.land (sum1Shl32 + p44) 18446744073709551615).
    do 1 zstep. model_reg 1 s4a (Z.land (p31 + p13) 18446744073709551615).
    do 1 zstep. model_reg 15 sum2 (Z.land (s2a + p24) 18446744073709551615).
    do 1 zstep. model_reg 28 c3a (Z.b2z (s3a <? p41)).
    do 1 zstep. model_reg 30 s3b (Z.land (s3a + p32) 18446744073709551615).
    do 1 zstep. model_reg 18 sum5 (Z.land (p21 + p12) 18446744073709551615).
    do 1 zstep. model_reg 22 r0c (Z.b2z (lo_lo <? sum1Shl32)).
    do 1 zstep. model_reg 24 sum1Mid (Z.lor sum1Shr32 c1Shl32).
    do 1 zstep. model_reg 29 c4a (Z.b2z (s4a <? p31)).
    do 1 zstep. model_reg 9 sum4 (Z.land (s4a + p22) 18446744073709551615).
    do 1 zstep. model_reg 21 c2b (Z.b2z (sum2 <? s2a)).
    do 1 zstep. model_reg 23 c3b (Z.b2z (s3b <? s3a)).
    do 1 zstep. model_reg 31 sum3 (Z.land (s3b + p23) 18446744073709551615).
    do 1 zstep. model_reg 8 c5 (Z.b2z (sum5 <? p21)).
    do 1 zstep. model_reg 24 r1a (Z.land (sum2 + sum1Mid) 18446744073709551615).
    do 1 zstep. model_reg 22 nr0c (Z.lxor r0c 18446744073709551615).
    do 1 zstep. model_reg 25 sum5Shr32 (Z.shiftr sum5 32).
    do 1 zstep. model_reg 18 sum5Shl32 (Z.land (Z.shiftl sum5 32) 18446744073709551615).
    do 1 zstep. model_reg 26 c4b (Z.b2z (sum4 <? s4a)).
    do 1 zstep. model_reg 29 hh1 (Z.land (c4a + p11) 18446744073709551615).
    do 1 zstep. model_reg 19 sum2Hi (Z.land (c2a + c2b) 18446744073709551615).
    do 1 zstep. model_reg 28 c3ab (Z.land (c3a + c3b) 18446744073709551615).
    do 1 zstep. model_reg 30 c3c (Z.b2z (sum3 <? s3b)).
    do 1 zstep. model_reg 15 cr1a (Z.b2z (r1a <? sum2)).
    do 1 zstep. model_reg 20 sum3Shr32 (Z.shiftr sum3 32).
    do 1 zstep. model_reg 31 sum3Shl32 (Z.land (Z.shiftl sum3 32) 18446744073709551615).
    do 1 zstep. model_reg 8 c5Shl32 (Z.land (Z.shiftl c5 32) 18446744073709551615).
    do 1 zstep. model_reg 29 hh2 (Z.land (hh1 + c4b) 18446744073709551615).
    do 1 zstep. model_reg 18 m1 (Z.land (sum4 + sum5Shl32) 18446744073709551615).
    do 1 zstep. model_reg 28 sum3Hi (Z.land (c3ab + c3c) 18446744073709551615).
    do 1 zstep. model_reg 31 r1 (Z.land (r1a + sum3Shl32) 18446744073709551615).
    do 1 zstep. model_reg 30 sum5MidHi (Z.lor c5Shl32 sum5Shr32).
    do 1 zstep. model_reg 8 cm1 (Z.b2z (m1 <? sum4)).
    do 1 zstep. model_reg 19 m2 (Z.land (m1 + sum2Hi) 18446744073709551615).
    do 1 zstep. model_reg 28 sum3HiShl32 (Z.land (Z.shiftl sum3Hi 32) 18446744073709551615).
    do 1 zstep. model_reg 9 cr1b (Z.b2z (r1 <? r1a)).
    do 1 zstep. model_reg 21 ltc (Z.b2z (nr0c <? r1)).
    do 1 zstep. model_reg 31 eqx (Z.lxor r1 nr0c).
    do 1 zstep. model_reg 29 hh3 (Z.land (hh2 + sum5MidHi) 18446744073709551615).
    do 1 zstep. model_reg 30 cm2 (Z.b2z (m2 <? m1)).
    do 1 zstep. model_reg 15 r1Hi (Z.land (cr1a + cr1b) 18446744073709551615).
    do 2 zstep. model_reg 28 sum3Mid (Z.lor sum3Shr32 sum3HiShl32).
    do 1 zstep. model_reg 29 hh4 (Z.land (hh3 + cm1) 18446744073709551615).
    zstep.
    replace (Z_to_bv 64 (Z.b2z (eqx <? 1) + -1)) with (Z_to_bv 64 (Z.land (Z.b2z (eqx =? 0) - 1) 18446744073709551615))
      by (rewrite Z_to_bv_land64, ltb1_eqb0 by lia; f_equal; lia).
    model_reg 31 neMask (Z.land (Z.b2z (eqx =? 0) - 1) 18446744073709551615).
    zstep. model_reg 29 hh5 (Z.land (hh4 + cm2) 18446744073709551615).
    do 1 zstep. model_reg 28 m3 (Z.land (m2 + sum3Mid) 18446744073709551615).
    zstep. model_reg 30 carry (Z.land neMask ltc).
    zstep. model_reg 31 cm3 (Z.b2z (m3 <? m2)).
    do 1 zstep. model_reg 15 m4 (Z.land (m3 + r1Hi) 18446744073709551615).
    do 1 zstep. model_reg 29 hh6 (Z.land (hh5 + cm3) 18446744073709551615).
    do 1 zstep. model_reg 28 cm4 (Z.b2z (m4 <? m3)).
    zstep. model_reg 30 q_lo (Z.land (m4 + carry) 18446744073709551615).
    zstep. model_reg 28 hh7 (Z.land (hh6 + cm4) 18446744073709551615).
    zstep. model_reg 15 cm5 (Z.b2z (q_lo <? m4)).
    zstep. model_reg 28 q_hi (Z.land (hh7 + cm5) 18446744073709551615).
    do 2 zstep.
    apply evt_done. unfold divtf3_mid2.
    exists q_hi, q_lo. repeat (lazymatch goal with |- ex _ => eexists end).
    split.
    { change (divc_wide x_hi x_lo A1 A2 A3 A4 = (q_hi, q_lo)).
      cbv beta delta [divc_wide]. sf_vocab. fold_model_lets. folded_check. reflexivity. }
    split. { exact Rq_hi. } split. { exact Rq_lo. }
    reflexivity.
  Time Qed.

  (* [comment removed for export] *)
  Definition divtf3_midC (sp gp tp sgw a6 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists q_hi q_lo y1 y8 y9 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y31,
      (forall sgn, div_core sgn ea eb aSigHi aLo bSigHi bLo scale
                   = divc_tail sgn (E_expM1 scale ea eb) q_hi q_lo aLo (E_aSigHiI aSigHi) (E_bSigHiI bSigHi) bLo (E_aHi2 aSigHi) (E_aLoTop aLo) (E_a2Lo aLo))
      /\ (0 <= q_hi < 2^64)%Z /\ (0 <= q_lo < 2^64)%Z
      /\ ms' = MS (mkR y1 sp gp tp (Z_to_bv 64 (E_expM1 scale ea eb)) (Z_to_bv 64 (E_aLoTop aLo)) (Z_to_bv 64 (E_aHi2 aSigHi))
                   y8 y9 w4 sgw w6 (Z_to_bv 64 (E_bSigHiI bSigHi)) (Z_to_bv 64 (E_a2Lo aLo)) (Z_to_bv 64 (Z.shiftr q_hi 49)) a6 (Z_to_bv 64 (E_aSigHiI aSigHi))
                   y18 y19 y20 y21 y22 y23 y24 y25 y26 y27
                   (Z_to_bv 64 q_hi) (Z_to_bv 64 (E_expM1 scale ea eb + 1)) (Z_to_bv 64 q_lo) y31)
               F (Z_to_bv 64 (sym 0x1c6b0 + 856)) fc None m (seg_rom img_segs).

  Lemma divtf3_core12 : forall (ra sp gp tp s0 s1 sgw a3 a4 a5 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 : word)
      (F : bvmap 5 word) fc (m : word -> option byte),
    mem_inv img_segs m ->
    (0 <= ea < 32768)%Z -> (0 <= eb < 32768)%Z -> (-1024 <= scale <= 1024)%Z ->
    evt img_segs (divtf3_midC sp gp tp sgw a6 F fc m)
      (MS (mkR ra sp gp tp w5 (Z_to_bv 64 ea) (Z_to_bv 64 eb) s0 s1 w4 sgw w6 a3 a4 a5 a6 w3
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 scale) t4 t5 t6)
          F (Z_to_bv 64 (sym 0x1c6b0 + 136)) fc None m (seg_rom img_segs)).
  Proof.
    intros until m. intros MI Ra Rb Rsc.
    eapply evt_cut. { eapply divtf3_core1; eauto. }
    intros ms1 P. (nelim P 8%nat; intros xh' xl' y21 y22 EQ1 Rxh Rxl ->).
    eapply evt_mono. { eapply divtf3_core2; eauto. }
    intros ms2 P2. (nelim P2 20%nat; intros q_hi q_lo y1 y8 y9 y18 y19 y20 z21 z22 y23 y24 y25 y26 y27 y31 HW Rqh Rql ->).
    unfold divtf3_midC. exists q_hi, q_lo. repeat (lazymatch goal with |- ex _ => eexists end).
    split. { intros sgn. rewrite EQ1. cbv beta delta [DCW]. rewrite HW. reflexivity. }
    split. { exact Rqh. } split. { exact Rql. }
    reflexivity.
  Qed.
End Core2.

End Img.
