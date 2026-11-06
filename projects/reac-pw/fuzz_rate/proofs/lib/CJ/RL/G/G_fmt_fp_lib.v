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
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib Require SFModel.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.P Require F_f128_mul.
From Stdlib Require Zify.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc Require RProgAt.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.G Require ProgAt3.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc Require RegFold.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc Require JunkAbs.
Module G_multf3_core.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.SFModel.
Import OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.P.F_f128_mul.F_f128_mul_core1.

(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.
Import OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.G.ProgAt3.Prog_multf3.   Import OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.G.ProgAt3.ProgAt. 
(* [comment removed for export] *)

Import ListNotations.

(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Step.step2_with rp rpm vh ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_with rp rpm vh.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.SysStep.step_ecall ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.astep_ecall.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Step.solve_load ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_load.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Step.solve_cond ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_cond.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Step.step ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Step.stepz ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Step.stepz_fast ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_fast.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.SysStep.sys_nret ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.asys_nret.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Tac.post_call segs m ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.apost_call segs m.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Step.simp_regs ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RegFold.simp_regs_f.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.find_t_eval k t ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.find_t_eval_at k t.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.JunkAbs.split_for_access_abs H segs m A cs kn n.
Section Img.
  Context {IMG : RImg}.
  Context {CODE_multf3_core : CodeAtT img_segs (sym 0x1b3d0) (multf3_prog_at IMG)}.
  Context {RB_multf3_core : RelCode (sym 0x1b3d0) 1792}.
  Collection ImgHyps := IMG CODE_multf3_core RB_multf3_core.


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

Definition multf3_entry := (sym 0x1b3d0)%Z.
Definition multf3_core_pc := (sym 0x1b3d0 + 128)%Z.
Definition multf3_mid_pc := (sym 0x1b3d0 + 524)%Z.

(* [comment removed for export] *)
Lemma mulhu_shl32 : forall x y, 0 <= x -> 0 <= y ->
  Z.shiftr (Z.land (Z.shiftl x 32) 18446744073709551615 * Z.land (Z.shiftl y 32) 18446744073709551615) 64
  = Z.land (Z.land x 4294967295 * Z.land y 4294967295) 18446744073709551615.
Proof.
  intros x y Hx Hy.
  rewrite !land_W64. change 4294967295 with (2^32 - 1). rewrite !zb_land_mask by lia.
  rewrite !Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change (2^64) with (2^32 * 2^32) at 1 2.
  rewrite !Zmult_mod_distr_r.
  pose proof (Z.mod_pos_bound x (2^32) ltac:(lia)). pose proof (Z.mod_pos_bound y (2^32) ltac:(lia)).
  replace (x mod 2^32 * 2^32 * (y mod 2^32 * 2^32)) with ((x mod 2^32 * (y mod 2^32)) * 2^64) by lia.
  rewrite Z.div_mul by lia. symmetry. apply Z.mod_small. nia.
Qed.

(* [comment removed for export] *)
Definition multf3_mid (ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (aExp bExp aSigHi aSigLo bSigHi bSigLo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists es hh hl lh ll y5' t1 t2' x8 x9 a5' a6' s2' s3' s4' s5' s6' s7' s8' t3 t4 t5 t6,
    (forall signHi scale, mul_core signHi aExp bExp aSigHi aSigLo bSigHi bSigLo scale = MC_tail signHi es hh hl lh ll scale)
    /\ (0 <= es < 65536)%Z /\ (0 <= hh < 2^64)%Z /\ (0 <= hl < 2^64)%Z /\ (0 <= lh < 2^64)%Z /\ (0 <= ll < 2^64)%Z /\
    y5' = Z_to_bv 64 es /\ a5' = Z_to_bv 64 18446744073709551615 /\ a6' = Z_to_bv 64 281474976710655 /\ t2' = Z_to_bv 64 (-16383) /\
    ms' = MS (mkR ra sp gp tp y5' t1 t2' x8 x9
                 a0 a1 (Z_to_bv 64 ll) (Z_to_bv 64 lh) (Z_to_bv 64 hh) a5' a6' (Z_to_bv 64 hl)
                 s2' s3' s4' s5' s6' s7' s8' s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 (sym 0x1b3d0 + 524)) fc None m (seg_rom img_segs).

Lemma multf3_core1 : forall (ra sp gp tp w1 w2 s0 s1 a0 a1 w4 a3 a4 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w3 t5 t6 : word) (ea eb : Z)
    (F : bvmap 5 word) fc (m : word -> option byte),
  mem_inv img_segs m ->
  (0 <= ea < 32768)%Z -> (0 <= eb < 32768)%Z ->
  evt img_segs (multf3_mid ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               ea eb (bv_unsigned w1) (bv_unsigned w3) (bv_unsigned w2) (bv_unsigned w4) m)
    (MS (mkR ra sp gp tp (Z_to_bv 64 eb) w1 w2 s0 s1 a0 a1 w4 a3 a4 (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 281474976710655) (Z_to_bv 64 ea)
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (Z.shiftr (bv_unsigned w1) 32)) w3 t5 t6)
        F (Z_to_bv 64 (sym 0x1b3d0 + 128)) fc None m (seg_rom img_segs)).
Proof.
  intros until m. intros MI He1 He2.
  pose_word_ranges.
  set (aExp := ea) in *. set (bExp := eb) in *.
  set (aSigHi := bv_unsigned w1) in *. set (aSigLo := bv_unsigned w3) in *. set (bSigHi := bv_unsigned w2) in *. set (bSigLo := bv_unsigned w4) in *.
  (* [comment removed for export] *)
  do 1 zstep. model_reg 13 bLo15 (Z.land (Z.shiftl bSigLo 15) 18446744073709551615).
  do 6 zstep. model_reg 12 A3 (Z.shiftr aSigLo 32).
  do 2 zstep. model_reg 5 expSum (Z.land (aExp + bExp) 18446744073709551615).
  do 2 zstep. model_reg 28 A1 (Z.lor (Z.shiftr aSigHi 32) 65536).
  do 3 zstep. model_reg 14 bHi15 (Z.lor (Z.shiftr bSigLo 49) (Z.land (Z.shiftl bSigHi 15) 18446744073709551615)).
  do 1 zstep. model_reg 8 B3 (Z.shiftr bLo15 32).
  do 2 zstep. model_reg 9 A2 (Z.land aSigHi 4294967295).
  do 1 zstep. model_reg 18 A4 (Z.land aSigLo 4294967295).
  do 2 zstep. model_reg 17 B1 (Z.lor (Z.shiftr (Z.land (Z.shiftl bSigHi 15) 18446744073709551615) 32) 2147483648).
  do 2 zstep. model_reg 30 p13 (Z.land (B3 * A1) 18446744073709551615).
  do 1 zstep. model_reg 31 B4 (Z.land bLo15 4294967295).
  do 1 zstep. model_reg 19 p23 (Z.land (B3 * A2) 18446744073709551615).
  do 1 zstep. rewrite mulhu_shl32 by zrange_nonneg. change (Z.land bLo15 4294967295) with B4. change (Z.land aSigHi 4294967295) with A2.
  model_reg 20 p24 (Z.land (B4 * A2) 18446744073709551615).
  do 1 zstep. model_reg 21 p33 (Z.land (B3 * A3) 18446744073709551615).
  do 1 zstep. model_reg 8 p43 (Z.land (B3 * A4) 18446744073709551615).
  do 1 zstep. rewrite mulhu_shl32 by zrange_nonneg. change (Z.land bLo15 4294967295) with B4. change (Z.land aSigLo 4294967295) with A4.
  model_reg 13 p44 (Z.land (B4 * A4) 18446744073709551615).
  do 1 zstep. model_reg 22 p11 (Z.land (B1 * A1) 18446744073709551615).
  do 1 zstep. model_reg 23 B2 (Z.land bHi15 4294967295).
  do 1 zstep. model_reg 24 p14 (Z.land (B4 * A1) 18446744073709551615).
  do 1 zstep. model_reg 9 p21 (Z.land (B1 * A2) 18446744073709551615).
  do 1 zstep. rewrite mulhu_shl32 by zrange_nonneg. change (Z.land bHi15 4294967295) with B2. change (Z.land aSigHi 4294967295) with A2.
  model_reg 6 p22 (Z.land (B2 * A2) 18446744073709551615).
  do 1 zstep. model_reg 18 p41 (Z.land (B1 * A4) 18446744073709551615).
  do 1 zstep. model_reg 17 p31 (Z.land (B1 * A3) 18446744073709551615).
  do 1 zstep. model_reg 31 p34 (Z.land (B4 * A3) 18446744073709551615).
  do 1 zstep. rewrite mulhu_shl32 by zrange_nonneg. change (Z.land bHi15 4294967295) with B2. change (Z.land aSigLo 4294967295) with A4.
  model_reg 14 p42 (Z.land (B2 * A4) 18446744073709551615).
  do 1 zstep. model_reg 21 s2a (Z.land (p24 + p33) 18446744073709551615).
  do 1 zstep. model_reg 28 p12 (Z.land (B2 * A1) 18446744073709551615).
  do 1 zstep. model_reg 12 p32 (Z.land (B2 * A3) 18446744073709551615).
  do 1 zstep. model_reg 8 sum1 (Z.land (p34 + p43) 18446744073709551615).
  do 1 zstep. model_reg 29 c2a (Z.b2z (s2a <? p24)).
  do 1 zstep. model_reg 14 sum2 (Z.land (s2a + p42) 18446744073709551615).
  do 1 zstep. model_reg 19 s3a (Z.land (p14 + p23) 18446744073709551615).
  do 1 zstep. model_reg 30 s4a (Z.land (p31 + p13) 18446744073709551615).
  do 1 zstep. model_reg 31 c1 (Z.b2z (sum1 <? p34)).
  do 1 zstep. model_reg 20 c2b (Z.b2z (sum2 <? s2a)).
  do 1 zstep. model_reg 21 c3a (Z.b2z (s3a <? p14)).
  do 1 zstep. model_reg 18 s3b (Z.land (s3a + p41) 18446744073709551615).
  do 1 zstep. model_reg 9 sum5 (Z.land (p12 + p21) 18446744073709551615).
  do 1 zstep. model_reg 23 sum1Shr32 (Z.shiftr sum1 32).
  do 1 zstep. model_reg 8 sum1Shl32 (Z.land (Z.shiftl sum1 32) 18446744073709551615).
  do 1 zstep. model_reg 17 c4a (Z.b2z (s4a <? p31)).
  do 1 zstep. model_reg 6 sum4 (Z.land (s4a + p22) 18446744073709551615).
  do 1 zstep. model_reg 29 sum2Hi (Z.land (c2a + c2b) 18446744073709551615).
  do 1 zstep. model_reg 19 c3b (Z.b2z (s3b <? s3a)).
  do 1 zstep. model_reg 20 sum3 (Z.land (s3b + p32) 18446744073709551615).
  do 1 zstep. model_reg 28 c5 (Z.b2z (sum5 <? p12)).
  do 1 zstep. model_reg 31 c1Shl32 (Z.land (Z.shiftl c1 32) 18446744073709551615).
  do 1 zstep. model_reg 12 lo_lo (Z.land (sum1Shl32 + p44) 18446744073709551615).
  do 1 zstep. model_reg 13 sum5Shr32 (Z.shiftr sum5 32).
  do 1 zstep. model_reg 9 sum5Shl32 (Z.land (Z.shiftl sum5 32) 18446744073709551615).
  do 1 zstep. model_reg 30 c4b (Z.b2z (sum4 <? s4a)).
  do 1 zstep. model_reg 17 hh1 (Z.land (c4a + p11) 18446744073709551615).
  do 1 zstep. model_reg 19 c3ab (Z.land (c3a + c3b) 18446744073709551615).
  do 1 zstep. model_reg 18 c3c (Z.b2z (sum3 <? s3b)).
  do 1 zstep. model_reg 8 r0c (Z.b2z (lo_lo <? sum1Shl32)).
  do 1 zstep. model_reg 31 sum1Mid (Z.lor sum1Shr32 c1Shl32).
  do 1 zstep. model_reg 21 sum3Shr32 (Z.shiftr sum3 32).
  do 1 zstep. model_reg 20 sum3Shl32 (Z.land (Z.shiftl sum3 32) 18446744073709551615).
  do 1 zstep. model_reg 28 c5Shl32 (Z.land (Z.shiftl c5 32) 18446744073709551615).
  do 1 zstep. model_reg 17 hh2 (Z.land (hh1 + c4b) 18446744073709551615).
  do 1 zstep. model_reg 29 m1 (Z.land (sum4 + sum2Hi) 18446744073709551615).
  do 1 zstep. model_reg 18 sum3Hi (Z.land (c3ab + c3c) 18446744073709551615).
  do 1 zstep. model_reg 31 r1a (Z.land (sum2 + sum1Mid) 18446744073709551615).
  do 1 zstep. model_reg 28 sum5MidHi (Z.lor c5Shl32 sum5Shr32).
  do 1 zstep. model_reg 13 cm1 (Z.b2z (m1 <? sum4)).
  do 1 zstep. model_reg 9 m2 (Z.land (m1 + sum5Shl32) 18446744073709551615).
  do 1 zstep. model_reg 14 cr1a (Z.b2z (r1a <? sum2)).
  do 1 zstep. model_reg 18 sum3HiShl32 (Z.land (Z.shiftl sum3Hi 32) 18446744073709551615).
  do 1 zstep. model_reg 20 r1 (Z.land (r1a + sum3Shl32) 18446744073709551615).
  do 1 zstep. model_reg 17 hh3 (Z.land (hh2 + cm1) 18446744073709551615).
  do 1 zstep. model_reg 6 cm2 (Z.b2z (m2 <? m1)).
  do 1 zstep. model_reg 29 cr1b (Z.b2z (r1 <? r1a)).
  do 1 zstep. model_reg 13 lo_hi (Z.land (r1 + r0c) 18446744073709551615).
  do 1 zstep. model_reg 30 sum3Mid (Z.lor sum3Shr32 sum3HiShl32).
  do 1 zstep. model_reg 17 hh4 (Z.land (hh3 + sum5MidHi) 18446744073709551615).
  do 1 zstep. model_reg 14 r1Hi (Z.land (cr1a + cr1b) 18446744073709551615).
  do 1 zstep. model_reg 28 carry (Z.b2z (lo_hi <? r1)).
  do 1 zstep. model_reg 17 hh5 (Z.land (hh4 + cm2) 18446744073709551615).
  do 1 zstep. model_reg 30 m3 (Z.land (m2 + sum3Mid) 18446744073709551615).
  do 1 zstep. model_reg 6 cm3 (Z.b2z (m3 <? m2)).
  do 1 zstep. model_reg 14 m4 (Z.land (m3 + r1Hi) 18446744073709551615).
  do 1 zstep. model_reg 6 hh6 (Z.land (hh5 + cm3) 18446744073709551615).
  do 1 zstep. model_reg 29 cm4 (Z.b2z (m4 <? m3)).
  do 1 zstep. model_reg 17 hi_lo (Z.land (m4 + carry) 18446744073709551615).
  do 1 zstep. model_reg 6 hh7 (Z.land (hh6 + cm4) 18446744073709551615).
  do 1 zstep. model_reg 14 cm5 (Z.b2z (hi_lo <? m4)).
  do 1 zstep. model_reg 14 hi_hi (Z.land (hh7 + cm5) 18446744073709551615).
  (* [comment removed for export] *)
  apply evt_done. unfold multf3_mid.
  exists expSum, hi_hi, hi_lo, lo_hi, lo_lo.
  repeat (lazymatch goal with |- ex _ => eexists end).
  split.
  { intros sg sc. cbv delta [mul_core]. sf_vocab. fold_model_lets. cbv delta [MC_tail]. sf_vocab. reflexivity. }
  split. { subst expSum aExp bExp. rewrite land_W64, Z.mod_small by lia. lia. }
  split. { exact Rhi_hi. } split. { exact Rhi_lo. } split. { exact Rlo_hi. } split. { exact Rlo_lo. }
  split. { reflexivity. } split. { reflexivity. } split. { reflexivity. } split. { reflexivity. }
  reflexivity.
Time Qed.

End Img.
End G_multf3_core.

(* [comment removed for export] *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib Require StoreCache.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib Require NElim.
Module G_multf3_tail.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.SFModel.
Import OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.P.F_f128_mul.F_f128_mul_core1 OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.P.F_f128_mul.
Import G_multf3_core.

(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.
Import OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.G.ProgAt3.Prog_multf3. Import OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.StoreCache.StoreFast OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.StoreCache. Import OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.NElim.   Import OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.G.ProgAt3.ProgAt. 
(* [comment removed for export] *)

Import ListNotations.

(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Step.step2_with rp rpm vh ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_with rp rpm vh.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.SysStep.step_ecall ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.astep_ecall.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Step.solve_load ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_load.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Step.solve_cond ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_cond.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Step.step ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Step.stepz ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Step.stepz_fast ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_fast.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.SysStep.sys_nret ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.asys_nret.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Tac.post_call segs m ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.apost_call segs m. (* [comment removed for export] *) Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs. Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs. Local Ltac mem_after_store ::= mem_after_store_fast. Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM. Local Ltac mem_after_store ::= mem_after_store_cached. Local Ltac addr_eq_tac ::= addr_eq_tac_cached. Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM. Local Ltac disjoint_goal ::= cbn [disjoint_from fst snd]; simpl_sizes_goal; disjoint_split.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Step.simp_regs ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RegFold.simp_regs_f.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.find_t_eval k t ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.find_t_eval_at k t.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.JunkAbs.split_for_access_abs H segs m A cs kn n.
Section Img.
  Context {IMG : RImg}.
  Context {CODE_multf3_tail : CodeAtT img_segs (sym 0x1b3d0) (multf3_prog_at IMG)}.
  Context {RB_multf3_tail : RelCode (sym 0x1b3d0) 1792}.
  Collection ImgHyps := IMG CODE_multf3_tail RB_multf3_tail.


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

(* [comment removed for export] *)
Definition multf3_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (R : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 R)) (Z_to_bv 64 (hi64 R)) a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom img_segs)
    /\ munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m' /\ wmono img_segs m m' /\ mem_inv img_segs m'
    /\ stk img_segs m' (bv_unsigned sp - 80) (bv_unsigned sp).

Definition saved9 (s8 s7 s6 s5 s4 s3 s2 s1 s0 : word) (j : list byte) : list cell :=
  [CB 8 j; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0].

(* [comment removed for export] *)
Lemma land_M32_small : forall x, 0 <= x < 4294967296 -> Z.land x 4294967295 = x.
Proof. intros. rewrite landM32_mod. apply Z.mod_small. lia. Qed.
Lemma land_ones_r : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551615 = x.
Proof. intros. rewrite land_W64. apply Z.mod_small. lia. Qed.
Lemma land_ones_l : forall x, 0 <= x < 2^64 -> Z.land 18446744073709551615 x = x.
Proof. intros. rewrite Z.land_comm. apply land_ones_r. assumption. Qed.
(* [comment removed for export] *)
Lemma sra63_neg : forall x, -2^63 <= x < 0 -> Z.shiftr (bv_signed (Z_to_bv 64 x)) 63 = -1.
Proof.
  intros x Hx. rewrite Z_to_bv_signed, bv_swrap_small.
  2:{ unfold bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 64 `div` 2) with (2^63). lia. }
  rewrite Z.shiftr_div_pow2 by lia. Z.div_mod_to_equations. lia.
Qed.
Lemma sra63_negw : forall x, 2^63 <= x < 2^64 -> Z.shiftr (bv_signed (Z_to_bv 64 x)) 63 = -1.
Proof.
  intros x Hx. replace (Z_to_bv 64 x) with (Z_to_bv 64 (x - 2^64)) by (apply Z_to_bv_eqm; Z.div_mod_to_equations; lia).
  apply sra63_neg. lia.
Qed.
Lemma sra63_pos : forall x, 0 <= x < 2^63 -> Z.shiftr (bv_signed (Z_to_bv 64 x)) 63 = 0.
Proof.
  intros x Hx. rewrite Z_to_bv_signed, bv_swrap_small.
  2:{ unfold bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 64 `div` 2) with (2^63). lia. }
  rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. lia.
Qed.
Lemma lxor_b2z_1 : forall b, Z.lxor (Z.b2z b) 1 = Z.b2z (negb b).
Proof. intros [|]; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac zzr := zsimp;
  try (lazymatch goal with |- context [(_ + 0)%Z] => rewrite ?Z.add_0_r end);
  try (lazymatch goal with |- context [Z.land (_ - Z.land _ 18446744073709551615) 18446744073709551615] => rewrite !land_sub_neg by alia end);
  try (lazymatch goal with |- context [Z.land _ 4294967295] => rewrite !land_M32_small by alia end);
  try (lazymatch goal with |- context [Z.shiftr (bv_signed (Z_to_bv 64 _)) 63] => rewrite !sra63_neg by alia end);
  try (lazymatch goal with |- context [Z.shiftr (bv_signed (Z_to_bv 64 _)) 63] => rewrite !sra63_pos by alia end);
  try (lazymatch goal with |- context [Z.land 18446744073709551615 _] => rewrite !land_ones_l by (first [zrange | alia]) end);
  try (lazymatch goal with |- context [Z.land 0 _] => rewrite ?Z.land_0_l end).
Ltac zrstep := step; zzr.

(* [comment removed for export] *)
Lemma mfr_normal : forall s pe hh hl lh ll,
  0 < pe <= 131072 -> 0 <= hl < 2^64 ->
  mul_finish s pe hh hl lh ll =
  mul_round s (Z.lor (Z.land (pe ≪ 48) 18446744073709551615) (Z.land hh 281474976710655)) (Z.land hl 18446744073709551615) lh ll.
Proof.
  intros * Hpe Hhl. rewrite (land_ones_r hl) by lia. apply mf_normal. lia.
Qed.

Lemma mfr_caseA : forall s pe hh hl lh ll,
  -126 <= pe < -63 -> 0 <= hh < 2^64 -> 0 <= hl < 2^64 -> 0 <= lh < 2^64 -> 0 <= ll < 2^64 ->
  mul_finish s pe hh hl lh ll =
  mul_round s 0 (hh ≫ Z.land (1 - pe) 63)
    (Z.lor (Z.lor (Z.land (hh ≪ Z.land (pe + 127) 63) 18446744073709551615)
                  (Z.land ((hl ≫ 1) ≫ Z.land (Z.lxor (pe + 127) 18446744073709551615) 63) 18446744073709551615)) 0)
    (Z.lor (Z.lor (Z.land (hl ≪ Z.land (pe + 127) 63) 18446744073709551615) (Z.land (lh ≫ Z.land (1 - pe) 63) 18446744073709551615))
           (Z.b2z (0 <? Z.lor (Z.land (ll ≪ Z.land (pe + 127) 63) 18446744073709551615)
                               (Z.lor (Z.land (lh ≪ Z.land (pe + 127) 63) 18446744073709551615)
                                      (Z.land ((ll ≫ 1) ≫ Z.land (Z.lxor (pe + 127) 18446744073709551615) 63) 18446744073709551615))))).
Proof. intros * Hpe Hhh Hhl Hlh Hll. mf_pure. Qed.

Lemma mfr_caseB : forall s pe hh hl lh ll,
  pe = -63 -> 0 <= hh < 2^64 -> 0 <= hl < 2^64 -> 0 <= lh < 2^64 -> 0 <= ll < 2^64 ->
  mul_finish s pe hh hl lh ll =
  mul_round s 0 (hh ≫ Z.land (1 - pe) 63)
    (Z.lor (Z.land (hl ≪ Z.land (pe + 127) 63) 18446744073709551615) 0)
    (Z.lor (Z.lor 0 (Z.land (lh ≫ Z.land (1 - pe) 63) 18446744073709551615))
           (Z.b2z (0 <? Z.lor 0 (Z.land (ll ≪ Z.land (pe + 127) 63) 18446744073709551615)))).
Proof. intros * Hpe Hhh Hhl Hlh Hll. mf_pure. Qed.

Lemma mfr_caseC : forall s pe hh hl lh ll,
  -63 < pe <= 0 -> 0 <= hh < 2^64 -> 0 <= hl < 2^64 -> 0 <= lh < 2^64 -> 0 <= ll < 2^64 ->
  mul_finish s pe hh hl lh ll =
  mul_round s (Z.land (hh ≫ Z.land (1 - pe) 63) 18446744073709551615)
    (Z.lor (Z.land (hl ≫ Z.land (1 - pe) 63) 18446744073709551615)
           (Z.land (Z.land (hh ≪ 1) 18446744073709551615 ≪ Z.land (Z.lxor (1 - pe) 18446744073709551615) 63) 18446744073709551615))
    (Z.lor (Z.land (hl ≪ Z.land (pe + 127) 63) 18446744073709551615) (Z.land (lh ≫ Z.land (1 - pe) 63) 18446744073709551615))
    (Z.lor (Z.lor 0 (Z.lor (Z.land (ll ≫ Z.land (1 - pe) 63) 18446744073709551615)
                           (Z.land (Z.land (lh ≪ 1) 18446744073709551615 ≪ Z.land (Z.lxor (1 - pe) 18446744073709551615) 63) 18446744073709551615)))
           (Z.b2z (0 <? Z.lor 0 (Z.land (ll ≪ Z.land (pe + 127) 63) 18446744073709551615)))).
Proof. intros * Hpe Hhh Hhl Hlh Hll. mf_pure. Qed.

Section Walk.
  Variables (sp : word).
  Notation spw := (Z_to_bv 64 (bv_unsigned sp + -80)).

  Ltac hyp :=
    match goal with
    | H : mem_inv _ ?m |- mem_inv _ ?m => exact H
    | H : munch ?W ?m ?m' |- munch ?W ?m ?m' => exact H
    | H : wmono _ ?m ?m' |- wmono _ ?m ?m' => exact H
    | H : stk _ ?m ?lo ?hi |- stk _ ?m ?lo ?hi => exact H
    | H : rw_cells _ ?m ?A _ |- rw_cells _ ?m ?A _ => exact H
    | H : (?a <= ?b)%Z |- (?a <= ?b)%Z => exact H
    | H : bv_unsigned ?w = _ |- bv_unsigned ?w = _ => exact H
    | H : ?x = ?y |- ?x = ?y => exact H
    | H : ?x <> ?y |- ?x <> ?y => exact H
    | |- (0 <= _ < _)%Z => zrange2
    end.
  Ltac join L := eapply L; try hyp.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac model_in H := sf_model_in H.

  Ltac eblia := rewrite ?Z.shiftl_mul_pow2 in * by lia; blia.
  Ltac decide_in_cond H c :=
    match c with
    | context [Z.eqb ?x ?y] =>
        first [ rewrite (proj2 (Z.eqb_eq x y)) in H by (clear H; eblia) | rewrite (proj2 (Z.eqb_neq x y)) in H by (clear H; eblia) ]
    | context [Z.ltb ?x ?y] =>
        first [ rewrite (proj2 (Z.ltb_lt x y)) in H by (clear H; eblia) | rewrite (proj2 (Z.ltb_ge x y)) in H by (clear H; eblia) ]
    | context [Z.leb ?x ?y] =>
        first [ rewrite (proj2 (Z.leb_le x y)) in H by (clear H; eblia) | rewrite (proj2 (Z.leb_gt x y)) in H by (clear H; eblia) ]
    end.
  Ltac decide_head H :=
    cbn_bool_in H;   (* [comment removed for export] *)
    lazymatch type of H with
    | _ = ?t => match t with context [if ?c then _ else _] => decide_in_cond H c end
    end;
    cbn_bool_in H.

  (* [comment removed for export] *)
  Lemma Lepi : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w0 w1
      y5 y6 y7 y8 y9 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y28 y29 y30 y31
      (F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
    mem_inv img_segs m1 ->
    munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m1 -> wmono img_segs m m1 ->
    stk img_segs m1 (bv_unsigned sp - 80) (bv_unsigned sp + -80) ->
    rw_cells img_segs m1 (bv_unsigned sp + -80) (saved9 s8 s7 s6 s5 s4 s3 s2 s1 s0 j) ->
    (4096 <= bv_unsigned sp)%Z ->
    Z_to_bv 64 (lo64 R) = w0 -> Z_to_bv 64 (hi64 R) = w1 ->
    evt img_segs (multf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
      (MS (mkR ra spw gp tp y5 y6 y7 y8 y9 w0 w1 y12 y13 y14 y15 y16 y17
               y18 y19 y20 y21 y22 y23 y24 s9 s10 s11 y28 y29 y30 y31)
          F (Z_to_bv 64 (sym 0x1b3d0 + 1436)) fc None m1 (seg_rom img_segs)).
  Proof.
    intros until R. intros MI MU WM ST FR SPLO H0 H1. unfold saved9 in FR.
    pose_word_ranges.
    do 11 zstep.
    release_frame FR ST (bv_unsigned sp).
    rewrite <- H0, <- H1. finish.
  Qed.

  (* [comment removed for export] *)
  Ltac res_words :=
    rewrite ?lo64_mk128, ?hi64_mk128 by zrange; weq.

  (* [comment removed for export] *)
  Lemma Linf : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (sgn : Z)
      y5 y6 y7 y8 y9 y10 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y28 y29 y30 y31
      (F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
    mem_inv img_segs m1 ->
    munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m1 -> wmono img_segs m m1 ->
    stk img_segs m1 (bv_unsigned sp - 80) (bv_unsigned sp + -80) ->
    rw_cells img_segs m1 (bv_unsigned sp + -80) (saved9 s8 s7 s6 s5 s4 s3 s2 s1 s0 j) ->
    (4096 <= bv_unsigned sp)%Z ->
    (0 <= sgn < 2^64)%Z ->
    R = mk128 (Z.lor sgn 9223090561878065152) 0 ->
    evt img_segs (multf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
      (MS (mkR ra spw gp tp y5 y6 y7 y8 y9 y10 (Z_to_bv 64 sgn) y12 y13 y14 y15 y16 y17
               y18 y19 y20 y21 y22 y23 y24 s9 s10 s11 y28 y29 y30 y31)
          F (Z_to_bv 64 (sym 0x1b3d0 + 700)) fc None m1 (seg_rom img_segs)).
  Proof.
    intros until R. intros MI MU WM ST FR SPLO Rs HR. subst R.
    do 5 zstep. join Lepi; res_words.
  Qed.

  (* [comment removed for export] *)
  Lemma Lup : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (rl rh1 : Z)
      y5 y6 y7 y8 y9 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y28 y29 y30 y31
      (F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
    mem_inv img_segs m1 ->
    munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m1 -> wmono img_segs m m1 ->
    stk img_segs m1 (bv_unsigned sp - 80) (bv_unsigned sp + -80) ->
    rw_cells img_segs m1 (bv_unsigned sp + -80) (saved9 s8 s7 s6 s5 s4 s3 s2 s1 s0 j) ->
    (4096 <= bv_unsigned sp)%Z ->
    (0 <= rl < 2^64)%Z -> (0 <= rh1 < 2^64)%Z ->
    R = mk128 (Z.land (rh1 + Z.b2z (Z.land (rl + 1) 18446744073709551615 =? 0)) 18446744073709551615) (Z.land (rl + 1) 18446744073709551615) ->
    evt img_segs (multf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
      (MS (mkR ra spw gp tp y5 y6 y7 y8 y9 (Z_to_bv 64 rl) (Z_to_bv 64 rh1) y12 y13 y14 y15 y16 y17
               y18 y19 y20 y21 y22 y23 y24 s9 s10 s11 y28 y29 y30 y31)
          F (Z_to_bv 64 (sym 0x1b3d0 + 1424)) fc None m1 (seg_rom img_segs)).
  Proof.
    intros until R. intros MI MU WM ST FR SPLO R0 R1 HR. subst R.
    do 3 zstep. join Lepi; res_words.
  Qed.

  (* [comment removed for export] *)
  Lemma Ltie : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (rl rh1 lh2 ll2 : Z)
      y5 y6 y7 y8 y9 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y28 y29 y30 y31
      (F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
    mem_inv img_segs m1 ->
    munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m1 -> wmono img_segs m m1 ->
    stk img_segs m1 (bv_unsigned sp - 80) (bv_unsigned sp + -80) ->
    rw_cells img_segs m1 (bv_unsigned sp + -80) (saved9 s8 s7 s6 s5 s4 s3 s2 s1 s0 j) ->
    (4096 <= bv_unsigned sp)%Z ->
    (0 <= rl < 2^64)%Z -> (0 <= rh1 < 2^64)%Z -> (0 <= lh2 < 2^64)%Z -> (0 <= ll2 < 2^64)%Z ->
    R = (if Z.lor ll2 (Z.lxor lh2 9223372036854775808) =? 0
         then mk128 (Z.land (rh1 + Z.b2z (Z.land (rl + Z.land rl 1) 18446744073709551615 <? rl)) 18446744073709551615)
                    (Z.land (rl + Z.land rl 1) 18446744073709551615)
         else mk128 rh1 rl) ->
    evt img_segs (multf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
      (MS (mkR ra spw gp tp y5 y6 y7 y8 y9 (Z_to_bv 64 rl) (Z_to_bv 64 rh1) (Z_to_bv 64 ll2) (Z_to_bv 64 lh2) y14 y15 y16 y17
               y18 y19 y20 y21 y22 y23 y24 s9 s10 s11 y28 y29 y30 y31)
          F (Z_to_bv 64 (sym 0x1b3d0 + 768)) fc None m1 (seg_rom img_segs)).
  Proof.
    intros until R. intros MI MU WM ST FR SPLO R0 R1 R2 R3 HR.
    do 4 zstep. zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *) decide_head HR. subst R. join Lepi; res_words.
    - decide_head HR. subst R. do 7 zstep. join Lepi; res_words.
  Qed.

  (* [comment removed for export] *)
  Lemma Lrnd2 : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (rl rh lh2 ll2 sgn : Z)
      y5 y6 y7 y8 y9 y16 y17 y18 y19 y20 y21 y22 y23 y24 y28 y29 y30 y31
      (F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
    mem_inv img_segs m1 ->
    munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m1 -> wmono img_segs m m1 ->
    stk img_segs m1 (bv_unsigned sp - 80) (bv_unsigned sp + -80) ->
    rw_cells img_segs m1 (bv_unsigned sp + -80) (saved9 s8 s7 s6 s5 s4 s3 s2 s1 s0 j) ->
    (4096 <= bv_unsigned sp)%Z ->
    (0 <= rl < 2^64)%Z -> (0 <= rh < 2^64)%Z -> (0 <= lh2 < 2^64)%Z -> (0 <= ll2 < 2^64)%Z -> (0 <= sgn < 2^64)%Z ->
    lh2 <> 9223372036854775808 ->
    R = mul_round sgn rh rl lh2 ll2 ->
    evt img_segs (multf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
      (MS (mkR ra spw gp tp y5 y6 y7 y8 y9 (Z_to_bv 64 rl) (Z_to_bv 64 sgn) (Z_to_bv 64 ll2) (Z_to_bv 64 lh2) (Z_to_bv 64 rh)
               (Z_to_bv 64 9223372036854775808) y16 y17
               y18 y19 y20 y21 y22 y23 y24 s9 s10 s11 y28 y29 y30 y31)
          F (Z_to_bv 64 (sym 0x1b3d0 + 752)) fc None m1 (seg_rom img_segs)).
  Proof.
    intros until R. intros MI MU WM ST FR SPLO R0 R1 R2 R3 R4 Kh HR.
    unfold mul_round in HR. model_in HR. decide_head HR.
    do 2 zstep. rewrite lxor_b2z_1. zstep.
    zstep. if_cases K; zify_cond K; rewrite zb_lxor_sign in K by lia.
    - (* [comment removed for export] *) decide_head HR. join Lup.
    - decide_head HR. join Ltie.
  Qed.

  (* [comment removed for export] *)
  Lemma Lhalf : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (rl rh lh2 ll2 sgn : Z)
      y5 y6 y7 y8 y9 y16 y17 y18 y19 y20 y21 y22 y23 y24 y28 y29 y30 y31
      (F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
    mem_inv img_segs m1 ->
    munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m1 -> wmono img_segs m m1 ->
    stk img_segs m1 (bv_unsigned sp - 80) (bv_unsigned sp + -80) ->
    rw_cells img_segs m1 (bv_unsigned sp + -80) (saved9 s8 s7 s6 s5 s4 s3 s2 s1 s0 j) ->
    (4096 <= bv_unsigned sp)%Z ->
    (0 <= rl < 2^64)%Z -> (0 <= rh < 2^64)%Z -> (0 <= lh2 < 2^64)%Z -> (0 <= ll2 < 2^64)%Z -> (0 <= sgn < 2^64)%Z ->
    lh2 = 9223372036854775808 ->
    R = mul_round sgn rh rl lh2 ll2 ->
    evt img_segs (multf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
      (MS (mkR ra spw gp tp y5 y6 y7 y8 y9 (Z_to_bv 64 rl) (Z_to_bv 64 sgn) (Z_to_bv 64 ll2) (Z_to_bv 64 lh2) (Z_to_bv 64 rh)
               (Z_to_bv 64 9223372036854775808) y16 y17
               y18 y19 y20 y21 y22 y23 y24 s9 s10 s11 y28 y29 y30 y31)
          F (Z_to_bv 64 (sym 0x1b3d0 + 1412)) fc None m1 (seg_rom img_segs)).
  Proof.
    intros until R. intros MI MU WM ST FR SPLO R0 R1 R2 R3 R4 Kh HR.
    unfold mul_round in HR. model_in HR. decide_head HR.
    do 2 zstep.
    zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *) decide_head HR. join Ltie.
    - decide_head HR. join Lup.
  Qed.

  (* [comment removed for export] *)
  Lemma Lfin : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (pe hh hl lh ll sgn : Z)
      y6 y8 y9 y10 y18 y19 y20 y21 y22 y23 y24 y28 y29 y30 y31
      (F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
    mem_inv img_segs m1 ->
    munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m1 -> wmono img_segs m m1 ->
    stk img_segs m1 (bv_unsigned sp - 80) (bv_unsigned sp + -80) ->
    rw_cells img_segs m1 (bv_unsigned sp + -80) (saved9 s8 s7 s6 s5 s4 s3 s2 s1 s0 j) ->
    (4096 <= bv_unsigned sp)%Z ->
    (-131072 <= pe < 32767)%Z -> (0 <= hh < 2^64)%Z -> (0 <= hl < 2^64)%Z -> (0 <= lh < 2^64)%Z -> (0 <= ll < 2^64)%Z ->
    (0 <= sgn < 2^64)%Z ->
    R = mul_finish sgn pe hh hl lh ll ->
    evt img_segs (multf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
      (MS (mkR ra spw gp tp (Z_to_bv 64 pe) y6 (Z_to_bv 64 (-16383)) y8 y9
               y10 (Z_to_bv 64 sgn) (Z_to_bv 64 ll) (Z_to_bv 64 lh) (Z_to_bv 64 hh)
               (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 281474976710655) (Z_to_bv 64 hl)
               y18 y19 y20 y21 y22 y23 y24 s9 s10 s11 y28 y29 y30 y31)
          F (Z_to_bv 64 (sym 0x1b3d0 + 720)) fc None m1 (seg_rom img_segs)).
  Proof.
    intros until R. intros MI MU WM ST FR SPLO Rpe Rhh Rhl Rlh Rll Rsg HR.
    pose_word_ranges.
    destruct (Z.lt_ge_cases 0 pe) as [C1|C1].
    - (* [comment removed for export] *)
      rewrite mfr_normal in HR by lia.
      zrstep; if_decide. do 4 zrstep. do 2 zrstep. zrstep; if_cases K; zify_cond K.
      + join Lhalf.
      + join Lrnd2.
    - destruct (Z.lt_ge_cases pe (-126)) as [C2|C2].
      + (* [comment removed for export] *)
        rewrite mf_tiny in HR by lia. subst R.
        zrstep; if_decide. do 3 zrstep. zrstep; if_decide. do 2 zrstep. join Lepi; res_words.
      + zrstep; if_decide. do 3 zrstep. zrstep; if_decide. do 5 zrstep.
        destruct (Z.lt_total pe (-63)) as [C3|[C3|C3]].
        * (* [comment removed for export] *)
          rewrite mfr_caseA in HR by lia.
          zrstep; if_decide. do 7 zrstep. zrstep; if_decide. do 5 zrstep.
          do 7 zrstep. zrstep; if_decide. do 6 zrstep. zrstep; if_decide. do 7 zrstep.
          zrstep; if_cases K; zify_cond K.
          -- join Lrnd2.
          -- join Lhalf.
        * (* [comment removed for export] *)
          rewrite mfr_caseB in HR by lia.
          zrstep; if_decide. do 4 zrstep. zrstep; if_decide. do 8 zrstep. zrstep; if_decide.
          do 6 zrstep. zrstep; if_decide. do 7 zrstep.
          zrstep; if_cases K; zify_cond K.
          -- join Lrnd2.
          -- join Lhalf.
        * (* [comment removed for export] *)
          rewrite mfr_caseC in HR by lia.
          zrstep; if_decide. do 4 zrstep. zrstep; if_decide. do 8 zrstep. zrstep; if_decide.
          do 9 zrstep. zrstep; if_decide. do 5 zrstep. do 6 zrstep.
          zrstep; if_cases K; zify_cond K.
          -- join Lrnd2.
          -- join Lhalf.
  Qed.

  (* [comment removed for export] *)
  Lemma Ltail : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (es hh hl lh ll scale sgn : Z)
      y6 y8 y9 y18 y19 y20 y21 y22 y23 y24 y28 y29 y30 y31
      (F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
    mem_inv img_segs m1 ->
    munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m1 -> wmono img_segs m m1 ->
    stk img_segs m1 (bv_unsigned sp - 80) (bv_unsigned sp + -80) ->
    rw_cells img_segs m1 (bv_unsigned sp + -80) (saved9 s8 s7 s6 s5 s4 s3 s2 s1 s0 j) ->
    (4096 <= bv_unsigned sp)%Z ->
    (0 <= es < 65536)%Z -> (0 <= hh < 2^64)%Z -> (0 <= hl < 2^64)%Z -> (0 <= lh < 2^64)%Z -> (0 <= ll < 2^64)%Z ->
    (-1024 <= scale <= 1024)%Z -> (0 <= sgn < 2^64)%Z ->
    R = MC_tail sgn es hh hl lh ll scale ->
    evt img_segs (multf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
      (MS (mkR ra spw gp tp (Z_to_bv 64 es) y6 (Z_to_bv 64 (-16383)) y8 y9
               (Z_to_bv 64 scale) (Z_to_bv 64 sgn) (Z_to_bv 64 ll) (Z_to_bv 64 lh) (Z_to_bv 64 hh)
               (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 281474976710655) (Z_to_bv 64 hl)
               y18 y19 y20 y21 y22 y23 y24 s9 s10 s11 y28 y29 y30 y31)
          F (Z_to_bv 64 (sym 0x1b3d0 + 524)) fc None m1 (seg_rom img_segs)).
  Proof.
    intros until R. intros MI MU WM ST FR SPLO Res Rhh Rhl Rlh Rll Rsc Rsg HR.
    pose_word_ranges.
    unfold MC_tail in HR. model_in HR.
    do 3 zstep. replace (scale + -16383) with (scale - 16383) by lia.
    zstep. if_cases K1; zify_cond K1; decide_head HR.
    - (* [comment removed for export] *)
      do 3 zstep. zstep. if_cases K2; zify_cond K2; signed_lits_in K2; decide_head HR.
      + join Lfin. all: first [lia | exact HR].
      + join Linf.
    - do 12 zstep. zstep. if_cases K2; zify_cond K2; signed_lits_in K2; decide_head HR.
      + join Linf.
      + zstep. rewrite <- (Z_to_bv_land64 (Z.shiftl ll 1)). join Lfin. all: first [lia | exact HR].
  Qed.
End Walk.

(* [comment removed for export] *)
Lemma multf3_core : forall ra sp gp tp w1 w2 s0 s1 (scale sgn ea eb : Z) w4 a3 a4 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w3 t5 t6
    y8 y9 y18 y19 y20 y21 y22 y23 y24 y28
    (F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
  y28 = Z_to_bv 64 (Z.shiftr (bv_unsigned w1) 32) ->
  mem_inv img_segs m1 ->
  munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m1 -> wmono img_segs m m1 ->
  stk img_segs m1 (bv_unsigned sp - 80) (bv_unsigned sp + -80) ->
  rw_cells img_segs m1 (bv_unsigned sp + -80) (saved9 s8 s7 s6 s5 s4 s3 s2 s1 s0 j) ->
  (4096 <= bv_unsigned sp)%Z ->
  (0 <= ea < 32768)%Z -> (0 <= eb < 32768)%Z -> (-1024 <= scale <= 1024)%Z -> (0 <= sgn < 2^64)%Z ->
  R = mul_core sgn ea eb (bv_unsigned w1) (bv_unsigned w3) (bv_unsigned w2) (bv_unsigned w4) scale ->
  evt img_segs (multf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp (Z_to_bv 64 eb) w1 w2 y8 y9 (Z_to_bv 64 scale) (Z_to_bv 64 sgn) w4 a3 a4
             (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 281474976710655) (Z_to_bv 64 ea)
             y18 y19 y20 y21 y22 y23 y24 s9 s10 s11 y28 w3 t5 t6)
        F (Z_to_bv 64 (sym 0x1b3d0 + 128)) fc None m1 (seg_rom img_segs)).
Proof.
  intros until R. intros Hy28 MI MU WM ST FR SPLO Ra Rb Rsc Rsg HR. subst y28 R.
  eapply evt_cut. { eapply multf3_core1; eauto. }
  intros ms' P.
  (nelim P 34%nat; intros es hh hl lh ll y5' t1 t2' x8 x9 a5' a6' s2' s3' s4' s5' s6' s7' s8' t3 t4 t5' t6' EQ Res Rhh Rhl Rlh Rll E5 Ea5 Ea6 Et2 E)
.
  subst ms' y5' a5' a6' t2'. rewrite EQ.
  eapply Ltail; eauto.
Qed.

End Img.
(* [comment removed for export] *)
Ltac zzr := zsimp;
  try (lazymatch goal with |- context [(_ + 0)%Z] => rewrite ?Z.add_0_r end);
  try (lazymatch goal with |- context [Z.land (_ - Z.land _ 18446744073709551615) 18446744073709551615] => rewrite !land_sub_neg by alia end);
  try (lazymatch goal with |- context [Z.land _ 4294967295] => rewrite !land_M32_small by alia end);
  try (lazymatch goal with |- context [Z.shiftr (bv_signed (Z_to_bv 64 _)) 63] => rewrite !sra63_neg by alia end);
  try (lazymatch goal with |- context [Z.shiftr (bv_signed (Z_to_bv 64 _)) 63] => rewrite !sra63_pos by alia end);
  try (lazymatch goal with |- context [Z.land 18446744073709551615 _] => rewrite !land_ones_l by (first [zrange | alia]) end);
  try (lazymatch goal with |- context [Z.land 0 _] => rewrite ?Z.land_0_l end).
Ltac zrstep := step; zzr.
End G_multf3_tail.

(* [comment removed for export] *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.P Require F_sf_helpers2.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.P Require F_f128_mul_top.
Module G_multf3_norm.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.SFModel.
Import OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.P.F_f128_mul.F_f128_mul_core1 OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.P.F_sf_helpers2 OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.P.F_f128_mul OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.P.F_f128_mul_top.
Import G_multf3_core G_multf3_tail.

(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.
Import OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.G.ProgAt3.Prog_multf3. Import OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.StoreCache.StoreFast OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.StoreCache.   Import OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.G.ProgAt3.ProgAt. 
(* [comment removed for export] *)

Import ListNotations.

(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Step.step2_with rp rpm vh ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_with rp rpm vh.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.SysStep.step_ecall ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.astep_ecall.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Step.solve_load ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_load.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Step.solve_cond ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_cond.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Step.step ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Step.stepz ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Step.stepz_fast ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_fast.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.SysStep.sys_nret ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.asys_nret.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Tac.post_call segs m ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.apost_call segs m. (* [comment removed for export] *) Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs. Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs. Local Ltac mem_after_store ::= mem_after_store_fast. Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM. Local Ltac mem_after_store ::= mem_after_store_cached. Local Ltac addr_eq_tac ::= addr_eq_tac_cached. Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM. Local Ltac disjoint_goal ::= cbn [disjoint_from fst snd]; simpl_sizes_goal; disjoint_split.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Step.simp_regs ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RegFold.simp_regs_f.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.find_t_eval k t ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.find_t_eval_at k t.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.JunkAbs.split_for_access_abs H segs m A cs kn n.
Section Img.
  Context {IMG : RImg}.
  Context {CODE_multf3_norm : CodeAtT img_segs (sym 0x1b3d0) (multf3_prog_at IMG)}.
  Context {RB_multf3_norm : RelCode (sym 0x1b3d0) 1792}.
  Collection ImgHyps := IMG CODE_multf3_norm RB_multf3_norm.


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

(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac decide_test1 t :=
  first [ replace t with false by (symmetry; first [apply Z.eqb_neq | apply Z.ltb_ge | apply Z.leb_gt]; blia)
        | replace t with true  by (symmetry; first [apply Z.eqb_eq | apply Z.ltb_lt | apply Z.leb_le]; blia) ];
  cbn [andb orb negb].
Ltac decide_test1_try t := try decide_test1 t.

Lemma sra63_K_neg : forall x, 9223372036854775808 <= Z.land x 18446744073709551615 ->
  Z.shiftr (bv_signed (Z_to_bv 64 x)) 63 = -1.
Proof.
  intros x K. rewrite land_W64 in K. rewrite <- Z_to_bv_mod64. apply sra63_negw.
  pose proof (Z.mod_pos_bound x (2^64) ltac:(lia)). lia.
Qed.
Lemma sra63_K_pos : forall x, Z.land x 18446744073709551615 < 9223372036854775808 ->
  Z.shiftr (bv_signed (Z_to_bv 64 x)) 63 = 0.
Proof.
  intros x K. rewrite land_W64 in K. rewrite <- Z_to_bv_mod64. apply sra63_pos.
  pose proof (Z.mod_pos_bound x (2^64) ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma ndr_lt64 : forall hi lo c,
  0 <= hi < 2^64 -> 0 <= lo < 2^64 -> 0 <= c < 2^64 -> clz128_mirror hi lo = c ->
  9223372036854775808 <= Z.land (Z.land (Z.land (c - 15) 18446744073709551615) 4294967295 + -64) 18446744073709551615 ->
  nd_hi hi lo = Z.lor (Z.land (hi ≪ Z.land (Z.land (c - 15) 18446744073709551615) 63) 18446744073709551615)
                      (Z.land ((lo ≫ 1) ≫ Z.land (Z.lxor (Z.land (Z.land (c - 15) 18446744073709551615) 4294967295) 18446744073709551615) 63) 18446744073709551615)
  /\ nd_lo hi lo = Z.land 18446744073709551615 (Z.land (lo ≪ Z.land (Z.land (c - 15) 18446744073709551615) 63) 18446744073709551615).
Proof.
  intros hi lo c Hhi Hlo Hc E K2.
  unfold nd_hi, nd_lo, norm_denormal. rewrite E. cbv beta zeta iota delta [shl128_mirror].
  change b2z with Z.b2z. unfold_sf. zb_fold_lits.
  replace (Z.land (Z.land (c - 15) 18446744073709551615) 4294967295 - 64) with (Z.land (Z.land (c - 15) 18446744073709551615) 4294967295 + -64) by lia.
  decide_test1 ((Z.land (Z.land (Z.land (c - 15) 18446744073709551615) 4294967295 + -64) 18446744073709551615 ≫ 63) =? 0)%Z. split; [| reflexivity]. strip_lands. reflexivity.
Qed.
Lemma ndr_ge64 : forall hi lo c,
  0 <= hi < 2^64 -> 0 <= lo < 2^64 -> 0 <= c < 2^64 -> clz128_mirror hi lo = c ->
  Z.land (Z.land (Z.land (c - 15) 18446744073709551615) 4294967295 + -64) 18446744073709551615 < 9223372036854775808 ->
  nd_hi hi lo = Z.land (lo ≪ Z.land (Z.land (Z.land (c - 15) 18446744073709551615) 4294967295) 63) 18446744073709551615
  /\ nd_lo hi lo = Z.land 0 (Z.land (lo ≪ Z.land (Z.land (c - 15) 18446744073709551615) 63) 18446744073709551615).
Proof.
  intros hi lo c Hhi Hlo Hc E K2.
  unfold nd_hi, nd_lo, norm_denormal. rewrite E. cbv beta zeta iota delta [shl128_mirror].
  change b2z with Z.b2z. unfold_sf. zb_fold_lits.
  replace (Z.land (Z.land (c - 15) 18446744073709551615) 4294967295 - 64) with (Z.land (Z.land (c - 15) 18446744073709551615) 4294967295 + -64) by lia.
  decide_test1 ((Z.land (Z.land (Z.land (c - 15) 18446744073709551615) 4294967295 + -64) 18446744073709551615 ≫ 63) =? 0)%Z. split; reflexivity.
Qed.

Section Norm.
  Variables (sp : word).
  Notation spw := (Z_to_bv 64 (bv_unsigned sp + -80)).
  Notation ONES := (Z_to_bv 64 18446744073709551615).
  Notation M48 := (Z_to_bv 64 281474976710655).

  (* [comment removed for export] *)
  Ltac norm_tail HQ E clz sh n32 hi lo :=
    let K2 := fresh "K2" in let E1 := fresh "E" in let E2 := fresh "E" in
    zstep; if_cases K2; zify_cond K2;
    [ rewrite (sra63_K_neg _ K2); do 9 zstep; subst n32 sh;
      destruct (ndr_lt64 hi lo clz ltac:(zrange) ltac:(zrange) ltac:(assumption) E K2) as [E1 E2];
      rewrite <- E1, <- E2; rewrite <- nd_clz_eq in E; rewrite <- E; eapply HQ
    | rewrite (sra63_K_pos _ K2); do 6 zstep; subst n32 sh;
      destruct (ndr_ge64 hi lo clz ltac:(zrange) ltac:(zrange) ltac:(assumption) E K2) as [E1 E2];
      (* [comment removed for export] *)
      match type of E1 with _ = Z.land ?v _ => rewrite <- (Z_to_bv_land64 v) end;
      rewrite <- E1, <- E2; rewrite <- nd_clz_eq in E; rewrite <- E; eapply HQ ].

  (* [comment removed for export] *)
  Lemma LnormA : forall (Q : machine_state -> Prop) ra gp tp t0 (h : Z) t2 s0 s1 wlo a1' a2' a3' a4 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t5 t6
      (F : bvmap 5 word) fc (m1 : word -> option byte),
    (0 <= h < 2^64)%Z ->
    (forall y13 y30 y31 y8 y9,
      evt img_segs Q
        (MS (mkR ra spw gp tp t0 (Z_to_bv 64 (nd_hi h (bv_unsigned wlo))) t2 y8 y9
                 (Z_to_bv 64 (16 - nd_clz h (bv_unsigned wlo))) a1' a2' y13 a4 ONES M48 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                 (Z_to_bv 64 (Z.shiftr (nd_hi h (bv_unsigned wlo)) 32)) (Z_to_bv 64 (nd_lo h (bv_unsigned wlo))) y30 y31)
            F (Z_to_bv 64 (sym 0x1b3d0 + 1524)) fc None m1 (seg_rom img_segs))) ->
    evt img_segs Q
      (MS (mkR ra spw gp tp t0 (Z_to_bv 64 h) t2 s0 s1 wlo a1' a2' a3' a4 ONES M48 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 wlo t5 t6)
          F (Z_to_bv 64 (sym 0x1b3d0 + 996)) fc None m1 (seg_rom img_segs)).
  Proof.
    intros until m1. intros Rh HQ.
    pose_word_ranges.
    zstep. zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      set (x := bv_unsigned wlo).
  do 6 zstep. model_reg 28 x1 (Z.lor x (Z.shiftr x 1)).
  do 6 zstep. model_reg 28 x2 (Z.lor x1 (Z.shiftr x1 2)).
  do 10 zstep. model_reg 28 x3 (Z.lor x2 (Z.shiftr x2 4)).
  do 2 zstep. model_reg 28 x4 (Z.lor x3 (Z.shiftr x3 8)).
  do 2 zstep. model_reg 28 x5 (Z.lor x4 (Z.shiftr x4 16)).
  do 2 zstep. model_reg 28 x6 (Z.lor x5 (Z.shiftr x5 32)).
  do 1 zstep. model_reg 28 y (Z.lxor x6 18446744073709551615).
  do 4 zstep. model_reg 28 c1 (Z.land (y - (Z.land (Z.shiftr y 1) 6148914691236517205)) 18446744073709551615).
  do 4 zstep. model_reg 28 c2 (Z.land ((Z.land c1 3689348814741910323) + (Z.land (Z.shiftr c1 2) 3689348814741910323)) 18446744073709551615).
  do 3 zstep. model_reg 28 c3 (Z.land (Z.land (c2 + (Z.shiftr c2 4)) 18446744073709551615) 1085102592571150095).
  do 2 zstep. model_reg 28 c4 (Z.shiftr (Z.land (c3 * 72340172838076673) 18446744073709551615) 56).
      assert (Ec4 : c4 = clz64_mirror x). { symmetry. cbv delta [clz64_mirror]. sf_vocab. fold_model_lets. reflexivity. }
      zstep. decide_test1 (h <? 1)%Z. change (Z.b2z true) with 1. zb_fold_lits.
      model_reg 13 clz (Z.lor (clz64_mirror x) 64).
      pose proof (clz128_hi_z h x K) as E. fold clz in E.
      zstep. model_reg 30 sh (Z.land (clz - 15) 18446744073709551615).
      do 3 zstep. model_reg 31 n32 (Z.land sh 4294967295).
      do 2 zstep. subst x. norm_tail HQ E clz sh n32 h (bv_unsigned wlo).
    - zstep.
  do 6 zstep. model_reg 28 x1 (Z.lor h (Z.shiftr h 1)).
  do 6 zstep. model_reg 28 x2 (Z.lor x1 (Z.shiftr x1 2)).
  do 10 zstep. model_reg 28 x3 (Z.lor x2 (Z.shiftr x2 4)).
  do 2 zstep. model_reg 28 x4 (Z.lor x3 (Z.shiftr x3 8)).
  do 2 zstep. model_reg 28 x5 (Z.lor x4 (Z.shiftr x4 16)).
  do 2 zstep. model_reg 28 x6 (Z.lor x5 (Z.shiftr x5 32)).
  do 1 zstep. model_reg 28 y (Z.lxor x6 18446744073709551615).
  do 4 zstep. model_reg 28 c1 (Z.land (y - (Z.land (Z.shiftr y 1) 6148914691236517205)) 18446744073709551615).
  do 4 zstep. model_reg 28 c2 (Z.land ((Z.land c1 3689348814741910323) + (Z.land (Z.shiftr c1 2) 3689348814741910323)) 18446744073709551615).
  do 3 zstep. model_reg 28 c3 (Z.land (Z.land (c2 + (Z.shiftr c2 4)) 18446744073709551615) 1085102592571150095).
  do 2 zstep. model_reg 28 c4 (Z.shiftr (Z.land (c3 * 72340172838076673) 18446744073709551615) 56).
      assert (Ec4 : c4 = clz64_mirror h). { symmetry. cbv delta [clz64_mirror]. sf_vocab. fold_model_lets. reflexivity. }
      zstep. decide_test1 (h <? 1)%Z. change (Z.b2z false) with 0. zb_fold_lits. rewrite Z.lor_0_r.
      model_reg 13 clz (clz64_mirror h).
      pose proof (clz128_hi_nz h (bv_unsigned wlo) K) as E. fold clz in E.
      zstep. model_reg 30 sh (Z.land (clz - 15) 18446744073709551615).
      do 3 zstep. model_reg 31 n32 (Z.land sh 4294967295).
      do 2 zstep. norm_tail HQ E clz sh n32 h (bv_unsigned wlo).
  Qed.


  (* [comment removed for export] *)
  Ltac norm_tailB HQ E clz sh n32 hi lo sc1 :=
    let K2 := fresh "K2" in let E1 := fresh "E" in let E2 := fresh "E" in
    zstep; if_cases K2; zify_cond K2;
    [ do 5 zstep; do 6 zstep; rewrite (sra63_K_neg _ K2); zb_fold_lits; subst n32 sh;
      destruct (ndr_lt64 hi lo clz ltac:(zrange) ltac:(zrange) ltac:(assumption) E K2) as [E1 E2];
      rewrite <- E1, <- E2
    | do 2 zstep; do 6 zstep; rewrite (sra63_K_pos _ K2); zb_fold_lits; subst n32 sh;
      destruct (ndr_ge64 hi lo clz ltac:(zrange) ltac:(zrange) ltac:(assumption) E K2) as [E1 E2];
      match type of E1 with _ = Z.land ?v _ => rewrite <- (Z_to_bv_land64 v) end;
      rewrite <- E1, <- E2 ];
    match goal with |- context [Z_to_bv 64 (Z.land sc1 18446744073709551615 - clz + 16)] =>
      replace (Z_to_bv 64 (Z.land sc1 18446744073709551615 - clz + 16)) with (Z_to_bv 64 (sc1 - clz + 16))
        by (apply Z_to_bv_eqm; rewrite land_W64; Z.div_mod_to_equations; lia) end;
    rewrite <- nd_clz_eq in E; rewrite <- E; eapply HQ.

  (* [comment removed for export] *)
  Lemma LnormB : forall (Q : machine_state -> Prop) ra gp tp t0 t1 (h sc1 : Z) s0 s1 wlo a1' y13 y14 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m1 : word -> option byte),
    (0 <= h < 2^64)%Z -> (-1024 <= sc1 <= 1024)%Z ->
    (forall y13' y14' y30 y31 y8 y9,
      evt img_segs Q
        (MS (mkR ra spw gp tp t0 t1 (Z_to_bv 64 (nd_hi h (bv_unsigned wlo))) y8 y9
                 (Z_to_bv 64 (sc1 - nd_clz h (bv_unsigned wlo) + 16)) a1' (Z_to_bv 64 (nd_lo h (bv_unsigned wlo))) y13' y14' ONES M48 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 y30 y31)
            F (Z_to_bv 64 (sym 0x1b3d0 + 128)) fc None m1 (seg_rom img_segs))) ->
    evt img_segs Q
      (MS (mkR ra spw gp tp t0 t1 (Z_to_bv 64 h) s0 s1 (Z_to_bv 64 sc1) a1' wlo y13 y14 ONES M48 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (sym 0x1b3d0 + 1532)) fc None m1 (seg_rom img_segs)).
  Proof.
    intros until m1. intros Rh Rsc HQ.
    pose_word_ranges.
    do 2 zstep. zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      set (x := bv_unsigned wlo).
  do 5 zstep. model_reg 14 x1 (Z.lor x (Z.shiftr x 1)).
  do 5 zstep. model_reg 14 x2 (Z.lor x1 (Z.shiftr x1 2)).
  do 8 zstep. model_reg 14 x3 (Z.lor x2 (Z.shiftr x2 4)).
  do 2 zstep. model_reg 14 x4 (Z.lor x3 (Z.shiftr x3 8)).
  do 2 zstep. model_reg 14 x5 (Z.lor x4 (Z.shiftr x4 16)).
  do 2 zstep. model_reg 14 x6 (Z.lor x5 (Z.shiftr x5 32)).
  do 1 zstep. model_reg 14 y (Z.lxor x6 18446744073709551615).
  do 4 zstep. model_reg 14 c1 (Z.land (y - (Z.land (Z.shiftr y 1) 6148914691236517205)) 18446744073709551615).
  do 6 zstep. model_reg 14 c2 (Z.land ((Z.land c1 3689348814741910323) + (Z.land (Z.shiftr c1 2) 3689348814741910323)) 18446744073709551615).
  do 4 zstep. model_reg 14 c3 (Z.land (Z.land (c2 + (Z.shiftr c2 4)) 18446744073709551615) 1085102592571150095).
  do 3 zstep. model_reg 14 c4 (Z.shiftr (Z.land (c3 * 72340172838076673) 18446744073709551615) 56).
      assert (Ec4 : c4 = clz64_mirror x). { symmetry. cbv delta [clz64_mirror]. sf_vocab. fold_model_lets. reflexivity. }
      zstep. decide_test1 (h <? 1)%Z. change (Z.b2z true) with 1. zb_fold_lits.
      model_reg 13 clz (Z.lor (clz64_mirror x) 64).
      pose proof (clz128_hi_z h x K) as E. fold clz in E.
      zstep. model_reg 14 sh (Z.land (clz - 15) 18446744073709551615).
      do 2 zstep. model_reg 31 n32 (Z.land sh 4294967295).
      zstep. subst x. norm_tailB HQ E clz sh n32 h (bv_unsigned wlo) sc1.
    - zstep.
  do 5 zstep. model_reg 14 x1 (Z.lor h (Z.shiftr h 1)).
  do 5 zstep. model_reg 14 x2 (Z.lor x1 (Z.shiftr x1 2)).
  do 8 zstep. model_reg 14 x3 (Z.lor x2 (Z.shiftr x2 4)).
  do 2 zstep. model_reg 14 x4 (Z.lor x3 (Z.shiftr x3 8)).
  do 2 zstep. model_reg 14 x5 (Z.lor x4 (Z.shiftr x4 16)).
  do 2 zstep. model_reg 14 x6 (Z.lor x5 (Z.shiftr x5 32)).
  do 1 zstep. model_reg 14 y (Z.lxor x6 18446744073709551615).
  do 4 zstep. model_reg 14 c1 (Z.land (y - (Z.land (Z.shiftr y 1) 6148914691236517205)) 18446744073709551615).
  do 6 zstep. model_reg 14 c2 (Z.land ((Z.land c1 3689348814741910323) + (Z.land (Z.shiftr c1 2) 3689348814741910323)) 18446744073709551615).
  do 4 zstep. model_reg 14 c3 (Z.land (Z.land (c2 + (Z.shiftr c2 4)) 18446744073709551615) 1085102592571150095).
  do 3 zstep. model_reg 14 c4 (Z.shiftr (Z.land (c3 * 72340172838076673) 18446744073709551615) 56).
      assert (Ec4 : c4 = clz64_mirror h). { symmetry. cbv delta [clz64_mirror]. sf_vocab. fold_model_lets. reflexivity. }
      zstep. decide_test1 (h <? 1)%Z. change (Z.b2z false) with 0. zb_fold_lits. rewrite Z.lor_0_r.
      model_reg 13 clz (clz64_mirror h).
      pose proof (clz128_hi_nz h (bv_unsigned wlo) K) as E. fold clz in E.
      zstep. model_reg 14 sh (Z.land (clz - 15) 18446744073709551615).
      do 2 zstep. model_reg 31 n32 (Z.land sh 4294967295).
      zstep. norm_tailB HQ E clz sh n32 h (bv_unsigned wlo) sc1.
  Qed.


End Norm.

End Img.
(* [comment removed for export] *)
Ltac decide_test1 t :=
  first [ replace t with false by (symmetry; first [apply Z.eqb_neq | apply Z.ltb_ge | apply Z.leb_gt]; blia)
        | replace t with true  by (symmetry; first [apply Z.eqb_eq | apply Z.ltb_lt | apply Z.leb_le]; blia) ];
  cbn [andb orb negb].
Ltac decide_test1_try t := try decide_test1 t.
End G_multf3_norm.

(* [comment removed for export] *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.G Require G_divtf3.
Module G_divtf3_norm.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.SFModel.
Import OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.P.F_f128_mul.F_f128_mul_core1 OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.P.F_sf_helpers2 OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.P.F_f128_mul OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.P.F_f128_mul_top.
Import G_multf3_core G_multf3_tail G_multf3_norm OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.G.G_divtf3.

(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.
Import OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.G.ProgAt3.Prog_divtf3.   Import OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.G.ProgAt3.ProgAt. 
(* [comment removed for export] *)

Import ListNotations.

(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Step.step2_with rp rpm vh ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_with rp rpm vh.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.SysStep.step_ecall ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.astep_ecall.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Step.solve_load ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_load.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Step.solve_cond ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_cond.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Step.step ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Step.stepz ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Step.stepz_fast ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_fast.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.SysStep.sys_nret ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.asys_nret.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Tac.post_call segs m ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.apost_call segs m.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Step.simp_regs ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RegFold.simp_regs_f.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.find_t_eval k t ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.find_t_eval_at k t.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.JunkAbs.split_for_access_abs H segs m A cs kn n.
Section Img.
  Context {IMG : RImg}.
  Context {CODE_divtf3_norm : CodeAtT img_segs (sym 0x1c6b0) (divtf3_prog_at IMG)}.
  Context {RB_divtf3_norm : RelCode (sym 0x1c6b0) 2308}.
  Collection ImgHyps := IMG CODE_divtf3_norm RB_divtf3_norm.


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


(* [comment removed for export] *)
Ltac decide_test1 t :=
  first [ replace t with false by (symmetry; first [apply Z.eqb_neq | apply Z.ltb_ge | apply Z.leb_gt]; blia)
        | replace t with true  by (symmetry; first [apply Z.eqb_eq | apply Z.ltb_lt | apply Z.leb_le]; blia) ];
  cbn [andb orb negb].
Ltac decide_test1_try t := try decide_test1 t.

Section Norm.
  Variables (sp : word).
  Notation spw := (Z_to_bv 64 (bv_unsigned sp + -112)).
  Notation M48 := (Z_to_bv 64 281474976710655).

  (* [comment removed for export] *)
  Ltac norm_tailA HQ E clz sh n32 hi lo :=
    let K2 := fresh "K2" in let E1 := fresh "E" in let E2 := fresh "E" in
    zstep; if_cases K2; zify_cond K2;
    [ do 5 zstep; do 5 zstep; rewrite (sra63_K_neg _ K2); zb_fold_lits; subst n32 sh;
      destruct (ndr_lt64 hi lo clz ltac:(zrange) ltac:(zrange) ltac:(assumption) E K2) as [E1 E2];
      rewrite <- E1, <- E2
    | do 2 zstep; do 5 zstep; rewrite (sra63_K_pos _ K2); zb_fold_lits; subst n32 sh;
      destruct (ndr_ge64 hi lo clz ltac:(zrange) ltac:(zrange) ltac:(assumption) E K2) as [E1 E2];
      match type of E1 with _ = Z.land ?v _ => rewrite <- (Z_to_bv_land64 v) end;
      rewrite <- E1, <- E2 ];
    rewrite <- nd_clz_eq in E; rewrite <- E; eapply HQ.

  (* [comment removed for export] *)
  Lemma LnormA : forall (Q : machine_state -> Prop) ra gp tp t0 t1 t2 (h : Z) s0 s1 wlo a1 a2 a3 a4 a5 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m1 : word -> option byte),
    (0 <= h < 2^64)%Z ->
    (forall y8 y13 y29 y30 y31,
      evt img_segs Q
        (MS (mkR ra spw gp tp t0 t1 t2 y8 s1 (Z_to_bv 64 (nd_lo h (bv_unsigned wlo))) a1 a2 y13 a4 a5 a6 (Z_to_bv 64 (nd_hi h (bv_unsigned wlo)))
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (16 - nd_clz h (bv_unsigned wlo))) y29 y30 y31)
            F (Z_to_bv 64 (sym 0x1c6b0 + 2040)) fc None m1 (seg_rom img_segs))) ->
    evt img_segs Q
      (MS (mkR ra spw gp tp t0 t1 t2 s0 s1 wlo a1 a2 a3 a4 a5 a6 (Z_to_bv 64 h) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (sym 0x1c6b0 + 1376)) fc None m1 (seg_rom img_segs)).
  Proof.
    intros until m1. intros Rh HQ.
    pose_word_ranges.
    do 2 zstep. zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      set (x := bv_unsigned wlo).
  do 5 zstep. model_reg 28 x1 (Z.lor x (Z.shiftr x 1)).
  do 5 zstep. model_reg 28 x2 (Z.lor x1 (Z.shiftr x1 2)).
  do 8 zstep. model_reg 28 x3 (Z.lor x2 (Z.shiftr x2 4)).
  do 2 zstep. model_reg 28 x4 (Z.lor x3 (Z.shiftr x3 8)).
  do 2 zstep. model_reg 28 x5 (Z.lor x4 (Z.shiftr x4 16)).
  do 2 zstep. model_reg 28 x6 (Z.lor x5 (Z.shiftr x5 32)).
  do 1 zstep. model_reg 28 y (Z.lxor x6 18446744073709551615).
  do 4 zstep. model_reg 28 c1 (Z.land (y - (Z.land (Z.shiftr y 1) 6148914691236517205)) 18446744073709551615).
  do 6 zstep. model_reg 28 c2 (Z.land ((Z.land c1 3689348814741910323) + (Z.land (Z.shiftr c1 2) 3689348814741910323)) 18446744073709551615).
  do 4 zstep. model_reg 28 c3 (Z.land (Z.land (c2 + (Z.shiftr c2 4)) 18446744073709551615) 1085102592571150095).
  do 3 zstep. model_reg 28 c4 (Z.shiftr (Z.land (c3 * 72340172838076673) 18446744073709551615) 56).
      assert (Ec4 : c4 = clz64_mirror x). { symmetry. cbv delta [clz64_mirror]. sf_vocab. fold_model_lets. reflexivity. }
      zstep. decide_test1 (h <? 1)%Z. change (Z.b2z true) with 1. zb_fold_lits.
      model_reg 13 clz (Z.lor (clz64_mirror x) 64).
      pose proof (clz128_hi_z h x K) as E. fold clz in E.
      zstep. model_reg 28 sh (Z.land (clz - 15) 18446744073709551615).
      do 2 zstep. model_reg 30 n32 (Z.land sh 4294967295).
      zstep. subst x. norm_tailA HQ E clz sh n32 h (bv_unsigned wlo).
    - zstep.
  do 5 zstep. model_reg 28 x1 (Z.lor h (Z.shiftr h 1)).
  do 5 zstep. model_reg 28 x2 (Z.lor x1 (Z.shiftr x1 2)).
  do 8 zstep. model_reg 28 x3 (Z.lor x2 (Z.shiftr x2 4)).
  do 2 zstep. model_reg 28 x4 (Z.lor x3 (Z.shiftr x3 8)).
  do 2 zstep. model_reg 28 x5 (Z.lor x4 (Z.shiftr x4 16)).
  do 2 zstep. model_reg 28 x6 (Z.lor x5 (Z.shiftr x5 32)).
  do 1 zstep. model_reg 28 y (Z.lxor x6 18446744073709551615).
  do 4 zstep. model_reg 28 c1 (Z.land (y - (Z.land (Z.shiftr y 1) 6148914691236517205)) 18446744073709551615).
  do 6 zstep. model_reg 28 c2 (Z.land ((Z.land c1 3689348814741910323) + (Z.land (Z.shiftr c1 2) 3689348814741910323)) 18446744073709551615).
  do 4 zstep. model_reg 28 c3 (Z.land (Z.land (c2 + (Z.shiftr c2 4)) 18446744073709551615) 1085102592571150095).
  do 3 zstep. model_reg 28 c4 (Z.shiftr (Z.land (c3 * 72340172838076673) 18446744073709551615) 56).
      assert (Ec4 : c4 = clz64_mirror h). { symmetry. cbv delta [clz64_mirror]. sf_vocab. fold_model_lets. reflexivity. }
      zstep. decide_test1 (h <? 1)%Z. change (Z.b2z false) with 0. zb_fold_lits. rewrite Z.lor_0_r.
      model_reg 13 clz (clz64_mirror h).
      pose proof (clz128_hi_nz h (bv_unsigned wlo) K) as E. fold clz in E.
      zstep. model_reg 28 sh (Z.land (clz - 15) 18446744073709551615).
      do 2 zstep. model_reg 30 n32 (Z.land sh 4294967295).
      zstep. norm_tailA HQ E clz sh n32 h (bv_unsigned wlo).
  Qed.

  (* [comment removed for export] *)
  Ltac norm_tailB2 HQ E clz sh n32 hi lo sc1 :=
    let K2 := fresh "K2" in let E1 := fresh "E" in let E2 := fresh "E" in
    zstep; if_cases K2; zify_cond K2;
    [ do 5 zstep; do 6 zstep; rewrite (sra63_K_neg _ K2); zb_fold_lits; subst n32 sh;
      destruct (ndr_lt64 hi lo clz ltac:(zrange) ltac:(zrange) ltac:(assumption) E K2) as [E1 E2];
      rewrite <- E1, <- E2
    | do 2 zstep; do 6 zstep; rewrite (sra63_K_pos _ K2); zb_fold_lits; subst n32 sh;
      destruct (ndr_ge64 hi lo clz ltac:(zrange) ltac:(zrange) ltac:(assumption) E K2) as [E1 E2];
      match type of E1 with _ = Z.land ?v _ => rewrite <- (Z_to_bv_land64 v) end;
      rewrite <- E1, <- E2 ];
    replace (Z_to_bv 64 (clz + sc1 + -16)) with (Z_to_bv 64 (sc1 + clz - 16)) by (f_equal; lia);
    rewrite <- nd_clz_eq in E; rewrite <- E; eapply HQ.

  (* [comment removed for export] *)
  Lemma LnormB : forall (Q : machine_state -> Prop) ra gp tp (h : Z) t1 t2 (sc1 : Z) s0 s1 a0 a1 wlo a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6
      (F : bvmap 5 word) fc (m1 : word -> option byte),
    (0 <= h < 2^64)%Z -> (-1024 <= sc1 <= 1024)%Z ->
    (forall y8 y13 y14 y29 y30 y31,
      evt img_segs Q
        (MS (mkR ra spw gp tp (Z_to_bv 64 (nd_hi h (bv_unsigned wlo))) t1 t2 y8 s1 a0 a1 (Z_to_bv 64 (nd_lo h (bv_unsigned wlo))) y13 y14 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (sc1 + nd_clz h (bv_unsigned wlo) - 16)) y29 y30 y31)
            F (Z_to_bv 64 (sym 0x1c6b0 + 136)) fc None m1 (seg_rom img_segs))) ->
    evt img_segs Q
      (MS (mkR ra spw gp tp (Z_to_bv 64 h) t1 t2 s0 s1 a0 a1 wlo a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 sc1) t4 t5 t6)
          F (Z_to_bv 64 (sym 0x1c6b0 + 2048)) fc None m1 (seg_rom img_segs)).
  Proof.
    intros until m1. intros Rh Rsc HQ.
    pose_word_ranges.
    do 2 zstep. zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      set (x := bv_unsigned wlo).
  do 5 zstep. model_reg 14 x1 (Z.lor x (Z.shiftr x 1)).
  do 5 zstep. model_reg 14 x2 (Z.lor x1 (Z.shiftr x1 2)).
  do 8 zstep. model_reg 14 x3 (Z.lor x2 (Z.shiftr x2 4)).
  do 2 zstep. model_reg 14 x4 (Z.lor x3 (Z.shiftr x3 8)).
  do 2 zstep. model_reg 14 x5 (Z.lor x4 (Z.shiftr x4 16)).
  do 2 zstep. model_reg 14 x6 (Z.lor x5 (Z.shiftr x5 32)).
  do 1 zstep. model_reg 14 y (Z.lxor x6 18446744073709551615).
  do 4 zstep. model_reg 14 c1 (Z.land (y - (Z.land (Z.shiftr y 1) 6148914691236517205)) 18446744073709551615).
  do 6 zstep. model_reg 14 c2 (Z.land ((Z.land c1 3689348814741910323) + (Z.land (Z.shiftr c1 2) 3689348814741910323)) 18446744073709551615).
  do 4 zstep. model_reg 14 c3 (Z.land (Z.land (c2 + (Z.shiftr c2 4)) 18446744073709551615) 1085102592571150095).
  do 3 zstep. model_reg 14 c4 (Z.shiftr (Z.land (c3 * 72340172838076673) 18446744073709551615) 56).
      assert (Ec4 : c4 = clz64_mirror x). { symmetry. cbv delta [clz64_mirror]. sf_vocab. fold_model_lets. reflexivity. }
      zstep. decide_test1 (h <? 1)%Z. change (Z.b2z true) with 1. zb_fold_lits.
      model_reg 13 clz (Z.lor (clz64_mirror x) 64).
      pose proof (clz128_hi_z h x K) as E. fold clz in E.
      zstep. model_reg 14 sh (Z.land (clz - 15) 18446744073709551615).
      do 2 zstep. model_reg 30 n32 (Z.land sh 4294967295).
      zstep. subst x. norm_tailB2 HQ E clz sh n32 h (bv_unsigned wlo) sc1.
    - zstep.
  do 5 zstep. model_reg 14 x1 (Z.lor h (Z.shiftr h 1)).
  do 5 zstep. model_reg 14 x2 (Z.lor x1 (Z.shiftr x1 2)).
  do 8 zstep. model_reg 14 x3 (Z.lor x2 (Z.shiftr x2 4)).
  do 2 zstep. model_reg 14 x4 (Z.lor x3 (Z.shiftr x3 8)).
  do 2 zstep. model_reg 14 x5 (Z.lor x4 (Z.shiftr x4 16)).
  do 2 zstep. model_reg 14 x6 (Z.lor x5 (Z.shiftr x5 32)).
  do 1 zstep. model_reg 14 y (Z.lxor x6 18446744073709551615).
  do 4 zstep. model_reg 14 c1 (Z.land (y - (Z.land (Z.shiftr y 1) 6148914691236517205)) 18446744073709551615).
  do 6 zstep. model_reg 14 c2 (Z.land ((Z.land c1 3689348814741910323) + (Z.land (Z.shiftr c1 2) 3689348814741910323)) 18446744073709551615).
  do 4 zstep. model_reg 14 c3 (Z.land (Z.land (c2 + (Z.shiftr c2 4)) 18446744073709551615) 1085102592571150095).
  do 3 zstep. model_reg 14 c4 (Z.shiftr (Z.land (c3 * 72340172838076673) 18446744073709551615) 56).
      assert (Ec4 : c4 = clz64_mirror h). { symmetry. cbv delta [clz64_mirror]. sf_vocab. fold_model_lets. reflexivity. }
      zstep. decide_test1 (h <? 1)%Z. change (Z.b2z false) with 0. zb_fold_lits. rewrite Z.lor_0_r.
      model_reg 13 clz (clz64_mirror h).
      pose proof (clz128_hi_nz h (bv_unsigned wlo) K) as E. fold clz in E.
      zstep. model_reg 14 sh (Z.land (clz - 15) 18446744073709551615).
      do 2 zstep. model_reg 30 n32 (Z.land sh 4294967295).
      zstep. norm_tailB2 HQ E clz sh n32 h (bv_unsigned wlo) sc1.
  Qed.
End Norm.

End Img.
(* [comment removed for export] *)
Ltac decide_test1 t :=
  first [ replace t with false by (symmetry; first [apply Z.eqb_neq | apply Z.ltb_ge | apply Z.leb_gt]; blia)
        | replace t with true  by (symmetry; first [apply Z.eqb_eq | apply Z.ltb_lt | apply Z.leb_le]; blia) ];
  cbn [andb orb negb].
Ltac decide_test1_try t := try decide_test1 t.
End G_divtf3_norm.

(* [comment removed for export] *)
Module G_multf3.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.SFModel.
Import OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.P.F_f128_mul.F_f128_mul_core1 OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.P.F_sf_helpers2 OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.P.F_f128_mul OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.P.F_f128_mul_top.
Import G_multf3_core G_multf3_tail G_multf3_norm.
Import OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.
Import OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.G.ProgAt3.Prog_multf3.   Import OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.G.ProgAt3.ProgAt. 
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Step.step2_with rp rpm vh ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_with rp rpm vh.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.SysStep.step_ecall ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.astep_ecall.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Step.solve_load ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_load.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Step.solve_cond ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_cond.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Step.step ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Step.stepz ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Step.stepz_fast ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_fast.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.SysStep.sys_nret ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.asys_nret.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Tac.post_call segs m ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.apost_call segs m.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Step.simp_regs ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RegFold.simp_regs_f.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.find_t_eval k t ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.find_t_eval_at k t.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.JunkAbs.split_for_access_abs H segs m A cs kn n.
Section Img.
  Context {IMG : RImg}.
  Context {CODE_multf3 : CodeAtT img_segs (sym 0x1b3d0) (multf3_prog_at IMG)}.
  Context {RB_multf3 : RelCode (sym 0x1b3d0) 1792}.
  Collection ImgHyps := IMG CODE_multf3 RB_multf3.



(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac flia ::= flia_fast.
Local Ltac unfold_sf_in H ::= unfold_sf_in_recast H.
Local Ltac blia ::= blia_fast.
(* [comment removed for export] *)
Local Ltac step ::= step_fast. Local Ltac stepz ::= stepz_fast.
Local Ltac zsimp ::= zsimp_fast.

Section Walk.
  Variables (sp a0 a1 a2 a3 : word).
  Notation a_lo := (bv_unsigned a0). Notation a_hi := (bv_unsigned a1).
  Notation b_lo := (bv_unsigned a2). Notation b_hi := (bv_unsigned a3).
  Notation spw := (Z_to_bv 64 (bv_unsigned sp + -80)).
  Notation E_sgn := (Z.land (Z.shiftl (Z.shiftr (Z.lxor b_hi a_hi) 63) 63) 18446744073709551615).
  Notation E_aExp := (Z.shiftr (Z.land (Z.shiftl a_hi 1) 18446744073709551615) 49).
  Notation E_bExp := (Z.shiftr (Z.land (Z.shiftl b_hi 1) 18446744073709551615) 49).
  Notation E_aSig := (Z.land a_hi 281474976710655).
  Notation E_bSig := (Z.land b_hi 281474976710655).
  Notation E_aAbs := (Z.land a_hi 9223372036854775807).
  Notation E_bAbs := (Z.land b_hi 9223372036854775807).
  Notation ONES := (Z_to_bv 64 18446744073709551615).
  Notation M48 := (Z_to_bv 64 281474976710655).

  (* [comment removed for export] *)
  Ltac hyp :=
    match goal with
    | H : mem_inv _ ?m |- mem_inv _ ?m => exact H
    | H : munch ?W ?m ?m' |- munch ?W ?m ?m' => exact H
    | H : wmono _ ?m ?m' |- wmono _ ?m ?m' => exact H
    | H : stk _ ?m ?lo ?hi |- stk _ ?m ?lo ?hi => exact H
    | H : rw_cells _ ?m ?A _ |- rw_cells _ ?m ?A _ => exact H
    | H : (?a <= ?b)%Z |- (?a <= ?b)%Z => exact H
    | H : bv_unsigned ?w = _ |- bv_unsigned ?w = _ => exact H
    | H : ?x = ?y |- ?x = ?y => exact H
    | H : ?x <> ?y |- ?x <> ?y => exact H
    | H : (?a <= ?x < ?b)%Z |- (?a <= ?x < ?b)%Z => exact H
    | |- (_ <= _ <= _)%Z => lia
    | |- (0 <= _ < _)%Z => first [zrange2 | lia]
    end.
  Ltac join L := eapply L; try hyp.
  (* [comment removed for export] *)
  Ltac model_in H := sf_model_in H.
  Ltac eblia := rewrite ?Z.shiftl_mul_pow2 in * by lia; blia.
  Ltac decide_in_cond H c :=
    match c with
    | context [Z.eqb ?x ?y] =>
        first [ rewrite (proj2 (Z.eqb_eq x y)) in H by (clear H; eblia) | rewrite (proj2 (Z.eqb_neq x y)) in H by (clear H; eblia) ]
    | context [Z.ltb ?x ?y] =>
        first [ rewrite (proj2 (Z.ltb_lt x y)) in H by (clear H; eblia) | rewrite (proj2 (Z.ltb_ge x y)) in H by (clear H; eblia) ]
    | context [Z.leb ?x ?y] =>
        first [ rewrite (proj2 (Z.leb_le x y)) in H by (clear H; eblia) | rewrite (proj2 (Z.leb_gt x y)) in H by (clear H; eblia) ]
    end.
  Ltac decide_head H :=
    cbn_bool_in H;   (* [comment removed for export] *)
    lazymatch type of H with
    | _ = ?t => match t with context [if ?c then _ else _] => decide_in_cond H c end
    end;
    cbn_bool_in H.
  (* [comment removed for export] *)
  Ltac decide_in_cond_t H c :=
    match c with
    | context [Z.eqb ?x ?y] => rewrite (proj2 (Z.eqb_eq x y)) in H by (clear H; eblia)
    | context [Z.ltb ?x ?y] => rewrite (proj2 (Z.ltb_lt x y)) in H by (clear H; eblia)
    | context [Z.leb ?x ?y] => rewrite (proj2 (Z.leb_le x y)) in H by (clear H; eblia)
    end.
  Ltac decide_in_cond_f H c :=
    match c with
    | context [Z.eqb ?x ?y] => rewrite (proj2 (Z.eqb_neq x y)) in H by (clear H; eblia)
    | context [Z.ltb ?x ?y] => rewrite (proj2 (Z.ltb_ge x y)) in H by (clear H; eblia)
    | context [Z.leb ?x ?y] => rewrite (proj2 (Z.leb_gt x y)) in H by (clear H; eblia)
    end.
  Ltac decide_head_t H := cbn_bool_in H;
    lazymatch type of H with | _ = ?t => match t with context [if ?c then _ else _] => decide_in_cond_t H c end end; cbn_bool_in H.
  Ltac decide_head_f H := cbn_bool_in H;
    lazymatch type of H with | _ = ?t => match t with context [if ?c then _ else _] => decide_in_cond_f H c end end; cbn_bool_in H.
  Ltac res_words := rewrite ?lo64_mk128, ?hi64_mk128 by zrange; first [ apply Z_to_bv_lit_self | weq ].

  (* [comment removed for export] *)
  Lemma Lbchk : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (h1 sc1 : Z) w3
      y8 y9 y13 y18 y19 y20 y21 y22 y23 y24 y30 y31
      (F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
    mem_inv img_segs m1 ->
    munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m1 -> wmono img_segs m m1 ->
    stk img_segs m1 (bv_unsigned sp - 80) (bv_unsigned sp + -80) ->
    rw_cells img_segs m1 (bv_unsigned sp + -80) (saved9 s8 s7 s6 s5 s4 s3 s2 s1 s0 j) ->
    (4096 <= bv_unsigned sp)%Z ->
    (0 <= h1 < 2^64)%Z -> (-600 <= sc1 <= 16)%Z ->
    R = FM_p2b a_hi b_lo b_hi h1 (bv_unsigned w3) sc1 ->
    evt img_segs (multf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
      (MS (mkR ra spw gp tp (Z_to_bv 64 E_bExp) (Z_to_bv 64 h1) (Z_to_bv 64 E_bSig) y8 y9
               (Z_to_bv 64 sc1) (Z_to_bv 64 E_sgn) a2 y13 (Z_to_bv 64 E_bAbs) ONES M48 (Z_to_bv 64 E_aExp)
               y18 y19 y20 y21 y22 y23 y24 s9 s10 s11 (Z_to_bv 64 (Z.shiftr h1 32)) w3 y30 y31)
          F (Z_to_bv 64 (sym 0x1b3d0 + 1524)) fc None m1 (seg_rom img_segs)).
  Proof.
    intros until R. intros MI MU WM ST FR SPLO Rh1 Rsc HR.
    pose_word_ranges.
    assert (Ra : 0 <= E_aExp < 32768).
    { rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. zb_masks. Z.div_mod_to_equations. lia. }
    assert (Rb : 0 <= E_bExp < 32768).
    { rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. zb_masks. Z.div_mod_to_equations. lia. }
    unfold FM_p2b in HR. model_in HR. 
    zstep. zstep. if_cases K; zify_cond K; [ decide_head_f HR | decide_head_t HR ].
    - (* [comment removed for export] *)
      join multf3_core. { rewrite unsigned_lit by lia. reflexivity. }
      rewrite !unsigned_lit by zrange. exact HR.
    - rewrite norm_denormal_eta in HR. cbn_bool_in HR.
      eapply LnormB; [zrange | lia |]. intros.
      pose proof (nd_clz_range E_bSig b_lo).
      pose proof (nd_hi_range E_bSig b_lo ltac:(zrange)). pose proof (nd_lo_range E_bSig b_lo).
      join multf3_core. { rewrite unsigned_lit by lia. reflexivity. }
      rewrite !unsigned_lit by assumption. exact HR.
  Qed.

  (* [comment removed for export] *)
  Lemma Lp2r : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
      y8 y9 y13 y18 y19 y20 y21 y22 y23 y24 y31
      (F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
    mem_inv img_segs m1 ->
    munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m1 -> wmono img_segs m m1 ->
    stk img_segs m1 (bv_unsigned sp - 80) (bv_unsigned sp + -80) ->
    rw_cells img_segs m1 (bv_unsigned sp + -80) (saved9 s8 s7 s6 s5 s4 s3 s2 s1 s0 j) ->
    (4096 <= bv_unsigned sp)%Z ->
    R = FM_p2 a_lo a_hi b_lo b_hi ->
    evt img_segs (multf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
      (MS (mkR ra spw gp tp (Z_to_bv 64 E_bExp) (Z_to_bv 64 E_aSig) (Z_to_bv 64 E_bSig) y8 y9
               a0 (Z_to_bv 64 E_sgn) a2 y13 (Z_to_bv 64 E_bAbs) ONES M48 (Z_to_bv 64 E_aExp)
               y18 y19 y20 y21 y22 y23 y24 s9 s10 s11 (Z_to_bv 64 (Z.shiftr E_aSig 32)) a0 (Z_to_bv 64 E_aAbs) y31)
          F (Z_to_bv 64 (sym 0x1b3d0 + 988)) fc None m1 (seg_rom img_segs)).
  Proof.
    intros until R. intros MI MU WM ST FR SPLO HR.
    pose_word_ranges.
    unfold FM_p2 in HR. model_in HR.
    zstep. zstep. if_cases K; zify_cond K; [ decide_head_f HR | decide_head_t HR ].
    - (* [comment removed for export] *)
      do 2 zstep. join Lbchk. all: rewrite ?unsigned_lit by zrange; exact HR.
    - rewrite norm_denormal_eta in HR. cbn_bool_in HR.
      eapply LnormA; [zrange |]. intros.
      pose proof (nd_clz_range E_aSig a_lo).
      pose proof (nd_hi_range E_aSig a_lo ltac:(zrange)). pose proof (nd_lo_range E_aSig a_lo).
      join Lbchk. all: rewrite ?unsigned_lit by assumption; exact HR.
  Qed.

  (* [comment removed for export] *)
  Lemma Linfr : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
      y8 y9 y13 y18 y19 y20 y21 y22 y23 y24 y31
      (F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
    mem_inv img_segs m1 ->
    munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m1 -> wmono img_segs m m1 ->
    stk img_segs m1 (bv_unsigned sp - 80) (bv_unsigned sp + -80) ->
    rw_cells img_segs m1 (bv_unsigned sp + -80) (saved9 s8 s7 s6 s5 s4 s3 s2 s1 s0 j) ->
    (4096 <= bv_unsigned sp)%Z ->
    R = FM_inf a_lo a_hi b_lo b_hi ->
    evt img_segs (multf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
      (MS (mkR ra spw gp tp (Z_to_bv 64 E_bExp) (Z_to_bv 64 E_aSig) (Z_to_bv 64 E_bSig) y8 y9
               a0 (Z_to_bv 64 E_sgn) a2 y13 (Z_to_bv 64 E_bAbs) ONES M48 (Z_to_bv 64 E_aExp)
               y18 y19 y20 y21 y22 y23 y24 s9 s10 s11 (Z_to_bv 64 (Z.shiftr E_aSig 32)) a0 (Z_to_bv 64 E_aAbs) y31)
          F (Z_to_bv 64 (sym 0x1b3d0 + 648)) fc None m1 (seg_rom img_segs)).
  Proof.
    intros until R. intros MI MU WM ST FR SPLO HR.
    pose_word_ranges.
    unfold FM_inf in HR. model_in HR.
    do 4 zstep. zstep. if_cases K7; zify_cond K7; [ decide_head_f HR | decide_head_t HR ].
    - (* [comment removed for export] *)
      do 2 zstep. zstep. if_cases K9; zify_cond K9; [ decide_head_f HR | decide_head_t HR ].
      + (* [comment removed for export] *)
        zstep. zstep. if_cases K11; zify_cond K11; [ decide_head_t HR | decide_head_f HR ].
        * (* [comment removed for export] *) subst R. do 2 zstep. join Lepi; res_words.
        * zstep. zstep. if_cases K12; zify_cond K12; [ decide_head_t HR | decide_head_f HR ].
          -- subst R. do 2 zstep. join Lepi; res_words.
          -- join Lp2r.
      + (* [comment removed for export] *)
        zstep. zstep. if_cases K10; zify_cond K10; [ decide_head_f HR | decide_head_t HR ].
        * join Linf.
        * subst R. do 3 zstep. join Lepi; res_words.
    - (* [comment removed for export] *)
      zstep. zstep. if_cases K8; zify_cond K8; [ decide_head_f HR | decide_head_t HR ].
      + join Linf.
      + subst R. do 2 zstep. do 3 zstep. join Lepi; res_words.
  Qed.

  (* [comment removed for export] *)
  Lemma Lbr : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
      y8 y9 y14 y18 y19 y20 y21 y22 y23 y24
      (F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
    mem_inv img_segs m1 ->
    munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m1 -> wmono img_segs m m1 ->
    stk img_segs m1 (bv_unsigned sp - 80) (bv_unsigned sp + -80) ->
    rw_cells img_segs m1 (bv_unsigned sp + -80) (saved9 s8 s7 s6 s5 s4 s3 s2 s1 s0 j) ->
    (4096 <= bv_unsigned sp)%Z ->
    R = FM_b a_lo a_hi b_lo b_hi ->
    evt img_segs (multf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
      (MS (mkR ra spw gp tp (Z_to_bv 64 E_bExp) (Z_to_bv 64 E_aSig) (Z_to_bv 64 E_bSig) y8 y9
               a0 (Z_to_bv 64 E_sgn) a2 a3 y14 ONES M48 (Z_to_bv 64 E_aExp)
               y18 y19 y20 y21 y22 y23 y24 s9 s10 s11 (Z_to_bv 64 (Z.shiftr E_aSig 32)) a0 (Z_to_bv 64 E_aAbs)
               (Z_to_bv 64 9223372036854775807))
          F (Z_to_bv 64 (sym 0x1b3d0 + 624)) fc None m1 (seg_rom img_segs)).
  Proof.
    intros until R. intros MI MU WM ST FR SPLO HR.
    pose_word_ranges.
    unfold FM_b in HR. model_in HR.
    do 3 zstep. zstep. if_cases K5; zify_cond K5; [ decide_head_t HR | decide_head_f HR ].
    - (* [comment removed for export] *)
      zstep. zstep. if_cases K6; zify_cond K6; [ decide_head_t HR | decide_head_f HR ].
      + (* [comment removed for export] *) join Linfr.
      + subst R. do 5 zstep. join Lepi; res_words.
    - zstep. zstep. if_cases K6; zify_cond K6; [ decide_head_f HR | decide_head_t HR ].
      + (* [comment removed for export] *) subst R. do 5 zstep. join Lepi; res_words.
      + join Linfr.
  Qed.

  (* [comment removed for export] *)
  Lemma Lspec : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
      y8 y9 y18 y19 y20 y21 y22 y23 y24 y30 y31
      (F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
    mem_inv img_segs m1 ->
    munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m1 -> wmono img_segs m m1 ->
    stk img_segs m1 (bv_unsigned sp - 80) (bv_unsigned sp + -80) ->
    rw_cells img_segs m1 (bv_unsigned sp + -80) (saved9 s8 s7 s6 s5 s4 s3 s2 s1 s0 j) ->
    (4096 <= bv_unsigned sp)%Z ->
    R = FM_a a_lo a_hi b_lo b_hi ->
    evt img_segs (multf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
      (MS (mkR ra spw gp tp (Z_to_bv 64 E_bExp) (Z_to_bv 64 E_aSig) (Z_to_bv 64 E_bSig) y8 y9
               a0 (Z_to_bv 64 E_sgn) a2 a3 a1 ONES M48 (Z_to_bv 64 E_aExp)
               y18 y19 y20 y21 y22 y23 y24 s9 s10 s11 (Z_to_bv 64 (Z.shiftr E_aSig 32)) a0 y30 y31)
          F (Z_to_bv 64 (sym 0x1b3d0 + 596)) fc None m1 (seg_rom img_segs)).
  Proof.
    intros until R. intros MI MU WM ST FR SPLO HR.
    pose_word_ranges.
    unfold FM_a in HR. model_in HR.
    do 4 zstep. zstep. if_cases K3; zify_cond K3; [ decide_head_t HR | decide_head_f HR ].
    - (* [comment removed for export] *)
      zstep. zstep. if_cases K4; zify_cond K4; [ decide_head_t HR | decide_head_f HR ].
      + join Lbr.
      + subst R. do 4 zstep. join Lepi; res_words.
    - zstep. zstep. if_cases K4; zify_cond K4; [ decide_head_f HR | decide_head_t HR ].
      + subst R. do 4 zstep. join Lepi; res_words.
      + join Lbr.
  Qed.

  (* [comment removed for export] *)
  Lemma multf3_walk : forall ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : word -> option byte),
    stk img_segs m (bv_unsigned sp - 80) (bv_unsigned sp) ->
    mem_inv img_segs m ->
    (4096 <= bv_unsigned sp)%Z ->
    evt img_segs (multf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                 (f128_mul_w a_lo a_hi b_lo b_hi) m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (sym 0x1b3d0)) fc None m (seg_rom img_segs)).
  Proof.
    intros until m. intros ST MI SPLO.
    pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m) as MU. pose proof (wmono_refl img_segs m) as WM.
    pose_word_ranges.
    carve_frame 80%nat ST.
    remember (f128_mul_w a_lo a_hi b_lo b_hi) as R eqn:HR.
    unfold f128_mul_w in HR. model_in HR.
    do 10 zstep. do 18 zstep.
    (* [comment removed for export] *)
    replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply Z_to_bv_eqm; reflexivity).
    rewrite <- (Z_to_bv_land64 (Z.shiftl (Z.shiftr (Z.lxor b_hi a_hi) 63) 63)).
    assert (Ra : 0 <= E_aExp < 32768).
    { rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. zb_masks. Z.div_mod_to_equations. lia. }
    assert (Rb : 0 <= E_bExp < 32768).
    { rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. zb_masks. Z.div_mod_to_equations. lia. }
    zstep. if_cases K1; zify_cond K1; [ decide_head_t HR | decide_head_f HR ].
    - (* [comment removed for export] *) join Lspec.
    - zstep. zstep. if_cases K2; zify_cond K2; [ decide_head_t HR | decide_head_f HR ].
      + join Lspec.
      + zstep. join multf3_core. { rewrite unsigned_lit by zrange. reflexivity. }
        all: rewrite ?unsigned_lit by zrange; exact HR.
  Qed.
End Walk.

Definition multf3_stmt : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : word -> option byte),
    stk img_segs m (bv_unsigned sp - 80) (bv_unsigned sp) ->
    mem_inv img_segs m ->
    (4096 <= bv_unsigned sp)%Z ->
    evt img_segs (multf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                 (f128_mul (mk128 (bv_unsigned a1) (bv_unsigned a0)) (mk128 (bv_unsigned a3) (bv_unsigned a2))) m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (sym 0x1b3d0)) fc None m (seg_rom img_segs)).

(* [comment removed for export] *)
Theorem multf3_spec : multf3_stmt.
Proof.
  unfold multf3_stmt. intros.
  rewrite f128_mul_words by (pose_word_ranges; assumption).
  apply multf3_walk; assumption.
Qed.

(* [comment removed for export] *)
Definition multf3_contract : Prop := multf3_stmt.
Lemma multf3_contract_ok : multf3_contract.
Proof. exact multf3_spec. Qed.


End Img.

(* [comment removed for export] *)
Existing Class multf3_contract.
End G_multf3.

(* [comment removed for export] *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Spec Require Prelim.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Spec Require SoftFloat.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Spec Require FmtFp.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.P Require SFW1_lemmas.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.G Require G_letf2.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.G Require G_fixunstfsi.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.G Require G_floatsitf.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.G Require G_floatunsitf.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.G Require G_pop_arg.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.G Require G_subtf3.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.G Require G_FmtFp_facts2.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.G Require G_signbitl.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.G Require G_fpclassifyl.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.G Require G_memset.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.G Require G_memcpy.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.G Require G_fwritex.
Module G_fmt_fp_calls.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.SFModel.
Import OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Spec.Prelim OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Spec.SoftFloat OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Spec.FmtFp.
Import OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.P.SFW1_lemmas.
Import OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.G.G_letf2 OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.G.G_fixunstfsi OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.G.G_floatsitf OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.G.G_floatunsitf OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.G.G_pop_arg.G_extenddftf2 OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.G.G_subtf3.G_fe_getround OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.G.G_subtf3.G_addtf3_A OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.G.G_subtf3.G_addtf3_E OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.G.G_subtf3 G_multf3_tail G_multf3 OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.G.G_divtf3 OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.G.G_FmtFp_facts2.G_frexpl OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.G.G_signbitl OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.G.G_fpclassifyl OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.G.G_memset OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.G.G_memcpy OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.G.G_fwritex.
Import OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac. Import OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.NElim.  
Import ListNotations.
Open Scope bv_scope.


(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Step.step2_with rp rpm vh ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_with rp rpm vh.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.SysStep.step_ecall ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.astep_ecall.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Step.solve_load ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_load.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Step.solve_cond ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_cond.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Step.step ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Step.stepz ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Step.stepz_fast ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_fast.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.SysStep.sys_nret ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.asys_nret.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Tac.post_call segs m ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.apost_call segs m.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Step.simp_regs ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RegFold.simp_regs_f.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.JunkAbs.split_for_access_abs H segs m A cs kn n.
Section Img.
  Context {IMG : RImg}.
  Context {RS_1c6b0 : RelSym (sym 0x1c6b0)}.
  Let rp_1c6b0 : (0 <= sym 0x1c6b0 /\ sym 0x1c6b0 < 2^30)%Z := @rel_sym_pf _ RS_1c6b0.
  Context {SPEC_letf2 : letf2_contract}.
  Context {SPEC_fixunstfsi : fixunstfsi_contract}.
  Context {SPEC_floatsitf : floatsitf_contract}.
  Context {SPEC_floatunsitf : floatunsitf_contract}.
  Context {SPEC_extenddftf2 : extenddftf2_contract}.
  Context {SPEC_frexpl : frexpl_contract}.
  Context {SPEC_signbitl : signbitl_contract}.
  Context {SPEC_fpclassifyl : fpclassifyl_contract}.
  Context {SPEC_multf3 : multf3_contract}.
  Context {SPEC_subtf3 : subtf3_contract}.
  Context {SPEC_addtf3_spec : addtf3_spec_c}.
  Collection ImgHyps := IMG RS_1c6b0 rp_1c6b0 SPEC_letf2 SPEC_fixunstfsi SPEC_floatsitf SPEC_floatunsitf SPEC_extenddftf2 SPEC_frexpl SPEC_signbitl SPEC_fpclassifyl SPEC_multf3 SPEC_subtf3 SPEC_addtf3_spec.



(* [comment removed for export] *)
Ltac norm_rsegs := idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Open Scope Z_scope.

Lemma lo64_range : forall x, 0 <= lo64 x < 2^64.
Proof. intros. unfold lo64, wrap64, ONES64. rewrite land_W64. apply Z.mod_pos_bound. lia. Qed.
Lemma hi64_range : forall x, 0 <= hi64 x < 2^64.
Proof. intros. unfold hi64, wrap64, ONES64. rewrite land_W64. apply Z.mod_pos_bound. lia. Qed.

(* [comment removed for export] *)
Definition canon (x : Z) : Z := lo64 x + 2^64 * hi64 x.

Lemma lo64_canon : forall x, lo64 (canon x) = lo64 x.
Proof. intros. unfold canon. apply lo64_words. apply lo64_range. Qed.
Lemma hi64_canon : forall x, hi64 (canon x) = hi64 x.
Proof. intros. unfold canon. apply hi64_words; [apply lo64_range | apply hi64_range]. Qed.
Lemma mk128_canon : forall x, mk128 (hi64 x) (lo64 x) = canon x.
Proof.
  intros. unfold mk128, canon. pose proof (lo64_range x). pose proof (hi64_range x).
  rewrite Z.shiftl_mul_pow2 by lia. rewrite lor_disjoint_add; [lia|].
  - apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 64).
    + rewrite Z.mul_pow2_bits_low by lia. reflexivity.
    + replace (Z.testbit (lo64 x) i) with false; [apply Bool.andb_false_r|].
      symmetry. destruct (Z.eq_dec (lo64 x) 0) as [->|]; [apply Z.bits_0|].
      apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 64; [apply Z.log2_lt_pow2; lia|lia].
Qed.
Lemma canon_small : forall x, 0 <= x < 2^128 -> canon x = x.
Proof.
  intros x Hx. unfold canon, lo64, hi64, wrap64, ONES64. rewrite !land_W64, Z.shiftr_div_pow2 by lia.
  rewrite (Z.mod_small (x / 2^64)) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  pose proof (Z.div_mod x (2^64) ltac:(lia)). lia.
Qed.
Lemma canon_range : forall x, 0 <= canon x < 2^128.
Proof. intros. unfold canon. pose proof (lo64_range x). pose proof (hi64_range x). lia. Qed.

Lemma f128_mul_canon : forall a b, f128_mul (canon a) (canon b) = f128_mul a b.
Proof. intros. unfold f128_mul. rewrite !lo64_canon, !hi64_canon. reflexivity. Qed.
Lemma f128_div_canon : forall a b, f128_div (canon a) (canon b) = f128_div a b.
Proof. intros. unfold f128_div. rewrite !lo64_canon, !hi64_canon. reflexivity. Qed.
Lemma f128_add_canon : forall a b, f128_add (canon a) (canon b) = f128_add a b.
Proof. intros. unfold f128_add. rewrite !lo64_canon, !hi64_canon. reflexivity. Qed.
Lemma f128_add_canon_l : forall a b, f128_add (canon a) b = f128_add a b.
Proof. intros. unfold f128_add. rewrite !lo64_canon, !hi64_canon. reflexivity. Qed.
Lemma f128_sub_canon : forall a b, f128_sub (canon a) (canon b) = f128_sub a b.
Proof. intros. unfold f128_sub. rewrite !lo64_canon, !hi64_canon. apply f128_add_canon_l. Qed.
Lemma f128_le_canon : forall a b, f128_le (canon a) (canon b) = f128_le a b.
Proof. intros. unfold f128_le. rewrite !lo64_canon, !hi64_canon. reflexivity. Qed.
Lemma fixunstfsi_a0_canon : forall a, fixunstfsi_a0 (canon a) = fixunstfsi_a0 a.
Proof. intros. unfold fixunstfsi_a0. rewrite !lo64_canon, !hi64_canon. reflexivity. Qed.

Lemma ulit_lo64 : forall x, bv_unsigned (Z_to_bv 64 (lo64 x)) = lo64 x.
Proof. intros. apply unsigned_lit. apply lo64_range. Qed.
Lemma ulit_hi64 : forall x, bv_unsigned (Z_to_bv 64 (hi64 x)) = hi64 x.
Proof. intros. apply unsigned_lit. apply hi64_range. Qed.

Local Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition leaf2_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (R : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 R)) (Z_to_bv 64 (hi64 R)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom img_segs)
    /\ munch [] m m' /\ wmono img_segs m m' /\ mem_inv img_segs m'.

(* [comment removed for export] *)
Definition leaf1_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (r : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom img_segs)
    /\ munch [] m m' /\ wmono img_segs m m' /\ mem_inv img_segs m'.

Lemma letf2_callv : forall ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (X Y : Z),
  mem_inv img_segs m ->
  evt img_segs (leaf1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (f128_le X Y) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x1b24c)) fc None m (seg_rom img_segs)).
Proof.
  intros until Y. intros MI. eapply evt_mono. { eapply SPEC_letf2. exact MI. }
  intros ms' P. unfold letf2_post in P. rewrite !ulit_lo64, !ulit_hi64 in P.
  change (lo64 X + 2 ^ 64 * hi64 X)%Z with (canon X) in P. change (lo64 Y + 2 ^ 64 * hi64 Y)%Z with (canon Y) in P.
  rewrite f128_le_canon in P. exact P.
Qed.

(* [comment removed for export] *)
Definition letf2_callv_c : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (X Y : Z),
  mem_inv img_segs m ->
  evt img_segs (leaf1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (f128_le X Y) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x1b24c)) fc None m (seg_rom img_segs)).
Lemma letf2_callv_c_ok : letf2_callv_c.
Proof. exact letf2_callv. Qed.


(* [comment removed for export] *)
Lemma letf2_callv0 : forall ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (X : Z),
  mem_inv img_segs m ->
  evt img_segs (leaf1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (f128_le X F128_ZERO) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 0) (Z_to_bv 64 0) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x1b24c)) fc None m (seg_rom img_segs)).
Proof. intros. change (Z_to_bv 64 0) with (Z_to_bv 64 (lo64 0)) at 1. change (Z_to_bv 64 0) with (Z_to_bv 64 (hi64 0)) at 1. apply letf2_callv. assumption. Qed.

(* [comment removed for export] *)
Definition letf2_callv0_c : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (X : Z),
  mem_inv img_segs m ->
  evt img_segs (leaf1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (f128_le X F128_ZERO) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 0) (Z_to_bv 64 0) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x1b24c)) fc None m (seg_rom img_segs)).
Lemma letf2_callv0_c_ok : letf2_callv0_c.
Proof. exact letf2_callv0. Qed.


Lemma fixunstfsi_callv : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (X : Z),
  mem_inv img_segs m ->
  evt img_segs (leaf1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (fixunstfsi_a0 X) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x1c488)) fc None m (seg_rom img_segs)).
Proof.
  intros until X. intros MI. eapply evt_mono. { eapply SPEC_fixunstfsi. exact MI. }
  intros ms' P. unfold fixunstfsi_post in P. rewrite !ulit_lo64, !ulit_hi64 in P.
  change (lo64 X + 2 ^ 64 * hi64 X)%Z with (canon X) in P. rewrite fixunstfsi_a0_canon in P. exact P.
Qed.

(* [comment removed for export] *)
Definition fixunstfsi_callv_c : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (X : Z),
  mem_inv img_segs m ->
  evt img_segs (leaf1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (fixunstfsi_a0 X) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x1c488)) fc None m (seg_rom img_segs)).
Lemma fixunstfsi_callv_c_ok : fixunstfsi_callv_c.
Proof. exact fixunstfsi_callv. Qed.


(* [comment removed for export] *)
Lemma floatsitf_callv : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (v i : Z),
  mem_inv img_segs m -> (0 <= v < 2^64)%Z -> v = sext32 i ->
  evt img_segs (leaf2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (f128_of_i32 i) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 v) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x1bad0)) fc None m (seg_rom img_segs)).
Proof.
  intros until i. intros MI Hv Hi. eapply evt_mono. { eapply SPEC_floatsitf; [exact MI|]. rewrite unsigned_lit by lia. exact Hi. }
  intros ms' P. exact P.
Qed.

(* [comment removed for export] *)
Definition floatsitf_callv_c : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (v i : Z),
  mem_inv img_segs m -> (0 <= v < 2^64)%Z -> v = sext32 i ->
  evt img_segs (leaf2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (f128_of_i32 i) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 v) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x1bad0)) fc None m (seg_rom img_segs)).
Lemma floatsitf_callv_c_ok : floatsitf_callv_c.
Proof. exact floatsitf_callv. Qed.

(* [comment removed for export] *)
Lemma floatsitf_callp : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (i : Z),
  mem_inv img_segs m -> (0 <= i < 2^31)%Z ->
  evt img_segs (leaf2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (f128_of_i32 i) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 i) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x1bad0)) fc None m (seg_rom img_segs)).
Proof. intros until i. intros MI Hi. apply floatsitf_callv; [exact MI | lia |]. rewrite sext32_small by lia. reflexivity. Qed.

(* [comment removed for export] *)
Definition floatsitf_callp_c : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (i : Z),
  mem_inv img_segs m -> (0 <= i < 2^31)%Z ->
  evt img_segs (leaf2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (f128_of_i32 i) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 i) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x1bad0)) fc None m (seg_rom img_segs)).
Lemma floatsitf_callp_c_ok : floatsitf_callp_c.
Proof. exact floatsitf_callp. Qed.


Lemma floatunsitf_callv : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (v u : Z),
  mem_inv img_segs m -> (0 <= v < 2^64)%Z -> v = sext32 u ->
  evt img_segs (leaf2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (f128_of_u32 u) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 v) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x1c51c)) fc None m (seg_rom img_segs)).
Proof.
  intros until u. intros MI Hv Hu. eapply evt_mono. { eapply SPEC_floatunsitf; [exact MI|]. rewrite unsigned_lit by lia. exact Hu. }
  intros ms' P. exact P.
Qed.

(* [comment removed for export] *)
Definition floatunsitf_callv_c : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (v u : Z),
  mem_inv img_segs m -> (0 <= v < 2^64)%Z -> v = sext32 u ->
  evt img_segs (leaf2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (f128_of_u32 u) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 v) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x1c51c)) fc None m (seg_rom img_segs)).
Lemma floatunsitf_callv_c_ok : floatunsitf_callv_c.
Proof. exact floatunsitf_callv. Qed.


(* [comment removed for export] *)
Lemma sext32_idem : forall z, sext32 (sext32 z) = sext32 z.
Proof. intros. apply sext32_congr. apply sext32_low. Qed.
Lemma floatunsitf_callfix : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (Y : Z),
  mem_inv img_segs m ->
  evt img_segs (leaf2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (f128_of_u32 (f128_to_u32 Y)) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (fixunstfsi_a0 Y)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x1c51c)) fc None m (seg_rom img_segs)).
Proof.
  intros until Y. intros MI. apply floatunsitf_callv; [exact MI | |].
  - unfold fixunstfsi_a0. apply sext32_range.
  - unfold f128_to_u32, M32. rewrite sext32_landM32. unfold fixunstfsi_a0. symmetry. apply sext32_idem.
Qed.

(* [comment removed for export] *)
Definition floatunsitf_callfix_c : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (Y : Z),
  mem_inv img_segs m ->
  evt img_segs (leaf2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (f128_of_u32 (f128_to_u32 Y)) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (fixunstfsi_a0 Y)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x1c51c)) fc None m (seg_rom img_segs)).
Lemma floatunsitf_callfix_c_ok : floatunsitf_callfix_c.
Proof. exact floatunsitf_callfix. Qed.


(* [comment removed for export] *)
Lemma extenddftf2_callv : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (D : Z),
  mem_inv img_segs m -> (0 <= D < 2^64)%Z ->
  evt img_segs (leaf2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (bvmap_set 10 (Z_to_bv 64 D) F) fc (f128_of_d D) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        (bvmap_set 10 (Z_to_bv 64 D) F) (Z_to_bv 64 (sym 0x1af98)) fc None m (seg_rom img_segs)).
Proof.
  intros until D. intros MI HD. eapply evt_mono. { eapply SPEC_extenddftf2. exact MI. }
  intros ms' P. unfold extenddftf2_post in P. rewrite freg_get_same, unsigned_lit in P by lia. exact P.
Qed.

(* [comment removed for export] *)
Definition extenddftf2_callv_c : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (D : Z),
  mem_inv img_segs m -> (0 <= D < 2^64)%Z ->
  evt img_segs (leaf2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (bvmap_set 10 (Z_to_bv 64 D) F) fc (f128_of_d D) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        (bvmap_set 10 (Z_to_bv 64 D) F) (Z_to_bv 64 (sym 0x1af98)) fc None m (seg_rom img_segs)).
Lemma extenddftf2_callv_c_ok : extenddftf2_callv_c.
Proof. exact extenddftf2_callv. Qed.


(* [comment removed for export] *)
Definition call2_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (K : Z) (R : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 R)) (Z_to_bv 64 (hi64 R)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom img_segs)
    /\ munch [(q - K, q)]%Z m m' /\ wmono img_segs m m' /\ mem_inv img_segs m'
    /\ stk img_segs m' (q - K) q.

Lemma multf3_callq : forall ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (q X Y : Z),
  stk img_segs m (q - 80) q -> mem_inv img_segs m -> (4096 <= q < 2^64)%Z ->
  evt img_segs (call2_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 80 (f128_mul X Y) m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x1b3d0)) fc None m (seg_rom img_segs)).
Proof.
  intros until Y. intros ST MI Hq.
  assert (Eq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  eapply evt_mono. { eapply (SPEC_multf3 ra (Z_to_bv 64 q)); rewrite ?Eq; eauto; lia. }
  intros ms' P. unfold multf3_post in P. rewrite !Eq, !ulit_lo64, !ulit_hi64, !mk128_canon, f128_mul_canon in P. exact P.
Qed.

(* [comment removed for export] *)
Definition multf3_callq_c : Prop := forall ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (q X Y : Z),
  stk img_segs m (q - 80) q -> mem_inv img_segs m -> (4096 <= q < 2^64)%Z ->
  evt img_segs (call2_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 80 (f128_mul X Y) m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x1b3d0)) fc None m (seg_rom img_segs)).
Lemma multf3_callq_c_ok : multf3_callq_c.
Proof. exact multf3_callq. Qed.


Lemma divtf3_callq : divtf3_stmt -> forall ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (q X Y : Z),
  stk img_segs m (q - 112) q -> mem_inv img_segs m -> (4096 <= q < 2^64)%Z ->
  evt img_segs (call2_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 112 (f128_div X Y) m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x1c6b0)) fc None m (seg_rom img_segs)).
Proof.
  intros DS. intros until Y. intros ST MI Hq.
  assert (Eq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  eapply evt_mono. { eapply (DS ra (Z_to_bv 64 q)); rewrite ?Eq; eauto; lia. }
  intros ms' P. unfold divtf3_post in P. rewrite !Eq, !ulit_lo64, !ulit_hi64, !mk128_canon, f128_div_canon in P. exact P.
Qed.

(* [comment removed for export] *)
Definition divtf3_callq_c : Prop := divtf3_stmt -> forall ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (q X Y : Z),
  stk img_segs m (q - 112) q -> mem_inv img_segs m -> (4096 <= q < 2^64)%Z ->
  evt img_segs (call2_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 112 (f128_div X Y) m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x1c6b0)) fc None m (seg_rom img_segs)).
Lemma divtf3_callq_c_ok : divtf3_callq_c.
Proof. exact divtf3_callq. Qed.


(* [comment removed for export] *)
Definition calla_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (R : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 fc' m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 R)) (Z_to_bv 64 (hi64 R)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc' None m' (seg_rom img_segs)
    /\ munch [(q - 48, q)]%Z m m' /\ wmono img_segs m m' /\ mem_inv img_segs m'
    /\ frm0 fc'
    /\ stk img_segs m' (q - 48) q.

Lemma addtf3_callq : forall ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (q X Y : Z),
  stk img_segs m (q - 48) q -> mem_inv img_segs m -> frm0 fc -> (48 <= q < 2^64)%Z ->
  evt img_segs (calla_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F (f128_add X Y) m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x1bc80)) fc None m (seg_rom img_segs)).
Proof.
  intros until Y. intros ST MI FRM Hq.
  assert (Eq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  eapply evt_mono. { eapply (SPEC_addtf3_spec ra (Z_to_bv 64 q)); rewrite ?Eq; eauto. }
  intros ms' P. unfold addtf3_post in P. rewrite !Eq, !ulit_lo64, !ulit_hi64 in P.
  change (lo64 X + 2 ^ 64 * hi64 X)%Z with (canon X) in P. change (lo64 Y + 2 ^ 64 * hi64 Y)%Z with (canon Y) in P.
  rewrite f128_add_canon in P. exact P.
Qed.

(* [comment removed for export] *)
Definition addtf3_callq_c : Prop := forall ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (q X Y : Z),
  stk img_segs m (q - 48) q -> mem_inv img_segs m -> frm0 fc -> (48 <= q < 2^64)%Z ->
  evt img_segs (calla_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F (f128_add X Y) m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x1bc80)) fc None m (seg_rom img_segs)).
Lemma addtf3_callq_c_ok : addtf3_callq_c.
Proof. exact addtf3_callq. Qed.


Lemma subtf3_callq : forall ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (q X Y : Z),
  stk img_segs m (q - 48) q -> mem_inv img_segs m -> frm0 fc -> (48 <= q < 2^64)%Z ->
  evt img_segs (calla_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F (f128_sub X Y) m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x1bc70)) fc None m (seg_rom img_segs)).
Proof.
  intros until Y. intros ST MI FRM Hq.
  assert (Eq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  eapply evt_mono. { eapply (SPEC_subtf3 ra (Z_to_bv 64 q)); rewrite ?Eq; eauto. }
  intros ms' P. unfold addtf3_post in P. rewrite !Eq, !ulit_lo64, !ulit_hi64 in P.
  change (lo64 X + 2 ^ 64 * hi64 X)%Z with (canon X) in P. change (lo64 Y + 2 ^ 64 * hi64 Y)%Z with (canon Y) in P.
  rewrite f128_sub_canon in P. exact P.
Qed.

(* [comment removed for export] *)
Definition subtf3_callq_c : Prop := forall ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (q X Y : Z),
  stk img_segs m (q - 48) q -> mem_inv img_segs m -> frm0 fc -> (48 <= q < 2^64)%Z ->
  evt img_segs (calla_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F (f128_sub X Y) m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x1bc70)) fc None m (seg_rom img_segs)).
Lemma subtf3_callq_c_ok : subtf3_callq_c.
Proof. exact subtf3_callq. Qed.


(* [comment removed for export] *)
Definition frexpl_postq (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (P x E : Z) (rest : list cell) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists x' e' t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 x')) (Z_to_bv 64 (hi64 x')) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom img_segs)
    /\ munch [(q - 32, q); (P, P + 4)]%Z m m' /\ wmono img_segs m m' /\ mem_inv img_segs m'
    /\ stk img_segs m' (q - 32) q
    /\ rw_cells img_segs m' P (C4 (Z_to_bv 64 e') :: rest)
    /\ frexpl FREXPL_FUEL x E = Some (x', e').

Lemma frexpl_callq : forall ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (q P X E : Z) (rest : list cell),
  stk img_segs m (q - 32) q -> mem_inv img_segs m ->
  rw_cells img_segs m P (C4 (Z_to_bv 64 E) :: rest) ->
  (P + 4 + Z.of_nat (cells_size rest) <= q - 32 \/ q <= P)%Z -> (32 <= q < 2^64)%Z -> (0 <= P < 2^64)%Z ->
  (Z.land (Z.shiftr (hi64 X) 48) 0x7fff <> 0%Z \/ f128_le X F128_ZERO = 0%Z) ->
  evt img_segs (frexpl_postq ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc P (canon X) E rest m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 P) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x1b174)) fc None m (seg_rom img_segs)).
Proof.
  intros until rest. intros ST MI CE SEP Hq HP PRE.
  assert (Eq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  assert (Ep : bv_unsigned (Z_to_bv 64 P) = P) by (apply unsigned_lit; lia).
  pose proof (rw_cells_bound _ _ _ _ CE) as BR. cbn [cells_size csize] in BR.
  apply (proj1 (rw_cells_app img_segs _ _ [_] _)) in CE. destruct CE as [CE CR]. cbn [cells_size csize Nat.add] in CR.
  change (Z.of_nat 4) with 4%Z in CR.
  eapply evt_mono.
  { eapply (SPEC_frexpl ra (Z_to_bv 64 q)); rewrite ?Eq, ?Ep, ?ulit_lo64, ?ulit_hi64; eauto; try lia.
    cbv zeta. change (lo64 X + 2 ^ 64 * hi64 X)%Z with (canon X). rewrite hi64_canon.
    unfold F128_ZERO in *. rewrite <- (f128_le_canon X 0) in PRE. replace (canon 0) with 0%Z in PRE by reflexivity. exact PRE. }
  intros ms' Q. unfold frexpl_post in Q. rewrite !Eq, !Ep, !ulit_lo64, !ulit_hi64 in Q.
  (nelim Q 23%nat; intros x' e' t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' -> MU WM MI' ST' CE' HF).
  unfold frexpl_postq. exists x', e'. repeat (lazymatch goal with |- ex _ => eexists end).
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|]. split; [|exact HF].
  apply (proj2 (rw_cells_app img_segs _ _ [_] _)). split; [exact CE'|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 4) with 4%Z.
  eapply rw_cells_transport; [exact CR | exact MU | exact WM |]. cbn [disjoint_from]. split; [lia|]. split; [lia|exact I].
Qed.

(* [comment removed for export] *)
Definition frexpl_callq_c : Prop := forall ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (q P X E : Z) (rest : list cell),
  stk img_segs m (q - 32) q -> mem_inv img_segs m ->
  rw_cells img_segs m P (C4 (Z_to_bv 64 E) :: rest) ->
  (P + 4 + Z.of_nat (cells_size rest) <= q - 32 \/ q <= P)%Z -> (32 <= q < 2^64)%Z -> (0 <= P < 2^64)%Z ->
  (Z.land (Z.shiftr (hi64 X) 48) 0x7fff <> 0%Z \/ f128_le X F128_ZERO = 0%Z) ->
  evt img_segs (frexpl_postq ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc P (canon X) E rest m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 P) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x1b174)) fc None m (seg_rom img_segs)).
Lemma frexpl_callq_c_ok : frexpl_callq_c.
Proof. exact frexpl_callq. Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma signbitl_canon : forall x, signbitl (canon x) = signbitl x.
Proof. intros. unfold signbitl. rewrite hi64_canon. reflexivity. Qed.
Lemma fpclassifyl_canon : forall x, fpclassifyl (canon x) = fpclassifyl x.
Proof. intros. unfold fpclassifyl. rewrite lo64_canon, hi64_canon. reflexivity. Qed.

Definition signbitl_postv (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (r : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' =>
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom img_segs)
    /\ munch [] m m /\ wmono img_segs m m /\ mem_inv img_segs m.
Lemma signbitl_callv : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (X : Z),
  mem_inv img_segs m ->
  evt img_segs (signbitl_postv ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (hi64 X)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc (signbitl X) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x1b128)) fc None m (seg_rom img_segs)).
Proof.
  intros until X. intros MI. eapply evt_mono. { eapply SPEC_signbitl. exact MI. }
  intros ms' P. unfold signbitl_post, signbitl_postv in *. rewrite !ulit_lo64, !ulit_hi64 in P.
  change (lo64 X + 2 ^ 64 * hi64 X)%Z with (canon X) in P. rewrite signbitl_canon in P. exact P.
Qed.

(* [comment removed for export] *)
Definition signbitl_callv_c : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (X : Z),
  mem_inv img_segs m ->
  evt img_segs (signbitl_postv ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (hi64 X)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc (signbitl X) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x1b128)) fc None m (seg_rom img_segs)).
Lemma signbitl_callv_c_ok : signbitl_callv_c.
Proof. exact signbitl_callv. Qed.


Definition fpclassifyl_postv (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (r : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists a1 a2 a3,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom img_segs)
    /\ munch [] m m /\ wmono img_segs m m /\ mem_inv img_segs m.
Lemma fpclassifyl_callv : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (X : Z),
  mem_inv img_segs m ->
  evt img_segs (fpclassifyl_postv ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc (fpclassifyl X) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x1b130)) fc None m (seg_rom img_segs)).
Proof.
  intros until X. intros MI. eapply evt_mono. { eapply SPEC_fpclassifyl. exact MI. }
  intros ms' P. unfold fpclassifyl_post, fpclassifyl_postv in *. rewrite !ulit_lo64, !ulit_hi64 in P.
  change (lo64 X + 2 ^ 64 * hi64 X)%Z with (canon X) in P. rewrite fpclassifyl_canon in P. exact P.
Qed.

(* [comment removed for export] *)
Definition fpclassifyl_callv_c : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (X : Z),
  mem_inv img_segs m ->
  evt img_segs (fpclassifyl_postv ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc (fpclassifyl X) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x1b130)) fc None m (seg_rom img_segs)).
Lemma fpclassifyl_callv_c_ok : fpclassifyl_callv_c.
Proof. exact fpclassifyl_callv. Qed.


(* [comment removed for export] *)
Lemma lo64_flip_sign : forall x, lo64 (Z.lxor x F128_SIGNBIT) = lo64 x.
Proof.
  intros. unfold lo64, wrap64, ONES64, F128_SIGNBIT. change 18446744073709551615%Z with (Z.ones 64).
  change 0x80000000000000000000000000000000%Z with (2^127)%Z.
  apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec.
  destruct (Z.lt_ge_cases i 64).
  - rewrite Z.lxor_spec, Z.pow2_bits_eqb by lia. destruct (Z.eqb_spec 127 i); [lia|]. now rewrite Bool.xorb_false_r.
  - rewrite Z.ones_spec_high by lia. now rewrite !Bool.andb_false_r.
Qed.
Lemma hi64_flip_sign : forall x, hi64 (Z.lxor x F128_SIGNBIT) = Z.lxor (hi64 x) 9223372036854775808.
Proof.
  intros. unfold hi64, wrap64, ONES64, F128_SIGNBIT. change 18446744073709551615%Z with (Z.ones 64).
  change 0x80000000000000000000000000000000%Z with (2^127)%Z. change 9223372036854775808%Z with (2^63)%Z.
  apply Z.bits_inj'. intros i Hi. rewrite Z.lxor_spec, !Z.land_spec, !Z.shiftr_spec, Z.lxor_spec, !Z.pow2_bits_eqb by lia.
  destruct (Z.lt_ge_cases i 64).
  - rewrite Z.ones_spec_low by lia. rewrite !Bool.andb_true_r.
    destruct (Z.eqb_spec 127 (i + 64)), (Z.eqb_spec 63 i); try lia; reflexivity.
  - rewrite Z.ones_spec_high by lia. rewrite !Bool.andb_false_r. destruct (Z.eqb_spec 63 i); [lia|reflexivity].
Qed.

End Img.
(* [comment removed for export] *)
Ltac norm_rsegs := idtac.

(* [comment removed for export] *)
Existing Class letf2_callv_c.
Existing Class letf2_callv0_c.
Existing Class fixunstfsi_callv_c.
Existing Class floatsitf_callv_c.
Existing Class floatsitf_callp_c.
Existing Class floatunsitf_callv_c.
Existing Class floatunsitf_callfix_c.
Existing Class extenddftf2_callv_c.
Existing Class multf3_callq_c.
Existing Class divtf3_callq_c.
Existing Class addtf3_callq_c.
Existing Class subtf3_callq_c.
Existing Class frexpl_callq_c.
Existing Class signbitl_callv_c.
Existing Class fpclassifyl_callv_c.
End G_fmt_fp_calls.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib Require Import SFModel Arr.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Spec Require Import Prelim SoftFloat FmtFp.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.P Require Import SFW1_lemmas.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.G Require Import G_fwritex G_pad.
Import G_fmt_fp_calls.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc Require RProgAt.
Import OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
 From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib Require Import NElim. From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc Require RegFold. From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc Require JunkAbs.
Import ListNotations.
Open Scope bv_scope.


(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Step.step2_with rp rpm vh ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_with rp rpm vh.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.SysStep.step_ecall ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.astep_ecall.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Step.solve_load ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_load.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Step.solve_cond ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_cond.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Step.step ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Step.stepz ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Step.stepz_fast ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_fast.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.SysStep.sys_nret ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.asys_nret.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Tac.post_call segs m ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.apost_call segs m.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Step.simp_regs ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RegFold.simp_regs_f.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.JunkAbs.split_for_access_abs H segs m A cs kn n.
Section Img.
  Context {IMG : RImg}.
  Collection ImgHyps := IMG.



(* [comment removed for export] *)
Ltac hyp :=
  lazymatch goal with
  | |- rw_cells _ ?m ?A ?cs =>
      match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
  | |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
  end.
Ltac showregs := let x10 := getreg 10%Z in let x11 := getreg 11%Z in let x12 := getreg 12%Z in let x13 := getreg 13%Z in let x14 := getreg 14%Z in let x15 := getreg 15%Z in let x16 := getreg 16%Z in let x17 := getreg 17%Z in let x5 := getreg 5%Z in let x6 := getreg 6%Z in let x7 := getreg 7%Z in let x8 := getreg 8%Z in let x9 := getreg 9%Z in let x18 := getreg 18%Z in let x19 := getreg 19%Z in let x20 := getreg 20%Z in let x21 := getreg 21%Z in let x22 := getreg 22%Z in let x23 := getreg 23%Z in let x24 := getreg 24%Z in let x25 := getreg 25%Z in let x26 := getreg 26%Z in let x27 := getreg 27%Z in let x2 := getreg 2%Z in
    idtac "a0=" x10; idtac "a1=" x11; idtac "a2=" x12; idtac "a3=" x13; idtac "a4=" x14; idtac "a5=" x15; idtac "a6=" x16; idtac "a7=" x17; idtac "t0=" x5; idtac "t1=" x6; idtac "t2=" x7; idtac "s0=" x8; idtac "s1=" x9; idtac "s2=" x18; idtac "s3=" x19; idtac "s4=" x20; idtac "s5=" x21; idtac "s6=" x22; idtac "s7=" x23; idtac "s8=" x24; idtac "s9=" x25; idtac "s10=" x26; idtac "s11=" x27; idtac "sp=" x2.

(* [comment removed for export] *)
Lemma le8_lit : forall z, (0 <= z < 2^64)%Z -> Z_to_le_bytes 8 z = le8 (Z_to_bv 64 z).
Proof. intros z Hz. rewrite <- store_bytes_8'. rewrite unsigned_lit by lia. reflexivity. Qed.
Lemma le4_lit : forall z, (0 <= z < 2^64)%Z -> Z_to_le_bytes 4 z = le4 (Z_to_bv 64 z).
Proof. intros z Hz. unfold le4. rewrite unsigned_lit by lia. reflexivity. Qed.
Ltac fix_litstore :=
  match goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
  | _ => idtac
  end.
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac zstep0 := zs.

(* [comment removed for export] *)
Ltac name_cb n H := match type of H with context [CB n ?l] => let j := fresh "jk" in set (j := l) in H; clearbody j end.

(* [comment removed for export] *)
Lemma shl52_land64 : forall f, (0 <= f)%Z -> Z.land (Z.shiftl f 52) 18446744073709551615 = (4503599627370496 * (f mod 4096))%Z.
Proof.
  intros f Hf. rewrite land_W64, Z.shiftl_mul_pow2 by lia. change (2^64)%Z with (4503599627370496 * 4096)%Z.
  change (2^52)%Z with 4503599627370496%Z. rewrite Z.mul_comm, Z.mul_mod_distr_l by lia. reflexivity.
Qed.
Lemma land_bit11 : forall f, Z.land f 2048 = (2048 * ((f / 2048) mod 2))%Z.
Proof. intros. change 2048%Z with (2^11)%Z. rewrite zb_land_pow2 by lia. reflexivity. Qed.
Lemma land_bit0 : forall f, Z.land f 1 = (f mod 2)%Z.
Proof. intros. change 1%Z with (2^1 - 1)%Z. rewrite zb_land_mask by lia. reflexivity. Qed.

Lemma signbitl_range : forall x, (0 <= signbitl x <= 1)%Z.
Proof.
  intros. unfold signbitl. pose proof (hi64_range x). rewrite Z.shiftr_div_pow2 by lia.
  split; [apply Z.div_pos; lia|]. apply Z.lt_succ_r. apply Z.div_lt_upper_bound; lia.
Qed.

Lemma fpclassifyl_range : forall x, (0 <= fpclassifyl x <= 4)%Z.
Proof. intros. unfold fpclassifyl. repeat match goal with |- context [if ?c then _ else _] => destruct c end; lia. Qed.

(* [comment removed for export] *)
Lemma sx32_lit : forall e, (-2^31 <= e < 2^31)%Z -> sx32 (Z_to_bv 64 e) = Z_to_bv 64 e.
Proof.
  intros e He. unfold sx32. apply Z_to_bv_eqm. rewrite unsigned_lit_wrap, swrap32_eq.
  change (2^64)%Z with 18446744073709551616%Z. Z.div_mod_to_equations. nia.
Qed.

(* [comment removed for export] *)
Ltac unwrapK K := rewrite ?land_W64 in K; change (2^64)%Z with 18446744073709551616%Z in K.
Ltac mlia := Z.div_mod_to_equations; lia.
Ltac dlia := first [lia | match goal with |- ?g => idtac "LIA FAILED:"; idtac g; fail 1 end].

Lemma fother : forall (F : bvmap 5 word) (v : word) (k : reg),
  bv_unsigned k <> 10%Z -> reg_get (bvmap_set 10 v F) k = reg_get F k.
Proof.
  intros F v k Hk. apply freg_get_other. unfold bv_eqb. apply Z.eqb_neq.
  change (bv_unsigned (10 : reg)) with 10%Z. lia.
Qed.

(* [comment removed for export] *)
Definition zb (l : list Z) : list byte := map (fun z => Z_to_bv 8 z) l.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bytes_le_to_Z_range : forall bs : list byte, (0 <= bytes_le_to_Z bs < 2^(8 * Z.of_nat (length bs)))%Z.
Proof.
  induction bs as [|b bs IH]; cbn [bytes_le_to_Z length]; [cbn; lia|].
  pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2^Z.of_N 8)%Z with (2^8)%Z in Hb.
  assert (Hs : (0 <= Z.shiftl (bytes_le_to_Z bs) 8)%Z) by (apply Z.shiftl_nonneg; lia).
  split. { apply Z.lor_nonneg. lia. }
  pose proof (Z.add_lor_land (bv_unsigned b) (Z.shiftl (bytes_le_to_Z bs) 8)) as E.
  pose proof (Z.land_nonneg (bv_unsigned b) (Z.shiftl (bytes_le_to_Z bs) 8)) as L.
  rewrite Z.shiftl_mul_pow2 in * by lia.
  replace (2 ^ (8 * Z.of_nat (S (length bs))))%Z with (2^8 * 2 ^ (8 * Z.of_nat (length bs)))%Z.
  2:{ rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  nia.
Qed.

Lemma Z_to_le_bytes_to_Z : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2^Z.of_N 8)%Z with (2^8)%Z in Hb.
  pose proof (bytes_le_to_Z_range bs) as HR.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 ?z) with (z mod 2^8)%Z.
    rewrite <- Z.land_ones by lia. rewrite Z.land_lor_distr_l.
    replace (Z.land (Z.shiftl (bytes_le_to_Z bs) 8) (Z.ones 8)) with 0%Z.
    2:{ symmetry. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
        destruct (Z.ltb_spec0 i 8).
        - rewrite Z.shiftl_spec_low by lia. reflexivity.
        - rewrite Z.ones_spec_high by lia. apply andb_false_r. }
    rewrite Z.lor_0_r, Z.land_ones by lia. apply Z.mod_small. lia.
  - rewrite Z.shiftr_lor, Z.shiftr_shiftl_l, Z.sub_diag, Z.shiftl_0_r by lia.
    rewrite (Z.shiftr_div_pow2 _ 8), Z.div_small by lia.
    rewrite Z.lor_0_l. exact IH.
Qed.

Lemma le4_of_bytes : forall bs : list byte, length bs = 4%nat -> le4 (le_bytes_to_word bs) = bs.
Proof.
  intros bs HL. unfold le4, le_bytes_to_word.
  pose proof (bytes_le_to_Z_range bs) as HR. rewrite HL in HR. change (2 ^ (8 * Z.of_nat 4))%Z with (2^32)%Z in HR.
  rewrite unsigned_lit by lia. rewrite <- HL. apply Z_to_le_bytes_to_Z.
Qed.

Lemma u32arr_of_u8arr : forall segs m A bs k,
  u8arr segs m A bs -> length bs = (4 * k)%nat ->
  exists ws, length ws = k /\ u32arr segs m A ws.
Proof.
  intros segs m A bs k [Hb Hw] HL.
  assert (G : forall k bs, length bs = (4 * k)%nat -> exists ws, length ws = k /\ u32s ws = bs).
  { clear. induction k as [|k IH]; intros bs HL.
    - exists []. destruct bs; [split; reflexivity| cbn in HL; lia].
    - (nelim (IH (skipn 4 bs) ltac:(rewrite length_skipn; lia)) 3%nat; intros ws Hlen Hu).
      exists (le_bytes_to_word (firstn 4 bs) :: ws). split; [cbn; lia|].
      cbn [u32s]. rewrite Hu, le4_of_bytes by (rewrite length_firstn; lia). apply firstn_skipn. }
  (nelim (G k bs HL) 3%nat; intros ws Hlen Hu). exists ws. split; [exact Hlen|]. split.
  - rewrite Hu. exact Hb.
  - rewrite Hlen. replace (4 * Z.of_nat k)%Z with (Z.of_nat (length bs)) by lia. exact Hw.
Qed.

Lemma u8arr_of_u32arr : forall segs m A ws, u32arr segs m A ws -> u8arr segs m A (u32s ws).
Proof. intros segs m A ws [Hb Hw]. split; [exact Hb|]. rewrite u32s_length. replace (Z.of_nat (4 * length ws)) with (4 * Z.of_nat (length ws))%Z by lia. exact Hw. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition wnth (ws : list word) (i : Z) : word := nth (Z.to_nat i) ws (Z_to_bv 64 0).
Definition wval (ws : list word) (i : Z) : Z := (bv_unsigned (wnth ws i) mod 4294967296)%Z.

Lemma nth_error_wnth : forall ws i, (0 <= i)%Z -> (Z.to_nat i < length ws)%nat -> nth_error ws (Z.to_nat i) = Some (wnth ws i).
Proof. intros ws i Hi Hl. unfold wnth. apply nth_error_nth'. exact Hl. Qed.

Lemma wval_upd_same : forall ws i v, (0 <= i)%Z -> (Z.to_nat i < length ws)%nat ->
  wval (upd ws (Z.to_nat i) v) i = (bv_unsigned v mod 4294967296)%Z.
Proof.
  intros ws i v Hi Hl. unfold wval, wnth.
  pose proof (nth_error_upd_same ws (Z.to_nat i) v Hl) as E.
  apply nth_error_nth with (d := Z_to_bv 64 0) in E. rewrite E. reflexivity.
Qed.
Lemma wval_upd_other : forall ws i j v, (0 <= i)%Z -> (0 <= j)%Z -> i <> j ->
  wval (upd ws (Z.to_nat i) v) j = wval ws j.
Proof.
  intros ws i j v Hi Hj Hij. unfold wval, wnth.
  destruct (Nat.lt_ge_cases (Z.to_nat j) (length ws)) as [Hl|Hl].
  - pose proof (nth_error_upd_other ws (Z.to_nat i) (Z.to_nat j) v ltac:(lia)) as E.
    rewrite (nth_error_nth' ws (Z_to_bv 64 0) Hl) in E.
    apply nth_error_nth with (d := Z_to_bv 64 0) in E. rewrite E. reflexivity.
  - rewrite !nth_overflow by (rewrite ?upd_length; lia). reflexivity.
Qed.
Lemma wval_range : forall ws i, (0 <= wval ws i < 4294967296)%Z.
Proof. intros. unfold wval. apply Z.mod_pos_bound. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma div1e9_magic : forall x, (0 <= x < 2^64)%Z ->
  Z.shiftr (Z.shiftr (Z.shiftr x 9 * 19342813113834067) 64) 11 = (x / 1000000000)%Z.
Proof.
  intros x Hx. rewrite !Z.shiftr_div_pow2 by lia. rewrite Z.div_div by lia.
  change (2^64 * 2^11)%Z with (2^75)%Z. change 1000000000%Z with (512 * 1953125)%Z. rewrite <- Z.div_div by lia.
  change (2^9)%Z with 512%Z.
  set (y := (x / 512)%Z). assert (Hy : (0 <= y < 2^55)%Z) by (subst y; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  clearbody y. clear x Hx.
  Z.div_mod_to_equations. nia.
Qed.

Lemma sx32_zero : forall w : word, bv_unsigned (sx32 w) = 0%Z <-> (bv_unsigned w mod 4294967296 = 0)%Z.
Proof.
  intros w. unfold sx32. rewrite unsigned_lit_wrap, swrap32_eq. pose proof (bv_unsigned_in_range 64 w) as R.
  unfold bv_modulus in R. change (2^64)%Z with 18446744073709551616%Z in *. change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z in R.
  split; intros H; Z.div_mod_to_equations; lia.
Qed.
Lemma sx32_nonzero : forall w : word, bv_unsigned (sx32 w) <> 0%Z <-> (bv_unsigned w mod 4294967296 <> 0)%Z.
Proof. intros w. rewrite sx32_zero. tauto. Qed.

Lemma mulhu_M_range : forall x, (0 <= x < 2^62)%Z ->
  (0 <= Z.shiftr (Z.shiftr x 9 * 19342813113834067) 64 < 18446744073709551616)%Z.
Proof.
  intros x Hx. rewrite !Z.shiftr_div_pow2 by lia.
  split. { apply Z.div_pos; [|lia]. apply Z.mul_nonneg_nonneg; [apply Z.div_pos; lia| lia]. }
  apply Z.div_lt_upper_bound; [lia|].
  assert (x / 2^9 < 2^53)%Z by (apply Z.div_lt_upper_bound; lia). 
  assert (0 <= x / 2^9)%Z by (apply Z.div_pos; lia). nia.
Qed.

End Img.
(* [comment removed for export] *)
Ltac hyp :=
  lazymatch goal with
  | |- rw_cells _ ?m ?A ?cs =>
      match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
  | |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
  end.
Ltac showregs := let x10 := getreg 10%Z in let x11 := getreg 11%Z in let x12 := getreg 12%Z in let x13 := getreg 13%Z in let x14 := getreg 14%Z in let x15 := getreg 15%Z in let x16 := getreg 16%Z in let x17 := getreg 17%Z in let x5 := getreg 5%Z in let x6 := getreg 6%Z in let x7 := getreg 7%Z in let x8 := getreg 8%Z in let x9 := getreg 9%Z in let x18 := getreg 18%Z in let x19 := getreg 19%Z in let x20 := getreg 20%Z in let x21 := getreg 21%Z in let x22 := getreg 22%Z in let x23 := getreg 23%Z in let x24 := getreg 24%Z in let x25 := getreg 25%Z in let x26 := getreg 26%Z in let x27 := getreg 27%Z in let x2 := getreg 2%Z in
    idtac "a0=" x10; idtac "a1=" x11; idtac "a2=" x12; idtac "a3=" x13; idtac "a4=" x14; idtac "a5=" x15; idtac "a6=" x16; idtac "a7=" x17; idtac "t0=" x5; idtac "t1=" x6; idtac "t2=" x7; idtac "s0=" x8; idtac "s1=" x9; idtac "s2=" x18; idtac "s3=" x19; idtac "s4=" x20; idtac "s5=" x21; idtac "s6=" x22; idtac "s7=" x23; idtac "s8=" x24; idtac "s9=" x25; idtac "s10=" x26; idtac "s11=" x27; idtac "sp=" x2.
Ltac fix_litstore :=
  match goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
  | _ => idtac
  end.
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac zstep0 := zs.
Ltac name_cb n H := match type of H with context [CB n ?l] => let j := fresh "jk" in set (j := l) in H; clearbody j end.
Ltac unwrapK K := rewrite ?land_W64 in K; change (2^64)%Z with 18446744073709551616%Z in K.
Ltac mlia := Z.div_mod_to_equations; lia.
Ltac dlia := first [lia | match goal with |- ?g => idtac "LIA FAILED:"; idtac g; fail 1 end].
