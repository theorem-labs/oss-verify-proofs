(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cjson/cjson_read_fuzzer/lib/P/F_floatsitf.v, with its module paths and module names changed; 140 of its 157 lines of code are new or changed and 38 lines of the source are left out. *)
(* The RL walk of __extendsftf2 (binary32 -> binary128): from the entry, the code returns the 128-bit value
   f128_of_f32 (fa0) of C_extendsftf2.v. The value is kept behind a name (RES) while the code is stepped; each register
   that the mirror names is matched to the mirror's let (the or-cascade, the 32-bit popcount, the shift and the
   exponent), with two bridges where the code's form differs from the mirror's: slti sh, 0 is b2z (is_neg64 sh), and
   (0x3f80 - clz) + 9 is the same word as add64 (sub64 0x3f80 clz) 9. At each of the four returns (zero, subnormal,
   normal, infinity or NaN) the mirror is unfolded, its tests are decided by the branch hypotheses, and its high word
   is the a1 register by conversion; the low word is a0 = 0. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.Spec Require Import SoftFloat.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.P Require Import SFW1_lemmas.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.RL.Reloc Require RProgAt.
Import OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.RL.Reloc.RProgAt.RTac. From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.RL.Reloc Require Import RProgNotJ. From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.RL.Reloc Require Import RProgNot. From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.RL.Reloc Require RegFold. From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.RL.Reloc Require RProgAt. From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.RL.Reloc Require JunkAbs.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.RL.G Require Import C_extendsftf2.
Import ListNotations.
Open Scope bv_scope.

From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.P Require F_sf_helpers2.
Import OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.P.F_sf_helpers2.SF_buildtac.
From Stdlib Require Import Zify Lia.

(* The stepping tactics run on the relocatable program tree (RProgAt) instead of a fixed image. *)
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.Lib.Step.step2_with rp rpm vh ::= OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_with rp rpm vh.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.Lib.SysStep.step_ecall ::= OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.RL.Reloc.RProgAt.RTac.astep_ecall.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.Lib.Step.solve_load ::= OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_load.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.Lib.Step.solve_cond ::= OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_cond.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.Lib.Step.step ::= OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.Lib.Step.stepz ::= OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.Lib.Step.stepz_fast ::= OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_fast.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.Lib.SysStep.sys_nret ::= OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.RL.Reloc.RProgAt.RTac.asys_nret.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.Lib.Tac.post_call segs m ::= OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.RL.Reloc.RProgAt.RTac.apost_call segs m.

(* Register writes are folded as they are made; the instruction at a pc is found in the tree by its offset. *)
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.Lib.Step.simp_regs ::= OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.RL.Reloc.RegFold.simp_regs_f.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.RL.Reloc.RProgAt.RTac.find_t_eval k t ::= OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.RL.Reloc.RProgAt.find_t_eval_at k t.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.RL.Reloc.JunkAbs.split_for_access_abs H segs m A cs kn n.

(* slti a3, sh, 0 (the sign of the 64-bit word sh) as the step writes it, and as the mirror writes it. *)
Lemma slti0_bridge : forall s, (0 <= s < 18446744073709551616)%Z ->
  b2z (is_neg64 s) = Z.b2z (Z.lxor s 9223372036854775808 <? 0 + 9223372036854775808)%Z.
Proof.
  intros s Hs. unfold b2z, is_neg64.
  rewrite (Z.shiftr_div_pow2 s 63) by lia.
  change (Z.lxor s 9223372036854775808) with (Z.lxor s (2^63)).
  rewrite (zb_lxor_pow2 s 63) by lia.
  change (2^63)%Z with 9223372036854775808%Z.
  destruct (Z.lt_ge_cases s 9223372036854775808) as [Hl|Hl].
  - rewrite (Z.div_small s 9223372036854775808) by lia.
    change (0 mod 2)%Z with 0%Z.
    replace (s + 9223372036854775808 - 2 * 9223372036854775808 * 0 <? 0 + 9223372036854775808)%Z with false
      by (symmetry; apply Z.ltb_ge; lia).
    reflexivity.
  - replace (s / 9223372036854775808)%Z with 1%Z
      by (apply Z.div_unique with (s - 9223372036854775808)%Z; lia).
    change (1 mod 2)%Z with 1%Z.
    replace (s + 9223372036854775808 - 2 * 9223372036854775808 * 1 <? 0 + 9223372036854775808)%Z with true
      by (symmetry; apply Z.ltb_lt; lia).
    reflexivity.
Qed.

(* addi a3, a4, 9 with a4 = 0x3f80 - clz: the code adds to the unwrapped difference, the mirror to its wrap64. *)
Lemma dexp_bridge : forall c,
  Z_to_bv 64 (Z.land (Z.land (16256 - c) 18446744073709551615 + 9) 18446744073709551615) = Z_to_bv 64 (16256 - c + 9).
Proof.
  intros c. apply Z_to_bv_eqm. rewrite !land_W64. change (2^64)%Z with 18446744073709551616%Z.
  Z.div_mod_to_equations. lia.
Qed.

Section Img.
  Context {IMG : RImg}.
  Context {CODE_extendsftf2 : CodeAtT img_segs (sym 0x200dc) (PROGAT_CODE_extendsftf2 IMG)}.
  Context {RB_extendsftf2 : RelCode (sym 0x200dc) 348}.
  Collection ImgHyps := IMG CODE_extendsftf2 RB_extendsftf2.

Local Ltac Lia.lia ::= Zify.zify; xlia zchecker.
(* Division facts are not needed by the arithmetic of this walk; the cleanup pass only costs time. *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac flia ::= flia_fast.
Local Ltac blia ::= blia_fast.
Local Ltac step ::= step_fast. Local Ltac stepz ::= stepz_fast.
Local Ltac zsimp ::= zsimp_fast.

Lemma extendsftf2_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  mem_inv img_segs m ->
  evt img_segs (extendsftf2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               (f128_of_f32 (bv_unsigned (reg_get F 10))) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x200dc)) fc None m (seg_rom img_segs)).
(* The statement takes all three image hypotheses (the contract is used with the code and its relocation bound). *)
Proof using ImgHyps.
  intros until m. intros MI.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl img_segs m) as WM.
  remember (f128_of_f32 (bv_unsigned (reg_get F 10))) as RES eqn:HRES.
  (* +0 fmv.x.w a1, fa0: a1 = sext32 of the low 32 bits of fa0. *)
  zstep. remember (reg_get F 10) as dw eqn:Edw.
  assert (Rdw : (0 <= bv_unsigned dw < 2^64)%Z) by apply (zr_word dw).
  unfold sx32. rewrite Z_to_bv_swrap32.
  name_as_by a1v (sext32 (bv_unsigned dw)) (apply sext32_range).
  (* +4 srliw a0, a1, 23 *)
  wstep. model_reg_w 10%Z sr23 (srliw a1v 23).
  (* +8 slli a2, a1, 41 (named, so that +16 stays the mirror's shr64 (shl64 a1 41) 41) *)
  zstep. name_reg 12%Z t41.
  (* +12 andi a3, a0, 255: the exponent; +16 srli a2, a2, 41: the fraction *)
  zstep. name_reg 13%Z aE.
  zstep. name_reg 12%Z aS.
  (* +20 beqz aE -> +72 *)
  zstep. if_cases K0; zify_cond K0.
  - (* +72 a0 = 0; +76 beqz aS -> +324 *)
    zstep. zstep. if_cases K2; zify_cond K2.
    + (* zero: +324 .. +344, the signed zero. *)
      do 6 zstep. name_reg 11%Z HI.
      assert (EH : f128_of_f32 (bv_unsigned dw) = mk128 HI 0).
      { unfold f128_of_f32. cbv beta zeta.
        destruct (Z.eqb_spec (Z.land (srliw (sext32 (bv_unsigned dw)) 23) 255) 0) as [E0|E0];
          [ | exfalso; exact (E0 K0) ].
        destruct (Z.eqb_spec (Z.shiftr (shl64 (sext32 (bv_unsigned dw)) 41) 41) 0) as [E2|E2];
          [ | exfalso; exact (E2 K2) ].
        reflexivity. }
      rewrite HRES, EH. sf_finish.
    + (* subnormal: +80 .. +128 the or-cascade *)
      zstep. zstep. model_reg 13%Z x1 (Z.lor aS (Z.shiftr aS 1)).
      zstep. zstep. model_reg 13%Z x2 (Z.lor x1 (Z.shiftr x1 2)).
      zstep. zstep. model_reg 13%Z x3 (Z.lor x2 (Z.shiftr x2 4)).
      zstep. zstep. zstep. model_reg 13%Z x4 (Z.lor x3 (Z.shiftr (Z.land (Z.shiftl x3 41) W64) 49)).
      zstep. zstep.
      zstep. zstep. model_reg 13%Z x5 (Z.lor x4 (Z.shiftr (Z.land (Z.shiftl x3 41) W64) 57)).
      (* +132 not; +136 .. +212 the 32-bit popcount, clz *)
      zstep. model_reg 13%Z y (Z.lxor x5 W64).
      zstep. zstep. zstep. zstep.
      zstep. model_reg 13%Z c1 (Z.land (y - Z.land (Z.shiftr y 1) 1431655765) W64).
      zstep. zstep. zstep. zstep. model_reg 13%Z c2 (Z.land (Z.land c1 858993459 + Z.land (Z.shiftr c1 2) 858993459) W64).
      zstep. zstep. zstep. zstep. zstep. model_reg 13%Z c3 (Z.land (Z.land (c2 + Z.shiftr c2 4) W64) 252645135).
      zstep. zstep. zstep. zstep. zstep.
      wstep. model_reg_w 13%Z clz (srliw (Z.land (c3 * 16843009) W64) 24).
      (* +216 a4 = 0x3f80 - clz; +220 sh = clz + 17; +224 aS << sh; +228 .. +236 the mask of sh < 0 *)
      zstep. zstep. model_reg 13%Z sh (Z.land (clz + 17) W64).
      zstep. zstep.
      replace (Z_to_bv 64 (Z.b2z (Z.lxor sh 9223372036854775808 <? 0 + 9223372036854775808))%Z)
        with (Z_to_bv 64 (b2z (is_neg64 sh))) by (f_equal; apply slti0_bridge; exact Rsh).
      name_as_by ng (b2z (is_neg64 sh)) (unfold b2z; destruct (is_neg64 sh); lia).
      zstep. model_reg 13%Z msk (Z.land (ng - 1) W64).
      zstep. model_reg 12%Z sg (Z.land msk (Z.land (Z.shiftl aS (Z.land sh 63)) W64)).
      (* +240 a5 = 1; +244 the exponent (0x3f80 - clz) + 9 *)
      zstep. zstep.
      replace (Z_to_bv 64 (16256 - clz + 9)%Z)
        with (Z_to_bv 64 (Z.land (Z.land (16256 - clz) W64 + 9) W64)) by apply dexp_bridge.
      name_as dE (Z.land (Z.land (16256 - clz) W64 + 9) W64).
      (* +248 .. +276: the leading one cleared, the sign and the exponent ORed in, ret *)
      do 8 zstep. name_reg 11%Z HI.
      assert (EH : f128_of_f32 (bv_unsigned dw) = mk128 HI 0).
      { unfold f128_of_f32. cbv beta zeta.
        destruct (Z.eqb_spec (Z.land (srliw (sext32 (bv_unsigned dw)) 23) 255) 0) as [E0|E0];
          [ | exfalso; exact (E0 K0) ].
        destruct (Z.eqb_spec (Z.shiftr (shl64 (sext32 (bv_unsigned dw)) 41) 41) 0) as [E2|E2];
          [ exfalso; exact (K2 E2) | ].
        reflexivity. }
      rewrite HRES, EH. sf_finish.
  - (* +24 a0 = 255; +28 bne aE, a0 -> +280 *)
    zstep. zstep. if_cases K1; zify_cond K1.
    + (* normal: +280 .. +320 *)
      do 11 zstep. name_reg 11%Z HI.
      assert (EH : f128_of_f32 (bv_unsigned dw) = mk128 HI 0).
      { unfold f128_of_f32. cbv beta zeta.
        destruct (Z.eqb_spec (Z.land (srliw (sext32 (bv_unsigned dw)) 23) 255) 0) as [E0|E0];
          [ exfalso; exact (K0 E0) | ].
        destruct (Z.eqb_spec (Z.land (srliw (sext32 (bv_unsigned dw)) 23) 255) 255) as [E1|E1];
          [ exfalso; exact (K1 E1) | ].
        reflexivity. }
      rewrite HRES, EH. sf_finish.
    + (* infinity or NaN: +32 .. +68 *)
      do 10 zstep. name_reg 11%Z HI.
      assert (EH : f128_of_f32 (bv_unsigned dw) = mk128 HI 0).
      { unfold f128_of_f32. cbv beta zeta.
        destruct (Z.eqb_spec (Z.land (srliw (sext32 (bv_unsigned dw)) 23) 255) 0) as [E0|E0];
          [ exfalso; exact (K0 E0) | ].
        destruct (Z.eqb_spec (Z.land (srliw (sext32 (bv_unsigned dw)) 23) 255) 255) as [E1|E1];
          [ | exfalso; exact (E1 K1) ].
        reflexivity. }
      rewrite HRES, EH. sf_finish.
Qed.

Lemma extendsftf2_contract_ok : extendsftf2_contract.
Proof. exact extendsftf2_spec. Qed.

End Img.
