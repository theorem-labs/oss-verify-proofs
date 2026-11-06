(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cjson/cjson_read_fuzzer/lib/RL/G/G_floatsitf.v, with its module paths, addresses and numbers changed; 50 of its 105 lines of code are new or changed and 146 lines of the source are left out. *)
(* The RL walk of __floatditf (signed 64-bit integer -> binary128): from the entry, the code returns the 128-bit value
   f128_of_i64 t of C_floatditf.v. The walk follows the 32-bit twin (__floatsitf): the a0 = 0 branch returns +0; the
   other path forms s = a0 >>s 63 and |t| = (a0 xor s) - s, counts the leading zeros with the or-cascade and the 64-bit
   popcount (the register values are matched to clz64_mirror by evaluation), and splits on the sign of n - 64 for the
   128-bit shift of the significand; the shared tail forms the low word, the exponent and the sign. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Spec Require Import SoftFloat.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.P Require Import SFW1_lemmas.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc Require RProgAt.
Import OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac. From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc Require Import RProgNotJ. From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc Require Import RProgNot. From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc Require RegFold. From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc Require RProgAt. From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc Require JunkAbs.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.G Require Import C_floatditf.
Import ListNotations.
Open Scope bv_scope.

From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.P Require F_sf_helpers2.
Import OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.P.F_sf_helpers2.SF_buildtac.
From Stdlib Require Import Zify Lia.

(* The stepping tactics run on the relocatable program tree (RProgAt) instead of a fixed image. *)
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Step.step2_with rp rpm vh ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_with rp rpm vh.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.SysStep.step_ecall ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.astep_ecall.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Step.solve_load ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_load.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Step.solve_cond ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_cond.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Step.step ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Step.stepz ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Step.stepz_fast ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_fast.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.SysStep.sys_nret ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.asys_nret.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Tac.post_call segs m ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.apost_call segs m.

(* Register writes are folded as they are made; the instruction at a pc is found in the tree by its offset. *)
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Step.simp_regs ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RegFold.simp_regs_f.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.find_t_eval k t ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.find_t_eval_at k t.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.JunkAbs.split_for_access_abs H segs m A cs kn n.

Section Img.
  Context {IMG : RImg}.
  Context {CODE_floatditf : CodeAtT img_segs (sym 0x7f000900) (PROGAT_CODE_floatditf IMG)}.
  Context {RB_floatditf : RelCode (sym 0x7f000900) 292}.
  Collection ImgHyps := IMG CODE_floatditf RB_floatditf.

Local Ltac Lia.lia ::= Zify.zify; xlia zchecker.
(* Division facts are not needed by the arithmetic of this walk; the cleanup pass only costs time. *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac flia ::= flia_fast.
Local Ltac blia ::= blia_fast.
Local Ltac step ::= step_fast. Local Ltac stepz ::= stepz_fast.
Local Ltac zsimp ::= zsimp_fast.

(* Decide one boolean test of the mirror from the branch hypothesis in context. *)
Ltac decide_test1 t :=
  first [ replace t with false by (symmetry; first [apply Z.eqb_neq | apply Z.ltb_ge | apply Z.leb_gt]; blia)
        | replace t with true  by (symmetry; first [apply Z.eqb_eq | apply Z.ltb_lt | apply Z.leb_le]; blia) ];
  cbn [andb orb negb].

(* The shared tail at +240 .. +288: the low word absW << (shW & 63) masked by srai(nM64, 63), the leading one
   cleared by xor 1 << 48, the exponent sext32 (0x403e - clz) << 48 added, the sign ORed in, and the return. *)
Local Ltac ditf_tail nM64 clz :=
  zstep; zstep; rewrite (srai63_word nM64) by lia; decide_tests_b;
  do 7 zstep; rewrite Z_to_bv_swrap32; rewrite (sext32_land64 (16446 - clz));
  name_as_by expW (sext32 (16446 - clz)) (apply sext32_range);
  zstep;
  match goal with |- context [Z_to_bv 64 (Z.shiftl ?x 48)] =>
    model_reg 15%Z expSh (Z.land (Z.shiftl x 48) W64) end;
  do 3 zstep.

Lemma floatditf_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (t : Z),
  mem_inv img_segs m ->
  bv_unsigned a0 = wrap64 t ->
  evt img_segs (floatditf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (f128_of_i64 t) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x7f000900)) fc None m (seg_rom img_segs)).
(* The statement takes all three image hypotheses (the contract is used with the code and its relocation bound). *)
Proof using ImgHyps.
  intros until t. intros MI U.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl img_segs m) as WM.
  assert (Ra0 : (0 <= bv_unsigned a0 < 2^64)%Z) by apply (zr_word a0).
  unfold f128_of_i64. rewrite <- U.
  cbv beta delta [add64 sub64 shl64 not64 is_neg64 sra63 lo64 hi64 wrap64 b2z ONES64 IMPLICIT_HI]. zb_fold_lits.
  (* +0 beqz a0 *)
  zstep. if_cases K0; zify_cond K0; decide_test1 ((bv_unsigned a0) =? 0%Z)%Z.
  - (* a0 = 0: +224 a1 = 0, +228 ret; the result is +0 with the low word a0 = 0. *)
    zstep. zstep. sf_finish.
  - (* +4 srai a1, a0, 63: s, the sign mask of a0. *)
    zstep. rewrite srai63_var. rewrite (sra63_leb (bv_unsigned a0)) by lia.
    name_as_by s (if 9223372036854775808 <=? bv_unsigned a0 then 18446744073709551615 else 0)%Z
      (destruct (9223372036854775808 <=? bv_unsigned a0)%Z; lia).
    (* +8 .. +44: the lui halves of the popcount masks, a0 xor s, the addiw, and absW = (a0 xor s) - s. *)
    do 10 zstep. model_reg 11%Z absW (Z.land (Z.lxor (bv_unsigned a0) s - s) W64).
    (* +48 .. +68 the 64-bit masks; +72 half = absW >> 1. *)
    do 7 zstep. model_reg 12%Z half (Z.shiftr absW 1).
    (* +76, +80 the last two masks; +84 .. +124 the or-cascade. *)
    do 3 zstep. model_reg 17%Z x1 (Z.lor absW half).
    do 2 zstep. model_reg 17%Z x2 (Z.lor x1 (Z.shiftr x1 2)).
    do 2 zstep. model_reg 17%Z x3 (Z.lor x2 (Z.shiftr x2 4)).
    do 2 zstep. model_reg 17%Z x4 (Z.lor x3 (Z.shiftr x3 8)).
    do 2 zstep. model_reg 17%Z x5 (Z.lor x4 (Z.shiftr x4 16)).
    do 2 zstep. model_reg 17%Z x6 (Z.lor x5 (Z.shiftr x5 32)).
    (* +128 not; +132 .. +180 the popcount (with +156 t0 = a0 >> 63 for the sign). *)
    zstep. model_reg 17%Z y (Z.lxor x6 W64).
    do 3 zstep. model_reg 16%Z c1 (Z.land (y - Z.land (Z.shiftr y 1) 6148914691236517205) W64).
    do 5 zstep. model_reg 13%Z c2 (Z.land (Z.land c1 3689348814741910323 + Z.land (Z.shiftr c1 2) 3689348814741910323) W64).
    do 3 zstep. model_reg 10%Z c3 (Z.land (Z.land (c2 + Z.shiftr c2 4) W64) 1085102592571150095).
    do 2 zstep. model_reg 13%Z c4 (Z.shiftr (Z.land (c3 * 72340172838076673) W64) 56).
    replace (Z_to_bv 64 c4) with (Z_to_bv 64 (clz64_mirror absW)) by (f_equal; model_eval; reflexivity).
    name_as_by clz (clz64_mirror absW) (apply clz64_mirror_range).
    (* +184 e = clz xor 63; +188, +192 shW = sext32 (112 - e). *)
    zstep. model_reg 10%Z e (Z.lxor clz 63).
    do 2 zstep. rewrite Z_to_bv_swrap32. rewrite (sext32_land64 (112 - e)).
    name_as_by shW (sext32 (112 - e)) (apply sext32_range).
    (* +196, +200 n = zext32 shW; +204 nM64 = n - 64; +208 the sign bit at bit 63. *)
    do 2 zstep. replace (Z_to_bv 64 (Z.land shW 4294967295)) with (Z_to_bv 64 (zext32 shW)) by reflexivity.
    name_as_by n (zext32 shW) (rewrite zext32_eq; pose proof (Z.mod_pos_bound shW 4294967296 ltac:(lia)); lia).
    zstep. model_reg 15%Z nM64 (Z.land (n - 64) W64).
    zstep.
    (* +212 bltz nM64 *)
    zstep. if_cases K1; zify_cond K1; decide_test1 ((Z.shiftr nM64 63) =? 0%Z)%Z.
    + (* n < 64: +232, +236 hi0 = half >> (not n & 63), then the tail. *)
      zstep. zstep.
      name_as_by hi0 (Z.shiftr half (Z.land (Z.lxor n W64) 63))
        (change (inr64 (Z.shiftr half (Z.land (Z.lxor n W64) 63))); apply zr_shiftr; [zrange | apply Z.land_nonneg; right; lia]).
      ditf_tail nM64 clz. sf_finish.
    + (* n >= 64: +216 hi0 = absW << (n & 63), +220 j, then the tail. *)
      zstep. zstep.
      ditf_tail nM64 clz. sf_finish.
Qed.

Lemma floatditf_contract_ok : floatditf_contract.
Proof. exact floatditf_spec. Qed.

End Img.
