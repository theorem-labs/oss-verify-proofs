(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cjson/cjson_read_fuzzer/lib/RL/G/G_pop_arg.v, with its addresses and numbers changed; 75 of its 139 lines of code are new or changed and 479 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.CJ.Spec Require Import SoftFloat.
Open Scope Z_scope.

(** The value __floatditf (compiler-rt, signed 64-bit integer -> binary128) returns, as the binary computes it, in the
    style of SoftFloat.v's f128_of_i32 (the 32-bit twin, __floatsitf): one let per register value, in the order the
    code computes it. t is the integer in a0; only wrap64 t is used, so t may be read as signed or unsigned.
      - a0 = 0: the result is +0 (both words 0);
      - otherwise s = a0 >>s 63, absW = (a0 xor s) - s (= |t|; 2^63 for t = -2^63), clz = clz64_mirror absW (the
        or-cascade and the 64-bit popcount the code runs), e = clz xor 63 (the index of the leading one), shW = 112 - e
        as a 32-bit word and n its zero extension; the significand absW << (112 - e) is formed as a 128-bit shift
        (high word: absW << n when n >= 64, else (absW >> 1) >> (not n & 63); low word: absW << shW masked by
        n - 64 < 0), the leading one (bit 112) is cleared by xor 1 << 48, the exponent 0x403e - clz is added at bit 48
        and the sign bit is ORed in.
    The conversion is exact: every 64-bit integer has at most 64 significant bits and binary128 has 113. *)
Definition f128_of_i64 (t : Z) : Z :=
  let a0 := wrap64 t in
  if a0 =? 0 then mk128 0 a0
  else
  let s := sra63 a0 in
  let absW := sub64 (Z.lxor a0 s) s in
  let half := shr64 absW 1 in
  let clz := clz64_mirror absW in
  let signHi := shl64 (shr64 a0 63) 63 in
  let e := Z.lxor clz 63 in
  let shW := sext32 (sub64 112 e) in
  let n := zext32 shW in
  let nM64 := sub64 n 64 in
  let hi0 := if negb (is_neg64 nM64) then shl64 absW (Z.land n 63)
             else shr64 half (Z.land (not64 n) 63) in
  let lo := Z.land (smask64 nM64) (shl64 absW (Z.land shW 63)) in
  let hi1 := Z.lxor hi0 IMPLICIT_HI in
  let expW := sext32 (sub64 0x403e clz) in
  let hi2 := add64 hi1 (shl64 expW 48) in
  let hi := Z.lor hi2 signHi in
  mk128 hi lo.

From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.CJ.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.CJ.RL.Reloc Require Import RStep RProgNotJ.
Import ListNotations.
Open Scope bv_scope.

(** The code of __floatditf: 292 bytes, 73 instructions, read from fuzz_role's image (plain 0x1496c; UBSan 0x14c04
    holds the same bytes, as do fuzz_rate's and fuzz_headamp's copies). All jumps are inside the routine, so B is the
    only base. Offsets: +0 beqz a0 -> +224 (a1 = 0, ret); +4..+208 sign, |t|, the clz and the shift amounts;
    +212 bltz nM64 -> +232; +216 sll, +220 j -> +240; +232..+236 the n < 64 high word; +240..+288 low word,
    exponent, sign, ret. *)
Definition floatditf_prog (B : Z) : RStep.ptree :=
  PNode 144%Z
  (PNode 72%Z
    (PNode 36%Z
      (PLeaf
          (PJ_Branch_BC_EQ_nnn 0 10 0 224 4
          (PJ_ShiftImm_ALU_SRA_nnn 4 11 10 63 4
          (PJ_Lui_nn 8 12 349525 4
          (PJ_Lui_nn 12 13 209715 4
          (PJ_Lui_nn 16 14 61681 4
          (PJ_Lui_nn 20 15 4112 4
          (PJ_Op_ALU_XOR_nnn 24 16 10 11 4
          (PJ_OpImm32_nnn 28 12 12 1365 4
          (PJ_OpImm32_nnn 32 13 13 819 4 nil))))))))))
      (PLeaf
          (PJ_OpImm32_nnn 36 14 14 3855 4
          (PJ_OpImm32_nnn 40 15 15 257 4
          (PJ_Op_ALU_SUB_nnn 44 11 16 11 4
          (PJ_ShiftImm_ALU_SLL_nnn 48 16 12 32 4
          (PJ_ShiftImm_ALU_SLL_nnn 52 17 13 32 4
          (PJ_ShiftImm_ALU_SLL_nnn 56 5 14 32 4
          (PJ_Op_ALU_ADD_nnn 60 16 12 16 4
          (PJ_ShiftImm_ALU_SLL_nnn 64 6 15 32 4
          (PJ_Op_ALU_ADD_nnn 68 13 13 17 4 nil)))))))))))
    (PNode 108%Z
      (PLeaf
          (PJ_ShiftImm_ALU_SRL_nnn 72 12 11 1 4
          (PJ_Op_ALU_ADD_nnn 76 14 14 5 4
          (PJ_Op_ALU_ADD_nnn 80 15 15 6 4
          (PJ_Op_ALU_OR_nnn 84 17 11 12 4
          (PJ_ShiftImm_ALU_SRL_nnn 88 5 17 2 4
          (PJ_Op_ALU_OR_nnn 92 17 17 5 4
          (PJ_ShiftImm_ALU_SRL_nnn 96 5 17 4 4
          (PJ_Op_ALU_OR_nnn 100 17 17 5 4
          (PJ_ShiftImm_ALU_SRL_nnn 104 5 17 8 4 nil))))))))))
      (PLeaf
          (PJ_Op_ALU_OR_nnn 108 17 17 5 4
          (PJ_ShiftImm_ALU_SRL_nnn 112 5 17 16 4
          (PJ_Op_ALU_OR_nnn 116 17 17 5 4
          (PJ_ShiftImm_ALU_SRL_nnn 120 5 17 32 4
          (PJ_Op_ALU_OR_nnn 124 17 17 5 4
          (PJ_OpImm_ALU_XOR_nnn 128 17 17 4095 4
          (PJ_ShiftImm_ALU_SRL_nnn 132 5 17 1 4
          (PJ_Op_ALU_AND_nnn 136 16 5 16 4
          (PJ_Op_ALU_SUB_nnn 140 16 17 16 4 nil))))))))))))
  (PNode 216%Z
    (PNode 180%Z
      (PLeaf
          (PJ_Op_ALU_AND_nnn 144 17 16 13 4
          (PJ_ShiftImm_ALU_SRL_nnn 148 16 16 2 4
          (PJ_Op_ALU_AND_nnn 152 13 16 13 4
          (PJ_ShiftImm_ALU_SRL_nnn 156 5 10 63 4
          (PJ_Op_ALU_ADD_nnn 160 13 17 13 4
          (PJ_ShiftImm_ALU_SRL_nnn 164 10 13 4 4
          (PJ_Op_ALU_ADD_nnn 168 10 13 10 4
          (PJ_Op_ALU_AND_nnn 172 10 10 14 4
          (PJ_Mul_M_MUL_nnn 176 13 10 15 4 nil))))))))))
      (PLeaf
          (PJ_ShiftImm_ALU_SRL_nnn 180 13 13 56 4
          (PJ_OpImm_ALU_XOR_nnn 184 10 13 63 4
          (PJ_OpImm_ALU_ADD_nnn 188 14 0 112 4
          (PJ_Op32_ALU_SUB_nnn 192 10 14 10 4
          (PJ_ShiftImm_ALU_SLL_nnn 196 14 10 32 4
          (PJ_ShiftImm_ALU_SRL_nnn 200 16 14 32 4
          (PJ_OpImm_ALU_ADD_nnn 204 15 16 4032 4
          (PJ_ShiftImm_ALU_SLL_nnn 208 14 5 63 4
          (PJ_Branch_BC_LT_nnn 212 15 0 20 4 nil)))))))))))
    (PNode 252%Z
      (PLeaf
          (PJ_Op_ALU_SLL_nnn 216 12 11 16 4
          (PJ_Jal_nn 220 0 20 4
          (PJ_OpImm_ALU_ADD_nnn 224 11 0 0 4
          (PJ_Jalr_nnn 228 0 1 0 4
          (PJ_OpImm_ALU_XOR_nnn 232 16 16 4095 4
          (PJ_Op_ALU_SRL_nnn 236 12 12 16 4
          (PJ_Op_ALU_SLL_nnn 240 10 11 10 4
          (PJ_ShiftImm_ALU_SRA_nnn 244 15 15 63 4
          (PJ_OpImm_ALU_ADD_nnn 248 11 0 1 4 nil))))))))))
      (PLeaf
          (PJ_Op_ALU_AND_nnn 252 10 15 10 4
          (PJ_Lui_nn 256 15 4 4
          (PJ_ShiftImm_ALU_SLL_nnn 260 11 11 48 4
          (PJ_OpImm_ALU_ADD_nnn 264 15 15 62 4
          (PJ_Op_ALU_XOR_nnn 268 11 12 11 4
          (PJ_Op32_ALU_SUB_nnn 272 15 15 13 4
          (PJ_ShiftImm_ALU_SLL_nnn 276 15 15 48 4
          (PJ_Op_ALU_ADD_nnn 280 11 11 15 4
          (PJ_Op_ALU_OR_nnn 284 11 11 14 4
          (PJ_Jalr_nnn 288 0 1 0 4 nil))))))))))))).

(** The routine is named by the sym key 0x7f000900. No released CJ file names __floatditf (the cjson image the CJ
    keys come from has no such routine), so the key is a synthetic one in the 0x7f000xxx range the CJ maps already
    use for routines outside that image (0x7f000100 .. 0x7f000800 are taken). fuzz_role's maps send it to 0x1496c
    (plain) and 0x14c04 (UBSan). *)
Definition PROGAT_CODE_floatditf (IMG : RImg) := floatditf_prog (sym 0x7f000900).

Section Img.
  Context {IMG : RImg}.
  (** What a proof of the contract takes from the image (the contract statement itself needs only IMG). *)
  Context {CODE_floatditf : CodeAtT img_segs (sym 0x7f000900) (PROGAT_CODE_floatditf IMG)}.
  Context {RB_floatditf : RelCode (sym 0x7f000900) 292}.

(** After the return: a0:a1 hold the result R (low word, high word); every other register the code may write (it
    writes a2-a7, t0 and t1) and every caller-saved register is left open, as floatsitf_post does; sp, gp, tp, ra and
    s0-s11 are as at entry; F and fcsr are unchanged (no FP instruction); memory is unchanged (no store, no stack). *)
Definition floatditf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (R : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 R)) (Z_to_bv 64 (hi64 R)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom img_segs)
    /\ munch [] m m' /\ wmono img_segs m m' /\ mem_inv img_segs m'.

(** floatditf_contract: from the entry with a0 = t (as a 64-bit word) and any other register values, the call returns
    R = f128_of_i64 t. The only premise besides the argument is mem_inv, as for floatsitf_contract, whose shape this
    is (there `bv_unsigned a0 = sext32 i`). *)
Definition floatditf_contract : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (t : Z),
  mem_inv img_segs m ->
  bv_unsigned a0 = wrap64 t ->
  evt img_segs (floatditf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (f128_of_i64 t) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x7f000900)) fc None m (seg_rom img_segs)).

End Img.

Existing Class floatditf_contract.
