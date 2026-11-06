(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cjson/cjson_read_fuzzer/lib/RL/G/G_fmodl.v, with its module paths and module names changed; 47 of its 162 lines of code are new or changed and 1788 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Spec Require Import SoftFloat.
Open Scope Z_scope.

(** The value __extendsftf2 (compiler-rt fp_extend_impl, binary32 -> binary128) returns, as the binary computes it,
    in the style of SoftFloat.v's mirrors (f128_of_d, f128_of_i32): one let per register value, in the order the code
    computes it, with SoftFloat.v's 64-bit helpers. The argument is the 64-bit value of fa0; the code reads only its
    low 32 bits (fmv.x.w a1,fa0 is `sext 64 (low32 fa0)` in LPS Sem.v), so the NaN box above them does not matter.
    The low word of the result is always 0. By class of the binary32 input:
      - exponent 1..254: exponent aExp + 0x3f80, fraction aSig << 25;
      - exponent 255 (infinity, NaN): exponent 0x7fff, fraction aSig << 25. The NaN payload and its quiet bit are
        kept as they are: a signalling NaN stays signalling and no flag is raised;
      - exponent 0, aSig = 0: the signed zero;
      - exponent 0, aSig <> 0 (subnormal): clz is the 32-bit count of leading zeros of aSig, computed by the
        or-cascade (shifts 1, 2, 4, then 8 and 16 read through t = aSig' << 41 shifted right by 49 and 57) and the
        32-bit popcount; aSig is shifted left by clz + 17 (its leading one then sits on bit 48), that bit is dropped
        (xor 1 << 48) and the exponent is 0x3f80 - clz + 9.
    In every case the binary128 value equals the binary32 value (sign, payload and quiet bit too for NaNs). *)
Definition f128_of_f32 (fbits : Z) : Z :=
  let a1 := sext32 fbits in
  let aExp := Z.land (srliw a1 23) 255 in
  let aSig := shr64 (shl64 a1 41) 41 in
  let signHi := shl64 (shr64 a1 31) 63 in
  if negb (aExp =? 0) then
    if negb (aExp =? 255) then
      let hi := Z.lor (Z.lor (shl64 (add64 aExp 0x3f80) 48) signHi) (shl64 aSig 25) in
      mk128 hi 0
    else
      let hi := Z.lor (Z.lor INF_HI signHi) (shl64 aSig 25) in
      mk128 hi 0
  else if aSig =? 0 then mk128 (Z.lor (Z.lor (shl64 0 48) signHi) aSig) 0
  else
    let x1 := Z.lor aSig (shr64 aSig 1) in
    let x2 := Z.lor x1 (shr64 x1 2) in
    let x3 := Z.lor x2 (shr64 x2 4) in
    let t := shl64 x3 41 in
    let x4 := Z.lor x3 (shr64 t 49) in
    let x5 := Z.lor x4 (shr64 t 57) in
    let y := not64 x5 in
    let c1 := sub64 y (Z.land (shr64 y 1) 0x55555555) in
    let c2 := add64 (Z.land c1 0x33333333) (Z.land (shr64 c1 2) 0x33333333) in
    let c3 := Z.land (add64 c2 (shr64 c2 4)) 0x0f0f0f0f in
    let clz := srliw (mul64 c3 0x01010101) 24 in
    let sh := add64 clz 17 in
    let sig := Z.land (sub64 (b2z (is_neg64 sh)) 1) (shl64 aSig (Z.land sh 63)) in
    let dstExp := add64 (sub64 0x3f80 clz) 9 in
    let hi := Z.lor (Z.lor (shl64 dstExp 48) signHi) (Z.lxor sig IMPLICIT_HI) in
    mk128 hi 0.

From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc Require Import RStep RProgNotJ.
Import ListNotations.
Open Scope bv_scope.

(** The code of __extendsftf2: 348 bytes, 87 instructions, read from fuzz_role's image (plain 0x14810; UBSan 0x14aa8
    holds the same bytes, as do fuzz_rate's and fuzz_headamp's copies and omx-clap-core's, whose G_fmodl.v carries
    this same tree as fmodl_prog_r1 under the same key). All jumps are inside the routine, so B is the only base.
    Offsets: +0 fmv.x.w; +20 beqz aExp -> +72 (zero or subnormal); +28 bne aExp,255 -> +280 (normal); +32..+68
    infinity or NaN, ret; +72 a0 = 0, +76 beqz aSig -> +324 (zero); +80..+276 subnormal, ret; +280..+320 normal,
    ret; +324..+344 zero, ret. *)
Definition extendsftf2_prog (B : Z) : RStep.ptree :=
  PNode 172%Z
  (PNode 84%Z
    (PNode 40%Z
      (PLeaf
          (PJ_Fmv_FMV_X_F_FMT_S_nn 0 11 10 4
          (PJ_ShiftImm32_ALU_SRL_nnn 4 10 11 23 4
          (PJ_ShiftImm_ALU_SLL_nnn 8 12 11 41 4
          (PJ_OpImm_ALU_AND_nnn 12 13 10 255 4
          (PJ_ShiftImm_ALU_SRL_nnn 16 12 12 41 4
          (PJ_Branch_BC_EQ_nnn 20 13 0 52 4
          (PJ_OpImm_ALU_ADD_nnn 24 10 0 255 4
          (PJ_Branch_BC_NE_nnn 28 13 10 252 4
          (PJ_OpImm_ALU_ADD_nnn 32 10 0 0 4
          (PJ_ShiftImm_ALU_SLL_nnn 36 12 12 25 4 nil)))))))))))
      (PLeaf
          (PJ_Lui_nn 40 13 8 4
          (PJ_OpImm_ALU_ADD_nnn 44 13 13 4095 4
          (PJ_ShiftImm_ALU_SRL_nnn 48 11 11 31 4
          (PJ_ShiftImm_ALU_SLL_nnn 52 11 11 63 4
          (PJ_ShiftImm_ALU_SLL_nnn 56 13 13 48 4
          (PJ_Op_ALU_OR_nnn 60 11 13 11 4
          (PJ_Op_ALU_OR_nnn 64 11 11 12 4
          (PJ_Jalr_nnn 68 0 1 0 4
          (PJ_OpImm_ALU_ADD_nnn 72 10 0 0 4
          (PJ_Branch_BC_EQ_nnn 76 12 0 248 4
          (PJ_ShiftImm_ALU_SRL_nnn 80 13 12 1 4 nil)))))))))))))
    (PNode 128%Z
      (PLeaf
          (PJ_Op_ALU_OR_nnn 84 13 12 13 4
          (PJ_ShiftImm_ALU_SRL_nnn 88 14 13 2 4
          (PJ_Op_ALU_OR_nnn 92 13 13 14 4
          (PJ_ShiftImm_ALU_SRL_nnn 96 14 13 4 4
          (PJ_Op_ALU_OR_nnn 100 13 13 14 4
          (PJ_ShiftImm_ALU_SLL_nnn 104 14 13 41 4
          (PJ_ShiftImm_ALU_SRL_nnn 108 15 14 49 4
          (PJ_Op_ALU_OR_nnn 112 13 13 15 4
          (PJ_Lui_nn 116 15 349525 4
          (PJ_OpImm32_nnn 120 15 15 1365 4
          (PJ_ShiftImm_ALU_SRL_nnn 124 14 14 57 4 nil))))))))))))
      (PLeaf
          (PJ_Op_ALU_OR_nnn 128 13 13 14 4
          (PJ_OpImm_ALU_XOR_nnn 132 13 13 4095 4
          (PJ_ShiftImm_ALU_SRL_nnn 136 14 13 1 4
          (PJ_Op_ALU_AND_nnn 140 14 14 15 4
          (PJ_Lui_nn 144 15 209715 4
          (PJ_OpImm32_nnn 148 15 15 819 4
          (PJ_Op_ALU_SUB_nnn 152 13 13 14 4
          (PJ_Op_ALU_AND_nnn 156 14 13 15 4
          (PJ_ShiftImm_ALU_SRL_nnn 160 13 13 2 4
          (PJ_Op_ALU_AND_nnn 164 13 13 15 4
          (PJ_Op_ALU_ADD_nnn 168 13 14 13 4 nil))))))))))))))
  (PNode 260%Z
    (PNode 216%Z
      (PLeaf
          (PJ_ShiftImm_ALU_SRL_nnn 172 14 13 4 4
          (PJ_Op_ALU_ADD_nnn 176 13 13 14 4
          (PJ_Lui_nn 180 14 61681 4
          (PJ_OpImm_ALU_ADD_nnn 184 14 14 3855 4
          (PJ_Op_ALU_AND_nnn 188 13 13 14 4
          (PJ_Lui_nn 192 14 4112 4
          (PJ_OpImm_ALU_ADD_nnn 196 14 14 257 4
          (PJ_Mul_M_MUL_nnn 200 13 13 14 4
          (PJ_Lui_nn 204 14 4 4
          (PJ_OpImm_ALU_ADD_nnn 208 14 14 3968 4
          (PJ_ShiftImm32_ALU_SRL_nnn 212 13 13 24 4 nil))))))))))))
      (PLeaf
          (PJ_Op_ALU_SUB_nnn 216 14 14 13 4
          (PJ_OpImm_ALU_ADD_nnn 220 13 13 17 4
          (PJ_Op_ALU_SLL_nnn 224 12 12 13 4
          (PJ_OpImm_ALU_SLT_nnn 228 13 13 0 4
          (PJ_OpImm_ALU_ADD_nnn 232 13 13 4095 4
          (PJ_Op_ALU_AND_nnn 236 12 13 12 4
          (PJ_OpImm_ALU_ADD_nnn 240 15 0 1 4
          (PJ_OpImm_ALU_ADD_nnn 244 13 14 9 4
          (PJ_ShiftImm_ALU_SLL_nnn 248 15 15 48 4
          (PJ_Op_ALU_XOR_nnn 252 12 12 15 4
          (PJ_ShiftImm_ALU_SRL_nnn 256 11 11 31 4 nil)))))))))))))
    (PNode 304%Z
      (PLeaf
          (PJ_ShiftImm_ALU_SLL_nnn 260 11 11 63 4
          (PJ_ShiftImm_ALU_SLL_nnn 264 13 13 48 4
          (PJ_Op_ALU_OR_nnn 268 11 13 11 4
          (PJ_Op_ALU_OR_nnn 272 11 11 12 4
          (PJ_Jalr_nnn 276 0 1 0 4
          (PJ_OpImm_ALU_ADD_nnn 280 10 0 0 4
          (PJ_Lui_nn 284 14 4 4
          (PJ_OpImm_ALU_ADD_nnn 288 14 14 3968 4
          (PJ_Op_ALU_ADD_nnn 292 13 13 14 4
          (PJ_ShiftImm_ALU_SLL_nnn 296 12 12 25 4
          (PJ_ShiftImm_ALU_SRL_nnn 300 11 11 31 4 nil))))))))))))
      (PLeaf
          (PJ_ShiftImm_ALU_SLL_nnn 304 11 11 63 4
          (PJ_ShiftImm_ALU_SLL_nnn 308 13 13 48 4
          (PJ_Op_ALU_OR_nnn 312 11 13 11 4
          (PJ_Op_ALU_OR_nnn 316 11 11 12 4
          (PJ_Jalr_nnn 320 0 1 0 4
          (PJ_ShiftImm_ALU_SRL_nnn 324 11 11 31 4
          (PJ_ShiftImm_ALU_SLL_nnn 328 11 11 63 4
          (PJ_ShiftImm_ALU_SLL_nnn 332 13 0 48 4
          (PJ_Op_ALU_OR_nnn 336 11 13 11 4
          (PJ_Op_ALU_OR_nnn 340 11 11 12 4
          (PJ_Jalr_nnn 344 0 1 0 4 nil)))))))))))))).

(** The routine is named by the sym key 0x200dc, the key the released CJ files give __extendsftf2 (G_fmodl.v). An
    image instantiates this file through its sym map: fuzz_role's maps send 0x200dc to 0x14810 (plain) and 0x14aa8
    (UBSan); CodeAtT and RelCode are then closed by computation, as for the other CJ routines. *)
Definition PROGAT_CODE_extendsftf2 (IMG : RImg) := extendsftf2_prog (sym 0x200dc).

Section Img.
  Context {IMG : RImg}.
  (** What a proof of the contract takes from the image (the contract statement itself needs only IMG). *)
  Context {CODE_extendsftf2 : CodeAtT img_segs (sym 0x200dc) (PROGAT_CODE_extendsftf2 IMG)}.
  Context {RB_extendsftf2 : RelCode (sym 0x200dc) 348}.

(** After the return: a0:a1 hold the result R (low word, high word); every other register the code may write (it
    writes a2-a5) and every caller-saved register is left open, as SoftFloat's other leaf posts do; sp, gp, tp, ra
    and s0-s11 are as at entry; F and fcsr are unchanged (fmv.x.w is the only FP instruction and it raises no flag);
    memory is unchanged (no store, no stack). *)
Definition extendsftf2_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (R : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 R)) (Z_to_bv 64 (hi64 R)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom img_segs)
    /\ munch [] m m' /\ wmono img_segs m m' /\ mem_inv img_segs m'.

(** extendsftf2_contract: from the entry, with any register values, the call returns R = f128_of_f32 of fa0's value
    (FP register 10, the binary32 argument of the RISC-V soft-float ABI). The only premise is mem_inv, as for the
    other leaves (letf2_contract, getf2_contract, extenddftf2_contract): no stack, no frm (no dynamic rounding). The
    shape is extenddftf2_contract's (the released double -> binary128 routine, which also reads fa0). *)
Definition extendsftf2_contract : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  mem_inv img_segs m ->
  evt img_segs (extendsftf2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               (f128_of_f32 (bv_unsigned (reg_get F 10))) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x200dc)) fc None m (seg_rom img_segs)).

End Img.

Existing Class extendsftf2_contract.
