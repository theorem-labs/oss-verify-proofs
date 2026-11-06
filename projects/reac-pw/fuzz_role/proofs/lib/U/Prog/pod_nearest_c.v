From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame FP.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Nearest.
Import ListNotations.
Open Scope Z_scope.

(** pod_nearest(f, lo, hi, out) (pod.h:152-171) as compiled into fuzz_role's UBSan build. Its only caller,
    expect_role (fuzz_role.c:55, inlined into LLVMFuzzerTestOneInput), passes lo = INT32_MIN and hi = INT32_MAX; the
    out-of-line copy folds them into constants, so it takes a0 = out and fa0 = f only. 340 bytes, 85 instructions at
    0x14490 in the UBSan image; frame 0x30 bytes: ra, s0, s1, s2, s3 at sp-8 .. sp-40 and fs0 at sp-48. The code is
    the plain build's (Prog/pod_nearest_c.v) with five sanitizer checks, each a branch to `unimp` at 0x145e0. In order:
      - 0x144ac `feq.s a1,fa0,fa0`, `beqz` -> 0x145a4: f is a NaN: s1 = 0, return 0;
      - 0x144b4 `fmv.s fs0,fa0`, s0 = out; 0x144bc `jal __extendsftf2` (0x14aa8): d in a0:a1, kept in s2:s3;
      - 0x144c4-0x144d4 fa5 = 2^31, `flt.s a0,fa5,fs0`: 2^31 < f returns 0 (0x145bc);
      - 0x144dc-0x144f8 a2:a3 = C1 = (long double)INT32_MIN - 1 (0 : 0xc01e000000020000), `jal __lttf2`
        (= __cmptf2, 0x14924), `bltz`: d < C1 returns 0;
      - check 1, float-cast-overflow upper bound: 0x144fc-0x14508 fa5 = 2^63 (0x5f000000), `flt.s a0,fs0,fa5`,
        `beqz` -> trap. Never taken: f is not a NaN and f <= 2^31 < 2^63 here;
      - check 2, float-cast-overflow lower bound: 0x1450c-0x14528 a2:a3 = C2 = -2^63 - 1 (0x0002000000000000 :
        0xc03e000000000000), `jal __gttf2` (= __getf2, 0x149ec), `blez` -> trap. Never taken: d >= C1 > C2, so the
        compare returns 1;
      - 0x1452c `fcvt.l.s s1,fs0,rtz`: t = (long long)d (static rounding toward zero);
      - 0x14534 `jal __floatditf` (0x14c04); 0x14548 `jal __subtf3` (0x14d28, a tail jump to __addtf3 0x14d38, whose
        frame is the 48 bytes below pod_nearest's): frac = d - t, kept in s2:s3;
      - 0x14554-0x14560 a2:a3 = 0.5L, `jal __getf2` (0x149ec), `bgez` -> 0x14590: check 3, `addi a0,s1,1`,
        `blt a0,s1` -> trap (signed overflow of t + 1). Never taken: t <= 2^31. Then r = t + 1 (0x14598);
      - else 0x14568-0x1457c a2:a3 = -0.5L, `jal __lttf2` (0x14924); `bgez` -> 0x1459c with r = t; below 0:
        check 4, `addi a0,s1,-1`, `blt a0,s1` -> r = t - 1, else `j` -> trap (signed overflow of t - 1). Never taken:
        t >= -2^31;
      - 0x1459c `sext.w a0,s1`, `beq a0,s1`: r fits in 32 bits; else return 0 (0x145a4);
      - check 5, alignment of the store: 0x145ac `andi a0,s0,7`, `bnez` -> trap. Never taken: out is 8-aligned (a
        premise). Then 0x145b4 `sd s1,0(s0)` stores r at out and return 1;
      - 0x145bc-0x145dc: a0 = s1; restore ra, s0-s3 and fs0; free the frame; ret.
    So the result is Nearest.nearest b INT32_MIN INT32_MAX, b the binary32 bits of f: return 1 with *out = r on
    Some r, return 0 with out untouched on None; no trap is reached.
    It reads fa0, a0 and its frame. It writes its frame [sp - 48, sp), __addtf3's frame [sp - 96, sp - 48), and on
    Some only the 8 bytes at out. Registers: a0 is the result (1 or 0); a1-a7 and t0-t6 are left open; ra, sp, gp, tp
    and s0-s11 come back. FP registers: fs0 is saved and restored, fa5 (f15) is written and not restored, and the
    callees keep F, so F' = F outside f15. fcsr: feq.s, flt.s and fcvt.l.s accrue flags and __addtf3 may raise NX;
    frm is never written, so it stays 0. __addtf3 rounds with the dynamic mode: hence frm0 fc.

    Callee contracts its walk takes as premises: the CJ soft-float contracts relocated to fuzz_role, instantiated
    with the UBSan image's sym map (CJ/RL/I/IImgU.v, instances in CJ/RL/I/InstU.v):
      extendsftf2_contract (CJ/RL/G/C_extendsftf2.v; key 0x200dc -> 0x14aa8);
      letf2_contract (CJ/RL/G/G_letf2.v; key 0x1b24c -> 0x14924; both __lttf2 calls);
      getf2_contract (CJ/RL/G/G_getf2.v; key 0x1b314 -> 0x149ec; the check-2 call and the 0.5L compare);
      floatditf_contract (CJ/RL/G/C_floatditf.v; key 0x7f000900 -> 0x14c04);
      subtf3_contract (CJ/RL/G/G_subtf3.v; key 0x1bc70 -> 0x14d28; with addtf3_spec_c, fe_getround_spec_c and
        fe_raise_inexact_spec_c; it takes stk (sp' - 48) sp' with sp' = sp - 48, mem_inv and frm0).
    The walk reaches them through U/CJBridge.v as the plain walk does through CJBridge.v (evt_bridge, MS_eq, mkR_eq,
    ret_pc_eq, frm0_iff, stk_iff, munch_iff, wmono_iff, mem_inv_to_cj / mem_inv_of_cj with MemNorm.task_mem). The
    trap checks need, besides the plain walk's value facts, f128_ge d C2 = 1 for d >= C1 (check 2) and the bounds
    -2^31 <= t <= 2^31 (checks 3 and 4).

    Call site (LLVMFuzzerTestOneInput, UBSan): 0x14128 `jal pod_nearest`, for a role value of POD_FLOAT type with
    size >= 4 (pod_float, pod.h:116-122), with sp = S - 0x220 (the harness frame) and
      fa0 = the binary32 at the start of ent->body (0x14120 `flw fa0,0x1c(a0)`, a0 + 0x1c = &pp->ent[v].body);
      a0 = sp + 0xb8 = &flag (0x14124 `addi a0,sp,0xb8`);
    the caller reads flag (`ld a2,0xb8(sp)` at 0x14130) only on a return of 1 (`beqz a0` at 0x1412c).
    Why each premise holds there: b = the 4 body bytes as a u32, so 0 <= b < 2^32, and flw writes them NaN-boxed
    (LPS Sem.v, FLoad FMT_S); out = sp + 0xb8 is 8 bytes of the harness frame, writable (FR), at or above this sp, so
    outside [sp - 96, sp), and 8-aligned because the harness sp is 16-aligned; the stack region [lo, sp) with
    lo = S - 65536 is the frame's stack (FR's stk and writability, outside the image) and holds the 96 bytes below
    this sp; frm0 fc is the slot's FP invariant; mem_inv and MemNorm.task_mem hold of the memory the cut runs on
    (MemNorm.normalize_cj, with MemNorm.mem_inv_cj_normalize). *)
Definition POD_NEAREST : Z := 0x14490.
Definition POD_NEAREST_TRAP : Z := 0x145e0.
Definition POD_NEAREST_STACK : Z := 96.

(** The bounds the compiler folded in: INT32_MIN and INT32_MAX (fuzz_role.c:55). *)
Definition NEAR_LO : Z := -2147483648.
Definition NEAR_HI : Z := 2147483647.

(** The return value: 1 on Some, 0 on None. *)
Definition pod_near_rc (o : option Z) : Z := match o with Some _ => 1 | None => 0 end.

(** Memory after the call: the 96 bytes below sp change, and on Some r also the 8 bytes at out, which then hold r;
    on None out is untouched (it lies outside the munched range). *)
Definition pod_near_mem (m m' : word -> option byte) (sp out : Z) (o : option Z) : Prop :=
  match o with
  | Some r => munch [(sp - POD_NEAREST_STACK, sp); (out, out + 8)] m m' /\ bytes_at rsegs m' out (le8 (Z_to_bv 64 r))
  | None => munch [(sp - POD_NEAREST_STACK, sp)] m m'
  end.

Definition pod_nearest_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo b : Z),
    0 <= b < 2^32 -> Sem.reg_get F (Z_to_bv 5 10) = Sem.nan_box (Z_to_bv 32 b) ->
    wr_at rsegs m (bv_unsigned a0) 8 -> bv_unsigned a0 mod 8 = 0 ->
    (bv_unsigned a0 + 8 <= bv_unsigned sp - POD_NEAREST_STACK \/ bv_unsigned sp <= bv_unsigned a0) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + POD_NEAREST_STACK <= bv_unsigned sp ->
    (forall a, lo <= a < bv_unsigned sp -> seg_rom rsegs (wa a) = None) ->
    frm0 fc -> mem_inv rsegs m -> MemNorm.task_mem rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (F' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (pod_near_rc (nearest b NEAR_LO NEAR_HI)))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc' None m' (seg_rom rsegs) /\
         (forall k : bv 5, bv_unsigned k <> 15 -> Sem.reg_get F' k = Sem.reg_get F k) /\
         frm0 fc' /\
         pod_near_mem m m' (bv_unsigned sp) (bv_unsigned a0) (nearest b NEAR_LO NEAR_HI) /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ MemNorm.task_mem rsegs m' /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 POD_NEAREST) fc None m (seg_rom rsegs)).
