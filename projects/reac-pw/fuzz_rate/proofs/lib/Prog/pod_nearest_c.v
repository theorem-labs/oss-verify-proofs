From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame FP.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Nearest.
Import ListNotations.
Open Scope Z_scope.

(** pod_nearest(f, lo, hi, out) (pod.h:152-171) as compiled into fuzz_rate. Its only caller, expect_rate
    (fuzz_rate.c:80, inlined into LLVMFuzzerTestOneInput), passes lo = INT32_MIN and hi = INT32_MAX; the out-of-line
    copy folds them into constants, so it takes a0 = out and fa0 = f only. 268 bytes, 67 instructions at 0x14884 in
    the plain image; frame 0x30 bytes: ra, s0, s1, s2, s3 at sp-8 .. sp-40 and fs0 at sp-48. In order:
      - 0x148a0 `feq.s a1,fa0,fa0`, `beqz` -> 0x1495c: f is a NaN: s1 = 0, return 0 (no call, no store but the frame);
      - 0x148a8 `fmv.s fs0,fa0`, s0 = out; 0x148b0 `jal __extendsftf2` (0x15050): d = (long double)f in a0:a1, kept
        in s2:s3;
      - 0x148b8-0x148c8 fa5 = 2^31 (`lui 0x4f000`, `fmv.w.x`), `flt.s a0,fa5,fs0`: 2^31 < f returns 0 (the test
        d > hi + 1, made on f);
      - 0x148d0-0x148ec a2:a3 = C1 = (long double)INT32_MIN - 1 (low word 0, high word 0xc01e000000020000),
        `jal __lttf2` (= __cmptf2 = __letf2, 0x14ecc), `bltz`: d < C1 returns 0 (the test d < lo - 1);
      - 0x148f0 `fcvt.l.s s1,fs0,rtz`: t = (long long)d, made on f (static rounding toward zero);
      - 0x148f8 `jal __floatditf` (0x151ac): (long double)t; 0x1490c `jal __subtf3` (0x152d0; it flips the sign of
        its second operand and jumps to __addtf3, 0x152e0, whose frame is the 48 bytes below pod_nearest's):
        frac = d - t, kept in s2:s3;
      - 0x14918-0x14924 a2:a3 = 0.5L (0 : 0x3ffe000000000000), `jal __getf2` (0x14f94), `bgez` -> 0x14950:
        r = t + 1;
      - else 0x1492c-0x14940 a2:a3 = -0.5L (0 : 0xbffe000000000000), `jal __lttf2` (0x14ecc): below 0 gives
        r = t - 1 (0x14948), else r = t;
      - 0x14954 `sext.w a0,s1`, `beq a0,s1`: r fits in 32 bits (lo <= r <= hi): 0x14964 `sd s1,0(s0)` stores r at out
        and return 1; else return 0;
      - 0x1496c-0x1498c: a0 = s1; restore ra, s0-s3 and fs0 (`fld` of the slot the prologue's `fsd` wrote); free
        the frame; ret.
    So the result is Nearest.nearest b INT32_MIN INT32_MAX, b the binary32 bits of f: return 1 with *out = r on
    Some r, return 0 with out untouched on None. (The C computes floor(f + 1/2) exactly: d = f, t = trunc d,
    frac = d - t and r = t + [frac >= 1/2] - [frac < -1/2] are exact; NaN and the infinities give None; the early
    range test drops only values whose rounding lies outside [lo, hi].)
    It reads fa0, a0 and its frame. It writes its frame [sp - 48, sp), __addtf3's frame [sp - 96, sp - 48), and on
    Some only the 8 bytes at out. Registers: a0 is the result (1 or 0 as a 64-bit word); a1-a7 and t0-t6 are left
    open (its own code and its callees' posts); ra, sp, gp, tp and s0-s11 come back (it restores s0-s3; the callees
    keep the s registers). FP registers: fs0 is saved and restored, fa5 (f15) is written and not restored, and the
    callees keep F, so F' = F outside f15. fcsr: feq.s, flt.s and fcvt.l.s accrue flags (NV for a NaN, NX for an
    inexact truncation) and __addtf3 may raise NX; no instruction writes frm, so frm stays 0. __addtf3 rounds with
    the dynamic mode (it reads frm through __fe_getround): hence frm0 fc.

    Callee contracts its walk takes as premises: the CJ soft-float contracts relocated to fuzz_rate, instantiated
    with the plain image's sym map (CJ/RL/I/IImgP.v, instances in CJ/RL/I/InstP.v):
      extendsftf2_contract (CJ/RL/G/C_extendsftf2.v; key 0x200dc -> 0x15050; result f128_of_f32 of fa0);
      letf2_contract (CJ/RL/G/G_letf2.v; key 0x1b24c -> 0x14ecc; result f128_le; both __lttf2 calls);
      floatditf_contract (CJ/RL/G/C_floatditf.v; key 0x7f000900 -> 0x151ac; result f128_of_i64 t);
      subtf3_contract (CJ/RL/G/G_subtf3.v; key 0x1bc70 -> 0x152d0; result f128_sub; it rests on addtf3_spec_c,
        fe_getround_spec_c and fe_raise_inexact_spec_c; it takes stk (sp' - 48) sp' with sp' = sp - 48, mem_inv
        and frm0);
      getf2_contract (CJ/RL/G/G_getf2.v; key 0x1b314 -> 0x14f94; result f128_ge).
    The walk reaches them through CJBridge.v (the released bridge between this frame library and the CJ one):
    evt_bridge turns a CJ evt into this library's evt; MS_eq, mkR_eq and ret_pc_eq identify the states; frm0_iff,
    stk_iff, munch_iff and wmono_iff carry the side facts; mem_inv_to_cj and mem_inv_of_cj convert
    mem_inv /\ MemNorm.task_mem into the CJ mem_inv and back (hence task_mem as a premise and in the post, as in
    the released boxreg contracts that call CJ code). The value steps rest on facts about the mirrors: f128_of_f32
    and f128_of_i64 are exact, f128_sub d t is exact, and f128_le / f128_ge compare d with C1 and frac with +-1/2
    by value.

    Call site (LLVMFuzzerTestOneInput, plain): 0x143a4 `jal pod_nearest`, for a rate value of POD_FLOAT type with
    size >= 4 (pod_float, pod.h:116-122), with sp = S - 0x220 (the harness frame) and
      fa0 = the binary32 at the start of ent->body (0x1439c `flw fa0,8(a0)`, a0 = &pp->ent[v]);
      a0 = sp + 0xb8 = &near (0x143a0 `addi a0,sp,0xb8`);
    the caller reads near (`lw a2,0xb8(sp)` at 0x143ac) only on a return of 1 (`beqz a0` at 0x143a8).
    Why each premise holds there: b = the 4 body bytes as a u32, so 0 <= b < 2^32, and flw writes them NaN-boxed
    (LPS Sem.v, FLoad FMT_S: fset rd (nan_box v)); out = sp + 0xb8 is 8 bytes of the harness frame, writable (FR),
    at or above this sp, so outside [sp - 96, sp), and 8-aligned because the harness sp is 16-aligned; the stack
    region [lo, sp) with lo = S - 65536 is the frame's stack (FR's stk and writability, outside the image) and holds
    the 96 bytes below this sp; frm0 fc is the slot's FP invariant (frm is 0 at entry and no instruction of the image
    writes frm); mem_inv and MemNorm.task_mem hold of the memory the cut runs on (MemNorm.normalize_cj, with
    MemNorm.mem_inv_cj_normalize). *)
Definition POD_NEAREST : Z := 0x14884.
Definition POD_NEAREST_STACK : Z := 96.

(** The bounds the compiler folded in: INT32_MIN and INT32_MAX (fuzz_rate.c:80). *)
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
