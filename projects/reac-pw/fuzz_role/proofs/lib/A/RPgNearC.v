From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame FP.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Nearest.
Import ListNotations.
Open Scope Z_scope.

(** pod_nearest(f, out) of reac-pw/fuzz_role's ASan image A (fuzz_role.asan, pinned sha256
    614cffc0864cc31d9d1ced61322c4efd567b64bc89fe09a227a05b5126e0debb; unstripped twin 6da77bafc5c0...), at the machine
    level: the image-A counterpart of the plain build's pod_nearest_contract (lib/Prog/pod_nearest_c.v), in the same
    library (lib/Lib evt over the image's segments A/Img0.rsegs), so that the plain walk's value half and callee
    bridges carry over. lib/A/RPgNear.v lifts it to RPgCSpec's rl_pod_nearest_specX.

    0x82ccc, 312 bytes, 78 instructions, frame 0x40 bytes: ra, s0, s1, s2, s3, s4 at sp-8 .. sp-48 and fs0 at sp-56.
    It is the plain code with three changes:
      - s4 is saved and restored too;
      - 0x82cfc-0x82d04 `auipc a0,0x18; ld a0,-0x4cc(a0); ld s4,0(a0)`: s4 = the 8 bytes at the address the .got slot
        A_GOT_SHADOW (0x9a830) holds, the shadow-offset cell A_SHADOW_CELL (0xa33f8, a .bss word), which holds
        A_SHADOW_OFF (0x7fff8000);
      - before the 8-byte store of r at out, the instrumented check 0x82dbc-0x82dc8 `srli a0,s0,3; add a0,a0,s4;
        lbu a0,0(a0); bnez a0` reads the shadow byte at A_SHADOW_OFF + out / 8 and goes to the error path 0x82dfc
        (`mv a0,s0; jal` to the 8-byte store report) when it is not 0. The contract's premise that this byte is 0
        makes that path unreachable.
    Its callees: __extendsftf2 0x83748, __lttf2 0x83434 (twice), __floatditf 0x838a4, __subtf3 0x839c8 (into
    __addtf3 0x839d8, whose 0x30-byte frame lies below pod_nearest's), __getf2 0x834fc: the CJ contracts at image A's
    symbol map (lib/CJ/RL/I/IImgA.v, instances lib/CJ/RL/I/InstA.v). Stack: the 64-byte frame and __addtf3's 48 bytes,
    A_NEAR_STACK = 112 bytes below sp. *)
Definition A_POD_NEAREST : Z := 0x82ccc.
Definition A_NEAR_STACK : Z := 112.
Definition A_GOT_SHADOW : Z := 0x9a830.
Definition A_SHADOW_CELL : Z := 0xa33f8.
Definition A_SHADOW_OFF : Z := 0x7fff8000.

(** The return value: 1 on Some, 0 on None. *)
Definition a_near_rc (o : option Z) : Z := match o with Some _ => 1 | None => 0 end.

(** Memory after the call: the 112 bytes below sp change, and on Some r also the 8 bytes at out, which then hold r;
    on None out is untouched. *)
Definition a_near_mem (m m' : word -> option byte) (sp out : Z) (o : option Z) : Prop :=
  match o with
  | Some r => munch [(sp - A_NEAR_STACK, sp); (out, out + 8)] m m' /\ bytes_at rsegs m' out (le8 (Z_to_bv 64 r))
  | None => munch [(sp - A_NEAR_STACK, sp)] m m'
  end.

(** The plain contract's premises with the stack at 112 bytes, plus the three cells the image-A code reads that the
    plain code does not: the .got slot, the shadow-offset cell (both below the stack window) and the shadow byte of
    out (outside the 112 bytes below sp), with the values the runtime keeps in them. *)
Definition pod_nearest_A_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo b : Z),
    0 <= b < 2^32 -> Sem.reg_get F (Z_to_bv 5 10) = Sem.nan_box (Z_to_bv 32 b) ->
    wr_at rsegs m (bv_unsigned a0) 8 -> bv_unsigned a0 mod 8 = 0 ->
    (bv_unsigned a0 + 8 <= bv_unsigned sp - A_NEAR_STACK \/ bv_unsigned sp <= bv_unsigned a0) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + A_NEAR_STACK <= bv_unsigned sp ->
    (forall a, lo <= a < bv_unsigned sp -> seg_rom rsegs (wa a) = None) ->
    A_SHADOW_CELL + 8 <= lo ->
    bytes_at rsegs m A_GOT_SHADOW (le8 (Z_to_bv 64 A_SHADOW_CELL)) ->
    bytes_at rsegs m A_SHADOW_CELL (le8 (Z_to_bv 64 A_SHADOW_OFF)) ->
    bytes_at rsegs m (A_SHADOW_OFF + bv_unsigned a0 / 8) [Z_to_bv 8 0] ->
    outside [(bv_unsigned sp - A_NEAR_STACK, bv_unsigned sp)] (A_SHADOW_OFF + bv_unsigned a0 / 8) ->
    frm0 fc -> mem_inv rsegs m -> MemNorm.task_mem rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (F' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (a_near_rc (nearest b INT32_MIN INT32_MAX)))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc' None m' (seg_rom rsegs) /\
         (forall k : bv 5, bv_unsigned k <> 15 -> Sem.reg_get F' k = Sem.reg_get F k) /\
         frm0 fc' /\
         a_near_mem m m' (bv_unsigned sp) (bv_unsigned a0) (nearest b INT32_MIN INT32_MAX) /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ MemNorm.task_mem rsegs m' /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 A_POD_NEAREST) fc None m (seg_rom rsegs)).
