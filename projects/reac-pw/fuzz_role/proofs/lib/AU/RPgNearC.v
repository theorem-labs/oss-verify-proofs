(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgNearC.v at b089f28d962e; the contract of image B's pod_nearest (fuzz_rate.asan-ubsan): the image is lib/AU/Img0.v, the entry, the .got slot and the shadow-offset cell are lib/AU/RtPgNearImgB.v's (0x83fcc, 0x9c170, 0xa4f38), the a_ names become b_, and the comment describes image B's code (five more branches to the trap `unimp` and one more __getf2 call). *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/AU/RtPgNearCB.v at 7e722b95884; relocated to reac-pw/fuzz_role's ASan image B (fuzz_role.asan-ubsan): the module paths name reac-pw/fuzz_role and the addresses are lib/AU/RPgNearImg.v's (0x82eb4, 0x9aad0, 0xa3678); role's image-B pod_nearest is fuzz_rate's image-B code but for its 8 `jal` words and the `ld` of the .got slot (its pc-relative fields), so the comment's offsets hold: the trap `unimp` E+0x174 = 0x83028 and the error path E+0x178 = 0x8302c. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame FP.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import Img0 RPgNearImg.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Nearest.
Import ListNotations.
Open Scope Z_scope.

(** pod_nearest(f, out) of reac-pw/fuzz_role's ASan image B (fuzz_role.asan-ubsan, pinned sha256
    b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; unstripped twin
    dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a), at the machine level: the image-B counterpart
    of image A's pod_nearest_A_contract (lib/A/RPgNearC.v), in the same library (lib/Lib evt over the image's
    segments lib/AU/Img0.v rsegs). lib/AU/RPgNear.v lifts it to RPgCSpec's rl_pod_nearest_specX.

    B_POD_NEAREST, 384 bytes, 96 instructions, frame 0x40 bytes: ra, s0, s1, s2, s3, s4 at sp-8 .. sp-48
    and fs0 at sp-56. It is image A's code (312 bytes, 78 instructions) with these changes (pcs as offsets from the
    entry E):
      - E+0x30-E+0x38 `auipc a0; ld a0,lo(a0); ld s4,0(a0)`: s4 = the 8 bytes at the address the .got slot
        B_GOT_SHADOW holds, the shadow-offset cell B_SHADOW_CELL (a .bss word), which holds B_SHADOW_OFF
        (0x7fff8000);
      - after the range test d < (long double)INT32_MIN - 1, two checks of the conversion (long long)d: E+0x7c-E+0x88
        `flt.s a0,fs0,fa5` (fa5 = 2^63) and `beqz a0`, and E+0x8c-E+0xa8 `jal __getf2` (d against -2^63 - 1) and
        `blez a0`, each a branch to the trap `unimp` at E+0x174;
      - t - 1 and t + 1 are formed in a0 and checked: E+0x104 `addi a0,s1,-1; blt a0,s1` (else `j` to the trap) and
        E+0x110 `addi a0,s1,1; blt a0,s1` (to the trap), then `mv s1,a0`;
      - before the instrumented check, E+0x12c `andi a0,s0,7; bnez a0` (to the trap): the alignment of out;
      - before the 8-byte store of r at out, the instrumented check E+0x134-E+0x140 `srli a0,s0,3; add a0,a0,s4;
        lbu a0,0(a0); bnez a0` reads the shadow byte at B_SHADOW_OFF + out / 8 and goes to the error path E+0x178
        (`mv a0,s0; jal` to the 8-byte store report) when it is not 0. The contract's premise that this byte is 0
        makes that path unreachable; the premises f a finite binary32 value in range and out mod 8 = 0 make every
        branch to the trap not taken.
    Its callees: __extendsftf2, __cmptf2 (twice), __getf2 (twice), __floatditf, __subtf3 (into __addtf3, whose
    0x30-byte frame lies below pod_nearest's): the CJ contracts at image B's symbol map (lib/AU/RPgNearImg.v
    N_img). Stack: the 64-byte frame and __addtf3's 48 bytes, B_NEAR_STACK = 112 bytes below sp. *)
Definition B_NEAR_STACK : Z := 112.
Definition B_SHADOW_OFF : Z := 0x7fff8000.

(** The return value: 1 on Some, 0 on None. *)
Definition b_near_rc (o : option Z) : Z := match o with Some _ => 1 | None => 0 end.

(** Memory after the call: the 112 bytes below sp change, and on Some r also the 8 bytes at out, which then hold r;
    on None out is untouched. *)
Definition b_near_mem (m m' : word -> option byte) (sp out : Z) (o : option Z) : Prop :=
  match o with
  | Some r => munch [(sp - B_NEAR_STACK, sp); (out, out + 8)] m m' /\ bytes_at rsegs m' out (le8 (Z_to_bv 64 r))
  | None => munch [(sp - B_NEAR_STACK, sp)] m m'
  end.

(** Image A's premises with image B's cells: the stack at 112 bytes, out 8-aligned (the alignment branch), the
    .got slot, the shadow-offset cell (both below the stack window) and the shadow byte of out (outside the 112 bytes
    below sp), with the values the runtime keeps in them. *)
Definition pod_nearest_B_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo b : Z),
    0 <= b < 2^32 -> Sem.reg_get F (Z_to_bv 5 10) = Sem.nan_box (Z_to_bv 32 b) ->
    wr_at rsegs m (bv_unsigned a0) 8 -> bv_unsigned a0 mod 8 = 0 ->
    (bv_unsigned a0 + 8 <= bv_unsigned sp - B_NEAR_STACK \/ bv_unsigned sp <= bv_unsigned a0) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + B_NEAR_STACK <= bv_unsigned sp ->
    (forall a, lo <= a < bv_unsigned sp -> seg_rom rsegs (wa a) = None) ->
    B_SHADOW_CELL + 8 <= lo ->
    bytes_at rsegs m B_GOT_SHADOW (le8 (Z_to_bv 64 B_SHADOW_CELL)) ->
    bytes_at rsegs m B_SHADOW_CELL (le8 (Z_to_bv 64 B_SHADOW_OFF)) ->
    bytes_at rsegs m (B_SHADOW_OFF + bv_unsigned a0 / 8) [Z_to_bv 8 0] ->
    outside [(bv_unsigned sp - B_NEAR_STACK, bv_unsigned sp)] (B_SHADOW_OFF + bv_unsigned a0 / 8) ->
    frm0 fc -> mem_inv rsegs m -> MemNorm.task_mem rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (F' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (b_near_rc (nearest b INT32_MIN INT32_MAX)))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc' None m' (seg_rom rsegs) /\
         (forall k : bv 5, bv_unsigned k <> 15 -> Sem.reg_get F' k = Sem.reg_get F k) /\
         frm0 fc' /\
         b_near_mem m m' (bv_unsigned sp) (bv_unsigned a0) (nearest b INT32_MIN INT32_MAX) /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ MemNorm.task_mem rsegs m' /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 B_POD_NEAREST) fc None m (seg_rom rsegs)).
