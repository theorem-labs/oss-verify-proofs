From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout.
Import ListNotations.
Open Scope Z_scope.

(** One turn of the builder's pod loop up to its stop test, as an evt: ent_build(&e, &in) inlined in
    LLVMFuzzerTestOneInput (UBSan image, pod.h:265-379, called at pod.h:427), from the loop head 0x13560 to the join
    0x13ee4 where the stop test of pod.h:428 begins (then the call of pod_write_ent at 0x13efc). The form is
    reac-pw/fuzz_role's U/Prog/RoleBuild/EntCut.v at rate's registers
    (liveness by a backward pass over 0x13560 .. 0x13ee4). Statement text only.

    Registers at 0x13560 (what the turn reads there): s9 = src, the input cursor; s10 = |r|, the bytes left, r being
    the input bytes at src; the constants pod_build's preheader set (0x132ac-0x13338) and the Struct's set-up
    (0x1354c): s0 = sp + 0x188 (t[96]), s1 = 4 (the Int type and size), s2 = 95 (the head-amp key's part clamp),
    s4 = 0xcccccccd << 32 (the multiplier of v / 10), s5 = 10 (kind % 10), s6 = 0x4000. s3 is the pod loop's
    counter k, which the turn keeps. pp and &pp->len are not in registers here: the cases that need them, and every
    path to the join, read them from the cells sp + 0xd8 (pp) and sp + 0xc8 (pp + 0x4000). The frame cells the turn
    reads: sp + 0x0 = 0x15555556 (the multiplier of v / 3), sp + 0x80 = ~(sp + 0x170) and sp + 0xa0 = ~(sp + 0xf0)
    (the bounds of the pointer-overflow checks on ch + k and e->body + n), sp + 0xc8, sp + 0xd8. Every other register
    is arbitrary.

    In order: memset(e = sp + 0xe8, 0, 104) (0x1356c); kind = fuzz_u8 (the empty input to 0x13ac4); kind % 10 by
    multiply (0x1358c-0x135a0); kind 9 by the branch at 0x135ac to 0x138a4, kinds 0-8 by `jr a1` (0x135d0) through the
    nine 4-byte offsets at 0x10558 (.rodata; targets 0:0x135d4 1:0x13778 2:0x13658 3:0x136c0 4:0x13610 5:0x137d0
    6:0x137f4 7:0x13708 8:0x13830); then the case's reads and stores into e (memcpy, memset, strlen; the vocab, odd_ch
    and param pointer tables of .data.rel.ro, the other tables and strings of .rodata). Its UBSan checks (branches to
    the `unimp` at 0x146bc: the cursor's p + 1 and p + n, the table indexes, e->body + n, r[k], ch + k) are not taken.
    At 0x13ee4, with (e, r') = ent_build r (Pod/Model.v): s9 = the cursor after the turn, t1 = |r'|, e's 104 bytes at
    sp + 0xe8 as Layout.ent_mem lays them out (type, size, body, zeros), s8 = pp and s11 = pp + 0x4000 (from their
    cells); sp, gp, tp, s0, s1, s2, s3, s4, s5, s6, F and fc unchanged (no FP instruction in the turn). The bytes
    changed: the callee stacks below sp, the spill cell [sp + 0x48, sp + 0x50) (0x137c0, 0x13958) and
    [sp + 0xe8, sp + 0x1e8): e, parts, ch[24] and t[96].

    Premises: r at src (src > 0), below the stack region; the stack region with the frame's locals (stk over
    [lo, sp + 0x1e8): present and writable), outside the image, sp 16-aligned; the .data.rel.ro tables as in the
    image; mem_inv. *)

Definition ENT_HEAD : Z := 0x13560.
Definition ENT_JOIN : Z := 0x13ee4.

Definition rb_ent_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (r : list byte) (src pp lo : Z),
    s9 = Z_to_bv 64 src -> s10 = Z_to_bv 64 (Z.of_nat (length r)) ->
    s0 = Z_to_bv 64 (bv_unsigned sp + 0x188) -> s1 = Z_to_bv 64 4 -> s2 = Z_to_bv 64 95 ->
    s4 = Z_to_bv 64 (0xcccccccd * 2^32) -> s5 = Z_to_bv 64 10 -> s6 = Z_to_bv 64 0x4000 ->
    0 < src -> bytes_at rsegs m src r -> src + Z.of_nat (length r) <= lo ->
    bytes_at rsegs m (bv_unsigned sp + 0x0) (le8 (Z_to_bv 64 0x15555556)) ->
    bytes_at rsegs m (bv_unsigned sp + 0x80) (le8 (Z_to_bv 64 (Z.lnot (bv_unsigned sp + 0x170)))) ->
    bytes_at rsegs m (bv_unsigned sp + 0xa0) (le8 (Z_to_bv 64 (Z.lnot (bv_unsigned sp + 0xf0)))) ->
    bytes_at rsegs m (bv_unsigned sp + 0xc8) (le8 (Z_to_bv 64 (pp + POD_LEN_OFF))) ->
    bytes_at rsegs m (bv_unsigned sp + 0xd8) (le8 (Z_to_bv 64 pp)) ->
    stk rsegs m lo (bv_unsigned sp + FRAME_LOCALS) -> lo + MID_STACK <= bv_unsigned sp -> bv_unsigned sp mod 16 = 0 ->
    (forall a, lo <= a < bv_unsigned sp + FRAME_LOCALS -> seg_rom rsegs (wa a) = None) ->
    (forall a, RELRO_TBL <= a < RELRO_TBL_END -> mrd rsegs m (wa a) = seg_rom rsegs (wa a)) ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (ra' t0' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7' s10' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' (Z_to_bv 64 (Z.of_nat (length (snd (ent_build r))))) t2' s0 s1
                       a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7' (Z_to_bv 64 pp)
                       (Z_to_bv 64 (src + Z.of_nat (length r) - Z.of_nat (length (snd (ent_build r)))))
                       s10' (Z_to_bv 64 (pp + POD_LEN_OFF)) t3' t4' t5' t6')
                  F (Z_to_bv 64 ENT_JOIN) fc None m' (seg_rom rsegs) /\
         bytes_at rsegs m' (bv_unsigned sp + 0xe8) (ent_mem (fst (ent_build r))) /\
         munch [(bv_unsigned sp - MID_STACK, bv_unsigned sp); (bv_unsigned sp + 0x48, bv_unsigned sp + 0x50);
                (bv_unsigned sp + 0xe8, bv_unsigned sp + FRAME_LOCALS)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp + FRAME_LOCALS))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ENT_HEAD) fc None m (seg_rom rsegs)).
