From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout.
Import ListNotations.
Open Scope Z_scope.

(** One turn of the builder's pod loop up to its stop test, as an evt: ent_build(&e, &in) inlined in
    LLVMFuzzerTestOneInput (UBSan image, pod.h:265-379, called at pod.h:427), from the loop head 0x13360 to the join
    0x13c48 where the stop test of pod.h:428 begins (then the call of pod_write_ent at 0x13c60). Statement text only.

    Registers at 0x13360 (what the turn reads there, and what it hands on): s9 = src, the input cursor, and s5 = src
    too (the path of an empty input keeps s5, and the code after the join reads the cursor from s5 and from s9);
    s1 = |r|, the bytes left, r being the input bytes at src; the constants pod_build's preheader set
    (0x130cc-0x1315c): s0 = 95 (the head-amp key's part clamp), s2 = 0xcccccccd << 32 (the multiplier of v / 10),
    s3 = 4, s10 = sp + 0x158 (t[96]); s7 = pp + 0x4000 = &pp->len and s8 = pp, which some cases use as scratch and
    reload from the cells sp + 0x78 and sp + 0x68. The frame cells the turn reads: sp + 0x8 = 0x15555556 (the
    multiplier of v / 3), sp + 0x50 = ~(sp + 0x140) and sp + 0x80 = ~(sp + 0xc0) (the bounds of the pointer-overflow
    checks on ch + k and e->body + n), sp + 0x68 = pp, sp + 0x78 = pp + 0x4000. Every other register is arbitrary.

    In order: memset(e = sp + 0xb8, 0, 104) (0x1336c); kind = fuzz_u8; kind % 10 by multiply (0x13384-0x1339c);
    kind 9 by the branch to 0x136cc, kinds 0-8 by `jr a1` (0x133cc) through the nine 4-byte offsets at 0x10548
    (.rodata); then the case's reads and stores into e (memcpy, memset, strlen; the vocab, odd_ch and param pointer
    tables of .data.rel.ro, the other tables and strings of .rodata). Its UBSan checks (39 branches to the `unimp` at
    0x14204: the cursor's p + 1 and p + n, the table indexes, e->body + n, r[k], ch + k) are not taken. At 0x13c48,
    with (e, r') = ent_build r (Pod/Model.v): s5 = s9 = the cursor after the turn, s1 = |r'|, e's 104 bytes at
    sp + 0xb8 as Layout.ent_mem lays them out (type, size, body, zeros), s7 and s8 as at the head; sp, gp, tp, s0, s2,
    s3, s10, s11 (k), F and fc unchanged (no FP instruction in the turn). The bytes changed: the callee stacks below
    sp (none of memset, memcpy and strlen uses one) and [sp + 0xb8, sp + 0x1b8): e, parts, ch[24] and t[96].

    Premises: r at src (src > 0), below the stack region; the stack region with the frame's locals (stk over
    [lo, sp + 0x1b8): present and writable), outside the image, sp 16-aligned; the .data.rel.ro tables as in the
    image; mem_inv. *)

Definition ENT_HEAD : Z := 0x13360.
Definition ENT_JOIN : Z := 0x13c48.

Definition rb_ent_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (r : list byte) (src pp lo : Z),
    s9 = Z_to_bv 64 src -> s5 = Z_to_bv 64 src -> s1 = Z_to_bv 64 (Z.of_nat (length r)) ->
    s0 = Z_to_bv 64 95 -> s2 = Z_to_bv 64 (0xcccccccd * 2^32) -> s3 = Z_to_bv 64 4 ->
    s10 = Z_to_bv 64 (bv_unsigned sp + 0x158) ->
    s7 = Z_to_bv 64 (pp + POD_LEN_OFF) -> s8 = Z_to_bv 64 pp ->
    0 < src -> bytes_at rsegs m src r -> src + Z.of_nat (length r) <= lo ->
    bytes_at rsegs m (bv_unsigned sp + 0x8) (le8 (Z_to_bv 64 0x15555556)) ->
    bytes_at rsegs m (bv_unsigned sp + 0x50) (le8 (Z_to_bv 64 (Z.lnot (bv_unsigned sp + 0x140)))) ->
    bytes_at rsegs m (bv_unsigned sp + 0x68) (le8 (Z_to_bv 64 pp)) ->
    bytes_at rsegs m (bv_unsigned sp + 0x78) (le8 (Z_to_bv 64 (pp + POD_LEN_OFF))) ->
    bytes_at rsegs m (bv_unsigned sp + 0x80) (le8 (Z_to_bv 64 (Z.lnot (bv_unsigned sp + 0xc0)))) ->
    stk rsegs m lo (bv_unsigned sp + FRAME_LOCALS) -> lo + MID_STACK <= bv_unsigned sp -> bv_unsigned sp mod 16 = 0 ->
    (forall a, lo <= a < bv_unsigned sp + FRAME_LOCALS -> seg_rom rsegs (wa a) = None) ->
    (forall a, RELRO_TBL <= a < RELRO_TBL_END -> mrd rsegs m (wa a) = seg_rom rsegs (wa a)) ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 (Z.of_nat (length (snd (ent_build r)))))
                       a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4'
                       (Z_to_bv 64 (src + Z.of_nat (length r) - Z.of_nat (length (snd (ent_build r)))))
                       s6' s7 s8
                       (Z_to_bv 64 (src + Z.of_nat (length r) - Z.of_nat (length (snd (ent_build r)))))
                       s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 ENT_JOIN) fc None m' (seg_rom rsegs) /\
         bytes_at rsegs m' (bv_unsigned sp + 0xb8) (ent_mem (fst (ent_build r))) /\
         munch [(bv_unsigned sp - MID_STACK, bv_unsigned sp); (bv_unsigned sp + 0xb8, bv_unsigned sp + FRAME_LOCALS)]
               m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp + FRAME_LOCALS))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ENT_HEAD) fc None m (seg_rom rsegs)).
