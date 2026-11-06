From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout.
Import ListNotations.
Open Scope Z_scope.

(** One turn of the builder's pod loop up to its pod_put test, as an evt: ent_build(&e, &in) inlined in
    LLVMFuzzerTestOneInput (plain image, pod.h:265-379, called at pod.h:427), from the loop head 0x1340c to the join
    0x13618 where the inlined pod_write_ent begins (pod.h:428). Statement text only.

    Registers at 0x1340c (what the turn reads there): s6 = src, the input cursor; s4 = |r|, the bytes left, r being
    the input bytes at src; and the constants pod_build's preheader set (0x131b4-0x131f4): s0 = sp + 0x150 (t[96]),
    s10 = sp + 0x118 (parts[4] and the digit buffer), s9 = 0xcccccccd << 32 (the multiplier of v / 10), s7 = 95 (the
    head-amp key's part clamp), s11 = 10; s2 = pp + 0x4000 = &pp->len (kind 9's path, 0x13900 .. 0x13938 .. 0x13610,
    does not reload it, and the join uses it as &pp->len). The frame cells the join stubs reload:
    sp + 0x50 = pp + 0x4000 (to s2), sp + 0x58 = pp (to s5), sp + 0x70 = -0x4001 (to a7), sp + 0x78 = -0x3ffd (to a6).
    Every other register is arbitrary.

    In order: memset(e = sp + 0x90, 0, 104) (0x13418); kind = fuzz_u8; kind % 10 by multiply (0x13428-0x1343c); kind
    9 by the branch to 0x13900, kinds 0-8 by `jr a1` (0x1346c) through the nine 4-byte offsets at 0x10510 (.rodata);
    then the case's reads and stores into e (memcpy, memset, strlen; the vocab and odd_ch pointer tables of
    .data.rel.ro, the other tables and strings of .rodata). At 0x13618, with (e, r') = ent_build r (Pod/Model.v):
    s3 = e's type and s4 = e's size (the inlined pod_write_ent puts them), s6 = the cursor after the turn, the cell
    sp + 0x88 = |r'| (reloaded to s4 at 0x136bc), e's 104 bytes at sp + 0x90 as Layout.ent_mem lays them out (type,
    size, body, zeros), s2 = pp + 0x4000, s5 = pp, a6 = -0x3ffd, a7 = -0x4001; sp, gp, tp, s0, s1 (k), s7, s8, s9, s10,
    s11, F and fc unchanged (no FP instruction in the turn; s1 and s8 are read after the join).
    The bytes changed: the callee stacks below sp (none of memset, memcpy and strlen uses one), the cell sp + 0x28
    (the cursor spill of kinds 1 and 5), and [sp + 0x88, sp + 0x1b0): the cell |r'|, e, parts, ch[24] and t[96].

    Premises: r at src (src > 0), below the stack region; the stack region with the frame's locals (stk over
    [lo, sp + 0x1b0): present and writable), outside the image, sp 16-aligned; the .data.rel.ro tables vocab and
    odd_ch as in the image; mem_inv. *)

Definition ENT_HEAD : Z := 0x1340c.
Definition ENT_JOIN : Z := 0x13618.

Definition rb_ent_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (r : list byte) (src pp lo : Z),
    s6 = Z_to_bv 64 src -> s4 = Z_to_bv 64 (Z.of_nat (length r)) ->
    s0 = Z_to_bv 64 (bv_unsigned sp + 0x150) -> s10 = Z_to_bv 64 (bv_unsigned sp + 0x118) ->
    s9 = Z_to_bv 64 (0xcccccccd * 2^32) -> s7 = Z_to_bv 64 95 -> s11 = Z_to_bv 64 10 ->
    s2 = Z_to_bv 64 (pp + POD_LEN_OFF) ->
    0 < src -> bytes_at rsegs m src r -> src + Z.of_nat (length r) <= lo ->
    bytes_at rsegs m (bv_unsigned sp + 0x50) (le8 (Z_to_bv 64 (pp + POD_LEN_OFF))) ->
    bytes_at rsegs m (bv_unsigned sp + 0x58) (le8 (Z_to_bv 64 pp)) ->
    bytes_at rsegs m (bv_unsigned sp + 0x70) (le8 (Z_to_bv 64 (-0x4001))) ->
    bytes_at rsegs m (bv_unsigned sp + 0x78) (le8 (Z_to_bv 64 (-0x3ffd))) ->
    stk rsegs m lo (bv_unsigned sp + FRAME_LOCALS) -> lo + MID_STACK <= bv_unsigned sp -> bv_unsigned sp mod 16 = 0 ->
    (forall a, lo <= a < bv_unsigned sp + FRAME_LOCALS -> seg_rom rsegs (wa a) = None) ->
    (forall a, RELRO_TBL <= a < RELRO_TBL_END -> mrd rsegs m (wa a) = seg_rom rsegs (wa a)) ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5'
                       (Z_to_bv 64 (-0x3ffd)) (Z_to_bv 64 (-0x4001)) (Z_to_bv 64 (pp + POD_LEN_OFF))
                       (Z_to_bv 64 (e_type (fst (ent_build r)))) (Z_to_bv 64 (e_size (fst (ent_build r))))
                       (Z_to_bv 64 pp)
                       (Z_to_bv 64 (src + Z.of_nat (length r) - Z.of_nat (length (snd (ent_build r)))))
                       s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 ENT_JOIN) fc None m' (seg_rom rsegs) /\
         bytes_at rsegs m' (bv_unsigned sp + 0x88) (le8 (Z_to_bv 64 (Z.of_nat (length (snd (ent_build r)))))) /\
         bytes_at rsegs m' (bv_unsigned sp + 0x90) (ent_mem (fst (ent_build r))) /\
         munch [(bv_unsigned sp - MID_STACK, bv_unsigned sp); (bv_unsigned sp + 0x28, bv_unsigned sp + 0x30);
                (bv_unsigned sp + 0x88, bv_unsigned sp + FRAME_LOCALS)]
               m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp + FRAME_LOCALS))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ENT_HEAD) fc None m (seg_rom rsegs)).
