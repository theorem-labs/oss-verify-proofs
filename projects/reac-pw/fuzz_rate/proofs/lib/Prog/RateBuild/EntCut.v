From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout.
Import ListNotations.
Open Scope Z_scope.

(** One turn of the builder's pod loop up to its pod_put test, as an evt: ent_build(&e, &in) inlined in
    LLVMFuzzerTestOneInput (plain image, pod.h:265-379, called at pod.h:427), from the loop head 0x13564 to the join
    0x13cec where the inlined pod_write_ent begins (pod.h:428). Ported from reac-pw/fuzz_role's
    Prog/RoleBuild/EntCut.v at rate's registers and frame cells. Statement
    text only.

    Registers at 0x13564 (what the turn reads there): s8 = src, the input cursor; s6 = |r|, the bytes left, r being
    the input bytes at src; and the constants pod_build's preheader set (0x132d4-0x1331c): s10 = sp + 0x158 (t[96]),
    s11 = sp + 0x120 (parts[4] and the digit buffer), s4 = 0xcccccccd << 32 (the multiplier of v / 10), s0 = 95 (the
    head-amp key's part clamp), s3 = 10; s1 = pp (kind 9's path, 0x135a0 .. 0x1396c .. 0x13764 .. 0x13ce4, does not
    reload it, and the join uses it as pp; kinds 0-8 overwrite s1 with (int8) kind at 0x135c0 and reload pp from the
    frame). The frame cells the join stubs reload: sp + 0x80 = pp (to s1), sp + 0x90 = -0x4001 (to t0),
    sp + 0x98 = -0x3ffd (to a7), sp + 0xb0 = pp + 0x4000 = &pp->len (to a6). Every other register is arbitrary.

    In order: memset(e = sp + 0xb8, 0, 104) (0x13570); kind = fuzz_u8; kind % 10 by multiply (0x13580-0x13594); kind
    9 by the branch to 0x1396c, kinds 0-8 by `jr a1` (0x135c4) through the nine 4-byte offsets at 0x10548 (.rodata);
    then the case's reads and stores into e (memcpy, memset, strlen; the vocab and odd_ch pointer tables of
    .data.rel.ro, the other tables and strings of .rodata). At 0x13cec, with (e, r') = ent_build r (Pod/Model.v):
    s5 = e's type and s6 = e's size (the inlined pod_write_ent puts them), s8 = the cursor after the turn, the cell
    sp + 0xa8 = |r'| (reloaded to s6 at 0x13d8c), e's 104 bytes at sp + 0xb8 as Layout.ent_mem lays them out (type,
    size, body, zeros), a6 = pp + 0x4000, a7 = -0x3ffd, t0 = -0x4001, s7 = 0x4000, s1 = pp; sp, gp, tp, s0, s2 (at),
    s3, s4, s9 (k), s10, s11, F and fc unchanged (no FP instruction in the turn; s2 and s9 are read after the join).
    The bytes changed: the callee stacks below sp (none of memset, memcpy and strlen uses one), the cells sp + 0x58
    (the cursor spill of the text kinds) and sp + 0xa8, and [sp + 0xb8, sp + 0x1b8): e, parts, ch[24] and t[96].

    Premises: r at src (src > 0), below the stack region; the stack region with the frame's locals (stk over
    [lo, sp + 0x1b8): present and writable), outside the image, sp 16-aligned; the .data.rel.ro tables vocab and
    odd_ch as in the image; mem_inv. *)

Definition ENT_HEAD : Z := 0x13564.
Definition ENT_JOIN : Z := 0x13cec.

Definition rb_ent_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (r : list byte) (src pp lo : Z),
    s8 = Z_to_bv 64 src -> s6 = Z_to_bv 64 (Z.of_nat (length r)) ->
    s10 = Z_to_bv 64 (bv_unsigned sp + 0x158) -> s11 = Z_to_bv 64 (bv_unsigned sp + 0x120) ->
    s4 = Z_to_bv 64 (0xcccccccd * 2^32) -> s0 = Z_to_bv 64 95 -> s3 = Z_to_bv 64 10 -> s1 = Z_to_bv 64 pp ->
    0 < src -> bytes_at rsegs m src r -> src + Z.of_nat (length r) <= lo ->
    bytes_at rsegs m (bv_unsigned sp + 0x80) (le8 (Z_to_bv 64 pp)) ->
    bytes_at rsegs m (bv_unsigned sp + 0x90) (le8 (Z_to_bv 64 (-0x4001))) ->
    bytes_at rsegs m (bv_unsigned sp + 0x98) (le8 (Z_to_bv 64 (-0x3ffd))) ->
    bytes_at rsegs m (bv_unsigned sp + 0xb0) (le8 (Z_to_bv 64 (pp + POD_LEN_OFF))) ->
    stk rsegs m lo (bv_unsigned sp + FRAME_LOCALS) -> lo + MID_STACK <= bv_unsigned sp -> bv_unsigned sp mod 16 = 0 ->
    (forall a, lo <= a < bv_unsigned sp + FRAME_LOCALS -> seg_rom rsegs (wa a) = None) ->
    (forall a, RELRO_TBL <= a < RELRO_TBL_END -> mrd rsegs m (wa a) = seg_rom rsegs (wa a)) ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (ra' t1' t2' a0' a1' a2' a3' a4' a5' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp (Z_to_bv 64 (-0x4001)) t1' t2' s0 (Z_to_bv 64 pp) a0' a1' a2' a3' a4' a5'
                       (Z_to_bv 64 (pp + POD_LEN_OFF)) (Z_to_bv 64 (-0x3ffd)) s2 s3 s4
                       (Z_to_bv 64 (e_type (fst (ent_build r)))) (Z_to_bv 64 (e_size (fst (ent_build r))))
                       (Z_to_bv 64 0x4000)
                       (Z_to_bv 64 (src + Z.of_nat (length r) - Z.of_nat (length (snd (ent_build r)))))
                       s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 ENT_JOIN) fc None m' (seg_rom rsegs) /\
         bytes_at rsegs m' (bv_unsigned sp + 0xa8) (le8 (Z_to_bv 64 (Z.of_nat (length (snd (ent_build r)))))) /\
         bytes_at rsegs m' (bv_unsigned sp + 0xb8) (ent_mem (fst (ent_build r))) /\
         munch [(bv_unsigned sp - MID_STACK, bv_unsigned sp); (bv_unsigned sp + 0x58, bv_unsigned sp + 0x60);
                (bv_unsigned sp + 0xa8, bv_unsigned sp + 0xb0); (bv_unsigned sp + 0xb8, bv_unsigned sp + FRAME_LOCALS)]
               m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp + FRAME_LOCALS))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ENT_HEAD) fc None m (seg_rom rsegs)).
