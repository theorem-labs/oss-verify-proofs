(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_wire/lib/U/Prog/LLVMFuzzerTestOneInput_cfb.v, with its module paths changed; 532 of its 580 lines of code are new or changed and 97 lines of the source are left out. *)
(* Modified by Theorem Labs: reac-repacer/fuzz_uci's lib/Prog/LLVMFuzzerTestOneInput_fr.v (6874bc78b1f) at fuzz_wire's
   module paths; lf_guard_img reads this image's __stack_chk_guard GOT slot 0x1cef0; lf_fr_call_x is new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_wire/lib/Prog/LLVMFuzzerTestOneInput_fr.v, with its module paths and module names changed; 455 of its 574 lines of code are new or changed and 461 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/U/Prog/Seg/Tac_slot.v, with its module names changed; 218 of its 245 lines of code are new or changed and 547 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/U/Prog/Seg/M01.v, with its module paths and module names changed; 201 of its 230 lines of code are new or changed and 216 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells FP.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Model Layout Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog Require Import reac_headamp_prop_parse_result_c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog Require Import SlotFR SlotInv.
Import ListNotations.
Open Scope Z_scope.

(** LLVMFuzzerTestOneInput of fuzz_headamp.c:311-360 (6404 bytes, 1601 instructions at 0x12fa8 in the UBSan image;
    frame 608 bytes; U/FrameAPI.ENTRY; the UBSan ELF, unstripped sha256 1d123858383d3510..., pinned 0516fd55d25d...).
    The plain contract (lib/Prog/LLVMFuzzerTestOneInput_c.v) with the UBSan numbers: the frame's obligation
    U/Prog/SlotFR.slot_goal (from U/FrameAPI.frame_ubsan), split at the cuts of U/Prog/SlotInv.v into S_E01, S_M01,
    S_M02, S_M03, S_M04, S_X01 below, plus the n >= 2^26 run (headamp_early_contract). The whole function promises
    lib_contract_g's lib_post, as in the plain build. The lifts are the plain file's: b1_fr_hb for the runs that write
    one block (M01 pp, M02 pod, M04a first), and for M03 and M04b, whose parses write errno through strtol (role's
    b1_fr_hb / sl_fr_run keep every byte outside the window and the block; FR itself lets errno change), the errno
    variants of U/Prog/Seg/Tac_errno.v (beside the kit): b1_fr_hb_errno / sl_fr_run_hb_errno / sl_mid_fp_hb_errno
    (write set: the window, one block, [errno_addr B, errno_addr B + 4)), te_fp3, te_parse_tp, te_parse_writes.

    UBSan checks: 94 trap branches in this function, all to the `unimp` at 0x148a0 ("j" sites: `bltu/bgeu x,y,8`
    over a `j 0x148a0`). Two are S_E01's (0x13010, 0x13058: data + 1, data + 2 wrap; data is a user block above 4096
    or `empty` with n = 0, so neither wraps). 68 lie in headamp_build_contract's range, the same 68 as role's
    role_build (the cursor's pointer-overflow checks, pp & 7, the header and buf[len] bounds, the table index checks,
    e->body + n, r[k], ch + k, the record copy's n_ent++ / ent bound / object size, the corruption's buf[off + k]),
    each dead by a premise (src > 0 and the input below 2^64; pp 16-aligned with its block below lo; len <= 5440 and
    e_size <= 45 of the model, Pod/Model.v pod_build_wf; sp + 0x1d8 < lo + 65536 <= 2^64). 24 lie in
    headamp_check_contract's range (&out[cap] 0x14160; ent index and pointer 0x14298 /
    0x1429c; body + size - 1 0x142c0; at++ in pod_next_pair 0x14304; keys++ 0x1436c; k + 13 0x1438c; rest + i
    0x143b4 / 0x143e0 / 0x14434; acc * 10 0x1441c; rest + used 0x14458 / 0x14464 / 0x14474; &ent[v] 0x14558 /
    0x1455c; the float-cast 0x14624 / 0x1463c; t + 1 0x146c0, t - 1 0x14694; x->cell[n] 0x14708 / 0x14720 / 0x14734 /
    0x14748), each dead by a bound of the record in pp (n_ent <= 32, e_size <= 45 with the body's NUL at
    body[size - 1]), of the cursor (acc <= 1000000 before `acc * 10`), of cap (n < cap <= 9) or of the binary32
    range test (-1 <= f <= 256, so |t| <= 256; C2 = -2^63 - 1 for the cast check). pod_write_ent's 10 traps are its
    contract's (U/Prog/pod_write_ent_c.v), the parse's 17 and the checks' 11 their contracts'.

    The frame bounds: MID_STACK = 0x90 + 0x120 + 0x50 = 512 (the parse chain, U PARSE_STACK; the soft-float callees use
    less); FRAME_LOCALS = 0x1d8: the locals [sp, sp + 0x1d8) (x at sp + 0xb8, res at sp + 0x178, the builder's t to
    sp + 0x1d8; the fsd saves of fs0-fs3 at [sp + 0x1d8, sp + 0x1f8), the integer saves at [sp + 0x1f8, sp + 0x260) =
    [S - 104, S)); the .data.rel.ro tables the builder reads: vocab (0x1f260, 9 pointers), odd_ch (0x1f2a8, 14
    pointers) and param (0x1f318, 8 pointers), inside U/FrameAPI.frame_RELRO [0x1f250, 0x1f3e8).

    The callee contracts the walks take as premises (the released forms relocated to headamp's UBSan image, or written
    in this directory), the plain file's with the UBSan addresses:
      S_E01: malloc through the frame's malloc_contract (ms_malloc = 0x1693c) by b1_malloc_call (hb = []).
      headamp_build_contract (M01): memset_contract (U/Prog/memset_c.v, 0x1db4c: 0x130a4, 0x132e8, 0x134c8, 0x13bbc,
             0x13efc), memcpy_contract (U/Prog/memcpy_c.v, 0x1d748: 0x13760, 0x138b0, 0x13954, 0x13b44, 0x13b74,
             0x13c40, 0x13cf8, 0x13e50), strlen_contract (U/Prog/strlen_c.v, 0x1dc7c: 0x1392c, 0x13b24, 0x13c30),
             pod_write_ent_contract (U/Prog/pod_write_ent_c.v, 0x14b5c, role's relocated by +0x838; called at
             0x132fc, 0x13e08, 0x13f14 with a0 = s8 = pp, a1 = sp + 0xb8 = &e), and the shared model's pod_build and
             pp_bytes with their step lemmas.
      S_M01: malloc by b1_malloc_call (hb = [(pp, 19744)], request len <= 5440).
      headamp_dup_pod_contract (M02): memcpy_contract at 0x14100 (pod <- pp->buf, len bytes).
      S_M02: malloc by b1_malloc_call (hb = [(pod, len); (pp, 19744)], request 3 cap + 3 <= 30).
      headamp_check_contract (M03): memset_contract (0x14128: out; 0x141a4: x = sp + 0xb8, 0, 0x88);
             reac_headamp_prop_parse_result_contract (U/Prog/reac_headamp_prop_parse_result_c.v, 0x14158:
             a0 = (null ? 0 : pod) from the cell sp + 0x10, a1 = out, a2 = cap, a3 = sp + 0x178; U/Prog/HeadSites.v
             parse_site_check); check_no_overrun_contract (0x1416c), check_count_contract (0x1417c),
             check_cells_valid_contract (0x14188) (U/Prog/check_*_c.v); when pp->corrupt = 0 (0x1418c-0x14194):
             expect_of inlined (0x14198-0x14780) with strncmp_contract (U/Prog/strncmp_c.v, 0x1dd0c, at 0x14330),
             strcmp_contract (U/Prog/strcmp_c.v, 0x1dc44, at 0x1448c / 0x144a0 / 0x144b4), and pod_nearest inlined
             (0x145ec-0x146f0) with the soft-float contracts relocated from role's CJ/RL/G (C_extendsftf2.v
             extendsftf2_contract, 0x152f8, at 0x14604; G_getf2.v getf2_contract, __gttf2 = __getf2 0x1523c, at
             0x14638 (the float-cast check against C2 = -2^63 - 1) and 0x14670 (0.5L); C_floatditf.v
             floatditf_contract, 0x15454, at 0x14648; G_subtf3.v subtf3_contract, 0x15578, at 0x1465c; G_letf2.v
             letf2_contract, __lttf2 = __letf2 0x15174, at 0x14688; each keeps F: f in fs0, -1.0f / 256.0f / 2^63
             in fs1 / fs2 / fs3 survive the six calls), giving x = x_bytes (expect_model null cap r);
             check_object_contract (0x14790), check_cells_contract (0x147a0), and for rc >= 0 (0x147a4)
             check_keys_contract (0x147b0), check_refusal_contract (0x147bc) (Pod/Headamp.v parse_props_build;
             U/Prog/HeadSites.v); first's size (0x147c0-0x147d8).
      S_M03: malloc by b1_malloc_call (hb = [out; pod; pp], request first_req rc <= 27).
      headamp_dup_first_contract (M04a): memcpy_contract at 0x147f8 when rc > 0.
      headamp_plain_contract (M04b): memset_contract (0x14808), reac_headamp_prop_parse_contract
             (U/Prog/reac_headamp_prop_parse_c.v, 0x14cc8 via 0x14818; U/Prog/HeadSites.v parse_site_plain),
             check_plain_contract (U/Prog/check_plain_c.v, 0x14828).
      S_X01: free(first) 0x14830, free(out) 0x14838, free(pod) 0x14840, free(pp) 0x14848 (pp from the cell sp + 0x70,
             0x14844), through the frame's free_contract (ms_free = 0x167fc) by b8_free_call, each with hb1 = [].
    Statement text only: no function is proved here. *)

Definition HEAD_BUILD : Z := 0x13090.
Definition HEAD_MALLOC2 : Z := 0x140e0.
Definition HEAD_DUP_POD : Z := 0x140e4.
Definition HEAD_MALLOC3 : Z := 0x14114.
Definition HEAD_CHECK : Z := 0x14118.
Definition HEAD_MALLOC4 : Z := 0x147dc.
Definition HEAD_DUP_FIRST : Z := 0x147e0.
Definition HEAD_PLAIN : Z := 0x147fc.
Definition HEAD_FREE : Z := 0x1482c.
(* The deepest callee stack below the harness sp: the parse chain, 0x90 + 0x120 + 0x50 = 512 bytes. *)
Definition MID_STACK : Z := PARSE_STACK.
(* The harness frame's locals below its FP and integer saves: [sp, sp + 0x1d8). *)
Definition FRAME_LOCALS : Z := 0x1d8.
(* The absolute-pointer tables of .data.rel.ro the builder reads: vocab (0x1f260, 9 pointers), odd_ch (0x1f2a8, 14
   pointers) and param (0x1f318, 8 pointers), inside U/FrameAPI.frame_RELRO [0x1f250, 0x1f3e8). *)
Definition RELRO_TBL : Z := 0x1f260.
Definition RELRO_TBL_END : Z := 0x1f358.

(** ** The n >= 2^26 run, stated
    0x12fa8 `addi sp,sp,-0x260`; the thirteen saves (0x12fac-0x12fdc) and four fsd of fs0-fs3 (0x12fe0-0x12fec);
    0x12ff0 `srli a2,a1,26`; 0x12ff4 `beqz a2` not taken; 0x12ff8 `j 0x1484c`; `mv a0,zero`, the thirteen restores,
    four fld of fs0-fs3 (0x14884-0x14890), `addi sp,sp,0x260`, `ret` (0x1484c-0x14898). No call, no trap, no cut. The
    plain statement with the 608-byte frame. *)
Definition headamp_early_contract : Prop :=
  forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S lo : Z),
    stk rsegs m lo S -> lo + 608 <= S -> S < 2 ^ 64 -> mem_inv rsegs m ->
    2 ^ 26 <= bv_unsigned a1 ->
    evt rsegs
      (fun ms' => exists (sp' a2' : word) (F' : bvmap 5 word) (m' : word -> option byte),
         ms' = MS (mkR ra sp' gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2' a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F' (ret_pc ra) fc None m' (seg_rom rsegs) /\
         sp' = Z_to_bv 64 S /\
         munch [(S - 608, S)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo S)
      (MS (mkR ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ENTRY) fc None m (seg_rom rsegs)).

(** ** M01, the builder segment as an evt: [0x13090, 0x140e0)
    From malloc(pp)'s return (0x13090 `bnez a0`; pp <> 0) to the second malloc's call (0x140e0 `jal malloc`, not
    executed). Registers at 0x13090 as U/Prog/SlotInv.Inv_K13090 names them: a0 = pp, s6 = src, s2 = the bytes left,
    s3 = cap, the cell sp + 0x10 = 1 - null, s1 = 19744, s0 = 0x5000. In order: memset(pp, 0, 19744) (0x130a4); the
    header, with the cells sp + 0x8 := cap (0x1312c), sp + 0x68 := pp + 0x4d14 (0x13200), sp + 0x70 := pp (0x13208),
    sp + 0x78 := pp + 0x4000 (0x1320c); the property loop (head 0x132a8), the Struct pod loop (head 0x134bc) with
    `jr a1` at 0x1352c through 0x10520, the pod_write_ent calls, the record copy, the patches; the top patch and the
    corruption (0x13fb8-0x140d4); len = pp->len (0x13fb8 / 0x140cc) and a0 = len + (len = 0) (0x140d8-0x140dc); no
    trap reached. It ends at 0x140e0 with a0 = s3 = len, s7 = pp + 0x4000, s8 = pp, the cells sp + 0x8 = cap,
    sp + 0x10 = 1 - null, sp + 0x68 = pp + 0x4d14, sp + 0x70 = pp, sp + 0x78 = pp + 0x4000, the pp block = pp_bytes of
    the record, sp, gp, tp, F, fc unchanged, and no byte changed outside the callees' stack below sp, the frame's
    locals [sp, sp + 0x1d8) and the pp block. Premises as the plain evt's, with s3 = cap and the null cell. *)
Definition headamp_build_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (rest junk : list byte) (nl cap src pp lo : Z),
    a0 = Z_to_bv 64 pp -> pp <> 0 -> pp mod 16 = 0 ->
    s6 = Z_to_bv 64 src -> s2 = Z_to_bv 64 (Z.of_nat (length rest)) ->
    s3 = Z_to_bv 64 cap -> 0 <= cap <= 9 -> 0 <= nl <= 1 ->
    bytes_at rsegs m (bv_unsigned sp + 0x10) (le8 (Z_to_bv 64 (1 - nl))) ->
    s1 = Z_to_bv 64 POD_PROPS -> s0 = Z_to_bv 64 0x5000 ->
    0 < src -> bytes_at rsegs m src rest ->
    rw_cells rsegs m pp [CB (Z.to_nat POD_PROPS) junk] ->
    (forall a, pp <= a < pp + POD_PROPS -> seg_rom rsegs (wa a) = None) ->
    (src + Z.of_nat (length rest) <= pp \/ pp + POD_PROPS <= src) ->
    src + Z.of_nat (length rest) <= lo -> pp + POD_PROPS <= lo ->
    stk rsegs m lo (bv_unsigned sp + FRAME_LOCALS) -> lo + MID_STACK <= bv_unsigned sp -> bv_unsigned sp mod 16 = 0 ->
    (forall a, lo <= a < bv_unsigned sp + FRAME_LOCALS -> seg_rom rsegs (wa a) = None) ->
    (forall a, RELRO_TBL <= a < RELRO_TBL_END -> mrd rsegs m (wa a) = seg_rom rsegs (wa a)) ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (ra' t0' t1' t2' s0' s1' a1' a2' a3' a4' a5' a6' a7' s2' s4' s5' s6' s9' s10' s11' t3' t4' t5'
                          t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0' s1' (Z_to_bv 64 (head_len rest)) a1' a2' a3' a4' a5' a6' a7'
                       s2' (Z_to_bv 64 (head_len rest)) s4' s5' s6' (Z_to_bv 64 (pp + POD_LEN_OFF)) (Z_to_bv 64 pp)
                       s9' s10' s11' t3' t4' t5' t6')
                  F (Z_to_bv 64 HEAD_MALLOC2) fc None m' (seg_rom rsegs) /\
         bytes_at rsegs m' pp (pp_bytes (head_rec rest)) /\
         bytes_at rsegs m' (bv_unsigned sp + 0x8) (le8 (Z_to_bv 64 cap)) /\
         bytes_at rsegs m' (bv_unsigned sp + 0x10) (le8 (Z_to_bv 64 (1 - nl))) /\
         bytes_at rsegs m' (bv_unsigned sp + 0x68) (le8 (Z_to_bv 64 (pp + POD_NENT_OFF))) /\
         bytes_at rsegs m' (bv_unsigned sp + 0x70) (le8 (Z_to_bv 64 pp)) /\
         bytes_at rsegs m' (bv_unsigned sp + 0x78) (le8 (Z_to_bv 64 (pp + POD_LEN_OFF))) /\
         munch [(bv_unsigned sp - MID_STACK, bv_unsigned sp + FRAME_LOCALS); (pp, pp + POD_PROPS)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp + FRAME_LOCALS))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 HEAD_BUILD) fc None m (seg_rom rsegs)).

(** ** M02, pod = fuzz_dup(pp->buf, len) as an evt: [0x140e4, 0x14114)
    From malloc(pod)'s return (0x140e4 `beqz a0`, not taken: pod <> 0) to out's malloc call (0x14114). Registers at
    0x140e4: a0 = pod, s3 = len, s8 = pp, the cell sp + 0x8 = cap. In order: s1 := pod (0x140e8); s2 := the byte at
    sp + 0x8 (0x140ec `lbu`); `beqz s3` not taken; memcpy(pod, pp, len) (0x14100); s0 := 3 cap, s4 := 3 cap + 3,
    a0 := s4 (0x14104-0x14110). It ends at 0x14114 with a0 = s4 = 3 cap + 3, s0 = 3 cap, s1 = pod, s2 = cap, every
    other s register as at 0x140e4 (s7 = pp + 0x4000, s8 = pp among them), F and fc unchanged, the pod block = buf r,
    and no byte changed outside the pod block. *)
Definition headamp_dup_pod_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (inp junk : list byte) (cap pp pod : Z),
    a0 = Z_to_bv 64 pod -> pod <> 0 ->
    s3 = Z_to_bv 64 (head_len inp) -> s8 = Z_to_bv 64 pp -> 0 <= cap <= 9 ->
    bytes_at rsegs m (bv_unsigned sp + 0x8) (le8 (Z_to_bv 64 cap)) ->
    bytes_at rsegs m pp (pp_bytes (head_rec inp)) ->
    rw_cells rsegs m pod [CB (Z.to_nat (head_len inp)) junk] ->
    (pod + head_len inp <= pp \/ pp + POD_PROPS <= pod) ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' (Z_to_bv 64 (3 * cap)) (Z_to_bv 64 pod) (Z_to_bv 64 (OUT_LEN cap))
                       a1' a2' a3' a4' a5' a6' a7'
                       (Z_to_bv 64 cap) s3 (Z_to_bv 64 (OUT_LEN cap)) s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 HEAD_MALLOC3) fc None m' (seg_rom rsegs) /\
         bytes_at rsegs m' pod (buf (head_rec inp)) /\
         munch [(pod, pod + head_len inp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 HEAD_DUP_POD) fc None m (seg_rom rsegs)).

(** ** M03, the checking segment as an evt: [0x14118, 0x147dc)
    From malloc(out)'s return (0x14118 `beqz a0`, not taken: out <> 0) to first's malloc call (0x147dc). Registers
    at 0x14118 as U/Prog/SlotInv.Inv_K14118 names them: a0 = out, s0 = 3 cap, s1 = pod, s2 = cap, s4 = 3 cap + 3,
    s7 = pp + 0x4000; the cells sp + 0x10 = 1 - null, sp + 0x68 = pp + 0x4d14, sp + 0x70 = pp, sp + 0x78 =
    pp + 0x4000; the pp block = pp_bytes r, the pod block = buf r. In order: s3 := out (0x1411c); memset(out, 0xa5,
    3 cap + 3) (0x14128); res := 0x5a x 12 (0x1412c-0x14138: .rodata 0x10518, `sd 0x178(sp)`, `sw 0x180(sp)`);
    s8 := 1 - null (0x1413c), s5 := (null ? 0 : pod) (0x14140-0x14144); rc := reac_headamp_prop_parse_result(s5,
    out, cap, sp + 0x178) (0x14158), s6 := rc (0x14164); check_no_overrun(out + 3 cap) (0x1416c), check_count
    (0x1417c), check_cells_valid (0x14188); when pp->corrupt = 0 (0x1418c-0x14194): expect_of inlined into
    x = sp + 0xb8 (0x14198-0x14780), check_object (0x14790), check_cells (0x147a0), and for rc >= 0 check_keys
    (0x147b0), check_refusal (0x147bc); s8 := 3 max(rc, 0), a0 := s8 + (s8 = 0) (0x147c0-0x147d8); no trap reached.
    It ends at 0x147dc with a0 = first_req rc, s1 = pod, s2 = cap, s3 = out, s4 = 3 cap + 3, s5 = (null ? 0 : pod),
    s6 = rc, s8 = 3 max(rc, 0), the cell sp + 0x70 = pp, out = out_after cap o, errno still a cell, sp, gp, tp
    unchanged, at some FP state with frm = 0, and no byte changed outside the callees' stack below sp, the frame's
    locals, the out block and errno. Premises and property as the plain evt's, with the UBSan cells. *)
Definition headamp_check_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (inp junk : list byte) (nl cap pp pod out lo : Z) (ev can : word),
    a0 = Z_to_bv 64 out -> 0 < out -> out mod 16 = 0 ->
    s0 = Z_to_bv 64 (3 * cap) -> s1 = Z_to_bv 64 pod -> s2 = Z_to_bv 64 cap -> s4 = Z_to_bv 64 (OUT_LEN cap) ->
    s7 = Z_to_bv 64 (pp + POD_LEN_OFF) -> 0 <= nl <= 1 -> 0 <= cap <= 9 ->
    bytes_at rsegs m (bv_unsigned sp + 0x10) (le8 (Z_to_bv 64 (1 - nl))) ->
    bytes_at rsegs m (bv_unsigned sp + 0x68) (le8 (Z_to_bv 64 (pp + POD_NENT_OFF))) ->
    bytes_at rsegs m (bv_unsigned sp + 0x70) (le8 (Z_to_bv 64 pp)) ->
    bytes_at rsegs m (bv_unsigned sp + 0x78) (le8 (Z_to_bv 64 (pp + POD_LEN_OFF))) ->
    bytes_at rsegs m pp (pp_bytes (head_rec inp)) ->
    0 < pod -> pod mod 16 = 0 -> bytes_at rsegs m pod (buf (head_rec inp)) ->
    rw_cells rsegs m out [CB (Z.to_nat (OUT_LEN cap)) junk] ->
    (forall a, out <= a < out + OUT_LEN cap -> seg_rom rsegs (wa a) = None) ->
    (out + OUT_LEN cap <= pod \/ pod + head_len inp <= out) ->
    (out + OUT_LEN cap <= pp \/ pp + POD_PROPS <= out) ->
    (pod + head_len inp <= pp \/ pp + POD_PROPS <= pod) ->
    out + OUT_LEN cap <= lo -> pod + head_len inp <= lo -> pp + POD_PROPS <= lo ->
    stk rsegs m lo (bv_unsigned sp + FRAME_LOCALS) -> lo + MID_STACK <= bv_unsigned sp -> bv_unsigned sp mod 16 = 0 ->
    (forall a, lo <= a < bv_unsigned sp + FRAME_LOCALS -> seg_rom rsegs (wa a) = None) ->
    rw_cells rsegs m (PARSE_ERRNO tp) [C4 ev] ->
    disjoint_from [(lo, bv_unsigned sp + FRAME_LOCALS); (pod, pod + head_len inp); (out, out + OUT_LEN cap);
                   (pp, pp + POD_PROPS)] (PARSE_ERRNO tp) 4 ->
    bytes_at rsegs m PARSE_SSP_GOT (le8 (Z_to_bv 64 PARSE_SSP_GUARD)) ->
    bytes_at rsegs m PARSE_SSP_GUARD (le8 can) ->
    disjoint_from [(lo, bv_unsigned sp + FRAME_LOCALS); (out, out + OUT_LEN cap);
                   (PARSE_ERRNO tp, PARSE_ERRNO tp + 4)] PARSE_SSP_GOT 8 ->
    disjoint_from [(lo, bv_unsigned sp + FRAME_LOCALS); (out, out + OUT_LEN cap);
                   (PARSE_ERRNO tp, PARSE_ERRNO tp + 4)] PARSE_SSP_GUARD 8 ->
    frm0 fc -> mem_inv rsegs m -> MemNorm.task_mem rsegs m ->
    evt rsegs
      (fun ms' => exists (ra' t0' t1' t2' s0' a1' a2' a3' a4' a5' a6' a7' s7' s9' s10' s11' t3' t4' t5' t6' : word)
                         (F' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte) (ev' : word),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0' (Z_to_bv 64 pod)
                       (Z_to_bv 64 (first_req (ans_rc (head_ans nl cap inp)))) a1' a2' a3' a4' a5' a6' a7'
                       (Z_to_bv 64 cap) (Z_to_bv 64 out) (Z_to_bv 64 (OUT_LEN cap))
                       (Z_to_bv 64 (if nl =? 1 then 0 else pod)) (Z_to_bv 64 (ans_rc (head_ans nl cap inp))) s7'
                       (Z_to_bv 64 (3 * Z.max (ans_rc (head_ans nl cap inp)) 0)) s9' s10' s11' t3' t4' t5' t6')
                  F' (Z_to_bv 64 HEAD_MALLOC4) fc' None m' (seg_rom rsegs) /\
         frm0 fc' /\
         bytes_at rsegs m' out (out_after cap (head_ans nl cap inp)) /\
         bytes_at rsegs m' (bv_unsigned sp + 0x70) (le8 (Z_to_bv 64 pp)) /\
         rw_cells rsegs m' (PARSE_ERRNO tp) [C4 ev'] /\
         munch [(bv_unsigned sp - MID_STACK, bv_unsigned sp + FRAME_LOCALS); (out, out + OUT_LEN cap);
                (PARSE_ERRNO tp, PARSE_ERRNO tp + 4)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp + FRAME_LOCALS))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 HEAD_CHECK) fc None m (seg_rom rsegs)).

(** ** M04a, first = fuzz_dup(out, 3 max(rc, 0)) past its malloc: [0x147e0, 0x147fc)
    The plain evt with the UBSan pcs: 0x147e0 `beqz a0` not taken, s7 := first (0x147e4), `blez s6` (0x147e8), for
    rc > 0 memcpy(first, out, 3 rc) (0x147f8). *)
Definition headamp_dup_first_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (w junk : list byte) (rc out first : Z),
    a0 = Z_to_bv 64 first -> first <> 0 ->
    s3 = Z_to_bv 64 out -> s6 = Z_to_bv 64 rc -> - 2 ^ 31 <= rc < 2 ^ 31 -> s8 = Z_to_bv 64 (3 * Z.max rc 0) ->
    (0 < rc -> Z.of_nat (length w) = 3 * rc /\ bytes_at rsegs m out w) ->
    rw_cells rsegs m first [CB (Z.to_nat (first_req rc)) junk] ->
    (first + first_req rc <= out \/ out + 3 * Z.max rc 0 <= first) ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 (Z_to_bv 64 first) s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 HEAD_PLAIN) fc None m' (seg_rom rsegs) /\
         (0 < rc -> bytes_at rsegs m' first w) /\
         munch [(first, first + first_req rc)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 HEAD_DUP_FIRST) fc None m (seg_rom rsegs)).

(** ** M04b, the plain parse and check_plain: [0x147fc, 0x1482c)
    The plain evt with the UBSan pcs: memset(out, 0xa5, 3 cap + 3) (0x14808); reac_headamp_prop_parse(s5, out, cap)
    (0x14818 -> 0x14cc8, `j 0x14cd0` with res = NULL); check_plain(plain, rc, out, first) (0x1481c-0x14828). *)
Definition headamp_plain_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (inp junk : list byte) (nl cap pod out first lo : Z) (ev can : word),
    s2 = Z_to_bv 64 cap -> s3 = Z_to_bv 64 out -> s4 = Z_to_bv 64 (OUT_LEN cap) ->
    s5 = Z_to_bv 64 (if nl =? 1 then 0 else pod) -> s6 = Z_to_bv 64 (ans_rc (head_ans nl cap inp)) ->
    s7 = Z_to_bv 64 first -> 0 <= nl <= 1 -> 0 <= cap <= 9 ->
    0 < pod -> pod mod 16 = 0 -> bytes_at rsegs m pod (buf (head_rec inp)) ->
    0 < out -> rw_cells rsegs m out [CB (Z.to_nat (OUT_LEN cap)) junk] ->
    (forall a, out <= a < out + OUT_LEN cap -> seg_rom rsegs (wa a) = None) ->
    bytes_at rsegs m first (ha_cells_bytes (ans_cells (head_ans nl cap inp))) ->
    (out + OUT_LEN cap <= pod \/ pod + head_len inp <= out) ->
    (first + 3 * Z.max (ans_rc (head_ans nl cap inp)) 0 <= out \/ out + OUT_LEN cap <= first) ->
    out + OUT_LEN cap <= lo -> pod + head_len inp <= lo ->
    first + 3 * Z.max (ans_rc (head_ans nl cap inp)) 0 <= lo ->
    stk rsegs m lo (bv_unsigned sp + FRAME_LOCALS) -> lo + MID_STACK <= bv_unsigned sp -> bv_unsigned sp mod 16 = 0 ->
    (forall a, lo <= a < bv_unsigned sp + FRAME_LOCALS -> seg_rom rsegs (wa a) = None) ->
    rw_cells rsegs m (PARSE_ERRNO tp) [C4 ev] ->
    disjoint_from [(lo, bv_unsigned sp + FRAME_LOCALS); (pod, pod + head_len inp); (out, out + OUT_LEN cap);
                   (first, first + 3 * Z.max (ans_rc (head_ans nl cap inp)) 0)] (PARSE_ERRNO tp) 4 ->
    bytes_at rsegs m PARSE_SSP_GOT (le8 (Z_to_bv 64 PARSE_SSP_GUARD)) ->
    bytes_at rsegs m PARSE_SSP_GUARD (le8 can) ->
    disjoint_from [(lo, bv_unsigned sp + FRAME_LOCALS); (out, out + OUT_LEN cap);
                   (PARSE_ERRNO tp, PARSE_ERRNO tp + 4)] PARSE_SSP_GOT 8 ->
    disjoint_from [(lo, bv_unsigned sp + FRAME_LOCALS); (out, out + OUT_LEN cap);
                   (PARSE_ERRNO tp, PARSE_ERRNO tp + 4)] PARSE_SSP_GUARD 8 ->
    frm0 fc -> mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (F' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte) (ev' : word),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (Z_to_bv 64 HEAD_FREE) fc' None m' (seg_rom rsegs) /\
         frm0 fc' /\
         rw_cells rsegs m' (PARSE_ERRNO tp) [C4 ev'] /\
         munch [(bv_unsigned sp - MID_STACK, bv_unsigned sp); (out, out + OUT_LEN cap);
                (PARSE_ERRNO tp, PARSE_ERRNO tp + 4)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp + FRAME_LOCALS))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 HEAD_PLAIN) fc None m (seg_rom rsegs)).

(** ** The segment statements (as the plain file's, with the UBSan cuts)
    S_E01, ENTRY -> K13090: the prologue (integer saves at [S - 104, S), the fsd of fs0-fs3 at [S - 136, S - 104)); n
      < 2^26; null into the cell sp + 0x10 as 1 - null, cap in s3 and the cursor (0x12ffc-0x1307c; the traps 0x13010,
      0x13058 dead); malloc(19744) at 0x1308c with ra = 0x13090 by b1_malloc_call (hb = [] to [(pp, 19744)]).
    S_M01, K13090 -> K140e4: headamp_build_contract (rest := g_rest g at g_src g, nl := g_null g, cap := g_cap g,
      lo := S - 65536, sp = S - 608), lifted by b1_fr_hb (pp); then `jal malloc` with a0 = g_len g by b1_malloc_call
      from hb = [(pp, 19744)], whose kept-bytes clause carries the pp block's bytes to the cut.
    S_M02, K140e4 -> K14118: headamp_dup_pod_contract with inp := g_rest g, lifted by b1_fr_hb (pod); then malloc(3
      g_cap g + 3) at 0x14114 by b1_malloc_call from hb = [(pod, g_len g); (pp, 19744)].
    S_M03, K14118 -> K147e0: headamp_check_contract on MemNorm.normalize_cj of the cut's memory (inp := g_rest g,
      nl := g_null g, cap := g_cap g; errno's cell from FR, the SSP cells ms_got_guard 0x1f3e8 / ms_guard 0x509d0),
      run and lifted by Tac_errno.v's sl_mid_fp_hb_errno_cj (the run on normalize_cj; out); then malloc(first_req rc)
      at 0x147dc by b1_malloc_call
      from hb = [out; pod; pp].
    S_M04, K147e0 -> K1482c: headamp_dup_first_contract lifted by b1_fr_hb (first), then headamp_plain_contract run
      and lifted by Tac_errno.v's sl_mid_fp_hb_errno (out).
    S_X01, K1482c -> RET: free(first) at 0x14830 (ra = 0x14834), free(out) at 0x14838 (ra = 0x1483c), free(pod) at
      0x14840 (ra = 0x14844), `ld a0,0x70(sp)` and free(pp) at 0x14848 (ra = 0x1484c), each by b8_free_call with
      hb1 = [] (each keeps the bytes of [S - 608, S)); `mv a0,zero`, the restores, the fld of fs0-fs3,
      `addi sp,sp,0x260`, ret: sl_run_fp and b8_post_FR, Post. *)
Section Stmts.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.

Definition S_E01 : Prop :=
  Hcut B APIf ra (Inv_K13090 B APIf ra empty) -> Hcut B APIf ra (Inv_ENTRY B APIf ra empty).
Definition S_M01 : Prop :=
  Hcut B APIf ra (Inv_K140e4 B APIf ra empty) -> Hcut B APIf ra (Inv_K13090 B APIf ra empty).
Definition S_M02 : Prop :=
  Hcut B APIf ra (Inv_K14118 B APIf ra empty) -> Hcut B APIf ra (Inv_K140e4 B APIf ra empty).
Definition S_M03 : Prop :=
  Hcut B APIf ra (Inv_K147e0 B APIf ra empty) -> Hcut B APIf ra (Inv_K14118 B APIf ra empty).
Definition S_M04 : Prop :=
  Hcut B APIf ra (Inv_K1482c B APIf ra empty) -> Hcut B APIf ra (Inv_K147e0 B APIf ra empty).
Definition S_X01 : Prop := Hcut B APIf ra (Inv_K1482c B APIf ra empty).

Definition seg_lemmas : Prop := S_E01 /\ S_M01 /\ S_M02 /\ S_M03 /\ S_M04 /\ S_X01.

End Stmts.
