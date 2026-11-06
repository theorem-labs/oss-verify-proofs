(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_wire/lib/U/Prog/LLVMFuzzerTestOneInput_cfb.v, with its module paths changed; 532 of its 580 lines of code are new or changed and 97 lines of the source are left out. *)
(* Modified by Theorem Labs: reac-repacer/fuzz_uci's lib/Prog/LLVMFuzzerTestOneInput_fr.v (6874bc78b1f) at fuzz_wire's
   module paths; lf_guard_img reads this image's __stack_chk_guard GOT slot 0x1cef0; lf_fr_call_x is new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_wire/lib/Prog/LLVMFuzzerTestOneInput_fr.v, with its module paths and module names changed; 455 of its 574 lines of code are new or changed and 461 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/U/Prog/Seg/Tac_slot.v, with its module names changed; 218 of its 245 lines of code are new or changed and 547 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/U/Prog/Seg/M01.v, with its module paths and module names changed; 194 of its 223 lines of code are new or changed and 216 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells FP.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Model Layout Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog Require Import reac_headamp_prop_parse_result_c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog Require Import SlotFR SlotInv.
Import ListNotations.
Open Scope Z_scope.

(** LLVMFuzzerTestOneInput of fuzz_headamp.c:311-360 (5880 bytes, 1470 instructions at 0x12f88 in the plain image,
    with pod.h's builder, fuzz.h's cursor and fuzz_dup, expect_of, read_channel, cell_value and pod_nearest inlined;
    frame 560 bytes; FrameAPI.ENTRY; the plain ELF, unstripped sha256 fe40c856bfc73f2b..., pinned 61497eebc35c...). It
    allocates four blocks (pp = malloc(19744), pod = fuzz_dup(pp->buf, len), out = malloc(3 (cap + 1)), first =
    fuzz_dup(out, 3 max(rc, 0)); freed first, out, pod, pp: LIFO), so its contract is in the form
    libreac/fuzz_ctrl's released slot consumes, as reac-pw/fuzz_role's and fuzz_pin's: the frame's obligation
    SlotFR.slot_goal (lib_contract_g for ENTRY, from FrameAPI.frame_plain), split at the cuts of SlotInv.v into the
    segment statements S_E01, S_M01, S_M02, S_M03, S_M04, S_X01 below (ctrl's continuation form: the H of each exit
    cut -> the H of the entry cut), plus the n >= 2^26 run (headamp_early_contract), which the slot proves as one evt
    like ctrl's slot_early. What the whole function promises is lib_contract_g's: from lib_pre at ENTRY (a0 = data,
    a1 = n, the input block or `empty` for n = 0; sp 16-aligned with 65536 writable bytes below it, above
    alloc_ceiling; ra even; frm = 0), it returns to ra with a0 = 0, every callee-saved integer register as at entry,
    the allocator back to its entry blocks (RES_END), the input bytes unchanged, no byte changed outside
    [sp - 65536, sp), errno and the allocator's own state, at an FP state with frm = 0 (lib_post; the epilogue's
    `fld` of fs0-fs2 is not tracked: lib_post asks only the integer callee-saved registers). On the way none of the
    eight checks aborts (check_no_overrun, check_count, check_cells_valid, check_object, check_cells, check_keys,
    check_refusal, check_plain): that is the content of headamp_check_contract's evt reaching 0x14164 and
    headamp_plain_contract's reaching 0x141b4.

    The middle segments' bodies are stated as evts, so that their walks can be proved apart from the slot; each
    segment's proof lifts its evt inside FR as role's segments lift theirs (the run over the stack window
    [S - 65536, S - 104) and one live harness block; Prog/Seg/Tac_b1.v b1_fr_hb). The runs that call a parse (M03's
    reac_headamp_prop_parse_result, M04b's reac_headamp_prop_parse) also write errno (strtol, under the parse:
    parse_post munches [errno, errno + 4)), which role's b1_fr_hb and Tac_slot.sl_fr_run do not allow (they ask every
    byte outside the window and the block to stay). FR itself lets errno change (its unchanged-byte clauses exclude
    [errno_addr, errno_addr + 4)), so those two lifts use the errno variants of Prog/Seg/Tac_errno.v (beside the
    kit, which stays as role's): `b1_fr_hb_errno` / `sl_fr_run_hb_errno` (the write set is the window, one block of
    hb and [errno_addr B, errno_addr B + 4)), `sl_mid_fp_hb_errno` (sl_mid_fp's twin with that write set),
    `te_fp3` (the munch list [(lo, hi); (o, o + k); (E, E + 4)] of M03 / M04b lies in it), `te_parse_tp` /
    `te_parse_writes` (PARSE_ERRNO tp = errno_addr B under FR; the parse's writes lie in it). The evts' munch lists
    name the errno region for that reason.

    The frame bounds the evts use: MID_STACK = the deepest callee stack below the harness sp, the parse chain
    reac_headamp_prop_parse_result 0xa0 + strtol 0x120 + __intscan 0x50 = 528 bytes (PARSE_STACK; the soft-float
    callees of the inlined pod_nearest use less: __subtf3 tail-calls __addtf3, 48 bytes); FRAME_LOCALS = 0x1b0: the
    harness frame's locals [sp, sp + 0x1b0) (x at sp + 0x90, res at sp + 0x150, the builder's e / parts / ch / t up
    to t's end at sp + 0x1b0; the fsd saves of fs0-fs2 are at [sp + 0x1b0, sp + 0x1c8), the integer saves at
    [sp + 0x1c8, sp + 0x230) = [S - 104, S)); the absolute-pointer tables of .data.rel.ro the builder reads,
    vocab (0x1ed60, 9 pointers) and odd_ch (0x1eda8, 14 pointers), inside FrameAPI.frame_RELRO [0x1ed50, 0x1eea8)
    (plain's param table is relative, in .rodata at 0x105f0). The soft-float callees take MemNorm.task_mem, as
    role's role_check_contract states it.

    Callee contracts the walks take as premises (by file and name; the released forms relocated to headamp's plain
    image, or written in this directory), and why each premise holds at each call site:
      S_E01: malloc through the frame's malloc_contract (ms_malloc = 0x1643c) by the kit's b1_malloc_call (hb = [];
             request 19744 <= 2^26: SlotFR.resb_room; ra = 0x13044 even).
      headamp_build_contract (M01): memset_contract (Prog/memset_c.v, MEMSET 0x1d64c: pp's 19744 bytes at 0x13068,
             the pad sites 0x132d4 / 0x136e0 / 0x13eb4, e at 0x13418, case 8 at 0x13ca0; each a region inside the pp
             block or the frame's locals, writable by the premises), memcpy_contract (Prog/memcpy_c.v, 0x1d248:
             0x135bc, 0x135ec, 0x136ac, 0x13720 (the 104-byte record into pp->ent), 0x13928, 0x13a2c, 0x13aac,
             0x13b60, 0x13c70: source and destination in the frame / the pp block / .rodata, apart), strlen_contract
             (Prog/strlen_c.v, 0x1d77c: 0x1359c, 0x13a04, 0x13b50; ch's read to the 8-byte boundary stays inside
             the frame, t follows ch), and the shared model's pod_build and pp_bytes (Pod/Model.v, Pod/Layout.v)
             with their step lemmas and pod_build_wf (len <= 5440, every body <= 45 bytes: the stop test and every
             pod_put guard fall through). It is role's role_build_contract with headamp's registers and cells.
      S_M01: malloc again by b1_malloc_call (hb = [(pp, 19744)], request len, 8 <= len <= 5440: Pod/Spa.v
             buf_header).
      headamp_dup_pod_contract (M02): memcpy_contract at 0x14068 (pod <- pp->buf, len bytes: the pp block's first
             len bytes are buf r (pp_bytes = buf r ++ ..., Pod/Layout.v pp_image), pod's len bytes writable, the two
             blocks apart).
      S_M02: malloc by b1_malloc_call (hb = [(pod, len); (pp, 19744)], request 3 cap + 3 <= 30).
      headamp_check_contract (M03): memset_contract (0x14090: out, 0xa5, 3 cap + 3; 0x140fc: x = sp + 0x90, 0,
             0x88: frame locals); reac_headamp_prop_parse_result_contract
             (Prog/reac_headamp_prop_parse_result_c.v, 0x140bc: a0 = (null ? 0 : pod), a1 = out, a2 = cap,
             a3 = sp + 0x150; every premise from this evt's premises and memset(out) / the res fill by
             Prog/HeadSites.v parse_site_check: the pod bytes buf r with buf_header, out writable and apart,
             errno, the SSP cells; lo + PARSE_STACK <= sp; frm0 fc); check_no_overrun_contract (0x140c8),
             check_count_contract (0x140d8), check_cells_valid_contract (0x140e4) (Prog/check_*_c.v; premises
             from the parse's post and parse_props_total / parse_props_keys alone, on any bytes, corrupted too:
             HeadSites site_no_overrun, site_count, site_cells_valid); when pp->corrupt = 0 (0x140e8
             `lw a0,4(s8)`): expect_of inlined
             (0x140f0-0x14108, 0x14220-0x14670: memset(x), is_props / params_struct through sp + 0x50, n_ent through
             s8, the pod_next_pair scan, strncmp_contract (Prog/strncmp_c.v,
             0x1d80c, at 0x14324: k against "reac.headamp." 0x102bd, 13 bytes; k is a NUL-terminated body of the
             pp block, size <= 45), read_channel, strcmp_contract (Prog/strcmp_c.v, kit, 0x1d744, at 0x1443c /
             0x14450 / 0x14464 against "phantom" 0x1032f, "pad" 0x1045f, "sens" 0x102b8), cell_value, and pod_nearest
             inlined (0x14548-0x145e4) with the soft-float contracts relocated to headamp from role's CJ/RL/G
             (C_extendsftf2.v extendsftf2_contract, __extendsftf2 0x14df8, at 0x14568; C_floatditf.v
             floatditf_contract, 0x14f54, at 0x1457c; G_subtf3.v subtf3_contract, 0x15078, at 0x14590, whose
             __addtf3 frame is 48 bytes below sp; G_getf2.v getf2_contract, __gttf2 = __getf2 0x14d3c, at 0x145a4;
             G_letf2.v letf2_contract, __lttf2 = __letf2 0x14c74, at 0x145bc; each keeps F and takes task_mem,
             stk, frm0: f in fs0 and the constants -1.0f / 256.0f in fs1 / fs2 survive the five calls), giving
             x = Spec/HeadBytes.v x_bytes (expect_model null cap r); then check_object_contract (0x14118),
             check_cells_contract (0x14128) and, for rc >= 0 (0x1412c), check_keys_contract (0x14138) and
             check_refusal_contract (0x14144): on an uncorrupted record parse_props = expect_model
             (Pod/Headamp.v parse_props_build; HeadSites site_spine, site_object, site_cells, site_keys,
             site_refusal); finally first's size s8 = 3 max(rc, 0) and a0 = first_req rc (0x14148-0x14160).
      S_M03: malloc by b1_malloc_call (hb = [(out, ..); (pod, ..); (pp, ..)], request first_req rc <= 27: rc <= cap
             <= 9 by parse_props_total).
      headamp_dup_first_contract (M04a): memcpy_contract at 0x14180 when rc > 0 (first <- out, 3 rc bytes: out's
             first 3 rc bytes are the cells, first's block has first_req rc = 3 rc bytes, the blocks apart).
      headamp_plain_contract (M04b): memset_contract (0x14190: out, 0xa5, 3 cap + 3);
             reac_headamp_prop_parse_contract (Prog/reac_headamp_prop_parse_c.v, 0x14874 via 0x141a0: the same
             a0, a1, a2 as the first call, R = 0; every premise from this evt's premises and memset(out) by
             HeadSites parse_site_plain: the pod bytes, out writable, errno a cell, the SSP cells); check_plain_contract
             (Prog/check_plain_c.v, 0x141b0: plain = rc since both parses answer parse_props (parse_arg null (buf r))
             cap on the same bytes, and out and first hold the same 3 rc bytes: HeadSites site_plain).
      S_X01: four frees through the frame's free_contract (ms_free = 0x162fc) by the kit's b8_free_call, each with
             hb1 = [] (the head block): free(first) 0x141b8, free(out) 0x141c0, free(pod) 0x141c8, free(pp) 0x141d0
             with pp read from the frame cell sp + 0x58 (0x141cc).
    Statement text only: no function is proved here. *)

(** The pcs of the cuts and evt ends (role's ROLE_BUILD / ROLE_MALLOC2 / ROLE_CHECK / ROLE_FREE, with headamp's
    third and fourth mallocs). *)
Definition HEAD_BUILD : Z := 0x13044.
Definition HEAD_MALLOC2 : Z := 0x14048.
Definition HEAD_DUP_POD : Z := 0x1404c.
Definition HEAD_MALLOC3 : Z := 0x1407c.
Definition HEAD_CHECK : Z := 0x14080.
Definition HEAD_MALLOC4 : Z := 0x14164.
Definition HEAD_DUP_FIRST : Z := 0x14168.
Definition HEAD_PLAIN : Z := 0x14184.
Definition HEAD_FREE : Z := 0x141b4.
(* The deepest callee stack below the harness sp: the parse chain, 0xa0 + 0x120 + 0x50 = 528 bytes. *)
Definition MID_STACK : Z := PARSE_STACK.
(* The harness frame's locals below its FP and integer saves: [sp, sp + 0x1b0). *)
Definition FRAME_LOCALS : Z := 0x1b0.
(* The absolute-pointer tables of .data.rel.ro the builder reads: vocab (0x1ed60, 9 pointers) and odd_ch (0x1eda8,
   14 pointers), inside FrameAPI.frame_RELRO [0x1ed50, 0x1eea8). *)
Definition RELRO_TBL : Z := 0x1ed60.
Definition RELRO_TBL_END : Z := 0x1ee18.

(** ** The n >= 2^26 run, stated (role's early_evt, Prog/RoleSlot.v:59-88, with headamp's frame and FP saves)
    0x12f88 `addi sp,sp,-0x230`; the thirteen saves ra, s0-s11 (0x12f8c-0x12fbc) and three fsd of fs0-fs2
    (0x12fc0-0x12fc8); 0x12fcc `srli a2,a1,26`; 0x12fd0 `beqz a2` not taken (n >= 2^26); 0x12fd4 `j 0x141d4`;
    `mv a0,zero`, the thirteen restores, three fld of fs0-fs2 (0x1420c-0x14214), `addi sp,sp,0x230`, `ret`
    (0x141d4-0x1421c). No call, no cut. It returns to ra with a0 = 0, a2 written, sp back to S, every other integer
    register kept, fcsr kept (fsd / fld accrue no flag, so frm stays as it was), the FP registers stated free (the
    fld reload the fsd slots; Post takes any FP state with frm = 0), and no byte changed outside the frame
    [S - 560, S). *)
Definition headamp_early_contract : Prop :=
  forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S lo : Z),
    stk rsegs m lo S -> lo + 560 <= S -> S < 2 ^ 64 -> mem_inv rsegs m ->
    2 ^ 26 <= bv_unsigned a1 ->
    evt rsegs
      (fun ms' => exists (sp' a2' : word) (F' : bvmap 5 word) (m' : word -> option byte),
         ms' = MS (mkR ra sp' gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2' a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F' (ret_pc ra) fc None m' (seg_rom rsegs) /\
         sp' = Z_to_bv 64 S /\
         munch [(S - 560, S)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo S)
      (MS (mkR ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ENTRY) fc None m (seg_rom rsegs)).

(** ** M01, the builder segment as an evt: [0x13044, 0x14048)
    From malloc(pp)'s return (0x13044 `bnez a0`, the abort branch 0x13048 not taken: pp <> 0) to the second malloc's
    call (0x14048 `jal malloc`, not executed). Registers at 0x13044 as SlotInv.Inv_K13044 names them: a0 = pp,
    s3 = src (the cursor after the two harness bytes), s2 = the bytes left, s7 = null, s6 = cap, s1 = 19744,
    s0 = 0x5000. In order (pod.h:382-449, fuzz.h:37-80): memset(pp, 0, 19744) (0x13068); the cell sp + 0x50 :=
    pp + 0x4000 (0x1306c); pod_build's header, the cells sp + 0x58 := pp (0x13188) and sp + 0x38 := pp + 0x4d14,
    s6 / s7 spilled to sp / sp + 8 (0x13198-0x1319c) when there are properties; the property loop (head 0x13208),
    the Struct pod loop (head 0x1340c) with ent_build's jump table (`jr a1` 0x1346c through 0x10510), the inlined
    pod_write_ent and the 104-byte record copy; the size patches; s6, s7, s8 reloaded (0x13f74-0x13f7c); the top
    patch and the corruption (0x13f80-0x1403c); then len = pp->len (0x14034) and a0 = len + (len = 0)
    (0x14040-0x14044). It ends at 0x14048 with a0 = s4 = len (len >= 8, so the request is len), s5 = pp, s6 = cap,
    s7 = null, s8 = pp + 0x4d14, the cells sp + 0x50 = pp + 0x4000 and sp + 0x58 = pp, the pp block = pp_bytes of
    the record pod_build made of the input, sp, gp, tp, F and fc unchanged (no FP instruction in this range), and no
    byte changed outside the callees' stack below sp, the frame's locals [sp, sp + 0x1b0) and the pp block.
    Premises: the k bytes rest at src (src > 0); the pp block's 19744 bytes present and writable (rw_cells), outside
    the image, apart from the input, both below the stack region [lo, sp); the stack region with the frame's locals
    (stk over [lo, sp + 0x1b0)), outside the image; the .data.rel.ro tables as in the image (FR's relro); mem_inv.
    The slot discharges each from FR at K13044 (see S_M01). *)
Definition headamp_build_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (rest junk : list byte) (nl cap src pp lo : Z),
    a0 = Z_to_bv 64 pp -> pp <> 0 -> pp mod 16 = 0 ->
    s3 = Z_to_bv 64 src -> s2 = Z_to_bv 64 (Z.of_nat (length rest)) ->
    s7 = Z_to_bv 64 nl -> 0 <= nl <= 1 -> s6 = Z_to_bv 64 cap -> 0 <= cap <= 9 ->
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
      (fun ms' => exists (ra' t0' t1' t2' s0' s1' a1' a2' a3' a4' a5' a6' a7' s2' s3' s9' s10' s11' t3' t4' t5' t6'
                          : word) (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0' s1' (Z_to_bv 64 (head_len rest)) a1' a2' a3' a4' a5' a6' a7'
                       s2' s3' (Z_to_bv 64 (head_len rest)) (Z_to_bv 64 pp) (Z_to_bv 64 cap) (Z_to_bv 64 nl)
                       (Z_to_bv 64 (pp + POD_NENT_OFF)) s9' s10' s11' t3' t4' t5' t6')
                  F (Z_to_bv 64 HEAD_MALLOC2) fc None m' (seg_rom rsegs) /\
         bytes_at rsegs m' pp (pp_bytes (head_rec rest)) /\
         bytes_at rsegs m' (bv_unsigned sp + 0x50) (le8 (Z_to_bv 64 (pp + POD_LEN_OFF))) /\
         bytes_at rsegs m' (bv_unsigned sp + 0x58) (le8 (Z_to_bv 64 pp)) /\
         munch [(bv_unsigned sp - MID_STACK, bv_unsigned sp + FRAME_LOCALS); (pp, pp + POD_PROPS)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp + FRAME_LOCALS))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 HEAD_BUILD) fc None m (seg_rom rsegs)).

(** ** M02, pod = fuzz_dup(pp->buf, len) as an evt: [0x1404c, 0x1407c)
    From malloc(pod)'s return (0x1404c `beqz a0`, the abort branch to 0x1467c not taken: pod <> 0) to out's malloc
    call (0x1407c `jal malloc`, not executed). Registers at 0x1404c as SlotInv.Inv_K1404c names them: a0 = pod,
    s4 = len, s5 = pp, s6 = cap. In order (fuzz.h:75-78, fuzz_headamp.c:326): s1 := pod (0x14050); s2 := cap & 0xff
    (0x14054); `beqz s4` not taken (len >= 8); memcpy(pod, pp, len) (0x14068); s0 := 3 cap, s4 := 3 cap + 3,
    a0 := s4 (0x1406c-0x14078). It ends at 0x1407c with a0 = s4 = 3 cap + 3, s0 = 3 cap, s1 = pod, s2 = cap, every
    other s register as at 0x1404c (s7 = null, s8 = pp + 0x4d14 among them), sp, gp, tp, F and fc unchanged, the pod
    block = buf r, and no byte changed outside the pod block (memcpy writes only its destination; no stack).
    Premises: the record's pp_bytes at pp; the pod block's len bytes writable, apart from pp; mem_inv. *)
Definition headamp_dup_pod_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (inp junk : list byte) (cap pp pod : Z),
    a0 = Z_to_bv 64 pod -> pod <> 0 ->
    s4 = Z_to_bv 64 (head_len inp) -> s5 = Z_to_bv 64 pp -> s6 = Z_to_bv 64 cap -> 0 <= cap <= 9 ->
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

(** ** M03, the checking segment as an evt: [0x14080, 0x14164)
    From malloc(out)'s return (0x14080 `beqz a0`, the abort branch to 0x1467c not taken: out <> 0) to first's malloc
    call (0x14164 `jal malloc`, not executed). Registers at 0x14080 as SlotInv.Inv_K14080 names them: a0 = out,
    s0 = 3 cap, s1 = pod, s2 = cap, s4 = 3 cap + 3, s7 = null, s8 = pp + 0x4d14; the cells sp + 0x50 = pp + 0x4000,
    sp + 0x58 = pp; the pp block = pp_bytes r and the pod block = buf r for the record r that pod_build made of some
    input (fuzz_headamp.c:326-350). In order: s3 := out (0x14084); memset(out, 0xa5, 3 cap + 3) (0x14090); res :=
    0x5a x 12 (0x14094-0x140a0: `ld` of .rodata 0x10508, `sd 0x150(sp)`, `sw 0x158(sp)`); s5 := (null ? 0 : pod)
    (0x140a4-0x140a8); rc := reac_headamp_prop_parse_result(s5, out, cap, sp + 0x150) (0x140bc), s6 := rc;
    check_no_overrun(out + 3 cap) (0x140c8), check_count(rc, cap, &res) (0x140d8), check_cells_valid(out, rc)
    (0x140e4); when pp->corrupt = 0 (0x140e8-0x140ec): expect_of inlined into x = sp + 0x90 (the memset, the
    is_props / params_struct tests, the pair loop with the pod_next_pair scan, strncmp, read_channel, the strcmp
    chain, cell_value with the inlined pod_nearest and its five soft-float calls, the cap break, the cell writes;
    0x140f0-0x14108, 0x14220-0x14670), check_object(rc, &res, &x) (0x14118), check_cells(out, rc, &x) (0x14128),
    and for rc >= 0 check_keys(&res, &x) (0x14138) and check_refusal(&res, &x) (0x14144); s8 := 3 max(rc, 0),
    a0 := s8 + (s8 = 0) (0x14148-0x14160). It ends at 0x14164 with a0 = first_req rc, s1 = pod, s2 = cap, s3 = out,
    s4 = 3 cap + 3, s5 = (null ? 0 : pod), s6 = rc, s8 = 3 max(rc, 0), the cell sp + 0x58 = pp, out = the parse's
    cells as bytes then 0xa5 (out_after cap o), errno some value and still a cell, sp, gp, tp unchanged, at some FP
    state with frm = 0 (the parse and the soft-float calls write FP registers and accrue fflags), and no byte changed
    outside the callees' stack below sp, the frame's locals, the out block and errno; here o = parse_props
    (parse_arg null (buf r)) cap and rc = ans_rc o.
    Reaching 0x14164 at all is the property: no check aborts. It holds because the parse's answer is o
    (reac_headamp_prop_parse_result_contract); o is answer_ok with keys <= 16384 on any bytes (parse_props_total,
    parse_props_keys), which is all check_no_overrun, check_count and check_cells_valid need; and on an uncorrupted r
    o = expect_model null cap r (parse_props_build), the answer expect_of computes from the record in pp into x,
    which is what check_object, check_cells, check_keys and check_refusal compare with.
    Premises: the record's pp_bytes at pp and buf r at pod (pod > 0, 16-aligned); the out block's 3 cap + 3 bytes
    writable, outside the image; the three blocks pairwise apart and below lo; the stack region with the frame's
    locals (stk over [lo, sp + 0x1b0)), outside the image; errno a cell apart from the stack region and the pod, out and
    pp blocks (the segment reads pp's record after the parse); the SSP GOT slot and guard strtol reads, apart from every
    region written before the parse; frm0 fc;
    mem_inv; MemNorm.task_mem (the slot runs this evt on MemNorm.normalize_cj of the cut's memory, as role's slot
    runs role_check_contract). *)
Definition headamp_check_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (inp junk : list byte) (nl cap pp pod out lo : Z) (ev can : word),
    a0 = Z_to_bv 64 out -> 0 < out -> out mod 16 = 0 ->
    s0 = Z_to_bv 64 (3 * cap) -> s1 = Z_to_bv 64 pod -> s2 = Z_to_bv 64 cap -> s4 = Z_to_bv 64 (OUT_LEN cap) ->
    s7 = Z_to_bv 64 nl -> s8 = Z_to_bv 64 (pp + POD_NENT_OFF) -> 0 <= nl <= 1 -> 0 <= cap <= 9 ->
    bytes_at rsegs m (bv_unsigned sp + 0x50) (le8 (Z_to_bv 64 (pp + POD_LEN_OFF))) ->
    bytes_at rsegs m (bv_unsigned sp + 0x58) (le8 (Z_to_bv 64 pp)) ->
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
         bytes_at rsegs m' (bv_unsigned sp + 0x58) (le8 (Z_to_bv 64 pp)) /\
         rw_cells rsegs m' (PARSE_ERRNO tp) [C4 ev'] /\
         munch [(bv_unsigned sp - MID_STACK, bv_unsigned sp + FRAME_LOCALS); (out, out + OUT_LEN cap);
                (PARSE_ERRNO tp, PARSE_ERRNO tp + 4)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp + FRAME_LOCALS))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 HEAD_CHECK) fc None m (seg_rom rsegs)).

(** ** M04a, first = fuzz_dup(out, 3 max(rc, 0)) past its malloc, as an evt: [0x14168, 0x14184)
    From malloc(first)'s return (0x14168 `beqz a0`, the abort branch to 0x1467c not taken: first <> 0) to the memset
    before the plain parse. Registers at 0x14168 as SlotInv.Inv_K14168 names them: a0 = first, s3 = out, s6 = rc,
    s8 = 3 max(rc, 0). In order (fuzz.h:75-78): s7 := first (0x1416c); `blez s6` (0x14170): for rc > 0,
    memcpy(first, out, 3 rc) (0x14180). It ends at 0x14184 with s7 = first, every other s register as at 0x14168,
    sp, gp, tp, F and fc unchanged, first's first 3 rc bytes = out's (when rc > 0), and no byte changed outside the
    first block (memcpy writes only its destination; no stack). It writes one block, so the slot lifts it by the
    kit's b1_fr_hb (first).
    Premises: rc's bound; out's first 3 rc bytes w (when rc > 0); the first block's first_req rc bytes writable,
    apart from out's 3 max(rc, 0) bytes; mem_inv. *)
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

(** ** M04b, the plain parse and check_plain as an evt: [0x14184, 0x141b4)
    From 0x14184 (after M04a) to the pc after check_plain's return. Registers at 0x14184: s2 = cap, s3 = out,
    s4 = 3 cap + 3, s5 = (null ? 0 : pod), s6 = rc, s7 = first. In order (fuzz_headamp.c:351-353): memset(out, 0xa5,
    3 cap + 3) (0x14190); plain := reac_headamp_prop_parse(s5, out, cap) (0x141a0 -> 0x14874, the tail jump to the
    parse with res = NULL); check_plain(plain, rc, out, first) (0x141a4-0x141b0). It ends at 0x141b4 with every s
    register as at 0x14184, sp, gp, tp unchanged, errno some value and still a cell, at some FP state with frm = 0
    (the parse writes FP registers and accrues fflags), and no byte changed outside the callees' stack below sp, the
    out block and errno (nothing in the harness frame at or above sp is written: res is NULL). Reaching 0x141b4 is
    check_plain's property: both parses answer parse_props (parse_arg null (buf r)) cap on the same pod bytes, so
    plain = rc, and out after the second parse holds the same cells as first. It writes one block (out), so the
    slot lifts it by Tac_errno.v's sl_mid_fp_hb_errno (out, and errno).
    Premises: the pod bytes buf r (pod > 0, 16-aligned) and rc the first parse's answer on them, o = parse_props
    (parse_arg null (buf r)) cap; first's bytes = o's cells as bytes; the out block writable, outside the image; the
    pod, out and first regions apart and below lo; the stack region (stk over [lo, sp + 0x1b0)), outside the image;
    errno a cell apart from the stack region and the three regions; the SSP cells, apart from every region written
    before the parse; frm0 fc; mem_inv. *)
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

(** ** The segment statements (ctrl's Slot.v Section Stmts form, as role's and pin's)
    S_E01, ENTRY -> K13044: the prologue (the integer saves at [S - 104, S), the fsd of fs0-fs2 at [S - 128,
      S - 104), inside the window); n < 2^26 by GV, so 0x12fd0 falls through; null, cap and the cursor
      (0x12fd8-0x13030, fuzz.h's fuzz_u8 twice); malloc(19744) at 0x13040 with ra = 0x13044 through the kit's
      b1_malloc_call (FR with hb = []), whose continuation gives FR with hb = [(pp, 19744)], pp <> 0, pp mod 16 = 0
      and the callee-saved registers.
    S_M01, K13044 -> K1404c: headamp_build_contract on the normalized memory, with rest := g_rest g at g_src g (the
      input block's tail, unchanged since ENTRY by FR and GV's blk_data, or empty), nl := g_null g, cap := g_cap g,
      lo := S - 65536 (FR's stk), sp = S - 560; the pp block's cells from the frame's blocks_writable and the
      allocator relation (present, outside the image); the tables from relro; lifted by b1_fr_hb (the pp block);
      then `jal malloc` with a0 = g_len g and b1_malloc_call from hb = [(pp, 19744)] (g_len g <= 5440: pod_build_wf,
      buf_header), whose kept-bytes clause carries the pp block's bytes to the cut.
    S_M02, K1404c -> K14080: headamp_dup_pod_contract with inp := g_rest g, the pod block's cells from the frame,
      lifted by b1_fr_hb (the pod block); then `jal malloc` with a0 = 3 g_cap g + 3 and b1_malloc_call from
      hb = [(pod, g_len g); (pp, 19744)], which keeps both blocks' bytes.
    S_M03, K14080 -> K14168: headamp_check_contract on MemNorm.normalize_cj of the cut's memory, with inp := g_rest g,
      nl := g_null g, cap := g_cap g, the cut's registers and cells, the out block's cells from the frame, errno's
      cell from FR's writable errno (in the image, apart from the stack and the heap blocks), the SSP cells from
      the allocator relation's statics (ms_got_guard 0x1eea8 = PARSE_SSP_GOT, ms_guard 0x50490 = PARSE_SSP_GUARD),
      frm0 from the cut's frm_zero; the run changes the FP state and writes the window, the out block and errno, so
      it runs by Tac_errno.v's sl_mid_fp_hb_errno_cj (the run on MemNorm.normalize_cj; the out block; te_fp3 for
      the munch list); then `jal malloc` with
      a0 = first_req rc and b1_malloc_call from hb = [(out, ..); (pod, ..); (pp, ..)] (first_req rc <= 27).
    S_M04, K14168 -> K141b4: headamp_dup_first_contract (w := the cut's cells of out; first's block from the frame),
      lifted by b1_fr_hb (the first block); then headamp_plain_contract (first's bytes from M04a's post, the pod
      bytes and errno from the cut), run and lifted by Tac_errno.v's sl_mid_fp_hb_errno (the out block).
    S_X01, K141b4 -> RET: `mv a0,s7` and free(first) at 0x141b8 (ra = 0x141bc), `mv a0,s3` and free(out) at 0x141c0
      (ra = 0x141c4), `mv a0,s1` and free(pod) at 0x141c8 (ra = 0x141cc), `ld a0,0x58(sp)` and free(pp) at 0x141d0
      (ra = 0x141d4), each by the kit's b8_free_call with hb1 = [] (the head block of the CUTST block list; each
      free keeps the bytes of [S - 560, S), so the cell sp + 0x58 still holds pp), which leaves hb = []; then
      `mv a0,zero`, the restores from the saved bytes, the fld of fs0-fs2, `addi sp,sp,0x230`, ret to ra, run by
      sl_run_fp (fld writes F; fcsr kept) and closed by b8_post_FR at that FP state: Post (lib_post; RES_END by
      resb_end). *)
Section Stmts.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.

Definition S_E01 : Prop :=
  Hcut B APIf ra (Inv_K13044 B APIf ra empty) -> Hcut B APIf ra (Inv_ENTRY B APIf ra empty).
Definition S_M01 : Prop :=
  Hcut B APIf ra (Inv_K1404c B APIf ra empty) -> Hcut B APIf ra (Inv_K13044 B APIf ra empty).
Definition S_M02 : Prop :=
  Hcut B APIf ra (Inv_K14080 B APIf ra empty) -> Hcut B APIf ra (Inv_K1404c B APIf ra empty).
Definition S_M03 : Prop :=
  Hcut B APIf ra (Inv_K14168 B APIf ra empty) -> Hcut B APIf ra (Inv_K14080 B APIf ra empty).
Definition S_M04 : Prop :=
  Hcut B APIf ra (Inv_K141b4 B APIf ra empty) -> Hcut B APIf ra (Inv_K14168 B APIf ra empty).
Definition S_X01 : Prop := Hcut B APIf ra (Inv_K141b4 B APIf ra empty).

Definition seg_lemmas : Prop := S_E01 /\ S_M01 /\ S_M02 /\ S_M03 /\ S_M04 /\ S_X01.

End Stmts.
