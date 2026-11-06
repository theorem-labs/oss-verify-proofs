(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_wire/lib/U/Prog/LLVMFuzzerTestOneInput_cfb.v, with its module paths changed; 532 of its 580 lines of code are new or changed and 97 lines of the source are left out. *)
(* Modified by Theorem Labs: reac-repacer/fuzz_uci's lib/Prog/LLVMFuzzerTestOneInput_fr.v (6874bc78b1f) at fuzz_wire's
   module paths; lf_guard_img reads this image's __stack_chk_guard GOT slot 0x1cef0; lf_fr_call_x is new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_wire/lib/Prog/LLVMFuzzerTestOneInput_fr.v, with its module paths and module names changed; 455 of its 574 lines of code are new or changed and 461 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/U/Prog/Seg/Tac_slot.v, with its module names changed; 218 of its 245 lines of code are new or changed and 547 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/U/Prog/Seg/M01.v, with its module paths and module names changed; 366 of its 391 lines of code are new or changed and 220 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/U/Prog/RoleBuild/Pre.v, with its module paths and module names changed; 131 of its 148 lines of code are new or changed and 374 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells FP.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog Require Import SlotFR SlotInv.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Model Layout.
Import ListNotations.
Open Scope Z_scope.

(** LLVMFuzzerTestOneInput of fuzz_rate.c:231-284 (5608 bytes, 1402 instructions at 0x12fc0 in the plain image; frame
    544 bytes; FrameAPI.ENTRY). It allocates three blocks (pp = malloc(19744), pod = malloc(len ? len : 1),
    buf = malloc(buflen ? buflen : 1); freed buf, pod, pp), so its contract is in the form libreac/fuzz_ctrl's
    released slot consumes, as reac-pw/fuzz_role's (Prog/LLVMFuzzerTestOneInput_c.v): the frame's obligation SlotFR.slot_goal (lib_contract_g for ENTRY, from
    FrameAPI.frame_plain), split at the cuts of SlotInv.v into the segment statements S_E01, S_M01, S_M02, S_M03,
    S_X01 below (ctrl's continuation form: the H of each exit cut -> the H of the entry cut), plus the n >= 2^26 run
    (0x12ff8 `srli a2,a1,26`; 0x13000 `j 0x14564`: `mv a0,zero` and the epilogue, no call), which the slot proves as
    one evt like ctrl's slot_early. What the whole function promises is lib_contract_g's: from lib_pre at ENTRY
    (a0 = data, a1 = n, the input block or `empty` for n = 0; sp 16-aligned with 65536 writable bytes below it, above
    alloc_ceiling; ra even; frm = 0), it returns to ra with a0 = 0, every callee-saved register as at entry, the
    allocator back to its entry blocks (RES_END), the input bytes unchanged, no byte changed outside
    [sp - 65536, sp) and the allocator's own state, at an FP state with frm = 0 (lib_post). On the way no check
    aborts: check_absent / check_rate / check_malformed (when pp->corrupt = 0), check_decide, check_code and
    check_list (two rounds), check_code(MALFORMED) are the content of rate_check_contract's evt reaching 0x14504;
    check_csv is the content of rate_csv_contract's evt reaching 0x1454c.

    The three middle bodies are stated as evts, rate_build_contract, rate_check_contract and rate_csv_contract, so
    that their walks can be proved apart from the slot; S_M01's, S_M02's and S_M03's proofs lift them inside FR as
    ctrl's segments lift theirs (the run over the stack window and one live harness block: Seg/Tac_b1.b1_fr_hb, and
    Seg/Tac_fp.sl_mid_fp_blk for the two evts that change the FP state). The callee contracts the walks take as
    premises (Prog/<fn>_c.v, relocated or written in this directory):
      S_E01: malloc through the frame's malloc_contract (ms_malloc = 0x16694) by the slot's malloc step (hb = [],
             request 19744 <= 2^26: SlotFR.resb_room);
      rate_build_contract: memset_contract (0x1d230), memcpy_contract (0x1ce2c), strlen_contract (0x1d360), and the
             shared model's pod_build and pp_bytes (Pod/Model.v, Pod/Layout.v) with their step lemmas;
      S_M01: malloc again by the slot's malloc step (hb = [(pp, 19744)], request len, 8 <= len <= 5440);
      rate_check_contract: memcpy_contract, the property parse's contract (reac_rate_prop_parse 0x14c58), strcmp
             (0x1d328), pod_nearest (0x14884), check_absent (0x145a8), check_rate (0x145c8), check_malformed
             (0x145e4), reac_rate_cfg_decide (0x14c04), check_decide (0x14608), reac_rate_refuse_code (0x14990),
             check_code (0x1461c), reac_rate_bit (0x149f4), reac_rate_is_closed (0x149c0), reac_rate_best_drivable
             (0x14a38), check_list (0x1466c), and Pod/Rate.v's parse_model_encode;
      S_M03: malloc by the slot's malloc step (hb = [(pod, len); (pp, 19744)], request bl in [1, 23]);
      rate_csv_contract: memset_contract, reac_rate_drivable_csv (0x14a78, which calls snprintf 0x188a8 and memcpy),
             check_csv (0x14734, which calls bcmp 0x1cdf8);
      S_X01: free(buf) and free(pod) by the slot's free of the head block (b8_free_call with hb1 = []) and free(pp)
             by the same step at hb = [(pp, 19744)], through the frame's free_contract (ms_free = 0x16554).
    Statement text only: no function is proved here. *)

(** The quantities of the three evts. *)
Definition RATE_BUILD : Z := 0x13158.
Definition RATE_MALLOC2 : Z := 0x141e0.
Definition RATE_CHECK : Z := 0x141e4.
Definition RATE_CHECK_END : Z := 0x14504.
Definition RATE_CSV : Z := 0x14514.
Definition RATE_FREE : Z := 0x1454c.
(* The callee stack below the harness sp that the build and check evts may use. Their deepest callees: the parse
   (0x50-byte frame), pod_nearest (0x30) and its soft-float routines, check_list / check_code (0x10) and their
   strcmp, memset / memcpy / strlen; 4096 bytes cover each with slack (FR's stack region gives 65536 - 544). *)
Definition MID_STACK : Z := 4096.
(* The csv evt's callee stack below the harness sp: reac_rate_drivable_csv's 0xb0-byte frame and snprintf's
   5936 bytes below its own sp (the released snprintf_contract's SNPRINTF_K), 6112 in all (6656 below the entry sp);
   check_csv 0x60. The contract asks 8192 (slack; within FR's stack region). *)
Definition CSV_STACK : Z := 8192.
(* The harness frame below its saved registers: [sp, sp + 0x1b8) (the saves are at [sp + 0x1b8, sp + 0x220)). *)
Definition FRAME_LOCALS : Z := 0x1b8.
(* The stack region lies above the image: every reserved image segment ends below 0x60000 (Seg/Tac_slot.SL_TOP;
   the last PT_LOAD ends at 0x50878, snprintf_contract's IMG_END). *)
Definition STACK_LO_MIN : Z := 0x60000.
(* The absolute-pointer tables of .data.rel.ro the builder reads: vocab (0x1e8e0, 9 pointers) and odd_ch (0x1e928,
   14 pointers), inside FrameAPI.frame_RELRO [0x1e8d0, 0x1ea28). *)
Definition RELRO_TBL : Z := 0x1e8e0.
Definition RELRO_TBL_END : Z := 0x1e998.
(* The stack guard's GOT slot and the guard (__stack_chk_guard), which snprintf reads: FrameAPI's ms_got_guard and
   ms_guard. *)
Definition RATE_GOT_GUARD : Z := 0x1ea28.
Definition RATE_GUARD : Z := 0x50010.

(* pp->len after pod_build of the bytes after the 7-byte header. *)
Definition rate_len (rest : list byte) : Z := Z.of_nat (length (buf (fst (pod_build rest)))).
(* buf's malloc request and block length: buflen ? buflen : 1. *)
Definition rate_bl (buflen : Z) : Z := buflen + (if buflen =? 0 then 1 else 0).

(** ** The builder segment as an evt: [0x13158, 0x141e0)
    From malloc(pp)'s return (0x13158 `bnez a0`, the abort branch 0x1315c not taken: pp <> 0) to the second
    malloc's call (0x141e0 `jal malloc`, not executed). Registers at 0x13158 as SlotInv.Inv_K13158 names them: a0 = pp,
    s5 = src (the input cursor after the header), s0 = the bytes left, the seven header values s6 = fl, s9 = mask,
    s10 = buflen, s7 = b3, the cell sp + 0x30 = b4 << 8, s11 = b5, s4 = b6 << 8, and s3 = 19744, s1 = 0x5000. In order
    (pod.h:382-449, fuzz.h:37-80): memset(pp, 0, 19744) (0x1317c); the header values spilled to the frame's low cells
    (0x13188, 0x132b4-0x132c4); pod_build's header and property loop (0x13334), its Struct pod loop (0x13564) with
    ent_build's jump table (`jr a1` 0x135c4 through 0x10548), the inlined pod_write_ent and the 104-byte record copy;
    the size patches; the corruption (0x14134-0x141d4); then len = pp->len (8 or 16 from 0x13208 / 0x13278 when
    pod_build adds no property, else `ld s4,0(a6)` at 0x140f0 / 0x14190 / 0x141c8) and a0 = len + (len = 0)
    (0x141d8-0x141dc). It ends at 0x141e0 with a0 = s4 = len (len >= 8, so the request is len), s1 = pp, the header
    values back in s6 = fl, s9 = mask, s10 = buflen, s7 = b3, s2 = b4 << 8, s11 = b5 and the cell
    sp + 0x28 = b6 << 8, the cells sp + 0x70 = pp + 0x4d14, sp + 0x80 = pp, sp + 0xb0 = pp + 0x4000, the pp block =
    pp_bytes of the record pod_build made of the input after the header, sp, gp, tp, F and fc unchanged (no FP
    instruction in this range), and no byte changed outside the callees' stack below sp, the harness frame's locals
    [sp, sp + 0x1b8) and the pp block.
    Premises: the k bytes rest at src (src > 0); the pp block's 19744 bytes present and writable (rw_cells), outside
    the image, apart from the input, both below the stack region [lo, sp); the stack region with the frame's locals
    (stk over [lo, sp + 0x1b8): present and writable, as FR's stk gives; strlen(ch) reads the bytes after ch's NUL
    to the next 8-byte boundary, inside ch[24]), outside the image; the .data.rel.ro tables as in the image (FR's
    relro); mem_inv. The slot discharges each from FR at K13158 (see S_M01). *)
Definition rate_build_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (rest junk : list byte) (fl mask buflen b3 b4 b5 b6 src pp lo : Z),
    a0 = Z_to_bv 64 pp -> pp <> 0 -> pp mod 16 = 0 ->
    s5 = Z_to_bv 64 src -> s0 = Z_to_bv 64 (Z.of_nat (length rest)) ->
    s6 = Z_to_bv 64 fl -> s9 = Z_to_bv 64 mask -> s10 = Z_to_bv 64 buflen -> s7 = Z_to_bv 64 b3 ->
    bytes_at rsegs m (bv_unsigned sp + 0x30) (le8 (Z_to_bv 64 (b4 * 256))) ->
    s11 = Z_to_bv 64 b5 -> s4 = Z_to_bv 64 (b6 * 256) ->
    0 <= fl < 256 -> 0 <= mask < 256 -> 0 <= buflen < 24 ->
    0 <= b3 < 256 -> 0 <= b4 < 256 -> 0 <= b5 < 256 -> 0 <= b6 < 256 ->
    s3 = Z_to_bv 64 POD_PROPS -> s1 = Z_to_bv 64 0x5000 ->
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
      (fun ms' => exists (ra' t0' t1' t2' s0' a1' a2' a3' a4' a5' a6' a7' s3' s5' s8' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0' (Z_to_bv 64 pp) (Z_to_bv 64 (rate_len rest))
                       a1' a2' a3' a4' a5' a6' a7'
                       (Z_to_bv 64 (b4 * 256)) s3' (Z_to_bv 64 (rate_len rest)) s5' (Z_to_bv 64 fl) (Z_to_bv 64 b3) s8'
                       (Z_to_bv 64 mask) (Z_to_bv 64 buflen) (Z_to_bv 64 b5) t3' t4' t5' t6')
                  F (Z_to_bv 64 RATE_MALLOC2) fc None m' (seg_rom rsegs) /\
         bytes_at rsegs m' pp (pp_bytes (fst (pod_build rest))) /\
         bytes_at rsegs m' (bv_unsigned sp + 0x28) (le8 (Z_to_bv 64 (b6 * 256))) /\
         bytes_at rsegs m' (bv_unsigned sp + 0x70) (le8 (Z_to_bv 64 (pp + POD_NENT_OFF))) /\
         bytes_at rsegs m' (bv_unsigned sp + 0x80) (le8 (Z_to_bv 64 pp)) /\
         bytes_at rsegs m' (bv_unsigned sp + 0xb0) (le8 (Z_to_bv 64 (pp + POD_LEN_OFF))) /\
         munch [(bv_unsigned sp - MID_STACK, bv_unsigned sp + FRAME_LOCALS); (pp, pp + POD_PROPS)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp + FRAME_LOCALS))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RATE_BUILD) fc None m (seg_rom rsegs)).

(** ** The checking segment as an evt: [0x141e4, 0x14504)
    From malloc(pod)'s return (0x141e4 `beqz a0`, the abort branch to 0x145a4 not taken: pod <> 0) to the pc after
    check_code(refuse_code(MALFORMED), MALFORMED) returned. Registers and cells at 0x141e4 as SlotInv.Inv_K141e4 names
    them: a0 = pod, s4 = len, s1 = pp, s6 = fl, s9 = mask, s10 = buflen, s7 = b3, s2 = b4 << 8, s11 = b5, the cells
    sp + 0x28 = b6 << 8, sp + 0x70 = pp + 0x4d14, sp + 0x80 = pp, sp + 0xb0 = pp + 0x4000; the pp block = pp_bytes r
    for the record r that pod_build made of some input. In order (fuzz_rate.c:245-270): memcpy(pod, pp, len) when
    len <> 0 (0x141fc); hz := 0x5a5a5a5a in the cell sp + 0x158 (0x14214); rc = reac_rate_prop_parse(fl bit 0 ? NULL
    : pod, sp + 0x158) (0x14224); when pp->corrupt = 0 (0x14228-0x14234), expect_rate inlined (0x14238-0x143c4:
    is_props, params_struct, the pod_next_pair scan with strcmp against "reac.cfg.rate" (0x14308), pod_int, or
    pod_float and pod_nearest(f, INT_MIN, INT_MAX, sp + 0xb8) (0x143a4)) and check_absent / check_rate /
    check_malformed by its answer; asked = {rc = 1 ? hz : 48000, other = b3 | b4 << 8 | b5 << 16 | b6 << 24}
    (0x143dc-0x14404); for each asked value (the loop 0x14414-0x144f0, two rounds): reac_rate_cfg_decide(role, asked,
    mask) and check_decide, refuse_code and check_code, reac_rate_bit, reac_rate_is_closed, reac_rate_best_drivable
    and check_list; then check_code(refuse_code(4), 4) (0x144f8, 0x14500). It ends at 0x14504 with s3 = pod,
    s9 = mask, s10 = buflen, the cell sp + 0x80 = pp unchanged, sp, gp, tp unchanged, at some FP state with frm = 0
    (the parse and pod_nearest write FP registers and accrue fflags), and no byte changed outside the callees' stack
    below sp, the frame's locals and the pod block.
    Reaching 0x14504 at all is the property: no check aborts. It holds because the parse's answer is parse_model of
    buf r, which for an uncorrupted r equals the answer expect_rate computes from the record in pp (Pod/Rate.v), and
    because check_decide's, check_code's and check_list's premises hold for every asked value and every mask (their
    contracts).
    Premises: the record's pp_bytes at pp; the pod block's len bytes present and writable, outside the image, apart
    from pp, both below lo; the stack region with the frame's locals (stk over [lo, sp + 0x1b8)), outside the image
    and above it (0x60000 <= lo); frm0 fc; mem_inv; MemNorm.task_mem (bytes only in the image's segments or below
    TASK_SIZE: the soft-float callees of pod_nearest take it, as libreac/fuzz_boxreg's CJ callees do; the slot runs
    this evt on MemNorm.normalize_cj of the cut's memory, which has it by mem_inv_cj_normalize). *)
Definition rate_check_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (inp junk : list byte) (fl mask buflen b3 b4 b5 b6 pp pod lo : Z),
    a0 = Z_to_bv 64 pod -> pod <> 0 -> pod mod 16 = 0 ->
    s4 = Z_to_bv 64 (rate_len inp) -> s1 = Z_to_bv 64 pp ->
    s6 = Z_to_bv 64 fl -> s9 = Z_to_bv 64 mask -> s10 = Z_to_bv 64 buflen -> s7 = Z_to_bv 64 b3 ->
    s2 = Z_to_bv 64 (b4 * 256) -> s11 = Z_to_bv 64 b5 ->
    0 <= fl < 256 -> 0 <= mask < 256 -> 0 <= buflen < 24 ->
    0 <= b3 < 256 -> 0 <= b4 < 256 -> 0 <= b5 < 256 -> 0 <= b6 < 256 ->
    bytes_at rsegs m (bv_unsigned sp + 0x28) (le8 (Z_to_bv 64 (b6 * 256))) ->
    bytes_at rsegs m (bv_unsigned sp + 0x70) (le8 (Z_to_bv 64 (pp + POD_NENT_OFF))) ->
    bytes_at rsegs m (bv_unsigned sp + 0x80) (le8 (Z_to_bv 64 pp)) ->
    bytes_at rsegs m (bv_unsigned sp + 0xb0) (le8 (Z_to_bv 64 (pp + POD_LEN_OFF))) ->
    bytes_at rsegs m pp (pp_bytes (fst (pod_build inp))) ->
    rw_cells rsegs m pod [CB (Z.to_nat (rate_len inp)) junk] ->
    (forall a, pod <= a < pod + rate_len inp -> seg_rom rsegs (wa a) = None) ->
    (pod + rate_len inp <= pp \/ pp + POD_PROPS <= pod) ->
    pod + rate_len inp <= lo -> pp + POD_PROPS <= lo ->
    stk rsegs m lo (bv_unsigned sp + FRAME_LOCALS) -> lo + MID_STACK <= bv_unsigned sp -> bv_unsigned sp mod 16 = 0 ->
    STACK_LO_MIN <= lo -> bv_unsigned sp < 2 ^ 63 ->
    (forall a, lo <= a < bv_unsigned sp + FRAME_LOCALS -> seg_rom rsegs (wa a) = None) ->
    frm0 fc -> mem_inv rsegs m -> MemNorm.task_mem rsegs m ->
    evt rsegs
      (fun ms' => exists (ra' t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s4' s5' s6' s7' s8' s11'
                          t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7'
                       s2' (Z_to_bv 64 pod) s4' s5' s6' s7' s8' (Z_to_bv 64 mask) (Z_to_bv 64 buflen) s11'
                       t3' t4' t5' t6')
                  F' (Z_to_bv 64 RATE_CHECK_END) fc' None m' (seg_rom rsegs) /\
         frm0 fc' /\
         bytes_at rsegs m' (bv_unsigned sp + 0x80) (le8 (Z_to_bv 64 pp)) /\
         munch [(bv_unsigned sp - MID_STACK, bv_unsigned sp + FRAME_LOCALS); (pod, pod + rate_len inp)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp + FRAME_LOCALS))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RATE_CHECK) fc None m (seg_rom rsegs)).

(** ** The csv segment as an evt: [0x14514, 0x1454c)
    From buf's malloc return (0x14514 `beqz a0`, the abort branch to 0x145a4 not taken: buf <> 0) to the pc after
    check_csv returned. Registers at 0x14514: a0 = buf, s5 = bl = buflen + (buflen = 0) (0x14504-0x14508, the request
    malloc took), s9 = mask, s10 = buflen, s3 = pod. In order (fuzz_rate.c:276-278): memset(buf, 0x5a, bl)
    (0x14524); len = reac_rate_drivable_csv(mask, buf, buflen) (0x14534; it writes the drivable rates of mask as
    decimal text, ","-separated, cut to buflen - 1 bytes and a NUL, by snprintf(cell, 16, "%s%d", ...) into its own
    stack cell and memcpy); check_csv(buf, buflen, len, mask) (0x14548). It ends at 0x1454c with s4 = buf, s3 = pod,
    sp, gp, tp unchanged, at some FP state with frm = 0 (snprintf's post returns any fflags with rounding mode 0 and
    f10 changed), and no byte changed outside the callees' stack below sp and the buf block: the harness frame
    [sp, S) is not written, so its cell sp + 0x80 = pp and the saved registers stay.
    Reaching 0x1454c at all is the property: check_csv does not abort, because drivable_csv's text for every mask
    and buflen is the one check_csv recomputes (their contracts).
    Premises: the buf block's bl bytes present and writable, outside the image, below lo; the stack region [lo, sp)
    (no write above sp), outside the image and above it (0x60000 <= lo), at least CSV_STACK bytes; frm0 fc; mem_inv;
    MemNorm.task_mem (snprintf's chain takes it; the slot runs this evt on MemNorm.normalize_cj of the cut's memory);
    the stack guard's GOT slot holds the guard's address and the guard holds some canary (snprintf_contract's
    premises; FR leaves these static bytes out, the slot reads them from the allocator's AllocExtra.ax_statics). *)
Definition rate_csv_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (junk : list byte) (mask buflen cb pod lo : Z) (canary : word),
    a0 = Z_to_bv 64 cb -> cb <> 0 -> cb mod 16 = 0 ->
    s5 = Z_to_bv 64 (rate_bl buflen) -> s9 = Z_to_bv 64 mask -> s10 = Z_to_bv 64 buflen -> s3 = Z_to_bv 64 pod ->
    0 <= mask < 256 -> 0 <= buflen < 24 ->
    rw_cells rsegs m cb [CB (Z.to_nat (rate_bl buflen)) junk] ->
    (forall a, cb <= a < cb + rate_bl buflen -> seg_rom rsegs (wa a) = None) ->
    cb + rate_bl buflen <= lo ->
    stk rsegs m lo (bv_unsigned sp) -> lo + CSV_STACK <= bv_unsigned sp -> bv_unsigned sp mod 16 = 0 ->
    STACK_LO_MIN <= lo -> bv_unsigned sp < 2 ^ 63 ->
    (forall a, lo <= a < bv_unsigned sp -> seg_rom rsegs (wa a) = None) ->
    bytes_at rsegs m RATE_GOT_GUARD (le8 (Z_to_bv 64 RATE_GUARD)) -> bytes_at rsegs m RATE_GUARD (le8 canary) ->
    frm0 fc -> mem_inv rsegs m -> MemNorm.task_mem rsegs m ->
    evt rsegs
      (fun ms' => exists (ra' t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s5' s6' s7' s8' s9' s10' s11'
                          t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7'
                       s2' (Z_to_bv 64 pod) (Z_to_bv 64 cb) s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6')
                  F' (Z_to_bv 64 RATE_FREE) fc' None m' (seg_rom rsegs) /\
         frm0 fc' /\
         munch [(bv_unsigned sp - CSV_STACK, bv_unsigned sp); (cb, cb + rate_bl buflen)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RATE_CSV) fc None m (seg_rom rsegs)).

(** ** The segment statements (ctrl's Slot.v Section Stmts form, as role's)
    S_E01, ENTRY -> K13158: the prologue (saves at [S - 104, S)); n < 2^26 by GV, so 0x12ffc falls through; the seven
      header reads and the cursor (0x13004-0x13144: each fuzz_u8 reads its byte when one is left, else gives 0);
      malloc(19744) at 0x13154 with ra = 0x13158 through the slot's malloc step (FR with hb = []), whose continuation
      gives FR with hb = [(pp, 19744)], pp <> 0, pp mod 16 = 0 and the callee-saved registers.
    S_M01, K13158 -> K141e4: rate_build_contract on the normalized memory, with rest := g_rest g at g_src g (the input
      block's tail after the header, unchanged since ENTRY by FR and GV's blk_data, or empty), the header values
      g_fl .. g_b6, lo := S - 65536 (FR's stk), sp = S - 544; the pp block's cells from the frame's blocks_writable and
      the allocator relation (present, outside the image); the tables from relro; then `jal malloc` with a0 = g_len g
      and the slot's malloc step from hb = [(pp, 19744)] (g_len g <= 5440: pod_build_wf), whose kept-bytes clause
      carries the pp block's bytes to the cut.
    S_M02, K141e4 -> K14504: rate_check_contract on MemNorm.normalize_cj of the cut's memory (Seg/Tac_fp.v), with
      inp := g_rest g, the cut's cells and registers, the pod block's cells from the frame, frm0 from the cut's
      frm_zero; the run writes [S - 544 - 4096, S - 104) and the pod block and ends at its own FP state, so FR and
      the block list carry over to the cut at that FP state (Seg/Tac_fp.sl_mid_fp_blk).
    S_M03, K14504 -> K1454c: `seqz s5,s10`, `add s5,s10,s5`, `mv a0,s5` and malloc(bl) at 0x14510 with ra = 0x14514
      through the slot's malloc step from hb = [(pod, g_len g); (pp, 19744)] (bl = g_bl g in [1, 23]), whose
      continuation gives FR with hb = [(buf, g_bl g); (pod, g_len g); (pp, 19744)]; then rate_csv_contract on
      MemNorm.normalize_cj of that memory, with the buf block's cells from the frame, the guard words from
      AllocExtra.ax_statics, frm0 from the cut; the run writes [S - 544 - 8192, S - 544) and the buf block (sl_mid_fp_blk).
    S_X01, K1454c -> RET: `mv a0,s4` and free(buf) at 0x14550 with ra = 0x14554 by the slot's free of the head block of
      [(buf, g_bl g); (pod, g_len g); (pp, 19744)]; `mv a0,s3` and free(pod) at 0x14558 with ra = 0x1455c by the same
      step on [(pod, g_len g); (pp, 19744)]; `ld a0,0x80(sp)` and free(pp) at 0x14560 with ra = 0x14564 on
      [(pp, 19744)], which leaves hb = []; `mv a0,zero`, the restores from the saved bytes, `addi sp,sp,0x220`, ret to
      ra: Post (lib_post; RES_END by resb_end). *)
Section Stmts.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.

Definition S_E01 : Prop :=
  Hcut B APIf ra (Inv_K13158 B APIf ra empty) -> Hcut B APIf ra (Inv_ENTRY B APIf ra empty).
Definition S_M01 : Prop :=
  Hcut B APIf ra (Inv_K141e4 B APIf ra empty) -> Hcut B APIf ra (Inv_K13158 B APIf ra empty).
Definition S_M02 : Prop :=
  Hcut B APIf ra (Inv_K14504 B APIf ra empty) -> Hcut B APIf ra (Inv_K141e4 B APIf ra empty).
Definition S_M03 : Prop :=
  Hcut B APIf ra (Inv_K1454c B APIf ra empty) -> Hcut B APIf ra (Inv_K14504 B APIf ra empty).
Definition S_X01 : Prop := Hcut B APIf ra (Inv_K1454c B APIf ra empty).

Definition seg_lemmas : Prop := S_E01 /\ S_M01 /\ S_M02 /\ S_M03 /\ S_X01.

End Stmts.
