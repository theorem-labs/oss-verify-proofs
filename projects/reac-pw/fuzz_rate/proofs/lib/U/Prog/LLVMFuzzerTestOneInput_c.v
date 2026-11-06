(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_wire/lib/U/Prog/LLVMFuzzerTestOneInput_cfb.v, with its module paths changed; 532 of its 580 lines of code are new or changed and 97 lines of the source are left out. *)
(* Modified by Theorem Labs: reac-repacer/fuzz_uci's lib/Prog/LLVMFuzzerTestOneInput_fr.v (6874bc78b1f) at fuzz_wire's
   module paths; lf_guard_img reads this image's __stack_chk_guard GOT slot 0x1cef0; lf_fr_call_x is new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_wire/lib/Prog/LLVMFuzzerTestOneInput_fr.v, with its module paths and module names changed; 455 of its 574 lines of code are new or changed and 461 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/U/Prog/Seg/Tac_slot.v, with its module names changed; 218 of its 245 lines of code are new or changed and 547 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/U/Prog/Seg/M01.v, with its module paths and module names changed; 366 of its 391 lines of code are new or changed and 220 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/U/Prog/RoleBuild/Pre.v, with its module paths and module names changed; 144 of its 161 lines of code are new or changed and 374 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells FP.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog Require Import SlotFR SlotInv.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Model Layout.
Import ListNotations.
Open Scope Z_scope.

(** LLVMFuzzerTestOneInput of fuzz_rate.c:231-284 (5856 bytes, 1464 instructions at 0x12fe0 in the UBSan image; frame
    592 bytes; U/FrameAPI.ENTRY). The plain contract (lib/Prog/LLVMFuzzerTestOneInput_c.v) with the UBSan numbers: the
    frame's obligation U/Prog/SlotFR.slot_goal (from U/FrameAPI.frame_ubsan), split at the cuts of U/Prog/SlotInv.v
    into S_E01, S_M01, S_M02, S_M03, S_X01 below, plus the n >= 2^26 run (0x13018 `srli a2,a1,26`; 0x13020
    `j 0x14678`), as one evt like ctrl's slot_early. The whole function promises lib_contract_g's lib_post, as in the
    plain build. The form is reac-pw/fuzz_role's U/Prog/LLVMFuzzerTestOneInput_c.v.

    UBSan checks: 81 trap branches in this function, all to the `unimp` at 0x146bc (0x146b8 is the abort call).
    7 are S_E01's: the pointer-overflow checks of in->p + 1 in the seven fuzz_u8 header
    reads (0x13038, 0x13054, 0x130b0, 0x143d8, 0x14400, 0x1442c, 0x14454; data is a user block with 4096 <= data
    and data + n <= alloc_ceiling (mr_blocks_range), so for k <= n, data + k is neither 0 nor 1 (each test traps iff
    data + k <=u 1); for n = 0 no check runs (0x13028 `beqz a1`)). 68 lie in rate_build's range (the cursor's
    pointer-overflow checks on in->p + 1 and in->p + n, pp & 7, the header and buf[len] bounds and pointer checks,
    the table index checks, e->body + n, r[k], ch + k, the record copy's n_ent++ / ent bound / object size, the
    corruption's buf[off + k]); each is dead by a premise of rate_build_contract, as role's are by
    role_build_contract's. 6 lie in rate_check's range (expect_rate's &ent[*at] bound and pointer, body + size - 1,
    the overflow of at++, &ent[v] bound and pointer), dead by n_ent <= 32 and e_size <= 45 of the record in pp. None
    lies in the decide loop, the csv range or the frees. pod_write_ent's 10 traps are its contract's.

    The callee contracts the walks take as premises (U/Prog/<fn>_c.v):
      S_E01: malloc through the frame's malloc_contract (ms_malloc = 0x16a7c) by the slot's malloc step;
      rate_build_contract: memset_contract (0x1d618), memcpy_contract (0x1d214), strlen_contract (0x1d748),
             pod_write_ent_contract (0x14a18; called at 0x13398, 0x13efc, 0x14010), and the shared model's
             pod_build and pp_bytes with their step lemmas;
      S_M01: malloc again by the slot's malloc step (hb = [(pp, 19744)], request len);
      rate_check_contract: memcpy, the property parse (reac_rate_prop_parse 0x14fe8), strcmp (0x1d710), pod_nearest
             (0x14b84), check_absent (0x146c0), check_rate (0x146e4), check_malformed (0x14704),
             reac_rate_cfg_decide (0x14f94), check_decide (0x1472c), reac_rate_refuse_code (0x14cd8), check_code
             (0x14744), reac_rate_bit (0x14d48), reac_rate_is_closed (0x14d14), reac_rate_best_drivable (0x14d8c),
             check_list (0x14798), and Pod/Rate.v's parse_model_encode;
      S_M03: malloc by the slot's malloc step (hb = [(pod, len); (pp, 19744)], request bl in [1, 23]);
      rate_csv_contract: memset, reac_rate_drivable_csv (0x14dcc; snprintf 0x18c90, memcpy), check_csv (0x14864;
             bcmp 0x1d1e0);
      S_X01: free(buf), free(pod) and free(pp) through the frame's free_contract (ms_free = 0x1693c) by the slot's
             free steps.
    Statement text only: no function is proved here. *)

Definition RATE_BUILD : Z := 0x13110.
Definition RATE_MALLOC2 : Z := 0x14208.
Definition RATE_CHECK : Z := 0x1420c.
Definition RATE_CHECK_END : Z := 0x14614.
Definition RATE_CSV : Z := 0x14628.
Definition RATE_FREE : Z := 0x14660.
(* The callee stack below the harness sp of the build and check evts, as in the plain file (the parse's frame 0x50,
   pod_nearest 0x30 and its soft-float routines, check_list / check_code 0x10). *)
Definition MID_STACK : Z := 4096.
(* The csv evt's callee stack below the harness sp: reac_rate_drivable_csv's 0xb0 and snprintf's 5936, 6112 in all
   (6704 below the entry sp); check_csv 0x90. The contract asks 8192. *)
Definition CSV_STACK : Z := 8192.
(* The harness frame below its saved registers: [sp, sp + 0x1e8) (the saves are at [sp + 0x1e8, sp + 0x250)). *)
Definition FRAME_LOCALS : Z := 0x1e8.
(* Every reserved image segment ends below 0x60000 (the last PT_LOAD ends at 0x50cc8, snprintf_contract's IMG_END). *)
Definition STACK_LO_MIN : Z := 0x60000.
(* The absolute-pointer tables of .data.rel.ro the builder reads: vocab (0x1ecc8, 9 pointers), odd_ch (0x1ed10,
   14 pointers) and param (0x1ed80, 8 pointers), inside U/FrameAPI.frame_RELRO [0x1ecb8, 0x1ee78). *)
Definition RELRO_TBL : Z := 0x1ecc8.
Definition RELRO_TBL_END : Z := 0x1edc0.
(* reac_rate_refuse_code's codes[] table, read by the checking segment: 5 absolute pointers in .data.rel.ro at
   0x1edc0 (plain: a relative table in .rodata), inside U/FrameAPI.frame_RELRO. *)
Definition CODES_TBL : Z := 0x1edc0.
Definition CODES_TBL_END : Z := 0x1ede8.
(* The stack guard's GOT slot and the guard (U/FrameAPI's ms_got_guard and ms_guard), which snprintf reads. *)
Definition RATE_GOT_GUARD : Z := 0x1ee78.
Definition RATE_GUARD : Z := 0x50460.

Definition rate_len (rest : list byte) : Z := Z.of_nat (length (buf (fst (pod_build rest)))).
Definition rate_bl (buflen : Z) : Z := buflen + (if buflen =? 0 then 1 else 0).

(** ** The builder segment as an evt: [0x13110, 0x14208)
    From malloc(pp)'s return (0x13110 `bnez a0`; pp <> 0) to the second malloc's call (0x14208 `jal malloc`, not
    executed). Registers and cells at 0x13110 as U/Prog/SlotInv.Inv_K13110 names them: a0 = pp, s7 = src, s1 = the bytes
    left, s2 = fl, s5 = mask, the cell sp + 0x30 = buflen, s4 = b3, the cells sp + 0x28 = b4 << 8, sp + 0x20 = b5,
    sp + 0x18 = b6 << 8, s3 = 19744, s0 = 0x5000. The plain evt's steps (memset(pp, 0, 19744) at 0x13124, the header
    values to the cells sp + 8 (0x131b8), sp + 0x10 (0x13190), sp + 0x38 (0x13294), the property loop 0x1333c, the
    Struct pod loop 0x13560 with `jr a1` at 0x135d0 through 0x10558, the pod_write_ent calls, the record copy, the
    patches, the corruption 0x14100-0x141fc, len = pp->len at 0x141f4 / 0x140d8, a0 = len + (len = 0) at
    0x14200-0x14204), with no trap reached. It ends at 0x14208 with a0 = s4 = len, s8 = pp, s11 = pp + 0x4000,
    s2 = fl, the cells sp + 8 = b3, sp + 0x10 = mask, sp + 0x18 = b6 << 8, sp + 0x20 = b5, sp + 0x28 = b4 << 8,
    sp + 0x30 = buflen, sp + 0x38 = fl, sp + 0x98 = pp + 0x4d14, sp + 0xd8 = pp, the pp block = pp_bytes of the
    record, sp, gp, tp, F, fc unchanged, and no byte changed outside the callees' stack below sp, the frame's locals
    [sp, sp + 0x1e8) and the pp block. Premises as the plain evt's, with the header cells for the plain registers. *)
Definition rate_build_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (rest junk : list byte) (fl mask buflen b3 b4 b5 b6 src pp lo : Z),
    a0 = Z_to_bv 64 pp -> pp <> 0 -> pp mod 16 = 0 ->
    s7 = Z_to_bv 64 src -> s1 = Z_to_bv 64 (Z.of_nat (length rest)) ->
    s2 = Z_to_bv 64 fl -> s5 = Z_to_bv 64 mask -> s4 = Z_to_bv 64 b3 ->
    bytes_at rsegs m (bv_unsigned sp + 0x30) (le8 (Z_to_bv 64 buflen)) ->
    bytes_at rsegs m (bv_unsigned sp + 0x28) (le8 (Z_to_bv 64 (b4 * 256))) ->
    bytes_at rsegs m (bv_unsigned sp + 0x20) (le8 (Z_to_bv 64 b5)) ->
    bytes_at rsegs m (bv_unsigned sp + 0x18) (le8 (Z_to_bv 64 (b6 * 256))) ->
    0 <= fl < 256 -> 0 <= mask < 256 -> 0 <= buflen < 24 ->
    0 <= b3 < 256 -> 0 <= b4 < 256 -> 0 <= b5 < 256 -> 0 <= b6 < 256 ->
    s3 = Z_to_bv 64 POD_PROPS -> s0 = Z_to_bv 64 0x5000 ->
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
      (fun ms' => exists (ra' t0' t1' t2' s0' s1' a1' a2' a3' a4' a5' a6' a7' s3' s5' s6' s7' s9' s10' t3' t4' t5'
                          t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0' s1' (Z_to_bv 64 (rate_len rest)) a1' a2' a3' a4' a5' a6' a7'
                       (Z_to_bv 64 fl) s3' (Z_to_bv 64 (rate_len rest)) s5' s6' s7' (Z_to_bv 64 pp)
                       s9' s10' (Z_to_bv 64 (pp + POD_LEN_OFF)) t3' t4' t5' t6')
                  F (Z_to_bv 64 RATE_MALLOC2) fc None m' (seg_rom rsegs) /\
         bytes_at rsegs m' pp (pp_bytes (fst (pod_build rest))) /\
         bytes_at rsegs m' (bv_unsigned sp + 0x8) (le8 (Z_to_bv 64 b3)) /\
         bytes_at rsegs m' (bv_unsigned sp + 0x10) (le8 (Z_to_bv 64 mask)) /\
         bytes_at rsegs m' (bv_unsigned sp + 0x18) (le8 (Z_to_bv 64 (b6 * 256))) /\
         bytes_at rsegs m' (bv_unsigned sp + 0x20) (le8 (Z_to_bv 64 b5)) /\
         bytes_at rsegs m' (bv_unsigned sp + 0x28) (le8 (Z_to_bv 64 (b4 * 256))) /\
         bytes_at rsegs m' (bv_unsigned sp + 0x30) (le8 (Z_to_bv 64 buflen)) /\
         bytes_at rsegs m' (bv_unsigned sp + 0x38) (le8 (Z_to_bv 64 fl)) /\
         bytes_at rsegs m' (bv_unsigned sp + 0x98) (le8 (Z_to_bv 64 (pp + POD_NENT_OFF))) /\
         bytes_at rsegs m' (bv_unsigned sp + 0xd8) (le8 (Z_to_bv 64 pp)) /\
         munch [(bv_unsigned sp - MID_STACK, bv_unsigned sp + FRAME_LOCALS); (pp, pp + POD_PROPS)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp + FRAME_LOCALS))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RATE_BUILD) fc None m (seg_rom rsegs)).

(** ** The checking segment as an evt: [0x1420c, 0x14614)
    From malloc(pod)'s return (0x1420c `beqz a0`, the abort branch to 0x146b8 not taken: pod <> 0) to the pc after
    check_code(refuse_code(MALFORMED), MALFORMED) returned. Registers and cells at 0x1420c as
    U/Prog/SlotInv.Inv_K1420c names them: a0 = pod, s4 = len, s8 = pp, s11 = pp + 0x4000, s2 = fl, the header cells
    sp + 8 .. sp + 0x38, sp + 0x98 = pp + 0x4d14, sp + 0xd8 = pp; the pp block = pp_bytes r for the record r that
    pod_build made of some input. The plain evt's steps (memcpy 0x14224, hz := 0x5a5a5a5a in sp + 0x188 at 0x14234,
    the parse 0x14244, expect_rate with strcmp 0x14360 and pod_nearest(f, INT_MIN, INT_MAX, sp + 0xe8) 0x14490,
    check_absent / check_rate 0x144a4 / check_malformed 0x144b8, asked[] in the cells sp + 0xe8 / sp + 0xec
    (0x14500-0x14504), the decide loop 0x1451c-0x14600 (two rounds, counter s1), check_code(refuse_code(4), 4) 0x14608
    and 0x14610), with no trap reached. It ends at 0x14614 with s3 = pod, s10 = mask (0x14518 `ld s10,0x10(sp)`), the
    cells sp + 0x30 = buflen and sp + 0xd8 = pp unchanged, sp, gp, tp unchanged, at some FP state with frm = 0, and no
    byte changed outside the callees' stack below sp, the frame's locals and the pod block. Premises as the plain
    evt's, MemNorm.task_mem included (the slot runs the evt on MemNorm.normalize_cj of the cut's memory), and one more:
    refuse_code reads its codes[] table from .data.rel.ro here, so those 40 bytes read as the image (FR's relro). *)
Definition rate_check_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (inp junk : list byte) (fl mask buflen b3 b4 b5 b6 pp pod lo : Z),
    a0 = Z_to_bv 64 pod -> pod <> 0 -> pod mod 16 = 0 ->
    s4 = Z_to_bv 64 (rate_len inp) -> s8 = Z_to_bv 64 pp -> s11 = Z_to_bv 64 (pp + POD_LEN_OFF) ->
    s2 = Z_to_bv 64 fl ->
    0 <= fl < 256 -> 0 <= mask < 256 -> 0 <= buflen < 24 ->
    0 <= b3 < 256 -> 0 <= b4 < 256 -> 0 <= b5 < 256 -> 0 <= b6 < 256 ->
    bytes_at rsegs m (bv_unsigned sp + 0x8) (le8 (Z_to_bv 64 b3)) ->
    bytes_at rsegs m (bv_unsigned sp + 0x10) (le8 (Z_to_bv 64 mask)) ->
    bytes_at rsegs m (bv_unsigned sp + 0x18) (le8 (Z_to_bv 64 (b6 * 256))) ->
    bytes_at rsegs m (bv_unsigned sp + 0x20) (le8 (Z_to_bv 64 b5)) ->
    bytes_at rsegs m (bv_unsigned sp + 0x28) (le8 (Z_to_bv 64 (b4 * 256))) ->
    bytes_at rsegs m (bv_unsigned sp + 0x30) (le8 (Z_to_bv 64 buflen)) ->
    bytes_at rsegs m (bv_unsigned sp + 0x38) (le8 (Z_to_bv 64 fl)) ->
    bytes_at rsegs m (bv_unsigned sp + 0x98) (le8 (Z_to_bv 64 (pp + POD_NENT_OFF))) ->
    bytes_at rsegs m (bv_unsigned sp + 0xd8) (le8 (Z_to_bv 64 pp)) ->
    bytes_at rsegs m pp (pp_bytes (fst (pod_build inp))) ->
    rw_cells rsegs m pod [CB (Z.to_nat (rate_len inp)) junk] ->
    (forall a, pod <= a < pod + rate_len inp -> seg_rom rsegs (wa a) = None) ->
    (pod + rate_len inp <= pp \/ pp + POD_PROPS <= pod) ->
    pod + rate_len inp <= lo -> pp + POD_PROPS <= lo ->
    stk rsegs m lo (bv_unsigned sp + FRAME_LOCALS) -> lo + MID_STACK <= bv_unsigned sp -> bv_unsigned sp mod 16 = 0 ->
    STACK_LO_MIN <= lo -> bv_unsigned sp < 2 ^ 63 ->
    (forall a, lo <= a < bv_unsigned sp + FRAME_LOCALS -> seg_rom rsegs (wa a) = None) ->
    (forall a, CODES_TBL <= a < CODES_TBL_END -> mrd rsegs m (wa a) = seg_rom rsegs (wa a)) ->
    frm0 fc -> mem_inv rsegs m -> MemNorm.task_mem rsegs m ->
    evt rsegs
      (fun ms' => exists (ra' t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s4' s5' s6' s7' s8' s9' s11'
                          t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7'
                       s2' (Z_to_bv 64 pod) s4' s5' s6' s7' s8' s9' (Z_to_bv 64 mask) s11' t3' t4' t5' t6')
                  F' (Z_to_bv 64 RATE_CHECK_END) fc' None m' (seg_rom rsegs) /\
         frm0 fc' /\
         bytes_at rsegs m' (bv_unsigned sp + 0x30) (le8 (Z_to_bv 64 buflen)) /\
         bytes_at rsegs m' (bv_unsigned sp + 0xd8) (le8 (Z_to_bv 64 pp)) /\
         munch [(bv_unsigned sp - MID_STACK, bv_unsigned sp + FRAME_LOCALS); (pod, pod + rate_len inp)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp + FRAME_LOCALS))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RATE_CHECK) fc None m (seg_rom rsegs)).

(** ** The csv segment as an evt: [0x14628, 0x14660)
    From buf's malloc return (0x14628 `beqz a0`, the abort branch to 0x146b8 not taken: buf <> 0) to the pc after
    check_csv returned. Registers at 0x14628: a0 = buf, s5 = bl = buflen + (buflen = 0) (0x14618-0x1461c), s0 = buflen
    (0x14614 `ld s0,0x30(sp)`), s10 = mask, s3 = pod. The plain evt's steps (memset(buf, 0x5a, bl) 0x14638,
    reac_rate_drivable_csv(mask, buf, buflen) 0x14648, check_csv(buf, buflen, len, mask) 0x1465c), with no trap in this
    range. It ends at 0x14660 with s4 = buf, s3 = pod, sp, gp, tp unchanged, at some FP state with frm = 0, and no byte
    changed outside the callees' stack below sp and the buf block (the harness frame [sp, S) is not written). Premises
    as the plain evt's. *)
Definition rate_csv_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (junk : list byte) (mask buflen cb pod lo : Z) (canary : word),
    a0 = Z_to_bv 64 cb -> cb <> 0 -> cb mod 16 = 0 ->
    s5 = Z_to_bv 64 (rate_bl buflen) -> s0 = Z_to_bv 64 buflen -> s10 = Z_to_bv 64 mask -> s3 = Z_to_bv 64 pod ->
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

(** ** The segment statements (as the plain file's, with the UBSan cuts)
    S_E01, ENTRY -> K13110: the prologue (saves at [S - 104, S)); n < 2^26; the seven header reads (0x13024-0x130f8 and
      out of line 0x143d0-0x1446c; the 7 traps dead); malloc(19744) at 0x1310c with ra = 0x13110 by the slot's malloc
      step (hb = [] to [(pp, 19744)]).
    S_M01, K13110 -> K1420c: rate_build_contract (rest := g_rest g at g_src g, the header values, lo := S - 65536,
      sp = S - 592), then `jal malloc` with a0 = g_len g by the slot's malloc step from hb = [(pp, 19744)], whose
      kept-bytes clause carries the pp block's bytes to the cut.
    S_M02, K1420c -> K14614: rate_check_contract with inp := g_rest g on MemNorm.normalize_cj (Seg/Tac_fp.sl_mid_fp_blk).
    S_M03, K14614 -> K14660: `ld s0,0x30(sp)`, `seqz s5,s0`, `add s5,s0,s5`, `mv a0,s5` and malloc(bl) at 0x14624 with
      ra = 0x14628 by the slot's malloc step from hb = [(pod, g_len g); (pp, 19744)]; then rate_csv_contract on
      MemNorm.normalize_cj (sl_mid_fp_blk), the guard words from AllocExtra.ax_statics.
    S_X01, K14660 -> RET: free(buf) at 0x14664 (ra = 0x14668), free(pod) at 0x1466c (ra = 0x14670) and free(pp) at
      0x14674 (ra = 0x14678, pp from `ld a0,0xd8(sp)`) by the slot's free steps, `mv a0,zero`, the restores,
      `addi sp,sp,0x250`, ret: Post. *)
Section Stmts.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.

Definition S_E01 : Prop :=
  Hcut B APIf ra (Inv_K13110 B APIf ra empty) -> Hcut B APIf ra (Inv_ENTRY B APIf ra empty).
Definition S_M01 : Prop :=
  Hcut B APIf ra (Inv_K1420c B APIf ra empty) -> Hcut B APIf ra (Inv_K13110 B APIf ra empty).
Definition S_M02 : Prop :=
  Hcut B APIf ra (Inv_K14614 B APIf ra empty) -> Hcut B APIf ra (Inv_K1420c B APIf ra empty).
Definition S_M03 : Prop :=
  Hcut B APIf ra (Inv_K14660 B APIf ra empty) -> Hcut B APIf ra (Inv_K14614 B APIf ra empty).
Definition S_X01 : Prop := Hcut B APIf ra (Inv_K14660 B APIf ra empty).

Definition seg_lemmas : Prop := S_E01 /\ S_M01 /\ S_M02 /\ S_M03 /\ S_X01.

End Stmts.
