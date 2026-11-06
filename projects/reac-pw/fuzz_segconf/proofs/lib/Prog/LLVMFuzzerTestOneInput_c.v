(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/LLVMFuzzerTestOneInput_fr.v, with its module paths and module names changed; 456 of its 574 lines of code are new or changed and 409 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/Prog/Seg/Tac_slot.v, with its module paths and module names changed; 259 of its 298 lines of code are new or changed and 535 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/Prog/SegSlot.v; 21 of its 38 lines of code are new or changed and 281 lines of the source are left out. *)
(** LLVMFuzzerTestOneInput of fuzz_segconf.c:579-673 (2032 bytes at 0x137c4 in the plain image 8dec0b814e6f; frame
    208 bytes; FrameAPI.ENTRY): its slot statements. It allocates c = malloc(16616) and m = calloc(1, 9236), one
    text = malloc(n + 1) per file turn (freed in the same turn), tab = calloc(cap + 1, 18) and mt = calloc(cap + 1,
    20), and frees mt, tab, m, c; so its contract is in the form libreac/fuzz_ctrl's released slot consumes, as
    reac-pw/fuzz_role's and reac-pw/fuzz_pin's: the frame's obligation SlotFR.slot_goal (lib_contract_g for ENTRY
    with G = frame_G = longl and GI = longl[120] = 0, from FrameAPI.frame_plain), split at the cuts of SlotInv.v into
    the segment statements below (ctrl's continuation form: the H of each exit cut -> the H of the entry cut; the
    file loop's cuts are indexed by the turn f, and its turn statements S_L01 .. S_L03 are for every f), plus the
    n >= 2^26 run (0x13800 `bnez a2` to 0x13f60: `mv a0,zero` and the epilogue, no call), which the slot proves as
    one evt (SegSlot.slot_early). What the whole function promises is lib_contract_g's: from lib_pre at ENTRY it
    returns to ra with a0 = 0, every callee-saved register as at entry, the allocator back to its entry blocks
    (RES_END), the input bytes unchanged, no byte changed outside [sp - 65536, sp), longl and the allocator's own
    state, longl[120] still 0, at an FP state with frm = 0 (lib_post over frame_G). On the way no check_* aborts:
    that is the content of the cut predicates carried from cut to cut.

    The segments (plain insns / conditional branches / calls):
      S_E01, ENTRY -> K138a4 (56 / 4 / 2): the prologue (saves at [S - 104, S)); n < 2^26 by GV, so 0x13800 falls
        through; the flags, cap and nfiles bytes (fuzz_u8); malloc(16616) at 0x1388c by Tac_b1.b1_malloc_call from
        hb = [] and calloc(1, 9236) at 0x138a0 by Tac_b1.b1_calloc_call from hb = [(c, 16616)] (premise:
        CallocBigC.calloc_contract_big at CALLOC_PC).
      S_M01, K138a4 -> K138e8 at f = 0 (18 / 2 / 2): the NULL tests of c and m (not taken: res <> 0) and
        reac_segconf_init(c) (an evt callee: memset(c, 0, 16616)).
      S_L01, K138e8 f -> K13984 f (39 / 6 / 2): fuzz_u8 (the label byte), fuzz_u16, the take, memchr (an evt callee),
        then malloc(n + 1) at 0x13980 by b1_malloc_call from hb = [m; c].
      S_L02, K13984 f -> K13ad8 f (86 / 11 / 10): the NULL test of text, memcpy(text, p, n), the label (snprintf, or
        memset(longl, 'L', 120) when the label byte has bit 7), m_file and reac_segconf_parse_file, or on the last
        turn m_file, m_cross (inlined, m_refuse) and reac_segconf_parse: all evt callees; FR across it by
        Tac_b1.b1_fr_hb with Wb = [text; m; c] and longl's written bytes.
      S_L03, K13ad8 f -> K138e8 (S f) or K13ae0 (2 / 1 / 1): free(text) at 0x13ad8 by Tac_b8.b8_free_call with
        hb1 = [], hb2 = [m; c] (its continuation keeps m's and c's bytes), then 0x13adc `bne s11,s2` back to the
        head (S f < nfiles) or out of the loop.
      S_M02, K13ae0 -> K13cac (115 / 9 / 21): check_segments, the per-segment reader queries and checks, the refusal
        and probe loops, m_find, check_absent (evt callees), then calloc(cap + 1, 18) at 0x13c98 and calloc(cap + 1,
        20) at 0x13ca8 by b1_calloc_call from hb = [m; c] and [tab; m; c].
      S_V01, K13cac -> K13f40 (170 / 24 / 10): the NULL tests of tab and mt, the 0x5a guard (memset), "enp1s0"
        (memcpy), m_declared and m_split (inlined: strrchr, memcpy, strcmp), reac_segconf_declared and
        check_declared (evt callees); FR by b1_fr_hb with Wb = [mt; tab].
      S_X01, K13f40 -> RET (8 / 0 / 4, then the 16-instruction epilogue): free(mt), free(tab), free(m), free(c), each
        the head of hb (b8_free_call with hb1 = []), which leaves hb = []; `mv a0,zero`, the restores from the saved
        bytes, `addi sp,sp,0xd0`, ret to ra: Post (Tac_b8.b8_post_FR; RES_END by resb_end).
    Statement text only: no function is proved here. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import SlotFR SlotInv.
Import ListNotations.
Open Scope Z_scope.

(** ** The segment statements (ctrl's Slot.v Section Stmts form, with ctrl's turn-indexed cuts for the file loop) *)
Section Stmts.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Variable CP : cut_preds.

Definition S_E01 : Prop :=
  Hcut B APIf ra (Inv_K138a4 B APIf ra empty CP) -> Hcut B APIf ra (Inv_ENTRY B APIf ra empty).
Definition S_M01 : Prop :=
  Hat B APIf ra (Inv_K138e8 B APIf ra empty CP) 0%nat -> Hcut B APIf ra (Inv_K138a4 B APIf ra empty CP).
Definition S_L01 : Prop := forall f,
  Hat B APIf ra (Inv_K13984 B APIf ra empty CP) f -> Hat B APIf ra (Inv_K138e8 B APIf ra empty CP) f.
Definition S_L02 : Prop := forall f,
  Hat B APIf ra (Inv_K13ad8 B APIf ra empty CP) f -> Hat B APIf ra (Inv_K13984 B APIf ra empty CP) f.
Definition S_L03 : Prop := forall f,
  Hat B APIf ra (Inv_K138e8 B APIf ra empty CP) (S f) -> Hcut B APIf ra (Inv_K13ae0 B APIf ra empty CP) ->
  Hat B APIf ra (Inv_K13ad8 B APIf ra empty CP) f.
Definition S_M02 : Prop :=
  Hcut B APIf ra (Inv_K13cac B APIf ra empty CP) -> Hcut B APIf ra (Inv_K13ae0 B APIf ra empty CP).
Definition S_V01 : Prop :=
  Hcut B APIf ra (Inv_K13f40 B APIf ra empty CP) -> Hcut B APIf ra (Inv_K13cac B APIf ra empty CP).
Definition S_X01 : Prop := Hcut B APIf ra (Inv_K13f40 B APIf ra empty CP).

Definition seg_lemmas : Prop :=
  S_E01 /\ S_M01 /\ S_L01 /\ S_L02 /\ S_L03 /\ S_M02 /\ S_V01 /\ S_X01.

End Stmts.
