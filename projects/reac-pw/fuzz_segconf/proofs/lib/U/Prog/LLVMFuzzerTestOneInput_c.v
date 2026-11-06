(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/LLVMFuzzerTestOneInput_fr.v, with its module paths and module names changed; 456 of its 574 lines of code are new or changed and 409 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/Prog/Seg/Tac_slot.v, with its module paths and module names changed; 259 of its 298 lines of code are new or changed and 535 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/Prog/SegSlot.v, with its module paths changed; 21 of its 38 lines of code are new or changed and 281 lines of the source are left out. *)
(** LLVMFuzzerTestOneInput of fuzz_segconf.c:579-673, UBSan build (2528 bytes at 0x13888 in the UBSan image
    afc060e3cc9c; frame 240 bytes; U/FrameAPI.ENTRY): its slot statements. The plain file's form
    (lib/Prog/LLVMFuzzerTestOneInput_c.v) with the UBSan cuts and pcs. It allocates c = malloc(16616) and
    m = calloc(1, 9236), one text = malloc(n + 1) per file turn (freed in the same turn), tab = calloc(cap + 1, 18)
    and mt = calloc(cap + 1, 20), and frees mt, tab, m, c; the frame's obligation SlotFR.slot_goal (lib_contract_g for
    ENTRY with G = frame_G = longl (0x33460, 121) and GI = longl[120] = 0, from U/FrameAPI.frame_ubsan) is split at the
    cuts of SlotInv.v into the segment statements below, plus the n >= 2^26 run (0x138c4 `bnez a2` to 0x1420c:
    `mv a0,zero` and the epilogue, no call), which the slot proves as one evt (SegSlot.slot_early). What the whole
    function promises is lib_contract_g's (U/Contract.v), as in the plain file. On the way no check_* aborts and no
    UBSan trap branch (to the `unimp` at 0x14264) is taken: that is the content of the cut predicates carried from
    cut to cut, and of the walks.

    The segments (UBSan insns / conditional branches / calls / trap branches):
      S_E01, ENTRY -> K13984 (64 / 7 / 2 / 3): the prologue (saves at [S - 104, S)); n < 2^26 by GV, so 0x138c4
        falls through; the flags, cap and nfiles bytes; malloc(16616) at 0x1396c by Tac_b1.b1_malloc_call from hb = []
        and calloc(1, 9236) at 0x13980 by Tac_b1.b1_calloc_call from hb = [(c, 16616)] (premise:
        CallocBigC.calloc_contract_big at CALLOC_PC = 0x172a0).
      S_M01, K13984 -> K139e4 at f = 0 (25 / 2 / 2 / 0): the NULL tests of c and m (not taken: res <> 0) and
        reac_segconf_init(c) (an evt callee).
      S_L01, K139e4 f -> K13aac f (51 / 11 / 2 / 5): the label byte, fuzz_u16, the take, memchr (an evt callee), then
        malloc(n + 1) at 0x13aa8 by b1_malloc_call from hb = [m; c].
      S_L02, K13aac f -> K13c34 f (100 / 16 / 10 / 5): the NULL test of text, memcpy, the label (snprintf, or
        memset(longl, 'L', 120) at 0x13b18), m_file and reac_segconf_parse_file, or on the last turn m_file, m_cross
        (inlined, m_refuse) and reac_segconf_parse: all evt callees; FR across it by Tac_b1.b1_fr_hb with
        Wb = [text; m; c] and longl's written bytes.
      S_L03, K13c34 f -> K139e4 (S f) or K13c3c (2 / 1 / 1 / 0): free(text) at 0x13c34 by Tac_b8.b8_free_call with
        hb1 = [], hb2 = [m; c], then 0x13c38 `bne s0,s10` back to the head or out of the loop.
      S_M02, K13c3c -> K13e90 (150 / 19 / 21 / 10): the checks, reader queries, refusal and probe loops (evt callees),
        then calloc(cap + 1, 18) at 0x13e7c and calloc(cap + 1, 20) at 0x13e8c by b1_calloc_call from hb = [m; c]
        and [tab; m; c].
      S_V01, K13e90 -> K141ec (221 / 39 / 10 / 15): the NULL tests of tab and mt, the guard memset, "enp1s0",
        m_declared and m_split (inlined), reac_segconf_declared and check_declared (evt callees); FR by b1_fr_hb
        with Wb = [mt; tab].
      S_X01, K141ec -> RET (8 / 0 / 4 / 0, then the 16-instruction epilogue 0x1420c-0x14248): free(mt), free(tab),
        free(m), free(c) (0x141f0 .. 0x14208), each the head of hb, which leaves hb = []; `mv a0,zero`, the restores,
        `addi sp,sp,0xf0`, ret to ra: Post (Tac_b8.b8_post_FR).
    Statement text only: no function is proved here. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import SlotFR SlotInv.
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
  Hcut B APIf ra (Inv_K13984 B APIf ra empty CP) -> Hcut B APIf ra (Inv_ENTRY B APIf ra empty).
Definition S_M01 : Prop :=
  Hat B APIf ra (Inv_K139e4 B APIf ra empty CP) 0%nat -> Hcut B APIf ra (Inv_K13984 B APIf ra empty CP).
Definition S_L01 : Prop := forall f,
  Hat B APIf ra (Inv_K13aac B APIf ra empty CP) f -> Hat B APIf ra (Inv_K139e4 B APIf ra empty CP) f.
Definition S_L02 : Prop := forall f,
  Hat B APIf ra (Inv_K13c34 B APIf ra empty CP) f -> Hat B APIf ra (Inv_K13aac B APIf ra empty CP) f.
Definition S_L03 : Prop := forall f,
  Hat B APIf ra (Inv_K139e4 B APIf ra empty CP) (S f) -> Hcut B APIf ra (Inv_K13c3c B APIf ra empty CP) ->
  Hat B APIf ra (Inv_K13c34 B APIf ra empty CP) f.
Definition S_M02 : Prop :=
  Hcut B APIf ra (Inv_K13e90 B APIf ra empty CP) -> Hcut B APIf ra (Inv_K13c3c B APIf ra empty CP).
Definition S_V01 : Prop :=
  Hcut B APIf ra (Inv_K141ec B APIf ra empty CP) -> Hcut B APIf ra (Inv_K13e90 B APIf ra empty CP).
Definition S_X01 : Prop := Hcut B APIf ra (Inv_K141ec B APIf ra empty CP).

Definition seg_lemmas : Prop :=
  S_E01 /\ S_M01 /\ S_L01 /\ S_L02 /\ S_L03 /\ S_M02 /\ S_V01 /\ S_X01.

End Stmts.
