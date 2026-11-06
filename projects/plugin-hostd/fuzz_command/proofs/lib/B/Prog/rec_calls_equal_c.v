(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the program walk of rec_calls_free on the ASan build of plugin-hostd/fuzz_command
   (0x8953c, 96 instructions, two loops), in the shape of cgif_file_fuzzer's walks (lib/A/AChc.v, ACh1..ACh3.v: one
   statement per loop point, each proved by a run of the symbolic executor from a fresh seed) and of this unit's
   sup_reply_code.v / xstrdup.v: the executor over the position-abstract listing (CmdPaLib.v), the inline checks removed
   by the shadow tokens (PaShadow.v), the free calls through afree04_sub (PaCall.v).
   Loop points: OUTER at 0x895b4 (entry i of the table, its nargs address in s2), INNER at 0x895e8 (argument a of
   entry i), TAIL at 0x89624 (the nargs store of entry i); the entry 0x8953c and the epilogue 0x89668 are walked once.
   Section hypotheses beyond the statement's AFREE4: HB (the image's symbol record, whose ts_prog names the program
   statics and whose zero-shadow ranges cover g_rec's call table and record.spill, CmdZsh.v cmd_addressable_in), TL
   (the free trampoline is the free rule's entry), MTL (the meter laws), PRW (prog_rw, YCbq.v: the program statics
   are writable) and IMG (the image facts, cmd_img_facts, whose cif_prog_img says every byte of
   g_rec / record.spill / g_quitting is in the image; CmdRecFacts.v).
   The nargs store into a table in a caller's side-stack frame is the frames-of-S clause of awr_byte (YCbq.v). The
   recorder conjuncts of the post are reduced to the reader lemmas of rec_calls_free_rep.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/rec_calls_free.v, with its module paths and module names changed; 44 of its 85 lines of code are new or changed and 1442 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/rec_calls_free_c.v, with its module names changed; 36 of its 68 lines of code are new or changed and 53 lines of the source are left out. *)
(* The contract of rec_calls_equal on the ASan+UBSan build of plugin-hostd/fuzz_command (image fuzz_command.asan-ubsan).

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): afn_pre at the entry,
   SRr of apost_base at the return. Functional content: fuzz_command's own released plain contract
   lib/Prog/rec_calls_equal_c.v:11-69 (rc_entry, entry_at, calls_at; the result `calls_eqb ca cb`, :42-47, used as it
   is). rec_calls_equal(a, na, b, nb) (H/recorder.c:162-177) returns 0 when na <> nb; otherwise it compares, entry by
   entry, the function numbers and the argument counts, and each pair of arguments with the strcmp wrapper
   (`___interceptor_strcmp`, reached through the 4-byte jump `__interceptor_trampoline_strcmp`), and returns 1 when
   all agree. It writes nothing outside its own frame and allocates nothing (FP = [], no meter).

   Addresses: entry BASE + AF_rec_calls_equal = 0x89ef8 (B, the pinned image). 164 instructions, frame 144 bytes,
   2 loops (0x89f98, 0x8a064), no side-stack frame, 6 inline checks: load4 on a[i].fn, b[i].fn, a[i].nargs,
   b[i].nargs (0x89fcc, 0x8a000, 0x8a020, 0x8a034) and load8 on a[i].args[k], b[i].args[k] (0x8a078, 0x8a08c), each
   a read of the shadow byte at (a >> 3) + SHADOW_OFF through the shadow base word (0xa5f50, a RELRO word
   arodata_okP keeps). The error path (a call of `__asan_report_load4` / `__asan_report_load8`, 0x8a11c, 0x8a16c,
   0x8a170, 0x8a174, 0x8a17c, 0x8a184) is not reached: each table lies in g_rec, in record.spill (shadow usable by
   `cmd_addressable_chk`) or in a side-stack frame object (rce_home). Every argument string is a live block: its one
   caller, check_round_trip (0x88594), hands it g_rec's table (acall_at puts every argument in a block) and first[],
   whose arguments are rec_calls_copy's fresh copies; the strcmp wrapper's reads come from AR's block facts and each
   tail word from `cmd_heap_tail_vis`. s0 holds ~(b[i].args) (0x8a05c) at the strcmp calls; no program call. It
   reaches no heap allocator and no side-stack frame: the post keeps ly and S.

   UBSan (B only, 8 trap sites, all to the one `unimp` at 0x8a168): 0x89fac, 0x89fb4 and 0x89fbc are the three
   checks of `a[i]` at recorder.c:170 (the result null while `a` is not; unsigned wrap of a + 56i; `a` null or not
   8-aligned); 0x89fe4, 0x89fec and 0x89ff4 are the same three for `b`; 0x8a064 and 0x8a068 are the wrap of
   a[i].args + 8k and b[i].args + 8k at recorder.c:173. rce_calls carries the one condition rce_home does not give,
   `a mod 8 = 0` (it admits any address in the g_rec and record.spill ranges); the rest follow from rce_home: the
   two global ranges are constants above 0 and far below 2 ^ 64, a frame object is in_app by AR_frames_law
   (4096 <= frame_addr, frame_addr + bytes <= ASAN_CEIL, lib/Reusable/YG0d.v:455-463), and nargs <= 6 keeps
   args + 8k inside the entry. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require rec_calls_equal_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaNoChain.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Module PRce := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.rec_calls_equal_c.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
#[local] Notation PC_STRCMP := (@pa_sigma _ cmd_listing PI CS___interceptor_trampoline_strcmp).
(* the stack this call needs: its own 144-byte frame, and the window the strcmp wrapper asks for (RtString.v's
   astrcmp_realizes, ecall_pre_stk segs B (2 * ESTACK)) *)
Definition REC_CALLS_EQUAL_STK : Z := 144 + 2 * ESTACK.
Definition EV_REC_CALLS_EQUAL : Z := 0.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* where a table lies: in g_rec's call table, in record.spill (registered globals, shadow usable by
   `cmd_addressable_chk`), or in an object of a live side-stack frame (check_round_trip's first[]) *)
Definition rce_home (ly : alayout) (S : astate) (W : world SEGS) (mem : word -> option byte) (a n : Z) : Prop :=
(A_G_REC + OFF_CALLS <= a /\ a + n <= A_G_REC + REC_SIZE) \/
(A_REC_SPILL <= a /\ a + n <= A_REC_SPILL + SC_SIZE) \/
afobj SEGS B ly S W mem a n.
(* a table of recorded calls at a: the plain proof's calls_at / entry_at / arg_at (rec_calls_equal_c.v:15-30) over
   the reader, each argument a string inside a live block (every caller passes blocks). `a mod 8 = 0` is the one
   UBSan condition rce_home does not give (0x89fbc for a, 0x89ff4 for b, recorder.c:170) *)
Definition rce_calls (ly : alayout) (S : astate) (W : world SEGS) (mem : word -> option byte) (a : Z)
(cs : list PRce.rc_entry) : Prop :=
(length cs <= 16)%nat /\ a mod 8 = 0 /\
rce_home ly S W mem a (CALL_SIZE * Z.of_nat (length cs)) /\
forall i e, nth_error cs i = Some e ->
 -2^31 <= fst e < 2^31 /\ (length (snd e) <= 6)%nat /\
 aval_mem (rdW W mem) (a + CALL_SIZE * Z.of_nat i + CALL_OFF_FN) 4 (fst e) /\
 aval_mem (rdW W mem) (a + CALL_SIZE * Z.of_nat i + CALL_OFF_NARGS) 4 (Z.of_nat (length (snd e))) /\
 forall k p, nth_error (snd e) k = Some p ->
   aval_mem (rdW W mem) (a + CALL_SIZE * Z.of_nat i + CALL_OFF_ARGS + 8 * Z.of_nat k) 8 (bv_unsigned (fst p)) /\
   in_blockA (ablocks B ly S) (bv_unsigned (fst p)) (Z.of_nat (length (snd p)) + 1) /\
   astr_atR (rdW W mem) (bv_unsigned (fst p)) (snd p).
(* the runtime entry the call reaches *)
Hypothesis ASTRCMP : forall fx0 : YK11.FPState, @astrcmp_realizes fx0 rc SEGS B PC_STRCMP.
(* `using MT`: the post has no meter conjunct (frame form), so MT is named here to keep the uniform signature
   trec_calls_equal_spec B MT *)
#[using="MT"]
Definition trec_calls_equal_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md (a b : Z) (ca cb : list PRce.rc_entry),
afn_pre_na SEGS B REC_CALLS_EQUAL_STK ly S W regs mem md ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
getr regs 10 = w64 a -> getr regs 11 = w64 (Z.of_nat (length ca)) ->
getr regs 12 = w64 b -> getr regs 13 = w64 (Z.of_nat (length cb)) ->
rce_calls ly S W mem a ca -> rce_calls ly S W mem b cb ->
st_nev S + EV_REC_CALLS_EQUAL <= EV_MAX ->
SRr SEGS W (cfg_at SEGS (BASE + AF_rec_calls_equal) regs mem md)
(apost_base SEGS B REC_CALLS_EQUAL_STK [] regs ly S W mem md EV_REC_CALLS_EQUAL
(fun ly' S' W' regs' mem' md' =>
 (* 1 when the two tables hold the same calls, else 0 (plain rec_calls_equal_c.v:61) *)
 getr regs' 10 = w64 (if PRce.calls_eqb ca cb then 1 else 0) /\
 Permutation (ablocks B ly' S') (ablocks B ly S) /\
 (* no allocator and no side-stack frame: the layout and the allocator state are kept *)
 ly' = ly /\ S' = S)).
End e.
End f.
End d.
