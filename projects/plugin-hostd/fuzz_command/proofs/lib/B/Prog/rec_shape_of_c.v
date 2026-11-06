(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: check_reply's ASan walk (fuzz_command.asan, 0x86d78) assembled from its
   segments, as proofs/cgif/cgif_file_fuzzer/lib/A/ACh5.v assembles cgif_close's (pb_cgif_closeX):
     s1 the entry to the memchr call, s2 memchr / check_reply_answer / sup_reply_code, s3 the code's split,
     s4 snprintf, s4b rec_code_declared, s5 strcmp, s6 strlen / rec_shape_of, s7 syntax_reply_matches twice,
     s8 the frame's release and the return.
   snprintf is the only call that changes the FP state, so s4b, s5 and s8 (the segments after it) are taken at every
   FP state and s4 uses them at the state the wrapper returns.
   `pb_check_reply` is tcheck_reply_spec (lib/A/Prog/check_reply_c.v). The walk's facts at the entry that the
   statement no longer states come from its premises: the record's cells (replace_str flag byte, stack guard, errno)
   from CmdRecCells' cmd_rec_cells, the recorder's GOT words from cmd_ro_ok's RO_ptr_a70xx bytes, the read-only
   ranges from CmdRecRo's cmd_ro_in_img, and the words' shadow from AR's zshadow_ok of the stack window
   [ly_stk_lo, ly_stk_hi) (the words lie in it: spZ regs <= w and w + WORDS_W + 12 <= ly_stk_hi ly). The kit lemmas
   take the image facts IMG (cmd_img_facts); the segments take CmdRecImg's cmd_heap_tail_vis, and its
   cmd_prog_unowned and cmd_rom_view_on at IMG, so no record fact is a Section hypothesis (the walk hypotheses keep
   cgif's names; the record facts are lemmas of lib/A/Prog/CmdRecFacts.v). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply.v, with its module paths and module names changed; 29 of its 57 lines of code are new or changed and 124 lines of the source are left out. *)
(* The contract of rec_shape_of on the ASan+UBSan build of plugin-hostd/fuzz_command (image fuzz_command.asan-ubsan).

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): afn_pre_na
   (lib/B/Prog/PaNoChain.v, cgif's afn_pre without the frame-chain conjunct: the function reaches no allocator and
   no side-stack entry) at the entry, SRr of apost_base at the return. Functional content: fuzz_command's own
   released plain contract lib/Prog/rec_shape_of_c.v:58-80 (a0 = shape_find shape_rows v: the reply shape of the row
   whose name is the verb, else mod-host's "resp 0"; the `a1 <= 16 ->` premise on the verb's bytes, :66-69), stated
   with the address-free form of the same table, lib/Prog/RecFacts.v:280-319 (shape_table, shape_lookup, shape_of),
   used as it is.
   The function (recorder.c:77-85) scans the 28 rows of the read-only table g_shapes (0xa5a20, 16 bytes a row:
   name pointer, reply pointer): for each row it asks the strlen wrapper (`___interceptor_strlen`, reached through
   the 4-byte jump `__interceptor_trampoline_strlen`) for the name's length and, when it equals len, compares the
   name with the verb through the bcmp wrapper (`__interceptor_trampoline_bcmp`); at the first match it returns the
   row's reply pointer, else the literal "resp 0" (.str 0x21d20 of fuzz/recorder.c). The two 8-byte loads from
   g_shapes have inline checks; g_shapes is a registered global of 448 bytes (asan_globals descriptor,
   size_with_redzone 544), so its shadow bytes say usable (CmdRecFacts' cmd_addressable_chk) and the error path (a
   call of `__asan_report_load8`) is not reached. The table and the 56 strings it points to, and .str 0x21d20, are
   among the image's read-only bytes (cmd_ro_ok, lib/B/Prog/CmdRo.v: RO_g_shapes and the RO_lit_* lists); what the
   strlen and bcmp wrappers ask of a name (aread_ok, the bytes after its terminator) comes from cmd_aread_ok_chk and
   cmd_tail_vis, and what the bcmp wrapper asks of a read-only verb (in the image, shadow words visible, off the
   scratch window) from cmd_ro_rd. No CmdRecFacts fact is a premise here.

   The post names the returned address by what it holds: a read-only string equal to shape_of v, which no runtime
   entry owns and which is not the errno cell (the read-only branch of astr_argA, lib/B/Prog/CmdRep.v). The walk
   proves which literal it is from RO_g_shapes and the unowned part from cmd_img_facts' cif_ro_unowned; no caller
   needs the address itself (check_reply passes it to syntax_reply_matches, the recorder's verbs to answer, both of
   which take the string as astr_argA).

   UBSan: no trap site and no `unimp` in the function (the trap-site summary). B's instruction stream is A's with
   only the pc-relative offsets changed (the shadow-base GOT word 0xa5f50, g_shapes, .str).

   Addresses: entry BASE + AF_rec_shape_of = 0x896d4 (B, the pinned image). 69 instructions, frame 96 bytes, no
   side-stack frame, 2 inline checks (0x89740, 0x89798), 1 loop (28 iterations, s5 steps by -2 from 0 to -56, back
   edge 0x89778 -> 0x8973c), 0 UBSan trap sites. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep
  CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaNoChain.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* the stack this call needs: its own 96-byte frame, and below it the bcmp wrapper's window (2 * ESTACK, cgif's
   abcmp_realizes, lib/YG0d.v:355), which covers the strlen wrapper's (ESTACK, the runtime contracts' final windows) *)
Definition REC_SHAPE_OF_STK : Z := 96 + 2 * ESTACK.
Definition EV_REC_SHAPE_OF : Z := 0.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the runtime entries the call reaches, with this tree's and cgif's names *)
Hypothesis ASTRLEN : forall fx0 : YK11.FPState, @astrlen_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strlen).
Hypothesis ABCMP : forall fx0 : YK11.FPState, @abcmp_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_bcmp).
(* `using MT`: the post has no meter conjunct (frame form), so MT is named here to keep the uniform signature
   trec_shape_of_spec B MT *)
#[using="MT"]
Definition trec_shape_of_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md (p : Z) (v : list byte),
afn_pre_na SEGS B REC_SHAPE_OF_STK ly S W regs mem md ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
(* the verb and its length (plain rec_shape_of_c.v:66) *)
getr regs 10 = w64 p -> 0 <= p < 2 ^ 64 ->
getr regs 11 = w64 (Z.of_nat (length v)) -> Z.of_nat (length v) < 2 ^ 64 ->
(* the table and the strings it points to (plain :64), each byte of them read-only (what astr_argA's read-only
   case of the post asks; that each lies in the read-only range is a constant fact, cmd_ro_in_img, which every walk
   has), and the bridge from the listing's object atoms to the table's address (lib/B/Prog/CmdObj.v) *)
cmd_ro_ok (rdW W mem) -> cmd_val_objs ->
(* the verb's bytes, which the bcmp wrapper reads only when len equals a name's length, so len <= 16
   (plain :67-69). Two kinds of caller: a byte range inside a live block that need not end in a NUL
   (sup_instance_verb passes line + strspn with the strcspn length, 0x8ba3c-0x8ba7c), or a whole string, the
   read-only literals (sup_worker_list's "worker_list" 0x21dc0 with 11, descriptors_get's 0x21fa0 with 14,
   sup_chain's 0x21f60 with 5, ...) and check_reply's word w0 (strlen, 0x87078-0x8708c), stated through
   astr_argA itself so its read-only arm is the one every other statement uses *)
(Z.of_nat (length v) <= 16 ->
 abytes_atR (rdW W mem) p v /\
 (in_blockA (ablocks B ly S) p (Z.of_nat (length v)) \/
  astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) [] p (Some v))) ->
st_nev S + EV_REC_SHAPE_OF <= EV_MAX ->
SRr SEGS W (cfg_at SEGS (BASE + AF_rec_shape_of) regs mem md)
(apost_base SEGS B REC_SHAPE_OF_STK [] regs ly S W mem md EV_REC_SHAPE_OF
(fun ly' S' W' regs' mem' md' =>
 (* a0: the reply shape's literal in the table's read-only strings (the plain post names shape_find of the
    shape rows, plain rec_shape_of_c.v:72), stated as astr_argA (lib/B/Prog/CmdRep.v) for ANY owned-block list:
    the pre form its users ask (answer's shape premise, syntax_reply_matches' shape premise; check_reply passes it
    on at 0x870e4-0x870f0). It holds through the read-only arm: every byte read-only (cmd_ro_in_img), owned by no
    runtime entry and not the errno cell (cmd_img_facts' cif_ro_unowned), and the record's checks cmd_addr_b,
    cmd_hull_b and the literal's end in cmd_ro_ends, each by computation over the 28 rows and .str 0x21d20; a heap
    result would have to be apart from every list O, and this one never is a block. *)
 (exists q, getr regs' 10 = w64 q /\ 0 <= q < 2 ^ 64 /\
  forall O, astr_argA B ly' S' (rdW W' mem') (in_roP SEGS RLO RHI) O q (Some (shape_of v))) /\
 Permutation (ablocks B ly' S') (ablocks B ly S) /\
 (* it allocates nothing and takes no side-stack frame: layout and allocator state unchanged (M6; mo_le_refl
    gives the meter) *)
 ly' = ly /\ S' = S)).
End e.
End f.
End d.
