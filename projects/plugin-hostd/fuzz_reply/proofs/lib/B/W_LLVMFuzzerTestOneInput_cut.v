(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the cut points and the composition of the ASan+UBSan walk of fuzz_reply's
   LLVMFuzzerTestOneInput (fuzz_reply.asan-ubsan 0x84408, 868 instructions to 0x85190), the image-B twin of
   lib/A/W_LLVMFuzzerTestOneInput_cut.v.  A NEW WALK, not a relocation: B allocates registers differently, calls
   relay_source and relay_reads where A inlines them, and inserts 32 UBSan trap branches to `unimp` (0x850fc).
   FROZEN once pushed: change a statement only through lane W8Entry-2.

   What this file proves, and how it differs from the other lanes' per-function theorems: as lib/A's twin.  The other
   lanes prove `fn_spec B (BASE + AF_fr_<fn>)`, an SRr from a function's entry to an `ajournal` post.  This file
   states the PROGRAM CONTRACT that TFIB_B_T consumes (lib/B/YCfn.v tfib_lib_contract_x at A_LLVMF 0x84408,
   RA_LLVMF 0x82240, A_EMPTY 0x5d8ca0) at checksum_shape (lib/ZTraceSpec.v), in the live-state `cf` form: the three
   clauses the cf variant changes are the Section parameters fr_live_pre / fr_live_post / fr_surv, the post's journal
   is W2's ajournal_gx over G_fr (lib/B/W_LLVMFuzzerTestOneInput_G.v G_fr_c), and the footprint is fr_FP.

   ------------------------------------------------------------------ the A -> B cut map (read from both objdumps)
   A pcs: fuzz_reply.asan objdump beside the pinned image (sha256 42c58610e125e0b4...), LLVMFuzzerTestOneInput 0x840b0, fr_B0 0x822ec.
   B pcs: fuzz_reply.asan-ubsan objdump beside the pinned image (sha256 10ffb5f9202ae2bd...), fr_B0 0x82344.
   A `jal`/`j` op_str is the RELATIVE immediate; the targets below are pc + imm, taken from objdump's own labels.

   | point        | A pc    | A off(fr_B0) | B pc    | B off(fr_B0) | B code                                        |
   |--------------|---------|--------------|---------|--------------|-----------------------------------------------|
   | entry        | 0x840b0 | 0x1dc4       | 0x84408 | 0x20c4       | addi sp,sp,-320                               |
   | H  loop head | 0x842a0 | 0x1fb4       | 0x845e0 | 0x229c       | beqz s5,84e64  (B tests in.n AT the head)     |
   | D  dispatch  | 0x843fc | 0x2110       | 0x8475c | 0x2418       | li a0,8                                       |
   | A0 add       | 0x84420 | 0x2134       | 0x84780 | 0x243c       | sd t1,144(s1); jal op_add                     |
   | A1 write     | 0x843bc | 0x20d0       | 0x84724 | 0x23e0       | beqz t1,8478c  (list_push)                    |
   | A2 drain     | 0x84520 | 0x2234       | 0x8489c | 0x2558       | beqz s5,850fc  (CALLS relay_source 0x848c0)   |
   | A3 close     | 0x84588 | 0x229c       | 0x84938 | 0x25f4       | beqz s5,850fc  (s->closed = 1)                |
   | A4 remove    | 0x844b4 | 0x21c8       | 0x84824 | 0x24e0       | sd t1,144(s1)  (CALLS relay_reads 0x84830)    |
   | A5 gone      | 0x845e4 | 0x22f8       | 0x849a0 | 0x265c       | sd s9,88(s1)   (CALLS relay_reads 0x84b0c)    |
   | A6 eintr     | 0x84614 | 0x2328       | 0x849d4 | 0x2690       | beqz s5,850fc  (s->eintr = 1)                 |
   | A7 event     | 0x845b4 | 0x22c8       | 0x8496c | 0x2628       | sd s9,88(s1)   (strnlen/malloc/relay_event)   |
   | A8 sendmax   | 0x84638 | 0x234c       | 0x84a00 | 0x26bc       | beqz t1,84cb8                                 |
   | A9 default   | 0x84660 | 0x2374       | 0x84a30 | 0x26ec       | beqz t1,84cd4                                 |
   | K  latch     | 0x84490 | 0x21a4       | 0x84804 | 0x24c0       | jal check_bounded                             |
   | X  exit      | 0x84bf8 | 0x290c       | 0x84e64 | 0x2b20       | lw s3,-324(a0) [g_nsrc]                       |
   | unimp (trap) | -       | -            | 0x850fc | 0x2db8       | the one UBSan trap landing pad                |
   Calls the segments cross, B pc -> callee: 0x84478 __asan_stack_malloc_1, 0x84590 and 0x84784 op_add,
   0x847fc list_push, 0x84804 check_bounded, 0x84830 and 0x84b0c relay_reads, 0x84858 relay_remove,
   0x84864 / 0x8491c / 0x84b68 check_no_loss_read, 0x84870 / 0x84928 / 0x84c14 check_no_loss,
   0x84884 / 0x84c24 / 0x84f8c check_shape_ends, 0x8488c / 0x84930 / 0x84c88 / 0x84fec check_shape_done,
   0x84894 / 0x85008 source_reset, 0x848c0 relay_source, 0x84900 / 0x84a6c pthread_mutex_lock,
   0x84908 drain, 0x84914 / 0x84a80 pthread_mutex_unlock, 0x84ae0 snprintf trampoline,
   0x84b48 relay_instance_gone, 0x84d3c strnlen trampoline, 0x84d48 malloc trampoline, 0x84d5c __asan_memcpy,
   0x84d8c relay_event, 0x84d94 check_shape_event, 0x84d9c free trampoline, 0x84f04 / 0x84fe4 relay_finish.

   ------------------------------------------------------------------ B vs A, the STRUCTURAL differences
   (1) OUT-OF-LINE CALLEES.  B CALLS relay_source (0x85d28, AF_fr_relay_source 0x39e4) at 0x848c0 inside ARM_drain,
       and relay_reads (0x864e8, AF_fr_relay_reads 0x41a4) at 0x84830 inside ARM_remove and at 0x84b0c inside
       ARM_gone, where A walks the inlined g_src scan.  Neither has a kit spec (lib/B/W_contract.v) nor an A
       statement.  They are the two Section hypotheses RSRC and RRDS below, in the kit's `aleafx_post` form (both
       are pure read-only leaves: they allocate nothing, free nothing, write no global).  Their text is the
       interface W8Entry-2 agrees with the contract writer; the three arms consume it.
   (2) THE LOOP TEST MOVED TO THE HEAD.  A tests `in.n != 0` at the latch (0x844ac `bnez s5,842a0`) and enters the
       head with bytes left; B tests it AT the head (0x845e0 `beqz s5,84e64`).  So B's INV_H carries
       `0 <= lm_k m <= c_n cx` where A's carries `0 <= lm_k m < c_n cx`, and B's SEG_PRO lands on INV_H alone
       (A's lands on `INV_H \/ INV_X`, because A's prologue holds the empty-input branch at 0x84244).
   (3) NO `full` FLAG.  A stores seven frame slots only after the empty-input exit (0x84270-0x8429c), so its
       aframe_at takes `full : bool` and INV_X uses `false`.  B stores every slot in the prologue, before the head
       (0x844ac-0x845d8), so B's aframe_at has no `full` and every cut point carries the whole frame.
   (4) DIFFERENT FRAME SLOTS AND REGISTERS.  B: s11 = SB (A: s10), s9 = t (A: s11), s7 = 1 (A: t2), s4 = the input
       cursor and t1 = the bytes left (A: t3 / t4), s5 = the picked source (same), s10 = HI_G_NOUT (A: s9),
       s2 = HI_G_SRC (same number, other value).  B keeps NO g_nsrc high half in a register (A keeps s7); its exit
       and ARM_gone re-derive it with auipc.  B has no `li s4,10` modulus register (A's reg 20): it materialises 10
       inline at 0x8460c.  Frame: B F+32/40/48/56/64/72/80/96/104/120/128/136/152/184, A F+24/32/48/56/64/72/80/88/
       96/104/112/120/128/136/152/184.
   (5) THE JUMP TABLE IS AT THE SAME ADDRESS (0x20e54, B object A_OBJ 24, A object A_OBJ 27) WITH OTHER WORDS: the
       nine 32-bit table-relative offsets are B's arm offsets (fr_jt_off below, read from the pinned ELF).  The
       dispatch code is instruction-for-instruction A's, so lf_seg_jt is re-proved here at B.
   (6) B's fake frame IS REAL.  B's LLVMFuzzerTestOneInput calls __asan_stack_malloc_1 at 0x84478 (128 bytes) and
       releases it at 0x85014-0x85074 with `ld a0,120(s4); sb zero,0(a0)`, exactly as A does; so B's lcut keeps the
       fake frame, fpos, the 16 shadow bytes and the flag word.  (The port's note that the fake frame belongs to
       `wake` alone is FALSE for this function: checked in B's own objdump, 0x84474-0x84488 and 0x8506c.)

   ------------------------------------------------------------------ the 32 UBSan trap branches (all -> 0x850fc)
   Census agrees with TRAPS-ALL.md (sha256 c90982171c9b; internal record): PTR_INC 9, NONNULL 7, ALIGN8 7, PTR_BLTU 4, NULL_XOR 2, ADDW 1,
   PTR_NOT 1, BASE_OK 1.  Each row names the lib/B/W_traps.v lemma that refutes it BY SHAPE; no walk may hand-roll
   a refutation (MERGE.md (sha256 0694aca87ccd; internal record) rule 4).  "seg" is the segment hypothesis below that crosses the branch.
     seg        B pc      branch                              shape      W_traps.v lemma      refuted by
     SEG_HEAD   0x845e8   bgeu s7,s4  (s4 = p+k+1, s7 = 1)    PTR_INC    trap_ptr_inc         0 < p, p + n < 2^47
     SEG_HEAD   0x84638   bgeu s7,a0  (a0 = p+k+2)            PTR_INC    trap_ptr_inc         same
     SEG_HEAD   0x8468c   bne a7,a3   (nopen accumulator)     ADDW       trap_addw1           0 <= nopen <= 4
     ARM_write  0x8472c   bgeu s7,a0                          PTR_INC    trap_ptr_inc         same
     ARM_write  0x847a0   bgeu s7,a2                          PTR_INC    trap_ptr_inc         same
     ARM_write  0x847d4   bltu s6,s4  (s6 = cursor + len)     PTR_BLTU   trap_ptr_bltu        len <= n, p+n < 2^47
     ARM_write  0x847d8   beqz s6                             NONNULL    trap_nonnull         0 < p
     ARM_write  0x847f0   bnez a0     (andi s5,7)             ALIGN8     trap_align8          g_s 32-aligned, ASRC 96
     ARM_remove 0x84834   beqz s5                             NONNULL    trap_nonnull         s5 = g_s + 96 i
     ARM_remove 0x84840   bnez a0     (andi s5,7)             ALIGN8     trap_align8          same
     ARM_drain  0x8489c   beqz s5                             NONNULL    trap_nonnull         same
     ARM_drain  0x848a4   bnez a0     (andi s5,7)             ALIGN8     trap_align8          same
     ARM_drain  0x848d4   bnez a0     (andi a0,7; a0 = entry) ALIGN8     trap_align8          RSRC's post: 8 | result
     ARM_close  0x84938   beqz s5                             NONNULL    trap_nonnull         same
     ARM_close  0x84940   bnez a0                             ALIGN8     trap_align8          same
     ARM_event  0x84978   bgeu s7,s5                          PTR_INC    trap_ptr_inc         same
     ARM_event  0x84cf8   bgeu s7,a1                          PTR_INC    trap_ptr_inc         same
     ARM_event  0x84d2c   bltu s4,s5                          PTR_BLTU   trap_ptr_bltu        same
     ARM_event  0x84d30   beqz s4                             NONNULL    trap_nonnull         same
     ARM_event  0x84d64   bltu a0,s8  (a0 = ~buf, s8 = len)   PTR_NOT    trap_ptr_wrap_not    malloc's post
     ARM_gone   0x849ac   bgeu s7,a2                          PTR_INC    trap_ptr_inc         same
     ARM_gone   0x84bd0   bltu a0,a1  (a1 = g_src, a0 = +off) PTR_BLTU   trap_ptr_bltu        table block below ceiling
     ARM_gone   0x84be0   beqz a2     (snez/seqz xor)         NULL_XOR   trap_null_xor        0 < g_src
     ARM_gone   0x84be4   beqz a1                             NONNULL    trap_nonnull         0 < g_src
     ARM_gone   0x84bec   bnez a1     (andi a0,7)             ALIGN8     trap_align8          table 16-aligned
     ARM_eintr  0x849d4   beqz s5                             NONNULL    trap_nonnull         same
     ARM_eintr  0x849dc   bnez a0                             ALIGN8     trap_align8          same
     ARM_sendmax 0x84a08  bgeu s7,a0                          PTR_INC    trap_ptr_inc         same
     ARM_default 0x84a38  bgeu s7,s5                          PTR_INC    trap_ptr_inc         same
     SEG_EXIT   0x84eac   bltu a0,a1  (g_src + 56 k)          PTR_BLTU   trap_ptr_bltu        same
     SEG_EXIT   0x84eb8   beqz a7     (snez/seqz xor)         NULL_XOR   trap_null_xor        0 < g_src
     SEG_EXIT   0x84ebc   beqz a3     (seqz(align) and snez)  BASE_OK    trap_base_ok         0 < g_src, 8 | g_src
   The walk is cut at five points; each segment between them is a Section hypothesis (SEG_ / ARM_) here, and the
   walks that close them replace the hypotheses one by one.  SEG_JT is proved. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00.
(* YE01 and YE2k are lib/B's: the program contract lib/B/YCfn.v states ameta_inv / arodata_okS /
   asink_none over them, so the cf twin below says the same words. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE01 YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract.
(* RelocB's sink-instance guard: after it no sink class is a hint, so every sink argument is passed with @ *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
(* Required, not Imported: rdword_of_val_mem, cited by its qualified name in the harness-block lemmas *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_frame.
(* Required, not Imported: the count names (xcnt_ok, SEC0 / CLS0, cnt_sec / cnt_cls: lib/B/ReplyCnt.v, the B kit's twin
   of lib/A/ReplyCnt.v, THE ONE DEFINITION), cited by their qualified names *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyCnt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* the program interface's constants, from the generated lib/B/YCfn.v (A_LLVMF 0x84408, RA_LLVMF 0x82240,
   A_EMPTY 0x5d8ca0, LLVMF_STK 32768); named, not copied *)
Local Notation A_LLVMF := YCfn.A_LLVMF.
Local Notation RA_LLVMF := YCfn.RA_LLVMF.
Local Notation A_EMPTY := YCfn.A_EMPTY.
Local Notation LLVMF_STK := YCfn.LLVMF_STK.

(* ------------------------------------------------------------------ the jump table *)
(* fuzz_reply.asan-ubsan 0x8475c-0x8477c: `bltu a1(op), 8 -> default; slli a1,a1,2; auipc/addi a0, 0x20e54;
   add a1,a1,a0; lw a1,0(a1); add a0,a1,a0; jr a0` - instruction for instruction image A's.  The table
   (B object A_OBJ 24 = 0x20e54, .rodata) holds nine 32-bit offsets relative to the table; fr_jt_off are those
   words, read from the pinned ELF's PT_LOAD image; fr_jt the arm's offset from fr_B0. *)
Definition fr_jtab : Z := 0x20e54.
Definition fr_jt_off (i : Z) : Z :=
  match i with
  | 0 => 407852 | 1 => 407760 | 2 => 408136 | 3 => 408292 | 4 => 408016
  | 5 => 408396 | 6 => 408448 | 7 => 408344 | 8 => 408492
  | _ => 0
  end.
Definition fr_jt (i : Z) : Z := fr_jtab + fr_jt_off i - fr_B0.
(* the arms, as offsets from fr_B0 (0x82344), and their C cases (fuzz_reply.c:699-739) *)
Definition AF_arm_add : Z := 0x243c.      (* 0x84780 case 0: op_add() *)
Definition AF_arm_write : Z := 0x23e0.    (* 0x84724 case 1: list_push(&s->pending, ...) *)
Definition AF_arm_drain : Z := 0x2558.    (* 0x8489c case 2: op_drain(s), through relay_source *)
Definition AF_arm_close : Z := 0x25f4.    (* 0x84938 case 3: s->closed = 1 *)
Definition AF_arm_remove : Z := 0x24e0.   (* 0x84824 case 4: op_remove(s), through relay_reads *)
Definition AF_arm_gone : Z := 0x265c.     (* 0x849a0 case 5: op_gone(id), through relay_reads *)
Definition AF_arm_eintr : Z := 0x2690.    (* 0x849d4 case 6: s->eintr = 1 *)
Definition AF_arm_event : Z := 0x2628.    (* 0x8496c case 7: op_event(p, strnlen(p, n)) *)
Definition AF_arm_sendmax : Z := 0x26bc.  (* 0x84a00 case 8: g_send_max = u8; g_send_eintr = 1 *)
Definition AF_arm_default : Z := 0x26ec.  (* 0x84a30 default (op 9): controller gone *)
Definition fr_arm (i : Z) : Z :=
  match i with
  | 0 => AF_arm_add | 1 => AF_arm_write | 2 => AF_arm_drain | 3 => AF_arm_close | 4 => AF_arm_remove
  | 5 => AF_arm_gone | 6 => AF_arm_eintr | 7 => AF_arm_event | 8 => AF_arm_sendmax | _ => AF_arm_default
  end.
Lemma fr_jt_arm : forall i, 0 <= i <= 8 -> fr_jt i = fr_arm i.
Proof.
  intros i Hi. assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8) as Hc by lia.
  destruct Hc as [->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]; reflexivity.
Qed.
(* the cut points, as offsets from fr_B0 *)
Definition AF_LLVM_head : Z := AF_fr_LLVMFuzzerTestOneInput + 0x1d8.     (* 0x845e0 *)
Definition AF_LLVM_dispatch : Z := AF_fr_LLVMFuzzerTestOneInput + 0x354. (* 0x8475c *)
Definition AF_LLVM_latch : Z := AF_fr_LLVMFuzzerTestOneInput + 0x3fc.    (* 0x84804 *)
Definition AF_LLVM_exit : Z := AF_fr_LLVMFuzzerTestOneInput + 0xa5c.     (* 0x84e64 *)
Definition OPS_MAX : Z := 512.

(* ------------------------------------------------------------------ the contract, cf form *)
Definition fr_RG : rep_globals := fr_globals_b.
(* two relay globals that are not rep_globals fields (W5's rf_spec takes them as GTU / GL): g_thread_up (the harness
   never starts the relay thread, so it stays 0) and g_listen (.data, init -1) *)
Definition AG_THREAD_UP : Z := 0x5d8ce0.
Definition AG_LISTEN : Z := 0xa2540.
Section cf.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head} {LS : lib_shape}.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
(* The three clauses lib/B/YCfn_cf.v changes (a Theorem Labs lane, 2026-10-28): the live-state bounds at entry, the
   live-state bounds of the post (in place of `k <= EV_LIB`), and the blocks that survive the call (in place of
   `Permutation (ablocks B ly' S') (ablocks B ly S)`: g_src's table and g_out's buffer may be live after it, and a
   realloc may move g_out's). *)
Variable fr_live_pre : astate -> Prop.
Variable fr_live_post : astate -> astate -> Z -> Prop.
Variable fr_surv : alayout -> astate -> alayout -> astate -> Prop.
(* The fourth changed clause (a Theorem Labs lane's ruling, 2026-10-28): the post's journal is W2's ajournal_gx over G_fr,
   fuzz_reply's 20 program globals, which the entry writes; the donor's bare ajournal forbids those writes. *)
Variable G_fr : list (Z * Z).
(* The fifth: the journal's footprint from the entry.  g_src's 896-byte table and g_out's buffer survive a call, so
   at the next input's entry they are live blocks the call writes, which the donor's FP [sink_token] forbids;
   fr_FP is those blocks' ranges as the entry state holds them.
   NO SINK TOKEN (a Theorem Labs lane's ruling G5, 2026-10-29 08:39Z): the program never opens the sink path, so fr_FP need
   not name it. *)
Variable fr_FP : bvmap 5 word -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> list (Z * Z).
Local Notation segs := tfibsegs.
Local Notation rd W mem := (mrestrict (w_H W) mem).
(* The sixth: the program's globals between calls: every source closed, the relay empty (no table yet, or the
   surviving one with no entry), the controller's stream and flags some state, g_gone some flag, the lock free, no
   wake pipe.  The globals' bytes WRITABLE, not PRESENT (a Theorem Labs lane's ruling G4): no segment reads presence of a
   G_fr byte, and presence could not be carried to the exit anyway (G_fr holds errno, which apres_kept excludes). *)
Definition fr_gi (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) : Prop :=
  (forall a, inG G_fr a -> writable_at segs (rd W mem) a) /\
  (forall i, (i < 4)%nat -> asrc_closed W mem (rg_s fr_RG + ASRC * Z.of_nat i)) /\
  (exists T, ra_rel B fr_RG ly S W mem T []) /\
  (exists c O mx cap out, aout_at B fr_RG ly S W mem c O mx (Z.of_nat (length O)) cap out) /\
  (exists gn, agone_at fr_RG W mem gn) /\ alock_at fr_RG W mem false /\ awake_at fr_RG W mem /\
  val_mem segs (rd W mem) AG_THREAD_UP 1 0 /\
  (exists lst, val_mem segs (rd W mem) AG_LISTEN 4 lst) /\
  (forall i, 0 <= i < 4 -> writable_at segs (rd W mem) (AG_LISTEN + i)).
(* The eighth (a Theorem Labs lane's approved text, 2026-10-29, landed on lib/A at a working branch 60c0b278422):
   THE HARNESS BLOCKS.  SEG_PRO's entry split of the live blocks into the input block, g_src's table, g_out's buffer
   and the rest needs them live and pairwise distinct.  fr_hblks names the blocks the globals point to - g_src's
   table (G, ATABLE) when g_src reads G <> 0, g_out's buffer (o, c) when g_capout reads c <> 0 - read through the view
   at rg_src / rg_out / rg_capout of B's fr_RG (fr_globals_b).  THE ONE DEFINITION on image B: lib/A's
   W_LLVMFuzzerTestOneInput_cut.v fr_hblks at B's names, the same text as the B driver's fr_hblks_b
   (lib/B/YCfn_cf.v:55-59 at 430b6b00098), which takes it from here. *)
Definition fr_hblks (W : world segs) (mem : word -> option byte) : list (Z * Z) :=
  let v := aview segs (w_H W) mem in
  (match rdword v (rg_src fr_RG) with Some G => if G =? 0 then [] else [(G, ATABLE)] | None => [] end) ++
  (match rdword v (rg_out fr_RG), rdword v (rg_capout fr_RG) with
   | Some o, Some c => if c =? 0 then [] else [(o, c)] | _, _ => [] end).
(* ---- THE CROSS-CALL LIVE COUNTS (the room round; the stable form, 2026-10-30):
   ReplyCnt.xcnt_ok S ly inp T0 cap out bounds the entry's live blocks OTHER than the input block inp, the relay table
   (T0, 896) when there is one, and g_out (cap, out): SEC0 secondary requests, CLS0 of each primary class (64 each).
   The blocks a call leaves live are exactly these plus the entry's rest, so the post re-establishes the bound at every
   call, the first included (fr_LS3c_exit_cnt, lib/A/ReplyLS3w.v on image A). *)
(* ---- THE g_capout BOUND (a measured invariant): g_out grows only in send_line, to 2 * (g_nout + len) <= 133,953,536,
   and its capacity is otherwise unchanged, so at a return it is at most max (entry, 133,953,536) <= CAPOUT_MAX; at the
   first call g_capout is a .bss word, 0.  CAPOUT_MAX is lib/B/YCfn_cf.v's OUT_MAX, restated here because the cut does
   not import the driver (the driver proves the two equal by reflexivity).  The pre and the post state it LAST, read as
   aout_at reads g_capout (lib/B/W_rep.v aout_at, val_mem 8 bytes). *)
Definition CAPOUT_MAX : Z := 4 * (OPS_MAX - 1) * 65535.
Definition fr_lib_pre_cf (regs : bvmap 5 word) (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (md : Model)
(p n : Z) (pl : list byte) (M : Z) : Prop :=
afn_pre segs B LLVMF_STK ly S W regs mem md [] /\
raZ regs = RA_LLVMF /\
getr regs 10 = w64 p /\ getr regs 11 = w64 n /\
((n = 0 /\ p = A_EMPTY) \/ (0 < n < 2 ^ 26 /\ In (p, n) (ablocks B ly S))) /\
n = Z.of_nat (length pl) /\ garr8 segs (rd W mem) p (map (fun b : byte => bv_unsigned b) pl) /\
frames S = [] /\ fr_live_pre S /\ fr_gi ly S W mem /\
(* the seventh: the read-only statics read as the image (rom_view), which every runtime contract takes *)
rom_view segs W mem /\
arodata_okS segs B RLO RHI (aview segs (w_H W) mem) /\
asink_none segs tfib_K (rd W mem) md /\
fd_lookup (m_fds md) (alloc_fd (m_fds md)) = None /\
Fs.fs_sorted (m_fs md) = true /\
ameta_inv segs tfib_K ly (rd W mem) M /\
mo_ok MT S (XM_LIB n) /\
(* STKR: the caller's stack is readable from the entry's sp up to ly_top (a Theorem Labs lane's ruling 16:46Z; a Theorem Labs lane's
   B check_no_loss clause, the only form true at every allowed state, since its unwinder follows saved s0 cells
   above sp0 and image B's stage2 0x8cb08 / main 0x81eac put argv, at >= usp + 8, in a saved-s0 slot).  Stated ONCE
   here, LAST so every positional destruct of the pre still binds; the driver supplies it at each call: [sp0, usp)
   by RelocA-2's AStkPres.v, [usp, ly_top) by the entry-image start-up fact.  The arms that call check_no_loss
   (ARM_drain, ARM_remove, ARM_gone, SEG_EXIT) take it from here (kept across callees by the journal's view
   clause above the callee's window) instead of carrying it as a hypothesis. *)
(forall a, spZ regs <= a < ly_top ly -> aview segs (w_H W) mem a <> None) /\
(* HB: the input block and the harness blocks are live and pairwise distinct (the eighth clause above).  Stated LAST,
   after STKR, so every positional destruct of the pre above it still binds. *)
(List.NoDup ((if n =? 0 then [] else [(p, n)]) ++ fr_hblks W mem) /\ incl (fr_hblks W mem) (ablocks B ly S)) /\
(* XCNT: the entry's live blocks other than the input, the table and g_out are few (ReplyCnt.xcnt_ok; T0 is the relay
   table as fr_gi's ra_rel names it, arelay_at's when not 0; (cap, out) g_out as its aout_at).  Stated LAST, after HB. *)
(exists T0 c O mx cap out, ra_rel B fr_RG ly S W mem T0 [] /\ aout_at B fr_RG ly S W mem c O mx (Z.of_nat (length O)) cap out /\
  ReplyCnt.xcnt_ok B S ly (if n =? 0 then [] else [(p, n)]) T0 cap out) /\
(* CAPOUT: g_capout at most CAPOUT_MAX (above).  Stated LAST, after XCNT. *)
(exists c, val_mem segs (arm W mem) (rg_capout fr_RG) 8 c /\ 0 <= c <= CAPOUT_MAX).
Definition fr_lib_post_cf (regs : bvmap 5 word) (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (md : Model)
(p n : Z) (M : Z) (l : lleaf)
(ly' : alayout) (S' : astate) (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) (k : Z) : Prop :=
ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ regs) (fr_FP regs ly S W mem) ly S W mem md [] ly' S' W' mem' md' k /\ fr_live_post S S' k /\
aregs_preserved regs regs' /\ getr regs' 10 = w64 0 /\
fr_surv ly S ly' S' /\ fr_gi ly' S' W' mem' /\ rom_view segs W' mem' /\
(forall fd, fd_lookup (m_fds md') fd = fd_lookup (m_fds md) fd) /\
m_fs md' = ll_fs l /\ ll_ret l = 0 /\ ll_out l = [] /\ Fs.fs_sorted (ll_fs l) = true /\
asink_none segs tfib_K (rd W' mem') md' /\
ameta_inv segs tfib_K ly' (rd W' mem') M /\
mo_le MT S S' (XN_LIB n) /\
(forall i, 0 <= i < n -> aview segs (w_H W') mem' (p + i) = aview segs (w_H W) mem (p + i)) /\
(* HB at the return: the harness blocks the globals name are live and pairwise distinct *)
(List.NoDup (fr_hblks W' mem') /\ incl (fr_hblks W' mem') (ablocks B ly' S')) /\
(* XCNT at the return: the next call's entry bound (ReplyCnt.xcnt_ok) *)
(exists T0 c O mx cap out, ra_rel B fr_RG ly' S' W' mem' T0 [] /\
  aout_at B fr_RG ly' S' W' mem' c O mx (Z.of_nat (length O)) cap out /\
  ReplyCnt.xcnt_ok B S' ly' (if n =? 0 then [] else [(p, n)]) T0 cap out) /\
(* CAPOUT at the return (above) *)
(exists c, val_mem segs (arm W' mem') (rg_capout fr_RG) 8 c /\ 0 <= c <= CAPOUT_MAX).
Definition fr_lib_contract_cf : Prop :=
forall ly S (W : world segs) (regs : bvmap 5 word) mem md p n pl M (K : lleaf -> TSet),
AI segs (w_H W) (w_A W) md ->
fr_lib_pre_cf regs ly S W mem md p n pl M ->
(forall (l : lleaf) (W' : world segs) (c' : config),
wle W W' -> AI segs (w_H W') (w_A W') (cfg_model c') ->
(exists ly' S' regs' mem' md' k,
c' = cfg_at segs RA_LLVMF regs' mem' md' /\
fr_lib_post_cf regs ly S W mem md p n M l ly' S' W' regs' mem' md' k) ->
srealizes segs c' (K l)) ->
srealizes segs (cfg_at segs A_LLVMF regs mem md) (LIBK pl (m_fs md) K).
(* ---- WITNESS (a): the pre's HB clause holds whenever g_src and g_capout read 0 (fr_hblks = []), as at the first
   call.  fr_hb_pre_of_image reduces it to image B: both globals are .bss (0x5d8d40, 0x5d90a0), whose bytes the image
   reads 0 (fr_hb_rom, computed on B's pinned segments), and a state whose view of those 16 bytes is the image's
   (B's start state, the B driver's to give) satisfies the clause for any input. *)
Lemma fr_hblks_nil : forall (W : world segs) mem,
  rdword (aview segs (w_H W) mem) (rg_src fr_RG) = Some 0 ->
  rdword (aview segs (w_H W) mem) (rg_capout fr_RG) = Some 0 -> fr_hblks W mem = [].
Proof.
  intros W mem H1 H2. unfold fr_hblks. cbv zeta. rewrite H1, H2. cbv beta iota.
  destruct (rdword (aview segs (w_H W) mem) (rg_out fr_RG)); reflexivity.
Qed.
Lemma fr_hb_pre_start : forall ly S (W : world segs) mem (p n : Z),
  rdword (aview segs (w_H W) mem) (rg_src fr_RG) = Some 0 ->
  rdword (aview segs (w_H W) mem) (rg_capout fr_RG) = Some 0 ->
  List.NoDup ((if n =? 0 then [] else [(p, n)]) ++ fr_hblks W mem) /\ incl (fr_hblks W mem) (ablocks B ly S).
Proof.
  intros ly S W mem p n H1 H2. rewrite (fr_hblks_nil W mem H1 H2), app_nil_r. split.
  - destruct (n =? 0); [constructor | constructor; [intros [] | constructor]].
  - intros b [].
Qed.
(* a .bss byte of image B: seg_rom reads it 0 *)
Definition fr_rom0 (a : Z) : bool :=
  match seg_rom segs (Z_to_bv 64 a) with Some b => bv_unsigned b =? 0 | None => false end.
Lemma fr_hb_rom : forall i, 0 <= i < 8 -> fr_rom0 (rg_src fr_RG + i) = true /\ fr_rom0 (rg_capout fr_RG + i) = true.
Proof.
  intros i Hi. assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) as Hc by lia.
  destruct Hc as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; split; vm_compute; reflexivity.
Qed.
Lemma fr_hb_rdword0 : forall (W : world segs) mem a,
  (forall i, 0 <= i < 8 -> aview segs (w_H W) mem (a + i) = Some 0) -> rdword (aview segs (w_H W) mem) a = Some 0.
Proof.
  intros W mem a Ha. pose proof (Ha 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0. unfold rdword.
  rewrite H0, (Ha 1 ltac:(lia)), (Ha 2 ltac:(lia)), (Ha 3 ltac:(lia)), (Ha 4 ltac:(lia)), (Ha 5 ltac:(lia)),
    (Ha 6 ltac:(lia)), (Ha 7 ltac:(lia)).
  reflexivity.
Qed.
Lemma fr_hb_pre_of_image : forall ly S (W : world segs) mem (p n : Z),
  (forall i, 0 <= i < 8 -> aview segs (w_H W) mem (rg_src fr_RG + i) =
     option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 (rg_src fr_RG + i)))) ->
  (forall i, 0 <= i < 8 -> aview segs (w_H W) mem (rg_capout fr_RG + i) =
     option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 (rg_capout fr_RG + i)))) ->
  List.NoDup ((if n =? 0 then [] else [(p, n)]) ++ fr_hblks W mem) /\ incl (fr_hblks W mem) (ablocks B ly S).
Proof.
  intros ly S W mem p n Hs Hc.
  assert (Z0 : forall a, fr_rom0 a = true ->
    option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a)) = Some 0).
  { intros a Ha. unfold fr_rom0 in Ha. destruct (seg_rom segs (Z_to_bv 64 a)) as [b|]; [|discriminate].
    apply Z.eqb_eq in Ha. cbn [option_map]. rewrite Ha. reflexivity. }
  apply fr_hb_pre_start; apply fr_hb_rdword0; intros i Hi;
    [rewrite (Hs i Hi) | rewrite (Hc i Hi)]; apply Z0; [exact (proj1 (fr_hb_rom i Hi)) | exact (proj2 (fr_hb_rom i Hi))].
Qed.
End cf.

(* the donor's srz_enter (lib/A/ACfh.v:47) *)
Lemma fr_srz_enter : forall (segs : list Segment) (W : world segs) (c : config) (T : TSet),
AI segs (w_H W) (w_A W) (cfg_model c) ->
SRr segs W c (fun W' c' => AI segs (w_H W') (w_A W') (cfg_model c') -> srealizes segs c' T) -> srealizes segs c T.
Proof. intros segs W c T HAI HS. apply (HS HAI T). intros W' c' _ HAI' HK. exact (HK HAI'). Qed.

(* ------------------------------------------------------------------ the walk's skeleton *)
Section w.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
(* the image's segments as the walk kit names them; they are tfibsegs (both are AsanUbsan.M.loaded_segments) *)
Local Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable fr_live_pre : astate -> Prop.
Variable fr_live_post : astate -> astate -> Z -> Prop.
Variable fr_surv : alayout -> astate -> alayout -> astate -> Prop.
Variable G_fr : list (Z * Z).
Variable fr_FP : bvmap 5 word -> alayout -> astate -> world segs -> (word -> option byte) -> list (Z * Z).
Hypothesis LAWS : AR_laws segs B.
Hypothesis HG : gx_ok segs B G_fr.
(* Two facts every segment that stores to a global or calls across errno takes, stated once here so all segments
   name the same text (discharged at integration: glob_wr_law at G_fr's 20 object ranges by vm_compute; errno_law
   from the instance's api_env, errno = tp - 164 = 0x5d994c in the thread block). *)
Definition glob_wr_law : Prop :=
  forall (H : word -> bool) (m : word -> option byte) a, inG G_fr a -> writable_at segs (mrestrict H m) a.
Definition errno_law : Prop :=
  forall ly S (W : world segs) mem md, AR segs B ly S W mem md ->
  (exists v, val_mem segs (arm W mem) (as_errno B) 4 v /\ 0 <= v < 2 ^ 32) /\ awr W mem (as_errno B) 4.
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).
Let RUN := paj_run_x (PL := PL_fr) (PI := PB_fr) B LAWS G_fr HG 0 [].
Let RUNTO := paj_run_to_x (PL := PL_fr) (PI := PB_fr) B LAWS G_fr HG 0 [].
Let BR := paj_branch (PI := PB_fr).

(* the call's context, the donor's rtcx (ACf5.v:45) *)
Record lfcx := LFCX {
  c_ly : alayout; c_S : astate; c_W : world segs; c_regs : bvmap 5 word; c_mem : word -> option byte; c_md : Model;
  c_p : Z; c_n : Z; c_pl : list byte; c_M : Z }.
Definition lf_base (cx : lfcx) : Prop :=
  AI segs (w_H (c_W cx)) (w_A (c_W cx)) (c_md cx) /\
  fr_lib_pre_cf B MT XM_LIB RLO RHI fr_live_pre G_fr (c_regs cx) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    (c_p cx) (c_n cx) (c_pl cx) (c_M cx).
Definition lf_entry (cx : lfcx) : config := cfg_at segs A_LLVMF (c_regs cx) (c_mem cx) (c_md cx).
(* the return to the driver with the contract's post, for checksum_shape's one leaf LL 0 fs [] *)
Definition lf_post (cx : lfcx) : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' k,
    c' = cfg_at segs RA_LLVMF regs' mem' md' /\
    fr_lib_post_cf B MT XN_LIB fr_live_post fr_surv G_fr fr_FP (c_regs cx) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx)
      (c_md cx) (c_p cx) (c_n cx) (c_M cx) (LL 0 (m_fs (c_md cx)) []) ly' S' W' regs' mem' md' k.
(* the journal's footprint from this call's entry *)
Definition lf_FP (cx : lfcx) : list (Z * Z) := fr_FP (c_regs cx) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx).

(* ---- the cut points' facts (the donor's rt_base / INV_* over a cut point, ACf5.v:52-82)
   A cut point carries: the journal from the entry (W2's ajournal_gx over G_fr, XO = 0, no out cells, the fake frame
   of class 1 owned); the frame (lf_F: s1, the saved registers, the slots the prologue stores) and the fake frame
   (header and shadow); the model lmod of the harness's sources, the relay's table and the output stream over
   lib/B/W_rep.v; the input block and its bytes; the loop's relational invariant RINV over the model; and the
   registers the next segment reads (one predicate per cut point). *)
Definition AG_NFD : Z := 0x5d8da0.                 (* g_nfd *)
Definition DIV10 : Z := 0x199999999999999a.        (* the /10 multiplier the loop keeps at F+136 *)
Definition HI_G_SRC : Z := 0x5d85dc.               (* s2: auipc at 0x845dc; g_src = s2 + 1892 *)
Definition HI_G_NOUT : Z := 0x5d95a4.              (* s10: auipc at 0x845a4; g_nout = s10 - 1892 *)
Definition HI_G_CLIENT : Z := 0xa2540.             (* F+32: auipc at 0x84540; g_client = + 32 *)
Definition HI_G_SMAX : Z := 0x5d9550.              (* F+72: auipc at 0x84550; g_send_max = - 1936 *)
Definition HI_G_GONE : Z := 0x5d955c.              (* F+64: auipc at 0x8455c; g_gone = - 1916 *)
Definition HI_G_SDEAD : Z := 0x5d9564.             (* F+40: auipc at 0x84564; g_send_dead = - 1892 *)
Definition HI_G_SEINTR : Z := 0x5d956c.            (* F+56: auipc at 0x8456c; g_send_eintr = - 1868 *)
Definition fake_shadow : list Z :=                 (* the 128-byte fake frame's shadow: prefix[48] at +32, poisoned *)
  [0xf1; 0xf1; 0xf1; 0xf1; 0xf8; 0xf8; 0xf8; 0xf8; 0xf8; 0xf8; 0xf3; 0xf3; 0xf3; 0xf3; 0xf3; 0xf3].
(* the saved registers: (offset below the entry sp, register); B's prologue is A's instruction for instruction *)
Definition saved_regs : list (Z * Z) :=
  [(8, 1); (16, 8); (24, 9); (32, 18); (40, 19); (48, 20); (56, 21); (64, 22); (72, 23); (80, 24); (88, 25);
   (96, 26); (104, 27)].
(* s1 = sp after `addi sp,sp,-320; andi sp,sp,-32` *)
Definition lf_F (cx : lfcx) : Z := (spZ (c_regs cx) - 320) - (spZ (c_regs cx) - 320) mod 32.
Definition sv8 (W : world segs) (mem : word -> option byte) (a v : Z) : Prop := val_mem segs (arm W mem) a 8 v.
(* The frame and the fake frame FF.  NO `full` FLAG (difference (3) above): B's prologue stores every slot before
   the loop's head, so the same frame holds at H, D, every arm, K and X. *)
Definition aframe_at (cx : lfcx) (FF : Z) (W : world segs) (mem : word -> option byte) : Prop :=
  let sp0 := spZ (c_regs cx) in let F := lf_F cx in
  (forall o r, In (o, r) saved_regs -> sv8 W mem (sp0 - o) (bv_unsigned (getr (c_regs cx) (Z_to_bv 5 r)))) /\
  awr W mem F (sp0 - F) /\
  sv8 W mem (F + 32) HI_G_CLIENT /\ sv8 W mem (F + 40) HI_G_SDEAD /\ sv8 W mem (F + 48) (rg_s fr_RG) /\
  sv8 W mem (F + 56) HI_G_SEINTR /\ sv8 W mem (F + 64) HI_G_GONE /\ sv8 W mem (F + 72) HI_G_SMAX /\
  sv8 W mem (F + 80) FF /\ sv8 W mem (F + 96) (SB + FF / 8) /\ sv8 W mem (F + 104) FF /\
  sv8 W mem (F + 120) (SB + rg_s fr_RG / 8) /\ sv8 W mem (F + 128) (rg_s fr_RG + 4) /\
  sv8 W mem (F + 136) DIV10 /\ sv8 W mem (F + 152) (SB + (rg_s fr_RG + 4) / 8) /\ sv8 W mem (F + 184) FF /\
  sv8 W mem FF 0x41b58ab3 /\ sv8 W mem (FF + 8) 0x1239d /\ sv8 W mem (FF + 16) A_LLVMF /\ awr W mem FF 128 /\
  garr8 segs (arm W mem) (SB + FF / 8) fake_shadow /\ awr W mem (SB + FF / 8) 16.
(* the model *)
Record lmod := LM {
  lm_k : Z;                         (* input consumed: in.p = p + k, in.n = n - k *)
  lm_hs : list (option hsrc);       (* g_s[0..3]: Some h open, None closed (96 zero bytes) *)
  lm_G : Z; lm_es : list rentry;    (* g_src and the relay's table *)
  lm_c : ctl; lm_O : list byte;     (* the output flags; what the controller read in this operation *)
  lm_mx : Z; lm_cap : Z; lm_out : Z;(* g_send_max, g_capout, g_out *)
  lm_gn : Z; lm_nfd : Z }.          (* g_gone, g_nfd *)
Definition aslot (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (i : nat) (o : option hsrc)
  : Prop :=
  match o with
  | Some h => asrc_at B ly S W mem (rg_s fr_RG + ASRC * Z.of_nat i) h
  | None => asrc_closed W mem (rg_s fr_RG + ASRC * Z.of_nat i)
  end.
Definition amodel_at (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (m : lmod) : Prop :=
  length (lm_hs m) = 4%nat /\ (forall i, (i < 4)%nat -> aslot ly S W mem i (nth i (lm_hs m) None)) /\
  arelay_at B fr_RG ly S W mem (lm_G m) (lm_es m) /\
  aout_at B fr_RG ly S W mem (lm_c m) (lm_O m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (lm_out m) /\
  agone_at fr_RG W mem (lm_gn m) /\ alock_at fr_RG W mem false /\ awake_at fr_RG W mem /\
  val_mem segs (arm W mem) AG_NFD 4 (lm_nfd m) /\ awr W mem AG_NFD 4 /\ 0 <= lm_nfd m <= OPS_MAX /\
  val_mem segs (arm W mem) AG_THREAD_UP 1 0 /\
  (exists lst, val_mem segs (arm W mem) AG_LISTEN 4 lst) /\ awr W mem AG_LISTEN 4.
(* the input block, as the contract hands it over, and its bytes *)
Definition ainput_at (cx : lfcx) (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) : Prop :=
  ((c_n cx = 0 /\ c_p cx = A_EMPTY) \/ (0 < c_n cx < 2 ^ 26 /\ In (c_p cx, c_n cx) (ablocks B ly S))) /\
  garr8 segs (arm W mem) (c_p cx) (map (fun b : byte => bv_unsigned b) (c_pl cx)).
(* The heap blocks the model names (W_rep's *_blks): the relay's table and entries, the open sources' blocks, the
   controller's buffer; and the input block. *)
Definition slot_blks (o : option hsrc) : list (Z * Z) := match o with Some h => asrc_blks h | None => [] end.
Definition model_blks (m : lmod) : list (Z * Z) :=
  (lm_G m, ATABLE) :: concat (map aentry_blks (lm_es m)) ++ concat (map slot_blks (lm_hs m)) ++
  aout_blks (lm_cap m) (lm_out m).
Definition input_blks (cx : lfcx) : list (Z * Z) := if c_n cx =? 0 then [] else [(c_p cx, c_n cx)].
(* the live blocks are the input block, the model's blocks, and the rest (the driver's), each once; a model block is
   either allocated during this call or inside the entry's footprint (the surviving table and buffer).
   The second clause is over the block's REQUEST size, not its plain size (a Theorem Labs lane's ruling of 2026-10-29 12:2xZ,
   landed on lib/A after this file's donor sha): a blk_FP callee needs the whole req_size footprint in lf_FP or in a
   tmp block, and it is free at the entry because fr_FP is ablocks_fp-shaped. *)
Definition ablocks_sep (cx : lfcx) (m : lmod) (ly : alayout) (S : astate) : Prop :=
  (exists rest, Permutation (ablocks B ly S) (input_blks cx ++ model_blks m ++ rest)) /\
  (forall b, In b (model_blks m) ->
     ~ In b (ablocks B (c_ly cx) (c_S cx)) \/
     (forall a, fst b <= a < fst b + req_size (snd b) -> inFP (lf_FP cx) a)).
(* ---- WITNESS (b): the post's HB clause from a cut point's facts.  The globals g_src / g_out / g_capout hold the
   model's table and buffer (amodel_at: arelay_at's g_src = lm_G m, aout_at's g_out / g_capout = lm_out m / lm_cap m),
   so fr_hblks is (lm_G m, ATABLE) :: aout_blks (lm_cap m) (lm_out m), both blocks of model_blks m; ablocks_sep's
   Permutation with the live blocks, which have no duplicate (the AR / ARx laws' pairwise disjointness), makes them
   distinct and live.  fr_hb_of_model is the law-free core (the cut_x twin cites it); fr_hb_post_AR takes the two
   block facts from AR's laws; fr_hblks_kept carries fr_hblks across a step that keeps the three globals' bytes.
   B's SEG_EXIT cites them at the exit's last state (lib/A's _exit.v lx_end_of_ffexit is the pattern). *)
Lemma fr_hb_of_model : forall cx m ly S (W : world segs) mem rest,
  (forall p n, In (p, n) (ablocks B ly S) -> 0 < p /\ p + req_size n <= alloc_ceiling) ->
  List.NoDup (ablocks B ly S) ->
  amodel_at ly S W mem m ->
  Permutation (ablocks B ly S) (input_blks cx ++ model_blks m ++ rest) ->
  fr_hblks W mem = (lm_G m, ATABLE) :: aout_blks (lm_cap m) (lm_out m) /\
  List.NoDup (fr_hblks W mem) /\ incl (fr_hblks W mem) (ablocks B ly S).
Proof.
  intros cx m ly S W mem rest HBK HND HM HP.
  pose proof asan_consts as (C1 & _).
  pose proof HM as (_ & _ & HRL & HOUT & _).
  pose proof HRL as (VG & _ & _ & _ & _ & _ & _ & HinG & _).
  pose proof HOUT as (_ & _ & _ & _ & VC & _ & VO & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & HCAP).
  destruct (HBK _ _ HinG) as (HG0 & HGc). change (req_size ATABLE) with 896 in HGc.
  assert (RG : rdword (aview tfibsegs (@w_H tfibsegs W) mem) (rg_src fr_RG) = Some (lm_G m))
    by (apply W_frame.rdword_of_val_mem; [exact VG | lia]).
  assert (HMD : List.NoDup (model_blks m)).
  { pose proof (Permutation_NoDup HP HND) as H.
    apply List.NoDup_app_remove_l in H. apply List.NoDup_app_remove_r in H. exact H. }
  unfold model_blks in HMD. apply NoDup_cons_iff in HMD as (HnG & HMD).
  apply List.NoDup_app_remove_l in HMD. apply List.NoDup_app_remove_l in HMD.
  assert (E : fr_hblks W mem = (lm_G m, ATABLE) :: aout_blks (lm_cap m) (lm_out m)).
  { destruct HCAP as [(Hc0 & Ho0 & _) | (Hcp & _ & HinO & _)].
    - rewrite Hc0 in VC.
      assert (RC : rdword (aview tfibsegs (@w_H tfibsegs W) mem) (rg_capout fr_RG) = Some 0)
        by (apply W_frame.rdword_of_val_mem; [exact VC | lia]).
      unfold fr_hblks, aout_blks. cbv zeta. rewrite RG, RC. cbv beta iota.
      rewrite (proj2 (Z.eqb_neq (lm_G m) 0)) by lia. rewrite Hc0.
      destruct (rdword (aview tfibsegs (@w_H tfibsegs W) mem) (rg_out fr_RG)); reflexivity.
    - destruct (HBK _ _ HinO) as (HO0 & HOc).
      unfold req_size in HOc. rewrite (proj2 (Z.eqb_neq (lm_cap m) 0)) in HOc by lia.
      assert (RC : rdword (aview tfibsegs (@w_H tfibsegs W) mem) (rg_capout fr_RG) = Some (lm_cap m))
        by (apply W_frame.rdword_of_val_mem; [exact VC | lia]).
      assert (RO : rdword (aview tfibsegs (@w_H tfibsegs W) mem) (rg_out fr_RG) = Some (lm_out m))
        by (apply W_frame.rdword_of_val_mem; [exact VO | lia]).
      unfold fr_hblks, aout_blks. cbv zeta. rewrite RG, RC, RO. cbv beta iota.
      rewrite (proj2 (Z.eqb_neq (lm_G m) 0)) by lia. rewrite (proj2 (Z.eqb_neq (lm_cap m) 0)) by lia.
      reflexivity. }
  split; [exact E|]. rewrite E. split.
  - constructor; [|exact HMD]. intros Hin. apply HnG. apply in_or_app. right. apply in_or_app. right. exact Hin.
  - intros b [<- | Hb]; [exact HinG|].
    apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. apply in_or_app. left.
    unfold model_blks. right. apply in_or_app. right. apply in_or_app. right. exact Hb.
Qed.
(* the live blocks have no duplicate: a block is disjoint from every other one, and from itself only if empty *)
Lemma fr_ablocks_nodup : forall ly S (W : world segs) mem md, AR segs B ly S W mem md -> List.NoDup (ablocks B ly S).
Proof.
  intros ly S W mem md HAR.
  assert (Hpos : Forall (fun b => 1 <= req_size (snd b)) (ablocks B ly S)).
  { apply Forall_forall. intros [p n] Hin.
    destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn).
    cbn [snd]. pose proof (req_size_pos n ltac:(lia)) as [Hq _]. exact Hq. }
  destruct (al_sep _ _ LAWS ly S W mem md HAR) as [Hp _]. apply pairwise_app_l in Hp as [Hp _].
  clear - Hpos Hp. revert Hpos Hp. induction (ablocks B ly S) as [|b l IH]; intros Hpos Hp; [constructor|].
  inversion Hpos as [|b0 l0 Hb Hl]; subst.
  cbn [map pairwise] in Hp. destruct Hp as [Hf Hp]. constructor; [|exact (IH Hl Hp)].
  intros Hin. rewrite Forall_forall in Hf. specialize (Hf (fst b, req_size (snd b)) (in_map _ _ _ Hin)).
  unfold zdisjoint in Hf. cbn [fst snd] in Hf. lia.
Qed.
Lemma fr_hb_post_AR : forall cx m ly S (W : world segs) mem md rest,
  AR segs B ly S W mem md -> amodel_at ly S W mem m ->
  Permutation (ablocks B ly S) (input_blks cx ++ model_blks m ++ rest) ->
  List.NoDup (fr_hblks W mem) /\ incl (fr_hblks W mem) (ablocks B ly S).
Proof.
  intros cx m ly S W mem md rest HAR HM HP.
  assert (HBK : forall p n, In (p, n) (ablocks B ly S) -> 0 < p /\ p + req_size n <= alloc_ceiling)
    by (intros p n Hin; destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & H1 & H2 & _); lia).
  destruct (fr_hb_of_model cx m ly S W mem rest HBK (fr_ablocks_nodup ly S W mem md HAR) HM HP) as (_ & H1 & H2).
  split; assumption.
Qed.
(* fr_hblks reads only g_src's, g_out's and g_capout's 8 bytes *)
Lemma fr_hblks_kept : forall (W W' : world segs) mem mem',
  (forall a, rg_src fr_RG <= a < rg_src fr_RG + 8 \/ rg_out fr_RG <= a < rg_out fr_RG + 8 \/
     rg_capout fr_RG <= a < rg_capout fr_RG + 8 -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a) ->
  fr_hblks W' mem' = fr_hblks W mem.
Proof.
  intros W W' mem mem' HK. unfold fr_hblks. cbv zeta.
  rewrite (YCbq.rdword_ext (aview tfibsegs (@w_H tfibsegs W) mem) (aview tfibsegs (@w_H tfibsegs W') mem')
    (rg_src fr_RG)) by (intros k Hk; apply HK; left; lia).
  rewrite (YCbq.rdword_ext (aview tfibsegs (@w_H tfibsegs W) mem) (aview tfibsegs (@w_H tfibsegs W') mem')
    (rg_out fr_RG)) by (intros k Hk; apply HK; right; left; lia).
  rewrite (YCbq.rdword_ext (aview tfibsegs (@w_H tfibsegs W) mem) (aview tfibsegs (@w_H tfibsegs W') mem')
    (rg_capout fr_RG)) by (intros k Hk; apply HK; right; right; lia).
  reflexivity.
Qed.
(* The allocator state's invariant beyond the journal: the meter (mo_ok / mo_le against the contract's XM_LIB /
   XN_LIB) and the live-bytes room (blocks_bytes) the callees and allocator sites take.  A Section variable: its
   definition is the instance's budget, and each segment names the facts it reads from it and the step it owes. *)
Variable LS : lfcx -> Z -> lmod -> alayout -> astate -> Prop.
(* The loop's relational invariant over the model (the plain proof's pair_ok / relay_at relations and its RI,
   Prog/SlotInv.v:253-314): a Section variable here; the arms consume it through their callees' functional halves. *)
Variable RINV : lfcx -> Z -> lmod -> Prop.
Definition lcut (cx : lfcx) (t : Z)
    (R : lmod -> Z -> bvmap 5 word -> world segs -> (word -> option byte) -> Prop)
    (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (W : world segs) : Prop :=
  exists own ly3 S3 k m fpos,
    ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP cx)
      (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) own ly3 S3 W mem md k /\
    own = [(1, fpos)] /\
    aframe_at cx (frame_addr ly3 1 fpos) W mem /\
    (* the fake frame's last word holds its flag pointer (written by __asan_stack_malloc_1: YCbq.v aj_stack_malloc's
       rdword at frame_addr + fs_frame_bytes 1 - 8; a Theorem Labs lane's ruling of 09:5xZ): the shutdown's `ld a0,120(s4);
       sb zero,0(a0)` (0x8506c) stores through it.  Here, not in aframe_at, because it names ly3 and fpos. *)
    sv8 W mem (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos) /\
    amodel_at ly3 S3 W mem m /\ ainput_at cx ly3 S3 W mem /\ rom_view segs W mem /\
    ablocks_sep cx m ly3 S3 /\ LS cx t m ly3 S3 /\
    RINV cx t m /\ R m (frame_addr ly3 1 fpos) regs W mem.
(* The registers every cut point inside the loop keeps.  B's allocation (difference (4)): s11 = SB, s10 = HI_G_NOUT,
   s2 = HI_G_SRC, s3 = FF + 32, s7 = 1; no modulus register and no g_nsrc high half. *)
Definition lregs_common (cx : lfcx) (FF : Z) (regs : bvmap 5 word) : Prop :=
  getr regs 2 = w64 (lf_F cx) /\ getr regs 8 = getr (c_regs cx) 2 /\ getr regs 9 = w64 (lf_F cx) /\
  getr regs 18 = w64 HI_G_SRC /\ getr regs 19 = w64 (FF + 32) /\ getr regs 23 = w64 1 /\
  getr regs 24 = w64 (SB + FF / 8) /\ getr regs 26 = w64 HI_G_NOUT /\ getr regs 27 = w64 SB /\
  getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B).
(* the input byte i, as the program reads it *)
Definition in_byte (cx : lfcx) (i : Z) : Z := bv_unsigned (nth (Z.to_nat i) (c_pl cx) (Z_to_bv 8 0)).
Definition picks (op : Z) : bool := (op =? 1) || (op =? 2) || (op =? 3) || (op =? 4) || (op =? 6).
(* pick(): the k-th open source (fuzz_reply.c:550-561) *)
Fixpoint pick_from (hs : list (option hsrc)) (i : nat) (k : Z) : option nat :=
  match hs with
  | [] => None
  | Some _ :: hs' => if k =? 0 then Some i else pick_from hs' (S i) (k - 1)
  | None :: hs' => pick_from hs' (S i) k
  end.
Definition nopen (hs : list (option hsrc)) : Z :=
  Z.of_nat (length (List.filter (fun o => match o with Some _ => true | None => false end) hs)).
Definition pick (hs : list (option hsrc)) (kb : Z) : option nat :=
  if nopen hs =? 0 then None else pick_from hs 0 (kb mod nopen hs).
(* H 0x845e0: t operations done; s5 = in.n left, s6 = in.p, s9 = t.  Unlike A, the head is the back edge's target
   AND the `in.n != 0` test (difference (2)), so in.n left may be 0 and SEG_HEAD takes that branch to the exit. *)
Definition lregs_H (cx : lfcx) (t : Z) (m : lmod) (FF : Z) (regs : bvmap 5 word) (W : world segs)
    (mem : word -> option byte) : Prop :=
  lregs_common cx FF regs /\ getr regs 25 = w64 t /\
  getr regs 21 = w64 (c_n cx - lm_k m) /\ getr regs 22 = w64 (c_p cx + lm_k m) /\
  0 <= t < OPS_MAX /\ 0 <= lm_k m <= c_n cx.
(* D 0x8475c: operation t decoded (a1 = op = in.p[0] % 10) and, for op in 1-4 and 6, the source picked (s5);
   s4 / t1 the cursor and the bytes left after the bytes read; case 1 with no open source enters arm 1 with s5 = 0 *)
Definition lregs_D (cx : lfcx) (t : Z) (m : lmod) (FF : Z) (regs : bvmap 5 word) (W : world segs)
    (mem : word -> option byte) : Prop :=
  lregs_common cx FF regs /\ getr regs 25 = w64 t /\
  0 <= t < OPS_MAX /\ 0 <= lm_k m < c_n cx /\ lm_O m = [] /\
  let op := in_byte cx (lm_k m) mod 10 in
  getr regs 11 = w64 op /\
  if picks op then
    let more := lm_k m + 1 <? c_n cx in
    let kb := if more then in_byte cx (lm_k m + 1) else 0 in
    let k' := if more then lm_k m + 2 else lm_k m + 1 in
    getr regs 20 = w64 (c_p cx + k') /\ getr regs 6 = w64 (c_n cx - k') /\
    ((exists i, pick (lm_hs m) kb = Some i /\ getr regs 21 = w64 (rg_s fr_RG + ASRC * Z.of_nat i)) \/
     (op = 1 /\ pick (lm_hs m) kb = None /\ getr regs 21 = w64 0))
  else
    getr regs 20 = w64 (c_p cx + lm_k m + 1) /\ getr regs 6 = w64 (c_n cx - lm_k m - 1) /\ getr regs 21 = w64 0.
(* K 0x84804: operation t done (the model is the one after it); s4 = in.p, F+144 = in.n left *)
Definition lregs_K (cx : lfcx) (t : Z) (m : lmod) (FF : Z) (regs : bvmap 5 word) (W : world segs)
    (mem : word -> option byte) : Prop :=
  lregs_common cx FF regs /\ getr regs 25 = w64 t /\ 0 <= t < OPS_MAX /\
  getr regs 20 = w64 (c_p cx + lm_k m) /\ sv8 W mem (lf_F cx + 144) (c_n cx - lm_k m) /\ 0 <= lm_k m <= c_n cx.
(* X 0x84e64: the loop left (or never entered) after t operations; the exit block reads s0, s1, s2, s10, s11 (it
   re-derives g_nsrc's high half with auipc, so no s7 clause, and g_s with auipc, so no s3 clause).  The last conjunct
   bounds t (0 <= t <= OPS_MAX), which the exit's room facts read (lib/A/ReplyLS3oRf.v on image A, commit
   066a0abe56c); every entry to X supplies it: SEG_HEAD from lregs_H's t < OPS_MAX, SEG_LATCH from lregs_K's (B's
   SEG_PRO lands on INV_H alone, difference (2)). *)
Definition lregs_X (cx : lfcx) (t : Z) (m : lmod) (FF : Z) (regs : bvmap 5 word) (W : world segs)
    (mem : word -> option byte) : Prop :=
  getr regs 2 = w64 (lf_F cx) /\ getr regs 8 = getr (c_regs cx) 2 /\ getr regs 9 = w64 (lf_F cx) /\
  getr regs 18 = w64 HI_G_SRC /\ getr regs 26 = w64 HI_G_NOUT /\ getr regs 27 = w64 SB /\
  getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\ 0 <= lm_k m <= c_n cx /\
  0 <= t <= OPS_MAX.
(* LF: the dispatch's facts (SEG_JT reads only that they survive a materialized model) *)
Definition LF (cx : lfcx) (t : Z) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (W : world segs)
  : Prop := lcut cx t (lregs_D cx t) regs mem md W.
Lemma LF_stable : forall cx t regs mem md W X,
  LF cx t regs mem md W -> LF cx t regs mem (with_vm_backing (m_vm_lazy md) X md) W.
Proof.
  intros cx t regs mem md W X (own & ly3 & S3 & k & m & fpos & HJ & HR).
  exists own, ly3, S3, k, m, fpos. split; [|exact HR].
  apply (ajournal_gx_materialize segs B LAWS pa_segs_low). exact HJ.
Qed.
Definition lf_jour (cx : lfcx) (W : world segs) (mem : word -> option byte) (md : Model) : Prop :=
  exists own ly3 S3 k, ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) own ly3 S3 W mem md k.
(* the jump table's nine words, as the program reads them (they are .rodata; the prologue derives this from the
   contract's arodata_okS) *)
Definition jt_rom (W : world segs) (mem : word -> option byte) : Prop :=
  forall i, 0 <= i <= 8 -> val_mem segs (mrestrict (w_H W) mem) (fr_jtab + 4 * i) 4 (fr_jt_off i).
(* the registers the dispatch keeps: all but x0, a0, a1 *)
Definition jt_kept : list (bv 5) :=
  [1; 2; 3; 4; 5; 6; 7; 8; 9; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
(* H 0x845e0 *)
Definition INV_H (cx : lfcx) (t : Z) : world segs -> config -> Prop :=
  fun W c => exists regs mem md, c = cfg_at segs (fr_B0 + AF_LLVM_head) regs mem md /\
    jt_rom W mem /\ lcut cx t (lregs_H cx t) regs mem md W.
(* D 0x8475c: operation t, a1 = op decoded *)
Definition INV_D (cx : lfcx) (t op : Z) : world segs -> config -> Prop :=
  fun W c => exists regs mem md, c = cfg_at segs (fr_B0 + AF_LLVM_dispatch) regs mem md /\
    getr regs 11 = w64 op /\ lf_jour cx W mem md /\ jt_rom W mem /\ LF cx t regs mem md W.
(* A_i: arm i's entry, operation t; the registers are the dispatch's (regsD) but for a0 and a1 *)
Definition INV_A (i : Z) (cx : lfcx) (t : Z) : world segs -> config -> Prop :=
  fun W c => exists regs regsD mem md, c = cfg_at segs (fr_B0 + fr_arm i) regs mem md /\
    (forall r, In r jt_kept -> getr regs r = getr regsD r) /\ getr regsD 11 = w64 i /\
    lf_jour cx W mem md /\ jt_rom W mem /\ LF cx t regsD mem md W.
(* K 0x84804: operation t done, before check_bounded; the relational invariant is the one after t + 1 operations *)
Definition INV_K (cx : lfcx) (t : Z) : world segs -> config -> Prop :=
  fun W c => exists regs mem md, c = cfg_at segs (fr_B0 + AF_LLVM_latch) regs mem md /\
    jt_rom W mem /\ lcut cx (t + 1) (lregs_K cx t) regs mem md W.
(* X 0x84e64: the loop left after t operations *)
Definition INV_X (cx : lfcx) : world segs -> config -> Prop :=
  fun W c => exists regs mem md t, c = cfg_at segs (fr_B0 + AF_LLVM_exit) regs mem md /\
    jt_rom W mem /\ lcut cx t (fun m FF => lregs_X cx t m FF) regs mem md W.

(* ---- SEG_JT, walked: the bound check against 8 and the jump table (0x8475c-0x8477c) *)
Definition jt_region : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 24)) 0 36 0 0
    [YP09.mkChunk 0 (CVal 4 (SLit 407852)); YP09.mkChunk 4 (CVal 4 (SLit 407760));
     YP09.mkChunk 8 (CVal 4 (SLit 408136)); YP09.mkChunk 12 (CVal 4 (SLit 408292));
     YP09.mkChunk 16 (CVal 4 (SLit 408016)); YP09.mkChunk 20 (CVal 4 (SLit 408396));
     YP09.mkChunk 24 (CVal 4 (SLit 408448)); YP09.mkChunk 28 (CVal 4 (SLit 408344));
     YP09.mkChunk 32 (CVal 4 (SLit 408492))].
Definition jt_facts : facts := mkFacts [ (11%nat, mkAF 0 9 0); (32%nat, mkAF SB SB 0) ] [] [].
Definition ss_jt : sstate := mkSS AF_LLVM_dispatch sr_atoms [jt_region] None jt_facts.
Definition JBx : sv := SOff 32 0.
Definition JBspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition jt_extra : list word := map (Z_to_bv 64) [SB].
Lemma VAL_jtab : VAL (A_OBJ 24) = fr_jtab.
Proof. vm_compute. reflexivity. Qed.
Lemma BASE_B0 : BASE = fr_B0.
Proof. vm_compute. reflexivity. Qed.
Lemma jt_entry : forall (W : world segs) regs mem op,
  getr regs 11 = w64 op -> 0 <= op <= 9 -> jt_rom W mem ->
  st_ok_pi segs VAL (Eimg (Ereg regs jt_extra)) ss_jt
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_LLVM_dispatch)) mem (seg_rom segs)))
  /\ sh_ok segs JBx [] (Eimg (Ereg regs jt_extra)) (mrestrict (w_H W) mem).
Proof.
  intros W regs mem op Hop Rop HROM.
  rewrite restrict_mkst_fx.
  set (E := Eimg (Ereg regs jt_extra)).
  assert (E11 : ew E 11 = Z_to_bv 64 op)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact Hop).
  assert (E32 : ew E 32 = Z_to_bv 64 SB)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (EJ : ew E (A_OBJ 24) = Z_to_bv 64 fr_jtab)
    by (subst E; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia); rewrite VAL_jtab; reflexivity).
  split.
  - unfold ss_jt. apply pa_entry_st_ok_full.
    + apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + apply Forall_cons; [|apply Forall_nil]. unfold region_ok, jt_region.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite EJ, unsigned_lit_small by (unfold fr_jtab; lia).
      split; [unfold fr_jtab; lia|]. split; [unfold fr_jtab; lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil;
        (eapply (chunk_ok_val segs E _ fr_jtab); [reflexivity | zside | zside |]).
      * exact (HROM 0 ltac:(lia)).
      * exact (HROM 1 ltac:(lia)).
      * exact (HROM 2 ltac:(lia)).
      * exact (HROM 3 ltac:(lia)).
      * exact (HROM 4 ltac:(lia)).
      * exact (HROM 5 ltac:(lia)).
      * exact (HROM 6 ltac:(lia)).
      * exact (HROM 7 ltac:(lia)).
      * exact (HROM 8 ltac:(lia)).
    + cbn. repeat split.
    + split; [|split; [exact I | exact I]].
      cbn [jt_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E11, E32, !unsigned_lit_small by (unfold SB; lia).
      rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB. repeat match goal with |- _ /\ _ => split end; lia.
  - unfold sh_ok. constructor.
Qed.
(* LF across the materialized models of consecutive runs, at the same memory *)
Ltac lf_close HLF :=
  first [ exact HLF | apply LF_stable; lf_close HLF ].
(* a run over read-only regions leaves the memory as it was *)
Ltac jt_mem HF Em := lazymatch type of HF with frame_of ?E ?rs ?m ?m' =>
  pose proof (frame_of_read_only E rs m m' ltac:(vm_compute; reflexivity) HF) as Em end.
Theorem lf_seg_jt : forall cx t op W c, lf_base cx -> 0 <= op <= 9 -> INV_D cx t op W c ->
  SRr segs W c (INV_A op cx t).
Proof.
  intros cx t op W c HB Rop (regs & mem & md & -> & Hop & (own & ly3 & S3 & k & HJ) & HROM & HLF).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  destruct (jt_entry W regs mem op Hop Rop HROM) as [HS SHOK].
  remember (Eimg (Ereg regs jt_extra)) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (E11 : ew E 11 = Z_to_bv 64 op)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact Hop).
  assert (EJ : ew E 265 = Z_to_bv 64 fr_jtab)   (* 265 = A_OBJ 24 *)
    by (subst E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); exact (f_equal (Z_to_bv 64) VAL_jtab)).
  assert (HAE : env_agree 32 (Ereg regs jt_extra) E)
    by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  clear HE.
  unfold cfg_at. change (w64 (fr_B0 + AF_LLVM_dispatch)) with (Z_to_bv 64 (BASE + AF_LLVM_dispatch)).
  (* li a0, 8 *)
  paj_run_tok RUN HS HJ SHOK JBspan.
  { apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
  jt_mem HF Em1. clear HF HFr HG0.
  (* bltu a0, a1: op > 8 goes to the default arm *)
  psrr_branch_tok RUN BR HS SHOK JBspan.
  - assert (Hop9 : op = 9).
    { rewrite branch_ltu_U, (U_lit E 8), (U_atom E 11 op E11) in Hc by lia. apply Z.ltb_lt in Hc. lia. }
    subst op.
    paj_run_to_tok RUNTO HS HJ SHOK JBspan AF_arm_default.
    { apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
    jt_mem HF Em2.
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs jt_extra jt_kept HS HAE ltac:(vm_compute; reflexivity)) as KR.
    pmkst HS. rewrite Em2 in *. rewrite Em1 in *.
    apply SRr_ret.
    lazymatch goal with |- INV_A _ _ _ _ {| cfg_ms := mkst ?r _ _ _; cfg_model := ?d |} =>
      exists r, regs, mem, d end.
    split; [reflexivity|].
    split; [intros r Hr; exact (KR r Hr)|]. split; [exact Hop|].
    split; [exists own, ly3, S3, k; exact HJ|].
    split; [exact HROM|].
    lf_close HLF.
  - assert (Hop8 : op <= 8).
    { rewrite branch_ltu_U, (U_lit E 8), (U_atom E 11 op E11) in Hc by lia. apply Z.ltb_ge in Hc. lia. }
    prreg HS (11%bv : bv 5) R11. rewrite E11 in R11.
    assert (Hc9 : op = 0 \/ op = 1 \/ op = 2 \/ op = 3 \/ op = 4 \/ op = 5 \/ op = 6 \/ op = 7 \/ op = 8) by lia.
    destruct Hc9 as [->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]].
    all: pose proof (st_ok_pi_pin_reg' (PI := PB_fr) _ _ _ (11%bv) _ HS R11 eq_refl) as HS2; clear HS; rename HS2 into HS.
    all: cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
    all: paj_run_tok RUN HS HJ SHOK JBspan;
      [ apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil] |].
    all: jt_mem HF Em2.
    all: pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs jt_extra jt_kept HS HAE ltac:(vm_compute; reflexivity)) as KR.
    all: prreg HS (10%bv : bv 5) R10.
    all: rewrite EJ, unsigned_lit_small in R10 by (unfold fr_jtab; lia).
    (* jr a0, to fr_jtab + the table word = the arm *)
    all: eapply (SRr_jr_pi (PL := PL_fr) (PI := PB_fr) W E _ _ _ _ 327783 (10%bv : bv 5) _ HS eq_refl);
      [ vm_compute; reflexivity | vm_refl_bv | exact R10 | unfold fr_jtab; lia
      | vm_compute; reflexivity | ].
    all: intros mat' ms1 -> _.
    all: rewrite Em2 in *; rewrite Em1 in *.
    all: apply SRr_ret.
    all: lazymatch goal with |- INV_A _ _ _ _ {| cfg_ms := mkst ?r _ _ _; cfg_model := ?d |} =>
      exists r, regs, mem, d end.
    all: split; [reflexivity|].
    all: split; [intros r Hr; exact (KR r Hr)|]. all: split; [exact Hop|].
    all: rewrite wvb_collapse in HJ.
    all: split; [exists own, ly3, S3, k; apply (ajournal_gx_materialize segs B LAWS Hsegs); exact HJ|].
    all: split; [exact HROM|].
    all: lf_close HLF.
Qed.
(* SEG_JT is lf_seg_jt above. *)
Definition SEG_JT := lf_seg_jt.

(* ---- the two callees B calls out of line where A inlines them (difference (1)).
   NO KIT SPEC EXISTS for either, and no A statement: these two hypotheses are the interface W8Entry-2 agrees with
   the hand writing lib/B/W_contract.v's relay_source / relay_reads contracts.  Both are pure read-only leaves (no
   allocation, no free, no fake frame, no global store), so both posts are the kit's aleafx_post at G = [], XO = 0,
   OUT = []: the allocator state is the one they were called with, the callee-saved registers are kept, every byte
   present stays present, and every byte outside the callee's own frame window is kept. *)
Definition RSRC_STK : Z := 16.                 (* relay_source 0x85d28: addi sp,sp,-16, ra at 8 *)
Definition RRDS_STK : Z := 16 + RSRC_STK.      (* relay_reads 0x864e8: addi sp,sp,-16, ra at 8, s0 at 0; calls relay_source *)
(* relay_source(fd) scans the g_nsrc entries of the table at g_src for the first with e.fd = fd and returns its
   address, or 0.  Its three traps (0x85d68, 0x85d74, 0x85d78) need 0 < g_src and 8 | g_src, which arelay_at gives
   through the live 896-byte block; when g_nsrc = 0 it returns 0 without reading the table (0x85d38 blez). *)
Hypothesis RSRC : forall W ly S (regs : bvmap 5 word) mem md ch T es fd,
  afn_pre segs B RSRC_STK ly S W regs mem md ch ->
  getr regs 10 = w64 fd -> 0 <= fd < 2 ^ 32 ->
  arelay_at B fr_RG ly S W mem T es -> rom_view segs W mem ->
  SRr segs W (cfg_at segs (fr_B0 + AF_fr_relay_source) regs mem md)
    (aleafx_post B RSRC_STK regs ly S W mem md
      (fun a0 =>
         (exists j e, nth_error es j = Some e /\ re_fd e = fd /\
            (forall i e', (i < j)%nat -> nth_error es i = Some e' -> re_fd e' <> fd) /\
            a0 = w64 (T + AENT * Z.of_nat j)) \/
         ((forall e, In e es -> re_fd e <> fd) /\ a0 = w64 0))).
(* relay_reads(s) reads s->fd, calls relay_source on it and returns 1 when that entry exists with eof = 0, else 0.
   Its traps (0x864f4, 0x864fc, 0x8652c) need 0 < s, 8 | s and 8 | the entry; the caller supplies the first two from
   s = g_s + 96 i (g_s is 32-aligned), the third is RSRC's own post.  It shadow-checks s before `lw s->fd`
   (0x8650c-0x86518, reported at 0x86568): `azs B HA 4` (W8Entry-2's ruling 18:04Z), a sub-range of g_s's
   Tfib_zero_shadow range, which both call sites (0x84830 remove, 0x84b0c gone) supply from _G.v's c_HZS. *)
Hypothesis RRDS : forall W ly S (regs : bvmap 5 word) mem md ch T es HA h,
  afn_pre segs B RRDS_STK ly S W regs mem md ch ->
  getr regs 10 = w64 HA -> 0 < HA -> HA mod 8 = 0 -> azs B HA 4 ->
  asrc_at B ly S W mem HA h ->
  arelay_at B fr_RG ly S W mem T es -> rom_view segs W mem ->
  SRr segs W (cfg_at segs (fr_B0 + AF_fr_relay_reads) regs mem md)
    (aleafx_post B RRDS_STK regs ly S W mem md
      (fun a0 =>
         (exists j e, nth_error es j = Some e /\ re_fd e = hs_fd h /\
            (forall i e', (i < j)%nat -> nth_error es i = Some e' -> re_fd e' <> hs_fd h) /\
            a0 = w64 (if re_eof e =? 0 then 1 else 0)) \/
         ((forall e, In e es -> re_fd e <> hs_fd h) /\ a0 = w64 0))).
(* the two texts, as one checked statement, so the arms' holders copy the same interface *)
Lemma rsrc_rrds_text :
  (forall W ly S (regs : bvmap 5 word) mem md ch T es fd,
   afn_pre segs B RSRC_STK ly S W regs mem md ch ->
   getr regs 10 = w64 fd -> 0 <= fd < 2 ^ 32 ->
   arelay_at B fr_RG ly S W mem T es -> rom_view segs W mem ->
   SRr segs W (cfg_at segs (fr_B0 + AF_fr_relay_source) regs mem md)
     (aleafx_post B RSRC_STK regs ly S W mem md
       (fun a0 =>
          (exists j e, nth_error es j = Some e /\ re_fd e = fd /\
             (forall i e', (i < j)%nat -> nth_error es i = Some e' -> re_fd e' <> fd) /\
             a0 = w64 (T + AENT * Z.of_nat j)) \/
          ((forall e, In e es -> re_fd e <> fd) /\ a0 = w64 0)))) /\
  (forall W ly S (regs : bvmap 5 word) mem md ch T es HA h,
   afn_pre segs B RRDS_STK ly S W regs mem md ch ->
   getr regs 10 = w64 HA -> 0 < HA -> HA mod 8 = 0 -> azs B HA 4 ->
   asrc_at B ly S W mem HA h ->
   arelay_at B fr_RG ly S W mem T es -> rom_view segs W mem ->
   SRr segs W (cfg_at segs (fr_B0 + AF_fr_relay_reads) regs mem md)
     (aleafx_post B RRDS_STK regs ly S W mem md
       (fun a0 =>
          (exists j e, nth_error es j = Some e /\ re_fd e = hs_fd h /\
             (forall i e', (i < j)%nat -> nth_error es i = Some e' -> re_fd e' <> hs_fd h) /\
             a0 = w64 (if re_eof e =? 0 then 1 else 0)) \/
          ((forall e, In e es -> re_fd e <> hs_fd h) /\ a0 = w64 0)))).
Proof. exact (conj RSRC RRDS). Qed.

(* The segments.  SEG_PRO: the prologue (frame, fake stack, the size refusal at 0x84530 refuted by n < 2^26, the
   globals' reset, op_add()) up to the loop head.  Unlike A, B's prologue has no empty-input branch of its own: the
   `in.n = 0` test is the head itself, so there is no `\/ INV_X` here (difference (2)). *)
Hypothesis SEG_PRO : forall cx, lf_base cx -> SRr segs (c_W cx) (lf_entry cx) (INV_H cx 0).
(* SEG_HEAD: the loop test `in.n != 0` (0x845e0, to the exit when it fails); one byte read for op; for op in 1-4
   and 6 the picked source (the open count and the k-th open source, the two loops at 0x84674 and 0x846d8); then the
   dispatch, case 1 with no source, or `continue` (0x8471c), which skips check_bounded and lands on the latch tail
   0x8480c (walked within SEG_HEAD to the next head or the exit). *)
Hypothesis SEG_HEAD : forall cx t W c, lf_base cx -> INV_H cx t W c ->
  SRr segs W c (fun W' c' => (exists op, 0 <= op <= 9 /\ INV_D cx t op W' c') \/ INV_A 1 cx t W' c' \/
    INV_H cx (t + 1) W' c' \/ INV_X cx W' c').
(* SEG_JT: the bound check against 8 and the jump table: arm `op` (op 9: the default arm); lf_seg_jt above. *)
(* The ten arms, each from its entry to the latch. *)
Hypothesis ARM_add : forall cx t W c, lf_base cx -> INV_A 0 cx t W c -> SRr segs W c (INV_K cx t).
Hypothesis ARM_write : forall cx t W c, lf_base cx -> INV_A 1 cx t W c -> SRr segs W c (INV_K cx t).
Hypothesis ARM_drain : forall cx t W c, lf_base cx -> INV_A 2 cx t W c -> SRr segs W c (INV_K cx t).
Hypothesis ARM_close : forall cx t W c, lf_base cx -> INV_A 3 cx t W c -> SRr segs W c (INV_K cx t).
Hypothesis ARM_remove : forall cx t W c, lf_base cx -> INV_A 4 cx t W c -> SRr segs W c (INV_K cx t).
Hypothesis ARM_gone : forall cx t W c, lf_base cx -> INV_A 5 cx t W c -> SRr segs W c (INV_K cx t).
Hypothesis ARM_eintr : forall cx t W c, lf_base cx -> INV_A 6 cx t W c -> SRr segs W c (INV_K cx t).
Hypothesis ARM_event : forall cx t W c, lf_base cx -> INV_A 7 cx t W c -> SRr segs W c (INV_K cx t).
Hypothesis ARM_sendmax : forall cx t W c, lf_base cx -> INV_A 8 cx t W c -> SRr segs W c (INV_K cx t).
Hypothesis ARM_default : forall cx t W c, lf_base cx -> INV_A 9 cx t W c -> SRr segs W c (INV_K cx t).
(* SEG_LATCH: check_bounded() and the loop counter (0x84808-0x84820: in.n and in.p reloaded, t + 1, t + 1 = 512). *)
Hypothesis SEG_LATCH : forall cx t W c, lf_base cx -> INV_K cx t W c ->
  SRr segs W c (fun W' c' => INV_H cx (t + 1) W' c' \/ INV_X cx W' c').
Lemma H_BOUND : forall cx t W c, INV_H cx t W c -> 0 <= t < OPS_MAX.
Proof.
  intros cx t W c (regs & mem & md & _ & _ & (own & ly3 & S3 & k & m & fpos & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HR)).
  destruct HR as (_ & _ & _ & _ & Ht & _). exact Ht.
Qed.
(* SEG_EXIT: relay_finish(), the held gestures' ends in the relay's table order, check_shape_done, the four
   source_reset()s, the fake frame's release and the epilogue. *)
Hypothesis SEG_EXIT : forall cx W c, lf_base cx -> INV_X cx W c -> SRr segs W c (lf_post cx).

(* one operation: the jump table's case split *)
Lemma lf_arm : forall cx t op W c, lf_base cx -> 0 <= op <= 9 -> INV_A op cx t W c -> SRr segs W c (INV_K cx t).
Proof.
  intros cx t op W c HB Hop HA.
  assert (op = 0 \/ op = 1 \/ op = 2 \/ op = 3 \/ op = 4 \/ op = 5 \/ op = 6 \/ op = 7 \/ op = 8 \/ op = 9) as Hc by lia.
  destruct Hc as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]].
  - exact (ARM_add cx t W c HB HA).
  - exact (ARM_write cx t W c HB HA).
  - exact (ARM_drain cx t W c HB HA).
  - exact (ARM_close cx t W c HB HA).
  - exact (ARM_remove cx t W c HB HA).
  - exact (ARM_gone cx t W c HB HA).
  - exact (ARM_eintr cx t W c HB HA).
  - exact (ARM_event cx t W c HB HA).
  - exact (ARM_sendmax cx t W c HB HA).
  - exact (ARM_default cx t W c HB HA).
Qed.
Lemma lf_iter : forall cx t W c, lf_base cx -> INV_H cx t W c ->
  SRr segs W c (fun W' c' => INV_H cx (t + 1) W' c' \/ INV_X cx W' c').
Proof.
  intros cx t W c HB HH.
  eapply SRr_bind; [exact (SEG_HEAD cx t W c HB HH)|].
  intros W1 c1 _ [(op & Hop & HD) | [HA | HHX]].
  - eapply SRr_bind; [exact (SEG_JT cx t op W1 c1 HB Hop HD)|].
    intros W2 c2 _ HA. eapply SRr_bind; [exact (lf_arm cx t op W2 c2 HB Hop HA)|].
    intros W3 c3 _ HK. exact (SEG_LATCH cx t W3 c3 HB HK).
  - eapply SRr_bind; [exact (ARM_write cx t W1 c1 HB HA)|].
    intros W3 c3 _ HK. exact (SEG_LATCH cx t W3 c3 HB HK).
  - exact (SRr_ret segs W1 c1 _ HHX).
Qed.
(* the operation loop: at most OPS_MAX - t more operations *)
Lemma lf_loop : forall cx, lf_base cx -> forall (m : nat) t W c, OPS_MAX - t <= Z.of_nat m -> INV_H cx t W c ->
  SRr segs W c (lf_post cx).
Proof.
  intros cx HB m. induction m as [|m IH]; intros t W c Hm HH.
  - pose proof (H_BOUND cx t W c HH) as Ht. cbn in Hm. lia.
  - pose proof (H_BOUND cx t W c HH) as Ht.
    eapply SRr_bind; [exact (lf_iter cx t W c HB HH)|].
    intros W' c' _ [HH' | HX].
    + apply (IH (t + 1) W' c'); [rewrite Nat2Z.inj_succ in Hm; lia | exact HH'].
    + exact (SEG_EXIT cx W' c' HB HX).
Qed.
Theorem lf_main : forall cx, lf_base cx -> SRr segs (c_W cx) (lf_entry cx) (lf_post cx).
Proof.
  intros cx HB.
  eapply SRr_bind; [exact (SEG_PRO cx HB)|].
  intros W' c' _ HH.
  exact (lf_loop cx HB (Z.to_nat OPS_MAX) 0 W' c' ltac:(unfold OPS_MAX; lia) HH).
Qed.

(* The program contract, in the donor's form at checksum_shape, from the segments (the theorem the B milestone
   consumes is lib/B/W_asm.v's ENTRY, which supplies the segments and the cf bridge). *)
Theorem lf_contract_of_segments :
  @fr_lib_contract_cf fx rc SK checksum_shape B MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv G_fr fr_FP.
Proof.
  intros ly S W regs mem md p n pl M K HAI HPRE HK.
  change tfibsegs with segs in *.
  change (LIBK pl (m_fs md) K) with (K (LL 0 (m_fs md) [])).
  apply (fr_srz_enter segs W (cfg_at segs A_LLVMF regs mem md) _ HAI).
  eapply SRr_mono; [exact (lf_main (LFCX ly S W regs mem md p n pl M) (conj HAI HPRE))|].
  intros W' c' Hwle (ly' & S' & regs' & mem' & md' & k & Hc & HP) HAI'.
  apply (HK (LL 0 (m_fs md) []) W' c' Hwle HAI'). exists ly', S', regs', mem', md', k. split; [exact Hc | exact HP].
Qed.
End w.
