(* The contract of joined on the ASan build of plugin-hostd/fuzz_command.

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): afn_pre at the entry,
   SRr of apost_base at the return; the fresh block and the meter as cgif's trawnew_specX states them
   (lib/YC7x.v:88, :92-101). Functional content: fuzz_command's own released plain contract lib/Prog/joined_c.v:20-79
   (join_need; words_view / words_place; a fresh block of join_need ws + 1 bytes that holds join_sp ws and its
   terminator, and *len = |join_sp ws|) and the model lib/Prog/RecFacts.v (join_sp).
   joined(w, len) (H/fuzz_command.c:152-177) sums strlen(w->w[k]) + 1 over the w->n words with the strlen wrapper
   (`___interceptor_strlen`, reached through the 4-byte jump `__interceptor_trampoline_strlen`), allocates that sum
   plus 1 through the malloc wrapper (0x888c0, the only allocation of the program whose size the input decides),
   writes the words with `__asan_memcpy`, one space between two, and a terminator, stores the length to *len and
   returns the block. The malloc rule returns a block at or above 4096, so the abort edge (`__asan_handle_no_return`,
   then abort) on a null result is not taken.
   `struct words` is {text @0, copy @8, w @16, n @24}; it lives in LLVMFuzzerTestOneInput's real stack frame. len
   is in the caller's real stack frame too (check_words passes s1 + 176 at 0x879e0, check_round_trip s1 + 144 at
   0x88248, s1 being each caller's realigned real stack pointer: ASan's stack-safety analysis kept it out of their
   side-stack frames), above joined's own stack pointer, so the footprint names [len, len + 8); as a written
   caller-stack slot it lies below ly_top (awr_byte's caller-stack clause, YCbq.v:502).
   s0 holds len (0x88848 mv s0,a1) at every runtime call, among them the malloc wrapper (0x888c0), whose rule asks
   chain_pre of s0: the frame chain from len is a premise (the only allocating call site of the program whose s0 is a
   stack pointer that is not a frame base, measured), which each caller gives from its own frame. The words
   are harness words, pointers into words_of's `copy` block (fuzz_command.c:120) for both callers, so they are
   stated as live blocks; the strlen wrapper's reads come from AR's block facts and each tail word from
   `cmd_heap_tail_vis`.

   Addresses: entry BASE + AF_joined = 0x887f4 (M, the pinned image). 178 instructions, 2 loops (0x88888, 0x88914),
   no side-stack frame, 13 inline checks: load4 on w->n (0x88844, 0x888e0, 0x88990), load8 on w->w (0x88864,
   0x88914, 0x88960) and on w->w[k] (0x88888, 0x8892c, 0x88978), store1 on the block (0x888d4, 0x88950, 0x889d8) and
   store8 on *len (0x889ec), each a read of the shadow byte at (a >> 3) + 0x7fff8000. The error path (a call of
   `__asan_report_*`) is not reached: the struct and len lie in the stack window, whose shadow AR's zshadow_ok
   keeps usable at every state (YG0n.v:188), the word array is in a live block, and every store to the block lands
   below join_need ws + 1. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require joined_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Module PJoin := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.joined_c.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* the stack this call needs: its own 112-byte frame, and the window the malloc wrapper asks for (ASTACK, cgif
   lib/YG0d.v:17; amalloc04_rule asks ASTACK - o <= STK, lib/YC5d.v:60). The strlen wrapper's window and
   __asan_memcpy's (ESTACK each, the runtime contracts' final windows) are smaller. *)
Definition JOINED_STK : Z := 112 + ASTACK.
(* one allocator event: the malloc *)
Definition EV_JOINED : Z := 1.
(* the live bytes the call adds: at most one malloc's worth (MALLOC_MAX, cgif lib/YG00.v:38) *)
Definition LIVE_JOINED : Z := MALLOC_MAX.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the meter the call spends: one malloc of join_need ws + 1 bytes *)
Definition XM_JOINED (ws : list (list byte)) : Z := mo_malloc MT (PJoin.join_need ws + 1).
(* the runtime entries the call reaches *)
Hypothesis AMALLOC4 : forall fx0 : YK11.FPState, @amalloc04_rule fx0 rc SK SEGS B MT.
Hypothesis AMEMCPY : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OCpy (SIG CS___asan_memcpy).
Hypothesis ASTRLEN : forall fx0 : YK11.FPState, @astrlen_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strlen).
Definition tjoined_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (W0 arr outp : Z) (wp : list Z) (ws : list (list byte)),
afn_pre SEGS B JOINED_STK ly S W regs mem md ch ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
getr regs 10 = w64 W0 -> getr regs 11 = w64 outp ->
(* the struct words, on the caller's real stack above this call's window, read only: n at +24, w at +16 (plain
   words_view, joined_c.v:41-44, and :58). It is 8-aligned: the B statement's premise (lib/B/Prog/joined_c.v:98, the
   UBSan trap 0x88b90 of the asan-ubsan build), carried here so that the A and B statements agree (this port's
   decision); both callers, check_words and check_round_trip, have it as a premise *)
spZ regs <= W0 + 16 -> W0 + 32 <= ly_stk_hi ly -> W0 mod 8 = 0 ->
length wp = length ws -> Z.of_nat (length ws) < 2 ^ 31 ->
aval_mem (rdW W mem) (W0 + 24) 4 (Z.of_nat (length ws)) ->
aval_mem (rdW W mem) (W0 + 16) 8 arr -> 0 <= arr < 2 ^ 64 ->
(* the word array in a live block, each word a string in a live block (plain words_view / words_place,
   joined_c.v:36-46); the array is 8-aligned (words_of's malloc of cap 8-byte pointers, fuzz_command.c:118): the B
   statement's premise (lib/B/Prog/joined_c.v:105, the UBSan traps 0x88c08, 0x88cc8 and 0x88d3c of the asan-ubsan
   build), carried here so that the A and B statements agree (this port's decision); both callers have it as a premise *)
arr mod 8 = 0 ->
in_blockA (ablocks B ly S) arr (8 * Z.of_nat (length ws)) ->
(forall k, (k < length ws)%nat ->
 aval_mem (rdW W mem) (arr + 8 * Z.of_nat k) 8 (nth k wp 0) /\ 0 <= nth k wp 0 < 2 ^ 64 /\
 in_blockA (ablocks B ly S) (nth k wp 0) (Z.of_nat (length (nth k ws [])) + 1) /\
 astr_atR (rdW W mem) (nth k wp 0) (nth k ws [])) ->
(* the size fits one malloc (plain :59; amalloc04_rule asks n < MALLOC_MAX, lib/YC5d.v:59) *)
PJoin.join_need ws + 1 < MALLOC_MAX ->
(* len: 8 aligned bytes of the caller's real stack that the call writes, inside the stack window below ly_top,
   apart from the struct's fields (plain :60-62) *)
spZ regs <= outp -> outp + 8 <= ly_top ly -> outp mod 8 = 0 ->
(outp + 8 <= W0 + 16 \/ W0 + 32 <= outp) ->
(* len's 8 bytes are present (the store at 0x889f4 asks writable_at). s0 = len at the malloc call 0x888c0 (0x88848
   mv s0,a1; s0 is not written before the call), so ASan's fast unwinder starts its chain at len: it reads len - 8
   (the caller's word) and len - 16, a slot neither caller writes (check_words s1 + 160, check_round_trip s1 + 128),
   and follows that word while it is an aligned address below the stack top (YG00.v:367-374, UnwindFast). Every
   word the chain can read lies in the machine stack [len - 16, ly_top), which the process maps to its top: that
   presence is the premise (pass 5b, joined's chain) *)
(forall i, 0 <= i < 8 -> apresent (w_H W) mem (outp + i)) ->
astack_pres ly (w_H W) mem (outp - 16) ->
st_nev S + EV_JOINED <= EV_MAX -> blocks_bytes S + LIVE_JOINED <= LIVE_MAX ->
mo_ok MT S (XM_JOINED ws) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_joined) regs mem md)
(apost_base SEGS B JOINED_STK [(outp, outp + 8)] regs ly S W mem md EV_JOINED
(fun ly' S' W' regs' mem' md' => exists res : Z,
 getr regs' 10 = w64 res /\ 4096 <= res < 2 ^ 64 /\
 (* a fresh block, apart from every block that was live (plain joined_c.v:70-71) *)
 Permutation (ablocks B ly' S') ((res, PJoin.join_need ws + 1) :: ablocks B ly S) /\
 Forall (fun qk => iv_apart res (PJoin.join_need ws + 1) (fst qk) (snd qk)) (ablocks B ly S) /\
 (* it holds the words joined by one space and a terminator, in a live block (the form send_message asks of its
    message); *len holds that length (plain :72-73) *)
 in_blockA (ablocks B ly' S') res (PJoin.join_need ws + 1) /\
 abytes_atR (rdW W' mem') res (join_sp ws ++ [Z_to_bv 8 0]) /\
 aval_mem (rdW W' mem') outp 8 (Z.of_nat (length (join_sp ws))) /\
 (* the blocks that were live are kept (plain :74) *)
 (forall p n i, In (p, n) (ablocks B ly S) -> 0 <= i < n -> rdW W' mem' (p + i) = rdW W mem (p + i)) /\
 blocks_bytes S' <= blocks_bytes S + LIVE_JOINED /\
 mo_le MT S S' (XM_JOINED ws))).
End e.
End f.
End d.
