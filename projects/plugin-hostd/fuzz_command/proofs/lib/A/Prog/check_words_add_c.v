(* The contract of check_words_add on the ASan build of plugin-hostd/fuzz_command.

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): afn_pre at the entry,
   SRr of apost_base at the return. Functional content: fuzz_command's own released plain contract
   lib/Prog/check_words_add_c.v:24-41, with its model in the same file (:12-22: is_placement_b, add_placement,
   add_next, add_client) and lib/Prog/CommandModel.v:42-45 (S_DASH, S_OWN, S_DEFAULT, S_POOL).
   The function (fuzz_command.c:333-352, is_placement inlined) takes the placement from word 3 when that word is
   "own", "default" or starts with "pool:" (two calls of the strcmp wrapper `___interceptor_strcmp` and one of the
   strncmp wrapper `___interceptor_strncmp`, reached through the 4-byte jumps `__interceptor_trampoline_strcmp` and
   `__interceptor_trampoline_strncmp`), else "-"; the client is the word after it, or "-"; then it checks that the
   recorded add call has 4 arguments and that arguments 2 and 3 are the placement and the client (two more strcmp
   calls), and calls abort() if not. The premises `nargs = 4`, `x2 = add_placement r w3` and
   `x3 = add_client r w3 w4` are what the caller (check_words) has established from `call_words_ok`
   (lib/Prog/check_words_c.v:63-65), so the abort edge (`__asan_handle_no_return`, then abort) is not taken.
   7 inline checks (shadow byte at (a >> 3) + 0x7fff8000): w[3] and w[next] in the heap array w->w (8-byte loads),
   placement[0] and placement[1] (1-byte loads, a word or the literal "-"), call->nargs, call->args[2],
   call->args[3] in g_rec; each byte is marked usable (the heap slots and words by AR's block facts, g_rec by
   `cmd_addressable_chk`, the literal by `cmd_addressable_chk`), so no error path (a call of
   `__asan_report_load1/4/8`) is reached. Every string it compares is a live block (every caller passes the
   recorded call's arguments, blocks by acall_at, and harness words in words_of's `copy` block,
   fuzz_command.c:120), so the wrappers' reads come from AR's block facts and each tail word from
   `cmd_heap_tail_vis`; the literals' reads from `cmd_aread_ok_chk`, their tails from `cmd_tail_vis`.
   s0 holds cp (0x88ae4 mv s0,a0) at the strcmp / strncmp calls only; no program call, no allocator call, so no
   achain premise. It reaches no heap allocator and no side-stack frame: the post keeps ly and S.

   Addresses: entry BASE + AF_check_words_add = 0x88abc (M, the pinned image). 121 instructions, 7 inline checks,
   no loop, frame 64 bytes (`addi sp,sp,-64`), no side-stack frame. The literals it reads (M, read from the pinned
   image; lib/A/Prog/CmdRo.v): "-" 0x21ac0 (RO_lit_21ac0), "own" 0x21ae0 (RO_lit_21ae0), "default" 0x21b00
   (RO_lit_21b00), "pool:" 0x21b20 (RO_lit_21b20). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import check_words_add_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaNoChain.
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
(* the stack this call needs: its own 64-byte frame, and the window the strcmp and strncmp wrappers ask for
   (ecall_pre_stk SEGS B (2 * ESTACK), lib/A/Rt/RtString.v:89, :102) *)
Definition CHECK_WORDS_ADD_STK : Z := 64 + 2 * ESTACK.
(* no allocator event: no malloc, no free, and neither wrapper allocates *)
Definition EV_CHECK_WORDS_ADD : Z := 0.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the runtime entries the call reaches, with this tree's names *)
Hypothesis ASTRCMP : forall fx0 : YK11.FPState, @astrcmp_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strcmp).
Hypothesis ASTRNCMP : forall fx0 : YK11.FPState, @astrncmp_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strncmp).
(* `using MT`: the post has no meter conjunct (frame form), so MT is named here to keep the uniform signature
   tcheck_words_add_spec B MT *)
#[using="MT"]
Definition tcheck_words_add_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md (cp wp r nargs p3 p4 q2 q3 : Z) (w3 w4 x2 x3 : list byte),
afn_pre_na SEGS B CHECK_WORDS_ADD_STK ly S W regs mem md ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
getr regs 10 = w64 cp -> getr regs 11 = w64 wp -> getr regs 12 = w64 r ->
0 <= r <= 64 -> 0 <= wp < 2 ^ 64 ->
(* the read-only bytes of the image, among them the four literals it reads (their shadow: `cmd_aread_ok_chk`,
   so no shadow premise) *)
cmd_ro_ok (rdW W mem) ->
(* the bridge from the listing's object atoms to the literals' absolute addresses (lib/A/Prog/CmdObj.v:21-22) *)
cmd_val_objs ->
(* the recorded call sits inside the recorder's object g_rec (its shadow usable by `cmd_addressable_chk`), so the
   inline checks at cp + 4, cp + 24 and cp + 32 need only the address range *)
A_G_REC + OFF_CALLS <= cp -> cp + CALL_SIZE <= A_G_REC + REC_SIZE ->
(* call is 8-aligned: the B statement's premise (lib/B/Prog/check_words_add_c.v:99, the UBSan trap 0x88ff0 of the
   asan-ubsan build, the alignment of call for call->nargs), carried here so that the A and B statements agree
   (this port's decision). The caller check_words passes &g_rec.calls[c] = A_G_REC + OFF_CALLS + CALL_SIZE * c, a
   multiple of 8 *)
cp mod 8 = 0 ->
aval_mem (rdW W mem) (cp + CALL_OFF_NARGS) 4 nargs -> 0 <= nargs <= 6 ->
(* its arguments 2 and 3, strings the recorder holds, each in a live block (plain :36-37; acall_at) *)
(nargs = 4 ->
 aval_mem (rdW W mem) (cp + CALL_OFF_ARGS + 16) 8 q2 /\ 0 <= q2 < 2 ^ 64 /\
 in_blockA (ablocks B ly S) q2 (Z.of_nat (length x2) + 1) /\ astr_atR (rdW W mem) q2 x2) ->
(nargs = 4 ->
 aval_mem (rdW W mem) (cp + CALL_OFF_ARGS + 24) 8 q3 /\ 0 <= q3 < 2 ^ 64 /\
 in_blockA (ablocks B ly S) q3 (Z.of_nat (length x3) + 1) /\ astr_atR (rdW W mem) q3 x3) ->
(* the harness's word list (plain :31-32): slots 3 and 4 of the heap array w->w, and the words they point at,
   pointers into the one `copy` block (fuzz_command.c:132-141) *)
(3 < r ->
 in_blockA (ablocks B ly S) (wp + 24) 8 /\ aval_mem (rdW W mem) (wp + 24) 8 p3 /\ 0 <= p3 < 2 ^ 64 /\
 in_blockA (ablocks B ly S) p3 (Z.of_nat (length w3) + 1) /\ astr_atR (rdW W mem) p3 w3) ->
(4 < r ->
 in_blockA (ablocks B ly S) (wp + 32) 8 /\ aval_mem (rdW W mem) (wp + 32) 8 p4 /\ 0 <= p4 < 2 ^ 64 /\
 in_blockA (ablocks B ly S) p4 (Z.of_nat (length w4) + 1) /\ astr_atR (rdW W mem) p4 w4) ->
(* w is 8-aligned: the B statement's premise (lib/B/Prog/check_words_add_c.v:121, the UBSan traps 0x88f08 and
   0x88fd0 of the asan-ubsan build, the 8-byte loads w[3] and w[next]), carried here so that the A and B statements
   agree (this port's decision). w->w is a malloc block start (AR_blocks_law: mod 16 = 0); the caller check_words
   passes it as it read it, with its own `arr mod 8 = 0` *)
wp mod 8 = 0 ->
(* what the caller has checked (plain :38): the recorded placement and client are the ones the message asks for *)
nargs = 4 -> x2 = add_placement r w3 -> x3 = add_client r w3 w4 ->
st_nev S + EV_CHECK_WORDS_ADD <= EV_MAX ->
SRr SEGS W (cfg_at SEGS (BASE + AF_check_words_add) regs mem md)
(apost_base SEGS B CHECK_WORDS_ADD_STK [] regs ly S W mem md EV_CHECK_WORDS_ADD
(fun ly' S' W' regs' mem' md' => Permutation (ablocks B ly' S') (ablocks B ly S) /\ ly' = ly /\ S' = S)).
End e.
End f.
End d.
