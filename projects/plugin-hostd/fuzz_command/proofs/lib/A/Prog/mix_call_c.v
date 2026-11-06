(* The contract of mix_call on the ASan build of plugin-hostd/fuzz_command.

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): afn_pre at the entry,
   SRr of apost_base at the return. Functional content: fuzz_command's own released plain contract
   lib/Prog/mix_call_c.v:23-47 (the result `mixcall h fn (map snd args)`) and the model lib/Prog/RecFacts.v:224-229
   (mix, mixcall: FNV-1a, 64 bits, over the 4 bytes of the call's function number and over each argument with its
   terminator). The plain contract takes the arguments as a list of (pointer, string) pairs; here they are the
   recorded call as the recorder's representation states it (`acall_at`, lib/A/Prog/CmdRep.v), so the strings are
   `snd e`.
   mix_call(h, c) (recorder.c:194-202, `mix` inlined, :180-192) reads c->fn byte by byte, c->nargs, each
   c->args[a], calls strlen on that argument and reads its bytes and its terminator. It writes nothing outside its
   own frame and allocates nothing (FP = [], no meter).

   Addresses: entry BASE + AF_mix_call = 0x8a7d8 (M, the pinned image). 97 instructions, 3 loops (the 4 bytes of
   c->fn, the arguments, the bytes of one argument), 4 inline checks (load1 on c->fn, load4 on c->nargs, load8 on
   c->args[a], load1 on the argument's bytes: each reads the shadow byte at (a >> 3) + 0x7fff8000; the error path,
   a call of `__asan_report_*`, is not reached), one wrapper call (strlen, `___interceptor_strlen` reached through
   the 4-byte jump `__interceptor_trampoline_strlen`). The FNV offset basis is the read-only word at 0x10330
   (`ld s0,-1252(a2)` at 0x8a81c and 0x8a890). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdObj CmdRo.
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
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
(* the stack this call needs: its own 80-byte frame (no realignment), and the window the strlen wrapper asks for
   (RtString.v's astrlen_realizes, ecall_pre_stk segs B ESTACK) *)
Definition MIX_CALL_STK : Z := 80 + ESTACK.
Definition EV_MIX_CALL : Z := 0.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the runtime entry the call reaches, with RtString.v's name, and the bridge from the image's object addresses to the
   listing's atoms (the FNV word at 0x10330 is one of them) *)
Hypothesis ASTRLEN : forall fx0 : YK11.FPState, @astrlen_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strlen).
Hypothesis VOBJS : cmd_val_objs.
(* `using MT`: the post has no meter conjunct (frame form), so MT is named here to keep the uniform signature
   tmix_call_spec B MT *)
#[using="MT"]
Definition tmix_call_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md (h c : Z) (e : rcall) (P : list (Z * Z)),
afn_pre_na SEGS B MIX_CALL_STK ly S W regs mem md ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
getr regs 10 = w64 h -> 0 <= h < 2 ^ 64 ->
getr regs 11 = w64 c ->
(* c is a slot of g_rec's call table or record.spill: program globals whose shadow is usable (CmdRecFacts'
   cmd_addressable_chk), so the checks on c->fn, c->nargs and c->args[a] pass *)
((exists i, 0 <= i < REC_CALLS_MAX /\ c = A_G_REC + OFF_CALLS + CALL_SIZE * i) \/ c = A_REC_SPILL) ->
(* the call it holds: function number, argument count, and each argument a string at the start of a live block;
   the strlen wrapper's reads of an argument: its bytes from acall_at, its tail word by cmd_heap_tail_vis (the
   terminator lies inside the argument's block) *)
acall_at (ablocks B ly S) (rdW W mem) c e P ->
(* the read-only bytes of the image; the FNV-1a offset basis is RO_lit_10330 *)
cmd_ro_ok (rdW W mem) ->
st_nev S + EV_MIX_CALL <= EV_MAX ->
SRr SEGS W (cfg_at SEGS (BASE + AF_mix_call) regs mem md)
(apost_base SEGS B MIX_CALL_STK [] regs ly S W mem md EV_MIX_CALL
(fun ly' S' W' regs' mem' md' =>
getr regs' 10 = w64 (mixcall h (fst e) (snd e)) /\
Permutation (ablocks B ly' S') (ablocks B ly S) /\
(* no allocator call and no side-stack frame: the layout and the allocator state are the entry's (the frame form
   of meter class (a); it gives mo_le MT S S' 0 by mo_le_refl) *)
ly' = ly /\ S' = S)).
End e.
End f.
End d.
