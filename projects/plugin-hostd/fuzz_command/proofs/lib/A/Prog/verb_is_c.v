(* The contract of verb_is on the ASan build of plugin-hostd/fuzz_command.

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): afn_pre at the entry,
   SRr of apost_base at the return. Functional content: fuzz_command's own released plain contract
   lib/Prog/verb_is_c.v:15-34 (the return value at :32) and its model lib/Spec/Verbs.v:124-127 (verb_is_m).
   The function (L/src/verbs.h:35, out of line; verbs_receive calls it three times) asks whether a token names the
   verb of a format: n = strcspn(f, " "), then strcspn(t, " \t") = n and strncmp(t, f, n) = 0. It writes nothing
   outside its own frame and allocates nothing.

   Addresses: entry BASE + AF_verb_is = 0x8df5c (M, the pinned image). 30 instructions, frame 32 bytes
   (`addi sp,sp,-32`, no realignment), no inline check, no loop, three wrapper calls: strcspn twice and strncmp
   (`___interceptor_<f>`, reached through the 4-byte jump `__interceptor_trampoline_<f>`). The two separator
   literals it passes, " " (.str.56, 0x22d80) and " \t" (.str, 0x224c0), are image objects, so their bytes are
   conjuncts of cmd_ro_ok (lib/A/Prog/CmdRo.v: RO_lit_22d80, RO_lit_224c0).
   The arguments: its one caller, verbs_receive, passes its first word tok[0] (s10, a word of its strdup block
   `copy`) as t, and an image literal as f (.str.21 0x227e0 at 0x8d8a0, .str.22 0x22800 at 0x8de4c, .str.23 0x22820
   at 0x8de6c). So t is a heap string, whose word tail is readable by cmd_heap_tail_vis
   (lib/A/Prog/CmdRecFacts.v), and f keeps astr_argA (its tail: cmd_tail_vis). The stack-protector cells the musl
   body under the strcspn wrapper compares are cmd_rec_cells. It allocates nothing and takes no side-stack frame,
   so its post gives `ly' = ly /\ S' = S` (meter class (a)). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdObj CmdRo CmdBase CmdRep.
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
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* the stack this call needs: its own 32-byte frame, and the window the strcspn and strncmp wrappers ask for
   (RtDefs.v's ecall_pre_stk segs B (2 * ESTACK), lib/A/Rt/RtString.v astrcspn_realizes / astrncmp_realizes) *)
Definition VERB_IS_STK : Z := 32 + 2 * ESTACK.
Definition EV_VERB_IS : Z := 0.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the wrappers it calls: the runtime contracts, at the listing's call targets. The span entries name the musl GOT word
   0xa7098 and the guard cell 0x6045d8 the body they run compares against *)
Hypothesis STRCSPN : forall fx0 : YK11.FPState, @RtString.astrcspn_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_strcspn) 0xa7098 0x6045d8.
Hypothesis STRNCMP : forall fx0 : YK11.FPState, @RtString.astrncmp_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_strncmp).
(* `using MT`: the post has no meter conjunct (frame form), so MT is named here to keep the uniform signature
   tverb_is_spec B MT *)
#[using="MT"]
Definition tverb_is_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md (t f : Z) (tb fb : list byte),
afn_pre_na SEGS B VERB_IS_STK ly S W regs mem md ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
getr regs 10 = w64 t -> 0 <= t < 2 ^ 64 -> getr regs 11 = w64 f -> 0 <= f < 2 ^ 64 ->
(* the token: a heap string (a word of verbs_receive's `copy` block); the format: an image literal, a string in a
   live block or in the read-only range (astr_argA), with its word tail readable *)
in_blockA (ablocks B ly S) t (Z.of_nat (length tb) + 1) -> astr_atR (rdW W mem) t tb ->
Z.of_nat (length tb) + 1 <= LMAX + 1 ->
astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) [] f (Some fb) ->
atail_vis SEGS W mem (f + Z.of_nat (length fb)) ->
(* the separator literals, and the bridge from the listing's object atoms to their addresses *)
cmd_ro_ok (rdW W mem) -> cmd_val_objs ->
st_nev S + EV_VERB_IS <= EV_MAX ->
SRr SEGS W (cfg_at SEGS (BASE + AF_verb_is) regs mem md)
(apost_base SEGS B VERB_IS_STK [] regs ly S W mem md EV_VERB_IS
(fun ly' S' W' regs' mem' md' =>
 getr regs' 10 = w64 (if Verbs.verb_is_m tb fb then 1 else 0) /\
 Permutation (ablocks B ly' S') (ablocks B ly S) /\
 (* it allocates nothing and takes no side-stack frame (meter class (a)) *)
 ly' = ly /\ S' = S)).
End e.
End f.
End d.
