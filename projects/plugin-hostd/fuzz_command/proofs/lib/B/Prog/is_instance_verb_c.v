(* The contract of is_instance_verb on the ASan+UBSan build of plugin-hostd/fuzz_command (fuzz_command.asan-ubsan).

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): afn_pre at the entry,
   SRr of apost_base at the return. Functional content: fuzz_command's own released plain contract
   lib/Prog/is_instance_verb_c.v:19-41 (the return value at :39) and its model lib/Spec/Verbs.v:64-69, 124-127
   (instance_verb_formats, verb_is_m). The B twin of lib/A/Prog/is_instance_verb_c.v, re-derived on B's code
   (the disassembly of is_instance_verb): the same 61 instructions at B addresses, with B's table and literals.
   The function (L/src/verbs.c:48-56) asks whether a token names one of the 18 instance verbs: verb_is is inlined,
   so it computes strcspn(t, " \t") once, then walks g_instance_verbs (18 pointers, the const table at 0xa5d00 in
   the read-only range [CMD_RLO, CMD_RHI)) with strcspn(f, " ") and strncmp(t, f, n) per entry. It writes nothing
   outside its own frame and allocates nothing.

   Addresses (B, its disassembly): entry BASE + AF_is_instance_verb = 0x8e340. 61 instructions, frame 80
   bytes (`addi sp,sp,-80`, no realignment), one loop of 18 passes (header 0x8e3ac, counter s4 down by 8 to -144),
   one inline check: the 8-byte load of the table slot (shadow byte at (a >> 3) + SHADOW_OFF through the shadow-base
   GOT word 0xa5f50, 0x8e3ac; the error path, a call of `__asan_report_load8` at 0x8e430, is not reached: the
   table's shadow is usable by CmdRecFacts' cmd_addressable_chk). Two wrapper calls: strcspn (0x8e384, 0x8e3c0) and
   strncmp (0x8e3d4), `___interceptor_<f>` through the 4-byte jumps `__interceptor_trampoline_strcspn` 0x45198 and
   `__interceptor_trampoline_strncmp` 0x4518c. The table, the 18 format strings it points to and the two separator
   literals are conjuncts of cmd_ro_ok (lib/B/Prog/CmdRo.v: RO_g_instance_verbs; RO_lit_22520, RO_lit_22a60,
   RO_lit_22aa0, RO_lit_22ac0, RO_lit_22b00, RO_lit_22b20, RO_lit_22560, RO_lit_22b60, RO_lit_22b80, RO_lit_22ba0,
   RO_lit_22be0, RO_lit_22c20, RO_lit_22c60, RO_lit_22ca0, RO_lit_22d00, RO_lit_22d20, RO_lit_22d60, RO_lit_22da0;
   " \t" RO_lit_22500, " " RO_lit_22dc0).
   The token: its one caller, verbs_receive, passes its first word tok[0] (s10 at 0x8d830, jal at 0x8d834), a word
   of its strdup block `copy`, so it is a heap string, whose word tail is readable by cmd_heap_tail_vis. The
   stack-protector cells the musl body under the strcspn wrapper compares (GOT word 0xa6bf8, guard cell 0x604158)
   are cmd_rec_cells. It allocates nothing and takes no side-stack frame, so its post gives `ly' = ly /\ S' = S`
   (meter class (a)).
   UBSan: 0 trap sites (the trap-site table has no row for is_instance_verb). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdObj CmdRo CmdBase CmdRep.
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
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* the stack this call needs: its own 80-byte frame, and the window the strcspn and strncmp wrappers ask for
   (RtDefs.v's ecall_pre_stk segs B (2 * ESTACK), lib/B/Rt/RtString.v astrcspn_realizes / astrncmp_realizes).
   M: the image's function table gives 16464 *)
Definition IS_INSTANCE_VERB_STK : Z := 80 + 2 * ESTACK.
Definition EV_IS_INSTANCE_VERB : Z := 0.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the wrappers it calls: their contracts, at the listing's call targets. The span entries name B's musl GOT word
   0xa6bf8 and the guard cell 0x604158 the body they run compares against *)
Hypothesis STRCSPN : forall fx0 : YK11.FPState, @RtString.astrcspn_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_strcspn) 0xa6bf8 0x604158.
Hypothesis STRNCMP : forall fx0 : YK11.FPState, @RtString.astrncmp_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_strncmp).
(* `using MT`: the post has no meter conjunct (frame form), so MT is named here to keep the uniform signature
   tis_instance_verb_spec B MT *)
#[using="MT"]
Definition tis_instance_verb_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md (t : Z) (tb : list byte),
afn_pre_na SEGS B IS_INSTANCE_VERB_STK ly S W regs mem md ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
getr regs 10 = w64 t -> 0 <= t < 2 ^ 64 ->
(* the token: a heap string, verbs_receive's first word in its `copy` block *)
in_blockA (ablocks B ly S) t (Z.of_nat (length tb) + 1) -> astr_atR (rdW W mem) t tb ->
Z.of_nat (length tb) + 1 <= LMAX + 1 ->
(* the table, the strings it points to and the separator literals, and the bridge from the listing's object atoms
   to their addresses *)
cmd_ro_ok (rdW W mem) -> cmd_val_objs ->
st_nev S + EV_IS_INSTANCE_VERB <= EV_MAX ->
SRr SEGS W (cfg_at SEGS (BASE + AF_is_instance_verb) regs mem md)
(apost_base SEGS B IS_INSTANCE_VERB_STK [] regs ly S W mem md EV_IS_INSTANCE_VERB
(fun ly' S' W' regs' mem' md' =>
 getr regs' 10 = w64 (if existsb (Verbs.verb_is_m tb) Verbs.Lit.instance_verb_formats then 1 else 0) /\
 Permutation (ablocks B ly' S') (ablocks B ly S) /\
 (* it allocates nothing and takes no side-stack frame (meter class (a)) *)
 ly' = ly /\ S' = S)).
End e.
End f.
End d.
