(* The contract of arg_line on the ASan build of plugin-hostd/fuzz_command.
   The callees' contracts are taken at every FP state (forall fx0), so a walk can use them at the fx' a call returns.

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): afn_pre at the entry,
   SRr of apost_base at the return; the fresh block as cgif's trawnew_specX states it (lib/YC7x.v:93-101), the
   meter as there (:88, :92). Functional content: fuzz_command's own released plain contract
   lib/Prog/arg_line_c.v:25-67 (arg_line_ret :25-49: the two cases m = 6 and m < 6, nargs := m + 1, args[m] := p,
   a block of |T| + 1 bytes that holds `canon T` and its terminator; the contract :51-67) and
   lib/Prog/RecFacts.v:154 (`canon`).
   arg_line(c, line) (recorder.c:229-233) appends rec_canonical(line, strlen(line)) to the call c when
   c->nargs < 6. c is a slot of g_rec's call table or record.spill (every caller passes record()'s result).

   Addresses: entry BASE + AF_arg_line = 0x8aa68 (M, the pinned image). 58 instructions, no loop, no side-stack
   frame; 3 inline checks on the slot (load4 of c->nargs twice, store8 of c->args[m]; each reads the shadow byte at
   (a >> 3) + 0x7fff8000 of a byte of g_rec or record.spill, which the allocator record marks usable (CmdRecFacts'
   cmd_addressable_chk), so the error
   path, a call of `__asan_report_*`, is not reached); callees: the strlen wrapper (`___interceptor_strlen`,
   reached through the 4-byte jump `__interceptor_trampoline_strlen`), rec_canonical. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import rec_canonical_c.
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
(* the stack this call needs: its own 48-byte frame (no realignment), and the deeper of the strlen wrapper's window
   (ESTACK, RtString.v astrlen_realizes) and rec_canonical's own need *)
Definition ARG_LINE_STK : Z := 48 + Z.max ESTACK REC_CANONICAL_STK.
(* one allocator event: the malloc inside rec_canonical (none when c->nargs = 6) *)
Definition EV_ARG_LINE : Z := EV_REC_CANONICAL.
(* the live bytes the call adds: rec_canonical's block of |T| + 1 bytes *)
Definition LIVE_ARG_LINE (T : list byte) : Z := LIVE_REC_CANONICAL T.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the meter the call spends: rec_canonical's malloc *)
Definition XM_ARG_LINE (T : list byte) : Z := XM_REC_CANONICAL MT T.
(* the callee's contract and the runtime entry, with this tree's name *)
Hypothesis TREC_CANONICAL : forall fx0 : YK11.FPState, @trec_canonical_spec fx0 rc SK PI B MT.
Hypothesis ASTRLEN : forall fx0 : YK11.FPState, @astrlen_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strlen).
Definition targ_line_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (c pl m : Z) (T : list byte),
afn_pre SEGS B ARG_LINE_STK ly S W regs mem md ch ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
getr regs 10 = w64 c -> getr regs 11 = w64 pl -> 0 <= pl < 2 ^ 64 ->
(* c is a slot of g_rec's call table or record.spill: program globals whose shadow is usable
   (cmd_addressable_chk), so the three checks pass *)
((exists i, 0 <= i < REC_CALLS_MAX /\ c = A_G_REC + OFF_CALLS + CALL_SIZE * i) \/ c = A_REC_SPILL) ->
aval_mem (rdW W mem) (c + CALL_OFF_NARGS) 4 m -> 0 <= m <= REC_ARGS_MAX ->
(* the line: a string of at most LMAX bytes inside a live block (plain arg_line_c.v:58-62). Every caller (sup_call,
   sup_connect, sup_broadcast, sup_host_setting, sup_instance_verb) passes its own line, which verbs_receive takes
   from its strndup block (verbs.c:219), so the block form, not astr_argA. The strlen wrapper reads
   the bytes and the tail word after the terminator: CmdRecFacts' cmd_heap_tail_vis gives that tail from the block.
   arg_line frees nothing, so no block is excluded *)
in_blockA (ablocks B ly S) pl (Z.of_nat (length T) + 1) -> astr_atR (rdW W mem) pl T ->
Z.of_nat (length T) + 1 <= LMAX + 1 ->
st_nev S + EV_ARG_LINE <= EV_MAX -> blocks_bytes S + LIVE_ARG_LINE T <= LIVE_MAX ->
mo_ok MT S (XM_ARG_LINE T) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_arg_line) regs mem md)
(apost_base SEGS B ARG_LINE_STK
 (* it writes c->nargs and c->args[m], and only when m < 6 *)
 (if m <? REC_ARGS_MAX
  then [(c + CALL_OFF_NARGS, c + CALL_OFF_NARGS + 4); (c + CALL_OFF_ARGS + 8 * m, c + CALL_OFF_ARGS + 8 * m + 8)]
  else [])
 regs ly S W mem md EV_ARG_LINE
(fun ly' S' W' regs' mem' md' =>
 blocks_bytes S' <= blocks_bytes S + LIVE_ARG_LINE T /\
 mo_le MT S S' (XM_ARG_LINE T) /\
 ((m = REC_ARGS_MAX /\ Permutation (ablocks B ly' S') (ablocks B ly S)) \/
  (m < REC_ARGS_MAX /\ exists p,
    let n := Z.of_nat (length T) + 1 in
    4096 <= p < 2 ^ 64 /\
    Permutation (ablocks B ly' S') ((p, n) :: ablocks B ly S) /\
    Forall (fun qk => iv_apart p n (fst qk) (snd qk)) (ablocks B ly S) /\
    aval_mem (rdW W' mem') (c + CALL_OFF_NARGS) 4 (m + 1) /\
    aval_mem (rdW W' mem') (c + CALL_OFF_ARGS + 8 * m) 8 p /\
    astr_atR (rdW W' mem') p (canon T))))).
End e.
End f.
End d.
