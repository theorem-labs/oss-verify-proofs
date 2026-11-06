(* The contract of arg_i on the ASan build of plugin-hostd/fuzz_command.
   The post is FP-existential (apost_baseF, the printf wrappers' shared post); the pre carries rounding mode 0.
   The callees' contracts are taken at every FP state (forall fx0), so a walk can use them at the fx' a call returns.

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): afn_pre at the entry,
   SRr of apost_base at the return; the fresh block as cgif's trawnew_specX states it (lib/YC7x.v:93-101), the
   meter as there (:88, :92). Functional content: fuzz_command's own released plain contract
   lib/Prog/arg_i_c.v:25-64 (arg_i_ret :25-50: the two cases m = 6 and m < 6, nargs := m + 1, args[m] := p, p holds
   `dec v` and its terminator; the contract :52-64) and lib/Prog/RecFacts.v:76-77 (`dec`).
   arg_i(c, v) (recorder.c:235-241, arg_s inlined :223-227) prints v with snprintf(b, 16, "%d", v) into b[16] of its
   own side-stack frame, and when c->nargs < 6 appends xstrdup(b) to the call c. c is a slot of g_rec's call table
   or record.spill (every caller passes record()'s result, recorder.c:205-221).
   Dropped from the plain post on purpose (as the walk plan of arg_i says): the bytes of b (b is in the
   released side-stack frame) and `p mod 16 = 0`.

   Addresses: entry BASE + AF_arg_i = 0x8a238 (M, the pinned image). 144 instructions; 3 inline checks on the slot
   (load4 of c->nargs twice, store8 of c->args[m]; each reads the shadow byte at (a >> 3) + 0x7fff8000 of a byte
   of g_rec or record.spill, which the allocator record marks usable (CmdRecFacts' cmd_addressable_chk), so the
   error path, a call of
   `__asan_report_*`, is not reached); a side-stack frame of class 0 (`__asan_stack_malloc_0`, request 64 bytes,
   released inline: shadow 0xf5 and the flag byte); the real-stack fallback and its one-pass probe loop are not
   taken (this port's decision: the use-after-return flag is pinned by the allocator record); callees: the snprintf
   wrapper, xstrdup. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import xstrdup_c.
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
(* the stack this call needs: its own 96-byte frame, 16 more for the realignment `andi sp,sp,-32` (sp mod 16 = 0 at
   the entry, afn_pre's astk_ok; callers enter with sp = 0 or 16 mod 32, a cross-check of arg_i's walk plan),
   and the deepest callee: the side-stack entry's window (ESTACK), the snprintf wrapper's (3 * ESTACK, the
   measured 6,672 bytes below the trampoline's entry sp), xstrdup's own need *)
Definition ARG_I_STK : Z := 96 + 16 + Z.max ESTACK (Z.max (3 * ESTACK) XSTRDUP_STK).
(* one allocator event: the malloc inside xstrdup (none when c->nargs = 6); the side-stack frame spends none *)
Definition EV_ARG_I : Z := EV_XSTRDUP.
(* the live bytes the call adds: the copy of dec v, at most 12 bytes *)
Definition LIVE_ARG_I (v : Z) : Z := LIVE_XSTRDUP (dec v).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the meter the call spends: xstrdup's copy of dec v *)
Definition XM_ARG_I (v : Z) : Z := XM_XSTRDUP MT (dec v).
(* the callee's contract, the runtime entries with this tree's and cgif's names, and the bridge for the "%d" format's
   address *)
Hypothesis TXSTRDUP : forall fx0 : YK11.FPState, @txstrdup_spec fx0 rc SK PI B MT.
Hypothesis ASTACK_MALLOC0 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 0.
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState, @asnprintf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_snprintf) 0xa7098 0x6045d8.
Hypothesis VOBJS : cmd_val_objs.
Definition targ_i_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (c v m : Z),
afn_pre SEGS B ARG_I_STK ly S W regs mem md ch ->
(* rounding mode 0 (frm = fcsr bits 5..7): the printf wrappers' frm0_entry; apost_baseF gives it back after a call *)
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
(* room for one more side-stack frame of class 0 (count_cid 0 < fs_frames 0) *)
Z.of_nat (length (frames S)) <= 8 ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
(* the read-only bytes of the image; the format "%d" is RO_lit_21f00 (its tail: cmd_tail_vis; its shadow:
   cmd_aread_ok_chk). The stack-protector GOT word and guard cell that musl's printf chain behind the snprintf
   wrapper checks are CmdRecFacts' cmd_rec_cells. *)
cmd_ro_ok (rdW W mem) ->
getr regs 10 = w64 c -> getr regs 11 = w64 v -> -2 ^ 31 <= v < 2 ^ 31 ->
(* c is a slot of g_rec's call table or record.spill: program globals whose shadow is usable
   (cmd_addressable_chk), so the three checks pass *)
((exists i, 0 <= i < REC_CALLS_MAX /\ c = A_G_REC + OFF_CALLS + CALL_SIZE * i) \/ c = A_REC_SPILL) ->
aval_mem (rdW W mem) (c + CALL_OFF_NARGS) 4 m -> 0 <= m <= REC_ARGS_MAX ->
st_nev S + EV_ARG_I <= EV_MAX -> blocks_bytes S + LIVE_ARG_I v <= LIVE_MAX ->
mo_ok MT S (XM_ARG_I v) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_arg_i) regs mem md)
(apost_baseF SEGS B ARG_I_STK
 (* it writes c->nargs and c->args[m], and only when m < 6 *)
 (if m <? REC_ARGS_MAX
  then [(c + CALL_OFF_NARGS, c + CALL_OFF_NARGS + 4); (c + CALL_OFF_ARGS + 8 * m, c + CALL_OFF_ARGS + 8 * m + 8)]
  else [])
 regs ly S W mem md EV_ARG_I
(fun ly' S' W' regs' mem' md' =>
 blocks_bytes S' <= blocks_bytes S + LIVE_ARG_I v /\
 mo_le MT S S' (XM_ARG_I v) /\
 ((m = REC_ARGS_MAX /\ Permutation (ablocks B ly' S') (ablocks B ly S)) \/
  (m < REC_ARGS_MAX /\ exists p,
    let n := Z.of_nat (length (dec v)) + 1 in
    4096 <= p < 2 ^ 64 /\
    Permutation (ablocks B ly' S') ((p, n) :: ablocks B ly S) /\
    Forall (fun qk => iv_apart p n (fst qk) (snd qk)) (ablocks B ly S) /\
    aval_mem (rdW W' mem') (c + CALL_OFF_NARGS) 4 (m + 1) /\
    aval_mem (rdW W' mem') (c + CALL_OFF_ARGS + 8 * m) 8 p /\
    astr_atR (rdW W' mem') p (dec v))))).
End e.
End f.
End d.
