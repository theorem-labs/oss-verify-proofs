(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: no trace premise, as the trace-store change of this port removes it from the rules of a call of malloc and free. *)
(* Modified by Theorem Labs, 2026-10: the rule a program walk uses at a call of an allocating string entry (strdup, strndup) of plugin-hostd/fuzz_command, in the shape cgif_file_fuzzer's amalloc04_rule has (lib/YC5d.v:56-74), with the copied bytes added and the string premises of the entry; module names. *)
(* Modified by Theorem Labs, 2026-10: copied from lib/A/Rt/RtAlloc04.v for fuzz_command.asan-ubsan: module paths. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI08 YN3v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtAlloc.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require StrFun.
Import ListNotations.
Local Open Scope Z_scope.

Module PStrFun := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec.StrFun.

(* A program walk does not use a runtime contract directly: it uses the rule of the call, which carries the
   journal of the call site, the stack offset, the footprint and the meter. cgif_file_fuzzer states that rule for
   malloc and free (lib/YC5d.v:56-116) and closes it from the contract and the model laws (lib/YCbp.v:29-43).
   fuzz_command calls two entries that allocate and are not malloc, so each needs its own rule of the same shape;
   the entry contract behind it is lib/B/Rt/RtAlloc.v. The extra conclusion is the bytes of the copy, and the extra
   premises are the ones the entry reads its argument under. *)

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable segs : list Segment.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.

(* strdup(x): one allocation of |s| + 1 bytes, holding the string and its terminator.
   [pc] is the trampoline the program calls; [pc_ra0] is the program counter the entry gives the unwinder. *)
Definition astrdup04_rule (pc pc_ra0 : Z) : Prop :=
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x s (o : Z) raw ch,
let n := astr_len s + 1 in
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 x -> 0 < x ->
astr_atR (aview segs (w_H W) memT) x s ->
aread_ok segs ASTACK W regsT memT x n ->
(forall a, x <= a < x + n -> adup_src_kept segs B lyc Sc a) ->
rt_rom_view segs B W memT ->
0 <= n < MALLOC_MAX -> blocks_bytes Sc + n <= LIVE_MAX ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
st_nev Sc < EV_MAX ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
mo_ok MT Sc (mo_malloc MT n) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal segs B STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + 1) /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
4096 <= res /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] /\
acall_kept segs B lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => res <= a < res + req_size n) /\
abytes_atR (aview segs (w_H W2) mem2) res (s ++ [Z_to_bv 8 0]) /\
mo_le MT Sc S2 (mo_malloc MT n)).

(* strndup(x, m): the argument is a buffer of m bytes which need not hold a terminator; the entry allocates
   strnlen_res m buf + 1 bytes and copies that prefix and a terminator. *)
Definition astrndup04_rule (pc pc_ra0 : Z) : Prop :=
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x m buf (o : Z) raw ch,
let kk := PStrFun.strnlen_res m buf in
let n := kk + 1 in
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 x -> getr regsT 11 = w64 m -> 0 <= m < 2 ^ 32 -> 0 < x ->
abytes_atR (aview segs (w_H W) memT) x buf ->
PStrFun.memchr_ok x 0 m buf ->
aread_ok segs ASTACK W regsT memT x (Z.min n (Z.of_nat (length buf))) ->
(exists p mm, In (p, mm) (ablocks B lyc Sc) /\ p <= x /\ x + Z.min n (Z.of_nat (length buf)) <= p + req_size mm) ->
~ (exists a, x <= a < x + Z.min n (Z.of_nat (length buf)) /\ aerrno_cell B a) ->
rt_rom_view segs B W memT ->
0 <= n < MALLOC_MAX -> blocks_bytes Sc + n <= LIVE_MAX ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
st_nev Sc < EV_MAX ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
mo_ok MT Sc (mo_malloc MT n) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal segs B STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + 1) /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
4096 <= res /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] /\
acall_kept segs B lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => res <= a < res + req_size n) /\
abytes_atR (aview segs (w_H W2) mem2) res (firstn (Z.to_nat kk) buf ++ [Z_to_bv 8 0]) /\
mo_le MT Sc S2 (mo_malloc MT n)).

End e.
End d.
End b.
