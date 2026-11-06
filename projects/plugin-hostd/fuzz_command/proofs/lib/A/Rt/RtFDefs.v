(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the contracts of the format entries that plugin-hostd/fuzz_command calls and cgif_file_fuzzer does not (snprintf, sprintf), in the form cgif_file_fuzzer's lib/YG0d.v states its interceptor contracts; the text they write is the one fuzz_command's own plain proof states for musl's printf core (lib/Prog/printf_facts_c.v), with its argument premise restated over the asan view of memory. *)
(* Modified by Theorem Labs, 2026-10: the contracts the walks of plugin-hostd/fuzz_command's snprintf and sprintf entries hand to each other (the va_list form of RtFormat.v's asnprintf_realizes, for the vsnprintf interceptor and for musl's vsnprintf, and ASan's printf_common over the pf_parse language), in the form RtFormat.v states its entry contracts. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require printf_facts_c.
Import ListNotations.
Open Scope Z_scope.

(* Program counters on the pinned image (objdump, nm). *)
Definition PC_vsnprintf_tramp : Z := 0x45178.  (* one j to ___interceptor_vsnprintf 0x49858 *)
Definition PC_vsnprintf_icpt : Z := 0x49858.
Definition PC_vsprintf_icpt : Z := 0x49b70.
Definition PC_vfprintf_tramp : Z := 0x45174.   (* one j to ___interceptor_vfprintf 0x497a4 *)
Definition PC_vfprintf_icpt : Z := 0x497a4.
Definition PC_printf_common : Z := 0x48cdc.
Definition PC_musl_vsnprintf : Z := 0x9e490.  (* REAL(vsnprintf), slot 0xa8198 *)
Definition PC_musl_vsprintf : Z := 0x9e638.   (* REAL(vsprintf), slot 0xa81a0: 5 instructions, j 0x45178 *)
Definition PC_musl_vfprintf : Z := 0x9b364.   (* REAL(vfprintf), slot 0xa8190 *)

(* Scratch windows. A caller that uses a callee's contract gives the callee its whole stated window, so the windows
   compose by frame + callee window, with these frames (prologue addi sp of each function, objdump):
   ___interceptor_snprintf 96, ___interceptor_sprintf 80, ___interceptor_vsnprintf 2,160,
   ___interceptor_vsprintf 2,160, printf_common 2,240, musl vsprintf 0 (tail jump), and the range check
   __asan_region_is_poisoned with its ESTACK contract (RtString.v).
     printf_common:            2,240 + ESTACK (range check)                         = 6,336 <= PCOM_STK 6,400
     vsnprintf interceptor:    2,160 + max (PCOM_STK, MUSL_VSN_STK, ESTACK)         = 9,968 <= VSN_ICPT_STK 9,984
     snprintf entry:              96 + VSN_ICPT_STK                                 = 10,080 <= 3 * ESTACK
     sprintf entry:               80 + 2,160 + 0 + VSN_ICPT_STK                     = 12,224 <= 3 * ESTACK
   MUSL_VSN_STK is the largest window the sprintf entry leaves for musl's vsnprintf: 12,288 - 80 - 2,160 - 2,160 =
   7,888, rounded down to 16. The measured depth below musl vsnprintf's entry is 3,808 bytes (4,352 with fmt_fp,
   which pf_parse makes unreachable), so the window has room; but a proof of musl's body that uses the donor's
   strnlen interceptor contract (YG0d.v astrnlen_realizes, 2 * ESTACK) at printf_core's %s call needs
   304 + 48 + 368 + 544 + 8,192 = 9,456 bytes, more than 7,808: that proof needs a strnlen interceptor contract
   with a window of at most 6,544 bytes. *)
Definition PCOM_STK : Z := 6400.
Definition MUSL_VSN_STK : Z := 7808.
Definition VSN_ICPT_STK : Z := 9984.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section c.
Variable segs : list Segment.
Variable B : asyms.

Local Notation PRE stk := (ecall_pre_stk segs B stk).
Local Notation RD stk := (aread_ok segs stk).
Local Notation WR stk := (awrite_ok segs B stk).
Local Notation STR := (astr_at segs).
Local Notation POST stk := (art_post segs B stk).

(* A va_list: [rs] are the 8-byte argument slots at [ap], readable, and outside the callee's scratch window. The
   snprintf and sprintf interceptors spill a3..a7 (a2..a7) into their own frames and pass the address of the first
   slot; every callee below reads the slots and writes none. *)
Definition aslots_ok (stk : Z) (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte)
(ap : Z) (rs : list word) : Prop :=
0 <= ap /\ ap + 8 * Z.of_nat (length rs) <= 2 ^ 63 /\
(forall i, (i < length rs)%nat ->
rdword (aview segs (w_H W) mem) (ap + 8 * Z.of_nat i) = Some (bv_unsigned (nth i rs (w64 0)))) /\
(forall a, ap <= a < ap + 8 * Z.of_nat (length rs) -> ~ ascratch_stk stk regs a).

(* vsnprintf(d, n, fmt, ap): the va_list form of asnprintf_realizes, with the window as a parameter. It writes
   w = min (n, |T| + 1) bytes, so sprintf's call (musl vsprintf passes n = 0x7fffffff) asks for the written prefix
   only, as asprintf_realizes does. *)
Definition avsnprintf_realizes (stk pc gotw guard : Z) : Prop :=
forall ly S W regs mem md d n f ap fmt ps args T rs,
let w := Z.min n (Z.of_nat (length T) + 1) in
aguard_ok segs W mem gotw guard ->
PRE stk ly S W regs mem md ->
getr regs 10 = w64 d -> getr regs 11 = w64 n -> getr regs 12 = w64 f -> getr regs 13 = w64 ap ->
1 <= n < 2 ^ 31 -> 0 < d -> 0 < f ->
STR W mem f (PF.pf_bytes fmt) ->
PF.pf_parse fmt = Some ps -> PF.pf_text ps args = Some T ->
Z.of_nat (length T) < 2 ^ 31 - 1 ->
RD stk W regs mem f (Z.of_nat (length fmt) + 1) ->
atail_vis segs W mem (f + Z.of_nat (length fmt)) ->
aslots_ok stk W regs mem ap rs ->
(ap + 8 * Z.of_nat (length rs) <= d \/ d + w <= ap) ->
apf_args_ok segs stk W regs mem d w rs args ->
WR stk ly S W regs mem d w ->
rt_rom_view segs B W mem ->
SRr segs W (cfg_at segs pc regs mem md)
(POST stk ly S W regs mem md (fun a => d <= a < d + w)
(fun regs' mem' => getr regs' 10 = w64 (Z.of_nat (length T)) /\
abytes_at segs W mem' d (PF.pf_bytes (firstn (Z.to_nat (n - 1)) T ++ [0])))).

(* ASan's printf_common(ctx, fmt, aq), check_printf on (common flag +84 = 1, a record cell): it walks the format
   and checks the reads of every %s / %.*s argument. It writes only its scratch window. [D] and [N] are any
   range the arguments keep away from (the destination of the caller). *)
Definition apcommon_realizes (pc : Z) : Prop :=
forall ly S W regs mem md f ap fmt ps args T rs D N,
PRE PCOM_STK ly S W regs mem md ->
getr regs 11 = w64 f -> getr regs 12 = w64 ap -> 0 < f ->
STR W mem f (PF.pf_bytes fmt) ->
PF.pf_parse fmt = Some ps -> PF.pf_text ps args = Some T ->
RD PCOM_STK W regs mem f (Z.of_nat (length fmt) + 1) ->
atail_vis segs W mem (f + Z.of_nat (length fmt)) ->
aslots_ok PCOM_STK W regs mem ap rs ->
apf_args_ok segs PCOM_STK W regs mem D N rs args ->
rt_rom_view segs B W mem ->
SRr segs W (cfg_at segs pc regs mem md)
(POST PCOM_STK ly S W regs mem md (fun _ => False) (fun _ _ => True)).

End c.
End b.
