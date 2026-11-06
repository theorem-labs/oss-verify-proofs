(* The contract of rec_calls_equal on the ASan build of plugin-hostd/fuzz_command.

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): afn_pre at the entry,
   SRr of apost_base at the return. Functional content: fuzz_command's own released plain contract
   lib/Prog/rec_calls_equal_c.v:11-69 (rc_entry, entry_at, calls_at; the result `calls_eqb ca cb`, :42-47, used as it
   is). rec_calls_equal(a, na, b, nb) (H/recorder.c:162-177) returns 0 when na <> nb; otherwise it compares, entry by
   entry, the function numbers and the argument counts, and each pair of arguments with the strcmp wrapper
   (`___interceptor_strcmp`, reached through the 4-byte jump `__interceptor_trampoline_strcmp`), and returns 1 when
   all agree. It writes nothing outside its own frame and allocates nothing (FP = [], no meter).

   Addresses: entry BASE + AF_rec_calls_equal = 0x89968 (M, the pinned image). 135 instructions, 2 loops (0x899dc,
   0x89a6c), no side-stack frame, 6 inline checks: load4 on a[i].fn, b[i].fn, a[i].nargs, b[i].nargs (0x899f4,
   0x89a08, 0x89a28, 0x89a3c) and load8 on a[i].args[k], b[i].args[k] (0x89a6c, 0x89a7c), each a read of the shadow
   byte at (a >> 3) + 0x7fff8000. The error path (a call of `__asan_report_load4` / `__asan_report_load8`) is not
   reached: each table lies in g_rec, in record.spill (shadow usable by `cmd_addressable_chk`) or in a side-stack
   frame object (rce_home). Every argument string is a live block: its one caller, check_round_trip (0x88294),
   hands it g_rec's table (acall_at puts every argument in a block) and first[], whose arguments are
   rec_calls_copy's fresh copies; the strcmp wrapper's reads come from AR's block facts and each tail word from
   `cmd_heap_tail_vis`. s0 holds a table address (0x899c4), below the stack, at the strcmp calls; no program
   call. It reaches no heap allocator and no side-stack frame: the post keeps ly and S. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require rec_calls_equal_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaNoChain.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Module PRce := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.rec_calls_equal_c.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
#[local] Notation PC_STRCMP := (@pa_sigma _ cmd_listing PI CS___interceptor_trampoline_strcmp).
(* the stack this call needs: its own 128-byte frame, and the window the strcmp wrapper asks for (RtString.v's
   astrcmp_realizes, ecall_pre_stk segs B (2 * ESTACK)) *)
Definition REC_CALLS_EQUAL_STK : Z := 128 + 2 * ESTACK.
Definition EV_REC_CALLS_EQUAL : Z := 0.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* where a table lies: in g_rec's call table, in record.spill (registered globals, shadow usable by
   `cmd_addressable_chk`), or in an object of a live side-stack frame (check_round_trip's first[]) *)
Definition rce_home (ly : alayout) (S : astate) (W : world SEGS) (mem : word -> option byte) (a n : Z) : Prop :=
(A_G_REC + OFF_CALLS <= a /\ a + n <= A_G_REC + REC_SIZE) \/
(A_REC_SPILL <= a /\ a + n <= A_REC_SPILL + SC_SIZE) \/
afobj SEGS B ly S W mem a n.
(* a table of recorded calls at a: the plain proof's calls_at / entry_at / arg_at (rec_calls_equal_c.v:15-30) over
   the reader, each argument a string inside a live block (every caller passes blocks). `a mod 8 = 0` is the B
   statement's conjunct (lib/B/Prog/rec_calls_equal_c.v:77, the UBSan traps 0x89fbc for a and 0x89ff4 for b of the
   asan-ubsan build, recorder.c:170), which rce_home does not give; it is carried here so that the A and B statements
   agree (this port's decision). The one caller, check_round_trip (0x88294), passes g_rec's table A_G_REC + OFF_CALLS
   and its frame object first[] (afobj) *)
Definition rce_calls (ly : alayout) (S : astate) (W : world SEGS) (mem : word -> option byte) (a : Z)
(cs : list PRce.rc_entry) : Prop :=
(length cs <= 16)%nat /\ a mod 8 = 0 /\
rce_home ly S W mem a (CALL_SIZE * Z.of_nat (length cs)) /\
forall i e, nth_error cs i = Some e ->
 -2^31 <= fst e < 2^31 /\ (length (snd e) <= 6)%nat /\
 aval_mem (rdW W mem) (a + CALL_SIZE * Z.of_nat i + CALL_OFF_FN) 4 (fst e) /\
 aval_mem (rdW W mem) (a + CALL_SIZE * Z.of_nat i + CALL_OFF_NARGS) 4 (Z.of_nat (length (snd e))) /\
 forall k p, nth_error (snd e) k = Some p ->
   aval_mem (rdW W mem) (a + CALL_SIZE * Z.of_nat i + CALL_OFF_ARGS + 8 * Z.of_nat k) 8 (bv_unsigned (fst p)) /\
   in_blockA (ablocks B ly S) (bv_unsigned (fst p)) (Z.of_nat (length (snd p)) + 1) /\
   astr_atR (rdW W mem) (bv_unsigned (fst p)) (snd p).
(* the runtime entry the call reaches *)
Hypothesis ASTRCMP : forall fx0 : YK11.FPState, @astrcmp_realizes fx0 rc SEGS B PC_STRCMP.
(* `using MT`: the post has no meter conjunct (frame form), so MT is named here to keep the uniform signature
   trec_calls_equal_spec B MT *)
#[using="MT"]
Definition trec_calls_equal_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md (a b : Z) (ca cb : list PRce.rc_entry),
afn_pre_na SEGS B REC_CALLS_EQUAL_STK ly S W regs mem md ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
getr regs 10 = w64 a -> getr regs 11 = w64 (Z.of_nat (length ca)) ->
getr regs 12 = w64 b -> getr regs 13 = w64 (Z.of_nat (length cb)) ->
rce_calls ly S W mem a ca -> rce_calls ly S W mem b cb ->
st_nev S + EV_REC_CALLS_EQUAL <= EV_MAX ->
SRr SEGS W (cfg_at SEGS (BASE + AF_rec_calls_equal) regs mem md)
(apost_base SEGS B REC_CALLS_EQUAL_STK [] regs ly S W mem md EV_REC_CALLS_EQUAL
(fun ly' S' W' regs' mem' md' =>
 (* 1 when the two tables hold the same calls, else 0 (plain rec_calls_equal_c.v:61) *)
 getr regs' 10 = w64 (if PRce.calls_eqb ca cb then 1 else 0) /\
 Permutation (ablocks B ly' S') (ablocks B ly S) /\
 (* no allocator and no side-stack frame: the layout and the allocator state are kept *)
 ly' = ly /\ S' = S)).
End e.
End f.
End d.
