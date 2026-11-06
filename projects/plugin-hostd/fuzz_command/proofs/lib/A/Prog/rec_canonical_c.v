(* The contract of rec_canonical on the ASan build of plugin-hostd/fuzz_command.

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): afn_pre at the entry,
   SRr of apost_base at the return; the fresh block as cgif's trawnew_specX states it (lib/YC7x.v:93-101), the meter
   as there (:88, :92). Functional content: fuzz_command's own released plain contract lib/Prog/rec_canonical_c.v:24-52
   and its model lib/Prog/RecFacts.v (canon = join_sp (words T): the words of the line, joined by one space).
   rec_canonical(text, len) (H/recorder.c:104-122, xmalloc inlined) allocates len + 1 bytes through the malloc
   wrapper, then copies the words of text[0..len) into the block, one space between two words, and a terminator.
   The malloc rule returns a block at or above 4096, so the abort edge (`__asan_handle_no_return`, then abort) on a
   null result is not taken.

   Addresses: entry BASE + AF_rec_canonical = 0x89300 (M, the pinned image). 117 instructions, 3 loops (0x89354,
   0x89364, 0x893e8), no side-stack frame, 5 inline checks: load1 on text[i] (0x89370, 0x893f0) and store1 on out[o]
   (0x893b4, 0x8940c, 0x89480), each a read of the shadow byte at (a >> 3) + 0x7fff8000. The error path (a call of
   `__asan_report_load1` / `__asan_report_store1`) is not reached: text lies in a live block (its one caller,
   arg_line, passes verbs_receive's strndup line), and out[o] lies in the fresh block of len + 1 bytes, because
   o <= |canon T| <= len. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep.
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
(* the stack this call needs: its own 32-byte frame, and the window the malloc wrapper asks for (ASTACK, cgif
   lib/YG0d.v:17; amalloc04_rule asks ASTACK - o <= STK, lib/YC5d.v:60) *)
Definition REC_CANONICAL_STK : Z := 32 + ASTACK.
(* one allocator event: the malloc *)
Definition EV_REC_CANONICAL : Z := 1.
(* the live bytes the call adds: the block of len + 1 bytes *)
Definition LIVE_REC_CANONICAL (T : list byte) : Z := Z.of_nat (length T) + 1.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the meter the call spends: one malloc of len + 1 bytes *)
Definition XM_REC_CANONICAL (T : list byte) : Z := mo_malloc MT (Z.of_nat (length T) + 1).
(* the runtime entry the call reaches *)
Hypothesis AMALLOC4 : forall fx0 : YK11.FPState, @amalloc04_rule fx0 rc SK SEGS B MT.
Definition trec_canonical_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (text : Z) (T : list byte),
afn_pre SEGS B REC_CANONICAL_STK ly S W regs mem md ch ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
getr regs 10 = w64 text -> 0 <= text < 2 ^ 64 -> getr regs 11 = w64 (Z.of_nat (length T)) ->
(* the line: its len bytes hold no NUL and len <= LMAX (plain rec_canonical_c.v:44-46); arg_line, the one caller,
   hands over a NUL-terminated string inside a live block (its own block-form premise), so the block form, not
   astr_argA. The text is read byte by byte inline, so no tail word is read *)
in_blockA (ablocks B ly S) text (Z.of_nat (length T) + 1) -> astr_atR (rdW W mem) text T ->
Z.of_nat (length T) + 1 <= LMAX + 1 ->
st_nev S + EV_REC_CANONICAL <= EV_MAX -> blocks_bytes S + LIVE_REC_CANONICAL T <= LIVE_MAX ->
mo_ok MT S (XM_REC_CANONICAL T) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_rec_canonical) regs mem md)
(apost_base SEGS B REC_CANONICAL_STK [] regs ly S W mem md EV_REC_CANONICAL
(fun ly' S' W' regs' mem' md' => exists p : Z,
 getr regs' 10 = w64 p /\ 4096 <= p < 2 ^ 64 /\
 (* a fresh block, apart from every block that was live (plain rec_canonical_c.v:30-31) *)
 Permutation (ablocks B ly' S') ((p, LIVE_REC_CANONICAL T) :: ablocks B ly S) /\
 Forall (fun qk => iv_apart p (LIVE_REC_CANONICAL T) (fst qk) (snd qk)) (ablocks B ly S) /\
 (* it holds the canonical line and its terminator, and the line is kept (plain rec_canonical_c.v:34-35) *)
 abytes_atR (rdW W' mem') p (canon T ++ [Z_to_bv 8 0]) /\ abytes_atR (rdW W' mem') text T /\
 blocks_bytes S' <= blocks_bytes S + LIVE_REC_CANONICAL T /\
 mo_le MT S S' (XM_REC_CANONICAL T))).
End e.
End f.
End d.
