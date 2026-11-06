(* The contract of check_words_pin_set on the ASan build of plugin-hostd/fuzz_command.

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): afn_pre at the entry,
   SRr of apost_base at the return. Functional content: fuzz_command's own released plain contract
   lib/Prog/check_words_pin_set_c.v:16-31 and its model lib/Prog/CommandModel.v (pin_verdict, S_DASH, S_VERDICT).
   The function checks that the pin_set call the recorder kept carries the verdict the harness computed from the
   message, and calls abort() if it does not; the pre-condition `x3 = pin_verdict r w4` is what the caller
   (check_words) has already established, so the abort edge is not taken.

   Addresses: entry BASE + AF_check_words_pin_set = 0x89020 (M, the pinned image). 58 instructions, 3 inline
   checks, no loop, two wrapper calls (strcmp, strncmp). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
(* the released plain contract defines pin_verdict (lib/Prog/check_words_pin_set_c.v:12-14); its module shares
   this file's base name, so it is named by its full path *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require check_words_pin_set_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable CmdSyms CmdList CmdAddr CmdPa CmdBase CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
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
(* the stack this call needs: its own 32-byte frame, and the window the strcmp and strncmp wrappers ask for
   (ecall_pre_stk segs B (2 * ESTACK), lib/A/Rt/RtDefs.v, after cgif's abcmp_realizes, lib/YG0d.v:355) *)
Definition CWPS_STK : Z := 32 + 2 * ESTACK.
Definition EV_CWPS : Z := 0.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
#[using="MT"]
Definition tcwps_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md (cp wp r nargs p4 p3 : Z) (w4 x3 : list byte),
afn_pre_na SEGS B CWPS_STK ly S W regs mem md ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
(* the two literals it compares against, "-" 0x21ac0 and "verdict=" 0x21b60, and the bridge from the listing's
   object atoms to those addresses *)
cmd_ro_ok (rdW W mem) -> cmd_val_objs ->
getr regs 10 = w64 cp -> getr regs 11 = w64 wp -> getr regs 12 = w64 r ->
0 <= r <= 64 ->
(* the recorded call sits inside the recorder's object g_rec. Its bytes are marked usable by the allocator
   invariant itself (g_rec is one of `as_zero_shadow B`, and AR's zshadow_ok gives the shadow bytes), so the two
   inline checks at cp + 4 and cp + 32 need no premise beyond the address range. *)
A_G_REC + OFF_CALLS <= cp -> cp + CALL_SIZE <= A_G_REC + REC_SIZE ->
(* call is 8-aligned: the B statement's premise (lib/B/Prog/check_words_pin_set_c.v:94, the UBSan trap 0x8955c of
   the asan-ubsan build, the alignment of call for call->nargs), carried here so that the A and B statements agree
   (this port's decision). The caller check_words passes &g_rec.calls[c] = A_G_REC + OFF_CALLS + CALL_SIZE * c, a
   multiple of 8 *)
cp mod 8 = 0 ->
aval_mem (rdW W mem) (cp + CALL_OFF_NARGS) 4 nargs -> 0 <= nargs <= 6 ->
(* its fourth argument: a string the recorder copied into a live block (acall_at puts every argument in a block,
   CmdRep.v; the plain contract's call_at, lib/Prog/RecInv.v:42-50) *)
(nargs = 4 ->
 aval_mem (rdW W mem) (cp + CALL_OFF_ARGS + 24) 8 p3 /\ 0 <= p3 < 2 ^ 64 /\
 in_blockA (ablocks B ly S) p3 (Z.of_nat (length x3) + 1) /\ astr_atR (rdW W mem) p3 x3) ->
(* the harness's word list, in the heap array w->w (fuzz_command.c:121, A6): the fifth word's pointer slot lies in
   that live block, which also keeps it apart from this call's own frame and from g_rec (the plain contract's
   word_slot, lib/Prog/check_words_pin_set_c.v:23), and the word itself inside the `copy` block *)
(4 < r ->
 in_blockA (ablocks B ly S) (wp + 32) 8 /\
 range_addressable (rdW W mem) SHADOW_OFF (wp + 32) 8 /\
 aval_mem (rdW W mem) (wp + 32) 8 p4 /\ 0 <= p4 < 2 ^ 64 /\
 in_blockA (ablocks B ly S) p4 (Z.of_nat (length w4) + 1) /\ astr_atR (rdW W mem) p4 w4) ->
(* w is 8-aligned: the B statement's premise (lib/B/Prog/check_words_pin_set_c.v:113, the UBSan trap 0x8950c of the
   asan-ubsan build, the 8-byte load w[4]), carried here so that the A and B statements agree (this port's decision).
   w->w is a malloc block start (AR_blocks_law: mod 16 = 0); the caller check_words passes it as it read it, with
   its own `arr mod 8 = 0` *)
wp mod 8 = 0 ->
(* what the caller has checked: the recorded verdict is the one the message asks for *)
nargs = 4 -> x3 = OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.check_words_pin_set_c.pin_verdict r w4 ->
st_nev S + EV_CWPS <= EV_MAX ->
SRr SEGS W (cfg_at SEGS (BASE + AF_check_words_pin_set) regs mem md)
(apost_base SEGS B CWPS_STK [] regs ly S W mem md EV_CWPS
(fun ly' S' W' regs' mem' md' => ly' = ly /\ S' = S)).
End e.
End f.
End d.
