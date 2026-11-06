(* The contract of sup_reply_code on the ASan build of plugin-hostd/fuzz_command.

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): afn_pre at the entry,
   SRr of apost_base at the return. Functional content: fuzz_command's own released plain contract
   lib/Prog/sup_reply_code_c.v:33-36, :52 (reply_code: the "resp " prefix test, then the number after it, else -999),
   with the value of the ASan atoi wrapper in place of musl's atoi.
   The function (recorder.c:287-290) compares the string with "resp " through the strncmp wrapper
   (`___interceptor_strncmp`, reached through the 4-byte jump `__interceptor_trampoline_strncmp`). When the five
   bytes agree it pops its frame and jumps to the atoi wrapper (`__interceptor_trampoline_atoi`) on the rest of the
   string (a tail jump, 0x89db8); else it returns -999.

   The atoi wrapper is not musl's atoi: it calls musl's strtol with base 10, which saturates at the range of a signed
   long, and truncates the result to int (aatoi_realizes, lib/A/Rt/RtNumber.v, value
   bv_swrap 32 (s10_val str)). So this contract states `reply_code_a`, the plain reply_code with that value
   (this port's decision: an ASan statement states the wrapper's value). reply_code_a and the plain reply_code agree
   whenever the number after "resp " lies in [-2^63, 2^63) (`__intscan_c.s10_inrange`, lib/Prog/__intscan_c.v:37),
   which holds for every string of at most 18 digits after the prefix; a caller that needs the plain value applies
   that bridge.

   The wrapper writes errno (aerrno_cell, lib/A/Rt/RtDefs.v); the journal of apost_base leaves the errno cell free
   (cgif lib/YCbq.v:360). The cells the atoi wrapper reads besides the string are facts of the allocator record,
   not premises: the runtime's replace_str flag byte 0xae8d5 is 1 (which makes the atoi wrapper call strtol), the
   errno cell is readable, and the stack guard holds (aguard_ok as RtDefs states it: the GOT word 0xa7098 holds
   0x6045d8 and the guard cell there is readable) all come from CmdRecFacts' cmd_rec_cells. What the strncmp
   wrapper asks of the literal "resp " (aread_ok, the bytes after its terminator) comes from cmd_aread_ok_chk and
   cmd_tail_vis.

   Addresses: entry BASE + AF_sup_reply_code = 0x89d6c (M, the pinned image). 20 instructions, no inline check,
   no loop, no side-stack frame. The literal "resp " is .str.2 at 0x21d20 (6 bytes, a registered global, M:
   asan_globals descriptor); its bytes are RO_lit_21d20 of cmd_ro_ok (lib/A/Prog/CmdRo.v), the plain proof's
   resp_lit_bytes (lib/Prog/sup_reply_code_c.v:12). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString RtNumber RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require __intscan_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep
  CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaNoChain.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* the ASan atoi wrapper's value (aatoi_realizes, lib/A/Rt/RtNumber.v) *)
Definition atoi_a (s : list byte) : Z := bv_swrap 32 (__intscan_c.s10_val s).
(* the plain reply_code (lib/Prog/sup_reply_code_c.v:33-36) with that value *)
Definition reply_code_a (x : list byte) : Z :=
  if list_eq_dec Z.eq_dec (map bv_unsigned (firstn 5 x)) [114; 101; 115; 112; 32]
  then atoi_a (skipn 5 x)
  else -999.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* the stack this call needs: its own 16-byte frame with the strncmp wrapper's window below it (RtDefs.v's
   ecall_pre_stk segs B (2 * ESTACK)), or the atoi wrapper's window 3 * ESTACK (RtNumber.v's aatoi_realizes), which
   starts at the entry sp because the jump to it comes after the frame is popped (0x89da8-0x89db8) *)
Definition SUP_REPLY_CODE_STK : Z := Z.max (16 + 2 * ESTACK) (3 * ESTACK).
Definition EV_SUP_REPLY_CODE : Z := 0.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the runtime entries the call reaches, with this tree's names *)
Hypothesis ASTRNCMP : forall fx0 : YK11.FPState, @astrncmp_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strncmp).
Hypothesis AATOI : forall fx0 : YK11.FPState, @aatoi_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_atoi) A_FLAG_REPLACE_STR A_SSP_GOT A_SSP_GUARD.
(* `using MT`: the post has no meter conjunct (frame form), so MT is named here to keep the uniform signature
   tsup_reply_code_spec B MT *)
#[using="MT"]
Definition tsup_reply_code_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md (x : Z) (s : list byte),
afn_pre_na SEGS B SUP_REPLY_CODE_STK ly S W regs mem md ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
getr regs 10 = w64 x -> 0 <= x < 2 ^ 64 ->
(* the string (plain sup_reply_code_c.v:44-47): inside a live block, NUL-terminated, and the bytes after its
   terminator up to the end of that 8-byte word readable, which musl's word loops under both wrappers read
   (RtDefs.v's atail_vis) *)
in_blockA (ablocks B ly S) x (Z.of_nat (length s) + 1) -> astr_atR (rdW W mem) x s ->
atail_vis SEGS W mem (x + Z.of_nat (length s)) ->
(* the literal "resp " (plain :48), among the image's read-only bytes, and the bridge from the listing's object
   atoms to its address (lib/A/Prog/CmdObj.v) *)
cmd_ro_ok (rdW W mem) -> cmd_val_objs ->
st_nev S + EV_SUP_REPLY_CODE <= EV_MAX ->
SRr SEGS W (cfg_at SEGS (BASE + AF_sup_reply_code) regs mem md)
(apost_base SEGS B SUP_REPLY_CODE_STK [] regs ly S W mem md EV_SUP_REPLY_CODE
(fun ly' S' W' regs' mem' md' =>
 getr regs' 10 = w64 (reply_code_a s) /\
 Permutation (ablocks B ly' S') (ablocks B ly S) /\
 (* it allocates nothing and takes no side-stack frame: layout and allocator state unchanged (M6; mo_le_refl
    gives the meter) *)
 ly' = ly /\ S' = S)).
End e.
End f.
End d.
