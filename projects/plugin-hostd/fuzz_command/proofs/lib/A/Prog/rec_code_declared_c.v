(* The contract of rec_code_declared on the ASan build of plugin-hostd/fuzz_command.

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): afn_pre at the entry,
   SRr of apost_base at the return. Functional content: fuzz_command's own released plain contract
   lib/Prog/rec_code_declared_c.v:15-27 (a0 = 1 when the code is declared, else 0) and its model
   lib/Prog/RecFacts.v:358-369 (rec_codes, declared), used as they are.
   The function (recorder.c:57-65) scans the 58 entries of the read-only table rec_codes (0x21ba0, 232 bytes) and
   returns 1 at the first entry equal to the code, else 0. Each 4-byte load of an entry has an inline check; rec_codes
   is a registered global of 232 bytes (M: asan_globals descriptor, size_with_redzone 288), so its shadow bytes say
   usable (CmdRecFacts' cmd_addressable_chk, which the walk applies; no premise here) and the error path (a call of
   `__asan_report_load4`) is not reached. The table's bytes are RO_rec_codes of cmd_ro_ok (lib/A/Prog/CmdRo.v),
   which are the plain proof's rec_codes_bytes (lib/Prog/rec_code_declared_c.v:12-13); the function forms the
   table's address pc-relatively (auipc/addi at 0x89184), with no GOT word.

   Addresses: entry BASE + AF_rec_code_declared = 0x89170 (M, the pinned image). 31 instructions, 1 inline check,
   1 loop (58 iterations, `li a4,58` at 0x8918c, back edge 0x891b8 -> 0x89194), no call, no side-stack frame. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep
  CmdObj CmdRo.
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
(* the stack this call needs: its own 16-byte frame; it calls nothing *)
Definition REC_CODE_DECLARED_STK : Z := 16.
Definition EV_REC_CODE_DECLARED : Z := 0.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* `using MT`: the post has no meter conjunct (frame form), so MT is named here to keep the uniform signature
   trec_code_declared_spec B MT *)
#[using="MT"]
Definition trec_code_declared_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md (c : Z),
afn_pre_na SEGS B REC_CODE_DECLARED_STK ly S W regs mem md ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
(* the code, an int, sign-extended in a0 (plain rec_code_declared_c.v:18-19) *)
getr regs 10 = w64 c -> -2^31 <= c < 2^31 ->
(* the table rec_codes, among the image's read-only bytes (plain :20), and the bridge from the listing's object
   atoms to its address (lib/A/Prog/CmdObj.v) *)
cmd_ro_ok (rdW W mem) -> cmd_val_objs ->
st_nev S + EV_REC_CODE_DECLARED <= EV_MAX ->
SRr SEGS W (cfg_at SEGS (BASE + AF_rec_code_declared) regs mem md)
(apost_base SEGS B REC_CODE_DECLARED_STK [] regs ly S W mem md EV_REC_CODE_DECLARED
(fun ly' S' W' regs' mem' md' =>
 getr regs' 10 = w64 (if declared c then 1 else 0) /\
 Permutation (ablocks B ly' S') (ablocks B ly S) /\
 (* it allocates nothing and takes no side-stack frame: layout and allocator state unchanged (M6; mo_le_refl
    gives the meter) *)
 ly' = ly /\ S' = S)).
End e.
End f.
End d.
