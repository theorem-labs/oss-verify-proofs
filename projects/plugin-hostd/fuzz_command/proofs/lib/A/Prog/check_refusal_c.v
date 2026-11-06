(* The contract of check_refusal on the ASan build of plugin-hostd/fuzz_command.
   The callees' contracts are taken at every FP state (forall fx0), so a walk can use them at the fx' a call returns.

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): afn_pre at the entry,
   SRr of apost_base at the return. Functional content: fuzz_command's own released plain contract
   lib/Prog/check_refusal_c.v:12-29, the refusal property of fuzz_command.c:447-456. When the recorder holds a
   reply and the reply is a refusal (its code is negative), the daemon must have changed nothing: g_rec.state is
   the state the harness saved before the message (the argument) and g_quitting is 0; else the function calls
   abort(). The code is the value the ASan build computes: sup_reply_code goes through the atoi wrapper, so the
   code is `reply_code_a` of lib/A/Prog/sup_reply_code_c.v (the plain `reply_code`'s prefix test with the atoi wrapper's
   value), not the plain proof's atoi_musl. The pre-condition `reply_code_a x < 0 -> state = before /\ quit = 0` is
   what the caller (LLVMFuzzerTestOneInput) has established from harness_props_holds
   (lib/Prog/HarnessProps.v:29), so the abort edge (0x87fac: __asan_handle_no_return, then abort) is not taken.

   What the function reads: g_rec.reply (g_rec + 928, 8 bytes) and g_rec.state (g_rec + 944, 8 bytes) through the
   GOT word 0xa7068, g_quitting (4 bytes) through the GOT word 0xa7080 (both GOT words are cmd_ro_ok's RO_ptr_a7068
   / RO_ptr_a7080, CmdRo.v:433-439), and, in sup_reply_code, the reply string, the literal "resp " and the errno
   cell. Each of the three inline checks reads the shadow byte at (a >> 3) + 0x7fff8000 of a byte of g_rec or
   g_quitting, which CmdRecFacts' cmd_addressable_chk says usable (its boolean checker covers g_quitting's partial
   last granule), so the error path (a call of __asan_report_load8 / __asan_report_load4) is not reached and the
   contract states the address range only. What sup_reply_code asks besides its string premises comes from the
   record: the bytes after the reply's terminator from cmd_heap_tail_vis (the reply is a heap block), and the
   stack-protector cells, the replace_str flag byte and the errno cell the atoi wrapper reads from cmd_rec_cells;
   none is a premise. It writes nothing outside its own frame.
   It keeps its argument `before` in s0 across its one program call (0x87f44 mv s0,a0; 0x87f50 jal sup_reply_code);
   it allocates nothing, so it carries no frame-chain premise (sup_reply_code is a non-allocating callee).

   Addresses: entry BASE + AF_check_refusal = 0x87f08 (M, the pinned image). 52 instructions, 3 inline checks
   (load8 2, load4 1), no loop, one program call (sup_reply_code at 0x87f50). Objects of the listing it loads:
   A_OBJ 0 (the shadow base), 2 (GOT g_rec), 6 (GOT g_quitting) (the image's function table). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep
  CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import sup_reply_code_c.
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
(* the stack this call needs: its own 32-byte frame (addi sp,sp,-32 at 0x87f08) and the window of its one
   callee, sup_reply_code (whose own need is its frame and the atoi wrapper's window) *)
Definition CHECK_REFUSAL_STK : Z := 32 + SUP_REPLY_CODE_STK.
(* no allocator event of its own; sup_reply_code spends none either *)
Definition EV_CHECK_REFUSAL : Z := EV_SUP_REPLY_CODE.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the callee's contract, never restated (lib/A/Prog/sup_reply_code_c.v) *)
Hypothesis HSUP_REPLY_CODE : forall fx0 : YK11.FPState, @tsup_reply_code_spec fx0 rc SK PI B MT.
(* `using MT`: the post has no meter conjunct (frame form), so MT is named here to keep the uniform signature
   tcheck_refusal_spec B MT *)
#[using="MT"]
Definition tcheck_refusal_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md (before reply state quit : Z) (y : option (list byte)),
afn_pre_na SEGS B CHECK_REFUSAL_STK ly S W regs mem md ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
(* the GOT words of g_rec and g_quitting, what sup_reply_code reads besides the reply (the literal "resp ",
   RO_lit_21d20), all among the image's read-only bytes; and the bridge from the listing's object atoms to the
   addresses named here (lib/A/Prog/CmdObj.v) *)
cmd_ro_ok (rdW W mem) -> cmd_val_objs ->
getr regs 10 = w64 before -> 0 <= before < 2 ^ 64 ->
(* g_rec.reply and g_rec.state: bytes of the recorder's object g_rec *)
aval_mem (rdW W mem) (A_G_REC + OFF_REPLY) 8 reply -> 0 <= reply < 2 ^ 64 ->
aval_mem (rdW W mem) (A_G_REC + OFF_STATE) 8 state -> 0 <= state < 2 ^ 64 ->
(* g_quitting *)
aval_mem (rdW W mem) A_G_QUITTING 4 quit -> 0 <= quit < 2 ^ 32 ->
(* the reply: none (a NULL pointer), or a NUL-terminated string inside a live block, the recorder's reply buffer
   (the reply is always that heap buffer or NULL, so no read-only branch; what sup_reply_code asks at 0x87f50) *)
(y = None -> reply = 0) ->
(forall x, y = Some x ->
 reply <> 0 /\ in_blockA (ablocks B ly S) reply (Z.of_nat (length x) + 1) /\ astr_atR (rdW W mem) reply x) ->
(* what the caller has established: a refused message changed nothing *)
(forall x, y = Some x -> reply_code_a x < 0 -> state = before /\ quit = 0) ->
st_nev S + EV_CHECK_REFUSAL <= EV_MAX ->
SRr SEGS W (cfg_at SEGS (BASE + AF_check_refusal) regs mem md)
(apost_base SEGS B CHECK_REFUSAL_STK [] regs ly S W mem md EV_CHECK_REFUSAL
(fun ly' S' W' regs' mem' md' =>
 Permutation (ablocks B ly' S') (ablocks B ly S) /\
 (* it allocates nothing and takes no side-stack frame, nor does sup_reply_code: layout and allocator state
    unchanged (M6; mo_le_refl gives the meter) *)
 ly' = ly /\ S' = S)).
End e.
End f.
End d.
