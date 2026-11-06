(* The contract of answer_code on the ASan build of plugin-hostd/fuzz_command.
   The post is FP-existential (apost_baseF, the printf wrappers' shared post); the pre carries rounding mode 0.
   The callees' contracts are taken at every FP state (forall fx0), so a walk can use them at the fx' a call returns.

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): afn_pre at the entry,
   SRr of apost_base at the return; the side-stack frame as cgif's class-1 users take it (aj_stack_malloc_atS,
   lib/YC85.v:292-310). Functional content: fuzz_command's own released plain contract
   lib/Prog/answer_code_c.v:27-63 (answer_code_ret :27-50, the contract :52-63: a0 = the code, the recorder holds
   `fst (rec_answer_code R code)`, the old answer freed, one fresh block owned by the recorder) and the model
   lib/Prog/RecModel.v:52 (`rec_answer_code R code = (set_answer R (Some (resp code)), code)`), RecFacts.v:122
   (`resp c = "resp " ++ dec c`).
   answer_code(code) (recorder.c:501-508) writes "resp <code>" into a 32-byte buffer with the snprintf wrapper
   (`___interceptor_snprintf`, reached through the 4-byte jump `__interceptor_trampoline_snprintf`, format "resp %d"
   at 0x21d00), hands it to hand_back (which frees the old answer, keeps one copy and returns another), frees the
   returned copy and returns the code. The buffer lives in a class-1 side-stack frame of 96 bytes taken with
   `__asan_stack_malloc_1` (this port's decision: the side-stack branch only; the use-after-return flag is the record's
   const cell as_uar_cell = 1, cgif lib/YG0f.v:193 aso_const_law, so the real-stack fallback is not taken) and
   released inline by the flag store (cgif's astack_free_law, lib/YG0d.v:300-308); its shadow bytes are marked usable
   for buf (00) and unusable around it (f1, f3, then f8 and f5 at the release). The stack-protector cells the musl
   body under the snprintf wrapper compares (RtDefs.v aguard_ok) are cmd_rec_cells (lib/A/Prog/CmdRecFacts.v).

   Addresses: entry BASE + AF_answer_code = 0x8cac4 (M, the pinned image). 124 instructions, no inline check, no
   data loop (the page-probe loop of the real-stack fallback is not reached). Calls: __asan_stack_malloc_1
   (0x3fa7c), the snprintf wrapper (0x45184), hand_back (0x8a478), the free wrapper (0x58980). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import hand_back_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG c := (@pa_sigma _ cmd_listing PI c).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* the stack this call needs: its own 96-byte frame and the realignment `andi sp,sp,-32` (at most 16 more bytes,
   0x8caf0), then the deepest window below it: hand_back's need, the free wrapper's ASTACK (cgif lib/YG0d.v:17),
   the snprintf wrapper's 3 * ESTACK (measured) or __asan_stack_malloc_1's ESTACK *)
Definition ANSWER_CODE_STK : Z := 112 + Z.max HAND_BACK_STK (Z.max ASTACK (3 * ESTACK)).
(* hand_back's free and two mallocs, then the free of the returned copy *)
Definition EV_ANSWER_CODE : Z := EV_HAND_BACK + 1.
(* the live bytes the call adds at its peak: hand_back's two copies of "resp <code>" *)
Definition LIVE_ANSWER_CODE (code : Z) : Z := LIVE_HAND_BACK (resp code).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Definition XM_ANSWER_CODE (code : Z) : Z := XM_HAND_BACK MT (resp code) + mo_free MT.
(* the callee and the runtime entries this call reaches *)
Hypothesis THAND_BACK : forall fx0 : YK11.FPState, @thand_back_spec fx0 rc SK PI B MT.
Hypothesis AFREE4 : forall fx0 : YK11.FPState, @afree04_rule fx0 rc SK SEGS B MT.
Hypothesis ASTACK1 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 1.
Hypothesis AFREE_LAW : astack_free_law SEGS B.
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState, @asnprintf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_snprintf) 0xa7098 0x6045d8.
Hypothesis VOBJS : cmd_val_objs.
Definition tanswer_code_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (code old : Z) (R : rstate) (O : list (Z * Z)),
afn_pre SEGS B ANSWER_CODE_STK ly S W regs mem md ch ->
(* rounding mode 0 (frm = fcsr bits 5..7): the printf wrappers' frm0_entry; apost_baseF gives it back after a call *)
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
(* the format string "resp %d" (RO_lit_21d00) and the GOT word of the use-after-return flag *)
cmd_ro_ok (rdW W mem) ->
getr regs 10 = w64 code -> -2 ^ 31 <= code < 2 ^ 31 ->
(* the recorder's state; old is the answer it holds (0 or the start of one of its blocks O), a 64-bit word *)
rec_repA B ly S (rdW W mem) R O ->
aval_mem (rdW W mem) (A_G_REC + OFF_ANSWER) 8 old -> 0 <= old < 2 ^ 64 ->
(* room for one more side-stack frame (cgif's frame-count premise, lib/YC7x.v:75) *)
Z.of_nat (length (frames S)) <= 8 ->
st_nev S + EV_ANSWER_CODE <= EV_MAX -> blocks_bytes S + LIVE_ANSWER_CODE code <= LIVE_MAX ->
mo_ok MT S (XM_ANSWER_CODE code) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_answer_code) regs mem md)
(apost_baseF SEGS B ANSWER_CODE_STK
 ((A_G_REC + OFF_ANSWER, A_G_REC + OFF_ANSWER + 8) :: ablocks_fp (filter (fun pn => fst pn =? old) O))
 regs ly S W mem md EV_ANSWER_CODE
(fun ly' S' W' regs' mem' md' => exists (p1 : Z) (O' : list (Z * Z)),
 let n := Z.of_nat (length (resp code)) + 1 in
 (* a0 = the code (plain answer_code_c.v:35) *)
 getr regs' 10 = w64 (snd (rec_answer_code R code)) /\
 (* one fresh block of |resp code| + 1 bytes, none of the blocks live at the entry that the call keeps (the old
    answer may be freed and its address reused); the old answer's block is gone, every other block stays *)
 (forall pn, In pn (ablocks B ly S) -> fst pn <> old -> pn <> (p1, n)) /\
 (forall pn, In pn (ablocks B ly' S') <-> (In pn (ablocks B ly S) /\ fst pn <> old) \/ pn = (p1, n)) /\
 (* the recorder now holds "resp <code>" as its answer, in p1 (plain answer_code_c.v:42-43) *)
 rec_repA B ly' S' (rdW W' mem') (fst (rec_answer_code R code)) O' /\
 (forall pn, In pn O' <-> (In pn O /\ fst pn <> old) \/ pn = (p1, n)) /\
 blocks_bytes S' <= blocks_bytes S + LIVE_ANSWER_CODE code /\
 mo_le MT S S' (XM_ANSWER_CODE code))).
End e.
End f.
End d.
