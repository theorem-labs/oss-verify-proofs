(* The contract of verbs_receive on the ASan+UBSan build of plugin-hostd/fuzz_command (fuzz_command.asan-ubsan).
   The post is FP-existential (apost_baseF, the printf wrappers' shared post); the pre carries rounding mode 0.
   The callees' contracts are taken at every FP state (forall fx0), so a walk can use them at the fx' a call returns.

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): afn_pre at the entry,
   SRr of apost_base at the return. Functional content: fuzz_command's own released plain contract
   lib/Prog/verbs_receive_c.v:37-81 (the recorder and g_quitting at :65-67, the message struct kept at :74-76, the
   block accounting at :68-77) and its model lib/Spec/VerbsRun.v:59-64 (run_receive), over lib/Spec/Verbs.v:315-319
   (receive: line, toks, plan, after). The plain contract takes the parsed value of musl's atoi (plain
   vr_run, verbs_receive_c.v:22-23); this one takes the value of the ASan wrapper, atoi_a and reply_code_a of
   lib/B/Prog/sup_reply_code_c.v (this port's decision: an ASan statement states the wrapper's value).
   The B twin of lib/A/Prog/verbs_receive_c.v, re-derived on B's code (its disassembly): the same C, the
   same 32 program callees and 13 runtime callees as A, a different instruction stream (734 instructions against
   A's 677: UBSan's 34 check sites below, no shadow check on the tok[k] loads).

   The function (L/src/verbs.c:217-238) reads one message: line = strndup(msg->data, msg->data_size), trims the
   trailing spaces, tabs, newlines and carriage returns, copy = strdup(line), splits copy into at most 64 words with
   strtok_r, and, with no word, replies sup_resp(-902); else it replies handle(line, tok, ntok) — the dispatch over
   the verbs, inlined — and, when the first word is preset_load or patch_set and there are at least two words,
   calls sup_after_reply(atoi(tok[1]), tok[0]). It then frees copy and line.

   Addresses (B's disassembly): entry BASE + AF_verbs_receive = 0x8ce4c. 734 instructions, the largest
   program function. Real frame 192 bytes (`addi sp,sp,-192`), then `andi sp,sp,-32` (0x8ce8c): at most 16 more
   bytes. Side-stack frame class 4 (640 bytes, `__asan_stack_malloc_4` at 0x8ceb8; description at 0x13794) holding
   tok[64] at frame+32 (0x8d0b4) and save at frame+608 (0x8cfb8). Its shadow is written at the entry (f1 x4 inline,
   then `__asan_set_shadow_f8` over 64 shadow bytes at 0x8cf3c, f2/f8/f3 inline), opened over tok by
   `__asan_set_shadow_00` at 0x8cfcc after strndup returns (and over save by the byte store at 0x8cfd0), and closed
   again at the return (f8 over save 0x8d730, `__asan_set_shadow_f8` over tok 0x8d73c, the magic 0x45e0360e at
   frame+0, `__asan_set_shadow_f5` 0x8d758 over the whole frame and the flag byte store through frame+1016,
   0x8d75c-0x8d760). Only the side-stack branch is stated (the use-after-return flag, read through the GOT word
   0xa5fa8, is the record's const cell as_uar_cell = 1, cgif lib/YG0f.v:193 aso_const_law), so the 4096-byte probe
   loop (0x8cedc-0x8cee4) and the 0x8d768 branch are dead. Four loops: the trim loop (0x8d014-0x8d050), the
   strtok_r loop (0x8d0c8-0x8d0f0, at most 64 passes), the 10-row scan over g_instance_info_verbs (0xa5c40,
   0x8d804-0x8d82c) and the dead probe loop. Eight inline checks, each reading the shadow byte at
   (a >> 3) + shadow base (GOT word 0xa5f50): load8 of msg+8 (0x8cf94) and msg+16 (0x8cfa8), load1 (0x8d020) and
   store1 (0x8d040) in the trim loop, load4 of msg+0 twice (0x8d0f8, 0x8d2c0), and load8 (0x8d804) / load4
   (0x8d894) of the g_instance_info_verbs row; each error path (a call of `__asan_report_*`, 0x8d984-0x8d9c0) is
   not reached by the premises on the message struct and the strndup block, and, for the read-only table, by
   cmd_addressable_chk (CmdRecFacts). s0 is the frame pointer (0x8ce88 addi s0,sp,192) at every program call, so
   no argument needs a frame chain premise: each callee's chain is this call's afn_pre chain with its
   own frame record on top (ra at s0 - 8, the caller's s0 at s0 - 16), and achain_chain_pre (YCbq.v:327) gives the
   runtime entries' chain_pre from it; no presence of the stack up to ly_top is assumed. The callees' string
   arguments: the words of `copy`
   and the line are heap strings (word tails: cmd_heap_tail_vis); the literals it passes (verb_is's formats .str.21,
   .str.22 0x22840 and .str.23, at 0x8d290, 0x8d8c8, 0x8d8e8; sup_reset's "all" .str.10 0x226a0) have their tails by
   cmd_tail_vis,
   and sup_instance_verb's ledger is a word of the read-only table (cmd_ro_ok).

   strtok_r is NOT intercepted (M, B's interceptor table): the calls at 0x8d08c/0x8d0e0 reach musl's strtok_r 0x9f360
   directly, which writes `save` inside this function's side-stack frame and one terminator inside `copy` (RtString.v's
   astrtok_r_realizes; separators " \t", .str 0x22500). strndup (0x8cfbc) and strdup (0x8d078) go through the
   wrappers of the memory-checking runtime, which allocate at most 8193 bytes each; both blocks are freed at
   0x8d720 (copy) and 0x8d728 (line). The stack-protector cells of the musl bodies under strcspn, strtok_r and atoi
   are B's GOT word 0xa6bf8 and guard cell 0x604158, and atoi's replace_str flag byte is 0xae455 (lib/B/Rt/RtAPI.v
   A_SSP_GOT, A_SSP_GUARD, A_FLAG_REPLACE_STR): CmdRecFacts' cmd_rec_cells gives all three.

   UBSan (trap mode: a failed check branches to the `unimp` at 0x8d938, a machine fault in cgif's model,
   lib/Reusable/YP00.v). 34 check sites (B's trap-site and trap exclusion tables), none taken on a path this statement
   allows, and none needs a premise of its own:
   - 0x8cf7c (msg null, verbs.c:219) and 0x8cf84 (msg not 8-aligned): msg lies in a frame of frames S and
     msg mod 8 = 0, both by the `afobj msg 24` premise;
   - 0x8cfe4 (line + strlen(line) wraps, verbs.c:222), 0x8cff4 (exactly one of line and end null) and 0x8d014
     (end - 1 null in the trim loop, verbs.c:223): line is strndup's fresh block of strnlen_res + 1 bytes (the
     ASTRNDUP rule's post), at or above 4096 and inside the heap below 2 ^ 47 (AR), and end runs over
     (line, line + strlen(line)];
   - 29 pointer-overflow sites on tok + 8k (k = 1..4; tok + 8k wraps or is null): 0x8d318 0x8d338 0x8d34c 0x8d3cc
     0x8d3e0 0x8d408 0x8d42c 0x8d444 0x8d458 0x8d460 0x8d49c 0x8d4f8 0x8d510 0x8d52c 0x8d534 0x8d57c 0x8d584
     0x8d5a8 0x8d5b0 0x8d5e0 0x8d5e8 0x8d5f0 0x8d62c 0x8d67c 0x8d708 0x8d7c4 0x8d858 0x8d914 0x8d91c. tok is this
     call's own class-4 frame + 32, which the SM4 rule returns inside the layout's frame area (below ly_stk_hi ly
     <= 2 ^ 47, afn_pre's astk_ok), so tok + 32 < 2 ^ 64 - 25 and tok + 8k <> 0.

   Resources: the plain proof's malloc budget, VR_MALLOCS = 32 allocations of at most VR_REQ = 8194 bytes
   (lib/Prog/verbs_receive_c.v:19-20), and the events of the handler path. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require RtString RtNumber RtAlloc04 RtShadow.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdObj CmdRo CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
chain_words_c descriptors_add_c descriptors_get_c descriptors_panel_get_c is_instance_verb_c lv2_refusals_forget_c
number_c pin_set_words_c pins_clear_c reply_c sup_add_c sup_after_reply_c sup_broadcast_c sup_call_c
sup_chain_c sup_chain_clear_c sup_connect_c sup_host_setting_c sup_instance_info_c sup_instance_verb_c sup_lv2_worker_set_c
sup_pin_accept_c sup_policy_set_c sup_pool_config_c sup_quarantine_clear_c sup_remove_c sup_remove_all_c
sup_reply_code_c sup_reset_c sup_resp_c sup_worker_env_c sup_worker_list_c verb_is_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* the message this call answers, and whether it asked the daemon to quit: lib/Spec/VerbsRun.v:59-64 run_receive,
   with the values the ASan wrappers return for atoi and for the code of a reply *)
Definition vr_runA (R : rstate) (D : list byte) : rstate * list byte * bool :=
VerbsRun.run_receive atoi_a reply_code_a R D.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* the deepest of the 32 program callees *)
Definition VR_CALLEE_STK : Z :=
Z.max CHAIN_WORDS_STK (Z.max DESCRIPTORS_ADD_STK (Z.max DESCRIPTORS_GET_STK (Z.max DESCRIPTORS_PANEL_GET_STK
(Z.max IS_INSTANCE_VERB_STK (Z.max LV2_REFUSALS_FORGET_STK (Z.max NUMBER_STK (Z.max PIN_SET_WORDS_STK
(Z.max PINS_CLEAR_STK (Z.max REPLY_STK (Z.max SUP_ADD_STK (Z.max SUP_AFTER_REPLY_STK (Z.max SUP_BROADCAST_STK
(Z.max SUP_CALL_STK (Z.max SUP_CHAIN_CLEAR_STK (Z.max SUP_CONNECT_STK (Z.max SUP_HOST_SETTING_STK
(Z.max SUP_INSTANCE_INFO_STK (Z.max SUP_INSTANCE_VERB_STK (Z.max SUP_LV2_WORKER_SET_STK (Z.max SUP_PIN_ACCEPT_STK
(Z.max SUP_POLICY_SET_STK (Z.max SUP_POOL_CONFIG_STK (Z.max SUP_QUARANTINE_CLEAR_STK (Z.max SUP_REMOVE_STK
(Z.max SUP_REMOVE_ALL_STK (Z.max SUP_REPLY_CODE_STK (Z.max SUP_RESET_STK (Z.max SUP_RESP_STK
(Z.max SUP_WORKER_ENV_STK (Z.max SUP_WORKER_LIST_STK VERB_IS_STK)))))))))))))))))))))))))))))).
(* the stack this call needs: its own frame, 192 bytes and at most 16 of realignment, and below it the deepest of
   its callees and of the runtime entries it reaches: the free wrapper and strdup/strndup ask ASTACK (cgif
   lib/YG0d.v:17, RtAlloc04.v's astrdup04_rule / astrndup04_rule), strtok_r asks 4 * ESTACK and atoi 3 * ESTACK
   (RtString.v's astrtok_r_realizes / RtNumber.v's aatoi_realizes), the comparison and span wrappers 2 * ESTACK,
   and strlen, the frame and the shadow entries ESTACK. M: B's function table gives 17152 = 192 + chain_words' 16960
   (without the realignment's 16) *)
Definition VERBS_RECEIVE_STK : Z := 192 + 16 + Z.max VR_CALLEE_STK (Z.max ASTACK (4 * ESTACK)).
(* The events one message spends, as a function of the route its first word selects. The plain proof's own verb
   classification is the model's: `Verbs.receive atoi_a D` (lib/Spec/Verbs.v:315-319) returns the step the dispatch
   takes and whether a call follows the reply, so one case per constructor is one case per route. A single constant
   over all routes would charge every message the deepest route and `sup_after_reply` on top of it, which a caller
   cannot afford: the measured worst case is about 2,372 events per call of the harness against EV_LIB 2,900
   (the allocator-event count per call of LLVMFuzzerTestOneInput). B's allocator calls per route are A's (UBSan
   moves calls between functions, not their number). *)
(* The recorder state is a parameter because a recorder entry's events depend on it: record()'s spill arm frees the
   arguments the spill held, `rec_spill_frees R` (CmdRep.v, inside EV_RECORD R), which is 0 while the table holds
   fewer than 16 calls. Each entry below is the first recorder call of its route, so it is applied to R itself;
   where a route makes a second recorder call (descriptors_add after sup_add, sup_host_setting after
   sup_broadcast, lv2_refusals_forget after pins_set / pins_clear) that callee is charged on the state the first
   left, `fst (sup_add_m R ...)`. *)
Definition ev_call (R : rstate) (c : Verbs.call) : Z :=
match c with
| Verbs.sup_add _ _ _ _ => EV_SUP_ADD R
| Verbs.descriptors_get _ => EV_DESCRIPTORS_GET R
| Verbs.descriptors_panel_get _ => EV_DESCRIPTORS_PANEL_GET R
| Verbs.sup_remove _ => EV_SUP_REMOVE R
| Verbs.sup_remove_all => EV_SUP_REMOVE_ALL R
| Verbs.sup_worker_list => EV_SUP_WORKER_LIST R
| Verbs.sup_instance_info _ => EV_SUP_INSTANCE_INFO R
| Verbs.sup_reset _ => EV_SUP_RESET R
| Verbs.sup_quarantine_clear _ => EV_SUP_QUARANTINE_CLEAR R
| Verbs.sup_policy_set _ _ => EV_SUP_POLICY_SET R
| Verbs.sup_lv2_worker_set _ _ => EV_SUP_LV2_WORKER_SET R
| Verbs.sup_pool_config _ _ => EV_SUP_POOL_CONFIG R
| Verbs.sup_worker_env _ _ _ => EV_SUP_WORKER_ENV R
| Verbs.sup_chain _ _ => EV_SUP_CHAIN R
| Verbs.sup_chain_clear _ => EV_SUP_CHAIN_CLEAR R
| Verbs.sup_pin_accept _ => EV_SUP_PIN_ACCEPT R
| Verbs.sup_instance_verb _ _ => EV_SUP_INSTANCE_VERB R
| Verbs.sup_call _ _ => EV_SUP_CALL R
| Verbs.sup_connect _ _ _ _ => EV_SUP_CONNECT R
end.
(* A route that makes two recorder calls charges the second on the state the first left, which the model gives:
   descriptors_add after sup_add (L/src/verbs.c:142-145; B: the sup_add call before 0x8d484, then 0x8d4a4),
   lv2_refusals_forget after pins_clear
   (:192-195; B 0x8d7cc, 0x8d7d4), and sup_host_setting after sup_broadcast (:212-213; B 0x8d944, 0x8d95c). The
   SPinSet case is unreachable here: `pin_set_words_m` is produced only under the first word pin_set, which
   ev_route reads off the words below. *)
Definition ev_step (R : rstate) (s : Verbs.step) : Z :=
match s with
| Verbs.SResp _ => EV_SUP_RESP
| Verbs.SCall c => ev_call R c
| Verbs.SAdd u i p q =>
  EV_SUP_ADD R + EV_SUP_REPLY_CODE + EV_DESCRIPTORS_ADD (fst (sup_add_m R (Some u) i p q))
| Verbs.SPinSet _ _ _ _ => 0
| Verbs.SPinClear u =>
  let '(R1, rc) := pins_clear_m R (Some u) in
  EV_PINS_CLEAR R + (if rc =? 0 then EV_LV2_REFUSALS_FORGET R1 else 0) + EV_SUP_RESP
| Verbs.SQuit => EV_SUP_RESP
| Verbs.SBroadcast ln _ => EV_SUP_BROADCAST R + EV_SUP_HOST_SETTING (fst (sup_broadcast_m R ln))
end.
(* Two verbs reach a program function before the dispatch decides to refuse, so their route is read off the first
   word, not off the step: `chain` always enters chain_words (L/src/verbs.c:179; B 0x8d614) and `pin_set` always
   enters pin_set_words (:187; B 0x8d664, then sup_resp at 0x8d88c), and each of the two may still answer
   sup_resp(-902) from inside. Every other refusal is decided in the dispatch itself and spends sup_resp alone. *)
Definition ev_route (R : rstate) (ln : list byte) (tk : list (list byte)) (s : Verbs.step) : Z :=
match tk with
| [] => EV_SUP_RESP
| v :: args =>
  if Verbs.list_eqb v Verbs.Lit.verb_chain then EV_CHAIN_WORDS R
  else if Verbs.list_eqb v Verbs.Lit.verb_pin_set then EV_PIN_SET_WORDS R ln args + EV_SUP_RESP
  else ev_step R s
end.
(* sup_after_reply runs only when the first word is preset_load or patch_set and a second word follows
   (L/src/verbs.c:233-234; B 0x8d6b8-0x8d718), which is exactly `Verbs.after` (lib/Spec/Verbs.v:309-313). It runs
   last, so it is charged on the state the handler and the reply left, `R2` of run_receive
   (lib/Spec/VerbsRun.v:59-64). *)
Definition ev_after (R2 : rstate) (af : option (Z * list byte)) : Z :=
match af with Some _ => EV_SUP_AFTER_REPLY R2 | None => 0 end.
(* strndup, strdup and their two frees; the route; the reply; and the call after the reply *)
Definition ev_vr (R : rstate) (D : list byte) : Z :=
let '(st, af) := Verbs.receive atoi_a D in
let '(R1, x, _) := VerbsRun.run_step reply_code_a R st in
4 + ev_route R (Verbs.line D) (Verbs.toks D) st + EV_REPLY
  + ev_after (fst (socket_send_m R1 (x ++ [Z_to_bv 8 0]))) af.
(* the plain proof's budget (lib/Prog/verbs_receive_c.v:19-20): 32 allocations of at most 8194 bytes *)
Definition VERBS_RECEIVE_MALLOCS : Z := 32.
Definition VERBS_RECEIVE_REQ : Z := 8194.
Definition LIVE_VERBS_RECEIVE : Z := VERBS_RECEIVE_MALLOCS * VERBS_RECEIVE_REQ.
(* the writable statics this call reaches: the recorder's g_rec and record.spill, and g_quitting, which the quit
   verb sets (L/src/verbs.c:202, the 4-byte store at 0x8d2ac) *)
Definition VERBS_RECEIVE_PG : list (Z * Z) :=
[(A_G_REC, A_G_REC + REC_SIZE); (A_REC_SPILL, A_REC_SPILL + SC_SIZE); (A_G_QUITTING, A_G_QUITTING + 4)].
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the two program counters the duplicating wrappers give the unwinder (lib/B/Rt/RtAPI.v PC_STRDUP_RA0 /
   PC_STRNDUP_RA0); the instance pins them from the image *)
Variables PC_STRDUP_RA0 PC_STRNDUP_RA0 : Z.
(* the meter: each of the route's allocator events (ev_vr R D, mallocs and frees) charged the largest allocation
   (8194 bytes) and a free, so that a caller's bound per event (LLVMFuzzerTestOneInput_c.v's XM_LTOI) dominates it
   on every route; a route-independent count of 32 mallocs would not (measured) *)
Definition XM_VERBS_RECEIVE (R : rstate) (D : list byte) : Z :=
ev_vr R D * (mo_malloc MT VERBS_RECEIVE_REQ + mo_free MT).
(* the 32 program callees' contracts, never restated *)
Hypothesis TCHAIN_WORDS : forall fx0 : YK11.FPState, @tchain_words_spec fx0 rc SK PI B MT.
Hypothesis TDESCRIPTORS_ADD : forall fx0 : YK11.FPState, @tdescriptors_add_spec fx0 rc SK PI B MT.
Hypothesis TDESCRIPTORS_GET : forall fx0 : YK11.FPState, @tdescriptors_get_spec fx0 rc SK PI B MT.
Hypothesis TDESCRIPTORS_PANEL_GET : forall fx0 : YK11.FPState, @tdescriptors_panel_get_spec fx0 rc SK PI B MT.
Hypothesis TIS_INSTANCE_VERB : forall fx0 : YK11.FPState, @tis_instance_verb_spec fx0 rc SK PI B MT.
Hypothesis TLV2_REFUSALS_FORGET : forall fx0 : YK11.FPState, @tlv2_refusals_forget_spec fx0 rc SK PI B MT.
Hypothesis TNUMBER : forall fx0 : YK11.FPState, @tnumber_spec fx0 rc SK PI B MT.
Hypothesis TPIN_SET_WORDS : forall fx0 : YK11.FPState, @tpin_set_words_spec fx0 rc SK PI B MT.
Hypothesis TPINS_CLEAR : forall fx0 : YK11.FPState, @tpins_clear_spec fx0 rc SK PI B MT.
Hypothesis TREPLY : forall fx0 : YK11.FPState, @treply_spec fx0 rc SK PI B MT.
Hypothesis TSUP_ADD : forall fx0 : YK11.FPState, @tsup_add_spec fx0 rc SK PI B MT.
Hypothesis TSUP_AFTER_REPLY : forall fx0 : YK11.FPState, @tsup_after_reply_spec fx0 rc SK PI B MT.
Hypothesis TSUP_BROADCAST : forall fx0 : YK11.FPState, @tsup_broadcast_spec fx0 rc SK PI B MT.
Hypothesis TSUP_CALL : forall fx0 : YK11.FPState, @tsup_call_spec fx0 rc SK PI B MT.
Hypothesis TSUP_CHAIN_CLEAR : forall fx0 : YK11.FPState, @tsup_chain_clear_spec fx0 rc SK PI B MT.
Hypothesis TSUP_CONNECT : forall fx0 : YK11.FPState, @tsup_connect_spec fx0 rc SK PI B MT.
Hypothesis TSUP_HOST_SETTING : forall fx0 : YK11.FPState, @tsup_host_setting_spec fx0 rc SK PI B MT.
Hypothesis TSUP_INSTANCE_INFO : forall fx0 : YK11.FPState, @tsup_instance_info_spec fx0 rc SK PI B MT.
Hypothesis TSUP_INSTANCE_VERB : forall fx0 : YK11.FPState, @tsup_instance_verb_spec fx0 rc SK PI B MT.
Hypothesis TSUP_LV2_WORKER_SET : forall fx0 : YK11.FPState, @tsup_lv2_worker_set_spec fx0 rc SK PI B MT.
Hypothesis TSUP_PIN_ACCEPT : forall fx0 : YK11.FPState, @tsup_pin_accept_spec fx0 rc SK PI B MT.
Hypothesis TSUP_POLICY_SET : forall fx0 : YK11.FPState, @tsup_policy_set_spec fx0 rc SK PI B MT.
Hypothesis TSUP_POOL_CONFIG : forall fx0 : YK11.FPState, @tsup_pool_config_spec fx0 rc SK PI B MT.
Hypothesis TSUP_QUARANTINE_CLEAR : forall fx0 : YK11.FPState, @tsup_quarantine_clear_spec fx0 rc SK PI B MT.
Hypothesis TSUP_REMOVE : forall fx0 : YK11.FPState, @tsup_remove_spec fx0 rc SK PI B MT.
Hypothesis TSUP_REMOVE_ALL : forall fx0 : YK11.FPState, @tsup_remove_all_spec fx0 rc SK PI B MT.
Hypothesis TSUP_REPLY_CODE : forall fx0 : YK11.FPState, @tsup_reply_code_spec fx0 rc SK PI B MT.
Hypothesis TSUP_RESET : forall fx0 : YK11.FPState, @tsup_reset_spec fx0 rc SK PI B MT.
Hypothesis TSUP_RESP : forall fx0 : YK11.FPState, @tsup_resp_spec fx0 rc SK PI B MT.
Hypothesis TSUP_WORKER_ENV : forall fx0 : YK11.FPState, @tsup_worker_env_spec fx0 rc SK PI B MT.
Hypothesis TSUP_WORKER_LIST : forall fx0 : YK11.FPState, @tsup_worker_list_spec fx0 rc SK PI B MT.
Hypothesis TVERB_IS : forall fx0 : YK11.FPState, @tverb_is_spec fx0 rc SK PI B MT.
(* the entries of the memory-checking runtime this call reaches, at the listing's call targets: the class-4
   side-stack frame, the three shadow-fill entries, the wrappers for strlen, strcmp, strncmp, strcspn, atoi,
   strdup and strndup, musl's strtok_r (not intercepted) and the free wrapper. B's stack-protector cells
   0xa6bf8 / 0x604158 and replace_str flag byte 0xae455 (lib/B/Rt/RtAPI.v). UBSan: SM4's frame is the one tok
   lies in, so with afn_pre's layout bound it excludes the 29 tok + 8k check sites listed in the header *)
Hypothesis SM4 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 4.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis SH00 : forall fx0 : YK11.FPState, @RtShadow.aset_shadow_realizes fx0 rc SEGS B (SIGMA CS___asan_set_shadow_00) 0.
Hypothesis SHF5 : forall fx0 : YK11.FPState, @RtShadow.aset_shadow_realizes fx0 rc SEGS B (SIGMA CS___asan_set_shadow_f5) 0xf5.
Hypothesis SHF8 : forall fx0 : YK11.FPState, @RtShadow.aset_shadow_realizes fx0 rc SEGS B (SIGMA CS___asan_set_shadow_f8) 0xf8.
Hypothesis STRLEN : forall fx0 : YK11.FPState, @RtString.astrlen_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_strlen).
Hypothesis STRCMP : forall fx0 : YK11.FPState, @RtString.astrcmp_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_strcmp).
Hypothesis STRNCMP : forall fx0 : YK11.FPState, @RtString.astrncmp_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_strncmp).
Hypothesis STRCSPN : forall fx0 : YK11.FPState, @RtString.astrcspn_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_strcspn) 0xa6bf8 0x604158.
Hypothesis STRTOK_R : forall fx0 : YK11.FPState, @RtString.astrtok_r_realizes fx0 rc SEGS B (SIGMA CS_strtok_r) 0xa6bf8 0x604158.
Hypothesis AATOI : forall fx0 : YK11.FPState, @RtNumber.aatoi_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_atoi) 0xae455 0xa6bf8 0x604158.
Hypothesis ASTRDUP : forall fx0 : YK11.FPState, @RtAlloc04.astrdup04_rule fx0 rc SK SEGS B MT (SIGMA CS___interceptor_trampoline_strdup) PC_STRDUP_RA0.
(* UBSan: strndup's post (a fresh block of strnlen_res + 1 bytes, in the heap: at or above 4096, below 2 ^ 47) is
   what excludes the check sites 0x8cfe4, 0x8cff4 and 0x8d014 on line and end (verbs.c:222-223) *)
Hypothesis ASTRNDUP : forall fx0 : YK11.FPState, @RtAlloc04.astrndup04_rule fx0 rc SK SEGS B MT (SIGMA CS___interceptor_trampoline_strndup) PC_STRNDUP_RA0.
Hypothesis AFREE : forall fx0 : YK11.FPState, @afree04_rule fx0 rc SK SEGS B MT.
Definition tverbs_receive_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (msg fd data n q0 : Z) (D : list byte)
  (R : rstate) (O rest : list (Z * Z)),
afn_pre SEGS B VERBS_RECEIVE_STK ly S W regs mem md ch ->
(* rounding mode 0 (frm = fcsr bits 5..7): the printf wrappers' frm0_entry; apost_baseF gives it back after a call *)
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
getr regs 10 = w64 msg -> 0 <= msg < 2 ^ 64 ->
(* the message struct, 24 bytes in the caller's side-stack frame (send_message's class-1 frame, frame + 32):
   the sender, the data pointer and the data size (plain :44-46). UBSan: afobj puts msg in a live side-stack frame
   (so msg <> 0) with msg mod 8 = 0, which excludes the check sites 0x8cf7c (msg null) and 0x8cf84 (msg
   misaligned) of verbs.c:219 *)
afobj SEGS B ly S W mem msg 24 ->
aval_mem (rdW W mem) msg 4 fd ->
aval_mem (rdW W mem) (msg + 8) 8 data -> 0 <= data < 2 ^ 64 ->
aval_mem (rdW W mem) (msg + 16) 8 n ->
(* the message bytes: a live block of exactly n bytes, none of the recorder's; it need hold no terminator, so the
   length strndup copies is the plain proof's strnlen_res (lib/Spec/StrFun.v:103) (plain :48-49). strndup's
   `PStrFun.memchr_ok data 0 n D` holds because |D| = n (StrFun.v:95-100: either case needs n <= |D|), and its
   aread_ok over [data, data + min (k + 1) n) is the live block's (RtAlloc04.v's astrndup04_rule asks no tail) *)
0 <= n <= 8192 -> Z.of_nat (length D) = n ->
In (data, Z.max n 1) (ablocks B ly S) -> ~ In (data, Z.max n 1) O ->
abytes_atR (rdW W mem) data D ->
(* the recorder, cleared by send_message before this call (plain :50-52) *)
rec_repA B ly S (rdW W mem) R O ->
r_calls R = [] -> r_answer R = None -> r_reply R = None -> r_nreplies R = 0 ->
(r_refuse R <> 0 -> declared (r_code R) = true) ->
Permutation (ablocks B ly S) (O ++ rest) ->
(* the quit flag (plain :53) *)
aval_mem (rdW W mem) A_G_QUITTING 4 q0 ->
(* the image's read-only bytes the callees load (the GOT words, the literals and the two verb tables among them)
   and the bridge from the listing's object atoms to their addresses; that each lies in the read-only range is a
   constant fact of the image (cmd_ro_in_img), not a premise. The errno cell (atoi reads and writes it), the
   runtime's replace_str flag byte 0xae455 (RtNumber.v's aatoi_realizes) and the stack-protector cells (strcspn,
   strtok_r, atoi) are cmd_rec_cells (CmdRecFacts) *)
cmd_ro_ok (rdW W mem) -> cmd_val_objs ->
(* room for this call's side-stack frame and its callees': with this call's class-4 frame a callee starts with at
   most 5 live frames (chain_words asks <= 5, number <= 6, sup_add, sup_call and sup_chain_clear <= 7, the other
   frame users <= 8) *)
Z.of_nat (length (frames S)) <= 4 ->
st_nev S + ev_vr R D <= EV_MAX -> blocks_bytes S + LIVE_VERBS_RECEIVE <= LIVE_MAX ->
mo_ok MT S (XM_VERBS_RECEIVE R D) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_verbs_receive) regs mem md)
(apost_baseF SEGS B VERBS_RECEIVE_STK (VERBS_RECEIVE_PG ++ ablocks_fp O) regs ly S W mem md (ev_vr R D)
(fun ly' S' W' regs' mem' md' =>
 let '(R', _, quit) := vr_runA R D in
 exists O' : list (Z * Z),
 (* the recorder holds what the message asked for, and the quit flag is set when the verb was quit (plain :65-67) *)
 rec_repA B ly' S' (rdW W' mem') R' O' /\
 aval_mem (rdW W' mem') A_G_QUITTING 4 (if quit then 1 else q0) /\
 (* strndup's and strdup's blocks are freed again, so the live blocks are the recorder's and the rest (plain :68-71,
    :77) *)
 Permutation (ablocks B ly' S') (O' ++ rest) /\
 ~ In (data, Z.max n 1) O' /\ abytes_atR (rdW W' mem') data D /\
 (* the message struct is unchanged (plain :74-76) *)
 aval_mem (rdW W' mem') msg 4 fd /\
 aval_mem (rdW W' mem') (msg + 8) 8 data /\
 aval_mem (rdW W' mem') (msg + 16) 8 n /\
 blocks_bytes S' <= blocks_bytes S + LIVE_VERBS_RECEIVE /\
 mo_le MT S S' (XM_VERBS_RECEIVE R D))).
End e.
End f.
End d.
