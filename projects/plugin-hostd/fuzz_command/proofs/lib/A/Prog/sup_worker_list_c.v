(* The contract of sup_worker_list on the ASan build of plugin-hostd/fuzz_command.
   The post is FP-existential (apost_baseF, the printf wrappers' shared post); the pre carries rounding mode 0.
   The callees' contracts are taken at every FP state (forall fx0), so a walk can use them at the fx' a call returns.

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): afn_pre at the entry,
   SRr of apost_base at the return; the fresh block the caller gets as cgif's trawnew_specX states one
   (lib/YC7x.v:93-101), the meter as there (:88, :92). Functional content: fuzz_command's own released plain
   contract lib/Prog/sup_worker_list_c.v:28-62 and the model lib/Prog/RecModel.v:138 (`sup_worker_list_m`,
   `rec_stub` of the REC id 8 with the arguments the verb carries, RecModel.v:73-75).
   sup_worker_list (recorder.c:390-393) records the call with record() (inlined, recorder.c:205-221: a new slot of
   g_rec.calls, or record.spill with its arguments freed when the table already holds 16 calls), records no
   argument, asks rec_shape_of for the reply shape the verb declares
   (daemon_shape "worker_list", the image string at 0x21d80) and tail-jumps to answer with changes = 0. It
   releases its own frame before the jump, so answer runs at this function's entry stack pointer.

   Addresses: entry BASE + AF_sup_worker_list = 0x8b4f0 (M, the pinned image). 58 instructions, 2 (store4:2) inline
   checks, no loop, no side-stack frame of its own. The error path of each check (a call of
   `__asan_report_*`) is not reached: the slot lies in g_rec or record.spill, whose shadow CmdRecFacts'
   cmd_addressable_chk gives as usable. The stack-protector GOT word 0xa7098 and guard cell 0x6045d8, which the
   snprintf wrapper under answer reads (RtDefs.v's aguard_ok), come from CmdRecFacts' cmd_rec_cells. s0 holds the
   slot (record.spill or a g_rec slot) at every program call, not a value of the caller. Callees: rec_calls_free,
   rec_shape_of, answer. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith List Bool Lia Permutation.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import rec_calls_free_c rec_shape_of_c answer_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* the stack this call needs: its own 32-byte frame and the deepest callee reached with the frame up;
   the tail jump `j answer` runs answer at this function's entry sp, so its need is not added to the frame
   but taken beside it *)
Definition SUP_WORKER_LIST_STK : Z := Z.max (32 + Z.max REC_CALLS_FREE_STK (REC_SHAPE_OF_STK)) ANSWER_STK.
(* the allocator events: the frees of record()'s spill arm and answer's free of the old answer with the two copies
   of the reply text *)
Definition EV_SUP_WORKER_LIST (R : rstate) : Z := rec_spill_frees R + EV_ANSWER.
(* the live bytes the call adds at its peak: answer's two copies of the reply text *)
Definition LIVE_SUP_WORKER_LIST (R : rstate) : Z := LIVE_ANSWER (snd (sup_worker_list_m R)).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the meter the call spends: the spill arm's frees and answer's *)
Definition XM_SUP_WORKER_LIST (R : rstate) : Z :=
  rec_spill_frees R * mo_free MT + XM_ANSWER MT (snd (sup_worker_list_m R)).
(* the callees' contracts, and the bridge from the image's object addresses to the listing's atoms *)
Hypothesis TRCF : forall fx0 : YK11.FPState, @trec_calls_free_spec fx0 rc SK PI B MT.
Hypothesis TREC_SHAPE_OF : forall fx0 : YK11.FPState, @trec_shape_of_spec fx0 rc SK PI B MT.
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.
Hypothesis VOBJS : cmd_val_objs.
Definition tsup_worker_list_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (R : rstate) (O : list (Z * Z)),
afn_pre SEGS B SUP_WORKER_LIST_STK ly S W regs mem md ch ->
(* rounding mode 0 (frm = fcsr bits 5..7): the printf wrappers' frm0_entry; apost_baseF gives it back after a call *)
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
(* the read-only bytes of the image and their addresses: the verb name RO_lit_21d80 (0x21d80, 11 bytes) and what
   rec_shape_of and answer read *)
cmd_ro_ok (rdW W mem) ->
rec_repA B ly S (rdW W mem) R O ->
(* room for one more side-stack frame: answer takes one of class 7 *)
Z.of_nat (length (frames S)) <= 8 ->
st_nev S + EV_SUP_WORKER_LIST R <= EV_MAX -> blocks_bytes S + LIVE_SUP_WORKER_LIST R <= LIVE_MAX ->
mo_ok MT S (XM_SUP_WORKER_LIST R) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_sup_worker_list) regs mem md)
(apost_baseF SEGS B SUP_WORKER_LIST_STK
 ((A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O)
 regs ly S W mem md (EV_SUP_WORKER_LIST R)
(fun ly' S' W' regs' mem' md' => exists (R' : rstate) (t : list byte) (q : Z) (O' : list (Z * Z)),
 (* the model's step: the recorder's new state and the reply text (plain lib/Prog/sup_worker_list_c.v:28-50) *)
 sup_worker_list_m R = (R', t) /\
 getr regs' 10 = w64 q /\ 4096 <= q < 2 ^ 64 /\
 rec_repA B ly' S' (rdW W' mem') R' O' /\
 (* the recorder owns what it owned, less what it freed, plus the blocks it made in this call *)
 (forall pn, In pn O' -> In pn O \/ ~ In pn (ablocks B ly S)) /\
 (* the caller's copy of the reply text: a block of its own, which the recorder does not own and which is none of
    the blocks that were live and none of the recorder's (record()'s spill arm and answer free recorder blocks,
    whose address and size malloc may hand out again) *)
 In (q, Z.of_nat (length t) + 1) (ablocks B ly' S') /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> pn <> (q, Z.of_nat (length t) + 1)) /\ ~ In q (map fst O') /\
 astr_atR (rdW W' mem') q t /\
 (* every block that was live and none of the recorder's is still live, and apart from the copy *)
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O ->
    In pn (ablocks B ly' S') /\ iv_apart (fst pn) (snd pn) q (Z.of_nat (length t) + 1)) /\
 (forall pn, In pn (ablocks B ly' S') ->
    (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O' \/ pn = (q, Z.of_nat (length t) + 1)) /\
 blocks_bytes S' <= blocks_bytes S + LIVE_SUP_WORKER_LIST R /\
 mo_le MT S S' (XM_SUP_WORKER_LIST R))).
End e.
End f.
End d.
