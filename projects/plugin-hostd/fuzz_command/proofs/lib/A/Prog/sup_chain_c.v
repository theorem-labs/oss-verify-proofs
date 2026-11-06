(* The contract of sup_chain on the ASan build of plugin-hostd/fuzz_command.
   The post is FP-existential (apost_baseF, the printf wrappers' shared post); the pre carries rounding mode 0.
   The callees' contracts are taken at every FP state (forall fx0), so a walk can use them at the fx' a call returns.

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): afn_pre at the entry,
   SRr of apost_base at the return; the fresh block the caller gets as cgif's trawnew_specX states one
   (lib/YC7x.v:93-101), the meter as there (:88, :92). Functional content: fuzz_command's own released plain
   contract lib/Prog/sup_chain_c.v:18-70 and the model lib/Prog/RecModel.v:101-102 (`sup_chain_m`, `rec_stub` of
   the REC id 17 with the instance number, the member count and the member list `dec_list ids`, RecModel.v:70-71,
   :73-75).
   sup_chain (recorder.c:464-479) records the call with record() (inlined, recorder.c:205-221: a new slot of
   g_rec.calls, or record.spill with its arguments freed when the table already holds 16 calls), allocates a text
   of 12n + 1 bytes for the member list (xmalloc inlined: the malloc wrapper, then the abort on a null result,
   which the live-bytes premise and 12n + 1 <= 745 < MALLOC_MAX exclude), adds the instance number and the member
   count with arg_i, prints the members into the text one at a time with the sprintf wrapper, adds the text with
   arg_s (xstrdup) and frees it, asks rec_shape_of for the shape the verb "chain" declares and tail-jumps to
   answer with changes = 1. It releases its own frame before the jump, so answer runs at this function's entry
   stack pointer.

   Addresses: entry BASE + AF_sup_chain = 0x8c2b4 (M, the pinned image). 169 instructions, 7 (load4:3 store1:1
   store4:2 store8:1) inline checks, one loop (one pass per member, at most 62), no side-stack frame of its own.
   The error path of each check (a call of `__asan_report_*`) is not reached: the slot lies in g_rec or
   record.spill, whose shadow cmd_addressable_chk (lib/A/Prog/CmdRecFacts.v) shows usable; the member array is in
   a live block or in a side-stack frame; and the text's first byte is in the block the malloc wrapper just marked
   usable. Callees: rec_calls_free, arg_i (twice), xstrdup, rec_shape_of, answer; the malloc, sprintf and free
   wrappers. The stack-protector cells the musl body under the sprintf wrapper compares are cmd_rec_cells. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import rec_calls_free_c arg_i_c xstrdup_c rec_shape_of_c answer_c.
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
(* the stack this call needs: its own 112-byte frame and the deepest callee reached with the frame up (the
   malloc and free wrappers ask for ASTACK, cgif lib/YG0d.v:17; the sprintf wrapper for 3 * ESTACK, by
   measurement); the tail jump `j answer` runs answer at this function's entry sp, so its need is taken
   beside the frame, not on top of it *)
Definition SUP_CHAIN_OWN : Z :=
  112 + Z.max REC_CALLS_FREE_STK (Z.max ARG_I_STK (Z.max XSTRDUP_STK
        (Z.max REC_SHAPE_OF_STK (Z.max ASTACK (3 * ESTACK))))).
Definition SUP_CHAIN_STK : Z := Z.max SUP_CHAIN_OWN ANSWER_STK.
(* the allocator events: the frees of record()'s spill arm, the malloc of the list text, the two recorded
   numbers, the copy of the list text, its free, and answer's three *)
Definition EV_SUP_CHAIN (R : rstate) : Z :=
  rec_spill_frees R + 1 + EV_ARG_I + EV_ARG_I + EV_XSTRDUP + 1 + EV_ANSWER.
(* the live bytes the call adds at its peak: the list text of 12n + 1 bytes, the two numbers, the copy of
   the list text, and answer's two copies of the reply *)
Definition LIVE_SUP_CHAIN (R : rstate) (id : Z) (ids : list Z) : Z :=
  12 * Z.of_nat (length ids) + 1 + LIVE_ARG_I id + LIVE_ARG_I (Z.of_nat (length ids)) +
  LIVE_XSTRDUP (dec_list ids) + LIVE_ANSWER (snd (sup_chain_m R id ids)).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the meter the call spends: the spill arm's frees, the list text and its free, the recorded arguments,
   and answer's *)
Definition XM_SUP_CHAIN (R : rstate) (id : Z) (ids : list Z) : Z := rec_spill_frees R * mo_free MT +
  mo_malloc MT (12 * Z.of_nat (length ids) + 1) + XM_ARG_I MT id + XM_ARG_I MT (Z.of_nat (length ids)) +
  XM_XSTRDUP MT (dec_list ids) + mo_free MT + XM_ANSWER MT (snd (sup_chain_m R id ids)).
(* the callees' contracts, and the bridge from the image's object addresses to the listing's atoms *)
Hypothesis TRCF : forall fx0 : YK11.FPState, @trec_calls_free_spec fx0 rc SK PI B MT.
Hypothesis TARG_I : forall fx0 : YK11.FPState, @targ_i_spec fx0 rc SK PI B MT.
Hypothesis TXSTRDUP : forall fx0 : YK11.FPState, @txstrdup_spec fx0 rc SK PI B MT.
Hypothesis TREC_SHAPE_OF : forall fx0 : YK11.FPState, @trec_shape_of_spec fx0 rc SK PI B MT.
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.
Hypothesis AMALLOC4 : forall fx0 : YK11.FPState, @amalloc04_rule fx0 rc SK SEGS B MT.
Hypothesis AFREE4 : forall fx0 : YK11.FPState, @afree04_rule fx0 rc SK SEGS B MT.
Hypothesis ASPRINTF : forall fx0 : YK11.FPState, @asprintf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_sprintf) 0xa7098 0x6045d8.
Hypothesis VOBJS : cmd_val_objs.
Definition tsup_chain_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (id pids : Z) (ids : list Z) (R : rstate) (O : list (Z * Z)),
afn_pre SEGS B SUP_CHAIN_STK ly S W regs mem md ch ->
(* rounding mode 0 (frm = fcsr bits 5..7): the printf wrappers' frm0_entry; apost_baseF gives it back after a call *)
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
(* the read-only bytes of the image and their addresses: the two formats sprintf prints with, "%d"
   (RO_lit_21f00) for the first member and " %d" (RO_lit_21ee0) for the others, the verb name
   "chain" (RO_lit_21f20, 5 bytes), and what rec_shape_of and answer read *)
cmd_ro_ok (rdW W mem) ->
getr regs 10 = w64 id -> -2 ^ 31 <= id < 2 ^ 31 ->
getr regs 11 = w64 pids -> 0 <= pids < 2 ^ 64 -> getr regs 12 = w64 (Z.of_nat (length ids)) ->
(* the caller (chain_words) passes 1 to 62 members, each a 32-bit int (plain sup_chain_c.v:34), so the
   list text is at most 12 * 62 + 1 = 745 bytes and the malloc cannot fail *)
(1 <= length ids <= 62)%nat -> Forall (fun v => -2 ^ 31 <= v < 2 ^ 31) ids ->
pids <> 0 -> pids mod 4 = 0 ->
(* the array of members: in the caller's side-stack frame (chain_words' ids[64], class 3), or in a live
   block that is none of the recorder's (record() and answer free the recorder's own blocks) *)
(afobj SEGS B ly S W mem pids (4 * Z.of_nat (length ids)) \/
 (in_blockA (ablocks B ly S) pids (4 * Z.of_nat (length ids)) /\
  Forall (fun qk => iv_apart pids (4 * Z.of_nat (length ids)) (fst qk) (snd qk)) O)) ->
abytes_atR (rdW W mem) pids (concat (map le32 ids)) ->
rec_repA B ly S (rdW W mem) R O ->
(* room for one more side-stack frame: answer takes one of class 7, arg_i one of class 0 *)
Z.of_nat (length (frames S)) <= 8 ->
st_nev S + EV_SUP_CHAIN R <= EV_MAX -> blocks_bytes S + LIVE_SUP_CHAIN R id ids <= LIVE_MAX ->
mo_ok MT S (XM_SUP_CHAIN R id ids) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_sup_chain) regs mem md)
(apost_baseF SEGS B SUP_CHAIN_STK
 ((A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O)
 regs ly S W mem md (EV_SUP_CHAIN R)
(fun ly' S' W' regs' mem' md' => exists (R' : rstate) (t : list byte) (q : Z) (O' : list (Z * Z)),
 (* the model's step: the recorder's new state and the reply text (plain lib/Prog/sup_chain_c.v:50-70) *)
 sup_chain_m R id ids = (R', t) /\
 getr regs' 10 = w64 q /\ 4096 <= q < 2 ^ 64 /\
 rec_repA B ly' S' (rdW W' mem') R' O' /\
 (* the recorder owns what it owned, less what it freed, plus the blocks it made in this call *)
 (forall pn, In pn O' -> In pn O \/ ~ In pn (ablocks B ly S)) /\
 (* the caller's copy of the reply text: a block of its own, which the recorder does not own, and none of the
    blocks the call kept (record()'s spill arm and answer free recorder blocks, whose addresses malloc may reuse) *)
 In (q, Z.of_nat (length t) + 1) (ablocks B ly' S') /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> pn <> (q, Z.of_nat (length t) + 1)) /\
 ~ In q (map fst O') /\
 astr_atR (rdW W' mem') q t /\
 (* every block that was live and none of the recorder's is still live, and apart from the copy *)
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O ->
    In pn (ablocks B ly' S') /\ iv_apart (fst pn) (snd pn) q (Z.of_nat (length t) + 1)) /\
 (forall pn, In pn (ablocks B ly' S') ->
    (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O' \/ pn = (q, Z.of_nat (length t) + 1)) /\
 blocks_bytes S' <= blocks_bytes S + LIVE_SUP_CHAIN R id ids /\
 mo_le MT S S' (XM_SUP_CHAIN R id ids))).
End e.
End f.
End d.
