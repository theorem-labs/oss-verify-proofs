(* The contract of sup_remove_all on the ASan build of plugin-hostd/fuzz_command.
   The post is FP-existential (apost_baseF, the printf wrappers' shared post); the pre carries rounding mode 0.
   The callees' contracts are taken at every FP state (forall fx0), so a walk can use them at the fx' a call returns.

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): afn_pre at the entry,
   SRr of apost_base at the return; the meter as cgif's (lib/YC7x.v:88, :92). Functional content: fuzz_command's own
   released plain contract lib/Prog/sup_remove_all_c.v:17-58 (sup_remove_all_sizes :17-18, sup_remove_all_ret
   :27-48, the contract :50-58) and the model lib/Prog/RecModel.v:121-122 (`sup_remove_all_m R = rec_stub R
   REC_REMOVE_ALL [] REC_MOD_HOST_SHAPE true`, with rec_stub :73-75, rec_record :38-39, rec_answer :47-50).
   sup_remove_all() (recorder.c:331-334, record() inlined :205-221) records the call REC_REMOVE_ALL, without
   arguments, in the next slot of g_rec's table (or, when the table holds 16 calls, in record.spill after
   rec_calls_free(&spill, 1) freed the spill's old arguments), restores its frame and tail-calls
   answer(c, REC_MOD_HOST_SHAPE, 1) (`j answer`, 0x8acf8; the shape is the literal "resp 0" at 0x21ce0).

   Addresses: entry BASE + AF_sup_remove_all = 0x8ac44 (M, the pinned image). 55 instructions, no loop, no
   side-stack frame of its own; 2 inline checks (store4 of c->fn and of c->nargs; each reads the shadow byte at
   (a >> 3) + 0x7fff8000 of a byte of g_rec or record.spill, which the allocator record marks usable (CmdRecFacts'
   cmd_addressable_chk), so the error path, a call of `__asan_report_*`, is not reached); callees: rec_calls_free,
   answer (tail). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import rec_calls_free_c answer_c.
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
(* the stack this call needs: its own 32-byte frame (no realignment) above rec_calls_free; answer runs at the entry
   sp after the tail call *)
Definition SUP_REMOVE_ALL_STK : Z := Z.max (32 + REC_CALLS_FREE_STK) ANSWER_STK.
(* the events: record()'s spill arm frees the spill's arguments (EV_REC_CALLS_FREE [l_spill Q], which is CmdRep's
   rec_spill_frees R: 0 while the table holds fewer than 16 calls, recorder.c:210-215), then answer. A function of
   the recorder state, as ev_calls is (the statements' rule for events). *)
Definition EV_SUP_REMOVE_ALL (R : rstate) : Z := rec_spill_frees R + EV_ANSWER.
(* the live bytes the call adds: answer's two copies of the text t (plain sup_remove_all_sizes) *)
Definition LIVE_SUP_REMOVE_ALL (t : list byte) : Z := LIVE_ANSWER t.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the meter the call spends: the spill's frees (rec_calls_free's XM_REC_CALLS_FREE MT [l_spill Q]), then
   answer's *)
Definition XM_SUP_REMOVE_ALL (R : rstate) (t : list byte) : Z := rec_spill_frees R * mo_free MT + XM_ANSWER MT t.
(* the callees' contracts, and the bridge for the addresses of g_rec, record.spill and the shape "resp 0" *)
Hypothesis TREC_CALLS_FREE : forall fx0 : YK11.FPState, @trec_calls_free_spec fx0 rc SK PI B MT.
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.
Hypothesis VOBJS : cmd_val_objs.
Definition tsup_remove_all_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (R : rstate) (O : list (Z * Z)),
let t := snd (sup_remove_all_m R) in
afn_pre SEGS B SUP_REMOVE_ALL_STK ly S W regs mem md ch ->
(* rounding mode 0 (frm = fcsr bits 5..7): the printf wrappers' frm0_entry; apost_baseF gives it back after a call *)
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
(* room for answer's side-stack frame (class 7) *)
Z.of_nat (length (frames S)) <= 8 ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
(* the read-only bytes of the image: the shape "resp 0" RO_lit_21ce0, the format "resp %d" RO_lit_21d00, the FNV
   basis RO_lit_10330. The stack-protector GOT word and guard cell for answer's snprintf are CmdRecFacts'
   cmd_rec_cells. *)
cmd_ro_ok (rdW W mem) ->
(* every byte of those objects lies in the read-only part of the image (answer's astr_argA asks it of the shape;
   the other conjuncts of its read-only branch are cif_ro_unowned and cmd_addressable_chk) *)
rec_repA B ly S (rdW W mem) R O ->
st_nev S + EV_SUP_REMOVE_ALL R <= EV_MAX -> blocks_bytes S + LIVE_SUP_REMOVE_ALL t <= LIVE_MAX ->
mo_ok MT S (XM_SUP_REMOVE_ALL R t) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_sup_remove_all) regs mem md)
(apost_baseF SEGS B SUP_REMOVE_ALL_STK
 (* g_rec's ncalls, call table and answer, g_rec.state, record.spill; the recorder's blocks (the spill's old
    arguments and the old answer may be freed; plain call_post_rec ... rec_area (map fst O),
    sup_remove_all_c.v:33) *)
 ((A_G_REC + OFF_NCALLS, A_G_REC + OFF_NCALLS + 4) :: (A_G_REC + OFF_CALLS, A_G_REC + OFF_ANSWER + 8) ::
  (A_G_REC + OFF_STATE, A_G_REC + OFF_STATE + 8) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O)
 regs ly S W mem md (EV_SUP_REMOVE_ALL R)
(fun ly' S' W' regs' mem' md' => exists R' O' q,
 sup_remove_all_m R = (R', t) /\
 let n := Z.of_nat (length t) + 1 in
 getr regs' 10 = w64 q /\ 4096 <= q < 2 ^ 64 /\
 (* the recorder's state after the call (plain sup_remove_all_c.v:30, :35) *)
 rec_repA B ly' S' (rdW W' mem') R' O' /\
 (forall pn, In pn O' -> In pn O \/ ~ In pn (ablocks B ly S)) /\
 (* the blocks: the caller's kept, the recorder's new set, and the returned text (plain
    sup_remove_all_c.v:36-43) *)
 (forall pn, In pn (ablocks B ly' S') -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O' \/ pn = (q, n)) /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B ly' S')) /\
 In (q, n) (ablocks B ly' S') /\ (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> pn <> (q, n)) /\
 ~ In q (map fst O') /\
 astr_atR (rdW W' mem') q t /\
 blocks_bytes S' <= blocks_bytes S + LIVE_SUP_REMOVE_ALL t /\
 mo_le MT S S' (XM_SUP_REMOVE_ALL R t))).
End e.
End f.
End d.
