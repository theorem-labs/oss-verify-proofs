(* The contract of sup_connect on the ASan build of plugin-hostd/fuzz_command.
   The post is FP-existential (apost_baseF, the printf wrappers' shared post); the pre carries rounding mode 0.
   The callees' contracts are taken at every FP state (forall fx0), so a walk can use them at the fx' a call returns.

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): afn_pre at the entry,
   SRr of apost_base at the return; the meter as cgif's (lib/YC7x.v:88, :92). Functional content: fuzz_command's own
   released plain contract lib/Prog/sup_connect_c.v:17-70 (sup_connect_sizes :17-21, sup_connect_ret :30-52, the
   contract :54-70) and the model lib/Prog/RecModel.v:124-126 (`sup_connect_m R verb line port_a port_b = rec_stub R
   REC_CONNECT [sarg verb; canon line; sarg port_a; sarg port_b] REC_MOD_HOST_SHAPE true`, with sarg :60-61,
   rec_stub :73-75, rec_record :38-39, rec_answer :47-50).
   sup_connect(verb, line, port_a, port_b) (recorder.c:336-345, record() and arg_s inlined :205-227) records the
   call REC_CONNECT in the next slot of g_rec's table (or, when the table holds 16 calls, in record.spill after
   rec_calls_free(&spill, 1) freed the spill's old arguments), appends xstrdup(verb or "(null)"), arg_line(c, line),
   xstrdup(port_a or "(null)"), xstrdup(port_b or "(null)"), restores its frame and tail-calls
   answer(c, REC_MOD_HOST_SHAPE, 1) (`j answer`, 0x8af0c; the shape is the literal "resp 0" at 0x21ce0).

   Addresses: entry BASE + AF_sup_connect = 0x8ad20 (M, the pinned image). 160 instructions, no loop, no side-stack
   frame of its own; 9 inline checks (store4 of c->fn and of c->nargs, 4 load4 of c->nargs and 3 store8 of
   c->args[nargs] around the inlined arg_s; each reads the shadow byte at
   (a >> 3) + 0x7fff8000 of a byte of g_rec or record.spill, which the allocator record marks usable (CmdRecFacts'
   cmd_addressable_chk), so the error path, a call of `__asan_report_*`, is not reached); callees: rec_calls_free,
   xstrdup (3), arg_line, answer (tail). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import rec_calls_free_c xstrdup_c arg_line_c answer_c.
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
(* the stack this call needs: its own 80-byte frame (no realignment) above the deepest of rec_calls_free, xstrdup
   and arg_line; answer runs at the entry sp after the tail call *)
Definition SUP_CONNECT_STK : Z :=
Z.max (80 + Z.max REC_CALLS_FREE_STK (Z.max XSTRDUP_STK ARG_LINE_STK)) ANSWER_STK.
(* the events: record()'s spill arm frees the spill's arguments (EV_REC_CALLS_FREE [l_spill Q], which is CmdRep's
   rec_spill_frees R: 0 while the table holds fewer than 16 calls, recorder.c:210-215), then the four arguments
   and answer. A function of the recorder state, as ev_calls is (this port's decision). *)
Definition EV_SUP_CONNECT (R : rstate) : Z :=
rec_spill_frees R + EV_XSTRDUP + EV_ARG_LINE + EV_XSTRDUP + EV_XSTRDUP + EV_ANSWER.
(* the live bytes the call adds: the four arguments and answer's two copies of the text t (plain
   sup_connect_sizes) *)
Definition LIVE_SUP_CONNECT (verb : option (list byte)) (line : list byte) (port_a port_b : option (list byte))
  (t : list byte) : Z :=
LIVE_XSTRDUP (sarg verb) + LIVE_ARG_LINE line + LIVE_XSTRDUP (sarg port_a) + LIVE_XSTRDUP (sarg port_b) +
LIVE_ANSWER t.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the meter the call spends: the spill's frees (rec_calls_free's XM_REC_CALLS_FREE MT [l_spill Q]), then the
   callees' own *)
Definition XM_SUP_CONNECT (R : rstate) (verb : option (list byte)) (line : list byte)
  (port_a port_b : option (list byte)) (t : list byte) : Z :=
rec_spill_frees R * mo_free MT + XM_XSTRDUP MT (sarg verb) + XM_ARG_LINE MT line + XM_XSTRDUP MT (sarg port_a) +
XM_XSTRDUP MT (sarg port_b) + XM_ANSWER MT t.
(* the callees' contracts, and the bridge for the addresses of g_rec, record.spill, "(null)" and the shape
   "resp 0" *)
Hypothesis TREC_CALLS_FREE : forall fx0 : YK11.FPState, @trec_calls_free_spec fx0 rc SK PI B MT.
Hypothesis TXSTRDUP : forall fx0 : YK11.FPState, @txstrdup_spec fx0 rc SK PI B MT.
Hypothesis TARG_LINE : forall fx0 : YK11.FPState, @targ_line_spec fx0 rc SK PI B MT.
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.
Hypothesis VOBJS : cmd_val_objs.
Definition tsup_connect_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (pv pl pa pb : Z) (verb : option (list byte)) (line : list byte)
  (port_a port_b : list byte) (R : rstate) (O : list (Z * Z)),
let t := snd (sup_connect_m R verb line (Some port_a) (Some port_b)) in
afn_pre SEGS B SUP_CONNECT_STK ly S W regs mem md ch ->
(* rounding mode 0 (frm = fcsr bits 5..7): the printf wrappers' frm0_entry; apost_baseF gives it back after a call *)
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
(* room for answer's side-stack frame (class 7) *)
Z.of_nat (length (frames S)) <= 8 ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
(* the read-only bytes of the image: "(null)" RO_lit_22480 (sarg None), the shape "resp 0" RO_lit_21ce0, the
   format "resp %d" RO_lit_21d00, the FNV basis RO_lit_10330. The stack-protector GOT word and guard cell for
   answer's snprintf are CmdRecFacts' cmd_rec_cells. *)
cmd_ro_ok (rdW W mem) ->
(* every byte of those objects lies in the read-only part of the image (astr_argA asks it of "(null)" and of the
   shape; the other conjuncts of its read-only branch are cif_ro_unowned and cmd_addressable_chk; their tails are
   cmd_tail_vis) *)
getr regs 10 = w64 pv -> 0 <= pv < 2 ^ 64 -> getr regs 11 = w64 pl -> 0 <= pl < 2 ^ 64 ->
getr regs 12 = w64 pa -> 0 <= pa < 2 ^ 64 -> getr regs 13 = w64 pb -> 0 <= pb < 2 ^ 64 ->
(* the verb: NULL (None) or a string of at most LMAX bytes in a live block that is none of the recorder's, or in
   the read-only image (plain str_arg, sup_connect_c.v:60, kept as astr_argA), with the tail word
   after its terminator readable, which xstrdup's strlen reads (a literal's by cmd_tail_vis, a block's by
   cmd_heap_tail_vis) *)
astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O pv verb ->
(forall x, verb = Some x -> atail_vis SEGS W mem (pv + Z.of_nat (length x))) ->
(* the line and the two ports: strings of at most LMAX bytes inside live blocks that are none of the recorder's
   (plain str_arg, sup_connect_c.v:61-63). The one caller, verbs_receive, passes its strndup line and two words of
   its strdup copy (0x8de80-0x8de90), so the block form, not astr_argA; the tails that arg_line's
   and xstrdup's strlen read are cmd_heap_tail_vis *)
in_blockA (ablocks B ly S) pl (Z.of_nat (length line) + 1) /\
Forall (fun qk => iv_apart pl (Z.of_nat (length line) + 1) (fst qk) (snd qk)) O /\
astr_atR (rdW W mem) pl line /\ Z.of_nat (length line) + 1 <= LMAX + 1 ->
in_blockA (ablocks B ly S) pa (Z.of_nat (length port_a) + 1) /\
Forall (fun qk => iv_apart pa (Z.of_nat (length port_a) + 1) (fst qk) (snd qk)) O /\
astr_atR (rdW W mem) pa port_a /\ Z.of_nat (length port_a) + 1 <= LMAX + 1 ->
in_blockA (ablocks B ly S) pb (Z.of_nat (length port_b) + 1) /\
Forall (fun qk => iv_apart pb (Z.of_nat (length port_b) + 1) (fst qk) (snd qk)) O /\
astr_atR (rdW W mem) pb port_b /\ Z.of_nat (length port_b) + 1 <= LMAX + 1 ->
rec_repA B ly S (rdW W mem) R O ->
st_nev S + EV_SUP_CONNECT R <= EV_MAX ->
blocks_bytes S + LIVE_SUP_CONNECT verb line (Some port_a) (Some port_b) t <= LIVE_MAX ->
mo_ok MT S (XM_SUP_CONNECT R verb line (Some port_a) (Some port_b) t) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_sup_connect) regs mem md)
(apost_baseF SEGS B SUP_CONNECT_STK
 (* g_rec's ncalls, call table and answer, g_rec.state, record.spill; the recorder's blocks (the spill's old
    arguments and the old answer may be freed; plain call_post_rec ... rec_area (map fst O), sup_connect_c.v:37) *)
 ((A_G_REC + OFF_NCALLS, A_G_REC + OFF_NCALLS + 4) :: (A_G_REC + OFF_CALLS, A_G_REC + OFF_ANSWER + 8) ::
  (A_G_REC + OFF_STATE, A_G_REC + OFF_STATE + 8) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O)
 regs ly S W mem md (EV_SUP_CONNECT R)
(fun ly' S' W' regs' mem' md' => exists R' O' q,
 sup_connect_m R verb line (Some port_a) (Some port_b) = (R', t) /\
 let n := Z.of_nat (length t) + 1 in
 getr regs' 10 = w64 q /\ 4096 <= q < 2 ^ 64 /\
 (* the recorder's state after the call (plain sup_connect_c.v:34, :39) *)
 rec_repA B ly' S' (rdW W' mem') R' O' /\
 (forall pn, In pn O' -> In pn O \/ ~ In pn (ablocks B ly S)) /\
 (* the blocks: the caller's kept, the recorder's new set, and the returned text (plain sup_connect_c.v:40-47) *)
 (forall pn, In pn (ablocks B ly' S') -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O' \/ pn = (q, n)) /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B ly' S')) /\
 In (q, n) (ablocks B ly' S') /\ (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> pn <> (q, n)) /\
 ~ In q (map fst O') /\
 astr_atR (rdW W' mem') q t /\
 blocks_bytes S' <= blocks_bytes S + LIVE_SUP_CONNECT verb line (Some port_a) (Some port_b) t /\
 mo_le MT S S' (XM_SUP_CONNECT R verb line (Some port_a) (Some port_b) t))).
End e.
End f.
End d.
