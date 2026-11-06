(* The contract of sup_add on the ASan build of plugin-hostd/fuzz_command.
   The post is FP-existential (apost_baseF, the printf wrappers' shared post); the pre carries rounding mode 0.
   The callees' contracts are taken at every FP state (forall fx0), so a walk can use them at the fx' a call returns.

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): afn_pre at the entry,
   SRr of apost_base at the return; the meter as cgif's (lib/YC7x.v:88, :92). Functional content: fuzz_command's own
   released plain contract lib/Prog/sup_add_c.v:17-68 (sup_add_sizes :17-21, sup_add_ret :30-52, the contract
   :54-68) and the model lib/Prog/RecModel.v:107-113 (`sup_add_m`: the call REC_ADD with [sarg uri; dec id;
   darg placement "-"; darg client "-"], then "resp -1" for an id outside [0, 10000), the refusal's
   "resp <code>", or the state folded with the call and "resp <id>"; with rec_record :38-39, rec_mix :41,
   hand_back :45).
   sup_add(uri, id, placement, client) (recorder.c:292-312, record() and arg_s inlined :205-227) takes a side-stack
   frame for buf[32], records the call REC_ADD in the next slot of g_rec's table (or, when the table holds 16 calls,
   in record.spill after rec_calls_free(&spill, 1) freed the spill's old arguments), appends xstrdup(uri or
   "(null)"), arg_i(c, id), xstrdup(placement or "-"), xstrdup(client or "-"); then: an id outside [0, 10000)
   (`srliw a0,s3,4; li a1,625; bltu`, 0x8a050-0x8a05c) prints "resp -1" into buf and hands it back; a refusal calls
   answer(c, NULL, 0) (`jal`, 0x8a08c: the frame must be released after it); otherwise g_rec.state := mix_call(
   g_rec.state, c), "resp <id>" into buf, hand_back(buf).

   Addresses: entry BASE + AF_sup_add = 0x89dbc (M, the pinned image). 287 instructions, no loop; 9 inline checks
   (store4 of c->fn and of c->nargs, 4 load4 of c->nargs and 3 store8 of c->args[nargs] around the inlined arg_s;
   each reads the shadow byte at (a >> 3) + 0x7fff8000 of a byte of g_rec or record.spill, which the allocator record
   marks usable (CmdRecFacts' cmd_addressable_chk), so the error path, a call of `__asan_report_*`, is not reached);
   a side-stack frame of class 1
   (`__asan_stack_malloc_1`, request 96 bytes, buf at frame + 32, released inline: shadow 0xf5 and the flag byte);
   the real-stack fallback and its one-pass probe loop are not taken (this port's decision: the use-after-return flag is
   pinned by the allocator record); callees: rec_calls_free, xstrdup (3), arg_i, mix_call, the snprintf wrapper,
   hand_back, answer. Walk plan: sup_add's (its `spZ regs mod 32 = 0` premise is dropped:
   sup_add realigns with `andi sp,sp,-32` at 0x89dfc, and the 16 bytes of slack are in SUP_ADD_STK). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_calls_free_c xstrdup_c arg_i_c mix_call_c hand_back_c answer_c.
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
(* the stack this call needs: its own 160-byte frame, 16 more for the realignment `andi sp,sp,-32` (sp mod 16 = 0
   at the entry, afn_pre's astk_ok), and the deepest callee: the side-stack entry's window (ESTACK), the snprintf
   wrapper's (3 * ESTACK, a measured 6,672 bytes below the trampoline's entry sp), rec_calls_free's,
   xstrdup's, arg_i's, mix_call's, hand_back's and
   answer's own needs (answer by `jal` here, so under sup_add's frame) *)
Definition SUP_ADD_STK : Z :=
160 + 16 + Z.max ESTACK (Z.max (3 * ESTACK) (Z.max REC_CALLS_FREE_STK (Z.max XSTRDUP_STK (Z.max ARG_I_STK
  (Z.max MIX_CALL_STK (Z.max HAND_BACK_STK ANSWER_STK)))))).
(* the events: record()'s spill arm frees the spill's arguments (EV_REC_CALLS_FREE [l_spill Q], which is CmdRep's
   rec_spill_frees R: 0 while the table holds fewer than 16 calls, recorder.c:210-215), the four arguments, then
   answer or hand_back. A function of the recorder state, as ev_calls is (this port's decision for event counts). *)
Definition EV_SUP_ADD (R : rstate) : Z :=
rec_spill_frees R + EV_XSTRDUP + EV_ARG_I + EV_XSTRDUP + EV_XSTRDUP + Z.max EV_ANSWER EV_HAND_BACK.
(* the live bytes the call adds: the four arguments and the two copies of the text t (plain sup_add_sizes) *)
Definition LIVE_SUP_ADD (uri : option (list byte)) (id : Z) (placement client : option (list byte))
  (t : list byte) : Z :=
LIVE_XSTRDUP (sarg uri) + LIVE_ARG_I id + LIVE_XSTRDUP (darg placement (bstr "-"%string)) +
LIVE_XSTRDUP (darg client (bstr "-"%string)) + Z.max (LIVE_ANSWER t) (LIVE_HAND_BACK t).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the meter the call spends: the spill's frees (rec_calls_free's XM_REC_CALLS_FREE MT [l_spill Q]), then the
   callees' own *)
Definition XM_SUP_ADD (R : rstate) (uri : option (list byte)) (id : Z) (placement client : option (list byte))
  (t : list byte) : Z :=
rec_spill_frees R * mo_free MT + XM_XSTRDUP MT (sarg uri) + XM_ARG_I MT id +
XM_XSTRDUP MT (darg placement (bstr "-"%string)) + XM_XSTRDUP MT (darg client (bstr "-"%string)) +
Z.max (XM_ANSWER MT t) (XM_HAND_BACK MT t).
(* the callees' contracts, the runtime entries with this tree's and cgif's names, and the bridge for the addresses of
   g_rec, record.spill, "-" and "resp %d" *)
Hypothesis TREC_CALLS_FREE : forall fx0 : YK11.FPState, @trec_calls_free_spec fx0 rc SK PI B MT.
Hypothesis TXSTRDUP : forall fx0 : YK11.FPState, @txstrdup_spec fx0 rc SK PI B MT.
Hypothesis TARG_I : forall fx0 : YK11.FPState, @targ_i_spec fx0 rc SK PI B MT.
Hypothesis TMIX_CALL : forall fx0 : YK11.FPState, @tmix_call_spec fx0 rc SK PI B MT.
Hypothesis THAND_BACK : forall fx0 : YK11.FPState, @thand_back_spec fx0 rc SK PI B MT.
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.
Hypothesis ASTACK_MALLOC1 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 1.
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState, @asnprintf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_snprintf) 0xa7098 0x6045d8.
Hypothesis VOBJS : cmd_val_objs.
Definition tsup_add_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (pu id pp pc : Z) (uri : list byte)
  (placement client : option (list byte)) (R : rstate) (O : list (Z * Z)),
let t := snd (sup_add_m R (Some uri) id placement client) in
afn_pre SEGS B SUP_ADD_STK ly S W regs mem md ch ->
(* rounding mode 0 (frm = fcsr bits 5..7): the printf wrappers' frm0_entry; apost_baseF gives it back after a call *)
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
(* room for its own side-stack frame (class 1) and one more under it (arg_i's class 0 or answer's class 7) *)
Z.of_nat (length (frames S)) <= 7 ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
(* the read-only bytes of the image: "-" RO_lit_21d40, the formats "%d" RO_lit_21f00 and "resp %d" RO_lit_21d00
   (their tails: cmd_tail_vis), the FNV basis RO_lit_10330. The stack-protector GOT word and guard cell that musl's
   printf chain behind the snprintf wrapper checks (here and in arg_i and answer) are CmdRecFacts' cmd_rec_cells. *)
cmd_ro_ok (rdW W mem) ->
(* every byte of those objects lies in the read-only part of the image (xstrdup's astr_argA asks it of the
   default "-"; the other conjuncts of its read-only branch are cif_ro_unowned and cmd_addressable_chk) *)
getr regs 10 = w64 pu -> 0 <= pu < 2 ^ 64 -> getr regs 11 = w64 id -> -2 ^ 31 <= id < 2 ^ 31 ->
getr regs 12 = w64 pp -> 0 <= pp < 2 ^ 64 -> getr regs 13 = w64 pc -> 0 <= pc < 2 ^ 64 ->
(* the uri: a string of at most LMAX bytes inside a live block that is none of the recorder's (plain str_arg,
   sup_add_c.v:60). The one caller, verbs_receive, passes the word tok[1] of its strdup copy (0x8da70), never NULL,
   so the block form, not astr_argA; xstrdup's strlen reads its tail by cmd_heap_tail_vis *)
in_blockA (ablocks B ly S) pu (Z.of_nat (length uri) + 1) /\
Forall (fun qk => iv_apart pu (Z.of_nat (length uri) + 1) (fst qk) (snd qk)) O /\
astr_atR (rdW W mem) pu uri /\ Z.of_nat (length uri) + 1 <= LMAX + 1 ->
(* placement and client: NULL (None) or a string of at most LMAX bytes in a live block that is none of the
   recorder's, or in the read-only image (plain str_arg, sup_add_c.v:61; astr_argA is kept), with the
   tail word after the terminator readable, which xstrdup's strlen reads *)
astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O pp placement ->
(forall x, placement = Some x -> atail_vis SEGS W mem (pp + Z.of_nat (length x))) ->
astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O pc client ->
(forall x, client = Some x -> atail_vis SEGS W mem (pc + Z.of_nat (length x))) ->
rec_repA B ly S (rdW W mem) R O ->
st_nev S + EV_SUP_ADD R <= EV_MAX -> blocks_bytes S + LIVE_SUP_ADD (Some uri) id placement client t <= LIVE_MAX ->
mo_ok MT S (XM_SUP_ADD R (Some uri) id placement client t) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_sup_add) regs mem md)
(apost_baseF SEGS B SUP_ADD_STK
 (* g_rec's ncalls, call table and answer, g_rec.state, record.spill; the recorder's blocks (the spill's old
    arguments and the old answer may be freed; plain call_post_rec ... rec_area (map fst O), sup_add_c.v:37) *)
 ((A_G_REC + OFF_NCALLS, A_G_REC + OFF_NCALLS + 4) :: (A_G_REC + OFF_CALLS, A_G_REC + OFF_ANSWER + 8) ::
  (A_G_REC + OFF_STATE, A_G_REC + OFF_STATE + 8) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O)
 regs ly S W mem md (EV_SUP_ADD R)
(fun ly' S' W' regs' mem' md' => exists R' O' q,
 sup_add_m R (Some uri) id placement client = (R', t) /\
 let n := Z.of_nat (length t) + 1 in
 getr regs' 10 = w64 q /\ 4096 <= q < 2 ^ 64 /\
 (* the recorder's state after the call (plain sup_add_c.v:34, :39) *)
 rec_repA B ly' S' (rdW W' mem') R' O' /\
 (forall pn, In pn O' -> In pn O \/ ~ In pn (ablocks B ly S)) /\
 (* the blocks: the caller's kept, the recorder's new set, and the returned text (plain sup_add_c.v:40-47) *)
 (forall pn, In pn (ablocks B ly' S') -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O' \/ pn = (q, n)) /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B ly' S')) /\
 In (q, n) (ablocks B ly' S') /\ (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> pn <> (q, n)) /\
 ~ In q (map fst O') /\
 astr_atR (rdW W' mem') q t /\
 blocks_bytes S' <= blocks_bytes S + LIVE_SUP_ADD (Some uri) id placement client t /\
 mo_le MT S S' (XM_SUP_ADD R (Some uri) id placement client t))).
End e.
End f.
End d.
