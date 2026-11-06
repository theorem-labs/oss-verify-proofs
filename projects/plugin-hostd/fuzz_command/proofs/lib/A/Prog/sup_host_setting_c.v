(* The contract of sup_host_setting on the ASan build of plugin-hostd/fuzz_command.
   The post is FP-existential (apost_baseF, the printf wrappers' shared post); the pre carries rounding mode 0.
   The callees' contracts are taken at every FP state (forall fx0), so a walk can use them at the fx' a call returns.

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): afn_pre at the entry,
   SRr of apost_base at the return, the meter as cgif's trawnew_specX (:88, :92). Functional content:
   fuzz_command's own released plain contract lib/Prog/sup_host_setting_c.v:17-66 and the model
   lib/Prog/RecModel.v:131-133 (`sup_host_setting_m`, which records the canonical line, the token count and the
   tokens joined by single spaces, and folds the call into the host_settings digest with `rec_mix_host`,
   RecModel.v:43).
   sup_host_setting (recorder.c:355-377) records the call with record() (inlined, recorder.c:205-221: a new slot
   of g_rec.calls, or record.spill with its arguments freed when the table already holds 16 calls), adds the
   canonical line with arg_line and the token count with arg_i, adds up the tokens' lengths with the strlen
   wrapper, allocates that many bytes plus one (xmalloc inlined: the malloc wrapper, then the abort on a null
   result, which the live-bytes premise and the LMAX bound exclude), joins the tokens into it (a separator
   written inline as two bytes, then the strcat wrapper per token), adds the joined text with arg_s (xstrdup),
   frees it, and folds the call into g_rec.host_settings (+ 952) with mix_call. It returns no value and calls no
   answer.

   Addresses: entry BASE + AF_sup_host_setting = 0x8b094 (M, the pinned image). 201 instructions, 10 (load4:2
   load8:2 store1:1 store4:2 store8:1 store_n:2) inline checks -- the only two `__asan_report_store_n` sites of
   the program, the two-byte separator store of the join loop -- two loops (one pass per token each, at most 64),
   no side-stack frame of its own. The error path of each check (a call of `__asan_report_*`) is not reached: the
   slot lies in g_rec or record.spill, which the allocator record marks usable (CmdRecFacts' cmd_addressable_chk);
   the pointer array is in a live
   block or in a side-stack frame; and the separator's two bytes lie inside the block the malloc wrapper just
   marked usable, which holds hs_words_len toks + 1 bytes. Callees: rec_calls_free, arg_line, arg_i, xstrdup,
   mix_call; the malloc, strlen, strcat and free wrappers. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import rec_calls_free_c arg_line_c arg_i_c xstrdup_c mix_call_c.
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
(* the bytes the joined word list needs, the plain proof's sup_host_setting_len
   (lib/Prog/sup_host_setting_c.v:17-18): one for each token's NUL, which the loop adds up with the strlen
   wrapper *)
Definition hs_words_len (toks : list (list byte)) : Z :=
  fold_right (fun w s => Z.of_nat (length w) + 1 + s) 0 toks.
(* the stack this call needs: its own 112-byte frame and the deepest callee (the malloc and free wrappers
   ask for ASTACK, cgif lib/YG0d.v:17; the strcat wrapper for 2 * ESTACK and the strlen wrapper for ESTACK,
   the runtime-entry proofs' windows). It calls no answer, so nothing is taken beside the frame *)
Definition SUP_HOST_SETTING_STK : Z :=
  112 +
  Z.max REC_CALLS_FREE_STK (Z.max ARG_LINE_STK (Z.max ARG_I_STK (Z.max XSTRDUP_STK (Z.max MIX_CALL_STK (ASTACK))))).
(* the allocator events: the frees of record()'s spill arm, the canonical line, the token count, the malloc
   of the joined word list, its copy, and its free *)
Definition EV_SUP_HOST_SETTING (R : rstate) : Z := rec_spill_frees R + EV_ARG_LINE + EV_ARG_I + 1 + EV_XSTRDUP + 1.
(* the live bytes the call adds at its peak: the canonical line, the token count, the joined word list and
   its copy *)
Definition LIVE_SUP_HOST_SETTING (R : rstate) (line : list byte) (toks : list (list byte)) : Z :=
  LIVE_ARG_LINE line + LIVE_ARG_I (Z.of_nat (length toks)) + (hs_words_len toks + 1) + LIVE_XSTRDUP (join_sp toks).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the meter the call spends: the spill arm's frees, the two recorded arguments, the word list with its
   copy, and the word list's free *)
Definition XM_SUP_HOST_SETTING (R : rstate) (line : list byte) (toks : list (list byte)) : Z :=
  rec_spill_frees R * mo_free MT + XM_ARG_LINE MT line +
  XM_ARG_I MT (Z.of_nat (length toks)) + mo_malloc MT (hs_words_len toks + 1) +
  XM_XSTRDUP MT (join_sp toks) + mo_free MT.
(* the callees' contracts, and the bridge from the image's object addresses to the listing's atoms *)
Hypothesis TRCF : forall fx0 : YK11.FPState, @trec_calls_free_spec fx0 rc SK PI B MT.
Hypothesis TARG_LINE : forall fx0 : YK11.FPState, @targ_line_spec fx0 rc SK PI B MT.
Hypothesis TARG_I : forall fx0 : YK11.FPState, @targ_i_spec fx0 rc SK PI B MT.
Hypothesis TXSTRDUP : forall fx0 : YK11.FPState, @txstrdup_spec fx0 rc SK PI B MT.
Hypothesis TMIX_CALL : forall fx0 : YK11.FPState, @tmix_call_spec fx0 rc SK PI B MT.
Hypothesis AMALLOC4 : forall fx0 : YK11.FPState, @amalloc04_rule fx0 rc SK SEGS B MT.
Hypothesis AFREE4 : forall fx0 : YK11.FPState, @afree04_rule fx0 rc SK SEGS B MT.
Hypothesis ASTRLEN : forall fx0 : YK11.FPState, @astrlen_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strlen).
Hypothesis ASTRCAT : forall fx0 : YK11.FPState, @astrcat_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strcat).
Hypothesis VOBJS : cmd_val_objs.
Definition tsup_host_setting_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (pl ptok : Z) (ps : list Z) (line : list byte)
  (toks : list (list byte)) (R : rstate) (O : list (Z * Z)),
afn_pre SEGS B SUP_HOST_SETTING_STK ly S W regs mem md ch ->
(* rounding mode 0 (frm = fcsr bits 5..7): the printf wrappers' frm0_entry; apost_baseF gives it back after a call *)
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
(* the read-only bytes of the image and their addresses: the "%d" format arg_i prints with
   (RO_lit_21f00), the separator " " the join writes inline, and the FNV-1a offset basis mix_call reads
   (RO_lit_10330). The stack-protector GOT word and guard cell for arg_i's snprintf are CmdRecFacts'
   cmd_rec_cells. *)
cmd_ro_ok (rdW W mem) ->
getr regs 10 = w64 pl -> 0 <= pl < 2 ^ 64 -> getr regs 11 = w64 ptok -> 0 <= ptok < 2 ^ 64 ->
getr regs 12 = w64 (Z.of_nat (length toks)) -> (1 <= length toks <= 64)%nat ->
(* the line: a string of at most LMAX bytes inside a live block that is none of the recorder's (the plain proof's
   str_arg, lib/Prog/RecKindB.v:164-175). The one caller, verbs_receive, passes its strndup line (0x8deac), so the
   block form, not astr_argA; arg_line's strlen reads its tail by cmd_heap_tail_vis *)
in_blockA (ablocks B ly S) pl (Z.of_nat (length line) + 1) /\
Forall (fun qk => iv_apart pl (Z.of_nat (length line) + 1) (fst qk) (snd qk)) O /\
astr_atR (rdW W mem) pl line /\ Z.of_nat (length line) + 1 <= LMAX + 1 ->
ptok <> 0 -> ptok mod 8 = 0 ->
(* the array of token pointers: in the caller's side-stack frame (verbs_receive's tok[64], class 4), or
   in a live block that is none of the recorder's *)
(afobj SEGS B ly S W mem ptok (8 * Z.of_nat (length toks)) \/
 (in_blockA (ablocks B ly S) ptok (8 * Z.of_nat (length toks)) /\
  Forall (fun qk => iv_apart ptok (8 * Z.of_nat (length toks)) (fst qk) (snd qk)) O)) ->
length ps = length toks ->
(* each pointer, an 8-byte word read as a 64-bit value *)
(forall i p, nth_error ps i = Some p -> 0 <= p < 2 ^ 64 /\ aval_mem (rdW W mem) (ptok + 8 * Z.of_nat i) 8 p) ->
(* every token is a string of its own inside a live block that is none of the recorder's (verbs_receive's tokens
   are words of its strdup copy, so the block form; the strlen and strcat wrappers read each tail
   by cmd_heap_tail_vis), and the joined list fits one message (plain sup_host_setting_c.v:59-60) *)
Forall2 (fun p w => in_blockA (ablocks B ly S) p (Z.of_nat (length w) + 1) /\
  Forall (fun qk => iv_apart p (Z.of_nat (length w) + 1) (fst qk) (snd qk)) O /\
  astr_atR (rdW W mem) p w /\ Z.of_nat (length w) + 1 <= LMAX + 1) ps toks ->
hs_words_len toks <= LMAX + 1 ->
rec_repA B ly S (rdW W mem) R O ->
(* room for one more side-stack frame: arg_i takes one of class 0 *)
Z.of_nat (length (frames S)) <= 8 ->
st_nev S + EV_SUP_HOST_SETTING R <= EV_MAX -> blocks_bytes S + LIVE_SUP_HOST_SETTING R line toks <= LIVE_MAX ->
mo_ok MT S (XM_SUP_HOST_SETTING R line toks) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_sup_host_setting) regs mem md)
(apost_baseF SEGS B SUP_HOST_SETTING_STK
 ((A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O)
 regs ly S W mem md (EV_SUP_HOST_SETTING R)
(fun ly' S' W' regs' mem' md' => exists O' : list (Z * Z),
 (* the recorder's state after the call: the call recorded with the canonical line, the token count and
    the joined words, and folded into g_rec.host_settings (plain lib/Prog/sup_host_setting_c.v:31-45) *)
 rec_repA B ly' S' (rdW W' mem') (sup_host_setting_m R line toks) O' /\
 (* the recorder owns what it owned plus the block it made in this call *)
 (forall pn, In pn O' -> In pn O \/ ~ In pn (ablocks B ly S)) /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B ly' S')) /\
 (forall pn, In pn (ablocks B ly' S') -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O') /\
 blocks_bytes S' <= blocks_bytes S + LIVE_SUP_HOST_SETTING R line toks /\
 mo_le MT S S' (XM_SUP_HOST_SETTING R line toks))).
End e.
End f.
End d.
