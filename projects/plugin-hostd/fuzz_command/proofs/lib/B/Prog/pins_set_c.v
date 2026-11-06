(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: check_reply's ASan walk (fuzz_command.asan, 0x86d78) assembled from its
   segments, as proofs/cgif/cgif_file_fuzzer/lib/A/ACh5.v assembles cgif_close's (pb_cgif_closeX):
     s1 the entry to the memchr call, s2 memchr / check_reply_answer / sup_reply_code, s3 the code's split,
     s4 snprintf, s4b rec_code_declared, s5 strcmp, s6 strlen / rec_shape_of, s7 syntax_reply_matches twice,
     s8 the frame's release and the return.
   snprintf is the only call that changes the FP state, so s4b, s5 and s8 (the segments after it) are taken at every
   FP state and s4 uses them at the state the wrapper returns.
   `pb_check_reply` is tcheck_reply_spec (lib/A/Prog/check_reply_c.v). The walk's facts at the entry that the
   statement no longer states come from its premises: the record's cells (replace_str flag byte, stack guard, errno)
   from CmdRecCells' cmd_rec_cells, the recorder's GOT words from cmd_ro_ok's RO_ptr_a70xx bytes, the read-only
   ranges from CmdRecRo's cmd_ro_in_img, and the words' shadow from AR's zshadow_ok of the stack window
   [ly_stk_lo, ly_stk_hi) (the words lie in it: spZ regs <= w and w + WORDS_W + 12 <= ly_stk_hi ly). The kit lemmas
   take the image facts IMG (cmd_img_facts); the segments take CmdRecImg's cmd_heap_tail_vis, and its
   cmd_prog_unowned and cmd_rom_view_on at IMG, so no record fact is a Section hypothesis (the walk hypotheses keep
   cgif's names; the record facts are lemmas of lib/A/Prog/CmdRecFacts.v). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply.v, with its module paths and module names changed; 64 of its 90 lines of code are new or changed and 126 lines of the source are left out. *)
(* The contract of pins_set on the ASan+UBSan build of plugin-hostd/fuzz_command (fuzz_command.asan-ubsan).
   The post is FP-existential (apost_baseF, the printf wrappers' shared post); the pre carries rounding mode 0.
   The callees' contracts are taken at every FP state (forall fx0), so a walk can use them at the fx' a call returns.

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): afn_pre at the entry,
   SRr of apost_base at the return, the meter as cgif's trawnew_specX (:88, :92). Functional content:
   fuzz_command's own released plain contract lib/Prog/pins_set_c.v:17-58 and the model
   lib/Prog/RecModel.v:89 (`pins_set_m`, `rec_stub_code` of the REC id 20, RecModel.v:77-79). The B twin of
   lib/A/Prog/pins_set_c.v, re-derived on B's code, which calls record() and arg_s() (lib/B/Prog/record_c.v,
   arg_s_c.v) where A inlined them.
   pins_set (recorder.c:510-522) records the call with record(20) (a new slot of g_rec.calls, or record.spill with
   its arguments freed when the table already holds 16 calls), adds its 4 arguments with arg_s (a copy of each
   string; arg_s replaces a NULL string by "(null)", and pins_set itself replaces a NULL verdict by "-", the image
   string at 0x21d80, 0x8c990-0x8c998), and then either answers the input's refusal code (g_rec.code, when
   g_rec.refuse is set) or folds the call into g_rec.state (g_rec + 944) with mix_call and answers SUCCESS. Either
   way it tail-jumps to answer_code (0x8c9f4 `j answer_code`), which turns the code into the text "resp <code>",
   keeps one copy as the recorder's answer and frees the other. It releases its own frame before the jump, so
   answer_code runs at this function's entry stack pointer with the caller's s0 and ra.

   Addresses (B, its disassembly): entry BASE + AF_pins_set = 0x8c938. 48 instructions, no inline ASan check (g_rec
   reached by auipc at constant offsets; the function table: 0 reports), no loop, a 48-byte real frame and no side-stack
   frame of its own (answer_code takes one of class 1), 0 UBSan trap sites (the trap-site summary). Callees: record
   (0x8a728, at 0x8c968), arg_s (0x8a820, at 0x8c974, 0x8c980, 0x8c98c, 0x8c9a4), mix_call (0x8ad54, at 0x8c9c8),
   answer_code (0x8c9f8, tail jump). s0 is the caller's at the record call (afn_pre's achain, carried by
   achain_lower) and the slot (record's result, in g_rec or record.spill, below the
   stack) at the arg_s and mix_call calls; the stack-protector cells the musl body under answer_code's snprintf
   wrapper compares are cmd_rec_cells (CmdRecFacts).
   The arguments: its one caller, pin_set_words, passes the words uri, files and layout of verbs_receive's strdup
   block `copy` (src/verbs.c:86), so those three are heap strings; the verdict is the tail of the fifth word or
   NULL (lib/Spec/Verbs.v:230-233). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import record_c arg_s_c mix_call_c answer_code_c.
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
(* the stack this call needs: its own 48-byte frame and the deepest callee reached with the frame up;
   the tail jump `j answer_code` runs answer_code at this function's entry sp, so its need is taken
   beside the frame, not on top of it. M: the image's function table gives 16608 = 48 + record's 16560 *)
Definition PINS_SET_STK : Z :=
  Z.max (48 + Z.max RECORD_STK (Z.max ARG_S_STK MIX_CALL_STK)) ANSWER_CODE_STK.
(* the allocator events: the frees of record()'s spill arm, the copies of the recorded arguments, and
   answer_code's: hand_back's free and two copies, then the free of the copy it returns *)
Definition EV_PINS_SET (R : rstate) : Z :=
  EV_RECORD R + EV_ARG_S + EV_ARG_S + EV_ARG_S + EV_ARG_S + EV_ANSWER_CODE.
(* the live bytes the call adds at its peak: the recorded arguments and answer_code's two copies of
   the reply text *)
Definition LIVE_PINS_SET (R : rstate) (uri files layout verdict : option (list byte)) : Z :=
  LIVE_ARG_S uri + LIVE_ARG_S files + LIVE_ARG_S layout +
  LIVE_ARG_S (Some (darg verdict (bstr "-"%string))) +
  LIVE_ANSWER_CODE (snd (pins_set_m R uri files layout verdict)).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the meter the call spends: record()'s spill arm, the recorded arguments, and answer_code's *)
Definition XM_PINS_SET (R : rstate) (uri files layout verdict : option (list byte)) : Z :=
  XM_RECORD MT R + XM_ARG_S MT uri + XM_ARG_S MT files + XM_ARG_S MT layout +
  XM_ARG_S MT (Some (darg verdict (bstr "-"%string))) +
  XM_ANSWER_CODE MT (snd (pins_set_m R uri files layout verdict)).
(* the callees' contracts, and the bridge from the image's object addresses to the listing's atoms *)
Hypothesis TRECORD : forall fx0 : YK11.FPState, @trecord_spec fx0 rc SK PI B MT.
Hypothesis TARG_S : forall fx0 : YK11.FPState, @targ_s_spec fx0 rc SK PI B MT.
Hypothesis TMIX_CALL : forall fx0 : YK11.FPState, @tmix_call_spec fx0 rc SK PI B MT.
Hypothesis TANSWER_CODE : forall fx0 : YK11.FPState, @tanswer_code_spec fx0 rc SK PI B MT.
Hypothesis VOBJS : cmd_val_objs.
Definition tpins_set_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (pu : Z) (pf : Z) (pl : Z) (pv : Z)
 (u f l : list byte) (verdict : option (list byte)) (R : rstate) (O : list (Z * Z)),
afn_pre SEGS B PINS_SET_STK ly S W regs mem md ch ->
(* rounding mode 0 (frm = fcsr bits 5..7): the printf wrappers' frm0_entry; apost_baseF gives it back after a call *)
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
(* the read-only bytes of the image and their addresses: the default "-" (0x21d80) of the verdict, arg_s's
   default "(null)" (0x224c0), the FNV-1a offset basis mix_call reads (0x10330), and the format answer_code prints
   with (0x21d40) *)
cmd_ro_ok (rdW W mem) ->
getr regs 10 = w64 pu -> 0 <= pu < 2 ^ 64 ->
getr regs 11 = w64 pf -> 0 <= pf < 2 ^ 64 ->
getr regs 12 = w64 pl -> 0 <= pl < 2 ^ 64 ->
getr regs 13 = w64 pv -> 0 <= pv < 2 ^ 64 ->
(* uri, files and layout: words of verbs_receive's `copy` block, apart from every block the recorder owns (record()
   and answer_code free the recorder's own blocks during the call); their word tails, which arg_s's strlen
   wrapper reads, are readable by cmd_heap_tail_vis. The verdict: such a string, a read-only byte range of the
   image, or NULL (the plain proof's str_arg, lib/Prog/RecKindB.v:164-175), with the bytes after its terminator up
   to the end of that 8-byte word readable (RtDefs.v's atail_vis) *)
in_blockA (ablocks B ly S) pu (Z.of_nat (length u) + 1) ->
Forall (fun qk => iv_apart pu (Z.of_nat (length u) + 1) (fst qk) (snd qk)) O ->
astr_atR (rdW W mem) pu u -> Z.of_nat (length u) + 1 <= LMAX + 1 ->
in_blockA (ablocks B ly S) pf (Z.of_nat (length f) + 1) ->
Forall (fun qk => iv_apart pf (Z.of_nat (length f) + 1) (fst qk) (snd qk)) O ->
astr_atR (rdW W mem) pf f -> Z.of_nat (length f) + 1 <= LMAX + 1 ->
in_blockA (ablocks B ly S) pl (Z.of_nat (length l) + 1) ->
Forall (fun qk => iv_apart pl (Z.of_nat (length l) + 1) (fst qk) (snd qk)) O ->
astr_atR (rdW W mem) pl l -> Z.of_nat (length l) + 1 <= LMAX + 1 ->
astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O pv verdict ->
(forall x, verdict = Some x -> atail_vis SEGS W mem (pv + Z.of_nat (length x))) ->
rec_repA B ly S (rdW W mem) R O ->
(* room for one more side-stack frame: answer_code takes one of class 1 *)
Z.of_nat (length (frames S)) <= 8 ->
st_nev S + EV_PINS_SET R <= EV_MAX ->
blocks_bytes S + LIVE_PINS_SET R (Some u) (Some f) (Some l) verdict <= LIVE_MAX ->
mo_ok MT S (XM_PINS_SET R (Some u) (Some f) (Some l) verdict) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_pins_set) regs mem md)
(apost_baseF SEGS B PINS_SET_STK
 ((A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O)
 regs ly S W mem md (EV_PINS_SET R)
(fun ly' S' W' regs' mem' md' => exists (R' : rstate) (r : Z) (O' : list (Z * Z)),
 (* the model's step: the recorder's new state and the code the pins answer (plain
    lib/Prog/pins_set_c.v:17-58) *)
 pins_set_m R (Some u) (Some f) (Some l) verdict = (R', r) /\
 getr regs' 10 = w64 r /\ -2 ^ 31 <= r < 2 ^ 31 /\
 rec_repA B ly' S' (rdW W' mem') R' O' /\
 (* the recorder owns what it owned, less the old answer answer_code freed and what record() freed, plus the
    blocks it made *)
 (forall pn, In pn O' -> In pn O \/ ~ In pn (ablocks B ly S)) /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B ly' S')) /\
 (forall pn, In pn (ablocks B ly' S') -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O') /\
 blocks_bytes S' <= blocks_bytes S + LIVE_PINS_SET R (Some u) (Some f) (Some l) verdict /\
 mo_le MT S S' (XM_PINS_SET R (Some u) (Some f) (Some l) verdict))).
End e.
End f.
End d.
