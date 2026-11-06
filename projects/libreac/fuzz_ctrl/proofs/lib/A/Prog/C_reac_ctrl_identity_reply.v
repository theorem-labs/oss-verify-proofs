(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the contract and walk of ctrl_finish on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/YC20.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlFinish.v, with its module paths and module names changed; 5922 of its 5983 lines of code are new or changed and 873 lines of the source are left out. *)
(* reac_ctrl_identity_reply (0x83f8c) of fuzz_ctrl's ASan build (image A, libreac v1.9.0).
   Writes the caller's three cells (pa 2 bytes, pp 8, pn 8, objects of the caller's frame), its own
   machine-stack frame, its own class-1 fake frame and that frame's shadow and flag: cgif's caller-journal form
   (the SOURCE of the pattern is cgif_file_fuzzer lib/YC20.v:311-365; that file is NOT ported and is only cited --
   this post is built from ajournal / aregs_preserved / tcj_kept, never from apost_base). Calls
   __asan_stack_malloc_1 (0x84008) and reac_ctrl_parse (0x840f4, contract treac_ctrl_parse_spec of
   C_reac_ctrl_parse.v). Model: Prog/RcReply.v.

   This file holds the accepted spec, one cut invariant per cut C0..C14 of the accepted stretch plan, one stretch
   lemma per stretch with its local helpers (prefix rp_<stretch>_), and the composed theorem
   pb_reac_ctrl_identity_reply, which chains the 16 stretch lemmas. All are proved (Qed); nothing is admitted.
   Its assumptions are the section hypotheses (PARSE = reac_ctrl_parse's contract, LAWS, RELRO_IMG, ...) and
   the allowed primitive axioms plus functional_extensionality_dep.

   Rule 24 (released-proof lookup), run 2026-10-28T21:06:42Z: `proof-index reac_ctrl_identity_reply` exit 1,
   nothing by name or by address; re-run and released-branch grep by a Theorem Labs CHECK lane at
   21:07:57Z / 21:14:55Z: CONFIRM. So this is a new walk in the released cgif structure.

   Sources of the statements: the accepted spec draft reply-A-spec-draft.md (a working note, not in this delivery)
   (a Theorem Labs lane accepted 21:50Z: caller-journal form, fake-frame arm only, +1 room premise; its CTX premise
   dropped there, its achain premise dropped at 00:04Z with parse's P6); the listing of
   a working branch lib/A/Prog/CtrlList.v (slots 3116..3420) and
   CtrlAddr.v; the cgif models cited per lemma below; reac_ctrl_parse's contract from a Theorem Labs lane's file
   lib/A/Prog/C_reac_ctrl_parse.v.

   NAMES: the ctrl PA layer (PaTable, PaSym, PaShadow, PaRun, PaStep, PaJournal, CtrlPa, CtrlPaLib, CtrlBase,
   CtrlFrame, YC85) and the caller-journal shapes tcj_kept / twr_ok / tsrc_ok (CtrlCallerJ.v, grant's
   lib/A/Prog/CtrlFinish.v:111-143 ported) are on this branch since the merge of a working branch
   c0a0ca3d4b2 (now at its frozen head 5c587a76cbc). reac_ctrl_parse's contract comes from a Theorem Labs lane's own file
   lib/A/Prog/C_reac_ctrl_parse.v (merged from a working branch 55301a93133, statement unchanged
   since 93f7070a5f5); its four names are used QUALIFIED (C_reac_ctrl_parse.treac_ctrl_parse_spec /
   .treac_ctrl_parse_post / .REAC_CTRL_PARSE_STK / .A_reac_ctrl_parseP). The six modules that exist in both the
   core and ctrl's lib/A/Reusable (YI04 YI16 YK11 YK1b YM05 YO09) are Required by the core prefix and used as
   lib.Reusable.X.n (porter's rule, 04:24Z / 04:33Z).

   SEGMENTS AND RO (A / B twin decision of Theorem Labs lanes, 23:37Z): every statement here is over the
   walk's segments `AB1v.tfibsegs`, not `pa_segs PI`; the bridge lemma `tfibsegs_rsegs` of lib/A/ProgBridge.v
   carries them to the footprint runs' `Img0.rsegs`. The read-only premise is a Theorem Labs lane's `arodata_okS`
   (Reusable/YE01.v:192, as lib/A/ACfn.v:43 states it: segs, B, RLO, RHI, reader); the PA layer's
   `arodata_okP` is reached from it by the single lemma `arodata_okP_of_S` (a Theorem Labs lane), so nothing is stated
   for it here. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
(* a Theorem Labs lane 21:42Z: the cgif core lands in ctrl's TOP-LEVEL lib/Reusable. Anything whose name collides with a ctrl
   module of the same name is used QUALIFIED; the collided ctrl module is never Imported here. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI16.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YM05.
(* the ctrl PA layer: the position-abstract listing engine and its ctrl instance (merged from
   a working branch c0a0ca3d4b2). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal CtrlSyms CtrlList CtrlAddr CtrlPa CtrlPaLib CtrlBase CtrlFrame YC85.
(* the caller-journal shapes tcj_kept / twr_ok / tsrc_ok (grant's lib/A/Prog/CtrlFinish.v:111-143, ported by a Theorem Labs lane). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import CtrlCallerJ.
(* ctrl's image-A walk kit (the ported generic parts of cgif's AC8a / ACbf / ACj1 / ACja / ACjr), green since
   the merge of a Theorem Labs lane's 411ba2461e4: prreg / pmkst / paj_run_to_tok come from CtrlPaLib, the
   realignment lemmas land_m32 / denot_and_m32 / sp1_facts from CtrlACja. Imported in cgif's own order
   (ACbf, CtrlACjr, ACj1, CtrlACja), so CtrlACja's `evalE ::=` is the one in scope. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import
YC81 YC4b YC1g YC1h YC1i ACbf CtrlACjr ACj1 CtrlACja.
(* qualified only (closure rule, a Theorem Labs lane 23:38Z): the walk's segments, the concrete PA instance and
   a Theorem Labs lane's read-only shape. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require AB1v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require CtrlImg.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YE01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcKind RcRec RcParse RcReply.
(* a Theorem Labs lane's reac_ctrl_parse contract; Required, never Imported (closure rule), so its names are qualified. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require C_reac_ctrl_parse.
(* the concrete instance is the one every PA shape here is resolved with; activated locally so that no name of
   CtrlImg is Imported (closure rule). *)
#[local] Existing Instance CtrlImg.PI_ctrl.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* lia's mod / div handling is switched off for THIS file only (a Theorem Labs lane 09:31Z: a ctrl-authored file never leaves a global
   setting changed at file end); files that Require this one keep their own setting. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Context {SK : lib.Reusable.YI16.sink_head}.
Section d.
(* The PA layer is instantiated with the CONCRETE instance CtrlImg.PI_ctrl (lib/A/Prog/CtrlImg.v:82, whose
   pa_segs is tfibsegs), not with an abstract `Context {PI : PAImg ctrl_listing}` (a Theorem Labs lane 23:49Z, found by
   a Theorem Labs lane): CtrlCallerJ's tcj_kept / twr_ok / tsrc_ok, stated over `world (pa_segs PI)`, then apply to this
   file's statements over tfibsegs because pa_segs PI_ctrl reduces to tfibsegs. *)
#[local] Notation SEGS := AB1v.tfibsegs.
#[local] Notation VAL := (@pa_val _ ctrl_listing CtrlImg.PI_ctrl).
#[local] Notation SIGMA := (@pa_sigma _ ctrl_listing CtrlImg.PI_ctrl).
#[local] Notation BASE := (@pa_val _ ctrl_listing CtrlImg.PI_ctrl A_TEXT).
(* RLO / RHI are Section variables below (a Theorem Labs lane 23:37Z / R3 of section 1.0 of the parse lane's note (a working note, not in this delivery)), not the PAImg fields. *)
Definition A_reac_ctrl_identity_replyP : Z := BASE + AF_reac_ctrl_identity_reply.
(* a Theorem Labs lane's parse spec is lib/A/Prog/C_reac_ctrl_parse.v (merged 98691a4da7b); the three names this file
   spends are qualified to it:
     C_reac_ctrl_parse.A_reac_ctrl_parseP    : Z                        (* := BASE + AF_reac_ctrl_parse *)
     C_reac_ctrl_parse.REAC_CTRL_PARSE_STK   : Z                        (* := 8800 *)
     C_reac_ctrl_parse.treac_ctrl_parse_spec : asyms -> Z -> Z -> Prop  (* over B RLO RHI, {SK} implicit *) *)
(* Its own frame is 128 bytes, realigned to 32 (rA >= sp - 144, 0x83fcc); every call runs at sp = rA:
   __asan_stack_malloc_1 needs ESTACK below it (0x84008), reac_ctrl_parse needs REAC_CTRL_PARSE_STK below it
   (0x840f4; a Theorem Labs lane's announced change of 2026-10-29 07:18Z, C_reac_ctrl_parse.v:46: `REAC_CTRL_PARSE_STK := 8800`,
   the window of the proved image-A reac_ctrl_parse run (REAC_CTRL_PARSE_K), with bcmp inside a lifted stretch; it
   was 160 + 2 * ESTACK = 8352 under the cgif-form reading, so a caller now supplies 448 more bytes). The real-stack
   fallback frame (0x84020 .. 0x84038) is never taken (UAR cell 1, the class has room), so it costs nothing. *)
Definition TREPLY_STK : Z := 144 + C_reac_ctrl_parse.REAC_CTRL_PARSE_STK.   (* = 8944 *)
(* The proofs below cite the two stack constants by name, never by value (a Theorem Labs lane 2026-10-29 07:21Z), so a change of
   C_reac_ctrl_parse.REAC_CTRL_PARSE_STK costs them nothing. `lia` needs only that TREPLY_STK is the parse window
   plus the 144 bytes of the realigned frame, and that the parse window is not negative. *)
Lemma rp_stk : TREPLY_STK = 144 + C_reac_ctrl_parse.REAC_CTRL_PARSE_STK /\
0 <= C_reac_ctrl_parse.REAC_CTRL_PARSE_STK.
Proof. split; [reflexivity | unfold C_reac_ctrl_parse.REAC_CTRL_PARSE_STK; lia]. Qed.
(* rp_E1 only: __asan_stack_malloc_1 runs at sp = rA as reac_ctrl_parse does, so its ESTACK window must fit in
   the parse window. *)
Lemma rp_stk_estack : ESTACK <= C_reac_ctrl_parse.REAC_CTRL_PARSE_STK.
Proof. unfold ESTACK, C_reac_ctrl_parse.REAC_CTRL_PARSE_STK; lia. Qed.
(* No allocator event: no malloc / free; __asan_stack_malloc_1 and the flag release keep st_nev. *)
Definition EV_REPLY : Z := 0.
Section e.
Variable B : asyms.
(* the read-only window of the image, as a Theorem Labs lane's ctl_base states it (lib/A/ACfn.v:32, :43). *)
Variables RLO RHI : Z.
(* cgif lib/YC20.v:56 relro_img (c8557374ad2); accepted by a Theorem Labs lane 00:14Z; the composer discharges it with
   pa_relro_img PI_ctrl, CtrlPa.v:79-81 *)
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> in_img SEGS a.
Definition treply_out (pa pp pn a : Z) : Prop :=
pa <= a < pa + 2 \/ pp <= a < pp + 8 \/ pn <= a < pn + 8.
Definition treac_ctrl_identity_reply_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
(W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
(lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (k : Z)
(regs : bvmap 5 word) (fr len pa pp pn : Z) (g : list byte) : world SEGS -> config -> Prop :=
fun W2 c2 => wle W W2 /\ exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + EV_REPLY) /\
aregs_preserved regs regs2 /\ frames S2 = frames Sc /\
Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
getr regs2 10 = w64 (reply_ret fr len pa pp pn g) /\
tcj_kept B TREPLY_STK lyc Sc W memc W2 mem2 (spZ regs)   (* CtrlCallerJ *)
(fun a => reply_ok fr len pa pp pn g = true /\ treply_out pa pp pn a) /\
(reply_ok fr len pa pp pn g = true ->
garr8 SEGS (mrestrict (w_H W2) mem2) pa (map bv_unsigned (reply_addr g)) /\
val_mem SEGS (mrestrict (w_H W2) mem2) pp 8 (fr + 38) /\
val_mem SEGS (mrestrict (w_H W2) mem2) pn 8 (ir_s g - 13)).
Definition treac_ctrl_identity_reply_spec : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(fr len pa pp pn : Z) (g : list byte),
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
YE01.arodata_okS SEGS B RLO RHI (aview SEGS (w_H W) memc) ->
YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 10 = w64 fr -> getr regs 11 = w64 len -> getr regs 12 = w64 pa ->
getr regs 13 = w64 pp -> getr regs 14 = w64 pn ->
0 <= fr < 2 ^ 64 -> 0 <= len < 2 ^ 64 -> 0 <= pa < 2 ^ 64 -> 0 <= pp < 2 ^ 64 -> 0 <= pn < 2 ^ 64 ->
(* The caller's frame chain (cgif YC20.v:355 `tlzw_spec`) is NOT a premise here: it was carried only to pay
   reac_ctrl_parse's P6, and a Theorem Labs lane dropped parse's P6 at 00:04Z, after which a Theorem Labs lane ruled that an
   achain nothing consumes must go. So the binder `ch`, this premise, the `rc_ch` field of `rcx` and the
   `rp_chain` carry are all dropped. cgif's companion `In (raZ regs :: spine ch) CTX` was already dropped:
   this function makes no allocation and so needs no call trace. *)
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - TREPLY_STK -> spZ regs <= sp0 ->
(* fake-stack class 1: its own frame (0x84008) and, while it holds it, reac_ctrl_parse's (0x835e8) *)
count_cid 1 (frames Sc) + 1 < fs_frames 1 ->
(* the message: read only when the four pointers are non-null and len >= 50 (RcParse.cp_rd n _ = [] for n < 50;
   the tests 0x84100 .. 0x84378); it lies in a heap block (both live call sites pass a malloc'd block, so fr is
   the block start: a Theorem Labs lane 21:42Z). *)
length g = 50%nat ->
(reply_args fr pa pp pn = true -> 50 <= len ->
(exists nb, In (fr, nb) (ablocks B lyc Sc) /\ 50 <= req_size nb) /\
tsrc_ok W memc (spZ regs) fr 50 /\                        (* CtrlCallerJ *)
garr8 SEGS (mrestrict (w_H W) memc) fr (map bv_unsigned g)) ->
(* How this premise pays treac_ctrl_parse_spec's three message obligations at C5 (the parse lane's note section 4 (a working note, not in this delivery), P9 / P12 / P13;
   the spec's `f` is this `fr`, and the spec's LIST `fr` is this `g`):
     P12 `length fr = 50`  <- `length g = 50%nat` above, verbatim (same list).
     P9  the heap block above (block start = fr), with `ablocks` unchanged from C0 to C5 (the stack-malloc rule
         keeps `ablocks`, cgif YC85.v:303).
     P13 the per-byte `aview` equalities <- `garr8 ... fr (map bv_unsigned g)` above, unfolded to `aview` as
         grant's CtrlIdentityPollBlock.v:368-371 does, with `cp_v g i = bv_unsigned (nth i g cp_z)`
         (RcParse.v:9); carried from memc to the C5 memory because C0..C5 writes only this function's own frame
         and its shadow. *)
(* the caller's three cells (0x843a0 sh, 0x843b4 sd, 0x843cc sd): objects of a caller frame, the caller's right
   to let the call write them (YC20.v:358-359 as grant's twr_ok), aligned, addressable, apart *)
(reply_args fr pa pp pn = true ->
pa mod 2 = 0 /\ pp mod 8 = 0 /\ pn mod 8 = 0 /\
(pa + 2 <= pp \/ pp + 8 <= pa) /\ (pa + 2 <= pn \/ pn + 8 <= pa) /\ (pp + 8 <= pn \/ pn + 8 <= pp) /\
(forall a, treply_out pa pp pn a ->
exists cid pos, In (cid, pos) (frames Sc) /\ in_zr a (frame_rng lyc (cid, pos))) /\
twr_ok B STK sp0 FP ly S lyc Sc own W memc (spZ regs) pa 2 /\     (* CtrlCallerJ *)
twr_ok B STK sp0 FP ly S lyc Sc own W memc (spZ regs) pp 8 /\
twr_ok B STK sp0 FP ly S lyc Sc own W memc (spZ regs) pn 8 /\
range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF pa 2 /\
range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF pp 8 /\
range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF pn 8) ->
SRr SEGS W (cfg_at SEGS A_reac_ctrl_identity_replyP regs memc mdc)
(treac_ctrl_identity_reply_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs fr len pa pp pn g).

(* ================================ the cut frame ====================================================== *)
(* The walk is 305 instructions with two loops and three exits, so it is cut as cgif cuts such walks (lib/A/ACa3.v
   :287 `ra_fromX0`, lib/A/ACid.v:99 `fl_fromX0`, used in lib/A/AC9u.v:77): one record for the spec's binders, one
   invariant per cut, and one CONTINUATION-PASSING statement per cut --
     rp_from_Ci := "from a machine state that satisfies cut Ci, the post holds".
   A stretch lemma is then `rp_from_Cj -> ... -> rp_from_Ci` for the cuts Cj the stretch can reach, and the
   theorem is their composition down to C0. The invariants are CONCRETE (registers, memory, journal), not symbolic
   states: an sstate can only be written by running the engine, and these statements must be writable and provable
   independently, one lane per stretch. Each lane rebuilds its symbolic state at its entry cut (as cgif's
   `ipb_entry` / `pa_entry_st_ok_full` do) and reads the next cut's concrete facts back off `st_ok_pi` at its exit
   (`prreg`, the region chunks, `ajournal_materialize`). *)

(* the spec's binders, as one record (cgif: `racx` ACa3.v, `flcx` ACid.v) *)
Record rcx : Type := mkRCX {
rc_STK : Z; rc_sp0 : Z; rc_FP : list (Z * Z);
rc_ly : alayout; rc_S : astate; rc_W0 : world SEGS; rc_mem0 : word -> option byte; rc_md0 : Model;
rc_own : list (Z * Z);
rc_lyc : alayout; rc_Sc : astate; rc_W : world SEGS; rc_memc : word -> option byte; rc_mdc : Model;
rc_k : Z; rc_regs : bvmap 5 word;
rc_fr : Z; rc_len : Z; rc_pa : Z; rc_pp : Z; rc_pn : Z;
rc_g : list byte }.

(* S = the entry sp; rA = the realigned frame base (0x83f8c `addi sp,sp,-128`, 0x83fcc `andi sp,sp,-32`);
   G / FL = this function's own class-1 fake frame and its flag. *)
Definition rp_S (cx : rcx) : Z := spZ (rc_regs cx).
Definition rp_rA (cx : rcx) : Z := 32 * ((rp_S cx - 128) / 32).
Definition rp_G (cx : rcx) (pos : Z) : Z := frame_addr (rc_lyc cx) 1 pos.
Definition rp_FL (cx : rcx) (pos : Z) : Z := flag_addr (rc_lyc cx) 1 pos.
Definition rp_own1 (cx : rcx) (pos : Z) : list (Z * Z) := (1, pos) :: rc_own cx.
Definition rp_argsb (cx : rcx) : bool := reply_args (rc_fr cx) (rc_pa cx) (rc_pp cx) (rc_pn cx).
Definition rp_okb (cx : rcx) : bool := reply_ok (rc_fr cx) (rc_len cx) (rc_pa cx) (rc_pp cx) (rc_pn cx) (rc_g cx).
Definition rp_ret (cx : rcx) : Z := reply_ret (rc_fr cx) (rc_len cx) (rc_pa cx) (rc_pp cx) (rc_pn cx) (rc_g cx).
Definition rp_s (cx : rcx) : Z := ir_s (rc_g cx).
(* every cut's pc, as BASE + AF + offset; the offsets are read off the v1.9 listing (CtrlList.v slot 3116 = AF
   0x30b0 = 0x83f8c). *)
Definition rp_pc (off : Z) : Z := A_reac_ctrl_identity_replyP + off.

Definition rp_post (cx : rcx) : world SEGS -> config -> Prop :=
treac_ctrl_identity_reply_post (rc_STK cx) (rc_sp0 cx) (rc_FP cx) (rc_ly cx) (rc_S cx) (rc_W0 cx) (rc_mem0 cx)
(rc_md0 cx) (rc_own cx) (rc_lyc cx) (rc_Sc cx) (rc_W cx) (rc_memc cx) (rc_k cx) (rc_regs cx)
(rc_fr cx) (rc_len cx) (rc_pa cx) (rc_pp cx) (rc_pn cx) (rc_g cx).

(* the spec's premise list, repackaged over `cx`; `treac_ctrl_identity_reply_spec` is exactly
   `forall cx-fields, rp_base cx -> SRr ... (rp_post cx)` after `intros`. *)
Definition rp_base (cx : rcx) : Prop :=
ajournal SEGS B (rc_STK cx) (rc_sp0 cx) (rc_FP cx) (rc_ly cx) (rc_S cx) (rc_W0 cx) (rc_mem0 cx) (rc_md0 cx)
(rc_own cx) (rc_lyc cx) (rc_Sc cx) (rc_W cx) (rc_memc cx) (rc_mdc cx) (rc_k cx) /\
YE01.arodata_okS SEGS B RLO RHI (aview SEGS (w_H (rc_W cx)) (rc_memc cx)) /\
YK0s.ret_ok (getr (rc_regs cx) 1) /\ 4096 <= raZ (rc_regs cx) /\
getr (rc_regs cx) 3 = w64 (as_gp B) /\ getr (rc_regs cx) 4 = w64 (as_tp B) /\
getr (rc_regs cx) 10 = w64 (rc_fr cx) /\ getr (rc_regs cx) 11 = w64 (rc_len cx) /\
getr (rc_regs cx) 12 = w64 (rc_pa cx) /\ getr (rc_regs cx) 13 = w64 (rc_pp cx) /\
getr (rc_regs cx) 14 = w64 (rc_pn cx) /\
0 <= rc_fr cx < 2 ^ 64 /\ 0 <= rc_len cx < 2 ^ 64 /\ 0 <= rc_pa cx < 2 ^ 64 /\ 0 <= rc_pp cx < 2 ^ 64 /\
0 <= rc_pn cx < 2 ^ 64 /\
rp_S cx mod 16 = 0 /\ rc_sp0 cx - rc_STK cx <= rp_S cx - TREPLY_STK /\ rp_S cx <= rc_sp0 cx /\
count_cid 1 (frames (rc_Sc cx)) + 1 < fs_frames 1 /\
length (rc_g cx) = 50%nat /\
(rp_argsb cx = true -> 50 <= rc_len cx ->
(exists nb, In (rc_fr cx, nb) (ablocks B (rc_lyc cx) (rc_Sc cx)) /\ 50 <= req_size nb) /\
tsrc_ok (rc_W cx) (rc_memc cx) (rp_S cx) (rc_fr cx) 50 /\
garr8 SEGS (mrestrict (w_H (rc_W cx)) (rc_memc cx)) (rc_fr cx) (map bv_unsigned (rc_g cx))) /\
(rp_argsb cx = true ->
rc_pa cx mod 2 = 0 /\ rc_pp cx mod 8 = 0 /\ rc_pn cx mod 8 = 0 /\
(rc_pa cx + 2 <= rc_pp cx \/ rc_pp cx + 8 <= rc_pa cx) /\
(rc_pa cx + 2 <= rc_pn cx \/ rc_pn cx + 8 <= rc_pa cx) /\
(rc_pp cx + 8 <= rc_pn cx \/ rc_pn cx + 8 <= rc_pp cx) /\
(forall a, treply_out (rc_pa cx) (rc_pp cx) (rc_pn cx) a ->
exists cid pos, In (cid, pos) (frames (rc_Sc cx)) /\ in_zr a (frame_rng (rc_lyc cx) (cid, pos))) /\
twr_ok B (rc_STK cx) (rc_sp0 cx) (rc_FP cx) (rc_ly cx) (rc_S cx) (rc_lyc cx) (rc_Sc cx) (rc_own cx)
(rc_W cx) (rc_memc cx) (rp_S cx) (rc_pa cx) 2 /\
twr_ok B (rc_STK cx) (rc_sp0 cx) (rc_FP cx) (rc_ly cx) (rc_S cx) (rc_lyc cx) (rc_Sc cx) (rc_own cx)
(rc_W cx) (rc_memc cx) (rp_S cx) (rc_pp cx) 8 /\
twr_ok B (rc_STK cx) (rc_sp0 cx) (rc_FP cx) (rc_ly cx) (rc_S cx) (rc_lyc cx) (rc_Sc cx) (rc_own cx)
(rc_W cx) (rc_memc cx) (rp_S cx) (rc_pn cx) 8 /\
range_addressable (aview SEGS (w_H (rc_W cx)) (rc_memc cx)) SHADOW_OFF (rc_pa cx) 2 /\
range_addressable (aview SEGS (w_H (rc_W cx)) (rc_memc cx)) SHADOW_OFF (rc_pp cx) 8 /\
range_addressable (aview SEGS (w_H (rc_W cx)) (rc_memc cx)) SHADOW_OFF (rc_pn cx) 8).

(* ---- the pieces every cut after the prologue carries ---------------------------------------------- *)
(* Registers the prologue sets and no stretch changes (0x83fcc..0x83ffc): sp = s1 = rA, s0 = S, s3 = pn, s4 = pp,
   s5 = pa, s6 = fr, s7 = len, s11 = SHADOW_OFF (cell A_OBJ 30 through GOT A_OBJ 1, AR_const_law YG0d.v:460);
   gp / tp as the image sets them. *)
Definition rp_regs_ok (cx : rcx) (regs3 : bvmap 5 word) : Prop :=
getr regs3 2 = w64 (rp_rA cx) /\ getr regs3 3 = w64 (as_gp B) /\ getr regs3 4 = w64 (as_tp B) /\
getr regs3 8 = w64 (rp_S cx) /\ getr regs3 9 = w64 (rp_rA cx) /\
getr regs3 19 = w64 (rc_pn cx) /\ getr regs3 20 = w64 (rc_pp cx) /\ getr regs3 21 = w64 (rc_pa cx) /\
getr regs3 22 = w64 (rc_fr cx) /\ getr regs3 23 = w64 (rc_len cx) /\ getr regs3 27 = w64 SHADOW_OFF.
(* the prologue's 13 saved words (0x83f94..0x83fc4): (offset below S, register). *)
Definition rp_saves : list (Z * Z) :=
[(8, 1); (16, 8); (24, 9); (32, 18); (40, 19); (48, 20); (56, 21); (64, 22); (72, 23); (80, 24); (88, 25);
(96, 26); (104, 27)].
Definition rp_saved (cx : rcx) (W3 : world SEGS) (mem3 : word -> option byte) : Prop :=
(* The zero the prologue writes at 0x83f90 `sd zero,0(sp)` (address rp_S cx - 128) is NOT carried: at C4, when
   rp_S cx mod 32 = 16, rA = rp_S cx - 144 and 0x8403c `sd s10,16(s1)` writes G over rp_S cx - 128, so that
   conjunct is FALSE there (found and Coq-checked by a Theorem Labs lane, evidence
   blocker-evidence.v (not in this delivery)). Nothing reads rp_S cx - 128
   again -- the epilogue loads only S-8 .. S-104 -- so only the 13 saved words below are kept. *)
Forall (fun p : Z * Z => val_mem SEGS (mrestrict (w_H W3) mem3) (rp_S cx - fst p) 8
(bv_unsigned (getr (rc_regs cx) (Z_to_bv 5 (snd p))))) rp_saves.
(* the layout may only grow along the journal, and `layout_le` fixes ly_F and ly_top (YG0f.v:64-69), so G and FL
   are the same addresses at every cut. *)
Definition rp_ly_ok (cx : rcx) (ly3 : alayout) : Prop :=
ly_F ly3 = ly_F (rc_lyc cx) /\ ly_top ly3 = ly_top (rc_lyc cx).
(* what is unchanged since the entry memory, with the stretch's own exception set E (cgif tlzw_kept YC20.v:311-323,
   as grant's tcj_kept). The own fake frame, its shadow and its flag need no exception: they are below
   alloc_ceiling (frames_bounds, YCbq.v:448), are no block of `ablocks` and no frame of `frames Sc`. *)
Definition rp_kept (cx : rcx) (W3 : world SEGS) (mem3 : word -> option byte) (E : Z -> Prop) : Prop :=
wle (rc_W cx) W3 /\
tcj_kept B TREPLY_STK (rc_lyc cx) (rc_Sc cx) (rc_W cx) (rc_memc cx) W3 mem3 (rp_S cx) E.
Definition rp_Enone : Z -> Prop := fun _ => False.
Definition rp_Eout (cx : rcx) : Z -> Prop :=
fun a => rp_okb cx = true /\ treply_out (rc_pa cx) (rc_pp cx) (rc_pn cx) a.
(* the message block at the current memory: its 50 bytes and the shadow the 8 message loads and the two loops
   check (0x84110, 0x84134, 0x84154, 0x84174, 0x8419c, 0x841c4, 0x84314, 0x84358, 0x8436c). *)
Definition rp_msg (cx : rcx) (W3 : world SEGS) (mem3 : word -> option byte) : Prop :=
rp_argsb cx = true -> 50 <= rc_len cx ->
garr8 SEGS (mrestrict (w_H W3) mem3) (rc_fr cx) (map bv_unsigned (rc_g cx)) /\
tsrc_ok W3 mem3 (rp_S cx) (rc_fr cx) 50.
(* the three caller cells at the current memory: their shadow (the checks at 0x84380 / 0x843a4 / 0x843bc) and
   their presence (the stores at 0x843a0 / 0x843b4 / 0x843cc). *)
Definition rp_out (cx : rcx) (W3 : world SEGS) (mem3 : word -> option byte) : Prop :=
rp_argsb cx = true ->
range_addressable (aview SEGS (w_H W3) mem3) SHADOW_OFF (rc_pa cx) 2 /\
range_addressable (aview SEGS (w_H W3) mem3) SHADOW_OFF (rc_pp cx) 8 /\
range_addressable (aview SEGS (w_H W3) mem3) SHADOW_OFF (rc_pn cx) 8 /\
(forall a, treply_out (rc_pa cx) (rc_pp cx) (rc_pn cx) a -> apresent (w_H W3) mem3 a).
(* the caller's chain is not carried: rp_chain was dropped with the achain premise (00:04Z, see above). *)
Definition rp_carry (cx : rcx) (regs3 : bvmap 5 word) (W3 : world SEGS) (mem3 : word -> option byte)
(E : Z -> Prop) : Prop :=
rp_regs_ok cx regs3 /\ rp_kept cx W3 mem3 E /\ rp_saved cx W3 mem3 /\ rp_msg cx W3 mem3 /\
rp_out cx W3 mem3 /\
YE01.arodata_okS SEGS B RLO RHI (aview SEGS (w_H W3) mem3).
(* the own frame's three words (0x84060/64/68, 0x84228) and its flag word (frame + 128 - 8, 0x84274). *)
Definition rp_fwords (cx : rcx) (pos : Z) (W3 : world SEGS) (mem3 : word -> option byte) (magic : Z) : Prop :=
val_mem SEGS (mrestrict (w_H W3) mem3) (rp_G cx pos) 8 magic /\
val_mem SEGS (mrestrict (w_H W3) mem3) (rp_G cx pos + 8) 8 (VAL (A_OBJ 15)) /\
val_mem SEGS (mrestrict (w_H W3) mem3) (rp_G cx pos + 16) 8 (VAL (A_OBJ 16)) /\
rdword (aview SEGS (w_H W3) mem3) (rp_G cx pos + 120) = Some (rp_FL cx pos).
Definition rp_fregs (cx : rcx) (pos : Z) (regs3 : bvmap 5 word) : Prop :=
getr regs3 18 = w64 (rp_G cx pos) /\ getr regs3 26 = w64 (rp_G cx pos) /\
getr regs3 25 = w64 (shadow_addr (rp_G cx pos)).
Definition rp_fpres (cx : rcx) (pos : Z) (W3 : world SEGS) (mem3 : word -> option byte) : Prop :=
forall a, rp_G cx pos <= a < rp_G cx pos + 128 -> apresent (w_H W3) mem3 a.
(* the own frame's 16 shadow bytes: f1 f1 f1 f1 | f8 f8 f8 f8 f8 | f3 .. (0x84074..0x840b4), then the record's
   32 + 4 bytes unpoisoned (0x840d0..0x840e4), then f8 again (0x8420c..0x8421c), then f5 (0x84230..0x84270). *)
Definition rp_sg_frame : list Z := [241; 241; 241; 241; 248; 248; 248; 248; 248; 243; 243; 243; 243; 243; 243; 243].
Definition rp_sg_live : list Z := [241; 241; 241; 241; 0; 0; 0; 0; 4; 243; 243; 243; 243; 243; 243; 243].
Definition rp_sg_f5 : list Z := [245; 245; 245; 245; 245; 245; 245; 245; 245; 245; 245; 245; 245; 245; 245; 245].
Definition rp_shadow (cx : rcx) (pos : Z) (W3 : world SEGS) (mem3 : word -> option byte) (sg : list Z) : Prop :=
shadow_cells (aview SEGS (w_H W3) mem3) SHADOW_OFF (rp_G cx pos) sg.
(* the journal while the own class-1 frame is held, and the two facts the frame gives about the state. *)
Definition rp_jhold (cx : rcx) (pos : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
(mem3 : word -> option byte) (md3 : Model) : Prop :=
ajournal SEGS B (rc_STK cx) (rc_sp0 cx) (rc_FP cx) (rc_ly cx) (rc_S cx) (rc_W0 cx) (rc_mem0 cx) (rc_md0 cx)
(rp_own1 cx pos) ly3 S3 W3 mem3 md3 (rc_k cx) /\
rp_ly_ok cx ly3 /\
frames S3 = (1, pos) :: frames (rc_Sc cx) /\ ~ In (1, pos) (frames (rc_Sc cx)) /\
ablocks B ly3 S3 = ablocks B (rc_lyc cx) (rc_Sc cx) /\
count_cid 1 (frames S3) < fs_frames 1.
(* the three caller cells written (0x843a0 / 0x843b4 / 0x843cc), in the post's form. *)
Definition rp_cells (cx : rcx) (W3 : world SEGS) (mem3 : word -> option byte) : Prop :=
garr8 SEGS (mrestrict (w_H W3) mem3) (rc_pa cx) (map bv_unsigned (reply_addr (rc_g cx))) /\
val_mem SEGS (mrestrict (w_H W3) mem3) (rc_pp cx) 8 (rc_fr cx + 38) /\
val_mem SEGS (mrestrict (w_H W3) mem3) (rc_pn cx) 8 (rp_s cx - 13).
(* the model facts the tests of C6..C10 have decided so far (RcReply.ir, RcParse.ctrlparse). *)
Definition rp_tags (cx : rcx) : Prop :=
50 <= rc_len cx /\ fst (ctrlparse (rc_len cx) (rc_g cx)) = 5 /\
cp_v (rc_g cx) 34 * 256 + cp_v (rc_g cx) 35 = 0x500 /\
cp_v (rc_g cx) 32 = 0x12 /\ cp_v (rc_g cx) 33 = 0x12 /\ 14 <= rp_s cx <= 23.
Definition rp_tags2 (cx : rcx) : Prop :=
rp_tags cx /\ cp_v (rc_g cx) 27 = 0xf0 /\ cp_v (rc_g cx) (Z.to_nat (26 + rp_s cx)) = 0xf7.

(* ================================ the cut invariants C0..C14 ========================================= *)
(* C0 entry, 0x83f8c (AF 0x30b0): the spec's own entry state. *)
Definition rp_C0 (cx : rcx) (regs3 : bvmap 5 word) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
(mem3 : word -> option byte) (md3 : Model) : Prop :=
regs3 = rc_regs cx /\ ly3 = rc_lyc cx /\ S3 = rc_Sc cx /\ W3 = rc_W cx /\ mem3 = rc_memc cx /\ md3 = rc_mdc cx.

(* C1 UAR test, 0x84000 (+0x74): the prologue is done, the two runtime cells are read, the `beqz a2` at 0x84000
   is decided by a2 = 1 (AR_const_law: the use-after-return cell is 1 after init). *)
Definition rp_C1 (cx : rcx) (regs3 : bvmap 5 word) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
(mem3 : word -> option byte) (md3 : Model) : Prop :=
ajournal SEGS B (rc_STK cx) (rc_sp0 cx) (rc_FP cx) (rc_ly cx) (rc_S cx) (rc_W0 cx) (rc_mem0 cx) (rc_md0 cx)
(rc_own cx) ly3 S3 W3 mem3 md3 (rc_k cx) /\
ly3 = rc_lyc cx /\ S3 = rc_Sc cx /\ W3 = rc_W cx /\
rp_carry cx regs3 W3 mem3 rp_Enone /\
getr regs3 1 = getr (rc_regs cx) 1 /\
getr regs3 11 = w64 (as_shadow_cell B) /\ getr regs3 12 = w64 1.

(* C2 fake-stack call, pc = SIGMA GS___asan_stack_malloc_1 (the `jal` at 0x84008, +0x7c, has run; PALibF's
   palf_sm1 rewrites SIGMA to `pc_stack_malloc (as_code B) 1`). *)
Definition rp_C2 (cx : rcx) (regs3 : bvmap 5 word) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
(mem3 : word -> option byte) (md3 : Model) : Prop :=
ajournal SEGS B (rc_STK cx) (rc_sp0 cx) (rc_FP cx) (rc_ly cx) (rc_S cx) (rc_W0 cx) (rc_mem0 cx) (rc_md0 cx)
(rc_own cx) ly3 S3 W3 mem3 md3 (rc_k cx) /\
ly3 = rc_lyc cx /\ S3 = rc_Sc cx /\ W3 = rc_W cx /\
rp_carry cx regs3 W3 mem3 rp_Enone /\
getr regs3 1 = w64 (rp_pc 0x80) /\ YK0s.ret_ok (getr regs3 1) /\ getr regs3 10 = w64 128 /\
count_cid 1 (frames S3) + 1 < fs_frames 1.

(* C3 call return, 0x8400c (+0x80): the class-1 frame is taken (the a0 = 0 arm is refuted by the room premise,
   so 0x84014 and the real-stack probe 0x84020..0x84038 are not walked). *)
Definition rp_C3 (cx : rcx) (pos : Z) (regs3 : bvmap 5 word) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
(mem3 : word -> option byte) (md3 : Model) : Prop :=
rp_jhold cx pos ly3 S3 W3 mem3 md3 /\ ly3 = rc_lyc cx /\ W3 = rc_W cx /\
rp_carry cx regs3 W3 mem3 rp_Enone /\
getr regs3 10 = w64 (rp_G cx pos) /\
zero_shadow (aview SEGS (w_H W3) mem3) SHADOW_OFF (rp_G cx pos) 128 /\
rdword (aview SEGS (w_H W3) mem3) (rp_G cx pos + 120) = Some (rp_FL cx pos) /\
rp_fpres cx pos W3 mem3.

(* C4 frame built, 0x840bc (+0x130): the stack slot rA+16, the three frame words and the 16 shadow bytes are
   written; a0 = -1 is the value the four null tests return. *)
Definition rp_C4 (cx : rcx) (pos : Z) (regs3 : bvmap 5 word) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
(mem3 : word -> option byte) (md3 : Model) : Prop :=
rp_jhold cx pos ly3 S3 W3 mem3 md3 /\ ly3 = rc_lyc cx /\ W3 = rc_W cx /\
rp_carry cx regs3 W3 mem3 rp_Enone /\ rp_fregs cx pos regs3 /\ rp_fpres cx pos W3 mem3 /\
rp_fwords cx pos W3 mem3 0x41b58ab3 /\ rp_shadow cx pos W3 mem3 rp_sg_frame /\
val_mem SEGS (mrestrict (w_H W3) mem3) (rp_rA cx + 16) 8 (rp_G cx pos) /\
getr regs3 10 = w64 (-1).

(* C5 parse call, pc = A_reac_ctrl_parseP (the `jal` at 0x840f4, +0x168, has run): the four pointers are
   non-null, the record at G+32 is unpoisoned (SG[4..7] = 0, SG[8] = 4), a0 = fr, a1 = len, a2 = s8 = G+32. *)
Definition rp_C5 (cx : rcx) (pos : Z) (regs3 : bvmap 5 word) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
(mem3 : word -> option byte) (md3 : Model) : Prop :=
rp_jhold cx pos ly3 S3 W3 mem3 md3 /\ ly3 = rc_lyc cx /\ W3 = rc_W cx /\
rp_carry cx regs3 W3 mem3 rp_Enone /\ rp_fregs cx pos regs3 /\ rp_fpres cx pos W3 mem3 /\
rp_fwords cx pos W3 mem3 0x41b58ab3 /\ rp_shadow cx pos W3 mem3 rp_sg_live /\
rp_argsb cx = true /\
getr regs3 1 = w64 (rp_pc 0x16c) /\ YK0s.ret_ok (getr regs3 1) /\
getr regs3 10 = w64 (rc_fr cx) /\ getr regs3 11 = w64 (rc_len cx) /\
getr regs3 12 = w64 (rp_G cx pos + 32) /\ getr regs3 24 = w64 (rp_G cx pos + 32) /\
range_addressable (aview SEGS (w_H W3) mem3) SHADOW_OFF (rp_G cx pos + 32) 36.

(* C6 parse return, 0x840f8 (+0x16c): a0 is the model's kind and [G+32, G+68) is the model's record; the journal
   index k is unchanged (parse raises no allocator event) and `ablocks` is unchanged. *)
Definition rp_C6 (cx : rcx) (pos : Z) (regs3 : bvmap 5 word) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
(mem3 : word -> option byte) (md3 : Model) : Prop :=
rp_jhold cx pos ly3 S3 W3 mem3 md3 /\
rp_carry cx regs3 W3 mem3 rp_Enone /\ rp_fregs cx pos regs3 /\ rp_fpres cx pos W3 mem3 /\
rp_fwords cx pos W3 mem3 0x41b58ab3 /\ rp_shadow cx pos W3 mem3 rp_sg_live /\
rp_argsb cx = true /\
getr regs3 10 = w64 (fst (ctrlparse (rc_len cx) (rc_g cx))) /\
getr regs3 24 = w64 (rp_G cx pos + 32) /\
range_addressable (aview SEGS (w_H W3) mem3) SHADOW_OFF (rp_G cx pos + 32) 36 /\
(forall i, (i < 36)%nat -> aview SEGS (w_H W3) mem3 (rp_G cx pos + 32 + Z.of_nat i) =
Some (bv_unsigned (nth i (snd (ctrlparse (rc_len cx) (rc_g cx))) cp_z))).

(* C7 after the s-range test, 0x84170 (+0x1e4): kind = 5, the u16 at G+60 is 0x500, fr[32] = fr[33] = 0x12 and
   s = fr[26] is in [14, 23] (0x8416c `bltu` not taken). a1 holds s from 0x84160 to the store at 0x843cc. *)
Definition rp_C7 (cx : rcx) (pos : Z) (regs3 : bvmap 5 word) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
(mem3 : word -> option byte) (md3 : Model) : Prop :=
rp_jhold cx pos ly3 S3 W3 mem3 md3 /\
rp_carry cx regs3 W3 mem3 rp_Enone /\ rp_fregs cx pos regs3 /\ rp_fpres cx pos W3 mem3 /\
rp_fwords cx pos W3 mem3 0x41b58ab3 /\ rp_shadow cx pos W3 mem3 rp_sg_live /\
rp_argsb cx = true /\ rp_tags cx /\ getr regs3 11 = w64 (rp_s cx).

(* C8 block-sum loop head, 0x841c4 (+0x238), turn i: 32 turns over fr+18 .. fr+49 (the model's ir_blk). *)
Definition rp_C8 (cx : rcx) (pos : Z) (i : Z) (regs3 : bvmap 5 word) (ly3 : alayout) (S3 : astate)
(W3 : world SEGS) (mem3 : word -> option byte) (md3 : Model) : Prop :=
rp_jhold cx pos ly3 S3 W3 mem3 md3 /\
rp_carry cx regs3 W3 mem3 rp_Enone /\ rp_fregs cx pos regs3 /\ rp_fpres cx pos W3 mem3 /\
rp_fwords cx pos W3 mem3 0x41b58ab3 /\ rp_shadow cx pos W3 mem3 rp_sg_live /\
rp_argsb cx = true /\ rp_tags2 cx /\ getr regs3 11 = w64 (rp_s cx) /\
0 <= i <= 31 /\
getr regs3 10 = w64 (rc_fr cx + 18 + i) /\ getr regs3 12 = w64 (rc_fr cx + 18 + i) /\
getr regs3 13 = w64 (psum (ir_blk (rc_g cx)) (Z.to_nat i)) /\ getr regs3 14 = w64 (32 - i).

(* C9 block sum passed, 0x84300 (+0x374): `zext.b` of the sum is 0, i.e. blocksum (ir_blk g) = 0. *)
Definition rp_C9 (cx : rcx) (pos : Z) (regs3 : bvmap 5 word) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
(mem3 : word -> option byte) (md3 : Model) : Prop :=
rp_jhold cx pos ly3 S3 W3 mem3 md3 /\
rp_carry cx regs3 W3 mem3 rp_Enone /\ rp_fregs cx pos regs3 /\ rp_fpres cx pos W3 mem3 /\
rp_fwords cx pos W3 mem3 0x41b58ab3 /\ rp_shadow cx pos W3 mem3 rp_sg_live /\
rp_argsb cx = true /\ rp_tags2 cx /\ getr regs3 11 = w64 (rp_s cx) /\
blocksum (ir_blk (rc_g cx)) = 0.

(* C9L (AUXILIARY, not one of C0..C14): the record-sum loop head, 0x84314 (+0x388), turn j: s - 8 turns over
   fr+34 .. (the model's ir_rec). The `beqz a2` at 0x84304 is never taken (s - 8 >= 6). *)
Definition rp_C9L (cx : rcx) (pos : Z) (j : Z) (regs3 : bvmap 5 word) (ly3 : alayout) (S3 : astate)
(W3 : world SEGS) (mem3 : word -> option byte) (md3 : Model) : Prop :=
rp_jhold cx pos ly3 S3 W3 mem3 md3 /\
rp_carry cx regs3 W3 mem3 rp_Enone /\ rp_fregs cx pos regs3 /\ rp_fpres cx pos W3 mem3 /\
rp_fwords cx pos W3 mem3 0x41b58ab3 /\ rp_shadow cx pos W3 mem3 rp_sg_live /\
rp_argsb cx = true /\ rp_tags2 cx /\ getr regs3 11 = w64 (rp_s cx) /\
blocksum (ir_blk (rc_g cx)) = 0 /\
0 <= j <= rp_s cx - 9 /\
getr regs3 10 = w64 (rc_fr cx + 34 + j) /\ getr regs3 14 = w64 (rc_fr cx + 34 + j) /\
getr regs3 12 = w64 (rp_s cx - 8 - j) /\ getr regs3 13 = w64 (psum (ir_rec (rc_g cx)) (Z.to_nat j)).

(* C10 stores, 0x84354 (+0x3c8): every test of `ir` has passed, so `ir len g = true`. *)
Definition rp_C10 (cx : rcx) (pos : Z) (regs3 : bvmap 5 word) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
(mem3 : word -> option byte) (md3 : Model) : Prop :=
rp_jhold cx pos ly3 S3 W3 mem3 md3 /\
rp_carry cx regs3 W3 mem3 rp_Enone /\ rp_fregs cx pos regs3 /\ rp_fpres cx pos W3 mem3 /\
rp_fwords cx pos W3 mem3 0x41b58ab3 /\ rp_shadow cx pos W3 mem3 rp_sg_live /\
rp_argsb cx = true /\ rp_tags2 cx /\ getr regs3 11 = w64 (rp_s cx) /\
ir (rc_len cx) (rc_g cx) = true.

(* C11 fail / join, 0x84208 (+0x27c): the join of the failing tests (through 0x84204, a0 = 0) and of the store
   run (0x843d4 `j`, a0 = 1). The four pointers are non-null on every path to it. *)
Definition rp_C11 (cx : rcx) (pos : Z) (regs3 : bvmap 5 word) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
(mem3 : word -> option byte) (md3 : Model) : Prop :=
rp_jhold cx pos ly3 S3 W3 mem3 md3 /\
rp_carry cx regs3 W3 mem3 (rp_Eout cx) /\ rp_fregs cx pos regs3 /\ rp_fpres cx pos W3 mem3 /\
rp_fwords cx pos W3 mem3 0x41b58ab3 /\ rp_shadow cx pos W3 mem3 rp_sg_live /\
rp_argsb cx = true /\
getr regs3 10 = w64 (rp_ret cx) /\
(rp_okb cx = true -> rp_cells cx W3 mem3).

(* C12 frame retire, 0x84220 (+0x294): also the -1 exit of C4 (the null arm). The shadow is the frame pattern
   again on both paths (C11 writes SG[4..8] := f8; the null arm never unpoisoned them). *)
Definition rp_C12 (cx : rcx) (pos : Z) (regs3 : bvmap 5 word) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
(mem3 : word -> option byte) (md3 : Model) : Prop :=
rp_jhold cx pos ly3 S3 W3 mem3 md3 /\
rp_carry cx regs3 W3 mem3 (rp_Eout cx) /\ rp_fregs cx pos regs3 /\ rp_fpres cx pos W3 mem3 /\
rp_fwords cx pos W3 mem3 0x41b58ab3 /\ rp_shadow cx pos W3 mem3 rp_sg_frame /\
getr regs3 10 = w64 (rp_ret cx) /\
(rp_okb cx = true -> rp_cells cx W3 mem3).

(* C13 before the inline release, 0x84274 (+0x2e8): the frame word is 0x45e0360e and the 16 shadow bytes are f5;
   the frame is still held. The `beqz s2` at 0x8422c is not taken (G >= 4096, frames_bounds). *)
Definition rp_C13 (cx : rcx) (pos : Z) (regs3 : bvmap 5 word) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
(mem3 : word -> option byte) (md3 : Model) : Prop :=
rp_jhold cx pos ly3 S3 W3 mem3 md3 /\
rp_carry cx regs3 W3 mem3 (rp_Eout cx) /\ rp_fregs cx pos regs3 /\ rp_fpres cx pos W3 mem3 /\
rp_fwords cx pos W3 mem3 0x45e0360e /\ rp_shadow cx pos W3 mem3 rp_sg_f5 /\
getr regs3 10 = w64 (rp_ret cx) /\
(rp_okb cx = true -> rp_cells cx W3 mem3).

(* C14 epilogue head, 0x842c0 (+0x334): the flag is 0, the frame is released (own back to own, frames back to
   frames Sc, the state is `stack_free_state 1 pos`), sp is still rA. *)
Definition rp_C14 (cx : rcx) (regs3 : bvmap 5 word) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
(mem3 : word -> option byte) (md3 : Model) : Prop :=
ajournal SEGS B (rc_STK cx) (rc_sp0 cx) (rc_FP cx) (rc_ly cx) (rc_S cx) (rc_W0 cx) (rc_mem0 cx) (rc_md0 cx)
(rc_own cx) ly3 S3 W3 mem3 md3 (rc_k cx) /\
rp_ly_ok cx ly3 /\ frames S3 = frames (rc_Sc cx) /\
Permutation (ablocks B ly3 S3) (ablocks B (rc_lyc cx) (rc_Sc cx)) /\
rp_regs_ok cx regs3 /\ rp_kept cx W3 mem3 (rp_Eout cx) /\ rp_saved cx W3 mem3 /\
getr regs3 10 = w64 (rp_ret cx) /\
(rp_okb cx = true -> rp_cells cx W3 mem3).

(* ================================ the continuations ================================================== *)
Definition rp_from_C0 : Prop :=
forall cx regs3 ly3 S3 W3 mem3 md3, rp_base cx -> rp_C0 cx regs3 ly3 S3 W3 mem3 md3 ->
SRr SEGS W3 (cfg_at SEGS (rp_pc 0) regs3 mem3 md3) (rp_post cx).
Definition rp_from_C1 : Prop :=
forall cx regs3 ly3 S3 W3 mem3 md3, rp_base cx -> rp_C1 cx regs3 ly3 S3 W3 mem3 md3 ->
SRr SEGS W3 (cfg_at SEGS (rp_pc 0x74) regs3 mem3 md3) (rp_post cx).
Definition rp_from_C2 : Prop :=
forall cx regs3 ly3 S3 W3 mem3 md3, rp_base cx -> rp_C2 cx regs3 ly3 S3 W3 mem3 md3 ->
SRr SEGS W3 (cfg_at SEGS (SIGMA GS___asan_stack_malloc_1) regs3 mem3 md3) (rp_post cx).
Definition rp_from_C3 : Prop :=
forall cx pos regs3 ly3 S3 W3 mem3 md3, rp_base cx -> rp_C3 cx pos regs3 ly3 S3 W3 mem3 md3 ->
SRr SEGS W3 (cfg_at SEGS (rp_pc 0x80) regs3 mem3 md3) (rp_post cx).
Definition rp_from_C4 : Prop :=
forall cx pos regs3 ly3 S3 W3 mem3 md3, rp_base cx -> rp_C4 cx pos regs3 ly3 S3 W3 mem3 md3 ->
SRr SEGS W3 (cfg_at SEGS (rp_pc 0x130) regs3 mem3 md3) (rp_post cx).
Definition rp_from_C5 : Prop :=
forall cx pos regs3 ly3 S3 W3 mem3 md3, rp_base cx -> rp_C5 cx pos regs3 ly3 S3 W3 mem3 md3 ->
SRr SEGS W3 (cfg_at SEGS C_reac_ctrl_parse.A_reac_ctrl_parseP regs3 mem3 md3) (rp_post cx).
Definition rp_from_C6 : Prop :=
forall cx pos regs3 ly3 S3 W3 mem3 md3, rp_base cx -> rp_C6 cx pos regs3 ly3 S3 W3 mem3 md3 ->
SRr SEGS W3 (cfg_at SEGS (rp_pc 0x16c) regs3 mem3 md3) (rp_post cx).
Definition rp_from_C7 : Prop :=
forall cx pos regs3 ly3 S3 W3 mem3 md3, rp_base cx -> rp_C7 cx pos regs3 ly3 S3 W3 mem3 md3 ->
SRr SEGS W3 (cfg_at SEGS (rp_pc 0x1e4) regs3 mem3 md3) (rp_post cx).
Definition rp_from_C8 : Prop :=
forall cx pos i regs3 ly3 S3 W3 mem3 md3, rp_base cx -> rp_C8 cx pos i regs3 ly3 S3 W3 mem3 md3 ->
SRr SEGS W3 (cfg_at SEGS (rp_pc 0x238) regs3 mem3 md3) (rp_post cx).
Definition rp_from_C9 : Prop :=
forall cx pos regs3 ly3 S3 W3 mem3 md3, rp_base cx -> rp_C9 cx pos regs3 ly3 S3 W3 mem3 md3 ->
SRr SEGS W3 (cfg_at SEGS (rp_pc 0x374) regs3 mem3 md3) (rp_post cx).
Definition rp_from_C9L : Prop :=
forall cx pos j regs3 ly3 S3 W3 mem3 md3, rp_base cx -> rp_C9L cx pos j regs3 ly3 S3 W3 mem3 md3 ->
SRr SEGS W3 (cfg_at SEGS (rp_pc 0x388) regs3 mem3 md3) (rp_post cx).
Definition rp_from_C10 : Prop :=
forall cx pos regs3 ly3 S3 W3 mem3 md3, rp_base cx -> rp_C10 cx pos regs3 ly3 S3 W3 mem3 md3 ->
SRr SEGS W3 (cfg_at SEGS (rp_pc 0x3c8) regs3 mem3 md3) (rp_post cx).
Definition rp_from_C11 : Prop :=
forall cx pos regs3 ly3 S3 W3 mem3 md3, rp_base cx -> rp_C11 cx pos regs3 ly3 S3 W3 mem3 md3 ->
SRr SEGS W3 (cfg_at SEGS (rp_pc 0x27c) regs3 mem3 md3) (rp_post cx).
Definition rp_from_C12 : Prop :=
forall cx pos regs3 ly3 S3 W3 mem3 md3, rp_base cx -> rp_C12 cx pos regs3 ly3 S3 W3 mem3 md3 ->
SRr SEGS W3 (cfg_at SEGS (rp_pc 0x294) regs3 mem3 md3) (rp_post cx).
Definition rp_from_C13 : Prop :=
forall cx pos regs3 ly3 S3 W3 mem3 md3, rp_base cx -> rp_C13 cx pos regs3 ly3 S3 W3 mem3 md3 ->
SRr SEGS W3 (cfg_at SEGS (rp_pc 0x2e8) regs3 mem3 md3) (rp_post cx).
Definition rp_from_C14 : Prop :=
forall cx regs3 ly3 S3 W3 mem3 md3, rp_base cx -> rp_C14 cx regs3 ly3 S3 W3 mem3 md3 ->
SRr SEGS W3 (cfg_at SEGS (rp_pc 0x334) regs3 mem3 md3) (rp_post cx).

(* ================================ the walk =========================================================== *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.                       (* ctrl: shadow cell A_OBJ 30, UAR cell A_OBJ 31 *)
Hypothesis TLF : PALibF B.                     (* fake-frame facts, as cgif AChf.v:63 / ACa2.v *)
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASM1 : astack_malloc_realizes SEGS B 1.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis PARSE : C_reac_ctrl_parse.treac_ctrl_parse_spec (SK := SK) B RLO RHI.   (* at BASE + AF_reac_ctrl_parse *)

(* ---- rp_R1a's local helpers (see the Require note at the head of the file) ------------------------- *)
(* every PA-layer lemma is stated over `pa_segs PI`; this file's SEGS is its reduct AB1v.tfibsegs, which no
   unifier can see through while PI is still a metavariable, so the proof first `change`s SEGS to this form. *)
#[local] Notation rpSEGS := (@pa_segs _ ctrl_listing CtrlImg.PI_ctrl).
(* the symbolic entry state of this stretch: the own 128-byte machine-stack window, the two GOT words
   (A_OBJ 1 shadow, A_OBJ 0 UAR) and the two runtime cells (A_OBJ 30 = SHADOW_OFF, A_OBJ 31 = 1). *)
Definition rp_R1a_Bx : sv := SOff 32 0.
Definition rp_R1a_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition rp_R1a_regions : smem :=
[ stack_region 128; got_regionP; obj8_region 30 (SLit SHADOW_OFF);
uar_got_regionP (A_OBJ 31); uar_cell_regionP (A_OBJ 31) ].
Definition rp_R1a_facts : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] [].
Definition rp_R1a_ss : sstate := mkSS AF_reac_ctrl_identity_reply sr_atoms rp_R1a_regions None rp_R1a_facts.
Definition rp_R1a_E (regs : bvmap 5 word) : env := Eimg (Ereg regs []).
(* `prreg` hands the realigned sp back as a concrete `alu64` term, so the two shapes the prologue makes --
   0x83fcc `andi sp,sp,-32` and 0x83fd0 `mv s1,sp` -- are discharged at that level; the `andi` value itself
   is CtrlACja's land_m32. *)
Lemma rp_R1a_alu_and_m32 : forall x, 0 <= x < 2 ^ 64 ->
alu64 ALU_AND (Z_to_bv 64 x) (Z_to_bv 64 (-32)) = w64 (32 * (x / 32)).
Proof.
intros x Hx. unfold w64. apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw].
rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small x) by lia. change ((-32) mod 2 ^ 64) with (2 ^ 64 - 32).
rewrite land_m32 by lia.
assert (Hb : 0 <= 32 * (x / 32) < 2 ^ 64)
by (pose proof (Z.mul_div_le x 32 ltac:(lia));
split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; lia] | lia]).
rewrite (Z.mod_small _ _ Hb). reflexivity.
Qed.
Lemma rp_R1a_alu_add0 : forall x : word, alu64 ALU_ADD x (Z_to_bv 64 0) = x.
Proof.
intros x. apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw]. rewrite Z_to_bv_unsigned.
unfold bv_wrap. rewrite Zmod_0_l, Z.add_0_r.
pose proof (bv_unsigned_in_range 64 x) as R. apply Z.mod_small. exact R.
Qed.
(* memory congruence outside the stretch's write window. *)
Lemma rp_R1a_aview_eq : forall (H : word -> bool) (m m' : word -> option byte) a,
mrestrict H m' (Z_to_bv 64 a) = mrestrict H m (Z_to_bv 64 a) ->
aview rpSEGS H m' a = aview rpSEGS H m a.
Proof.
intros H m m' a Hx. unfold aview, mbyte. rewrite Hx. reflexivity.
Qed.
Lemma rp_R1a_val_mem_eq : forall (m m' : word -> option byte) a n v,
(forall k, (k < n)%nat -> m' (Z_to_bv 64 (a + Z.of_nat k)) = m (Z_to_bv 64 (a + Z.of_nat k))) ->
val_mem rpSEGS m a n v -> val_mem rpSEGS m' a n v.
Proof.
intros m m' a n v Hk Hv j Hj. specialize (Hv j Hj).
unfold mbyte in Hv |- *. rewrite (Hk j Hj). exact Hv.
Qed.

(* R1a  C0 -> C1, 0x83f8c..0x83ffc (+0x00..+0x70). Entry lemma from the caller journal (as grant's
   CtrlIdentityPollBlock.v:174 `ipb_entry`), the stack region for [S-144, S), the realignment `andi sp,sp,-32`
   as cgif AChf.v:127-170 (`denot_and_m32`, `st_ok_pi_havoc_hi`, `ast_ok_pi_set_reg_fp`, `st_ok_pi_add_fact`),
   the two runtime cells by `aconstsF` (AR_const_law: the shadow cell is SHADOW_OFF, the UAR cell is 1), the 14
   stores justified by `awr_byte`'s window case, `paj_run_to_tok` to +0x74.
   Donors: image B `rp_entry` :1214 (first half), `rA_facts` :1036; image A v1.8 `seg_prologue` :1655,
   `rA_facts` :647. Difficulty: medium (the realignment surgery is the only delicate step). *)
Lemma rp_R1a : rp_from_C1 -> rp_from_C0.
Proof.
unfold rp_from_C0. intros NEXT cx regs3 ly3 S3 W3 mem3 md3 HB HC0.
destruct HC0 as (-> & -> & -> & -> & -> & ->).
pose proof HB as HB0.
destruct HB as (HJ & HROD & Hra & Hra4 & Hgp & Htp & H10 & H11 & H12 & H13 & H14 &
Rfr & Rlen & Rpa & Rpp & Rpn & Hal16 & Hlo & Hhi & Hroom & HLG & HMSG & HOUT).
change AB1v.tfibsegs with rpSEGS in *.
pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _ & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof rp_stk as (Tstk & Pstk).
destruct (al_const _ _ LAWS _ _ _ _ _ HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
rewrite (palf_got_uar B TL) in Kguar. rewrite (pal_uar_cell B TL) in Kguar, Kuar.
pose proof (pa_obj_img 0 ltac:(lia)) as Hob0. pose proof (pa_obj_img 1 ltac:(lia)) as Hob1.
pose proof (pa_obj_img 30 ltac:(lia)) as Hob30. pose proof (pa_obj_img 31 ltac:(lia)) as Hob31.
pose proof (palf_sep B TLF) as Hsep. cbn [zseps zseps_from fst snd] in Hsep.
rewrite (pal_uar_cell B TL) in Hsep.
set (E := rp_R1a_E (rc_regs cx)).
assert (HEI : img_env VAL A_LIM E) by (unfold E, rp_R1a_E; apply Eimg_env).
assert (E2 : ew E 2 = getr (rc_regs cx) 2)
by (unfold E, rp_R1a_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat (rc_regs cx) _ 2 2%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = rp_S cx) by (rewrite E2; reflexivity).
assert (Eo0 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
by (unfold E, rp_R1a_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Eo1 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)))
by (unfold E, rp_R1a_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Eo30 : ew E (A_OBJ 30) = Z_to_bv 64 (VAL (A_OBJ 30)))
by (unfold E, rp_R1a_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Eo31 : ew E (A_OBJ 31) = Z_to_bv 64 (VAL (A_OBJ 31)))
by (unfold E, rp_R1a_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v)
by (intros n v Hn Hv; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv).
assert (HS : st_ok_pi rpSEGS VAL E rp_R1a_ss
(restrict (w_H (rc_W cx)) (mkst (rc_regs cx) (Z_to_bv 64 (BASE + AF_reac_ctrl_identity_reply)) (rc_memc cx) (seg_rom rpSEGS)))).
{ rewrite restrict_mkst_fx. unfold rp_R1a_ss. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold rp_R1a_regions, stack_region, got_regionP, obj8_region, uar_got_regionP, uar_cell_regionP.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
+ cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable rpSEGS). apply Hpres. unfold rp_S in *. lia.
+ rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Eo1) by (pose proof (pa_val_range (A_OBJ 1)); lia).
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
apply (chunk_ok_val rpSEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 30) 0) (VAL (A_OBJ 30)));
[cbn [sv_denot]; rewrite Eo30, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| pose proof (pa_val_range (A_OBJ 30)); zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword rpSEGS (w_H (rc_W cx)) (rc_memc cx) _ _ Kgot).
+ rewrite (VB (A_OBJ 30) (VAL (A_OBJ 30)) Eo30) by (pose proof (pa_val_range (A_OBJ 30)); lia).
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
apply (chunk_ok_val rpSEGS E _ (VAL (A_OBJ 30)) 0 8 (SLit SHADOW_OFF) SHADOW_OFF);
[reflexivity | unfold SHADOW_OFF; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword rpSEGS (w_H (rc_W cx)) (rc_memc cx) _ _ Kcell).
+ rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) Eo0) by (pose proof (pa_val_range (A_OBJ 0)); lia).
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
apply (chunk_ok_val rpSEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 31) 0) (VAL (A_OBJ 31)));
[cbn [sv_denot]; rewrite Eo31, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| pose proof (pa_val_range (A_OBJ 31)); zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword rpSEGS (w_H (rc_W cx)) (rc_memc cx) _ _ Kguar).
+ rewrite (VB (A_OBJ 31) (VAL (A_OBJ 31)) Eo31) by (pose proof (pa_val_range (A_OBJ 31)); lia).
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
apply (chunk_ok_val rpSEGS E _ (VAL (A_OBJ 31)) 0 4 (SLit 1) 1); [reflexivity | zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rd32 rpSEGS (w_H (rc_W cx)) (rc_memc cx) _ _ Kuar).
- apply pairwise_disjoint_of_extents.
unfold rp_R1a_regions, stack_region, got_regionP, obj8_region, uar_got_regionP, uar_cell_regionP, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) Eo0) by (pose proof (pa_val_range (A_OBJ 0)); lia).
rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Eo1) by (pose proof (pa_val_range (A_OBJ 1)); lia).
rewrite (VB (A_OBJ 30) (VAL (A_OBJ 30)) Eo30) by (pose proof (pa_val_range (A_OBJ 30)); lia).
rewrite (VB (A_OBJ 31) (VAL (A_OBJ 31)) Eo31) by (pose proof (pa_val_range (A_OBJ 31)); lia).
cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil Hstk0 Hlo Hhi Tstk Pstk C1 C3 Hob0 Hob1 Hob30 Hob31 Hsep.
unfold rp_S. clear. intros. repeat match goal with H : _ /\ _ |- _ => destruct H as [? ?] end.
repeat split; lia.
- split; [|split; [exact I | exact I]].
cbn [rp_R1a_facts f_atoms atoms_ok]. split; [|exact I].
unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Usp. change (2 ^ 4) with 16.
unfold rp_S in *. split; [lia|]. split; [exact Hal16 | lia]. }
assert (SHOK : sh_ok rpSEGS rp_R1a_Bx (@nil shent) E (mrestrict (w_H (rc_W cx)) (rc_memc cx)))
by (apply Forall_nil).
pose proof (paj_run_to B LAWS) as RUNTO.
unfold cfg_at, rp_pc, A_reac_ctrl_identity_replyP. rewrite Z.add_0_r.
change (w64 (BASE + AF_reac_ctrl_identity_reply)) with (Z_to_bv 64 (BASE + AF_reac_ctrl_identity_reply)).
paj_run_to_tok RUNTO HS HJ SHOK rp_R1a_Bspan 0x3124.
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0 ?fp ?b0 ?bc ?lyx ?own =>
let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0 fp b0 bc lyx own) end.
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (rp_S cx - rc_sp0 cx));
[reflexivity | cbn [ew]; rewrite Usp; lia
| cbn [YP09.r_wlo stack_region]; unfold rp_S in *; lia
| cbn [YP09.r_whi stack_region]; unfold rp_S in *; lia |].
repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
(* ---- the entry registers as the environment sees them ------------------------------------------- *)
assert (EEn : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr (rc_regs cx) r)
by (intros n r Hn; unfold E, rp_R1a_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (Rsp : 2 ^ 46 <= rp_S cx <= 2 ^ 47) by (unfold rp_S in *; lia).
assert (RrA : rp_S cx - 128 - 16 <= rp_rA cx <= rp_S cx - 128 /\ rp_rA cx mod 32 = 0 /\ rp_rA cx mod 16 = 0).
{ unfold rp_rA.
exact (sp1_facts (rp_S cx - 128) ltac:(lia)
ltac:(rewrite <- Zminus_mod_idemp_l, Hal16; reflexivity)). }
prreg HS (1%bv : bv 5) R1. rewrite (EEn 1%nat 1%bv eq_refl) in R1.
prreg HS (3%bv : bv 5) R3. rewrite (EEn 3%nat 3%bv eq_refl) in R3.
prreg HS (4%bv : bv 5) R4. rewrite (EEn 4%nat 4%bv eq_refl) in R4.
prreg HS (8%bv : bv 5) R8. rewrite (EEn 2%nat 2%bv eq_refl) in R8.
prreg HS (19%bv : bv 5) R19. rewrite (EEn 14%nat 14%bv eq_refl) in R19.
prreg HS (20%bv : bv 5) R20. rewrite (EEn 13%nat 13%bv eq_refl) in R20.
prreg HS (21%bv : bv 5) R21. rewrite (EEn 12%nat 12%bv eq_refl) in R21.
prreg HS (22%bv : bv 5) R22. rewrite (EEn 10%nat 10%bv eq_refl) in R22.
prreg HS (23%bv : bv 5) R23. rewrite (EEn 11%nat 11%bv eq_refl) in R23.
prreg HS (11%bv : bv 5) R11.
replace 271%nat with (A_OBJ 30) in R11 by (cbv [A_OBJ A_TEXT]; reflexivity).
rewrite Eo30, <- (pal_cell B TL) in R11.
prreg HS (12%bv : bv 5) Ra12.
prreg HS (27%bv : bv 5) R27.
prreg HS (2%bv : bv 5) R2. rewrite Usp in R2.
rewrite rp_R1a_alu_and_m32 in R2 by lia.
replace (rp_S cx + -128) with (rp_S cx - 128) in R2 by lia.
change (32 * ((rp_S cx - 128) / 32)) with (rp_rA cx) in R2.
prreg HS (9%bv : bv 5) R9. rewrite rp_R1a_alu_add0, Usp in R9.
rewrite rp_R1a_alu_and_m32 in R9 by lia.
replace (rp_S cx + -128) with (rp_S cx - 128) in R9 by lia.
change (32 * ((rp_S cx - 128) / 32)) with (rp_rA cx) in R9.
(* ---- what the prologue kept ---------------------------------------------------------------------- *)
assert (HM : forall xx : word, ~ (rp_S cx - 128 <= bv_unsigned xx < rp_S cx) ->
mrestrict (w_H (rc_W cx)) (ms_mem ms) xx = mrestrict (w_H (rc_W cx)) (rc_memc cx) xx).
{ intros xx Hxx. apply HFr. intros (rr & Hrr & Hbb).
let l := eval vm_compute in (ss_mem rp_R1a_ss) in change (ss_mem rp_R1a_ss) with l in Hrr.
cbn [In] in Hrr.
repeat (destruct Hrr as [Hrr | Hrr]); try (exfalso; exact Hrr); subst rr;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hbb;
rewrite ?Usp in Hbb; lia. }
assert (HV : forall a, 0 <= a < 2 ^ 64 -> ~ (rp_S cx - 128 <= a < rp_S cx) ->
aview rpSEGS (w_H (rc_W cx)) (ms_mem ms) a = aview rpSEGS (w_H (rc_W cx)) (rc_memc cx) a).
{ intros a Ha Hn. apply rp_R1a_aview_eq. apply HM. rewrite unsigned_lit_small by lia. lia. }
(* every address this stretch can have touched is in the own 128-byte window, which lies above
   alloc_ceiling and so meets no block, no frame, no shadow byte and no image byte. *)
assert (HLOW : forall a, 0 <= a < 2 ^ 46 -> ~ (rp_S cx - 128 <= a < rp_S cx)) by lia.
(* ---- the 13 saved words -------------------------------------------------------------------------- *)
lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict ?Hh ?msx) =>
let r0 := eval vm_compute in (nth 0 (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
pose proof (st_ok_region_nth E (abs_ss VAL ssx) (restrict Hh msx) 0%nat r0 HS
ltac:(vm_compute; reflexivity)) as HR0 end.
cbn [ms_mem restrict mkst] in HR0.
assert (HSAV : rp_saved cx (rc_W cx) (ms_mem ms)).
{ unfold rp_saved, rp_saves. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
lazymatch goal with |- val_mem _ _ (rp_S cx - ?off) _ (bv_unsigned (getr _ (Z_to_bv 5 ?z))) =>
let n := eval vm_compute in (Z.to_nat z) in
refine (field_of_region E _ 2%nat (rp_S cx) _ (-128) 0 (-128) 0 (- off) 8%N (SOff n 0) _ HR0 Usp
ltac:(vm_compute; tauto)
ltac:(cbn [sv_denot]; rewrite (EEn n (Z_to_bv 5 z) ltac:(vm_compute; reflexivity));
rewrite Z.add_0_r; reflexivity)
ltac:(cbn; apply bv_unsigned_in_range) ltac:(cbn; lia)) end. }
(* ---- the message, the caller's cells and the read-only window are untouched ---------------------- *)
assert (HMSG2 : rp_msg cx (rc_W cx) (ms_mem ms)).
{ unfold rp_msg. intros Hargs Hlen50. destruct (HMSG Hargs Hlen50) as (HB1 & HB2 & HB3).
pose proof HB2 as (Hnn & Hra2 & Hhull & Hamr & Hfr0 & Hfr1).
assert (HOUTR : forall a, rc_fr cx <= a < rc_fr cx + 50 -> ~ (rp_S cx - 128 <= a < rp_S cx))
by (intros a Ha; pose proof (proj2 (Hnn a Ha)); unfold ESTACK in *; lia).
split.
- intros j Hj. destruct (HB3 j Hj) as [Hv Hr]. split; [|exact Hr].
rewrite map_length, HLG in Hj.
apply (rp_R1a_val_mem_eq (mrestrict (w_H (rc_W cx)) (rc_memc cx))); [|exact Hv].
intros k Hk. apply HM. rewrite unsigned_lit_small.
+ apply HOUTR. lia.
+ lia.
- unfold tsrc_ok. split; [|split; [|split; [|split; [|split]]]].
+ intros a Ha. split; [| exact (proj2 (Hnn a Ha))].
rewrite HV; [apply (proj1 (Hnn a Ha)) | lia | apply HOUTR; lia].
+ intros x Hx. destruct (Hra2 x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
rewrite HV; [exact Hs | unfold shadow_of_addr, SHADOW_OFF in *; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr;
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)); assert (x / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia); lia
| unfold shadow_of_addr, SHADOW_OFF in *; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr;
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)); assert (x / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia); lia].
+ intros s Hs. rewrite HV; [apply Hhull; exact Hs | | ];
unfold shadow_addr, shadow_of_addr, SHADOW_OFF in Hs;
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr;
pose proof (Z.div_pos (rc_fr cx) 8 ltac:(lia) ltac:(lia));
pose proof (Z.div_pos (2147450880 + rc_fr cx / 8) 8 ltac:(lia) ltac:(lia));
assert ((rc_fr cx + 50 - 1) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia);
assert ((2147450880 + (rc_fr cx + 50 - 1) / 8) / 8 <= 2 ^ 42) by (apply Z.div_le_upper_bound; lia); lia.
+ exact Hamr. + exact Hfr0. + exact Hfr1. }
assert (HOUT2 : rp_out cx (rc_W cx) (ms_mem ms)).
{ unfold rp_out. change AB1v.tfibsegs with rpSEGS. intros Hargs. destruct (HOUT Hargs) as
(Ha2 & Hp8 & Hn8 & Dap & Dan & Dpn & Hfrm & Wa & Wp & Wn & RAa & RAp & RAn).
assert (HCELL : forall a, treply_out (rc_pa cx) (rc_pp cx) (rc_pn cx) a -> 4096 <= a < alloc_ceiling).
{ intros a Ha. destruct (Hfrm a Ha) as (cid & pos & Hin & Hzr).
destruct (frames_bounds rpSEGS B LAWS (rc_lyc cx) (rc_Sc cx) (rc_W cx) (rc_memc cx) (rc_mdc cx) cid pos HAR Hin)
as (Hf0 & Hfc & _). unfold in_zr, frame_rng in Hzr. cbn [fst snd] in Hzr. lia. }
assert (HSH : forall a, 4096 <= a < alloc_ceiling -> forall x, a <= x < a + 8 ->
aview rpSEGS (w_H (rc_W cx)) (ms_mem ms) (shadow_of_addr SHADOW_OFF x) =
aview rpSEGS (w_H (rc_W cx)) (rc_memc cx) (shadow_of_addr SHADOW_OFF x)).
{ intros a Ha x Hx. unfold shadow_of_addr, SHADOW_OFF.
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
assert (x / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
apply HV; lia. }
split; [|split; [|split]].
- intros x Hx. destruct (RAa x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
rewrite <- Hs. apply (HSH (rc_pa cx)); [apply HCELL; unfold treply_out; left; lia | lia].
- intros x Hx. destruct (RAp x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
rewrite <- Hs. apply (HSH (rc_pp cx)); [apply HCELL; unfold treply_out; right; left; lia | lia].
- intros x Hx. destruct (RAn x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
rewrite <- Hs. apply (HSH (rc_pn cx)); [apply HCELL; unfold treply_out; right; right; lia | lia].
- intros a Ha. apply (apresent_grows (w_H (rc_W cx)) (rc_memc cx) (ms_mem ms) a HG).
destruct Ha as [Ha | [Ha | Ha]].
+ exact (proj1 (proj2 (Wa a ltac:(lia)))).
+ exact (proj1 (proj2 (Wp a ltac:(lia)))).
+ exact (proj1 (proj2 (Wn a ltac:(lia)))). }
assert (HROD2 : YE01.arodata_okS rpSEGS B RLO RHI (aview rpSEGS (w_H (rc_W cx)) (ms_mem ms))).
{ intros a Ha Hown Herr. rewrite HV.
+ exact (HROD a Ha Hown Herr).
+ assert (Himg : in_img rpSEGS a)
by (destruct Ha as [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr] | apply RELRO_IMG; exact Hr]).
pose proof (pa_img_range a Himg). lia.
+ assert (Himg : in_img rpSEGS a)
by (destruct Ha as [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr] | apply RELRO_IMG; exact Hr]).
pose proof (pa_img_range a Himg). lia. }
(* ---- the kept clause ----------------------------------------------------------------------------- *)
assert (HKEPT : rp_kept cx (rc_W cx) (ms_mem ms) rp_Enone).
{ unfold rp_kept. split; [apply wle_refl|]. unfold tcj_kept.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
split; [intros a Ha Hw _; apply HV; lia|].
split.
- intros b m i Hin Hi _.
destruct (al_blocks _ _ LAWS (rc_lyc cx) (rc_Sc cx) (rc_W cx) (rc_memc cx) (rc_mdc cx) b m HAR Hin)
as (_ & Hb4096 & Hbceil & _). apply HV; lia.
- split.
+ intros a Hin _ _. pose proof (pa_img_range a Hin). apply HV; lia.
+ split.
* intros cid pos a Hin Hr _.
destruct (frames_bounds rpSEGS B LAWS (rc_lyc cx) (rc_Sc cx) (rc_W cx) (rc_memc cx) (rc_mdc cx) cid pos HAR Hin)
as (Hf0 & Hfc & _).
pose proof (fs_frame_bytes_nonneg cid) as Hfb.
pose proof (shadow_addr_bounds (frame_addr (rc_lyc cx) cid pos) ltac:(lia)) as Hs1.
pose proof (shadow_addr_bounds (frame_addr (rc_lyc cx) cid pos + fs_frame_bytes cid) ltac:(lia)) as Hs2.
pose proof (shadow_range_end (frame_addr (rc_lyc cx) cid pos) (fs_frame_bytes cid) Hfb) as Hs3.
unfold in_zr, frame_rng in Hr. cbn [fst snd] in Hr. apply HV; destruct Hr as [Hr|Hr]; lia.
* split.
-- intros a _ _ Hpr. exact (apresent_grows (w_H (rc_W cx)) (rc_memc cx) (ms_mem ms) a HG Hpr).
-- intros a Ha. apply Hpres2. lia. }
(* ---- hand over to C1 ----------------------------------------------------------------------------- *)
pmkst HS.
replace (BASE + 12580) with (rp_pc 0x74)
by (unfold rp_pc, A_reac_ctrl_identity_replyP, AF_reac_ctrl_identity_reply; lia).
apply (NEXT cx (ms_regs ms) (rc_lyc cx) (rc_Sc cx) (rc_W cx) (ms_mem ms) _ HB0).
unfold rp_C1. split; [exact HJ|].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split.
- unfold rp_carry. split.
+ unfold rp_regs_ok. repeat split.
* exact R2. * rewrite R3; exact Hgp. * rewrite R4; exact Htp.
* rewrite R8. unfold rp_S, spZ, w64. symmetry. apply Z_to_bv_bv_unsigned.
* exact R9. * rewrite R19; exact H14. * rewrite R20; exact H13. * rewrite R21; exact H12.
* rewrite R22; exact H10. * rewrite R23; exact H11. * exact R27.
+ split; [exact HKEPT|]. split; [exact HSAV|]. split; [exact HMSG2|]. split; [exact HOUT2 | exact HROD2].
- split; [exact R1|]. split; [exact R11 | exact Ra12].
Qed.

(* R1b  C1 -> C2, 0x84000..0x84004 (+0x74..+0x78). `beqz a2` decided by a2 = 1 (C1), then `li a0,128`; the jal
   at 0x84008 sets ra = +0x80 and stops at the PCall. Donors: B `rp_entry` :1214 (the UAR test), A18 `FKA` :742.
   Difficulty: easy. *)
Lemma rp_R1b : rp_from_C2 -> rp_from_C1.
Proof.
intros HC2 cx regs3 ly3 S3 W3 mem3 md3 Hbase HC1.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
destruct HC1 as (HJ & Hly & HSc & HW & Hcarry & Hra1 & Hs11 & Ha2).
subst ly3 S3 W3.
set (E := Eimg (Ereg regs3 (@nil word))).
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (E12 : ew E 12 = w64 1).
{ unfold E. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat regs3 (@nil word) 12 (12%bv) eq_refl). exact Ha2. }
assert (HF12 : afact_ok E 12 (mkAF 1 1 0)).
{ cbv beta iota delta [afact_ok af_lo af_hi af_al2].
  rewrite E12. unfold w64. rewrite unsigned_lit_small by lia.
  change (2 ^ 0) with 1. rewrite Z.mod_1_r. repeat split; lia. }
assert (HS : st_ok_pi SEGS VAL E
   (mkSS (AF_reac_ctrl_identity_reply + 0x74) sr_atoms (@nil YP09.region) None
         (mkFacts [(12%nat, mkAF 1 1 0)] [] []))
   (restrict (w_H (rc_W cx)) (mkst regs3 (w64 (rp_pc 0x74)) mem3 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx.
  unfold rp_pc, A_reac_ctrl_identity_replyP, w64. rewrite <- Z.add_assoc.
  apply (pa_entry_st_ok_full (PI := CtrlImg.PI_ctrl)).
  - unfold E. apply regs_ok_Eimg_Ereg.
  - vm_compute; reflexivity.
  - apply Forall_nil.
  - cbn; exact I.
  - cbv beta iota delta [facts_ok atoms_ok conds_ok alias_ok f_atoms f_conds f_alias].
    split; [ split; [ exact HF12 | exact I ] | split; exact I ]. }
assert (SHOK : sh_ok SEGS (SLit 0) (@nil shent) E (mrestrict (w_H (rc_W cx)) mem3))
  by constructor.
paj_run_tok (paj_run (PI := CtrlImg.PI_ctrl) B LAWS) HS HJ SHOK (0%Z, 0%Z).
{ awr_ok_tac. }
(* the three register-only instructions wrote no byte, so the memory is the entry memory. *)
assert (Hmem : ms_mem ms = mem3).
{ apply FunctionalExtensionality.functional_extensionality; intros x.
  exact (frame_of_nil E mem3 (ms_mem ms) x HF). }
pmkst HS.
rewrite Hmem in HJ |- *.
assert (Eall : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r ->
  ew E n = getr regs3 r).
{ intros n r Hn Hr. unfold E. rewrite Eimg_low by (unfold A_TEXT; lia).
  exact (ew_Ereg_nat regs3 (@nil word) n r Hr). }
prreg HS (1%bv : bv 5) RP1. prreg HS (10%bv : bv 5) RP10.
prreg HS (2%bv : bv 5) RP2. prreg HS (3%bv : bv 5) RP3. prreg HS (4%bv : bv 5) RP4.
prreg HS (8%bv : bv 5) RP8. prreg HS (9%bv : bv 5) RP9. prreg HS (19%bv : bv 5) RP19.
prreg HS (20%bv : bv 5) RP20. prreg HS (21%bv : bv 5) RP21. prreg HS (22%bv : bv 5) RP22.
prreg HS (23%bv : bv 5) RP23. prreg HS (27%bv : bv 5) RP27.
destruct Hcarry as (Hregs & Hrest).
unfold rp_regs_ok in Hregs.
destruct Hregs as (Hr2 & Hr3 & Hr4 & Hr8 & Hr9 & Hr19 & Hr20 & Hr21 & Hr22 & Hr23 & Hr27).
pose proof Hbase as HBc.
destruct HBc as (HJ0 & HRO0 & Hra0 & Hra40 & Hgp0 & Htp0 & Ha10 & Ha11 & Ha12 & Ha13 & Ha14 &
  Hfrr & Hlenr & Hpar & Hppr & Hpnr & HS16b & HSwin & HSsp0 & Hcnt & Hrest2).
apply (HC2 cx (ms_regs ms) (rc_lyc cx) (rc_Sc cx) (rc_W cx) mem3 _ Hbase).
unfold rp_C2.
split; [exact HJ|].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split.
{ unfold rp_carry. split; [|exact Hrest].
  unfold rp_regs_ok. repeat split.
  - rewrite RP2, (Eall 2%nat (2%bv) ltac:(lia) eq_refl). exact Hr2.
  - rewrite RP3, (Eall 3%nat (3%bv) ltac:(lia) eq_refl). exact Hr3.
  - rewrite RP4, (Eall 4%nat (4%bv) ltac:(lia) eq_refl). exact Hr4.
  - rewrite RP8, (Eall 8%nat (8%bv) ltac:(lia) eq_refl). exact Hr8.
  - rewrite RP9, (Eall 9%nat (9%bv) ltac:(lia) eq_refl). exact Hr9.
  - rewrite RP19, (Eall 19%nat (19%bv) ltac:(lia) eq_refl). exact Hr19.
  - rewrite RP20, (Eall 20%nat (20%bv) ltac:(lia) eq_refl). exact Hr20.
  - rewrite RP21, (Eall 21%nat (21%bv) ltac:(lia) eq_refl). exact Hr21.
  - rewrite RP22, (Eall 22%nat (22%bv) ltac:(lia) eq_refl). exact Hr22.
  - rewrite RP23, (Eall 23%nat (23%bv) ltac:(lia) eq_refl). exact Hr23.
  - rewrite RP27, (Eall 27%nat (27%bv) ltac:(lia) eq_refl). exact Hr27. }
split.
{ rewrite RP1; unfold w64, rp_pc, A_reac_ctrl_identity_replyP, AF_reac_ctrl_identity_reply;
  try (f_equal; lia). }
split.
{ rewrite RP1; apply ret_ok_codeptr_v; [lia | reflexivity]. }
split.
{ rewrite RP10; unfold w64; try reflexivity. }
exact Hcnt.
Qed.

(* ---- E1 local helpers (named rp_E1_*, local to this stretch; no CtrlACjr kit tactic is used) ---- *)

(* register file: rp_regs_ok survives a call that preserves the callee-saved registers. *)
Lemma rp_E1_regs_pres : forall cx (r1 r2 : bvmap 5 word),
  rp_regs_ok cx r1 -> aregs_preserved r1 r2 -> rp_regs_ok cx r2.
Proof.
  intros cx r1 r2 (A2 & A3 & A4 & A8 & A9 & A19 & A20 & A21 & A22 & A23 & A27) HP.
  unfold rp_regs_ok.
  repeat split;
  [ exact (eq_trans (HP 2 ltac:(unfold acallee_saved; lia)) A2) |
   exact (eq_trans (HP 3 ltac:(unfold acallee_saved; lia)) A3) |
   exact (eq_trans (HP 4 ltac:(unfold acallee_saved; lia)) A4) |
   exact (eq_trans (HP 8 ltac:(unfold acallee_saved; lia)) A8) |
   exact (eq_trans (HP 9 ltac:(unfold acallee_saved; lia)) A9) |
   exact (eq_trans (HP 19 ltac:(unfold acallee_saved; lia)) A19) |
   exact (eq_trans (HP 20 ltac:(unfold acallee_saved; lia)) A20) |
   exact (eq_trans (HP 21 ltac:(unfold acallee_saved; lia)) A21) |
   exact (eq_trans (HP 22 ltac:(unfold acallee_saved; lia)) A22) |
   exact (eq_trans (HP 23 ltac:(unfold acallee_saved; lia)) A23) |
   exact (eq_trans (HP 27 ltac:(unfold acallee_saved; lia)) A27) ].
Qed.

(* kept transport: compose the caller-journal kept (memc -> mem1) with a call's acall_kept
   (mem1 -> mem2) whose window lies inside the journal's stack window.  Duplicates no kit lemma;
   it is the tcj_kept/acall_kept clause-by-clause composition. *)
Lemma rp_E1_kept : forall STK lyc Sc Wref memc Wc mem1 mem2 sp slo shi (E : Z -> Prop),
  tcj_kept B STK lyc Sc Wref memc Wc mem1 sp E ->
  acall_kept SEGS B lyc Sc Wc mem1 Wc mem2 slo shi E ->
  alloc_ceiling <= sp - STK -> sp - STK <= slo -> shi <= sp -> sp <= 2 ^ 47 ->
  tcj_kept B STK lyc Sc Wref memc Wc mem2 sp E.
Proof.
  intros STK lyc Sc Wref memc Wc mem1 mem2 sp slo shi E
    (T1 & T2 & T3 & T4 & T5 & T6) (A1 & A2 & A3 & A4 & A5 & A6) Hac Hlo Hhi Hsp47.
  split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha Hw HE. exact (eq_trans (A1 a Ha ltac:(lia)) (T1 a Ha Hw HE)).
  - intros b m i Hin Hi HE. exact (eq_trans (A2 b m i Hin Hi HE) (T2 b m i Hin Hi HE)).
  - intros a Hin Ho He. exact (eq_trans (A3 a Hin Ho He) (T3 a Hin Ho He)).
  - intros cid pos a Hin Hz HE.
    exact (eq_trans (A4 cid pos a Hin Hz HE) (T4 cid pos a Hin Hz HE)).
  - intros a Ha Hw Hp. exact (A5 a Ha ltac:(lia) (T5 a Ha Hw Hp)).
  - intros a Ha.
    destruct (Z_le_gt_dec slo a) as [Hlo2|Hlo2]; [destruct (Z_lt_ge_dec a shi) as [Hhi2|Hhi2]|].
    + exact (A6 a ltac:(lia)).
    + exact (A5 a ltac:(lia) ltac:(lia) (T6 a Ha)).
    + exact (A5 a ltac:(lia) ltac:(lia) (T6 a Ha)).
Qed.

(* a live fake-stack frame has class in [0,10] (wf_fakestack of the model state). *)
Lemma rp_E1_cid : forall ly S W mem md cid pos,
  AR SEGS B ly S W mem md -> In (cid, pos) (frames S) -> 0 <= cid <= 10.
Proof.
  intros ly S W mem md cid pos HAR Hin.
  pose proof (am_wf _ _ _ _ (proj1 HAR)) as HWF.
  assert (HFS : wf_fs S) by (destruct HWF; assumption).
  assert (HWL : Forall (fun cp : Z * Z => 0 <= fst cp <= 10 /\ 0 <= snd cp < fs_frames (fst cp))
                  (fs_live (st_fs S))) by (destruct HFS; assumption).
  rewrite Forall_forall in HWL.
  exact (proj1 (HWL (cid, pos) Hin)).
Qed.

(* every ro address is an image address (the two disjuncts of arodata_okS). *)
Lemma rp_E1_roimg : forall a,
  ((exists s, In s SEGS /\ seg_writable s = false /\
      Z.of_N (seg_base s) <= a < Z.of_N (seg_base s) + Z.of_N (seg_size s)) \/ (RLO <= a < RHI)) ->
  in_img SEGS a.
Proof.
  intros a [(s & Hs & _ & Hr) | Hrelro]; [exists s; split; [exact Hs | exact Hr] | apply RELRO_IMG; exact Hrelro].
Qed.

(* frame class alignment mod 8 from mod 32. *)
Lemma rp_E1_mod8 : forall z, z mod 32 = 0 -> z mod 8 = 0.
Proof.
  intros z H. apply (proj2 (Z.mod_divide z 8 ltac:(lia))).
  apply (Z.divide_trans 8 32 z); [exists 4; reflexivity | exact (proj1 (Z.mod_divide z 32 ltac:(lia)) H)].
Qed.

(* E1  C2 -> C3, the call of __asan_stack_malloc_1 (0x84008, +0x7c).
   `aj_stack_malloc_atS SEGS B LAWS pa_segs_low (pal_env B TL) ML SMP 1 ASM1` (cgif YC85.v:291) after
   `rewrite (palf_sm1 B TLF)`; room from C2's `count_cid 1 (frames Sc) + 1 < fs_frames 1`; o = rA - sp0 with
   o mod 16 = 0 (rA mod 32 = 0) and ESTACK - o <= STK. The rule's post is exactly C3's frame facts
   (zero_shadow, the flag word, presence, ablocks kept, frames extended, the journal with own' = (1,pos)::own).
   Donors: B `rp_entry` :1214 / `rFK` :1063; A18 `FKA` :742, `rr_cls_seth` :1245. Difficulty: easy-medium. *)
Lemma rp_E1 : rp_from_C3 -> rp_from_C2.
Proof.
  intros H3 cx regs3 ly3 S3 W3 mem3 md3 HBASE HC2.
  pose proof HBASE as HBASEc.
  destruct HBASE as (HJ0 & HRO0 & Hra00 & Hra40 & Hgp0 & Htp0 & Ha100 & Ha110 & Ha120 & Ha130 & Ha140 &
    Hfrr & Hlenr & Hpar & Hppr & Hpnr & HS16 & HSwin & HSsp0 & Hcnt0 & Hglen & Hmsg0 & Hout0).
  destruct HC2 as (HJ & Hly3 & HS3 & HW3 & HCAR & Hra & Hretok & Ha0 & Hroom).
  subst ly3 S3 W3.
  pose proof HCAR as HCARc.
  destruct HCAR as (HREGS & HKEPT & HSAVED & HMSG & HOUT & HROD).
  pose proof HREGS as HREGSc.
  destruct HREGS as (R2 & R3 & R4 & R8 & R9 & R19 & R20 & R21 & R22 & R23 & R27).
  destruct HKEPT as (Hwle2 & Htcj2).
  (* astk_ok from the caller journal *)
  pose proof HJ as HJd.
  destruct HJd as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSTK & _ & _).
  destruct HSTK as (Jsp16 & JSTK0 & Jclo & Jlosp & Jsphi & Jhi47 & Jbot & Jtop1 & Jtop2).
  pose proof alloc_ceiling_val as HAC.
  pose proof rp_stk as (Tstk & Pstk). pose proof rp_stk_estack as Estk.
  assert (HSlo : alloc_ceiling <= rp_S cx - TREPLY_STK) by lia.
  assert (Hpow : (2:Z) ^ 47 < 2 ^ 64) by (apply Z.pow_lt_mono_r; lia).
  pose proof (Z.div_mod (rp_S cx - 128) 32 ltac:(lia)) as Hdm.
  pose proof (Z.mod_pos_bound (rp_S cx - 128) 32 ltac:(lia)) as Hmb.
  assert (HrAlo : rp_S cx - 160 < rp_rA cx) by (unfold rp_rA; lia).
  assert (HrAhi : rp_rA cx <= rp_S cx - 128) by (unfold rp_rA; lia).
  (* rA >= S - 144 exactly (S mod 16 = 0); with rp_stk_estack, __asan_stack_malloc_1's [rA - ESTACK, rA) lies in
     [S - TREPLY_STK, S) *)
  assert (HrA144 : rp_S cx - 144 <= rp_rA cx).
  { pose proof (Z.div_mod (rp_S cx) 16 ltac:(lia)) as D16. rewrite HS16, Z.add_0_r in D16. unfold rp_rA. lia. }
  assert (HShi47 : rp_S cx <= 2 ^ 47) by lia.
  assert (HrArng : 0 <= rp_rA cx < 2 ^ 64) by lia.
  assert (HrAmod : rp_rA cx mod 16 = 0).
  { unfold rp_rA. replace (32 * ((rp_S cx - 128) / 32)) with (16 * (2 * ((rp_S cx - 128) / 32))) by lia.
    rewrite Z.mul_comm. apply Z_mod_mult. }
  assert (HspA : spZ regs3 = rp_rA cx)
    by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; exact HrArng).
  (* the call *)
  eapply SRr_bind.
  { unfold cfg_at. rewrite (palf_sm1 B TLF).
    refine (aj_stack_malloc_atS SEGS B LAWS pa_segs_low (pal_env B TL) ML SMP 1 ASM1 ltac:(lia)
      (rc_W cx) regs3 mem3 (rc_STK cx) (rc_sp0 cx) (rc_FP cx) (rc_ly cx) (rc_S cx)
      (rc_W0 cx) (rc_mem0 cx) (rc_md0 cx) (rc_own cx) (rc_lyc cx) (rc_Sc cx) md3 (rc_k cx)
      (rp_rA cx - rc_sp0 cx) (getr regs3 1) HJ _ _ _ _ R3 R4 eq_refl Hretok _).
    - rewrite HspA. lia.
    - rewrite Zminus_mod, HrAmod, Jsp16. reflexivity.
    - lia.
    - lia.
    - lia. }
  cbv beta.
  intros W' c' Hwle' Hpost.
  destruct Hpost as (HeqW & S2 & regs2 & mem2 & md2 & pos & Hc' & HJ2 & HPRES & Ha0' & Hab & Hfrs2 &
    Hnin & Hnev2 & Hbb2 & Hz & Hflag & Hacall & HJ1 & Hfs).
  subst W'. subst c'.
  pose proof (proj1 HJ) as HARc.    (* AR SEGS B lyc Sc rc_W mem3 md3 *)
  pose proof (proj1 HJ2) as HAR2.   (* AR SEGS B lyc S2 rc_W mem2 md2 *)
  change (fs_frame_bytes 1) with 128 in Hz, Hflag.
  (* rewrite the return pc so the config is cfg_at (rp_pc 0x80) *)
  rewrite Hra.
  apply (H3 cx pos regs2 (rc_lyc cx) S2 (rc_W cx) mem2 md2 HBASEc).
  (* ===== build rp_C3 ===== *)
  (* kept at C3 *)
  assert (Hkept3 : tcj_kept B TREPLY_STK (rc_lyc cx) (rc_Sc cx) (rc_W cx) (rc_memc cx) (rc_W cx) mem2 (rp_S cx) rp_Enone).
  { eapply rp_E1_kept.
    - exact Htcj2.
    - exact Hacall.
    - exact HSlo.
    - lia.
    - lia.
    - exact HShi47. }
  (* rp_carry at C3 *)
  assert (HREGS2 : rp_regs_ok cx regs2) by (apply (rp_E1_regs_pres cx regs3 regs2 HREGSc HPRES)).
  assert (HSAVED2 : rp_saved cx (rc_W cx) mem2).
  { unfold rp_saved in HSAVED |- *. rewrite Forall_forall in HSAVED |- *. intros p Hp.
    assert (Hfp : 8 <= fst p <= 104)
      by (unfold rp_saves in Hp; cbn [In] in Hp;
          repeat (destruct Hp as [<- | Hp]); try (cbn [fst]; lia); contradiction).
    eapply val_mem_kept; [| exact (HSAVED p Hp)].
    intros kk Hkk. destruct Hacall as (K1 & _).
    apply K1; [ lia | unfold ESTACK; lia ]. }
  assert (HMSG2 : rp_msg cx (rc_W cx) mem2).
  { unfold rp_msg in HMSG |- *. intros Hargs Hlen50.
    destruct (HMSG Hargs Hlen50) as (HG3 & HTS3).
    destruct (Hmsg0 Hargs Hlen50) as ((nb & Hinnb & Hnbsz) & _ & _).
    assert (Hinnb2 : In (rc_fr cx, nb) (ablocks B (rc_lyc cx) S2)) by (rewrite Hab; exact Hinnb).
    assert (Hgl : length (rc_g cx) = 50%nat) by exact Hglen.
    split.
    - (* garr8 at mem2 *)
      intros j Hj. rewrite length_map in Hj. destruct (HG3 j ltac:(rewrite length_map; lia)) as (HVj & HBj).
      split; [|exact HBj].
      eapply val_mem_entry_block;
        [ exact HJ1 | exact Hinnb | exact Hinnb2 | lia | cbn [Z.of_nat]; lia
        | intros x Hx (rg & [] & _) | exact HVj ].
    - (* tsrc_ok at mem2 *)
      destruct HTS3 as (HTSdata & HTSra & HTShull & HTSamem & HTSq0 & HTSq63).
      unfold tsrc_ok. split; [|split; [|split; [|split; [|split]]]].
      + intros a Ha. split.
        * destruct (al_blocks _ _ LAWS (rc_lyc cx) S2 (rc_W cx) mem2 md2 (rc_fr cx) nb HAR2 Hinnb2)
            as (_ & _ & _ & _ & Hpr & _).
          apply aview_some_of_apresent. exact (proj1 (Hpr a ltac:(lia))).
        * exact (proj2 (HTSdata a Ha)).
      + eapply range_addressable_of_block; [ exact LAWS | exact HAR2 | exact Hinnb2 | lia | lia ].
      + eapply shadow_hull_vis_of_block;
          [ exact LAWS | exact HAR2 | exact Hinnb2 | lia | lia | lia ].
      + exact HTSamem.
      + exact HTSq0.
      + exact HTSq63. }
  assert (HOUT2 : rp_out cx (rc_W cx) mem2).
  { unfold rp_out in HOUT |- *. intros Hargs.
    destruct (HOUT Hargs) as (RApa3 & RApp3 & RApn3 & Hprescells3).
    destruct (Hout0 Hargs) as (_ & _ & _ & _ & _ & _ & Hcellfr & _ & _ & _ & _ & _ & _).
    (* per-cell range_addressable and presence *)
    assert (HRAcell : forall q n, (forall x, q <= x < q + n -> treply_out (rc_pa cx) (rc_pp cx) (rc_pn cx) x) ->
      range_addressable (aview SEGS (w_H (rc_W cx)) mem3) SHADOW_OFF q n ->
      range_addressable (aview SEGS (w_H (rc_W cx)) mem2) SHADOW_OFF q n).
    { intros q n Hin HRA x Hx.
      destruct (Hcellfr x (Hin x Hx)) as (cidw & posw & Hinw & Hzrw).
      unfold in_zr, frame_rng in Hzrw. cbn [fst snd] in Hzrw.
      assert (Hcidw : 0 <= cidw <= 10) by (apply (rp_E1_cid _ _ _ _ _ _ _ HARc Hinw)).
      destruct (al_frames _ _ LAWS (rc_lyc cx) (rc_Sc cx) (rc_W cx) mem3 md3 cidw posw HARc Hinw)
        as (Hfm32 & _ & _ & _).
      assert (HRA1 : range_addressable (aview SEGS (w_H (rc_W cx)) mem2) SHADOW_OFF x 1).
      { eapply range_addressable_entry_frame;
          [ exact LAWS | exact HJ1 | exact Hinw | lia | lia | lia
          | exact (rp_E1_mod8 _ Hfm32) | intros z (rg & [] & _) | exact HARc
          | eapply range_addressable_sub; [ exact HRA | lia | lia ] ]. }
      exact (HRA1 x ltac:(lia)). }
    split; [|split; [|split]].
    - apply (HRAcell (rc_pa cx) 2 ltac:(intros x Hx; unfold treply_out; lia) RApa3).
    - apply (HRAcell (rc_pp cx) 8 ltac:(intros x Hx; unfold treply_out; lia) RApp3).
    - apply (HRAcell (rc_pn cx) 8 ltac:(intros x Hx; unfold treply_out; lia) RApn3).
    - intros a Ha.
      destruct (Hcellfr a Ha) as (cidw & posw & Hinw & Hzrw).
      unfold in_zr, frame_rng in Hzrw. cbn [fst snd] in Hzrw.
      assert (Hinw2 : In (cidw, posw) (frames S2)) by (rewrite Hfrs2; right; exact Hinw).
      destruct (al_frames _ _ LAWS (rc_lyc cx) S2 (rc_W cx) mem2 md2 cidw posw HAR2 Hinw2)
        as (_ & _ & Hfpr & _).
      apply (proj1 (Hfpr a ltac:(lia))). }
  assert (HROD2 : YE01.arodata_okS SEGS B RLO RHI (aview SEGS (w_H (rc_W cx)) mem2)).
  { intros a Hro Hown Herr.
    destruct Hkept3 as (_ & _ & T3 & _).
    exact (eq_trans (T3 a (rp_E1_roimg a Hro) Hown Herr) (HRO0 a Hro Hown Herr)). }
  assert (HCAR2 : rp_carry cx regs2 (rc_W cx) mem2 rp_Enone).
  { unfold rp_carry. split; [exact HREGS2 | split; [| split; [exact HSAVED2 |
      split; [exact HMSG2 | split; [exact HOUT2 | exact HROD2]]]]].
    split; [apply wle_refl | exact Hkept3]. }
  (* rp_jhold at C3 *)
  assert (Hjhold : rp_jhold cx pos (rc_lyc cx) S2 (rc_W cx) mem2 md2).
  { unfold rp_jhold. split; [exact HJ2 | split; [split; reflexivity |
      split; [exact Hfrs2 | split; [exact Hnin | split; [exact Hab |]]]]].
    rewrite Hfrs2. cbn [count_cid]. rewrite Z.eqb_refl. lia. }
  (* assemble rp_C3 *)
  unfold rp_C3. split; [exact Hjhold | split; [reflexivity | split; [reflexivity |
    split; [exact HCAR2 | split; [| split; [| split]]]]]].
  - unfold rp_G. exact Ha0'.
  - unfold rp_G. exact Hz.
  - unfold rp_G, rp_FL. replace (frame_addr (rc_lyc cx) 1 pos + 128 - 8)
      with (frame_addr (rc_lyc cx) 1 pos + 120) in Hflag by lia. exact Hflag.
  - (* rp_fpres *)
    intros a Ha.
    assert (Hfin2 : In (1, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
    destruct (al_frames _ _ LAWS (rc_lyc cx) S2 (rc_W cx) mem2 md2 1 pos HAR2 Hfin2)
      as (_ & _ & Hfpr & _).
    change (fs_frame_bytes 1) with 128 in Hfpr.
    unfold rp_G in Ha.
    assert (Hrng : frame_addr (rc_lyc cx) 1 pos <= a < frame_addr (rc_lyc cx) 1 pos + 128) by lia.
    exact (proj1 (Hfpr a Hrng)).
Qed.

(* ---- rp_R2's local helpers (prefix rp_R2_): the entry symbolic state at C3 (atoms: registers 0..31, atom 32 =
   shadow_addr G; regions: the stack slot rA+16 (base s1 = atom 9), the frame words [G, G+24) (base a0 = atom 10),
   the 16 frame-shadow bytes (base atom 32); facts: HPTR 5 for G and cgif's shadow alias), the stretch's write set,
   and the small memory / layout facts the C4 rebuild uses. *)
Definition rp_R2_ss0 : sstate := mkSS 0x3130 sr_atoms
[YP09.mkRegion (Some 9%nat) 16 24 16 24 [];
 YP09.mkRegion (Some 10%nat) 0 24 0 24 [];
 YP09.mkRegion (Some 32%nat) 0 16 0 16 []] None
(mkFacts [(10%nat, HPTR 5)] [] [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 0) (SLit 3)) (SOff 27 0), SOff 32 0)]).
Definition rp_R2_X (rA G a : Z) : Prop :=
(rA + 16 <= a < rA + 24) \/ (G <= a < G + 24) \/ (SHADOW_OFF + G / 8 <= a < SHADOW_OFF + G / 8 + 16).
Lemma rp_R2_app_band : forall lo len y, in_app lo len -> lo <= y < lo + len ->
4096 <= y /\ (y < SHADOW_OFF \/ SHADOW_OFF + 2 ^ 44 <= y) /\ y < alloc_ceiling.
Proof.
intros lo len y Hl Hy. pose proof ASAN_CEIL_range as [HC _].
unfold in_app, ASAN_CEIL, SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.
Lemma rp_R2_mbyte_kept : forall E rs (m m' : word -> option byte) a,
frame_of E rs m m' -> 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a -> mbyte SEGS m' a = mbyte SEGS m a.
Proof.
intros E rs m m' a HF Ha Hn. unfold mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by lia. exact Hn.
Qed.
Lemma rp_R2_apresent_grows : forall H (m m' : word -> option byte) a,
mem_grows (mrestrict H m) (mrestrict H m') -> apresent H m a -> apresent H m' a.
Proof.
intros H m m' a HG (Hh & b & Hb). split; [exact Hh|].
specialize (HG (Z_to_bv 64 a)). unfold mrestrict in HG. rewrite Hh, Hb in HG.
destruct (m' (Z_to_bv 64 a)) as [b'|]; [exists b'; reflexivity | exfalso; exact (HG ltac:(discriminate) eq_refl)].
Qed.
Lemma rp_R2_aview_grows : forall H (m m' : word -> option byte) a,
mem_grows (mrestrict H m) (mrestrict H m') -> aview SEGS H m a <> None -> aview SEGS H m' a <> None.
Proof.
intros H m m' a HG Hv. unfold aview, mbyte in *.
destruct (mrestrict H m (Z_to_bv 64 a)) eqn:E1.
- pose proof (HG (Z_to_bv 64 a) ltac:(rewrite E1; discriminate)) as E2.
destruct (mrestrict H m' (Z_to_bv 64 a)); [discriminate | exfalso; exact (E2 eq_refl)].
- destruct (mrestrict H m' (Z_to_bv 64 a)); [discriminate | exact Hv].
Qed.
Lemma rp_R2_chunk8 : forall E m base off v,
YP09.chunk_ok SEGS E m base (YP09.mkChunk off (CVal 8 v)) ->
val_mem SEGS m (base + off) 8 (bv_unsigned (sv_denot E v)).
Proof.
intros E m base off v HC k Hk.
destruct (HC (Z.of_nat k) ltac:(cbn; lia)) as (b & Hc & Hm). cbn [cbyte YP09.c_val YP09.c_off] in Hc, Hm.
injection Hc as <-. rewrite Hm. f_equal. unfold byte_of_word.
rewrite le_byte_small by (pose proof (bv_unsigned_in_range 64 (sv_denot E v)) as R; change (bv_modulus 64) with (2 ^ (8 * Z.of_nat 8)) in R; lia || exact R).
reflexivity.
Qed.
Lemma rp_R2_chunk1 : forall E m base off v,
YP09.chunk_ok SEGS E m base (YP09.mkChunk off (CVal 1 v)) ->
mbyte SEGS m (base + off) = Some (byte_of_word (sv_denot E v) 0).
Proof.
intros E m base off v HC. destruct (HC 0 ltac:(cbn; lia)) as (b & Hc & Hm). cbn [cbyte YP09.c_val YP09.c_off] in Hc, Hm.
injection Hc as <-. rewrite Z.add_0_r in Hm. exact Hm.
Qed.
Lemma rp_R2_Forall_nth : forall {A} (P : A -> Prop) l i x, Forall P l -> nth_error l i = Some x -> P x.
Proof. intros A P l i x HF Hn. rewrite Forall_forall in HF. apply HF. exact (nth_error_In l i Hn). Qed.
Lemma rp_R2_rdword_ext : forall (rd rd' : reader) a, (forall k, 0 <= k < 8 -> rd' (a + k) = rd (a + k)) ->
rdword rd' a = rdword rd a.
Proof.
intros rd rd' a H. unfold rdword. pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
rewrite H0, (H 1), (H 2), (H 3), (H 4), (H 5), (H 6), (H 7) by lia. reflexivity.
Qed.
Lemma rp_R2_shadow_cells : forall E H m base cs (sg : list Z),
Forall (YP09.chunk_ok SEGS E (mrestrict H m) base) cs ->
(forall i, (i < length sg)%nat -> exists v, In (YP09.mkChunk (Z.of_nat i) (CVal 1 (SLit v))) cs /\
Some (bv_unsigned (byte_of_word (Z_to_bv 64 v) 0)) = nth_error sg i) ->
forall i, (i < length sg)%nat -> aview SEGS H m (base + Z.of_nat i) = nth_error sg i.
Proof.
intros E H m base cs sg HF Hc i Hi. destruct (Hc i Hi) as (v & Hin & Hv).
rewrite Forall_forall in HF. pose proof (rp_R2_chunk1 _ _ _ _ _ (HF _ Hin)) as Hm.
unfold aview. rewrite Hm. cbn [option_map sv_denot]. exact Hv.
Qed.
(* the write set misses: addresses above the ceiling outside this call's window; application addresses outside
   the own frame; the shadow of such an address; the shadow of a frame disjoint from the own frame. *)
Lemma rp_R2_notX_high : forall S rA G a, S - 144 <= rA <= S - 128 -> 0 <= G -> G + 128 <= alloc_ceiling ->
alloc_ceiling + TREPLY_STK <= S -> alloc_ceiling <= a -> ~ (S - TREPLY_STK <= a < S) -> ~ rp_R2_X rA G a.
Proof.
intros S rA G a H1 H2 H3 H4 H5 H6 HX. pose proof alloc_ceiling_value as (HAC & _). pose proof rp_stk as (Tstk & Pstk).
pose proof (Z.div_mod G 8 ltac:(lia)). pose proof (Z.mod_pos_bound G 8 ltac:(lia)).
unfold rp_R2_X, SHADOW_OFF in HX. lia.
Qed.
Lemma rp_R2_notX_app : forall rA G lo len y, in_app lo len -> lo <= y < lo + len -> in_app G 128 ->
~ (G <= y < G + 128) -> alloc_ceiling <= rA -> ~ rp_R2_X rA G y.
Proof.
intros rA G lo len y Hl Hy HG Hn Hr HX. pose proof alloc_ceiling_value as (HAC & _).
pose proof (rp_R2_app_band lo len y Hl Hy) as (Y1 & Y2 & Y3).
pose proof (Z.div_mod G 8 ltac:(unfold in_app in HG; lia)). pose proof (Z.mod_pos_bound G 8 ltac:(lia)).
unfold in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in HG. unfold rp_R2_X, SHADOW_OFF in *. lia.
Qed.
Lemma rp_R2_notX_sh : forall rA G x, 0 <= x < alloc_ceiling -> in_app G 128 -> G mod 8 = 0 ->
~ (G <= x < G + 128) -> alloc_ceiling <= rA -> ~ rp_R2_X rA G (SHADOW_OFF + x / 8).
Proof.
intros rA G x Hx HG HG8 Hn Hr HX. pose proof alloc_ceiling_value as (HAC & _).
pose proof (Z.div_mod G 8 ltac:(lia)). pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)).
unfold in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in HG. unfold rp_R2_X, SHADOW_OFF in *. lia.
Qed.
Lemma rp_R2_notX_shr : forall rA G F n a, in_app F n -> F mod 8 = 0 -> n mod 8 = 0 -> 0 <= n ->
in_app G 128 -> G mod 8 = 0 -> (F + n <= G \/ G + 128 <= F) -> alloc_ceiling <= rA ->
SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + n / 8 -> ~ rp_R2_X rA G a.
Proof.
intros rA G F n a HF HF8 Hn8 Hn HG HG8 Hd Hr Ha HX. pose proof alloc_ceiling_value as (HAC & _).
pose proof (Z.div_mod F 8 ltac:(lia)). pose proof (Z.div_mod n 8 ltac:(lia)). pose proof (Z.div_mod G 8 ltac:(lia)).
unfold in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in HF, HG. unfold rp_R2_X, SHADOW_OFF in *. lia.
Qed.
Lemma rp_R2_mod8 : forall x k, x mod (8 * k) = 0 -> 0 < k -> x mod 8 = 0.
Proof.
intros x k H Hk. apply Z.mod_divide in H; [|lia]. destruct H as [q Hq]. subst x.
replace (q * (8 * k)) with ((q * k) * 8) by lia. apply Z.mod_mul. lia.
Qed.
Lemma rp_R2_notX_win : forall S rA G a, S - 144 <= rA <= S - 128 -> 0 <= G -> G + 128 <= alloc_ceiling ->
alloc_ceiling + TREPLY_STK <= S -> S - 104 <= a -> ~ rp_R2_X rA G a.
Proof.
intros S rA G a H1 H2 H3 H4 H5 HX. pose proof alloc_ceiling_value as (HAC & _). pose proof rp_stk as (Tstk & Pstk).
pose proof (Z.div_mod G 8 ltac:(lia)). pose proof (Z.mod_pos_bound G 8 ltac:(lia)).
unfold rp_R2_X, SHADOW_OFF in HX. lia.
Qed.
Lemma rp_R2_notX_own : forall rA G y, in_app G 128 -> G + 24 <= y < G + 128 -> alloc_ceiling <= rA ->
~ rp_R2_X rA G y.
Proof.
intros rA G y HG Hy Hr HX. pose proof alloc_ceiling_value as (HAC & _).
pose proof (Z.div_mod G 8 ltac:(unfold in_app in HG; lia)). pose proof (Z.mod_pos_bound G 8 ltac:(lia)).
unfold in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in HG. unfold rp_R2_X, SHADOW_OFF in *. lia.
Qed.

(* R2  C3 -> C4, 0x8400c..0x840b8 (+0x80..+0x12c). `bnez s2` at 0x8401c decided by `frames_bounds`
   (4096 <= G), so the real-stack arm is dead; then `sd s10,16(s1)`, the three frame words and the 16 shadow
   bytes. The state surgery is cgif AChf.v:241-343 (the frame region with the chunk at 120, the frame-shadow
   region `fshadow_region`, the facts HPTR 5 / the shadow alias); writes justified by `awr_byte`'s `in_frames`
   case on own' = (1,pos)::own. Donors: B `rp_fwords` :1145, `rk_facts` :1077, `rBI` :1067; A18 `seg_prologue`
   :1655 (tail), `rr_geo` :775, `PRO` :909. Difficulty: HARD (the biggest state-building step). *)
Lemma rp_R2 : rp_from_C4 -> rp_from_C3.
Proof.
intros F4 cx pos regs3 ly3 S3 W3 mem3 md3 HB HC3.
destruct HC3 as (HJH & -> & -> & HCA & H10 & HZS & HFLw & HFP).
pose proof HJH as (HJ & Hlyok & Hfrs & Hnin & Hab & Hcnt).
pose proof HCA as (HRG & (HwW & HK) & HSV & HMSG & HOUT & HROD).
pose proof HK as (HK1 & HK2 & HK3 & HK4 & HK5 & HK6).
pose proof HB as (HJ0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HS16 & HSTK & HSsp0 & _ & HLG & HMSGB & HCELLB).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HASTK & _).
pose proof HASTK as (_ & HSTK0 & Hstk1 & Hstk2 & Hstk3 & Hstk4 & _).
pose proof HRG as (R2 & R3 & R4 & R8 & R9 & R19 & R20 & R21 & R22 & R23 & R27).
pose proof rp_stk as (Tstk & Pstk).
pose proof alloc_ceiling_value as (HAC & _).
pose proof (Z.div_mod (rp_S cx) 16 ltac:(lia)) as D16. rewrite HS16, Z.add_0_r in D16.
assert (HrA : rp_S cx - 144 <= rp_rA cx <= rp_S cx - 128 /\ rp_rA cx mod 32 = 0).
{ unfold rp_rA. pose proof (Z.div_mod (rp_S cx - 128) 32 ltac:(lia)). pose proof (Z.mod_pos_bound (rp_S cx - 128) 32 ltac:(lia)).
split; [lia|]. rewrite Z.mul_comm, Z.mod_mul by lia. reflexivity. }
destruct HrA as (HrA & HrA32).
assert (HSlo : alloc_ceiling + TREPLY_STK <= rp_S cx) by lia.
assert (HShi : rp_S cx <= 2 ^ 47) by lia.
assert (Hin1 : In (1, pos) (frames S3)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 pos HAR Hin1) as (HG4 & HGc & HGapp).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 pos HAR Hin1) as (HGal & _ & HGpres & HGSpres).
assert (FB1 : fs_frame_bytes 1 = 128) by reflexivity.
rewrite FB1 in HGc, HGapp, HGpres, HGSpres. change (128 / 8) with 16 in HGSpres.
fold (rp_G cx pos) in HG4, HGc, HGapp, HGal, HGpres, HGSpres.
assert (HGq : rp_G cx pos = 32 * (rp_G cx pos / 32)) by (pose proof (Z.div_mod (rp_G cx pos) 32 ltac:(lia)); lia).
assert (HG8 : rp_G cx pos / 8 = 4 * (rp_G cx pos / 32)).
{ rewrite HGq at 1. replace (32 * (rp_G cx pos / 32)) with (4 * (rp_G cx pos / 32) * 8) by lia. apply Z.div_mul. lia. }
remember (Eimg (Ereg regs3 [Z_to_bv 64 (SHADOW_OFF + rp_G cx pos / 8)])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs3 r).
{ intros n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr. change (bv_modulus 5) with 32 in Hr.
subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (E32 : ew E 32 = Z_to_bv 64 (SHADOW_OFF + rp_G cx pos / 8)).
{ subst E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs3 _ 0). }
assert (HRE : regs_ok E sr_atoms regs3) by (subst E; apply regs_ok_Eimg_Ereg).
clear HE.
assert (E9 : ew E 9 = w64 (rp_rA cx)) by (rewrite (EE 9%nat 9%bv eq_refl); exact R9).
assert (E10 : ew E 10 = w64 (rp_G cx pos)) by (rewrite (EE 10%nat 10%bv eq_refl); exact H10).
assert (E27 : ew E 27 = w64 SHADOW_OFF) by (rewrite (EE 27%nat 27%bv eq_refl); exact R27).
assert (U9 : bv_unsigned (ew E 9) = rp_rA cx) by (rewrite E9; unfold w64; apply unsigned_lit_small; lia).
assert (U10 : bv_unsigned (ew E 10) = rp_G cx pos) by (rewrite E10; unfold w64; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = SHADOW_OFF + rp_G cx pos / 8) by (rewrite E32; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (HS : st_ok_pi SEGS VAL E rp_R2_ss0 (restrict (w_H (rc_W cx)) (mkst regs3 (w64 (rp_pc 0x80)) mem3 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx.
replace (w64 (rp_pc 0x80)) with (Z_to_bv 64 (BASE + 0x3130))
by (unfold rp_pc, A_reac_ctrl_identity_replyP, w64, AF_reac_ctrl_identity_reply; f_equal; lia).
unfold rp_R2_ss0. apply (pa_entry_st_ok_full (L := ctrl_listing) (PI := CtrlImg.PI_ctrl)).
- exact HRE.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]];
unfold YP09.region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
+ rewrite U9. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
intros o Ho. apply (apresent_writable SEGS). apply HK6. lia.
+ rewrite U10. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
intros o Ho. apply (apresent_writable SEGS). apply HFP. lia.
+ rewrite U32. split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split; [|apply Forall_nil].
intros o Ho. apply (apresent_writable SEGS). pose proof (proj1 (HGSpres o ltac:(lia))) as Hp. unfold shadow_addr in Hp. exact Hp.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
rewrite U9, U10, U32. pose proof (rp_R2_app_band _ _ (rp_G cx pos) HGapp ltac:(lia)) as Hb.
repeat split; unfold SHADOW_OFF in *; lia.
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
split; [split; [|exact I]|]; [unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite U10; change (2 ^ 5) with 32; lia|].
split; [exact I|]. split; [|exact I].
exact (shadow_decl_ok E 10 27 32 (rp_G cx pos) SHADOW_OFF E10 ltac:(lia) E27 E32). }
assert (HGm8 : rp_G cx pos mod 8 = 0) by exact (rp_R2_mod8 _ 4 HGal ltac:(lia)).
assert (HrAc : alloc_ceiling <= rp_rA cx) by lia.
assert (NW : forall a, in_wrange E (ss_mem rp_R2_ss0) a -> rp_R2_X (rp_rA cx) (rp_G cx pos) a).
{ intros a (r & Hin & Hr). unfold rp_R2_ss0 in Hin. cbn in Hin.
destruct Hin as [<-|[<-|[<-|[]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
[rewrite U9 in Hr | rewrite U10 in Hr | rewrite U32 in Hr]; unfold rp_R2_X; lia. }
unfold cfg_at.
pose proof (SRr_run_to_pi_AJ (PI := CtrlImg.PI_ctrl) (PL := PL_ctrl) B LAWS) as RUNTOP.
paj_run_to_sh RUNTOP HS HJ 0x31e0.
{ intros a Hw. apply NW in Hw. unfold awr_byte. unfold rp_R2_X in Hw. destruct Hw as [Hw|[Hw|Hw]].
- left. lia.
- right; right; right. exists 1, pos. split; [unfold rp_own1; left; reflexivity|].
left. unfold in_zr. cbn [fst snd]. rewrite FB1. unfold rp_G in Hw. lia.
- right; right; right. exists 1, pos. split; [unfold rp_own1; left; reflexivity|].
right. unfold in_zr, shadow_addr. cbn [fst snd]. rewrite FB1. change (128 / 8) with 16. unfold rp_G in Hw. lia. }
cbn [ms_mem] in HF, HFr, HG.
pose proof (st_ok_mem_ok pa_segs E _ _ HS) as (_ & HRO & _). cbn [ms_mem restrict] in HRO.
prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19.
prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23.
prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
pmkst HS.
set (mem4 := ms_mem ms) in *. set (regs4 := ms_regs ms) in *. set (md4 := with_vm_backing (m_vm_lazy md3) mat md3) in *.
replace (Z_to_bv 64 (BASE + 12768)) with (w64 (rp_pc 0x130))
by (unfold rp_pc, A_reac_ctrl_identity_replyP, w64, AF_reac_ctrl_identity_reply; f_equal; lia).
change (SRr SEGS (rc_W cx) (cfg_at SEGS (rp_pc 0x130) regs4 mem4 md4) (rp_post cx)).
apply (F4 cx pos regs4 (rc_lyc cx) S3 (rc_W cx) mem4 md4 HB).
(* what the run kept: everything outside the write set rp_R2_X *)
assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ rp_R2_X (rp_rA cx) (rp_G cx pos) a ->
mbyte SEGS (mrestrict (w_H (rc_W cx)) mem4) a = mbyte SEGS (mrestrict (w_H (rc_W cx)) mem3) a).
{ intros a Ha Hx. apply (rp_R2_mbyte_kept E (ss_mem rp_R2_ss0)); [exact HFr | exact Ha | intros Hw; exact (Hx (NW a Hw))]. }
assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ rp_R2_X (rp_rA cx) (rp_G cx pos) a ->
aview SEGS (w_H (rc_W cx)) mem4 a = aview SEGS (w_H (rc_W cx)) mem3 a).
{ intros a Ha Hx. unfold aview. rewrite (KM a Ha Hx). reflexivity. }
assert (KV : forall a n v, 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
(forall k, 0 <= k < Z.of_nat n -> ~ rp_R2_X (rp_rA cx) (rp_G cx pos) (a + k)) ->
val_mem SEGS (mrestrict (w_H (rc_W cx)) mem3) a n v -> val_mem SEGS (mrestrict (w_H (rc_W cx)) mem4) a n v).
{ intros a n v Ha Hn Hx Hv k Hk. rewrite KM by (lia || (apply Hx; lia)). exact (Hv k Hk). }
assert (NXi : forall a, in_img SEGS a -> 0 <= a < 2 ^ 64 /\ ~ rp_R2_X (rp_rA cx) (rp_G cx pos) a).
{ intros a Ha. pose proof (CtrlImg.ctrl_img_range a Ha) as Hr. split; [lia|]. intros HX.
unfold rp_R2_X in HX. destruct HX as [HX|[HX|HX]]; [lia| |unfold SHADOW_OFF in HX; lia].
assert (Hc : exists cid pos', In (cid, pos') (frames S3) /\
frame_addr (rc_lyc cx) cid pos' <= a < frame_addr (rc_lyc cx) cid pos' + fs_frame_bytes cid)
by (exists 1, pos; split; [exact Hin1 | rewrite FB1; fold (rp_G cx pos); lia]).
destruct (al_client_img _ _ LAWS _ _ _ _ _ a HAR (or_intror (or_introl Hc))) as [_ Hni]. exact (Hni Ha). }
unfold rp_C4.
refine (conj _ (conj eq_refl (conj eq_refl (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))).
- (* rp_jhold *)
exact (conj HJ (conj Hlyok (conj Hfrs (conj Hnin (conj Hab Hcnt))))).
- (* rp_carry *)
unfold rp_carry. refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
+ unfold rp_regs_ok.
rewrite Q2, Q3, Q4, Q8, Q9, Q19, Q20, Q21, Q22, Q23, Q27, (EE 2%nat 2%bv eq_refl), (EE 3%nat 3%bv eq_refl),
(EE 4%nat 4%bv eq_refl), (EE 8%nat 8%bv eq_refl), (EE 9%nat 9%bv eq_refl), (EE 19%nat 19%bv eq_refl),
(EE 20%nat 20%bv eq_refl), (EE 21%nat 21%bv eq_refl), (EE 22%nat 22%bv eq_refl), (EE 23%nat 23%bv eq_refl),
(EE 27%nat 27%bv eq_refl). exact HRG.
+ unfold rp_kept. split; [exact HwW|]. unfold tcj_kept.
refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
* intros a Ha Hw Hn.
assert (NX : ~ rp_R2_X (rp_rA cx) (rp_G cx pos) a) by (apply (rp_R2_notX_high (rp_S cx)); [lia | lia | lia | lia | lia | exact Hw]).
etransitivity; [exact (KA a ltac:(lia) NX)|]. exact (HK1 a Ha Hw Hn).
* intros b m i Hbm Hi Hn. assert (Hbm3 : In (b, m) (ablocks B (rc_lyc cx) S3)) by (rewrite Hab; exact Hbm).
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hbm3) as (Hb16 & Hb4096 & Hbc & Hbapp & _).
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ b m 1 pos HAR Hbm3 Hin1) as Hsep.
unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. rewrite FB1 in Hsep. fold (rp_G cx pos) in Hsep.
assert (NX : ~ rp_R2_X (rp_rA cx) (rp_G cx pos) (b + i))
by (apply (rp_R2_notX_app _ _ b (req_size m)); [exact Hbapp | lia | exact HGapp | lia | exact HrAc]).
etransitivity; [exact (KA (b + i) ltac:(lia) NX)|]. exact (HK2 b m i Hbm Hi Hn).
* intros a Himg Hown Herr.
etransitivity; [exact (KA a (proj1 (NXi a Himg)) (proj2 (NXi a Himg)))|]. exact (HK3 a Himg Hown Herr).
* intros cid' pos' a Hin' Ha Hn.
assert (Hin3 : In (cid', pos') (frames S3)) by (rewrite Hfrs; right; exact Hin').
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid' pos' HAR Hin3) as (HF4 & HFc & HFapp).
destruct (frame_al64 SEGS B _ _ _ _ _ cid' pos' HAR Hin3) as (HF64 & HB64 & HB64').
destruct (in_split _ _ Hin') as (l2 & l3 & Hsp).
pose proof (sep_frames_pos SEGS B LAWS _ _ _ _ _ (1, pos) (cid', pos') [] l2 l3 HAR ltac:(rewrite Hfrs, Hsp; reflexivity)) as Hsep.
unfold zdisjoint, frame_rng in Hsep. cbn [fst snd] in Hsep. rewrite FB1 in Hsep. fold (rp_G cx pos) in Hsep.
assert (NXa : 0 <= a < 2 ^ 64 /\ ~ rp_R2_X (rp_rA cx) (rp_G cx pos) a).
{ destruct Ha as [Ha|Ha]; unfold in_zr, frame_rng in Ha; cbn [fst snd] in Ha.
- split; [lia|]. exact (rp_R2_notX_app _ _ _ _ a HFapp ltac:(lia) HGapp ltac:(lia) HrAc).
- unfold shadow_addr in Ha.
pose proof (rp_R2_mod8 _ 8 HF64 ltac:(lia)) as Hfm8. pose proof (rp_R2_mod8 _ 8 HB64 ltac:(lia)) as Hbm8.
split.
+ pose proof (Z.div_mod (frame_addr (rc_lyc cx) cid' pos') 8 ltac:(lia)).
pose proof (Z.div_mod (fs_frame_bytes cid') 8 ltac:(lia)). unfold SHADOW_OFF in Ha. lia.
+ exact (rp_R2_notX_shr _ _ _ (fs_frame_bytes cid') a HFapp Hfm8 Hbm8 ltac:(lia) HGapp HGm8 ltac:(lia) HrAc Ha). }
etransitivity; [exact (KA a (proj1 NXa) (proj2 NXa))|]. exact (HK4 cid' pos' a Hin' Ha Hn).
* intros a Ha Hw Hp. exact (rp_R2_apresent_grows _ _ _ _ HG (HK5 a Ha Hw Hp)).
* intros a Ha. exact (rp_R2_apresent_grows _ _ _ _ HG (HK6 a Ha)).
+ unfold rp_saved in HSV |- *. rewrite Forall_forall in HSV |- *. intros p Hp. pose proof (HSV p Hp) as Hv.
destruct p as [d r].
assert (Hd : 8 <= d <= 104)
by (unfold rp_saves in Hp; cbn in Hp; repeat (destruct Hp as [Hp|Hp]; [injection Hp as <- <-; lia|]); destruct Hp).
cbn [fst snd] in Hv |- *. apply KV; [lia | lia | | exact Hv].
intros k Hk. apply (rp_R2_notX_win (rp_S cx)); lia.
+ unfold rp_msg in HMSG |- *. intros Hargs Hlen. destruct (HMSG Hargs Hlen) as (Hg & Hts).
destruct (HMSGB Hargs Hlen) as ((nb & Hnb & Hnb50) & _ & _).
assert (Hnb3 : In (rc_fr cx, nb) (ablocks B (rc_lyc cx) S3)) by (rewrite Hab; exact Hnb).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hnb3) as (Hb16 & Hb4096 & Hbc & Hbapp & _).
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ 1 pos HAR Hnb3 Hin1) as Hsep.
unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. rewrite FB1 in Hsep. fold (rp_G cx pos) in Hsep.
assert (NXm : forall x, rc_fr cx <= x < rc_fr cx + 50 ->
0 <= x < 2 ^ 64 /\ ~ rp_R2_X (rp_rA cx) (rp_G cx pos) x /\
0 <= SHADOW_OFF + x / 8 < 2 ^ 64 /\ ~ rp_R2_X (rp_rA cx) (rp_G cx pos) (SHADOW_OFF + x / 8)).
{ intros x Hx. pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)).
split; [lia|]. split; [exact (rp_R2_notX_app _ _ _ _ x Hbapp ltac:(lia) HGapp ltac:(lia) HrAc)|].
split; [unfold SHADOW_OFF; lia|]. apply rp_R2_notX_sh; [lia | exact HGapp | exact HGm8 | lia | exact HrAc]. }
split.
* intros j Hj. destruct (Hg j Hj) as (Hv & Hr). split; [|exact Hr].
rewrite length_map, HLG in Hj. apply KV; [lia | lia | | exact Hv].
intros k Hk. cbn [Z.of_nat] in Hk. replace k with 0 by lia. rewrite Z.add_0_r.
assert (HjZ : 0 <= Z.of_nat j < 50) by lia.
exact (proj1 (proj2 (NXm (rc_fr cx + Z.of_nat j) ltac:(lia)))).
* destruct Hts as (T1 & T2 & T3 & T4 & T5 & T6).
split; [|split; [|split; [|exact (conj T4 (conj T5 T6))]]].
-- intros a Ha. destruct (T1 a Ha) as (Ta & Tb). split; [|exact Tb]. exact (rp_R2_aview_grows _ _ _ _ HG Ta).
-- intros x Hx. destruct (T2 x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
unfold shadow_of_addr in *. destruct (NXm x Hx) as (_ & _ & N1 & N2). etransitivity; [exact (KA _ N1 N2)|]. exact Hs.
-- intros s Hs. exact (rp_R2_aview_grows _ _ _ _ HG (T3 s Hs)).
+ unfold rp_out in HOUT |- *. intros Hargs. destruct (HOUT Hargs) as (Ra & Rp & Rn & Rpres).
destruct (HCELLB Hargs) as (_ & _ & _ & _ & _ & _ & Hfrm & _).
assert (NXc : forall x, treply_out (rc_pa cx) (rc_pp cx) (rc_pn cx) x ->
0 <= SHADOW_OFF + x / 8 < 2 ^ 64 /\ ~ rp_R2_X (rp_rA cx) (rp_G cx pos) (SHADOW_OFF + x / 8)).
{ intros x Hx. destruct (Hfrm x Hx) as (cid' & pos' & Hin' & Hxr).
assert (Hin3 : In (cid', pos') (frames S3)) by (rewrite Hfrs; right; exact Hin').
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid' pos' HAR Hin3) as (HF4 & HFc & HFapp).
destruct (in_split _ _ Hin') as (l2 & l3 & Hsp).
pose proof (sep_frames_pos SEGS B LAWS _ _ _ _ _ (1, pos) (cid', pos') [] l2 l3 HAR ltac:(rewrite Hfrs, Hsp; reflexivity)) as Hsep.
unfold zdisjoint, frame_rng in Hsep. cbn [fst snd] in Hsep. rewrite FB1 in Hsep. fold (rp_G cx pos) in Hsep.
unfold in_zr, frame_rng in Hxr. cbn [fst snd] in Hxr.
pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)).
split; [unfold SHADOW_OFF; lia|]. apply rp_R2_notX_sh; [lia | exact HGapp | exact HGm8 | lia | exact HrAc]. }
refine (conj _ (conj _ (conj _ _))).
* intros x Hx. destruct (Ra x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok]. unfold shadow_of_addr in *.
destruct (NXc x ltac:(unfold treply_out; lia)) as (N1 & N2). etransitivity; [exact (KA _ N1 N2)|]. exact Hs.
* intros x Hx. destruct (Rp x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok]. unfold shadow_of_addr in *.
destruct (NXc x ltac:(unfold treply_out; lia)) as (N1 & N2). etransitivity; [exact (KA _ N1 N2)|]. exact Hs.
* intros x Hx. destruct (Rn x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok]. unfold shadow_of_addr in *.
destruct (NXc x ltac:(unfold treply_out; lia)) as (N1 & N2). etransitivity; [exact (KA _ N1 N2)|]. exact Hs.
* intros a Ha. exact (rp_R2_apresent_grows _ _ _ _ HG (Rpres a Ha)).
+ unfold YE01.arodata_okS in HROD |- *. intros a Ha Hown Herr.
assert (Himg : in_img SEGS a).
{ destruct Ha as [(s & Hs & _ & Hr)|Hr]; [exists s; split; [exact Hs | exact Hr] | exact (RELRO_IMG a Hr)]. }
etransitivity; [exact (KA a (proj1 (NXi a Himg)) (proj2 (NXi a Himg)))|]. exact (HROD a Ha Hown Herr).
- (* rp_fregs *)
unfold rp_fregs. rewrite Q18, Q26, Q25, E10, E32. split; [reflexivity|]. split; [reflexivity|].
unfold shadow_addr, w64. reflexivity.
- (* rp_fpres *)
unfold rp_fpres. intros a Ha. exact (rp_R2_apresent_grows _ _ _ _ HG (HFP a Ha)).
- (* rp_fwords *)
pose proof (rp_R2_Forall_nth _ _ 1 _ HRO eq_refl) as RF1. destruct RF1 as (_ & _ & _ & HC1).
cbn [YP09.r_chunks YP09.r_base base_val] in HC1. rewrite U10 in HC1.
pose proof (rp_R2_chunk8 _ _ _ _ _ (rp_R2_Forall_nth _ _ 0 _ HC1 eq_refl)) as W16.
pose proof (rp_R2_chunk8 _ _ _ _ _ (rp_R2_Forall_nth _ _ 1 _ HC1 eq_refl)) as W8.
pose proof (rp_R2_chunk8 _ _ _ _ _ (rp_R2_Forall_nth _ _ 2 _ HC1 eq_refl)) as W0.
cbn [sv_denot] in W16, W8, W0.
rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (HEI 257%nat ltac:(unfold A_TEXT, A_LIM; lia)) in W16.
rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (HEI 256%nat ltac:(unfold A_TEXT, A_LIM; lia)) in W8.
rewrite Z.add_0_r, unsigned_lit_small in W0 by lia.
unfold rp_fwords. refine (conj W0 (conj W8 (conj W16 _))).
rewrite (rp_R2_rdword_ext (aview SEGS (w_H (rc_W cx)) mem3)); [exact HFLw|].
intros k Hk. apply KA; [lia|]. apply rp_R2_notX_own; [exact HGapp | lia | exact HrAc].
- (* rp_shadow *)
pose proof (rp_R2_Forall_nth _ _ 2 _ HRO eq_refl) as RF2. destruct RF2 as (_ & _ & _ & HC2).
cbn [YP09.r_chunks YP09.r_base base_val] in HC2. rewrite U32 in HC2.
unfold rp_shadow, shadow_cells, shadow_of_addr. intros i Hi.
apply (rp_R2_shadow_cells E _ _ _ _ _ HC2); [|exact Hi].
intros j Hj. unfold rp_sg_frame in Hj. cbn [length] in Hj.
do 16 (destruct j as [|j]; [eexists; split; [cbn [In]; repeat (first [left; reflexivity | right]) | vm_compute; reflexivity] |]).
lia.
- (* the stack slot rA+16 *)
pose proof (rp_R2_Forall_nth _ _ 0 _ HRO eq_refl) as RF0. destruct RF0 as (_ & _ & _ & HC0).
cbn [YP09.r_chunks YP09.r_base base_val] in HC0. rewrite U9 in HC0.
pose proof (rp_R2_chunk8 _ _ _ _ _ (rp_R2_Forall_nth _ _ 0 _ HC0 eq_refl)) as WS.
cbn [sv_denot] in WS. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, U10 in WS. exact WS.
- (* a0 = -1 *)
rewrite Q10. unfold w64. apply bv_eq. vm_compute. reflexivity.
Qed.

(* ---- R34 local helpers (named rp_R34_*, local to this stretch) ---------------------------------- *)
(* The kept clause is anti-monotone in its exception set: what C4 keeps with no exception, C12 and C5
   keep with any.  (No kit lemma: CtrlCallerJ.v states tcj_kept and proves nothing about it.) *)
Lemma rp_R34_kept_any : forall cx (W3 : world SEGS) (mem3 : word -> option byte) (Er : Z -> Prop),
rp_kept cx W3 mem3 rp_Enone -> rp_kept cx W3 mem3 Er.
Proof.
intros cx W3 mem3 Er (Hwle & K1 & K2 & K3 & K4 & K5 & K6).
split; [exact Hwle|].
split; [intros a H1 H2 _; exact (K1 a H1 H2 (fun Hx : False => Hx))|].
split; [intros b m i H1 H2 _; exact (K2 b m i H1 H2 (fun Hx : False => Hx))|].
split; [exact K3|].
split; [intros cid ps a H1 H2 _; exact (K4 cid ps a H1 H2 (fun Hx : False => Hx))|].
split; [exact K5 | exact K6].
Qed.

(* R34  C4 -> C5 or C12, 0x840bc..0x840f0 (+0x130..+0x164). The four null tests (`psrr_branch_tok` x4; the
   taken arm goes to C12 with a0 = -1 and reply_args = false), then, on the non-null arm, s8 := G+32 and the
   five shadow stores SG[4..7] := 0, SG[8] := 4, which give `range_addressable (G+32) 36`; the three argument
   moves. (This is rows R3 and R4 of the accepted plan: no cut of C0..C14 separates them.)
   Donors: B `rp_null` :1608, `rr_unp_run` :1839, `rr_BI_unp` :1906, `rr_unpoison_addr` :512; A18 `seg_null`
   :1593, `rr_unpoison_steps` :2558, `rr_unpoison_addr` :522. Difficulty: medium. *)
Lemma rp_R34 : rp_from_C5 -> rp_from_C12 -> rp_from_C4.
Proof.
intros K5 K12 cx pos regs3 ly3 S3 W3 mem3 md3 HBASE HC4.
pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
pose proof HBASE as (HJ0 & HRO0 & Hra & Hra4 & Hgp0 & Htp0 & Ha10 & Ha11 & Ha12 & Ha13 & Ha14 &
Hfrr & Hlenr & Hpar & Hppr & Hpnr & HS16 & HSwin & HSsp0 & Hcnt & Hglen & Hmsg0 & Hout0).
destruct HC4 as ((HJ & HLY & HFRS & HNIN & HAB & HCNT) & Ely & EW & HCAR & HFREG & HFPRES & HFW & HSG & HrA & Ha0).
subst ly3. subst W3.
destruct HFREG as (R18 & R26 & R25).
destruct HCAR as (HREGS & HKEPT & HSAVED & HMSG & HOUT & HROD).
destruct HREGS as (R2 & R3 & R4 & R8 & R9 & R19 & R20 & R21 & R22 & R23 & R27).
pose proof (proj1 HJ) as HAR.
assert (Hfin : In (1, pos) (frames S3)) by (rewrite HFRS; left; reflexivity).
assert (EG : frame_addr (rc_lyc cx) 1 pos = rp_G cx pos) by reflexivity.
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 pos HAR Hfin) as (HFal & HFapp & HFpr & HFSpr).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 pos HAR Hfin) as (HF4096 & HFceil & HFhigh).
change (fs_frame_bytes 1) with 128 in *.
rewrite EG in HFal, HFapp, HFpr, HFSpr, HF4096, HFceil, HFhigh.
change (128 / 8) with 16 in HFSpr.
pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
set (G := rp_G cx pos) in *.
assert (HG8lo : 512 <= G / 8) by (apply Z.div_le_lower_bound; lia).
assert (HG8hi : G / 8 <= 17592186044416) by (apply Z.div_le_upper_bound; lia).
assert (ESA : shadow_addr G = SHADOW_OFF + G / 8) by reflexivity.
set (SA := shadow_addr G) in *.
assert (HSAlo : 2147451392 <= SA) by (rewrite ESA; unfold SHADOW_OFF; lia).
assert (HSAhi : SA + 16 <= 35184372088832) by (rewrite ESA; unfold SHADOW_OFF; lia).
remember (Eimg (Ereg regs3 (@nil word))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs3 r)
by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E25 : ew E 25 = Z_to_bv 64 SA) by (rewrite (EE 25%nat 25%bv eq_refl); exact R25).
assert (E19 : ew E 19 = Z_to_bv 64 (rc_pn cx)) by (rewrite (EE 19%nat 19%bv eq_refl); exact R19).
assert (E20 : ew E 20 = Z_to_bv 64 (rc_pp cx)) by (rewrite (EE 20%nat 20%bv eq_refl); exact R20).
assert (E21 : ew E 21 = Z_to_bv 64 (rc_pa cx)) by (rewrite (EE 21%nat 21%bv eq_refl); exact R21).
assert (E22 : ew E 22 = Z_to_bv 64 (rc_fr cx)) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
assert (E2 : ew E 2 = w64 (rp_rA cx)) by (rewrite (EE 2%nat 2%bv eq_refl); exact R2).
assert (E3 : ew E 3 = w64 (as_gp B)) by (rewrite (EE 3%nat 3%bv eq_refl); exact R3).
assert (E4 : ew E 4 = w64 (as_tp B)) by (rewrite (EE 4%nat 4%bv eq_refl); exact R4).
assert (E8 : ew E 8 = w64 (rp_S cx)) by (rewrite (EE 8%nat 8%bv eq_refl); exact R8).
assert (E9 : ew E 9 = w64 (rp_rA cx)) by (rewrite (EE 9%nat 9%bv eq_refl); exact R9).
assert (E10 : ew E 10 = w64 (-1)) by (rewrite (EE 10%nat 10%bv eq_refl); exact Ha0).
assert (E18 : ew E 18 = w64 G) by (rewrite (EE 18%nat 18%bv eq_refl); exact R18).
assert (E23 : ew E 23 = w64 (rc_len cx)) by (rewrite (EE 23%nat 23%bv eq_refl); exact R23).
assert (E26 : ew E 26 = w64 G) by (rewrite (EE 26%nat 26%bv eq_refl); exact R26).
assert (E27 : ew E 27 = w64 SHADOW_OFF) by (rewrite (EE 27%nat 27%bv eq_refl); exact R27).
assert (B25 : base_val E (Some 25%nat) = SA)
by (cbn [base_val]; rewrite E25; apply unsigned_lit_small; lia).
pose proof (pa_entry_st_ok_full (PI := CtrlImg.PI_ctrl) E (AF_reac_ctrl_identity_reply + 0x130) sr_atoms regs3
[YP09.mkRegion (Some 25%nat) 0 16 0 0 (@nil YP09.chunk)]
(mkFacts [(25%nat, mkAF 2147451392 35184372088832 0)] [] [])
(mrestrict (w_H (rc_W cx)) mem3)
ltac:(subst E; apply regs_ok_Eimg_Ereg)
ltac:(vm_compute; reflexivity)
ltac:(apply Forall_cons; [|apply Forall_nil]; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks];
rewrite B25; split; [lia|];
split; [change (2 ^ 64) with 18446744073709551616; lia|]; split; [intros o Ho; lia|apply Forall_nil])
ltac:(cbn [pairwise_disjoint all_disjoint]; split; exact I)
ltac:(split; [cbn [atoms_ok]; split;
[unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E25, unsigned_lit_small by lia;
rewrite Z.pow_0_r, Z.mod_1_r; lia | exact I] | split; exact I])) as HS.
rewrite <- restrict_mkst_fx in HS.
assert (SHOK : sh_ok SEGS (SLit SHADOW_OFF) (@nil shent) E (mrestrict (w_H (rc_W cx)) mem3)) by constructor.
assert (HMcur : forall x : word, (mem3 : word -> option byte) x = mem3 x) by reflexivity.
pose proof (paj_run B LAWS) as RUN.
pose proof (paj_run_to B LAWS) as RUNTO.
pose proof (paj_branch (L := ctrl_listing)) as BR.
unfold cfg_at, rp_pc, A_reac_ctrl_identity_replyP.
replace (w64 (BASE + AF_reac_ctrl_identity_reply + 0x130))
with (Z_to_bv 64 (BASE + (AF_reac_ctrl_identity_reply + 0x130))) by (unfold w64; f_equal; lia).
psrr_branch_tok RUN BR HS SHOK (0, 0).
{ (* 0x840bc: fr = 0, the null arm *)
  lazymatch goal with Hx : branch_taken _ _ _ = true |- _ => rename Hx into HcT end.
  rewrite branch_eq_U in HcT.
  rewrite ?(U_atom E 19 (rc_pn cx) E19), ?(U_atom E 20 (rc_pp cx) E20),
          ?(U_atom E 21 (rc_pa cx) E21), ?(U_atom E 22 (rc_fr cx) E22) in HcT by lia.
  rewrite U_lit in HcT by lia. apply Z.eqb_eq in HcT.
  assert (HARGS : rp_argsb cx = false)
  by (unfold rp_argsb, reply_args; rewrite HcT, Z.eqb_refl; cbn [negb];
      rewrite ?Bool.andb_false_r, ?Bool.andb_false_l; reflexivity).
  paj_run_to_tok RUNTO HS HJ SHOK (0, 0) (AF_reac_ctrl_identity_reply + 0x294).
  { intros a (r & Hin & Hr); exfalso; cbn [In] in Hin;
    destruct Hin as [Heq | []]; subst r;
    cbv [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; lia. }
  lazymatch goal with
  | HFx : frame_of _ _ _ (ms_mem ?msn) |- _ =>
    assert (HMEM : ms_mem msn = mem3)
    by (apply FunctionalExtensionality.functional_extensionality; intros x;
        first [rewrite <- (HMcur x) | idtac]; apply HFx;
        intros (r & Hin & Hr); cbn [In] in Hin;
        destruct Hin as [Heq | []]; subst r;
        cbv [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; lia)
  end.
  rewrite HMEM in HJ.
  assert (HRET : rp_ret cx = -1)
  by (unfold rp_ret, reply_ret; change (reply_args (rc_fr cx) (rc_pa cx) (rc_pp cx) (rc_pn cx))
      with (rp_argsb cx); rewrite HARGS; reflexivity).
  assert (HOKB : rp_okb cx = false)
  by (unfold rp_okb, reply_ok; change (reply_args (rc_fr cx) (rc_pa cx) (rc_pp cx) (rc_pn cx))
      with (rp_argsb cx); rewrite HARGS; reflexivity).
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (10%bv : bv 5) P10.
  prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19. prreg HS (20%bv : bv 5) P20.
  prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23.
  prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26. prreg HS (27%bv : bv 5) P27.
  lazymatch goal with
  | |- SRr _ _ (mkCfg (mkst ?r ?p ?m ?rom) ?md) _ =>
    replace p with (w64 (rp_pc 0x294)) by
    (unfold w64, rp_pc, A_reac_ctrl_identity_replyP, AF_reac_ctrl_identity_reply; f_equal; lia)
  end.
  lazymatch goal with
  | |- SRr _ _ (mkCfg (mkst ?r ?p ?m ?rom) ?md) _ =>
    apply (K12 cx pos r (rc_lyc cx) S3 (rc_W cx) m md HBASE)
  end.
  rewrite HMEM.
  split; [split; [exact HJ | split; [exact HLY | split; [exact HFRS | split; [exact HNIN |
    split; [exact HAB | exact HCNT]]]]]|].
  split.
  { split; [repeat split; [rewrite P2; exact E2 | rewrite P3; exact E3 | rewrite P4; exact E4
    | rewrite P8; exact E8 | rewrite P9; exact E9 | rewrite P19; exact E19 | rewrite P20; exact E20
    | rewrite P21; exact E21 | rewrite P22; exact E22 | rewrite P23; exact E23
    | rewrite P27; exact E27]|].
    split; [apply rp_R34_kept_any; exact HKEPT|].
    split; [exact HSAVED|]. split; [exact HMSG|]. split; [exact HOUT | exact HROD]. }
  split; [split; [rewrite P18; exact E18 | split; [rewrite P26; exact E26 | rewrite P25; exact E25]]|].
  split; [exact HFPRES|].
  split; [exact HFW|].
  split; [exact HSG|].
  split; [rewrite P10, E10, HRET; reflexivity|].
  intros Hx. rewrite HOKB in Hx. discriminate. }
paj_run_tok RUN HS HJ SHOK (0, 0).
{ intros a (r & Hin & Hr); exfalso; cbn [In] in Hin;
  destruct Hin as [Heq | []]; subst r;
  cbv [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; lia. }
lazymatch goal with
| HFx : frame_of _ _ _ (ms_mem ?msn) |- _ =>
  assert (HMnew : forall x : word, ms_mem msn x = mem3 x)
  by (intros x; first [rewrite <- (HMcur x) | idtac]; apply HFx;
      intros (r & Hin & Hr); cbn [In] in Hin;
      destruct Hin as [Heq | []]; subst r;
      cbv [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; lia)
end;
clear HMcur; rename HMnew into HMcur;
repeat match goal with Hq : frame_of _ _ _ _ |- _ => clear Hq end;
repeat match goal with Hq : mem_grows _ _ |- _ => clear Hq end.
psrr_branch_tok RUN BR HS SHOK (0, 0).
{ (* 0x840c0: pa = 0, the null arm *)
  lazymatch goal with Hx : branch_taken _ _ _ = true |- _ => rename Hx into HcT end.
  rewrite branch_eq_U in HcT.
  rewrite ?(U_atom E 19 (rc_pn cx) E19), ?(U_atom E 20 (rc_pp cx) E20),
          ?(U_atom E 21 (rc_pa cx) E21), ?(U_atom E 22 (rc_fr cx) E22) in HcT by lia.
  rewrite U_lit in HcT by lia. apply Z.eqb_eq in HcT.
  assert (HARGS : rp_argsb cx = false)
  by (unfold rp_argsb, reply_args; rewrite HcT, Z.eqb_refl; cbn [negb];
      rewrite ?Bool.andb_false_r, ?Bool.andb_false_l; reflexivity).
  paj_run_to_tok RUNTO HS HJ SHOK (0, 0) (AF_reac_ctrl_identity_reply + 0x294).
  { intros a (r & Hin & Hr); exfalso; cbn [In] in Hin;
    destruct Hin as [Heq | []]; subst r;
    cbv [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; lia. }
  lazymatch goal with
  | HFx : frame_of _ _ _ (ms_mem ?msn) |- _ =>
    assert (HMEM : ms_mem msn = mem3)
    by (apply FunctionalExtensionality.functional_extensionality; intros x;
        first [rewrite <- (HMcur x) | idtac]; apply HFx;
        intros (r & Hin & Hr); cbn [In] in Hin;
        destruct Hin as [Heq | []]; subst r;
        cbv [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; lia)
  end.
  rewrite HMEM in HJ.
  assert (HRET : rp_ret cx = -1)
  by (unfold rp_ret, reply_ret; change (reply_args (rc_fr cx) (rc_pa cx) (rc_pp cx) (rc_pn cx))
      with (rp_argsb cx); rewrite HARGS; reflexivity).
  assert (HOKB : rp_okb cx = false)
  by (unfold rp_okb, reply_ok; change (reply_args (rc_fr cx) (rc_pa cx) (rc_pp cx) (rc_pn cx))
      with (rp_argsb cx); rewrite HARGS; reflexivity).
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (10%bv : bv 5) P10.
  prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19. prreg HS (20%bv : bv 5) P20.
  prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23.
  prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26. prreg HS (27%bv : bv 5) P27.
  lazymatch goal with
  | |- SRr _ _ (mkCfg (mkst ?r ?p ?m ?rom) ?md) _ =>
    replace p with (w64 (rp_pc 0x294)) by
    (unfold w64, rp_pc, A_reac_ctrl_identity_replyP, AF_reac_ctrl_identity_reply; f_equal; lia)
  end.
  lazymatch goal with
  | |- SRr _ _ (mkCfg (mkst ?r ?p ?m ?rom) ?md) _ =>
    apply (K12 cx pos r (rc_lyc cx) S3 (rc_W cx) m md HBASE)
  end.
  rewrite HMEM.
  split; [split; [exact HJ | split; [exact HLY | split; [exact HFRS | split; [exact HNIN |
    split; [exact HAB | exact HCNT]]]]]|].
  split.
  { split; [repeat split; [rewrite P2; exact E2 | rewrite P3; exact E3 | rewrite P4; exact E4
    | rewrite P8; exact E8 | rewrite P9; exact E9 | rewrite P19; exact E19 | rewrite P20; exact E20
    | rewrite P21; exact E21 | rewrite P22; exact E22 | rewrite P23; exact E23
    | rewrite P27; exact E27]|].
    split; [apply rp_R34_kept_any; exact HKEPT|].
    split; [exact HSAVED|]. split; [exact HMSG|]. split; [exact HOUT | exact HROD]. }
  split; [split; [rewrite P18; exact E18 | split; [rewrite P26; exact E26 | rewrite P25; exact E25]]|].
  split; [exact HFPRES|].
  split; [exact HFW|].
  split; [exact HSG|].
  split; [rewrite P10, E10, HRET; reflexivity|].
  intros Hx. rewrite HOKB in Hx. discriminate. }
paj_run_tok RUN HS HJ SHOK (0, 0).
{ intros a (r & Hin & Hr); exfalso; cbn [In] in Hin;
  destruct Hin as [Heq | []]; subst r;
  cbv [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; lia. }
lazymatch goal with
| HFx : frame_of _ _ _ (ms_mem ?msn) |- _ =>
  assert (HMnew : forall x : word, ms_mem msn x = mem3 x)
  by (intros x; first [rewrite <- (HMcur x) | idtac]; apply HFx;
      intros (r & Hin & Hr); cbn [In] in Hin;
      destruct Hin as [Heq | []]; subst r;
      cbv [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; lia)
end;
clear HMcur; rename HMnew into HMcur;
repeat match goal with Hq : frame_of _ _ _ _ |- _ => clear Hq end;
repeat match goal with Hq : mem_grows _ _ |- _ => clear Hq end.
psrr_branch_tok RUN BR HS SHOK (0, 0).
{ (* 0x840c4: pp = 0, the null arm *)
  lazymatch goal with Hx : branch_taken _ _ _ = true |- _ => rename Hx into HcT end.
  rewrite branch_eq_U in HcT.
  rewrite ?(U_atom E 19 (rc_pn cx) E19), ?(U_atom E 20 (rc_pp cx) E20),
          ?(U_atom E 21 (rc_pa cx) E21), ?(U_atom E 22 (rc_fr cx) E22) in HcT by lia.
  rewrite U_lit in HcT by lia. apply Z.eqb_eq in HcT.
  assert (HARGS : rp_argsb cx = false)
  by (unfold rp_argsb, reply_args; rewrite HcT, Z.eqb_refl; cbn [negb];
      rewrite ?Bool.andb_false_r, ?Bool.andb_false_l; reflexivity).
  paj_run_to_tok RUNTO HS HJ SHOK (0, 0) (AF_reac_ctrl_identity_reply + 0x294).
  { intros a (r & Hin & Hr); exfalso; cbn [In] in Hin;
    destruct Hin as [Heq | []]; subst r;
    cbv [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; lia. }
  lazymatch goal with
  | HFx : frame_of _ _ _ (ms_mem ?msn) |- _ =>
    assert (HMEM : ms_mem msn = mem3)
    by (apply FunctionalExtensionality.functional_extensionality; intros x;
        first [rewrite <- (HMcur x) | idtac]; apply HFx;
        intros (r & Hin & Hr); cbn [In] in Hin;
        destruct Hin as [Heq | []]; subst r;
        cbv [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; lia)
  end.
  rewrite HMEM in HJ.
  assert (HRET : rp_ret cx = -1)
  by (unfold rp_ret, reply_ret; change (reply_args (rc_fr cx) (rc_pa cx) (rc_pp cx) (rc_pn cx))
      with (rp_argsb cx); rewrite HARGS; reflexivity).
  assert (HOKB : rp_okb cx = false)
  by (unfold rp_okb, reply_ok; change (reply_args (rc_fr cx) (rc_pa cx) (rc_pp cx) (rc_pn cx))
      with (rp_argsb cx); rewrite HARGS; reflexivity).
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (10%bv : bv 5) P10.
  prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19. prreg HS (20%bv : bv 5) P20.
  prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23.
  prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26. prreg HS (27%bv : bv 5) P27.
  lazymatch goal with
  | |- SRr _ _ (mkCfg (mkst ?r ?p ?m ?rom) ?md) _ =>
    replace p with (w64 (rp_pc 0x294)) by
    (unfold w64, rp_pc, A_reac_ctrl_identity_replyP, AF_reac_ctrl_identity_reply; f_equal; lia)
  end.
  lazymatch goal with
  | |- SRr _ _ (mkCfg (mkst ?r ?p ?m ?rom) ?md) _ =>
    apply (K12 cx pos r (rc_lyc cx) S3 (rc_W cx) m md HBASE)
  end.
  rewrite HMEM.
  split; [split; [exact HJ | split; [exact HLY | split; [exact HFRS | split; [exact HNIN |
    split; [exact HAB | exact HCNT]]]]]|].
  split.
  { split; [repeat split; [rewrite P2; exact E2 | rewrite P3; exact E3 | rewrite P4; exact E4
    | rewrite P8; exact E8 | rewrite P9; exact E9 | rewrite P19; exact E19 | rewrite P20; exact E20
    | rewrite P21; exact E21 | rewrite P22; exact E22 | rewrite P23; exact E23
    | rewrite P27; exact E27]|].
    split; [apply rp_R34_kept_any; exact HKEPT|].
    split; [exact HSAVED|]. split; [exact HMSG|]. split; [exact HOUT | exact HROD]. }
  split; [split; [rewrite P18; exact E18 | split; [rewrite P26; exact E26 | rewrite P25; exact E25]]|].
  split; [exact HFPRES|].
  split; [exact HFW|].
  split; [exact HSG|].
  split; [rewrite P10, E10, HRET; reflexivity|].
  intros Hx. rewrite HOKB in Hx. discriminate. }
paj_run_tok RUN HS HJ SHOK (0, 0).
{ intros a (r & Hin & Hr); exfalso; cbn [In] in Hin;
  destruct Hin as [Heq | []]; subst r;
  cbv [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; lia. }
lazymatch goal with
| HFx : frame_of _ _ _ (ms_mem ?msn) |- _ =>
  assert (HMnew : forall x : word, ms_mem msn x = mem3 x)
  by (intros x; first [rewrite <- (HMcur x) | idtac]; apply HFx;
      intros (r & Hin & Hr); cbn [In] in Hin;
      destruct Hin as [Heq | []]; subst r;
      cbv [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; lia)
end;
clear HMcur; rename HMnew into HMcur;
repeat match goal with Hq : frame_of _ _ _ _ |- _ => clear Hq end;
repeat match goal with Hq : mem_grows _ _ |- _ => clear Hq end.
psrr_branch_tok RUN BR HS SHOK (0, 0).
{ (* 0x840c8: pn = 0, the null arm *)
  lazymatch goal with Hx : branch_taken _ _ _ = true |- _ => rename Hx into HcT end.
  rewrite branch_eq_U in HcT.
  rewrite ?(U_atom E 19 (rc_pn cx) E19), ?(U_atom E 20 (rc_pp cx) E20),
          ?(U_atom E 21 (rc_pa cx) E21), ?(U_atom E 22 (rc_fr cx) E22) in HcT by lia.
  rewrite U_lit in HcT by lia. apply Z.eqb_eq in HcT.
  assert (HARGS : rp_argsb cx = false)
  by (unfold rp_argsb, reply_args; rewrite HcT, Z.eqb_refl; cbn [negb];
      rewrite ?Bool.andb_false_r, ?Bool.andb_false_l; reflexivity).
  paj_run_to_tok RUNTO HS HJ SHOK (0, 0) (AF_reac_ctrl_identity_reply + 0x294).
  { intros a (r & Hin & Hr); exfalso; cbn [In] in Hin;
    destruct Hin as [Heq | []]; subst r;
    cbv [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; lia. }
  lazymatch goal with
  | HFx : frame_of _ _ _ (ms_mem ?msn) |- _ =>
    assert (HMEM : ms_mem msn = mem3)
    by (apply FunctionalExtensionality.functional_extensionality; intros x;
        first [rewrite <- (HMcur x) | idtac]; apply HFx;
        intros (r & Hin & Hr); cbn [In] in Hin;
        destruct Hin as [Heq | []]; subst r;
        cbv [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; lia)
  end.
  rewrite HMEM in HJ.
  assert (HRET : rp_ret cx = -1)
  by (unfold rp_ret, reply_ret; change (reply_args (rc_fr cx) (rc_pa cx) (rc_pp cx) (rc_pn cx))
      with (rp_argsb cx); rewrite HARGS; reflexivity).
  assert (HOKB : rp_okb cx = false)
  by (unfold rp_okb, reply_ok; change (reply_args (rc_fr cx) (rc_pa cx) (rc_pp cx) (rc_pn cx))
      with (rp_argsb cx); rewrite HARGS; reflexivity).
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (10%bv : bv 5) P10.
  prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19. prreg HS (20%bv : bv 5) P20.
  prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23.
  prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26. prreg HS (27%bv : bv 5) P27.
  lazymatch goal with
  | |- SRr _ _ (mkCfg (mkst ?r ?p ?m ?rom) ?md) _ =>
    replace p with (w64 (rp_pc 0x294)) by
    (unfold w64, rp_pc, A_reac_ctrl_identity_replyP, AF_reac_ctrl_identity_reply; f_equal; lia)
  end.
  lazymatch goal with
  | |- SRr _ _ (mkCfg (mkst ?r ?p ?m ?rom) ?md) _ =>
    apply (K12 cx pos r (rc_lyc cx) S3 (rc_W cx) m md HBASE)
  end.
  rewrite HMEM.
  split; [split; [exact HJ | split; [exact HLY | split; [exact HFRS | split; [exact HNIN |
    split; [exact HAB | exact HCNT]]]]]|].
  split.
  { split; [repeat split; [rewrite P2; exact E2 | rewrite P3; exact E3 | rewrite P4; exact E4
    | rewrite P8; exact E8 | rewrite P9; exact E9 | rewrite P19; exact E19 | rewrite P20; exact E20
    | rewrite P21; exact E21 | rewrite P22; exact E22 | rewrite P23; exact E23
    | rewrite P27; exact E27]|].
    split; [apply rp_R34_kept_any; exact HKEPT|].
    split; [exact HSAVED|]. split; [exact HMSG|]. split; [exact HOUT | exact HROD]. }
  split; [split; [rewrite P18; exact E18 | split; [rewrite P26; exact E26 | rewrite P25; exact E25]]|].
  split; [exact HFPRES|].
  split; [exact HFW|].
  split; [exact HSG|].
  split; [rewrite P10, E10, HRET; reflexivity|].
  intros Hx. rewrite HOKB in Hx. discriminate. }
(* the memory is still the C4 memory: nothing has been written yet. *)
assert (HMEMf : forall (ms : machine_state), (forall x : word, ms_mem ms x = mem3 x) -> ms_mem ms = mem3)
by (intros msq Hq; apply FunctionalExtensionality.functional_extensionality; exact Hq).
assert (HMEMq : forall m : word -> option byte, (forall x : word, m x = mem3 x) -> m = mem3)
by (intros mq Hq; apply FunctionalExtensionality.functional_extensionality; exact Hq).
(* 0x840cc..0x840e4 write SG[4..8]: open the shadow region's write window. *)
lazymatch goal with
| HSx : st_ok_pi _ _ _ ?ssx (restrict _ ?msn) |- _ =>
  pose proof (HMEMf msn HMcur) as HMm;
  pose proof (ast_ok_pi_set_region E ssx (restrict (w_H (rc_W cx)) msn) 0%nat
    (YP09.mkRegion (Some 25%nat) 0 16 0 0 (@nil YP09.chunk))
    (YP09.mkRegion (Some 25%nat) 0 16 4 9 (@nil YP09.chunk)) HSx
    ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
    ltac:(unfold region_ok;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ms_mem restrict];
          rewrite B25, HMm; split; [lia|];
          split; [change (2 ^ 64) with 18446744073709551616; lia|];
          split; [intros o Ho; apply (apresent_writable SEGS); exact (proj1 (HFSpr o ltac:(lia)))
                 | apply Forall_nil])) as HS3
end.
clear HS. rename HS3 into HS.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts list_upd] in HS.
paj_run_to_tok RUNTO HS HJ SHOK (0, 0) AF_reac_ctrl_parse.
{ (* the five shadow bytes are inside this function's own class-1 frame's shadow *)
  lazymatch goal with
  | |- awr_ok ?Ex ?rs ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' a1 a2 a3 a4 a5 a6 a7)
  end.
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 25%nat SA);
  [ reflexivity
  | rewrite E25; apply unsigned_lit_small; lia
  | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; right; right;
    exists 1, pos; split; [unfold rp_own1; left; reflexivity|];
    right; rewrite EG; unfold in_zr; cbn [fst snd];
    change (fs_frame_bytes 1 / 8) with 16; fold SA; lia
  | apply awr_ok_nil ]. }
(* the memory before the five stores was still the C4 memory *)
lazymatch goal with
| HFx : frame_of _ _ (mrestrict _ ?mp) (mrestrict _ _) |- _ =>
  rewrite (HMEMq mp HMcur) in HFx
end.
(* nothing outside the five shadow bytes [SA+4, SA+9) changed *)
lazymatch goal with
| HFx : frame_of _ _ (mrestrict _ mem3) (mrestrict _ (ms_mem ?msn)) |- _ =>
  assert (HUP : forall a, 0 <= a < 2 ^ 64 -> ~ (SA + 4 <= a < SA + 9) ->
    aview SEGS (w_H (rc_W cx)) (ms_mem msn) a = aview SEGS (w_H (rc_W cx)) mem3 a)
  by (intros a Ha Hn; apply aview_eq_of; apply HFx;
      rewrite unsigned_lit_small by lia;
      intros (r & Hin & Hr); cbn [In] in Hin;
      destruct Hin as [Heq | []]; subst r;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; rewrite B25 in Hr; lia)
end.
lazymatch goal with
| HGx : mem_grows (mrestrict _ ?mp0) (mrestrict _ (ms_mem ?msn)) |- _ =>
  rewrite (HMEMq mp0 HMcur) in HGx; pose proof HGx as HGROW;
  assert (HPRES : forall a, apresent (w_H (rc_W cx)) mem3 a ->
    apresent (w_H (rc_W cx)) (ms_mem msn) a)
  by (intros a Hap; exact (apresent_grows _ _ _ a HGx Hap))
end.
(* application memory never meets this frame's 16 shadow bytes *)
assert (HNSH : forall p n a, in_app p n -> p <= a < p + n -> ~ (SA <= a < SA + 16)).
{ intros p n a Hin Hpa Hsh.
  apply (fshadow_not_app G 16 p n a); [lia | lia | exact Hin | rewrite ESA in Hsh; unfold SHADOW_OFF in Hsh; lia | exact Hpa]. }
(* the four pointers are non-null on this arm *)
repeat match goal with
| Hx : branch_taken _ _ _ = false |- _ =>
  rewrite branch_eq_U in Hx;
  rewrite ?(U_atom E 19 (rc_pn cx) E19), ?(U_atom E 20 (rc_pp cx) E20),
          ?(U_atom E 21 (rc_pa cx) E21), ?(U_atom E 22 (rc_fr cx) E22) in Hx by lia;
  rewrite U_lit in Hx by lia; apply Z.eqb_neq in Hx
end.
assert (HARGST : rp_argsb cx = true).
{ unfold rp_argsb, reply_args.
  repeat match goal with Hx : ?v <> 0 |- _ => rewrite (proj2 (Z.eqb_neq v 0) Hx) end.
  reflexivity. }
assert (HGq : G = 32 * (G / 32)) by (pose proof (Z.div_mod G 32 ltac:(lia)); lia).
assert (HG8z : G mod 8 = 0)
by (rewrite HGq; replace (32 * (G / 32)) with (4 * (G / 32) * 8) by lia; apply Z_mod_mult).
destruct (al_flag _ _ LAWS _ _ _ _ _ 1 pos HAR Hfin) as (HFLp & HFLo & HFLin & HFLce).
assert (HFLr : 0 <= rp_FL cx pos < 2 ^ 64)
by (unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFLin; unfold rp_FL; lia).
lazymatch type of HUP with
| forall a, _ -> _ -> aview _ _ ?M a = _ =>
  assert (HMV : forall a (n : nat) v, G <= a -> a + Z.of_nat n <= G + 128 ->
    val_mem SEGS (mrestrict (w_H (rc_W cx)) mem3) a n v ->
    val_mem SEGS (mrestrict (w_H (rc_W cx)) M) a n v)
  by (intros a n v Hlo Hhi Hv;
      apply (val_mem_moved SEGS (w_H (rc_W cx)) (w_H (rc_W cx)) mem3 M a a n v); [|exact Hv];
      intros k Hk; apply HUP; [lia|];
      intros Hw; exact (HNSH G 128 (a + k) HFapp ltac:(lia) ltac:(lia)));
  assert (HMVany : forall a (n : nat) v, 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
    (forall k, 0 <= k < Z.of_nat n -> ~ (SA + 4 <= a + k < SA + 9)) ->
    val_mem SEGS (mrestrict (w_H (rc_W cx)) mem3) a n v ->
    val_mem SEGS (mrestrict (w_H (rc_W cx)) M) a n v)
  by (intros a n v Hlo Hhi Hout Hv;
      apply (val_mem_moved SEGS (w_H (rc_W cx)) (w_H (rc_W cx)) mem3 M a a n v); [|exact Hv];
      intros k Hk; apply HUP; [lia | exact (Hout k Hk)])
end.
(* the entry sp is far above the shadow *)
assert (HSTK : astk_ok (rc_STK cx) (rc_ly cx) (rc_sp0 cx))
by (pose proof HJ as HJc;
    destruct HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hs & _ & _); exact Hs).
destruct HSTK as (Jsp16 & JSTK0 & Jclo & Jlosp & Jsphi & Jhi47 & Jbot & Jtop1 & Jtop2).
pose proof alloc_ceiling_val as HACv.
pose proof rp_stk as (Tstk & Pstk).
assert (HSlo : 0x7fff7f800000 <= rp_S cx) by lia.
(* the shadow byte of an application address outside this frame is outside the five written bytes *)
assert (HSHOUT : forall y, 0 <= y -> (y < G \/ G + 128 <= y) ->
  ~ (SA + 4 <= shadow_of_addr SHADOW_OFF y < SA + 9)).
{ intros y Hy0 Hcase Hsh. unfold shadow_of_addr in Hsh. rewrite ESA in Hsh. unfold SHADOW_OFF in Hsh.
  pose proof (Z.div_mod G 8 ltac:(lia)) as HDG.
  destruct Hcase as [Hlt | Hge].
  - assert (y / 8 <= (G - 1) / 8) by (apply Z.div_le_mono; lia).
    assert ((G - 1) / 8 = G / 8 - 1)
    by (pose proof (Z.div_mod (G - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (G - 1) 8 ltac:(lia)); lia). lia.
  - assert ((G + 128) / 8 <= y / 8) by (apply Z.div_le_mono; lia).
    assert ((G + 128) / 8 = G / 8 + 16)
    by (pose proof (Z.div_mod (G + 128) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (G + 128) 8 ltac:(lia)); lia). lia. }
(* read the five written shadow bytes back off the region's chunks *)
lazymatch type of HS with
| st_ok _ _ ?ssx ?msr =>
  pose proof (st_ok_region_nth E ssx msr 0%nat
    (YP09.mkRegion (Some 25%nat) 0 16 4 9
      [YP09.mkChunk 8 (CVal 1 (SLit 4)); YP09.mkChunk 7 (CVal 1 (SLit 0));
       YP09.mkChunk 6 (CVal 1 (SLit 0)); YP09.mkChunk 5 (CVal 1 (SLit 0));
       YP09.mkChunk 4 (CVal 1 (SLit 0))]) HS ltac:(vm_compute; reflexivity)) as HRSH
end.
cbn [ms_mem restrict mkst] in HRSH.
lazymatch type of HUP with
| forall a, _ -> _ -> aview _ _ ?M a = _ =>
  assert (AVC : forall od v, In (YP09.mkChunk od (CVal 1 (SLit v)))
    [YP09.mkChunk 8 (CVal 1 (SLit 4)); YP09.mkChunk 7 (CVal 1 (SLit 0));
     YP09.mkChunk 6 (CVal 1 (SLit 0)); YP09.mkChunk 5 (CVal 1 (SLit 0));
     YP09.mkChunk 4 (CVal 1 (SLit 0))] -> 0 <= v < 256 ->
    aview SEGS (w_H (rc_W cx)) M (SA + od) = Some v)
  by (intros od v Hin Hv;
      apply (aview_of_val_mem1 SEGS (w_H (rc_W cx)) M (SA + od) v); [|lia];
      exact (field_of_region E _ 25%nat SA _ 0 16 4 9 od 1%N (SLit v) v HRSH
        ltac:(rewrite E25; apply unsigned_lit_small; lia) Hin
        ltac:(cbn [sv_denot]; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)))
end.
lazymatch type of HUP with
| forall a, _ -> _ -> aview _ _ ?M a = _ =>
  assert (HVIS : forall a, 0 <= a < 2 ^ 64 ->
    aview SEGS (w_H (rc_W cx)) mem3 a <> None -> aview SEGS (w_H (rc_W cx)) M a <> None)
  by (intros a Ha Hne;
      destruct (Z_le_dec (SA + 4) a) as [Hl|Hl];
      [ destruct (Z_lt_dec a (SA + 9)) as [Hr|Hr];
        [ assert (HC5 : a = SA + 4 \/ a = SA + 5 \/ a = SA + 6 \/ a = SA + 7 \/ a = SA + 8) by lia;
          destruct HC5 as [HC|[HC|[HC|[HC|HC]]]]; rewrite HC;
          [ rewrite (AVC 4 0 ltac:(cbn [In]; right; right; right; right; left; reflexivity) ltac:(lia))
          | rewrite (AVC 5 0 ltac:(cbn [In]; right; right; right; left; reflexivity) ltac:(lia))
          | rewrite (AVC 6 0 ltac:(cbn [In]; right; right; left; reflexivity) ltac:(lia))
          | rewrite (AVC 7 0 ltac:(cbn [In]; right; left; reflexivity) ltac:(lia))
          | rewrite (AVC 8 4 ltac:(cbn [In]; left; reflexivity) ltac:(lia)) ]; discriminate
        | rewrite (HUP a Ha ltac:(lia)); exact Hne ]
      | rewrite (HUP a Ha ltac:(lia)); exact Hne ])
end.
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3.
prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20.
prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23.
prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26.
prreg HS (27%bv : bv 5) Q27.
lazymatch goal with
| |- SRr _ _ (mkCfg (mkst ?r ?pq ?m ?rom) ?md) _ =>
  replace pq with (w64 C_reac_ctrl_parse.A_reac_ctrl_parseP) by (vm_compute; reflexivity)
end.
lazymatch goal with
| |- SRr _ _ (mkCfg (mkst ?r ?pq ?m ?rom) ?md) _ =>
  apply (K5 cx pos r (rc_lyc cx) S3 (rc_W cx) m md HBASE)
end.
split; [split; [exact HJ | split; [exact HLY | split; [exact HFRS | split; [exact HNIN |
  split; [exact HAB | exact HCNT]]]]]|].
split; [reflexivity|]. split; [reflexivity|].
split.
{ split; [repeat split; [rewrite Q2; exact E2 | rewrite Q3; exact E3 | rewrite Q4; exact E4
  | rewrite Q8; exact E8 | rewrite Q9; exact E9 | rewrite Q19; exact E19 | rewrite Q20; exact E20
  | rewrite Q21; exact E21 | rewrite Q22; exact E22 | rewrite Q23; exact E23
  | rewrite Q27; exact E27]|].
  split.
  { destruct HKEPT as (Hwle & KA1 & KA2 & KA3 & KA4 & KA5 & KA6).
    split; [exact Hwle|].
    split.
    { intros a Ha1 Ha2 _. etransitivity; [apply (HUP a ltac:(lia) ltac:(lia))|].
      exact (KA1 a Ha1 Ha2 (fun Hx : False => Hx)). }
    split.
    { intros b m i Hin Hi _.
      assert (Hin3 : In (b, m) (ablocks B (rc_lyc cx) S3)) by (rewrite HAB; exact Hin).
      destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hin3) as (Hq16 & Hq4096 & Hqceil & Hqia & _ & _).
      etransitivity; [apply (HUP (b + i) ltac:(lia)
        ltac:(intros Hw; exact (HNSH b (req_size m) (b + i) Hqia ltac:(lia) ltac:(lia))))|].
      exact (KA2 b m i Hin Hi (fun Hx : False => Hx)). }
    split.
    { intros a Himg Hown Herr. pose proof (pa_img_range a Himg) as HIR.
      etransitivity; [apply (HUP a ltac:(lia) ltac:(lia))|]. exact (KA3 a Himg Hown Herr). }
    split.
    { intros cid ps a Hin Hzr _.
      assert (Hin3 : In (cid, ps) (frames S3)) by (rewrite HFRS; right; exact Hin).
      destruct (al_frames _ _ LAWS _ _ _ _ _ cid ps HAR Hin3) as (Hf32 & Hfapp & _ & _).
      destruct (frame_al64 SEGS B _ _ _ _ _ cid ps HAR Hin3) as (Hf64 & Hfs64 & Hfs0).
      destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid ps HAR Hin3) as (Hfb1 & Hfb2 & _).
      destruct (in_split _ _ Hin) as (l2 & l3 & El).
      pose proof (sep_frames_pos SEGS B LAWS _ _ _ _ _ (1, pos) (cid, ps) [] l2 l3 HAR
        ltac:(rewrite HFRS, El; reflexivity)) as HDF.
      unfold zdisjoint, frame_rng in HDF. cbn [fst snd] in HDF. rewrite EG in HDF.
      change (fs_frame_bytes 1) with 128 in HDF.
      assert (HAout : ~ (SA + 4 <= a < SA + 9)).
      { unfold in_zr, frame_rng in Hzr. cbn [fst snd] in Hzr.
        destruct Hzr as [Hr1 | Hr2].
        - intros Hw.
          exact (HNSH (frame_addr (rc_lyc cx) cid ps) (fs_frame_bytes cid) a Hfapp ltac:(lia) ltac:(lia)).
        - pose proof (Z.div_mod (frame_addr (rc_lyc cx) cid ps) 8 ltac:(lia)) as DF8.
          pose proof (Z.mod_pos_bound (frame_addr (rc_lyc cx) cid ps) 8 ltac:(lia)) as DFm.
          pose proof (Z.div_mod (frame_addr (rc_lyc cx) cid ps) 64 ltac:(lia)) as DF64.
          pose proof (Z.div_mod (fs_frame_bytes cid) 8 ltac:(lia)) as DS8.
          pose proof (Z.mod_pos_bound (fs_frame_bytes cid) 8 ltac:(lia)) as DSm.
          pose proof (Z.div_mod (fs_frame_bytes cid) 64 ltac:(lia)) as DS64.
          pose proof (Z.div_mod G 8 ltac:(lia)) as DG8.
          revert Hr2. unfold shadow_addr. rewrite ESA. unfold SHADOW_OFF.
          intros Hr2 Hw. destruct HDF as [Hd|Hd]; lia. }
      etransitivity; [apply (HUP a ltac:(unfold in_zr, frame_rng in Hzr; cbn [fst snd] in Hzr;
        unfold shadow_addr in Hzr; pose proof (Z.div_mod (frame_addr (rc_lyc cx) cid ps) 8 ltac:(lia));
        pose proof (Z.mod_pos_bound (frame_addr (rc_lyc cx) cid ps) 8 ltac:(lia));
        pose proof (Z.div_mod (fs_frame_bytes cid) 8 ltac:(lia));
        pose proof (Z.mod_pos_bound (fs_frame_bytes cid) 8 ltac:(lia));
        unfold SHADOW_OFF in *; change (2 ^ 64) with 18446744073709551616;
        destruct Hzr as [Hr1|Hr2]; lia) HAout)|].
      exact (KA4 cid ps a Hin Hzr (fun Hx : False => Hx)). }
    split; [intros a Ha1 Ha2 Hp; apply HPRES; exact (KA5 a Ha1 Ha2 Hp)
           | intros a Ha; apply HPRES; exact (KA6 a Ha)]. }
  split.
  { unfold rp_saved in HSAVED |- *. rewrite Forall_forall in HSAVED |- *.
    intros [o r] Hin. cbn [fst snd].
    assert (Ho : 8 <= o <= 104).
    { cbv [rp_saves] in Hin. cbn [In] in Hin.
      repeat (destruct Hin as [Heq | Hin]; [inversion Heq; lia|]). destruct Hin. }
    apply (HMVany (rp_S cx - o) 8%nat); [lia | lia | intros kk Hk; lia|].
    exact (HSAVED (o, r) Hin). }
  split.
  { unfold rp_msg in HMSG |- *. intros Hargs Hlen.
    destruct (HMSG Hargs Hlen) as [HGA HSRC].
    destruct (Hmsg0 Hargs Hlen) as ((nb & Hinb & Hreq) & _ & _).
    assert (Hinb3 : In (rc_fr cx, nb) (ablocks B (rc_lyc cx) S3)) by (rewrite HAB; exact Hinb).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ (rc_fr cx) nb HAR Hinb3)
      as (Hb16 & Hb4096 & Hbceil & Hbia & Hbpres & _).
    pose proof Hbia as Hbapp.
    pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ (rc_fr cx) nb 1 pos HAR Hinb3 Hfin) as HDJ.
    unfold zdisjoint in HDJ. cbn [fst snd] in HDJ. rewrite EG in HDJ.
    change (fs_frame_bytes 1) with 128 in HDJ.
    assert (HNW : forall a, rc_fr cx <= a < rc_fr cx + 50 -> ~ (SA + 4 <= a < SA + 9))
    by (intros a Ha Hw; exact (HNSH (rc_fr cx) (req_size nb) a Hbapp ltac:(lia) ltac:(lia))).
    assert (HNWS : forall a, rc_fr cx <= a < rc_fr cx + 50 ->
      ~ (SA + 4 <= shadow_of_addr SHADOW_OFF a < SA + 9))
    by (intros a Ha; apply HSHOUT; [lia | destruct HDJ as [Hd|Hd]; [left; lia | right; lia]]).
    pose proof HSRC as (HS1 & HS2 & HS3 & HS4 & HS5 & HS6).
    split.
    { intros j Hj. destruct (HGA j Hj) as [Hv Hr]. split; [|exact Hr].
      rewrite length_map, Hglen in Hj.
      apply (HMVany (rc_fr cx + Z.of_nat j) 1%nat); [lia | lia | |exact Hv].
      intros kk Hk. apply HNW. lia. }
    split.
    { intros a Ha. destruct (HS1 a Ha) as [Hv Hs]. split; [|exact Hs].
      apply HVIS; [lia | exact Hv]. }
    split.
    { apply (range_addressable_agree (aview SEGS (w_H (rc_W cx)) mem3)); [|exact HS2].
      intros x Hx. apply HUP; [pose proof (Z.div_mod x 8 ltac:(lia)); pose proof (Z.mod_pos_bound x 8 ltac:(lia));
       unfold shadow_of_addr, SHADOW_OFF; lia | exact (HNWS x Hx)]. }
    split; [|split; [exact HS4 | split; [exact HS5 | exact HS6]]].
    unfold shadow_hull_vis in HS3 |- *. intros sq Hsq.
    apply HVIS; [|exact (HS3 sq Hsq)].
    revert Hsq. unfold shadow_addr, SHADOW_OFF.
    pose proof (Z.div_mod (rc_fr cx) 8 ltac:(lia)) as D1.
    pose proof (Z.mod_pos_bound (rc_fr cx) 8 ltac:(lia)) as D2.
    pose proof (Z.div_mod (rc_fr cx + 50 - 1) 8 ltac:(lia)) as D3.
    pose proof (Z.mod_pos_bound (rc_fr cx + 50 - 1) 8 ltac:(lia)) as D4.
    pose proof (Z.div_mod (2147450880 + (rc_fr cx + 50 - 1) / 8) 8 ltac:(lia)) as D5.
    pose proof (Z.mod_pos_bound (2147450880 + (rc_fr cx + 50 - 1) / 8) 8 ltac:(lia)) as D6.
    pose proof (Z.div_mod (2147450880 + rc_fr cx / 8) 8 ltac:(lia)) as D7.
    pose proof (Z.mod_pos_bound (2147450880 + rc_fr cx / 8) 8 ltac:(lia)) as D8.
    intros Hsq. change (2 ^ 64) with 18446744073709551616. lia. }
  split.
  { unfold rp_out in HOUT |- *. intros Hargs.
    destruct (HOUT Hargs) as (O1 & O2 & O3 & O4).
    destruct (Hout0 Hargs) as (_ & _ & _ & _ & _ & _ & Hfr3 & _).
    assert (HOF : forall a, treply_out (rc_pa cx) (rc_pp cx) (rc_pn cx) a ->
      (a < G \/ G + 128 <= a) /\ 0 <= a < 2 ^ 64).
    { intros a Ha. destruct (Hfr3 a Ha) as (cid & ps & Hin & Hzr).
      destruct (in_split _ _ Hin) as (l2 & l3 & El).
      pose proof (sep_frames_pos SEGS B LAWS _ _ _ _ _ (1, pos) (cid, ps) [] l2 l3 HAR
        ltac:(rewrite HFRS, El; reflexivity)) as HDF.
      unfold zdisjoint, frame_rng in HDF. cbn [fst snd] in HDF. rewrite EG in HDF.
      change (fs_frame_bytes 1) with 128 in HDF.
      unfold in_zr, frame_rng in Hzr. cbn [fst snd] in Hzr.
      assert (Hin3 : In (cid, ps) (frames S3)) by (rewrite HFRS; right; exact Hin).
      destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid ps HAR Hin3) as (Hcb1 & Hcb2 & _).
      split; [destruct HDF as [Hd|Hd]; [right; lia | left; lia] | lia]. }
    lazymatch type of HUP with
    | forall a, _ -> _ -> aview _ _ ?Mq a = _ =>
      assert (HRA : forall q n, (forall a, q <= a < q + n -> treply_out (rc_pa cx) (rc_pp cx) (rc_pn cx) a) ->
        range_addressable (aview SEGS (w_H (rc_W cx)) mem3) SHADOW_OFF q n ->
        range_addressable (aview SEGS (w_H (rc_W cx)) Mq) SHADOW_OFF q n)
      by (intros q n Hq Hr; apply (range_addressable_agree (aview SEGS (w_H (rc_W cx)) mem3)); [|exact Hr];
          intros x Hx; destruct (HOF x (Hq x Hx)) as [Hcc Hbb];
          apply HUP; [pose proof (Z.div_mod x 8 ltac:(lia)); pose proof (Z.mod_pos_bound x 8 ltac:(lia));
            unfold shadow_of_addr, SHADOW_OFF; lia | apply HSHOUT; [lia | exact Hcc]])
    end.
    split; [apply HRA; [intros a Ha; left; lia | exact O1]|].
    split; [apply HRA; [intros a Ha; right; left; lia | exact O2]|].
    split; [apply HRA; [intros a Ha; right; right; lia | exact O3]|].
    intros a Ha. apply HPRES. exact (O4 a Ha). }
  unfold YE01.arodata_okS in HROD |- *.
  intros a Ha Hown Herr.
  assert (Himg : in_img SEGS a)
  by (destruct Ha as [(sg & Hin & _ & Hb) | Hr];
      [exists sg; split; [exact Hin | exact Hb] | exact (RELRO_IMG a Hr)]).
  pose proof (pa_img_range a Himg) as HIR.
  rewrite (HUP a ltac:(lia) ltac:(lia)). exact (HROD a Ha Hown Herr). }
split; [split; [rewrite Q18; exact E18 | split; [rewrite Q26; exact E26 | rewrite Q25; exact E25]]|].
split; [unfold rp_fpres; intros a Ha; apply HPRES; exact (HFPRES a Ha)|].
split.
{ destruct HFW as (FW0 & FW8 & FW16 & FW120).
  split; [apply (HMV G 8%nat); [lia | cbn [Z.of_nat]; lia | exact FW0]|].
  split; [apply (HMV (G + 8) 8%nat); [lia | cbn [Z.of_nat]; lia | exact FW8]|].
  split; [apply (HMV (G + 16) 8%nat); [lia | cbn [Z.of_nat]; lia | exact FW16]|].
  apply rdword_of_val_mem; [|exact HFLr].
  apply (HMV (G + 120) 8%nat); [lia | cbn [Z.of_nat]; lia|].
  exact (val_mem_of_rdword SEGS _ _ _ _ FW120). }
split.
{ assert (ESH : shadow_of_addr SHADOW_OFF (rp_G cx pos) = SA) by reflexivity.
  unfold rp_shadow, shadow_cells in HSG |- *.
  rewrite ESH in HSG |- *.
  intros i Hi. cbv [rp_sg_live] in Hi; cbn [length] in Hi.
  destruct i as [|i]; [rewrite (HUP (SA + Z.of_nat 0) ltac:(cbn [Z.of_nat]; lia) ltac:(cbn [Z.of_nat]; lia)); rewrite (HSG 0%nat ltac:(cbv [rp_sg_frame]; cbn [length]; lia)); cbn; reflexivity|].
  destruct i as [|i]; [rewrite (HUP (SA + Z.of_nat 1) ltac:(cbn [Z.of_nat]; lia) ltac:(cbn [Z.of_nat]; lia)); rewrite (HSG 1%nat ltac:(cbv [rp_sg_frame]; cbn [length]; lia)); cbn; reflexivity|].
  destruct i as [|i]; [rewrite (HUP (SA + Z.of_nat 2) ltac:(cbn [Z.of_nat]; lia) ltac:(cbn [Z.of_nat]; lia)); rewrite (HSG 2%nat ltac:(cbv [rp_sg_frame]; cbn [length]; lia)); cbn; reflexivity|].
  destruct i as [|i]; [rewrite (HUP (SA + Z.of_nat 3) ltac:(cbn [Z.of_nat]; lia) ltac:(cbn [Z.of_nat]; lia)); rewrite (HSG 3%nat ltac:(cbv [rp_sg_frame]; cbn [length]; lia)); cbn; reflexivity|].
  destruct i as [|i]; [rewrite (AVC (Z.of_nat 4) 0 ltac:(cbn [In]; right; right; right; right; left; reflexivity) ltac:(lia)); cbn; reflexivity|].
  destruct i as [|i]; [rewrite (AVC (Z.of_nat 5) 0 ltac:(cbn [In]; right; right; right; left; reflexivity) ltac:(lia)); cbn; reflexivity|].
  destruct i as [|i]; [rewrite (AVC (Z.of_nat 6) 0 ltac:(cbn [In]; right; right; left; reflexivity) ltac:(lia)); cbn; reflexivity|].
  destruct i as [|i]; [rewrite (AVC (Z.of_nat 7) 0 ltac:(cbn [In]; right; left; reflexivity) ltac:(lia)); cbn; reflexivity|].
  destruct i as [|i]; [rewrite (AVC (Z.of_nat 8) 4 ltac:(cbn [In]; left; reflexivity) ltac:(lia)); cbn; reflexivity|].
  destruct i as [|i]; [rewrite (HUP (SA + Z.of_nat 9) ltac:(cbn [Z.of_nat]; lia) ltac:(cbn [Z.of_nat]; lia)); rewrite (HSG 9%nat ltac:(cbv [rp_sg_frame]; cbn [length]; lia)); cbn; reflexivity|].
  destruct i as [|i]; [rewrite (HUP (SA + Z.of_nat 10) ltac:(cbn [Z.of_nat]; lia) ltac:(cbn [Z.of_nat]; lia)); rewrite (HSG 10%nat ltac:(cbv [rp_sg_frame]; cbn [length]; lia)); cbn; reflexivity|].
  destruct i as [|i]; [rewrite (HUP (SA + Z.of_nat 11) ltac:(cbn [Z.of_nat]; lia) ltac:(cbn [Z.of_nat]; lia)); rewrite (HSG 11%nat ltac:(cbv [rp_sg_frame]; cbn [length]; lia)); cbn; reflexivity|].
  destruct i as [|i]; [rewrite (HUP (SA + Z.of_nat 12) ltac:(cbn [Z.of_nat]; lia) ltac:(cbn [Z.of_nat]; lia)); rewrite (HSG 12%nat ltac:(cbv [rp_sg_frame]; cbn [length]; lia)); cbn; reflexivity|].
  destruct i as [|i]; [rewrite (HUP (SA + Z.of_nat 13) ltac:(cbn [Z.of_nat]; lia) ltac:(cbn [Z.of_nat]; lia)); rewrite (HSG 13%nat ltac:(cbv [rp_sg_frame]; cbn [length]; lia)); cbn; reflexivity|].
  destruct i as [|i]; [rewrite (HUP (SA + Z.of_nat 14) ltac:(cbn [Z.of_nat]; lia) ltac:(cbn [Z.of_nat]; lia)); rewrite (HSG 14%nat ltac:(cbv [rp_sg_frame]; cbn [length]; lia)); cbn; reflexivity|].
  destruct i as [|i]; [rewrite (HUP (SA + Z.of_nat 15) ltac:(cbn [Z.of_nat]; lia) ltac:(cbn [Z.of_nat]; lia)); rewrite (HSG 15%nat ltac:(cbv [rp_sg_frame]; cbn [length]; lia)); cbn; reflexivity|].
  exfalso. lia. }
split; [exact HARGST|].
split; [rewrite Q1; unfold w64, rp_pc, A_reac_ctrl_identity_replyP, AF_reac_ctrl_identity_reply;
  f_equal; lia|].
split; [rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity]|].
split; [rewrite Q10; exact E22|].
split; [rewrite Q11; exact E23|].
split; [rewrite Q12; cbn [sv_denot]; rewrite E26, unsigned_lit_small by lia; reflexivity|].
split; [rewrite Q24; cbn [sv_denot]; rewrite E26, unsigned_lit_small by lia; reflexivity|].
unfold range_addressable. intros x Hx.
assert (HSH : shadow_of_addr SHADOW_OFF x = SA + (x - G) / 8)
by (replace x with (G + (x - G)) at 1 by lia;
    rewrite shadow_of_addr_aligned_off by exact HG8z; reflexivity).
assert (HDM : 8 * ((x - G) / 8) + (x - G) mod 8 = x - G /\ 0 <= (x - G) mod 8 < 8)
by (split; [pose proof (Z.div_mod (x - G) 8 ltac:(lia)); lia
           | apply Z.mod_pos_bound; lia]).
assert (HXM : x mod 8 = (x - G) mod 8)
by (pose proof (Z.div_mod G 8 ltac:(lia)) as HDG;
    replace x with ((x - G) + G / 8 * 8) at 1 by lia; rewrite Z_mod_plus_full; reflexivity).
rewrite HSH.
assert (HD : (x - G) / 8 = 4 \/ (x - G) / 8 = 5 \/ (x - G) / 8 = 6 \/ (x - G) / 8 = 7 \/ (x - G) / 8 = 8) by lia.
destruct HD as [HDq|[HDq|[HDq|[HDq|HDq]]]]; rewrite HDq.
- exists 0. split; [apply (AVC 4 0); [cbn [In]; right; right; right; right; left; reflexivity | lia] | left; reflexivity].
- exists 0. split; [apply (AVC 5 0); [cbn [In]; right; right; right; left; reflexivity | lia] | left; reflexivity].
- exists 0. split; [apply (AVC 6 0); [cbn [In]; right; right; left; reflexivity | lia] | left; reflexivity].
- exists 0. split; [apply (AVC 7 0); [cbn [In]; right; left; reflexivity | lia] | left; reflexivity].
- exists 4. split; [apply (AVC 8 4); [cbn [In]; left; reflexivity | lia] | right; split; lia].
Qed.

(* ---- rp_E2's local helpers (arithmetic and shadow geometry only; the walk kit has no equivalent:
   its land_m32 / denot_and_m32 / sp1_facts decide the `andi` INSTRUCTION, not the value `rp_rA cx`) ---- *)
(* the realigned frame base: 32 * ((S - 128) / 32) is S - 128 or S - 144 when S mod 16 = 0. *)
Lemma rp_E2_rA : forall s, s mod 16 = 0 ->
s - 144 <= 32 * ((s - 128) / 32) <= s - 128 /\ (32 * ((s - 128) / 32)) mod 32 = 0.
Proof.
intros s H16.
pose proof (Z.div_mod (s - 128) 32 ltac:(lia)) as D.
pose proof (Z.mod_pos_bound (s - 128) 32 ltac:(lia)) as R.
assert (Hs16 : (s - 128) mod 16 = 0) by (rewrite Zminus_mod, H16; reflexivity).
assert (Hr16 : (s - 128) mod 32 mod 16 = 0).
{ rewrite <- (Znumtheory.Zmod_div_mod 16 32 (s - 128) ltac:(lia) ltac:(lia) ltac:(exists 2; reflexivity)).
exact Hs16. }
pose proof (Z.div_mod ((s - 128) mod 32) 16 ltac:(lia)) as DR.
rewrite Hr16, Z.add_0_r in DR.
assert (Hq : (s - 128) mod 32 / 16 = 0 \/ (s - 128) mod 32 / 16 = 1) by lia.
split; [lia | rewrite Z.mul_comm; apply Z_mod_mult].
Qed.
(* mod 32 = 0 gives mod 8 = 0 (frame_addr is 32-aligned, al_frames). *)
Lemma rp_E2_m32_m8 : forall x, x mod 32 = 0 -> x mod 8 = 0.
Proof.
intros x H. pose proof (Z.div_mod x 32 ltac:(lia)) as D. rewrite H, Z.add_0_r in D.
rewrite D. replace (32 * (x / 32)) with ((4 * (x / 32)) * 8) by lia. apply Z_mod_mult.
Qed.
(* an app range's shadow lies in [kLowMemEnd, kHighShadowEnd), which is apart from every app address. *)
Lemma rp_E2_sh_rng : forall f bs a, 4096 <= f -> 0 <= bs -> f + bs <= alloc_ceiling ->
shadow_addr f <= a < shadow_addr f + bs / 8 -> kLowMemEnd <= a < kHighShadowEnd.
Proof.
intros f bs a Hf Hbs Hfb Ha.
pose proof (shadow_range_end f bs Hbs) as HE.
pose proof asan_consts as (CC & _).
assert (Hd : (f + bs) / 8 <= 17592184995840).
{ replace 17592184995840 with (140737479966720 / 8) by (vm_compute; reflexivity).
apply Z.div_le_mono; lia. }
assert (Hf8 : 0 <= f / 8) by (apply Z.div_pos; lia).
unfold shadow_addr, SHADOW_OFF, kLowMemEnd, kHighShadowEnd in *. lia.
Qed.
Lemma rp_E2_app_sh : forall g a, in_app g 128 -> kLowMemEnd <= a < kHighShadowEnd ->
~ (g + 32 <= a < g + 68).
Proof.
intros g a (H1 & H2) Ha.
unfold kLowMemEnd, kHighShadowEnd, kLowShadowBeg, kHighMemBeg in *.
destruct H2 as [H2 | (H2 & H3)]; lia.
Qed.
(* a byte of an 8-aligned range of 8-aligned length has its shadow byte inside the range's shadow. *)
Lemma rp_E2_shin : forall f bs a, f mod 8 = 0 -> bs mod 8 = 0 -> 0 <= f -> 0 <= bs -> f <= a < f + bs ->
shadow_addr f <= shadow_addr a < shadow_addr f + bs / 8.
Proof.
intros f bs a Hf8 Hb8 Hf Hb Ha. unfold shadow_addr.
pose proof (Z.div_mod f 8 ltac:(lia)) as Df. rewrite Hf8, Z.add_0_r in Df.
pose proof (Z.div_mod bs 8 ltac:(lia)) as Db. rewrite Hb8, Z.add_0_r in Db.
assert (H1 : f / 8 <= a / 8) by (apply Z.div_le_mono; lia).
assert (H2 : a / 8 < f / 8 + bs / 8) by (apply Z.div_lt_upper_bound; lia).
lia.
Qed.

(* E2  C5 -> C6, the call of reac_ctrl_parse (0x840f4, +0x168).
   `SRr_bind` + `PARSE` with STK/sp0/FP/ly/S/W0/mem0/md0 of cx, own := (1,pos)::own, lyc := ly3, Sc := S3,
   W := W3, memc := mem3, mdc := md3, k := rc_k cx, f := fr, n := len, o := G+32, fr-list := g. Its premises
   (the parse lane's note section 4 (a working note, not in this delivery)): P1 the journal of C5; P2 `arodata_okP` (rp_carry); P3 ra = +0x16c, `ret_ok_codeptr_v`;
   P4 gp/tp; P5 a0/a1/a2 and `0 <= len < 2^64`; (P6, the caller chain, is gone: a Theorem Labs lane dropped it 00:04Z); P7 rA mod 16 = 0 and
   sp0 - STK <= rA - REAC_CTRL_PARSE_STK (from TREPLY_STK = 144 + REAC_CTRL_PARSE_STK and rA >= S - 144);
   P8 `count_cid 1 (frames S3) < fs_frames 1` (rp_jhold); P9 / P12 / P13 the message premise of rp_base carried
   by rp_msg; P10 `afobj ... (G+32) 36` from the frame membership, G mod 32 = 0 and C5's range_addressable;
   P11 the per-byte `awr_byte` from `in_frames ((1,pos)::own)`.
   Its post gives C6: a0 = fst (ctrlparse len g), the 36 record bytes, the same k, frames and ablocks, and
   `acall_kept ... (rA - REAC_CTRL_PARSE_STK) rA (fun a => G+32 <= a < G+68)`, from which rp_carry (the saved
   words at [S-104, S) are above rA; the message block, the caller cells and their shadow are kept by its block
   and frame clauses) and rp_shadow rp_sg_live (the frame's shadow is kept: it is not in [G+32, G+68)) follow.
   cgif's model of a caller-journal callee called while a class-1 frame is held: lib/A/AC9u.v:343.
   Donors: B `rp_call` :2234, `rp_parse` :2400, `rr_JB_parse` :2142, `rk_cwin` :2014; A18 `seg_parse` :2598,
   `PRS` :2179. Difficulty: HARD (the kept transport is the bulk of it). *)
Lemma rp_E2 : rp_from_C6 -> rp_from_C5.
Proof.
intros F6 cx pos regs3 ly3 S3 W3 mem3 md3 HB H5.
pose proof HB as HB0.
unfold rp_base in HB.
destruct HB as (HBJ & HBRO & HBret & HBra & HBgp & HBtp & HBa0 & HBa1 & HBa2 & HBa3 & HBa4 &
HBfr & HBlen & HBpa & HBpp & HBpn & HB16 & HBwin & HBsp0 & HBcnt & HBg50 & HBmsg & HBcell).
unfold rp_C5 in H5.
destruct H5 as (HJ & Ely & EW & HC & HFR & HFP & HFW & HSG & HARG & Hra1 & Hretok &
Ha0 & Ha1 & Ha2 & Hs8 & HRA36).
subst ly3. subst W3.
unfold rp_jhold in HJ. destruct HJ as (HJ1 & HLY3 & Hfrs3 & Hnin & Hab3 & Hcnt3).
unfold rp_carry in HC. destruct HC as (HRG & HKP & HSAV & HMSG & HOUT & HRO).
unfold rp_kept, tcj_kept in HKP.
destruct HKP as (Hwle3 & TK1 & TK2 & TK3 & TK4 & TK5 & TK6).
pose proof (proj1 HJ1) as HAR3.
pose proof asan_consts as (CC & _).
assert (HFB1 : fs_frame_bytes 1 = 128) by (vm_compute; reflexivity).
assert (HFB18 : fs_frame_bytes 1 / 8 = 16) by (vm_compute; reflexivity).
pose proof rp_stk as (Tstk & Pstk).
assert (Hin1 : In (1, pos) (frames S3)) by (rewrite Hfrs3; left; reflexivity).
(* --- the own class-1 frame: 32-aligned, in app memory, below the ceiling --- *)
destruct (al_frames _ _ LAWS (rc_lyc cx) S3 (rc_W cx) mem3 md3 1 pos HAR3 Hin1) as (HGm32 & _ & _ & _).
assert (HGm8 : rp_G cx pos mod 8 = 0) by (apply rp_E2_m32_m8; exact HGm32).
destruct (frames_bounds SEGS B LAWS (rc_lyc cx) S3 (rc_W cx) mem3 md3 1 pos HAR3 Hin1)
as (HG0 & HGceil & HGapp).
rewrite HFB1 in HGceil, HGapp.
assert (HGdef : frame_addr (rc_lyc cx) 1 pos = rp_G cx pos) by reflexivity.
rewrite HGdef in HGm32, HG0, HGceil, HGapp.
(* --- the stack geometry: alloc_ceiling + TREPLY_STK <= S <= 2 ^ 47, and rA --- *)
pose proof HJ1 as HJc.
destruct HJc as (HAR3' & HLY1 & HSEC1 & HWLE1 & HIO1 & HFRS1 & HNEV1 & HK1 & HJa & HJb & HJc1 & HJd &
HJe & HJf & Hstk3 & HJg & HJh).
destruct Hstk3 as (Hsp016 & HSTK0 & Hceil3 & Hlo3 & Hhi3 & H47 & Hbot3 & Htop3 & Htop3').
assert (HSlo : alloc_ceiling + TREPLY_STK <= rp_S cx) by lia.
assert (HShi : rp_S cx <= 2 ^ 47) by lia.
destruct (rp_E2_rA (rp_S cx) HB16) as (HrAb & HrA32).
assert (HrAb' : rp_S cx - 144 <= rp_rA cx <= rp_S cx - 128) by exact HrAb.
assert (HrA32' : rp_rA cx mod 32 = 0) by exact HrA32.
assert (HspA : spZ regs3 = rp_rA cx).
{ unfold spZ. destruct HRG as (H2 & _). rewrite H2. unfold w64. apply unsigned_lit_small. lia. }
assert (HrA16 : rp_rA cx mod 16 = 0).
{ pose proof (Z.div_mod (rp_rA cx) 32 ltac:(lia)) as D. rewrite HrA32', Z.add_0_r in D.
rewrite D. replace (32 * (rp_rA cx / 32)) with ((2 * (rp_rA cx / 32)) * 16) by lia. apply Z_mod_mult. }
(* --- what the call may write is apart from every caller object and from the own frame's other bytes --- *)
assert (HappC : forall cid p a, In (cid, p) (frames S3) ->
shadow_addr (frame_addr (rc_lyc cx) cid p) <= a < shadow_addr (frame_addr (rc_lyc cx) cid p)
+ fs_frame_bytes cid / 8 -> ~ (rp_G cx pos + 32 <= a < rp_G cx pos + 68)).
{ intros cid p a Hin Ha.
destruct (frames_bounds SEGS B LAWS (rc_lyc cx) S3 (rc_W cx) mem3 md3 cid p HAR3 Hin) as (Hf0 & Hfc & _).
apply (rp_E2_app_sh _ _ HGapp).
exact (rp_E2_sh_rng _ _ a Hf0 (fs_frame_bytes_nonneg cid) Hfc Ha). }
assert (HdF : forall cid p a, In (cid, p) (frames (rc_Sc cx)) ->
in_zr a (frame_rng (rc_lyc cx) (cid, p)) -> ~ (rp_G cx pos + 32 <= a < rp_G cx pos + 68)).
{ intros cid p a Hin Hz.
apply in_split in Hin. destruct Hin as (l2 & l3 & Esc).
pose proof (sep_frames_pos SEGS B LAWS (rc_lyc cx) S3 (rc_W cx) mem3 md3 (1, pos) (cid, p) [] l2 l3 HAR3
ltac:(rewrite Hfrs3, Esc; reflexivity)) as Hdis.
unfold zdisjoint, frame_rng, in_zr in Hdis, Hz. cbn [fst snd] in Hdis, Hz.
rewrite HFB1 in Hdis. unfold rp_G. lia. }
assert (HdS : forall cid p a, In (cid, p) (frames (rc_Sc cx)) ->
in_zr a (shadow_addr (frame_addr (rc_lyc cx) cid p), fs_frame_bytes cid / 8) ->
~ (rp_G cx pos + 32 <= a < rp_G cx pos + 68)).
{ intros cid p a Hin Hz. unfold in_zr in Hz. cbn [fst snd] in Hz.
exact (HappC cid p a ltac:(rewrite Hfrs3; right; exact Hin) Hz). }
assert (HdB : forall b m i, In (b, m) (ablocks B (rc_lyc cx) (rc_Sc cx)) -> 0 <= i < req_size m ->
~ (rp_G cx pos + 32 <= b + i < rp_G cx pos + 68)).
{ intros b m i Hin Hi.
pose proof (sep_block_frame SEGS B LAWS (rc_lyc cx) S3 (rc_W cx) mem3 md3 b m 1 pos HAR3
ltac:(rewrite Hab3; exact Hin) Hin1) as Hdis.
unfold zdisjoint in Hdis. cbn [fst snd] in Hdis. rewrite HFB1 in Hdis. unfold rp_G. lia. }
assert (HdSG : forall a, shadow_addr (rp_G cx pos) <= a < shadow_addr (rp_G cx pos) + 16 ->
~ (rp_G cx pos + 32 <= a < rp_G cx pos + 68)).
{ intros a Ha. apply (HappC 1 pos a Hin1). rewrite HFB1. exact Ha. }
assert (HdG : forall a, rp_G cx pos <= a < rp_G cx pos + 128 ->
~ (rp_G cx pos + 32 <= a < rp_G cx pos + 68) -> rp_G cx pos <= a < rp_G cx pos + 128) by (intros; assumption).
(* --- the call --- *)
eapply SRr_bind.
{ apply (PARSE (rc_STK cx) (rc_sp0 cx) (rc_FP cx) (rc_ly cx) (rc_S cx) (rc_W0 cx) (rc_mem0 cx) (rc_md0 cx)
(rp_own1 cx pos) (rc_lyc cx) S3 (rc_W cx) mem3 md3 (rc_k cx) regs3
(rc_fr cx) (rc_len cx) (rp_G cx pos + 32) (rc_g cx)).
- (* P1 *) exact HJ1.
- (* P2 *) exact HRO.
- (* P3 *) exact Hretok.
- (* P3' *) unfold raZ. rewrite Hra1. unfold w64, rp_pc, A_reac_ctrl_identity_replyP.
pose proof (@pa_B_ok _ ctrl_listing CtrlImg.PI_ctrl) as (HBo0 & HBo1 & _).
rewrite unsigned_lit_small by (unfold AF_reac_ctrl_identity_reply; lia).
unfold AF_reac_ctrl_identity_reply. lia.
- (* P4 gp *) destruct HRG as (_ & H3 & _). exact H3.
- (* P4 tp *) destruct HRG as (_ & _ & H4 & _). exact H4.
- (* P5 a0 *) exact Ha0.
- (* P5 a1 *) exact Ha1.
- (* P5 a2 *) exact Ha2.
- (* P5 n *) exact HBlen.
- (* P7 align *) rewrite HspA. exact HrA16.
- (* P7 window *) rewrite HspA. lia.
- (* P7 top *) rewrite HspA. lia.
- (* P8 room *) exact Hcnt3.
- (* P9 block *) intros Hn. destruct (HBmsg HARG Hn) as ((nb & Hinb & Hreq) & _ & _).
exists nb. split; [rewrite Hab3; exact Hinb | exact Hreq].
- (* P10 afobj *) intros _. unfold afobj. split; [| split].
+ exists 1, pos. split; [exact Hin1 | split; [lia | split; [exact (rp_E2_m32_m8 _ HGm32) | ]]].
rewrite HFB1. unfold rp_G. lia.
+ pose proof (Z.div_mod (rp_G cx pos) 8 ltac:(lia)) as D. rewrite HGm8, Z.add_0_r in D.
rewrite D. replace (8 * (rp_G cx pos / 8) + 32) with ((rp_G cx pos / 8 + 4) * 8) by lia.
apply Z_mod_mult.
+ exact HRA36.
- (* P11 awr_byte *) intros _ a Ha. right. right. right.
exists 1, pos. split; [left; reflexivity | left]. unfold in_zr. cbn [fst snd]. rewrite HFB1.
unfold rp_G in *. lia.
- (* P12 *) exact HBg50.
- (* P13 *) intros Hn i Hi. destruct (HMSG HARG Hn) as (HG3 & _).
assert (Hlen50 : length (map bv_unsigned (rc_g cx)) = 50%nat) by (rewrite length_map; exact HBg50).
destruct (HG3 i ltac:(rewrite Hlen50; exact Hi)) as (Hv & Hr).
assert (Hnth : nth i (map bv_unsigned (rc_g cx)) 0 = cp_v (rc_g cx) i).
{ unfold cp_v, cp_b. rewrite <- (map_nth bv_unsigned (rc_g cx) cp_z i). reflexivity. }
rewrite Hnth in Hv, Hr.
exact (aview_of_val_mem1 SEGS (w_H (rc_W cx)) mem3 (rc_fr cx + Z.of_nat i) (cp_v (rc_g cx) i) Hv Hr). }
(* --- after the call --- *)
cbv beta. intros W' c' Hwle' Hpost.
unfold C_reac_ctrl_parse.treac_ctrl_parse_post in Hpost.
destruct Hpost as (ly2 & S2 & regs2 & mem2 & md2 & Ec & HJ2 & HPR & Hfrs2 & Hab2 & Hff & Ha02 & Hrec & HK).
unfold acall_kept in HK. destruct HK as (K1 & K2 & K3 & K4 & K5 & K6).
(* the call's exception set is `fun a => o <= a < o + 36` with o = G + 32 *)
assert (HE36 : forall a, ~ (rp_G cx pos + 32 <= a < rp_G cx pos + 68) ->
~ (rp_G cx pos + 32 <= a < rp_G cx pos + 32 + 36)) by (intros a Hno Hc; apply Hno; lia).
subst c'. rewrite Hra1.
pose proof (proj1 HJ2) as HAR2.
assert (Hin1' : In (1, pos) (frames S2)) by (rewrite Hfrs2; exact Hin1).
(* the layout's fixed fields *)
assert (HFeq : forall cid p, frame_addr ly2 cid p = frame_addr (rc_lyc cx) cid p).
{ intros cid p. unfold frame_addr.
destruct HJ2 as (_ & HL2 & _). destruct HL2 as (_ & _ & _ & _ & _ & HF2 & _).
destruct HLY1 as (_ & _ & _ & _ & _ & HF1 & _). rewrite HF2, HF1. reflexivity. }
assert (HLYok : rp_ly_ok cx ly2).
{ unfold rp_ly_ok.
destruct HJ2 as (_ & HL2 & _). destruct HL2 as (_ & _ & _ & _ & _ & HF2 & _ & _ & HTp2 & _).
destruct HLY1 as (_ & _ & _ & _ & _ & HF1 & _ & _ & HTp1 & _).
split; [rewrite HF2, HF1; reflexivity | rewrite HTp2, HTp1; reflexivity]. }
(* every byte outside the call's window and outside [G+32, G+68) reads as it did at C5 *)
assert (KW : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (rp_S cx - TREPLY_STK <= a < rp_S cx) ->
aview SEGS (w_H W') mem2 a = aview SEGS (w_H (rc_W cx)) mem3 a).
{ intros a Hq1 Hq2. apply K1; [exact Hq1 | rewrite HspA; lia]. }
assert (KFR : forall cid p a, In (cid, p) (frames S3) -> in_zr a (frame_rng (rc_lyc cx) (cid, p)) ->
~ (rp_G cx pos + 32 <= a < rp_G cx pos + 68) ->
aview SEGS (w_H W') mem2 a = aview SEGS (w_H (rc_W cx)) mem3 a).
{ intros cid p a Hin Hz HE. exact (K4 cid p a Hin (or_introl Hz) (HE36 a HE)). }
assert (KSH : forall cid p a, In (cid, p) (frames S3) ->
in_zr a (shadow_addr (frame_addr (rc_lyc cx) cid p), fs_frame_bytes cid / 8) ->
~ (rp_G cx pos + 32 <= a < rp_G cx pos + 68) ->
aview SEGS (w_H W') mem2 a = aview SEGS (w_H (rc_W cx)) mem3 a).
{ intros cid p a Hin Hz HE. exact (K4 cid p a Hin (or_intror Hz) (HE36 a HE)). }
(* the own frame's bytes and its 16 shadow bytes *)
assert (KG : forall a, rp_G cx pos <= a < rp_G cx pos + 128 ->
~ (rp_G cx pos + 32 <= a < rp_G cx pos + 68) ->
aview SEGS (w_H W') mem2 a = aview SEGS (w_H (rc_W cx)) mem3 a).
{ intros a Ha HE. apply (KFR 1 pos a Hin1); [| exact HE].
unfold in_zr, frame_rng. cbn [fst snd]. rewrite HFB1. unfold rp_G in *. lia. }
assert (KGS : forall a, shadow_addr (rp_G cx pos) <= a < shadow_addr (rp_G cx pos) + 16 ->
aview SEGS (w_H W') mem2 a = aview SEGS (w_H (rc_W cx)) mem3 a).
{ intros a Ha. apply (KSH 1 pos a Hin1); [| exact (HdSG a Ha)].
unfold in_zr. cbn [fst snd]. rewrite HFB18. exact Ha. }
apply (F6 cx pos regs2 ly2 S2 W' mem2 md2).
{ exact HB0. }
unfold rp_C6.
split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]]].
- (* rp_jhold *) unfold rp_jhold. split; [| split; [| split; [| split; [| split]]]].
+ exact HJ2.
+ exact HLYok.
+ rewrite Hfrs2. exact Hfrs3.
+ exact Hnin.
+ rewrite Hab2. exact Hab3.
+ rewrite Hfrs2. exact Hcnt3.
- (* rp_carry *) unfold rp_carry. split; [| split; [| split; [| split; [| split]]]].
+ (* rp_regs_ok *) unfold rp_regs_ok in HRG |- *.
destruct HRG as (R2 & R3 & R4 & R8 & R9 & R19 & R20 & R21 & R22 & R23 & R27).
repeat split;
[ rewrite <- R2; exact (HPR 2 ltac:(unfold acallee_saved; lia))
| rewrite <- R3; exact (HPR 3 ltac:(unfold acallee_saved; lia))
| rewrite <- R4; exact (HPR 4 ltac:(unfold acallee_saved; lia))
| rewrite <- R8; exact (HPR 8 ltac:(unfold acallee_saved; lia))
| rewrite <- R9; exact (HPR 9 ltac:(unfold acallee_saved; lia))
| rewrite <- R19; exact (HPR 19 ltac:(unfold acallee_saved; lia))
| rewrite <- R20; exact (HPR 20 ltac:(unfold acallee_saved; lia))
| rewrite <- R21; exact (HPR 21 ltac:(unfold acallee_saved; lia))
| rewrite <- R22; exact (HPR 22 ltac:(unfold acallee_saved; lia))
| rewrite <- R23; exact (HPR 23 ltac:(unfold acallee_saved; lia))
| rewrite <- R27; exact (HPR 27 ltac:(unfold acallee_saved; lia)) ].
+ (* rp_kept *) unfold rp_kept, tcj_kept.
split; [| split; [| split; [| split; [| split; [| split]]]]].
* exact Hwle'.
* intros a Hq1 Hq2 HE.
exact (eq_trans (KW a Hq1 Hq2) (TK1 a Hq1 Hq2 HE)).
* intros b m i Hin Hi HE.
exact (eq_trans (K2 b m i ltac:(rewrite Hab3; exact Hin) Hi (HE36 (b + i) (HdB b m i Hin Hi)))
(TK2 b m i Hin Hi HE)).
* intros a Hi Ho He. exact (eq_trans (K3 a Hi Ho He) (TK3 a Hi Ho He)).
* intros cid p a Hin Hz HE.
assert (Hin' : In (cid, p) (frames S3)) by (rewrite Hfrs3; right; exact Hin).
destruct Hz as [Hz | Hz].
{ exact (eq_trans (KFR cid p a Hin' Hz (HdF cid p a Hin Hz))
(TK4 cid p a Hin (or_introl Hz) HE)). }
{ exact (eq_trans (KSH cid p a Hin' Hz (HdS cid p a Hin Hz))
(TK4 cid p a Hin (or_intror Hz) HE)). }
* intros a Hq1 Hq2 Hp. apply K5; [exact Hq1 | rewrite HspA; lia |].
exact (TK5 a Hq1 Hq2 Hp).
* intros a Ha.
destruct (Z_le_gt_dec (rp_rA cx) a).
{ apply K5; [lia | rewrite HspA; lia | apply TK6; exact Ha]. }
destruct (Z_lt_ge_dec a (rp_rA cx - C_reac_ctrl_parse.REAC_CTRL_PARSE_STK)).
{ apply K5; [lia | rewrite HspA; lia | apply TK6; exact Ha]. }
{ apply K6. rewrite HspA. lia. }
+ (* rp_saved *) unfold rp_saved in HSAV |- *.
rewrite Forall_forall in HSAV |- *. intros p Hp. specialize (HSAV p Hp).
assert (Hoff : 8 <= fst p <= 104).
{ unfold rp_saves in Hp. cbn [In] in Hp.
repeat (destruct Hp as [Hp | Hp]; [subst p; cbn [fst]; lia |]). destruct Hp. }
apply (val_mem_kept SEGS (w_H (rc_W cx)) (w_H W') mem3 mem2 (rp_S cx - fst p) 8
(bv_unsigned (getr (rc_regs cx) (Z_to_bv 5 (snd p))))); [| exact HSAV].
intros kk Hkk. apply K1; [lia | rewrite HspA; lia].
+ (* rp_msg *) intros Harg Hn.
destruct (HMSG Harg Hn) as (HG3 & HT3).
destruct (HBmsg Harg Hn) as ((nb & Hinb & Hreq) & _ & _).
assert (Hmeq : forall a, rc_fr cx <= a < rc_fr cx + 50 ->
aview SEGS (w_H W') mem2 a = aview SEGS (w_H (rc_W cx)) mem3 a).
{ intros a Ha. replace a with (rc_fr cx + (a - rc_fr cx)) by lia.
apply (K2 (rc_fr cx) nb (a - rc_fr cx) ltac:(rewrite Hab3; exact Hinb) ltac:(lia)).
apply HE36. apply (HdB (rc_fr cx) nb (a - rc_fr cx) Hinb ltac:(lia)). }
assert (Hinb2 : In (rc_fr cx, nb) (ablocks B ly2 S2)) by (rewrite Hab2, Hab3; exact Hinb).
split.
* intros j Hj. destruct (HG3 j Hj) as (Hv & Hr). split; [| exact Hr].
assert (Hj50 : (j < 50)%nat) by (rewrite length_map, HBg50 in Hj; exact Hj).
apply (val_mem_kept SEGS (w_H (rc_W cx)) (w_H W') mem3 mem2 (rc_fr cx + Z.of_nat j) 1
(nth j (map bv_unsigned (rc_g cx)) 0)); [| exact Hv].
intros kk Hkk. apply Hmeq. lia.
* unfold tsrc_ok in HT3 |- *.
destruct HT3 as (T3a & T3b & T3c & T3d & T3e & T3f).
split; [| split; [| split; [| split; [| split]]]].
{ intros a Ha. destruct (T3a a Ha) as (Hv & Hs). split; [| exact Hs].
exact (fun Hc => Hv (eq_trans (eq_sym (Hmeq a Ha)) Hc)). }
{ exact (range_addressable_of_block SEGS B LAWS ly2 S2 W' mem2 md2 (rc_fr cx) nb (rc_fr cx) 50
HAR2 Hinb2 ltac:(lia) ltac:(lia)). }
{ exact (shadow_hull_vis_of_block SEGS B LAWS ly2 S2 W' mem2 md2 (rc_fr cx) nb (rc_fr cx) 50
HAR2 Hinb2 ltac:(lia) ltac:(lia) ltac:(lia)). }
{ exact T3d. }
{ exact T3e. }
{ exact T3f. }
+ (* rp_out *) intros Harg.
destruct (HOUT Harg) as (Opa & Opp & Opn & Opr).
destruct (HBcell Harg) as (_ & _ & _ & _ & _ & _ & Hfrm & _).
assert (Hcell : forall q n, (forall a, q <= a < q + n -> treply_out (rc_pa cx) (rc_pp cx) (rc_pn cx) a) ->
range_addressable (aview SEGS (w_H (rc_W cx)) mem3) SHADOW_OFF q n ->
range_addressable (aview SEGS (w_H W') mem2) SHADOW_OFF q n).
{ intros q n Hin Hra x Hx.
destruct (Hra x Hx) as (sv & Hsv & Hok). exists sv. split; [| exact Hok].
rewrite <- Hsv. destruct (Hfrm x (Hin x Hx)) as (cid & p & Hinf & Hz).
assert (Hinf' : In (cid, p) (frames S3)) by (rewrite Hfrs3; right; exact Hinf).
destruct (al_frames _ _ LAWS (rc_lyc cx) S3 (rc_W cx) mem3 md3 cid p HAR3 Hinf') as (Hm32 & _ & _ & _).
pose proof (YG0s.frame_facts B (rc_lyc cx) S3 (aview SEGS (w_H (rc_W cx)) mem3) cid p
(proj1 HAR3) Hinf') as (Hcid & _).
assert (Hbs8 : fs_frame_bytes cid mod 8 = 0).
{ rewrite (YG0s.fs_frame_bytes_eq cid ltac:(lia)).
replace (64 * 2 ^ cid) with ((8 * 2 ^ cid) * 8) by lia. apply Z_mod_mult. }
destruct (frames_bounds SEGS B LAWS (rc_lyc cx) S3 (rc_W cx) mem3 md3 cid p HAR3 Hinf')
as (Hf0 & Hfc & _).
assert (Hzin : shadow_addr (frame_addr (rc_lyc cx) cid p) <= shadow_addr x <
shadow_addr (frame_addr (rc_lyc cx) cid p) + fs_frame_bytes cid / 8).
{ apply rp_E2_shin.
- exact (rp_E2_m32_m8 _ Hm32).
- exact Hbs8.
- lia.
- exact (fs_frame_bytes_nonneg cid).
- unfold in_zr, frame_rng in Hz. cbn [fst snd] in Hz. lia. }
apply (KSH cid p (shadow_addr x) Hinf'); [unfold in_zr; cbn [fst snd]; exact Hzin |].
exact (HappC cid p (shadow_addr x) Hinf' Hzin). }
split; [| split; [| split]].
* apply (Hcell (rc_pa cx) 2); [intros a Ha; left; exact Ha | exact Opa].
* apply (Hcell (rc_pp cx) 8); [intros a Ha; right; left; exact Ha | exact Opp].
* apply (Hcell (rc_pn cx) 8); [intros a Ha; right; right; exact Ha | exact Opn].
* intros a Ha. destruct (Hfrm a Ha) as (cid & p & Hinf & Hz).
assert (Hinf2 : In (cid, p) (frames S2)) by (rewrite Hfrs2, Hfrs3; right; exact Hinf).
destruct (al_frames _ _ LAWS ly2 S2 W' mem2 md2 cid p HAR2 Hinf2) as (_ & _ & Hpres & _).
assert (Hrng : frame_addr ly2 cid p <= a < frame_addr ly2 cid p + fs_frame_bytes cid).
{ rewrite HFeq. unfold in_zr, frame_rng in Hz. cbn [fst snd] in Hz. lia. }
exact (proj1 (Hpres a Hrng)).
+ (* arodata_okS *) intros a Ha Hown Herr.
rewrite (K3 a ltac:(destruct Ha as [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr]
| exact (RELRO_IMG a Hr)]) Hown Herr).
exact (HRO a Ha Hown Herr).
- (* rp_fregs *) unfold rp_fregs in HFR |- *.
destruct HFR as (F18 & F26 & F25).
split; [rewrite <- F18; exact (HPR 18 ltac:(unfold acallee_saved; lia))
| split; [rewrite <- F26; exact (HPR 26 ltac:(unfold acallee_saved; lia))
| rewrite <- F25; exact (HPR 25 ltac:(unfold acallee_saved; lia))]].
- (* rp_fpres *) intros a Ha.
destruct (al_frames _ _ LAWS ly2 S2 W' mem2 md2 1 pos HAR2 Hin1') as (_ & _ & Hpres & _).
assert (Hrng : frame_addr ly2 1 pos <= a < frame_addr ly2 1 pos + fs_frame_bytes 1).
{ rewrite HFeq, HFB1. unfold rp_G in Ha. lia. }
exact (proj1 (Hpres a Hrng)).
- (* rp_fwords *) unfold rp_fwords in HFW |- *.
destruct HFW as (Fw0 & Fw8 & Fw16 & Fw120).
split; [| split; [| split]].
+ apply (val_mem_kept SEGS (w_H (rc_W cx)) (w_H W') mem3 mem2 (rp_G cx pos) 8 0x41b58ab3);
[intros kk Hkk; apply KG; lia | exact Fw0].
+ apply (val_mem_kept SEGS (w_H (rc_W cx)) (w_H W') mem3 mem2 (rp_G cx pos + 8) 8 (VAL (A_OBJ 15)));
[intros kk Hkk; apply KG; lia | exact Fw8].
+ apply (val_mem_kept SEGS (w_H (rc_W cx)) (w_H W') mem3 mem2 (rp_G cx pos + 16) 8 (VAL (A_OBJ 16)));
[intros kk Hkk; apply KG; lia | exact Fw16].
+ rewrite <- Fw120. apply rdword_ext. intros kk Hkk. apply KG; lia.
- (* rp_shadow *) unfold rp_shadow, shadow_cells in HSG |- *.
intros i Hi. rewrite <- (HSG i Hi). apply KGS.
unfold rp_sg_live in Hi. cbn [length] in Hi.
unfold shadow_of_addr, shadow_addr. lia.
- (* rp_argsb *) exact HARG.
- (* a0 *) exact Ha02.
- (* s8 *) rewrite <- Hs8. exact (HPR 24 ltac:(unfold acallee_saved; lia)).
- (* range_addressable of the record *) intros x Hx.
destruct (HRA36 x Hx) as (sv & Hsv & Hok). exists sv. split; [| exact Hok].
rewrite <- Hsv. apply KGS.
assert (Hzin : shadow_addr (rp_G cx pos) <= shadow_addr x < shadow_addr (rp_G cx pos) + 16).
{ exact (rp_E2_shin (rp_G cx pos) 128 x HGm8 eq_refl ltac:(lia) ltac:(lia) ltac:(lia)). }
unfold shadow_of_addr, shadow_addr in *. lia.
- (* the 36 record bytes *) intros i Hi.
apply (Hrec ltac:(unfold rp_G in *; lia) i Hi).
Qed.

(* rp_R5a local helpers. 0x840f8 .. 0x8416c and the three slow shadow paths 0x843d8 .. 0x843f4 hold no store, so
   the stretch is walked by concrete single steps (YK11 step_* + YA0n SRr_step): every step keeps the memory mem3
   and the world W3 and only re-materializes the model. *)
Lemma rp_R5a_go : forall (W : world SEGS) (regs : bvmap 5 word) (pc : word) (mem : word -> option byte)
(md : Model) (Q : world SEGS -> config -> Prop) (regs' : bvmap 5 word) (pc' : word),
RiscvSemantics.step SEGS (mkst regs pc (mrestrict (w_H W) mem) (seg_rom SEGS)) =
MachineOk (mkst regs' pc' (mrestrict (w_H W) mem) (seg_rom SEGS)) ->
(forall md', same_but_materialized md md' -> SRr SEGS W (mkCfg (mkst regs' pc' mem (seg_rom SEGS)) md') Q) ->
SRr SEGS W (mkCfg (mkst regs pc mem (seg_rom SEGS)) md) Q.
Proof.
intros W regs pc mem md Q regs' pc' Hs Hk.
eapply (SRr_step SEGS CtrlImg.ctrl_wx W); [reflexivity | rewrite restrict_mkst_fx; exact Hs |].
intros md' Hsame. cbn [ms_mem mkst]. rewrite unrestrict_mkst_mrestrict. exact (Hk md' Hsame).
Qed.
Lemma rp_R5a_vaddi : forall x k, v_addi (Z_to_bv 64 x) k = Z_to_bv 64 (x + k).
Proof. intros x k. apply bv_eq. unfold v_addi. rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite Zplus_mod_idemp_l. reflexivity. Qed.
Lemma rp_R5a_vadd : forall x y, v_add (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x + y).
Proof.
intros x y. apply bv_eq. unfold v_add. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
rewrite Zplus_mod_idemp_l, Zplus_mod_idemp_r. reflexivity.
Qed.
Lemma rp_R5a_vsrli3 : forall x, 0 <= x < 2 ^ 64 -> v_srli (Z_to_bv 64 x) 3 = Z_to_bv 64 (x / 8).
Proof. intros x Hx. unfold v_srli. rewrite unsigned_lit_small by exact Hx. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.
Lemma rp_R5a_vandi7 : forall x, 0 <= x < 2 ^ 64 -> v_andi (Z_to_bv 64 x) 7 = Z_to_bv 64 (x mod 8).
Proof.
intros x Hx. unfold v_andi. rewrite unsigned_lit_small by exact Hx. change (bv_wrap 64 7) with (Z.ones 3).
rewrite Z.land_ones by lia. reflexivity.
Qed.
Lemma rp_R5a_ceq : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> c_eq (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof. intros a b Ha Hb. unfold c_eq, bv_eqb. rewrite !unsigned_lit_small by assumption. reflexivity. Qed.
Lemma rp_R5a_clts : forall a b, 0 <= a < 2 ^ 63 -> 0 <= b < 2 ^ 63 -> c_lts (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof.
intros a b Ha Hb. unfold c_lts, bv_lts.
rewrite !bv_signed_small by (rewrite unsigned_lit_small by lia; lia). rewrite !unsigned_lit_small by lia. reflexivity.
Qed.
(* the 0x8416c test (RcReplyLib.v:43 rc_srange, restated over c_ltu: RcReplyLib is not loaded here) *)
Lemma rp_R5a_ltu : forall s, 0 <= s < 256 ->
c_ltu (Z_to_bv 64 (s + -24)) (Z_to_bv 64 (-10)) = negb ((14 <=? s) && (s <=? 23)).
Proof.
intros s Hs. rewrite c_ltu_ltb, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
change ((-10) mod 2 ^ 64) with 18446744073709551606.
destruct (Z.ltb_spec s 24) as [L|L].
- replace ((s + -24) mod 2 ^ 64) with (s + -24 + 2 ^ 64)
    by (apply Z.mod_unique with (q := -1); [left; lia | lia]).
  destruct (Z.leb_spec 14 s) as [L14|L14]; cbn [andb negb].
  + replace (s <=? 23) with true by (symmetry; apply Z.leb_le; lia). cbn [negb]. apply Z.ltb_ge. lia.
  + apply Z.ltb_lt. lia.
- rewrite Z.mod_small by lia. replace (s <=? 23) with false by (symmetry; apply Z.leb_gt; lia).
  rewrite andb_false_r. cbn [negb]. apply Z.ltb_lt. lia.
Qed.
Lemma rp_R5a_lbv : forall b : byte, bv_unsigned b < 128 -> v_lb b = Z_to_bv 64 (bv_unsigned b).
Proof.
intros b Hb. unfold v_lb, bv_signed. rewrite bv_swrap_small; [reflexivity|].
change (bv_half_modulus 8) with 128. pose proof (u8_range b). lia.
Qed.
Lemma rp_R5a_mbyte : forall (H : word -> bool) mem a (b : byte),
aview SEGS H mem a = Some (bv_unsigned b) -> mbyte SEGS (mrestrict H mem) a = Some b.
Proof.
intros H mem a b Hv. unfold aview in Hv.
destruct (mbyte SEGS (mrestrict H mem) a) as [c|]; cbn in Hv; [|discriminate].
injection Hv as Hc. f_equal. apply bv_eq. exact Hc.
Qed.
Lemma rp_R5a_mbyte_ex : forall (H : word -> bool) mem a s, aview SEGS H mem a = Some s ->
exists b : byte, mbyte SEGS (mrestrict H mem) a = Some b /\ bv_unsigned b = s.
Proof.
intros H mem a s Hv. unfold aview in Hv.
destruct (mbyte SEGS (mrestrict H mem) a) as [c|]; cbn in Hv; [|discriminate].
injection Hv as Hc. exists c. split; [reflexivity | exact Hc].
Qed.
Lemma rp_R5a_rd1 : forall m a (b : byte), mbyte SEGS m a = Some b -> rdn SEGS m (Z_to_bv 64 a) 1 = Some [b].
Proof.
intros m a b H. apply rdn_mbytes. split; [reflexivity|]. intros i Hi.
destruct i as [|i]; [|lia]. cbn [nth_error]. replace (a + Z.of_nat 0) with a by lia. exact H.
Qed.
Lemma rp_R5a_rd2 : forall m a (b0 b1 : byte), mbyte SEGS m a = Some b0 -> mbyte SEGS m (a + 1) = Some b1 ->
rdn SEGS m (Z_to_bv 64 a) 2 = Some [b0; b1].
Proof.
intros m a b0 b1 H0 H1. apply rdn_mbytes. split; [reflexivity|]. intros i Hi.
destruct i as [|[|i]]; [| |lia]; cbn [nth_error].
- replace (a + Z.of_nat 0) with a by lia. exact H0.
- replace (a + Z.of_nat 1) with (a + 1) by lia. exact H1.
Qed.
Lemma rp_R5a_lor8 : forall a b, 0 <= a < 256 -> 0 <= b -> Z.lor a (Z.shiftl b 8) = a + b * 256.
Proof.
intros a b Ha Hb.
assert (Hl : Z.land a (Z.shiftl b 8) = 0).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
  - rewrite Z.shiftl_spec_low by lia. apply andb_false_r.
  - rewrite (Z_testbit_high 8 a i) by lia. reflexivity. }
rewrite <- Z.lxor_lor by exact Hl. rewrite <- Z.add_nocarry_lxor by exact Hl.
rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.
Lemma rp_R5a_ble2 : forall b0 b1 : byte, bytes_le_to_Z [b0; b1] = bv_unsigned b0 + bv_unsigned b1 * 256.
Proof.
intros b0 b1. pose proof (u8_range b0). pose proof (u8_range b1). cbn [bytes_le_to_Z].
rewrite Z.shiftl_0_l, Z.lor_0_r. apply rp_R5a_lor8; lia.
Qed.
Lemma rp_R5a_nthv : forall (g : list byte) j, nth j (map bv_unsigned g) 0 = cp_v g j.
Proof. intros g. unfold cp_v, cp_b. induction g as [|x g IH]; intros [|j]; cbn [map nth]; try reflexivity. apply IH. Qed.
Lemma rp_R5a_rec : forall len (g : list byte), fst (ctrlparse len g) = 5 -> 50 <= len /\
nth 28 (snd (ctrlparse len g)) cp_z = cp_b g 35 /\ nth 29 (snd (ctrlparse len g)) cp_z = cp_b g 34.
Proof.
intros len g Hk. destruct (ctrlparse_rec len g (or_introl Hk)) as (HD & _ & H28 & H29).
apply cp_hdr_spec in HD. split; [lia | split; assumption].
Qed.
Lemma rp_R5a_irF : forall len (g : list byte),
(fst (ctrlparse len g) = 5 -> cp_v g 34 * 256 + cp_v g 35 = 0x500 -> cp_v g 32 = 0x12 -> cp_v g 33 = 0x12 ->
14 <= cp_v g 26 <= 23 -> False) -> ir len g = false.
Proof.
intros len g H. destruct (ir len g) eqn:E; [|reflexivity]. exfalso. apply ir_true in E. unfold ir_s in E.
destruct E as (E1 & E2 & E3 & E4 & E5 & _). exact (H E1 E2 E3 E4 E5).
Qed.
(* the registers the stretch keeps (a0 / a1 / a2 are its only targets) *)
Definition rp_R5a_RS (cx : rcx) (pos : Z) (regs : bvmap 5 word) : Prop :=
rp_regs_ok cx regs /\ rp_fregs cx pos regs /\ getr regs 24 = w64 (rp_G cx pos + 32).
Lemma rp_R5a_RS_upd : forall cx pos regs (r : bv 5) v, r = 10%bv \/ r = 11%bv \/ r = 12%bv ->
rp_R5a_RS cx pos regs -> rp_R5a_RS cx pos (regupd regs r v).
Proof.
intros cx pos regs r v Hr HR. unfold rp_R5a_RS, rp_regs_ok, rp_fregs in *.
destruct Hr as [ -> | [ -> | -> ] ]; rewrite !getr_other by reg_neq_tac; exact HR.
Qed.
Lemma rp_R5a_jhold : forall cx pos ly3 S3 W3 mem3 md md', rp_jhold cx pos ly3 S3 W3 mem3 md ->
same_but_materialized md md' -> rp_jhold cx pos ly3 S3 W3 mem3 md'.
Proof.
intros cx pos ly3 S3 W3 mem3 md md' HJH Hm. unfold rp_jhold in *. destruct HJH as (HJ & Hr). split; [|exact Hr].
rewrite (same_but_materialized_wvb md md' Hm). apply (ajournal_materialize SEGS B LAWS CtrlImg.ctrl_segs_low). exact HJ.
Qed.
Lemma rp_R5a_kept : forall cx W3 mem3, rp_kept cx W3 mem3 rp_Enone -> rp_kept cx W3 mem3 (rp_Eout cx).
Proof.
intros cx W3 mem3 Hk. unfold rp_kept, tcj_kept in *. destruct Hk as (Hw & K1 & K2 & K3 & K4 & K5 & K6).
split; [exact Hw|]. split; [intros a Ha Hs _; exact (K1 a Ha Hs (fun x => x))|].
split; [intros b m i Hin Hi _; exact (K2 b m i Hin Hi (fun x => x))|].
split; [exact K3|]. split; [intros cid p a Hin Hr _; exact (K4 cid p a Hin Hr (fun x => x))|].
split; [exact K5 | exact K6].
Qed.
Lemma rp_R5a_carry : forall cx regs regs' W3 mem3 (E : Z -> Prop),
rp_carry cx regs W3 mem3 rp_Enone -> rp_regs_ok cx regs' ->
(rp_kept cx W3 mem3 rp_Enone -> rp_kept cx W3 mem3 E) -> rp_carry cx regs' W3 mem3 E.
Proof.
intros cx regs regs' W3 mem3 E HC Hrg HkE. unfold rp_carry in *. destruct HC as (_ & Hk & Hr).
exact (conj Hrg (conj (HkE Hk) Hr)).
Qed.
Local Ltac rp_R5a_fetch :=
lazymatch goal with |- fetch_word _ (Z_to_bv 64 ?pc) = Some _ =>
let r := eval vm_compute in (clookup CtrlImg.ctrltbl pc) in
lazymatch r with Some ?w => exact (CtrlImg.ctrltbl_ok pc w ltac:(vm_compute; reflexivity)) end end.
Local Ltac rp_R5a_ecall := lazymatch goal with |- is_ecall _ = false => vm_compute; reflexivity end.
Local Ltac rp_R5a_dec := lazymatch goal with |- decode_any _ = Some _ =>
apply (@bool_decide_eq_true_1 _ _); vm_compute; reflexivity end.
Local Ltac rp_R5a_auto := lazymatch goal with
| |- fetch_word _ _ = _ => rp_R5a_fetch
| |- is_ecall _ = _ => rp_R5a_ecall
| |- decode_any _ = _ => rp_R5a_dec
| _ => idtac end.
Local Ltac rp_R5a_zlit x := lazymatch x with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.
Local Ltac rp_R5a_norm :=
try unfold btgt;
repeat first
[ rewrite getr_zero
| rewrite getr_same by reg_neq_tac
| rewrite getr_other by reg_neq_tac
| match goal with
  | |- context [bv_eqb ?a ?b] =>
      let v := eval vm_compute in (bv_eqb a b) in
      lazymatch v with
      | true => change (bv_eqb a b) with true; cbv beta iota
      | false => change (bv_eqb a b) with false; cbv beta iota end
  | |- context [bv_signed ?a] =>
      let v := eval vm_compute in (bv_signed a) in rp_R5a_zlit v; change (bv_signed a) with v
  | |- context [@bv_unsigned 6 ?a] =>
      let v := eval vm_compute in (bv_unsigned a) in rp_R5a_zlit v; change (bv_unsigned a) with v
  | |- context [v_addi (Z_to_bv 64 ?x) ?k] => rewrite (rp_R5a_vaddi x k)
  | |- context [v_add (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)] => rewrite (rp_R5a_vadd x y)
  | |- context [Z_to_bv 64 (?a + ?b)] =>
      rp_R5a_zlit a; rp_R5a_zlit b; let v := eval vm_compute in (a + b) in change (a + b) with v
  end ].
Local Ltac rp_R5a_mdnext H :=
let md := fresh "md" in let Hs := fresh "Hs" in intros md Hs;
apply (same_but_materialized_trans _ _ _ H) in Hs; clear H; rename Hs into H.
Local Ltac rp_R5a_rs :=
repeat (apply rp_R5a_RS_upd; [first [left; reflexivity | right; left; reflexivity | right; right; reflexivity] |]);
assumption.

(* R5a  C6 -> C7 or C11, 0x840f8..0x8416c (+0x16c..+0x1e0). kind = 5 (`bne` to 0x84204), the u16 at G+60
   (= struct[28..29] = g35, g34 by RcParse.ctrlparse_rec, so cp_v g 34 * 256 + cp_v g 35 = 0x500), the two
   0x12 bytes at fr+32 / fr+33 and the range test on s = fr[26] (`rc_srange`, RcReplyLib.v:43). Each message
   load is preceded by its shadow check, discharged from rp_msg's `tsrc_ok`; each failing arm goes to 0x84204
   and so to C11 with a0 = 0 and `ir len g = false`.
   Donors: B `rp_tag` :3894, `rr_ir_false` :3783; A18 `seg_tests` :3018, `seg_tests_short` :3132, `ir_pass`
   :3001. Difficulty: medium-hard (many branches; the model side is `ir`'s conjuncts one at a time). *)
Lemma rp_R5a : rp_from_C7 -> rp_from_C11 -> rp_from_C6.
Proof.
intros HC7 HC11 cx pos regs3 ly3 S3 W3 mem3 md3 HB H6.
pose proof H6 as (HJ & HCa & HFr & HFp & HFw & HSh & HA & H10 & H24 & HRA & HREC).
assert (HCa' := HCa). unfold rp_carry in HCa'. destruct HCa' as (HRg & _ & _ & HMsg & _).
assert (HLg : length (rc_g cx) = 50%nat) by (unfold rp_base in HB; decompose [and] HB; assumption).
assert (RS3 : rp_R5a_RS cx pos regs3) by (split; [exact HRg | split; [exact HFr | exact H24]]).
(* the fail join: 0x84204 `li a0,0`, then C11 at 0x84208 *)
assert (KF : forall regs pc md', pc = Z_to_bv 64 0x84204 -> rp_R5a_RS cx pos regs ->
  same_but_materialized md3 md' -> ir (rc_len cx) (rc_g cx) = false ->
  SRr SEGS W3 (mkCfg (mkst regs pc mem3 (seg_rom SEGS)) md') (rp_post cx)).
{ intros regs pc md' -> RS HmK Hir.
  eapply rp_R5a_go; [eapply step_addi with (rd := 10%bv) (rs := 0%bv) (imm := 0%bv); rp_R5a_auto |].
  rp_R5a_mdnext HmK. rp_R5a_norm.
  pose proof (rp_R5a_RS_upd cx pos regs 10%bv (Z_to_bv 64 0) (or_introl eq_refl) RS) as (Hrg' & Hfr' & _).
  change (Z_to_bv 64 0x84208) with (w64 (rp_pc 0x27c)).
  apply (HC11 cx pos _ ly3 S3 W3 mem3 _ HB).
  unfold rp_C11.
  split; [exact (rp_R5a_jhold cx pos ly3 S3 W3 mem3 md3 _ HJ HmK)|].
  split; [exact (rp_R5a_carry cx regs3 _ W3 mem3 (rp_Eout cx) HCa Hrg' (rp_R5a_kept cx W3 mem3))|].
  split; [exact Hfr'|]. split; [exact HFp|]. split; [exact HFw|]. split; [exact HSh|]. split; [exact HA|].
  unfold rp_argsb in HA. split.
  - rewrite getr_same by reg_neq_tac. unfold rp_ret, reply_ret. rewrite HA, Hir. reflexivity.
  - unfold rp_okb, reply_ok. rewrite HA, Hir. cbn [andb]. discriminate. }
(* the pass exit: C7 at 0x84170 *)
assert (KO : forall regs pc md', pc = Z_to_bv 64 0x84170 -> rp_R5a_RS cx pos regs ->
  same_but_materialized md3 md' -> rp_tags cx -> getr regs 11 = w64 (rp_s cx) ->
  SRr SEGS W3 (mkCfg (mkst regs pc mem3 (seg_rom SEGS)) md') (rp_post cx)).
{ intros regs pc md' -> (Hrg & Hfr' & _) HmK Ht H11.
  change (Z_to_bv 64 0x84170) with (w64 (rp_pc 0x1e4)).
  apply (HC7 cx pos regs ly3 S3 W3 mem3 md' HB).
  unfold rp_C7.
  split; [exact (rp_R5a_jhold cx pos ly3 S3 W3 mem3 md3 md' HJ HmK)|].
  split; [exact (rp_R5a_carry cx regs3 regs W3 mem3 rp_Enone HCa Hrg (fun h => h))|].
  split; [exact Hfr'|]. split; [exact HFp|]. split; [exact HFw|]. split; [exact HSh|]. split; [exact HA|].
  split; [exact Ht | exact H11]. }
unfold cfg_at. change (w64 (rp_pc 0x16c)) with (Z_to_bv 64 0x840f8).
assert (HmK : same_but_materialized md3 md3) by apply same_but_materialized_refl.
pose proof (ctrlparse_kind_range (rc_len cx) (rc_g cx)) as Hkr.
(* 0x840f8 li a1,5 *)
eapply rp_R5a_go; [eapply step_addi with (rd := 11%bv) (rs := 0%bv) (imm := 5%bv); rp_R5a_auto |].
rp_R5a_mdnext HmK. rp_R5a_norm.
(* 0x840fc bne a0,a1 -> 0x84204 : kind = 5 *)
destruct (Z.eqb_spec (fst (ctrlparse (rc_len cx) (rc_g cx))) 5) as [E5|N5].
2:{ eapply rp_R5a_go.
    { eapply step_bne_tk with (rs1 := 10%bv) (rs2 := 11%bv) (imm := Z_to_bv 13 264); rp_R5a_auto.
      rp_R5a_norm. rewrite H10. unfold w64. rewrite rp_R5a_ceq by lia. apply Z.eqb_neq. exact N5. }
    rp_R5a_mdnext HmK. rp_R5a_norm.
    apply (KF _ _ _ eq_refl); [rp_R5a_rs | exact HmK | apply rp_R5a_irF; intros; lia]. }
(* kind = 5: the message is read (len >= 50) *)
destruct (rp_R5a_rec _ _ E5) as (H50 & H28 & H29).
destruct (HMsg HA H50) as (HG8 & HTS).
destruct HTS as (_ & HRAm & _ & _ & Hfr0 & Hfr63).
assert (MB : forall j, (j < 50)%nat ->
  mbyte SEGS (mrestrict (w_H W3) mem3) (rc_fr cx + Z.of_nat j) = Some (cp_b (rc_g cx) j)).
{ intros j Hj. rewrite (garr8_mbyte SEGS _ _ _ j HG8) by (rewrite length_map, HLg; exact Hj).
  rewrite rp_R5a_nthv. unfold cp_v. rewrite Z_to_bv_bv_unsigned. reflexivity. }
assert (SH : forall x, rc_fr cx <= x < rc_fr cx + 50 -> exists b : byte,
  mbyte SEGS (mrestrict (w_H W3) mem3) (shadow_of_addr SHADOW_OFF x) = Some b /\ saddr_ok x (bv_unsigned b)).
{ intros x Hx. destruct (HRAm x Hx) as (s & Hs & Hok). destruct (rp_R5a_mbyte_ex _ _ _ _ Hs) as (b & Hb & Hbu).
  exists b. rewrite Hbu. split; assumption. }
pose proof (cp_v_range' (rc_g cx) 26) as R26. pose proof (cp_v_range' (rc_g cx) 32) as R32.
pose proof (cp_v_range' (rc_g cx) 33) as R33. pose proof (cp_v_range' (rc_g cx) 34) as R34.
pose proof (cp_v_range' (rc_g cx) 35) as R35.
(* 0x840fc not taken *)
eapply rp_R5a_go.
{ eapply step_bne_ft with (rs1 := 10%bv) (rs2 := 11%bv) (imm := Z_to_bv 13 264); rp_R5a_auto.
  rp_R5a_norm. rewrite H10. unfold w64. rewrite rp_R5a_ceq by lia. apply Z.eqb_eq. exact E5. }
rp_R5a_mdnext HmK. rp_R5a_norm.
(* 0x84100 lhu a0,28(s8): the u16 at G+60 is [g35; g34] *)
eapply rp_R5a_go.
{ eapply step_lhu with (rd := 10%bv) (rs := 24%bv) (imm := 28%bv) (bs := [cp_b (rc_g cx) 35; cp_b (rc_g cx) 34])
    (v := Z_to_bv 64 (cp_v (rc_g cx) 35 + cp_v (rc_g cx) 34 * 256)); rp_R5a_auto.
  - rp_R5a_norm. rewrite H24. unfold w64. rp_R5a_norm. apply rp_R5a_rd2.
    + apply rp_R5a_mbyte. rewrite <- H28.
      replace (rp_G cx pos + 32 + 28) with (rp_G cx pos + 32 + Z.of_nat 28) by lia. apply HREC. lia.
    + apply rp_R5a_mbyte. rewrite <- H29.
      replace (rp_G cx pos + 32 + 28 + 1) with (rp_G cx pos + 32 + Z.of_nat 29) by lia. apply HREC. lia.
  - rewrite rp_R5a_ble2. rewrite unsigned_lit_small by lia. reflexivity. }
rp_R5a_mdnext HmK. rp_R5a_norm.
(* 0x84104 li a1,1280 *)
eapply rp_R5a_go; [eapply step_addi with (rd := 11%bv) (rs := 0%bv) (imm := 1280%bv); rp_R5a_auto |].
rp_R5a_mdnext HmK. rp_R5a_norm.
(* 0x84108 bne a0,a1 -> 0x84204 : the u16 is 0x500 *)
destruct (Z.eqb_spec (cp_v (rc_g cx) 34 * 256 + cp_v (rc_g cx) 35) 0x500) as [EU|NU].
2:{ eapply rp_R5a_go.
    { eapply step_bne_tk with (rs1 := 10%bv) (rs2 := 11%bv) (imm := Z_to_bv 13 252); rp_R5a_auto.
      rp_R5a_norm. rewrite rp_R5a_ceq by lia. apply Z.eqb_neq. lia. }
    rp_R5a_mdnext HmK. rp_R5a_norm.
    apply (KF _ _ _ eq_refl); [rp_R5a_rs | exact HmK | apply rp_R5a_irF; intros; lia]. }
(* 0x84160 .. 0x8416c: s = fr[26] and its range test *)
assert (K160 : forall regs pc md', pc = Z_to_bv 64 0x84160 -> rp_R5a_RS cx pos regs ->
  same_but_materialized md3 md' -> cp_v (rc_g cx) 32 = 0x12 -> cp_v (rc_g cx) 33 = 0x12 ->
  getr regs 10 = Z_to_bv 64 (rc_fr cx + 26) ->
  SRr SEGS W3 (mkCfg (mkst regs pc mem3 (seg_rom SEGS)) md') (rp_post cx)).
{ intros regs pc md' -> RS Hm0 E32 E33 A10. clear HmK. rename Hm0 into HmK.
  eapply rp_R5a_go.
  { eapply step_lbu with (rd := 11%bv) (rs := 10%bv) (imm := 0%bv) (b := cp_b (rc_g cx) 26); rp_R5a_auto.
    rp_R5a_norm. rewrite A10. rp_R5a_norm. apply rp_R5a_rd1. rewrite Z.add_0_r. exact (MB 26%nat ltac:(lia)). }
  rp_R5a_mdnext HmK. rp_R5a_norm. change (bv_unsigned (cp_b (rc_g cx) 26)) with (cp_v (rc_g cx) 26).
  eapply rp_R5a_go; [eapply step_addi with (rd := 10%bv) (rs := 11%bv) (imm := Z_to_bv 12 (-24)); rp_R5a_auto |].
  rp_R5a_mdnext HmK. rp_R5a_norm.
  eapply rp_R5a_go; [eapply step_addi with (rd := 12%bv) (rs := 0%bv) (imm := Z_to_bv 12 (-10)); rp_R5a_auto |].
  rp_R5a_mdnext HmK. rp_R5a_norm.
  destruct ((14 <=? cp_v (rc_g cx) 26) && (cp_v (rc_g cx) 26 <=? 23)) eqn:ER.
  - eapply rp_R5a_go.
    { eapply step_bltu_ft with (rs1 := 10%bv) (rs2 := 12%bv) (imm := Z_to_bv 13 152); rp_R5a_auto.
      rp_R5a_norm. rewrite rp_R5a_ltu by lia. rewrite ER. reflexivity. }
    rp_R5a_mdnext HmK. rp_R5a_norm.
    apply andb_true_iff in ER as [ER1 ER2]. apply Z.leb_le in ER1. apply Z.leb_le in ER2.
    apply (KO _ _ _ eq_refl); [rp_R5a_rs | exact HmK | |].
    + unfold rp_tags, rp_s, ir_s. split; [exact H50|]. split; [exact E5|]. split; [exact EU|].
      split; [exact E32|]. split; [exact E33|]. lia.
    + rp_R5a_norm. unfold rp_s, ir_s, w64. reflexivity.
  - eapply rp_R5a_go.
    { eapply step_bltu_tk with (rs1 := 10%bv) (rs2 := 12%bv) (imm := Z_to_bv 13 152); rp_R5a_auto.
      rp_R5a_norm. rewrite rp_R5a_ltu by lia. rewrite ER. reflexivity. }
    rp_R5a_mdnext HmK. rp_R5a_norm.
    apply (KF _ _ _ eq_refl); [rp_R5a_rs | exact HmK |].
    apply rp_R5a_irF. intros _ _ _ _ Hs.
    rewrite (proj2 (Z.leb_le _ _) (proj1 Hs)), (proj2 (Z.leb_le _ _) (proj2 Hs)) in ER. discriminate. }
(* 0x8414c .. 0x8415c (slow path 0x843f0 / 0x843f4): the shadow check of fr+26 *)
assert (K14c : forall regs pc md', pc = Z_to_bv 64 0x8414c -> rp_R5a_RS cx pos regs ->
  same_but_materialized md3 md' -> cp_v (rc_g cx) 32 = 0x12 -> cp_v (rc_g cx) 33 = 0x12 ->
  SRr SEGS W3 (mkCfg (mkst regs pc mem3 (seg_rom SEGS)) md') (rp_post cx)).
{ intros regs pc md' -> RS Hm0 E32 E33. clear HmK. rename Hm0 into HmK.
  pose proof RS as ((_ & _ & _ & _ & _ & _ & _ & _ & R22 & _ & R27) & _ & _). unfold w64 in R22, R27.
  destruct (SH (rc_fr cx + 26) ltac:(lia)) as (bs & Hbs & Hok).
  assert (Hs8 : 0 <= bv_unsigned bs < 8) by (pose proof (u8_range bs); unfold saddr_ok in Hok; lia).
  eapply rp_R5a_go; [eapply step_addi with (rd := 10%bv) (rs := 22%bv) (imm := 26%bv); rp_R5a_auto |].
  rp_R5a_mdnext HmK. rp_R5a_norm. rewrite R22. rp_R5a_norm.
  eapply rp_R5a_go; [eapply step_srli with (rd := 11%bv) (rs := 10%bv) (sh := 3%bv); rp_R5a_auto |].
  rp_R5a_mdnext HmK. rp_R5a_norm. rewrite rp_R5a_vsrli3 by lia.
  eapply rp_R5a_go; [eapply step_add with (rd := 11%bv) (rs1 := 11%bv) (rs2 := 27%bv); rp_R5a_auto |].
  rp_R5a_mdnext HmK. rp_R5a_norm. rewrite R27. rp_R5a_norm.
  eapply rp_R5a_go.
  { eapply step_lb with (rd := 11%bv) (rs := 11%bv) (imm := 0%bv) (b := bs); rp_R5a_auto.
    rp_R5a_norm. apply rp_R5a_rd1.
    replace ((rc_fr cx + 26) / 8 + SHADOW_OFF + 0) with (shadow_of_addr SHADOW_OFF (rc_fr cx + 26))
      by (unfold shadow_of_addr; lia). exact Hbs. }
  rp_R5a_mdnext HmK. rp_R5a_norm. rewrite (rp_R5a_lbv bs) by lia.
  destruct (Z.eqb_spec (bv_unsigned bs) 0) as [S0|SN].
  - eapply rp_R5a_go.
    { eapply step_bne_ft with (rs1 := 11%bv) (rs2 := 0%bv) (imm := Z_to_bv 13 660); rp_R5a_auto.
      rp_R5a_norm. rewrite rp_R5a_ceq by lia. apply Z.eqb_eq. exact S0. }
    rp_R5a_mdnext HmK. rp_R5a_norm.
    apply (K160 _ _ _ eq_refl); [rp_R5a_rs | exact HmK | exact E32 | exact E33 | rp_R5a_norm; reflexivity].
  - eapply rp_R5a_go.
    { eapply step_bne_tk with (rs1 := 11%bv) (rs2 := 0%bv) (imm := Z_to_bv 13 660); rp_R5a_auto.
      rp_R5a_norm. rewrite rp_R5a_ceq by lia. apply Z.eqb_neq. exact SN. }
    rp_R5a_mdnext HmK. rp_R5a_norm.
    eapply rp_R5a_go; [eapply step_andi with (rd := 12%bv) (rs := 10%bv) (imm := 7%bv); rp_R5a_auto |].
    rp_R5a_mdnext HmK. rp_R5a_norm. rewrite rp_R5a_vandi7 by lia.
    eapply rp_R5a_go.
    { eapply step_blt_tk with (rs1 := 12%bv) (rs2 := 11%bv) (imm := Z_to_bv 13 (-660)); rp_R5a_auto.
      rp_R5a_norm. rewrite rp_R5a_clts by (pose proof (Z.mod_pos_bound (rc_fr cx + 26) 8 ltac:(lia)); lia).
      apply Z.ltb_lt. unfold saddr_ok in Hok. lia. }
    rp_R5a_mdnext HmK. rp_R5a_norm.
    apply (K160 _ _ _ eq_refl); [rp_R5a_rs | exact HmK | exact E32 | exact E33 | rp_R5a_norm; reflexivity]. }
(* 0x84140 .. 0x84148: fr[33] = 0x12 *)
assert (K140 : forall regs pc md', pc = Z_to_bv 64 0x84140 -> rp_R5a_RS cx pos regs ->
  same_but_materialized md3 md' -> cp_v (rc_g cx) 32 = 0x12 -> getr regs 10 = Z_to_bv 64 (rc_fr cx + 33) ->
  SRr SEGS W3 (mkCfg (mkst regs pc mem3 (seg_rom SEGS)) md') (rp_post cx)).
{ intros regs pc md' -> RS Hm0 E32 A10. clear HmK. rename Hm0 into HmK.
  eapply rp_R5a_go.
  { eapply step_lbu with (rd := 10%bv) (rs := 10%bv) (imm := 0%bv) (b := cp_b (rc_g cx) 33); rp_R5a_auto.
    rp_R5a_norm. rewrite A10. rp_R5a_norm. apply rp_R5a_rd1. rewrite Z.add_0_r. exact (MB 33%nat ltac:(lia)). }
  rp_R5a_mdnext HmK. rp_R5a_norm. change (bv_unsigned (cp_b (rc_g cx) 33)) with (cp_v (rc_g cx) 33).
  eapply rp_R5a_go; [eapply step_addi with (rd := 11%bv) (rs := 0%bv) (imm := 18%bv); rp_R5a_auto |].
  rp_R5a_mdnext HmK. rp_R5a_norm.
  destruct (Z.eqb_spec (cp_v (rc_g cx) 33) 0x12) as [E33|N33].
  - eapply rp_R5a_go.
    { eapply step_bne_ft with (rs1 := 10%bv) (rs2 := 11%bv) (imm := Z_to_bv 13 188); rp_R5a_auto.
      rp_R5a_norm. rewrite rp_R5a_ceq by lia. apply Z.eqb_eq. exact E33. }
    rp_R5a_mdnext HmK. rp_R5a_norm.
    apply (K14c _ _ _ eq_refl); [rp_R5a_rs | exact HmK | exact E32 | exact E33].
  - eapply rp_R5a_go.
    { eapply step_bne_tk with (rs1 := 10%bv) (rs2 := 11%bv) (imm := Z_to_bv 13 188); rp_R5a_auto.
      rp_R5a_norm. rewrite rp_R5a_ceq by lia. apply Z.eqb_neq. exact N33. }
    rp_R5a_mdnext HmK. rp_R5a_norm.
    apply (KF _ _ _ eq_refl); [rp_R5a_rs | exact HmK | apply rp_R5a_irF; intros; lia]. }
(* 0x8412c .. 0x8413c (slow path 0x843e4 / 0x843e8): the shadow check of fr+33 *)
assert (K12c : forall regs pc md', pc = Z_to_bv 64 0x8412c -> rp_R5a_RS cx pos regs ->
  same_but_materialized md3 md' -> cp_v (rc_g cx) 32 = 0x12 ->
  SRr SEGS W3 (mkCfg (mkst regs pc mem3 (seg_rom SEGS)) md') (rp_post cx)).
{ intros regs pc md' -> RS Hm0 E32. clear HmK. rename Hm0 into HmK.
  pose proof RS as ((_ & _ & _ & _ & _ & _ & _ & _ & R22 & _ & R27) & _ & _). unfold w64 in R22, R27.
  destruct (SH (rc_fr cx + 33) ltac:(lia)) as (bs & Hbs & Hok).
  assert (Hs8 : 0 <= bv_unsigned bs < 8) by (pose proof (u8_range bs); unfold saddr_ok in Hok; lia).
  eapply rp_R5a_go; [eapply step_addi with (rd := 10%bv) (rs := 22%bv) (imm := 33%bv); rp_R5a_auto |].
  rp_R5a_mdnext HmK. rp_R5a_norm. rewrite R22. rp_R5a_norm.
  eapply rp_R5a_go; [eapply step_srli with (rd := 11%bv) (rs := 10%bv) (sh := 3%bv); rp_R5a_auto |].
  rp_R5a_mdnext HmK. rp_R5a_norm. rewrite rp_R5a_vsrli3 by lia.
  eapply rp_R5a_go; [eapply step_add with (rd := 11%bv) (rs1 := 11%bv) (rs2 := 27%bv); rp_R5a_auto |].
  rp_R5a_mdnext HmK. rp_R5a_norm. rewrite R27. rp_R5a_norm.
  eapply rp_R5a_go.
  { eapply step_lb with (rd := 11%bv) (rs := 11%bv) (imm := 0%bv) (b := bs); rp_R5a_auto.
    rp_R5a_norm. apply rp_R5a_rd1.
    replace ((rc_fr cx + 33) / 8 + SHADOW_OFF + 0) with (shadow_of_addr SHADOW_OFF (rc_fr cx + 33))
      by (unfold shadow_of_addr; lia). exact Hbs. }
  rp_R5a_mdnext HmK. rp_R5a_norm. rewrite (rp_R5a_lbv bs) by lia.
  destruct (Z.eqb_spec (bv_unsigned bs) 0) as [S0|SN].
  - eapply rp_R5a_go.
    { eapply step_bne_ft with (rs1 := 11%bv) (rs2 := 0%bv) (imm := Z_to_bv 13 680); rp_R5a_auto.
      rp_R5a_norm. rewrite rp_R5a_ceq by lia. apply Z.eqb_eq. exact S0. }
    rp_R5a_mdnext HmK. rp_R5a_norm.
    apply (K140 _ _ _ eq_refl); [rp_R5a_rs | exact HmK | exact E32 | rp_R5a_norm; reflexivity].
  - eapply rp_R5a_go.
    { eapply step_bne_tk with (rs1 := 11%bv) (rs2 := 0%bv) (imm := Z_to_bv 13 680); rp_R5a_auto.
      rp_R5a_norm. rewrite rp_R5a_ceq by lia. apply Z.eqb_neq. exact SN. }
    rp_R5a_mdnext HmK. rp_R5a_norm.
    eapply rp_R5a_go; [eapply step_andi with (rd := 12%bv) (rs := 10%bv) (imm := 7%bv); rp_R5a_auto |].
    rp_R5a_mdnext HmK. rp_R5a_norm. rewrite rp_R5a_vandi7 by lia.
    eapply rp_R5a_go.
    { eapply step_blt_tk with (rs1 := 12%bv) (rs2 := 11%bv) (imm := Z_to_bv 13 (-680)); rp_R5a_auto.
      rp_R5a_norm. rewrite rp_R5a_clts by (pose proof (Z.mod_pos_bound (rc_fr cx + 33) 8 ltac:(lia)); lia).
      apply Z.ltb_lt. unfold saddr_ok in Hok. lia. }
    rp_R5a_mdnext HmK. rp_R5a_norm.
    apply (K140 _ _ _ eq_refl); [rp_R5a_rs | exact HmK | exact E32 | rp_R5a_norm; reflexivity]. }
(* 0x84120 .. 0x84128: fr[32] = 0x12 *)
assert (K120 : forall regs pc md', pc = Z_to_bv 64 0x84120 -> rp_R5a_RS cx pos regs ->
  same_but_materialized md3 md' -> getr regs 10 = Z_to_bv 64 (rc_fr cx + 32) ->
  SRr SEGS W3 (mkCfg (mkst regs pc mem3 (seg_rom SEGS)) md') (rp_post cx)).
{ intros regs pc md' -> RS Hm0 A10. clear HmK. rename Hm0 into HmK.
  eapply rp_R5a_go.
  { eapply step_lbu with (rd := 10%bv) (rs := 10%bv) (imm := 0%bv) (b := cp_b (rc_g cx) 32); rp_R5a_auto.
    rp_R5a_norm. rewrite A10. rp_R5a_norm. apply rp_R5a_rd1. rewrite Z.add_0_r. exact (MB 32%nat ltac:(lia)). }
  rp_R5a_mdnext HmK. rp_R5a_norm. change (bv_unsigned (cp_b (rc_g cx) 32)) with (cp_v (rc_g cx) 32).
  eapply rp_R5a_go; [eapply step_addi with (rd := 11%bv) (rs := 0%bv) (imm := 18%bv); rp_R5a_auto |].
  rp_R5a_mdnext HmK. rp_R5a_norm.
  destruct (Z.eqb_spec (cp_v (rc_g cx) 32) 0x12) as [E32|N32].
  - eapply rp_R5a_go.
    { eapply step_bne_ft with (rs1 := 10%bv) (rs2 := 11%bv) (imm := Z_to_bv 13 220); rp_R5a_auto.
      rp_R5a_norm. rewrite rp_R5a_ceq by lia. apply Z.eqb_eq. exact E32. }
    rp_R5a_mdnext HmK. rp_R5a_norm.
    apply (K12c _ _ _ eq_refl); [rp_R5a_rs | exact HmK | exact E32].
  - eapply rp_R5a_go.
    { eapply step_bne_tk with (rs1 := 10%bv) (rs2 := 11%bv) (imm := Z_to_bv 13 220); rp_R5a_auto.
      rp_R5a_norm. rewrite rp_R5a_ceq by lia. apply Z.eqb_neq. exact N32. }
    rp_R5a_mdnext HmK. rp_R5a_norm.
    apply (KF _ _ _ eq_refl); [rp_R5a_rs | exact HmK | apply rp_R5a_irF; intros; lia]. }
(* 0x8410c .. 0x8411c (slow path 0x843d8 / 0x843dc): the shadow check of fr+32 *)
assert (K10c : forall regs pc md', pc = Z_to_bv 64 0x8410c -> rp_R5a_RS cx pos regs ->
  same_but_materialized md3 md' -> SRr SEGS W3 (mkCfg (mkst regs pc mem3 (seg_rom SEGS)) md') (rp_post cx)).
{ intros regs pc md' -> RS Hm0. clear HmK. rename Hm0 into HmK.
  pose proof RS as ((_ & _ & _ & _ & _ & _ & _ & _ & R22 & _ & R27) & _ & _). unfold w64 in R22, R27.
  destruct (SH (rc_fr cx + 32) ltac:(lia)) as (bs & Hbs & Hok).
  assert (Hs8 : 0 <= bv_unsigned bs < 8) by (pose proof (u8_range bs); unfold saddr_ok in Hok; lia).
  eapply rp_R5a_go; [eapply step_addi with (rd := 10%bv) (rs := 22%bv) (imm := 32%bv); rp_R5a_auto |].
  rp_R5a_mdnext HmK. rp_R5a_norm. rewrite R22. rp_R5a_norm.
  eapply rp_R5a_go; [eapply step_srli with (rd := 11%bv) (rs := 10%bv) (sh := 3%bv); rp_R5a_auto |].
  rp_R5a_mdnext HmK. rp_R5a_norm. rewrite rp_R5a_vsrli3 by lia.
  eapply rp_R5a_go; [eapply step_add with (rd := 11%bv) (rs1 := 11%bv) (rs2 := 27%bv); rp_R5a_auto |].
  rp_R5a_mdnext HmK. rp_R5a_norm. rewrite R27. rp_R5a_norm.
  eapply rp_R5a_go.
  { eapply step_lb with (rd := 11%bv) (rs := 11%bv) (imm := 0%bv) (b := bs); rp_R5a_auto.
    rp_R5a_norm. apply rp_R5a_rd1.
    replace ((rc_fr cx + 32) / 8 + SHADOW_OFF + 0) with (shadow_of_addr SHADOW_OFF (rc_fr cx + 32))
      by (unfold shadow_of_addr; lia). exact Hbs. }
  rp_R5a_mdnext HmK. rp_R5a_norm. rewrite (rp_R5a_lbv bs) by lia.
  destruct (Z.eqb_spec (bv_unsigned bs) 0) as [S0|SN].
  - eapply rp_R5a_go.
    { eapply step_bne_ft with (rs1 := 11%bv) (rs2 := 0%bv) (imm := Z_to_bv 13 700); rp_R5a_auto.
      rp_R5a_norm. rewrite rp_R5a_ceq by lia. apply Z.eqb_eq. exact S0. }
    rp_R5a_mdnext HmK. rp_R5a_norm.
    apply (K120 _ _ _ eq_refl); [rp_R5a_rs | exact HmK | rp_R5a_norm; reflexivity].
  - eapply rp_R5a_go.
    { eapply step_bne_tk with (rs1 := 11%bv) (rs2 := 0%bv) (imm := Z_to_bv 13 700); rp_R5a_auto.
      rp_R5a_norm. rewrite rp_R5a_ceq by lia. apply Z.eqb_neq. exact SN. }
    rp_R5a_mdnext HmK. rp_R5a_norm.
    eapply rp_R5a_go; [eapply step_andi with (rd := 12%bv) (rs := 10%bv) (imm := 7%bv); rp_R5a_auto |].
    rp_R5a_mdnext HmK. rp_R5a_norm. rewrite rp_R5a_vandi7 by lia.
    eapply rp_R5a_go.
    { eapply step_blt_tk with (rs1 := 12%bv) (rs2 := 11%bv) (imm := Z_to_bv 13 (-700)); rp_R5a_auto.
      rp_R5a_norm. rewrite rp_R5a_clts by (pose proof (Z.mod_pos_bound (rc_fr cx + 32) 8 ltac:(lia)); lia).
      apply Z.ltb_lt. unfold saddr_ok in Hok. lia. }
    rp_R5a_mdnext HmK. rp_R5a_norm.
    apply (K120 _ _ _ eq_refl); [rp_R5a_rs | exact HmK | rp_R5a_norm; reflexivity]. }
(* 0x84108 not taken: on to the fr+32 check *)
eapply rp_R5a_go.
{ eapply step_bne_ft with (rs1 := 10%bv) (rs2 := 11%bv) (imm := Z_to_bv 13 252); rp_R5a_auto.
  rp_R5a_norm. rewrite rp_R5a_ceq by lia. apply Z.eqb_eq. lia. }
rp_R5a_mdnext HmK. rp_R5a_norm.
apply (K10c _ _ _ eq_refl); [rp_R5a_rs | exact HmK].
Qed.

(* LOCAL helpers of this stretch, named rp_R5b_kept_any / rp_R5b_carry_any / rp_R5b_frame_eq. *)
Lemma rp_R5b_kept_any : forall (cx : rcx) (W3 : world SEGS) (mem3 : word -> option byte) (E : Z -> Prop),
rp_kept cx W3 mem3 rp_Enone -> rp_kept cx W3 mem3 E.
Proof.
intros cx W3 mem3 E (Hw & K1 & K2 & K3 & K4 & K5 & K6).
split; [exact Hw|]. unfold tcj_kept.
split; [intros a H1 H2 _; exact (K1 a H1 H2 ltac:(unfold rp_Enone; intros []))|].
split; [intros b m i H1 H2 _; exact (K2 b m i H1 H2 ltac:(unfold rp_Enone; intros []))|].
split; [exact K3|].
split; [intros cid q a H1 H2 _; exact (K4 cid q a H1 H2 ltac:(unfold rp_Enone; intros []))|].
split; [exact K5 | exact K6].
Qed.

Lemma rp_R5b_carry_any : forall (cx : rcx) (regs3 : bvmap 5 word) (W3 : world SEGS)
(mem3 : word -> option byte) (E : Z -> Prop),
rp_carry cx regs3 W3 mem3 rp_Enone -> rp_carry cx regs3 W3 mem3 E.
Proof.
intros cx regs3 W3 mem3 E (H1 & H2 & H3 & H4 & H5 & H6).
split; [exact H1|]. split; [exact (rp_R5b_kept_any cx W3 mem3 E H2)|].
split; [exact H3|]. split; [exact H4|]. split; [exact H5 | exact H6].
Qed.

Lemma rp_R5b_frame_eq : forall (Ev : env) (rs : smem) (m m' : word -> option byte),
(forall r : YP09.region, In r rs -> YP09.r_whi r <= YP09.r_wlo r) ->
frame_of Ev rs m m' -> forall x : word, m' x = m x.
Proof.
intros Ev rs m m' Hro HF x. apply HF. intros (r & Hin & Hr).
pose proof (Hro r Hin). unfold base_val in Hr. lia.
Qed.

(* R5b  C7 -> C8 or C11, 0x84170..0x841c0 (+0x1e4..+0x234). fr[27] = 0xf0 and fr[26+s] = 0xf7 (the second
   address is concrete per case of s; split on s in [14, 23] right after C7), then the loop setup
   a3 := 0, a4 := 32, a0 := a2 := fr+18, which is C8 at i = 0.
   Donors: as R5a. Difficulty: medium. *)
Lemma rp_R5b : rp_from_C8 -> rp_from_C11 -> rp_from_C7.
Proof.
intros F8 F11 cx pos regs3 ly3 S3 W3 mem3 md3 HB HC7.
pose proof (paj_run_to B LAWS) as RUNTO.
pose proof (paj_branch (PI := CtrlImg.PI_ctrl)) as BR.
destruct HC7 as (HJH & HCar & HFR & HFP & HFW & HSH & Hargs & Htags & H11).
pose proof HJH as (HJ & HLY & HFRM & HNIN & HABL & HCNT).
pose proof HCar as (HRG & HKEPT & HSAV & HMSG & HOUT & HROD).
pose proof Htags as (Hlen50 & Hkind & Hu16 & Hg32 & Hg33 & Hsrange).
pose proof HRG as (G2 & G3 & G4 & G8 & G9 & G19 & G20 & G21 & G22 & G23 & G27).
destruct (HMSG Hargs Hlen50) as (HARR & HSRC).
pose proof HSRC as (HVIS & HRA50 & HHULL & HAMEM & HQ0 & HQ63).
assert (HLG : length (rc_g cx) = 50%nat) by (clear - HB; unfold rp_base in HB; tauto).
assert (HFR64 : 0 <= rc_fr cx < 2 ^ 64) by (clear - HB; unfold rp_base in HB; tauto).
assert (HFRB : 0 <= rc_fr cx <= 140737488355277)
by (clear - HAMEM HQ0; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HAMEM; lia).
assert (HAPART : forall x, rc_fr cx <= x < rc_fr cx + 50 -> ~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416))
by (clear - HAMEM; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF in *; lia).
assert (HBZ : forall i, 0 <= i < 50 ->
val_mem SEGS (mrestrict (w_H W3) mem3) (rc_fr cx + i) 1 (cp_v (rc_g cx) (Z.to_nat i)) /\
0 <= cp_v (rc_g cx) (Z.to_nat i) < 256).
{ intros i Hi.
assert (Hj : (Z.to_nat i < length (map bv_unsigned (rc_g cx)))%nat)
by (rewrite length_map, HLG; lia).
pose proof (HARR (Z.to_nat i) Hj) as HN.
replace (nth (Z.to_nat i) (map bv_unsigned (rc_g cx)) 0) with (cp_v (rc_g cx) (Z.to_nat i)) in HN.
2:{ unfold cp_v, cp_b. change 0 with (bv_unsigned cp_z). symmetry. apply map_nth. }
rewrite Z2Nat.id in HN by lia. exact HN. }
assert (Hcase : rp_s cx = 14 \/ rp_s cx = 15 \/ rp_s cx = 16 \/ rp_s cx = 17 \/ rp_s cx = 18 \/
rp_s cx = 19 \/ rp_s cx = 20 \/ rp_s cx = 21 \/ rp_s cx = 22 \/ rp_s cx = 23)
by (clear - Hsrange; lia).
destruct Hcase as [Hs|[Hs|[Hs|[Hs|[Hs|[Hs|[Hs|[Hs|[Hs|Hs]]]]]]]]].
all: lazymatch goal with Hs : rp_s _ = ?sv |- _ =>
let R5BMEM := idtac; (
repeat (lazymatch goal with
| HFx : frame_of ?Ev ?rs ?m ?m' |- _ =>
let Hq := fresh "Hq" in
assert (Hq : m' = m) by
(apply FunctionalExtensionality.functional_extensionality;
apply (rp_R5b_frame_eq Ev rs m m');
[ intros rr Hrr; cbn [In] in Hrr; destruct Hrr as [Hrr|[]];
rewrite <- Hrr; cbn [YP09.r_whi YP09.r_wlo]; lia
| exact HFx ]);
try (rewrite Hq in * ); clear Hq HFx
end)) in
let R5BREGS := idtac; (
prreg HS (2%bv : bv 5) Q2; rewrite (ER 2%nat 2%bv ltac:(lia) eq_refl) in Q2;
prreg HS (3%bv : bv 5) Q3; rewrite (ER 3%nat 3%bv ltac:(lia) eq_refl) in Q3;
prreg HS (4%bv : bv 5) Q4; rewrite (ER 4%nat 4%bv ltac:(lia) eq_refl) in Q4;
prreg HS (8%bv : bv 5) Q8; rewrite (ER 8%nat 8%bv ltac:(lia) eq_refl) in Q8;
prreg HS (9%bv : bv 5) Q9; rewrite (ER 9%nat 9%bv ltac:(lia) eq_refl) in Q9;
prreg HS (18%bv : bv 5) Q18; rewrite (ER 18%nat 18%bv ltac:(lia) eq_refl) in Q18;
prreg HS (19%bv : bv 5) Q19; rewrite (ER 19%nat 19%bv ltac:(lia) eq_refl) in Q19;
prreg HS (20%bv : bv 5) Q20; rewrite (ER 20%nat 20%bv ltac:(lia) eq_refl) in Q20;
prreg HS (21%bv : bv 5) Q21; rewrite (ER 21%nat 21%bv ltac:(lia) eq_refl) in Q21;
prreg HS (22%bv : bv 5) Q22; rewrite (ER 22%nat 22%bv ltac:(lia) eq_refl) in Q22;
prreg HS (23%bv : bv 5) Q23; rewrite (ER 23%nat 23%bv ltac:(lia) eq_refl) in Q23;
prreg HS (25%bv : bv 5) Q25; rewrite (ER 25%nat 25%bv ltac:(lia) eq_refl) in Q25;
prreg HS (26%bv : bv 5) Q26; rewrite (ER 26%nat 26%bv ltac:(lia) eq_refl) in Q26;
prreg HS (27%bv : bv 5) Q27; rewrite (ER 27%nat 27%bv ltac:(lia) eq_refl) in Q27) in
let R5BJHOLD := idtac; (unfold rp_jhold;
split; [exact HJ|]; split; [exact HLY|]; split; [exact HFRM|];
split; [exact HNIN|]; split; [exact HABL|]; exact HCNT) in
let R5BCARRY := idtac; (unfold rp_carry;
split; [ unfold rp_regs_ok;
split; [rewrite Q2; exact G2|]; split; [rewrite Q3; exact G3|];
split; [rewrite Q4; exact G4|]; split; [rewrite Q8; exact G8|];
split; [rewrite Q9; exact G9|]; split; [rewrite Q19; exact G19|];
split; [rewrite Q20; exact G20|]; split; [rewrite Q21; exact G21|];
split; [rewrite Q22; exact G22|]; split; [rewrite Q23; exact G23|];
rewrite Q27; exact G27 |];
split; [exact HKEPT|]; split; [exact HSAV|]; split; [exact HMSG|];
split; [exact HOUT | exact HROD]) in
let R5BFREGS := idtac; (unfold rp_fregs;
split; [rewrite Q18; exact (proj1 HFR)|];
split; [rewrite Q26; exact (proj1 (proj2 HFR))|];
rewrite Q25; exact (proj2 (proj2 HFR))) in
let R5BFAIL := idtac; (
assert (ERET : rp_ret cx = 0) by
(unfold rp_ret, reply_ret; unfold rp_argsb in Hargs; rewrite Hargs, EIR; reflexivity);
assert (EOKB : rp_okb cx = false) by
(unfold rp_okb, reply_ok; unfold rp_argsb in Hargs; rewrite Hargs, EIR; reflexivity);
paj_run_to_tok RUNTO HS HJ SHOK (SHADOW_OFF, SHADOW_OFF + 17592186044415)
(AF_reac_ctrl_identity_reply + 0x27c);
[ apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo]; lia | apply awr_ok_nil] | ];
pmkst HS; R5BMEM; R5BREGS; prreg HS (10%bv : bv 5) Q10;
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ ?p _ _) _) _ =>
replace p with (w64 (rp_pc 0x27c)) by
(unfold w64, rp_pc, A_reac_ctrl_identity_replyP; f_equal;
unfold AF_reac_ctrl_identity_reply; lia) end;
apply (F11 cx pos _ ly3 S3 W3 mem3 _ HB);
unfold rp_C11;
split; [ R5BJHOLD |];
split; [ apply (rp_R5b_carry_any cx _ W3 mem3 (rp_Eout cx)); R5BCARRY |];
split; [ R5BFREGS |];
split; [ exact HFP |]; split; [ exact HFW |]; split; [ exact HSH |];
split; [ exact Hargs |];
split; [ rewrite ERET, Q10; reflexivity |];
intros Hk; rewrite EOKB in Hk; discriminate) in
(* the two message bytes this stretch reads: fr[27] and fr[26 + s] *)
destruct (HBZ 27 ltac:(lia)) as [V27 R27v];
destruct (HBZ (26 + sv) ltac:(lia)) as [V8 R8v];
change (Z.to_nat 27) with 27%nat in V27, R27v;
(* the symbolic entry state at +0x1e4 *)
pose proof (Eimg_env (Ereg regs3 [w64 (cp_v (rc_g cx) 27);
w64 (cp_v (rc_g cx) (Z.to_nat (26 + sv)))])) as HEI;
set (E := Eimg (Ereg regs3 [w64 (cp_v (rc_g cx) 27); w64 (cp_v (rc_g cx) (Z.to_nat (26 + sv)))])) in HEI |- *;
assert (EL : forall n, (n < A_TEXT)%nat ->
ew E n = ew (Ereg regs3 [w64 (cp_v (rc_g cx) 27); w64 (cp_v (rc_g cx) (Z.to_nat (26 + sv)))]) n)
by (intros n Hn; subst E; apply Eimg_low; exact Hn);
assert (E22 : ew E 22 = w64 (rc_fr cx))
by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs3 _ 22 22%bv eq_refl); exact G22);
assert (E27 : ew E 27 = w64 SHADOW_OFF)
by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs3 _ 27 27%bv eq_refl); exact G27);
assert (E11 : ew E 11 = w64 sv)
by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs3 _ 11 11%bv eq_refl);
rewrite H11, Hs; reflexivity);
assert (E32 : ew E 32 = w64 (cp_v (rc_g cx) 27))
by (rewrite EL by (unfold A_TEXT; lia); replace 32%nat with (32 + 0)%nat by lia;
rewrite ew_Ereg_extra; reflexivity);
assert (E33 : ew E 33 = w64 (cp_v (rc_g cx) (Z.to_nat (26 + sv))))
by (rewrite EL by (unfold A_TEXT; lia); replace 33%nat with (32 + 1)%nat by lia;
rewrite ew_Ereg_extra; reflexivity);
assert (ER : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r ->
ew E n = getr regs3 r)
by (intros n r Hn Hnr; rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hnr);
assert (HS0 : st_ok_pi SEGS VAL E
(mkSS (AF_reac_ctrl_identity_reply + 0x1e4) sr_atoms
[YP09.mkRegion (Some 22%nat) 0 50 0 0
[YP09.mkChunk 27 (CVal 1 (SOff 32 0)); YP09.mkChunk (26 + sv) (CVal 1 (SOff 33 0))]]
None
(mkFacts [(22%nat, mkAF 0 140737488355277 0); (27%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
(32%nat, mkAF 0 255 0); (33%nat, mkAF 0 255 0)] [] []))
(restrict (w_H W3) (mkst regs3 (w64 (rp_pc 0x1e4)) mem3 (seg_rom SEGS))));
[ replace (w64 (rp_pc 0x1e4)) with (Z_to_bv 64 (BASE + (AF_reac_ctrl_identity_reply + 0x1e4)))
by (unfold w64, rp_pc, A_reac_ctrl_identity_replyP; f_equal; lia);
rewrite restrict_mkst_fx;
apply (pa_entry_st_ok_full (PI := CtrlImg.PI_ctrl));
[ apply regs_ok_Eimg_Ereg
| vm_compute; reflexivity
| apply Forall_cons; [|apply Forall_nil];
unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
rewrite E22; unfold w64; rewrite unsigned_lit_small by lia;
split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
[ apply (chunk_ok_val SEGS E _ (rc_fr cx) 27 1 (SOff 32 0) (cp_v (rc_g cx) 27));
[ cbn [sv_denot]; rewrite E32; unfold w64; rewrite unsigned_lit_small by lia;
rewrite Z.add_0_r; reflexivity | zside | zside | exact V27 ]
| apply (chunk_ok_val SEGS E _ (rc_fr cx) (26 + sv) 1 (SOff 33 0)
(cp_v (rc_g cx) (Z.to_nat (26 + sv))));
[ cbn [sv_denot]; rewrite E33; unfold w64; rewrite unsigned_lit_small by lia;
rewrite Z.add_0_r; reflexivity | zside | zside | exact V8 ] ]
| cbn [pairwise_disjoint all_disjoint]; tauto
| split; [|split; [exact I | exact I]];
cbn [f_atoms atoms_ok];
split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E22; unfold w64;
rewrite unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia|];
split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E27; unfold w64;
rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia); rewrite Z.pow_0_r, Z.mod_1_r;
unfold SHADOW_OFF; lia|];
split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E32; unfold w64;
rewrite unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia|];
split; [|exact I];
unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E33; unfold w64;
rewrite unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia ]
| idtac ];
pose proof (st_ok_pi_pin_reg' E _ _ 11%bv sv HS0
ltac:(cbn [ms_regs restrict mkst]; rewrite H11, Hs; unfold w64; reflexivity) eq_refl) as HS;
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS;
clear HS0;
assert (SHOK : sh_ok SEGS (SOff 27 0) [mkSHE 22 0 50] E (mrestrict (w_H W3) mem3));
[ apply Forall_cons; [|apply Forall_nil];
apply (shent_ok_of_range SEGS (w_H W3) mem3 E (SOff 27 0) 22 (rc_fr cx) 50 (rc_fr cx) 0 50 HRA50);
[ exact (U_atom E 27 SHADOW_OFF E27 ltac:(unfold SHADOW_OFF; lia))
| exact (U_atom E 22 (rc_fr cx) E22 ltac:(lia)) | lia | lia
| intros x Hx; apply HAPART; lia ]
| idtac ];
unfold cfg_at;
paj_run_to_tok RUNTO HS HJ SHOK (SHADOW_OFF, SHADOW_OFF + 17592186044415)
(AF_reac_ctrl_identity_reply + 0x238);
[ apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo]; lia | apply awr_ok_nil] | ];
psrr_branch_tok RUNTO BR HS SHOK (SHADOW_OFF, SHADOW_OFF + 17592186044415);
[ rewrite ?branch_eq_U, ?branch_ne_U in Hc;
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
rewrite (U_atom Ev 32 (cp_v (rc_g cx) 27)
ltac:(rewrite ?ew_ewset_other by lia; exact E32) ltac:(lia)) in Hc end;
rewrite U_lit in Hc by lia;
apply (proj1 (negb_true_iff _)) in Hc; apply (proj1 (Z.eqb_neq _ _)) in Hc;
assert (EIR : ir (rc_len cx) (rc_g cx) = false);
[ destruct (ir (rc_len cx) (rc_g cx)) eqn:EE; [|reflexivity];
exfalso; apply ir_true in EE;
destruct EE as (_ & _ & _ & _ & _ & H27f & _ & _ & _); clear - Hc H27f; lia | ];
R5BFAIL
| rewrite ?branch_eq_U, ?branch_ne_U in Hc;
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
rewrite (U_atom Ev 32 (cp_v (rc_g cx) 27)
ltac:(rewrite ?ew_ewset_other by lia; exact E32) ltac:(lia)) in Hc end;
rewrite U_lit in Hc by lia;
apply (proj1 (negb_false_iff _)) in Hc; apply (proj1 (Z.eqb_eq _ _)) in Hc;
assert (Hg27 : cp_v (rc_g cx) 27 = 0xf0) by (clear - Hc; lia);
clear Hc;
paj_run_to_tok RUNTO HS HJ SHOK (SHADOW_OFF, SHADOW_OFF + 17592186044415)
(AF_reac_ctrl_identity_reply + 0x238);
[ apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo]; lia | apply awr_ok_nil] | ];
psrr_branch_tok RUNTO BR HS SHOK (SHADOW_OFF, SHADOW_OFF + 17592186044415);
[ rewrite ?branch_eq_U, ?branch_ne_U in Hc;
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
rewrite (U_atom Ev 33 (cp_v (rc_g cx) (Z.to_nat (26 + sv)))
ltac:(rewrite ?ew_ewset_other by lia; exact E33) ltac:(lia)) in Hc end;
rewrite U_lit in Hc by lia;
apply (proj1 (negb_true_iff _)) in Hc; apply (proj1 (Z.eqb_neq _ _)) in Hc;
assert (EIR : ir (rc_len cx) (rc_g cx) = false);
[ destruct (ir (rc_len cx) (rc_g cx)) eqn:EE; [|reflexivity];
exfalso; apply ir_true in EE;
destruct EE as (_ & _ & _ & _ & _ & _ & Hf7f & _ & _);
change (ir_s (rc_g cx)) with (rp_s cx) in Hf7f; rewrite Hs in Hf7f;
clear - Hc Hf7f; lia | ];
R5BFAIL
| rewrite ?branch_eq_U, ?branch_ne_U in Hc;
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
rewrite (U_atom Ev 33 (cp_v (rc_g cx) (Z.to_nat (26 + sv)))
ltac:(rewrite ?ew_ewset_other by lia; exact E33) ltac:(lia)) in Hc end;
rewrite U_lit in Hc by lia;
apply (proj1 (negb_false_iff _)) in Hc; apply (proj1 (Z.eqb_eq _ _)) in Hc;
assert (Hgf7 : cp_v (rc_g cx) (Z.to_nat (26 + sv)) = 0xf7) by (clear - Hc; lia);
clear Hc;
paj_run_to_tok RUNTO HS HJ SHOK (SHADOW_OFF, SHADOW_OFF + 17592186044415)
(AF_reac_ctrl_identity_reply + 0x238);
[ apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo]; lia | apply awr_ok_nil] | ];
pmkst HS;
R5BMEM;
R5BREGS;
prreg HS (10%bv : bv 5) Q10; prreg HS (11%bv : bv 5) Q11;
prreg HS (12%bv : bv 5) Q12; prreg HS (13%bv : bv 5) Q13;
prreg HS (14%bv : bv 5) Q14;
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ ?p _ _) _) _ =>
replace p with (w64 (rp_pc 0x238)) by
(unfold w64, rp_pc, A_reac_ctrl_identity_replyP; f_equal;
unfold AF_reac_ctrl_identity_reply; lia) end;
apply (F8 cx pos 0 _ ly3 S3 W3 mem3 _ HB);
unfold rp_C8;
split; [ R5BJHOLD |];
split; [ R5BCARRY |];
split; [ R5BFREGS |];
split; [ exact HFP |]; split; [ exact HFW |]; split; [ exact HSH |];
split; [ exact Hargs |];
split; [ split; [exact Htags|]; split; [exact Hg27|]; rewrite Hs; exact Hgf7 |];
split; [ rewrite Q11, Hs; unfold w64; reflexivity |];
split; [ lia |];
split; [ rewrite Q10, E22; unfold w64; rewrite unsigned_lit_small by lia;
f_equal; lia |];
split; [ rewrite Q12, E22; unfold w64; rewrite unsigned_lit_small by lia;
f_equal; lia |];
split; [ rewrite Q13; unfold w64; f_equal; cbn [Z.to_nat psum]; reflexivity
| rewrite Q14; unfold w64; f_equal; lia ] ] ]
end.
Qed.

(* ---- rp_R6's local helpers: the loop 0x841c4..0x84204 walked on the concrete machine state (YK11 / YK14
   step lemmas, SRr_msteps), the code words from the code table CtrlImg.ctrltbl. ---- *)
Lemma rp_R6_F : forall pc w, clookup CtrlImg.ctrltbl pc = Some w -> fetch_word SEGS (w64 pc) = Some (Z_to_bv 32 w).
Proof. exact CtrlImg.ctrltbl_ok. Qed.
Lemma rp_R6_F1c4 : fetch_word SEGS (w64 0x841c4) = Some (Z_to_bv 32 0x00355793). Proof. apply rp_R6_F; vm_compute; reflexivity. Qed.
Lemma rp_R6_F1c8 : fetch_word SEGS (w64 0x841c8) = Some (Z_to_bv 32 0x01b787b3). Proof. apply rp_R6_F; vm_compute; reflexivity. Qed.
Lemma rp_R6_F1cc : fetch_word SEGS (w64 0x841cc) = Some (Z_to_bv 32 0x00078783). Proof. apply rp_R6_F; vm_compute; reflexivity. Qed.
Lemma rp_R6_F1d0 : fetch_word SEGS (w64 0x841d0) = Some (Z_to_bv 32 0x02079063). Proof. apply rp_R6_F; vm_compute; reflexivity. Qed.
Lemma rp_R6_F1d4 : fetch_word SEGS (w64 0x841d4) = Some (Z_to_bv 32 0x00064783). Proof. apply rp_R6_F; vm_compute; reflexivity. Qed.
Lemma rp_R6_F1d8 : fetch_word SEGS (w64 0x841d8) = Some (Z_to_bv 32 0xfff70713). Proof. apply rp_R6_F; vm_compute; reflexivity. Qed.
Lemma rp_R6_F1dc : fetch_word SEGS (w64 0x841dc) = Some (Z_to_bv 32 0x00150513). Proof. apply rp_R6_F; vm_compute; reflexivity. Qed.
Lemma rp_R6_F1e0 : fetch_word SEGS (w64 0x841e0) = Some (Z_to_bv 32 0x00f686b3). Proof. apply rp_R6_F; vm_compute; reflexivity. Qed.
Lemma rp_R6_F1e4 : fetch_word SEGS (w64 0x841e4) = Some (Z_to_bv 32 0x00160613). Proof. apply rp_R6_F; vm_compute; reflexivity. Qed.
Lemma rp_R6_F1e8 : fetch_word SEGS (w64 0x841e8) = Some (Z_to_bv 32 0xfc071ee3). Proof. apply rp_R6_F; vm_compute; reflexivity. Qed.
Lemma rp_R6_F1ec : fetch_word SEGS (w64 0x841ec) = Some (Z_to_bv 32 0x0100006f). Proof. apply rp_R6_F; vm_compute; reflexivity. Qed.
Lemma rp_R6_F1f0 : fetch_word SEGS (w64 0x841f0) = Some (Z_to_bv 32 0x00757813). Proof. apply rp_R6_F; vm_compute; reflexivity. Qed.
Lemma rp_R6_F1f4 : fetch_word SEGS (w64 0x841f4) = Some (Z_to_bv 32 0xfef840e3). Proof. apply rp_R6_F; vm_compute; reflexivity. Qed.
Lemma rp_R6_F1fc : fetch_word SEGS (w64 0x841fc) = Some (Z_to_bv 32 0x0ff6f513). Proof. apply rp_R6_F; vm_compute; reflexivity. Qed.
Lemma rp_R6_F200 : fetch_word SEGS (w64 0x84200) = Some (Z_to_bv 32 0x10050063). Proof. apply rp_R6_F; vm_compute; reflexivity. Qed.
Lemma rp_R6_F204 : fetch_word SEGS (w64 0x84204) = Some (Z_to_bv 32 0x00000513). Proof. apply rp_R6_F; vm_compute; reflexivity. Qed.
Lemma rp_R6_D1c4 : decode_any (Z_to_bv 32 0x00355793) = Some (ShiftImm ALU_SRL 15 10 3, 4%Z). Proof. vm_refl_bv. Qed.
Lemma rp_R6_D1c8 : decode_any (Z_to_bv 32 0x01b787b3) = Some (Op ALU_ADD 15 15 27, 4%Z). Proof. vm_refl_bv. Qed.
Lemma rp_R6_D1cc : decode_any (Z_to_bv 32 0x00078783) = Some (Load SZ1 true 15 15 0, 4%Z). Proof. vm_refl_bv. Qed.
Lemma rp_R6_D1d0 : decode_any (Z_to_bv 32 0x02079063) = Some (Branch BC_NE 15 0 32, 4%Z). Proof. vm_refl_bv. Qed.
Lemma rp_R6_D1d4 : decode_any (Z_to_bv 32 0x00064783) = Some (Load SZ1 false 15 12 0, 4%Z). Proof. vm_refl_bv. Qed.
Lemma rp_R6_D1d8 : decode_any (Z_to_bv 32 0xfff70713) = Some (OpImm ALU_ADD 14 14 4095, 4%Z). Proof. vm_refl_bv. Qed.
Lemma rp_R6_D1dc : decode_any (Z_to_bv 32 0x00150513) = Some (OpImm ALU_ADD 10 10 1, 4%Z). Proof. vm_refl_bv. Qed.
Lemma rp_R6_D1e0 : decode_any (Z_to_bv 32 0x00f686b3) = Some (Op ALU_ADD 13 13 15, 4%Z). Proof. vm_refl_bv. Qed.
Lemma rp_R6_D1e4 : decode_any (Z_to_bv 32 0x00160613) = Some (OpImm ALU_ADD 12 12 1, 4%Z). Proof. vm_refl_bv. Qed.
Lemma rp_R6_D1e8 : decode_any (Z_to_bv 32 0xfc071ee3) = Some (Branch BC_NE 14 0 8156, 4%Z). Proof. vm_refl_bv. Qed.
Lemma rp_R6_D1ec : decode_any (Z_to_bv 32 0x0100006f) = Some (Jal 0 16, 4%Z). Proof. vm_refl_bv. Qed.
Lemma rp_R6_D1f0 : decode_any (Z_to_bv 32 0x00757813) = Some (OpImm ALU_AND 16 10 7, 4%Z). Proof. vm_refl_bv. Qed.
Lemma rp_R6_D1f4 : decode_any (Z_to_bv 32 0xfef840e3) = Some (Branch BC_LT 16 15 8160, 4%Z). Proof. vm_refl_bv. Qed.
Lemma rp_R6_D1fc : decode_any (Z_to_bv 32 0x0ff6f513) = Some (OpImm ALU_AND 10 13 255, 4%Z). Proof. vm_refl_bv. Qed.
Lemma rp_R6_D200 : decode_any (Z_to_bv 32 0x10050063) = Some (Branch BC_EQ 10 0 256, 4%Z). Proof. vm_refl_bv. Qed.
Lemma rp_R6_D204 : decode_any (Z_to_bv 32 0x00000513) = Some (OpImm ALU_ADD 10 0 0, 4%Z). Proof. vm_refl_bv. Qed.
(* one step that keeps the registers / that writes one register, onto a numeral pc *)
Lemma rp_R6_ms : forall (R R' : bvmap 5 word) (pc pc' : Z) (pcw : word) (m : word -> option byte) t,
RiscvSemantics.step SEGS (mkst R (w64 pc) m (seg_rom SEGS)) = MachineOk (mkst R' pcw m (seg_rom SEGS)) ->
pcw = w64 pc' -> msteps SEGS (mkst R' (w64 pc') m (seg_rom SEGS)) t ->
msteps SEGS (mkst R (w64 pc) m (seg_rom SEGS)) t.
Proof. intros R R' pc pc' pcw m t H Hp Ht. subst pcw. eapply mst_step; [reflexivity | exact H | exact Ht]. Qed.
Lemma rp_R6_msv : forall (R R1 : bvmap 5 word) (rd : Prelude.reg) (v' : word) (pc pc' : Z) (pcw : word)
(m : word -> option byte) t,
RiscvSemantics.step SEGS (mkst R (w64 pc) m (seg_rom SEGS)) = MachineOk (mkst R1 pcw m (seg_rom SEGS)) ->
R1 = regupd R rd v' -> pcw = w64 pc' ->
msteps SEGS (mkst (regupd R rd v') (w64 pc') m (seg_rom SEGS)) t ->
msteps SEGS (mkst R (w64 pc) m (seg_rom SEGS)) t.
Proof.
intros R R1 rd v' pc pc' pcw m t H HR Hp Ht. subst R1 pcw.
eapply mst_step; [reflexivity | exact H | exact Ht].
Qed.
Local Ltac rp_R6_pc := apply bv_eq; vm_compute; reflexivity.
Local Ltac rp_R6_if := try (match goal with |- context [if ?c then _ else _] => replace c with false by reflexivity end; cbv iota); f_equal.
Local Ltac rp_R6_gres := repeat first [ rewrite getr_same by reg_neq_tac | rewrite getr_other by reg_neq_tac ].
(* the value facts of the run *)
Lemma rp_R6_srl3 : forall x, 0 <= x < 2 ^ 64 -> v_srli (Z_to_bv 64 x) 3 = Z_to_bv 64 (x / 8).
Proof. intros x Hx. unfold v_srli. rewrite unsigned_lit_small by lia. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.
Lemma rp_R6_add : forall a b, 0 <= a -> 0 <= b -> a + b < 2 ^ 64 -> v_add (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof. intros a b Ha Hb Hab. unfold v_add. rewrite !unsigned_lit_small by lia. reflexivity. Qed.
Lemma rp_R6_and7 : forall a, 0 <= a < 2 ^ 64 -> v_andi (Z_to_bv 64 a) 7 = Z_to_bv 64 (a mod 8).
Proof.
intros a Ha. unfold v_andi. rewrite unsigned_lit_small by lia. change (bv_wrap 64 7) with 7.
change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity.
Qed.
Lemma rp_R6_and255 : forall a, 0 <= a < 2 ^ 64 -> v_andi (Z_to_bv 64 a) 255 = Z_to_bv 64 (a mod 256).
Proof.
intros a Ha. unfold v_andi. rewrite unsigned_lit_small by lia. change (bv_wrap 64 255) with 255.
change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity.
Qed.
Lemma rp_R6_ceq : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> c_eq (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof. intros a b Ha Hb. unfold c_eq, bv_eqb. rewrite !unsigned_lit_small by lia. reflexivity. Qed.
Lemma rp_R6_lts : forall a b, 0 <= a < 2 ^ 63 -> 0 <= b < 2 ^ 63 -> c_lts (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof.
intros a b Ha Hb. unfold c_lts, bv_lts.
rewrite !lib.Reusable.YK11.bv_signed_small by (rewrite unsigned_lit_small by lia; lia).
rewrite !unsigned_lit_small by lia. reflexivity.
Qed.
Lemma rp_R6_lb : forall sh : byte, bv_unsigned sh < 128 -> v_lb sh = Z_to_bv 64 (bv_unsigned sh).
Proof.
intros sh H. unfold v_lb. f_equal. unfold bv_signed. apply bv_swrap_small.
pose proof (bv_unsigned_in_range 8 sh) as R. change (bv_half_modulus 8) with 128. lia.
Qed.
Lemma rp_R6_rdn1 : forall (m : word -> option byte) a b, mbyte SEGS m a = Some b -> 0 <= a < 2 ^ 64 ->
rdn SEGS m (v_addi (Z_to_bv 64 a) 0) 1 = Some [b].
Proof.
intros m a b H Ha. rewrite YCbn.v_addi_lit, Z.add_0_r.
apply (proj2 (rdn_mbytes SEGS m 1 a [b])). split; [reflexivity|].
intros k Hk. destruct k as [|k]; [|lia]. replace (a + Z.of_nat 0) with a by lia. exact H.
Qed.
Lemma rp_R6_byte : forall (g : list byte) (j : nat),
bv_unsigned (Z_to_bv 8 (le_byte (nth j (map bv_unsigned g) 0) 1 0)) = bv_unsigned (nth j g (Z_to_bv 8 0)).
Proof.
intros g j.
assert (E : nth j (map bv_unsigned g) 0 = bv_unsigned (nth j g (Z_to_bv 8 0)))
by exact (map_nth bv_unsigned g (Z_to_bv 8 0) j).
rewrite E. pose proof (bv_unsigned_in_range 8 (nth j g (Z_to_bv 8 0))) as R. unfold bv_modulus in R.
change (2 ^ Z.of_N 8) with 256 in R.
rewrite le_byte_small by first [lia | change (2 ^ (8 * Z.of_nat 1)) with 256; lia].
change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. lia.
Qed.
Lemma rp_R6_psum : forall (l : list byte) (k : nat), 0 <= psum l k <= 255 * Z.of_nat k.
Proof.
intros l k. induction k as [|k IH]; cbn [psum]; [lia|].
pose proof (bv_unsigned_in_range 8 (nth k l (Z_to_bv 8 0))) as R. unfold bv_modulus in R.
change (2 ^ Z.of_N 8) with 256 in R. lia.
Qed.
Lemma rp_R6_nth_skipn : forall (l : list byte) (n k : nat) (d : byte), nth k (skipn n l) d = nth (n + k) l d.
Proof.
intros l n. revert l. induction n as [|n IH]; intros l k d; [reflexivity|].
destruct l as [|a l]; cbn [skipn]; [destruct k; reflexivity|]. cbn [Nat.add nth]. apply IH.
Qed.
(* 0x841c4 .. 0x841d0, and the slow arm 0x841f0 .. 0x841f4: the shadow check of x (a5, a6 written) *)
Lemma rp_R6_chk : forall (m : word -> option byte) (R : bvmap 5 word) (x : Z) (sh : byte),
getr R 10 = w64 x -> getr R 27 = w64 SHADOW_OFF -> 0 <= x < 2 ^ 63 ->
mbyte SEGS m (SHADOW_OFF + x / 8) = Some sh -> saddr_ok x (bv_unsigned sh) ->
exists R1, msteps SEGS (mkst R (w64 0x841c4) m (seg_rom SEGS)) (mkst R1 (w64 0x841d4) m (seg_rom SEGS)) /\
(forall r : Prelude.reg, r <> 15%bv -> r <> 16%bv -> getr R1 r = getr R r).
Proof.
intros m R x sh H10 H27 Hx Hsh Hok.
pose proof (bv_unsigned_in_range 8 sh) as Hshr. unfold bv_modulus in Hshr. change (2 ^ Z.of_N 8) with 256 in Hshr.
assert (Hx8 : 0 <= x / 8 < 2 ^ 60) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
assert (Hs8 : bv_unsigned sh < 8) by (destruct Hok as [S0|[_ S8]]; lia).
set (R0 := regupd (regupd (regupd R 15%bv (w64 (x / 8))) 15%bv (w64 (SHADOW_OFF + x / 8))) 15%bv (w64 (bv_unsigned sh))).
assert (PRE : forall t, msteps SEGS (mkst R0 (w64 0x841d0) m (seg_rom SEGS)) t ->
  msteps SEGS (mkst R (w64 0x841c4) m (seg_rom SEGS)) t).
{ intros t Ht.
  eapply rp_R6_msv with (rd := 15%bv) (v' := w64 (x / 8)) (pc' := 0x841c8);
  [exact (lib.Reusable.YK11.step_srli SEGS _ (w64 0x841c4) m (seg_rom SEGS) _ _ _ _ rp_R6_F1c4 eq_refl rp_R6_D1c4) | rp_R6_if; rewrite H10; imm_norm; unfold w64; apply rp_R6_srl3; lia | rp_R6_pc |].
  eapply rp_R6_msv with (rd := 15%bv) (v' := w64 (SHADOW_OFF + x / 8)) (pc' := 0x841cc);
  [exact (lib.Reusable.YK11.step_add SEGS _ (w64 0x841c8) m (seg_rom SEGS) _ _ _ _ rp_R6_F1c8 eq_refl rp_R6_D1c8) | rp_R6_if; rp_R6_gres; rewrite H27; unfold w64; rewrite rp_R6_add by (unfold SHADOW_OFF; lia); f_equal; lia | rp_R6_pc |].
  eapply rp_R6_msv with (rd := 15%bv) (v' := w64 (bv_unsigned sh)) (pc' := 0x841d0);
  [eapply lib.Reusable.YK11.step_lb; [exact rp_R6_F1cc | reflexivity | exact rp_R6_D1cc |];
   rp_R6_gres; imm_norm; unfold w64; apply rp_R6_rdn1; [exact Hsh | unfold SHADOW_OFF; lia]
  | rp_R6_if; unfold w64; apply rp_R6_lb; lia | rp_R6_pc |].
  exact Ht. }
assert (G0 : forall r : Prelude.reg, r <> 15%bv -> getr R0 r = getr R r)
by (intros r Hr; unfold R0; rewrite !getr_other by exact Hr; reflexivity).
assert (R015 : getr R0 15 = w64 (bv_unsigned sh)) by (unfold R0; rp_R6_gres; reflexivity).
assert (R010 : getr R0 10 = w64 x) by (rewrite G0 by reg_neq_tac; exact H10).
destruct Hok as [S0|[Slt S8]].
- exists R0. split; [|intros r Hr15 Hr16; apply G0; exact Hr15].
  apply PRE.
  eapply (rp_R6_ms _ _ 0x841d0 0x841d4);
  [eapply lib.Reusable.YK11.step_bne_ft; [exact rp_R6_F1d0 | reflexivity | exact rp_R6_D1d0 |];
   rewrite R015, getr_zero, S0; reflexivity | rp_R6_pc |].
  apply mst_refl.
- exists (regupd R0 16%bv (w64 (x mod 8))).
  split; [|intros r Hr15 Hr16; rewrite getr_other by exact Hr16; apply G0; exact Hr15].
  apply PRE.
  eapply (rp_R6_ms _ _ 0x841d0 0x841f0);
  [eapply lib.Reusable.YK11.step_bne_tk; [exact rp_R6_F1d0 | reflexivity | exact rp_R6_D1d0 |];
   rewrite R015, getr_zero; unfold w64; rewrite rp_R6_ceq by lia; apply Z.eqb_neq; lia | rp_R6_pc |].
  eapply rp_R6_msv with (rd := 16%bv) (v' := w64 (x mod 8)) (pc' := 0x841f4);
  [exact (lib.Reusable.YK11.step_andi SEGS _ (w64 0x841f0) m (seg_rom SEGS) _ _ _ _ rp_R6_F1f0 eq_refl rp_R6_D1f0) | rp_R6_if; rewrite R010; imm_norm; unfold w64; apply rp_R6_and7; lia | rp_R6_pc |].
  eapply (rp_R6_ms _ _ 0x841f4 0x841d4);
  [eapply lib.Reusable.YK11.step_blt_tk; [exact rp_R6_F1f4 | reflexivity | exact rp_R6_D1f4 |];
   rp_R6_gres; rewrite R015; unfold w64; rewrite rp_R6_lts by (pose proof (Z.mod_pos_bound x 8 ltac:(lia)); lia);
   apply Z.ltb_lt; exact Slt | rp_R6_pc |].
  apply mst_refl.
Qed.
(* 0x841d4 .. 0x841e8: the byte load, the three counters, the sum, and `bnez a4` *)
Lemma rp_R6_body : forall (m : word -> option byte) (R : bvmap 5 word) (x sum c : Z) (b : byte),
getr R 10 = w64 x -> getr R 12 = w64 x -> getr R 13 = w64 sum -> getr R 14 = w64 c ->
0 <= x < 2 ^ 63 -> 0 <= sum < 2 ^ 62 -> 1 <= c <= 32 -> mbyte SEGS m x = Some b ->
exists R1, msteps SEGS (mkst R (w64 0x841d4) m (seg_rom SEGS))
(mkst R1 (w64 (if c =? 1 then 0x841ec else 0x841c4)) m (seg_rom SEGS)) /\
getr R1 10 = w64 (x + 1) /\ getr R1 12 = w64 (x + 1) /\ getr R1 13 = w64 (sum + bv_unsigned b) /\
getr R1 14 = w64 (c - 1) /\
(forall r : Prelude.reg, r <> 10%bv -> r <> 12%bv -> r <> 13%bv -> r <> 14%bv -> r <> 15%bv -> getr R1 r = getr R r).
Proof.
intros m R x sum c b H10 H12 H13 H14 Hx Hs Hc Hb.
pose proof (bv_unsigned_in_range 8 b) as Hbr. unfold bv_modulus in Hbr. change (2 ^ Z.of_N 8) with 256 in Hbr.
eexists. split.
{
eapply rp_R6_msv with (rd := 15%bv) (v' := w64 (bv_unsigned b)) (pc' := 0x841d8);
[eapply lib.Reusable.YK11.step_lbu; [exact rp_R6_F1d4 | reflexivity | exact rp_R6_D1d4 |];
 rewrite H12; imm_norm; unfold w64; apply rp_R6_rdn1; [exact Hb | lia]
| rp_R6_if; reflexivity | rp_R6_pc |].
eapply rp_R6_msv with (rd := 14%bv) (v' := w64 (c - 1)) (pc' := 0x841dc);
[exact (lib.Reusable.YK11.step_addi SEGS _ (w64 0x841d8) m (seg_rom SEGS) _ _ _ _ rp_R6_F1d8 eq_refl rp_R6_D1d8) | rp_R6_if; rp_R6_gres; rewrite H14; imm_norm; unfold w64; rewrite YCbn.v_addi_lit; f_equal; lia | rp_R6_pc |].
eapply rp_R6_msv with (rd := 10%bv) (v' := w64 (x + 1)) (pc' := 0x841e0);
[exact (lib.Reusable.YK11.step_addi SEGS _ (w64 0x841dc) m (seg_rom SEGS) _ _ _ _ rp_R6_F1dc eq_refl rp_R6_D1dc) | rp_R6_if; rp_R6_gres; rewrite H10; imm_norm; unfold w64; rewrite YCbn.v_addi_lit; reflexivity | rp_R6_pc |].
eapply rp_R6_msv with (rd := 13%bv) (v' := w64 (sum + bv_unsigned b)) (pc' := 0x841e4);
[exact (lib.Reusable.YK11.step_add SEGS _ (w64 0x841e0) m (seg_rom SEGS) _ _ _ _ rp_R6_F1e0 eq_refl rp_R6_D1e0) | rp_R6_if; rp_R6_gres; rewrite H13; unfold w64; apply rp_R6_add; lia | rp_R6_pc |].
eapply rp_R6_msv with (rd := 12%bv) (v' := w64 (x + 1)) (pc' := 0x841e8);
[exact (lib.Reusable.YK11.step_addi SEGS _ (w64 0x841e4) m (seg_rom SEGS) _ _ _ _ rp_R6_F1e4 eq_refl rp_R6_D1e4) | rp_R6_if; rp_R6_gres; rewrite H12; imm_norm; unfold w64; rewrite YCbn.v_addi_lit; reflexivity | rp_R6_pc |].
destruct (Z.eqb_spec c 1) as [E1|E1].
- eapply (rp_R6_ms _ _ 0x841e8 0x841ec);
  [eapply lib.Reusable.YK11.step_bne_ft; [exact rp_R6_F1e8 | reflexivity | exact rp_R6_D1e8 |];
   rp_R6_gres; rewrite getr_zero; unfold w64; rewrite rp_R6_ceq by lia; apply Z.eqb_eq; lia | rp_R6_pc |].
  apply mst_refl.
- eapply (rp_R6_ms _ _ 0x841e8 0x841c4);
  [eapply lib.Reusable.YK11.step_bne_tk; [exact rp_R6_F1e8 | reflexivity | exact rp_R6_D1e8 |];
   rp_R6_gres; rewrite getr_zero; unfold w64; rewrite rp_R6_ceq by lia; apply Z.eqb_neq; lia | rp_R6_pc |].
  apply mst_refl. }
split; [rp_R6_gres; reflexivity|]. split; [rp_R6_gres; reflexivity|]. split; [rp_R6_gres; reflexivity|].
split; [rp_R6_gres; reflexivity|].
intros r Hr10 Hr12 Hr13 Hr14 Hr15. rewrite !getr_other by assumption. reflexivity.
Qed.
(* 0x841ec .. 0x84200 (`j`, `zext.b`, `beqz`): to 0x84300 when the byte sum is 0 mod 256 *)
Lemma rp_R6_pass : forall (m : word -> option byte) (R : bvmap 5 word) (sum : Z),
getr R 13 = w64 sum -> 0 <= sum < 2 ^ 62 -> sum mod 256 = 0 ->
exists R1, msteps SEGS (mkst R (w64 0x841ec) m (seg_rom SEGS)) (mkst R1 (w64 0x84300) m (seg_rom SEGS)) /\
(forall r : Prelude.reg, r <> 10%bv -> getr R1 r = getr R r).
Proof.
intros m R sum H13 Hs H0. eexists. split.
{ eapply (rp_R6_ms R R 0x841ec 0x841fc);
[exact (YK14.step_jal_link SEGS R (w64 0x841ec) m (seg_rom SEGS) _ _ _ rp_R6_F1ec eq_refl rp_R6_D1ec) | rp_R6_pc |].
eapply rp_R6_msv with (rd := 10%bv) (v' := w64 (sum mod 256)) (pc' := 0x84200);
[exact (lib.Reusable.YK11.step_andi SEGS _ (w64 0x841fc) m (seg_rom SEGS) _ _ _ _ rp_R6_F1fc eq_refl rp_R6_D1fc) | rp_R6_if; rewrite H13; imm_norm; unfold w64; apply rp_R6_and255; lia | rp_R6_pc |].
eapply (rp_R6_ms _ _ 0x84200 0x84300);
[eapply lib.Reusable.YK11.step_beq_tk; [exact rp_R6_F200 | reflexivity | exact rp_R6_D200 |];
 rp_R6_gres; rewrite getr_zero, H0; reflexivity | rp_R6_pc |].
apply mst_refl. }
intros r Hr. rewrite getr_other by exact Hr. reflexivity.
Qed.
(* 0x841ec .. 0x84204: to the join 0x84208 with a0 = 0 when the byte sum is not 0 mod 256 *)
Lemma rp_R6_fail : forall (m : word -> option byte) (R : bvmap 5 word) (sum : Z),
getr R 13 = w64 sum -> 0 <= sum < 2 ^ 62 -> sum mod 256 <> 0 ->
exists R1, msteps SEGS (mkst R (w64 0x841ec) m (seg_rom SEGS)) (mkst R1 (w64 0x84208) m (seg_rom SEGS)) /\
getr R1 10 = w64 0 /\ (forall r : Prelude.reg, r <> 10%bv -> getr R1 r = getr R r).
Proof.
intros m R sum H13 Hs H0. eexists. split.
{ eapply (rp_R6_ms R R 0x841ec 0x841fc);
[exact (YK14.step_jal_link SEGS R (w64 0x841ec) m (seg_rom SEGS) _ _ _ rp_R6_F1ec eq_refl rp_R6_D1ec) | rp_R6_pc |].
eapply rp_R6_msv with (rd := 10%bv) (v' := w64 (sum mod 256)) (pc' := 0x84200);
[exact (lib.Reusable.YK11.step_andi SEGS _ (w64 0x841fc) m (seg_rom SEGS) _ _ _ _ rp_R6_F1fc eq_refl rp_R6_D1fc) | rp_R6_if; rewrite H13; imm_norm; unfold w64; apply rp_R6_and255; lia | rp_R6_pc |].
eapply (rp_R6_ms _ _ 0x84200 0x84204);
[eapply lib.Reusable.YK11.step_beq_ft; [exact rp_R6_F200 | reflexivity | exact rp_R6_D200 |];
 rp_R6_gres; rewrite getr_zero; unfold w64;
 rewrite rp_R6_ceq by (pose proof (Z.mod_pos_bound sum 256 ltac:(lia)); lia); apply Z.eqb_neq; exact H0
| rp_R6_pc |].
eapply rp_R6_msv with (rd := 10%bv) (v' := w64 0) (pc' := 0x84208);
[exact (lib.Reusable.YK11.step_addi SEGS _ (w64 0x84204) m (seg_rom SEGS) _ _ _ _ rp_R6_F204 eq_refl rp_R6_D204) | rp_R6_if; rewrite getr_zero; imm_norm; unfold w64; rewrite YCbn.v_addi_lit; reflexivity | rp_R6_pc |].
apply mst_refl. }
split; [rp_R6_gres; reflexivity|]. intros r Hr. rewrite !getr_other by exact Hr. reflexivity.
Qed.
(* the cut facts the run carries *)
Lemma rp_R6_jhold : forall cx pos ly3 S3 W3 mem3 md3 X, rp_jhold cx pos ly3 S3 W3 mem3 md3 ->
rp_jhold cx pos ly3 S3 W3 mem3 (with_vm_backing (m_vm_lazy md3) X md3).
Proof.
intros cx pos ly3 S3 W3 mem3 md3 X (HJ & REST). split; [|exact REST].
apply (ajournal_materialize SEGS B LAWS CtrlImg.ctrl_segs_low). exact HJ.
Qed.
Lemma rp_R6_carry : forall cx (regs regs' : bvmap 5 word) W mem E, rp_carry cx regs W mem E ->
(forall r : Prelude.reg, r <> 10%bv -> r <> 12%bv -> r <> 13%bv -> r <> 14%bv -> r <> 15%bv -> r <> 16%bv ->
 getr regs' r = getr regs r) ->
rp_carry cx regs' W mem E.
Proof.
intros cx regs regs' W mem E (HR & REST) G. split; [|exact REST].
unfold rp_regs_ok in *. rewrite !G by reg_neq_tac. exact HR.
Qed.
Lemma rp_R6_Eout : forall cx (regs : bvmap 5 word) W mem, rp_carry cx regs W mem rp_Enone ->
rp_carry cx regs W mem (rp_Eout cx).
Proof.
intros cx regs W mem (HR & (Hw & K1 & K2 & K3 & K4 & K5 & K6) & REST).
split; [exact HR|]. split; [|exact REST]. split; [exact Hw|].
split; [intros a Ha Hs _; exact (K1 a Ha Hs (fun F => F))|].
split; [intros b0 m0 i0 Hin Hi _; exact (K2 b0 m0 i0 Hin Hi (fun F => F))|].
split; [exact K3|].
split; [intros cid pos0 a Hin Hr _; exact (K4 cid pos0 a Hin Hr (fun F => F))|].
split; [exact K5 | exact K6].
Qed.

(* R6  C8 -> C9 or C11, 0x841c4..0x84200 (+0x238..+0x274), 32 turns. By induction on 32 - i, exactly as the
   donors' loop lemmas: each turn is the shadow check of fr+18+i (from rp_msg), the byte load, the three
   `addi` and `bnez a4`; at i = 32 the run falls through 0x841ec to 0x841fc, where `zext.b` of the sum is
   `blocksum (ir_blk g)` and `beqz` splits to C9 (0) or to 0x84204 -> C11.
   The slow path 0x841f0..0x841f8 (`__asan_report_load1`) is never reached: the shadow byte is 0.
   Donors: B `BlkLoop` / `rloopB` :40; A18 `BlkLoop` / `rloopB` :32, `join_blk` :172. Difficulty: medium
   (mechanical once the first turn is done). *)
Lemma rp_R6 : rp_from_C9 -> rp_from_C11 -> rp_from_C8.
Proof.
intros F9 F11.
assert (PC0 : rp_pc 0x238 = 0x841c4) by (vm_compute; reflexivity).
assert (PC9 : rp_pc 0x374 = 0x84300) by (vm_compute; reflexivity).
assert (PC11 : rp_pc 0x27c = 0x84208) by (vm_compute; reflexivity).
assert (IND : forall (n : nat) cx pos i regs3 ly3 S3 W3 mem3 md3, Z.to_nat (32 - i) = n -> rp_base cx ->
  rp_C8 cx pos i regs3 ly3 S3 W3 mem3 md3 ->
  SRr SEGS W3 (cfg_at SEGS (rp_pc 0x238) regs3 mem3 md3) (rp_post cx)).
2: { intros cx pos i regs3 ly3 S3 W3 mem3 md3 HB HC. exact (IND _ cx pos i regs3 ly3 S3 W3 mem3 md3 eq_refl HB HC). }
induction n as [|n IH]; intros cx pos i regs3 ly3 S3 W3 mem3 md3 Hn HB HC;
pose proof HC as (HJ & HCA & HFR & HFP & HFW & HSH & HAR & HT2 & H11 & Hi & H10 & H12 & H13 & H14).
{ lia. }
pose proof HCA as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H27) & _ & _ & HMSG & _).
pose proof HT2 as ((HL50 & _) & _).
destruct (HMSG HAR HL50) as (HG & HTS).
pose proof HTS as (_ & HRA & _ & _ & Hq0 & Hq63).
assert (HLg : length (rc_g cx) = 50%nat) by (clear - HB; unfold rp_base in HB; decompose [and] HB; assumption).
set (x := rc_fr cx + 18 + i) in *.
assert (Hx : 0 <= x < 2 ^ 63) by (unfold x; lia).
(* the shadow byte of x (rp_msg's range_addressable) *)
destruct (HRA x ltac:(unfold x; lia)) as (s & Hs & Hok).
unfold aview, shadow_of_addr in Hs. cbv beta in Hs.
match type of Hs with context [option_map _ ?t] => destruct t as [sh|] eqn:Esh end;
cbn [option_map] in Hs; [|discriminate Hs].
injection Hs as Hs. subst s.
(* the message byte fr[18+i] (rp_msg's garr8) *)
destruct (HG (18 + Z.to_nat i)%nat ltac:(rewrite length_map; lia)) as (Hb & _).
pose proof (Hb 0%nat ltac:(lia)) as Hb0.
replace (rc_fr cx + Z.of_nat (18 + Z.to_nat i) + Z.of_nat 0) with x in Hb0 by (unfold x; lia).
set (b := Z_to_bv 8 (le_byte (nth (18 + Z.to_nat i) (map bv_unsigned (rc_g cx)) 0) 1 0)) in Hb0.
assert (Eb : bv_unsigned b = bv_unsigned (nth (18 + Z.to_nat i) (rc_g cx) (Z_to_bv 8 0))) by apply rp_R6_byte.
pose proof (bv_unsigned_in_range 8 b) as Hbr. unfold bv_modulus in Hbr. change (2 ^ Z.of_N 8) with 256 in Hbr.
pose proof (rp_R6_psum (ir_blk (rc_g cx)) (Z.to_nat i)) as PSr.
assert (PS1 : psum (ir_blk (rc_g cx)) (Z.to_nat (i + 1)) = psum (ir_blk (rc_g cx)) (Z.to_nat i) + bv_unsigned b).
{ replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. cbn [psum]. f_equal.
  rewrite Eb. unfold ir_blk. rewrite rp_R6_nth_skipn. reflexivity. }
(* one turn: 0x841c4 -> 0x841d4 -> 0x841ec / 0x841c4 *)
destruct (rp_R6_chk (mrestrict (w_H W3) mem3) regs3 x sh H10 H27 Hx Esh Hok) as (R1 & MS1 & G1).
destruct (rp_R6_body (mrestrict (w_H W3) mem3) R1 x (psum (ir_blk (rc_g cx)) (Z.to_nat i)) (32 - i) b)
as (R2 & MS2 & G10 & G12 & G13 & G14 & G2).
{ rewrite G1 by reg_neq_tac. exact H10. }
{ rewrite G1 by reg_neq_tac. exact H12. }
{ rewrite G1 by reg_neq_tac. exact H13. }
{ rewrite G1 by reg_neq_tac. exact H14. }
{ exact Hx. }
{ lia. }
{ lia. }
{ exact Hb0. }
assert (GP : forall r : Prelude.reg, r <> 10%bv -> r <> 12%bv -> r <> 13%bv -> r <> 14%bv -> r <> 15%bv -> r <> 16%bv ->
  getr R2 r = getr regs3 r)
by (intros r Ha Hb' Hc Hd He Hf; rewrite G2 by assumption; apply G1; assumption).
assert (HFR2 : rp_fregs cx pos R2) by (unfold rp_fregs in *; rewrite !GP by reg_neq_tac; exact HFR).
assert (H112 : getr R2 11 = w64 (rp_s cx)) by (rewrite GP by reg_neq_tac; exact H11).
unfold cfg_at. rewrite PC0.
destruct (Z.eq_dec i 31) as [I31|I31].
- (* the last turn, then the exit 0x841ec .. 0x84204 *)
  replace (32 - i =? 1) with true in MS2 by (symmetry; apply Z.eqb_eq; lia).
  replace (Z.to_nat (i + 1)) with 32%nat in PS1 by lia.
  pose proof (rp_R6_psum (ir_blk (rc_g cx)) 32) as PS32.
  assert (BS : blocksum (ir_blk (rc_g cx)) = (psum (ir_blk (rc_g cx)) (Z.to_nat i) + bv_unsigned b) mod 256)
  by (unfold blocksum; rewrite PS1; reflexivity).
  destruct (Z.eq_dec (blocksum (ir_blk (rc_g cx))) 0) as [B0|B0].
  + destruct (rp_R6_pass (mrestrict (w_H W3) mem3) R2 _ G13 ltac:(lia) ltac:(lia)) as (R3 & MS3 & G3).
    eapply (SRr_msteps SEGS CtrlImg.ctrl_wx W3 _ (mkst R3 (w64 0x84300) (mrestrict (w_H W3) mem3) (seg_rom SEGS)) md3).
    { rewrite restrict_mkst_fx. eapply msteps_trans; [exact MS1|]. eapply msteps_trans; [exact MS2|]. exact MS3. }
    intros md' Hsbm _. rewrite unrestrict_mkst_mrestrict. rewrite (same_but_materialized_wvb md3 md' Hsbm).
    replace (w64 0x84300) with (w64 (rp_pc 0x374)) by (rewrite PC9; reflexivity).
    apply (F9 cx pos R3 ly3 S3 W3 mem3 _ HB).
    assert (GP3 : forall r : Prelude.reg, r <> 10%bv -> r <> 12%bv -> r <> 13%bv -> r <> 14%bv -> r <> 15%bv -> r <> 16%bv ->
      getr R3 r = getr regs3 r)
    by (intros r Ha Hb' Hc Hd He Hf; rewrite G3 by assumption; apply GP; assumption).
    unfold rp_C9.
    split; [apply rp_R6_jhold; exact HJ|].
    split; [exact (rp_R6_carry cx regs3 R3 W3 mem3 rp_Enone HCA GP3)|].
    split; [unfold rp_fregs in *; rewrite !G3 by reg_neq_tac; exact HFR2|].
    split; [exact HFP|]. split; [exact HFW|]. split; [exact HSH|]. split; [exact HAR|]. split; [exact HT2|].
    split; [rewrite G3 by reg_neq_tac; exact H112|].
    exact B0.
  + destruct (rp_R6_fail (mrestrict (w_H W3) mem3) R2 _ G13 ltac:(lia) ltac:(lia)) as (R3 & MS3 & G310 & G3).
    eapply (SRr_msteps SEGS CtrlImg.ctrl_wx W3 _ (mkst R3 (w64 0x84208) (mrestrict (w_H W3) mem3) (seg_rom SEGS)) md3).
    { rewrite restrict_mkst_fx. eapply msteps_trans; [exact MS1|]. eapply msteps_trans; [exact MS2|]. exact MS3. }
    intros md' Hsbm _. rewrite unrestrict_mkst_mrestrict. rewrite (same_but_materialized_wvb md3 md' Hsbm).
    replace (w64 0x84208) with (w64 (rp_pc 0x27c)) by (rewrite PC11; reflexivity).
    apply (F11 cx pos R3 ly3 S3 W3 mem3 _ HB).
    assert (GP3 : forall r : Prelude.reg, r <> 10%bv -> r <> 12%bv -> r <> 13%bv -> r <> 14%bv -> r <> 15%bv -> r <> 16%bv ->
      getr R3 r = getr regs3 r)
    by (intros r Ha Hb' Hc Hd He Hf; rewrite G3 by assumption; apply GP; assumption).
    assert (HIR : ir (rc_len cx) (rc_g cx) = false).
    { destruct (ir (rc_len cx) (rc_g cx)) eqn:E; [|reflexivity].
      apply ir_true in E. destruct E as (_ & _ & _ & _ & _ & _ & _ & E & _). contradiction. }
    unfold rp_C11.
    split; [apply rp_R6_jhold; exact HJ|].
    split; [apply rp_R6_Eout; exact (rp_R6_carry cx regs3 R3 W3 mem3 rp_Enone HCA GP3)|].
    split; [unfold rp_fregs in *; rewrite !G3 by reg_neq_tac; exact HFR2|].
    split; [exact HFP|]. split; [exact HFW|]. split; [exact HSH|]. split; [exact HAR|].
    split; [rewrite G310; unfold rp_ret, reply_ret; unfold rp_argsb in HAR; rewrite HAR, HIR; reflexivity|].
    intros HOK. exfalso. unfold rp_okb, reply_ok in HOK. unfold rp_argsb in HAR. rewrite HAR, HIR in HOK.
    discriminate HOK.
- (* the next turn, C8 at i + 1 *)
  replace (32 - i =? 1) with false in MS2 by (symmetry; apply Z.eqb_neq; lia).
  eapply (SRr_msteps SEGS CtrlImg.ctrl_wx W3 _ (mkst R2 (w64 0x841c4) (mrestrict (w_H W3) mem3) (seg_rom SEGS)) md3).
  { rewrite restrict_mkst_fx. eapply msteps_trans; [exact MS1 | exact MS2]. }
  intros md' Hsbm _. rewrite unrestrict_mkst_mrestrict. rewrite (same_but_materialized_wvb md3 md' Hsbm).
  rewrite <- PC0.
  apply (IH cx pos (i + 1) R2 ly3 S3 W3 mem3 _); [lia | exact HB |].
  unfold rp_C8.
  split; [apply rp_R6_jhold; exact HJ|].
  split; [exact (rp_R6_carry cx regs3 R2 W3 mem3 rp_Enone HCA GP)|].
  split; [exact HFR2|].
  split; [exact HFP|]. split; [exact HFW|]. split; [exact HSH|]. split; [exact HAR|]. split; [exact HT2|].
  split; [exact H112|].
  split; [lia|].
  split; [rewrite G10; unfold x; f_equal; lia|].
  split; [rewrite G12; unfold x; f_equal; lia|].
  split; [rewrite G13, PS1; reflexivity|].
  rewrite G14. f_equal. lia.
Qed.

(* ---- rp_R7L: local helpers of the record-loop stretch. The loop body and its two exits write no memory, so
   each instruction is one concrete `SRr_step` (YA0n.v:133) through the core's step lemmas (YK11.v), with the
   journal carried across the step's materialization by `ajournal_materialize` (YCbq.v:664). ---- *)
Lemma rp_R7L_go : forall (W : world SEGS) (P : Model -> Prop) regs mem md (pc pc' : Z) regs' Q,
(forall m m', P m -> same_but_materialized m m' -> P m') -> P md ->
RiscvSemantics.step SEGS (mkst regs (Z_to_bv 64 pc) (mrestrict (w_H W) mem) (seg_rom SEGS)) =
MachineOk (mkst regs' (Z_to_bv 64 pc') (mrestrict (w_H W) mem) (seg_rom SEGS)) ->
(forall md', P md' -> SRr SEGS W (cfg_at SEGS pc' regs' mem md') Q) ->
SRr SEGS W (cfg_at SEGS pc regs mem md) Q.
Proof.
intros W P regs mem md pc pc' regs' Q HC HP Hs HK. unfold cfg_at, w64.
eapply (SRr_step SEGS CtrlImg.ctrl_wx W); [reflexivity | rewrite restrict_mkst_fx; exact Hs |].
intros md' Hm. pose proof (HK md' (HC md md' HP Hm)) as HK'. unfold cfg_at, w64 in HK'.
rewrite <- (unrestrict_mkst_mrestrict (w_H W) regs' (Z_to_bv 64 pc') mem (seg_rom SEGS)) in HK'.
exact HK'.
Qed.
Lemma rp_R7L_srli : forall (W : world SEGS) (P : Model -> Prop) regs mem md (pc pc' w : Z) (rd rs : bv 5) (sh : bv 6)
(shz : Z) Q,
(forall m m', P m -> same_but_materialized m m' -> P m') -> P md ->
clookup CtrlImg.ctrltbl pc = Some w -> is_ecall (Z_to_bv 32 w) = false ->
decode_any (Z_to_bv 32 w) = Some (ShiftImm ALU_SRL rd rs sh, 4%Z) -> rd <> 0%bv -> bv_unsigned sh = shz ->
pc' = pc + 4 ->
(forall md', P md' -> SRr SEGS W (cfg_at SEGS pc' (regupd regs rd (v_srli (getr regs rs) shz)) mem md') Q) ->
SRr SEGS W (cfg_at SEGS pc regs mem md) Q.
Proof.
intros W P regs mem md pc pc' w rd rs sh shz Q HC HP Hl He Hd Hr Hsh Hpc HK.
refine (rp_R7L_go W P regs mem md pc pc' _ Q HC HP _ HK).
rewrite (step_srli SEGS regs (Z_to_bv 64 pc) _ _ _ rd rs sh (CtrlImg.ctrltbl_ok pc w Hl) He Hd).
rewrite (bv_eqb_neq rd 0%bv Hr), v_addi_lit, Hsh, Hpc. reflexivity.
Qed.
Lemma rp_R7L_add : forall (W : world SEGS) (P : Model -> Prop) regs mem md (pc pc' w : Z) (rd rs1 rs2 : bv 5) Q,
(forall m m', P m -> same_but_materialized m m' -> P m') -> P md ->
clookup CtrlImg.ctrltbl pc = Some w -> is_ecall (Z_to_bv 32 w) = false ->
decode_any (Z_to_bv 32 w) = Some (Op ALU_ADD rd rs1 rs2, 4%Z) -> rd <> 0%bv -> pc' = pc + 4 ->
(forall md', P md' -> SRr SEGS W (cfg_at SEGS pc' (regupd regs rd (v_add (getr regs rs1) (getr regs rs2))) mem md') Q) ->
SRr SEGS W (cfg_at SEGS pc regs mem md) Q.
Proof.
intros W P regs mem md pc pc' w rd rs1 rs2 Q HC HP Hl He Hd Hr Hpc HK.
refine (rp_R7L_go W P regs mem md pc pc' _ Q HC HP _ HK).
rewrite (step_add SEGS regs (Z_to_bv 64 pc) _ _ _ rd rs1 rs2 (CtrlImg.ctrltbl_ok pc w Hl) He Hd).
rewrite (bv_eqb_neq rd 0%bv Hr), v_addi_lit, Hpc. reflexivity.
Qed.
Lemma rp_R7L_addi : forall (W : world SEGS) (P : Model -> Prop) regs mem md (pc pc' w : Z) (rd rs : bv 5) (imm : bv 12)
(immz : Z) Q,
(forall m m', P m -> same_but_materialized m m' -> P m') -> P md ->
clookup CtrlImg.ctrltbl pc = Some w -> is_ecall (Z_to_bv 32 w) = false ->
decode_any (Z_to_bv 32 w) = Some (OpImm ALU_ADD rd rs imm, 4%Z) -> rd <> 0%bv -> bv_signed imm = immz ->
pc' = pc + 4 ->
(forall md', P md' -> SRr SEGS W (cfg_at SEGS pc' (regupd regs rd (v_addi (getr regs rs) immz)) mem md') Q) ->
SRr SEGS W (cfg_at SEGS pc regs mem md) Q.
Proof.
intros W P regs mem md pc pc' w rd rs imm immz Q HC HP Hl He Hd Hr Him Hpc HK.
refine (rp_R7L_go W P regs mem md pc pc' _ Q HC HP _ HK).
rewrite (step_addi SEGS regs (Z_to_bv 64 pc) _ _ _ rd rs imm (CtrlImg.ctrltbl_ok pc w Hl) He Hd).
rewrite (bv_eqb_neq rd 0%bv Hr), Him, v_addi_lit, Hpc. reflexivity.
Qed.
Lemma rp_R7L_andi : forall (W : world SEGS) (P : Model -> Prop) regs mem md (pc pc' w : Z) (rd rs : bv 5) (imm : bv 12)
(immz : Z) Q,
(forall m m', P m -> same_but_materialized m m' -> P m') -> P md ->
clookup CtrlImg.ctrltbl pc = Some w -> is_ecall (Z_to_bv 32 w) = false ->
decode_any (Z_to_bv 32 w) = Some (OpImm ALU_AND rd rs imm, 4%Z) -> rd <> 0%bv -> bv_signed imm = immz ->
pc' = pc + 4 ->
(forall md', P md' -> SRr SEGS W (cfg_at SEGS pc' (regupd regs rd (v_andi (getr regs rs) immz)) mem md') Q) ->
SRr SEGS W (cfg_at SEGS pc regs mem md) Q.
Proof.
intros W P regs mem md pc pc' w rd rs imm immz Q HC HP Hl He Hd Hr Him Hpc HK.
refine (rp_R7L_go W P regs mem md pc pc' _ Q HC HP _ HK).
rewrite (step_andi SEGS regs (Z_to_bv 64 pc) _ _ _ rd rs imm (CtrlImg.ctrltbl_ok pc w Hl) He Hd).
rewrite (bv_eqb_neq rd 0%bv Hr), Him, v_addi_lit, Hpc. reflexivity.
Qed.
Lemma rp_R7L_lb : forall (W : world SEGS) (P : Model -> Prop) regs mem md (pc pc' w : Z) (rd rs : bv 5) (imm : bv 12)
(b : byte) Q,
(forall m m', P m -> same_but_materialized m m' -> P m') -> P md ->
clookup CtrlImg.ctrltbl pc = Some w -> is_ecall (Z_to_bv 32 w) = false ->
decode_any (Z_to_bv 32 w) = Some (Load SZ1 true rd rs imm, 4%Z) -> rd <> 0%bv -> bv_signed imm = 0 ->
pc' = pc + 4 ->
rdn SEGS (mrestrict (w_H W) mem) (getr regs rs) 1%nat = Some [b] ->
(forall md', P md' -> SRr SEGS W (cfg_at SEGS pc' (regupd regs rd (v_lb b)) mem md') Q) ->
SRr SEGS W (cfg_at SEGS pc regs mem md) Q.
Proof.
intros W P regs mem md pc pc' w rd rs imm b Q HC HP Hl He Hd Hr Him Hpc Hrd HK.
refine (rp_R7L_go W P regs mem md pc pc' _ Q HC HP _ HK).
rewrite (step_lb SEGS regs (Z_to_bv 64 pc) _ _ _ rd rs imm b (CtrlImg.ctrltbl_ok pc w Hl) He Hd).
- rewrite (bv_eqb_neq rd 0%bv Hr), v_addi_lit, Hpc. reflexivity.
- rewrite Him. unfold v_addi. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact Hrd.
Qed.
Lemma rp_R7L_lbu : forall (W : world SEGS) (P : Model -> Prop) regs mem md (pc pc' w : Z) (rd rs : bv 5) (imm : bv 12)
(b : byte) Q,
(forall m m', P m -> same_but_materialized m m' -> P m') -> P md ->
clookup CtrlImg.ctrltbl pc = Some w -> is_ecall (Z_to_bv 32 w) = false ->
decode_any (Z_to_bv 32 w) = Some (Load SZ1 false rd rs imm, 4%Z) -> rd <> 0%bv -> bv_signed imm = 0 ->
pc' = pc + 4 ->
rdn SEGS (mrestrict (w_H W) mem) (getr regs rs) 1%nat = Some [b] ->
(forall md', P md' -> SRr SEGS W (cfg_at SEGS pc' (regupd regs rd (Z_to_bv 64 (bv_unsigned b))) mem md') Q) ->
SRr SEGS W (cfg_at SEGS pc regs mem md) Q.
Proof.
intros W P regs mem md pc pc' w rd rs imm b Q HC HP Hl He Hd Hr Him Hpc Hrd HK.
refine (rp_R7L_go W P regs mem md pc pc' _ Q HC HP _ HK).
rewrite (step_lbu SEGS regs (Z_to_bv 64 pc) _ _ _ rd rs imm b (CtrlImg.ctrltbl_ok pc w Hl) He Hd).
- rewrite (bv_eqb_neq rd 0%bv Hr), v_addi_lit, Hpc. reflexivity.
- rewrite Him. unfold v_addi. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact Hrd.
Qed.
Lemma rp_R7L_bne_tk : forall (W : world SEGS) (P : Model -> Prop) regs mem md (pc pc' w : Z) (rs1 rs2 : bv 5)
(imm : bv 13) Q,
(forall m m', P m -> same_but_materialized m m' -> P m') -> P md ->
clookup CtrlImg.ctrltbl pc = Some w -> is_ecall (Z_to_bv 32 w) = false ->
decode_any (Z_to_bv 32 w) = Some (Branch BC_NE rs1 rs2 imm, 4%Z) -> pc' = pc + bv_signed imm ->
c_eq (getr regs rs1) (getr regs rs2) = false ->
(forall md', P md' -> SRr SEGS W (cfg_at SEGS pc' regs mem md') Q) ->
SRr SEGS W (cfg_at SEGS pc regs mem md) Q.
Proof.
intros W P regs mem md pc pc' w rs1 rs2 imm Q HC HP Hl He Hd Hpc Hc HK.
refine (rp_R7L_go W P regs mem md pc pc' regs Q HC HP _ HK).
rewrite (step_bne_tk SEGS regs (Z_to_bv 64 pc) _ _ _ rs1 rs2 imm (CtrlImg.ctrltbl_ok pc w Hl) He Hd Hc).
rewrite btgt_lit, Hpc. reflexivity.
Qed.
Lemma rp_R7L_bne_ft : forall (W : world SEGS) (P : Model -> Prop) regs mem md (pc pc' w : Z) (rs1 rs2 : bv 5)
(imm : bv 13) Q,
(forall m m', P m -> same_but_materialized m m' -> P m') -> P md ->
clookup CtrlImg.ctrltbl pc = Some w -> is_ecall (Z_to_bv 32 w) = false ->
decode_any (Z_to_bv 32 w) = Some (Branch BC_NE rs1 rs2 imm, 4%Z) -> pc' = pc + 4 ->
c_eq (getr regs rs1) (getr regs rs2) = true ->
(forall md', P md' -> SRr SEGS W (cfg_at SEGS pc' regs mem md') Q) ->
SRr SEGS W (cfg_at SEGS pc regs mem md) Q.
Proof.
intros W P regs mem md pc pc' w rs1 rs2 imm Q HC HP Hl He Hd Hpc Hc HK.
refine (rp_R7L_go W P regs mem md pc pc' regs Q HC HP _ HK).
rewrite (step_bne_ft SEGS regs (Z_to_bv 64 pc) _ _ _ rs1 rs2 imm (CtrlImg.ctrltbl_ok pc w Hl) He Hd Hc).
rewrite v_addi_lit, Hpc. reflexivity.
Qed.
Lemma rp_R7L_blt_tk : forall (W : world SEGS) (P : Model -> Prop) regs mem md (pc pc' w : Z) (rs1 rs2 : bv 5)
(imm : bv 13) Q,
(forall m m', P m -> same_but_materialized m m' -> P m') -> P md ->
clookup CtrlImg.ctrltbl pc = Some w -> is_ecall (Z_to_bv 32 w) = false ->
decode_any (Z_to_bv 32 w) = Some (Branch BC_LT rs1 rs2 imm, 4%Z) -> pc' = pc + bv_signed imm ->
c_lts (getr regs rs1) (getr regs rs2) = true ->
(forall md', P md' -> SRr SEGS W (cfg_at SEGS pc' regs mem md') Q) ->
SRr SEGS W (cfg_at SEGS pc regs mem md) Q.
Proof.
intros W P regs mem md pc pc' w rs1 rs2 imm Q HC HP Hl He Hd Hpc Hc HK.
refine (rp_R7L_go W P regs mem md pc pc' regs Q HC HP _ HK).
rewrite (step_blt_tk SEGS regs (Z_to_bv 64 pc) _ _ _ rs1 rs2 imm (CtrlImg.ctrltbl_ok pc w Hl) He Hd Hc).
rewrite btgt_lit, Hpc. reflexivity.
Qed.
Lemma rp_R7L_jal : forall (W : world SEGS) (P : Model -> Prop) regs mem md (pc pc' w : Z) (imm : bv 21) Q,
(forall m m', P m -> same_but_materialized m m' -> P m') -> P md ->
clookup CtrlImg.ctrltbl pc = Some w -> is_ecall (Z_to_bv 32 w) = false ->
decode_any (Z_to_bv 32 w) = Some (Jal 0%bv imm, 4%Z) -> pc' = pc + bv_signed imm ->
(forall md', P md' -> SRr SEGS W (cfg_at SEGS pc' regs mem md') Q) ->
SRr SEGS W (cfg_at SEGS pc regs mem md) Q.
Proof.
intros W P regs mem md pc pc' w imm Q HC HP Hl He Hd Hpc HK.
refine (rp_R7L_go W P regs mem md pc pc' regs Q HC HP _ HK).
rewrite (step_jal_x0 SEGS regs (Z_to_bv 64 pc) _ _ _ imm (CtrlImg.ctrltbl_ok pc w Hl) He Hd).
rewrite btgt_lit, Hpc. reflexivity.
Qed.
Lemma rp_R7L_rdn : forall (m : word -> option byte) (a : Z) (b : byte),
mbyte SEGS m a = Some b -> rdn SEGS m (Z_to_bv 64 a) 1%nat = Some [b].
Proof.
intros m a b H. revert H. unfold mbyte. cbn [rdn].
destruct (m (Z_to_bv 64 a)) as [b0|]; intros H; cbn iota in H |- *;
[injection H as <-; reflexivity | rewrite H; reflexivity].
Qed.
Lemma rp_R7L_u8 : forall v, 0 <= v < 256 -> bv_unsigned (Z_to_bv 8 v) = v.
Proof. intros v Hv. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. exact Hv. Qed.
Lemma rp_R7L_lbsmall : forall b : byte, 0 <= bv_unsigned b < 128 -> v_lb b = Z_to_bv 64 (bv_unsigned b).
Proof.
intros b Hb. unfold v_lb, bv_signed, bv_swrap. f_equal. change (bv_half_modulus 8) with 128.
unfold bv_wrap. change (bv_modulus 8) with 256. rewrite Z.mod_small by lia. lia.
Qed.
Lemma rp_R7L_sgn64 : forall a, 0 <= a < 2 ^ 63 -> bv_signed (Z_to_bv 64 a) = a.
Proof.
intros a Ha. unfold bv_signed, bv_swrap. rewrite unsigned_lit_small by lia. change (bv_half_modulus 64) with (2 ^ 63).
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia. lia.
Qed.
Lemma rp_R7L_ceq : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> c_eq (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof. intros a b Ha Hb. unfold c_eq, bv_eqb. rewrite !unsigned_lit_small by lia. reflexivity. Qed.
Lemma rp_R7L_clts : forall a b, 0 <= a < 2 ^ 63 -> 0 <= b < 2 ^ 63 -> c_lts (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros a b Ha Hb. unfold c_lts, bv_lts. rewrite !rp_R7L_sgn64 by lia. reflexivity. Qed.
Lemma rp_R7L_and7 : forall a, 0 <= a < 2 ^ 64 -> v_andi (Z_to_bv 64 a) 7 = Z_to_bv 64 (a mod 8).
Proof.
intros a Ha. unfold v_andi. rewrite unsigned_lit_small by lia. change (bv_wrap 64 7) with (Z.ones 3).
rewrite Z.land_ones by lia. reflexivity.
Qed.
Lemma rp_R7L_and127 : forall a, 0 <= a < 2 ^ 64 -> v_andi (Z_to_bv 64 a) 127 = Z_to_bv 64 (a mod 128).
Proof.
intros a Ha. unfold v_andi. rewrite unsigned_lit_small by lia. change (bv_wrap 64 127) with (Z.ones 7).
rewrite Z.land_ones by lia. reflexivity.
Qed.
Lemma rp_R7L_shaddr : forall x, 0 <= x < 2 ^ 63 ->
v_add (v_srli (Z_to_bv 64 x) 3) (Z_to_bv 64 SHADOW_OFF) = Z_to_bv 64 (shadow_of_addr SHADOW_OFF x).
Proof.
intros x Hx. unfold v_add, v_srli, shadow_of_addr.
rewrite (unsigned_lit_small x) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
rewrite (unsigned_lit_small (x / 8)) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite (unsigned_lit_small SHADOW_OFF) by (unfold SHADOW_OFF; lia).
f_equal. lia.
Qed.
Lemma rp_R7L_psum : forall bs k, 0 <= psum bs k <= 255 * Z.of_nat k.
Proof.
intros bs k. induction k as [|k IH]; cbn [psum]; [lia|].
pose proof (bv_unsigned_in_range 8 (nth k bs (Z_to_bv 8 0))) as R. unfold bv_modulus in R.
change (2 ^ Z.of_N 8) with 256 in R. lia.
Qed.
Lemma rp_R7L_rec_len : forall g, length g = 50%nat -> 14 <= ir_s g <= 23 -> length (ir_rec g) = Z.to_nat (ir_s g - 8).
Proof. intros g HL HS. unfold ir_rec. rewrite length_firstn, length_skipn, HL. lia. Qed.
Lemma rp_R7L_rec_nth : forall g j, length g = 50%nat -> 14 <= ir_s g <= 23 -> 0 <= j < ir_s g - 8 ->
bv_unsigned (nth (Z.to_nat j) (ir_rec g) (Z_to_bv 8 0)) = nth (Z.to_nat (34 + j)) (map bv_unsigned g) 0.
Proof.
intros g j HL HS HJ. unfold ir_rec. rewrite nth_firstn.
replace (Z.to_nat j <? Z.to_nat (ir_s g - 8))%nat with true by (symmetry; apply Nat.ltb_lt; lia).
rewrite nth_skipn.
assert (EV : nth (Z.to_nat (34 + j)) (map bv_unsigned g) 0 =
nth (Z.to_nat (34 + j)) (map bv_unsigned g) (bv_unsigned (Z_to_bv 8 0))) by (apply nth_indep; rewrite length_map; lia).
rewrite EV, map_nth. do 2 f_equal. lia.
Qed.
Lemma rp_R7L_jmat : forall cx pos ly3 S3 W3 mem3 m m',
rp_jhold cx pos ly3 S3 W3 mem3 m -> same_but_materialized m m' -> rp_jhold cx pos ly3 S3 W3 mem3 m'.
Proof.
intros cx pos ly3 S3 W3 mem3 m m' (HJ & HR) Hm. rewrite (same_but_materialized_wvb m m' Hm).
split; [apply (ajournal_materialize SEGS B LAWS CtrlImg.ctrl_segs_low); exact HJ | exact HR].
Qed.
Lemma rp_R7L_carry : forall cx regs regs' W3 mem3 (E E' : Z -> Prop),
rp_carry cx regs W3 mem3 E -> rp_regs_ok cx regs' -> (forall a, E a -> E' a) -> rp_carry cx regs' W3 mem3 E'.
Proof.
intros cx regs regs' W3 mem3 E E' (_ & (HW & K1 & K2 & K3 & K4 & K5 & K6) & HR) HRO HE.
split; [exact HRO|]. split; [|exact HR]. split; [exact HW|].
split; [intros a Ha Hs HnE; apply K1; [exact Ha | exact Hs | intros HEa; apply HnE, HE, HEa]|].
split; [intros b m i Hin Hi HnE; apply (K2 b m i Hin Hi); intros HEa; apply HnE, HE, HEa|].
split; [exact K3|].
split; [intros cid p a Hin Hr HnE; apply (K4 cid p a Hin Hr); intros HEa; apply HnE, HE, HEa|].
split; [exact K5 | exact K6].
Qed.
Lemma rp_R7L_gu : forall regs (r r' : bv 5) v,
getr (regupd regs r v) r' = if bv_eqb r' 0%bv then Z_to_bv 64 0 else if bv_eqb r' r then v else getr regs r'.
Proof.
intros regs r r' v. unfold getr at 1. destruct (bv_eqb r' 0%bv) eqn:E0; [reflexivity|].
destruct (bv_eqb r' r) eqn:E1.
- unfold bv_eqb in E1. apply Z.eqb_eq, bv_eq in E1. subst r'. apply regupd_same.
- rewrite regupd_other by (intros Heq; subst r'; rewrite bv_eqb_refl in E1; discriminate E1).
unfold getr. rewrite E0. reflexivity.
Qed.
(* one register-file layer at a time: unfold one named register file (rp_R7L_name) or rewrite one regupd,
   decide the closed register tests, drop the dead branch *)
Ltac rp_R7L_greg :=
repeat (first [ rewrite rp_R7L_gu
| match goal with E : ?R = regupd _ _ _ |- context [getr ?R _] => rewrite E end ];
repeat match goal with |- context [bv_eqb ?a ?b] =>
let e := eval vm_compute in (bv_eqb a b) in
lazymatch e with true => change (bv_eqb a b) with true | false => change (bv_eqb a b) with false end end;
cbv beta iota).
(* name the register file a step produced, so that the next steps' terms stay small *)
Ltac rp_R7L_name :=
match goal with |- SRr _ _ (cfg_at _ _ ?R _ _) _ =>
lazymatch R with regupd _ _ _ => let r := fresh "rgs" in let e := fresh "Ergs" in remember R as r eqn:e | _ => idtac end
end.
Ltac rp_R7L_side JC HJ := first [ exact JC | exact HJ | vm_refl_bv ].

(* R7L (AUXILIARY, the record loop's induction) C9L(j) -> C10 or C11, 0x84314..0x84350 (+0x388..+0x3c4).
   By induction on (s - 8) - j, as R6; at the exit `andi a3,127` is `recsum (ir_rec g)` and `bnez` splits to
   0x84204 -> C11 or falls through to C10.
   Donors: A18 `RecLoop` / `rloopR` :103, `join_rec1` :208 (image B has no donor here: B calls
   reac_ctrl_record_cksum_verify where A inlines the loop). Difficulty: medium. *)
Lemma rp_R7L : rp_from_C10 -> rp_from_C11 -> rp_from_C9L.
Proof.
intros F10 F11 cx pos j0 regs0 ly3 S3 W3 mem3 md0 HB HC0.
pose (JP := fun m => rp_jhold cx pos ly3 S3 W3 mem3 m).
assert (JC : forall m m', JP m -> same_but_materialized m m' -> JP m')
by (intros m m' Hm Hs; exact (rp_R7L_jmat cx pos ly3 S3 W3 mem3 m m' Hm Hs)).
assert (HLG : length (rc_g cx) = 50%nat) by (unfold rp_base in HB; decompose [and] HB; assumption).
assert (ES : rp_s cx = ir_s (rc_g cx)) by reflexivity.
(* one turn of the loop, from C9L(j) to C9L(j + 1) (taken `bnez a2`) or to C10 / C11 (the exit) *)
assert (ITER : forall j regs md, rp_C9L cx pos j regs ly3 S3 W3 mem3 md ->
(forall regs' md', rp_C9L cx pos (j + 1) regs' ly3 S3 W3 mem3 md' ->
SRr SEGS W3 (cfg_at SEGS (rp_pc 0x388) regs' mem3 md') (rp_post cx)) ->
SRr SEGS W3 (cfg_at SEGS (rp_pc 0x388) regs mem3 md) (rp_post cx)).
{ intros j regs md HC NEXT.
pose proof HC as (HJ & HCA & HFG & HFP & HFW & HSH & HAR & HT2 & H11 & HBS & HJR & H10 & H14 & H12 & H13).
pose proof (proj1 HCA) as HRO.
pose proof HRO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H27).
pose proof HCA as (_ & _ & _ & HMSG & _).
pose proof HT2 as ((HLEN & HK5 & H3435 & H32 & H33 & HS) & H27v & HF7).
destruct (HMSG HAR HLEN) as (HG & (_ & HRA & _ & _ & Hfr0 & Hfr50)).
remember (rc_fr cx + 34 + j) as x eqn:Ex.
assert (Hx : rc_fr cx <= x < rc_fr cx + 50) by lia.
(* the shadow byte of x (range_addressable of tsrc_ok in rp_msg) *)
destruct (HRA x Hx) as (sv & Hsv & Hok).
unfold aview in Hsv. cbv beta in Hsv. change (@pa_segs _ ctrl_listing CtrlImg.PI_ctrl) with SEGS in Hsv. revert Hsv.
destruct (mbyte SEGS (mrestrict (w_H W3) mem3) (shadow_of_addr SHADOW_OFF x)) as [bsh|] eqn:Emb;
intros Hsv; cbn [option_map] in Hsv; [|discriminate Hsv].
injection Hsv as Hsv. unfold saddr_ok in Hok.
assert (Hsv8 : 0 <= sv < 8) by (pose proof (Z.mod_pos_bound x 8 ltac:(lia)); lia).
(* the message byte at x (garr8 of rp_msg) *)
assert (Hj34 : (Z.to_nat (34 + j) < length (map bv_unsigned (rc_g cx)))%nat) by (rewrite length_map, HLG; lia).
destruct (HG _ Hj34) as (HVM & Hvr).
set (v := nth (Z.to_nat (34 + j)) (map bv_unsigned (rc_g cx)) 0) in *.
pose proof (HVM 0%nat ltac:(lia)) as MB.
rewrite le_byte_small in MB; [| change (2 ^ (8 * Z.of_nat 1)) with 256; lia | lia].
replace (Z.shiftr v (8 * Z.of_nat 0)) with v in MB by (change (8 * Z.of_nat 0) with 0; rewrite Z.shiftr_0_r; reflexivity).
replace (rc_fr cx + Z.of_nat (Z.to_nat (34 + j)) + Z.of_nat 0) with x in MB by lia.
(* the partial sum after this turn *)
assert (PS : v_add (w64 (psum (ir_rec (rc_g cx)) (Z.to_nat j))) (Z_to_bv 64 (bv_unsigned (Z_to_bv 8 v)))
= w64 (psum (ir_rec (rc_g cx)) (Z.to_nat (j + 1)))).
{ unfold w64, v_add. rewrite (rp_R7L_u8 v Hvr).
pose proof (rp_R7L_psum (ir_rec (rc_g cx)) (Z.to_nat j)) as PR.
rewrite (unsigned_lit_small (psum (ir_rec (rc_g cx)) (Z.to_nat j))) by lia.
rewrite (unsigned_lit_small v) by lia.
replace (Z.to_nat (j + 1)) with (S (Z.to_nat j)) by lia. cbn [psum].
rewrite (rp_R7L_rec_nth (rc_g cx) j HLG) by lia. reflexivity. }
(* 0x84324 .. 0x84338 and the exits, from either arm of the shadow check *)
assert (BODY : forall regsB mdB,
getr regsB 10%bv = w64 x -> getr regsB 14%bv = w64 x -> getr regsB 12%bv = w64 (rp_s cx - 8 - j) ->
getr regsB 13%bv = w64 (psum (ir_rec (rc_g cx)) (Z.to_nat j)) -> getr regsB 11%bv = w64 (rp_s cx) ->
rp_regs_ok cx regsB -> rp_fregs cx pos regsB -> JP mdB ->
SRr SEGS W3 (cfg_at SEGS 0x84324 regsB mem3 mdB) (rp_post cx)).
{ intros regsB mdB HB10 HB14 HB12 HB13 HB11 HROB HFGB HJB.
(* 0x84324 lbu a5,0(a4) *)
eapply (rp_R7L_lbu W3 JP _ mem3 _ 0x84324 0x84328 0x00074783 15%bv 14%bv (Z_to_bv 12 0) (Z_to_bv 8 v));
[rp_R7L_side JC HJB .. | rewrite HB14; apply rp_R7L_rdn; exact MB | intros md5 HJ5; rp_R7L_name].
(* 0x84328 addi a2,a2,-1 *)
eapply (rp_R7L_addi W3 JP _ mem3 _ 0x84328 0x8432c 0xfff60613 12%bv 12%bv (Z_to_bv 12 (-1)) (-1));
[rp_R7L_side JC HJ5 .. | intros md6 HJ6; rp_R7L_name].
(* 0x8432c addi a0,a0,1 *)
eapply (rp_R7L_addi W3 JP _ mem3 _ 0x8432c 0x84330 0x00150513 10%bv 10%bv (Z_to_bv 12 1) 1);
[rp_R7L_side JC HJ6 .. | intros md7 HJ7; rp_R7L_name].
(* 0x84330 add a3,a3,a5 *)
eapply (rp_R7L_add W3 JP _ mem3 _ 0x84330 0x84334 0x00f686b3 13%bv 13%bv 15%bv);
[rp_R7L_side JC HJ7 .. | intros md8 HJ8; rp_R7L_name].
(* 0x84334 addi a4,a4,1 *)
eapply (rp_R7L_addi W3 JP _ mem3 _ 0x84334 0x84338 0x00170713 14%bv 14%bv (Z_to_bv 12 1) 1);
[rp_R7L_side JC HJ8 .. | intros md9 HJ9; rp_R7L_name].
(* 0x84338 bnez a2,0x84314 *)
destruct (Z.eqb_spec (rp_s cx - 8 - j + -1) 0) as [L0|L0].
- (* the last turn: falls through to 0x8433c *)
eapply (rp_R7L_bne_ft W3 JP _ mem3 _ 0x84338 0x8433c 0xfc061ee3 12%bv 0%bv (Z_to_bv 13 (-36)));
[rp_R7L_side JC HJ9 .. | | intros md10 HJ10; rp_R7L_name].
{ rp_R7L_greg. rewrite HB12. unfold w64. rewrite v_addi_lit, rp_R7L_ceq by lia. apply Z.eqb_eq. exact L0. }
(* 0x8433c j 0x8434c *)
eapply (rp_R7L_jal W3 JP _ mem3 _ 0x8433c 0x8434c 0x0100006f (Z_to_bv 21 16));
[rp_R7L_side JC HJ10 .. | intros md11 HJ11; rp_R7L_name].
(* 0x8434c andi a0,a3,127 *)
eapply (rp_R7L_andi W3 JP _ mem3 _ 0x8434c 0x84350 0x07f6f513 10%bv 13%bv (Z_to_bv 12 127) 127);
[rp_R7L_side JC HJ11 .. | intros md12 HJ12; rp_R7L_name].
assert (RS : psum (ir_rec (rc_g cx)) (Z.to_nat (j + 1)) mod 128 = recsum (ir_rec (rc_g cx))).
{ unfold recsum. rewrite (rp_R7L_rec_len (rc_g cx) HLG) by lia. do 2 f_equal. lia. }
pose proof (rp_R7L_psum (ir_rec (rc_g cx)) (Z.to_nat (j + 1))) as PR1.
pose proof (Z.mod_pos_bound (psum (ir_rec (rc_g cx)) (Z.to_nat (j + 1))) 128 ltac:(lia)) as PM.
(* 0x84350 bnez a0,0x84204 *)
destruct (Z.eqb_spec (recsum (ir_rec (rc_g cx))) 0) as [R0|R0].
+ (* record sum 0: falls through to C10 (0x84354) *)
eapply (rp_R7L_bne_ft W3 JP _ mem3 _ 0x84350 (rp_pc 0x3c8) 0xea051ae3 10%bv 0%bv (Z_to_bv 13 (-332)));
[rp_R7L_side JC HJ12 .. | | intros md13 HJ13; rp_R7L_name].
{ rp_R7L_greg. rewrite HB13, PS. unfold w64. rewrite rp_R7L_and127 by lia. rewrite rp_R7L_ceq by lia.
rewrite RS. apply Z.eqb_eq. exact R0. }
refine (F10 cx pos _ ly3 S3 W3 mem3 md13 HB _).
assert (IRT : ir (rc_len cx) (rc_g cx) = true).
{ unfold ir. repeat (apply andb_true_intro; split); first [apply Z.eqb_eq | apply Z.leb_le];
first [assumption | lia]. }
unfold rp_C10.
split; [exact HJ13|].
split; [apply (rp_R7L_carry cx regs _ W3 mem3 rp_Enone rp_Enone HCA);
[unfold rp_regs_ok; rp_R7L_greg; exact HROB | intros a Ha; exact Ha]|].
split; [unfold rp_fregs; rp_R7L_greg; exact HFGB|].
split; [exact HFP|]. split; [exact HFW|]. split; [exact HSH|]. split; [exact HAR|]. split; [exact HT2|].
split; [rp_R7L_greg; exact HB11|]. exact IRT.
+ (* record sum not 0: 0x84204 li a0,0, then C11 (0x84208) *)
eapply (rp_R7L_bne_tk W3 JP _ mem3 _ 0x84350 0x84204 0xea051ae3 10%bv 0%bv (Z_to_bv 13 (-332)));
[rp_R7L_side JC HJ12 .. | | intros md13 HJ13; rp_R7L_name].
{ rp_R7L_greg. rewrite HB13, PS. unfold w64. rewrite rp_R7L_and127 by lia. rewrite rp_R7L_ceq by lia.
rewrite RS. apply Z.eqb_neq. exact R0. }
eapply (rp_R7L_addi W3 JP _ mem3 _ 0x84204 (rp_pc 0x27c) 0x00000513 10%bv 0%bv (Z_to_bv 12 0) 0);
[rp_R7L_side JC HJ13 .. | intros md14 HJ14; rp_R7L_name].
refine (F11 cx pos _ ly3 S3 W3 mem3 md14 HB _).
assert (IRF : ir (rc_len cx) (rc_g cx) = false).
{ unfold ir. rewrite (proj2 (Z.eqb_neq _ _) R0). apply andb_false_r. }
unfold rp_C11.
split; [exact HJ14|].
split; [apply (rp_R7L_carry cx regs _ W3 mem3 rp_Enone (rp_Eout cx) HCA);
[unfold rp_regs_ok; rp_R7L_greg; exact HROB | intros a []]|].
split; [unfold rp_fregs; rp_R7L_greg; exact HFGB|].
split; [exact HFP|]. split; [exact HFW|]. split; [exact HSH|]. split; [exact HAR|].
split.
* rp_R7L_greg. unfold rp_ret, reply_ret. unfold rp_argsb in HAR. rewrite HAR, IRF. unfold w64.
rewrite v_addi_lit. reflexivity.
* intros Hok'. exfalso. unfold rp_okb, reply_ok in Hok'. rewrite IRF, andb_false_r in Hok'. discriminate Hok'.
- (* another turn: back to the head (0x84314) with j + 1 *)
eapply (rp_R7L_bne_tk W3 JP _ mem3 _ 0x84338 (rp_pc 0x388) 0xfc061ee3 12%bv 0%bv (Z_to_bv 13 (-36)));
[rp_R7L_side JC HJ9 .. | | intros md10 HJ10; rp_R7L_name].
{ rp_R7L_greg. rewrite HB12. unfold w64. rewrite v_addi_lit, rp_R7L_ceq by lia. apply Z.eqb_neq. exact L0. }
apply NEXT. unfold rp_C9L.
split; [exact HJ10|].
split; [apply (rp_R7L_carry cx regs _ W3 mem3 rp_Enone rp_Enone HCA);
[unfold rp_regs_ok; rp_R7L_greg; exact HROB | intros a Ha; exact Ha]|].
split; [unfold rp_fregs; rp_R7L_greg; exact HFGB|].
split; [exact HFP|]. split; [exact HFW|]. split; [exact HSH|]. split; [exact HAR|]. split; [exact HT2|].
split; [rp_R7L_greg; exact HB11|]. split; [exact HBS|]. split; [lia|].
split; [rp_R7L_greg; rewrite HB10; unfold w64; rewrite v_addi_lit; f_equal; lia|].
split; [rp_R7L_greg; rewrite HB14; unfold w64; rewrite v_addi_lit; f_equal; lia|].
split; [rp_R7L_greg; rewrite HB12; unfold w64; rewrite v_addi_lit; f_equal; lia|].
rp_R7L_greg. rewrite HB13. exact PS. }
replace (rp_pc 0x388) with 0x84314 by (vm_compute; reflexivity).
(* 0x84314 srli a5,a0,3 *)
eapply (rp_R7L_srli W3 JP _ mem3 _ 0x84314 0x84318 0x00355793 15%bv 10%bv (Z_to_bv 6 3) 3);
[rp_R7L_side JC HJ .. | intros md1 HJ1; rp_R7L_name].
(* 0x84318 add a5,a5,s11 *)
eapply (rp_R7L_add W3 JP _ mem3 _ 0x84318 0x8431c 0x01b787b3 15%bv 15%bv 27%bv);
[rp_R7L_side JC HJ1 .. | intros md2 HJ2; rp_R7L_name].
(* 0x8431c lb a5,0(a5): the shadow byte of x *)
eapply (rp_R7L_lb W3 JP _ mem3 _ 0x8431c 0x84320 0x00078783 15%bv 15%bv (Z_to_bv 12 0) bsh);
[rp_R7L_side JC HJ2 .. | | intros md3 HJ3; rp_R7L_name].
{ rp_R7L_greg. rewrite H10, H27. unfold w64. rewrite (rp_R7L_shaddr x) by lia. apply rp_R7L_rdn. exact Emb. }
(* 0x84320 bnez a5,0x84340 *)
destruct (Z.eqb_spec sv 0) as [Sv0|Sv0].
- (* shadow byte 0: falls through to 0x84324 *)
eapply (rp_R7L_bne_ft W3 JP _ mem3 _ 0x84320 0x84324 0x02079063 15%bv 0%bv (Z_to_bv 13 32));
[rp_R7L_side JC HJ3 .. | | intros md4 HJ4; rp_R7L_name].
{ rp_R7L_greg. rewrite (rp_R7L_lbsmall bsh) by lia. rewrite Hsv, rp_R7L_ceq by lia. apply Z.eqb_eq. exact Sv0. }
apply BODY; [rp_R7L_greg; exact H10 | rp_R7L_greg; exact H14 | rp_R7L_greg; exact H12 | rp_R7L_greg; exact H13
| rp_R7L_greg; exact H11 | unfold rp_regs_ok; rp_R7L_greg; exact HRO | unfold rp_fregs; rp_R7L_greg; exact HFG
| exact HJ4].
- (* partial granule: 0x84340 andi a6,a0,7; 0x84344 blt a6,a5 is taken (x mod 8 < shadow byte) *)
eapply (rp_R7L_bne_tk W3 JP _ mem3 _ 0x84320 0x84340 0x02079063 15%bv 0%bv (Z_to_bv 13 32));
[rp_R7L_side JC HJ3 .. | | intros md4 HJ4; rp_R7L_name].
{ rp_R7L_greg. rewrite (rp_R7L_lbsmall bsh) by lia. rewrite Hsv, rp_R7L_ceq by lia. apply Z.eqb_neq. exact Sv0. }
eapply (rp_R7L_andi W3 JP _ mem3 _ 0x84340 0x84344 0x00757813 16%bv 10%bv (Z_to_bv 12 7) 7);
[rp_R7L_side JC HJ4 .. | intros md5 HJ5; rp_R7L_name].
eapply (rp_R7L_blt_tk W3 JP _ mem3 _ 0x84344 0x84324 0xfef840e3 16%bv 15%bv (Z_to_bv 13 (-32)));
[rp_R7L_side JC HJ5 .. | | intros md6 HJ6; rp_R7L_name].
{ rp_R7L_greg. rewrite H10, (rp_R7L_lbsmall bsh) by lia. rewrite Hsv. unfold w64.
rewrite rp_R7L_and7 by lia. rewrite rp_R7L_clts by (pose proof (Z.mod_pos_bound x 8 ltac:(lia)); lia).
apply Z.ltb_lt. lia. }
apply BODY; [rp_R7L_greg; exact H10 | rp_R7L_greg; exact H14 | rp_R7L_greg; exact H12 | rp_R7L_greg; exact H13
| rp_R7L_greg; exact H11 | unfold rp_regs_ok; rp_R7L_greg; exact HRO | unfold rp_fregs; rp_R7L_greg; exact HFG
| exact HJ6]. }
(* the induction on the turns left, (s - 9) - j *)
assert (LOOP : forall n j regs md, Z.to_nat (rp_s cx - 9 - j) = n -> rp_C9L cx pos j regs ly3 S3 W3 mem3 md ->
SRr SEGS W3 (cfg_at SEGS (rp_pc 0x388) regs mem3 md) (rp_post cx)).
{ induction n as [|n IH]; intros j regs md En HC.
- apply (ITER j regs md HC). intros regs' md' HC'. exfalso.
destruct HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJR & _).
destruct HC' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJR' & _). lia.
- apply (ITER j regs md HC). intros regs' md' HC'. apply (IH (j + 1) regs' md'); [|exact HC'].
destruct HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJR & _). lia. }
exact (LOOP _ j0 regs0 md0 eq_refl HC0).
Qed.

(* ---- helpers local to the rp_R7 lane ------------------------------------------------------------- *)
(* This stretch writes no memory (ss_mem of its symbolic state is []), so the run's `frame_of` with the
   empty write range gives the restricted memories pointwise equal, and every memory fact of C9 is
   transported to C9L by these lemmas. *)
Lemma rp_R7_mbyte : forall (W3 : world SEGS) (m m' : word -> option byte),
(forall x, mrestrict (w_H W3) m' x = mrestrict (w_H W3) m x) ->
forall a, mbyte SEGS (mrestrict (w_H W3) m') a = mbyte SEGS (mrestrict (w_H W3) m) a.
Proof. intros W3 m m' H a. unfold mbyte. rewrite H. reflexivity. Qed.

Lemma rp_R7_aview : forall (W3 : world SEGS) (m m' : word -> option byte),
(forall x, mrestrict (w_H W3) m' x = mrestrict (w_H W3) m x) ->
forall a, aview SEGS (w_H W3) m' a = aview SEGS (w_H W3) m a.
Proof. intros W3 m m' H a. unfold aview. rewrite (rp_R7_mbyte W3 m m' H a). reflexivity. Qed.

Lemma rp_R7_rdext : forall (W3 : world SEGS) (m m' : word -> option byte),
(forall x, mrestrict (w_H W3) m' x = mrestrict (w_H W3) m x) ->
rd_ext (aview SEGS (w_H W3) m) (aview SEGS (w_H W3) m').
Proof. intros W3 m m' H c v Hc. rewrite (rp_R7_aview W3 m m' H c). exact Hc. Qed.

Lemma rp_R7_apresent : forall (W3 : world SEGS) (m m' : word -> option byte),
(forall x, mrestrict (w_H W3) m' x = mrestrict (w_H W3) m x) ->
forall a, apresent (w_H W3) m a -> apresent (w_H W3) m' a.
Proof.
intros W3 m m' H a Ha. destruct Ha as (Hh & b & Hb). split; [exact Hh|]. exists b.
pose proof (H (Z_to_bv 64 a)) as Hx. unfold mrestrict in Hx. rewrite Hh in Hx. rewrite Hx. exact Hb.
Qed.

Lemma rp_R7_val_mem : forall (W3 : world SEGS) (m m' : word -> option byte),
(forall x, mrestrict (w_H W3) m' x = mrestrict (w_H W3) m x) ->
forall a n v, val_mem SEGS (mrestrict (w_H W3) m) a n v -> val_mem SEGS (mrestrict (w_H W3) m') a n v.
Proof. intros W3 m m' H a n v HV k Hk. rewrite (rp_R7_mbyte W3 m m' H). exact (HV k Hk). Qed.

Lemma rp_R7_garr8 : forall (W3 : world SEGS) (m m' : word -> option byte),
(forall x, mrestrict (w_H W3) m' x = mrestrict (w_H W3) m x) ->
forall p l, garr8 SEGS (mrestrict (w_H W3) m) p l -> garr8 SEGS (mrestrict (w_H W3) m') p l.
Proof.
intros W3 m m' H p l HG j Hj. destruct (HG j Hj) as [HV HR].
split; [exact (rp_R7_val_mem W3 m m' H _ _ _ HV) | exact HR].
Qed.

Lemma rp_R7_carry : forall (cx : rcx) (regs3 regs4 : bvmap 5 word) (W3 : world SEGS)
(m m' : word -> option byte),
(forall x, mrestrict (w_H W3) m' x = mrestrict (w_H W3) m x) ->
rp_regs_ok cx regs4 -> rp_carry cx regs3 W3 m rp_Enone -> rp_carry cx regs4 W3 m' rp_Enone.
Proof.
intros cx regs3 regs4 W3 m m' Hm HR4 HC.
destruct HC as (HR & HK & HSv & HMs & HOu & HRO).
destruct HK as (HW & T1 & T2 & T3 & T4 & T5 & T6).
pose proof (rp_R7_aview W3 m m' Hm) as Hav.
pose proof (rp_R7_rdext W3 m m' Hm) as Hrd.
split; [exact HR4|].
split.
{ split; [exact HW|].
  split; [intros a H1 H2 H3; rewrite Hav; exact (T1 a H1 H2 H3)|].
  split; [intros b n i H1 H2 H3; rewrite Hav; exact (T2 b n i H1 H2 H3)|].
  split; [intros a H1 H2 H3; rewrite Hav; exact (T3 a H1 H2 H3)|].
  split; [intros cid pp a H1 H2 H3; rewrite Hav; exact (T4 cid pp a H1 H2 H3)|].
  split; [intros a H1 H2 H3; exact (rp_R7_apresent W3 m m' Hm a (T5 a H1 H2 H3))|].
  intros a H1; exact (rp_R7_apresent W3 m m' Hm a (T6 a H1)). }
split.
{ unfold rp_saved in HSv |- *. eapply Forall_impl; [|exact HSv].
  intros p Hp. exact (rp_R7_val_mem W3 m m' Hm _ _ _ Hp). }
split.
{ intros H1 H2. destruct (HMs H1 H2) as (HG & U1 & U2 & U3 & U4 & U5 & U6).
  split; [exact (rp_R7_garr8 W3 m m' Hm _ _ HG)|].
  split; [intros a Ha; destruct (U1 a Ha) as [Hn Hs]; split; [rewrite Hav; exact Hn | exact Hs]|].
  split; [exact (range_addressable_ext _ _ _ _ _ Hrd U2)|].
  split; [intros s Hs; rewrite Hav; exact (U3 s Hs)|].
  split; [exact U4|]. split; [exact U5 | exact U6]. }
split.
{ intros H1. destruct (HOu H1) as (O1 & O2 & O3 & O4).
  split; [exact (range_addressable_ext _ _ _ _ _ Hrd O1)|].
  split; [exact (range_addressable_ext _ _ _ _ _ Hrd O2)|].
  split; [exact (range_addressable_ext _ _ _ _ _ Hrd O3)|].
  intros a Ha. exact (rp_R7_apresent W3 m m' Hm a (O4 a Ha)). }
intros a H1 H2 H3. rewrite Hav. exact (HRO a H1 H2 H3).
Qed.

Ltac rp_R7_in := cbn [In]; repeat first [left; reflexivity | right].

(* R7  C9 -> C10 or C11, 0x84300..0x84310 (+0x374..+0x384) and then the loop. `beqz a2` at 0x84304 is never
   taken (a2 = s - 8 >= 6), the three setup instructions give C9L at j = 0, and R7L closes it.
   Donors: A18 `join_rec0` :192. Difficulty: easy (given R7L). *)
Lemma rp_R7 : rp_from_C9L -> rp_from_C10 -> rp_from_C11 -> rp_from_C9.
Proof.
intros F9L _ _ cx pos regs3 ly3 S3 W3 mem3 md3 HBASE HC9.
destruct HC9 as (HJH & HCAR & HFREG & HFPRES & HFW & HSHD & HARGS & HTAGS2 & R11 & HBS).
pose proof HJH as (HJ & HLY & HFRM & HNIN & HABL & HCNT).
pose proof HCAR as (HREG & HKEPT & HSAV & HMSG & HOUT & HRO).
pose proof HREG as (G2 & G3 & G4 & G8 & G9 & G19 & G20 & G21 & G22 & G23 & G27).
pose proof HTAGS2 as (HTAGS & Hf0 & Hf7).
pose proof HTAGS as (HL50 & HKIND & HU16 & H12a & H12b & HSR).
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs3 []))) by apply Eimg_env.
assert (EL : forall n, (n < A_TEXT)%nat -> ew (Eimg (Ereg regs3 [])) n = ew (Ereg regs3 []) n)
by (intros n Hn; apply Eimg_low; exact Hn).
assert (E11 : ew (Eimg (Ereg regs3 [])) 11 = w64 (rp_s cx)).
{ rewrite EL by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs3 [] 11 11%bv eq_refl). exact R11. }
assert (E22 : ew (Eimg (Ereg regs3 [])) 22 = w64 (rc_fr cx)).
{ rewrite EL by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs3 [] 22 22%bv eq_refl). exact G22. }
assert (HAE : env_agree 32 (Ereg regs3 []) (Eimg (Ereg regs3 [])))
by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | reflexivity]).
unfold cfg_at.
replace (w64 (rp_pc 0x374)) with (Z_to_bv 64 (BASE + (AF_reac_ctrl_identity_reply + 0x374)))
by (unfold w64, rp_pc, A_reac_ctrl_identity_replyP; f_equal; lia).
assert (HS : st_ok_pi SEGS VAL (Eimg (Ereg regs3 []))
(mkSS (AF_reac_ctrl_identity_reply + 0x374) sr_atoms [] None (mkFacts [(11%nat, mkAF 14 23 0)] [] []))
(restrict (w_H W3)
(mkst regs3 (Z_to_bv 64 (BASE + (AF_reac_ctrl_identity_reply + 0x374))) mem3 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply (pa_entry_st_ok_full (PI := CtrlImg.PI_ctrl)).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute; reflexivity.
  - apply Forall_nil.
  - cbn; exact I.
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok]. split; [|exact I].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E11.
    unfold w64. rewrite unsigned_lit_small by lia.
    rewrite Z.pow_0_r, Z.mod_1_r. lia. }
assert (SHOK : sh_ok SEGS (SOff 27 0) (@nil shent) (Eimg (Ereg regs3 []))
(mrestrict (w_H W3) mem3)) by apply Forall_nil.
pose (RUNTO := paj_run_to B LAWS).
paj_run_to_tok RUNTO HS HJ SHOK (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1)
(AF_reac_ctrl_identity_reply + 0x388).
- apply awr_ok_nil.
- match goal with H : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ => rename H into HFRm end.
  match goal with H : st_ok_pi _ _ _ _ (restrict _ _) |- _ => rename H into HSx end.
  match goal with H : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => rename H into HJx end.
  assert (Hmeq : forall x, mrestrict (w_H W3) (ms_mem ms) x = mrestrict (w_H W3) mem3 x)
  by (intros x; apply HFRm; intros Hw; destruct Hw as (r & Hin & _); destruct Hin).
  prreg HSx (10%bv : bv 5) P10.
  prreg HSx (12%bv : bv 5) P12.
  prreg HSx (13%bv : bv 5) P13.
  prreg HSx (14%bv : bv 5) P14.
  assert (RK : forall r : bv 5, In r
  [(2%bv : bv 5); 3%bv; 4%bv; 8%bv; 9%bv; 11%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv;
  25%bv; 26%bv; 27%bv] -> getr (ms_regs ms) r = getr regs3 r).
  { lazymatch type of HSx with st_ok_pi _ _ ?Ev _ _ =>
    eapply (regs_kept_of_st_ok_pi Ev _ _ regs3 [] _ HSx) end.
    - exact HAE.
    - vm_compute; reflexivity. }
  assert (Hfr64 : 0 <= rc_fr cx < 2 ^ 64) by (unfold rp_base in HBASE; tauto).
  assert (F22 : ew (Ereg regs3 []) 22 = w64 (rc_fr cx))
  by (rewrite (ew_Ereg_nat regs3 [] 22 22%bv eq_refl); exact G22).
  assert (F11 : ew (Ereg regs3 []) 11 = w64 (rp_s cx))
  by (rewrite (ew_Ereg_nat regs3 [] 11 11%bv eq_refl); exact R11).
  unfold A_TEXT, A_LIM in P10, P12, P14.
  cbn [Nat.leb Nat.ltb andb] in P10, P12, P14.
  rewrite F22 in P10, P14. rewrite F11 in P12.
  unfold w64 in P10, P12, P14.
  rewrite unsigned_lit_small in P10, P14 by lia.
  rewrite unsigned_lit_small in P12 by lia.
  assert (Hms : ms = mkst (ms_regs ms)
  (Z_to_bv 64 (BASE + (AF_reac_ctrl_identity_reply + 0x388))) (ms_mem ms) (seg_rom SEGS))
  by exact (st_ok_pi_restrict_mkst (w_H W3) _ _ _ HSx eq_refl).
  rewrite Hms.
  replace (Z_to_bv 64 (BASE + (AF_reac_ctrl_identity_reply + 0x388))) with (w64 (rp_pc 0x388))
  by (unfold w64, rp_pc, A_reac_ctrl_identity_replyP; f_equal; lia).
  apply (F9L cx pos 0 (ms_regs ms) ly3 S3 W3 (ms_mem ms) _ HBASE).
  assert (HR4 : rp_regs_ok cx (ms_regs ms)).
  { unfold rp_regs_ok. repeat split; rewrite RK by rp_R7_in; assumption. }
  split.
  { split; [exact HJx|]. split; [exact HLY|]. split; [exact HFRM|].
    split; [exact HNIN|]. split; [exact HABL | exact HCNT]. }
  split; [exact (rp_R7_carry cx regs3 (ms_regs ms) W3 mem3 (ms_mem ms) Hmeq HR4 HCAR)|].
  split.
  { unfold rp_fregs in HFREG |- *. repeat split; rewrite RK by rp_R7_in; tauto. }
  split.
  { intros a Ha. exact (rp_R7_apresent W3 mem3 (ms_mem ms) Hmeq a (HFPRES a Ha)). }
  split.
  { destruct HFW as (F1 & F2 & F3 & F4).
    split; [exact (rp_R7_val_mem W3 mem3 (ms_mem ms) Hmeq _ _ _ F1)|].
    split; [exact (rp_R7_val_mem W3 mem3 (ms_mem ms) Hmeq _ _ _ F2)|].
    split; [exact (rp_R7_val_mem W3 mem3 (ms_mem ms) Hmeq _ _ _ F3)|].
    rewrite (rdword_ext (aview SEGS (w_H W3) mem3) (aview SEGS (w_H W3) (ms_mem ms))
    (rp_G cx pos + 120) (fun k _ => rp_R7_aview W3 mem3 (ms_mem ms) Hmeq (rp_G cx pos + 120 + k))).
    exact F4. }
  split.
  { unfold rp_shadow in HSHD |- *.
    exact (shadow_cells_ext _ _ _ _ _ (rp_R7_rdext W3 mem3 (ms_mem ms) Hmeq) HSHD). }
  split; [exact HARGS|].
  split; [exact HTAGS2|].
  split; [rewrite RK by rp_R7_in; exact R11|].
  split; [exact HBS|].
  split; [lia|].
  split; [rewrite P10; unfold w64; f_equal; cbn [Z.to_nat]; lia|].
  split; [rewrite P14; unfold w64; f_equal; cbn [Z.to_nat]; lia|].
  split; [rewrite P12; unfold w64; f_equal; cbn [Z.to_nat]; lia|].
  rewrite P13; unfold w64; f_equal; cbn [Z.to_nat psum]; reflexivity.
Qed.

(* ---- rp_R8's local helpers (local to the stretch) ---------------------------------------------------- *)
(* The symbolic state at C10. Atoms: registers 0..31 (Ereg), 32 / 33 = the message bytes fr[36] / fr[37];
   s11 (atom 27) holds SHADOW_OFF and is the shadow base of the token engine. Regions: the two message bytes
   (read-only) and the three caller cells pa (2), pp (8), pn (8), writable. *)
Definition rp_R8_regions : smem := [
YP09.mkRegion (Some 22%nat) 36 38 0 0 [YP09.mkChunk 36 (CVal 1 (SOff 32 0)); YP09.mkChunk 37 (CVal 1 (SOff 33 0))];
YP09.mkRegion (Some 21%nat) 0 2 0 2 [];
YP09.mkRegion (Some 20%nat) 0 8 0 8 [];
YP09.mkRegion (Some 19%nat) 0 8 0 8 [] ].
Definition rp_R8_facts : facts :=
mkFacts [(27%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (22%nat, mkAF 0 (2 ^ 47 - 51) 0); (21%nat, mkAF 0 (2 ^ 47 - 2) 1);
(20%nat, mkAF 0 (2 ^ 47 - 8) 3); (19%nat, mkAF 0 (2 ^ 47 - 8) 3); (32%nat, mkAF 0 255 0); (33%nat, mkAF 0 255 0)] [] [].
Definition rp_R8_ss : sstate := mkSS (AF_reac_ctrl_identity_reply + 0x3c8) sr_atoms rp_R8_regions None rp_R8_facts.
(* the shadow the stretch's checks read: the 50 message bytes and the three cells (rp_msg / rp_out). *)
Definition rp_R8_SH : list shent := [mkSHE 22 0 50; mkSHE 21 0 2; mkSHE 20 0 8; mkSHE 19 0 8].
Definition rp_R8_span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* A caller's right to let the call write a byte (twr_ok, over `own` and `lyc`) is a right of the stretch's
   journal (over `(1, pos) :: own` and ly3, which has the same ly_F). *)
Lemma rp_R8_awr : forall STK sp0 FP bl0 blc (ly ly' : alayout) own c a,
ly_F ly' = ly_F ly -> awr_byte STK sp0 FP bl0 blc ly own a -> awr_byte STK sp0 FP bl0 blc ly' (c :: own) a.
Proof.
intros STK sp0 FP bl0 blc ly ly' own c a HF [H | [H | [H | (cid & p & Hin & Hz)]]].
- left. exact H.
- right. left. exact H.
- right. right. left. exact H.
- right. right. right. exists cid, p. split; [right; exact Hin|]. unfold frame_addr in *. rewrite HF. exact Hz.
Qed.
(* byte equality from equality mod 256 *)
Lemma rp_R8_zbyte : forall x y, x mod 256 = y mod 256 -> Z_to_bv 8 x = Z_to_bv 8 y.
Proof. intros x y H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. exact H. Qed.
(* the `slli 8; or` of two bytes is their sum (same fact as Reusable/YK0w.v lor_shiftl8, operands swapped) *)
Lemma rp_R8_lor : forall a b, 0 <= a -> 0 <= b < 256 -> Z.lor (a * 256) b = a * 256 + b.
Proof.
intros a b Ha Hb.
assert (Hl : Z.land (a * 256) b = 0).
{ apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
destruct (Z.ltb_spec n 8) as [Hn8|Hn8].
- change 256 with (2 ^ 8). rewrite Z.mul_pow2_bits_low by lia. reflexivity.
- replace (Z.testbit b n) with false; [apply andb_false_r|].
symmetry. apply Z.testbit_false; [lia|]. rewrite Z.div_small; [reflexivity|].
split; [lia|]. apply (Z.lt_le_trans _ 256); [lia|]. change 256 with (2 ^ 8). apply Z.pow_le_mono_r; lia. }
rewrite <- Z.lxor_lor by exact Hl. rewrite <- Z.add_nocarry_lxor by exact Hl. reflexivity.
Qed.
Lemma rp_R8_bytes2 : forall a b, 0 <= a < 256 -> 0 <= b < 256 ->
(a * 256 + b) mod 256 = b /\ Z.shiftr (a * 256 + b) 8 mod 256 = a.
Proof.
intros a b Ha Hb. split.
- rewrite Z.add_comm, Z_mod_plus_full. apply Z.mod_small. lia.
- rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
rewrite Z.add_comm, Z.div_add by lia. rewrite (Z.div_small b 256) by lia. rewrite Z.add_0_l. apply Z.mod_small. lia.
Qed.
Lemma rp_R8_le1 : forall b, 0 <= b < 256 -> YO0f.le_byte b 1 0 = b.
Proof.
intros b Hb. unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. rewrite (Z.mod_small b (2 ^ 8)) by (change (2 ^ 8) with 256; lia). apply Z.mod_small. lia.
Qed.
(* an 8-byte chunk of the symbolic memory is an 8-byte value of the concrete one (as Reusable/YI67.v
   val_mem_low_of_chunk, for n = 8 and a value below 2^64) *)
Lemma rp_R8_vm8 : forall E m base off e v,
YP09.chunk_ok SEGS E m base (YP09.mkChunk off (CVal 8 e)) -> bv_unsigned (sv_denot E e) = v -> 0 <= v < 2 ^ 64 ->
val_mem SEGS m (base + off) 8 v.
Proof.
intros E m base off e v H Hv Hr k Hk.
destruct (H (Z.of_nat k)) as (b & Hb1 & Hb2); [cbn [YP09.c_len YP09.cv_len YP09.c_val Z.of_N]; lia|].
cbn [YP09.cbyte YP09.c_off YP09.c_val] in Hb1, Hb2. unfold YP09.byte_of_word in Hb1. injection Hb1 as <-.
rewrite Hb2, Hv. f_equal. apply rp_R8_zbyte. unfold YO0f.le_byte.
change (8 * Z.of_nat 8) with 64. rewrite (Z.mod_small v (2 ^ 64)) by lia. rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma rp_R8_rdword : forall (rd rd' : reader) a, (forall i, 0 <= i < 8 -> rd' (a + i) = rd (a + i)) ->
rdword rd' a = rdword rd a.
Proof.
intros rd rd' a H. unfold rdword.
pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
rewrite H0, (H 1), (H 2), (H 3), (H 4), (H 5), (H 6), (H 7) by lia. reflexivity.
Qed.
Lemma rp_R8_shx : forall x, 0 <= x < 2 ^ 47 ->
SHADOW_OFF <= shadow_of_addr SHADOW_OFF x < SHADOW_OFF + 17592186044416.
Proof.
intros x Hx. unfold shadow_of_addr.
assert (0 <= x / 8) by (apply Z.div_pos; lia).
assert (x / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
lia.
Qed.

(* R8  C10 -> C11, 0x84354..0x843d4 (+0x3c8..+0x448). Reads fr[36], fr[37] (shadow checks from rp_msg), then
   the three stores: `sh a0,0(s5)` = pa gets (g36 << 8) | g37 = reply_addr g, `sd a0,0(s4)` = pp gets fr + 38,
   `sd a1,0(s3)` = pn gets s - 13 (a1 still holds s since 0x84160). Each store is preceded by its shadow check,
   discharged from rp_out's range_addressable; the writes are justified by the three `twr_ok` of rp_base
   (the `in_frames own` case of `awr_byte`), so the journal and `tcj_kept ... (rp_Eout cx)` extend. a0 := 1 and
   `j 0x84208`. The error calls 0x8442c..0x8444c are not reached.
   Donors: B `rp_stores` :3629, `rr_shadow0` :3434, `rOUTW` :3456; A18 `seg_stores` :3185. Difficulty: HARD
   (three caller writes through the journal; this is where twr_ok is spent). *)

(* R8  C10 -> C11, 0x84354..0x843d4 (+0x3c8..+0x448). Reads fr[36], fr[37] (shadow checks from rp_msg), then
   the three stores: `sh a0,0(s5)` = pa gets (g36 << 8) | g37 = reply_addr g, `sd a0,0(s4)` = pp gets fr + 38,
   `sd a1,0(s3)` = pn gets s - 13 (a1 still holds s since 0x84160). Each store is preceded by its shadow check,
   discharged from rp_out's range_addressable; the writes are justified by the three `twr_ok` of rp_base
   (the `in_frames own` case of `awr_byte`), so the journal and `tcj_kept ... (rp_Eout cx)` extend. a0 := 1 and
   `j 0x84208`. The error calls 0x8442c..0x8444c are not reached.
   Donors: B `rp_stores` :3629, `rr_shadow0` :3434, `rOUTW` :3456; A18 `seg_stores` :3185. Difficulty: HARD
   (three caller writes through the journal; this is where twr_ok is spent). *)
Lemma rp_R8 : rp_from_C11 -> rp_from_C10.
Proof.
intros F11 cx pos regs3 ly3 S3 W3 mem3 md3 HB HC.
pose proof HB as HB0.
destruct cx as [STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fr len pa pp pn g].
unfold rp_C10, rp_base, rp_jhold, rp_carry, rp_regs_ok, rp_kept, rp_saved, rp_msg, rp_out, rp_fregs, rp_fpres,
rp_fwords, rp_shadow, rp_tags2, rp_tags, rp_argsb, rp_S, rp_rA, rp_G, rp_FL, rp_own1, rp_s, rp_ly_ok in HB, HC.
cbn [rc_STK rc_sp0 rc_FP rc_ly rc_S rc_W0 rc_mem0 rc_md0 rc_own rc_lyc rc_Sc rc_W rc_memc rc_mdc rc_k rc_regs
rc_fr rc_len rc_pa rc_pp rc_pn rc_g] in HB, HC.
destruct HB as (HJ0 & HROD0 & Hra0 & Hra4 & Hgp0 & Htp0 & G10 & G11 & G12 & G13 & G14 & Rfr & Rlen & Rpa & Rpp & Rpn
& Hal16 & Hwlo & Hwhi & Hroom & Hlg & HMSG0 & HOUT0).
destruct HC as ((HJ & (HLF & HLT) & HFRS & HNIN & HABL & HCNT) & (HRG & (HWLE & HKP) & HSV & HMSG & HOUT & HROD)
& HFR & HFP & HFW & HSHD & HARG & HTG2 & H11 & HIR).
destruct HTG2 as ((Hlen50 & Hkind & H3435 & H32 & H33 & Hsr) & H27 & Hf7).
destruct (HMSG HARG Hlen50) as (HGM & HTS). clear HMSG.
destruct (HOUT HARG) as (HRApa & HRApp & HRApn & HPRES). clear HOUT.
destruct (HMSG0 HARG Hlen50) as ((nb & Hblk & Hnb) & HTS0 & HGM0). clear HMSG0.
destruct (HOUT0 HARG) as (Hpa2 & Hpp8 & Hpn8 & Dapp & Dapn & Dppn & HCELL & TWa & TWp & TWn & RAa0 & RAp0 & RAn0).
clear HOUT0.
destruct HRG as (R2 & R3 & R4 & R8 & R9 & R19 & R20 & R21 & R22 & R23 & R27).
destruct HFR as (R18 & R26 & R25).
pose proof HJ0 as (HAR0 & _).
pose proof HJ as (HAR3 & _).
pose proof HTS as (HTSv & HRAfr & HHULL & HAMEM & Hfr0 & Hfr63).
(* disjunctive facts are kept under a binder so that `lia` does not split on them everywhere *)
assert (DISJ : forall _ : unit, (pa + 2 <= pp \/ pp + 8 <= pa) /\ (pa + 2 <= pn \/ pn + 8 <= pa) /\
(pp + 8 <= pn \/ pn + 8 <= pp)) by (intros _; auto).
clear Dapp Dapn Dppn.
assert (HOK : reply_ok fr len pa pp pn g = true) by (unfold reply_ok; rewrite HARG, HIR; reflexivity).
assert (FB1 : fs_frame_bytes 1 = 128) by reflexivity.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (Hfr47 : fr + 51 <= 2 ^ 47)
by (clear - HAMEM; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HAMEM; lia).
assert (HfrS : forall x, fr <= x < fr + 50 -> ~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416))
by (intros x Hx; clear - HAMEM Hx; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HAMEM;
unfold SHADOW_OFF; lia).
(* every byte of the three cells lies in a frame of Sc: in application memory, below alloc_ceiling, not in the
   image, apart from the message block, from this function's own frame and from the stack window below S. *)
assert (CELLA : forall a, treply_out pa pp pn a ->
4096 <= a < alloc_ceiling /\ (a < SHADOW_OFF \/ SHADOW_OFF + 17592186044416 <= a) /\
(a < fr \/ fr + 50 <= a) /\ (a < frame_addr lyc 1 pos \/ frame_addr lyc 1 pos + 128 <= a) /\
(a < spZ regs - ESTACK \/ spZ regs <= a)).
{ intros a Ha. destruct (HCELL a Ha) as (cid & p & Hin & Hz).
unfold in_zr, frame_rng in Hz. cbn [fst snd] in Hz.
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid p HAR0 Hin) as (Hf0 & Hfc & Happ).
pose proof (sep_block_frame SEGS B LAWS lyc Sc W memc mdc fr nb cid p HAR0 Hblk Hin) as Hsep.
destruct (in_split _ _ Hin) as (l2 & l3 & El).
assert (El3 : frames S3 = [] ++ (1, pos) :: l2 ++ (cid, p) :: l3) by (rewrite HFRS, El; reflexivity).
pose proof (sep_frames_pos SEGS B LAWS ly3 S3 W3 mem3 md3 (1, pos) (cid, p) [] l2 l3 HAR3 El3) as Hsep2.
unfold zdisjoint, frame_rng in Hsep, Hsep2. cbn [fst snd] in Hsep, Hsep2.
unfold frame_addr in Hsep2, Hsep, Hz, Hf0, Hfc, Happ |- *. rewrite HLF in Hsep2. rewrite FB1 in Hsep2.
assert (Hst : ~ (spZ regs - ESTACK <= a < spZ regs)).
{ unfold treply_out in Ha. destruct Ha as [Ha | [Ha | Ha]];
[destruct (TWa a Ha) as (_ & _ & _ & Hn) | destruct (TWp a Ha) as (_ & _ & _ & Hn)
| destruct (TWn a Ha) as (_ & _ & _ & Hn)]; exact Hn. }
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
pose proof (fs_frame_bytes_nonneg cid) as Hfb.
clear - Hz Hf0 Hfc Happ Hsep Hsep2 Hst Hnb Hfb. unfold SHADOW_OFF. lia. }
assert (CELLI : forall a, treply_out pa pp pn a -> ~ in_img SEGS a).
{ intros a Ha. destruct (HCELL a Ha) as (cid & p & Hin & Hz).
unfold in_zr, frame_rng in Hz. cbn [fst snd] in Hz.
refine (proj2 (al_client_img _ _ LAWS lyc Sc W memc mdc a HAR0 _)).
right. left. exists cid, p. split; [exact Hin | exact Hz]. }
assert (Bpa : 4096 <= pa /\ pa + 2 <= alloc_ceiling).
{ destruct (CELLA pa ltac:(left; lia)) as (K0 & _). destruct (CELLA (pa + 1) ltac:(left; lia)) as (K1 & _).
clear - K0 K1. lia. }
assert (Bpp : 4096 <= pp /\ pp + 8 <= alloc_ceiling).
{ destruct (CELLA pp ltac:(right; left; lia)) as (K0 & _). destruct (CELLA (pp + 7) ltac:(right; left; lia)) as (K1 & _).
clear - K0 K1. lia. }
assert (Bpn : 4096 <= pn /\ pn + 8 <= alloc_ceiling).
{ destruct (CELLA pn ltac:(right; right; lia)) as (K0 & _). destruct (CELLA (pn + 7) ltac:(right; right; lia)) as (K1 & _).
clear - K0 K1. lia. }
assert (Mpa : fr + 38 <= pa \/ pa + 2 <= fr + 36).
{ destruct (CELLA pa ltac:(left; lia)) as (_ & _ & K0 & _). destruct (CELLA (pa + 1) ltac:(left; lia)) as (_ & _ & K1 & _).
clear - K0 K1. lia. }
assert (Mpp : fr + 38 <= pp \/ pp + 8 <= fr + 36).
{ destruct (CELLA pp ltac:(right; left; lia)) as (_ & _ & K0 & _).
destruct (CELLA (pp + 7) ltac:(right; left; lia)) as (_ & _ & K1 & _). clear - K0 K1. lia. }
assert (Mpn : fr + 38 <= pn \/ pn + 8 <= fr + 36).
{ destruct (CELLA pn ltac:(right; right; lia)) as (_ & _ & K0 & _).
destruct (CELLA (pn + 7) ltac:(right; right; lia)) as (_ & _ & K1 & _). clear - K0 K1. lia. }
assert (DISM : forall _ : unit, (fr + 38 <= pa \/ pa + 2 <= fr + 36) /\ (fr + 38 <= pp \/ pp + 8 <= fr + 36) /\
(fr + 38 <= pn \/ pn + 8 <= fr + 36)) by (intros _; auto).
clear Mpa Mpp Mpn.
(* the message bytes 36 / 37 at mem3 *)
assert (GB : forall j, (j < 50)%nat -> val_mem SEGS (mrestrict (w_H W3) mem3) (fr + Z.of_nat j) 1 (cp_v g j)).
{ intros j Hj. destruct (HGM j ltac:(rewrite length_map; lia)) as [Hv _].
rewrite (nth_indep _ 0 (bv_unsigned cp_z)) in Hv by (rewrite length_map; lia).
rewrite map_nth in Hv. exact Hv. }
pose (g36 := cp_v g 36). pose (g37 := cp_v g 37).
assert (Hg36 : 0 <= g36 < 256) by apply cp_v_range'.
assert (Hg37 : 0 <= g37 < 256) by apply cp_v_range'.
(* the valuation of the symbolic state *)
pose (E := Eimg (L := ctrl_listing) (PI := CtrlImg.PI_ctrl) (Ereg regs3 [Z_to_bv 64 g36; Z_to_bv 64 g37])).
assert (HEI : img_env VAL A_LIM E) by apply Eimg_env.
assert (HREG : regs_ok E sr_atoms regs3) by apply regs_ok_Eimg_Ereg.
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs3 [Z_to_bv 64 g36; Z_to_bv 64 g37]) n)
by (intros n Hn; apply Eimg_low; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 g36) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 g37) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 1)).
assert (ER : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs3 r)
by (intros n r Hn Hr; rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hr).
clearbody E. clear EL.
assert (V22 : bv_unsigned (ew E 22) = fr)
by (rewrite (ER 22%nat 22%bv) by first [lia | reflexivity]; rewrite R22; unfold w64; apply unsigned_lit_small; lia).
assert (V21 : bv_unsigned (ew E 21) = pa)
by (rewrite (ER 21%nat 21%bv) by first [lia | reflexivity]; rewrite R21; unfold w64; apply unsigned_lit_small; lia).
assert (V20 : bv_unsigned (ew E 20) = pp)
by (rewrite (ER 20%nat 20%bv) by first [lia | reflexivity]; rewrite R20; unfold w64; apply unsigned_lit_small; lia).
assert (V19 : bv_unsigned (ew E 19) = pn)
by (rewrite (ER 19%nat 19%bv) by first [lia | reflexivity]; rewrite R19; unfold w64; apply unsigned_lit_small; lia).
assert (V27 : bv_unsigned (ew E 27) = SHADOW_OFF)
by (rewrite (ER 27%nat 27%bv) by first [lia | reflexivity]; rewrite R27; unfold w64; apply unsigned_lit_small;
unfold SHADOW_OFF; lia).
assert (V32 : bv_unsigned (ew E 32) = g36) by (rewrite E32; apply unsigned_lit_small; lia).
assert (V33 : bv_unsigned (ew E 33) = g37) by (rewrite E33; apply unsigned_lit_small; lia).
assert (UA : forall n v, bv_unsigned (ew E n) = v -> U E (SOff n 0) = v).
{ intros n v Hv. unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact Hv. }
assert (V11 : bv_unsigned (ew E 11) = ir_s g)
by (rewrite (ER 11%nat 11%bv) by first [lia | reflexivity]; rewrite H11; unfold w64; apply unsigned_lit_small;
pose proof (cp_v_range' g 26); unfold ir_s; lia).
pose proof HJ0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _ & _).
destruct Hstk as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof rp_stk as (Tstk & Pstk).
assert (HSb : alloc_ceiling + TREPLY_STK <= spZ regs <= 2 ^ 47)
by (clear - Hceil Hslo Hshi H47 Hwlo Hwhi; lia).
assert (HG0 : 4096 <= frame_addr lyc 1 pos /\ frame_addr lyc 1 pos + 128 <= alloc_ceiling).
{ assert (Hin1 : In (1, pos) (frames S3)) by (rewrite HFRS; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 mem3 md3 1 pos HAR3 Hin1) as (Hf0 & Hfc & _).
unfold frame_addr in Hf0, Hfc |- *. rewrite HLF in Hf0, Hfc. rewrite FB1 in Hfc. lia. }
(* the symbolic state at C10 *)
assert (HS : st_ok_pi SEGS VAL E rp_R8_ss
(restrict (w_H W3) (mkst regs3 (Z_to_bv 64 (BASE + (AF_reac_ctrl_identity_reply + 0x3c8))) mem3 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold rp_R8_ss. apply (pa_entry_st_ok_full (PI := CtrlImg.PI_ctrl)).
- exact HREG.
- vm_compute. reflexivity.
- unfold rp_R8_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
+ rewrite V22. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor; [|constructor]].
* apply (chunk_ok_val SEGS E _ fr 36 1 (SOff 32 0) g36);
[cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
exact (GB 36%nat ltac:(lia)).
* apply (chunk_ok_val SEGS E _ fr 37 1 (SOff 33 0) g37);
[cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
exact (GB 37%nat ltac:(lia)).
+ rewrite V21. split; [lia|]. split; [lia|].
split; [intros o Ho; apply (apresent_writable SEGS); apply HPRES; unfold treply_out; lia | constructor].
+ rewrite V20. split; [lia|]. split; [lia|].
split; [intros o Ho; apply (apresent_writable SEGS); apply HPRES; unfold treply_out; lia | constructor].
+ rewrite V19. split; [lia|]. split; [lia|].
split; [intros o Ho; apply (apresent_writable SEGS); apply HPRES; unfold treply_out; lia | constructor].
- apply pairwise_disjoint_of_extents.
unfold rp_R8_regions, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
rewrite V22, V21, V20, V19.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
destruct (DISJ tt) as (DJ1 & DJ2 & DJ3). destruct (DISM tt) as (DM1 & DM2 & DM3).
clear - DJ1 DJ2 DJ3 DM1 DM2 DM3. repeat split; lia.
- split; [|split; exact I].
unfold rp_R8_facts. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite V27, V22, V21, V20, V19, V32, V33.
change (2 ^ 0) with 1. change (2 ^ 1) with 2. change (2 ^ 3) with 8. rewrite !Z.mod_1_r.
unfold SHADOW_OFF. clear - Hfr0 Hfr47 Bpa Bpp Bpn C1 Hpa2 Hpp8 Hpn8 Hg36 Hg37. repeat split; lia. }
assert (SHOK : sh_ok SEGS (SOff 27 0) rp_R8_SH E (mrestrict (w_H W3) mem3)).
{ pose proof (UA 27%nat _ V27) as UB.
unfold sh_ok, rp_R8_SH. repeat apply Forall_cons; try apply Forall_nil.
- apply (shent_ok_of_range SEGS (w_H W3) mem3 E (SOff 27 0) 22 fr 50 fr 0 50 HRAfr UB (UA 22%nat _ V22));
[lia | lia |]. intros x Hx. cbn [Z.min Z.max] in Hx. apply HfrS. lia.
- apply (shent_ok_of_range SEGS (w_H W3) mem3 E (SOff 27 0) 21 pa 2 pa 0 2 HRApa UB (UA 21%nat _ V21));
[lia | lia |]. intros x Hx. cbn [Z.min Z.max] in Hx.
destruct (CELLA x ltac:(left; lia)) as (_ & KS & _). clear - KS. lia.
- apply (shent_ok_of_range SEGS (w_H W3) mem3 E (SOff 27 0) 20 pp 8 pp 0 8 HRApp UB (UA 20%nat _ V20));
[lia | lia |]. intros x Hx. cbn [Z.min Z.max] in Hx.
destruct (CELLA x ltac:(right; left; lia)) as (_ & KS & _). clear - KS. lia.
- apply (shent_ok_of_range SEGS (w_H W3) mem3 E (SOff 27 0) 19 pn 8 pn 0 8 HRApn UB (UA 19%nat _ V19));
[lia | lia |]. intros x Hx. cbn [Z.min Z.max] in Hx.
destruct (CELLA x ltac:(right; right; lia)) as (_ & KS & _). clear - KS. lia. }
unfold cfg_at.
replace (w64 (rp_pc 0x3c8)) with (Z_to_bv 64 (BASE + (AF_reac_ctrl_identity_reply + 0x3c8)))
by (unfold w64, rp_pc, A_reac_ctrl_identity_replyP; f_equal; lia).
pose proof (paj_run_to (PL := PL_ctrl) (PI := CtrlImg.PI_ctrl) B LAWS) as RUNTO.
paj_run_to_tok RUNTO HS HJ SHOK rp_R8_span (AF_reac_ctrl_identity_reply + 0x27c).
- (* the writes: the three cells, by the caller's twr_ok *)
unfold rp_R8_ss, rp_R8_regions. cbn [ss_mem]. rewrite HABL.
apply awr_ok_cons_ro; [cbn; lia|].
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 21%nat pa); [reflexivity | exact V21 | |].
{ cbn [YP09.r_wlo YP09.r_whi]. intros a Ha.
apply (rp_R8_awr STK sp0 FP _ _ lyc ly3 own (1, pos) a HLF). exact (proj1 (TWa a ltac:(lia))). }
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 20%nat pp); [reflexivity | exact V20 | |].
{ cbn [YP09.r_wlo YP09.r_whi]. intros a Ha.
apply (rp_R8_awr STK sp0 FP _ _ lyc ly3 own (1, pos) a HLF). exact (proj1 (TWp a ltac:(lia))). }
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 19%nat pn); [reflexivity | exact V19 | |].
{ cbn [YP09.r_wlo YP09.r_whi]. intros a Ha.
apply (rp_R8_awr STK sp0 FP _ _ lyc ly3 own (1, pos) a HLF). exact (proj1 (TWn a ltac:(lia))). }
apply awr_ok_nil.
- (* the state at 0x84208 (C11) *)
prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10.
prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20.
prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23.
prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
rewrite (ER 2%nat 2%bv) in Q2 by first [lia | reflexivity].
rewrite (ER 3%nat 3%bv) in Q3 by first [lia | reflexivity].
rewrite (ER 4%nat 4%bv) in Q4 by first [lia | reflexivity].
rewrite (ER 8%nat 8%bv) in Q8 by first [lia | reflexivity].
rewrite (ER 9%nat 9%bv) in Q9 by first [lia | reflexivity].
rewrite (ER 18%nat 18%bv) in Q18 by first [lia | reflexivity].
rewrite (ER 19%nat 19%bv) in Q19 by first [lia | reflexivity].
rewrite (ER 20%nat 20%bv) in Q20 by first [lia | reflexivity].
rewrite (ER 21%nat 21%bv) in Q21 by first [lia | reflexivity].
rewrite (ER 22%nat 22%bv) in Q22 by first [lia | reflexivity].
rewrite (ER 23%nat 23%bv) in Q23 by first [lia | reflexivity].
rewrite (ER 25%nat 25%bv) in Q25 by first [lia | reflexivity].
rewrite (ER 26%nat 26%bv) in Q26 by first [lia | reflexivity].
rewrite (ER 27%nat 27%bv) in Q27 by first [lia | reflexivity].
pose proof (st_ok_mem_ok SEGS _ _ _ HS) as HMO. cbn [abs_ss setpc ss_mem restrict ms_mem] in HMO.
destruct HMO as (_ & HMO & _).
apply Forall_inv_tail in HMO.
pose proof (Forall_inv HMO) as Hrpa. apply Forall_inv_tail in HMO.
pose proof (Forall_inv HMO) as Hrpp. apply Forall_inv_tail in HMO.
pose proof (Forall_inv HMO) as Hrpn. clear HMO.
destruct Hrpa as (_ & _ & _ & Hcpa). destruct Hrpp as (_ & _ & _ & Hcpp). destruct Hrpn as (_ & _ & _ & Hcpn).
cbn [YP09.r_base YP09.r_chunks base_val] in Hcpa, Hcpp, Hcpn.
rewrite !ew_ewset_other in Hcpa, Hcpp, Hcpn by lia.
rewrite V21 in Hcpa. rewrite V20 in Hcpp. rewrite V19 in Hcpn.
apply Forall_inv in Hcpa. apply Forall_inv in Hcpp. apply Forall_inv in Hcpn.
pmkst HS.
set (regs' := ms_regs ms) in *. set (mem' := ms_mem ms) in *.
set (md' := with_vm_backing (m_vm_lazy md3) mat md3) in *.
match goal with |- context [Z_to_bv 64 (?b + 13100)] =>
replace (Z_to_bv 64 (b + 13100)) with (w64 (rp_pc 0x27c))
by (unfold w64, rp_pc, A_reac_ctrl_identity_replyP, AF_reac_ctrl_identity_reply; f_equal; lia) end.
apply (F11 _ pos regs' ly3 S3 W3 mem' md' HB0).
(* memory off the three cells is unchanged *)
assert (HMB : forall a, 0 <= a < 2 ^ 64 -> ~ treply_out pa pp pn a ->
mrestrict (w_H W3) mem' (Z_to_bv 64 a) = mrestrict (w_H W3) mem3 (Z_to_bv 64 a)).
{ intros a Ha Hn. apply HFr. rewrite unsigned_lit_small by lia.
intros (r & Hin & Hr).
unfold rp_R8_ss, rp_R8_regions in Hin. cbn [ss_mem In] in Hin.
apply Hn. unfold treply_out.
destruct Hin as [<- | [<- | [<- | [<- | []]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
rewrite ?V21, ?V20, ?V19 in Hr; lia. }
assert (HEQ : forall a, 0 <= a < 2 ^ 64 -> ~ treply_out pa pp pn a ->
aview SEGS (w_H W3) mem' a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha Hn. unfold aview, YP09.mbyte. rewrite (HMB a Ha Hn). reflexivity. }
unfold rp_C11, rp_jhold, rp_carry, rp_regs_ok, rp_kept, rp_saved, rp_msg, rp_out, rp_fregs, rp_fpres, rp_fwords,
rp_shadow, rp_argsb, rp_S, rp_rA, rp_G, rp_FL, rp_own1, rp_ly_ok, rp_Eout, rp_okb, rp_ret, rp_cells, rp_s.
cbn [rc_STK rc_sp0 rc_FP rc_ly rc_S rc_W0 rc_mem0 rc_md0 rc_own rc_lyc rc_Sc rc_W rc_memc rc_mdc rc_k rc_regs
rc_fr rc_len rc_pa rc_pp rc_pn rc_g].
destruct HKP as (K1 & K2 & K3 & K4 & K5 & K6).
split.
{ split; [exact HJ|]. split; [exact (conj HLF HLT)|]. split; [exact HFRS|]. split; [exact HNIN|].
split; [exact HABL | exact HCNT]. }
split.
{ split.
{ rewrite Q2, Q3, Q4, Q8, Q9, Q19, Q20, Q21, Q22, Q23, Q27.
exact (conj R2 (conj R3 (conj R4 (conj R8 (conj R9 (conj R19 (conj R20 (conj R21 (conj R22 (conj R23 R27)))))))))). }
split.
{ split; [exact HWLE|]. split; [|split; [|split; [|split; [|split]]]].
- intros a Ha Hs Hne. rewrite HEQ by first [lia | intros Ht; apply Hne; exact (conj HOK Ht)].
exact (K1 a Ha Hs (fun x => x)).
- intros b m i Hin Hi Hne.
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR0 Hin) as (_ & Hb4096 & Hbceil & _).
rewrite HEQ by first [lia | intros Ht; apply Hne; exact (conj HOK Ht)].
exact (K2 b m i Hin Hi (fun x => x)).
- intros a Hin Ho He. pose proof (CtrlImg.ctrl_img_range a Hin) as Hir.
rewrite HEQ by first [lia | intros Ht; exact (CELLI a Ht Hin)].
exact (K3 a Hin Ho He).
- intros cid p a Hin Hrr Hne.
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid p HAR0 Hin) as (Hf0 & Hfc & _).
pose proof (fs_frame_bytes_nonneg cid) as Hfb.
pose proof (shadow_addr_bounds (frame_addr lyc cid p) ltac:(lia)) as Hs1.
pose proof (shadow_addr_bounds (frame_addr lyc cid p + fs_frame_bytes cid) ltac:(lia)) as Hs2.
pose proof (shadow_range_end (frame_addr lyc cid p) (fs_frame_bytes cid) Hfb) as Hs3.
assert (Ha : 0 <= a < 2 ^ 64).
{ unfold in_zr, frame_rng in Hrr. cbn [fst snd] in Hrr.
clear - Hrr Hf0 Hfc Hs1 Hs2 Hs3 C1 C2 C5 Hfb. destruct Hrr; lia. }
rewrite HEQ by first [exact Ha | intros Ht; apply Hne; exact (conj HOK Ht)].
exact (K4 cid p a Hin Hrr (fun x => x)).
- intros a Ha Hs Hp. exact (apresent_grows (w_H W3) mem3 mem' a HG (K5 a Ha Hs Hp)).
- intros a Ha. exact (apresent_grows (w_H W3) mem3 mem' a HG (K6 a Ha)). }
split.
{ apply Forall_forall. intros [o r] Hin. pose proof (proj1 (Forall_forall _ _) HSV _ Hin) as Hv.
cbn [fst snd] in Hv |- *.
assert (Ho : 8 <= o <= 104).
{ clear - Hin. unfold rp_saves in Hin. cbn [In] in Hin.
repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; lia|]). destruct Hin. }
apply (val_mem_kept SEGS (w_H W3) (w_H W3) mem3 mem' _ 8 _); [|exact Hv].
intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk. apply HEQ; [lia|].
intros Ht. destruct (CELLA _ Ht) as (_ & _ & _ & _ & KS). unfold ESTACK in KS. lia. }
split.
{ intros _ _. split.
- apply (garr8_frame SEGS (mrestrict (w_H W3) mem3) (mrestrict (w_H W3) mem') fr _ HGM).
intros a Ha. rewrite length_map, Hlg in Ha. change (Z.of_nat 50) with 50 in Ha.
unfold YP09.mbyte. rewrite (HMB a ltac:(lia) ltac:(intros Ht; destruct (CELLA a Ht) as (_ & _ & KF & _); lia)).
reflexivity.
- unfold tsrc_ok. split; [|split; [|split; [|split; [exact HAMEM | split; [exact Hfr0 | exact Hfr63]]]]].
+ intros a Ha. destruct (HTSv a Ha) as (Hnn & Hst). split; [|exact Hst].
rewrite HEQ; [exact Hnn | lia |]. intros Ht. destruct (CELLA a Ht) as (_ & _ & KF & _). lia.
+ apply (range_addressable_agree (aview SEGS (w_H W3) mem3) _ SHADOW_OFF fr 50); [|exact HRAfr].
intros x Hx. pose proof (rp_R8_shx x ltac:(lia)) as Hsx.
apply HEQ; [unfold SHADOW_OFF in Hsx |- *; lia | intros Ht; destruct (CELLA _ Ht) as (_ & KS & _); lia].
+ intros s Hs. exact (aview_keeps_vis SEGS (w_H W3) mem3 mem' s HG (HHULL s Hs)). }
split.
{ intros _. split; [|split; [|split]].
- apply (range_addressable_agree (aview SEGS (w_H W3) mem3) _ SHADOW_OFF pa 2); [|exact HRApa].
intros x Hx. pose proof (rp_R8_shx x ltac:(lia)) as Hsx.
apply HEQ; [unfold SHADOW_OFF in Hsx |- *; lia | intros Ht; destruct (CELLA _ Ht) as (_ & KS & _); lia].
- apply (range_addressable_agree (aview SEGS (w_H W3) mem3) _ SHADOW_OFF pp 8); [|exact HRApp].
intros x Hx. pose proof (rp_R8_shx x ltac:(lia)) as Hsx.
apply HEQ; [unfold SHADOW_OFF in Hsx |- *; lia | intros Ht; destruct (CELLA _ Ht) as (_ & KS & _); lia].
- apply (range_addressable_agree (aview SEGS (w_H W3) mem3) _ SHADOW_OFF pn 8); [|exact HRApn].
intros x Hx. pose proof (rp_R8_shx x ltac:(lia)) as Hsx.
apply HEQ; [unfold SHADOW_OFF in Hsx |- *; lia | intros Ht; destruct (CELLA _ Ht) as (_ & KS & _); lia].
- intros a Ha. exact (apresent_grows (w_H W3) mem3 mem' a HG (HPRES a Ha)). }
{ unfold YE01.arodata_okS. intros a Hro Ho He.
assert (Hin : in_img SEGS a)
by (destruct Hro as [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr] | exact (RELRO_IMG a Hr)]).
pose proof (CtrlImg.ctrl_img_range a Hin) as Hir.
rewrite HEQ by first [lia | intros Ht; exact (CELLI a Ht Hin)].
exact (HROD a Hro Ho He). } }
split.
{ rewrite Q18, Q26, Q25. exact (conj R18 (conj R26 R25)). }
split.
{ intros a Ha. exact (apresent_grows (w_H W3) mem3 mem' a HG (HFP a Ha)). }
split.
{ destruct HFW as (Hw0 & Hw8 & Hw16 & Hw120).
split; [|split; [|split]].
- apply (val_mem_kept SEGS (w_H W3) (w_H W3) mem3 mem' _ 8 _); [|exact Hw0].
intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk. apply HEQ; [lia|].
intros Ht. destruct (CELLA _ Ht) as (_ & _ & _ & KG & _). lia.
- apply (val_mem_kept SEGS (w_H W3) (w_H W3) mem3 mem' _ 8 _); [|exact Hw8].
intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk. apply HEQ; [lia|].
intros Ht. destruct (CELLA _ Ht) as (_ & _ & _ & KG & _). lia.
- apply (val_mem_kept SEGS (w_H W3) (w_H W3) mem3 mem' _ 8 _); [|exact Hw16].
intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk. apply HEQ; [lia|].
intros Ht. destruct (CELLA _ Ht) as (_ & _ & _ & KG & _). lia.
- rewrite (rp_R8_rdword (aview SEGS (w_H W3) mem3)); [exact Hw120|].
intros i Hi. apply HEQ; [lia|]. intros Ht. destruct (CELLA _ Ht) as (_ & _ & _ & KG & _). lia. }
split.
{ intros i Hi. pose proof (HSHD i Hi) as Hc.
assert (Hi16 : (i < 16)%nat) by (cbn [length rp_sg_live] in Hi; exact Hi).
assert (SHlo : 0 <= frame_addr lyc 1 pos / 8) by (apply Z.div_pos; lia).
assert (SHhi : frame_addr lyc 1 pos / 8 <= 17592186044400)
by (apply Z.div_le_upper_bound; [lia | clear - HG0 C1; lia]).
rewrite HEQ; [exact Hc | clear - SHlo SHhi Hi16; unfold shadow_of_addr, SHADOW_OFF; lia
| intros Ht; destruct (CELLA _ Ht) as (_ & KS & _);
clear - KS SHlo SHhi Hi16; unfold shadow_of_addr, SHADOW_OFF in *; lia]. }
split; [exact HARG|].
split.
{ rewrite Q10. unfold reply_ret. rewrite HARG, HIR. reflexivity. }
intros _. split; [|split].
{ (* pa gets reply_addr g = [g37; g36] *)
assert (Ue : U (ewset (ewset E 512 w) 513 w0) (SAlu ALU_OR (SAlu ALU_SLL (SOff 32 0) (SLit 8)) (SOff 33 0)) =
g36 * 256 + g37).
{ rewrite !U_SAlu. cbn [zalu_raw]. rewrite U_SLit, !U_SOff, !ew_ewset_other by lia. rewrite V32, V33, !Z.add_0_r.
change (Z.land (zcanon 8) 63) with 8.
rewrite (zcanon_id g36), (zcanon_id g37) by (unfold M64; lia).
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
rewrite (zcanon_id (g36 * 256)) by (unfold M64; lia).
rewrite rp_R8_lor by lia. apply zcanon_id. unfold M64. lia. }
assert (Cpa : forall i, 0 <= i < 2 -> YP09.mbyte SEGS (mrestrict (w_H W3) mem') (pa + 0 + i) =
Some (Z_to_bv 8 (Z.shiftr (g36 * 256 + g37) (8 * i)))).
{ intros i Hi. destruct (Hcpa i) as (b & Hb1 & Hb2); [cbn [YP09.c_len YP09.cv_len YP09.c_val Z.of_N]; lia|].
cbn [YP09.cbyte YP09.c_off YP09.c_val] in Hb1. cbn [YP09.c_off] in Hb2. injection Hb1 as Hb1.
transitivity (Some b); [exact Hb2|]. f_equal. rewrite <- Hb1. unfold YP09.byte_of_word.
f_equal. apply (f_equal (fun z => Z.shiftr z (8 * i))). exact Ue. }
destruct (rp_R8_bytes2 g36 g37 Hg36 Hg37) as (Bl & Bh).
intros j Hj. cbn [reply_addr map length] in Hj |- *.
destruct j as [|[|j]]; [| | lia].
- cbn [nth]. split; [|exact (cp_v_range' g 37)]. intros kk Hkk. assert (kk = 0%nat) as -> by lia.
replace (pa + Z.of_nat 0 + Z.of_nat 0) with (pa + 0 + 0) by lia. rewrite (Cpa 0) by lia. f_equal.
apply rp_R8_zbyte. change (bv_unsigned (cp_b g 37)) with g37. rewrite rp_R8_le1 by lia.
change (8 * 0) with 0. rewrite Z.shiftr_0_r, Bl. rewrite Z.mod_small by lia. reflexivity.
- cbn [nth]. split; [|exact (cp_v_range' g 36)]. intros kk Hkk. assert (kk = 0%nat) as -> by lia.
replace (pa + Z.of_nat 1 + Z.of_nat 0) with (pa + 0 + 1) by lia. rewrite (Cpa 1) by lia. f_equal.
apply rp_R8_zbyte. change (bv_unsigned (cp_b g 36)) with g36. rewrite rp_R8_le1 by lia.
change (8 * 1) with 8. rewrite Bh. rewrite Z.mod_small by lia. reflexivity. }
{ (* pp gets fr + 38 *)
replace pp with (pp + 0) at 1 by lia.
apply (rp_R8_vm8 _ _ _ _ _ _ Hcpp).
- cbn [sv_denot]. rewrite !ew_ewset_other by lia. rewrite V22. apply unsigned_lit_small. lia.
- lia. }
{ (* pn gets s - 13 *)
replace pn with (pn + 0) at 1 by lia.
apply (rp_R8_vm8 _ _ _ _ _ _ Hcpn).
- cbn [sv_denot]. rewrite !ew_ewset_other by lia. rewrite V11. apply unsigned_lit_small. lia.
- lia. }
Qed.

(* LOCAL helper of this stretch (no kit lemma duplicates it): an 8-aligned boundary separates shadow cells. *)
Lemma rp_R9_shlt : forall F x, F mod 8 = 0 -> 0 <= x < F -> shadow_addr x < shadow_addr F.
Proof.
intros F x HF Hx. unfold shadow_addr.
assert (H8 : F = F / 8 * 8) by (pose proof (Z.div_mod F 8 ltac:(lia)); lia).
assert (Hle : x / 8 <= F / 8 - 1).
{ replace (F / 8 - 1) with ((F - 1) / 8).
- apply Z.div_le_mono; lia.
- replace (F - 1) with ((F / 8 - 1) * 8 + 7) by lia.
rewrite Z.div_add_l by lia. replace (7 / 8) with 0 by reflexivity. lia. }
lia.
Qed.

(* R9  C11 -> C12, 0x84208..0x8421c (+0x27c..+0x290). The five shadow bytes SG[4..8] := f8 (re-poison of the
   record), inside the own frame's shadow: `awr_byte`'s `in_frames` case; `paj_run_to_tok` stopping at +0x294.
   Donors: B `rp_f8` :3362; A18 `seg_rep` :1508. Difficulty: easy. *)

(* R9  C11 -> C12, 0x84208..0x8421c (+0x27c..+0x290). The five shadow bytes SG[4..8] := f8 (re-poison of the
   record), inside the own frame's shadow: `awr_byte`'s `in_frames` case; `paj_run_to_tok` stopping at +0x294.
   Donors: B `rp_f8` :3362; A18 `seg_rep` :1508. Difficulty: easy. *)
Lemma rp_R9 : rp_from_C12 -> rp_from_C11.
Proof.
intros F12 cx pos regs3 ly3 S3 W3 mem3 md3 HB HC.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
destruct HC as (HJH & HCAR & HFRG & HFPR & HFW & HSG & HARGS & HA0 & HCELLS).
destruct HJH as (HJ & HLY & HFRS & HNIN & HAB & HCNT).
destruct HCAR as (HRG & HKEPT & HSAV & HMSG & HOUT & HRO).
assert (Epc1 : rp_pc 0x27c = BASE + 0x332c)
by (unfold rp_pc, A_reac_ctrl_identity_replyP, AF_reac_ctrl_identity_reply; lia).
assert (E25v : getr regs3 25 = w64 (shadow_addr (rp_G cx pos))) by exact (proj2 (proj2 HFRG)).
assert (HinS : In (1, pos) (frames S3)) by (rewrite HFRS; left; reflexivity).
pose proof (proj1 HJ) as HAR3.
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 mem3 md3 1 pos HAR3 HinS) as (HG4096 & HGceil & HGapp).
assert (EFA : frame_addr ly3 1 pos = rp_G cx pos)
by (unfold rp_G, frame_addr; rewrite (proj1 HLY); reflexivity).
rewrite EFA in HG4096, HGceil, HGapp.
change (fs_frame_bytes 1) with 128 in HG4096, HGceil, HGapp.
pose proof (proj1 lib.Reusable.YM05.alloc_ceiling_val) as HAC.
pose proof (shadow_addr_bounds (rp_G cx pos) ltac:(unfold kHighMemEnd; lia)) as HSB1.
pose proof (shadow_range_end (rp_G cx pos) 128 ltac:(lia)) as HSE.
pose proof (shadow_addr_bounds (rp_G cx pos + 128) ltac:(unfold kHighMemEnd; lia)) as HSB2.
change (128 / 8) with 16 in HSE.
assert (HSpres : forall i, 0 <= i < 16 -> apresent (w_H W3) mem3 (shadow_addr (rp_G cx pos) + i)).
{ destruct (al_frames _ _ LAWS ly3 S3 W3 mem3 md3 1 pos HAR3 HinS) as (_ & _ & _ & Hsh).
rewrite EFA in Hsh. intros i Hi. apply (proj1 (Hsh i ltac:(change (fs_frame_bytes 1 / 8) with 16; lia))). }
remember (Eimg (Ereg regs3 [])) as Ev eqn:HEv.
assert (HEI : img_env VAL A_LIM Ev) by (subst Ev; apply Eimg_env).
assert (E25 : ew Ev 25 = getr regs3 25)
by (subst Ev; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs3 _ 25 25%bv eq_refl)).
assert (E25u : bv_unsigned (ew Ev 25) = shadow_addr (rp_G cx pos))
by (rewrite E25, E25v; unfold w64; apply unsigned_lit_small; unfold kLowMemEnd, kHighShadowEnd in HSB1; lia).
assert (HS : st_ok_pi SEGS VAL Ev
(mkSS 0x332c sr_atoms [YP09.mkRegion (Some 25%nat) 0 16 4 9 []] None (mkFacts [] [] []))
(mkst regs3 (Z_to_bv 64 (BASE + 0x332c)) (mrestrict (w_H W3) mem3) (seg_rom SEGS))).
{ apply (@pa_entry_st_ok_full _ _ ctrl_listing CtrlImg.PI_ctrl Ev 0x332c sr_atoms regs3
[YP09.mkRegion (Some 25%nat) 0 16 4 9 []] (mkFacts [] [] []) (mrestrict (w_H W3) mem3)).
- subst Ev. apply regs_ok_Eimg_Ereg.
- vm_compute; reflexivity.
- constructor; [|constructor]. unfold region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite E25u. unfold kLowMemEnd, kHighShadowEnd in HSB1.
split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
intros o Ho. apply (apresent_writable SEGS). apply HSpres. lia.
- cbn. repeat split.
- cbn. repeat split.
}
unfold cfg_at. rewrite Epc1. unfold w64 at 1.
rewrite <- restrict_mkst_fx in HS.
pose proof (SRr_run_to_pi_AJ B LAWS) as RUNTOP.
paj_run_to_sh RUNTOP HS HJ 0x3344.
{ eapply (awr_ok_cons_gen Ev _ _ _ _ _ _ _ _ _ 25%nat (shadow_addr (rp_G cx pos))).
- reflexivity.
- exact E25u.
- cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. right; right; right.
exists 1, pos. split; [left; reflexivity|]. right.
unfold in_zr. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes 1 / 8) with 16. lia.
- apply awr_ok_nil. }
(* ---- the five written bytes (chunks at offsets 4..8 of the frame's shadow) ---- *)
assert (HNW : forall a, ~ (shadow_addr (rp_G cx pos) + 4 <= a < shadow_addr (rp_G cx pos) + 9) ->
~ in_wrange Ev [YP09.mkRegion (Some 25%nat) 0 16 4 9 []] a).
{ intros a Ha (r & Hin & Hr). cbn [In] in Hin. destruct Hin as [<-|[]].
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite E25u in Hr. lia. }
assert (HEQ : forall a, 0 <= a < 2 ^ 64 ->
~ (shadow_addr (rp_G cx pos) + 4 <= a < shadow_addr (rp_G cx pos) + 9) ->
aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha Hn. apply aview_eq_of. apply HFr. rewrite Z_to_bv_unsigned.
unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_small by lia.
cbn [ss_mem]. apply HNW. exact Hn. }
assert (HCHF : forall c, In c [YP09.mkChunk 8 (CVal 1 (SLit 18446744073709551608));
YP09.mkChunk 7 (CVal 1 (SLit 18446744073709551608)); YP09.mkChunk 6 (CVal 1 (SLit 18446744073709551608));
YP09.mkChunk 5 (CVal 1 (SLit 18446744073709551608)); YP09.mkChunk 4 (CVal 1 (SLit 18446744073709551608))] ->
YP09.chunk_ok SEGS Ev (ms_mem (restrict (w_H W3) ms)) (shadow_addr (rp_G cx pos)) c).
{ pose proof (st_ok_mem_ok SEGS Ev _ _ HS) as HM. destruct HM as (_ & HMR & _).
rewrite Forall_forall in HMR.
specialize (HMR _ ltac:(cbn [ss_mem abs_ss setpc]; left; reflexivity)).
destruct HMR as (_ & _ & _ & HC).
cbn [YP09.r_chunks YP09.r_base base_val] in HC. rewrite E25u in HC.
rewrite Forall_forall in HC. exact HC. }
assert (HSH248 : forall off, 4 <= off <= 8 ->
aview SEGS (w_H W3) (ms_mem ms) (shadow_addr (rp_G cx pos) + off) = Some 248).
{ intros off Hoff.
assert (Hin : In (YP09.mkChunk off (CVal 1 (SLit 18446744073709551608)))
[YP09.mkChunk 8 (CVal 1 (SLit 18446744073709551608)); YP09.mkChunk 7 (CVal 1 (SLit 18446744073709551608));
YP09.mkChunk 6 (CVal 1 (SLit 18446744073709551608)); YP09.mkChunk 5 (CVal 1 (SLit 18446744073709551608));
YP09.mkChunk 4 (CVal 1 (SLit 18446744073709551608))]).
{ assert (Ho5 : off = 4 \/ off = 5 \/ off = 6 \/ off = 7 \/ off = 8) by lia.
destruct Ho5 as [H5|[H5|[H5|[H5|H5]]]]; rewrite H5; cbn [In]; tauto. }
destruct (HCHF _ Hin 0 ltac:(cbn; lia)) as (b & Hb1 & Hb2).
cbn [cbyte YP09.c_off YP09.c_val sv_denot] in Hb1. injection Hb1 as <-.
cbn [ms_mem restrict c_off] in Hb2. rewrite Z.add_0_r in Hb2.
unfold aview. rewrite Hb2. vm_compute. reflexivity. }
assert (HAE : env_agree 32 (Ereg regs3 []) Ev)
by (subst Ev; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (HRK : forall r, In r ([2;3;4;8;9;10;18;19;20;21;22;23;25;26;27]%bv : list (bv 5)) ->
getr (ms_regs ms) r = getr regs3 r).
{ exact (regs_kept_of_st_ok_pi Ev _ _ regs3 [] ([2;3;4;8;9;10;18;19;20;21;22;23;25;26;27]%bv : list (bv 5))
HS HAE ltac:(vm_compute; reflexivity)). }
(* ---- separations: no address any carried fact mentions is in [SG+4, SG+9) ---- *)
destruct (al_frames _ _ LAWS ly3 S3 W3 mem3 md3 1 pos HAR3 HinS) as (HG32 & _ & _ & _).
rewrite EFA in HG32.
assert (HG8 : rp_G cx pos mod 8 = 0)
by (pose proof (Z.div_mod (rp_G cx pos) 32 ltac:(lia)); pose proof (Z.div_mod (rp_G cx pos) 8 ltac:(lia));
pose proof (Z.mod_pos_bound (rp_G cx pos) 8 ltac:(lia)); lia).
assert (ESH : shadow_of_addr SHADOW_OFF (rp_G cx pos) = shadow_addr (rp_G cx pos)) by reflexivity.
assert (HW64 : 0 <= shadow_addr (rp_G cx pos) /\ shadow_addr (rp_G cx pos) + 16 < alloc_ceiling)
by (unfold kLowMemEnd, kHighShadowEnd in HSB1; lia).
assert (NWapp : forall a, app_addr a ->
~ (shadow_addr (rp_G cx pos) + 4 <= a < shadow_addr (rp_G cx pos) + 9)).
{ intros a Ha Hw. unfold app_addr, kLowShadowBeg, kHighMemBeg in Ha.
unfold kLowMemEnd, kHighShadowEnd in HSB1, HSB2. destruct Ha as (Ha0 & [Ha|[Ha1 Ha2]]); lia. }
assert (NWimg : forall a, in_img SEGS a ->
~ (shadow_addr (rp_G cx pos) + 4 <= a < shadow_addr (rp_G cx pos) + 9)).
{ intros a Hi Hw. pose proof (Hsegs a Hi) as Hlo. unfold kLowMemEnd in HSB1, Hlo. lia. }
assert (HEQapp : forall a, app_addr a -> aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha. apply HEQ; [|apply NWapp; exact Ha].
unfold app_addr, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Ha.
destruct Ha as (Ha0 & [Ha|[Ha1 Ha2]]); lia. }
assert (HEQsh : forall x, 0 <= x < kHighMemEnd ->
~ (shadow_addr (rp_G cx pos) + 4 <= shadow_addr x < shadow_addr (rp_G cx pos) + 9) ->
aview SEGS (w_H W3) (ms_mem ms) (shadow_addr x) = aview SEGS (w_H W3) mem3 (shadow_addr x)).
{ intros x Hx Hn. pose proof (shadow_addr_bounds x Hx). apply HEQ; [|exact Hn].
unfold kLowMemEnd, kHighShadowEnd in *. lia. }
assert (NWsh : forall q n x, (rp_G cx pos + 128 <= q \/ q + n <= rp_G cx pos) -> 0 <= q -> q <= x < q + n ->
~ (shadow_addr (rp_G cx pos) + 4 <= shadow_addr x < shadow_addr (rp_G cx pos) + 9)).
{ intros q n x Hd Hq Hx Hw. destruct Hd as [Hd|Hd].
- pose proof (shadow_mono (rp_G cx pos + 128) x ltac:(lia)). lia.
- pose proof (rp_R9_shlt (rp_G cx pos) x HG8 ltac:(lia)). lia. }
assert (NWblk : forall b n x, In (b, n) (ablocks B (rc_lyc cx) (rc_Sc cx)) -> b <= x < b + req_size n ->
app_addr x /\ ~ (shadow_addr (rp_G cx pos) + 4 <= shadow_addr x < shadow_addr (rp_G cx pos) + 9)).
{ intros b n x Hin Hx. rewrite <- HAB in Hin.
destruct (al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 b n HAR3 Hin) as (_ & Hb4096 & Hbceil & Hbapp & _ & _).
split; [exact (in_app_addr _ _ _ Hbapp Hx)|].
pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 mem3 md3 b n 1 pos HAR3 Hin HinS) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EFA in Hd. change (fs_frame_bytes 1) with 128 in Hd.
apply (NWsh b (req_size n) x ltac:(lia) ltac:(lia) Hx). }
assert (NWfr : forall cid pos' x, In (cid, pos') (frames (rc_Sc cx)) ->
in_zr x (frame_rng (rc_lyc cx) (cid, pos')) ->
app_addr x /\ ~ (shadow_addr (rp_G cx pos) + 4 <= shadow_addr x < shadow_addr (rp_G cx pos) + 9)).
{ intros cid pos' x Hin Hx.
assert (EFA2 : frame_addr (rc_lyc cx) cid pos' = frame_addr ly3 cid pos')
by (unfold frame_addr; rewrite (proj1 HLY); reflexivity).
unfold in_zr, frame_rng in Hx. cbn [fst snd] in Hx. rewrite EFA2 in Hx.
assert (HinS2 : In (cid, pos') (frames S3)) by (rewrite HFRS; right; exact Hin).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 mem3 md3 cid pos' HAR3 HinS2) as (Hf0 & Hfc & Hfapp).
split; [exact (in_app_addr _ _ _ Hfapp Hx)|].
apply in_split in Hin as (g1 & g2 & Eg).
assert (Hd : zdisjoint (frame_rng ly3 (1, pos)) (frame_rng ly3 (cid, pos'))).
{ eapply (sep_frames_pos SEGS B LAWS ly3 S3 W3 mem3 md3 (1, pos) (cid, pos') [] g1 g2 HAR3).
rewrite HFRS, Eg. reflexivity. }
unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. rewrite EFA in Hd.
change (fs_frame_bytes 1) with 128 in Hd.
apply (NWsh (frame_addr ly3 cid pos') (fs_frame_bytes cid) x ltac:(lia) ltac:(lia) Hx). }
assert (NWfrsh : forall cid pos' a, In (cid, pos') (frames (rc_Sc cx)) ->
in_zr a (shadow_addr (frame_addr (rc_lyc cx) cid pos'), fs_frame_bytes cid / 8) ->
0 <= a < 2 ^ 64 /\ ~ (shadow_addr (rp_G cx pos) + 4 <= a < shadow_addr (rp_G cx pos) + 9)).
{ intros cid pos' a Hin Hx.
assert (EFA2 : frame_addr (rc_lyc cx) cid pos' = frame_addr ly3 cid pos')
by (unfold frame_addr; rewrite (proj1 HLY); reflexivity).
unfold in_zr in Hx. cbn [fst snd] in Hx. rewrite EFA2 in Hx.
assert (HinS2 : In (cid, pos') (frames S3)) by (rewrite HFRS; right; exact Hin).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 mem3 md3 cid pos' HAR3 HinS2) as (Hf0 & Hfc & Hfapp).
pose proof (fs_frame_bytes_nonneg cid) as Hnn.
pose proof (shadow_addr_bounds (frame_addr ly3 cid pos') ltac:(unfold kHighMemEnd; lia)) as Hsb1'.
pose proof (shadow_addr_bounds (frame_addr ly3 cid pos' + fs_frame_bytes cid)
ltac:(unfold kHighMemEnd; lia)) as Hsb2'.
pose proof (shadow_range_end (frame_addr ly3 cid pos') (fs_frame_bytes cid) Hnn) as Hse'.
split; [unfold kLowMemEnd, kHighShadowEnd in Hsb1', Hsb2'; lia|].
apply in_split in Hin as (g1 & g2 & Eg).
assert (Hd : zdisjoint (frame_rng ly3 (1, pos)) (frame_rng ly3 (cid, pos'))).
{ eapply (sep_frames_pos SEGS B LAWS ly3 S3 W3 mem3 md3 (1, pos) (cid, pos') [] g1 g2 HAR3).
rewrite HFRS, Eg. reflexivity. }
unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. rewrite EFA in Hd.
change (fs_frame_bytes 1) with 128 in Hd.
destruct Hd as [Hd|Hd].
- pose proof (shadow_mono (rp_G cx pos + 128) (frame_addr ly3 cid pos') ltac:(lia)). lia.
- pose proof (shadow_mono (frame_addr ly3 cid pos' + fs_frame_bytes cid) (rp_G cx pos) ltac:(lia)). lia. }
(* ---- the stack window is above alloc_ceiling ---- *)
pose proof HB as HB'.
destruct HB' as (HBJ & HBro & HBret & HBra & HBgp & HBtp & HB10 & HB11 & HB12 & HB13 & HB14 &
HBfr & HBlen & HBpa & HBpp & HBpn & HBm16 & HBstk1 & HBstk2 & HBroom & HBg50 & HBmsg & HBout).
destruct HBJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSTKok & _).
destruct HSTKok as (_ & _ & Hceil0 & Hlo0 & Hhi0 & H47 & _).
pose proof rp_stk as (Tstk & Pstk).
assert (HSTKlo : alloc_ceiling + TREPLY_STK <= rp_S cx) by lia.
assert (HSThi : rp_S cx <= 2 ^ 47) by lia.
destruct HW64 as (HWlo0 & HWhi0).
assert (HEQstk : forall a, rp_S cx - 128 <= a < rp_S cx ->
aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha. apply HEQ; lia. }
(* ---- land on C12 ---- *)
assert (Epc2 : rp_pc 0x294 = BASE + 13124)
by (unfold rp_pc, A_reac_ctrl_identity_replyP, AF_reac_ctrl_identity_reply; lia).
pmkst HS.
rewrite <- Epc2.
change (Z_to_bv 64 (rp_pc 0x294)) with (w64 (rp_pc 0x294)).
apply (F12 cx pos (ms_regs ms) ly3 S3 W3 (ms_mem ms)
(with_vm_backing (m_vm_lazy md3) mat md3) HB).
unfold rp_C12.
split.
{ split; [exact HJ|]. split; [exact HLY|]. split; [exact HFRS|].
split; [exact HNIN|]. split; [exact HAB|]. exact HCNT. }
split.
{ (* rp_carry *)
destruct HRG as (G2 & G3 & G4 & G8 & G9 & G19 & G20 & G21 & G22 & G23 & G27).
split.
{ unfold rp_regs_ok.
split; [rewrite (HRK 2%bv ltac:(cbn [In]; tauto)); exact G2|].
split; [rewrite (HRK 3%bv ltac:(cbn [In]; tauto)); exact G3|].
split; [rewrite (HRK 4%bv ltac:(cbn [In]; tauto)); exact G4|].
split; [rewrite (HRK 8%bv ltac:(cbn [In]; tauto)); exact G8|].
split; [rewrite (HRK 9%bv ltac:(cbn [In]; tauto)); exact G9|].
split; [rewrite (HRK 19%bv ltac:(cbn [In]; tauto)); exact G19|].
split; [rewrite (HRK 20%bv ltac:(cbn [In]; tauto)); exact G20|].
split; [rewrite (HRK 21%bv ltac:(cbn [In]; tauto)); exact G21|].
split; [rewrite (HRK 22%bv ltac:(cbn [In]; tauto)); exact G22|].
split; [rewrite (HRK 23%bv ltac:(cbn [In]; tauto)); exact G23|].
rewrite (HRK 27%bv ltac:(cbn [In]; tauto)); exact G27. }
destruct HKEPT as (HWLE & K1 & K2 & K3 & K4 & K5 & K6).
split.
{ split; [exact HWLE|]. unfold tcj_kept.
split; [intros a Ha1 Ha2 Ha3; etransitivity; [apply (HEQ a ltac:(lia) ltac:(lia)) | exact (K1 a Ha1 Ha2 Ha3)]|].
split.
{ intros b m i Hin Hi He.
destruct (NWblk b m (b + i) Hin ltac:(lia)) as (Happ & _).
etransitivity; [apply (HEQapp (b + i) Happ) | exact (K2 b m i Hin Hi He)]. }
split.
{ intros a Hi Ho He.
pose proof (Hsegs a Hi) as Hlo'. unfold kLowMemEnd in Hlo', HSB1.
etransitivity; [apply (HEQ a ltac:(lia) ltac:(lia)) | exact (K3 a Hi Ho He)]. }
split.
{ intros cid pos' a Hin Hr Hne.
assert (Hnw : 0 <= a < 2 ^ 64 /\ ~ (shadow_addr (rp_G cx pos) + 4 <= a < shadow_addr (rp_G cx pos) + 9)).
{ destruct Hr as [Hr|Hr].
- destruct (NWfr cid pos' a Hin Hr) as (Happ & _). split; [|apply NWapp; exact Happ].
unfold app_addr, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
destruct Happ as (Hx0 & [Hx|[Hx1 Hx2]]); lia.
- exact (NWfrsh cid pos' a Hin Hr). }
etransitivity; [apply (HEQ a (proj1 Hnw) (proj2 Hnw)) | exact (K4 cid pos' a Hin Hr Hne)]. }
split.
{ intros a Ha1 Ha2 Hp. eapply apresent_grows; [exact HG|]. exact (K5 a Ha1 Ha2 Hp). }
{ intros a Ha. eapply apresent_grows; [exact HG|]. exact (K6 a Ha). } }
split.
{ (* rp_saved *)
unfold rp_saved in HSAV |- *. rewrite Forall_forall in HSAV |- *. intros p Hp.
assert (Hpf : 8 <= fst p <= 104)
by (revert Hp; unfold rp_saves; cbn [In]; intros H;
repeat (destruct H as [Hq|H]; [subst p; cbn [fst]; lia|]); destruct H).
eapply (val_mem_moved SEGS (w_H W3) (w_H W3) mem3 (ms_mem ms)); [|exact (HSAV p Hp)].
intros k Hk. cbn [Z.of_nat] in Hk. apply HEQstk. lia. }
split.
{ (* rp_msg *)
intros Hargs Hlen50. destruct (HMSG Hargs Hlen50) as (Hgarr & Hsrc).
destruct (HBmsg Hargs Hlen50) as ((nb & Hnbin & Hnbsz) & _ & _).
assert (HFRapp : forall x, rc_fr cx <= x < rc_fr cx + 50 ->
app_addr x /\ ~ (shadow_addr (rp_G cx pos) + 4 <= shadow_addr x < shadow_addr (rp_G cx pos) + 9))
by (intros x Hx; apply (NWblk (rc_fr cx) nb x Hnbin); lia).
split.
{ intros j Hj. destruct (Hgarr j Hj) as (Hv & Hr). split; [|exact Hr].
assert (Hj50 : (j < 50)%nat)
by (first [rewrite length_map in Hj | rewrite map_length in Hj]; rewrite HBg50 in Hj; exact Hj).
eapply (val_mem_moved SEGS (w_H W3) (w_H W3) mem3 (ms_mem ms)); [|exact Hv].
intros k Hk. cbn [Z.of_nat] in Hk. apply HEQapp.
exact (proj1 (HFRapp (rc_fr cx + Z.of_nat j + k) ltac:(lia))). }
destruct Hsrc as (T1 & T2 & T3 & T4 & T5 & T6).
split.
{ intros a Ha. split; [eapply aview_keeps_vis; [exact HG|]; exact (proj1 (T1 a Ha)) | exact (proj2 (T1 a Ha))]. }
split.
{ intros x Hx. destruct (T2 x Hx) as (sv & Hsv & Hok). exists sv. split; [|exact Hok].
change (shadow_of_addr SHADOW_OFF x) with (shadow_addr x) in Hsv |- *.
destruct (HFRapp x Hx) as (Happ & Hnw).
etransitivity; [apply (HEQsh x ltac:(unfold app_addr, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ; unfold kHighMemEnd;
destruct Happ as (Hx0 & [Hq|[Hq1 Hq2]]); lia) Hnw) | exact Hsv]. }
split; [intros s Hs; eapply aview_keeps_vis; [exact HG|]; exact (T3 s Hs)|].
split; [exact T4|]. split; [exact T5 | exact T6]. }
split.
{ (* rp_out *)
intros Hargs. destruct (HOUT Hargs) as (Oa & Op & On & Opres).
destruct (HBout Hargs) as (_ & _ & _ & _ & _ & _ & Hfrmem & _).
assert (HOA : forall x, treply_out (rc_pa cx) (rc_pp cx) (rc_pn cx) x ->
app_addr x /\ ~ (shadow_addr (rp_G cx pos) + 4 <= shadow_addr x < shadow_addr (rp_G cx pos) + 9))
by (intros x Hx; destruct (Hfrmem x Hx) as (cid & pos' & Hin & Hz); exact (NWfr cid pos' x Hin Hz)).
assert (HRA : forall q n, (forall x, q <= x < q + n -> treply_out (rc_pa cx) (rc_pp cx) (rc_pn cx) x) ->
range_addressable (aview SEGS (w_H W3) mem3) SHADOW_OFF q n ->
range_addressable (aview SEGS (w_H W3) (ms_mem ms)) SHADOW_OFF q n).
{ intros q n Hq Hr x Hx. destruct (Hr x Hx) as (sv & Hsv & Hok). exists sv. split; [|exact Hok].
change (shadow_of_addr SHADOW_OFF x) with (shadow_addr x) in Hsv |- *.
destruct (HOA x (Hq x Hx)) as (Happ & Hnw).
etransitivity; [apply (HEQsh x ltac:(unfold app_addr, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ; unfold kHighMemEnd;
destruct Happ as (Hx0 & [Hq'|[Hq1 Hq2]]); lia) Hnw) | exact Hsv]. }
split; [apply HRA; [intros x Hx; left; lia | exact Oa]|].
split; [apply HRA; [intros x Hx; right; left; lia | exact Op]|].
split; [apply HRA; [intros x Hx; right; right; lia | exact On]|].
intros a Ha. eapply apresent_grows; [exact HG|]. exact (Opres a Ha). }
{ (* arodata_okS *)
intros a Hro Ho He.
assert (Himg : in_img SEGS a)
by (destruct Hro as [(s & Hs1 & _ & Hs2)|Hr]; [exists s; split; [exact Hs1 | exact Hs2] | exact (RELRO_IMG a Hr)]).
pose proof (Hsegs a Himg) as Hlo'. unfold kLowMemEnd in Hlo', HSB1.
rewrite (HEQ a ltac:(lia) ltac:(lia)). exact (HRO a Hro Ho He). } }
split.
{ (* rp_fregs *)
destruct HFRG as (Q18 & Q26 & Q25).
split; [rewrite (HRK 18%bv ltac:(cbn [In]; tauto)); exact Q18|].
split; [rewrite (HRK 26%bv ltac:(cbn [In]; tauto)); exact Q26|].
rewrite (HRK 25%bv ltac:(cbn [In]; tauto)); exact Q25. }
split.
{ intros a Ha. eapply apresent_grows; [exact HG|]. exact (HFPR a Ha). }
split.
{ (* rp_fwords *)
destruct HFW as (F0 & F8w & F16w & FLw).
assert (HEQfr : forall a, rp_G cx pos <= a < rp_G cx pos + 128 ->
aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) mem3 a)
by (intros a Ha; apply HEQapp; exact (in_app_addr _ _ _ HGapp Ha)).
split; [eapply (val_mem_moved SEGS (w_H W3) (w_H W3) mem3 (ms_mem ms)); [|exact F0];
intros k Hk; cbn [Z.of_nat] in Hk; apply HEQfr; lia|].
split; [eapply (val_mem_moved SEGS (w_H W3) (w_H W3) mem3 (ms_mem ms)); [|exact F8w];
intros k Hk; cbn [Z.of_nat] in Hk; apply HEQfr; lia|].
split; [eapply (val_mem_moved SEGS (w_H W3) (w_H W3) mem3 (ms_mem ms)); [|exact F16w];
intros k Hk; cbn [Z.of_nat] in Hk; apply HEQfr; lia|].
rewrite (rdword_ext (aview SEGS (w_H W3) mem3) (aview SEGS (w_H W3) (ms_mem ms))
(rp_G cx pos + 120) ltac:(intros k Hk; apply HEQfr; lia)). exact FLw. }
split.
{ (* rp_shadow: the record's five cells are f8 again *)
unfold rp_shadow, shadow_cells in HSG |- *.
change (shadow_of_addr SHADOW_OFF (rp_G cx pos)) with (shadow_addr (rp_G cx pos)) in HSG |- *.
intros i Hi. cbn [length rp_sg_frame] in Hi.
do 16 (destruct i as [|i];
[ first
[ erewrite HSH248 by (cbn [Z.of_nat]; lia); cbn [nth_error rp_sg_frame]; reflexivity
| rewrite HEQ by (cbn [Z.of_nat]; lia);
erewrite HSG by (cbn [length rp_sg_live]; lia);
cbn [nth_error rp_sg_live rp_sg_frame]; reflexivity ]
| ]).
lia. }
split.
{ rewrite (HRK 10%bv ltac:(cbn [In]; tauto)); exact HA0. }
{ (* rp_cells *)
intros Hok. destruct (HCELLS Hok) as (Ca & Cp & Cn).
destruct (HBout HARGS) as (_ & _ & _ & _ & _ & _ & Hfrmem & _).
assert (HOA : forall x, treply_out (rc_pa cx) (rc_pp cx) (rc_pn cx) x -> app_addr x)
by (intros x Hx; destruct (Hfrmem x Hx) as (cid & pos' & Hin & Hz); exact (proj1 (NWfr cid pos' x Hin Hz))).
split.
{ intros j Hj. destruct (Ca j Hj) as (Hv & Hr).
assert (Hj2 : (j < 2)%nat) by (cbn [length map reply_addr] in Hj; lia).
split; [|exact Hr].
eapply (val_mem_moved SEGS (w_H W3) (w_H W3) mem3 (ms_mem ms)); [|exact Hv].
intros k Hk. cbn [Z.of_nat] in Hk. apply HEQapp. apply HOA. left. lia. }
split.
{ eapply (val_mem_moved SEGS (w_H W3) (w_H W3) mem3 (ms_mem ms)); [|exact Cp].
intros k Hk. cbn [Z.of_nat] in Hk. apply HEQapp. apply HOA. right. left. lia. }
{ eapply (val_mem_moved SEGS (w_H W3) (w_H W3) mem3 (ms_mem ms)); [|exact Cn].
intros k Hk. cbn [Z.of_nat] in Hk. apply HEQapp. apply HOA. right. right. lia. } }
Qed.

(* ---- local helpers of stretch R10 (see the report; swap for kit names when they land) ------------- *)
(* The addresses C12 -> C13 writes are the first word of the own class-1 frame and the 16 bytes of that
   frame's shadow. `rp_R10_prot` collects every address class the invariants protect: the high memory at
   and above alloc_ceiling (the machine stack), the live blocks, the image, and the OTHER frames of the
   state together with their shadows. `rp_R10_notw` says no protected address is written. *)
Definition rp_R10_prot (ly3 : alayout) (S3 : astate) (pos a : Z) : Prop :=
alloc_ceiling <= a \/
(exists b n, In (b, n) (ablocks B ly3 S3) /\ b <= a < b + req_size n) \/
in_img SEGS a \/
(exists cid p, In (cid, p) (frames S3) /\ (cid, p) <> (1, pos) /\
(in_zr a (frame_addr ly3 cid p, fs_frame_bytes cid) \/
in_zr a (shadow_addr (frame_addr ly3 cid p), fs_frame_bytes cid / 8))) \/
(exists x, 4096 <= x < alloc_ceiling /\
~ (frame_addr ly3 1 pos <= x < frame_addr ly3 1 pos + 128) /\ a = SHADOW_OFF + x / 8).

Lemma rp_R10_mod256 : forall z, z mod 2 ^ 64 mod 256 = z mod 256.
Proof.
intros z. change (2 ^ 64) with 18446744073709551616.
rewrite <- (Z_mod_plus_full (z mod 18446744073709551616)
(72057594037927936 * (z / 18446744073709551616)) 256).
f_equal. pose proof (Z.div_mod z 18446744073709551616 ltac:(lia)). lia.
Qed.

(* one byte of a chunk, as CtrlFinish.v:139 `val_mem1_of_chunk` states it (duplicated locally). *)
Lemma rp_R10_vm1 : forall (Ez : env) (m : word -> option byte) (q off : Z) (e : sv) (z : Z),
YP09.chunk_ok SEGS Ez m q (YP09.mkChunk off (CVal 1 e)) -> sv_denot Ez e = Z_to_bv 64 z ->
val_mem SEGS m (q + off) 1%nat (z mod 256).
Proof.
intros Ez m q off e z Hc Hz kk Hk.
assert (Hk0 : kk = 0%nat) by lia. subst kk.
destruct (Hc 0 ltac:(cbn; lia)) as (bb & Hb1 & Hb2).
cbn [YP09.cbyte YP09.c_off YP09.c_val] in Hb1, Hb2. injection Hb1 as <-.
rewrite !Z.add_0_r in Hb2. cbn [Z.of_nat]. rewrite Z.add_0_r. rewrite Hb2. f_equal.
unfold YP09.byte_of_word. rewrite Hz, Z_to_bv_unsigned.
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with 256. change (bv_modulus 64) with (2 ^ 64).
unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
change (2 ^ 8) with 256. rewrite !Z.shiftr_0_r. rewrite !Z.mod_mod by lia.
apply rp_R10_mod256.
Qed.

(* a val_mem survives a memory change that fixes its bytes. *)
Lemma rp_R10_vmove : forall (m m' : word -> option byte) (a : Z) (n : nat) (v : Z),
(forall k, (k < n)%nat -> m' (Z_to_bv 64 (a + Z.of_nat k)) = m (Z_to_bv 64 (a + Z.of_nat k))) ->
val_mem SEGS m a n v -> val_mem SEGS m' a n v.
Proof.
intros m m' a n v H HV k Hk. unfold YP09.mbyte. rewrite (H k Hk). exact (HV k Hk).
Qed.

Lemma rp_R10_shbnd : forall ly3 S3 W3 mem3 md3 cid p,
AR SEGS B ly3 S3 W3 mem3 md3 -> In (cid, p) (frames S3) ->
2147450880 <= shadow_addr (frame_addr ly3 cid p) /\
shadow_addr (frame_addr ly3 cid p) + fs_frame_bytes cid / 8 <= 17594332446736 /\
8 * (frame_addr ly3 cid p / 8) = frame_addr ly3 cid p /\
8 * (fs_frame_bytes cid / 8) = fs_frame_bytes cid /\
shadow_addr (frame_addr ly3 cid p) = 2147450880 + frame_addr ly3 cid p / 8.
Proof.
intros ly3 S3 W3 mem3 md3 cid p HAR Hin.
pose proof (frames_bounds SEGS B LAWS ly3 S3 W3 mem3 md3 cid p HAR Hin) as (H1 & H2 & _).
destruct (frame_al64 SEGS B ly3 S3 W3 mem3 md3 cid p HAR Hin) as (A1 & A2 & A3).
pose proof asan_consts as (C1 & _ & _ & _ & _).
assert (D1 : frame_addr ly3 cid p = 8 * (frame_addr ly3 cid p / 8) + frame_addr ly3 cid p mod 8)
by (apply Z.div_mod; lia).
assert (D2 : fs_frame_bytes cid = 8 * (fs_frame_bytes cid / 8) + fs_frame_bytes cid mod 8)
by (apply Z.div_mod; lia).
assert (M1 : frame_addr ly3 cid p mod 8 = 0).
{ pose proof (Z.div_mod (frame_addr ly3 cid p) 64 ltac:(lia)) as Q. rewrite A1 in Q.
pose proof (Z.mod_pos_bound (frame_addr ly3 cid p) 8 ltac:(lia)). lia. }
assert (M2 : fs_frame_bytes cid mod 8 = 0).
{ pose proof (Z.div_mod (fs_frame_bytes cid) 64 ltac:(lia)) as Q. rewrite A2 in Q.
pose proof (Z.mod_pos_bound (fs_frame_bytes cid) 8 ltac:(lia)). lia. }
unfold shadow_addr, SHADOW_OFF. repeat split; lia.
Qed.

Lemma rp_R10_notw : forall ly3 S3 W3 mem3 md3 pos a,
AR SEGS B ly3 S3 W3 mem3 md3 -> In (1, pos) (frames S3) ->
rp_R10_prot ly3 S3 pos a ->
~ (frame_addr ly3 1 pos <= a < frame_addr ly3 1 pos + 128) /\
~ (shadow_addr (frame_addr ly3 1 pos) <= a < shadow_addr (frame_addr ly3 1 pos) + 16).
Proof.
intros ly3 S3 W3 mem3 md3 pos a HAR Hin HP.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (EFB : fs_frame_bytes 1 = 128) by reflexivity.
pose proof (frames_bounds SEGS B LAWS ly3 S3 W3 mem3 md3 1 pos HAR Hin) as (HG1 & HG2 & HG3).
rewrite EFB in HG2, HG3.
destruct (rp_R10_shbnd ly3 S3 W3 mem3 md3 1 pos HAR Hin) as (SB1 & SB2 & SB3 & _ & SB5).
rewrite EFB in SB2. change (128 / 8) with 16 in SB2.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HG3.
destruct HP as [Hc | [(b & n & Hb & Hba) | [Himg | [(cid & p & Hcp & Hne & Hor)
| (x & Hx & Hxn & Hax)]]]].
- split; lia.
- pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 mem3 md3 b n 1 pos HAR Hb Hin) as HD.
unfold zdisjoint in HD. cbn [fst snd] in HD. rewrite EFB in HD.
destruct (al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 b n HAR Hb) as (_ & Hb4 & Hbc & Hbapp & _).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp.
split; lia.
- pose proof (pa_segs_low a Himg) as Hlo. unfold kLowMemEnd in Hlo.
split; [|lia].
intros Hr.
destruct (al_client_img _ _ LAWS ly3 S3 W3 mem3 md3 a HAR
ltac:(right; left; exists 1, pos; split; [exact Hin|]; rewrite EFB; lia)) as (_ & Hni).
exact (Hni Himg).
- destruct (al_sep _ _ LAWS ly3 S3 W3 mem3 md3 HAR) as [Hp _].
apply pairwise_app_l in Hp as [_ Hpf].
assert (HD : zdisjoint (frame_addr ly3 1 pos, fs_frame_bytes 1)
(frame_addr ly3 cid p, fs_frame_bytes cid)).
{ apply (pairwise_zdisjoint_split _ _ _ Hpf).
exact (map_split_2 (fun f : Z * Z => (frame_addr ly3 (fst f) (snd f), fs_frame_bytes (fst f)))
_ _ _ (in_split_2 _ _ _ Hin Hcp ltac:(intros Hq; apply Hne; symmetry; exact Hq))). }
unfold zdisjoint in HD. cbn [fst snd] in HD. rewrite EFB in HD.
destruct (rp_R10_shbnd ly3 S3 W3 mem3 md3 cid p HAR Hcp) as (TB1 & TB2 & TB3 & TB4 & TB5).
destruct (al_frames _ _ LAWS ly3 S3 W3 mem3 md3 cid p HAR Hcp) as (_ & Happ2 & _ & _).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ2.
destruct Hor as [Hor | Hor]; unfold in_zr in Hor; cbn [fst snd] in Hor; split; lia.
- subst a.
assert (Dx : x = 8 * (x / 8) + x mod 8) by (apply Z.div_mod; lia).
assert (Drx : 0 <= x mod 8 < 8) by (apply Z.mod_pos_bound; lia).
unfold SHADOW_OFF. split; lia.
Qed.

(* R10  C12 -> C13, 0x84220..0x84270 (+0x294..+0x2e4). The retire word 0x45e0360e at G, `beqz s2` at 0x8422c
   not taken (G >= 4096), then the 16 shadow bytes := f5; `paj_run_to_tok` stopping at +0x2e8.
   Donors: B `rp_td_side` :3140, `rr_TI_fr` :2990; A18 `seg_epi` :1303 (side arm). Difficulty: easy-medium. *)
Lemma rp_R10 : rp_from_C13 -> rp_from_C12.
Proof.
intros F13 cx pos regs3 ly3 S3 W3 mem3 md3 HB HC.
destruct HC as (HJH & HCAR & HFRG & HFP & HFW & HSHD & HA0 & HCELL).
destruct HJH as (HJ & HLY & HFRS & HNIN & HAB & HCNT).
destruct HCAR as (HREGS & HKEPT & HSAVED & HMSG & HOUT & HROD).
destruct HFRG as (R18 & R26 & R25).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _ & _).
assert (Hin1 : In (1, pos) (frames S3)) by (rewrite HFRS; left; reflexivity).
assert (EFA : frame_addr ly3 1 pos = rp_G cx pos)
by (unfold rp_G, frame_addr; rewrite (proj1 HLY); reflexivity).
pose proof (frames_bounds SEGS B LAWS ly3 S3 W3 mem3 md3 1 pos HAR Hin1) as (HG1 & HG2 & HG3).
destruct (al_frames _ _ LAWS ly3 S3 W3 mem3 md3 1 pos HAR Hin1) as (HGal & _ & HGpres & HGsh).
rewrite EFA in HG1, HG2, HG3, HGal, HGpres, HGsh.
assert (EFB : fs_frame_bytes 1 = 128) by reflexivity.
rewrite EFB in HG2, HG3, HGpres, HGsh.
change (128 / 8) with 16 in HGsh.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (GG := rp_G cx pos) in *.
assert (HGlt : 0 <= GG < 2 ^ 64) by (change (2 ^ 64) with 18446744073709551616; lia).
assert (Dq : GG = 8 * (GG / 8) + GG mod 8) by (apply Z.div_mod; lia).
assert (Dr : 0 <= GG mod 8 < 8) by (apply Z.mod_pos_bound; lia).
assert (HSGlt : 0 <= shadow_addr GG < 2 ^ 64)
by (unfold shadow_addr, SHADOW_OFF; change (2 ^ 64) with 18446744073709551616; lia).
assert (HSGhi : shadow_addr GG + 16 <= 18446744073709551616)
by (unfold shadow_addr, SHADOW_OFF; lia).
assert (HDISJ : GG + 128 <= shadow_addr GG \/ shadow_addr GG + 16 <= GG).
{ destruct HG3 as (_ & [Hlow | [Hhi _]]).
- left. unfold shadow_addr, SHADOW_OFF, kLowShadowBeg in *. lia.
- right. unfold shadow_addr, SHADOW_OFF, kHighMemBeg in *. lia. }
remember (Eimg (Ereg regs3 (@nil word))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs3 (@nil word)) n)
by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E18 : ew E 18%nat = getr regs3 18)
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs3 _ 18%nat 18%bv eq_refl)).
assert (E25 : ew E 25%nat = getr regs3 25)
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs3 _ 25%nat 25%bv eq_refl)).
assert (E26 : ew E 26%nat = getr regs3 26)
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs3 _ 26%nat 26%bv eq_refl)).
assert (U18 : bv_unsigned (ew E 18%nat) = GG)
by (rewrite E18, R18; unfold w64; apply unsigned_lit_small; lia).
assert (U26 : bv_unsigned (ew E 26%nat) = GG)
by (rewrite E26, R26; unfold w64; apply unsigned_lit_small; lia).
assert (U25 : bv_unsigned (ew E 25%nat) = shadow_addr GG)
by (rewrite E25, R25; unfold w64; apply unsigned_lit_small; lia).
assert (P64 : (2 : Z) ^ 64 = 18446744073709551616) by reflexivity.
assert (HR12 : Forall (region_ok SEGS E (mrestrict (w_H W3) mem3))
[YP09.mkRegion (Some 26%nat) 0 8 0 8 []; YP09.mkRegion (Some 25%nat) 0 16 0 16 []]).
{ apply Forall_cons.
- unfold region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite U26, P64. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
intros o Ho. apply (apresent_writable SEGS). exact (proj1 (HGpres (GG + o) ltac:(lia))).
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite U25, P64. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
intros o Ho. apply (apresent_writable SEGS). exact (proj1 (HGsh o ltac:(lia))). }
assert (HS : st_ok_pi SEGS VAL E
(mkSS (AF_reac_ctrl_identity_reply + 0x294) sr_atoms
[YP09.mkRegion (Some 26%nat) 0 8 0 8 []; YP09.mkRegion (Some 25%nat) 0 16 0 16 []]
None (mkFacts [(18%nat, HPTR 5)] [] []))
(restrict (w_H W3) (mkst regs3 (w64 (rp_pc 0x294)) mem3 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold w64, rp_pc, A_reac_ctrl_identity_replyP.
replace (BASE + AF_reac_ctrl_identity_reply + 0x294)
with (BASE + (AF_reac_ctrl_identity_reply + 0x294)) by ring.
change AB1v.tfibsegs with (@pa_segs _ ctrl_listing CtrlImg.PI_ctrl).
apply (pa_entry_st_ok_full E (AF_reac_ctrl_identity_reply + 0x294) sr_atoms regs3
[YP09.mkRegion (Some 26%nat) 0 8 0 8 []; YP09.mkRegion (Some 25%nat) 0 16 0 16 []]
(mkFacts [(18%nat, HPTR 5)] [] []) (mrestrict (w_H W3) mem3)).
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute; reflexivity.
- exact HR12.
- apply pairwise_disjoint_of_extents. unfold extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U25, U26.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; [exact I | exact I]].
cbn [f_atoms atoms_ok]. split; [|exact I]. unfold afact_ok, HPTR.
cbn [af_lo af_hi af_al2]. rewrite U18. change (2 ^ 5) with 32.
split; [lia|]. split; [exact HGal | lia]. }
pose proof (SRr_run_to_pi_AJ (PI := CtrlImg.PI_ctrl) B LAWS) as RUNTOP.
unfold cfg_at.
paj_run_to_sh RUNTOP HS HJ (AF_reac_ctrl_identity_reply + 0x2e8).
{ intros a (r & Hin & Ha).
unfold rp_own1, awr_byte, in_frames. right; right; right.
exists 1, pos. split; [left; reflexivity|].
cbn [In] in Hin. rewrite EFB.
destruct Hin as [<- | [<- | []]];
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Ha.
- left. rewrite U26 in Ha. rewrite EFA. unfold in_zr. cbn [fst snd]. lia.
- right. rewrite U25 in Ha. rewrite EFA. unfold in_zr. cbn [fst snd].
change (128 / 8) with 16. lia. }
(* ---- what the stretch kept ---------------------------------------------------------------- *)
destruct (rp_R10_shbnd ly3 S3 W3 mem3 md3 1 pos HAR Hin1) as (SBa & SBb & SBc & _ & SBe).
rewrite EFA in SBa, SBb, SBc, SBe. rewrite EFB in SBb. change (128 / 8) with 16 in SBb.
assert (HG3u : 4096 <= GG /\ (GG + 128 <= 2147446784 \/
(17594333495296 <= GG /\ GG + 128 <= alloc_ceiling)))
by (unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HG3; exact HG3).
assert (EFAg : forall c q, frame_addr ly3 c q = frame_addr (rc_lyc cx) c q)
by (intros c q; unfold frame_addr; rewrite (proj1 HLY); reflexivity).
destruct Hstk as (Jsp16 & JSTK0 & Jclo & Jlosp & Jsphi & Jhi47 & Jbot & Jtop1 & Jtop2).
pose proof HB as HB'.
destruct HB' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
HBlo & HBhi & _ & HBg & HBmsg & HBout).
pose proof rp_stk as (Tstk & Pstk).
assert (HSlo : alloc_ceiling + TREPLY_STK <= rp_S cx) by lia.
assert (HShi : rp_S cx <= 2 ^ 47) by lia.
assert (KEEPM : forall x : word,
~ (GG <= bv_unsigned x < GG + 8) ->
~ (shadow_addr GG <= bv_unsigned x < shadow_addr GG + 16) ->
mrestrict (w_H W3) (ms_mem ms) x = mrestrict (w_H W3) mem3 x).
{ intros x H1 H2. apply HFr. intros (r & Hin0 & Ha). cbn [In] in Hin0.
destruct Hin0 as [Hr | [Hr | []]]; subst r;
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
[rewrite U26 in Ha | rewrite U25 in Ha]; lia. }
assert (KEEPV : forall a, 0 <= a < 2 ^ 64 ->
~ (GG <= a < GG + 8) -> ~ (shadow_addr GG <= a < shadow_addr GG + 16) ->
aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha H1 H2. unfold aview, YP09.mbyte.
rewrite (KEEPM (Z_to_bv 64 a)); [reflexivity | |];
rewrite unsigned_lit_small by lia; assumption. }
assert (PROTM : forall a, 0 <= a < 2 ^ 64 -> rp_R10_prot ly3 S3 pos a ->
mrestrict (w_H W3) (ms_mem ms) (Z_to_bv 64 a) = mrestrict (w_H W3) mem3 (Z_to_bv 64 a)).
{ intros a Ha HP.
destruct (rp_R10_notw ly3 S3 W3 mem3 md3 pos a HAR Hin1 HP) as (N1 & N2).
rewrite EFA in N1, N2. apply KEEPM; rewrite unsigned_lit_small by lia; lia. }
assert (PROTV : forall a, 0 <= a < 2 ^ 64 -> rp_R10_prot ly3 S3 pos a ->
aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha HP.
destruct (rp_R10_notw ly3 S3 W3 mem3 md3 pos a HAR Hin1 HP) as (N1 & N2).
rewrite EFA in N1, N2. apply KEEPV; lia. }
assert (FRMM : forall a, GG + 8 <= a < GG + 128 ->
mrestrict (w_H W3) (ms_mem ms) (Z_to_bv 64 a) = mrestrict (w_H W3) mem3 (Z_to_bv 64 a))
by (intros a Ha; apply KEEPM; rewrite unsigned_lit_small by lia; lia).
assert (FRMV : forall a, GG + 8 <= a < GG + 128 ->
aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) mem3 a)
by (intros a Ha; apply KEEPV; lia).
(* ---- the two regions the run wrote -------------------------------------------------------- *)
pose proof HS as HSc.
destruct HSc as (_ & _ & _ & _ & _ & _ & _ & HMOK & _).
destruct HMOK as (_ & HROK & _).
pose proof (Forall_inv HROK) as HRF.
pose proof (Forall_inv (Forall_inv_tail HROK)) as HRS.
destruct HRF as (_ & _ & _ & HCF). destruct HRS as (_ & _ & _ & HCS).
cbn [YP09.r_base YP09.r_chunks base_val] in HCF, HCS.
rewrite U26 in HCF. rewrite U25 in HCS.
assert (VWORD : val_mem SEGS (mrestrict (w_H W3) (ms_mem ms)) GG 8%nat 1172321806).
{ pose proof (val_of_chunk_ok SEGS E (mrestrict (w_H W3) (ms_mem ms)) GG 0 8
(SLit 1172321806) 1172321806 (Forall_inv HCF) ltac:(reflexivity)
ltac:(cbn; lia) ltac:(cbn; lia)) as HV.
rewrite Z.add_0_r in HV. exact HV. }
assert (SHV1 : forall off, 0 <= off < 16 ->
val_mem SEGS (mrestrict (w_H W3) (ms_mem ms)) (shadow_addr GG + off) 1%nat 245).
{ intros off Hoff.
assert (HIN : In (YP09.mkChunk off (CVal 1 (SLit 18446744073709551605)))
[YP09.mkChunk 11 (CVal 1 (SLit 18446744073709551605));
YP09.mkChunk 10 (CVal 1 (SLit 18446744073709551605));
YP09.mkChunk 9 (CVal 1 (SLit 18446744073709551605));
YP09.mkChunk 8 (CVal 1 (SLit 18446744073709551605));
YP09.mkChunk 15 (CVal 1 (SLit 18446744073709551605));
YP09.mkChunk 14 (CVal 1 (SLit 18446744073709551605));
YP09.mkChunk 13 (CVal 1 (SLit 18446744073709551605));
YP09.mkChunk 12 (CVal 1 (SLit 18446744073709551605));
YP09.mkChunk 3 (CVal 1 (SLit 18446744073709551605));
YP09.mkChunk 2 (CVal 1 (SLit 18446744073709551605));
YP09.mkChunk 1 (CVal 1 (SLit 18446744073709551605));
YP09.mkChunk 0 (CVal 1 (SLit 18446744073709551605));
YP09.mkChunk 7 (CVal 1 (SLit 18446744073709551605));
YP09.mkChunk 6 (CVal 1 (SLit 18446744073709551605));
YP09.mkChunk 5 (CVal 1 (SLit 18446744073709551605));
YP09.mkChunk 4 (CVal 1 (SLit 18446744073709551605))]).
{ assert (Ho : off = 0 \/ off = 1 \/ off = 2 \/ off = 3 \/ off = 4 \/ off = 5 \/ off = 6 \/
off = 7 \/ off = 8 \/ off = 9 \/ off = 10 \/ off = 11 \/ off = 12 \/ off = 13 \/ off = 14 \/
off = 15) by lia.
repeat (destruct Ho as [-> | Ho]); try (subst off); cbn [In]; tauto. }
pose proof (proj1 (Forall_forall _ _) HCS _ HIN) as HC.
pose proof (rp_R10_vm1 E (mrestrict (w_H W3) (ms_mem ms)) (shadow_addr GG) off
(SLit 18446744073709551605) 18446744073709551605 HC ltac:(reflexivity)) as HV.
replace (18446744073709551605 mod 256) with 245 in HV by reflexivity. exact HV. }
(* ---- the registers ------------------------------------------------------------------------ *)
assert (HAE : env_agree 32 (Ereg regs3 (@nil word)) E)
by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
assert (RK : forall r, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 10%bv; 18%bv; 19%bv; 20%bv; 21%bv;
22%bv; 23%bv; 25%bv; 26%bv; 27%bv] -> getr (ms_regs ms) r = getr regs3 r).
{ intros r Hr.
exact (regs_kept_of_st_ok_pi E _ _ regs3 (@nil word)
[2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 10%bv; 18%bv; 19%bv; 20%bv; 21%bv;
22%bv; 23%bv; 25%bv; 26%bv; 27%bv] HS HAE
ltac:(vm_compute; reflexivity) r Hr). }
(* ---- the cut C13 -------------------------------------------------------------------------- *)
pmkst HS. cbn [ss_pc].
assert (EPC : BASE + 13208 = rp_pc 0x2e8)
by (unfold rp_pc, A_reac_ctrl_identity_replyP, AF_reac_ctrl_identity_reply; lia).
rewrite EPC.
apply (F13 cx pos (ms_regs ms) ly3 S3 W3 (ms_mem ms) _ HB).
(* ---- the eight parts of C13 --------------------------------------------------------------- *)
assert (SHR : forall x, 0 <= x < alloc_ceiling -> 0 <= SHADOW_OFF + x / 8 < 2 ^ 64).
{ intros x Hx. pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)).
unfold SHADOW_OFF. lia. }
assert (FRDISJ : forall cid q, In (cid, q) (frames (rc_Sc cx)) ->
GG + 128 <= frame_addr ly3 cid q \/ frame_addr ly3 cid q + fs_frame_bytes cid <= GG).
{ intros cid q Hcq.
assert (Hin3 : In (cid, q) (frames S3)) by (rewrite HFRS; right; exact Hcq).
destruct (al_sep _ _ LAWS ly3 S3 W3 mem3 md3 HAR) as [Hp _].
apply pairwise_app_l in Hp as [_ Hpf].
assert (HD : zdisjoint (frame_addr ly3 1 pos, fs_frame_bytes 1)
(frame_addr ly3 cid q, fs_frame_bytes cid)).
{ apply (pairwise_zdisjoint_split _ _ _ Hpf).
exact (map_split_2 (fun f : Z * Z => (frame_addr ly3 (fst f) (snd f), fs_frame_bytes (fst f)))
_ _ _ (in_split_2 _ _ _ Hin1 Hin3 ltac:(intros Hq; injection Hq as <- <-; exact (HNIN Hcq)))). }
unfold zdisjoint in HD. cbn [fst snd] in HD. rewrite EFA, EFB in HD. exact HD. }
assert (POTHER : forall cid q a, In (cid, q) (frames (rc_Sc cx)) ->
(in_zr a (frame_rng (rc_lyc cx) (cid, q)) \/
in_zr a (shadow_addr (frame_addr (rc_lyc cx) cid q), fs_frame_bytes cid / 8)) ->
0 <= a < 2 ^ 64 /\ rp_R10_prot ly3 S3 pos a).
{ intros cid q a Hcq Hor.
assert (Hin3 : In (cid, q) (frames S3)) by (rewrite HFRS; right; exact Hcq).
pose proof (frames_bounds SEGS B LAWS ly3 S3 W3 mem3 md3 cid q HAR Hin3) as (F1 & F2 & _).
destruct (rp_R10_shbnd ly3 S3 W3 mem3 md3 cid q HAR Hin3) as (T1 & T2 & _ & _ & _).
unfold frame_rng in Hor. cbn [fst snd] in Hor.
rewrite <- (EFAg cid q) in Hor.
assert (Hor' := Hor). unfold in_zr in Hor'. cbn [fst snd] in Hor'.
split; [lia|].
right; right; right; left. exists cid, q. split; [exact Hin3|].
split; [intros Hq; injection Hq as -> ->; exact (HNIN Hcq)|]. exact Hor. }
assert (PFRAME : forall cid q a, In (cid, q) (frames (rc_Sc cx)) ->
in_zr a (frame_rng (rc_lyc cx) (cid, q)) ->
(0 <= a < 2 ^ 64 /\ rp_R10_prot ly3 S3 pos a) /\
(0 <= SHADOW_OFF + a / 8 < 2 ^ 64 /\ rp_R10_prot ly3 S3 pos (SHADOW_OFF + a / 8))).
{ intros cid q a Hcq Hor.
assert (Hin3 : In (cid, q) (frames S3)) by (rewrite HFRS; right; exact Hcq).
pose proof (frames_bounds SEGS B LAWS ly3 S3 W3 mem3 md3 cid q HAR Hin3) as (F1 & F2 & _).
pose proof (FRDISJ cid q Hcq) as FD.
assert (Hor' := Hor). unfold frame_rng, in_zr in Hor'. cbn [fst snd] in Hor'.
rewrite <- (EFAg cid q) in Hor'.
split; [exact (POTHER cid q a Hcq (or_introl Hor))|].
split; [apply SHR; lia|].
right; right; right; right. exists a. split; [lia|]. split; [rewrite EFA; lia | reflexivity]. }
unfold rp_C13.
split.
{ unfold rp_jhold. split; [exact HJ|]. split; [exact HLY|]. split; [exact HFRS|].
split; [exact HNIN|]. split; [exact HAB | exact HCNT]. }
split.
{ unfold rp_carry. split.
{ destruct HREGS as (Q2 & Q3 & Q4 & Q8 & Q9 & Q19 & Q20 & Q21 & Q22 & Q23 & Q27).
unfold rp_regs_ok.
split; [rewrite (RK 2%bv ltac:(cbn [In]; tauto)); exact Q2|].
split; [rewrite (RK 3%bv ltac:(cbn [In]; tauto)); exact Q3|].
split; [rewrite (RK 4%bv ltac:(cbn [In]; tauto)); exact Q4|].
split; [rewrite (RK 8%bv ltac:(cbn [In]; tauto)); exact Q8|].
split; [rewrite (RK 9%bv ltac:(cbn [In]; tauto)); exact Q9|].
split; [rewrite (RK 19%bv ltac:(cbn [In]; tauto)); exact Q19|].
split; [rewrite (RK 20%bv ltac:(cbn [In]; tauto)); exact Q20|].
split; [rewrite (RK 21%bv ltac:(cbn [In]; tauto)); exact Q21|].
split; [rewrite (RK 22%bv ltac:(cbn [In]; tauto)); exact Q22|].
split; [rewrite (RK 23%bv ltac:(cbn [In]; tauto)); exact Q23|].
rewrite (RK 27%bv ltac:(cbn [In]; tauto)); exact Q27. }
split.
{ unfold rp_kept. split; [exact (proj1 HKEPT)|].
destruct (proj2 HKEPT) as (K1 & K2 & K3 & K4 & K5 & K6).
split.
{ intros a Ha Hn HnE.
etransitivity; [exact (PROTV a ltac:(lia) ltac:(left; lia)) | exact (K1 a Ha Hn HnE)]. }
split.
{ intros b n i Hb Hi HnE.
assert (Hb3 : In (b, n) (ablocks B ly3 S3)) by (rewrite HAB; exact Hb).
destruct (al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 b n HAR Hb3) as (_ & Bf1 & Bf2 & _ & _).
etransitivity;
[exact (PROTV (b + i) ltac:(lia) ltac:(right; left; exists b, n; split; [exact Hb3 | lia]))
| exact (K2 b n i Hb Hi HnE)]. }
split.
{ intros a Himg Hno Herr. pose proof (pa_segs_low a Himg) as Hlo. unfold kLowMemEnd in Hlo.
etransitivity; [exact (PROTV a ltac:(lia) ltac:(right; right; left; exact Himg))
| exact (K3 a Himg Hno Herr)]. }
split.
{ intros cid q a Hcq Hor HnE.
destruct (POTHER cid q a Hcq Hor) as (PR1 & PR2).
etransitivity; [exact (PROTV a PR1 PR2) | exact (K4 cid q a Hcq Hor HnE)]. }
split.
{ intros a Ha Hn Hp0. exact (apresent_grows _ _ _ _ HG (K5 a Ha Hn Hp0)). }
{ intros a Ha. exact (apresent_grows _ _ _ _ HG (K6 a Ha)). } }
split.
{ unfold rp_saved in HSAVED |- *. rewrite Forall_forall in HSAVED |- *.
intros p Hp.
assert (Hfp : 8 <= fst p <= 104).
{ unfold rp_saves in Hp. cbn [In] in Hp.
repeat (destruct Hp as [<- | Hp]); cbn [fst]; lia. }
eapply rp_R10_vmove; [|exact (HSAVED p Hp)].
intros k Hk. apply PROTM; [lia | left; lia]. }
split.
{ unfold rp_msg in HMSG |- *. intros Hargs Hlen.
destruct (HMSG Hargs Hlen) as (HGARR & HTSRC).
destruct (HBmsg Hargs Hlen) as ((nb & Hnb & Hnbs) & _ & _).
assert (Hnb3 : In (rc_fr cx, nb) (ablocks B ly3 S3)) by (rewrite HAB; exact Hnb).
destruct (al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 (rc_fr cx) nb HAR Hnb3)
as (_ & Bf1 & Bf2 & _ & _).
pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 mem3 md3 (rc_fr cx) nb 1 pos HAR Hnb3 Hin1)
as HDB. unfold zdisjoint in HDB. cbn [fst snd] in HDB. rewrite EFA, EFB in HDB.
assert (PFR : forall a, rc_fr cx <= a < rc_fr cx + 50 ->
(0 <= a < 2 ^ 64 /\ rp_R10_prot ly3 S3 pos a) /\
(0 <= SHADOW_OFF + a / 8 < 2 ^ 64 /\ rp_R10_prot ly3 S3 pos (SHADOW_OFF + a / 8))).
{ intros a Ha.
split; [split; [lia | right; left; exists (rc_fr cx), nb; split; [exact Hnb3 | lia]]|].
split; [apply SHR; lia|].
right; right; right; right. exists a. split; [lia|]. split; [lia | reflexivity]. }
split.
{ intros j Hj. destruct (HGARR j Hj) as (CV & CR). split; [|exact CR].
rewrite length_map in Hj. rewrite HBg in Hj.
eapply rp_R10_vmove; [|exact CV]. intros k Hk.
assert (Hk0 : k = 0%nat) by lia. subst k.
destruct (PFR (rc_fr cx + Z.of_nat j + Z.of_nat 0) ltac:(lia)) as ((P1 & P2) & _).
exact (PROTM _ P1 P2). }
destruct HTSRC as (T1 & T2 & T3 & T4 & T5 & T6).
split.
{ intros a Ha. destruct (T1 a Ha) as (TV & TS). split; [|exact TS].
eapply (aview_keeps_vis SEGS); [exact HG | exact TV]. }
split.
{ eapply range_addressable_agree; [|exact T2]. intros x Hx.
destruct (PFR x Hx) as (_ & (P1 & P2)). exact (PROTV _ P1 P2). }
split; [|split; [exact T4 | split; [exact T5 | exact T6]]].
intros s Hs. eapply (aview_keeps_vis SEGS); [exact HG | exact (T3 s Hs)]. }
split.
{ unfold rp_out in HOUT |- *. intros Hargs.
destruct (HOUT Hargs) as (O1 & O2 & O3 & O4).
destruct (HBout Hargs) as (_ & _ & _ & _ & _ & _ & HCFR & _ & _ & _ & _ & _ & _).
assert (PO : forall a, treply_out (rc_pa cx) (rc_pp cx) (rc_pn cx) a ->
(0 <= a < 2 ^ 64 /\ rp_R10_prot ly3 S3 pos a) /\
(0 <= SHADOW_OFF + a / 8 < 2 ^ 64 /\ rp_R10_prot ly3 S3 pos (SHADOW_OFF + a / 8))).
{ intros a Hta. destruct (HCFR a Hta) as (cid & q & Hcq & Hzr).
exact (PFRAME cid q a Hcq Hzr). }
split.
{ eapply range_addressable_agree; [|exact O1]. intros x Hx.
destruct (PO x ltac:(unfold treply_out; left; lia)) as (_ & (P1 & P2)).
exact (PROTV _ P1 P2). }
split.
{ eapply range_addressable_agree; [|exact O2]. intros x Hx.
destruct (PO x ltac:(unfold treply_out; right; left; lia)) as (_ & (P1 & P2)).
exact (PROTV _ P1 P2). }
split.
{ eapply range_addressable_agree; [|exact O3]. intros x Hx.
destruct (PO x ltac:(unfold treply_out; right; right; lia)) as (_ & (P1 & P2)).
exact (PROTV _ P1 P2). }
intros a Hta. exact (apresent_grows _ _ _ _ HG (O4 a Hta)). }
{ unfold YE01.arodata_okS in HROD |- *. intros a Hsrc Hno Herr.
assert (Himg : in_img SEGS a).
{ destruct Hsrc as [(s & Hs & _ & Hr) | Hr];
[exists s; split; [exact Hs | exact Hr] | exact (RELRO_IMG a Hr)]. }
pose proof (pa_segs_low a Himg) as Hlo. unfold kLowMemEnd in Hlo.
etransitivity; [exact (PROTV a ltac:(lia) ltac:(right; right; left; exact Himg))
| exact (HROD a Hsrc Hno Herr)]. } }
split.
{ unfold rp_fregs.
split; [rewrite (RK 18%bv ltac:(cbn [In]; tauto)); exact R18|].
split; [rewrite (RK 26%bv ltac:(cbn [In]; tauto)); exact R26|].
rewrite (RK 25%bv ltac:(cbn [In]; tauto)); exact R25. }
split.
{ unfold rp_fpres in HFP |- *. intros a Ha.
exact (apresent_grows _ _ _ _ HG (HFP a Ha)). }
split.
{ unfold rp_fwords in HFW |- *. destruct HFW as (_ & FW8 & FW16 & FWfl).
split; [exact VWORD|].
split. { eapply rp_R10_vmove; [|exact FW8]. intros k Hk. apply FRMM. lia. }
split. { eapply rp_R10_vmove; [|exact FW16]. intros k Hk. apply FRMM. lia. }
unfold rdword in FWfl |- *. rewrite !FRMV by lia. exact FWfl. }
split.
{ unfold rp_shadow, shadow_cells. intros i Hi.
unfold rp_sg_f5 in Hi |- *. cbn [length] in Hi.
assert (HEN : nth_error [245; 245; 245; 245; 245; 245; 245; 245; 245; 245; 245; 245; 245; 245;
245; 245] i = Some 245)
by (do 16 (destruct i as [|i]; [reflexivity|]); cbn [length] in Hi; lia).
rewrite HEN. apply (aview_of_val_mem1 SEGS); [|lia].
exact (SHV1 (Z.of_nat i) ltac:(lia)). }
split.
{ rewrite (RK 10%bv ltac:(cbn [In]; tauto)). exact HA0. }
{ intros Hok.
assert (Hargs : rp_argsb cx = true).
{ unfold rp_okb, reply_ok in Hok. apply andb_prop in Hok. exact (proj1 Hok). }
destruct (HCELL Hok) as (CA & CP & CN).
destruct (HBout Hargs) as (_ & _ & _ & _ & _ & _ & HCFR & _ & _ & _ & _ & _ & _).
assert (PO : forall a, treply_out (rc_pa cx) (rc_pp cx) (rc_pn cx) a ->
0 <= a < 2 ^ 64 /\ rp_R10_prot ly3 S3 pos a).
{ intros a Hta. destruct (HCFR a Hta) as (cid & q & Hcq & Hzr).
exact (proj1 (PFRAME cid q a Hcq Hzr)). }
unfold rp_cells.
split.
{ intros j Hj. destruct (CA j Hj) as (CV & CR). split; [|exact CR].
rewrite length_map in Hj. unfold reply_addr in Hj. cbn [length] in Hj.
eapply rp_R10_vmove; [|exact CV]. intros k Hk.
assert (Hk0 : k = 0%nat) by lia. subst k.
destruct (PO (rc_pa cx + Z.of_nat j + Z.of_nat 0) ltac:(unfold treply_out; left; lia))
as (P1 & P2). exact (PROTM _ P1 P2). }
split.
{ eapply rp_R10_vmove; [|exact CP]. intros k Hk.
destruct (PO (rc_pp cx + Z.of_nat k) ltac:(unfold treply_out; right; left; lia)) as (P1 & P2).
exact (PROTM _ P1 P2). }
{ eapply rp_R10_vmove; [|exact CN]. intros k Hk.
destruct (PO (rc_pn cx + Z.of_nat k) ltac:(unfold treply_out; right; right; lia)) as (P1 & P2).
exact (PROTM _ P1 P2). } }
Qed.

(* R11  C13 -> C14, 0x84274..0x842bc (+0x2e8..+0x330): the inline flag release. `fs_rwA` + `add_flag_regionA`
   make FL writable, then `paj_run_flag_sh RUNF` with `RUNF := aj_flag_store_pi B LAWS ML ASF FFL` (CtrlFrame.v
   :460, cgif's macro `exitRAX` lib/A/ACa7.v:484): the obligations are that every written address is
   inside `awr_byte` or is `flag_addr lyc 1 pos`, and that the flag byte reads 0 after. The journal then drops
   (1,pos) from own and the state becomes `stack_free_state 1 pos`, which is C14. The run is stopped at +0x334
   (the engine would otherwise fold the whole epilogue into it).
   Donors: B `rp_epi` :3303, `rr_TI_flag` :3045; A18 `seg_epi` :1303, `rr_cls_set` :1195. Difficulty: medium. *)
(* LOCAL helpers of this stretch (kit-free; see the report): the symbolic entry state of C13.
   atom 32 = the own fake frame's base G, atom 33 = its flag address FL. *)
Definition rp_R11_extra (cx : rcx) (pos : Z) : list word :=
[Z_to_bv 64 (rp_G cx pos); Z_to_bv 64 (rp_FL cx pos)].
Definition rp_R11_E (cx : rcx) (pos : Z) (regs3 : bvmap 5 word) : env :=
Eimg (Ereg regs3 (rp_R11_extra cx pos)).
(* the flag byte (writable) and the frame's last word, which holds the flag address *)
Definition rp_R11_rs : smem :=
[ YP09.mkRegion (Some 33%nat) 0 1 0 1 [];
YP09.mkRegion (Some 18%nat) 120 128 0 0 [YP09.mkChunk 120 (CVal 8 (SOff 33 0))] ].
Definition rp_R11_ss : sstate :=
mkSS (AF_reac_ctrl_identity_reply + 0x2e8) sr_atoms rp_R11_rs None (mkFacts [] [] []).

Lemma rp_R11 : rp_from_C14 -> rp_from_C13.
Proof.
intros F14 cx pos regs3 ly3 S3 W3 mem3 md3 HB HC.
pose proof pa_segs_low as SEGLOW.
pose proof asan_consts as (CA1 & CA2 & CA3 & CA4 & CA5).
destruct HC as (HJH & HCAR & HFRG & HFPR & HFW & HSH & HA0 & HCELL).
destruct HJH as (HJ & HLY & HFRS & HNIN & HABL & HCNT).
destruct HCAR as (HREGS & HKEPT & HSAVED & HMSG & HOUT & HRO).
destruct HKEPT as (HWLE & HTCJ).
pose proof (proj1 HJ) as HAR.
assert (Hfin : In (1, pos) (frames S3)) by (rewrite HFRS; left; reflexivity).
(* the flag's facts, and G / FL are layout-independent along the journal *)
assert (EFL : flag_addr ly3 1 pos = rp_FL cx pos)
by (unfold rp_FL, flag_addr; rewrite (proj1 HLY); reflexivity).
assert (EFAg : forall cid p', frame_addr ly3 cid p' = frame_addr (rc_lyc cx) cid p')
by (intros cid p'; unfold frame_addr; rewrite (proj1 HLY); reflexivity).
assert (EFA : frame_addr ly3 1 pos = rp_G cx pos) by (unfold rp_G; apply EFAg).
destruct (FFL ly3 S3 W3 mem3 md3 1 pos HAR Hfin)
as (HFLp & HFLo & (HFLapp & HFLimg) & (HFL4096 & HFLz2 & HFLceil)).
rewrite EFL in HFLp, HFLo, HFLimg, HFL4096, HFLceil.
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 mem3 md3 1 pos HAR Hfin) as (HG4096 & HGceil & HGapp).
rewrite EFA in HG4096, HGceil, HGapp.
change (fs_frame_bytes 1) with 128 in HG4096, HGceil, HGapp.
destruct (al_frames SEGS B LAWS ly3 S3 W3 mem3 md3 1 pos HAR Hfin) as (_ & _ & HFpres & _).
rewrite EFA in HFpres. change (fs_frame_bytes 1) with 128 in HFpres.
assert (HFLnF : ~ (rp_G cx pos <= rp_FL cx pos < rp_G cx pos + 128))
by (intros Hx; exact (proj2 (HFpres _ Hx) HFLo)).
(* the premises of rp_base this stretch spends *)
assert (HBlo : rc_sp0 cx - rc_STK cx <= rp_S cx - TREPLY_STK)
by (clear - HB; unfold rp_base in HB; tauto).
assert (HBhi : rp_S cx <= rc_sp0 cx) by (clear - HB; unfold rp_base in HB; tauto).
(* absolute bounds on the entry sp, from the journal's stack window (as RP_R12's rp_R12 does) *)
assert (HSTK : astk_ok (rc_STK cx) (rc_ly cx) (rc_sp0 cx)).
{ pose proof HJ as HJc.
destruct HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hs & _ & _). exact Hs. }
destruct HSTK as (Jsp16 & JSTK0 & Jclo & Jlosp & Jsphi & Jhi47 & Jbot & Jtop1 & Jtop2).
pose proof alloc_ceiling_val as HAC.
pose proof rp_stk as (Tstk & Pstk).
assert (HSlo : 0x7fff7f800000 <= rp_S cx) by lia.
assert (HShi : rp_S cx <= 2 ^ 47) by lia.
assert (HBout : rp_argsb cx = true -> forall a, treply_out (rc_pa cx) (rc_pp cx) (rc_pn cx) a ->
exists cid p', In (cid, p') (frames (rc_Sc cx)) /\ in_zr a (frame_rng (rc_lyc cx) (cid, p')))
by (clear - HB; unfold rp_base in HB; intros Hra; tauto).
(* the env and the entry symbolic state *)
set (E := rp_R11_E cx pos regs3).
assert (HEI : img_env VAL A_LIM E) by (unfold E, rp_R11_E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs3 (rp_R11_extra cx pos)) n)
by (intros n Hn; unfold E, rp_R11_E; apply Eimg_low; exact Hn).
assert (E18 : ew E 18%nat = Z_to_bv 64 (rp_G cx pos)).
{ unfold E, rp_R11_E. rewrite (YC1g.ew_Eimg_Ereg_nat regs3 _ 18 18%bv eq_refl).
exact (proj1 HFRG). }
assert (E33 : ew E 33%nat = Z_to_bv 64 (rp_FL cx pos)).
{ rewrite EL by (unfold A_TEXT; lia). replace 33%nat with (32 + 1)%nat by lia.
rewrite ew_Ereg_extra. reflexivity. }
assert (ER : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs3 r)
by (intros n r Hn; unfold E, rp_R11_E; apply YC1g.ew_Eimg_Ereg_nat; exact Hn).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v)
by (intros n v Hn Hv; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv).
unfold cfg_at.
replace (w64 (rp_pc 0x2e8)) with (Z_to_bv 64 (BASE + (AF_reac_ctrl_identity_reply + 0x2e8)))
by (unfold w64, rp_pc, A_reac_ctrl_identity_replyP; f_equal; lia).
assert (HS : st_ok_pi SEGS VAL E rp_R11_ss
(restrict (w_H W3) (mkst regs3 (Z_to_bv 64 (BASE + (AF_reac_ctrl_identity_reply + 0x2e8))) mem3 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold rp_R11_ss.
apply (pa_entry_st_ok_full (L := ctrl_listing) (PI := CtrlImg.PI_ctrl)).
- unfold E, rp_R11_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold rp_R11_rs. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
+ rewrite (VB 33%nat (rp_FL cx pos) E33) by lia.
split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
intros o Ho. apply (apresent_writable SEGS).
replace (rp_FL cx pos + o) with (rp_FL cx pos) by lia. exact HFLp.
+ rewrite (VB 18%nat (rp_G cx pos) E18) by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val SEGS E _ (rp_G cx pos) 120 8 (SOff 33 0) (rp_FL cx pos)).
* cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
* change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
* lia.
* cbn [N.to_nat]. exact (val_mem_of_rdword SEGS (w_H W3) mem3 _ _ (proj2 (proj2 (proj2 HFW)))).
- unfold rp_R11_rs. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
cbn [YP09.r_base YP09.r_lo YP09.r_hi].
rewrite (VB 33%nat (rp_FL cx pos) E33) by lia. rewrite (VB 18%nat (rp_G cx pos) E18) by lia.
split; [split; [lia | exact I] | split; [exact I | exact I]].
- split; [exact I | split; [exact I | exact I]]. }
(* E must stay opaque from here: prreg's `cbn [... Eimg ...]` would otherwise unfold the image env. *)
clearbody E.
(* the inline flag release: three instructions (ld / sb / j), stopping at +0x334 *)
let r := eval vm_compute in (sym_runN_pi pl_tpi 3 rp_R11_ss) in
lazymatch r with
| (?ssx, ?stx) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_runN_pi pl_tpi 3 rp_R11_ss = (ssx, stx)) by (vm_compute; reflexivity);
eapply (aj_flag_store_pi (L := ctrl_listing) (PI := CtrlImg.PI_ctrl) B LAWS ML ASF FFL W3 3 E rp_R11_ss ssx stx _
(rc_STK cx) (rc_sp0 cx) (rc_FP cx) (rc_ly cx) (rc_S cx) (rc_W0 cx) (rc_mem0 cx) (rc_md0 cx)
(rc_own cx) ly3 S3 md3 (rc_k cx) 1 pos _ HEI HS Hrun I HJ)
end.
- lia.
- (* every written byte is the flag byte *)
intros a (r & Hin & Hr). cbn [In] in Hin.
destruct Hin as [<- | [<- | []]];
cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr.
+ rewrite (VB 33%nat (rp_FL cx pos) E33) in Hr by lia. right. rewrite EFL. lia.
+ rewrite (VB 18%nat (rp_G cx pos) E18) in Hr by lia. exfalso. lia.
- (* the flag byte reads 0 after the store *)
intros msr HSr. rewrite EFL.
pose proof (YC1g.st_ok_pi_region_nth E _ msr 0 _ HSr eq_refl) as HR.
destruct HR as (_ & _ & _ & HRc).
pose proof (proj1 (Forall_forall _ _) HRc _ (or_introl eq_refl)) as HCk.
destruct (HCk 0 ltac:(cbn [YP09.c_len YP09.cv_len YP09.c_val]; lia)) as (bb & Hb1 & Hb2).
cbn [YP09.r_base YP09.r_chunks YP09.c_off YP09.c_val cbyte byte_of_word] in Hb1, Hb2.
rewrite (VB 33%nat (rp_FL cx pos) E33) in Hb2 by lia.
rewrite !Z.add_0_r in Hb2. rewrite Hb2. rewrite <- Hb1. reflexivity.
- (* C14 *)
intros ms4 mat HS4 HJ4 HF HF' HG. cbn [ms_mem mkst] in HF, HF', HG.
(* memory is unchanged away from the flag byte *)
assert (EQ : forall a, 0 <= a < 2 ^ 64 -> a <> rp_FL cx pos ->
aview SEGS (w_H W3) (ms_mem ms4) a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha Hne. apply aview_eq_of. apply HF'.
intros (r & Hin & Hr). rewrite Z_to_bv_unsigned in Hr. unfold bv_wrap, bv_modulus in Hr.
change (2 ^ Z.of_N 64) with (2 ^ 64) in Hr. rewrite (Z.mod_small a) in Hr by lia.
cbn [In] in Hin. destruct Hin as [<- | [<- | []]];
cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr.
- rewrite (VB 33%nat (rp_FL cx pos) E33) in Hr by lia. apply Hne. lia.
- rewrite (VB 18%nat (rp_G cx pos) E18) in Hr by lia. lia. }
(* the three ways an address of the carried facts differs from the flag byte *)
assert (STKNE : forall a, rp_S cx - TREPLY_STK <= a < rp_S cx -> a <> rp_FL cx pos).
{ intros a Ha Hx.
assert (Hw : awr_byte (rc_STK cx) (rc_sp0 cx) (rc_FP cx) (ablocks B (rc_ly cx) (rc_S cx))
(ablocks B ly3 S3) ly3 (rp_own1 cx pos) a) by (left; lia).
destruct (awr_byte_cases SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw) as (Hno & _).
apply Hno. rewrite Hx. exact HFLo. }
assert (BLKNE : forall b m i, In (b, m) (ablocks B ly3 S3) -> 0 <= i < req_size m ->
0 <= b + i < 2 ^ 64 /\ b + i <> rp_FL cx pos).
{ intros b m i Hin Hi.
destruct (al_blocks SEGS B LAWS ly3 S3 W3 mem3 md3 b m HAR Hin) as (_ & Hb4 & Hbc & _ & Hbp & _).
split; [lia|]. intros Hx. apply (proj2 (Hbp (b + i) ltac:(lia))). rewrite Hx. exact HFLo. }
assert (FRMNE : forall cid p' a, In (cid, p') (frames S3) ->
(in_zr a (frame_rng ly3 (cid, p')) \/
in_zr a (shadow_addr (frame_addr ly3 cid p'), fs_frame_bytes cid / 8)) ->
0 <= a < 2 ^ 64 /\ a <> rp_FL cx pos).
{ intros cid p' a Hin Hz.
destruct (al_frames SEGS B LAWS ly3 S3 W3 mem3 md3 cid p' HAR Hin) as (_ & _ & Hfp & Hsp).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 mem3 md3 cid p' HAR Hin) as (Hb1 & Hb2 & _).
pose proof (fs_frame_bytes_nonneg cid) as Hnn.
assert (Hd : fs_frame_bytes cid / 8 <= fs_frame_bytes cid) by (apply Z.div_le_upper_bound; lia).
unfold in_zr, frame_rng in Hz. cbn [fst snd] in Hz.
destruct Hz as [Hz | Hz].
- split; [lia|]. intros Hx. apply (proj2 (Hfp a ltac:(lia))). rewrite Hx. exact HFLo.
- pose proof (shadow_addr_bounds (frame_addr ly3 cid p') ltac:(lia)) as Hsb.
unfold kLowMemEnd, kHighShadowEnd in Hsb.
specialize (Hsp (a - shadow_addr (frame_addr ly3 cid p')) ltac:(lia)).
replace (shadow_addr (frame_addr ly3 cid p') + (a - shadow_addr (frame_addr ly3 cid p')))
with a in Hsp by lia.
split; [lia|]. intros Hx. apply (proj2 Hsp). rewrite Hx. exact HFLo. }
assert (OUTNE : rp_argsb cx = true -> forall a, treply_out (rc_pa cx) (rc_pp cx) (rc_pn cx) a ->
0 <= a < 2 ^ 64 /\ a <> rp_FL cx pos).
{ intros Hra a Ha. destruct (HBout Hra a Ha) as (cid & p' & Hin & Hz).
assert (Hin3 : In (cid, p') (frames S3)) by (rewrite HFRS; right; exact Hin).
apply (FRMNE cid p' a Hin3). left.
unfold in_zr, frame_rng in Hz |- *. cbn [fst snd] in Hz |- *. rewrite (EFAg cid p'). exact Hz. }
(* the registers the three instructions leave alone *)
prreg HS4 (2%bv : bv 5) R2. rewrite (ER 2%nat 2%bv eq_refl) in R2.
prreg HS4 (3%bv : bv 5) R3. rewrite (ER 3%nat 3%bv eq_refl) in R3.
prreg HS4 (4%bv : bv 5) R4. rewrite (ER 4%nat 4%bv eq_refl) in R4.
prreg HS4 (8%bv : bv 5) R8. rewrite (ER 8%nat 8%bv eq_refl) in R8.
prreg HS4 (9%bv : bv 5) R9. rewrite (ER 9%nat 9%bv eq_refl) in R9.
prreg HS4 (10%bv : bv 5) R10. rewrite (ER 10%nat 10%bv eq_refl) in R10.
prreg HS4 (19%bv : bv 5) R19. rewrite (ER 19%nat 19%bv eq_refl) in R19.
prreg HS4 (20%bv : bv 5) R20. rewrite (ER 20%nat 20%bv eq_refl) in R20.
prreg HS4 (21%bv : bv 5) R21. rewrite (ER 21%nat 21%bv eq_refl) in R21.
prreg HS4 (22%bv : bv 5) R22. rewrite (ER 22%nat 22%bv eq_refl) in R22.
prreg HS4 (23%bv : bv 5) R23. rewrite (ER 23%nat 23%bv eq_refl) in R23.
prreg HS4 (27%bv : bv 5) R27. rewrite (ER 27%nat 27%bv eq_refl) in R27.
(* the machine state at +0x334 *)
pose proof (st_ok_pi_restrict_mkst (w_H W3) E _ ms4 HS4 ltac:(vm_compute; reflexivity)) as HPC.
lazymatch type of HS4 with
| st_ok_pi _ _ _ ?ssx _ =>
assert (EPC : Z_to_bv 64 (BASE + ss_pc ssx) = w64 (rp_pc 0x334))
by (unfold w64, rp_pc, A_reac_ctrl_identity_replyP; f_equal;
cbn [ss_pc]; unfold AF_reac_ctrl_identity_reply; lia)
end.
rewrite EPC in HPC. rewrite HPC at 1.
apply (F14 cx (ms_regs ms4) ly3 (stack_free_state 1 pos S3) W3 (ms_mem ms4)
(with_vm_backing (m_vm_lazy md3) mat md3) HB).
(* rp_C14 *)
unfold rp_C14. split; [exact HJ4|].
split; [exact HLY|].
assert (EQfr : frames (stack_free_state 1 pos S3) = frames (rc_Sc cx)).
{ change (frames (stack_free_state 1 pos S3)) with (del_pos (frames S3) 1 pos).
rewrite HFRS. cbn [del_pos]. rewrite !Z.eqb_refl. reflexivity. }
split; [exact EQfr|].
assert (EQabl : ablocks B ly3 (stack_free_state 1 pos S3) = ablocks B (rc_lyc cx) (rc_Sc cx)).
{ unfold ablocks. rewrite blocks_stack_free_state. exact HABL. }
split; [rewrite EQabl; apply Permutation_refl|].
split.
{ unfold rp_regs_ok in HREGS |- *. destruct HREGS as (Q2 & Q3 & Q4 & Q8 & Q9 & Q19 & Q20 & Q21 & Q22 & Q23 & Q27).
rewrite R2, R3, R4, R8, R9, R19, R20, R21, R22, R23, R27.
repeat split; assumption. }
split.
{ (* rp_kept *)
split; [exact HWLE|].
destruct HTCJ as (K1 & K2 & K3 & K4 & K5 & K6). unfold tcj_kept. repeat apply conj.
- intros a Ha1 Ha2 Ha3.
transitivity (aview SEGS (w_H W3) mem3 a);
[apply EQ; [lia | lia] | exact (K1 a Ha1 Ha2 Ha3)].
- intros b m i Hin Hi He.
assert (Hin3 : In (b, m) (ablocks B ly3 S3)) by (rewrite HABL; exact Hin).
destruct (BLKNE b m i Hin3 Hi) as (Hr1 & Hr2).
transitivity (aview SEGS (w_H W3) mem3 (b + i));
[apply EQ; [exact Hr1 | exact Hr2] | exact (K2 b m i Hin Hi He)].
- intros a Hi Hs He.
assert (Hne : a <> rp_FL cx pos) by (intros Hx; apply HFLimg; rewrite <- Hx; exact Hi).
pose proof (SEGLOW a Hi) as Hlo. unfold kLowMemEnd in Hlo.
transitivity (aview SEGS (w_H W3) mem3 a);
[apply EQ; [lia | exact Hne] | exact (K3 a Hi Hs He)].
- intros cid p' a Hin Hz He.
assert (Hin3 : In (cid, p') (frames S3)) by (rewrite HFRS; right; exact Hin).
assert (Hz3 : in_zr a (frame_rng ly3 (cid, p')) \/
in_zr a (shadow_addr (frame_addr ly3 cid p'), fs_frame_bytes cid / 8)).
{ unfold in_zr, frame_rng in Hz |- *. cbn [fst snd] in Hz |- *. rewrite (EFAg cid p'). exact Hz. }
destruct (FRMNE cid p' a Hin3 Hz3) as (Hr1 & Hr2).
transitivity (aview SEGS (w_H W3) mem3 a);
[apply EQ; [exact Hr1 | exact Hr2] | exact (K4 cid p' a Hin Hz He)].
- intros a H1 H2 H3. eapply apresent_grows; [exact HG | exact (K5 a H1 H2 H3)].
- intros a Ha. eapply apresent_grows; [exact HG | exact (K6 a Ha)]. }
split.
{ (* rp_saved *)
unfold rp_saved in HSAVED |- *. rewrite Forall_forall in HSAVED |- *. intros p Hp.
assert (Hb : 8 <= fst p <= 104).
{ clear - Hp. unfold rp_saves in Hp. cbn [In] in Hp.
repeat (destruct Hp as [<- | Hp]; [cbn [fst]; lia|]). destruct Hp. }
eapply (val_mem_kept SEGS (w_H W3) (w_H W3) mem3 (ms_mem ms4)); [|exact (HSAVED p Hp)].
intros k Hk. apply EQ; [lia | apply STKNE; lia]. }
split; [rewrite R10; exact HA0|].
(* rp_cells *)
intros Hok.
assert (HRA : rp_argsb cx = true).
{ unfold rp_okb, reply_ok in Hok. unfold rp_argsb.
exact (proj1 (andb_prop _ _ Hok)). }
destruct (HCELL Hok) as (Ca & Cp & Cn). split; [|split].
+ intros j Hj. destruct (Ca j Hj) as (Cv & Cr). split; [|exact Cr].
cbn [length map reply_addr] in Hj.
eapply (val_mem_kept SEGS (w_H W3) (w_H W3) mem3 (ms_mem ms4)); [|exact Cv].
intros k Hk. apply EQ.
* exact (proj1 (OUTNE HRA (rc_pa cx + Z.of_nat j + k) ltac:(left; lia))).
* exact (proj2 (OUTNE HRA (rc_pa cx + Z.of_nat j + k) ltac:(left; lia))).
+ eapply (val_mem_kept SEGS (w_H W3) (w_H W3) mem3 (ms_mem ms4)); [|exact Cp].
intros k Hk. apply EQ.
* exact (proj1 (OUTNE HRA (rc_pp cx + k) ltac:(right; left; lia))).
* exact (proj2 (OUTNE HRA (rc_pp cx + k) ltac:(right; left; lia))).
+ eapply (val_mem_kept SEGS (w_H W3) (w_H W3) mem3 (ms_mem ms4)); [|exact Cn].
intros k Hk. apply EQ.
* exact (proj1 (OUTNE HRA (rc_pn cx + k) ltac:(right; right; lia))).
* exact (proj2 (OUTNE HRA (rc_pn cx + k) ltac:(right; right; lia))).
Qed.

(* ---- R12 local helpers (named rp_R12_*, local to this stretch; no CtrlACjr kit is used) ---------- *)
Definition rp_R12_SB : Z := 0x7fff8000.
Definition rp_R12_Bx : sv := SLit rp_R12_SB.
Definition rp_R12_Bspan : Z * Z := (rp_R12_SB, rp_R12_SB + 2 ^ 44 - 1).
(* the 13 saved words of [S-104, S), read back by 0x842c4..0x842f4; atoms 32..44 name their values,
   in the order of rp_saves. *)
Definition rp_R12_region : YP09.region :=
YP09.mkRegion (Some 8%nat) (-104) 0 0 0
[YP09.mkChunk (-8) (CVal 8 (SOff 32 0)); YP09.mkChunk (-16) (CVal 8 (SOff 33 0));
YP09.mkChunk (-24) (CVal 8 (SOff 34 0)); YP09.mkChunk (-32) (CVal 8 (SOff 35 0));
YP09.mkChunk (-40) (CVal 8 (SOff 36 0)); YP09.mkChunk (-48) (CVal 8 (SOff 37 0));
YP09.mkChunk (-56) (CVal 8 (SOff 38 0)); YP09.mkChunk (-64) (CVal 8 (SOff 39 0));
YP09.mkChunk (-72) (CVal 8 (SOff 40 0)); YP09.mkChunk (-80) (CVal 8 (SOff 41 0));
YP09.mkChunk (-88) (CVal 8 (SOff 42 0)); YP09.mkChunk (-96) (CVal 8 (SOff 43 0));
YP09.mkChunk (-104) (CVal 8 (SOff 44 0))].
Definition rp_R12_facts : facts := mkFacts [(8%nat, mkAF 0x7fff7f800000 (2 ^ 47) 4)] [] [].
Definition rp_R12_ss : sstate :=
mkSS (AF_reac_ctrl_identity_reply + 0x334) sr_atoms [rp_R12_region] None rp_R12_facts.
Definition rp_R12_extra (cx : rcx) : list word :=
[getr (rc_regs cx) (Z_to_bv 5 1); getr (rc_regs cx) (Z_to_bv 5 8); getr (rc_regs cx) (Z_to_bv 5 9);
getr (rc_regs cx) (Z_to_bv 5 18); getr (rc_regs cx) (Z_to_bv 5 19); getr (rc_regs cx) (Z_to_bv 5 20);
getr (rc_regs cx) (Z_to_bv 5 21); getr (rc_regs cx) (Z_to_bv 5 22); getr (rc_regs cx) (Z_to_bv 5 23);
getr (rc_regs cx) (Z_to_bv 5 24); getr (rc_regs cx) (Z_to_bv 5 25); getr (rc_regs cx) (Z_to_bv 5 26);
getr (rc_regs cx) (Z_to_bv 5 27)].
Definition rp_R12_E (cx : rcx) (regs3 : bvmap 5 word) : env := Eimg (Ereg regs3 (rp_R12_extra cx)).
Lemma rp_R12_bv5 : forall (r : bv 5) (z : Z), bv_unsigned r = z -> Z_to_bv 5 z = r.
Proof. intros r z <-. apply Z_to_bv_bv_unsigned. Qed.
Ltac rp12_chunk cx EXa HSV jj aa oo pp :=
apply (chunk_ok_val _ (rp_R12_E cx _) _ (rp_S cx) oo 8 (SOff aa 0)
(bv_unsigned (nth jj (rp_R12_extra cx) (Z_to_bv 64 0))));
[ cbn [sv_denot]; replace aa with (32 + jj)%nat by lia; rewrite (EXa jj ltac:(lia));
rewrite Z.add_0_r; reflexivity
| pose proof (u64_range (nth jj (rp_R12_extra cx) (Z_to_bv 64 0))); zside
| zside
| change (N.to_nat 8) with 8%nat; replace (rp_S cx + oo) with (rp_S cx - pp) by lia;
pose proof (HSV jj ltac:(lia)) as HVV; unfold rp_saves, rp_R12_extra in HVV |- *;
cbn [nth fst snd] in HVV |- *; exact HVV ].
(* the symbolic state at the epilogue head +0x334: the 13 saved words are the only memory it reads. *)
Lemma rp_R12_entry : forall cx (regs3 : bvmap 5 word) (W3 : world SEGS) mem3,
0x7fff7f800000 <= rp_S cx -> rp_S cx <= 2 ^ 47 -> rp_S cx mod 16 = 0 ->
getr regs3 8 = w64 (rp_S cx) -> rp_saved cx W3 mem3 ->
st_ok_pi SEGS VAL (rp_R12_E cx regs3) rp_R12_ss
(restrict (w_H W3) (mkst regs3 (Z_to_bv 64 (BASE + (AF_reac_ctrl_identity_reply + 0x334))) mem3
(seg_rom SEGS)))
/\ sh_ok SEGS rp_R12_Bx [] (rp_R12_E cx regs3) (mrestrict (w_H W3) mem3).
Proof.
intros cx regs3 W3 mem3 HSlo HShi HS16 R8 HSAVED.
split; [|constructor].
rewrite restrict_mkst_fx.
assert (E8 : ew (rp_R12_E cx regs3) 8 = w64 (rp_S cx)).
{ unfold rp_R12_E. rewrite Eimg_low by (unfold A_TEXT; lia).
rewrite (ew_Ereg_nat regs3 _ 8 8%bv eq_refl). exact R8. }
assert (HB : base_val (rp_R12_E cx regs3) (Some 8%nat) = rp_S cx).
{ cbn [base_val]. rewrite E8. unfold w64. apply unsigned_lit_small. lia. }
assert (EXa : forall j, (j < 13)%nat ->
ew (rp_R12_E cx regs3) (32 + j)%nat = nth j (rp_R12_extra cx) (Z_to_bv 64 0)).
{ intros j Hj. unfold rp_R12_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (HSV : forall j, (j < 13)%nat ->
val_mem SEGS (mrestrict (w_H W3) mem3) (rp_S cx - fst (nth j rp_saves (0, 0))) 8
(bv_unsigned (getr (rc_regs cx) (Z_to_bv 5 (snd (nth j rp_saves (0, 0))))))).
{ intros j Hj. unfold rp_saved in HSAVED. rewrite Forall_forall in HSAVED.
apply (HSAVED (nth j rp_saves (0, 0))). apply nth_In. unfold rp_saves. cbn [length]. lia. }
unfold rp_R12_ss. apply (pa_entry_st_ok_full (PI := CtrlImg.PI_ctrl)).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor].
unfold rp_R12_region, region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
rewrite HB.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
repeat apply Forall_cons; try apply Forall_nil.
+ rp12_chunk cx EXa HSV 0%nat 32%nat (-8) 8.
+ rp12_chunk cx EXa HSV 1%nat 33%nat (-16) 16.
+ rp12_chunk cx EXa HSV 2%nat 34%nat (-24) 24.
+ rp12_chunk cx EXa HSV 3%nat 35%nat (-32) 32.
+ rp12_chunk cx EXa HSV 4%nat 36%nat (-40) 40.
+ rp12_chunk cx EXa HSV 5%nat 37%nat (-48) 48.
+ rp12_chunk cx EXa HSV 6%nat 38%nat (-56) 56.
+ rp12_chunk cx EXa HSV 7%nat 39%nat (-64) 64.
+ rp12_chunk cx EXa HSV 8%nat 40%nat (-72) 72.
+ rp12_chunk cx EXa HSV 9%nat 41%nat (-80) 80.
+ rp12_chunk cx EXa HSV 10%nat 42%nat (-88) 88.
+ rp12_chunk cx EXa HSV 11%nat 43%nat (-96) 96.
+ rp12_chunk cx EXa HSV 12%nat 44%nat (-104) 104.
- cbn [pairwise_disjoint all_disjoint]. split; exact I.
- split; [|split; exact I].
cbn [rp_R12_facts f_atoms atoms_ok].
split; [|exact I].
unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E8. unfold w64.
rewrite unsigned_lit_small by lia. change (2 ^ 4) with 16. repeat split; lia.
Qed.

(* R12  C14 -> the post, 0x842c0..0x842fc (+0x334..+0x370). `addi sp,s0,-128`, the 13 loads from [S-104, S)
   (rp_saved gives each value back, so `aregs_preserved` holds), `addi sp,sp,128` and `ret` by `paj_ret_at`.
   The post is built from the journal (`ajournal_materialize`, `ajournal_mono_k` with EV_REPLY = 0), from
   rp_kept (the `tcj_kept` conjunct), from `frames S3 = frames Sc` and the `Permutation` of C14, from
   `getr regs3 10 = w64 (rp_ret cx)` and from rp_cells; `wle W W2` is the world growth SRr_bind threads through
   the walk (YA0n.v:40).
   Donors: B `rp_ret` :2650, `rp_main` :4089; A18 `seg_ret` :1059, `rep_run` :3432. Difficulty: medium. *)
Lemma rp_R12 : rp_from_C14.
Proof.
unfold rp_from_C14. intros cx regs3 ly3 S3 W3 mem3 md3 HBASE HC14.
pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
destruct HBASE as (HJ0 & HRO0 & Hra & Hra4 & Hgp0 & Htp0 & Ha10 & Ha11 & Ha12 & Ha13 & Ha14 &
Hfrr & Hlenr & Hpar & Hppr & Hpnr & HS16 & HSwin & HSsp0 & Hcnt & Hglen & Hmsg0 & Hout0).
destruct HC14 as (HJ & HLY & HFRM & HPERM & HREGS & HKEPT & HSAVED & HA0 & HCELLS).
destruct HREGS as (R2' & R3' & R4' & R8' & R9' & R19' & R20' & R21' & R22' & R23' & R27').
(* the entry sp lies in the stack window the journal pins. *)
assert (HSTK : astk_ok (rc_STK cx) (rc_ly cx) (rc_sp0 cx)).
{ pose proof HJ as HJc.
destruct HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hs & _ & _). exact Hs. }
destruct HSTK as (Jsp16 & JSTK0 & Jclo & Jlosp & Jsphi & Jhi47 & Jbot & Jtop1 & Jtop2).
pose proof alloc_ceiling_val as HAC.
pose proof rp_stk as (Tstk & Pstk).
assert (HSlo : 0x7fff7f800000 <= rp_S cx) by lia.
assert (HShi : rp_S cx <= 2 ^ 47) by lia.
destruct (rp_R12_entry cx regs3 W3 mem3 HSlo HShi HS16 R8' HSAVED) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (rp_R12_E cx regs3))
by (unfold rp_R12_E; apply Eimg_env).
(* the env values this stretch reads back *)
assert (E3 : ew (rp_R12_E cx regs3) 3 = getr regs3 3)
by (unfold rp_R12_E; rewrite Eimg_low by (unfold A_TEXT; lia);
exact (ew_Ereg_nat regs3 _ 3 3%bv eq_refl)).
assert (E4 : ew (rp_R12_E cx regs3) 4 = getr regs3 4)
by (unfold rp_R12_E; rewrite Eimg_low by (unfold A_TEXT; lia);
exact (ew_Ereg_nat regs3 _ 4 4%bv eq_refl)).
assert (E8 : ew (rp_R12_E cx regs3) 8 = getr regs3 8)
by (unfold rp_R12_E; rewrite Eimg_low by (unfold A_TEXT; lia);
exact (ew_Ereg_nat regs3 _ 8 8%bv eq_refl)).
assert (E10 : ew (rp_R12_E cx regs3) 10 = getr regs3 10)
by (unfold rp_R12_E; rewrite Eimg_low by (unfold A_TEXT; lia);
exact (ew_Ereg_nat regs3 _ 10 10%bv eq_refl)).
assert (EXa : forall j, (j < 13)%nat ->
ew (rp_R12_E cx regs3) (32 + j)%nat = nth j (rp_R12_extra cx) (Z_to_bv 64 0))
by (intros j Hj; unfold rp_R12_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (E32 : ew (rp_R12_E cx regs3) 32 = getr (rc_regs cx) (Z_to_bv 5 1))
by (replace 32%nat with (32 + 0)%nat by lia; rewrite (EXa 0%nat ltac:(lia));
unfold rp_R12_extra; cbn [nth]; reflexivity).
assert (E33 : ew (rp_R12_E cx regs3) 33 = getr (rc_regs cx) (Z_to_bv 5 8))
by (replace 33%nat with (32 + 1)%nat by lia; rewrite (EXa 1%nat ltac:(lia));
unfold rp_R12_extra; cbn [nth]; reflexivity).
assert (E34 : ew (rp_R12_E cx regs3) 34 = getr (rc_regs cx) (Z_to_bv 5 9))
by (replace 34%nat with (32 + 2)%nat by lia; rewrite (EXa 2%nat ltac:(lia));
unfold rp_R12_extra; cbn [nth]; reflexivity).
assert (E35 : ew (rp_R12_E cx regs3) 35 = getr (rc_regs cx) (Z_to_bv 5 18))
by (replace 35%nat with (32 + 3)%nat by lia; rewrite (EXa 3%nat ltac:(lia));
unfold rp_R12_extra; cbn [nth]; reflexivity).
assert (E36 : ew (rp_R12_E cx regs3) 36 = getr (rc_regs cx) (Z_to_bv 5 19))
by (replace 36%nat with (32 + 4)%nat by lia; rewrite (EXa 4%nat ltac:(lia));
unfold rp_R12_extra; cbn [nth]; reflexivity).
assert (E37 : ew (rp_R12_E cx regs3) 37 = getr (rc_regs cx) (Z_to_bv 5 20))
by (replace 37%nat with (32 + 5)%nat by lia; rewrite (EXa 5%nat ltac:(lia));
unfold rp_R12_extra; cbn [nth]; reflexivity).
assert (E38 : ew (rp_R12_E cx regs3) 38 = getr (rc_regs cx) (Z_to_bv 5 21))
by (replace 38%nat with (32 + 6)%nat by lia; rewrite (EXa 6%nat ltac:(lia));
unfold rp_R12_extra; cbn [nth]; reflexivity).
assert (E39 : ew (rp_R12_E cx regs3) 39 = getr (rc_regs cx) (Z_to_bv 5 22))
by (replace 39%nat with (32 + 7)%nat by lia; rewrite (EXa 7%nat ltac:(lia));
unfold rp_R12_extra; cbn [nth]; reflexivity).
assert (E40 : ew (rp_R12_E cx regs3) 40 = getr (rc_regs cx) (Z_to_bv 5 23))
by (replace 40%nat with (32 + 8)%nat by lia; rewrite (EXa 8%nat ltac:(lia));
unfold rp_R12_extra; cbn [nth]; reflexivity).
assert (E41 : ew (rp_R12_E cx regs3) 41 = getr (rc_regs cx) (Z_to_bv 5 24))
by (replace 41%nat with (32 + 9)%nat by lia; rewrite (EXa 9%nat ltac:(lia));
unfold rp_R12_extra; cbn [nth]; reflexivity).
assert (E42 : ew (rp_R12_E cx regs3) 42 = getr (rc_regs cx) (Z_to_bv 5 25))
by (replace 42%nat with (32 + 10)%nat by lia; rewrite (EXa 10%nat ltac:(lia));
unfold rp_R12_extra; cbn [nth]; reflexivity).
assert (E43 : ew (rp_R12_E cx regs3) 43 = getr (rc_regs cx) (Z_to_bv 5 26))
by (replace 43%nat with (32 + 11)%nat by lia; rewrite (EXa 11%nat ltac:(lia));
unfold rp_R12_extra; cbn [nth]; reflexivity).
assert (E44 : ew (rp_R12_E cx regs3) 44 = getr (rc_regs cx) (Z_to_bv 5 27))
by (replace 44%nat with (32 + 12)%nat by lia; rewrite (EXa 12%nat ltac:(lia));
unfold rp_R12_extra; cbn [nth]; reflexivity).
clear EXa.
(* the run: 0x842c0 .. 0x842fc, 16 instructions, ending at the `ret`. *)
pose proof (paj_run B LAWS) as RUN.
pose proof (paj_ret_at (PL := PL_ctrl) (PI := CtrlImg.PI_ctrl)) as RET.
unfold cfg_at, rp_pc, A_reac_ctrl_identity_replyP.
replace (w64 (BASE + AF_reac_ctrl_identity_reply + 0x334))
with (Z_to_bv 64 (BASE + (AF_reac_ctrl_identity_reply + 0x334))) by (unfold w64; f_equal; lia).
paj_run_tok RUN HS HJ SHOK rp_R12_Bspan;
[ intros a Ha; exfalso; destruct Ha as (r & Hin & Hr);
cbv [rp_R12_ss ss_mem] in Hin; cbn [In] in Hin;
destruct Hin as [Heq | []]; subst r;
cbv [rp_R12_region YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; lia |].
(* no byte is written, so the memory is the entry memory *)
lazymatch goal with
| HFx : frame_of _ _ _ (ms_mem ?msn) |- _ =>
assert (HMEM : ms_mem msn = mem3)
by (apply FunctionalExtensionality.functional_extensionality; intros x; apply HFx;
intros (r & Hin & Hr); cbv [rp_R12_ss ss_mem] in Hin; cbn [In] in Hin;
destruct Hin as [Heq | []]; subst r;
cbv [rp_R12_region YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; lia)
end.
prreg HS (1%bv : bv 5) RA1.
prreg HS (10%bv : bv 5) RA10.
prreg HS (Z_to_bv 5 2) RP2. prreg HS (Z_to_bv 5 3) RP3. prreg HS (Z_to_bv 5 4) RP4.
prreg HS (Z_to_bv 5 8) RP8. prreg HS (Z_to_bv 5 9) RP9.
prreg HS (Z_to_bv 5 18) RP18. prreg HS (Z_to_bv 5 19) RP19. prreg HS (Z_to_bv 5 20) RP20.
prreg HS (Z_to_bv 5 21) RP21. prreg HS (Z_to_bv 5 22) RP22. prreg HS (Z_to_bv 5 23) RP23.
prreg HS (Z_to_bv 5 24) RP24. prreg HS (Z_to_bv 5 25) RP25. prreg HS (Z_to_bv 5 26) RP26.
prreg HS (Z_to_bv 5 27) RP27.
eapply (RET W3 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros matR.
unfold rp_post, treac_ctrl_identity_reply_post.
split; [exact (proj1 HKEPT)|].
eexists ly3, S3, _, _, _.
split; [cbn [ms_regs]; rewrite RA1, E32,
(rp_R12_bv5 (1%bv : bv 5) 1 ltac:(vm_compute; reflexivity)), Hra; reflexivity|].
split.
{ replace (rc_k cx + EV_REPLY) with (rc_k cx) by (unfold EV_REPLY; lia).
cbn [ms_mem].
lazymatch goal with HJx : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJx end. }
split.
{ intros r Hr. unfold acallee_saved in Hr.
assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/
r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
cbn [ms_regs].
repeat (destruct Hc as [->|Hc]); try (subst r).
- rewrite RP2, E8, R8'. unfold rp_S, spZ, w64.
rewrite (rp_R12_bv5 (2%bv : bv 5) 2 ltac:(vm_compute; reflexivity)). apply Z_to_bv_bv_unsigned.
- rewrite RP3, E3, R3'.
rewrite (rp_R12_bv5 (3%bv : bv 5) 3 ltac:(vm_compute; reflexivity)). symmetry. exact Hgp0.
- rewrite RP4, E4, R4'.
rewrite (rp_R12_bv5 (4%bv : bv 5) 4 ltac:(vm_compute; reflexivity)). symmetry. exact Htp0.
- rewrite RP8. exact E33.
- rewrite RP9. exact E34.
- rewrite RP18. exact E35.
- rewrite RP19. exact E36.
- rewrite RP20. exact E37.
- rewrite RP21. exact E38.
- rewrite RP22. exact E39.
- rewrite RP23. exact E40.
- rewrite RP24. exact E41.
- rewrite RP25. exact E42.
- rewrite RP26. exact E43.
- rewrite RP27. exact E44. }
split; [exact HFRM|].
split; [exact HPERM|].
split; [cbn [ms_regs]; rewrite RA10, E10, HA0; unfold rp_ret; reflexivity|].
split; [cbn [ms_mem]; rewrite HMEM; exact (proj2 HKEPT)|].
cbn [ms_mem]. rewrite HMEM. exact HCELLS.
Qed.

(* ================================ the theorem ======================================================== *)
(* Proof outline (not written in this piece; it is the composition only, no new obligation):
     pose proof rp_R12                                   as F14.                  (* rp_from_C14 *)
     pose proof (rp_R11 F14)                             as F13.
     pose proof (rp_R10 F13)                             as F12.
     pose proof (rp_R9  F12)                             as F11.
     pose proof (rp_R8  F11)                             as F10.
     pose proof (rp_R7L F10 F11)                         as F9L.
     pose proof (rp_R7  F9L F10 F11)                     as F9.
     pose proof (rp_R6  F9 F11)                          as F8.
     pose proof (rp_R5b F8 F11)                          as F7.
     pose proof (rp_R5a F7 F11)                          as F6.
     pose proof (rp_E2  F6)                              as F5.
     pose proof (rp_R34 F5 F12)                          as F4.
     pose proof (rp_R2  F4)                              as F3.
     pose proof (rp_E1  F3)                              as F2.
     pose proof (rp_R1b F2)                              as F1.
     pose proof (rp_R1a F1)                              as F0.                   (* rp_from_C0 *)
   then `intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fr len pa pp pn g H1 .. H22`,
   pack them into `cx := mkRCX STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fr len pa pp pn g`,
   and apply `F0 cx regs lyc Sc W memc mdc` with `rp_base cx` (the premises, in order) and `rp_C0` (six
   `reflexivity`). `rp_post cx` is `treac_ctrl_identity_reply_post ...` by `reflexivity`. *)
Theorem pb_reac_ctrl_identity_reply : treac_ctrl_identity_reply_spec.
Proof.
pose proof rp_R12 as F14.
pose proof (rp_R11 F14) as F13.
pose proof (rp_R10 F13) as F12.
pose proof (rp_R9 F12) as F11.
pose proof (rp_R8 F11) as F10.
pose proof (rp_R7L F10 F11) as F9L.
pose proof (rp_R7 F9L F10 F11) as F9.
pose proof (rp_R6 F9 F11) as F8.
pose proof (rp_R5b F8 F11) as F7.
pose proof (rp_R5a F7 F11) as F6.
pose proof (rp_E2 F6) as F5.
pose proof (rp_R34 F5 F12) as F4.
pose proof (rp_R2 F4) as F3.
pose proof (rp_E1 F3) as F2.
pose proof (rp_R1b F2) as F1.
pose proof (rp_R1a F1) as F0.
unfold treac_ctrl_identity_reply_spec.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fr len pa pp pn g.
intros H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23.
assert (HB : rp_base (mkRCX STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fr len pa pp pn g)).
{ exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 (conj H10
    (conj H11 (conj H12 (conj H13 (conj H14 (conj H15 (conj H16 (conj H17 (conj H18 (conj H19 (conj H20
    (conj H21 (conj H22 H23)))))))))))))))))))))). }
assert (HC0 : rp_C0 (mkRCX STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fr len pa pp pn g)
  regs lyc Sc W memc mdc).
{ exact (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl eq_refl))))). }
pose proof (F0 _ _ _ _ _ _ _ HB HC0) as HR.
assert (EPC : rp_pc 0 = A_reac_ctrl_identity_replyP) by (unfold rp_pc; apply Z.add_0_r).
rewrite EPC in HR.
exact HR.
Qed.
End e.
End d.
End b.
