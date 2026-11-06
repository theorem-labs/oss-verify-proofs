(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* reac_box_catalogue_match (0x84498 = BASE + AF_reac_box_catalogue_match) of fuzz_ctrl's ASan build
   (image A, libreac v1.9.0): the cgif-form contract.

   STATEMENT ONLY. `Theorem pb_reac_box_catalogue_match` and its walk are in reac_box_catalogue_match_glue.v
   (statement / walk split for the callers, two Theorem Labs lanes via a Theorem Labs lane 08:2xZ). Rule 24:
   `proof-index reac_box_catalogue_match` gives 0 named, 0 by address and 0 related hits (a Theorem Labs lane,
   2026-10-28 21:05Z), second-agent check a Theorem Labs lane CONFIRM; At ossv/recipes c5e779efe8c (2026-10-31), no released proof of this function is reused.

   Contract form: the function writes only its own side-stack frame and returns a value in a0, so it takes cgif's
   `afn_pre` / `apost_base` form (lib/Reusable/APostBase.v:54, copied verbatim from cgif lib/YC20.v:91-96), not the
   caller-journal form that its two callees take.

   Segments: the statement is over the walk's segments `tfibsegs` (lib/A/AB1v.v:11), not `pa_segs PI`
   (two Theorem Labs lanes, 23:37Z; bridge lemma `tfibsegs_rsegs` in ProgBridge.v). The PA layer enters through
   the CONCRETE instance `PI_ctrl` (lib/A/Prog/CtrlImg.v:79, whose `pa_segs` IS `tfibsegs`), so `pa_segs PI_ctrl`
   reduces to `tfibsegs` and lib/A/Prog/CtrlCallerJ.v's `tcj_kept` / `twr_ok` / `tsrc_ok` apply at the two calls
   (a Theorem Labs lane, 23:49Z). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
(* The six modules that exist both in the core (lib/Reusable) and in ctrl's lib/A/Reusable (YI04 YI16 YK11 YK1b YM05
   YO09) are Required from the core's directory and named `lib.Reusable.X.n` (porter a Theorem Labs lane 04:24Z / 04:33Z). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK11 YK1b.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YK0h YK0i YK14 YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YI04 YI16.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YN3v YI09 YI08 YI00.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YE00 YE01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import AB1v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import
PaTable PaSym PaRun PaShadow PaJournal CtrlSyms CtrlList CtrlAddr CtrlPa CtrlPaLib CtrlImg CtrlFrame CtrlRo.
(* `apost_base` comes from the Reusable copy, never from a private one (brief, 2026-10-28); imported last so that
   it wins over the PA layer's copy of the same cgif text. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import APostBase.
(* ctrl's plain files: Required QUALIFIED only, never Imported (glue closure rule, porter 23:38Z; a Theorem Labs lane Q6). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcMatch.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require reac_box_catalogue_match_lib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* The FP state, the run ceiling and the sink head are the core's (lib.Reusable.YK11, lib.Reusable.YM05,
   lib.Reusable.YI16), the ones PI_ctrl, afn_pre and apost_base take. Written fully qualified: their short names also
   name lib/A/Reusable/ and lib/B/Reusable/ modules, and with the Requires above on a Theorem Labs lane's PA head they did not
   resolve to the core's (type-checks 02:33Z / 03:00Z: "?rc: Cannot infer this placeholder of type RunCeil" at the
   line of A_catalogue_matchP, then "?fx: Cannot infer the implicit parameter fx of apost_base" at the post). The
   meaning is the one intended. *)
Section b. Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.FPState}
  {rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil}.
Context {SK : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI16.sink_head}.
Section d.
(* The concrete image instance: no `Context {PI : PAImg ctrl_listing}` (two Theorem Labs lanes, 23:49Z). *)
#[local] Notation VAL := (@pa_val _ ctrl_listing PI_ctrl).
#[local] Notation SIGMA := (@pa_sigma _ ctrl_listing PI_ctrl).
#[local] Notation BASE := (@pa_val _ ctrl_listing PI_ctrl A_TEXT).

Definition A_catalogue_matchP : Z := BASE + AF_reac_box_catalogue_match.
(* BOX_CATALOGUE is object 17 of the listing (PAddHi at 0x846a4, CtrlList.v:3608; 0x9e800 in image A,
   CtrlAddr.v:87): 11 rows of 296 bytes = 0xcb8 bytes, [0x9e800, 0x9e800 + 0xcb8). *)
Definition A_CM_TBL : Z := VAL (A_OBJ 17).
Definition CM_ROWS : Z := 3256.
Definition CM_TBLZ : list Z := map (fun b : byte => bv_unsigned b) reac_box_catalogue_match_lib.CM_TBL.
(* The function's own frame: `84498: addi sp,sp,-128` then `844d4: andi sp,sp,-32`, so with S mod 16 = 0 the body
   runs at S - 144 <= CA <= S - 128 (the arithmetic of D A/ACez.v:85-88 for cgif's -128 frame). *)
Definition CM_FRAME : Z := 144.
(* CM_STK is ctrl's plain window K = 9136 = 336 + 8800 (reac_box_catalogue_match_c.v:14-19, CM_K): the frame on the
   real-stack arm (A - 192 >= S - 336) plus reac_ctrl_parse's plain window 8800. The lifted stretches
   (reac_box_catalogue_match_F<n>.v, the source's Section Match) carry that window as their stack premises
   (stk / addressable / fp over [S - 9136, S); S1's footprint range), so the statement gives the walk all of it
   (a Theorem Labs lane, 2026-10-29: decision B1). It covers the cgif bound of the side-stack arm, CM_FRAME + max over the
   calls made at sp = CA:
     - reac_ctrl_parse at `84684: jal 83578`      : REAC_CTRL_PARSE_STK      = 8800 (a Theorem Labs lane, C_reac_ctrl_parse.v:46)
     - reac_box_model_block at `846c8: jal 85b44` : REAC_BOX_MODEL_BLOCK_STK = 4320 (a Theorem Labs lane's draft sec. 2-3 (a working note, not in this delivery))
     - the bcmp wrapper at `846dc: jal 42970`     : 2 * ESTACK = 8192 (`aj_bcmp_at`, D YCbq.v:2065)
     - `__asan_stack_malloc_2` at `84500/84504`   : ESTACK = 4096 (`aj_stack_malloc_atS`, D YC85.v:295)
   CA >= S - 160 (CA_facts, reac_box_catalogue_match.v:232), so 160 + max(8800, 4320, 8192, 4096) = 8960 <= 9136
   (the real-stack arm calls at CA - 192 >= S - 336: 336 + 8800 = 9136, with equality). The callees' own constants
   are not restated here: they belong to their owners' files (CONVENTIONS sec. 2). *)
Definition CM_STK : Z := 9136.
(* The function makes no heap allocation and neither callee allocates, and `__asan_stack_malloc_N` is not a journal
   event (no `tick` in `stack_malloc`, D YG00.v:569-578); the bcmp wrapper keeps k (D YCbq.v:2075). *)
Definition EV_CM : Z := 0.
Definition LIVE_CM : Z := 0.
Section h.
Variable B : asyms.
(* The read-only window, as a Theorem Labs lane's `ctl_base` carries it (two Theorem Labs lanes, 23:37Z): Section variables right
   after B, so callers write `treac_box_catalogue_match_spec (SK := SK) B RLO RHI GLOBS`. *)
Variables RLO RHI : Z.
(* The read-only window lies in the image: what `arodata_ok_journalP` needs to carry the RO fact across each call
   (cgif lib/YC20.v:56, used at :60-68; here with SEGS = tfibsegs). The composer discharges it from PI_ctrl's
   `pa_relro_lo` / `pa_relro_hi` / `pa_relro_img` (a Theorem Labs lane via a Theorem Labs lane, 00:14Z); RLO / RHI stay Variables, so
   no relro range is written into this statement. *)
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> lib.Reusable.YG0d.in_img tfibsegs a.
(* The runtime's table of registered globals. *)
Variable GLOBS : list (Z * Z).

Definition treac_box_catalogue_match_post (regs : bvmap 5 word) ly S (W : world tfibsegs)
(mem : word -> option byte) md (len : Z) (fb : list byte) : world tfibsegs -> config -> Prop :=
apost_base tfibsegs B CM_STK [] regs ly S W mem md EV_CM
(fun ly' S' W' regs' mem' md' =>
lib.Reusable.YK11.getr regs' 10 = w64 (RcMatch.want A_CM_TBL len fb) /\
Permutation (ablocks B ly' S') (ablocks B ly S)).

Definition treac_box_catalogue_match_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (f len : Z) (fb : list byte),
afn_pre tfibsegs B CM_STK ly S W regs mem md ch ->
(* RO premise in a Theorem Labs lane's `ctl_base` form (Reusable/YE01.v:192, as A/ACfn.v:43 uses it); the PA layer's
   `arodata_okP` comes from ProgWorld's `arodata_okP_of_S` (a Theorem Labs lane; donor cgif A/ACfj.v:119). *)
arodata_okS tfibsegs B RLO RHI (aview tfibsegs (w_H W) mem) ->
(* No `achain` premise on entry and no `In (raZ regs :: spine ch) CTX`: the walk cannot supply a chain at the callee
   call sites, `astack_malloc_realizes` does not ask for one, and reac_ctrl_parse's spec dropped its own `achain`
   premise and its `ch` binder (a Theorem Labs lane 00:04Z, replacing the 21:47Z rule; a Theorem Labs lane 00:04Z R5). `afn_pre`
   still carries its own chain conjunct (D YCbq.v:341) through the binder `ch`. *)
(* a0 = f (`844f8: mv s3,a0`), a1 = len (`844dc: mv s4,a1`); a2 is overwritten at 0x844e4 before any use. *)
lib.Reusable.YK11.getr regs 10 = w64 f -> lib.Reusable.YK11.getr regs 11 = w64 len -> 0 <= f < 2 ^ 64 -> 0 <= len < 2 ^ 64 ->
(* The record: a live heap block, read only when 50 <= len. At both call sites the block's request size IS len
   (a Theorem Labs lane Q7, 21:33Z: R14 0x81838 and F36 0x828d4), so `50 <= len -> 50 <= req_size Lf` costs the caller nothing;
   the shape is reac_ctrl_parse's own premise (a Theorem Labs lane's spec draft sec. 1.1 (a working note, not in this delivery)). *)
length fb = 50%nat ->
(50 <= len -> exists Lf, In (f, Lf) (ablocks B ly S) /\ 50 <= req_size Lf) ->
(50 <= len -> garr8 tfibsegs (mrestrict (w_H W) mem) f (map (fun b : byte => bv_unsigned b) fb)) ->
(* The catalogue rows: values, registered shadow and image bounds. reac_box_model_block reads row i of this table
   (a Theorem Labs lane's draft sec. 6 (a working note, not in this delivery)). The `.str.4` premises of the draft are dropped: the composer discharges them, not this
   caller (sec. 4 of a Theorem Labs lane's working note, not in this delivery). *)
garr8 tfibsegs (mrestrict (w_H W) mem) A_CM_TBL CM_TBLZ ->
In (A_CM_TBL, CM_ROWS) GLOBS -> IMG_LO + 64 <= A_CM_TBL -> A_CM_TBL + CM_ROWS + 64 <= IMG_HI ->
(* The catalogue bytes are read-only image data, outside the owned statics and outside errno: what carries their
   values across the calls, and what reac_box_model_block asks of the row it reads, per sec. 6, open item 10(a) (a Theorem Labs lane's working note, not in this delivery;
   the text is a Theorem Labs lane's, with this file's RLO / RHI). *)
(forall a, A_CM_TBL <= a < A_CM_TBL + CM_ROWS ->
   in_roP tfibsegs RLO RHI a /\
   ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)) ->
(* Frame room, per class used along the chain (a Theorem Labs lane, Q2 21:29Z): class 2 for this function's
   `__asan_stack_malloc_2` at 0x84504, class 1 for reac_ctrl_parse, class 0 for reac_box_model_block. The form is
   the one cgif's rule takes (D YC85.v:298, applied at D A/AChf.v:209 for cid 2). The callees see
   `frames Sc = (2, pos) :: frames S`, and `count_cid c ((2,pos) :: l) = count_cid c l` for c <> 2
   (D YG01.v:214-215), so these three premises are exactly what they ask for. *)
count_cid 2 (frames S) < fs_frames 2 ->
count_cid 1 (frames S) < fs_frames 1 ->
count_cid 0 (frames S) < fs_frames 0 ->
st_nev S + EV_CM <= EV_MAX -> blocks_bytes S + LIVE_CM <= LIVE_MAX ->
SRr tfibsegs W (cfg_at tfibsegs A_catalogue_matchP regs mem md)
(treac_box_catalogue_match_post regs ly S W mem md len fb).
End h.
End d.
End b.
