(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S8aNumA.v, with its module names changed; 580 of its 611 lines of code are new or changed and 747 lines of the source are left out. *)
(* On the Step-1 contract texts (the re-hiding move): the walk's live journal and every
   stretch statement sit at the world relation R := YA0nH.wle' SEGS YGcfRehidePost.RZ_cf, the relation of the text's
   post QF (fpostFbm is AFTER-FREE-ONLY, restated at wle' in PRH_Base.v's R FAMILIES block). crt_live_journal is
   `exists WS, ajournal_xwR .. (wle' SEGS RZ_cf) .. WS /\ wbudget [] kb WS` (the notation AJW below) and CRT_B_AT_X / _C
   / _L3 / _L0 conclude `YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (crt_cfg ..) QF`. Names, binders and Records are
   unchanged. The contract note for the segment files is the internal file WLE-CONTRACT.md. *)
(* fuzz_preset: the IMAGE-GENERIC GLUE of the walk of check_round_trip
   (fuzz_preset.c new:772-781 with round_trip_rewrite new:715-769 INLINED) against the contract text
   tcheck_round_trip_specX (lib/A/PRH_FnCheck.v), on the harness-fix #102 pins.
   This file STATES: the boundary predicates of the segment cut, the live state a boundary carries, and the register
   snapshots. The segment proofs (Crt102A*.v) and the composition (Crt102Top.v) consume exactly these names. Its only
   proofs are the CAP bridge at the end of the file (crt_copy_cap_of_ncap48 and its two helpers).

   INPUTS OF RECORD (taken by path; every file of this walk repeats them):
   - pins: A' asan 1be0f53d96cb9d6c (twin bff8519bbe3ea0e4), B' asan-ubsan d663f82d7f488d30 (twin c90d4fa54d43160b).
   - contract texts: commit 3438f3406f33 -- lib/A/PRH_Base.v 016934fdc1af,
     lib/A/PRH_FnCheck.v 37d8e4d0072e, lib/A/PRH_Img.v 934516a622e8, lib/B/PRH_ImgB.v 3216eca68342,
     lib/Spec/PresetRodata.v 4eb7e95e7e93, lib/Spec/PresetRodataCheck.v 04662cf6a9cf.
   - listings of record: commit d42e123915ae -- lib/A/Listing_prog.v 1ab147923c5d,
     lib/A/PAImg_prog.v 47eeb54e93be, lib/B/Listing_prog.v 8bcc2c9e7809, lib/B/PAImg_prog.v 4392ab2c09ba,
     lib/Reusable/YPsym.v b6f5a85d234d.
   - engine: the WHOLE SET by path from commit 459129c18903 (YCbqG.v c3b5d0111037,
     YGcallcf.v 6d2b13c24437, YG0dcf.v f2e11ac13457, the YC80x / YC1fPx collapse, YGcallMxmn.v, YSRrMemnorm(J).v).
   - build route pins102: the internal file zfb-targets.dc6f8f60073340be.sh, FACTS 8f3e7e1a07f1, PAU pau-preset-102.
   - rule 24: no function proved (proof-index check_round_trip, exit 0,
     output an internal record of that lookup): the released proofs are plain (lib/Prog) and ubsan
     (lib/U/Prog) only, concluding in SR, not consumable here. Written new.

   LIBRARY TEXTS ARE CITED ONLY UNDER THE REQUEST BOUND. The merged alloc.c sets g_ran_out only for a request
   n <= g_most, and raises g_peak to g_live + n on a refusal, so prh_oks' third conjunct (PRH_Base.v:460) and the
   peak equalities of pj_parse / pj_set / the writer are FALSE above g_most until the E sweep. This walk carries
   `RQA_crt t <= most` to EVERY call explicitly (Crt102Model.v's named per-call bounds) and that is what makes each
   citation legitimate; the peak equalities are not leaned on anywhere.

   THE WILD BUDGET (kb round; the landing cut's texts at PRH_FnCheck.v 8feca2000b76). The text takes the room
   `wild_room (as_universe B) [] (prh_wk F_check_round_trip) (st_depot S)` (:1366) and posts a BUDGETED journal,
   fpostFbm .. (wbudget [] (prh_wk F_check_round_trip)) (:1405), and its two budgeted callees do the same at their own
   budgets (tround_trip_text_specX :1216 / :1256, 32; tparse_noting_specX :638 / :649, 2). The only budgeted call rule,
   YCbqGwild.aj_call_xbF, leaves the caller at the budget WS0 ++ WS1, never at the unbudgeted journal. So this file
   states (G1) the journal notation AJW at a budget, (G2) QF at the text's budget 66, (G3) crt_live with its budget kb
   and its journal at a budget WS with wbudget [] kb WS, and (G4) each boundary's kb (THE BOUNDARIES' note).

   THE FRAME. check_round_trip takes a class-3 fake frame: `addi sp, sp, -0xe0`, 13 saves at sp0-8 .. sp0-0x68
   (ra, s0 .. s11), `addi s0, sp, 0xe0` (s0 = the entry sp), `andi sp, sp, -0x20` (sp = s1 = CRT_sp1), the
   use-after-return flag out of its GOT word, `__asan_stack_malloc_3` with a0 = 0x140 at entry+0x6c. The class-3
   frame is fs_frame_bytes 3 = 512 bytes; the flag word sits at F + 504 (the listing's `ld a0, 0x1f8(s3)`), the
   frame's shadow is 64 bytes and the request's 0x140 bytes are its first 40 shadow bytes.
   The locals in it: back at F+0x20, v at F+0x80, copy at F+0xe0. The STACK PATH (the frame call returning 0, and
   the alloca fallback at +0x84..+0x9c) is UNREACHABLE: the flag is 1 by alx_const and PALib, and
   astack_malloc_realizes_cf returns frame_addr ly 3 pos, which frames_bounds_x puts at or above 4096.

   round_trip_rewrite IS INLINED. Cuts U..C and X are its body, run on check_round_trip's own class-3 frame; its
   unpoison of back / v (A' 0x82a54-0x82a88) and its re-poison (A' 0x82b74-0x82bac) are check_round_trip's steps,
   and its returns never materialise. Its read-back callee is parse_noting, not pj_parse.

   IMAGE B'. The two images agree in OPCODES to index 113 (first opcode divergence +0x1c8) but their REGISTER
   OPERANDS differ from +0x5c: 31 of the 101 slots in [+0x0, +0x194) (row CRT-B-EPHM). So every register
   fact below is IMAGE A' ONLY, and each boundary that names a register has a `_B` twin, byte-equal except the
   register numbers and the B' spill constants: crt_bregs_B, crt_dregs_B, crt_at_J_B, crt_at_U_B, crt_at_X_B,
   crt_at_L0_B. crt_live has none: it names no register, and CRT_SP_F, CRT_SAVED and CRT_OFF_COPY are the same on
   both images (the prologue evidence of row T8).

   NUMERALS. LENGTH: 0xe0 (own frame), 0x20 (the realignment), 8 / 0x20 / 0x80 / 0xe0 (the frame's locals), 0x1f8
   (the flag word's offset in a class-3 frame = fs_frame_bytes 3 - 8), 0x38 (sizeof struct pj), 0x18 / 0x20 / 0x28
   (kids / keys / n inside struct pj), 56 / 512 / 64. DERIVED: every cut offset (4 * the slot inside the function,
   Crt102Img.v), the spill offsets off s1, shadow_addr. WORD: 6 (PJ_OBJECT), 4 (PJ_STRING), -8 / -0xf / -0xe / -0xd
   (the poison bytes f8 / f1 / f2 / f3). No ADDRESS literal: every code address is pa_sigma / pa_val of the listing.
   *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YGcallx YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames FCiface YGcallSx YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomLive YAkMemnorm.
(* The re-hiding move's world relation (YA0nH.wle', YA0nH.SRr') at preset's zone RZ_cf *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjRoundTrip PresetRoomPos PresetReqAt PresetReqAtNoMiss.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes WriterValue PjWriteHyp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnCheck CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnPj PRH_FnWriter PRH_PjOrder.
(* Crt102Model's `cm_at` (the index the at-search finds), for the B' loop tail's crt_at_L3_B / crt_at_C_B below.
   No cycle: Crt102Model.v Requires no Crt102 file. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import Crt102Model.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the frame's own numbers (LENGTH, read off the listing; no ADDRESS) ---- *)
Definition CRT_FRAME : Z := 224.          (* 0xe0, the first `addi sp, sp, -0xe0` *)
Definition CRT_ALIGN : Z := 32.           (* the `andi sp, sp, -0x20` *)
Definition CRT_CID : Z := 3.              (* __asan_stack_malloc_3 *)
Definition CRT_REQ : Z := 320.            (* 0x140, the request the call makes *)
Definition CRT_OFF_BACK : Z := 32.        (* back  = F + 0x20 *)
Definition CRT_OFF_V : Z := 128.          (* v     = F + 0x80 *)
Definition CRT_OFF_COPY : Z := 224.       (* copy  = F + 0xe0 *)
(* struct pj (56 bytes): type at 0, num at 8, str at 0x10, kids at 0x18, keys at 0x20, n at 0x28 *)
Definition PJ_OFF_KIDS : Z := 24.
Definition PJ_OFF_KEYS : Z := 32.
Definition PJ_OFF_N : Z := 40.
(* the words the body spills at s1 (= the realigned sp). IMAGE A' ONLY: B' spills other words at other offsets and
   keeps other registers (Crt102Img's measurement; the internal file DESIGN.md's B' section). Offsets of the writes read off the internal file crt.A.s
   and corrected by Crt102Img. *)
Definition CRT_SP_SAVED : Z := 24.        (* 0x18(s1) = saved, written at +0x498 *)
Definition CRT_SP_AT : Z := 32.           (* 0x20(s1) = at *)
Definition CRT_SP_BACK : Z := 56.         (* 0x38(s1) = &back, written at +0x2a0 *)
Definition CRT_SP_SHN : Z := 72.          (* 0x48(s1) = shadow(&doc->n), written at +0x250 *)
Definition CRT_SP_PN : Z := 80.           (* 0x50(s1) = &doc->n, written at +0x230; OVERWRITTEN at +0x49c with doc->n *)
Definition CRT_SP_N : Z := 88.            (* 0x58(s1) = doc->n, written at +0x238 *)
Definition CRT_SP_F : Z := 112.           (* 0x70(s1) = F, written at +0xa0 *)
(* the same three words on IMAGE B', at OTHER offsets of s1 (the word-by-word decode of row CRT-B-UGKO1,
   re-read by this walk off the internal file crt.B.s): `addi a0, s6, 0x28` +0x224, `sd a1, 0x50(s1)` +0x230 with a1 = the shadow of
   &doc->n, `sd a0, 0x58(s1)` +0x23c with a0 = &doc->n, `ld a0, 0(a0)` and `sd a0, 0x48(s1)` +0x244 = doc->n.
   CRT_SP_SAVED / CRT_SP_AT / CRT_SP_BACK on B' are the B' segments' to measure; CRT_SP_F is the same on both. *)
Definition CRT_SP_SHN_B : Z := 80.        (* B' 0x50(s1) = shadow(&doc->n), written at +0x230 *)
Definition CRT_SP_PN_B : Z := 88.         (* B' 0x58(s1) = &doc->n, written at +0x23c *)
Definition CRT_SP_N_B : Z := 72.          (* B' 0x48(s1) = doc->n, written at +0x244 *)
(* B': the lbu immediate of the two g_own_ran_out loads at +0x2c4 / +0x2f0, which reuse s10 from O1's `auipc s10`
   at +0x288 (row T4's CRT_OWN_LO_B; row CRT-B-UGKO1's decode checked the auipc lands at pi_g_own_ran_out - 0x2d0) *)
Definition CRT_OWN_LO_B : Z := 720.
(* B': the cut crt_at_W_B sits at - pj_write's argument set-up, BEFORE its call (+0x2a4 .. +0x2b8 `jal pj_write`);
   Crt102Img's CRT_W_OFF_B (+0x2bc) is pj_write's RETURN. Defined ONCE here (the walk owner's order); T3's Base copy and
   T4's copy are deleted and both cite this. DERIVED (an offset from the B' entry 0x82828), not an address. *)
Definition CRT_W0_OFF_B : Z := 676.
(* the B' spill slots off s1 (= CRT_sp1) the loop tail reads that the slots above do not name - row T6's
   (commit 62d39032031, lib/B/Prog/Crt102SeamB.v blob efaa8f4f71e4), read off B/Listing_prog.v
   8bcc2c9e7809 (writer offset, line). CRT_SP_SAVED (0x18) and CRT_SP_AT (0x20) are A' slots: B' keeps saved at 0(s1)
   and at at 0x40(s1). CRT_SP_BACK 0x38 and CRT_SP_F 0x70 are kept on B'. *)
Definition CRT_SP_SAVED_B : Z := 0.     (* 0(s1) = saved: `sd s8, 0(s1)` +0x478 (L0's first word), line 1412 *)
Definition CRT_SP_SHKIDS_B : Z := 40.   (* 0x28(s1) = shadow (&doc->kids): `sd a0, 0x28(s1)` +0x5b0, line 1490 *)
Definition CRT_SP_KEYS_B : Z := 48.     (* 0x30(s1) = &doc->keys: `sd a0, 0x30(s1)` +0x4a4, line 1423 *)
Definition CRT_SP_AT_B : Z := 64.       (* 0x40(s1) = at: `sd a1, 0x40(s1)` +0x56c, line 1473 *)
Definition CRT_SP_KIDS_B : Z := 72.     (* 0x48(s1) = &doc->kids from +0x5a4 (line 1487) on; before it, the glue's
                                           CRT_SP_N_B (doc->n as U read it) *)
(* the thirteen saved slots, as offsets below the entry sp, with the register each holds *)
Definition CRT_SAVED : list (bv 5) := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg}.
#[local] Existing Instance CfParams_preset.
Context {PI : PrhImg} {RL : PrhRoomLive} {SK : YI16.sink_head} {L : ptable asym} {PA : PAImg L}.
#[local] Notation SEGS := (@pa_segs _ L PA).
#[local] Notation VAL := (@pa_val _ L PA).
#[local] Notation SIGMA := (@pa_sigma _ L PA).
#[local] Notation BASE := (@pa_val _ L PA A_TEXT).
#[local] Notation RLO := (@pa_relro_lo _ L PA).
#[local] Notation RHI := (@pa_relro_hi _ L PA).
#[local] Notation PST := (@prh_pst PI).
#[local] Notation STKC := (@STK_check_round_trip PI).
(* the image's cut offsets: NAMED here, given their measured values by the image file (Crt102Img.v) *)
Context {CRT_PC CRT_E_OFF CRT_P_OFF CRT_H_OFF CRT_M_OFF CRT_R1_OFF CRT_R2_OFF CRT_T_OFF CRT_U_OFF CRT_G_OFF
         CRT_K_OFF CRT_O1_OFF CRT_W_OFF CRT_N_OFF CRT_O2_OFF CRT_FF_OFF CRT_X_OFF CRT_J_OFF CRT_Z_OFF CRT_Q_OFF
         CRT_L0_OFF CRT_L1_OFF CRT_L2_OFF CRT_L3_OFF CRT_C_OFF CRT_AB_OFF : Z}.

Section f.
Context {B : asyms}.
Context {ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop}.
(* G1 (kb round): the journal from the entry at a wild-trace budget WS (YCbqG.v ajournal_xw; its last conjunct is
   `incl (wild_part (as_universe B) (st_depot S')) (wild_part (as_universe B) (st_depot S) ++ WS)`, YCbqG.v:400). The unbudgeted ajournal_x is ajournal_xw at
   WS = [], and no statement of this file names it any more.
   The re-hiding move: the journal is the engine's R form ajournal_xwR at
   R := YA0nH.wle' SEGS YGcfRehidePost.RZ_cf (YCbqG.v; its fourth conjunct is `wle' SEGS RZ_cf W W'`, every other
   conjunct is ajournal_xw's), the relation of QF's journal, so a callee post at wle' composes into it. *)
#[local] Notation AJW := (ajournal_xwR (SK := SK) SEGS B PST ARx (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf)).

Section g.
(* ---- the entry: tcheck_round_trip_specX's binders (PRH_FnCheck.v:766-797) ---- *)
Context {rp_sm : list Z -> Z * Z} {rp_x : list Z}
        {rp_os : list (option nat * option nat * option nat)} {rp_i : nat} {rp_H0 : list Z}
        {rp_hist : list YG00.chunk}.
Context {ly : alayout} {S : astate} {Hp : list Z} {W : world SEGS} {regs : bvmap 5 word}
        {mem : word -> option byte} {md : Model} {ch : list (Z * Z * Z)}
        {doc : Z} {t : PjTree.jv} {D : list (Z * Z)} {x : list Z}
        {Lam : list (Z * Z)} {peak cnt ran most : Z}
        {CTX0 : list (list Z)} {a_mod_at a_stamp : Z}.
#[local] Notation sp0 := (spZ regs).

(* the realigned stack pointer the body runs on: s1 = sp = (sp0 - 0xe0) rounded down to 32 (DERIVED) *)
Definition CRT_sp1 : Z := (sp0 - CRT_FRAME) / CRT_ALIGN * CRT_ALIGN.

(* ---- the text's conclusion, as one name every segment proof ends in. tcheck_round_trip_specX's post at
   commit 5f3f7cc29ecb (PRH_FnCheck.v f7be7f968195:1028-1039) over the record model (PresetReqAt 379c33e9e482):
   NO position after room_live_cf; the EXACT advance by `length (PresetReqAt.round_trip rp_sm t)` (ReaderRes.jr_strtod for rp_sm in this tree's keyed text, PRH_FnCheck.v:2422) on the r = 0 arm
   only; the r = 1 arm states none. ---- *)
(* RESTATED (PRH_FnCheck 9ecd8eb167c6): the E sweep moved g_most and g_own_ran_out into
   the ledger (prh_ledger .. ran most own, PRH_Base fdb45545469b:522), so the post's separate prh_most / prh_own are
   gone and own' is bound with the ledger's other cells. Verbatim otherwise. *)
Definition QT : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  fun ly' S' Hp' W' regs' mem' md' =>
    room_live_cf S' /\ exists Lam' peak' cset cnt' ran' own',
    Permutation Lam' Lam /\ Permutation (ablocks B ly' S') (ablocks B ly S) /\ peak <= peak' /\
    0 <= cset <= 3 /\ (forall ms, t = PjTree.JObj ms -> In ck_MOD_AT (map fst ms) -> cset = 0) /\
    prh_ledger B ly' S' Hp' W' mem' Lam' peak' cnt' SIZE_MAXZ ran' most own' /\
    pj_nodeR SEGS (mrestrict (w_H W') mem') (prh_lin Lam') doc t D /\
    exists r, getr regs' 10 = w64 r /\
      (* commit 6557b95928b5 (PRH_FnCheck 0b6f7b597757): THE r = 1 ARM IS DEAD under the text's new entry premise
         prh_cons_from (every allocation of the call is a consumer allocation of the run, so no real refusal) *)
      r = 0 /\
      ((r = 1 /\ (own' = 1 \/ ran' = 1) /\ cnt <= cnt' <= cnt + ck_crt_count t cset) \/
       (r = 0 /\ own' = 0 /\ cnt' = cnt + ck_crt_count t cset /\ ran' = ran /\
        exists hist', PresetRoomPos.iface_room_pos rp_sm rp_x rp_os
          (rp_i + length (PresetReqAt.round_trip rp_sm t))%nat rp_H0 hist' S')).

(* G2 (kb round): QF as before (fQmn mem QT under the text's m-form post), now at the text's BUDGETED form
   (tcheck_round_trip_specX, PRH_FnCheck.v 8feca2000b76:1405): fpostFbm (= fpostFb .. (fQmn mem ..), PRH_Base.v
   ef7c8ca98529:1402-1406, YCbqGwild.apost_base_xbF at the Section's fx) at wbudget [] (prh_wk F_check_round_trip),
   66 = 32 + 32 + 2 (PRH_Base.v:151-160): the two round_trip_text calls and the one parse_noting call. *)
Definition QF : world SEGS -> config -> Prop :=
  fpostFbm B ARx SK (YCbqGwild.wbudget [] (prh_wk F_check_round_trip)) STKC [] regs ly S Hp W mem md (fQmn mem QT).

(* ---- RECORDS, NOT CONJUNCTIONS (the walk owner's approval, 2026-10-30, of this walk's plan). Every predicate below
   whose TOP level binds nothing is a Prop Record with one field per former conjunct, field names <pred>_<role>
   (the unit's convention for glue predicates and kit posts alike). A predicate whose top level binds (crt_pos) is a
   Record whose binding part is one field over a second Record (crt_pos_at). A field may itself be an existential or
   a disjunction: crt_at_J's count and crt_at_L0's outcome are ONE field each, so the arms stay a disjunction inside a
   named field. QT is NOT a Record: it is the text's post, verbatim.
   READ a field by its projection (`crt_live_side HL`), never by an intro pattern: a pattern counts positions, and
   this unit measured four breaks of that kind on 2026-10-29 (a 54-minute Kit hang on a positional intro over a grown
   crt_live, 85 positional sites in the B' rows, tpj_set's mid-predicate conjunct, the Ent102CutsB comment).
   BUILD one with the named literal `{| crt_live_journal := ..; .. |}` (or `refine {| .. := _; .. |}`).
   The statements are the conjunctions they replace, field for field, in the same order: nothing is added or
   removed. ---- *)
(* The projections take the Record's parameters IMPLICITLY (inferred from the record argument), so a field reads as
   `crt_live_side HL`. Implicit Arguments is on from here to the end of Section g: every Definition below has a
   non-dependent type, so it gains no implicit argument and its explicit arguments are unchanged. *)
Local Set Implicit Arguments.

(* ---- the thirteen saved words, read back by the epilogue: the boundary carries the SLOTS, not the registers
   (ra is not callee-saved, and after any call every one of s0 .. s11 may hold something else) ---- *)
Definition crt_saved (Wc : world SEGS) (memc : word -> option byte) : Prop :=
  forall j, (j < 13)%nat ->
  val_mem SEGS (mrestrict (w_H Wc) memc) (sp0 - 8 * (Z.of_nat j + 1)) 8
    (bv_unsigned (getr regs (nth j CRT_SAVED 0%bv))).

(* ---- the fake frame the prologue holds: it is on the frame list, its bytes are present, and the word the retire
   store reads holds its flag's address ---- *)
Record crt_frame (lyc : alayout) (Sc : astate) (Wc : world SEGS) (memc : word -> option byte) (pos : Z) : Prop :=
  mk_crt_frame {
  crt_frame_listed : In (CRT_CID, pos) (frames Sc);
  crt_frame_flag_word : rdword (aview SEGS (w_H Wc) memc) (frame_addr lyc CRT_CID pos + fs_frame_bytes CRT_CID - 8)
    = Some (flag_addr lyc CRT_CID pos);
  crt_frame_present : forall a, frame_addr lyc CRT_CID pos <= a < frame_addr lyc CRT_CID pos + fs_frame_bytes CRT_CID ->
     apresent (w_H Wc) memc a }.

(* ---- a word the body spilled at s1 and reads back later ---- *)
Definition crt_spill (Wc : world SEGS) (memc : word -> option byte) (off v : Z) : Prop :=
  val_mem SEGS (mrestrict (w_H Wc) memc) (CRT_sp1 + off) 8 v.

(* ---- the ledger side of a boundary: the ledger at that point, the flags, the request bound, the room, the
   read-only view, and the document still readable in the blocks the boundary names.
   NO ROOM POSITION (removed 2026-10-29, the walk owner's yes to this walk's proposal): every r = 1 exit (C1, C2, C4a,
   C4c) comes after a refusal, where the callee's text states no position, so a position conjunct here made crt_live
   unproducible on reachable arms - a false boundary. The position now travels as `crt_pos` on the r = 0-path
   boundaries only. CONSEQUENCE: crt_side and crt_live no longer depend on rp_sm rp_x rp_os rp_i rp_H0, so an
   explicit `@crt_live ..` application loses those five arguments; use named arguments. ---- *)
(* RESTATED (lib/A/PRH_Base.v section c): prh_ledger now carries g_most and g_own_ran_out (.. ran most own), so the
   separate prh_own / prh_most conjuncts are gone - read them with PRH_Base.prh_ledger_own / prh_ledger_most. The
   arguments of crt_side are unchanged (ownc is the ledger's own cell now). *)
Record crt_side (lyc : alayout) (Sc : astate) (Hpc : list Z) (Wc : world SEGS) (memc : word -> option byte)
  (Lamc : list (Z * Z)) (peakc cntc ownc ranc : Z) : Prop := mk_crt_side {
  crt_side_ledger : prh_ledger B lyc Sc Hpc Wc memc Lamc peakc cntc SIZE_MAXZ ranc most ownc;
  crt_side_peak : peak <= peakc;
  crt_side_room : room_live_cf Sc;
  crt_side_arodata : arodata_okP SEGS RLO RHI B (aview SEGS (w_H Wc) memc);
  crt_side_doc : pj_nodeR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) doc t D;
  crt_side_doc_blocks : forall bk, In bk D -> In bk Lamc }.

(* ---- THE LIVE STATE after the frame call: the journal from the entry with the class-3 frame owned, the saved
   words, the frame, the side facts, and THE BLOCKS THE WALK HOLDS BEYOND THE ENTRY'S (`Dx`).
   `Dx` is why this is an invariant and not three continuation premises: every post of a callee relates the
   allocator blocks only to the blocks AT ITS OWN CALL, so a boundary that does not carry the relation to the
   ENTRY cannot rebuild it, and `QT` asks for exactly that at the return (Crt102Arms' finding). At M, `Dx = []`.
   `blocks_bytes Sc = blocks_bytes S` for the callees' live-room premises follows from it by `blocks_bytes_bsum`. ---- *)
(* G3 (kb round): THE WILD BUDGET kb. The journal from the entry is at a budget WS - the wild traces the budgeted
   calls made so far may have stored - with `wbudget [] kb WS` (wfresh [] WS <= kb, YCbqGwild.v:113; 0c63874858e4:102 as history).
   kb is the budget SPENT on the paths into the boundary, so it is not one constant (the next callee is paid from
   the room left): 0 at M, 32 between rtt1 and rtt2, 64 at U and W, 66 at L0, L3, C, X and J (THE BOUNDARIES'
   note). The room a later callee asks comes from the text's entry room by YCbqGwild.ajournal_xw_roomR (YCbqGwild.v:384) and
   wild_room_le (:186): `wild_room (as_universe B) [] (66 - kb) (st_depot Sc)`. At WS = [] the field is the unbudgeted journal at wle'
   (ajournal_xR, YCbqG.v:425-429; its wle form is ajournal_x, :413-417), and a live state at kb is one at every larger budget. *)
Record crt_live (kb : nat) (lyc : alayout) (Sc : astate) (Hpc : list Z) (Wc : world SEGS) (memc : word -> option byte)
  (mdc : Model) (kj pos : Z) (Dx Lamc : list (Z * Z)) (peakc cntc ownc ranc : Z) : Prop := mk_crt_live {
  crt_live_journal : exists WS : list (list Z),
    AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] lyc Sc Hpc Wc memc mdc kj WS /\ YCbqGwild.wbudget [] kb WS;
  crt_live_side : crt_side lyc Sc Hpc Wc memc Lamc peakc cntc ownc ranc;
  crt_live_lam_perm : Permutation Lamc (Dx ++ Lam);
  crt_live_blocks_perm : Permutation (ablocks B lyc Sc) (ablocks B ly S ++ ck_hblks Dx);
  crt_live_dx_apart : forall bk, In bk Dx -> ~ In bk D;
  crt_live_saved : crt_saved Wc memc;
  crt_live_frame : crt_frame lyc Sc Wc memc pos;
  crt_live_fspill : crt_spill Wc memc CRT_SP_F (frame_addr lyc CRT_CID pos);
  (* COPY'S SHADOW IS OPEN from H to Z: the prologue writes its seven shadow bytes (s2+0x1c .. +0x22) as 00 and
     nothing writes them again until the re-poison at +0x348, so every boundary has it. Two consumers:
     round_trip_text's `ck_out_ok .. copy 56` at M, whose wdest_ok (PRH_Base.v:877-881) asks for both of these at
     the call's memory (Crt102Entry's finding), and pj_free's prhPj_slot at &copy in the tail, whose 56-byte
     memset of the node is instrumented (Crt102Tail's finding). *)
  crt_live_copy_open : range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF
    (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) 56;
  crt_live_copy_hull : shadow_hull_vis (aview SEGS (w_H Wc) memc) (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) 56;
  crt_live_memnorm : YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS memc }.

(* ---- the registers the body keeps from the prologue on. s0 = the entry sp, s1 = sp = CRT_sp1,
   s2 = the frame's shadow, s3 = the frame-call result, s4 = &copy, s7 = -8, s10 = the shadow base, s11 = F.
   (RISC-V names: s0 = 8, s1 = 9, s2 = 18, s3 = 19, s4 = 20, s5 = 21, s6 = 22, s7 = 23, s8 = 24, s9 = 25,
   s10 = 26, s11 = 27.) ---- *)
Record crt_bregs (rg : bvmap 5 word) (F : Z) : Prop := mk_crt_bregs {
  crt_bregs_sp : getr rg 2 = w64 CRT_sp1;
  crt_bregs_gp : getr rg 3 = getr regs 3;
  crt_bregs_tp : getr rg 4 = getr regs 4;
  crt_bregs_s0 : getr rg 8 = w64 sp0;
  crt_bregs_s1 : getr rg 9 = w64 CRT_sp1;
  crt_bregs_s2 : getr rg 18 = w64 (shadow_addr F);
  crt_bregs_s4 : getr rg 20 = w64 (F + CRT_OFF_COPY);
  (* s3 = the frame-area call's result. It is written ONCE, by `mv s3, a0` at +0x70, and is callee-saved, so it is
     F at every boundary; the retire needs it twice, at the `beqz s3` that would take the (dead) stack path and at
     the flag store's `ld a0, 0x1f8(s3)`. (Crt102Tail's finding.) *)
  crt_bregs_s3 : getr rg 19 = w64 F;
  crt_bregs_s7 : getr rg 23 = w64 (2 ^ 64 - 8);
  crt_bregs_s10 : getr rg 26 = w64 SHADOW_OFF;
  crt_bregs_s11 : getr rg 27 = w64 F }.
(* before the member loop s5 still holds doc *)
Record crt_dregs (rg : bvmap 5 word) (F : Z) : Prop := mk_crt_dregs {
  crt_dregs_bregs : crt_bregs rg F;
  crt_dregs_s5 : getr rg 21 = w64 doc }.

(* ---- PROPOSAL (row T8, 14:5xZ; accepted in shape by the walk owner 14:55Z, frozen by this walk): the
   image-B' twins. B' (asan-ubsan d663f82d) allocates the body's registers differently from A' after +0x1c8
   (lib/B/Listing_prog.v 8bcc2c9e7809 @ d42e123915ae, check_round_trip at 0x82828;
   prologue `ld s11, 0(a1)` +0x5c, `mv s6, a0` +0x60, `mv s7, a0` +0x70, `mv s3, s7` +0x7c, `addi s4, s3, 0xe0`
   +0xa4, `srli s2, s3, 3` / `add s2, s2, s11`, `addi s9, zero, -8` +0xb8; the tail `beqz s7` +0x378,
   `ld a0, 0x1f8(s7)` +0x388, `mv a0, s5` +0x434). So on B': s7 = the frame-call result (F at every boundary,
   since crt_frame puts the class-3 frame on the list), s3 = F, s9 = -8, s11 = the shadow base, s5 = the value the
   function returns, s6 = doc. Byte-equal to the A' texts except the register numbers. The spill slot of F
   (0x70(s1), CRT_SP_F), the thirteen saved slots (CRT_SAVED) and CRT_OFF_COPY are the same on both images. *)
Record crt_bregs_B (rg : bvmap 5 word) (F : Z) : Prop := mk_crt_bregs_B {
  crt_bregs_B_sp : getr rg 2 = w64 CRT_sp1;
  crt_bregs_B_gp : getr rg 3 = getr regs 3;
  crt_bregs_B_tp : getr rg 4 = getr regs 4;
  crt_bregs_B_s0 : getr rg 8 = w64 sp0;
  crt_bregs_B_s1 : getr rg 9 = w64 CRT_sp1;
  crt_bregs_B_s2 : getr rg 18 = w64 (shadow_addr F);
  crt_bregs_B_s4 : getr rg 20 = w64 (F + CRT_OFF_COPY);
  crt_bregs_B_s3 : getr rg 19 = w64 F;
  crt_bregs_B_s7 : getr rg 23 = w64 F;
  crt_bregs_B_s9 : getr rg 25 = w64 (2 ^ 64 - 8);
  crt_bregs_B_s11 : getr rg 27 = w64 SHADOW_OFF }.
(* on B', doc stays in s6 *)
Record crt_dregs_B (rg : bvmap 5 word) (F : Z) : Prop := mk_crt_dregs_B {
  crt_dregs_B_bregs : crt_bregs_B rg F;
  crt_dregs_B_s6 : getr rg 22 = w64 doc }.

(* ---- the state of the frame's three locals, as a boundary names it.
   `copy` is ZEROED by __asan_memset at +0x190 (new:774-775 `struct pj copy = empty`), so at M it is the zero tree,
   not an indeterminate 56 bytes; after a successful rtt1 it holds the compact read-back tree over Db. ---- *)
Definition crt_copy_zero (Wc : world SEGS) (memc : word -> option byte) (F : Z) : Prop :=
  pj_zeroR SEGS (mrestrict (w_H Wc) memc) (F + CRT_OFF_COPY).
Definition crt_copy_tree (Wc : world SEGS) (memc : word -> option byte) (Lamc : list (Z * Z)) (F : Z)
  (tv : PjTree.jv) (Db : list (Z * Z)) : Prop :=
  pj_nodeR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) (F + CRT_OFF_COPY) tv Db.

(* ---- THE ROOM POSITION on the r = 0 path (the walk owner's yes, 2026-10-29). `evs` is what is still to happen of
   the model's own list for this call, PresetReqAt.round_trip (record blob 379c33e9e482): the walk has done `pre`,
   it is at position rp_i + length pre with the room the model gives there, and the run's events from there are
   exactly `evs`. The text's entry premise `prh_run_at .. rp_i (PresetReqAt.round_trip rp_sm t)` with
   `iface_room_pos .. rp_i ..` is crt_pos S (round_trip rp_sm t); its r = 0 post is crt_pos S' [] read back. Carried
   ONLY on the r = 0-path boundaries, each with its own suffix below; never on an r = 1 arm, where the callee's text
   states no position. ---- *)
(* the text is keyed (HP_sm, PRH_FnCheck.v:2369-2370): it has no rp_sm binder and writes ReaderRes.jr_strtod where
    rp_sm stood, and it takes `PRH_Base.prh_cons_from ReaderRes.jr_strtod rp_x rp_os rp_i (length (PresetReqAt.round_trip ReaderRes.jr_strtod t))`
    (:2378). Not every callee text takes such a window (tpj_free_specX, PRH_FnPj.v:1105-1170, and tfuzz_free_specX, PRH_FnAlloc.v:342-428, take none); of the callee texts only the keyed six (PRH_FnWriter.v:
   1152-1157) fix the strtod model, the writer / tx texts keep rp_sm free. So crt_pos carries the window for the
   remaining `evs`, split by PRH_Base.prh_cons_from_app_iff exactly as the run premise by prh_run_at_app_iff. *)
(* RECORD FORM: the binding part is crt_pos_at (the position after `pre`, with the history `hist`), one field
   crt_pos_ex of crt_pos. Read it as `destruct (crt_pos_ex HP) as (pre & hist & HA)` - two binders and one name, no
   position count - and then crt_pos_split / crt_pos_room / crt_pos_run / crt_pos_cons of HA. *)
Record crt_pos_at (Sc : astate) (evs : list PresetReqAt.hev) (pre : list PresetReqAt.hev)
  (hist : list YG00.chunk) : Prop := mk_crt_pos_at {
  crt_pos_split : PresetReqAt.round_trip rp_sm t = pre ++ evs;
  crt_pos_room : PresetRoomPos.iface_room_pos rp_sm rp_x rp_os (rp_i + length pre)%nat rp_H0 hist Sc;
  crt_pos_run : prh_run_at rp_sm rp_x rp_os (rp_i + length pre)%nat evs;
  crt_pos_cons : PRH_Base.prh_cons_from rp_sm rp_x rp_os (rp_i + length pre)%nat (length evs) }.
Record crt_pos (Sc : astate) (evs : list PresetReqAt.hev) : Prop := mk_crt_pos {
  crt_pos_strtod : rp_sm = ReaderRes.jr_strtod;
  crt_pos_ex : exists pre hist, crt_pos_at Sc evs pre hist }.

(* the remaining suffix of round_trip at each r = 0 cut, in the model's own pieces (PresetReqAt.v 379c33e9e482:
   round_trip :330-335, rw_evs :325-327, set_evs :315-320). round_trip t =
   rt_text t false ++ rt_text t true ++ [HBulk (fo t)] ++ (JObj ms => rw_evs ms ++ [HBulk (fo (copy_set ms))]
   | _ => [HBulk (fo t)]); rw_evs ms = set_evs ms ++ w_evs (copy_set ms) true ++ parse_evs (wdoc ..) [] ++
   w_free (copy_set ms) true ++ [HBulk (fo (copy_set ms))]. The loops (strcmp, same) make no allocator event, so
   L0, L3 and C share one suffix. *)
(* J (and X, which carries crt_at_J): only pj_free (&copy) is left *)
Definition crt_evs_J : list PresetReqAt.hev :=
  match t with
  | PjTree.JObj ms => [PresetReqAt.HBulk (PresetReqAt.fo (PresetReqAt.copy_set ms))]
  | _ => [PresetReqAt.HBulk (PresetReqAt.fo t)]
  end.
(* the tree `copy` holds at J on the r = 0 arm: rtt1's read-back of t when t is not an object (C3), the pj_set
   result copy_set ms when it is (C4-full) - so crt_evs_J = [HBulk (fo crt_tree_J)] by unfolding *)
Definition crt_tree_J : PjTree.jv :=
  match t with
  | PjTree.JObj ms => PresetReqAt.copy_set ms
  | _ => t
  end.
(* L0 (on its granted arm), L3, C: fuzz_free (saved), pj_free (&back), pj_free (&copy) *)
Definition crt_evs_L0 (ms : list (list Z * PjTree.jv)) : list PresetReqAt.hev :=
  PresetReqAt.w_free (PresetReqAt.copy_set ms) true ++
  [PresetReqAt.HBulk (PresetReqAt.fo (PresetReqAt.copy_set ms))] ++
  [PresetReqAt.HBulk (PresetReqAt.fo (PresetReqAt.copy_set ms))].
(* W: pj_write (copy, 1), parse_noting, then L0's *)
Definition crt_evs_W (ms : list (list Z * PjTree.jv)) : list PresetReqAt.hev :=
  PresetReqAt.w_evs (PresetReqAt.copy_set ms) true ++
  PresetReqAt.parse_evs rp_sm (WriterValue.wdoc (PresetReqAt.copy_set ms) true) [] ++ crt_evs_L0 ms.
(* U: the whole rewrite, then pj_free (&copy) *)
Definition crt_evs_U (ms : list (list Z * PjTree.jv)) : list PresetReqAt.hev :=
  PresetReqAt.rw_evs rp_sm ms ++ [PresetReqAt.HBulk (PresetReqAt.fo (PresetReqAt.copy_set ms))].

(* ---- the configuration at a cut ---- *)
Definition crt_cfg (fxk : YK11.FPState) (off : Z) (rg : bvmap 5 word) (memc : word -> option byte)
  (mdc : Model) : config :=
  mkCfg (@YK11.mkst fxk rg (Z_to_bv 64 (BASE + (CRT_PC + off))) memc (YK11.seg_rom SEGS)) mdc.

(* ---- THE BOUNDARIES. Each is `the run from this configuration reaches QF`, so a segment lemma is
   `crt_at_<next> -> crt_at_<this>` and the composition is their chain (the H5Crt stage shape, re-cut on the
   #102 offsets). A boundary names: the live state, the frame, the registers, the spills written before it, and the
   semantic facts the arms below it need.
   G4 (kb round): THE BUDGET EACH BOUNDARY'S crt_live CARRIES. crt_live is shared by A' and B', so each B' Record
   takes the kb of its A' twin, and the value is FORCED, not chosen, by two bounds: PRODUCIBLE - kb is at least the
   budget spent on every path into the boundary (the landing of aj_call_xbF is at WS0 ++ WS1, YCbqGwild.wbudget_app);
   CONSUMABLE - kb plus the budget of every budgeted callee still ahead is at most 66, the budget of QF (the next
   callee is paid from `wild_room [] (66 - kb)`). The walk's other callees spend none of it.
   - crt_at_U, crt_at_U_B, crt_at_W_B: rtt1 and rtt2 are spent (32 + 32) and parse_noting (2) is ahead, so kb = 64,
     spelled (prh_wk F_round_trip_text + prh_wk F_round_trip_text)%nat. W_B sits BEFORE pj_write's call, so
     parse_noting is still ahead there.
   - crt_at_L0, crt_at_L0_B, crt_at_L3_B, crt_at_C_B: parse_noting is spent too and nothing budgeted is ahead, so
     kb = 66, spelled prh_wk F_check_round_trip.
   - crt_at_J, crt_at_J_B (and crt_at_X, crt_at_X_B, through them): the rewrite's end (C -> X) enters at 66 and QF is
     at 66, so kb = 66 and the tail lands by identity. The C3 exit (t not an object) enters at 64, after rtt2: a STEP
     UP, 64 <= 66, not an identity, sound because wbudget is an upper bound; it gives up only room, and from J on
     nothing asks for room. ---- *)

(* J (+0x340): the JOIN. Reached by C1 (rtt1 = 1), C2 (rtt2 = 1), C3 (not an object) and X (the rewrite's end).
   a0 = &copy is about to be handed to pj_free; s6 holds the value the function returns. Whatever the arms left in
   `copy` is a FREEABLE tree over Dc, and the counters are the arm's. *)
Record crt_at_J (fxk : YK11.FPState) (lyc : alayout) (Sc : astate) (Hpc : list Z) (Wc : world SEGS)
  (memc : word -> option byte) (mdc : Model) (kj pos : Z) (Lamc : list (Z * Z)) (peakc cntc ownc ranc : Z)
  (Dc : list (Z * Z)) (rg : bvmap 5 word) (r : Z) : Prop := mk_crt_at_J {
  (* `Dc` IS the invariant's `Dx` at this point: the blocks the arm holds beyond the entry's, which are exactly
     the ones pj_free is about to give back. The three relations (Lamc, ablocks, apartness from the document)
     come from crt_live, so they are maintained segment by segment rather than rebuilt here. *)
  crt_at_J_live : crt_live (prh_wk F_check_round_trip) lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cntc ownc ranc;
  (* THE FLOAT STATE the arms reached. QF is fpostFbm = apost_base_xbF at the Section's fx, so the tail has to give
     frm_zero and fregs_kept_x for the state it returns in; pj_free, __asan_set_shadow_f5, the flag store and the
     epilogue leave the f registers alone, so the value is the one the arm's last call (aj_call_xF / aj_call_xbF)
     left. Only the arm knows it (by transitivity over the calls it made), so the boundary carries it. (Crt102Arms'
     finding.) *)
  crt_at_J_frm_zero : frm_zero (@YK11.fp_csr fxk);
  crt_at_J_fregs : fregs_kept_x fx fxk;
  crt_at_J_bregs : crt_bregs rg (frame_addr lyc CRT_CID pos);
  crt_at_J_ret : getr rg 22 = w64 r;
  crt_at_J_copy_fd : pj_fdR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) DOC_D
    (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) Dc;
  (* THE COUNT at the join. On C4a and C4c the arm has already run pj_set, whose allocation count is the `cset` of
     QT, so the r = 1 bound is `ck_crt_count t cset`, NOT `ck_crt_count t 0`: pj_set's absent-and-taken arm makes
     c = 1, or 3 when n = cap, and its refused arm 1 <= c <= 3 (Crt102Rewrite's finding). C1, C2 and C3 take
     cset = 0. The side condition is QT's own, carried here so the tail hands it over unchanged. *)
  (* commit 6557b95928b5: THE r = 1 ARM IS DEAD (QT now states r = 0; the callees' texts state their refusal
     arms dead under prh_cons_from). Stated as the text states it: `r = 0 /\` in front, the old disjunction kept
     so a producer's r = 0 case is unchanged; every r = 1 exit (C1, C2, C4a, C4c) must be shown UNREACHABLE at its
     source, from the callee text's dead refusal arm. *)
  crt_at_J_r0 : r = 0;
  crt_at_J_count :
  exists cset, 0 <= cset <= 3 /\ (forall ms, t = PjTree.JObj ms -> In ck_MOD_AT (map fst ms) -> cset = 0) /\
   ((r = 1 /\ (ownc = 1 \/ ranc = 1) /\ cnt <= cntc <= cnt + ck_crt_count t cset) \/
    (r = 0 /\ ownc = 0 /\ ranc = ran /\ cntc = cnt + ck_crt_count t cset /\
     (* the room position on the r = 0 arm only: pj_free (&copy) is all that is left of round_trip *)
     crt_pos Sc crt_evs_J /\
     (* the tree `copy` holds, named, with its block layout and depth (Crt102Tail's finding, the walk owner's yes):
        tpj_free_specX keys its run events on that tree through prhPj_free_evs_supply / PRH_PjOrder.pj_free_fo,
        which need pj_nodeR, the block sizes against tblk (UP TO PERMUTATION - no ordered block fact exists) and the
        depth bound; pj_fdR alone names the pointer, not the tree.
        True of the binary: on C3 copy holds rtt1's read-back of t, on C4-full the pj_set result copy_set ms. *)
     pj_nodeR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) crt_tree_J Dc /\
     Permutation (map (fun b => snd b + cf_head) Dc) (PresetReqAtNoMiss.tblk crt_tree_J) /\
     (* copy's FREE ORDER, ORDERED (the walk owner's freeze; consumer: the A' tail's pj_free (&copy) at +0x344, whose
        position transfer reads HBulk in order - cf_frees_follow / quar_fifo_cf). A FREE list, so ordered; only the
        BLOCK list (tblk) is multiset-only. *)
     (exists Fc, PRH_PjOrder.pj_foR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) DOC_D
        (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) Dc Fc /\
      map (fun b => snd b + cf_head) Fc = PresetReqAt.fo crt_tree_J) /\
     (PjTree.depth crt_tree_J <= DOC_D)%nat)) }.

(* J on B' (PROPOSAL, see crt_bregs_B): crt_at_J with crt_bregs_B and the value the function returns in s5 *)
Record crt_at_J_B (fxk : YK11.FPState) (lyc : alayout) (Sc : astate) (Hpc : list Z) (Wc : world SEGS)
  (memc : word -> option byte) (mdc : Model) (kj pos : Z) (Lamc : list (Z * Z)) (peakc cntc ownc ranc : Z)
  (Dc : list (Z * Z)) (rg : bvmap 5 word) (r : Z) : Prop := mk_crt_at_J_B {
  crt_at_J_B_live : crt_live (prh_wk F_check_round_trip) lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cntc ownc ranc;
  crt_at_J_B_frm_zero : frm_zero (@YK11.fp_csr fxk);
  crt_at_J_B_fregs : fregs_kept_x fx fxk;
  crt_at_J_B_bregs : crt_bregs_B rg (frame_addr lyc CRT_CID pos);
  crt_at_J_B_ret : getr rg 21 = w64 r;
  crt_at_J_B_copy_fd : pj_fdR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) DOC_D
    (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) Dc;
  crt_at_J_B_r0 : r = 0;
  crt_at_J_B_count :
  exists cset, 0 <= cset <= 3 /\ (forall ms, t = PjTree.JObj ms -> In ck_MOD_AT (map fst ms) -> cset = 0) /\
   ((r = 1 /\ (ownc = 1 \/ ranc = 1) /\ cnt <= cntc <= cnt + ck_crt_count t cset) \/
    (r = 0 /\ ownc = 0 /\ ranc = ran /\ cntc = cnt + ck_crt_count t cset /\
     crt_pos Sc crt_evs_J /\
     pj_nodeR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) crt_tree_J Dc /\
     Permutation (map (fun b => snd b + cf_head) Dc) (PresetReqAtNoMiss.tblk crt_tree_J) /\
     (exists Fc, PRH_PjOrder.pj_foR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) DOC_D
        (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) Dc Fc /\
      map (fun b => snd b + cf_head) Fc = PresetReqAt.fo crt_tree_J) /\
     (PjTree.depth crt_tree_J <= DOC_D)%nat)) }.

(* X (+0x304): the shared re-poison of back and v, entered from C4a, C4c and the end of the rewrite. Same state as
   J but the two locals' shadow is still unpoisoned and `back` holds no tree (C4a / C4c) or was just freed (C4). *)
Record crt_at_X (fxk : YK11.FPState) (lyc : alayout) (Sc : astate) (Hpc : list Z) (Wc : world SEGS)
  (memc : word -> option byte) (mdc : Model) (kj pos : Z) (Lamc : list (Z * Z)) (peakc cntc ownc ranc : Z)
  (Dc : list (Z * Z)) (rg : bvmap 5 word) (r : Z) : Prop := mk_crt_at_X {
  crt_at_X_join : crt_at_J fxk lyc Sc Hpc Wc memc mdc kj pos Lamc peakc cntc ownc ranc Dc rg r;
  (* back and v are open: their 56-byte windows are addressable and hold no live block *)
  crt_at_X_back_open : range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF
    (frame_addr lyc CRT_CID pos + CRT_OFF_BACK) 56;
  crt_at_X_v_open : range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF
    (frame_addr lyc CRT_CID pos + CRT_OFF_V) 56 }.

(* X on B' (+0x30c): crt_at_X with crt_at_J -> crt_at_J_B, byte-equal otherwise. The flag is x21 on B'
   (`addi s5, zero, 1` at +0x290; row CRT-B-UGKO1's decode), which crt_at_J_B carries. *)
Record crt_at_X_B (fxk : YK11.FPState) (lyc : alayout) (Sc : astate) (Hpc : list Z) (Wc : world SEGS)
  (memc : word -> option byte) (mdc : Model) (kj pos : Z) (Lamc : list (Z * Z)) (peakc cntc ownc ranc : Z)
  (Dc : list (Z * Z)) (rg : bvmap 5 word) (r : Z) : Prop := mk_crt_at_X_B {
  crt_at_X_B_join : crt_at_J_B fxk lyc Sc Hpc Wc memc mdc kj pos Lamc peakc cntc ownc ranc Dc rg r;
  (* back and v are open: their 56-byte windows are addressable and hold no live block *)
  crt_at_X_B_back_open : range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF
    (frame_addr lyc CRT_CID pos + CRT_OFF_BACK) 56;
  crt_at_X_B_v_open : range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF
    (frame_addr lyc CRT_CID pos + CRT_OFF_V) 56 }.

(* U (+0x1e4): the head of the INLINED round_trip_rewrite, reached from T when doc->type is PJ_OBJECT. Both
   round_trip_text calls have returned 0, so `copy` holds the compact read-back tree over Db and the count is the
   two calls'. Agreed between Crt102Arms (which produces it) and Crt102Rewrite (which consumes it). *)
Record crt_at_U (fxk : YK11.FPState) (lyc : alayout) (Sc : astate) (Hpc : list Z) (Wc : world SEGS)
  (memc : word -> option byte) (mdc : Model) (kj pos : Z) (Db Lamc : list (Z * Z)) (peakc cntc : Z)
  (rg : bvmap 5 word) (ms : list (list Z * PjTree.jv)) : Prop := mk_crt_at_U {
  crt_at_U_live : crt_live (prh_wk F_round_trip_text + prh_wk F_round_trip_text)%nat lyc Sc Hpc Wc memc mdc kj pos Db
    Lamc peakc cntc 0 ran;
  crt_at_U_frm_zero : frm_zero (@YK11.fp_csr fxk);
  crt_at_U_fregs : fregs_kept_x fx fxk;
  crt_at_U_dregs : crt_dregs rg (frame_addr lyc CRT_CID pos);
  crt_at_U_obj : t = PjTree.JObj ms;
  crt_at_U_tree_ok : ck_tree_ok lyc Sc Lamc Wc memc doc t D;
  crt_at_U_copy : crt_copy_tree Wc memc Lamc (frame_addr lyc CRT_CID pos) t Db;
  (* the read-back's blocks, as round_trip_text's r = 0 arm names them *)
  crt_at_U_db_fresh : forall a k, In (a, k) Db -> ~ In (a - cf_head, k + cf_head) (ablocks B ly S);
  crt_at_U_db_lsz : Permutation (map snd Db) (map Z.of_nat (ReaderRes.lsz (PjRoundTrip.ttrace t)));
  crt_at_U_db_nlive : Z.of_nat (length Db) = ReaderRes.nlive (PjRoundTrip.ttrace t);
  crt_at_U_cnt : cntc = cnt + PjWriteHyp.wcalls t false + Z.of_nat (PjRoundTrip.tcalls t) +
               PjWriteHyp.wcalls t true + Z.of_nat (PjRoundTrip.tcalls t);
  (* the room position: both round_trip_text calls are done (rtt2's own pj_free (&back) included), the rewrite and
     pj_free (&copy) are left *)
  crt_at_U_pos : crt_pos Sc (crt_evs_U ms);
  (* copy's blocks against tblk t UP TO PERMUTATION (Crt102Rewrite's GAP R5; restated from the ordered form 2026-10-29,
     the walk owner's order): the model ties the live set to the run only up to permutation, and the reader's
     allocation order differs from tblk's pre-order, so no ordered block fact is available at any instance.
     Writer-side: copy at U holds rtt1's read-back of wdoc t false (PresetFreeFo.rd_blocks_wdoc + fo_tblk give the
     permutation, commit 407db1d16e7). This Permutation does NOT fix the header's cap (counterexample at crt_at_U_B). *)
  crt_at_U_copy_tblk : Permutation (map (fun b => snd b + cf_head) Db) (PresetReqAtNoMiss.tblk t);
  (* copy's HEADER CAP, the A' twin of crt_at_U_B's (consumer: Crt102Rewrite's pj_set (&copy, ..) at A' +0x278 via
     prhPj_set_evs_supply, PRH_FnPj:549-552; producer: Crt102Arms from round_trip_text's copy arm, CAP) *)
  crt_at_U_copy_cap : forall ty num str kids keys n cap,
     pj_hdrR SEGS (mrestrict (w_H Wc) memc) (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) ty num str kids keys n cap ->
     cap = Z.of_nat (PresetReqAt.ncap (length ms));
  (* copy's ORDERED FREE LIST at U, in the EXACT shape of the kit's tpj_set_specX ordered entry premise on its object
     (commit cdde0ed15730, PRH_FnPj 838c63d8cd16:999-1002) at o = copy, D = Db (the walk owner's
     yes 2026-10-30, on this walk's finding: the batch's pj_set takes it, and U carried none). CONSUMERS: the rewrite's
     pj_set (&copy, ..) - Crt102Rewrite (A'), row T3 (B'). PRODUCER: rtt1's copy arm, tround_trip_text_specX's
     ordered conjunct (FREEORD-COPY; kit PRH_FnCheck 909d5290d0ba:1289-1293) with PresetFreeFo.pj_frees_wdoc_t -
     Crt102Arms (A'), row T2 (B'). *)
  crt_at_U_copy_fo : cf_head = PresetReqAt.HEAD -> forall nn, (PjTree.depth (PjTree.JObj ms) <= nn)%nat ->
     exists F, PRH_PjOrder.pj_foR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) nn
       (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) Db F /\
     map (fun b => snd b + cf_head) F = PresetReqAt.fo (PjTree.JObj ms) }.

(* U on B' (+0x1ec): crt_at_U with crt_dregs -> crt_dregs_B, byte-equal otherwise. On B' doc is x22 (s6, from
   `mv x22, a0` at +0x60), x21 holds 1 (`addi x21, x0, 1` at +0x1b4), x23 is F (`mv x23, a0` at +0x70) and x27 the
   shadow base (`ld x27, 0(a1)` at +0x5c) - the word-by-word decode of row CRT-B-UGKO1. *)
Record crt_at_U_B (fxk : YK11.FPState) (lyc : alayout) (Sc : astate) (Hpc : list Z) (Wc : world SEGS)
  (memc : word -> option byte) (mdc : Model) (kj pos : Z) (Db Lamc : list (Z * Z)) (peakc cntc : Z)
  (rg : bvmap 5 word) (ms : list (list Z * PjTree.jv)) : Prop := mk_crt_at_U_B {
  crt_at_U_B_live : crt_live (prh_wk F_round_trip_text + prh_wk F_round_trip_text)%nat lyc Sc Hpc Wc memc mdc kj pos Db
    Lamc peakc cntc 0 ran;
  crt_at_U_B_frm_zero : frm_zero (@YK11.fp_csr fxk);
  crt_at_U_B_fregs : fregs_kept_x fx fxk;
  crt_at_U_B_dregs : crt_dregs_B rg (frame_addr lyc CRT_CID pos);
  crt_at_U_B_obj : t = PjTree.JObj ms;
  crt_at_U_B_tree_ok : ck_tree_ok lyc Sc Lamc Wc memc doc t D;
  crt_at_U_B_copy : crt_copy_tree Wc memc Lamc (frame_addr lyc CRT_CID pos) t Db;
  (* the read-back's blocks, as round_trip_text's r = 0 arm names them *)
  crt_at_U_B_db_fresh : forall a k, In (a, k) Db -> ~ In (a - cf_head, k + cf_head) (ablocks B ly S);
  crt_at_U_B_db_lsz : Permutation (map snd Db) (map Z.of_nat (ReaderRes.lsz (PjRoundTrip.ttrace t)));
  crt_at_U_B_db_nlive : Z.of_nat (length Db) = ReaderRes.nlive (PjRoundTrip.ttrace t);
  crt_at_U_B_cnt : cntc = cnt + PjWriteHyp.wcalls t false + Z.of_nat (PjRoundTrip.tcalls t) +
               PjWriteHyp.wcalls t true + Z.of_nat (PjRoundTrip.tcalls t);
  crt_at_U_B_pos : crt_pos Sc (crt_evs_U ms);
  crt_at_U_B_copy_tblk : Permutation (map (fun b => snd b + cf_head) Db) (PresetReqAtNoMiss.tblk t);
  (* copy's HEADER CAP (the walk owner's order, for T3's pj_set supply prhPj_set_evs_supply, PRH_FnPj:549-552). Not
     derivable from the Permutation and pj_nodeR - the CRT-B-UGKO1 counterexample: ms = [(key, JStr s)], |key| = 55,
     |s| = 7, tblk = [464; 80; 72; 24], ncap 1 = 8; a copy with header cap = 1, kids / keys blocks 72 / 24 and string
     blocks 448 / 64 satisfies pj_nodeR, the Permutation, the lsz permutation and length Db = nlive, with cap = 1 <> 8;
     pj_cstrR bounds a string block only from below. Producer: T2, from round_trip_text's copy arm (CAP, pj_ncapR). *)
  crt_at_U_B_copy_cap : forall ty num str kids keys n cap,
     pj_hdrR SEGS (mrestrict (w_H Wc) memc) (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) ty num str kids keys n cap ->
     cap = Z.of_nat (PresetReqAt.ncap (length ms));
  (* copy's ORDERED FREE LIST at U, crt_at_U_copy_fo's B' twin (same text). Consumer row T3, producer row T2. *)
  crt_at_U_B_copy_fo : cf_head = PresetReqAt.HEAD -> forall nn, (PjTree.depth (PjTree.JObj ms) <= nn)%nat ->
     exists F, PRH_PjOrder.pj_foR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) nn
       (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) Db F /\
     map (fun b => snd b + cf_head) F = PresetReqAt.fo (PjTree.JObj ms) }.

(* ---- the rewritten tree, its pretty text and g_count at pj_write's entry (Crt102Loops' names, landed here so the
   rewrite and the loop slices share one spelling): the two round_trip_text counts, pj_string's strdup, pj_set's cset ---- *)
Definition crt_tc : PjTree.jv := ck_crt_tree t.
Definition crt_wP : list (list Z) := WriterValue.wdpieces crt_tc true.
Definition crt_tb : list Z := WriterValue.wdoc crt_tc true.
Definition crt_cw (cset : Z) : Z :=
  cnt + PjWriteHyp.wcalls t false + Z.of_nat (PjRoundTrip.tcalls t) +
  PjWriteHyp.wcalls t true + Z.of_nat (PjRoundTrip.tcalls t) + 1 + cset.

(* L0 (+0x470): O2's two tests fell through (g_own_ran_out = 0 and fuzz_alloc_ran_out () = 0), s6 is 1 when pj_write
   returned NULL and `snez rc` otherwise, s8 = saved. The two callee outcomes are FORWARDED as pj_write's and
   parse_noting's posts give them, and the loop slice does the deduction that kills the property abort of new:740.
   Agreed between Crt102Rewrite (which produces it) and Crt102Loops (which consumes it). *)
Record crt_at_L0 (fxk : YK11.FPState) (lyc : alayout) (Sc : astate) (Hpc : list Z) (Wc : world SEGS)
  (memc : word -> option byte) (mdc : Model) (kj pos : Z) (Dc Dx Lamc : list (Z * Z)) (peakc cntc : Z)
  (rg : bvmap 5 word) (ms : list (list Z * PjTree.jv)) (cset saved rc : Z) : Prop := mk_crt_at_L0 {
  crt_at_L0_obj : t = PjTree.JObj ms;
  crt_at_L0_frm_zero : frm_zero (@YK11.fp_csr fxk);
  crt_at_L0_fregs : fregs_kept_x fx fxk;
  (* `Dx` is what the invariant holds at L0 and `Dc` only what `copy` owns: on the saved <> 0 branch the walk also
     holds pj_write's buffer and, on the Some arm, the read-back's blocks, so `Dx = Dc` is FALSE there and
     crt_at_L0 would be unproducible on the C4-full path (Crt102Rewrite's finding, agreed with Crt102Loops). The
     two Permutations that used to sit on the Some arm are crt_live's. *)
  crt_at_L0_live : crt_live (prh_wk F_check_round_trip) lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc 0 0;
  crt_at_L0_dregs : crt_dregs rg (frame_addr lyc CRT_CID pos);
  crt_at_L0_saved : getr rg 24 = w64 saved;
  crt_at_L0_flag : getr rg 22 = w64 (if saved =? 0 then 1 else if rc =? 0 then 0 else 1);
  crt_at_L0_sp_back : crt_spill Wc memc CRT_SP_BACK (frame_addr lyc CRT_CID pos + CRT_OFF_BACK);
  crt_at_L0_sp_shn : crt_spill Wc memc CRT_SP_SHN (shadow_addr (doc + PJ_OFF_N));
  crt_at_L0_sp_pn : crt_spill Wc memc CRT_SP_PN (doc + PJ_OFF_N);
  crt_at_L0_sp_n : crt_spill Wc memc CRT_SP_N (Z.of_nat (length ms));
  crt_at_L0_doc_align : doc mod 8 = 0;
  crt_at_L0_doc_open : range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF doc 56;
  crt_at_L0_back_open : range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF
    (frame_addr lyc CRT_CID pos + CRT_OFF_BACK) 56;
  crt_at_L0_v_open : range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF
    (frame_addr lyc CRT_CID pos + CRT_OFF_V) 56;
  crt_at_L0_cset_range : 0 <= cset <= 3;
  crt_at_L0_cset_mod : In ck_MOD_AT (map fst ms) -> cset = 0;
  crt_at_L0_copy : pj_nodeR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc)
    (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) crt_tc Dc;
  crt_at_L0_copy_fd : pj_fdR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) DOC_D
    (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) Dc;
  (* copy's blocks against tblk UP TO PERMUTATION and its depth - the J field's copy facts, produced by the rewrite from
     pj_set's post and carried to J by the loops (Crt102Loops' finding; the B' twin carries the same so T5 can hand them
     to crt_at_L3_B, as the approved T5-T7 seam fix requires). WRITER-SIDE. *)
  crt_at_L0_copy_tblk : Permutation (map (fun b => snd b + cf_head) Dc) (PresetReqAtNoMiss.tblk crt_tree_J);
  (* copy's free order, ordered - beside the copy Permutation, outside the arm split: it comes from pj_set's post,
     before pj_write, so it holds on every arm *)
  crt_at_L0_copy_fo : exists Fc, PRH_PjOrder.pj_foR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) DOC_D
     (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) Dc Fc /\
   map (fun b => snd b + cf_head) Fc = PresetReqAt.fo crt_tree_J;
  crt_at_L0_copy_depth : (PjTree.depth crt_tree_J <= DOC_D)%nat;
  (* THE OUTCOME: pj_write's and parse_noting's posts, forwarded; ONE field, the arms a disjunction inside it *)
  crt_at_L0_outcome :
  exists ok : list bool,
  let st' := PRH_FnWriter.prhWriter_putN ok (WriterApp.w0 (crt_cw cset) SIZE_MAXZ) crt_wP in
  (* commit 3ac20a5c9e30: prh_oks ok cnt fail k ns most ran ran' - ns = the call's per-call user requests;
     tpj_write_specX's form verbatim (PRH_FnWriter 98737c36ea08:738) *)
  prh_oks ok (crt_cw cset) SIZE_MAXZ
    (PRH_FnWriter.prhWriter_k ok (WriterApp.w0 (crt_cw cset) SIZE_MAXZ) crt_wP)
    (PRH_FnWriter.prhWriter_reqs ok (WriterApp.w0 (crt_cw cset) SIZE_MAXZ) crt_wP) most 0 0 /\
  ((saved = 0 /\ WriterApp.w_failed st' <> 0 /\ Dx = Dc) \/
   (saved <> 0 /\ WriterApp.w_failed st' = 0 /\
    exists (okr : list bool) (res : option PjTree.jv) (tr : list PjGrammar.ev),
      PjGrammar.jr_run ReaderRes.jr_strtod crt_tb okr = (res, tr) /\
      (* tparse_noting_specX's form verbatim (PRH_FnCheck 0844ed8c0608:668) *)
      prh_oks okr (WriterApp.w_cnt st') SIZE_MAXZ (PjGrammar.calls tr) (prh_ev_reqs tr) most 0 0 /\
      cntc = WriterApp.w_cnt st' + Z.of_nat (PjGrammar.calls tr) /\
      (SIZE_MAXZ < WriterApp.w_cnt st' \/ WriterApp.w_cnt st' + ck_ncalls crt_tb <= SIZE_MAXZ ->
         res = ck_read crt_tb /\ Z.of_nat (PjGrammar.calls tr) = ck_ncalls crt_tb) /\
      match res with
      | Some tv => rc = 0 /\
          (* the room position, on this arm only (pj_write and the reading were granted): fuzz_free (saved),
             pj_free (&back) and pj_free (&copy) are left *)
          crt_pos Sc (crt_evs_L0 ms) /\ exists Dback,
          Dx = Dback ++ (saved, WriterApp.w_cap st') :: Dc /\
          pj_nodeR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) (frame_addr lyc CRT_CID pos + CRT_OFF_BACK) tv Dback /\
          (* back's blocks against tblk crt_tc UP TO PERMUTATION: back is the read-back of wdoc crt_tc true
             (writer-side; the T5-T7 seam fix, restated to the permutation form, twinned on A') *)
          Permutation (map (fun b => snd b + cf_head) Dback) (PresetReqAtNoMiss.tblk crt_tc) /\
          (* back's free order, the A' twin of crt_at_L0_B's (same text; Crt102Loops' finding: the exit's
             pj_free (&back) needs it; Crt102Rewrite produces it at parse_noting's return, FREEORD) *)
          (exists Fb, PRH_PjOrder.pj_foR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) DOC_D
             (frame_addr lyc CRT_CID pos + CRT_OFF_BACK) Dback Fb /\
           map (fun b => snd b + cf_head) Fb = PresetReqAt.fo crt_tc)
      | None => rc = -1 /\ Dx = (saved, WriterApp.w_cap st') :: Dc
      end)) }.

(* L0 on B' (+0x478): crt_at_L0 with crt_dregs -> crt_dregs_B, the flag in x21 instead of x22 (B' N +0x2ec is
   `snez s5, a0` = `sltu s5, zero, a0`, and +0x47c tests `bnez s5`; the decode in the B' binary, row
   CRT-B-RRT), and the three B' spill constants; byte-equal otherwise. `saved` stays in x24 (B' +0x2bc `mv s8, a0`)
   and `&back` stays at 0x38(s1) (B' +0x2a8 `sd a0, 0x38(s1)`), so CRT_SP_BACK is shared. *)
Record crt_at_L0_B (fxk : YK11.FPState) (lyc : alayout) (Sc : astate) (Hpc : list Z) (Wc : world SEGS)
  (memc : word -> option byte) (mdc : Model) (kj pos : Z) (Dc Dx Lamc : list (Z * Z)) (peakc cntc : Z)
  (rg : bvmap 5 word) (ms : list (list Z * PjTree.jv)) (cset saved rc : Z) : Prop := mk_crt_at_L0_B {
  crt_at_L0_B_obj : t = PjTree.JObj ms;
  crt_at_L0_B_frm_zero : frm_zero (@YK11.fp_csr fxk);
  crt_at_L0_B_fregs : fregs_kept_x fx fxk;
  crt_at_L0_B_live : crt_live (prh_wk F_check_round_trip) lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc 0 0;
  crt_at_L0_B_dregs : crt_dregs_B rg (frame_addr lyc CRT_CID pos);
  crt_at_L0_B_saved : getr rg 24 = w64 saved;
  crt_at_L0_B_flag : getr rg 21 = w64 (if saved =? 0 then 1 else if rc =? 0 then 0 else 1);
  crt_at_L0_B_sp_back : crt_spill Wc memc CRT_SP_BACK (frame_addr lyc CRT_CID pos + CRT_OFF_BACK);
  crt_at_L0_B_sp_shn : crt_spill Wc memc CRT_SP_SHN_B (shadow_addr (doc + PJ_OFF_N));
  crt_at_L0_B_sp_pn : crt_spill Wc memc CRT_SP_PN_B (doc + PJ_OFF_N);
  crt_at_L0_B_sp_n : crt_spill Wc memc CRT_SP_N_B (Z.of_nat (length ms));
  crt_at_L0_B_doc_align : doc mod 8 = 0;
  crt_at_L0_B_doc_open : range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF doc 56;
  crt_at_L0_B_back_open : range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF
    (frame_addr lyc CRT_CID pos + CRT_OFF_BACK) 56;
  crt_at_L0_B_v_open : range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF
    (frame_addr lyc CRT_CID pos + CRT_OFF_V) 56;
  crt_at_L0_B_cset_range : 0 <= cset <= 3;
  crt_at_L0_B_cset_mod : In ck_MOD_AT (map fst ms) -> cset = 0;
  crt_at_L0_B_copy : pj_nodeR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc)
    (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) crt_tc Dc;
  crt_at_L0_B_copy_fd : pj_fdR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) DOC_D
    (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) Dc;
  crt_at_L0_B_copy_tblk : Permutation (map (fun b => snd b + cf_head) Dc) (PresetReqAtNoMiss.tblk crt_tree_J);
  crt_at_L0_B_copy_fo : exists Fc, PRH_PjOrder.pj_foR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) DOC_D
     (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) Dc Fc /\
   map (fun b => snd b + cf_head) Fc = PresetReqAt.fo crt_tree_J;
  crt_at_L0_B_copy_depth : (PjTree.depth crt_tree_J <= DOC_D)%nat;
  crt_at_L0_B_outcome :
  exists ok : list bool,
  let st' := PRH_FnWriter.prhWriter_putN ok (WriterApp.w0 (crt_cw cset) SIZE_MAXZ) crt_wP in
  prh_oks ok (crt_cw cset) SIZE_MAXZ
    (PRH_FnWriter.prhWriter_k ok (WriterApp.w0 (crt_cw cset) SIZE_MAXZ) crt_wP)
    (PRH_FnWriter.prhWriter_reqs ok (WriterApp.w0 (crt_cw cset) SIZE_MAXZ) crt_wP) most 0 0 /\
  ((saved = 0 /\ WriterApp.w_failed st' <> 0 /\ Dx = Dc) \/
   (saved <> 0 /\ WriterApp.w_failed st' = 0 /\
    exists (okr : list bool) (res : option PjTree.jv) (tr : list PjGrammar.ev),
      PjGrammar.jr_run ReaderRes.jr_strtod crt_tb okr = (res, tr) /\
      prh_oks okr (WriterApp.w_cnt st') SIZE_MAXZ (PjGrammar.calls tr) (prh_ev_reqs tr) most 0 0 /\
      cntc = WriterApp.w_cnt st' + Z.of_nat (PjGrammar.calls tr) /\
      (SIZE_MAXZ < WriterApp.w_cnt st' \/ WriterApp.w_cnt st' + ck_ncalls crt_tb <= SIZE_MAXZ ->
         res = ck_read crt_tb /\ Z.of_nat (PjGrammar.calls tr) = ck_ncalls crt_tb) /\
      match res with
      | Some tv => rc = 0 /\ crt_pos Sc (crt_evs_L0 ms) /\ exists Dback,
          Dx = Dback ++ (saved, WriterApp.w_cap st') :: Dc /\
          pj_nodeR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) (frame_addr lyc CRT_CID pos + CRT_OFF_BACK) tv Dback /\
          Permutation (map (fun b => snd b + cf_head) Dback) (PresetReqAtNoMiss.tblk crt_tc) /\
          (* back's FREE ORDER, ORDERED (the walk owner's freeze, the T5-T7 seam's text): back is a read-back of the
             writer's own text, so its free list is fo crt_tc (PresetFreeFo.pj_frees_wdoc_t, proved); iface_room_pos
             reads the free history in order (cf_frees_follow), so a permutation would not carry the position. Produced
             at parse_noting's return (tparse_noting_specX's free-order conjunct, FREEORD) by T5. *)
          (exists Fb, PRH_PjOrder.pj_foR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) DOC_D
             (frame_addr lyc CRT_CID pos + CRT_OFF_BACK) Dback Fb /\
           map (fun b => snd b + cf_head) Fb = PresetReqAt.fo crt_tc)
      | None => rc = -1 /\ Dx = (saved, WriterApp.w_cap st') :: Dc
      end)) }.

(* W on B' (+0x2a4): crt_at_U_B carried through U, G, K, O1 - pj_string (&v, STAMP) = 0 and pj_set (&copy, MOD_AT, &v)
   = 0, so `set` = 1 and `copy` holds the rewritten tree crt_tc over the blocks Dc it owns; O1's two flag tests fell
   through (g_own_ran_out = 0, fuzz_alloc_ran_out () = 0); s5 = 1 (+0x290); s10 = O1's auipc (+0x288), whose + 0x2d0
   is g_own_ran_out; the U spills; the count at pj_write's entry crt_cw cset; the room used so far (Crt102Model's
   cm_live_write `b'` premise). WRITTEN in row T4 (commit 33b3e227271, lib/B/Prog/Crt102B_T4.v:215-236) and CHECKED
   conjunct by conjunct against the B' listing by row CRT-B-UGKO1 (which
   produces this state). Landed with exactly one substitution, `crt_dregsB` -> the frozen `crt_dregs_B` (the T4
   copies of the register snapshots are deleted by the unit owner's ruling: equal only by permutation); its local
   notations liveB / spillB / cwB / tcB are the glue's own crt_live / crt_spill / crt_cw / crt_tc, and
   `@pi_g_own_ran_out prh_img_B` is pi_g_own_ran_out at the ambient PrhImg (= prh_img_B at the B' instance). *)
Record crt_at_W_B (fxk : YK11.FPState) (lyc : alayout) (Sc : astate) (Hpc : list Z) (Wc : world SEGS)
  (memc : word -> option byte) (mdc : Model) (kj pos : Z) (Dc Lamc : list (Z * Z)) (peakc cntc : Z)
  (rg : bvmap 5 word) (ms : list (list Z * PjTree.jv)) (cset : Z) : Prop := mk_crt_at_W_B {
  crt_at_W_B_obj : t = PjTree.JObj ms;
  crt_at_W_B_frm_zero : frm_zero (@YK11.fp_csr fxk);
  crt_at_W_B_fregs : fregs_kept_x fx fxk;
  crt_at_W_B_live : crt_live (prh_wk F_round_trip_text + prh_wk F_round_trip_text)%nat lyc Sc Hpc Wc memc mdc kj pos Dc
    Lamc peakc cntc 0 0;
  crt_at_W_B_dregs : crt_dregs_B rg (frame_addr lyc CRT_CID pos);
  crt_at_W_B_s5 : getr rg 21 = w64 1;
  crt_at_W_B_s10_own : getr rg 26 = w64 (pi_g_own_ran_out - CRT_OWN_LO_B);
  crt_at_W_B_sp_shn : crt_spill Wc memc CRT_SP_SHN_B (shadow_addr (doc + PJ_OFF_N));
  crt_at_W_B_sp_pn : crt_spill Wc memc CRT_SP_PN_B (doc + PJ_OFF_N);
  crt_at_W_B_sp_n : crt_spill Wc memc CRT_SP_N_B (Z.of_nat (length ms));
  crt_at_W_B_doc_align : doc mod 8 = 0;
  crt_at_W_B_doc_open : range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF doc 56;
  crt_at_W_B_back_open : range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF
    (frame_addr lyc CRT_CID pos + CRT_OFF_BACK) 56;
  crt_at_W_B_v_open : range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF
    (frame_addr lyc CRT_CID pos + CRT_OFF_V) 56;
  crt_at_W_B_cset_range : 0 <= cset <= 3;
  crt_at_W_B_cset_mod : In ck_MOD_AT (map fst ms) -> cset = 0;
  crt_at_W_B_cnt : cntc = crt_cw cset;
  crt_at_W_B_copy : pj_nodeR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc)
    (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) crt_tc Dc;
  crt_at_W_B_tree_vis : PRH_FnWriter.prhWriter_tree_vis Wc memc Dc;
  crt_at_W_B_live_bound : YCbq.bsum (ck_hblks Dc) <= LIVE_round_trip_text t false + LIVE_round_trip_text t true +
    PRH_FnPj.LIVE_pj_string (Z.of_nat (length ck_STAMP)) +
    PRH_FnPj.LIVE_pj_set (ck_members t) (ck_members t) (Z.of_nat (length ck_MOD_AT));
  (* the room position (2026-10-29): pj_string and pj_set were granted, so set_evs is done; pj_write,
     the reading, fuzz_free (saved), pj_free (&back) and pj_free (&copy) are left *)
  crt_at_W_B_pos : crt_pos Sc (crt_evs_W ms);
  (* copy's blocks against tblk UP TO PERMUTATION and its depth (the walk owner's order: W_B must carry them, since T4's
     frozen start has only pj_nodeR .. copy crt_tc Dc and L0_B's copy conjunct is otherwise an obligation nobody can
     discharge). PRODUCER: T3's pj_set (tpj_set_specX's post gives it on both granted arms, under cf_head = HEAD, Dw =
     [(a, 21)], 21 + 16 = 37 = tblk (JStr MOD_VAL)); T4 threads it W -> Wr -> S -> L0. The cf_head guard is written as the
     texts write it; under CfParams_preset it is reflexivity, so L0_B's unguarded conjunct follows. WRITER-SIDE. *)
  crt_at_W_B_copy_tblk : cf_head = PresetReqAt.HEAD ->
     Permutation (map (fun b => snd b + cf_head) Dc) (PresetReqAtNoMiss.tblk crt_tree_J);
  (* copy's free order, ordered (produced by T3's pj_set) *)
  crt_at_W_B_copy_fo : exists Fc, PRH_PjOrder.pj_foR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) DOC_D
     (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) Dc Fc /\
   map (fun b => snd b + cf_head) Fc = PresetReqAt.fo crt_tree_J;
  crt_at_W_B_copy_depth : (PjTree.depth crt_tree_J <= DOC_D)%nat }.

(* ---- THE SEAM STATEMENTS for the B' loop tail (rows T5 = CRT-B-L012, T6 = CRT-B-L3, T7 = CRT-B-CEXIT),
   WRITTEN in row T6 (commit 62d39032031, lib/B/Prog/Crt102SeamB.v blob efaa8f4f71e4, #102 pins
   type-check rc=0, log, the internal file zf-fuzz-preset-62d3903203.build-20261029T155901Z.log) and landed VERBATIM; its local
   notations LIVE / BREGS / SPILL / TC / XB / L0B / QFB / CFG are the glue's crt_live / crt_bregs_B / crt_spill /
   crt_tc / crt_at_X_B / crt_at_L0_B / QF / crt_cfg at this Section's binders. Its `bi` section (the instantiation at
   prh_img_B / B_prog_listing) stays in its own file: the glue imports no image.
   B' cuts: L0 +0x478 -> L1 +0x4f8 -> L2 +0x56c -> L3 +0x5b4 -> C +0x6f8 (also from +0x584 when doc->n = 0) -> the
   exit +0x80c `j` X (+0x30c). T5 = L0 -> {L3 (i = 0, doc->n > 0), C (doc->n = 0)}; T6 = L3 -> C; T7 = C -> X. *)

(* L3 on B' (+0x5b4), the MEMBER-LOOP HEAD at index i: T5's post (i = 0) and T6's invariant. Reached from L2's
   fall-through (+0x5b0, doc->n > 0) and from the back edge `bltu s5, a0` (+0x6f4). The new:740 abort is gone
   (saved <> 0, rc = 0), the read-back is the rewritten tree (back holds crt_tc over Dback), `at` is cm_at ms and
   back.n = doc->n + (at = doc->n) has been tested (new:748). The count is QT's r = 0 count in closed form, so T6 and
   T7 carry it unchanged. The walk holds Dx = Dback ++ (saved, kw) :: Dc. Registers (B'): s5 (x21) = i, s8 (x24) =
   8 i, s10 (x26) = 56 i, s6 (x22) = shadow (&doc->keys); doc is no longer in a register (s6 is overwritten at
   +0x59c), so crt_bregs_B, not crt_dregs_B. *)
Record crt_at_L3_B (fxk : YK11.FPState) (lyc : alayout) (Sc : astate) (Hpc : list Z) (Wc : world SEGS)
  (memc : word -> option byte) (mdc : Model) (kj pos : Z) (Dc Dback Lamc : list (Z * Z)) (peakc cntc : Z)
  (rg : bvmap 5 word) (ms : list (list Z * PjTree.jv)) (cset saved kw : Z) (i : nat) : Prop := mk_crt_at_L3_B {
  crt_at_L3_B_obj : t = PjTree.JObj ms;
  crt_at_L3_B_frm_zero : frm_zero (@YK11.fp_csr fxk);
  crt_at_L3_B_fregs : fregs_kept_x fx fxk;
  crt_at_L3_B_live : crt_live (prh_wk F_check_round_trip) lyc Sc Hpc Wc memc mdc kj pos (Dback ++ (saved, kw) :: Dc)
    Lamc peakc cntc 0 0;
  crt_at_L3_B_bregs : crt_bregs_B rg (frame_addr lyc CRT_CID pos);
  crt_at_L3_B_s5_i : getr rg 21 = w64 (Z.of_nat i);
  crt_at_L3_B_s8_i : getr rg 24 = w64 (8 * Z.of_nat i);
  crt_at_L3_B_s10_i : getr rg 26 = w64 (56 * Z.of_nat i);
  crt_at_L3_B_s6_keys : getr rg 22 = w64 (shadow_addr (doc + PJ_OFF_KEYS));
  crt_at_L3_B_sp_saved : crt_spill Wc memc CRT_SP_SAVED_B saved;
  crt_at_L3_B_sp_shkids : crt_spill Wc memc CRT_SP_SHKIDS_B (shadow_addr (doc + PJ_OFF_KIDS));
  crt_at_L3_B_sp_keys : crt_spill Wc memc CRT_SP_KEYS_B (doc + PJ_OFF_KEYS);
  crt_at_L3_B_sp_back : crt_spill Wc memc CRT_SP_BACK (frame_addr lyc CRT_CID pos + CRT_OFF_BACK);
  crt_at_L3_B_sp_at : crt_spill Wc memc CRT_SP_AT_B (Z.of_nat (cm_at ms));
  crt_at_L3_B_sp_kids : crt_spill Wc memc CRT_SP_KIDS_B (doc + PJ_OFF_KIDS);
  crt_at_L3_B_sp_shn : crt_spill Wc memc CRT_SP_SHN_B (shadow_addr (doc + PJ_OFF_N));
  crt_at_L3_B_sp_pn : crt_spill Wc memc CRT_SP_PN_B (doc + PJ_OFF_N);
  crt_at_L3_B_doc_align : doc mod 8 = 0;
  crt_at_L3_B_doc_open : range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF doc 56;
  crt_at_L3_B_back_open : range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF
    (frame_addr lyc CRT_CID pos + CRT_OFF_BACK) 56;
  crt_at_L3_B_v_open : range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF
    (frame_addr lyc CRT_CID pos + CRT_OFF_V) 56;
  crt_at_L3_B_i_lt : (i < length ms)%nat;
  crt_at_L3_B_cset_range : 0 <= cset <= 3;
  crt_at_L3_B_cset_mod : In ck_MOD_AT (map fst ms) -> cset = 0;
  crt_at_L3_B_cnt : cntc = cnt + ck_crt_count t cset;
  crt_at_L3_B_saved_nz : saved <> 0;
  crt_at_L3_B_copy : pj_nodeR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc)
    (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) crt_tc Dc;
  crt_at_L3_B_copy_fd : pj_fdR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) DOC_D
    (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) Dc;
  crt_at_L3_B_back : pj_nodeR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc)
    (frame_addr lyc CRT_CID pos + CRT_OFF_BACK) crt_tc Dback;
  (* the room position (2026-10-29): the loops make no allocator event, so L0's suffix stands *)
  crt_at_L3_B_pos : crt_pos Sc (crt_evs_L0 ms);
  (* the T5-T7 seam fix (approved by the walk owner, 2026-10-29; block facts restated to the permutation form): pj_write's
     buffer size, back's and copy's blocks against tblk up to permutation (both WRITER-SIDE), and the copy facts the
     J field needs - carried through T5 / T6 unchanged *)
  crt_at_L3_B_kw : kw = last (PresetReqAt.wcaps (PresetReqAt.copy_set ms) true) 0;
  crt_at_L3_B_back_tblk : Permutation (map (fun b => snd b + cf_head) Dback) (PresetReqAtNoMiss.tblk crt_tc);
  (* back's free order, carried from L0 (the loops touch neither back nor the allocator; T6 carries it) *)
  crt_at_L3_B_back_fo : exists Fb, PRH_PjOrder.pj_foR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) DOC_D
     (frame_addr lyc CRT_CID pos + CRT_OFF_BACK) Dback Fb /\
   map (fun b => snd b + cf_head) Fb = PresetReqAt.fo crt_tc;
  crt_at_L3_B_copy_tblk : Permutation (map (fun b => snd b + cf_head) Dc) (PresetReqAtNoMiss.tblk crt_tree_J);
  crt_at_L3_B_copy_fo : exists Fc, PRH_PjOrder.pj_foR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) DOC_D
     (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) Dc Fc /\
   map (fun b => snd b + cf_head) Fc = PresetReqAt.fo crt_tree_J;
  crt_at_L3_B_copy_depth : (PjTree.depth crt_tree_J <= DOC_D)%nat }.

(* C on B' (+0x6f8), the FINAL-CHECKS ENTRY: T6's post and T7's pre (and T5's post when doc->n = 0, by `beqz a3`
   +0x584). The member compares of new:750-755 have all passed; C reads only &back (0x38), at (0x40), saved (0(s1))
   and the shadow base (x27). No loop register is carried. *)
Record crt_at_C_B (fxk : YK11.FPState) (lyc : alayout) (Sc : astate) (Hpc : list Z) (Wc : world SEGS)
  (memc : word -> option byte) (mdc : Model) (kj pos : Z) (Dc Dback Lamc : list (Z * Z)) (peakc cntc : Z)
  (rg : bvmap 5 word) (ms : list (list Z * PjTree.jv)) (cset saved kw : Z) : Prop := mk_crt_at_C_B {
  crt_at_C_B_obj : t = PjTree.JObj ms;
  crt_at_C_B_frm_zero : frm_zero (@YK11.fp_csr fxk);
  crt_at_C_B_fregs : fregs_kept_x fx fxk;
  crt_at_C_B_live : crt_live (prh_wk F_check_round_trip) lyc Sc Hpc Wc memc mdc kj pos (Dback ++ (saved, kw) :: Dc)
    Lamc peakc cntc 0 0;
  crt_at_C_B_bregs : crt_bregs_B rg (frame_addr lyc CRT_CID pos);
  crt_at_C_B_sp_saved : crt_spill Wc memc CRT_SP_SAVED_B saved;
  crt_at_C_B_sp_back : crt_spill Wc memc CRT_SP_BACK (frame_addr lyc CRT_CID pos + CRT_OFF_BACK);
  crt_at_C_B_sp_at : crt_spill Wc memc CRT_SP_AT_B (Z.of_nat (cm_at ms));
  crt_at_C_B_back_open : range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF
    (frame_addr lyc CRT_CID pos + CRT_OFF_BACK) 56;
  crt_at_C_B_v_open : range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF
    (frame_addr lyc CRT_CID pos + CRT_OFF_V) 56;
  crt_at_C_B_cset_range : 0 <= cset <= 3;
  crt_at_C_B_cset_mod : In ck_MOD_AT (map fst ms) -> cset = 0;
  crt_at_C_B_cnt : cntc = cnt + ck_crt_count t cset;
  crt_at_C_B_saved_nz : saved <> 0;
  crt_at_C_B_copy : pj_nodeR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc)
    (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) crt_tc Dc;
  crt_at_C_B_copy_fd : pj_fdR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) DOC_D
    (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) Dc;
  crt_at_C_B_back : pj_nodeR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc)
    (frame_addr lyc CRT_CID pos + CRT_OFF_BACK) crt_tc Dback;
  crt_at_C_B_pos : crt_pos Sc (crt_evs_L0 ms);
  crt_at_C_B_kw : kw = last (PresetReqAt.wcaps (PresetReqAt.copy_set ms) true) 0;
  crt_at_C_B_back_tblk : Permutation (map (fun b => snd b + cf_head) Dback) (PresetReqAtNoMiss.tblk crt_tc);
  (* back's free order, carried to C (T7 projects it for pj_free (&back)) *)
  crt_at_C_B_back_fo : exists Fb, PRH_PjOrder.pj_foR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) DOC_D
     (frame_addr lyc CRT_CID pos + CRT_OFF_BACK) Dback Fb /\
   map (fun b => snd b + cf_head) Fb = PresetReqAt.fo crt_tc;
  crt_at_C_B_copy_tblk : Permutation (map (fun b => snd b + cf_head) Dc) (PresetReqAtNoMiss.tblk crt_tree_J);
  crt_at_C_B_copy_fo : exists Fc, PRH_PjOrder.pj_foR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) DOC_D
     (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) Dc Fc /\
   map (fun b => snd b + cf_head) Fc = PresetReqAt.fo crt_tree_J;
  crt_at_C_B_copy_depth : (PjTree.depth crt_tree_J <= DOC_D)%nat }.

(* the stretch statements (rows T5-T7): from any state a cut describes, at any float state, QF, at the re-hiding
   move's step relation YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf (QF's journal is at wle') *)
Definition CRT_B_AT_X : Prop :=
  forall fxk lyc Sc Hpc Wc memc mdc kj pos Lamc peakc cntc ownc ranc Dc rg r,
  crt_at_X_B fxk lyc Sc Hpc Wc memc mdc kj pos Lamc peakc cntc ownc ranc Dc rg r ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (crt_cfg fxk CRT_X_OFF rg memc mdc) QF.
Definition CRT_B_AT_C : Prop :=
  forall fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg ms cset saved kw,
  crt_at_C_B fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg ms cset saved kw ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (crt_cfg fxk CRT_C_OFF rg memc mdc) QF.
Definition CRT_B_AT_L3 : Prop :=
  forall fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg ms cset saved kw i,
  crt_at_L3_B fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg ms cset saved kw i ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (crt_cfg fxk CRT_L3_OFF rg memc mdc) QF.
Definition CRT_B_AT_L0 : Prop :=
  forall fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dx Lamc peakc cntc rg ms cset saved rcd,
  crt_at_L0_B fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dx Lamc peakc cntc rg ms cset saved rcd ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (crt_cfg fxk CRT_L0_OFF rg memc mdc) QF.
(* the three rows: each takes the statements of the cuts its segment reaches *)
Definition CRT_B_SEG_T5 : Prop := CRT_B_AT_L3 -> CRT_B_AT_C -> CRT_B_AT_L0.
Definition CRT_B_SEG_T6 : Prop := CRT_B_AT_C -> CRT_B_AT_L3.
Definition CRT_B_SEG_T7 : Prop := CRT_B_AT_X -> CRT_B_AT_C.

Local Unset Implicit Arguments.

End g.
End f.
End w.

(* ---- THE CAP BRIDGE (the walk owner's ruling 2026-10-30: committed, named, proved). The kit states copy's header
   cap on rtt1's copy arm as PRH_Reader.pj_ncapR segs m copy t (commit cdde0ed15730:
   PRH_FnCheck 909d5290d0ba:1295-1299, pj_ncapR at PRH_Reader.v:243); the glue's field crt_at_U_copy_cap /
   crt_at_U_B_copy_cap is the pj_hdrR form. pj_ncapR's OBJECT clause is
     `rd_u64 m (p + 48) (Z.of_nat (PresetReqAt.ncap (length members))) /\ exists kids, ..`,
   so the field follows from that clause's first conjunct by crt_copy_cap_of_ncap48 below: pj_hdrR's last conjunct
   reads the same eight bytes as `cap`, and rd_u64 has one value. pj_ncapR is on this base (PRH_Reader.v:243,
   Required at :92); the bridge is stated over its object clause, and its users take the cap word from pj_ncapR
   with `cbn [pj_ncapR]` first (Crt102Arms.v:864-866 arms_rtt_bridge; Crt102B_RRT.v:2012-2013 crtb_rrt).
   crt_rdword_of_vm is Crt102KitB.cb4_rdword_of_val_mem's statement and proof, copied (the glue cannot import a
   file that imports it). Proves no function; rule 24: no function proved. ---- *)
Lemma crt_rdword_of_vm : forall sg (Hh : word -> bool) m0 a v,
  val_mem sg (mrestrict Hh m0) a 8 v -> 0 <= v < 2 ^ 64 -> rdword (aview sg Hh m0) a = Some v.
Proof.
intros sg Hh m0 a v Hv Hr.
assert (Bk : forall k, (k < 8)%nat -> aview sg Hh m0 (a + Z.of_nat k) = Some (le_byte v 8 k)).
{ intros k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold le_byte. apply Z.mod_mod. lia. }
unfold rdword.
rewrite <- (Z.add_0_r a) at 1. change 0 with (Z.of_nat 0) at 1. rewrite (Bk 0%nat) by lia.
change 1 with (Z.of_nat 1). rewrite (Bk 1%nat) by lia. change 2 with (Z.of_nat 2) at 1. rewrite (Bk 2%nat) by lia.
change 3 with (Z.of_nat 3). rewrite (Bk 3%nat) by lia. change 4 with (Z.of_nat 4). rewrite (Bk 4%nat) by lia.
change 5 with (Z.of_nat 5). rewrite (Bk 5%nat) by lia. change 6 with (Z.of_nat 6). rewrite (Bk 6%nat) by lia.
change 7 with (Z.of_nat 7). rewrite (Bk 7%nat) by lia.
f_equal. apply le_bytes8. exact Hr.
Qed.

Lemma crt_rd_u64_det : forall sg (Hh : word -> bool) m0 a v1 v2,
  rd_u64 sg (mrestrict Hh m0) a v1 -> rd_u64 sg (mrestrict Hh m0) a v2 -> v1 = v2.
Proof.
intros sg Hh m0 a v1 v2 (R1 & V1) (R2 & V2).
pose proof (crt_rdword_of_vm sg Hh m0 a v1 V1 R1) as E1. rewrite (crt_rdword_of_vm sg Hh m0 a v2 V2 R2) in E1.
injection E1 as E1. symmetry. exact E1.
Qed.

Lemma crt_copy_cap_of_ncap48 : forall sg (Hh : word -> bool) m0 p (ms : list (list Z * PjTree.jv))
    ty num str kids keys n cap,
  rd_u64 sg (mrestrict Hh m0) (p + 48) (Z.of_nat (PresetReqAt.ncap (length ms))) ->
  pj_hdrR sg (mrestrict Hh m0) p ty num str kids keys n cap ->
  cap = Z.of_nat (PresetReqAt.ncap (length ms)).
Proof.
intros sg Hh m0 p ms ty num str kids keys n cap HN (_ & _ & _ & _ & _ & _ & _ & HC).
exact (crt_rd_u64_det sg Hh m0 (p + 48) cap _ HC HN).
Qed.
Print Assumptions crt_copy_cap_of_ncap48.
