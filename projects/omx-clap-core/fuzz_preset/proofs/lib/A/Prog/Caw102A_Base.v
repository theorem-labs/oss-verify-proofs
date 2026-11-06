(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: for omx-clap-core/fuzz_preset, the CALLER-WINDOW call kit over YCbqG.v's journal
   ajournal_x (allocator invariant a parameter ARx, ghost head set Hp after S, program statics PST), generic: no image
   class, no address, no ledger. Credit: WalkS4, lib/A/Prog/PRW_CallerJ.v at 85a188622c5 (statements and proofs taken
   from there; changes below). Donors there: cj_kept from cgif_file_fuzzer lib/YC20.v:311-325 tlzw_kept and
   lib/YC8n.v:272-287 tlzw_kept_of_journal (origin/release/pau-projects-recipes), generalised to ajournal_x's keep
   clauses; aj_call_xW from YCbqGcall.v aj_call_x (cgif YCbq.v:1845-1883 aj_call, origin/ossv/recipes).
   What a walk of a function in the caller-window form needs:
   - fwin_x / fpostW_x / fpostWF_x: lib/A/PRH_Base.v's fwin / fpostW / fpostWF (K0) restated with the image segs and
     the statics PST as parameters, same bodies: PRH_Base.fpostW B ARx SK STK d FP .. is
     fpostW_x (SK := SK) pa_segs B prh_pst ARx STK d FP .. by unfolding (this file does not Require lib/A).
   - START: ajournal_x_init_W, the widened journal (STK + e) (sp + e) at the entry state.
   - CALL of a caller-window callee: aj_call_xW / aj_call_xWF (callee state in mkst form), aj_call_xW_sp /
     aj_call_xWF_sp (the entry form of YCbqGcall.v's aj_call_x_sp: st_ok, ss_resv, the machine state ms).
     The footprint side condition is YCbqG.v's own fp_sub_x (h-hpreset-7 9052c7a7d74 :688-691), whose fourth
     disjunct `sp0 - STK <= a < sp0` is the caller's window: WalkS4's fp_sub_xW is that predicate, so this file
     no longer states one and ajournal_x_sub_W (the name WalkS4's callers use) is YCbqG's ajournal_x_sub.
   - vrd_call_W: h-verbs-3's lib/A/VrdArm.v call rule (6d4cddbdff5), premise shape kept, as a corollary of
     aj_call_xW_sp at e1 := - o.
   - aj_call_xWF_d: WalkH6's caller-window float call rule (h-walk-identity's S8aCallW.v aj_call_xWF), verbatim: no
     fwin_x for the callee and no window-kept clause on either side.
   - END: cj_kept (the keep clauses of ajournal_x relative to the entry, the walker's window and its written cells OR
     exempted) across stretches (cj_kept_exec) and calls (cj_kept_of_journal), chained (cj_kept_trans), closed by
     fpostW_x_of_kept / fpostWF_x_of_kept; fpostW_x_of_apost: apost_base_x is fpostW_x at e = 0.
   Numerals: 16, 4096, 8, 4 and 2 ^ 64 are LENGTH; 0 is LENGTH (the empty window e = 0) or DERIVED (event count);
   register numbers 1, 3, 4 (ra, gp, tp) are WORD. No address literal; no image constant. *)
(* Modified by Theorem Labs, 2026-10: the kit over a world relation R (suffix R). A free or realloc of a live block can
   hide shadow again, so a walk that crosses one proves YA0nH.SRrG at a relation wider than wle with its journal at that
   relation (YCbqG.v ajournal_xR). cj_keptR is cj_kept with the world conjunct R W W2 (a copy of the body; the guard
   cj_kept_R_wle shows by reflexivity that cj_kept is cj_keptR at wle). The R forms of cj_kept_refl / cj_kept_exec /
   ajournal_x_init_W take R and its reflexivity, of cj_kept_trans / ajournal_x_sub_W R and its transitivity, of
   cj_kept_of_journal / fpostW_x_of_apost / fpostW_x_of_kept / fpostWF_x_of_kept R alone; the call rules
   aj_call_xWR / aj_call_xW_spR / aj_call_xWFR / aj_call_xWF_spR / vrd_call_WR / aj_call_xWF_dR take R and both laws
   first, then the plain rule's binders, with the journals, the callee's post (fpostW_xR / fpostWF_xR) and the
   conclusion at R. Each plain lemma is its R form at wle (wle_refl / wle_trans); its statement is unchanged.
   fpostW_x_R_lift: a plain fpostW_x (journal at wle) is fpostW_xR at every R that contains wle. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Reusable/YCbqGcallW.v, with its module names changed; 482 of its 526 lines of code are new or changed and 767 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S4_PsFree.v, with its module paths and module names changed; 635 of its 689 lines of code are new or changed and 472 lines of the source are left out. *)
(* fuzz_preset lib/A, the #102 re-walk of check_as_written on image A' (ASan build): the SHARED BASE of the segment
   lemmas (lane CawA102, h-rw-pre-5). States only: the entry record, the text's premises, the cut predicates and the
   segment statements; the segment files Caw102A_WA*.v prove them.
   rule 24: no function proved. rule 24: proves no function (kind: segment lemma).
   THE IMAGE: A' = asan pin sha256 1be0f53d96cb9d6c (twin bff8519bbe3ea0e4, code equal over the function range).
   THE INPUTS, each BY PATH (lane's own copies, cited by blob):
  - listing of record: #102 listings v3 (owner 16:28Z), origin/cold/h-verbs-1-listing-pins102 74dcda1eda12,
    lib/A/Listing_prog.v 7ed1529926bd (the re-emit d42e123915ae's listing 1ab147923c5d, its header comment only
    changed) (lib/A/PAImg_prog.v 505a51ff7d08 is NOT Required: its PI_prog_A certificate checks the #102 image's
    bytes, which the cb base f65cfdd5cac0 does not carry; the walk is PARAMETRIC over {PA : PAImg A_prog_listing} and
    uses the listing's own tables, PL_caw_A below, the terms of PAImg_prog.v 47eeb54e93be :177-181; v3 pre-evaluates
    its A_prog_tpi, which is equal to PL_caw_A's ptree_of_list by computation), lib/Reusable/YPsym.v
    b6f5a85d234d. Slot check re-run on d42e123915ae (lane CawA102,
     13:2xZ): the 86 slots 630..715 are the twin's words except 13 relocation / call slots, all as the plan says
     (PHi 0x81fd4, PLdHi A_OBJ 0 0x81fd8, PCall __wrap_malloc 0x81ff4 / ex_value 0x82014 / __wrap_free 0x82020 /
     __asan_report_load1 0x82094 / __wrap_free 0x820a8 / fuzz_alloc_ran_out 0x820c4 / __asan_handle_no_return 0x82108 /
     abort 0x8210c, PHi 0x82028, PHi 0x820b4, PLdHi A_OBJ 13 (g_own_ran_out) SZ1 unsigned 0x820b8).
  - the kit (as this tree carries it; first prepared on the batch tip, lead 03:0xZ), its kit texts by
    path: lib/A/PRH_FnCheck.v (tcheck_as_written_specX :1313-1402, :832-902 in blob c40cf3fdcd2a: NO run-word list DW (the binder and
    prh_univ_closure's argument are gone, PRH_Base.v:1200-1243); the ROOM COUNTS `sec_cnt S <= LSEC + DRV` and
    `ccnt24 S <= L24 + DRV` as entry premises after room_live_cf S (PRH_FnCheck.v:1343-1344, tpadded_specX's spelling); a NEW post
    conjunct, THE OUTCOME (PRH_FnCheck.v:1379-1388): at any run position i at S whose next events are the scratch pair and whose
    allocation among them is a consumer event (PRH_Base.prh_cons_from .. i 2), r = 0 and S' is the position i + 2),
    PRH_Base.v (prh_univ_closure CTX0, prh_univ_closure_lit; prh_cons_from :435; the outcome note
    :336-371), PRH_FnEx.v, PRH_FnAlloc.v 4d8aeba047e5, PRH_Refute.v 23f7a37f01c9 (prh_refute_at: a granted
    NULL of the allocator at a consumer position is impossible, P8 at the instance through PresetCfnA), PRH_Img.v
    (the #102 integration line's, the #102 A' record), lib/Spec PresetRoomPosKeep.v (room_pos_keep_free takes the free's
    own `admits`), PresetFreeFo.v.
  - engine: the P'' set as the kit's cut carries it (lib/Reusable by path from that cut: YCbqG.v, the
    journal with the wild-trace budget, read through ajx_* and built by ajx_intro; YG01.v 845507e218b0, admits /
    admits_fix; YGcallMxmn.v 3c08bbab8292, the allocator rules with the `admits` call premise; YCbqGwild.v; YGcfNames.v;
    YGcfRoomLive.v, ...). Every image / start-up / generated file is the #102 integration line's.
  - base: the kit's cut, merged forward into this row's head (the
    record head, with the #102 integration line), this lane's files over it;
    the P'' trial's fixes (WA0..WA4) folded in. PRW_StepKit.v is the #102 integration line's.
   THE CODE (A' 0x81fb8, 86 instructions; DERIVED byte offsets from the entry; the entry is the listing's slot
   A_prog_slot AS_check_as_written = 630, never a typed address):
     +0    prologue: frame 80 (ra +72, s0 +64, s1 +56, s2 +48), s1 = doc, s0 = rc, a2 = the GOT word A_OBJ 0, a3 = end,
           s2 = the shadow base (A_OBJ 12), struct ex at sp + 8: p +8 = data, end +16, depth +24 = 0
     +60   jal __wrap_malloc (size + 1)                                    [WA0]
     +64   beqz a0 -> +112                                                 (the cut CAW_PC_NULL, WA1's, NOT this lane)
     +68   CAW_PC_X: a1 = rc == 0 ? doc : 0; scratch +32 = a0; differs +40 = 0; jal ex_value (+92)   [WA2]
     +96   beqz a0 -> +128; else free (scratch) at +104, j +248 (li s2, -1) -> +252
     +128  CAW_PC_R: the inlined ex_ws loop +160..+196 with its shadow test; __asan_report_load1 +220 REFUTED;
           sd p, free (scratch) +240, p == end ? (+328: lw s2, differs) : (+248: li s2, -1) -> +252   [WA3]
     +252  CAW_PC_OOM: lbu a0 <- g_own_ran_out; s1 = 1; a0 != 0 -> +300; jal fuzz_alloc_ran_out +268;
           a0 != 0 -> +300 (refuted: ran = 0)                               [WA4]
     +276  CAW_PC_CHK: (rc == 0) == (want < 0) -> abort (+336, REFUTED); s1 = 0; rc != 0 -> +300;
           want != 0 -> abort (REFUTED)                                    [WA5]
     +300  CAW_PC_END: a0 = s1; restore ra, s0, s1, s2; sp += 80; ret (+324)   [WA6]
   THE FORM (rulings 12:18Z-12:31Z, h-rw-pre-5 lane-102 brief): GENERIC P, abstract in every proof:
   `forall P, srr_inv_laws segs P -> [srr_inv_call segs P ->] [srr_inv_mn segs P ->] caw_seg_* P`, each caw_seg_*
   ending in SRr segs W c (fun W' c' => Q W' c' /\ P (ms_mem (cfg_ms c'))), its R form caw_seg_*R in YA0nH.SRrG segs R. CONTINUATION
   FORM (agreed with CawB102, the B' twin): every segment but the last takes, for each cut it reaches, the continuation at that cut
   for a generic final post Q; the last (WA6) ends in fpostF .. Qb for a generic post body Qb. The top composes them.
   THE ALLOCATOR: the cf instance, ARcfx := ARcf segs B /\ xs_placed_cf (FuzzFree.v / H2CawF.v / CawB102's choice),
   room_live_cf at a8's instance prh_room_live_a8 (YGcfRoomLive.room_live_room with the hull budget gives QM_cf at a call).
   g_own_ran_out / g_most: the kit's Batch 2 has LANDED (decff67d721f: prh_glob / prh_ledger carry most and own; the text's
   premise is `prh_ledger .. ran most 0` and its post `exists own', prh_ledger .. ran most own'`), so the threading this
   base carried since c3fe12bc7ff1 (caw_pst, from a Theorem Labs lane's own_load_flip / own_load_only_empty_cut) is removed by
   citation: EVERY cut carries `caw_ledger D .. own` LAST, the entry's ledger values with the record's most and the byte
   the cut holds (0 up to the NULL arm's store, ownv at CHK / END); prh_ledger_own / prh_ledger_most project it.
  THE RUN POSITION (the post-implication form; the cno B' base's cnb_prog shape, Cno102B_Base.v b5421fc37cbc :386 on
  a working branch 182081b57e58): the text binds no position at entry. So each cut carries
  caw_prog D E S for the events E made since entry: for ANY run position i at the entry state whose next events are
  E, a position i + length E of the cut's state. E = [] at caw_at_null (the refused malloc makes no event), caw_ev1 D =
  [HMal (size + 1)] at caw_at_X / caw_at_R, caw_evs D = [HMal (size + 1); HFr (size + 1)] at caw_at_OOM / caw_at_CHK,
  and per arm at caw_at_END (r = 1 with [], r = 0 with caw_evs D), which IS the text's post. (The cno shape's live-set
  conjunct is not taken: this text's post states no live set.)
  THE OUTCOME (the batch text's :879-888): the refused arm is DEAD under the run hypothesis. caw_dead D says it: at any
  run position i at the ENTRY state whose next events are caw_evs D and whose allocation is a consumer event
  (prh_cons_from .. i 2), the scratch was not refused. It is proved where the allocator's path is held, at WA0's NULL
  arm (PRH_Refute.prh_refute_at with the malloc's granted NULL path at the entry state, the malloc's own state), and
  carried, state-free, by caw_at_null and caw_at_END's r = 1 arm; the post's outcome conjunct follows from it there,
  and from caw_prog D (caw_evs D) on the r = 0 arm.
  THE ROOM COUNTS (CAW_CNT DISCHARGED BY CONVERSION): the batch text has them as entry premises (:862-863), the
  23rd / 24th conjuncts of caw_pre in the text's order; caw_cnt D is literally their conjunction, so caw_pre_cnt
  (Qed, a projection) gives it and the named argument CAW_CNT is gone. caw_carry still carries caw_cnt D (the
  malloc's and the free's RL steps read it). NO malloc / free keep argument: YGcallMxmnKeep's aj_malloc_x_ct_m_keep /
  aj_free_x_ct_m_rh_keep carry the memnorm keep (YGcallMxmn's plain rules state none since part 3c, YGcallMxmn.v:137-141).
  caw_pre is read BY NAME (caw_pre_* below, one projection per conjunct), never positionally.
   Numerals: offsets 0..336 are DERIVED (4 x slot inside the function); 80 / 72 / 64 / 56 / 48 / 40 / 32 / 24 / 16 / 8
   are LENGTHs (the frame and its slots, read off `addi sp, sp, -80` and the sd / ld immediates); register numbers
   1 2 3 4 8 9 10 11 12 13 18 19-27 (WORD); 2 ^ 31 / 2 ^ 62 / 2 ^ 64 / 3 * 2 ^ 20 the text's bounds. No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YI16 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG YGcfNames YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00cf YG01cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfAroBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
(* the generic-P carriers: srr_inv_laws in YC80x (14f84f225e8f), srr_inv_call / srr_inv_mn and the memnorm instances in
   YSRrMemnorm (5ffa8525936b) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PresetRoomPos PresetRun PresetReqAt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetLiveBounds.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Img PRH_Reader PRH_FnEx PRH_FnCheck.
(* the PLAIN build's sink instance is loaded transitively here; it must never fill an ASan sink argument *)
#[global] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the function's cut offsets (DERIVED byte offsets inside check_as_written, A' listing d42e123915ae) ---- *)
(* caw's slot in the listing: DERIVED, = A_prog_slot AS_check_as_written of PAImg_prog.v 505a51ff7d08 :419
   (A_entry_check_as_written); the image fact cwi_entry below ties it to pa_sigma *)
Definition CAW_SLOT : nat := 630.
Definition CAW_OFF : Z := 4 * Z.of_nat CAW_SLOT.
Definition CAW_FRAME : Z := 80.
Definition CAW_PC_X : Z := 68.       (* after the malloc, a0 <> 0: snez a1, s0 *)
Definition CAW_PC_NULL : Z := 112.   (* the malloc's NULL arm: auipc a0 (WA1's cut, not this lane's segment) *)
Definition CAW_PC_R : Z := 128.      (* ex_value read the value: ld a1, 8(sp) *)
Definition CAW_PC_REPORT : Z := 220. (* jal __asan_report_load1 (refuted) *)
Definition CAW_PC_OOM : Z := 252.    (* auipc a0; lbu a0 <- g_own_ran_out: s2 = want *)
Definition CAW_PC_CHK : Z := 276.    (* seqz a0, s0: the two property checks *)
Definition CAW_PC_END : Z := 300.    (* mv a0, s1: the epilogue *)
Definition CAW_PC_ABORT : Z := 336.  (* jal __asan_handle_no_return (refuted) *)
Lemma CAW_OFF_val : CAW_OFF = 2520.
Proof. vm_compute. reflexivity. Qed.
Lemma CAW_FRAME_val : pi_frame (PrhImg := prh_img_A) F_check_as_written = CAW_FRAME.
Proof. vm_compute. reflexivity. Qed.
(* the listing's own tables (PAImg_prog.v 47eeb54e93be :177-181, the same terms; Required from no file that checks the
   #102 image's bytes): the engine's vm_compute needs a closed table, so the walk's PL is PL_caw_A *)
Definition A_prog_tpi_caw : ptree asym := ptree_of_list A_prog_listing.
Definition A_prog_tw_caw : ctable := Eval vm_compute in (tw_of 0 A_prog_listing).
Definition PL_caw_A : PAListing A_prog_listing :=
{| pl_tpi := A_prog_tpi_caw; pl_tpi_eq := eq_refl; pl_tw := A_prog_tw_caw; pl_tw_eq := ltac:(vm_compute; reflexivity);
pl_lim := ltac:(vm_compute; reflexivity); pl_len := ltac:(vm_compute; discriminate); pl_slot0 := ltac:(vm_compute; exact I) |}.

Section cw. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Context {PA : PAImg A_prog_listing}.
(* the image's generated per-function data (PRH_Img.v, #102 pins), the listing's tables, and a8's room instance,
   bound ONCE here *)
#[local] Instance CW_PrhImg : PrhImg := prh_img_A.
#[local] Instance CW_PAListing : PAListing A_prog_listing := PL_caw_A.
#[local] Instance CW_RL : PrhRoomLive := prh_room_live_a8.
#[local] Notation segs := (@pa_segs _ A_prog_listing PA).
#[local] Notation VAL := (@pa_val _ A_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable SK : YI16.sink_head.
Variable CTX0 : list (list Z).
(* the allocator relation of the walk (S1KitAlloc's ARxs, YGcallcf.v): ARcf with the error-buffer extents placed *)
Definition ARcfx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop :=
  fun ly S Hp W mem md => ARcf segs B ly S Hp W mem md /\ xs_placed_cf ly S.

(* ---- THE IMAGE FACTS the walk reads of PA (and, cwi_pst_ok / cwi_pst_errno, of the runtime symbols B: so caw_img
   takes B, `caw_img (PA := PA) B`), each proved at the instance by computation (PAImg_prog.v's
   A_entry_check_as_written, A_prog_val, A_alias_hints_ok, and the re-emitted object pin 13 = g_own_ran_out) ---- *)
Record caw_img : Prop := {
  cwi_base : BASE = A_prog_base;
  cwi_entry : SIGMA AS_check_as_written = BASE + CAW_OFF;
  cwi_own : VAL (A_OBJ 13) = pi_g_own_ran_out;
  (* the program-written statics are writable image bytes, outside the read-only view (CawA102WA4's finding: the
     journal exempts prh_pst from its image clause, so without this a callee could move a read-only byte and
     arodata_okP would not cross the call); at the instance by computation on prh_pst and the segments *)
  cwi_pst_rw : forall a, Exists (in_zr a) prh_pst -> ~ in_roP segs (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) a;
  (* the program-written statics are image bytes (CawA102WA3's finding: the runtime rules keep a byte off the owned
     statics and errno only when it is in_img; S1ImgA.pst_in_img_A's form, at the instance by computation) *)
  cwi_pst_img : forall a, Exists (in_zr a) prh_pst -> in_img segs a;
  (* the image's objects lie below the image top (CawA102WA0's finding: the GOT word A_OBJ 0 and the shadow cell
     A_OBJ 12 must be apart from the frame for the entry state; pa_obj_img bounds them by the abstract pa_hi only);
     at the instance pa_hi is IMG_TOP (PAImg_prog.v 505a51ff7d08 :408) *)
  cwi_hi : @pa_hi _ _ PA <= YImgTop.IMG_TOP;
  (* the hi / lo pair of WA1's `sb s1, 1304(a0)` at +120 (a PW slot the certificate checks as a word only): the alias
     row (SOff (A_HI 11) 1304, SOff (A_OBJ 13) 0) of Listing_prog.v 7ed1529926bd :7283, i.e. the byte g_own_ran_out;
     at the instance by PAImg_prog.v 505a51ff7d08 A_alias_hints_ok (a Theorem Labs lane's WA1 wa1i_hi11, the cno base's cni_hi9) *)
  cwi_hi11 : VAL (A_HI 11) + 1304 = VAL (A_OBJ 13);
  (* a program static is a byte its segment holds, so with cwi_pst_rw it is writable_at for every memory (h-rw-sta-6's
     WA1 wa1i_pst_seg, the cno base's cni_pst_seg, S1ImgA.v pst_wv_A's fact); at the instance by computation *)
  cwi_pst_seg : forall a, Exists (in_zr a) prh_pst -> YK11.seg_rom segs (Z_to_bv 64 a) <> None;
  (* the mixed-write runner's PST_ok (YCbqG.v :755): a store to a program static is a store to an image byte the
     runtime does not own (a Theorem Labs lane's WA1 wa1i_pst_ok, the cno base's cni_pst_ok, FuzzFree.v :386-403's pal_pst_ok
     form); it reads B, so it is proved where B is bound, by computation [a Theorem Labs lane] *)
  cwi_pst_ok : forall a, Exists (in_zr a) prh_pst -> in_img segs a /\ ~ Exists (in_zr a) (as_owned_static B);
  (* the program statics are apart from errno: the runtime __wrap_free rows keep g_own_ran_out / g_most only given it
     (YCbq.v acall_kept's image clause exempts errno, which api_env puts inside the image); the A' twin of the cno
     base's cni_pst_errno (Cno102A_Base.v 2aede65f76e5 :158, cold/h-rw-pre-5-cno102a-r 41dfdb047827). Closed by
     vm_compute at the instance [a Theorem Labs lane, where B is bound] *)
  cwi_pst_errno : forall a, Exists (in_zr a) prh_pst -> ~ (as_errno B <= a < as_errno B + 4);
  (* ---- THE cf LAYER'S RELRO ROWS (lib/Reusable/YG0ncf.v relro_seg_t / errno_relro_t, YGcfAroBridge.v
     ro_reads_nw_t), the cno base's cni_relro_seg / cni_errno_relro / cni_relro_top / cni_relro_eq / cni_ro_reads_nw:
     what the allocator call's memory premise QMm_cf asks of the image (arodata_ok_cf, through
     YGcfAroBridge.arodata_ok_cf_of_P from the walk's reader form arodata_okP over pa_relro_lo / pa_relro_hi). At the
     instance by lib/A/CfAroPresetA.v's relro_seg_preset_A / errno_relro_preset_A / relro_top_preset_A /
     ro_reads_nw_preset_A, and the range equation by computation ---- *)
  cwi_relro_seg : YG0ncf.relro_seg_t segs;
  cwi_errno_relro : YG0ncf.errno_relro_t B;
  cwi_relro_top : cf_relro_hi <= 2 ^ 64;
  cwi_relro_eq : cf_relro_lo = @pa_relro_lo _ _ PA /\ cf_relro_hi = @pa_relro_hi _ _ PA;
  cwi_ro_reads_nw : YGcfAroBridge.ro_reads_nw_t segs
}.

Definition caw_pc (o : Z) : Z := BASE + CAW_OFF + o.

(* ---- THE ENTRY DATA: every binder of tcheck_as_written_specX (PRH_FnCheck.v c40cf3fdcd2a :833 @7cdbb61b5fa0) ---- *)
Record caw_in : Type := mkCawIn {
  cw_ly : alayout; cw_S : astate; cw_Hp : list Z; cw_W : world segs;
  cw_regs : bvmap 5 word; cw_mem : word -> option byte; cw_md : Model; cw_ch : list (Z * Z * Z);
  cw_data : Z; cw_x : list Z; cw_rc : Z; cw_doc : Z; cw_t : PjTree.jv; cw_D : list (Z * Z);
  cw_Lam : list (Z * Z); cw_peak : Z; cw_cnt : Z; cw_fail : Z; cw_ran : Z; cw_most : Z
}.
Definition cw_size (D : caw_in) : Z := Z.of_nat (length (cw_x D)).
Definition cw_sp0 (D : caw_in) : Z := spZ (cw_regs D).

(* ---- tcheck_as_written_specX's 27 premises (PRH_FnCheck.v:1316-1363), at one record, in the text's order (the run-word
   list DW is gone from prh_univ_closure, :1322; the room counts :1343-1344, the hull budget :1349 and HPOS :1359-1362 are new) ---- *)
Definition caw_pre (D : caw_in) : Prop :=
  fpre B ARcfx STK_check_as_written (cw_ly D) (cw_S D) (cw_Hp D) (cw_W D) (cw_regs D) (cw_mem D) (cw_md D) (cw_ch D) /\
  YAkMemnorm.memnorm segs (cw_mem D) /\
  prh_univ_closure B CTX0 /\
  getr (cw_regs D) 10 = w64 (cw_data D) /\ getr (cw_regs D) 11 = w64 (cw_size D) /\
  getr (cw_regs D) 12 = w64 (cw_rc D) /\ getr (cw_regs D) 13 = w64 (cw_doc D) /\
  - 2 ^ 31 <= cw_rc D < 2 ^ 31 /\ 0 <= cw_doc D < 2 ^ 64 /\
  cw_size D <= 3 * 2 ^ 20 /\ 0 < cw_data D /\ cw_data D + cw_size D < 2 ^ 62 /\
  src_rd (cw_W D) (cw_mem D) (cw_data D) (cw_x D) /\
  (0 < cw_size D -> PRH_FnEx.prhex_inblk B (cw_ly D) (cw_S D) (cw_Hp D) (cw_data D) (cw_size D)) /\
  (cw_rc D = 0 /\ ck_read (cw_x D) = Some (cw_t D) \/ cw_rc D <> 0 /\ ck_read (cw_x D) = None) /\
  (cw_rc D = 0 -> ck_tree_ok (cw_ly D) (cw_S D) (cw_Lam D) (cw_W D) (cw_mem D) (cw_doc D) (cw_t D) (cw_D D)) /\
  prh_ledger B (cw_ly D) (cw_S D) (cw_Hp D) (cw_W D) (cw_mem D) (cw_Lam D) (cw_peak D) (cw_cnt D) (cw_fail D) (cw_ran D)
    (cw_most D) 0 /\
  cw_ran D = 0 /\
  blocks_bytes (cw_S D) + LIVE_check_as_written (cw_size D) <= LIVE_MAX /\ cw_size D + 1 < cf_malloc_max /\
  Z.of_nat (length (frames (cw_S D))) <= ck_FRAMES_CAP - FR_check_as_written /\
  room_live_cf (cw_S D) /\
  YGcfRoomLive.sec_cnt (cw_S D) <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV /\
  YGcfRoomLive.ccnt24 (cw_S D) <= PresetLiveBounds.L24 + PresetLiveBounds.DRV /\
  (* the hull budget of the scratch pair and the run position at entry (HPOS): the text's two premises before
     ck_frm0, in its spelling *)
  PresetHullBudget.hull_budget (cw_S D) [PresetReqAt.HMal (cw_size D + 1); PresetReqAt.HFr (cw_size D + 1)] /\
  (exists (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option nat)) (rp_i : nat)
     (rp_H0 : list Z) (rp_hist : list YG00.chunk),
     (length rp_os <= 4)%nat /\ PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist (cw_S D) /\
     PRH_Base.prh_run_at rp_sm rp_x rp_os rp_i [PresetReqAt.HMal (cw_size D + 1)]) /\
  ck_frm0.

(* ---- caw_pre BY NAME: one projection per conjunct, in the text's order (a consumer cites these, never a
   positional pattern over caw_pre) ---- *)
Section pre_proj.
Variable D : caw_in.
Hypothesis HP : caw_pre D.
Lemma caw_pre_fpre :
  fpre B ARcfx STK_check_as_written (cw_ly D) (cw_S D) (cw_Hp D) (cw_W D) (cw_regs D) (cw_mem D) (cw_md D) (cw_ch D).
Proof. destruct HP as (H & _). exact H. Qed.
Lemma caw_pre_mn : YAkMemnorm.memnorm segs (cw_mem D).
Proof. destruct HP as (_ & H & _). exact H. Qed.
Lemma caw_pre_univ : prh_univ_closure B CTX0.
Proof. destruct HP as (_ & _ & H & _). exact H. Qed.
Lemma caw_pre_r10 : getr (cw_regs D) 10 = w64 (cw_data D).
Proof. destruct HP as (_ & _ & _ & H & _). exact H. Qed.
Lemma caw_pre_r11 : getr (cw_regs D) 11 = w64 (cw_size D).
Proof. destruct HP as (_ & _ & _ & _ & H & _). exact H. Qed.
Lemma caw_pre_r12 : getr (cw_regs D) 12 = w64 (cw_rc D).
Proof. destruct HP as (_ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma caw_pre_r13 : getr (cw_regs D) 13 = w64 (cw_doc D).
Proof. destruct HP as (_ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma caw_pre_rc : - 2 ^ 31 <= cw_rc D < 2 ^ 31.
Proof. destruct HP as (_ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma caw_pre_doc : 0 <= cw_doc D < 2 ^ 64.
Proof. destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma caw_pre_size : cw_size D <= 3 * 2 ^ 20.
Proof. destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma caw_pre_data0 : 0 < cw_data D.
Proof. destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma caw_pre_data62 : cw_data D + cw_size D < 2 ^ 62.
Proof. destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma caw_pre_src : src_rd (cw_W D) (cw_mem D) (cw_data D) (cw_x D).
Proof. destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma caw_pre_inblk : 0 < cw_size D -> PRH_FnEx.prhex_inblk B (cw_ly D) (cw_S D) (cw_Hp D) (cw_data D) (cw_size D).
Proof. destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma caw_pre_case : cw_rc D = 0 /\ ck_read (cw_x D) = Some (cw_t D) \/ cw_rc D <> 0 /\ ck_read (cw_x D) = None.
Proof. destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma caw_pre_tree :
  cw_rc D = 0 -> ck_tree_ok (cw_ly D) (cw_S D) (cw_Lam D) (cw_W D) (cw_mem D) (cw_doc D) (cw_t D) (cw_D D).
Proof. destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma caw_pre_ledger : prh_ledger B (cw_ly D) (cw_S D) (cw_Hp D) (cw_W D) (cw_mem D) (cw_Lam D) (cw_peak D) (cw_cnt D)
  (cw_fail D) (cw_ran D) (cw_most D) 0.
Proof. destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma caw_pre_ran : cw_ran D = 0.
Proof. destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma caw_pre_live : blocks_bytes (cw_S D) + LIVE_check_as_written (cw_size D) <= LIVE_MAX.
Proof. destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma caw_pre_max : cw_size D + 1 < cf_malloc_max.
Proof. destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma caw_pre_frames : Z.of_nat (length (frames (cw_S D))) <= ck_FRAMES_CAP - FR_check_as_written.
Proof. destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma caw_pre_room : room_live_cf (cw_S D).
Proof.
destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H.
Qed.
Lemma caw_pre_sec : YGcfRoomLive.sec_cnt (cw_S D) <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV.
Proof.
destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _).
exact H.
Qed.
Lemma caw_pre_c24 : YGcfRoomLive.ccnt24 (cw_S D) <= PresetLiveBounds.L24 + PresetLiveBounds.DRV.
Proof.
destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _).
exact H.
Qed.
Lemma caw_pre_hull :
  PresetHullBudget.hull_budget (cw_S D) [PresetReqAt.HMal (cw_size D + 1); PresetReqAt.HFr (cw_size D + 1)].
Proof.
destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _).
exact H.
Qed.
Lemma caw_pre_hpos :
  exists (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option nat)) (rp_i : nat)
    (rp_H0 : list Z) (rp_hist : list YG00.chunk),
    (length rp_os <= 4)%nat /\ PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist (cw_S D) /\
    PRH_Base.prh_run_at rp_sm rp_x rp_os rp_i [PresetReqAt.HMal (cw_size D + 1)].
Proof.
destruct HP
  as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _).
exact H.
Qed.
Lemma caw_pre_frm0 : ck_frm0.
Proof.
destruct HP
  as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H).
exact H.
Qed.
End pre_proj.

(* ---- THE ROOM COUNTS (formerly the named argument CAW_CNT): caw_cnt D is the conjunction of the text's two count
   premises (PRH_FnCheck.v:1343-1344), so the batch text discharges it BY CONVERSION (caw_pre_cnt) ---- *)
Definition caw_cnt (D : caw_in) : Prop :=
  YGcfRoomLive.sec_cnt (cw_S D) <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV /\
  YGcfRoomLive.ccnt24 (cw_S D) <= PresetLiveBounds.L24 + PresetLiveBounds.DRV.
Lemma caw_pre_cnt : forall D, caw_pre D -> caw_cnt D.
Proof. intros D HP. exact (conj (caw_pre_sec D HP) (caw_pre_c24 D HP)). Qed.

(* ---- the scratch's run events: malloc (size + 1) granted, then its free (the model's [HMal (n + 1); HFr (n + 1)] of
   PresetRun.call_rest, PresetReqAt.v:272) ---- *)
Definition caw_ev1 (D : caw_in) : list PresetReqAt.hev := [PresetReqAt.HMal (cw_size D + 1)].
Definition caw_evs (D : caw_in) : list PresetReqAt.hev :=
  [PresetReqAt.HMal (cw_size D + 1); PresetReqAt.HFr (cw_size D + 1)].

(* ---- THE PROGRESS FACT a cut carries for the events E made since entry (the text's post-implication form; the cno
   B' base's cnb_prog, without its live-set conjunct): for ANY run position i at the entry state whose next events
   are E, a position i + length E of this state ---- *)
Definition caw_prog (D : caw_in) (E : list PresetReqAt.hev) (S3 : astate) : Prop :=
  forall (sm : list Z -> Z * Z) (x0 : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
    (H0 : list Z) (hist : list YG00.chunk),
    PresetRoomPos.iface_room_pos sm x0 os i H0 hist (cw_S D) -> PRH_Base.prh_run_at sm x0 os i E ->
    exists hist', PresetRoomPos.iface_room_pos sm x0 os (i + length E)%nat H0 hist' S3.
(* ---- THE OUTCOME's dead arm (PRH_FnCheck.v c40cf3fdcd2a :879-888): at any run position i at the ENTRY state whose
   next events are the scratch pair and whose allocation among them is a consumer event, the scratch was NOT refused.
   It is the refused arm's exclusion, state-free (it names only the entry state), proved at WA0's NULL arm where the
   malloc's granted NULL path is held (PRH_Refute.prh_refute_at) ---- *)
Definition caw_dead (D : caw_in) : Prop :=
  forall (sm : list Z -> Z * Z) (x0 : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
    (H0 : list Z) (hist : list YG00.chunk),
    PresetRoomPos.iface_room_pos sm x0 os i H0 hist (cw_S D) -> PRH_Base.prh_run_at sm x0 os i (caw_evs D) ->
    PRH_Base.prh_cons_from sm x0 os i (length (caw_evs D)) -> False.
(* at entry, no event yet *)
Lemma caw_prog_entry : forall D, caw_prog D [] (cw_S D).
Proof. intros D sm x0 os i H0 hist Hp _. exists hist. cbn [length]. rewrite Nat.add_0_r. exact Hp. Qed.
(* a run's next events split: E1 then E2 at i + length E1 *)
Lemma caw_firstn_app : forall {A : Type} (l E1 E2 : list A),
  firstn (length (E1 ++ E2)) l = E1 ++ E2 ->
  firstn (length E1) l = E1 /\ firstn (length E2) (skipn (length E1) l) = E2.
Proof.
intros A l E1 E2. revert l. induction E1 as [|e E1 IH]; intros l H.
- cbn [app length firstn skipn] in H |- *. split; [reflexivity | exact H].
- destruct l as [|y l]; cbn [app length firstn] in H; [discriminate H|].
  injection H as Hy H. subst y. destruct (IH l H) as [H1 H2].
  cbn [length firstn skipn]. split; [f_equal; exact H1 | exact H2].
Qed.
Lemma caw_skipn_add : forall {A : Type} (n m : nat) (l : list A), skipn n (skipn m l) = skipn (m + n) l.
Proof.
intros A n m. induction m as [|m IH]; intros l; [reflexivity|].
destruct l as [|y l]; cbn; [destruct n; reflexivity | exact (IH l)].
Qed.
Lemma caw_run_at_app : forall sm x0 os i (E1 E2 : list PresetReqAt.hev),
  PRH_Base.prh_run_at sm x0 os i (E1 ++ E2) ->
  PRH_Base.prh_run_at sm x0 os i E1 /\ PRH_Base.prh_run_at sm x0 os (i + length E1)%nat E2.
Proof.
intros sm x0 os i E1 E2 H. unfold PRH_Base.prh_run_at in *.
destruct (caw_firstn_app _ E1 E2 H) as [H1 H2]. split; [exact H1|].
rewrite <- caw_skipn_add. exact H2.
Qed.
(* the next event, one at a time (PresetRoomPosKeep.room_pos_keep_alloc / _free take it by nth_error) *)
Lemma caw_run_at_nth : forall sm x0 os i (e : PresetReqAt.hev) (E : list PresetReqAt.hev),
  PRH_Base.prh_run_at sm x0 os i (e :: E) -> nth_error (PresetRun.hruns sm x0 os) i = Some e.
Proof.
intros sm x0 os i e E. unfold PRH_Base.prh_run_at.
remember (PresetRun.hruns sm x0 os) as l eqn:El. clear El. revert l.
induction i as [|i IH]; intros l H; destruct l as [|z l]; cbn in H |- *; try discriminate.
- injection H as -> _. reflexivity.
- exact (IH l H).
Qed.

(* ---- the text's post body and post, at one record, VERBATIM (PRH_FnCheck.v c40cf3fdcd2a :874-902): the ledger at
   own', THE OUTCOME under the run hypothesis, and the position in the post-implication form keyed on the scratch's
   own grant ---- *)
Definition caw_Qb (D : caw_in) : alayout -> astate -> list Z -> world segs -> bvmap 5 word ->
  (word -> option byte) -> Model -> Prop :=
  fun ly' S' Hp' W' regs' mem' md' =>
       room_live_cf S' /\ Hp' = cw_Hp D /\ ablocks B ly' S' = ablocks B (cw_ly D) (cw_S D) /\
       exists own', prh_ledger B ly' S' Hp' W' mem' (cw_Lam D) (cw_peak D) (cw_cnt D) (cw_fail D) (cw_ran D) (cw_most D)
         own' /\
       bytes_at W' mem' (cw_data D) (cw_x D) /\
       exists r, getr regs' 10 = w64 r /\
        (forall (sm : list Z -> Z * Z) (x0 : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
           (H0 : list Z) (hist : list YG00.chunk),
           PresetRoomPos.iface_room_pos sm x0 os i H0 hist (cw_S D) ->
           PRH_Base.prh_run_at sm x0 os i [PresetReqAt.HMal (cw_size D + 1); PresetReqAt.HFr (cw_size D + 1)] ->
           PRH_Base.prh_cons_from sm x0 os i (length [PresetReqAt.HMal (cw_size D + 1); PresetReqAt.HFr (cw_size D + 1)]) ->
           r = 0 /\ exists hist', PresetRoomPos.iface_room_pos sm x0 os
             (i + length [PresetReqAt.HMal (cw_size D + 1); PresetReqAt.HFr (cw_size D + 1)])%nat H0 hist' S') /\
        ((r = 1 /\ own' = 1 /\ (forall (sm : list Z -> Z * Z) (x0 : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
           (H0 : list Z) (hist : list YG00.chunk),
           PresetRoomPos.iface_room_pos sm x0 os i H0 hist (cw_S D) -> PRH_Base.prh_run_at sm x0 os i (@nil PresetReqAt.hev) ->
           exists hist', PresetRoomPos.iface_room_pos sm x0 os (i + length (@nil PresetReqAt.hev))%nat H0 hist' S')) \/
         (r = 0 /\ own' = 0 /\
          (forall (sm : list Z -> Z * Z) (x0 : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
          (H0 : list Z) (hist : list YG00.chunk),
          PresetRoomPos.iface_room_pos sm x0 os i H0 hist (cw_S D) ->
          PRH_Base.prh_run_at sm x0 os i [PresetReqAt.HMal (cw_size D + 1); PresetReqAt.HFr (cw_size D + 1)] ->
          exists hist', PresetRoomPos.iface_room_pos sm x0 os
            (i + length [PresetReqAt.HMal (cw_size D + 1); PresetReqAt.HFr (cw_size D + 1)])%nat H0 hist' S') /\
           (cw_rc D = 0 -> pj_nodeR segs (rdW W' mem') (prh_lin (cw_Lam D)) (cw_doc D) (cw_t D) (cw_D D)))).
(* the post's position conjuncts ARE caw_prog at [] / caw_evs (by conversion) *)
Lemma caw_Qb_prog : forall D S',
  (caw_prog D [] S' <->
   (forall (sm : list Z -> Z * Z) (x0 : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
      (H0 : list Z) (hist : list YG00.chunk),
      PresetRoomPos.iface_room_pos sm x0 os i H0 hist (cw_S D) -> PRH_Base.prh_run_at sm x0 os i (@nil PresetReqAt.hev) ->
      exists hist', PresetRoomPos.iface_room_pos sm x0 os (i + length (@nil PresetReqAt.hev))%nat H0 hist' S')) /\
  (caw_prog D (caw_evs D) S' <->
   (forall (sm : list Z -> Z * Z) (x0 : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
      (H0 : list Z) (hist : list YG00.chunk),
      PresetRoomPos.iface_room_pos sm x0 os i H0 hist (cw_S D) ->
      PRH_Base.prh_run_at sm x0 os i [PresetReqAt.HMal (cw_size D + 1); PresetReqAt.HFr (cw_size D + 1)] ->
      exists hist', PresetRoomPos.iface_room_pos sm x0 os
        (i + length [PresetReqAt.HMal (cw_size D + 1); PresetReqAt.HFr (cw_size D + 1)])%nat H0 hist' S')).
Proof. intros D S'. split; reflexivity. Qed.
Definition caw_cfg0 (D : caw_in) : config :=
  cfg_at segs (SIGMA AS_check_as_written) (cw_regs D) (cw_mem D) (cw_md D).
Definition caw_text_post (D : caw_in) : world segs -> config -> Prop :=
  fpostFm B ARcfx SK STK_check_as_written [] (cw_regs D) (cw_ly D) (cw_S D) (cw_Hp D) (cw_W D) (cw_mem D) (cw_md D)
    (caw_Qb D).

(* THE RECORD IS THE TEXT: a walk of every record whose premises hold is the kit's text at ARcfx (checks that caw_pre and
   caw_text_post are the text's, binder for binder; the room counts caw_cnt D are caw_pre's own, caw_pre_cnt) *)
Lemma caw_text_of_walk :
  (forall D, caw_pre D -> caw_cnt D -> SRr segs (cw_W D) (caw_cfg0 D) (caw_text_post D)) ->
  tcheck_as_written_specX B ARcfx SK CTX0.
Proof.
intros HW ly S Hp W regs mem md ch data x rc0 doc t D Lam peak cnt fail ran most
  size H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 Hhull Hhpos H25.
pose (R := mkCawIn ly S Hp W regs mem md ch data x rc0 doc t D Lam peak cnt fail ran most).
assert (Hpre : caw_pre R)
  by exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 (conj H10 (conj H11
    (conj H12 (conj H13 (conj H14 (conj H15 (conj H16 (conj H17 (conj H18 (conj H19 (conj H20 (conj H21 (conj H22
    (conj H23 (conj H24 (conj Hhull (conj Hhpos H25)))))))))))))))))))))))))).
apply YA0nH.SRr_SRr'. exact (HW R Hpre (caw_pre_cnt R Hpre)).
Qed.
(* caw_text_of_walk at the text's own conclusion form: a walk of every record whose premises hold, each at
   YA0nH.SRr' segs RZ_cf (the re-hide's world relation, at which the walk runs past the scratch's free), is the kit's text *)
Lemma caw_text_of_walkR :
  (forall D, caw_pre D -> caw_cnt D ->
     YA0nH.SRr' segs YGcfRehidePost.RZ_cf (cw_W D) (caw_cfg0 D) (caw_text_post D)) ->
  tcheck_as_written_specX B ARcfx SK CTX0.
Proof.
intros HW ly S Hp W regs mem md ch data x rc0 doc t D Lam peak cnt fail ran most
  size H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 Hhull Hhpos H25.
pose (R := mkCawIn ly S Hp W regs mem md ch data x rc0 doc t D Lam peak cnt fail ran most).
assert (Hpre : caw_pre R)
  by exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 (conj H10 (conj H11
    (conj H12 (conj H13 (conj H14 (conj H15 (conj H16 (conj H17 (conj H18 (conj H19 (conj H20 (conj H21 (conj H22
    (conj H23 (conj H24 (conj Hhull (conj Hhpos H25)))))))))))))))))))))))))).
exact (HW R Hpre (caw_pre_cnt R Hpre)).
Qed.

(* ---- WHAT EVERY CUT CARRIES ---- *)
(* the journal from entry: the function's own frame on the real stack, no fake frame, FP empty *)
Definition caw_J (D : caw_in) (ly3 : alayout) (S3 : astate) (Hp3 : list Z) (W3 : world segs)
  (mem3 : word -> option byte) (md3 : Model) (k : Z) : Prop :=
  ajournal_x (SK := SK) segs B prh_pst ARcfx STK_check_as_written (cw_sp0 D) []
    (cw_ly D) (cw_S D) (cw_Hp D) (cw_W D) (cw_mem D) (cw_md D) [] ly3 S3 Hp3 W3 mem3 md3 k.
(* caw_J over a world relation R: ajournal_xR R in place of ajournal_x, every argument as caw_J's *)
Definition caw_JR (R : world segs -> world segs -> Prop) (D : caw_in) (ly3 : alayout) (S3 : astate) (Hp3 : list Z)
  (W3 : world segs) (mem3 : word -> option byte) (md3 : Model) (k : Z) : Prop :=
  ajournal_xR (SK := SK) segs B prh_pst ARcfx R STK_check_as_written (cw_sp0 D) []
    (cw_ly D) (cw_S D) (cw_Hp D) (cw_W D) (cw_mem D) (cw_md D) [] ly3 S3 Hp3 W3 mem3 md3 k.
Lemma caw_J_R_wle : forall D ly3 S3 Hp3 W3 mem3 md3 k,
  caw_J D ly3 S3 Hp3 W3 mem3 md3 k = caw_JR (@wle segs) D ly3 S3 Hp3 W3 mem3 md3 k.
Proof. reflexivity. Qed.
(* gp, tp and the callee-saved registers the function never writes, at their entry values *)
Definition caw_kregs (D : caw_in) (regs3 : bvmap 5 word) : Prop :=
  forall r : bv 5, In r [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs3 r = getr (cw_regs D) r.
(* the prologue's four saved words: ra at sp0 - 8, s0 at - 16, s1 at - 24, s2 at - 32 *)
Definition caw_saved (D : caw_in) (W3 : world segs) (mem3 : word -> option byte) : Prop :=
  val_mem segs (rdW W3 mem3) (cw_sp0 D - 8) 8 (raZ (cw_regs D)) /\
  val_mem segs (rdW W3 mem3) (cw_sp0 D - 16) 8 (bv_unsigned (getr (cw_regs D) 8)) /\
  val_mem segs (rdW W3 mem3) (cw_sp0 D - 24) 8 (bv_unsigned (getr (cw_regs D) 9)) /\
  val_mem segs (rdW W3 mem3) (cw_sp0 D - 32) 8 (bv_unsigned (getr (cw_regs D) 18)).
(* the float state at a cut: ex_value (musl strtod) may change it; rounding mode back at 0, fs0-fs11 kept *)
Definition caw_fl (fy : YK11.FPState) : Prop := frm_zero (@YK11.fp_csr fy) /\ fregs_kept_x fx fy.
(* the carry: the entry's premises and the room counts (caw_pre_cnt), the float state, the journal from entry, the kept and
   saved registers, the frame pointer, the harness heads, the non-primary room and the read-only view (the ledger is
   each cut's last conjunct, caw_ledger, at the byte g_own_ran_out holds there; the run position is each cut's
   caw_prog) *)
Definition caw_carry (D : caw_in) (fy : YK11.FPState) (ly3 : alayout) (S3 : astate) (Hp3 : list Z) (W3 : world segs)
  (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model) (k : Z) : Prop :=
  caw_pre D /\ caw_cnt D /\ caw_fl fy /\ caw_J D ly3 S3 Hp3 W3 mem3 md3 k /\ caw_kregs D regs3 /\
  spZ regs3 = cw_sp0 D - CAW_FRAME /\ caw_saved D W3 mem3 /\
  Hp3 = cw_Hp D /\ room_live_cf S3 /\
  arodata_okP segs (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) B (aview segs (w_H W3) mem3).
(* caw_carry over a world relation R: the journal conjunct caw_JR R, every other conjunct as caw_carry's *)
Definition caw_carryR (R : world segs -> world segs -> Prop) (D : caw_in) (fy : YK11.FPState) (ly3 : alayout)
  (S3 : astate) (Hp3 : list Z) (W3 : world segs) (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model)
  (k : Z) : Prop :=
  caw_pre D /\ caw_cnt D /\ caw_fl fy /\ caw_JR R D ly3 S3 Hp3 W3 mem3 md3 k /\ caw_kregs D regs3 /\
  spZ regs3 = cw_sp0 D - CAW_FRAME /\ caw_saved D W3 mem3 /\
  Hp3 = cw_Hp D /\ room_live_cf S3 /\
  arodata_okP segs (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) B (aview segs (w_H W3) mem3).
Lemma caw_carry_R_wle : forall D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k,
  caw_carry D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k = caw_carryR (@wle segs) D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k.
Proof. reflexivity. Qed.
(* the scratch block expected() took (__wrap_malloc (size + 1)), new since entry *)
Definition caw_scr (D : caw_in) (ly3 : alayout) (S3 : astate) (scr : Z) : Prop :=
  4096 <= scr /\ ablocks B ly3 S3 = ablocks B (cw_ly D) (cw_S D) ++ [(scr, cw_size D + 1)].
(* expected()'s result want, as check_as_written's two checks read it (fuzz_preset.c new:333-349, :570-589) *)
Definition caw_want (D : caw_in) (want : Z) : Prop :=
  (ck_read (cw_x D) = None /\ want = -1) \/
  (exists u, ck_read (cw_x D) = Some u /\ (want = 0 \/ want = 1) /\ (want = 1 <-> cw_rc D = 0 /\ cw_t D <> u)).

(* the machine configuration at a cut of the function *)
Definition caw_cfg (fy : YK11.FPState) (o : Z) (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model) : config :=
  mkCfg (@YK11.mkst fy regs3 (Z_to_bv 64 (caw_pc o)) mem3 (YK11.seg_rom segs)) md3.
(* a segment's post: the final post Q, and the invariant P at the end memory *)
Definition caw_QP (P : (word -> option byte) -> Prop) (Q : world segs -> config -> Prop) : world segs -> config -> Prop :=
  fun W' c' => Q W' c' /\ P (ms_mem (cfg_ms c')).
(* the ledger at a cut (the kit's Batch 2, decff67d721f): the entry's values, the record's most, and own, the byte
   g_own_ran_out holds at the cut (prh_ledger_own reads it; a hand step writes it only at the NULL arm's
   `sb 1, g_own_ran_out`). It replaces the caw_pst threading of c3fe12bc7ff1 by citation. *)
Definition caw_ledger (D : caw_in) (ly3 : alayout) (S3 : astate) (Hp3 : list Z) (W3 : world segs)
  (mem3 : word -> option byte) (own : Z) : Prop :=
  prh_ledger B ly3 S3 Hp3 W3 mem3 (cw_Lam D) (cw_peak D) (cw_cnt D) (cw_fail D) (cw_ran D) (cw_most D) own.

(* ---- THE CUTS ---- *)
(* CAW_PC_X (+68): the scratch malloc returned scr <> 0 (its event made: caw_prog at caw_ev1); the struct holds p =
   data, end, depth = 0 *)
Definition caw_at_X (D : caw_in) (fy : YK11.FPState) (ly3 : alayout) (S3 : astate) (Hp3 : list Z) (W3 : world segs)
  (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model) (k scr : Z) : Prop :=
  caw_carry D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k /\
  caw_prog D (caw_ev1 D) S3 /\
  getr regs3 10 = w64 scr /\ getr regs3 8 = w64 (cw_rc D) /\ getr regs3 9 = w64 (cw_doc D) /\
  getr regs3 18 = w64 SHADOW_OFF /\
  val_mem segs (rdW W3 mem3) (cw_sp0 D - 72) 8 (cw_data D) /\
  val_mem segs (rdW W3 mem3) (cw_sp0 D - 64) 8 (cw_data D + cw_size D) /\
  val_mem segs (rdW W3 mem3) (cw_sp0 D - 56) 8 0 /\
  caw_scr D ly3 S3 scr /\
  caw_ledger D ly3 S3 Hp3 W3 mem3 0 /\
  PresetHullBudget.hull_budget S3 [PresetReqAt.HFr (cw_size D + 1)].
(* CAW_PC_NULL (+112): the scratch malloc was refused (a0 = 0; the wrapper's errno and out-of-memory byte), so no
   event was made (caw_prog at []); the refusal is DEAD under the run hypothesis (caw_dead, proved at the malloc from its
   granted NULL path); the store of 1 to g_own_ran_out (+120) is WA1's, so the cell still holds the entry's 0 *)
Definition caw_at_null (D : caw_in) (fy : YK11.FPState) (ly3 : alayout) (S3 : astate) (Hp3 : list Z) (W3 : world segs)
  (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model) (k : Z) : Prop :=
  caw_carry D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k /\ caw_prog D [] S3 /\ caw_dead D /\
  getr regs3 10 = w64 0 /\ getr regs3 8 = w64 (cw_rc D) /\ getr regs3 9 = w64 (cw_doc D) /\
  ablocks B ly3 S3 = ablocks B (cw_ly D) (cw_S D) /\
  rd32 (aview segs (w_H W3) mem3) (as_errno B) 12 /\ aview segs (w_H W3) mem3 (as_oom_byte B) = Some 1 /\
  caw_ledger D ly3 S3 Hp3 W3 mem3 0.
(* CAW_PC_R (+128): ex_value read the value u with the rest `rest` after it: p = data + size - |rest|; the scratch
   is still live; differs dl is set exactly when rc = 0 and the reader's tree is not u; the text still readable *)
Definition caw_at_R (D : caw_in) (fy : YK11.FPState) (ly3 : alayout) (S3 : astate) (Hp3 : list Z) (W3 : world segs)
  (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model) (k scr : Z) (u : PjTree.jv) (rest : list Z)
  (dl : Z) : Prop :=
  caw_carry D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k /\
  caw_prog D (caw_ev1 D) S3 /\
  getr regs3 8 = w64 (cw_rc D) /\ getr regs3 9 = w64 (cw_doc D) /\ getr regs3 18 = w64 SHADOW_OFF /\
  prhex_V 0 (cw_x D) = Some (u, rest) /\
  val_mem segs (rdW W3 mem3) (cw_sp0 D - 72) 8 (cw_data D + cw_size D - Z.of_nat (length rest)) /\
  val_mem segs (rdW W3 mem3) (cw_sp0 D - 64) 8 (cw_data D + cw_size D) /\
  val_mem segs (rdW W3 mem3) (cw_sp0 D - 48) 8 scr /\
  val_mem segs (rdW W3 mem3) (cw_sp0 D - 40) 4 dl /\ (dl = 0 \/ dl = 1) /\
  (dl = 1 <-> cw_rc D = 0 /\ cw_t D <> u) /\
  src_rd W3 mem3 (cw_data D) (cw_x D) /\
  caw_scr D ly3 S3 scr /\
  caw_ledger D ly3 S3 Hp3 W3 mem3 0 /\
  PresetHullBudget.hull_budget S3 [PresetReqAt.HFr (cw_size D + 1)].
(* caw_at_OOM over a world relation R: caw_carryR R in place of caw_carry *)
Definition caw_at_OOMR (R : world segs -> world segs -> Prop) (D : caw_in) (fy : YK11.FPState) (ly3 : alayout)
  (S3 : astate) (Hp3 : list Z) (W3 : world segs) (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model)
  (k want : Z) : Prop :=
  caw_carryR R D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k /\ caw_prog D (caw_evs D) S3 /\
  getr regs3 8 = w64 (cw_rc D) /\ getr regs3 18 = w64 want /\ caw_want D want /\
  ablocks B ly3 S3 = ablocks B (cw_ly D) (cw_S D) /\
  caw_ledger D ly3 S3 Hp3 W3 mem3 0.
(* CAW_PC_OOM (+252): the scratch is freed (the entry's blocks; both events made: caw_prog at caw_evs); s2 = want *)
Definition caw_at_OOM (D : caw_in) (fy : YK11.FPState) (ly3 : alayout) (S3 : astate) (Hp3 : list Z) (W3 : world segs)
  (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model) (k want : Z) : Prop :=
  caw_carry D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k /\ caw_prog D (caw_evs D) S3 /\
  getr regs3 8 = w64 (cw_rc D) /\ getr regs3 18 = w64 want /\ caw_want D want /\
  ablocks B ly3 S3 = ablocks B (cw_ly D) (cw_S D) /\
  caw_ledger D ly3 S3 Hp3 W3 mem3 0.
Lemma caw_at_OOM_R_wle : forall D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k want,
  caw_at_OOM D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k want =
  caw_at_OOMR (@wle segs) D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k want.
Proof. reflexivity. Qed.
(* caw_at_CHK over a world relation R: caw_carryR R in place of caw_carry *)
Definition caw_at_CHKR (R : world segs -> world segs -> Prop) (D : caw_in) (fy : YK11.FPState) (ly3 : alayout)
  (S3 : astate) (Hp3 : list Z) (W3 : world segs) (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model)
  (k want ownv : Z) : Prop :=
  caw_carryR R D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k /\ caw_prog D (caw_evs D) S3 /\
  getr regs3 8 = w64 (cw_rc D) /\ getr regs3 18 = w64 want /\ caw_want D want /\ ownv = 0 /\
  ablocks B ly3 S3 = ablocks B (cw_ly D) (cw_S D) /\
  caw_ledger D ly3 S3 Hp3 W3 mem3 ownv.
(* CAW_PC_CHK (+276): out_of_memory () was 0 (ownv = 0, the byte the code read, which the cut's ledger ties to the
   current memory); s2 = want; both events made *)
Definition caw_at_CHK (D : caw_in) (fy : YK11.FPState) (ly3 : alayout) (S3 : astate) (Hp3 : list Z) (W3 : world segs)
  (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model) (k want ownv : Z) : Prop :=
  caw_carry D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k /\ caw_prog D (caw_evs D) S3 /\
  getr regs3 8 = w64 (cw_rc D) /\ getr regs3 18 = w64 want /\ caw_want D want /\ ownv = 0 /\
  ablocks B ly3 S3 = ablocks B (cw_ly D) (cw_S D) /\
  caw_ledger D ly3 S3 Hp3 W3 mem3 ownv.
Lemma caw_at_CHK_R_wle : forall D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k want ownv,
  caw_at_CHK D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k want ownv =
  caw_at_CHKR (@wle segs) D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k want ownv.
Proof. reflexivity. Qed.
(* caw_at_END over a world relation R: caw_carryR R in place of caw_carry *)
Definition caw_at_ENDR (R : world segs -> world segs -> Prop) (D : caw_in) (fy : YK11.FPState) (ly3 : alayout)
  (S3 : astate) (Hp3 : list Z) (W3 : world segs) (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model)
  (k r ownv : Z) : Prop :=
  caw_carryR R D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k /\
  getr regs3 9 = w64 r /\
  ((r = 1 /\ ownv = 1 /\ caw_prog D [] S3 /\ caw_dead D) \/
   (r = 0 /\ ownv = 0 /\ caw_prog D (caw_evs D) S3)) /\
  ablocks B ly3 S3 = ablocks B (cw_ly D) (cw_S D) /\
  caw_ledger D ly3 S3 Hp3 W3 mem3 ownv.
(* CAW_PC_END (+300): s1 = r, the return value; r = 1 exactly when the own value ownv is 1, the byte the cut's ledger
   holds (so the post's own' is the cut's); the progress per arm, as the text's post: r = 1 (the scratch refused) made
   no event and is dead under the run hypothesis (caw_dead, the text's OUTCOME conjunct), r = 0 made both *)
Definition caw_at_END (D : caw_in) (fy : YK11.FPState) (ly3 : alayout) (S3 : astate) (Hp3 : list Z) (W3 : world segs)
  (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model) (k r ownv : Z) : Prop :=
  caw_carry D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k /\
  getr regs3 9 = w64 r /\
  ((r = 1 /\ ownv = 1 /\ caw_prog D [] S3 /\ caw_dead D) \/
   (r = 0 /\ ownv = 0 /\ caw_prog D (caw_evs D) S3)) /\
  ablocks B ly3 S3 = ablocks B (cw_ly D) (cw_S D) /\
  caw_ledger D ly3 S3 Hp3 W3 mem3 ownv.
Lemma caw_at_END_R_wle : forall D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k r ownv,
  caw_at_END D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k r ownv =
  caw_at_ENDR (@wle segs) D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k r ownv.
Proof. reflexivity. Qed.
(* the post's own' at the End cut, read off its ledger (PRH_Base.prh_ledger_own) *)
Lemma caw_at_END_own : forall D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k r ownv,
  caw_at_END D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k r ownv -> prh_own W3 mem3 ownv.
Proof.
intros D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k r ownv (_ & _ & _ & _ & H). unfold caw_ledger in H.
eapply prh_ledger_own. exact H.
Qed.

(* ---- THE SEGMENT STATEMENTS (generic P, generic final post Q; continuation form) ---- *)
Section segs. Variable P : (word -> option byte) -> Prop.
(* the continuation at a cut *)
(* the continuation at a cut over a world relation R: the cut's own R form where it has one (caw_at_OOMR,
   caw_at_CHKR, caw_at_ENDR), and YA0nH.SRrG segs R in place of SRr segs *)
Definition caw_k_XR (R : world segs -> world segs -> Prop) (Q : world segs -> config -> Prop) (D : caw_in) : Prop :=
  forall fy ly3 S3 Hp3 W3 regs3 mem3 md3 k scr,
    caw_at_X D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k scr -> P mem3 ->
    YA0nH.SRrG segs R W3 (caw_cfg fy CAW_PC_X regs3 mem3 md3) (caw_QP P Q).
Definition caw_k_X (Q : world segs -> config -> Prop) (D : caw_in) : Prop :=
  caw_k_XR (@wle segs) Q D.
Lemma caw_k_X_R_wle : forall Q D, caw_k_X Q D = caw_k_XR (@wle segs) Q D.
Proof. reflexivity. Qed.
Definition caw_k_nullR (R : world segs -> world segs -> Prop) (Q : world segs -> config -> Prop) (D : caw_in) : Prop :=
  forall fy ly3 S3 Hp3 W3 regs3 mem3 md3 k,
    caw_at_null D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k -> P mem3 ->
    YA0nH.SRrG segs R W3 (caw_cfg fy CAW_PC_NULL regs3 mem3 md3) (caw_QP P Q).
Definition caw_k_null (Q : world segs -> config -> Prop) (D : caw_in) : Prop :=
  caw_k_nullR (@wle segs) Q D.
Lemma caw_k_null_R_wle : forall Q D, caw_k_null Q D = caw_k_nullR (@wle segs) Q D.
Proof. reflexivity. Qed.
Definition caw_k_RR (R : world segs -> world segs -> Prop) (Q : world segs -> config -> Prop) (D : caw_in) : Prop :=
  forall fy ly3 S3 Hp3 W3 regs3 mem3 md3 k scr u rest dl,
    caw_at_R D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k scr u rest dl -> P mem3 ->
    YA0nH.SRrG segs R W3 (caw_cfg fy CAW_PC_R regs3 mem3 md3) (caw_QP P Q).
Definition caw_k_R (Q : world segs -> config -> Prop) (D : caw_in) : Prop :=
  caw_k_RR (@wle segs) Q D.
Lemma caw_k_R_R_wle : forall Q D, caw_k_R Q D = caw_k_RR (@wle segs) Q D.
Proof. reflexivity. Qed.
Definition caw_k_OOMR (R : world segs -> world segs -> Prop) (Q : world segs -> config -> Prop) (D : caw_in) : Prop :=
  forall fy ly3 S3 Hp3 W3 regs3 mem3 md3 k want,
    caw_at_OOMR R D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k want -> P mem3 ->
    YA0nH.SRrG segs R W3 (caw_cfg fy CAW_PC_OOM regs3 mem3 md3) (caw_QP P Q).
Definition caw_k_OOM (Q : world segs -> config -> Prop) (D : caw_in) : Prop :=
  caw_k_OOMR (@wle segs) Q D.
Lemma caw_k_OOM_R_wle : forall Q D, caw_k_OOM Q D = caw_k_OOMR (@wle segs) Q D.
Proof. reflexivity. Qed.
Definition caw_k_CHKR (R : world segs -> world segs -> Prop) (Q : world segs -> config -> Prop) (D : caw_in) : Prop :=
  forall fy ly3 S3 Hp3 W3 regs3 mem3 md3 k want ownv,
    caw_at_CHKR R D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k want ownv -> P mem3 ->
    YA0nH.SRrG segs R W3 (caw_cfg fy CAW_PC_CHK regs3 mem3 md3) (caw_QP P Q).
Definition caw_k_CHK (Q : world segs -> config -> Prop) (D : caw_in) : Prop :=
  caw_k_CHKR (@wle segs) Q D.
Lemma caw_k_CHK_R_wle : forall Q D, caw_k_CHK Q D = caw_k_CHKR (@wle segs) Q D.
Proof. reflexivity. Qed.
Definition caw_k_ENDR (R : world segs -> world segs -> Prop) (Q : world segs -> config -> Prop) (D : caw_in) : Prop :=
  forall fy ly3 S3 Hp3 W3 regs3 mem3 md3 k r ownv,
    caw_at_ENDR R D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k r ownv -> P mem3 ->
    YA0nH.SRrG segs R W3 (caw_cfg fy CAW_PC_END regs3 mem3 md3) (caw_QP P Q).
Definition caw_k_END (Q : world segs -> config -> Prop) (D : caw_in) : Prop :=
  caw_k_ENDR (@wle segs) Q D.
Lemma caw_k_END_R_wle : forall Q D, caw_k_END Q D = caw_k_ENDR (@wle segs) Q D.
Proof. reflexivity. Qed.

(* WA0 (+0 -> +68 / +112): the prologue, the GOT and shadow-base loads, the struct, the scratch malloc, the beqz (the
   room counts caw_cnt D are its premise, caw_pre_cnt of the entry; the NULL arm's caw_dead is proved here) *)
Definition caw_seg_WA0 : Prop :=
  forall Q D, caw_pre D -> caw_cnt D -> caw_k_X Q D -> caw_k_null Q D ->
  P (ms_mem (cfg_ms (caw_cfg0 D))) ->
  SRr segs (cw_W D) (caw_cfg0 D) (caw_QP P Q).
(* caw_seg_WA0 over a world relation R: the continuations' R forms (caw_k_XR, caw_k_nullR; their cuts stay the wle
   forms caw_at_X / caw_at_null, no free is behind them) and YA0nH.SRrG segs R in place of SRr. caw_seg_WA0_lift
   below gives it from caw_seg_WA0 at every R that contains wle and is transitive *)
Definition caw_seg_WA0R (R : world segs -> world segs -> Prop) : Prop :=
  forall Q D, caw_pre D -> caw_cnt D -> caw_k_XR R Q D -> caw_k_nullR R Q D ->
  P (ms_mem (cfg_ms (caw_cfg0 D))) ->
  YA0nH.SRrG segs R (cw_W D) (caw_cfg0 D) (caw_QP P Q).
Lemma caw_seg_WA0_R_wle : caw_seg_WA0 = caw_seg_WA0R (@wle segs).
Proof. reflexivity. Qed.
(* WA1 (+112 -> +300): the malloc's NULL arm, noted (): `sb 1, g_own_ran_out` (+120, the prh_pst row pi_g_own_ran_out
   of the kit's batch 1), s1 = 1, j +300; r = 1 with the last-written own value ownv = 1 *)
Definition caw_seg_WA1 : Prop :=
  forall Q D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k,
  caw_at_null D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k -> caw_k_END Q D -> P mem3 ->
  SRr segs W3 (caw_cfg fy CAW_PC_NULL regs3 mem3 md3) (caw_QP P Q).
(* caw_seg_WA1 over a world relation R: the End continuation's R form caw_k_ENDR (the End cut is reached past the
   free too) and YA0nH.SRrG segs R; its own cut caw_at_null stays the wle form. caw_seg_WA1_lift below gives it from
   caw_seg_WA1 at every R that contains wle and is transitive *)
Definition caw_seg_WA1R (R : world segs -> world segs -> Prop) : Prop :=
  forall Q D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k,
  caw_at_null D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k -> caw_k_ENDR R Q D -> P mem3 ->
  YA0nH.SRrG segs R W3 (caw_cfg fy CAW_PC_NULL regs3 mem3 md3) (caw_QP P Q).
Lemma caw_seg_WA1_R_wle : caw_seg_WA1 = caw_seg_WA1R (@wle segs).
Proof. reflexivity. Qed.
(* WA2 (+68 -> +128 / +252): ex_value at depth 0 against the tree (rc == 0 ? doc : NULL); refused: free the
   scratch, want = -1 *)
Definition caw_seg_WA2 : Prop :=
  forall Q D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k scr,
  caw_at_X D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k scr -> caw_k_R Q D -> caw_k_OOM Q D -> P mem3 ->
  SRr segs W3 (caw_cfg fy CAW_PC_X regs3 mem3 md3) (caw_QP P Q).
(* caw_seg_WA2 over a world relation R: the continuations' R forms (caw_k_RR, caw_k_OOMR) and YA0nH.SRrG segs R in
   place of SRr. The refused arm frees the scratch by the free rule under the re-hide, so the run past it is at
   YA0nH.wle' segs RZ_cf: WA2 proves this form at that relation *)
Definition caw_seg_WA2R (R : world segs -> world segs -> Prop) : Prop :=
  forall Q D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k scr,
  caw_at_X D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k scr -> caw_k_RR R Q D -> caw_k_OOMR R Q D -> P mem3 ->
  YA0nH.SRrG segs R W3 (caw_cfg fy CAW_PC_X regs3 mem3 md3) (caw_QP P Q).
Lemma caw_seg_WA2_R_wle : caw_seg_WA2 = caw_seg_WA2R (@wle segs).
Proof. reflexivity. Qed.
(* WA3 (+128 -> +252): the inlined ex_ws loop (report site +220 refuted), the scratch freed, want = differs when
   the rest after the value is all whitespace, else -1 *)
Definition caw_seg_WA3 : Prop :=
  forall Q D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k scr u rest dl,
  caw_at_R D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k scr u rest dl -> caw_k_OOM Q D -> P mem3 ->
  SRr segs W3 (caw_cfg fy CAW_PC_R regs3 mem3 md3) (caw_QP P Q).
(* caw_seg_WA3 over a world relation R (caw_k_OOMR, YA0nH.SRrG segs R); WA3 frees the scratch under the re-hide, so
   it proves this form at YA0nH.wle' segs RZ_cf *)
Definition caw_seg_WA3R (R : world segs -> world segs -> Prop) : Prop :=
  forall Q D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k scr u rest dl,
  caw_at_R D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k scr u rest dl -> caw_k_OOMR R Q D -> P mem3 ->
  YA0nH.SRrG segs R W3 (caw_cfg fy CAW_PC_R regs3 mem3 md3) (caw_QP P Q).
Lemma caw_seg_WA3_R_wle : caw_seg_WA3 = caw_seg_WA3R (@wle segs).
Proof. reflexivity. Qed.
(* WA4 (+252 -> +300 / +276): out_of_memory (): the g_own_ran_out load (it reads caw_at_OOM's ledger byte, 0) and
   fuzz_alloc_ran_out (its a0 = ran = 0 arm refutes the r = 1 exit through it) *)
Definition caw_seg_WA4 : Prop :=
  forall Q D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k want,
  caw_at_OOM D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k want ->
  caw_k_END Q D -> caw_k_CHK Q D -> P mem3 ->
  SRr segs W3 (caw_cfg fy CAW_PC_OOM regs3 mem3 md3) (caw_QP P Q).
(* caw_seg_WA4 over a world relation R: its own cut caw_at_OOMR R (reached past the free), the continuations' R forms
   (caw_k_ENDR, caw_k_CHKR) and YA0nH.SRrG segs R; WA4 proves it at YA0nH.wle' segs RZ_cf *)
Definition caw_seg_WA4R (R : world segs -> world segs -> Prop) : Prop :=
  forall Q D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k want,
  caw_at_OOMR R D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k want ->
  caw_k_ENDR R Q D -> caw_k_CHKR R Q D -> P mem3 ->
  YA0nH.SRrG segs R W3 (caw_cfg fy CAW_PC_OOM regs3 mem3 md3) (caw_QP P Q).
Lemma caw_seg_WA4_R_wle : caw_seg_WA4 = caw_seg_WA4R (@wle segs).
Proof. reflexivity. Qed.
(* WA5 (+276 -> +300): the two property checks, both abort edges (+336) refuted from the pre's rc / ck_read premise
   and want *)
Definition caw_seg_WA5 : Prop :=
  forall Q D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k want ownv,
  caw_at_CHK D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k want ownv -> caw_k_END Q D -> P mem3 ->
  SRr segs W3 (caw_cfg fy CAW_PC_CHK regs3 mem3 md3) (caw_QP P Q).
(* caw_seg_WA5 over a world relation R: its own cut caw_at_CHKR R, the End continuation caw_k_ENDR and
   YA0nH.SRrG segs R; WA5 proves it at YA0nH.wle' segs RZ_cf *)
Definition caw_seg_WA5R (R : world segs -> world segs -> Prop) : Prop :=
  forall Q D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k want ownv,
  caw_at_CHKR R D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k want ownv -> caw_k_ENDR R Q D -> P mem3 ->
  YA0nH.SRrG segs R W3 (caw_cfg fy CAW_PC_CHK regs3 mem3 md3) (caw_QP P Q).
Lemma caw_seg_WA5_R_wle : caw_seg_WA5 = caw_seg_WA5R (@wle segs).
Proof. reflexivity. Qed.
(* WA6 (+300 -> ret): a0 = s1, the frame restored, the return: the text's float-form post at any body Qb that holds at
   the end state with a0 = r *)
Definition caw_seg_WA6 : Prop :=
  forall (Qb : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
    D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k r ownv,
  caw_at_END D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k r ownv ->
  (forall regs' md', getr regs' 10 = w64 r -> aregs_preserved (cw_regs D) regs' -> Qb ly3 S3 Hp3 W3 regs' mem3 md') ->
  P mem3 ->
  SRr segs W3 (caw_cfg fy CAW_PC_END regs3 mem3 md3)
    (fun W' c' => fpostF (fx := fx) B ARcfx SK STK_check_as_written [] (cw_regs D) (cw_ly D) (cw_S D) (cw_Hp D) (cw_W D)
       (cw_mem D) (cw_md D) Qb W' c' /\ P (ms_mem (cfg_ms c'))).
(* caw_seg_WA6 over a world relation R: its own cut caw_at_ENDR R and YA0nH.SRrG segs R (the post fpostF is at
   YA0nH.wle' segs RZ_cf already); WA6 proves it at that relation *)
Definition caw_seg_WA6R (R : world segs -> world segs -> Prop) : Prop :=
  forall (Qb : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
    D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k r ownv,
  caw_at_ENDR R D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k r ownv ->
  (forall regs' md', getr regs' 10 = w64 r -> aregs_preserved (cw_regs D) regs' -> Qb ly3 S3 Hp3 W3 regs' mem3 md') ->
  P mem3 ->
  YA0nH.SRrG segs R W3 (caw_cfg fy CAW_PC_END regs3 mem3 md3)
    (fun W' c' => fpostF (fx := fx) B ARcfx SK STK_check_as_written [] (cw_regs D) (cw_ly D) (cw_S D) (cw_Hp D) (cw_W D)
       (cw_mem D) (cw_md D) Qb W' c' /\ P (ms_mem (cfg_ms c'))).
Lemma caw_seg_WA6_R_wle : caw_seg_WA6 = caw_seg_WA6R (@wle segs).
Proof. reflexivity. Qed.
End segs.

(* ---- THE LIFTS to a world relation R that contains wle and is transitive: a wle carry / End cut is one at R (the
   journal's world conjunct only, ajournal_xwR_mono), and a segment whose own cut is a wle form (WA0, WA1) runs, by its
   wle statement, to cuts at which its R continuations take over (the run's post records the cut reached) ---- *)
Section lift.
Variable R : world segs -> world segs -> Prop.
Hypothesis R_wle : forall W W', wle W W' -> R W W'.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
(* an SRr run each of whose post states starts an SRrG run at R is an SRrG run at R *)
Lemma caw_SRr_SRrG_bind : forall W c (Q0 Q : world segs -> config -> Prop),
  SRr segs W c Q0 -> (forall W' c', Q0 W' c' -> YA0nH.SRrG segs R W' c' Q) -> YA0nH.SRrG segs R W c Q.
Proof.
intros W c Q0 Q H HK.
apply (YA0nH.SRrG_bind segs R R_trans W c Q0 Q (YA0nH.SRr_SRrG segs R R_wle W c Q0 H)).
intros W' c' _ HQ0. exact (HK W' c' HQ0).
Qed.
Lemma caw_carry_R_lift : forall D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k,
  caw_carry D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k -> caw_carryR R D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k.
Proof.
intros D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k (H1 & H2 & H3 & HJ & H5).
refine (conj H1 (conj H2 (conj H3 (conj _ H5)))).
unfold caw_JR, ajournal_xR. unfold caw_J in HJ.
apply (ajournal_xwR_mono (SK := SK) segs B prh_pst _ (@wle segs) R R_wle). exact HJ.
Qed.
Lemma caw_at_END_R_lift : forall D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k r ownv,
  caw_at_END D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k r ownv -> caw_at_ENDR R D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k r ownv.
Proof.
intros D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k r ownv (HC & H).
exact (conj (caw_carry_R_lift D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k HC) H).
Qed.
(* WA0: its wle run stops at the X / null cuts (the post names the cut reached), then caw_k_XR / caw_k_nullR *)
Lemma caw_seg_WA0_lift : forall P, caw_seg_WA0 P -> caw_seg_WA0R P R.
Proof.
intros P H0 Q D Hpre Hcnt KX KN HP.
apply (caw_SRr_SRrG_bind _ _ (caw_QP P (fun W' c' =>
  (exists fy ly3 S3 Hp3 regs3 mem3 md3 k scr, c' = caw_cfg fy CAW_PC_X regs3 mem3 md3 /\
     caw_at_X D fy ly3 S3 Hp3 W' regs3 mem3 md3 k scr) \/
  (exists fy ly3 S3 Hp3 regs3 mem3 md3 k, c' = caw_cfg fy CAW_PC_NULL regs3 mem3 md3 /\
     caw_at_null D fy ly3 S3 Hp3 W' regs3 mem3 md3 k)))).
- apply (H0 _ D Hpre Hcnt); [| | exact HP].
  + intros fy ly3 S3 Hp3 W3 regs3 mem3 md3 k scr HAT HPM.
    apply (YA0nH.SRrG_ret segs (@wle segs) (wle_refl segs)). split; [|exact HPM].
    left. exists fy, ly3, S3, Hp3, regs3, mem3, md3, k, scr. split; [reflexivity | exact HAT].
  + intros fy ly3 S3 Hp3 W3 regs3 mem3 md3 k HAT HPM.
    apply (YA0nH.SRrG_ret segs (@wle segs) (wle_refl segs)). split; [|exact HPM].
    right. exists fy, ly3, S3, Hp3, regs3, mem3, md3, k. split; [reflexivity | exact HAT].
- intros W' c' [[(fy & ly3 & S3 & Hp3 & regs3 & mem3 & md3 & k & scr & -> & HAT)
                | (fy & ly3 & S3 & Hp3 & regs3 & mem3 & md3 & k & -> & HAT)] HPM].
  + exact (KX fy ly3 S3 Hp3 W' regs3 mem3 md3 k scr HAT HPM).
  + exact (KN fy ly3 S3 Hp3 W' regs3 mem3 md3 k HAT HPM).
Qed.
(* WA1: its wle run stops at the End cut, then caw_k_ENDR at that cut's R form *)
Lemma caw_seg_WA1_lift : forall P, caw_seg_WA1 P -> caw_seg_WA1R P R.
Proof.
intros P H1 Q D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k HAT KEND HPM.
apply (caw_SRr_SRrG_bind _ _ (caw_QP P (fun W' c' => exists fy' ly' S' Hp' regs' mem' md' k' r ownv,
  c' = caw_cfg fy' CAW_PC_END regs' mem' md' /\ caw_at_END D fy' ly' S' Hp' W' regs' mem' md' k' r ownv))).
- apply (H1 _ D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k HAT); [|exact HPM].
  intros fy' ly' S' Hp' W' regs' mem' md' k' r ownv HAE HPM'.
  apply (YA0nH.SRrG_ret segs (@wle segs) (wle_refl segs)). split; [|exact HPM'].
  exists fy', ly', S', Hp', regs', mem', md', k', r, ownv. split; [reflexivity | exact HAE].
- intros W' c' ((fy' & ly' & S' & Hp' & regs' & mem' & md' & k' & r & ownv & -> & HAE) & HPM').
  exact (KEND fy' ly' S' Hp' W' regs' mem' md' k' r ownv
    (caw_at_END_R_lift D fy' ly' S' Hp' W' regs' mem' md' k' r ownv HAE) HPM').
Qed.
End lift.

(* the instantiation at the top: memnorm of the entry memory gives memnorm at m (YSRrMemnorm's carriers) *)
Definition caw_mn (D : caw_in) (m : word -> option byte) : Prop :=
  YAkMemnorm.memnorm segs (cw_mem D) -> YAkMemnorm.memnorm segs m.
Lemma caw_mn_laws : forall D, srr_inv_laws segs (caw_mn D).
Proof. intros D. exact (srr_inv_laws_imp segs (YAkMemnorm.memnorm segs) (cw_mem D) (srr_inv_laws_memnorm_k segs)). Qed.
Lemma caw_mn_call : forall D, srr_inv_call segs (caw_mn D).
Proof. intros D. exact (srr_inv_call_imp segs (cw_mem D)). Qed.
Lemma caw_mn_mn : forall D, caw_pre D -> srr_inv_mn segs (caw_mn D).
Proof. intros D HP. exact (srr_inv_mn_imp segs (cw_mem D) (caw_pre_mn D HP)). Qed.
End cw.
(* caw_img takes B (cwi_pst_ok / cwi_pst_errno read it) and the cf image ci (the relro rows read it): each projection
   infers rc, ci, PA and B from its caw_img argument, so a use stays `cwi_<field> CWI` *)
Arguments cwi_base {rc ci PA B} _.
Arguments cwi_entry {rc ci PA B} _.
Arguments cwi_own {rc ci PA B} _.
Arguments cwi_pst_rw {rc ci PA B} _.
Arguments cwi_pst_img {rc ci PA B} _.
Arguments cwi_hi {rc ci PA B} _.
Arguments cwi_hi11 {rc ci PA B} _.
Arguments cwi_pst_seg {rc ci PA B} _.
Arguments cwi_pst_ok {rc ci PA B} _.
Arguments cwi_pst_errno {rc ci PA B} _.
Arguments cwi_relro_seg {rc ci PA B} _.
Arguments cwi_errno_relro {rc ci PA B} _.
Arguments cwi_relro_top {rc ci PA B} _.
Arguments cwi_relro_eq {rc ci PA B} _.
Arguments cwi_ro_reads_nw {rc ci PA B} _.
