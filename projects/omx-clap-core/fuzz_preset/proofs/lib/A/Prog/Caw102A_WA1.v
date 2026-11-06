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
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S4_PsFree.v, with its module paths and module names changed; 466 of its 520 lines of code are new or changed and 472 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/Caw102A_WA4.v; 196 of its 279 lines of code are new or changed and 437 lines of the source are left out. *)
(* fuzz_preset lib/A, the #102 re-walk of check_as_written on image A' (ASan build, pin sha256 1be0f53d96cb9d6c),
   part of the re-walk (re-fitted to the re-keyed base and then to the batch base, in two
   steps): segment WA1. On the kit's cut of the #102 batch, preset-tree-at-2026-10-30T04-57-22Z.tsv (sha256 652fe98064b9; internal record).
   rule 24: no function proved. rule 24: proves no function (kind: segment lemma).
   WHAT IT PROVES: caw_wa1_holds : caw_seg_WA1 (fx := fx) B SK CTX0 P (Caw102A_Base.v, statements of 6fb51f0a23b0),
   for an ABSTRACT memory invariant P with PLAW : srr_inv_laws segs P (the segment calls nothing, so no srr_inv_call
   and no srr_inv_mn). The malloc's NULL arm, noted () inlined: from CAW_PC_NULL (+112, the base's cut caw_at_null)
   to CAW_PC_END (+300, the continuation caw_k_END) with r = 1 and the last-written own value ownv = 1.
   RE-FIT TO THE BATCH BASE: base of record (as at
   preset-tree-at-2026-10-30T02-52-53Z.tsv (sha256 5a024403b9d9; internal record), lib/A/Prog/Caw102A_Base.v 6fb51f0a23b0), bound now to the kit's cut
   preset-tree-at-2026-10-30T04-57-22Z.tsv (sha256 652fe98064b9; internal record) (PRH_FnCheck.v c40cf3fdcd2a, tcheck_as_written_specX :832-902;
   PRH_Base.v ef7c8ca98529; the journal YCbqG.v 219748197d6b). This file was proved on the f97c base
   preset-tree-at-2026-10-29T19-45-00Z.tsv (sha256 93ba80c03f7d; internal record) (Caw102A_Base.v deec9ccf853b). What changed, and why:
   - the run-word list DW is gone from the text (its binder and prh_univ_closure's argument): the base drops its
     Section variable DW, so this file drops its own `Variable DW` and the statement reads
     caw_seg_WA1 (fx := fx) B SK CTX0 P. No other statement change.
   - caw_pre now has 27 conjuncts (Caw102A_Base.v:229-256; the room counts, hull budget and HPOS follow room_live_cf, so ck_frm0
     moved by four): it is read BY NAME, caw_pre_fpre (the only part this segment reads), never by a positional pattern.
   - THE OUTCOME (the text's :879-888): caw_at_null carries caw_dead D (third, after caw_prog D [] S3), proved at
     WA0's NULL arm; the End cut's r = 1 arm asks it, state-free (it names only the entry state), so this segment
     passes the cut's fact on unchanged.
   Earlier re-fits kept: caw_carry carries the room counts caw_cnt D (second conjunct), passed on unchanged (no
   allocator step here); caw_at_null carries the progress fact caw_prog D [] S3 and the End cut's r = 1 arm asks it
   at the same S3; fpre's last conjunct frm_zero (fp_csr fx) is not read here; the statement names the entry float
   state explicitly, (fx := fx) (a local float state of the context is an instance candidate for a later implicit
   FPState).
   THE INPUTS (BY PATH; this file Requires them and changes none; blobs as the kit's cut preset-tree-at-2026-10-30T04-57-22Z.tsv (sha256 652fe98064b9; internal record) carries them):
   the base of record above (its header lists the listing, the texts and the engine set of record):
   lib/A/Listing_prog.v 7ed1529926bd (slots 658..661 = +112..+124; the alias row :7283), lib/A/PRH_Base.v
   ef7c8ca98529 (prh_pst with the row (pi_g_own_ran_out, pi_gz_own_ran_out); prh_glob / prh_ledger with most and own,
   the named projections), lib/A/PRH_FnCheck.v c40cf3fdcd2a, lib/A/PRH_Img.v 934516a622e8 (the #102 A' record),
   engine: lib/Reusable/YC1fPx.v 7814b594066f (paj_run_to_x_m_inv, the mixed-write runner: frame bytes or a program
   static of PST), YC1fP.v (pa_entry_st_ok_full, regs_kept_of_st_ok_pi), YCbqG.v 219748197d6b (ajournal_x read by
   ajx_img / ajx_ar, alx_blocks, blk_img_x), YGcallcf.v / YG0lawscf.v (the cf instance's laws), YSRrMemnorm.v,
   YImgTop.v (IMG_TOP, the base's cwi_hi bound); lib/A/Prog/S1Ledger.v 8cf15eeb6311 (prh_ledger_iff,
   prh_lblocks_kept, prh_ledger_hblock, prh_val_mem_keep); lib/A/Prog/PRW_StepKit.v 0df3991c13f4
   (st_ok_region_nth, field_of_region).
   THE CODE (the A' twin's disassembly in the internal file check_as_written.A_new.s, lines 29-32; DERIVED byte offsets from the entry):
     +112  auipc a0                       listing PHi (a0) 11: a0 = the hi atom A_HI 11
     +116  addi s1, zero, 1               s1 = 1 (r)
     +120  sb s1, 1304(a0)                a PW slot the certificate checks as a word only: its target is the alias row
                                          (SOff (A_HI 11) 1304, SOff (A_OBJ 13) 0) of A_alias_hints, i.e. g_own_ran_out
                                          (the base's cwi_own: VAL (A_OBJ 13) = pi_g_own_ran_out); a program static of
                                          prh_pst (Batch 1's row), so the runner's write premise holds by its PST arm
     +124  j +300                         to CAW_PC_END, memory and every register but a0 / s1 as at +112
   THE POST AT +300 (caw_at_END, r = 1, ownv = 1, with the cut's progress fact caw_prog D [] S3: the refused malloc
   made no event and nothing since moved S; and the cut's outcome fact caw_dead D, which names only the entry state):
   the journal from entry by the runner (the PST write, ajournal_x_exec_mixed); the saved slots
   [sp0 - 32, sp0) by the runner's frame (only the one byte at VAL (A_OBJ 13) moved); the ledger caw_ledger D .. 1
   (prh_ledger at the entry's values with cw_most and own = 1): its five value statics and g_most are other rows of
   prh_pst (apart by computation on prh_img_A), g_own_ran_out is the byte the `sb` wrote, read off the run's region
   wa1_rg (its one chunk CVal 1 (SLit 1); PRW_StepKit.field_of_region), and a harness head (a - cf_head + i, i < 8)
   never meets the byte: the block base a - cf_head is 16-aligned (alx_blocks) and so is the byte (computation), so a
   meeting is at i = 0, a block byte, which blk_img_x keeps off the image while the byte is an image byte
   (cwi_pst_img); the read-only view by wa1_rod_keep (the journal from entry with FP = [] and the base's cwi_pst_rw);
   room, blocks, the progress fact, the outcome fact, the room counts caw_cnt D, Hp unchanged (no allocator step).
   NAMED ARGUMENTS (Section hypotheses, owners in brackets): CWI : caw_img B (the base's image facts of PA and B,
   proved at the instance [a Theorem Labs lane / the instantiation file; cwi_pst_ok reads B: a Theorem Labs lane]). This segment reads three of
   them that the base's caw_img gained for it (Caw102A_Base.v
   b11cb55938ad; they were this file's wa1_img fields wa1i_*, the same texts):
     cwi_hi11  : VAL (A_HI 11) + 1304 = VAL (A_OBJ 13)  - the hi / lo pair of the `sb` (Listing_prog.v 7ed1529926bd
                  :7283's row; at PI_prog_A by PAImg_prog.v 505a51ff7d08 A_alias_hints_ok). Without it the parametric
                  PA may put the `sb` anywhere: the certificate pins A_HI 11 only to the auipc word of PA's own table.
                  The cno base states the same fact for its pair as cni_hi9 (Cno102A_Base.v, cn_img).
     cwi_pst_ok : forall a, Exists (in_zr a) prh_pst -> in_img segs a /\ ~ Exists (in_zr a) (as_owned_static B) -
                  the mixed-write runner's PST_ok (YCbqG.v :755); the cno base's cni_pst_ok, the padded base's
                  pdi_pst_ok, FuzzFree.v :414-415's form. It reads B (the runtime's owned statics), so it is proved
                  where B is bound, by computation [the kit, as FuzzFree.v :414-415's pal_pst_ok]; the other two read PA only
                  and are proved at PI_prog_A by computation [a Theorem Labs lane / the instantiation file].
     cwi_pst_seg : forall a, Exists (in_zr a) prh_pst -> YK11.seg_rom segs (Z_to_bv 64 a) <> None - a program
                  static is a byte its segment holds, so with cwi_pst_rw it is writable_at for every memory (the
                  region's write window); the cno base's cni_pst_seg, S1ImgA.v pst_wv_A's fact. Without it a
                  parametric segment may end its bytes before the static and the `sb` faults when memory has none.
   The cut state seats the byte's band as the atom fact (A_OBJ 13, [0, YImgTop.IMG_TOP]) (pa_obj_img + cwi_hi): the
   engine's write-window check against the shadow span (YCbn.v cells_safe_b) needs a range for the region's base.
   P / PLAW: the generic invariant and its laws [the top's instantiation: caw_mn_laws of the base].
   NOT a Section hypothesis here: the room counts caw_cnt D (entry premises of the batch text; the top supplies them by
   the base's caw_pre_cnt) reach this segment inside caw_at_null's carry and leave it unchanged in caw_at_END's carry.
   NO REPORT / TRAP / ABORT SITE in +112..+300 (the `sb` is not instrumented; the plan's 5.3 row WA1).
   Numerals: 112 / 300 (DERIVED offsets: CAW_PC_NULL, CAW_PC_END of the base); 1304 (DERIVED: the `sb`'s
   displacement 0x518, Listing_prog.v :675's word 0x50950c23); 11 / 13 (DERIVED: the listing's hi index and object
   number); 1 (LENGTH: the byte g_own_ran_out; WORD: r); 8 (LENGTH: a word, a head); 16 (DERIVED: the blocks law's
   alignment); 32 / 33 (DERIVED: the engine's atom numbering); 2 ^ 44 / 2 ^ 64 (bounds); register numbers (WORD).
   No ADDRESS literal. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x YC1fPx YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcallcf YG0lawscf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PresetRoomPos PresetRun PresetReqAt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Img PRH_Reader PRH_FnEx PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import Caw102A_Base.
(* st_ok_region_nth / field_of_region (the cut's g_own_ran_out byte at +300) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require PRW_StepKit.
(* PRW_StepKit loads YF0v.v, which turns zify's euclidean-division equations off globally; back on here (as WA2) *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* the PLAIN build's sink instance is loaded transitively here; it must never fill an ASan sink argument *)
#[global] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* the static byte g_own_ran_out, the image object A_OBJ 13: one byte, written, no chunk (its old value is not read) *)
Definition wa1_rg : YP09.region := YP09.mkRegion (Some (A_OBJ 13)) 0 1 0 1 [].
(* the engine's shadow arguments: no shadow check runs in +112..+300 *)
Definition WA1_Bx : sv := SOff 33 0.
Definition WA1_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* the symbolic state at the cut (+112): every register its own atom, the byte, its address band below the image
   top (the engine's write-window check against the shadow span needs it), and the `sb`'s alias row *)
Definition wa1_ss0 : sstate :=
  mkSS (CAW_OFF + CAW_PC_NULL) sr_atoms [wa1_rg] None
    (mkFacts [(A_OBJ 13, mkAF 0 YImgTop.IMG_TOP 0)] [] [(SOff (A_HI 11) 1304, SOff (A_OBJ 13) 0)]).
(* the registers no instruction of the segment writes (sp, gp, tp, s0, s2 .. s11) *)
Definition WA1_KEPT : list (bv 5) := [2; 3; 4; 8; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

(* a goal `In r l` for a literal register r of a literal list *)
Ltac wa1_in := cbn; repeat (first [left; reflexivity | right]).

Lemma wa1_kept_sub : forall r : bv 5, In r [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> In r WA1_KEPT.
Proof. intros r Hr. cbn in Hr. repeat (destruct Hr as [<- | Hr]; [wa1_in |]). destruct Hr. Qed.

(* find_segment over a segment list (YL0b / PSstrlen's shape): its hit holds the address; an address of a listed
   segment has a hit *)
Lemma wa1_find_spec : forall (sl : list Segment) x n s, find_segment sl x n = Some s ->
  In s sl /\ Z.of_N (seg_base s) <= x /\ x + n <= Z.of_N (seg_base s) + Z.of_N (seg_size s).
Proof.
induction sl as [|s0 r IH]; intros x n s H; cbn in H; [discriminate H|].
destruct (Z.leb (Z.of_N (seg_base s0)) x && Z.leb (x + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0))) eqn:E.
- injection H as <-. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1, E2.
  split; [left; reflexivity | lia].
- destruct (IH x n s H) as (Hi & H1 & H2). split; [right; exact Hi | lia].
Qed.
Lemma wa1_find_some : forall (sl : list Segment) x,
  (exists sg, In sg sl /\ Z.of_N (seg_base sg) <= x < Z.of_N (seg_base sg) + Z.of_N (seg_size sg)) ->
  find_segment sl x 1 <> None.
Proof.
induction sl as [|s0 r IH]; intros x (sg & Hin & Hr); [destruct Hin|]. cbn.
lazymatch goal with |- (if ?b then _ else _) <> None => destruct b eqn:E end; [discriminate|].
destruct Hin as [<- | Hin].
- exfalso. apply andb_false_iff in E as [E | E]; apply Z.leb_gt in E; lia.
- apply IH. exists sg. split; [exact Hin | exact Hr].
Qed.

Section wa1. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Context {PA : PAImg A_prog_listing}.
#[local] Existing Instances CW_PrhImg CW_PAListing CW_RL.
#[local] Notation segs := (@pa_segs _ A_prog_listing PA).
#[local] Notation VAL := (@pa_val _ A_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable SK : YI16.sink_head.
Variable CTX0 : list (list Z).
(* the base's image facts of PA and B (cwi_hi11 / cwi_pst_ok / cwi_pst_seg among them) [a Theorem Labs lane / the instantiation
   file; cwi_pst_ok reads B: a Theorem Labs lane] *)
Hypothesis CWI : caw_img (PA := PA) B.
(* the cf instance's laws (AR_laws_ok_cf at YGcallcf's bridge), as FuzzFree.v / Caw102A_WA4.v *)
Let LAWS_cf : AR_laws_cf segs B := AR_laws_ok_cf segs B.
Let LAWS : AR_laws_x segs B (ARcfx B) cf_head := AR_laws_x_xs segs B LAWS_cf.
(* the generic invariant and the runner laws (no call in the segment) *)
Variable P : (word -> option byte) -> Prop.
Hypothesis PLAW : srr_inv_laws segs P.

(* a read-only image byte is an image byte *)
Lemma wa1_ro_img : forall a, in_roP segs (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) a -> in_img segs a.
Proof.
intros a [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)].
Qed.

(* the read-only view crosses a journal with an empty footprint (the statics are outside it: cwi_pst_rw) *)
Lemma wa1_rod_keep : forall STK sp0 ly S Hp W mem md ly' S' Hp' W' mem' md' k,
  ajournal_x (SK := SK) segs B prh_pst (ARcfx B) STK sp0 [] ly S Hp W mem md [] ly' S' Hp' W' mem' md' k ->
  arodata_okP segs (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) B (aview segs (w_H W) mem) ->
  arodata_okP segs (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) B (aview segs (w_H W') mem').
Proof.
intros STK sp0 ly S Hp W mem md ly' S' Hp' W' mem' md' k HJ HRO a Hro Hno Hne.
pose proof (ajx_img HJ) as J11.
rewrite (J11 a (wa1_ro_img a Hro) Hno Hne (fun Hq => cwi_pst_rw CWI a Hq Hro) (fun Hs => False_ind _ (sink_closed_nil Hs))).
exact (HRO a Hro Hno Hne).
Qed.

(* a program static is writable whatever the memory holds: it is an image byte (cwi_pst_img) of no read-only
   segment (cwi_pst_rw) that its segment holds (cwi_pst_seg), so wview falls back to that writable segment's byte *)
Lemma wa1_writable : forall (m : word -> option byte) a, Exists (in_zr a) prh_pst -> writable_at segs m a.
Proof.
intros m a Ha. pose proof (cwi_pst_img CWI a Ha) as Hi. pose proof (cwi_pst_rw CWI a Ha) as Hro.
pose proof (cwi_pst_seg CWI a Ha) as Hsr.
pose proof (@pa_segs_low _ _ PA a Hi) as Hlow. pose proof asan_consts as (_ & _ & _ & _ & C5).
unfold writable_at, wview. destruct (m (Z_to_bv 64 a)); [discriminate|].
rewrite unsigned_lit_small by lia.
destruct (find_segment _ _ _) as [sg|] eqn:Ef; [| exfalso; exact (wa1_find_some segs a Hi Ef)].
destruct (wa1_find_spec _ _ _ _ Ef) as (Hin & H1 & H2).
destruct (seg_writable sg) eqn:Ew; cbv beta iota.
- destruct (segment_byte_at (seg_bytes sg) (Z.to_N (a - Z.of_N (seg_base sg)))) eqn:Eb; [discriminate|].
  exfalso. apply Hsr. unfold YK11.seg_rom, memory_read. change (Z.of_N 1) with 1.
  rewrite unsigned_lit_small by lia. rewrite Ef.
  destruct (seg_readable sg); [|reflexivity].
  change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes]. rewrite Eb. reflexivity.
- exfalso. apply Hro. left. exists sg. split; [exact Hin|]. split; [exact Ew | lia].
Qed.

(* the runner's frame: off the byte VAL (A_OBJ 13), the memory is unchanged *)
Lemma wa1_keep : forall E (m m' : word -> option byte) a,
  frame_of E [wa1_rg] m m' -> bv_unsigned (ew E (A_OBJ 13)) = VAL (A_OBJ 13) ->
  0 <= a < 2 ^ 64 -> a <> VAL (A_OBJ 13) -> mbyte segs m' a = mbyte segs m a.
Proof.
intros E m m' a HF Hb Ha Hne. unfold mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
intros (r & [<- | []] & Hr). unfold wa1_rg in Hr.
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr.
rewrite Hb, unsigned_lit_small in Hr by exact Ha. lia.
Qed.

(* a value cell apart from the byte keeps its value across the frame *)
Lemma wa1_cell_keep : forall (m m' : word -> option byte) c (w : nat) v,
  (forall a, 0 <= a < 2 ^ 64 -> a <> pi_g_own_ran_out -> mbyte segs m' a = mbyte segs m a) ->
  ((0 <=? c) && (c + Z.of_nat w <=? 2 ^ 64) &&
   ((c + Z.of_nat w <=? pi_g_own_ran_out) || (pi_g_own_ran_out + 1 <=? c)))%bool = true ->
  val_mem segs m c w v -> val_mem segs m' c w v.
Proof.
intros m m' c w v HK Hb Hv. apply andb_prop in Hb as [Hb Ho]. apply andb_prop in Hb as [H0 H1].
apply Z.leb_le in H0, H1.
apply (prh_val_mem_keep (L := A_prog_listing) (PA := PA) _ _ _ _ _ Hv). intros i Hi.
apply HK; [lia|]. apply orb_prop in Ho as [Ho | Ho]; apply Z.leb_le in Ho; lia.
Qed.

(* a symbolic state at listing offset CAW_OFF + o is the cut configuration caw_cfg at o *)
Lemma wa1_leaf : forall (fz : YK11.FPState) (W : world segs) E ss ms md o (G : world segs -> config -> Prop),
  st_ok_pi (fx := fz) segs VAL E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = CAW_OFF + o ->
  SRr segs W (caw_cfg fz o (ms_regs ms) (ms_mem ms) md) G -> SRr segs W (mkCfg ms md) G.
Proof.
intros fz W E ss ms md o G HS Hrv Hpc H.
rewrite (st_ok_pi_restrict_mkst (fx := fz) _ _ _ _ HS Hrv), Hpc.
unfold caw_cfg, caw_pc in H. rewrite Z.add_assoc. exact H.
Qed.

Lemma caw_wa1_holds : caw_seg_WA1 (fx := fx) B SK CTX0 P.
Proof.
intros Q D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k HAT KEND HPM.
destruct HAT as ((HPRE & HCNT & HFL & HJ & HKR & HSP & HSV & EHp & HRL & HROD) & HRP & HDEAD & R10 & R8 & R9 & EAB &
  HERR & HOOM & HLG).
unfold caw_ledger in HLG.
(* caw_pre BY NAME: the entry's fpre (caw_pre_fpre) *)
pose proof (caw_pre_fpre (fx := fx) B CTX0 D HPRE) as HFP.
pose proof HFP as (HPX & HROD0 & _).
pose proof HPX as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
unfold caw_J in HJ.
pose proof (ajx_ar HJ) as HAR3.
pose proof (cwi_own CWI) as Cown.
pose proof (cwi_hi11 CWI) as Chi.
pose proof (@pa_val_range _ _ PA (A_OBJ 13)) as Ro13.
pose proof (@pa_val_range _ _ PA (A_HI 11)) as Rhi.
pose proof (@pa_obj_img _ _ PA 13 ltac:(lia)) as Hobj.
pose proof (cwi_hi CWI) as Chi8.
pose proof asan_consts as (C1 & _).
assert (Esp0 : cw_sp0 D = spZ (cw_regs D)) by reflexivity.
assert (Rsp : YM05.alloc_ceiling <= cw_sp0 D <= 2 ^ 47) by (rewrite Esp0; lia).
assert (Htop : VAL (A_OBJ 13) + 8 <= YImgTop.IMG_TOP) by lia.
unfold YImgTop.IMG_TOP in Htop.
(* the byte is the prh_pst row of g_own_ran_out (Batch 1), 16-aligned *)
assert (Hgz : 1 <= Z.of_nat pi_gz_own_ran_out) by (unfold Z.le; vm_compute; discriminate).
assert (Hown_pst : Exists (in_zr (VAL (A_OBJ 13))) prh_pst).
{ rewrite Cown. unfold prh_pst. do 6 apply Exists_cons_tl. apply Exists_cons_hd.
  unfold in_zr. cbn [fst snd]. lia. }
assert (A16 : VAL (A_OBJ 13) mod 16 = 0) by (rewrite Cown; vm_compute; reflexivity).
pose proof (cwi_pst_img CWI _ Hown_pst) as Himg13.
(* ---- the cut's symbolic state: the registers, the byte's region, the alias row ---- *)
set (E := Eimg (Ereg regs3 [])).
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (Uo13 : bv_unsigned (ew E (A_OBJ 13)) = VAL (A_OBJ 13)).
{ unfold E. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia). apply unsigned_lit_small. lia. }
assert (Uhi : bv_unsigned (ew E (A_HI 11)) = VAL (A_HI 11)).
{ unfold E. rewrite Eimg_img by (unfold A_HI, A_TEXT, A_LIM; lia). apply unsigned_lit_small. lia. }
assert (AG : env_agree 32 (Ereg regs3 []) E).
{ unfold E. split; [intros i Hi; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. }
assert (HS : st_ok_pi (fx := fy) segs VAL E wa1_ss0
  (restrict (w_H W3) (@YK11.mkst fy regs3 (Z_to_bv 64 (BASE + (CAW_OFF + CAW_PC_NULL))) mem3 (YK11.seg_rom segs)))).
{ rewrite restrict_mkst_fx. unfold wa1_ss0. apply pa_entry_st_ok_full.
  - unfold E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold region_ok, wa1_rg.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Uo13.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. replace o with 0 by lia. rewrite Z.add_0_r. apply wa1_writable. exact Hown_pst.
  - cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [|split; [exact I|]].
    { split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Uo13.
      split; [unfold YImgTop.IMG_TOP; lia|]. split; [rewrite Z.pow_0_r; apply Z.mod_1_r | lia]. }
    split; [|exact I].
    cbn [sv_denot]. rewrite Uhi, Uo13, Chi, Z.add_0_r. reflexivity. }
assert (SHOK : sh_ok segs WA1_Bx [] E (mrestrict (w_H W3) mem3)) by (unfold sh_ok; apply Forall_nil).
pose (RUNTO := paj_run_to_x_m_inv (fx := fy) (SK := SK) (PL := CW_PAListing) (PI := PA) B prh_pst (ARcfx B) LAWS
  (cwi_pst_ok CWI) P PLAW).
unfold caw_cfg, caw_pc. rewrite <- Z.add_assoc.
(* ---- +112 .. +300: auipc, li s1 1, sb s1 -> g_own_ran_out, j: the PST write ---- *)
paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM WA1_Bspan (CAW_OFF + CAW_PC_END).
all: try solve
  [ let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
    intros a (r & Hin & Hr); right; unfold wa1_ss0 in Hin; cbn [ss_mem In] in Hin;
    destruct Hin as [<- | []]; unfold wa1_rg in Hr;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite Uo13 in Hr;
    replace a with (VAL (A_OBJ 13)) by lia; exact Hown_pst ].
lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into ms2 end.
assert (KR2 : forall r, In r WA1_KEPT -> getr (ms_regs ms2) r = getr regs3 r)
  by exact (regs_kept_of_st_ok_pi (fx := fy) _ _ _ regs3 [] WA1_KEPT HS AG ltac:(vm_compute; reflexivity)).
(* the frame: only the byte VAL (A_OBJ 13) moved *)
assert (KB : forall a, 0 <= a < 2 ^ 64 -> a <> VAL (A_OBJ 13) ->
  mbyte segs (rdW W3 (ms_mem ms2)) a = mbyte segs (rdW W3 mem3) a).
{ intros a Ha Hne. unfold wa1_ss0 in HFr. cbn [ss_mem] in HFr. exact (wa1_keep E _ _ a HFr Uo13 Ha Hne). }
assert (KB' : forall a, 0 <= a < 2 ^ 64 -> a <> pi_g_own_ran_out ->
  mbyte segs (rdW W3 (ms_mem ms2)) a = mbyte segs (rdW W3 mem3) a).
{ intros a Ha Hne. apply KB; [exact Ha | rewrite Cown; exact Hne]. }
(* the four saved words [sp0 - 32, sp0) lie on the stack, far above the image *)
assert (HSV' : caw_saved D W3 (ms_mem ms2)).
{ unfold caw_saved in HSV |- *. destruct HSV as (V1 & V2 & V3 & V4).
  repeat split;
    (eapply (prh_val_mem_keep (L := A_prog_listing) (PA := PA)); [eassumption | intros i Hi; apply KB; lia]). }
(* the cut's byte at +300: the region wa1_rg of the state there holds s1 = 1 at its offset 0 (the `sb`) *)
pose proof (PRW_StepKit.st_ok_region_nth segs _ _ _ 0 _ HS eq_refl) as Hreg. cbn [ms_mem restrict] in Hreg.
assert (Vown : val_mem segs (rdW W3 (ms_mem ms2)) (VAL (A_OBJ 13) + 0) (N.to_nat 1) 1).
{ apply (PRW_StepKit.field_of_region segs _ _ (A_OBJ 13) (VAL (A_OBJ 13)) _ _ _ _ _ 0 1 (SLit 1) 1 Hreg).
  - exact Uo13.
  - cbn. left. reflexivity.
  - reflexivity.
  - split; [lia | reflexivity].
  - unfold Z.le. discriminate. }
assert (HOWN1 : prh_own W3 (ms_mem ms2) 1).
{ split; [|right; reflexivity]. rewrite <- Cown. rewrite Z.add_0_r in Vown. change (N.to_nat 1) with 1%nat in Vown.
  change pi_gz_own_ran_out with 1%nat. exact Vown. }
(* the ledger at own = 1 (caw_ledger D .. 1): its five value statics and g_most are other prh_pst rows, kept by the
   frame; g_own_ran_out is the byte just written; a head never meets the byte (16-alignment, blk_img_x) *)
assert (HLG' : prh_ledger B ly3 S3 Hp3 W3 (ms_mem ms2) (cw_Lam D) (cw_peak D) (cw_cnt D) (cw_fail D) (cw_ran D)
  (cw_most D) 1).
{ pose proof HLG as HLb. apply prh_ledger_bounds in HLb. destruct HLb as (Bl & Bp & Bc & Bf & Br).
  pose proof HLG as Vl. apply prh_ledger_live in Vl.
  pose proof HLG as Vp. apply prh_ledger_peak in Vp.
  pose proof HLG as Vc. apply prh_ledger_count in Vc.
  pose proof HLG as Vf. apply prh_ledger_fail in Vf.
  pose proof HLG as Vr. apply prh_ledger_ran in Vr.
  pose proof HLG as Vm. apply PRH_Base.prh_ledger_most in Vm.
  apply (proj2 (prh_ledger_iff (L := A_prog_listing) (PA := PA) B _ _ _ _ _ _ _ _ _ _ _ _)).
  split.
  - unfold prh_glob. refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj HOWN1 _))))))).
    + eapply wa1_cell_keep; [exact KB' | vm_compute; reflexivity | exact Vl].
    + eapply wa1_cell_keep; [exact KB' | vm_compute; reflexivity | exact Vp].
    + eapply wa1_cell_keep; [exact KB' | vm_compute; reflexivity | exact Vc].
    + eapply wa1_cell_keep; [exact KB' | vm_compute; reflexivity | exact Vf].
    + eapply wa1_cell_keep; [exact KB' | vm_compute; reflexivity | exact Vr].
    + destruct Vm as (Vm & Rm'). split; [|exact Rm'].
      eapply wa1_cell_keep; [exact KB' | vm_compute; reflexivity | exact Vm].
    + exact (conj Bl (conj Bp (conj Bc (conj Bf Br)))).
  - pose proof HLG as HLB.
    apply (proj1 (prh_ledger_iff (L := A_prog_listing) (PA := PA) B _ _ _ _ _ _ _ _ _ _ _ _)) in HLB as [_ HB].
    apply (prh_lblocks_kept (L := A_prog_listing) (PA := PA) B ly3 S3 Hp3 W3 mem3 ly3 S3 Hp3 W3 (ms_mem ms2) _ HB).
    + intros a kk i Hin Hi.
      destruct (prh_ledger_hblock (L := A_prog_listing) (PA := PA) B ly3 S3 Hp3 W3 mem3 _ _ _ _ _ a kk _ _ HLG Hin)
        as (Hk0 & Hb & _).
      destruct (alx_blocks _ _ _ LAWS ly3 S3 Hp3 W3 mem3 md3 _ _ HAR3 Hb) as (Hb16 & Hb4k & Hbc & _).
      assert (Hrq : 1 <= req_size (kk + cf_head))
        by (pose proof cf_head_nonneg; unfold req_size; destruct (Z.eqb_spec (kk + cf_head) 0); lia).
      apply KB; [lia|]. intros Heq.
      pose proof (Z.div_mod (a - cf_head) 16 ltac:(lia)) as D1. rewrite Hb16 in D1.
      pose proof (Z.div_mod (VAL (A_OBJ 13)) 16 ltac:(lia)) as D2. rewrite A16 in D2.
      assert (Ei : i = 0) by lia. subst i.
      apply (blk_img_x _ _ _ LAWS ly3 S3 Hp3 W3 mem3 md3 _ _ (a - cf_head + 0) HAR3 Hb); [lia|].
      rewrite Heq. exact Himg13.
    + intros a kk _ H. exact H.
    + apply Permutation_refl. }
apply (wa1_leaf fy W3 _ _ ms2 _ CAW_PC_END _ HS eq_refl ltac:(vm_compute; reflexivity)).
apply (KEND fy ly3 S3 Hp3 W3 (ms_regs ms2) (ms_mem ms2) _ k 1 1); [|exact HPM].
(* the End cut, the r = 1 arm with the cut's progress fact caw_prog D [] S3 (the refused malloc made no event) and
   the cut's outcome fact caw_dead D (state-free: it names only the entry state) *)
split; [|split; [| split; [left; split; [reflexivity | split; [reflexivity | exact (conj HRP HDEAD)]]
  | exact (conj EAB HLG')]]].
- unfold caw_carry.
  split; [exact HPRE|]. split; [exact HCNT|]. split; [exact HFL|]. split; [unfold caw_J; exact HJ|].
  split; [intros r Hr; rewrite (KR2 r (wa1_kept_sub r Hr)); exact (HKR r Hr)|].
  split; [unfold spZ; rewrite (KR2 2%bv ltac:(wa1_in)); exact HSP|].
  split; [exact HSV'|]. split; [exact EHp|]. split; [exact HRL|].
  exact (wa1_rod_keep _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HROD0).
- rewrite (st_ok_pi_restrict_reg (fx := fy) _ _ _ _ 9%bv HS). reflexivity.
Qed.
End wa1.

Print Assumptions caw_wa1_holds.
