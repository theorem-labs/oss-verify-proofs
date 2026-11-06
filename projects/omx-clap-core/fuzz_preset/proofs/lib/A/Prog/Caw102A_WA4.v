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
(* fuzz_preset lib/A, the #102 re-walk of check_as_written on image A' (ASan build), lane CawA102R: segment WA4.
   rule 24: no function proved. rule 24: proves no function (kind: segment lemma).
   INT102-READY on the kit's cut 7cdbb61b5fa0 (prepared on the batch kit's tip e45217a4c7ba).
   WHAT IT PROVES: caw_wa4_holds : caw_seg_WA4 (fx := fx) B SK CTX0 P (Caw102A_Base.v), for an ABSTRACT memory
   invariant P with PLAW : srr_inv_laws segs P and PCALL : srr_inv_call segs P (the segment calls one text,
   fuzz_alloc_ran_out, whose text has no memnorm entry premise, so no srr_inv_mn). out_of_memory () inlined, from
   CAW_PC_OOM (+252) to CAW_PC_CHK (+276, continuation caw_k_CHK); the exit to CAW_PC_END (+300) is refuted twice.
   BASE OF RECORD (as at the batch-prep base, lib/A/Prog/Caw102A_Base.v;
   its header lists the listing, the cut's kit texts and the engine set of record; its kit Caw102A_Kit.v 3d241a90402d
   is not Required here).
   THE INPUTS (BY PATH, as the kit's cut carries them; this file Requires them, it changes none; the blob pins are the kit's cut's, recorded by
   git hash-object there): lib/A/PRH_FnAlloc.v 4d8aeba047e5 (tfuzz_alloc_ran_out_specX, :193 on this tree: binders
   most own; its premise and its post's last conjunct are `prh_ledger .. ran most own`, its post's S' = S),
   lib/A/PRH_Base.v (fpre :1004-1026, its last conjunct frm_zero (fp_csr fx), FRM0-ENTRY; prh_own :805,
   prh_ledger :826, PRH_Base.prh_ledger_own :856; S1Ledger.v's prh_ledger_own, the malloc OWN frame lemma, is NOT
   used), PRH_Img.v 934516a622e8; lib/A/Listing_prog.v 7ed1529926bd (slots 693..698 = +252..+272); engine (the P'' set
   of the kit's cut): lib/Reusable/YCbqG.v (the journal, read through its ajxR_* projections), YC80x.v 14f84f225e8f,
   YC1fPx.v 7814b594066f (paj_run_x_inv / paj_run_to_x_inv and their tactics), YC1fP.v 96e2e49ece5f (paj_branch,
   psrr_branch_tok, pa_entry_st_ok_full), YCbqGcall.v c1fcd07d2537 (aj_call_x_sp), YSRrMemnorm.v 5ffa8525936b
   (srr_inv_call), YGcallcf.v 8645fa6a514f / YG0lawscf.v 17c91dd453e4 (the cf instance's laws); lib/A/Prog/PRW_StepKit.v
   0df3991c13f4 (pa_slot_lt_ceil_b, fpre's raZ bound at the call, evar-free).
   WHAT CHANGED (the batch-prep base; the previous state was this file bd7ed4c072d9 on the base deec9ccf853b with the P''
   journal fixes of the P'' trial), each forced by the batch text
   tcheck_as_written_specX (lib/A/PRH_FnCheck.v c40cf3fdcd2a :832-902):
   - the run-word list DW is gone (the text's binder and prh_univ_closure's argument): the Section variable DW is
     removed, so the statement is caw_seg_WA4 (fx := fx) B SK CTX0 P. This is the only statement change.
   - caw_pre now has 27 conjuncts (Caw102A_Base.v:229-256: the room counts sec_cnt / ccnt24 follow room_live_cf, :862-863,
     then the hull budget and HPOS), so a positional pattern over it mis-binds: caw_pre is read BY NAME, through the
     base's projections caw_pre_fpre / _rc / _doc / _size / _data0 / _data62 / _ran / _live / _max / _frames (the parts
     this segment reads: fpre, cw_ran D = 0 at +272, and the arithmetic facts its lia steps may use).
   - caw_at_END's r = 1 arm gains caw_dead D (the text's OUTCOME, :879-888): this segment builds no caw_at_END (both
     exits to +300 are REFUTED; KEND stays the statement's continuation argument), so nothing moves with it. caw_at_OOM,
     caw_at_CHK and caw_carry are unchanged; caw_cnt D passes from the cut's carry to caw_at_CHK's as it stands.
   Unchanged: the byte the +256 load reads is PRH_Base.prh_ledger_own of the cut's ledger (own 0: the +264 exit is
   REFUTED); the call takes the cut's ledger at `cw_most D` and own 0, and its post gives the ledger at the same values
   at W2 / mem2, which is caw_at_CHK's last conjunct as it stands; caw_prog D (caw_evs D) S at both cuts (the callee
   keeps S); the callee's fpre takes frm_zero from the cut's caw_fl fy, first conjunct.
   ACROSS THE CALL: P by PCALL from the text's fQmn keep; the read-only view by wa4_rod_keep (the journal from entry and
   the base's cwi_pst_rw); the saved slots [sp0 - 32, sp0) by the callee's journal (they lie above its window); the
   registers WA4_KEPT by aregs_preserved; S' = S, Hp' = Hp, ablocks and the ledger (most, own 0) from the text's post.
   THE CODE (the A' twin's disassembly in the internal file check_as_written.A_new.s of the plan, the internal file PLAN-cno-caw-102.md; DERIVED byte offsets
   from the entry):
     +252  auipc a0 ; +256 lbu a0 <- g_own_ran_out (listing PHi / PLdHi (A_OBJ 13) SZ1 unsigned; cwi_own: VAL (A_OBJ 13)
           = pi_g_own_ran_out; the byte is the region wa4_rg below, its value the atom 32 = 0, caw_at_OOM's ledger at own 0)
     +260  li s1, 1
     +264  bnez a0 -> +300: REFUTED (wa4 branch at +264: a0 = the atom 32 = 0, E32)
     +268  jal fuzz_alloc_ran_out (its text, through aj_call_x_sp, o = -80; a0 = ran on return)
     +272  bnez a0 -> +300: REFUTED (wa4 branch at +272: a0 = ran = cw_ran D = 0 by caw_pre's `cw_ran D = 0`)
     +276  fall through: caw_k_CHK with want (s2 kept), ownv = 0, the ledger the text's post gives (own 0)
   NAMED ARGUMENTS (Section hypotheses, owners in brackets): CWI : caw_img (the base's image facts of PA, proved at the
   instance [a Theorem Labs lane / the instantiation file]); HRANOUT : fuzz_alloc_ran_out's text, float-generic (it leaves the
   float state alone; the call runs at the cut's fy) [a Theorem Labs lane, discharged by that text's walk]; P / PLAW / PCALL: the
   generic invariant and its laws [the top's instantiation: caw_mn_laws / caw_mn_call of the base]. No boundary
   premise (the cut's ledger, caw_ledger D .. 0, carries the byte g_own_ran_out).
   REFUTED SITES: (1) +264 taken: E32 gives the atom 32 = Z_to_bv 64 0, so `branch_taken BC_NE (a0) (SLit 0) = true`
   computes to `false = true` (vm_compute on the closed condition; discriminate). (2) +272 taken (the r = 1 exit
   through fuzz_alloc_ran_out): the text's post gives a0 = w64 ran with ran = cw_ran D, caw_pre gives cw_ran D = 0 (E10:
   the atom 10 of the state at +272 is Z_to_bv 64 0), the same computation.
   Numerals: 252 / 264 / 268 / 272 / 276 / 300 (DERIVED offsets: CAW_PC_OOM, CAW_PC_RET, CAW_PC_CHK, CAW_PC_END of the
   base and this file); 80 (LENGTH: the frame, o = -80); 1 (LENGTH: the byte g_own_ran_out); 8 / 32 (LENGTH: a word, the
   saved-slot band); 32 / 33 (DERIVED: the engine's first extra atom); 2 ^ 31 / 2 ^ 40 / 2 ^ 44 / 2 ^ 64 (bounds);
   register numbers (WORD). No ADDRESS literal. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x YC1fPx YSRrMemnorm YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcallcf YG0lawscf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PresetRoomPos PresetRun PresetReqAt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Img PRH_Reader PRH_FnEx PRH_FnCheck PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require PRW_StepKit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import Caw102A_Base.
(* the PLAIN build's sink instance is loaded transitively here; it must never fill an ASan sink argument *)
#[global] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* the return site of the jal at +268 (DERIVED offset) *)
Definition CAW_PC_RET : Z := 272.
(* the static byte g_own_ran_out, the image object A_OBJ 13: one read-only chunk, its value the atom 32 *)
Definition wa4_rg : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 13)) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))].
(* the engine's shadow arguments: no shadow check runs in +252..+276 *)
Definition WA4_Bx : sv := SOff 33 0.
Definition WA4_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* the symbolic states at the cut (+252) and at the return site (+272): every register its own atom *)
Definition wa4_ss0 : sstate := mkSS (CAW_OFF + CAW_PC_OOM) sr_atoms [wa4_rg] None (mkFacts [] [] []).
Definition wa4_ss1 : sstate := mkSS (CAW_OFF + CAW_PC_RET) sr_atoms [] None (mkFacts [] [] []).
(* the registers no instruction of the segment writes and fuzz_alloc_ran_out keeps (sp, gp, tp, s0, s2 .. s11) *)
Definition WA4_KEPT : list (bv 5) := [2; 3; 4; 8; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

(* a goal `In r l` for a literal register r of a literal list *)
Ltac wa4_in := cbn; repeat (first [left; reflexivity | right]).
(* the write premise of a run whose regions are read-only *)
Ltac wa4_nowr := first
  [ apply awr_ok_nil
  | let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
    intros a (r & Hin & Hr); cbn in Hin; destruct Hin as [<- | []]; cbn in Hr; lia ].

Lemma wa4_kept_sub : forall r : bv 5, In r [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> In r WA4_KEPT.
Proof. intros r Hr. cbn in Hr. repeat (destruct Hr as [<- | Hr]; [wa4_in |]). destruct Hr. Qed.

(* a callee keeps every register of WA4_KEPT *)
Lemma wa4_pres : forall regs regs', aregs_preserved regs regs' -> forall r, In r WA4_KEPT -> getr regs' r = getr regs r.
Proof.
intros regs regs' HP r Hr. cbn in Hr.
repeat (destruct Hr as [<- | Hr];
  [ first [ exact (HP 2 ltac:(unfold acallee_saved; lia)) | exact (HP 3 ltac:(unfold acallee_saved; lia))
          | exact (HP 4 ltac:(unfold acallee_saved; lia)) | exact (HP 8 ltac:(unfold acallee_saved; lia))
          | exact (HP 18 ltac:(unfold acallee_saved; lia)) | exact (HP 19 ltac:(unfold acallee_saved; lia))
          | exact (HP 20 ltac:(unfold acallee_saved; lia)) | exact (HP 21 ltac:(unfold acallee_saved; lia))
          | exact (HP 22 ltac:(unfold acallee_saved; lia)) | exact (HP 23 ltac:(unfold acallee_saved; lia))
          | exact (HP 24 ltac:(unfold acallee_saved; lia)) | exact (HP 25 ltac:(unfold acallee_saved; lia))
          | exact (HP 26 ltac:(unfold acallee_saved; lia)) | exact (HP 27 ltac:(unfold acallee_saved; lia)) ]
  | ]).
destruct Hr.
Qed.

Section wa4. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
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
(* the base's image facts of PA [CawA102 / the instantiation file] *)
Hypothesis CWI : caw_img (PA := PA) B.
(* fuzz_alloc_ran_out's kit text (PRH_FnAlloc.v 4d8aeba047e5 :175), at every float state [the kit] *)
Hypothesis HRANOUT : forall fz : YK11.FPState, tfuzz_alloc_ran_out_specX (fx := fz) B (ARcfx B) SK.
(* the cf instance's laws (h-mani-a8's AR_laws_ok_cf at YGcallcf's bridge), as FuzzFree.v *)
Let LAWS_cf : AR_laws_cf segs B := AR_laws_ok_cf segs B.
Let LAWS : AR_laws_x segs B (ARcfx B) cf_head := AR_laws_x_xs segs B LAWS_cf.
(* the generic invariant: the runner laws, and the call law for the one call *)
Variable P : (word -> option byte) -> Prop.
Hypothesis PLAW : srr_inv_laws segs P.
Hypothesis PCALL : srr_inv_call segs P.

(* a read-only image byte is an image byte *)
Lemma wa4_ro_img : forall a, in_roP segs (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) a -> in_img segs a.
Proof.
intros a [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)].
Qed.

(* the read-only view crosses a journal with an empty footprint (the statics are outside it: cwi_pst_rw) *)
Lemma wa4_rod_keep : forall STK sp0 ly S Hp W mem md ly' S' Hp' W' mem' md' k,
  ajournal_x (SK := SK) segs B prh_pst (ARcfx B) STK sp0 [] ly S Hp W mem md [] ly' S' Hp' W' mem' md' k ->
  arodata_okP segs (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) B (aview segs (w_H W) mem) ->
  arodata_okP segs (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) B (aview segs (w_H W') mem').
Proof.
intros STK sp0 ly S Hp W mem md ly' S' Hp' W' mem' md' k HJ HRO a Hro Hno Hne.
pose proof (ajx_img HJ) as J11.
rewrite (J11 a (wa4_ro_img a Hro) Hno Hne (fun Hq => cwi_pst_rw CWI a Hq Hro) (fun Hs => False_ind _ (sink_closed_nil Hs))).
exact (HRO a Hro Hno Hne).
Qed.
(* wa4_rod_keep over a world relation R: the journal at R (ajournal_xR), read through ajxR_img *)
Lemma wa4_rod_keepR : forall (R : world segs -> world segs -> Prop) STK sp0 ly S Hp W mem md ly' S' Hp' W' mem' md' k,
  ajournal_xR (SK := SK) segs B prh_pst (ARcfx B) R STK sp0 [] ly S Hp W mem md [] ly' S' Hp' W' mem' md' k ->
  arodata_okP segs (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) B (aview segs (w_H W) mem) ->
  arodata_okP segs (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) B (aview segs (w_H W') mem').
Proof.
intros R STK sp0 ly S Hp W mem md ly' S' Hp' W' mem' md' k HJ HRO a Hro Hno Hne.
pose proof (ajxR_img HJ) as J11.
rewrite (J11 a (wa4_ro_img a Hro) Hno Hne (fun Hq => cwi_pst_rw CWI a Hq Hro) (fun Hs => False_ind _ (sink_closed_nil Hs))).
exact (HRO a Hro Hno Hne).
Qed.

(* a symbolic state at listing offset CAW_OFF + o is the cut configuration caw_cfg at o *)
Lemma wa4_leaf : forall (fz : YK11.FPState) (W : world segs) E ss ms md o (G : world segs -> config -> Prop),
  st_ok_pi (fx := fz) segs VAL E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = CAW_OFF + o ->
  SRr segs W (caw_cfg fz o (ms_regs ms) (ms_mem ms) md) G -> SRr segs W (mkCfg ms md) G.
Proof.
intros fz W E ss ms md o G HS Hrv Hpc H.
rewrite (st_ok_pi_restrict_mkst (fx := fz) _ _ _ _ HS Hrv), Hpc.
unfold caw_cfg, caw_pc in H. rewrite Z.add_assoc. exact H.
Qed.
(* wa4_leaf over a world relation R (YA0nH.SRrG segs R in place of SRr segs) *)
Lemma wa4_leafR : forall (fz : YK11.FPState) (R : world segs -> world segs -> Prop) (W : world segs) E ss ms md o
  (G : world segs -> config -> Prop),
  st_ok_pi (fx := fz) segs VAL E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = CAW_OFF + o ->
  YA0nH.SRrG segs R W (caw_cfg fz o (ms_regs ms) (ms_mem ms) md) G -> YA0nH.SRrG segs R W (mkCfg ms md) G.
Proof.
intros fz R W E ss ms md o G HS Hrv Hpc H.
rewrite (st_ok_pi_restrict_mkst (fx := fz) _ _ _ _ HS Hrv), Hpc.
unfold caw_cfg, caw_pc in H. rewrite Z.add_assoc. exact H.
Qed.
(* the world relation past the free (the re-hide's zone) *)
#[local] Abbreviation RW := (YA0nH.wle' segs YGcfRehidePost.RZ_cf).
(* YC1fP.paj_branch over any world relation R (a branch takes no step: the case split on its condition) *)
Lemma wa4_branchR : forall (fz : YK11.FPState) (R : world segs -> world segs -> Prop) W E ss ms md Q c a b,
  st_ok_pi (fx := fz) segs VAL E ss (restrict (w_H W) ms) ->
  (branch_taken c (sv_denot E a) (sv_denot E b) = true ->
   st_ok_pi (fx := fz) segs VAL E (add_cond ss (mkAC c a b)) (restrict (w_H W) ms) ->
   YA0nH.SRrG segs R W (mkCfg ms md) Q) ->
  (branch_taken c (sv_denot E a) (sv_denot E b) = false ->
   st_ok_pi (fx := fz) segs VAL E (add_cond ss (mkAC (neg_bc c) a b)) (restrict (w_H W) ms) ->
   YA0nH.SRrG segs R W (mkCfg ms md) Q) ->
  YA0nH.SRrG segs R W (mkCfg ms md) Q.
Proof.
intros fz R W E ss ms md Q c a b HS HT HF.
destruct (branch_taken c (sv_denot E a) (sv_denot E b)) eqn:Hb.
- apply HT; [reflexivity|]. pose proof (st_ok_add_cond segs E _ _ c a b HS Hb) as H. destruct ss; exact H.
- apply HF; [reflexivity|]. pose proof (st_ok_add_cond_neg segs E _ _ c a b HS Hb) as H. destruct ss; exact H.
Qed.

Lemma caw_wa4_holds : caw_seg_WA4 (fx := fx) B SK CTX0 P.
Proof.
intros Q D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k want HAT KEND KCHK HPM.
destruct HAT as ((HPRE & HCNT & HFL & HJ & HKR & HSP & HSV & EHp & HRL & HROD) & HRP & R8 & R18 & HWANT & EAB & HLG).
(* caw_pre BY NAME (the base's projections; a positional pattern over its 27 conjuncts would mis-bind) *)
pose proof (caw_pre_fpre (fx := fx) B CTX0 D HPRE) as HFP.
pose proof (caw_pre_rc (fx := fx) B CTX0 D HPRE) as Hrc.
pose proof (caw_pre_doc (fx := fx) B CTX0 D HPRE) as Hdoc.
pose proof (caw_pre_size (fx := fx) B CTX0 D HPRE) as Hsz.
pose proof (caw_pre_data0 (fx := fx) B CTX0 D HPRE) as Hd0.
pose proof (caw_pre_data62 (fx := fx) B CTX0 D HPRE) as Hd62.
pose proof (caw_pre_ran (fx := fx) B CTX0 D HPRE) as HRAN0.
pose proof (caw_pre_live (fx := fx) B CTX0 D HPRE) as HLIVE.
pose proof (caw_pre_max (fx := fx) B CTX0 D HPRE) as HMAX.
pose proof (caw_pre_frames (fx := fx) B CTX0 D HPRE) as HFR.
pose proof HFP as (HPX & HROD0 & HSTKHI & HRAC & HFZ0).
pose proof HPX as (HAR0 & Hra0 & Hra40 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
unfold caw_J in HJ.
pose proof (ajx_ar HJ) as HAR3. pose proof (ajx_ly HJ) as Hly.
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
(* the cut's ledger at own 0: g_own_ran_out holds 0, the byte the load reads (PRH_Base's projection, not S1Ledger's) *)
assert (HOWN3 : prh_own W3 mem3 0) by (unfold caw_ledger in HLG; eapply PRH_Base.prh_ledger_own; exact HLG).
pose proof HOWN3 as (Vown & _).
pose proof (cwi_base CWI) as Cbase.
pose proof (cwi_own CWI) as Cown.
pose proof (@pa_val_range _ _ PA (A_OBJ 13)) as Ro13.
pose proof YM05.alloc_ceiling_value as Hceilv.
pose proof CAW_OFF_val as Coff.
assert (HSTKf0 : 0 <= STK_fuzz_alloc_ran_out) by (unfold Z.le; vm_compute; discriminate).
assert (HSTKc : STK_fuzz_alloc_ran_out + 80 <= STK_check_as_written) by (unfold Z.le; vm_compute; discriminate).
assert (Esp0 : cw_sp0 D = spZ (cw_regs D)) by reflexivity.
assert (Hraw : 0 <= BASE + (CAW_OFF + CAW_PC_RET) < 2 ^ 64)
  by (rewrite Cbase, Coff; unfold A_prog_base, CAW_PC_RET; lia).
(* ---- the cut's symbolic state: the registers, and the byte g_own_ran_out as the atom 32 (= 0) ---- *)
set (E := Eimg (Ereg regs3 [Z_to_bv 64 0])).
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (E32 : ew E 32 = Z_to_bv 64 0).
{ unfold E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs3 [Z_to_bv 64 0] 0). }
assert (Uo13 : bv_unsigned (ew E (A_OBJ 13)) = VAL (A_OBJ 13)).
{ unfold E. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia). apply unsigned_lit_small. lia. }
assert (AG : env_agree 32 (Ereg regs3 [Z_to_bv 64 0]) E).
{ unfold E. split; [intros i Hi; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. }
assert (HS : st_ok_pi (fx := fy) segs VAL E wa4_ss0
  (restrict (w_H W3) (@YK11.mkst fy regs3 (Z_to_bv 64 (BASE + (CAW_OFF + CAW_PC_OOM))) mem3 (YK11.seg_rom segs)))).
{ rewrite restrict_mkst_fx. unfold wa4_ss0. apply pa_entry_st_ok_full.
  - unfold E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold region_ok, wa4_rg.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Uo13.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
    apply (chunk_ok_val segs E _ (VAL (A_OBJ 13)) 0 1 (SOff 32 0) 0).
    + cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    + cbn; lia.
    + cbn; lia.
    + rewrite Z.add_0_r, Cown. replace (N.to_nat 1) with pi_gz_own_ran_out by (vm_compute; reflexivity). exact Vown.
  - cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
  - split; [exact I | split; exact I]. }
assert (SHOK : sh_ok segs WA4_Bx [] E (mrestrict (w_H W3) mem3)) by (unfold sh_ok; apply Forall_nil).
pose (RUN := paj_run_x_inv (fx := fy) (SK := SK) (PL := CW_PAListing) (PI := PA) B prh_pst (ARcfx B) LAWS P PLAW).
pose (RUNTO := paj_run_to_x_inv (fx := fy) (SK := SK) (PL := CW_PAListing) (PI := PA) B prh_pst (ARcfx B) LAWS P PLAW).
pose (BR := paj_branch (fx := fy) (L := A_prog_listing) (PI := PA)).
unfold caw_cfg, caw_pc. rewrite <- Z.add_assoc.
(* ---- +252 .. +264: auipc, lbu a0 <- g_own_ran_out, li s1 1, up to the bnez (no store) ---- *)
paj_run_tok_x_inv RUN HS HJ SHOK HPM WA4_Bspan.
all: try solve [wa4_nowr].
lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into ms1 end.
lazymatch type of HF with frame_of _ ?rs _ _ =>
  pose proof (frame_of_read_only _ rs _ _ ltac:(vm_compute; reflexivity) HF) as EM1 end.
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK WA4_Bspan.
- (* +264 TAKEN: REFUTED, a0 = the byte g_own_ran_out = the atom 32 = 0 (caw_at_OOM's ledger at own 0; E32) *)
  exfalso.
  cbn [sv_denot] in Hc.
  lazymatch type of Hc with context [ew ?Ex 32%nat] =>
    replace (ew Ex 32%nat) with (Z_to_bv 64 0) in Hc by (symmetry; exact E32) end.
  vm_compute in Hc. discriminate Hc.
- (* +264 NOT TAKEN: g_own_ran_out = 0; on to the call *)
  (* +264 .. +268: the bnez falls through, jal fuzz_alloc_ran_out *)
  paj_run_tok_x_inv RUN HS HJ SHOK HPM WA4_Bspan.
  all: try solve [wa4_nowr].
  lazymatch goal with HS : st_ok _ _ _ (restrict _ ?m) |- _ => rename m into msc end.
  lazymatch type of HF with frame_of _ ?rs _ _ =>
    pose proof (frame_of_read_only _ rs _ _ ltac:(vm_compute; reflexivity) HF) as EM2 end.
  clear HF HFr HG.
  assert (EMc : ms_mem msc = mem3) by (rewrite EM2; exact EM1).
  assert (KRc : forall r, In r WA4_KEPT -> getr (ms_regs msc) r = getr regs3 r).
  { intros r Hr.
    exact (regs_kept_of_st_ok segs _ _ (restrict (w_H W3) msc) regs3 [Z_to_bv 64 0] WA4_KEPT HS AG
      ltac:(vm_compute; reflexivity) r Hr). }
  assert (Hspc : spZ (ms_regs msc) = cw_sp0 D - CAW_FRAME)
    by (unfold spZ; rewrite (KRc 2%bv ltac:(wa4_in)); exact HSP).
  assert (HRA : getr (ms_regs msc) 1 = Z_to_bv 64 (BASE + (CAW_OFF + CAW_PC_RET))).
  { rewrite (st_ok_restrict_reg segs (w_H W3) E _ msc 1%bv HS). exact (codeptr_val E (CAW_OFF + CAW_PC_RET) HEI). }
  (* ---- the call: fuzz_alloc_ran_out's text through aj_call_x_sp (o = -80, empty chain: s0 = rc) ---- *)
  eapply SRr_bind.
  { eapply (aj_call_x_sp (fx := fy) (SK := SK) segs B prh_pst (ARcfx B) LAWS (@pa_segs_low _ _ PA)
      W3 E _ msc STK_check_as_written (cw_sp0 D) [] (cw_ly D) (cw_S D) (cw_Hp D) (cw_W D) (cw_mem D) (cw_md D) []
      ly3 S3 Hp3 _ k STK_fuzz_alloc_ran_out [] (-80) (Z_to_bv 64 (BASE + (CAW_OFF + CAW_PC_RET))) [] _ HS).
    - reflexivity.
    - exact HJ.
    - rewrite Hspc. unfold CAW_FRAME. lia.
    - reflexivity.
    - lia.
    - exact HSTKf0.
    - lia.
    - rewrite (KRc 3%bv ltac:(wa4_in)), (HKR 3%bv ltac:(wa4_in)). exact Hgp.
    - rewrite (KRc 4%bv ltac:(wa4_in)), (HKR 4%bv ltac:(wa4_in)). exact Htp.
    - exact HRA.
    - apply (ret_ok_codeptr_v (PI := PA)); [rewrite Coff; unfold CAW_PC_RET; lia | vm_compute; reflexivity].
    - rewrite unsigned_lit_small by exact Hraw. rewrite Cbase, Coff. unfold A_prog_base, CAW_PC_RET. lia.
    - (* the empty chain: s0 holds rc (an int, sign-extended), below the ceiling or above the stack top *)
      left. split; [|reflexivity].
      unfold s0Z. rewrite (KRc 8%bv ltac:(wa4_in)), R8. unfold w64. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
      change (2 ^ Z.of_N 64) with (2 ^ 64).
      destruct (Z_le_gt_dec 0 (cw_rc D)) as [Hp0 | Hn0].
      + rewrite Z.mod_small by lia. left. lia.
      + replace (cw_rc D mod 2 ^ 64) with (cw_rc D + 2 ^ 64)
          by (rewrite <- (Z.mod_small (cw_rc D + 2 ^ 64) (2 ^ 64)) by lia;
              rewrite Z.add_mod, Z.mod_same, Z.add_0_r, Z.mod_mod by lia; reflexivity).
        right; left. rewrite Etop. lia.
    - (* the callee: the text at the call's state, the cut's fy, the cut's ledger (most, own 0) *)
      intros HPXc.
      refine (HRANOUT fy ly3 S3 Hp3 W3 (ms_regs msc) (ms_mem msc) _ [] (cw_Lam D) (cw_peak D) (cw_cnt D) (cw_fail D)
        (cw_ran D) (cw_most D) 0 _ _).
      + refine (conj HPXc (conj _ (conj _ (conj _ _)))).
        * rewrite EMc. exact HROD.
        * rewrite Hspc, Eshi. unfold CAW_FRAME. rewrite Esp0. lia.
        * unfold raZ. rewrite HRA, unsigned_lit_small by exact Hraw.
          apply (PRW_StepKit.pa_slot_lt_ceil_b (PL := CW_PAListing) (PI := PA));
            [rewrite Coff; unfold CAW_PC_RET; lia | vm_compute; reflexivity].
        * (* FRM0-ENTRY: the call runs at the cut's float state fy, whose rounding mode caw_fl gives as 0 *)
          exact (proj1 HFL).
      + rewrite EMc. unfold caw_ledger in HLG. exact HLG.
    - intros a Ha. exfalso. exact (inFP_nil a Ha). }
  (* ---- after the call, at the return site +272 ---- *)
  cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & HJ1 & HPR & HQ2).
  unfold fQmn in HQ2. destruct HQ2 as ((HRL2 & R10' & EHp2 & ES2 & EAB2 & HLG2) & HMN2).
  subst S2.
  assert (HPM2 : P mem2) by exact (PCALL _ mem2 HMN2 HPM).
  clear HS SHOK HEI HJ HPM Hc.
  set (E3 := Eimg (Ereg regs2 [])).
  assert (HEI : img_env VAL A_LIM E3) by (unfold E3; apply Eimg_env).
  assert (AG3 : env_agree 32 (Ereg regs2 []) E3).
  { unfold E3. split; [intros i Hi; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. }
  assert (E10 : ew E3 10 = Z_to_bv 64 0).
  { unfold E3. rewrite Eimg_low by (unfold A_TEXT; lia).
    rewrite (ew_Ereg_nat regs2 [] 10 10%bv eq_refl), R10', HRAN0. reflexivity. }
  assert (HS3 : st_ok_pi (fx := fy) segs VAL E3 wa4_ss1
    (restrict (w_H W2) (@YK11.mkst fy regs2 (Z_to_bv 64 (BASE + (CAW_OFF + CAW_PC_RET))) mem2 (YK11.seg_rom segs)))).
  { rewrite restrict_mkst_fx. unfold wa4_ss1. apply pa_entry_st_ok_full;
      [unfold E3; apply regs_ok_Eimg_Ereg | reflexivity | apply Forall_nil | exact I | split; [exact I | split; exact I]]. }
  assert (SHOK3 : sh_ok segs WA4_Bx [] E3 (mrestrict (w_H W2) mem2)) by (unfold sh_ok; apply Forall_nil).
  psrr_branch_tok RUN BR HS3 SHOK3 WA4_Bspan.
  + (* +272 TAKEN: REFUTED, a0 = ran = cw_ran D = 0 (the r = 1 exit through fuzz_alloc_ran_out) *)
    exfalso.
    cbn [sv_denot] in Hc.
    lazymatch type of Hc with context [ew ?Ex 10%nat] =>
      replace (ew Ex 10%nat) with (Z_to_bv 64 0) in Hc by (symmetry; exact E10) end.
    vm_compute in Hc. discriminate Hc.
  + (* +272 not taken: on to CAW_PC_CHK *)
    lazymatch goal with H : st_ok_pi _ _ _ _ _ |- _ => rename H into HS4 end.
    paj_run_to_tok_x_inv RUNTO HS4 HJ2 SHOK3 HPM2 WA4_Bspan (CAW_OFF + CAW_PC_CHK).
    all: try solve [wa4_nowr].
    lazymatch goal with HS4 : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into ms4 end.
    lazymatch type of HF with frame_of _ ?rs _ _ =>
      pose proof (frame_of_read_only _ rs _ _ ltac:(vm_compute; reflexivity) HF) as EM4 end.
    clear HF HFr HG.
    assert (KR4 : forall r, In r WA4_KEPT -> getr (ms_regs ms4) r = getr regs2 r)
      by exact (regs_kept_of_st_ok_pi (fx := fy) _ _ _ regs2 [] WA4_KEPT HS4 AG3 ltac:(vm_compute; reflexivity)).
    assert (KRall : forall r, In r WA4_KEPT -> getr (ms_regs ms4) r = getr regs3 r).
    { intros r Hr. rewrite (KR4 r Hr), (wa4_pres _ _ HPR r Hr). exact (KRc r Hr). }
    (* the saved slots [sp0 - 32, sp0) lie above the callee's window: its journal keeps them *)
    assert (HKST : forall a, cw_sp0 D - 32 <= a < cw_sp0 D -> aview segs (w_H W2) mem2 a = aview segs (w_H W3) mem3 a).
    { intros a Ha. pose proof (ajx_hi HJ1) as G1. rewrite <- EMc. apply G1.
      - rewrite Esp0 in Ha. lia.
      - lia. }
    apply (wa4_leaf fy W2 _ _ ms4 _ CAW_PC_CHK _ HS4 eq_refl ltac:(vm_compute; reflexivity)).
    apply (KCHK fy ly2 S3 Hp2 W2 (ms_regs ms4) (ms_mem ms4) _ (k + k1) want 0); [|exact HPM2].
    rewrite EM4.
    split; [|split; [exact HRP|split; [|split; [|split; [exact HWANT | split; [reflexivity | split; [rewrite EAB2; exact EAB |]]]]]]].
    * unfold caw_carry.
      split; [exact HPRE|]. split; [exact HCNT|]. split; [exact HFL|]. split; [unfold caw_J; rewrite <- EM4; exact HJ2|].
      split; [intros r Hr; rewrite (KRall r (wa4_kept_sub r Hr)); exact (HKR r Hr)|].
      split; [unfold spZ; rewrite (KRall 2%bv ltac:(wa4_in)); exact HSP|].
      split; [unfold caw_saved in HSV |- *; destruct HSV as (V1 & V2 & V3 & V4);
              repeat split; (eapply val_mem_kept; [intros i Hi; apply HKST; cbn in Hi; lia | eassumption])|].
      split; [rewrite EHp2; exact EHp|]. split; [exact (HRL2 HRL)|].
      rewrite <- EM4. exact (wa4_rod_keep _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2 HROD0).
    * rewrite (KRall 8%bv ltac:(wa4_in)). exact R8.
    * rewrite (KRall 18%bv ltac:(wa4_in)). exact R18.
    * (* caw_ledger at CAW_PC_CHK, ownv = 0: the text's post gives the ledger at the cut's values (most, own 0) at W2 /
         mem2 *)
      unfold caw_ledger. exact HLG2.
Qed.

(* caw_wa4_holds past the free, at RW: the same walk with the R runners and the R branch; the call by aj_call_x_spR at
   RW, the callee's wle text lifted into RW (SRr_SRrG, apost_base_x_R_lift); the cut and the continuations at RW *)
Lemma caw_wa4_holdsR : caw_seg_WA4R (fx := fx) B SK CTX0 P (YA0nH.wle' segs YGcfRehidePost.RZ_cf).
Proof.
intros Q D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k want HAT KEND KCHK HPM.
destruct HAT as ((HPRE & HCNT & HFL & HJ & HKR & HSP & HSV & EHp & HRL & HROD) & HRP & R8 & R18 & HWANT & EAB & HLG).
pose proof (caw_pre_fpre (fx := fx) B CTX0 D HPRE) as HFP.
pose proof (caw_pre_rc (fx := fx) B CTX0 D HPRE) as Hrc.
pose proof (caw_pre_doc (fx := fx) B CTX0 D HPRE) as Hdoc.
pose proof (caw_pre_size (fx := fx) B CTX0 D HPRE) as Hsz.
pose proof (caw_pre_data0 (fx := fx) B CTX0 D HPRE) as Hd0.
pose proof (caw_pre_data62 (fx := fx) B CTX0 D HPRE) as Hd62.
pose proof (caw_pre_ran (fx := fx) B CTX0 D HPRE) as HRAN0.
pose proof (caw_pre_live (fx := fx) B CTX0 D HPRE) as HLIVE.
pose proof (caw_pre_max (fx := fx) B CTX0 D HPRE) as HMAX.
pose proof (caw_pre_frames (fx := fx) B CTX0 D HPRE) as HFR.
pose proof HFP as (HPX & HROD0 & HSTKHI & HRAC & HFZ0).
pose proof HPX as (HAR0 & Hra0 & Hra40 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
unfold caw_JR in HJ.
pose proof (ajxR_ar HJ) as HAR3. pose proof (ajxR_ly HJ) as Hly.
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (HOWN3 : prh_own W3 mem3 0) by (unfold caw_ledger in HLG; eapply PRH_Base.prh_ledger_own; exact HLG).
pose proof HOWN3 as (Vown & _).
pose proof (cwi_base CWI) as Cbase.
pose proof (cwi_own CWI) as Cown.
pose proof (@pa_val_range _ _ PA (A_OBJ 13)) as Ro13.
pose proof YM05.alloc_ceiling_value as Hceilv.
pose proof CAW_OFF_val as Coff.
assert (HSTKf0 : 0 <= STK_fuzz_alloc_ran_out) by (unfold Z.le; vm_compute; discriminate).
assert (HSTKc : STK_fuzz_alloc_ran_out + 80 <= STK_check_as_written) by (unfold Z.le; vm_compute; discriminate).
assert (Esp0 : cw_sp0 D = spZ (cw_regs D)) by reflexivity.
assert (Hraw : 0 <= BASE + (CAW_OFF + CAW_PC_RET) < 2 ^ 64)
  by (rewrite Cbase, Coff; unfold A_prog_base, CAW_PC_RET; lia).
set (E := Eimg (Ereg regs3 [Z_to_bv 64 0])).
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (E32 : ew E 32 = Z_to_bv 64 0).
{ unfold E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs3 [Z_to_bv 64 0] 0). }
assert (Uo13 : bv_unsigned (ew E (A_OBJ 13)) = VAL (A_OBJ 13)).
{ unfold E. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia). apply unsigned_lit_small. lia. }
assert (AG : env_agree 32 (Ereg regs3 [Z_to_bv 64 0]) E).
{ unfold E. split; [intros i Hi; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. }
assert (HS : st_ok_pi (fx := fy) segs VAL E wa4_ss0
  (restrict (w_H W3) (@YK11.mkst fy regs3 (Z_to_bv 64 (BASE + (CAW_OFF + CAW_PC_OOM))) mem3 (YK11.seg_rom segs)))).
{ rewrite restrict_mkst_fx. unfold wa4_ss0. apply pa_entry_st_ok_full.
  - unfold E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold region_ok, wa4_rg.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Uo13.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
    apply (chunk_ok_val segs E _ (VAL (A_OBJ 13)) 0 1 (SOff 32 0) 0).
    + cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    + cbn; lia.
    + cbn; lia.
    + rewrite Z.add_0_r, Cown. replace (N.to_nat 1) with pi_gz_own_ran_out by (vm_compute; reflexivity). exact Vown.
  - cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
  - split; [exact I | split; exact I]. }
assert (SHOK : sh_ok segs WA4_Bx [] E (mrestrict (w_H W3) mem3)) by (unfold sh_ok; apply Forall_nil).
pose (RUN := paj_run_x_invR (fx := fy) (SK := SK) (L := A_prog_listing) (PL := CW_PAListing) (PI := PA)
  B prh_pst (ARcfx B) LAWS P PLAW RW (YA0nH.wle'_refl segs YGcfRehidePost.RZ_cf)
  (YA0nH.wle'_trans segs YGcfRehidePost.RZ_cf)).
pose (RUNTO := paj_run_to_x_invR (fx := fy) (SK := SK) (L := A_prog_listing) (PL := CW_PAListing) (PI := PA)
  B prh_pst (ARcfx B) LAWS P PLAW RW (YA0nH.wle'_refl segs YGcfRehidePost.RZ_cf)
  (YA0nH.wle'_trans segs YGcfRehidePost.RZ_cf)).
pose (BR := wa4_branchR fy RW).
unfold caw_cfg, caw_pc. rewrite <- Z.add_assoc.
(* +252 .. +264 *)
paj_run_tok_x_inv RUN HS HJ SHOK HPM WA4_Bspan.
all: try solve [wa4_nowr].
lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into ms1 end.
lazymatch type of HF with frame_of _ ?rs _ _ =>
  pose proof (frame_of_read_only _ rs _ _ ltac:(vm_compute; reflexivity) HF) as EM1 end.
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK WA4_Bspan.
- (* +264 taken: refuted (E32) *)
  exfalso.
  cbn [sv_denot] in Hc.
  lazymatch type of Hc with context [ew ?Ex 32%nat] =>
    replace (ew Ex 32%nat) with (Z_to_bv 64 0) in Hc by (symmetry; exact E32) end.
  vm_compute in Hc. discriminate Hc.
- (* +264 not taken: +264 .. +268 *)
  paj_run_tok_x_inv RUN HS HJ SHOK HPM WA4_Bspan.
  all: try solve [wa4_nowr].
  lazymatch goal with HS : st_ok _ _ _ (restrict _ ?m) |- _ => rename m into msc end.
  lazymatch type of HF with frame_of _ ?rs _ _ =>
    pose proof (frame_of_read_only _ rs _ _ ltac:(vm_compute; reflexivity) HF) as EM2 end.
  clear HF HFr HG.
  assert (EMc : ms_mem msc = mem3) by (rewrite EM2; exact EM1).
  assert (KRc : forall r, In r WA4_KEPT -> getr (ms_regs msc) r = getr regs3 r).
  { intros r Hr.
    exact (regs_kept_of_st_ok segs _ _ (restrict (w_H W3) msc) regs3 [Z_to_bv 64 0] WA4_KEPT HS AG
      ltac:(vm_compute; reflexivity) r Hr). }
  assert (Hspc : spZ (ms_regs msc) = cw_sp0 D - CAW_FRAME)
    by (unfold spZ; rewrite (KRc 2%bv ltac:(wa4_in)); exact HSP).
  assert (HRA : getr (ms_regs msc) 1 = Z_to_bv 64 (BASE + (CAW_OFF + CAW_PC_RET))).
  { rewrite (st_ok_restrict_reg segs (w_H W3) E _ msc 1%bv HS). exact (codeptr_val E (CAW_OFF + CAW_PC_RET) HEI). }
  (* the call at RW *)
  eapply (YA0nH.SRrG_bind segs RW (YA0nH.wle'_trans segs YGcfRehidePost.RZ_cf)).
  { eapply (aj_call_x_spR (fx := fy) (SK := SK) segs B prh_pst (ARcfx B) LAWS (@pa_segs_low _ _ PA)
      RW (YA0nH.wle'_refl segs YGcfRehidePost.RZ_cf) (YA0nH.wle'_trans segs YGcfRehidePost.RZ_cf)
      W3 E _ msc STK_check_as_written (cw_sp0 D) [] (cw_ly D) (cw_S D) (cw_Hp D) (cw_W D) (cw_mem D) (cw_md D) []
      ly3 S3 Hp3 _ k STK_fuzz_alloc_ran_out [] (-80) (Z_to_bv 64 (BASE + (CAW_OFF + CAW_PC_RET))) [] _ HS).
    - reflexivity.
    - exact HJ.
    - rewrite Hspc. unfold CAW_FRAME. lia.
    - reflexivity.
    - lia.
    - exact HSTKf0.
    - lia.
    - rewrite (KRc 3%bv ltac:(wa4_in)), (HKR 3%bv ltac:(wa4_in)). exact Hgp.
    - rewrite (KRc 4%bv ltac:(wa4_in)), (HKR 4%bv ltac:(wa4_in)). exact Htp.
    - exact HRA.
    - apply (ret_ok_codeptr_v (PI := PA)); [rewrite Coff; unfold CAW_PC_RET; lia | vm_compute; reflexivity].
    - rewrite unsigned_lit_small by exact Hraw. rewrite Cbase, Coff. unfold A_prog_base, CAW_PC_RET. lia.
    - left. split; [|reflexivity].
      unfold s0Z. rewrite (KRc 8%bv ltac:(wa4_in)), R8. unfold w64. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
      change (2 ^ Z.of_N 64) with (2 ^ 64).
      destruct (Z_le_gt_dec 0 (cw_rc D)) as [Hp0 | Hn0].
      + rewrite Z.mod_small by lia. left. lia.
      + replace (cw_rc D mod 2 ^ 64) with (cw_rc D + 2 ^ 64)
          by (rewrite <- (Z.mod_small (cw_rc D + 2 ^ 64) (2 ^ 64)) by lia;
              rewrite Z.add_mod, Z.mod_same, Z.add_0_r, Z.mod_mod by lia; reflexivity).
        right; left. rewrite Etop. lia.
    - (* the callee: the kit's wle text, lifted into RW *)
      intros HPXc.
      eapply (YA0nH.SRrG_mono segs RW).
      { apply (YA0nH.SRr_SRrG segs RW (YA0nH.wle_wle' segs YGcfRehidePost.RZ_cf)).
        refine (HRANOUT fy ly3 S3 Hp3 W3 (ms_regs msc) (ms_mem msc) _ [] (cw_Lam D) (cw_peak D) (cw_cnt D) (cw_fail D)
          (cw_ran D) (cw_most D) 0 _ _).
        + refine (conj HPXc (conj _ (conj _ (conj _ _)))).
          * rewrite EMc. exact HROD.
          * rewrite Hspc, Eshi. unfold CAW_FRAME. rewrite Esp0. lia.
          * unfold raZ. rewrite HRA, unsigned_lit_small by exact Hraw.
            apply (PRW_StepKit.pa_slot_lt_ceil_b (PL := CW_PAListing) (PI := PA));
              [rewrite Coff; unfold CAW_PC_RET; lia | vm_compute; reflexivity].
          * exact (proj1 HFL).
        + rewrite EMc. unfold caw_ledger in HLG. exact HLG. }
      intros W' c' _ Hc'.
      exact (apost_base_x_R_lift (fx := fy) (SK := SK) segs B prh_pst (ARcfx B) RW
        (YA0nH.wle_wle' segs YGcfRehidePost.RZ_cf) _ _ _ _ _ _ _ _ _ _ _ _ Hc').
    - intros a Ha. exfalso. exact (inFP_nil a Ha). }
  (* after the call, at the return site +272 *)
  cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & HJ1 & HPR & HQ2).
  unfold fQmn in HQ2. destruct HQ2 as ((HRL2 & R10' & EHp2 & ES2 & EAB2 & HLG2) & HMN2).
  subst S2.
  assert (HPM2 : P mem2) by exact (PCALL _ mem2 HMN2 HPM).
  clear HS SHOK HEI HJ HPM Hc.
  set (E3 := Eimg (Ereg regs2 [])).
  assert (HEI : img_env VAL A_LIM E3) by (unfold E3; apply Eimg_env).
  assert (AG3 : env_agree 32 (Ereg regs2 []) E3).
  { unfold E3. split; [intros i Hi; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. }
  assert (E10 : ew E3 10 = Z_to_bv 64 0).
  { unfold E3. rewrite Eimg_low by (unfold A_TEXT; lia).
    rewrite (ew_Ereg_nat regs2 [] 10 10%bv eq_refl), R10', HRAN0. reflexivity. }
  assert (HS3 : st_ok_pi (fx := fy) segs VAL E3 wa4_ss1
    (restrict (w_H W2) (@YK11.mkst fy regs2 (Z_to_bv 64 (BASE + (CAW_OFF + CAW_PC_RET))) mem2 (YK11.seg_rom segs)))).
  { rewrite restrict_mkst_fx. unfold wa4_ss1. apply pa_entry_st_ok_full;
      [unfold E3; apply regs_ok_Eimg_Ereg | reflexivity | apply Forall_nil | exact I | split; [exact I | split; exact I]]. }
  assert (SHOK3 : sh_ok segs WA4_Bx [] E3 (mrestrict (w_H W2) mem2)) by (unfold sh_ok; apply Forall_nil).
  psrr_branch_tok RUN BR HS3 SHOK3 WA4_Bspan.
  + (* +272 taken: refuted (E10) *)
    exfalso.
    cbn [sv_denot] in Hc.
    lazymatch type of Hc with context [ew ?Ex 10%nat] =>
      replace (ew Ex 10%nat) with (Z_to_bv 64 0) in Hc by (symmetry; exact E10) end.
    vm_compute in Hc. discriminate Hc.
  + (* +272 not taken: on to CAW_PC_CHK *)
    lazymatch goal with H : st_ok_pi _ _ _ _ _ |- _ => rename H into HS4 end.
    paj_run_to_tok_x_inv RUNTO HS4 HJ2 SHOK3 HPM2 WA4_Bspan (CAW_OFF + CAW_PC_CHK).
    all: try solve [wa4_nowr].
    lazymatch goal with HS4 : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into ms4 end.
    lazymatch type of HF with frame_of _ ?rs _ _ =>
      pose proof (frame_of_read_only _ rs _ _ ltac:(vm_compute; reflexivity) HF) as EM4 end.
    clear HF HFr HG.
    assert (KR4 : forall r, In r WA4_KEPT -> getr (ms_regs ms4) r = getr regs2 r)
      by exact (regs_kept_of_st_ok_pi (fx := fy) _ _ _ regs2 [] WA4_KEPT HS4 AG3 ltac:(vm_compute; reflexivity)).
    assert (KRall : forall r, In r WA4_KEPT -> getr (ms_regs ms4) r = getr regs3 r).
    { intros r Hr. rewrite (KR4 r Hr), (wa4_pres _ _ HPR r Hr). exact (KRc r Hr). }
    assert (HKST : forall a, cw_sp0 D - 32 <= a < cw_sp0 D -> aview segs (w_H W2) mem2 a = aview segs (w_H W3) mem3 a).
    { intros a Ha. pose proof (ajxR_hi HJ1) as G1. rewrite <- EMc. apply G1.
      - rewrite Esp0 in Ha. lia.
      - lia. }
    apply (wa4_leafR fy RW W2 _ _ ms4 _ CAW_PC_CHK _ HS4 eq_refl ltac:(vm_compute; reflexivity)).
    apply (KCHK fy ly2 S3 Hp2 W2 (ms_regs ms4) (ms_mem ms4) _ (k + k1) want 0); [|exact HPM2].
    rewrite EM4.
    split; [|split; [exact HRP|split; [|split; [|split; [exact HWANT | split; [reflexivity | split; [rewrite EAB2; exact EAB |]]]]]]].
    * unfold caw_carryR.
      split; [exact HPRE|]. split; [exact HCNT|]. split; [exact HFL|]. split; [unfold caw_JR; rewrite <- EM4; exact HJ2|].
      split; [intros r Hr; rewrite (KRall r (wa4_kept_sub r Hr)); exact (HKR r Hr)|].
      split; [unfold spZ; rewrite (KRall 2%bv ltac:(wa4_in)); exact HSP|].
      split; [unfold caw_saved in HSV |- *; destruct HSV as (V1 & V2 & V3 & V4);
              repeat split; (eapply val_mem_kept; [intros i Hi; apply HKST; cbn in Hi; lia | eassumption])|].
      split; [rewrite EHp2; exact EHp|]. split; [exact (HRL2 HRL)|].
      rewrite <- EM4. exact (wa4_rod_keepR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2 HROD0).
    * rewrite (KRall 8%bv ltac:(wa4_in)). exact R8.
    * rewrite (KRall 18%bv ltac:(wa4_in)). exact R18.
    * unfold caw_ledger. exact HLG2.
Qed.
End wa4.

Print Assumptions caw_wa4_holds.
Print Assumptions caw_wa4_holdsR.
