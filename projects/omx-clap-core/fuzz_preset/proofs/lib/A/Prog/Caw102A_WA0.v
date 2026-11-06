(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/ExvB_Open_sh.v, with its module paths and module names changed; 1178 of its 1215 lines of code are new or changed and 43 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/Caw102A_WA2.v, with its module paths and module names changed; 450 of its 533 lines of code are new or changed and 1132 lines of the source are left out. *)
(* fuzz_preset lib/A, the #102 re-walk of check_as_written on image A' (ASan build): segment WA0 (lane CawA102R,
   h-rw-pre-5; first proved by CawA102WA0, re-proved on the caw_pst base by CawRWA0, on the ledger base by CawDWA0, on
   the f97c re-keyed base by CawGWA0, on the batch kit's base by CawA102R.KWA0). INT102-READY on the kit's cut 7cdbb61b5fa0.
   It proves Caw102A_Base.v's caw_seg_WA0 (caw_wa0_holds) for an abstract memory invariant P with srr_inv_laws and
   srr_inv_call (the segment crosses __wrap_malloc).
   rule 24: no function proved. rule 24: proves no function (kind: segment lemma).
   THE BASE (statements, not edited here; their blobs as at a working branch 2f79e2e7d77e):
   lib/A/Prog/Caw102A_Base.v (caw_seg_WA0, caw_pre and its projections caw_pre_*, caw_cnt, caw_prog,
   caw_dead, caw_evs, caw_ev1, caw_run_at_nth, caw_at_X / caw_at_null, caw_k_X / caw_k_null, caw_ledger, caw_img with
   cwi_base / cwi_entry / cwi_pst_rw / cwi_pst_img / cwi_hi / cwi_pst_ok / cwi_pst_errno) and lib/A/Prog/Caw102A_Kit.v
   3d241a90402d (caw_st_ok_e, caw_Ee, caw_reg_st, caw_sp_st), on the kit's
   cut. Every base name with an implicit float state in a statement of
   this file gets the entry's, `(fx := fx)`.
   WHAT CHANGED (the batch-prep base, the batch tip), and why: the batch text tcheck_as_written_specX (PRH_FnCheck.v
   c40cf3fdcd2a :832-902)
   (1) has no run-word list DW (prh_univ_closure CTX0, PRH_Base.v 6d0ab94b8f66 :1203, prh_univ_closure_lit :1225): the
       Section variable DW is removed, and caw_pre / caw_seg_WA0 / prh_univ_closure / prh_univ_closure_lit lose their DW
       argument here (wa0_entry, wa0_trace, caw_wa0_holds);
   (2) takes the room counts as entry premises (:862-863); with the hull budget and HPOS after them caw_pre now has 27
       conjuncts (Caw102A_Base.v:229-256), and (3) caw_pre is read BY NAME: its positional destructs (in wa0_entry and
       caw_wa0_holds; they now mis-bind, ck_frm0 moved by four, 23rd to 27th) are the base's projections caw_pre_fpre ..
       caw_pre_frm0. caw_seg_WA0 still takes caw_cnt D (the top gives it by caw_pre_cnt), and wa0_counts reads it as before;
   (4) states THE OUTCOME (:879-888), which the base carries as caw_dead D, a new third conjunct of caw_at_null. It is
       proved at the NULL arm from the malloc rule's granted path `apath (malloc_cf (size + 1) tr (cw_S D)) trc (PNull,
       S2)` with `gflag trc = true`, by PRH_Refute.prh_refute_at at U := as_universe B, k := length (caw_evs D) = 2, e :=
       HMal (size + 1) (read off the run by caw_run_at_nth), s := cw_S D (the malloc's own input state, where the entry
       position holds), Wf_cf from the entry's ARx by ARx_wf_law_xs (the Wf law the malloc rule is given).
   No statement of this file changed except the loss of DW.
   THE INPUTS, each by path: the listing of record #102 v3, lib/A/Listing_prog.v 7ed1529926bd (the re-emit
   d42e123915ae's listing 1ab147923c5d; the walk is PARAMETRIC over {PA : PAImg A_prog_listing} with the base's tables
   PL_caw_A); the kit's cut: PRH_Base.v (fpre with frm_zero, prh_univ_closure CTX0,
   prh_ledger with most and own, prh_run_at, prh_cons_from), PRH_FnCheck.v c40cf3fdcd2a, PRH_Refute.v 23f7a37f01c9
   (prh_refute_at, prh_granted_null), PRH_Img.v 934516a622e8, PRH_Reader.v 4266e709561a, PRH_FnEx.v,
   lib/A/PresetCfnA.v 1a941f38d5fe, lib/Spec PresetRoomPos.v 943d62290e8e, PresetRoomPosKeep.v,
   PresetSite17.v 74734062f6b7 (is_alloc), S1Ledger.v 8cf15eeb6311 (prh_ledger_kept_aview, prh_ledger_hblock, both at
   most own), YImgTop.v d2a97d3111ce; the engine's P'' set as the kit's cut carries it (YCbqG.v, the journal
   read through ajx_*; YGcallMxmn.v 3c08bbab8292, aj_malloc_x_ct_m with the `admits` call premise; YGcallcf.v
   8645fa6a514f, ARx_wf_law_xs); YGcfRoomLive.v (sec_cnt, ccnt24, rl_sec_ok, rl_b24_ok, RL_malloc_step);
   PRW_StepKit.v 0df3991c13f4; lib/Spec/PresetLiveBounds.v f78da450d5f6 (LSEC, L24, DRV). THE REQUIRE CLOSURE now
   holds lib/A/PresetCfnA.v and ZImage (PRH_Refute Requires PresetCfnA, P8 at the instance): this file builds on the
   pins102 route only.
   THE CODE (A' 0x81fb8; DERIVED byte offsets from the entry, the listing's slot A_prog_slot AS_check_as_written):
     +0 .. +60  addi sp, sp, -80; the four saves (ra -8, s0 -16, s1 -24, s2 -32 from the entry sp); s1 = doc; s0 = rc;
                a2 = the GOT word A_OBJ 0; a3 = data + size; s2 = the shadow base read through it (A_OBJ 12); the
                struct at sp + 8: p = data, end = data + size, depth = 0; a0 = size + 1; jal __wrap_malloc
                ONE engine run (YC1fPx.paj_run_x_inv at P), from the entry state wa0_entry (frame region 80, the GOT
                word and shadow-cell regions as S4_PsEntry's got_regionP / bcell_regionP) to the wrapper's entry.
     the call   YGcallMxmnKeep.aj_malloc_x_ct_m_keep at the cf instance (amalloc_realizes_x_xs_keep of AMALLOC; QM_cf from
                room_live_room and caw_pre_hull; the empty chain, s0 = rc an int, wa0_chain; the trace by prh_univ_closure's literal
                clause at the return site +64, wa0_site / wa0_trace); P across it by PCALL from the rule's memnorm keep.
     +64        beqz a0: BOTH arms walked (no refuted site in this segment).
                taken (a0 = 0, the refused malloc) -> CAW_PC_NULL (+112): caw_k_null; caw_prog D [] by
                PresetRoomPosKeep.room_pos_keep_alloc_null; caw_dead D by PRH_Refute.prh_refute_at from the rule's
                granted NULL path at cw_S D; errno = 12 and the out-of-memory byte from the rule's res = 0 arm.
                not taken (a0 = scr, 4096 <= scr) -> CAW_PC_X (+68): caw_k_X; caw_prog D (caw_ev1 D) by
                room_pos_keep_alloc with the run's event HMal (size + 1) (caw_run_at_nth).
   WHAT CROSSES THE CALL: room_live_cf by YGcfRoomLive.RL_malloc_step, its live-set premises rl_sec_ok / rl_b24_ok from
   caw_cnt D (wa0_counts); the frame words (above the call's window, acall_kept's first clause); the statics
   (cwi_pst_img, pal_pst_ok, acall_kept's image clause, KST) and the ledger's heads (the journal's block clause) for the
   ledger at most 0 (g_own_ran_out and g_most are its rows); arodata_okP by the journal's image clause and cwi_pst_rw;
   the kept registers by aregs_preserved; the float state is the entry's (fx).
   THE ALLOCATOR PARAMETERS: cp := CfParams_preset (CawA102's ruling, 13:5xZ: rl_sec_ok's bound is CfParams-specific,
   so room_live_cf after the scratch malloc is not provable at a generic cp; the top composes at CfParams_preset).
  SECTION HYPOTHESES (owners): PAL : PALib (the unit's image binding of B, as lib/A/Prog/FuzzFree.v takes it; owner
  a Theorem Labs lane); pal_pst_ok is NOT a hypothesis (a Theorem Labs lane, as WA2): a Let from caw_img's cwi_pst_ok / cwi_pst_errno;
  AMALLOC : YGcfMallocComposeKeep.amalloc_realizes_cf_keep (the malloc wrapper's runtime row at the cf instance with the memnorm keep, owner a Theorem Labs lane);
  CWI : caw_img (the image facts of PA; owner the instantiation, by computation [a Theorem Labs lane, where B is bound]); PLAW / PCALL
  (the invariant's laws, the segment form; owner the top, at caw_mn). No new Section hypothesis: the room counts are
  caw_cnt D, a premise of caw_seg_WA0 (the top gives it from caw_pre by caw_pre_cnt).
   Numerals: 80 / 72 / 64 / 56 / 32 / 24 / 16 / 8 (LENGTH: the frame and its slots); 64 / 68 / 112 (DERIVED: offsets
   inside the function, CAW_PC_X / CAW_PC_NULL of the base); 2584 / 240 (DERIVED: the engine's code pointer atom
   A_TEXT and offset CAW_OFF + 64); atoms 2 / 32 (DERIVED: the engine's numbering); register numbers (WORD); 4096,
   2 ^ 31, 2 ^ 44, 2 ^ 46, 2 ^ 47, 2 ^ 64 (LENGTH / word and band bounds). No ADDRESS literal. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YG00cf YG01cf YG0ncf YG0dcf YG0lawscf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x YC1fPx YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcallx YGcallcf YGcallMxmn.
(* the keep-carrying malloc rule and its contract (part 3c took the memnorm keep out of the plain rule's post) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallMxmnKeep YGcfMallocComposeKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfAroBridge YGcfSecsStep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetHullBudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetHullPay.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPosKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetLiveBounds.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Img PRH_Reader PRH_FnEx PRH_FnCheck.
(* the granted NULL of the allocator at a consumer position is impossible (caw_dead at the NULL arm) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Refute.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_StepKit S1Ledger Caw102A_Base Caw102A_Kit.
#[global] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.


(* compute the symbolic value of one register in the goal *)
Ltac wa0_sv := lazymatch goal with |- context [sv_denot ?Ex (sr_get ?sr ?r)] =>
  let t' := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with t' end.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg}.
Context {PA : PAImg A_prog_listing}.
#[local] Existing Instance CfParams_preset.
#[local] Existing Instances CW_PrhImg CW_PAListing CW_RL.
#[local] Notation segs := (@pa_segs _ A_prog_listing PA).
#[local] Notation VAL := (@pa_val _ A_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable SK : YI16.sink_head.
Variable CTX0 : list (list Z).
Hypothesis CWI : caw_img (PA := PA) B.
Hypothesis PAL : PALib (rc := rc) (L := A_prog_listing) (PI := PA) B.
(* the statics are off the owned statics and errno: the base's cwi_pst_ok / cwi_pst_errno (no Section hypothesis) *)
Let pal_pst_ok : forall a, Exists (in_zr a) prh_pst ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4) :=
  fun a Ha => conj (proj2 (cwi_pst_ok CWI a Ha)) (cwi_pst_errno CWI a Ha).
(* the malloc wrapper's runtime row with the memnorm keep at the leaf (YGcfMallocComposeKeep.v): this walk carries P
   across the call with it (PCALL below) *)
Hypothesis AMALLOC : YGcfMallocComposeKeep.amalloc_realizes_cf_keep segs B.
Let LAWS_cf : AR_laws_cf segs B := AR_laws_ok_cf segs B.
Let LAWS : AR_laws_x segs B (ARcfx B) cf_head := AR_laws_x_xs segs B LAWS_cf.
Let OWNLOW := ARx_owned_low_law_xs segs B LAWS_cf.
Let WFL := ARx_wf_law_xs segs B.
Let XSL := ARx_xs_law_xs segs B.
Let AMALLOCx := YGcallMxmnKeep.amalloc_realizes_x_xs_keep segs B AMALLOC.
Variable P : (word -> option byte) -> Prop.
Hypothesis PLAW : srr_inv_laws segs P.
Hypothesis PCALL : srr_inv_call segs P.

Lemma wa0_stk : ASTACK + CAW_FRAME <= STK_check_as_written.
Proof. unfold Z.le. vm_compute. discriminate. Qed.

Lemma wa0_obj : forall i, (i < 39)%nat -> 0 <= VAL (A_OBJ i) /\ VAL (A_OBJ i) + 8 <= YImgTop.IMG_TOP.
Proof.
intros i Hi. pose proof (pa_obj_img i Hi) as [H1 H2]. pose proof (cwi_hi CWI) as H3.
pose proof (pa_val_range (A_OBJ i)). lia.
Qed.

Definition wa0_E (regs : bvmap 5 word) : env := @Eimg _ A_prog_listing PA (Ereg regs [Z_to_bv 64 SHADOW_OFF]).
Definition wa0_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition wa0_ss : sstate := mkSS CAW_OFF sr_atoms [stack_region CAW_FRAME; got_regionP; bcell_regionP 32] None wa0_facts.
Definition wa0_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).

Lemma wa0_entry : forall D : caw_in, caw_pre (fx := fx) B CTX0 D ->
  st_ok_pi segs VAL (wa0_E (cw_regs D)) wa0_ss
    (restrict (w_H (cw_W D)) (mkst (cw_regs D) (Z_to_bv 64 (BASE + CAW_OFF)) (cw_mem D) (seg_rom segs))).
Proof.
intros D HPRE.
pose proof (caw_pre_fpre (fx := fx) B CTX0 D HPRE) as (HPX & _).
pose proof HPX as (HAR & _ & _ & _ & _ & Hstk & Hpres & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof wa0_stk as HSTK. unfold ASTACK, CAW_FRAME in HSTK.
destruct (alx_const segs B (ARcfx B) LAWS _ _ _ _ _ _ HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B PAL), (pal_cell B PAL) in Kgot. rewrite (pal_cell B PAL) in Kcell.
pose proof (pal_got_cell B PAL) as Hgc.
pose proof (wa0_obj 0 ltac:(lia)) as Hg0. pose proof (wa0_obj 12 ltac:(lia)) as Hg12.
rewrite YImgTop.IMG_TOP_val in Hg0, Hg12.
set (E := wa0_E (cw_regs D)).
assert (E2 : ew E 2 = getr (cw_regs D) 2).
{ subst E. unfold wa0_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat _ _ 2 2%bv eq_refl). }
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF).
{ subst E. unfold wa0_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra _ _ 0). }
assert (Eo0 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; unfold wa0_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Eo12 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; unfold wa0_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ (cw_regs D)) by (rewrite E2; reflexivity).
assert (Ush : bv_unsigned (ew E 32) = SHADOW_OFF) by (rewrite E32; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (Ug0 : bv_unsigned (ew E (A_OBJ 0)) = VAL (A_OBJ 0))
  by (rewrite Eo0; apply unsigned_lit_small; pose proof (pa_val_range (A_OBJ 0)); lia).
assert (Ug12 : bv_unsigned (ew E (A_OBJ 12)) = VAL (A_OBJ 12))
  by (rewrite Eo12; apply unsigned_lit_small; pose proof (pa_val_range (A_OBJ 12)); lia).
rewrite restrict_mkst_fx. unfold wa0_ss. apply pa_entry_st_ok_full.
- subst E. unfold wa0_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold stack_region, got_regionP, bcell_regionP.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite Usp. unfold CAW_FRAME. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
  + rewrite Ug0. split; [lia|]. split; [pose proof (pa_val_range (A_OBJ 0)); lia|].
    split; [intros o Ho; lia|]. constructor; [|constructor].
    apply (chunk_ok_val segs E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
      [cbn [sv_denot]; rewrite Eo12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | pose proof (pa_val_range (A_OBJ 12)); zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword segs (w_H (cw_W D)) (cw_mem D) _ _ Kgot).
  + rewrite Ug12. split; [lia|]. split; [pose proof (pa_val_range (A_OBJ 12)); lia|].
    split; [intros o Ho; lia|]. constructor; [|constructor].
    apply (chunk_ok_val segs E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) SHADOW_OFF);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | unfold SHADOW_OFF; zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword segs (w_H (cw_W D)) (cw_mem D) _ _ Kcell).
- apply pairwise_disjoint_of_extents.
  unfold stack_region, got_regionP, bcell_regionP, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite Usp, Ug0, Ug12. unfold CAW_FRAME.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; first [exact I | lia].
- split; [|split; [exact I | exact I]].
  cbn [wa0_facts f_atoms atoms_ok].
  split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Usp; change (2 ^ 4) with 16;
          split; [lia|]; split; [exact Hal16 | lia]|].
  split; [|exact I].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Ush. rewrite Z.pow_0_r, Z.mod_1_r. lia.
Qed.

Ltac wa0_awr Usp :=
  lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0 ?bc ?ly' ?own' =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0 bc ly' own') end;
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat 0);
  [ reflexivity | rewrite Z.add_0_r; exact Usp | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia
  | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|];
    apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]; apply awr_ok_nil ].


(* ---- the malloc's live-set premises at the entry state, from caw_cnt D (caw_seg_WA0's premise: sec_cnt <= LSEC +
   DRV, ccnt24 <= L24 + DRV, tpadded_specX's spelling): RL_malloc_step's rl_sec_ok / rl_b24_ok at those bounds; the
   parameter conjuncts are closed facts at CfParams_preset (LSEC + DRV = 9,524: 9,524 + QSEC_MAX 4,177 + 3 < 16,000;
   8,192 * (L24 + DRV + N24Q + 1) + 4 * kUserMapSize <= kFreeArrayOffset, CfRoomLivePreset.v d0e5e47dcb02's figures) ---- *)
Lemma wa0_counts : forall S,
  YGcfRoomLive.sec_cnt S <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV ->
  YGcfRoomLive.ccnt24 S <= PresetLiveBounds.L24 + PresetLiveBounds.DRV ->
  YGcfRoomLive.rl_sec_ok (cp := CfParams_preset) (PresetLiveBounds.LSEC + PresetLiveBounds.DRV) S /\
  YGcfRoomLive.rl_b24_ok (PresetLiveBounds.L24 + PresetLiveBounds.DRV) S.
Proof.
intros S C1 C2. split; split;
  [exact C1 | apply Z.ltb_lt; vm_compute; reflexivity | exact C2 | apply Z.leb_le; vm_compute; reflexivity].
Qed.

(* chain_pre with the empty chain: s0 holds rc (an int, sign-extended), never a frame pointer above sp
   (H2CawBase.v caw_chain, 1934271f1f4, verbatim) *)
Lemma wa0_chain : forall ly rd regs rc0, 4096 <= raZ regs -> getr regs 8 = w64 rc0 -> - 2 ^ 31 <= rc0 < 2 ^ 31 ->
  2 ^ 31 <= spZ regs -> ly_top ly <= 2 ^ 47 -> chain_pre ly rd regs [].
Proof.
intros ly rd regs rc0 Hra Hs0 Hrc Hsp Htop. split; [exact Hra|].
destruct (frame0_ok ly regs); [|reflexivity].
replace (bad_next (spZ regs) (ly_top ly) (s0Z regs)) with true; [reflexivity|]. symmetry.
unfold bad_next, s0Z. rewrite Hs0. unfold w64. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with (2 ^ 64).
destruct (Z_le_gt_dec 0 rc0) as [Hp|Hn].
- rewrite Z.mod_small by lia. apply orb_true_intro. left. apply orb_true_intro. left. apply Z.leb_le. lia.
- replace (rc0 mod 2 ^ 64) with (rc0 + 2 ^ 64) by (rewrite <- (Z.mod_small (rc0 + 2 ^ 64) (2 ^ 64)) by lia;
    rewrite Z.add_mod, Z.mod_same, Z.add_0_r, Z.mod_mod by lia; reflexivity).
  apply orb_true_intro. left. apply orb_true_intro. right. apply Z.leb_le. lia.
Qed.

(* the malloc's return site is check_as_written's one RT_malloc site (PRH_Img.v's generated table) *)
Lemma wa0_site : In (caw_pc 64) (pi_ret_sites F_check_as_written RT_malloc).
Proof. unfold caw_pc. rewrite (cwi_base CWI). vm_compute. left. reflexivity. Qed.

(* the malloc's trace: the empty chain's [pc0; ra], or [pc0] (prh_univ_closure's literal clause) *)
Lemma wa0_trace : forall ly regs, prh_univ_closure B CTX0 -> raZ regs = caw_pc 64 ->
  In (call_trace ly (pc_malloc_ra0 (as_code B)) regs []) (as_universe B).
Proof.
intros ly regs HU Hra. apply call_trace_in; [exact (proj1 HU RT_malloc)|].
unfold call_trace0. rewrite Hra.
exact (prh_univ_closure_lit B CTX0 F_check_as_written RT_malloc (caw_pc 64) HU wa0_site).
Qed.

(* a read-only byte is an image byte (S4_PsEntry.v pe_ro_img) *)
Lemma wa0_ro_img : forall a, in_roP segs (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) a -> in_img segs a.
Proof.
intros a [(sg & Hin & _ & Hr) | Hr];
  [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ A_prog_listing PA a Hr)].
Qed.

(* a register the run leaves alone, read at the entry environment *)
Lemma wa0_reg_0 : forall (H : word -> bool) ss ms regs (r : bv 5),
  st_ok segs (wa0_E regs) ss (restrict H ms) ->
  sr_get (ss_regs ss) r = SOff (Z.to_nat (bv_unsigned r)) 0 -> getr (ms_regs ms) r = getr regs r.
Proof.
intros H ss ms regs r HS Hr. rewrite (st_ok_restrict_reg segs H _ ss ms r HS), Hr. cbn [sv_denot].
pose proof (u5_range r) as Hu. unfold wa0_E. rewrite Eimg_low by (unfold A_TEXT; lia).
rewrite (ew_Ereg_nat regs _ _ r) by (rewrite Z2Nat.id; lia).
rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned.
Qed.
(* the same at a cut's frame environment (Caw102A_Kit's caw_Ee) *)
Lemma wa0_reg_e : forall (H : word -> bool) ss ms regs sp0 vals (r : bv 5),
  st_ok_pi segs VAL (caw_Ee regs sp0 vals) ss (restrict H ms) ->
  sr_get (ss_regs ss) r = SOff (Z.to_nat (bv_unsigned r)) 0 -> r <> 2%bv -> getr (ms_regs ms) r = getr regs r.
Proof.
intros H ss ms regs sp0 vals r HS Hr H2.
apply (caw_reg_st (fz := fx) H _ ss ms r _ _ HS Hr). apply caw_Ee_reg; [|exact H2].
pose proof (u5_range r). rewrite Z2Nat.id by lia. reflexivity.
Qed.


Lemma wa0_req : forall z, 0 < z -> req_size z = z.
Proof. intros z Hz. unfold req_size. destruct (Z.eqb_spec z 0); lia. Qed.
Ltac wa0_cs := unfold acallee_saved;
  lazymatch goal with |- context [bv_unsigned ?x] =>
    let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end; lia.
Ltac wa0_in := cbn [In]; repeat first [left; reflexivity | right].
(* sp read back from the engine's SOff 2 (- 80) (Caw102A_WA3.v caw_sp_of_reg) *)
Lemma wa0_sp_of_reg : forall regs E sp0, getr regs 2 = sv_denot E (SOff 2 (- CAW_FRAME)) -> ew E 2 = Z_to_bv 64 sp0 ->
  CAW_FRAME <= sp0 < 2 ^ 64 -> spZ regs = sp0 - CAW_FRAME.
Proof.
intros regs E sp0 Hr E2 Hsp. unfold spZ. rewrite Hr.
change (bv_unsigned (sv_denot E (SOff 2 (- CAW_FRAME)))) with (U E (SOff 2 (- CAW_FRAME))).
unfold CAW_FRAME in *. rewrite U_SOff, E2, unsigned_lit_small by lia. unfold zcanon, M64. apply Z.mod_small. lia.
Qed.
(* the write premise of a run whose one region (the cut's frame, no window) is read-only *)
Ltac wa0_awr0 :=
  lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0 ?bc ?ly' ?own' =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0 bc ly' own') end;
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia | apply awr_ok_nil].

Lemma caw_wa0_holds : caw_seg_WA0 (fx := fx) B SK CTX0 P.
Proof.
unfold caw_seg_WA0. intros Q D HPRE HCNT KX KN HPM.
(* caw_pre BY NAME (the base's projections) *)
pose proof (caw_pre_fpre (fx := fx) B CTX0 D HPRE) as HFP. pose proof (caw_pre_mn (fx := fx) B CTX0 D HPRE) as HMN.
pose proof (caw_pre_univ (fx := fx) B CTX0 D HPRE) as HUNIV.
pose proof (caw_pre_r10 (fx := fx) B CTX0 D HPRE) as H10. pose proof (caw_pre_r11 (fx := fx) B CTX0 D HPRE) as H11.
pose proof (caw_pre_r12 (fx := fx) B CTX0 D HPRE) as H12. pose proof (caw_pre_r13 (fx := fx) B CTX0 D HPRE) as H13.
pose proof (caw_pre_rc (fx := fx) B CTX0 D HPRE) as Hrc. pose proof (caw_pre_doc (fx := fx) B CTX0 D HPRE) as Hdoc.
pose proof (caw_pre_size (fx := fx) B CTX0 D HPRE) as Hsz. pose proof (caw_pre_data0 (fx := fx) B CTX0 D HPRE) as Hd0.
pose proof (caw_pre_data62 (fx := fx) B CTX0 D HPRE) as Hd62. pose proof (caw_pre_src (fx := fx) B CTX0 D HPRE) as HSRC.
pose proof (caw_pre_inblk (fx := fx) B CTX0 D HPRE) as HINB.
pose proof (caw_pre_case (fx := fx) B CTX0 D HPRE) as HCASE. pose proof (caw_pre_tree (fx := fx) B CTX0 D HPRE) as HTREE.
pose proof (caw_pre_ledger (fx := fx) B CTX0 D HPRE) as HLED. pose proof (caw_pre_ran (fx := fx) B CTX0 D HPRE) as HRAN.
pose proof (caw_pre_live (fx := fx) B CTX0 D HPRE) as HLIVE. pose proof (caw_pre_max (fx := fx) B CTX0 D HPRE) as HMAX.
pose proof (caw_pre_frames (fx := fx) B CTX0 D HPRE) as HFRS.
pose proof (caw_pre_room (fx := fx) B CTX0 D HPRE) as HROOM. pose proof (caw_pre_frm0 (fx := fx) B CTX0 D HPRE) as HFRM.
pose proof HFP as (HPX & HROD & HSPHI & HRAC & HFRM0).
pose proof HPX as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof wa0_stk as HSTK. unfold ASTACK, CAW_FRAME in HSTK.
pose proof (cwi_base CWI) as HBASE. pose proof CAW_OFF_val as HOFF.
assert (Hsz0 : 0 <= cw_size D) by (unfold cw_size; lia).
pose proof (wa0_entry D HPRE) as HS.
pose proof (ajournal_x_init (SK := SK) segs B prh_pst (ARcfx B) STK_check_as_written [] _ _ _ _ _ _ _ _ HPX) as HJ.
set (E := wa0_E (cw_regs D)) in HS.
assert (EL : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr (cw_regs D) r).
{ intros n r Hn. pose proof (u5_range r). subst E. unfold wa0_E. rewrite Eimg_low by (unfold A_TEXT; lia).
  exact (ew_Ereg_nat _ _ n r Hn). }
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF).
{ subst E. unfold wa0_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra _ _ 0). }
assert (Usp : bv_unsigned (ew E 2) = spZ (cw_regs D)) by (rewrite (EL 2%nat 2%bv eq_refl); reflexivity).
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold wa0_E; apply Eimg_env).
assert (SHOK : sh_ok segs (SOff 32 0) [] E (mrestrict (w_H (cw_W D)) (cw_mem D))) by constructor.
pose (RUN := @paj_run_x_inv fx rc SK A_prog_listing CW_PAListing PA B prh_pst (ARcfx B) _ LAWS P PLAW).
pose (RUNTO := @paj_run_to_x_inv fx rc SK A_prog_listing CW_PAListing PA B prh_pst (ARcfx B) _ LAWS P PLAW).
pose (BR := paj_branch (L := A_prog_listing) (PI := PA)).
unfold caw_cfg0, cfg_at. rewrite (cwi_entry CWI). change (w64 (BASE + CAW_OFF)) with (Z_to_bv 64 (BASE + CAW_OFF)).
(* ---- +0 .. +60: the frame, the four saves, s1 = doc, s0 = rc, the GOT word and the shadow base, the struct, a0 =
   size + 1, jal __wrap_malloc ---- *)
paj_run_tok_x_inv RUN HS HJ SHOK HPM wa0_Bspan; [wa0_awr Usp|].
rename HS into HS1, HJ into HJ1, HPM into HPM1.
lazymatch type of HS1 with st_ok _ _ _ (restrict _ ?m) => set (ms1 := m) in * end.
(* the bytes the run wrote: the frame [sp0 - 80, sp0) *)
assert (HW1 : forall a, in_wrange E (ss_mem wa0_ss) a -> spZ (cw_regs D) - CAW_FRAME <= a < spZ (cw_regs D)).
{ intros a (r & Hin & Hr). vm_compute in Hin. destruct Hin as [Hq|[Hq|[Hq|[]]]]; subst;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Usp in Hr; unfold CAW_FRAME; lia. }
assert (KA1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ (cw_regs D) - CAW_FRAME <= a < spZ (cw_regs D)) ->
  aview segs (w_H (cw_W D)) (ms_mem ms1) a = aview segs (w_H (cw_W D)) (cw_mem D) a).
{ intros a Ha Hn. apply aview_eq_of. apply HFr. rewrite unsigned_lit_small by lia. intros Hin. exact (Hn (HW1 a Hin)). }
clear HF HFr HG.
(* the frame's words after the run *)
lazymatch type of HS1 with st_ok _ _ ?ss _ =>
  let r0 := eval vm_compute in (nth_error (ss_mem ss) 0) in
  lazymatch r0 with Some ?rg =>
    pose proof (st_ok_region_nth segs E _ _ 0%nat rg HS1 ltac:(vm_compute; reflexivity)) as HREG end end.
cbn [ms_mem restrict] in HREG.
assert (VS : forall od e v, In (YP09.mkChunk od (CVal 8 e)) [YP09.mkChunk (-56) (CVal 8 (SLit 0));
    YP09.mkChunk (-64) (CVal 8 (SAlu ALU_ADD (SOff 10 0) (SOff 11 0))); YP09.mkChunk (-72) (CVal 8 (SOff 10 0));
    YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0));
    YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))] ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  val_mem segs (rdW (cw_W D) (ms_mem ms1)) (spZ (cw_regs D) + od) 8 v).
{ intros od e v Hin Hd Hv. exact (slot_of_region segs E _ _ _ _ _ _ _ od e v HREG Usp Hin Hd Hv). }
(* the registers at the call *)
assert (R1 : getr (ms_regs ms1) 1%bv = Z_to_bv 64 (caw_pc 64)).
{ rewrite (st_ok_restrict_reg segs (w_H (cw_W D)) E _ _ 1%bv HS1). wa0_sv.
  change (SOff 240 2584) with (SOff A_TEXT (CAW_OFF + 64)). rewrite (codeptr_val E _ HEI).
  unfold caw_pc. f_equal. lia. }
assert (Hpc64 : 4096 <= caw_pc 64 < 2 ^ 40).
{ unfold caw_pc. rewrite HBASE, HOFF. unfold A_prog_base. lia. }
assert (R8 : getr (ms_regs ms1) 8%bv = w64 (cw_rc D)).
{ rewrite (st_ok_restrict_reg segs (w_H (cw_W D)) E _ _ 8%bv HS1). wa0_sv. cbn [sv_denot].
  rewrite (EL 12%nat 12%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned. exact H12. }
assert (R9 : getr (ms_regs ms1) 9%bv = w64 (cw_doc D)).
{ rewrite (st_ok_restrict_reg segs (w_H (cw_W D)) E _ _ 9%bv HS1). wa0_sv. cbn [sv_denot].
  rewrite (EL 13%nat 13%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned. exact H13. }
assert (R18 : getr (ms_regs ms1) 18%bv = w64 SHADOW_OFF).
{ rewrite (st_ok_restrict_reg segs (w_H (cw_W D)) E _ _ 18%bv HS1). wa0_sv. cbn [sv_denot].
  rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (R10 : getr (ms_regs ms1) 10%bv = w64 (cw_size D + 1)).
{ rewrite (st_ok_restrict_reg segs (w_H (cw_W D)) E _ _ 10%bv HS1). wa0_sv.
  apply bv_eq. rewrite denot_SOff, (EL 11%nat 11%bv eq_refl), H11. unfold w64.
  rewrite !unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia. }
assert (R2 : getr (ms_regs ms1) 2%bv = sv_denot E (SOff 2 (- CAW_FRAME)))
  by exact (st_ok_restrict_reg segs (w_H (cw_W D)) E _ _ 2%bv HS1).
assert (KR1 : forall r : bv 5, In r [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
  getr (ms_regs ms1) r = getr (cw_regs D) r).
{ intros r Hr. apply (wa0_reg_0 _ _ _ _ r HS1).
  cbn [In] in Hr; repeat (destruct Hr as [<- | Hr]; [vm_compute; reflexivity|]); destruct Hr. }
pose proof (alloc_model_laws_x_cf B (universe_ok_of_ARcf segs B _ _ _ _ _ _ (proj1 HAR))) as AMX.
(* the malloc's trace is a FIXED one of the universe (P'' set: the call rule asks `admits`, YG01.admits_fix, and its
   post carries the trace in the journal's wild budget, which ajournal_xw_fix1 drops again) *)
assert (HTRm : In (call_trace (cw_ly D) (pc_malloc_ra0 (as_code B)) (ms_regs ms1) []) (as_universe B)).
{ apply wa0_trace; [exact HUNIV|]. unfold raZ. rewrite R1. apply unsigned_lit_small. lia. }
(* ---- the call: __wrap_malloc (size + 1), YGcallMxmnKeep's aj_malloc_x_ct_m_keep at the cf instance ---- *)
eapply SRr_bind.
{ eapply (YGcallMxmnKeep.aj_malloc_x_ct_m_keep (SK := SK) segs B prh_pst (ARcfx B) QM_cf (QMm_cf segs B) malloc_cf
    cf_malloc_max free_cf (Wf_cf (as_universe B)) xs_cf LAWS (@pa_segs_low _ _ PA) (pal_env B PAL) OWNLOW WFL AMX
    (QMQ_cf segs B) XSL AMALLOCx
    (cw_W D) E _ ms1 STK_check_as_written (spZ (cw_regs D)) [] (cw_ly D) (cw_S D) (cw_Hp D) (cw_W D) (cw_mem D)
    (cw_md D) [] (cw_ly D) (cw_S D) (cw_Hp D) _ 0 (cw_size D + 1) (- CAW_FRAME) (ew E 2) (Z_to_bv 64 (caw_pc 64)) []
    HS1).
  - exact (pal_malloc B PAL).
  - reflexivity.
  - exact HJ1.
  - exact R10.
  - lia.
  - unfold LIVE_check_as_written in HLIVE. exact HLIVE.
  - exact R2.
  - reflexivity.
  - exact Usp.
  - reflexivity.
  - unfold CAW_FRAME. lia.
  - unfold ASTACK, CAW_FRAME. lia.
  - rewrite (KR1 3%bv ltac:(cbn; tauto)). exact Hgp.
  - rewrite (KR1 4%bv ltac:(cbn; tauto)). exact Htp.
  - exact R1.
  - unfold caw_pc. rewrite <- Z.add_assoc. apply ret_ok_codeptr_v; rewrite HOFF; [lia | reflexivity].
  - (* the call memory's QMm_cf: the room as before, cf_hull_ok from the entry's hull budget
       (PresetHullPay.hull_ok_of_budget), arodata_ok_cf from the reader form at the call memory (the journal's image
       clause carries the entry's) through the bridge at caw_img's relro rows *)
    destruct (QM_cf_of_room segs B _ _ _ _ _ _ (proj1 HAR) HQT (YGcfRoomLive.room_live_room _ HROOM)
      (PresetHullPay.hull_ok_of_budget _ _ (caw_pre_hull (fx := fx) B CTX0 D HPRE))) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6).
    refine (conj Q1 (conj Q2 (conj Q3 (conj Q4 (conj Q5 (conj Q6 _)))))).
    destruct (cwi_relro_eq CWI) as [ERL ERH].
    apply (YGcfAroBridge.arodata_ok_cf_of_P segs B (cw_W D) (ms_mem ms1) (cwi_relro_seg CWI) (cwi_errno_relro CWI)
      (cwi_relro_top CWI) (cwi_ro_reads_nw CWI)).
    rewrite ERL, ERH. intros a Hro Hn He.
    rewrite (ajx_img HJ1 a (wa0_ro_img a Hro) Hn He (fun Hx => cwi_pst_rw CWI a Hx Hro)
      (fp_spares_closed _ _ sink_closed_nil)).
    exact (HROD a Hro Hn He).
  - apply (wa0_chain _ _ _ (cw_rc D)).
    + unfold raZ. rewrite R1, unsigned_lit_small by lia. lia.
    + exact R8.
    + exact Hrc.
    + unfold spZ at 1. rewrite R2. rewrite denot_SOff, Usp. unfold CAW_FRAME. rewrite zcanon_id by (unfold M64; lia). lia.
    + lia.
  - exact (admits_fix _ _ _ (universe_ok_of_ARcf segs B _ _ _ _ _ _ (proj1 HAR)) HTRm). }
(* ---- after the call: the return site +64 ---- *)
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & res & -> & HJ2 & HP2 & R10' & Hfrs2 & HPREc & Htrc
  & (p & trc & Hpath & Hgf & Hleaf & Hpn & Hpa) & HARMS & HMNK).
clear Hleaf.
(* P across the call: the memnorm keep of aj_malloc_x_ct_m_keep and the call law *)
assert (HPM2 : P mem2) by exact (PCALL _ _ HMNK HPM1).
(* the hull: the call uses the scratch's malloc (PresetHullBudget.hull_used_of_call, any return value); the entry's
   budget of the scratch pair pays it, the free's part is left for the cut *)
assert (HHB2 : PresetHullBudget.hull_budget S2 [PresetReqAt.HFr (cw_size D + 1)])
  by exact (PresetHullBudget.hull_budget_app (cw_S D) S2 [PresetReqAt.HMal (cw_size D + 1)]
    [PresetReqAt.HFr (cw_size D + 1)] (caw_pre_hull (fx := fx) B CTX0 D HPRE)
    (PresetHullBudget.hull_used_of_call _ _ _ _ (YGcfSecsStep.secs_malloc_step _ _ _ _ _ Hpath))).
assert (HPREcf := acall_pre_x_xs_cf segs B _ _ _ _ _ _ _ _ HPREc).
(* the journal after the call: the fixed trace leaves the budget; then read BY NAME (YCbqG's ajx_ projections) *)
pose proof (ajournal_xw_fix1 HTRm HJ2) as HJ2f. clear HJ2. rename HJ2f into HJ2.
pose proof (ajx_ar HJ2) as HAR2. pose proof (ajx_hi HJ2) as JF1. pose proof (ajx_blk HJ2) as JF2.
pose proof (ajx_img HJ2) as JF3.
(* the non-primary room after the malloc (a8's RL_malloc_step; its live-set premises rl_sec_ok / rl_b24_ok at the
   entry state from caw_cnt D (HCNT), wa0_counts) *)
destruct (wa0_counts (cw_S D) (proj1 HCNT) (proj2 HCNT)) as (CSEC & C24).
assert (HROOM2 : YGcfRoomLive.room_live_cf S2)
  by exact (YGcfRoomLive.RL_malloc_step segs B _ _ _ _ _ _ _ _ _ _ _ _ _ (p, S2) HPREcf CSEC C24 HROOM Hpath).
(* what the call kept: above its window (the frame), the image off the owned statics and errno *)
assert (HKc : exists Ek, YGcallx.acall_kept_x (rc := rc) segs B (cw_ly D) (cw_S D) (cw_W D) (ms_mem ms1) W2 mem2
   (spZ (cw_regs D) + - CAW_FRAME - ASTACK) (spZ (cw_regs D) + - CAW_FRAME) Ek)
  by (destruct HARMS as [(_ & _ & H & _) | (_ & _ & H)]; eexists; exact H).
destruct HKc as (Ek & HKk). unfold YGcallx.acall_kept_x, acall_kept in HKk. destruct HKk as (K1 & K2 & K3 & K4 & K5 & K6).
assert (KF : forall a, spZ (cw_regs D) - CAW_FRAME <= a < spZ (cw_regs D) ->
  aview segs (w_H W2) mem2 a = aview segs (w_H (cw_W D)) (ms_mem ms1) a)
  by (intros a Ha; apply K1; unfold ASTACK, CAW_FRAME in *; lia).
assert (KST : forall a, Exists (in_zr a) prh_pst -> aview segs (w_H W2) mem2 a = aview segs (w_H (cw_W D)) (cw_mem D) a).
{ intros a Ha. pose proof (cwi_pst_img CWI a Ha) as Hi. pose proof (@pa_segs_low _ _ PA a Hi) as Hl.
  destruct (pal_pst_ok a Ha) as [Ho He]. rewrite (K3 a Hi Ho He). apply KA1; unfold CAW_FRAME; lia. }
assert (VF : forall od e v, In (YP09.mkChunk od (CVal 8 e)) [YP09.mkChunk (-56) (CVal 8 (SLit 0));
    YP09.mkChunk (-64) (CVal 8 (SAlu ALU_ADD (SOff 10 0) (SOff 11 0))); YP09.mkChunk (-72) (CVal 8 (SOff 10 0));
    YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0));
    YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))] ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> - CAW_FRAME <= od -> od + 8 <= 0 ->
  val_mem segs (rdW W2 mem2) (cw_sp0 D + od) 8 v).
{ intros od e v Hin Hd Hv Ho1 Ho2.
  apply (val_mem_kept segs (w_H (cw_W D)) (w_H W2) (ms_mem ms1) mem2 _ 8 v); [|exact (VS od e v Hin Hd Hv)].
  intros kk Hkk. apply KF. unfold cw_sp0. cbn in Hkk. lia. }
(* the saved words, the ledger and the read-only view at the call's end state *)
assert (HSV2 : caw_saved D W2 mem2).
{ unfold caw_saved.
  replace (cw_sp0 D - 8) with (cw_sp0 D + -8) by lia. replace (cw_sp0 D - 16) with (cw_sp0 D + -16) by lia.
  replace (cw_sp0 D - 24) with (cw_sp0 D + -24) by lia. replace (cw_sp0 D - 32) with (cw_sp0 D + -32) by lia.
  split; [|split; [|split]].
  - apply (VF (-8) (SOff 1 0)); [wa0_in | | apply u64_range | unfold CAW_FRAME; lia | lia].
    cbn [sv_denot]. rewrite (EL 1%nat 1%bv eq_refl), Z.add_0_r. reflexivity.
  - apply (VF (-16) (SOff 8 0)); [wa0_in | | apply u64_range | unfold CAW_FRAME; lia | lia].
    cbn [sv_denot]. rewrite (EL 8%nat 8%bv eq_refl), Z.add_0_r. reflexivity.
  - apply (VF (-24) (SOff 9 0)); [wa0_in | | apply u64_range | unfold CAW_FRAME; lia | lia].
    cbn [sv_denot]. rewrite (EL 9%nat 9%bv eq_refl), Z.add_0_r. reflexivity.
  - apply (VF (-32) (SOff 18 0)); [wa0_in | | apply u64_range | unfold CAW_FRAME; lia | lia].
    cbn [sv_denot]. rewrite (EL 18%nat 18%bv eq_refl), Z.add_0_r. reflexivity. }
assert (Hsub : forall x, In x (ablocks B (cw_ly D) (cw_S D)) -> In x (ablocks B ly2 S2))
  by (destruct HARMS as [(_ & Eab & _) | (_ & Eab & _)]; intros x Hx; rewrite Eab; [exact Hx | apply in_or_app; left; exact Hx]).
(* the ledger at the call's end state at the entry's own byte 0 and the record's most (the kit's Batch 2: g_own_ran_out and
   g_most are prh_ledger's rows): KST keeps every prh_pst byte; the hand run +64 -> +68 / +112 writes no memory *)
assert (HLED2 : prh_ledger B ly2 S2 (cw_Hp D) W2 mem2 (cw_Lam D) (cw_peak D) (cw_cnt D) (cw_fail D) (cw_ran D)
  (cw_most D) 0).
{ apply (prh_ledger_kept_aview B (cw_ly D) (cw_S D) (cw_Hp D) (cw_W D) (cw_mem D) ly2 S2 (cw_Hp D) W2 mem2 _ _ _ _ _ _ _
    HLED).
  - exact KST.
  - intros a k i HinL Hi.
    destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ a k _ _ HLED HinL) as (Hk0 & Hab & _).
    change (@cf_head CfParams_preset) with 16 in *.
    apply (JF2 (a - 16) (k + 16) i Hab (Hsub _ Hab)); [rewrite wa0_req by lia; lia | apply inFP_nil].
  - intros a k _ Hab. exact (Hsub _ Hab).
  - apply Permutation_refl. }
assert (HROD2 : arodata_okP segs (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) B (aview segs (w_H W2) mem2)).
{ intros a Hro Hn He.
  rewrite (JF3 a (wa0_ro_img a Hro) Hn He (fun Hx => cwi_pst_rw CWI a Hx Hro) (fp_spares_closed _ _ sink_closed_nil)).
  exact (HROD a Hro Hn He). }
(* the registers after the call: the callee-saved ones are the call's *)
assert (P2 : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs2 r = getr (ms_regs ms1) r)
  by (intros r Hr; pose proof (HP2 _ Hr) as X; rewrite !Z_to_bv_bv_unsigned in X; exact X).
assert (E2' : ew E 2 = Z_to_bv 64 (spZ (cw_regs D)))
  by (rewrite (EL 2%nat 2%bv eq_refl); unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
assert (Hsp1 : spZ (ms_regs ms1) = spZ (cw_regs D) - CAW_FRAME)
  by (apply (wa0_sp_of_reg _ E); [exact R2 | exact E2' | unfold CAW_FRAME; lia]).
assert (Hsp2 : spZ regs2 = spZ (cw_regs D) - CAW_FRAME)
  by (unfold spZ at 1; rewrite (P2 2%bv ltac:(wa0_cs)); exact Hsp1).
(* the scratch's address is a word *)
assert (Hres : 0 <= res < 2 ^ 64).
{ destruct HARMS as [(-> & _) | (H4 & Eab & _)]; [lia|].
  assert (Hin : In (res, cw_size D + 1) (ablocks B ly2 S2)) by (rewrite Eab; apply in_or_app; right; left; reflexivity).
  destruct (alx_blocks segs B (ARcfx B) LAWS _ _ _ _ _ _ _ _ HAR2 Hin) as (_ & _ & Hc & _).
  rewrite wa0_req in Hc by lia. lia. }
(* the symbolic state at +64 (Caw102A_Kit's frame state, no word read) *)
replace (caw_pc 64) with (BASE + (CAW_OFF + 64)) by (unfold caw_pc; lia).
pose proof (caw_st_ok_e (fz := fx) W2 regs2 mem2 (CAW_OFF + 64) (spZ (cw_regs D)) [] [] 0 0 (mkFacts [] [] [])
  ltac:(vm_compute; reflexivity) ltac:(cbn; lia) Hsp2 ltac:(unfold CAW_FRAME; lia) ltac:(intros o Ho; lia) I
  ltac:(split; [exact I | split; exact I])) as HS2.
set (E3 := caw_Ee regs2 (spZ (cw_regs D)) []) in HS2.
assert (HEI3 : img_env VAL A_LIM E3) by (subst E3; unfold caw_Ee; apply Eimg_env).
assert (SHOK3 : sh_ok segs (SOff 32 0) [] E3 (mrestrict (w_H W2) mem2)) by constructor.
assert (U10 : U E3 (SOff 10 0) = res).
{ apply U_atom; [|exact Hres]. subst E3. rewrite (caw_Ee_reg _ _ _ 10 10%bv eq_refl ltac:(discriminate)). exact R10'. }
psrr_branch_tok RUN BR HS2 SHOK3 wa0_Bspan.
- (* +64 beqz taken: a0 = 0, the refused malloc: to CAW_PC_NULL *)
  rewrite branch_eq_U, U10, U_SLit in Hc. replace (zcanon 0) with 0 in Hc by reflexivity. apply Z.eqb_eq in Hc.
  destruct HARMS as [(Hres0 & Eab2 & _ & Herr & Hoom) | (Hres4 & _)]; [| exfalso; lia].
  subst res.
  assert (Ep : p = PNull) by (apply Hpn; reflexivity). subst p.
  paj_run_to_tok_x_inv RUNTO HS2 HJ2 SHOK3 HPM2 wa0_Bspan (CAW_OFF + CAW_PC_NULL); [wa0_awr0|].
  lazymatch type of HF with frame_of _ ?rs _ _ =>
    pose proof (frame_of_read_only _ rs _ _ ltac:(vm_compute; reflexivity) HF) as EM end.
  lazymatch type of HS2 with st_ok_pi _ _ _ _ (restrict _ ?m) => set (ms3 := m) in * end.
  pmkst HS2. rewrite EM in HJ2, HPM2 |- *.
  lazymatch goal with |- context [Z_to_bv 64 (BASE + ?z)] =>
    replace (BASE + z) with (caw_pc CAW_PC_NULL) by (unfold caw_pc, CAW_PC_NULL; rewrite HOFF; lia) end.
  refine (KN fx ly2 S2 (cw_Hp D) W2 (ms_regs ms3) mem2 _ _ _ HPM2).
  split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
  + split; [exact HPRE|]. split; [exact HCNT|]. split; [split; [exact HFRM | intros r _; reflexivity]|].
    split; [unfold caw_J; exact HJ2|].
    split.
    { intros r Hr. rewrite (wa0_reg_e _ _ _ _ _ _ r HS2).
      - rewrite (P2 r). + exact (KR1 r Hr). + cbn [In] in Hr; repeat (destruct Hr as [<- | Hr]; [wa0_cs|]); destruct Hr.
      - cbn [In] in Hr; repeat (destruct Hr as [<- | Hr]; [vm_compute; reflexivity|]); destruct Hr.
      - cbn [In] in Hr; repeat (destruct Hr as [<- | Hr]; [discriminate|]); destruct Hr. }
    split; [exact (caw_sp_st (fz := fx) _ _ _ _ (spZ (cw_regs D)) HS2 ltac:(vm_compute; reflexivity) (caw_Ee_sp _ _ _)
              ltac:(unfold CAW_FRAME; lia))|].
    split; [exact HSV2|]. split; [reflexivity|]. split; [exact HROOM2 | exact HROD2].
  + (* no event (the refused malloc): any entry position i is a position i + 0 of S2 *)
    intros sm x0 os i H0 hist Hp _. exists hist. cbn [length]. rewrite Nat.add_0_r.
    exact (PresetRoomPosKeep.room_pos_keep_alloc_null segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ (cw_size D + 1) _ _ S2 HPREcf
      ltac:(clear - Hsz0 HMAX; lia) ltac:(unfold LIVE_check_as_written in HLIVE; exact HLIVE) HTRm Hpath Hp).
  + (* the refusal is DEAD under the run hypothesis (caw_dead): the rule's granted NULL path at cw_S D, the malloc's own
       input state, where the entry position i holds; at a consumer allocation HMal (size + 1) (the run's event at i,
       caw_run_at_nth) it is impossible (PRH_Refute.prh_refute_at, k := length (caw_evs D) = 2) *)
    intros sm x0 os i H0 hist Hp Hrun Hcons.
    apply (PRH_Refute.prh_refute_at (as_universe B) sm x0 os i (length (caw_evs D)) (PresetReqAt.HMal (cw_size D + 1))
      H0 hist (cw_S D) Hcons (Nat.lt_0_succ 1)
      (caw_run_at_nth sm x0 os i (PresetReqAt.HMal (cw_size D + 1)) [PresetReqAt.HFr (cw_size D + 1)] Hrun)
      eq_refl Hp (WFL (cw_ly D) (cw_S D) (cw_Hp D) (cw_W D) (cw_mem D) (cw_md D) HAR)).
    left. do 4 eexists. split; [exact Hpath | exact Hgf].
  + rewrite (wa0_reg_e _ _ _ _ _ _ 10%bv HS2 ltac:(vm_compute; reflexivity) ltac:(discriminate)). exact R10'.
  + rewrite (wa0_reg_e _ _ _ _ _ _ 8%bv HS2 ltac:(vm_compute; reflexivity) ltac:(discriminate)), (P2 8%bv ltac:(wa0_cs)).
    exact R8.
  + rewrite (wa0_reg_e _ _ _ _ _ _ 9%bv HS2 ltac:(vm_compute; reflexivity) ltac:(discriminate)), (P2 9%bv ltac:(wa0_cs)).
    exact R9.
  + exact Eab2.
  + split; [exact Herr | split; [exact Hoom | exact HLED2]].
- (* +64 beqz not taken: a0 = scr <> 0: to CAW_PC_X *)
  rewrite branch_eq_U, U10, U_SLit in Hc. replace (zcanon 0) with 0 in Hc by reflexivity. apply Z.eqb_neq in Hc.
  destruct HARMS as [(Hres0 & _) | (Hres4 & Eab2 & _)]; [exfalso; exact (Hc Hres0)|].
  assert (Hpn' : p <> PNull) by (intros Ep; apply Hpn in Ep; lia).
  paj_run_to_tok_x_inv RUNTO HS2 HJ2 SHOK3 HPM2 wa0_Bspan (CAW_OFF + CAW_PC_X); [wa0_awr0|].
  lazymatch type of HF with frame_of _ ?rs _ _ =>
    pose proof (frame_of_read_only _ rs _ _ ltac:(vm_compute; reflexivity) HF) as EM end.
  lazymatch type of HS2 with st_ok_pi _ _ _ _ (restrict _ ?m) => set (ms3 := m) in * end.
  pmkst HS2. rewrite EM in HJ2, HPM2 |- *.
  lazymatch goal with |- context [Z_to_bv 64 (BASE + ?z)] =>
    replace (BASE + z) with (caw_pc CAW_PC_X) by (unfold caw_pc, CAW_PC_X; rewrite HOFF; lia) end.
  refine (KX fx ly2 S2 (cw_Hp D) W2 (ms_regs ms3) mem2 _ _ res _ HPM2).
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]].
  + split; [exact HPRE|]. split; [exact HCNT|]. split; [split; [exact HFRM | intros r _; reflexivity]|].
    split; [unfold caw_J; exact HJ2|].
    split.
    { intros r Hr. rewrite (wa0_reg_e _ _ _ _ _ _ r HS2).
      - rewrite (P2 r). + exact (KR1 r Hr). + cbn [In] in Hr; repeat (destruct Hr as [<- | Hr]; [wa0_cs|]); destruct Hr.
      - cbn [In] in Hr; repeat (destruct Hr as [<- | Hr]; [vm_compute; reflexivity|]); destruct Hr.
      - cbn [In] in Hr; repeat (destruct Hr as [<- | Hr]; [discriminate|]); destruct Hr. }
    split; [exact (caw_sp_st (fz := fx) _ _ _ _ (spZ (cw_regs D)) HS2 ltac:(vm_compute; reflexivity) (caw_Ee_sp _ _ _)
              ltac:(unfold CAW_FRAME; lia))|].
    split; [exact HSV2|]. split; [reflexivity|]. split; [exact HROOM2 | exact HROD2].
  + (* the event HMal (size + 1) at the entry position i (caw_run_at_nth): a position i + 1 of S2 *)
    intros sm x0 os i H0 hist Hp Hrun. exists hist. unfold caw_ev1. cbn [length]. rewrite Nat.add_1_r.
    exact (PresetRoomPosKeep.room_pos_keep_alloc segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ (cw_size D + 1) _ _ p S2 HPREcf
      ltac:(clear - Hsz0 HMAX; lia) ltac:(unfold LIVE_check_as_written in HLIVE; exact HLIVE) HTRm Hpath Hpn' Hp
      (caw_run_at_nth _ _ _ _ _ _ Hrun)).
  + rewrite (wa0_reg_e _ _ _ _ _ _ 10%bv HS2 ltac:(vm_compute; reflexivity) ltac:(discriminate)). exact R10'.
  + rewrite (wa0_reg_e _ _ _ _ _ _ 8%bv HS2 ltac:(vm_compute; reflexivity) ltac:(discriminate)), (P2 8%bv ltac:(wa0_cs)).
    exact R8.
  + rewrite (wa0_reg_e _ _ _ _ _ _ 9%bv HS2 ltac:(vm_compute; reflexivity) ltac:(discriminate)), (P2 9%bv ltac:(wa0_cs)).
    exact R9.
  + rewrite (wa0_reg_e _ _ _ _ _ _ 18%bv HS2 ltac:(vm_compute; reflexivity) ltac:(discriminate)), (P2 18%bv ltac:(wa0_cs)).
    exact R18.
  + replace (cw_sp0 D - 72) with (cw_sp0 D + -72) by lia.
    apply (VF (-72) (SOff 10 0)); [wa0_in | | lia | unfold CAW_FRAME; lia | lia].
    cbn [sv_denot]. rewrite (EL 10%nat 10%bv eq_refl), H10, Z.add_0_r. unfold w64.
    rewrite unsigned_lit_small by lia. reflexivity.
  + replace (cw_sp0 D - 64) with (cw_sp0 D + -64) by lia.
    apply (VF (-64) (SAlu ALU_ADD (SOff 10 0) (SOff 11 0))); [wa0_in | | lia | unfold CAW_FRAME; lia | lia].
    apply bv_eq.
    change (bv_unsigned (sv_denot E (SAlu ALU_ADD (SOff 10 0) (SOff 11 0))))
      with (U E (SAlu ALU_ADD (SOff 10 0) (SOff 11 0))).
    rewrite U_SAlu, !U_SOff, (EL 10%nat 10%bv eq_refl), (EL 11%nat 11%bv eq_refl), H10, H11. cbn [zalu_raw].
    unfold w64. rewrite !unsigned_lit_small by lia. rewrite !Z.add_0_r.
    rewrite (zcanon_id (cw_data D)) by (unfold M64; lia). rewrite (zcanon_id (cw_size D)) by (unfold M64; lia).
    apply zcanon_id. unfold M64. lia.
  + replace (cw_sp0 D - 56) with (cw_sp0 D + -56) by lia.
    apply (VF (-56) (SLit 0)); [wa0_in | cbn [sv_denot]; reflexivity | lia | unfold CAW_FRAME; lia | lia].
  + split; [split; [exact Hres4 | exact Eab2]|]. split; [exact HLED2 | exact HHB2].
Qed.

End s.

Print Assumptions caw_wa0_holds.
