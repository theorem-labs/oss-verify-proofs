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
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S4_PsFree.v, with its module paths and module names changed; 305 of its 342 lines of code are new or changed and 489 lines of the source are left out. *)
(* fuzz_preset lib/A, the #102 re-walk of check_as_written on image A' (ASan build): segment WA5 (lane CawA102,
   h-rw-pre-5), the two property checks, from the cut CAW_PC_CHK (+276) to the cut CAW_PC_END (+300).
   rule 24: no function proved. rule 24: proves no function (kind: segment lemma).
   INT102-READY on the kit's cut 7cdbb61b5fa0 (prepared on the batch kit's tip e45217a4c7ba).
   PROVES caw_wa5_holds : caw_seg_WA5 (fx := fx) B SK CTX0 P for an ABSTRACT P with PLAW : srr_inv_laws segs P only
   (call-free: no srr_inv_call, no srr_inv_mn). P is never unfolded: every engine run goes through the runner twin
   paj_run_to_x_inv (YC1fPx.v) at the state's float state fy with PLAW; no run stores, so the memory at +300 is the
   cut's (frame_of_read_only) and P crosses by the runs' HPM. Every base name with an implicit float state in a
   statement of this file gets the entry's, `(fx := fx)`.
   BASE OF RECORD (as at the batch-prep base): lib/A/Prog/Caw102A_Base.v,
   Caw102A_Kit.v 3d241a90402d (unchanged); the kit texts and the engine (the P'' set) as the kit's cut carries
   them, by path, as Caw102A_Base.v's header names them: PRH_Base.v, PRH_FnCheck.v c40cf3fdcd2a,
   PRH_Img.v 934516a622e8, YCbqG.v.
   WHAT CHANGED (the batch-prep base; the previous state was this file 4c8b433ed6bc on the base deec9ccf853b) and WHY, each
   forced by the batch text tcheck_as_written_specX (PRH_FnCheck.v c40cf3fdcd2a :832-902):
   - the run-word list DW is gone (the text's binder and prh_univ_closure's argument): the Section variable DW is
     removed, so the statement is caw_seg_WA5 (fx := fx) B SK CTX0 P. This is the only statement change.
   - caw_pre now has 27 conjuncts (Caw102A_Base.v:229-256: the room counts sec_cnt / ccnt24 follow room_live_cf, :862-863,
     then the hull budget and HPOS) and is read BY NAME: the positional destruct of caw_pre is replaced by the base's
     projections caw_pre_fpre / caw_pre_rc / caw_pre_case (the three parts this segment reads).
   - caw_at_END's r = 1 arm gains caw_dead D (the text's OUTCOME, :879-888): this segment builds only the r = 0 arm
     (`r = 0 /\ ownv = 0 /\ caw_prog D (caw_evs D) S3`, unchanged), so nothing moves with it.
   Unchanged: this segment writes no memory and makes no event, so it hands caw_at_CHK's ledger (at ownv), its caw_prog
   D (caw_evs D) S3 and the carry's caw_cnt D to caw_at_END's r = 0 arm as they are; the property checks are unchanged.
   THE CODE (the A' twin's disassembly in the internal file check_as_written.A_new.s of the plan, the internal file PLAN-cno-caw-102.md, DERIVED byte offsets
   from the entry, the listing's slot A_prog_slot AS_check_as_written = CAW_SLOT):
     +276  seqz a0, s0              (a0 = (rc == 0))
     +280  slti a1, s2, 0           (a1 = (want < 0))
     +284  beq a0, a1 -> +336       ABORT EDGE 1 (__asan_handle_no_return, abort): REFUTED
     +288  mv s1, zero              (r = 0)
     +292  bnez s0 -> +300          (rc != 0: to the epilogue)
     +296  bnez s2 -> +336          ABORT EDGE 2: REFUTED
     +300  CAW_PC_END: the continuation caw_k_END at r = 0, ownv = 0 (caw_at_CHK's ownv = 0)
   THE TWO CASES (caw_pre's `rc = 0 /\ ck_read x = Some t \/ rc <> 0 /\ ck_read x = None` with caw_at_CHK's caw_want D
   want; the assert HC2 below): rc = 0 gives ck_read x = Some t, so caw_want's Some arm at u = t, where want = 1 <->
   t <> t is false, so want = 0; rc <> 0 gives ck_read x = None, so caw_want's None arm, want = -1.
   REFUTED SITES (each in the branch's taken / fall-through goal, from the condition Hc rewritten by branch_eq_U /
   branch_ne_U to the U values of the compared terms):
   - +284 `beq a0, a1` taken -> +336 (abort): rc = 0, want = 0: U (sltu s0 1) = 1 (Ua0) and U (slt s2 0) = 0 (Ua1),
     so (1 =? 0) = true is false; rc <> 0, want = -1: U (sltu s0 1) = 0 (Ua0, from U s0 <> 0, Hu8) and
     U (slt s2 0) = 1 (Ua1, s2 = 2 ^ 64 - 1), so (0 =? 1) = true is false.
   - +296 `bnez s2` taken -> +336 (abort): reached only when rc = 0 (+292 falls through), where want = 0: U s2 = 0
     (U18), so negb (0 =? 0) = true is false.
   - (no abort, infeasible path) +292 `bnez s0` taken when rc = 0 (U s0 = 0, U8) and not taken when rc <> 0 (U s0 <> 0,
     Hu8).
   Both arrivals at +300 (rc <> 0: +292 taken; rc = 0: +296 falls through) give caw_at_END at r = 0 (s1 = zero),
   ownv = 0: the carry (with caw_cnt D as at the cut) with the run's journal at the run's memory (= the cut's), the kept
   registers off the symbolic state (caw6_kregs_st, Caw102A_WA6.v), sp off the symbolic state (caw_sp_st,
   Caw102A_Kit.v), the cut's progress fact caw_prog D (caw_evs D) S3 (no event since the cut), its ablocks and its
   ledger at ownv, the rest as at the cut.
   NAMED ARGUMENTS: none. SECTION HYPOTHESES: PLAW : srr_inv_laws segs P (owner: the top, Caw102A's composition, which
   instantiates P := caw_mn D and discharges it by caw_mn_laws). Instance bindings only otherwise (the base's
   CW_PrhImg / CW_PAListing / CW_RL; the allocator laws LAWS := AR_laws_x_xs (AR_laws_ok_cf), h-mani-a8's, as FuzzFree.v).
   INPUTS (each BY PATH, as Caw102A_Base.v's header): listing of record
   lib/A/Listing_prog.v 7ed1529926bd, lib/Reusable/YPsym.v b6f5a85d234d; the engine set of the kit's cut
   (YCbqG.v, YGcallcf.v 8645fa6a514f, YC80x.v 14f84f225e8f, YC1fPx.v 7814b594066f, YSRrMemnorm.v
   5ffa8525936b, ...) as the base's header names them.
   MODELS: origin/cold/h-hpreset-7-walk-H2H5 1934271f1f4 lib/A/Prog/H2CawF.v (the same checks on the old pin: branches by
   psrr_branch_tok, refuted abort edges by branch_eq_U / branch_ne_U, read-only runs), ported to the generic-P runner.
   Numerals: 276 .. 336 (DERIVED offsets, in CAW_PC_CHK / CAW_PC_END / CAW_PC_ABORT), 2 ^ 31 / 2 ^ 46 / 2 ^ 47 / 2 ^ 64
   (the text's rc bound, the stack range, the word range), 2 ^ 44 (the shadow span), 1 / 0 / -1 (the compared values),
   register numbers 2 8 9 18 (WORD). No ADDRESS. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcallcf YG0lawscf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x YC1fPx YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Img PRH_Reader PRH_FnEx PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import Caw102A_Base Caw102A_Kit Caw102A_WA6.
(* the PLAIN build's sink instance is loaded transitively here; it must never fill an ASan sink argument *)
#[global] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* the write premise of a run whose region is read-only *)
Ltac caw5_nowr := let a := fresh "a" in let rg := fresh "rg" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros a (rg & Hin & Hr); cbn in Hin; destruct Hin as [<- | []]; cbn in Hr; lia.
(* after a read-only run (paj_run_to_tok_x_inv left HF HFr HG): EM : the new machine memory = the cut's *)
Ltac caw5_ro0 HF HFr HG EM :=
  lazymatch type of HF with frame_of _ ?rs _ _ =>
    pose proof (frame_of_read_only _ rs _ _ ltac:(vm_compute; reflexivity) HF) as EM end;
  clear HF HFr HG.
(* the same, chained onto EM : ms_mem <previous state> = the cut's memory *)
Ltac caw5_ro HF HFr HG EM :=
  let Em := fresh "Em" in
  lazymatch type of HF with frame_of _ ?rs _ _ =>
    pose proof (frame_of_read_only _ rs _ _ ltac:(vm_compute; reflexivity) HF) as Em end;
  clear HF HFr HG; rewrite EM in Em; clear EM; rename Em into EM.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Context {PA : PAImg A_prog_listing}.
#[local] Existing Instances CW_PrhImg CW_PAListing CW_RL.
#[local] Notation segs := (@pa_segs _ A_prog_listing PA).
#[local] Notation VAL := (@pa_val _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
Variable B : asyms.
Variable SK : YI16.sink_head.
Variable CTX0 : list (list Z).
(* the allocator's laws: h-mani-a8's AR_laws_ok_cf (YG0lawscf.v), at YGcallcf's bridge (as FuzzFree.v) *)
Let LAWS : AR_laws_x segs B (ARcfx B) cf_head := AR_laws_x_xs segs B (AR_laws_ok_cf segs B).
(* the generic invariant: a call-free segment takes srr_inv_laws only *)
Variable P : (word -> option byte) -> Prop.
Hypothesis PLAW : srr_inv_laws segs P.

(* seqz of a nonzero word is 0 *)
Lemma caw5_sltu1 : forall E a, U E a <> 0 -> U E (SAlu ALU_SLTU a (SLit 1)) = 0.
Proof.
intros E a H. rewrite U_SAlu, U_SLit. cbn [zalu_raw]. change (zcanon 1) with 1.
destruct (Z.ltb_spec (U E a) 1) as [Hlt | _]; [pose proof (U_range E a); lia | reflexivity].
Qed.

Lemma caw_wa5_holds : caw_seg_WA5 (fx := fx) B SK CTX0 P.
Proof.
intros Q D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k want ownv HAT HK HPM.
destruct HAT as ((Hpre & HCNT & HFL & HJ & Hk & Hsp & HSV & EHp & HROOM & HROD3) & Hrp & R8 & R18 & HW & Hown & Eab & HLED).
(* caw_pre BY NAME (the base's projections; a positional pattern over its 27 conjuncts would mis-bind) *)
pose proof (caw_pre_fpre (fx := fx) B CTX0 D Hpre) as HFP.
pose proof (caw_pre_rc (fx := fx) B CTX0 D Hpre) as Hrc.
pose proof (caw_pre_case (fx := fx) B CTX0 D Hpre) as HCASE.
pose proof HFP as ((_ & _ & _ & _ & _ & Hstk & _) & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof (@YM05.alloc_ceiling_value rc) as Hceilv.
assert (Rsp : 2 ^ 46 <= cw_sp0 D <= 2 ^ 47) by (unfold cw_sp0; lia).
(* the two cases: rc = 0 with want = 0, rc <> 0 with want = -1 *)
assert (HC2 : (cw_rc D = 0 /\ want = 0) \/ (cw_rc D <> 0 /\ want = -1)).
{ destruct HCASE as [[Hrc0 Ht] | [Hrcn Hn]]; destruct HW as [[Hn' Hw] | (u & Hu & Hw01 & Hw1)].
  - rewrite Ht in Hn'. discriminate Hn'.
  - left. split; [exact Hrc0|]. rewrite Ht in Hu. injection Hu as Hu.
    destruct Hw01 as [H0 | H1]; [exact H0|]. exfalso.
    destruct (proj1 Hw1 H1) as [_ Hne]. exact (Hne Hu).
  - right. split; [exact Hrcn | exact Hw].
  - rewrite Hn in Hu. discriminate Hu. }
clear HW HCASE.
assert (HS : st_ok_pi (fx := fy) segs VAL (caw_Ee regs3 (cw_sp0 D) [])
  (mkSS (CAW_OFF + CAW_PC_CHK) caw_sr80 [caw_fregion_e [] 0 0] None (mkFacts [] [] []))
  (restrict (w_H W3) (@YK11.mkst fy regs3 (Z_to_bv 64 (BASE + (CAW_OFF + CAW_PC_CHK))) mem3 (YK11.seg_rom segs)))).
{ apply (caw_st_ok_e (fz := fy)).
  - vm_compute. reflexivity.
  - cbn. lia.
  - exact Hsp.
  - unfold CAW_FRAME. lia.
  - intros o Ho. lia.
  - exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. split; [exact I | split; exact I]. }
unfold caw_cfg. replace (caw_pc CAW_PC_CHK) with (BASE + (CAW_OFF + CAW_PC_CHK)) by (unfold caw_pc; lia).
set (E := caw_Ee regs3 (cw_sp0 D) []) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold caw_Ee; apply Eimg_env).
assert (SHOK : sh_ok segs (SOff 32 0) [] E (mrestrict (w_H W3) mem3)) by (unfold sh_ok; apply Forall_nil).
assert (HAG : env_agree 32 (Ereg (regupd regs3 2%bv (Z_to_bv 64 (cw_sp0 D))) (map (Z_to_bv 64) [SHADOW_OFF])) E)
  by (subst E; apply caw_Ee_agree).
assert (E2 : ew E 2 = Z_to_bv 64 (cw_sp0 D)) by (subst E; apply caw_Ee_sp).
assert (E8 : ew E 8 = w64 (cw_rc D))
  by (subst E; rewrite (caw_Ee_reg regs3 _ _ 8 8%bv eq_refl ltac:(discriminate)); exact R8).
assert (E18 : ew E 18 = w64 want)
  by (subst E; rewrite (caw_Ee_reg regs3 _ _ 18 18%bv eq_refl ltac:(discriminate)); exact R18).
clearbody E.
assert (U0 : U E (SLit 0) = 0) by (rewrite U_SLit; reflexivity).
unfold caw_J in HJ.
(* the arrival at +300: caw_k_END at r = 0 and the last-read own value ownv = 0 *)
assert (TO_END : forall pc regs mem md k', pc = BASE + (CAW_OFF + CAW_PC_END) ->
  caw_J B SK D ly3 S3 Hp3 W3 mem md k' -> caw_kregs D regs -> spZ regs = cw_sp0 D - CAW_FRAME ->
  getr regs 9 = w64 0 -> mem = mem3 -> P mem ->
  SRr segs W3 (mkCfg (@YK11.mkst fy regs (Z_to_bv 64 pc) mem (YK11.seg_rom segs)) md) (caw_QP P Q)).
{ intros pc regs mem md k' -> HJ' Hk' Hsp' R9' -> HP'.
  replace (BASE + (CAW_OFF + CAW_PC_END)) with (caw_pc CAW_PC_END) by (unfold caw_pc; lia).
  exact (HK fy ly3 S3 Hp3 W3 regs mem3 md k' 0 ownv
    (conj (conj Hpre (conj HCNT (conj HFL (conj HJ' (conj Hk' (conj Hsp' (conj HSV (conj EHp (conj HROOM HROD3)))))))))
      (conj R9' (conj (or_intror (conj eq_refl (conj Hown Hrp))) (conj Eab HLED)))) HP'). }
pose (RUNTO := @paj_run_to_x_inv fy rc SK A_prog_listing CW_PAListing PA B prh_pst _ _ LAWS P PLAW).
pose (RUN := @paj_run_x_inv fy rc SK A_prog_listing CW_PAListing PA B prh_pst _ _ LAWS P PLAW).
pose (BR := paj_branch (fx := fy) (L := A_prog_listing) (PI := PA)).
(* +276 seqz, +280 slti; stop at the beq (+284) *)
paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1) (CAW_OFF + CAW_PC_END).
{ caw5_nowr. }
caw5_ro0 HF HFr HG EM.
destruct HC2 as [[Hrc0 Hw0] | [Hrcn Hwm]].
- (* rc = 0, want = 0 *)
  assert (U8 : U E (SOff 8 0) = 0) by (rewrite U_SOff, E8, Hrc0; vm_compute; reflexivity).
  assert (U18 : U E (SOff 18 0) = 0) by (rewrite U_SOff, E18, Hw0; vm_compute; reflexivity).
  assert (Ua0 : U E (SAlu ALU_SLTU (SOff 8 0) (SLit 1)) = 1) by (rewrite U_SAlu, U_SLit, U8; vm_compute; reflexivity).
  assert (Ua1 : U E (SAlu ALU_SLT (SOff 18 0) (SLit 0)) = 0) by (rewrite U_SAlu, U_SLit, U18; vm_compute; reflexivity).
  psrr_branch_tok RUN BR HS SHOK (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
  + (* +284 beq taken: ABORT EDGE 1 (+336) refuted, (rc == 0) = 1 <> 0 = (want < 0) *)
    exfalso. rewrite branch_eq_U, Ua0, Ua1 in Hc. vm_compute in Hc. discriminate Hc.
  + clear Hc.
    (* +288 mv s1, zero; stop at bnez s0 (+292) *)
    paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1) (CAW_OFF + CAW_PC_END).
    { caw5_nowr. }
    caw5_ro HF HFr HG EM.
    psrr_branch_tok RUN BR HS SHOK (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
    * (* +292 bnez s0 taken: infeasible, rc = 0 *)
      exfalso. rewrite branch_ne_U, U8, U0 in Hc. vm_compute in Hc. discriminate Hc.
    * clear Hc.
      (* stop at bnez s2 (+296) *)
      paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1) (CAW_OFF + CAW_PC_END).
      { caw5_nowr. }
      caw5_ro HF HFr HG EM.
      psrr_branch_tok RUN BR HS SHOK (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
      -- (* +296 bnez s2 taken: ABORT EDGE 2 (+336) refuted, want = 0 *)
         exfalso. rewrite branch_ne_U, U18, U0 in Hc. vm_compute in Hc. discriminate Hc.
      -- clear Hc.
         (* the fall-through to +300: stop *)
         paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1) (CAW_OFF + CAW_PC_END).
         { caw5_nowr. }
         caw5_ro HF HFr HG EM.
         prreg HS (9%bv : bv 5) Q9.
         pmkst HS.
         eapply TO_END; [first [reflexivity | rewrite CAW_OFF_val; unfold CAW_PC_END; lia] | exact HJ | | | | exact EM | exact HPM].
         ++ lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) =>
              exact (caw6_kregs_st fy D (w_H W3) E _ m regs3 (cw_sp0 D) [] HS HAG ltac:(vm_compute; reflexivity) Hk) end.
         ++ lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) =>
              apply (caw_sp_st (fz := fy) (w_H W3) E _ m (cw_sp0 D) HS eq_refl E2) end. unfold CAW_FRAME. lia.
         ++ first [exact Q9 | rewrite Q9; apply bv_eq; vm_compute; reflexivity].
- (* rc <> 0, want = -1 *)
  assert (Hu8 : U E (SOff 8 0) <> 0).
  { rewrite U_SOff, E8, Z.add_0_r. unfold w64. rewrite Z_to_bv_unsigned. unfold zcanon, M64, bv_wrap, bv_modulus.
    change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_mod by lia. intros H.
    destruct (Z_le_gt_dec 0 (cw_rc D)) as [Hpos | Hneg].
    - rewrite Z.mod_small in H by lia. exact (Hrcn H).
    - assert (Hm : cw_rc D mod 2 ^ 64 = cw_rc D + 2 ^ 64).
      { rewrite <- (Z.mod_small (cw_rc D + 2 ^ 64) (2 ^ 64)) by lia.
        rewrite Z.add_mod, Z.mod_same, Z.add_0_r, Z.mod_mod by lia. reflexivity. }
      lia. }
  assert (U18 : U E (SOff 18 0) = 2 ^ 64 - 1) by (rewrite U_SOff, E18, Hwm; vm_compute; reflexivity).
  assert (Ua0 : U E (SAlu ALU_SLTU (SOff 8 0) (SLit 1)) = 0) by exact (caw5_sltu1 E _ Hu8).
  assert (Ua1 : U E (SAlu ALU_SLT (SOff 18 0) (SLit 0)) = 1) by (rewrite U_SAlu, U_SLit, U18; vm_compute; reflexivity).
  psrr_branch_tok RUN BR HS SHOK (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
  + (* +284 beq taken: ABORT EDGE 1 (+336) refuted, (rc == 0) = 0 <> 1 = (want < 0) *)
    exfalso. rewrite branch_eq_U, Ua0, Ua1 in Hc. vm_compute in Hc. discriminate Hc.
  + clear Hc.
    (* +288 mv s1, zero; stop at bnez s0 (+292) *)
    paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1) (CAW_OFF + CAW_PC_END).
    { caw5_nowr. }
    caw5_ro HF HFr HG EM.
    psrr_branch_tok RUN BR HS SHOK (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
    * clear Hc.
      (* +292 bnez s0 taken: to +300; stop *)
      paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1) (CAW_OFF + CAW_PC_END).
      { caw5_nowr. }
      caw5_ro HF HFr HG EM.
      prreg HS (9%bv : bv 5) Q9.
      pmkst HS.
      eapply TO_END; [first [reflexivity | rewrite CAW_OFF_val; unfold CAW_PC_END; lia] | exact HJ | | | | exact EM | exact HPM].
      -- lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) =>
           exact (caw6_kregs_st fy D (w_H W3) E _ m regs3 (cw_sp0 D) [] HS HAG ltac:(vm_compute; reflexivity) Hk) end.
      -- lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) =>
           apply (caw_sp_st (fz := fy) (w_H W3) E _ m (cw_sp0 D) HS eq_refl E2) end. unfold CAW_FRAME. lia.
      -- first [exact Q9 | rewrite Q9; apply bv_eq; vm_compute; reflexivity].
    * (* +292 bnez s0 not taken: infeasible, rc <> 0 *)
      exfalso. rewrite branch_ne_U, U0 in Hc. apply negb_false_iff, Z.eqb_eq in Hc. exact (Hu8 Hc).
Qed.

(* the relation past the scratch's free *)
#[local] Abbreviation RW := (YA0nH.wle' segs YGcfRehidePost.RZ_cf).
(* YC1fP.paj_branch over any world relation R (a branch takes no step: the case split on its condition) *)
Lemma wa5_branchR : forall (fz : YK11.FPState) (R : world segs -> world segs -> Prop) W E ss ms md Q c a b,
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

(* caw_wa5_holds at RW: the cut's journal is at RW, the runs are the R runners, the arrival at +300 is caw_k_ENDR *)
Lemma caw_wa5_holdsR : caw_seg_WA5R (fx := fx) B SK CTX0 P (YA0nH.wle' segs YGcfRehidePost.RZ_cf).
Proof.
intros Q D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k want ownv HAT HK HPM.
destruct HAT as ((Hpre & HCNT & HFL & HJ & Hk & Hsp & HSV & EHp & HROOM & HROD3) & Hrp & R8 & R18 & HW & Hown & Eab & HLED).
pose proof (caw_pre_fpre (fx := fx) B CTX0 D Hpre) as HFP.
pose proof (caw_pre_rc (fx := fx) B CTX0 D Hpre) as Hrc.
pose proof (caw_pre_case (fx := fx) B CTX0 D Hpre) as HCASE.
pose proof HFP as ((_ & _ & _ & _ & _ & Hstk & _) & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof (@YM05.alloc_ceiling_value rc) as Hceilv.
assert (Rsp : 2 ^ 46 <= cw_sp0 D <= 2 ^ 47) by (unfold cw_sp0; lia).
assert (HC2 : (cw_rc D = 0 /\ want = 0) \/ (cw_rc D <> 0 /\ want = -1)).
{ destruct HCASE as [[Hrc0 Ht] | [Hrcn Hn]]; destruct HW as [[Hn' Hw] | (u & Hu & Hw01 & Hw1)].
  - rewrite Ht in Hn'. discriminate Hn'.
  - left. split; [exact Hrc0|]. rewrite Ht in Hu. injection Hu as Hu.
    destruct Hw01 as [H0 | H1]; [exact H0|]. exfalso.
    destruct (proj1 Hw1 H1) as [_ Hne]. exact (Hne Hu).
  - right. split; [exact Hrcn | exact Hw].
  - rewrite Hn in Hu. discriminate Hu. }
clear HW HCASE.
assert (HS : st_ok_pi (fx := fy) segs VAL (caw_Ee regs3 (cw_sp0 D) [])
  (mkSS (CAW_OFF + CAW_PC_CHK) caw_sr80 [caw_fregion_e [] 0 0] None (mkFacts [] [] []))
  (restrict (w_H W3) (@YK11.mkst fy regs3 (Z_to_bv 64 (BASE + (CAW_OFF + CAW_PC_CHK))) mem3 (YK11.seg_rom segs)))).
{ apply (caw_st_ok_e (fz := fy)).
  - vm_compute. reflexivity.
  - cbn. lia.
  - exact Hsp.
  - unfold CAW_FRAME. lia.
  - intros o Ho. lia.
  - exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. split; [exact I | split; exact I]. }
unfold caw_cfg. replace (caw_pc CAW_PC_CHK) with (BASE + (CAW_OFF + CAW_PC_CHK)) by (unfold caw_pc; lia).
set (E := caw_Ee regs3 (cw_sp0 D) []) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold caw_Ee; apply Eimg_env).
assert (SHOK : sh_ok segs (SOff 32 0) [] E (mrestrict (w_H W3) mem3)) by (unfold sh_ok; apply Forall_nil).
assert (HAG : env_agree 32 (Ereg (regupd regs3 2%bv (Z_to_bv 64 (cw_sp0 D))) (map (Z_to_bv 64) [SHADOW_OFF])) E)
  by (subst E; apply caw_Ee_agree).
assert (E2 : ew E 2 = Z_to_bv 64 (cw_sp0 D)) by (subst E; apply caw_Ee_sp).
assert (E8 : ew E 8 = w64 (cw_rc D))
  by (subst E; rewrite (caw_Ee_reg regs3 _ _ 8 8%bv eq_refl ltac:(discriminate)); exact R8).
assert (E18 : ew E 18 = w64 want)
  by (subst E; rewrite (caw_Ee_reg regs3 _ _ 18 18%bv eq_refl ltac:(discriminate)); exact R18).
clearbody E.
assert (U0 : U E (SLit 0) = 0) by (rewrite U_SLit; reflexivity).
unfold caw_JR in HJ.
(* the arrival at +300: caw_k_ENDR at r = 0 and ownv = 0 *)
assert (TO_END : forall pc regs mem md k', pc = BASE + (CAW_OFF + CAW_PC_END) ->
  caw_JR B SK RW D ly3 S3 Hp3 W3 mem md k' -> caw_kregs D regs -> spZ regs = cw_sp0 D - CAW_FRAME ->
  getr regs 9 = w64 0 -> mem = mem3 -> P mem ->
  YA0nH.SRrG segs RW W3 (mkCfg (@YK11.mkst fy regs (Z_to_bv 64 pc) mem (YK11.seg_rom segs)) md) (caw_QP P Q)).
{ intros pc regs mem md k' -> HJ' Hk' Hsp' R9' -> HP'.
  replace (BASE + (CAW_OFF + CAW_PC_END)) with (caw_pc CAW_PC_END) by (unfold caw_pc; lia).
  exact (HK fy ly3 S3 Hp3 W3 regs mem3 md k' 0 ownv
    (conj (conj Hpre (conj HCNT (conj HFL (conj HJ' (conj Hk' (conj Hsp' (conj HSV (conj EHp (conj HROOM HROD3)))))))))
      (conj R9' (conj (or_intror (conj eq_refl (conj Hown Hrp))) (conj Eab HLED)))) HP'). }
pose (RUNTO := paj_run_to_x_invR (fx := fy) (SK := SK) (L := A_prog_listing) (PL := CW_PAListing) (PI := PA)
  B prh_pst (ARcfx B) LAWS P PLAW RW (YA0nH.wle'_refl segs YGcfRehidePost.RZ_cf)
  (YA0nH.wle'_trans segs YGcfRehidePost.RZ_cf)).
pose (RUN := paj_run_x_invR (fx := fy) (SK := SK) (L := A_prog_listing) (PL := CW_PAListing) (PI := PA)
  B prh_pst (ARcfx B) LAWS P PLAW RW (YA0nH.wle'_refl segs YGcfRehidePost.RZ_cf)
  (YA0nH.wle'_trans segs YGcfRehidePost.RZ_cf)).
pose (BR := wa5_branchR fy RW).
(* +276 seqz, +280 slti; stop at the beq (+284) *)
paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1) (CAW_OFF + CAW_PC_END).
{ caw5_nowr. }
caw5_ro0 HF HFr HG EM.
destruct HC2 as [[Hrc0 Hw0] | [Hrcn Hwm]].
- (* rc = 0, want = 0 *)
  assert (U8 : U E (SOff 8 0) = 0) by (rewrite U_SOff, E8, Hrc0; vm_compute; reflexivity).
  assert (U18 : U E (SOff 18 0) = 0) by (rewrite U_SOff, E18, Hw0; vm_compute; reflexivity).
  assert (Ua0 : U E (SAlu ALU_SLTU (SOff 8 0) (SLit 1)) = 1) by (rewrite U_SAlu, U_SLit, U8; vm_compute; reflexivity).
  assert (Ua1 : U E (SAlu ALU_SLT (SOff 18 0) (SLit 0)) = 0) by (rewrite U_SAlu, U_SLit, U18; vm_compute; reflexivity).
  psrr_branch_tok RUN BR HS SHOK (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
  + (* +284 beq taken: refuted *)
    exfalso. rewrite branch_eq_U, Ua0, Ua1 in Hc. vm_compute in Hc. discriminate Hc.
  + clear Hc.
    (* +288 mv s1, zero; stop at bnez s0 (+292) *)
    paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1) (CAW_OFF + CAW_PC_END).
    { caw5_nowr. }
    caw5_ro HF HFr HG EM.
    psrr_branch_tok RUN BR HS SHOK (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
    * (* +292 bnez s0 taken: infeasible, rc = 0 *)
      exfalso. rewrite branch_ne_U, U8, U0 in Hc. vm_compute in Hc. discriminate Hc.
    * clear Hc.
      (* stop at bnez s2 (+296) *)
      paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1) (CAW_OFF + CAW_PC_END).
      { caw5_nowr. }
      caw5_ro HF HFr HG EM.
      psrr_branch_tok RUN BR HS SHOK (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
      -- (* +296 bnez s2 taken: refuted, want = 0 *)
         exfalso. rewrite branch_ne_U, U18, U0 in Hc. vm_compute in Hc. discriminate Hc.
      -- clear Hc.
         (* the fall-through to +300: stop *)
         paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1) (CAW_OFF + CAW_PC_END).
         { caw5_nowr. }
         caw5_ro HF HFr HG EM.
         prreg HS (9%bv : bv 5) Q9.
         pmkst HS.
         eapply TO_END; [first [reflexivity | rewrite CAW_OFF_val; unfold CAW_PC_END; lia] | exact HJ | | | | exact EM | exact HPM].
         ++ lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) =>
              exact (caw6_kregs_st fy D (w_H W3) E _ m regs3 (cw_sp0 D) [] HS HAG ltac:(vm_compute; reflexivity) Hk) end.
         ++ lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) =>
              apply (caw_sp_st (fz := fy) (w_H W3) E _ m (cw_sp0 D) HS eq_refl E2) end. unfold CAW_FRAME. lia.
         ++ first [exact Q9 | rewrite Q9; apply bv_eq; vm_compute; reflexivity].
- (* rc <> 0, want = -1 *)
  assert (Hu8 : U E (SOff 8 0) <> 0).
  { rewrite U_SOff, E8, Z.add_0_r. unfold w64. rewrite Z_to_bv_unsigned. unfold zcanon, M64, bv_wrap, bv_modulus.
    change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_mod by lia. intros H.
    destruct (Z_le_gt_dec 0 (cw_rc D)) as [Hpos | Hneg].
    - rewrite Z.mod_small in H by lia. exact (Hrcn H).
    - assert (Hm : cw_rc D mod 2 ^ 64 = cw_rc D + 2 ^ 64).
      { rewrite <- (Z.mod_small (cw_rc D + 2 ^ 64) (2 ^ 64)) by lia.
        rewrite Z.add_mod, Z.mod_same, Z.add_0_r, Z.mod_mod by lia. reflexivity. }
      lia. }
  assert (U18 : U E (SOff 18 0) = 2 ^ 64 - 1) by (rewrite U_SOff, E18, Hwm; vm_compute; reflexivity).
  assert (Ua0 : U E (SAlu ALU_SLTU (SOff 8 0) (SLit 1)) = 0) by exact (caw5_sltu1 E _ Hu8).
  assert (Ua1 : U E (SAlu ALU_SLT (SOff 18 0) (SLit 0)) = 1) by (rewrite U_SAlu, U_SLit, U18; vm_compute; reflexivity).
  psrr_branch_tok RUN BR HS SHOK (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
  + (* +284 beq taken: refuted *)
    exfalso. rewrite branch_eq_U, Ua0, Ua1 in Hc. vm_compute in Hc. discriminate Hc.
  + clear Hc.
    (* +288 mv s1, zero; stop at bnez s0 (+292) *)
    paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1) (CAW_OFF + CAW_PC_END).
    { caw5_nowr. }
    caw5_ro HF HFr HG EM.
    psrr_branch_tok RUN BR HS SHOK (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
    * clear Hc.
      (* +292 bnez s0 taken: to +300; stop *)
      paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1) (CAW_OFF + CAW_PC_END).
      { caw5_nowr. }
      caw5_ro HF HFr HG EM.
      prreg HS (9%bv : bv 5) Q9.
      pmkst HS.
      eapply TO_END; [first [reflexivity | rewrite CAW_OFF_val; unfold CAW_PC_END; lia] | exact HJ | | | | exact EM | exact HPM].
      -- lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) =>
           exact (caw6_kregs_st fy D (w_H W3) E _ m regs3 (cw_sp0 D) [] HS HAG ltac:(vm_compute; reflexivity) Hk) end.
      -- lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) =>
           apply (caw_sp_st (fz := fy) (w_H W3) E _ m (cw_sp0 D) HS eq_refl E2) end. unfold CAW_FRAME. lia.
      -- first [exact Q9 | rewrite Q9; apply bv_eq; vm_compute; reflexivity].
    * (* +292 bnez s0 not taken: infeasible, rc <> 0 *)
      exfalso. rewrite branch_ne_U, U0 in Hc. apply negb_false_iff, Z.eqb_eq in Hc. exact (Hu8 Hc).
Qed.

End s.

Print Assumptions caw_wa5_holds.
Print Assumptions caw_wa5_holdsR.
