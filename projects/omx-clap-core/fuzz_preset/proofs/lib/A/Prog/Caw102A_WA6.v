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
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S4_PsFree.v, with its module paths and module names changed; 218 of its 254 lines of code are new or changed and 490 lines of the source are left out. *)
(* fuzz_preset lib/A, the #102 re-walk of check_as_written on image A' (ASan build): segment WA6 (lane CawA102,
   h-rw-pre-5), the epilogue and the return, from the cut CAW_PC_END (+300) to the text's float-form post.
   rule 24: no function proved. rule 24: proves no function (kind: segment lemma).
   INT102-READY on the kit's cut 7cdbb61b5fa0 (prepared on the batch kit's tip e45217a4c7ba).
   PROVES caw_wa6_holds : caw_seg_WA6 (fx := fx) B SK CTX0 P for an ABSTRACT P with PLAW : srr_inv_laws segs P only
   (call-free: no srr_inv_call, no srr_inv_mn). P is never unfolded: the one engine run goes through the runner twin
   paj_run_x_inv (YC1fPx.v) at the state's float state fy with PLAW, premise the cut's P mem3; the return leaves the
   memory as it is, so the post's P is the run's. Every base name with an implicit float state in a statement of this
   file gets the entry's, `(fx := fx)`.
   BASE OF RECORD (as at the batch-prep base): lib/A/Prog/Caw102A_Base.v,
   Caw102A_Kit.v 3d241a90402d (unchanged); the kit texts and the engine (the P'' set) as the kit's cut carries
   them, by path, as Caw102A_Base.v's header names them: PRH_Base.v, PRH_FnCheck.v c40cf3fdcd2a,
   PRH_Img.v 934516a622e8, YCbqG.v.
   WHAT CHANGED (the batch-prep base; the previous state was this file 1e9ed878cb91 on the base deec9ccf853b) and WHY, each
   forced by the batch text tcheck_as_written_specX (PRH_FnCheck.v c40cf3fdcd2a :832-902):
   - the run-word list DW is gone (the text's binder and prh_univ_closure's argument): the Section variable DW is
     removed, so the statement is caw_seg_WA6 (fx := fx) B SK CTX0 P. This is the only statement change.
   - caw_pre now has 27 conjuncts (Caw102A_Base.v:229-256: the room counts sec_cnt / ccnt24 follow room_live_cf, :862-863,
     then the hull budget and HPOS) and is read BY NAME: the positional destruct of caw_pre is replaced by the base's
     projection caw_pre_fpre (the one part this segment reads, fpre's afn_pre_x).
   - caw_at_END's r = 1 arm gains caw_dead D (the text's OUTCOME, :879-888): this segment does not read the arms (the
     post body Qb is the statement's premise at a0 = r; the top builds it from the cut's arm, caw_dead included), so its
     destruct of the cut, whose top-level conjuncts are unchanged, skips the arm as before.
   Unchanged: this segment reads only the carry's float state, journal, kept / saved registers and sp, fpre's
   afn_pre_x and s1 = r.
   THE CODE (the A' twin's disassembly in the internal file check_as_written.A_new.s of the plan, the internal file PLAN-cno-caw-102.md, DERIVED byte offsets
   from the entry, the listing's slot A_prog_slot AS_check_as_written = CAW_SLOT):
     +300  mv a0, s1                (a0 = r, the cut's s1)
     +304  ld ra, 72(sp); +308 ld s0, 64(sp); +312 ld s1, 56(sp); +316 ld s2, 48(sp)   (the cut's caw_saved words)
     +320  addi sp, sp, 80          (sp = the entry sp0)
     +324  ret                      (to raZ (cw_regs D): paj_ret_at)
   ONE symbolic run +300 -> +324 over the frame [sp0 - 80, sp0) of the Kit (Caw102A_Kit.v caw_st_ok_e: atom 2 is sp0,
   the four saved words atoms 33 .. 36), read-only (no store: the memory after the run is the cut's, frame_of_read_only).
   The post: ra = the entry ra (the journal's return pc, afn_pre_x's ret_ok), aregs_preserved from the restored s0 / s1 /
   s2, sp = sp0 and the kept registers (caw_kregs), the journal from caw_J (ajournal_x_materialize), the float state
   from caw_fl, the body Qb from the statement's premise at a0 = r.
   REFUTED SITES: none (no branch in +300 .. +324).
   NAMED ARGUMENTS: none. SECTION HYPOTHESES: PLAW : srr_inv_laws segs P (owner: the top, Caw102A's composition, which
   instantiates P := caw_mn D and discharges it by caw_mn_laws). Instance bindings only otherwise (the base's CW_PrhImg /
   CW_PAListing / CW_RL; the allocator laws LAWS := AR_laws_x_xs (AR_laws_ok_cf), a Theorem Labs lane's, as FuzzFree.v).
   INPUTS (each BY PATH, as Caw102A_Base.v's header): listing of record
   lib/A/Listing_prog.v 7ed1529926bd, lib/Reusable/YPsym.v b6f5a85d234d; the engine set of the kit's cut
   (YCbqG.v, YGcallcf.v 8645fa6a514f, YC80x.v 14f84f225e8f, YC1fPx.v 7814b594066f, YSRrMemnorm.v
   5ffa8525936b, ...) as the base's header names them.
   MODELS: origin/cold/h-hpreset-7-walk-H2H5 1934271f1f4 lib/A/Prog/H2CawR.v (the same epilogue on the old pin: caw_aregs,
   paj_ret_at, apost_base_xF's witnesses, ajournal_x_materialize), ported to the generic-P runner and this base.
   Numerals: 300 / 324 (DERIVED offsets, in CAW_PC_END), -32 / -24 / -16 / -8 (DERIVED: the ld offsets 48 / 56 / 64 / 72
   minus the frame 80), 8 (LENGTH: a word), 33 .. 36 (DERIVED: the Kit's atom numbering, 32 the shadow base),
   2 ^ 46 / 2 ^ 47 / 2 ^ 4 (the stack atom's range and alignment, astk_ok), 2 ^ 44 (the shadow span), register numbers
   1 2 3 4 8 9 10 18 19-27 (WORD). No ADDRESS. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import Caw102A_Base Caw102A_Kit.
(* the PLAIN build's sink instance is loaded transitively here; it must never fill an ASan sink argument *)
#[global] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* the callee-saved registers are the entry's when sp, s0, s1, s2 are and the others never moved (H2CawR.v caw_aregs) *)
Ltac caw6_inbv := repeat (first [left; apply bv_eq; reflexivity | right]).
Lemma caw6_aregs : forall (regs regs' : bvmap 5 word),
  (forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r) ->
  aregs_preserved regs regs'.
Proof.
intros regs regs' H r Hr. unfold acallee_saved in Hr.
assert (E : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
  r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
repeat (destruct E as [-> | E]; [apply H; caw6_inbv |]). subst r. apply H; caw6_inbv.
Qed.

(* the epilogue's frame words: s2 at sp0 - 32, s1 at - 24, s0 at - 16, ra at - 8 (atoms 33 .. 36); sp0's range *)
Definition caw6_offs : list (Z * N) := [(-32, 8%N); (-24, 8%N); (-16, 8%N); (-8, 8%N)].
Definition caw6_facts : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] [].

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

(* the kept registers of a stage, read off its symbolic state over the Kit's env (atom 2 = sp0) *)
Lemma caw6_kregs_st : forall (fz : YK11.FPState) D (H : word -> bool) E ss ms regs sp0 vals,
  st_ok_pi (fx := fz) segs VAL E ss (restrict H ms) ->
  env_agree 32 (Ereg (regupd regs 2%bv (Z_to_bv 64 sp0)) (map (Z_to_bv 64) (SHADOW_OFF :: vals))) E ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0))
    [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv = true ->
  caw_kregs D regs -> caw_kregs D (ms_regs ms).
Proof.
intros fz D H E ss ms regs sp0 vals HS HA Hl Hk r Hr.
assert (Hne : r <> 2%bv).
{ intros ->. cbn [In] in Hr.
  repeat (destruct Hr as [Hr | Hr]; [apply (f_equal bv_unsigned) in Hr; vm_compute in Hr; discriminate |]). exact Hr. }
pose proof (regs_kept_of_st_ok_pi (fx := fz) (L := A_prog_listing) (PI := PA) E ss (restrict H ms) _ _ _ HS HA Hl r Hr) as X.
cbn [restrict ms_regs] in X. rewrite X. rewrite caw_getr_upd_other by exact Hne. exact (Hk r Hr).
Qed.

Lemma caw_wa6_holds : caw_seg_WA6 (fx := fx) B SK CTX0 P.
Proof.
intros Qb D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k r ownv HAT HQB HPM.
destruct HAT as ((Hpre & _ & [Hfz Hfk] & HJ & Hk & Hsp & HSV & EHp & HROOM & HROD3) & R9 & _ & _ & _).
(* caw_pre BY NAME (the base's projection; a positional pattern over its 27 conjuncts would mis-bind) *)
pose proof (caw_pre_fpre (fx := fx) B CTX0 D Hpre) as (HAFN & _).
pose proof HAFN as (_ & Hra & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof (@YM05.alloc_ceiling_value rc) as Hceilv.
unfold caw_J, cw_sp0 in HJ. unfold cw_sp0, CAW_FRAME in Hsp.
unfold caw_saved, cw_sp0 in HSV. destruct HSV as (V1 & V8 & V9 & V18).
assert (Rsp : 2 ^ 46 <= spZ (cw_regs D) <= 2 ^ 47) by lia.
set (vals := [bv_unsigned (getr (cw_regs D) 18); bv_unsigned (getr (cw_regs D) 9);
              bv_unsigned (getr (cw_regs D) 8); raZ (cw_regs D)]).
pose proof (bv_unsigned_in_range _ (getr (cw_regs D) 18)) as R18.
pose proof (bv_unsigned_in_range _ (getr (cw_regs D) 9)) as R9'.
pose proof (bv_unsigned_in_range _ (getr (cw_regs D) 8)) as R8'.
pose proof (bv_unsigned_in_range _ (getr (cw_regs D) 1)) as R1.
unfold bv_modulus in R18, R9', R8', R1. change (2 ^ Z.of_N 64) with (2 ^ 64) in R18, R9', R8', R1.
assert (HS : st_ok_pi (fx := fy) segs VAL (caw_Ee regs3 (spZ (cw_regs D)) vals)
  (mkSS (CAW_OFF + CAW_PC_END) caw_sr80 [caw_fregion_e caw6_offs 0 0] None caw6_facts)
  (restrict (w_H W3) (@YK11.mkst fy regs3 (Z_to_bv 64 (BASE + (CAW_OFF + CAW_PC_END))) mem3 (YK11.seg_rom segs)))).
{ apply (caw_st_ok_e (fz := fy)).
  - vm_compute. reflexivity.
  - cbn. lia.
  - unfold CAW_FRAME. lia.
  - unfold CAW_FRAME. lia.
  - intros o Ho. lia.
  - cbn [caw_vals_ok caw6_offs vals].
    replace (spZ (cw_regs D) + -32) with (spZ (cw_regs D) - 32) by lia.
    replace (spZ (cw_regs D) + -24) with (spZ (cw_regs D) - 24) by lia.
    replace (spZ (cw_regs D) + -16) with (spZ (cw_regs D) - 16) by lia.
    replace (spZ (cw_regs D) + -8) with (spZ (cw_regs D) - 8) by lia.
    change (8 * Z.of_N 8) with 64. change (Z.of_N 8) with 8. change (N.to_nat 8) with 8%nat.
    unfold raZ in *. repeat split; try assumption; lia.
  - unfold facts_ok, caw6_facts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. split; [|split; exact I].
    split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite caw_Ee_sp, unsigned_lit_small by lia.
    change (2 ^ 4) with 16. split; [lia|]. split; [exact Hal16 | lia]. }
unfold caw_cfg. replace (caw_pc CAW_PC_END) with (BASE + (CAW_OFF + CAW_PC_END)) by (unfold caw_pc; lia).
set (E := caw_Ee regs3 (spZ (cw_regs D)) vals) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold caw_Ee; apply Eimg_env).
assert (SHOK : sh_ok segs (SOff 32 0) [] E (mrestrict (w_H W3) mem3)) by (unfold sh_ok; apply Forall_nil).
assert (HAG : env_agree 32 (Ereg (regupd regs3 2%bv (Z_to_bv 64 (spZ (cw_regs D)))) (map (Z_to_bv 64) (SHADOW_OFF :: vals))) E)
  by (subst E; apply caw_Ee_agree).
assert (E33 : ew E 33 = getr (cw_regs D) 18)
  by (subst E vals; rewrite (caw_Ee_val regs3 _ _ 0 ltac:(lia)); apply Z_to_bv_bv_unsigned).
assert (E34 : ew E 34 = getr (cw_regs D) 9)
  by (subst E vals; rewrite (caw_Ee_val regs3 _ _ 1 ltac:(lia)); apply Z_to_bv_bv_unsigned).
assert (E35 : ew E 35 = getr (cw_regs D) 8)
  by (subst E vals; rewrite (caw_Ee_val regs3 _ _ 2 ltac:(lia)); apply Z_to_bv_bv_unsigned).
assert (E36 : ew E 36 = getr (cw_regs D) 1)
  by (subst E vals; rewrite (caw_Ee_val regs3 _ _ 3 ltac:(lia)); unfold raZ; apply Z_to_bv_bv_unsigned).
assert (E9 : ew E 9 = getr regs3 9) by (subst E; exact (caw_Ee_reg regs3 _ vals 9 9%bv eq_refl ltac:(discriminate))).
assert (E2 : ew E 2 = Z_to_bv 64 (spZ (cw_regs D))) by (subst E; apply caw_Ee_sp).
clearbody E.
pose (RUN := @paj_run_x_inv fy rc SK A_prog_listing CW_PAListing PA B prh_pst _ _ LAWS P PLAW).
pose (RET := @paj_ret_at fy rc A_prog_listing CW_PAListing PA).
(* +300 .. +320: mv a0, s1, the four restores, addi sp, sp, 80; stop at the ret (+324) *)
paj_run_tok_x_inv RUN HS HJ SHOK HPM (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
{ intros a (rg & Hin & Hrg). cbn in Hin. destruct Hin as [<- | []]. cbn in Hrg. lia. }
lazymatch type of HF with frame_of _ ?rs _ _ =>
  pose proof (frame_of_read_only _ rs _ _ ltac:(vm_compute; reflexivity) HF) as Emem end.
clear HF HFr HG.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (8%bv : bv 5) Q8.
prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (10%bv : bv 5) Q10.
rewrite E36 in Q1. rewrite E35 in Q8. rewrite E34 in Q9. rewrite E33 in Q18. rewrite E9, R9 in Q10. rewrite E2 in Q2.
assert (HKP : caw_kregs D (ms_regs ms))
  by exact (caw6_kregs_st fy D (w_H W3) E _ ms regs3 (spZ (cw_regs D)) vals HS HAG ltac:(vm_compute; reflexivity) Hk).
assert (HAREGS : aregs_preserved (cw_regs D) (ms_regs ms)).
{ apply caw6_aregs. intros rr Hrr. cbn [In] in Hrr.
  destruct Hrr as [<- | [<- | [<- | [<- | [<- | [<- | Hrr]]]]]].
  - rewrite Q2. unfold spZ. apply Z_to_bv_bv_unsigned.
  - apply HKP. left; reflexivity.
  - apply HKP. right; left; reflexivity.
  - exact Q8.
  - exact Q9.
  - exact Q18.
  - apply HKP. right; right; exact Hrr. }
rewrite Emem in HJ.
(* +324: the return to the entry ra *)
eapply (RET W3 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. cbn [cfg_ms]. split; [| exact HPM].
rewrite Emem. unfold fpostF, apost_base_xFR.
lazymatch goal with |- exists _ _ _ _ _ _ _ _, mkCfg (YK11.mkst ?rg _ ?m _) ?d = _ /\ _ =>
  exists fy, ly3, S3, Hp3, rg, m, d, k end.
split; [rewrite Q1, Hra; reflexivity|].
(* the float state at the return is the cut's fy: caw_fl's frm_zero and fregs_kept_x fx fy *)
split; [exact Hfz|]. split; [exact Hfk|].
(* the post's journal is at wle' (fpostF, PRH_Base.v): the walk's wle journal lifts by YA0nH.wle_wle' *)
split; [apply (ajournal_xwR_mono (SK := SK) segs B prh_pst _ (@wle segs) (YA0nH.wle' segs YGcfRehidePost.RZ_cf)
  (YA0nH.wle_wle' segs YGcfRehidePost.RZ_cf));
  eapply (ajournal_x_materialize (SK := SK) segs B prh_pst _ LAWS (@pa_segs_low _ _ PA)); exact HJ|].
split; [exact HAREGS|].
exact (HQB _ _ Q10 HAREGS).
Qed.

(* the relation past the scratch's free *)
#[local] Abbreviation RW := (YA0nH.wle' segs YGcfRehidePost.RZ_cf).
(* caw_wa6_holds at RW: the cut's journal is at RW, the run is the R runner, the return an SRr step lifted into RW *)
Lemma caw_wa6_holdsR : caw_seg_WA6R (fx := fx) B SK CTX0 P (YA0nH.wle' segs YGcfRehidePost.RZ_cf).
Proof.
intros Qb D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k r ownv HAT HQB HPM.
destruct HAT as ((Hpre & _ & [Hfz Hfk] & HJ & Hk & Hsp & HSV & EHp & HROOM & HROD3) & R9 & _ & _ & _).
pose proof (caw_pre_fpre (fx := fx) B CTX0 D Hpre) as (HAFN & _).
pose proof HAFN as (_ & Hra & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof (@YM05.alloc_ceiling_value rc) as Hceilv.
unfold caw_JR, cw_sp0 in HJ. unfold cw_sp0, CAW_FRAME in Hsp.
unfold caw_saved, cw_sp0 in HSV. destruct HSV as (V1 & V8 & V9 & V18).
assert (Rsp : 2 ^ 46 <= spZ (cw_regs D) <= 2 ^ 47) by lia.
set (vals := [bv_unsigned (getr (cw_regs D) 18); bv_unsigned (getr (cw_regs D) 9);
              bv_unsigned (getr (cw_regs D) 8); raZ (cw_regs D)]).
pose proof (bv_unsigned_in_range _ (getr (cw_regs D) 18)) as R18.
pose proof (bv_unsigned_in_range _ (getr (cw_regs D) 9)) as R9'.
pose proof (bv_unsigned_in_range _ (getr (cw_regs D) 8)) as R8'.
pose proof (bv_unsigned_in_range _ (getr (cw_regs D) 1)) as R1.
unfold bv_modulus in R18, R9', R8', R1. change (2 ^ Z.of_N 64) with (2 ^ 64) in R18, R9', R8', R1.
assert (HS : st_ok_pi (fx := fy) segs VAL (caw_Ee regs3 (spZ (cw_regs D)) vals)
  (mkSS (CAW_OFF + CAW_PC_END) caw_sr80 [caw_fregion_e caw6_offs 0 0] None caw6_facts)
  (restrict (w_H W3) (@YK11.mkst fy regs3 (Z_to_bv 64 (BASE + (CAW_OFF + CAW_PC_END))) mem3 (YK11.seg_rom segs)))).
{ apply (caw_st_ok_e (fz := fy)).
  - vm_compute. reflexivity.
  - cbn. lia.
  - unfold CAW_FRAME. lia.
  - unfold CAW_FRAME. lia.
  - intros o Ho. lia.
  - cbn [caw_vals_ok caw6_offs vals].
    replace (spZ (cw_regs D) + -32) with (spZ (cw_regs D) - 32) by lia.
    replace (spZ (cw_regs D) + -24) with (spZ (cw_regs D) - 24) by lia.
    replace (spZ (cw_regs D) + -16) with (spZ (cw_regs D) - 16) by lia.
    replace (spZ (cw_regs D) + -8) with (spZ (cw_regs D) - 8) by lia.
    change (8 * Z.of_N 8) with 64. change (Z.of_N 8) with 8. change (N.to_nat 8) with 8%nat.
    unfold raZ in *. repeat split; try assumption; lia.
  - unfold facts_ok, caw6_facts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. split; [|split; exact I].
    split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite caw_Ee_sp, unsigned_lit_small by lia.
    change (2 ^ 4) with 16. split; [lia|]. split; [exact Hal16 | lia]. }
unfold caw_cfg. replace (caw_pc CAW_PC_END) with (BASE + (CAW_OFF + CAW_PC_END)) by (unfold caw_pc; lia).
set (E := caw_Ee regs3 (spZ (cw_regs D)) vals) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold caw_Ee; apply Eimg_env).
assert (SHOK : sh_ok segs (SOff 32 0) [] E (mrestrict (w_H W3) mem3)) by (unfold sh_ok; apply Forall_nil).
assert (HAG : env_agree 32 (Ereg (regupd regs3 2%bv (Z_to_bv 64 (spZ (cw_regs D)))) (map (Z_to_bv 64) (SHADOW_OFF :: vals))) E)
  by (subst E; apply caw_Ee_agree).
assert (E33 : ew E 33 = getr (cw_regs D) 18)
  by (subst E vals; rewrite (caw_Ee_val regs3 _ _ 0 ltac:(lia)); apply Z_to_bv_bv_unsigned).
assert (E34 : ew E 34 = getr (cw_regs D) 9)
  by (subst E vals; rewrite (caw_Ee_val regs3 _ _ 1 ltac:(lia)); apply Z_to_bv_bv_unsigned).
assert (E35 : ew E 35 = getr (cw_regs D) 8)
  by (subst E vals; rewrite (caw_Ee_val regs3 _ _ 2 ltac:(lia)); apply Z_to_bv_bv_unsigned).
assert (E36 : ew E 36 = getr (cw_regs D) 1)
  by (subst E vals; rewrite (caw_Ee_val regs3 _ _ 3 ltac:(lia)); unfold raZ; apply Z_to_bv_bv_unsigned).
assert (E9 : ew E 9 = getr regs3 9) by (subst E; exact (caw_Ee_reg regs3 _ vals 9 9%bv eq_refl ltac:(discriminate))).
assert (E2 : ew E 2 = Z_to_bv 64 (spZ (cw_regs D))) by (subst E; apply caw_Ee_sp).
clearbody E.
pose (RUN := paj_run_x_invR (fx := fy) (SK := SK) (L := A_prog_listing) (PL := CW_PAListing) (PI := PA)
  B prh_pst (ARcfx B) LAWS P PLAW RW (YA0nH.wle'_refl segs YGcfRehidePost.RZ_cf)
  (YA0nH.wle'_trans segs YGcfRehidePost.RZ_cf)).
pose (RET := @paj_ret_at fy rc A_prog_listing CW_PAListing PA).
(* +300 .. +320; stop at the ret (+324) *)
paj_run_tok_x_inv RUN HS HJ SHOK HPM (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
{ intros a (rg & Hin & Hrg). cbn in Hin. destruct Hin as [<- | []]. cbn in Hrg. lia. }
lazymatch type of HF with frame_of _ ?rs _ _ =>
  pose proof (frame_of_read_only _ rs _ _ ltac:(vm_compute; reflexivity) HF) as Emem end.
clear HF HFr HG.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (8%bv : bv 5) Q8.
prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (10%bv : bv 5) Q10.
rewrite E36 in Q1. rewrite E35 in Q8. rewrite E34 in Q9. rewrite E33 in Q18. rewrite E9, R9 in Q10. rewrite E2 in Q2.
assert (HKP : caw_kregs D (ms_regs ms))
  by exact (caw6_kregs_st fy D (w_H W3) E _ ms regs3 (spZ (cw_regs D)) vals HS HAG ltac:(vm_compute; reflexivity) Hk).
assert (HAREGS : aregs_preserved (cw_regs D) (ms_regs ms)).
{ apply caw6_aregs. intros rr Hrr. cbn [In] in Hrr.
  destruct Hrr as [<- | [<- | [<- | [<- | [<- | [<- | Hrr]]]]]].
  - rewrite Q2. unfold spZ. apply Z_to_bv_bv_unsigned.
  - apply HKP. left; reflexivity.
  - apply HKP. right; left; reflexivity.
  - exact Q8.
  - exact Q9.
  - exact Q18.
  - apply HKP. right; right; exact Hrr. }
rewrite Emem in HJ.
(* +324: the return to the entry ra, an SRr step (wle is inside RW) *)
eapply (YA0nH.SRr_SRrG segs RW (YA0nH.wle_wle' segs YGcfRehidePost.RZ_cf)).
eapply (RET W3 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. cbn [cfg_ms]. split; [| exact HPM].
rewrite Emem. unfold fpostF, apost_base_xFR.
lazymatch goal with |- exists _ _ _ _ _ _ _ _, mkCfg (YK11.mkst ?rg _ ?m _) ?d = _ /\ _ =>
  exists fy, ly3, S3, Hp3, rg, m, d, k end.
split; [rewrite Q1, Hra; reflexivity|].
split; [exact Hfz|]. split; [exact Hfk|].
(* the post's journal at RW: the run's RW journal, materialized *)
split; [eapply (ajournal_x_materializeR (SK := SK) segs B prh_pst _ LAWS (@pa_segs_low _ _ PA) RW); exact HJ|].
split; [exact HAREGS|].
exact (HQB _ _ Q10 HAREGS).
Qed.

End s.

Print Assumptions caw_wa6_holds.
Print Assumptions caw_wa6_holdsR.
