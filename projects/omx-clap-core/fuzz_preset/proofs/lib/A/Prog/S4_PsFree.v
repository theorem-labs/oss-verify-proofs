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
(* fuzz_preset lib/A, slice S4 (parse_string, image A, ASan build): PsDec's sub-stretch A, the FREE PATH, from its cut
   ps_at_freeP (S4_PsDecKit.v) at PS_FREECUT to the NULL return PS_RET0, where the Section hypothesis ps_seg_ret0P takes
   over. Contract: this row's lib/A/Prog/S4_PsBase.v and PsDec's split lib/A/Prog/S4_PsDecKit.v (ps_at_freeP,
   ps_at_free; S4_PsDecWalk.v), as this row carries them (at a working branch 322e57164236 they
   were blobs ddfbf3f650fe / 22d1543a7e2d / a66ce71e7d7b).
   FILE SET (a Theorem Labs lane PsRebindA): the kit's cut 7cdbb61b5fa0 merged forward into the row's
   prep head (PRH_Base ef7c8ca98529, PRH_FnAlloc 4d8aeba047e5, PRH_FnReader f1ae32e3b2cd; the P'' set's YCbqG.v /
   YCbqGwild.v / YCbqGcallW.v: the budgeted journal ajournal_xw, aj_call_xWb, wild_room_admits, AR_laws_x's field 25);
   the listing and image files are the cut's (int102's). PRW_StepKit.v (pa_slot_lt_ceil_b); PRW_HShadow.v.
   THE CODE (the neutral listing, the internal file parse_string.fuzz_preset.asan.s of the image of record; DERIVED byte offsets from
   parse_string's entry, the listing's A_prog_slot AS_parse_string):
     1276  mv a0, s2          PS_FREECUT: a0 = out, the block the one fuzz_malloc made
     1280  jal fuzz_free      PS_FREE (a PCall slot): ra = the return site at 1284
     1284  li s2, 0           PS_RET0: the join of every refusing path (ps_seg_ret0 from here)
   THE PROOF: one engine run from 1276 to the call (two slots, no store, no shadow check); the call by ps_free_callP, ONE
   lemma at the call's state: YCbqGwild.aj_call_xWb over fuzz_free's BUDGETED text (fpostbm at wbudget [ct] 0, ct the
   call's own trace: pf_xb_of_apost, e1 = 0), fpre's last conjuncts from the jal's return pc 1284 by
   PRW_StepKit.pa_slot_lt_ceil_b (pf_ret_range, a closed goal) and the entry's frm_zero, the call trace from
   prh_univ_closure_lit / prh_cw_ok (s0 = q, the chain through ps_chain0_of_pre / ps_qgap_of_pre / ps_chain_call, read
   below q only: prh_cur_low ends it after one record), the NULL arm of the text refuted (out <> 0: the ledger holds
   out), the non-NULL arm: the block given back (ablocks and Hp the entry's, the ledger's Lam the entry's), the text
   across the call by ps_src_after_call; then ps_seg_ret0P at PS_RET0, with ps_Qres's bad-escape arm.
   THE ADMISSION AND THE BUDGET (the kit's cut 7cdbb61b5fa0: tfuzz_free_specX :320-353 asks
   `admits (as_universe B) (call_trace ..) S` and posts at wbudget [ct] 0; parse_string's text gives the cursor set CW
   by prh_cw_ok and `wild_room (as_universe B) CW 0 (st_depot S)` at entry). The call trace is either a FIXED trace
   (the literal site, or a cursor trace whose saved ra is a pi_call_rets return: prh_univ_closure_cur) or a cursor
   trace IN CW (prh_cw_ok's first arm). Fixed: admits_ct_fix; after the call the free's budget is fixed traces only,
   so the journal goes back to budget [] (ajournal_xw_incl, ajournal_xw_fix1). In CW: wild_room_admits at the room the
   journal keeps from the entry (ajournal_xw_room at WS = []), with the depot's NoDup from AR_laws_x's FIELD 25
   alx_depot_nodup (a Theorem Labs lane's working branch b4ca247aad5d, YCbqG.v 219748197d6b; ruled by the
   owner 02:32Z on a Theorem Labs lane PsRebindA's countermodel); after the call the budget [ct] is within CW.
   THE ROOM POSITION (tfuzz_free_specX of PRH_FnAlloc.v 4d8aeba047e5 at the cut; POST-IMPLICATION):
   no position at entry; for p <> 0 the post transfers any position at the call's state S by its own event
   [HFr (n + cf_head)]. The cut's ps_alloc carries ps_rpos_mal, fuzz_malloc's transfer from the entry state by
   [HMal (Q + 1 + cf_head)]; ps_rpos_snoc composes the two into the bad-escape arm's transfer by
   [HMal ..; HFr ..], its EXACT advance. The text's p <> 0 room facts at entry (room_live_cf S, the class-24 count) are
   the cut's, under `fun _ =>`.
   THE LIVE COUNT: the text asks `YGcfRoomLive.ccnt24 S <= PresetLiveBounds.L24 + PresetLiveBounds.DRV` at the
   call's state (= the cut's: 1276 does not touch the allocator state); it is the ARGUMENT of ps_free_callP,
   ps_seg_free_cntP and ps_seg_free_cnt, which S4_PsTop derives from the text's peak premise (ps_cnts) and the cut's
   block list; never a Section stand-in.
   THE HULL: the text's `p <> 0 -> hull_budget S []` is the entry budget (ps_pre) less the malloc's use, which the cut's
   ps_rpos_mal carries (S4_PsBase.ps_hull_free); the post's hull_used S S2 [] keeps the use in ps_rpos_snoc.
   Numerals: 1276 / 1280 / 1284 (DERIVED offsets inside parse_string, PS_FREECUT / PS_FREE / PS_RET0 of the kit and the
   base); 144 (LENGTH: PS_FRAME, checked by vm_compute); 8 / 16 / 24 (LENGTH: a word, the chain record, the cursor
   struct); 4096 (LENGTH: a page); 2 ^ 30 / 2 ^ 40 / 2 ^ 44 / 2 ^ 47 / 2 ^ 64 (LENGTH: listing, image, shadow, stack
   and word bounds); 2 (LENGTH: code alignment); register numbers 1, 2, 3, 4, 8, 10, 18 (WORD); atom 24 (DERIVED: the
   engine's numbering, s8). No ADDRESS literal: addresses are pa_sigma / pa_val of PAImg_prog.v or PRH_Img.v fields.
   THE GENERIC-P FORM (a Theorem Labs lane 12:18Z / 12:22Z): ps_free_callP / ps_seg_free_cntP are stated over a memory invariant
   P (Section variables P, PLAW : srr_inv_laws segs P, PCALL : srr_inv_call segs P: this stretch crosses a kit call),
   at the cut ps_at_freeP P (ps_carryP: ps_carry with `/\ P mem` last) and the post ps_postP P. The run 1276..1280 goes
   through YSRrMemnorm's runner twin paj_run_x_inv at P with PLAW (premise the carry's P mem). fuzz_free's post is
   m-form (fpostm, Q = fQmn mem Q0: `Q0 .. /\ (memnorm segs mem -> memnorm segs mem')`), so P mem2 is PCALL mem mem2
   applied to the post's own keep and to the cut's P mem: no argument.
   THE STABLE STATEMENT ps_seg_free_cnt (Section pfT) is the P := (fun _ => True) instance (srr_inv_laws_True,
   srr_inv_call_True, ps_seg_ret0_of_True, ps_ex_carryP_T, ps_postP_T of the base). Its statement is the one of
   7e5a49a2288 at the cursor set CW (for DW) with the position argument ps_free_rp deleted (ps_free_rp, ps_free_KF
   and the interim keep ps_free_mn are deleted): an EXEMPT change, made for the callee's TEXT, which now gives the keep
   and the position transfer; its consumer is S4_PsTop.
   SECTION HYPOTHESES (owner: WalkS4's S4_PsTop / the slice's assembly): LAWS (the base's), HFREE (the base's callee
   text), ZSA / IMGV (S4_PsSrc.v's image facts), and HRET0, the stretch ps_seg_ret0P P (S4_PsRet.v ps_ret0_walkP) in
   Section pf and ps_seg_ret0 (S4_PsRet.v ps_ret0_walk) in Section pfT. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0p YCbqG YGcfNames YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep.
(* the memnorm keep's runner side (YSRrMemnorm.v 5ffa8525936b Requires YAkMemnorm only: no LiaTwx2 `lia ::=`) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x YC1fPx YCbqGcall YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoomLive.
(* the budgeted call rule aj_call_xWb, the wild room and its admission (the cut's P'' engine), qualified *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetLiveBounds.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Img PRH_Reader PRH_Charge PRH_FnAlloc PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_CallerJ PRW_HShadow S4_PsBase S4_PsSrc S4_PsDecKit.
(* fpre's return-address ceiling at the jal's return pc (walk-S7B preset-tree-at-2026-10-29T13-38-38Z.tsv (sha256 d07ac858278b; internal record), PRW_StepKit.v blob 0df3991c13f4) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require PRW_StepKit.
(* the re-hiding move: SRrG / SRr' / wle' (YA0nH) at preset's zone YGcfRehidePost.RZ_cf (the kit's primed
   tfuzz_free_specX: SRr' with its post fpostbm at wle'), and the kept relation over R (YCbqGcallW.cj_keptR,
   cj_kept_transR, qualified) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
(* the PLAIN build's sink instance is loaded transitively here; it must never fill an ASan sink argument *)
#[global] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.
Module PSB := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog.S4_PsBase.

(* the engine's shadow span (no shadow check runs in 1276..1280; the run needs a span) *)
Definition PF_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).

(* a list with x last and x nowhere else, split around x *)
Lemma pf_app_last : forall (A : Type) (l b1 b2 : list A) (x : A),
  ~ In x l -> l ++ [x] = b1 ++ x :: b2 -> b1 ++ b2 = l.
Proof.
intros A l. induction l as [|y l IH]; intros b1 b2 x Hn E.
- destruct b1 as [|z b1]; cbn in E.
  + injection E as E. subst b2. reflexivity.
  + injection E as _ E. destruct b1; discriminate E.
- destruct b1 as [|z b1]; cbn in E.
  + injection E as E1 _. subst y. exfalso. apply Hn. left. reflexivity.
  + injection E as E1 E2. subst z. cbn. f_equal. apply (IH b1 b2 x); [intros Hi; apply Hn; right; exact Hi | exact E2].
Qed.
Lemma pf_mod16 : forall e, e mod 16 = 0 -> (- 144 - e) mod 16 = 0.
Proof.
intros e He. apply Z.mod_divide; [lia|]. apply Z.mod_divide in He; [|lia]. destruct He as (t & Ht).
exists (- 9 - t). lia.
Qed.
(* compute the engine's symbolic value of one register in the goal *)
Ltac pf_sr := lazymatch goal with |- context [sr_get ?s ?r] =>
  let e := eval vm_compute in (sr_get s r) in change (sr_get s r) with e end.

Section pf. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
#[local] Existing Instances PSB.PS_PrhImg PSB.PS_PAListing PSB.PS_PAImg.
#[local] Notation segs := (@pa_segs _ A_prog_listing PSB.PS_PAImg).
#[local] Notation VAL := (@pa_val _ A_prog_listing PSB.PS_PAImg).
#[local] Notation BASE := (@pa_val _ A_prog_listing PSB.PS_PAImg A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Variable CTX : list (list Z).
Variable CW : list (list Z).
Hypothesis LAWS : AR_laws_x segs B ARx cf_head.
(* the callee's kit text (the kit's cut 7cdbb61b5fa0, PRH_FnAlloc.v blob 4d8aeba047e5 :320-360: the admission premise and the
   budgeted post at wbudget [ct] 0), the base's Section hypothesis *)
Hypothesis HFREE : tfuzz_free_specX B ARx SK.
(* S4_PsSrc.v's two image facts *)
Hypothesis ZSA : forall q m, In (q, m) (as_zero_shadow B) -> q mod 8 = 0 /\ m mod 8 = 0.
Hypothesis IMGV : ARx_img_shadow_vis segs ARx.
(* the memory invariant the stretch carries (a Theorem Labs lane 12:18Z / 12:22Z): the runner laws, and the call law for the one
   the kit call (fuzz_free) *)
Variable P : (word -> option byte) -> Prop.
Hypothesis PLAW : srr_inv_laws segs P.
Hypothesis PCALL : srr_inv_call segs P.
(* the NULL return stretch after the free (S4_PsRet.v ps_ret0_walkPR at wle' segs RZ_cf), taken here so the stretches
   compose by `apply` *)
Hypothesis HRET0 : ps_seg_ret0PR B ARx SK P (wle' segs YGcfRehidePost.RZ_cf) CTX CW.

(* a register the run leaves alone: its atom, read at the entry environment *)
Lemma pf_reg_atom : forall regs (r : bv 5) n, Z.of_nat n = bv_unsigned r ->
  sv_denot (Eimg (Ereg regs [])) (SOff n 0) = getr regs r.
Proof.
intros regs r n Hn. rewrite sv_atom0. rewrite Eimg_low by (pose proof (u5_range r); unfold A_TEXT; lia).
apply ew_Ereg_nat. exact Hn.
Qed.

(* the return site of the free call is one of parse_string's fuzz_free sites (PRH_Img.v's generated table) *)
Lemma pf_site : In (ps_pc PS_RET0) (pi_ret_sites F_parse_string RT_fuzz_free).
Proof.
assert (Hb : existsb (Z.eqb (ps_pc PS_RET0)) (pi_ret_sites F_parse_string RT_fuzz_free) = true)
  by (vm_compute; reflexivity).
apply existsb_exists in Hb as (x & Hx & Hxe). apply Z.eqb_eq in Hxe. rewrite Hxe. exact Hx.
Qed.
(* the return site as a value: a code word of the listing, below the run's allocation ceiling (fpre's 4th conjunct,
   PRH_Base.v blob ef7c8ca98529 :1002, discharged from the jal's return pc: PRW_StepKit.pa_slot_lt_ceil_b on a closed
   goal) *)
Lemma pf_ret_range : 4096 <= ps_pc PS_RET0 /\ ps_pc PS_RET0 + 4096 < 2 ^ 64 /\
  YK0s.ret_ok (w64 (ps_pc PS_RET0)) /\ ps_pc PS_RET0 < YM05.alloc_ceiling.
Proof.
pose proof (@pa_B_ok _ _ PSB.PS_PAImg) as (HB0 & HB1 & _).
assert (HO0 : 4096 <= PS_OFF) by (unfold Z.le; vm_compute; discriminate).
assert (HO1 : PS_OFF + 4096 <= 2 ^ 30) by (unfold Z.le; vm_compute; discriminate).
unfold ps_pc, PS_RET0. split; [lia|]. split; [lia|].
replace (BASE + PS_OFF + 1284) with (BASE + (PS_OFF + 1284)) by lia. split.
- unfold w64. apply ret_ok_codeptr_v; [lia | vm_compute; reflexivity].
- apply (PRW_StepKit.pa_slot_lt_ceil_b (PS_OFF + 1284)); [lia | vm_compute; reflexivity].
Qed.

(* the kept relation does not look at the model's materialised pages *)
Lemma pf_kept_md : forall STKf sp OR FPc lyc Sc W memc mdc ly2 S2 W2 mem2 md2 md3,
  cj_kept SK segs B prh_pst STKf sp OR FPc lyc Sc W memc mdc ly2 S2 W2 mem2 md2 -> same_but_materialized md2 md3 ->
  cj_kept SK segs B prh_pst STKf sp OR FPc lyc Sc W memc mdc ly2 S2 W2 mem2 md3.
Proof.
intros STKf sp OR FPc lyc Sc W memc mdc ly2 S2 W2 mem2 md2 md3 (H1 & H2 & H3 & H4 & H5) Hs.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [|exact H5].
exact (aos_step_same_io _ _ _ _ H4 (same_io_materialized _ _ Hs)).
Qed.

(* the kept relation from a callee's journal at ANY budget WS (YCbqGcallW.cj_kept_of_journal at WS = [], the same
   proof: cj_kept reads no budget) *)
Lemma pf_kept_of_journal_w : forall STKf sp FPc lyc Sc Hpc W memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 WS OR,
  ajournal_xw (SK := SK) segs B prh_pst ARx STKf sp FPc lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 WS ->
  cj_kept SK segs B prh_pst STKf sp OR FPc lyc Sc W memc mdc ly2 S2 W2 mem2 md2.
Proof.
intros STKf sp FPc lyc Sc Hpc W memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 WS OR HJ.
pose proof (ajx_ly HJ) as Hly. pose proof (ajx_secs HJ) as Hsecs. pose proof (ajx_wle HJ) as Hwle.
pose proof (ajx_io HJ) as Hio. pose proof (ajx_frs HJ) as Hfrs. pose proof (ajx_hi HJ) as F1. pose proof (ajx_blk HJ) as F2.
pose proof (ajx_img HJ) as F3. pose proof (ajx_frm HJ) as F4. pose proof (ajx_gone HJ) as Hgone.
pose proof (ajx_extra HJ) as F5.
split; [exact Hly|]. split; [exact Hsecs|]. split; [exact Hwle|]. split; [exact Hio|].
split; [rewrite Hfrs; reflexivity|].
split; [intros a Ha Hw _; exact (F1 a Ha Hw)|].
split; [intros p m i H1 H2 Hi Hf _; exact (F2 p m i H1 H2 Hi Hf)|].
split; [exact Hgone|].
split; [intros a Hi Hn He Hp Hs _; exact (F3 a Hi Hn He Hp Hs)|].
split; [intros cid pos a Hin Hr Hf _; exact (F4 cid pos a Hin Hr Hf)|].
intros a Hx He _. exact (F5 a Hx He).
Qed.
(* the same over a world relation R (fuzz_free's journal is at wle' segs RZ_cf): the kept relation at R *)
Lemma pf_kept_of_journal_wR : forall (R : world segs -> world segs -> Prop)
  STKf sp FPc lyc Sc Hpc W memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 WS OR,
  ajournal_xwR (SK := SK) segs B prh_pst ARx R STKf sp FPc lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 WS ->
  YCbqGcallW.cj_keptR (SK := SK) segs B prh_pst R STKf sp OR FPc lyc Sc W memc mdc ly2 S2 W2 mem2 md2.
Proof.
intros R STKf sp FPc lyc Sc Hpc W memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 WS OR HJ.
pose proof (ajxR_ly HJ) as Hly. pose proof (ajxR_secs HJ) as Hsecs. pose proof (ajxR_rel HJ) as Hrel.
pose proof (ajxR_io HJ) as Hio. pose proof (ajxR_frs HJ) as Hfrs. pose proof (ajxR_hi HJ) as F1. pose proof (ajxR_blk HJ) as F2.
pose proof (ajxR_img HJ) as F3. pose proof (ajxR_frm HJ) as F4. pose proof (ajxR_gone HJ) as Hgone.
pose proof (ajxR_extra HJ) as F5.
split; [exact Hly|]. split; [exact Hsecs|]. split; [exact Hrel|]. split; [exact Hio|].
split; [rewrite Hfrs; reflexivity|].
split; [intros a Ha Hw _; exact (F1 a Ha Hw)|].
split; [intros p m i H1 H2 Hi Hf _; exact (F2 p m i H1 H2 Hi Hf)|].
split; [exact Hgone|].
split; [intros a Hi Hn He Hp Hs _; exact (F3 a Hi Hn He Hp Hs)|].
split; [intros cid pos a Hin Hr Hf _; exact (F4 cid pos a Hin Hr Hf)|].
intros a Hx He _. exact (F5 a Hx He).
Qed.
(* a budgeted base post (fuzz_free's fpostbm) is the budgeted caller-window post at e = 0 (YCbqGcallW.fpostW_x_of_apost
   at a budget), so aj_call_xWb takes it *)
Lemma pf_xb_of_apost : forall (Pw : list (list Z) -> Prop) STK FP regs ly S Hp W mem md
  (Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop) W' c',
  YCbqGwild.apost_base_xb (SK := SK) segs B prh_pst ARx Pw STK FP regs ly S Hp W mem md Q W' c' ->
  YCbqGwild.fpostW_xb (SK := SK) segs B prh_pst ARx Pw STK 0 FP regs ly S Hp W mem md Q W' c'.
Proof.
intros Pw STK FP regs ly S Hp W mem md Q W' c' (ly' & S' & Hp' & regs' & mem' & md' & k & WS & Hc & HP & HJ & Hpr & HQ).
exists ly', S', Hp', regs', mem', md', k, WS. rewrite !Z.add_0_r.
split; [exact Hc|]. split; [exact HP|]. split; [exact HJ|]. split; [intros a Ha; lia|]. split; [exact Hpr | exact HQ].
Qed.
(* the same over a world relation R (fuzz_free's primed post fpostbm is at wle' segs RZ_cf) *)
Lemma pf_xb_of_apostR : forall (R : world segs -> world segs -> Prop) (Pw : list (list Z) -> Prop) STK FP regs ly S Hp W
  mem md (Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop) W' c',
  YCbqGwild.apost_base_xbR (SK := SK) segs B prh_pst ARx R Pw STK FP regs ly S Hp W mem md Q W' c' ->
  YCbqGwild.fpostW_xbR (SK := SK) segs B prh_pst ARx R Pw STK 0 FP regs ly S Hp W mem md Q W' c'.
Proof.
intros R Pw STK FP regs ly S Hp W mem md Q W' c' (ly' & S' & Hp' & regs' & mem' & md' & k & WS & Hc & HP & HJ & Hpr & HQ).
exists ly', S', Hp', regs', mem', md', k, WS. rewrite !Z.add_0_r.
split; [exact Hc|]. split; [exact HP|]. split; [exact HJ|]. split; [intros a Ha; lia|]. split; [exact Hpr | exact HQ].
Qed.
(* the cursor traces of a free site are in the universe: the kit's PRH_Base.prh_univ_closure_wild (clause 4b) *)
Lemma pf_closure_inU : forall F r w, prh_univ_closure B CTX -> prh_cursor F -> In r (prh_free_sites F) ->
  inU (as_universe B) (prh_trace (pc_free_ra0 (as_code B)) r [w]).
Proof. intros F r w HU Hk Hr. eapply prh_univ_closure_wild; eassumption. Qed.

(* ---- THE CALL: the walk at fuzz_free's entry (pc = the callee, ra = the return site PS_RET0, a0 = out), the cut's
   facts at the call's state, the live count of the callee's text and the post position as arguments; the memnorm keep
   comes from the text's m-form post. The kit's primed text crosses the free: the call is the engine's rule over R at
   wle' segs RZ_cf (YCbqGwild.aj_call_xWbR; the cut's journal, at wle, lifted once here), and from the post state on
   the walk's journal and kept relation are at wle', so the NULL return is ps_seg_ret0PR at wle' ---- *)
Lemma ps_free_callP : forall D ly S Hp W regs mem md out Q k,
  ps_pre B ARx CTX CW D ->
  ps_carryP B ARx SK P D ly S Hp W mem md k [] -> ps_alloc B D ly S Hp W mem out Q -> ps_gptp D regs ->
  pj_in_okR segs (rdW W mem) (pi_q D) (pi_text D) (pi_len D) (pi_p D) (pi_d D) (pi_tb D) ->
  arodata_okP segs (@pa_relro_lo _ A_prog_listing PSB.PS_PAImg) (@pa_relro_hi _ A_prog_listing PSB.PS_PAImg) B
    (aview segs (w_H W) mem) ->
  PjGrammar.scan (ps_x D) = Some Q -> PjGrammar.decode (ps_x D) = None ->
  getr regs 2 = w64 (PS_SP D) -> getr regs 1 = w64 (ps_pc PS_RET0) -> getr regs 10 = w64 out ->
  getr regs 8 = w64 (pi_q D) ->
  YGcfRoomLive.ccnt24 S <= PresetLiveBounds.L24 + PresetLiveBounds.DRV ->
  SRr' segs YGcfRehidePost.RZ_cf W (cfg_at segs (@pa_sigma _ A_prog_listing PSB.PS_PAImg AS_fuzz_free) regs mem md)
    (ps_postPR B ARx SK P (wle' segs YGcfRehidePost.RZ_cf) CW D).
Proof.
intros D ly S Hp W regs mem md out Q k HPRE HC HAL HGT HIN HROD HSC HDN R2 R1 R10 R8 HC24.
pose proof HPRE as ((HPX & HROD0 & HSTKHI) & HUNIV & HCH & HCLOW & HCW & HGAP & HROOM0 & (HWR0 & HCNTS0) & H100 & HIN0
  & Hpl & Hnth & HWIN & Hq1 & Hq2 & HRA0 & HSRC0 & HHOME0 & HLED0 & HCNT & HLIVE).
pose proof HPX as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
pose proof Hstk0 as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HWIN as (He0 & He16 & Hetop & Hepres).
destruct HC as (HJ & HK & HSV & HSRC & HHOME & HPM).
pose proof (ajx_ar HJ) as HAR. pose proof (ajx_ly HJ) as Hly.
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof HAL as HALc.
destruct HAL as (Hcnt & Hout & Hout16 & EHp & Eab & HLED & Hvis & Hroom & Hpos1 & Hbb).
pose proof cf_head_nonneg as Hh0.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HFR : PS_FRAME = 144) by (vm_compute; reflexivity).
assert (EPS : PS_SP D = spZ (pi_regs D) - 144) by (unfold PS_SP; rewrite HFR; reflexivity).
assert (EWSP : PS_WSP D = spZ (pi_regs D) + pi_e D) by reflexivity.
assert (EWSTK : PS_WSTK D = STK_parse_string + pi_e D) by reflexivity.
(* DERIVED (vm_compute on the generated PRH_Img values): fuzz_free's budget and parse_string's frame fit parse_string's *)
assert (HSTKf : 0 <= STK_fuzz_free) by (unfold Z.le; vm_compute; discriminate).
assert (HSTKb : STK_fuzz_free + 144 <= STK_parse_string) by (unfold Z.le; vm_compute; discriminate).
pose proof pf_ret_range as (Hpc0 & Hpc1 & Hpcok & Hpcc).
assert (Hsp : spZ regs = PS_SP D).
{ unfold spZ. rewrite R2. unfold w64. apply unsigned_lit_small. unfold PS_SP. rewrite HFR. lia. }
assert (Hraz : raZ regs = ps_pc PS_RET0) by (unfold raZ; rewrite R1; unfold w64; apply unsigned_lit_small; lia).
assert (Hs0 : s0Z regs = pi_q D) by (unfold s0Z; rewrite R8; unfold w64; apply unsigned_lit_small; lia).
(* the block the malloc made, and its footprint *)
assert (Hin_o : In (out - cf_head, Z.of_nat Q + 1 + cf_head) (ablocks B ly S))
  by (rewrite Eab; apply in_or_app; right; left; reflexivity).
assert (Rq : req_size (Z.of_nat Q + 1 + cf_head) = Z.of_nat Q + 1 + cf_head) by (apply ps_req; lia).
destruct (alx_blocks segs B ARx LAWS ly S Hp W mem md _ _ HAR Hin_o) as (_ & H4096o & Hco & _).
rewrite Rq in Hco.
assert (Hnew : ~ In (out - cf_head, Z.of_nat Q + 1 + cf_head) (ablocks B (pi_ly D) (pi_S D)))
  by (apply (ps_newblk B ARx LAWS ly S (pi_ly D) (pi_S D) Hp W mem md _ HAR); [cbn [snd]; lia | exact Eab]).
assert (HFP1 : forall a, inFP (ablocks_fp [(out - cf_head, Z.of_nat Q + 1 + cf_head)]) a ->
  out - cf_head <= a < out + Z.of_nat Q + 1).
{ intros a (r & Hr & Ha). destruct Hr as [<- | []]. cbn [fst snd] in Ha. rewrite Rq in Ha. lia. }
assert (Htmp : forall a, out - cf_head <= a < out + Z.of_nat Q + 1 ->
  in_tmp_block (ablocks B (pi_ly D) (pi_S D)) (ablocks B ly S) a).
{ intros a Ha. exists (out - cf_head), (Z.of_nat Q + 1 + cf_head). split; [exact Hin_o|].
  split; [exact Hnew|]. rewrite Rq. lia. }
(* ---- the chain from q at the call view, and the free's trace ---- *)
assert (Hag : forall a, spZ (pi_regs D) <= a < pi_q D ->
  aview segs (w_H W) mem a = aview segs (w_H (pi_W D)) (pi_mem D) a).
{ intros a Ha. pose proof HK as (_ & _ & _ & _ & _ & K1 & _). apply K1; [lia | lia |].
  intros Hor. apply inFP_cons in Hor as [Hor | Hor]; [lia | exact (inFP_nil a Hor)]. }
assert (Hf0 : frame0_ok ly regs = true).
{ unfold frame0_ok. apply Z.ltb_lt. rewrite Hsp, Etop. unfold PS_SP. rewrite HFR. lia. }
(* the call trace is FIXED (the literal site, or a cursor trace at a pi_call_rets return) or a cursor trace IN CW *)
assert (HTR : exists ch, achain ly (aview segs (w_H W) mem) (PS_SP D) (pi_q D) ch /\
  (In (call_trace ly (pc_free_ra0 (as_code B)) regs ch) (u_fix (as_universe B)) \/
   (In (call_trace ly (pc_free_ra0 (as_code B)) regs ch) CW /\
    inU (as_universe B) (call_trace ly (pc_free_ra0 (as_code B)) regs ch)))).
{ set (rd := fun a => if a <? pi_q D then aview segs (w_H W) mem a else aview segs (w_H (pi_W D)) (pi_mem D) a).
  assert (Hrd : forall a, spZ (pi_regs D) <= a < ly_top (pi_ly D) -> rd a = aview segs (w_H (pi_W D)) (pi_mem D) a).
  { intros a Ha. subst rd. cbv beta. destruct (Z.ltb_spec a (pi_q D)) as [Hl|Hl]; [apply Hag; lia | reflexivity]. }
  destruct (ps_chain_call D rd (ps_chain0_of_pre B ARx CTX CW D HPRE) (ps_qgap_of_pre B ARx CTX CW D HPRE)
    ltac:(lia) Hrd) as (ch & Hc).
  (* below q the reader is the call view, and the call view is the entry view *)
  assert (Hrdc : forall o, 8 <= o <= 16 -> rdword (aview segs (w_H W) mem) (pi_q D - o) = rdword rd (pi_q D - o)).
  { intros o Ho. symmetry. apply rdword_ext. intros kk Hkk. subst rd. cbv beta.
    rewrite (proj2 (Z.ltb_lt (pi_q D - o + kk) (pi_q D))) by lia. reflexivity. }
  assert (Hrde : forall o, 8 <= o <= 16 ->
    rdword rd (pi_q D - o) = rdword (aview segs (w_H (pi_W D)) (pi_mem D)) (pi_q D - o)).
  { intros o Ho. apply rdword_ext. intros kk Hkk. subst rd. cbv beta.
    rewrite (proj2 (Z.ltb_lt (pi_q D - o + kk) (pi_q D))) by lia. apply Hag. lia. }
  unfold prh_cw_ok in HCW. unfold prh_cur_low in HCLOW. rewrite ps_s0_q in HCW, HCLOW.
  exists ch. unfold call_trace. rewrite Hf0.
  change (PS_SP D) with (spZ (pi_regs D) - pi_frame F_parse_string).
  destruct Hc as [(Hbad & ->) | (Hv1 & Hv2 & Hv3 & Hfp & Hfa)].
  - split; [apply (achain_ly_top (pi_ly D) ly); [exact Etop | left; exact (conj Hbad eq_refl)]|].
    rewrite Hraz. left. exact (prh_univ_closure_lit B CTX F_parse_string RT_fuzz_free (ps_pc PS_RET0) HUNIV pf_site).
  - destruct ch as [|[[fp ra] nfp] rest].
    + split; [|rewrite Hraz; left; exact (prh_univ_closure_lit B CTX F_parse_string RT_fuzz_free (ps_pc PS_RET0) HUNIV pf_site)].
      apply (achain_ly_top (pi_ly D) ly); [exact Etop|]. right.
      split; [exact Hv1|]. split; [exact Hv2|]. split; [exact Hv3|]. split; [|exact Hfa].
      cbn [fpchain] in Hfp |- *. destruct Hfp as (r0 & Hr0 & Hr0b). exists r0. split; [|exact Hr0b].
      rewrite (Hrdc 8) by lia. exact Hr0.
    + cbn [fpchain] in Hfp. destruct Hfp as (-> & Hq8' & Hra & Hnfp & Hra4 & Hrest).
      assert (Hnlow : nfp < alloc_ceiling) by (apply HCLOW; rewrite <- (Hrde 16) by lia; exact Hnfp).
      assert (Hbn : forall top, bad_next (pi_q D) top nfp = true).
      { intros top. unfold bad_next. replace (nfp <=? pi_q D) with true by (symmetry; apply Z.leb_le; lia). reflexivity. }
      rewrite Hbn in Hrest. cbv beta iota in Hrest. subst rest.
      split.
      * apply (achain_ly_top (pi_ly D) ly); [exact Etop|]. right.
        split; [exact Hv1|]. split; [exact Hv2|]. split; [exact Hv3|]. split; [|exact Hfa].
        cbn [fpchain]. rewrite Hbn.
        split; [reflexivity|]. split; [exact Hq8'|]. split; [rewrite (Hrdc 8) by lia; exact Hra|].
        split; [rewrite (Hrdc 16) by lia; exact Hnfp|]. split; [exact Hra4 | exact eq_refl].
      * rewrite Hraz.
        assert (Hsite : In (ps_pc PS_RET0) (prh_free_sites F_parse_string))
          by (unfold prh_free_sites; apply in_or_app; right; exact pf_site).
        destruct (HCW (ps_pc PS_RET0) ra Hsite ltac:(rewrite <- (Hrde 8) by lia; exact Hra)) as [Hcw | Hcr].
        -- right. split; [exact Hcw|].
           exact (pf_closure_inU F_parse_string (ps_pc PS_RET0) ra HUNIV (or_introl eq_refl) Hsite).
        -- left. exact (prh_univ_closure_cur B CTX F_parse_string (ps_pc PS_RET0) ra HUNIV (or_introl eq_refl) Hsite Hcr). }
destruct HTR as (ch1 & Hch1 & Htrs).
(* the wild room at the call's state: the entry's (the text's premise), kept by the journal at budget [] *)
assert (HWR : YCbqGwild.wild_room (as_universe B) CW 0 (st_depot S))
  by exact (YCbqGwild.ajournal_xw_room (SK := SK) segs B prh_pst ARx (PS_WSTK D) (PS_WSP D) [(pi_q D, pi_q D + 8)]
              (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_mem D) (pi_md D) [] ly S Hp W mem md k [] CW 0
              HJ HWR0 (le_n 0)).
(* THE ADMISSION of the free text (the batch kit PRH_FnAlloc 4d8aeba047e5 :340): a fixed trace, or a CW trace by the wild
   room, the depot's NoDup from LAWS (AR_laws_x field 25, alx_depot_nodup) at the call's ARx state *)
assert (Hadm : admits (as_universe B) (call_trace ly (pc_free_ra0 (as_code B)) regs ch1) S).
{ destruct Htrs as [Hfix | (Hcw & HinU)].
  - exact (admits_ct_fix _ _ _ _ _ _ Hfix).
  - exact (YCbqGwild.wild_room_admits (as_universe B) CW 0 S _ (alx_depot_nodup _ _ _ LAWS ly S Hp W mem md HAR) HWR
             HinU (or_introl Hcw)). }
assert (Eout0 : (out =? 0) = false) by (apply Z.eqb_neq; lia).
(* ---- the call ---- *)
unfold cfg_at, w64. unfold SRr'.
eapply (SRrG_bind segs (wle' segs YGcfRehidePost.RZ_cf) (wle'_trans segs YGcfRehidePost.RZ_cf)).
{ eapply (YCbqGwild.aj_call_xWbR (SK := SK) segs B prh_pst ARx LAWS (@pa_segs_low _ _ PSB.PS_PAImg)
    (wle' segs YGcfRehidePost.RZ_cf) (wle'_refl segs YGcfRehidePost.RZ_cf) (wle'_trans segs YGcfRehidePost.RZ_cf)
    W regs mem
    (pa_sigma AS_fuzz_free) (PS_WSTK D) (PS_WSP D) [(pi_q D, pi_q D + 8)]
    (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_mem D) (pi_md D) [] ly S Hp md k []
    STK_fuzz_free 0 (ablocks_fp [(out - cf_head, Z.of_nat Q + 1 + cf_head)]) (PS_SP D - PS_WSP D)
    (w64 (ps_pc PS_RET0)) ch1).
  - (* the cut's journal is at wle; at the call it is the journal at wle' *)
    eapply (ajournal_xwR_mono (SK := SK) segs B prh_pst ARx (@wle segs));
      [exact (wle_wle' segs YGcfRehidePost.RZ_cf) | exact HJ].
  - rewrite Hsp. lia.
  - replace (PS_SP D - PS_WSP D) with (- 144 - pi_e D) by lia. exact (pf_mod16 _ He16).
  - lia.
  - exact HSTKf.
  - lia.
  - lia.
  - reflexivity.
  - lia.
  - destruct HGT as [G3 _]. rewrite G3. exact Hgp0.
  - destruct HGT as [_ G4]. rewrite G4. exact Htp0.
  - exact R1.
  - exact Hpcok.
  - unfold w64. rewrite unsigned_lit_small by lia. exact Hpc0.
  - replace (PS_WSP D + (PS_SP D - PS_WSP D)) with (PS_SP D) by lia. rewrite Hs0. exact Hch1.
  - intros HP1 _.
    assert (HFP : fpre B ARx STK_fuzz_free ly S Hp W regs mem md ch1).
    { refine (conj HP1 (conj HROD (conj _ (conj _ (ps_frm0 B ARx CTX CW D HPRE)))));
        [rewrite Hsp, Eshi; lia | rewrite Hraz; exact Hpcc]. }
    eapply (SRrG_mono segs (wle' segs YGcfRehidePost.RZ_cf)).
    { exact (HFREE (pi_most D) (pi_own D)
        ly S Hp W regs mem md ch1 out (Z.of_nat Q + 1) ((out, Z.of_nat Q + 1) :: pi_Lam D) _ _ _ _
        HFP (fun _ => Hroom) (fun _ => HC24)
        (* the hull budget for no event: the text's less the malloc's use (S4_PsBase.ps_hull_free) *)
        (fun _ => ps_hull_free B ARx CTX CW D Q S HPRE Hpos1)
        Hadm R10 (or_intror (or_introl eq_refl)) HLED). }
    intros W' c' _ HPOST. rewrite Eout0 in HPOST. exact (pf_xb_of_apostR _ _ _ _ _ _ _ _ _ _ _ _ _ _ HPOST).
  - intros a Ha. right; left. exact (Htmp a (HFP1 a Ha)). }
(* ---- after the call: the post state at PS_RET0 ---- *)
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & WS1 & -> & HB1 & HJ2 & HJ1 & _ & HP2 & (HQ2 & HKM)).
(* the invariant across the call: the call law at the text's own memnorm keep (fQmn's second conjunct) *)
assert (HPM2 : P mem2) by exact (PCALL mem mem2 HKM HPM).
(* fuzz_free's post, read BY NAME through the kit's projection layer (PRH_FnAlloc.v tffP_R_of and the fields of tffP_R,
   the arm records tffP_R1 / tffP_R2); md2 and regs2 are the arguments of the post that its body does not mention *)
apply tffP_R_of with (regs' := regs2) (md' := md2) in HQ2.
pose proof (tffP_room HQ2) as Hroom2. pose proof (tffP_hull HQ2) as HHU2. pose proof (tffP_pos_free HQ2) as Hfr2.
destruct (tffP_arm HQ2) as [HA1 | HA2]; [pose proof (tffP1_null (tffP_R1_of HA1)); lia|].
destruct (tffP_R2_of HA2) as (l1 & l2 & HR2).
pose proof (tffP2_hp HR2) as EHp2. destruct (tffP2_ablocks HR2) as (b1 & b2 & Eb1 & Eb2).
pose proof (tffP2_lam HR2) as El. pose proof (tffP2_ledger HR2) as HLED2. clear HQ2 HA2 HR2.
(* the position transfer after the call: fuzz_malloc's (the cut's ps_rpos_mal) followed by this free's own, HFr of the
   same block (the text's p <> 0 implication); the free uses no hull (its post's hull_used S S2 []) *)
pose proof (Hroom2 ltac:(lia)) as Hroom2'.
assert (Hpos2 : ps_rpos D [PresetReqAt.HMal (Z.of_nat Q + 1 + cf_head); PresetReqAt.HFr (Z.of_nat Q + 1 + cf_head)] S2)
  by exact (ps_rpos_snoc D [PresetReqAt.HMal (Z.of_nat Q + 1 + cf_head)] (PresetReqAt.HFr (Z.of_nat Q + 1 + cf_head))
             S S2 Hpos1 HHU2 (Hfr2 ltac:(lia))).
(* the block list is the entry's again *)
assert (Eab2 : ablocks B ly2 S2 = ablocks B (pi_ly D) (pi_S D)).
{ rewrite Eb2. rewrite Eab in Eb1. exact (pf_app_last _ _ _ _ _ Hnew Eb1). }
(* the ledger's Lam is the entry's again: out was in it once (NoDup) *)
pose proof HLED as HND; apply ps_led_nodup in HND. pose proof HLED as HFa; apply ps_led_blocks in HFa. pose proof HLED as HPm; apply ps_led_heads in HPm.
assert (Hnot : ~ In out (map fst (pi_Lam D))).
{ cbn [map fst] in HND. inversion HND as [|x l HN HND2]; subst. intros Hi. apply HN.
  first [ apply list_elem_of_In; exact Hi | apply elem_of_list_In; exact Hi | exact Hi ]. }
assert (El12 : l1 ++ l2 = pi_Lam D).
{ apply (f_equal (@tl (Z * Z))) in El. destruct l1 as [|x l1]; cbn in El; [symmetry; exact El|].
  exfalso. apply Hnot. rewrite El. apply in_map_iff. exists (out, Z.of_nat Q + 1). split; [reflexivity|].
  apply in_or_app. right. left. reflexivity. }
rewrite El12 in HLED2.
(* the hidden heads are the entry's again *)
assert (Hnhp : ~ In (out - cf_head) (pi_Hp D)).
{ intros Hi. rewrite EHp in HPm. cbn [map fst] in HPm. apply Permutation_cons_inv in HPm.
  apply (Permutation_in _ HPm) in Hi. apply in_map_iff in Hi as ((a & kk) & Ea & Hin). cbn [fst] in Ea.
  apply Hnot. apply in_map_iff. exists (a, kk). split; [cbn [fst]; lia | exact Hin]. }
assert (EHp2' : Hp2 = pi_Hp D).
{ rewrite EHp2, EHp. cbn [remove]. destruct (Z.eq_dec (out - cf_head) (out - cf_head)) as [_|C]; [|exfalso; exact (C eq_refl)].
  apply notin_remove. exact Hnhp. }
(* the registers the callee keeps *)
assert (P2 : getr regs2 2%bv = getr regs 2%bv) by exact (HP2 2 ltac:(unfold acallee_saved; lia)).
assert (P3 : getr regs2 3%bv = getr regs 3%bv) by exact (HP2 3 ltac:(unfold acallee_saved; lia)).
assert (P4 : getr regs2 4%bv = getr regs 4%bv) by exact (HP2 4 ltac:(unfold acallee_saved; lia)).
(* the callee's journal keeps every stack byte at or above its sp (parse_string's frame, q's struct) *)
pose proof (ajxR_ar HJ1) as HAR2. pose proof (ajxR_hi HJ1) as G1.
assert (Hkst : forall a, PS_SP D <= a < 2 ^ 64 -> aview segs (w_H W2) mem2 a = aview segs (w_H W) mem a).
{ intros a Ha. apply G1; lia. }
pose proof (ajxR_pres HJ2) as Jpres2.
(* the kept relation from the entry, through the call, at wle' (the cut's, at wle, lifted; the callee's at wle') *)
assert (HK2 : YCbqGcallW.cj_keptR (SK := SK) segs B prh_pst (wle' segs YGcfRehidePost.RZ_cf) STK_parse_string
  (spZ (pi_regs D)) [(pi_q D, pi_q D + 8)] [] (pi_ly D) (pi_S D) (pi_W D) (pi_mem D) (pi_md D) ly2 S2 W2 mem2 md2).
{ eapply (YCbqGcallW.cj_kept_transR (SK := SK) segs B prh_pst ARx LAWS (wle' segs YGcfRehidePost.RZ_cf)
    (wle'_trans segs YGcfRehidePost.RZ_cf));
    [eapply ps_keptR_mono with (R1 := @wle segs); [exact (wle_wle' segs YGcfRehidePost.RZ_cf) | exact HK]
    | | exact HAR0 | exact HAR | | | |].
  - exact (pf_kept_of_journal_wR (wle' segs YGcfRehidePost.RZ_cf) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      [(pi_q D, pi_q D + 8)] HJ1).
  - lia.
  - lia.
  - intros a Ha. exfalso. exact (inFP_nil a Ha).
  - intros a Ha. right; left. exact (Htmp a (HFP1 a Ha)). }
(* the saved registers *)
assert (HSV2 : ps_saved D W2 mem2).
{ unfold ps_saved in *. destruct HSV as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11 & V12 & V13).
  repeat split; (eapply val_mem_keep; [intros i Hi; apply Hkst; cbn in Hi; lia | eassumption]). }
(* the text, across the call *)
assert (HLen : Z.of_nat (length (pi_tb D)) = pi_len D)
  by (pose proof HIN as (_ & _ & _ & _ & _ & _ & _ & _ & Hl & _); exact Hl).
pose proof HHOME as HHOMEc. rewrite <- HLen in HHOMEc.
assert (SP1 : forall a, inFP (ablocks_fp [(out - cf_head, Z.of_nat Q + 1 + cf_head)]) a ->
  ~ (pi_text D <= a < pi_text D + Z.of_nat (length (pi_tb D)))).
{ intros a Ha Hta. rewrite HLen in Hta. pose proof (HFP1 a Ha) as Hfa.
  destruct (ps_txt_out B ARx LAWS D ly S Hp W mem md out Q a HAR HHOME HALc Hta); lia. }
assert (SP2 : ~ YI16.sink_open_fp (ablocks_fp [(out - cf_head, Z.of_nat Q + 1 + cf_head)])).
{ apply sink_closed_ablocks_fp. apply Forall_cons; [cbn [fst]; lia | apply Forall_nil]. }
assert (SP3 : forall p n, In (p, n) (ablocks B ly S) -> ~ In p Hp -> In (p, n) (ablocks B ly2 S2) /\ ~ In p Hp2).
{ intros p n Hin Hnh. rewrite EHp2'. split.
  - rewrite Eab2. rewrite Eab in Hin. apply in_app_or in Hin as [Hin | [E | []]]; [exact Hin|].
    exfalso. injection E as E1 E2. apply Hnh. rewrite EHp, <- E1. left. reflexivity.
  - intros Hi. apply Hnh. rewrite EHp. right. exact Hi. }
assert (SP4 : forall b m, In (b, m) (pi_Lam D) -> In (b - cf_head, m + cf_head) (ablocks B ly S)).
{ intros b m Hin. pose proof (proj1 (Forall_forall _ _) HFa (b, m) (or_intror Hin)) as (_ & Hab & _). exact Hab. }
assert (SP5 : forall b m, In (b, m) (pi_Lam D) ->
  0 <= m /\ In (b - cf_head, m + cf_head) (ablocks B ly2 S2) /\ In (b - cf_head) Hp2).
{ intros b m Hin. pose proof HLED2 as HF2; apply ps_led_blocks in HF2.
  pose proof (proj1 (Forall_forall _ _) HF2 (b, m) Hin) as (Hm0 & Hab & Hhp & _). exact (conj Hm0 (conj Hab Hhp)). }
assert (SP6 : forall h, In h Hp2 -> exists k, 0 <= k /\ In (h, k) (ablocks B ly2 S2)).
{ intros h Hh. pose proof HLED2 as HF2; apply ps_led_blocks in HF2. pose proof HLED2 as HP2m; apply ps_led_heads in HP2m. apply (Permutation_in _ HP2m) in Hh.
  apply in_map_iff in Hh as ((a & m) & Ea & Hin). cbn [fst] in Ea.
  pose proof (proj1 (Forall_forall _ _) HF2 (a, m) Hin) as (Hm0 & Hab & _). cbn [fst snd] in Hm0, Hab.
  exists (m + cf_head). split; [lia|]. rewrite <- Ea. exact Hab. }
destruct (ps_src_after_call_wR B ARx SK LAWS ZSA IMGV (wle' segs YGcfRehidePost.RZ_cf) _ _ _ ly S Hp W mem md
  ly2 S2 Hp2 W2 mem2 md2 k1 WS1 (pi_Lam D) (pi_text D) (pi_tb D) HJ1 HSRC HHOMEc SP1 SP2 SP3 SP4 SP5 SP6)
  as [HSRC2 HHOME2].
rewrite HLen in HHOME2.
(* the cursor struct and the text at the post state *)
assert (HIN2 : pj_in_okR segs (rdW W2 mem2) (pi_q D) (pi_text D) (pi_len D) (pi_p D) (pi_d D) (pi_tb D)).
{ destruct HIN as (Vp & Ve & Vd & Hrw & Hq8 & Ht0 & Ht62 & Htp & Hlen' & Hg & Hqt & Hd).
  split; [eapply val_mem_keep; [intros i Hi; apply Hkst; cbn in Hi; lia | exact Vp]|].
  split; [eapply val_mem_keep; [intros i Hi; apply Hkst; cbn in Hi; lia | exact Ve]|].
  split; [eapply val_mem_keep; [intros i Hi; apply Hkst; cbn in Hi; lia | exact Vd]|].
  split; [intros x Hx; apply (apresent_writable segs); apply Jpres2; lia|].
  do 5 (split; [assumption|]).
  split; [exact (proj1 HSRC2)|]. split; assumption. }
(* the bytes the stretch charged: the one block given back *)
assert (Eg : PRH_Charge.prhPs_gtrace (ps_x D) = [PjGrammar.EAlloc (Datatypes.S Q); PjGrammar.EFree (Datatypes.S Q)]).
{ unfold PRH_Charge.prhPs_gtrace, PjGrammar.jr_string. cbv beta. rewrite HSC, HDN. reflexivity. }
assert (HBB2 : blocks_bytes S2 <= blocks_bytes (pi_S D) + PRH_Charge.prh_held (PRH_Charge.prhPs_gtrace (ps_x D))).
{ rewrite (blocks_bytes_bsum B ly2 S2), (blocks_bytes_bsum B (pi_ly D) (pi_S D)), Eab2, Eg.
  unfold PRH_Charge.prh_held. cbn [PjGrammar.held PjGrammar.held_ev PjGrammar.calls PjGrammar.is_call]. lia. }
(* THE BUDGET at the NULL return (the text's post is at wbudget CW 0): the free's budget WS1 holds only its own trace
   (wbudget [ct] 0); a fixed trace adds no wild trace, so the journal goes back to budget []; a CW trace is within CW *)
pose proof (YCbqGwild.wfresh_zero_incl _ _ (proj1 (Nat.le_0_r _) HB1)) as Hinc1.
assert (HBW : exists WS, YCbqGwild.wbudget CW 0 WS /\
  ajournal_xwR (SK := SK) segs B prh_pst ARx (wle' segs YGcfRehidePost.RZ_cf) (PS_WSTK D) (PS_WSP D)
    [(pi_q D, pi_q D + 8)] (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_mem D) (pi_md D) [] ly2 S2 Hp2 W2 mem2 md2
    (k + k1) WS).
{ destruct Htrs as [Hfix | (Hcw & _)].
  - exists []. split; [apply ps_wb_nil|].
    refine (ajournal_xw_fix1R (WS := []) (tr := call_trace ly (pc_free_ra0 (as_code B)) regs ch1) Hfix _).
    exact (ajx_budgetR ([] ++ [call_trace ly (pc_free_ra0 (as_code B)) regs ch1]) HJ2
             (wild_incl_mono _ _ _ _ Hinc1 (ajxR_wild HJ2))).
  - exists WS1. split; [|exact HJ2].
    unfold YCbqGwild.wbudget. rewrite (YCbqGwild.wfresh_incl CW WS1); [lia|].
    intros t Ht. destruct (Hinc1 t Ht) as [<- | []]. exact Hcw. }
destruct HBW as (WS & HBW & HJW).
(* ---- the NULL return, with ps_Qres's bad-escape arm ---- *)
apply (HRET0 D ly2 S2 Hp2 W2 regs2 mem2 md2 HPRE).
split; [exists (k + k1), WS; split; [exact HBW|]; split; [exact HJW|]; split; [exact HK2|]; split; [exact HSV2|];
  split; [exact HSRC2|]; split; [exact HHOME2 | exact HPM2]|].
split; [unfold ps_gptp; rewrite P3, P4; exact HGT|].
split; [rewrite P2; exact R2|].
split; [exact Hroom2'|].
split; [exact HBB2|].
unfold ps_Qres. rewrite HSC. right; right; left.
split; [exact Hcnt|]. split; [reflexivity|]. split; [exact HDN|]. split; [exact EHp2'|]. split; [exact Eab2|].
split; [exact HLED2|]. split; [exact HIN2|].
(* the exact advance: the malloc's event and the free's *)
exact Hpos2.
Qed.

(* ---- THE STRETCH: from the cut at PS_FREECUT, ps_seg_free's statement with the live count of fuzz_free's text at the
   cut's state (= the call's: 1276 touches neither the allocator state nor the memory). The run to the call is at wle,
   into S4_PsBase's hand-off form ps_finP; the call crosses the free (ps_finP_hand) ---- *)
Theorem ps_seg_free_cntP : forall D ly S Hp W regs mem md out Q,
  ps_pre B ARx CTX CW D -> ps_at_freeP B ARx SK P D ly S Hp W regs mem md out Q ->
  YGcfRoomLive.ccnt24 S <= PresetLiveBounds.L24 + PresetLiveBounds.DRV ->
  SRr' segs YGcfRehidePost.RZ_cf W (cfg_at segs (ps_pc PS_FREECUT) regs mem md)
    (ps_postPR B ARx SK P (wle' segs YGcfRehidePost.RZ_cf) CW D).
Proof.
intros D ly S Hp W regs mem md out Q HPRE HAT HC24.
apply ps_finP_SRr'.
destruct HAT as ((k & HC) & HAL & HGT & HIN & HROD & HSC & HDN & R2 & R18 & R8).
pose proof HC as (HJ & HK & HSV & HSRC & HHOME & HPM).
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs []))) by apply Eimg_env.
assert (HS : st_ok_pi segs VAL (Eimg (Ereg regs [])) (mkSS (PS_OFF + PS_FREECUT) sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + (PS_OFF + PS_FREECUT))) mem (seg_rom segs)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - reflexivity.
  - apply Forall_nil.
  - exact I.
  - split; [exact I | split; exact I]. }
assert (SHOK : sh_ok segs (SOff 24 0) [] (Eimg (Ereg regs [])) (mrestrict (w_H W) mem)) by (unfold sh_ok; apply Forall_nil).
(* the runner twin at the stretch's invariant P *)
pose (RUN := @paj_run_x_inv fx rc SK _ PSB.PS_PAListing PSB.PS_PAImg B prh_pst ARx _ LAWS P PLAW).
unfold cfg_at, ps_pc, w64. replace (BASE + PS_OFF + PS_FREECUT) with (BASE + (PS_OFF + PS_FREECUT)) by lia.
(* slots 1276-1280: a0 = s2, jal fuzz_free; no store *)
paj_run_tok_x_inv RUN HS HJ SHOK HPM PF_Bspan; [apply awr_ok_nil|].
pmkst HS.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msn) =>
  assert (Emem : ms_mem msn = mem)
    by (apply functional_extensionality; intros x; apply HF; intros (r & Hin & _); cbn [ss_mem In] in Hin; destruct Hin)
end.
rewrite Emem in HJ, HPM |- *.
lazymatch type of HS with st_ok _ ?E ?ss (restrict ?H ?msn) =>
  assert (Kr : forall (r : bv 5) n, sr_get (ss_regs ss) r = SOff n 0 -> Z.of_nat n = bv_unsigned r ->
    getr (ms_regs msn) r = getr regs r)
    by (intros r n Hr Hn; rewrite (st_ok_restrict_reg segs H E ss msn r HS), Hr; apply pf_reg_atom; exact Hn);
  assert (K10 : getr (ms_regs msn) 10%bv = getr regs 18%bv)
    by (rewrite (st_ok_restrict_reg segs H E ss msn 10%bv HS); pf_sr; apply pf_reg_atom; reflexivity);
  assert (K1 : getr (ms_regs msn) 1%bv = w64 (ps_pc PS_RET0))
    by (rewrite (st_ok_restrict_reg segs H E ss msn 1%bv HS); pf_sr; rewrite (codeptr_val _ _ HEI);
        unfold w64; f_equal; vm_compute; reflexivity);
  assert (K2 : getr (ms_regs msn) 2%bv = getr regs 2%bv) by (apply (Kr _ 2%nat); [vm_compute; reflexivity | reflexivity]);
  assert (K3 : getr (ms_regs msn) 3%bv = getr regs 3%bv) by (apply (Kr _ 3%nat); [vm_compute; reflexivity | reflexivity]);
  assert (K4 : getr (ms_regs msn) 4%bv = getr regs 4%bv) by (apply (Kr _ 4%nat); [vm_compute; reflexivity | reflexivity]);
  assert (K8 : getr (ms_regs msn) 8%bv = getr regs 8%bv) by (apply (Kr _ 8%nat); [vm_compute; reflexivity | reflexivity])
end.
(* the call, at fuzz_free's entry *)
apply ps_finP_hand. apply (ps_free_callP D ly S Hp W _ mem _ out Q k HPRE).
- split; [exact HJ|]. split; [|exact (conj HSV (conj HSRC (conj HHOME HPM)))].
  apply (pf_kept_md _ _ _ _ _ _ _ _ _ _ _ _ _ md); [exact HK|].
  first [ apply same_but_materialized_wvb_any | apply with_vm_backing_same
        | eapply same_but_materialized_trans; apply same_but_materialized_wvb_any ].
- exact HAL.
- unfold ps_gptp. rewrite K3, K4. exact HGT.
- exact HIN.
- exact HROD.
- exact HSC.
- exact HDN.
- rewrite K2. exact R2.
- exact K1.
- rewrite K10. exact R18.
- rewrite K8. exact R8.
- exact HC24.
Qed.
End pf.

(* ---- the stable statement as the P := (fun _ => True) instance: 7e5a49a2288's ps_seg_free_cnt, at CW, with the count
   argument (the free text gives the memnorm keep and the position transfer) ---- *)
Section pfT. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
#[local] Existing Instances PSB.PS_PrhImg PSB.PS_PAListing PSB.PS_PAImg.
#[local] Notation segs := (@pa_segs _ A_prog_listing PSB.PS_PAImg).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Variable CTX : list (list Z).
Variable CW : list (list Z).
Hypothesis LAWS : AR_laws_x segs B ARx cf_head.
Hypothesis HFREE : tfuzz_free_specX B ARx SK.
Hypothesis ZSA : forall q m, In (q, m) (as_zero_shadow B) -> q mod 8 = 0 /\ m mod 8 = 0.
Hypothesis IMGV : ARx_img_shadow_vis segs ARx.
Hypothesis HRET0 : ps_seg_ret0R B ARx SK (wle' segs YGcfRehidePost.RZ_cf) CTX CW.
Theorem ps_seg_free_cnt : forall D ly S Hp W regs mem md out Q,
  ps_pre B ARx CTX CW D -> ps_at_free B ARx SK D ly S Hp W regs mem md out Q ->
  YGcfRoomLive.ccnt24 S <= PresetLiveBounds.L24 + PresetLiveBounds.DRV ->
  SRr' segs YGcfRehidePost.RZ_cf W (cfg_at segs (ps_pc PS_FREECUT) regs mem md)
    (ps_postR B ARx SK (wle' segs YGcfRehidePost.RZ_cf) CW D).
Proof.
intros D ly S Hp W regs mem md out Q HPRE (Hc & HAT) HC24.
unfold SRr'. eapply (SRrG_mono segs (wle' segs YGcfRehidePost.RZ_cf)).
{ apply (ps_seg_free_cntP B ARx SK CTX CW LAWS HFREE ZSA IMGV (fun _ => True) srr_inv_laws_True srr_inv_call_True
    (proj2 (ps_seg_ret0R_of_True B ARx SK (wle' segs YGcfRehidePost.RZ_cf) CTX CW) HRET0) D ly S Hp W regs mem md out Q HPRE).
  - split; [apply ps_ex_carryP_T; exact Hc | exact HAT].
  - exact HC24. }
intros W' c' _ HQ. apply ps_postPR_T. exact HQ.
Qed.
End pfT.
