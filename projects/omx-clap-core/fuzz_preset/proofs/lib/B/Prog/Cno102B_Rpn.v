(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S8aNumA.v, with its module paths and module names changed; 1138 of its 1209 lines of code are new or changed and 707 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/Crt102TailB.v, with its module paths and module names changed; 1122 of its 1216 lines of code are new or changed and 1115 lines of the source are left out. *)
(* rule 24: no function proved
   rule 24: proves no function (kind: segment lemma)
   fuzz_preset, image B' (#102 pins: asan-ubsan sha256 d663f82d7f488d30): the three parse_noting CALL STEPS of the
   re-walk of check_no_overread (cno, B' entry 0x819f0) against the kit's text tcheck_no_overread_specX, sub-lane CutPn of
   lane CnoB102rR (a Theorem Labs lane, plan, the internal file PLAN-cno-caw-102.md 5.2): cnb_pn1_step (CNB_PN1 632, 0x81c68 -> CNB_READ2),
   cnb_pn2_step (CNB_PN2 676, 0x81c94 -> CNB_READ3), cnb_pn3_step (CNB_PN3 720, 0x81cc0 -> 724 `mv s7, a0` -> CNB_CMP),
   each an instance of the one generic step cnb_pn_call (the `jal parse_noting` at a cut, then the call).
   RE-FIT TO THE KIT CUT a working branch 7cdbb61b5fa0 (this row's base 
   75415fdb6e76) from the f97c texts (sub-lane CnoBPn's proof, the port of image A''s lib/A/Prog/Cno102A_Rpn.v).
   INPUTS: the contract lib/B/Prog/Cno102B_Base.v (cnb_pre CTX0 D with the wild_room conjunct; cnb_J D wk, the budgeted
   journal at the spent wild budget; cnb_base .. k wk; cnb_at_pn1 / pn2 / pn3 at wk 0 / 2 / 4 -> cnb_ex_read2 / read3 /
   cmp at wk 2 / 4 / 6; cnb_fo, the trees' free order against pj_frees), in its forms for the move below: cnb_JR /
   cnb_baseR over a world relation R and cnb_baseR_mono; each cut and exit as its R form (cnb_at_pn2R / pn3R,
   cnb_ex_read2R / read3R / cmpR), here at wle' SEGS RZ_cf; the step kit lib/B/Prog/Cno102B_Ro.v (the R forms of its
   world lemmas: cnb_hs_callR, cnb_hs_addiR, cnb_base_matR, cnb_chainR, cnb_roomR, cnb_J_wildR; and cnb_entry_facts,
   cnb_fo_keep, cnb_regsat_get, cnb_regsat_kept, cnb_open_keep, cnb_slots_agree, cnb_rcslot_agree, cnb_stk_val,
   cnb_prog_app, cnb_prog_eq, ro_rdword_kept, ro_hull_mono); the kit's text tparse_noting_specX (lib/A/PRH_FnCheck.v,
   restated for the move: no DW; RQ_pj_parse tb <= most; the room YCbqGwild.wild_room (as_universe B) []
   (prh_wk F_parse_noting) (st_depot S); the LAST premise PresetHullBudget.hull_budget S (parse_evs jr_strtod tb []);
   the conclusion SRr' segs RZ_cf; the budgeted post fpostFbm (wbudget [] (prh_wk F_parse_noting)) at wle' segs RZ_cf,
   its inner post FIRST PresetHullBudget.hull_used S S' (parse_evs jr_strtod tb []); prh_oks over prh_ev_reqs tr; the
   refusal peak; the outcome clause (not read here); on the Some arm rd_blocks, THE FREE ORDER (pj_foR against pj_frees
   ok tb under cf_head = HEAD) and pj_ncapR) as Section hypothesis HPN, for any float state, its inner post read through
   the kit's named projections (tpnP_Q, tpnP_R_of, tpnP_RSome_of / tpnP_RNone_of, tpnP_granted_read); lib/A/PRH_Base.v (fpre,
   fpostFbm / fpostFb restated in place at wle' segs RZ_cf, prh_ledger, prh_oks, prh_refused, prh_ev_reqs, prh_wk),
   lib/A/PRH_PjOrder.v e5917626b82b (pj_foR_frame), lib/A/PRH_Reader.v 4266e709561a (pj_nodeR_frame, pj_zeroR_frame,
   garr8R_frame), lib/A/PRH_Charge.v 2b0b34262818 / lib/A/PRH_FnPj.v 5aca5cbe2cfb (prh_maxreq, RQ_pj_parse); the run
   model lib/Spec/PjGrammar.v 5d4026de2876 (agrees, agrees_fuel, G7_1 / G7_2, jr_run_eq), PresetReqAt.v 43c958024221
   (parse_evs, pj_frees, jfv / jfl), PresetRun.v 5ac818ab1fe6 (okof, okk_true / okk_false, ranout, pkR_app, pkR_mono),
   PjReqBound.v 8c22fd172b82 (ev_req); listing lib/B/Listing_prog.v c97cc46b3e13 (slots 201 + off / 4: PCall
   AS_parse_noting 1 at 632 / 676 / 720, PW 0x50b93 `mv s7, a0` at 724); engine lib/Reusable/YCbqG.v (ajournal_xwR
   read through the ajxR_* projections, ajournal_xw_subR), YCbqGwild.v (apost_base_xbFR, afn_pre_x_at_wR,
   wbudget_app), YA0nH.v (SRr', wle', wle'_trans, wle_wle') and YSRrG.v (SRr'_bind / SRr'_mono / SRr'_ret); the hull
   kit lib/Spec/PresetHullBudget.v (hull_budget, hull_used, hull_used_refl, hull_budget_infix, hull_budget_app);
   lib/A/Prog/PRW_StepKit.v 0df3991c13f4 (pa_slot_lt_ceil_b).
   THE MOVE (a free or a realloc can hide shadow memory again): tparse_noting_specX's run crosses frees (pj_parse frees
   on a refusal), so it concludes SRr' SEGS RZ_cf and its post's journal is at wle' SEGS RZ_cf (WLE' below). So every
   statement here concludes SRr' SEGS RZ_cf, and cnb_pn_call / cnbp_pn_entry take and give the cut's base at wle'
   (cnb_baseR at WLE'). pn2 and pn3 start at cuts after a free (cnb_at_pn2R / pn3R at WLE'); pn1 starts at a cut before
   any free (cnb_at_pn1, at wle), whose base is lifted first (the Base's cnb_baseR_mono at wle_wle'). The exits
   cnb_ex_read2R / read3R / cmpR lie after the call, at WLE'. No world conjunct of a journal (ajxR_rel) is read here.
   THE HULL: the text takes PresetHullBudget.hull_budget S (parse_evs jr_strtod tb []) (its all-granted events) and
   states hull_used S S' (parse_evs jr_strtod tb []) first in its inner post. The cut at a call carries hull_budget S
   (cnb_hrest_<stage> x) LAST (copies at pn1, rd1 at pn2, rd2 at pn3); the Base's split lemma gives cnb_hrest_<stage> x
   = parse_evs jr_strtod x [] ++ cnb_hrest_<next> x; cnb_pn_call takes that budget, pays the text from its head
   (hull_budget_infix at the empty used prefix) and gives the next cut the rest (hull_budget_app with the post's
   hull_used): rd1 at read2, rd2 at read3, rd0 at the compare. pn3's return-site step `mv s7, a0` keeps S.
   THE CALL (cnbp_call_x): the callee's budgeted journal (budget WS1, wbudget [] 2 WS1) composes with the function's
   (ajournal_xw_subR at wle'; footprint the one struct [d, d + 56) in the function's own fake frame), and the next
   cut's journal is cnb_JR at wle' D (wk + 2) at WS0 ++ WS1 (the kit's cnb_J_wildR); fpre from the journal
   (afn_pre_x_at_wR; STK_check_no_overread = 27392 covers sp = s1 >= entry sp - 176 and STK_parse_noting = 27216,
   margin 176) and cnb_baseR's frm_zero; the room from the kit's cnb_roomR at wk = 0 / 2 / 4 (wk + 2 <= 6); the chain
   through the entry's saved s0 / ra; fpre's raZ bound from one closed lemma per return slot (cnb_pn_site1 / 2 / 3);
   the text's two room counts from cnb_pre's counts along ck_cno_evs .. None None None (cnbp_pkR_mid over
   cnbp_cno_split); RQ_pj_parse tb <= most from cnb_pre.
   THE GRANT (section 1b, no premise): the post's outcomes ok are, for the reading, its trace, its events, its pj_free
   list and its ran-out, the model's grant okof og of one og (cnbp_grant; the pure grammar lemma (d),
   cnbp_parse_evs_pre / cnbp_pj_frees_pre, proved from PjGrammar.agrees: a refusal ends the reading), and g_ran_out = 1
   exactly when og runs out (prh_oks with fail = SIZE_MAX; every request of the reading is at most RQ_pj_parse tb,
   cnbp_ev_reqs_le, so at most g_most). THE NEXT CUT from the text's post: cnb_mid at nr + 1 (the copies by the block
   clause and AR_laws_x's alx_shadow, the structs by the frame clause, the input's bytes by the block and image
   clauses), cnb_res from the jr_run equation, cnb_rd from jr_run at okof og, cnb_fo of the new tree from the text's
   free order (pj_frees ok = pj_frees (okof og)), cnb_fo of the earlier trees by pj_foR_frame (they sit in the other
   structs and in Lam blocks the call keeps), cnb_prog extended by the reading's events under og (cnb_prog_app over
   the text's exact live set and position), g_most / g_own_ran_out by the text's post ledger (the same most / own),
   the slots of [s1, entry sp) by the stack clause.
   Numerals: 632 .. 728 (DERIVED: byte offsets inside cno, the cuts of Cno102B_Base.v and the listing's slots);
   160 / 176 / 192 / 32 / 16 / 8 / 56 / 64 / 512 / 128 / 224 / 280 / 152 / 144 (LENGTH: frame, alignment, slot and
   struct sizes, the class-3 frame and its shadow); 27216 / 27392 (LENGTH: the two texts' stack windows); 0 / 2 / 4 / 6
   (COUNT: the spent wild budget); register numbers (WORD); 2 ^ 28 / 2 ^ 30 / 2 ^ 40 / 2 ^ 62 / 2 ^ 64 (LENGTH:
   offset, run, size and word bounds). No ADDRESS. *)
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
(* YK06 is NOT imported: its plain alloc_ceiling would shadow the RunCeil field YM05.alloc_ceiling (Cno102B_Base.v) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjRoundTrip PresetRoomPos PjReqBound.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetHullBudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnAlloc
  PRH_FnReader PRH_FnPj PRH_FnEx PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_PjOrder PRH_Charge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_StepKit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import Cno102B_Base Cno102B_Ro.
(* the PLAIN build's sink instance is loaded transitively; it must never fill an ASan sink argument *)
#[global] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* ==== 1. pure helpers (Cno102A_Rpn.v section 1, B' names) ==== *)
Lemma cnbp_regsat_incl : forall regs l l', cnb_regsat regs l -> incl l' l -> cnb_regsat regs l'.
Proof.
intros regs l l' H Hi. unfold cnb_regsat in *. apply Forall_forall. intros p Hp.
exact (proj1 (Forall_forall _ _) H p (Hi p Hp)).
Qed.
Lemma cnbp_Forall_and : forall {A : Type} (P Q R : A -> Prop) l, Forall P l -> Forall Q l -> (forall x, P x -> Q x -> R x) ->
  Forall R l.
Proof.
intros A P Q R l HP HQ H. rewrite Forall_forall in *. intros x Hx. exact (H x (HP x Hx) (HQ x Hx)).
Qed.
Lemma cnbp_mod32_at : forall F x j, F mod 32 = 0 -> x = F + 32 * j -> x mod 32 = 0.
Proof. intros F x j H ->. replace (F + 32 * j) with (F + j * 32) by lia. rewrite Z.mod_add by lia. exact H. Qed.
Lemma cnbp_mod8 : forall x, x mod 32 = 0 -> x mod 8 = 0.
Proof.
intros x H. apply Z.mod_divide in H; [|lia]. apply Z.mod_divide; [lia|]. destruct H as [q ->]. exists (4 * q). lia.
Qed.
(* the realigned sp: 32-aligned, in [entry sp - 176, entry sp - 160] (the entry sp is 16-aligned) *)
Section s1. Context {rc : YM05.RunCeil} {PA : PAImg B_prog_listing}.
Lemma cnbp_S1 : forall D : @cnb_in rc PA, cnb_sp0 D mod 16 = 0 ->
  cnb_sp0 D - 176 <= cnb_S1 D <= cnb_sp0 D - 160 /\ cnb_S1 D mod 32 = 0 /\ (cnb_S1 D - cnb_sp0 D) mod 16 = 0.
Proof.
intros D H16. destruct (cnb_S1_bounds D H16) as (H1 & H2 & H3).
apply Z.mod_divide in H3; [|lia]. apply Z.mod_divide in H16; [|lia].
destruct H3 as [a Ea]. destruct H16 as [b Eb].
split; [lia|]. split; [rewrite Ea; apply Z.mod_mul; lia|].
replace (cnb_S1 D - cnb_sp0 D) with ((2 * a - b) * 16) by lia. apply Z.mod_mul. lia.
Qed.
End s1.

(* the reading's counts (PjGrammar G7_1 / G7_2 / ok_upto_dec, as H5RttS3.v s3_read_some) *)
Lemma cnbp_read_some : forall x ok t tr,
  PjGrammar.jr_run ReaderRes.jr_strtod x ok = (Some t, tr) ->
  PjGrammar.json_read ReaderRes.jr_strtod x = Some t /\ tr = snd (PjGrammar.jr_run ReaderRes.jr_strtod x []).
Proof.
intros x ok t tr H.
destruct (PjGrammar.ok_upto_dec ok (PjGrammar.ncalls ReaderRes.jr_strtod x)) as [Hu | (j & Hj & Hf & Hb)].
- rewrite (PjGrammar.G7_1 _ x ok Hu) in H. injection H as E1 E2. split; [exact E1 | symmetry; exact E2].
- exfalso. destruct (PjGrammar.G7_2 _ x ok j Hj Hf Hb) as [H1 _]. rewrite H in H1. discriminate H1.
Qed.
Lemma cnbp_calls_le : forall x ok res tr,
  PjGrammar.jr_run ReaderRes.jr_strtod x ok = (res, tr) ->
  (PjGrammar.calls tr <= PjGrammar.ncalls ReaderRes.jr_strtod x)%nat.
Proof.
intros x ok res tr H.
destruct (PjGrammar.ok_upto_dec ok (PjGrammar.ncalls ReaderRes.jr_strtod x)) as [Hu | (j & Hj & Hf & Hb)].
- rewrite (PjGrammar.G7_1 _ x ok Hu) in H. injection H as _ E2. subst tr. unfold PjGrammar.ncalls. lia.
- destruct (PjGrammar.G7_2 _ x ok j Hj Hf Hb) as [_ H2]. rewrite H in H2. cbn [snd] in H2. lia.
Qed.
Lemma cnbp_held_le_hpeak : forall tr, PjGrammar.held tr <= hpeakR tr.
Proof. induction tr as [|e r IH]; cbn [PjGrammar.held hpeakR]; lia. Qed.
Lemma cnbp_hpeak_nonneg : forall tr, 0 <= hpeakR tr.
Proof. destruct tr as [|e r]; cbn [hpeakR]; lia. Qed.
Lemma cnbp_nlive_le_calls : forall tr, ReaderRes.nlive tr <= Z.of_nat (PjGrammar.calls tr).
Proof.
induction tr as [|e r IH]; cbn [ReaderRes.nlive PjGrammar.calls]; [lia|].
destruct e as [n|[|m] n|n|n]; cbn [ReaderRes.nlive_ev PjGrammar.is_call]; lia.
Qed.
Lemma cnbp_bsum_hblks {cp : CfParams} : forall D, bsum (ck_hblks D) = Ledger.lsum D + cf_head * Z.of_nat (length D).
Proof.
induction D as [|[a kk] D IH]; [cbn; lia|].
unfold ck_hblks in *. cbn [map length Ledger.lsum fst snd]. rewrite bsum_cons. cbn [snd]. rewrite IH. lia.
Qed.

(* the tree representation is monotone in its block predicate *)
Lemma cnbp_cstrR_lblk : forall segs m lblk lblk' a k s, pj_cstrR segs m lblk a k s ->
  (forall a k, lblk a k -> lblk' a k) -> pj_cstrR segs m lblk' a k s.
Proof. intros segs m lblk lblk' a k s (Hl & Hr) H. split; [exact (H _ _ Hl) | exact Hr]. Qed.
Lemma cnbp_memsR_lblk : forall segs m lblk lblk' (P P' : Z -> PjTree.jv -> list (Z * Z) -> Prop) l a ka D,
  pj_memsR segs m lblk P a ka l D -> (forall a k, lblk a k -> lblk' a k) ->
  (forall i nm u D1, nth_error l i = Some (nm, u) -> P (a + 56 * Z.of_nat i) u D1 -> P' (a + 56 * Z.of_nat i) u D1) ->
  pj_memsR segs m lblk' P' a ka l D.
Proof.
intros segs m lblk lblk' P P' l. induction l as [|[nm u] r IH]; intros a ka D H Hl HP; cbn [pj_memsR] in H |- *;
  [exact H|].
destruct H as (x & k & D1 & D2 & -> & Hx & Hc & H1 & H2). exists x, k, D1, D2. split; [reflexivity|].
split; [exact Hx|]. split; [exact (cnbp_cstrR_lblk _ _ _ _ _ _ _ Hc Hl)|].
split.
- specialize (HP 0%nat nm u D1 eq_refl). replace (a + 56 * Z.of_nat 0) with a in HP by lia. exact (HP H1).
- apply (IH (a + 56) (ka + 8) D2 H2 Hl). intros i nm' u' D1' Hi HPi.
  specialize (HP (S i) nm' u' D1' Hi). replace (a + 56 * Z.of_nat (S i)) with (a + 56 + 56 * Z.of_nat i) in HP by lia.
  exact (HP HPi).
Qed.
Lemma cnbp_nodeR_lblk : forall segs t m lblk lblk' p D, pj_nodeR segs m lblk p t D ->
  (forall a k, lblk a k -> lblk' a k) -> pj_nodeR segs m lblk' p t D.
Proof.
intros segs t. induction t as [| | | txt bits | s | items IH | members IH] using PjTree.jv_ind';
  intros m lblk lblk' p D H Hl; cbn [pj_nodeR] in H |- *;
  destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & Hb);
  (split; [exact Hn|]); (split; [exact Ha|]); exists num, str, kids, keys, n, cap; (split; [exact Hh|]).
- exact Hb.
- exact Hb.
- exact Hb.
- destruct Hb as (E1 & E2 & E3 & E4 & E5 & k & Hc & ED).
  split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
  exists k. split; [exact (cnbp_cstrR_lblk _ _ _ _ _ _ _ Hc Hl) | exact ED].
- destruct Hb as (E2 & E3 & E4 & E5 & k & Hc & ED).
  split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
  exists k. split; [exact (cnbp_cstrR_lblk _ _ _ _ _ _ _ Hc Hl) | exact ED].
- destruct Hb as (Es & Ek & En & Hc & Hcap & Di & ED & Hi).
  split; [exact Es|]. split; [exact Ek|]. split; [exact En|]. split; [exact Hc|].
  split; [destruct Hcap as [Hcap|(Hc0 & Hk)]; [left; exact Hcap | right; split; [exact Hc0 | exact (Hl _ _ Hk)]]|].
  exists Di. split; [exact ED|].
  apply (pj_itemsR_mono (pj_nodeR segs m lblk) (pj_nodeR segs m lblk') items kids Di Hi).
  intros i u D1 Hil _ HP. rewrite Forall_forall in IH. exact (IH u (nth_error_In items i Hil) m lblk lblk' _ D1 HP Hl).
- destruct Hb as (Es & En & Hc & Hcap & Di & ED & Hi).
  split; [exact Es|]. split; [exact En|]. split; [exact Hc|].
  split; [destruct Hcap as [Hcap|(Hc0 & Hk & Hy)];
    [left; exact Hcap | right; split; [exact Hc0 | split; [exact (Hl _ _ Hk) | exact (Hl _ _ Hy)]]]|].
  exists Di. split; [exact ED|].
  apply (cnbp_memsR_lblk segs m lblk lblk' (pj_nodeR segs m lblk) (pj_nodeR segs m lblk') members kids keys Di Hi Hl).
  intros i nm u D1 Hil HP. rewrite Forall_forall in IH. specialize (IH (nm, u) (nth_error_In members i Hil)).
  cbn [snd] in IH. exact (IH m lblk lblk' _ D1 HP Hl).
Qed.

(* a runtime block's shadow (ARx's block-shadow law) gives a copy's src_rd shadow conjuncts *)
Lemma cnbp_bshadow_ra : forall (rd : reader) p len, 0 <= len ->
  block_shadow rd SHADOW_OFF p (req_size (len + 16)) -> range_addressable rd SHADOW_OFF p len.
Proof.
intros rd p len Hlen (Hp8 & Hn & Hb) x Hx.
assert (Hrq : req_size (len + 16) = len + 16) by (unfold req_size; destruct (Z.eqb_spec (len + 16) 0); lia).
rewrite Hrq in Hb.
assert (Hq : x / 8 = p / 8 + (x - p) / 8).
{ pose proof (Z.div_mod p 8 ltac:(lia)) as Ep. rewrite Hp8, Z.add_0_r in Ep.
  replace x with ((x - p) + p / 8 * 8) at 1 by lia. rewrite Z.div_add by lia. lia. }
assert (Hi0 : 0 <= (x - p) / 8) by (apply Z.div_pos; lia).
assert (Hi1 : (x - p) / 8 < (len + 16) / 8).
{ apply (Z.le_lt_trans _ ((len - 1) / 8)); [apply Z.div_le_mono; lia|].
  apply Z.div_lt_upper_bound; [lia|]. pose proof (Z.mul_div_le (len + 16) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (len + 16) 8 ltac:(lia)).
  pose proof (Z.div_mod (len + 16) 8 ltac:(lia)). pose proof (Z.div_mod (len - 1) 8 ltac:(lia)). lia. }
assert (Hi2 : (x - p) / 8 < (len + 16 + 7) / 8) by (pose proof (Z.div_le_mono (len + 16) (len + 16 + 7) 8 ltac:(lia) ltac:(lia)); lia).
specialize (Hb ((x - p) / 8) (conj Hi0 Hi2)).
rewrite (proj2 (Z.ltb_lt _ _) Hi1) in Hb.
exists 0. split; [|left; reflexivity].
unfold shadow_of_addr in *. rewrite Hq, Z.add_assoc. exact Hb.
Qed.

(* the ledger list and the block list after a reading whose blocks Ds go to one of the three structs *)
Lemma cnbp_perm_lam : forall {A : Type} (L2 L Ds D1 D2 D3 a b c L0 : list A),
  Permutation L2 (Ds ++ L) -> Permutation L (D1 ++ D2 ++ D3 ++ L0) ->
  Permutation (a ++ b ++ c) (Ds ++ D1 ++ D2 ++ D3) -> Permutation L2 (a ++ b ++ c ++ L0).
Proof.
intros A L2 L Ds D1 D2 D3 a b c L0 H1 H2 H3. rewrite H1, H2. rewrite !app_assoc. rewrite !app_assoc in H3.
rewrite H3. reflexivity.
Qed.
Lemma cnbp_perm_blocks {cp : CfParams} : forall (AB2 AB C Ds D1 D2 D3 a b c A0 : list (Z * Z)),
  Permutation AB2 (AB ++ ck_hblks Ds) -> Permutation AB (C ++ ck_hblks (D1 ++ D2 ++ D3) ++ A0) ->
  Permutation (a ++ b ++ c) (Ds ++ D1 ++ D2 ++ D3) -> Permutation AB2 (C ++ ck_hblks (a ++ b ++ c) ++ A0).
Proof.
intros AB2 AB C Ds D1 D2 D3 a b c A0 H1 H2 H3. rewrite H1, H2. unfold ck_hblks.
rewrite (Permutation_map (fun ak : Z * Z => (fst ak - cf_head, snd ak + cf_head)) H3).
rewrite (map_app _ Ds (D1 ++ D2 ++ D3)).
set (X := map (fun ak : Z * Z => (fst ak - cf_head, snd ak + cf_head)) (D1 ++ D2 ++ D3)).
set (Y := map (fun ak : Z * Z => (fst ak - cf_head, snd ak + cf_head)) Ds).
rewrite <- !app_assoc. apply Permutation_app_head.
transitivity ((X ++ A0) ++ Y); [rewrite <- app_assoc; reflexivity|]. apply Permutation_app_comm.
Qed.

(* the callee-saved registers, by a boolean test *)
Definition cnbp_csb (z : Z) : bool :=
  (z =? 2) || (z =? 3) || (z =? 4) || (z =? 8) || (z =? 9) || ((18 <=? z) && (z <=? 27)).
Lemma cnbp_csb_ok : forall z, cnbp_csb z = true -> acallee_saved z.
Proof.
intros z. unfold cnbp_csb, acallee_saved.
destruct (Z.eqb_spec z 2); [intros _; lia|].
destruct (Z.eqb_spec z 3); [intros _; lia|].
destruct (Z.eqb_spec z 4); [intros _; lia|].
destruct (Z.eqb_spec z 8); [intros _; lia|].
destruct (Z.eqb_spec z 9); [intros _; lia|].
destruct (Z.leb_spec 18 z); destruct (Z.leb_spec z 27); cbn [orb andb]; intros Hb; try discriminate Hb; lia.
Qed.
(* across the jal (ra := ret) and the call (aregs_preserved): a snapshot of callee-saved registers is kept *)
Lemma cnbp_regsat_call : forall regs regs' l (v1 : word),
  cnb_regsat regs l -> aregs_preserved (regupd regs 1%bv v1) regs' ->
  forallb (fun r : bv 5 => cnbp_csb (bv_unsigned r)) (map fst l) = true ->
  cnb_regsat regs' l.
Proof.
intros regs regs' l v1 H HP Hc. unfold cnb_regsat in *. rewrite Forall_forall in *.
intros [r v] Hin. cbn [fst snd]. pose proof (H _ Hin) as E. cbn [fst snd] in E.
assert (Hcs : acallee_saved (bv_unsigned r)).
{ apply cnbp_csb_ok. rewrite forallb_forall in Hc. apply Hc. apply in_map_iff. exists (r, v). split; [reflexivity | exact Hin]. }
pose proof (HP _ Hcs) as E2. rewrite Z_to_bv_bv_unsigned in E2. rewrite E2.
rewrite getr_other; [exact E|].
intros Er. subst r. change (bv_unsigned (1%bv : bv 5)) with 1 in Hcs. unfold acallee_saved in Hcs. lia.
Qed.
(* a snapshot list inside another (both written out): membership by search *)
Ltac cnbp_incl := let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; unfold cnb_core, cnb_s8 in Hx |- *; cbn [In app] in Hx |- *;
  repeat (destruct Hx as [<-|Hx]; [repeat (first [left; reflexivity | right])|]); destruct Hx.
(* a register written outside a snapshot keeps the snapshot *)
Lemma cnbp_regsat_upd : forall regs l (r : bv 5) w, ~ In r (map fst l) -> cnb_regsat regs l ->
  cnb_regsat (regupd regs r w) l.
Proof.
intros regs l r w Hn H. unfold cnb_regsat in *. rewrite Forall_forall in *.
intros [r' v] Hin. cbn [fst snd]. rewrite getr_other.
- exact (H _ Hin).
- intros E. apply Hn. apply in_map_iff. exists (r', v). split; [exact E | exact Hin].
Qed.
Lemma cnbp_v_addi0 : forall x : word, v_addi x 0 = x.
Proof.
intros x. unfold v_addi. rewrite Z.add_0_r. apply bv_eq. rewrite Z_to_bv_unsigned.
apply bv_wrap_small, bv_unsigned_in_range.
Qed.

(* ==== 1b. THE READER'S GRANT LISTS (the kit's owed pure grammar lemma (d), PRH_FnPj.v 5aca5cbe2cfb's
   prhPj_parse_evs_starved comment :482-490; proved here): two grant lists that agree on the first calls tr outcomes of a
   reading give the same reading, the same trace and the same pj_free list, so the same parse_evs; hence every
   outcome list ok of a reading is, for its events and its ran-out, the model's grant okof o of ONE o (None when ok
   grants every allocation the reading makes, Some j at its first refusal j). A refusal ends a reading
   (PjGrammar.agrees: jbind stops at the first None), which is why no premise is needed. ==== *)
(* the split of a trace at its (j+1)-th call is unique *)
Lemma cnbp_split_uniq : forall (P P' : list PjGrammar.ev) E E' r r',
  P ++ E :: r = P' ++ E' :: r' -> PjGrammar.calls P = PjGrammar.calls P' ->
  PjGrammar.is_call E = true -> PjGrammar.is_call E' = true -> P = P' /\ E = E'.
Proof.
induction P as [|a P IH]; intros P' E E' r r' Heq Hc HE HE'.
- destruct P' as [|a' P']; cbn [app] in Heq.
  + injection Heq as E1 _. subst E'. split; reflexivity.
  + injection Heq as E1 _. subst a'. cbn [PjGrammar.calls] in Hc. rewrite HE in Hc. discriminate Hc.
- destruct P' as [|a' P']; cbn [app] in Heq.
  + injection Heq as E1 _. subst a. cbn [PjGrammar.calls] in Hc. rewrite HE' in Hc. discriminate Hc.
  + injection Heq as E1 Heq. subst a'. cbn [PjGrammar.calls] in Hc.
    assert (Hc' : PjGrammar.calls P = PjGrammar.calls P') by (destruct (PjGrammar.is_call a); lia).
    destruct (IH P' E E' r r' Heq Hc' HE HE') as [-> ->]. split; reflexivity.
Qed.
(* a computation that agrees (PjGrammar.agrees): the result, the trace and the rest of the list are those of any
   list that agrees with ok on the first calls of the trace *)
Lemma cnbp_agrees_pre : forall (A : Type) (m : PjGrammar.M A), PjGrammar.agrees m ->
  forall ok ok' r t rest, m ok = (r, t, rest) ->
  (forall i, (i < PjGrammar.calls t)%nat -> nth i ok' true = nth i ok true) ->
  m ok' = (r, t, skipn (PjGrammar.calls t) ok') /\ rest = skipn (PjGrammar.calls t) ok.
Proof.
intros A m Hm ok ok' r t rest E Hag.
destruct (PjGrammar.ok_upto_dec ok (PjGrammar.calls (snd (fst (m []))))) as [Hu | (j & Hj & Hf & Hu)].
- pose proof (proj1 (Hm ok) Hu) as E1. rewrite E in E1. injection E1 as -> -> ->.
  assert (Hu' : PjGrammar.ok_upto ok' (PjGrammar.calls (snd (fst (m []))))).
  { intros i Hi. rewrite (Hag i Hi). exact (Hu i Hi). }
  rewrite (proj1 (Hm ok') Hu'). split; reflexivity.
- destruct (proj2 (Hm ok) j Hj Hf Hu) as (P & e & rest0 & E1 & Hs & Hc & Hic).
  rewrite E in E1. injection E1 as -> -> ->.
  assert (Hct : PjGrammar.calls (P ++ [PjGrammar.EFail (PjGrammar.esize e)]) = S j)
    by (rewrite PjGrammar.calls_app; cbn [PjGrammar.calls PjGrammar.is_call]; lia).
  rewrite Hct in Hag |- *.
  assert (Hf' : nth j ok' true = false) by (rewrite (Hag j ltac:(lia)); exact Hf).
  assert (Hu' : PjGrammar.ok_upto ok' j) by (intros i Hi; rewrite (Hag i ltac:(lia)); exact (Hu i Hi)).
  destruct (proj2 (Hm ok') j Hj Hf' Hu') as (P' & e' & rest' & E2 & Hs' & Hc' & Hic').
  rewrite Hs in Hs'. destruct (cnbp_split_uniq P P' e e' rest0 rest' Hs' ltac:(lia) Hic Hic') as [<- <-].
  rewrite E2. split; reflexivity.
Qed.
(* one bind step: the first computation agrees on the first calls of its own trace, and the continuation's list is
   the rest *)
Lemma cnbp_bind_pre : forall (A B : Type) (m : PjGrammar.M A) (k : A -> PjGrammar.M B) ok ok' r t ok1,
  PjGrammar.agrees m -> m ok = (r, t, ok1) ->
  (forall i, (i < PjGrammar.calls (snd (fst (PjGrammar.jbind m k ok))))%nat -> nth i ok' true = nth i ok true) ->
  (forall i, (i < PjGrammar.calls t)%nat -> nth i ok' true = nth i ok true) /\
  m ok' = (r, t, skipn (PjGrammar.calls t) ok') /\ ok1 = skipn (PjGrammar.calls t) ok /\
  (forall a, r = Some a -> forall i, (i < PjGrammar.calls (snd (fst (k a ok1))))%nat ->
     nth i (skipn (PjGrammar.calls t) ok') true = nth i ok1 true).
Proof.
intros A B m k ok ok' r t ok1 Hm E H.
assert (HT : (PjGrammar.calls t <= PjGrammar.calls (snd (fst (PjGrammar.jbind m k ok))))%nat /\
  forall a, r = Some a -> PjGrammar.calls (snd (fst (PjGrammar.jbind m k ok))) =
    (PjGrammar.calls t + PjGrammar.calls (snd (fst (k a ok1))))%nat).
{ unfold PjGrammar.jbind. rewrite E. destruct r as [a|].
  - destruct (k a ok1) as [[r2 t2] ok2] eqn:Ek. cbn [fst snd]. rewrite PjGrammar.calls_app.
    split; [lia|]. intros a' Ea. injection Ea as <-. rewrite Ek. reflexivity.
  - cbn [fst snd]. split; [lia|]. intros a Ea. discriminate Ea. }
destruct HT as (HT1 & HT2).
assert (Ht : forall i, (i < PjGrammar.calls t)%nat -> nth i ok' true = nth i ok true) by (intros i Hi; apply H; lia).
destruct (cnbp_agrees_pre A m Hm ok ok' r t ok1 E Ht) as (E' & ->).
split; [exact Ht|]. split; [exact E'|]. split; [reflexivity|].
intros a Ea i Hi. rewrite !PjGrammar.nth_skipn_b. apply H. rewrite (HT2 a Ea). lia.
Qed.
(* pj_free's walk (PresetReqAt.jfv / jfl) reads the grant list only through grow, jr_name and jrv, so it agrees as the
   reading does: the same pj_free list for lists agreeing on the first calls of the reading's trace *)
Lemma cnbp_jfv_pre : forall (sm : list Z -> Z * Z) f,
  (forall d x ok ok', (forall i, (i < PjGrammar.calls (snd (fst (PjGrammar.jrv sm f d x ok))))%nat ->
       nth i ok' true = nth i ok true) ->
     PresetReqAt.jfv sm f d x ok' = PresetReqAt.jfv sm f d x ok) /\
  (forall d o n cap acc af y ok ok',
     (forall i, (i < PjGrammar.calls (snd (fst (PjGrammar.jrl sm f d o n cap acc y ok))))%nat ->
       nth i ok' true = nth i ok true) ->
     PresetReqAt.jfl sm f d o n cap af y ok' = PresetReqAt.jfl sm f d o n cap af y ok).
Proof.
intros sm f. induction f as [|f IH]; [split; intros; reflexivity|].
destruct IH as (IHv & IHl). split.
- intros d x ok ok' H. cbn [PresetReqAt.jfv].
  destruct (PjGrammar.skip x) as [|b y] eqn:Ex; [reflexivity|].
  destruct (b =? 123) eqn:E1; [|destruct (b =? 91) eqn:E2].
  + cbn [PjGrammar.jrv] in H. rewrite Ex, E1 in H.
    unfold PresetReqAt.jf_cont, PjGrammar.jr_cont in *. cbv zeta in *.
    destruct (Nat.ltb _ (S d)); [reflexivity|].
    destruct (PjGrammar.skip (tl (b :: y))) as [|c r].
    * exact (IHl (S d) true 0%nat 0%nat [] [] [] ok ok' H).
    * destruct (c =? PjGrammar.closer true); [reflexivity|]. exact (IHl (S d) true 0%nat 0%nat [] [] _ ok ok' H).
  + cbn [PjGrammar.jrv] in H. rewrite Ex, E1, E2 in H.
    unfold PresetReqAt.jf_cont, PjGrammar.jr_cont in *. cbv zeta in *.
    destruct (Nat.ltb _ (S d)); [reflexivity|].
    destruct (PjGrammar.skip (tl (b :: y))) as [|c r].
    * exact (IHl (S d) false 0%nat 0%nat [] [] [] ok ok' H).
    * destruct (c =? PjGrammar.closer false); [reflexivity|]. exact (IHl (S d) false 0%nat 0%nat [] [] _ ok ok' H).
  + destruct (PjGrammar.jrv sm (S f) d x ok) as [[rv tv] okv] eqn:Ev. cbn [fst snd] in H |- *.
    destruct (cnbp_agrees_pre _ _ (proj1 (PjGrammar.agrees_fuel sm (S f)) d x) ok ok' rv tv okv Ev H) as (Ev' & _).
    rewrite Ev'. reflexivity.
- intros d o n cap acc af y ok ok' H. cbn [PresetReqAt.jfl]. cbn [PjGrammar.jrl] in H.
  destruct (PjGrammar.grow o n cap ok) as [[rg tg] okg] eqn:Eg.
  destruct (cnbp_bind_pre _ _ _ _ ok ok' _ _ _ (PjGrammar.agrees_grow o n cap) Eg H) as (_ & Eg' & -> & Hk1).
  rewrite Eg'. destruct rg as [cap1|]; [|reflexivity].
  specialize (Hk1 cap1 eq_refl). cbv beta in Hk1.
  set (ok1 := skipn (PjGrammar.calls tg) ok) in *. set (ok1' := skipn (PjGrammar.calls tg) ok') in *.
  destruct (PjGrammar.jr_name o y ok1) as [[rn tn] okn] eqn:En.
  destruct (cnbp_bind_pre _ _ _ _ ok1 ok1' _ _ _ (PjGrammar.agrees_jr_name o y) En Hk1) as (_ & En' & -> & Hk2).
  rewrite En'. destruct rn as [[name y1]|]; [|reflexivity].
  specialize (Hk2 (name, y1) eq_refl). cbv beta iota in Hk2.
  set (ok2 := skipn (PjGrammar.calls tn) ok1) in *. set (ok2' := skipn (PjGrammar.calls tn) ok1') in *.
  destruct (PjGrammar.jrv sm f d y1 ok2) as [[rv tv] okv] eqn:Ev.
  destruct (cnbp_bind_pre _ _ _ _ ok2 ok2' _ _ _ (proj1 (PjGrammar.agrees_fuel sm f) d y1) Ev Hk2)
    as (Hv & Ev' & -> & Hk3).
  cbv zeta. rewrite (IHv d y1 ok2 ok2' ltac:(rewrite Ev; exact Hv)), Ev'.
  destruct rv as [[v r]|]; [|reflexivity].
  specialize (Hk3 (v, r) eq_refl). cbv beta iota in Hk3.
  destruct (PjGrammar.skip r) as [|c r1]; [reflexivity|].
  destruct (c =? 44); [|reflexivity].
  exact (IHl d o (S n) cap1 ((name, v) :: acc) _ r1 _ _ Hk3).
Qed.
(* (d): the reading, its trace and its pj_free list, hence its events, of two lists agreeing on its calls *)
Lemma cnbp_jr_run_pre : forall (sm : list Z -> Z * Z) x ok ok',
  (forall i, (i < PjGrammar.calls (snd (PjGrammar.jr_run sm x ok)))%nat -> nth i ok' true = nth i ok true) ->
  PjGrammar.jr_run sm x ok' = PjGrammar.jr_run sm x ok.
Proof.
intros sm x ok ok' H. rewrite !PjGrammar.jr_run_eq in *. cbn [fst snd] in H.
destruct (PjGrammar.jr_value sm 0 x ok) as [[r t] rest] eqn:E. cbn [fst snd] in H |- *.
destruct (cnbp_agrees_pre _ _ (PjGrammar.agrees_jr_value sm 0 x) ok ok' r t rest E H) as (E' & _).
rewrite E'. reflexivity.
Qed.
Lemma cnbp_parse_evs_pre : forall (sm : list Z -> Z * Z) x ok ok',
  (forall i, (i < PjGrammar.calls (snd (PjGrammar.jr_run sm x ok)))%nat -> nth i ok' true = nth i ok true) ->
  PresetReqAt.parse_evs sm x ok' = PresetReqAt.parse_evs sm x ok.
Proof.
intros sm x ok ok' H. unfold PresetReqAt.parse_evs, PresetReqAt.rtr, PresetReqAt.pj_frees.
rewrite (cnbp_jr_run_pre sm x ok ok' H).
rewrite (proj1 (cnbp_jfv_pre sm _) 0%nat x ok ok'); [reflexivity|].
rewrite PjGrammar.jr_run_eq in H. exact H.
Qed.
(* ... and the same pj_free list (the reading's free order, tparse_noting_specX's Some arm) *)
Lemma cnbp_pj_frees_pre : forall (sm : list Z -> Z * Z) x ok ok',
  (forall i, (i < PjGrammar.calls (snd (PjGrammar.jr_run sm x ok)))%nat -> nth i ok' true = nth i ok true) ->
  PresetReqAt.pj_frees sm ok' x = PresetReqAt.pj_frees sm ok x.
Proof.
intros sm x ok ok' H. unfold PresetReqAt.pj_frees.
apply (proj1 (cnbp_jfv_pre sm _) 0%nat x ok ok').
rewrite PjGrammar.jr_run_eq in H. exact H.
Qed.
(* THE GRANT of a reading's outcome list ok: o = None when ok grants every allocation the reading makes, Some j at
   its first refusal j; the same reading, events and pj_free list, and ran-out exactly when ok refuses inside the
   reading *)
Lemma cnbp_grant : forall (sm : list Z -> Z * Z) x ok, exists o,
  PjGrammar.jr_run sm x (PresetRun.okof o) = PjGrammar.jr_run sm x ok /\
  PresetReqAt.parse_evs sm x (PresetRun.okof o) = PresetReqAt.parse_evs sm x ok /\
  PresetReqAt.pj_frees sm (PresetRun.okof o) x = PresetReqAt.pj_frees sm ok x /\
  ((PresetRun.ranout sm x o = false /\
    forall i, (i < PjGrammar.calls (snd (PjGrammar.jr_run sm x ok)))%nat -> nth i ok true = true) \/
   (PresetRun.ranout sm x o = true /\
    exists i, (i < PjGrammar.calls (snd (PjGrammar.jr_run sm x ok)))%nat /\ nth i ok true = false)).
Proof.
intros sm x ok.
destruct (PjGrammar.ok_upto_dec ok (PjGrammar.ncalls sm x)) as [Hu | (j & Hj & Hf & Hu)].
- exists None.
  pose proof (PjGrammar.G7_1_calls sm x ok Hu) as Ec.
  assert (Hag : forall i, (i < PjGrammar.calls (snd (PjGrammar.jr_run sm x ok)))%nat ->
    nth i (PresetRun.okof None) true = nth i ok true).
  { intros i Hi. rewrite Ec in Hi. rewrite (Hu i Hi). cbn [PresetRun.okof]. destruct i; reflexivity. }
  split; [exact (cnbp_jr_run_pre sm x ok _ Hag)|]. split; [exact (cnbp_parse_evs_pre sm x ok _ Hag)|].
  split; [exact (cnbp_pj_frees_pre sm x ok _ Hag)|].
  left. split; [reflexivity|]. intros i Hi. rewrite Ec in Hi. exact (Hu i Hi).
- exists (Some j).
  destruct (PjGrammar.G7_2 sm x ok j Hj Hf Hu) as (_ & Ec).
  assert (Hag : forall i, (i < PjGrammar.calls (snd (PjGrammar.jr_run sm x ok)))%nat ->
    nth i (PresetRun.okof (Some j)) true = nth i ok true).
  { intros i Hi. rewrite Ec in Hi. cbn [PresetRun.okof]. destruct (Nat.lt_ge_cases i j) as [Hl|Hg].
    - rewrite (PresetRun.okk_true j i Hl), (Hu i Hl). reflexivity.
    - replace i with j by lia. rewrite PresetRun.okk_false, Hf. reflexivity. }
  split; [exact (cnbp_jr_run_pre sm x ok _ Hag)|]. split; [exact (cnbp_parse_evs_pre sm x ok _ Hag)|].
  split; [exact (cnbp_pj_frees_pre sm x ok _ Hag)|].
  right. split.
  + cbn [PresetRun.ranout]. apply Nat.ltb_lt. unfold PjGrammar.ncalls in Hj. exact Hj.
  + exists j. split; [rewrite Ec; lia | exact Hf].
Qed.
(* a grant under which the reading does not run out gives the all-granted reading's events *)
Lemma cnbp_pe_none : forall (sm : list Z -> Z * Z) x o, PresetRun.ranout sm x o = false ->
  PresetReqAt.parse_evs sm x (PresetRun.okof o) = PresetReqAt.parse_evs sm x [].
Proof.
intros sm x [j|] H; [|reflexivity]. cbn [PresetRun.ranout PresetRun.okof] in *. apply Nat.ltb_ge in H.
apply cnbp_parse_evs_pre. intros i Hi. unfold PresetReqAt.rtr in H.
rewrite (PresetRun.okk_true j i ltac:(lia)). destruct i; reflexivity.
Qed.
(* the peak of a count along the next reading, from a live set reached by E, inside the peak along E ++ X ++ R *)
Lemma cnbp_pkR_mid : forall f (s0 s : list Z) E X R,
  Permutation s (PresetReqAt.hlive_from s0 E) ->
  (PresetRun.pkR f s X <= PresetRun.pkR f s0 (E ++ X ++ R))%nat.
Proof.
intros f s0 s E X R H. rewrite !PresetRun.pkR_app.
pose proof (PresetRun.pkR_mono f X s (PresetReqAt.hlive_from s0 E) (PresetReqAt.subm_perm _ _ (Permutation_sym H))).
lia.
Qed.
(* EVERY REQUEST OF A READING IS AT MOST THE ALL-GRANTED READING'S LARGEST (PRH_Charge.v prh_maxreq's comment: a
   refused run is P ++ [EFail (esize E)] with E in the granted trace, PjGrammar.agrees), so at most RQ_pj_parse x;
   what prh_oks's refusal clause asks of each call's request (prh_ev_reqs) against g_most *)
Lemma cnbp_maxreq_in : forall l e, In e l -> Z.of_nat (PjGrammar.esize e) <= PRH_Charge.prh_maxreq l.
Proof.
induction l as [|a l IH]; intros e H; [destruct H|]. unfold PRH_Charge.prh_maxreq in *. cbn [map fold_right].
destruct H as [<-|H]; [lia|]. specialize (IH e H). lia.
Qed.
Lemma cnbp_maxreq_nonneg : forall l, 0 <= PRH_Charge.prh_maxreq l.
Proof. induction l as [|a l IH]; unfold PRH_Charge.prh_maxreq in *; cbn [map fold_right]; lia. Qed.
Lemma cnbp_req_le : forall (sm : list Z -> Z * Z) x ok e, In e (snd (PjGrammar.jr_run sm x ok)) ->
  PjReqBound.ev_req e <= PRH_Charge.prh_maxreq (snd (PjGrammar.jr_run sm x [])).
Proof.
intros sm x ok e Hin. rewrite PjGrammar.jr_run_eq in Hin |- *. cbn [snd] in Hin |- *.
pose proof (PjGrammar.agrees_jr_value sm 0 x ok) as (H1 & H2).
pose proof (PjReqBound.ev_req_le_esize e) as He.
destruct (PjGrammar.ok_upto_dec ok (PjGrammar.calls (snd (fst (PjGrammar.jr_value sm 0 x [])))))
  as [Hu | (j & Hj & Hf & Hu)].
- rewrite (H1 Hu) in Hin. cbn [fst snd] in Hin. pose proof (cnbp_maxreq_in _ e Hin). lia.
- destruct (H2 j Hj Hf Hu) as (P & E & rest & E1 & Hs & _ & _). rewrite E1 in Hin. cbn [fst snd] in Hin.
  rewrite Hs. apply in_app_or in Hin as [Hin|Hin].
  + pose proof (cnbp_maxreq_in (P ++ E :: rest) e ltac:(apply in_or_app; left; exact Hin)). lia.
  + destruct Hin as [<-|[]]. cbn [PjReqBound.ev_req].
    pose proof (cnbp_maxreq_in (P ++ E :: rest) E ltac:(apply in_or_app; right; left; reflexivity)). lia.
Qed.
Lemma cnbp_ev_reqs_le : forall (sm : list Z -> Z * Z) x ok i,
  nth i (prh_ev_reqs (snd (PjGrammar.jr_run sm x ok))) 0 <= PRH_Charge.prh_maxreq (snd (PjGrammar.jr_run sm x [])).
Proof.
intros sm x ok i. unfold prh_ev_reqs.
destruct (Nat.lt_ge_cases i (length (map PjReqBound.ev_req (filter PjGrammar.is_call (snd (PjGrammar.jr_run sm x ok))))))
  as [Hl|Hg].
- apply (nth_In _ 0) in Hl. apply in_map_iff in Hl as (e & <- & He).
  (* prh_ev_reqs's filter is stdpp's (a decidable predicate): its membership through elem_of *)
  assert (He' : In e (snd (PjGrammar.jr_run sm x ok))).
  { first [ apply list_elem_of_In in He | apply elem_of_list_In in He ].
    apply list_basics.list.list_elem_of_filter in He.
    destruct He as (_ & He).
    first [ apply list_elem_of_In; exact He | apply elem_of_list_In; exact He ]. }
  exact (cnbp_req_le sm x ok e He').
- rewrite nth_overflow by exact Hg. apply cnbp_maxreq_nonneg.
Qed.

(* ==== 2. the three call sites: CLOSED facts, one top-level lemma per call site and its return slot (the only
   vm_compute of this file, each on a closed goal of the listing's own table) ==== *)
Lemma cnb_pn_site1 : plookup B_prog_tpi_cno (CNB_OFF + CNB_PN1) = Some (PCall AS_parse_noting 1%bv) /\
  match plookup B_prog_tpi_cno (CNB_OFF + CNB_RET1) with Some _ => true | None => false end = true.
Proof.
split; lazymatch goal with
  | |- plookup B_prog_tpi_cno (CNB_OFF + CNB_PN1) = _ => vm_compute; reflexivity
  | |- match plookup B_prog_tpi_cno (CNB_OFF + CNB_RET1) with _ => _ end = true => vm_compute; reflexivity end.
Qed.
Lemma cnb_pn_site2 : plookup B_prog_tpi_cno (CNB_OFF + CNB_PN2) = Some (PCall AS_parse_noting 1%bv) /\
  match plookup B_prog_tpi_cno (CNB_OFF + CNB_RET2) with Some _ => true | None => false end = true.
Proof.
split; lazymatch goal with
  | |- plookup B_prog_tpi_cno (CNB_OFF + CNB_PN2) = _ => vm_compute; reflexivity
  | |- match plookup B_prog_tpi_cno (CNB_OFF + CNB_RET2) with _ => _ end = true => vm_compute; reflexivity end.
Qed.
Lemma cnb_pn_site3 : plookup B_prog_tpi_cno (CNB_OFF + CNB_PN3) = Some (PCall AS_parse_noting 1%bv) /\
  match plookup B_prog_tpi_cno (CNB_OFF + CNB_RET3) with Some _ => true | None => false end = true.
Proof.
split; lazymatch goal with
  | |- plookup B_prog_tpi_cno (CNB_OFF + CNB_PN3) = _ => vm_compute; reflexivity
  | |- match plookup B_prog_tpi_cno (CNB_OFF + CNB_RET3) with _ => _ end = true => vm_compute; reflexivity end.
Qed.
(* 724 `mv s7, a0` (PW 0x50b93 = addi s7, a0, 0), then CNB_CMP *)
Lemma cnb_pn_mv : cnb_is_addi CNB_RET3 23%bv 10%bv 0 = true.
Proof. lazymatch goal with |- cnb_is_addi CNB_RET3 _ _ _ = true => vm_compute; reflexivity end. Qed.

(* ==== 3. the call ==== *)
Section rpn. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Existing Instance prh_img_B.
Context {PA : PAImg B_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
(* the world relation after a free (the move): the hidden set may grow only inside the fixed zone RZ_cf *)
#[local] Notation WLE' := (wle' SEGS YGcfRehidePost.RZ_cf).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
Hypothesis IMG : cnb_img B.
Variable CTX0 : list (list Z).
(* The kit's text of parse_noting (PRH_FnCheck.v tparse_noting_specX, restated for the move: no DW; the conclusion SRr'
   segs RZ_cf; the post fpostFbm at wle' segs RZ_cf; the LAST premise PresetHullBudget.hull_budget S (parse_evs
   jr_strtod tb []) and the inner post's FIRST conjunct PresetHullBudget.hull_used S S' (parse_evs jr_strtod tb [])),
   for ANY float state *)
Hypothesis HPN : forall fz : YK11.FPState,
  @tparse_noting_specX fz rc ci cp prh_img_B RL B_prog_listing PA B ARx SK CTX0.

Lemma cnbp_stk_pn : STK_parse_noting = 27216.
Proof. lazymatch goal with |- STK_parse_noting = _ => vm_compute; reflexivity end. Qed.

(* the three call sites: the PCall slot, and the return address below the ceiling (fpre's raZ bound), even *)
Lemma cnb_pn_ret_ok : forall off, off = CNB_PN1 \/ off = CNB_PN2 \/ off = CNB_PN3 ->
  plookup B_prog_tpi_cno (CNB_OFF + off) = Some (PCall AS_parse_noting 1%bv) /\
  4096 <= cnb_pc (off + 4) < YM05.alloc_ceiling /\ YK0s.ret_ok (w64 (cnb_pc (off + 4))) /\ 0 <= off < 2 ^ 28.
Proof.
intros off Hoff. pose proof (cnbi_base B IMG) as HB. pose proof cnb_off_val as HO.
assert (Hs : plookup B_prog_tpi_cno (CNB_OFF + off) = Some (PCall AS_parse_noting 1%bv) /\
  match plookup B_prog_tpi_cno (CNB_OFF + (off + 4)) with Some _ => true | None => false end = true /\
  0 <= off < 2 ^ 28 /\ (CNB_OFF + (off + 4)) mod 2 = 0).
{ destruct Hoff as [-> | [-> | ->]];
    [destruct cnb_pn_site1 as (A1 & A2) | destruct cnb_pn_site2 as (A1 & A2) | destruct cnb_pn_site3 as (A1 & A2)];
    (split; [exact A1|]); (split; [exact A2|]); rewrite HO;
    (split; [unfold CNB_PN1, CNB_PN2, CNB_PN3; lia | reflexivity]). }
destruct Hs as (Hpl & Hsl & Hr28 & Hr2).
unfold cnb_pc, w64. replace (BASE + CNB_OFF + (off + 4)) with (BASE + (CNB_OFF + (off + 4))) by lia.
split; [exact Hpl|]. split; [split|split].
- rewrite HB. unfold B_prog_base. lia.
- exact (pa_slot_lt_ceil_b (PL := PL_cno_B) (PI := PA) (CNB_OFF + (off + 4)) ltac:(lia) Hsl).
- apply ret_ok_codeptr_v; [lia | exact Hr2].
- exact Hr28.
Qed.

Lemma cnb_dne : forall D : cnb_in, (cnb_d1 D =? cnb_d2 D) = false /\ (cnb_d1 D =? cnb_d3 D) = false /\
  (cnb_d2 D =? cnb_d1 D) = false /\ (cnb_d2 D =? cnb_d3 D) = false /\
  (cnb_d3 D =? cnb_d1 D) = false /\ (cnb_d3 D =? cnb_d2 D) = false.
Proof.
intros D. unfold cnb_d1, cnb_d2, cnb_d3.
repeat match goal with |- _ /\ _ => split end; apply Z.eqb_neq; lia.
Qed.

(* the reading's slot in the three structs: the struct at d takes the reading's state st, the other two keep theirs *)
Definition cnb_upd_ok (D : cnb_in) (d : Z) (st st1 st2 st3 : cnb_st) (u : cnb_st * cnb_st * cnb_st) : Prop :=
  Permutation (cnb_Dof (fst (fst u)) ++ cnb_Dof (snd (fst u)) ++ cnb_Dof (snd u))
    (cnb_Dof st ++ cnb_Dof st1 ++ cnb_Dof st2 ++ cnb_Dof st3) /\
  (if d =? cnb_d1 D then st1 = None /\ fst (fst u) = st else fst (fst u) = st1) /\
  (if d =? cnb_d2 D then st2 = None /\ snd (fst u) = st else snd (fst u) = st2) /\
  (if d =? cnb_d3 D then st3 = None /\ snd u = st else snd u = st3).

(* the call of a callee whose text concludes, across a free, in SRr' SEGS RZ_cf with the budgeted apost_base_xbFR at
   wle' SEGS RZ_cf (P := wbudget [] (prh_wk F_parse_noting)) at window STK_parse_noting below sp = s1, footprint the
   struct [d, d + 56) in the function's own fake frame: the callee's journal composes with the function's
   (ajournal_xw_subR at wle'; s1 >= entry sp - 176 and STK_check_no_overread - STK_parse_noting = 176), and the budgets
   add (wbudget_app): the next cut's journal is cnb_JR at wle' at wk + 2 *)
Lemma cnbp_call_x : forall (W : world SEGS) fxk regs mem md D wk ly S Hp k d
  (Q : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  cnb_JR B ARx WLE' D wk ly S Hp W mem md k -> spZ regs = cnb_S1 D ->
  frame_addr ly CNB_CID (bi_fpos D) <= d -> d + 56 <= frame_addr ly CNB_CID (bi_fpos D) + fs_frame_bytes CNB_CID ->
  SRr' SEGS YGcfRehidePost.RZ_cf W (@cnb_cfg SEGS fxk (SIGMA AS_parse_noting) regs mem md)
    (YCbqGwild.apost_base_xbFR (fx := fxk) (SK := SK) SEGS B prh_pst ARx WLE'
       (YCbqGwild.wbudget [] (prh_wk F_parse_noting)) STK_parse_noting [(d, d + 56)] regs ly S Hp W mem md Q) ->
  SRr' SEGS YGcfRehidePost.RZ_cf W (@cnb_cfg SEGS fxk (SIGMA AS_parse_noting) regs mem md)
    (fun W2 c2 => exists (fx' : YK11.FPState) ly2 S2 Hp2 regs2 mem2 md2 k1 WS1,
       c2 = mkCfg (@YK11.mkst fx' regs2 (getr regs 1) mem2 (YK11.seg_rom SEGS)) md2 /\
       frm_zero (@YK11.fp_csr fx') /\ fregs_kept_x fxk fx' /\
       cnb_JR B ARx WLE' D (wk + prh_wk F_parse_noting) ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
       ajournal_xwR (SK := SK) SEGS B prh_pst ARx WLE' STK_parse_noting (cnb_S1 D) [(d, d + 56)] ly S Hp W mem md []
         ly2 S2 Hp2 W2 mem2 md2 k1 WS1 /\
       aregs_preserved regs regs2 /\ Q ly2 S2 Hp2 W2 regs2 mem2 md2).
Proof.
intros W fxk regs mem md D wk ly S Hp k d Q HJ Hsp Hd1 Hd2 HT.
destruct HJ as (WS0 & HJW & HWB).
pose proof (ajxR_stk HJW) as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof cnbp_stk_pn as ES2. pose proof cnb_stk_val as ES1.
destruct (cnbp_S1 D Hal16) as (HS1b & HS1c & Ho16).
eapply (SRr'_mono SEGS YGcfRehidePost.RZ_cf); [exact HT|].
cbv beta. intros W2 c2 _ (fx' & ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & WS1 & -> & HFZ & HFK & HPW & HJ1 & HP2 & HQ).
rewrite Hsp in HJ1.
exists fx', ly2, S2, Hp2, regs2, mem2, md2, k1, WS1. split; [reflexivity|]. split; [exact HFZ|]. split; [exact HFK|].
split; [|split; [exact HJ1 | split; [exact HP2 | exact HQ]]].
assert (Hle1 : cnb_sp0 D - STK_check_no_overread <= cnb_S1 D - STK_parse_noting) by lia.
assert (Hle2 : cnb_S1 D <= cnb_sp0 D) by lia.
assert (HFsub : fp_sub_x B STK_check_no_overread (cnb_sp0 D) [] [(d, d + 56)] (bi_ly D) (bi_S D)
                  [(CNB_CID, bi_fpos D)] ly S).
{ intros a (rr & Hin & Hrr). destruct Hin as [<-|[]]. cbn [fst snd] in Hrr.
  right. right. left. exists (CNB_CID, bi_fpos D). split; [left; reflexivity|].
  unfold in_zr, frame_rng. cbn [fst snd]. lia. }
apply (cnb_J_wildR B ARx WLE' D wk ly2 S2 Hp2 W2 mem2 md2 (k + k1) WS0 WS1); [|exact HWB | exact HPW].
exact (ajournal_xw_subR (SK := SK) SEGS B prh_pst ARx LAWS pa_segs_low WLE' (wle'_trans SEGS YGcfRehidePost.RZ_cf)
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJW HJ1 Hle1 Hle2 HFsub).
Qed.

(* THE CALL AT THE CALLEE ENTRY (ra = ret): one reading of the copy r into the struct d, after the events E since
   entry, at the spent wild budget wk (wk + 2 <= 6: the room from cnb_roomR); the reading's grant og is CHOSEN after
   the call to match the instance's outcomes (cnbp_grant). The struct d gets the free order at og (cnb_fo); a tree of
   another struct keeps its free order (pj_foR_frame). The base and the journals are at wle' SEGS RZ_cf (the call
   crosses a free). THE HULL: the text's budget premise is the head of the budget the caller passes
   (hull_budget_infix); the post's hull_used leaves the rest Hr at S' (hull_budget_app) *)
Lemma cnbp_pn_entry : forall P, srr_inv_laws SEGS P -> srr_inv_call SEGS P -> srr_inv_mn SEGS P ->
  forall D fxk ly S Hp W regs mem md k (wk : nat) Lam peak cnt (nr : nat) r1 r2 r3 st1 st2 st3 r d ret E
    (upd : cnb_st -> cnb_st * cnb_st * cnb_st) (Hr : list PresetReqAt.hev),
  (wk + prh_wk F_parse_noting <= prh_wk F_check_no_overread)%nat ->
  cnb_pre (fx := fx) B ARx CTX0 D ->
  cnb_baseR (fx := fx) B ARx WLE' D fxk ly S Hp W regs mem md k wk ->
  cnb_regsat regs (cnb_core D ++ [(10%bv, r); (11%bv, cnb_size D); (12%bv, d)]) ->
  getr regs 1%bv = w64 ret -> YK0s.ret_ok (w64 ret) -> 4096 <= ret -> ret < YM05.alloc_ceiling ->
  (r = r1 \/ r = r2 \/ r = r3) -> r <> 0 ->
  (d = cnb_d1 D \/ d = cnb_d2 D \/ d = cnb_d3 D) ->
  (nr <= 2)%nat ->
  cnb_prog D E S ->
  (exists R, ck_cno_evs ReaderRes.jr_strtod (bi_x D) None None None = E ++ cnb_pe D None ++ R) ->
  cnb_mid B D ly S Hp W mem Lam peak cnt 0 0 nr r1 r2 r3 st1 st2 st3 ->
  (forall st, cnb_upd_ok D d st st1 st2 st3 (upd st)) ->
  P mem ->
  PresetHullBudget.hull_budget S (PresetReqAt.parse_evs ReaderRes.jr_strtod (bi_x D) [] ++ Hr) ->
  SRr' SEGS YGcfRehidePost.RZ_cf W (@cnb_cfg SEGS fxk (SIGMA AS_parse_noting) regs mem md) (fun W' c' =>
    exists fx' ly' S' Hp' regs' mem' md' k' Lam' peak' cnt' ran' rcv st og,
      c' = @cnb_cfg SEGS fx' ret regs' mem' md' /\
      cnb_baseR (fx := fx) B ARx WLE' D fx' ly' S' Hp' W' regs' mem' md' k' (wk + prh_wk F_parse_noting) /\
      aregs_preserved regs regs' /\ getr regs' 10 = w64 rcv /\
      (forall a, cnb_S1 D <= a < cnb_sp0 D -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) /\
      cnb_prog D (E ++ cnb_pe D og) S' /\ ran' = (if cnb_ro D og then 1 else 0) /\
      cnb_mid B D ly' S' Hp' W' mem' Lam' peak' cnt' ran' 0 (Datatypes.S nr) r1 r2 r3
        (fst (fst (upd st))) (snd (fst (upd st))) (snd (upd st)) /\
      cnb_res D ran' rcv st /\ cnb_rd D og st /\ cnb_fo D W' mem' Lam' og d st /\
      (forall o d0 st0, (d0 = cnb_d1 D \/ d0 = cnb_d2 D \/ d0 = cnb_d3 D) -> d0 <> d -> incl (cnb_Dof st0) Lam ->
         cnb_fo D W mem Lam o d0 st0 -> cnb_fo D W' mem' Lam' o d0 st0) /\
      P mem' /\ PresetHullBudget.hull_budget S' Hr).
Proof.
intros P PL PC PM D fxk ly S Hp W regs mem md k wk Lam peak cnt nr r1 r2 r3 st1 st2 st3 r d ret E upd HrL
  Hwk HPRE HB HR Hra1 Hrok Hret0 HretC Hr Hr0 Hd Hnr HPROG HSPLIT HM HU HP HHB.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@cf_head_nonneg cp) as Hh0.
pose proof cnbp_stk_pn as ES2. pose proof cnb_stk_val as ES1.
assert (Efb : fs_frame_bytes CNB_CID = 512) by reflexivity.
destruct (cnb_chainR B ARx WLE' CTX0 D fxk ly S Hp W regs mem md k wk HPRE HB) as (ch1 & Hch1).
(* ---- the entry ---- *)
pose proof HPRE as HPRE'. unfold cnb_pre in HPRE'. cbv zeta in HPRE'.
destruct HPRE' as ((HPRE0 & HRO0 & HHI0 & HRA0 & HFZ0) & HMN0 & HCL & HCTX & H10e & H11e & Hsz & HSRC0 & HHOME0 &
  HLED0 & HCNT0 & HRAN0 & HRQ0 & HLIVE0 & HPAD & HRQ & HFR0 & HROOM0 & HFRM0 & HWR0 & HPKS0 & HPK240 & _).
destruct HPRE0 as (HAR0 & Hrok0 & Hra0 & Hgp0 & Htp0 & Hstk0 & Hwin0 & Hch0 & Hqt0).
change (spZ (bi_regs D)) with (cnb_sp0 D) in HHI0.
(* ---- the cut ---- *)
destruct HB as (HFZ & HFK & HJ & HFRM & HSAV & HG3 & HG4 & HRO).
destruct HM as (HC1 & HC2 & HC3 & HLED & HPK & HCNT & HROOM & HLIVE & HO1 & HO2 & HO3 & HD1 & HD2 & HD3 &
  HPL & HPB & HFRESH & HDATA).
pose proof HJ as (WS0 & HJW & HWB).
pose proof (ajxR_ar HJW) as HAR. pose proof (ajxR_ly HJW) as Hly. pose proof (ajxR_hi HJW) as F1.
pose proof (ajxR_stk HJW) as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof Hly as (_ & _ & _ & _ & _ & EF & _ & _ & Etop & Eslo & Eshi & _).
rewrite ES1 in F1, Hslo, Hbot.
destruct (cnbp_S1 D Hal16) as (HS1b & HS1c & Ho16).
(* the frame and the struct d in it *)
assert (Hin3 : In (CNB_CID, bi_fpos D) (frames S)) by (rewrite (proj1 HFRM); left; reflexivity).
assert (EFa : frame_addr ly CNB_CID (bi_fpos D) = cnb_F D) by (unfold cnb_F, frame_addr; rewrite EF; reflexivity).
destruct (alx_frames SEGS B ARx LAWS ly S Hp W mem md CNB_CID (bi_fpos D) HAR Hin3) as (HF32 & HFapp & HFb & HFs).
destruct (frames_bounds_x SEGS B ARx LAWS ly S Hp W mem md CNB_CID (bi_fpos D) HAR Hin3) as (HF4096 & HFceil & _).
rewrite EFa in HF32, HFapp, HFb, HFs, HF4096, HFceil. rewrite Efb in HFapp, HFb, HFs, HFceil.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
assert (Hdd : cnb_F D + 32 <= d /\ d + 56 <= cnb_F D + 280 /\ d mod 32 = 0).
{ unfold cnb_d1, cnb_d2, cnb_d3 in Hd.
  destruct Hd as [-> | [-> | ->]]; (split; [lia|]); (split; [lia|]).
  - apply (cnbp_mod32_at (cnb_F D) _ 1 HF32). lia.
  - apply (cnbp_mod32_at (cnb_F D) _ 4 HF32). lia.
  - apply (cnbp_mod32_at (cnb_F D) _ 7 HF32). lia. }
assert (Hdop : cnb_open W mem d) by (destruct Hd as [-> | [-> | ->]]; assumption).
(* the registers *)
assert (Hinl : forall (rr : bv 5) v, In (rr, v) (cnb_core D ++ [(10%bv, r); (11%bv, cnb_size D); (12%bv, d)]) ->
  getr regs rr = w64 v) by (intros rr v Hpi; exact (cnb_regsat_get regs _ rr v HR Hpi)).
assert (Hsp : spZ regs = cnb_S1 D).
{ unfold spZ. rewrite (Hinl 2%bv (cnb_S1 D)) by (unfold cnb_core; cbn [app In]; tauto). unfold w64.
  rewrite unsigned_lit_small by lia. reflexivity. }
assert (Hs0 : s0Z regs = cnb_sp0 D).
{ unfold s0Z. rewrite (Hinl 8%bv (cnb_sp0 D)) by (unfold cnb_core; cbn [app In]; tauto). unfold w64.
  rewrite unsigned_lit_small by lia. reflexivity. }
assert (Hraz : raZ regs = ret) by (unfold raZ; rewrite Hra1; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
assert (H10 : getr regs 10 = w64 r) by (exact (Hinl 10%bv r ltac:(unfold cnb_core; cbn [app In]; tauto))).
assert (H11 : getr regs 11 = w64 (cnb_size D)) by (exact (Hinl 11%bv (cnb_size D) ltac:(unfold cnb_core; cbn [app In]; tauto))).
assert (H12 : getr regs 12 = w64 d) by (exact (Hinl 12%bv d ltac:(unfold cnb_core; cbn [app In]; tauto))).
(* the copy read *)
assert (HrC : cnb_copy B D ly S Hp W mem r) by (destruct Hr as [-> | [-> | ->]]; assumption).
destruct HrC as [Hr00|(Hrb & HrHp & HrSRC)]; [exfalso; exact (Hr0 Hr00)|].
pose proof HrSRC as (HrBy & Hr4096 & HrCeil & HrAm & HrRA & HrHV).
(* the text's two room counts along the all-granted reading, from the count along check_no_overread's list *)
assert (HPKS : Z.of_nat (PresetRun.pkR YGcfRoomLive.rl_sec_req (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
    (PresetReqAt.parse_evs ReaderRes.jr_strtod (bi_x D) [])) <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV).
{ destruct HSPLIT as (R & ER). rewrite ER in HPKS0.
  pose proof (cnbp_pkR_mid YGcfRoomLive.rl_sec_req _ _ E (cnb_pe D None) R (proj1 HPROG)) as Hm.
  unfold cnb_pe in Hm, HPKS0. cbn [PresetRun.okof] in Hm, HPKS0. lia. }
assert (HPK24 : Z.of_nat (PresetRun.pkR (PresetRoom.in_cls YG00.kBatchClass) (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
    (PresetReqAt.parse_evs ReaderRes.jr_strtod (bi_x D) [])) <= PresetLiveBounds.L24 + PresetLiveBounds.DRV).
{ destruct HSPLIT as (R & ER). rewrite ER in HPK240.
  pose proof (cnbp_pkR_mid (PresetRoom.in_cls YG00.kBatchClass) _ _ E (cnb_pe D None) R (proj1 HPROG)) as Hm.
  unfold cnb_pe in Hm, HPK240. cbn [PresetRun.okof] in Hm, HPK240. lia. }
(* counts and budget *)
assert (HLV0 : 0 <= PRH_FnPj.LIVE_pj_parse (bi_x D)).
{ unfold PRH_FnPj.LIVE_pj_parse. pose proof (cnbp_hpeak_nonneg (prhPj_ptrace (bi_x D))).
  assert (0 <= cf_head * (Z.of_nat (PjGrammar.calls (prhPj_ptrace (bi_x D))) + 1)) by (apply Z.mul_nonneg_nonneg; lia).
  lia. }
assert (Hnc : ck_ncalls (bi_x D) <= 2 * cnb_size D + 2).
{ unfold ck_ncalls, cnb_size, PjGrammar.ncalls. pose proof (PjGrammar.G7_4 ReaderRes.jr_strtod (bi_x D) []). lia. }
assert (Hnc0 : 0 <= ck_ncalls (bi_x D)) by (unfold ck_ncalls; lia).
assert (Hnrnc : Z.of_nat nr * ck_ncalls (bi_x D) <= 2 * ck_ncalls (bi_x D)) by (apply Z.mul_le_mono_nonneg_r; lia).
assert (Hsz0 : 0 <= cnb_size D) by (unfold cnb_size; lia).
assert (Hlv1 : blocks_bytes S + PRH_FnPj.LIVE_pj_parse (bi_x D) <= LIVE_MAX).
{ assert (H31 : 1 <= Z.of_nat (3 - nr)) by lia.
  pose proof (Z.mul_le_mono_nonneg_r 1 (Z.of_nat (3 - nr)) (PRH_FnPj.LIVE_pj_parse (bi_x D)) HLV0 H31) as HM1.
  set (NL := Z.of_nat (3 - nr) * PRH_FnPj.LIVE_pj_parse (bi_x D)) in *. lia. }
(* ---- the text's premises ---- *)
assert (HPREX : afn_pre_x SEGS B ARx STK_parse_noting ly S Hp W regs mem md ch1).
{ apply (YCbqGwild.afn_pre_x_at_wR (SK := SK) SEGS B prh_pst ARx WLE' STK_check_no_overread (cnb_sp0 D) []
    (bi_ly D) (bi_S D) (bi_Hp D) (bi_W D) (bi_mem D) (bi_md D) [(CNB_CID, bi_fpos D)] ly S Hp W mem md k WS0 regs
    STK_parse_noting (cnb_S1 D - cnb_sp0 D) ch1 HJW).
  - lia.
  - exact Ho16.
  - lia.
  - lia.
  - lia.
  - rewrite Hra1. exact Hrok.
  - rewrite Hraz. lia.
  - rewrite HG3. exact Hgp0.
  - rewrite HG4. exact Htp0.
  - rewrite Hsp, Hs0. exact Hch1. }
assert (HFPRE : fpre (fx := fxk) B ARx STK_parse_noting ly S Hp W regs mem md ch1).
{ split; [exact HPREX|]. split; [exact HRO|]. split; [rewrite Hsp, Eshi; lia|].
  split; [rewrite Hraz; exact HretC | exact HFZ]. }
assert (Hhome : PRH_FnReader.prhReader_home B ly S Hp Lam r (cnb_size D)).
{ right. exists r, (cnb_size D + 16). split; [exact Hrb|]. split; [exact HrHp|]. lia. }
assert (Hmr : Z.of_nat (PjRoundTrip.maxrun (bi_x D)) < 2 ^ 30).
{ pose proof (PjRoundTrip.G12_1 (bi_x D)). unfold cnb_size in Hsz. lia. }
assert (Hout : ck_out_ok B STK_parse_noting ly S W regs mem d 56).
{ split.
  - exists CNB_CID, (bi_fpos D). split; [exact Hin3|]. rewrite EFa, Efb. lia.
  - split; [lia|]. split; [lia|].
    split; [unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd; lia|].
    split; [|split; [exact (proj1 Hdop) | intros _; exact (proj2 Hdop)]].
    intros a Ha. destruct (HFb a ltac:(lia)) as (Hpr & Hno).
    split; [exact (apresent_writable SEGS _ _ _ Hpr)|]. split; [exact Hno|]. rewrite Hsp, ES2. lia. }
assert (Hfrl : Z.of_nat (length (frames S)) <= ck_FRAMES_CAP - FR_parse_noting).
{ rewrite (proj1 HFRM). cbn [length]. unfold FR_check_no_overread in HFR0. lia. }
assert (Hcntb : cnt + 2 * cnb_size D + 2 < 2 ^ 64 - 1) by (unfold cnb_size in *; lia).
(* THE WILD ROOM of the call: the entry room less the budget spent so far (the kit's cnb_roomR at wle') *)
pose proof (cnb_roomR B ARx WLE' CTX0 D wk ly S Hp W mem md k HPRE HJ Hwk) as HWR.
(* THE HULL BUDGET of the call (the text's last premise): the head of the budget the caller passes, the reading's
   all-granted events *)
pose proof (HPN fxk (bi_most D) 0 ly S Hp W regs mem md ch1 r
  (bi_x D) d Lam peak cnt SIZE_MAXZ 0 HFPRE (PM mem HP) HCL H10 H11 H12 ltac:(unfold cnb_size in Hsz; lia)
  ltac:(lia) ltac:(lia) HrSRC Hhome Hmr (cnbp_mod8 d (proj2 (proj2 Hdd))) Hout eq_refl HLED
  ltac:(unfold cnb_size in Hcntb; exact Hcntb) Hlv1 HRQ HRQ0 Hfrl HFZ HROOM HWR HPKS HPK24
  (PresetHullBudget.hull_budget_infix S S [] (PresetReqAt.parse_evs ReaderRes.jr_strtod (bi_x D) []) HrL HHB
     (PresetHullBudget.hull_used_refl S []))) as HT.
(* the text's inner post IS the kit's named tpnP_Q (PRH_FnCheck.v tpnP_Q_check); it is read below through tpnP_R_of *)
lazymatch type of HT with context [SRr' _ _ _ _ (?FPOST ?QPOST)] =>
  change QPOST with (tpnP_Q B (bi_most D) 0 ly S r (bi_x D) d Lam peak cnt SIZE_MAXZ (Z.of_nat (length (bi_x D))))
    in HT
end.
(* fpostFbm / fpostFb are the budgeted post at wle' SEGS RZ_cf: the engine's apost_base_xbFR there *)
unfold fpostFbm, fpostFb in HT.
(* ---- the call ---- *)
eapply (SRr'_mono SEGS YGcfRehidePost.RZ_cf);
  [exact (cnbp_call_x W fxk regs mem md D wk ly S Hp k d _ HJ Hsp ltac:(rewrite EFa; lia)
     ltac:(rewrite EFa, Efb; lia) HT)|].
cbv beta. intros W2 c2 _ (fx' & ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & WS1 & Hc2 & HFZ' & HFK' & HJ2 & HJ1 & HP2 &
  HQ).
(* the text's inner post, through the kit's named projections (PRH_FnCheck.v tpnP_R_of; the arms by tpnP_RSome_of /
   tpnP_RNone_of below) *)
destruct HQ as (HQ & Hmn).
destruct (tpnP_R_of HQ) as (Lam2 & peak2 & cnt2 & fail2 & ran2 & ok & res & tr & HQR).
pose proof (tpnP_hull HQR) as HHU. pose proof (tpnP_room HQR) as HROOM2. pose proof (tpnP_run HQR) as Hrun.
pose proof (tpnP_live HQR) as HLV2. pose proof (tpnP_pos HQR) as HPS2. pose proof (tpnP_oks HQR) as Hoks.
pose proof (tpnP_cnt HQR) as Hcnt2. pose proof (tpnP_fail HQR) as Hfa. pose proof (tpnP_peak HQR) as Hpk2.
pose proof (tpnP_ledger HQR) as HLED2. pose proof (tpnP_arm HQR) as Hres.
(* ---- what the callee's journal keeps ---- *)
pose proof (ajxR_ar HJ1) as HAR2. pose proof (ajxR_ly HJ1) as Hly1. pose proof (ajxR_frs HJ1) as Hfrs1.
pose proof (ajxR_hi HJ1) as G1. pose proof (ajxR_blk HJ1) as G2. pose proof (ajxR_img HJ1) as G3.
pose proof (ajxR_frm HJ1) as G4.
pose proof Hly1 as (_ & _ & _ & _ & _ & EF1 & _).
rewrite ES2 in G1.
assert (Hin3' : In (CNB_CID, bi_fpos D) (frames S2)) by (rewrite Hfrs1; exact Hin3).
assert (EFa2 : frame_addr ly2 CNB_CID (bi_fpos D) = cnb_F D)
  by (rewrite <- EFa; unfold frame_addr; rewrite EF1; reflexivity).
destruct (alx_frames SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 CNB_CID (bi_fpos D) HAR2 Hin3') as (_ & _ & HFb2 & HFs2).
rewrite EFa2, Efb in HFb2, HFs2.
assert (HnFP : forall a, inFP [(d, d + 56)] a -> d <= a < d + 56)
  by (intros a (rr & Hin & Hrr'); destruct Hin as [<-|[]]; cbn [fst snd] in Hrr'; exact Hrr').
assert (KFR : forall a, cnb_F D <= a < cnb_F D + 512 -> ~ (d <= a < d + 56) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha Hna. apply (G4 CNB_CID (bi_fpos D) a Hin3).
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFa, Efb. lia.
  - intros Hf. exact (Hna (HnFP a Hf)). }
assert (KSH : forall a, shadow_addr (cnb_F D) <= a < shadow_addr (cnb_F D) + 64 ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha. apply (G4 CNB_CID (bi_fpos D) a Hin3).
  - right. unfold in_zr. cbn [fst snd]. rewrite EFa, Efb. change (512 / 8) with 64. lia.
  - intros Hf. apply HnFP in Hf. unfold shadow_addr, SHADOW_OFF in Ha.
    pose proof (Z.div_mod (cnb_F D) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (cnb_F D) 8 ltac:(lia)). lia. }
assert (KST : forall a, cnb_S1 D <= a < cnb_sp0 D -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a)
  by (intros a Ha; apply G1; lia).
assert (KBL : forall p n i, In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly2 S2) -> 0 <= i < req_size n ->
  aview SEGS (w_H W2) mem2 (p + i) = aview SEGS (w_H W) mem (p + i)).
{ intros p n i H1 H2 Hi. apply (G2 p n i H1 H2 Hi). intros Hf. apply HnFP in Hf.
  apply (frame_not_block_x SEGS B ARx LAWS ly S Hp W mem md (CNB_CID, bi_fpos D) p n (p + i) HAR Hin3 H1); [|lia].
  unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFa, Efb. lia. }
(* an image byte that is read-only, not runtime-owned and not errno's is kept (the image clause; PST is writable) *)
assert (KI : forall a, in_roP SEGS (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) a ->
  ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Hro Hown Herr. apply G3.
  + destruct Hro as [(sg & Hsg & _ & Hb) | Hrel]; [exists sg; split; [exact Hsg | exact Hb] | exact (pa_relro_img a Hrel)].
  + exact Hown.
  + exact Herr.
  + intros Hpst. exact (cnbi_pst_rw B IMG a Hpst Hro).
  + apply fp_spares_closed. intros (rr & Hin & Hrr'). destruct Hin as [<-|[]]. cbn [fst snd] in Hrr'. lia. }
(* ---- the reading: fail stays SIZE_MAX, its calls at most the grammar's ---- *)
assert (Hfail2 : fail2 = SIZE_MAXZ).
{ destruct Hfa as [Fa1 Fa2]. unfold SIZE_MAXZ in *.
  destruct (Z_lt_le_dec (2 ^ 64 - 1) (cnt + Z.of_nat (PjGrammar.calls tr))) as [Hl|Hl].
  - apply Fa1. pose proof (prh_ledger_bounds B ly S Hp W mem Lam peak cnt (2 ^ 64 - 1) 0 (bi_most D) 0 HLED). lia.
  - apply Fa2. lia. }
rewrite Hfail2 in HLED2.
pose proof (cnbp_calls_le (bi_x D) ok res tr Hrun) as Hcl.
(* ---- THE GRANT: the model's okof og of the instance's outcomes ok (no premise: a refusal ends the reading) ---- *)
destruct (cnbp_grant ReaderRes.jr_strtod (bi_x D) ok) as (og & Ejr & Epe & Efr & Hgr).
rewrite Hrun in Hgr. cbn [snd] in Hgr.
(* g_ran_out = 1 exactly when og runs out: a refusal inside the reading is of a request at most RQ_pj_parse x, so at
   most g_most (cnb_pre), so it sets g_ran_out (prh_oks's third clause) *)
assert (Hran2 : ran2 = (if cnb_ro D og then 1 else 0)).
{ unfold cnb_ro. destruct Hoks as (_ & Ho2 & Ho3).
  pose proof (PjGrammar.G7_4 ReaderRes.jr_strtod (bi_x D) ok) as H74. rewrite Hrun in H74. cbn [snd] in H74.
  destruct Hgr as [(-> & Hall) | (-> & i & Hi & Hfi)].
  - destruct Ho2 as [E0 | (_ & i & Hi & Hfi & _)]; [exact E0|]. unfold prh_refused in Hfi.
    rewrite (Hall i Hi) in Hfi. cbn [negb andb] in Hfi. discriminate Hfi.
  - apply (Ho3 i Hi).
    + unfold prh_refused. rewrite Hfi. cbn [negb andb]. apply negb_true_iff. apply Z.eqb_neq.
      unfold SIZE_MAXZ, cnb_size in *. lia.
    + pose proof (cnbp_ev_reqs_le ReaderRes.jr_strtod (bi_x D) ok i) as Hq. rewrite Hrun in Hq. cbn [snd] in Hq.
      unfold PRH_FnPj.RQ_pj_parse, prhPj_ptrace in HRQ0. change prh_jr_strtod with ReaderRes.jr_strtod in HRQ0. lia. }
assert (HR2 : exists rcv st, getr regs2 10 = w64 rcv /\ Permutation Lam2 (cnb_Dof st ++ Lam) /\
  Permutation (ablocks B ly2 S2) (ablocks B ly S ++ ck_hblks (cnb_Dof st)) /\
  (forall a kk, In (a, kk) (cnb_Dof st) -> ~ In (a - cf_head, kk + cf_head) (ablocks B ly S)) /\
  cnb_doc W2 mem2 Lam2 d st /\ bsum (ck_hblks (cnb_Dof st)) <= PRH_FnPj.LIVE_pj_parse (bi_x D) /\
  cnb_res D ran2 rcv st /\ cnb_rd D og st /\ cnb_fo D W2 mem2 Lam2 og d st).
{ destruct res as [t|].
  - destruct (tpnP_RSome_of Hres) as (D0 & HRS).
    destruct (cnbp_read_some (bi_x D) ok t tr Hrun) as (Hjr & Etr).
    exists 0, (Some (t, D0)). cbn [cnb_Dof].
    split; [exact (tpnPs_ret HRS)|]. split; [exact (tpnPs_lam HRS)|]. split; [exact (tpnPs_ablocks HRS)|].
    split; [exact (tpnPs_fresh HRS)|].
    split; [split; [exact (tpnPs_node HRS) | exact (PjGrammar.json_read_depth _ _ _ Hjr)]|].
    split.
    + rewrite cnbp_bsum_hblks, (ReaderRes.lsz_counts D0 tr (tpnPs_sizes HRS) (tpnPs_nlive HRS)), (tpnPs_nlive HRS).
      pose proof (cnbp_held_le_hpeak tr). pose proof (cnbp_nlive_le_calls tr). pose proof (cnbp_hpeak_nonneg tr).
      assert (cf_head * ReaderRes.nlive tr <= cf_head * Z.of_nat (PjGrammar.calls tr)) by (apply Z.mul_le_mono_nonneg_l; lia).
      unfold PRH_FnPj.LIVE_pj_parse, prhPj_ptrace. change prh_jr_strtod with ReaderRes.jr_strtod. rewrite <- Etr. lia.
    + split; [intros _; unfold ck_read; rewrite Hjr; split; [reflexivity | exists D0; reflexivity]|].
      split; [unfold cnb_rd; rewrite Ejr, Hrun; reflexivity|].
      (* THE FREE ORDER of the new tree: the text's, at the instance's outcomes ok, is the model's at og *)
      unfold cnb_fo. intros Hh n Hn. destruct (tpnPs_freeord HRS Hh Hn) as (Fo & HFo & EFo). exists Fo.
      split; [exact HFo|].
      rewrite EFo. symmetry. exact Efr.
  - pose proof (tpnP_RNone_of Hres) as HRN.
    exists (-1), None. cbn [cnb_Dof cnb_doc]. unfold ck_hblks. cbn [map].
    split; [exact (tpnPn_ret HRN)|]. split; [exact (tpnPn_lam HRN)|].
    split; [rewrite app_nil_r; exact (tpnPn_ablocks HRN)|]. split; [intros a kk []|].
    split; [exact (tpnPn_zero HRN)|]. split; [cbn; exact HLV0|].
    split; [|split; [unfold cnb_rd; rewrite Ejr, Hrun; reflexivity | exact I]].
    intros Hran0. rewrite <- (tpnP_granted_read HQR Hran0); [split; reflexivity|].
    right. unfold SIZE_MAXZ. lia. }
destruct HR2 as (rcv & st & H10' & HSTL2 & HSTAB2 & HSTfr & HSTdoc & HSTbs & HSTres & HSTrd & HSTfo).
(* ---- the copies ---- *)
assert (HCP : forall r0, cnb_copy B D ly S Hp W mem r0 -> cnb_copy B D ly2 S2 Hp2 W2 mem2 r0).
{ intros r0 [->|(Hb & Hnh & Hsrc)]; [left; reflexivity|]. right.
  assert (Hb2 : In (r0, cnb_size D + 16) (ablocks B ly2 S2))
    by (apply (Permutation_in _ (Permutation_sym HSTAB2)); apply in_or_app; left; exact Hb).
  assert (Hrq : req_size (cnb_size D + 16) = cnb_size D + 16)
    by (unfold req_size; destruct (Z.eqb_spec (cnb_size D + 16) 0); lia).
  assert (Hnoh : forall h, In h Hp2 -> ~ (r0 <= h < r0 + req_size (cnb_size D + 16))).
  { intros h Hh Hhr.
    pose proof (prh_ledger_heads B ly2 S2 Hp2 W2 mem2 Lam2 peak2 cnt2 SIZE_MAXZ ran2 (bi_most D) 0 HLED2) as Hheads.
    apply (Permutation_in _ Hheads) in Hh. apply in_map_iff in Hh as ([a kk] & Eh & Hak). cbn [fst] in Eh.
    pose proof (prh_ledger_blocks B ly2 S2 Hp2 W2 mem2 Lam2 peak2 cnt2 SIZE_MAXZ ran2 (bi_most D) 0 HLED2) as HBL.
    rewrite Forall_forall in HBL. destruct (HBL _ Hak) as (Hk0 & Hab2 & _). cbn [fst snd] in Hk0, Hab2.
    destruct (req_size_pos (kk + cf_head) (Z.add_nonneg_nonneg _ _ Hk0 Hh0)) as (Hq1 & _).
    destruct (Z.eq_dec (a - cf_head) r0) as [Ea|Ea];
      [destruct (Z.eq_dec (kk + cf_head) (cnb_size D + 16)) as [Ek|Ek]|].
    - (* the same block: a new tree block is fresh, an old one's head is in Hp *)
      apply (Permutation_in _ HSTL2) in Hak. apply in_app_or in Hak as [Hak|Hak].
      + apply (HSTfr a kk Hak). rewrite Ea, Ek. exact Hb.
      + apply Hnh. pose proof (prh_ledger_heads B ly S Hp W mem Lam peak cnt SIZE_MAXZ 0 (bi_most D) 0 HLED) as Hh1.
        apply (Permutation_in _ (Permutation_sym Hh1)). apply in_map_iff. exists (a, kk). split; [exact Ea | exact Hak].
    - pose proof (sep_blocks_x SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 (a - cf_head) (kk + cf_head) r0 (cnb_size D + 16)
        HAR2 Hab2 Hb2 ltac:(intros Eq; injection Eq as _ E2; exact (Ek E2))) as Hz.
      unfold zdisjoint in Hz. cbn [fst snd] in Hz. rewrite Hrq in Hz, Hhr. lia.
    - pose proof (sep_blocks_x SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 (a - cf_head) (kk + cf_head) r0 (cnb_size D + 16)
        HAR2 Hab2 Hb2 ltac:(intros Eq; injection Eq as E1 _; exact (Ea E1))) as Hz.
      unfold zdisjoint in Hz. cbn [fst snd] in Hz. rewrite Hrq in Hz, Hhr. lia. }
  split; [exact Hb2|]. split; [intros Hh; apply (Hnoh r0 Hh); rewrite Hrq; lia|].
  destruct Hsrc as (Hby & H4 & Hc & Ham & Hra & Hhv).
  destruct (alx_shadow SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 r0 (cnb_size D + 16) HAR2 Hb2 Hnoh) as (Hbs & Hhv2).
  split; [|split; [exact H4|split; [exact Hc|split; [exact Ham|split]]]].
  - unfold bytes_at in *. apply (garr8R_frame SEGS (rdW W mem) (rdW W2 mem2) r0 (bi_x D) Hby).
    intros a Ha. apply (mbyte_of_aview SEGS). replace a with (r0 + (a - r0)) by lia.
    apply (KBL r0 (cnb_size D + 16) (a - r0) Hb Hb2). rewrite Hrq. unfold cnb_size. lia.
  - exact (cnbp_bshadow_ra _ r0 (cnb_size D) Hsz0 Hbs).
  - intros Hpos. apply (ro_hull_mono _ r0 (req_size (cnb_size D + 16))); [rewrite Hrq; unfold cnb_size in *; lia | exact Hhv2]. }
(* ---- the input's bytes (cnb_pre's home of the text: a harness block of the entry ledger, a read-only image range,
   or an allocator block of the entry; each a block live before and after, or an image byte, that the call keeps) ---- *)
assert (KX : forall x, bi_data D <= x < bi_data D + cnb_size D ->
  aview SEGS (w_H W2) mem2 x = aview SEGS (w_H W) mem x).
{ intros x Hx.
  assert (HE : forall b, In b (ablocks B (bi_ly D) (bi_S D)) -> In b (ablocks B ly S))
    by (intros b Hb; apply (Permutation_in _ (Permutation_sym HPB)); apply in_or_app; right; apply in_or_app; right;
        exact Hb).
  assert (HE2 : forall b, In b (ablocks B ly S) -> In b (ablocks B ly2 S2))
    by (intros b Hb; apply (Permutation_in _ (Permutation_sym HSTAB2)); apply in_or_app; left; exact Hb).
  destruct (HHOME0 ltac:(lia)) as [[(b & m & Hin & Hb & Hm) | [(_ & _ & _ & Hro) | (_ & _ & Hro)]]
    | (b & m & Hin & Hnh & Hb & Hm)].
  - pose proof (proj1 (Forall_forall _ _) (prh_ledger_blocks B (bi_ly D) (bi_S D) (bi_Hp D) (bi_W D) (bi_mem D)
      (bi_Lam D) (bi_peak D) (bi_cnt D) SIZE_MAXZ (bi_ran D) (bi_most D) 0 HLED0) (b, m) Hin) as (Hm0 & Hab & _).
    cbn [fst snd] in Hm0, Hab.
    pose proof (req_size_pos (m + @cf_head cp) ltac:(lia)) as (_ & Hq2).
    replace x with ((b - cf_head) + (x - b + cf_head)) by lia. apply (KBL _ _ _ (HE _ Hab) (HE2 _ (HE _ Hab))). lia.
  - destruct (Hro x ltac:(lia)) as (Hrop & Hown & Herr). exact (KI x Hrop Hown Herr).
  - destruct (Hro x ltac:(lia)) as (Hrop & Hown & Herr & _). exact (KI x Hrop Hown Herr).
  - pose proof (req_size_pos m ltac:(lia)) as (_ & Hq2).
    replace x with (b + (x - b)) by lia. apply (KBL _ _ _ (HE _ Hin) (HE2 _ (HE _ Hin))). lia. }
(* ---- the structs: open, and the trees of the other two kept ---- *)
assert (HOPEN : forall c, 32 <= c <= 224 -> c mod 8 = 0 -> cnb_open W mem (cnb_F D + c) -> cnb_open W2 mem2 (cnb_F D + c)).
{ intros c Hc Hc8 Ho. exact (cnb_open_keep _ _ (cnb_F D) c HF32 ltac:(lia) Hc Hc8 KSH Ho). }
(* a tree of another struct (its root in the frame away from d, its blocks Lam blocks): the call keeps its footprint *)
assert (HAGR : forall d0 D1, cnb_F D + 32 <= d0 -> d0 + 56 <= cnb_F D + 280 -> (d0 + 56 <= d \/ d + 56 <= d0) ->
  incl D1 Lam -> pj_agreeR SEGS (rdW W mem) (rdW W2 mem2) (pj_footR d0 D1)).
{ intros d0 D1 Hd01 Hd02 Hdis Hinc x Hx.
  destruct Hx as [Hx|((a & kk) & Hbk & Hx)].
  + split; [apply (mbyte_of_aview SEGS); apply KFR; lia|].
    intros _. apply (apresent_writable SEGS). exact (proj1 (HFb2 x ltac:(lia))).
  + unfold pj_holdsR in Hx. cbn [fst snd] in Hx.
    pose proof (Hinc _ Hbk) as HbL.
    pose proof (prh_ledger_blocks B ly S Hp W mem Lam peak cnt SIZE_MAXZ 0 (bi_most D) 0 HLED) as HB1.
    rewrite Forall_forall in HB1. destruct (HB1 _ HbL) as (Hk0 & Hab1 & _). cbn [fst snd] in Hk0, Hab1.
    assert (HbL2 : In (a, kk) Lam2) by (apply (Permutation_in _ (Permutation_sym HSTL2)); apply in_or_app; right; exact HbL).
    pose proof (prh_ledger_blocks B ly2 S2 Hp2 W2 mem2 Lam2 peak2 cnt2 SIZE_MAXZ ran2 (bi_most D) 0 HLED2) as HB2.
    rewrite Forall_forall in HB2. destruct (HB2 _ HbL2) as (_ & Hab2 & _). cbn [fst snd] in Hab2.
    destruct (req_size_pos (kk + cf_head) (Z.add_nonneg_nonneg _ _ Hk0 Hh0)) as (_ & Hq2).
    split.
    * apply (mbyte_of_aview SEGS). replace x with ((a - cf_head) + (x - (a - cf_head))) by lia.
      apply (KBL _ _ _ Hab1 Hab2). lia.
    * intros _. apply (apresent_writable SEGS).
      destruct (alx_blocks SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 (a - cf_head) (kk + cf_head) HAR2 Hab2)
        as (_ & _ & _ & _ & Hpr2 & _).
      exact (proj1 (Hpr2 x ltac:(lia))). }
assert (HLIN : forall D1, incl D1 Lam -> forall b, In b D1 -> In b Lam2).
{ intros D1 Hinc b Hb. apply (Permutation_in _ (Permutation_sym HSTL2)). apply in_or_app. right. exact (Hinc _ Hb). }
assert (HDOC : forall d0 st0, cnb_F D + 32 <= d0 -> d0 + 56 <= cnb_F D + 280 -> (d0 + 56 <= d \/ d + 56 <= d0) ->
  incl (cnb_Dof st0) Lam -> cnb_doc W mem Lam d0 st0 -> cnb_doc W2 mem2 Lam2 d0 st0).
{ intros d0 st0 Hd01 Hd02 Hdis Hinc Hdoc. destruct st0 as [[t0 D1]|]; cbn [cnb_doc cnb_Dof] in *.
  - destruct Hdoc as (Hn & Hdep). split; [|exact Hdep].
    apply (cnbp_nodeR_lblk SEGS t0 _ (prh_lin Lam));
      [|intros a kk Hak; unfold prh_lin in *; apply (Permutation_in _ (Permutation_sym HSTL2)); apply in_or_app; right; exact Hak].
    exact (pj_nodeR_frame SEGS t0 (rdW W mem) (rdW W2 mem2) (prh_lin Lam) d0 D1 Hn (HAGR d0 D1 Hd01 Hd02 Hdis Hinc)).
  - apply (pj_zeroR_frame SEGS (rdW W mem) (rdW W2 mem2) d0 Hdoc). intros x Hx. apply (mbyte_of_aview SEGS).
    apply KFR; lia. }
(* THE FREE ORDER of a tree of another struct, kept (the kit's cnb_fo_keep, PRH_PjOrder.pj_foR_frame over the same
   footprint) *)
assert (HFOK : forall o d0 st0, cnb_F D + 32 <= d0 -> d0 + 56 <= cnb_F D + 280 -> (d0 + 56 <= d \/ d + 56 <= d0) ->
  incl (cnb_Dof st0) Lam -> cnb_fo D W mem Lam o d0 st0 -> cnb_fo D W2 mem2 Lam2 o d0 st0).
{ intros o d0 st0 Hd01 Hd02 Hdis Hinc Hfo.
  exact (cnb_fo_keep D W mem Lam W2 mem2 Lam2 o d0 st0 Hfo (HAGR d0 (cnb_Dof st0) Hd01 Hd02 Hdis Hinc)
    (HLIN (cnb_Dof st0) Hinc)). }
(* ---- THE EXIT ---- *)
pose proof (HU st) as (HUp & HU1 & HU2 & HU3).
assert (Hd123 : cnb_d1 D = cnb_F D + 32 /\ cnb_d2 D = cnb_F D + 128 /\ cnb_d3 D = cnb_F D + 224)
  by (unfold cnb_d1, cnb_d2, cnb_d3; lia).
assert (HinL : forall x, In x (cnb_Dof st1 ++ cnb_Dof st2 ++ cnb_Dof st3) -> In x Lam)
  by (intros x Hx; apply (Permutation_in _ (Permutation_sym HPL)); rewrite !app_assoc in *; apply in_or_app; left; exact Hx).
exists fx', ly2, S2, Hp2, regs2, mem2, md2, (k + k1), Lam2, peak2, cnt2, ran2, rcv, st, og.
split; [rewrite Hc2; unfold cnb_cfg; rewrite Hra1; reflexivity|].
split.
{ (* cnb_baseR at wle' *)
  split; [exact HFZ'|]. split; [intros rr Hr8; rewrite (HFK' rr Hr8); exact (HFK rr Hr8)|].
  split; [exact HJ2|].
  split.
  { destruct HFRM as (Ef & Hni & Hflag & Hp1 & Hp2').
    split; [rewrite Hfrs1; exact Ef|]. split; [exact Hni|].
    split; [|split].
    - assert (Efl : flag_addr ly2 CNB_CID (bi_fpos D) = flag_addr ly CNB_CID (bi_fpos D))
        by (unfold flag_addr; rewrite EF1; reflexivity).
      rewrite Efl, <- Hflag, Efb.
      apply (ro_rdword_kept _ _ (cnb_F D + 504) (cnb_F D + 512)); [intros a Ha; apply KFR; lia | lia | lia].
    - intros a Ha. rewrite Efb in Ha. exact (proj1 (HFb2 a Ha)).
    - intros a Ha. rewrite Efb in Ha. change (512 / 8) with 64 in Ha.
      replace a with (shadow_addr (cnb_F D) + (a - shadow_addr (cnb_F D))) by lia.
      apply (proj1 (HFs2 (a - shadow_addr (cnb_F D)) ltac:(change (512 / 8) with 64; lia))). }
  split.
  { unfold cnb_saved in *. apply Forall_forall. intros [o rr] Hin.
    pose proof (proj1 (Forall_forall _ _) HSAV (o, rr) Hin) as Hv. cbn [fst snd] in Hv |- *.
    assert (Ho : 56 <= o <= 152)
      by (cbn in Hin; repeat destruct Hin as [Hin|Hin]; try (injection Hin as <- _; lia); destruct Hin).
    rewrite <- Hv. apply (ro_rdword_kept _ _ (cnb_S1 D) (cnb_sp0 D)); [exact KST | lia | lia]. }
  split; [exact (eq_trans (HP2 3 ltac:(unfold acallee_saved; lia)) HG3)|].
  split; [exact (eq_trans (HP2 4 ltac:(unfold acallee_saved; lia)) HG4)|].
  intros a Hro Hown Herr. rewrite <- (HRO a Hro Hown Herr). exact (KI a Hro Hown Herr). }
split; [exact HP2|]. split; [exact H10'|].
split; [exact KST|].
split.
{ (* the events: this reading's under the grant og, the text's exact live set and position *)
  apply (cnb_prog_app D E (cnb_pe D og) S S2 HPROG).
  - unfold cnb_pe. rewrite Epe. exact HLV2.
  - unfold cnb_pe. rewrite Epe. exact HPS2. }
split; [exact Hran2|].
split.
{ (* cnb_mid *)
  split; [exact (HCP r1 HC1)|]. split; [exact (HCP r2 HC2)|]. split; [exact (HCP r3 HC3)|].
  split; [exact HLED2|].
  split; [rewrite Hpk2; clear - HPK; lia|].
  split.
  { rewrite Hcnt2. unfold ck_ncalls in *. rewrite Nat2Z.inj_succ, Z.mul_succ_l.
    set (NN := Z.of_nat nr * Z.of_nat (PjGrammar.ncalls ReaderRes.jr_strtod (bi_x D))) in *. lia. }
  split; [exact HROOM2|].
  split.
  { rewrite (blocks_bytes_bsum B ly2 S2), (bsum_perm _ _ HSTAB2), bsum_app, <- (blocks_bytes_bsum B ly S).
    assert (E3 : Z.of_nat (3 - Datatypes.S nr) = Z.of_nat (3 - nr) - 1) by lia. rewrite E3, Z.mul_sub_distr_r, Z.mul_1_l.
    set (NL := Z.of_nat (3 - nr) * PRH_FnPj.LIVE_pj_parse (bi_x D)) in *. lia. }
  split; [exact (HOPEN 32 ltac:(lia) eq_refl HO1)|].
  split; [exact (HOPEN 128 ltac:(lia) eq_refl HO2)|].
  split; [exact (HOPEN 224 ltac:(lia) eq_refl HO3)|].
  split.
  { destruct (Z.eqb d (cnb_d1 D)) eqn:E1b in HU1.
    - apply Z.eqb_eq in E1b. destruct HU1 as (_ & ->). rewrite <- E1b. exact HSTdoc.
    - apply Z.eqb_neq in E1b. rewrite HU1.
      apply HDOC; [lia | lia | lia | intros x Hx; apply HinL; apply in_or_app; left; exact Hx | exact HD1]. }
  split.
  { destruct (Z.eqb d (cnb_d2 D)) eqn:E1b in HU2.
    - apply Z.eqb_eq in E1b. destruct HU2 as (_ & ->). rewrite <- E1b. exact HSTdoc.
    - apply Z.eqb_neq in E1b. rewrite HU2.
      apply HDOC; [lia | lia | lia | intros x Hx; apply HinL; apply in_or_app; right; apply in_or_app; left; exact Hx | exact HD2]. }
  split.
  { destruct (Z.eqb d (cnb_d3 D)) eqn:E1b in HU3.
    - apply Z.eqb_eq in E1b. destruct HU3 as (_ & ->). rewrite <- E1b. exact HSTdoc.
    - apply Z.eqb_neq in E1b. rewrite HU3.
      apply HDOC; [lia | lia | lia | intros x Hx; apply HinL; apply in_or_app; right; apply in_or_app; right; exact Hx | exact HD3]. }
  split; [exact (cnbp_perm_lam _ _ _ _ _ _ _ _ _ _ HSTL2 HPL HUp)|].
  split; [exact (cnbp_perm_blocks _ _ _ _ _ _ _ _ _ _ _ HSTAB2 HPB HUp)|].
  split.
  { intros a kk Hak. apply (Permutation_in _ HUp) in Hak. apply in_app_or in Hak as [Hak|Hak].
    - intros Hab0. apply (HSTfr a kk Hak). apply (Permutation_in _ (Permutation_sym HPB)).
      apply in_or_app; right; apply in_or_app; right; exact Hab0.
    - exact (HFRESH a kk Hak). }
  unfold bytes_at in *. apply (garr8R_frame SEGS (rdW W mem) (rdW W2 mem2) (bi_data D) (bi_x D) HDATA).
  intros x Hx. apply (mbyte_of_aview SEGS). apply KX. unfold cnb_size. lia. }
split; [exact HSTres|]. split; [exact HSTrd|]. split; [exact HSTfo|].
split.
{ intros o d0 st0 Hd0 Hne Hinc Hfo. apply (HFOK o d0 st0); [| | |exact Hinc | exact Hfo];
    clear - Hd Hd0 Hne; unfold cnb_d1, cnb_d2, cnb_d3 in *; lia. }
split; [exact (PC mem mem2 Hmn HP)|].
(* the hull budget left for the next cut: the caller's budget less the reading's use *)
exact (PresetHullBudget.hull_budget_app S S2 (PresetReqAt.parse_evs ReaderRes.jr_strtod (bi_x D) []) HrL HHB HHU).
Qed.

(* THE GENERIC CALL STEP: at the `jal parse_noting` of a cut (a0 = r, a1 = size, a2 = d) whose events since entry are
   E, at the spent wild budget wk (wk + 2 <= 6), one reading of the copy r into the struct d; it ends at the return
   site off + 4 at the budget wk + 2 with the events E ++ the reading's under its grant og (cnbp_grant: og matches the
   instance's outcomes; no premise), g_ran_out = 1 exactly when og runs out, the struct against the model's reading at
   og (cnb_rd), its tree's free order at og (cnb_fo), and the free order of a tree of another struct kept. The call
   crosses a free: the base is at wle' SEGS RZ_cf on both sides and the step concludes SRr'. THE HULL: from a budget
   at S for the reading's all-granted events followed by Hr, the budget Hr at S' *)
Lemma cnb_pn_call : forall P, srr_inv_laws SEGS P -> srr_inv_call SEGS P -> srr_inv_mn SEGS P ->
  forall D fxk ly S Hp W regs mem md k (wk : nat) Lam peak cnt (nr : nat) r1 r2 r3 st1 st2 st3 r d off E
    (upd : cnb_st -> cnb_st * cnb_st * cnb_st) (Hr : list PresetReqAt.hev),
  (wk + prh_wk F_parse_noting <= prh_wk F_check_no_overread)%nat ->
  cnb_pre (fx := fx) B ARx CTX0 D ->
  cnb_baseR (fx := fx) B ARx WLE' D fxk ly S Hp W regs mem md k wk ->
  cnb_regsat regs (cnb_core D ++ [(10%bv, r); (11%bv, cnb_size D); (12%bv, d)]) ->
  plookup B_prog_tpi_cno (CNB_OFF + off) = Some (PCall AS_parse_noting 1%bv) -> 0 <= off < 2 ^ 28 ->
  4096 <= cnb_pc (off + 4) < YM05.alloc_ceiling -> YK0s.ret_ok (w64 (cnb_pc (off + 4))) ->
  (r = r1 \/ r = r2 \/ r = r3) -> r <> 0 ->
  (d = cnb_d1 D \/ d = cnb_d2 D \/ d = cnb_d3 D) ->
  (nr <= 2)%nat ->
  cnb_prog D E S ->
  (exists R, ck_cno_evs ReaderRes.jr_strtod (bi_x D) None None None = E ++ cnb_pe D None ++ R) ->
  cnb_mid B D ly S Hp W mem Lam peak cnt 0 0 nr r1 r2 r3 st1 st2 st3 ->
  (forall st, cnb_upd_ok D d st st1 st2 st3 (upd st)) ->
  P mem ->
  PresetHullBudget.hull_budget S (PresetReqAt.parse_evs ReaderRes.jr_strtod (bi_x D) [] ++ Hr) ->
  SRr' SEGS YGcfRehidePost.RZ_cf W (@cnb_cfg SEGS fxk (cnb_pc off) regs mem md) (fun W' c' =>
    exists fx' ly' S' Hp' regs' mem' md' k' Lam' peak' cnt' ran' rcv st og,
      c' = @cnb_cfg SEGS fx' (cnb_pc (off + 4)) regs' mem' md' /\
      cnb_baseR (fx := fx) B ARx WLE' D fx' ly' S' Hp' W' regs' mem' md' k' (wk + prh_wk F_parse_noting) /\
      aregs_preserved (regupd regs 1%bv (w64 (cnb_pc (off + 4)))) regs' /\ getr regs' 10 = w64 rcv /\
      (forall a, cnb_S1 D <= a < cnb_sp0 D -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) /\
      cnb_prog D (E ++ cnb_pe D og) S' /\ ran' = (if cnb_ro D og then 1 else 0) /\
      cnb_mid B D ly' S' Hp' W' mem' Lam' peak' cnt' ran' 0 (Datatypes.S nr) r1 r2 r3
        (fst (fst (upd st))) (snd (fst (upd st))) (snd (upd st)) /\
      cnb_res D ran' rcv st /\ cnb_rd D og st /\ cnb_fo D W' mem' Lam' og d st /\
      (forall o d0 st0, (d0 = cnb_d1 D \/ d0 = cnb_d2 D \/ d0 = cnb_d3 D) -> d0 <> d -> incl (cnb_Dof st0) Lam ->
         cnb_fo D W mem Lam o d0 st0 -> cnb_fo D W' mem' Lam' o d0 st0) /\
      P mem' /\ PresetHullBudget.hull_budget S' Hr).
Proof.
intros P PL PC PM D fxk ly S Hp W regs mem md k wk Lam peak cnt nr r1 r2 r3 st1 st2 st3 r d off E upd HrL
  Hwk HPRE HB HR Hpl Hoff (Hret0 & HretC) Hrok Hr Hr0 Hd Hnr HPROG HSPLIT HM HU HP HHB.
apply (cnb_hs_callR WLE' W fxk regs mem md _ off (off + 4) AS_parse_noting Hpl Hoff eq_refl).
intros X.
assert (HB1 : cnb_baseR (fx := fx) B ARx WLE' D fxk ly S Hp W (regupd regs 1%bv (w64 (cnb_pc (off + 4)))) mem
                (with_vm_backing (m_vm_lazy md) X md) k wk)
  by (apply (cnb_base_matR B ARx LAWS WLE' D fxk ly S Hp W regs _ mem md k wk X HB); ro_getr; reflexivity).
assert (HR1 : cnb_regsat (regupd regs 1%bv (w64 (cnb_pc (off + 4))))
                (cnb_core D ++ [(10%bv, r); (11%bv, cnb_size D); (12%bv, d)])).
{ apply (cnb_regsat_kept regs _ _ HR). unfold cnb_core. cbn [app].
  repeat (apply Forall_cons; [cbn [fst]; ro_getr; reflexivity|]). apply Forall_nil. }
assert (Hra1 : getr (regupd regs 1%bv (w64 (cnb_pc (off + 4)))) 1%bv = w64 (cnb_pc (off + 4))) by (ro_getr; reflexivity).
exact (cnbp_pn_entry P PL PC PM D fxk ly S Hp W _ mem _ k wk Lam peak cnt nr r1 r2 r3 st1 st2 st3 r d
  (cnb_pc (off + 4)) E upd HrL Hwk HPRE HB1 HR1 Hra1 Hrok Hret0 HretC Hr Hr0 Hd Hnr HPROG HSPLIT HM HU HP HHB).
Qed.

(* the readings' piece of check_no_overread's all-granted list, after the three granted copies *)
Lemma cnbp_cno_split : forall (D : cnb_in) r1 r2 r3, r1 <> 0 -> r2 <> 0 -> r3 <> 0 ->
  exists R, ck_cno_evs ReaderRes.jr_strtod (bi_x D) None None None =
    cnb_cevs D r1 r2 r3 ++ cnb_pe D None ++ cnb_pe D None ++ cnb_pe D None ++ R.
Proof.
intros D r1 r2 r3 H1 H2 H3. unfold cnb_cevs, cnb_cblks, cnb_cblk, cnb_pe, cnb_size.
rewrite (proj2 (Z.eqb_neq r1 0) H1), (proj2 (Z.eqb_neq r2 0) H2), (proj2 (Z.eqb_neq r3 0) H3).
eexists. reflexivity.
Qed.
(* a grant that does not run out gives the all-granted reading's events *)
Lemma cnbp_cnb_pe_none : forall (D : cnb_in) o, cnb_ro D o = false -> cnb_pe D o = cnb_pe D None.
Proof. intros D o H. exact (cnbp_pe_none ReaderRes.jr_strtod (bi_x D) o H). Qed.

(* ==== 4. the three steps ==== *)
(* THE HULL at each step: the cut's hull conjunct (pn1 at cnb_hrest_copies, pn2 at cnb_hrest_rd1, pn3 at
   cnb_hrest_rd2), rewritten by the Base's split lemma (cnb_hrest_rd1_split / rd2_split / rd0_split), is the
   reading's all-granted events followed by the next stage; cnb_pn_call pays the reading from it and gives the next
   stage at S', the exit cut's hull conjunct (read2 at rd1, read3 at rd2, cmp at rd0) *)
(* CNB_PN1 (632) -> CNB_READ2 (636): rc1 in a0; the first reading's struct is d1; the wild budget 0 -> 2; the hull
   stage copies -> rd1. The cut lies before any free (wle): its base is lifted into wle' before the crossing call *)
Lemma cnb_pn1_step : forall P, srr_inv_laws SEGS P -> srr_inv_call SEGS P -> srr_inv_mn SEGS P ->
  forall D fxk ly S Hp W regs mem md k r1 r2 r3,
  cnb_pre (fx := fx) B ARx CTX0 D -> cnb_at_pn1 (fx := fx) B ARx D fxk ly S Hp W regs mem md k r1 r2 r3 -> P mem ->
  SRr' SEGS YGcfRehidePost.RZ_cf W (@cnb_cfg SEGS fxk (cnb_pc CNB_PN1) regs mem md)
    (fun W' c' => cnb_ex_read2R (fx := fx) B ARx WLE' D W' c' /\ P (ms_mem (cfg_ms c'))).
Proof.
intros P HL HC HMN D fxk ly S Hp W regs mem md k r1 r2 r3 HPRE HAT HP.
destruct HAT as (HB & HR & HSL & Hr1 & Hr2 & Hr3 & EHp & HPROG & HM & HHB).
destruct (cnb_entry_facts B ARx CTX0 D HPRE) as (Hal16 & _).
destruct (cnb_pn_ret_ok CNB_PN1 (or_introl eq_refl)) as (Hpl & Hret & Hrok & Hoff).
destruct (cnb_dne D) as (E12 & E13 & _ & _ & _ & _).
assert (HU : forall st, cnb_upd_ok D (cnb_d1 D) st None None None (st, None, None)).
{ intros st. unfold cnb_upd_ok. cbn [fst snd cnb_Dof app]. rewrite (Z.eqb_refl (cnb_d1 D)), E12, E13. cbv beta iota.
  split; [rewrite !app_nil_r; apply Permutation_refl|]. repeat split. }
destruct (cnbp_cno_split D r1 r2 r3 Hr1 Hr2 Hr3) as (R0 & ER0).
assert (HRc : cnb_regsat regs (cnb_core D ++ [(10%bv, r1); (11%bv, cnb_size D); (12%bv, cnb_d1 D)]))
  by (apply (cnbp_regsat_incl regs _ _ HR); cnbp_incl).
assert (HRk : cnb_regsat regs (cnb_core D ++ [cnb_s8; (23%bv, cnb_size D); (25%bv, r1)]))
  by (apply (cnbp_regsat_incl regs _ _ HR); cnbp_incl).
(* the cut's base at wle (no free crossed since entry), lifted into wle' for the crossing call *)
pose proof (cnb_baseR_mono B ARx (@wle SEGS) WLE' (wle_wle' SEGS YGcfRehidePost.RZ_cf) D fxk ly S Hp W regs mem md k
  0%nat HB) as HBR.
(* the cut's hull budget: reading 1's all-granted events, then the rest after it *)
rewrite cnb_hrest_rd1_split in HHB.
eapply (SRr'_bind SEGS YGcfRehidePost.RZ_cf).
{ exact (cnb_pn_call P HL HC HMN D fxk ly S Hp W regs mem md k 0%nat (bi_Lam D) (bi_peak D) (bi_cnt D) 0%nat r1 r2 r3
    None None None r1 (cnb_d1 D) CNB_PN1 (cnb_cevs D r1 r2 r3) (fun st => (st, None, None)) (cnb_hrest_rd1 (bi_x D))
    ltac:(apply Nat.leb_le; reflexivity) HPRE HBR HRc Hpl Hoff
    Hret Hrok (or_introl eq_refl) Hr1 (or_introl eq_refl) ltac:(lia) HPROG
    (ex_intro _ (cnb_pe D None ++ cnb_pe D None ++ R0) ER0) HM HU HP HHB). }
intros W' c' _ (fx' & ly' & S' & Hp' & regs' & mem' & md' & k' & Lam' & peak' & cnt' & ran' & rcv & st & og & -> &
  HB' & HPR & H10 & KST & HPROG' & HRAN & HM' & HRES & HRD & HFO & _ & HPm & HHB').
assert (HK : cnb_regsat regs' (cnb_core D ++ [cnb_s8; (23%bv, cnb_size D); (25%bv, r1)])).
{ apply (cnbp_regsat_call regs regs' _ _ HRk HPR).
  unfold cnb_core, cnb_s8. cbn [map fst app]. reflexivity. }
apply (SRr'_ret SEGS YGcfRehidePost.RZ_cf). split; [|exact HPm].
exists fx', ly', S', Hp', regs', mem', md', k', Lam', peak', cnt', ran', r1, r2, r3, rcv, st, og.
split; [reflexivity|].
split; [exact HB'|].
split; [apply (cnbp_regsat_incl regs' ((10%bv, rcv) :: cnb_core D ++ [cnb_s8; (23%bv, cnb_size D); (25%bv, r1)]));
  [apply Forall_cons; [exact H10 | exact HK] | cnbp_incl]|].
split; [exact (cnb_slots_agree D W mem W' mem' r2 r3 Hal16 KST HSL)|].
split; [exact Hr1|]. split; [exact Hr2|]. split; [exact Hr3|]. split; [exact HPROG'|].
split; [rewrite HRAN; unfold cnb_ranz, ck_cno_ranout, cnb_ro;
  destruct (PresetRun.ranout ReaderRes.jr_strtod (bi_x D) og); reflexivity|].
split; [exact HM'|]. split; [exact HRES|]. split; [exact HRD|]. split; [exact HFO | exact HHB'].
Qed.

(* CNB_PN2 (676) -> CNB_READ3 (680): rc2 in a0, rc1 still at s1 + 8; the second reading's struct is d2; the wild
   budget 2 -> 4; reading 1's tree keeps its free order; the hull stage rd1 -> rd2; after a free (WLE') *)
Lemma cnb_pn2_step : forall P, srr_inv_laws SEGS P -> srr_inv_call SEGS P -> srr_inv_mn SEGS P ->
  forall D fxk ly S Hp W regs mem md k Lam peak cnt r1 r2 r3 rc1 st1 o1,
  cnb_pre (fx := fx) B ARx CTX0 D ->
  cnb_at_pn2R (fx := fx) B ARx WLE' D fxk ly S Hp W regs mem md k Lam peak cnt r1 r2 r3 rc1 st1 o1 -> P mem ->
  SRr' SEGS YGcfRehidePost.RZ_cf W (@cnb_cfg SEGS fxk (cnb_pc CNB_PN2) regs mem md)
    (fun W' c' => cnb_ex_read3R (fx := fx) B ARx WLE' D W' c' /\ P (ms_mem (cfg_ms c'))).
Proof.
intros P HL HC HMN D fxk ly S Hp W regs mem md k Lam peak cnt r1 r2 r3 rc1 st1 o1 HPRE HAT HP.
destruct HAT as (HB & HR & HSL & HRC1 & Hr1 & Hr2 & Hr3 & HPROG & HRO1 & HM & HRES1 & HRD1 & HFO1 & HHB).
destruct (cnb_entry_facts B ARx CTX0 D HPRE) as (Hal16 & _).
assert (Hinc1 : incl (cnb_Dof st1) Lam).
{ pose proof HM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPL & _).
  intros x Hx. apply (Permutation_in _ (Permutation_sym HPL)). apply in_or_app. left. exact Hx. }
destruct (cnb_pn_ret_ok CNB_PN2 (or_intror (or_introl eq_refl))) as (Hpl & Hret & Hrok & Hoff).
destruct (cnb_dne D) as (_ & _ & E21 & E23 & _ & _).
assert (HU : forall st, cnb_upd_ok D (cnb_d2 D) st st1 None None (st1, st, None)).
{ intros st. unfold cnb_upd_ok. cbn [fst snd cnb_Dof app]. rewrite E21, (Z.eqb_refl (cnb_d2 D)), E23. cbv beta iota.
  split; [rewrite !app_nil_r; apply Permutation_app_comm|]. repeat split. }
assert (HRc : cnb_regsat regs (cnb_core D ++ [(10%bv, r2); (11%bv, cnb_size D); (12%bv, cnb_d2 D)]))
  by (apply (cnbp_regsat_incl regs _ _ HR); cnbp_incl).
assert (HRk : cnb_regsat regs (cnb_core D ++ [cnb_s8; (23%bv, cnb_size D); (25%bv, r1)]))
  by (apply (cnbp_regsat_incl regs _ _ HR); cnbp_incl).
assert (HSP : exists R, ck_cno_evs ReaderRes.jr_strtod (bi_x D) None None None =
  (cnb_cevs D r1 r2 r3 ++ cnb_pe D o1) ++ cnb_pe D None ++ R).
{ destruct (cnbp_cno_split D r1 r2 r3 Hr1 Hr2 Hr3) as (R0 & ER0). exists (cnb_pe D None ++ R0).
  rewrite ER0, (cnbp_cnb_pe_none D o1 HRO1), <- !app_assoc. reflexivity. }
(* the cut's hull budget: reading 2's all-granted events, then the rest after it *)
rewrite cnb_hrest_rd2_split in HHB.
eapply (SRr'_bind SEGS YGcfRehidePost.RZ_cf).
{ exact (cnb_pn_call P HL HC HMN D fxk ly S Hp W regs mem md k 2%nat Lam peak cnt 1%nat r1 r2 r3
    st1 None None r2 (cnb_d2 D) CNB_PN2 (cnb_cevs D r1 r2 r3 ++ cnb_pe D o1) (fun st => (st1, st, None))
    (cnb_hrest_rd2 (bi_x D)) ltac:(apply Nat.leb_le; reflexivity) HPRE HB HRc
    Hpl Hoff Hret Hrok (or_intror (or_introl eq_refl)) Hr2 (or_intror (or_introl eq_refl)) ltac:(lia) HPROG HSP HM HU HP
    HHB). }
intros W' c' _ (fx' & ly' & S' & Hp' & regs' & mem' & md' & k' & Lam' & peak' & cnt' & ran' & rcv & st & og & -> &
  HB' & HPR & H10 & KST & HPROG' & HRAN & HM' & HRES & HRD & HFO & HKFO & HPm & HHB').
assert (HK : cnb_regsat regs' (cnb_core D ++ [cnb_s8; (23%bv, cnb_size D); (25%bv, r1)])).
{ apply (cnbp_regsat_call regs regs' _ _ HRk HPR).
  unfold cnb_core, cnb_s8. cbn [map fst app]. reflexivity. }
apply (SRr'_ret SEGS YGcfRehidePost.RZ_cf). split; [|exact HPm].
exists fx', ly', S', Hp', regs', mem', md', k', Lam', peak', cnt', ran', r1, r2, r3, rc1, rcv, st1, st, o1, og.
split; [reflexivity|].
split; [exact HB'|].
split; [apply (cnbp_regsat_incl regs' ((10%bv, rcv) :: cnb_core D ++ [cnb_s8; (23%bv, cnb_size D); (25%bv, r1)]));
  [apply Forall_cons; [exact H10 | exact HK] | cnbp_incl]|].
split; [exact (cnb_slots_agree D W mem W' mem' r2 r3 Hal16 KST HSL)|].
split; [exact (cnb_rcslot_agree D W mem W' mem' 8 rc1 Hal16 ltac:(lia) KST HRC1)|].
split; [exact Hr1|]. split; [exact Hr2|]. split; [exact Hr3|].
split; [apply (cnb_prog_eq D ((cnb_cevs D r1 r2 r3 ++ cnb_pe D o1) ++ cnb_pe D og));
  [unfold cnb_revs2; rewrite HRO1, <- app_assoc; reflexivity | exact HPROG']|].
split; [rewrite HRAN; unfold cnb_ranz, ck_cno_ranout; unfold cnb_ro in HRO1 |- *; rewrite HRO1;
  destruct (PresetRun.ranout ReaderRes.jr_strtod (bi_x D) og); reflexivity|].
split; [exact HM'|].
split; [intros _; exact (HRES1 eq_refl)|]. split; [exact HRES|].
split; [unfold cnb_rds2; rewrite HRO1; split; [exact HRD1 | exact HRD]|].
split; [|split; [exact HFO | exact HHB']].
apply (HKFO o1 (cnb_d1 D) st1 (or_introl eq_refl) ltac:(unfold cnb_d1, cnb_d2; lia) Hinc1 HFO1).
Qed.

(* CNB_PN3 (720) -> 724 `mv s7, a0` -> CNB_CMP (728): rc3 in s7, rc1 / rc2 at s1 + 8 / s1 + 0; the struct is d3; the
   wild budget 4 -> 6; readings 1 and 2's trees keep their free order; the hull stage rd2 -> rd0; after a free (WLE') *)
Lemma cnb_pn3_step : forall P, srr_inv_laws SEGS P -> srr_inv_call SEGS P -> srr_inv_mn SEGS P ->
  forall D fxk ly S Hp W regs mem md k Lam peak cnt r1 r2 r3 rc1 rc2 st1 st2 o1 o2,
  cnb_pre (fx := fx) B ARx CTX0 D ->
  cnb_at_pn3R (fx := fx) B ARx WLE' D fxk ly S Hp W regs mem md k Lam peak cnt r1 r2 r3 rc1 rc2 st1 st2 o1 o2 ->
  P mem ->
  SRr' SEGS YGcfRehidePost.RZ_cf W (@cnb_cfg SEGS fxk (cnb_pc CNB_PN3) regs mem md)
    (fun W' c' => cnb_ex_cmpR (fx := fx) B ARx WLE' D W' c' /\ P (ms_mem (cfg_ms c'))).
Proof.
intros P HL HC HMN D fxk ly S Hp W regs mem md k Lam peak cnt r1 r2 r3 rc1 rc2 st1 st2 o1 o2 HPRE HAT HP.
destruct HAT as (HB & HR & HSL & HRC1 & HRC2 & Hr1 & Hr2 & Hr3 & HPROG & HRO1 & HRO2 & HM & HRES1 & HRES2 & HRD1 & HRD2 &
  HFO1 & HFO2 & HHB).
destruct (cnb_entry_facts B ARx CTX0 D HPRE) as (Hal16 & _).
assert (Hinc12 : incl (cnb_Dof st1) Lam /\ incl (cnb_Dof st2) Lam).
{ pose proof HM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPL & _).
  split; intros x Hx; apply (Permutation_in _ (Permutation_sym HPL)); apply in_or_app;
    [left; exact Hx | right; apply in_or_app; left; exact Hx]. }
destruct (cnb_pn_ret_ok CNB_PN3 (or_intror (or_intror eq_refl))) as (Hpl & Hret & Hrok & Hoff).
destruct (cnb_dne D) as (_ & _ & _ & _ & E31 & E32).
assert (HU : forall st, cnb_upd_ok D (cnb_d3 D) st st1 st2 None (st1, st2, st)).
{ intros st. unfold cnb_upd_ok. cbn [fst snd cnb_Dof app]. rewrite E31, E32, (Z.eqb_refl (cnb_d3 D)). cbv beta iota.
  split; [rewrite app_nil_r, (app_assoc (cnb_Dof st1)); apply Permutation_app_comm|]. repeat split. }
assert (HRc : cnb_regsat regs (cnb_core D ++ [(10%bv, r3); (11%bv, cnb_size D); (12%bv, cnb_d3 D)]))
  by (apply (cnbp_regsat_incl regs _ _ HR); cnbp_incl).
assert (HRk : cnb_regsat regs (cnb_core D ++ [cnb_s8; (25%bv, r1)]))
  by (apply (cnbp_regsat_incl regs _ _ HR); cnbp_incl).
assert (HSP : exists R, ck_cno_evs ReaderRes.jr_strtod (bi_x D) None None None =
  (cnb_cevs D r1 r2 r3 ++ cnb_revs2 D o1 o2) ++ cnb_pe D None ++ R).
{ destruct (cnbp_cno_split D r1 r2 r3 Hr1 Hr2 Hr3) as (R0 & ER0). exists R0.
  rewrite ER0. unfold cnb_revs2. rewrite HRO1, (cnbp_cnb_pe_none D o1 HRO1), (cnbp_cnb_pe_none D o2 HRO2).
  rewrite <- !app_assoc. reflexivity. }
(* the cut's hull budget: reading 3's all-granted events, then the rest after it *)
rewrite cnb_hrest_rd0_split in HHB.
eapply (SRr'_bind SEGS YGcfRehidePost.RZ_cf).
{ exact (cnb_pn_call P HL HC HMN D fxk ly S Hp W regs mem md k 4%nat Lam peak cnt 2%nat r1 r2 r3
    st1 st2 None r3 (cnb_d3 D) CNB_PN3 (cnb_cevs D r1 r2 r3 ++ cnb_revs2 D o1 o2) (fun st => (st1, st2, st))
    (cnb_hrest_rd0 (bi_x D)) ltac:(apply Nat.leb_le; reflexivity) HPRE HB
    HRc Hpl Hoff Hret Hrok (or_intror (or_intror eq_refl)) Hr3 (or_intror (or_intror eq_refl)) ltac:(lia) HPROG HSP HM
    HU HP HHB). }
intros W' c' _ (fx' & ly' & S' & Hp' & regs' & mem' & md' & k' & Lam' & peak' & cnt' & ran' & rcv & st & og & -> &
  HB' & HPR & H10 & KST & HPROG' & HRAN & HM' & HRES & HRD & HFO & HKFO & HPm & HHB').
assert (HK : cnb_regsat regs' (cnb_core D ++ [cnb_s8; (25%bv, r1)])).
{ apply (cnbp_regsat_call regs regs' _ _ HRk HPR).
  unfold cnb_core, cnb_s8. cbn [map fst app]. reflexivity. }
(* 724 `mv s7, a0` *)
apply (cnb_hs_addiR WLE' W' fx' regs' mem' md' _ CNB_RET3 CNB_CMP 23%bv 10%bv 0 cnb_pn_mv eq_refl
  ltac:(unfold CNB_RET3; lia) eq_refl).
intros X. rewrite cnbp_v_addi0.
assert (HK3 : cnb_regsat (regupd regs' 23%bv (getr regs' 10%bv)) ((23%bv, rcv) :: cnb_core D ++ [cnb_s8; (25%bv, r1)])).
{ apply Forall_cons; [cbn [fst snd]; rewrite getr_same; [exact H10 | discriminate]|].
  apply cnbp_regsat_upd; [|exact HK]. unfold cnb_core, cnb_s8. cbn [map fst app In].
  intros Hin. repeat destruct Hin as [Hin|Hin]; try discriminate Hin; exact Hin. }
apply (SRr'_ret SEGS YGcfRehidePost.RZ_cf). split; [|exact HPm].
exists fx', ly', S', Hp', (regupd regs' 23%bv (getr regs' 10%bv)), mem', (with_vm_backing (m_vm_lazy md') X md'), k',
  Lam', peak', cnt', ran', r1, r2, r3, rc1, rc2, rcv, st1, st2, st, o1, o2, og.
split; [reflexivity|].
split; [exact (cnb_base_matR B ARx LAWS WLE' D fx' ly' S' Hp' W' regs' (regupd regs' 23%bv (getr regs' 10%bv)) mem' md'
  k' _ X HB' ltac:(ro_getr; reflexivity) ltac:(ro_getr; reflexivity))|].
split; [apply (cnbp_regsat_incl _ _ _ HK3); cnbp_incl|].
split; [exact (cnb_slots_agree D W mem W' mem' r2 r3 Hal16 KST HSL)|].
split; [exact (cnb_rcslot_agree D W mem W' mem' 8 rc1 Hal16 ltac:(lia) KST HRC1)|].
split; [exact (cnb_rcslot_agree D W mem W' mem' 0 rc2 Hal16 ltac:(lia) KST HRC2)|].
split; [exact Hr1|]. split; [exact Hr2|]. split; [exact Hr3|].
split; [apply (cnb_prog_eq D ((cnb_cevs D r1 r2 r3 ++ cnb_revs2 D o1 o2) ++ cnb_pe D og));
  [unfold cnb_revs2, cnb_revs3; rewrite HRO1, HRO2, <- !app_assoc; reflexivity | exact HPROG']|].
split; [rewrite HRAN; unfold cnb_ranz, ck_cno_ranout; unfold cnb_ro in HRO1, HRO2 |- *; rewrite HRO1, HRO2;
  destruct (PresetRun.ranout ReaderRes.jr_strtod (bi_x D) og); reflexivity|].
split; [exact HM'|].
split; [intros _; exact (HRES1 eq_refl)|]. split; [intros _; exact (HRES2 eq_refl)|]. split; [exact HRES|].
split; [unfold cnb_rds3; rewrite HRO1, HRO2; split; [exact HRD1 | split; [exact HRD2 | exact HRD]]|].
destruct Hinc12 as (Hinc1 & Hinc2).
split; [exact (HKFO o1 (cnb_d1 D) st1 (or_introl eq_refl) ltac:(unfold cnb_d1, cnb_d3; lia) Hinc1 HFO1)|].
split; [exact (HKFO o2 (cnb_d2 D) st2 (or_intror (or_introl eq_refl)) ltac:(unfold cnb_d2, cnb_d3; lia) Hinc2 HFO2)|].
split; [exact HFO | exact HHB'].
Qed.

End rpn.
