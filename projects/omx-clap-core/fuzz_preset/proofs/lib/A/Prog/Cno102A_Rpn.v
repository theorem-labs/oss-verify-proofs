(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YP0n.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/Reusable/YP0n.v, with its module paths and module names changed; 1214 of its 1315 lines of code are new or changed and 1889 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/Cno102A_Base.v, with its module names changed; 1363 of its 1481 lines of code are new or changed and 1197 lines of the source are left out. *)
(* fuzz_preset, image A' (#102 pins: asan sha256 1be0f53d96cb9d6c, unstripped twin bff8519bbe3ea0e4): the three
   parse_noting CALL STEPS of the re-walk of check_no_overread (CA6 / CA7 / CA8 of the internal file PLAN-cno-caw-102.md 5.1):
   cn_pn1_step (CN_PN1 0x81c10 -> CN_READ2), cn_pn2_step (CN_PN2 0x81ce4 -> CN_READ3), cn_pn3_step (CN_PN3 0x81d14 ->
   CN_CMP), each an instance of the one generic step cn_pn_call. First written on
   a working branch ad7ca7b5a3be and finished after the 15:4xZ restart; re-fitted to the kit Batch 2,
   to the #102 kit and then to the kit's CUT preset-tree-at-2026-10-30T04-57-22Z.tsv (sha256 652fe98064b9; internal record).
   rule 24: no function proved
   rule 24: proves no function (kind: segment lemma)
   INPUTS (by path, blobs at this commit's parent): CONTRACT lib/A/Prog/Cno102A_Base.v at
   a working branch 4b59cadb07a1, blob ba76a7bc31c9 (cn_at_pn1 / pn2 / pn3 -> cn_ex_read2 / read3 /
   cmp; cn_pre without DW, read by name (the cn_pre_ projections); cn_base at the wild budget wk (cn_J: exists WS,
   ajournal_xw .. WS /\ wbudget [] wk WS), wk = 0 / 2 / 4 at the three starts and 2 / 4 / 6 at the exits; cn_room_pn;
   the free-order tie cn_fo of each struct a reading filled, carried to the exits), in its forms for the re-hiding
   move (below): cn_baseR / cn_room_pnR over a world relation and cn_baseR_mono, and every cut and exit by its R form
   (cn_at_read2R / cn_ex_read2R, cn_at_pn2R / pn3R, cn_at_read3R / cn_ex_read3R, cn_at_cmpR / cn_ex_cmpR) at wle',
   each cut's hull conjunct LAST (cn_hrest_copies / rd1 / rd2 / rd0) and the split lemmas cn_hrest_rd1_split / rd2_split /
   rd0_split. The text tparse_noting_specX
   (lib/A/PRH_FnCheck.v blob c40cf3fdcd2a :596-730, the cut 7cdbb61b5fa0: no DW; the new premises RQ_pj_parse tb <= most
   and the wild room wild_room (as_universe B) [] (prh_wk F_parse_noting) (st_depot S); the post under fpostFbm ..
   (wbudget [] (prh_wk F_parse_noting)); prh_oks keyed on prh_ev_reqs tr against most; the refusal peak; the
   consumer-reading outcome clause; on the Some arm rd_blocks, the free order pj_foR .. = pj_frees jr_strtod ok tb
   (:718-720) and pj_ncapR) as Section hypothesis HPN, for any float state, instantiated at most := ci_most D,
   own := 0;
   lib/A/PRH_Base.v ef7c8ca98529 (fpre; fpostFb / fpostFbm; prh_oks / prh_refused; prh_ev_reqs; prh_wk);
   lib/A/PRH_Charge.v (prh_maxreq), lib/A/PRH_FnPj.v 5aca5cbe2cfb (RQ_pj_parse = prh_maxreq of the granted trace),
   lib/A/PRH_PjOrder.v e5917626b82b (pj_foR, pj_foR_frame); the model lib/Spec/PresetRun.v (okof, ranout, okk_true /
   okk_false, pkR_app / pkR_mono), PresetReqAt.v (parse_evs, jfv / jfl, pj_frees, hlive_from_app, subm_perm),
   PresetReqAtNoMiss.v (hlive_from_perm), PjGrammar.v (agrees, G7_1_calls / G7_2 / G7_4), PjReqBound.v
   (ev_req_le_esize). Engine: lib/Reusable/YCbqG.v (ajournal_xwR, ajxR_* projections, ajournal_xw_subR,
   ajournal_x_materializeR), YCbqGwild.v (apost_base_xbFR, wbudget_app, afn_pre_x_at_wR, ajournal_xw_rebaseR /
   ajournal_xw_unbase0R), YA0nH.v (SRr', wle', SRr_SRr', wle_wle', wle'_trans), YSRrG.v (SRr'_bind / SRr'_mono /
   SRr'_ret). Listing Listing_prog.v at the cut's blob.
   THE RE-HIDING MOVE: tparse_noting_specX is a CROSSING text (its run reaches pj_parse's frees on a refusal): it
   concludes SRr' SEGS RZ (RZ := YGcfRehidePost.RZ_cf, the fixed zone) with the post fpostFbm (PRH_Base.v restates
   it in place at wle' SEGS RZ: the journal's world conjunct is wle', the engine's apost_base_xbFR there). So every
   step here concludes SRr' SEGS RZ, its exits carry their journals at wle' (the Base's cn_baseR at that relation:
   cn_ex_read2R / cn_ex_read3R / cn_ex_cmpR at wle'), and cn_pn_call takes the cut's journal at wle':
   pn2 / pn3 start at cuts that lie after a free (cn_at_pn2R / cn_at_pn3R at wle'), pn1 at one before it
   (cn_at_pn1 at wle), whose base is lifted first (the Base's cn_baseR_mono at wle_wle'). The return-site register
   steps after a call stay plain SRr, lifted by SRr_SRr'. No world conjunct (ajxR_rel) is read here.
   THE HULL: tparse_noting_specX takes PresetHullBudget.hull_budget S (parse_evs jr_strtod tb []) (its all-granted
   events) and states hull_used S S' (parse_evs jr_strtod tb []) first in its post. The cut at a call carries
   hull_budget S (cn_hrest_<stage> x) (stage copies before pn1, rd1 before pn2, rd2 before pn3, the Base's names) and
   the Base's split lemma gives cn_hrest_<stage> x = parse_evs jr_strtod x [] ++ cn_hrest_<next> x; cn_pn_call pays
   the text from the head (PresetHullBudget.hull_budget_infix at an empty used prefix) and hands the next cut its
   conjunct (hull_budget_app with the post's hull_used): rd1 at read2, rd2 at read3, rd0 at the compare. The file is
   generic in the CfParams instance, and the only callee premise is hull_budget, so no cf_hull_ok is formed here.
   THE CALL: YCbqGwild.v aj_call_xbF_sp's composition (cn_call_x below, over a concrete call state: the rule's st_ok
   premise only seats a symbolic state; footprint the one struct [d, d + 56) in the function's own fake frame): the
   callee's journal at its budget WS1 (wbudget [] 2 WS1) composes with the cut's at WS0 by ajournal_xw_subR at
   wle' SEGS RZ, and the next cut's journal is at WS0 ++ WS1, wbudget [] (wk + 2) by YCbqGwild.wbudget_app. fpre from
   the journal (afn_pre_x_at_wR; STK_check_no_overread = 27424 covers sp = s1 - 27216) and cn_base's frm_zero, the
   chain through the entry's saved s0 / ra, fpre's raZ bound from closed per-slot lemmas (cn_ret_ceil); the text's
   wild room from cn_pre and the cut's journal (the Base's cn_room_pnR at wle', wk + 2 <= 6); the request bound from
   cn_pre_most; the text's two room counts from cn_pre's pkR peaks over ck_cno_evs .. None None None and the cut's
   cn_prog live set (cn_pkR_mid: PresetRun.pkR_app / pkR_mono).
   THE GRANT (section 1b): the post's outcome list ok is, for its reading, its events, its free list and its ran-out,
   the model's grant okof og of ONE og (cn_grant), by the owed grammar lemma (d) PROVED here (cn_jr_run_pre /
   cn_pj_frees_pre / cn_parse_evs_pre: grant lists that agree on the reading's calls give the same jr_run, pj_frees and
   parse_evs; the B' twin's proof). So no AGREE-PREFIX premise is carried. A refusal inside the reading sets
   g_ran_out because its request is at most the granted reading's largest (cn_reqs_most: the refused call's EFail
   carries the granted call's size, PjGrammar.agrees), which is RQ_pj_parse x <= ci_most D (cn_pre_most).
   THE FREE ORDER (cn_fo): the struct a reading fills gets the text's Some-arm order list at ok, turned into okof og by
   cn_grant's pj_frees equation; the other structs' ties cross the call by PRH_PjOrder.pj_foR_frame (the call writes
   only its own struct and fresh blocks; their trees sit in their own Lam blocks).
   THE POST CONJUNCTS OF tparse_noting_specX THIS FILE USES: hull_used, room_live_cf S', the jr_run equation, the
   exact live set and the position implication (cn_prog_app), prh_oks's second and third conjuncts (ran' = 1 exactly
   when ok refuses inside the reading), cnt' = cnt + calls tr, fail_after (to keep fail = SIZE_MAX), peak' = Z.max ..
   (used ONLY for peak <= peak'), `ran' <> 0 -> res = None`, `ran' = 0 -> .. -> res = ck_read tb /\ calls =
   ck_ncalls`, the post ledger (at ci_most D and own 0), and the `match res` arms (the tree, its free order and its
   fresh blocks, or the zero struct). NOT used: the consumer-reading outcome clause (the readings here are P1 events),
   prh_oks's first conjunct, the hpeak bound, the injected-failure arm, bytes_at of the copy, rd_blocks, pj_ncapR. The
   inner post is read BY NAME (PRH_FnCheck.v: tpnP_R through tpnP_R_of, the arms through tpnP_RSome_of /
   tpnP_RNone_of, the granted guard through tpnP_granted_read), so a conjunct appended to it breaks nothing here. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjRoundTrip PresetRoomPos PjReqBound
  PresetHullBudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Img PRH_Reader PRH_FnAlloc
  PRH_FnReader PRH_FnPj PRH_FnEx PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Charge PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_StepKit Cno102A_Base.
(* the PLAIN build's sink instance is loaded transitively; it must never fill an ASan sink argument *)
#[global] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
(* (no file-wide default timeout) *)
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.
(* the re-hiding move's fixed zone: after a free the world relation is YA0nH.wle' SEGS RZ *)
#[local] Notation RZ := YGcfRehidePost.RZ_cf.

(* ==== 1. pure helpers ==== *)
Lemma cn_regsat_get : forall regs l (r : bv 5) v, cn_regsat regs l -> In (r, v) l -> getr regs r = w64 v.
Proof. intros regs l r v H Hin. unfold cn_regsat in H. exact (proj1 (Forall_forall _ _) H (r, v) Hin). Qed.
Lemma cn_regsat_incl : forall regs l l', cn_regsat regs l -> incl l' l -> cn_regsat regs l'.
Proof.
intros regs l l' H Hi. unfold cn_regsat in *. apply Forall_forall. intros p Hp.
exact (proj1 (Forall_forall _ _) H p (Hi p Hp)).
Qed.
(* a register the callee saves is kept *)
Lemma cn_pres : forall regs regs' (r : bv 5), aregs_preserved regs regs' -> acallee_saved (bv_unsigned r) ->
  getr regs' r = getr regs r.
Proof.
intros regs regs' r H Hs. pose proof (H _ Hs) as E.
assert (Er : Z_to_bv 5 (bv_unsigned r) = r) by (apply bv_eq; rewrite Z_to_bv_unsigned; apply bv_wrap_small, bv_unsigned_in_range).
rewrite Er in E. exact E.
Qed.
Lemma cn_pres_regsat : forall regs regs' l, aregs_preserved regs regs' ->
  Forall (fun r : bv 5 => acallee_saved (bv_unsigned r)) (map fst l) -> cn_regsat regs l -> cn_regsat regs' l.
Proof.
intros regs regs' l HP Hc H. unfold cn_regsat in *. rewrite Forall_forall in *.
intros [r v] Hin. cbn [fst snd]. pose proof (H _ Hin) as E. cbn [fst snd] in E. rewrite <- E.
apply cn_pres; [exact HP|]. apply Hc. apply in_map_iff. exists (r, v). split; [reflexivity | exact Hin].
Qed.
Lemma cn_regsat_upd : forall regs l (r : bv 5) w, ~ In r (map fst l) -> cn_regsat regs l -> cn_regsat (regupd regs r w) l.
Proof.
intros regs l r w Hn H. unfold cn_regsat in *. rewrite Forall_forall in *.
intros [r' v] Hin. cbn [fst snd]. rewrite getr_other.
- exact (H _ Hin).
- intros E. apply Hn. apply in_map_iff. exists (r', v). split; [exact E | exact Hin].
Qed.
Lemma cn_Forall_and : forall {A : Type} (P Q R : A -> Prop) l, Forall P l -> Forall Q l -> (forall x, P x -> Q x -> R x) ->
  Forall R l.
Proof.
intros A P Q R l HP HQ H. rewrite Forall_forall in *. intros x Hx. exact (H x (HP x Hx) (HQ x Hx)).
Qed.
Lemma cn_rdword_agree : forall (rd rd' : reader) a, (forall i, 0 <= i < 8 -> rd' (a + i) = rd (a + i)) ->
  rdword rd' a = rdword rd a.
Proof.
intros rd rd' a H. unfold rdword.
assert (H0 : rd' a = rd a) by (pose proof (H 0 ltac:(lia)) as E; rewrite Z.add_0_r in E; exact E).
rewrite H0, (H 1), (H 2), (H 3), (H 4), (H 5), (H 6), (H 7) by lia. reflexivity.
Qed.
Lemma cn_land32 : forall x, 0 <= x -> Z.land x (-32) = x - x mod 32.
Proof.
intros x Hx. replace (-32) with (Z.lnot (Z.ones 5)) by reflexivity.
rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia.
rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
change (2 ^ 5) with 32. pose proof (Z.div_mod x 32 ltac:(lia)). lia.
Qed.
Lemma cn_mod32_at : forall F x j, F mod 32 = 0 -> x = F + 32 * j -> x mod 32 = 0.
Proof. intros F x j H ->. replace (F + 32 * j) with (F + j * 32) by lia. rewrite Z.mod_add by lia. exact H. Qed.
Lemma cn_mod8 : forall x, x mod 32 = 0 -> x mod 8 = 0.
Proof.
intros x H. apply Z.mod_divide in H; [|lia]. apply Z.mod_divide; [lia|]. destruct H as [q ->]. exists (4 * q). lia.
Qed.
Lemma cn_mod2 : forall x, x mod 4 = 0 -> x mod 2 = 0.
Proof.
intros x H. apply Z.mod_divide in H; [|lia]. apply Z.mod_divide; [lia|]. destruct H as [q ->]. exists (2 * q). lia.
Qed.
Lemma cn_v_addi0 : forall x : word, v_addi x 0 = x.
Proof.
intros x. unfold v_addi. rewrite Z.add_0_r. apply bv_eq. rewrite Z_to_bv_unsigned.
apply bv_wrap_small, bv_unsigned_in_range.
Qed.

(* the reading's counts (PjGrammar G7_1 / G7_2 / ok_upto_dec, as H5RttS3.v s3_read_some) *)
Lemma cn_read_some : forall x ok t tr,
  PjGrammar.jr_run ReaderRes.jr_strtod x ok = (Some t, tr) ->
  PjGrammar.json_read ReaderRes.jr_strtod x = Some t /\ tr = snd (PjGrammar.jr_run ReaderRes.jr_strtod x []).
Proof.
intros x ok t tr H.
destruct (PjGrammar.ok_upto_dec ok (PjGrammar.ncalls ReaderRes.jr_strtod x)) as [Hu | (j & Hj & Hf & Hb)].
- rewrite (PjGrammar.G7_1 _ x ok Hu) in H. injection H as E1 E2. split; [exact E1 | symmetry; exact E2].
- exfalso. destruct (PjGrammar.G7_2 _ x ok j Hj Hf Hb) as [H1 _]. rewrite H in H1. discriminate H1.
Qed.
Lemma cn_calls_le : forall x ok res tr,
  PjGrammar.jr_run ReaderRes.jr_strtod x ok = (res, tr) ->
  (PjGrammar.calls tr <= PjGrammar.ncalls ReaderRes.jr_strtod x)%nat.
Proof.
intros x ok res tr H.
destruct (PjGrammar.ok_upto_dec ok (PjGrammar.ncalls ReaderRes.jr_strtod x)) as [Hu | (j & Hj & Hf & Hb)].
- rewrite (PjGrammar.G7_1 _ x ok Hu) in H. injection H as _ E2. subst tr. unfold PjGrammar.ncalls. lia.
- destruct (PjGrammar.G7_2 _ x ok j Hj Hf Hb) as [_ H2]. rewrite H in H2. cbn [snd] in H2. lia.
Qed.
Lemma cn_held_le_hpeak : forall tr, PjGrammar.held tr <= hpeakR tr.
Proof. induction tr as [|e r IH]; cbn [PjGrammar.held hpeakR]; lia. Qed.
Lemma cn_hpeak_nonneg : forall tr, 0 <= hpeakR tr.
Proof. destruct tr as [|e r]; cbn [hpeakR]; lia. Qed.
Lemma cn_nlive_le_calls : forall tr, ReaderRes.nlive tr <= Z.of_nat (PjGrammar.calls tr).
Proof.
induction tr as [|e r IH]; cbn [ReaderRes.nlive PjGrammar.calls]; [lia|].
destruct e as [n|[|m] n|n|n]; cbn [ReaderRes.nlive_ev PjGrammar.is_call]; lia.
Qed.
Lemma cn_bsum_hblks {cp : CfParams} : forall D, bsum (ck_hblks D) = Ledger.lsum D + cf_head * Z.of_nat (length D).
Proof.
induction D as [|[a kk] D IH]; [cbn; lia|].
unfold ck_hblks in *. cbn [map length Ledger.lsum fst snd]. rewrite bsum_cons. cbn [snd]. rewrite IH. lia.
Qed.

(* the tree representation is monotone in its block predicate *)
Lemma cn_cstrR_lblk : forall segs m lblk lblk' a k s, pj_cstrR segs m lblk a k s ->
  (forall a k, lblk a k -> lblk' a k) -> pj_cstrR segs m lblk' a k s.
Proof. intros segs m lblk lblk' a k s (Hl & Hr) H. split; [exact (H _ _ Hl) | exact Hr]. Qed.
Lemma cn_memsR_lblk : forall segs m lblk lblk' (P P' : Z -> PjTree.jv -> list (Z * Z) -> Prop) l a ka D,
  pj_memsR segs m lblk P a ka l D -> (forall a k, lblk a k -> lblk' a k) ->
  (forall i nm u D1, nth_error l i = Some (nm, u) -> P (a + 56 * Z.of_nat i) u D1 -> P' (a + 56 * Z.of_nat i) u D1) ->
  pj_memsR segs m lblk' P' a ka l D.
Proof.
intros segs m lblk lblk' P P' l. induction l as [|[nm u] r IH]; intros a ka D H Hl HP; cbn [pj_memsR] in H |- *;
  [exact H|].
destruct H as (x & k & D1 & D2 & -> & Hx & Hc & H1 & H2). exists x, k, D1, D2. split; [reflexivity|].
split; [exact Hx|]. split; [exact (cn_cstrR_lblk _ _ _ _ _ _ _ Hc Hl)|].
split.
- specialize (HP 0%nat nm u D1 eq_refl). replace (a + 56 * Z.of_nat 0) with a in HP by lia. exact (HP H1).
- apply (IH (a + 56) (ka + 8) D2 H2 Hl). intros i nm' u' D1' Hi HPi.
  specialize (HP (S i) nm' u' D1' Hi). replace (a + 56 * Z.of_nat (S i)) with (a + 56 + 56 * Z.of_nat i) in HP by lia.
  exact (HP HPi).
Qed.
Lemma cn_nodeR_lblk : forall segs t m lblk lblk' p D, pj_nodeR segs m lblk p t D ->
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
  exists k. split; [exact (cn_cstrR_lblk _ _ _ _ _ _ _ Hc Hl) | exact ED].
- destruct Hb as (E2 & E3 & E4 & E5 & k & Hc & ED).
  split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
  exists k. split; [exact (cn_cstrR_lblk _ _ _ _ _ _ _ Hc Hl) | exact ED].
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
  apply (cn_memsR_lblk segs m lblk lblk' (pj_nodeR segs m lblk) (pj_nodeR segs m lblk') members kids keys Di Hi Hl).
  intros i nm u D1 Hil HP. rewrite Forall_forall in IH. specialize (IH (nm, u) (nth_error_In members i Hil)).
  cbn [snd] in IH. exact (IH m lblk lblk' _ D1 HP Hl).
Qed.

(* a runtime block's shadow (ARx's block-shadow law) gives a copy's src_rd shadow conjuncts *)
Lemma cn_bshadow_ra : forall (rd : reader) p len, 0 <= len ->
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
Lemma cn_hull_sub : forall (rd : reader) p n len, 0 < len <= n -> shadow_hull_vis rd p n -> shadow_hull_vis rd p len.
Proof.
intros rd p n len Hl H s Hs. apply H. split; [lia|].
assert (shadow_addr (p + len - 1) <= shadow_addr (p + n - 1)) by (unfold shadow_addr; apply Z.add_le_mono_l, Z.div_le_mono; lia).
assert (shadow_addr (p + len - 1) / 8 <= shadow_addr (p + n - 1) / 8) by (apply Z.div_le_mono; lia).
lia.
Qed.
(* a struct's shadow lies in the frame's shadow (F mod 32 = 0, the struct at F + 32 .. F + 280) *)
Lemma cn_struct_shadow : forall F d0, F mod 32 = 0 -> 0 <= F -> F + 32 <= d0 -> d0 + 56 <= F + 280 -> d0 mod 32 = 0 ->
  (forall x, d0 <= x < d0 + 56 -> shadow_addr F <= shadow_of_addr SHADOW_OFF x < shadow_addr F + 64) /\
  (forall s, shadow_addr d0 / 8 * 8 <= s < shadow_addr (d0 + 56 - 1) / 8 * 8 + 8 ->
     shadow_addr F <= s < shadow_addr F + 64).
Proof.
intros F d0 HF HF0 H1 H2 Hd. unfold shadow_addr, shadow_of_addr, SHADOW_OFF.
pose proof (Z.div_mod F 32 ltac:(lia)) as EF. rewrite HF, Z.add_0_r in EF.
pose proof (Z.div_mod d0 32 ltac:(lia)) as Ed. rewrite Hd, Z.add_0_r in Ed.
set (f := F / 32) in *. set (g := d0 / 32) in *.
assert (EF8 : F / 8 = 4 * f) by (rewrite EF; replace (32 * f) with ((4 * f) * 8) by lia; apply Z.div_mul; lia).
assert (Ed8 : d0 / 8 = 4 * g) by (rewrite Ed; replace (32 * g) with ((4 * g) * 8) by lia; apply Z.div_mul; lia).
split.
- intros x Hx. pose proof (Z.div_le_mono d0 x 8 ltac:(lia) ltac:(lia)).
  assert (x / 8 < 4 * f + 35) by (apply Z.div_lt_upper_bound; lia). lia.
- intros s Hs.
  assert (Hlo : (2147450880 + d0 / 8) / 8 * 8 = 2147450880 + 8 * (g / 2)).
  { rewrite Ed8. pose proof (Z.div_mod g 2 ltac:(lia)). pose proof (Z.mod_pos_bound g 2 ltac:(lia)).
    replace (2147450880 + 4 * g) with ((268431360 + g / 2) * 8 + 4 * (g mod 2)) by lia.
    rewrite Z.div_add_l by lia. rewrite (Z.div_small (4 * (g mod 2)) 8) by lia. lia. }
  assert (Hhi : (2147450880 + (d0 + 56 - 1) / 8) / 8 * 8 <= 2147450880 + (d0 + 55) / 8).
  { replace (d0 + 56 - 1) with (d0 + 55) by lia. rewrite Z.mul_comm. apply Z.mul_div_le. lia. }
  assert ((d0 + 55) / 8 < 4 * g + 7) by (apply Z.div_lt_upper_bound; lia).
  pose proof (Z.div_mod g 2 ltac:(lia)). pose proof (Z.mod_pos_bound g 2 ltac:(lia)).
  rewrite EF8. lia.
Qed.

(* the ledger list and the block list after a reading whose blocks Ds go to one of the three structs *)
Lemma cn_perm_lam : forall {A : Type} (L2 L Ds D1 D2 D3 a b c L0 : list A),
  Permutation L2 (Ds ++ L) -> Permutation L (D1 ++ D2 ++ D3 ++ L0) ->
  Permutation (a ++ b ++ c) (Ds ++ D1 ++ D2 ++ D3) -> Permutation L2 (a ++ b ++ c ++ L0).
Proof.
intros A L2 L Ds D1 D2 D3 a b c L0 H1 H2 H3. rewrite H1, H2. rewrite !app_assoc. rewrite !app_assoc in H3.
rewrite H3. reflexivity.
Qed.
Lemma cn_perm_blocks {cp : CfParams} : forall (AB2 AB C Ds D1 D2 D3 a b c A0 : list (Z * Z)),
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

(* ==== 1b. THE READER'S GRANT LISTS (the kit's owed pure grammar lemma (d), PRH_FnPj.v 5aca5cbe2cfb's (the cut's)
   prhPj_parse_evs_starved comment; proved here, the B' twin's proof (lib/B/Prog/Cno102B_Rpn.v, by a Theorem Labs sub-lane) with
   cn_ names): two grant lists that agree on the first calls tr outcomes of a reading give the same reading, the same
   trace and the same pj_free list, so the same parse_evs; hence every outcome list ok of a reading is, for its events,
   its free list and its ran-out, the model's grant okof o of ONE o (None when ok grants every allocation the reading
   makes, Some j at its first refusal j). A refusal ends a reading (PjGrammar.agrees: jbind stops at the first None),
   which is why no premise (AGREE-PREFIX) is needed. ==== *)
(* the split of a trace at its (j+1)-th call is unique *)
Lemma cn_split_uniq : forall (P P' : list PjGrammar.ev) E E' r r',
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
Lemma cn_agrees_pre : forall (A : Type) (m : PjGrammar.M A), PjGrammar.agrees m ->
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
  rewrite Hs in Hs'. destruct (cn_split_uniq P P' e e' rest0 rest' Hs' ltac:(lia) Hic Hic') as [<- <-].
  rewrite E2. split; reflexivity.
Qed.
(* one bind step: the first computation agrees on the first calls of its own trace, and the continuation's list is
   the rest *)
Lemma cn_bind_pre : forall (A B : Type) (m : PjGrammar.M A) (k : A -> PjGrammar.M B) ok ok' r t ok1,
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
destruct (cn_agrees_pre A m Hm ok ok' r t ok1 E Ht) as (E' & ->).
split; [exact Ht|]. split; [exact E'|]. split; [reflexivity|].
intros a Ea i Hi. rewrite !PjGrammar.nth_skipn_b. apply H. rewrite (HT2 a Ea). lia.
Qed.
(* pj_free's walk (PresetReqAt.jfv / jfl) reads the grant list only through grow, jr_name and jrv, so it agrees as the
   reading does: the same pj_free list for lists agreeing on the first calls of the reading's trace *)
Lemma cn_jfv_pre : forall (sm : list Z -> Z * Z) f,
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
    destruct (cn_agrees_pre _ _ (proj1 (PjGrammar.agrees_fuel sm (S f)) d x) ok ok' rv tv okv Ev H) as (Ev' & _).
    rewrite Ev'. reflexivity.
- intros d o n cap acc af y ok ok' H. cbn [PresetReqAt.jfl]. cbn [PjGrammar.jrl] in H.
  destruct (PjGrammar.grow o n cap ok) as [[rg tg] okg] eqn:Eg.
  destruct (cn_bind_pre _ _ _ _ ok ok' _ _ _ (PjGrammar.agrees_grow o n cap) Eg H) as (_ & Eg' & -> & Hk1).
  rewrite Eg'. destruct rg as [cap1|]; [|reflexivity].
  specialize (Hk1 cap1 eq_refl). cbv beta in Hk1.
  set (ok1 := skipn (PjGrammar.calls tg) ok) in *. set (ok1' := skipn (PjGrammar.calls tg) ok') in *.
  destruct (PjGrammar.jr_name o y ok1) as [[rn tn] okn] eqn:En.
  destruct (cn_bind_pre _ _ _ _ ok1 ok1' _ _ _ (PjGrammar.agrees_jr_name o y) En Hk1) as (_ & En' & -> & Hk2).
  rewrite En'. destruct rn as [[name y1]|]; [|reflexivity].
  specialize (Hk2 (name, y1) eq_refl). cbv beta iota in Hk2.
  set (ok2 := skipn (PjGrammar.calls tn) ok1) in *. set (ok2' := skipn (PjGrammar.calls tn) ok1') in *.
  destruct (PjGrammar.jrv sm f d y1 ok2) as [[rv tv] okv] eqn:Ev.
  destruct (cn_bind_pre _ _ _ _ ok2 ok2' _ _ _ (proj1 (PjGrammar.agrees_fuel sm f) d y1) Ev Hk2)
    as (Hv & Ev' & -> & Hk3).
  cbv zeta. rewrite (IHv d y1 ok2 ok2' ltac:(rewrite Ev; exact Hv)), Ev'.
  destruct rv as [[v r]|]; [|reflexivity].
  specialize (Hk3 (v, r) eq_refl). cbv beta iota in Hk3.
  destruct (PjGrammar.skip r) as [|c r1]; [reflexivity|].
  destruct (c =? 44); [|reflexivity].
  exact (IHl d o (S n) cap1 ((name, v) :: acc) _ r1 _ _ Hk3).
Qed.
(* (d): the reading, its trace and its pj_free list, hence its events, of two lists agreeing on its calls *)
Lemma cn_jr_run_pre : forall (sm : list Z -> Z * Z) x ok ok',
  (forall i, (i < PjGrammar.calls (snd (PjGrammar.jr_run sm x ok)))%nat -> nth i ok' true = nth i ok true) ->
  PjGrammar.jr_run sm x ok' = PjGrammar.jr_run sm x ok.
Proof.
intros sm x ok ok' H. rewrite !PjGrammar.jr_run_eq in *. cbn [fst snd] in H.
destruct (PjGrammar.jr_value sm 0 x ok) as [[r t] rest] eqn:E. cbn [fst snd] in H |- *.
destruct (cn_agrees_pre _ _ (PjGrammar.agrees_jr_value sm 0 x) ok ok' r t rest E H) as (E' & _).
rewrite E'. reflexivity.
Qed.
Lemma cn_parse_evs_pre : forall (sm : list Z -> Z * Z) x ok ok',
  (forall i, (i < PjGrammar.calls (snd (PjGrammar.jr_run sm x ok)))%nat -> nth i ok' true = nth i ok true) ->
  PresetReqAt.parse_evs sm x ok' = PresetReqAt.parse_evs sm x ok.
Proof.
intros sm x ok ok' H. unfold PresetReqAt.parse_evs, PresetReqAt.rtr, PresetReqAt.pj_frees.
rewrite (cn_jr_run_pre sm x ok ok' H).
rewrite (proj1 (cn_jfv_pre sm _) 0%nat x ok ok'); [reflexivity|].
rewrite PjGrammar.jr_run_eq in H. exact H.
Qed.
(* (d) for pj_free's list alone: the free order of two grant lists agreeing on the reading's calls *)
Lemma cn_pj_frees_pre : forall (sm : list Z -> Z * Z) x ok ok',
  (forall i, (i < PjGrammar.calls (snd (PjGrammar.jr_run sm x ok)))%nat -> nth i ok' true = nth i ok true) ->
  PresetReqAt.pj_frees sm ok' x = PresetReqAt.pj_frees sm ok x.
Proof.
intros sm x ok ok' H. unfold PresetReqAt.pj_frees.
apply (proj1 (cn_jfv_pre sm _) 0%nat x ok ok'). rewrite PjGrammar.jr_run_eq in H. exact H.
Qed.
(* THE GRANT of a reading's outcome list ok: o = None when ok grants every allocation the reading makes, Some j at
   its first refusal j; the same reading, events and free list, and ran-out exactly when ok refuses inside the
   reading *)
Lemma cn_grant : forall (sm : list Z -> Z * Z) x ok, exists o,
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
  split; [exact (cn_jr_run_pre sm x ok _ Hag)|]. split; [exact (cn_parse_evs_pre sm x ok _ Hag)|].
  split; [exact (cn_pj_frees_pre sm x ok _ Hag)|].
  left. split; [reflexivity|]. intros i Hi. rewrite Ec in Hi. exact (Hu i Hi).
- exists (Some j).
  destruct (PjGrammar.G7_2 sm x ok j Hj Hf Hu) as (_ & Ec).
  assert (Hag : forall i, (i < PjGrammar.calls (snd (PjGrammar.jr_run sm x ok)))%nat ->
    nth i (PresetRun.okof (Some j)) true = nth i ok true).
  { intros i Hi. rewrite Ec in Hi. cbn [PresetRun.okof]. destruct (Nat.lt_ge_cases i j) as [Hl|Hg].
    - rewrite (PresetRun.okk_true j i Hl), (Hu i Hl). reflexivity.
    - replace i with j by lia. rewrite PresetRun.okk_false, Hf. reflexivity. }
  split; [exact (cn_jr_run_pre sm x ok _ Hag)|]. split; [exact (cn_parse_evs_pre sm x ok _ Hag)|].
  split; [exact (cn_pj_frees_pre sm x ok _ Hag)|].
  right. split.
  + cbn [PresetRun.ranout]. apply Nat.ltb_lt. unfold PjGrammar.ncalls in Hj. exact Hj.
  + exists j. split; [rewrite Ec; lia | exact Hf].
Qed.
(* a grant under which the reading does not run out gives the all-granted reading's events *)
Lemma cn_parse_evs_noro : forall (sm : list Z -> Z * Z) x o, PresetRun.ranout sm x o = false ->
  PresetReqAt.parse_evs sm x (PresetRun.okof o) = PresetReqAt.parse_evs sm x [].
Proof.
intros sm x [j|] H; [|reflexivity]. cbn [PresetRun.ranout PresetRun.okof] in *. apply Nat.ltb_ge in H.
apply cn_parse_evs_pre. intros i Hi. unfold PresetReqAt.rtr in H.
rewrite (PresetRun.okk_true j i ltac:(lia)). destruct i; reflexivity.
Qed.
(* the peak of a count along the next reading, from a live set reached by E, inside the peak along E ++ X ++ R *)
Lemma cn_pkR_mid : forall f (s0 s : list Z) E X R,
  Permutation s (PresetReqAt.hlive_from s0 E) ->
  (PresetRun.pkR f s X <= PresetRun.pkR f s0 (E ++ X ++ R))%nat.
Proof.
intros f s0 s E X R H. rewrite !PresetRun.pkR_app.
pose proof (PresetRun.pkR_mono f X s (PresetReqAt.hlive_from s0 E) (PresetReqAt.subm_perm _ _ (Permutation_sym H))).
lia.
Qed.
(* THE REQUESTS OF A READING (prh_oks's ns at the cut: prh_ev_reqs tr against g_most): every request of a reading
   under any grant list is at most the granted reading's largest single request (PRH_Charge.prh_maxreq of the granted
   trace, which RQ_pj_parse is): up to its first refusal the trace is the granted one's, and the refused call's EFail
   carries the granted call's size (PjGrammar.agrees) *)
Lemma cn_maxreq_ge : forall t e, In e t -> Z.of_nat (PjGrammar.esize e) <= PRH_Charge.prh_maxreq t.
Proof.
intros t e. unfold PRH_Charge.prh_maxreq. induction t as [|e' t IH]; intros H; [destruct H|].
cbn [map fold_right]. destruct H as [<-|H]; [lia|]. specialize (IH H). lia.
Qed.
Lemma cn_maxreq_le : forall t M, 0 <= M -> (forall e, In e t -> Z.of_nat (PjGrammar.esize e) <= M) ->
  PRH_Charge.prh_maxreq t <= M.
Proof.
intros t M HM. unfold PRH_Charge.prh_maxreq. induction t as [|e t IH]; intros H; cbn [map fold_right]; [lia|].
pose proof (H e (or_introl eq_refl)) as H1. pose proof (IH (fun e' He' => H e' (or_intror He'))) as H2. lia.
Qed.
(* a request of prh_ev_reqs t is some event of t's (prh_ev_reqs filters with the list filter of PRH_Base's scope:
   unfolded by computation on each cons, its decision destructed) *)
Lemma cn_ev_reqs_in : forall t y, In y (prh_ev_reqs t) -> exists e, In e t /\ PjReqBound.ev_req e = y.
Proof.
induction t as [|a t IH]; intros y H; unfold prh_ev_reqs in H; cbn in H; [destruct H|].
repeat (match type of H with context [if ?c then _ else _] => destruct c end; cbn in H);
  first
    [ destruct H as [<-|H];
      [ exists a; split; [left; reflexivity | reflexivity]
      | destruct (IH y H) as (e & He & Ee); exists e; split; [right; exact He | exact Ee] ]
    | destruct (IH y H) as (e & He & Ee); exists e; split; [right; exact He | exact Ee] ].
Qed.
Lemma cn_ev_reqs_le : forall t i, nth i (prh_ev_reqs t) 0 <= PRH_Charge.prh_maxreq t.
Proof.
intros t i. destruct (Nat.lt_ge_cases i (length (prh_ev_reqs t))) as [Hl|Hg].
- assert (Hin : In (nth i (prh_ev_reqs t) 0) (prh_ev_reqs t)) by (apply nth_In; exact Hl).
  destruct (cn_ev_reqs_in t _ Hin) as (e & He & Ee). rewrite <- Ee.
  pose proof (PjReqBound.ev_req_le_esize e) as H1. pose proof (cn_maxreq_ge t e He) as H2. lia.
- rewrite nth_overflow by exact Hg. unfold PRH_Charge.prh_maxreq.
  induction (map _ t) as [|a l IH]; cbn [fold_right]; lia.
Qed.
Lemma cn_reqs_most : forall (sm : list Z -> Z * Z) x ok i,
  nth i (prh_ev_reqs (snd (PjGrammar.jr_run sm x ok))) 0 <= PRH_Charge.prh_maxreq (snd (PjGrammar.jr_run sm x [])).
Proof.
intros sm x ok i. rewrite !PjGrammar.jr_run_eq. cbn [snd].
pose proof (cn_ev_reqs_le (snd (fst (PjGrammar.jr_value sm 0 x ok))) i) as H1.
enough (H2 : PRH_Charge.prh_maxreq (snd (fst (PjGrammar.jr_value sm 0 x ok))) <=
             PRH_Charge.prh_maxreq (snd (fst (PjGrammar.jr_value sm 0 x [])))) by lia.
pose proof (PjGrammar.agrees_jr_value sm 0 x ok) as (Hu & Hf).
destruct (PjGrammar.ok_upto_dec ok (PjGrammar.calls (snd (fst (PjGrammar.jr_value sm 0 x [])))))
  as [Hok | (j & Hj & Hfj & Hoj)].
- rewrite (Hu Hok). cbn [fst snd]. lia.
- destruct (Hf j Hj Hfj Hoj) as (P & e & rest & E1 & E2 & _ & _). rewrite E1, E2. cbn [fst snd].
  apply cn_maxreq_le.
  + pose proof (cn_maxreq_ge (P ++ e :: rest) e ltac:(apply in_or_app; right; left; reflexivity)) as H3. lia.
  + intros e' He'. apply in_app_or in He' as [He'|[<-|[]]].
    * apply cn_maxreq_ge. apply in_or_app. left. exact He'.
    * cbn [PjGrammar.esize]. apply cn_maxreq_ge. apply in_or_app. right. left. reflexivity.
Qed.

(* ==== 2. one register step at a listing slot (H5RttS3.v s3_addi / s3_jal over the base's PL_cno_A) ==== *)
Section stp. Context {fz : YK11.FPState} {rc : YM05.RunCeil}.
Context {PA : PAImg A_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
Lemma cn_step_addi : forall (W : world SEGS) regs mem md Q w k (rd rs : bv 5) (imm : bv 12),
  plookup (@pl_tpi _ PL_cno_A) k = Some (PW w) ->
  decode_any (Z_to_bv 32 w) = Some (OpImm ALU_ADD rd rs imm, 4%Z) ->
  bv_eqb rd 0 = false -> 0 <= k -> k + 4 < 2 ^ 40 ->
  (forall mat', SRr SEGS W
     (mkCfg (@YK11.mkst fz (regupd regs rd (v_addi (getr regs rs) (bv_signed imm)))
               (Z_to_bv 64 (BASE + (k + 4))) mem (YK11.seg_rom SEGS))
            (with_vm_backing (m_vm_lazy md) mat' md)) Q) ->
  SRr SEGS W (mkCfg (@YK11.mkst fz regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md Q w k rd rs imm Hpl Hdec Hrd Hk0 Hk4 HK.
pose proof (@pa_lookup_pw rc A_prog_listing PL_cno_A PA k w Hpl) as (Hl & _ & _).
pose proof (@pa_B_ok rc A_prog_listing PA) as (HB0 & HB1 & _).
eapply (SRr_step SEGS pa_wx W); [reflexivity | |].
- rewrite restrict_mkst_fx.
  rewrite (step_addi SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)
             (Z_to_bv 32 w) rd rs imm (pa_fetch_ok _ _ Hl)
             (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec).
  rewrite Hrd. reflexivity.
- intros model' Hsame. rewrite (same_but_materialized_wvb md model' Hsame).
  cbn [ms_mem YK11.mkst]. rewrite unrestrict_mkst_mrestrict.
  replace (v_addi (Z_to_bv 64 (BASE + k)) 4) with (Z_to_bv 64 (BASE + (k + 4))); [apply HK|].
  unfold v_addi. rewrite unsigned_lit_small by lia. f_equal. lia.
Qed.
(* `j off` (jal zero): the registers unchanged *)
Lemma cn_step_j : forall (W : world SEGS) regs mem md Q w k tgt (imm : bv 21),
  plookup (@pl_tpi _ PL_cno_A) k = Some (PW w) ->
  decode_any (Z_to_bv 32 w) = Some (Jal 0%bv imm, 4%Z) ->
  0 <= k -> k + 4 < 2 ^ 40 ->
  btgt (Z_to_bv 64 (BASE + k)) (bv_signed imm) = Z_to_bv 64 tgt ->
  (forall mat', SRr SEGS W
     (mkCfg (@YK11.mkst fz regs (Z_to_bv 64 tgt) mem (YK11.seg_rom SEGS))
            (with_vm_backing (m_vm_lazy md) mat' md)) Q) ->
  SRr SEGS W (mkCfg (@YK11.mkst fz regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md Q w k tgt imm Hpl Hdec Hk0 Hk4 Htgt HK.
pose proof (@pa_lookup_pw rc A_prog_listing PL_cno_A PA k w Hpl) as (Hl & _ & _).
assert (H00 : bv_eqb (0%bv : bv 5) 0 = true) by (vm_compute; reflexivity).
eapply (SRr_step SEGS pa_wx W); [reflexivity | |].
- rewrite restrict_mkst_fx.
  rewrite (step_jal_link SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)
             (Z_to_bv 32 w) 0%bv imm (pa_fetch_ok _ _ Hl)
             (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec).
  rewrite H00. reflexivity.
- intros model' Hsame. rewrite (same_but_materialized_wvb md model' Hsame).
  cbn [ms_mem YK11.mkst]. rewrite unrestrict_mkst_mrestrict. rewrite Htgt. apply HK.
Qed.
End stp.
(* ==== 2b. the three return slots: CLOSED facts (each vm_compute in its own top-level lemma, never in a step proof)
   and the register steps from each return site to the next cut. A' twin: 0x81c14 `mv s7, a0` (0x50b93) then 0x81c18
   `j 0x81cb4` (0x9c0006f); 0x81ce8 `mv s9, a0` (0x50c93); 0x81d18 `mv s4, a0` (0x50a13). ==== *)
Lemma cn_pl_ret1 : plookup (@pl_tpi _ PL_cno_A) (CN_OFF + CN_RET1) = Some (PW 330643).
Proof. vm_compute. reflexivity. Qed.
Lemma cn_pl_j1 : plookup (@pl_tpi _ PL_cno_A) (CN_OFF + CN_RET1 + 4) = Some (PW 163577967).
Proof. vm_compute. reflexivity. Qed.
Lemma cn_pl_ret2 : plookup (@pl_tpi _ PL_cno_A) (CN_OFF + CN_RET2) = Some (PW 330899).
Proof. vm_compute. reflexivity. Qed.
Lemma cn_pl_ret3 : plookup (@pl_tpi _ PL_cno_A) (CN_OFF + CN_RET3) = Some (PW 330259).
Proof. vm_compute. reflexivity. Qed.
(* the decoder's register fields carry Z_to_bv's proofs: equal to the literals by bv_eq, not by reflexivity *)
Lemma cn_dec_ret1 : decode_any (Z_to_bv 32 330643) = Some (OpImm ALU_ADD 23%bv 10%bv 0%bv, 4%Z).
Proof. vm_compute. f_equal. f_equal. f_equal; apply bv_eq; reflexivity. Qed.
Lemma cn_dec_j1 : decode_any (Z_to_bv 32 163577967) = Some (Jal 0%bv 156%bv, 4%Z).
Proof. vm_compute. f_equal. f_equal. f_equal; apply bv_eq; reflexivity. Qed.
Lemma cn_dec_ret2 : decode_any (Z_to_bv 32 330899) = Some (OpImm ALU_ADD 25%bv 10%bv 0%bv, 4%Z).
Proof. vm_compute. f_equal. f_equal. f_equal; apply bv_eq; reflexivity. Qed.
Lemma cn_dec_ret3 : decode_any (Z_to_bv 32 330259) = Some (OpImm ALU_ADD 20%bv 10%bv 0%bv, 4%Z).
Proof. vm_compute. f_equal. f_equal. f_equal; apply bv_eq; reflexivity. Qed.
Lemma cn_rd_nz : bv_eqb (23%bv : bv 5) 0 = false /\ bv_eqb (25%bv : bv 5) 0 = false /\ bv_eqb (20%bv : bv 5) 0 = false.
Proof. vm_compute. repeat split. Qed.
Lemma cn_signed0 : bv_signed (0%bv : bv 12) = 0.
Proof. vm_compute. reflexivity. Qed.
Lemma cn_k_ok :
  (0 <= CN_OFF + CN_RET1 /\ CN_OFF + CN_RET1 + 4 < 2 ^ 40) /\
  (0 <= CN_OFF + CN_RET1 + 4 /\ CN_OFF + CN_RET1 + 4 + 4 < 2 ^ 40) /\
  (0 <= CN_OFF + CN_RET2 /\ CN_OFF + CN_RET2 + 4 < 2 ^ 40) /\
  (0 <= CN_OFF + CN_RET3 /\ CN_OFF + CN_RET3 + 4 < 2 ^ 40).
Proof. vm_compute. repeat split; congruence. Qed.
(* the return addresses at the image's text base: aligned and above the first page *)
Lemma cn_ret_al :
  ((A_prog_base + CN_OFF + CN_RET1) mod 4 = 0 /\ 4096 <= A_prog_base + CN_OFF + CN_RET1) /\
  ((A_prog_base + CN_OFF + CN_RET2) mod 4 = 0 /\ 4096 <= A_prog_base + CN_OFF + CN_RET2) /\
  ((A_prog_base + CN_OFF + CN_RET3) mod 4 = 0 /\ 4096 <= A_prog_base + CN_OFF + CN_RET3).
Proof. vm_compute. repeat split; congruence. Qed.
Lemma cn_btgt_j1 : btgt (Z_to_bv 64 (A_prog_base + (CN_OFF + CN_RET1 + 4))) (bv_signed (156%bv : bv 21)) =
  Z_to_bv 64 (A_prog_base + CN_OFF + CN_READ2).
Proof. unfold btgt, v_addi. f_equal; vm_compute; reflexivity. Qed.

(* the callee-saved registers, by a boolean test *)
Definition cn_csb (z : Z) : bool :=
  (z =? 2) || (z =? 3) || (z =? 4) || (z =? 8) || (z =? 9) || ((18 <=? z) && (z <=? 27)).
Lemma cn_csb_ok : forall z, cn_csb z = true -> acallee_saved z.
Proof.
intros z. unfold cn_csb, acallee_saved.
destruct (Z.eqb_spec z 2); [intros _; lia|].
destruct (Z.eqb_spec z 3); [intros _; lia|].
destruct (Z.eqb_spec z 4); [intros _; lia|].
destruct (Z.eqb_spec z 8); [intros _; lia|].
destruct (Z.eqb_spec z 9); [intros _; lia|].
destruct (Z.leb_spec 18 z); destruct (Z.leb_spec z 27); cbn [orb andb]; intros Hb; try discriminate Hb; lia.
Qed.
(* after a call and one `mv rd, a0`: the callee-saved snapshot l is kept, rd holds v *)
Lemma cn_regsat_seat : forall regs regs' l l' (rd : bv 5) w v,
  cn_regsat regs l -> aregs_preserved regs regs' ->
  forallb (fun r : bv 5 => cn_csb (bv_unsigned r)) (map fst l) = true ->
  forallb (fun r : bv 5 => negb (bv_unsigned r =? bv_unsigned rd)) (map fst l) = true ->
  bv_eqb rd 0 = false -> w = w64 v -> incl l' ((rd, v) :: l) ->
  cn_regsat (regupd regs' rd w) l'.
Proof.
intros regs regs' l l' rd w v H HP Hc Hn Hrd Hw Hi.
apply (cn_regsat_incl _ ((rd, v) :: l) l'); [|exact Hi].
unfold cn_regsat. apply Forall_cons.
- cbn [fst snd]. rewrite getr_same; [exact Hw|]. intros E. rewrite E in Hrd. vm_compute in Hrd. discriminate Hrd.
- apply (cn_regsat_upd regs' l rd w).
  + intros Hin. rewrite forallb_forall in Hn. specialize (Hn rd Hin). rewrite Z.eqb_refl in Hn.
    cbn [negb] in Hn. discriminate Hn.
  + apply (cn_pres_regsat regs regs' l HP); [|exact H].
    apply Forall_forall. intros r Hr. apply cn_csb_ok. rewrite forallb_forall in Hc. exact (Hc r Hr).
Qed.
(* the regs 3 / 4 (gp / tp) of cn_base are not the three `mv` targets *)
Lemma cn_keep34 : forall regs (rd : bv 5) w, rd = 20%bv \/ rd = 23%bv \/ rd = 25%bv ->
  getr (regupd regs rd w) 3 = getr regs 3 /\ getr (regupd regs rd w) 4 = getr regs 4.
Proof.
intros regs rd w Hrd. split; apply getr_other; destruct Hrd as [->|[->| ->]];
  intros E; apply (f_equal bv_unsigned) in E; vm_compute in E; discriminate E.
Qed.
(* a snapshot list inside another (both written out): membership by search *)
Ltac cn_incl := let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; unfold cn_core, cn_s8 in Hx |- *; cbn [In app] in Hx |- *;
  repeat (destruct Hx as [<-|Hx]; [repeat (first [left; reflexivity | right])|]); destruct Hx.

Section cl. Context {rc : YM05.RunCeil} {PA : PAImg A_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
Lemma cn_ret_ceil : BASE + (CN_OFF + CN_RET1) < YM05.alloc_ceiling /\ BASE + (CN_OFF + CN_RET2) < YM05.alloc_ceiling /\
  BASE + (CN_OFF + CN_RET3) < YM05.alloc_ceiling.
Proof.
split; [|split].
- exact (pa_slot_lt_ceil_b (PL := PL_cno_A) (PI := PA) (CN_OFF + CN_RET1) ltac:(vm_compute; split; congruence)
    ltac:(vm_compute; reflexivity)).
- exact (pa_slot_lt_ceil_b (PL := PL_cno_A) (PI := PA) (CN_OFF + CN_RET2) ltac:(vm_compute; split; congruence)
    ltac:(vm_compute; reflexivity)).
- exact (pa_slot_lt_ceil_b (PL := PL_cno_A) (PI := PA) (CN_OFF + CN_RET3) ltac:(vm_compute; split; congruence)
    ltac:(vm_compute; reflexivity)).
Qed.
(* the call's three return-address premises at each slot *)
Lemma cn_ret1_ok : BASE = A_prog_base ->
  cn_pc CN_RET1 mod 4 = 0 /\ 4096 <= cn_pc CN_RET1 /\ cn_pc CN_RET1 < YM05.alloc_ceiling.
Proof.
intros H. pose proof (proj1 cn_ret_ceil) as Hc. destruct cn_ret_al as ((A1 & A2) & _).
unfold cn_pc. rewrite H in *. split; [exact A1|]. split; [exact A2|]. lia.
Qed.
Lemma cn_ret2_ok : BASE = A_prog_base ->
  cn_pc CN_RET2 mod 4 = 0 /\ 4096 <= cn_pc CN_RET2 /\ cn_pc CN_RET2 < YM05.alloc_ceiling.
Proof.
intros H. pose proof (proj1 (proj2 cn_ret_ceil)) as Hc. destruct cn_ret_al as (_ & (A1 & A2) & _).
unfold cn_pc. rewrite H in *. split; [exact A1|]. split; [exact A2|]. lia.
Qed.
Lemma cn_ret3_ok : BASE = A_prog_base ->
  cn_pc CN_RET3 mod 4 = 0 /\ 4096 <= cn_pc CN_RET3 /\ cn_pc CN_RET3 < YM05.alloc_ceiling.
Proof.
intros H. pose proof (proj2 (proj2 cn_ret_ceil)) as Hc. destruct cn_ret_al as (_ & _ & (A1 & A2)).
unfold cn_pc. rewrite H in *. split; [exact A1|]. split; [exact A2|]. lia.
Qed.
Lemma cn_dne : forall D : cn_in, (cn_d1 D =? cn_d2 D) = false /\ (cn_d1 D =? cn_d3 D) = false /\
  (cn_d2 D =? cn_d1 D) = false /\ (cn_d2 D =? cn_d3 D) = false /\
  (cn_d3 D =? cn_d1 D) = false /\ (cn_d3 D =? cn_d2 D) = false.
Proof.
intros D. unfold cn_d1, cn_d2, cn_d3.
repeat match goal with |- _ /\ _ => split end; apply Z.eqb_neq; lia.
Qed.
(* two distinct struct slots: both in the frame's struct area, and 56 bytes apart *)
Lemma cn_d_sep : forall (D : cn_in) d0 d, (d0 = cn_d1 D \/ d0 = cn_d2 D \/ d0 = cn_d3 D) ->
  (d = cn_d1 D \/ d = cn_d2 D \/ d = cn_d3 D) -> d0 <> d ->
  cn_F D + 32 <= d0 /\ d0 + 56 <= cn_F D + 280 /\ (d0 + 56 <= d \/ d + 56 <= d0).
Proof. intros D d0 d H0 H Hne. unfold cn_d1, cn_d2, cn_d3 in *. lia. Qed.

(* the call's register premise, read off each call state's snapshot *)
Lemma cn_call_regs1 : forall (D : cn_in) regs r1 r3,
  cn_regsat regs (cn_core D ++ [cn_s8; (1%bv, cn_pc CN_RET1); (10%bv, r1); (11%bv, cn_size D); (12%bv, cn_d1 D);
                                (19%bv, cn_d3 D); (20%bv, cn_size D); (21%bv, cn_d2 D); (22%bv, r3); (23%bv, -1);
                                (25%bv, cn_d1 D); (26%bv, r1)]) ->
  cn_regsat regs (cn_core D ++ [(1%bv, cn_pc CN_RET1); (10%bv, r1); (11%bv, cn_size D); (12%bv, cn_d1 D)]).
Proof. intros D regs r1 r3 H. apply (cn_regsat_incl regs _ _ H). cn_incl. Qed.
Lemma cn_call_regs2 : forall (D : cn_in) regs r1 r2 r3 rc1,
  cn_regsat regs (cn_core D ++ [cn_s8; (1%bv, cn_pc CN_RET2); (10%bv, r2); (11%bv, cn_size D); (12%bv, cn_d2 D);
                                (19%bv, cn_d3 D); (20%bv, cn_size D); (21%bv, cn_d2 D); (22%bv, r3); (23%bv, rc1);
                                (25%bv, cn_d1 D); (26%bv, r1)]) ->
  cn_regsat regs (cn_core D ++ [(1%bv, cn_pc CN_RET2); (10%bv, r2); (11%bv, cn_size D); (12%bv, cn_d2 D)]).
Proof. intros D regs r1 r2 r3 rc1 H. apply (cn_regsat_incl regs _ _ H). cn_incl. Qed.
Lemma cn_call_regs3 : forall (D : cn_in) regs r1 r3 rc1 rc2,
  cn_regsat regs (cn_core D ++ [cn_s8; (1%bv, cn_pc CN_RET3); (10%bv, r3); (11%bv, cn_size D); (12%bv, cn_d3 D);
                                (19%bv, cn_d3 D); (20%bv, cn_size D); (21%bv, 1); (22%bv, r3); (23%bv, rc1);
                                (25%bv, rc2); (26%bv, r1)]) ->
  cn_regsat regs (cn_core D ++ [(1%bv, cn_pc CN_RET3); (10%bv, r3); (11%bv, cn_size D); (12%bv, cn_d3 D)]).
Proof. intros D regs r1 r3 rc1 rc2 H. apply (cn_regsat_incl regs _ _ H). cn_incl. Qed.

(* the next cut's snapshot after the call (aregs_preserved) and the `mv`: rc1 in s7, rc2 in s9, rc3 in s4 *)
Lemma cn_seat1 : forall (D : cn_in) regs regs' r1 r3 rcv,
  cn_regsat regs (cn_core D ++ [cn_s8; (1%bv, cn_pc CN_RET1); (10%bv, r1); (11%bv, cn_size D); (12%bv, cn_d1 D);
                                (19%bv, cn_d3 D); (20%bv, cn_size D); (21%bv, cn_d2 D); (22%bv, r3); (23%bv, -1);
                                (25%bv, cn_d1 D); (26%bv, r1)]) ->
  aregs_preserved regs regs' -> getr regs' 10 = w64 rcv ->
  cn_regsat (regupd regs' 23%bv (getr regs' 10%bv))
    (cn_core D ++ [cn_s8; (19%bv, cn_d3 D); (20%bv, cn_size D); (21%bv, cn_d2 D); (22%bv, r3);
                   (23%bv, rcv); (25%bv, cn_d1 D); (26%bv, r1)]).
Proof.
intros D regs regs' r1 r3 rcv H HP H10.
apply (cn_regsat_seat regs regs' (cn_core D ++ [cn_s8; (19%bv, cn_d3 D); (20%bv, cn_size D); (21%bv, cn_d2 D);
                                                (22%bv, r3); (25%bv, cn_d1 D); (26%bv, r1)]) _ 23%bv _ rcv);
  [apply (cn_regsat_incl regs _ _ H); cn_incl | exact HP | vm_compute; reflexivity | vm_compute; reflexivity
  | exact (proj1 cn_rd_nz) | exact H10 | cn_incl].
Qed.
Lemma cn_seat2 : forall (D : cn_in) regs regs' r1 r2 r3 rc1 rcv,
  cn_regsat regs (cn_core D ++ [cn_s8; (1%bv, cn_pc CN_RET2); (10%bv, r2); (11%bv, cn_size D); (12%bv, cn_d2 D);
                                (19%bv, cn_d3 D); (20%bv, cn_size D); (21%bv, cn_d2 D); (22%bv, r3); (23%bv, rc1);
                                (25%bv, cn_d1 D); (26%bv, r1)]) ->
  aregs_preserved regs regs' -> getr regs' 10 = w64 rcv ->
  cn_regsat (regupd regs' 25%bv (getr regs' 10%bv))
    (cn_core D ++ [cn_s8; (19%bv, cn_d3 D); (20%bv, cn_size D); (21%bv, cn_d2 D); (22%bv, r3);
                   (23%bv, rc1); (25%bv, rcv); (26%bv, r1)]).
Proof.
intros D regs regs' r1 r2 r3 rc1 rcv H HP H10.
apply (cn_regsat_seat regs regs' (cn_core D ++ [cn_s8; (19%bv, cn_d3 D); (20%bv, cn_size D); (21%bv, cn_d2 D);
                                                (22%bv, r3); (23%bv, rc1); (26%bv, r1)]) _ 25%bv _ rcv);
  [apply (cn_regsat_incl regs _ _ H); cn_incl | exact HP | vm_compute; reflexivity | vm_compute; reflexivity
  | exact (proj1 (proj2 cn_rd_nz)) | exact H10 | cn_incl].
Qed.
Lemma cn_seat3 : forall (D : cn_in) regs regs' r1 r3 rc1 rc2 rcv,
  cn_regsat regs (cn_core D ++ [cn_s8; (1%bv, cn_pc CN_RET3); (10%bv, r3); (11%bv, cn_size D); (12%bv, cn_d3 D);
                                (19%bv, cn_d3 D); (20%bv, cn_size D); (21%bv, 1); (22%bv, r3); (23%bv, rc1);
                                (25%bv, rc2); (26%bv, r1)]) ->
  aregs_preserved regs regs' -> getr regs' 10 = w64 rcv ->
  cn_regsat (regupd regs' 20%bv (getr regs' 10%bv))
    (cn_core D ++ [cn_s8; (19%bv, cn_d3 D); (20%bv, rcv); (21%bv, 1); (22%bv, r3);
                   (23%bv, rc1); (25%bv, rc2); (26%bv, r1)]).
Proof.
intros D regs regs' r1 r3 rc1 rc2 rcv H HP H10.
apply (cn_regsat_seat regs regs' (cn_core D ++ [cn_s8; (19%bv, cn_d3 D); (21%bv, 1); (22%bv, r3); (23%bv, rc1);
                                                (25%bv, rc2); (26%bv, r1)]) _ 20%bv _ rcv);
  [apply (cn_regsat_incl regs _ _ H); cn_incl | exact HP | vm_compute; reflexivity | vm_compute; reflexivity
  | exact (proj2 (proj2 cn_rd_nz)) | exact H10 | cn_incl].
Qed.

(* the register steps from each return site to the next cut *)
Lemma cn_run_ret1 : forall (fz : YK11.FPState) (W : world SEGS) regs mem md Q, BASE = A_prog_base ->
  (forall mat1 mat2, SRr SEGS W (@cn_cfg SEGS fz (cn_pc CN_READ2) (regupd regs 23%bv (getr regs 10%bv)) mem
     (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy md) mat1 md)) mat2
        (with_vm_backing (m_vm_lazy md) mat1 md))) Q) ->
  SRr SEGS W (@cn_cfg SEGS fz (cn_pc CN_RET1) regs mem md) Q.
Proof.
intros fz W regs mem md Q HB0 HK.
destruct cn_k_ok as ((K1a & K1b) & (K1c & K1d) & _).
unfold cn_cfg.
replace (w64 (cn_pc CN_RET1)) with (Z_to_bv 64 (BASE + (CN_OFF + CN_RET1))) by (unfold w64, cn_pc; f_equal; lia).
apply (cn_step_addi (fz := fz) W regs mem md Q 330643 (CN_OFF + CN_RET1) 23%bv 10%bv 0%bv cn_pl_ret1 cn_dec_ret1
  (proj1 cn_rd_nz) K1a K1b).
intros mat1. rewrite cn_signed0, cn_v_addi0.
apply (cn_step_j (fz := fz) W _ mem _ Q 163577967 (CN_OFF + CN_RET1 + 4) (cn_pc CN_READ2) 156%bv cn_pl_j1 cn_dec_j1
  K1c K1d).
- unfold cn_pc. rewrite HB0. exact cn_btgt_j1.
- intros mat2. exact (HK mat1 mat2).
Qed.
Lemma cn_run_ret2 : forall (fz : YK11.FPState) (W : world SEGS) regs mem md Q,
  (forall mat1, SRr SEGS W (@cn_cfg SEGS fz (cn_pc CN_READ3) (regupd regs 25%bv (getr regs 10%bv)) mem
     (with_vm_backing (m_vm_lazy md) mat1 md)) Q) ->
  SRr SEGS W (@cn_cfg SEGS fz (cn_pc CN_RET2) regs mem md) Q.
Proof.
intros fz W regs mem md Q HK.
destruct cn_k_ok as (_ & _ & (K2a & K2b) & _).
unfold cn_cfg.
replace (w64 (cn_pc CN_RET2)) with (Z_to_bv 64 (BASE + (CN_OFF + CN_RET2))) by (unfold w64, cn_pc; f_equal; lia).
apply (cn_step_addi (fz := fz) W regs mem md Q 330899 (CN_OFF + CN_RET2) 25%bv 10%bv 0%bv cn_pl_ret2 cn_dec_ret2
  (proj1 (proj2 cn_rd_nz)) K2a K2b).
intros mat1. rewrite cn_signed0, cn_v_addi0.
replace (Z_to_bv 64 (BASE + (CN_OFF + CN_RET2 + 4))) with (w64 (cn_pc CN_READ3))
  by (unfold w64, cn_pc, CN_RET2, CN_READ3; f_equal; lia).
exact (HK mat1).
Qed.
Lemma cn_run_ret3 : forall (fz : YK11.FPState) (W : world SEGS) regs mem md Q,
  (forall mat1, SRr SEGS W (@cn_cfg SEGS fz (cn_pc CN_CMP) (regupd regs 20%bv (getr regs 10%bv)) mem
     (with_vm_backing (m_vm_lazy md) mat1 md)) Q) ->
  SRr SEGS W (@cn_cfg SEGS fz (cn_pc CN_RET3) regs mem md) Q.
Proof.
intros fz W regs mem md Q HK.
destruct cn_k_ok as (_ & _ & _ & (K3a & K3b)).
unfold cn_cfg.
replace (w64 (cn_pc CN_RET3)) with (Z_to_bv 64 (BASE + (CN_OFF + CN_RET3))) by (unfold w64, cn_pc; f_equal; lia).
apply (cn_step_addi (fz := fz) W regs mem md Q 330259 (CN_OFF + CN_RET3) 20%bv 10%bv 0%bv cn_pl_ret3 cn_dec_ret3
  (proj2 (proj2 cn_rd_nz)) K3a K3b).
intros mat1. rewrite cn_signed0, cn_v_addi0.
replace (Z_to_bv 64 (BASE + (CN_OFF + CN_RET3 + 4))) with (w64 (cn_pc CN_CMP))
  by (unfold w64, cn_pc, CN_RET3, CN_CMP; f_equal; lia).
exact (HK mat1).
Qed.
End cl.

(* ==== 3. the call ==== *)
Section rpn. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Existing Instance prh_img_A.
Context {PA : PAImg A_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation VAL := (@pa_val _ A_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
Hypothesis IMG : cn_img B.
Variable CTX0 : list (list Z).
(* The text of parse_noting (PRH_FnCheck.v :608-, restated for the re-hiding move: it concludes SRr' SEGS RZ, its post
   fpostFbm is PRH_Base.v's family at wle' SEGS RZ, and it takes the hull budget premise and states hull_used first in
   its post; the post-implication form at the wild budget prh_wk F_parse_noting = 2), for ANY float state *)
Hypothesis HPN : forall fz : YK11.FPState,
  @tparse_noting_specX fz rc ci cp prh_img_A RL A_prog_listing PA B ARx SK CTX0.
(* the journal from entry at the re-hiding relation (every journal of this file lies after or across a free) *)
#[local] Notation AJW := (ajournal_xwR (SK := SK) SEGS B prh_pst ARx (wle' SEGS RZ)).

(* ---- THE PROGRESS FACT across a call (the Base's cn_prog: the live set and the run position after the events made
   since entry; the B' kit's cnb_prog_eq / cnb_prog_app, lib/B/Prog/Cno102B_Ro.v, with cn_ names) ---- *)
(* an equal event list (the pieces' regrouping at a skipped reading) *)
Lemma cn_prog_eq : forall D E E' S, E = E' -> cn_prog D E S -> cn_prog D E' S.
Proof. intros D E E' S <- H. exact H. Qed.
(* a callee that makes events E' (a post-implication text: the exact live set after E' and, for any run position at
   its entry state whose next events are E', the position after them) extends the fact by E' *)
Lemma cn_prog_app : forall D E E' S S',
  cn_prog D E S ->
  Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S'))
    (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) E') ->
  (forall (sm : list Z -> Z * Z) (x0 : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
     (H0 : list Z) (hist : list YG00.chunk),
     PresetRoomPos.iface_room_pos sm x0 os i H0 hist S -> prh_run_at sm x0 os i E' ->
     exists hist', PresetRoomPos.iface_room_pos sm x0 os (i + length E')%nat H0 hist' S') ->
  cn_prog D (E ++ E') S'.
Proof.
intros D E E' S S' (HL & HP) HL' HP'. split.
- rewrite PresetReqAt.hlive_from_app. apply (Permutation_trans HL').
  apply PresetReqAtNoMiss.hlive_from_perm. exact HL.
- intros sm x0 os i H0 hist Hpos Hrun. apply prh_run_at_app_iff in Hrun as (R1 & R2).
  destruct (HP sm x0 os i H0 hist Hpos R1) as (hist1 & Hpos1).
  destruct (HP' sm x0 os (i + length E)%nat H0 hist1 Hpos1 R2) as (hist2 & Hpos2).
  exists hist2. rewrite length_app, Nat.add_assoc. exact Hpos2.
Qed.

(* the reading's slot in the three structs: the struct at d takes the reading's state st, the other two keep theirs *)
Definition cn_upd_ok (D : cn_in) (d : Z) (st st1 st2 st3 : cn_st) (u : cn_st * cn_st * cn_st) : Prop :=
  Permutation (cn_Dof (fst (fst u)) ++ cn_Dof (snd (fst u)) ++ cn_Dof (snd u))
    (cn_Dof st ++ cn_Dof st1 ++ cn_Dof st2 ++ cn_Dof st3) /\
  (if d =? cn_d1 D then st1 = None /\ fst (fst u) = st else fst (fst u) = st1) /\
  (if d =? cn_d2 D then st2 = None /\ snd (fst u) = st else snd (fst u) = st2) /\
  (if d =? cn_d3 D then st3 = None /\ snd u = st else snd u = st3).

(* cn_base (at the re-hiding relation: used only after a call of parse_noting) at registers that keep gp / tp *)
Lemma cn_base_regs : forall D fxk ly S Hp W regs regs2 mem md k wk,
  cn_baseR (fx := fx) B ARx (wle' SEGS RZ) D fxk ly S Hp W regs mem md k wk -> getr regs2 3 = getr regs 3 ->
  getr regs2 4 = getr regs 4 -> cn_baseR (fx := fx) B ARx (wle' SEGS RZ) D fxk ly S Hp W regs2 mem md k wk.
Proof.
intros D fxk ly S Hp W regs regs2 mem md k wk (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8) E3 E4.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
split; [rewrite E3; exact H6|]. split; [rewrite E4; exact H7|]. exact H8.
Qed.

(* the call of a callee whose text concludes in apost_base_xbFR PW at wle' SEGS RZ (a budgeted post at the re-hiding
   relation: the callee's journal at a wild budget WS1 with PW WS1) at window STK_parse_noting below sp = s1,
   footprint the struct [d, d + 56) in the function's own frame: YCbqGwild.v aj_call_xbF_sp's composition over a
   concrete call state (its st_ok premise only seats a symbolic state); the cut's journal at its budget WS0 and the
   callee's compose at WS0 ++ WS1 (YCbqG.ajournal_xw_subR at wle' SEGS RZ, transitive by wle'_trans) *)
Lemma cn_call_x : forall (W : world SEGS) fxk regs mem md D ly S Hp k WS0 d (PW : list (list Z) -> Prop)
  (Q : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  AJW STK_check_no_overread (cn_sp0 D) [] (ci_ly D) (ci_S D) (ci_Hp D) (ci_W D) (ci_mem D) (ci_md D)
    [(CN_CID, ci_fpos D)] ly S Hp W mem md k WS0 ->
  spZ regs = cn_S1 D ->
  STK_check_no_overread = 27424 -> STK_parse_noting = 27216 ->
  frame_addr ly CN_CID (ci_fpos D) <= d -> d + 56 <= frame_addr ly CN_CID (ci_fpos D) + fs_frame_bytes CN_CID ->
  SRr' SEGS RZ W (@cn_cfg SEGS fxk (SIGMA AS_parse_noting) regs mem md)
    (YCbqGwild.apost_base_xbFR (fx := fxk) (SK := SK) SEGS B prh_pst ARx (wle' SEGS RZ) PW STK_parse_noting
       [(d, d + 56)] regs ly S Hp W mem md Q) ->
  SRr' SEGS RZ W (@cn_cfg SEGS fxk (SIGMA AS_parse_noting) regs mem md)
    (fun W2 c2 => exists (fx' : YK11.FPState) ly2 S2 Hp2 regs2 mem2 md2 k1 WS1,
       c2 = mkCfg (@YK11.mkst fx' regs2 (getr regs 1) mem2 (YK11.seg_rom SEGS)) md2 /\
       frm_zero (@YK11.fp_csr fx') /\ fregs_kept_x fxk fx' /\ PW WS1 /\
       AJW STK_check_no_overread (cn_sp0 D) [] (ci_ly D) (ci_S D) (ci_Hp D) (ci_W D) (ci_mem D) (ci_md D)
         [(CN_CID, ci_fpos D)] ly2 S2 Hp2 W2 mem2 md2 (k + k1) (WS0 ++ WS1) /\
       AJW STK_parse_noting (cn_S1 D) [(d, d + 56)] ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 /\
       aregs_preserved regs regs2 /\ Q ly2 S2 Hp2 W2 regs2 mem2 md2).
Proof.
intros W fxk regs mem md D ly S Hp k WS0 d PW Q HJ Hsp ES1 ES2 Hd1 Hd2 HT.
pose proof (ajxR_stk HJ) as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & _). rewrite ES1 in Hslo.
assert (Hsp0 : 0 <= cn_sp0 D - 192) by lia.
assert (Hs1 : cn_S1 D = cn_sp0 D - 192 - (cn_sp0 D - 192) mod 32) by (unfold cn_S1; apply cn_land32; exact Hsp0).
pose proof (Z.div_mod (cn_sp0 D - 192) 32 ltac:(lia)) as Em32.
pose proof (Z.mod_pos_bound (cn_sp0 D - 192) 32 ltac:(lia)) as Bm32.
pose proof (Z.div_mod (cn_sp0 D) 16 ltac:(lia)) as Em16.
assert (HS1 : cn_S1 D = cn_sp0 D - 192 \/ cn_S1 D = cn_sp0 D - 208) by (rewrite Hs1; lia).
clear Em32 Bm32 Em16 Hs1.
eapply SRr'_mono; [exact HT|].
cbv beta. intros W2 c2 _ (fx' & ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & WS1 & -> & HFZ & HFK & HPW & HJ1 & HP2 & HQ).
rewrite Hsp in HJ1.
exists fx', ly2, S2, Hp2, regs2, mem2, md2, k1, WS1. split; [reflexivity|]. split; [exact HFZ|]. split; [exact HFK|].
split; [exact HPW|].
split; [|split; [exact HJ1 | split; [exact HP2 | exact HQ]]].
assert (Hle1 : cn_sp0 D - STK_check_no_overread <= cn_S1 D - STK_parse_noting) by (rewrite ES1, ES2; lia).
assert (Hle2 : cn_S1 D <= cn_sp0 D) by lia.
assert (HFsub : fp_sub_x B STK_check_no_overread (cn_sp0 D) [] [(d, d + 56)] (ci_ly D) (ci_S D)
                  [(CN_CID, ci_fpos D)] ly S).
{ intros a (rr & Hin & Hrr). destruct Hin as [<-|[]]. cbn [fst snd] in Hrr.
  right. right. left. exists (CN_CID, ci_fpos D). split; [left; reflexivity|].
  unfold in_zr, frame_rng. cbn [fst snd]. lia. }
exact (ajournal_xw_subR (SK := SK) SEGS B prh_pst ARx LAWS pa_segs_low (wle' SEGS RZ) (wle'_trans SEGS RZ)
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HJ1 Hle1 Hle2 HFsub).
Qed.

(* THE GENERIC CALL STEP: at the callee's entry (ra = ret), one reading of the copy r into the struct d, after the
   events E made since entry and at the wild budget wk (wk + 2 <= 6: room for this reading's 2), the cut's journal at
   the re-hiding relation wle' SEGS RZ and its hull budget for this reading's all-granted events followed by Hrest; it
   ends at ret at budget wk + 2 (journal at wle') with the events E ++ the reading's under its grant og (cn_grant: og
   matches the instance's outcomes; no premise), g_ran_out = 1 exactly when og runs out, the struct against the
   model's reading at og (cn_rd) and its free-order tie at og (cn_fo), every other struct's free-order tie kept, and
   the hull budget Hrest at the post state *)
Lemma cn_pn_call : forall P, srr_inv_laws SEGS P -> srr_inv_call SEGS P -> srr_inv_mn SEGS P ->
  forall D fxk ly S Hp W regs mem md k (wk : nat) Lam peak cnt (nr : nat) r1 r2 r3 st1 st2 st3 r d ret E
    (Hrest : list PresetReqAt.hev) (upd : cn_st -> cn_st * cn_st * cn_st),
  cn_pre (fx := fx) B ARx CTX0 D ->
  cn_baseR (fx := fx) B ARx (wle' SEGS RZ) D fxk ly S Hp W regs mem md k wk -> (wk + 2 <= 6)%nat ->
  cn_regsat regs (cn_core D ++ [(1%bv, ret); (10%bv, r); (11%bv, cn_size D); (12%bv, d)]) ->
  ret mod 4 = 0 -> 4096 <= ret -> ret < YM05.alloc_ceiling ->
  cn_slots D W mem r1 r2 ->
  (r = r1 \/ r = r2 \/ r = r3) -> r <> 0 ->
  (d = cn_d1 D \/ d = cn_d2 D \/ d = cn_d3 D) ->
  (nr <= 2)%nat ->
  cn_prog D E S ->
  (exists R, ck_cno_evs ReaderRes.jr_strtod (ci_x D) None None None = E ++ cn_pe D None ++ R) ->
  cn_mid B D ly S Hp W mem Lam peak cnt 0 0 nr r1 r2 r3 st1 st2 st3 ->
  (forall st, cn_upd_ok D d st st1 st2 st3 (upd st)) ->
  PresetHullBudget.hull_budget S (PresetReqAt.parse_evs ReaderRes.jr_strtod (ci_x D) [] ++ Hrest) ->
  P mem ->
  SRr' SEGS RZ W (@cn_cfg SEGS fxk (SIGMA AS_parse_noting) regs mem md) (fun W' c' =>
    exists fx' ly' S' Hp' regs' mem' md' k' Lam' peak' cnt' ran' rcv st og,
      c' = @cn_cfg SEGS fx' ret regs' mem' md' /\
      cn_baseR (fx := fx) B ARx (wle' SEGS RZ) D fx' ly' S' Hp' W' regs' mem' md' k' (wk + 2) /\
      aregs_preserved regs regs' /\ getr regs' 10 = w64 rcv /\
      cn_slots D W' mem' r1 r2 /\
      cn_prog D (E ++ cn_pe D og) S' /\ ran' = (if cn_ro D og then 1 else 0) /\
      cn_mid B D ly' S' Hp' W' mem' Lam' peak' cnt' ran' 0 (Datatypes.S nr) r1 r2 r3
        (fst (fst (upd st))) (snd (fst (upd st))) (snd (upd st)) /\
      cn_res D ran' rcv st /\ cn_rd D og st /\ cn_fo D W' mem' Lam' og d st /\
      (forall o d0 st0, (d0 = cn_d1 D /\ st0 = st1 \/ d0 = cn_d2 D /\ st0 = st2 \/ d0 = cn_d3 D /\ st0 = st3) ->
         d0 <> d -> cn_fo D W mem Lam o d0 st0 -> cn_fo D W' mem' Lam' o d0 st0) /\
      PresetHullBudget.hull_budget S' Hrest /\
      P mem').
Proof.
intros P PL PC PM D fxk ly S Hp W regs mem md k wk Lam peak cnt nr r1 r2 r3 st1 st2 st3 r d ret E Hrest upd
  HPRE HB Hwk HR Hret4 Hret0 HretC HSL Hr Hr0 Hd Hnr HPROG HSPLIT HM HU HHB HP.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@cf_head_nonneg cp) as Hh0.
assert (ES : STK_parse_noting = 27216 /\ STK_check_no_overread = 27424) by (vm_compute; split; reflexivity).
destruct ES as [ES2 ES1].
assert (Efb : fs_frame_bytes CN_CID = 512) by (vm_compute; reflexivity).
(* ---- the entry, cn_pre read by name ---- *)
pose proof (cn_pre_fpre (fx := fx) B ARx CTX0 D HPRE) as (HPRE0 & HRO0 & HHI0 & HRA0 & HFZ0).
destruct HPRE0 as (HAR0 & Hrok0 & Hra0 & Hgp0 & Htp0 & Hstk0 & Hwin0 & Hch0 & Hqt0).
pose proof (cn_pre_univ (fx := fx) B ARx CTX0 D HPRE) as HCL.
pose proof (cn_pre_size (fx := fx) B ARx CTX0 D HPRE) as Hsz.
pose proof (cn_pre_cnt (fx := fx) B ARx CTX0 D HPRE) as HCNT0.
pose proof (cn_pre_most (fx := fx) B ARx CTX0 D HPRE) as HRQ0.
pose proof (cn_pre_maxpj (fx := fx) B ARx CTX0 D HPRE) as HRQ.
pose proof (cn_pre_frames (fx := fx) B ARx CTX0 D HPRE) as HFR0.
pose proof (cn_pre_pksec (fx := fx) B ARx CTX0 D HPRE) as HPKS0.
pose proof (cn_pre_pk24 (fx := fx) B ARx CTX0 D HPRE) as HPK240.
(* ---- the cut; its journal read BY NAME (YCbqG's ajxR_ projections, at wle' SEGS RZ) ---- *)
destruct HB as (HFZ & HFK & HJcn & HFRM & HSAV & HG3 & HG4 & HRO).
(* the text's wild room for this reading, from cn_pre's and the journal so far (the Base's cn_room_pnR) *)
pose proof (cn_room_pnR (fx := fx) B ARx (wle' SEGS RZ) CTX0 D ly S Hp W mem md k wk HPRE HJcn Hwk) as HWR.
destruct HJcn as (WS0 & HJ & HWB0).
destruct HM as (HC1 & HC2 & HC3 & HLED & HPK & HCNT & HROOM & HLIVE & HO1 & HO2 & HO3 & HD1 & HD2 & HD3 &
  HPL & HPB & HFRESH).
pose proof (ajxR_ar HJ) as HAR. pose proof (ajxR_ly HJ) as Hly. pose proof (ajxR_k HJ) as Hk.
pose proof (ajxR_hi HJ) as F1. pose proof (ajxR_stk HJ) as Hstat.
destruct Hstat as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof Hly as (_ & _ & _ & _ & _ & EF & _ & _ & Etop & Eslo & Eshi & _).
rewrite ES1 in F1, Hslo, Hbot.
assert (Hs1 : cn_S1 D = cn_sp0 D - 192 - (cn_sp0 D - 192) mod 32) by (unfold cn_S1; apply cn_land32; lia).
pose proof (Z.div_mod (cn_sp0 D - 192) 32 ltac:(lia)) as Em32.
pose proof (Z.mod_pos_bound (cn_sp0 D - 192) 32 ltac:(lia)) as Bm32.
pose proof (Z.div_mod (cn_sp0 D) 16 ltac:(lia)) as Em16.
assert (HS1 : cn_S1 D = cn_sp0 D - 192 \/ cn_S1 D = cn_sp0 D - 208) by (rewrite Hs1; lia).
clear Em32 Bm32 Em16 Hs1.
assert (Hs1b : cn_sp0 D - 208 <= cn_S1 D <= cn_sp0 D - 192) by lia.
(* the frame and the struct d in it *)
assert (Hin3 : In (CN_CID, ci_fpos D) (frames S)) by (rewrite (proj1 HFRM); left; reflexivity).
assert (EFa : frame_addr ly CN_CID (ci_fpos D) = cn_F D) by (unfold cn_F, frame_addr; rewrite EF; reflexivity).
destruct (alx_frames SEGS B ARx LAWS ly S Hp W mem md CN_CID (ci_fpos D) HAR Hin3) as (HF32 & HFapp & HFb & HFs).
destruct (frames_bounds_x SEGS B ARx LAWS ly S Hp W mem md CN_CID (ci_fpos D) HAR Hin3) as (HF4096 & HFceil & _).
rewrite EFa in HF32, HFapp, HFb, HFs, HF4096, HFceil. rewrite Efb in HFapp, HFb, HFs, HFceil.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
assert (Hdd : cn_F D + 32 <= d /\ d + 56 <= cn_F D + 280 /\ d mod 32 = 0).
{ unfold cn_d1, cn_d2, cn_d3 in Hd.
  destruct Hd as [-> | [-> | ->]]; (split; [lia|]); (split; [lia|]).
  - apply (cn_mod32_at (cn_F D) _ 1 HF32). lia.
  - apply (cn_mod32_at (cn_F D) _ 4 HF32). lia.
  - apply (cn_mod32_at (cn_F D) _ 7 HF32). lia. }
assert (Hdop : cn_open W mem d) by (destruct Hd as [-> | [-> | ->]]; assumption).
(* the registers *)
assert (Hinl : forall (rr : bv 5) v, In (rr, v) (cn_core D ++ [(1%bv, ret); (10%bv, r); (11%bv, cn_size D); (12%bv, d)]) ->
  getr regs rr = w64 v) by (intros rr v Hpi; exact (cn_regsat_get regs _ rr v HR Hpi)).
assert (Hsp : spZ regs = cn_S1 D).
{ unfold spZ. rewrite (Hinl 2%bv (cn_S1 D)) by (unfold cn_core; cbn [app In]; tauto). unfold w64.
  rewrite unsigned_lit_small by lia. reflexivity. }
assert (Hs0 : s0Z regs = cn_sp0 D).
{ unfold s0Z. rewrite (Hinl 8%bv (cn_sp0 D)) by (unfold cn_core; cbn [app In]; tauto). unfold w64.
  rewrite unsigned_lit_small by lia. reflexivity. }
assert (Hra1 : getr regs 1 = w64 ret) by (exact (Hinl 1%bv ret ltac:(unfold cn_core; cbn [app In]; tauto))).
assert (Hraz : raZ regs = ret) by (unfold raZ; rewrite Hra1; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
assert (H10 : getr regs 10 = w64 r) by (exact (Hinl 10%bv r ltac:(unfold cn_core; cbn [app In]; tauto))).
assert (H11 : getr regs 11 = w64 (cn_size D)) by (exact (Hinl 11%bv (cn_size D) ltac:(unfold cn_core; cbn [app In]; tauto))).
assert (H12 : getr regs 12 = w64 d) by (exact (Hinl 12%bv d ltac:(unfold cn_core; cbn [app In]; tauto))).
(* the copy read *)
assert (HrC : cn_copy B D ly S Hp W mem r) by (destruct Hr as [-> | [-> | ->]]; assumption).
destruct HrC as [Hr00|(Hrb & HrHp & HrSRC)]; [exfalso; exact (Hr0 Hr00)|].
pose proof HrSRC as (HrBy & Hr4096 & HrCeil & HrAm & HrRA & HrHV).
(* the text's two room counts along the all-granted reading, from the count along check_no_overread's list *)
assert (HPKS : Z.of_nat (PresetRun.pkR YGcfRoomLive.rl_sec_req (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
    (PresetReqAt.parse_evs ReaderRes.jr_strtod (ci_x D) [])) <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV).
{ destruct HSPLIT as (R & ER). rewrite ER in HPKS0.
  pose proof (cn_pkR_mid YGcfRoomLive.rl_sec_req _ _ E (cn_pe D None) R (proj1 HPROG)) as Hm.
  unfold cn_pe in Hm, HPKS0. cbn [PresetRun.okof] in Hm, HPKS0. clear - Hm HPKS0. lia. }
assert (HPK24 : Z.of_nat (PresetRun.pkR (PresetRoom.in_cls YG00.kBatchClass) (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
    (PresetReqAt.parse_evs ReaderRes.jr_strtod (ci_x D) [])) <= PresetLiveBounds.L24 + PresetLiveBounds.DRV).
{ destruct HSPLIT as (R & ER). rewrite ER in HPK240.
  pose proof (cn_pkR_mid (PresetRoom.in_cls YG00.kBatchClass) _ _ E (cn_pe D None) R (proj1 HPROG)) as Hm.
  unfold cn_pe in Hm, HPK240. cbn [PresetRun.okof] in Hm, HPK240. clear - Hm HPK240. lia. }
(* counts and budget *)
assert (HLV0 : 0 <= PRH_FnPj.LIVE_pj_parse (ci_x D)).
{ unfold PRH_FnPj.LIVE_pj_parse. pose proof (cn_hpeak_nonneg (prhPj_ptrace (ci_x D))).
  assert (0 <= cf_head * (Z.of_nat (PjGrammar.calls (prhPj_ptrace (ci_x D))) + 1)) by (apply Z.mul_nonneg_nonneg; lia).
  lia. }
assert (Hnc : ck_ncalls (ci_x D) <= 2 * cn_size D + 2).
{ unfold ck_ncalls, cn_size, PjGrammar.ncalls. pose proof (PjGrammar.G7_4 ReaderRes.jr_strtod (ci_x D) []). lia. }
assert (Hnc0 : 0 <= ck_ncalls (ci_x D)) by (unfold ck_ncalls; lia).
assert (Hnrnc : Z.of_nat nr * ck_ncalls (ci_x D) <= 2 * ck_ncalls (ci_x D)) by (apply Z.mul_le_mono_nonneg_r; lia).
assert (Hsz0 : 0 <= cn_size D) by (unfold cn_size; lia).
assert (Hlv1 : blocks_bytes S + PRH_FnPj.LIVE_pj_parse (ci_x D) <= LIVE_MAX).
{ assert (H31 : 1 <= Z.of_nat (3 - nr)) by lia.
  pose proof (Z.mul_le_mono_nonneg_r 1 (Z.of_nat (3 - nr)) (PRH_FnPj.LIVE_pj_parse (ci_x D)) HLV0 H31) as HM1.
  set (NL := Z.of_nat (3 - nr) * PRH_FnPj.LIVE_pj_parse (ci_x D)) in *. lia. }
(* ---- the achain at the call: s0 = the entry sp, the saved ra / s0 at sp0 - 8 / sp0 - 16 ---- *)
assert (Hch : exists ch1, achain ly (aview SEGS (w_H W) mem) (spZ regs) (s0Z regs) ch1).
{ rewrite Hsp, Hs0.
  destruct (Z_lt_le_dec (cn_sp0 D) (ly_top ly - 16)) as [Hlt|Hge].
  - exists ((cn_sp0 D, raZ (ci_regs D), s0Z (ci_regs D)) :: ci_ch D).
    apply (achain_push ly (aview SEGS (w_H (ci_W D)) (ci_mem D)) (aview SEGS (w_H W) mem) (cn_sp0 D)
             (s0Z (ci_regs D)) (raZ (ci_regs D)) (ci_ch D) (cn_S1 D)).
    + apply (achain_ly_top (ci_ly D) ly); [exact Etop | exact Hch0].
    + lia.
    + intros a Ha. apply F1; lia.
    + pose proof (proj1 (Forall_forall _ _) HSAV (184, 1%bv) ltac:(cbn [In]; tauto)) as Esv. cbn [fst snd] in Esv.
      replace (cn_sp0 D - 8) with (cn_sp0 D - 192 + 184) by lia. exact Esv.
    + pose proof (proj1 (Forall_forall _ _) HSAV (176, 8%bv) ltac:(cbn [In]; tauto)) as Esv. cbn [fst snd] in Esv.
      replace (cn_sp0 D - 16) with (cn_sp0 D - 192 + 176) by lia. exact Esv.
    + exact Hra0.
    + lia.
    + apply Z.mod_divide in Hal16; [|lia]. apply Z.mod_divide; [lia|]. destruct Hal16 as [q Eq]. exists (2 * q). lia.
    + exact Hlt.
    + lia.
  - exists []. left. split; [right; left; lia | reflexivity]. }
destruct Hch as (ch1 & Hch).
(* ---- the text's premises ---- *)
assert (HPREX : afn_pre_x SEGS B ARx STK_parse_noting ly S Hp W regs mem md ch1).
{ apply (YCbqGwild.afn_pre_x_at_wR (SK := SK) SEGS B prh_pst ARx (wle' SEGS RZ) STK_check_no_overread (cn_sp0 D) []
    (ci_ly D) (ci_S D) (ci_Hp D) (ci_W D) (ci_mem D) (ci_md D) [(CN_CID, ci_fpos D)] ly S Hp W mem md k WS0 regs
    STK_parse_noting (cn_S1 D - cn_sp0 D) ch1 HJ).
  - lia.
  - destruct HS1 as [Es1|Es1]; rewrite Es1; [replace (cn_sp0 D - 192 - cn_sp0 D) with (-192) by lia
      | replace (cn_sp0 D - 208 - cn_sp0 D) with (-208) by lia]; reflexivity.
  - lia.
  - lia.
  - lia.
  - rewrite Hra1. apply ret_ok_even. unfold w64. rewrite unsigned_lit_small by lia. exact (cn_mod2 ret Hret4).
  - lia.
  - rewrite HG3. exact Hgp0.
  - rewrite HG4. exact Htp0.
  - exact Hch. }
assert (HFPRE : fpre (fx := fxk) B ARx STK_parse_noting ly S Hp W regs mem md ch1).
{ split; [exact HPREX|]. split; [exact HRO|]. split; [rewrite Hsp; lia|].
  split; [rewrite Hraz; exact HretC | exact HFZ]. }
assert (Hhome : PRH_FnReader.prhReader_home B ly S Hp Lam r (cn_size D)).
{ right. exists r, (cn_size D + 16). split; [exact Hrb|]. split; [exact HrHp|]. lia. }
assert (Hmr : Z.of_nat (PjRoundTrip.maxrun (ci_x D)) < 2 ^ 30).
{ pose proof (PjRoundTrip.G12_1 (ci_x D)). unfold cn_size in Hsz. lia. }
assert (Hout : ck_out_ok B STK_parse_noting ly S W regs mem d 56).
{ split.
  - exists CN_CID, (ci_fpos D). split; [exact Hin3|]. rewrite EFa, Efb. lia.
  - split; [lia|]. split; [lia|].
    split; [unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd; lia|].
    split; [|split; [exact (proj1 Hdop) | intros _; exact (proj2 Hdop)]].
    intros a Ha. destruct (HFb a ltac:(lia)) as (Hpr & Hno).
    split; [exact (apresent_writable SEGS _ _ _ Hpr)|]. split; [exact Hno|]. rewrite Hsp, ES2. lia. }
assert (Hfrl : Z.of_nat (length (frames S)) <= ck_FRAMES_CAP - FR_parse_noting).
{ rewrite (proj1 HFRM). cbn [length]. unfold FR_check_no_overread in HFR0. lia. }
assert (Hcntb : cnt + 2 * cn_size D + 2 < 2 ^ 64 - 1).
{ clear - HCNT HCNT0 Hnrnc Hnc Hnc0 Hsz Hnr. unfold cn_size in *. lia. }
(* the text's hull budget: this reading's all-granted events, the head of the cut's (no use before it) *)
assert (HHBt : PresetHullBudget.hull_budget S (PresetReqAt.parse_evs ReaderRes.jr_strtod (ci_x D) [])).
{ exact (PresetHullBudget.hull_budget_infix S S [] (PresetReqAt.parse_evs ReaderRes.jr_strtod (ci_x D) []) Hrest HHB
    (PresetHullBudget.hull_used_refl S [])). }
pose proof (HPN fxk (ci_most D) 0 ly S Hp W regs mem md ch1 r
  (ci_x D) d Lam peak cnt SIZE_MAXZ 0 HFPRE (PM mem HP) HCL H10 H11 H12 ltac:(unfold cn_size in Hsz; lia)
  ltac:(lia) ltac:(lia) HrSRC Hhome Hmr (cn_mod8 d (proj2 (proj2 Hdd))) Hout eq_refl HLED
  ltac:(unfold cn_size in Hcntb; exact Hcntb) Hlv1 HRQ HRQ0 Hfrl HFZ HROOM HWR HPKS HPK24 HHBt) as HT.
(* fpostFbm / fpostFb are PRH_Base.v's family at wle' SEGS RZ: the engine's apost_base_xbFR there *)
unfold fpostFbm, fpostFb in HT.
(* ---- the call ---- *)
eapply SRr'_mono; [exact (cn_call_x W fxk regs mem md D ly S Hp k WS0 d _ _ HJ Hsp ES1 ES2 ltac:(rewrite EFa; lia)
  ltac:(rewrite EFa, Efb; lia) HT)|].
cbv beta.
intros W2 c2 _ (fx' & ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & WS1 & Hc2 & HFZ' & HFK' & HWB1 & HJ2 & HJ1 & HP2 & HQ).
(* the text's inner post read BY NAME (PRH_FnCheck.v's record tpnP_R, through tpnP_R_of; the post does not read the
   model, so tpnP_R_of's md' is bound by name); fQmn's memnorm keep beside *)
destruct HQ as (HQ & Hmn).
apply tpnP_R_of with (md' := md2) in HQ as (Lam2 & peak2 & cnt2 & fail2 & ran2 & ok & res & tr & HPR).
pose proof (tpnP_hull HPR) as HHU. pose proof (tpnP_room HPR) as HROOM2. pose proof (tpnP_run HPR) as Hrun.
pose proof (tpnP_live HPR) as HLV2. pose proof (tpnP_pos HPR) as HPS2. pose proof (tpnP_oks HPR) as Hoks.
pose proof (tpnP_cnt HPR) as Hcnt2. pose proof (tpnP_fail HPR) as Hfa. pose proof (tpnP_peak HPR) as Hpk2.
pose proof (tpnP_ledger HPR) as HLED2. pose proof (tpnP_arm HPR) as Hres.
(* ---- what the callee's journal keeps ---- *)
pose proof (ajxR_ar HJ1) as HAR2. pose proof (ajxR_ly HJ1) as Hly1. pose proof (ajxR_frs HJ1) as Hfrs1.
pose proof (ajxR_hi HJ1) as G1. pose proof (ajxR_blk HJ1) as G2. pose proof (ajxR_img HJ1) as G3.
pose proof (ajxR_frm HJ1) as G4.
pose proof Hly1 as (_ & _ & _ & _ & _ & EF1 & _).
rewrite ES2 in G1.
assert (Hin3' : In (CN_CID, ci_fpos D) (frames S2)) by (rewrite Hfrs1; exact Hin3).
assert (EFa2 : frame_addr ly2 CN_CID (ci_fpos D) = cn_F D) by (rewrite <- EFa; unfold frame_addr; rewrite EF1; reflexivity).
destruct (alx_frames SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 CN_CID (ci_fpos D) HAR2 Hin3') as (_ & _ & HFb2 & HFs2).
rewrite EFa2, Efb in HFb2, HFs2.
assert (HnFP : forall a, inFP [(d, d + 56)] a -> d <= a < d + 56)
  by (intros a (rr & Hin & Hrr'); destruct Hin as [<-|[]]; cbn [fst snd] in Hrr'; exact Hrr').
assert (KFR : forall a, cn_F D <= a < cn_F D + 512 -> ~ (d <= a < d + 56) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha Hna. apply (G4 CN_CID (ci_fpos D) a Hin3).
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFa, Efb. lia.
  - intros Hf. exact (Hna (HnFP a Hf)). }
assert (KSH : forall a, shadow_addr (cn_F D) <= a < shadow_addr (cn_F D) + 64 ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha. apply (G4 CN_CID (ci_fpos D) a Hin3).
  - right. unfold in_zr. cbn [fst snd]. rewrite EFa, Efb. change (512 / 8) with 64. lia.
  - intros Hf. apply HnFP in Hf. unfold shadow_addr, SHADOW_OFF in Ha.
    pose proof (Z.div_mod (cn_F D) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (cn_F D) 8 ltac:(lia)). lia. }
assert (KST : forall a, cn_S1 D <= a < cn_sp0 D -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a)
  by (intros a Ha; apply G1; lia).
assert (KBL : forall p n i, In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly2 S2) -> 0 <= i < req_size n ->
  aview SEGS (w_H W2) mem2 (p + i) = aview SEGS (w_H W) mem (p + i)).
{ intros p n i H1 H2 Hi. apply (G2 p n i H1 H2 Hi). intros Hf. apply HnFP in Hf.
  apply (frame_not_block_x SEGS B ARx LAWS ly S Hp W mem md (CN_CID, ci_fpos D) p n (p + i) HAR Hin3 H1); [|lia].
  unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFa, Efb. lia. }
(* ---- the reading: fail stays SIZE_MAX, its calls at most the grammar's ---- *)
assert (Hfail2 : fail2 = SIZE_MAXZ).
{ destruct Hfa as [Fa1 Fa2]. unfold SIZE_MAXZ in *.
  destruct (Z_lt_le_dec (2 ^ 64 - 1) (cnt + Z.of_nat (PjGrammar.calls tr))) as [Hl|Hl].
  - apply Fa1. pose proof (prh_ledger_bounds B ly S Hp W mem Lam peak cnt (2 ^ 64 - 1) 0 (ci_most D) 0 HLED). lia.
  - apply Fa2. lia. }
rewrite Hfail2 in HLED2.
pose proof (cn_calls_le (ci_x D) ok res tr Hrun) as Hcl.
(* ---- THE GRANT: the model's okof og of the instance's outcomes ok (no premise: a refusal ends the reading) ---- *)
destruct (cn_grant ReaderRes.jr_strtod (ci_x D) ok) as (og & Ejr & Epe & Epf & Hgr).
rewrite Hrun in Hgr. cbn [snd] in Hgr.
assert (Hran2 : ran2 = (if cn_ro D og then 1 else 0)).
{ unfold cn_ro. destruct Hoks as (_ & Ho2 & Ho3).
  pose proof (PjGrammar.G7_4 ReaderRes.jr_strtod (ci_x D) ok) as H74. rewrite Hrun in H74. cbn [snd] in H74.
  destruct Hgr as [(-> & Hall) | (-> & i & Hi & Hfi)].
  - destruct Ho2 as [E0 | (_ & i & Hi & Hfi & _)]; [exact E0|]. unfold prh_refused in Hfi.
    rewrite (Hall i Hi) in Hfi. cbn [negb andb] in Hfi. discriminate Hfi.
  - (* the refusal is a refused (n) with n at most g_most: the request bound of the reading (cn_reqs_most) *)
    apply (Ho3 i Hi).
    + unfold prh_refused. rewrite Hfi. cbn [negb andb]. apply negb_true_iff, Z.eqb_neq.
      clear - Hcntb H74 Hi. unfold SIZE_MAXZ, cn_size in *. lia.
    + pose proof (cn_reqs_most ReaderRes.jr_strtod (ci_x D) ok i) as Hq. rewrite Hrun in Hq. cbn [snd] in Hq.
      unfold PRH_FnPj.RQ_pj_parse, prhPj_ptrace in HRQ0. change prh_jr_strtod with ReaderRes.jr_strtod in HRQ0.
      clear - Hq HRQ0. lia. }
assert (HR2 : exists rcv st, getr regs2 10 = w64 rcv /\ Permutation Lam2 (cn_Dof st ++ Lam) /\
  Permutation (ablocks B ly2 S2) (ablocks B ly S ++ ck_hblks (cn_Dof st)) /\
  (forall a kk, In (a, kk) (cn_Dof st) -> ~ In (a - cf_head, kk + cf_head) (ablocks B ly S)) /\
  cn_doc W2 mem2 Lam2 d st /\ bsum (ck_hblks (cn_Dof st)) <= PRH_FnPj.LIVE_pj_parse (ci_x D) /\
  cn_res D ran2 rcv st /\ cn_rd D og st /\ cn_fo D W2 mem2 Lam2 og d st).
{ destruct res as [t|].
  - apply tpnP_RSome_of in Hres as (D0 & HPS).
    pose proof (tpnPs_ret HPS) as H10'. pose proof (tpnPs_lam HPS) as HPL2. pose proof (tpnPs_sizes HPS) as HPsz.
    pose proof (tpnPs_nlive HPS) as HPlen. pose proof (tpnPs_freeord HPS) as HPFO. pose proof (tpnPs_fresh HPS) as HPfr.
    pose proof (tpnPs_ablocks HPS) as HPab. pose proof (tpnPs_node HPS) as HPnode.
    destruct (cn_read_some (ci_x D) ok t tr Hrun) as (Hjr & Etr).
    exists 0, (Some (t, D0)). cbn [cn_Dof].
    split; [exact H10'|]. split; [exact HPL2|]. split; [exact HPab|]. split; [exact HPfr|].
    split; [split; [exact HPnode | exact (PjGrammar.json_read_depth _ _ _ Hjr)]|].
    split.
    + rewrite cn_bsum_hblks, (ReaderRes.lsz_counts D0 tr HPsz HPlen), HPlen.
      pose proof (cn_held_le_hpeak tr). pose proof (cn_nlive_le_calls tr). pose proof (cn_hpeak_nonneg tr).
      assert (cf_head * ReaderRes.nlive tr <= cf_head * Z.of_nat (PjGrammar.calls tr)) by (apply Z.mul_le_mono_nonneg_l; lia).
      unfold PRH_FnPj.LIVE_pj_parse, prhPj_ptrace. change prh_jr_strtod with ReaderRes.jr_strtod. rewrite <- Etr. lia.
    + split; [intros _; unfold ck_read; rewrite Hjr; split; [reflexivity | exists D0; reflexivity]|].
      split; [unfold cn_rd; rewrite Ejr, Hrun; reflexivity|].
      (* THE FREE ORDER at the grant og: the text's at ok, by cn_grant's pj_frees equation *)
      cbn [cn_fo]. intros HH n Hn. destruct (HPFO HH n Hn) as (F & HF & HM).
      exists F. split; [exact HF|]. rewrite Epf. exact HM.
  - apply tpnP_RNone_of in Hres.
    pose proof (tpnPn_ret Hres) as H10'. pose proof (tpnPn_lam Hres) as HPL2. pose proof (tpnPn_ablocks Hres) as HPab.
    pose proof (tpnPn_zero Hres) as HPz.
    exists (-1), None. cbn [cn_Dof cn_doc]. unfold ck_hblks. cbn [map].
    split; [exact H10'|]. split; [exact HPL2|]. split; [rewrite app_nil_r; exact HPab|]. split; [intros a kk []|].
    split; [exact HPz|]. split; [cbn; exact HLV0|].
    split; [|split; [unfold cn_rd; rewrite Ejr, Hrun; reflexivity | cbn [cn_fo]; exact I]].
    intros Hran0. rewrite <- (tpnP_granted_read HPR Hran0); [split; reflexivity|].
    right. unfold SIZE_MAXZ. lia. }
destruct HR2 as (rcv & st & H10' & HSTL2 & HSTAB2 & HSTfr & HSTdoc & HSTbs & HSTres & HSTrd & HSTfo).
(* ---- the copies ---- *)
assert (HCP : forall r0, cn_copy B D ly S Hp W mem r0 -> cn_copy B D ly2 S2 Hp2 W2 mem2 r0).
{ intros r0 [->|(Hb & Hnh & Hsrc)]; [left; reflexivity|]. right.
  assert (Hb2 : In (r0, cn_size D + 16) (ablocks B ly2 S2))
    by (apply (Permutation_in _ (Permutation_sym HSTAB2)); apply in_or_app; left; exact Hb).
  assert (Hrq : req_size (cn_size D + 16) = cn_size D + 16)
    by (unfold req_size; destruct (Z.eqb_spec (cn_size D + 16) 0); lia).
  assert (Hnoh : forall h, In h Hp2 -> ~ (r0 <= h < r0 + req_size (cn_size D + 16))).
  { intros h Hh Hhr.
    pose proof (prh_ledger_heads B ly2 S2 Hp2 W2 mem2 Lam2 peak2 cnt2 SIZE_MAXZ ran2 (ci_most D) 0 HLED2) as Hheads.
    apply (Permutation_in _ Hheads) in Hh. apply in_map_iff in Hh as ([a kk] & Eh & Hak). cbn [fst] in Eh.
    pose proof (prh_ledger_blocks B ly2 S2 Hp2 W2 mem2 Lam2 peak2 cnt2 SIZE_MAXZ ran2 (ci_most D) 0 HLED2) as HBL.
    rewrite Forall_forall in HBL. destruct (HBL _ Hak) as (Hk0 & Hab2 & _). cbn [fst snd] in Hk0, Hab2.
    destruct (req_size_pos (kk + cf_head) (Z.add_nonneg_nonneg _ _ Hk0 Hh0)) as (Hq1 & _).
    destruct (Z.eq_dec (a - cf_head) r0) as [Ea|Ea];
      [destruct (Z.eq_dec (kk + cf_head) (cn_size D + 16)) as [Ek|Ek]|].
    - (* the same block: a new tree block is fresh, an old one's head is in Hp *)
      apply (Permutation_in _ HSTL2) in Hak. apply in_app_or in Hak as [Hak|Hak].
      + apply (HSTfr a kk Hak). rewrite Ea, Ek. exact Hb.
      + apply Hnh. pose proof (prh_ledger_heads B ly S Hp W mem Lam peak cnt SIZE_MAXZ 0 (ci_most D) 0 HLED) as Hh1.
        apply (Permutation_in _ (Permutation_sym Hh1)). apply in_map_iff. exists (a, kk). split; [exact Ea | exact Hak].
    - pose proof (sep_blocks_x SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 (a - cf_head) (kk + cf_head) r0 (cn_size D + 16)
        HAR2 Hab2 Hb2 ltac:(intros Eq0; injection Eq0 as _ E2; exact (Ek E2))) as Hz.
      unfold zdisjoint in Hz. cbn [fst snd] in Hz. rewrite Hrq in Hz, Hhr. lia.
    - pose proof (sep_blocks_x SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 (a - cf_head) (kk + cf_head) r0 (cn_size D + 16)
        HAR2 Hab2 Hb2 ltac:(intros Eq0; injection Eq0 as E1 _; exact (Ea E1))) as Hz.
      unfold zdisjoint in Hz. cbn [fst snd] in Hz. rewrite Hrq in Hz, Hhr. lia. }
  split; [exact Hb2|]. split; [intros Hh; apply (Hnoh r0 Hh); rewrite Hrq; lia|].
  destruct Hsrc as (Hby & H4 & Hc & Ham & Hra & Hhv).
  destruct (alx_shadow SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 r0 (cn_size D + 16) HAR2 Hb2 Hnoh) as (Hbs & Hhv2).
  split; [|split; [exact H4|split; [exact Hc|split; [exact Ham|split]]]].
  - unfold bytes_at in *. apply (garr8R_frame SEGS (rdW W mem) (rdW W2 mem2) r0 (ci_x D) Hby).
    intros a Ha. apply (mbyte_of_aview SEGS). replace a with (r0 + (a - r0)) by lia.
    apply (KBL r0 (cn_size D + 16) (a - r0) Hb Hb2). rewrite Hrq. unfold cn_size. lia.
  - exact (cn_bshadow_ra _ r0 (cn_size D) Hsz0 Hbs).
  - intros Hpos. apply (cn_hull_sub _ r0 (req_size (cn_size D + 16))); [rewrite Hrq; unfold cn_size in *; lia | exact Hhv2]. }
(* ---- the structs: open, and the trees of the other two kept ---- *)
assert (HOPEN : forall d0, cn_F D + 32 <= d0 -> d0 + 56 <= cn_F D + 280 -> d0 mod 32 = 0 ->
  cn_open W mem d0 -> cn_open W2 mem2 d0).
{ intros d0 H1 H2 H3 (Hra & Hhv).
  destruct (cn_struct_shadow (cn_F D) d0 HF32 ltac:(lia) H1 H2 H3) as (Hs1' & Hs2'). split.
  - apply (range_addressable_agree (aview SEGS (w_H W) mem) (aview SEGS (w_H W2) mem2) SHADOW_OFF d0 56); [|exact Hra].
    intros x Hx. apply KSH. exact (Hs1' x Hx).
  - intros s Hs. rewrite (KSH s (Hs2' s Hs)). exact (Hhv s Hs). }
(* a struct d0 apart from d whose blocks are in Lam keeps its bytes (and writability) across the call *)
assert (HAGR : forall d0 D1, cn_F D + 32 <= d0 -> d0 + 56 <= cn_F D + 280 -> (d0 + 56 <= d \/ d + 56 <= d0) ->
  incl D1 Lam -> pj_agreeR SEGS (rdW W mem) (rdW W2 mem2) (pj_footR d0 D1)).
{ intros d0 D1 Hd01 Hd02 Hdis Hinc x Hx.
  destruct Hx as [Hx|((a & kk) & Hbk & Hx)].
  - split; [apply (mbyte_of_aview SEGS); apply KFR; lia|].
    intros _. apply (apresent_writable SEGS). exact (proj1 (HFb2 x ltac:(lia))).
  - unfold pj_holdsR in Hx. cbn [fst snd] in Hx.
    pose proof (Hinc _ Hbk) as HbL.
    pose proof (prh_ledger_blocks B ly S Hp W mem Lam peak cnt SIZE_MAXZ 0 (ci_most D) 0 HLED) as HB1.
    rewrite Forall_forall in HB1. destruct (HB1 _ HbL) as (Hk0 & Hab1 & _). cbn [fst snd] in Hk0, Hab1.
    assert (HbL2 : In (a, kk) Lam2) by (apply (Permutation_in _ (Permutation_sym HSTL2)); apply in_or_app; right; exact HbL).
    pose proof (prh_ledger_blocks B ly2 S2 Hp2 W2 mem2 Lam2 peak2 cnt2 SIZE_MAXZ ran2 (ci_most D) 0 HLED2) as HB2.
    rewrite Forall_forall in HB2. destruct (HB2 _ HbL2) as (_ & Hab2 & _). cbn [fst snd] in Hab2.
    destruct (req_size_pos (kk + cf_head) (Z.add_nonneg_nonneg _ _ Hk0 Hh0)) as (_ & Hq2).
    split.
    + apply (mbyte_of_aview SEGS). replace x with ((a - cf_head) + (x - (a - cf_head))) by lia.
      apply (KBL _ _ _ Hab1 Hab2). lia.
    + intros _. apply (apresent_writable SEGS).
      destruct (alx_blocks SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 (a - cf_head) (kk + cf_head) HAR2 Hab2)
        as (_ & _ & _ & _ & Hpr2 & _).
      exact (proj1 (Hpr2 x ltac:(lia))). }
assert (HDOC : forall d0 st0, cn_F D + 32 <= d0 -> d0 + 56 <= cn_F D + 280 -> (d0 + 56 <= d \/ d + 56 <= d0) ->
  incl (cn_Dof st0) Lam -> cn_doc W mem Lam d0 st0 -> cn_doc W2 mem2 Lam2 d0 st0).
{ intros d0 st0 Hd01 Hd02 Hdis Hinc Hdoc. destruct st0 as [[t0 D1]|]; cbn [cn_doc cn_Dof] in *.
  - destruct Hdoc as (Hn & Hdep). split; [|exact Hdep].
    apply (cn_nodeR_lblk SEGS t0 _ (prh_lin Lam));
      [|intros a kk Hak; unfold prh_lin in *; apply (Permutation_in _ (Permutation_sym HSTL2)); apply in_or_app; right; exact Hak].
    apply (pj_nodeR_frame SEGS t0 (rdW W mem) (rdW W2 mem2) (prh_lin Lam) d0 D1 Hn).
    exact (HAGR d0 D1 Hd01 Hd02 Hdis Hinc).
  - apply (pj_zeroR_frame SEGS (rdW W mem) (rdW W2 mem2) d0 Hdoc). intros x Hx. apply (mbyte_of_aview SEGS).
    apply KFR; lia. }
(* THE FREE-ORDER TIE of such a struct crosses the call (PRH_PjOrder.pj_foR_frame: its footprint keeps its bytes, and
   its blocks stay in the ledger list) *)
assert (HFOK : forall o d0 st0, cn_F D + 32 <= d0 -> d0 + 56 <= cn_F D + 280 -> (d0 + 56 <= d \/ d + 56 <= d0) ->
  incl (cn_Dof st0) Lam -> cn_fo D W mem Lam o d0 st0 -> cn_fo D W2 mem2 Lam2 o d0 st0).
{ intros o d0 st0 Hd01 Hd02 Hdis Hinc Hfo. destruct st0 as [[t0 D1]|]; cbn [cn_fo cn_Dof] in *; [|exact I].
  intros HH n Hn. destruct (Hfo HH n Hn) as (F & HF & HM). exists F. split; [|exact HM].
  apply (PRH_PjOrder.pj_foR_frame SEGS n (rdW W mem) (rdW W2 mem2) (prh_lin Lam) (prh_lin Lam2) d0 D1 F HF).
  - intros a kk Hak. unfold prh_lin. apply (Permutation_in _ (Permutation_sym HSTL2)). apply in_or_app. right.
    exact (Hinc _ Hak).
  - exact (HAGR d0 D1 Hd01 Hd02 Hdis Hinc). }
(* ---- THE EXIT ---- *)
pose proof (HU st) as (HUp & HU1 & HU2 & HU3).
assert (Hd123 : cn_d1 D = cn_F D + 32 /\ cn_d2 D = cn_F D + 128 /\ cn_d3 D = cn_F D + 224) by (unfold cn_d1, cn_d2, cn_d3; lia).
assert (HinL : forall x, In x (cn_Dof st1 ++ cn_Dof st2 ++ cn_Dof st3) -> In x Lam)
  by (intros x Hx; apply (Permutation_in _ (Permutation_sym HPL)); rewrite !app_assoc in *; apply in_or_app; left; exact Hx).
exists fx', ly2, S2, Hp2, regs2, mem2, md2, (k + k1), Lam2, peak2, cnt2, ran2, rcv, st, og.
split; [rewrite Hc2; unfold cn_cfg; rewrite Hra1; reflexivity|].
split.
{ (* cn_base *)
  split; [exact HFZ'|]. split; [intros rr Hr8; rewrite (HFK' rr Hr8); exact (HFK rr Hr8)|].
  split; [exists (WS0 ++ WS1); split; [exact HJ2 | exact (YCbqGwild.wbudget_app [] wk 2 WS0 WS1 HWB0 HWB1)]|].
  split.
  { destruct HFRM as (Ef & Hni & Hflag & Hp1 & Hp2').
    split; [rewrite Hfrs1; exact Ef|]. split; [exact Hni|].
    split; [|split].
    - assert (Efl : flag_addr ly2 CN_CID (ci_fpos D) = flag_addr ly CN_CID (ci_fpos D)) by (unfold flag_addr; rewrite EF1; reflexivity).
      rewrite Efl, <- Hflag. apply cn_rdword_agree. intros i Hi. rewrite Efb. apply KFR; lia.
    - intros a Ha. rewrite Efb in Ha. exact (proj1 (HFb2 a Ha)).
    - intros a Ha. rewrite Efb in Ha. change (512 / 8) with 64 in Ha.
      replace a with (shadow_addr (cn_F D) + (a - shadow_addr (cn_F D))) by lia.
      apply (proj1 (HFs2 (a - shadow_addr (cn_F D)) ltac:(change (512 / 8) with 64; lia))). }
  split.
  { unfold cn_saved in *.
    refine (cn_Forall_and (fun p : Z * bv 5 => 88 <= fst p <= 184) _ _ _ _ HSAV _); [repeat constructor; cbn [fst]; lia |].
    intros [o rr] Ho Hv. cbn [fst snd] in *. rewrite <- Hv. apply cn_rdword_agree. intros i Hi. apply KST. lia. }
  split; [rewrite (cn_pres regs regs2 3%bv HP2) by (vm_compute; lia); exact HG3|].
  split; [rewrite (cn_pres regs regs2 4%bv HP2) by (vm_compute; lia); exact HG4|].
  (* the read-only view, by the callee's journal: no read-only byte is a program static (cni_pst_rw) *)
  intros a Hro Ho He.
  assert (Himg : in_img SEGS a)
    by (destruct Hro as [(s & Hs & _ & Hlo & Hhi) | Hrl]; [exists s; split; [exact Hs | lia] | apply pa_relro_img; exact Hrl]).
  rewrite (G3 a Himg Ho He).
  - exact (HRO a Hro Ho He).
  - intros Hpst. exact (cni_pst_rw B IMG a Hpst Hro).
  - apply fp_spares_closed. intros (rr & Hin & Hrr'). destruct Hin as [<-|[]]. cbn [fst snd] in Hrr'. lia. }
split; [exact HP2|]. split; [exact H10'|].
split.
{ unfold cn_slots in *.
  refine (cn_Forall_and (fun p : Z * Z => 24 <= fst p <= 80) _ _ _ _ HSL _); [repeat constructor; cbn [fst]; lia |].
  intros [o v] Ho Hv. cbn [fst snd] in *. rewrite <- Hv. apply cn_rdword_agree. intros i Hi. apply KST. lia. }
split.
{ (* the events: this reading's under the grant og, the text's exact live set and position *)
  apply (cn_prog_app D E (cn_pe D og) S S2 HPROG).
  - unfold cn_pe. rewrite Epe. exact HLV2.
  - unfold cn_pe. rewrite Epe. exact HPS2. }
split; [exact Hran2|].
split.
{ (* cn_mid *)
  split; [exact (HCP r1 HC1)|]. split; [exact (HCP r2 HC2)|]. split; [exact (HCP r3 HC3)|].
  split; [exact HLED2|].
  split; [rewrite Hpk2; lia|].
  split.
  { rewrite Hcnt2. unfold ck_ncalls in *. rewrite Nat2Z.inj_succ, Z.mul_succ_l.
    set (NN := Z.of_nat nr * Z.of_nat (PjGrammar.ncalls ReaderRes.jr_strtod (ci_x D))) in *. lia. }
  split; [exact HROOM2|].
  split.
  { rewrite (blocks_bytes_bsum B ly2 S2), (bsum_perm _ _ HSTAB2), bsum_app, <- (blocks_bytes_bsum B ly S).
    assert (E3 : Z.of_nat (3 - Datatypes.S nr) = Z.of_nat (3 - nr) - 1) by lia. rewrite E3, Z.mul_sub_distr_r, Z.mul_1_l.
    set (NL := Z.of_nat (3 - nr) * PRH_FnPj.LIVE_pj_parse (ci_x D)) in *. lia. }
  split; [apply HOPEN; [lia | lia | rewrite (proj1 Hd123); apply (cn_mod32_at (cn_F D) _ 1 HF32); lia | exact HO1]|].
  split; [apply HOPEN; [lia | lia | rewrite (proj1 (proj2 Hd123)); apply (cn_mod32_at (cn_F D) _ 4 HF32); lia | exact HO2]|].
  split; [apply HOPEN; [lia | lia | rewrite (proj2 (proj2 Hd123)); apply (cn_mod32_at (cn_F D) _ 7 HF32); lia | exact HO3]|].
  split.
  { destruct (Z.eqb (d) (cn_d1 D)) eqn:E1b in HU1.
    - apply Z.eqb_eq in E1b. destruct HU1 as (_ & ->). rewrite <- E1b. exact HSTdoc.
    - apply Z.eqb_neq in E1b. rewrite HU1.
      apply HDOC; [lia | lia | lia | intros x Hx; apply HinL; apply in_or_app; left; exact Hx | exact HD1]. }
  split.
  { destruct (Z.eqb (d) (cn_d2 D)) eqn:E1b in HU2.
    - apply Z.eqb_eq in E1b. destruct HU2 as (_ & ->). rewrite <- E1b. exact HSTdoc.
    - apply Z.eqb_neq in E1b. rewrite HU2.
      apply HDOC; [lia | lia | lia | intros x Hx; apply HinL; apply in_or_app; right; apply in_or_app; left; exact Hx | exact HD2]. }
  split.
  { destruct (Z.eqb (d) (cn_d3 D)) eqn:E1b in HU3.
    - apply Z.eqb_eq in E1b. destruct HU3 as (_ & ->). rewrite <- E1b. exact HSTdoc.
    - apply Z.eqb_neq in E1b. rewrite HU3.
      apply HDOC; [lia | lia | lia | intros x Hx; apply HinL; apply in_or_app; right; apply in_or_app; right; exact Hx | exact HD3]. }
  split; [exact (cn_perm_lam _ _ _ _ _ _ _ _ _ _ HSTL2 HPL HUp)|].
  split; [exact (cn_perm_blocks _ _ _ _ _ _ _ _ _ _ _ HSTAB2 HPB HUp)|].
  intros a kk Hak. apply (Permutation_in _ HUp) in Hak. apply in_app_or in Hak as [Hak|Hak].
  - intros Hab0. apply (HSTfr a kk Hak). apply (Permutation_in _ (Permutation_sym HPB)).
    apply in_or_app; right; apply in_or_app; right; exact Hab0.
  - exact (HFRESH a kk Hak). }
split; [exact HSTres|]. split; [exact HSTrd|]. split; [exact HSTfo|].
split.
{ (* the other structs' free-order ties *)
  intros o d0 st0 Hsel Hne Hfo.
  assert (Hd0 : d0 = cn_d1 D \/ d0 = cn_d2 D \/ d0 = cn_d3 D)
    by (destruct Hsel as [(-> & _)|[(-> & _)|(-> & _)]]; [left | right; left | right; right]; reflexivity).
  assert (Hinc : incl (cn_Dof st0) Lam).
  { intros x Hx. apply HinL. destruct Hsel as [(_ & ->)|[(_ & ->)|(_ & ->)]]; rewrite !in_app_iff; tauto. }
  destruct (cn_d_sep D d0 d Hd0 Hd Hne) as (Hs1' & Hs2' & Hs3').
  exact (HFOK o d0 st0 Hs1' Hs2' Hs3' Hinc Hfo). }
(* the hull: the reading used at most its all-granted events, so the cut's rest is the next cut's budget *)
split; [exact (PresetHullBudget.hull_budget_app S S2 (PresetReqAt.parse_evs ReaderRes.jr_strtod (ci_x D) []) Hrest HHB
  HHU)|].
exact (PC mem mem2 Hmn HP).
Qed.
(* the journal (cn_base's only Model-dependent conjunct) across a register step's materialization: at the cut's
   budget WS by YCbqGwild's rebase / unbase (the state, so the depot, is unchanged) around YCbqG's empty-budget rule;
   at the re-hiding relation (used only after a call of parse_noting), by their R forms *)
Lemma cn_base_mat : forall D fxk ly S Hp W regs mem md k wk X,
  cn_baseR (fx := fx) B ARx (wle' SEGS RZ) D fxk ly S Hp W regs mem md k wk ->
  cn_baseR (fx := fx) B ARx (wle' SEGS RZ) D fxk ly S Hp W regs mem (with_vm_backing (m_vm_lazy md) X md) k wk.
Proof.
intros D fxk ly S Hp W regs mem md k wk X (H1 & H2 & (WS & H3 & HWB) & H4).
split; [exact H1|]. split; [exact H2|]. split; [|exact H4].
exists WS. split; [|exact HWB].
eapply (YCbqGwild.ajournal_xw_unbase0R (SK := SK) SEGS B prh_pst ARx (wle' SEGS RZ)); [|exact (ajxR_wild H3)].
apply (ajournal_x_materializeR (SK := SK) SEGS B _ ARx LAWS (@pa_segs_low _ _ PA) (wle' SEGS RZ)).
exact (YCbqGwild.ajournal_xw_rebaseR (SK := SK) SEGS B prh_pst ARx (wle' SEGS RZ) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  H3).
Qed.

(* the readings' piece of check_no_overread's all-granted list, after the three granted copies *)
Lemma cn_cno_split : forall (D : cn_in) r1 r2 r3, r1 <> 0 -> r2 <> 0 -> r3 <> 0 ->
  exists R, ck_cno_evs ReaderRes.jr_strtod (ci_x D) None None None =
    cn_cevs D r1 r2 r3 ++ cn_pe D None ++ cn_pe D None ++ cn_pe D None ++ R.
Proof.
intros D r1 r2 r3 H1 H2 H3. unfold cn_cevs, cn_cblks, cn_cblk, cn_pe, cn_size.
rewrite (proj2 (Z.eqb_neq r1 0) H1), (proj2 (Z.eqb_neq r2 0) H2), (proj2 (Z.eqb_neq r3 0) H3).
eexists. reflexivity.
Qed.
(* a grant that does not run out gives the all-granted reading's events *)
Lemma cn_pe_none : forall (D : cn_in) o, cn_ro D o = false -> cn_pe D o = cn_pe D None.
Proof. intros D o H. exact (cn_parse_evs_noro ReaderRes.jr_strtod (ci_x D) o H). Qed.

(* ==== 4. the three steps ==== *)
(* pn1 starts at a cut before any free (cn_at_pn1 at wle) and ends at read2 after one (cn_ex_read2R at wle') *)
Lemma cn_pn1_step : forall P, srr_inv_laws SEGS P -> srr_inv_call SEGS P -> srr_inv_mn SEGS P ->
  forall D fxk ly S Hp W regs mem md k r1 r2 r3,
  cn_pre (fx := fx) B ARx CTX0 D -> cn_at_pn1 (fx := fx) B ARx D fxk ly S Hp W regs mem md k r1 r2 r3 -> P mem ->
  SRr' SEGS RZ W (@cn_cfg SEGS fxk (SIGMA AS_parse_noting) regs mem md)
    (fun W' c' => cn_ex_read2R (fx := fx) B ARx (wle' SEGS RZ) D W' c' /\ P (ms_mem (cfg_ms c'))).
Proof.
intros P HL HC HMN D fxk ly S Hp W regs mem md k r1 r2 r3 HPRE HAT HP.
destruct HAT as (HB & HR & HSL & Hr1 & Hr2 & Hr3 & _ & HPROG & HM & HHB).
(* the base at wle, lifted to the relation the reading's post states *)
pose proof (cn_baseR_mono (fx := fx) B ARx (@wle SEGS) (wle' SEGS RZ) (wle_wle' SEGS RZ) D fxk ly S Hp W regs mem md k 0
  HB) as HBw.
(* the hull after the copies: this reading's all-granted events, then rd1's rest *)
rewrite (cn_hrest_rd1_split (ci_x D)) in HHB.
pose proof (cni_base B IMG) as HB0.
destruct (cn_ret1_ok HB0) as (Hm4 & H4k & Hceil).
destruct (cn_dne D) as (E12 & E13 & _ & _ & _ & _).
assert (HU : forall st, cn_upd_ok D (cn_d1 D) st None None None (st, None, None)).
{ intros st. unfold cn_upd_ok. cbn [fst snd cn_Dof app]. rewrite (Z.eqb_refl (cn_d1 D)), E12, E13. cbv beta iota.
  split; [rewrite !app_nil_r; apply Permutation_refl|]. repeat split. }
destruct (cn_cno_split D r1 r2 r3 Hr1 Hr2 Hr3) as (R0 & ER0).
eapply SRr'_bind.
{ exact (cn_pn_call P HL HC HMN D fxk ly S Hp W regs mem md k 0%nat (ci_Lam D) (ci_peak D) (ci_cnt D) 0%nat r1 r2 r3
    None None None r1 (cn_d1 D) (cn_pc CN_RET1) (cn_cevs D r1 r2 r3) (cn_hrest_rd1 (ci_x D)) (fun st => (st, None, None))
    HPRE HBw ltac:(lia) (cn_call_regs1 D regs r1 r3 HR) Hm4 H4k Hceil HSL (or_introl eq_refl) Hr1 (or_introl eq_refl)
    ltac:(lia) HPROG (ex_intro _ (cn_pe D None ++ cn_pe D None ++ R0) ER0) HM HU HHB HP). }
intros W' c' _ (fx' & ly' & S' & Hp' & regs' & mem' & md' & k' & Lam' & peak' & cnt' & ran' & rcv & st & og & -> & HB' &
  HPR & H10 & HSL' & HPROG' & HRAN & HM' & HRES & HRD & HFO & _ & HHB' & HPm).
(* the return-site register steps: plain, lifted *)
apply (SRr_SRr' SEGS RZ).
apply (cn_run_ret1 fx' W' regs' mem' md' _ HB0). intros mat1 mat2.
destruct (cn_keep34 regs' 23%bv (getr regs' 10%bv) (or_intror (or_introl eq_refl))) as (K3 & K4).
apply SRr_ret. split; [|exact HPm].
unfold cn_ex_read2R.
eexists fx', ly', S', Hp', _, mem', _, k', Lam', peak', cnt', ran', r1, r2, r3, 0, rcv, st, og.
split; [reflexivity|].
unfold cn_at_read2R.
split; [exact (cn_base_regs D fx' ly' S' Hp' W' regs' _ mem' _ k' _
  (cn_base_mat _ _ _ _ _ _ _ _ _ _ _ mat2 (cn_base_mat _ _ _ _ _ _ _ _ _ _ _ mat1 HB')) K3 K4)|].
split; [exact (cn_seat1 D regs regs' r1 r3 rcv HR HPR H10)|].
split; [exact HSL'|].
split; [split; [lia|]; split; [intros _; exact (conj Hr1 (conj Hr2 Hr3)) | intros E; exfalso; exact (E eq_refl)]|].
split; [exact HM'|].
split; [intros _; split; [exact HPROG'|]; split; [|split; [exact HRD | split; [exact HRES | exact HFO]]]|].
- rewrite HRAN. unfold cn_ranz, ck_cno_ranout, cn_ro.
  destruct (PresetRun.ranout ReaderRes.jr_strtod (ci_x D) og); reflexivity.
- split; [intros E; exfalso; exact (E eq_refl) | exact HHB'].
Qed.

(* pn2 and pn3 start at cuts after a free (cn_at_pn2R / cn_at_pn3R at wle') *)
Lemma cn_pn2_step : forall P, srr_inv_laws SEGS P -> srr_inv_call SEGS P -> srr_inv_mn SEGS P ->
  forall D fxk ly S Hp W regs mem md k Lam peak cnt r1 r2 r3 rc1 st1 o1,
  cn_pre (fx := fx) B ARx CTX0 D ->
  cn_at_pn2R (fx := fx) B ARx (wle' SEGS RZ) D fxk ly S Hp W regs mem md k Lam peak cnt r1 r2 r3 rc1 st1 o1 -> P mem ->
  SRr' SEGS RZ W (@cn_cfg SEGS fxk (SIGMA AS_parse_noting) regs mem md)
    (fun W' c' => cn_ex_read3R (fx := fx) B ARx (wle' SEGS RZ) D W' c' /\ P (ms_mem (cfg_ms c'))).
Proof.
intros P HL HC HMN D fxk ly S Hp W regs mem md k Lam peak cnt r1 r2 r3 rc1 st1 o1 HPRE HAT HP.
destruct HAT as (HB & HR & HSL & Hr1 & Hr2 & Hr3 & HPROG & HRO1 & HRD1 & HFO1 & HM & HRES1 & HHB).
(* the hull after reading 1: this reading's all-granted events, then rd2's rest *)
rewrite (cn_hrest_rd2_split (ci_x D)) in HHB.
pose proof (cni_base B IMG) as HB0.
destruct (cn_ret2_ok HB0) as (Hm4 & H4k & Hceil).
destruct (cn_dne D) as (E12 & _ & E21 & E23 & _ & _).
assert (N12 : cn_d1 D <> cn_d2 D) by (apply Z.eqb_neq; exact E12).
assert (HU : forall st, cn_upd_ok D (cn_d2 D) st st1 None None (st1, st, None)).
{ intros st. unfold cn_upd_ok. cbn [fst snd cn_Dof app]. rewrite E21, (Z.eqb_refl (cn_d2 D)), E23. cbv beta iota.
  split; [rewrite !app_nil_r; apply Permutation_app_comm|]. repeat split. }
assert (HSP : exists R, ck_cno_evs ReaderRes.jr_strtod (ci_x D) None None None =
  (cn_cevs D r1 r2 r3 ++ cn_pe D o1) ++ cn_pe D None ++ R).
{ destruct (cn_cno_split D r1 r2 r3 Hr1 Hr2 Hr3) as (R0 & ER0). exists (cn_pe D None ++ R0).
  rewrite ER0, (cn_pe_none D o1 HRO1), <- !app_assoc. reflexivity. }
eapply SRr'_bind.
{ exact (cn_pn_call P HL HC HMN D fxk ly S Hp W regs mem md k 2%nat Lam peak cnt 1%nat r1 r2 r3
    st1 None None r2 (cn_d2 D) (cn_pc CN_RET2) (cn_cevs D r1 r2 r3 ++ cn_pe D o1) (cn_hrest_rd2 (ci_x D))
    (fun st => (st1, st, None)) HPRE HB ltac:(lia) (cn_call_regs2 D regs r1 r2 r3 rc1 HR) Hm4 H4k Hceil HSL
    (or_intror (or_introl eq_refl)) Hr2 (or_intror (or_introl eq_refl)) ltac:(lia) HPROG HSP HM HU HHB HP). }
intros W' c' _ (fx' & ly' & S' & Hp' & regs' & mem' & md' & k' & Lam' & peak' & cnt' & ran' & rcv & st & og & -> & HB' &
  HPR & H10 & HSL' & HPROG' & HRAN & HM' & HRES & HRD & HFO & HFT & HHB' & HPm).
(* the return-site register step: plain, lifted *)
apply (SRr_SRr' SEGS RZ).
apply (cn_run_ret2 fx' W' regs' mem' md' _). intros mat1.
destruct (cn_keep34 regs' 25%bv (getr regs' 10%bv) (or_intror (or_intror eq_refl))) as (K3 & K4).
apply SRr_ret. split; [|exact HPm].
unfold cn_ex_read3R.
eexists fx', ly', S', Hp', _, mem', _, k', Lam', peak', cnt', ran', r1, r2, r3, rc1, rcv, st1, st, o1, og.
split; [reflexivity|].
unfold cn_at_read3R.
split; [exact (cn_base_regs D fx' ly' S' Hp' W' regs' _ mem' _ k' _ (cn_base_mat _ _ _ _ _ _ _ _ _ _ _ mat1 HB') K3 K4)|].
split; [exact (cn_seat2 D regs regs' r1 r2 r3 rc1 rcv HR HPR H10)|].
split; [exact HSL'|]. split; [exact Hr1|]. split; [exact Hr2|]. split; [exact Hr3|].
split; [apply (cn_prog_eq D ((cn_cevs D r1 r2 r3 ++ cn_pe D o1) ++ cn_pe D og));
  [unfold cn_revs2; rewrite HRO1, <- app_assoc; reflexivity | exact HPROG']|].
split; [rewrite HRAN; unfold cn_ranz, ck_cno_ranout; unfold cn_ro in HRO1 |- *; rewrite HRO1;
  destruct (PresetRun.ranout ReaderRes.jr_strtod (ci_x D) og); reflexivity|].
split; [unfold cn_rds2; rewrite HRO1; split; [exact HRD1 | exact HRD]|].
split; [exact (HFT o1 (cn_d1 D) st1 (or_introl (conj eq_refl eq_refl)) N12 HFO1)|].
split; [exact HFO|].
split; [exact HM'|].
split; [intros _; exact (HRES1 eq_refl)|]. split; [exact HRES | exact HHB'].
Qed.

Lemma cn_pn3_step : forall P, srr_inv_laws SEGS P -> srr_inv_call SEGS P -> srr_inv_mn SEGS P ->
  forall D fxk ly S Hp W regs mem md k Lam peak cnt r1 r2 r3 rc1 rc2 st1 st2 o1 o2,
  cn_pre (fx := fx) B ARx CTX0 D ->
  cn_at_pn3R (fx := fx) B ARx (wle' SEGS RZ) D fxk ly S Hp W regs mem md k Lam peak cnt r1 r2 r3 rc1 rc2 st1 st2 o1 o2 ->
  P mem ->
  SRr' SEGS RZ W (@cn_cfg SEGS fxk (SIGMA AS_parse_noting) regs mem md)
    (fun W' c' => cn_ex_cmpR (fx := fx) B ARx (wle' SEGS RZ) D W' c' /\ P (ms_mem (cfg_ms c'))).
Proof.
intros P HL HC HMN D fxk ly S Hp W regs mem md k Lam peak cnt r1 r2 r3 rc1 rc2 st1 st2 o1 o2 HPRE HAT HP.
destruct HAT as (HB & HR & HSL & Hr1 & Hr2 & Hr3 & HPROG & HRO1 & HRO2 & HRD1 & HRD2 & HFO1 & HFO2 & HM & HRES1 &
  HRES2 & HHB).
(* the hull after reading 2: this reading's all-granted events, then rd0's rest *)
rewrite (cn_hrest_rd0_split (ci_x D)) in HHB.
pose proof (cni_base B IMG) as HB0.
destruct (cn_ret3_ok HB0) as (Hm4 & H4k & Hceil).
destruct (cn_dne D) as (_ & E13 & _ & E23 & E31 & E32).
assert (N13 : cn_d1 D <> cn_d3 D) by (apply Z.eqb_neq; exact E13).
assert (N23 : cn_d2 D <> cn_d3 D) by (apply Z.eqb_neq; exact E23).
assert (HU : forall st, cn_upd_ok D (cn_d3 D) st st1 st2 None (st1, st2, st)).
{ intros st. unfold cn_upd_ok. cbn [fst snd cn_Dof app]. rewrite E31, E32, (Z.eqb_refl (cn_d3 D)). cbv beta iota.
  split; [rewrite app_nil_r, (app_assoc (cn_Dof st1)); apply Permutation_app_comm|]. repeat split. }
assert (HSP : exists R, ck_cno_evs ReaderRes.jr_strtod (ci_x D) None None None =
  (cn_cevs D r1 r2 r3 ++ cn_revs2 D o1 o2) ++ cn_pe D None ++ R).
{ destruct (cn_cno_split D r1 r2 r3 Hr1 Hr2 Hr3) as (R0 & ER0). exists R0.
  rewrite ER0. unfold cn_revs2. rewrite HRO1, (cn_pe_none D o1 HRO1), (cn_pe_none D o2 HRO2).
  rewrite <- !app_assoc. reflexivity. }
eapply SRr'_bind.
{ exact (cn_pn_call P HL HC HMN D fxk ly S Hp W regs mem md k 4%nat Lam peak cnt 2%nat r1 r2 r3
    st1 st2 None r3 (cn_d3 D) (cn_pc CN_RET3) (cn_cevs D r1 r2 r3 ++ cn_revs2 D o1 o2) (cn_hrest_rd0 (ci_x D))
    (fun st => (st1, st2, st)) HPRE HB ltac:(lia) (cn_call_regs3 D regs r1 r3 rc1 rc2 HR) Hm4 H4k Hceil HSL
    (or_intror (or_intror eq_refl)) Hr3 (or_intror (or_intror eq_refl)) ltac:(lia) HPROG HSP HM HU HHB HP). }
intros W' c' _ (fx' & ly' & S' & Hp' & regs' & mem' & md' & k' & Lam' & peak' & cnt' & ran' & rcv & st & og & -> & HB' &
  HPR & H10 & HSL' & HPROG' & HRAN & HM' & HRES & HRD & HFO & HFT & HHB' & HPm).
(* the return-site register step: plain, lifted *)
apply (SRr_SRr' SEGS RZ).
apply (cn_run_ret3 fx' W' regs' mem' md' _). intros mat1.
destruct (cn_keep34 regs' 20%bv (getr regs' 10%bv) (or_introl eq_refl)) as (K3 & K4).
apply SRr_ret. split; [|exact HPm].
unfold cn_ex_cmpR.
eexists fx', ly', S', Hp', _, mem', _, k', Lam', peak', cnt', ran', r1, r2, r3, rc1, rc2, rcv, st1, st2, st, o1, o2, og.
split; [reflexivity|].
unfold cn_at_cmpR.
split; [exact (cn_base_regs D fx' ly' S' Hp' W' regs' _ mem' _ k' _ (cn_base_mat _ _ _ _ _ _ _ _ _ _ _ mat1 HB') K3 K4)|].
split; [exact (cn_seat3 D regs regs' r1 r3 rc1 rc2 rcv HR HPR H10)|].
split; [exact HSL'|]. split; [exact Hr1|]. split; [exact Hr2|]. split; [exact Hr3|].
split; [apply (cn_prog_eq D ((cn_cevs D r1 r2 r3 ++ cn_revs2 D o1 o2) ++ cn_pe D og));
  [unfold cn_revs2, cn_revs3; rewrite HRO1, HRO2, <- !app_assoc; reflexivity | exact HPROG']|].
split; [rewrite HRAN; unfold cn_ranz, ck_cno_ranout; unfold cn_ro in HRO1, HRO2 |- *; rewrite HRO1, HRO2;
  destruct (PresetRun.ranout ReaderRes.jr_strtod (ci_x D) og); reflexivity|].
split; [unfold cn_rds3; rewrite HRO1, HRO2; split; [exact HRD1 | split; [exact HRD2 | exact HRD]]|].
split; [exact (HFT o1 (cn_d1 D) st1 (or_introl (conj eq_refl eq_refl)) N13 HFO1)|].
split; [exact (HFT o2 (cn_d2 D) st2 (or_intror (or_introl (conj eq_refl eq_refl))) N23 HFO2)|].
split; [exact HFO|].
split; [exact HM'|].
split; [intros _; exact (HRES1 eq_refl)|]. split; [intros _; exact (HRES2 eq_refl)|].
split; [exact HRES | exact HHB'].
Qed.

End rpn.

(* the audit: each lemma closed under the Section hypotheses (LAWS, IMG, HPN) only *)
Print Assumptions cn_pn_call.
Print Assumptions cn_pn1_step.
Print Assumptions cn_pn2_step.
Print Assumptions cn_pn3_step.
