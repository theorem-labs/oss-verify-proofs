(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/CfRBridgeAjRealloc.v; 65 of its 333 lines of code are new or changed and 249 lines of the source are left out. *)
(* plugin-hostd/fuzz_reply.asan_ubsan, image B: the image-B twin of lib/A/CfRBridgeAjReallocRh.v (row R-2), under lib/B
   so the B tree is self-contained (as lib/B/CfRBridgeAjReallocB.v). Its text is the A file's with the lib/B modules
   (YGcfRehidePost, YG0dcfR, AjxCallRh, CfRBridgeAjReallocB, YGcfReallocComposeRh, YGcfInstReallocK) in place of
   lib/A's; the A file's header follows.
   The RE-HIDE twin of the realloc(p, n) call-site rule. realloc(p, n) frees the old block inside the call, and a
   secondary free may re-hide shadow, so the rule's world order is R := wle' segs RZ_cf and the contract is the primed
   one.
   aj_realloc_at_x_ct_rh is CfRBridgeAjReallocB.aj_realloc_at_x_ct (its (B'') text, QMm_cf at the call) with:
   - the realization YGcfInstReallocK.arealloc_realizes_cf_k segs B Hpc pc kr: the layer's primed room form (amreal'
     over RZ_cf, the leaf YG0dcfR.realloc_leaf_cf_rh, ROOM_cf_k at the entry and in the post), so the rule is stated
     at the room ROOM_cf_k Sc (RK_realloc + kr) and the model facts amx_realloc_rp at that room;
   - the caller's hull admission at the call's entry, cf_hull_adm Sc n (CfParams' field), right after the trace
     premise, passed through to the realization (which derives the post state from it);
   - the journals ajournal_xR .. (wle' segs RZ_cf), and the step SRrG segs (wle' segs RZ_cf);
   - the leaf realloc_leaf_cf_rh.
   Proof: aj_realloc_at_x_ct's steps, with amreal'_SRr'04 (YG0dH) in place of amreal_SRr04, SRrG_mono, the callee
   journal from AjxCallRh.call_effect_journal_rh_cf (the primed post's world and frame conjuncts) in place of
   acall_post_journal_xw, ajournal_x_nil_pstR / ajournal_x_subR (wle'_trans), and acall_kept_of_journal_xR.
   realloc(NULL, n) frees no live block (free_cf PNull, then malloc_cf n) and crosses no re-hide: its rule at R,
   aj_realloc_null_at_x_ct_rh below, is CfRBridgeAjReallocB.aj_realloc_null_at_x_ct lifted to R (same contract
   arealloc_null_realizes_cf, same leaf malloc_leaf_cf).
   Rule 24: no function is proved; statement composition over the cf contracts and model lemmas only. Event terms
   and numerals as in CfRBridgeAjReallocB.v. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YI16 YG0p YCbq YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import FCiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcallx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfTok YGcfRoomPre YGcfXs YGcallcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG03cf YG03dcf YG06bcf YG07cf YGcfAmx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfPath ReallocP YGcfRealloc.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfRoomKeep.
(* Required, not Imported: YGcfAmx2 restates universe_ok_of_ARcf (YGcallcf's name); cited by qualified name. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YGcfAmx2.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH YG0dH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YGcfRehidePost YG0dcfR AjxCallRh.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import CfRBridgeAjReallocB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YGcfReallocComposeRh YGcfInstReallocK.
(* stdpp, through the LPS modules, shadows several list names; the lemmas here are Stdlib's. *)
From Stdlib Require Import List.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section CfRAjRh. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Context {SK : YI16.sink_head}.
Section J.
Variable segs : list Segment.
Variable B : asyms.
Variable PST : list (Z * Z).
Hypothesis L : AR_laws_cf segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis errno_low : api_env segs B.
Hypothesis HU : universe_ok (as_universe B).
Local Abbreviation ARxs := (fun ly S Hp W mem md => ARcf segs B ly S Hp W mem md /\ xs_placed_cf ly S).
Local Abbreviation LAWS := (AR_laws_x_xs segs B L).
Local Abbreviation OWNLOW := (ARx_owned_low_law_xs segs B L).
Local Abbreviation WFL := (ARx_wf_law_xs segs B).
Local Abbreviation XSL := (ARx_xs_law_xs segs B).
Local Abbreviation LBLK := (alx_blocks segs B ARxs LAWS).
Local Abbreviation LLAY := (alx_layout segs B ARxs LAWS).

(* realloc(p, n) of a live block under the re-hide. *)
Lemma aj_realloc_at_x_ct_rh : forall (kr : nat) (pc : Z), amx_realloc_rp B (fun S => ROOM_cf_k S (RK_realloc + kr)) ->
forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa n0 n (o : Z) raw ch,
YGcfInstReallocK.arealloc_realizes_cf_k segs B Hpc pc kr ->
ajournal_xR segs B PST ARxs (wle' segs RZ_cf) STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
In (pa, n0) (ablocks B lyc Sc) -> ~ In pa Hpc ->
getr regsT 10 = w64 pa -> getr regsT 11 = w64 n ->
1 <= n < cf_malloc_max -> blocks_bytes Sc + n <= LIVE_MAX ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
QMm_cf segs B Sc memT -> ROOM_cf_k Sc (RK_realloc + kr) ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
In (call_trace lyc cf_pc_realloc_ra0 regsT ch) (as_universe B) ->
cf_hull_adm Sc n ->
(In (pa, n0) (ablocks B ly S) -> forall i, 0 <= i < req_size n0 -> inFP FP (pa + i)) ->
SRrG segs (wle' segs RZ_cf) W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xR segs B PST ARxs (wle' segs RZ_cf) STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hpc W2 mem2 md2 (k + (st_nev S2 - st_nev Sc)) /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
acall_pre_x segs B ARxs (QMm_cf segs B) lyc Sc Hpc W regsT memT mdc ch /\
(exists q p trc, sptr_addr B lyc p = pa /\ In (p, n0) (blocks Sc) /\
 apath (realloc_tree_with malloc_cf free_cf p n (call_trace lyc cf_pc_realloc_ra0 regsT ch) Sc) trc (q, S2) /\
 YG0d.gflag trc = true /\
 realloc_leaf_cf_rh segs B lyc Sc Hpc W regsT memT mdc p n0 n (q, S2) W2 c2 /\
 (q = PNull -> mt_refused malloc_cf free_cf n (call_trace lyc cf_pc_realloc_ra0 regsT ch) Sc S2) /\
 realloc_hp_cf B lyc p q Hpc = Hpc /\
 (q = PNull <-> res = 0) /\ (q <> PNull -> res = sptr_addr B ly2 q) /\
 (q <> PNull -> forall i, 0 <= i < Z.min n0 n -> aview segs (w_H W2) mem2 (res + i) = aview segs (w_H W) memT (pa + i)) /\
 (q <> PNull -> forall i, 0 <= i < 4 -> mem2 (w64 (as_errno B + i)) = memT (w64 (as_errno B + i))) /\
 (forall x : word, ~ aowned B lyc Sc (bv_unsigned x) -> ~ aowned B ly2 S2 (bv_unsigned x) ->
  ~ ascratch B ASTACK regsT (bv_unsigned x) ->
  ~ ((q <> PNull /\ res <= bv_unsigned x < res + req_size n) \/ (q <> PNull /\ pa <= bv_unsigned x < pa + req_size n0)
     \/ Exists (in_zr (bv_unsigned x)) (xs_cf lyc Sc ++ xs_cf ly2 S2)) ->
  mem2 x = memT x)) /\
((res = 0 /\ ablocks B ly2 S2 = ablocks B lyc Sc /\
  acall_kept_x segs B lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun _ => False) /\
  rd32 (aview segs (w_H W2) mem2) (as_errno B) 12 /\ aview segs (w_H W2) mem2 (as_oom_byte B) = Some 1)
 \/ (4096 <= res /\
  (exists l1 l2, ablocks B lyc Sc = l1 ++ (pa, n0) :: l2 /\ Permutation (ablocks B ly2 S2) ((res, n) :: l1 ++ l2)) /\
  acall_kept_x segs B lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o)
   (fun a => (res <= a < res + req_size n) \/ (pa <= a < pa + req_size n0))))).
Proof.
intros kr pc AMR W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa n0 n o raw ch
AREAL HJ Hin Hnhp Ha0 Ha1 Hn Hlive Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw HQM HRP Hch Htr HADM HFP.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (proj1 errno_low) as [He0 He1].
assert (ASTACK = 16384) as Has by reflexivity.
destruct (proj1 (in_ablocks B lyc Sc pa n0) Hin) as (p & Hpq & Hpin).
destruct (LBLK lyc Sc Hpc W memT mdc pa n0 HAR Hin) as (Hpa16 & Hpa4096 & Hpaceil & [Hpah Hpah2] & Hpab & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (HstkC : astk_ok ASTACK lyc (spZ regsT)).
{ unfold astk_ok, ly_bot in *. rewrite Hsp', Eslo, Eshi, Etop. repeat split; try zlia.
all: rewrite Z.add_mod, Hal16, Hal by zlia; reflexivity. }
assert (HPRE : acall_pre_x segs B ARxs (QMm_cf segs B) lyc Sc Hpc W regsT memT mdc ch).
{ destruct HstkC as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
split; [exact HAR|]. split; [rewrite Hra; exact Hraw|].
split; [exact Q1|]. split; [zlia|]. split; [zlia|]. split; [zlia|].
split; [intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia|].
split; [exact Hgp|]. split; [exact Htp|]. split; [exact Hch | exact HQM]. }
destruct (proj1 (acall_pre_x_xs segs B lyc Sc Hpc W regsT memT mdc ch) HPRE) as [HPREcf HXc].
pose proof (WFL lyc Sc Hpc W memT mdc HAR) as HWF.
pose proof (AMR Sc p n0 n (call_trace lyc cf_pc_realloc_ra0 regsT ch) HWF (QMQ_cf segs B Sc memT HQM) HRP Hpin Hn Hlive
  (admits_fix _ _ Sc HU Htr))
as (HSAFE & HPROG & HNSP & HMP).
pose proof (AREAL lyc Sc W regsT memT mdc p n0 n ch HPREcf HRP Hpin ltac:(rewrite Hpq; exact Ha0)
ltac:(rewrite Hpq; exact Hnhp) Ha1 Hn Hlive (admits_fix _ _ Sc HU Htr) HADM) as HREAL.
eapply SRrG_mono.
{ exact (amreal'_SRr'04 segs RZ_cf _ W _ _ HREAL HSAFE HPROG HNSP). }
intros W2 c2 HwleW (r & tr & Hpath & Hgf & [[Hleaf Href] _]).
pose proof (HMP tr r Hpath) as HQ. destruct r as [q S2]. unfold YGcfAmx2.realloc_post_cf in HQ.
cbn [fst snd] in HQ, Href.
destruct HQ as (Hnev2 & Hsecs2 & Hfrs2 & HblN & HblS).
pose proof Hleaf as Hleaf0.
destruct Hleaf as (ly2 & regs2 & mem2 & md2 & -> & HPOSTcf & Hres & HQT2 & Hcopy & HERR & HX2 & Herrno & Hrawf).
cbn [fst snd] in HPOSTcf, Hres, HQT2, HERR, HX2, Hcopy, Herrno, Hrawf.
assert (EHp : realloc_hp_cf B lyc p q Hpc = Hpc) by (apply cfr_aj_hp_notin; rewrite Hpq; exact Hnhp).
rewrite EHp in HPOSTcf.
pose proof HPOSTcf as (HAR2cf & Hly2 & Hwle2' & HP & Hio2 & Hfr2 & Hpres2).
assert (HAR2 : ARxs ly2 S2 Hpc W2 mem2 md2) by exact (conj HAR2cf HX2).
destruct (LLAY _ _ _ _ _ _ ly2 HAR Hly2) as (Eab & Efa & Eown).
set (f2 := fun b : sptr * Z => (sptr_addr B ly2 (fst b), snd b)).
set (fc := fun b : sptr * Z => (sptr_addr B lyc (fst b), snd b)).
assert (Efc : forall b, In b (blocks Sc) -> f2 b = fc b).
{ intros b Hb. exact (map_eq_In f2 fc (blocks Sc) b Eab Hb). }
destruct (asptr_null_dec q) as [-> | Hqn].
- (* NULL: the old block stays, Hp and the blocks are unchanged *)
cbn in Hres.
assert (Eab2 : ablocks B ly2 S2 = ablocks B lyc Sc).
{ unfold ablocks. change (map f2 (blocks S2) = map fc (blocks Sc)). rewrite (HblN eq_refl). apply map_ext_in. exact Efc. }
assert (HJ1 : ajournal_xR segs B [] ARxs (wle' segs RZ_cf) ASTACK (spZ regsT) [] lyc Sc Hpc W memT mdc [] ly2 S2 Hpc W2 mem2 md2
(st_nev S2 - st_nev Sc)).
{ eapply (call_effect_journal_rh_cf segs B ARxs LAWS segs_low errno_low OWNLOW ASTACK lyc Sc Hpc W regsT memT mdc ly2 S2 Hpc W2 mem2 md2 _
(fun a => Exists (in_zr a) (xs_cf lyc Sc ++ xs_cf ly2 S2)) [] [] (st_nev S2 - st_nev Sc));
[exact HAR2 | exact Hly2 | exact Hwle2' | exact Hio2 | exact Hfr2 | exact Hpres2 | exact HAR | exact (proj1 HAR) |
 exact HstkC | exact Hfrs2 | zlia | zlia | exact Hsecs2 | | | | exact HQT2].
- intros a Ha. apply (cfr_aj_xs_write_ok segs B L lyc Sc Hpc W memT mdc ly2 S2 Hpc W2 mem2 md2 a HAR HAR2 Hly2);
[intros b m Hb; left; rewrite Eab2; exact Hb | intros f Hf; rewrite Hfrs2; exact Hf | exact Ha].
- intros a [[Hf _] | [[Hf _] | Hx]]; [exfalso; exact (Hf eq_refl) | exfalso; exact (Hf eq_refl) | left; exact Hx].
- intros q' m i Hq Hnq Hi. exfalso. apply Hnq. rewrite Eab2. exact Hq. }
exists ly2, S2, regs2, mem2, md2, 0.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ rewrite Hsp' in HJ1. change own with ([] ++ own).
eapply (ajournal_x_subR segs B PST ARxs LAWS segs_low (wle'_trans segs RZ_cf));
[exact HJ | exact (ajournal_x_nil_pstR segs B ARxs PST _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) | zlia | zlia | intros a (rg & [] & _)]. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Hfrs2|].
split; [exact HPRE|].
split.
{ exists PNull, p, tr. split; [exact Hpq|]. split; [exact Hpin|]. split; [exact Hpath|]. split; [exact Hgf|].
split; [exact Hleaf0|]. split; [exact Href|]. split; [exact EHp|].
split; [split; intros _; reflexivity|].
split; [intros Hc; exfalso; exact (Hc eq_refl)|]. split; [intros Hc; exfalso; exact (Hc eq_refl)|].
split; [intros Hc; exfalso; exact (Hc eq_refl)|].
intros x H1 H2 H3 H4. apply Hrawf; [exact H1 | exact H2 | exact H3 |].
intros [[Hc _]|[[Hc _]|Hx]]; [exact (Hc eq_refl) | exact (Hc eq_refl) | apply H4; right; right; exact Hx]. }
left. split; [reflexivity|]. split; [exact Eab2|].
split.
{ rewrite Hsp' in HJ1. eapply (acall_kept_of_journal_xR segs B ARxs segs_low);
[exact HJ1 | exact HAR | intros a (rg & [] & _) | | exact sink_closed_nil].
intros b m i Hb Hi _. rewrite Eab2. exact Hb. }
exact (HERR eq_refl).
- (* success: the old block leaves, the new block is appended *)
destruct (HblS Hqn) as (l1 & l2 & Hsplit & Hbl2).
set (res := sptr_addr B ly2 q) in *.
assert (EabC : ablocks B lyc Sc = map fc l1 ++ (pa, n0) :: map fc l2).
{ unfold ablocks. change (map fc (blocks Sc) = map fc l1 ++ (pa, n0) :: map fc l2). rewrite Hsplit, map_app. cbn [map app].
replace (fc (p, n0)) with (pa, n0) by (subst fc; cbn [fst snd]; rewrite Hpq; reflexivity). reflexivity. }
assert (Eab2 : ablocks B ly2 S2 = map fc l1 ++ map fc l2 ++ [(res, n)]).
{ unfold ablocks. change (map f2 (blocks S2) = map fc l1 ++ map fc l2 ++ [(res, n)]). rewrite Hbl2, !map_app. cbn [map].
assert (E1 : map f2 l1 = map fc l1)
by (apply map_ext_in; intros b Hb; apply Efc; rewrite Hsplit; apply in_or_app; left; exact Hb).
assert (E2 : map f2 l2 = map fc l2)
by (apply map_ext_in; intros b Hb; apply Efc; rewrite Hsplit; apply in_or_app; right; right; exact Hb).
rewrite E1, E2. reflexivity. }
assert (Hnew : In (res, n) (ablocks B ly2 S2)).
{ rewrite Eab2. apply in_or_app. right. apply in_or_app. right. left. reflexivity. }
destruct (LBLK ly2 S2 Hpc W2 mem2 md2 res n HAR2 Hnew) as (_ & Hr4096 & _).
assert (HnewNotPre : forall a, res <= a < res + req_size n -> ~ (pa <= a < pa + req_size n0) ->
~ In (res, n) (ablocks B lyc Sc)).
{ intros a Ha Hna Hin'. rewrite EabC in Hin'. apply in_app_or in Hin' as [H1 | [H1 | H1]].
- apply in_split in H1 as (b1 & b2 & Ebq).
pose proof (sep_blocks_pos_x segs B ARxs LAWS ly2 S2 Hpc W2 mem2 md2 (res, n) (res, n) b1 (b2 ++ map fc l2) [] HAR2
ltac:(rewrite Eab2, Ebq, <- !app_assoc; reflexivity)) as Hd.
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. zlia.
- injection H1 as E1 E2. apply Hna. rewrite E1, E2. exact Ha.
- apply in_split in H1 as (b1 & b2 & Ebq).
pose proof (sep_blocks_pos_x segs B ARxs LAWS ly2 S2 Hpc W2 mem2 md2 (res, n) (res, n) (map fc l1 ++ b1) b2 [] HAR2
ltac:(rewrite Eab2, Ebq, <- !app_assoc; reflexivity)) as Hd.
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. zlia. }
assert (HJ1 : ajournal_xR segs B [] ARxs (wle' segs RZ_cf) ASTACK (spZ regsT) [(pa, pa + req_size n0)] lyc Sc Hpc W memT mdc [] ly2 S2 Hpc W2 mem2 md2
(st_nev S2 - st_nev Sc)).
{ eapply (call_effect_journal_rh_cf segs B ARxs LAWS segs_low errno_low OWNLOW ASTACK lyc Sc Hpc W regsT memT mdc ly2 S2 Hpc W2 mem2 md2 _
(fun a => Exists (in_zr a) (xs_cf lyc Sc ++ xs_cf ly2 S2) /\ ~ (pa <= a < pa + req_size n0))
[(pa, pa + req_size n0)] [] (st_nev S2 - st_nev Sc));
[exact HAR2 | exact Hly2 | exact Hwle2' | exact Hio2 | exact Hfr2 | exact Hpres2 | exact HAR | exact (proj1 HAR) |
 exact HstkC | exact Hfrs2 | zlia | zlia | exact Hsecs2 | | | | exact HQT2].
- intros a [Hx Hna]. apply (cfr_aj_xs_write_ok segs B L lyc Sc Hpc W memT mdc ly2 S2 Hpc W2 mem2 md2 a HAR HAR2 Hly2);
[ | intros f Hf; rewrite Hfrs2; exact Hf | exact Hx].
intros b m Hb. rewrite EabC in Hb. apply in_app_or in Hb as [H1 | [H1 | H1]].
+ left. rewrite Eab2. apply in_or_app. left. exact H1.
+ right. injection H1 as <- <-. exact Hna.
+ left. rewrite Eab2. apply in_or_app. right. apply in_or_app. left. exact H1.
- intros a Ha. destruct (cfr_aj_rng_dec a pa (req_size n0)) as [Hold | Hnold].
+ right. exists pa, n0. split; [left; exact Hin|]. split; [exact Hold|]. left.
exists (pa, pa + req_size n0). split; [left; reflexivity | cbn [fst snd]; zlia].
+ destruct Ha as [[_ Ha] | [[_ Ha] | Hx]].
* right. exists res, n. split; [right; exact Hnew|]. split; [exact Ha|]. right. exact (HnewNotPre a Ha Hnold).
* exfalso. rewrite Hpq in Ha. exact (Hnold Ha).
* left. exact (conj Hx Hnold).
- intros p' m i Hp' Hnp Hi. exists (pa, pa + req_size n0). split; [left; reflexivity|]. cbn [fst snd].
rewrite EabC in Hp'. apply in_app_or in Hp' as [H1 | [H1 | H1]].
+ exfalso. apply Hnp. rewrite Eab2. apply in_or_app. left. exact H1.
+ injection H1 as <- <-. zlia.
+ exfalso. apply Hnp. rewrite Eab2. apply in_or_app. right. apply in_or_app. left. exact H1. }
exists ly2, S2, regs2, mem2, md2, res.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ rewrite Hsp' in HJ1. change own with ([] ++ own).
eapply (ajournal_x_subR segs B PST ARxs LAWS segs_low (wle'_trans segs RZ_cf));
[exact HJ | exact (ajournal_x_nil_pstR segs B ARxs PST _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) | zlia | zlia |].
intros a (rg & [<-|[]] & Ha). cbn [fst snd] in Ha.
destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (pa, n0) (ablocks B ly S)) as [H0|H0].
- left. replace a with (pa + (a - pa)) by zlia. apply (HFP H0). zlia.
- right; left. exists pa, n0. split; [exact Hin|]. split; [exact H0 | zlia]. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Hfrs2|].
split; [exact HPRE|].
split.
{ exists q, p, tr. split; [exact Hpq|]. split; [exact Hpin|]. split; [exact Hpath|]. split; [exact Hgf|].
split; [exact Hleaf0|]. split; [exact Href|]. split; [exact EHp|].
split; [split; [intros Hc; exfalso; exact (Hqn Hc) | intros Hc; zlia]|].
split; [intros _; reflexivity|].
split; [intros _ i Hi; rewrite <- Hpq; exact (Hcopy Hqn i Hi)|].
split; [exact Herrno|].
intros x H1 H2 H3 H4. apply Hrawf; [exact H1 | exact H2 | exact H3 |]. rewrite Hpq. exact H4. }
right. split; [exact Hr4096|].
split.
{ exists (map fc l1), (map fc l2). split; [exact EabC|].
rewrite Eab2, app_assoc. apply Permutation_sym. apply Permutation_cons_append. }
rewrite Hsp' in HJ1.
eapply (acall_kept_of_journal_xR segs B ARxs segs_low);
[exact HJ1 | exact HAR | | | apply sink_closed_pos; constructor; [cbn [fst]; zlia | constructor]].
+ intros a (rg & [<-|[]] & Ha). cbn [fst snd] in Ha. right. exact Ha.
+ intros b m i Hb Hi HnE. rewrite EabC in Hb. apply in_app_or in Hb as [H1 | [H1 | H1]].
* rewrite Eab2. apply in_or_app. left. exact H1.
* exfalso. injection H1 as <- <-. apply HnE. right. zlia.
* rewrite Eab2. apply in_or_app. right. apply in_or_app. left. exact H1.
Qed.

(* realloc(NULL, n) at R := wle' segs RZ_cf: CfRBridgeAjReallocB.aj_realloc_null_at_x_ct with both journals
   ajournal_xR .. (wle' segs RZ_cf) and the step SRrG segs (wle' segs RZ_cf); every other premise and conclusion is
   its text. Proof: the strict rule itself, at the journal that starts at the call state (YCbqG.ajournal_x_initR's
   body at wle, STK := ASTACK, sp0 := spZ regsT, o := 0); its step lifted by SRr_SRrG (wle_wle'), its journal by
   ajournal_xR_mono (wle_wle') and ajournal_x_nil_pstR, then put under the caller's journal by ajournal_x_subR
   (wle'_trans), as aj_realloc_at_x_ct_rh does. *)
Lemma aj_realloc_null_at_x_ct_rh : forall (pc : Z),
forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k n (o : Z) raw ch,
arealloc_null_realizes_cf segs B Hpc pc ->
ajournal_xR segs B PST ARxs (wle' segs RZ_cf) STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
getr regsT 10 = w64 0 -> getr regsT 11 = w64 n ->
1 <= n < cf_malloc_max -> blocks_bytes Sc + n <= LIVE_MAX ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
QMm_cf segs B Sc memT ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
In (call_trace lyc cf_pc_realloc_ra0 regsT ch) (as_universe B) ->
SRrG segs (wle' segs RZ_cf) W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xR segs B PST ARxs (wle' segs RZ_cf) STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hpc W2 mem2 md2 (k + (st_nev S2 - st_nev Sc)) /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
acall_pre_x segs B ARxs (QMm_cf segs B) lyc Sc Hpc W regsT memT mdc ch /\
(exists q trc, apath (realloc_null_tree_with malloc_cf free_cf n (call_trace lyc cf_pc_realloc_ra0 regsT ch) Sc) trc (q, S2) /\
 YG0d.gflag trc = true /\
 malloc_leaf_cf segs B lyc Sc Hpc W regsT memT mdc n (q, S2) W2 c2 /\
 (q = PNull -> mt_refused malloc_cf free_cf n (call_trace lyc cf_pc_realloc_ra0 regsT ch) Sc S2) /\
 (q = PNull <-> res = 0) /\ (q <> PNull -> res = sptr_addr B ly2 q) /\
 (q <> PNull -> forall i, 0 <= i < 4 -> mem2 (w64 (as_errno B + i)) = memT (w64 (as_errno B + i))) /\
 (forall x : word, ~ aowned B lyc Sc (bv_unsigned x) -> ~ aowned B ly2 S2 (bv_unsigned x) ->
  ~ ascratch B ASTACK regsT (bv_unsigned x) ->
  ~ ((q <> PNull /\ res <= bv_unsigned x < res + req_size n) \/ Exists (in_zr (bv_unsigned x)) (xs_cf lyc Sc ++ xs_cf ly2 S2)) ->
  mem2 x = memT x)) /\
((res = 0 /\ ablocks B ly2 S2 = ablocks B lyc Sc /\
  acall_kept_x segs B lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun _ => False) /\
  rd32 (aview segs (w_H W2) mem2) (as_errno B) 12 /\ aview segs (w_H W2) mem2 (as_oom_byte B) = Some 1)
 \/ (4096 <= res /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] /\
  acall_kept_x segs B lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => res <= a < res + req_size n)))).
Proof.
intros pc W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k n o raw ch
ANULL HJ Ha0 Ha1 Hn Hlive Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw HQM Hch Htr.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (proj1 errno_low) as [He0 He1].
assert (ASTACK = 16384) as Has by reflexivity.
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (HstkC : astk_ok ASTACK lyc (spZ regsT)).
{ unfold astk_ok, ly_bot in *. rewrite Hsp', Eslo, Eshi, Etop. repeat split; try zlia.
all: rewrite Z.add_mod, Hal16, Hal by zlia; reflexivity. }
(* the journal at wle that starts at the call state *)
assert (J0 : ajournal_x segs B [] ARxs ASTACK (spZ regsT) [] lyc Sc Hpc W memT mdc [] lyc Sc Hpc W memT mdc 0).
{ split; [exact HAR|]. split; [apply layout_le_refl|]. split; [zlia|]. split; [apply wle_refl|].
split; [apply aos_step_refl|]. split; [reflexivity|]. split; [zlia|]. split; [zlia|].
split; [intros; reflexivity|]. split; [intros; reflexivity|]. split; [intros; reflexivity|]. split; [intros; reflexivity|].
split; [intros p m i H1 H2; exfalso; exact (H2 H1)|].
split; [intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia|].
split; [exact HstkC|]. split; [intros; reflexivity | exact HQT]. }
(* the strict rule at that journal, PST := [] *)
pose proof (aj_realloc_null_at_x_ct segs B [] L segs_low errno_low HU pc
  W regsT memT ASTACK (spZ regsT) [] lyc Sc Hpc W memT mdc [] lyc Sc Hpc mdc 0 n 0 raw ch
  ANULL J0 Ha0 Ha1 Hn Hlive ltac:(zlia) ltac:(reflexivity) ltac:(zlia) ltac:(zlia) Hgp Htp Hra Hraw HQM Hch Htr) as HSR.
eapply SRrG_mono.
{ exact (SRr_SRrG segs (wle' segs RZ_cf) (wle_wle' segs RZ_cf) _ _ _ HSR). }
intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & res & Hc2 & HJ1 & Rest).
rewrite Z.add_0_l in HJ1. rewrite !Z.add_0_r, Hsp' in Rest.
assert (HJ1R : ajournal_xR segs B PST ARxs (wle' segs RZ_cf) ASTACK (sp0 + o) [] lyc Sc Hpc W memT mdc [] ly2 S2 Hpc W2 mem2 md2
(st_nev S2 - st_nev Sc)).
{ apply (ajournal_x_nil_pstR segs B ARxs PST). rewrite <- Hsp'.
eapply ajournal_xR_mono; [exact (wle_wle' segs RZ_cf) | exact HJ1]. }
exists ly2, S2, regs2, mem2, md2, res.
split; [exact Hc2|].
split.
{ change own with ([] ++ own).
eapply (ajournal_x_subR segs B PST ARxs LAWS segs_low (wle'_trans segs RZ_cf));
[exact HJ | exact HJ1R | zlia | zlia | intros a (rg & [] & _)]. }
exact Rest.
Qed.

End J.
End CfRAjRh.

Print Assumptions aj_realloc_at_x_ct_rh.
Print Assumptions aj_realloc_null_at_x_ct_rh.
