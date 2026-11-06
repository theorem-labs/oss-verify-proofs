(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-30 (row M3, route R; new file). rule 24: proves no function (kind: invariant lemma; the route-R
   crossing rule of a re-hiding free call over the journal, plus the realization lifts at R).

   aj_free_at_x_ct_rh is the route-R twin of lib/Reusable/YGcallx.v aj_free_at_x_ctR (:715-821) at
   R := wle' segs RZ_cf, for the RE-HIDING cf free (the shape agreed in
   CROSSING-SHAPE-PROPOSAL.md (sha256 25c63e2cb70b; internal record) section 2). It is stated in Section n at the shape of
   lib/A/CfRBridgeAjFreeN.v: ARx := ARxs (Reusable/YGcallcf.v:252, ARcf /\ xs_placed_cf), QMm := QMm_cf segs B,
   ft := free_cf, code := as_code B, with the Section r laws of YGcallx.v from YGcallcf.v (LAWS := AR_laws_x_xs L,
   OWNLOW := ARx_owned_low_law_xs L, WFL := ARx_wf_law_xs, the model laws := alloc_model_laws_x_cf HU). Against
   aj_free_at_x_ctR's text it changes, and only:
   - the realization `afree_realizes_xR R` is `afree_realizes_cf_rh segs B` (lib/A/YG0dcfR.v:61, primed);
   - both journals are `ajournal_xR segs B PST ARxs (wle' segs RZ_cf)`, the step is `SRrG segs (wle' segs RZ_cf)`;
   - the call's QM premise `QMm Sc memT` is `QMm_cf segs B Sc memT`, by name (it carries arodata_ok_cf at the call
     memory, and since part 3c no memnorm; no separate premise at the lemma level, proposal row 5);
   - the leaf `free_leaf_xR R` is `free_leaf_cf_rh segs B` (lib/A/YG0dcfR.v:46);
   - R_trans is not a premise: R is fixed, and wle'_trans segs RZ_cf discharges it.
   QMm_cf is never unfolded here: the proof reads it only through YGcallcf's QMQ_cf and acall_pre_x_xs; no memnorm use.
   Event terms: st_nev appears only in the journal index k + (st_nev S2 - st_nev Sc) and, inside the proof, in the
   call journal's index st_nev S2 - st_nev Sc, both as YGcallx.v:722 / :791 (exception 3, the tick update).

   The proof is aj_free_at_x_ctR's, with: the callee journal from call_effect_journal_rh_cf_pst (lib/A/AjxCallRh.v:183;
   its world and frame premises are the primed post's two changed conjuncts, its ARcf premise is the call state's
   HAR); amreal'_SRr'04 (Reusable/YG0dH.v:224) in place of amrealG_SRrG04; SRrG_mono; ajournal_x_subR with
   wle'_trans segs RZ_cf; acall_kept_of_journal_xR (Reusable/YGcallx.v:676) for the kept conjunct.

   The realization lifts at R. A re-hiding leaf is not an acall_post_xR post at any R (its frame also excepts the
   call's dead set dead_shadow_new), so the YGcallx forms at R do not hold it. free_leaf_x_rh / afree_realizes_x_rh below
   are YGcallx.v's free_leaf_x / afree_realizes_x (:260 / :287) at a generic ARx with lib/A/YGcfRehidePost.v's re-hide
   post (acall_post_cf_rh's body, :330-338, with ARcf -> ARx) and amreal' segs RZ_cf, and the YGcallcf.v bridges are
   restated over them: free_leaf_cf_x_rh (:96 free_leaf_cf_x), afree_realizes_cf_x_rh (:100 afree_realizes_cf_x),
   free_leaf_cf_xs_rh (:355 free_leaf_cf_xs), afree_realizes_x_xs_rh (:392 afree_realizes_x_xs, by YG0dHc.v
   amreal'_apostg and YGcfXs.v free_cf_frame in place of amreal_ipost), free_leaf_x_xs_cf_rh (:411 free_leaf_x_xs_cf).
   No address, no ledger, no image numeral: 10 / 1 / 3 / 4 are RISC-V register numbers, 16 / 4096 / 16384 cgif's
   LENGTH constants (YGcallx.v:84-86). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0s YG0dH YG0dHc.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YI16 YG0p YCbq YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import FCiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcallx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YGcfNames YG01cf YG00cf YG0ncf YG0dcf YGcfXs YGcallcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import YGcfRehidePost YG0dcfR AjxCallRh.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope bv_scope.
Local Open Scope Z_scope.

Section n. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.

(* ---------------------------------------------------------------------------- *)
(* The primed free forms at a generic ARx (the re-hide twins of YGcallx.v:260 / :287).                       *)
Section x.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable QMm : astate -> (word -> option byte) -> Prop.
Variable ft : sptr -> list Z -> YG00.M unit.

(* YGcallx.free_leaf_x with the re-hide post: acall_post_cf_rh's body (YGcfRehidePost.v:330-338) at ARx in place of
   ARcf; every other conjunct is free_leaf_x's (= YG0dcfR.free_leaf_cf_rh's). *)
Definition free_leaf_x_rh (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (p : sptr) (n : Z)
(r : unit * astate) (W' : world segs) (c' : config) : Prop :=
exists ly' regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
(ARx ly' (snd r) Hp W' mem' md' /\ layout_le (length (st_secs S)) ly ly' /\
 wle_in segs (dead_shadow_new ly S (snd r)) W W' /\
 aregs_preserved regs regs' /\ same_io md md' /\
 (forall a, 0 <= a < 2 ^ 64 -> ~ aowned B ly S a -> ~ aowned B ly' (snd r) a -> ~ ascratch B ASTACK regs a ->
  ~ (p <> PNull /\ sptr_addr B ly p <= a < sptr_addr B ly p + req_size n) ->
  ~ dead_shadow_new ly S (snd r) a ->
  aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
 (forall a, spZ regs - ASTACK <= a < spZ regs -> apresent (w_H W') mem' a)) /\
qtight (snd r) /\
(forall i, 0 <= i < 4 -> mem' (w64 (as_errno B + i)) = mem (w64 (as_errno B + i))) /\
(forall x : word, ~ aowned B ly S (bv_unsigned x) -> ~ aowned B ly' (snd r) (bv_unsigned x) ->
 ~ ascratch B ASTACK regs (bv_unsigned x) ->
 ~ (p <> PNull /\ sptr_addr B ly p <= bv_unsigned x < sptr_addr B ly p + req_size n) ->
 mem' x = mem x).

(* YGcallx.afree_realizes_x with amreal' over RZ_cf and the leaf above (= YG0dcfR.afree_realizes_cf_rh's shape). *)
Definition afree_realizes_x_rh : Prop :=
forall ly S Hp W regs mem md p n ch,
acall_pre_x segs B ARx QMm ly S Hp W regs mem md ch ->
(p = PNull \/ In (p, n) (blocks S)) -> getr regs 10 = w64 (sptr_addr B ly p) ->
~ In (sptr_addr B ly p) Hp ->
admits (as_universe B) (call_trace ly (pc_free_ra0 (as_code B)) regs ch) S ->
amreal' segs RZ_cf (ft p (call_trace ly (pc_free_ra0 (as_code B)) regs ch) S) W
(cfg_at segs (pc_wrap_free (as_code B)) regs mem md)
(free_leaf_x_rh ly S Hp W regs mem md p n).
End x.

(* YGcallcf.v:92 free_leaf_cf_x, primed. *)
Lemma free_leaf_cf_x_rh :
free_leaf_cf_rh segs B = free_leaf_x_rh (fun ly S Hp W mem md => ARcf segs B ly S Hp W mem md).
Proof. reflexivity. Qed.

(* YGcallcf.v:96 afree_realizes_cf_x, primed. *)
Lemma afree_realizes_cf_x_rh :
afree_realizes_cf_rh segs B =
afree_realizes_x_rh (fun ly S Hp W mem md => ARcf segs B ly S Hp W mem md) (QMm_cf segs B) free_cf.
Proof. reflexivity. Qed.

(* YGcallcf.v:253's relation, verbatim *)
Local Abbreviation ARxs := (fun ly S Hp W mem md => ARcf segs B ly S Hp W mem md /\ xs_placed_cf ly S).

(* YGcallcf.v:427 free_leaf_cf_xs, primed: the leaf at ARxs from the primed cf leaf, xs_placed_cf at the call and
   free_cf's state frame. *)
Lemma free_leaf_cf_xs_rh : forall ly S Hp W regs mem md ch p n r W' c',
acall_pre_cf segs B ly S Hp W regs mem md ch -> xs_placed_cf ly S -> free_frame_cf S (snd r) ->
free_leaf_cf_rh segs B ly S Hp W regs mem md p n r W' c' -> free_leaf_x_rh ARxs ly S Hp W regs mem md p n r W' c'.
Proof.
intros ly S Hp W regs mem md ch p n r W' c' Hpre HP (FX & FS) (ly' & regs' & mem' & md' & Hc & HPOST & HQ).
rewrite (acall_post_cf_rh_unfold segs B) in HPOST. destruct HPOST as (A1 & A2 & R).
pose proof (amc_wf _ _ _ _ _ (proj1 (proj1 Hpre))) as W0. unfold Wf_cf in W0.
pose proof (xs_placed_cf_layout _ _ _ _ ly ly' S W0 A2 HP) as HP'.
assert (HX : xs_placed_cf ly' (snd r)).
{ apply (xs_placed_cf_mono ly' S (snd r)); [exact (FX ly') | intros z Hz; left; exact (FS ly' z Hz) | exact HP']. }
exists ly', regs', mem', md'. exact (conj Hc (conj (conj (conj A1 HX) (conj A2 R)) HQ)).
Qed.

(* YGcallcf.v:464 afree_realizes_x_xs, primed: the primed cf text, lifted to ARxs; no premise beyond it. free_cf's
   state frame on every granted path (YGcfXs.v free_cf_frame) rides through amreal' by amreal'_apostg (YG0dHc.v). *)
Lemma afree_realizes_x_xs_rh : afree_realizes_cf_rh segs B -> afree_realizes_x_rh ARxs (QMm_cf segs B) free_cf.
Proof.
intros AF ly S Hp W regs mem md p n ch Hpre H1 H2 H3 H4.
destruct (proj1 (acall_pre_x_xs segs B ly S Hp W regs mem md ch) Hpre) as [Hpc HX].
assert (HF : forall tr r, apath (free_cf p (call_trace ly (pc_free_ra0 (as_code B)) regs ch) S) tr r ->
  gflag tr = true -> free_frame_cf S (snd r)).
{ intros tr [[] S'] Hpath _. exact (free_cf_frame p _ S tr S' Hpath). }
pose proof (amreal'_apostg segs RZ_cf _ _ _ _ _ HF (AF ly S Hp W regs mem md p n ch Hpc H1 H2 H3 H4)) as HR.
eapply amreal'_mono; [|exact HR].
intros r W' c' [HFr Hl]. exact (free_leaf_cf_xs_rh ly S Hp W regs mem md ch p n r W' c' Hpc HX HFr Hl).
Qed.

(* YGcallcf.v:483 free_leaf_x_xs_cf, primed: the projection from the ARxs leaf to the primed cf leaf. *)
Lemma free_leaf_x_xs_cf_rh : forall ly S Hp W regs mem md p n r W' c',
free_leaf_x_rh ARxs ly S Hp W regs mem md p n r W' c' -> free_leaf_cf_rh segs B ly S Hp W regs mem md p n r W' c'.
Proof.
intros ly S Hp W regs mem md p n r W' c' (ly' & regs' & mem' & md' & Hc & ((HAR & _) & R) & Rest).
exists ly', regs', mem', md'. split; [exact Hc|]. split; [|exact Rest].
rewrite (acall_post_cf_rh_unfold segs B). exact (conj HAR R).
Qed.

(* ---------------------------------------------------------------------------- *)
(* The crossing rule.                                                             *)
Variable PST : list (Z * Z).
Hypothesis L : AR_laws_cf segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis errno_low : api_env segs B.
Hypothesis HU : universe_ok (as_universe B).

(* YGcallx.v:707 aj_free_at_x_ctR at R := wle' segs RZ_cf, re-hiding (changes in the header). *)
Lemma aj_free_at_x_ct_rh : afree_realizes_cf_rh segs B ->
forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa n (o : Z) raw ch,
ajournal_xR segs B PST ARxs (wle' segs RZ_cf) STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
In (pa, n) (ablocks B lyc Sc) -> ~ In pa Hpc ->
getr regsT 10 = w64 pa ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
QMm_cf segs B Sc memT ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
In (call_trace lyc (pc_free_ra0 (as_code B)) regsT ch) (as_universe B) ->
(In (pa, n) (ablocks B ly S) -> forall i, 0 <= i < req_size n -> inFP FP (pa + i)) ->
SRrG segs (wle' segs RZ_cf) W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_free (as_code B))) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xR segs B PST ARxs (wle' segs RZ_cf) STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hpc W2 mem2 md2 (k + (st_nev S2 - st_nev Sc)) /\
aregs_preserved regsT regs2 /\
(exists l1 l2, ablocks B lyc Sc = l1 ++ (pa, n) :: l2 /\ ablocks B ly2 S2 = l1 ++ l2) /\
frames S2 = frames Sc /\
acall_pre_x segs B ARxs (QMm_cf segs B) lyc Sc Hpc W regsT memT mdc ch /\
In (call_trace lyc (pc_free_ra0 (as_code B)) regsT ch) (as_universe B) /\
(exists q trc, sptr_addr B lyc q = pa /\ In (q, n) (blocks Sc) /\
apath (free_cf q (call_trace lyc (pc_free_ra0 (as_code B)) regsT ch) Sc) trc (tt, S2) /\ gflag trc = true /\
free_leaf_cf_rh segs B lyc Sc Hpc W regsT memT mdc q n (tt, S2) W2 c2) /\
acall_kept_x segs B lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => pa <= a < pa + req_size n)).
Proof.
intros AFCF W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa n o raw ch
HJ Hin Hnhp Ha0 Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw HQM Hch Htr HFP.
(* the Section r laws of YGcallx.v at ARxs (YGcallcf.v), and the contract at ARxs *)
pose proof L as LAWS. apply AR_laws_x_xs in LAWS.
pose proof L as OWNLOW. apply ARx_owned_low_law_xs in OWNLOW.
pose proof (ARx_wf_law_xs segs B) as WFL.
pose proof HU as AMX. apply alloc_model_laws_x_cf in AMX.
pose proof (afree_realizes_x_xs_rh AFCF) as AFREE.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (proj1 errno_low) as [He0 He1].
assert (ASTACK = 16384) as Has by reflexivity.
destruct (proj1 (in_ablocks B lyc Sc pa n) Hin) as (q & Hq & Hqin).
destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc W memT mdc pa n HAR Hin) as (Hpa16 & Hpa4096 & Hpaceil & [Hpah Hpah2] & Hpab & _).
assert (Hqnn : q <> PNull) by (intros ->; cbn in Hq; zlia).
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
pose proof (WFL lyc Sc Hpc W memT mdc HAR) as HWF.
pose proof (admits_fix _ _ Sc HU Htr) as Htr'.
destruct AMX as [_ AMF].
pose proof (AMF Sc q n (call_trace lyc (pc_free_ra0 (as_code B)) regsT ch) HWF (QMQ_cf segs B Sc memT HQM) (or_intror Hqin) Htr')
as (HSAFE & HPROG & HNSP & HMP).
pose proof (AFREE lyc Sc Hpc W regsT memT mdc q n ch HPRE (or_intror Hqin) ltac:(rewrite Hq; exact Ha0)
ltac:(rewrite Hq; exact Hnhp) Htr') as HREAL.
eapply SRrG_mono.
{ exact (amreal'_SRr'04 segs RZ_cf _ W _ _ HREAL HSAFE HPROG HNSP). }
intros W2 c2 HwleW (r & tr & Hpath & Hgf & Hleaf).
pose proof (HMP tr r Hpath) as HQ. destruct r as [[] S2]. unfold free_post_x in HQ. cbn [fst snd] in HQ.
destruct HQ as (Hnev2 & Hsecs2 & Hfrs2 & (l1 & l2 & Hsplit & Hbl2)).
destruct Hsplit as [[Hnull _] | Hsplit]; [exfalso; exact (Hqnn Hnull)|].
cbn [fst snd] in *.
pose proof Hleaf as Hleaf0.
destruct Hleaf as (ly2 & regs2 & mem2 & md2 & -> & HPOST & HQT2 & _).
(* the primed post: its world (wle_in over the call's dead set) and frame (off that set) are the callee journal's
   two premises that differ from acall_post_journal_xR's *)
pose proof HPOST as (HAR2 & Hly2 & Hwin2 & HP & Hio2 & Hfr2 & Hpres2).
destruct (alx_layout _ _ _ LAWS _ _ _ _ _ _ ly2 HAR Hly2) as (Eab & Efa & Eown).
set (f2 := fun b : sptr * Z => (sptr_addr B ly2 (fst b), snd b)).
set (fc := fun b : sptr * Z => (sptr_addr B lyc (fst b), snd b)).
assert (Efc : forall b, In b (blocks Sc) -> f2 b = fc b).
{ intros b Hb. exact (map_eq_In f2 fc (blocks Sc) b Eab Hb). }
assert (Eab2 : ablocks B ly2 S2 = map fc l1 ++ map fc l2).
{ unfold ablocks. change (map f2 (blocks S2) = map fc l1 ++ map fc l2). rewrite Hbl2, map_app.
f_equal; apply map_ext_in; intros b Hb; apply Efc; rewrite Hsplit; apply in_or_app; [left; exact Hb | right; right; exact Hb]. }
assert (EabC : ablocks B lyc Sc = map fc l1 ++ (pa, n) :: map fc l2).
{ unfold ablocks. change (map fc (blocks Sc) = map fc l1 ++ (pa, n) :: map fc l2). rewrite Hsplit, map_app. cbn [map app].
replace (fc (q, n)) with (pa, n) by (subst fc; cbn [fst snd]; rewrite Hq; reflexivity). reflexivity. }
assert (Hlive : forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> ~ (pa <= b + i < pa + req_size n) ->
In (b, m) (ablocks B ly2 S2)).
{ intros b m i Hb Hi HnE. rewrite Eab2. rewrite EabC in Hb. apply in_app_or in Hb as [Hb | [Hb | Hb]].
- apply in_or_app. left. exact Hb.
- exfalso. injection Hb as <- <-. apply HnE. zlia.
- apply in_or_app. right. exact Hb. }
assert (HgoneC : forall p m i, In (p, m) (ablocks B lyc Sc) -> ~ In (p, m) (ablocks B ly2 S2) -> 0 <= i < req_size m ->
inFP [(pa, pa + req_size n)] (p + i)).
{ intros p m i Hp0 Hnp Hi. exists (pa, pa + req_size n). split; [left; reflexivity|]. cbn [fst snd].
destruct (Z_lt_le_dec (p + i) pa) as [H1|H1]; [exfalso; apply Hnp; apply (Hlive p m i Hp0 Hi); zlia|].
destruct (Z_lt_le_dec (p + i) (pa + req_size n)) as [H2|H2]; [zlia|]. exfalso; apply Hnp; apply (Hlive p m i Hp0 Hi); zlia. }
(* the callee journal at PST = [] (call_effect_journal_rh_cf_pst): Eb is the leaf's freed block, XW is empty *)
assert (HJ1 : ajournal_xR segs B [] ARxs (wle' segs RZ_cf) ASTACK (spZ regsT) [(pa, pa + req_size n)] lyc Sc Hpc W memT mdc [] ly2 S2 Hpc W2 mem2 md2
(st_nev S2 - st_nev Sc)).
{ apply (call_effect_journal_rh_cf_pst segs B ARxs LAWS segs_low errno_low OWNLOW [] ASTACK lyc Sc Hpc W regsT memT mdc
  ly2 S2 Hpc W2 mem2 md2 (fun a => q <> PNull /\ sptr_addr B lyc q <= a < sptr_addr B lyc q + req_size n) (fun _ => False)
  [(pa, pa + req_size n)] [] (st_nev S2 - st_nev Sc));
  [exact HAR2 | exact Hly2 | exact Hwin2 | exact Hio2 | exact Hfr2 | exact Hpres2 | exact HAR | exact (proj1 HAR)
  | exact HstkC | exact Hfrs2 | zlia | zlia | exact Hsecs2 | intros a [] | | exact HgoneC | exact HQT2].
intros a [_ Ha]. right. rewrite Hq in Ha. exists pa, n. split; [left; exact Hin|]. split; [exact Ha|]. left.
exists (pa, pa + req_size n). split; [left; reflexivity | cbn; zlia]. }
exists ly2, S2, regs2, mem2, md2.
split.
{ unfold cfg_at, raZ. rewrite Hra. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
split.
{ rewrite Hsp' in HJ1. change own with ([] ++ own).
eapply (ajournal_x_subR segs B PST ARxs LAWS segs_low (wle'_trans segs RZ_cf));
[exact HJ | eapply ajournal_x_nil_pstR; exact HJ1 | zlia | zlia |].
intros a (rg & [<-|[]] & Ha). cbn [fst snd] in Ha.
destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (pa, n) (ablocks B ly S)) as [H0|H0].
- left. replace a with (pa + (a - pa)) by zlia. apply (HFP H0). zlia.
- right; left. exists pa, n. split; [exact Hin|]. split; [exact H0 | zlia]. }
split; [exact HP|].
split; [exists (map fc l1), (map fc l2); split; [exact EabC | exact Eab2]|].
split; [exact Hfrs2|].
split; [exact HPRE|]. split; [exact Htr|].
split; [exists q, tr; split; [exact Hq|]; split; [exact Hqin|]; split; [exact Hpath|]; split;
  [exact Hgf | exact (free_leaf_x_xs_cf_rh _ _ _ _ _ _ _ _ _ _ _ _ Hleaf0)]|].
rewrite Hsp' in HJ1.
eapply (acall_kept_of_journal_xR segs B ARxs segs_low);
[exact HJ1 | exact HAR | | exact Hlive | apply sink_closed_pos; constructor; [cbn [fst]; zlia | constructor]].
intros a (rg & [<-|[]] & Ha). cbn [fst snd] in Ha. exact Ha.
Qed.

End n.

(* The lane's checks: the statement with its implicit arguments, the modules of the primed forms it names, and
   Print Assumptions of every top (toolchain/allowed-axioms.txt). *)
Set Printing Implicit.
Check aj_free_at_x_ct_rh.
Unset Printing Implicit.
Locate free_leaf_cf_rh. Locate afree_realizes_cf_rh. Locate call_effect_journal_rh_cf_pst. Locate RZ_cf.
Locate dead_shadow_new.
About aj_free_at_x_ct_rh.
Print Assumptions aj_free_at_x_ct_rh.
Print Assumptions free_leaf_cf_x_rh.
Print Assumptions afree_realizes_cf_x_rh.
Print Assumptions free_leaf_cf_xs_rh.
Print Assumptions afree_realizes_x_xs_rh.
Print Assumptions free_leaf_x_xs_cf_rh.
