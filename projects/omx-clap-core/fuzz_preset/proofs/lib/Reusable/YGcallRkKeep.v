(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset, the memnorm-keeping twins of the realloc call rules over a world relation R
   (YGcallRx.v section 3R: aj_realloc_at_xR / aj_realloc_xR) and of their cf instance from the cgif layer's primed _k
   row (YGcallRcf.v: arealloc_realizes_x_cfR, aj_realloc_at_x_cfR / aj_realloc_x_cfR, which take
   YGcfInstReallocK.arealloc_realizes_cf_k).  rule 24: proves no function (kind: invariant lemma).
   1. THE LEAF AND THE TEXT (Section gr): realloc_leaf_xR_keep is YGcallRx.v's realloc_leaf_xR with the memnorm keep
      `YAkMemnorm.memnorm segs mem -> YAkMemnorm.memnorm segs mem'` as its LAST conjunct, flat, after the raw frame (the
      place YGcallRxKeep.v's malloc_leaf_x_keep has it); arealloc_realizes_xR_keep is arealloc_realizes_xR with that
      leaf. _of_keep projects a keep form to the plain one; realloc_leaf_xR_keep_of builds the keep leaf from the plain
      leaf and the keep at the leaf's end configuration (YGcfMallocCompose.v at_mem_cf, written out).
   2. THE KEEP AS A CALLEE POST: apost_keep APOST is APOST (acall_post_x's type) with the keep from the call memory to
      the post memory. The rules over R are generic in APOST, and their two post laws (YGcallx.v apost_ar_law /
      apost_j_law) only read APOST, so both pass to apost_keep APOST (apost_ar_law_keep / apost_j_law_keep). The keep
      leaf over APOST and the plain leaf over apost_keep APOST hold together (realloc_leaf_xR_keep_apost /
      realloc_leaf_xR_apost_keep: each arm's post carries the keep, and every result is in one arm), and so do the two
      texts (arealloc_realizes_xR_keep_apost).
   3. THE RULES (Section rR): aj_realloc_at_xR_keep / aj_realloc_xR_keep are aj_realloc_at_xR / aj_realloc_xR with the
      keep leaf in the text and in the post. Each is its original at APOST := apost_keep APOST, the post mapped by
      SRrG_mono; no step of the original is run again.
   4. THE CF INSTANCE (Section J): realloc_leaf_cf_xR_keep / realloc_leaf_x_xs_cfR_keep are YGcallRcf.v's
      realloc_leaf_cf_xR / realloc_leaf_x_xs_cfR for YGcfInstReallocKKeep.v's realloc_leaf_cf_rh_keep;
      arealloc_realizes_x_cfR_keep lifts YGcfInstReallocKKeep.arealloc_realizes_cf_k_keep as arealloc_realizes_x_cfR
      lifts the plain row (the same R := wle' segs RZ_cf, APOST := APOST_cf and room RQ := qtight /\ ROOM_cf_k
      (RK_realloc + k) /\ cf_hull_adm); Section instR's aj_realloc_at_x_cfR_keep / aj_realloc_x_cfR_keep are
      YGcallRcf.v's aj_realloc_at_x_cfR / aj_realloc_x_cfR, with the same binders in the same order, from the keep row.
   realloc (NULL, n) has no rule here: the _k null row YGcfInstReallocK.arealloc_null_realizes_cf_k stays unprimed and
   is the plain null row with the entry room added (YGcfInstReallocK.arealloc_null_realizes_cf_k_of; its instance
   arealloc_null_realizes_cf_k_inst takes the premises of the plain instance), so the null call rule with the keep is
   YGcallRxKeep.v's aj_realloc_null_at_x_keep over YGcfReallocComposeKeep.v's arealloc_null_realizes_cf_keep.
   Numerals: 1, 2, 3, 4, 10, 11 in getr are RISC-V register numbers (WORD); 12 (ENOMEM) and 1 (the OOM byte's value)
   are WORD; 16 (stack alignment) and 4096 (the lowest block address) are LENGTH constants of the engine's rules. No
   ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbq YCbqG YGcallx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ReallocP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YG0dH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcallRx.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------------------------------------------------------------------------- *)
(* 1. The leaf and the text, 2. the keep as a callee post, over YGcallRx.v Section gr's variables. *)
Section gr. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable QMm : astate -> (word -> option byte) -> Prop.
Variable RQ : astate -> Z -> list Z -> Prop.
Variable mt : Z -> list Z -> YG00.M sptr.
Variable nmax : Z.
Variable ft : sptr -> list Z -> YG00.M unit.
Variable WFx : astate -> Prop.
Variable XS : alayout -> astate -> list (Z * Z).

(* YGcallRx.v realloc_leaf_xR with the memnorm keep as its last conjunct. *)
Definition realloc_leaf_xR_keep
(APOST : (Z -> alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model ->
  (Z -> Prop) -> alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop))
(Hp : list Z) (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (p : sptr) (n_old n : Z)
(r : sptr * astate) (W' : world segs) (c' : config) : Prop :=
exists ly' regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
getr regs' 10 = w64 (sptr_addr B ly' (fst r)) /\ qtight (snd r) /\
(fst r = PNull ->
 APOST ASTACK ly S Hp W regs mem md (fun a => Exists (in_zr a) (XS ly S ++ XS ly' (snd r)))
   ly' (snd r) W' regs' mem' md' /\
 rd32 (aview segs (w_H W') mem') (as_errno B) 12 /\ aview segs (w_H W') mem' (as_oom_byte B) = Some 1) /\
(fst r <> PNull ->
 APOST ASTACK ly S (remove Z.eq_dec (sptr_addr B ly p) Hp) W regs mem md
   (fun a => (sptr_addr B ly' (fst r) <= a < sptr_addr B ly' (fst r) + req_size n) \/
             (sptr_addr B ly p <= a < sptr_addr B ly p + req_size n_old) \/
             Exists (in_zr a) (XS ly S ++ XS ly' (snd r)))
   ly' (snd r) W' regs' mem' md' /\
 (forall i, 0 <= i < Z.min n_old n ->
   aview segs (w_H W') mem' (sptr_addr B ly' (fst r) + i) = aview segs (w_H W) mem (sptr_addr B ly p + i))) /\
(fst r <> PNull -> forall i, 0 <= i < 4 -> mem' (w64 (as_errno B + i)) = mem (w64 (as_errno B + i))) /\
(forall x : word, ~ aowned B ly S (bv_unsigned x) -> ~ aowned B ly' (snd r) (bv_unsigned x) ->
 ~ ascratch B ASTACK regs (bv_unsigned x) ->
 ~ ((fst r <> PNull /\ sptr_addr B ly' (fst r) <= bv_unsigned x < sptr_addr B ly' (fst r) + req_size n)
    \/ (fst r <> PNull /\ sptr_addr B ly p <= bv_unsigned x < sptr_addr B ly p + req_size n_old)
    \/ Exists (in_zr (bv_unsigned x)) (XS ly S ++ XS ly' (snd r))) ->
 mem' x = mem x) /\
(YAkMemnorm.memnorm segs mem -> YAkMemnorm.memnorm segs mem').

Lemma realloc_leaf_xR_of_keep : forall APOST Hp ly S W regs mem md p n_old n r W' c',
realloc_leaf_xR_keep APOST Hp ly S W regs mem md p n_old n r W' c' ->
realloc_leaf_xR segs B XS APOST Hp ly S W regs mem md p n_old n r W' c'.
Proof.
intros APOST Hp ly S W regs mem md p n_old n r W' c' (ly' & regs' & mem' & md' & Hc & H1 & H2 & H3 & H4 & H5 & H6 & _).
exists ly', regs', mem', md'. exact (conj Hc (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 H6)))))).
Qed.

Lemma realloc_leaf_xR_keep_of : forall APOST Hp ly S W regs mem md p n_old n r W' c',
realloc_leaf_xR segs B XS APOST Hp ly S W regs mem md p n_old n r W' c' ->
(forall pc regs' mem' md', c' = cfg_at segs pc regs' mem' md' ->
 YAkMemnorm.memnorm segs mem -> YAkMemnorm.memnorm segs mem') ->
realloc_leaf_xR_keep APOST Hp ly S W regs mem md p n_old n r W' c'.
Proof.
intros APOST Hp ly S W regs mem md p n_old n r W' c' (ly' & regs' & mem' & md' & Hc & H1 & H2 & H3 & H4 & H5 & H6) HM.
exists ly', regs', mem', md'.
exact (conj Hc (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (HM _ _ _ _ Hc)))))))).
Qed.

(* YGcallRx.v arealloc_realizes_xR with the keep leaf. *)
Definition arealloc_realizes_xR_keep (R : world segs -> world segs -> Prop)
(APOST : (Z -> alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model ->
  (Z -> Prop) -> alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop))
(pc pc0 : Z) : Prop :=
forall Hp ly S W regs mem md p n_old n ch,
acall_pre_x segs B ARx QMm ly S Hp W regs mem md ch ->
RQ S n (call_trace ly pc0 regs ch) ->
In (p, n_old) (blocks S) -> getr regs 10 = w64 (sptr_addr B ly p) ->
~ In (sptr_addr B ly p) Hp ->
getr regs 11 = w64 n ->
1 <= n < nmax -> blocks_bytes S + n <= LIVE_MAX ->
admits (as_universe B) (call_trace ly pc0 regs ch) S ->
amrealG segs R (realloc_tree_with mt ft p n (call_trace ly pc0 regs ch) S) W
(cfg_at segs pc regs mem md)
(fun r W' c' => realloc_leaf_xR_keep APOST Hp ly S W regs mem md p n_old n r W' c' /\
 (fst r = PNull -> mt_refused mt ft n (call_trace ly pc0 regs ch) S (snd r))).

Lemma arealloc_realizes_xR_of_keep : forall R APOST pc pc0,
arealloc_realizes_xR_keep R APOST pc pc0 -> arealloc_realizes_xR segs B ARx QMm RQ mt nmax ft XS R APOST pc pc0.
Proof.
intros R APOST pc pc0 H Hp ly S W regs mem md p n_old n ch HPRE HRQ Hin H10 Hhid H11 Hn Hlive Htr.
eapply (amrealG_mono segs R); [|exact (H Hp ly S W regs mem md p n_old n ch HPRE HRQ Hin H10 Hhid H11 Hn Hlive Htr)].
intros r W' c' [HL HN]. exact (conj (realloc_leaf_xR_of_keep APOST Hp ly S W regs mem md p n_old n r W' c' HL) HN).
Qed.

(* A callee post with the memnorm keep from the call memory to the post memory. *)
Definition apost_keep
(APOST : (Z -> alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model ->
  (Z -> Prop) -> alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop))
(stk : Z) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (E : Z -> Prop)
(ly' : alayout) (S' : astate) (W' : world segs) (regs' : bvmap 5 word)
(mem' : word -> option byte) (md' : Model) : Prop :=
APOST stk ly S Hp W regs mem md E ly' S' W' regs' mem' md' /\
(YAkMemnorm.memnorm segs mem -> YAkMemnorm.memnorm segs mem').

Lemma apost_ar_law_keep : forall APOST, apost_ar_law segs ARx APOST -> apost_ar_law segs ARx (apost_keep APOST).
Proof.
intros APOST H stk ly S Hp W regs mem md E ly' S' W' regs' mem' md' [HP _].
exact (H stk ly S Hp W regs mem md E ly' S' W' regs' mem' md' HP).
Qed.

Lemma apost_j_law_keep : forall R APOST,
apost_j_law (SK := SK) segs B ARx R APOST -> apost_j_law (SK := SK) segs B ARx R (apost_keep APOST).
Proof.
intros R APOST H lyc Sc Hpc W regs memc mdc ly2 S2 Hp2 W2 regs2 mem2 md2 Eb XW FP1 k1 WS [HP _].
exact (H lyc Sc Hpc W regs memc mdc ly2 S2 Hp2 W2 regs2 mem2 md2 Eb XW FP1 k1 WS HP).
Qed.

(* The keep leaf over APOST is the plain leaf over apost_keep APOST. *)
Lemma realloc_leaf_xR_keep_apost : forall APOST Hp ly S W regs mem md p n_old n r W' c',
realloc_leaf_xR_keep APOST Hp ly S W regs mem md p n_old n r W' c' ->
realloc_leaf_xR segs B XS (apost_keep APOST) Hp ly S W regs mem md p n_old n r W' c'.
Proof.
intros APOST Hp ly S W regs mem md p n_old n r W' c' (ly' & regs' & mem' & md' & Hc & H1 & H2 & LN & LS & H5 & H6 & HM).
exists ly', regs', mem', md'.
refine (conj Hc (conj H1 (conj H2 (conj _ (conj _ (conj H5 H6)))))).
- intros Hq. destruct (LN Hq) as [HP Hr]. exact (conj (conj HP HM) Hr).
- intros Hq. destruct (LS Hq) as [HP Hr]. exact (conj (conj HP HM) Hr).
Qed.

(* And back: every result is in one arm, whose post carries the keep. *)
Lemma realloc_leaf_xR_apost_keep : forall APOST Hp ly S W regs mem md p n_old n r W' c',
realloc_leaf_xR segs B XS (apost_keep APOST) Hp ly S W regs mem md p n_old n r W' c' ->
realloc_leaf_xR_keep APOST Hp ly S W regs mem md p n_old n r W' c'.
Proof.
intros APOST Hp ly S W regs mem md p n_old n r W' c' (ly' & regs' & mem' & md' & Hc & H1 & H2 & LN & LS & H5 & H6).
exists ly', regs', mem', md'.
assert (HM : YAkMemnorm.memnorm segs mem -> YAkMemnorm.memnorm segs mem').
{ destruct (asptr_null_dec (fst r)) as [Hq | Hq];
  [destruct (LN Hq) as [[_ K] _] | destruct (LS Hq) as [[_ K] _]]; exact K. }
refine (conj Hc (conj H1 (conj H2 (conj _ (conj _ (conj H5 (conj H6 HM))))))).
- intros Hq. destruct (LN Hq) as [[HP _] Hr]. exact (conj HP Hr).
- intros Hq. destruct (LS Hq) as [[HP _] Hr]. exact (conj HP Hr).
Qed.

Lemma arealloc_realizes_xR_keep_apost : forall R APOST pc pc0,
arealloc_realizes_xR_keep R APOST pc pc0 ->
arealloc_realizes_xR segs B ARx QMm RQ mt nmax ft XS R (apost_keep APOST) pc pc0.
Proof.
intros R APOST pc pc0 H Hp ly S W regs mem md p n_old n ch HPRE HRQ Hin H10 Hhid H11 Hn Hlive Htr.
eapply (amrealG_mono segs R); [|exact (H Hp ly S W regs mem md p n_old n ch HPRE HRQ Hin H10 Hhid H11 Hn Hlive Htr)].
intros r W' c' [HL HN]. exact (conj (realloc_leaf_xR_keep_apost APOST Hp ly S W regs mem md p n_old n r W' c' HL) HN).
Qed.

(* ---------------------------------------------------------------------------- *)
(* 3. The rules over R with the keep leaf.                                         *)
Section r.
Context {HL : Z}.  (* AR_laws_x's head length (YCbqG.v), implicit: inferred from LAWS *)
Hypothesis LAWS : AR_laws_x segs B ARx HL.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis errno_low : api_env segs B.
Hypothesis WFL : ARx_wf_law segs ARx WFx.
Hypothesis RMX : realloc_model_law_x B RQ mt nmax ft WFx.
Hypothesis XSL : ARx_xs_law segs B ARx XS.

Section rR.
Variable R : world segs -> world segs -> Prop.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Variable APOST : (Z -> alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model ->
  (Z -> Prop) -> alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop).
Hypothesis POST_AR : apost_ar_law segs ARx APOST.
Hypothesis POST_J : apost_j_law (SK := SK) segs B ARx R APOST.

(* YGcallRx.v aj_realloc_at_xR with the keep leaf: aj_realloc_at_xR at apost_keep APOST. *)
Lemma aj_realloc_at_xR_keep : forall pcR pc0, arealloc_realizes_xR_keep R APOST pcR pc0 ->
forall {WS : list (list Z)} W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa n_old n (o : Z) raw ch,
@ajournal_xwR rc SK segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k WS ->
In (pa, n_old) (ablocks B lyc Sc) -> ~ In pa Hpc ->
getr regsT 10 = w64 pa -> getr regsT 11 = w64 n -> 1 <= n < nmax -> blocks_bytes Sc + n <= LIVE_MAX ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
QMm Sc memT ->
RQ Sc n (call_trace lyc pc0 regsT ch) ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
admits (as_universe B) (call_trace lyc pc0 regsT ch) Sc ->
(In (pa, n_old) (ablocks B ly S) -> forall i, 0 <= i < req_size n_old -> inFP FP (pa + i)) ->
SRrG segs R W (mkCfg (mkst regsT (Z_to_bv 64 pcR) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
@ajournal_xwR rc SK segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + (st_nev S2 - st_nev Sc))
  (WS ++ [call_trace lyc pc0 regsT ch]) /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
acall_pre_x segs B ARx QMm lyc Sc Hpc W regsT memT mdc ch /\
admits (as_universe B) (call_trace lyc pc0 regsT ch) Sc /\
(exists p q, sptr_addr B lyc p = pa /\ In (p, n_old) (blocks Sc) /\ sptr_addr B ly2 q = res /\ (q = PNull <-> res = 0) /\
  (exists trc, apath (realloc_tree_with mt ft p n (call_trace lyc pc0 regsT ch) Sc) trc (q, S2) /\ YG0d.gflag trc = true) /\
  realloc_leaf_xR_keep APOST Hpc lyc Sc W regsT memT mdc p n_old n (q, S2) W2 c2) /\
((res = 0 /\ Hp2 = Hpc /\ ablocks B ly2 S2 = ablocks B lyc Sc /\ blocks S2 = blocks Sc /\
  acall_kept_x segs B lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun _ => False) /\
  rd32 (aview segs (w_H W2) mem2) (as_errno B) 12 /\ aview segs (w_H W2) mem2 (as_oom_byte B) = Some 1 /\
  mt_refused mt ft n (call_trace lyc pc0 regsT ch) Sc S2)
 \/
 (4096 <= res /\ res mod 16 = 0 /\ Hp2 = remove Z.eq_dec pa Hpc /\
  (exists l1 l2, ablocks B lyc Sc = l1 ++ (pa, n_old) :: l2 /\ ablocks B ly2 S2 = l1 ++ l2 ++ [(res, n)]) /\
  (forall i, 0 <= i < Z.min n_old n -> aview segs (w_H W2) mem2 (res + i) = aview segs (w_H W) memT (pa + i)) /\
  acall_kept_x segs B lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o)
    (fun a => (res <= a < res + req_size n) \/ (pa <= a < pa + req_size n_old))))).
Proof.
intros pcR pc0 AREAL WS W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa n_old n o raw ch
HJ Hin Hhid Ha0 Ha1 Hn Hlive Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw HQM HRQ Hch Htr HFP.
eapply (SRrG_mono segs R).
{ exact (aj_realloc_at_xR (SK := SK) segs B PST ARx QMm RQ mt nmax ft WFx XS LAWS segs_low errno_low WFL RMX XSL
    R R_trans (apost_keep APOST) (apost_ar_law_keep APOST POST_AR) (apost_j_law_keep R APOST POST_J) pcR pc0
    (arealloc_realizes_xR_keep_apost R APOST pcR pc0 AREAL) (WS := WS) W regsT memT STK sp0 FP ly S Hp W0 mem md own
    lyc Sc Hpc mdc k pa n_old n o raw ch
    HJ Hin Hhid Ha0 Ha1 Hn Hlive Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw HQM HRQ Hch Htr HFP). }
intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & res & Hc & HJ2 & Hpr & Hr & Hf & HP & Ht &
  (p & q & E1 & E2 & E3 & E4 & E5 & HL0) & HA).
exists ly2, S2, Hp2, regs2, mem2, md2, res.
refine (conj Hc (conj HJ2 (conj Hpr (conj Hr (conj Hf (conj HP (conj Ht (conj _ HA)))))))).
exists p, q. exact (conj E1 (conj E2 (conj E3 (conj E4 (conj E5
  (realloc_leaf_xR_apost_keep APOST Hpc lyc Sc W regsT memT mdc p n_old n (q, S2) W2 c2 HL0)))))).
Qed.

(* YGcallRx.v aj_realloc_xR with the keep leaf: the rule at a symbolic state reaching the realloc entry. *)
Lemma aj_realloc_xR_keep : forall pcR pc0, arealloc_realizes_xR_keep R APOST pcR pc0 ->
forall {WS : list (list Z)} W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa n_old n (o : Z) spw raw ch,
st_ok segs E ss (restrict (w_H W) ms) -> ss_pc ss = pcR -> ss_resv ss = None ->
@ajournal_xwR rc SK segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k WS ->
In (pa, n_old) (ablocks B lyc Sc) -> ~ In pa Hpc ->
getr (ms_regs ms) 10 = w64 pa -> getr (ms_regs ms) 11 = w64 n -> 1 <= n < nmax -> blocks_bytes Sc + n <= LIVE_MAX ->
getr (ms_regs ms) 2 = sv_denot E (SOff 2 o) -> ew E 2 = spw -> bv_unsigned spw = sp0 ->
o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
QMm Sc (ms_mem ms) ->
RQ Sc n (call_trace lyc pc0 (ms_regs ms) ch) ->
chain_pre lyc (aview segs (w_H W) (ms_mem ms)) (ms_regs ms) ch ->
admits (as_universe B) (call_trace lyc pc0 (ms_regs ms) ch) Sc ->
(In (pa, n_old) (ablocks B ly S) -> forall i, 0 <= i < req_size n_old -> inFP FP (pa + i)) ->
SRrG segs R W (mkCfg ms mdc)
(fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
@ajournal_xwR rc SK segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + (st_nev S2 - st_nev Sc))
  (WS ++ [call_trace lyc pc0 (ms_regs ms) ch]) /\
aregs_preserved (ms_regs ms) regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
acall_pre_x segs B ARx QMm lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch /\
admits (as_universe B) (call_trace lyc pc0 (ms_regs ms) ch) Sc /\
(exists p q, sptr_addr B lyc p = pa /\ In (p, n_old) (blocks Sc) /\ sptr_addr B ly2 q = res /\ (q = PNull <-> res = 0) /\
  (exists trc, apath (realloc_tree_with mt ft p n (call_trace lyc pc0 (ms_regs ms) ch) Sc) trc (q, S2) /\ YG0d.gflag trc = true) /\
  realloc_leaf_xR_keep APOST Hpc lyc Sc W (ms_regs ms) (ms_mem ms) mdc p n_old n (q, S2) W2 c2) /\
((res = 0 /\ Hp2 = Hpc /\ ablocks B ly2 S2 = ablocks B lyc Sc /\ blocks S2 = blocks Sc /\
  acall_kept_x segs B lyc Sc W (ms_mem ms) W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun _ => False) /\
  rd32 (aview segs (w_H W2) mem2) (as_errno B) 12 /\ aview segs (w_H W2) mem2 (as_oom_byte B) = Some 1 /\
  mt_refused mt ft n (call_trace lyc pc0 (ms_regs ms) ch) Sc S2)
 \/
 (4096 <= res /\ res mod 16 = 0 /\ Hp2 = remove Z.eq_dec pa Hpc /\
  (exists l1 l2, ablocks B lyc Sc = l1 ++ (pa, n_old) :: l2 /\ ablocks B ly2 S2 = l1 ++ l2 ++ [(res, n)]) /\
  (forall i, 0 <= i < Z.min n_old n -> aview segs (w_H W2) mem2 (res + i) = aview segs (w_H W) (ms_mem ms) (pa + i)) /\
  acall_kept_x segs B lyc Sc W (ms_mem ms) W2 mem2 (sp0 + o - ASTACK) (sp0 + o)
    (fun a => (res <= a < res + req_size n) \/ (pa <= a < pa + req_size n_old))))).
Proof.
intros pcR pc0 AREAL WS W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa n_old n o spw raw ch
HS Hpcs Hrv HJ Hin Hhid Ha0 Ha1 Hn Hlb Hsp HE2 Hspw Hal Hneg Hbud Hgp Htp Hra Hraw HQM HRQ Hch Htr HFP.
eapply (SRrG_mono segs R).
{ exact (aj_realloc_xR (SK := SK) segs B PST ARx QMm RQ mt nmax ft WFx XS LAWS segs_low errno_low WFL RMX XSL
    R R_trans (apost_keep APOST) (apost_ar_law_keep APOST POST_AR) (apost_j_law_keep R APOST POST_J) pcR pc0
    (arealloc_realizes_xR_keep_apost R APOST pcR pc0 AREAL) (WS := WS) W E ss ms STK sp0 FP ly S Hp W0 mem md own
    lyc Sc Hpc mdc k pa n_old n o spw raw ch
    HS Hpcs Hrv HJ Hin Hhid Ha0 Ha1 Hn Hlb Hsp HE2 Hspw Hal Hneg Hbud Hgp Htp Hra Hraw HQM HRQ Hch Htr HFP). }
intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & res & Hc & HJ2 & Hpr & Hr & Hf & HP & Ht &
  (p & q & E1 & E2 & E3 & E4 & E5 & HL0) & HA).
exists ly2, S2, Hp2, regs2, mem2, md2, res.
refine (conj Hc (conj HJ2 (conj Hpr (conj Hr (conj Hf (conj HP (conj Ht (conj _ HA)))))))).
exists p, q. exact (conj E1 (conj E2 (conj E3 (conj E4 (conj E5
  (realloc_leaf_xR_apost_keep APOST Hpc lyc Sc W (ms_regs ms) (ms_mem ms) mdc p n_old n (q, S2) W2 c2 HL0)))))).
Qed.
End rR.
End r.
End gr.

(* ---------------------------------------------------------------------------- *)
(* 4. The cf instance from the cgif layer's primed _k row with the keep.           *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfNames YG01cf YG00cf YG0ncf YG0dcf YGcallcf YGcfRealloc YGcallRcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfTok YG07cf YG03cf YGcfRoomPre.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require
YGcfRoomKeep YGcfRehidePost YG0dcfR YGcfInstReallocK YGcfInstReallocKKeep YGcfMallocCompose YGcfMallocComposeE.

Section G. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Section J.
Variable segs : list Segment.
Variable B : asyms.
Local Abbreviation ARxs := (fun ly S Hp W mem md => ARcf segs B ly S Hp W mem md /\ YG0ncf.xs_placed_cf ly S).

(* YGcallRcf.v realloc_leaf_cf_xR with the keep: the primed keep leaf is the generic keep leaf over R at APOST_cf. *)
Lemma realloc_leaf_cf_xR_keep : forall Hp ly S W regs mem md p n_old n r W' c',
YGcfInstReallocKKeep.realloc_leaf_cf_rh_keep segs B ly S Hp W regs mem md p n_old n r W' c' ->
realloc_leaf_xR_keep segs B xs_cf (APOST_cf segs B) Hp ly S W regs mem md p n_old n r W' c'.
Proof.
intros Hp ly S W regs mem md p n_old n r W' c' [HL HM].
exact (realloc_leaf_xR_keep_of segs B xs_cf (APOST_cf segs B) Hp ly S W regs mem md p n_old n r W' c'
  (realloc_leaf_cf_xR segs B Hp ly S W regs mem md p n_old n r W' c' HL) HM).
Qed.

(* YGcallRcf.v realloc_leaf_x_xs_cfR with the keep: and back. *)
Lemma realloc_leaf_x_xs_cfR_keep : forall Hp ly S W regs mem md p n_old n r W' c',
realloc_leaf_xR_keep segs B xs_cf (APOST_cf segs B) Hp ly S W regs mem md p n_old n r W' c' ->
YGcfInstReallocKKeep.realloc_leaf_cf_rh_keep segs B ly S Hp W regs mem md p n_old n r W' c'.
Proof.
intros Hp ly S W regs mem md p n_old n r W' c' H.
split.
- exact (realloc_leaf_x_xs_cfR segs B Hp ly S W regs mem md p n_old n r W' c'
    (realloc_leaf_xR_of_keep segs B xs_cf (APOST_cf segs B) Hp ly S W regs mem md p n_old n r W' c' H)).
- destruct H as (ly' & regs' & mem' & md' & Hc & _ & _ & _ & _ & _ & _ & HM). rewrite Hc.
  exact (YGcfMallocComposeE.at_mem_cf_cfg segs _ _ _ _ _ HM).
Qed.

(* YGcallRcf.v arealloc_realizes_x_cfR with the keep texts: the keep row, for every ghost set and headroom, gives the
   generic keep text over R at R := wle' segs RZ_cf, APOST := APOST_cf, with the room RQ := qtight /\ ROOM_cf_k
   (RK_realloc + k) /\ cf_hull_adm; the post's room is dropped. *)
Lemma arealloc_realizes_x_cfR_keep : forall pc,
(forall Hp k, YGcfInstReallocKKeep.arealloc_realizes_cf_k_keep segs B Hp pc k) ->
forall k,
arealloc_realizes_xR_keep segs B ARxs (QMm_cf segs B) (fun s n _ => qtight s /\ YGcfRoomKeep.ROOM_cf_k s (YGcfRoomKeep.RK_realloc + k) /\ cf_hull_adm s n)
  malloc_cf cf_malloc_max free_cf xs_cf (wle' segs YGcfRehidePost.RZ_cf) (APOST_cf segs B) pc cf_pc_realloc_ra0.
Proof.
intros pc H k Hp ly S W regs mem md p n_old n ch HPRE (_ & HRk & HADM) Hin H10 Hhid H11 Hn Hlive Htr.
pose proof (H Hp k ly S W regs mem md p n_old n ch (acall_pre_x_xs_cf segs B ly S Hp W regs mem md ch HPRE) HRk
  Hin H10 Hhid H11 Hn Hlive Htr HADM) as H0.
cbv beta in H0 |- *.
eapply (amrealG_mono segs (wle' segs YGcfRehidePost.RZ_cf)); [|exact H0].
intros r W' c' [[HL HN] _].
split; [exact (realloc_leaf_cf_xR_keep Hp ly S W regs mem md p n_old n r W' c' HL) | exact HN].
Qed.

(* YGcallRcf.v Section instR's rules with the keep: aj_realloc_at_xR_keep / aj_realloc_xR_keep at the cf instance,
   with the same Section hypotheses and binders as aj_realloc_at_x_cfR / aj_realloc_x_cfR, from the keep row. *)
Section instR.
Context {SK : YI16.sink_head}.
Variable PST : list (Z * Z).
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x segs B ARxs HL.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis errno_low : YCbq.api_env segs B.
Hypothesis OWNLOW : ARx_owned_low_law segs B ARxs.
Hypothesis WFL : ARx_wf_law segs ARxs (Wf_cf (as_universe B)).
Hypothesis XSL : ARx_xs_law segs B ARxs xs_cf.
Hypothesis UOK : universe_ok (as_universe B).

Definition aj_realloc_at_x_cfR_keep (k : nat) (pc : Z)
  (AREAL : forall Hp k, YGcfInstReallocKKeep.arealloc_realizes_cf_k_keep segs B Hp pc k) :=
  fun (WS : list (list Z)) => aj_realloc_at_xR_keep (SK := SK) segs B PST ARxs (QMm_cf segs B) (fun s n _ => qtight s /\ YGcfRoomKeep.ROOM_cf_k s (YGcfRoomKeep.RK_realloc + k) /\ cf_hull_adm s n)
    malloc_cf cf_malloc_max free_cf (Wf_cf (as_universe B)) xs_cf LAWS segs_low errno_low WFL
    (realloc_model_law_x_cfR B k UOK) XSL (wle' segs YGcfRehidePost.RZ_cf) (wle'_trans segs YGcfRehidePost.RZ_cf)
    (APOST_cf segs B) (POST_AR_cf segs B) (POST_J_cf (SK := SK) segs B LAWS segs_low errno_low OWNLOW)
    pc cf_pc_realloc_ra0 (arealloc_realizes_x_cfR_keep pc AREAL k) (WS := WS).

Definition aj_realloc_x_cfR_keep (k : nat) (pc : Z)
  (AREAL : forall Hp k, YGcfInstReallocKKeep.arealloc_realizes_cf_k_keep segs B Hp pc k) :=
  fun (WS : list (list Z)) => aj_realloc_xR_keep (SK := SK) segs B PST ARxs (QMm_cf segs B) (fun s n _ => qtight s /\ YGcfRoomKeep.ROOM_cf_k s (YGcfRoomKeep.RK_realloc + k) /\ cf_hull_adm s n)
    malloc_cf cf_malloc_max free_cf (Wf_cf (as_universe B)) xs_cf LAWS segs_low errno_low WFL
    (realloc_model_law_x_cfR B k UOK) XSL (wle' segs YGcfRehidePost.RZ_cf) (wle'_trans segs YGcfRehidePost.RZ_cf)
    (APOST_cf segs B) (POST_AR_cf segs B) (POST_J_cf (SK := SK) segs B LAWS segs_low errno_low OWNLOW)
    pc cf_pc_realloc_ra0 (arealloc_realizes_x_cfR_keep pc AREAL k) (WS := WS).
End instR.
End J.
End G.
