(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the IMAGE-FREE part of lib/A/W_journal.v (itself a remapped copy of
   proofs/plugin-hostd/fuzz_reply/lib/A/W_journal.v, origin/cold/port-reply-w2 6328acea202, blob ecd9547e32f; see
   W_journal.v's header for the renames). Split out under h-rw-pca-4's standing statement / walk rule (02:36Z) after
   h-rw-pca-7's measurement (02:33Z, donor controls clean): W_journal.v Requires PcapSyms / PcapPa / PcapPaLib for its
   Section g (paj_run_x / paj_run_to_x at the listing), and PcapPa Requires PcapList, the ASan program listing, so every
   lib/B file Requiring W_journal (PaGxSites, PcapEntryDefs, PcapEntryPhases, PcapEntryEntry, PcapEntryOpen,
   PcapEntrySkip) carried image A's listing. MOVED here unchanged, no statement text altered: the G / XO journal
   (inG, inGb, gover, gagree and their lemmas; Section b: gx_ok, ajournal_g, ajournal_gx and every lemma over it) and
   the run chain over ajournal_gx (Section e: run_post_pi_tok_AJX, SRr_chain_pi_tok_AJX, SRr_run_pi_tok_AJX,
   SRr_run_to_pi_tok_AJX), which takes the symbol type and listing as Variables. Requires only lib/Reusable and the
   image-free kit (PaTable, PaSym, PaRun, PaShadow, PaJournal). lib/B Requires THIS file. W_journal.v keeps Section g
   and Requires Export this file, so lib/A users see no change. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaRun PaShadow.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YC5d.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* G: a list of (base, length) ranges of program globals. *)
Definition inG (G : list (Z * Z)) (a : Z) : Prop := Exists (in_zr a) G.
Definition inGb (G : list (Z * Z)) (a : Z) : bool := existsb (fun r => (fst r <=? a) && (a <? fst r + snd r)) G.
Lemma inGb_spec : forall G a, inGb G a = true <-> inG G a.
Proof.
intros G a. unfold inGb, inG. rewrite existsb_exists, Exists_exists. split.
- intros (r & Hin & Hr). exists r. split; [exact Hin|]. unfold in_zr.
  apply andb_prop in Hr as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
- intros (r & Hin & Hr). exists r. split; [exact Hin|]. unfold in_zr in Hr.
  apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.
Lemma inGb_false : forall G a, inGb G a = false <-> ~ inG G a.
Proof.
intros G a. split.
- intros H HG. apply inGb_spec in HG. rewrite H in HG. discriminate.
- intros H. destruct (inGb G a) eqn:E; [exfalso; apply H; apply inGb_spec; exact E | reflexivity].
Qed.
Lemma inG_nil : forall a, ~ inG [] a.
Proof. intros a H. inversion H. Qed.
Lemma inG_app : forall G1 G2 a, inG (G1 ++ G2) a <-> inG G1 a \/ inG G2 a.
Proof. intros G1 G2 a. unfold inG. rewrite Exists_app. reflexivity. Qed.
Lemma inG_cons : forall r G a, inG (r :: G) a <-> in_zr a r \/ inG G a.
Proof.
intros r G a. unfold inG. split; intros H.
- inversion H; subst; [left | right]; assumption.
- destruct H as [H|H]; [apply Exists_cons_hd | apply Exists_cons_tl]; exact H.
Qed.
(* The memory that is m' on the bytes of G and m elsewhere. *)
Definition gover (G : list (Z * Z)) (m m' : word -> option byte) : word -> option byte :=
fun x => if inGb G (bv_unsigned x) then m' x else m x.
(* m' agrees with m, as the walk sees it (through H), on every byte outside G. *)
Definition gagree (G : list (Z * Z)) (H : word -> bool) (m m' : word -> option byte) : Prop :=
forall x : word, inGb G (bv_unsigned x) = false -> mrestrict H m' x = mrestrict H m x.
Lemma gagree_refl : forall G H m, gagree G H m m.
Proof. intros G H m x _. reflexivity. Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Local Notation ajournal := (ajournal segs B).

(* The side condition on G: image bytes outside the allocator's statics.  Such a byte is not aowned
   (AR_owned_image_law, YG0d.v:474-475), not hidden (H_off_segments), below alloc_ceiling and not in the
   shadow (segs_low).  errno is not excluded: a lane whose function stores errno may put errno's 4 bytes
   in its G if it shows them in the image and outside as_owned_static. *)
Definition gx_ok (G : list (Z * Z)) : Prop :=
forall a, inG G a -> in_img segs a /\ ~ Exists (in_zr a) (as_owned_static B).
Lemma gx_ok_nil : gx_ok [].
Proof. intros a H. exfalso. exact (inG_nil a H). Qed.
Lemma gx_ok_app : forall G1 G2, gx_ok G1 -> gx_ok G2 -> gx_ok (G1 ++ G2).
Proof. intros G1 G2 H1 H2 a Ha. apply inG_app in Ha as [Ha|Ha]; [exact (H1 a Ha) | exact (H2 a Ha)]. Qed.
Lemma gx_ok_sub : forall G1 G2, (forall a, inG G1 a -> inG G2 a) -> gx_ok G2 -> gx_ok G1.
Proof. intros G1 G2 Hs H2 a Ha. exact (H2 a (Hs a Ha)). Qed.

Lemma find_segment_img : forall a, in_img segs a -> find_segment segs a 1 <> None.
Proof.
intros a (sg & Hin & Hr). induction segs as [|s rest IH] in Hin |- *; [destruct Hin|]. cbn.
destruct (Z.leb (Z.of_N (seg_base s)) a && Z.leb (a + 1) (Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool eqn:E;
[discriminate|].
destruct Hin as [<- | Hin].
- exfalso. apply Bool.andb_false_iff in E as [E|E]; [apply Z.leb_gt in E | apply Z.leb_gt in E]; lia.
- exact (IH Hin).
Qed.
Lemma hidden_not_img : forall (W : world segs) (x : word), in_img segs (bv_unsigned x) -> w_H W x = false.
Proof.
intros W x Hi. destruct (w_H W x) eqn:E; [|reflexivity].
exfalso. exact (find_segment_img _ Hi (w_Hoff W x E)).
Qed.
Lemma inG_low : forall G a, gx_ok G -> inG G a -> 0 <= a < kLowMemEnd.
Proof. intros G a HG Ha. exact (segs_low a (proj1 (HG a Ha))). Qed.

(* Every byte the journal compares, compared against the overlaid start memory. *)
Lemma aview_gover_tr : forall G (W Wc : world segs) mem memc memc' a,
gx_ok G ->
(forall x, inGb G (bv_unsigned x) = false -> memc' x = memc x) ->
aview segs (w_H Wc) memc a = aview segs (w_H W) mem a ->
aview segs (w_H Wc) memc' a = aview segs (w_H W) (gover G mem memc') a.
Proof.
intros G W Wc mem memc memc' a HG Heq E. unfold aview, mbyte, mrestrict, gover in *.
destruct (inGb G (bv_unsigned (Z_to_bv 64 a))) eqn:Hg.
- assert (Hi : in_img segs (bv_unsigned (Z_to_bv 64 a))) by (apply HG; apply inGb_spec; exact Hg).
  rewrite (hidden_not_img Wc _ Hi), (hidden_not_img W _ Hi). reflexivity.
- rewrite (Heq _ Hg). exact E.
Qed.
Lemma aview_out_G : forall G (H : word -> bool) memc memc' a,
0 <= a < 2 ^ 64 -> ~ inG G a ->
(forall x, inGb G (bv_unsigned x) = false -> memc' x = memc x) ->
aview segs H memc' a = aview segs H memc a.
Proof.
intros G H memc memc' a Ha Hn Heq. apply aview_eq_of. unfold mrestrict.
rewrite Heq; [reflexivity|]. rewrite unsigned_lit_small by lia. apply inGb_false. exact Hn.
Qed.

(* A write to G bytes only: the journal survives with the start memory overlaid on G. *)
Lemma ajournal_rebase : forall G STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k memc',
gx_ok G ->
ajournal STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ->
(forall x, inGb G (bv_unsigned x) = false -> memc' x = memc x) ->
mem_grows (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) memc') ->
ajournal STK sp0 FP ly S W (gover G mem memc') md own lyc Sc Wc memc' mdc k.
Proof.
intros G STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k memc' HG HJ Heq Hgr.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (T : forall a, aview segs (w_H Wc) memc a = aview segs (w_H W) mem a ->
aview segs (w_H Wc) memc' a = aview segs (w_H W) (gover G mem memc') a).
{ intros a. exact (aview_gover_tr G W Wc mem memc memc' a HG Heq). }
split.
{ eapply (al_frame _ _ LAWS); [exact HAR | | | reflexivity | reflexivity | reflexivity |].
  - intros a Ha Ho. destruct (inGb G a) eqn:Hg.
    + exfalso. apply inGb_spec in Hg. destruct (HG a Hg) as [Hi Hno].
      apply Hno. exact (proj1 (al_owned_image _ _ LAWS _ _ _ _ _ a HAR Hi) Ho).
    + apply (aview_out_G G); [exact Ha | apply inGb_false; exact Hg | exact Heq].
  - intros a Hv. eapply aview_keeps_vis; [exact Hgr | exact Hv].
  - intros a _ Hh. apply Heq. destruct (inGb G (bv_unsigned (w64 a))) eqn:Hg; [|reflexivity].
    exfalso. assert (Hi : in_img segs (bv_unsigned (w64 a))) by (apply HG; apply inGb_spec; exact Hg).
    rewrite (hidden_not_img Wc _ Hi) in Hh. discriminate. }
split; [exact Hly|]. split; [exact Hsecs|]. split; [exact Hwle|]. split; [exact Hio|].
split; [exact Hfrs|]. split; [exact Hnev|]. split; [exact Hk|].
split; [intros a Ha Hs; apply T; exact (F1 a Ha Hs)|].
split; [intros p n i H1 H2 Hi Hnf; apply T; exact (F2 p n i H1 H2 Hi Hnf)|].
split; [intros a Hi Hno He Hsp; apply T; exact (F3 a Hi Hno He Hsp)|].
split; [intros cid pos a Hin Hr Hnf; apply T; exact (F4 cid pos a Hin Hr Hnf)|].
split; [exact Hgone|].
split.
{ intros a Ha. destruct (Hpres a Ha) as [Hh [b Hb]]. split; [exact Hh|]. exists b.
  rewrite Heq; [exact Hb|]. rewrite unsigned_lit_small by lia. apply inGb_false. intros HGa.
  pose proof (inG_low G a HG HGa). lia. }
split; [exact Hstatic|]. split; [intros a Hx He; apply T; exact (F5 a Hx He) | exact HQT].
Qed.

(* The start memory enters the journal only through aview: two start memories with the same view give
   the same journal. *)
Lemma ajournal_start_ext : forall STK sp0 FP ly S W mem mem' md own lyc Sc Wc memc mdc k,
ajournal STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ->
(forall a, aview segs (w_H W) mem' a = aview segs (w_H W) mem a) ->
ajournal STK sp0 FP ly S W mem' md own lyc Sc Wc memc mdc k.
Proof.
intros STK sp0 FP ly S W mem mem' md own lyc Sc Wc memc mdc k HJ Hx.
destruct HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
split; [exact HAR|]. split; [exact Hly|]. split; [exact Hsecs|]. split; [exact Hwle|]. split; [exact Hio|].
split; [exact Hfrs|]. split; [exact Hnev|]. split; [exact Hk|].
split; [intros a Ha Hs; rewrite Hx; exact (F1 a Ha Hs)|].
split; [intros p n i H1 H2 Hi Hnf; rewrite Hx; exact (F2 p n i H1 H2 Hi Hnf)|].
split; [intros a Hi Hno He Hsp; rewrite Hx; exact (F3 a Hi Hno He Hsp)|].
split; [intros cid pos a Hin Hr Hnf; rewrite Hx; exact (F4 cid pos a Hin Hr Hnf)|].
split; [exact Hgone|]. split; [exact Hpres|]. split; [exact Hstatic|].
split; [intros a Hx' He; rewrite Hx; exact (F5 a Hx' He) | exact HQT].
Qed.
Lemma aview_gagree : forall G H m m' a, gagree G H m m' -> inGb G (bv_unsigned (Z_to_bv 64 a)) = false ->
aview segs H m' a = aview segs H m a.
Proof. intros G H m m' a Hag Hg. apply aview_eq_of. exact (Hag _ Hg). Qed.

(* THE JOURNAL. *)
Definition ajournal_g (G : list (Z * Z)) (STK sp0 : Z) (FP : list (Z * Z))
(ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (md : Model)
(own : list (Z * Z))
(ly' : alayout) (S' : astate) (W' : world segs) (mem' : word -> option byte) (md' : Model) (k : Z) : Prop :=
exists memS, ajournal STK sp0 FP ly S W memS md own ly' S' W' mem' md' k /\ gagree G (w_H W) mem memS.
Definition ajournal_gx (G : list (Z * Z)) (XO : Z) (OUT : list (Z * Z)) (STK sp0 : Z) (FP : list (Z * Z))
(ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (md : Model)
(own : list (Z * Z))
(ly' : alayout) (S' : astate) (W' : world segs) (mem' : word -> option byte) (md' : Model) (k : Z) : Prop :=
0 <= STK /\ 0 <= XO /\
ajournal_g G (STK + XO) (sp0 + XO) FP ly S W mem md own ly' S' W' mem' md' k /\
(forall a, sp0 <= a < sp0 + XO -> ~ inFP OUT a -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a).

(* At G = [], XO = 0, OUT = [] it is the donor's journal. *)
Lemma ajournal_gx_nil : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
ajournal_gx [] 0 [] STK sp0 FP ly S W mem md own ly' S' W' mem' md' k <->
ajournal STK sp0 FP ly S W mem md own ly' S' W' mem' md' k.
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k. split.
- intros (_ & _ & (memS & HJ & Hag) & _). rewrite !Z.add_0_r in HJ.
  eapply ajournal_start_ext; [exact HJ|]. intros a. symmetry. apply (aview_gagree [] _ _ _ a Hag). reflexivity.
- intros HJ. pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & Hstk0 & _) & _).
  split; [lia|]. split; [lia|]. split; [exists mem; split; [rewrite !Z.add_0_r; exact HJ | apply gagree_refl]|].
  intros a Ha. lia.
Qed.
Lemma ajournal_gx_pack : forall G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k memS,
0 <= STK -> 0 <= XO ->
ajournal (STK + XO) (sp0 + XO) FP ly S W memS md own ly' S' W' mem' md' k -> gagree G (w_H W) mem memS ->
(forall a, sp0 <= a < sp0 + XO -> ~ inFP OUT a -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a) ->
ajournal_gx G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k.
Proof.
intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k memS H0 H1 HJ Hag Hout.
split; [exact H0|]. split; [exact H1|]. split; [exists memS; split; [exact HJ | exact Hag] | exact Hout].
Qed.
(* For a function with no out-parameter the out clause is empty. *)
Lemma out_none : forall (W W' : world segs) mem mem' sp0 OUT a,
sp0 <= a < sp0 + 0 -> ~ inFP OUT a -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
Proof. intros. lia. Qed.

(* The entry: the GUIDE's ajournal_init, at any G, with the window raised by XO. *)
Lemma ajournal_gx_init : forall G XO OUT STK FP ly S W regs mem md ch,
afn_pre segs B STK ly S W regs mem md ch ->
0 <= XO -> XO mod 16 = 0 -> spZ regs + XO <= ly_top ly ->
(forall a, spZ regs <= a < spZ regs + XO -> apresent (w_H W) mem a) ->
ajournal_gx G XO OUT STK (spZ regs) FP ly S W mem md [] ly S W mem md 0.
Proof.
intros G XO OUT STK FP ly S W regs mem md ch HPRE HXO HX16 HXtop HXp.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
apply (ajournal_gx_pack G XO OUT STK (spZ regs) FP ly S W mem md [] ly S W mem md 0 mem); [lia | lia | | apply gagree_refl |].
- split; [exact HAR|]. split; [apply layout_le_refl|]. split; [lia|]. split; [apply wle_refl|]. split; [apply aos_step_refl|].
  split; [reflexivity|]. split; [lia|]. split; [lia|].
  split; [intros; reflexivity|]. split; [intros; reflexivity|]. split; [intros; reflexivity|]. split; [intros; reflexivity|].
  split; [intros p n i H1 H2; exfalso; exact (H2 H1)|].
  split; [intros a Ha; destruct (Z.lt_ge_cases a (spZ regs)); [apply Hpres; lia | apply HXp; lia]|].
  split; [|split; [intros; reflexivity | exact HQT]].
  unfold astk_ok. rewrite Z.add_mod, Hal, HX16 by lia. cbn. lia.
- intros a Ha _. reflexivity.
Qed.

(* The write obligation of a run: every written byte is an awr_byte of the function's OWN window (and not
   one of its out cells' window), or a byte of G, or an out cell. *)
Definition awr_ok_x (E : env) (rs : smem) (G : list (Z * Z)) (XO : Z) (OUT : list (Z * Z))
(STK sp0 : Z) (FP : list (Z * Z)) (bl0 blc : list (Z * Z)) (ly : alayout) (own : list (Z * Z)) : Prop :=
forall a, in_wrange E rs a ->
(awr_byte STK sp0 FP bl0 blc ly own a /\ ~ (sp0 <= a < sp0 + XO)) \/ inG G a \/ (inFP OUT a /\ sp0 <= a < sp0 + XO).
Lemma awr_ok_x_of0 : forall E rs G OUT STK sp0 FP bl0 blc ly own,
awr_ok E rs STK sp0 FP bl0 blc ly own -> awr_ok_x E rs G 0 OUT STK sp0 FP bl0 blc ly own.
Proof. intros E rs G OUT STK sp0 FP bl0 blc ly own H a Ha. left. split; [exact (H a Ha) | lia]. Qed.
Lemma awr_ok_x_of : forall E rs G XO OUT STK sp0 FP bl0 blc ly own,
awr_ok E rs STK sp0 FP bl0 blc ly own -> (forall a, in_wrange E rs a -> ~ (sp0 <= a < sp0 + XO)) ->
awr_ok_x E rs G XO OUT STK sp0 FP bl0 blc ly own.
Proof. intros E rs G XO OUT STK sp0 FP bl0 blc ly own H Hn a Ha. left. split; [exact (H a Ha) | exact (Hn a Ha)]. Qed.
Lemma awr_ok_x_nil : forall E G XO OUT STK sp0 FP bl0 blc ly own, awr_ok_x E [] G XO OUT STK sp0 FP bl0 blc ly own.
Proof. intros E G XO OUT STK sp0 FP bl0 blc ly own a (r & Hin & _). destruct Hin. Qed.
Lemma awr_ok_x_cons : forall E r rs G XO OUT STK sp0 FP bl0 blc ly own,
(forall a, base_val E (r_base r) + r_wlo r <= a < base_val E (r_base r) + r_whi r ->
 (awr_byte STK sp0 FP bl0 blc ly own a /\ ~ (sp0 <= a < sp0 + XO)) \/ inG G a \/ (inFP OUT a /\ sp0 <= a < sp0 + XO)) ->
awr_ok_x E rs G XO OUT STK sp0 FP bl0 blc ly own -> awr_ok_x E (r :: rs) G XO OUT STK sp0 FP bl0 blc ly own.
Proof.
intros E r rs G XO OUT STK sp0 FP bl0 blc ly own H1 H2 a (r' & Hin & Hr). destruct Hin as [<- | Hin].
- exact (H1 a Hr).
- apply H2. exists r'. split; [exact Hin | exact Hr].
Qed.
(* A region of a global, all of whose writable bytes lie in G. *)
Lemma awr_ok_x_cons_g : forall E r rs G XO OUT STK sp0 FP bl0 blc ly own,
(forall a, base_val E (r_base r) + r_wlo r <= a < base_val E (r_base r) + r_whi r -> inG G a) ->
awr_ok_x E rs G XO OUT STK sp0 FP bl0 blc ly own -> awr_ok_x E (r :: rs) G XO OUT STK sp0 FP bl0 blc ly own.
Proof. intros E r rs G XO OUT STK sp0 FP bl0 blc ly own H1 H2. apply awr_ok_x_cons; [|exact H2]. intros a Ha. right; left. exact (H1 a Ha). Qed.
(* A region whose writable bytes are awr_bytes (the GUIDE's awr_ok_tac proves the premise for one region). *)
Lemma awr_ok_x_cons_awr0 : forall E r rs G OUT STK sp0 FP bl0 blc ly own,
awr_ok E [r] STK sp0 FP bl0 blc ly own ->
awr_ok_x E rs G 0 OUT STK sp0 FP bl0 blc ly own -> awr_ok_x E (r :: rs) G 0 OUT STK sp0 FP bl0 blc ly own.
Proof.
intros E r rs G OUT STK sp0 FP bl0 blc ly own H1 H2. apply awr_ok_x_cons; [|exact H2].
intros a Ha. left. split; [|lia]. apply H1. exists r. split; [left; reflexivity | exact Ha].
Qed.

(* A step of the program: the donor's ajournal_exec (YCbq.v:635) over ajournal_gx. *)
Lemma ajournal_gx_exec : forall G XO OUT STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k memc' mdc' (Wr : Z -> Prop),
gx_ok G ->
ajournal_gx G XO OUT STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ->
(forall x : word, ~ Wr (bv_unsigned x) -> mrestrict (w_H Wc) memc' x = mrestrict (w_H Wc) memc x) ->
mem_grows (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) memc') ->
(forall x : word, w_H Wc x = true -> memc' x = memc x) ->
same_but_materialized mdc mdc' ->
(forall a, Wr a -> (awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ ~ (sp0 <= a < sp0 + XO)) \/
 inG G a \/ (inFP OUT a /\ sp0 <= a < sp0 + XO)) ->
ajournal_gx G XO OUT STK sp0 FP ly S W mem md own lyc Sc Wc memc' mdc' k.
Proof.
intros G XO OUT STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k memc' mdc' Wr HG HJ Hfr Hgr Hhid Hsame HW.
destruct HJ as (HSTK & HXO & (memS & HJ & Hag) & Hout).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (memM := fun x : word => if inGb G (bv_unsigned x) then memc x else memc' x).
assert (HM : forall x, inGb G (bv_unsigned x) = false -> memc' x = memM x)
by (intros x Hg; unfold memM; rewrite Hg; reflexivity).
assert (HJM : ajournal (STK + XO) (sp0 + XO) FP ly S W memS md own lyc Sc Wc memM mdc' k).
{ eapply (ajournal_exec segs B LAWS segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ memM mdc'
    (fun a => Wr a /\ ~ inG G a) HJ).
  - intros x Hx. unfold memM, mrestrict. destruct (inGb G (bv_unsigned x)) eqn:Hg; [reflexivity|].
    pose proof (Hfr x ltac:(intros HWx; apply Hx; split; [exact HWx | apply inGb_false; exact Hg])) as E.
    unfold mrestrict in E. exact E.
  - intros x Hx. pose proof (Hgr x) as Hg1. unfold memM, mrestrict in Hx, Hg1 |- *.
    destruct (w_H Wc x); [exact Hx|]. destruct (inGb G (bv_unsigned x)); [exact Hx | exact (Hg1 Hx)].
  - intros x Hh. unfold memM. destruct (inGb G (bv_unsigned x)); [reflexivity|]. exact (Hhid x Hh).
  - exact Hsame.
  - intros a [HWa HnG]. destruct (HW a HWa) as [[Haw _] | [HGa | [_ Hwin]]].
    + destruct Haw as [Hs | Hrest]; [left; lia | right; exact Hrest].
    + exfalso. exact (HnG HGa).
    + left. lia. }
assert (Hgr2 : mem_grows (mrestrict (w_H Wc) memM) (mrestrict (w_H Wc) memc')).
{ intros x Hx. pose proof (Hgr x) as Hg1. unfold memM, mrestrict in Hx, Hg1 |- *.
  destruct (w_H Wc x); [exact Hx|]. destruct (inGb G (bv_unsigned x)); [exact (Hg1 Hx) | exact Hx]. }
pose proof (ajournal_rebase G _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ memc' HG HJM HM Hgr2) as HJ2.
apply (ajournal_gx_pack G XO OUT STK sp0 FP ly S W mem md own lyc Sc Wc memc' mdc' k (gover G memS memc') HSTK HXO HJ2).
- intros x Hg. unfold mrestrict, gover. rewrite Hg. exact (Hag x Hg).
- intros a Ha Hno. rewrite <- (Hout a Ha Hno). apply aview_eq_of. apply Hfr.
  rewrite unsigned_lit_small by lia. intros HWa. destruct (HW a HWa) as [[_ Hn] | [HGa | [Ho _]]].
  + exact (Hn Ha).
  + pose proof (inG_low G a HG HGa). lia.
  + exact (Hno Ho).
Qed.
Lemma ajournal_gx_materialize : forall G XO OUT STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k X,
ajournal_gx G XO OUT STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ->
ajournal_gx G XO OUT STK sp0 FP ly S W mem md own lyc Sc Wc memc (with_vm_backing (m_vm_lazy mdc) X mdc) k.
Proof.
intros G XO OUT STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k X (H0 & H1 & (memS & HJ & Hag) & Hout).
apply (ajournal_gx_pack G XO OUT STK sp0 FP ly S W mem md own lyc Sc Wc memc _ k memS H0 H1); [|exact Hag | exact Hout].
apply (ajournal_materialize segs B LAWS segs_low). exact HJ.
Qed.
(* What the caller reads off a callee's journal: the donor's facts, outside G. *)
Lemma ajournal_gx_inner : forall G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
ajournal_gx G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
exists memS, ajournal (STK + XO) (sp0 + XO) FP ly S W memS md own ly' S' W' mem' md' k /\
(forall a, ~ inG G (bv_unsigned (Z_to_bv 64 a)) -> aview segs (w_H W) memS a = aview segs (w_H W) mem a).
Proof.
intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k (_ & _ & (memS & HJ & Hag) & _).
exists memS. split; [exact HJ|]. intros a Ha. apply (aview_gagree G _ _ _ a Hag). apply inGb_false. exact Ha.
Qed.
Lemma ajournal_gx_AR : forall G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
ajournal_gx G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k -> AR segs B ly' S' W' mem' md'.
Proof. intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k (_ & _ & (memS & HJ & _) & _). exact (proj1 HJ). Qed.
Lemma ajournal_gx_G_mono : forall G G' XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
(forall a, inG G a -> inG G' a) ->
ajournal_gx G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
ajournal_gx G' XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k.
Proof.
intros G G' XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k Hs (H0 & H1 & (memS & HJ & Hag) & Hout).
split; [exact H0|]. split; [exact H1|]. split; [|exact Hout]. exists memS. split; [exact HJ|].
intros x Hg. apply Hag. apply inGb_false. intros HGa. apply inGb_false in Hg. exact (Hg (Hs _ HGa)).
Qed.

(* A CALLEE'S JOURNAL INSIDE ITS CALLER'S: the donor's ajournal_sub (YCbq.v:724) over ajournal_gx.  The
   callee's start memory memS1 agrees with the caller's current memory outside G only, so the composed
   start memory takes the bytes of G from memS1 and every other byte from the caller's start memory memS0. *)
Lemma aview_gover_sub : forall G (W Wc : world segs) memS0 memS1 memc a,
gx_ok G -> gagree G (w_H Wc) memc memS1 ->
aview segs (w_H Wc) memc a = aview segs (w_H W) memS0 a ->
aview segs (w_H Wc) memS1 a = aview segs (w_H W) (gover G memS0 memS1) a.
Proof.
intros G W Wc memS0 memS1 memc a HG Hag E.
destruct (inGb G (bv_unsigned (Z_to_bv 64 a))) eqn:Hg.
- assert (Hi : in_img segs (bv_unsigned (Z_to_bv 64 a))) by (apply HG; apply inGb_spec; exact Hg).
  unfold aview, mbyte, mrestrict, gover. rewrite Hg, (hidden_not_img Wc _ Hi), (hidden_not_img W _ Hi). reflexivity.
- rewrite (aview_gagree G _ _ _ a Hag Hg), E. apply aview_eq_of. unfold mrestrict, gover. rewrite Hg. reflexivity.
Qed.
(* The inner journals: the donor's ajournal_sub with the callee's start memory memS1. *)
Lemma ajournal_sub_g : forall G STK sp0 FP ly S W memS0 md own lyc Sc Wc memc mdc k memS1
STK1 sp1 FP1 nf ly2 S2 W2 mem2 md2 k1,
gx_ok G ->
ajournal STK sp0 FP ly S W memS0 md own lyc Sc Wc memc mdc k ->
ajournal STK1 sp1 FP1 lyc Sc Wc memS1 mdc nf ly2 S2 W2 mem2 md2 k1 ->
gagree G (w_H Wc) memc memS1 ->
sp0 - STK <= sp1 - STK1 -> sp1 <= sp0 ->
(forall a, inFP FP1 a -> (inFP FP a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n) \/
 in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a) ->
ajournal STK sp0 FP ly S W (gover G memS0 memS1) md (nf ++ own) ly2 S2 W2 mem2 md2 (k + k1).
Proof.
intros G STK sp0 FP ly S W memS0 md own lyc Sc Wc memc mdc k memS1 STK1 sp1 FP1 nf ly2 S2 W2 mem2 md2 k1 HG
(HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT)
(HAR2 & Hly2 & Hsecs2 & Hwle2 & Hio2 & Hfrs2 & Hnev2 & Hk2 & G1 & G2 & G3 & G4 & Hgone2 & Hpres2 & Hstatic2 & G5 & HQT2)
Hag Hlo Hhi HF.
pose proof Hstatic as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (T : forall a, aview segs (w_H W2) mem2 a = aview segs (w_H Wc) memS1 a ->
  aview segs (w_H Wc) memc a = aview segs (w_H W) memS0 a ->
  aview segs (w_H W2) mem2 a = aview segs (w_H W) (gover G memS0 memS1) a).
{ intros a E1 E0. rewrite E1. exact (aview_gover_sub G W Wc memS0 memS1 memc a HG Hag E0). }
assert (E1 : forall a, alloc_ceiling <= a < 2 ^ 64 -> aview segs (w_H Wc) memS1 a = aview segs (w_H Wc) memc a).
{ intros a Ha. apply (aview_gagree G _ _ _ a Hag). rewrite unsigned_lit_small by lia. apply inGb_false.
  intros HGa. pose proof (inG_low G a HG HGa). lia. }
split; [exact HAR2|].
split; [eapply layout_le_trans; [exact Hsecs | exact Hly | exact Hly2]|].
split; [lia|]. split; [eapply wle_trans; eassumption|].
assert (HFo : YI16.sink_open_fp FP1 -> YI16.sink_open_fp FP).
{ intros (r & Hr & H0). destruct (HF 0 (ex_intro _ r (conj Hr H0))) as [((r' & Hr' & H0') & _) | (b & n & Hin & _ & Hb)].
  - exists r'. split; [exact Hr' | exact H0'].
  - exfalso. pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & H4096 & _). lia. }
split; [eapply aos_step_trans_fp; [exact HFo | exact Hio | exact Hio2]|].
split; [rewrite Hfrs2, Hfrs, app_assoc; reflexivity|]. split; [lia|]. split; [lia|].
split.
{ intros a Ha Hs. apply T; [apply G1; [exact Ha | lia] | exact (F1 a Ha Hs)]. }
split.
{ intros p n i H1 H2 Hi Hnf.
  assert (Hc2 : In (p, n) (ablocks B lyc Sc)).
  { destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (p, n) (ablocks B lyc Sc)) as [Hc|Hc]; [exact Hc|].
    exfalso. exact (Hnf (Hgone p n i H1 Hc Hi)). }
  apply T; [|exact (F2 p n i H1 Hc2 Hi Hnf)].
  apply (G2 p n i Hc2); [exact H2 | exact Hi |].
  intros Hf1. destruct (HF _ Hf1) as [[Hf _] | (b & m & Hbin & Hb0 & Hr)]; [exact (Hnf Hf)|].
  assert (Hne : (b, m) <> (p, n)) by (intros E; rewrite E in Hb0; exact (Hb0 H1)).
  pose proof (sep_blocks segs B LAWS lyc Sc Wc memc mdc b m p n HAR Hbin Hc2 Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
split.
{ intros a Hi Hns He Hsp. apply T; [|exact (F3 a Hi Hns He Hsp)].
  apply (G3 a Hi Hns He). intros Ho1. exact (Hsp (HFo Ho1)). }
split.
{ intros cid pos a Hin Hr Hnf.
  assert (HinC : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; right; exact Hin).
  assert (Efr : frame_addr lyc cid pos = frame_addr ly cid pos).
  { unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
  apply T; [|exact (F4 cid pos a Hin Hr Hnf)].
  apply (G4 cid pos a HinC).
  - unfold frame_rng in *. cbn [fst snd] in *. rewrite Efr. exact Hr.
  - intros Hf1. destruct (HF _ Hf1) as [[Hf _] | (b & m & Hbin & Hb0 & Hrb)]; [exact (Hnf Hf)|].
    destruct (frames_bounds segs B LAWS lyc Sc Wc memc mdc cid pos HAR HinC) as (Hf0 & Hfc & Hfh).
    destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc b m HAR Hbin) as (_ & _ & _ & [Hh1 Hh2] & _).
    pose proof (sep_block_frame segs B LAWS lyc Sc Wc memc mdc b m cid pos HAR Hbin HinC) as Hd.
    unfold zdisjoint, frame_rng, in_zr in Hd, Hr. cbn [fst snd] in Hd, Hr. rewrite Efr in Hd.
    pose proof (shadow_addr_bounds (frame_addr ly cid pos) ltac:(zlia)).
    pose proof (shadow_addr_bounds (frame_addr ly cid pos + fs_frame_bytes cid) ltac:(zlia)).
    pose proof (shadow_range_end (frame_addr ly cid pos) (fs_frame_bytes cid) (fs_frame_bytes_nonneg cid)).
    destruct Hr as [Hr|Hr]; zlia. }
split.
{ intros p n i H1 H2 Hi.
  destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (p, n) (ablocks B lyc Sc)) as [Hc|Hc];
  [|exact (Hgone p n i H1 Hc Hi)].
  assert (Hf1 : inFP FP1 (p + i)) by (apply (Hgone2 p n i Hc); [exact H2 | exact Hi]).
  destruct (HF _ Hf1) as [[Hf _] | (b & m & Hbin & Hb0 & Hr)]; [exact Hf|].
  assert (Hne : (b, m) <> (p, n)) by (intros E; rewrite E in Hb0; exact (Hb0 H1)).
  pose proof (sep_blocks segs B LAWS lyc Sc Wc memc mdc b m p n HAR Hbin Hc Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
split.
{ intros a Ha.
  destruct (Z_lt_le_dec a (sp1 - STK1)) as [Hb|Hb]; [|destruct (Z_lt_le_dec a sp1) as [Hb2|Hb2]; [apply Hpres2; lia|]].
  - apply (apresent_transfer segs (w_H Wc) (w_H W2) memc mem2 a);
    [lia | intros Him; pose proof (segs_low a Him); lia | | apply Hpres; exact Ha].
    rewrite (G1 a ltac:(lia) ltac:(lia)). apply E1. lia.
  - apply (apresent_transfer segs (w_H Wc) (w_H W2) memc mem2 a);
    [lia | intros Him; pose proof (segs_low a Him); lia | | apply Hpres; exact Ha].
    rewrite (G1 a ltac:(lia) ltac:(lia)). apply E1. lia. }
split; [exact Hstatic|]. split; [|exact HQT2].
{ intros a HXa He.
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eextra & _).
  apply T; [apply G5; [rewrite Eextra; exact HXa | exact He] | exact (F5 a HXa He)]. }
Qed.
(* W3Checks' statement.  The out clause: a byte of [sp0, sp0 + XO0) outside OUT0 is outside the callee's
   window (callee's frame clause), or in [sp1, sp1 + XO1) outside OUT1 (callee's out clause), since an out
   cell of the callee in [sp0, sp0 + XO0) is one of OUT0. *)
Lemma ajournal_gx_sub : forall G STK sp0 XO0 OUT0 FP ly S W mem md own lyc Sc Wc memc mdc k
STK1 sp1 XO1 OUT1 FP1 nf ly2 S2 W2 mem2 md2 k1,
ajournal_gx G XO0 OUT0 STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ->
ajournal_gx G XO1 OUT1 STK1 sp1 FP1 lyc Sc Wc memc mdc nf ly2 S2 W2 mem2 md2 k1 ->
sp0 - STK <= sp1 - STK1 -> sp1 <= sp0 -> sp1 + XO1 <= sp0 + XO0 ->
(forall a, inFP OUT1 a -> (sp0 - STK <= a < sp0) \/ inFP OUT0 a) ->
gx_ok G ->
(forall a, inFP FP1 a -> (inFP FP a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n) \/
 in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a) ->
ajournal_gx G XO0 OUT0 STK sp0 FP ly S W mem md (nf ++ own) ly2 S2 W2 mem2 md2 (k + k1).
Proof.
intros G STK sp0 XO0 OUT0 FP ly S W mem md own lyc Sc Wc memc mdc k STK1 sp1 XO1 OUT1 FP1 nf ly2 S2 W2 mem2 md2 k1
(HSTK & HXO0 & (memS0 & HJ0 & Hag0) & Hout0) (HSTK1 & HXO1 & (memS1 & HJ1 & Hag1) & Hout1) Hlo Hhi Hxo HO HG HF.
pose proof HJ0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
apply (ajournal_gx_pack G XO0 OUT0 STK sp0 FP ly S W mem md (nf ++ own) ly2 S2 W2 mem2 md2 (k + k1)
  (gover G memS0 memS1) HSTK HXO0).
- apply (ajournal_sub_g G (STK + XO0) (sp0 + XO0) FP ly S W memS0 md own lyc Sc Wc memc mdc k memS1
    (STK1 + XO1) (sp1 + XO1) FP1 nf ly2 S2 W2 mem2 md2 k1 HG HJ0 HJ1 Hag1); [lia | lia | exact HF].
- intros x Hg. unfold mrestrict, gover. rewrite Hg. exact (Hag0 x Hg).
- intros a Ha Hno.
  destruct (Z_lt_le_dec a (sp1 + XO1)) as [Hin1 | Hge1].
  + assert (Hno1 : ~ inFP OUT1 a) by (intros Ho; destruct (HO a Ho) as [Hs | Ho0]; [lia | exact (Hno Ho0)]).
    rewrite (Hout1 a ltac:(lia) Hno1). exact (Hout0 a Ha Hno).
  + rewrite (G1 a ltac:(lia) ltac:(lia)).
    rewrite (aview_gagree G _ _ _ a Hag1).
    * exact (Hout0 a Ha Hno).
    * rewrite unsigned_lit_small by lia. apply inGb_false. intros HGa. pose proof (inG_low G a HG HGa). lia.
Qed.
End b.

(* The run chain of Reusable/YC80.v:53-141, over ajournal_gx. *)
Section e.
Variable psym : Type.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis Hwx : wx_segs_nowrap segs.
Variable fetch : Z -> option Z.
Variable val : nat -> Z.
Variable sigma : psym -> Z.
Variable listing : ptable psym.
Variable tpi0 : ptree psym.
Variable tw0 : ctable.
Hypothesis Hfetch : forall pc w, fetch pc = Some w -> fetch_word segs (Z_to_bv 64 pc) = Some (Z_to_bv 32 w).
Hypothesis Hcert : pi_check psym fetch val sigma listing = true.
Hypothesis HB : 0 <= val A_TEXT /\ val A_TEXT + 2 ^ 40 < 2 ^ 64 /\ val A_TEXT mod 4 = 0.
Variable A_LIM : nat.
Hypothesis HLIM0 : (A_TEXT < A_LIM)%nat.
Hypothesis HLIM : forallb (pinstr_atoms_ltb A_LIM) listing = true.
Hypothesis HLEN : 4 * Z.of_nat (length listing) <= 2 ^ 40.
Hypothesis Htpi : ptree_of_list listing = tpi0.
Hypothesis Htw : tw_of 0 listing = tw0.
Variable G : list (Z * Z).
Hypothesis HG : gx_ok segs B G.
Variable XO : Z.
Variable OUT : list (Z * Z).
Local Notation ajournal_gx := (ajournal_gx segs B G XO OUT).
Local Notation img_env := (img_env val A_LIM).
Local Notation st_ok_pi := (st_ok_pi segs val).
Definition run_post_pi_tok_AJX (W : world segs) (E : env) (K : nat) (Bx : sv) (SH : list shent) (ss : sstate) (st' : shst)
(r : ptrun_status psym)
(ms : machine_state) (STK sp0 : Z) (FP : list (Z * Z)) ly S W0 mem md own lyc Sc (mdc : Model) (k : Z)
(Q : world segs -> config -> Prop) : Prop :=
forall ws ms' mat',
length ws = sh_j st' ->
img_env (extK E K ws) ->
match r with
| PTS_call s => st_ok segs (extK E K ws) (setpc (sh_ss st') (sigma s)) (restrict (w_H W) ms')
| _ => st_ok_pi (extK E K ws) (sh_ss st') (restrict (w_H W) ms')
end ->
sh_ok segs Bx SH (extK E K ws) (mrestrict (w_H W) (ms_mem ms')) ->
ajournal_gx STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms') (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
SRr segs W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q.
Lemma SRr_chain_pi_tok_AJX : forall W E K Bx SH ws ss (st' : shst) (r : ptrun_status psym) ms msr' STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q,
msteps segs (restrict (w_H W) ms) msr' ->
length ws = sh_j st' ->
img_env (extK E K ws) ->
match r with
| PTS_call s => st_ok segs (extK E K ws) (setpc (sh_ss st') (sigma s)) msr'
| _ => st_ok_pi (extK E K ws) (sh_ss st') msr'
end ->
sh_ok segs Bx SH (extK E K ws) (ms_mem msr') ->
frame_of E (ss_mem ss) (ms_mem (restrict (w_H W) ms)) (ms_mem msr') ->
ajournal_gx STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms) mdc k ->
awr_ok_x E (ss_mem ss) G XO OUT STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
run_post_pi_tok_AJX W E K Bx SH ss st' r ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof.
intros W E K Bx SH ws ss st' r ms msr' STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q Hms Hlen HE' HS' Hsh' Hfr HJ Hwr Hk.
apply (SRr_msteps segs Hwx W ms msr' mdc Q Hms).
intros model' Hsame Hcl.
rewrite (same_but_materialized_wvb mdc model' Hsame).
pose proof (restrict_unrestrict_clean (w_H W) (ms_mem ms) msr' Hcl) as Hrr.
pose proof (mrestrict_unrestrict_mem (w_H W) (ms_mem ms) msr' Hcl) as Hmm.
pose proof (msteps_mem_grows segs _ _ Hms) as Hgr. cbn [ms_mem restrict] in Hgr.
apply (Hk ws (unrestrict (w_H W) (ms_mem ms) msr') (m_vm_materialized model') Hlen HE').
- rewrite Hrr. exact HS'.
- rewrite Hmm. exact Hsh'.
- eapply (ajournal_gx_exec segs B LAWS segs_low G XO OUT) with (Wr := in_wrange E (ss_mem ss)); [exact HG | exact HJ | | | | | exact Hwr].
+ rewrite Hmm. exact Hfr.
+ rewrite Hmm. exact Hgr.
+ intros x Hx. cbn [unrestrict ms_mem]. unfold munrestrict. rewrite Hx. reflexivity.
+ rewrite <- (same_but_materialized_wvb mdc model' Hsame). exact Hsame.
- cbn [unrestrict ms_mem]. apply frame_of_unrestrict. exact Hfr.
- rewrite Hmm. exact Hfr.
- rewrite Hmm. exact Hgr.
Qed.
Lemma SRr_run_pi_tok_AJX : forall W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q,
(A_LIM <= K)%nat -> img_env E ->
st_ok_pi E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_runN_pi_tok tpi0 tw0 K Bx Bspan SH n ss = (st', r) ->
ajournal_gx STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms) mdc k ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
awr_ok_x E (ss_mem ss) G XO OUT STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
run_post_pi_tok_AJX W E K Bx SH ss st' r ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof.
intros W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q HK HE HS Hsh Hchk Hrun HJ Hobl Hwr Hk.
rewrite <- Htpi, <- Htw in Hrun.
destruct (sym_run_pi_tok_sound psym segs fetch val sigma listing Hfetch Hcert HB A_LIM HLIM0 HLIM HLEN K Bx Bspan SH HK n E ss _ st' r
HE HS Hsh Hchk Hrun Hobl) as (ws & msr' & Hlen & Hms & HE' & HP & Hsh' & _ & Hfr).
eapply SRr_chain_pi_tok_AJX; [exact Hms | exact Hlen | exact HE' | | exact Hsh' | exact Hfr | exact HJ | exact Hwr | exact Hk].
destruct r; cbn [ptok_post] in HP; first [exact HP | destruct HP].
Qed.
Lemma SRr_run_to_pi_tok_AJX : forall W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q,
(A_LIM <= K)%nat -> img_env E ->
st_ok_pi E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_run_toN_pi_tok tpi0 tw0 K Bx Bspan SH n stop ss = (st', r) ->
ajournal_gx STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms) mdc k ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
awr_ok_x E (ss_mem ss) G XO OUT STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
run_post_pi_tok_AJX W E K Bx SH ss st' r ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof.
intros W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q HK HE HS Hsh Hchk Hrun HJ Hobl Hwr Hk.
rewrite <- Htpi, <- Htw in Hrun.
destruct (sym_run_to_pi_tok_sound psym segs fetch val sigma listing Hfetch Hcert HB A_LIM HLIM0 HLIM HLEN K Bx Bspan SH HK n stop E ss _ st' r
HE HS Hsh Hchk Hrun Hobl) as (ws & msr' & Hlen & Hms & HE' & HP & Hsh' & _ & Hfr).
eapply SRr_chain_pi_tok_AJX; [exact Hms | exact Hlen | exact HE' | | exact Hsh' | exact Hfr | exact HJ | exact Hwr | exact Hk].
destruct r; cbn [ptok_post] in HP; first [exact HP | destruct HP].
Qed.
End e.

End a.
