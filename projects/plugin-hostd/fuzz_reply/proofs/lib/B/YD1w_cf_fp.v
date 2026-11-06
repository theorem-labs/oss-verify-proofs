(* Made by a Theorem Labs lane (2026-10-29, a Theorem Labs lane's DRIVER_CF_B) as the image-B twin of lib/A/AD1w_cf_fp.v
   (commit 46f1762ad5a): the same text over lib/B's W_journal and lib/B's YCbqG (the copy A2's
   YD1w_cf moves to under a Theorem Labs lane's 21:41Z amendment); module paths changed, no image numeral. *)
(* Footprint weakening for the cf journal (Reusable/YCbqG.v ajournal_x): a journal over a footprint FP is a journal
   over any larger footprint FP'.  The bridge from W8's program contract to the cf driver interface needs it once:
   W8's post journals over fr_FP (the entry writes no output, so its footprint has no sink_token), and the driver
   interface (AD1w_cf.v fr_lib_post_drv) journals over sink_token :: fr_FP, the shape the donor driver's footprint
   lemmas are stated over (AD1r.v).  Every footprint use in ajournal_x is monotone in the right direction: the output
   step (aos_step_mono), the kept-byte clauses (premise ~ inFP FP, and fp_spares_mono), and the freed-block clause
   (conclusion inFP FP, inFP_mono). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_journal.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

Section fp. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.

(* ROUTE R: each lemma below is stated over ajournal_xR at any world relation R (the journal's fourth conjunct, which
   every proof passes through unchanged), NAMER with R implicit; the strict NAME is its twin at wle (ajournal_x is
   ajournal_xR at wle by conversion, YCbqG.v). The cf driver's bridge from W8's contract at R (YD1w_cf_br.v
   fr_post_bridgeR) takes the R twins. *)
Lemma ajournal_x_fp_weakenR {R : world segs -> world segs -> Prop} : forall STK sp0 FP FP' ly S Hp (W : world segs)
  mem md own ly' S' Hp' (W' : world segs) mem' md' k,
  incl FP FP' ->
  ajournal_xR segs B PST ARx R STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
  ajournal_xR segs B PST ARx R STK sp0 FP' ly S Hp W mem md own ly' S' Hp' W' mem' md' k.
Proof.
  intros STK sp0 FP FP' ly S Hp W mem md own ly' S' Hp' W' mem' md' k Hincl
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17).
  refine (conj H1 (conj H2 (conj H3 (conj H4 (conj _ (conj H6 (conj H7 (conj H8 (conj H9
    (conj _ (conj _ (conj _ (conj _ (conj H14 (conj H15 (conj H16 H17)))))))))))))))).
  - exact (aos_step_mono FP FP' md md' (sink_open_mono FP FP' Hincl) H5).
  - intros p n i Hin Hin' Hi Hn. apply (H10 p n i Hin Hin' Hi).
    intros Hf. exact (Hn (inFP_mono FP FP' (p + i) Hincl Hf)).
  - intros a Hi Ho He Hps Hs. exact (H11 a Hi Ho He Hps (fp_spares_mono FP FP' a Hincl Hs)).
  - intros cid pos a Hf Hr Hn. apply (H12 cid pos a Hf Hr).
    intros Hfp. exact (Hn (inFP_mono FP FP' a Hincl Hfp)).
  - intros p n i Hin Hn Hi. exact (inFP_mono FP FP' (p + i) Hincl (H13 p n i Hin Hn Hi)).
Qed.
Lemma ajournal_x_fp_weaken : forall STK sp0 FP FP' ly S Hp (W : world segs) mem md own ly' S' Hp'
  (W' : world segs) mem' md' k,
  incl FP FP' ->
  ajournal_x segs B PST ARx STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
  ajournal_x segs B PST ARx STK sp0 FP' ly S Hp W mem md own ly' S' Hp' W' mem' md' k.
Proof. exact (@ajournal_x_fp_weakenR (@wle segs)). Qed.

(* the one use: from the entry's footprint to the driver's, sink_token in front *)
Corollary ajournal_x_add_sinkR {R : world segs -> world segs -> Prop} : forall STK sp0 FP ly S Hp (W : world segs)
  mem md own ly' S' Hp' (W' : world segs) mem' md' k,
  ajournal_xR segs B PST ARx R STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
  ajournal_xR segs B PST ARx R STK sp0 (sink_token :: FP) ly S Hp W mem md own ly' S' Hp' W' mem' md' k.
Proof.
  intros STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k H.
  exact (ajournal_x_fp_weakenR STK sp0 FP (sink_token :: FP) ly S Hp W mem md own ly' S' Hp' W' mem' md' k
    (incl_tl sink_token (incl_refl FP)) H).
Qed.
Corollary ajournal_x_add_sink : forall STK sp0 FP ly S Hp (W : world segs) mem md own ly' S' Hp'
  (W' : world segs) mem' md' k,
  ajournal_x segs B PST ARx STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
  ajournal_x segs B PST ARx STK sp0 (sink_token :: FP) ly S Hp W mem md own ly' S' Hp' W' mem' md' k.
Proof. exact (@ajournal_x_add_sinkR (@wle segs)). Qed.

(* PST weakening: a journal whose image clause exempts PST is one that exempts any larger PST'.  The bridge uses it
   once, from the walk header's PST := [] (globals in the G overlay; W8's cut) to the driver header's PST := G_fr_c B
   (YD1w_cf.v fr_lib_post_drv, preset's PresetCfnA.v:582 form). *)
Lemma ajournal_x_pst_weakenR {R : world segs -> world segs -> Prop} : forall (PST' : list (Z * Z)) STK sp0 FP ly S Hp
  (W : world segs) mem md own ly' S' Hp' (W' : world segs) mem' md' k,
  incl PST PST' ->
  ajournal_xR segs B PST ARx R STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
  ajournal_xR segs B PST' ARx R STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k.
Proof.
  intros PST' STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k Hincl
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17).
  refine (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9
    (conj H10 (conj _ (conj H12 (conj H13 (conj H14 (conj H15 (conj H16 H17)))))))))))))))).
  intros a Hi Ho He Hnp Hs. apply (H11 a Hi Ho He); [| exact Hs].
  intros Hx. apply Hnp. rewrite Exists_exists in Hx |- *. destruct Hx as (r & Hr & Hz).
  exists r. split; [exact (Hincl r Hr) | exact Hz].
Qed.
Lemma ajournal_x_pst_weaken : forall (PST' : list (Z * Z)) STK sp0 FP ly S Hp (W : world segs) mem md own ly' S'
  Hp' (W' : world segs) mem' md' k,
  incl PST PST' ->
  ajournal_x segs B PST ARx STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
  ajournal_x segs B PST' ARx STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k.
Proof. exact (@ajournal_x_pst_weakenR (@wle segs)). Qed.

(* The G-overlay step.  W8's program contract journals from a G-OVERLAID start memory memS (W_journal_x.v
   ajournal_g_x: `exists memS, ajournal_x .. W memS .. /\ gagree G (w_H W) mem memS`, memS agreeing with mem outside
   the program globals G); the driver header journals from the real start memory mem with the globals exempt as
   PST'.  The two meet when every byte a kept clause names is either off G (so memS and mem agree there) or, for the
   image clause, inside PST'.  Goff are the five places the clauses read the start memory; at the instance
   (G := G_fr_c B, PST' := G_fr_c B) each is a placement fact: the globals are image bytes below alloc_ceiling, in no
   heap block, frame, shadow or extra range. *)
Lemma ajournal_x_degagR {R : world segs -> world segs -> Prop} : forall (G PST' : list (Z * Z)) memS STK sp0 FP ly S
  Hp (W : world segs) mem md own ly' S' Hp' (W' : world segs) mem' md' k,
  let Goff a := inGb G (bv_unsigned (Z_to_bv 64 a)) = false in
  incl PST PST' ->
  (forall a, in_img segs a -> ~ Exists (in_zr a) PST' -> Goff a) ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> Goff a) ->
  (forall p n i, In (p, n) (ablocks B ly S) -> 0 <= i < req_size n -> Goff (p + i)) ->
  (forall cid pos a, In (cid, pos) (frames S) ->
     (in_zr a (frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) ->
     Goff a) ->
  (forall a, Exists (in_zr a) (ly_extra ly) -> ~ (as_errno B <= a < as_errno B + 4) -> Goff a) ->
  gagree G (w_H W) mem memS ->
  ajournal_xR segs B PST ARx R STK sp0 FP ly S Hp W memS md own ly' S' Hp' W' mem' md' k ->
  ajournal_xR segs B PST' ARx R STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k.
Proof.
  intros G PST' memS STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k Goff Hincl HGP HGC HGB HGF HGE Hag
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17).
  assert (AG : forall a, Goff a -> aview segs (w_H W) memS a = aview segs (w_H W) mem a)
    by (intros a Hg; exact (aview_gagree segs G (w_H W) mem memS a Hag Hg)).
  refine (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8
    (conj _ (conj _ (conj _ (conj _ (conj H13 (conj H14 (conj H15 (conj _ H17)))))))))))))))).
  - intros a Ha Hw. rewrite <- (AG a (HGC a Ha)). exact (H9 a Ha Hw).
  - intros p n i Hin Hin' Hi Hn. rewrite <- (AG (p + i) (HGB p n i Hin Hi)). exact (H10 p n i Hin Hin' Hi Hn).
  - intros a Hi Ho He Hnp Hs. rewrite <- (AG a (HGP a Hi Hnp)). apply (H11 a Hi Ho He); [| exact Hs].
    intros Hx. apply Hnp. rewrite Exists_exists in Hx |- *. destruct Hx as (r & Hr & Hz).
    exists r. split; [exact (Hincl r Hr) | exact Hz].
  - intros cid pos a Hf Hr Hn. rewrite <- (AG a (HGF cid pos a Hf Hr)). exact (H12 cid pos a Hf Hr Hn).
  - intros a Hx He. rewrite <- (AG a (HGE a Hx He)). exact (H16 a Hx He).
Qed.
Lemma ajournal_x_degag : forall (G PST' : list (Z * Z)) memS STK sp0 FP ly S Hp (W : world segs) mem md own
  ly' S' Hp' (W' : world segs) mem' md' k,
  let Goff a := inGb G (bv_unsigned (Z_to_bv 64 a)) = false in
  incl PST PST' ->
  (forall a, in_img segs a -> ~ Exists (in_zr a) PST' -> Goff a) ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> Goff a) ->
  (forall p n i, In (p, n) (ablocks B ly S) -> 0 <= i < req_size n -> Goff (p + i)) ->
  (forall cid pos a, In (cid, pos) (frames S) ->
     (in_zr a (frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) ->
     Goff a) ->
  (forall a, Exists (in_zr a) (ly_extra ly) -> ~ (as_errno B <= a < as_errno B + 4) -> Goff a) ->
  gagree G (w_H W) mem memS ->
  ajournal_x segs B PST ARx STK sp0 FP ly S Hp W memS md own ly' S' Hp' W' mem' md' k ->
  ajournal_x segs B PST' ARx STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k.
Proof. exact (@ajournal_x_degagR (@wle segs)). Qed.
End fp.
