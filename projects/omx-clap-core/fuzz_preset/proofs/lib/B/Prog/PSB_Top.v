(* fuzz_preset lib/B, parse_string on image B' (asan-ubsan sha256 d663f82d7f48): THE WALK, composed from its stretches.
   THE TEXT (a working branch): the KIT TEXT tparse_string_specX of the announced the kit cut
   7cdbb61b5fa0 (owner 06:11Z; PRH_FnReader.v blob f1ae32e3b2cd :517-681) itself: POST-IMPLICATION, the cursor set CW (prh_cw_ok, the wild room
   at entry), the post m-form and BUDGETED (fpostWbm .. (wbudget CW 0) ..). The change from the earlier
   statement DRAFT_tparse_string_specX (PS_Draft.v, deleted) was a RESTATEMENT, NOT a conversion: the kit's refused arm adds the
   outcome-exclusion conjunct (:622-629) and counts ((cnt + 1) mod 2 ^ 64) (:633-635); the walk proves both
   (PS_Gen.ps_excl_of_malloc from fuzz_malloc's outcome clause; the mod is prh_alloc_post arm 2's). On the #102 pins
   (asan-ubsan d663f82d, image B'); at image B's instances (prh_img_B, B_prog_listing, PI_prog_B), for every run's
   contexts CTX and cursor set CW, under the journal laws LAWS (at hl := cf_head), the listing's library facts TL
   (PALib over PI_prog_B), the statics' placement PST_ok, the image facts ZSA / IMGV (PSB_Src.v; IMGV at image B's own
   bounds), the kit's prh_head_wide HW, the four callees' kit texts (tfuzz_malloc_specX / tfuzz_free_specX, thex4_specX /
   tput_utf8_specX). The cursor free's admission needs the depot's NoDup: AR_laws_x FIELD 25 alx_depot_nodup
   (a Theorem Labs lane, a working branch b4ca247aad5d: YCbqG.v 219748197d6b, YCbqGwild.v 0c63874858e4, YGcallcf.v
   8645fa6a514f, taken by path), read off LAWS; the former named premise DEPOT is GONE. NO per-record premise: the
   post-implication form needs no agreement.
   GENERIC P (a Theorem Labs lane 12:18Z / 12:22Z): every stretch is proved over an abstract memory invariant P
   (srr_inv_laws, srr_inv_call where it calls); psb_holds_of_segsP instantiates P once per record as ps_mn D (the
   memnorm keep of the m-form post).
   Composition: entry <- scan, ret0; scan <- ret0, dec; dec (its own measure) <- u, free, retok; u <- free;
   free <- ret0. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YI16 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG YGcfNames YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x YSRrMemnorm.
(* the re-hiding move's wle' and its laws (YA0nH) at preset's zone YGcfRehidePost.RZ_cf *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnAlloc PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PS_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import
PSB_Base PSB_Src PSB_Entry PSB_Scan PSB_Dec PSB_U PSB_Tail.
(* the PLAIN build's sink instance is loaded transitively; it must never fill an ASan sink argument *)
#[global] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Open Scope Z_scope.

Section top. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
(* image B's instances (PSB_Base.v's), the ones every statement below names *)
#[local] Existing Instances PSB_PrhImg PSB_PAListing PSB_PAImg.
#[local] Notation segs := (@pa_segs _ B_prog_listing PSB_PAImg).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Hypothesis LAWS : AR_laws_x segs B ARx cf_head.
Hypothesis TL : PALib (L := B_prog_listing) (PI := PI_prog_B) B.
Hypothesis PST_ok : forall a, Exists (in_zr a) prh_pst -> in_img segs a /\ ~ Exists (in_zr a) (as_owned_static B).
Hypothesis ZSA : forall q m, In (q, m) (as_zero_shadow B) -> q mod 8 = 0 /\ m mod 8 = 0.
Hypothesis IMGV : psb_img_shadow_vis ARx.
Hypothesis HW : prh_head_wide.
Hypothesis HMALLOC : tfuzz_malloc_specX B ARx SK.
Hypothesis HFREE : tfuzz_free_specX B ARx SK.
Hypothesis HHEX4 : thex4_specX B ARx SK.
Hypothesis HPUTU : tput_utf8_specX B ARx SK.

(* the walk at any invariant P: the entry stretch *)
Lemma psb_entryP_of_stretches : forall CTX CW (P : (word -> option byte) -> Prop),
  srr_inv_laws segs P -> srr_inv_call segs P -> psb_seg_entryP B ARx SK CTX CW P.
Proof.
intros CTX CW P PLAW PCALL.
assert (R0 : psb_seg_ret0P B ARx SK CTX CW P) by (eapply psb_ret0_holdsP; eassumption).
assert (RK : psb_seg_retokP B ARx SK CTX CW P) by (eapply psb_retok_holdsP; eassumption).
(* the NULL return after the bad escape's fuzz_free: the ret0 stretch over the relation wle' segs RZ_cf *)
assert (R0R : psb_seg_ret0PR B ARx SK CTX CW P (wle' segs YGcfRehidePost.RZ_cf))
  by (eapply psb_ret0_holdsPR;
      first [ eassumption | exact (wle'_refl segs YGcfRehidePost.RZ_cf) | exact (wle'_trans segs YGcfRehidePost.RZ_cf)
            | exact (wle_wle' segs YGcfRehidePost.RZ_cf) ]).
assert (FR : psb_seg_freeP B ARx SK CTX CW P) by (eapply psb_free_holdsP; eassumption).
assert (UU : psb_seg_uP B ARx SK CTX CW P) by (eapply psb_u_holdsP; eassumption).
assert (ST : psb_dec_stepP B ARx SK CTX CW P) by (eapply psb_dec_step_holdsP; eassumption).
assert (DE : psb_seg_decP B ARx SK CTX CW P) by exact (psb_seg_dec_of_stepP B ARx SK CTX CW P ST).
assert (SC : psb_seg_scanP B ARx SK CTX CW P) by (eapply psb_scan_holdsP; eassumption).
eapply psb_entry_holdsP; eassumption.
Qed.

(* THE FUNCTION PROOF: the KIT TEXT (the kit cut 7cdbb61b5fa0) at image B' *)
Theorem parse_string_holds_B : forall CTX CW,
  tparse_string_specX (PI := PSB_PrhImg) (L := B_prog_listing) (PA := PSB_PAImg) B ARx SK CTX CW.
Proof.
intros CTX CW. apply (psb_holds_of_segsP B ARx SK CTX CW).
intros P PLAW PCALL. exact (psb_entryP_of_stretches CTX CW P PLAW PCALL).
Qed.

End top.

(* the guard (CrcBp's trap, 2026-10-29 19:2xZ): the closure also loads PLAIN image files, where a short image name can
   resolve to the plain lib/Img0.v; the segments every statement above is over (pa_segs of PSB_Base's PSB_PAImg :=
   PI_prog_B) ARE image B's, by conversion, named fully qualified *)
Section g. Context {rc : YM05.RunCeil}.
Lemma psb_segs_B : @pa_segs _ B_prog_listing PI_prog_B =
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Img0.rsegs.
Proof. reflexivity. Qed.
End g.
Locate Img0.rsegs.
Locate B_prog_listing.
Locate PI_prog_B.
Locate prh_img_B.

(* the wrong-image check of the rebind brief (rule 7): every PA / L / PI argument names image B *)
Set Printing Implicit. Unset Printing Notations.
About parse_string_holds_B.
Unset Printing Implicit. Set Printing Notations.
Print Assumptions parse_string_holds_B.
