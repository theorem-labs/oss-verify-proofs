(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from part of proofs/libreac/fuzz_grant/lib/A/Prog/GrantClose.v (grant_PALib,
   grant_api_env, grant_ML, grant_SMP, grant_FFL; a working branch bcad42da99f) and of a Theorem Labs lane's AGrantT.v (Let HD)
   for libreac/fuzz_identity's ASan+UBSan build (image B): the facts are stated at the applied B core's record IdentB
   (lib/ReusableB/YD2l.v, cgif YD2l.v's TfibB renamed) and the listing's instance PI_identb (B/Prog/IdentBImg.v); the
   allocator rules AMALLOC4 and AFREE4 are added; module paths changed. *)
(* The runtime glue of fuzz_identity's ASan+UBSan closer (lib/B/IdentTopB.v): TL, ML, SMP, FFL, AMALLOC4 and AFREE4, the
   link's Section hypotheses, each at its exact type, and the closer's Let HD, proved from the applied B core's lemmas:
     TL        PALib IdentB                       IdentBPaLib.v:308; api_env from TfibB_syms's ts_universe_drv (YF0m.v)
     ML        model_laws (as_universe IdentB)    model_laws_ok (Reusable/YG05.v:139), ts_universe of TfibB_syms
     SMP       stack_malloc_progressP IdentB      stack_malloc_progress (Reusable/YG05.v:70)
     FFL       frame_flag_lawP (SEGSr rc) IdentB  AR_laws_ok (YG0q.v:804) and identb_img_cover (B/Prog/IdentBImg.v:60)
     AMALLOC4  amalloc04_rule .. ameter_triv      amalloc04_rule_triv (ReusableB/YCbp.v:30) of tfib_amalloc_realizes
                                                  (ReusableB/YF0w.v)
     AFREE4    afree04_rule .. ameter_triv        afree04_rule_triv (ReusableB/YCbp.v:39) of afree_realizes_closed
                                                  (ReusableB/YF0q.v:10)
     HD        as_dhash IdentB t = tfib_dhash t   eq_refl (YD2l.v: as_dhash := tfib_dhash), as fuzz_grant's AGrantT.v:37 *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.ReusableB Require Import YF0l YF0m YB1v YD2l YF0w YF0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YP09 YK04 YA0i YA0n YF0p.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG0q YG05 YCbq YI16 YC5d.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.ReusableB Require Import YCbp.
From OSSVerify.libreac.fuzz_identity.images Require Import AsanUbsan.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
IdentBSyms IdentBList IdentBAddr IdentBPa IdentBImg IdentBPaLib.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require IdentEntryLink.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Local Notation SEGSr rc := (@pa_segs _ identb_listing (@PI_identb rc)).
Local Notation SKB := IdentEntryLink.ident_asan_ubsan_sink_head.

(* ---- the image: every loaded byte lies below kLowMemEnd ---------------------------------------------------- *)
Lemma identb_segs_low : forall (rc : YM05.RunCeil) a, in_img (SEGSr rc) a -> 0 <= a < kLowMemEnd.
Proof.
intros rc a (sg & Hin & Ha). change (SEGSr rc) with identb_segs in Hin. unfold identb_segs, AsanUbsan.M.loaded_segments in Hin.
unfold kLowMemEnd.
repeat (destruct Hin as [<- | Hin];
  [match type of Ha with ?lo <= a < ?lo + ?sz =>
     let l := eval vm_compute in lo in let h := eval vm_compute in sz in change sz with h in Ha; change lo with l in Ha end;
   lia |]).
contradiction.
Qed.

(* ---- TL (IdentEntryLink.v:234 Hypothesis TL; IdentTopB.v:216) -------------------------------------------- *)
Lemma identb_api_env : forall (fx : YK11.FPState) (rc : YM05.RunCeil), api_env (SEGSr rc) IdentB.
Proof.
intros fx rc. split; [|split].
- cbn [as_errno IdentB]. unfold TFIB_ERRNO, kLowMemEnd. lia.
- intros a Ha. cbn [as_errno IdentB] in Ha. unfold TFIB_ERRNO in Ha. unfold in_img.
  (* the errno word lies in the fourth LOAD segment, [0x9e388, 0x5f9b30) *)
  exists AsanUbsan.AsanUbsan_segment_003. split.
  + change (SEGSr rc) with identb_segs. unfold identb_segs, AsanUbsan.M.loaded_segments. do 3 right; left; reflexivity.
  + match goal with |- ?lo <= a < ?lo + ?sz =>
      let l := eval vm_compute in lo in let h := eval vm_compute in sz in change sz with h; change lo with l end.
    lia.
- split; apply (ts_universe_drv IdentB TfibB_syms);
    cbn [as_code IdentB Tfib_code pc_malloc_ra0 pc_free_ra0 DRV_TRACES In];
    repeat (first [left; reflexivity | right]).
Qed.

Lemma identb_TL : forall (fx : YK11.FPState) (rc : YM05.RunCeil), PALib IdentB.
Proof.
intros fx rc. constructor.
- reflexivity.
- reflexivity.
- vm_compute. first [left; intro H; discriminate H | right; intro H; discriminate H].
- exact (identb_api_env fx rc).
- reflexivity.
- reflexivity.
- cbn [as_code IdentB Tfib_code pc_free_ra0 pc_malloc_ra0]. split; vm_compute; reflexivity.
Qed.

(* ---- ML, SMP (IdentEntryLink.v:237, :240 Hypotheses ML, SMP; IdentTopB.v:219, :222) ---------------------- *)
Lemma identb_ML : forall (fx : YK11.FPState) (rc : YM05.RunCeil), model_laws (as_universe IdentB).
Proof. intros fx rc. exact (model_laws_ok (as_universe IdentB) (ts_universe IdentB TfibB_syms)). Qed.

Lemma identb_SMP : forall (fx : YK11.FPState) (rc : YM05.RunCeil), stack_malloc_progressP IdentB.
Proof. intros fx rc s cid W Hc Hn. exact (stack_malloc_progress (as_universe IdentB) s cid W Hc Hn). Qed.

(* ---- FFL (IdentEntryLink.v:242 Hypothesis FFL; IdentTopB.v:224) ------------------------------------------ *)
Lemma identb_FFL : forall (fx : YK11.FPState) (rc : YM05.RunCeil), frame_flag_lawP (SEGSr rc) IdentB.
Proof.
intros fx rc. pose proof (AR_laws_ok (SEGSr rc) IdentB) as LAWS.
intros ly S W mem md cid pos HAR Hin.
destruct (al_flag _ _ LAWS ly S W mem md cid pos HAR Hin) as (Hp & Ho & Happ & Hceil).
destruct (al_client_img _ _ LAWS ly S W mem md (flag_addr ly cid pos) HAR) as [Hhull Himg].
{ right. right. exists cid, pos. split; [exact Hin | reflexivity]. }
pose proof HAR as (M & L & _). pose proof (identb_img_cover ly S md L) as [C1 C2].
destruct Happ as [H4096 Hz]. unfold in_zr in Hhull.
split; [exact Hp|]. split; [exact Ho|]. split.
- split; [|exact Himg]. unfold app_addr, in_app, ASAN_CEIL in *. lia.
- split; [exact H4096|]. split; [|exact Hceil]. unfold zone2, off_img, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.

(* ---- HD (IdentTopB.v:252 Let HD) ------------------------------------------------------------------------- *)
Lemma identb_HD : forall t, as_dhash IdentB t = tfib_dhash t.
Proof. intros t. reflexivity. Qed.

(* ---- AMALLOC4, AFREE4 (IdentEntryLink.v:243, :704 Hypotheses AMALLOC4, AFREE4; IdentTopB.v:225, :238) ---- *)
(* The meter is the entry link's ameter_triv (IdentEntryLink.v:80), the one IdentTopB.v names; YCbp.v:17's twin has the
   same body, so the core lemmas below close the goal by conversion. *)
Lemma identb_AMALLOC4 : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @amalloc04_rule fx rc SKB (SEGSr rc) IdentB IdentEntryLink.ameter_triv.
Proof.
intros fx rc.
exact (@amalloc04_rule_triv fx rc SKB (SEGSr rc) IdentB (identb_segs_low rc) (identb_api_env fx rc)
  (AR_laws_ok (SEGSr rc) IdentB) (identb_ML fx rc) (tfib_amalloc_realizes IdentB TfibB_syms identb_HD)).
Qed.

Lemma identb_AFREE4 : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @afree04_rule fx rc SKB (SEGSr rc) IdentB IdentEntryLink.ameter_triv.
Proof.
intros fx rc.
exact (@afree04_rule_triv fx rc SKB (SEGSr rc) IdentB (identb_segs_low rc) (identb_api_env fx rc)
  (AR_laws_ok (SEGSr rc) IdentB) (identb_ML fx rc) (afree_realizes_closed IdentB TfibB_syms identb_HD)).
Qed.
