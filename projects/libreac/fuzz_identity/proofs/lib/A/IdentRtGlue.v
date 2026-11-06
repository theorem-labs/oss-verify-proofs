(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from part of proofs/libreac/fuzz_grant/lib/A/Prog/GrantClose.v (grant_PALib,
   grant_api_env, grant_FFL; a working branch bcad42da99f) for libreac/fuzz_identity's ASan build (image A): the facts
   are stated at the applied core's record IdentB (lib/A/AD2l.v) and the listing's instance PI_ident (A/Prog/IdentImg.v);
   module paths changed. *)
(* The runtime glue of fuzz_identity's ASan closer (lib/A/IdentTop.v:211, :220): TL and FFL, the link's Section
   hypotheses (A/Prog/IdentEntryLink.v:233, :242), each at its exact type, proved from the applied core's lemmas:
     TL   PALib IdentB                          IdentPaLib.v:307; api_env from TfibB_syms's ts_universe_drv (A/AF0m.v)
     FFL  frame_flag_lawP (SEGSr rc) IdentB     YCbq.v:799; from AR_laws_ok (YG0q.v:804) and ident_img_cover
                                                (A/Prog/IdentImg.v:59) *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A Require Import AF0l AF0m AD2l.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YP09 YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG0q YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05.
From OSSVerify.libreac.fuzz_identity.images Require Import Asan.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaTable PaSym IdentSyms IdentList IdentAddr IdentPa IdentImg IdentPaLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Local Notation SEGSr rc := (@pa_segs _ ident_listing (@PI_ident rc)).

(* ---- TL (IdentEntryLink.v:233 Hypothesis TL; IdentTop.v:211) --------------------------------------------- *)
Lemma ident_api_env : forall (fx : YK11.FPState) (rc : YM05.RunCeil), api_env (SEGSr rc) IdentB.
Proof.
intros fx rc. split; [|split].
- cbn [as_errno IdentB]. unfold TFIB_ERRNO, kLowMemEnd. lia.
- intros a Ha. cbn [as_errno IdentB] in Ha. unfold TFIB_ERRNO in Ha. unfold in_img.
  (* the errno word lies in the fourth LOAD segment, [0x9e0a8, 0x5f9830) *)
  exists Asan.Asan_segment_003. split.
  + change (SEGSr rc) with ident_segs. unfold ident_segs, Asan.M.loaded_segments. do 3 right; left; reflexivity.
  + match goal with |- ?lo <= a < ?lo + ?sz =>
      let l := eval vm_compute in lo in let h := eval vm_compute in sz in change sz with h; change lo with l end.
    lia.
- split; apply (ts_universe_drv IdentB TfibB_syms);
    cbn [as_code IdentB Tfib_code pc_malloc_ra0 pc_free_ra0 DRV_TRACES In];
    repeat (first [left; reflexivity | right]).
Qed.

Lemma ident_TL : forall (fx : YK11.FPState) (rc : YM05.RunCeil), PALib IdentB.
Proof.
intros fx rc. constructor.
- reflexivity.
- reflexivity.
- vm_compute. first [left; intro H; discriminate H | right; intro H; discriminate H].
- exact (ident_api_env fx rc).
- reflexivity.
- reflexivity.
- cbn [as_code IdentB Tfib_code pc_free_ra0 pc_malloc_ra0]. split; vm_compute; reflexivity.
Qed.

(* ---- FFL (IdentEntryLink.v:242 Hypothesis FFL; IdentTop.v:220) ------------------------------------------- *)
Lemma ident_FFL : forall (fx : YK11.FPState) (rc : YM05.RunCeil), frame_flag_lawP (SEGSr rc) IdentB.
Proof.
intros fx rc. pose proof (AR_laws_ok (SEGSr rc) IdentB) as LAWS.
intros ly S W mem md cid pos HAR Hin.
destruct (al_flag _ _ LAWS ly S W mem md cid pos HAR Hin) as (Hp & Ho & Happ & Hceil).
destruct (al_client_img _ _ LAWS ly S W mem md (flag_addr ly cid pos) HAR) as [Hhull Himg].
{ right. right. exists cid, pos. split; [exact Hin | reflexivity]. }
pose proof HAR as (M & L & _). pose proof (ident_img_cover ly S md L) as [C1 C2].
destruct Happ as [H4096 Hz]. unfold in_zr in Hhull.
split; [exact Hp|]. split; [exact Ho|]. split.
- split; [|exact Himg]. unfold app_addr, in_app, ASAN_CEIL in *. lia.
- split; [exact H4096|]. split; [|exact Hceil]. unfold zone2, off_img, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.
