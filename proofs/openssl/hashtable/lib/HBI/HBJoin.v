(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.openssl.hashtable.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import PropExec ShapeAlg AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanInit.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CxRel CxPlan CxPlanSound CxGlue HBPlanImage HBAtable HBChain HBCheckG HBParity HBOpenDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.

Section Join.
  Variable SV : env -> (word -> option byte) -> Prop.
  Variable argH : env -> word -> bool.
  Variable ISP : Z.
  Variable fs : Fs.Fs.
  #[local] Notation CSOK S := (cs_ok HASEGS HAT AsanInit.LIMIT S argH ISP fs).

  Lemma csok_svg : forall (P : env -> Prop) E cs R FULL m, CSOK SV E cs R FULL m -> P E -> CSOK (SVG P SV) E cs R FULL m.
  Proof.
    intros P E cs R FULL m HC HP.
    apply (cs_ok_sinv HASEGS HAT AsanInit.LIMIT argH ISP fs SV (SVG P SV) E cs R FULL m); [|exact HC].
    intros HS. split; [exact HS | exact HP].
  Qed.

  Lemma piece_cover2 : forall (P1 P2 : env -> Prop) cs T,
    (forall E R FULL m, CSOK SV E cs R FULL m -> P1 E \/ P2 E) ->
    piece (SVG P1 SV) argH ISP fs cs T -> piece (SVG P2 SV) argH ISP fs cs T -> piece SV argH ISP fs cs T.
  Proof.
    intros P1 P2 cs T Hc H1 H2 E R FULL m HC. destruct (Hc E R FULL m HC) as [HP|HP].
    - exact (H1 E R FULL m (csok_svg P1 E cs R FULL m HC HP)).
    - exact (H2 E R FULL m (csok_svg P2 E cs R FULL m HC HP)).
  Qed.

  Lemma piece_cover3 : forall (P1 P2 P3 : env -> Prop) cs T,
    (forall E R FULL m, CSOK SV E cs R FULL m -> P1 E \/ P2 E \/ P3 E) ->
    piece (SVG P1 SV) argH ISP fs cs T -> piece (SVG P2 SV) argH ISP fs cs T -> piece (SVG P3 SV) argH ISP fs cs T -> piece SV argH ISP fs cs T.
  Proof.
    intros P1 P2 P3 cs T Hc H1 H2 H3 E R FULL m HC. destruct (Hc E R FULL m HC) as [HP|[HP|HP]].
    - exact (H1 E R FULL m (csok_svg P1 E cs R FULL m HC HP)).
    - exact (H2 E R FULL m (csok_svg P2 E cs R FULL m HC HP)).
    - exact (H3 E R FULL m (csok_svg P3 E cs R FULL m HC HP)).
  Qed.
  (* [comment removed for export] *)
  Lemma piece_svg_all : forall (P : env -> Prop) cs T,
    (forall E, P E) -> piece (SVG P SV) argH ISP fs cs T -> piece SV argH ISP fs cs T.
  Proof. intros P cs T HP H E R FULL m HC. exact (H E R FULL m (csok_svg P E cs R FULL m HC (HP E))). Qed.

  (* [comment removed for export] *)
  Lemma piece_even_only : forall cs T, knows_range (kn cs) 6%nat 6 6 = true ->
    piece SV argH ISP fs (with_facts cs [par_even]) T -> piece SV argH ISP fs cs T.
  Proof.
    intros cs T KR PE E R FULL m HC.
    pose proof (knows_range_sound _ _ _ _ 6%nat 6 6 KR (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC)) as H6.
    apply (PE E R FULL m). apply (csok_with_facts SV argH ISP fs); [exact HC|].
    intros M. constructor; [|constructor]. unfold par_even. cbn [kentry_ok]. split; [reflexivity|].
    replace (bv_unsigned (edenot E (EVar 6))) with 6 by lia. reflexivity.
  Qed.
End Join.
