(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr Frame TacX Bytes StoreDj.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ref Require Import XE_kit.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import BSegs AsShadow AsConst AsImgSh AsIface AsCXXHeap AsWalk AsStack0.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import AXRep AXRep2 AXPRep AXPRep2 AXRep_leafP N8Kit N8Kit2 N8Kit3 X8Kit X8LeafKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section PSIDE2.
  Context {HCEIL : HeapCeil}.

  Definition pside2 (m : mem) (lo shi : Z) (ACC SHV : list (Z * Z)) : Prop :=
    aside m lo shi ACC SHV /\ AXStatics2 m.

  Lemma pside2_intro : forall m lo shi ACC SHV,
    ACONST m -> stack0 m lo shi -> AXStatics2 m ->
    Forall (fun o : Z * Z => accessible m (fst o) (snd o)) ACC ->
    Forall (fun o : Z * Z => 0 <= fst o /\ 0 <= snd o /\ fst o + snd o <= AAPP_HI /\ shvis m (fst o) (fst o + snd o)) SHV ->
    pside2 m lo shi ACC SHV.
  Proof. intros m lo shi ACC SHV AC SK XS FA FS. split; [| exact XS]. split; [exact AC|]. split; [exact SK|]. split; [exact FA| exact FS]. Qed.

  Lemma pside2_transport : forall W m m' lo shi ACC SHV,
    pside2 m lo shi ACC SHV -> munch W m m' -> wmono bsegs m m' -> Forall pwin W -> pside2 m' lo shi ACC SHV.
  Proof.
    intros W m m' lo shi ACC SHV (AS & XS) MU WM FW. split.
    - eapply aside_transport; [exact AS| exact MU| exact WM|]. eapply Forall_impl; [| exact FW]. intros iv (K & _). exact K.
    - eapply AXStatics2_transport; [exact XS| exact MU| exact WM|]. eapply Forall_impl; [| exact FW]. intros iv (_ & K). exact K.
  Qed.

  (* [comment removed for export] *)
  Lemma pside2_aconst : forall m lo shi ACC SHV, pside2 m lo shi ACC SHV -> ACONST m.
  Proof. intros m lo shi ACC SHV ((K & _) & _). exact K. Qed.
  Lemma pside2_stack0 : forall m lo shi ACC SHV, pside2 m lo shi ACC SHV -> stack0 m lo shi.
  Proof. intros m lo shi ACC SHV ((_ & K & _) & _). exact K. Qed.
  Lemma pside2_statics2 : forall m lo shi ACC SHV, pside2 m lo shi ACC SHV -> AXStatics2 m.
  Proof. intros m lo shi ACC SHV (_ & K). exact K. Qed.
  Lemma pside2_statics : forall m lo shi ACC SHV, pside2 m lo shi ACC SHV -> AXStatics m.
  Proof. intros m lo shi ACC SHV (_ & K). exact (AXStatics2_AXStatics _ K). Qed.
  Lemma pside2_acc : forall m lo shi ACC SHV o n, pside2 m lo shi ACC SHV -> In (o, n) ACC -> accessible m o n.
  Proof. intros m lo shi ACC SHV o n ((_ & _ & K & _) & _) IN. exact (proj1 (Forall_forall _ _) K _ IN). Qed.
  Lemma pside2_shvis : forall m lo shi ACC SHV o n, pside2 m lo shi ACC SHV -> In (o, n) SHV -> shvis m o (o + n).
  Proof. intros m lo shi ACC SHV o n ((_ & _ & _ & K) & _) IN. exact (proj2 (proj2 (proj2 (proj1 (Forall_forall _ _) K _ IN)))). Qed.
  (* [comment removed for export] *)
  Lemma pside2_pside : forall m lo shi ACC SHV, pside2 m lo shi ACC SHV -> pside m lo shi ACC SHV.
  Proof. intros m lo shi ACC SHV (K & XS). split; [exact K| exact (AXStatics2_AXStatics _ XS)]. Qed.

  (* [comment removed for export] *)
  Lemma shv_entry : forall m A n, aapp A n -> 0 <= n -> shvis m A (A + n) ->
    0 <= A /\ 0 <= n /\ A + n <= AAPP_HI /\ shvis m A (A + n).
  Proof.
    intros m A n AP Hn SV. pose proof (aapp_bounds A n AP Hn) as (B1 & B2 & B3 & B4 & B5). unfold AAPP_HI in *.
    split; [lia|]. split; [lia|]. split; [lia| exact SV].
  Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

  Lemma parser_vt_accessible : forall m, ACONST m -> accessible m AVP_PARSER 96.
  Proof. intros m AC. apply (ACONST_img_accessible m AVP_PARSER 96 AC). vm_compute. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma parser_vt_read0 : forall m k, ACONST m -> 0 <= k < 96 ->
    ov_read_bytes bsegs m (Z_to_bv 64 (Z.shiftr (AVP_PARSER + k) 3 + 2147450880)) 1 = Some [b8 0].
  Proof.
    intros m k AC Hk.
    apply (accessible_read0_in m AVP_PARSER 96 (AVP_PARSER + k) (parser_vt_accessible m AC)); [reflexivity | reflexivity | lia].
  Qed.
End PSIDE2.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac ps_in := cbn [In]; repeat first [ left; reflexivity | right ].

(* [comment removed for export] *)
Ltac sh0_lit :=
  try replace (zxb (b8 0)) with (Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity);
  try replace (sxb (b8 0)) with (Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).

(* [comment removed for export] *)
Ltac ps_now SD MU WM FW SDc :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    pose proof (pside2_transport _ _ mc _ _ _ _ SD MU WM FW) as SDc
  end.

(* [comment removed for export] *)
Ltac ps_chk8 SD MU WM FW O n g AL PRE :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    let SDc := fresh "SDc" in let RD := fresh "RD" in
    pose proof (pside2_transport _ _ mc _ _ _ _ SD MU WM FW) as SDc;
    pose proof (accessible_read0_sr mc O n g (pside2_acc _ _ _ _ _ O n SDc ltac:(ps_in)) ltac:(clear; lia)
                  ltac:(clear - AL; unfold hideL in AL; Z.div_mod_to_equations; lia) ltac:(clear; lia)) as RD;
    rewrite ?Z.add_0_r in RD; clear SDc;
    PRE; clear RD; sh0_lit;
    shchk_br
  end.

(* [comment removed for export] *)
Ltac ps_chkin SD MU WM FW O n x AL PRE :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    let SDc := fresh "SDc" in let RD := fresh "RD" in
    pose proof (pside2_transport _ _ mc _ _ _ _ SD MU WM FW) as SDc;
    pose proof (accessible_read0_in mc O n x (pside2_acc _ _ _ _ _ O n SDc ltac:(ps_in)) AL ltac:(reflexivity)
                  ltac:(clear; lia)) as RD;
    rewrite ?Z.add_0_r in RD; clear SDc;
    PRE; clear RD; sh0_lit;
    shchk_br
  end.

(* [comment removed for export] *)
Ltac ps_chkst SD MU WM FW lo shi g w tac PRE :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    let SDc := fresh "SDc" in let RD := fresh "RD" in let B1 := fresh "B1" in let B2 := fresh "B2" in
    pose proof (pside2_transport _ _ mc _ _ _ _ SD MU WM FW) as SDc;
    assert (B1 : lo <= g) by tac; assert (B2 : g + w <= shi) by tac;
    pose proof (stack0_read0_sr mc lo shi g w (pside2_stack0 _ lo shi _ _ SDc) B1 ltac:(clear; lia) B2) as RD;
    rewrite ?Z.add_0_r in RD; clear SDc B1 B2;
    PRE; clear RD; sh0_lit;
    shchk_br
  end.

(* [comment removed for export] *)
Ltac ps_chkvt SD MU WM FW k PRE :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    let SDc := fresh "SDc" in let RD := fresh "RD" in
    pose proof (pside2_transport _ _ mc _ _ _ _ SD MU WM FW) as SDc;
    pose proof (parser_vt_read0 mc k (pside2_aconst _ _ _ _ _ SDc) ltac:(clear; lia)) as RD;
    unfold AVP_PARSER in RD; cbn [Z.add Pos.add Pos.succ Pos.add_carry] in RD; clear SDc;
    PRE; clear RD; sh0_lit;
    shchk_br
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac go1 := first [ step | if_false | if_true ].

(* [comment removed for export] *)
Ltac steps_to pc :=
  do 40 (lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => idtac
         | |- evt _ _ _ => go1
         end).
