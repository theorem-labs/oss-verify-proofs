(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AsAtomics AsDepotInv F_memset AllocWalkKit.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AW_Leaves AW_PoisonShadow AW_SysconfPg AllocTacX.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section HCW.
  Context {HCEIL : HeapCeil}.

Local Unset Keyed Unification.

(* [comment removed for export] *)
Record RENV (g : word) (b244 : byte) (m : mem) : Prop := mkRENV {
  re_got  : rw_cells asegs m 6191096 (map (fun v => C8 (wz v)) AGOT_VALS);                       (* [comment removed for export] *)
  re_shb  : rw_cells asegs m 6990072 [C8 (wz 2147450880)];                                      (* [comment removed for export] *)
  re_hme  : rw_cells asegs m 6993376 [C8 (wz 140737488355327); C8 (wz 0); C8 (wz 0)];           (* [comment removed for export] *)
  re_thresh : rw_cells asegs m 7586976 [C8 (wz 0xffffffffffffffff)];                                       (* [comment removed for export] *)
  re_mlim : rw_cells asegs m 7587000 [C8 (wz 0)];                                               (* [comment removed for export] *)
  re_dd   : rw_cells asegs m 7587075 [C1 (b8 1)];                                               (* [comment removed for export] *)
  re_madv : rw_cells asegs m 7587100 [C1 b244];                                                 (* [comment removed for export] *)
  re_rms  : rw_cells asegs m 6204016 [C8 (wz 5676560)];                                         (* [comment removed for export] *)
  re_psc  : rw_cells asegs m 7578528 [C8 (wz 4096)];                                            (* [comment removed for export] *)
  re_lpg  : rw_cells asegs m 12590928 [C8 (wz 4096)];                                            (* [comment removed for export] *)
  re_ssp  : rw_cells asegs m 6199192 [C8 (wz 12590288)];                                         (* [comment removed for export] *)
  re_grd  : rw_cells asegs m 12590288 [C8 g]                                                     (* [comment removed for export] *)
}.

End HCW.

Ltac open_renv E :=
  destruct E as [Rgot Rshb Rhme Rthresh Rmlim Rdd Rmadv Rrms Rpsc Rlpg Rssp Rgrd]; unfold AGOT_VALS in Rgot; cbn [map] in Rgot.

(* [comment removed for export] *)
Ltac split_frame FR sizes :=
  lazymatch type of FR with rw_cells _ _ _ [CB ?n ?j] =>
    let J := fresh "J" in remember j as J in FR;
    match goal with E : J = j |- _ => clear E end;
    apply (rw_cells_split_CB asegs _ _ [] n J [] sizes) in FR; [| reflexivity]; cbn [mk_CB_cells app] in FR;
    repeat match type of FR with context [CB _ (take ?k ?l)] => let K := fresh "jk" in remember (take k l) as K in FR end;
    repeat match type of FR with context [CB _ (drop ?k ?l)] => let K := fresh "jk" in remember (drop k l) as K in FR end;
    repeat match goal with H : _ = take _ _ |- _ => clear H | H : _ = drop _ _ |- _ => clear H end
  end.

Section HCW2.
  Context {HCEIL : HeapCeil}.

Lemma renv_transport : forall g b m m' W,
  RENV g b m -> munch W m m' -> wmono asegs m m' ->
  disjoint_from W 6191096 120 -> disjoint_from W 6990072 8 -> disjoint_from W 6993376 24 -> disjoint_from W 7586976 8 ->
  disjoint_from W 7587000 8 -> disjoint_from W 7587075 1 -> disjoint_from W 7587100 1 -> disjoint_from W 6204016 8 ->
  disjoint_from W 7578528 8 -> disjoint_from W 12590928 8 -> disjoint_from W 6199192 8 -> disjoint_from W 12590288 8 ->
  RENV g b m'.
Proof.
  intros g b m m' W E MU WM; intros; destruct E; constructor;
    (eapply rw_cells_transport; [eassumption | exact MU | exact WM | ]);
    unfold AGOT_VALS; cbn [cells_size csize length map Nat.add Nat.mul]; assumption.
Qed.

End HCW2.

Ltac renv_at E MU WM E' :=
  lazymatch type of MU with munch ?W ?m ?m' =>
    lazymatch type of E with RENV ?g ?b m =>
      region_table; region_hull_memo W;   (* [comment removed for export] *)
      assert (E' : RENV g b m');
      [ apply (renv_transport g b m m' W E MU WM); cbn [disjoint_from]; region_decide | ]
    end end.

(* [comment removed for export] *)
Section HCW3.
  Context {HCEIL : HeapCeil}.

Lemma asegs_below_top : forall seg, In seg asegs -> Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <= 12599296.
Proof.
  intros seg H. unfold asegs, RefMemImage.Ref.loaded_segments in H. cbn -[Z.of_N Z.add] in H.
  destruct H as [<-|[<-|[<-|[<-|[]]]]]; vm_compute; discriminate.
Qed.

(* [comment removed for export] *)
Definition prm_pb (addr : Z) : Z := round_up (sh addr) 4096.
Definition prm_pe (addr size : Z) : Z := round_down (sh addr + size / 8) 4096.

End HCW3.
