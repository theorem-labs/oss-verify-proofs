(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac InitMem ITree Nodes Decode.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import ExecF ITreeA Shadow.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg RtCells AProto ABase ABytes AMalloc_iface ADepot_iface ARep ALayout AHeapP ARepExt FsKit AFake_iface. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_tlsga. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_tlsga.F_tlsga. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import F_m2s_b. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AFake_sm0. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_sm0.AFake_sm0. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AFake_sm0. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_sm0.AFake_sm2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import StepF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AFake_arep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_arep.AFake_arep.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition fk_is (c F : Z) (b : ablock) : bool :=
  match ab_kind b with ABFake c' => (c' =? c) && (ab_addr b =? F) | ABHeap _ => false end.
Definition fk_rel (c F : Z) (LB : list ablock) : list ablock := List.filter (fun b => negb (fk_is c F b)) LB.

Lemma fk_rel_In : forall c F LB b, In b (fk_rel c F LB) <-> In b LB /\ fk_is c F b = false.
Proof. intros. unfold fk_rel. rewrite filter_In, negb_true_iff. tauto. Qed.
Lemma fk_rel_heap : forall c F LB p A n, In (HB p A n) LB -> In (HB p A n) (fk_rel c F LB).
Proof. intros. apply fk_rel_In. split; [assumption| reflexivity]. Qed.
Lemma fk_rel_not_In : forall c F n LB, ~ In (FKB c F n) (fk_rel c F LB).
Proof. intros c F n LB H. apply fk_rel_In in H. destruct H as [_ H]. unfold fk_is in H. cbn in H. rewrite !Z.eqb_refl in H. discriminate. Qed.
Lemma fk_rel_hb_ids : forall c F LB, hb_ids (fk_rel c F LB) = hb_ids LB.
Proof.
  intros c F LB. unfold fk_rel. induction LB as [|b l IH]; [reflexivity|].
  change (List.filter (fun b0 => negb (fk_is c F b0)) (b :: l)) with (if negb (fk_is c F b) then b :: List.filter (fun b0 => negb (fk_is c F b0)) l else List.filter (fun b0 => negb (fk_is c F b0)) l).
  unfold hb_ids in *. destruct b as [[p|c'] A n]; unfold fk_is at 1; cbn [ab_kind ab_addr negb flat_map app].
  - rewrite IH. reflexivity.
  - destruct ((c' =? c) && (A =? F)); cbn [negb flat_map ab_kind app]; exact IH.
Qed.

Section CANSEC1. Context {rc : runConstT} {ov : annOV} {gb : GcBit}.

Lemma afake_ext : forall L LB LB' m, AFAKE L LB m -> (forall b, In b LB <-> In b LB') -> AFAKE L LB' m.
Proof.
  intros L LB LB' m (G & CE & HS & LOG & NGC & DC1 & DC2 & FL & LV & TFSC) EQ.
  split; [exact G|]. split; [exact CE|]. split; [exact HS|]. split; [exact LOG|]. split; [exact NGC|]. split; [exact DC1|]. split; [exact DC2|]. split.
  - intros c pos b Hc Hp Hb NZ. apply EQ. exact (FL c pos b Hc Hp Hb NZ).
  - split; [| exact TFSC]. intros c F n Hin. apply LV. apply EQ. exact Hin.
Qed.

Lemma fk_rel_members : forall L LB m c F n, AFAKE L LB m -> In (FKB c F n) LB ->
  forall b, In b LB <-> In b (FKB c F n :: fk_rel c F LB).
Proof.
  intros L LB m c F n AF Hin b. split.
  - intros Hb. destruct (fk_is c F b) eqn:E.
    + left. destruct b as [[p|c'] A n']; unfold fk_is in E; cbn [ab_kind ab_addr] in E; [discriminate|].
      apply andb_true_iff in E. destruct E as [E1 E2]. apply Z.eqb_eq in E1, E2. subst c' A.
      pose proof (afake_lb L LB m c F n AF Hin) as (_ & N1 & _). pose proof (afake_lb L LB m c F n' AF Hb) as (_ & N2 & _). congruence.
    + right. apply fk_rel_In. split; assumption.
  - intros [<- | Hb]; [exact Hin| apply fk_rel_In in Hb; tauto].
Qed.

Lemma ablocks_fk_rel : forall L st X LB c F, ablocks L st X LB -> ablocks L st X (fk_rel c F LB).
Proof.
  intros L st X LB c F (H1 & H2 & H3 & H4). split; [|split; [|split]].
  - intros p A n Hin. apply (H1 p A n). apply fk_rel_In in Hin. tauto.
  - intros c' A n Hin. apply (H2 c' A n). apply fk_rel_In in Hin. tauto.
  - rewrite fk_rel_hb_ids. exact H3.
  - apply NoDup_filter. exact H4.
Qed.

Section S.
Variable DI : ADepotIface.
Variables (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop).
Notation AH := (AFake_arep.AFake_arep.AH DI AQ ASEC).
Hypothesis HL : ahole_laws AH.
Notation AREP_frame_ext' := (AFake_arep.AFake_arep.AREP_frame_ext' DI AQ ASEC HL).

Theorem fake_release_G : forall L RNG st LB m cls F N,
  AHEAP_P AH L RNG st LB m -> In (FKB cls F N) LB ->
  AHEAP_P AH L RNG st (fk_rel cls F LB) (write_to_mem m (wa (fflag L cls F)) [Z_to_bv 8 0]).
Proof.
  intros L RNG st LB m cls F N AHP Hin. pose proof AHP as (ALO & ARNG & [X [AR BL]] & HFK). cbn [AFake_arep.AFake_arep.AH ah_fake] in HFK.
  pose proof (afake_lb L _ m cls F N HFK Hin) as (Hc & Hn & Npos & F64 & FLO & FHI & FK & FC & pos & Hp & HF & EF & FR).
  pose proof HFK as (G & _). pose proof G as (G1 & G2 & G3 & _). pose proof (ablk_lin _ _ G2) as (GL1 & GL2 & GL3 & GL4). unfold FAKESZ, AIMG_HI in *.
  split; [exact ALO|]. split; [exact ARNG|]. split.
  - exists X. split; [| apply ablocks_fk_rel; exact BL].
    eapply (AREP_frame_ext' _ _ _ _ _ [(fflag L cls F, fflag L cls F + 1)]); [exact ALO| exact AR| | |].
    + apply munch_write; [apply munch_refl| lia| cbn; lia|]. cbn. left. lia.
    + apply wmono_write, wmono_refl.
    + constructor; [|constructor]. cbn. intros _. left. lia.
  - cbn [AFake_arep.AFake_arep.AH ah_fake]. apply (afake_release L (fk_rel cls F LB) m cls F N); [| apply fk_rel_not_In].
    eapply afake_ext; [exact HFK| apply (fk_rel_members L LB m cls F N HFK Hin)].
Qed.

End S.
End CANSEC1.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.Shadow.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import RtCells.TwinB AProto.TwinB ABase.TwinB ABytes.TwinB AMalloc_iface.TwinB ADepot_iface.TwinB ARep.TwinB ALayout.TwinB AHeapP.TwinB ARepExt.TwinB FsKit.TwinB AFake_iface.TwinB.

  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_tlsga.TwinB.F_tlsga. Import F_m2s_b.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_sm0.TwinB.AFake_sm0.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_sm0.TwinB.AFake_sm2.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
 Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_arep.TwinB.AFake_arep.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition fk_is (c F : Z) (b : ablock) : bool :=
  match ab_kind b with ABFake c' => (c' =? c) && (ab_addr b =? F) | ABHeap _ => false end.
Definition fk_rel (c F : Z) (LB : list ablock) : list ablock := List.filter (fun b => negb (fk_is c F b)) LB.

Lemma fk_rel_In : forall c F LB b, In b (fk_rel c F LB) <-> In b LB /\ fk_is c F b = false.
Proof. intros. unfold fk_rel. rewrite filter_In, negb_true_iff. tauto. Qed.
Lemma fk_rel_heap : forall c F LB p A n, In (HB p A n) LB -> In (HB p A n) (fk_rel c F LB).
Proof. intros. apply fk_rel_In. split; [assumption| reflexivity]. Qed.
Lemma fk_rel_not_In : forall c F n LB, ~ In (FKB c F n) (fk_rel c F LB).
Proof. intros c F n LB H. apply fk_rel_In in H. destruct H as [_ H]. unfold fk_is in H. cbn in H. rewrite !Z.eqb_refl in H. discriminate. Qed.
Lemma fk_rel_hb_ids : forall c F LB, hb_ids (fk_rel c F LB) = hb_ids LB.
Proof.
  intros c F LB. unfold fk_rel. induction LB as [|b l IH]; [reflexivity|].
  change (List.filter (fun b0 => negb (fk_is c F b0)) (b :: l)) with (if negb (fk_is c F b) then b :: List.filter (fun b0 => negb (fk_is c F b0)) l else List.filter (fun b0 => negb (fk_is c F b0)) l).
  unfold hb_ids in *. destruct b as [[p|c'] A n]; unfold fk_is at 1; cbn [ab_kind ab_addr negb flat_map app].
  - rewrite IH. reflexivity.
  - destruct ((c' =? c) && (A =? F)); cbn [negb flat_map ab_kind app]; exact IH.
Qed.

Section CANSEC1. Context {rc : runConstT} {ov : annOV} {gb : GcBit}.

Lemma afake_ext : forall L LB LB' m, AFAKE L LB m -> (forall b, In b LB <-> In b LB') -> AFAKE L LB' m.
Proof.
  intros L LB LB' m (G & CE & HS & LOG & NGC & DC1 & DC2 & FL & LV & TFSC) EQ.
  split; [exact G|]. split; [exact CE|]. split; [exact HS|]. split; [exact LOG|]. split; [exact NGC|]. split; [exact DC1|]. split; [exact DC2|]. split.
  - intros c pos b Hc Hp Hb NZ. apply EQ. exact (FL c pos b Hc Hp Hb NZ).
  - split; [| exact TFSC]. intros c F n Hin. apply LV. apply EQ. exact Hin.
Qed.

Lemma fk_rel_members : forall L LB m c F n, AFAKE L LB m -> In (FKB c F n) LB ->
  forall b, In b LB <-> In b (FKB c F n :: fk_rel c F LB).
Proof.
  intros L LB m c F n AF Hin b. split.
  - intros Hb. destruct (fk_is c F b) eqn:E.
    + left. destruct b as [[p|c'] A n']; unfold fk_is in E; cbn [ab_kind ab_addr] in E; [discriminate|].
      apply andb_true_iff in E. destruct E as [E1 E2]. apply Z.eqb_eq in E1, E2. subst c' A.
      pose proof (afake_lb L LB m c F n AF Hin) as (_ & N1 & _). pose proof (afake_lb L LB m c F n' AF Hb) as (_ & N2 & _). congruence.
    + right. apply fk_rel_In. split; assumption.
  - intros [<- | Hb]; [exact Hin| apply fk_rel_In in Hb; tauto].
Qed.

Lemma ablocks_fk_rel : forall L st X LB c F, ablocks L st X LB -> ablocks L st X (fk_rel c F LB).
Proof.
  intros L st X LB c F (H1 & H2 & H3 & H4). split; [|split; [|split]].
  - intros p A n Hin. apply (H1 p A n). apply fk_rel_In in Hin. tauto.
  - intros c' A n Hin. apply (H2 c' A n). apply fk_rel_In in Hin. tauto.
  - rewrite fk_rel_hb_ids. exact H3.
  - apply NoDup_filter. exact H4.
Qed.

Section S.
Variable DI : ADepotIface.
Variables (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop).
Notation AH := (AFake_arep.TwinB.AFake_arep.AH DI AQ ASEC).
Hypothesis HL : ahole_laws AH.
Notation AREP_frame_ext' := (AFake_arep.TwinB.AFake_arep.AREP_frame_ext' DI AQ ASEC HL).

Theorem fake_release_G : forall L RNG st LB m cls F N,
  AHEAP_P AH L RNG st LB m -> In (FKB cls F N) LB ->
  AHEAP_P AH L RNG st (fk_rel cls F LB) (write_to_mem m (wa (fflag L cls F)) [Z_to_bv 8 0]).
Proof.
  intros L RNG st LB m cls F N AHP Hin. pose proof AHP as (ALO & ARNG & [X [AR BL]] & HFK). cbn [AFake_arep.TwinB.AFake_arep.AH ah_fake] in HFK.
  pose proof (afake_lb L _ m cls F N HFK Hin) as (Hc & Hn & Npos & F64 & FLO & FHI & FK & FC & pos & Hp & HF & EF & FR).
  pose proof HFK as (G & _). pose proof G as (G1 & G2 & G3 & _). pose proof (ablk_lin _ _ G2) as (GL1 & GL2 & GL3 & GL4). unfold FAKESZ, AIMG_HI in *.
  split; [exact ALO|]. split; [exact ARNG|]. split.
  - exists X. split; [| apply ablocks_fk_rel; exact BL].
    eapply (AREP_frame_ext' _ _ _ _ _ [(fflag L cls F, fflag L cls F + 1)]); [exact ALO| exact AR| | |].
    + apply munch_write; [apply munch_refl| lia| cbn; lia|]. cbn. left. lia.
    + apply wmono_write, wmono_refl.
    + constructor; [|constructor]. cbn. intros _. left. lia.
  - cbn [AFake_arep.TwinB.AFake_arep.AH ah_fake]. apply (afake_release L (fk_rel cls F LB) m cls F N); [| apply fk_rel_not_In].
    eapply afake_ext; [exact HFK| apply (fk_rel_members L LB m cls F N HFK Hin)].
Qed.

End S.
End CANSEC1.
End TwinB.
