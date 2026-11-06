(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Tac Image ZBridge SysStep Bytes Walk Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes Decode.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Image OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Walk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Arr OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Decode.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import MRepAux Mall5lv Mallj6y Mallwlb Mallrkx Malllim Mallzvh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc Mall7vg Monad MProg MProg MTree MRep MRepAux.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import Mallkgx Mall1es Mall79j KNodes KLink MSafe.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Malls6g.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import AllocSpec LayoutP0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import MI_Inv LB_Inv LB_Sum LB_Ctrl LB_Own.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section CEIL.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

Record ias := mkIAS { ia_s : PState; ia_LB : list block; ia_rr : RunRandom }.   (* [comment removed for export] *)

Definition G0 (s : PState) (mo : Model) : Prop := True.
Lemma gframe_G0 : gframe G0. Proof. intros ? ? ? ? _ _ _ _. exact I. Qed.

Definition find_blk (LB : list block) (p : Z) : option block := find (fun b => Z.eqb (blk_addr b) p) LB.
Definition p0_live (A : ias) (p : Z) : option Z :=
  match find_blk (ia_LB A) p with Some b => Some (blk_size b) | None => None end.

(* [comment removed for export] *)
Lemma heap_zone_p0 a : heap_zone LayoutP0 a <-> (0 <= a < alloc_ceiling /\ ~ (0x10000 <= a < 0x63000)).
Proof. unfold heap_zone, in_image. cbn [al_image_lo al_image_hi LayoutP0]. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). tauto. Qed.

Definition p0_owned (A : ias) (a : Z) : Prop :=
  p0_static a \/ (heap_zone LayoutP0 a /\ ~ in_block (ia_LB A) a).

(* [comment removed for export] *)
Definition repl0 (m : mem) : Prop := rw_cells rsegs m MALLOC_REPLACED [C4 (Z_to_bv 64 0)].

Lemma rw_cells_agree' m m' A cs :
  rw_cells rsegs m A cs -> (forall x, (A <= bv_unsigned x < A + Z.of_nat (cells_size cs))%Z -> m' x = m x) -> rw_cells rsegs m' A cs.
Proof.
  intros [[Hwf (H0 & H1 & Hb)] (W0 & W1 & Hw)] AG.
  pose proof (cells_bytes_length cs Hwf) as LEN.
  split; [split; [exact Hwf|]|].
  - split; [lia|]. split; [lia|]. intros i Hi. unfold mrd. rewrite AG; [apply Hb; exact Hi|]. rewrite wa_unsigned by lia. lia.
  - split; [lia|]. split; [lia|]. intros i Hi. unfold wview. rewrite AG; [apply Hw; exact Hi|]. rewrite wa_unsigned by lia. lia.
Qed.

Lemma repl0_agree m m' : repl0 m ->
  (forall a, MALLOC_REPLACED <= a < MALLOC_REPLACED + 4 -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)) -> repl0 m'.
Proof.
  intros R AG. eapply rw_cells_agree'; [exact R|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx.
  rewrite <- (definitions.Z_to_bv_bv_unsigned 64 x). apply AG. lia.
Qed.

(* [comment removed for export] *)
Definition lb_bytes (LB : list block) : Z := zsum (map blk_size LB).
Definition p0_livebytes (A : ias) : Z := lb_bytes (ia_LB A).
Definition p0_nlive (A : ias) : Z := zlen (ia_LB A).
Definition blk0 (LB : list block) : list blk := map (fun b : block => ((blk_slot b, 0), blk_size b)) LB.
Definition xof (LB : list block) : list (bptr * Z) := map (fun b : block => (blk_id b, blk_size b)) LB.

Definition p0_ainv (A : ias) (m : mem) (md : Model) : Prop :=
  HEAP (Rr:=ia_rr A) (ia_s A) (ia_LB A) m /\ OWN (map blk_id (ia_LB A)) G0 (ia_s A) md /\ repl0 m
  /\ QV (ps_m (ia_s A)) (blk0 (ia_LB A)).

End CEIL.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section Geometry.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)
Variables (s : PState) (LB : list block) (m : mem).
Hypothesis HP : HEAP s LB m.

Lemma heap_block_zone : forall b, In b LB ->
  4096 <= blk_addr b /\ 0 <= blk_size b /\ blk_addr b + blk_size b < alloc_ceiling
  /\ (blk_addr b + blk_size b < 0x10000 \/ 0x63000 <= blk_addr b) /\ blk_addr b mod 16 = 0.
Proof.
  intros b Hb. (first [ pose proof ((HEAP_block_range_proof s LB m b HP Hb)) as dR_1; dand3 dR_1 as _ AL _ | pose proof (HEAP_block_range_proof s LB m b HP Hb) as (_ & AL & _) ]).
  destruct HP as (st & LB0 & PERM & _ & MR & [_ AR]). pose proof (Malls6g.areach_facts_proof _ _ AR) as MF.
  assert (IN0 : In b LB0) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hb]).
  (first [ pose proof ((rblock_inside_strict st LB0 m b MF MR IN0)) as dR_2; dex1 dR_2 as r; dand8 dR_2 as Hr Hk LO HI BZ R4 RC RI | pose proof ((rblock_inside_strict st LB0 m b MF MR IN0)) as dR_2; dand9 dR_2 as r Hr Hk LO HI BZ R4 RC RI | destruct (rblock_inside_strict st LB0 m b MF MR IN0) as (r & Hr & Hk & LO & HI & BZ & R4 & RC & RI) ]). lia.
Qed.

Lemma heap_block_hz : forall b a, In b LB -> blk_addr b <= a <= blk_addr b + blk_size b -> heap_zone LayoutP0 a.
Proof.
  intros b a Hb Ha. apply heap_zone_p0. pose proof (heap_block_zone b Hb). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). lia.
Qed.

(* [comment removed for export] *)
Lemma heap_blocks_apart : forall b1 b2, In b1 LB -> In b2 LB -> blk_id b1 <> blk_id b2 ->
  blk_addr b1 + blk_size b1 < blk_addr b2 \/ blk_addr b2 + blk_size b2 < blk_addr b1.
Proof.
  intros b1 b2 I1 I2 NE. destruct HP as (st & LB0 & PERM & _ & MR & [_ AR]).
  pose proof (Malls6g.areach_facts_proof _ _ AR) as MF.
  assert (IN1 : In b1 LB0) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| exact I1]).
  assert (IN2 : In b2 LB0) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| exact I2]).
  destruct (decide (blk_slot b1 = blk_slot b2)) as [ES|NS].
  - exfalso. apply NE. pose proof (mf_nodup _ _ MF) as ND.
    clear -ND IN1 IN2 ES; try pose proof alloc_ceiling_val. induction LB0 as [|b LB0 IH]; [destruct IN1|]. cbn in ND. inversion ND; subst.
    destruct IN1 as [->|IN1], IN2 as [->|IN2]; [reflexivity| | | apply IH; assumption].
    + exfalso. apply H1. rewrite ES. apply in_map_iff. exists b2; auto.
    + exfalso. apply H1. rewrite <- ES. apply in_map_iff. exists b1; auto.
  - destruct (N.eq_dec (fst (blk_slot b1)) (fst (blk_slot b2))) as [EF|NF].
    + exact (Malls6g.areach_blocks_apart_proof _ _ AR b1 b2 IN1 IN2 EF NS).
    + (first [ pose proof ((rblock_inside_strict st LB0 m b1 MF MR IN1)) as dR_3; dex1 dR_3 as r1; dand5 dR_3 as Hr1 Hk1 LO1 HI1 _ | pose proof ((rblock_inside_strict st LB0 m b1 MF MR IN1)) as dR_3; dand6 dR_3 as r1 Hr1 Hk1 LO1 HI1 _ | destruct (rblock_inside_strict st LB0 m b1 MF MR IN1) as (r1 & Hr1 & Hk1 & LO1 & HI1 & _) ]).
      (first [ pose proof ((rblock_inside_strict st LB0 m b2 MF MR IN2)) as dR_4; dex1 dR_4 as r2; dand5 dR_4 as Hr2 Hk2 LO2 HI2 _ | pose proof ((rblock_inside_strict st LB0 m b2 MF MR IN2)) as dR_4; dand6 dR_4 as r2 Hr2 Hk2 LO2 HI2 _ | destruct (rblock_inside_strict st LB0 m b2 MF MR IN2) as (r2 & Hr2 & Hk2 & LO2 & HI2 & _) ]).
      pose proof MR as (WF & _). (first [ pose proof (WF) as dR_5; dand4 dR_5 as _ _ DJ _ | pose proof WF as (_ & _ & DJ & _) ]).
      pose proof (lr_lo_group r1 Hk1). pose proof (lr_lo_group r2 Hk2).
      destruct (DJ _ _ _ _ Hr1 Hr2 NF); lia.
Qed.

Lemma heap_ids_nodup : List.NoDup (map blk_id LB).
Proof. exact (HEAP_blocks_nodup_proof s LB m HP). Qed.

Lemma heap_addr_inj : forall b1 b2, In b1 LB -> In b2 LB -> blk_addr b1 = blk_addr b2 -> b1 = b2.
Proof.
  intros b1 b2 I1 I2 E. destruct (decide (blk_id b1 = blk_id b2)) as [EI|NI].
  - pose proof heap_ids_nodup as ND. clear -ND I1 I2 EI; try pose proof alloc_ceiling_val.
    induction LB as [|b L IH]; [destruct I1|]. cbn in ND. inversion ND; subst.
    destruct I1 as [->|I1], I2 as [->|I2]; [reflexivity| | | apply IH; assumption].
    + exfalso. apply H1. rewrite EI. apply in_map_iff. exists b2; auto.
    + exfalso. apply H1. rewrite <- EI. apply in_map_iff. exists b1; auto.
  - exfalso. pose proof (heap_block_zone b1 I1). pose proof (heap_block_zone b2 I2).
    destruct (heap_blocks_apart b1 b2 I1 I2 NI); lia.
Qed.

(* [comment removed for export] *)
Lemma heap_block_mapped : forall b i, In b LB -> 0 <= i < blk_size b -> m (wa (blk_addr b + i)) <> None.
Proof.
  intros b i Hb Hi. destruct HP as (st & LB0 & PERM & _ & MR & [_ AR]).
  pose proof (Malls6g.areach_facts_proof _ _ AR) as MF.
  assert (IN0 : In b LB0) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hb]).
  (first [ pose proof ((rblock_inside_strict st LB0 m b MF MR IN0)) as dR_6; dex1 dR_6 as r; dand8 dR_6 as Hr Hk LO HI BZ R4 RC RI | pose proof ((rblock_inside_strict st LB0 m b MF MR IN0)) as dR_6; dand9 dR_6 as r Hr Hk LO HI BZ R4 RC RI | destruct (rblock_inside_strict st LB0 m b MF MR IN0) as (r & Hr & Hk & LO & HI & BZ & R4 & RC & RI) ]).
  (first [ pose proof (MR) as dR_7; dand6 dR_7 as WF CX GL ARr GR SH | pose proof MR as (WF & CX & GL & ARr & GR & SH) ]). destruct (SH _ r Hr Hk) as [(W0 & W1 & HW) _].
  specialize (HW (blk_addr b + i - r_base r) ltac:(lia)). replace (r_base r + (blk_addr b + i - r_base r)) with (blk_addr b + i) in HW by lia.
  rewrite p0_wview_overlay in HW; [exact HW|]. unfold wa. rewrite unsigned_lit; [lia|]. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). lia.
Qed.
End Geometry.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma find_blk_some LB p b : find_blk LB p = Some b -> In b LB /\ blk_addr b = p.
Proof. intros H. unfold find_blk in H. apply find_some in H. destruct H as [Hin E]. apply Z.eqb_eq in E. auto. Qed.

Lemma find_blk_none LB p : find_blk LB p = None -> forall b, In b LB -> blk_addr b <> p.
Proof. intros H b Hb E. unfold find_blk in H. pose proof (find_none _ _ H b Hb) as X. cbn in X. apply Z.eqb_neq in X. exact (X E). Qed.

Section CEIL2.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

Lemma find_blk_in s LB m b : HEAP s LB m -> In b LB -> find_blk LB (blk_addr b) = Some b.
Proof.
  intros HP Hb. destruct (find_blk LB (blk_addr b)) as [b'|] eqn:E.
  - apply find_blk_some in E. destruct E as [Hin Ea]. f_equal. exact (heap_addr_inj s LB m HP b' b Hin Hb Ea).
  - exfalso. exact (find_blk_none LB _ E b Hb eq_refl).
Qed.

Lemma p0_live_some A p n : p0_live A p = Some n -> exists b, In b (ia_LB A) /\ blk_addr b = p /\ blk_size b = n.
Proof.
  unfold p0_live. destruct (find_blk (ia_LB A) p) as [b|] eqn:E; [|discriminate]. intros H. inversion H; subst.
  apply find_blk_some in E. exists b. tauto.
Qed.

Lemma p0_live_in s LB m b : HEAP s LB m -> In b LB -> p0_live (mkIAS s LB Rr) (blk_addr b) = Some (blk_size b).
Proof. intros HP Hb. unfold p0_live. cbn [ia_LB]. rewrite (find_blk_in s LB m b HP Hb). reflexivity. Qed.

(* [comment removed for export] *)
Lemma in_lb_remove LB q b : In b (lb_remove q LB) <-> In b LB /\ blk_id b <> q.
Proof.
  unfold lb_remove. rewrite <- !list_elem_of_In. rewrite list_elem_of_filter.
  unfold bptr_eqb. destruct (aptr_eqb_spec' (fst (blk_id b)) (fst q)) as [E|NE]; cbn [andb negb].
  - destruct (Z.eqb_spec (snd (blk_id b)) (snd q)) as [E2|NE2]; cbn.
    + split; [intros [H _]; destruct H| intros [_ H]]. exfalso. apply H. destruct (blk_id b), q; cbn in *; congruence.
    + split; [intros [_ H]| intros [H H']]; split; auto. intros X. apply NE2. rewrite X. reflexivity.
  - split; [intros [_ H]| intros [H _]]; split; auto; try exact I. intros X. apply NE. rewrite X. reflexivity.
Qed.

Lemma find_blk_remove s LB m b q : HEAP s LB m -> In b LB -> q <> blk_addr b ->
  find_blk (lb_remove (blk_id b) LB) q = find_blk LB q.
Proof.
  intros HP Hb Hq.
  destruct (find_blk LB q) as [b'|] eqn:E.
  - apply find_blk_some in E. destruct E as [Hin Ea].
    assert (Hin' : In b' (lb_remove (blk_id b) LB)).
    { apply in_lb_remove. split; [exact Hin|]. intros EI. apply Hq. rewrite <- Ea.
      f_equal. symmetry. apply (heap_addr_inj s LB m HP b b' Hb Hin).
      pose proof (heap_ids_nodup s LB m HP) as ND.
      clear -ND Hb Hin EI; try pose proof alloc_ceiling_val. induction LB as [|x L IH]; [destruct Hb|]. cbn in ND. inversion ND; subst.
      destruct Hb as [->|Hb], Hin as [->|Hin]; [reflexivity| | | apply IH; assumption].
      - exfalso. apply H1. rewrite <- EI. apply in_map_iff. exists b'; auto.
      - exfalso. apply H1. rewrite EI. apply in_map_iff. exists b; auto. }
    destruct (find_blk (lb_remove (blk_id b) LB) q) as [b''|] eqn:E2.
    + apply find_blk_some in E2. destruct E2 as [Hin'' Ea'']. apply in_lb_remove in Hin''. destruct Hin'' as [Hin'' _].
      f_equal. apply (heap_addr_inj s LB m HP b'' b' Hin'' Hin). congruence.
    + exfalso. exact (find_blk_none _ _ E2 b' Hin' Ea).
  - destruct (find_blk (lb_remove (blk_id b) LB) q) as [b''|] eqn:E2; [|reflexivity].
    apply find_blk_some in E2. destruct E2 as [Hin'' Ea'']. apply in_lb_remove in Hin''. destruct Hin'' as [Hin'' _].
    exfalso. exact (find_blk_none _ _ E b'' Hin'' Ea'').
Qed.

Lemma find_blk_remove_self s LB m b : HEAP s LB m -> In b LB -> find_blk (lb_remove (blk_id b) LB) (blk_addr b) = None.
Proof.
  intros HP Hb. destruct (find_blk (lb_remove (blk_id b) LB) (blk_addr b)) as [b'|] eqn:E; [|reflexivity].
  apply find_blk_some in E. destruct E as [Hin Ea]. apply in_lb_remove in Hin. destruct Hin as [Hin NE].
  exfalso. apply NE. f_equal. apply (heap_addr_inj s LB m HP b' b Hin Hb Ea).
Qed.

Lemma bptr_eqb_refl q : bptr_eqb q q = true.
Proof. unfold bptr_eqb. destruct (aptr_eqb_spec' (fst q) (fst q)); [| congruence]. rewrite Z.eqb_refl. reflexivity. Qed.

Lemma lb_remove_cons q b L :
  lb_remove q (b :: L) = if bptr_eqb (blk_id b) q then lb_remove q L else b :: lb_remove q L.
Proof.
  unfold lb_remove. cbn [filter list_filter]. destruct (bptr_eqb (blk_id b) q); cbn; reflexivity.
Qed.

Lemma lb_remove_notin q L : ~ In q (map blk_id L) -> lb_remove q L = L.
Proof.
  induction L as [|x L IH]; intros H; [reflexivity|].
  rewrite lb_remove_cons. cbn in H.
  destruct (bptr_eqb (blk_id x) q) eqn:E.
  - exfalso. apply H. left. unfold bptr_eqb in E. apply andb_prop in E. destruct E as [E1 E2].
    destruct (aptr_eqb_spec' (fst (blk_id x)) (fst q)) as [E1'|]; [|discriminate]. apply Z.eqb_eq in E2.
    destruct (blk_id x), q; cbn in *; congruence.
  - f_equal. apply IH. tauto.
Qed.

(* [comment removed for export] *)

End CEIL2.
