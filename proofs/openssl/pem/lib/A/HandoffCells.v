(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import PropExec ShapeAlg SpinAlg AsanAcct AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlan AsanPlanSound.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import HandoffKit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import HandoffImage.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP.
Open Scope Z_scope.


(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint cells_wfb (cs : list cell) : bool :=
  match cs with
  | [] => true
  | CB n bs :: r => (Nat.eqb (length bs) n && cells_wfb r)%bool
  | _ :: r => cells_wfb r
  end.

Lemma cells_wfb_sound : forall cs, cells_wfb cs = true -> cells_wf cs.
Proof.
  induction cs as [|c r IH]; intros H; [exact I|].
  destruct c; cbn [cells_wfb cells_wf cell_wf] in *;
    try (split; [exact I| exact (IH H)]).
  apply andb_prop in H as [H1 H2]. split; [apply Nat.eqb_eq; exact H1| exact (IH H2)].
Qed.

Fixpoint blist_eqb (xs ys : list byte) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => (bv_eqb x y && blist_eqb xs' ys')%bool
  | _, _ => false
  end.

Lemma blist_eqb_eq : forall xs ys, blist_eqb xs ys = true -> xs = ys.
Proof.
  induction xs as [|x xs IH]; intros [|y ys] H; cbn [blist_eqb] in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H1 H2]. apply bv_eqb_eq in H1. subst y. rewrite (IH ys H2). reflexivity.
Qed.

(* [comment removed for export] *)
Definition hs_bytes (ch : acs) (a n : Z) : option (list byte) :=
  match hs_table asegs (klit_cut a (a + n) (kn ch)) a n with Some zs => Some (map (Z_to_bv 8) zs) | None => None end.

(* [comment removed for export] *)
Definition hs_cells (ch : acs) (a : Z) (cs : list cell) : bool :=
  (cells_wfb cs && Z.leb 0 a && Z.leb (a + Z.of_nat (cells_size cs)) (2 ^ 47)
   && match hs_bytes ch a (Z.of_nat (cells_size cs)) with
      | Some bs => blist_eqb (cells_bytes cs) bs
      | None => false
      end)%bool.

(* [comment removed for export] *)
Definition hs_rw_cells (ch : acs) (a : Z) (cs : list cell) : bool :=
  (hs_cells ch a cs && seg_rw_ok asegs a (Z.of_nat (cells_size cs)))%bool.

(* [comment removed for export] *)
Definition dec_le (bs : list byte) : Z := fold_right (fun b acc => bv_unsigned b + 256 * acc) 0 bs.
Definition hs_word (ch : acs) (a : Z) (n : nat) : word :=
  match hs_bytes ch a (Z.of_nat n) with Some bs => Z_to_bv 64 (dec_le bs) | None => Z_to_bv 64 0 end.
Definition hs_blob (ch : acs) (a : Z) (n : nat) : list byte :=
  match hs_bytes ch a (Z.of_nat n) with Some bs => bs | None => [] end.
Definition hs_byte (ch : acs) (a : Z) : byte := nth 0 (hs_blob ch a 1) (Z_to_bv 8 0).

Section Cells.
Variables (A : atable) (LIMIT : Z)
          (SINV : env -> (word -> option byte) -> Prop) (argH : env -> word -> bool) (ISP : Z) (FS0 : Fs.Fs).
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment asegs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a /\ ISP <= bv_unsigned a.
Variables (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : APS.cs_ok asegs A LIMIT SINV argH ISP FS0 E ch R FULL model.
Variable A' : list (Z * Z).
Hypothesis HA' : forall p, page_allowedb (APS.allowA A E ch) p = true -> page_allowedb A' p = true.

#[local] Notation m := (mH FULL model A').

Lemma hi_ro_cells : forall a cs, hs_cells ch a cs = true -> ro_cells asegs m a cs.
Proof.
  intros a cs H. unfold hs_cells in H.
  apply andb_prop in H as [H Hb]. apply andb_prop in H as [H Hhi]. apply andb_prop in H as [Hwf Hlo].
  apply Z.leb_le in Hlo. apply Z.leb_le in Hhi.
  unfold hs_bytes in Hb. destruct (hs_table asegs (klit_cut a (a + Z.of_nat (cells_size cs)) (kn ch)) a (Z.of_nat (cells_size cs))) as [zs|] eqn:Ht; [|discriminate].
  apply blist_eqb_eq in Hb.
  pose proof (hi_lit_cut asegs A LIMIT SINV argH ISP FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA'
                _ _ a (Z.of_nat (cells_size cs)) zs Ht Hlo ltac:(lia) Hhi) as Hl.
  unfold ro_cells, cells_at. split; [exact (cells_wfb_sound cs Hwf)|]. rewrite Hb. exact Hl.
Qed.

Lemma hi_rw_cells : forall a cs, hs_rw_cells ch a cs = true -> rw_cells asegs m a cs.
Proof.
  intros a cs H. unfold hs_rw_cells in H. apply andb_prop in H as [H Hs].
  split; [exact (hi_ro_cells a cs H)|].
  exact (proj1 (seg_rw_ok_sound asegs a (Z.of_nat (cells_size cs)) Hs m)).
Qed.

End Cells.

