(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Common Require Import FastWord FastWordSem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Common.Ax Require Import ExTrie.
From OssFuzzTheorems.Proofs.openssl.ct.lib.HX Require Import HxRegs HxVal HxBytes HxMem HxMemSound HxStep HxHook HxToolkit HxQuery.
From OssFuzzTheorems.Proofs.openssl.ct.lib.HXS Require Import HxsKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXA Require Import HxaInit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record query : Type := Q { q_tag : int; q_lo : Z; q_size : Z; q_off : Z; q_ks : list kb }.

Definition q_ok (S : sstate) (q : query) : bool :=
  match mget (s_mem S) (q_tag q) with
  | Some rg => (match rg_abs rg with
                | Some a => (to_Z a =? q_lo q) && negb (q_lo q =? 0)
                | None => (q_lo q =? 0) && (to_Z (rg_size rg) =? q_size q) && rg_wr rg && negb (q_tag q =? T_STK)%uint63 && (0 <? q_size q)
                          && negb (rg_al rg =? 0)%uint63
                end)
               && (0 <=? q_off q) && (q_off q + Z.of_nat (length (q_ks q)) <=? to_Z (rg_size rg)) && kb_check ctasegs rg (q_off q) (q_ks q)
  | None => false
  end.

(* [comment removed for export] *)
Definition q_addr (rho : valuation) (q : query) : Z := (if q_lo q =? 0 then rho (q_tag q) else q_lo q) + q_off q.

Lemma q_sound (rho : valuation) (S : sstate) (m : word -> option byte) (q : query) :
  Rmem ctasegs rho (s_mem S) m -> q_ok S q = true ->
  exists rg bs, mget (s_mem S) (q_tag q) = Some rg /\ Forall2 (kb_ok rho) (q_ks q) bs /\ bytes_at ctasegs m (q_addr rho q) bs
                /\ (rg_wr rg = true -> wr_at ctasegs m (q_addr rho q) (Z.of_nat (length (q_ks q))))
                /\ (q_lo q = 0 -> rg_abs rg = None /\ to_Z (rg_size rg) = q_size q /\ rg_wr rg = true /\ q_tag q <> T_STK /\ 0 < q_size q
                                  /\ 0 < rho (q_tag q) /\ rho (q_tag q) + q_size q < 2 ^ 63).
Proof.
  intros [HRg _] H. unfold q_ok in H. destruct (mget (s_mem S) (q_tag q)) as [rg|] eqn:Eg; [|discriminate].
  apply andb_prop in H as [H Hk]. apply andb_prop in H as [H Hfit]. apply andb_prop in H as [Habs Hoff].
  apply Z.leb_le in Hoff, Hfit. pose proof (HRg _ _ Eg) as Hok.
  destruct (kb_check_sound ctasegs rho (q_tag q) rg m (q_ks q) (q_off q) Hok Hk Hoff Hfit) as (bs & HF & Hb & Hw).
  exists rg, bs. split; [reflexivity|]. split; [exact HF|].
  pose proof Hok as (B0 & B1 & _). unfold two63 in B1. unfold rbase in B0, B1, Hb, Hw |- *. unfold q_addr in *.
  destruct (rg_abs rg) as [a|] eqn:Ea.
  - apply andb_prop in Habs as [Habs Hnz]. apply Z.eqb_eq in Habs. rewrite Habs in *. apply negb_true_iff in Hnz. rewrite Hnz.
    split; [exact Hb|]. split; [exact Hw|]. intros E0. apply Z.eqb_neq in Hnz. contradiction.
  - apply andb_prop in Habs as [Habs H6]. apply andb_prop in Habs as [Habs H5]. apply andb_prop in Habs as [Habs H4]. apply andb_prop in Habs as [Habs H3]. apply andb_prop in Habs as [H1 H2].
    apply Z.eqb_eq in H2. apply Z.ltb_lt in H5. apply negb_true_iff in H4. apply negb_true_iff in H6. rewrite H1 in *.
    assert (Hal0 : to_Z (rg_al rg) <> 0) by (intros X; destruct (eqbP (rg_al rg) 0) as [Y|Y]; [discriminate | apply Y; exact X]).
    split; [exact Hb|]. split; [exact Hw|]. intros _.
    repeat split; try assumption; try lia. intros E1. rewrite E1 in H4. discriminate.
Qed.

(* [comment removed for export] *)
Lemma q_cells (rho : valuation) (S : sstate) (m : word -> option byte) (q : query) (cs : list Cells.cell) :
  Rmem ctasegs rho (s_mem S) m -> q_ok S q = true -> cells_wf cs ->
  (forall bs, Forall2 (kb_ok rho) (q_ks q) bs -> bs = cells_bytes cs) ->
  ro_cells ctasegs m (q_addr rho q) cs.
Proof.
  intros HR Hq Hwf Hbs. destruct (q_sound rho S m q HR Hq) as (rg & bs & _ & HF & Hb & _). rewrite (Hbs bs HF) in Hb. split; assumption.
Qed.

Lemma q_rw_cells (rho : valuation) (S : sstate) (m : word -> option byte) (q : query) (cs : list Cells.cell) :
  Rmem ctasegs rho (s_mem S) m -> q_ok S q = true -> q_lo q = 0 -> cells_wf cs -> length (q_ks q) = cells_size cs ->
  (forall bs, Forall2 (kb_ok rho) (q_ks q) bs -> bs = cells_bytes cs) ->
  rw_cells ctasegs m (rho (q_tag q) + q_off q) cs.
Proof.
  intros HR Hq E0 Hwf Hl Hbs. destruct (q_sound rho S m q HR Hq) as (rg & bs & _ & HF & Hb & Hw & Hh).
  destruct (Hh E0) as (_ & _ & Hwr & _). unfold q_addr in Hb, Hw. rewrite E0 in Hb, Hw. cbn [Z.eqb] in Hb, Hw.
  rewrite (Hbs bs HF) in Hb. split; [split; assumption|]. rewrite <- Hl. exact (Hw Hwr).
Qed.

(* [comment removed for export] *)
Fixpoint nodupb (l : list int) : bool :=
  match l with [] => true | t :: l' => negb (existsb (fun t' => (t =? t')%uint63) l') && nodupb l' end.

Lemma nodupb_ok : forall l, nodupb l = true -> List.NoDup l.
Proof.
  induction l as [|t l IH]; intros H; [constructor|]. cbn [nodupb] in H. apply andb_prop in H as [H1 H2].
  constructor; [|exact (IH H2)]. intros Hin. apply negb_true_iff in H1.
  assert (X : existsb (fun t' => (t =? t')%uint63) l = true) by (apply existsb_exists; exists t; split; [exact Hin | apply Uint63.eqb_refl]).
  congruence.
Qed.

(* [comment removed for export] *)
Lemma bs_ptr (rho : valuation) (tag : int) (bs : list byte) : 0 < rho tag -> rho tag < 2 ^ 63 ->
  Forall2 (kb_ok rho) (kbs_ptr tag) bs -> bs = cells_bytes [C8 (wz (rho tag))].
Proof. intros H0 H1 H. cbn [cells_bytes cbytes]. rewrite app_nil_r. apply (kbs_ptr_bytes rho tag bs); [lia | exact H]. Qed.

Lemma bs_lit8 (rho : valuation) (z : Z) (bs : list byte) : 0 <= z < 2 ^ 64 ->
  Forall2 (kb_ok rho) (kbs_Z 8 z) bs -> bs = cells_bytes [C8 (wz z)].
Proof.
  intros Hz H. cbn [cells_bytes cbytes]. rewrite app_nil_r. rewrite (kbs_Z_bytes rho 8 z bs ltac:(lia) H).
  unfold le8, word_to_le_bytes, wz. rewrite Z_to_bv_unsigned, bv_wrap_small by exact Hz. reflexivity.
Qed.

Lemma bs_lit4 (rho : valuation) (z : Z) (bs : list byte) : 0 <= z < 2 ^ 64 ->
  Forall2 (kb_ok rho) (kbs_Z 4 z) bs -> bs = le4 (wz z).
Proof. intros Hz H. rewrite (kbs_Z_bytes rho 4 z bs ltac:(lia) H). unfold le4, wz. rewrite Z_to_bv_unsigned, bv_wrap_small by exact Hz. reflexivity. Qed.

Lemma bs_lit1 (rho : valuation) (z : Z) (bs : list byte) : 0 <= z ->
  Forall2 (kb_ok rho) (kbs_Z 1 z) bs -> bs = [Z_to_bv 8 z].
Proof. intros Hz H. rewrite (kbs_Z_bytes rho 1 z bs Hz H). reflexivity. Qed.

(* [comment removed for export] *)
Lemma F2_nil (rho : valuation) (bs : list byte) : Forall2 (kb_ok rho) [] bs -> bs = cells_bytes [].
Proof. intros H. inversion H. reflexivity. Qed.

Lemma F2_ptr (rho : valuation) (tag : int) (ks : list kb) (cs : list Cells.cell) (bs : list byte) : 0 < rho tag -> rho tag < 2 ^ 63 ->
  (forall bs', Forall2 (kb_ok rho) ks bs' -> bs' = cells_bytes cs) ->
  Forall2 (kb_ok rho) (kbs_ptr tag ++ ks) bs -> bs = cells_bytes (C8 (wz (rho tag)) :: cs).
Proof.
  intros H0 H1 Hk H. destruct (Forall2_app_split _ _ _ _ H) as (b1 & b2 & -> & F1 & F2). cbn [cells_bytes cbytes].
  rewrite (Hk b2 F2). f_equal. pose proof (bs_ptr rho tag b1 H0 H1 F1) as E. cbn [cells_bytes cbytes] in E. rewrite app_nil_r in E. exact E.
Qed.

Lemma F2_lit8 (rho : valuation) (z : Z) (ks : list kb) (cs : list Cells.cell) (bs : list byte) : 0 <= z < 2 ^ 64 ->
  (forall bs', Forall2 (kb_ok rho) ks bs' -> bs' = cells_bytes cs) ->
  Forall2 (kb_ok rho) (kbs_Z 8 z ++ ks) bs -> bs = cells_bytes (C8 (wz z) :: cs).
Proof.
  intros Hz Hk H. destruct (Forall2_app_split _ _ _ _ H) as (b1 & b2 & -> & F1 & F2). cbn [cells_bytes cbytes].
  rewrite (Hk b2 F2). f_equal. pose proof (bs_lit8 rho z b1 Hz F1) as E. cbn [cells_bytes cbytes] in E. rewrite app_nil_r in E. exact E.
Qed.

Lemma F2_lit4 (rho : valuation) (z : Z) (ks : list kb) (cs : list Cells.cell) (bs : list byte) : 0 <= z < 2 ^ 64 ->
  (forall bs', Forall2 (kb_ok rho) ks bs' -> bs' = cells_bytes cs) ->
  Forall2 (kb_ok rho) (kbs_Z 4 z ++ ks) bs -> bs = cells_bytes (C4 (wz z) :: cs).
Proof.
  intros Hz Hk H. destruct (Forall2_app_split _ _ _ _ H) as (b1 & b2 & -> & F1 & F2). cbn [cells_bytes cbytes].
  rewrite (Hk b2 F2). f_equal. exact (bs_lit4 rho z b1 Hz F1).
Qed.

Lemma F2_lit1 (rho : valuation) (z : Z) (ks : list kb) (cs : list Cells.cell) (bs : list byte) : 0 <= z ->
  (forall bs', Forall2 (kb_ok rho) ks bs' -> bs' = cells_bytes cs) ->
  Forall2 (kb_ok rho) (kbs_Z 1 z ++ ks) bs -> bs = cells_bytes (C1 (Z_to_bv 8 z) :: cs).
Proof.
  intros Hz Hk H. destruct (Forall2_app_split _ _ _ _ H) as (b1 & b2 & -> & F1 & F2). cbn [cells_bytes cbytes].
  rewrite (Hk b2 F2). f_equal. exact (bs_lit1 rho z b1 Hz F1).
Qed.

Lemma F2_bytes (rho : valuation) (zs : list Z) (bs : list byte) :
  Forall2 (kb_ok rho) (kbs_bytes zs) bs -> bs = cells_bytes [CB (length zs) (map (Z_to_bv 8) zs)].
Proof. intros H. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact (kbs_bytes_bytes rho zs bs H). Qed.

(* [comment removed for export] *)
Lemma F2_tail (rho : valuation) (ks : list kb) (bs : list byte) (P : list byte -> Prop) :
  (forall bs', Forall2 (kb_ok rho) (ks ++ []) bs' -> P bs') -> Forall2 (kb_ok rho) ks bs -> P bs.
Proof. intros H F. apply H. rewrite app_nil_r. exact F. Qed.


