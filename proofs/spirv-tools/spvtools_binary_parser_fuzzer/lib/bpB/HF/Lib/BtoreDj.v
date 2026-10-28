(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BellsX BacX BLFrame.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Definition chunk_disj (A2 s2 A S : Z) : Prop := A2 + s2 <= A \/ A + S <= A2.
Definition chunk_nodj (A2 s2 A S : Z) : Prop := True.
Definition chunk_in (W : list ivl) (A S : Z) : Prop := inside W A S.

Lemma inside_sub : forall W A S k n, inside W A S -> 0 <= k -> k + n <= S -> inside W (A + k) n.
Proof. induction W as [|[lo hi] W IH]; cbn; intros A S k n H Hk Hn; [exact H|]. destruct H as [H|H]; [left; lia| right; eauto]. Qed.

Section WithSegs.
  Variable segs : list Segment.

  Lemma tgt_bounds : forall mT A csT S kn (c' : cell),
    rw_cells segs mT A csT -> Z.of_nat (cells_size csT) = S -> (Z.of_nat kn + Z.of_nat (csize c') <=? S) = true ->
    0 <= A /\ A + S <= 2^64 /\ 0 <= A + Z.of_nat kn /\ A + Z.of_nat kn + Z.of_nat (csize c') <= 2^64 /\ Z.of_nat kn + Z.of_nat (csize c') <= S.
  Proof. intros mT A csT S kn c' HT ES HK. apply Z.leb_le in HK. pose proof (rw_cells_bound segs mT A csT HT). lia. Qed.

  Lemma dj_core : forall mT A csT S kn (c' : cell) A2 s2,
    rw_cells segs mT A csT -> Z.of_nat (cells_size csT) = S -> (Z.of_nat kn + Z.of_nat (csize c') <=? S) = true ->
    cell_wf c' -> chunk_disj A2 s2 A S ->
    0 <= A + Z.of_nat kn /\ A + Z.of_nat kn + Z.of_nat (length (cbytes c')) <= 2^64
    /\ (A2 + s2 <= A + Z.of_nat kn \/ A + Z.of_nat kn + Z.of_nat (length (cbytes c')) <= A2).
  Proof.
    intros mT A csT S kn c' A2 s2 HT ES HK WF DJ. rewrite (cbytes_length c' WF).
    destruct (tgt_bounds mT A csT S kn c' HT ES HK) as (B1 & B2 & B3 & B4 & B5). unfold chunk_disj in DJ. lia.
  Qed.

  Lemma rw_cells_frame_dj : forall mT A csT S kn (c' : cell) m A2 cs2 s2,
    rw_cells segs mT A csT -> Z.of_nat (cells_size csT) = S -> (Z.of_nat kn + Z.of_nat (csize c') <=? S) = true -> cell_wf c' ->
    Z.of_nat (cells_size cs2) = s2 -> chunk_disj A2 s2 A S ->
    rw_cells segs m A2 cs2 -> rw_cells segs (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) A2 cs2.
  Proof.
    intros mT A csT S kn c' m A2 cs2 s2 HT ES HK WF E2 DJ H. destruct (dj_core mT A csT S kn c' A2 s2 HT ES HK WF DJ) as (P1 & P2 & P3).
    apply rw_cells_frame; [exact H| exact P1| exact P2| rewrite E2; exact P3].
  Qed.
  Lemma ro_cells_frame_dj : forall mT A csT S kn (c' : cell) m A2 cs2 s2,
    rw_cells segs mT A csT -> Z.of_nat (cells_size csT) = S -> (Z.of_nat kn + Z.of_nat (csize c') <=? S) = true -> cell_wf c' ->
    Z.of_nat (cells_size cs2) = s2 -> chunk_disj A2 s2 A S ->
    ro_cells segs m A2 cs2 -> ro_cells segs (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) A2 cs2.
  Proof.
    intros mT A csT S kn c' m A2 cs2 s2 HT ES HK WF E2 DJ H. destruct (dj_core mT A csT S kn c' A2 s2 HT ES HK WF DJ) as (P1 & P2 & P3).
    apply ro_cells_frame; [exact H| exact P1| exact P2| rewrite E2; exact P3].
  Qed.
  Lemma bytes_at_frame_dj : forall mT A csT S kn (c' : cell) m A2 bs2 s2,
    rw_cells segs mT A csT -> Z.of_nat (cells_size csT) = S -> (Z.of_nat kn + Z.of_nat (csize c') <=? S) = true -> cell_wf c' ->
    Z.of_nat (length bs2) = s2 -> chunk_disj A2 s2 A S ->
    bytes_at segs m A2 bs2 -> bytes_at segs (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) A2 bs2.
  Proof.
    intros mT A csT S kn c' m A2 bs2 s2 HT ES HK WF E2 DJ H. destruct (dj_core mT A csT S kn c' A2 s2 HT ES HK WF DJ) as (P1 & P2 & P3).
    apply bytes_at_write_other; [exact H| exact P1| exact P2| rewrite E2; exact P3].
  Qed.
  Lemma u8arr_frame_dj : forall mT A csT S kn (c' : cell) m A2 bs2 s2,
    rw_cells segs mT A csT -> Z.of_nat (cells_size csT) = S -> (Z.of_nat kn + Z.of_nat (csize c') <=? S) = true -> cell_wf c' ->
    Z.of_nat (length bs2) = s2 -> chunk_disj A2 s2 A S ->
    u8arr segs m A2 bs2 -> u8arr segs (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) A2 bs2.
  Proof.
    intros mT A csT S kn c' m A2 bs2 s2 HT ES HK WF E2 DJ H. destruct (dj_core mT A csT S kn c' A2 s2 HT ES HK WF DJ) as (P1 & P2 & P3).
    apply u8arr_frame; [exact H| exact P1| exact P2| rewrite E2; exact P3].
  Qed.
  Lemma u8ro_frame_dj : forall mT A csT S kn (c' : cell) m A2 bs2 s2,
    rw_cells segs mT A csT -> Z.of_nat (cells_size csT) = S -> (Z.of_nat kn + Z.of_nat (csize c') <=? S) = true -> cell_wf c' ->
    Z.of_nat (length bs2) = s2 -> chunk_disj A2 s2 A S ->
    u8ro segs m A2 bs2 -> u8ro segs (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) A2 bs2.
  Proof.
    intros mT A csT S kn c' m A2 bs2 s2 HT ES HK WF E2 DJ H. destruct (dj_core mT A csT S kn c' A2 s2 HT ES HK WF DJ) as (P1 & P2 & P3).
    apply u8ro_frame; [exact H| exact P1| exact P2| rewrite E2; exact P3].
  Qed.
  Lemma u32arr_frame_dj : forall mT A csT S kn (c' : cell) m A2 ws s2,
    rw_cells segs mT A csT -> Z.of_nat (cells_size csT) = S -> (Z.of_nat kn + Z.of_nat (csize c') <=? S) = true -> cell_wf c' ->
    4 * Z.of_nat (length ws) = s2 -> chunk_disj A2 s2 A S ->
    u32arr segs m A2 ws -> u32arr segs (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) A2 ws.
  Proof.
    intros mT A csT S kn c' m A2 ws s2 HT ES HK WF E2 DJ H. destruct (dj_core mT A csT S kn c' A2 s2 HT ES HK WF DJ) as (P1 & P2 & P3).
    apply u32arr_frame; [exact H| exact P1| exact P2| rewrite E2; exact P3].
  Qed.
  Lemma u64arr_frame_dj : forall mT A csT S kn (c' : cell) m A2 ws s2,
    rw_cells segs mT A csT -> Z.of_nat (cells_size csT) = S -> (Z.of_nat kn + Z.of_nat (csize c') <=? S) = true -> cell_wf c' ->
    8 * Z.of_nat (length ws) = s2 -> chunk_disj A2 s2 A S ->
    u64arr segs m A2 ws -> u64arr segs (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) A2 ws.
  Proof.
    intros mT A csT S kn c' m A2 ws s2 HT ES HK WF E2 DJ H. destruct (dj_core mT A csT S kn c' A2 s2 HT ES HK WF DJ) as (P1 & P2 & P3).
    apply u64arr_frame; [exact H| exact P1| exact P2| rewrite E2; exact P3].
  Qed.
  Lemma munch_write_in : forall mT A csT S kn (c' : cell) W m0 m,
    rw_cells segs mT A csT -> Z.of_nat (cells_size csT) = S -> (Z.of_nat kn + Z.of_nat (csize c') <=? S) = true -> cell_wf c' ->
    chunk_in W A S ->
    munch W m0 m -> munch W m0 (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')).
  Proof.
    intros mT A csT S kn c' W m0 m HT ES HK WF IN H.
    destruct (tgt_bounds mT A csT S kn c' HT ES HK) as (B1 & B2 & B3 & B4 & B5).
    apply munch_write; [exact H| exact B3| rewrite (cbytes_length c' WF); exact B4|].
    rewrite (cbytes_length c' WF). apply (inside_sub W A S); [exact IN| lia| exact B5].
  Qed.
  Lemma stk_write_in : forall mT A csT S kn (c' : cell) m lo hi,
    rw_cells segs mT A csT -> Z.of_nat (cells_size csT) = S -> (Z.of_nat kn + Z.of_nat (csize c') <=? S) = true -> cell_wf c' ->
    stk segs m lo hi -> stk segs (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) lo hi.
  Proof.
    intros mT A csT S kn c' m lo hi HT ES HK WF H.
    destruct (tgt_bounds mT A csT S kn c' HT ES HK) as (B1 & B2 & B3 & B4 & B5).
    apply stk_write; [exact H| exact B3| rewrite (cbytes_length c' WF); exact B4].
  Qed.
End WithSegs.

From Ltac2 Require Ltac2.
Module N8Lit.
  Import Ltac2.
  Ltac2 rec nat_lit (t : constr) : bool :=
    match Constr.Unsafe.kind t with
    | Constr.Unsafe.Constructor _ _ => Constr.equal t 'O
    | Constr.Unsafe.App f args =>
        if Constr.equal f 'S then (if Int.equal (Array.length args) 1 then nat_lit (Array.get args 0) else false) else false
    | _ => false
    end.
  Ltac2 cell_lit (c : constr) : bool :=
    match Constr.Unsafe.kind c with
    | Constr.Unsafe.App f args =>
        if Constr.equal f 'C8 then true else if Constr.equal f 'C4 then true else if Constr.equal f 'C2 then true
        else if Constr.equal f 'C1 then true
        else if Constr.equal f 'CB then (if Int.equal (Array.length args) 2 then nat_lit (Array.get args 0) else false)
        else false
    | _ => false
    end.

  Ltac2 rec list_lit (chk : constr -> bool) (l : constr) : bool :=
    match Constr.Unsafe.kind l with
    | Constr.Unsafe.App f args =>
        if Int.equal (Array.length args) 3 then
          (if Constr.equal f '@cons then (if chk (Array.get args 1) then list_lit chk (Array.get args 2) else false) else false)
        else if Int.equal (Array.length args) 1 then Constr.equal f '@nil
        else false
    | _ => false
    end.
  Ltac2 cells_lit (cs : constr) : unit := if list_lit cell_lit cs then () else Control.zero (Tactic_failure None).
  Ltac2 plain_list_lit (l : constr) : unit := if list_lit (fun _ => true) l then () else Control.zero (Tactic_failure None).
End N8Lit.
Ltac n8_cells_lit cs := let f := ltac2:(c |- N8Lit.cells_lit (Option.get (Ltac1.to_constr c))) in f cs.
Ltac n8_list_lit l := let f := ltac2:(c |- N8Lit.plain_list_lit (Option.get (Ltac1.to_constr c))) in f l.

Ltac dj_size_cells cs :=
  match goal with
  | _ => let _ := constr:(ltac:(n8_cells_lit cs; exact I) : True) in eval lazy in (Z.of_nat (cells_size cs))
  | _ => constr:(Z.of_nat (cells_size cs))
  end.
Ltac dj_size_len t xs :=
  match goal with
  | _ => let _ := constr:(ltac:(n8_list_lit xs; exact I) : True) in eval lazy in t
  | _ => t
  end.

Ltac dj_get A2 s2 A S k :=
  lazymatch goal with
  | DJ : chunk_disj A2 s2 A S |- _ => k DJ
  | _ : chunk_nodj A2 s2 A S |- _ => fail
  | _ =>
      let DJ := fresh "DJc" in
      first [ assert (DJ : chunk_disj A2 s2 A S) by (unfold chunk_disj; simpl_arr_sizes; simpl_sizes; lia)
            | pose proof (I : chunk_nodj A2 s2 A S) as DJ; fail ];
      k DJ
  end.

Definition chunk_noin (W : list ivl) (A S : Z) : Prop := True.

Ltac dj_ensure A2 s2 A S :=
  lazymatch goal with
  | _ : chunk_disj A2 s2 A S |- _ => idtac
  | _ : chunk_nodj A2 s2 A S |- _ => idtac
  | _ => let DJ := fresh "DJc" in
         first [ assert (DJ : chunk_disj A2 s2 A S) by (unfold chunk_disj; simpl_arr_sizes; simpl_sizes; lia)
               | pose proof (I : chunk_nodj A2 s2 A S) as DJ ]
  end.
Ltac in_ensure W A S :=
  lazymatch goal with
  | _ : chunk_in W A S |- _ => idtac
  | _ : chunk_noin W A S |- _ => idtac
  | _ => let DJ := fresh "INc" in
         first [ assert (DJ : chunk_in W A S) by (unfold chunk_in; cbn [inside]; lia)
               | pose proof (I : chunk_noin W A S) as DJ ]
  end.

Ltac tc1_orig_rw segs m a bs H A2 cs2 :=
  first [ apply (rw_cells_frame segs m A2 cs2 a bs) in H; [ | lia | simpl_sizes; slia | simpl_sizes; slia ]
        | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ].
Ltac tc1_orig_ro segs m a bs H A2 cs2 :=
  first [ apply (ro_cells_frame segs m A2 cs2 a bs) in H; [ | lia | simpl_sizes; slia | simpl_sizes; slia ]
        | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ].
Ltac tc1_orig_ba segs m a bs H A2 bs2 :=
  first [ apply (bytes_at_write_other segs m a bs A2 bs2) in H; [ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
        | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ].
Ltac tc1_orig_u8 segs m a bs H A2 xs :=
  first [ apply (u8arr_frame segs m A2 xs a bs) in H; [ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
        | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ].
Ltac tc1_orig_u32 segs m a bs H A2 xs :=
  first [ apply (u32arr_frame segs m A2 xs a bs) in H; [ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
        | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ].
Ltac tc1_orig_u64 segs m a bs H A2 xs :=
  first [ apply (u64arr_frame segs m A2 xs a bs) in H; [ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
        | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ].
Ltac tc1_orig_u8ro segs m a bs H A2 xs :=
  first [ apply (u8ro_frame segs m A2 xs a bs) in H; [ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
        | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ].

Ltac transport_chunks_dj segs m a bs mT A csT S kn c' HT ES HK :=
  repeat match goal with
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      let s2 := dj_size_cells cs2 in
      dj_ensure A2 s2 A S;
      lazymatch goal with
      | DJ : chunk_disj A2 s2 A S |- _ =>
          apply (rw_cells_frame_dj segs mT A csT S kn c' m A2 cs2 s2 HT ES HK I (@eq_refl Z s2) DJ) in H
      | _ => tc1_orig_rw segs m a bs H A2 cs2
      end
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      let s2 := dj_size_cells cs2 in
      dj_ensure A2 s2 A S;
      lazymatch goal with
      | DJ : chunk_disj A2 s2 A S |- _ =>
          apply (ro_cells_frame_dj segs mT A csT S kn c' m A2 cs2 s2 HT ES HK I (@eq_refl Z s2) DJ) in H
      | _ => tc1_orig_ro segs m a bs H A2 cs2
      end
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      let s2 := dj_size_len (Z.of_nat (length bs2)) bs2 in
      dj_ensure A2 s2 A S;
      lazymatch goal with
      | DJ : chunk_disj A2 s2 A S |- _ =>
          apply (bytes_at_frame_dj segs mT A csT S kn c' m A2 bs2 s2 HT ES HK I (@eq_refl Z s2) DJ) in H
      | _ => tc1_orig_ba segs m a bs H A2 bs2
      end
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_write segs m A2 n2 (wa a) bs) in H
  | H : u8arr segs m ?A2 ?xs |- _ =>
      let s2 := dj_size_len (Z.of_nat (length xs)) xs in
      dj_ensure A2 s2 A S;
      lazymatch goal with
      | DJ : chunk_disj A2 s2 A S |- _ =>
          apply (u8arr_frame_dj segs mT A csT S kn c' m A2 xs s2 HT ES HK I (@eq_refl Z s2) DJ) in H
      | _ => tc1_orig_u8 segs m a bs H A2 xs
      end
  | H : u32arr segs m ?A2 ?xs |- _ =>
      let s2 := dj_size_len (4 * Z.of_nat (length xs)) xs in
      dj_ensure A2 s2 A S;
      lazymatch goal with
      | DJ : chunk_disj A2 s2 A S |- _ =>
          apply (u32arr_frame_dj segs mT A csT S kn c' m A2 xs s2 HT ES HK I (@eq_refl Z s2) DJ) in H
      | _ => tc1_orig_u32 segs m a bs H A2 xs
      end
  | H : u64arr segs m ?A2 ?xs |- _ =>
      let s2 := dj_size_len (8 * Z.of_nat (length xs)) xs in
      dj_ensure A2 s2 A S;
      lazymatch goal with
      | DJ : chunk_disj A2 s2 A S |- _ =>
          apply (u64arr_frame_dj segs mT A csT S kn c' m A2 xs s2 HT ES HK I (@eq_refl Z s2) DJ) in H
      | _ => tc1_orig_u64 segs m a bs H A2 xs
      end
  | H : u8ro segs m ?A2 ?xs |- _ =>
      let s2 := dj_size_len (Z.of_nat (length xs)) xs in
      dj_ensure A2 s2 A S;
      lazymatch goal with
      | DJ : chunk_disj A2 s2 A S |- _ =>
          apply (u8ro_frame_dj segs mT A csT S kn c' m A2 xs s2 HT ES HK I (@eq_refl Z s2) DJ) in H
      | _ => tc1_orig_u8ro segs m a bs H A2 xs
      end
  | MU : munch ?Wq ?mq m |- _ =>
      in_ensure Wq A S;
      lazymatch goal with
      | IN : chunk_in Wq A S |- _ => apply (munch_write_in segs mT A csT S kn c' Wq mq m HT ES HK I IN) in MU
      | _ => first [ apply (munch_write Wq mq m a bs) in MU; [ | lia | simpl_sizes; slia | cbn [inside]; simpl_sizes; slia ]
                   | fail 100 "store outside the declared footprint:" a ]
      end
  | WMo : wmono segs ?mq m |- _ => apply (wmono_write segs mq m (wa a) bs) in WMo
  | STq : stk segs m ?loq ?hiq |- _ => apply (stk_write_in segs mT A csT S kn c' m loq hiq HT ES HK I) in STq
  end.

Ltac transport_chunks_orig segs m a bs :=
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ => tc1_orig_ba segs m a bs H A2 bs2
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_write segs m A2 n2 (wa a) bs) in H
  | H : rw_cells segs m ?A2 ?cs2 |- _ => tc1_orig_rw segs m a bs H A2 cs2
  | H : ro_cells segs m ?A2 ?cs2 |- _ => tc1_orig_ro segs m a bs H A2 cs2
  | H : u8arr segs m ?A2 ?xs |- _ => tc1_orig_u8 segs m a bs H A2 xs
  | H : u32arr segs m ?A2 ?xs |- _ => tc1_orig_u32 segs m a bs H A2 xs
  | H : u64arr segs m ?A2 ?xs |- _ => tc1_orig_u64 segs m a bs H A2 xs
  | H : u8ro segs m ?A2 ?xs |- _ => tc1_orig_u8ro segs m a bs H A2 xs
  end.

Ltac transport_chunks_n8 segs m a bs :=
  first
    [ lazymatch a with
      | (?A + Z.of_nat ?kn)%Z =>
        lazymatch bs with
        | cbytes ?c' =>
          lazymatch goal with
          | HT : rw_cells segs (write_to_mem m (wa a) bs) A ?csT |- _ =>
              let S := dj_size_cells csT in
              is_Zlit S;
              let ES := fresh "TCs" in let HK := fresh "TCk" in
              assert (ES : Z.of_nat (cells_size csT) = S) by reflexivity;
              assert (HK : (Z.of_nat kn + Z.of_nat (csize c') <=? S) = true) by reflexivity;
              transport_chunks_dj segs m a bs (write_to_mem m (wa a) bs) A csT S kn c' HT ES HK;
              clear ES HK
          end
        end
      end
    | transport_chunks_orig segs m a bs ].
