(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import MState Mem Cells Exec Step Frame Arr Tac StoreFast StoreFastZ NoCast.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Inductive sf_dj (lo2 hi2 lo1 hi1 : Z) : Prop := SfDj : (hi2 <= lo1 \/ hi1 <= lo2) -> sf_dj lo2 hi2 lo1 hi1.
Inductive sf_dj_no (lo2 hi2 lo1 hi1 : Z) : Prop := SfDjNo : sf_dj_no lo2 hi2 lo1 hi1.

Lemma sf_dj_use : forall lo2 hi2 A S z n : Z,
  sf_dj lo2 hi2 A (A + S) -> ((0 <=? z) && (z + n <=? S))%bool = true ->
  hi2 <= A + z \/ A + z + n <= lo2.
Proof.
  intros lo2 hi2 A S z n [D] Hb. apply andb_true_iff in Hb. destruct Hb as [Hz Hn].
  apply Z.leb_le in Hz. apply Z.leb_le in Hn. lia.
Qed.

(* [comment removed for export] *)
Lemma sf_dj_lit : forall A2 A X c2 c s2 z n : Z,
  A2 = X + c2 -> A = X + c -> ((c2 + s2 <=? c + z) || (c + z + n <=? c2))%bool = true ->
  A2 + s2 <= A + z \/ A + z + n <= A2.
Proof.
  intros A2 A X c2 c s2 z n -> -> Hb. apply orb_true_iff in Hb. destruct Hb as [H|H]; apply Z.leb_le in H; lia.
Qed.
Lemma sf_in_lit : forall lo hi A X l h c z n : Z,
  lo = X + l -> hi = X + h -> A = X + c -> ((l <=? c + z) && (c + z + n <=? h))%bool = true ->
  lo <= A + z /\ A + z + n <= hi.
Proof.
  intros lo hi A X l h c z n -> -> -> Hb. apply andb_true_iff in Hb. destruct Hb as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.
Lemma sf_base_0 : forall X : Z, X = X + 0. Proof. intros; symmetry; apply Z.add_0_r. Qed.

Ltac sfc_is_lit c := lazymatch c with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.
(* [comment removed for export] *)
Ltac sfc_split_addr t k :=
  lazymatch t with
  | (?X + ?c)%Z => first [ sfc_is_lit c; k X c (@eq_refl Z t) | k t 0%Z (sf_base_0 t) ]
  | _ => first [ sfc_is_lit t; k 0%Z t (@eq_refl Z t) | k t 0%Z (sf_base_0 t) ]
  end.
(* [comment removed for export] *)
Ltac sfc_dj_lit A2 s2 A z n :=
  sfc_is_lit s2;
  sfc_split_addr A2 ltac:(fun X2 c2 p2 =>
  sfc_split_addr A ltac:(fun X c p =>
    constr_eq X2 X;
    exact (sf_dj_lit A2 A X c2 c s2 z n p2 p (@eq_refl bool true)))).
(* [comment removed for export] *)
Ltac sfc_in_lit A z n :=
  cbn [inside];
  repeat first
    [ lazymatch goal with
      | |- (?lo <= _ /\ _ <= ?hi)%Z \/ _ =>
          left;
          sfc_split_addr lo ltac:(fun Xl l pl => sfc_split_addr hi ltac:(fun Xh h ph => sfc_split_addr A ltac:(fun X c p =>
            constr_eq Xl X; constr_eq Xh X;
            exact (sf_in_lit lo hi A X l h c z n pl ph p (@eq_refl bool true)))))
      end
    | right ].

(* [comment removed for export] *)
Ltac sfc_chunk_hi A2 cs2 :=
  let e := constr:(Z.of_nat (cells_size cs2)) in
  let v := eval cbv [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in e in
  lazymatch v with
  | Zpos _ => constr:(A2 + v)
  | Z0 => constr:(A2 + v)
  | _ => constr:(A2 + e)
  end.

Ltac sfc_chunk_size cs2 :=
  let e := constr:(Z.of_nat (cells_size cs2)) in
  eval cbv [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in e.

(* [comment removed for export] *)
Ltac sfc_ensure lo2 hi2 A S :=
  lazymatch goal with
  | _ : sf_dj lo2 hi2 A (A + S) |- _ => idtac
  | _ : sf_dj_no lo2 hi2 A (A + S) |- _ => idtac
  | _ =>
      let D := fresh "sfdj" in
      first [ assert (D : sf_dj lo2 hi2 A (A + S)) by (apply SfDj; simpl_sizes_goal; sf_arr_sizes; tslia)
            | pose proof (SfDjNo lo2 hi2 A (A + S)) as D ]
  end.

(* [comment removed for export] *)
Ltac sfc_side lo2 hi2 A S z n :=
  first [ lazymatch goal with D : sf_dj lo2 hi2 A (A + S) |- _ => exact (sf_dj_use lo2 hi2 A S z n D (@eq_refl bool true)) end
        | simpl_sizes_goal; sf_arr_sizes; tslia ].
Ltac sfc_side_in A z n := first [ solve [ sfc_in_lit A z n ] | cbn [inside]; tslia ].

(* [comment removed for export] *)
Ltac transport_chunks_cached segs m A S z bs n Hn Ha Hl :=
  (repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      let hi := constr:(A2 + Z.of_nat (length bs2)) in sfc_ensure A2 hi A S;
      first [ apply (bytes_at_write_other_n segs m (A + z) bs A2 bs2 n Hn Ha Hl) in H; [ | sfc_side A2 hi A S z n ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_write segs m A2 n2 (wa (A + z)) bs) in H
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ (* [comment removed for export] *)
              let s2 := sfc_chunk_size cs2 in
              apply (rw_cells_frame_n segs m A2 cs2 (A + z) bs n Hn Ha Hl) in H; [ | sfc_dj_lit A2 s2 A z n ]
            | let hi := sfc_chunk_hi A2 cs2 in sfc_ensure A2 hi A S;
              apply (rw_cells_frame_n segs m A2 cs2 (A + z) bs n Hn Ha Hl) in H; [ | sfc_side A2 hi A S z n ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ (* [comment removed for export] *)
              let s2 := sfc_chunk_size cs2 in
              apply (ro_cells_frame_n segs m A2 cs2 (A + z) bs n Hn Ha Hl) in H; [ | sfc_dj_lit A2 s2 A z n ]
            | let hi := sfc_chunk_hi A2 cs2 in sfc_ensure A2 hi A S;
              apply (ro_cells_frame_n segs m A2 cs2 (A + z) bs n Hn Ha Hl) in H; [ | sfc_side A2 hi A S z n ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      let hi := constr:(A2 + Z.of_nat (length xs)) in sfc_ensure A2 hi A S;
      first [ apply (u8arr_frame_n segs m A2 xs (A + z) bs n Hn Ha Hl) in H; [ | sfc_side A2 hi A S z n ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      let hi := constr:(A2 + 4 * Z.of_nat (length xs)) in sfc_ensure A2 hi A S;
      first [ apply (u32arr_frame_n segs m A2 xs (A + z) bs n Hn Ha Hl) in H; [ | sfc_side A2 hi A S z n ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      let hi := constr:(A2 + 8 * Z.of_nat (length xs)) in sfc_ensure A2 hi A S;
      first [ apply (u64arr_frame_n segs m A2 xs (A + z) bs n Hn Ha Hl) in H; [ | sfc_side A2 hi A S z n ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      let hi := constr:(A2 + Z.of_nat (length xs)) in sfc_ensure A2 hi A S;
      first [ apply (u8ro_frame_n segs m A2 xs (A + z) bs n Hn Ha Hl) in H; [ | sfc_side A2 hi A S z n ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  end);
  transport_chunks_extra m (A + z) bs n Hn Ha Hl.

Ltac footprint_after_store_cached segs m A S z bs n Hn Ha Hl :=
  repeat match goal with
  | MU : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_write_n Wq mq m (A + z) bs n Hn Ha Hl) in MU; [ | sfc_side_in A z n ]
            | fail 100 "store outside the declared footprint:" A z ]
  | WMo : wmono segs ?mq m |- _ => apply (wmono_write segs mq m (wa (A + z)) bs) in WMo
  | STq : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_write_n segs m loq hiq (A + z) bs n Hn Ha Hl) in STq
            | fail 100 "cannot transport stk hypothesis" STq ]
  end.

(* [comment removed for export] *)
Ltac mem_after_store_fastzc :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
    let z := eval cbv in (Z.of_nat kn) in
    lazymatch z with Z0 => idtac | Zpos _ => idtac end;
    let c' := cell_of_bytes bs in
    let n := eval cbv in (csize c') in
    lazymatch goal with
    | H : rw_cells segs m A ?cs0 |- _ =>
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          let HB := fresh "HB" in
          pose proof (rw_cells_bound segs m A cs H) as HB; literal_cell_sizes_in HB; cbn [cells_size csize Nat.add] in HB;
          zlit_of_nat_in HB;
          let S := lazymatch type of HB with (0 <= A /\ A + ?S <= _) => S end in
          lazymatch S with Zpos _ => idtac | Z0 => idtac end;
          try lazymatch goal with
          | HI : mem_inv segs m |- _ =>
              apply (mem_inv_store_cbytes segs m (wa (A + Z.of_nat kn)) c') in HI;
              [ change (Z.of_nat kn) with z in HI
              | exact I | apply (rw_cells_store_ok segs m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
          end;
          nocast (change (write_to_mem m (wa (A + Z.of_nat kn)) bs) with (write_to_mem m (wa (A + z)) (cbytes c')));
          let H' := fresh "CH" in
          pose proof (rw_cells_write segs m A cs kn c0 c' H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
          clear H;
          cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
          change (Z.of_nat kn) with z in H';
          store_facts_z HB A z (cbytes c') ltac:(fun n' Hn Ha Hl =>
            transport_chunks_cached segs m A S z (cbytes c') n' Hn Ha Hl;
            footprint_after_store_cached segs m A S z (cbytes c') n' Hn Ha Hl);
          let m' := fresh "m" in
          remember (write_to_mem m (wa (A + z)) (cbytes c')) as m' eqn:Heqm;
          clear Heqm; clear HB; try clear m; try rename H' into H
        end
    end
  end.
