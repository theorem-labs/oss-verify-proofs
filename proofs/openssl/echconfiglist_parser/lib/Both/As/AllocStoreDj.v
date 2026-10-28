(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr CellsX TacX Frame StoreDj.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AllocTacX.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Ltac dj_ensure_rx A2 s2 A S :=
  lazymatch goal with
  | _ : chunk_disj A2 s2 A S |- _ => idtac
  | _ : chunk_nodj A2 s2 A S |- _ => idtac
  | _ => let DJ := fresh "DJc" in
         first [ assert (DJ : chunk_disj A2 s2 A S) by (unfold chunk_disj; simpl_sizes; rx_arr_sizes; region_decide)
               | pose proof (I : chunk_nodj A2 s2 A S) as DJ ]
  end.
Ltac in_ensure_rx W A S :=
  lazymatch goal with
  | _ : chunk_in W A S |- _ => idtac
  | _ : chunk_noin W A S |- _ => idtac
  | _ => let DJ := fresh "INc" in
         first [ assert (DJ : chunk_in W A S) by (unfold chunk_in; simpl_sizes; region_inside)
               | pose proof (I : chunk_noin W A S) as DJ ]
  end.

(* [comment removed for export] *)
Ltac tc1_rx segs m a bs H HA HL lem :=
  first [ apply lem in H; [ | first [exact HA | lia] | rx_exactL HL | simpl_sizes; rx_arr_sizes; region_decide ]
        | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ].

Ltac transport_chunks_dj_rx segs m a bs mT A csT S kn c' HT ES HK HA HL :=
  repeat match goal with
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      let s2 := dj_size_cells cs2 in
      dj_ensure_rx A2 s2 A S;
      lazymatch goal with
      | DJ : chunk_disj A2 s2 A S |- _ =>
          apply (rw_cells_frame_dj segs mT A csT S kn c' m A2 cs2 s2 HT ES HK I (@eq_refl Z s2) DJ) in H
      | _ => tc1_rx segs m a bs H HA HL (rw_cells_frame segs m A2 cs2 a bs)
      end
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      let s2 := dj_size_cells cs2 in
      dj_ensure_rx A2 s2 A S;
      lazymatch goal with
      | DJ : chunk_disj A2 s2 A S |- _ =>
          apply (ro_cells_frame_dj segs mT A csT S kn c' m A2 cs2 s2 HT ES HK I (@eq_refl Z s2) DJ) in H
      | _ => tc1_rx segs m a bs H HA HL (ro_cells_frame segs m A2 cs2 a bs)
      end
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      let s2 := dj_size_len (Z.of_nat (length bs2)) bs2 in
      dj_ensure_rx A2 s2 A S;
      lazymatch goal with
      | DJ : chunk_disj A2 s2 A S |- _ =>
          apply (bytes_at_frame_dj segs mT A csT S kn c' m A2 bs2 s2 HT ES HK I (@eq_refl Z s2) DJ) in H
      | _ => tc1_rx segs m a bs H HA HL (bytes_at_write_other segs m a bs A2 bs2)
      end
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_write segs m A2 n2 (wa a) bs) in H
  | H : u8arr segs m ?A2 ?xs |- _ =>
      let s2 := dj_size_len (Z.of_nat (length xs)) xs in
      dj_ensure_rx A2 s2 A S;
      lazymatch goal with
      | DJ : chunk_disj A2 s2 A S |- _ =>
          apply (u8arr_frame_dj segs mT A csT S kn c' m A2 xs s2 HT ES HK I (@eq_refl Z s2) DJ) in H
      | _ => tc1_rx segs m a bs H HA HL (u8arr_frame segs m A2 xs a bs)
      end
  | H : u32arr segs m ?A2 ?xs |- _ =>
      let s2 := dj_size_len (4 * Z.of_nat (length xs)) xs in
      dj_ensure_rx A2 s2 A S;
      lazymatch goal with
      | DJ : chunk_disj A2 s2 A S |- _ =>
          apply (u32arr_frame_dj segs mT A csT S kn c' m A2 xs s2 HT ES HK I (@eq_refl Z s2) DJ) in H
      | _ => tc1_rx segs m a bs H HA HL (u32arr_frame segs m A2 xs a bs)
      end
  | H : u64arr segs m ?A2 ?xs |- _ =>
      let s2 := dj_size_len (8 * Z.of_nat (length xs)) xs in
      dj_ensure_rx A2 s2 A S;
      lazymatch goal with
      | DJ : chunk_disj A2 s2 A S |- _ =>
          apply (u64arr_frame_dj segs mT A csT S kn c' m A2 xs s2 HT ES HK I (@eq_refl Z s2) DJ) in H
      | _ => tc1_rx segs m a bs H HA HL (u64arr_frame segs m A2 xs a bs)
      end
  | H : u8ro segs m ?A2 ?xs |- _ =>
      let s2 := dj_size_len (Z.of_nat (length xs)) xs in
      dj_ensure_rx A2 s2 A S;
      lazymatch goal with
      | DJ : chunk_disj A2 s2 A S |- _ =>
          apply (u8ro_frame_dj segs mT A csT S kn c' m A2 xs s2 HT ES HK I (@eq_refl Z s2) DJ) in H
      | _ => tc1_rx segs m a bs H HA HL (u8ro_frame segs m A2 xs a bs)
      end
  | MU : munch ?Wq ?mq m |- _ =>
      in_ensure_rx Wq A S;
      lazymatch goal with
      | IN : chunk_in Wq A S |- _ => apply (munch_write_in segs mT A csT S kn c' Wq mq m HT ES HK I IN) in MU
      | _ => first [ apply (munch_write Wq mq m a bs) in MU; [ | first [exact HA | lia] | rx_exactL HL | simpl_sizes; region_inside ]
                   | fail 100 "store outside the declared footprint:" a ]
      end
  | WMo : wmono segs ?mq m |- _ => apply (wmono_write segs mq m (wa a) bs) in WMo
  | STq : stk segs m ?loq ?hiq |- _ => apply (stk_write_in segs mT A csT S kn c' m loq hiq HT ES HK I) in STq
  end.

(* [comment removed for export] *)
Ltac transport_chunks_rx_orig segs m a bs :=
  let HA := fresh "RXA" in let HL := fresh "RXL" in
  rx_range_facts a bs HA HL;
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_write_other segs m a bs A2 bs2) in H;
              [ | first [exact HA | lia] | rx_exactL HL | simpl_sizes; rx_arr_sizes; region_decide ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_write segs m A2 n2 (wa a) bs) in H
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_frame segs m A2 cs2 a bs) in H;
              [ | first [exact HA | lia] | rx_exactL HL | simpl_sizes; region_decide ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_frame segs m A2 cs2 a bs) in H;
              [ | first [exact HA | lia] | rx_exactL HL | simpl_sizes; region_decide ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_frame segs m A2 xs a bs) in H;
              [ | first [exact HA | lia] | rx_exactL HL | simpl_sizes; rx_arr_sizes; region_decide ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (u32arr_frame segs m A2 xs a bs) in H;
              [ | first [exact HA | lia] | rx_exactL HL | simpl_sizes; rx_arr_sizes; region_decide ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_frame segs m A2 xs a bs) in H;
              [ | first [exact HA | lia] | rx_exactL HL | simpl_sizes; rx_arr_sizes; region_decide ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (u8ro_frame segs m A2 xs a bs) in H;
              [ | first [exact HA | lia] | rx_exactL HL | simpl_sizes; rx_arr_sizes; region_decide ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  end;
  try clear HA; try clear HL.

Ltac transport_chunks_rx8 segs m a bs :=
  region_table;
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
              let HA := fresh "RXA" in let HL := fresh "RXL" in
              rx_range_facts a bs HA HL;
              transport_chunks_dj_rx segs m a bs (write_to_mem m (wa a) bs) A csT S kn c' HT ES HK HA HL;
              clear ES HK; try clear HA; try clear HL
          end
        end
      end
    | transport_chunks_rx_orig segs m a bs ].
