(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr.
Import ListNotations.
Open Scope Z_scope.

Definition hidden (P : Prop) : Prop := P.
Ltac hide H := lazymatch type of H with ?T => change (hidden T) in H end.
Ltac unhide := repeat match goal with H : hidden _ |- _ => unfold hidden in H end.
Ltac hide_all_disj := repeat match goal with H : _ \/ _ |- _ => hide H end.
Ltac hide_not_mentioning1 X :=
  repeat match goal with
         | H : ?P \/ ?Q |- _ =>
             lazymatch P with context [X] => fail | _ => lazymatch Q with context [X] => fail | _ => hide H end end
         end.
(* [comment removed for export] *)
Ltac base_of A := lazymatch A with ?X + _ => base_of X | ?X - _ => base_of X | _ => A end.
(* [comment removed for export] *)
Ltac unhide_related X Y :=
  hide_all_disj;
  first [ constr_eq X Y
        | repeat match goal with
                 | H : hidden (?P \/ ?Q) |- _ =>
                     lazymatch constr:((P, Q)) with
                     | context [X] => lazymatch constr:((P, Q)) with context [Y] => unfold hidden in H end
                     end
                 end ].
Ltac unhide_mentioning X :=
  hide_all_disj;
  repeat match goal with
         | H : hidden (?P \/ ?Q) |- _ => lazymatch constr:((P, Q)) with context [X] => unfold hidden in H end
         end.
(* [comment removed for export] *)
Ltac hide_unrelated X Y := unhide_related X Y.

(* [comment removed for export] *)
Ltac dj_range X :=
  lazymatch goal with
  | |- True => exact I
  | |- _ <= ?l \/ _ => let Y := base_of l in unhide_related X Y; slia
  | |- _ => slia
  end.
Ltac dj_ranges X := cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; repeat split; dj_range X.

Ltac transport_chunks_hide segs m a bs :=
  let Y := base_of a in
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      let X := base_of A2 in unhide_related X Y;
      first [ apply (bytes_at_write_other segs m a bs A2 bs2) in H; [ hide_all_disj | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
            | hide_all_disj; idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_write segs m A2 n2 (wa a) bs) in H
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      let X := base_of A2 in unhide_related X Y;
      first [ apply (rw_cells_frame segs m A2 cs2 a bs) in H; [ hide_all_disj | lia | simpl_sizes; slia | simpl_sizes; slia ]
            | hide_all_disj; idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      let X := base_of A2 in unhide_related X Y;
      first [ apply (ro_cells_frame segs m A2 cs2 a bs) in H; [ hide_all_disj | lia | simpl_sizes; slia | simpl_sizes; slia ]
            | hide_all_disj; idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      let X := base_of A2 in unhide_related X Y;
      first [ apply (u8arr_frame segs m A2 xs a bs) in H; [ hide_all_disj | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
            | hide_all_disj; idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      let X := base_of A2 in unhide_related X Y;
      first [ apply (u32arr_frame segs m A2 xs a bs) in H; [ hide_all_disj | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
            | hide_all_disj; idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      let X := base_of A2 in unhide_related X Y;
      first [ apply (u64arr_frame segs m A2 xs a bs) in H; [ hide_all_disj | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
            | hide_all_disj; idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      let X := base_of A2 in unhide_related X Y;
      first [ apply (u8ro_frame segs m A2 xs a bs) in H; [ hide_all_disj | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
            | hide_all_disj; idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  end.

Ltac footprint_after_store_hide segs m a bs :=
  let Y := base_of a in
  repeat match goal with
  | MU : munch ?Wq ?mq m |- _ =>
      hide_all_disj;
      first [ apply (munch_write Wq mq m a bs) in MU; [ hide_all_disj | lia | simpl_sizes; slia | cbn [inside]; simpl_sizes; slia ]
            | unhide_mentioning Y; apply (munch_write Wq mq m a bs) in MU; [ hide_all_disj | lia | simpl_sizes; slia | cbn [inside]; simpl_sizes; slia ]
            | fail 100 "store outside the declared footprint:" a ]
  | WMo : wmono segs ?mq m |- _ => apply (wmono_write segs mq m (wa a) bs) in WMo
  | STq : stk segs m ?loq ?hiq |- _ =>
      hide_all_disj;
      first [ apply (stk_write segs m loq hiq a bs) in STq; [ hide_all_disj | lia | simpl_sizes; slia ]
            | let L := base_of loq in unhide_related Y L; apply (stk_write segs m loq hiq a bs) in STq; [ hide_all_disj | lia | simpl_sizes; slia ]
            | fail 100 "cannot transport stk hypothesis" STq ]
  end.

Ltac transport_after_call_hide segs m m' MU WM :=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      let X := base_of A2 in
      first [ apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | dj_ranges X; fail ]; hide_all_disj
            | hide_all_disj; idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      let X := base_of A2 in
      first [ apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | dj_ranges X; fail ]; hide_all_disj
            | hide_all_disj; idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      let X := base_of A2 in
      first [ apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | dj_ranges X; fail ]; hide_all_disj
            | hide_all_disj; idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      let X := base_of A2 in
      first [ apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | dj_ranges X; fail ]; hide_all_disj
            | hide_all_disj; idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      let X := base_of A2 in
      first [ apply (u32arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | dj_ranges X; fail ]; hide_all_disj
            | hide_all_disj; idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      let X := base_of A2 in
      first [ apply (u64arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | dj_ranges X; fail ]; hide_all_disj
            | hide_all_disj; idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      let X := base_of A2 in
      first [ apply (u8ro_transport segs W m m' A2 xs) in H; [ | exact MU | dj_ranges X; fail ]; hide_all_disj
            | hide_all_disj; idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : stk segs m ?loq ?hiq |- _ =>
      let X := base_of loq in
      first [ apply (stk_transport_disjoint segs W m m' loq hiq) in H; [ | exact MU | exact WM | dj_ranges X; fail ]; hide_all_disj
            | hide_all_disj; clear H ]
  | H : munch ?Wq ?mq m |- _ =>
      hide_all_disj;
      first [ apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ unfold sub_fp; cbn [outside]; intros; slia | exact MU ] ]
            | fail 100 "callee footprint not inside caller footprint" ]
  | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
  end.

(* [comment removed for export] *)
Ltac sep_solve :=
  lazymatch goal with
  | |- ?L <= ?B \/ _ => let X := base_of L in let Y := base_of B in unhide_related X Y; lia
  end.
