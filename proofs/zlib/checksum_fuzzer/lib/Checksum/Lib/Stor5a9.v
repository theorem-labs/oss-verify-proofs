(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac Storrsf DietLia2 TacDiet2.
From Ltac2 Require Ltac2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope bv_scope.

(* [comment removed for export] *)
Ltac sd_side side := idtac; side ltac:(idtac; simpl_sizes_goal) ltac:(idtac; diet_note_fb; simpl_sizes_goal; tslia).
Ltac sd_disjoint_goal side :=
  idtac; side ltac:(idtac; cbv [disjoint_from fst snd]; simpl_sizes_goal) ltac:(idtac; diet_note_fb; disjoint_goal).

(* [comment removed for export] *)
Ltac sd_store_facts ws a bs k :=
  let Hn := fresh "Hn_st" in let Ha := fresh "Ha_st" in let Hl := fresh "Hl_st" in
  let n0 := constr:(Z.of_nat (@length byte bs)) in
  let n1 := eval cbv [length app cbytes cells_bytes le8 le4 le2 le1 word_to_le_bytes Z_to_le_bytes
                      Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in n0 in
  let n := lazymatch n1 with Zpos _ => n1 | Z0 => n1 | _ => n0 end in
  first [ assert (Hn : Z.of_nat (@length byte bs) = n) by exact eq_refl
        | fail "store_facts: length of" bs "vs" n ];
  sf_hide_poison;
  ws ltac:(fun side side_ns side_dm =>
    first [ assert (Ha : (0 <= a)%Z) by (idtac; side_ns ltac:(idtac) ltac:(idtac; tlia)) | sf_unhide; fail "store_facts: 0 <=" a ];
    first [ assert (Hl : (a + n <= 2^64)%Z)
              by (idtac; side_ns ltac:(idtac)
                    ltac:(idtac; first [ tlia | rewrite <- Hn; simpl_sizes; rewrite ?u32s_length, ?u64s_length, ?upd_length; tlia ]))
          | sf_unhide; fail "store_facts:" a "+" n "<= 2^64" ];
    (* [comment removed for export] *)
    let Hl' := fresh "dHl" in
    assert (Hl' : (a + Z.of_nat (@length byte bs) <= 2^64)%Z) by (rewrite Hn; exact Hl);
    store_ctx_of_facts true a bs Ha Hl' ltac:(sd_side side)
      ltac:(fun SC X b => k n Hn Ha Hl SC X b side side_ns);
    clear Hl');
  clear Hn Ha Hl; sf_unhide.

Ltac sd_transport_chunks_with segs m a bs n Hn Ha Hl SC X b side :=
  (repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ tr_lit H (bytes_at_write_other_lit segs m a bs X b A2 bs2 SC) b A2 constr:(Z.of_nat (@length byte bs2))
            | tr_sb H (bytes_at_write_other_sb segs m a bs X b) (bytes_at_write_other_sb0 segs m a bs X b) chk_sb b X A2 constr:(Z.of_nat (@length byte bs2))
            | apply (bytes_at_write_other_n segs m a bs A2 bs2 n Hn Ha Hl) in H; [ | sd_side side ]; diet_note_h
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_write segs m A2 n2 (wa a) bs) in H
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ tr_lit H (rw_cells_frame_lit segs m a bs X b A2 cs2 SC) b A2 constr:(Z.of_nat (cells_size cs2))
            | tr_sb H (rw_cells_frame_sb segs m a bs X b) (rw_cells_frame_sb0 segs m a bs X b) chk_sb b X A2 constr:(Z.of_nat (cells_size cs2))
            | apply (rw_cells_frame_n segs m A2 cs2 a bs n Hn Ha Hl) in H; [ | sd_side side ]; diet_note_h
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ tr_lit H (ro_cells_frame_lit segs m a bs X b A2 cs2 SC) b A2 constr:(Z.of_nat (cells_size cs2))
            | tr_sb H (ro_cells_frame_sb segs m a bs X b) (ro_cells_frame_sb0 segs m a bs X b) chk_sb b X A2 constr:(Z.of_nat (cells_size cs2))
            | apply (ro_cells_frame_n segs m A2 cs2 a bs n Hn Ha Hl) in H; [ | sd_side side ]; diet_note_h
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ tr_lit H (u8arr_frame_lit segs m a bs X b A2 xs SC) b A2 constr:(Z.of_nat (@length byte xs))
            | tr_sb H (u8arr_frame_sb segs m a bs X b) (u8arr_frame_sb0 segs m a bs X b) chk_sb b X A2 constr:(Z.of_nat (@length byte xs))
            | apply (u8arr_frame_n segs m A2 xs a bs n Hn Ha Hl) in H; [ | sd_side side ]; diet_note_h
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ tr_lit H (u32arr_frame_lit segs m a bs X b A2 xs SC) b A2 constr:((4 * Z.of_nat (@length word xs))%Z)
            | tr_sb H (u32arr_frame_sb segs m a bs X b) (u32arr_frame_sb0 segs m a bs X b) chk_sb b X A2 constr:((4 * Z.of_nat (@length word xs))%Z)
            | apply (u32arr_frame_n segs m A2 xs a bs n Hn Ha Hl) in H; [ | sd_side side ]; diet_note_h
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ tr_lit H (u64arr_frame_lit segs m a bs X b A2 xs SC) b A2 constr:((8 * Z.of_nat (@length word xs))%Z)
            | tr_sb H (u64arr_frame_sb segs m a bs X b) (u64arr_frame_sb0 segs m a bs X b) chk_sb b X A2 constr:((8 * Z.of_nat (@length word xs))%Z)
            | apply (u64arr_frame_n segs m A2 xs a bs n Hn Ha Hl) in H; [ | sd_side side ]; diet_note_h
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ tr_lit H (u8ro_frame_lit segs m a bs X b A2 xs SC) b A2 constr:(Z.of_nat (@length byte xs))
            | tr_sb H (u8ro_frame_sb segs m a bs X b) (u8ro_frame_sb0 segs m a bs X b) chk_sb b X A2 constr:(Z.of_nat (@length byte xs))
            | apply (u8ro_frame_n segs m A2 xs a bs n Hn Ha Hl) in H; [ | sd_side side ]; diet_note_h
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  end);
  transport_chunks_extra m a bs n Hn Ha Hl.


Ltac sd_footprint_after_store_with segs m a bs n Hn Ha Hl side_ns :=
  repeat match goal with
  | MU : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_write_n Wq mq m a bs n Hn Ha Hl) in MU;
              [ | idtac; side_ns ltac:(idtac; cbn [inside]) ltac:(idtac; diet_note_fb; cbn [inside]; tslia) ]
            | fail 100 "store outside the declared footprint:" a ]
  | WMo : wmono segs ?mq m |- _ => apply (wmono_write segs mq m (wa a) bs) in WMo
  | STq : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_write_n segs m loq hiq a bs n Hn Ha Hl) in STq
            | fail 100 "cannot transport stk hypothesis" STq ]
  end.


Ltac sd_transport_chunks_ws ws segs m a bs :=
  sd_store_facts ws a bs ltac:(fun n Hn Ha Hl SC X b side side_ns => sd_transport_chunks_with segs m a bs n Hn Ha Hl SC X b side).
Ltac sd_footprint_after_store_ws ws segs m a bs :=
  sd_store_facts ws a bs ltac:(fun n Hn Ha Hl SC X b side side_ns => sd_footprint_after_store_with segs m a bs n Hn Ha Hl side_ns).

Ltac sd_mem_after_store_new ws :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
    let c' := cell_of_bytes bs in
    let n := eval cbv in (csize c') in
    lazymatch goal with
    | H : rw_cells segs m A ?cs0 |- _ =>
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          let HB := fresh "HB" in
          first [ OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.TacDiet2.natz_pose_bound segs m A cs H HB
                | pose proof (rw_cells_bound segs m A cs H) as HB; literal_cell_sizes_in HB; cbn [cells_size csize Nat.add] in HB ];
          try lazymatch goal with
          | HI : mem_inv segs m |- _ =>
              apply (mem_inv_store_cbytes segs m (wa (A + Z.of_nat kn)) c') in HI;
              [ | exact I | apply (rw_cells_store_ok segs m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
          end;
          change bs with (cbytes c');
          let H' := fresh "CH" in
          pose proof (rw_cells_write segs m A cs kn c0 c' H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
          clear H;
          cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
          sd_store_facts ws (A + Z.of_nat kn)%Z (cbytes c') ltac:(fun n' Hn Ha Hl SC X b side side_ns =>
            sd_transport_chunks_with segs m (A + Z.of_nat kn)%Z (cbytes c') n' Hn Ha Hl SC X b side;
            sd_footprint_after_store_with segs m (A + Z.of_nat kn)%Z (cbytes c') n' Hn Ha Hl side_ns);
          let m' := fresh "m" in
          remember (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) as m' eqn:Heqm;
          clear Heqm; clear HB; try clear m; try rename H' into H
        end
    end
  end.


Ltac sd_transport_after_call_new ws segs m m' MU WM :=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  sf_hide_poison;
  ws ltac:(fun side side_ns side_dm => repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | sd_disjoint_goal side ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | sd_disjoint_goal side ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | sd_disjoint_goal side ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | sd_disjoint_goal side ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (u32arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | sd_disjoint_goal side ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | sd_disjoint_goal side ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (u8ro_transport segs W m m' A2 xs) in H; [ | exact MU | sd_disjoint_goal side ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_transport_disjoint segs W m m' loq hiq) in H; [ | exact MU | exact WM | sd_disjoint_goal side ]
            | clear H ]
  | H : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_trans Wq mq m m') in H;
              [ | eapply (munch_weaken W Wq m m');
                [ unfold sub_fp; cbn [outside];
                  (* [comment removed for export] *)
                  first [ intros; Zify.zify; xlia zchecker
                        | sf_unhide; zify_prune_plain; intros; Zify.zify; xlia zchecker
                        | intros; tslia ]
                | exact MU ] ]
            | fail 100 "callee footprint not inside caller footprint" ]
  | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
  end);
  transport_call_extra segs W m m' MU WM;
  sf_unhide.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac sd_ws := fun k => diet_with_side k.
Ltac sd_transport_chunks segs m a bs :=
  diet_dispatch_chunks ltac:(idtac; sd_transport_chunks_ws sd_ws segs m a bs) ltac:(idtac; transport_chunks_fast segs m a bs).
Ltac sd_footprint_after_store segs m a bs :=
  diet_dispatch_fp ltac:(idtac; sd_footprint_after_store_ws sd_ws segs m a bs) ltac:(idtac; footprint_after_store_fast segs m a bs).
Ltac sd_mem_after_store :=
  diet_dispatch_store ltac:(idtac; sd_mem_after_store_new sd_ws) ltac:(idtac; mem_after_store_fast).
Ltac sd_transport_after_call segs m m' MU WM :=
  diet_dispatch_call ltac:(idtac; sd_transport_after_call_new sd_ws segs m m' MU WM)
                     ltac:(idtac; transport_after_call_fast segs m m' MU WM).
