(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import MState Mem Cells Exec Step Frame Arr Tac StoreFast NoCast.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Lemma sfz_store_range : forall A S z n : Z,
  (0 <= A /\ A + S <= 2^64) -> ((0 <=? z) && (z + n <=? S))%bool = true ->
  0 <= A + z /\ A + z + n <= 2^64.
Proof.
  intros A S z n [H0 H1] Hb. apply andb_true_iff in Hb. destruct Hb as [Hz Hn].
  apply Z.leb_le in Hz. apply Z.leb_le in Hn. split; lia.
Qed.

(* [comment removed for export] *)
Ltac store_facts_z HB A z bs k :=
  let Hn := fresh "Hn_st" in let Ha := fresh "Ha_st" in let Hl := fresh "Hl_st" in
  let n0 := constr:(Z.of_nat (@length byte bs)) in
  let n1 := eval cbv [length app cbytes cells_bytes le8 le4 le2 le1 word_to_le_bytes Z_to_le_bytes
                      Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in n0 in
  let n := lazymatch n1 with Zpos _ => n1 | Z0 => n1 | _ => n0 end in
  first [ assert (Hn : Z.of_nat (@length byte bs) = n) by exact eq_refl
        | fail "store_facts: length of" bs "vs" n ];
  sf_hide_poison;
  first [ lazymatch type of HB with
          | (0 <= A /\ A + ?S <= _) =>
              lazymatch S with Zpos _ => idtac | Z0 => idtac end;
              lazymatch n with Zpos _ => idtac | Z0 => idtac end;
              pose proof (proj1 (sfz_store_range A S z n HB (@eq_refl bool true))) as Ha;
              pose proof (proj2 (sfz_store_range A S z n HB (@eq_refl bool true))) as Hl
          end
        | first [ assert (Ha : (0 <= A + z)) by tlia | sf_unhide; fail "store_facts: 0 <=" A "+" z ];
          first [ assert (Hl : (A + z + n <= 2^64))
                    by first [ tlia | rewrite <- Hn; simpl_sizes; rewrite ?u32s_length, ?u64s_length, ?upd_length; tlia ]
                | sf_unhide; fail "store_facts:" A "+" z "+" n "<= 2^64" ] ];
  k n Hn Ha Hl;
  clear Hn Ha Hl; sf_unhide.

(* [comment removed for export] *)
Ltac is_nat_lit n := lazymatch n with O => idtac | S ?m => is_nat_lit m end.
Ltac zlit_of_nat_in H :=
  repeat match type of H with
  | context [Z.of_nat ?N] =>
      is_nat_lit N;
      let v := eval cbv in (Z.of_nat N) in
      lazymatch v with Zpos _ => idtac | Z0 => idtac end;
      change (Z.of_nat N) with v in H
  end.

(* [comment removed for export] *)
Ltac mem_after_store_fastz :=
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
            transport_chunks_with segs m (A + z)%Z (cbytes c') n' Hn Ha Hl;
            footprint_after_store_with segs m (A + z)%Z (cbytes c') n' Hn Ha Hl);
          let m' := fresh "m" in
          remember (write_to_mem m (wa (A + z)) (cbytes c')) as m' eqn:Heqm;
          clear Heqm; clear HB; try clear m; try rename H' into H
        end
    end
  end.
