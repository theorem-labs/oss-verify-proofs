(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXStepR KXExec KXSound KXFull KXBridge KXTac KXGo KXMem KXMem2.
Import ListNotations.
Import KXS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac kx_unsnoc l :=
  lazymatch l with
  | @cons _ ?x (@nil _) => constr:((@nil sentry, x))
  | @cons _ ?h ?t => let r := kx_unsnoc t in lazymatch r with (?i, ?x) => constr:((@cons sentry h i, x)) end
  end.

(* [comment removed for export] *)
Ltac kx_chunk_off zs A a :=
  let r := kx_rz zs A in
  lazymatch r with
  | (?l', ?eA) =>
      let same := constr:(ltac:(first [ constr_eq l' zs; exact true | exact false ]) : bool) in
      lazymatch same with
      | true => eval vm_compute in (let sa := zsa eA in
                                    if expr_eqb (a_base sa) (a_base a) then Some (a_off a - a_off sa) else None)
      | false => constr:(@None Z)
      end
  end.

Ltac kx_store_rw segs m E zs Az CELL a :=
  match goal with
  | H : rw_cells segs m ?A ?cs |- _ =>
      let d := kx_chunk_off zs A a in
      lazymatch d with
      | Some ?k =>
          let ok := eval vm_compute in (Z.leb 0 k) in
          lazymatch ok with true => idtac end;
          let cs' := eval cbv beta iota zeta delta [cells_store cb_split_ok cb_split cb_pieces cell_at cell_upd csize Z.to_nat Pos.to_nat Pos.iter_op
                                                     Nat.eqb Nat.ltb Nat.leb Nat.sub Nat.add andb app] in (cells_store cs (Z.to_nat k) CELL) in
          lazymatch cs' with
          | Some ?cs2 =>
              let H' := fresh "KXC" in
              pose proof (kx_rw_cells_storeZ segs m A cs k CELL cs2 H ltac:(reflexivity) I ltac:(vm_compute; discriminate)) as H';
              (* [comment removed for export] *)
              first [ constr_eq Az (A + k)
                    | let HE := fresh "KXAE" in
                      assert (HE : A + k = Az) by kx_lia;
                      rewrite HE in H'; clear HE ];
              clear H; rename H' into H
          end
      end
  end.

Ltac kx_store_u8 segs m Az CELL :=
  match goal with
  | H : u8arr segs m ?A ?bs |- _ =>
      let bs' := fresh "kxbuf" in let H' := fresh "KXU" in let HL := fresh "KXUL" in
      destruct (kx_u8arr_store segs m A bs Az (cbytes CELL) H ltac:(simpl_sizes; kx_lia)) as (bs' & H' & HL);
      clear H; rename H' into H
  end.

Ltac kx_mem_step segs E zs nz KXA KXLF m log :=
  let r := kx_unsnoc log in
  lazymatch r with
  | (?init, SE ?a ?w ?v) =>
      change (mem_denot E m log) with (mem_denot E m (init ++ [SE a w v])) in *;
      rewrite (mem_denot_unroll E m init a w v) in *;
      let KXLF' := fresh "KXLF" in let HA0 := fresh "KXAR" in
      destruct (log_flat_last E init a w v KXLF) as (KXLF' & HA0); clear KXLF; rename KXLF' into KXLF;
      (* [comment removed for export] *)
      let ab := eval cbv in (a_base a) in
      let zb := kx_ez E zs nz ab in
      let off := eval cbv in (a_off a) in
      let HEQ := fresh "KXEQ" in
      (* [comment removed for export] *)
      lazymatch goal with
      | _ : 0 <= zb < 2^64 |- _ => idtac
      | _ => let HRG := fresh "KXRG" in assert (HRG : 0 <= zb < 2^64) by kx_lia
      end;
      assert (HEQ : estart E a = zb + off)
        by (apply (estart_ez zs E a KXA); change (0 <= zb < 2^64); assumption);
      rewrite HEQ in *; clear HEQ;
      (* [comment removed for export] *)
      let W := kx_word E zs nz v in
      let CELL := eval cbv beta iota delta [kx_cell] in (kx_cell w W) in
      let HV := fresh "KXV" in
      assert (HV : kx_sbytes E w v = cbytes CELL)
        by (change (kx_sbytes E w v = cbytes (kx_cell w W)); rewrite kx_cell_bytes; unfold kx_sbytes; f_equal; kx_word_prf E zs KXA v);
      rewrite HV in *; clear HV;
      (* [comment removed for export] *)
      first [ kx_store_rw segs m E zs (zb + off) CELL a
            | kx_store_u8 segs m (zb + off) CELL
            | idtac ];
      lazymatch goal with
      | |- context [write_to_mem m (wa ?Az) (cbytes CELL)] =>
          cbn [Z.of_nat] in HA0;
          transport_chunks segs m Az (cbytes CELL);
          footprint_after_store segs m Az (cbytes CELL);
          let m1 := fresh "m" in
          set (m1 := write_to_mem m (wa Az) (cbytes CELL)) in *; clearbody m1;
          clear HA0
      end
  end.

Ltac kx_mem_loop segs E zs nz KXA KXLF :=
  lazymatch goal with
  | |- context [mem_denot E ?m ?log] =>
      lazymatch log with
      | @nil _ => change (mem_denot E m (@nil sentry)) with m in *
      | _ => kx_mem_step segs E zs nz KXA KXLF m log; kx_mem_loop segs E zs nz KXA KXLF
      end
  | _ => idtac
  end.

Ltac kx_mem_replay :=
  lazymatch goal with
  | |- evt ?segs _ (MS ?R _ _ _ _ (mem_denot ?E ?m ?log) _) =>
      lazymatch goal with
      | KXA : atoms_ok ?zs E, KXLF : log_flat E log |- _ =>
          let nz := kx_len zs in
          (* [comment removed for export] *)
          try match goal with MI0 : mem_inv segs m |- _ => clear MI0 end;
          (* [comment removed for export] *)
          let kxR := fresh "kxR" in
          set (kxR := R);
          kx_mem_loop segs E zs nz KXA KXLF; clear KXLF;
          subst kxR
      end
  | _ => idtac
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac kx_estarts E zs nz KXA :=
  repeat match goal with
  | |- context [estart E ?a] =>
      let ab := eval cbv in (a_base a) in
      let zb := kx_ez E zs nz ab in
      let off := eval cbv in (a_off a) in
      let HEQ := fresh "KXEQ" in
      assert (HEQ : estart E a = zb + off) by (apply (estart_ez zs E a KXA); change (0 <= zb < 2^64); kx_lia);
      rewrite HEQ; clear HEQ
  | |- context [elenZ E (ELit ?z)] =>
      let v := eval vm_compute in (z mod 2^64) in change (elenZ E (ELit z)) with v
  end.

Ltac kx_side_pre :=
  lazymatch goal with
  | KXA : atoms_ok ?zs ?E |- sc_resid _ _ ?E _ =>
      let nz := kx_len zs in
      cbn [sc_resid sc_denot]; unfold flat;
      lazymatch goal with
      | |- rd_ok _ _ _ _ _ => idtac
      | |- store_ok _ _ _ _ = true => idtac
      | _ => kx_estarts E zs nz KXA
      end
  end.

(* [comment removed for export] *)
Ltac kx_z := kx_side_pre; kx_lia.

(* [comment removed for export] *)
Ltac kx_rd_fact segs m H :=
  lazymatch type of H with
  | bytes_at segs m ?A ?bs => constr:(rd_at_bytes_at segs m A bs H)
  | u8arr segs m ?A ?bs => constr:(rd_at_u8arr segs m A bs H)
  | rw_cells segs m ?A ?cs => constr:(rd_at_rw_cells segs m A cs H)
  | ro_cells segs m ?A ?cs => constr:(rd_at_ro_cells segs m A cs H)
  end.
Ltac kx_rd H :=
  kx_side_pre;
  lazymatch goal with
  | KXA : atoms_ok ?zs ?E |- rd_ok ?segs ?m ?E ?a ?n =>
      let nz := kx_len zs in
      let P := kx_rd_fact segs m H in
      eapply (kx_rd_ok segs m E a n _ _ P); kx_estarts E zs nz KXA; simpl_sizes; kx_lia
  end.
Ltac kx_wr H :=
  kx_side_pre;
  lazymatch goal with
  | KXA : atoms_ok ?zs ?E |- store_ok ?segs ?m (adenot ?E ?a) ?n = true =>
      let nz := kx_len zs in
      let P := lazymatch type of H with
               | wr_at segs m _ _ => H
               | u8arr segs m _ _ => constr:(proj2 H)
               | rw_cells segs m _ _ => constr:(proj2 H)
               end in
      eapply (kx_store_ok segs m E a n _ _ P); kx_estarts E zs nz KXA; simpl_sizes; kx_lia
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac kx_rz_old zs T :=
  let r := kx_rz zs T in
  lazymatch r with
  | (?l', ?e) =>
      let same := constr:(ltac:(first [ constr_eq l' zs; exact true | exact false ]) : bool) in
      lazymatch same with true => e end
  end.

(* [comment removed for export] *)
Ltac kx_len_term bs :=
  match goal with
  | HL : Z.of_nat (length bs) = ?n |- _ => constr:((n, HL))
  | _ => constr:((Z.of_nat (length bs), @eq_refl Z (Z.of_nat (length bs))))
  end.

Ltac kx_estart_prf zs E KXA eA A :=
  (* [comment removed for export] *)
  let off := eval vm_compute in (zoff eA) in
  constr:(ltac:(apply (estart_zx zs E eA KXA); [vm_compute; reflexivity | change (0 <= A - off < 2^64); kx_lia]) : estart E (zsa eA) = A).
Ltac kx_elen_prf zs E KXA eN N :=
  constr:(ltac:(apply (elen_zx zs E eN KXA); [vm_compute; reflexivity | change (0 <= N < 2^64); kx_lia]) : elenZ E (zx eN) = N).

(* [comment removed for export] *)
Ltac kx_mem_hyp segs E m log kn zs KXA KXK KXLF H :=
  lazymatch type of H with
  | bytes_at segs m ?A ?bs =>
      let ln := kx_len_term bs in
      lazymatch ln with (?N, ?HL) =>
        let eA := kx_rz_old zs A in let eN := kx_rz_old zs N in
        let ok := eval vm_compute in (log_apart_b kn log (zsa eA) (zx eN)) in
        lazymatch ok with true =>
          let PA := kx_estart_prf zs E KXA eA A in let PN := kx_elen_prf zs E KXA eN N in
          apply (kx_bytes_at_apart segs E m kn KXK log A bs (zsa eA) (zx eN) KXLF ltac:(vm_cast_no_check (@eq_refl bool true)) PA
                   (eq_trans PN (eq_sym HL))) in H
        end
      end
  | u8arr segs m ?A ?bs =>
      let ln := kx_len_term bs in
      lazymatch ln with (?N, ?HL) =>
        let eA := kx_rz_old zs A in let eN := kx_rz_old zs N in
        let PA := kx_estart_prf zs E KXA eA A in let PN := kx_elen_prf zs E KXA eN N in
        let ok := eval vm_compute in (log_apart_b kn log (zsa eA) (zx eN)) in
        lazymatch ok with
        | true =>
            apply (kx_u8arr_apart segs E m kn KXK log A bs (zsa eA) (zx eN) KXLF ltac:(vm_cast_no_check (@eq_refl bool true)) PA
                     (eq_trans PN (eq_sym HL))) in H
        | false =>
            let ok2 := eval vm_compute in (log_u8_b kn log (zsa eA) (zx eN)) in
            lazymatch ok2 with true =>
              let bs' := fresh "kxbuf" in let H' := fresh "KXU" in let HL' := fresh "KXUL" in
              destruct (kx_u8arr_log segs E m kn KXK log A bs (zsa eA) (zx eN) KXLF ltac:(vm_cast_no_check (@eq_refl bool true)) PA
                          (eq_trans PN (eq_sym HL)) H) as (bs' & H' & HL');
              clear H; rename H' into H
            end
        end
      end
  | rw_cells segs m ?A ?cs =>
      let N := eval lazy in (Z.of_nat (cells_size cs)) in
      let eA := kx_rz_old zs A in
      let PA := kx_estart_prf zs E KXA eA A in
      let ok := eval vm_compute in (log_apart_b kn log (zsa eA) (ELit N)) in
      lazymatch ok with
      | true =>
          apply (kx_rw_cells_apart segs E m kn KXK log A cs (zsa eA) (ELit N) KXLF ltac:(vm_cast_no_check (@eq_refl bool true)) PA
                   ltac:(reflexivity)) in H
      | false =>
          let cl := eval vm_compute in (log_class kn (zsa eA) N log) in
          lazymatch cl with
          | Some ?cl0 =>
              let cs' := eval cbv beta iota zeta delta [cells_hits cells_store cb_split_ok cb_split cb_pieces cell_at cell_upd csize kx_cell
                                                         Z.to_nat Pos.to_nat Pos.iter_op Nat.eqb Nat.ltb Nat.leb Nat.sub Nat.add andb app]
                         in (cells_hits E cs log cl0) in
              lazymatch cs' with
              | Some ?cs2 =>
                  let H' := fresh "KXC" in
                  pose proof (proj1 (kx_rw_cells_log segs E m kn KXK log cl0 A cs cs2 (zsa eA) KXLF PA ltac:(vm_compute; reflexivity)
                                       ltac:(vm_cast_no_check (@eq_refl (option (list (option Z))) (Some cl0))) ltac:(reflexivity) H)) as H';
                  clear H; rename H' into H
              end
          end
      end
  | ro_cells segs m ?A ?cs =>
      let N := eval lazy in (Z.of_nat (cells_size cs)) in
      let eA := kx_rz_old zs A in
      let PA := kx_estart_prf zs E KXA eA A in
      let ok := eval vm_compute in (log_apart_b kn log (zsa eA) (ELit N)) in
      lazymatch ok with true =>
        apply (kx_ro_cells_apart segs E m kn KXK log A cs (zsa eA) (ELit N) KXLF ltac:(vm_cast_no_check (@eq_refl bool true)) PA
                 ltac:(reflexivity)) in H
      end
  | wr_at segs m ?A ?N => apply (kx_wr_at_log segs E m log A N) in H
  | stk segs m ?lo ?hi => apply (kx_stk_log segs E m log lo hi KXLF) in H
  | wmono segs ?m0 m => apply (fun X => wmono_trans segs m0 m (mem_denot E m log) X (kx_wmono_log segs E m log)) in H
  end.

(* [comment removed for export] *)
Ltac kx_cells_words E zs nz KXA H log :=
  lazymatch log with
  | @nil _ => idtac
  | @cons _ (SE _ _ ?v) ?rest =>
      try (lazymatch type of H with context [edenot E v] => idtac end;
           let W := kx_word E zs nz v in
           lazymatch W with context [edenot E v] => fail | _ => idtac end;
           let HV := fresh "KXV" in
           assert (HV : edenot E v = W) by kx_word_prf E zs KXA v;
           rewrite HV in H; clear HV);
      kx_cells_words E zs nz KXA H rest
  end.

(* [comment removed for export] *)
Ltac kx_wins zs W :=
  lazymatch W with
  | @nil _ => constr:(@nil (saddr * expr))
  | @cons _ (?lo, ?hi) ?rest =>
      let elo := kx_rz_old zs lo in let en := kx_rz_old zs (hi - lo) in
      let r := kx_wins zs rest in constr:(@cons (saddr * expr) (zsa elo, zx en) r)
  end.
Ltac kx_wins_ok zs E KXA W :=
  lazymatch goal with
  | |- Forall _ (@nil _) => apply Forall_nil
  | |- Forall _ (@cons _ _ _) =>
      lazymatch W with
      | @cons _ (?lo, ?hi) ?rest =>
          let elo := kx_rz_old zs lo in let en := kx_rz_old zs (hi - lo) in
          let PA := kx_estart_prf zs E KXA elo lo in let PN := kx_elen_prf zs E KXA en (hi - lo) in
          apply Forall_cons;
          [ exists lo, hi; split; [ cbn [In]; auto 20 | split; [ exact PA | cbn [fst snd]; rewrite PA, PN; lia ] ]
          | kx_wins_ok zs E KXA rest ]
      end
  end.

(* [comment removed for export] *)
Ltac kx_log_apart E zs nz KXA :=
  cbn [log_apart]; repeat split; kx_estarts E zs nz KXA; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; simpl_sizes; kx_lia.
Ltac kx_log_u8P E zs nz KXA :=
  cbn [log_u8P]; repeat split; kx_estarts E zs nz KXA; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; simpl_sizes; kx_lia.
Ltac kx_log_inside E zs nz KXA :=
  cbn [log_inside inside]; repeat split; kx_estarts E zs nz KXA; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; kx_lia.
Ltac kx_mem_hyp_slow segs E m log zs nz KXA KXLF H :=
  lazymatch type of H with
  | bytes_at segs m ?A ?bs => apply (kx_bytes_at_log segs E m log A bs KXLF ltac:(kx_log_apart E zs nz KXA)) in H
  | u8arr segs m ?A ?bs =>
      first [ apply (kx_u8arr_apartP segs E m log A bs KXLF ltac:(kx_log_apart E zs nz KXA)) in H
            | let bs' := fresh "kxbuf" in let H' := fresh "KXU" in let HL' := fresh "KXUL" in
              destruct (kx_u8arr_logP segs E m log A bs KXLF ltac:(kx_log_u8P E zs nz KXA) H) as (bs' & H' & HL');
              clear H; rename H' into H ]
  | rw_cells segs m ?A ?cs => apply (kx_rw_cells_apartP segs E m log A cs KXLF ltac:(kx_log_apart E zs nz KXA)) in H
  | ro_cells segs m ?A ?cs => apply (kx_ro_cells_apartP segs E m log A cs KXLF ltac:(kx_log_apart E zs nz KXA)) in H
  end.

Ltac kx_mem :=
  lazymatch goal with
  | |- context [mem_denot ?E ?m ?log] =>
      lazymatch goal with
      | KXA : atoms_ok ?zs E, KXLF : log_flat E log, KXK : know_ok ?segs E m ?kn |- _ =>
          let nz := kx_len zs in
          try match goal with MI0 : mem_inv segs m |- _ => clear MI0 end;
          (* [comment removed for export] *)
          repeat match goal with
          | H : ?T |- _ =>
              lazymatch T with
              | bytes_at segs m _ _ => idtac | u8arr segs m _ _ => idtac | rw_cells segs m _ _ => idtac
              | ro_cells segs m _ _ => idtac | wr_at segs m _ _ => idtac | stk segs m _ _ => idtac | wmono segs _ m => idtac
              end;
              first [ kx_mem_hyp segs E m log kn zs KXA KXK KXLF H; kx_cells_words E zs nz KXA H log
                    | kx_mem_hyp_slow segs E m log zs nz KXA KXLF H
                    | idtac "kx_mem: dropping hypothesis (not justified against the run's stores):" H; clear H ]
          end;
          (* [comment removed for export] *)
          repeat match goal with
          | MU : munch ?W ?m0 m |- _ =>
              first [ let ws := kx_wins zs W in
                      let HW := fresh "KXW" in
                      assert (HW : Forall (win_ok E W) ws) by kx_wins_ok zs E KXA W;
                      apply (kx_munch_logb segs E m kn KXK log W ws m0 KXLF HW ltac:(vm_compute; reflexivity)) in MU; clear HW
                    | apply (kx_munch_log E m0 m log W KXLF ltac:(kx_log_inside E zs nz KXA)) in MU
                    | fail 100 "kx_mem: a store of the run is not inside the declared footprint" MU ]
          end;
          let m' := fresh "m" in
          set (m' := mem_denot E m log) in *; clearbody m'; clear KXLF
      end
  | _ => idtac
  end.

(* [comment removed for export] *)
Ltac kx_read_eq j H :=
  lazymatch goal with
  | KXRD : reads_ok ?segs ?m ?nz0 ?reads ?E, KXA : atoms_ok ?zs ?E |- _ =>
      let nz := kx_len zs in
      let k := eval vm_compute in (j - nz)%nat in
      let r := eval vm_compute in (nth_error reads k) in
      lazymatch r with
      | Some (?a, ?n, ?sx) =>
          pose proof (KXRD k a n sx ltac:(vm_cast_no_check (@eq_refl (option rdspec) (Some (a, n, sx))))) as H;
          let ab := eval cbv in (a_base a) in
          let zb := kx_ez E zs nz ab in
          let off := eval cbv in (a_off a) in
          change (ev E j = rdval segs m (wa (estart E a)) n sx) in H;
          first [ rewrite (estart_ez zs E a KXA) in H by (change (0 <= zb < 2^64); kx_lia);
                  change (ev E j = rdval segs m (wa (zb + off)) n sx) in H
                | idtac ]
      end
  end.

(* [comment removed for export] *)
Ltac kx_read_ranges_loop segs m E KXRD nz reads k :=
  lazymatch reads with
  | @nil _ => idtac
  | @cons _ (?a, ?n, ?sx) ?rest =>
      lazymatch sx with
      | false =>
          let small := eval vm_compute in (Nat.ltb n 8) in
          lazymatch small with
          | true =>
              let j := eval vm_compute in (nz + k)%nat in
              let hi := eval vm_compute in (2 ^ (8 * Z.of_nat n) - 1) in
              let HR := fresh "KXRR" in
              assert (HR : 0 <= bv_unsigned (ev E j) <= hi)
                by (let X := fresh in
                    pose proof (KXRD k a n false ltac:(reflexivity)) as X;
                    change (ev E j = rdval segs m (adenot E a) n false) in X;
                    rewrite X; exact (rdval_range segs m _ n ltac:(vm_compute; lia)))
          | false => idtac
          end
      | true => idtac
      end;
      let k' := eval vm_compute in (S k) in
      kx_read_ranges_loop segs m E KXRD nz rest k'
  end.
Ltac kx_read_ranges :=
  lazymatch goal with
  | |- context [mem_denot ?E _ _] =>
      lazymatch goal with
      | KXRD : reads_ok ?segs ?m ?nz ?reads E |- _ => kx_read_ranges_loop segs m E KXRD nz reads 0%nat
      end
  | |- _ =>
      match goal with
      | KXRD : reads_ok ?segs ?m ?nz ?reads ?E |- _ => kx_read_ranges_loop segs m E KXRD nz reads 0%nat
      end
  end.

(* [comment removed for export] *)
Ltac kx_abs :=
  repeat match goal with
  | |- context [edenot ?E ?e] =>
      let x := fresh "kxw" in generalize (edenot E e); intro x
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac kx_list_set l i v :=
  lazymatch i with
  | O => lazymatch l with @cons _ _ ?t => constr:(@cons word v t) end
  | S ?i' => lazymatch l with @cons _ ?h ?t => let t' := kx_list_set t i' v in constr:(@cons word h t') end
  end.

(* [comment removed for export] *)
Ltac kx_gen_reg i :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS (mkR ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?x17 ?x18 ?x19 ?x20
                             ?x21 ?x22 ?x23 ?x24 ?x25 ?x26 ?x27 ?x28 ?x29 ?x30 ?x31) ?F ?pc ?fc ?rv ?m ?rom) =>
      let xs := constr:([x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13; x14; x15; x16; x17; x18; x19; x20;
                         x21; x22; x23; x24; x25; x26; x27; x28; x29; x30; x31]) in
      let j := eval vm_compute in (pred i) in
      let xi := kx_nth j xs in
      let v := fresh "kxv" in
      cut (forall v : word, ltac:(let l' := kx_list_set xs j v in exact (evt segs Q (MS (mkRl l') F pc fc rv m rom))));
      [ let HH := fresh in intro HH; rewrite mkRl_mkR; exact (HH xi)
      | let v' := fresh "kxv" in intro v'; rewrite <- mkRl_mkR; revert v' ]
  end.
Definition kxword : Type := word.    (* [comment removed for export] *)
Ltac kx_gen_regs l :=
  lazymatch l with
  | @nil _ => idtac
  | @cons _ ?i ?t =>
      kx_gen_regs t; kx_gen_reg i;
      let v := fresh "kxv" in intro v; change kxword in (type of v)
  end.

Ltac kx_join_begin HJ :=
  let KJ := fresh "KXJ" in
  evar (KJ : Prop); cut KJ; [ intro HJ; subst KJ | subst KJ ].

Ltac kx_revert_mem m :=
  repeat match goal with
  | H : ?T |- _ => lazymatch T with context [m] => revert H end
  end; revert m.

(* [comment removed for export] *)
Definition kx_keep (P : Prop) : Prop := P.
Tactic Notation "kx_fact" ident(H) constr(P) := assert (H : kx_keep P) by (unfold kx_keep; kx_lia).

(* [comment removed for export] *)
Ltac kx_tidy :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
      repeat match goal with
      | H : bytes_at segs ?m' _ _ |- _ => lazymatch m' with m => fail | _ => clear H end
      | H : u8arr segs ?m' _ _ |- _ => lazymatch m' with m => fail | _ => clear H end
      | H : rw_cells segs ?m' _ _ |- _ => lazymatch m' with m => fail | _ => clear H end
      | H : ro_cells segs ?m' _ _ |- _ => lazymatch m' with m => fail | _ => clear H end
      | H : stk segs ?m' _ _ |- _ => lazymatch m' with m => fail | _ => clear H end
      | H : wr_at segs ?m' _ _ |- _ => lazymatch m' with m => fail | _ => clear H end
      | H : mem_inv segs ?m' |- _ => lazymatch m' with m => fail | _ => clear H end
      | H : munch _ _ ?m' |- _ => lazymatch m' with m => fail | _ => clear H end
      | H : wmono segs _ ?m' |- _ => lazymatch m' with m => fail | _ => clear H end
      end
  end.

Ltac kx_join HJ REGS :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ ?m0 _) =>
      kx_mem;
      lazymatch goal with
      | |- evt _ _ (MS _ _ _ _ _ ?m _) =>
          kx_gen_regs REGS;
          kx_revert_mem m;
          repeat match goal with H : kx_keep _ |- _ => revert H end;
          repeat match goal with
          | |- context [ev ?E ?j] => generalize (ev E j)
          | |- context [edenot ?E ?e] => generalize (edenot E e)
          end;
          repeat match goal with v : kxword |- _ => revert v end;
          exact HJ
      end
  end.

Ltac kx_join_end := intros; unfold kx_keep in *; kx_tidy.

(* [comment removed for export] *)
Ltac kx_enum H E e j lo cnt P :=
  pose proof (kx_enum_ok E e j lo cnt P ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(kx_lia)) as H.

(* [comment removed for export] *)
Ltac kx_erange H e :=
  lazymatch goal with
  | KXK : know_ok ?segs ?E ?m ?kn |- _ =>
      let r := eval vm_compute in (erange kn e) in
      lazymatch r with
      | Some (?lo, ?hi) =>
          pose proof (erange_sound segs E m kn e lo hi KXK ltac:(vm_cast_no_check (@eq_refl (option (Z * Z)) (Some (lo, hi))))) as H
      | None => fail "kx_erange: no interval known for" e
      end
  end.
Ltac kx_opaque_ranges :=
  repeat match goal with
  | KXK : know_ok _ ?E _ _ |- context [bv_unsigned (edenot ?E ?e)] =>
      lazymatch goal with
      | _ : _ <= bv_unsigned (edenot E e) <= _ |- _ => fail
      | _ => let H := fresh "KXOR" in kx_erange H e
      end
  end.

(* [comment removed for export] *)
Lemma kx_srlw_lit : forall zs E a s, atoms_ok zs E -> 1 <= s <= 31 ->
  bv_unsigned (edenot E (EAluw ALU_SRL a (ELit s))) = (uz E zs a mod 2^32) / 2^s.
Proof.
  intros zs E a s HA Hs. rewrite <- (uz_sound zs E a HA). cbn [edenot]. rewrite w_srlw. unfold v_srlw.
  rewrite (Z_to_bv_unsigned 64 s), (bv_wrap_small 64 s) by (unfold bv_modulus; change (2 ^ Z.of_N 64) with (2^64); lia).
  rewrite (Z.mod_small s 32) by lia. rewrite Z.shiftr_div_pow2 by lia. rewrite bv_wrap32_mod.
  set (u := bv_unsigned (edenot E a) mod 2^32).
  assert (U : 0 <= u < 2^32) by (apply Z.mod_pos_bound; lia).
  assert (P : 2 <= 2^s) by (change 2 with (2^1) at 1; apply Z.pow_le_mono_r; lia).
  assert (D : 0 <= u / 2^s < 2^31).
  { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. nia. }
  rewrite swrap32_small by lia. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  unfold bv_modulus. change (2 ^ Z.of_N 64) with (2^64). lia.
Qed.

Ltac kx_srlw1 E zs KXA a s :=
  let nz := kx_len zs in
  let ua := kx_uz E zs nz a in
  let p := eval vm_compute in (2^s) in
  let HH := fresh "KXSW" in
  assert (HH : bv_unsigned (edenot E (EAluw ALU_SRL a (ELit s))) = (ua mod 2^32) / p)
    by exact (kx_srlw_lit zs E a s KXA ltac:(lia));
  repeat match goal with H : context [bv_unsigned (edenot E (EAluw ALU_SRL a (ELit s)))] |- _ =>
           lazymatch H with HH => fail | _ => rewrite HH in H end end;
  try rewrite HH; clear HH.
Ltac kx_srlw :=
  repeat match goal with
  | KXA : atoms_ok ?zs ?E |- context [bv_unsigned (edenot ?E (EAluw ALU_SRL ?a (ELit ?s)))] => kx_srlw1 E zs KXA a s
  | KXA : atoms_ok ?zs ?E, H : context [bv_unsigned (edenot ?E (EAluw ALU_SRL ?a (ELit ?s)))] |- _ => kx_srlw1 E zs KXA a s
  end.

(* [comment removed for export] *)
Ltac kx_land1 x c :=
  lazymatch c with Zpos _ => idtac | Z0 => idtac end;
  lazymatch goal with
  | _ : 0 <= Z.land x c <= c |- _ => fail
  | _ => let H := fresh "KXLR" in
         assert (H : 0 <= Z.land x c <= c) by (split; [apply Z.land_nonneg; right; lia | apply land_le_r; lia])
  end.
Ltac kx_land_ranges :=
  repeat match goal with
  | |- context [Z.land ?x ?c] => kx_land1 x c
  | _ : context [Z.land ?x ?c] |- _ => kx_land1 x c
  end.

(* [comment removed for export] *)
Ltac kx_strip_mod :=
  repeat match goal with
  | H : context [?z mod 2^64] |- _ => rewrite (Z.mod_small z (2^64)) in H by lia
  | |- context [?z mod 2^64] => rewrite (Z.mod_small z (2^64)) by lia
  end.

(* [comment removed for export] *)
Ltac kx_ev_ranges :=
  repeat match goal with
  | KXK : know_ok _ ?E _ _ |- context [bv_unsigned (ev ?E ?j)] =>
      lazymatch goal with
      | _ : _ <= bv_unsigned (ev E j) <= _ |- _ => fail
      | _ => let H := fresh "KXVR" in kx_erange H (EVar j); cbn [edenot] in H
      end
  end.
