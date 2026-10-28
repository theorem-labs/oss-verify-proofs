(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import StepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

Ltac is_Zlit a := lazymatch a with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.

Ltac fold_lits :=
  repeat match goal with
  | |- context [Z.b2z (?a <? ?b)%Z] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.b2z (a <? b)%Z) in change (Z.b2z (a <? b)%Z) with v
  | |- context [Z.b2z (?a =? ?b)%Z] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.b2z (a =? b)%Z) in change (Z.b2z (a =? b)%Z) with v
  | |- context [Z.add ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.add a b) in change (Z.add a b) with v
  | |- context [Z.lor ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.lor a b) in change (Z.lor a b) with v
  | |- context [Z.land ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.land a b) in change (Z.land a b) with v
  end.

Ltac zify_lts K :=
  unfold bv_lts in K; rewrite ?land7_mod in K;
  rewrite !signed_lit_small64 in K by (Z.div_mod_to_equations; lia);
  zify_bool K.

Ltac pr := match goal with |- evtF _ _ _ (MS ?r _ ?pc _ _ ?mm _) => idtac pc; idtac r end.
Ltac prr l := match goal with |- evtF _ _ _ (MS ?r _ ?pc _ _ ?mm _) => idtac "pc=" pc;
  let rec go l := lazymatch l with | nil => idtac | ?k :: ?l' => let v := reg_val k in idtac k "=" v; go l' end in go l end.

(* [comment removed for export] *)
Ltac is_closed_lits E :=
  lazymatch E with
  | Z.add ?a ?b => is_closed_lits a; is_closed_lits b
  | Z.sub ?a ?b => is_closed_lits a; is_closed_lits b
  | Z.of_nat ?k => idtac
  | _ => is_Zlit E
  end.

Ltac addr_eq_tac_fast :=
  lazymatch goal with
  | |- Z_to_bv 64 ?e = wa ?t =>
      tryif (is_closed_lits e; is_closed_lits t)
      then (unfold wa; f_equal; vm_compute; reflexivity)
      else (symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ])
  | _ => symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ]
  end.

(* [comment removed for export] *)
Ltac acc_facts B := assert (B : True) by exact I.

Ltac solve_acc_shadow H :=
  lazymatch goal with
  | |- acc_in ?RNG (Z_to_bv 64 ?E, ?n) =>
      let nz := eval cbv in (Z.of_nat n) in
      lazymatch type of H with rng _ ?lo ?len =>
        apply (rng_acc_litZ' RNG lo len E n nz H (@eq_refl Z nz) (@eq_refl bool true));
        let B := fresh "B" in acc_facts B;
        rewrite ?shad_div in B |- *; unfold ASHOFF in B |- *;
        rewrite ?Z.shiftr_div_pow2 in B |- * by lia; change (2 ^ 3)%Z with 8%Z in B |- *;
        Z.div_mod_to_equations; lia
      end
  end.

Ltac acc_hint_shadow :=
  lazymatch goal with
  | |- acc_in _ (Z_to_bv 64 ?E, _) =>
      first [ assumption      (* [comment removed for export] *)
            | is_closed_lits E; match goal with H : rng _ 65536 _ |- _ => solve_acc_with H end
            | lazymatch E with context [Z.shiftr _ 3] =>
                match goal with H : rng _ (shad _) _ |- _ => solve_acc_shadow H end
              end ]
  end.

(* [comment removed for export] *)
Ltac small_offset k :=
  lazymatch k with
  | Z0 => idtac
  | Zpos ?p => let b := eval vm_compute in (Z.ltb k 65536) in lazymatch b with true => idtac end
  end.

Ltac solve_load_guarded :=
  match goal with
  | |- context [ov_read_bytes ?segs ?m ?a ?n] =>
    let E := addr_expr a in
    match goal with
    | H : rw_cells segs m ?A ?cs0 |- _ =>
        let k := addr_diff E A in
        small_offset k;
        let kn := eval vm_compute in (Z.to_nat k) in
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          rewrite (rw_cells_read_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
        end
    | H : ro_cells segs m ?A ?cs0 |- _ =>
        let k := addr_diff E A in
        small_offset k;
        let kn := eval vm_compute in (Z.to_nat k) in
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with ro_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          rewrite (ro_cells_read_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
        end
    | HR : ov_read_bytes segs m a n = Some ?bs |- _ =>      (* [comment removed for export] *)
        rewrite HR
    | HR : ov_read_bytes segs m ?a' n = Some ?bs |- _ =>
        cbv delta [wa] in HR;
        first [ rewrite HR
              | replace (ov_read_bytes segs m a n) with (Some bs)
                  by (rewrite <- HR; f_equal; word_eq_tac) ]
    end
  end;
  load_post.

Ltac solve_store_guarded :=
  match goal with
  | |- context [store_ok ?segs ?m ?a ?n] =>
    rewrite ?store_bytes_8', ?store_bytes_4', ?store_bytes_2', ?store_bytes_1';
    let E := addr_expr a in
    match goal with
    | H : rw_cells segs m ?A ?cs0 |- _ =>
        let k := addr_diff E A in
        small_offset k;
        let kn := eval vm_compute in (Z.to_nat k) in
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          rewrite (rw_cells_store_ok_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac]);
          cbv beta iota;
          match goal with
          | |- context [write_to_mem m a ?bs] =>
              replace (write_to_mem m a bs) with (write_to_mem m (wa (A + Z.of_nat kn)) bs) by (f_equal; addr_eq_tac)
          end
        end
    | HS : store_ok segs m ?a' n = true |- _ =>
        cbv delta [wa] in HS;
        first [ rewrite HS
              | replace (store_ok segs m a n) with true
                  by (rewrite <- HS; f_equal; word_eq_tac);
                try replace (write_to_mem m a) with (write_to_mem m a')
                  by (f_equal; word_eq_tac) ];
        cbv beta iota
    end
  end.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Lemma aip_zero : forall a s, 0 <= a < 8 -> (s = 0 \/ (0 < s <= 7 /\ a < s)) ->
  Z.land (Z.b2z (0 <? s)) (Z.lxor (Z.b2z (Z.lxor a 9223372036854775808 <? Z.lxor s 9223372036854775808)) 1) = 0.
Proof.
  intros a s Ha [Hs|Hs].
  - subst s. reflexivity.
  - change 9223372036854775808 with (2^63). rewrite !zb_lxor_sign, !Z.mod_small by lia.
    replace (0 <? s) with true by (symmetry; apply Z.ltb_lt; lia).
    replace (a + 2^63 <? s + 2^63) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.
End CANSEC1.
