(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BImage BZBridge BSysStep BSFModel BellsX BArr BacX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BllocRep.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section HCW.
  Context {HCEIL : HeapCeil}.

Lemma zx32_wz : forall x, 0 <= x < 2^32 -> zx32 (wz x) = wz x.
Proof. intros x Hx. unfold zx32, wz. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

Lemma shl32_shr30 : forall x, 0 <= x < 2^32 -> Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl x 32))) 30 = 4 * x.
Proof.
  intros x Hx. rewrite Z.shiftl_mul_pow2 by lia. rewrite unsigned_lit by lia. rewrite Z.shiftr_div_pow2 by lia.
  replace (x * 2^32) with ((4 * x) * 2^30) by lia. apply Z.div_mul. lia.
Qed.

Lemma shl32_val : forall x, 0 <= x < 2^32 -> bv_unsigned (Z_to_bv 64 (Z.shiftl x 32)) = x * 2^32.
Proof. intros x Hx. rewrite Z.shiftl_mul_pow2 by lia. rewrite unsigned_lit by lia. reflexivity. Qed.

Section WithSegs.
  Variable segs : list Segment.
  Lemma u32arr_snoc : forall m A ws w,
    u32arr segs m A (ws ++ [w]) <-> u32arr segs m A ws /\ rw_cells segs m (A + 4 * Z.of_nat (length ws)) [C4 w].
  Proof.
    intros m A ws w. unfold u32arr, rw_cells, cells_at. rewrite u32s_app. cbn [u32s map concat cells_bytes cbytes cells_wf cell_wf cells_size csize app].
    rewrite app_nil_r. rewrite bytes_at_app, u32s_length, length_app. cbn [length].
    replace (Z.of_nat (4 * length ws)) with (4 * Z.of_nat (length ws)) by lia.
    replace (4 * Z.of_nat (length ws + 1)) with (4 * Z.of_nat (length ws) + 4) by lia.
    rewrite wr_at_app by lia. change (Z.of_nat (4 + 0)) with 4. tauto.
  Qed.
  Lemma u64arr_snoc : forall m A ws w,
    u64arr segs m A (ws ++ [w]) <-> u64arr segs m A ws /\ rw_cells segs m (A + 8 * Z.of_nat (length ws)) [C8 w].
  Proof.
    intros m A ws w. unfold u64arr, rw_cells, cells_at. rewrite u64s_app. cbn [u64s map concat cells_bytes cbytes cells_wf cell_wf cells_size csize app].
    rewrite app_nil_r. rewrite bytes_at_app, u64s_length, length_app. cbn [length].
    replace (Z.of_nat (8 * length ws)) with (8 * Z.of_nat (length ws)) by lia.
    replace (8 * Z.of_nat (length ws + 1)) with (8 * Z.of_nat (length ws) + 8) by lia.
    rewrite wr_at_app by lia. change (Z.of_nat (8 + 0)) with 8. tauto.
  Qed.

End WithSegs.

Lemma junk_of_rw_cells : forall m A cs, rw_cells asegs m A cs -> junk m A (Z.of_nat (cells_size cs)).
Proof. intros m A cs H Hn. eapply stk_of_rw_cells. exact H. Qed.

End HCW.

Ltac addr_diff_near E A :=
  let k := addr_diff E A in
  let b := eval vm_compute in (Z.ltb (Z.abs k) 2048)%Z in
  lazymatch b with true => k end.

Ltac solve_load_near :=
  match goal with
  | |- context [ov_read_bytes ?segs ?m ?a ?n] =>
    let E := addr_expr a in
    match goal with
    | H : rw_cells segs m ?A ?cs0 |- _ =>
        let k := addr_diff_near E A in
        let kn := eval vm_compute in (Z.to_nat k) in
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          rewrite (rw_cells_read_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
        end
    | H : ro_cells segs m ?A ?cs0 |- _ =>
        let k := addr_diff_near E A in
        let kn := eval vm_compute in (Z.to_nat k) in
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with ro_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          rewrite (ro_cells_read_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
        end
    | HR : ov_read_bytes segs m ?a' n = Some ?bs |- _ =>
        cbv delta [wa] in HR;
        first [ rewrite HR
              | replace (ov_read_bytes segs m a n) with (Some bs)
                  by (rewrite <- HR; f_equal; word_eq_tac) ]
    end
  end;
  load_post.

Ltac solve_load ::= first [ solve_load_near | solve_load_image ].

Ltac solve_store_near :=
  match goal with
  | |- context [store_ok ?segs ?m ?a ?n] =>
    rewrite ?store_bytes_8', ?store_bytes_4', ?store_bytes_2', ?store_bytes_1';
    let E := addr_expr a in
    match goal with
    | H : rw_cells segs m ?A ?cs0 |- _ =>
        let k := addr_diff_near E A in
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
    end
  end.

Ltac head_of t := lazymatch t with ?h _ => head_of h | _ => t end.
Ltac post_callN segs m :=
  let ms' := fresh "ms'" in let PO := fresh "PO" in
  intros ms' PO;
  (let h := head_of ltac:(type of PO) in try unfold h in PO);
  rewrite ?unsigned_lit in PO by lia; rewrite ?Z.add_0_r in PO; revert ms' PO; post_call segs m.
Tactic Notation "callN" uconstr(SPEC) :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [ eapply SPEC | post_callN segs m ]
  end.

Section HCW2.
  Context {HCEIL : HeapCeil}.

Lemma stk_cells : forall m lo hi, stk asegs m lo hi -> lo <= hi ->
  exists junk, rw_cells asegs m lo [CB (Z.to_nat (hi - lo)) junk].
Proof.
  intros m lo hi ST LE. destruct (stk_carve asegs m lo hi (Z.to_nat (hi - lo)) ST) as [_ [junk R]]; [lia|].
  rewrite Z2Nat.id in R by lia. replace (hi - (hi - lo)) with lo in R by lia. exists junk. exact R.
Qed.

Inductive hidden (P : Prop) : Prop := Hide (p : P).

End HCW2.

Ltac hide_hyp H := apply Hide in H.
Ltac unhide_hyp H := destruct H as [H].
Lemma hidden_out : forall P : Prop, hidden P -> P.
Proof. intros P [p]. exact p. Qed.

Ltac nb_from pf T :=
  lazymatch T with
  | ?A /\ ?B => nb_from constr:(@proj1 A B pf) A; nb_from constr:(@proj2 A B pf) B
  | akobj ?X 4096 => first [ lazymatch goal with _ : akobj X 4096 |- _ => idtac end | pose proof (pf : akobj X 4096) as THB | idtac ]
  | aapp ?X 160 => first [ lazymatch goal with _ : aapp X 160 |- _ => idtac end | pose proof (pf : aapp X 160) as CTB | idtac ]
  | _ => idtac
  end.
Ltac name_bands :=
  try (match goal with
       | H : hidden ?P |- _ => lazymatch P with context [akobj _ 4096] => nb_from constr:(hidden_out P H) P end
       end);
  try (match goal with
       | H : hidden ?P |- _ => lazymatch P with context [aapp _ 160] => nb_from constr:(hidden_out P H) P end
       end);
  try (match goal with
       | H : ?P |- _ => lazymatch P with hidden _ => fail | _ /\ _ => lazymatch P with context [akobj _ 4096] => nb_from H P end end
       end);
  try (match goal with
       | H : ?P |- _ => lazymatch P with hidden _ => fail | _ /\ _ => lazymatch P with context [aapp _ 160] => nb_from H P end end
       end).

Section HCW3.
  Context {HCEIL : HeapCeil}.

Definition hide (P : Prop) : Prop := hidden P.

End HCW3.

