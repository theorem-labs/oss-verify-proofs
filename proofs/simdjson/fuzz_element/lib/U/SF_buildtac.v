(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From Ltac2 Require Import Ltac2.
#[global] Set Default Proof Mode "Classic".
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Sf_lib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac lit_range :=
  lazymatch goal with
  | |- (0 <= ?z < _)%Z => is_Zlit_zb z; split; [ apply (proj1 (Z.leb_le _ _)); reflexivity
                                               | apply (proj1 (Z.ltb_lt _ _)); reflexivity ]
  | |- (0 <= ?z)%Z => is_Zlit_zb z; apply (proj1 (Z.leb_le _ _)); reflexivity
  | |- (0 < ?z)%Z => is_Zlit_zb z; apply (proj1 (Z.ltb_lt _ _)); reflexivity
  end.

Ltac flia_fast := first [ assumption | lit_range | slim; lia | lia ].

Ltac recast_hyp H T' :=
  let T := type of H in
  let h := fresh "rc" in
  pose proof ((@eq_ind Prop T (fun X : Prop => X) H T' (@eq_refl Prop T')) : T') as h;
  clear H; rename h into H.

Ltac recast_with f H :=
  let T := type of H in let T' := f T in
  first [ constr_eq T T' | recast_hyp H T' ].

Ltac unfold_sf_term T :=
  eval cbv beta delta [add64 sub64 mul64 shl64 not64 ltu64 eqz64 nez64 zext32 sext32 srliw mulhu
         is_neg64 sra63 lt_s64 lo64 hi64 wrap64 b2z
         ONES64 M32 SIGN64 MASK48 MASKLO ABS_HI INF_HI QUIET_HI QNAN_HI IMPLICIT_HI] in T.
Ltac unfold_sf_in_recast H := recast_with unfold_sf_term H.

Ltac sf_vocab_term T :=
  eval cbv beta delta [add64 sub64 mul64 shl64 not64 ltu64 eqz64 nez64 zext32 sext32 srliw mulhu
         is_neg64 sra63 lt_s64 lo64 hi64 wrap64
         ONES64 M32 SIGN64 MASK48 MASKLO ABS_HI INF_HI QUIET_HI QNAN_HI IMPLICIT_HI] in T.
Ltac sf_model_in H :=
  recast_with sf_vocab_term H; rewrite ?b2z_Zb2z in H; zb_fold_lits_in H.

Ltac cbn_bool_term T := eval cbn [andb orb negb] in T.
Ltac cbn_bool_in H := recast_with cbn_bool_term H.

Ltac unfold_in_recast c H := recast_with ltac:(fun T => eval unfold c in T) H.

Ltac zeq_special e m :=
  lazymatch m with
  | Z.b2z (?s <? ?y) =>
      lazymatch e with
      | Z.b2z (s <? ?x) =>
          is_var s; f_equal; apply (f_equal Z.b2z); cbv delta [s];
          apply eq_true_iff_eq; rewrite 2?Z.ltb_lt; slim; rewrite ?land_W64; lia
      end
  | Z.land (?u + ?v) 18446744073709551615 =>
      match goal with
      | E : v = _ |- _ => is_var v; apply Z_to_bv_eqm; rewrite E; slim; rewrite ?land_W64; lia
      | E : u = _ |- _ => is_var u; apply Z_to_bv_eqm; rewrite E; slim; rewrite ?land_W64; lia
      end
  end.

Ltac lia1 := Zify.zify; xlia zchecker.

Ltac2 rec sf_plain_arith (t : constr) : bool :=
  lazy_match! t with
  | Z.le _ _ => true | Z.lt _ _ => true | Z.ge _ _ => true | Z.gt _ _ => true
  | @eq _ _ _ => true
  | le _ _ => true | lt _ _ => true | ge _ _ => true | gt _ _ => true
  | N.le _ _ => true | N.lt _ _ => true | Z.divide _ _ => true
  | True => true | False => true
  | not ?q => sf_plain_arith q
  | ?a /\ ?b => Bool.and (sf_plain_arith a) (sf_plain_arith b)
  | ?a \/ ?b => Bool.and (sf_plain_arith a) (sf_plain_arith b)
  | ?a -> ?b => Bool.and (sf_plain_arith a) (sf_plain_arith b)
  | _ => false
  end.
Ltac2 sf_prune2 () : unit :=
  let hs := Control.hyps () in
  let ids := List.map_filter (fun h => let (id, body, ty) := h in
                match body with
                | Some _ => None
                | None => if sf_plain_arith ty then None
                          else (lazy_match! (Constr.type ty) with Prop => Some id | _ => None end)
                end) hs in
  match ids with [] => () | _ :: _ => Std.clear ids end.

Ltac sf_prune_defs :=
  repeat match goal with
  | H : ?v = _ |- _ => is_var v; clear H; clear v
  | H : _ = ?v |- _ => is_var v; clear H; clear v
  end.
Ltac sf_prune := ltac2:(Control.enter sf_prune2); sf_prune_defs.

Ltac zb_masks_fast :=
  repeat match goal with
  | |- context [Z.land ?x ?m] =>
      is_Zlit_zb m;
      let k := eval vm_compute in (Z.log2 (m + 1)) in
      let m' := eval vm_compute in (2 ^ k - 1)%Z in
      constr_eq m m';
      let p := eval vm_compute in (2 ^ k)%Z in
      replace (Z.land x m) with (x mod p)%Z
        by (symmetry; change m with (2^k - 1)%Z; change p with (2^k)%Z; apply zb_land_mask;
            apply (proj1 (Z.leb_le _ _)); reflexivity)
  | H : context [Z.land ?x ?m] |- _ =>
      is_Zlit_zb m;
      let k := eval vm_compute in (Z.log2 (m + 1)) in
      let m' := eval vm_compute in (2 ^ k - 1)%Z in
      constr_eq m m';
      let p := eval vm_compute in (2 ^ k)%Z in
      replace (Z.land x m) with (x mod p)%Z in H
        by (symmetry; change m with (2^k - 1)%Z; change p with (2^k)%Z; apply zb_land_mask;
            apply (proj1 (Z.leb_le _ _)); reflexivity)
  end.

Ltac blia_fast :=
  intros; pose_word_ranges; sf_prune;
  rewrite ?Z.land_lor_distr_l in *;
  rewrite ?Z.lor_eq_0_iff in *;
  rewrite ?zb_lxor_eq0 in *;
  zb_masks_fast;
  rewrite ?Z.shiftr_div_pow2 in * by lia1;
  zb_fold_lits;
  lia1.

Ltac alia := sf_prune; lia1.

Ltac alu_only i :=
  lazymatch i with
  | OpImm _ _ _ _ => idtac | ShiftImm _ _ _ _ => idtac | Op _ _ _ _ => idtac
  | OpImm32 _ _ _ => idtac | ShiftImm32 _ _ _ _ => idtac | Op32 _ _ _ _ => idtac
  | Mul _ _ _ _ => idtac | Mul32 _ _ _ _ => idtac | Lui _ _ => idtac
  end.

Ltac vnorm_tail_fast :=
  repeat match goal with
         |- context [@bv_add 64 (Z_to_bv 64 ?a) (Z_to_bv 64 ?b)] => rewrite (lit_add_lit a b) end;
  (match goal with |- context [w0] => rewrite ?w0_lit | _ => idtac end);
  (match goal with |- context [w1] => rewrite ?w1_lit | _ => idtac end);
  unfold v_addi, v_add, v_sub, v_mul, v_andi, v_ori, v_xori, v_and, v_or, v_xor,
         v_slli, v_srli, v_srai, v_sll, v_srl, v_sra, v_lui, v_auipc,
         v_addiw, v_slliw, v_srliw, v_sraiw, v_addw, v_subw, v_sllw, v_srlw, v_sraw,
         v_mulh, v_mulhsu, v_mulhu, v_mulw, btgt;
  repeat match goal with
         | |- context [Z_to_bv 64 (bv_unsigned (Z_to_bv 64 ?e) + ?d)] => rewrite (unsigned_Z_to_bv_add e d)
         | |- context [Z_to_bv 64 (?d + bv_unsigned (Z_to_bv 64 ?e))] => rewrite (unsigned_Z_to_bv_add_r e d)
         end;
  fold_closed_in_goal;
  (match goal with |- context [Z_to_bv 64 (bv_unsigned _)] => rewrite ?Z_to_bv_lit_self | _ => idtac end);
  (match goal with |- context [bv_and _ (bv_not _)] => rewrite ?ret_pc_fold | _ => idtac end);
  repeat match goal with
  | |- context [ret_pc (Z_to_bv 64 ?n)] => is_Zlit n;
       replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end.

Ltac step_core_fast segs R F pc fc rv m ro :=
  let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
  lazymatch fw with
  | Some ?w =>
    let ec := eval vm_compute in (is_ecall w) in
    lazymatch ec with
    | false =>
      let d := eval vm_compute in (decode_any w) in
      lazymatch d with
      | Some (?i, ?sz) =>
        tryif alu_only i then
          (eapply evt_step;
           [ split; [reflexivity|];
             rewrite (step_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
             exec_cbv; simp_is_x0; simp_regs; vnorm_rw_for i; vnorm_tail_fast;
             reflexivity
           | ])
        else step_core segs R F pc fc rv m ro
      | None => fail "undecodable instruction at" pc
      end
    | true => fail "ecall at" pc
    end
  | None => fail "no instruction at" pc
  end.

Ltac step_fast :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) => step_core_fast segs R F pc fc rv m ro
  | |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail "pc is not a literal:" pc
  end.

Ltac zsimp_fast :=
  (match goal with
   | |- context [v_sltu _ _] => rewrite ?v_sltu_b2z, ?v_slt_b2z, ?v_sltiu_b2z, ?v_slti_b2z
   | |- context [v_slt _ _] => rewrite ?v_sltu_b2z, ?v_slt_b2z, ?v_sltiu_b2z, ?v_slti_b2z
   | |- context [v_sltiu _ _] => rewrite ?v_sltu_b2z, ?v_slt_b2z, ?v_sltiu_b2z, ?v_slti_b2z
   | |- context [v_slti _ _] => rewrite ?v_sltu_b2z, ?v_slt_b2z, ?v_sltiu_b2z, ?v_slti_b2z
   | |- _ => idtac
   end);
  cbv delta [zxb];
  zb_fold_lits;
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?e)] =>
      first [ rewrite (inr64_unsigned_lit e) by zrange
            | zs_wrap e ]
  | |- _ => progress zs_idioms
  end; zb_fold_lits.
