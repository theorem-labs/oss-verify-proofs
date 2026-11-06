(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SFModel.
Module SF_buildtac.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Ltac2.Ltac2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

#[global] Set Default Proof Mode "Classic".
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel.

(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac lit_range :=
  lazymatch goal with
  | |- (0 <= ?z < _)%Z => is_Zlit_zb z; split; [ apply (proj1 (Z.leb_le _ _)); reflexivity
                                               | apply (proj1 (Z.ltb_lt _ _)); reflexivity ]
  | |- (0 <= ?z)%Z => is_Zlit_zb z; apply (proj1 (Z.leb_le _ _)); reflexivity
  | |- (0 < ?z)%Z => is_Zlit_zb z; apply (proj1 (Z.ltb_lt _ _)); reflexivity
  end.
(* [comment removed for export] *)
Ltac flia_fast := first [ assumption | lit_range | slim; lia | lia ].

(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac recast_hyp H T' :=
  let T := type of H in
  let h := fresh "rc" in
  pose proof ((@eq_ind Prop T (fun X : Prop => X) H T' (@eq_refl Prop T')) : T') as h;
  clear H; rename h into H.

(* [comment removed for export] *)
Ltac recast_with f H :=
  let T := type of H in let T' := f T in
  first [ constr_eq T T' | recast_hyp H T' ].

(* [comment removed for export] *)
Ltac unfold_sf_term T :=
  eval cbv beta delta [add64 sub64 mul64 shl64 not64 ltu64 eqz64 nez64 zext32 sext32 srliw mulhu
         is_neg64 sra63 lt_s64 lo64 hi64 wrap64 b2z
         ONES64 M32 SIGN64 MASK48 MASKLO ABS_HI INF_HI QUIET_HI QNAN_HI IMPLICIT_HI] in T.
Ltac unfold_sf_in_recast H := recast_with unfold_sf_term H.

(* [comment removed for export] *)
Ltac sf_vocab_term T :=
  eval cbv beta delta [add64 sub64 mul64 shl64 not64 ltu64 eqz64 nez64 zext32 sext32 srliw mulhu
         is_neg64 sra63 lt_s64 lo64 hi64 wrap64
         ONES64 M32 SIGN64 MASK48 MASKLO ABS_HI INF_HI QUIET_HI QNAN_HI IMPLICIT_HI] in T.
Ltac sf_model_in H :=
  recast_with sf_vocab_term H; rewrite ?b2z_Zb2z in H; zb_fold_lits_in H.

(* [comment removed for export] *)
Ltac cbn_bool_term T := eval cbn [andb orb negb] in T.
Ltac cbn_bool_in H := recast_with cbn_bool_term H.

(* [comment removed for export] *)
Ltac unfold_in_recast c H := recast_with ltac:(fun T => eval unfold c in T) H.

(* [comment removed for export] *)
(* [comment removed for export] *)
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

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac lia1 := Zify.zify; xlia zchecker.
(* [comment removed for export] *)
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
(* [comment removed for export] *)
Ltac sf_prune_defs :=
  repeat match goal with
  | H : ?v = _ |- _ => is_var v; clear H; clear v
  | H : _ = ?v |- _ => is_var v; clear H; clear v
  end.
Ltac sf_prune := ltac2:(Control.enter sf_prune2); sf_prune_defs.

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Ltac alia := sf_prune; lia1.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac alu_only i :=
  lazymatch i with
  | OpImm _ _ _ _ => idtac | ShiftImm _ _ _ _ => idtac | Op _ _ _ _ => idtac
  | OpImm32 _ _ _ => idtac | ShiftImm32 _ _ _ _ => idtac | Op32 _ _ _ _ => idtac
  | Mul _ _ _ _ => idtac | Mul32 _ _ _ _ => idtac | Lui _ _ => idtac
  end.

(* [comment removed for export] *)
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

Ltac step_fast_orig :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) => step_core_fast segs R F pc fc rv m ro
  | |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail "pc is not a literal:" pc
  end.
(* [comment removed for export] *)
Ltac step_fast := step2_fast.

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
End SF_buildtac.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require SFW1_lemmas.
Module F_f128_to_u32.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.


Import ListNotations.
Open Scope bv_scope.

Import SF_buildtac.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac flia ::= flia_fast.
Local Ltac blia ::= blia_fast.
(* [comment removed for export] *)
Local Ltac step ::= step_fast. Local Ltac stepz ::= stepz_fast.
Local Ltac zsimp ::= zsimp_fast.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma lo64_words : forall lo hi, (0 <= lo < 2^64)%Z -> lo64 (lo + 2^64 * hi) = lo.
Proof.
  intros lo hi H. unfold lo64. rewrite wrap64_mod.
  rewrite Z.mul_comm, Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma hi64_words : forall lo hi, (0 <= lo < 2^64)%Z -> (0 <= hi < 2^64)%Z -> hi64 (lo + 2^64 * hi) = hi.
Proof.
  intros lo hi Hl Hh. unfold hi64. rewrite wrap64_mod, Z.shiftr_div_pow2 by lia.
  rewrite Z.mul_comm, Z.div_add, Z.div_small by lia. apply Z.mod_small. lia.
Qed.
End F_f128_to_u32.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import SFModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.


Import ListNotations.
Local Open Scope Z_scope.

Import SF_buildtac.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac flia ::= flia_fast.
Local Ltac blia ::= blia_fast.
(* [comment removed for export] *)
Local Ltac step ::= step_fast. Local Ltac stepz ::= stepz_fast.
Local Ltac zsimp ::= zsimp_fast.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma shr56_mul64_range : forall y k, 0 <= Z.shiftr (mul64 y k) 56 < 256.
Proof.
  intros. unfold mul64. pose proof (wrap64_range (y * k)) as H.
  rewrite Z.shiftr_div_pow2 by lia. split. { apply Z.div_pos; lia. } apply Z.div_lt_upper_bound; lia.
Qed.

Lemma clz64_mirror_range : forall x, 0 <= clz64_mirror x < 256.
Proof. intros x. unfold clz64_mirror. cbv zeta. apply shr56_mul64_range. Qed.

Lemma lor_lt_256 : forall a b, 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lor a b < 256.
Proof.
  intros a b Ha Hb. split. { apply Z.lor_nonneg; lia. }
  destruct (Z.eq_dec a 0) as [->|Na]. { rewrite Z.lor_0_l. lia. }
  destruct (Z.eq_dec b 0) as [->|Nb]. { rewrite Z.lor_0_r. lia. }
  assert (Hl : Z.lor a b <> 0). { intro E. apply Z.lor_eq_0_iff in E. lia. }
  pose proof (Z.lor_nonneg a b).
  change 256 with (2^8). apply Z.log2_lt_pow2; [lia|].
  rewrite Z.log2_lor by lia. apply Z.max_lub_lt; apply Z.log2_lt_pow2; lia.
Qed.

Lemma clz128_mirror_range : forall hi lo, 0 <= clz128_mirror hi lo < 256.
Proof.
  intros. unfold clz128_mirror. cbv zeta. apply lor_lt_256.
  - apply clz64_mirror_range.
  - destruct (hi =? 0); cbv; split; congruence.
Qed.
Lemma shr_land_W64 : forall x k, (0 <= x < 2^64) -> 0 <= k -> Z.land (Z.shiftr x k) 18446744073709551615 = Z.shiftr x k.
Proof. intros. rewrite land_W64. apply Z.mod_small. apply (zr_shiftr x k); assumption. Qed.
Lemma land_ones_l : forall x, 0 <= x < 2^64 -> Z.land 18446744073709551615 x = x.
Proof. intros. rewrite Z.land_comm, land_W64. apply Z.mod_small. lia. Qed.
Ltac strip_lands :=
  repeat match goal with
  | |- context [Z.land (Z.shiftr ?x ?k) 18446744073709551615] =>
      rewrite (shr_land_W64 x k) by (first [zrange | zrange_nonneg | lia])
  end.

Definition nd_hi (sigHi sigLo : Z) : Z := let '(h, _, _) := norm_denormal sigHi sigLo in h.
Definition nd_lo (sigHi sigLo : Z) : Z := let '(_, l, _) := norm_denormal sigHi sigLo in l.
Definition nd_clz (sigHi sigLo : Z) : Z := let '(_, _, c) := norm_denormal sigHi sigLo in c.
Lemma norm_denormal_eta : forall sigHi sigLo,
  norm_denormal sigHi sigLo = (nd_hi sigHi sigLo, nd_lo sigHi sigLo, nd_clz sigHi sigLo).
Proof. intros. unfold nd_hi, nd_lo, nd_clz. destruct (norm_denormal sigHi sigLo) as [[h l] c]. reflexivity. Qed.

Lemma nd_clz_eq : forall sigHi sigLo, nd_clz sigHi sigLo = clz128_mirror sigHi sigLo.
Proof.
  intros. unfold nd_clz, norm_denormal.
  destruct (shl128_mirror sigHi sigLo (sub64 (clz128_mirror sigHi sigLo) 15)) as [h l]. reflexivity.
Qed.
Lemma nd_clz_range : forall sigHi sigLo, 0 <= nd_clz sigHi sigLo < 256.
Proof. intros. rewrite nd_clz_eq. apply clz128_mirror_range. Qed.

(* [comment removed for export] *)
Lemma clz128_hi_nz : forall hi lo, hi <> 0 -> clz128_mirror hi lo = clz64_mirror hi.
Proof.
  intros. unfold clz128_mirror. replace (hi =? 0) with false by (symmetry; apply Z.eqb_neq; assumption).
  cbn. apply Z.lor_0_r.
Qed.
Lemma clz128_hi_z : forall hi lo, hi = 0 -> clz128_mirror hi lo = Z.lor (clz64_mirror lo) 64.
Proof. intros. subst. reflexivity. Qed.