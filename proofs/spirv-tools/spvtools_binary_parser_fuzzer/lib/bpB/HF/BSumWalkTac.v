(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPropExec BCatExec BCatSim BSeqExec BStepTac BHoare BWalkTac BStoreOk BStreamSim BMmapSim.
Import ListNotations.
Open Scope bv_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma bytes_le_to_Z_4 : forall v : word, (bv_unsigned v < 2^32)%Z ->
  bytes_le_to_Z (word_to_le_bytes 4 v) = bv_unsigned v.
Proof.
  intros v Hv. rewrite bytes_le_N.
  change (2 ^ (8 * Z.of_nat 4))%Z with (2^32)%Z.
  apply Z.mod_small. pose proof (u64_range v). lia.
Qed.

Lemma v_lw_small : forall z, (0 <= z < 2147483648)%Z -> v_lw (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold v_lw. f_equal. rewrite u_Z2bv by lia.
  apply (bv_swrap_small 32). change (bv_half_modulus 32) with 2147483648%Z. lia.
Qed.

Lemma c_eq_Z : forall a b : Z, (0 <= a < 2^64)%Z -> (0 <= b < 2^64)%Z ->
  c_eq (Z_to_bv 64 a) (Z_to_bv 64 b) = Z.eqb a b.
Proof. intros a b Ha Hb. unfold c_eq, bv_eqb. rewrite !u_Z2bv by lia. reflexivity. Qed.

Lemma c_eq_refl : forall x : word, c_eq x x = true.
Proof. intros x. unfold c_eq. apply bv_eqb_refl. Qed.

Ltac zlen :=
  repeat match goal with
         | |- context [length (word_to_le_bytes ?n ?v)] => rewrite (length_N_to_le_bytes n v)
         end;
  cbn [Z.of_nat Pos.of_succ_nat Pos.succ length].
Ltac zsimp := zlen; u_norm.

Ltac sok_stack SOK :=
  store_ok_peel;
  eapply (store_ok_sub _ _ _ _ 144%nat); [ | exact SOK | | ]; zsimp; lia.

Ltac clear_disj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Ltac lia_fast := first [ solve [ clear_disj; lia ] | lia ].

Lemma rdn_wbytes_out_Z : forall segs bs m (zb za : Z) n,
  (0 <= za < 2^64 /\ za + Z.of_nat n <= 2^64 /\ 0 <= zb < 2^64 /\
   zb + Z.of_nat (length bs) <= 2^64 /\
   (za + Z.of_nat n <= zb \/ zb + Z.of_nat (length bs) <= za))%Z ->
  rdn segs (wbytes m (Z_to_bv 64 zb) bs) (Z_to_bv 64 za) n = rdn segs m (Z_to_bv 64 za) n.
Proof.
  intros segs bs m zb za n (Ha & Han & Hb & Hbn & Hd).
  apply rdn_wbytes_out; rewrite ?u_Z2bv by lia; lia.
Qed.
Ltac rdn_peel1 :=
  first [ rewrite rdn_wbytes_out_Z by (zlen; lia_fast)
        | rewrite rdn_wbytes_out by (zsimp; lia_fast) ].
Ltac rdn_by H := repeat rdn_peel1; exact H.

Ltac rdn_hyp :=
  match goal with
  | H : rdn _ _ ?a ?n = Some _ |- rdn _ _ ?a ?n = Some _ => exact H
  end.
Ltac rdn_solve :=
  lazymatch goal with
  | |- rdn _ (wbytes _ ?a _) ?b _ = _ =>
      tryif constr_eq a b then (apply rdn_wbytes_hit8; zsimp; lia)
      else (rdn_peel1; rdn_solve)
  | |- _ => rdn_hyp
  end.

Ltac zbv_target x i :=
  lazymatch x with
  | Z_to_bv 64 (?a - ?b)%Z => let d := eval cbv in (b - i)%Z in constr:(Z_to_bv 64 (a - d))
  | Z_to_bv 64 (?a + ?b)%Z => let d := eval cbv in (b + i)%Z in constr:(Z_to_bv 64 (a + d))
  | Z_to_bv 64 ?a =>
      lazymatch i with
      | Zneg _ => let d := eval cbv in (- i)%Z in constr:(Z_to_bv 64 (a - d))
      | _ => constr:(Z_to_bv 64 (a + i))
      end
  | _ =>
      lazymatch i with
      | Zneg _ => let d := eval cbv in (- i)%Z in constr:(Z_to_bv 64 (bv_unsigned x - d))
      | _ => constr:(Z_to_bv 64 (bv_unsigned x + i))
      end
  end.

Ltac addr_norm :=
  match goal with
  | |- context [v_addi ?x ?i] =>
      let e := constr:(v_addi x i) in
      tryif check_closed_term e then wlit_closed e
      else first
        [ rewrite (v_addi_0 x)
        | let t := zbv_target x i in
          replace e with t by (unfold v_addi; u_norm; first [reflexivity | f_equal; lia]) ]
  | _ => idtac
  end.

Ltac sp_renorm :=
  match goal with
  | |- context [regupd _ 2 (v_addi ?x ?i)] =>
      let e := constr:(v_addi x i) in
      first
        [ rewrite (v_addi_0 x)
        | let t := zbv_target x i in
          replace e with t by (unfold v_addi; u_norm; first [reflexivity | f_equal; lia]) ]
  end.

Ltac getr_hyps :=
  repeat match goal with
         | H : getr ?rs ?n = _ |- context [getr ?rs ?n] => rewrite H
         end.
Ltac addr_tac := getr_hyps; unfold v_addi; u_norm; first [reflexivity | f_equal; lia | apply bv_eq; u_norm; lia].
Ltac val_tac := first [reflexivity | assumption | symmetry; assumption].

Ltac stepST F D aa vv oktac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Store SZ8 _ _ _, _) =>
        eapply step_sd_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | gres; imm_norm; addr_tac | gres; val_tac | oktac ]
    | decode_any _ = Some (Store SZ4 _ _ _, _) =>
        eapply step_sw_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | gres; imm_norm; addr_tac | gres; val_tac | oktac ]
    | decode_any _ = Some (Store SZ1 _ _ _, _) =>
        eapply BMmapSim.step_sb_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | gres; imm_norm; addr_tac | gres; val_tac
        | reflexivity | oktac ]
    end
  | step_simpl ].

Ltac stepLD F D bsv vv rdtac vtac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Load SZ8 _ _ _ _, _) => eapply step_ld with (bs := bsv) (v := vv)
    | decode_any _ = Some (Load SZ4 true _ _ _, _) => eapply step_lw with (bs := bsv) (v := vv)
    | decode_any _ = Some (Load SZ4 false _ _ _, _) => eapply step_lwu with (bs := bsv) (v := vv)
    end;
    [ exact F | reflexivity | exact D | gres; imm_norm; getr_hyps; rdtac | vtac ]
  | step_simpl ]; vnorm.

Ltac stepLD8 F D vv := stepLD F D (word_to_le_bytes 8 vv) vv ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).

Ltac stepLBU F D bb rdtac :=
  chain_step;
  [ reflexivity
  | eapply step_lbu with (b := bb);
    [ exact F | reflexivity | exact D | gres; imm_norm; getr_hyps; rdtac ]
  | step_simpl ]; vnorm.

Ltac unorm :=
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
      lazymatch z with
      | context [bv_unsigned (Z_to_bv 64 _)] => fail
      | _ => rewrite (u_Z2bv z) by lia
      end
  end.

Ltac addi_renorm :=
  match goal with
  | |- context [regupd _ _ (v_addi (Z_to_bv 64 ?x) ?i)] =>
      let t := zbv_target (Z_to_bv 64 x) i in
      replace (v_addi (Z_to_bv 64 x) i) with t by (unfold v_addi; unorm; f_equal; lia)
  end.

Lemma rdn_img : forall segs mem (a : Z) (n : nat) (lo hi : Z),
  (forall i, (lo <= i < hi)%Z -> mem (Z_to_bv 64 i) = None) ->
  (lo <= a)%Z -> (a + Z.of_nat n <= hi)%Z -> (0 <= lo)%Z -> (hi < 2^64)%Z ->
  rdn segs mem (Z_to_bv 64 a) n = rdn segs (fun _ => None) (Z_to_bv 64 a) n.
Proof.
  intros segs mem a n lo hi Himg Hlo Hhi H0 H64.
  apply rdn_ext; [u_norm; lia|].
  intros x Hx. revert Hx. u_norm. intros Hx.
  rewrite <- (Z_to_bv_bv_unsigned 64 x). apply Himg. lia.
Qed.

Ltac img_exists :=
  lazymatch goal with |- exists bs, ?l = Some bs =>
    let v := eval vm_compute in l in
    lazymatch v with Some ?bs => exists bs; vm_compute; reflexivity end
  end.

Ltac enum_nat k N tac :=
  let rec go n := lazymatch n with
    | O => lia
    | S ?m => destruct k as [|k]; [tac | go m]
    end in go N.

Ltac zaddr H :=
  repeat match type of H with
  | context [Z_to_bv 64 (?a + ?b)%Z] =>
      let c := eval cbv in (a + b)%Z in change (a + b)%Z with c in H
  end.

Ltac zaddr_goal :=
  repeat match goal with
  | |- context [Z_to_bv 64 (?a + ?b)%Z] =>
      let c := eval cbv in (a + b)%Z in
      lazymatch c with
      | Zpos _ => change (a + b)%Z with c
      end
  end.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
