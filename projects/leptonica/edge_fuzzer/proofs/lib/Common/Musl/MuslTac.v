(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica Require Import SumWalkTac.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Reloc Require Import RelocKit.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rl_of_Zsum : forall d c k c', (c + k = c')%Z -> Z_to_bv 64 (c + d + k) = rl d c'.
Proof. intros d c k c' <-. unfold rl. f_equal. lia. Qed.
Lemma rl_of_Z : forall d c, Z_to_bv 64 (c + d) = rl d c.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Ltac rl_zaddr H :=
  repeat match type of H with
  | context [Z_to_bv 64 (?c + ?d + ?k)%Z] =>
      is_Z_lit c; is_Z_lit k; tryif is_Z_lit d then fail else
      let c' := eval cbv in (c + k)%Z in rewrite (rl_of_Zsum d c k c' eq_refl) in H
  | context [Z_to_bv 64 (?c + ?d)%Z] =>
      is_Z_lit c; tryif is_Z_lit d then fail else change (Z_to_bv 64 (c + d)%Z) with (rl d c) in H
  | context [Z_to_bv 64 (?a + ?b)%Z] =>
      is_Z_lit a; is_Z_lit b;
      let c := eval cbv in (a + b)%Z in change (a + b)%Z with c in H
  end.
Ltac rl_zaddr_goal :=
  repeat match goal with
  | |- context [Z_to_bv 64 (?c + ?d + ?k)%Z] =>
      is_Z_lit c; is_Z_lit k; tryif is_Z_lit d then fail else
      let c' := eval cbv in (c + k)%Z in rewrite (rl_of_Zsum d c k c' eq_refl)
  | |- context [Z_to_bv 64 (?c + ?d)%Z] =>
      is_Z_lit c; tryif is_Z_lit d then fail else change (Z_to_bv 64 (c + d)%Z) with (rl d c)
  | |- context [Z_to_bv 64 (?a + ?b)%Z] =>
      is_Z_lit a; is_Z_lit b;
      let c := eval cbv in (a + b)%Z in
      lazymatch c with Zpos _ => change (a + b)%Z with c end
  end.

(* [comment removed for export] *)
Ltac rl_zaddr_all :=
  repeat match goal with
  | H : context [Z_to_bv 64 (?c + @rl_delta ?RL ?b)%Z] |- _ =>
      is_Z_lit c; change (Z_to_bv 64 (c + @rl_delta RL b)%Z) with (rl (@rl_delta RL b) c) in H
  | |- context [Z_to_bv 64 (?c + @rl_delta ?RL ?b)%Z] =>
      is_Z_lit c; change (Z_to_bv 64 (c + @rl_delta RL b)%Z) with (rl (@rl_delta RL b) c)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[export] Ltac u_norm ::= rl_unorm; repeat rewrite u_Z2bv by lia.
#[export] Ltac unorm ::=
  rl_unorm;
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
      lazymatch z with
      | context [bv_unsigned (Z_to_bv 64 _)] => fail
      | _ => rewrite (u_Z2bv z) by lia
      end
  end.
Ltac rzsimp := zsimp.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac addrZ a :=
  lazymatch a with
  | rl ?d ?c => constr:((c + d)%Z)
  | Z_to_bv 64 ?z => constr:(z)
  end.
#[export] Ltac rdn_peel1 ::=
  first [ rewrite rdn_wbytes_out_Z by (zlen; lia_fast)
        | lazymatch goal with
          | |- rdn ?segs (wbytes ?m ?b ?bs) ?a ?n = _ =>
              let zb := addrZ b in let za := addrZ a in
              change (rdn segs (wbytes m b bs) a n) with (rdn segs (wbytes m (Z_to_bv 64 zb) bs) (Z_to_bv 64 za) n);
              rewrite (rdn_wbytes_out_Z segs bs m zb za n) by (zlen; lia_fast);
              change (Z_to_bv 64 za) with a
          end
        | rewrite rdn_wbytes_out by (rzsimp; lia_fast) ].

#[export] Ltac rdn_solve ::=
  lazymatch goal with
  | |- rdn _ (wbytes _ ?a _) ?b _ = _ =>
      tryif constr_eq a b then (apply rdn_wbytes_hit8; rzsimp; lia)
      else (rdn_peel1; rdn_solve)
  | |- _ => rdn_hyp
  end.

(* [comment removed for export] *)
#[export] Ltac addr_norm ::=
  match goal with
  | |- context [v_addi (rl ?d ?c) ?i] => rl_val (v_addi (rl d c) i)
  | |- context [v_addi ?x ?i] =>
      let e := constr:(v_addi x i) in
      tryif check_closed_term e then wlit_closed e
      else first
        [ rewrite (v_addi_0 x)
        | let t := zbv_target x i in
          replace e with t by (unfold v_addi; u_norm; first [reflexivity | f_equal; lia]) ]
  | _ => idtac
  end.


(* [comment removed for export] *)
Ltac stepretK F D FK tac :=
  lazymatch type of FK with
  | fetch_word _ ?k = Some _ =>
      stepjr F D k ltac:(gres; tac);
      imm_norm;
      rewrite (fetch_ret_ok _ _ _ FK : v_jalr k 0 = k)
  end.

(* [comment removed for export] *)
Ltac stepjrK F D FK tac :=
  lazymatch type of FK with
  | fetch_word _ ?k = Some _ =>
      stepjr F D k tac;
      imm_norm;
      rewrite (fetch_ret_ok _ _ _ FK : v_jalr k 0 = k)
  end.

Ltac stepretF F D FK :=
  lazymatch type of FK with
  | fetch_word _ ?k = Some _ =>
      stepjr F D k ltac:(gres; first [reflexivity | assumption | bveq]);
      imm_norm;
      rewrite (fetch_ret_ok _ _ _ FK : v_jalr k 0 = k)
  end.

(* [comment removed for export] *)
Lemma rl_ret_ok_near : forall segs d c0 c (w : bv 32),
  fetch_word segs (rl d c0) = Some w -> ((c - c0) mod 2 = 0)%Z -> ret_ok (rl d c).
Proof.
  intros segs d c0 c w H Hc. apply ret_ok_even.
  pose proof (fetch_even _ _ _ H) as E. rewrite rl_u_mod in E |- *.
  change (2 ^ 64)%Z with (2 * 2 ^ 63)%Z in *.
  rewrite Z.rem_mul_r in E |- * by lia.
  rewrite Z.mul_comm, Z.mod_add in E |- * by lia. rewrite Z.mod_mod in E |- * by lia.
  replace (c + d)%Z with ((c0 + d) + (c - c0))%Z by lia.
  rewrite Z.add_mod by lia. rewrite E, Hc. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rl_rel_add : forall dX t dY u, v_add (Z_to_bv 64 ((t + dX) - (u + dY))) (rl dY u) = rl dX t.
Proof.
  intros dX t dY u. unfold v_add. rewrite rl_u_mod, Z_to_bv_unsigned. unfold rl. apply Z_to_bv64_mod_eq.
  change (bv_wrap 64 (t + dX - (u + dY))) with ((t + dX - (u + dY)) mod 2^64)%Z.
  rewrite <- Zplus_mod. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma rl_add_l_lit : forall d c k c', (c + k = c')%Z -> v_add (Z_to_bv 64 k) (rl d c) = rl d c'.
Proof. intros d c k c' <-. apply rl_add_l. Qed.
Lemma rl_add_r_lit : forall d c k c', (c + k = c')%Z -> v_add (rl d c) (Z_to_bv 64 k) = rl d c'.
Proof. intros d c k c' <-. apply rl_add_r. Qed.
Ltac rl_addfold :=
  repeat match goal with
  | |- context [v_add (Z_to_bv 64 ?k) (rl ?d ?c)] =>
      is_Z_lit k; is_Z_lit c; let c' := eval cbv in (c + k)%Z in rewrite (rl_add_l_lit d c k c' eq_refl)
  | |- context [v_add (rl ?d ?c) (Z_to_bv 64 ?k)] =>
      is_Z_lit k; is_Z_lit c; let c' := eval cbv in (c + k)%Z in rewrite (rl_add_r_lit d c k c' eq_refl)
  end.
Lemma rl_wrap64 : forall d c c', (c mod 2^64 = c')%Z -> rl d c = rl d c'.
Proof. intros d c c' <-. unfold rl. apply Z_to_bv64_mod_eq. rewrite Zplus_mod_idemp_l. reflexivity. Qed.
Ltac rl_wrap :=
  repeat match goal with
  | |- context [rl ?d ?c] =>
      is_Z_lit c; let c' := eval cbv in (c mod 2^64)%Z in
      tryif constr_eq c c' then fail else rewrite (rl_wrap64 d c c' eq_refl)
  end.

(* [comment removed for export] *)
Ltac rl_cond :=
  idtac;
  first [ cond_compute
        | rewrite rl_ltu_same by (rl_bounds; lia); reflexivity
        | rewrite rl_eqb_same by (rl_bounds; lia); reflexivity
        | (* [comment removed for export] *)
          unfold c_eq, c_ltu, bv_eqb, bv_ltu; rl_bounds; rl_unorm; rewrite ?u_Z2bv by lia;
          first [ apply Z.eqb_neq | apply Z.eqb_eq | apply Z.ltb_lt | apply Z.ltb_ge ]; lia ].

Ltac rl_ret_ok_at b c k :=
  let c0 := eval vm_compute in (c + k)%Z in
  let z0 := eval vm_compute in (code_lookup canon_code b c0) in
  lazymatch z0 with
  | Some ?w0 =>
      exact (rl_ret_ok_near _ _ c0 c _
               (rl_fetch b c0 (Z_to_bv 32 w0) ltac:(vm_cast_no_check (@eq_refl bool true))) eq_refl)
  | None =>          (* [comment removed for export] *)
      let r := eval vm_compute in (site_find canon_sites 0%nat c0) in
      lazymatch r with
      | Some (?i, _, _) =>
          let s := eval vm_compute in (nth_error canon_sites i) in
          lazymatch s with
          | Some ?cs => exact (rl_ret_ok_near _ _ c0 c _ (rl_site_F i cs (@eq_refl _ (Some cs))) eq_refl)
          end
      end
  end.
Ltac rl_ret_ok :=
  lazymatch goal with
  | |- ret_ok (rl (@rl_delta ?RL ?b) ?c) =>
      first [ rl_ret_ok_at b c 0%Z | rl_ret_ok_at b c (-4)%Z | rl_ret_ok_at b c 4%Z | rl_ret_ok_at b c (-8)%Z | rl_ret_ok_at b c 8%Z
            | rl_ret_ok_at b c (-12)%Z | rl_ret_ok_at b c 12%Z | rl_ret_ok_at b c (-16)%Z | rl_ret_ok_at b c 16%Z ]
  end.
