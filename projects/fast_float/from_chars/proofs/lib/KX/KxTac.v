(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec FxLin FxCore FxSubst FxSound FxMem FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxDrv FxFrame FxCall FxRgs RefMemcpyLib.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.RefMemcpyLib.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Mem Cells Exec Frame Arr Step Image RegsEquiv MState.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.Proofs.fast_float.from_chars.lib.KX Require Import KxBridge KxRun.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac lnorm_in H :=
  repeat match type of H with
  | context [lden ?E ?l] =>
      lazymatch l with
      | lvar _ => rewrite (lden_lvar E) in H
      | _ => let l' := eval vm_compute in l in
             lazymatch l' with
             | LIN 0 [(?x, 1)] => change (lden E l) with (lden E (lvar x)) in H; rewrite (lden_lvar E x) in H
             | _ => change (lden E l) with (Z_to_bv 64 (lz E l')) in H; unfold lz in H; cbn [l_c l_t tsum] in H
             end
      end
  end.
Ltac lnorm :=
  repeat match goal with
  | |- context [lden ?E ?l] =>
      lazymatch l with
      | lvar _ => rewrite (lden_lvar E)
      | _ => let l' := eval vm_compute in l in
             lazymatch l' with
             | LIN 0 [(?x, 1)] => change (lden E l) with (lden E (lvar x)); rewrite (lden_lvar E x)
             | _ => change (lden E l) with (Z_to_bv 64 (lz E l')); unfold lz; cbn [l_c l_t tsum]
             end
      end
  end.
Ltac rget_norm_in H := repeat match type of H with context [rget ?T ?k] =>
  let v := eval vm_compute in (rget T k) in change (rget T k) with v in H end.
Ltac rget_norm := repeat match goal with |- context [rget ?T ?k] =>
  let v := eval vm_compute in (rget T k) in change (rget T k) with v end.
Ltac ubase := lnorm; rewrite u_Z_to_bv; unfold vz; rewrite ?Z.add_0_l, ?Z.add_0_r, ?Z.mul_1_l.

(* [comment removed for export] *)
Definition sgn (k : Z) : Z := if Z.ltb (2 ^ 63) k then k - two64 else k.
Definition lsgn (l : lin) : lin := LIN (sgn (l_c l)) (List.map (fun p => (fst p, sgn (snd p))) (l_t l)).
Lemma eqm_sgn : forall k, eqm k (sgn k).
Proof.
  intros k. unfold sgn. destruct (Z.ltb (2 ^ 63) k); [|apply eqm_refl].
  unfold eqm. rewrite Zminus_mod, Z_mod_same_full, Z.sub_0_r, Zmod_mod. reflexivity.
Qed.
Lemma tsum_lsgn : forall E t, eqm (tsum E t) (tsum E (List.map (fun p => (fst p, sgn (snd p))) t)).
Proof.
  intros E t. induction t as [|[x k] t IH]; cbn [tsum List.map fst snd]; [apply eqm_refl|].
  apply eqm_add; [apply eqm_mul; [apply eqm_sgn | apply eqm_refl] | exact IH].
Qed.
Lemma lden_lsgn : forall E l, lden E l = lden E (lsgn l).
Proof.
  intros E [c t]. apply lden_eqm. unfold lz, lsgn. cbn [l_c l_t]. apply eqm_add; [apply eqm_sgn | apply tsum_lsgn].
Qed.
Ltac lnorm_s :=
  repeat match goal with
  | |- context [lden ?E ?l] =>
      lazymatch l with
      | lvar _ => rewrite (lden_lvar E)
      | _ => let l' := eval vm_compute in (lsgn l) in
             lazymatch l' with
             | LIN 0 [(?x, 1)] => rewrite (lden_lsgn E l); change (lsgn l) with (lvar x); rewrite (lden_lvar E x)
             | _ => rewrite (lden_lsgn E l); change (lsgn l) with l'; unfold lden at 1, lz at 1; cbn [l_c l_t tsum]
             end
      end
  end.
Ltac ubase_s := lnorm_s; rewrite ?u_Z_to_bv; unfold vz; rewrite ?Z.add_0_l, ?Z.add_0_r, ?Z.mul_1_l.
Ltac lnorm_s_in H :=
  repeat match type of H with
  | context [lden ?E ?l] =>
      lazymatch l with
      | lvar _ => rewrite (lden_lvar E) in H
      | _ => let l' := eval vm_compute in (lsgn l) in
             lazymatch l' with
             | LIN 0 [(?x, 1)] => rewrite (lden_lsgn E l) in H; change (lsgn l) with (lvar x) in H; rewrite (lden_lvar E x) in H
             | _ => rewrite (lden_lsgn E l) in H; change (lsgn l) with l' in H; unfold lden, lz in H; cbn [l_c l_t tsum] in H
             end
      end
  end.


Ltac getr_mkR_norm := rewrite getr_mkR;
  match goal with |- context [Z.to_nat (bv_unsigned ?r)] =>
    let v := eval vm_compute in (Z.to_nat (bv_unsigned r)) in change (Z.to_nat (bv_unsigned r)) with v end; cbn beta iota.

Section Segs.
Variable segs : list Segment.
(* [comment removed for export] *)
#[using="Type"] Lemma u8arr_of_stk : forall m lo (n : nat), stk segs m lo (lo + Z.of_nat n) -> exists bs, u8arr segs m lo bs /\ length bs = n.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m lo n (H1 & H2 & H).
  destruct (bytes_exist segs m lo n H1 H2) as (bs & Hb & Hl).
  { intros i Hi. destruct (H (lo + Z.of_nat i) ltac:(lia)) as (_ & b & X). rewrite X. discriminate. }
  exists bs. split; [|exact Hl]. split; [exact Hb|]. rewrite Hl. split; [exact H1|]. split; [lia|].
  intros i Hi. exact (proj1 (H (lo + i) ltac:(lia))).
Qed.
#[using="Type"] Lemma word_of_stk : forall m lo, stk segs m lo (lo + 8) -> exists w, rw_cells segs m lo [C8 w].
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m lo S. destruct (u8arr_of_stk m lo 8 S) as (bs & (Hb & Hw) & Hl). exists (Z_to_bv 64 (lez bs)).
  split.
  - split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r, le8_lez by exact Hl. exact Hb.
  - cbn [cells_size csize]. rewrite Hl in Hw. exact Hw.
Qed.
#[using="Type"] Lemma rg_ok_untrack : forall E m b s c o bvs, rg_ok segs E m (track (RG b s RW c) o bvs) -> rg_ok segs E m (RG b s RW TEmpty).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E m b s c o bvs (H1 & H2 & H3 & _). refine (conj H1 (conj H2 (conj H3 _))). intros p v X. cbn [rg_cont] in X. rewrite tget_empty in X. discriminate.
Qed.
#[using="Type"] Lemma rg_ok_untrack2 : forall E m b s c o bvs o' bvs', rg_ok segs E m (track (track (RG b s RW c) o bvs) o' bvs') ->
  rg_ok segs E m (RG b s RW TEmpty).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E m b s c o bvs o' bvs' (H1 & H2 & H3 & _). refine (conj H1 (conj H2 (conj H3 _))). intros p v X. cbn [rg_cont] in X. rewrite tget_empty in X. discriminate.
Qed.
End Segs.
