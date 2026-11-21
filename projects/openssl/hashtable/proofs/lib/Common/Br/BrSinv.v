(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (argv[0]'s address check moved to the plain chain's glue, which places its own string block). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.FX Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxMemSound.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import PropExec AxSymExec3 AxSymExec3Sound AsanPlanCore CxPlan.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.Br Require Import BrEnv BrPure.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section Sinv.
Variable rho : int -> word.
Variable xv : nat -> word.
Variable xb : nat -> list byte.
Variable VT : vtab.
Variable M : itrie region.
Variable TL : ttab.
Variable XT : list (int * AX2.lin).
Variable ts : int.
Variable tc : Z.
Hypothesis Hrho0 : rho 0%uint63 = Z_to_bv 64 0.
Hypothesis HM : forall t rg, iget t M = Some rg -> region_ok rho t rg.
Hypothesis HTL : tl_ok VT M TL = true.
Hypothesis HXT : xt_ok rho xv xb VT XT.

Local Notation E := (env_of rho xv xb VT).
Local Notation ISP := (bv_unsigned (rho ts) + tc).

Definition is_lit_var (x : nat) (z : Z) : bool :=
  match vt_get VT x with
  | Some (VVal (FV t w)) => (t =? 0)%uint63 && (wZ w =? z)
  | _ => false
  end.

Definition is_ext_var (x : nat) : bool :=
  match vt_get VT x with None | Some VExt => true | _ => false end.

(* LPS c0dd863a: no argv[0] check here: [CAP.e_str0] is the c0dd863a launch's argv[0], which a plain family
   state does not name; the plain glue (H0BrGlue2 / HUBrGlue2) places its own string area. *)
Definition sinv_check : bool :=
  is_lit_var 1 1 && is_lit_var 3 0 && is_lit_var 7 0 && is_ext_var 2
  && match aview VT M TL XT (AX2.SA CAP.e_sp0 0) with
     | Some (t, o) => (t =? ts)%uint63 && (o =? tc)
     | None => false
     end
  && match pgview VT M TL ts tc (AX2.SA CAP.e_pgsp 0) with
     | Some k => k =? 0
     | None => false
     end.

Lemma is_lit_var_sound x z : is_lit_var x z = true -> 0 <= z < 2 ^ 64 -> AX2.edenot E (AX2.EVar x) = Z_to_bv 64 z.
Proof.
  unfold is_lit_var. intros H Hz. cbn [AX2.edenot]. rewrite ev_env_of.
  destruct (vt_get VT x) as [[[t w]| |]|]; try discriminate.
  apply andb_prop in H as [Ht Hw]. apply Uint63.eqb_spec in Ht. apply Z.eqb_eq in Hw. subst t.
  cbn [vden]. rewrite (fk_dv_conc rho w Hrho0). unfold wbv. rewrite Hw. reflexivity.
Qed.

Lemma is_ext_var_sound x : is_ext_var x = true -> AX2.ev E x = xv x.
Proof.
  unfold is_ext_var. intros H. rewrite ev_env_of. destruct (vt_get VT x) as [[| |]|]; try discriminate; reflexivity.
Qed.

Theorem sinv_facts : sinv_check = true ->
  AX2S.uE E CAP.e_sp0 = ISP
  /\ AX2S.uE E CAP.e_pgsp = ISP - ISP mod 4096
  /\ AX2.edenot E (AX2.EVar 1) = Z_to_bv 64 1
  /\ AX2.edenot E (AX2.EVar 3) = Z_to_bv 64 0
  /\ AX2.edenot E (AX2.EVar 7) = Z_to_bv 64 0.
Proof.
  unfold sinv_check. intros H.
  apply andb_prop in H as [H Hpg]. apply andb_prop in H as [H Hsp].
  apply andb_prop in H as [H Hx2]. apply andb_prop in H as [H H7]. apply andb_prop in H as [H1 H3].
  split; [|split; [|split; [|split]]].
  - destruct (aview VT M TL XT (AX2.SA CAP.e_sp0 0)) as [[t o]|] eqn:Hav; [|discriminate].
    apply andb_prop in Hsp as [Ht Ho]. apply Uint63.eqb_spec in Ht. apply Z.eqb_eq in Ho. subst t o.
    pose proof (aview_sound rho xv xb VT M TL XT HM Hrho0 HTL HXT _ ts tc Hav) as Hs.
    unfold AX2S.estart in Hs. cbn [AX2.a_base AX2.a_off] in Hs. unfold AX2S.uE. lia.
  - destruct (pgview VT M TL ts tc (AX2.SA CAP.e_pgsp 0)) as [k|] eqn:Hp; [|discriminate].
    apply Z.eqb_eq in Hpg. subst k.
    pose proof (pgview_sound rho xv xb VT M TL Hrho0 HM HTL ts tc _ 0 Hp) as Hs.
    unfold AX2S.estart in Hs. cbn [AX2.a_base AX2.a_off] in Hs. unfold AX2S.uE.
    pose proof (Z.div_mod ISP 4096 ltac:(lia)). lia.
  - apply is_lit_var_sound; [exact H1 | lia].
  - apply is_lit_var_sound; [exact H3 | lia].
  - apply is_lit_var_sound; [exact H7 | lia].
Qed.

End Sinv.
