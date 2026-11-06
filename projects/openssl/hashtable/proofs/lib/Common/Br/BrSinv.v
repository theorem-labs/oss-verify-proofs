(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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

Definition str0_check : bool :=
  match tl_get TL ts with
  | Some td =>
      let l := elin VT CAP.e_str0 in
      let l' := AX2.ladd (tag_lin td) (AX2.snorm (td_c td + 192), [(8, AX2.EVar 2)]) in
      (td_c td =? tc) && terms_eqb (snd l) (snd l') && (AX2.snorm (fst l - fst l') =? 0)
  | None => false
  end.

Definition sinv_check : bool :=
  is_lit_var 1 1 && is_lit_var 3 0 && is_lit_var 7 0 && is_ext_var 2
  && match aview VT M TL XT (AX2.SA CAP.e_sp0 0) with
     | Some (t, o) => (t =? ts)%uint63 && (o =? tc)
     | None => false
     end
  && match pgview VT M TL ts tc (AX2.SA CAP.e_pgsp 0) with
     | Some k => k =? 0
     | None => false
     end
  && str0_check.

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
  /\ AX2.edenot E (AX2.EVar 7) = Z_to_bv 64 0
  /\ AX2S.eqm (AX2S.uE E CAP.e_str0) (ISP + 192 + 8 * bv_unsigned (xv 2)).
Proof.
  unfold sinv_check. intros H.
  apply andb_prop in H as [H Hstr]. apply andb_prop in H as [H Hpg]. apply andb_prop in H as [H Hsp].
  apply andb_prop in H as [H Hx2]. apply andb_prop in H as [H H7]. apply andb_prop in H as [H1 H3].
  split; [|split; [|split; [|split; [|split]]]].
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
  - unfold str0_check in Hstr. destruct (tl_get TL ts) as [td|] eqn:Hg; [|discriminate].
    apply andb_prop in Hstr as [Hstr Hc]. apply andb_prop in Hstr as [Htc Hte].
    apply Z.eqb_eq in Htc, Hc. apply terms_eqb_eq in Hte.
    pose proof (elin_sound rho xv xb VT Hrho0 CAP.e_str0) as Hl.
    pose proof (tag_lin_sound rho xv xb VT M HM ts td (tl_In_ok VT M TL HTL ts td (tl_get_In TL ts td Hg))) as Ht.
    set (l := elin VT CAP.e_str0) in *.
    set (l' := AX2.ladd (tag_lin td) (AX2.snorm (td_c td + 192), [(8, AX2.EVar 2)])) in *.
    assert (Hll : AX2S.eqm (AX2S.lden E l) (AX2S.lden E l')).
    { unfold AX2S.lden. rewrite Hte. destruct (AX2S.eqm_snorm (fst l - fst l')) as [q Hq]. rewrite Hc in Hq.
      exists (- q). lia. }
    eapply AX2S.eqm_trans; [apply AX2S.eqm_sym; exact Hl|].
    eapply AX2S.eqm_trans; [exact Hll|].
    eapply AX2S.eqm_trans; [apply AX2S.ladd_sound|].
    replace (ISP + 192 + 8 * bv_unsigned (xv 2)) with (bv_unsigned (rho ts) + (tc + 192 + 8 * bv_unsigned (xv 2))) by lia.
    apply AX2S.eqm_add; [exact Ht|].
    unfold AX2S.lden. cbn [fst snd AX2S.tden]. unfold AX2S.uE. cbn [AX2.edenot].
    rewrite (is_ext_var_sound 2 Hx2). rewrite Htc.
    destruct (AX2S.eqm_snorm (tc + 192)) as [q Hq]. exists q. lia.
Qed.

End Sinv.
