(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Cfg Require Import LedgerCfg.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.FX Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxMemSound FxDrive FxDrive3.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import PropExec AxSymExec3 AxSymExec3Sound.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import AsanPlanCore AsanPlan AsanPlanSound.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Br Require Import BrEnv Br3Aux.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition page_var_of (a : AX2.expr) : option nat :=
  match a with
  | AX2.EMd M_MUL (AX2.ELit z) (AX2.EVar v) => if z =? 4096 then Some v else None
  | _ => None
  end.
Lemma page_var_of_sound a v : page_var_of a = Some v -> a = AX2.EMd M_MUL (AX2.ELit 4096) (AX2.EVar v).
Proof.
  unfold page_var_of. intros H. destruct a as [| |op a1 a2|op a1 a2|op a1 a2|op a1 a2|sx lo nn a1|sx kk i nn]; try discriminate H.
  destruct op; try discriminate H. destruct a1; try discriminate H. destruct a2; try discriminate H.
  destruct (Z.eqb_spec z 4096) as [->|Hne]; [|discriminate H]. injection H as ->. reflexivity.
Qed.
Definition lit_of (n : AX2.expr) : option Z := match n with AX2.ELit z => Some z | _ => None end.
Lemma lit_of_sound n z : lit_of n = Some z -> n = AX2.ELit z.
Proof. unfold lit_of. intros H. destruct n; try discriminate H. injection H as ->. reflexivity. Qed.

Definition op_match (XTn : list (int * nat)) (e : fent) (a n : AX2.expr) : bool :=
  let '(t, off, len) := e in
  (off =? 0)%uint63
  && match page_var_of a with
     | Some v => existsb (fun p : int * nat => (fst p =? t)%uint63 && Nat.eqb (snd p) v) XTn
     | None => false
     end
  && match lit_of n with Some z => z =? to_Z len | None => false end.

(* [comment removed for export] *)
Definition vnew_silent (k : APC.mkind) : bool := negb (APS.is_none_kind k) && negb (APS.is_lazy_kind k).
(* [comment removed for export] *)
Definition vnew_lazy (k : APC.mkind) : bool := negb (APS.is_none_kind k) && APS.is_lazy_kind k.

(* [comment removed for export] *)
Fixpoint vmx_walk (XTn : list (int * nat)) (fuel : nat) (opsR : list vop) (opsA : list APC.vmop) {struct fuel} : bool :=
  match fuel with
  | O => false
  | S f =>
      match opsR with
      | (OpShadow, _) :: rR => vmx_walk XTn f rR opsA
      | (OpGrant, _) :: rR => vmx_walk XTn f rR opsA
      | _ =>
          match opsA with
          | [] => match opsR with [] => true | _ => false end
          | APC.VNew k a n :: rA =>
              if vnew_silent k then vmx_walk XTn f opsR rA
              else if vnew_lazy k then
                     match opsR with
                     | (OpLazy, e) :: rR => op_match XTn e a n && vmx_walk XTn f rR rA
                     | _ => false
                     end
                   else false
          | APC.VUnmap a n :: rA =>
              match opsR with
              | (OpCut, e) :: rR => op_match XTn e a n && vmx_walk XTn f rR rA
              | _ => false
              end
          | APC.VFixIn false false a n :: rA =>
              match opsR with
              | (OpCommit, e) :: rR => op_match XTn e a n && vmx_walk XTn f rR rA
              | _ => false
              end
          | _ => false
          end
      end
  end.

(* [comment removed for export] *)
Definition vmx_chk (XTn : list (int * nat)) (opsF : list vop) (opsS opsE : list APC.vmop) : bool :=
  let k := (List.length opsE - List.length opsS)%nat in
  APC.list_eqb APC.vmop_eqb (skipn k opsE) opsS
  && vmx_walk XTn (S (List.length opsF + k)) (rev opsF) (firstn k opsE).

(* [comment removed for export] *)
(* [comment removed for export] *)

Section VmxSound.
Variable rho' : int -> word.
Variable xv : nat -> word.
Variable xb : nat -> list byte.
Variable VT : vtab.
Variable XTn : list (int * nat).
#[local] Notation E1 := (env_of rho' xv xb VT).
(* [comment removed for export] *)
Hypothesis HXTn : Forall (fun p => AX2S.eqm (AX2S.lden E1 (snd p)) (bv_unsigned (rho' (fst p))))
                         (map (fun p : int * nat => (fst p, page_lin (snd p))) XTn).

Lemma page_var_word t v : In (t, v) XTn -> AX2.edenot E1 (AX2.EMd M_MUL (AX2.ELit 4096) (AX2.EVar v)) = rho' t.
Proof.
  intros Hin.
  assert (Hm : In (t, page_lin v) (map (fun p : int * nat => (fst p, page_lin (snd p))) XTn))
    by (apply in_map_iff; exists (t, v); split; [reflexivity | exact Hin]).
  pose proof (proj1 (Forall_forall _ _) HXTn _ Hm) as H1. cbn [fst snd] in H1.
  pose proof (AX2S.lin_of_sound E1 (AX2.EMd M_MUL (AX2.ELit 4096) (AX2.EVar v))) as H2. fold (page_lin v) in H2.
  unfold AX2S.uE in H2.
  assert (H3 : AX2S.eqm (bv_unsigned (AX2.edenot E1 (AX2.EMd M_MUL (AX2.ELit 4096) (AX2.EVar v)))) (bv_unsigned (rho' t))).
  { destruct H1 as [q1 Hq1]. destruct H2 as [q2 Hq2]. exists (q1 - q2). lia. }
  rewrite (br_eqm_word _ _ H3). apply Z_to_bv_bv_unsigned.
Qed.

Lemma op_match_sound e a n : op_match XTn e a n = true ->
  APS.vm_iv E1 a n = den rho' e /\ APS.vm_lo E1 a = e_lo (den rho' e) /\ APS.vm_hi E1 a n = e_hi (den rho' e).
Proof.
  destruct e as [[t off] len]. unfold op_match. intros Hc.
  apply andb_prop in Hc as [Hc Hn]. apply andb_prop in Hc as [Hoff Ha].
  apply Uint63.eqb_spec in Hoff. subst off.
  destruct (page_var_of a) as [v|] eqn:Epv; [|discriminate Ha]. apply page_var_of_sound in Epv. subst a.
  apply existsb_exists in Ha as ([t' v'] & Hin & Heq). cbn [fst snd] in Heq.
  apply andb_prop in Heq as [Ht Hv]. apply Uint63.eqb_spec in Ht. apply Nat.eqb_eq in Hv. subst t' v'.
  destruct (lit_of n) as [zn|] eqn:Eln; [|discriminate Hn]. apply lit_of_sound in Eln. subst n. apply Z.eqb_eq in Hn. subst zn.
  pose proof (page_var_word t v Hin) as Ew.
  assert (Eadr : adr rho' t (to_Z 0) = rho' t).
  { apply bv_eq. change (to_Z 0) with 0. rewrite (adr_unsigned rho' t 0); [lia | lia | pose proof (br_u64 (rho' t)); lia]. }
  assert (Eiv : APS.vm_iv E1 (AX2.EMd M_MUL (AX2.ELit 4096) (AX2.EVar v)) (AX2.ELit (to_Z len)) = den rho' (t, 0%uint63, len)).
  { unfold APS.vm_iv. cbn [den]. rewrite Ew, Eadr. reflexivity. }
  split; [exact Eiv|]. unfold APS.vm_lo, APS.vm_hi, e_hi, e_lo, e_sz. rewrite <- Eiv. unfold APS.vm_iv. cbn [fst snd]. split; reflexivity.
Qed.

(* [comment removed for export] *)
Fixpoint replayA (opsA : list APC.vmop) (x : list (word * word) * list (word * word)) : list (word * word) * list (word * word) :=
  match opsA with
  | [] => x
  | op :: r => let (na, lz) := replayA r x in APS.vm_step E1 op na lz
  end.
Fixpoint replayF (opsR : list vop) (x : list (word * word) * list (word * word)) : list (word * word) * list (word * word) :=
  match opsR with
  | [] => x
  | o :: r => let (na, lz) := replayF r x in (na_step rho' na o, lz_step rho' lz o)
  end.

Lemma replayA_app ops S : APS.vm_replay E1 (ops ++ S) = replayA ops (APS.vm_replay E1 S).
Proof. induction ops as [|op r IH]; [reflexivity|]. cbn [app APS.vm_replay replayA]. rewrite IH. reflexivity. Qed.

Lemma replayF_app l1 l2 x : replayF (l1 ++ l2) x = replayF l1 (replayF l2 x).
Proof. induction l1 as [|o r IH]; [reflexivity|]. cbn [app replayF]. rewrite IH. reflexivity. Qed.

Lemma replayF_apply ops : forall na0 lz0, (na_apply rho' ops na0, lz_apply rho' ops lz0) = replayF (rev ops) (na0, lz0).
Proof.
  induction ops as [|o r IH]; intros na0 lz0; [reflexivity|].
  cbn [rev]. rewrite replayF_app. cbn [replayF]. rewrite <- IH. reflexivity.
Qed.

Lemma step_silentA kd a n rA opsR x :
  vnew_silent kd = true -> replayA rA x = replayF opsR x -> replayA (APC.VNew kd a n :: rA) x = replayF opsR x.
Proof.
  intros Hs IHx. cbn [replayA]. rewrite IHx. destruct (replayF opsR x) as [na lz].
  unfold APS.vm_step. unfold vnew_silent in Hs. apply andb_prop in Hs as [E1n E2l]. apply negb_true_iff in E1n, E2l.
  rewrite E1n, E2l. reflexivity.
Qed.

Lemma step_silentF k e rR opsA x :
  (k = OpShadow \/ k = OpGrant) -> replayA opsA x = replayF rR x -> replayA opsA x = replayF ((k, e) :: rR) x.
Proof.
  intros Hk IHx. cbn [replayF]. rewrite <- IHx. destruct (replayA opsA x) as [na lz].
  unfold na_step, lz_step. cbn [fst]. destruct Hk as [-> | ->]; reflexivity.
Qed.

Lemma step_lazy kd a n rA e rR x :
  vnew_lazy kd = true -> op_match XTn e a n = true -> replayA rA x = replayF rR x ->
  replayA (APC.VNew kd a n :: rA) x = replayF ((OpLazy, e) :: rR) x.
Proof.
  intros Hl Hm IHx. destruct (op_match_sound e a n Hm) as (Eiv & Elo & Ehi).
  cbn [replayA replayF]. rewrite IHx. destruct (replayF rR x) as [na lz].
  unfold APS.vm_step, na_step, lz_step. cbn [fst snd].
  unfold vnew_lazy in Hl. apply andb_prop in Hl as [E1n E2l]. apply negb_true_iff in E1n. rewrite E1n, E2l, Eiv. reflexivity.
Qed.

Lemma step_cut a n rA e rR x :
  op_match XTn e a n = true -> replayA rA x = replayF rR x ->
  replayA (APC.VUnmap a n :: rA) x = replayF ((OpCut, e) :: rR) x.
Proof.
  intros Hm IHx. destruct (op_match_sound e a n Hm) as (Eiv & Elo & Ehi).
  cbn [replayA replayF]. rewrite IHx. destruct (replayF rR x) as [na lz].
  unfold APS.vm_step, na_step, lz_step. cbn [fst snd]. rewrite Elo, Ehi. reflexivity.
Qed.

Lemma step_commit a n rA e rR x :
  op_match XTn e a n = true -> replayA rA x = replayF rR x ->
  replayA (APC.VFixIn false false a n :: rA) x = replayF ((OpCommit, e) :: rR) x.
Proof.
  intros Hm IHx. destruct (op_match_sound e a n Hm) as (Eiv & Elo & Ehi).
  cbn [replayA replayF]. rewrite IHx. destruct (replayF rR x) as [na lz].
  unfold APS.vm_step, na_step, lz_step. cbn [fst snd]. rewrite Elo, Ehi. reflexivity.
Qed.

Lemma vmx_walk_sound fuel : forall opsR opsA, vmx_walk XTn fuel opsR opsA = true -> forall x, replayA opsA x = replayF opsR x.
Proof.
  induction fuel as [|f IH]; intros opsR opsA Hc x; [discriminate Hc|]. cbn [vmx_walk] in Hc.
  (* [comment removed for export] *)
  assert (HA : forall opsR0, opsR0 = opsR ->
     match opsA with
     | [] => match opsR0 with [] => true | _ => false end
     | APC.VNew k a n :: rA =>
         if vnew_silent k then vmx_walk XTn f opsR0 rA
         else if vnew_lazy k then match opsR0 with (OpLazy, e) :: rR => op_match XTn e a n && vmx_walk XTn f rR rA | _ => false end
              else false
     | APC.VUnmap a n :: rA => match opsR0 with (OpCut, e) :: rR => op_match XTn e a n && vmx_walk XTn f rR rA | _ => false end
     | APC.VFixIn false false a n :: rA => match opsR0 with (OpCommit, e) :: rR => op_match XTn e a n && vmx_walk XTn f rR rA | _ => false end
     | _ => false
     end = true -> replayA opsA x = replayF opsR x).
  { intros opsR0 -> H. destruct opsA as [|op rA].
    - destruct opsR; [reflexivity | discriminate H].
    - destruct op as [kd a n|x1 y1 a n|a n|a n]; try discriminate H.
      + destruct (vnew_silent kd) eqn:Es; [exact (step_silentA kd a n rA opsR x Es (IH _ _ H x))|].
        destruct (vnew_lazy kd) eqn:El; [|discriminate H].
        destruct opsR as [|[k e] rR]; [discriminate H|]. destruct k; try discriminate H.
        apply andb_prop in H as [Hm Hw]. exact (step_lazy kd a n rA e rR x El Hm (IH _ _ Hw x)).
      + destruct x1; [discriminate H|]. destruct y1; [discriminate H|].
        destruct opsR as [|[k e] rR]; [discriminate H|]. destruct k; try discriminate H.
        apply andb_prop in H as [Hm Hw]. exact (step_commit a n rA e rR x Hm (IH _ _ Hw x)).
      + destruct opsR as [|[k e] rR]; [discriminate H|]. destruct k; try discriminate H.
        apply andb_prop in H as [Hm Hw]. exact (step_cut a n rA e rR x Hm (IH _ _ Hw x)). }
  destruct opsR as [|[k e] rR]; [exact (HA _ eq_refl Hc)|].
  destruct k; try exact (HA _ eq_refl Hc).
  - exact (step_silentF OpGrant e rR opsA x (or_intror eq_refl) (IH _ _ Hc x)).
  - exact (step_silentF OpShadow e rR opsA x (or_introl eq_refl) (IH _ _ Hc x)).
Qed.

(* [comment removed for export] *)
Theorem vmx_sound opsF opsS opsE na0 lz0 :
  vmx_chk XTn opsF opsS opsE = true ->
  APS.vm_replay E1 opsS = (na0, lz0) ->
  APS.vm_replay E1 opsE = (na_apply rho' opsF na0, lz_apply rho' opsF lz0).
Proof.
  unfold vmx_chk. intros Hc HS. apply andb_prop in Hc as [Heq Hw].
  apply (APS.list_eqb_eq APC.vmop_eqb APS.vmop_eqb_eq) in Heq.
  set (k := (List.length opsE - List.length opsS)%nat) in *.
  rewrite <- (firstn_skipn k opsE), Heq, replayA_app, HS, replayF_apply.
  exact (vmx_walk_sound _ _ _ Hw (na0, lz0)).
Qed.
End VmxSound.
