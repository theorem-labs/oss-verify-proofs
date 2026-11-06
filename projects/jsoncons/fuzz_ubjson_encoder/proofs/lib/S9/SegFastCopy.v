(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore SegFastLoad.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import BMode.
Import ListNotations. Import AX2. Import AX2B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module AX2Y.
Section WithSegs.
Variable segs : list Segment. Context {bmK : BMode}.
Section Ctx.
Variable bc : bctx. Variable kx : kix. Variable kx2 : AX2L.kix2.

Definition know_lookupB2 (rb : expr) (rk : Z) (n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
  match AX2L.know_lookupA0I2 bc kx kx2 segs rb rk n sx hints acc with
  | LMiss acc' hints' =>
      match know_bytes_lit segs (bc_fk bc) rb rk n with
      | Some bs => LHit (lit_of_bytes sx n bs) acc' hints'
      | None => LMiss acc' hints'
      end
  | r => r
  end.
Definition kread8e2 (b : expr) (off : Z) : option expr :=
  match know_lookupB2 b off 8 false [] [] with
  | LHit v [] _ => Some v
  | _ => None
  end.
Fixpoint copy_facts2 (fuel : nat) (sb : expr) (sk : Z) (db : expr) (dk : Z) (n : Z) : option (list kentry) :=
  match fuel with
  | O => Some []
  | S f =>
      if (Z.leb 8 n &&
          match kread8e2 sb sk with Some _ => true | None => match APC.kread_bytesB segs bc 8 sb sk with Some _ => true | None => false end end)%bool then
        match (match kread8e2 sb sk with
               | Some v => Some v
               | None => match APC.kread_bytesB segs bc 8 sb sk with
                         | Some bs => Some (ELit (zbytes_le_to_Z bs))
                         | None => None
                         end
               end), copy_facts2 f sb (sk + 8) db (dk + 8) (n - 8) with
        | Some v, Some rest => Some (KWord (SA db dk) 8 v :: rest)
        | _, _ => None
        end
      else if Z.leb 1 n then
        match know_lookupB2 sb sk 1 false [] [], copy_facts2 f sb (sk + 1) db (dk + 1) (n - 1) with
        | LHit v [] _, Some rest => Some (KWord (SA db dk) 1 v :: rest)
        | _, _ => None
        end
      else Some []
  end.
End Ctx.

Lemma know_lookupB2_eq : forall kn rb rk n sx hints acc,
  know_lookupB2 (mkbc kn) (mk_kix kn) (AX2L.mk_kix2 kn) rb rk n sx hints acc = know_lookupB segs (mkbc kn) rb rk n sx hints acc.
Proof.
  intros. unfold know_lookupB2, know_lookupB, know_lookupAB. rewrite AX2L.know_lookupA0I2_eq. reflexivity.
Qed.
Lemma kread8e2_eq : forall kn b off, kread8e2 (mkbc kn) (mk_kix kn) (AX2L.mk_kix2 kn) b off = APC.kread8eB segs (mkbc kn) b off.
Proof. intros. unfold kread8e2, APC.kread8eB. rewrite know_lookupB2_eq. reflexivity. Qed.
Lemma copy_facts2_eq : forall kn fuel sb sk db dk n,
  copy_facts2 (mkbc kn) (mk_kix kn) (AX2L.mk_kix2 kn) fuel sb sk db dk n = APC.copy_factsB segs (mkbc kn) fuel sb sk db dk n.
Proof.
  intros kn fuel. induction fuel as [|f IH]; intros; [reflexivity|].
  cbn [copy_facts2 APC.copy_factsB]. rewrite !kread8e2_eq, !know_lookupB2_eq, !IH. reflexivity.
Qed.
End WithSegs.

Section Ctx3.
Variable segs : list Segment. Context {bmK : BMode}.
Variable bc : bctx. Variable kx : kix. Variable kx2 : AX2L.kix2.
Fixpoint copy_facts3 (fuel : nat) (sb : expr) (sk : Z) (db : expr) (dk : Z) (n : Z) : option (list kentry) :=
  match fuel with
  | O => Some []
  | S f =>
      let bytewise (u : unit) :=
        if Z.leb 1 n then
          match know_lookupB2 segs bc kx kx2 sb sk 1 false [] [], copy_facts3 f sb (sk + 1) db (dk + 1) (n - 1) with
          | LHit v [] _, Some rest => Some (KWord (SA db dk) 1 v :: rest)
          | _, _ => None
          end
        else Some [] in
      if Z.leb 8 n then
        match (match kread8e2 segs bc kx kx2 sb sk with
               | Some v => Some v
               | None => match APC.kread_bytesB segs bc 8 sb sk with
                         | Some bs => Some (ELit (zbytes_le_to_Z bs))
                         | None => None
                         end
               end) with
        | Some v => match copy_facts3 f sb (sk + 8) db (dk + 8) (n - 8) with Some rest => Some (KWord (SA db dk) 8 v :: rest) | None => None end
        | None => bytewise tt
        end
      else bytewise tt
  end.
Lemma copy_facts3_eq : forall fuel sb sk db dk n, copy_facts3 fuel sb sk db dk n = copy_facts2 segs bc kx kx2 fuel sb sk db dk n.
Proof.
  induction fuel as [|f IH]; intros; [reflexivity|]. cbn [copy_facts3 copy_facts2]. cbv zeta. rewrite !IH.
  destruct (Z.leb 8 n); cbn [andb]; [|reflexivity].
  destruct (kread8e2 segs bc kx kx2 sb sk) as [v|]; [reflexivity|].
  destruct (APC.kread_bytesB segs bc 8 sb sk) as [bs|]; reflexivity.
Qed.
End Ctx3.

Definition copy_factsM2 (segs : list Segment) (fuel : nat) (k : list kentry) :=
  copy_facts3 segs (mkbc k) (mk_kix k) (AX2L.mk_kix2 k) fuel.
Lemma copy_factsM2_eq : copy_factsM2 = @APC.copy_facts.
Proof.
  apply functional_extensionality; intros segs. apply functional_extensionality; intros fuel. apply functional_extensionality; intros k.
  unfold copy_factsM2. repeat (apply functional_extensionality; intros ?). rewrite copy_facts3_eq, copy_facts2_eq, APC.copy_factsB_eqf'. reflexivity.
Qed.
End AX2Y.
