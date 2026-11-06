(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import PropExec CatExec StoreOk.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Definition wb_lay : Type := (word * list byte)%type.
Definition wb_l (a : word) (bs : list byte) : wb_lay := (a, bs).
Definition wb_mem : Type := word -> option byte.
Fixpoint wb_chain (m : word -> option byte) (l : list wb_lay) : word -> option byte :=
  match l with
  | [] => m
  | ly :: l' => wbytes (wb_chain m l') (fst ly) (snd ly)
  end.

Lemma wb_chain_grows : forall m l, mem_grows m (wb_chain m l).
Proof.
  intros m l. induction l as [|[a bs] l IH]; cbn [wb_chain fst snd]; [apply mem_grows_refl|].
  eapply mem_grows_trans; [exact IH | apply wbytes_grows].
Qed.

Lemma store_ok_wb_chain : forall segs n m l M a,
  M = wb_chain m l -> store_ok segs m a n = true -> store_ok segs M a n = true.
Proof. intros segs n m l M a -> H. eapply store_ok_mono; [apply wb_chain_grows | exact H]. Qed.

(* [comment removed for export] *)
Ltac wb_ulist M :=
  lazymatch M with
  | wbytes ?M' ?a ?bs => let l := wb_ulist M' in uconstr:(@cons wb_lay (wb_l a bs) l)
  | _ => uconstr:(@nil wb_lay)
  end.
Ltac wb_base M := lazymatch M with wbytes ?M' _ _ => wb_base M' | _ => M end.

Ltac store_ok_peel ::=
  repeat first
    [ lazymatch goal with
      | |- store_ok ?segs ?M ?a ?n = true =>
          lazymatch M with wbytes (wbytes _ _ _) _ _ => idtac end;
          let l := wb_ulist M in
          let m := wb_base M in
          refine (store_ok_wb_chain segs n m l M a (@eq_refl wb_mem M) _)
      end
    | eapply store_ok_mono; [apply wbytes_grows|]
    | eapply store_ok_mono; [apply write_to_mem_grows|]
    | eapply store_ok_mono; [apply apply_zeros_grows|]
    | eapply store_ok_mono; [apply apply_writes_grows|] ].
