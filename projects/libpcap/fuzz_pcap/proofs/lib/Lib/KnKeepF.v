(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool FunctionalExtensionality.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require Import AxSymExec3 AxSymExec3Sound AxSymExec3B AsanPlanCore AxSymExec3F.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBlock__Lib. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBlock__Lib.MallocSymAux.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Module KKF.
Import AX2. Import AX2S. Import AX2B.

Definition keep_bpB (md : mmode) (bc : bctx) (sp : sprep) (ub : expr) (uk : Z) (un : expr) (K : kentry) : bool :=
  is_fact_b K
  || (match md with MGrow => kwr_b K | MUnmap => kimg_b K end)
  || APC.kentry_apart_bpB bc sp ub uk un K.

Definition kn_keepM (md : mmode) (allkn kn : list kentry) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let bc := mkbc allkn in
  let sp := mk_sprepB bc ub uk un in
  List.filter (keep_bpB md bc sp ub uk un) kn.

Lemma kapart_bp_eq : forall allkn ub uk un K,
  APC.kentry_apart_bp allkn (mk_sprep allkn ub uk un) ub uk un K = kapart_b allkn ub uk un K.
Proof.
  intros allkn ub uk un K.
  destruct K as [[b k] w v|[b k] l|[b k] l bk|lo hi|e m|e lo hi|[b k] n|c1 m1 c2 m2|[b k] l c|[b k] l];
    cbn [APC.kentry_apart_bp kapart_b]; rewrite ?ranges_apart_p_eq; reflexivity.
Qed.

Lemma kn_keepM_eq : kn_keepM = kn_keep.
Proof.
  apply functional_extensionality; intros md. apply functional_extensionality; intros allkn.
  apply functional_extensionality; intros kn. apply functional_extensionality; intros ub.
  apply functional_extensionality; intros uk. apply functional_extensionality; intros un.
  unfold kn_keepM, kn_keep. rewrite mk_sprepB_eqf.
  induction kn as [|K rest IH]; [reflexivity|].
  cbn [List.filter]. rewrite IH. unfold keep_bpB, keep_b.
  rewrite APC.kentry_apart_bpB_eqf, kapart_bp_eq. reflexivity.
Qed.

End KKF.

(* [comment removed for export] *)
Ltac kn_head t := lazymatch t with ?f _ => kn_head f | _ => t end.
Ltac kn_fast :=
  rewrite <- ?KKF.kn_keepM_eq;
  lazymatch goal with
  | |- context [KKF.kn_keepM] => idtac
  | |- ?l = _ => let h := kn_head l in (try (progress unfold h)); rewrite <- ?KKF.kn_keepM_eq
  end;
  lazymatch goal with |- @eq ?T _ ?b => vm_cast_no_check (@eq_refl T b) end.

(* [comment removed for export] *)
Fixpoint kl_eqb (a b : list AX2.kentry) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => APC.kentry_eqb x y && kl_eqb a' b'
  | _, _ => false
  end.
Ltac nf_share K t :=
  let v := eval vm_compute in t in
  let n := eval vm_compute in (Nat.sub (List.length v) (List.length K)) in
  let ok := eval vm_compute in (kl_eqb (List.skipn n v) K) in
  lazymatch ok with
  | true => let p := eval vm_compute in (List.firstn n v) in
            let w := eval cbn [List.app] in (List.app p K) in exact w
  | _ => exact v
  end.
Ltac nf_run K t :=
  let ok := eval vm_compute in (kl_eqb (AX2.s_know (fst (fst t))) K) in
  lazymatch ok with
  | true =>
      let v := eval vm_compute in
        (let '(ss, scs, scr) := t in
         (AX2.SSR (AX2.s_pc ss) (AX2.s_regs ss) (AX2.s_log ss) [] (AX2.s_next ss) (AX2.s_resv ss), scs, scr)) in
      lazymatch v with
      | (AX2.SSR ?pc ?rg ?lg _ ?nx ?rv, ?scs, ?scr) => exact (AX2.SSR pc rg lg K nx rv, scs, scr)
      end
  | _ => let v := eval vm_compute in t in exact v
  end.
(* [comment removed for export] *)
Ltac nf_rope R t :=
  let ok := eval vm_compute in (kl_eqb t R) in
  lazymatch ok with
  | true => exact R
  | _ => let v := eval vm_compute in t in exact v
  end.
Ltac nf_car R t :=
  let ok := eval vm_compute in (kl_eqb (fst (fst t)) R) in
  lazymatch ok with
  | true =>
      let cs := eval vm_compute in (snd (fst t)) in
      let hs := eval vm_compute in (snd t) in
      exact (R, cs, hs)
  | _ => let v := eval vm_compute in t in exact v
  end.
