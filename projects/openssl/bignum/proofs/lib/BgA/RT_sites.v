(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac Mem Frame Cells Step Arr. 
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgA Require Import Layout RT_iface R_depot_defs R_unwind_defs R_unwind_chain RT_state.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition MAIN_PCS : list Z := [PC_MALLOC; PC_FREE; PC_CALLOC; PC_REALLOC].

Lemma prefixes_closed : forallb (fun s => forallb (fun k => existsb (site_eqb (firstn k s)) SITE_PREFIXES) (seq 0 (S (length s)))) SITE_TRACES = true.
Proof. vm_compute. reflexivity. Qed.
Lemma T_MAIN_incl : forall tr, In tr (traces_of MAIN_PCS SITE_TRACES) -> In tr T_MAIN.
Proof.
  intros tr H. unfold traces_of in H. apply in_flat_map in H as (pc & Hpc & H). apply in_flat_map in H as (s & Hs & H).
  apply in_map_iff in H as (p & E & Hp). subst tr. unfold prefixes in Hp. apply in_map_iff in Hp as (k & E & Hk). subst p.
  unfold T_MAIN. apply in_flat_map. exists pc. split; [exact Hpc|]. apply in_map.
  pose proof (proj1 (forallb_forall _ _) prefixes_closed s Hs) as X. cbv beta in X.
  pose proof (proj1 (forallb_forall _ _) X k Hk) as Y. cbv beta in Y.
  apply existsb_exists in Y as (t & Ht & E). apply site_eqb_eq in E. rewrite E. exact Ht.
Qed.

Lemma sites_ok : sites_okb 4096 MAIN_PCS 28 SITE_TRACES = true. Proof. vm_compute. reflexivity. Qed.

Lemma T_MAIN_rng64 : forall tr, In tr T_MAIN -> Forall (fun x => 0 <= x < 2 ^ 64) tr.
Proof.
  intros tr H. assert (X : forallb (fun t => forallb (fun x => (0 <=? x) && (x <? 2 ^ 64)) t) T_MAIN = true) by (vm_compute; reflexivity).
  pose proof (proj1 (forallb_forall _ _) X tr H) as Y. cbv beta in Y. apply Forall_forall. intros x Hx.
  pose proof (proj1 (forallb_forall _ _) Y x Hx) as Z0. cbv beta in Z0. apply andb_prop in Z0 as [Z1 Z2]. apply Z.leb_le in Z1. apply Z.ltb_lt in Z2. lia.
Qed.

Theorem site_trace_main : forall (m : mem) pc bot top (ra s0 sp : word),
  In pc MAIN_PCS -> unwind_ch m ra s0 sp -> top - 16 <= 2 ^ 63 ->
  exists ch tr, chain_cells [(0, bv_unsigned sp)] m (bv_unsigned s0) ch
    /\ unwind_trace pc 4096 bot top 30 (bv_unsigned sp) ((bv_unsigned ra, bv_unsigned s0) :: ch) = Some tr
    /\ In tr T_MAIN /\ (1 <= length tr <= TR_MAX)%nat.
Proof.
  intros m pc bot top ra s0 sp Hpc (ras & Hs & HU) Htop.
  pose proof (bv_unsigned_in_range 64 sp) as RSP.
  destruct (site_unwind USTACK_TOP [(0, bv_unsigned sp)] m MAIN_PCS SITE_TRACES 28 pc bot top 30 (bv_unsigned sp) (bv_unsigned ra)
              (bv_unsigned s0) ras sites_ok Hpc Hs ltac:(unfold USTACK_TOP; lia) Htop ltac:(lia) ltac:(cbn; lia) HU)
    as (ch & tr & CC & ET & HT & HL).
  { intros a Ha _. cbn [disjoint_from]. split; [right; exact Ha | exact I]. }
  exists ch, tr. split; [exact CC|]. split; [exact ET|]. split; [apply T_MAIN_incl; exact HT | cbn in HL; lia].
Qed.

