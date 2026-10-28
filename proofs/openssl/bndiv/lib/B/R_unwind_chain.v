(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac ImageA Arr Walk.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import R_small R_thread R_cache_defs R_unwind_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Notation mem := (word -> option byte).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition fp_stop (f fp : Z) : Prop := fp <= f \/ fp mod 8 <> 0 \/ 2 ^ 63 <= fp.

Fixpoint chain_ok (f : Z) (ch : list (Z * Z)) : Prop :=
  match ch with
  | [] => False
  | (ra, fp) :: ch' =>
      match ch' with
      | [] => fp_stop f fp
      | _ :: _ => f + 16 <= fp /\ fp mod 8 = 0 /\ chain_ok fp ch'
      end
  end.

Lemma fp_stop_fr_ok : forall f hi fp, hi <= 2 ^ 63 -> fp_stop f fp -> fr_ok f hi fp = false.
Proof.
  intros f hi fp Hhi [H|[H|H]]; unfold fr_ok.
  - rewrite (proj2 (Z.ltb_ge f fp)) by lia. reflexivity.
  - rewrite (proj2 (Z.eqb_neq (fp mod 8) 0)) by exact H. rewrite andb_false_r. reflexivity.
  - rewrite (proj2 (Z.ltb_ge fp hi)) by lia. rewrite andb_false_r. reflexivity.
Qed.

Lemma uw_loop_prefix : forall pc page hi maxd ch f acc,
  chain_ok f ch -> hi <= 2 ^ 63 -> Forall (fun r => page <= r /\ r <> pc) (map fst ch) ->
  Z.of_nat (length acc) + Z.of_nat (length ch) <= maxd ->
  exists k, (1 <= k <= length ch)%nat /\ uw_loop pc page hi maxd ch f acc = Some (acc ++ firstn k (map fst ch)).
Proof.
  intros pc page hi maxd ch. induction ch as [|[ra fp] ch IH]; intros f acc HC Hhi HF HL; [destruct HC|].
  cbn [map fst] in HF. apply Forall_cons_iff in HF as [(Hra & Hne) HF]. cbn [length] in HL.
  cbn [uw_loop]. rewrite (proj2 (Z.leb_gt maxd (Z.of_nat (length acc)))) by lia.
  rewrite (proj2 (Z.ltb_ge ra page)) by lia. rewrite (proj2 (Z.eqb_neq ra pc)) by exact Hne.
  destruct ch as [|[ra2 fp2] ch'].
  - cbn [chain_ok] in HC. rewrite (fp_stop_fr_ok f hi fp Hhi HC). exists 1%nat. cbn [length map fst firstn]. split; [lia | reflexivity].
  - cbn [chain_ok] in HC. destruct HC as (H1 & H2 & HC).
    destruct (fr_ok f hi fp).
    + destruct (IH fp (acc ++ [ra]) HC Hhi HF) as (k & Hk & E).
      { rewrite length_app. cbn [length] in *. lia. }
      exists (S k). split; [cbn [length] in *; lia|]. rewrite E. rewrite <- app_assoc. reflexivity.
    + exists 1%nat. split; [cbn [length]; lia | reflexivity].
Qed.

Lemma unwind_trace_prefix : forall pc page bot top maxd bp ch,
  chain_ok bp ch -> top - 16 <= 2 ^ 63 -> Forall (fun r => page <= r /\ r <> pc) (map fst ch) ->
  1 + Z.of_nat (length ch) <= maxd ->
  exists k, (k <= length ch)%nat /\ unwind_trace pc page bot top maxd bp ch = Some (pc :: firstn k (map fst ch)).
Proof.
  intros pc page bot top maxd bp ch HC Htop HF HL. unfold unwind_trace.
  destruct (top / 4096 =? 0); [exists 0%nat; split; [lia | reflexivity]|].
  destruct (fr_ok bot (top - 16) bp); [| exists 0%nat; split; [lia | reflexivity]].
  destruct (uw_loop_prefix pc page (top - 16) maxd ch bp [pc] HC Htop HF) as (k & Hk & E); [cbn [length]; lia|].
  exists k. split; [lia | exact E].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition prefixes (l : list Z) : list (list Z) := map (fun k => firstn k l) (seq 0 (S (length l))).

Lemma in_prefixes : forall (l : list Z) k, (k <= length l)%nat -> In (firstn k l) (prefixes l).
Proof. intros l k Hk. unfold prefixes. apply in_map_iff. exists k. split; [reflexivity|]. apply in_seq. lia. Qed.

(* [comment removed for export] *)
Definition traces_of (pcs : list Z) (sites : list (list Z)) : list (list Z) :=
  flat_map (fun pc => flat_map (fun s => map (cons pc) (prefixes s)) sites) pcs.

Lemma in_traces_of : forall pcs sites pc s k, In pc pcs -> In s sites -> (k <= length s)%nat ->
  In (pc :: firstn k s) (traces_of pcs sites).
Proof.
  intros pcs sites pc s k Hpc Hs Hk. unfold traces_of. apply in_flat_map. exists pc. split; [exact Hpc|].
  apply in_flat_map. exists s. split; [exact Hs|]. apply in_map. apply in_prefixes. exact Hk.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint uw_chain (TOPB : Z) (m : mem) (f fp : Z) (ras : list Z) : Prop :=
  match ras with
  | [] => fp_stop f fp
  | r :: ras' =>
      f + 16 <= fp /\ fp mod 8 = 0 /\ fp <= TOPB
      /\ exists fp', 0 <= fp' < 2 ^ 64
                     /\ rw_cells bsegs m (fp + -16) [C8 (Z_to_bv 64 fp'); C8 (Z_to_bv 64 r)] /\ uw_chain TOPB m fp fp' ras'
  end.

Lemma uw_chain_cells : forall TOPB W (m : mem) ras f fp ra,
  TOPB <= 2 ^ 63 -> 0 <= f -> uw_chain TOPB m f fp ras ->
  (forall a, f <= a -> a + 16 <= TOPB -> disjoint_from W a 16) ->
  Forall (fun r => 0 <= r < 2 ^ 64) ras ->
  exists ch, map fst ch = ras /\ chain_cells W m fp ch /\ chain_ok f ((ra, fp) :: ch).
Proof.
  intros TOPB W m ras. induction ras as [|r ras IH]; intros f fp ra HT Hf HU HW HR.
  - exists []. cbn in *. split; [reflexivity|]. split; [exact I | exact HU].
  - cbn [uw_chain] in HU. destruct HU as (H1 & H2 & H3 & fp' & Hfp' & HC & HU).
    apply Forall_cons_iff in HR as [Hr HR].
    destruct (IH fp fp' r HT ltac:(lia) HU) as (ch & E & CC & OK); [intros a Ha Ha'; apply HW; lia | exact HR|].
    exists ((r, fp') :: ch). split; [cbn [map fst]; rewrite E; reflexivity|]. split.
    + cbn [chain_cells]. split; [exact HC|]. split; [lia|]. split; [apply HW; lia | exact CC].
    + change (f + 16 <= fp /\ fp mod 8 = 0 /\ chain_ok fp ((r, fp') :: ch)). split; [exact H1|]. split; [exact H2 | exact OK].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition sites_okb (page : Z) (pcs : list Z) (k : nat) (sites : list (list Z)) : bool :=
  forallb (fun s => (length s <=? k)%nat
                    && forallb (fun r => (0 <=? r) && (page <=? r) && (r <? 2 ^ 64) && forallb (fun pc => negb (r =? pc)) pcs) s) sites.

Lemma sites_okb_spec : forall page pcs k sites s pc, sites_okb page pcs k sites = true -> In s sites -> In pc pcs ->
  (length s <= k)%nat /\ Forall (fun r => page <= r /\ r <> pc) s /\ Forall (fun r => 0 <= r < 2 ^ 64) s.
Proof.
  intros page pcs k sites s pc H Hs Hpc.
  unfold sites_okb in H. pose proof (proj1 (forallb_forall _ _) H s Hs) as X. cbv beta in X.
  apply andb_prop in X as [X1 X2]. apply Nat.leb_le in X1. split; [exact X1|].
  split; apply Forall_forall; intros r Hr; pose proof (proj1 (forallb_forall _ _) X2 r Hr) as Y; cbv beta in Y;
    apply andb_prop in Y as [Y Y3]; apply andb_prop in Y as [Y Y2]; apply andb_prop in Y as [Y0 Y1];
    apply Z.leb_le in Y0; apply Z.leb_le in Y1; apply Z.ltb_lt in Y2.
  - split; [exact Y1|]. pose proof (proj1 (forallb_forall _ _) Y3 pc Hpc) as Z0. cbv beta in Z0.
    apply negb_true_iff in Z0. apply Z.eqb_neq in Z0. exact Z0.
  - lia.
Qed.

Theorem site_unwind : forall TOPB W (m : mem) pcs sites kmax pc bot top maxd sp ra s0 ras,
  sites_okb 4096 pcs kmax sites = true -> In pc pcs -> In (ra :: ras) sites ->
  TOPB <= 2 ^ 63 -> top - 16 <= 2 ^ 63 -> 0 <= sp -> 2 + Z.of_nat kmax <= maxd ->
  uw_chain TOPB m sp s0 ras ->
  (forall a, sp <= a -> a + 16 <= TOPB -> disjoint_from W a 16) ->
  exists ch tr, chain_cells W m s0 ch
    /\ unwind_trace pc 4096 bot top maxd sp ((ra, s0) :: ch) = Some tr
    /\ In tr (traces_of pcs sites) /\ (1 <= length tr <= 1 + kmax)%nat.
Proof.
  intros TOPB W m pcs sites kmax pc bot top maxd sp ra s0 ras OKB Hpc Hs HT Htop Hsp Hmax HU HW.
  destruct (sites_okb_spec 4096 pcs kmax sites (ra :: ras) pc OKB Hs Hpc) as (HL & HF & HR).
  apply Forall_cons_iff in HR as [Hra HR].
  destruct (uw_chain_cells TOPB W m ras sp s0 ra HT Hsp HU HW HR) as (ch & E & CC & OK).
  assert (EM : map fst ((ra, s0) :: ch) = ra :: ras) by (cbn [map fst]; rewrite E; reflexivity).
  assert (EL : length ((ra, s0) :: ch) = length (ra :: ras)) by (rewrite <- EM, length_map; reflexivity).
  destruct (unwind_trace_prefix pc 4096 bot top maxd sp ((ra, s0) :: ch) OK Htop) as (k & Hk & ET).
  { rewrite EM. exact HF. }
  { rewrite EL. lia. }
  exists ch, (pc :: firstn k (ra :: ras)). split; [exact CC|]. split; [rewrite <- EM; exact ET|]. split.
  - apply in_traces_of; [exact Hpc | exact Hs | rewrite <- EL; exact Hk].
  - cbn [length]. rewrite length_firstn. rewrite EL in Hk. lia.
Qed.
