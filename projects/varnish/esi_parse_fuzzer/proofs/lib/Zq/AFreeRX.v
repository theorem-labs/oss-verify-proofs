(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ADepotM.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts ARtSnjd AMalmys.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AQWf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AQWf AFreeB1 ATransp AFreeB3 AFreeRS ARt4z85.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSnjd OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalmys OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AQWf.AQOps OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AQWf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeB1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ATransp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeB3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeRS OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt4z85.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
#[local] Notation WF := (WF AL_pboth).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Notation wz z := (Z_to_bv 64 z) (only parsing).
Ltac kung_all := unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kShadowOffset, kRegionSize, kSpaceSize, kFreeArrayOffset,
                        kHighShadowMapBeg, kSpaceReserve, kMaxSize in *.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition bsl (sb : Z) (l : list batch) : list (Z * Z) := map (fun b => (batch_addr sb b, batch_bytes b)) l.

Lemma bsl_length : forall sb l, length (bsl sb l) = length l.
Proof. intros. unfold bsl. apply length_map. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lsum_bsl : forall sb l, lsum (bsl sb l) = q_bytes l.
Proof. intros sb. induction l as [|b l IH]; [reflexivity|]. unfold bsl in *. cbn [map lsum]. rewrite q_bytes_cons, IH. reflexivity. Qed.
Lemma baddr_bsl : forall sb l i d, (i < length l)%nat -> baddr (bsl sb l) i = batch_addr sb (nth i l d).
Proof.
  intros sb l i d Hi. unfold baddr, bsl. rewrite map_map. cbn [fst].
  rewrite (nth_indep _ 0 (batch_addr sb d)) by (rewrite length_map; exact Hi). rewrite map_nth. reflexivity.
Qed.
Lemma bsz_bsl : forall sb l i d, (i < length l)%nat -> bsz (bsl sb l) i = batch_bytes (nth i l d).
Proof.
  intros sb l i d Hi. unfold bsz, bsl. rewrite map_map. cbn [snd].
  rewrite (nth_indep _ 0 (batch_bytes d)) by (rewrite length_map; exact Hi). rewrite map_nth. reflexivity.
Qed.
Lemma baddr_bsl_cons : forall sb b l, baddr (bsl sb (b :: l)) 0 = batch_addr sb b.
Proof. reflexivity. Qed.
Lemma baddr_over : forall bs i, (length bs <= i)%nat -> baddr bs i = 0.
Proof. intros bs i H. unfold baddr. apply nth_overflow. rewrite length_map. exact H. Qed.
Lemma firstn_bsl : forall sb l k, firstn k (bsl sb l) = bsl sb (firstn k l).
Proof. intros. unfold bsl. rewrite firstn_map. reflexivity. Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma npop_rsplit : forall sb l min, 
  let k := npop min (q_bytes l) (bsl sb l) in fst (rsplit l min) = firstn k l /\ snd (rsplit l min) = skipn k l.
Proof.
  intros sb l min. cbv zeta. induction l as [|b l IH]; [split; reflexivity|].
  unfold bsl. cbn [map npop rsplit]. fold (bsl sb l).
  rewrite q_bytes_cons. replace (batch_bytes b + q_bytes l - batch_bytes b) with (q_bytes l) by lia.
  destruct (Z.leb_spec (batch_bytes b + q_bytes l) min) as [LE|GT]; destruct (Z.ltb_spec min (batch_bytes b + q_bytes l)) as [LT|GE]; try lia.
  - cbn [firstn skipn]. split; reflexivity.
  - destruct (rsplit l min) as [R rest]. cbn [fst snd] in IH |- *. destruct IH as [-> ->]. cbn [firstn skipn]. split; reflexivity.
Qed.
Lemma npop_length : forall sb l min, (npop min (q_bytes l) (bsl sb l) <= length l)%nat.
Proof. intros. pose proof (npop_le_length min (bsl sb l) (q_bytes l)) as H. rewrite bsl_length in H. exact H. Qed.

(* [comment removed for export] *)
Lemma batches_repr_nth : forall (mm : mem) sb l i b d,
  batches_repr LPA mm sb l -> nth_error l i = Some b ->
  let a := batch_addr sb b in
  u64_at rsegs mm (a + off_qb_next) (match nth_error l (S i) with Some b' => batch_addr sb b' | None => 0 end) /\
  u64_at rsegs mm (a + off_qb_size) (batch_bytes b) /\
  u64_at rsegs mm (a + off_qb_count) (Z.of_nat (length (ba_entries b))) /\
  (forall j e, nth_error (ba_entries b) j = Some e -> u64_at rsegs mm (a + off_qb_batch (Z.of_nat j)) (hdr_of sb (qe_chunk e) (qe_n e))) /\
  mapped mm a kQuarantineBatchBytes /\ nth i l d = b.
Proof.
  intros mm sb l. induction l as [|b0 l IH]; intros i b d BR H; [destruct i; discriminate|].
  cbn [batches_repr] in BR. (first [ dand6 BR as Hn Hs Hc He Hm Hr | destruct BR as (Hn & Hs & Hc & He & Hm & Hr) ]).
  destruct i as [|i].
  - cbn in H. injection H as ->. cbv zeta. cbn [nth_error nth]. destruct l as [|b' l']; (split; [exact Hn| split; [exact Hs| split; [exact Hc| split; [exact He| split; [exact Hm| reflexivity]]]]]).
  - cbn in H. cbn [nth]. exact (IH i b d Hr H).
Qed.

Lemma ebytes_bound : forall M es, (forall e, In e es -> 0 <= qe_bytes e <= M) -> 0 <= ebytes es <= Z.of_nat (length es) * M.
Proof.
  intros M es. induction es as [|e es IH]; intros EW; [cbn; lia|].
  rewrite ebytes_cons. cbn [length]. rewrite Nat2Z.inj_succ.
  pose proof (EW e ltac:(left; reflexivity)). specialize (IH ltac:(intros x Hx; apply EW; right; exact Hx)). nia.
Qed.

Section Chain.
Context {Clg : Ceiling}.
  Variables (A : AState) (v : mem).
  Hypothesis AR : WF A /\ @arepr _ DepotRepL LPA AL_pboth [] A v.
  #[warnings="-notation-for-abbreviation"] Local Notation sb := (a_sb A).

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma bchain_of : forall l, batches_repr LPA v sb l -> bchain v (bsl sb l).
  Proof.
    intros l BR i Hi. rewrite bsl_length in Hi.
    destruct (nth_error l i) as [b|] eqn:E; [| apply nth_error_None in E; lia].
    pose proof (batches_repr_nth v sb l i b (BA 0 []) BR E) as X. cbv zeta in X. (first [ dand6 X as Hn Hs _ _ Hm Hnth | destruct X as (Hn & Hs & _ & _ & Hm & Hnth) ]).
    rewrite (baddr_bsl sb l i (BA 0 []) Hi), (bsz_bsl sb l i (BA 0 []) Hi), Hnth.
    assert (NX : baddr (bsl sb l) (S i) = match nth_error l (S i) with Some b' => batch_addr sb b' | None => 0 end).
    { destruct (nth_error l (S i)) as [b'|] eqn:E2.
      - pose proof (nth_error_Some_lt _ _ _ E2) as L2. rewrite (baddr_bsl sb l (S i) (BA 0 []) L2).
        rewrite (nth_error_nth' l (BA 0 []) L2) in E2. injection E2 as ->. reflexivity.
      - apply baddr_over. rewrite bsl_length. apply nth_error_None. exact E2. }
    rewrite NX. unfold off_qb_next, off_qb_size in Hn, Hs. rewrite Z.add_0_r in Hn.
    apply ro_rw.
    - split; [exact (conj I (conj I I))|]. cbn [cells_bytes cbytes app]. rewrite app_nil_r. apply bytes_at_app. split; [exact Hn|]. rewrite length_le8. exact Hs.
    - cbn [cells_size csize Nat.add]. intros q Hq. apply Hm. unfold kQuarantineBatchBytes. lia.
  Qed.
End Chain.
