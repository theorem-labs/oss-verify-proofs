(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatSim StoreOk AsanAcct HeapIface HeapIfaceA As0Tables
     ArtMem Pm5ArtLeaf Pm5ArtAllocG Pm5ArtPoison Pm5ArtRzLog Pm5ArtAllocA Pm5ArtInitCache Pm5ArtPopulate1 ArtRuns ArtRunsMem Pm5ArtCls Pm5ArtFp Pm5ArtClsRep Pm5ArtClsGfa2 Pm5ArtCellEx Pm5ArtByteCell Pm5ArtCellJoin
     Pm5ArtCARSpec Pm5ArtAlloc3Pure Pm5ArtDepotA Pm5ArtDepot ArtBridge Pm5ArtAllocate3 Pm5ArtSecAllocPost Pm5ArtSecRSpec Pm5ArtAllocate3L Pm5ArtMallocTop3L Pm5ArtInv Pm5ArtInvMallocPure Pm5ArtInvMallocFp Pm5ArtInvMalloc
     Pm5ArtInvMallocL.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Section RepLB.
Variable FSG : Type.
Variables (rn : art_run) (G : art_gs FSG) (LB : list (Z * Z)) (M M' : word -> option byte).
Variables (Sp n rz qz rs qr qn m8 nd q msz r : Z) (kb : nat) (b1 : Z).
Let nch := Z.of_nat (length (g_sec FSG G)).
Let cm := g_sec_committed FSG G.
Let ab := 4096 + r.
Let u := ab + rz.
Let WL := art_malloc3L_fp Sp (rn_t rn) (rn_parr rn) nch r msz (rn_l2 rn) (rn_blk rn) cm.

Hypothesis REP : art_alloc_rep FSG rn G LB M.
Hypothesis Hn : 8 <= n < 2 ^ 39.            (* [comment removed for export] *)
Hypothesis Erz16 : rz = 16 * qz.
Hypothesis Hqz : 2 <= qz <= 128.
Hypothesis En : n = 8 * qn + m8.
Hypothesis Hm8 : 0 <= m8 <= 7.
Hypothesis Ers : rs = 8 * qr.
Hypothesis Hrs : n <= rs <= n + 7.
Hypothesis Hsec : 65536 < rs + rz.
Hypothesis End : nd = rs + rz + rz.
Hypothesis Hq : 4096 * (q - 1) < nd <= 4096 * q.
Hypothesis Emsz : msz = 4096 * q + 4096.
Hypothesis HS : rn_HI rn + 4096 <= Sp - 4096.
Hypothesis Edep : g_depot FSG G = Datatypes.S kb.
Hypothesis GRANT : art_sec_grant3 (rn_HI rn) (rn_t rn) (rn_ctx rn) (rn_parr rn) (rn_spb rn) (rn_l2 rn) (rn_blk rn) msz r.
Hypothesis GLIVE : forall p, In p (art_live (g_log FSG G)) -> apart r msz (fst p) (snd p).
Hypothesis OUT : art_malloc_out_sec rn M M' Sp n rz qz qn m8 nd msz r nch cm kb b1.
Hypothesis LIVE : forall p, In p (art_live (g_log FSG G)) ->
  0 < fst p /\ 0 < snd p /\ fst p + snd p <= rn_HI rn /\ (fst p + snd p <= 0x7fff7000 \/ 0x10007fff8000 <= fst p)
  /\ (forall o, In o (art_objs rn) -> apart (fst p) (snd p) (fst o) (snd o)).

Lemma art_lrep_block_cases : forall b, In b LB ->
  (exists c0 w0, 1 <= c0 <= 30 /\ art_cptr_ok (AsanTab.class_size c0) (cl_au (g_cls FSG G c0)) w0 /\ 1 <= snd b
      /\ rn_spb rn + c0 * 2 ^ 32 + 16 * w0 + 16 <= fst b /\ fst b + snd b <= rn_spb rn + c0 * 2 ^ 32 + 16 * w0 + AsanTab.class_size c0)
  \/ (exists p, In p (art_live (g_log FSG G)) /\ fst p + 4096 <= fst b /\ fst b + snd b <= fst p + snd p /\ 1 <= snd b).
Proof.
  intros b Hb. pose proof REP as (_ & _ & _ & _ & CH & SEC & _ & _ & _ & BL & _).
  destruct (BL b Hb) as [(c0 & w0 & Hc0 & V0 & St0)|(s & Hs & Hq0 & Eu & En0)].
  - left. exists c0, w0. specialize (CH c0 Hc0). cbv zeta in CH. destruct CH as (_ & _ & _ & III). specialize (III w0 V0). rewrite St0 in III.
    destruct III as (_ & J2 & J3 & (bb & _ & _ & _ & _ & Hn0) & _). split; [exact Hc0|]. split; [exact V0|]. split; [lia|split; [exact J2|exact J3]].
  - right. destruct SEC as (_ & _ & _ & _ & _ & _ & _ & _ & SALL & _). destruct (In_nth_error _ _ Hs) as (i & Hi).
    destruct (SALL i s Hi) as (_ & P2 & _ & _ & _ & _ & P7 & P8 & P9 & _). rewrite Hq0 in P9. destruct P9 as (_ & (bb & _ & _ & _ & _ & Hn0) & _).
    exists (sc_map s, sc_msize s). cbn [fst snd]. rewrite <- Eu, <- En0. split; [exact P2|]. split; [lia|]. split; [exact P8|lia].
Qed.

Lemma art_lrep_blocks_apart_r : forall b, In b LB -> apart r msz (fst b) (snd b).
Proof.
  intros b Hb. destruct (art_lrep_block_cases b Hb) as [(c0 & w0 & Hc0 & V0 & Hn0 & J2 & J3)|(p & Hp & P1 & P2 & Hn0)].
  - pose proof (art_lchunk_in FSG rn G LB M rz r kb REP Edep c0 w0 Hc0 V0) as (K1 & K2). destruct GRANT as (_ & Ark & _). clear - K1 K2 Ark J2 J3 Hn0. unfold apart in *. lia.
  - pose proof (GLIVE p Hp) as AP. clear - AP P1 P2 Hn0. unfold apart in *. lia.
Qed.

Lemma art_lrep_blocks_apart : blocks_apart u n LB.
Proof.
  intros b Hb. pose proof (art_lrep_blocks_apart_r b Hb) as AP.
  destruct (art_lrep_num FSG rn G LB M rz qz rs qr nd q msz r kb REP Erz16 Hqz Ers Hsec End Hq Emsz Edep GRANT) as (_ & _ & _ & Hfit & Hrz & _).
  unfold u, ab in *. clear - AP Hfit Hrz Hn Hrs End. unfold apart in AP. lia.
Qed.

Lemma art_lrep_nfp_block : forall b a, In b LB -> fst b <= a < fst b + snd b -> art_out WL a.
Proof.
  intros b a Hb Ha. destruct (art_lrep_block_cases b Hb) as [(c0 & w0 & Hc0 & V0 & Hn0 & J2 & J3)|(p & Hp & P1 & P2 & Hn0)].
  - pose proof (art_lchunk_in FSG rn G LB M rz r kb REP Edep c0 w0 Hc0 V0) as (K1 & K2).
    apply (art_gap_out WL a 1 a); [|lia].
    apply (art_lgap_kspace FSG rn G LB M Sp rz qz rs qr nd q msz r kb REP Erz16 Hqz Ers Hsec End Hq Emsz HS Edep GRANT a 1); clear - K1 K2 J2 J3 Ha Hn0; lia.
  - apply (art_gap_out WL a 1 a); [|lia].
    apply (art_lgap_grant FSG rn G LB M Sp rz qz rs qr nd q msz r kb REP Erz16 Hqz Ers Hsec End Hq Emsz HS Edep GRANT GLIVE LIVE p a 1); [lia|exact Hp|clear - P1 Ha; lia|clear - P2 Ha; lia].
Qed.
End RepLB.
