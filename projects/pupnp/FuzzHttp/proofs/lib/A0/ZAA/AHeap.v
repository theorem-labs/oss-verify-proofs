(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts AllocA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAA Require Import AEnv ADepot ALayout PEnv LJ APrim APrimSpec2 APrimQ ASec AQuar.
Import ListNotations.
Open Scope Z_scope.

Record astA := mkASA {
  as_H : word -> bool;
  as_pages : list word;
  as_lay : alayout;
  as_penv : penv;
  as_prim : prim;
  as_sec : asec;
  as_quar : aquar;
  as_depot : list Z;
  as_dtotal : Z;
  as_live : list qchunk
}.

Definition am_ghost0 (s : astA) : (word -> bool) * list word := (as_H s, as_pages s).

Section H.
Context {HC : HasCeiling}.

Definition lc_user (AL : alayout) (ch : qchunk) : Z := qc_hdr AL ch + 16.
Definition blk_of (AL : alayout) (ch : qchunk) : block Z := (lc_user AL ch, lc_user AL ch, qc_n ch).

Definition lchunk_rep (AL : alayout) (m : mem) (ch : qchunk) : Prop :=
  let B := qc_blk AL ch in let M := qc_hdr AL ch in let n := qc_n ch in let rz := qc_rz ch in
  (exists bits actx, Z.land (bv_unsigned bits) 3 = 1
                     /\ rw_cells asegs m M [CB 4 [Z_to_bv 8 2; bits; Z_to_bv 8 0; Z_to_bv 8 0]; C4 (wz n); C8 actx])
  /\ (16 < rz -> rw_cells asegs m B [C8 (wz CHUNK_MAGIC); C8 (wz M)] /\ exists j, rw_cells asegs m (B + 16) [CB (Z.to_nat (rz - 32)) j])
  /\ (exists ub, rw_cells asegs m (M + 16) [CB (Z.to_nat n) ub])
  /\ (exists j, rw_cells asegs m (M + 16 + n) [CB (Z.to_nat (qc_bsize ch - rz - n)) j])
  /\ rw_cells asegs m (sh B) [CB (Z.to_nat (rz / 8)) (fa_bytes (rz / 8))]
  /\ rw_cells asegs m (sh (M + 16)) (shadow_cells (block_shadow n))
  /\ rw_cells asegs m (sh (M + 16 + rup8 n)) [CB (Z.to_nat ((qc_bsize ch - rz - rup8 n) / 8)) (fa_bytes ((qc_bsize ch - rz - rup8 n) / 8))]
  /\ match qc_kind ch with
     | QPrim _ _ => True
     | QSec sc => (exists j, rw_cells asegs m (sc_beg sc + 32) [CB 4064 j]) /\ rw_cells asegs m (sh (sc_beg sc)) [CB 512 (fa_bytes 512)]
     end.

Definition prim_of (ch : qchunk) : list (Z * Z) := match qc_kind ch with QPrim c v => [(c, v)] | QSec _ => [] end.
Definition held_of (s : astA) : list (Z * Z) :=
  map (fun b => (K_BCLASS, qb_v b)) (q_loc (as_quar s) ++ q_glob (as_quar s))
  ++ flat_map prim_of (q_all_chunks (as_quar s)) ++ flat_map prim_of (as_live s).

Definition sec_of (ch : qchunk) : list schunk := match qc_kind ch with QPrim _ _ => [] | QSec sc => [sc] end.

Definition RHEAP_A0 (s : astA) (LB : list (block Z)) (m : mem) : Prop :=
  let AL := as_lay s in
  Permutation LB (map (blk_of AL) (as_live s))
  /\ alayout_ok AL
  /\ mclean (as_H s) m /\ shvis (as_H s) m
  /\ poison_env (as_penv s) m /\ thread_env (al_thread AL) m
  /\ RPRIM AL (as_prim s) m /\ prim_ok (as_prim s)
  /\ RSEC AL (as_sec s) m
  /\ RQUAR AL (as_quar s) m
  /\ RDEPOT (al_depot AL) (as_depot s) (as_dtotal s) m
  /\ held_ok (as_prim s) (held_of s)
  /\ Permutation (se_chunks (as_sec s)) (flat_map sec_of (q_all_chunks (as_quar s)) ++ flat_map sec_of (as_live s))
  /\ Forall qchunk_wf (as_live s)
  /\ Forall (lchunk_rep AL m) (as_live s).

Definition prim0 : prim := mkPRIM (repeat pclass0 32) false 0 0.
Definition as0 (H0 : word -> bool) (P0 : list word) (AL : alayout) (E : penv) (hs0 : list Z) (tot0 : Z) : astA :=
  mkASA H0 P0 AL E prim0 (mkSEC [] 0) (mkAQ [] []) hs0 tot0 [].

#[using="Type"] Lemma am_ghost0_as0 : forall H0 P0 AL E hs0 tot0, am_ghost0 (as0 H0 P0 AL E hs0 tot0) = (H0, P0).
Proof. reflexivity. Qed.

#[using="Type"] Lemma RHEAP_A0_init : forall H0 P0 AL E hs0 tot0 m,
  alayout_ok AL -> mclean H0 m -> shvis H0 m -> poison_env E m -> thread_env (al_thread AL) m ->
  RPRIM AL prim0 m -> RSEC AL (mkSEC [] 0) m -> RQUAR AL (mkAQ [] []) m -> RDEPOT (al_depot AL) hs0 tot0 m ->
  RHEAP_A0 (as0 H0 P0 AL E hs0 tot0) [] m.
Proof.
  intros H0 P0 AL E hs0 tot0 m AO MC SV PE TE RP RS RQ RD. unfold RHEAP_A0, as0. cbn [as_lay as_H as_penv as_prim as_sec as_quar as_depot as_dtotal as_live].
  split; [constructor|]. split; [exact AO|]. split; [exact MC|]. split; [exact SV|]. split; [exact PE|]. split; [exact TE|].
  split; [exact RP|]. split; [intros _ c Hc; unfold prim0, get_cls; cbn [pr_cls]; destruct (nth_in_or_default (Z.to_nat c) (repeat pclass0 32) pclass0) as [IN| ->]; [apply repeat_spec in IN; rewrite IN|]; reflexivity|].
  split; [exact RS|]. split; [exact RQ|]. split; [exact RD|].
  split; [split; [constructor| constructor]|]. split; [constructor|]. split; constructor.
Qed.
End H.
