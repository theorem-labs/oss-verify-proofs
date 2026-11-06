(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From stdpp Require Import base list.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Ceiling Arr SysStep.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts ATac IcptA0 AllocA0 ATacAp.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7A0 Require Import ShadowKit.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.AW Require Import HttpAllocA HttpRepA AWKit HObjA HObjK H_list_access H_ListFind H_freelist H_ListAddTail HPrepA.
Import ListNotations.
Open Scope Z_scope.

Section W.
Context {HC : HasCeiling}.
Variable FI : fs_if.
Variable AI : am_if FI.
Local Notation K := (am_K FI AI).
Local Notation BLK := (block K).
Local Notation BL := (list (block K)).
Local Notation hdr := (hdr FI AI).

Fixpoint ns3_of (ns : list (BLK * Z)) (hs : list hdr) : list (Z * Z * Z) :=
  match ns, hs with
  | (b, it) :: ns', h :: hs' => (blk_addr b, it, hid FI AI h) :: ns3_of ns' hs'
  | _, _ => []
  end.

#[using="Type"] Lemma ns3_of_nil_iff : forall ns hs, length ns = length hs -> (ns3_of ns hs = [] <-> ns = []).
Proof. intros [|[b it] ns] [|h hs] HL; cbn in *; split; intros E; try reflexivity; try discriminate; lia. Qed.

#[using="Type"] Lemma ns3_of_In : forall (ns : list (BLK * Z)) (hs : list hdr) N it id,
  map snd ns = map (hA FI AI) hs -> In (N, it, id) (ns3_of ns hs) ->
  exists b h, In (b, it) ns /\ In h hs /\ N = blk_addr b /\ it = hA FI AI h /\ id = hid FI AI h.
Proof.
  induction ns as [|[b0 it0] ns IH]; intros hs N it id IT HI; destruct hs as [|h0 hs]; cbn [ns3_of] in HI; try destruct HI.
  - cbn [map] in IT. injection IT as E1 E2. inversion H; subst. exists b0, h0. cbn [snd]. repeat split; try reflexivity; left; reflexivity.
  - cbn [map] in IT. injection IT as E1 E2. destruct (IH hs N it id E2 H) as (b & h & H1 & H2 & H3).
    exists b, h. split; [right; exact H1|]. split; [right; exact H2| exact H3].
Qed.

#[using="Type"] Lemma ns3_of_hdr : forall (ns : list (BLK * Z)) (hs : list hdr) h,
  length ns = length hs -> In h hs -> exists N it, In (N, it, hid FI AI h) (ns3_of ns hs).
Proof.
  induction ns as [|[b0 it0] ns IH]; intros hs h HL Hh; destruct hs as [|h0 hs]; cbn [length] in HL; try discriminate; [destruct Hh|].
  cbn [ns3_of]. destruct Hh as [<-|Hh]; [exists (blk_addr b0), it0; left; reflexivity|].
  destruct (IH hs h ltac:(lia) Hh) as (N & it & HI). exists N, it. right. exact HI.
Qed.

#[using="Type"] Lemma lsegA_of_dlseg : forall (ns : list (BLK * Z)) (hs : list hdr) m pv TAIL,
  dlseg FI AI m ns pv TAIL -> hdrs_mem FI AI m hs -> map snd ns = map (hA FI AI) hs ->
  (forall h, In h hs -> hA FI AI h <> 0) ->
  lsegA m (ns3_of ns hs) (hd_addr FI AI ns TAIL) pv TAIL.
Proof.
  induction ns as [|[b it] ns IH]; intros hs m pv TAIL DL HM IT NZ; destruct hs as [|h hs]; cbn [map] in IT; try discriminate; cbn [ns3_of lsegA HObjA.hd_addr]; [reflexivity|].
  injection IT as E1 E2. cbn [HObjA.dlseg] in DL. destruct DL as (SZ & A0 & AT & ITR & NC & DL').
  cbn [HObjA.hdrs_mem] in HM. destruct HM as (((pad & HCc) & _) & HP0 & HM').
  split; [reflexivity|]. split; [exact AT|]. split; [exact A0|]. split; [subst it; apply NZ; left; reflexivity|].
  split; [unfold hdro_pure in HP0; lia|].
  exists (hd_addr FI AI ns TAIL), (wz (nA FI AI h)), (wz (nlen FI AI h)), pad.
  split; [exact NC|]. split; [subst it; exact HCc|].
  apply IH; [exact DL'| exact HM'| exact E2| intros h' Hh'; apply NZ; right; exact Hh'].
Qed.

#[using="Type"] Lemma hdrs_mem_In : forall (hs : list hdr) m h, hdrs_mem FI AI m hs -> In h hs -> hdro_mem FI AI m h /\ hdro_pure FI AI h.
Proof.
  induction hs as [|h0 hs IH]; intros m h HM HI; [destruct HI|]. cbn [HObjA.hdrs_mem] in HM. destruct HM as (H1 & H2 & HM').
  destruct HI as [<-|HI]; [split; assumption| exact (IH m h HM' HI)].
Qed.
#[using="Type"] Lemma hdrs_blocks_In : forall (hs : list hdr) h b, In h hs -> In b (hblocks FI AI h) -> In b (hdrs_blocks FI AI hs).
Proof.
  intros hs h b Hh Hb. unfold hdrs_blocks. apply in_concat. exists (hblocks FI AI h). split; [apply in_map; exact Hh| exact Hb].
Qed.

#[using="Type"] Lemma blk_objA : forall s (LB : BL) m (b : BLK), RHEAP_A FI AI s LB m -> In b LB -> objA m (blk_addr b) (blk_size b).
Proof.
  intros s LB m b HR Hb. destruct (am_block_range FI AI s LB m b HR Hb) as (R1 & R2 & R3 & R4 & R5 & R6 & R7).
  split; [exact R5|]. split; [lia|]. split; [clear - R2; Z.div_mod_to_equations; lia|].
  eapply (block_shw FI AI s LB m b); [exact HR| exact Hb| lia| lia| exact R3].
Qed.

#[using="Type"] Lemma plist_view : forall s (LB : BL) m P (ns : list (BLK * Z)) (hs : list hdr) X,
  RHEAP_A FI AI s LB m -> p_hlist FI AI m P ns hs X -> bsub FI AI (hl_blocks FI AI ns hs) LB ->
  lsegA m (ns3_of ns hs) (hd_addr FI AI ns (P + 312)) (P + 288) (P + 312)
  /\ (forall N it id, In (N, it, id) (ns3_of ns hs) -> objA m N 24 /\ objA m it 88)
  /\ length ns = length hs.
Proof.
  intros s LB m P ns hs X HR (LHC & FLC & FFC & DL & HM & IT & VB & ZL & X0) SUB.
  assert (LEN : length ns = length hs) by (rewrite <- (length_map snd ns), IT, length_map; reflexivity).
  unfold hl_blocks in SUB. apply (bsub_app FI AI) in SUB. destruct SUB as [NSUB HSUB].
  assert (HIN : forall h, In h hs -> In (hk FI AI h, hA FI AI h, 88) LB).
  { intros h Hh. apply HSUB. apply (hdrs_blocks_In hs h _ Hh). left. reflexivity. }
  split; [| split; [| exact LEN]].
  - apply lsegA_of_dlseg; [exact DL| exact HM| exact IT|]. intros h Hh.
    destruct (am_block_range FI AI s LB m _ HR (HIN h Hh)) as (R1 & _). cbn in R1. lia.
  - intros N it id HI. destruct (ns3_of_In ns hs N it id IT HI) as (b & h & Hb & Hh & -> & -> & ->).
    assert (BIN : In b LB) by (apply NSUB; apply (in_map fst _ _ Hb)).
    pose proof (proj1 (dlseg_facts FI AI _ _ _ _ _ _ DL Hb)) as BSZ.
    pose proof (blk_objA s LB m b HR BIN) as OB. rewrite BSZ in OB.
    pose proof (blk_objA s LB m _ HR (HIN h Hh)) as OH. cbn [blk_addr blk_size fst snd] in OH.
    split; [exact OB| exact OH].
Qed.
End W.
