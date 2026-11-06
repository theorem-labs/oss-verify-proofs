(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from parts of lib/A/DMwalkIF.v (dr_leaf_r / dorecycle_spec_r / dorecycle_ok_t, rchunk_m_t / rchunk_ok_t, drain_m_cf_t / drain_ok_t), each restated at the re-hide twins of DIfaceRh.v (YG0dH.amreal' at YGcfRehidePost.RZ_cf, YGcfRehidePost.acall_post_x_rh); every premise and every other conjunct is unchanged. *)
(* F1 priming row R3 (re-hide at a secondary recycle): the heads of lane B1's real-merge drain walk at the re-hide
   twins.  Recycle's secondary arm hides the dead shadow hull's interior at its return (YA0nR.SRr'_rehide_ret), so
   Recycle (H4's head) and every walk that binds across it (DoRecycle, H2's head; the drain, the lane's top) are
   stated over YG0dH.amreal' at YGcfRehidePost.RZ_cf with the post YGcfRehidePost.acall_post_x_rh.  MergeBatches
   (mb_ok_t, SRr) and CacheDealloc (cdealloc_g_t, MnRecycle.de_cdealloc_m_t) re-hide nothing and stay released:
   a walk that calls them lifts once at the call (MergeBatches by YA0nH.SRr_SRr'; CacheDealloc by
   YG0dH.amreal_amreal' with YGcfRehidePost.acall_post_x_rh_of).
   A new file, so that DMwalkIF.v and its consumers stay byte-unchanged (as DIfaceRh.v).
   rule 24: no function proved (kind: statement heads at the re-hide forms). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YGcfRehidePost.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH YG0dH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0 YFl1.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1w YFeq YFew YFeu YFgj.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG00cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ImgBaseDG AGif2reply DGif0reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import DMspec DMiface DIfaceR DMwalkIF.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ErrnoG MemnormT MnRecycle DIfaceRh.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Open Scope am_scope.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* H2: DoRecycle (DMwalkIF.dr_leaf_r / dorecycle_spec_r / dorecycle_ok_t) at the twins.                             *)
Section dr.
Variable B : asyms.
Variable ARXr : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable DRq : astate -> list chunk -> list Z -> Prop.
Variable RMAXD : Z.

(* dr_leaf_r with acall_post_x_rh. *)
Definition dr_leaf_rh (inst : Z) (ly : alayout) (X : astate) (W : world tfibsegs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (r : unit * astate) (W' : world tfibsegs) (c' : config) : Prop :=
exists regs' mem' md',
c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
YGcfRehidePost.acall_post_x_rh B ARXr AOX inst DRSTACK_X ly X W regs mem md (fun a => spZ regs <= a < spZ regs + 32)
  ly (snd r) W' regs' mem' md' /\
acall_raw_x B AOX inst DRSTACK_X ly X W regs mem md (fun a => spZ regs <= a < spZ regs + 32)
  ly (snd r) W' regs' mem' md' /\
ErrnoG.errno_kept B mem mem' /\ MemnormT.memnorm_keep tfibsegs mem mem' /\
DRq (snd r) [] [] /\ st_cache_inited (snd r) = true /\
(forall a, AOX ly (snd r) a -> AOX ly X a) /\
(forall a, spZ regs <= a < spZ regs + 32 -> apresent (w_H W') mem' a).

(* dorecycle_spec_r over amreal'. *)
Definition dorecycle_spec_rh : Prop :=
forall inst ly X P W regs mem md,
dr_pre_r B ARXr AOX DRq inst ly X P W regs mem md ->
amreal' tfibsegs YGcfRehidePost.RZ_cf (do_recycle (length P) P X) W (cfg_at tfibsegs A_DoRecycle regs mem md)
  (dr_leaf_rh inst ly X W regs mem md).

(* A DoRecycle leaf / walk that re-hides nothing gives the twin. *)
Lemma dr_leaf_rh_of : forall inst ly X W regs mem md r W' c',
dr_leaf_r B ARXr AOX DRq inst ly X W regs mem md r W' c' -> dr_leaf_rh inst ly X W regs mem md r W' c'.
Proof.
intros inst ly X W regs mem md r W' c' (regs' & mem' & md' & Hc & HP & HT).
exists regs', mem', md'. split; [exact Hc|].
split; [exact (YGcfRehidePost.acall_post_x_rh_of B ARXr AOX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP) | exact HT].
Qed.
Lemma dorecycle_spec_rh_of : dorecycle_spec_r B ARXr AOX DRq -> dorecycle_spec_rh.
Proof.
intros H inst ly X P W regs mem md PRE.
eapply amreal'_mono; [| exact (amreal_amreal' tfibsegs YGcfRehidePost.RZ_cf _ _ _ _ (H inst ly X P W regs mem md PRE))].
intros r W' c' HL. exact (dr_leaf_rh_of inst ly X W regs mem md r W' c' HL).
Qed.

(* dorecycle_ok_rh_t, drain_m_cf_rh_t and drain_ok_rh_t have NO [_rh_of]: each swaps the Recycle premise (negative
   position) for its weaker twin, so neither head implies the other; they are the walks' new obligations. *)

(* dorecycle_ok_t at the twins: Recycle's contract is DIfaceRh.de_rchunk_m_rh_t, CacheDealloc's stays released. *)
Definition dorecycle_ok_rh_t : Prop :=
TfibSyms B -> rmaxd_ok RMAXD ->
di_frame_t ARXr AOX -> di_rview_x_t B ARXr DRq RMAXD ->
DIfaceRh.de_rchunk_m_rh_t B ARXr AOX DRq -> MnRecycle.de_cdealloc_m_t B ARXr AOX DRq ->
dorecycle_spec_rh.
End dr.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* H4: Recycle (DMwalkIF.rchunk_m_t / rchunk_ok_t) at the twin.  The secondary arm applies YA0nR.SRr'_rehide_ret at *)
(* the walk's return; the primary arm re-hides nothing and lifts.  The premises are rchunk_ok_t's, unchanged;        *)
(* CacheDealloc's class-generic contract (cdealloc_g_t) stays released.                                            *)
Section callees.
Variable B : asyms.
Variable ARXr : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable DRq : astate -> list chunk -> list Z -> Prop.
Variables (NMAXD LMAXD RMAXD : Z).
Definition rchunk_m_rh_t : Prop := DIfaceRh.de_rchunk_m_rh_t B ARXr AOX DRq.
Definition rchunk_ok_rh_t : Prop :=
TfibSyms B -> nmaxd_ok NMAXD -> lmaxd_ok NMAXD LMAXD -> rmaxd_ok RMAXD -> drq_sizes DRq NMAXD LMAXD ->
di_frame_t ARXr AOX -> di_rview_x_t B ARXr DRq RMAXD -> cdealloc_g_t B ARXr AOX RMAXD -> rchunk_m_rh_t.
(* The released head gives the twin: the premises are the same, the conclusion weakens by de_rchunk_m_rh_of. *)
Lemma rchunk_ok_rh_of : rchunk_ok_t B ARXr AOX DRq NMAXD LMAXD RMAXD -> rchunk_ok_rh_t.
Proof.
intros H TB N L R D F V C. exact (DIfaceRh.de_rchunk_m_rh_of B ARXr AOX DRq (H TB N L R D F V C)).
Qed.
End callees.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The lane's top (DMwalkIF.drain_m_cf_t / drain_ok_t) at the twins: it concludes DIfaceRh.de_drain_m_rh_t from      *)
(* DIfaceRh.de_rchunk_m_rh_t; the read fields and CacheDealloc's contract stay released.                           *)
Section t1.
Variable B : asyms.
Variable ARX : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable ARXr : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable L24 : Z.
Variable QB : astate -> Prop.
Variable DRq : astate -> list chunk -> list Z -> Prop.
Variable RMAXD : Z.
Definition drain_m_cf_rh_t : Prop :=
TfibSyms B -> drain_reads B ARX ARXr AOX L24 QB DRq RMAXD ->
DIfaceRh.de_rchunk_m_rh_t B ARXr AOX DRq -> MnRecycle.de_cdealloc_m_t B ARXr AOX DRq ->
DIfaceRh.de_drain_m_rh_t B ARX AOX drain_body_cf L24 QB.
Definition drain_ok_rh_t : Prop :=
rmaxd_ok RMAXD -> L24 < 2 ^ 40 ->
(forall X, QB X -> qc_bytes (st_qglobal X) <= 2 ^ 30 /\ qc_bytes (st_qthread X) <= 2 ^ 29) ->
drain_m_cf_rh_t.
End t1.
End d.
