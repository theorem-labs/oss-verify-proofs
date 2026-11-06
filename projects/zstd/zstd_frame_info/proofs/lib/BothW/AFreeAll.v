(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import ExecF ITreeA StepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree AsanCtrl AsanEmbed AsanQB.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import BImg AProto ABase ABytes AQConst AKitQ AMalloc_iface ADepot_iface ARep ARepQ ARepQP ALayout AHeapP
     AFreeModel AFreeModelR AFreeRep AFreeRead ASec F_afree_arep F_afree_arepR AFreeRefillP ASF_kit ASF_all
     F_adepot AFake_iface AFake_arep AInstance AInstanceM AInstanceF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
#[using="Type"] Lemma qb_norec : forall st p ch, (a_live st) !! p = Some ch -> qb_ok st p = true ->
  chunk_size ch <= Q_MAX /\ a_qglob_bytes (st_enq (set_live (delete p (a_live st)) st) ch) + a_qloc_bytes (st_enq (set_live (delete p (a_live st)) st) ch) <= Q_MAX.
Proof.
  intros st p ch LIVE QB. unfold qb_ok in QB. rewrite LIVE in QB.
  apply andb_prop in QB as [QB Q3]. apply andb_prop in QB as [Q1 Q2]. apply Z.leb_le in Q1, Q2, Q3.
  set (st1 := set_live (delete p (a_live st)) st).
  assert (E1 : a_qloc_bytes st1 = a_qloc_bytes st /\ a_qglob_bytes st1 = a_qglob_bytes st) by (split; reflexivity).
  unfold Q_BATCH_BYTES in Q3. Local Ltac2 Set LiaHints.tbl := fun () => "0030>17129787009.1052123886037.1367458024100.1300000:00A00HS2Q12Q22Q3S2Q32E1S2Q32E1".
split; [lia|].
  unfold st_enq. destruct (enq_app st1 ch) as [s|] eqn:EA.
  - destruct (enq_app_Some st1 ch s EA) as (l & b & _ & _ & ->). cbn [a_qloc_bytes a_qglob_bytes set_qloc]. lia.
  - pose proof (enq_new_core ch st1) as (_ & _ & G2 & _ & _ & L2 & _). rewrite G2, L2. unfold Q_BATCH_BYTES. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Section S.
Variable DI : ADepotIface.
Variable AFK : alayout -> list ablock -> amem -> Prop.
Hypothesis HL : ahole_laws (AHQ DI ASEC_of AFK).
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
                                  /\ (snd iv <= 0x9dcb0 \/ 0x9dd70 <= fst iv)
                                  /\ (snd iv <= 0xa2240 \/ 0x123270 <= fst iv)
                                  /\ (snd iv <= 0x130ac8 \/ 0x130acc <= fst iv)) CI.
Hypothesis CI_OK2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI.

(* [comment removed for export] *)
#[using="HL CI_OK CI_OK2"] Theorem afree_total : afree_stmt CI (AHEAP_P (AHQ DI ASEC_of AFK)).
Proof.
  unfold afree_stmt. intros until tr. intros AH HIN QB. intros.
  pose proof AH as AH0. destruct AH0 as (ALO & ARNG & [X [AR BL]] & HFK).
  destruct (proj1 BL p A n HIN) as [(b & Hb & Sb & Ub & Nb)|(mb & ms & Lp & _)].
  - (* [comment removed for export] *)
    pose proof AR as AR0. destruct AR0 as (WF & _). pose proof WF as WF0. destruct WF0 as (_ & _ & _ & _ & _ & _ & _ & BUSY & _).
    destruct (BUSY b Hb) as [CLb M]. rewrite Sb in M. destruct M as (Nb1 & _ & _ & _ & _ & LIVE). rewrite Nb in Nb1, LIVE.
    destruct (qb_norec st p _ LIVE QB) as [_ NR].
    Local Ltac2 Set LiaHints.tbl := fun () => "0010>29969492191.83000005S3Nb1".
eapply (afree_norecycle DI ASEC_of AFK HL CI CI_OK CI_OK2); try eassumption; [lia|]. intros _. exact NR.
  - (* [comment removed for export] *)
    destruct (qb_norec st p _ Lp QB) as [NQ NR]. cbn [chunk_size] in NQ.
    eapply (afree_sec_norecycle DI AFK HL CI CI_OK CI_OK2); try eassumption. intros _. exact NR.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End S.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Theorem AHI_free : afree_stmt aci_I (AHEAP_P AHI).
Proof. exact (afree_total adepot_iface AFAKE AH_laws aci_I aci_okQ aci_ok2). Qed.

(* [comment removed for export] *)
Definition AI_closed : AMallocIface := AI_of AHI_free.
End CANSEC1.
