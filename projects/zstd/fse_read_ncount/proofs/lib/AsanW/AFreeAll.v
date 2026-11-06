(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import ExecF ITreeA StepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree AsanCtrl AsanEmbed AsanQB.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg AProto ABase ABytes AQConst AKitQ AMalloc_iface ADepot_iface ARep ARepQ ARepQP ALayout AHeapP
AFreeModel AFreeModelR AFreeRep AFreeRead ASec F_afree_arep F_afree_arepR AFreeRefillP ASF_kit ASF_all
F_adepot AFake_iface AFake_arep AInstance AInstanceM AInstanceF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_orc_old ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_k12.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.slia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.slia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.flia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.flia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange_nonneg ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_nonneg_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.solve_load_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.word_eq_tac_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes_k12.
(* [comment removed for export] *)

Open Scope Z_scope.
Section CANSEC1. Context {rc : runConstT}.
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
/\ (snd iv <= 0x9f0f0 \/ 0x9f1b0 <= fst iv)
/\ (snd iv <= 0xa3680 \/ 0x1246b0 <= fst iv)
/\ (snd iv <= 0x131f08 \/ 0x131f0c <= fst iv)) CI.
Hypothesis CI_OK2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI.
#[using="HL CI_OK CI_OK2"] Theorem afree_total : afree_stmt CI (AHEAP_P (AHQ DI ASEC_of AFK)).
Proof.
unfold afree_stmt. intros until tr. intros AH HIN QB. intros.
pose proof AH as AH0. destruct AH0 as (ALO & ARNG & [X [AR BL]] & HFK).
destruct (proj1 BL p A n HIN) as [(b & Hb & Sb & Ub & Nb)|(mb & ms & Lp & _)].
-
pose proof AR as AR0. destruct AR0 as (WF & _). pose proof WF as WF0. destruct WF0 as (_ & _ & _ & _ & _ & _ & _ & BUSY & _).
destruct (BUSY b Hb) as [CLb M]. rewrite Sb in M. destruct M as (Nb1 & _ & _ & _ & _ & LIVE). rewrite Nb in Nb1, LIVE.
destruct (qb_norec st p _ LIVE QB) as [_ NR].
Local Ltac2 Set LiaHints.tbl := fun () => "0010>29969492191.83000005S3Nb1".
eapply (afree_norecycle DI ASEC_of AFK HL CI CI_OK CI_OK2); try eassumption; [lia|]. intros _. exact NR.
-
destruct (qb_norec st p _ Lp QB) as [NQ NR]. cbn [chunk_size] in NQ.
eapply (afree_sec_norecycle DI AFK HL CI CI_OK CI_OK2); try eassumption. intros _. exact NR.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End S.
#[using="Type"] Theorem AHI_free : afree_stmt aci_I (AHEAP_P AHI).
Proof. exact (afree_total adepot_iface AFAKE AH_laws aci_I aci_okQ aci_ok2). Qed.
End CANSEC1.
