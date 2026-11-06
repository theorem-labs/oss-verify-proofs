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
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAA Require Import AEnv ADepot ALayout APrim ATacA ACells LJ LJU PEnv APrimSpec APrimSpec2 APrimLem AFrame APrimPop APrimPopR APrimPopLens APrimQ APrimFrame AFrameM
                        APrimDealloc APrimCover ASec ASecD AQuar AQuarM AHeap AFoot F_prim_refill F_prim_cdealloc F_poison F_quar_Ep F_quar_E F_quar_A AQuarR AQuarS AQuarP ATacFix
                        F_quar_M F_quar_DR F_quar_R F_quar_D F_sec_A F_quar_P AQuarT AQuarU F_gct F_depot F_depot_C F_quar_C F_prim_L0 F_hooks F_dealloc
                        F_ialloc F_unwind F_stacktrace F_free_icpt F_free_null F_alloc_env ALedger AFsEnv.
Import ListNotations.
Open Scope Z_scope.

Record astB := mkASB {
  bs_H : word -> bool;
  bs_pages : list word;
  bs_prim : prim;
  bs_sec : asec;
  bs_quar : aquar;
  bs_depot : list Z;
  bs_dtotal : Z;
  bs_nsec : Z;
  bs_live : list (qchunk * Z);
  bs_depot0 : list Z
}.
Definition bs_ghost (s : astB) : (word -> bool) * list word := (bs_H s, bs_pages s).

Section H2.
Context {HC : HasCeiling}.
Variables (AL : alayout) (E : penv).
Notation L := (al_thread AL).
Notation D := (al_depot AL).
Notation THR := (at_thr (al_thread AL)).
Notation TQ := (at_thr (al_thread AL) + TQ_OFF).

Definition lr_ok (r : qchunk * Z) : Prop := snd r = qc_n (fst r) \/ (snd r = 0 /\ qc_n (fst r) = 1).
Definition blk_ofB (r : qchunk * Z) : block Z := (lc_user AL (fst r), lc_user AL (fst r), snd r).
Definition live_chunks (s : astB) : list qchunk := map fst (bs_live s).
Definition heldB (s : astB) : list (Z * Z) := flat_map prim_of (live_chunks s).
Definition bs_X (s : astB) : pstate := (bs_prim s, bs_sec s).
Definition bs_gl (s : astB) : list qbatch := q_glob (bs_quar s) ++ q_loc (bs_quar s).

Definition sec_slack_ok (ch : qchunk) : Prop :=
  match qc_kind ch with QPrim _ _ => True | QSec _ => qc_rz ch + rup8 (qc_n ch) + 16 <= qc_bsize ch end.

Definition allheld (s : astB) : list (Z * Z) := tc_of (bs_gl s) ++ heldB s.

Definition sec_live_cnt (s : astB) : Z := Z.of_nat (length (flat_map sec_of (live_chunks s))).
Definition sec_rec_bytes (r : qchunk * Z) : Z := match qc_kind (fst r) with QSec _ => snd r | QPrim _ _ => 0 end.
Definition sec_live_bytes (s : astB) : Z := fold_right (fun r acc => sec_rec_bytes r + acc) 0 (bs_live s).
Definition budget_ok (s : astB) : Prop :=
  (forall c, 1 <= c <= 31 -> p_mu (get_cls (bs_prim s) c) <= PM c)
  /\ (forall c, 1 <= c <= 31 -> cls_cnt c (live_chunks s) * a0_csz c <= A0_CAP c)
  /\ pr_calloc (bs_prim s) = sum_cs (allheld s) /\ pr_cmapped (bs_prim s) = sum_mu (bs_prim s)
  /\ sec_live_cnt s <= A0_SEC_CNT /\ sec_live_bytes s <= A0_SEC_BYTES /\ 0 <= bs_nsec s <= A0_NSEC_MAX.

Definition dr_invB (X : pstate) (H : word -> bool) (m : mem) (WB : list qbatch) (WC : list qchunk) (hrest : list (Z * Z)) : Prop :=
  RPRIM AL (fst X) m /\ prim_ok (fst X) /\ RSEC AL (snd X) m
  /\ poison_env E m /\ thread_env L m /\ shvis H m
  /\ Forall qchunk_wf WC /\ Forall (qchunk_rep AL m) WC /\ Forall (held_kind X) WC
  /\ held_ok (fst X) (map bpair WB ++ flat_map prim_of WC ++ hrest)
  /\ List.NoDup (flat_map sec_of WC)
  /\ Forall qbatch_wf0 WB /\ Forall (fun b => exists nx, qbatch_rep AL m b nx) WB.
#[using="Type"] Lemma dr_inv_of_B : forall X H m WB WC hrest, dr_invB X H m WB WC hrest -> mem_inv asegs m -> dr_inv AL E X H m WB WC hrest.
Proof. intros X H m WB WC hrest (A1 & A2 & A3 & A4 & A5 & A6 & A7) MI. unfold dr_inv. tauto. Qed.
#[using="Type"] Lemma dr_invB_of : forall X H m WB WC hrest, dr_inv AL E X H m WB WC hrest -> dr_invB X H m WB WC hrest /\ mem_inv asegs m.
Proof. intros X H m WB WC hrest (A1 & A2 & A3 & A4 & A5 & A6 & A7). unfold dr_invB. tauto. Qed.

Definition depot_ok (hs0 hs : list Z) (total : Z) : Prop :=
  List.NoDup hs /\ incl hs (hs0 ++ map depot_hash A0_TRACES) /\ 0 <= total <= 31 * zlen hs /\ (length hs0 <= 4)%nat.

Definition RHEAP_B (s : astB) (LB : list (block Z)) (m : mem) : Prop :=
  let X := bs_X s in let Q := bs_quar s in let gl := bs_gl s in
  Permutation LB (map blk_ofB (bs_live s)) /\ Forall lr_ok (bs_live s)
  /\ alayout_ok AL
  /\ dr_invB X (bs_H s) m gl (flat_map qb_chunks gl) (heldB s)
  /\ qlist_rep AL m (q_glob Q) 0 /\ rw_cells asegs m QUAR_GQ (qcells AL (q_glob Q)) /\ qcache_rep AL m TQ (q_loc Q)
  /\ rw_cells asegs m QUAR_MTX [CB 4 [b8 0; b8 0; b8 0; b8 0]] /\ quar_env m /\ quar_wf Q
  /\ RDEPOT D (bs_depot s) (bs_dtotal s) m /\ depot_ok (bs_depot0 s) (bs_depot s) (bs_dtotal s)
  /\ Forall qchunk_wf (live_chunks s) /\ Forall (lchunk_rep AL m) (live_chunks s) /\ Forall (held_kind X) (live_chunks s)
  /\ Permutation (se_chunks (bs_sec s)) (flat_map sec_of (flat_map qb_chunks gl) ++ flat_map sec_of (live_chunks s))
  /\ cover (bs_prim s) (allheld s)
  /\ thread_env2 AL m /\ hooks_env m /\ trace_env m /\ alloc_env m /\ (exists inited, ia_cells 262144 262728 inited m)
  /\ Forall ch_cls_ok (live_chunks s) /\ Forall ch_cls_ok (flat_map qb_chunks gl) /\ Forall sec_slack_ok (live_chunks s) /\ budget_ok s

  /\ fs_tls_env (at_thr (al_thread AL)) A0_DTV A0_TLSB (al_dtls AL) (al_fsb AL) m.

#[using="Type"] Lemma sec_rec_bytes_nonneg : forall r, lr_ok r -> qchunk_wf (fst r) -> 0 <= sec_rec_bytes r.
Proof.
  intros [ch cn] LR (_ & _ & N1 & _). unfold sec_rec_bytes. cbn [fst snd] in *. destruct (qc_kind ch); [lia|]. destruct LR as [LR|[LR _]]; cbn [fst snd] in LR; lia.
Qed.
#[using="Type"] Lemma sec_measures_rest : forall (l1 l2 : list (qchunk * Z)) x, lr_ok x -> qchunk_wf (fst x) ->
  Z.of_nat (length (flat_map sec_of (map fst (l1 ++ l2)))) <= Z.of_nat (length (flat_map sec_of (map fst (l1 ++ x :: l2))))
  /\ fold_right (fun r acc => sec_rec_bytes r + acc) 0 (l1 ++ l2) <= fold_right (fun r acc => sec_rec_bytes r + acc) 0 (l1 ++ x :: l2).
Proof.
  intros l1 l2 x LR WF. pose proof (sec_rec_bytes_nonneg x LR WF) as NN. split.
  - rewrite !map_app, !flat_map_app, !length_app. cbn [map flat_map]. rewrite length_app. lia.
  - induction l1 as [|y l1 IH]; cbn [app fold_right]; lia.
Qed.

End H2.
