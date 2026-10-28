(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import ApBase ApState ApOwner ApLogic ApInv ApErr ApBridge.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit D_defs D_cs D_libiface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import R_unwind_chain.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import LibKitA ARun BnHeapA BnRepDefs BnRepA ImplA BnIfaceA W_cryptoA UnwindA EdgesA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells ApErrKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApRepDefs ApRep ApIface ApFrame ApErrKitA ApErrKitA2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma other_not_restA : forall (st : ap_st bptr) E OW (pb : bptr),
  ~ In pb (es_ids st ++ env_ids E) -> ~ In pb (map blk_id (rest_blocks OW E (as_cnf st))) /\ pb <> p_es E.
Proof.
  intros st E OW pb NI. rewrite in_app_iff in NI. split.
  - rewrite rest_ids, in_app_iff. intros [H|H].
    + apply NI. right. rewrite env_ids_unfold. cbn [In] in H |- *. tauto.
    + apply NI. left. apply cnf_ids_in_es_ids. exact H.
  - intros ->. apply NI. right. rewrite env_ids_unfold. cbn. tauto.
Qed.

(* [comment removed for export] *)
Lemma err_rep_agree_es : forall E OW st m m',
  ap_env_ok E OW -> err_rep m E OW st -> agree_on (fun a => e_es E <= a < e_es E + ES_SIZE) m m' -> err_rep m' E OW st.
Proof.
  intros E OW st m m' HE (Hsh & H & F1 & F2 & F3) AG. destruct (env_in E OW HE) as (IES & _).
  split; [exact Hsh|]. split; [|repeat split; assumption].
  pose proof Hsh as (L1 & L2 & L3 & L4 & L5 & L6 & L7).
  destruct H as (R0 & R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9).
  Local Ltac esa L :=
    intros a Ha; cbv beta;
    rewrite ?wl_length, ?length_map, ?repeat_length, ?L in Ha;
    unfold ESO_FLAGS, ESO_MARKS, ESO_BUFFER, ESO_DATA, ESO_DSIZE, ESO_DFLAGS, ESO_FILE, ESO_LINE, ESO_FUNC, ESO_TOP, ES_SIZE, ERR_NUM in *;
    cbn [cells_size csize Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ Pos.mul Pos.add] in Ha; lia.
  split; [eapply u32arr_agree; [exact AG|exact R0|]; esa L1|].
  split; [eapply u32arr_agree; [exact AG|exact R1|]; esa L1|].
  split; [eapply u64arr_agree; [exact AG|exact R2|]; esa L2|].
  split; [eapply u64arr_agree; [exact AG|exact R3|]; esa L3|].
  split; [eapply u64arr_agree; [exact AG|exact R4|]; esa L3|].
  split; [eapply u32arr_agree; [exact AG|exact R5|]; esa L4|].
  split; [eapply u64arr_agree; [exact AG|exact R6|]; esa L5|].
  split; [eapply u32arr_agree; [exact AG|exact R7|]; esa L6|].
  split; [eapply u64arr_agree; [exact AG|exact R8|]; esa L7|].
  eapply rw_cells_agree; [exact AG|exact R9|]; esa L1.
Qed.

Section WithRT.
Context {AR : ARun}.
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Theorem ap_state_but_blockA : forall Σ (st : ap_st bptr) m m' OW LB E bo SP (pb : bptr) PB nB,
  AHEAP Σ OW LB m -> ap_state st m OW E bo -> ids_ok E st ->
  In (pb, PB, nB) OW -> ~ In pb (es_ids st ++ env_ids E) ->
  agree_on (fun a => aclient_addr (OW ++ LB) SP a /\ outside [(PB, PB + nB)] a) m m' ->
  ap_state st m' OW E bo.
Proof.
  intros Σ st m m' OW LB E bo SP pb PB nB HEAP AS _ HBIN NI AG.
  destruct (other_not_restA st E OW pb NI) as [NR NES].
  pose proof (proj1 (ap_state_splitA _ _ _ _ _) AS) as [HR ER].
  assert (HBIN' : In (pb, PB, nB) (OW ++ LB)) by (apply in_or_app; left; exact HBIN).
  apply ap_state_splitA. split.
  - eapply rest_agreeA; [exact HR|]. eapply agree_on_mono; [exact AG|]. intros a Ha. cbv beta. cbn [outside].
    destruct (rest_addr_casesA OW E (as_cnf st) a Ha) as [(R1 & CS & R2)|(b & Hb & Hr)].
    + split; [right; left; exact CS|]. split; [| exact I].
      intros Hin. exact (blk_not_static Σ OW LB m (pb, PB, nB) a HEAP HBIN' Hin CS).
    + pose proof (rest_blocks_OWA _ _ _ _ _ _ HR Hb) as HbOW.
      split; [right; right; exists b; split; [apply in_or_app; left; exact HbOW| exact Hr]|]. split; [| exact I].
      assert (NE : blk_id b <> pb) by (intros E0; apply NR; rewrite <- E0; apply in_map; exact Hb).
      destruct b as [[q A] n]. cbn [blk_id blk_addr blk_size fst snd] in Hr, NE.
      pose proof (blk_disjointA Σ OW LB m q A n pb PB nB HEAP ltac:(apply in_or_app; left; exact HbOW) HBIN' NE). lia.
  - pose proof HR as (HE & _). destruct (env_in E OW HE) as (IES & _).
    eapply err_rep_agree_es; [exact HE| exact ER|]. eapply agree_on_mono; [exact AG|]. intros a Ha. cbv beta in Ha. cbv beta. cbn [outside].
    split; [right; right; exists (p_es E, e_es E, ES_SIZE); split; [apply in_or_app; left; exact IES| cbn [blk_addr blk_size fst snd]; exact Ha]|].
    split; [| exact I].
    assert (NE : p_es E <> pb) by (intros E0; exact (NES (eq_sym E0))).
    pose proof (blk_disjointA Σ OW LB m (p_es E) (e_es E) ES_SIZE pb PB nB HEAP ltac:(apply in_or_app; left; exact IES) HBIN' NE). lia.
Qed.

Theorem data_cells_but_blockA : forall Σ (st : ap_st bptr) m m' OW LB E bo SP (pb : bptr) PB nB,
  AHEAP Σ OW LB m -> ap_state st m OW E bo -> data_cells m OW st ->
  In (pb, PB, nB) OW -> ~ In pb (es_ids st ++ env_ids E) ->
  agree_on (fun a => aclient_addr (OW ++ LB) SP a /\ outside [(PB, PB + nB)] a) m m' ->
  data_cells m' OW st.
Proof.
  intros Σ st m m' OW LB E bo SP pb PB nB HEAP AS [DC DF] HBIN NI AG.
  pose proof (ap_state_esA _ _ _ _ _ AS) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & OD).
  assert (HBIN' : In (pb, PB, nB) (OW ++ LB)) by (apply in_or_app; left; exact HBIN).
  split; [| exact DF]. intros i q k Hd. destruct (DC i q k Hd) as [Hk [junk HC]]. split; [exact Hk|]. exists junk.
  pose proof (optb_ok_nth OW _ i q k OD Hd) as [HqOW Hpos].
  eapply rw_cells_agree; [exact AG| exact HC|]. intros a Ha. cbv beta. cbn [outside].
  cbn [cells_size csize Nat.add] in Ha. rewrite Nat.add_0_r, Z2Nat.id in Ha by lia.
  split; [right; right; exists (q, badr OW q, k); split; [apply in_or_app; left; exact HqOW| cbn [blk_addr blk_size fst snd]; lia]|]. split; [| exact I].
  assert (NE : q <> pb) by (intros ->; apply NI; apply in_app_iff; left; eapply es_ids_data; exact Hd).
  pose proof (blk_disjointA Σ OW LB m q (badr OW q) k pb PB nB HEAP ltac:(apply in_or_app; left; exact HqOW) HBIN' NE). lia.
Qed.

End WithRT.
