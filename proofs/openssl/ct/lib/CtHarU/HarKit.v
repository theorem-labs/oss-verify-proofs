(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Prog LibProg CtSizes CtWire CtModel ApBase ApState ApErr ApBridge.
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem SFModel.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface Malloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface RAligned_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import STree Monad Stdio ProgG.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit Driver_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit BnHeap BnRep W_crypto.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpInit HxpFacts HxpLaws.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs ApRep ApWalkTac ApErrKit ApIface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtParseU Require Import PzDefs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctU Require Import SctDefs W_sct_list_free SctRep W_sct_leaves W_sk_leaves SctStmt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtEncU Require Import EncKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rin_ivs_app : forall X Y a, rin_ivs (X ++ Y) a <-> rin_ivs X a \/ rin_ivs Y a.
Proof. induction X as [|iv X IH]; intros Y a; cbn; [tauto|]. rewrite IH. tauto. Qed.

Lemma rin_ivs_LIBW_AP : forall a, rin_ivs LIBW_AP a -> 0x2c2e98 <= a < 0x3545b0.
Proof. intros a H. unfold LIBW_AP in H. cbn [rin_ivs fst snd] in H. lia. Qed.

Lemma LIBW_AP_HX : forall a, rin_ivs LIBW_AP a -> rin_ivs LIBW_HX a.
Proof. intros a H. unfold LIBW_AP in H. unfold LIBW_HX. cbn [rin_ivs fst snd] in *. lia. Qed.

(* [comment removed for export] *)
Lemma drv_cells_client : forall LB SP a, lxs_addr a \/ stderr_addr a -> lx_client LB SP LIBW_HX a.
Proof.
  intros LB SP a Ha. assert (Hni : ~ rin_ivs LIBW_HX a).
  { intros H. destruct (LIBW_HX_img a H) as (_ & _ & ND). apply ND. unfold drv_addr. destruct Ha as [Ha|Ha]; [right; right; left; exact Ha| right; left; exact Ha]. }
  destruct Ha as [Ha|Ha]; [exact (lxs_addr_client _ _ _ a Ha Hni) | exact (stderr_addr_client _ _ _ a Ha Hni)].
Qed.

(* [comment removed for export] *)
Lemma sk_rep_relist : forall m L L' adr k,
  sk_rep m L adr k -> (forall b, In b (sk_allblocks adr k) -> In b L') -> sk_rep m L' adr k.
Proof.
  intros m L L' adr k (HIN & HC & HD & HFI & ND) HL. unfold sk_allblocks in HL.
  assert (AR : forall x o, In x (sk_items k) -> (forall b, In b (oblk adr o) -> In b (sct_blocks adr x)) -> arr_rep m L adr o -> arr_rep m L' adr o).
  { intros x [[q0 n0]|] Hx Ho H; cbn in H |- *; [| exact I]. destruct H as (A1 & A2 & A3). split; [exact A1|]. split; [| exact A3].
    apply HL. rewrite !in_app_iff. left. clear - Hx Ho. induction (sk_items k) as [|y t IH]; [destruct Hx|].
    cbn. apply in_app_iff. destruct Hx as [<-|Hx]; [left; apply Ho; left; reflexivity| right; exact (IH Hx)]. }
  split; [apply HL; rewrite !in_app_iff; right; right; left; reflexivity|].
  split; [exact HC|].
  split. { destruct (sk_data k) as [[q na]|]; [| exact HD]. destruct HD as (H1 & H2 & H3 & H4). split; [| split; [exact H2| split; [exact H3| exact H4]]].
           apply HL. rewrite !in_app_iff. right. left. cbn. left. reflexivity. }
  split; [| exact ND].
  apply Forall_forall. intros x Hx. pose proof (proj1 (Forall_forall _ _) HFI x Hx) as (X1 & X2 & X3 & X4 & X5 & X6 & REST).
  assert (BL : forall b, In b (sct_blocks adr x) -> In b L').
  { intros b Hb. apply HL. rewrite !in_app_iff. left. clear - Hx Hb. induction (sk_items k) as [|y t IH]; [destruct Hx|].
    cbn. apply in_app_iff. destruct Hx as [<-|Hx]; [left; exact Hb| right; exact (IH Hx)]. }
  split; [apply BL; unfold sct_blocks; rewrite !in_app_iff; right; right; right; right; left; reflexivity|]. split; [exact X2|].
  split; [apply (AR x); [exact Hx| intros b Hb; unfold sct_blocks; rewrite !in_app_iff; tauto| exact X3]|].
  split; [apply (AR x); [exact Hx| intros b Hb; unfold sct_blocks; rewrite !in_app_iff; tauto| exact X4]|].
  split; [apply (AR x); [exact Hx| intros b Hb; unfold sct_blocks; rewrite !in_app_iff; tauto| exact X5]|].
  split; [apply (AR x); [exact Hx| intros b Hb; unfold sct_blocks; rewrite !in_app_iff; tauto| exact X6]| exact REST].
Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
Lemma ro_cells_recast : forall m A cs cs',
  ro_cells ctusegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> ro_cells ctusegs m A cs'.
Proof. intros m A cs cs' [Hwf Hb] Hwf' Eb. split; [exact Hwf'| rewrite Eb; exact Hb]. Qed.

Local Ltac img_cell A n c :=
  let bs := eval vm_compute in (match image_bytes ctusegs A n with Some bs => bs | None => [] end) in
  lazymatch goal with |- ro_cells _ ?mm _ _ =>
  apply (ro_cells_recast mm A [CB n bs] [c]);
  [ apply (ap_img_ro_cells mm A n bs); [assumption| unfold IMG_LO; lia| unfold IMG_HI; cbn; lia| vm_compute; reflexivity]
  | cbn; repeat split; reflexivity
  | cbv -[Z_to_bv]; repeat first [reflexivity | apply (f_equal2 (@cons _)); [apply bv_eq; vm_compute; reflexivity|]] ] end.

Lemma null_meth_create : forall m, ap_img m -> ro_cells ctusegs m (NULL_METHOD + 72) [C8 (wz 0)].
Proof. intros m IMG. unfold NULL_METHOD, MallocRep.wz. img_cell (0x2d70f0 + 72) 8%nat (C8 (Z_to_bv 64 0)). Qed.
Lemma null_meth_destroy : forall m, ap_img m -> ro_cells ctusegs m (NULL_METHOD + 80) [C8 (wz 0)].
Proof. intros m IMG. unfold NULL_METHOD, MallocRep.wz. img_cell (0x2d70f0 + 80) 8%nat (C8 (Z_to_bv 64 0)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma payload_ok_munch : forall s OW LB m m' D d W lo,
  RHEAP s (OW ++ LB) m -> payload_ok m LB D d -> munch W m m' -> alloc_ceiling <= lo ->
  Forall (fun iv => lo <= fst iv \/ iv = (LX_ERRNO, LX_ERRNO + 4) \/ (exists q A n, In (q, A, n) OW /\ A <= fst iv /\ snd iv <= A + n)) W ->
  payload_ok m' LB D d.
Proof.
  intros s OW LB m m' D d W lo HEAP (PB & PF & D0 & DN & D30 & HB) MU CEIL HW.
  split; [|split; [exact PF|split; [exact D0|split; [exact DN|split; [exact D30|exact HB]]]]].
  destruct HB as [->|(b & Hb & HbD & HbE)].
  { cbn. destruct PB as (P1 & P2 & P3). split; [exact P1|]. split; [exact P2|]. intros i Hi. cbn in Hi. lia. }
  destruct b as [[qb A] n]. cbn [blk_addr blk_size fst snd] in HbD, HbE.
  assert (HbL : In (qb, A, n) (OW ++ LB)) by (apply in_app_iff; right; exact Hb).
  pose proof (blk_bounds _ _ _ _ _ _ HEAP HbL) as (B1 & B2 & B3 & B4 & B5). pose proof (LH_nodup _ _ _ HEAP) as ND.
  eapply bytes_at_transport; [exact PB| exact MU|]. apply disjoint_from_forall. unfold to_bytes. rewrite length_map. unfold zlength in HbE.
  eapply Forall_impl; [|exact HW]. intros [x y] [H|[H|(q & A' & n' & HIn & HA & Hy)]]; cbn [fst snd] in *.
  - lia.
  - injection H as -> ->. unfold LX_ERRNO, RATP. lia.
  - assert (Hq : q <> qb).
    { intros ->. rewrite map_app in ND. eapply (NoDup_app_disjoint _ _ qb ND); [eapply in_ids; exact HIn| eapply in_ids; exact Hb]. }
    pose proof (blk_disjoint _ _ _ q A' n' qb A n HEAP ltac:(apply in_app_iff; left; exact HIn) HbL Hq). lia.
Qed.

Lemma rw_cells_lx : forall LB SP X m m' A cs,
  lx_pres LB SP X m m' -> rw_cells ctusegs m A cs -> SP <= A ->
  (forall a, A <= a < A + Z.of_nat (cells_size cs) -> ~ rin_ivs X a) ->
  rw_cells ctusegs m' A cs.
Proof.
  intros LB SP X m m' A cs LX H HA HX. eapply (rw_cells_agree (lx_client LB SP X)); [exact LX| exact H|].
  intros a Ha. split; [apply HX; exact Ha| left; lia].
Qed.

Lemma payload_ok_lx : forall s OW LB m m' D d SP X1 lo,
  RHEAP s (OW ++ LB) m -> payload_ok m LB D d -> lx_pres LB SP (X1 ++ LIBW_AP) m m' -> alloc_ceiling <= lo ->
  Forall (fun iv => lo <= fst iv) X1 -> payload_ok m' LB D d.
Proof.
  intros s OW LB m m' D d SP X1 lo HEAP (PB & PF & D0 & DN & D30 & HB) LX CEIL HX1.
  split; [|split; [exact PF|split; [exact D0|split; [exact DN|split; [exact D30|exact HB]]]]].
  destruct HB as [->|(b & Hb & HbD & HbE)].
  { cbn. destruct PB as (P1 & P2 & P3). split; [exact P1|]. split; [exact P2|]. intros i Hi. cbn in Hi. lia. }
  destruct b as [[qb A] n]. cbn [blk_addr blk_size fst snd] in HbD, HbE.
  assert (HbL : In (qb, A, n) (OW ++ LB)) by (apply in_app_iff; right; exact Hb).
  pose proof (blk_bounds _ _ _ _ _ _ HEAP HbL) as (B1 & B2 & B3 & B4 & B5). unfold zlength in HbE.
  eapply bytes_at_agree; [exact LX| exact PB|]. unfold to_bytes. rewrite length_map. intros a Ha. split.
  - rewrite rin_ivs_app. intros [H|H].
    + clear - H Ha HX1 B3 CEIL HbD HbE. induction X1 as [|[x y] X1 IH]; cbn in H; [exact H|]. apply Forall_cons_iff in HX1. destruct HX1 as [H1 H2].
      cbn [fst] in H1. destruct H as [H|H]; [lia| exact (IH H2 H)].
    + apply rin_ivs_LIBW_AP in H. lia.
  - right. left. exists (qb, A, n). split; [exact Hb|]. cbn. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Act.
  Variables (sp : word) (m : mem) (s : PState) (LB : list block) (E : ap_env) (lo B : Z) (canary : word).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis GLO : 3493888 <= lo.
  Hypothesis SPB : bv_unsigned sp <= B.
  Hypothesis B63 : B < 2 ^ 63.
  Local Notation HINV := (einv sp m s LB E lo B canary [] []).

  Lemma einv_adopt : forall q sX stX mX OWX errvX boX pb A n NEW,
    HINV q sX stX mX OWX errvX boX ((pb, A, n) :: NEW) -> HINV q sX stX mX ((pb, A, n) :: OWX) errvX boX NEW.
  Proof.
    intros until NEW. intros OI.
    pose proof (einv_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ OI) as (HEAP3 & ND3 & BND & FRESH & _).
    destruct OI as ((HEAP & AS & IDS & DC & AUX0 & LOQ0 & ST0 & ERR0 & SSP & MI0) & LX & KO & KI & KP & SO & FA).
    pose proof (ap_state_es _ _ _ _ _ AS) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & OD).
    pose proof (BND pb A n ltac:(apply in_app_iff; right; left; reflexivity)) as (A0 & N0 & AC & _ & A16).
    assert (NI : ~ In pb (map blk_id OWX)) by (intros Hin; apply (FRESH pb A n ltac:(left; reflexivity)); rewrite map_app; apply in_app_iff; left; exact Hin).
    assert (HEAP' : RHEAP sX (((pb, A, n) :: OWX) ++ NEW ++ LB) mX).
    { eapply RHEAP_perm; [exact HEAP|]. cbn [app]. apply Permutation_sym. apply Permutation_middle. }
    split; [| split; [exact LX| split; [intros b []| split; [intros b []| split; [exact KP| split; [exact SO| exact FA]]]]]].
    split; [exact HEAP'|]. split; [apply ap_state_cons_fresh; [exact AS| exact NI| lia| lia| exact A16]|]. split; [exact IDS|].
    split; [apply data_cells_cons_fresh; [exact DC| exact OD| exact NI]|].
    split; [exact AUX0|]. split; [exact LOQ0|]. split; [exact ST0|]. split; [exact ERR0|]. split; [| exact MI0].
    rewrite (ssp_canary_0 _ _ _ _ HEAP SSP). eapply RHEAP_ssp. exact HEAP'.
  Qed.

  Lemma einv_release : forall q sX stX mX OWX errvX boX pb A n NEW,
    HINV q sX stX mX ((pb, A, n) :: OWX) errvX boX NEW -> ~ In pb (es_ids stX ++ env_ids E) ->
    HINV q sX stX mX OWX errvX boX ((pb, A, n) :: NEW).
  Proof.
    intros until NEW. intros OI NPB.
    pose proof (einv_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ OI) as (HEAP3 & ND3 & BND & FRESH & _).
    destruct OI as ((HEAP & AS & IDS & DC & AUX0 & LOQ0 & ST0 & ERR0 & SSP & MI0) & LX & KO & KI & KP & SO & FA).
    cbn [map blk_id fst snd app] in ND3. apply NoDup_cons_iff in ND3. destruct ND3 as [NI _]. rewrite !map_app, !in_app_iff in NI.
    assert (RM : lb_remove pb ((pb, A, n) :: OWX) = OWX).
    { rewrite lb_remove_cons. cbn [blk_id fst snd]. rewrite bptr_eqb_refl. apply lb_remove_notin. tauto. }
    assert (HEAP' : RHEAP sX (OWX ++ ((pb, A, n) :: NEW) ++ LB) mX).
    { eapply RHEAP_perm; [exact HEAP|]. cbn [app]. apply Permutation_middle. }
    rewrite in_app_iff in NPB.
    split; [| split; [exact LX| split; [intros b []| split; [intros b []| split; [exact KP| split; [exact SO| exact FA]]]]]].
    split; [exact HEAP'|]. split; [rewrite <- RM; apply ap_state_remove_other; [exact AS| tauto| tauto]|]. split; [exact IDS|].
    split; [rewrite <- RM; apply data_cells_remove_other; [exact DC| tauto]|].
    split; [exact AUX0|]. split; [exact LOQ0|]. split; [exact ST0|]. split; [exact ERR0|]. split; [| exact MI0].
    rewrite (ssp_canary_0 _ _ _ _ HEAP SSP). eapply RHEAP_ssp. exact HEAP'.
  Qed.
End Act.
End WithCeiling0.
