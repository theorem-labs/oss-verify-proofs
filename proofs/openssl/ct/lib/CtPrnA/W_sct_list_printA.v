(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG CtSizes CtWire CtTime CtModel BnBase BnModel BnTree ApBase ApState ApLogic ApErr PrintfModel PrintfModelX.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Printf_pieces Printf_piecesx Printf_apfmt Printf_ctfmt Printf_sn.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit D_defs D_cs I_lkit FX_lib F_pop_arg F_printf_iface I_vsnstmt R_unwind_chain GDesc.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells ApErrKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnP Require Import BnKit BnKit2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnW Require Import BnTac BnMem BnTacX.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit AsLoop.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA BnRepDefs BnRepA ImplA ImplAX BnIfaceA AsStruct RtCallA UnwindA UnwindX EdgesA W_cryptoA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtFrameA Require Import AFrameKit AFrameCall AFrameTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApATac ApBImg ApWalkTac ApRepDefs ApRep ApIface ApFrame ApErrKitA2 ApStateButBlockA W_akit W_bio_push Fr_bio_write_intern W_bio_write Fr_BIO_vprintf Fr_BIO_printf W_bio_printf W_bio_printf2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctP Require Import SctDefs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctP Require W_sct_list_free SctRep W_sk_leaves SctStmt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctA Require Import SctRepA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctA Require Import SctWire.                (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctA Require Import RtGenStmtA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeA Require Import TimeKitA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtPrnA Require Import W_sk_leavesA PrnSctFmtA W_bio_hex_stringA PrnSctKitA PrnStmtA W_sct_printA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeA Require Import BTacX.                (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition SCT_LIST_LOOP_A : Z := 0x3383c4.
Definition SCT_LIST_EPI_A : Z := 0x338410.
Definition SCT_LIST_PRINT_STACK_A : Z := 80 + SCT_PRINT_STACK_A.
Definition SCT_LIST_PRINT_FRAMES_A : Z := 5.
Definition SCT_LIST_PRINT_COST_A (n : Z) : Z := 2^22.

(* [comment removed for export] *)
Fixpoint scts_print_costA (l : list (sctr bptr)) : Z :=
  match l with [] => 0 | x :: t => sct_print_costA x + 3 + scts_print_costA t end.

Lemma scts_print_costA_app : forall l1 l2, scts_print_costA (l1 ++ l2) = scts_print_costA l1 + scts_print_costA l2.
Proof. intros l1 l2. induction l1 as [|x l1 IH]; [reflexivity|]. cbn [app scts_print_costA]. rewrite IH. lia. Qed.

Lemma sct_print_costA_nonneg : forall x, 0 <= sc_extlen x -> 0 <= sc_siglen x -> 0 <= sc_bloblen x -> 0 <= sct_print_costA x.
Proof.
  intros x H1 H2 H3. unfold sct_print_costA, SCT_PRINT_BASE_A, HX_CRED, prn_item_wt, CtSctP.SctRep.logid_len, CT_V1_HASHLEN.
  destruct (sc_version x =? 0); [destruct (sc_logid x); lia| lia].
Qed.

Lemma scts_print_costA_nonneg : forall l, Forall (fun x => 0 <= sc_extlen x /\ 0 <= sc_siglen x /\ 0 <= sc_bloblen x) l -> 0 <= scts_print_costA l.
Proof.
  intros l H. induction l as [|x l IH]; [cbn; lia|]. apply Forall_cons_iff in H as [(H1 & H2 & H3) Hl]. cbn [scts_print_costA].
  pose proof (sct_print_costA_nonneg x H1 H2 H3). specialize (IH Hl). lia.
Qed.

(* [comment removed for export] *)
Lemma scts_print_costA_wire : forall l, Forall (fun x => 0 <= sc_extlen x /\ 0 <= sc_siglen x /\ 0 <= sc_bloblen x) l ->
  2 * scts_print_costA l <= 51 * scts_wire l.
Proof.
  intros l H. induction l as [|x l IH]; [rewrite scts_wire_nil; cbn; lia|]. apply Forall_cons_iff in H as [(H1 & H2 & H3) Hl]. specialize (IH Hl).
  cbn [scts_print_costA]. rewrite scts_wire_cons.
  assert (WT : 0 <= prn_item_wt x <= i2o_sct_len x).
  { unfold prn_item_wt, i2o_sct_len, CtSctP.SctRep.logid_len, CT_V1_HASHLEN. destruct (sc_version x =? 0); [destruct (sc_logid x); lia| lia]. }
  unfold sct_print_costA, SCT_PRINT_BASE_A, HX_CRED in *. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sep_lit_roA : ro_bytes ctasegs A_SEP_A (zb [10] ++ Z_to_bv 8 0 :: zb [0; 0; 0; 0; 0; 0]).
Proof. apply ro_bytes_b_sound. vm_compute. reflexivity. Qed.

Lemma sepA_vargA : forall OW LB m, vargA_ok OW LB m (Z_to_bv 64 A_SEP_A) (PA_s [10]).
Proof.
  intros OW LB m. unfold vargA_ok, A_SEP_A. rewrite (unsigned_lit 299488) by (clear; lia).
  exists (zb [0; 0; 0; 0; 0; 0]). change (zlength [10]) with 1. change (zlength (zb [0; 0; 0; 0; 0; 0])) with 6.
  split; [constructor; [clear; lia| constructor]|]. split; [clear; lia|]. split; [clear; cbn; lia|].
  right. split; [clear; lia|]. split; [cbv; discriminate|]. split; [exact sep_lit_roA|].
  intros AR' Σ' m' H'. eapply (af_lib_acc_lit _ (@ar_AF AR') Σ' m' (0x491e0, 2, 32)); [exact (@AH_art AR' _ _ _ _ H')| vm_compute; reflexivity| cbn; clear; lia| cbn; clear; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma arr_repA_agreeP : forall P m m' L adr o,
  agree_on P m m' -> (forall q n a, o = Some (q, n) -> adr q <= a < adr q + n -> P a) -> arr_repA m L adr o -> arr_repA m' L adr o.
Proof.
  intros P m m' L adr [[q n]|] AG HP H; cbn in *; [| exact I]. destruct H as (Hn & HL & bs & HB). split; [exact Hn|]. split; [exact HL|]. exists bs.
  eapply rw_cells_agree; [exact AG| exact HB|]. intros a Ha. cbn in Ha. rewrite Nat.add_0_r, Z2Nat.id in Ha by lia. eapply HP; [reflexivity| lia].
Qed.

Lemma sct_repA_agreeP : forall P m m' L adr s,
  agree_on P m m' -> (forall b a, In b (sct_blocks adr s) -> blk_addr b <= a < blk_addr b + blk_size b -> P a) -> sct_repA m L adr s -> sct_repA m' L adr s.
Proof.
  intros P m m' L adr s AG HP (H1 & AL & H2 & H3 & H4 & H5 & H6 & REST).
  assert (BL : forall b, (In b (CtSctP.W_sct_list_free.oblk adr (osz32 (sc_logid s))) \/ In b (CtSctP.W_sct_list_free.oblk adr (sc_ext s))
                          \/ In b (CtSctP.W_sct_list_free.oblk adr (sc_sig s)) \/ In b (CtSctP.W_sct_list_free.oblk adr (sc_blob s))
                          \/ b = (sc_blk s, adr (sc_blk s), SCT_SIZE)) -> In b (sct_blocks adr s)).
  { intros b Hb. unfold CtSctP.W_sct_list_free.sct_blocks. rewrite !in_app_iff. cbn. destruct Hb as [Hb|[Hb|[Hb|[Hb| ->]]]]; tauto. }
  split; [exact H1|]. split; [exact AL|]. split.
  { eapply rw_cells_agree; [exact AG| exact H2|]. intros a Ha. apply (HP (sc_blk s, adr (sc_blk s), SCT_SIZE)); [apply BL; right; right; right; right; reflexivity|].
    cbn. rewrite CtSctP.SctRep.sct_cells_size in Ha. unfold SCT_SIZE in *. lia. }
  split; [eapply arr_repA_agreeP; [exact AG| intros q n a Ho Ha; apply (HP (q, adr q, n)); [apply BL; left; rewrite Ho; left; reflexivity| cbn; lia]| exact H3]|].
  split; [eapply arr_repA_agreeP; [exact AG| intros q n a Ho Ha; apply (HP (q, adr q, n)); [apply BL; right; left; rewrite Ho; left; reflexivity| cbn; lia]| exact H4]|].
  split; [eapply arr_repA_agreeP; [exact AG| intros q n a Ho Ha; apply (HP (q, adr q, n)); [apply BL; right; right; left; rewrite Ho; left; reflexivity| cbn; lia]| exact H5]|].
  split; [eapply arr_repA_agreeP; [exact AG| intros q n a Ho Ha; apply (HP (q, adr q, n)); [apply BL; right; right; right; left; rewrite Ho; left; reflexivity| cbn; lia]| exact H6]|].
  exact REST.
Qed.

Lemma sk_repA_agreeP : forall P m m' L adr k,
  agree_on P m m' -> (forall b a, In b (sk_blocks adr k) -> blk_addr b <= a < blk_addr b + blk_size b -> P a) -> sk_repA m L adr k -> sk_repA m' L adr k.
Proof.
  intros P m m' L adr k AG HP (HIN & (sorted & SR & HC) & HD & HF & ND).
  split; [exact HIN|]. split.
  { exists sorted. split; [exact SR|]. eapply rw_cells_agree; [exact AG| exact HC|]. intros a Ha. change (Z.of_nat (cells_size (sk_cells adr k sorted))) with STACK_SIZE in Ha.
    apply (HP (sk_blk k, adr (sk_blk k), STACK_SIZE)); [unfold CtSctP.SctStmt.sk_blocks; rewrite !in_app_iff; right; right; left; reflexivity| cbn; exact Ha]. }
  split.
  { destruct (sk_data k) as [[q na]|] eqn:ED; [| exact HD]. destruct HD as (H1 & HA & H2 & H3 & jb & H4 & H5). split; [exact H1|]. split; [exact HA|]. split; [exact H2|]. split; [exact H3|].
    exists jb. split; [exact H4|]. eapply rw_cells_agree; [exact AG| exact H5|]. intros a Ha. rewrite CtSctP.W_sk_leaves.data_block_size in Ha.
    apply (HP (q, adr q, 8 * na)); [unfold CtSctP.SctStmt.sk_blocks; rewrite ED, !in_app_iff; right; left; left; reflexivity| cbn]. unfold sk_num in *. lia. }
  split; [| exact ND].
  apply Forall_forall. intros s Hs. eapply sct_repA_agreeP; [exact AG| | exact (proj1 (Forall_forall _ _) HF s Hs)].
  intros b a Hb Ha. apply (HP b); [| exact Ha]. unfold CtSctP.SctStmt.sk_blocks. rewrite !in_app_iff. left.
  clear - Hs Hb. induction (sk_items k) as [|y t IH]; [destruct Hs|]. cbn. apply in_app_iff. destruct Hs as [<-|Hs]; [left; exact Hb| right; exact (IH Hs)].
Qed.

(* [comment removed for export] *)
Lemma sk_data_cellsA_appP : forall (m : mem) adr D i done rest,
  sk_data_cellsA m adr D i (done ++ rest) -> sk_data_cellsA m adr D (i + zlength done) rest.
Proof.
  intros m adr D i done. revert i. induction done as [|y d IH]; intros i rest H.
  - unfold zlength. cbn [length Z.of_nat]. rewrite Z.add_0_r. exact H.
  - cbn [sk_data_cellsA app] in H. destruct H as [_ H]. pose proof (IH _ _ H) as H'. unfold zlength in *. cbn [length].
    replace (i + Z.of_nat (S (length d))) with (i + 1 + Z.of_nat (length d)) by lia. exact H'.
Qed.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RTS := (@ar_RT AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation FRM := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).
Hypothesis PFC : printf_contracts RTS.
Hypothesis REA : realloc_contract_gen RTS.

(* [comment removed for export] *)
Lemma SCT_print_bindA : forall {B : Type} (Fk : unit * ap_st bptr -> aprog bptr B)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RTS) (OW LB : list block) (lo : Z)
    (pb : bptr) (out pv nw : Z) (adr : bptr -> Z) (x : sctr bptr) (st : ap_st bptr) (ras : list Z)
    (Q : B -> rts RTS -> machine_state -> Prop),
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo + SCT_PRINT_STACK_A <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A -> (S (S (S (S (length FRM)))) < FRAMES_MAX)%nat -> sct_print_costA x <= rt_credit RTS Σ ->
  crypto_statics m -> realloc_statics m ->
  sct_repA m (OW ++ LB) adr x ->
  In (pb, out, BIO_SIZE) OW -> ~ In pb (map blk_id (sct_blocks adr x)) ->
  rw_cells ctasegs m out (bio_null_cells NULL_METHOD pv nw) -> 0 <= nw < 2^64 ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx SCT_PRINT_A (bv_unsigned ra :: ras) ->
  a0 = wz (adr (sc_blk x)) -> a1 = wz out -> a2 = wz 4 -> a3 = wz 0 ->
  (forall Σ' ms', sct_print_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB lo out pv m (sct_print_costA x) Σ' ms' -> implAp (Fk (tt, st)) Σ' Q ms') ->
  implAp (apbind (sct_print x st) Fk) Σ Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz SCT_PRINT_A) fc None m (seg_rom ctasegs)).
Proof.
  intros until Q. intros HEAP ST CEIL LO TOP AL16 MI TP FLEN CRED CS RS REP HBIN NPB HB NW UW CTX A0 A1 A2 A3 KQ.
  eapply (implAp_bind (sct_print x st) Fk Σ (fun r Σ' ms' => r = (tt, st) /\ sct_print_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB lo out pv m (sct_print_costA x) Σ' ms') Q).
  - eapply (SCT_print_walkA PFC REA); try eassumption. intros Σ' ms' PO. split; [reflexivity| exact PO].
  - intros [[] st'] Σ' ms' [E PO]. injection E as <-. exact (KQ Σ' ms' PO).
Qed.

(* [comment removed for export] *)
Lemma lp_itemA : forall Σc mc (OW LB : list block) adr k (pb : bptr) out done x t,
  AHEAP Σc OW LB mc -> sk_repA mc LB adr k -> In (pb, out, BIO_SIZE) OW -> sk_items k = done ++ x :: t ->
  exists q na, sk_data k = Some (q, na)
    /\ In (sk_blk k, adr (sk_blk k), STACK_SIZE) (OW ++ LB) /\ adr (sk_blk k) mod 16 = 0
    /\ In (q, adr q, 8 * na) (OW ++ LB) /\ adr q mod 16 = 0 /\ sk_num k <= na
    /\ ro_cells ctasegs mc (adr (sk_blk k)) [C4 (wz (sk_num k))] /\ ro_cells ctasegs mc (adr (sk_blk k) + SKO_DATA) [C8 (wz (adr q))]
    /\ 0 <= zlength done < sk_num k /\ sk_num k < 2^23
    /\ ro_cells ctasegs mc (adr q + 8 * zlength done) [C8 (wz (adr (sc_blk x)))]
    /\ sct_repA mc (OW ++ LB) adr x /\ ~ In pb (map blk_id (sct_blocks adr x)).
Proof.
  intros Σc mc OW LB adr k pb out done x t HEAP SK HBIN EQ.
  pose proof (sk_repA_free_view _ _ _ _ SK) as ((SC1 & SC2 & _) & HST & HOD & DCS & _ & _).
  pose proof SK as ((_ & ALS) & _ & HD & HF & _).
  assert (LEN : sk_num k = zlength done + 1 + zlength t) by (unfold sk_num; rewrite EQ, zlength_app'; unfold zlength; cbn [length]; lia).
  pose proof (zlength_nonneg'' done) as D0. pose proof (zlength_nonneg'' t) as T0.
  destruct (sk_data k) as [[q na]|] eqn:ED; [| exfalso; rewrite HOD in EQ; destruct done; discriminate].
  destruct HOD as [HQ HNA]. destruct HD as (_ & ALD & _ & NA23 & _). cbn [optr] in SC2, DCS.
  exists q, na. split; [reflexivity|].
  split; [apply in_or_app; right; exact HST|]. split; [exact ALS|].
  split; [apply in_or_app; right; exact HQ|]. split; [exact ALD|]. split; [exact HNA|].
  split; [exact SC1|]. split; [exact SC2|].
  split; [lia|]. split; [lia|].
  split. { rewrite EQ in DCS. apply sk_data_cellsA_appP in DCS. cbn [sk_data_cellsA] in DCS. rewrite Z.add_0_l in DCS. exact (proj1 DCS). }
  assert (HX : sct_repA mc LB adr x) by (apply (proj1 (Forall_forall _ _) HF); rewrite EQ; apply in_app_iff; right; left; reflexivity).
  split.
  { destruct HX as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & REST).
    assert (ARR : forall o, arr_repA mc LB adr o -> arr_repA mc (OW ++ LB) adr o).
    { intros [[q' n']|] H; cbn in *; [| exact I]. destruct H as (B1 & B2 & B3). split; [exact B1|]. split; [apply in_or_app; right; exact B2| exact B3]. }
    split; [apply in_or_app; right; exact H1|]. split; [exact H2|]. split; [exact H3|].
    split; [apply ARR; exact H4|]. split; [apply ARR; exact H5|]. split; [apply ARR; exact H6|]. split; [apply ARR; exact H7|]. exact REST. }
  pose proof (AH_nodup _ _ _ _ HEAP) as ND. rewrite map_app in ND.
  intros Hin. apply in_map_iff in Hin. destruct Hin as (b & Eb & Hb).
  refine (ApErrKit.NoDup_app_disjoint _ _ pb ND _ _); [apply in_map_iff; exists (pb, out, BIO_SIZE); split; [reflexivity| exact HBIN]|].
  rewrite <- Eb. apply in_map. exact (sct_repA_blocks_in _ _ _ _ HX _ Hb).
Qed.

Section Act.
(* [comment removed for export] *)
Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : mem) (Σ : rts RTS) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z).
Variables (lo : Z) (K : list block) (ras : list Z) (adr : bptr -> Z) (k : skr bptr) (pb : bptr) (out pv W : Z).
Hypothesis PRE : ap_preA Σ st m OW LB E bo sp lo SCT_LIST_PRINT_STACK_A (SCT_LIST_PRINT_COST_A (zlength (sk_items k))) SCT_LIST_PRINT_FRAMES_A.
Hypothesis UW : uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras.
Hypothesis CTX : uk_ctx SCT_LIST_PRINT_A (bv_unsigned ra :: ras).
Hypothesis SK : sk_repA m LB adr k.
Hypothesis HBIN : In (pb, out, BIO_SIZE) OW.
Hypothesis NIDS : ~ In pb (es_ids st ++ env_ids E).
Hypothesis KOW : forall b, In b K -> In b OW.
Hypothesis KID : forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E).
Hypothesis KNB : forall b, In b K -> blk_id b <> pb.
Hypothesis WI1 : 2 + sk_wire k <= W.
Hypothesis WI2 : W <= MAX_SCT_LIST_SIZE.

Definition lframe : list cell := [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Local Notation POST := (ap_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB E lo m K (SCT_LIST_PRINT_COST_A (zlength (sk_items k))) (sct_print_resA st OW out pv)).

(* [comment removed for export] *)
Definition linv (Σc : rts RTS) (mc : mem) (nwc : Z) : Prop :=
  AHEAP Σc OW LB mc /\ mem_inv ctasegs mc /\ stk ctasegs mc lo (bv_unsigned sp + -80)
  /\ apres_ex LB OW (bv_unsigned sp) [(out, out + 128)]%Z m mc
  /\ rw_cells ctasegs mc (bv_unsigned sp + -80) lframe
  /\ rw_cells ctasegs mc out (bio_null_cells NULL_METHOD pv nwc) /\ 0 <= nwc < 2^64.

(* [comment removed for export] *)
Lemma base_facts :
  0 <= bv_unsigned sp < 2^64 /\ SEGTOP_A <= ACEIL /\ SHHI <= ACEIL /\ ACEIL + STACK_WIN <= USTACK_TOP /\ ACEIL <= lo
  /\ lo + 80 + SCT_PRINT_STACK_A <= bv_unsigned sp /\ bv_unsigned sp + 16 <= USTACK_TOP /\ bv_unsigned sp mod 16 = 0
  /\ 0 < out /\ out + 128 <= ACEIL /\ In (pb, out, 128) (OW ++ LB)
  /\ bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -80)) = bv_unsigned sp + -80
  /\ 2^22 <= rt_credit RTS Σ /\ (S (S (S (S (length FRM)))) < FRAMES_MAX)%nat
  /\ scts_print_costA (sk_items k) <= 2^21.
Proof.
  pose proof PRE as (HEAP & AS & IDS & DC & ST & CEIL & LOSP & TOP & AL16 & MI & CRED & FRMS).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3).
  assert (HBIN' : In (pb, out, 128) (OW ++ LB)) by (apply in_or_app; left; exact HBIN).
  pose proof (AH_range_gen _ _ _ _ _ HEAP HBIN') as (B0 & _ & _ & BC & _). cbn [blk_addr blk_size fst snd] in B0, BC.
  unfold SCT_LIST_PRINT_STACK_A in LOSP. unfold SCT_LIST_PRINT_COST_A in CRED. unfold SCT_LIST_PRINT_FRAMES_A in FRMS.
  pose proof CEIL as CEILu. unfold BnHeapA.ACEIL in CEILu. pose proof C1 as C1u. unfold SEGTOP_A, BnHeapA.ACEIL in C1u.
  repeat (split; [first [assumption| clear - LOSP; lia]|]).
  pose proof LOSP as LOSPu. unfold SCT_PRINT_STACK_A, SC_BODY_STACK_A, RT_STACK in LOSPu.
  split; [apply unsigned_lit; clear - SPR LOSPu CEILu C1u; lia|].
  split; [clear - CRED; lia|]. split; [clear - FRMS; lia|].
  (* [comment removed for export] *)
  pose proof (sk_repA_scts _ _ _ _ SK) as [HF _].
  assert (NN : Forall (fun x => 0 <= sc_extlen x /\ 0 <= sc_siglen x /\ 0 <= sc_bloblen x) (sk_items k)).
  { apply Forall_forall. intros x Hx. pose proof (proj1 (Forall_forall _ _) HF x Hx) as (_ & _ & _ & _ & A2 & A3 & A4 & _ & _ & _ & _ & _ & _ & EXL & _).
    unfold sc_siglen, sc_bloblen. rewrite EXL. unfold CtSctP.SctRep.olen.
    split; [destruct (sc_ext x) as [[q n]|]; [destruct A2 as (N0 & _); clear - N0; lia| clear; lia]|].
    split; [destruct (sc_sig x) as [[q n]|]; [destruct A3 as (N0 & _); clear - N0; lia| clear; lia]|].
    destruct (sc_blob x) as [[q n]|]; [destruct A4 as (N0 & _); clear - N0; lia| clear; lia]. }
  pose proof (scts_print_costA_wire _ NN) as CW. unfold sk_wire in WI1. unfold MAX_SCT_LIST_SIZE in WI2. clear - CW WI1 WI2. lia.
Qed.

(* [comment removed for export] *)
Lemma items_nonneg : Forall (fun x => 0 <= sc_extlen x /\ 0 <= sc_siglen x /\ 0 <= sc_bloblen x) (sk_items k).
Proof.
  pose proof (sk_repA_scts _ _ _ _ SK) as [HF _].
  apply Forall_forall. intros x Hx. pose proof (proj1 (Forall_forall _ _) HF x Hx) as (_ & _ & _ & _ & A2 & A3 & A4 & _ & _ & _ & _ & _ & _ & EXL & _).
  unfold sc_siglen, sc_bloblen. rewrite EXL. unfold CtSctP.SctRep.olen.
  split; [destruct (sc_ext x) as [[q n]|]; [destruct A2 as (N0 & _); clear - N0; lia| clear; lia]|].
  split; [destruct (sc_sig x) as [[q n]|]; [destruct A3 as (N0 & _); clear - N0; lia| clear; lia]|].
  destruct (sc_blob x) as [[q n]|]; [destruct A4 as (N0 & _); clear - N0; lia| clear; lia].
Qed.

Lemma suffix_cost_nonneg : forall done rest, sk_items k = done ++ rest -> 0 <= scts_print_costA rest.
Proof.
  intros done rest EQ. apply scts_print_costA_nonneg. pose proof items_nonneg as NN. rewrite EQ in NN. apply Forall_app in NN. exact (proj2 NN).
Qed.

(* [comment removed for export] *)
Lemma off_bio : forall a, aclient_addr (OW ++ LB) (bv_unsigned sp) a ->
  (forall b, In b (OW ++ LB) -> blk_addr b <= a < blk_addr b + blk_size b -> blk_id b <> pb) -> outside [(out, out + 128)]%Z a.
Proof.
  intros a Ha Hb. pose proof PRE as (HEAP & _ & _ & _ & _ & CEIL & LOSP & _).
  pose proof base_facts as (_ & C1 & _ & _ & _ & LO' & _ & _ & OB0 & OBC & HBIN' & _).
  pose proof CEIL as CEILu. unfold BnHeapA.ACEIL in CEILu. pose proof OBC as OBCu. unfold BnHeapA.ACEIL in OBCu. pose proof C1 as C1u. unfold SEGTOP_A, BnHeapA.ACEIL in C1u.
  cbn [outside fst snd]. split; [| exact I].
  destruct Ha as [Ha|[Ha|(b & HbL & Hr)]].
  - clear - Ha OBCu CEILu LO'. unfold SCT_PRINT_STACK_A, SC_BODY_STACK_A, RT_STACK in LO'. lia.
  - intros Hin. exact (ApErrKitA2.blk_not_static Σ OW LB m (pb, out, 128) a HEAP HBIN' Hin Ha).
  - pose proof (Hb b HbL Hr) as NE.
    pose proof (AH_disjoint_gen _ _ _ _ b (pb, out, 128) HEAP HbL HBIN' NE) as DJ. cbn [blk_addr blk_size fst snd] in DJ. clear - DJ Hr. lia.
Qed.

Lemma lb_not_bio : forall b, In b LB -> blk_id b <> pb.
Proof.
  intros b Hb Eb. pose proof PRE as (HEAP & _). pose proof (AH_nodup _ _ _ _ HEAP) as ND. rewrite map_app in ND.
  refine (ApErrKit.NoDup_app_disjoint _ _ pb ND _ _); [apply in_map_iff; exists (pb, out, BIO_SIZE); split; [reflexivity| exact HBIN]| rewrite <- Eb; apply in_map; exact Hb].
Qed.

(* [comment removed for export] *)
Lemma lp_open : forall Σc mc nwc, linv Σc mc nwc ->
  ap_state st mc OW E bo /\ data_cells mc OW st /\ sk_repA mc LB adr k /\ crypto_statics mc /\ realloc_statics mc
  /\ uw_chain USTACK_TOP mc (bv_unsigned sp + -80) (bv_unsigned sp) (bv_unsigned ra :: ras).
Proof.
  intros Σc mc nwc (HEAPc & MIc & STc & AX & FR & HB & NW).
  pose proof PRE as (HEAP & AS & IDS & DC & ST & CEIL & LOSP & TOP & AL16 & MI & CRED & FRMS).
  pose proof base_facts as (SPR & C1 & C2 & C3 & _ & LO' & _ & _ & OB0 & OBC & HBIN' & ESP & _).
  pose proof CEIL as CEILu. unfold BnHeapA.ACEIL in CEILu. pose proof OBC as OBCu. unfold BnHeapA.ACEIL in OBCu. pose proof TOP as TOPu. unfold USTACK_TOP in TOPu.
  unfold apres_ex in AX.
  assert (ASc : ap_state st mc OW E bo) by (exact (ap_state_but_blockA Σ st m mc OW LB E bo (bv_unsigned sp) pb out 128 HEAP AS IDS HBIN NIDS AX)).
  split; [exact ASc|]. split; [exact (data_cells_but_blockA Σ st m mc OW LB E bo (bv_unsigned sp) pb out 128 HEAP AS DC HBIN NIDS AX)|].
  split.
  { eapply sk_repA_agreeP; [exact AX| | exact SK]. intros b a Hb Hr. pose proof (sk_repA_blocks_in _ _ _ _ b SK Hb) as HbL.
    assert (HbL' : In b (OW ++ LB)) by (apply in_or_app; right; exact HbL).
    split; [right; right; exists b; split; [exact HbL'| exact Hr]|].
    apply off_bio; [right; right; exists b; split; [exact HbL'| exact Hr]|].
    intros b' Hb' Hr' Eb'. pose proof (lb_not_bio b HbL) as NE.
    assert (NE2 : blk_id b' <> blk_id b) by (intros E2; apply NE; rewrite <- E2; exact Eb').
    pose proof (AH_disjoint_gen _ _ _ _ b' b HEAP Hb' HbL' NE2) as DJ. clear - DJ Hr Hr'. lia. }
  pose proof ASc as (_ & (CSc & RSc & _) & _). split; [exact CSc|]. split; [exact RSc|].
  (* [comment removed for export] *)
  unfold lframe in FR.
  apply (uw_push_frame mc (bv_unsigned sp + -80) (bv_unsigned sp) 80 [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] (bv_unsigned ra) (bv_unsigned s0) ras);
    [reflexivity| clear; lia| clear - AL16; Z.div_mod_to_equations; lia| clear - TOPu; unfold USTACK_TOP; lia| apply bv_unsigned_in_range
    | rewrite !Z_to_bv_bv_unsigned; exact FR|].
  eapply uw_chain_agreeP; [exact AX| exact UW|]. intros a X Ha. split; [left; clear - Ha X; lia|].
  cbn [outside fst snd]; split; [clear - Ha X OBCu CEILu LO'; unfold SCT_PRINT_STACK_A, SC_BODY_STACK_A, RT_STACK in LO'; lia| exact I].
Qed.

(* [comment removed for export] *)
Lemma linv_munch : forall Σc mc mc' nwc lo' hi',
  linv Σc mc nwc -> munch [(lo', hi')] mc mc' -> wmono ctasegs mc mc' -> mem_inv ctasegs mc' -> stk ctasegs mc' lo (bv_unsigned sp + -80) ->
  ACEIL <= lo' -> hi' <= bv_unsigned sp + -80 -> linv Σc mc' nwc.
Proof.
  intros Σc mc mc' nwc lo' hi' (HEAPc & MIc & STc & AX & FR & HB & NW) MU WM MI' ST' H1 H2.
  pose proof PRE as (HEAP & _). pose proof base_facts as (SPR & C1 & C2 & C3 & CEIL & LO' & TOP & _ & OB0 & OBC & HBIN' & ESP & _).
  pose proof CEIL as CEILu. unfold BnHeapA.ACEIL in CEILu. pose proof OBC as OBCu. unfold BnHeapA.ACEIL in OBCu. pose proof C1 as C1u. unfold SEGTOP_A, BnHeapA.ACEIL in C1u.
  pose proof H1 as H1u. unfold BnHeapA.ACEIL in H1u. pose proof TOP as TOPu. unfold USTACK_TOP in TOPu.
  pose proof (agree_on_of_munch_nw _ _ _ MU) as AG.
  split. { eapply AH_frame; [exact HEAPc| exact MU| exact WM|]. constructor; [left; cbn [fst snd]; clear - H1 H2 TOP; unfold USTACK_TOP in *; lia| constructor]. }
  split; [exact MI'|]. split; [exact ST'|].
  split.
  { unfold apres_ex in *. eapply agree_on_trans; [exact AX|]. eapply agree_on_mono; [exact AG|]. intros a [Ha _]. cbn [outside fst snd]. split; [| exact I].
    destruct Ha as [Ha|[Ha|(b & HbL & Hr)]].
    - clear - Ha H2. lia.
    - destruct Ha as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. destruct Hin as [E0|[E0|[E0|[]]]]; injection E0 as <- <-; clear - Hr C1u H1u; lia.
    - pose proof (AH_range_gen _ _ _ _ b HEAP HbL) as (_ & _ & _ & B3 & _). clear - B3 Hr H1u. unfold BnHeapA.ACEIL in B3. lia. }
  split. { eapply rw_cells_agree; [exact AG| exact FR|]. intros a Ha. unfold lframe in Ha. cbn [cells_size csize Nat.add outside fst snd] in Ha |- *. split; [clear - Ha H2; lia| exact I]. }
  split; [| exact NW].
  eapply rw_cells_agree; [exact AG| exact HB|]. intros a Ha. unfold bio_null_cells, bio_cells in Ha. cbn [cells_size csize Nat.add outside fst snd] in Ha |- *.
  split; [clear - Ha OBCu H1u; lia| exact I].
Qed.

(* [comment removed for export] *)
Lemma linv_call : forall Σc mc nwc Σ' mc' nw',
  linv Σc mc nwc -> AHEAP Σ' OW LB mc' -> mem_inv ctasegs mc' -> stk ctasegs mc' lo (bv_unsigned sp + -80) ->
  apres_ex LB OW (bv_unsigned sp + -80) [(out, out + 128)]%Z mc mc' ->
  rw_cells ctasegs mc' out (bio_null_cells NULL_METHOD pv nw') -> 0 <= nw' < 2^64 -> linv Σ' mc' nw'.
Proof.
  intros Σc mc nwc Σ' mc' nw' (HEAPc & MIc & STc & AX & FR & HB & NW) HEAP' MI' ST' AP HB' NW'.
  pose proof base_facts as (SPR & C1 & C2 & C3 & CEIL & LO' & TOP & _ & OB0 & OBC & HBIN' & ESP & _).
  pose proof CEIL as CEILu. unfold BnHeapA.ACEIL in CEILu. pose proof OBC as OBCu. unfold BnHeapA.ACEIL in OBCu. pose proof TOP as TOPu. unfold USTACK_TOP in TOPu.
  split; [exact HEAP'|]. split; [exact MI'|]. split; [exact ST'|].
  split.
  { unfold apres_ex in *. eapply agree_on_trans; [exact AX|]. eapply agree_on_mono; [exact AP|]. intros a [Ha Ho]. split; [| exact Ho].
    destruct Ha as [Ha|Ha]; [left; clear - Ha; lia| right; exact Ha]. }
  split.
  { unfold apres_ex in AP. eapply rw_cells_agree; [exact AP| exact FR|]. intros a Ha. unfold lframe in Ha. cbn [cells_size csize Nat.add outside fst snd] in Ha |- *.
    split; [left; clear - Ha TOPu; unfold USTACK_TOP; lia|]. split; [| exact I]. clear - Ha OBCu CEILu LO'. unfold SCT_PRINT_STACK_A, SC_BODY_STACK_A, RT_STACK in LO'. lia. }
  split; [exact HB'| exact NW'].
Qed.

(* [comment removed for export] *)
Lemma lp_close : forall Σc mc nwc (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Fc : bvmap 5 word) (fcc : bv 32),
  linv Σc mc nwc -> rt_credit RTS Σ - 2^22 <= rt_credit RTS Σc ->
  POST (tt, st) Σc (MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        Fc (ret_pc ra) fcc None mc (seg_rom ctasegs)).
Proof.
  intros until fcc. intros LI CR. pose proof LI as (HEAPc & MIc & STc & AX & FR & HB & NW).
  pose proof (lp_open _ _ _ LI) as (ASc & DCc & SKc & CSc & RSc & UWc).
  pose proof PRE as (HEAP & AS & IDS & DC & ST & CEIL & LOSP & TOP & AL16 & MI & CRED & FRMS).
  pose proof base_facts as (SPR & C1 & C2 & C3 & _ & LO' & _ & _ & OB0 & OBC & HBIN' & ESP & CRED22 & _).
  pose proof CEIL as CEILu. unfold BnHeapA.ACEIL in CEILu.
  (* [comment removed for export] *)
  pose proof FR as FR'. unfold lframe in FR'. eapply stk_release in FR'; [| exact STc| clear - LO' CEILu; unfold SCT_PRINT_STACK_A, SC_BODY_STACK_A, RT_STACK in LO'; lia].
  cbn [cells_size csize Nat.add] in FR'. replace (bv_unsigned sp + -80 + Z.of_nat 80) with (bv_unsigned sp) in FR' by (clear; lia).
  unfold ap_postA. do 15 eexists. exists Fc, fcc, mc, OW, bo. split; [reflexivity|]. cbn [fst snd].
  split.
  { unfold ap_preA. split; [exact HEAPc|]. split; [exact ASc|]. split; [exact IDS|]. split; [exact DCc|]. split; [exact FR'|]. split; [exact CEIL|].
    split; [clear - LOSP; unfold SCT_LIST_PRINT_STACK_A, SCT_PRINT_STACK_A, SC_BODY_STACK_A, RT_STACK in LOSP; lia|]. split; [exact TOP|]. split; [exact AL16|]. split; [exact MIc|].
    split; [clear - CR CRED22; lia| unfold SCT_LIST_PRINT_FRAMES_A in FRMS; clear - FRMS; lia]. }
  split.
  { unfold ax_pres, ax_client. unfold apres_ex in AX. eapply agree_on_mono; [exact AX|]. intros a [_ Ha]. split; [eapply aclient_addr_mono; [| exact Ha]; intros b Hb; apply in_or_app; right; exact Hb|].
    apply off_bio; [eapply aclient_addr_mono; [| exact Ha]; intros b Hb; apply in_or_app; right; exact Hb|].
    intros b HbL Hr. destruct Ha as [Ha'|[Ha'|(b2 & Hb2 & Hr2)]].
    - exfalso. pose proof (AH_range_gen _ _ _ _ b HEAP HbL) as (_ & _ & _ & B3 & _). clear - B3 Hr Ha' CEILu LO'. unfold BnHeapA.ACEIL in B3. unfold SCT_PRINT_STACK_A, SC_BODY_STACK_A, RT_STACK in LO'. lia.
    - exfalso. exact (ApErrKitA2.blk_not_static Σ OW LB m b a HEAP HbL Hr Ha').
    - intros Eb. pose proof (lb_not_bio b2 Hb2) as NE2.
      assert (NE : blk_id b2 <> blk_id b) by (rewrite Eb; exact NE2).
      pose proof (AH_disjoint_gen _ _ _ _ b2 b HEAP ltac:(apply in_or_app; right; exact Hb2) HbL NE) as DJ. clear - DJ Hr Hr2. lia. }
  split; [unfold SCT_LIST_PRINT_COST_A; exact CR|].
  split.
  { split; [exact KOW|]. split; [intros b Hb Hin; apply (KID b Hb); apply in_app_iff; left; exact Hin|].
    intros a Ha (b & Hb & Hr). unfold apres_ex in AX. apply AX; [exact Ha|].
    assert (HbL : In b (OW ++ LB)) by (apply in_or_app; left; exact (KOW b Hb)).
    split; [right; right; exists b; split; [exact HbL| exact Hr]|].
    apply off_bio; [right; right; exists b; split; [exact HbL| exact Hr]|].
    intros b' Hb' Hr' Eb'. pose proof (KNB b Hb) as NE.
    assert (NE2 : blk_id b' <> blk_id b) by (intros E2; apply NE; rewrite <- E2; exact Eb').
    pose proof (AH_disjoint_gen _ _ _ _ b' b HEAP Hb' HbL NE2) as DJ. clear - DJ Hr Hr'. lia. }
  unfold sct_print_resA. split; [reflexivity|]. split; [reflexivity|]. exists nwc. split; [exact NW| exact HB].
Qed.

Local Ltac step := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
Local Ltac rstep := OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.      (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma lp_finishA : forall Σc mc nwc (Fc : bvmap 5 word) (fcc : bv 32)
    (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x22 x23 x24 t3 t4 t5 t6 : word),
  linv Σc mc nwc -> rt_credit RTS Σ - 2^22 <= rt_credit RTS Σc ->
  evt ctasegs (POST (tt, st) Σc)
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp (wz TP_A) t0 t1 t2 sp (Z_to_bv 64 0) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 A_SEP_A) (Z_to_bv 64 4) (Z_to_bv 64 out) (Z_to_bv 64 (adr (sk_blk k))) x22 x23 x24 s9 s10 s11 t3 t4 t5 t6)
        Fc (Z_to_bv 64 SCT_LIST_EPI_A) fcc None mc (seg_rom ctasegs)).
Proof.
  intros until t6. intros LI CR. pose proof LI as (HEAPc & MI & ST & AX & FR & HB & NW).
  pose proof base_facts as (SPR & C1 & C2 & C3 & CEIL & LO' & TOP & AL16 & OB0 & OBC & HBIN' & ESP & _).
  pose proof CEIL as CEILu. unfold BnHeapA.ACEIL in CEILu. pose proof LO' as LOu. unfold SCT_PRINT_STACK_A, SC_BODY_STACK_A, RT_STACK in LOu.
  unfold lframe in FR. unfold SCT_LIST_EPI_A, A_SEP_A, MallocRep.wz.
  pose proof (munch_refl [(lo, bv_unsigned sp + -80)] mc) as MU. pose proof (wmono_refl ctasegs mc) as WM.
  do 10 zstep.
  zstep. zstep.
  apply evt_done. apply (lp_close Σc mc nwc); [exact LI| exact CR].
Qed.

(* [comment removed for export] *)
Lemma lp_loopA : forall t x done i Σc mc nwc (Fc : bvmap 5 word) (fcc : bv 32)
    (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  sk_items k = done ++ x :: t -> i = zlength done ->
  linv Σc mc nwc -> rt_credit RTS Σ - 2^22 + scts_print_costA (x :: t) <= rt_credit RTS Σc ->
  implAp (scts_print (x :: t) st) Σc POST
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp (wz TP_A) t0 t1 t2 sp (Z_to_bv 64 0) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 A_SEP_A) (Z_to_bv 64 4) (Z_to_bv 64 out) (Z_to_bv 64 (adr (sk_blk k))) (Z_to_bv 64 (sk_num k)) (Z_to_bv 64 i) (Z_to_bv 64 A_C10_A)
             s9 s10 s11 t3 t4 t5 t6)
        Fc (Z_to_bv 64 SCT_LIST_LOOP_A) fcc None mc (seg_rom ctasegs)).
Proof.
  induction t as [|y t IH]; intros x done i Σc mc nwc Fc fcc x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 EQ Ei LI CR; subst i.
  all: pose proof LI as (HEAPc & MI & ST & AX & FR & HB & NW).
  all: pose proof PRE as (HEAP & _).
  all: pose proof base_facts as (SPR & C1 & C2 & C3 & CEIL & LO' & TOP & AL16 & OB0 & OBC & HBIN' & ESP & CRED22 & FLEN & _).
  all: pose proof CEIL as CEILu; unfold BnHeapA.ACEIL in CEILu; pose proof LO' as LOu; unfold SCT_PRINT_STACK_A, SC_BODY_STACK_A, RT_STACK in LOu;
       pose proof TOP as TOPu; unfold USTACK_TOP in TOPu; pose proof OBC as OBCu; unfold BnHeapA.ACEIL in OBCu.
  all: destruct (lp_itemA Σc mc OW LB adr k pb out done x _ HEAPc (proj1 (proj2 (proj2 (lp_open _ _ _ LI)))) HBIN EQ)
         as (q & na & ED & HST & ALS & HQ & ALD & NA & RNUM & RDAT & IR & N23 & RITEM & REPX & NPB).
  all: pose proof (zlength_nonneg'' done) as D0.
  all: pose proof (suffix_cost_nonneg (done ++ [x]) _ ltac:(rewrite <- app_assoc; exact EQ)) as CTt.
  all: cbn [scts_print_costA] in CR, CTt.
  (* [comment removed for export] *)
  all: lazymatch goal with |- implAp (scts_print (?x0 :: ?r0) ?st0) ?S0 ?Q0 ?ms0 =>
         change (implAp (apbind (sct_print x0 st0) (fun p => scts_print r0 (snd p))) S0 Q0 ms0) end.
  all: unfold SCT_LIST_LOOP_A, A_SEP_A, A_C10_A, MallocRep.wz in *.
  all: pose proof (munch_refl [(lo, bv_unsigned sp + -80)] mc) as MU; pose proof (wmono_refl ctasegs mc) as WM.
  all: unfold lframe in FR.
  all: apply implAp_from_evt.
  (* [comment removed for export] *)
  all: zstep; zstep; zstep.
  all: eapply evt_cut; [eapply (OPENSSL_sk_value_specA) with (lo := lo) (OW := OW) (LB := LB) (kb := sk_blk k) (q := q) (SA := adr (sk_blk k)) (num := sk_num k) (D := adr q) (na := na) (i := zlength done) (V := adr (sc_blk x));
         [exact HEAPc| rewrite ESP; exact ST| exact MI| exact CEIL| rewrite ESP; clear - LOu; lia| exact HST| uchk_open; exact ALS| exact HQ| uchk_open; exact ALD| exact NA
         | exact RNUM| exact RDAT| exact IR| clear - N23; lia| exact RITEM| reflexivity| reflexivity]|].
  all: cbv beta; intros msV PO; unfold leaf16A_post, leafA_post in PO; rewrite ?ESP in PO;
       destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & mV & -> & MUv & WMv & MIv & STv & _).
  all: rewrite (ret_pc_even 0x3383d4) by (clear; lia).
  all: assert (LIv : linv Σc mV nwc) by (eapply (linv_munch Σc mc mV nwc); [exact LI| exact MUv| exact WMv| exact MIv| exact STv| clear - CEILu LOu; unfold BnHeapA.ACEIL; lia| clear; lia]).
  all: clear MU WM MUv WMv MIv STv HEAPc MI ST AX FR HB RNUM RDAT RITEM REPX; pose proof LIv as (HEAPc & MI & ST & AX & FR & HB & _).
  all: pose proof (lp_open _ _ _ LIv) as (_ & _ & SKv & CSv & RSv & UWv).
  all: destruct (lp_itemA Σc mV OW LB adr k pb out done x _ HEAPc SKv HBIN EQ) as (q' & na' & _ & _ & _ & _ & _ & _ & RNUM & _ & _ & _ & _ & REPX & _).
  all: pose proof (munch_refl [(lo, bv_unsigned sp + -80)] mV) as MU; pose proof (wmono_refl ctasegs mV) as WM.
  all: unfold lframe in FR.
  (* [comment removed for export] *)
  all: zstep; zstep; zstep; zstep.
  all: apply evt_done.
  all: eapply (SCT_print_bindA _) with (lo := lo) (pb := pb) (nw := nwc) (adr := adr) (ras := bv_unsigned ra :: ras);
         [exact HEAPc| rewrite ESP; exact ST| exact CEIL| rewrite ESP; unfold SCT_PRINT_STACK_A, SC_BODY_STACK_A, RT_STACK; clear - LOu; lia| rewrite ESP; clear - TOPu; unfold USTACK_TOP; lia
         | rewrite ESP; uchk_open; clear - AL16 SPR LOu CEILu; Z.div_mod_to_equations; lia
         | exact MI| reflexivity| exact FLEN| clear - CR CRED22 CTt; lia| exact CSv| exact RSv| exact REPX| exact HBIN| exact NPB| exact HB| exact NW
         | rewrite ESP; exact UWv| rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_SCT_LIST_print_34c840 CTX)
         | reflexivity| reflexivity| reflexivity| reflexivity|].
  all: intros ΣR msR PO; unfold sct_print_postA in PO; rewrite ?ESP in PO;
       destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & FcR & fcR & mR & nwR & -> & HEAPR & CRR & STR & MIR & APR & NWR & HBR).
  all: cbn [fst snd]. all: rewrite (ret_pc_even 0x3383e4) by (clear; lia). all: unfold MallocRep.wz.
  all: assert (LIR : linv ΣR mR nwR) by (eapply (linv_call Σc mV nwc); [exact LIv| exact HEAPR| exact MIR| exact STR| exact APR| exact HBR| exact NWR]).
  all: clear MU WM HEAPc MI ST AX FR HB SKv CSv RSv UWv REPX HEAPR STR MIR APR HBR LIv; pose proof LIR as (HEAPc & MI & ST & AX & FR & HB & _).
  all: pose proof (lp_open _ _ _ LIR) as (_ & _ & SKR & _).
  all: destruct (lp_itemA ΣR mR OW LB adr k pb out done x _ HEAPc SKR HBIN EQ) as (q'' & na'' & _ & _ & _ & _ & _ & _ & RNUM' & _).
  all: pose proof (munch_refl [(lo, bv_unsigned sp + -80)] mR) as MU; pose proof (wmono_refl ctasegs mR) as WM.
  all: unfold lframe in FR.
  all: clear mV RNUM. all: rename RNUM' into RNUM.
  (* [comment removed for export] *)
  all: apply implAp_from_evt.
  all: zstep; zstep.
  all: eapply evt_cut; [eapply (OPENSSL_sk_num_specA) with (lo := lo) (OW := OW) (LB := LB) (kb := sk_blk k) (SA := adr (sk_blk k)) (num := sk_num k);
         [exact HEAPc| rewrite ESP; exact ST| exact MI| exact CEIL| rewrite ESP; clear - LOu; lia| exact HST| uchk_open; exact ALS| exact RNUM| clear - N23 IR; lia| reflexivity]|].
  all: cbv beta; intros msN PO; unfold leaf16A_post, leafA_post in PO; rewrite ?ESP in PO;
       destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & mN & -> & MUn & WMn & MIn & STn & _).
  all: rewrite (ret_pc_even 0x3383f0) by (clear; lia).
  all: assert (LIn : linv ΣR mN nwR) by (eapply (linv_munch ΣR mR mN nwR); [exact LIR| exact MUn| exact WMn| exact MIn| exact STn| clear - CEILu LOu; unfold BnHeapA.ACEIL; lia| clear; lia]).
  all: clear MU WM MUn WMn MIn STn HEAPc MI ST AX FR HB RNUM SKR LIR; pose proof LIn as (HEAPc & MI & ST & AX & FR & HB & _).
  all: pose proof (munch_refl [(lo, bv_unsigned sp + -80)] mN) as MU; pose proof (wmono_refl ctasegs mN) as WM.
  all: unfold lframe in FR. all: clear mR.
  (* [comment removed for export] *)
  2: pose proof (zlength_nonneg'' t) as TL0.
  1: assert (LEN : sk_num k = zlength done + 1) by (unfold sk_num; rewrite EQ, zlength_app'; unfold zlength; cbn [length]; clear; lia).
  2: assert (LEN : sk_num k = zlength done + 2 + zlength t) by (unfold sk_num; rewrite EQ, zlength_app'; unfold zlength in *; cbn [length]; clear; lia).
  all: zstep; rewrite (swrap32_small (sk_num k + -1)) by (clear - N23 IR; lia).
  - (* [comment removed for export] *)
    zstep. if_cases KB; zify_cond KB; [| exfalso; revert KB; rewrite ?signed_small, ?unsigned_lit by (clear - N23 IR D0 LEN; lia); clear - N23 IR D0 LEN; lia]. try clear KB.
    zstep. rewrite (swrap32_small (zlength done + 1)) by (clear - N23 IR D0; lia).
    zstep. if_cases KN; zify_cond KN; [exfalso; revert KN; rewrite ?unsigned_lit by (clear - N23 IR D0 LEN; lia); clear - LEN; lia|]. try clear KN.
    apply evt_done. cbn [scts_print]. unfold aret. apply implAp_ret_evt.
    eapply lp_finishA; [exact LIn| clear - CRR CR; lia].
  - (* [comment removed for export] *)
    zstep. if_cases KB; zify_cond KB; [exfalso; revert KB; rewrite ?signed_small, ?unsigned_lit by (clear - N23 IR D0 LEN TL0; lia); clear - N23 IR D0 LEN TL0; lia|]. try clear KB.
    zstep. zstep. zstep. zstep.
    apply evt_done.
    eapply implAp_step.
    { eapply (BIO_printf_null_cpsA PFC) with (lo := lo) (OW := OW) (LB := LB) (pb := pb) (out := out) (pv := pv) (nw := nwR) (A := 0xa7d40) (fmt := FMT_C10) (args := [PA_s [10]]) (o := [10]);
        [exact HEAPc| rewrite ESP; exact ST| exact CEIL
        | rewrite ESP; unfold BIO_PRINTF_NULL_STACK, BIO_VPRINTF_NULL_STACK, BIO_WRITE_NULL_STACK, BPRF_FRAME, BVPF_FRAME, BWI_FRAME, RT_STACK; clear - LOu; lia
        | rewrite ESP; clear - TOPu; unfold USTACK_TOP; lia
        | rewrite ESP; uchk_open; clear - AL16 SPR LOu CEILu; Z.div_mod_to_equations; lia
        | exact MI| reflexivity| clear - FLEN; lia| clear - CRR CR CTt CRED22; lia| exact HBIN| exact HB| exact NWR
        | exact (vfmtA_C10 [10] ltac:(change (zlength [10]) with 1; clear; lia))| change (zlength [10]) with 1; clear; lia
        | cbn [vargsA_ok]; split; [apply sepA_vargA| exact I]| reflexivity| reflexivity]. }
    intros ΣP msP PO. unfold bio_printf_null_post in PO. rewrite ?ESP in PO.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & FcP & fcP & mP & -> & MIp & STp & APp & HEAPp & _ & CRp & HBp).
    rewrite (ret_pc_even 0x338408) by (clear; lia). unfold MallocRep.wz.
    rewrite <- bio_null_cells_mod in HBp. unfold BIO_SIZE in APp.
    assert (LIp : linv ΣP mP ((nwR + zlength [10]) mod 2^64)).
    { eapply (linv_call ΣR mN nwR); [exact LIn| exact HEAPp| exact MIp| exact STp| exact APp| exact HBp| apply Z.mod_pos_bound; clear; lia]. }
    clear MU WM HEAPc MI ST AX FR HB MIp STp APp HBp LIn. pose proof LIp as (HEAPc & MI & ST & AX & FR & HB & _).
    pose proof (munch_refl [(lo, bv_unsigned sp + -80)] mP) as MU. pose proof (wmono_refl ctasegs mP) as WM.
    unfold lframe in FR. clear mN.
    apply implAp_from_evt.
    (* [comment removed for export] *)
    zstep. rewrite (swrap32_small (zlength done + 1)) by (clear - N23 IR D0; lia).
    zstep. if_cases KN; zify_cond KN; [| exfalso; revert KN; rewrite ?unsigned_lit by (clear - N23 IR D0 LEN TL0; lia); clear - LEN TL0; lia]. try clear KN.
    apply evt_done.
    eapply (IH y (done ++ [x]) (zlength done + 1));
      [rewrite <- app_assoc; exact EQ| rewrite zlength_app'; reflexivity| exact LIp| cbn [scts_print_costA] in CRp |- *; clear - CRp CRR CR; lia].
Qed.

(* [comment removed for export] *)
Lemma lp_mainA : forall (tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (nw : Z),
  tp = wz TP_A -> a0 = wz (adr (sk_blk k)) -> a1 = wz out -> a2 = wz 4 -> a3 = wz A_SEP_A -> a4 = wz 0 ->
  rw_cells ctasegs m out (bio_null_cells NULL_METHOD pv nw) -> 0 <= nw < 2^64 ->
  implAp (sct_list_print k st) Σ POST
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz SCT_LIST_PRINT_A) fc None m (seg_rom ctasegs)).
Proof.
  intros until nw. intros -> -> -> -> -> -> HB NW.
  pose proof PRE as (HEAP & AS & IDS & DC & ST & CEIL & LOSP & TOP & AL16 & MI & CRED & FRMS).
  pose proof base_facts as (SPR & C1 & C2 & C3 & _ & LO' & _ & _ & OB0 & OBC & HBIN' & ESP & CRED22 & FLEN & CW).
  pose proof CEIL as CEILu. unfold BnHeapA.ACEIL in CEILu. pose proof LO' as LOu. unfold SCT_PRINT_STACK_A, SC_BODY_STACK_A, RT_STACK in LOu.
  pose proof TOP as TOPu. unfold USTACK_TOP in TOPu. pose proof OBC as OBCu. unfold BnHeapA.ACEIL in OBCu. pose proof C1 as C1u. unfold SEGTOP_A, BnHeapA.ACEIL in C1u.
  unfold SCT_LIST_PRINT_A, A_SEP_A, MallocRep.wz.
  unfold bio_null_cells, bio_cells in HB.
  (* [comment removed for export] *)
  pose proof (sk_repA_free_view _ _ _ _ SK) as ((RNUM & _ & _) & HSTl & HOD & _ & _ & _). pose proof (proj2 (proj1 SK)) as ALS.
  assert (HST : In (sk_blk k, adr (sk_blk k), STACK_SIZE) (OW ++ LB)) by (apply in_or_app; right; exact HSTl).
  assert (NUMR : 0 <= sk_num k < 2^23).
  { pose proof (zlength_nonneg'' (sk_items k)) as Z0. pose proof SK as (_ & _ & HD & _ & _).
    destruct (sk_data k) as [[q na]|]; [destruct HD as (_ & _ & H3 & H4 & _); clear - Z0 H3 H4; unfold sk_num in *; lia| unfold sk_num; rewrite HD; unfold zlength; cbn; clear; lia]. }
  unfold MallocRep.wz in RNUM.
  pose proof (AH_range_gen _ _ _ _ _ HEAP HST) as (BS0 & _ & _ & BS3 & _). cbn [blk_addr blk_size fst snd] in BS0, BS3. unfold BnHeapA.ACEIL, STACK_SIZE in BS3.
  assert (SEPK : adr (sk_blk k) + 56 <= bv_unsigned sp + -80) by (clear - BS3 CEILu LOu; lia).
  assert (SEPB : out + 128 <= bv_unsigned sp + -80) by (clear - OBCu CEILu LOu; lia).
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  apply implAp_from_evt.
  (* [comment removed for export] *)
  carve_frame 80%nat ST. zstep. do 10 zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  (* [comment removed for export] *)
  zstep. name_mem m1.
  match goal with H : munch _ m m1 |- _ => rename H into MU1 end. match goal with H : wmono ctasegs m m1 |- _ => rename H into WM1 end.
  assert (HEAP1 : AHEAP Σ OW LB m1).
  { eapply AH_frame; [exact HEAP| exact MU1| exact WM1|]. constructor; [left; cbn [fst snd]; clear - CEIL TOP; unfold USTACK_TOP in *; lia| constructor]. }
  eapply evt_cut; [eapply (OPENSSL_sk_num_specA) with (lo := lo) (OW := OW) (LB := LB) (kb := sk_blk k) (SA := adr (sk_blk k)) (num := sk_num k);
    [exact HEAP1| rewrite ESP; exact ST| exact MI| exact CEIL| rewrite ESP; clear - LOu; lia| exact HST| uchk_open; exact ALS| exact RNUM| clear - NUMR; lia| reflexivity]|].
  cbv beta. intros ms2 PO. unfold leaf16A_post, leafA_post in PO. rewrite ?ESP in PO.
  destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & -> & MU2 & WM2 & MI2 & ST2 & _).
  rewrite (ret_pc_even 0x3383b0) by (clear; lia).
  (* [comment removed for export] *)
  assert (LI1 : linv Σ m1 nw).
  { split; [exact HEAP1|]. split; [exact MI|]. split; [exact ST|].
    split. { unfold apres_ex. eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU1)|]. intros a [Ha _]. cbn [outside fst snd]. split; [| exact I].
             destruct Ha as [Ha|[Ha|(b & HbL & Hr)]].
             - clear - Ha. lia.
             - destruct Ha as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. destruct Hin as [E0|[E0|[E0|[]]]]; injection E0 as <- <-; clear - Hr C1u CEILu; lia.
             - pose proof (AH_range_gen _ _ _ _ b HEAP HbL) as (_ & _ & _ & B3 & _). clear - B3 Hr CEILu. unfold BnHeapA.ACEIL in B3. lia. }
    split; [exact FR|]. split; [| exact NW].
    first [ exact HB
          | eapply rw_cells_agree; [apply (agree_on_of_munch_nw _ _ _ MU1)| exact HB|]; intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *;
            split; [clear - Ha OBCu CEILu; lia| exact I] ]. }
  assert (LI2 : linv Σ m2 nw).
  { eapply (linv_munch Σ m1 m2 nw); [exact LI1| exact MU2| exact WM2| exact MI2| exact ST2| clear - CEILu LOu; unfold BnHeapA.ACEIL; lia| clear; lia]. }
  clear MU1 WM1 MU2 WM2 MI2 ST2 RNUM HEAP1 LI1. try clear MU. try clear WM. try clear MI. try clear ST. try clear FR. try clear HB. clear m1.
  pose proof LI2 as (HEAP2 & MI & ST & AX & FR & HB & _).
  pose proof (munch_refl [(lo, bv_unsigned sp + -80)] m2) as MU. pose proof (wmono_refl ctasegs m2) as WM.
  unfold lframe in FR.
  (* [comment removed for export] *)
  zstep. if_cases KZ; zify_cond KZ.
  - assert (N0 : sk_num k = 0) by (revert KZ; rewrite ?signed_small, ?unsigned_lit by (clear - NUMR; lia); clear - NUMR; lia). clear KZ.
    assert (E0 : sk_items k = []) by (unfold sk_num in N0; destruct (sk_items k); [reflexivity| exfalso; revert N0; unfold zlength; cbn; clear; lia]).
    assert (TREE : sct_list_print k st = ARet (tt, st)) by (unfold sct_list_print; rewrite E0; reflexivity).
    apply evt_done. rewrite TREE. apply implAp_ret_evt.
    eapply lp_finishA; [exact LI2| clear; lia].
  - assert (NP : 0 < sk_num k) by (first [exact KZ0| revert KZ; rewrite ?signed_small, ?unsigned_lit by (clear - NUMR; lia); clear - NUMR; lia]). try clear KZ. try clear KZ0 KZ1.
    assert (exists xi ti, sk_items k = xi :: ti) as (xi & ti & EI).
    { unfold sk_num in NP. destruct (sk_items k) as [|xi ti]; [exfalso; revert NP; unfold zlength; cbn; clear; lia| exists xi, ti; reflexivity]. }
    assert (TREE : sct_list_print k st = scts_print (xi :: ti) st) by (unfold sct_list_print; rewrite EI; reflexivity).
    zstep. zstep. zstep. zstep.
    apply evt_done. rewrite TREE.
    eapply (lp_loopA ti xi [] 0);
      [rewrite EI; reflexivity| reflexivity| exact LI2| rewrite <- EI; clear - CW CRED22; lia].
Qed.
End Act.

(* [comment removed for export] *)
Theorem SCT_LIST_print_walkA : SCT_LIST_print_specA SCT_LIST_PRINT_STACK_A SCT_LIST_PRINT_COST_A SCT_LIST_PRINT_FRAMES_A.
Proof.
  intros until W. intros PRE TP UW CTX NE A0 A1 A2 A3 A4 SK ADR HBIN NIDS HB NW KOW KID KNB WI1 WI2.
  eapply lp_mainA; first [exact PRE| exact UW| exact CTX| exact SK| exact HBIN| exact NIDS| exact KOW| exact KID| exact KNB| exact WI1| exact WI2
                         | exact TP| exact A0| exact A1| exact A2| exact A3| exact A4| exact HB| exact NW].
Qed.

End WithRT.
