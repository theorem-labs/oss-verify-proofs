(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
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
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import ApBase ApState ApLogic ApInv ApErr ApBridge.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit D_defs D_cs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import R_unwind_chain.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import LibKitA ARun BnHeapA BnRepDefs BnRepA ImplA BnIfaceA W_cryptoA UnwindA EdgesA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApRepDefs ApRep ApIface ApFrame ApErrKitA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation FR := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).
Implicit Types st : ap_st bptr.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma blk_boundsA : forall Σ OW LB m p A n, AHEAP Σ OW LB m -> In (p, A, n) (OW ++ LB) ->
  0 < A /\ 0 < n /\ A + n <= ACEIL /\ (A + n <= 0x10000 \/ SEGTOP_A <= A) /\ ACEIL + STACK_WIN <= USTACK_TOP.
Proof.
  intros Σ OW LB m p A n H HIN. pose proof (AH_range_gen _ _ _ _ _ H HIN) as (R1 & R2 & R3 & R4 & R5). cbn [blk_addr blk_size fst snd] in *.
  pose proof (AH_pos_gen _ _ _ _ _ H HIN) as P. cbn [blk_size snd] in P. pose proof (AH_ceil _ _ _ _ H) as (_ & _ & C3).
  repeat split; try assumption; lia.
Qed.

Lemma blk_disjointA : forall Σ OW LB m p A n q A' n', AHEAP Σ OW LB m -> In (p, A, n) (OW ++ LB) -> In (q, A', n') (OW ++ LB) -> p <> q ->
  A + n <= A' \/ A' + n' <= A.
Proof.
  intros Σ OW LB m p A n q A' n' H H1 H2 NE. pose proof (AH_disjoint_gen _ _ _ _ _ _ H H1 H2 NE) as D.
  unfold blk_apart in D. cbn [blk_addr blk_size fst snd] in D. lia.
Qed.

(* [comment removed for export] *)
Lemma blk_not_static : forall Σ OW LB m b a, AHEAP Σ OW LB m -> In b (OW ++ LB) -> blk_addr b <= a < blk_addr b + blk_size b -> ~ client_static a.
Proof.
  intros Σ OW LB m b a H HIN Hr [(l & h & Hin & Hlh) _]. pose proof (AH_range_gen _ _ _ _ _ H HIN) as (_ & _ & _ & _ & R5).
  unfold CLIENT_STATIC in Hin. unfold SEGTOP_A in R5. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; lia.
Qed.

(* [comment removed for export] *)
Lemma libw_s_range : forall a, rin_ivs LIBW_S a -> 0x5aebe0 <= a < SEGTOP_A /\ ~ (ERRNO_A <= a < ERRNO_A + 4).
Proof. intros a Ha. unfold LIBW_S in Ha. cbn [rin_ivs fst snd] in Ha. unfold SEGTOP_A, ERRNO_A, TP_A. lia. Qed.

(* [comment removed for export] *)
Lemma lib_addr_whereA : forall Σ OW LB m a, AHEAP Σ OW LB m -> lib_addr OW a ->
  (0x5aebe0 <= a < SEGTOP_A /\ client_static a /\ ~ (ERRNO_A <= a < ERRNO_A + 4))
  \/ (exists b, In b OW /\ blk_addr b <= a < blk_addr b + blk_size b /\ a < ACEIL /\ ~ client_static a).
Proof.
  intros Σ OW LB m a H [Ha|(b & Hb & Hr)].
  - left. pose proof (libw_s_range a Ha) as [R1 R2]. split; [exact R1|]. split; [exact (ar_LIBW_cs a (LIBW_S_A a Ha)) | exact R2].
  - right. exists b. assert (HIN : In b (OW ++ LB)) by (apply in_or_app; left; exact Hb).
    pose proof (AH_range_gen _ _ _ _ _ H HIN) as (_ & _ & _ & R4 & _).
    split; [exact Hb|]. split; [exact Hr|]. split; [lia | exact (blk_not_static _ _ _ _ b a H HIN Hr)].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ap_restA (m : mem) (OW : list block) (E : ap_env) (bo : Z * Z) (cnf : option (bptr * bptr * bptr)) : Prop :=
  ap_env_ok E OW /\ ap_statics_fixed m E /\ ap_statics_cnf m OW (e_stage E) cnf /\ tl_chain m E /\ exlock_free m E
  /\ bio_out_rep m E (fst bo) (snd bo).

Lemma ap_state_splitA : forall st m OW E bo, ap_state st m OW E bo <-> ap_restA m OW E bo (as_cnf st) /\ err_rep m E OW st.
Proof. intros. unfold ap_state, ap_restA. destruct bo. cbn [fst snd]. tauto. Qed.

Lemma ap_state_joinA : forall st m OW E bo,
  ap_restA m OW E bo (as_cnf st) -> es_shape st -> es_raw m (e_es E) (g_of st (badr OW)) ->
  Forall (optb_ok OW) (as_file st) -> Forall (optb_ok OW) (as_func st) -> Forall (optb_ok OW) (as_data st) ->
  ap_state st m OW E bo.
Proof. intros st m OW E bo HR SH ES F1 F2 F3. apply ap_state_splitA. split; [exact HR|]. split; [exact SH|]. split; [apply es_at_raw; exact ES|]. auto. Qed.

Lemma ap_state_esA : forall st m OW E bo, ap_state st m OW E bo ->
  es_raw m (e_es E) (g_of st (badr OW)) /\ g_len (g_of st (badr OW)) /\ es_shape st
  /\ In (p_es E, e_es E, ES_SIZE) OW /\ 0 < e_es E /\ e_es E + ES_SIZE < 2^63 /\ e_es E mod 16 = 0
  /\ Forall (optb_ok OW) (as_file st) /\ Forall (optb_ok OW) (as_func st) /\ Forall (optb_ok OW) (as_data st).
Proof.
  intros st m OW E bo (HE & _ & _ & _ & _ & _ & (SH & EAT & F1 & F2 & F3)).
  pose proof HE as (HF & ND & HP). destruct (env_in E OW HE) as (IES & _).
  unfold CtRepP.ApRepDefs.env_blocks in HP. apply Forall_cons_iff in HP as [PES _]. cbn [blk_addr blk_size fst snd] in PES.
  split; [apply es_at_raw; exact EAT|]. split; [apply g_len_of; exact SH|]. split; [exact SH|]. split; [exact IES|].
  destruct PES as (P1 & P2 & P3). repeat split; assumption.
Qed.

Lemma rest_blocks_OWA : forall m OW E bo cnf b, ap_restA m OW E bo cnf -> In b (rest_blocks OW E cnf) -> In b OW.
Proof.
  intros m OW E bo cnf b (HE & _ & HC & _) Hb. destruct (env_in E OW HE) as (IES & IMK & ISA & IND & IXL).
  unfold CtRepP.ApErrKit.rest_blocks in Hb. apply in_app_iff in Hb. destruct Hb as [Hb|Hb].
  - cbn [In] in Hb. destruct Hb as [<-|[<-|[<-|[<-|[]]]]]; assumption.
  - destruct cnf as [[[lk lh] bk]|]; cbn [CtRepP.ApErrKit.cnf_rblocks In] in Hb; [|destruct Hb].
    cbn [ap_statics_cnf] in HC. destruct HC as (_ & _ & _ & _ & _ & _ & _ & _ & I1 & I2 & I3 & _).   (* [comment removed for export] *)
    destruct Hb as [<-|[<-|[<-|[]]]]; assumption.
Qed.

Local Ltac static_iv lo hi :=
  intros a Ha; apply (lib_addr_static _ a lo hi); [unfold LIBW_S; cbn; tauto|];
  cbn [cells_size csize cells_size Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Ha;
  unfold TL_MASTER_ONCE, TL_MASTER_INIT, TL_MASTER_KEY, AP_DC_INITED, AP_DC_KEY, AP_DC_ONCE1, AP_DC_ONCE1_RET, AP_DC_ONCE2, AP_DC_ONCE2_RET,
    AP_DC_EXLOCK, AP_DC_EXMETH_BIO, AP_DC_CONF_DIAG, AP_DC_INT, OI_STOPPED, OI_BASE_ONCE, OI_BASE_RET, OI_OPTSDONE, AP_IN_INIT_KEY, AP_OPTSDONE_LOCK,
    AP_TSD_DC_SLOT, TSD_MK_SLOT, AP_TSD_USED, AP_TSD_INIT_SLOT, TSD_MAIN, K_MASTER_KEY, V_DC_KEY, V_IN_INIT_KEY, CR_REALLOC_IMPL,
    AP_CONFIG_ONCE, AP_CONFIG_INITED, AP_OBJ_ONCE, AP_OBJ_INITED, AP_OBJ_LOCK, AP_OBJ_ADDED, AP_CONF_METH, AP_CANCELBUF, OI_BASE_INITED, OI_DO_CLEANUP,
    D_libiface.OSSL_BASE_INITED, D_libiface.OSSL_DO_GLOBAL_CLEANUP, AP_OPENSSL_CONFIGURED in Ha; lia.
Local Ltac block_iv HIn :=
  intros a Ha; eapply lib_addr_block; [exact HIn|];
  cbn [cells_size csize Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ length repeat c8s c4s zeros4 map mutex_free_cells sa_cells bio_null_cells bio_cells lhash_cells] in Ha;
  unfold BIO_SIZE, ES_SIZE, MUTEX_SIZE, CtRepP.ApRepDefs.SZ_OBJ_LOCK, CtRepP.ApRepDefs.SZ_ADDED, CtRepP.ApRepDefs.SZ_ADDED_BUCKETS, OFF_MK_SA in *; lia.

(* [comment removed for export] *)
Theorem rest_agreeA : forall m m' OW E bo cnf,
  ap_restA m OW E bo cnf -> agree_on (lib_addr (rest_blocks OW E cnf)) m m' -> ap_restA m' OW E bo cnf.
Proof.
  intros m m' OW E bo cnf (HE & HS & HC & HT & HX & HB) AG.
  assert (RB : forall b, In b [(p_mk E, e_mk E, 72); (p_sa E, e_sa E, 32); (p_nd E, e_nd E, 128); (p_xl E, e_xl E, MUTEX_SIZE)] ->
               In b (rest_blocks OW E cnf)) by (intros b Hb; unfold CtRepP.ApErrKit.rest_blocks; apply in_app_iff; left; exact Hb).
  split; [exact HE|]. split; [eapply (ap_statics_fixed_agree (rest_blocks OW E cnf)); [exact HS|exact AG]|].
  split.
  { destruct cnf as [[[lk lh] bk]|]; cbn [ap_statics_cnf] in *.
    - destruct HC as (S1 & S1b & S2 & S3 & S3b & S4 & S4b & S6 & I1 & I2 & I3 & M1 & M2 & M3).
      assert (J1 : In (lk, badr OW lk, SZ_OBJ_LOCK) (rest_blocks OW E (Some (lk, lh, bk)))) by (unfold CtRepP.ApErrKit.rest_blocks; apply in_app_iff; right; cbn; tauto).
      assert (J2 : In (lh, badr OW lh, SZ_ADDED) (rest_blocks OW E (Some (lk, lh, bk)))) by (unfold CtRepP.ApErrKit.rest_blocks; apply in_app_iff; right; cbn; tauto).
      assert (J3 : In (bk, badr OW bk, SZ_ADDED_BUCKETS) (rest_blocks OW E (Some (lk, lh, bk)))) by (unfold CtRepP.ApErrKit.rest_blocks; apply in_app_iff; right; cbn; tauto).
      split; [eapply rw_cells_agree; [exact AG|exact S1|]; static_iv 0xba46c0 0xba8ae0|].
      split; [eapply rw_cells_agree; [exact AG|exact S1b|]; static_iv 0xba46c0 0xba8ae0|].
      split; [eapply rw_cells_agree; [exact AG|exact S2|]; static_iv 0xba46c0 0xba8ae0|].
      split; [eapply rw_cells_agree; [exact AG|exact S3|]; static_iv 0xba46c0 0xba8ae0|].
      split; [eapply rw_cells_agree; [exact AG|exact S3b|]; static_iv 0xba46c0 0xba8ae0|].
      split; [eapply rw_cells_agree; [exact AG|exact S4|]; static_iv 0xba46c0 0xba8ae0|].
      split; [eapply rw_cells_agree; [exact AG|exact S4b|]; static_iv 0xba46c0 0xba8ae0|].
      split; [eapply rw_cells_agree; [exact AG|exact S6|]; static_iv 0xbca7a0 0xbcab98|].
      split; [exact I1|]. split; [exact I2|]. split; [exact I3|].
      split; [eapply rw_cells_agree; [exact AG|exact M1|]; block_iv J1|].
      split; [eapply rw_cells_agree; [exact AG|exact M2|]; block_iv J2|].
      eapply rw_cells_agree; [exact AG|exact M3|]; block_iv J3.
    - destruct HC as (S1 & S1b & S2 & S3 & S3b & S4 & S4b & S6).
      split; [eapply rw_cells_agree; [exact AG|exact S1|]; static_iv 0xba46c0 0xba8ae0|].
      split; [eapply rw_cells_agree; [exact AG|exact S1b|]; static_iv 0xba46c0 0xba8ae0|].
      split; [eapply rw_cells_agree; [exact AG|exact S2|]; static_iv 0xba46c0 0xba8ae0|].
      split; [eapply rw_cells_agree; [exact AG|exact S3|]; static_iv 0xba46c0 0xba8ae0|].
      split; [eapply rw_cells_agree; [exact AG|exact S3b|]; static_iv 0xba46c0 0xba8ae0|].
      split; [eapply rw_cells_agree; [exact AG|exact S4|]; static_iv 0xba46c0 0xba8ae0|].
      split; [eapply rw_cells_agree; [exact AG|exact S4b|]; static_iv 0xba46c0 0xba8ae0|].
      eapply rw_cells_agree; [exact AG|exact S6|]; static_iv 0xbca7a0 0xbcab98. }
  assert (IMK : In (p_mk E, e_mk E, 72) (rest_blocks OW E cnf)) by (apply RB; cbn; tauto).
  assert (ISA : In (p_sa E, e_sa E, 32) (rest_blocks OW E cnf)) by (apply RB; cbn; tauto).
  assert (IND : In (p_nd E, e_nd E, 128) (rest_blocks OW E cnf)) by (apply RB; cbn; tauto).
  assert (IXL : In (p_xl E, e_xl E, MUTEX_SIZE) (rest_blocks OW E cnf)) by (apply RB; cbn; tauto).
  split.
  { destruct HT as (T1 & (pad & T2) & T3).
    split; [eapply ro_cells_agree; [exact AG|exact T1|]; block_iv IMK|].
    split; [exists pad; eapply ro_cells_agree; [exact AG|exact T2|]; block_iv ISA|].
    eapply ro_cells_agree; [exact AG|exact T3|]; block_iv IND. }
  split; [eapply rw_cells_agree; [exact AG|exact HX|]; block_iv IXL|].
  exact I.   (* [comment removed for export] *)
Qed.

(* [comment removed for export] *)
Lemma restA_of_lib_agree : forall m m' OW E bo cnf,
  ap_restA m OW E bo cnf -> agree_on (lib_addr OW) m m' -> ap_restA m' OW E bo cnf.
Proof.
  intros m m' OW E bo cnf HR AG. eapply rest_agreeA; [exact HR|]. eapply agree_on_mono; [exact AG|].
  intros a [Ha|(b & Hb & Hr)]; [left; exact Ha|right]. exists b. split; [| exact Hr]. eapply rest_blocks_OWA; [exact HR | exact Hb].
Qed.

Lemma es_not_restA : forall st m OW E bo, ap_state st m OW E bo -> ids_ok E st -> ~ In (p_es E) (map blk_id (rest_blocks OW E (as_cnf st))).
Proof.
  intros st m OW E bo AS IDS H. rewrite rest_ids in H. apply in_app_iff in H.
  pose proof (env_ids_nodup _ _ _ _ _ AS) as ND. rewrite env_ids_unfold in ND.
  destruct H as [H|H].
  - cbn [In] in H.
    repeat match goal with H : List.NoDup (_ :: _) |- _ => apply NoDup_cons_iff in H; destruct H as [? H] end.
    cbn [In] in *. intuition congruence.
  - apply cnf_ids_in_es_ids in H. destruct IDS as (IDS & _ & _).
    exact (NoDup_app_disjoint _ _ _ IDS H ltac:(rewrite env_ids_unfold; cbn; tauto)).
Qed.

Lemma rest_OW_removeA : forall m OW E bo cnf q,
  ap_restA m OW E bo cnf -> ~ In q (map blk_id (rest_blocks OW E cnf)) -> q <> p_es E -> ap_restA m (lb_remove q OW) E bo cnf.
Proof.
  intros m OW E bo cnf q (HE & HS & HC & HT & HX & HB) Hq Hqe. rewrite rest_ids in Hq. rewrite in_app_iff in Hq. cbn [In] in Hq.
  split.
  { destruct HE as (HF & ND & HP). split; [|split; [apply NoDup_lb_remove; exact ND|exact HP]].
    unfold CtRepP.ApRepDefs.env_blocks in *. repeat match goal with H : Forall _ (_ :: _) |- _ => apply Forall_cons_iff in H; destruct H as [? H] end.
    repeat (apply Forall_cons; [apply lb_remove_In; split; [assumption|cbn; intros EQ; first [exact (Hqe (eq_sym EQ)) | apply Hq; left; tauto]]|]). apply Forall_nil. }
  split; [exact HS|]. split; [|split; [exact HT|split; [exact HX|exact HB]]].
  destruct cnf as [[[lk lh] bk]|]; cbn [ap_statics_cnf ApInv.cnf_blocks map fst] in *; [|exact HC].
  destruct HC as (S1 & S1b & S2 & S3 & S3b & S4 & S4b & S6 & I1 & I2 & I3 & M1 & M2 & M3).
  assert (N1 : lk <> q) by (intros EQ; apply Hq; right; rewrite EQ; cbn; tauto). assert (N2 : lh <> q) by (intros EQ; apply Hq; right; rewrite EQ; cbn; tauto).
  assert (N3 : bk <> q) by (intros EQ; apply Hq; right; rewrite EQ; cbn; tauto).
  rewrite !(badr_remove_other OW lk q N1), !(badr_remove_other OW lh q N2), !(badr_remove_other OW bk q N3).
  repeat (split; [assumption|]). split; [apply lb_remove_In; split; [exact I1|cbn; exact N1]|].
  split; [apply lb_remove_In; split; [exact I2|cbn; exact N2]|]. split; [apply lb_remove_In; split; [exact I3|cbn; exact N3]|].
  split; [exact M1|]. split; [exact M2|exact M3].
Qed.

Lemma rest_OW_consA : forall m OW E bo cnf q A0 n0,
  ap_restA m OW E bo cnf -> ~ In q (map blk_id OW) -> 0 < A0 -> A0 + n0 < 2^63 -> A0 mod 16 = 0 -> ap_restA m ((q, A0, n0) :: OW) E bo cnf.
Proof.
  intros m OW E bo cnf q A0 n0 (HE & HS & HC & HT & HX & HB) Hq HA Hn H16.
  assert (NEQ : forall p A n, In (p, A, n) OW -> bptr_eqb q p = false).
  { intros p A n H. apply bptr_eqb_neq. intros ->. apply Hq. change p with (blk_id (p, A, n)). apply in_map. exact H. }
  split.
  { destruct HE as (HF & ND & HP). split; [|split; [cbn [map blk_id fst snd]; constructor; [exact Hq|exact ND]|exact HP]].
    eapply Forall_impl; [|exact HF]. intros b Hb. right. exact Hb. }
  split; [exact HS|]. split; [|split; [exact HT|split; [exact HX|exact HB]]].
  destruct cnf as [[[lk lh] bk]|]; cbn [ap_statics_cnf] in *; [|exact HC].
  destruct HC as (S1 & S1b & S2 & S3 & S3b & S4 & S4b & S6 & I1 & I2 & I3 & M1 & M2 & M3).
  rewrite !badr_cons, (NEQ _ _ _ I1), (NEQ _ _ _ I2), (NEQ _ _ _ I3).
  repeat (split; [assumption|]). split; [right; exact I1|]. split; [right; exact I2|]. split; [right; exact I3|].
  split; [exact M1|]. split; [exact M2|exact M3].
Qed.

Lemma rest_lremoveA : forall m OW E bo cnf od,
  ap_restA m OW E bo cnf -> (forall q n, od = Some (q, n) -> ~ In q (map blk_id (rest_blocks OW E cnf)) /\ q <> p_es E) ->
  ap_restA m (lremove od OW) E bo cnf.
Proof. intros m OW E bo cnf [[q n]|] HR H; cbn; [|exact HR]. destruct (H q n eq_refl) as [H1 H2]. apply rest_OW_removeA; assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition segW (L : list block) (lo SP : Z) (P : bptr -> Prop) (iv : Z * Z) : Prop :=
  (lo <= fst iv /\ snd iv <= SP) \/ iv = (ERRNO_A, ERRNO_A + 4) \/ (exists p A n, In (p, A, n) L /\ P p /\ A <= fst iv /\ snd iv <= A + n).

Lemma segW_mono : forall L lo SP (P P' : bptr -> Prop) W, (forall p, P p -> P' p) -> Forall (segW L lo SP P) W -> Forall (segW L lo SP P') W.
Proof.
  intros L lo SP P P' W HP HW. eapply Forall_impl; [| exact HW]. intros iv [H|[H|(p & A & n & H1 & H2 & H3)]]; [left; exact H | right; left; exact H | right; right].
  exists p, A, n. auto.
Qed.

(* [comment removed for export] *)
Lemma seg_closeA : forall Σ OW LB W mb mc lo SP (P : bptr -> Prop),
  AHEAP Σ OW LB mb -> ACEIL <= lo -> lo <= SP -> SP <= USTACK_TOP -> munch W mb mc -> wmono ctasegs mb mc ->
  Forall (segW (OW ++ LB) lo SP P) W -> (forall p A n, In (p, A, n) (OW ++ LB) -> P p -> In (p, A, n) OW) ->
  AHEAP Σ OW LB mc /\ ax_pres LB SP LIBW_A mb mc.
Proof.
  intros Σ OW LB W mb mc lo SP P HEAP CEIL LOSP TOP MU WM HW HP. split.
  - eapply AH_frame; [exact HEAP | exact MU | exact WM |]. eapply Forall_impl; [| exact HW].
    intros [x y] [[H1 H2]|[->|(p & A & n & HIn & Hp & HA & Hy)]]; cbn [fst snd] in *.
    + left. cbn [fst snd]. lia.
    + right; left. cbn [fst snd]. intros a Ha. apply errno_static. unfold ERRNO_A, TP_A in Ha. lia.
    + right; right. exists (p, A, n). split; [exact HIn | cbn; lia].
  - unfold ax_pres. eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU)|]. intros a [NA Ha].
    apply seg_outside. eapply Forall_impl; [| exact HW]. intros [x y] [[H1 H2]|[->|(p & A & n & HIn & Hp & HA & Hy)]]; cbn [fst snd] in *.
    + destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [lia | |].
      * pose proof (lib_addr_whereA Σ OW LB mb a HEAP) as X. destruct Ha as [(l & h & Hin & Hlh) _].
        pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & _). unfold CLIENT_STATIC in Hin. unfold SEGTOP_A in C1. cbn [In] in Hin.
        clear - Hin Hlh C1 CEIL H1. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; lia.
      * pose proof (blk_boundsA Σ OW LB mb (blk_id b) (blk_addr b) (blk_size b) HEAP ltac:(apply in_or_app; right; destruct b as [[? ?] ?]; exact Hb)) as (_ & _ & B3 & _). lia.
    + intros Hin. apply NA. unfold LIBW_A, ERRNO_A, TP_A in *. cbn [rin_ivs fst snd]. lia.
    + intros Hin. destruct Ha as [Ha|[Ha|(b & Hb & Hr)]].
      * pose proof (blk_boundsA Σ OW LB mb p A n HEAP HIn) as (_ & _ & B3 & _). clear - B3 CEIL LOSP Ha Hin HA Hy. lia.
      * exact (blk_not_static Σ OW LB mb (p, A, n) a HEAP HIn ltac:(cbn; lia) Ha).
      * assert (NE : p <> blk_id b).
        { intros ->. pose proof (AH_nodup _ _ _ _ HEAP) as ND. rewrite map_app in ND.
          apply (nodup_app_disj _ _ (blk_id b) ND); [| apply in_map; exact Hb].
          change (blk_id b) with (blk_id (blk_id b, A, n)). apply in_map. exact (HP _ _ _ HIn Hp). }
        pose proof (blk_disjointA Σ OW LB mb p A n (blk_id b) (blk_addr b) (blk_size b) HEAP HIn
                      ltac:(apply in_or_app; right; destruct b as [[? ?] ?]; exact Hb) NE). lia.
Qed.

(* [comment removed for export] *)
Lemma rest_addr_casesA : forall OW E cnf a,
  lib_addr (rest_blocks OW E cnf) a ->
  (0x5aebe0 <= a < SEGTOP_A /\ client_static a /\ ~ (ERRNO_A <= a < ERRNO_A + 4)) \/ (exists b, In b (rest_blocks OW E cnf) /\ blk_addr b <= a < blk_addr b + blk_size b).
Proof.
  intros OW E cnf a [H|(b & Hb & Hr)]; [left | right; exists b; auto].
  pose proof (libw_s_range a H) as [R1 R2]. split; [exact R1|]. split; [exact (ar_LIBW_cs a (LIBW_S_A a H)) | exact R2].
Qed.

Lemma rest_of_segA : forall Σ OWc LB W mb mc OW E bo cnf lo SP,
  ap_restA mb OW E bo cnf -> AHEAP Σ OWc LB mb -> (forall b, In b (rest_blocks OW E cnf) -> In b (OWc ++ LB)) -> ACEIL <= lo ->
  munch W mb mc ->
  Forall (segW (OWc ++ LB) lo SP (fun p => ~ In p (map blk_id (rest_blocks OW E cnf)))) W ->
  ap_restA mc OW E bo cnf.
Proof.
  intros Σ OWc LB W mb mc OW E bo cnf lo SP HR HEAP HL CEIL MU HW.
  eapply rest_agreeA; [exact HR|]. eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU)|]. intros a Ha. apply seg_outside.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & _).
  eapply Forall_impl; [|exact HW]. intros [x y] [[H1 H2]|[->|(p & A & n & HIn & Hni & HA & Hy)]]; cbn [fst snd] in *.
  - destruct (rest_addr_casesA _ _ _ _ Ha) as [(Hs & _)|([[p A] n] & Hb & Hr)]; [lia|].
    cbn [blk_addr blk_size fst snd] in Hr. pose proof (blk_boundsA Σ OWc LB mb p A n HEAP (HL _ Hb)) as (_ & _ & B3 & _). lia.
  - destruct (rest_addr_casesA _ _ _ _ Ha) as [(_ & _ & NE)|([[p A] n] & Hb & Hr)]; [exact NE|].
    cbn [blk_addr blk_size fst snd] in Hr. pose proof (blk_boundsA Σ OWc LB mb p A n HEAP (HL _ Hb)) as (_ & _ & _ & B4 & _). unfold ERRNO_A, TP_A, SEGTOP_A in *. lia.
  - intros Hin. destruct (rest_addr_casesA _ _ _ _ Ha) as [(_ & Hs & _)|([[p' A'] n'] & Hb & Hr)].
    + exact (blk_not_static Σ OWc LB mb (p, A, n) a HEAP HIn ltac:(cbn; lia) Hs).
    + cbn [blk_addr blk_size fst snd] in Hr.
      assert (Hp : p <> p') by (intros ->; apply Hni; change p' with (blk_id (p', A', n')); apply in_map; exact Hb).
      pose proof (blk_disjointA Σ OWc LB mb p A n p' A' n' HEAP HIn (HL _ Hb) Hp). lia.
Qed.

Lemma data_cells_of_munchA : forall Σ OWc LB W mb mc OW st lo SP,
  data_cells mb OW st -> (forall i q k, get_data i st = Some (q, k) -> In (q, badr OW q, k) (OWc ++ LB)) -> AHEAP Σ OWc LB mb ->
  ACEIL <= lo -> munch W mb mc ->
  Forall (segW (OWc ++ LB) lo SP (fun p => forall i q k, get_data i st = Some (q, k) -> q <> p)) W ->
  data_cells mc OW st.
Proof.
  intros Σ OWc LB W mb mc OW st lo SP [DC DF] HD HEAP CEIL MU HW. split; [|exact DF]. intros i q k Hd.
  destruct (DC i q k Hd) as [Hk [junk HC]]. split; [exact Hk|]. exists junk.
  pose proof (HD i q k Hd) as HIn'. pose proof (blk_boundsA Σ OWc LB mb q (badr OW q) k HEAP HIn') as (B1 & B2 & B3 & B4 & B5).
  eapply rw_cells_agree; [apply (agree_on_of_munch_nw _ _ _ MU) | exact HC |]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. rewrite Nat.add_0_r, Z2Nat.id in Ha by lia.
  apply seg_outside. eapply Forall_impl; [|exact HW]. intros [x y] [[H1 H2]|[->|(p & A & n & HInp & Hne & HA & Hy)]]; cbn [fst snd] in *.
  - lia.
  - unfold ERRNO_A, TP_A, SEGTOP_A in *. lia.
  - pose proof (blk_disjointA Σ OWc LB mb q (badr OW q) k p A n HEAP HIn' HInp ltac:(intros ->; exact (Hne i p k Hd eq_refl))). lia.
Qed.

Lemma kept_of_munchA : forall Σ OWc LB W mb mc K lo SP,
  AHEAP Σ OWc LB mb -> (forall b, In b K -> In b (OWc ++ LB)) -> ACEIL <= lo -> munch W mb mc ->
  Forall (segW (OWc ++ LB) lo SP (fun p => ~ In p (map blk_id K))) W ->
  kept K mb mc.
Proof.
  intros Σ OWc LB W mb mc K lo SP HEAP HK CEIL MU HW a Ha (b & Hb & Hr). apply MU. unfold wa. rewrite unsigned_lit by lia.
  destruct b as [[q A'] n']. cbn [blk_addr blk_size fst snd] in Hr.
  pose proof (blk_boundsA Σ OWc LB mb q A' n' HEAP (HK _ Hb)) as (B1 & B2 & B3 & B4 & B5).
  apply seg_outside. eapply Forall_impl; [|exact HW]. intros [x y] [[H1 H2]|[H|(p & A & n & HIn & Hni & HA & Hy)]]; cbn [fst snd] in *.
  - lia.
  - injection H as -> ->. unfold ERRNO_A, TP_A, SEGTOP_A in *. lia.
  - assert (Hpq : p <> q) by (intros ->; apply Hni; change q with (blk_id (q, A', n')); apply in_map; exact Hb).
    pose proof (blk_disjointA Σ OWc LB mb p A n q A' n' HEAP HIn (HK _ Hb) Hpq). lia.
Qed.

(* [comment removed for export] *)
Lemma es_raw_of_munchA : forall Σ OWc LB W mb mc E g lo SP (pe : bptr),
  es_raw mb (e_es E) g -> g_len g -> In (pe, e_es E, ES_SIZE) (OWc ++ LB) -> AHEAP Σ OWc LB mb -> ACEIL <= lo ->
  munch W mb mc -> wmono ctasegs mb mc ->
  Forall (segW (OWc ++ LB) lo SP (fun p => p <> pe)) W ->
  es_raw mc (e_es E) g.
Proof.
  intros Σ OWc LB W mb mc E g lo SP pe ES GL HIN HEAP CEIL MU WM HW.
  pose proof (blk_boundsA Σ OWc LB mb pe (e_es E) ES_SIZE HEAP HIN) as (B1 & B2 & B3 & B4 & B5). unfold ES_SIZE in *.
  eapply es_raw_transport; [exact ES | exact GL | exact MU | exact WM |].
  clear ES MU WM. induction HW as [|[x y] W H1 HW IH]; cbn; [exact I|]. split; [| exact IH].
  destruct H1 as [[H1 H2]|[H|(p & A & n & HInp & Hne & HA & Hy)]]; cbn [fst snd] in *.
  - lia.
  - injection H as -> ->. unfold ERRNO_A, TP_A, SEGTOP_A in *. lia.
  - pose proof (blk_disjointA Σ OWc LB mb p A n pe (e_es E) 904 HEAP HInp HIN Hne). lia.
Qed.

(* [comment removed for export] *)
Lemma data_cells_store1A : forall Σ OWc LB mc m' OW st lo SP x y pd D nd junk',
  data_cells mc OW st -> (forall i q k, get_data i st = Some (q, k) -> In (q, badr OW q, k) (OWc ++ LB)) ->
  In (pd, D, nd) (OWc ++ LB) -> 1 <= nd <= ERR_DATA_MAX_A -> AHEAP Σ OWc LB mc -> ACEIL <= lo -> lo <= x -> y <= SP ->
  munch [(x, y); (D, D + 1)] mc m' ->
  rw_cells ctasegs m' D [CB (Z.to_nat nd) junk'] ->
  data_cells m' OW st.
Proof.
  intros Σ OWc LB mc m' OW st lo SP x y pd D nd junk' [DC DF] HD HIn Hnd HEAP CEIL Hx Hy MU HC'. split; [|exact DF]. intros i q k Hd.
  destruct (DC i q k Hd) as [Hk [junk HC]]. split; [exact Hk|]. pose proof (HD i q k Hd) as HInq.
  pose proof (AH_nodup _ _ _ _ HEAP) as ND.
  destruct (bptr_eqb q pd) eqn:E.
  - apply bptr_eqb_eq in E. subst q. destruct (badr_size_unique (OWc ++ LB) pd (badr OW pd) k D nd ND HInq HIn) as [-> ->]. exists junk'. exact HC'.
  - assert (NE : q <> pd) by (intros ->; rewrite bptr_eqb_refl in E; discriminate).
    exists junk. pose proof (blk_boundsA Σ OWc LB mc q (badr OW q) k HEAP HInq) as (B1 & B2 & B3 & B4 & B5).
    pose proof (blk_disjointA Σ OWc LB mc q (badr OW q) k pd D nd HEAP HInq HIn NE) as DJ.
    eapply rw_cells_agree; [apply (agree_on_of_munch_nw _ _ _ MU) | exact HC |]. intros a Ha. cbn [cells_size csize Nat.add] in Ha.
    rewrite Nat.add_0_r, Z2Nat.id in Ha by lia. cbn [outside]. split; [lia|]. split; [lia|exact I].
Qed.

(* [comment removed for export] *)
Lemma data_cells_OWA : forall m OW OW' st,
  data_cells m OW st -> (forall i q k, get_data i st = Some (q, k) -> badr OW' q = badr OW q) -> data_cells m OW' st.
Proof. intros m OW OW' st [DC DF] HB. split; [|exact DF]. intros i q k Hd. rewrite (HB i q k Hd). exact (DC i q k Hd). Qed.

Lemma data_cells_subA : forall m OW st st',
  data_cells m OW st -> (forall i q k, get_data i st' = Some (q, k) -> exists j, get_data j st = Some (q, k)) -> dflags_ok st' -> data_cells m OW st'.
Proof. intros m OW st st' [DC DF] HS DF'. split; [|exact DF']. intros i q k Hd. destruct (HS i q k Hd) as [j Hj]. exact (DC j q k Hj). Qed.

Lemma data_cells_dflagsA : forall m OW st, data_cells m OW st -> dflags_ok st.
Proof. intros m OW st [_ DF]. exact DF. Qed.

(* [comment removed for export] *)
Lemma kept_of_lib_agree : forall (K OW : list block) m m',
  (forall b, In b K -> In b OW) -> agree_on (lib_addr OW) m m' -> kept K m m'.
Proof.
  intros K OW m m' HK AG a Ha Hin. apply (AG a Ha). destruct Hin as (b & Hb & Hr). right. exists b. split; [exact (HK b Hb) | exact Hr].
Qed.

(* [comment removed for export] *)
Lemma ap_state_of_munchA : forall Σ st m m' OW LB E bo W lo SP,
  ap_state st m OW E bo -> AHEAP Σ OW LB m -> ACEIL <= lo -> munch W m m' ->
  Forall (segW (OW ++ LB) lo SP (fun _ => False)) W ->
  ap_state st m' OW E bo.
Proof.
  intros Σ st m m' OW LB E bo W lo SP AS HEAP CEIL MU HW. eapply ap_state_agree; [exact AS|].
  eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU)|]. intros a Ha. apply seg_outside.
  pose proof (lib_addr_whereA Σ OW LB m a HEAP Ha) as C.
  eapply Forall_impl; [|exact HW]. intros [x y] [[H1 H2]|[H|(p & A & n & _ & [] & _)]]; cbn [fst snd] in *.
  - destruct C as [(C1 & _)|(b & _ & _ & C3 & _)]; [pose proof (AH_ceil _ _ _ _ HEAP) as (X & _); lia | lia].
  - injection H as -> ->. destruct C as [(_ & _ & C2)|(b & Hb & Hr & _ & NS)]; [exact C2|].
    intros Hin. apply NS. apply errno_static. unfold ERRNO_A, TP_A in Hin. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lib_addr_rest_aclient : forall (OW L : list block) E cnf SP a,
  (forall b, In b (rest_blocks OW E cnf) -> In b L) -> lib_addr (rest_blocks OW E cnf) a -> aclient_addr L SP a.
Proof.
  intros OW L E cnf SP a HL [Ha|(b & Hb & Hr)].
  - right; left. exact (ar_LIBW_cs a (LIBW_S_A a Ha)).
  - right; right. exists b. split; [exact (HL b Hb) | exact Hr].
Qed.

Lemma rest_of_aclientA : forall (L : list block) SP m m' OW E bo cnf,
  ap_restA m OW E bo cnf -> agree_on (aclient_addr L SP) m m' -> (forall b, In b (rest_blocks OW E cnf) -> In b L) -> ap_restA m' OW E bo cnf.
Proof.
  intros L SP m m' OW E bo cnf HR AG HL. eapply rest_agreeA; [exact HR|]. eapply agree_on_mono; [exact AG|]. intros a Ha. exact (lib_addr_rest_aclient OW L E cnf SP a HL Ha).
Qed.

Lemma data_cells_aclientA : forall (L : list block) SP m m' OW st,
  data_cells m OW st -> agree_on (aclient_addr L SP) m m' -> (forall i q k, get_data i st = Some (q, k) -> In (q, badr OW q, k) L) -> data_cells m' OW st.
Proof.
  intros L SP m m' OW st [DC DF] AG HL. split; [|exact DF]. intros i q k Hd. destruct (DC i q k Hd) as [Hk [junk HC]]. split; [exact Hk|]. exists junk.
  eapply rw_cells_agree; [exact AG|exact HC|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. rewrite Nat.add_0_r, Z2Nat.id in Ha by lia.
  right. right. exists (q, badr OW q, k). split; [eapply HL; exact Hd|]. cbn. lia.
Qed.

Lemma kept_of_aclientA : forall (K L : list block) SP m m', agree_on (aclient_addr L SP) m m' -> (forall b, In b K -> In b L) -> kept K m m'.
Proof.
  intros K L SP m m' AG HK a Ha (b & Hb & Hr). apply (AG a Ha). right. right. exists b. split; [apply HK; exact Hb|exact Hr].
Qed.

(* [comment removed for export] *)
Definition ofree_postA (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (Σ : rts RT) (OW' LB : list block) (lo : Z) (m : mem) (Σ' : rts RT) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m',
    ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctasegs)
    /\ mem_inv ctasegs m' /\ stk ctasegs m' lo (bv_unsigned sp)
    /\ agree_on (aclient_addr (OW' ++ LB) (bv_unsigned sp)) m m'
    /\ rt_credit RT Σ' = rt_credit RT Σ
    /\ AHEAP Σ' OW' LB m'.

(* [comment removed for export] *)
Lemma CRYPTO_free_opt_walkAp : forall {X : Type}
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (od : option (bptr * Z)) (adr : bptr -> Z) (lo : Z) (ras : list Z)
    (k : aprog bptr X) (Q : X -> rts RT -> machine_state -> Prop),
  AHEAP Σ OW LB m -> match od with Some (q, n) => In (q, adr q, n) OW | None => True end ->
  stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo <= bv_unsigned sp - CRYPTO_FREE_STACK ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A -> crypto_statics m -> a0 = wz (optr adr od) ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx CRYPTO_FREE (bv_unsigned ra :: ras) ->
  (forall Σ' ms', ofree_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ (lremove od OW) LB lo m Σ' ms' -> implAp k Σ' Q ms') ->
  implAp (ofree (option_map fst od) k) Σ Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz CRYPTO_FREE) fc None m (seg_rom ctasegs)).
Proof.
  intros until Q. intros HEAP HIN ST CEIL LO SPT SP16 MI TP CS HA0 UW CTX K.
  destruct od as [[q n]|]; cbn [option_map fst CtRepP.ApErrKit.ofree optr CtRepP.ApErrKit.lremove] in *.
  - eapply CRYPTO_free_walkAp with (A := adr q) (n := n); try eassumption.
    intros Σ' ms' PO. apply K. unfold cfree_postA in PO. unfold ofree_postA.
    destruct PO as (x5 & x6 & x7 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & F' & fc' & m' & -> & MI' & ST' & AG' & CR' & HEAP').
    exists x5, x6, x7, x10, x11, x12, x13, x14, x15, x16, x17, x28, x29, x30, x31, F', fc', m'. split; [reflexivity|].
    split; [exact MI'|]. split; [exact ST'|]. split; [| split; [exact CR' | exact HEAP']].
    rewrite (lb_remove_app_l q OW LB (AH_nodup _ _ _ _ HEAP) ltac:(change q with (blk_id (q, adr q, n)); apply in_map; exact HIN)) in AG'. exact AG'.
  - subst tp. eapply implAp_step_same.
    { eapply (CRYPTO_free_null_cpsA ra sp gp (wz TP_A)); try eassumption; reflexivity. }
    intros ms' PO. apply K. unfold cfree_null_post in PO. unfold ofree_postA.
    destruct PO as (x5 & x6 & x7 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & F' & fc' & m' & -> & MI' & ST' & HEAP' & AG').
    exists x5, x6, x7, x10, x11, x12, x13, x14, x15, x16, x17, x28, x29, x30, x31, F', fc', m'. split; [reflexivity|].
    split; [exact MI'|]. split; [exact ST'|]. split; [exact AG'|]. split; [reflexivity | exact HEAP'].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section SegBaseA.
Variables (m0 : mem) (OW : list block) (st : ap_st bptr) (E : ap_env) (bo : Z * Z) (LB K : list block) (SP lo : Z) (Σ0 : rts RT).

Definition seg_baseA (c : Z) (Σc : rts RT) (OWc : list block) (mb : mem) : Prop :=
  AHEAP Σc OWc LB mb /\ ax_pres LB SP LIBW_A m0 mb
  /\ ap_restA mb OW E bo (as_cnf st) /\ (forall b, In b (rest_blocks OW E (as_cnf st)) -> In b (OWc ++ LB))
  /\ data_cells mb OW st /\ (forall i q k, get_data i st = Some (q, k) -> In (q, badr OW q, k) (OWc ++ LB))
  /\ kept K m0 mb /\ (forall b, In b K -> In b OWc)
  /\ In (p_es E, e_es E, 904) OWc
  /\ rt_credit RT Σ0 - c <= rt_credit RT Σc.
  (* [comment removed for export] *)

(* [comment removed for export] *)
Definition seg_writableA (p : bptr) : Prop :=
  ~ In p (map blk_id (rest_blocks OW E (as_cnf st))) /\ (forall i q k, get_data i st = Some (q, k) -> q <> p) /\ ~ In p (map blk_id K).

Hypothesis CEIL : ACEIL <= lo.
Hypothesis LOSP : lo <= SP.
Hypothesis TOP : SP <= USTACK_TOP.
Hypothesis IDS : ids_ok E st.
Hypothesis AS0 : exists mI, ap_state st mI OW E bo.
Hypothesis KIDS : forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E).

Lemma es_writableA : seg_writableA (p_es E).
Proof.
  clear CEIL LOSP TOP. split; [|split].
  - destruct AS0 as [mI AS]. eapply es_not_restA; [exact AS|exact IDS].
  - intros i q k Hd ->. exact (ids_data_es_ne E st i (p_es E) k IDS Hd eq_refl).
  - eapply K_not_env; [exact KIDS|]. rewrite env_ids_unfold. cbn. tauto.
Qed.

(* [comment removed for export] *)
Lemma seg_baseA_munch : forall c Σc OWc mb mc W,
  seg_baseA c Σc OWc mb -> munch W mb mc -> wmono ctasegs mb mc ->
  Forall (segW (OWc ++ LB) lo SP (fun p => seg_writableA p /\ In p (map blk_id OWc))) W ->
  seg_baseA c Σc OWc mc.
Proof.
  intros c Σc OWc mb mc W (HEAP & AX & HAR & RB & DC & DIN & KP & KOW & IES & CR) MU WM HW.
  assert (INCL : forall b, In b OWc -> In b (OWc ++ LB)) by (intros b Hb; apply in_app_iff; left; exact Hb).
  destruct (seg_closeA Σc OWc LB W mb mc lo SP (fun p => seg_writableA p /\ In p (map blk_id OWc)) HEAP CEIL LOSP TOP MU WM HW) as [HEAP' AX'].
  { intros p A n HIN [_ Hp]. apply in_map_iff in Hp. destruct Hp as ([[p' A'] n'] & Ep & Hb). cbn in Ep. subst p'.
    pose proof (AH_nodup _ _ _ _ HEAP) as ND. destruct (badr_size_unique (OWc ++ LB) p A n A' n' ND HIN (INCL _ Hb)) as [-> ->]. exact Hb. }
  split; [exact HEAP'|]. split; [eapply ax_pres_trans; [exact AX|exact AX']|].
  split; [eapply (rest_of_segA Σc OWc LB W mb mc); [exact HAR|exact HEAP|exact RB|exact CEIL|exact MU|eapply segW_mono; [|exact HW]; intros p [[H _] _]; exact H]|].
  split; [exact RB|].
  split; [eapply (data_cells_of_munchA Σc OWc LB W mb mc); [exact DC|exact DIN|exact HEAP|exact CEIL|exact MU|eapply segW_mono; [|exact HW]; intros p [[_ [H _]] _]; exact H]|].
  split; [exact DIN|].
  split; [eapply kept_trans; [exact KP| eapply (kept_of_munchA Σc OWc LB W mb mc K lo); [exact HEAP|intros b Hb; apply INCL; apply KOW; exact Hb|exact CEIL|exact MU|eapply segW_mono; [|exact HW]; intros p [[_ [_ H]] _]; exact H]]|].
  split; [exact KOW|]. split; [exact IES|exact CR].
Qed.

(* [comment removed for export] *)
Lemma seg_baseA_free : forall c Σc Σ' OWc mb mc od SP',
  seg_baseA c Σc OWc mb ->
  (forall q n, od = Some (q, n) -> In q (map blk_id OWc) /\ seg_writableA q /\ q <> p_es E) ->
  agree_on (aclient_addr (lremove od OWc ++ LB) SP') mb mc -> SP' <= SP -> AHEAP Σ' (lremove od OWc) LB mc -> rt_credit RT Σ' = rt_credit RT Σc ->
  seg_baseA c Σ' (lremove od OWc) mc.
Proof.
  intros c Σc Σ' OWc mb mc od SP' (HEAP & AX & HAR & RB & DC & DIN & KP & KOW & IES & CR) Hod AG' HSP HEAP' CR'.
  pose proof (AH_nodup _ _ _ _ HEAP) as ND.
  assert (QI : forall q n, od = Some (q, n) -> In q (map blk_id OWc)) by (intros q n H; exact (proj1 (Hod q n H))).
  assert (EOW : lremove od (OWc ++ LB) = lremove od OWc ++ LB) by (apply (lremove_app od OWc LB ND QI)).
  assert (RB' : forall b, In b (rest_blocks OW E (as_cnf st)) -> In b (lremove od OWc ++ LB)).
  { rewrite <- EOW. apply rest_blocks_lremove; [exact RB|]. intros q n H. exact (proj1 (proj1 (proj2 (Hod q n H)))). }
  assert (DIN' : forall i q k, get_data i st = Some (q, k) -> In (q, badr OW q, k) (lremove od OWc ++ LB)).
  { intros i q k Hd. rewrite <- EOW. apply lremove_keep; [eapply DIN; exact Hd|].
    intros q' n' H. cbn. exact (proj1 (proj2 (proj1 (proj2 (Hod q' n' H)))) i q k Hd). }
  assert (KOW' : forall b, In b K -> In b (lremove od OWc)).
  { intros b Hb. apply (K_lremove K OWc od KOW); [|exact Hb]. intros q n H. exact (proj2 (proj2 (proj1 (proj2 (Hod q n H))))). }
  split; [exact HEAP'|]. split; [eapply ax_pres_trans; [exact AX| eapply (ax_pres_of_aclient (lremove od OWc) LB); [exact AG'|exact HSP]]|].
  split; [eapply (rest_of_aclientA (lremove od OWc ++ LB)); [exact HAR|exact AG'|exact RB']|]. split; [exact RB'|].
  split; [eapply (data_cells_aclientA (lremove od OWc ++ LB)); [exact DC|exact AG'|exact DIN']|]. split; [exact DIN'|].
  split; [eapply kept_trans; [exact KP|eapply (kept_of_aclientA K (lremove od OWc ++ LB)); [exact AG'|intros b Hb; apply in_app_iff; left; apply KOW'; exact Hb]]|].
  split; [exact KOW'|]. split.
  { apply lremove_keep; [exact IES|]. intros q n H. cbn. apply not_eq_sym. exact (proj2 (proj2 (Hod q n H))). }
  rewrite CR'. exact CR.
Qed.

(* [comment removed for export] *)
Lemma seg_baseA_malloc : forall c Σc Σ' OWc mb mc p A n SP' n',
  seg_baseA c Σc OWc mb ->
  agree_on (aclient_addr (OWc ++ LB) SP') mb mc -> SP' <= SP -> AHEAP Σ' ((p, A, n) :: OWc) LB mc -> rt_credit RT Σc - mcost n' <= rt_credit RT Σ' ->
  seg_baseA (c + mcost n') Σ' ((p, A, n) :: OWc) mc.
Proof.
  intros c Σc Σ' OWc mb mc p A n SP' n' (HEAP & AX & HAR & RB & DC & DIN & KP & KOW & IES & CR) AG' HSP HEAP' CR'.
  split; [exact HEAP'|]. split; [eapply ax_pres_trans; [exact AX| eapply (ax_pres_of_aclient OWc LB); [exact AG'|exact HSP]]|].
  split; [eapply (rest_of_aclientA (OWc ++ LB)); [exact HAR|exact AG'|exact RB]|]. split; [intros b Hb; right; apply RB; exact Hb|].
  split; [eapply (data_cells_aclientA (OWc ++ LB)); [exact DC|exact AG'|exact DIN]|]. split; [intros i q k Hd; right; eapply DIN; exact Hd|].
  split; [eapply kept_trans; [exact KP|eapply (kept_of_aclientA K (OWc ++ LB)); [exact AG'|intros b Hb; apply in_app_iff; left; apply KOW; exact Hb]]|].
  split; [intros b Hb; right; apply KOW; exact Hb|]. split; [right; exact IES|]. clear - CR CR'. lia.
Qed.

(* [comment removed for export] *)
Lemma seg_baseA_crypto_statics : forall c Σc OWc mb, seg_baseA c Σc OWc mb -> crypto_statics mb.
Proof. intros c Σc OWc mb (_ & _ & HAR & _). destruct HAR as (_ & (CS & _) & _). exact CS. Qed.
Lemma seg_baseA_heap : forall c Σc OWc mb, seg_baseA c Σc OWc mb -> AHEAP Σc OWc LB mb.
Proof. intros c Σc OWc mb (H & _). exact H. Qed.
(* [comment removed for export] *)
Lemma seg_baseA_ax : forall c Σc OWc mb, seg_baseA c Σc OWc mb -> ax_pres LB SP LIBW_A m0 mb.
Proof. intros c Σc OWc mb H. exact (proj1 (proj2 H)). Qed.
Lemma seg_baseA_es : forall c Σc OWc mb, seg_baseA c Σc OWc mb -> In (p_es E, e_es E, 904) OWc.
Proof. intros c Σc OWc mb (_ & _ & _ & _ & _ & _ & _ & _ & IES & _). exact IES. Qed.
Lemma seg_baseA_kow : forall c Σc OWc mb, seg_baseA c Σc OWc mb -> forall b, In b K -> In b OWc.
Proof. intros c Σc OWc mb (_ & _ & _ & _ & _ & _ & _ & KOW & _). exact KOW. Qed.
Lemma seg_baseA_credit : forall c Σc OWc mb, seg_baseA c Σc OWc mb -> rt_credit RT Σ0 - c <= rt_credit RT Σc.
Proof. intros c Σc OWc mb (_ & _ & _ & _ & _ & _ & _ & _ & _ & CR). exact CR. Qed.

(* [comment removed for export] *)
Lemma fresh_writableA : forall c Σc OWc mb p,
  seg_baseA c Σc OWc mb -> ~ In p (map blk_id (OWc ++ LB)) -> seg_writableA p.
Proof.
  intros c Σc OWc mb p (HEAP & AX & HAR & RB & DC & DIN & KP & KOW & IES & CR) NI. split; [|split].
  - intros Hin. apply NI. apply in_map_iff in Hin. destruct Hin as (b & <- & Hb). apply in_map. apply RB. exact Hb.
  - intros i q k Hd ->. apply NI. change p with (blk_id (p, badr OW p, k)). apply in_map. eapply DIN. exact Hd.
  - intros Hin. apply NI. apply in_map_iff in Hin. destruct Hin as (b & <- & Hb). apply in_map. apply in_app_iff. left. apply KOW. exact Hb.
Qed.

(* [comment removed for export] *)
Lemma seg_baseA_intro : forall c Σc mb,
  AHEAP Σc OW LB mb -> ax_pres LB SP LIBW_A m0 mb -> ap_state st mb OW E bo -> data_cells mb OW st ->
  kept K m0 mb -> (forall b, In b K -> In b OW) -> rt_credit RT Σ0 - c <= rt_credit RT Σc ->
  seg_baseA c Σc OW mb.
Proof.
  intros c Σc mb HEAP AX AS DC KP KOW CR.
  assert (INCL : forall b, In b OW -> In b (OW ++ LB)) by (intros b Hb; apply in_app_iff; left; exact Hb).
  pose proof (proj1 (proj1 (ap_state_splitA _ _ _ _ _) AS)) as HAR.
  pose proof (ap_state_esA _ _ _ _ _ AS) as (_ & _ & _ & IES & _ & _ & _ & _ & _ & OD). unfold ES_SIZE in IES.
  split; [exact HEAP|]. split; [exact AX|]. split; [exact HAR|].
  split; [intros b Hb; apply INCL; eapply rest_blocks_OWA; [exact HAR|exact Hb]|]. split; [exact DC|].
  split; [intros i q k Hd; apply INCL; exact (proj1 (optb_ok_nth OW _ i q k OD Hd))|].
  split; [exact KP|]. split; [exact KOW|]. split; [exact IES|exact CR].
Qed.

End SegBaseA.

End WithRT.
