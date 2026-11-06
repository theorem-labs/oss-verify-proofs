(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step.
From OSSVerify.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import ApBase ApState ApOwner.
From OSSVerify.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit.
From OSSVerify.Proofs.openssl.ct.lib.CtHXU Require Import HxpFacts HxpInit.
From OSSVerify.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ro_cells_agree : forall P m m' A cs,
  agree_on P m m' -> ro_cells ctusegs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> P a) ->
  ro_cells ctusegs m' A cs.
Proof.
  intros P m m' A cs same [wf_cs bytes_old] cover.
  assert (bytes_new : bytes_at ctusegs m' A (cells_bytes cs)).
  { refine (bytes_at_agree P m m' A _ same bytes_old _).
    rewrite (cells_bytes_length cs wf_cs). exact cover. }
  exact (conj wf_cs bytes_new).
Qed.

Lemma u64arr_agree : forall P m m' A ws,
  agree_on P m m' -> u64arr ctusegs m A ws -> (forall a, A <= a < A + 8 * Z.of_nat (length ws) -> P a) -> u64arr ctusegs m' A ws.
Proof.
  intros P m m' A ws same [bytes_old wr_old] cover.
  pose proof (wr_at_agree P m m' A _ same wr_old cover) as wr_new.
  assert (bytes_new : bytes_at ctusegs m' A (u64s ws)).
  { refine (bytes_at_agree P m m' A _ same bytes_old _).
    intros a in_span. apply cover. rewrite u64s_length in in_span. lia. }
  exact (conj bytes_new wr_new).
Qed.
Lemma u32arr_agree : forall P m m' A ws,
  agree_on P m m' -> u32arr ctusegs m A ws -> (forall a, A <= a < A + 4 * Z.of_nat (length ws) -> P a) -> u32arr ctusegs m' A ws.
Proof.
  intros P m m' A ws same [bytes_old wr_old] cover.
  pose proof (wr_at_agree P m m' A _ same wr_old cover) as wr_new.
  assert (bytes_new : bytes_at ctusegs m' A (u32s ws)).
  { refine (bytes_at_agree P m m' A _ same bytes_old _).
    intros a in_span. apply cover. rewrite u32s_length in in_span. lia. }
  exact (conj bytes_new wr_new).
Qed.

Lemma wl_length l : length (wl l) = length l. Proof. unfold wl. apply length_map. Qed.

(* [comment removed for export] *)
Definition lib_addr (OW : list block) (a : Z) : Prop := rin_ivs LIBW_HX a \/ in_block OW a.

Lemma lib_addr_static : forall OW a lo hi, In (lo, hi) LIBW_HX -> lo <= a < hi -> lib_addr OW a.
Proof.
  intros OW a lo hi Hin Ha. left. unfold LIBW_HX in *. cbn [rin_ivs fst snd].
  repeat (destruct Hin as [E|Hin]; [injection E as <- <-; tauto|]). destruct Hin.
Qed.

Lemma lib_addr_block : forall OW a p A n, In (p, A, n) OW -> A <= a < A + n -> lib_addr OW a.
Proof. intros OW a p A n Hin Ha. right. exists (p, A, n). split; [exact Hin|]. cbn. exact Ha. Qed.

Local Ltac static_iv lo hi :=
  intros a Ha; apply (lib_addr_static _ a lo hi); [unfold LIBW_HX; cbn; tauto|];
  cbn [cells_size csize cells_size Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Ha;
  unfold TL_MASTER_ONCE8, TL_MASTER_KEY8, AP_DC_INITED, AP_DC_KEY, AP_DC_ONCE1, AP_DC_ONCE2, AP_DC_EXLOCK, AP_DC_EXMETH_BIO, AP_DC_CONF_DIAG,
    OI_STOPPED, OI_BASE_ONCE, OI_OPTSDONE, AP_IN_INIT_KEY, AP_OPTSDONE_LOCK, TCB_TSD, AP_TSD_DC_SLOT, TSD_MK_SLOT, AP_TSD_USED, AP_TSD_INIT_SLOT,
    CR_GOT_MALLOC, CR_GOT_FREE, CR_MEMSET_FUNC, CR_MALLOC_IMPL, CR_REALLOC_IMPL, CR_FREE_IMPL, CR_NO_CUSTOMIZE, AP_CONFIG_ONCE, AP_OBJ_ONCE, AP_OBJ_LOCK,
    AP_OBJ_ADDED, AP_CONF_METH, AP_CANCELBUF, OI_BASE_INITED, OI_DO_CLEANUP, AP_OPENSSL_CONFIGURED in Ha; lia.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma crypto_statics_agree : forall OW m m', crypto_statics m -> agree_on (lib_addr OW) m m' -> crypto_statics m'.
Proof.
  intros OW m m' (C1 & C2 & C3 & C4 & C5 & C6) AG. unfold crypto_statics.
  split; [eapply ro_cells_agree; [exact AG|exact C1|]; static_iv 0x31e898 0x31e950|].
  split; [eapply ro_cells_agree; [exact AG|exact C2|]; static_iv 0x31e898 0x31e950|].
  split; [eapply ro_cells_agree; [exact AG|exact C3|]; static_iv 0x31fd90 0x320370|].
  split; [eapply ro_cells_agree; [exact AG|exact C4|]; static_iv 0x31fd90 0x320370|].
  split; [eapply ro_cells_agree; [exact AG|exact C5|]; static_iv 0x31fd90 0x320370|].
  eapply ro_cells_agree; [exact AG|exact C6|]; static_iv 0x3306d0 0x333158.
Qed.

Lemma realloc_statics_agree : forall OW m m', realloc_statics m -> agree_on (lib_addr OW) m m' -> realloc_statics m'.
Proof.
  intros OW m m' (C1 & C2) AG. split;
    [ eapply ro_cells_agree; [exact AG|exact C1|]; static_iv 0x31e898 0x31e950
    | eapply ro_cells_agree; [exact AG|exact C2|]; static_iv 0x31fd90 0x320370 ].
Qed.

Lemma ap_statics_fixed_agree : forall OW E m m', ap_statics_fixed m E -> agree_on (lib_addr OW) m m' -> ap_statics_fixed m' E.
Proof.
  intros OW E m m' H AG.
  destruct H as (CS & RS & S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13 & (lk & S14) & S15 & S16 & S17 & S18 & S19 & S20 & (cb & S21) & (b0 & S22) & S23 & S24).
  split; [eapply crypto_statics_agree; [exact CS|exact AG]|]. split; [eapply realloc_statics_agree; [exact RS|exact AG]|].
  split; [exact I|].
  split; [eapply ro_cells_agree; [exact AG|exact S2|]; static_iv 0x3306d0 0x333158|].
  split; [eapply ro_cells_agree; [exact AG|exact S3|]; static_iv 0x3306d0 0x333158|].
  split; [eapply ro_cells_agree; [exact AG|exact S4|]; static_iv 0x3306d0 0x333158|].
  split; [eapply ro_cells_agree; [exact AG|exact S5|]; static_iv 0x3306d0 0x333158|].
  split; [eapply ro_cells_agree; [exact AG|exact S6|]; static_iv 0x3306d0 0x333158|].
  split; [eapply ro_cells_agree; [exact AG|exact S7|]; static_iv 0x3306d0 0x333158|].
  split; [eapply ro_cells_agree; [exact AG|exact S8|]; static_iv 0x3306d0 0x333158|].
  split; [eapply ro_cells_agree; [exact AG|exact S9|]; static_iv 0x3306d0 0x333158|].
  split; [eapply ro_cells_agree; [exact AG|exact S10|]; static_iv 0x3306d0 0x333158|].
  split; [eapply ro_cells_agree; [exact AG|exact S11|]; static_iv 0x3306d0 0x333158|].
  split; [eapply ro_cells_agree; [exact AG|exact S12|]; static_iv 0x3306d0 0x333158|].
  split; [eapply ro_cells_agree; [exact AG|exact S13|]; static_iv 0x3306d0 0x333158|].
  split; [exists lk; eapply ro_cells_agree; [exact AG|exact S14|]; static_iv 0x3306d0 0x333158|].
  split; [eapply ro_cells_agree; [exact AG|exact S15|]; static_iv 0x3331c8 0x3331d8|].
  split; [eapply ro_cells_agree; [exact AG|exact S16|]; static_iv 0x354150 0x3545b0|].
  split; [eapply ro_cells_agree; [exact AG|exact S17|]; static_iv 0x354150 0x3545b0|].
  split; [eapply rw_cells_agree; [exact AG|exact S18|]; static_iv 0x333192 0x333193|].
  split; [eapply ro_cells_agree; [exact AG|exact S19|]; static_iv 0x31fd90 0x320370|].
  split; [eapply ro_cells_agree; [exact AG|exact S20|]; static_iv 0x31fd90 0x320370|].
  split; [exists cb; eapply rw_cells_agree; [exact AG|exact S21|]; static_iv 0x3331c8 0x3331d8|].
  split; [exists b0; eapply rw_cells_agree; [exact AG|exact S22|]; static_iv 0x3306d0 0x333158|].
  split; [eapply rw_cells_agree; [exact AG|exact S23|]; static_iv 0x3306d0 0x333158|].
  eapply ro_cells_agree; [exact AG|exact S24|]; unfold SCT_FREE_GOT; static_iv 0x31e898 0x31e950.
  
Qed.

Local Ltac block_iv HIn :=
  intros a Ha; eapply lib_addr_block; [exact HIn|];
  cbn [cells_size csize Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ length repeat c8s c4s zeros4 map mutex_free_cells sa_cells bio_null_cells bio_cells lhash_cells] in Ha;
  unfold BIO_SIZE, ES_SIZE, MUTEX_SIZE, SZ_OBJ_LOCK, SZ_ADDED, SZ_ADDED_BUCKETS, OFF_MK_SA in *; lia.

Lemma ap_statics_cnf_agree : forall OW sg cnf m m', ap_statics_cnf m OW sg cnf -> agree_on (lib_addr OW) m m' -> ap_statics_cnf m' OW sg cnf.
Proof.
  intros OW sg [[[lk lh] bk]|] m m' H AG; cbn [ap_statics_cnf] in *.
  - destruct H as (S1 & S2 & S3 & S4 & S5 & S6 & I1 & I2 & I3 & M1 & M2 & M3).
    split; [eapply rw_cells_agree; [exact AG|exact S1|]; static_iv 0x3306d0 0x333158|].
    split; [eapply rw_cells_agree; [exact AG|exact S2|]; static_iv 0x3306d0 0x333158|].
    split; [eapply rw_cells_agree; [exact AG|exact S3|]; static_iv 0x3306d0 0x333158|].
    split; [eapply rw_cells_agree; [exact AG|exact S4|]; static_iv 0x3306d0 0x333158|].
    split; [eapply rw_cells_agree; [exact AG|exact S5|]; static_iv 0x3306d0 0x333158|].
    split; [eapply rw_cells_agree; [exact AG|exact S6|]; static_iv 0x354150 0x3545b0|].
    split; [exact I1|]. split; [exact I2|]. split; [exact I3|].
    split; [eapply rw_cells_agree; [exact AG|exact M1|]; block_iv I1|].
    split; [eapply rw_cells_agree; [exact AG|exact M2|]; block_iv I2|].
    eapply rw_cells_agree; [exact AG|exact M3|]; block_iv I3.
  - destruct H as (S1 & S2 & S3 & S4 & S5 & S6).
    split; [eapply rw_cells_agree; [exact AG|exact S1|]; static_iv 0x3306d0 0x333158|].
    split; [eapply rw_cells_agree; [exact AG|exact S2|]; static_iv 0x3306d0 0x333158|].
    split; [eapply rw_cells_agree; [exact AG|exact S3|]; static_iv 0x3306d0 0x333158|].
    split; [eapply rw_cells_agree; [exact AG|exact S4|]; static_iv 0x3306d0 0x333158|].
    split; [eapply rw_cells_agree; [exact AG|exact S5|]; static_iv 0x3306d0 0x333158|].
    eapply rw_cells_agree; [exact AG|exact S6|]; static_iv 0x354150 0x3545b0.
Qed.

(* [comment removed for export] *)
Lemma env_in : forall E OW, ap_env_ok E OW ->
  In (p_es E, e_es E, ES_SIZE) OW /\ In (p_mk E, e_mk E, 72) OW
  /\ In (p_sa E, e_sa E, 32) OW /\ In (p_nd E, e_nd E, 128) OW /\ In (p_xl E, e_xl E, MUTEX_SIZE) OW.
Proof.
  intros E OW (HF & _ & _). unfold env_blocks in HF.
  repeat match goal with H : Forall _ (_ :: _) |- _ => apply Forall_cons_iff in H; destruct H as [? H] end. repeat split; assumption.
Qed.

Lemma tl_chain_agree : forall E OW m m', ap_env_ok E OW -> tl_chain m E -> agree_on (lib_addr OW) m m' -> tl_chain m' E.
Proof.
  intros E OW m m' HE (T1 & (pad & T2) & T3) AG. destruct (env_in E OW HE) as (_ & IMK & ISA & IND & _).
  split; [eapply ro_cells_agree; [exact AG|exact T1|]; block_iv IMK|].
  split; [exists pad; eapply ro_cells_agree; [exact AG|exact T2|]; block_iv ISA|].
  eapply ro_cells_agree; [exact AG|exact T3|]; block_iv IND.
Qed.

Lemma exlock_free_agree : forall E OW m m', ap_env_ok E OW -> exlock_free m E -> agree_on (lib_addr OW) m m' -> exlock_free m' E.
Proof.
  intros E OW m m' HE H AG. destruct (env_in E OW HE) as (_ & _ & _ & _ & IXL).
  eapply rw_cells_agree; [exact AG|exact H|]; block_iv IXL.
Qed.

Lemma bio_out_rep_agree : forall E OW m m' pv nw, ap_env_ok E OW -> bio_out_rep m E pv nw -> agree_on (lib_addr OW) m m' -> bio_out_rep m' E pv nw.
Proof. intros; exact I. Qed.

Lemma err_rep_agree : forall E OW st m m', ap_env_ok E OW -> err_rep m E OW st -> agree_on (lib_addr OW) m m' -> err_rep m' E OW st.
Proof.
  intros E OW st m m' HE (Hsh & H & F1 & F2 & F3) AG. destruct (env_in E OW HE) as (IES & _).
  split; [exact Hsh|]. split; [|repeat split; assumption].
  pose proof Hsh as (L1 & L2 & L3 & L4 & L5 & L6 & L7).
  destruct H as (R0 & R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9).
  Local Ltac esa IES L :=
    intros a Ha; eapply lib_addr_block; [exact IES|];
    rewrite ?wl_length, ?length_map, ?repeat_length, ?L in Ha;
    unfold ESO_FLAGS, ESO_MARKS, ESO_BUFFER, ESO_DATA, ESO_DSIZE, ESO_DFLAGS, ESO_FILE, ESO_LINE, ESO_FUNC, ESO_TOP, ES_SIZE, ERR_NUM in *;
    cbn [cells_size csize Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ Pos.mul Pos.add] in Ha; lia.
  split; [eapply u32arr_agree; [exact AG|exact R0|]; esa IES L1|].
  split; [eapply u32arr_agree; [exact AG|exact R1|]; esa IES L1|].
  split; [eapply u64arr_agree; [exact AG|exact R2|]; esa IES L2|].
  split; [eapply u64arr_agree; [exact AG|exact R3|]; esa IES L3|].
  split; [eapply u64arr_agree; [exact AG|exact R4|]; esa IES L3|].
  split; [eapply u32arr_agree; [exact AG|exact R5|]; esa IES L4|].
  split; [eapply u64arr_agree; [exact AG|exact R6|]; esa IES L5|].
  split; [eapply u32arr_agree; [exact AG|exact R7|]; esa IES L6|].
  split; [eapply u64arr_agree; [exact AG|exact R8|]; esa IES L7|].
  eapply rw_cells_agree; [exact AG|exact R9|]; esa IES L1.
Qed.

Lemma ap_img_agree : forall OW m m', ap_img m -> agree_on (lib_addr OW) m m' -> ap_img m'.
Proof.
  intros OW m m' H AG a Ha. specialize (H a Ha). unfold mrd in *.
  assert (Ha64 : 0 <= a < 2^64) by (unfold IMG_LO, IMG_HI in Ha; lia).
  assert (HL : lib_addr OW a).
  { destruct (Z.lt_ge_cases a 0x317430); [apply (lib_addr_static _ a 0x2c2e98 0x317430)|apply (lib_addr_static _ a 0x317430 0x31e730)];
      unfold LIBW_HX, IMG_LO, IMG_HI in *; cbn; try tauto; lia. }
  destruct (AG a Ha64 HL) as [E _]. rewrite E. exact H.
Qed.

Theorem ap_state_agree : forall st m m' OW E bo, ap_state st m OW E bo -> agree_on (lib_addr OW) m m' -> ap_state st m' OW E bo.
Proof.
  intros st m m' OW E bo (HE & HI & HS & HC & HT & HX & HB & HR) AG. split; [exact HE|].
  split; [eapply ap_img_agree; [exact HI|exact AG]|].
  split; [eapply ap_statics_fixed_agree; [exact HS|exact AG]|].
  split; [eapply ap_statics_cnf_agree; [exact HC|exact AG]|].
  split; [eapply tl_chain_agree; [exact HE|exact HT|exact AG]|].
  split; [eapply exlock_free_agree; [exact HE|exact HX|exact AG]|].
  split; [eapply bio_out_rep_agree; [exact HE|exact HB|exact AG]|].
  eapply err_rep_agree; [exact HE|exact HR|exact AG].
Qed.

(* [comment removed for export] *)
Theorem ap_lib_inv_agree : forall ls OW m m',
  ap_lib_inv ls m OW -> agree_on (fun a => rin_ivs LIBW_HX a \/ in_block OW a) m m' -> ap_lib_inv ls m' OW.
Proof.
  intros ls OW m m' (E & Hwf & HSG & nw & HS) AG. exists E. split; [exact Hwf|]. split; [exact HSG|]. exists nw. eapply ap_state_agree; [exact HS|exact AG].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lib_addr_rclient : forall OW L SP a, (forall b, In b OW -> In b L) -> lib_addr OW a -> rclient_addr L SP a.
Proof.
  intros OW L SP a HL [H|H].
  - right. left. unfold LIBW_HX in H. cbn [rin_ivs fst snd] in H. unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP. lia.
  - right. right. destruct H as (b & Hb & Hr). exists b. split; [apply HL; exact Hb|exact Hr].
Qed.

Theorem ap_state_heap_pres : forall st m m' OW L E bo SP,
  ap_state st m OW E bo -> rheap_pres L SP m m' -> (forall b, In b OW -> In b L) -> ap_state st m' OW E bo.
Proof.
  intros st m m' OW L E bo SP HS HP HL. eapply ap_state_agree; [exact HS|].
  intros a Ha Hl. apply (HP a Ha). eapply lib_addr_rclient; [exact HL|exact Hl].
Qed.

(* [comment removed for export] *)
Lemma ap_state_heap_pres_app : forall st m m' OW LB E bo SP,
  ap_state st m OW E bo -> rheap_pres (OW ++ LB) SP m m' -> ap_state st m' OW E bo.
Proof. intros. eapply ap_state_heap_pres; [eassumption|eassumption|]. intros b Hb. apply in_app_iff. left. exact Hb. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma wl_lset : forall l i v, wl (lset l i v) = Arr.upd (wl l) i (wz v).
Proof. induction l as [|x l IH]; intros [|i] v; cbn; try reflexivity. unfold wl in IH. rewrite IH. reflexivity. Qed.

Lemma map_lset : forall {A B} (f : A -> B) l i v, map f (lset l i v) = lset (map f l) i (f v).
Proof. induction l as [|x l IH]; intros [|i] v; cbn; try reflexivity. rewrite IH. reflexivity. Qed.

Lemma lset_length : forall {A} (l : list A) i v, length (lset l i v) = length l.
Proof. induction l as [|x l IH]; intros [|i] v; cbn; auto. Qed.

(* [comment removed for export] *)
Lemma as_proj_set_file i v (st : ap_st bptr) :
  as_file (set_file i v st) = lset (as_file st) i v /\ as_func (set_file i v st) = as_func st /\ as_data (set_file i v st) = as_data st
  /\ as_marks (set_file i v st) = as_marks st /\ as_buf (set_file i v st) = as_buf st /\ as_line (set_file i v st) = as_line st
  /\ as_dflags (set_file i v st) = as_dflags st /\ as_top (set_file i v st) = as_top st /\ as_bottom (set_file i v st) = as_bottom st
  /\ as_cnf (set_file i v st) = as_cnf st.
Proof. repeat split; reflexivity. Qed.

Lemma es_shape_set : forall (st : ap_st bptr) i,
  es_shape st ->
  (forall v, es_shape (set_file i v st)) /\ (forall v, es_shape (set_func i v st)) /\ (forall v, es_shape (set_data i v st))
  /\ (forall v, es_shape (set_marks i v st)) /\ (forall v, es_shape (set_buf i v st)) /\ (forall v, es_shape (set_line i v st))
  /\ (forall v, es_shape (set_dflags i v st)) /\ (forall v, es_shape (set_top v st)) /\ (forall v, es_shape (set_bottom v st)).
Proof.
  intros st i (L1 & L2 & L3 & L4 & L5 & L6 & L7). unfold es_shape; cbn. repeat split; rewrite ?lset_length; assumption.
Qed.

(* [comment removed for export] *)
Lemma es_at_set_file : forall m A (st : ap_st bptr) adr i v,
  u32arr ctusegs m (A + ESO_FLAGS) (wl (repeat 0 ERR_NUM)) ->
  u32arr ctusegs m (A + ESO_MARKS) (wl (as_marks st)) ->
  u64arr ctusegs m (A + ESO_BUFFER) (wl (as_buf st)) ->
  u64arr ctusegs m (A + ESO_DATA) (wl (map (optr adr) (as_data st))) ->
  u64arr ctusegs m (A + ESO_DSIZE) (wl (map osize (as_data st))) ->
  u32arr ctusegs m (A + ESO_DFLAGS) (wl (as_dflags st)) ->
  u64arr ctusegs m (A + ESO_FILE) (Arr.upd (wl (map (optr adr) (as_file st))) i (wz (optr adr v))) ->
  u32arr ctusegs m (A + ESO_LINE) (wl (as_line st)) ->
  u64arr ctusegs m (A + ESO_FUNC) (wl (map (optr adr) (as_func st))) ->
  rw_cells ctusegs m (A + ESO_TOP) [C4 (wz (Z.of_nat (as_top st))); C4 (wz (Z.of_nat (as_bottom st)))] ->
  es_at m A (set_file i v st) adr.
Proof.
  intros m A st adr i v flags marks buf data dsize dflags file line func topbot.
  pose proof (eq_trans (f_equal wl (map_lset (optr adr) (as_file st) i v))
                       (wl_lset (map (optr adr) (as_file st)) i (optr adr v))) as file_words.
  rewrite <- file_words in file.
  exact (conj flags (conj marks (conj buf (conj data (conj dsize (conj dflags
           (conj file (conj line (conj func topbot))))))))).
Qed.

Lemma es_at_set_top : forall m A (st : ap_st bptr) adr (t b : nat),
  (let st' := set_bottom b (set_top t st) in
   u32arr ctusegs m (A + ESO_FLAGS) (wl (repeat 0 ERR_NUM)) ->
   u32arr ctusegs m (A + ESO_MARKS) (wl (as_marks st)) ->
   u64arr ctusegs m (A + ESO_BUFFER) (wl (as_buf st)) ->
   u64arr ctusegs m (A + ESO_DATA) (wl (map (optr adr) (as_data st))) ->
   u64arr ctusegs m (A + ESO_DSIZE) (wl (map osize (as_data st))) ->
   u32arr ctusegs m (A + ESO_DFLAGS) (wl (as_dflags st)) ->
   u64arr ctusegs m (A + ESO_FILE) (wl (map (optr adr) (as_file st))) ->
   u32arr ctusegs m (A + ESO_LINE) (wl (as_line st)) ->
   u64arr ctusegs m (A + ESO_FUNC) (wl (map (optr adr) (as_func st))) ->
   rw_cells ctusegs m (A + ESO_TOP) [C4 (wz (Z.of_nat t)); C4 (wz (Z.of_nat b))] ->
   es_at m A st' adr).
Proof.
  intros m A st adr t b st' flags marks buf data dsize dflags file line func topbot.
  exact (conj flags (conj marks (conj buf (conj data (conj dsize (conj dflags
           (conj file (conj line (conj func topbot))))))))).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma image_bytes_spec : forall n A bs, image_bytes ctusegs A n = Some bs ->
  forall i, (i < n)%nat -> seg_rom ctusegs (wa (A + Z.of_nat i)) = nth_error bs i.
Proof.
  induction n as [|k step]; intros A bs img i below; [lia|].
  cbn [image_bytes] in img.
  destruct (seg_rom ctusegs (wa A)) as [b0|] eqn:first_byte; [|discriminate img].
  destruct (image_bytes ctusegs (A + 1) k) as [rest|] eqn:tail_bytes; [|discriminate img].
  injection img as <-.
  destruct i as [|j].
  - replace (A + Z.of_nat 0) with A by lia. exact first_byte.
  - pose proof (step (A + 1) rest tail_bytes j ltac:(lia)) as later.
    replace (A + 1 + Z.of_nat j) with (A + Z.of_nat (S j)) in later by lia.
    exact later.
Qed.

(* [comment removed for export] *)
Lemma ap_img_ro_cells : forall m A n bs,
  ap_img m -> IMG_LO <= A -> A + Z.of_nat n <= IMG_HI -> image_bytes ctusegs A n = Some bs ->
  ro_cells ctusegs m A [CB n bs].
Proof.
  intros m A n bs pristine lo_ok hi_ok img.
  pose proof (image_bytes_length ctusegs n A bs img) as len_bs.
  assert (A_nonneg : 0 <= A) by (unfold IMG_LO in lo_ok; lia).
  assert (end_fits : A + Z.of_nat (length bs) <= 2 ^ 64) by (rewrite len_bs; unfold IMG_HI in hi_ok; lia).
  assert (reads : forall i : nat, (i < length bs)%nat -> mrd ctusegs m (wa (A + Z.of_nat i)) = nth_error bs i).
  { intros i below. rewrite len_bs in below.
    rewrite (pristine (A + Z.of_nat i)) by lia.
    exact (image_bytes_spec n A bs img i below). }
  pose proof (conj A_nonneg (conj end_fits reads) : bytes_at ctusegs m A bs) as raw.
  refine (conj (conj len_bs I) _).
  cbn [cells_bytes cbytes]. rewrite app_nil_r. exact raw.
Qed.
End WithCeiling0.
