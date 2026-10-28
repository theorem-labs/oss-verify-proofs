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
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import ApBase ApState ApOwner.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit D_libiface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import LibKitA ARun BnHeapA BnRepDefs BnRepA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApRepDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma wl_length l : length (wl l) = length l. Proof. unfold CtRepP.ApRepDefs.wl. apply length_map. Qed.

(* [comment removed for export] *)
Definition lib_addr (OW : list block) (a : Z) : Prop := rin_ivs LIBW_S a \/ in_block OW a.

Lemma lib_addr_static : forall OW a lo hi, In (lo, hi) LIBW_S -> lo <= a < hi -> lib_addr OW a.
Proof.
  intros OW a lo hi Hin Ha. left. unfold LIBW_S in *. cbn [rin_ivs fst snd].
  repeat (destruct Hin as [E|Hin]; [injection E as <- <-; tauto|]). destruct Hin.
Qed.

Lemma lib_addr_block : forall OW a p A n, In (p, A, n) OW -> A <= a < A + n -> lib_addr OW a.
Proof. intros OW a p A n Hin Ha. right. exists (p, A, n). split; [exact Hin|]. cbn. exact Ha. Qed.

(* [comment removed for export] *)
Lemma LIBW_S_A : forall a, rin_ivs LIBW_S a -> rin_ivs LIBW_A a.
Proof. intros a Ha. unfold LIBW_S, LIBW_A in *. cbn [rin_ivs fst snd] in *. lia. Qed.
Lemma LIBW_S_FP : forall a, rin_ivs LIBW_S a -> in_ranges LIB_FP a.
Proof.
  intros a Ha. unfold LIBW_S, LIB_FP, in_ranges in *. cbn [rin_ivs fst snd] in Ha.
  destruct Ha as [H|[H|[H|[H|[H|[]]]]]];
    [ exists 0x5aebe0, 0x5af400 | exists 0xba46c0, 0xba8ae0 | exists 0xba935a, 0xba935b | exists 0xba9390, 0xba9398 | exists 0xbca7a0, 0xbcab98 ];
    (split; [cbn; tauto| lia]).
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
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma crypto_statics_agree' : forall OW m m', crypto_statics m -> agree_on (lib_addr OW) m m' -> crypto_statics m'.
Proof.
  intros OW m m' (C1 & C2 & C3 & C4) AG. unfold BnRepDefs.crypto_statics.
  split; [eapply ro_cells_agree; [exact AG|exact C1|]; unfold CR_MEMSET_FUNC; static_iv 0x5aebe0 0x5af400|].
  split; [eapply ro_cells_agree; [exact AG|exact C2|]; unfold CR_MALLOC_IMPL; static_iv 0x5aebe0 0x5af400|].
  split; [eapply ro_cells_agree; [exact AG|exact C3|]; unfold CR_FREE_IMPL; static_iv 0x5aebe0 0x5af400|].
  eapply ro_cells_agree; [exact AG|exact C4|]; unfold CR_NO_CUSTOMIZE; static_iv 0xba46c0 0xba8ae0.
Qed.

Lemma realloc_statics_agree : forall OW m m', realloc_statics m -> agree_on (lib_addr OW) m m' -> realloc_statics m'.
Proof. intros OW m m' C1 AG. unfold realloc_statics in *. eapply ro_cells_agree; [exact AG|exact C1|]. static_iv 0x5aebe0 0x5af400. Qed.

Lemma ap_statics_fixed_agree : forall OW E m m', ap_statics_fixed m E -> agree_on (lib_addr OW) m m' -> ap_statics_fixed m' E.
Proof.
  intros OW E m m' H AG.
  destruct H as (CS & RS & S1 & S2 & S2b & S3 & S4 & S5 & S6 & S6b & S7 & S7b & S8 & S9 & S10 & S11 & S12 & S12b & S13 & (lk & S14) & S16 & S17 & (u & S18) & S19 & S20 & (cb & S21) & (b0 & S22) & S23).
  split; [eapply crypto_statics_agree'; [exact CS|exact AG]|]. split; [eapply realloc_statics_agree; [exact RS|exact AG]|].
  split; [exact I|].
  split; [eapply ro_cells_agree; [exact AG|exact S2|]; static_iv 0xba46c0 0xba8ae0|].
  split; [eapply ro_cells_agree; [exact AG|exact S2b|]; static_iv 0xba46c0 0xba8ae0|].
  split; [eapply ro_cells_agree; [exact AG|exact S3|]; static_iv 0xba46c0 0xba8ae0|].
  split; [eapply ro_cells_agree; [exact AG|exact S4|]; static_iv 0xba46c0 0xba8ae0|].
  split; [eapply ro_cells_agree; [exact AG|exact S5|]; static_iv 0xba46c0 0xba8ae0|].
  split; [eapply ro_cells_agree; [exact AG|exact S6|]; static_iv 0xba46c0 0xba8ae0|].
  split; [eapply ro_cells_agree; [exact AG|exact S6b|]; static_iv 0xba46c0 0xba8ae0|].
  split; [eapply ro_cells_agree; [exact AG|exact S7|]; static_iv 0xba46c0 0xba8ae0|].
  split; [eapply ro_cells_agree; [exact AG|exact S7b|]; static_iv 0xba46c0 0xba8ae0|].
  split; [eapply ro_cells_agree; [exact AG|exact S8|]; static_iv 0xba46c0 0xba8ae0|].
  split; [eapply ro_cells_agree; [exact AG|exact S9|]; static_iv 0xba46c0 0xba8ae0|].
  split; [eapply ro_cells_agree; [exact AG|exact S10|]; static_iv 0xba46c0 0xba8ae0|].
  split; [eapply ro_cells_agree; [exact AG|exact S11|]; static_iv 0xba46c0 0xba8ae0|].
  split; [eapply ro_cells_agree; [exact AG|exact S12|]; static_iv 0xba46c0 0xba8ae0|].
  split; [eapply ro_cells_agree; [exact AG|exact S12b|]; static_iv 0xba46c0 0xba8ae0|].
  split; [eapply ro_cells_agree; [exact AG|exact S13|]; static_iv 0xba46c0 0xba8ae0|].
  split; [exists lk; eapply ro_cells_agree; [exact AG|exact S14|]; static_iv 0xba46c0 0xba8ae0|].
  split; [eapply ro_cells_agree; [exact AG|exact S16|]; static_iv 0xbca7a0 0xbcab98|].
  split; [eapply ro_cells_agree; [exact AG|exact S17|]; static_iv 0xbca7a0 0xbcab98|].
  split; [exists u; eapply rw_cells_agree; [exact AG|exact S18|]; static_iv 0xba935a 0xba935b|].
  split; [eapply ro_cells_agree; [exact AG|exact S19|]; static_iv 0x5aebe0 0x5af400|].
  split; [eapply ro_cells_agree; [exact AG|exact S20|]; static_iv 0x5aebe0 0x5af400|].
  split; [exists cb; eapply rw_cells_agree; [exact AG|exact S21|]; static_iv 0xba9390 0xba9398|].
  split; [exists b0; eapply rw_cells_agree; [exact AG|exact S22|]; static_iv 0xba46c0 0xba8ae0|].
  eapply rw_cells_agree; [exact AG|exact S23|]; static_iv 0xba46c0 0xba8ae0.
Qed.

Lemma ap_statics_cnf_agree : forall OW sg cnf m m', ap_statics_cnf m OW sg cnf -> agree_on (lib_addr OW) m m' -> ap_statics_cnf m' OW sg cnf.
Proof.
  intros OW sg [[[lk lh] bk]|] m m' H AG; cbn [ap_statics_cnf] in *.
  - destruct H as (S1 & S1b & S2 & S3 & S3b & S4 & S4b & S6 & I1 & I2 & I3 & M1 & M2 & M3).
    split; [eapply rw_cells_agree; [exact AG|exact S1|]; static_iv 0xba46c0 0xba8ae0|].
    split; [eapply rw_cells_agree; [exact AG|exact S1b|]; static_iv 0xba46c0 0xba8ae0|].
    split; [eapply rw_cells_agree; [exact AG|exact S2|]; static_iv 0xba46c0 0xba8ae0|].
    split; [eapply rw_cells_agree; [exact AG|exact S3|]; static_iv 0xba46c0 0xba8ae0|].
    split; [eapply rw_cells_agree; [exact AG|exact S3b|]; static_iv 0xba46c0 0xba8ae0|].
    split; [eapply rw_cells_agree; [exact AG|exact S4|]; static_iv 0xba46c0 0xba8ae0|].
    split; [eapply rw_cells_agree; [exact AG|exact S4b|]; static_iv 0xba46c0 0xba8ae0|].
    split; [eapply rw_cells_agree; [exact AG|exact S6|]; static_iv 0xbca7a0 0xbcab98|].
    split; [exact I1|]. split; [exact I2|]. split; [exact I3|].
    split; [eapply rw_cells_agree; [exact AG|exact M1|]; block_iv I1|].
    split; [eapply rw_cells_agree; [exact AG|exact M2|]; block_iv I2|].
    eapply rw_cells_agree; [exact AG|exact M3|]; block_iv I3.
  - destruct H as (S1 & S1b & S2 & S3 & S3b & S4 & S4b & S6).
    split; [eapply rw_cells_agree; [exact AG|exact S1|]; static_iv 0xba46c0 0xba8ae0|].
    split; [eapply rw_cells_agree; [exact AG|exact S1b|]; static_iv 0xba46c0 0xba8ae0|].
    split; [eapply rw_cells_agree; [exact AG|exact S2|]; static_iv 0xba46c0 0xba8ae0|].
    split; [eapply rw_cells_agree; [exact AG|exact S3|]; static_iv 0xba46c0 0xba8ae0|].
    split; [eapply rw_cells_agree; [exact AG|exact S3b|]; static_iv 0xba46c0 0xba8ae0|].
    split; [eapply rw_cells_agree; [exact AG|exact S4|]; static_iv 0xba46c0 0xba8ae0|].
    split; [eapply rw_cells_agree; [exact AG|exact S4b|]; static_iv 0xba46c0 0xba8ae0|].
    eapply rw_cells_agree; [exact AG|exact S6|]; static_iv 0xbca7a0 0xbcab98.
Qed.

(* [comment removed for export] *)
Lemma env_in : forall E OW, ap_env_ok E OW ->
  In (p_es E, e_es E, ES_SIZE) OW /\ In (p_mk E, e_mk E, 72) OW
  /\ In (p_sa E, e_sa E, 32) OW /\ In (p_nd E, e_nd E, 128) OW /\ In (p_xl E, e_xl E, MUTEX_SIZE) OW.
Proof.
  intros E OW (HF & _ & _). unfold CtRepP.ApRepDefs.env_blocks in HF.
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

(* [comment removed for export] *)
Section WithRT.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Lemma ap_img_of_art : forall Σ m, ART RT Σ m -> ap_img m.
Proof. intros Σ m HA. destruct (af_client_consts RT AF Σ m HA) as (_ & _ & _ & _ & R). exact R. Qed.

Lemma ap_img_of_heap : forall Σ OW LB m, AHEAP Σ OW LB m -> ap_img m.
Proof. intros Σ OW LB m H. exact (ap_img_of_art Σ m (AH_art _ _ _ _ H)). Qed.

Theorem ap_state_agree : forall st m m' OW E bo, ap_state st m OW E bo -> agree_on (lib_addr OW) m m' -> ap_state st m' OW E bo.
Proof.
  intros st m m' OW E bo (HE & HS & HC & HT & HX & HB & HR) AG. split; [exact HE|].
  split; [eapply ap_statics_fixed_agree; [exact HS|exact AG]|].
  split; [eapply ap_statics_cnf_agree; [exact HC|exact AG]|].
  split; [eapply tl_chain_agree; [exact HE|exact HT|exact AG]|].
  split; [eapply exlock_free_agree; [exact HE|exact HX|exact AG]|].
  split; [eapply bio_out_rep_agree; [exact HE|exact HB|exact AG]|].
  eapply err_rep_agree; [exact HE|exact HR|exact AG].
Qed.

(* [comment removed for export] *)
Theorem ap_state_rt : forall st m m' OW LB E bo SP,
  ap_state st m OW E bo -> agree_on (aclient_addr (OW ++ LB) SP) m m' -> ap_state st m' OW E bo.
Proof.
  intros st m m' OW LB E bo SP HS AG. eapply ap_state_agree; [exact HS|].
  eapply agree_on_mono; [exact AG|]. intros a [Ha|(b & Hb & Hr)].
  - right; left. exact (ar_LIBW_cs a (LIBW_S_A a Ha)).
  - right; right. exists b. split; [apply in_or_app; left; exact Hb| exact Hr].
Qed.

(* [comment removed for export] *)
Theorem ap_state_libfp : forall st m m' OW E bo,
  ap_state st m OW E bo -> (forall a : word, in_ranges LIB_FP (bv_unsigned a) \/ in_live (map blk_an OW) (bv_unsigned a) -> m' a = m a) ->
  ap_state st m' OW E bo.
Proof.
  intros st m m' OW E bo HS AG. eapply ap_state_agree; [exact HS|].
  intros a Ha HL. unfold wa. pose proof (AG (Z_to_bv 64 a)) as EQ. rewrite unsigned_lit in EQ by lia. apply EQ.
  destruct HL as [H|(b & Hb & Hr)]; [left; exact (LIBW_S_FP a H)| right].
  exists (blk_addr b), (blk_size b). split; [| exact Hr]. apply in_map_iff. exists b. split; [reflexivity| exact Hb].
Qed.

End WithRT.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
