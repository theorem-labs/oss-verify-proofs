(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Stdio Prog LibProg ProgG CtSizes CtWire CtModel.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import ApBase ApState ApLogic ApInv ApErr ApParse ApBridge.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit D_defs D_cs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import R_unwind_chain.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA BnRepDefs BnRepA ImplA ImplAX BnIfaceA UnwindA EdgesA UnwindX W_cryptoA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells ApErrKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApRepDefs ApRep ApIface W_get_objectA ApErrKitA2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctP Require Import SctDefs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctP Require SctRep O2iKit W_sct_list_free W_o2i_sct_list.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtPrnA Require Import W_sk_leavesA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctA Require Import SctRepA SctStmtA W_o2i_sigA O2iSctStmtB.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctA Require Import SctWire.                (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope am_scope.

(* [comment removed for export] *)
Definition O2I_SCT_LIST_STACK_A : Z := 128 + O2I_SCT_STACK_A.   (* [comment removed for export] *)
Definition O2I_SCT_LIST_COST_A : Z := 2 ^ 21.
Definition O2I_SCT_LIST_FRAMES_A : Z := O2I_SCT_FRAMES_A.

(* [comment removed for export] *)
Definition push_reserve (num : Z) : Z :=
  (if num <=? 6076 then mcost (8 * 9721) else 0) + (if num <=? 9721 then mcost (8 * 15553) else 0) + (if num <=? 15553 then mcost (8 * 24884) else 0).
(* [comment removed for export] *)
Definition sched : list Z := [4; 6; 9; 14; 22; 35; 56; 89; 142; 227; 363; 580; 928; 1484; 2374; 3798; 6076; 9721; 15553; 24884].
Definition na_sched (o : option (bptr * Z)) : Prop := match o with None => True | Some (_, na) => In na sched end.

Lemma mcost_nonneg : forall n, 0 <= mcost n.
Proof. intros n. unfold mcost. destruct (n <=? 64512) eqn:E; [lia| apply Z.leb_gt in E; lia]. Qed.
Lemma push_reserve_nonneg : forall num, 0 <= push_reserve num.
Proof.
  intros num. unfold push_reserve. pose proof (mcost_nonneg (8 * 9721)). pose proof (mcost_nonneg (8 * 15553)). pose proof (mcost_nonneg (8 * 24884)).
  destruct (num <=? 6076); destruct (num <=? 9721); destruct (num <=? 15553); lia.
Qed.
Lemma push_reserve_mono : forall a b, a <= b -> push_reserve b <= push_reserve a.
Proof.
  intros a b H. unfold push_reserve. pose proof (mcost_nonneg (8 * 9721)). pose proof (mcost_nonneg (8 * 15553)). pose proof (mcost_nonneg (8 * 24884)).
  destruct (a <=? 6076) eqn:A1; destruct (b <=? 6076) eqn:B1; destruct (a <=? 9721) eqn:A2; destruct (b <=? 9721) eqn:B2; destruct (a <=? 15553) eqn:A3; destruct (b <=? 15553) eqn:B3;
    rewrite ?Z.leb_le, ?Z.leb_gt in A1; rewrite ?Z.leb_le, ?Z.leb_gt in B1; rewrite ?Z.leb_le, ?Z.leb_gt in A2; rewrite ?Z.leb_le, ?Z.leb_gt in B2;
    rewrite ?Z.leb_le, ?Z.leb_gt in A3; rewrite ?Z.leb_le, ?Z.leb_gt in B3; lia.
Qed.
Lemma push_reserve_0 : push_reserve 0 = 851680.
Proof. reflexivity. Qed.
(* [comment removed for export] *)
Lemma sched_forallb : forall f, forallb f sched = true -> forall na, In na sched -> f na = true.
Proof. intros f H na Hin. exact (proj1 (forallb_forall f sched) H na Hin). Qed.
Lemma sched_next : forall na, In na sched -> na < 24884 -> In (na * 8 / 5) sched.
Proof.
  intros na H L.
  pose proof (sched_forallb (fun x => (24884 <=? x) || existsb (Z.eqb (x * 8 / 5)) sched) eq_refl na H) as X. cbn beta in X.
  apply Bool.orb_true_iff in X. destruct X as [X|X]; [apply Z.leb_le in X; lia|].
  apply existsb_exists in X. destruct X as (y & Hy & E). apply Z.eqb_eq in E. rewrite E. exact Hy.
Qed.
(* [comment removed for export] *)
Lemma sched_grow_cost : forall na, In na sched -> na < 24884 -> mcost (8 * (na * 8 / 5)) <= push_reserve na - push_reserve (na + 1).
Proof.
  intros na H L.
  pose proof (sched_forallb (fun x => (24884 <=? x) || (mcost (8 * (x * 8 / 5)) <=? push_reserve x - push_reserve (x + 1))) eq_refl na H) as X. cbn beta in X.
  apply Bool.orb_true_iff in X. destruct X as [X|X]; [apply Z.leb_le in X; lia|]. apply Z.leb_le in X. exact X.
Qed.
Lemma sched_ge4 : forall na, In na sched -> 4 <= na <= 24884.
Proof.
  intros na H. pose proof (sched_forallb (fun x => (4 <=? x) && (x <=? 24884)) eq_refl na H) as X. cbn beta in X.
  apply Bool.andb_true_iff in X. destruct X as [X1 X2]. apply Z.leb_le in X1. apply Z.leb_le in X2. lia.
Qed.
Lemma sched_step1 : forall na, In na sched -> na + 1 <= na * 8 / 5.
Proof. intros na H. pose proof (sched_forallb (fun x => x + 1 <=? x * 8 / 5) eq_refl na H) as X. cbn beta in X. apply Z.leb_le in X. exact X. Qed.

(* [comment removed for export] *)
Lemma mcost_superadd : forall a b, 0 <= a -> 0 <= b -> a + b <= 65535 -> mcost a + mcost b <= mcost (a + b).
Proof.
  intros a b Ha Hb Hab. unfold mcost.
  destruct (a <=? 64512) eqn:Ea; destruct (b <=? 64512) eqn:Eb; destruct (a + b <=? 64512) eqn:Eab;
    rewrite ?Z.leb_le, ?Z.leb_gt in Ea; rewrite ?Z.leb_le, ?Z.leb_gt in Eb; rewrite ?Z.leb_le, ?Z.leb_gt in Eab; lia.
Qed.

Lemma zlength_ge0' : forall {A} (l : list A), 0 <= zlength l.
Proof. intros A l. unfold zlength. lia. Qed.

(* [comment removed for export] *)
Lemma sct_repA_ext : forall (adr1 adr2 : bptr -> Z) mA L x, (forall q, In q (CtSctP.O2iKit.sct_ids x) -> adr2 q = adr1 q) -> sct_repA mA L adr1 x -> sct_repA mA L adr2 x.
Proof.
  intros adr1 adr2 mA L x H (H1 & AL & H2 & H3 & H4 & H5 & H6 & H7 & REST).
  assert (H' : forall q, In q (CtSctP.O2iKit.oid (sc_logid x)) \/ In q (CtSctP.O2iKit.oid (option_map fst (sc_ext x))) \/ In q (CtSctP.O2iKit.oid (option_map fst (sc_sig x)))
                         \/ In q (CtSctP.O2iKit.oid (option_map fst (sc_blob x))) \/ sc_blk x = q -> adr2 q = adr1 q).
  { intros q Hq. apply H. unfold CtSctP.O2iKit.sct_ids. rewrite !in_app_iff. cbn [In]. tauto. }
  assert (E5 : adr2 (sc_blk x) = adr1 (sc_blk x)) by (apply H'; right; right; right; right; reflexivity).
  assert (AR' : forall o, (forall q n, o = Some (q, n) -> adr2 q = adr1 q) -> arr_repA mA L adr1 o -> arr_repA mA L adr2 o).
  { intros [[q n]|] Ho Hr; cbn in *; [| exact I]. rewrite (Ho q n eq_refl). exact Hr. }
  split; [rewrite E5; exact H1|]. split; [rewrite E5; exact AL|]. split; [rewrite E5, (CtSctP.W_o2i_sct_list.sct_cells_ext adr1 adr2 x) by exact H; exact H2|].
  split; [apply AR'; [intros q n Ho; apply H'; left; unfold CtSctP.W_sct_list_free.osz32 in Ho; destruct (sc_logid x); cbn in Ho |- *; [injection Ho; intros; subst; left; reflexivity| discriminate]| exact H3]|].
  split; [apply AR'; [intros q n Ho; apply H'; right; left; rewrite Ho; left; reflexivity| exact H4]|].
  split; [apply AR'; [intros q n Ho; apply H'; right; right; left; rewrite Ho; left; reflexivity| exact H5]|].
  split; [apply AR'; [intros q n Ho; apply H'; right; right; right; left; rewrite Ho; left; reflexivity| exact H6]|].
  split; [rewrite (CtSctP.W_o2i_sct_list.sct_blocks_ext adr1 adr2 x) by exact H; exact H7| exact REST].
Qed.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition o2i_list_postA2 (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (Σ : rts RT) (OW LB : list block) (E : ap_env) (lo : Z) (m : mem) (K : list block) (CST : Z)
    (adr : bptr -> Z) (len PIN : Z)
    (r : option (skr bptr) * ap_st bptr) (Σ' : rts RT) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m' OW' bo' (adr' : bptr -> Z) (NEW : list block) (pv : word),
    ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 (wz match fst r with Some k => adr' (sk_blk k) | None => 0 end) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctasegs)
    /\ ap_preA Σ' (snd r) m' OW' (NEW ++ LB) E bo' sp lo 0 0 0
    /\ ax_pres LB (bv_unsigned sp) ([(PIN, PIN + 8)] ++ LIBW_A) m m'
    /\ rt_credit RT Σ - CST <= rt_credit RT Σ'
    /\ blocks_kept K (snd r) OW' m m'
    /\ (forall b, In b LB -> adr' (blk_id b) = adr (blk_id b))
    /\ (forall b, In b NEW -> ~ In (blk_id b) (map blk_id (OW' ++ LB)))
    /\ Forall lbokA NEW
    /\ rw_cells ctasegs m' PIN [C8 pv]
    /\ match fst r with
       | None => NEW = []
       | Some k => Permutation NEW (sk_blocks adr' k) /\ sk_repA m' (OW' ++ NEW ++ LB) adr' k /\ 2 + sk_wire k <= len /\ len <= MAX_SCT_LIST_SIZE
                   /\ 3 * zlength (sk_items k) + 2 <= len
       end.

Definition o2i_sct_list_specA2 (STK : Z) (CST : Z -> Z) (FRM : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z)
         (lo : Z) (K : list block) (ras : list Z)
         (adr : bptr -> Z) (c : list Z) (D len PIN : Z),
    ap_preA Σ st m OW LB E bo sp lo STK (CST len) FRM -> tp = wz TP_A ->
    uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx O2I_SCT_LIST_A (bv_unsigned ra :: ras) -> ras <> nil ->
    (forall b, In b K -> In b OW) -> (forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E)) ->
    len = zlength c -> 0 <= D -> D + zlength c < 2 ^ 63 -> Forall (fun b => 0 <= b < 256) c -> bytes_at ctasegs m D (to_bytes c) ->
    (c = [] \/ exists pb PA psz, In (pb, PA, psz) LB /\ PA <= D /\ D + zlength c <= PA + psz) ->
    (forall b, In b LB -> adr (blk_id b) = blk_addr b) ->
    cellA_in LB PIN 8 -> PIN mod 8 = 0 -> (PIN + 8 <= D \/ D + zlength c <= PIN) -> rw_cells ctasegs m PIN [C8 (wz D)] ->
    a0 = wz 0 -> a1 = wz PIN -> a2 = wz len ->
    implAp (o2i_sct_list c len st) Σ
           (o2i_list_postA2 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB E lo m K (CST len) adr len PIN)
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz O2I_SCT_LIST_A) fc None m (seg_rom ctasegs)).

End WithRT.
