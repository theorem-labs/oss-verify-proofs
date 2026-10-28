(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Stdio Prog LibProg ProgG CtSizes CtWire CtTime CtModel ApBase ApState ApLogic ApInv ApErr ApParse ApBridge.
From Stdlib Require Import ZArith List Lia Bool Permutation FunctionalExtensionality.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit D_defs D_cs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import R_unwind_chain.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA BnRepDefs BnRepA ImplA ImplAX BnIfaceA UnwindA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtFrameA Require Import AFrameKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require ApIface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApRepDefs ApRep ApIface ApErrKitA ApErrKitA2 PzBitsA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctP Require Import SctDefs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctP Require W_sct_list_free SctRep W_sk_leaves SctStmt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctA Require Import SctRepA SctStmtA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHarA Require Import Fr_FuzzerTestOneInput.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma apbind_assoc : forall {ptr A B C} (t : aprog ptr A) (f : A -> aprog ptr B) (g : B -> aprog ptr C),
  apbind (apbind t f) g = apbind t (fun a => apbind (f a) g).
Proof.
  intros ptr A B C t. induction t as [a| |n k IH|p k IH|p n k IH|p n k IH|o k IH|p n k IH]; intros f g; cbn [apbind]; try reflexivity;
    f_equal; try (apply functional_extensionality; intros r; apply IH); apply IH.
Qed.

Lemma abind_assoc : forall {ptr A B C} (m : @AM ptr A) (f : A -> @AM ptr B) (g : B -> @AM ptr C) st,
  abind (abind m f) g st = abind m (fun a => abind (f a) g) st.
Proof.
  intros ptr A B C m f g st. unfold abind. rewrite apbind_assoc. reflexivity.
Qed.

(* [comment removed for export] *)
Definition ct_after {ptr} (ok : option (skr ptr)) : @AM ptr unit :=
  match ok with
  | None => aret tt
  | Some k => abind (amalloc SZ_BIO) (fun bio => abind (sct_list_print k) (fun _ => abind (afree bio) (fun _ => abind (i2d_sct_list k) (fun _ => sk_free_all k))))
  end.
Definition ct_tail {ptr} : @AM ptr Z := abind err_clear_error (fun _ => aret 0).
Definition ct_kk {ptr} (ok : option (skr ptr)) : @AM ptr Z := abind (ct_after ok) (fun _ => ct_tail).

Lemma ct_call_tree : forall (d : list Z) (st : ap_st bptr), ct_call d st = CtSctP.SctStmt.d2i_list_tree d ct_kk st.
Proof.
  intros d st. unfold ct_call, CtSctP.SctStmt.d2i_list_tree, ct_kk, ct_tail, ct_after. unfold abind. cbv beta.
  f_equal. apply functional_extensionality. intros [[os|] st1]; cbn [fst snd]; [| reflexivity].
  rewrite apbind_assoc. f_equal. apply functional_extensionality. intros [k st2]. cbn [fst snd].
  rewrite apbind_assoc. f_equal. all: try (apply functional_extensionality; intros [u st3]; cbn [fst snd]; destruct k as [k|]; reflexivity).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithCeiling. Context {CE__ : Ceiling.Ceiling}.
Lemma arr_repA_relist : forall m L L' adr o,
  arr_repA m L adr o -> (forall b, In b (CtSctP.W_sct_list_free.oblk adr o) -> In b L') -> arr_repA m L' adr o.
Proof.
  intros m L L' adr [[q n]|] H HI; cbn in *; [| exact I]. destruct H as (H1 & H2 & H3). split; [exact H1|]. split; [apply HI; left; reflexivity| exact H3].
Qed.

Lemma sct_repA_relist : forall m L L' adr s,
  sct_repA m L adr s -> (forall b, In b (sct_blocks adr s) -> In b L') -> sct_repA m L' adr s.
Proof.
  intros m L L' adr s (H1 & AL & H2 & H3 & H4 & H5 & H6 & H7) HI. unfold CtSctP.W_sct_list_free.sct_blocks in HI.
  split; [apply HI; rewrite !in_app_iff; do 4 right; left; reflexivity|]. split; [exact AL|]. split; [exact H2|].
  split; [eapply arr_repA_relist; [exact H3|]; intros b Hb; apply HI; rewrite !in_app_iff; tauto|].
  split; [eapply arr_repA_relist; [exact H4|]; intros b Hb; apply HI; rewrite !in_app_iff; tauto|].
  split; [eapply arr_repA_relist; [exact H5|]; intros b Hb; apply HI; rewrite !in_app_iff; tauto|].
  split; [eapply arr_repA_relist; [exact H6|]; intros b Hb; apply HI; rewrite !in_app_iff; tauto| exact H7].
Qed.

Lemma sk_repA_relist : forall m L L' adr k,
  sk_repA m L adr k -> (forall b, In b (sk_blocks adr k) -> In b L') -> sk_repA m L' adr k.
Proof.
  intros m L L' adr k (H1 & H2 & H3 & H4 & H5) HI. unfold CtSctP.SctStmt.sk_blocks in HI.
  split; [split; [apply HI; rewrite !in_app_iff; right; right; left; reflexivity| exact (proj2 H1)]|]. split; [exact H2|].
  split.
  - destruct (sk_data k) as [[q na]|]; [| exact H3]. destruct H3 as (A1 & A2). split; [| exact A2]. apply HI. rewrite !in_app_iff. right. left. left. reflexivity.
  - split; [| exact H5]. apply Forall_forall. intros s Hs. eapply sct_repA_relist; [exact (proj1 (Forall_forall _ _) H4 s Hs)|].
    intros b Hb. apply HI. rewrite !in_app_iff. left. clear - Hs Hb. induction (sk_items k) as [|s' t IH]; [destruct Hs|].
    cbn. apply in_app_iff. destruct Hs as [->|Hs]; [left; exact Hb| right; exact (IH Hs)].
Qed.

Lemma sk_repA_blocks : forall m L adr k b, sk_repA m L adr k -> In b (sk_blocks adr k) -> In b L.
Proof. intros. eapply sk_repA_blocks_in; eassumption. Qed.

(* [comment removed for export] *)
Lemma arr_repA_agree : forall P m m' L adr o,
  agree_on P m m' -> (forall q n a, o = Some (q, n) -> adr q <= a < adr q + n -> P a) -> arr_repA m L adr o -> arr_repA m' L adr o.
Proof.
  intros P m m' L adr [[q n]|] AG HP H; cbn in *; [| exact I]. destruct H as (Hn & HL & bs & HB). split; [exact Hn|]. split; [exact HL|]. exists bs.
  eapply rw_cells_agree; [exact AG| exact HB|]. intros a Ha. cbn in Ha. rewrite Nat.add_0_r, Z2Nat.id in Ha by lia. eapply HP; [reflexivity| lia].
Qed.

Lemma sct_repA_agree : forall P m m' L adr s,
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
  split; [eapply arr_repA_agree; [exact AG| intros q n a Ho Ha; apply (HP (q, adr q, n)); [apply BL; left; rewrite Ho; left; reflexivity| cbn; lia]| exact H3]|].
  split; [eapply arr_repA_agree; [exact AG| intros q n a Ho Ha; apply (HP (q, adr q, n)); [apply BL; right; left; rewrite Ho; left; reflexivity| cbn; lia]| exact H4]|].
  split; [eapply arr_repA_agree; [exact AG| intros q n a Ho Ha; apply (HP (q, adr q, n)); [apply BL; right; right; left; rewrite Ho; left; reflexivity| cbn; lia]| exact H5]|].
  split; [eapply arr_repA_agree; [exact AG| intros q n a Ho Ha; apply (HP (q, adr q, n)); [apply BL; right; right; right; left; rewrite Ho; left; reflexivity| cbn; lia]| exact H6]|].
  exact REST.
Qed.

Lemma sk_cellsA_size : forall adr k sorted, Z.of_nat (cells_size (sk_cells adr k sorted)) = STACK_SIZE.
Proof. intros. reflexivity. Qed.

Lemma sk_repA_agree : forall P m m' L adr k,
  agree_on P m m' -> (forall b a, In b (sk_blocks adr k) -> blk_addr b <= a < blk_addr b + blk_size b -> P a) -> sk_repA m L adr k -> sk_repA m' L adr k.
Proof.
  intros P m m' L adr k AG HP (HIN & (sorted & SR & HC) & HD & HF & ND).
  split; [exact HIN|]. split.
  { exists sorted. split; [exact SR|]. eapply rw_cells_agree; [exact AG| exact HC|]. intros a Ha. rewrite sk_cellsA_size in Ha.
    apply (HP (sk_blk k, adr (sk_blk k), STACK_SIZE)); [unfold CtSctP.SctStmt.sk_blocks; rewrite !in_app_iff; right; right; left; reflexivity| cbn; exact Ha]. }
  split.
  { destruct (sk_data k) as [[q na]|] eqn:ED; [| exact HD]. destruct HD as (H1 & HA & H2 & H3 & jb & H4 & H5). split; [exact H1|]. split; [exact HA|]. split; [exact H2|]. split; [exact H3|].
    exists jb. split; [exact H4|]. eapply rw_cells_agree; [exact AG| exact H5|]. intros a Ha. rewrite CtSctP.W_sk_leaves.data_block_size in Ha.
    apply (HP (q, adr q, 8 * na)); [unfold CtSctP.SctStmt.sk_blocks; rewrite ED, !in_app_iff; right; left; left; reflexivity| cbn]. unfold sk_num in *. lia. }
  split; [| exact ND].
  apply Forall_forall. intros s Hs. eapply sct_repA_agree; [exact AG| | exact (proj1 (Forall_forall _ _) HF s Hs)].
  intros b a Hb Ha. apply (HP b); [| exact Ha]. unfold CtSctP.SctStmt.sk_blocks. rewrite !in_app_iff. left.
  clear - Hs Hb. induction (sk_items k) as [|y t IH]; [destruct Hs|]. cbn. apply in_app_iff. destruct Hs as [<-|Hs]; [left; exact Hb| right; exact (IH Hs)].
Qed.
End WithCeiling.

Section WithRT.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)
Lemma AHEAP_permLB : forall Σ OW LB LB' m, AHEAP Σ OW LB m -> Permutation LB LB' -> AHEAP Σ OW LB' m.
Proof.
  intros Σ OW LB LB' m (HA & HS & HFr & (FW & PB & LBr & P1 & P2 & F & AP) & ND & HF1 & HF2) P.
  split; [exact HA|]. split; [exact HS|]. split; [exact HFr|].
  split. { split; [exact FW|]. exists PB, LBr. split; [| split; [exact P2| split; [exact F| exact AP]]]. eapply Permutation_trans; [symmetry; exact P| exact P1]. }
  split. { eapply nodup_ids_perm; [| exact ND]. apply Permutation_app_head. exact P. }
  split; [exact HF1|]. apply Forall_forall. intros b Hb. apply (proj1 (Forall_forall _ _) HF2). eapply Permutation_in; [symmetry; exact P| exact Hb].
Qed.

Lemma AHEAP_permOW : forall Σ OW OW' LB m, AHEAP Σ OW LB m -> Permutation OW OW' -> AHEAP Σ OW' LB m.
Proof.
  intros Σ OW OW' LB m (HA & HS & HFr & (FW & PB & LBr & P1 & P2 & F & AP) & ND & HF1 & HF2) P.
  split; [exact HA|]. split; [exact HS|]. split; [exact HFr|].
  split. { split; [exact FW|]. exists PB, LBr. split; [exact P1|]. split; [| split; [exact F| exact AP]].
           eapply Permutation_trans; [exact P2|]. apply Permutation_map. apply Permutation_app_tail. exact P. }
  split. { eapply nodup_ids_perm; [| exact ND]. apply Permutation_app_tail. exact P. }
  split; [| exact HF2]. apply Forall_forall. intros b Hb. apply (proj1 (Forall_forall _ _) HF1). eapply Permutation_in; [symmetry; exact P| exact Hb].
Qed.

(* [comment removed for export] *)
Lemma optb_ok_remove_other : forall (OW : list block) p o, List.NoDup (map blk_id OW) ->
  (forall q k, o = Some (q, k) -> q <> p) -> optb_ok OW o -> optb_ok (lb_remove p OW) o.
Proof.
  intros OW p [[q k]|] ND Ho H; [|exact I]. unfold CtRepP.ApRepDefs.optb_ok in *. destruct H as [HIn Hpos]. specialize (Ho q k eq_refl).
  rewrite (badr_remove_other OW q p Ho). split; [|exact Hpos]. apply lb_remove_In. split; [exact HIn|]. cbn. exact Ho.
Qed.

Lemma map_optr_remove_other : forall (OW : list block) p (l : list (option (bptr * Z))),
  (forall q k, In (Some (q, k)) l -> q <> p) -> map (optr (badr (lb_remove p OW))) l = map (optr (badr OW)) l.
Proof.
  intros OW p l Hl. induction l as [|o l IH]; [reflexivity|]. cbn [map]. rewrite IH by (intros q k H; apply (Hl q k); right; exact H). f_equal.
  destruct o as [[q k]|]; [|reflexivity]. unfold optr. apply badr_remove_other. apply (Hl q k). left. reflexivity.
Qed.

Lemma in_fm_es_ids : forall (st : ap_st bptr) q k,
  (In (Some (q, k)) (as_file st) \/ In (Some (q, k)) (as_func st) \/ In (Some (q, k)) (as_data st)) -> In q (es_ids st).
Proof.
  intros st q k H. unfold CtRepP.ApIface.es_ids, st_blocks. rewrite !map_app, !in_app_iff.
  assert (FM : forall l, In (Some (q, k)) l -> In q (map fst (fm l))).
  { intros l Hl. induction l as [|o l IH]; [destruct Hl|]. destruct Hl as [->|Hl]; cbn; [left; reflexivity|].
    destruct o as [[q' k']|]; cbn; [right|]; apply IH; exact Hl. }
  destruct H as [H|[H|H]]; [left|right; left|right; right; left]; apply FM; exact H.
Qed.

Lemma ap_state_remove_other : forall st m OW E bo q,
  ap_state st m OW E bo -> ~ In q (env_ids E) -> ~ In q (es_ids st) -> ap_state st m (lb_remove q OW) E bo.
Proof.
  intros st m OW E bo q AS NE NS.
  pose proof (proj1 (ap_state_splitA _ _ _ _ _) AS) as [HR ER]. destruct ER as (SH & EAT & F1 & F2 & F3).
  pose proof AS as (HE & _). destruct HE as (_ & ND & _).
  assert (NR : ~ In q (map blk_id (rest_blocks OW E (as_cnf st)))).
  { rewrite rest_ids. rewrite in_app_iff. intros [H|H]; [apply NE; rewrite env_ids_unfold; cbn [In] in H |- *; tauto|].
    apply NS. apply cnf_ids_in_es_ids. exact H. }
  assert (NEs : q <> p_es E) by (intros ->; apply NE; rewrite env_ids_unfold; cbn; tauto).
  assert (OTH : forall l, (forall o, In o l -> In o (as_file st) \/ In o (as_func st) \/ In o (as_data st)) -> forall q' k, In (Some (q', k)) l -> q' <> q).
  { intros l Hl q' k HIn ->. apply NS. eapply in_fm_es_ids. apply Hl. exact HIn. }
  apply ap_state_joinA.
  - apply rest_OW_removeA; [exact HR| exact NR| exact NEs].
  - exact SH.
  - rewrite (g_of_adr_ext st (badr OW) (badr (lb_remove q OW)));
      [apply es_at_raw; exact EAT| apply map_optr_remove_other; apply OTH; tauto| apply map_optr_remove_other; apply OTH; tauto| apply map_optr_remove_other; apply OTH; tauto].
  - apply Forall_forall. intros o Ho. apply optb_ok_remove_other; [exact ND| intros q' k ->; eapply OTH; [|exact Ho]; tauto| exact (proj1 (Forall_forall _ _) F1 o Ho)].
  - apply Forall_forall. intros o Ho. apply optb_ok_remove_other; [exact ND| intros q' k ->; eapply OTH; [|exact Ho]; tauto| exact (proj1 (Forall_forall _ _) F2 o Ho)].
  - apply Forall_forall. intros o Ho. apply optb_ok_remove_other; [exact ND| intros q' k ->; eapply OTH; [|exact Ho]; tauto| exact (proj1 (Forall_forall _ _) F3 o Ho)].
Qed.

Lemma data_cells_remove_other : forall m (OW : list block) st q,
  data_cells m OW st -> ~ In q (es_ids st) -> data_cells m (lb_remove q OW) st.
Proof.
  intros m OW st q DC NS. eapply data_cells_OWA; [exact DC|]. intros i p k Hd. apply badr_remove_other.
  intros ->. apply NS. eapply es_ids_data. exact Hd.
Qed.

Lemma ap_preA_permLB : forall Σ st m OW LB LB' E bo sp lo S C F,
  ap_preA Σ st m OW LB E bo sp lo S C F -> Permutation LB LB' -> ap_preA Σ st m OW LB' E bo sp lo S C F.
Proof.
  intros until F. intros (HEAP & REST) P. split; [exact (AHEAP_permLB _ _ _ _ _ HEAP P)| exact REST].
Qed.
End WithRT.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fto_pbs (f : Z) (qb qd : bptr) : list block := [(qb, f + 32, 8); (qd, f + 64, 8)].

Section WithRT2.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).

Lemma fto_open_one : forall Σ1 OW LB m3 f q A n k jst,
  @BnHeapA.AHEAP (push AR f 1) Σ1 OW LB m3 -> @fr_geo (push AR f 1) f 1 ->
  rw_cells ctasegs m3 (shad f) (fto_shadow_pro jst) ->
  f <= A -> A + n <= f + 120 -> 0 < n -> A mod 8 = 0 -> shad A = shad f + Z.of_nat k -> (k + length (ushadow n) <= 12)%nat ->
  firstn (length (ushadow n)) (skipn k (cells_bytes (fto_shadow_pro jst))) = ushadow n ->
  ~ In q (map blk_id (OW ++ LB)) -> (forall b, In b LB -> blk_apart (q, A, n) b) ->
  @BnHeapA.AHEAP (push AR f 1) Σ1 OW ((q, A, n) :: LB) m3.
Proof.
  intros Σ1 OW LB m3 f q A n k jst HEAP GEO FRS A1 A2 Hn A8 Hs Hk Hf Hq AP.
  destruct GEO as (G1 & G2 & G3 & G4 & G5).
  apply (@frame_obj_open (push AR f 1) Σ1 OW LB m3 f 1%nat q A n (or_introl eq_refl) HEAP A1); [change (fs_size 1) with 128; clear - A2; lia | exact Hn | | exact Hq | exact AP].
  apply (acc_of_shadow_cells m3 (shad f) (fto_shadow_pro jst) k A n FRS A8 ltac:(clear - G1 A1; lia) ltac:(clear - Hn; lia) Hs); [| exact Hf].
  pose proof (proj1 (proj1 FRS)) as WF. rewrite (cells_bytes_length _ WF). clear - Hk. cbn. lia.
Qed.

Lemma fto_open_pbs : forall Σ1 OW LB m3 f jst,
  @BnHeapA.AHEAP (push AR f 1) Σ1 OW LB m3 -> (forall b, In b (OW ++ LB) -> off_fr f 1 b) -> @fr_geo (push AR f 1) f 1 ->
  rw_cells ctasegs m3 (shad f) (fto_shadow_pro jst) ->
  exists qb qd, @BnHeapA.AHEAP (push AR f 1) Σ1 OW (fto_pbs f qb qd ++ LB) m3
    /\ ~ In qb (map blk_id (OW ++ LB)) /\ ~ In qd (map blk_id (OW ++ LB)) /\ qb <> qd.
Proof.
  intros Σ1 OW LB m3 f jst HEAP3 FRESH GEO FRS.
  pose proof GEO as (G1 & G2 & G3 & G4 & G5). change (fs_size 1) with 128 in G3, G5.
  assert (F8 : f mod 8 = 0) by (clear - G2; Z.div_mod_to_equations; lia).
  assert (SH : forall i, 0 <= i -> shad (f + i) = shad f + i / 8) by (intros i Hi; exact (shad_aligned_add f i F8 Hi)).
  assert (APL : forall q A n b, f + 32 <= A -> A + n <= f + 120 -> In b LB -> blk_apart (q, A, n) b).
  { intros q A n b HA HA2 Hb. pose proof (FRESH b (in_or_app _ _ _ (or_intror Hb))) as O. unfold off_fr in O. unfold blk_apart. change (fs_size 1) with 128 in O.
    cbn [blk_addr blk_size fst snd]. clear - O HA HA2. lia. }
  destruct (bptr_fresh (map blk_id (OW ++ LB))) as [qd Hqd].
  pose proof (fto_open_one Σ1 OW LB m3 f qd (f + 64) 8 8%nat jst HEAP3 GEO FRS ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
                ltac:(clear - F8; Z.div_mod_to_equations; lia) ltac:(rewrite SH by (clear; lia); clear; cbn; lia) ltac:(clear; cbv; lia) eq_refl Hqd
                ltac:(intros b Hb; apply APL; [clear; lia| clear; lia| exact Hb])) as HEAPd.
  set (LBd := (qd, f + 64, 8) :: LB) in HEAPd.
  destruct (bptr_fresh (map blk_id (OW ++ LBd))) as [qb Hqb].
  pose proof (fto_open_one Σ1 OW LBd m3 f qb (f + 32) 8 4%nat jst HEAPd GEO FRS ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
                ltac:(clear - F8; Z.div_mod_to_equations; lia) ltac:(rewrite SH by (clear; lia); clear; cbn; lia) ltac:(clear; cbv; lia) eq_refl Hqb
                ltac:(intros b [<-|Hb]; [unfold blk_apart; cbn; clear; lia| apply APL; [clear; lia| clear; lia| exact Hb]])) as HEAPb.
  subst LBd. exists qb, qd. split; [exact HEAPb|].
  assert (Hqb' : ~ In qb (map blk_id (OW ++ LB))).
  { intros Hin. apply Hqb. rewrite map_app in Hin |- *. cbn [map blk_id fst snd]. apply in_app_iff in Hin. apply in_or_app. destruct Hin as [Hin|Hin]; [left; exact Hin| right; right; exact Hin]. }
  split; [exact Hqb'|]. split; [exact Hqd|].
  intros E. apply Hqb. rewrite E. rewrite map_app. apply in_or_app. right. left. reflexivity.
Qed.
End WithRT2.
