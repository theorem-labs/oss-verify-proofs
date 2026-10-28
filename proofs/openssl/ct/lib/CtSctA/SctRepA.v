(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Prog CtSizes CtWire CtModel.
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import LibKitA ARun BnHeapA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require ApErrKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctP Require Import SctDefs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctP Require W_sct_list_free SctRep W_sk_leaves SctStmt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation lremove := CtRepP.ApErrKit.lremove.
Notation osz32 := CtSctP.W_sct_list_free.osz32.
Notation oblk := CtSctP.W_sct_list_free.oblk.
Notation sct_blocks := CtSctP.W_sct_list_free.sct_blocks.
Notation scts_blocks := CtSctP.W_sct_list_free.scts_blocks.
Notation remove_sct := CtSctP.W_sct_list_free.remove_sct.
Notation remove_scts := CtSctP.W_sct_list_free.remove_scts.
Notation sct_cells := CtSctP.SctRep.sct_cells.
Notation olen := CtSctP.SctRep.olen.
Notation ptrw := CtSctP.W_sk_leaves.ptrw.
Notation data_block := CtSctP.W_sk_leaves.data_block.
Notation dblk := CtSctP.W_sk_leaves.dblk.
Notation sk_blocks := CtSctP.SctStmt.sk_blocks.

(* [comment removed for export] *)
Definition SK_SCT_CMP_THUNK_A : Z := 0x336b00.
Definition SK_SCT_COPY_THUNK_A : Z := 0x336b2c.
Definition SK_SCT_FREEFUNC_THUNK_A : Z := 0x336b54.   (* [comment removed for export] *)
Definition sk_cells (adr : bptr -> Z) (k : skr bptr) (sorted : Z) : list cell :=
  [C4 (wz (sk_num k)); C4 (wz 0); C8 (wz (optr adr (sk_data k))); C4 (wz sorted); C4 (wz (olen (sk_data k)));
   C8 (wz 0); C8 (wz SK_SCT_CMP_THUNK_A); C8 (wz SK_SCT_FREEFUNC_THUNK_A); C8 (wz SK_SCT_COPY_THUNK_A)].

Local Notation mem := (word -> option byte).

Section WithCeiling. Context {CE__ : Ceiling.Ceiling}.

(* [comment removed for export] *)
Lemma rw_cells_app : forall segs (m : mem) A cs1 cs2,
  rw_cells segs m A (cs1 ++ cs2) <-> rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros segs m A cs1 cs2. unfold rw_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, bytes_at_app.
  split.
  - intros [[[W1 W2] [B1 B2]] WR].
    pose proof (cells_bytes_length cs1 W1) as L1. rewrite L1 in B2.
    destruct WR as (HA & HN & HW).
    split; [split; [split; assumption|] | split; [split; assumption|]].
    + split; [lia|]. split; [lia|]. intros i Hi. apply HW. lia.
    + split; [lia|]. split; [lia|]. intros i Hi.
      replace (A + Z.of_nat (cells_size cs1) + i)%Z with (A + (Z.of_nat (cells_size cs1) + i))%Z by lia. apply HW. lia.
  - intros [[[W1 B1] (HA1 & HN1 & HW1)] [[W2 B2] (HA2 & HN2 & HW2)]].
    pose proof (cells_bytes_length cs1 W1) as L1.
    split; [split; [split; assumption|] |].
    + split; [exact B1|]. rewrite L1. exact B2.
    + split; [lia|]. split; [lia|]. intros i Hi. destruct (Z_lt_dec i (Z.of_nat (cells_size cs1))).
      * apply HW1. lia.
      * replace (A + i)%Z with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1)))%Z by lia. apply HW2. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sct_ptr_cellsA (m : mem) (adr : bptr -> Z) (s : sctr bptr) : Prop :=
  let A := adr (sc_blk s) in
  ro_cells ctasegs m (A + SCTO_SCT) [C8 (wz (optr adr (sc_blob s)))]
  /\ ro_cells ctasegs m (A + SCTO_LOG_ID) [C8 (wz (optr adr (osz32 (sc_logid s))))]
  /\ ro_cells ctasegs m (A + SCTO_EXT) [C8 (wz (optr adr (sc_ext s)))]
  /\ ro_cells ctasegs m (A + SCTO_SIG) [C8 (wz (optr adr (sc_sig s)))].

(* [comment removed for export] *)
Definition arr_repA (m : mem) (L : list block) (adr : bptr -> Z) (o : option (bptr * Z)) : Prop :=
  match o with
  | Some (q, n) => 0 < n /\ In (q, adr q, n) L /\ exists bs, rw_cells ctasegs m (adr q) [CB (Z.to_nat n) bs]
  | None => True
  end.

(* [comment removed for export] *)
Definition sct_repA (m : mem) (L : list block) (adr : bptr -> Z) (x : sctr bptr) : Prop :=
  In (sc_blk x, adr (sc_blk x), SCT_SIZE) L /\ adr (sc_blk x) mod 16 = 0
  /\ rw_cells ctasegs m (adr (sc_blk x)) (sct_cells adr x (-1) 0)
  /\ arr_repA m L adr (osz32 (sc_logid x)) /\ arr_repA m L adr (sc_ext x) /\ arr_repA m L adr (sc_sig x) /\ arr_repA m L adr (sc_blob x)
  /\ List.NoDup (map blk_id (sct_blocks adr x))
  /\ (sc_version x = -1 \/ 0 <= sc_version x < 256) /\ (sc_version x = 0 -> sct_nid x <> NID_undef)
  /\ 0 <= sc_hash x < 256 /\ 0 <= sc_sigalg x < 256 /\ 0 <= sc_ts x < 2^64
  /\ sc_extlen x = olen (sc_ext x)
  /\ olen (sc_ext x) <= MAX_SCT_SIZE /\ olen (sc_sig x) <= MAX_SCT_SIZE /\ olen (sc_blob x) <= MAX_SCT_SIZE.

Definition scts_repA (m : mem) (L : list block) (adr : bptr -> Z) (l : list (sctr bptr)) : Prop :=
  Forall (sct_repA m L adr) l /\ List.NoDup (map blk_id (scts_blocks adr l)).

Lemma sct_repA_blocks_in : forall m L adr x, sct_repA m L adr x -> forall b, In b (sct_blocks adr x) -> In b L.
Proof.
  intros m L adr x (H1 & _ & _ & H3 & H4 & H5 & H6 & _) b Hb. unfold CtSctP.W_sct_list_free.sct_blocks in Hb. rewrite !in_app_iff in Hb.
  assert (AR : forall o, arr_repA m L adr o -> In b (oblk adr o) -> In b L).
  { intros [[q n]|] H Hin; cbn in *; [| destruct Hin]. destruct Hin as [<-|[]]. exact (proj1 (proj2 H)). }
  destruct Hb as [Hb|[Hb|[Hb|[Hb|[<-|[]]]]]]; [exact (AR _ H3 Hb)| exact (AR _ H4 Hb)| exact (AR _ H5 Hb)| exact (AR _ H6 Hb)| exact H1].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition st_cellsA (m : mem) (SA num D : Z) : Prop :=
  ro_cells ctasegs m SA [C4 (wz num)] /\ ro_cells ctasegs m (SA + SKO_DATA) [C8 (wz D)] /\ ro_cells ctasegs m (SA + SKO_FREE_THUNK) [C8 (wz SK_SCT_FREEFUNC_THUNK_A)].

(* [comment removed for export] *)
Fixpoint sk_data_cellsA (m : mem) (adr : bptr -> Z) (D i : Z) (l : list (sctr bptr)) : Prop :=
  match l with [] => True | s :: t => ro_cells ctasegs m (D + 8 * i) [C8 (wz (adr (sc_blk s)))] /\ sk_data_cellsA m adr D (i + 1) t end.

(* [comment removed for export] *)
Definition sk_repA (m : mem) (L : list block) (adr : bptr -> Z) (k : skr bptr) : Prop :=
  (In (sk_blk k, adr (sk_blk k), STACK_SIZE) L /\ adr (sk_blk k) mod 16 = 0)
  /\ (exists sorted, 0 <= sorted <= 1 /\ rw_cells ctasegs m (adr (sk_blk k)) (sk_cells adr k sorted))
  /\ match sk_data k with
     | Some (q, na) => In (q, adr q, 8 * na) L /\ adr q mod 16 = 0 /\ sk_num k <= na /\ SK_MIN_NODES <= na < 2^23
                       /\ exists jb, Z.of_nat (length jb) = 8 * (na - sk_num k) /\ rw_cells ctasegs m (adr q) (data_block adr (sk_items k) jb)
     | None => sk_items k = []
     end
  /\ Forall (sct_repA m L adr) (sk_items k)
  /\ List.NoDup (map blk_id (scts_blocks adr (sk_items k) ++ dblk adr (sk_data k) ++ [(sk_blk k, adr (sk_blk k), STACK_SIZE)])).

(* [comment removed for export] *)
Lemma sk_repA_scts : forall m L adr k, sk_repA m L adr k -> scts_repA m L adr (sk_items k).
Proof.
  intros m L adr k (_ & _ & _ & HF & ND). split; [exact HF|]. rewrite map_app in ND. exact (proj2 (proj2 (CtSctP.W_sct_list_free.NoDup_app_split _ _ ND))).
Qed.

Lemma sk_repA_blocks_in : forall m L adr k b, sk_repA m L adr k -> In b (sk_blocks adr k) -> In b L.
Proof.
  intros m L adr k b ((HIN & _) & _ & HD & HF & _) Hb. unfold CtSctP.SctStmt.sk_blocks in Hb. rewrite !in_app_iff in Hb.
  assert (ITEMS : forall l, Forall (sct_repA m L adr) l -> In b (scts_blocks adr l) -> In b L).
  { intros l HFl. induction HFl as [|x t Hx HFt IH]; intros Hbl; [destruct Hbl|]. cbn in Hbl. apply in_app_iff in Hbl.
    destruct Hbl as [Hbl|Hbl]; [exact (sct_repA_blocks_in _ _ _ _ Hx _ Hbl)| exact (IH Hbl)]. }
  destruct Hb as [Hb|[Hb|Hb]].
  - exact (ITEMS _ HF Hb).
  - destruct (sk_data k) as [[q na]|]; cbn in Hb; [| destruct Hb]. destruct Hb as [<-|[]]. exact (proj1 HD).
  - destruct Hb as [<-|[]]. exact HIN.
Qed.

Lemma sk_data_cellsA_of_block : forall m adr D i items junk,
  rw_cells ctasegs m (D + 8 * i) (data_block adr items junk) -> sk_data_cellsA m adr D i items.
Proof.
  intros m adr D i items junk. revert i. induction items as [|x t IH]; intros i H; cbn; [exact I|].
  unfold CtSctP.W_sk_leaves.data_block in H. cbn [map app] in H.
  change (C8 (ptrw adr x) :: map C8 (map (ptrw adr) t) ++ [CB (length junk) junk]) with ([C8 (ptrw adr x)] ++ data_block adr t junk) in H.
  apply rw_cells_app in H. destruct H as [H1 H2]. split; [exact (proj1 H1)|]. apply IH. cbn [cells_size csize Nat.add] in H2.
  replace (D + 8 * (i + 1)) with (D + 8 * i + Z.of_nat 8) by lia. exact H2.
Qed.

(* [comment removed for export] *)
Lemma sk_repA_free_view : forall m L adr k, sk_repA m L adr k ->
  st_cellsA m (adr (sk_blk k)) (sk_num k) (optr adr (sk_data k))
  /\ In (sk_blk k, adr (sk_blk k), STACK_SIZE) L
  /\ match sk_data k with Some (q, na) => In (q, adr q, 8 * na) L /\ sk_num k <= na | None => sk_items k = [] end
  /\ sk_data_cellsA m adr (optr adr (sk_data k)) 0 (sk_items k)
  /\ Forall (fun b => In b L) (scts_blocks adr (sk_items k))
  /\ List.NoDup (map blk_id (scts_blocks adr (sk_items k) ++ oblk adr (sk_data k) ++ [(sk_blk k, adr (sk_blk k), STACK_SIZE)])).
Proof.
  intros m L adr k SK. pose proof SK as ((HIN & AL) & (sorted & SR & HC) & HD & HF & ND).
  split.
  { unfold st_cellsA, SKO_DATA, SKO_FREE_THUNK. unfold sk_cells in HC.
    lazymatch type of HC with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?rest) =>
      change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: rest) with ([c0] ++ [c1] ++ [c2] ++ [c3; c4; c5; c6] ++ [c7] ++ rest) in HC end.
    apply rw_cells_app in HC. destruct HC as [H0 HC]. apply rw_cells_app in HC. destruct HC as [_ HC]. apply rw_cells_app in HC. destruct HC as [H2 HC].
    apply rw_cells_app in HC. destruct HC as [_ HC]. apply rw_cells_app in HC. destruct HC as [H7 _]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add] in *.
    rewrite <- ?Z.add_assoc in *. cbn [Z.add Pos.add Pos.succ] in *.
    split; [exact (proj1 H0)|]. split; [exact (proj1 H2)| exact (proj1 H7)]. }
  split; [exact HIN|].
  split. { destruct (sk_data k) as [[q na]|]; [| exact HD]. destruct HD as (H1 & _ & H2 & _ & _). split; [exact H1| exact H2]. }
  split. { destruct (sk_data k) as [[q na]|]; cbn [optr].
           - destruct HD as (_ & _ & _ & _ & junk & _ & HB). eapply sk_data_cellsA_of_block. rewrite Z.mul_0_r, Z.add_0_r. exact HB.
           - rewrite HD. exact I. }
  split.
  { apply Forall_forall. intros b Hb. eapply sk_repA_blocks_in; [exact SK|]. unfold CtSctP.SctStmt.sk_blocks. apply in_app_iff. left. exact Hb. }
  destruct (sk_data k) as [[q na]|]; cbn [CtSctP.W_sk_leaves.dblk CtSctP.W_sct_list_free.oblk] in ND |- *; [| exact ND]. revert ND. rewrite !map_app. cbn [map blk_id fst snd app]. intros ND. exact ND.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithRT.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation FR := (@ar_FR AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)
Definition lbokA (b : block) : Prop := blk_okA b /\ ~ pb_in b.

Lemma lb_remove_perm : forall p (L L' : list block), Permutation L L' -> Permutation (lb_remove p L) (lb_remove p L').
Proof.
  intros p L L' P. induction P as [|x l l' P IH|x y l|l l' l'' P1 IH1 P2 IH2].
  - reflexivity.
  - rewrite !lb_remove_cons. destruct (bptr_eqb (blk_id x) p); [exact IH | apply perm_skip; exact IH].
  - rewrite !lb_remove_cons. destruct (bptr_eqb (blk_id y) p), (bptr_eqb (blk_id x) p); try reflexivity. apply perm_swap.
  - eapply Permutation_trans; [exact IH1 | exact IH2].
Qed.

Lemma not_pb_in_of_live : forall Σ OW LB m b, AHEAP Σ OW LB m -> In (blk_an b) (rt_live RT Σ) -> 0 < blk_size b -> ~ pb_in b.
Proof.
  intros Σ OW LB m b H HL POS (f & k & Hin & H1 & H2).
  destruct (AH_fr_range _ _ _ _ f k H Hin) as (_ & _ & _ & _ & APART). pose proof (fs_size_div8 k) as [_ D8].
  destruct (APART (blk_addr b) (blk_size b) HL) as [X|X]; lia.
Qed.

(* [comment removed for export] *)
Lemma AH_release : forall Σ OW LB m b, AHEAP Σ (b :: OW) LB m -> AHEAP Σ OW (b :: LB) m /\ lbokA b.
Proof.
  intros Σ OW LB m b H. pose proof H as (HA & HS & HFr & (FW & PB & LBr & P1 & P2 & F & AP) & ND & HF1 & HF2).
  apply Forall_cons_iff in HF1 as [OKb HF1].
  assert (LIVE : In (blk_an b) (rt_live RT Σ)).
  { eapply Permutation_in; [symmetry; exact P2|]. cbn [app map]. left. reflexivity. }
  assert (NPB : ~ pb_in b) by (eapply not_pb_in_of_live; [exact H | exact LIVE | exact (proj1 (proj2 OKb))]).
  split; [| split; [exact OKb | exact NPB]].
  split; [exact HA|]. split; [exact HS|]. split; [exact HFr|].
  split. { split; [exact FW|]. exists PB, (b :: LBr). split; [| split; [| split; [exact F | exact AP]]].
           - eapply Permutation_trans; [apply perm_skip; exact P1|]. apply Permutation_middle.
           - eapply Permutation_trans; [exact P2|]. cbn [app]. rewrite !map_app. cbn [map]. rewrite map_app. apply Permutation_middle. }
  split. { eapply nodup_ids_perm; [| exact ND]. cbn [app]. apply Permutation_middle. }
  split; [exact HF1|]. constructor; [exact (proj1 (proj2 OKb)) | exact HF2].
Qed.

(* [comment removed for export] *)
Lemma AH_adopt : forall Σ OW LB m b, AHEAP Σ OW LB m -> In b LB -> lbokA b -> AHEAP Σ (b :: OW) (lb_remove (blk_id b) LB) m.
Proof.
  intros Σ OW LB m b H Hb [OKb NPB]. pose proof H as (HA & HS & HFr & (FW & PB & LBr & P1 & P2 & F & AP) & ND & HF1 & HF2).
  assert (NDL : List.NoDup (map blk_id LB)) by (rewrite map_app in ND; exact (nodup_app_r _ _ ND)).
  assert (HbL : In b LBr).
  { apply (Permutation_in _ P1) in Hb. apply in_app_or in Hb as [Hb|Hb]; [| exact Hb]. exfalso. apply NPB.
    exact (proj1 (proj1 (Forall_forall _ _) F b Hb)). }
  destruct (in_split _ _ HbL) as (L1 & L2 & ->).
  assert (PL : Permutation LB (b :: PB ++ L1 ++ L2)).
  { eapply Permutation_trans; [exact P1|]. symmetry. rewrite (app_assoc PB L1 L2), (app_assoc PB L1 (b :: L2)). apply Permutation_middle. }
  assert (NDb : List.NoDup (map blk_id (b :: PB ++ L1 ++ L2))) by (eapply nodup_ids_perm; [exact PL | exact NDL]).
  assert (RM : Permutation (lb_remove (blk_id b) LB) (PB ++ L1 ++ L2)).
  { eapply Permutation_trans; [apply lb_remove_perm; exact PL|]. rewrite (lb_remove_head _ _ NDb). reflexivity. }
  split; [exact HA|]. split; [exact HS|]. split; [exact HFr|].
  split. { split; [exact FW|]. exists PB, (L1 ++ L2). split; [exact RM|]. split; [| split; [exact F | exact AP]].
           eapply Permutation_trans; [exact P2|]. rewrite !map_app. cbn [map app]. symmetry.
           rewrite (app_assoc (map blk_an OW) (map blk_an L1) (map blk_an L2)), (app_assoc (map blk_an OW) (map blk_an L1) (blk_an b :: map blk_an L2)). apply Permutation_middle. }
  split. { eapply nodup_ids_perm; [| exact ND]. cbn [app].
           eapply Permutation_trans; [apply Permutation_app_head; eapply Permutation_trans; [exact PL| apply perm_skip; symmetry; exact RM] | ]. symmetry. apply Permutation_middle. }
  split; [constructor; [exact OKb | exact HF1]|].
  apply Forall_forall. intros x Hx. apply lb_remove_incl in Hx. exact (proj1 (Forall_forall _ _) HF2 x Hx).
Qed.

(* [comment removed for export] *)
Lemma AH_release_list : forall Σ NEW OW LB m, AHEAP Σ (NEW ++ OW) LB m -> AHEAP Σ OW (NEW ++ LB) m /\ Forall lbokA NEW.
Proof.
  intros Σ NEW. induction NEW as [|b NEW IH]; intros OW LB m H; [split; [exact H | constructor]|].
  cbn [app] in H. destruct (AH_release _ _ _ _ _ H) as [H1 OK1].
  (* [comment removed for export] *)
  assert (H2 : AHEAP Σ (NEW ++ OW) (b :: LB) m) by exact H1.
  destruct (IH _ _ _ H2) as [H3 OK3].
  split; [| constructor; [exact OK1 | exact OK3]].
  (* [comment removed for export] *)
  pose proof H3 as (HA & HS & HFr & (FW & PB & LBr & P1 & P2 & F & AP) & ND & HF1 & HF2).
  split; [exact HA|]. split; [exact HS|]. split; [exact HFr|].
  split. { split; [exact FW|]. exists PB, LBr. split; [| split; [exact P2 | split; [exact F | exact AP]]].
           eapply Permutation_trans; [| exact P1]. cbn [app]. apply Permutation_middle. }
  split. { eapply nodup_ids_perm; [| exact ND]. apply Permutation_app_head. symmetry. cbn [app]. apply Permutation_middle. }
  split; [exact HF1|]. apply Forall_forall. intros x Hx. apply (proj1 (Forall_forall _ _) HF2). eapply Permutation_in; [| exact Hx]. cbn [app]. apply Permutation_middle.
Qed.

Lemma AH_adopt_list : forall Σ NEW OW LB m, AHEAP Σ OW (NEW ++ LB) m -> Forall lbokA NEW -> AHEAP Σ (NEW ++ OW) LB m.
Proof.
  intros Σ NEW. induction NEW as [|b NEW IH]; intros OW LB m H OK; [exact H|].
  apply Forall_cons_iff in OK as [OKb OK]. cbn [app] in H.
  pose proof (AH_adopt _ _ _ _ b H (or_introl eq_refl) OKb) as H1.
  rewrite (lb_remove_head b (NEW ++ LB)) in H1; [| pose proof (AH_nodup _ _ _ _ H) as NDX; rewrite map_app in NDX; exact (nodup_app_r _ _ NDX)].
  (* [comment removed for export] *)
  pose proof (IH (b :: OW) LB m H1 OK) as H2.
  pose proof H2 as (HA & HS & HFr & (FW & PB & LBr & P1 & P2 & F & AP) & ND & HF1 & HF2).
  split; [exact HA|]. split; [exact HS|]. split; [exact HFr|].
  split. { split; [exact FW|]. exists PB, LBr. split; [exact P1|]. split; [| split; [exact F | exact AP]].
           eapply Permutation_trans; [exact P2|]. apply Permutation_map. apply Permutation_app_tail. symmetry. cbn [app]. apply Permutation_middle. }
  split. { eapply nodup_ids_perm; [| exact ND]. apply Permutation_app_tail. symmetry. cbn [app]. apply Permutation_middle. }
  split; [| exact HF2]. apply Forall_forall. intros x Hx. apply (proj1 (Forall_forall _ _) HF1). eapply Permutation_in; [| exact Hx]. cbn [app]. apply Permutation_middle.
Qed.
End WithRT.
End WithCeiling.
