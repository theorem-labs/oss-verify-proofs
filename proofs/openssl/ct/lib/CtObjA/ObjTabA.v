(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac ZBridge Arr Frame Cells Step Mem Bytes. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim ApObjTab ApObj.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import GDesc Layout RT_iface RT_client_kit D_defs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import LibKitA ARun BnHeapA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require W_obj_lookup ApObjRep.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApRepDefs ApObjRep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation zbytes := CtRepP.W_obj_lookup.zbytes.
Notation obj_bsearch_idx := CtRepP.W_obj_lookup.obj_bsearch_idx.

(* [comment removed for export] *)
Definition A_SO_G : gdesc := (0x506e0, 9598, 11968).
Definition A_SO_LO : Z := 0x506e0.
Definition A_SO_HI : Z := 0x506e0 + 9598.
Lemma A_SO_G_memb : gd_memb A_SO_G = true. Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Definition A_NIDOBJS_G : gdesc := (0x534500, 60160, 75200).
Definition A_OBJOBJS_G : gdesc := (0x6f780, 5408, 6752).
Lemma A_NIDOBJS_G_memb : gd_memb A_NIDOBJS_G = true. Proof. vm_compute. reflexivity. Qed.
Lemma A_OBJOBJS_G_memb : gd_memb A_OBJOBJS_G = true. Proof. vm_compute. reflexivity. Qed.

Lemma ro_cells_recastA : forall m A cs cs',
  ro_cells ctasegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> ro_cells ctasegs m A cs'.
Proof. intros m A cs cs' [Hwf Hb] Hwf' Eb. split; [exact Hwf'| rewrite Eb; exact Hb]. Qed.

Lemma ro_cells_prefixA : forall m A cs1 cs2, ro_cells ctasegs m A (cs1 ++ cs2) -> ro_cells ctasegs m A cs1.
Proof.
  intros m A cs1 cs2 [Hwf Hb]. split.
  - clear Hb. induction cs1 as [|c cs1 IH]; [exact I|]. destruct Hwf as [H1 H2]. split; [exact H1| exact (IH H2)].
  - rewrite cells_bytes_app in Hb. exact (proj1 (proj1 (bytes_at_app _ _ _ _ _) Hb)).
Qed.

Lemma gd_In_memb : forall g, In g GDESC -> gd_memb g = true.
Proof.
  intros g Hg. unfold gd_memb. apply existsb_exists. exists g. split; [exact Hg|].
  unfold gd_eqb. rewrite !Z.eqb_refl. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition obj_entryA (m : mem) (i idx ED : Z) : Prop :=
  let '(nid, content, lnlen) := tab_entry i in
  0 <= idx < NUM_NID /\ 0 <= ED /\ (0 < zlength content -> A_SO_LO <= ED /\ ED + zlength content <= A_SO_HI) /\ 0 <= nid < 2^31 /\
  ro_cells ctasegs m (A_OBJ_OBJS_VA + 4 * i) [C4 (wz idx)] /\
  ro_cells ctasegs m (A_NID_OBJS_VA + 40 * idx + 16) [C4 (wz nid); C4 (wz (zlength content)); C8 (wz ED)] /\
  bytes_at ctasegs m ED (map (Z_to_bv 8) content) /\ Forall (fun c => 0 <= c < 256) content /\
  idx = nid /\ ro_cells ctasegs m (A_NID_OBJS_VA + 40 * idx + 32) [C4 (wz 0)]
  /\ (0 < zlength content -> 0 < nid).
Definition obj_table_okA (m : mem) : Prop := forall i, 0 <= i < NUM_OBJ -> exists idx ED, obj_entryA m i idx ED.

Definition obj_entry_checkA (i : Z) : bool :=
  let '(nid, content, lnlen) := tab_entry i in
  match image_bytes ctasegs (A_NID_OBJS_VA + 40 * nid + 24) 8 with
  | Some db =>
      let ED := le_val (zbytes db) in
      (0 <=? nid) && (nid <? NUM_NID) && (nid <? 2^31)
      && ro_bytes_b ctasegs (A_OBJ_OBJS_VA + 4 * i) (le4 (wz nid))
      && img_bytesb (A_NID_OBJS_VA + 40 * nid + 16) (le4 (wz nid) ++ le4 (wz (zlength content)) ++ le8 (wz ED))
      && img_bytesb (A_NID_OBJS_VA + 40 * nid + 32) (le4 (wz 0))
      && ((zlength content =? 0)
          || ((A_SO_LO <=? ED) && (ED + zlength content <=? A_SO_HI) && (0 <? nid) && ro_bytes_b ctasegs ED (map (Z_to_bv 8) content)))
      && forallb (fun c => (0 <=? c) && (c <? 256)) content
  | None => false
  end.

Fixpoint zrange (k : nat) (z : Z) : list Z := match k with O => [] | S k' => z :: zrange k' (z + 1) end.
Lemma zrange_In : forall k z x, z <= x < z + Z.of_nat k -> In x (zrange k z).
Proof. induction k as [|k IH]; intros z x H; [lia|]. cbn. destruct (Z.eq_dec z x); [left; exact e| right]. apply IH. lia. Qed.

Lemma obj_table_checkA : forallb obj_entry_checkA (zrange 1352 0) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma le_val_zbytes8 : forall db, length db = 8%nat -> 0 <= le_val (zbytes db) < 2^64.
Proof.
  intros db L. pose proof (le_val_range _ (bytes_ok_map db)) as R. unfold zbytes. rewrite length_map, L in R.
  change (256 ^ Z.of_nat 8) with (2^64) in R. exact R.
Qed.

Lemma obj_entry_checkA_sound : forall m i, mem_inv ctasegs m -> relro_pristine m -> 0 <= i < NUM_OBJ -> obj_entry_checkA i = true ->
  exists idx ED, obj_entryA m i idx ED.
Proof.
  intros m i MI R Hi H. unfold obj_entry_checkA in H. unfold obj_entryA.
  destruct (tab_entry i) as [[nid content] lnlen].
  destruct (image_bytes ctasegs (A_NID_OBJS_VA + 40 * nid + 24) 8) as [db|] eqn:DB; [|discriminate].
  set (ED := le_val (zbytes db)) in H.
  repeat (apply andb_prop in H; destruct H as [H ?X]).
  rename X into CR, X0 into CT, X1 into FL, X2 into REC, X3 into OO, X4 into N31, X5 into NH.
  apply Z.leb_le in H. apply Z.ltb_lt in NH. apply Z.ltb_lt in N31.
  pose proof (le_val_zbytes8 db (image_bytes_length _ _ _ _ DB)) as EDR. fold ED in EDR.
  assert (CRF : Forall (fun c => 0 <= c < 256) content).
  { apply Forall_forall. intros c Hc. pose proof (proj1 (forallb_forall _ _) CR c Hc) as X. cbv beta in X.
    apply andb_prop in X. destruct X as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2. lia. }
  assert (ZL : 0 <= zlength content) by (unfold zlength; lia).
  exists nid, ED. unfold NUM_NID, NUM_OBJ, A_OBJ_OBJS_VA, A_NID_OBJS_VA, A_SO_LO, A_SO_HI in *.
  (* [comment removed for export] *)
  assert (CTF : (zlength content = 0) \/ (329440 <= ED /\ ED + zlength content <= 329440 + 9598 /\ 0 < nid /\ ro_bytes_b ctasegs ED (map (Z_to_bv 8) content) = true)).
  { apply Bool.orb_prop in CT. destruct CT as [CT|CT]; [left; apply Z.eqb_eq in CT; exact CT| right].
    repeat (apply andb_prop in CT; destruct CT as [CT ?Y]). apply Z.leb_le in CT. apply Z.leb_le in Y1. apply Z.ltb_lt in Y0. auto. }
  split; [lia|]. split; [lia|]. split; [intros Hz; destruct CTF as [CTF|CTF]; lia|]. split; [lia|].
  split. { pose proof (ro_cells_image ctasegs m _ _ MI OO ltac:(lia) ltac:(cbn; lia)) as X.
           eapply ro_cells_recastA; [exact X| cbn; tauto| cbn [cells_bytes cbytes]; rewrite app_nil_r; reflexivity]. }
  split. { apply (relro_ro_cells m _ _ R); [cbn; tauto| unfold RELRO_LO; lia| unfold RELRO_HI; cbn; lia| cbn [cells_bytes cbytes]; rewrite app_nil_r; exact REC]. }
  split. { destruct CTF as [CTF|(C1 & C2 & C3 & C4)].
           - assert (content = []) as -> by (destruct content; [reflexivity| unfold zlength in CTF; cbn in CTF; lia]). apply bytes_at_nil. clear - EDR. lia.
           - pose proof (ro_cells_image ctasegs m _ _ MI C4 ltac:(lia) ltac:(rewrite length_map; unfold zlength in C2; lia)) as [_ X].
             cbn [cells_bytes cbytes] in X. rewrite app_nil_r in X. exact X. }
  split; [exact CRF|]. split; [reflexivity|].
  split. { apply (relro_ro_cells m _ _ R); [cbn; tauto| unfold RELRO_LO; lia| unfold RELRO_HI; cbn; lia| cbn [cells_bytes cbytes]; rewrite app_nil_r; exact FL]. }
  intros Hz. destruct CTF as [CTF|CTF]; lia.
Qed.

Theorem obj_table_okA_intro : forall m, mem_inv ctasegs m -> relro_pristine m -> obj_table_okA m.
Proof.
  intros m MI R i Hi. apply (obj_entry_checkA_sound m i MI R Hi).
  exact (proj1 (forallb_forall _ _) obj_table_checkA i (zrange_In 1352 0 i ltac:(unfold NUM_OBJ in Hi; lia))).
Qed.

(* [comment removed for export] *)
Lemma obj_table_okA_heap : forall (AR : ARun) Σ OW LB m, @BnHeapA.AHEAP AR Σ OW LB m -> mem_inv ctasegs m -> obj_table_okA m.
Proof. intros AR Σ OW LB m H MI. exact (obj_table_okA_intro m MI (af_relro _ (@ar_AF AR) Σ m (@AH_art AR _ _ _ _ H))). Qed.

(* [comment removed for export] *)
Lemma obj_lookup_hit_factsA : forall m kb nid lnlen,
  obj_table_okA m -> obj_lookup (zbytes kb) = Some (nid, lnlen) -> (0 < length kb)%nat ->
  0 < nid < NUM_NID /\ static_obj_ok nid lnlen
  /\ exists i content ED, obj_bsearch_idx OBJ_BSEARCH_FUEL (zbytes kb) 0 NUM_OBJ = Some i /\ tab_entry i = (nid, content, lnlen) /\ obj_entryA m i nid ED.
Proof.
  intros m kb nid lnlen TOK LK KL. destruct (CtRepP.W_obj_lookup.obj_lookup_idx _ _ _ LK) as (i & BI & NID & LNL & IR).
  pose proof (CtRepP.W_obj_lookup.obj_bsearch_idx_hit _ _ _ _ _ BI) as HC. apply CtRepP.W_obj_lookup.obj_cmp_zero_len in HC.
  rewrite CtRepP.W_obj_lookup.zlength_zbytes in HC.
  destruct (TOK i IR) as (idx & ED & HE). pose proof HE as HE0. unfold obj_entryA in HE.
  destruct (tab_entry i) as [[enid content] elnlen] eqn:TE. cbn [fst snd] in NID, LNL, HC. subst enid elnlen.
  destruct HE as (IDX & ED0 & EDL & NIDR & RO1 & RO2 & HEB & CR & INID & ROF & NZ). subst idx.
  split; [split; [apply NZ; lia| lia]|].
  split. { exists i, content. split; [exact IR|]. split; [exact TE|]. intros E0. subst content. unfold zlength in HC. cbn in HC. lia. }
  exists i, content, ED. split; [exact BI|]. split; [exact TE|]. exact HE0.
Qed.

(* [comment removed for export] *)
Lemma static_obj_cellsA : forall m nid lnlen,
  obj_table_okA m -> static_obj_ok nid lnlen -> 0 < nid ->
  exists content ED,
    ro_cells ctasegs m (A_NID_OBJS_VA + 40 * nid + 16) [C4 (wz nid); C4 (wz (zlength content)); C8 (wz ED)]
    /\ ro_cells ctasegs m (A_NID_OBJS_VA + 40 * nid + 32) [C4 (wz 0)]
    /\ bytes_at ctasegs m ED (map (Z_to_bv 8) content) /\ Forall (fun c => 0 <= c < 256) content
    /\ 0 <= ED /\ (0 < zlength content -> A_SO_LO <= ED /\ ED + zlength content <= A_SO_HI).
Proof.
  intros m nid lnlen TOK (i & content & Hi & TE & _) Hn.
  destruct (TOK i Hi) as (idx & ED & HE). unfold obj_entryA in HE. rewrite TE in HE.
  destruct HE as (IDX & ED0 & EDL & NIDR & RO1 & RO2 & HEB & CR & INID & ROF & NZ). subst idx.
  exists content, ED. split; [exact RO2|]. split; [exact ROF|]. split; [exact HEB|]. split; [exact CR|]. split; [exact ED0| exact EDL].
Qed.

(* [comment removed for export] *)
Lemma static_obj_nid_cellA : forall m nid lnlen,
  obj_table_okA m -> static_obj_ok nid lnlen -> ro_cells ctasegs m (A_NID_OBJS_VA + 40 * nid + 16) [C4 (wz nid)].
Proof.
  intros m nid lnlen TOK (i & content & Hi & TE & _).
  destruct (TOK i Hi) as (idx & ED & HE). unfold obj_entryA in HE. rewrite TE in HE.
  destruct HE as (IDX & _ & _ & _ & _ & RO2 & _ & _ & INID & _). subst idx.
  lazymatch type of RO2 with ro_cells _ _ _ [?c1; ?c2; ?c3] => change [c1; c2; c3] with ([c1] ++ [c2; c3]) in RO2 end.
  exact (ro_cells_prefixA _ _ _ _ RO2).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition gd_find (a : Z) : option gdesc := find (fun g => gd_beg g =? a) GDESC.

Definition obj_name_entryA (m : mem) (nid lnlen : Z) : Prop :=
  exists (LN ED : Z) (g : gdesc) (lnb slack : list byte),
    ro_cells ctasegs m (A_NID_OBJS_VA + 40 * nid + 8) [C8 (wz LN)] /\ 0x10000 <= LN /\ LN + lnlen + 8 <= A_NID_OBJS_VA /\
    gd_memb g = true /\ gd_beg g = LN /\ lnlen + 1 <= gd_size g /\
    bytes_at ctasegs m LN (lnb ++ Z_to_bv 8 0 :: slack) /\ Z.of_nat (length lnb) = lnlen /\ ~ In (Z_to_bv 8 0) lnb /\ length slack = 7%nat /\
    ro_cells ctasegs m (A_NID_OBJS_VA + 40 * nid + 24) [C8 (wz ED)] /\ 0 < ED < 2^64.

Definition obj_name_checkA (i : Z) : bool :=
  let '(nid, content, lnlen) := tab_entry i in
  (zlength content =? 0) ||
  match image_bytes ctasegs (A_NID_OBJS_VA + 40 * nid + 8) 8, image_bytes ctasegs (A_NID_OBJS_VA + 40 * nid + 24) 8 with
  | Some lb, Some db =>
      let LN := le_val (zbytes lb) in
      let ED := le_val (zbytes db) in
      (0 <=? lnlen) && (0x10000 <=? LN) && (LN + lnlen + 8 <=? A_NID_OBJS_VA) && (0 <? ED) && (0 <=? nid) && (nid <? NUM_NID)
      && img_bytesb (A_NID_OBJS_VA + 40 * nid + 8) (le8 (wz LN)) && img_bytesb (A_NID_OBJS_VA + 40 * nid + 24) (le8 (wz ED))
      && match gd_find LN with Some g => (lnlen + 1 <=? gd_size g) | None => false end
      && match image_bytes ctasegs LN (Z.to_nat (lnlen + 8)) with
         | Some sb => ro_bytes_b ctasegs LN sb
                      && forallb (fun b : byte => negb (bv_eqb b (Z_to_bv 8 0))) (firstn (Z.to_nat lnlen) sb)
                      && match nth_error sb (Z.to_nat lnlen) with Some z => bv_eqb z (Z_to_bv 8 0) | None => false end
         | None => false
         end
  | _, _ => false
  end.

Lemma obj_names_checkA : forallb obj_name_checkA (zrange 1352 0) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma obj_name_checkA_sound : forall m i, mem_inv ctasegs m -> relro_pristine m -> 0 <= i < NUM_OBJ -> obj_name_checkA i = true ->
  let '(nid, content, lnlen) := tab_entry i in content <> [] -> obj_name_entryA m nid lnlen.
Proof.
  intros m i MI R I0 H. unfold obj_name_checkA in H.
  destruct (tab_entry i) as [[nid content] lnlen]. intros NE.
  apply Bool.orb_prop in H. destruct H as [H|H]; [apply Z.eqb_eq in H; exfalso; apply NE; destruct content; [reflexivity| unfold zlength in H; cbn in H; lia]|].
  destruct (image_bytes ctasegs (A_NID_OBJS_VA + 40 * nid + 8) 8) as [lb|] eqn:LB; [|discriminate].
  destruct (image_bytes ctasegs (A_NID_OBJS_VA + 40 * nid + 24) 8) as [db|] eqn:DB; [|discriminate].
  set (LN := le_val (zbytes lb)) in H. set (ED := le_val (zbytes db)) in H.
  repeat (apply andb_prop in H; destruct H as [H ?X]).
  rename X into SM, X0 into GF, X1 into EDB, X2 into ELB, X3 into NIDH, X4 into NID0, X5 into ED0, X6 into LNH, X7 into LN0.
  apply Z.leb_le in H. apply Z.leb_le in LN0. apply Z.leb_le in LNH. apply Z.ltb_lt in ED0. apply Z.leb_le in NID0. apply Z.ltb_lt in NIDH.
  destruct (gd_find LN) as [g|] eqn:GFE; [|discriminate]. apply Z.leb_le in GF.
  unfold gd_find in GFE. apply find_some in GFE. destruct GFE as [GIN GBE]. apply Z.eqb_eq in GBE.
  destruct (image_bytes ctasegs LN (Z.to_nat (lnlen + 8))) as [sb|] eqn:SB; [|discriminate].
  repeat (apply andb_prop in SM; destruct SM as [SM ?Y]). rename Y into NUL, Y0 into NZ.
  pose proof (image_bytes_length _ _ _ _ SB) as SBL.
  destruct (nth_error sb (Z.to_nat lnlen)) as [z|] eqn:NZE; [|discriminate]. unfold bv_eqb in NUL. apply Z.eqb_eq in NUL. apply bv_eq in NUL. subst z.
  pose proof (le_val_zbytes8 db (image_bytes_length _ _ _ _ DB)) as EDR. fold ED in EDR.
  unfold obj_name_entryA. unfold NUM_NID, NUM_OBJ, A_NID_OBJS_VA in *.
  exists LN, ED, g, (firstn (Z.to_nat lnlen) sb), (skipn (Z.to_nat lnlen + 1) sb).
  destruct (nth_error_split sb (Z.to_nat lnlen) _ NZE) as (l1 & l2 & SPLIT & L1).
  assert (F1 : firstn (Z.to_nat lnlen) sb = l1) by (rewrite SPLIT, <- L1; rewrite firstn_app, firstn_all, Nat.sub_diag; cbn; rewrite app_nil_r; reflexivity).
  assert (S1 : skipn (Z.to_nat lnlen + 1) sb = l2).
  { rewrite SPLIT, <- L1, skipn_app. replace (length l1 + 1 - length l1)%nat with 1%nat by lia. rewrite skipn_all2 by lia. reflexivity. }
  rewrite F1, S1. rewrite F1 in NZ.
  split. { apply (relro_ro_cells m _ _ R); [cbn; tauto| unfold RELRO_LO; lia| unfold RELRO_HI; cbn; lia| cbn [cells_bytes cbytes]; rewrite app_nil_r; exact ELB]. }
  split; [exact LN0|]. split; [exact LNH|].
  split; [exact (gd_In_memb g GIN)|]. split; [exact GBE|]. split; [exact GF|].
  split. { pose proof (ro_cells_image ctasegs m LN sb MI SM ltac:(lia) ltac:(rewrite SBL; lia)) as [_ HB].
           cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB. rewrite SPLIT in HB. exact HB. }
  split; [rewrite L1; lia|].
  split. { intros HIn. apply (proj1 (forallb_forall _ _) NZ) in HIn. cbv beta in HIn. unfold bv_eqb in HIn. rewrite Z.eqb_refl in HIn. discriminate. }
  split; [rewrite <- S1, length_skipn, SBL; lia|].
  split. { apply (relro_ro_cells m _ _ R); [cbn; tauto| unfold RELRO_LO; lia| unfold RELRO_HI; cbn; lia| cbn [cells_bytes cbytes]; rewrite app_nil_r; exact EDB]. }
  exact (conj ED0 (proj2 EDR)).
Qed.

(* [comment removed for export] *)
Lemma static_obj_namesA : forall (AR : ARun) Σ OW LB m nid lnlen,
  @BnHeapA.AHEAP AR Σ OW LB m -> mem_inv ctasegs m -> static_obj_ok nid lnlen -> obj_name_entryA m nid lnlen.
Proof.
  intros AR Σ OW LB m nid lnlen HEAP MI (i & content & Hi & TE & NE).
  pose proof (proj1 (forallb_forall _ _) obj_names_checkA i ltac:(apply zrange_In; unfold NUM_OBJ in Hi; lia)) as C.
  pose proof (obj_name_checkA_sound m i MI (af_relro _ (@ar_AF AR) Σ m (@AH_art AR _ _ _ _ HEAP)) Hi C) as S. rewrite TE in S. exact (S NE).
Qed.
