(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.CJ.Spec Require Import KInvS8 MI_InvS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Spec Require Import MI_Kit MI_Arith.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.CJ.Spec Require Import MI_ListS8 MI_ExtS8 MI_Ext2S8 MI_GeomS8 KStepS8 MI_WAMetaS8 MI_Pres4S8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.CJ.Lib Require Import DecodeS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.CJ.Bridge Require Import BrResS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.Heap Require Import HeTreeS8 HeAbsS8 HeWNtfS8.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section HMMETA.
Context {RUNp : RunP}.

Definition regsum (f : region -> Z) (st : mstate) : Z := zsum (map (fun kr : N * region => f (snd kr)) (map_to_list (s_regions st))).

Lemma zsum_cons x l : zsum (x :: l) = x + zsum l. Proof. reflexivity. Qed.

Lemma regsum_insert_fresh f st st' rid r : s_regions st !! rid = None -> s_regions st' = <[rid := r]> (s_regions st) ->
  regsum f st' = regsum f st + f r.
Proof.
  intros N E. unfold regsum. rewrite E. rewrite (zsum_perm _ _ (Permutation_map _ (map_to_list_insert _ _ _ N))). cbn [map]. rewrite zsum_cons. cbn [snd]. lia.
Qed.

Lemma regsum_update f st st' rid r0 r : s_regions st !! rid = Some r0 -> s_regions st' = <[rid := r]> (s_regions st) ->
  regsum f st' = regsum f st + f r - f r0.
Proof.
  intros H E. unfold regsum. rewrite E.
  pose proof (map_to_list_delete _ _ _ H) as P1.
  assert (D : delete rid (s_regions st) !! rid = None) by (apply lookup_delete_eq).
  assert (P2 : map_to_list (<[rid := r]> (s_regions st)) ≡ₚ (rid, r) :: map_to_list (delete rid (s_regions st))).
  { rewrite <- insert_delete_eq. apply map_to_list_insert. exact D. }
  rewrite (zsum_perm _ _ (Permutation_map (fun kr : N * region => f (snd kr)) P2)).
  rewrite <- (zsum_perm _ _ (Permutation_map (fun kr : N * region => f (snd kr)) P1)). cbn [map]. rewrite !zsum_cons. cbn [snd]. lia.
Qed.

Lemma regsum_delete f st st' rid r0 : s_regions st !! rid = Some r0 -> s_regions st' = delete rid (s_regions st) ->
  regsum f st' = regsum f st - f r0.
Proof.
  intros H E. unfold regsum. rewrite E.
  rewrite <- (zsum_perm _ _ (Permutation_map (fun kr : N * region => f (snd kr)) (map_to_list_delete _ _ _ H))). cbn [map]. rewrite zsum_cons. cbn [snd]. lia.
Qed.

Lemma regsum_ext f st st' : s_regions st' = s_regions st -> regsum f st' = regsum f st.
Proof. intros E. unfold regsum. rewrite E. reflexivity. Qed.

Definition isgreg (r : region) : Z := match r_kind r with RKGroup => 1 | _ => 0 end.
Definition metalen (r : region) : Z := match r_kind r with RKMeta => r_len r | _ => 0 end.

Lemma ngreg_regsum st : ngreg st = regsum isgreg st.
Proof.
  unfold ngreg, regsum. generalize (map_to_list (s_regions st)) as l. induction l as [|[k r] l IH]; [reflexivity|].
  cbn [List.filter map]. rewrite zsum_cons. unfold is_greg at 1. cbn [snd]. unfold isgreg at 1.
  destruct (r_kind r); cbn [length]; lia.
Qed.

Lemma Phi_regsum st : Phi st = regsum wreg st + brk_dead_w st.
Proof. reflexivity. Qed.

Record CURI (st : mstate) : Prop := mkCURI {
  cu_ids : forall rid r, s_regions st !! rid = Some r -> (rid < s_next_rid st)%N;
  cu_cursor : 0 <= c_avail_meta_area_count (s_ctx st) /\
      (0 < c_avail_meta_area_count (s_ctx st) -> c_avail_meta_areas (s_ctx st) <> None) /\
      (forall rid off, c_avail_meta_areas (s_ctx st) = Some (rid, off) ->
       exists r, s_regions st !! rid = Some r /\ is_metakind r /\ PGSZ <= off /\ off mod PGSZ = 0
         /\ off + c_avail_meta_area_count (s_ctx st) * PGSZ = r_len r
         /\ (0 < c_avail_meta_area_count (s_ctx st) -> r_kind r = RKMeta));
  cu_brkfront : forall rid r, s_regions st !! rid = Some r -> r_kind r = RKBrk -> frontier st rid r = r_len r;
  cu_brk : match c_brk (s_ctx st) with
      | BrkUntried => forall rid r, s_regions st !! rid = Some r -> r_kind r <> RKBrk
      | BrkLive rid off => exists r, s_regions st !! rid = Some r /\ r_kind r = RKBrk /\ r_len r = off
      | BrkDead => True
      end;
  cu_brk1 : forall rid1 rid2 r1 r2, s_regions st !! rid1 = Some r1 -> s_regions st !! rid2 = Some r2 ->
      r_kind r1 = RKBrk -> r_kind r2 = RKBrk -> rid1 = rid2;
  cu_shape : forall rid r, s_regions st !! rid = Some r -> 0 < r_len r /\ (is_metakind r -> r_len r mod PGSZ = 0 /\ 2 * PGSZ <= r_len r);
  cu_areas : forall a ar, s_areas st !! a = Some ar ->
      exists r, s_regions st !! (fst a) = Some r /\ is_metakind r /\ snd a mod PGSZ = 0 /\ PGSZ <= snd a
                 /\ snd a + PGSZ <= frontier st (fst a) r;
  cu_tail : forall t, c_meta_area_tail (s_ctx st) = Some t -> s_areas st !! t <> None;
  cu_tail0 : c_meta_area_tail (s_ctx st) = None -> c_avail_meta_count (s_ctx st) = 0;
  cu_metas : forall m mr, s_metas st !! m = Some mr -> exists a ar k, s_areas st !! a = Some ar /\ 0 <= k < NSLOTS /\ m = mslot a k;
  cu_avail : 0 <= c_avail_meta_count (s_ctx st) <= NSLOTS /\
      (0 < c_avail_meta_count (s_ctx st) ->
       exists a, c_meta_area_tail (s_ctx st) = Some a /\
         c_avail_meta (s_ctx st) = Some (mslot a (NSLOTS - c_avail_meta_count (s_ctx st))) /\
         forall k, NSLOTS - c_avail_meta_count (s_ctx st) <= k < NSLOTS -> s_metas st !! (mslot a k) = None);
  cu_init : c_init_done (s_ctx st) = 0 -> s_areas st = ∅
}.

Lemma CURI_of X st L BL LS : INVC X st L BL LS -> CURI st.
Proof.
  intros (IR & IA & _ & _ & _ & _). constructor.
  - exact (ir_ids _ _ _ IR).
  - exact (ir_cursor _ _ _ IR).
  - exact (ir_brkfront _ _ _ IR).
  - pose proof (ir_brk _ _ _ IR) as B. unfold ctx in B. destruct (c_brk (s_ctx st)) eqn:E.
    + exact (proj2 B).
    + exact I.
    + exact (proj2 B).
  - exact (ir_brk1 _ _ _ IR).
  - intros rid r H. destruct (ir_shape _ _ _ IR rid r H) as (_ & _ & H1 & _ & _ & H2). split; [exact H1| exact H2].
  - intros a ar H. exact (proj1 (ia_areas _ IA a ar H)).
  - exact (ia_tail _ IA).
  - intros H. exact (proj2 (ia_tail0 _ IA H)).
  - exact (ia_metas _ IA).
  - exact (ia_avail _ IA).
  - intros H. destruct (ia_secret _ IA) as [_ [(_ & _ & E)|(E & _)]]; [exact E| rewrite E in H; discriminate].
Qed.

Record MARITH (st : mstate) : Prop := mkMA {
  ma_shnn : 0 <= c_meta_alloc_shift (s_ctx st);
  ma_poti : 2 ^ c_meta_alloc_shift (s_ctx st) <= 1 + c_avail_meta_area_count (s_ctx st) + nareas st;
  ma_shi : 2 ^ c_meta_alloc_shift (s_ctx st) <= 2 + 2 * nareas st;
  ma_mbi : regsum metalen st <= 2 * PGSZ * 2 ^ c_meta_alloc_shift (s_ctx st);
  ma_brki : forall rid r, s_regions st !! rid = Some r -> r_kind r = RKBrk -> r_len r <= PGSZ * (1 + nareas st);
  ma_cnti : NSLOTS * nareas st - c_avail_meta_count (s_ctx st) <= nmeta st
}.

Lemma mslot_inj a a' k k' : snd a mod PGSZ = 0 -> snd a' mod PGSZ = 0 -> 0 <= k < NSLOTS -> 0 <= k' < NSLOTS ->
  mslot a k = mslot a' k' -> a = a' /\ k = k'.
Proof.
  intros Ha Ha' Hk Hk' E. unfold mslot, aadd, AREA_HDR, META_SIZE, NSLOTS, PGSZ in *. destruct a as [ra oa], a' as [ra' oa']. cbn in *.
  injection E as E1 E2. subst ra'.
  assert (oa = oa') by (pose proof (Z.mod_pos_bound oa 4096 ltac:(lia)); pose proof (Z.mod_pos_bound oa' 4096 ltac:(lia));
                        pose proof (Z_div_mod_eq_full oa 4096); pose proof (Z_div_mod_eq_full oa' 4096); nia).
  subst oa'. split; [reflexivity| lia].
Qed.

Definition take_st (st : mstate) (m : aptr) : mstate :=
  upd_meta m (fun r => m_set_prev None (m_set_next None r))
    (upd_ctx (fun c => set_avail_meta (Some (aadd m META_SIZE)) (set_avail_meta_count (c_avail_meta_count c - 1) c)) st).

Lemma am_take_eq {T} st m (k : mstate -> optr -> M T) bail : c_avail_meta (s_ctx st) = Some m -> am_take st k bail = k (take_st st m) (Some m).
Proof. intros H. unfold am_take, ctx. rewrite H. reflexivity. Qed.

Lemma take_metas st m : s_metas (take_st st m) = <[m := m_set_prev None (m_set_next None (get_meta_rec st m))]> (s_metas st).
Proof. reflexivity. Qed.
Lemma take_MR st m x : MR (take_st st m) x = if aptr_eqb x m then m_set_prev None (m_set_next None (MR st x)) else MR st x.
Proof. unfold MR, take_st. rewrite get_meta_rec_upd. destruct (aptr_eqb_spec x m) as [->|NE]; reflexivity. Qed.
Lemma take_ctx st m : s_ctx (take_st st m) = set_avail_meta (Some (aadd m META_SIZE)) (set_avail_meta_count (c_avail_meta_count (s_ctx st) - 1) (s_ctx st)).
Proof. reflexivity. Qed.
Lemma take_groups st m : s_groups (take_st st m) = s_groups st. Proof. reflexivity. Qed.
Lemma take_slots st m : s_slots (take_st st m) = s_slots st. Proof. reflexivity. Qed.
Lemma take_regions st m : s_regions (take_st st m) = s_regions st. Proof. reflexivity. Qed.
Lemma take_areas st m : s_areas (take_st st m) = s_areas st. Proof. reflexivity. Qed.
Lemma take_next_rid st m : s_next_rid (take_st st m) = s_next_rid st. Proof. reflexivity. Qed.

Lemma nmeta_insert_fresh st st' m r : s_metas st !! m = None -> s_metas st' = <[m := r]> (s_metas st) -> nmeta st' = nmeta st + 1.
Proof. intros H E. unfold nmeta. rewrite E, map_size_insert_None by exact H. lia. Qed.

Definition ct_st (s : mstate) (p : aptr) : mstate := take_st (carve_rest (adv s p) p) (mslot p 0).

Lemma ct_eq {T} s p (k : mstate -> optr -> M T) bail : am_carve s p k bail = k (ct_st s p) (Some (mslot p 0)).
Proof. rewrite am_carve_eq. apply am_take_eq. unfold carve_rest. destruct (c_meta_area_tail (ctx (adv s p))); reflexivity. Qed.

Lemma ct_areas_eq s p : s_areas (ct_st s p) =
  match c_meta_area_tail (s_ctx s) with
  | Some tl => <[p := mkArea (c_secret (s_ctx s)) (a_next (default (mkArea 0 None 0)
                 ((<[tl := match s_areas s !! tl with Some a => mkArea (a_check a) (Some p) (a_nslots a) | None => mkArea 0 (Some p) 0 end]> (s_areas s)) !! p))) NSLOTS]>
               (<[tl := match s_areas s !! tl with Some a => mkArea (a_check a) (Some p) (a_nslots a) | None => mkArea 0 (Some p) 0 end]> (s_areas s))
  | None => <[p := mkArea (c_secret (s_ctx s)) (a_next (default (mkArea 0 None 0) (s_areas s !! p))) NSLOTS]> (s_areas s)
  end.
Proof. unfold ct_st, carve_rest, adv, ctx. cbn -[lookup insert NSLOTS AREA_HDR META_SIZE mslot]. destruct (c_meta_area_tail (s_ctx s)); reflexivity. Qed.

Lemma ct_areas_some s p a : s_areas s !! p = None -> (forall t, c_meta_area_tail (s_ctx s) = Some t -> s_areas s !! t <> None) ->
  (s_areas (ct_st s p) !! a <> None <-> (a = p \/ s_areas s !! a <> None)).
Proof.
  intros NA TL. rewrite ct_areas_eq. destruct (c_meta_area_tail (s_ctx s)) as [tl|] eqn:ET.
  - assert (Htl : s_areas s !! tl <> None) by (apply TL; reflexivity).
    assert (NE : tl <> p) by (intros ->; exact (Htl NA)).
    split.
    + intros H. destruct (aptr_eqb_spec a p) as [->|NEa]; [left; reflexivity| right].
      rewrite lookup_insert_ne in H by congruence. destruct (aptr_eqb_spec a tl) as [->|NEt]; [exact Htl|].
      rewrite lookup_insert_ne in H by congruence. exact H.
    + intros [->|H]; [rewrite lookup_insert_eq; discriminate|]. destruct (aptr_eqb_spec a p) as [->|NEa]; [rewrite lookup_insert_eq; discriminate|].
      rewrite lookup_insert_ne by congruence. destruct (aptr_eqb_spec a tl) as [->|NEt]; [rewrite lookup_insert_eq; discriminate|].
      rewrite lookup_insert_ne by congruence. exact H.
  - split.
    + intros H. destruct (aptr_eqb_spec a p) as [->|NEa]; [left; reflexivity| right]. rewrite lookup_insert_ne in H by congruence. exact H.
    + intros [->|H]; [rewrite lookup_insert_eq; discriminate|]. destruct (aptr_eqb_spec a p) as [->|NEa]; [rewrite lookup_insert_eq; discriminate|].
      rewrite lookup_insert_ne by congruence. exact H.
Qed.

Lemma ct_nareas s p : s_areas s !! p = None -> (forall t, c_meta_area_tail (s_ctx s) = Some t -> s_areas s !! t <> None) ->
  nareas (ct_st s p) = nareas s + 1.
Proof.
  intros NA TL. unfold nareas. rewrite ct_areas_eq. destruct (c_meta_area_tail (s_ctx s)) as [tl|] eqn:ET.
  - assert (Htl : s_areas s !! tl <> None) by (apply TL; reflexivity).
    assert (NE : tl <> p) by (intros ->; exact (Htl NA)).
    destruct (s_areas s !! tl) as [atl|] eqn:Etl; [| congruence].
    rewrite map_size_insert_None.
    + rewrite map_size_insert_Some by (eexists; exact Etl). lia.
    + rewrite lookup_insert_ne by congruence. exact NA.
  - rewrite map_size_insert_None by exact NA. lia.
Qed.

Lemma ct_metas s p : s_metas (ct_st s p) = <[mslot p 0 := m_set_prev None (m_set_next None (get_meta_rec s (mslot p 0)))]> (s_metas s).
Proof. unfold ct_st, carve_rest, adv, ctx. cbn -[lookup insert NSLOTS AREA_HDR META_SIZE mslot]. destruct (c_meta_area_tail (s_ctx s)); reflexivity. Qed.

Lemma ct_same s p :
  s_groups (ct_st s p) = s_groups s /\ s_slots (ct_st s p) = s_slots s /\ s_regions (ct_st s p) = s_regions s
  /\ s_next_rid (ct_st s p) = s_next_rid s
  /\ c_avail_meta_areas (s_ctx (ct_st s p)) = Some (aadd p 4096)
  /\ c_avail_meta_area_count (s_ctx (ct_st s p)) = c_avail_meta_area_count (s_ctx s) - 1
  /\ c_avail_meta_count (s_ctx (ct_st s p)) = NSLOTS - 1
  /\ c_avail_meta (s_ctx (ct_st s p)) = Some (aadd (mslot p 0) META_SIZE)
  /\ c_meta_area_tail (s_ctx (ct_st s p)) = Some p
  /\ c_meta_alloc_shift (s_ctx (ct_st s p)) = c_meta_alloc_shift (s_ctx s)
  /\ c_brk (s_ctx (ct_st s p)) = c_brk (s_ctx s)
  /\ c_init_done (s_ctx (ct_st s p)) = c_init_done (s_ctx s)
  /\ c_free_meta_head (s_ctx (ct_st s p)) = c_free_meta_head (s_ctx s)
  /\ c_active (s_ctx (ct_st s p)) = c_active (s_ctx s) /\ c_usage (s_ctx (ct_st s p)) = c_usage (s_ctx s)
  /\ c_bounces (s_ctx (ct_st s p)) = c_bounces (s_ctx s) /\ c_seq (s_ctx (ct_st s p)) = c_seq (s_ctx s)
  /\ c_unmap_seq (s_ctx (ct_st s p)) = c_unmap_seq (s_ctx s) /\ c_mmap_counter (s_ctx (ct_st s p)) = c_mmap_counter (s_ctx s).
Proof. unfold ct_st, carve_rest, adv, ctx. cbn -[lookup insert NSLOTS AREA_HDR META_SIZE mslot]. destruct (c_meta_area_tail (s_ctx s)); cbn; repeat split; reflexivity. Qed.

Record PCV (s : mstate) (p : aptr) : Prop := mkPCV {
  pc_cur : c_avail_meta_areas (s_ctx s) = Some p;
  pc_ac : 1 <= c_avail_meta_area_count (s_ctx s);
  pc_cnt : c_avail_meta_count (s_ctx s) = 0;
  pc_init : c_init_done (s_ctx s) <> 0;
  pc_reg : exists r, s_regions s !! fst p = Some r /\ is_metakind r /\ PGSZ <= snd p /\ snd p mod PGSZ = 0
             /\ snd p + c_avail_meta_area_count (s_ctx s) * PGSZ = r_len r /\ (2 <= c_avail_meta_area_count (s_ctx s) -> r_kind r = RKMeta);
  pc_ids : forall rid r, s_regions s !! rid = Some r -> (rid < s_next_rid s)%N;
  pc_brk : match c_brk (s_ctx s) with
      | BrkUntried => forall rid r, s_regions s !! rid = Some r -> r_kind r <> RKBrk
      | BrkLive rid off => exists r, s_regions s !! rid = Some r /\ r_kind r = RKBrk /\ r_len r = off
      | BrkDead => True
      end;
  pc_brk1 : forall rid1 rid2 r1 r2, s_regions s !! rid1 = Some r1 -> s_regions s !! rid2 = Some r2 ->
      r_kind r1 = RKBrk -> r_kind r2 = RKBrk -> rid1 = rid2;
  pc_shape : forall rid r, s_regions s !! rid = Some r -> 0 < r_len r /\ (is_metakind r -> r_len r mod PGSZ = 0 /\ 2 * PGSZ <= r_len r);
  pc_areas : forall a ar, s_areas s !! a = Some ar ->
      exists r, s_regions s !! (fst a) = Some r /\ is_metakind r /\ snd a mod PGSZ = 0 /\ PGSZ <= snd a
                 /\ snd a + PGSZ <= frontier s (fst a) r;
  pc_brkfront : forall rid r, s_regions s !! rid = Some r -> r_kind r = RKBrk ->
      frontier s rid r = r_len r \/ (rid = fst p /\ c_avail_meta_area_count (s_ctx s) = 1);
  pc_tail : forall t, c_meta_area_tail (s_ctx s) = Some t -> s_areas s !! t <> None;
  pc_metas : forall m mr, s_metas s !! m = Some mr -> exists a ar k, s_areas s !! a = Some ar /\ 0 <= k < NSLOTS /\ m = mslot a k;
  pc_shnn : 0 <= c_meta_alloc_shift (s_ctx s);
  pc_poti : 2 ^ c_meta_alloc_shift (s_ctx s) <= 1 + c_avail_meta_area_count (s_ctx s) + nareas s;
  pc_shi : 2 ^ c_meta_alloc_shift (s_ctx s) <= 2 + 2 * (nareas s + 1);
  pc_mbi : regsum metalen s <= 2 * PGSZ * 2 ^ c_meta_alloc_shift (s_ctx s);
  pc_brki : forall rid r, s_regions s !! rid = Some r -> r_kind r = RKBrk -> r_len r <= PGSZ * (2 + nareas s);
  pc_cnti : NSLOTS * nareas s <= nmeta s
}.

Lemma pcv_fresh s p : PCV s p -> s_areas s !! p = None /\ (forall k, 0 <= k < NSLOTS -> s_metas s !! mslot p k = None).
Proof.
  intros PC. destruct (pc_reg _ _ PC) as (r & Hr & Kr & Po & Pm & _).
  assert (NA : s_areas s !! p = None).
  { destruct (s_areas s !! p) as [ar|] eqn:E; [|reflexivity]. exfalso.
    destruct (pc_areas _ _ PC p ar E) as (r' & Hr' & _ & _ & _ & Hf). rewrite Hr in Hr'. injection Hr' as <-.
    unfold frontier in Hf. rewrite (pc_cur _ _ PC) in Hf. destruct p as [rid off]. cbn [fst snd] in Hf. rewrite N.eqb_refl in Hf. unfold PGSZ in Hf. lia. }
  split; [exact NA|]. intros k Hk. destruct (s_metas s !! mslot p k) as [mr|] eqn:E; [|reflexivity]. exfalso.
  destruct (pc_metas _ _ PC _ _ E) as (a & ar & k' & Ha & Hk' & Ea).
  destruct (pc_areas _ _ PC a ar Ha) as (_ & _ & _ & Am & _ & _).
  destruct (mslot_inj p a k k' Pm Am Hk Hk' Ea) as [<- _]. rewrite Ha in NA. discriminate.
Qed.

Lemma ct_post s p : PCV s p ->
  CURI (ct_st s p) /\ MARITH (ct_st s p) /\ MR (ct_st s p) (mslot p 0) = meta0 /\ s_metas s !! mslot p 0 = None
  /\ nmeta (ct_st s p) = nmeta s + 1 /\ nareas (ct_st s p) = nareas s + 1
  /\ (forall x, x <> mslot p 0 -> MR (ct_st s p) x = MR s x).
Proof.
  intros PC. destruct (pcv_fresh s p PC) as [NA NM].
  pose proof (ct_same s p) as (G1 & S1 & R1 & N1 & CA1 & AC1 & CT1 & AV1 & TL1 & SH1 & BR1 & IN1 & FM1 & AC1' & US1 & BO1 & SE1 & UN1 & MC1).
  pose proof (ct_metas s p) as M1.
  pose proof (ct_nareas s p NA (pc_tail _ _ PC)) as NA1.
  pose proof (fun a => ct_areas_some s p a NA (pc_tail _ _ PC)) as AS1.
  destruct (pc_reg _ _ PC) as (r & Hr & Kr & Po & Pm & Elen & K2).
  assert (NM0 : s_metas s !! mslot p 0 = None) by (apply NM; unfold NSLOTS; lia).
  assert (MR0 : MR (ct_st s p) (mslot p 0) = meta0) by (unfold MR, get_meta_rec at 1; rewrite M1, lookup_insert_eq; cbn [default]; unfold get_meta_rec; rewrite NM0; reflexivity).
  assert (MRo : forall x, x <> mslot p 0 -> MR (ct_st s p) x = MR s x) by (intros x NE; unfold MR, get_meta_rec; rewrite M1, lookup_insert_ne by congruence; reflexivity).
  assert (NMt : nmeta (ct_st s p) = nmeta s + 1) by (apply (nmeta_insert_fresh s _ (mslot p 0) _ NM0 M1)).
  assert (FR : forall rid r0, frontier (ct_st s p) rid r0 = if (fst p =? rid)%N then snd p + 4096 else r_len r0).
  { intros rid r0. unfold frontier. rewrite CA1. destruct p as [prid poff]. reflexivity. }
  assert (FR0 : forall rid r0, frontier s rid r0 = if (fst p =? rid)%N then snd p else r_len r0).
  { intros rid r0. unfold frontier. rewrite (pc_cur _ _ PC). destruct p as [prid poff]. reflexivity. }
  split; [| split; [| split; [exact MR0| split; [exact NM0| split; [exact NMt| split; [exact NA1| exact MRo]]]]]].
  - constructor.
    + rewrite R1, N1. exact (pc_ids _ _ PC).
    + rewrite AC1, CA1. split; [pose proof (pc_ac _ _ PC); lia|]. split; [discriminate|].
      intros rid off E. injection E as <- <-. exists r. rewrite R1. cbn [fst snd aadd].
      split; [exact Hr|]. split; [exact Kr|]. split; [unfold PGSZ in *; lia|]. split; [unfold PGSZ in *; rewrite Z.add_mod by lia; rewrite Pm; reflexivity|].
      split; [unfold PGSZ in *; lia|]. intros H2. apply K2. lia.
    + intros rid r0 Hr0 Kb. rewrite R1 in Hr0. pose proof (FR rid r0) as FRr. unfold frontier in FRr |- *. rewrite FRr.
      destruct (pc_brkfront _ _ PC rid r0 Hr0 Kb) as [E|(-> & E1)].
      * destruct (N.eqb_spec (fst p) rid) as [<-|NE]; [| reflexivity].
        rewrite Hr in Hr0. injection Hr0 as <-. rewrite FR0, N.eqb_refl in E. exfalso. pose proof (pc_ac _ _ PC). unfold PGSZ in *. lia.
      * rewrite N.eqb_refl. rewrite Hr in Hr0. injection Hr0 as <-. rewrite E1 in Elen. unfold PGSZ in *. lia.
    + rewrite BR1, R1. exact (pc_brk _ _ PC).
    + rewrite R1. exact (pc_brk1 _ _ PC).
    + rewrite R1. exact (pc_shape _ _ PC).
    + intros a ar Ha. rewrite R1.
      destruct (aptr_eqb_spec a p) as [->|NEa].
      * exists r. split; [exact Hr|]. split; [exact Kr|]. split; [exact Pm|]. split; [exact Po|]. rewrite FR, N.eqb_refl. unfold PGSZ. lia.
      * assert (Ha0 : s_areas s !! a <> None) by (destruct (proj1 (AS1 a) ltac:(rewrite Ha; discriminate)) as [E|E]; [congruence| exact E]).
        destruct (s_areas s !! a) as [ar0|] eqn:E0; [| congruence].
        destruct (pc_areas _ _ PC a ar0 E0) as (r0 & Hr0 & K0 & Am & Ap & Af). exists r0. split; [exact Hr0|]. split; [exact K0|]. split; [exact Am|]. split; [exact Ap|].
        rewrite FR. rewrite FR0 in Af. destruct (N.eqb_spec (fst p) (fst a)); [unfold PGSZ in *; lia| exact Af].
    + intros t Ht. rewrite TL1 in Ht. injection Ht as <-. apply (proj2 (AS1 p)). left. reflexivity.
    + rewrite TL1. discriminate.
    + intros m mr Hm. rewrite M1 in Hm. destruct (aptr_eqb_spec m (mslot p 0)) as [->|NEm].
      * destruct (s_areas (ct_st s p) !! p) as [ap|] eqn:Ep; [| exfalso; apply (proj2 (AS1 p)) ; [left; reflexivity| exact Ep]].
        exists p, ap, 0. split; [exact Ep|]. split; [unfold NSLOTS; lia| reflexivity].
      * rewrite lookup_insert_ne in Hm by congruence. destruct (pc_metas _ _ PC m mr Hm) as (a & ar & k & Ha & Hk & ->).
        destruct (s_areas (ct_st s p) !! a) as [a'|] eqn:Ea; [| exfalso; apply (proj2 (AS1 a)); [right; rewrite Ha; discriminate| exact Ea]].
        exists a, a', k. split; [exact Ea|]. split; [exact Hk| reflexivity].
    + rewrite CT1. split; [unfold NSLOTS; lia|]. intros _. exists p. split; [exact TL1|]. split.
      * rewrite AV1, mslot_succ. replace (NSLOTS - (NSLOTS - 1)) with (0 + 1) by (unfold NSLOTS; lia). reflexivity.
      * intros k Hk. rewrite M1. rewrite lookup_insert_ne.
        -- apply NM. unfold NSLOTS in *. lia.
        -- intros E. destruct (mslot_inj p p k 0 Pm Pm ltac:(unfold NSLOTS in *; lia) ltac:(unfold NSLOTS; lia) (eq_sym E)) as [_ E']. unfold NSLOTS in *. lia.
    + rewrite IN1. intros H. exfalso. exact (pc_init _ _ PC H).
  - constructor.
    + rewrite SH1. exact (pc_shnn _ _ PC).
    + rewrite SH1, AC1, NA1. pose proof (pc_poti _ _ PC). lia.
    + rewrite SH1, NA1. pose proof (pc_shi _ _ PC). lia.
    + rewrite SH1, (regsum_ext _ _ _ R1). exact (pc_mbi _ _ PC).
    + intros rid r0 Hr0 Kb. rewrite R1 in Hr0. rewrite NA1. pose proof (pc_brki _ _ PC rid r0 Hr0 Kb). lia.
    + rewrite CT1, NA1, NMt. pose proof (pc_cnti _ _ PC). unfold NSLOTS in *. lia.
Qed.

Record MFR (s s' : mstate) : Prop := mkMFR {
  mf_regions : s_regions s' = s_regions s;
  mf_areas : s_areas s' = s_areas s;
  mf_keys : forall x, s_metas s' !! x = None <-> s_metas s !! x = None;
  mf_rid : s_next_rid s' = s_next_rid s;
  mf_amc : c_avail_meta_count (s_ctx s') = c_avail_meta_count (s_ctx s);
  mf_amac : c_avail_meta_area_count (s_ctx s') = c_avail_meta_area_count (s_ctx s);
  mf_am : c_avail_meta (s_ctx s') = c_avail_meta (s_ctx s);
  mf_amas : c_avail_meta_areas (s_ctx s') = c_avail_meta_areas (s_ctx s);
  mf_tail : c_meta_area_tail (s_ctx s') = c_meta_area_tail (s_ctx s);
  mf_shift : c_meta_alloc_shift (s_ctx s') = c_meta_alloc_shift (s_ctx s);
  mf_brk : c_brk (s_ctx s') = c_brk (s_ctx s);
  mf_init : c_init_done (s_ctx s') = c_init_done (s_ctx s)
}.

Lemma nmeta_keys s s' : (forall x, s_metas s' !! x = None <-> s_metas s !! x = None) -> nmeta s' = nmeta s.
Proof.
  intros K. unfold nmeta. f_equal. rewrite <- !size_dom. f_equal. apply set_eq. intros x. rewrite !elem_of_dom. split.
  - intros [v Hv]. destruct (s_metas s !! x) eqn:E; [eexists; reflexivity|]. apply K in E. congruence.
  - intros [v Hv]. destruct (s_metas s' !! x) eqn:E; [eexists; reflexivity|]. apply K in E. congruence.
Qed.

Lemma CURI_frame s s' : CURI s -> MFR s s' -> CURI s'.
Proof.
  intros C [R A K N AMC AMAC AM AMAS TL SH BR IN].
  assert (FR : forall rid r, frontier s' rid r = frontier s rid r) by (intros; unfold frontier; rewrite AMAS; reflexivity).
  destruct C as [C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12]. constructor.
  - rewrite R, N. exact C1.
  - rewrite AMAC, AMAS, R. exact C2.
  - intros rid r H Hk. rewrite FR. rewrite R in H. exact (C3 rid r H Hk).
  - rewrite BR, R. exact C4.
  - rewrite R. exact C5.
  - rewrite R. exact C6.
  - intros a ar H. rewrite A in H. rewrite R. destruct (C7 a ar H) as (r & H1 & H2 & H3 & H4 & H5). exists r. rewrite FR. auto.
  - intros t H. rewrite A. apply C8. rewrite <- TL. exact H.
  - intros H. rewrite AMC. apply C9. rewrite <- TL. exact H.
  - intros m mr H. rewrite A. destruct (s_metas s !! m) as [mr0|] eqn:E; [| apply K in E; congruence].
    exact (C10 m mr0 E).
  - rewrite AMC, TL, AM. destruct C11 as [C11a C11b]. split; [exact C11a|]. intros H. destruct (C11b H) as (a & H1 & H2 & H3). exists a. split; [exact H1|]. split; [exact H2|].
    intros k Hk. apply K. exact (H3 k Hk).
  - rewrite IN, A. exact C12.
Qed.

Lemma MARITH_frame s s' : MARITH s -> MFR s s' -> MARITH s'.
Proof.
  intros M F. pose proof (nmeta_keys _ _ (mf_keys _ _ F)) as NM.
  assert (NA : nareas s' = nareas s) by (unfold nareas; rewrite (mf_areas _ _ F); reflexivity).
  destruct M as [M1 M2 M3 M4 M5 M6]. constructor.
  - rewrite (mf_shift _ _ F). exact M1.
  - rewrite (mf_shift _ _ F), (mf_amac _ _ F), NA. exact M2.
  - rewrite (mf_shift _ _ F), NA. exact M3.
  - rewrite (mf_shift _ _ F), (regsum_ext _ _ _ (mf_regions _ _ F)). exact M4.
  - intros rid r H K. rewrite (mf_regions _ _ F) in H. rewrite NA. exact (M5 rid r H K).
  - rewrite (mf_amc _ _ F), NA, NM. exact M6.
Qed.

Lemma take_post st : CURI st -> MARITH st -> 0 < c_avail_meta_count (s_ctx st) ->
  exists a, c_meta_area_tail (s_ctx st) = Some a /\ c_avail_meta (s_ctx st) = Some (mslot a (NSLOTS - c_avail_meta_count (s_ctx st)))
  /\ let m := mslot a (NSLOTS - c_avail_meta_count (s_ctx st)) in
     CURI (take_st st m) /\ MARITH (take_st st m) /\ MR (take_st st m) m = meta0 /\ s_metas st !! m = None
     /\ nmeta (take_st st m) = nmeta st + 1 /\ (forall x, x <> m -> MR (take_st st m) x = MR st x).
Proof.
  intros C M Hc. pose proof (cu_avail _ C) as [CA CB]. destruct (CB Hc) as (a & TL & AV & ABS).
  exists a. split; [exact TL|]. split; [exact AV|]. cbn zeta.
  set (m := mslot a (NSLOTS - c_avail_meta_count (s_ctx st))).
  assert (Ha : s_areas st !! a <> None) by (apply (cu_tail _ C); exact TL).
  destruct (s_areas st !! a) as [ar|] eqn:Ear; [| congruence].
  destruct (cu_areas _ C a ar Ear) as (r0 & _ & _ & Am & _ & _).
  assert (Nm : s_metas st !! m = None) by (apply ABS; lia).
  assert (MR0 : MR (take_st st m) m = meta0).
  { rewrite take_MR, aptr_eqb_refl. unfold MR, get_meta_rec. rewrite Nm. reflexivity. }
  assert (MRo : forall x, x <> m -> MR (take_st st m) x = MR st x) by (intros x NE; rewrite take_MR, aptr_eqb_neq by exact NE; reflexivity).
  assert (NMt : nmeta (take_st st m) = nmeta st + 1) by (apply (nmeta_insert_fresh st _ m _ Nm (take_metas st m))).
  assert (FR : forall rid r, frontier (take_st st m) rid r = frontier st rid r) by (intros; unfold frontier; rewrite take_ctx; reflexivity).
  split; [| split; [| split; [exact MR0| split; [exact Nm| split; [exact NMt| exact MRo]]]]].
  - destruct C as [C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12]. constructor.
    + rewrite take_regions, take_next_rid. exact C1.
    + rewrite take_regions, take_ctx. cbn. exact C2.
    + intros rid r H K. rewrite FR. rewrite take_regions in H. exact (C3 rid r H K).
    + rewrite take_regions, take_ctx. cbn. exact C4.
    + rewrite take_regions. exact C5.
    + rewrite take_regions. exact C6.
    + intros a0 ar0 H. rewrite take_areas in H. rewrite take_regions. destruct (C7 a0 ar0 H) as (r & H1 & H2 & H3 & H4 & H5). exists r. rewrite FR. auto.
    + intros t H. rewrite take_areas. apply C8. rewrite take_ctx in H. exact H.
    + rewrite take_ctx. cbn [set_avail_meta set_avail_meta_count c_meta_area_tail]. rewrite TL. discriminate.
    + intros x mr H. rewrite take_areas. rewrite take_metas in H. destruct (aptr_eqb_spec x m) as [Ex|NE]; [subst x|].
      * exists a, ar, (NSLOTS - c_avail_meta_count (s_ctx st)). split; [exact Ear|]. split; [lia| reflexivity].
      * rewrite lookup_insert_ne in H by congruence. exact (C10 x mr H).
    + rewrite take_ctx. cbn [set_avail_meta set_avail_meta_count c_meta_area_tail c_avail_meta_count c_avail_meta]. split; [lia|]. intros H. exists a. split; [exact TL|]. split.
      * unfold m. rewrite mslot_succ. f_equal. f_equal. lia.
      * intros k Hk. rewrite take_metas, lookup_insert_ne.
        -- apply ABS. lia.
        -- intros E. unfold m in E. destruct (mslot_inj a a k (NSLOTS - c_avail_meta_count (s_ctx st)) Am Am ltac:(unfold NSLOTS in *; lia) ltac:(unfold NSLOTS in *; lia) (eq_sym E)) as [_ E']. lia.
    + rewrite take_areas, take_ctx. cbn [set_avail_meta set_avail_meta_count c_init_done]. exact C12.
  - destruct M as [M1 M2 M3 M4 M5 M6]. constructor.
    + rewrite take_ctx. exact M1.
    + rewrite take_ctx. unfold nareas in *. rewrite take_areas. exact M2.
    + rewrite take_ctx. unfold nareas in *. rewrite take_areas. exact M3.
    + rewrite take_ctx, (regsum_ext _ _ _ (take_regions st m)). exact M4.
    + intros rid r H K. rewrite take_regions in H. unfold nareas in *. rewrite take_areas. exact (M5 rid r H K).
    + rewrite NMt, take_ctx. cbn [set_avail_meta set_avail_meta_count c_avail_meta_count]. unfold nareas in *. rewrite take_areas. lia.
Qed.

Record AMPOST (st : mstate) (LS : lhead -> list aptr) (st1 : mstate) (LS1 : lhead -> list aptr) (mo : optr) (dc dn : Z) : Prop := mkAMP {
  ap_groups : s_groups st1 = s_groups st;
  ap_slots : s_slots st1 = s_slots st;
  ap_data : forall x, data_of (MR st1 x) = data_of (MR st x);
  ap_active : forall sc, active st1 sc = active st sc;
  ap_usage : forall sc, usage st1 sc = usage st sc;
  ap_ctxo : c_bounces (s_ctx st1) = c_bounces (s_ctx st) /\ c_seq (s_ctx st1) = c_seq (s_ctx st)
            /\ c_unmap_seq (s_ctx st1) = c_unmap_seq (s_ctx st) /\ c_mmap_counter (s_ctx st1) = c_mmap_counter (s_ctx st);
  ap_lists : lists_ok st1 LS1;
  ap_lsa : forall sc, LS1 (LActive sc) = LS (LActive sc);
  ap_lsf : LS1 LFree = LS LFree \/ exists m, LS LFree = m :: LS1 LFree /\ mo = Some m;
  ap_res : forall m, mo = Some m -> MR st1 m = meta0 /\ (forall h, ~ In m (LS1 h)) /\ s_metas st1 !! m <> None
                                   /\ (head_of (LS LFree) = Some m \/ (s_metas st !! m = None /\ LS LFree = []));
  ap_pres : forall x, s_metas st !! x <> None -> s_metas st1 !! x <> None;
  ap_newpres : forall x, s_metas st1 !! x <> None -> s_metas st !! x <> None \/ mo = Some x;
  ap_nmeta : nmeta st1 = nmeta st \/ (nmeta st1 = nmeta st + 1 /\ LS LFree = []);
  ap_regions : forall rid r, s_regions st !! rid = Some r -> r_kind r <> RKBrk -> s_regions st1 !! rid = Some r;
  ap_nogrp : forall rid r, s_regions st1 !! rid = Some r -> r_kind r = RKGroup -> s_regions st !! rid = Some r;
  ap_ngreg : ngreg st1 = ngreg st;
  ap_rid : (s_next_rid st <= s_next_rid st1)%N;
  ap_curi : CURI st1;
  ap_marith : MARITH st1;
  ap_cost : mo <> None -> dc <= Phi st1 - Phi st /\ dn <= Psi st1 - Psi st
}.

Definition AMPRE (st : mstate) (LS : lhead -> list aptr) : Prop :=
  CURI st /\ MARITH st /\ lists_ok st LS /\ (forall m, In m (LS LFree) -> data_of (MR st m) = data_of meta0).

Lemma lists_ok_same_metas st st' LS : lists_ok st LS -> s_metas st' = s_metas st -> (forall h, get_head st' h = get_head st h) -> lists_ok st' LS.
Proof. intros LO EM EH. apply (lists_ok_links st st' LS LO EH). intros x. unfold MR, get_meta_rec. rewrite EM. split; reflexivity. Qed.

Lemma pow2_shift_succ s : 0 <= s -> Z.shiftl 2 s = 2 ^ (s + 1).
Proof. intros H. rewrite Z.shiftl_mul_pow2 by exact H. rewrite Z.pow_add_r by lia. lia. Qed.

Lemma ampost_ct s LS s2 p dc dn :
  PCV s2 p -> lists_ok s LS -> LS LFree = [] ->
  s_metas s2 = s_metas s -> s_groups s2 = s_groups s -> s_slots s2 = s_slots s -> (forall h, get_head s2 h = get_head s h) ->
  (forall sc, usage s2 sc = usage s sc) -> c_bounces (s_ctx s2) = c_bounces (s_ctx s) -> c_seq (s_ctx s2) = c_seq (s_ctx s) ->
  c_unmap_seq (s_ctx s2) = c_unmap_seq (s_ctx s) -> c_mmap_counter (s_ctx s2) = c_mmap_counter (s_ctx s) ->
  nareas s2 = nareas s ->
  (forall rid r, s_regions s !! rid = Some r -> r_kind r <> RKBrk -> s_regions s2 !! rid = Some r) ->
  (forall rid r, s_regions s2 !! rid = Some r -> r_kind r = RKGroup -> s_regions s !! rid = Some r) ->
  ngreg s2 = ngreg s -> (s_next_rid s <= s_next_rid s2)%N ->
  dc <= Phi s2 - Phi s -> dn <= 4 ->
  AMPOST s LS (ct_st s2 p) LS (Some (mslot p 0)) dc dn.
Proof.
  intros PC LO FE EM EG ES EH EU EB ESQ EUN EMC ENA ER ERG EGR ERID DC DN.
  destruct (ct_post s2 p PC) as (CU & MA & MR0 & NM0 & NMt & NAt & MRo).
  destruct (pcv_fresh s2 p PC) as [NA NM].
  pose proof (ct_same s2 p) as (G1 & S1 & R1 & N1 & CA1 & AC1 & CT1 & AV1 & TL1 & SH1 & BR1 & IN1 & FM1 & ACT1 & US1 & BO1 & SE1 & UN1 & MC1).
  pose proof (ct_metas s2 p) as M1.
  assert (NMs : s_metas s !! mslot p 0 = None) by (rewrite <- EM; exact NM0).
  assert (LO2 : lists_ok (ct_st s2 p) LS).
  { apply (lists_ok_links s (ct_st s2 p) LS LO).
    - intros h. rewrite <- EH. destruct h; cbn [get_head]; [unfold active, ctx; rewrite ACT1; reflexivity| unfold ctx; rewrite FM1; reflexivity].
    - intros x. destruct (aptr_eqb_spec x (mslot p 0)) as [->|NE].
      + rewrite MR0. unfold MR, get_meta_rec. rewrite NMs. split; reflexivity.
      + rewrite (MRo x NE). unfold MR, get_meta_rec. rewrite EM. split; reflexivity. }
  constructor.
  - rewrite G1, EG. reflexivity.
  - rewrite S1, ES. reflexivity.
  - intros x. destruct (aptr_eqb_spec x (mslot p 0)) as [->|NE].
    + rewrite MR0. unfold MR, get_meta_rec. rewrite NMs. reflexivity.
    + rewrite (MRo x NE). unfold MR, get_meta_rec. rewrite EM. reflexivity.
  - intros sc. unfold active, ctx. rewrite ACT1. exact (EH (LActive sc)).
  - intros sc. unfold usage, ctx. rewrite US1. exact (EU sc).
  - rewrite BO1, SE1, UN1, MC1. auto.
  - exact LO2.
  - reflexivity.
  - left. reflexivity.
  - intros m Em. injection Em as <-. split; [exact MR0|]. split.
    + apply (lists_notin _ _ LO2). rewrite MR0. reflexivity.
    + split; [rewrite M1, lookup_insert_eq; discriminate|]. right. split; [exact NMs| exact FE].
  - intros x Hx. rewrite M1, EM. rewrite lookup_insert. destruct (decide (mslot p 0 = x)); [discriminate| exact Hx].
  - intros x Hx. rewrite M1 in Hx. destruct (aptr_eqb_spec x (mslot p 0)) as [->|NE]; [right; reflexivity|].
    left. rewrite lookup_insert_ne in Hx by congruence. rewrite <- EM. exact Hx.
  - right. split; [| exact FE]. rewrite NMt. unfold nmeta. rewrite EM. reflexivity.
  - intros rid r H K. rewrite R1. exact (ER rid r H K).
  - intros rid r H K. rewrite R1 in H. exact (ERG rid r H K).
  - rewrite ngreg_regsum, (regsum_ext _ _ _ R1), <- ngreg_regsum. exact EGR.
  - rewrite N1. exact ERID.
  - exact CU.
  - exact MA.
  - intros _. split.
    + rewrite !Phi_regsum in *. rewrite (regsum_ext wreg _ _ R1). unfold brk_dead_w in *. rewrite BR1. exact DC.
    + unfold Psi. rewrite NAt, ENA. rewrite ngreg_regsum, (regsum_ext _ _ _ R1), <- ngreg_regsum, EGR. lia.
Qed.

Lemma ampost_refl s LS dc dn : CURI s -> MARITH s -> lists_ok s LS -> AMPOST s LS s LS None dc dn.
Proof.
  intros C M LO. constructor.
  - reflexivity.
  - reflexivity.
  - intros x. reflexivity.
  - intros sc. reflexivity.
  - intros sc. reflexivity.
  - repeat split; reflexivity.
  - exact LO.
  - intros sc. reflexivity.
  - left. reflexivity.
  - intros m E. discriminate.
  - intros x Hx. exact Hx.
  - intros x Hx. left. exact Hx.
  - left. reflexivity.
  - intros rid r H _. exact H.
  - intros rid r H _. exact H.
  - reflexivity.
  - apply N.le_refl.
  - exact C.
  - exact M.
  - intros E. exfalso. exact (E eq_refl).
Qed.

Lemma mmap_len_aligned_eq l : 0 <= l -> l mod PGSZ = 0 -> mmap_len l = l.
Proof. intros H1 H2. apply mmap_len_of_aligned; [exact H1| exact H2]. Qed.

Lemma pcv_of_curi s p : CURI s -> MARITH s -> c_avail_meta_count (s_ctx s) = 0 -> c_init_done (s_ctx s) <> 0 ->
  c_avail_meta_areas (s_ctx s) = Some p -> 1 <= c_avail_meta_area_count (s_ctx s) -> PCV s p.
Proof.
  intros C M H0 Hin EP A1. destruct C as [C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12]. destruct M as [M1 M2 M3 M4 M5 M6].
  destruct C2 as (_ & _ & C2c). destruct p as [rid off]. destruct (C2c rid off EP) as (r & Hr & Kr & Po & Pm & Elen & K0).
  constructor.
  - exact EP.
  - exact A1.
  - exact H0.
  - exact Hin.
  - exists r. cbn [fst snd]. split; [exact Hr|]. split; [exact Kr|]. split; [exact Po|]. split; [exact Pm|]. split; [exact Elen|].
    intros H2. apply K0. lia.
  - exact C1.
  - exact C4.
  - exact C5.
  - exact C6.
  - exact C7.
  - intros rid' r' H K. left. exact (C3 rid' r' H K).
  - exact C8.
  - exact C10.
  - exact M1.
  - exact M2.
  - lia.
  - exact M4.
  - intros rid' r' H K. pose proof (M5 rid' r' H K). unfold PGSZ in *. lia.
  - rewrite H0 in M6. lia.
Qed.

Lemma am_D T s LS (k : mstate -> optr -> M T) bail c n Q :
  CURI s -> MARITH s -> c_avail_meta_count (s_ctx s) = 0 -> c_init_done (s_ctx s) <> 0 -> lists_ok s LS -> LS LFree = [] ->
  (forall st1 mo c1 n1, AMPOST s LS st1 LS mo (c1 - c) (Z.of_nat n1 - Z.of_nat n) -> (mo <> None -> (Z.of_nat n1 - Z.of_nat n + 2 <= Psi st1 - Psi s)) ->
     apw ecost (k st1 mo) c1 n1 Q) ->
  apw ecost (am_after_brk s true k bail) c n Q.
Proof.
  intros C M Hc0 Hin LO FE CONT.
  pose proof (cu_cursor _ C) as (CU1 & CU2 & CU3).

  assert (FIN : forall s2 p c2 n2, c_avail_meta_areas (s_ctx s2) = Some p -> PCV s2 p ->
                  s_metas s2 = s_metas s -> s_groups s2 = s_groups s -> s_slots s2 = s_slots s -> (forall h, get_head s2 h = get_head s h) ->
                  (forall sc, usage s2 sc = usage s sc) -> c_bounces (s_ctx s2) = c_bounces (s_ctx s) -> c_seq (s_ctx s2) = c_seq (s_ctx s) ->
                  c_unmap_seq (s_ctx s2) = c_unmap_seq (s_ctx s) -> c_mmap_counter (s_ctx s2) = c_mmap_counter (s_ctx s) ->
                  nareas s2 = nareas s ->
                  (forall rid r, s_regions s !! rid = Some r -> r_kind r <> RKBrk -> s_regions s2 !! rid = Some r) ->
                  (forall rid r, s_regions s2 !! rid = Some r -> r_kind r = RKGroup -> s_regions s !! rid = Some r) ->
                  ngreg s2 = ngreg s -> (s_next_rid s <= s_next_rid s2)%N ->
                  c2 - c <= Phi s2 - Phi s -> (Z.of_nat n2 - Z.of_nat n <= 1) -> CURI s2 -> MARITH s2 ->
                  apw ecost (am_finish s2 true k bail) c2 n2 Q).
  { intros s2 p c2 n2 EP PC EM EG ES EH EU EB ESQ EUN EMC ENA ER ERG EGR ERID DC DN C2 M2.
    unfold am_finish, ctx. rewrite EP.
    assert (Pm : snd p mod PGSZ = 0) by (destruct (pc_reg _ _ PC) as (r & _ & _ & _ & H & _); exact H).
    rewrite Pm. cbn [Z.eqb negb]. apply apw_vis. intros r.
    destruct (mprotect_answer_ok r); cbn [negb]; [| apply apw_bad].
    destruct ((r =? 0) || (r =? TWO64 - ENOSYS)).
    - rewrite ct_eq. apply CONT.
      + apply (ampost_ct s LS s2 p); auto; cbn [ecost] in *; lia.
      + intros _. destruct (ct_post s2 p PC) as (_ & _ & _ & _ & _ & NAt & _). pose proof (ct_same s2 p) as (_ & _ & R1 & _).
        unfold Psi. rewrite NAt, ENA, !ngreg_regsum, (regsum_ext _ _ _ R1), <- !ngreg_regsum, EGR. lia.
    - apply CONT; [| intros E; exfalso; exact (E eq_refl)].
      assert (LO2 : lists_ok s2 LS) by (apply (lists_ok_same_metas s s2 LS LO EM EH)).
      constructor; auto.
      + intros x. unfold MR, get_meta_rec. rewrite EM. reflexivity.
      + intros sc. exact (EH (LActive sc)).
      + intros m Em; discriminate.
      + intros x Hx. rewrite EM. exact Hx.
      + intros x Hx. left. rewrite <- EM. exact Hx.
      + left. unfold nmeta. rewrite EM. reflexivity.
      + intros E. exfalso. exact (E eq_refl). }
  unfold am_after_brk, ctx.
  destruct (Z.eqb_spec (c_avail_meta_area_count (s_ctx s)) 0) as [A0|A0].
  -
    set (nn := Z.shiftl 2 (c_meta_alloc_shift (s_ctx s))).
    assert (Enn : nn = 2 ^ (c_meta_alloc_shift (s_ctx s) + 1)) by (apply pow2_shift_succ; exact (ma_shnn _ M)).
    apply apw_vis. intros r. destruct (mmap_answer_ok (live_ranges s) (nn * PGSZ) r) eqn:ANS; cbn [negb]; [| apply apw_bad].
    destruct (is_err r) eqn:ERR.
    + apply CONT; [apply ampost_refl; assumption| intros E; exfalso; exact (E eq_refl)].
    + cbv zeta. unfold new_region. cbv zeta.
      set (rid := s_next_rid s).
      set (st1 := set_next_rid (N.succ rid) (set_regions (<[rid := mkRegion RKMeta r (nn * PGSZ)]> (s_regions s)) s)).
      set (st2 := upd_ctx (fun c0 => set_meta_alloc_shift (c_meta_alloc_shift c0 + 1)
                                   (set_avail_meta_area_count (nn - 1) (set_avail_meta_areas (Some (rid, PGSZ)) c0))) st1).
      assert (Nrid : s_regions s !! rid = None).
      { destruct (s_regions s !! rid) as [r0|] eqn:E; [| reflexivity]. pose proof (cu_ids _ C rid r0 E). unfold rid in *. lia. }
      assert (R2 : s_regions st2 = <[rid := mkRegion RKMeta r (nn * PGSZ)]> (s_regions s)) by reflexivity.
      assert (L2 : forall q, s_regions st2 !! q = if (q =? rid)%N then Some (mkRegion RKMeta r (nn * PGSZ)) else s_regions s !! q).
      { intros q. rewrite R2. destruct (N.eqb_spec q rid) as [->|NE]; [apply lookup_insert_eq| rewrite lookup_insert_ne by congruence; reflexivity]. }
      pose proof (ma_shnn _ M) as SHN.
      assert (NN2 : 2 <= nn) by (rewrite Enn; assert (1 <= 2 ^ c_meta_alloc_shift (s_ctx s)) by (pose proof (Z.pow_pos_nonneg 2 (c_meta_alloc_shift (s_ctx s)) ltac:(lia) SHN); lia); rewrite Z.pow_add_r by lia; lia).
      assert (FR2 : forall q r0, frontier st2 q r0 = if (rid =? q)%N then PGSZ else r_len r0) by (intros; reflexivity).
      assert (FRs : forall q r0, s_regions s !! q = Some r0 -> frontier s q r0 = r_len r0).
      { intros q r0 Hq. unfold frontier. destruct (c_avail_meta_areas (s_ctx s)) as [[q0 o0]|] eqn:EC; [| reflexivity].
        destruct (CU3 q0 o0 eq_refl) as (r1 & Hr1 & _ & _ & _ & E1 & _). destruct (N.eqb_spec q0 q) as [->|NE]; [| reflexivity].
        rewrite Hq in Hr1. injection Hr1 as <-. rewrite A0 in E1. lia. }
      assert (C2 : CURI st2).
      { destruct C as [C1 Cc C3 C4 C5 C6 C7 C8 C9 C10 C11 C12]. constructor.
        - intros q r0 H. rewrite L2 in H. cbn [s_next_rid st2 st1 upd_ctx set_next_rid]. destruct (N.eqb_spec q rid) as [->|NE]; [lia|].
          pose proof (C1 q r0 H). lia.
        - cbn. split; [lia|]. split; [discriminate|]. intros q o E. injection E as <- <-. exists (mkRegion RKMeta r (nn * PGSZ)).
          rewrite L2, N.eqb_refl. cbn. split; [reflexivity|]. split; [right; reflexivity|]. unfold PGSZ. split; [lia|]. split; [reflexivity|].
          split; [lia| reflexivity].
        - intros q r0 H K. rewrite L2 in H. rewrite FR2. destruct (N.eqb_spec q rid) as [->|NE].
          + injection H as <-. discriminate.
          + destruct (N.eqb_spec rid q) as [E|_]; [congruence|]. reflexivity.
        - cbn. destruct (c_brk (s_ctx s)); [intros q r0 H; rewrite L2 in H; destruct (N.eqb_spec q rid) as [->|NE]; [injection H as <-; discriminate| exact (C4 q r0 H)]| exact I|].
          destruct C4 as (r0 & H0 & K0 & E0). exists r0. rewrite L2. destruct (N.eqb_spec rid0 rid) as [->|NE]; [rewrite Nrid in H0; discriminate|]. auto.
        - intros q1 q2 r1 r2 H1 H2 K1 K2. rewrite L2 in H1, H2.
          destruct (N.eqb_spec q1 rid) as [->|NE1]; [injection H1 as <-; discriminate|]. destruct (N.eqb_spec q2 rid) as [->|NE2]; [injection H2 as <-; discriminate|].
          exact (C5 q1 q2 r1 r2 H1 H2 K1 K2).
        - intros q r0 H. rewrite L2 in H. destruct (N.eqb_spec q rid) as [->|NE]; [injection H as <-; cbn; unfold PGSZ; split; [lia|]; intros _; split; [rewrite Z.mod_mul by lia; reflexivity| lia]| exact (C6 q r0 H)].
        - intros a ar H. cbn in H. destruct (C7 a ar H) as (r0 & H0 & K0 & Am & Ap & Af). exists r0. rewrite L2.
          destruct (N.eqb_spec (fst a) rid) as [E|NE]; [rewrite <- E, H0 in Nrid; discriminate|]. split; [exact H0|]. split; [exact K0|]. split; [exact Am|]. split; [exact Ap|].
          rewrite FR2. destruct (N.eqb_spec rid (fst a)) as [E|_]; [congruence|]. rewrite (FRs (fst a) r0 H0) in Af. exact Af.
        - exact C8.
        - exact C9.
        - exact C10.
        - exact C11.
        - exact C12. }
      assert (M2 : MARITH st2).
      { destruct M as [M1 Mp Ms Mm Mb Mc]. constructor; cbn [s_ctx st2 st1 upd_ctx set_next_rid set_regions set_meta_alloc_shift set_avail_meta_area_count set_avail_meta_areas
                                                c_meta_alloc_shift c_avail_meta_area_count c_avail_meta_count].
        - lia.
        - unfold nareas in *. cbn. rewrite <- Enn. lia.
        - unfold nareas in *. cbn. rewrite Z.pow_add_r by lia. rewrite A0 in Mp. lia.
        - rewrite (regsum_insert_fresh metalen s st2 rid _ Nrid R2). cbn [metalen r_kind r_len].
          assert (E2 : 2 ^ (c_meta_alloc_shift (s_ctx s) + 1) = 2 * 2 ^ c_meta_alloc_shift (s_ctx s)) by (rewrite Z.pow_add_r by lia; lia).
          rewrite E2. rewrite Enn, E2. unfold PGSZ in *. lia.
        - intros q r0 H K. rewrite L2 in H. destruct (N.eqb_spec q rid) as [->|NE]; [injection H as <-; discriminate|]. unfold nareas in *. cbn. exact (Mb q r0 H K).
        - unfold nareas, nmeta in *. cbn. exact Mc. }
      apply (FIN st2 (rid, PGSZ) _ (S n)); try reflexivity; auto.
      * apply pcv_of_curi; auto. cbn. lia.
      * intros q r0 H K. rewrite L2. destruct (N.eqb_spec q rid) as [->|NE]; [rewrite Nrid in H; discriminate| exact H].
      * intros q r0 H K. rewrite L2 in H. destruct (N.eqb_spec q rid) as [->|NE]; [injection H as <-; discriminate| exact H].
      * rewrite !ngreg_regsum. rewrite (regsum_insert_fresh isgreg s st2 rid _ Nrid R2). cbn. lia.
      * cbn. unfold rid. lia.
      * assert (PH : Phi st2 = Phi s + nn * PGSZ).
        { rewrite !Phi_regsum, (regsum_insert_fresh wreg s st2 rid _ Nrid R2). cbn [wreg r_kind r_len].
          change (brk_dead_w st2) with (brk_dead_w s). lia. }
        rewrite PH. cbn [ecost]. replace (is_fixed (MAP_PRIVATE + MAP_ANON)) with false by reflexivity.
        rewrite mmap_len_aligned_eq; [lia| unfold PGSZ; lia| unfold PGSZ; rewrite Z.mod_mul by lia; reflexivity].
      * rewrite Nat2Z.inj_succ. lia.
  -
    destruct (c_avail_meta_areas (s_ctx s)) as [p|] eqn:EP; [| exfalso; apply CU2; [lia| reflexivity]].
    apply (FIN s p c n); try reflexivity; auto.
    + apply pcv_of_curi; auto. lia.
    + lia.
    + lia.
Qed.

Record CTXONLY (s s' : mstate) : Prop := mkCO {
  co_metas : s_metas s' = s_metas s;
  co_groups : s_groups s' = s_groups s;
  co_slots : s_slots s' = s_slots s;
  co_regions : s_regions s' = s_regions s;
  co_areas : s_areas s' = s_areas s;
  co_rid : s_next_rid s' = s_next_rid s;
  co_active : c_active (s_ctx s') = c_active (s_ctx s);
  co_usage : c_usage (s_ctx s') = c_usage (s_ctx s);
  co_fmh : c_free_meta_head (s_ctx s') = c_free_meta_head (s_ctx s);
  co_other : c_bounces (s_ctx s') = c_bounces (s_ctx s) /\ c_seq (s_ctx s') = c_seq (s_ctx s)
             /\ c_unmap_seq (s_ctx s') = c_unmap_seq (s_ctx s) /\ c_mmap_counter (s_ctx s') = c_mmap_counter (s_ctx s)
}.

Lemma ampost_pre s s' LS st1 LS1 mo dc dn dc' dn' : CTXONLY s s' -> AMPOST s' LS st1 LS1 mo dc dn ->
  (mo <> None -> dc' <= dc + (Phi s' - Phi s) /\ dn' <= Psi st1 - Psi s) -> AMPOST s LS st1 LS1 mo dc' dn'.
Proof.
  intros [E1 E2 E3 E4 E5 E6 E7 E8 E9 (E10 & E11 & E12 & E13)] [P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19 P20] D.
  assert (MRe : forall x, MR s' x = MR s x) by (intros x; unfold MR, get_meta_rec; rewrite E1; reflexivity).
  assert (NMe : nmeta s' = nmeta s) by (unfold nmeta; rewrite E1; reflexivity).
  assert (PSe : Psi s' = Psi s) by (unfold Psi, nareas; rewrite !ngreg_regsum, (regsum_ext _ _ _ E4), E5; reflexivity).
  constructor.
  - rewrite P1. exact E2.
  - rewrite P2. exact E3.
  - intros x. rewrite P3, MRe. reflexivity.
  - intros sc. rewrite P4. unfold active, ctx. rewrite E7. reflexivity.
  - intros sc. rewrite P5. unfold usage, ctx. rewrite E8. reflexivity.
  - destruct P6 as (Q1 & Q2 & Q3 & Q4). rewrite Q1, Q2, Q3, Q4. auto.
  - exact P7.
  - exact P8.
  - exact P9.
  - intros m Hm. destruct (P10 m Hm) as (R1 & R2 & R3 & R4). rewrite E1 in R4. auto.
  - intros x Hx. apply P11. rewrite E1. exact Hx.
  - intros x Hx. rewrite <- E1. exact (P12 x Hx).
  - rewrite <- NMe. exact P13.
  - intros rid r H K. apply P14; [rewrite E4; exact H| exact K].
  - intros rid r H K. rewrite <- E4. exact (P15 rid r H K).
  - rewrite P16. rewrite !ngreg_regsum, (regsum_ext _ _ _ E4). reflexivity.
  - rewrite <- E6. exact P17.
  - exact P18.
  - exact P19.
  - intros Hm. destruct (P20 Hm) as [C1 C2]. destruct (D Hm) as [D1 D2]. split; [lia| exact D2].
Qed.

Lemma Psi_ctxonly s s' : CTXONLY s s' -> Psi s' = Psi s.
Proof. intros CO. unfold Psi, nareas. rewrite !ngreg_regsum, (regsum_ext _ _ _ (co_regions _ _ CO)), (co_areas _ _ CO). reflexivity. Qed.

Definition ami (st : mstate) : mstate :=
  if c_init_done (ctx st) =? 0 then upd_ctx (fun c => set_init_done 1 (set_secret (s_secret st) c)) st else st.

Lemma ami_facts st : CURI st -> MARITH st ->
  CTXONLY st (ami st) /\ CURI (ami st) /\ MARITH (ami st) /\ c_init_done (s_ctx (ami st)) <> 0 /\ Phi (ami st) = Phi st
  /\ (forall h, get_head (ami st) h = get_head st h)
  /\ c_avail_meta_count (s_ctx (ami st)) = c_avail_meta_count (s_ctx st) /\ c_avail_meta_area_count (s_ctx (ami st)) = c_avail_meta_area_count (s_ctx st)
  /\ c_brk (s_ctx (ami st)) = c_brk (s_ctx st).
Proof.
  intros C M. unfold ami, ctx. destruct (Z.eqb_spec (c_init_done (s_ctx st)) 0) as [E|E].
  - split; [constructor; try reflexivity; repeat split; reflexivity|].
    split; [| split; [| split; [cbn; discriminate| split; [reflexivity| split; [intros h; destruct h; reflexivity| repeat split]]]]].
    + destruct C as [C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12]. constructor; try assumption. cbn. discriminate.
    + destruct M; constructor; assumption.
  - split; [constructor; try reflexivity; repeat split; reflexivity|].
    split; [exact C|]. split; [exact M|]. split; [exact E|]. split; [reflexivity|]. split; [intros h; reflexivity|]. repeat split.
Qed.

Lemma brkdead_facts s : CURI s -> MARITH s -> c_brk (s_ctx s) <> BrkDead ->
  let s' := upd_ctx (set_brk BrkDead) s in
  CTXONLY s s' /\ CURI s' /\ MARITH s' /\ Phi s' = Phi s + 2 * PGSZ /\ (forall h, get_head s' h = get_head s h)
  /\ c_avail_meta_count (s_ctx s') = c_avail_meta_count (s_ctx s) /\ c_init_done (s_ctx s') = c_init_done (s_ctx s).
Proof.
  intros C M NB. cbn zeta. split; [constructor; try reflexivity; repeat split; reflexivity|].
  split; [| split; [| split; [| split; [intros h; destruct h; reflexivity| split; reflexivity]]]].
  - destruct C as [C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12]. constructor; try assumption. cbn. exact I.
  - destruct M; constructor; assumption.
  - rewrite !Phi_regsum, (regsum_ext wreg (upd_ctx (set_brk BrkDead) s) s eq_refl). unfold brk_dead_w. cbn [s_ctx upd_ctx set_brk c_brk]. destruct (c_brk (s_ctx s)); [unfold PGSZ; lia| congruence| unfold PGSZ; lia].
Qed.

Theorem am_walk T st LS (k : mstate -> optr -> M T) bail c n Q :
  AMPRE st LS ->
  (forall st1 LS1 mo c1 n1, AMPOST st LS st1 LS1 mo (c1 - c) (Z.of_nat n1 - Z.of_nat n) -> apw ecost (k st1 mo) c1 n1 Q) ->
  apw ecost (alloc_meta st k bail) c n Q.
Proof.
  intros (C & M & LO & FD) CONT.
  destruct (ami_facts st C M) as (CO & C1 & M1 & IN1 & PH1 & HD1 & AMC1 & AMAC1 & BR1).
  assert (LO1 : lists_ok (ami st) LS) by (apply (lists_ok_same_metas st (ami st) LS LO (co_metas _ _ CO) HD1)).

  assert (LIFT : forall st1 LS1 mo c1 n1, AMPOST (ami st) LS st1 LS1 mo (c1 - c) (Z.of_nat n1 - Z.of_nat n) ->
                   apw ecost (k st1 mo) c1 n1 Q).
  { intros st1 LS1 mo c1 n1 P. apply (CONT st1 LS1 mo c1 n1). apply (ampost_pre st (ami st) LS st1 LS1 mo _ _ _ _ CO P).
    intros Hm. destruct (ap_cost _ _ _ _ _ _ _ P Hm) as [_ D2]. rewrite PH1, <- (Psi_ctxonly _ _ CO). split; [lia| exact D2]. }
  unfold alloc_meta. fold (ami st). set (s := ami st) in *.
  change (c_free_meta_head (ctx s)) with (get_head s LFree).
  destruct (get_head s LFree) as [m|] eqn:FH.
  -
    pose proof (lo_head _ _ LO1 LFree) as EH. rewrite FH in EH.
    destruct (LS LFree) as [|m' rest] eqn:ELF; [discriminate|]. injection EH as <-.
    assert (Min : In m (LS LFree)) by (rewrite ELF; left; reflexivity).
    pose proof (lists_dequeue s LS LO1 LFree m [] rest ltac:(rewrite ELF; reflexivity)) as LOd. cbn [app] in LOd.
    set (sd := dequeue LFree m s) in *.
    destruct (dequeue_frame LFree m s) as (D1 & _ & D3 & D4 & D5 & D6 & _ & _ & _ & D10). fold sd in D1, D3, D4, D5, D6, D10.
    assert (Pm : s_metas s !! m <> None) by (apply present_of_next; exact (lists_in_next_some _ _ LO1 _ m Min)).
    assert (PRES : forall x, s_metas sd !! x <> None -> s_metas s !! x <> None).
    { intros x Hx. destruct (dequeue_keys LFree m s x Hx) as [H|[->|[H|H]]]; [exact H| exact Pm| |].
      - destruct (lists_prev_in _ _ LO1 _ m Min) as (y & Hy & Ey & _). fold (MR s m) in H. rewrite H in Ey. injection Ey as <-.
        apply present_of_next. exact (lists_in_next_some _ _ LO1 _ x Hy).
      - destruct (lists_next_in _ _ LO1 _ m Min) as (y & Hy & Ey & _). fold (MR s m) in H. rewrite H in Ey. injection Ey as <-.
        apply present_of_next. exact (lists_in_next_some _ _ LO1 _ x Hy). }
    assert (MF : MFR s sd).
    { constructor; try (apply D10); auto.
      intros x. split.
      - intros Hx. destruct (s_metas s !! x) eqn:E; [| reflexivity]. exfalso. apply (dequeue_keys_mono LFree m s x) in Hx; [exact Hx| rewrite E; discriminate].
      - intros Hx. destruct (s_metas sd !! x) eqn:E; [| reflexivity]. exfalso. apply (PRES x); [rewrite E; discriminate| exact Hx]. }
    apply (LIFT _ (fupd LS LFree rest) _ c n).
    assert (MRm : MR sd m = meta0).
    { pose proof (dequeue_data LFree m s m) as Dd. pose proof (dequeue_next LFree m s m) as Dn. pose proof (dequeue_prev LFree m s m) as Dp.
      rewrite aptr_eqb_refl in Dn, Dp. fold sd in Dd, Dn, Dp. assert (MRe : MR s m = MR st m) by (unfold MR, get_meta_rec; rewrite (co_metas _ _ CO); reflexivity). rewrite MRe, (FD m ltac:(first [exact Min | left; reflexivity])) in Dd.
      destruct (MR sd m) as [a1 a2 a3 a4 a5 a6 a7 a8 a9]. unfold data_of, meta0 in *. cbn in Dd, Dn, Dp. inversion Dd. subst. reflexivity. }
    assert (NDr : ~ In m rest).
    { pose proof (lo_nodup _ _ LO1 LFree) as ND. rewrite ELF in ND. apply NoDup_cons in ND as [N _]. intros X. apply N. apply list_elem_of_In. exact X. }
    constructor.
    + exact D5.
    + exact D6.
    + intros x. apply dequeue_data.
    + intros sc. change (active sd sc) with (get_head sd (LActive sc)). rewrite dequeue_head. destruct (decide (LActive sc = LFree)); [discriminate| reflexivity].
    + intros sc. unfold usage. rewrite (cb_usage _ _ D10). reflexivity.
    + rewrite (cb_bounces _ _ D10), (cb_seq _ _ D10), (cb_unmap _ _ D10), (cb_mc _ _ D10). auto.
    + exact LOd.
    + intros sc. rewrite fupd_ne by discriminate. reflexivity.
    + right. exists m. rewrite fupd_eq. split; [exact ELF| reflexivity].
    + intros m2 Em. injection Em as <-. split; [exact MRm|]. split.
      * intros h Hh. destruct (decide (h = LFree)) as [->|NEh]; [rewrite fupd_eq in Hh; exact (NDr Hh)|].
        rewrite fupd_ne in Hh by exact NEh. exact (NEh (lo_disj _ _ LO1 h LFree m Hh Min)).
      * split; [apply dequeue_key_m|]. left. rewrite ELF. reflexivity.
    + intros x Hx. apply dequeue_keys_mono. exact Hx.
    + intros x Hx. left. exact (PRES x Hx).
    + left. apply (nmeta_dequeue s LS LFree m LO1 Min).
    + intros rid r H _. rewrite D1. exact H.
    + intros rid r H _. rewrite D1 in H. exact H.
    + rewrite !ngreg_regsum, (regsum_ext _ _ _ D1). reflexivity.
    + fold sd. destruct (dequeue_frame LFree m s) as (_ & _ & D3' & _). rewrite D3'. apply N.le_refl.
    + exact (CURI_frame s sd C1 MF).
    + exact (MARITH_frame s sd M1 MF).
    + intros _. rewrite !Phi_regsum, (regsum_ext _ _ _ D1). unfold Psi, nareas. rewrite !ngreg_regsum, (regsum_ext _ _ _ D1), D4.
      unfold brk_dead_w. rewrite (cb_brk _ _ D10). lia.
  - assert (FE : LS LFree = []) by (pose proof (lo_head _ _ LO1 LFree) as E; rewrite FH in E; destruct (LS LFree); [reflexivity| discriminate]).
    unfold ctx. destruct (Z.eqb_spec (c_avail_meta_count (s_ctx s)) 0) as [Z0|Z0]; cbn [negb].
    + set (brk_dead := match c_brk (s_ctx s) with BrkDead => true | _ => false end).
      destruct ((c_avail_meta_area_count (s_ctx s) =? 0) && negb brk_dead) eqn:BD.
      * destruct (c_brk (s_ctx s)) as [ | | rid off] eqn:EB.
        --
           apply Bool.andb_true_iff in BD as [A0 _]. apply Z.eqb_eq in A0.
           assert (DEAD : forall c' n', c' = c + 2 * PGSZ -> (n' = S (S n))%nat ->
                     apw ecost (am_after_brk (upd_ctx (set_brk BrkDead) s) true k bail) c' n' Q).
           { intros c' n' -> ->. destruct (brkdead_facts s C1 M1 ltac:(rewrite EB; discriminate)) as (CO2 & C2 & M2 & PH2 & HD2 & AMC2 & IN2).
             apply (am_D T _ LS k bail _ _ Q C2 M2 ltac:(rewrite AMC2; exact Z0) ltac:(rewrite IN2; exact IN1)
                      (lists_ok_same_metas s _ LS LO1 (co_metas _ _ CO2) HD2) FE).
             intros st1 mo c1 n1 P EXT. apply (LIFT st1 LS mo c1 n1).
             apply (ampost_pre s _ LS st1 LS mo _ _ _ _ CO2 P). intros Hm. rewrite PH2, <- (Psi_ctxonly _ _ CO2). specialize (EXT Hm).
             split; [lia|]. rewrite !Nat2Z.inj_succ in EXT. lia. }
           apply apw_vis. intros cur. destruct (brk0_answer_ok cur) eqn:B0; cbn [negb]; [| apply apw_bad].
           apply apw_vis. intros r. destruct (brk_answer_ok cur (round_up_pg cur + 2 * PGSZ) r) eqn:B1; cbn [negb]; [| apply apw_bad].
           assert (NZ : (round_up_pg cur + 2 * PGSZ =? 0) = false).
           { apply Z.eqb_neq. unfold brk0_answer_ok in B0. apply Bool.andb_true_iff in B0 as [B0 _]. apply Bool.andb_true_iff in B0 as [B0 _].
             apply Z.ltb_lt in B0. unfold round_up_pg.
             assert (HL : 0 <= Z.land (- cur) (PGSZ - 1)) by (apply Z.land_nonneg; right; unfold PGSZ; lia). set (q := Z.land (- cur) (PGSZ - 1)) in *. clearbody q. unfold PGSZ in *. lia. }
           destruct (Z.eqb_spec r (round_up_pg cur + 2 * PGSZ)) as [Er|Nr]; cbn [negb].
           ++ destruct (brk_pages_ok s (round_up_pg cur) (2 * PGSZ)) eqn:BP; cbn [negb]; [| apply apw_bad].
              apply apw_vis. intros rg. destruct (mmap_fixed_answer_ok (round_up_pg cur) rg) eqn:GF; cbn [negb]; [| apply apw_bad].
              unfold new_region. cbv zeta.
              set (rid := s_next_rid s).
              set (base := round_up_pg cur).
              set (st2 := upd_ctx (fun c0 => set_avail_meta_area_count 1 (set_avail_meta_areas (Some (rid, PGSZ)) (set_brk (BrkLive rid (2 * PGSZ)) c0)))
                            (set_next_rid (N.succ rid) (set_regions (<[rid := mkRegion RKBrk base (2 * PGSZ)]> (s_regions s)) s))).
              assert (Nrid : s_regions s !! rid = None).
              { destruct (s_regions s !! rid) as [r0|] eqn:E; [| reflexivity]. pose proof (cu_ids _ C1 rid r0 E). unfold rid in *. lia. }
              assert (R2 : s_regions st2 = <[rid := mkRegion RKBrk base (2 * PGSZ)]> (s_regions s)) by reflexivity.
              assert (L2 : forall q, s_regions st2 !! q = if (q =? rid)%N then Some (mkRegion RKBrk base (2 * PGSZ)) else s_regions s !! q).
              { intros q. rewrite R2. destruct (N.eqb_spec q rid) as [->|NE]; [apply lookup_insert_eq| rewrite lookup_insert_ne by congruence; reflexivity]. }
              pose proof (cu_cursor _ C1) as (_ & _ & CU3).
              assert (FRs : forall q r0, s_regions s !! q = Some r0 -> frontier s q r0 = r_len r0).
              { intros q r0 Hq. unfold frontier. destruct (c_avail_meta_areas (s_ctx s)) as [[q0 o0]|] eqn:EC; [| reflexivity].
                destruct (CU3 q0 o0 eq_refl) as (r1 & Hr1 & _ & _ & _ & E1 & _). destruct (N.eqb_spec q0 q) as [->|NE]; [| reflexivity].
                rewrite Hq in Hr1. injection Hr1 as <-. rewrite A0 in E1. lia. }
              unfold am_after_brk. change (c_avail_meta_area_count (ctx st2)) with 1. cbn [Z.eqb Pos.eqb].
              unfold am_finish. change (c_avail_meta_areas (ctx st2)) with (Some (rid, PGSZ)). cbn [snd].
              replace (if negb (PGSZ mod PGSZ =? 0) then false else false) with false by reflexivity.
              rewrite ct_eq. apply (LIFT _ LS _ _ _).
              apply (ampost_ct s LS st2 (rid, PGSZ)); try reflexivity.
              ** constructor.
                 --- reflexivity.
                 --- cbn. lia.
                 --- exact Z0.
                 --- exact IN1.
                 --- exists (mkRegion RKBrk base (2 * PGSZ)). cbn [fst snd]. rewrite L2, N.eqb_refl. split; [reflexivity|].
                     split; [left; reflexivity|]. cbn. unfold PGSZ. split; [lia|]. split; [reflexivity|]. split; [lia| lia].
                 --- intros q r0 H. rewrite L2 in H. cbn. destruct (N.eqb_spec q rid) as [->|NE]; [lia|]. pose proof (cu_ids _ C1 q r0 H). unfold rid in *. lia.
                 --- cbn. exists (mkRegion RKBrk base (2 * PGSZ)). rewrite L2, N.eqb_refl. auto.
                 --- intros q1 q2 r1 r2 H1 H2 K1 K2. pose proof (cu_brk _ C1) as CB. rewrite EB in CB. rewrite L2 in H1, H2.
                     destruct (N.eqb_spec q1 rid) as [->|NE1]; destruct (N.eqb_spec q2 rid) as [->|NE2]; auto;
                       [exfalso; exact (CB q2 r2 H2 K2)| exfalso; exact (CB q1 r1 H1 K1)| exfalso; exact (CB q1 r1 H1 K1)].
                 --- intros q r0 H. rewrite L2 in H. destruct (N.eqb_spec q rid) as [->|NE]; [injection H as <-; cbn; unfold PGSZ; split; [lia| intros _; split; [reflexivity| lia]]| exact (cu_shape _ C1 q r0 H)].
                 --- intros a ar H. cbn in H. destruct (cu_areas _ C1 a ar H) as (r0 & H0 & K0 & Am & Ap & Af). exists r0. rewrite L2.
                     destruct (N.eqb_spec (fst a) rid) as [E|NE]; [rewrite <- E, H0 in Nrid; discriminate|]. split; [exact H0|]. split; [exact K0|]. split; [exact Am|]. split; [exact Ap|].
                     unfold frontier. cbn. destruct (N.eqb_spec rid (fst a)) as [E|_]; [congruence|]. rewrite (FRs (fst a) r0 H0) in Af. exact Af.
                 --- intros q r0 H K. rewrite L2 in H. destruct (N.eqb_spec q rid) as [->|NE]; [right; split; reflexivity|].
                     exfalso. pose proof (cu_brk _ C1) as CB. rewrite EB in CB. exact (CB q r0 H K).
                 --- intros t H. exact (cu_tail _ C1 t H).
                 --- intros m mr H. exact (cu_metas _ C1 m mr H).
                 --- exact (ma_shnn _ M1).
                 --- pose proof (ma_poti _ M1) as P. change (nareas st2) with (nareas s). cbn [s_ctx st2 upd_ctx]. cbn. lia.
                 --- pose proof (ma_shi _ M1) as P. change (nareas st2) with (nareas s). cbn. lia.
                 --- rewrite (regsum_insert_fresh metalen s st2 rid _ Nrid R2). cbn [metalen r_kind]. pose proof (ma_mbi _ M1). cbn. lia.
                 --- intros q r0 H K. rewrite L2 in H. destruct (N.eqb_spec q rid) as [->|NE].
                     +++ injection H as <-. cbn [r_len]. change (nareas st2) with (nareas s). assert (0 <= nareas s) by (unfold nareas; lia). unfold PGSZ. lia.
                     +++ pose proof (ma_brki _ M1 q r0 H K). change (nareas st2) with (nareas s). unfold PGSZ in *. lia.
                 --- pose proof (ma_cnti _ M1) as P. rewrite Z0 in P. change (nareas st2) with (nareas s). change (nmeta st2) with (nmeta s). lia.
              ** exact LO1.
              ** exact FE.
              ** intros q r0 H K. rewrite L2. destruct (N.eqb_spec q rid) as [->|NE]; [rewrite Nrid in H; discriminate| exact H].
              ** intros q r0 H K. rewrite L2 in H. destruct (N.eqb_spec q rid) as [->|NE]; [injection H as <-; discriminate| exact H].
              ** rewrite !ngreg_regsum, (regsum_insert_fresh isgreg s st2 rid _ Nrid R2). cbn. lia.
              ** cbn. unfold rid. lia.
              ** rewrite !Phi_regsum, (regsum_insert_fresh wreg s st2 rid _ Nrid R2). cbn [wreg r_kind r_len ecost].
                 change (brk_dead_w st2) with 0. unfold brk_dead_w. rewrite EB. rewrite NZ, Z.eqb_refl.
                 replace (is_fixed (MAP_PRIVATE + MAP_ANON + MAP_FIXED)) with true by reflexivity. unfold PGSZ. lia.
              ** lia.
           ++ apply DEAD; [cbn [ecost]; rewrite NZ, Z.eqb_refl; lia| reflexivity].
        -- apply (am_D T s LS k bail c n Q C1 M1 Z0 IN1 LO1 FE). intros st1 mo c1 n1 P _. apply (LIFT st1 LS mo c1 n1). exact P.
        --
           apply Bool.andb_true_iff in BD as [A0 _]. apply Z.eqb_eq in A0.
           pose proof (cu_brk _ C1) as CB. rewrite EB in CB. destruct CB as (rb & Hrb & Krb & Lrb).
           assert (ECOST : forall z, 0 <= ecost (EBrk z) <= 2 * PGSZ) by (intros z; cbn [ecost]; destruct (z =? 0); unfold PGSZ; lia).
           assert (DEAD : forall c' n', c <= c' <= c + 2 * PGSZ -> (n' = S n)%nat ->
                     apw ecost (am_after_brk (upd_ctx (set_brk BrkDead) s) true k bail) c' n' Q).
           { intros c' n' Hc' ->. destruct (brkdead_facts s C1 M1 ltac:(rewrite EB; discriminate)) as (CO2 & C2 & M2 & PH2 & HD2 & AMC2 & IN2).
             apply (am_D T _ LS k bail _ _ Q C2 M2 ltac:(rewrite AMC2; exact Z0) ltac:(rewrite IN2; exact IN1)
                      (lists_ok_same_metas s _ LS LO1 (co_metas _ _ CO2) HD2) FE).
             intros st1 mo c1 n1 P EXT. apply (LIFT st1 LS mo c1 n1).
             apply (ampost_pre s _ LS st1 LS mo _ _ _ _ CO2 P). intros Hm. rewrite PH2, <- (Psi_ctxonly _ _ CO2). specialize (EXT Hm).
             split; [lia|]. rewrite !Nat2Z.inj_succ in EXT. lia. }
           apply apw_vis. intros r. destruct (brk_answer_ok (conc s (rid, off)) (conc s (rid, off) + PGSZ) r) eqn:B1; cbn [negb]; [| apply apw_bad].
           destruct (Z.eqb_spec r (conc s (rid, off) + PGSZ)) as [Er|Nr]; cbn [negb].
           ++ destruct (brk_pages_ok s (conc s (rid, off)) PGSZ) eqn:BP; cbn [negb]; [| apply apw_bad].
              set (rn := mkRegion RKBrk (r_base rb) (off + PGSZ)).
              assert (Eu : upd_region rid (fun rg => mkRegion (r_kind rg) (r_base rg) (off + PGSZ)) s = set_regions (<[rid := rn]> (s_regions s)) s).
              { unfold upd_region, get_region. rewrite Hrb. unfold rn. rewrite Krb. reflexivity. }
              rewrite Eu.
              set (st2 := upd_ctx (fun c0 => set_avail_meta_area_count 1 (set_avail_meta_areas (Some (rid, off)) (set_brk (BrkLive rid (off + PGSZ)) c0)))
                            (set_regions (<[rid := rn]> (s_regions s)) s)).
              assert (R2 : s_regions st2 = <[rid := rn]> (s_regions s)) by reflexivity.
              assert (L2 : forall q, s_regions st2 !! q = if (q =? rid)%N then Some rn else s_regions s !! q).
              { intros q. rewrite R2. destruct (N.eqb_spec q rid) as [->|NE]; [apply lookup_insert_eq| rewrite lookup_insert_ne by congruence; reflexivity]. }
              pose proof (cu_shape _ C1 rid rb Hrb) as (Sh1 & Sh2). destruct (Sh2 ltac:(left; exact Krb)) as [Smod Sge]. rewrite Lrb in Smod, Sge.
              pose proof (cu_cursor _ C1) as (_ & _ & CU3).
              assert (FRs : forall q r0, s_regions s !! q = Some r0 -> frontier s q r0 = r_len r0).
              { intros q r0 Hq. unfold frontier. destruct (c_avail_meta_areas (s_ctx s)) as [[q0 o0]|] eqn:EC; [| reflexivity].
                destruct (CU3 q0 o0 eq_refl) as (r1 & Hr1 & _ & _ & _ & E1 & _). destruct (N.eqb_spec q0 q) as [->|NE]; [| reflexivity].
                rewrite Hq in Hr1. injection Hr1 as <-. rewrite A0 in E1. lia. }
              unfold am_after_brk. change (c_avail_meta_area_count (ctx st2)) with 1. cbn [Z.eqb Pos.eqb].
              unfold am_finish. change (c_avail_meta_areas (ctx st2)) with (Some (rid, off)). cbn [snd].
              replace (if negb (off mod PGSZ =? 0) then false else false) with false by (destruct (negb _); reflexivity).
              rewrite ct_eq. apply (LIFT _ LS _ _ _).
              apply (ampost_ct s LS st2 (rid, off)); try reflexivity.
              ** constructor.
                 --- reflexivity.
                 --- cbn. lia.
                 --- exact Z0.
                 --- exact IN1.
                 --- exists rn. cbn [fst snd]. rewrite L2, N.eqb_refl. split; [reflexivity|].
                     split; [left; reflexivity|]. unfold rn. cbn. unfold PGSZ in *. split; [lia|]. split; [exact Smod|]. split; [lia| lia].
                 --- intros q r0 H. rewrite L2 in H. change (s_next_rid st2) with (s_next_rid s). destruct (N.eqb_spec q rid) as [->|NE].
                     +++ exact (cu_ids _ C1 rid rb Hrb).
                     +++ exact (cu_ids _ C1 q r0 H).
                 --- cbn. exists rn. rewrite L2, N.eqb_refl. auto.
                 --- intros q1 q2 r1 r2 H1 H2 K1 K2. rewrite L2 in H1, H2.
                     destruct (N.eqb_spec q1 rid) as [->|NE1]; destruct (N.eqb_spec q2 rid) as [->|NE2]; auto.
                     +++ exact (cu_brk1 _ C1 rid q2 rb r2 Hrb H2 Krb K2).
                     +++ exact (cu_brk1 _ C1 q1 rid r1 rb H1 Hrb K1 Krb).
                     +++ exact (cu_brk1 _ C1 q1 q2 r1 r2 H1 H2 K1 K2).
                 --- intros q r0 H. rewrite L2 in H. destruct (N.eqb_spec q rid) as [->|NE].
                     +++ injection H as <-. unfold rn. cbn. unfold PGSZ in *. split; [lia|]. intros _. split; [rewrite Z.add_mod by lia; rewrite Smod; reflexivity| lia].
                     +++ exact (cu_shape _ C1 q r0 H).
                 --- intros a ar H. cbn in H. destruct (cu_areas _ C1 a ar H) as (r0 & H0 & K0 & Am & Ap & Af).
                     destruct (N.eqb_spec (fst a) rid) as [E|NE].
                     +++ exists rn. rewrite L2, E, N.eqb_refl. split; [reflexivity|]. split; [left; reflexivity|]. split; [exact Am|]. split; [exact Ap|].
                         rewrite E, Hrb in H0. injection H0 as <-. rewrite E in Af. rewrite (cu_brkfront _ C1 rid rb Hrb Krb), Lrb in Af.
                         unfold frontier. cbn. rewrite N.eqb_refl. exact Af.
                     +++ exists r0. rewrite L2. destruct (N.eqb_spec (fst a) rid) as [E|_]; [congruence|]. split; [exact H0|]. split; [exact K0|]. split; [exact Am|]. split; [exact Ap|].
                         unfold frontier. cbn. destruct (N.eqb_spec rid (fst a)) as [E|_]; [congruence|]. rewrite (FRs (fst a) r0 H0) in Af. exact Af.
                 --- intros q r0 H K. rewrite L2 in H. destruct (N.eqb_spec q rid) as [->|NE]; [right; split; reflexivity|].
                     exfalso. pose proof (cu_brk1 _ C1 q rid r0 rb H Hrb K Krb). congruence.
                 --- intros t H. exact (cu_tail _ C1 t H).
                 --- intros m mr H. exact (cu_metas _ C1 m mr H).
                 --- exact (ma_shnn _ M1).
                 --- pose proof (ma_poti _ M1) as P. change (nareas st2) with (nareas s). cbn. lia.
                 --- pose proof (ma_shi _ M1) as P. change (nareas st2) with (nareas s). cbn. lia.
                 --- rewrite (regsum_update metalen s st2 rid rb rn Hrb R2). assert (Mrb : metalen rb = 0) by (unfold metalen; rewrite Krb; reflexivity). assert (Mrn : metalen rn = 0) by reflexivity. rewrite Mrb, Mrn. pose proof (ma_mbi _ M1). change (c_meta_alloc_shift (s_ctx st2)) with (c_meta_alloc_shift (s_ctx s)). lia.
                 --- intros q r0 H K. rewrite L2 in H. destruct (N.eqb_spec q rid) as [->|NE].
                     +++ injection H as <-. unfold rn. cbn [r_len]. change (nareas st2) with (nareas s). pose proof (ma_brki _ M1 rid rb Hrb Krb). rewrite Lrb in *. unfold PGSZ in *. lia.
                     +++ pose proof (ma_brki _ M1 q r0 H K). change (nareas st2) with (nareas s). unfold PGSZ in *. lia.
                 --- pose proof (ma_cnti _ M1) as P. rewrite Z0 in P. change (nareas st2) with (nareas s). change (nmeta st2) with (nmeta s). lia.
              ** exact LO1.
              ** exact FE.
              ** intros q r0 H K. rewrite L2. destruct (N.eqb_spec q rid) as [->|NE]; [rewrite Hrb in H; injection H as <-; contradiction| exact H].
              ** intros q r0 H K. rewrite L2 in H. destruct (N.eqb_spec q rid) as [->|NE]; [injection H as <-; discriminate| exact H].
              ** rewrite !ngreg_regsum, (regsum_update isgreg s st2 rid rb rn Hrb R2). unfold rn, isgreg. cbn. rewrite Krb. lia.
              ** rewrite !Phi_regsum, (regsum_update wreg s st2 rid rb rn Hrb R2). unfold rn, wreg. cbn [r_kind r_len]. rewrite Krb, Lrb.
                 assert (BW2 : brk_dead_w st2 = 0) by reflexivity. assert (BW0 : brk_dead_w s = 0) by (unfold brk_dead_w; rewrite EB; reflexivity). rewrite BW2, BW0. pose proof (ECOST (conc s (rid, off) + PGSZ)). unfold PGSZ in *. lia.
              ** lia.
           ++ apply DEAD; [pose proof (ECOST (conc s (rid, off) + PGSZ)); lia| reflexivity].
      * apply (am_D T s LS k bail c n Q C1 M1 Z0 IN1 LO1 FE). intros st1 mo c1 n1 P _. apply (LIFT st1 LS mo c1 n1). exact P.
    +
      destruct (take_post s C1 M1 ltac:(pose proof (proj1 (cu_avail _ C1)); lia)) as (a & TL & AV & CT & MT & MR0 & NM0 & NMt & MRo).
      rewrite (am_take_eq s _ k bail AV). apply (LIFT _ LS _ c n).
      set (m := mslot a (NSLOTS - c_avail_meta_count (s_ctx s))) in *.
      assert (MRs : MR s m = meta0) by (unfold MR, get_meta_rec; rewrite NM0; reflexivity).
      assert (LOt : lists_ok (take_st s m) LS).
      { apply (lists_ok_links s (take_st s m) LS LO1); [intros h; destruct h; reflexivity|].
        intros x. destruct (aptr_eqb_spec x m) as [->|NE]; [rewrite MR0, MRs; split; reflexivity| rewrite (MRo x NE); split; reflexivity]. }
      constructor.
      * apply take_groups.
      * apply take_slots.
      * intros x. destruct (aptr_eqb_spec x m) as [->|NE]; [rewrite MR0, MRs; reflexivity| rewrite (MRo x NE); reflexivity].
      * intros sc. reflexivity.
      * intros sc. reflexivity.
      * repeat split; reflexivity.
      * exact LOt.
      * intros sc. reflexivity.
      * left. reflexivity.
      * intros m' Em. injection Em as <-. split; [exact MR0|]. split; [apply (lists_notin _ _ LOt); rewrite MR0; reflexivity|].
        split; [rewrite take_metas, lookup_insert_eq; discriminate| right; split; [exact NM0| exact FE]].
      * intros x Hx. rewrite take_metas, lookup_insert. destruct (decide (m = x)); [discriminate| exact Hx].
      * intros x Hx. rewrite take_metas in Hx. destruct (aptr_eqb_spec x m) as [->|NE]; [right; reflexivity|].
        left. rewrite lookup_insert_ne in Hx by congruence. exact Hx.
      * right. split; [exact NMt| exact FE].
      * intros rid r H _. rewrite take_regions. exact H.
      * intros rid r H _. rewrite take_regions in H. exact H.
      * rewrite !ngreg_regsum, (regsum_ext _ _ _ (take_regions s m)). reflexivity.
      * rewrite take_next_rid. apply N.le_refl.
      * exact CT.
      * exact MT.
      * intros _. rewrite !Phi_regsum, (regsum_ext _ _ _ (take_regions s m)). unfold Psi, nareas. rewrite !ngreg_regsum, (regsum_ext _ _ _ (take_regions s m)), take_areas.
        change (brk_dead_w (take_st s m)) with (brk_dead_w s). lia.
Qed.

End HMMETA.
