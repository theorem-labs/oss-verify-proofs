(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc Require Import Prelim STree Malloc MallocCtrl KInv
  MI_Inv MI_Kit MI_List MI_Cnt MI_Ledger MI_WAMeta MI_WSlot2 MI_WNtf2 MI_Contracts MF_Phi MF_SiteC.
Unset Lia Cache.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Set Keyed Unification.
Import ListNotations.
Local Open Scope Z_scope.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc Require Export MF_EvolA.
Unset Nia Cache. Unset Nra Cache.

Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Section FIRST_GROUP.
Variables (st1 : mstate) (Mt : aptr) (a2 : Z).
Hypothesis HI : c_init_done (s_ctx st1) = 1.
Hypothesis HC : 50 <= c_avail_meta_count (s_ctx st1).
Hypothesis HF : c_free_meta_head (s_ctx st1) = None.
Hypothesis HA : forall sc, active st1 sc = None.
Hypothesis HG : s_groups st1 = ∅.
Hypothesis HM : s_metas st1 !! Mt = Some meta0.

Definition fg_st4 : mstate :=
  upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c)
          (upd_meta Mt (m_set_maplen (Z.shiftr 69632 12)) (fst (new_region RKGroup a2 69632 st1))).
Definition fg_final : mstate := fin_st 44 Mt (agtN fg_st4 44 Mt (s_next_rid st1, 0) 1 0).

Lemma first_group_leaf {R} (k : mstate -> Z -> M R) bail :
  ag_tail lay_none fg_st4 44 Mt (s_next_rid st1, 0) 1 0
     (fun st2 go => match go with
                    | None => k st2 (-1)
                    | Some g => let st3 := upd_meta g (fun r => m_set_avail (m_avail r - 1) r) st2 in
                                queue (LActive 44) g st3 (fun st4 => k st4 0) bail
                    end)
  = k fg_final 0.
Proof.
  rewrite ag_tail_none_eq. cbv beta iota zeta. unfold fg_final. apply slot_fin_eq.
  - rewrite (get_meta_rec_of_lookup _ _ _ ltac:(rewrite agtN_metas, aptr_eqb_refl; reflexivity)).
    rewrite (proj1 (agG_links _ _ _ _ _)). unfold fg_st4. rewrite get_meta_rec_upd_ctx, get_meta_rec_upd_same.
    unfold get_meta_rec. autorewrite with mst. rewrite HM. reflexivity.
  - rewrite (get_meta_rec_of_lookup _ _ _ ltac:(rewrite agtN_metas, aptr_eqb_refl; reflexivity)).
    rewrite (proj2 (agG_links _ _ _ _ _)). unfold fg_st4. rewrite get_meta_rec_upd_ctx, get_meta_rec_upd_same.
    unfold get_meta_rec. autorewrite with mst. rewrite HM. reflexivity.
  - rewrite agtN_active. unfold fg_st4, active, ctx. autorewrite with mst. cbn. autorewrite with mst. apply HA.
Qed.

Lemma PHI_first_group : PHI fg_final.
Proof.
  unfold fg_final.
  assert (A7 : forall sc, active (fin_st 44 Mt (agtN fg_st4 44 Mt (s_next_rid st1, 0) 1 0)) sc = if sc =? 44 then Some Mt else None).
  { intros sc. rewrite fin_active, agtN_active. unfold fg_st4, active, ctx. autorewrite with mst. cbn. autorewrite with mst.
    destruct (sc =? 44); [reflexivity| apply HA]. }
  assert (MG : get_meta_rec (fin_st 44 Mt (agtN fg_st4 44 Mt (s_next_rid st1, 0) 1 0)) Mt
               = mkMeta (Some Mt) (Some Mt) (Some (s_next_rid st1, 0)) 0 0 0 1 44 17).
  { unfold fin_st, get_meta_rec. autorewrite with mst. rewrite lookup_insert_eq. unfold get_meta_rec. autorewrite with mst. rewrite lookup_insert_eq.
    rewrite (get_meta_rec_of_lookup _ _ _ ltac:(rewrite agtN_metas, aptr_eqb_refl; reflexivity)).
    unfold fg_st4. rewrite get_meta_rec_upd_ctx, get_meta_rec_upd_same. unfold get_meta_rec. autorewrite with mst. rewrite HM. reflexivity. }
  assert (C7 : c_init_done (s_ctx (fin_st 44 Mt (agtN fg_st4 44 Mt (s_next_rid st1, 0) 1 0))) = c_init_done (s_ctx st1)
       /\ c_avail_meta_count (s_ctx (fin_st 44 Mt (agtN fg_st4 44 Mt (s_next_rid st1, 0) 1 0))) = c_avail_meta_count (s_ctx st1)
       /\ c_free_meta_head (s_ctx (fin_st 44 Mt (agtN fg_st4 44 Mt (s_next_rid st1, 0) 1 0))) = c_free_meta_head (s_ctx st1)).
  { unfold fin_st, agtN, fg_st4. autorewrite with mst. cbn. autorewrite with mst. repeat split; reflexivity. }
  destruct C7 as (C1 & C2 & C3).
  split; [rewrite C1; exact HI|]. split; [rewrite C2; lia|]. split.
  { intros sc m. rewrite A7. destruct (sc =? 44); [| discriminate]. intros E. injection E as <-. rewrite MG. repeat split; reflexivity. }
  split. { left. rewrite C3, C2. split; [exact HF| lia]. }
  intros b h Hb. unfold fin_st, agtN, fg_st4 in Hb. autorewrite with mst in Hb. rewrite HG in Hb.
  destruct (aptr_eqb_spec b (s_next_rid st1, 0)) as [->|NE]; [| rewrite lookup_insert_ne, lookup_empty in Hb by congruence; discriminate].
  rewrite lookup_insert_eq in Hb. injection Hb as <-. exists Mt. split; [reflexivity|].
  unfold buf_group. rewrite MG. cbn [m_last_idx m_maplen m_freeable m_avail m_freed m_next m_prev m_sizeclass].
  split; [reflexivity|]. split; [lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  left. split; [reflexivity|]. split; [reflexivity|]. split; [rewrite A7; reflexivity|]. split; [lia|].
  vm_compute. reflexivity.
Qed.
End FIRST_GROUP.

Theorem T2_F_sim : forall cs L c, PHIB cs -> SIMREL cs L -> In c (ld_live L) ->
  exists a len K, cfree cs (Some c) = SVis (EMunmap a len) K /\ 0 < len
    /\ (forall ru, munmap_answer_ok ru = true -> exists cs', K ru = SRet cs').
Proof.
  intros cs L c HP CR Hc.
  destruct (bf_slot cs L c HP CR Hc) as (m & b & ai & Hs & Hb & Hmem & BG & ML & CF0).
  destruct HP as (PI & PC & PA & PF & PG).
  pose proof BG as (L0 & MP & FR & AV & FD & CASES).
  remember (cfree cs (Some c)) as t eqn:CP.
  unfold cfree in CP. rewrite Hs in CP. unfold free_tail in CP.

  revert CP. replace FUEL with (S (Nat.pred FUEL)) by reflexivity. generalize (Nat.pred FUEL). intros F' CP.
  rewrite AV, FD, L0 in CP.
  change (negb (testbit (Z.lor 0 0) 0)) with true in CP. rewrite guard_true in CP.
  change (negb ((0 =? 0) || (Z.lor 0 0 + bit 0 =? mask_upto 0))) with false in CP. cbv iota in CP.
  rewrite ntf_unfold in CP. change (MR cs m) with (get_meta_rec cs m) in CP.
  rewrite FD, AV, L0 in CP. change (Z.lor 0 0 + bit 0 =? mask_upto 0) with true in CP.
  assert (OK2F : okay_to_free cs m = true).
  { unfold okay_to_free. rewrite FR. cbn [Z.eqb].
    destruct CASES as [(_ & _ & _ & Hsc & STR)|(_ & _ & Hsc)].
    - replace (get_stride (get_meta_rec cs m) <? UNIT * size_class (m_sizeclass (get_meta_rec cs m))) with true by (symmetry; apply Z.ltb_lt; exact STR).
      rewrite orb_true_r. reflexivity.
    - replace (48 <=? m_sizeclass (get_meta_rec cs m)) with true by (symmetry; apply Z.leb_le; exact Hsc). reflexivity. }
  rewrite OK2F in CP. cbn [andb] in CP.
  set (KT := fun (st3 : mstate) (mi : mapinfo) => match mi with
        | Some (base, len) => if negb (len =? 0) then SVis (EMunmap (conc st3 base) len) (fun ru => if munmap_answer_ok ru then ret (drop_region (fst base) st3) else bad_answer (ret cs)) else ret st3
        | None => ret st3 end) in CP.
  set (stX := match m_next (get_meta_rec cs m) with Some _ => upd_meta m clr_rec (set_active (m_sizeclass (get_meta_rec cs m)) None cs) | None => cs end).
  assert (CP' : t = sbind (free_group mstate dec_slots (nontrivial_free dec_slots F') stX m KT (ret cs)) (fun st1 => ret (strip st1))).
  { destruct CASES as [(NX & _ & HA & Hsc & _)|(NX & _ & _)]; rewrite NX in CP; subst stX; rewrite NX.
    - unfold guard in CP. replace (m_sizeclass (get_meta_rec cs m) <? 48) with true in CP by (symmetry; apply Z.ltb_lt; lia).
      rewrite HA, optr_eqb_refl in CP. rewrite (dequeue_self _ _ _ NX) in CP. cbn [set_head] in CP.
      rewrite active_upd_meta, active_set_active, Z.eqb_refl in CP. exact CP.
    - exact CP. }
  clear CP.
  assert (MRX : get_meta_rec stX m = match m_next (get_meta_rec cs m) with Some _ => clr_rec (get_meta_rec cs m) | None => get_meta_rec cs m end).
  { subst stX. destruct (m_next (get_meta_rec cs m)); [| reflexivity]. rewrite get_meta_rec_upd_same. reflexivity. }
  assert (FX : m_sizeclass (get_meta_rec stX m) = m_sizeclass (get_meta_rec cs m) /\ m_last_idx (get_meta_rec stX m) = 0
          /\ m_mem (get_meta_rec stX m) = Some b /\ m_maplen (get_meta_rec stX m) = m_maplen (get_meta_rec cs m)
          /\ get_stride (get_meta_rec stX m) = get_stride (get_meta_rec cs m)).
  { rewrite MRX. destruct (m_next (get_meta_rec cs m)); cbn; rewrite ?L0, ?Hmem; repeat split; reflexivity. }
  destruct FX as (F1 & F2 & F3 & F4 & F5).
  unfold free_group in CP'. rewrite F1, F2, F3, F4, F5 in CP'.
  replace (negb (m_maplen (get_meta_rec cs m) =? 0)) with true in CP' by (symmetry; apply negb_true_iff; apply Z.eqb_neq; exact MP).
  try rewrite if_true_eq in CP'.
  rewrite free_meta_eq in CP'.
  assert (EKT : forall st3 len, len <> 0 ->
            KT st3 (Some (b, len)) = SVis (EMunmap (conc st3 b) len) (fun ru => if munmap_answer_ok ru then ret (drop_region (fst b) st3) else bad_answer (ret cs))).
  { intros st3 len Hl. subst KT. cbv beta iota. replace (len =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hl). reflexivity. }
  rewrite EKT in CP' by lia. clear EKT. clearbody KT.
  rewrite sbind_vis in CP'.
  eexists _, _, _. split; [exact CP'|]. split; [lia|].
  intros ru Hru. cbv beta. rewrite Hru. rewrite sbind_ret. eexists. reflexivity.
Qed.
Theorem T2_F : forall cs L c, PHIB cs -> creach cs L -> In c (ld_live L) ->
  exists a len K, cfree cs (Some c) = SVis (EMunmap a len) K /\ 0 < len
    /\ (forall ru, munmap_answer_ok ru = true -> exists cs', K ru = SRet cs').
Proof. intros cs L c HP CR Hc. exact (T2_F_sim cs L c HP (creach_sim cs L CR) Hc). Qed.

End CEIL.
