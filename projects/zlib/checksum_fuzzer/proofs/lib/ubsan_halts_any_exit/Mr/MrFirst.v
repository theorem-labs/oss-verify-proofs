(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Spec Require SM08. Import SM08. Import SM08.MallocCtrl.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Mr Require Import MrFeasNull MrFeasNull44 MrFeasSome1 MrTall MrShape MrDrv MrUcb.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Definition AMF (st st' : mstate) (m : aptr) : Prop :=
  keeps_active st st' /\ c_free_meta_head (ctx st') = None /\ s_slots st' = s_slots st /\ c_usage (ctx st') = c_usage (ctx st) /\
  m_next (get_meta_rec st' m) = None /\ m_prev (get_meta_rec st' m) = None /\
  c_avail_meta (ctx st') = Some (aadd m META_SIZE) /\ cnt st' = NSLOTS - 1.

Section U.
Context {R : Type} (Post : R -> Z -> Z -> Prop) (Bud : Z -> Z -> Prop).
Hypothesis HBm : forall c u c' u', Bud c u -> c' <= c -> u' <= u -> Bud c' u'.
Local Notation ucb := (ucbg Bud).

Definition PRE (st0 st : mstate) : Prop :=
  keeps_active st0 st /\ c_free_meta_head (ctx st) = None /\ s_slots st = s_slots st0 /\ c_usage (ctx st) = c_usage (ctx st0).

Lemma PRE_refl st : c_free_meta_head (ctx st) = None -> PRE st st.
Proof. intros H. split; [apply ka_refl|]. split; [exact H|]. split; reflexivity. Qed.

Lemma ucb_guard tag c (k bail : M R) kb C U : ucb k kb C U Post -> ucb (guard tag c k bail) kb C U Post.
Proof. intros H. unfold guard. destruct c; [exact H | exact I]. Qed.

Lemma ucb_queue h m st (k : mstate -> M R) bail kb C U :
  (forall st', ucb (k st') kb C U Post) -> ucb (queue h m st k bail) kb C U Post.
Proof. intros Hk. unfold queue. apply ucb_guard. apply ucb_guard. destruct (get_head st h); apply Hk. Qed.

Lemma ucb_free_meta m st (k : mstate -> M R) bail kb C U :
  (forall st', ucb (k st') kb C U Post) -> ucb (free_meta m st k bail) kb C U Post.
Proof. intros Hk. unfold free_meta. apply ucb_queue. exact Hk. Qed.

Lemma ucb_am_take_f st0 st (k : mstate -> optr -> M R) bail kb C U :
  PRE st0 st ->
  (forall st' m, PRE st0 st' -> m_next (get_meta_rec st' m) = None -> m_prev (get_meta_rec st' m) = None ->
                 c_avail_meta (ctx st') = Some (aadd m META_SIZE) -> cnt st' = cnt st - 1 -> ucb (k st' (Some m)) kb C U Post) ->
  ucb (am_take st k bail) kb C U Post.
Proof.
  intros (P1 & P2 & P3 & P4) Hk. unfold am_take. destruct (c_avail_meta (ctx st)) as [m|]; [|exact I].
  apply Hk; try reflexivity; try (rewrite gmr_upd_same; reflexivity).
  repeat split; assumption.
Qed.

Lemma ucb_am_carve_f st0 st p (k : mstate -> optr -> M R) bail kb C U :
  PRE st0 st ->
  (forall st' m, AMF st0 st' m -> ucb (k st' (Some m)) kb C U Post) -> ucb (am_carve st p k bail) kb C U Post.
Proof.
  intros (P1 & P2 & P3 & P4) Hk. unfold am_carve.
  match goal with |- ucb (am_take ?s5 k bail) _ _ _ _ => set (st5 := s5) end.
  assert (P5 : PRE st0 st5 /\ cnt st5 = NSLOTS).
  { subst st5. destruct (c_meta_area_tail (ctx (upd_ctx (fun c => set_avail_meta_areas (Some (aadd p 4096))
             (set_avail_meta_area_count (c_avail_meta_area_count c - 1) c)) st))) eqn:E;
      (split; [repeat split; assumption | reflexivity]). }
  destruct P5 as [P5 C5]. clearbody st5.
  apply (ucb_am_take_f st0 st5); [exact P5|].
  intros st' m (Q1 & Q2 & Q3 & Q4) N1 N2 AV CT. apply Hk. unfold AMF. repeat split; try assumption. lia.
Qed.

Lemma ucb_am_finish_f st0 st nu (k : mstate -> optr -> M R) bail kb C U :
  PRE st0 st -> Bud C U ->
  (forall st' m kb' c u, AMF st0 st' m -> c <= C -> u <= U -> ucb (k st' (Some m)) kb' c u Post) ->
  (forall st' kb' c u, c <= C -> u <= U -> ucb (k st' None) kb' c u Post) ->
  ucb (am_finish st nu k bail) kb C U Post.
Proof.
  intros P HB Hk Hn. unfold am_finish. destruct (c_avail_meta_areas (ctx st)) as [p|]; [|exact I].
  destruct (if negb (snd p mod PGSZ =? 0) then false else nu).
  - cbn [ucbg]. split; [exact I|]. cbn [ev_kb ev_dc ev_du]. split; [eapply HBm; [exact HB | lia | lia]|].
    intros z _. destruct (negb (mprotect_answer_ok z)); [exact I|].
    destruct ((z =? 0) || (z =? TWO64 - ENOSYS)).
    + apply ucb_am_carve_f with (st0 := st0); [exact P|]. intros st' m A. apply Hk; [exact A | lia | lia].
    + apply Hn; lia.
  - apply ucb_am_carve_f with (st0 := st0); [exact P|]. intros st' m A. apply Hk; [exact A | lia | lia].
Qed.

Lemma ucb_am_after_brk_f st0 st nu (k : mstate -> optr -> M R) bail kb C U :
  PRE st0 st -> c_meta_alloc_shift (ctx st) = 0 -> Bud (C + 2) (U + 12288) ->
  (forall st' m kb' c u, AMF st0 st' m -> c <= C + 2 -> u <= U + 12288 -> ucb (k st' (Some m)) kb' c u Post) ->
  (forall st' kb' c u, c <= C + 2 -> u <= U + 12288 -> ucb (k st' None) kb' c u Post) ->
  ucb (am_after_brk st nu k bail) kb C U Post.
Proof.
  intros P HS HB Hk Hn. unfold am_after_brk. rewrite HS. change (Z.shiftl 2 0 * PGSZ) with 8192.
  destruct (c_avail_meta_area_count (ctx st) =? 0).
  - cbn [ucbg]. split; [cbn; lia|]. cbn [ev_kb ev_dc ev_du]. split; [eapply HBm; [exact HB | lia | lia]|].
    intros z _. destruct (negb (mmap_answer_ok _ _ _ z)); [exact I|].
    destruct (is_err z); [apply Hn; lia|].
    destruct (new_region RKMeta z _ st) as [st1 rid] eqn:E.
    apply ucb_am_finish_f with (st0 := st0).
    + pose proof (f_equal fst E) as E1. cbn [fst] in E1. rewrite <- E1. destruct P as (P1 & P2 & P3 & P4). repeat split; assumption.
    + eapply HBm; [exact HB | lia | lia].
    + intros st' m kb' c u A Hc Hu. apply Hk; [exact A | lia | lia].
    + intros st' kb' c u Hc Hu. apply Hn; lia.
  - apply ucb_am_finish_f with (st0 := st0); [exact P | eapply HBm; [exact HB | lia | lia] | |].
    + intros st' m kb' c u A Hc Hu. apply Hk; [exact A | lia | lia].
    + intros st' kb' c u Hc Hu. apply Hn; lia.
Qed.

Lemma round_up_pg_le (x : Z) : x <= round_up_pg x <= x + 4095.
Proof. exact (round_up_pg_bounds x). Qed.

Lemma ucb_alloc_meta_first st (k : mstate -> optr -> M R) bail b C U :
  c_free_meta_head (ctx st) = None -> cnt st = 0 -> c_brk (ctx st) = BrkUntried -> c_meta_alloc_shift (ctx st) = 0 ->
  (* port727 (): 32768 -> 36864: a brk grow is charged one more page (MrUcb.ev_du); the
     caller's budget (2 ^ 17) still covers it. *)
  Bud (C + 5) (U + 36864) ->
  (forall st' m kb' c u, AMF st st' m -> c <= C + 5 -> u <= U + 36864 -> ucb (k st' (Some m)) kb' c u Post) ->
  (forall st' kb' c u, c <= C + 5 -> u <= U + 36864 -> ucb (k st' None) kb' c u Post) ->
  ucb (alloc_meta st k bail) (Some b) C U Post.
Proof.
  intros HF HC HB HS HBud Hk Hn. unfold alloc_meta.
  set (st0 := if c_init_done (ctx st) =? 0 then _ else st).
  assert (P0 : PRE st st0 /\ cnt st0 = 0 /\ c_brk (ctx st0) = BrkUntried /\ c_meta_alloc_shift (ctx st0) = 0).
  { subst st0. destruct (c_init_done (ctx st) =? 0);
      (split; [repeat split; try assumption; try reflexivity; apply ka_refl | split; [exact HC | split; [exact HB | exact HS]]]). }
  destruct P0 as (P0 & C0 & B0 & S0). clearbody st0.
  destruct P0 as (P1 & P2 & P3 & P4). rewrite P2.
  replace (c_avail_meta_count (ctx st0) =? 0) with true by (symmetry; apply Z.eqb_eq; exact C0). cbn [negb].
  assert (P : PRE st st0) by (repeat split; assumption).
  rewrite B0. rewrite andb_true_r.
  destruct (c_avail_meta_area_count (ctx st0) =? 0).
  2:{ apply ucb_am_after_brk_f with (st0 := st); [exact P | exact S0 | eapply HBm; [exact HBud | lia | lia] | |].
      - intros st' m kb' c u A Hc Hu. apply Hk; [exact A | lia | lia].
      - intros st' kb' c u Hc Hu. apply Hn; lia. }
  cbn [ucbg]. split; [left; reflexivity|]. cbn [ev_kb ev_dc ev_du Z.eqb]. split; [eapply HBm; [exact HBud | lia | lia]|].
  intros cur Hcur. cbn [ev_ans] in Hcur. specialize (Hcur eq_refl). subst cur.
  destruct (brk0_answer_ok b) eqn:Eb; cbn [negb]; [|exact I].
  pose proof (round_up_pg_le b) as Hr.
  assert (NE : (round_up_pg b + 2 * PGSZ =? 0) = false).
  { apply Z.eqb_neq. unfold brk0_answer_ok in Eb. apply andb_prop in Eb as [Eb _]. apply andb_prop in Eb as [Eb _]. apply Z.ltb_lt in Eb.
    unfold PGSZ. lia. }
  cbn [ucbg]. split; [right; unfold PGSZ; lia|]. cbn [ev_kb ev_dc ev_du]. rewrite NE.
  split; [eapply HBm; [exact HBud | lia | unfold PGSZ in *; lia]|]. intros r _.
  destruct (negb (brk_answer_ok b _ r)); [exact I|].
  destruct (negb (r =? round_up_pg b + 2 * PGSZ)).
  { apply ucb_am_after_brk_f with (st0 := st); [repeat split; assumption | exact S0 | eapply HBm; [exact HBud | lia | unfold PGSZ in *; lia] | |].
    - intros st' m kb' c u A Hc Hu. apply Hk; [exact A | lia | unfold PGSZ in *; lia].
    - intros st' kb' c u Hc Hu. apply Hn; [lia | unfold PGSZ in *; lia]. }
  destruct (negb (brk_pages_ok st0 _ _)); [exact I|].
  cbn [ucbg]. split; [cbn; unfold PGSZ; lia|]. cbn [ev_kb ev_dc ev_du].
  split; [eapply HBm; [exact HBud | lia | unfold PGSZ in *; lia]|]. intros rg _.
  destruct (negb (mmap_fixed_answer_ok _ rg)); [exact I|].
  destruct (new_region RKBrk _ _ st0) as [st1 rid] eqn:E.
  pose proof (f_equal fst E) as E1. cbn [fst] in E1.
  apply ucb_am_after_brk_f with (st0 := st).
  - rewrite <- E1. repeat split; assumption.
  - rewrite <- E1. exact S0.
  - eapply HBm; [exact HBud | lia | unfold PGSZ in *; lia].
  - intros st' m kb' c u A Hc Hu. apply Hk; [exact A | lia | unfold PGSZ in *; lia].
  - intros st' kb' c u Hc Hu. apply Hn; [lia | unfold PGSZ in *; lia].
Qed.

End U.

Lemma as_S {R} lay f st sc req (k : mstate -> Z -> M R) bail :
  alloc_slot lay (S f) st sc req k bail =
    try_avail sc st (fun st1 first =>
      if negb (first =? 0) then k st1 (ctz32 first) else
      alloc_group R lay (alloc_slot lay f) st1 sc req (fun st2 go =>
        match go with
        | None => k st2 (-1)
        | Some g =>
          let st3 := upd_meta g (fun r => m_set_avail (m_avail r - 1) r) st2 in
          queue (LActive sc) g st3 (fun st4 => k st4 0) bail
        end) bail) bail.
Proof. reflexivity. Qed.

Lemma sc_65536 : size_to_class 65536 = 44. Proof. vm_compute. reflexivity. Qed.

Lemma gmr_add_slots m p stride cntv st g : get_meta_rec (add_slots m p stride cntv st) g = get_meta_rec st g. Proof. reflexivity. Qed.
Lemma gmr_put_group p mo ai st g : get_meta_rec (put_group p mo ai st) g = get_meta_rec st g. Proof. reflexivity. Qed.
Lemma gmr_set_usage sc v st g : get_meta_rec (set_usage sc v st) g = get_meta_rec st g. Proof. reflexivity. Qed.
Lemma gmr_upd_ctx f st g : get_meta_rec (upd_ctx f st) g = get_meta_rec st g. Proof. reflexivity. Qed.
Lemma gmr_set_head h v st g : get_meta_rec (set_head h v st) g = get_meta_rec st g. Proof. destruct h; reflexivity. Qed.
Lemma gmr_step_seq st g : get_meta_rec (step_seq st) g = get_meta_rec st g.
Proof. unfold step_seq. destruct (c_seq (ctx st) =? 255); reflexivity. Qed.
Lemma gmr_new_region kd base len st g : get_meta_rec (fst (new_region kd base len st)) g = get_meta_rec st g. Proof. reflexivity. Qed.

Lemma act_add_slots m p stride cntv st sc : active (add_slots m p stride cntv st) sc = active st sc. Proof. reflexivity. Qed.
Lemma act_put_group p mo ai st sc : active (put_group p mo ai st) sc = active st sc. Proof. reflexivity. Qed.
Lemma act_set_usage sc0 v st sc : active (set_usage sc0 v st) sc = active st sc. Proof. reflexivity. Qed.
Lemma act_upd_meta g f st sc : active (upd_meta g f st) sc = active st sc. Proof. reflexivity. Qed.
Lemma act_mmap_counter st sc : active (upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) st) sc = active st sc. Proof. reflexivity. Qed.
Lemma act_step_seq st sc : active (step_seq st) sc = active st sc.
Proof. unfold step_seq. destruct (c_seq (ctx st) =? 255); reflexivity. Qed.
Lemma act_new_region kd base len st sc : active (fst (new_region kd base len st)) sc = active st sc. Proof. reflexivity. Qed.

Definition first_final (st2 : mstate) (m : aptr) (rid : N) (needed : Z) : mstate :=
  let stA := upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) (upd_meta m (m_set_maplen (Z.shiftr needed 12)) st2) in
  let st1 := set_usage 44 (usage stA 44 + 1) stA in
  let st2' := upd_meta m (fun r => m_set_sizeclass 44 (m_set_freeable 1 (m_set_last_idx (1 - 1)
                (m_set_mem (Some (rid, 0)) (m_set_freed (mask_upto (1 - 1) - mask_upto 0) (m_set_avail (mask_upto 0) r)))))) st1 in
  let st3 := put_group (rid, 0) (Some m) 0 st2' in
  let st4 := add_slots m (rid, 0) (get_stride (get_meta_rec st3 m)) 1 st3 in
  let st5 := upd_meta m (fun r => m_set_avail (m_avail r - 1) r) st4 in
  let st6 := upd_meta m (fun r => m_set_prev (Some m) (m_set_next (Some m) r)) st5 in
  set_head (LActive 44) (Some m) st6.

Lemma first_final_KST : forall st2 m rid,
  (forall sc, active st2 sc = None) -> c_free_meta_head (ctx st2) = None ->
  c_avail_meta (ctx st2) = Some (aadd m META_SIZE) -> cnt st2 = NSLOTS - 1 -> s_next_rid st2 = N.succ rid ->
  KST (Z.of_nat FUEL + 10) (first_final st2 m rid 69632) (Some m) None [(m, (rid, 0))].
Proof.
  intros st2 m rid HA HF HV HC HN.
  assert (RM : get_meta_rec (first_final st2 m rid 69632) m =
               m_set_prev (Some m) (m_set_next (Some m)
                 ((fun r => m_set_avail (m_avail r - 1) r)
                    ((fun r => m_set_sizeclass 44 (m_set_freeable 1 (m_set_last_idx (1 - 1)
                        (m_set_mem (Some (rid, 0)) (m_set_freed (mask_upto (1 - 1) - mask_upto 0) (m_set_avail (mask_upto 0) r))))))
                       (m_set_maplen (Z.shiftr 69632 12) (get_meta_rec st2 m)))))).
  { unfold first_final. rewrite gmr_set_head, gmr_upd_same, gmr_upd_same, gmr_add_slots, gmr_put_group, gmr_upd_same, gmr_set_usage,
      gmr_upd_ctx, gmr_upd_same. reflexivity. }
  constructor.
  - intros sc. unfold first_final. cbv zeta. unfold set_head, set_active, active. cbn [ctx s_ctx upd_ctx c_active set_active_map].
    destruct (Z.eqb_spec sc 44) as [->|NE].
    + apply lookup_insert_eq.
    + rewrite lookup_insert_ne by congruence. apply (HA sc).
  - exact HF.
  - intros a Ha. discriminate.
  - intros g b [E|[]]. injection E as <- <-. split; [|split; [|split; [reflexivity | right; reflexivity]]].
    + unfold first_final. cbv zeta. cbn. rewrite Z.mul_0_r, Z.add_0_r. apply lookup_insert_eq.
    + change (s_next_rid (first_final st2 m rid 69632)) with (s_next_rid st2). rewrite HN. cbn. lia.
  - cbn. apply NoDup_singleton.
  - cbn. apply NoDup_singleton.
  - intros m' E. injection E as <-. exists (rid, 0). split; [left; reflexivity|]. rewrite RM.
    unfold act44_rec, solo_rec. cbn. repeat split; try reflexivity. discriminate.
  - exists (aadd m META_SIZE). split; [exact HV|]. intros g [<-|[]]. right. cbn. unfold META_SIZE. lia.
  - change (cnt (first_final st2 m rid 69632)) with (cnt st2). rewrite HC. unfold NSLOTS, FUEL. lia.
Qed.

Ltac eval_closed_ifs st' :=
  repeat match goal with |- context [if ?c then _ else _] =>
    lazymatch c with context [st'] => fail | _ => idtac end;
    let v := eval vm_compute in c in
    lazymatch v with true => idtac | false => idtac end;
    change c with v; cbv iota end.

Section FIRST.
Variable Bud : Z -> Z -> Prop.
Hypothesis HBm : forall c u c' u', Bud c u -> c' <= c -> u' <= u -> Bud c' u'.

Theorem malloc_core_first_KST cs b C U :
  allnone cs -> c_free_meta_head (ctx cs) = None -> cnt cs = 0 -> usage cs 44 = 0 ->
  c_brk (ctx cs) = BrkUntried -> c_meta_alloc_shift (ctx cs) = 0 -> Bud (C + 7) (U + 2 ^ 17) ->
  ucbg Bud (malloc_core lay_none cs 65536) (Some b) C U
      (fun r c u => match snd r with
                    | Some (g, idx) => idx = 0 /\ exists b, m_mem (get_meta_rec (fst r) g) = Some b /\
                                                  KST (Z.of_nat FUEL + 10) (fst r) (Some g) None [(g, b)]
                    | None => True end /\ c <= C + 7 /\ u <= U + 2 ^ 17).
Proof.
  intros HA HF HC HU HB HS HBud. unfold malloc_core.
  change (size_overflows 65536) with false. change (MMAP_THRESHOLD <=? 65536) with false. cbv iota.
  unfold malloc_small_ctrl. rewrite sc_65536. cbv zeta. rewrite (HA 44).
  change ((4 <=? 44) && (44 <? 32) && negb (44 =? 6) && Z.even 44 && (usage cs 44 =? 0)) with false. cbv iota.
  rewrite (HA 44). change (negb (lowbit 0 =? 0)) with false. cbv iota.
  unfold FUEL at 1. change 64%nat with (S 63). rewrite as_S.
  unfold try_avail. rewrite (HA 44). change (negb (0 =? 0)) with false. cbv iota.
  unfold alloc_group.
  apply (ucb_alloc_meta_first _ Bud HBm); [exact HF | exact HC | exact HB | exact HS | eapply HBm; [exact HBud | lia | lia] |
                                           | intros st' kb' c u Hc Hu; cbn [ucbg snd]; split; [exact I | lia]].
  intros st' m kb' c0 u0 (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8) Hc0 Hu0.
  assert (HU' : usage st' 44 = 0) by (unfold usage in *; rewrite A4; exact HU).
  cbv zeta. rewrite HU'.
  unfold is_bouncing, account_bounce. change (sc_in_seq_range 44) with false. cbn [andb negb].
  eval_closed_ifs st'.
  change (round_up_pg (65536 + IB + UNIT)) with 69632.
  cbn [ucbg]. split; [cbn; lia|]. cbn [ev_kb ev_dc ev_du]. split; [eapply HBm; [exact HBud | lia | lia]|].
  intros r _. destruct (negb (mmap_answer_ok _ _ _ r)); [exact I|].
  destruct (is_err r).
  { apply ucb_free_meta. intros st2. cbn [ucbg snd]. split; [exact I | lia]. }
  destruct (new_region RKGroup r 69632 (step_seq st')) as [st2 rid] eqn:E.
  assert (Est2 : st2 = fst (new_region RKGroup r 69632 (step_seq st'))) by (rewrite E; reflexivity).
  assert (Erid : s_next_rid st2 = N.succ rid).
  { pose proof (f_equal snd E) as X. cbn [snd] in X. rewrite Est2, <- X. reflexivity. }
  assert (HA2 : forall sc, active st2 sc = None).
  { intros sc. rewrite Est2, act_new_region, act_step_seq, A1. apply HA. }
  assert (HF2 : c_free_meta_head (ctx st2) = None).
  { rewrite Est2. unfold new_region, step_seq. cbn [fst]. destruct (c_seq (ctx st') =? 255); exact A2. }
  assert (HV2 : c_avail_meta (ctx st2) = Some (aadd m META_SIZE)).
  { rewrite Est2. unfold new_region, step_seq. cbn [fst]. destruct (c_seq (ctx st') =? 255); exact A7. }
  assert (HC2 : cnt st2 = NSLOTS - 1).
  { rewrite Est2. unfold new_region, step_seq, cnt. cbn [fst]. destruct (c_seq (ctx st') =? 255); exact A8. }
  assert (HN2 : m_next (get_meta_rec st2 m) = None) by (rewrite Est2, gmr_new_region, gmr_step_seq; exact A5).
  assert (HP2 : m_prev (get_meta_rec st2 m) = None) by (rewrite Est2, gmr_new_region, gmr_step_seq; exact A6).
  clear E Est2.
  unfold ag_tail. cbv zeta. change (lh_hdr lay_none ?x ?y) with x.
  match goal with |- context [queue (LActive 44) m ?s5 _ _] => set (st5 := s5) end.
  assert (N5 : m_next (get_meta_rec st5 m) = None /\ m_prev (get_meta_rec st5 m) = None /\ active st5 44 = None).
  { subst st5. rewrite !gmr_upd_same, !gmr_add_slots, !gmr_put_group, !gmr_upd_same, !gmr_set_usage, !gmr_upd_ctx, !gmr_upd_same.
    cbn [m_next m_prev m_set_avail m_set_sizeclass m_set_freeable m_set_last_idx m_set_mem m_set_freed m_set_maplen].
    split; [exact HN2|]. split; [exact HP2|].
    rewrite act_upd_meta, act_add_slots, act_put_group, act_upd_meta, act_set_usage, act_mmap_counter, act_upd_meta. apply HA2. }
  destruct N5 as (N5 & P5 & H5).
  unfold queue. rewrite N5, P5. cbn [optr_eqb]. unfold guard. unfold get_head. rewrite H5.
  match goal with |- ucbg _ (match active ?sf 44 with _ => _ end) _ _ _ _ =>
    assert (EF : sf = first_final st2 m rid 69632) by (subst st5; reflexivity) end.
  rewrite EF.
  pose proof (first_final_KST st2 m rid HA2 HF2 HV2 HC2 Erid) as KF.
  rewrite (ks_act _ _ _ _ _ KF 44). change (44 =? 44) with true. cbv iota.
  cbn [ucbg snd fst]. split; [|lia]. split; [reflexivity|]. exists (rid, 0). split; [|exact KF].
  destruct (ks_a44 _ _ _ _ _ KF m eq_refl) as (b0 & [Eb|[]] & ((Hmem & _) & _)). injection Eb as <-. exact Hmem.
Qed.

Lemma allnone_strip : forall st, allnone st -> allnone (strip st).
Proof. intros st H sc. exact (H sc). Qed.

Definition first_post (C U : Z) (r : mstate * option cptr) (c u : Z) : Prop :=
  match snd r with
  | Some c0 => exists g b, c0 = aadd b UNIT /\ KST (Z.of_nat FUEL + 10) (fst r) (Some g) None [(g, b)]
  | None => True end /\ c <= C + 7 /\ u <= U + 2 ^ 17.

Theorem cmalloc_first_KST_g cs b C U :
  allnone cs -> c_free_meta_head (ctx cs) = None -> cnt cs = 0 -> usage cs 44 = 0 ->
  c_brk (ctx cs) = BrkUntried -> c_meta_alloc_shift (ctx cs) = 0 -> Bud (C + 7) (U + 2 ^ 17) ->
  ucbg Bud (cmalloc cs 65536) (Some b) C U (first_post C U).
Proof.
  intros HA HF HC HU HB HS HBud. unfold cmalloc.
  eapply ucbg_sbind; [apply (malloc_core_first_KST cs b C U HA HF HC HU HB HS HBud)|].
  intros [st1 [[g idx]|]] kb' c u [H Hcu]; cbn [fst snd] in H |- *; [|cbn [ucbg]; split; [exact I | exact Hcu]].
  destruct H as (-> & b0 & Hmem & K'). cbn [ucbg]. split; [|exact Hcu]. cbn [fst snd]. exists g, b0. split; [|apply KST_strip; exact K'].
  unfold slot_of, slot_start'. rewrite Hmem. cbn [default]. unfold aadd, id. rewrite Z.mul_0_r, Z.add_0_r. reflexivity.
Qed.
End FIRST.

Theorem cmalloc_first_KST cs b C U :
  allnone cs -> c_free_meta_head (ctx cs) = None -> cnt cs = 0 -> usage cs 44 = 0 ->
  c_brk (ctx cs) = BrkUntried -> c_meta_alloc_shift (ctx cs) = 0 ->
  ucb (cmalloc cs 65536) (Some b) C U (first_post C U).
Proof.
  intros HA HF HC HU HB HS. apply (ucbg_ucb (fun _ _ => True)).
  apply cmalloc_first_KST_g; auto.
Qed.
