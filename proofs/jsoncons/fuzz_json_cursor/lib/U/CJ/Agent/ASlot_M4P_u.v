(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.

From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.Agent Require Import F_syscalls_u MallocRep_u F_malloc_free_u F_malloc_fast_u F_malloc_enframe_u MallocTree_u MallocFacts_A_u MallocHINV_u MallocKit_A_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.Agent Require Import MallocKit_AB_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.Agent Require Import Malloc_fp_u MallocKit_A2_u F_malloc_big_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.Agent Require Import MallocKit_A3_u ASlot_W9_u ASlot_W14_u.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.

Lemma pos_iter_slots' (m p : aptr) (stride : Z) : forall n tb,
  0 < stride ->
  let F := fun acc : Z * gmap aptr (aptr * Z) => let (i, t) := acc in (i + 1, <[aadd p (UNIT + stride * i) := (m, i)]> t) in
  fst (Pos.iter F (0, tb) n) = Z.pos n
  /\ (snd (Pos.iter F (0, tb) n)) !! (aadd p UNIT) = Some (m, 0)
  /\ (forall q, (snd (Pos.iter F (0, tb) n)) !! q <> None -> tb !! q <> None \/ exists i, 0 <= i < Z.pos n /\ q = aadd p (UNIT + stride * i)).
Proof.
  intros n tb HS F. induction n as [|n IH] using Pos.peano_ind.
  - cbn [Pos.iter]. unfold F. rewrite Z.mul_0_r, Z.add_0_r. split; [reflexivity|]. split; [apply lookup_insert_eq|].
    intros q Hq. destruct (decide (q = aadd p UNIT)) as [->|NE]; [right; exists 0; rewrite Z.mul_0_r, Z.add_0_r; split; [lia| reflexivity]|].
    left. rewrite lookup_insert_ne in Hq by congruence. exact Hq.
  - rewrite Pos.iter_succ. destruct IH as (I1 & I2 & I3). fold F. destruct (Pos.iter F (0, tb) n) as [i t] eqn:EP. cbn [fst snd] in I1, I2, I3 |- *.
    unfold F at 1. unfold F at 1. unfold F at 1. cbn [fst snd]. subst i.
    split; [lia|]. split.
    + rewrite lookup_insert_ne; [exact I2|]. unfold aadd. intros E. apply (f_equal snd) in E. cbn in E. unfold UNIT in E. nia.
    + intros q Hq. destruct (decide (q = aadd p (UNIT + stride * Z.pos n))) as [->|NE].
      * right. exists (Z.pos n). split; [lia| reflexivity].
      * rewrite lookup_insert_ne in Hq by congruence. destruct (I3 q Hq) as [X|(i & Hi & ->)]; [left; exact X| right; exists i; split; [lia| reflexivity]].
Qed.

Lemma add_slots_first' m p stride c st : 1 <= c -> 0 < stride ->
  (s_slots (add_slots m p stride c st)) !! (aadd p UNIT) = Some (m, 0)
  /\ (forall q, (s_slots (add_slots m p stride c st)) !! q <> None -> (s_slots st) !! q <> None \/ exists i, 0 <= i < c /\ q = aadd p (UNIT + stride * i)).
Proof.
  intros Hc HS. unfold add_slots. cbn [s_slots set_slots].
  destruct c as [|n|n]; [lia| |lia]. cbn [Z.iter].
  destruct (pos_iter_slots' m p stride n (s_slots st) HS) as (_ & A & B). split; [exact A| exact B].
Qed.

Lemma mask_upto_range' k : 0 <= k <= 31 -> 1 <= mask_upto k < 2^32 /\ 2^k <= mask_upto k.
Proof.
  intros Hkk. unfold mask_upto. rewrite Z.pow_add_r by lia. change (2^1) with 2.
  assert (1 <= 2^k) by (change 1 with (2^0); apply Z.pow_le_mono_r; lia).
  assert (2^k <= 2^31) by (apply Z.pow_le_mono_r; lia).
  change (2^32) with (2 * 2^31). lia.
Qed.

Lemma put_meta_wr8_comm mt r q v st : put_meta mt r (wr8 q v st) = wr8 q v (put_meta mt r st).
Proof. destruct st; reflexivity. Qed.
Lemma put_meta_zero_hdrs_comm mt r p size : forall k i st,
  put_meta mt r (zero_hdrs p size i k st) = zero_hdrs p size i k (put_meta mt r st).
Proof. induction k as [|k IH]; intros i st; cbn [zero_hdrs]; [reflexivity|]. rewrite IH, put_meta_wr8_comm. reflexivity. Qed.
Lemma rec_zero_hdrs p size q : forall k i st, get_meta_rec (zero_hdrs p size i k st) q = get_meta_rec st q.
Proof. induction k as [|k IH]; intros i st; cbn [zero_hdrs]; [reflexivity|]. rewrite IH. destruct st; reflexivity. Qed.

Section SMG.
Variables (stT : mstate) (sc cnt ai ml : Z) (mt p : aptr).
Let stF := st_model stT sc cnt ai mt p.
Hypothesis SC : 0 <= sc < 48.
Hypothesis CNT : 1 <= cnt <= 32.
Hypothesis AI : 0 <= ai <= cnt - 1.
Hypothesis ML : 0 <= ml.
Hypothesis REC : get_meta_rec stT mt = mkMeta None None None 0 0 0 0 0 ml.
Hypothesis P0 : 0 <= snd p.

Definition sm_rec : meta :=
  mkMeta (Some mt) (Some mt) (Some p) (mask_upto ai - 1) (mask_upto (cnt - 1) - mask_upto ai) (cnt - 1) 1 sc ml.

Lemma smg_proj :
  s_regions stF = s_regions stT /\ s_shadow stF = s_shadow (hdr_havoc p stT)
  /\ s_groups stF = <[p := mkGhdr (Some mt) (Z.land ai 31)]> (s_groups stT)
  /\ s_areas stF = s_areas stT /\ s_tick stF = s_tick stT /\ s_next_rid stF = s_next_rid stT /\ s_reserved stF = s_reserved stT
  /\ c_brk (ctx stF) = c_brk (ctx stT) /\ c_mmap_counter (ctx stF) = c_mmap_counter (ctx stT)
  /\ c_free_meta_head (ctx stF) = c_free_meta_head (ctx stT).
Proof. repeat split; reflexivity. Qed.

Lemma smg_rec_mt : get_meta_rec stF mt = sm_rec.
Proof.
  unfold stF. rewrite (st_model_eq_rec stT sc cnt ai ml mt p SC CNT REC P0).
  unfold stFin, stE. rewrite rec_set_active, get_meta_rec_put_same. reflexivity.
Qed.

Lemma smg_rec_other q : q <> mt -> get_meta_rec stF q = get_meta_rec stT q.
Proof.
  intros NE. unfold stF. rewrite (st_model_eq_rec stT sc cnt ai ml mt p SC CNT REC P0).
  unfold stFin, stE, stD, stC, stB, stA. rewrite rec_set_active, get_meta_rec_put_other, rec_put_group, get_meta_rec_put_other, rec_set_usage, rec_hdr_havoc by exact NE.
  reflexivity.
Qed.

Lemma smg_active c : active stF c = if c =? sc then Some mt else active stT c.
Proof.
  unfold stF, st_model. cbv zeta. rewrite active_set_active. destruct (c =? sc); [reflexivity|].
  rewrite !active_upd_meta. reflexivity.
Qed.

Lemma smg_ctx :
  ctx stF = set_active_map (<[sc := mt]> (c_active (ctx stT))) (set_usage_map (<[sc := usage stT sc + cnt]> (c_usage (ctx stT))) (ctx stT)).
Proof. reflexivity. Qed.

Lemma smg_usage i : usage stF i = if i =? sc then usage stT sc + cnt else usage stT i.
Proof.
  unfold usage. rewrite smg_ctx. cbn [c_usage set_active_map set_usage_map].
  destruct (Z.eqb_spec i sc) as [E|NE]; [rewrite E, lookup_insert_eq; reflexivity| rewrite lookup_insert_ne by congruence; reflexivity].
Qed.

Lemma smg_stride : get_stride sm_rec = if (cnt =? 1) && negb (ml =? 0) then ml * 4096 - 16 else 16 * size_class sc.
Proof.
  unfold get_stride, sm_rec. cbn [m_last_idx m_maplen m_sizeclass].
  replace (cnt - 1 =? 0) with (cnt =? 1) by (destruct (Z.eqb_spec cnt 1); destruct (Z.eqb_spec (cnt - 1) 0); try reflexivity; lia).
  unfold UNIT. reflexivity.
Qed.

Lemma smg_slot0 : 0 < get_stride sm_rec -> (s_slots stF) !! (fst p, snd p + 16) = Some (mt, 0).
Proof.
  intros HS. unfold stF, st_model. cbv zeta.
  match goal with |- s_slots (set_active _ _ (upd_meta _ _ (upd_meta _ _ ?X))) !! _ = _ =>
    change (s_slots (set_active _ _ (upd_meta _ _ (upd_meta _ _ X)))) with (s_slots X) end.
  match goal with |- s_slots (add_slots mt p ?s cnt ?X) !! _ = _ =>
    replace s with (get_stride sm_rec) end.
  2:{ unfold upd_meta. rewrite rec_put_group, get_meta_rec_put_same, rec_set_usage, rec_hdr_havoc, REC. unfold get_stride, sm_rec.
      cbn [m_last_idx m_maplen m_sizeclass m_set_sizeclass m_set_freeable m_set_last_idx m_set_mem m_set_freed m_set_avail].
      replace (Z.land (cnt - 1) 31) with (cnt - 1) by (change 31 with (Z.ones 5); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
      replace (Z.land sc 63) with sc by (change 63 with (Z.ones 6); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
      reflexivity. }
  change (fst p, snd p + 16) with (aadd p UNIT).
  apply (proj1 (add_slots_first' mt p (get_stride sm_rec) cnt _ ltac:(lia) HS)).
Qed.

Lemma smg_shadow_other q : q <> fst p -> get_shadow stF q = get_shadow stT q.
Proof.
  intros NE. unfold get_shadow. rewrite (proj1 (proj2 smg_proj)). unfold hdr_havoc, upd_shadow. cbn [s_shadow set_shadow].
  rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

Lemma smg_shadow_p :
  get_shadow stF (fst p) = mkShadow (r_cells (get_shadow stT (fst p)))
                             (<[snd p / 16 := hav_add 12 (s_tick stT) (default [] ((r_hav (get_shadow stT (fst p))) !! (snd p / 16)))]> (r_hav (get_shadow stT (fst p))))
                             (r_havp (get_shadow stT (fst p))).
Proof.
  unfold get_shadow at 1. rewrite (proj1 (proj2 smg_proj)). unfold hdr_havoc, upd_shadow. cbn [s_shadow set_shadow].
  rewrite lookup_insert_eq. reflexivity.
Qed.

Lemma smg_group_p : (s_groups stF) !! p = Some (mkGhdr (Some mt) (Z.land ai 31)).
Proof. rewrite (proj1 (proj2 (proj2 smg_proj))). apply lookup_insert_eq. Qed.

Lemma smg_groups_inv b' gh : (s_groups stF) !! b' = Some gh -> (b' = p /\ gh = mkGhdr (Some mt) (Z.land ai 31)) \/ (b' <> p /\ (s_groups stT) !! b' = Some gh).
Proof.
  rewrite (proj1 (proj2 (proj2 smg_proj))). intros H. destruct (decide (b' = p)) as [->|NE].
  - left. rewrite lookup_insert_eq in H. inversion H. auto.
  - right. rewrite lookup_insert_ne in H by congruence. auto.
Qed.

Lemma smg_groups_old b' gh : (s_groups stT) !! p = None -> (s_groups stT) !! b' = Some gh -> (s_groups stF) !! b' = Some gh.
Proof.
  intros GN H. rewrite (proj1 (proj2 (proj2 smg_proj))). rewrite lookup_insert_ne; [exact H|]. intros ->. rewrite GN in H. discriminate.
Qed.

Lemma smg_grp_hdr_cov off : snd p <= off < snd p + 12 -> grp_hdr_cov stF (fst p) off.
Proof. intros Ho. exists p, (mkGhdr (Some mt) (Z.land ai 31)). split; [exact smg_group_p|]. split; [reflexivity| lia]. Qed.

Lemma smg_grp_hdr_cov_old q off : (s_groups stT) !! p = None -> grp_hdr_cov stT q off -> grp_hdr_cov stF q off.
Proof. intros GN (b' & gh & Hb & Hf & Ho). exists b', gh. split; [apply smg_groups_old; assumption| auto]. Qed.

Lemma smg_conc q : conc stF q = conc stT q.
Proof. unfold conc, get_region. rewrite (proj1 smg_proj). reflexivity. Qed.

Lemma smg_meta_slot q : meta_slot stT q <-> meta_slot stF q.
Proof. split; intros H; (eapply meta_slot_same_areas; [| exact H]); rewrite (proj1 (proj2 (proj2 (proj2 smg_proj)))); reflexivity. Qed.

Lemma smg_ret_span rid' S len :
  (exists g b, active stF sc = Some g /\ m_mem (get_meta_rec stF g) = Some b /\ rid' = fst b
     /\ S = snd b + 16 + get_stride (get_meta_rec stF g) * 0 /\ len = get_stride (get_meta_rec stF g) - 4) ->
  rid' = fst p /\ S = snd p + 16 /\ len = get_stride sm_rec - 4.
Proof.
  intros (g & b & HA & HM & -> & -> & ->). rewrite smg_active, Z.eqb_refl in HA. inversion HA; subst g.
  rewrite smg_rec_mt in HM |- *. cbn in HM. inversion HM; subst b. split; [reflexivity| split; [lia| reflexivity]].
Qed.
End SMG.

Lemma Zle_1_nonneg' x : 1 <= x < 2^28 -> 0 <= x /\ True.
Proof. intros H. split; [lia| exact I]. Qed.

Section SM.
Variables (stT : mstate) (sc cnt ai ml : Z) (mt : aptr) (rid : N) (r0 : region).
Let p : aptr := (rid, 0).
Let stF := st_model stT sc cnt ai mt p.
Hypothesis SC : 0 <= sc < 48.
Hypothesis CNT : 1 <= cnt <= 32.
Hypothesis AI : 0 <= ai <= cnt - 1.
Hypothesis ML : 1 <= ml < 2^28.
Hypothesis REC : get_meta_rec stT mt = mkMeta None None None 0 0 0 0 0 ml.
Hypothesis HrT : (s_regions stT) !! rid = Some r0.
Hypothesis Hk0 : r_kind r0 = RKGroup.
Hypothesis SHT : (s_shadow stT) !! rid = None.
Hypothesis GNT : forall off, (s_groups stT) !! (rid, off) = None.

Let P0 : 0 <= snd p := Z.le_refl 0.
Let ML0 : 0 <= ml := proj1 (Zle_1_nonneg' ml ML).

Lemma sm_proj :
  s_regions stF = s_regions stT /\ s_shadow stF = s_shadow (hdr_havoc p stT)
  /\ s_groups stF = <[p := mkGhdr (Some mt) (Z.land ai 31)]> (s_groups stT)
  /\ s_areas stF = s_areas stT /\ s_tick stF = s_tick stT /\ s_next_rid stF = s_next_rid stT /\ s_reserved stF = s_reserved stT
  /\ c_brk (ctx stF) = c_brk (ctx stT) /\ c_mmap_counter (ctx stF) = c_mmap_counter (ctx stT)
  /\ c_free_meta_head (ctx stF) = c_free_meta_head (ctx stT).
Proof. exact (smg_proj stT sc cnt ai mt p). Qed.

Lemma sm_rec_mt : get_meta_rec stF mt = sm_rec sc cnt ai ml mt p.
Proof. apply (smg_rec_mt stT sc cnt ai ml mt p); assumption. Qed.

Lemma sm_active c : active stF c = if c =? sc then Some mt else active stT c.
Proof. exact (smg_active stT sc cnt ai mt p c). Qed.

Lemma sm_ml_nz : (ml =? 0) = false.
Proof. apply Z.eqb_neq. lia. Qed.

Lemma sm_stride : get_stride (sm_rec sc cnt ai ml mt p) = if cnt =? 1 then ml * 4096 - 16 else 16 * size_class sc.
Proof. rewrite (smg_stride sc cnt ai ml mt p) by assumption. rewrite sm_ml_nz, andb_true_r. reflexivity. Qed.

Lemma sm_slot0 : 0 < get_stride (sm_rec sc cnt ai ml mt p) -> (s_slots stF) !! (rid, 16) = Some (mt, 0).
Proof. intros HS. apply (smg_slot0 stT sc cnt ai ml mt p); assumption. Qed.

Lemma sm_cell_read off : 0 <= off -> cell_read (get_shadow stF rid) off = if off <? 12 then Unknown 0 else Known 0.
Proof.
  clear ML0 P0 SC CNT AI ML REC HrT Hk0 GNT.
  intros Ho. unfold get_shadow. rewrite (proj1 (proj2 sm_proj)). fold (get_shadow (hdr_havoc p stT) rid).
  apply cell_read_hh0; [exact SHT| exact Ho].
Qed.

Lemma sm_cells_none off : (r_cells (get_shadow stF rid)) !! off = None.
Proof.
  clear ML0 P0 SC CNT AI ML REC HrT Hk0 GNT.
  change rid with (fst p). rewrite (smg_shadow_p stT sc cnt ai mt p). cbn [r_cells]. unfold p, get_shadow. cbn [fst]. rewrite SHT. cbn. apply lookup_empty.
Qed.

Lemma sm_hav_none off : 16 <= off -> (r_hav (get_shadow stF rid)) !! (off / 16) = None.
Proof.
  clear ML0 P0 SC CNT AI ML REC HrT Hk0 GNT. intros Ho. change rid with (fst p). rewrite (smg_shadow_p stT sc cnt ai mt p). cbn [r_hav]. unfold p. cbn [fst snd]. change (0 / 16) with 0.
  rewrite lookup_insert_ne by (Z.div_mod_to_equations; lia). unfold get_shadow. rewrite SHT. cbn. apply lookup_empty.
Qed.

Lemma sm_havp_none k : (r_havp (get_shadow stF rid)) !! k = None.
Proof.
  clear ML0 P0 SC CNT AI ML REC HrT Hk0 GNT.
  change rid with (fst p). rewrite (smg_shadow_p stT sc cnt ai mt p). cbn [r_havp]. unfold p, get_shadow. cbn [fst]. rewrite SHT. cbn. apply lookup_empty.
Qed.

Lemma sm_shadow_other q : q <> rid -> get_shadow stF q = get_shadow stT q.
Proof. intros NE. exact (smg_shadow_other stT sc cnt ai mt p q NE). Qed.

Lemma sm_groups_rid off gh : (s_groups stF) !! (rid, off) = Some gh -> off = 0 /\ gh = mkGhdr (Some mt) (Z.land ai 31).
Proof.
  intros H. destruct (smg_groups_inv stT sc cnt ai mt p _ _ H) as [[E ->]|[NE H']].
  - unfold p in E. inversion E. auto.
  - rewrite GNT in H'. discriminate.
Qed.

Lemma sm_grp_hdr_cov off : 0 <= off < 12 -> grp_hdr_cov stF rid off.
Proof. clear ML0 P0 CNT AI ML REC HrT Hk0 GNT SHT. intros Ho. apply (smg_grp_hdr_cov stT sc cnt ai mt p SC off). cbn. lia. Qed.

Lemma sm_grp_hdr_cov_old q off : grp_hdr_cov stT q off -> grp_hdr_cov stF q off.
Proof. intros H. exact (smg_grp_hdr_cov_old stT sc cnt ai mt p P0 q off (GNT 0) H). Qed.

Lemma sm_conc q : conc stF q = conc stT q.
Proof. exact (smg_conc stT sc cnt ai mt p q). Qed.

Lemma sm_meta_slot q : meta_slot stT q <-> meta_slot stF q.
Proof. exact (smg_meta_slot stT sc cnt ai mt p q). Qed.

Lemma sm_rdv o : rdv pans_mem o stF (rid, 13) = 0.
Proof. clear ML0 P0 SC CNT AI ML REC HrT Hk0 GNT. unfold rdv. cbn [fst snd]. rewrite sm_cell_read by lia. reflexivity. Qed.

Lemma sm_stride_mod16 : get_stride (get_meta_rec stF mt) mod 16 = 0.
Proof.
  rewrite sm_rec_mt, sm_stride. destruct (cnt =? 1).
  - replace (ml * 4096 - 16) with ((256 * ml - 1) * 16) by lia. apply Z_mod_mult.
  - rewrite Z.mul_comm. apply Z_mod_mult.
Qed.

Lemma sm_slot_ok (req nd : Z) :
  0 <= req < 2^32 -> req + 4 <= 16 * size_class sc ->
  r_len r0 = nd -> nd = 4096 * ml -> req + 20 <= nd -> 16 * size_class sc < 2^18 ->
  (cnt = 1 /\ nd < req + 20 + 4096 \/ 16 * size_class sc * cnt + 16 <= nd /\ nd < 16 * size_class sc * cnt + 16 + 4096) ->
  meta_slot stT mt ->
  slot_ok stF mt p r0 0 req
  /\ get_stride (get_meta_rec stF mt) = (if cnt =? 1 then nd - 16 else 16 * size_class sc)
  /\ 16 <= get_stride (get_meta_rec stF mt) /\ 16 + get_stride (get_meta_rec stF mt) <= nd.
Proof.
  intros RQ FIT LEN EML NDR SZ NDC MS.
  pose proof (size_class_range sc SC) as SZR.
  assert (RU : round_up_pg nd = nd).
  { rewrite EML. unfold round_up_pg. change (PGSZ - 1) with (Z.ones 12). rewrite Z.land_ones by lia. change (2 ^ 12) with 4096.
    replace (- (4096 * ml)) with ((- ml) * 4096) by lia. rewrite Z_mod_mult. lia. }
  assert (STR : get_stride (get_meta_rec stF mt) = if cnt =? 1 then nd - 16 else 16 * size_class sc).
  { rewrite sm_rec_mt, sm_stride. destruct (cnt =? 1); lia. }
  assert (S20 : 16 <= get_stride (get_meta_rec stF mt) /\ 16 + get_stride (get_meta_rec stF mt) * cnt <= nd
               /\ req + 4 <= get_stride (get_meta_rec stF mt) /\ get_stride (get_meta_rec stF mt) - 4 - req < 2^31
               /\ (forall off, 16 * off + req + 4 <= get_stride (get_meta_rec stF mt) -> off < 65536)).
  { rewrite STR. destruct (Z.eqb_spec cnt 1) as [E1|NE1].
    - rewrite E1. destruct NDC as [[_ X]|[X1 X2]]; (split; [lia|]; split; [lia|]; split; [lia|]; split; [lia|]; intros off Hoff; lia).
    - destruct NDC as [[X _]|[X1 X2]]; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. intros off Hoff. lia. }
  destruct S20 as (G20 & GSP & GFIT & G31 & G18).
  pose proof (mask_upto_range' ai ltac:(lia)) as [A1 A2]. pose proof (mask_upto_range' (cnt - 1) ltac:(lia)) as [C1 C2].
  assert (AM : mask_upto ai <= mask_upto (cnt - 1)) by (unfold mask_upto; apply Z.sub_le_mono_r; apply Z.pow_le_mono_r; lia).
  split; [| split; [exact STR| split; [exact G20| nia]]].
  constructor.
  - rewrite sm_rec_mt. reflexivity.
  - rewrite (proj1 sm_proj). exact HrT.
  - exact Hk0.
  - unfold p. cbn [snd]. lia.
  - reflexivity.
  - rewrite sm_rec_mt. cbn [m_last_idx sm_rec]. lia.
  - rewrite sm_rec_mt. cbn [m_last_idx sm_rec]. lia.
  - replace (m_last_idx (get_meta_rec stF mt)) with (cnt - 1) by (rewrite sm_rec_mt; reflexivity).
    rewrite LEN, RU. unfold p. cbn [snd]. replace (cnt - 1 + 1) with cnt by lia. lia.
  - exact G20.
  - apply sm_stride_mod16.
  - exact G31.
  - lia.
  - exact GFIT.
  - intros b' gh Hb' Hf. destruct b' as [b1 b2]. unfold p in Hf. cbn in Hf. subst b1. destruct (sm_groups_rid _ _ Hb') as [-> _]. unfold p. cbn [snd]. left. lia.
  - unfold p. cbn [fst snd]. replace (0 + 16 + get_stride (get_meta_rec stF mt) * 0 - 4) with 12 by lia. rewrite sm_cell_read by lia. reflexivity.
  - intros off O0 OF. rewrite Z.mul_0_r, Z.add_0_l. rewrite Z.mul_comm, Z_div_mult by lia. apply G18. exact OF.
  - unfold p. cbn [fst snd]. replace (0 + 16 + get_stride (get_meta_rec stF mt) * 0) with 16 by lia. apply sm_slot0. rewrite <- sm_rec_mt. lia.
  - apply (proj1 (sm_meta_slot mt)). exact MS.
  - rewrite sm_rec_mt. cbn [m_avail sm_rec]. lia.
  - rewrite sm_rec_mt. cbn [m_freed sm_rec]. lia.
  - rewrite sm_rec_mt. cbn [m_freeable sm_rec]. lia.
  - rewrite sm_rec_mt. cbn [m_maplen sm_rec]. lia.
  - rewrite sm_rec_mt. cbn [m_sizeclass sm_rec]. lia.
Qed.

Lemma sm_ret_span rid' S len :
  (exists g b, active stF sc = Some g /\ m_mem (get_meta_rec stF g) = Some b /\ rid' = fst b
     /\ S = snd b + 16 + get_stride (get_meta_rec stF g) * 0 /\ len = get_stride (get_meta_rec stF g) - 4) ->
  rid' = rid /\ S = 16.
Proof.
  intros H. destruct (smg_ret_span stT sc cnt ai ml mt p SC CNT REC P0 rid' S len H) as (-> & -> & _). unfold p. cbn. split; reflexivity.
Qed.
End SM.
End CEIL_WRAP_1.

