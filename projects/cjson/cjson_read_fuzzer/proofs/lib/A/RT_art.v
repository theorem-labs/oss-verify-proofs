(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes PropExec MState Mem Cells Step Frame Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg RT_defs RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_wf RT_rep RT_kit CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_kit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit.RT_shlem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_front.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition RTSH (st : rtstate) (x : Z) : Prop :=
     (SH AIMG_LO <= x < KLOWSHADOW_END)   (* [comment removed for export] *)
  \/ (KHIGHSHADOW_BEG <= x < KHIGHMEM_BEG)
  \/ (exists b, In b (d_sblocks (st_depot st)) /\ b <= x < b + STOREBLOCK_SIZE).
(* [comment removed for export] *)
Definition gwin_in (g : lghost) (x : word) : Prop :=
  in_winb (g_win g) x = true \/ SH alloc_ceiling <= bv_unsigned x < SH alloc_ceiling + 4096.
Definition GWIN (st : rtstate) (m : word -> option byte) (mo : Model) (g : lghost) : Prop :=
  forall x, gwin_in g x -> lzf mo x = true -> RTSH st (bv_unsigned x) -> m x <> None.
Lemma gwin_in_win : forall g x, in_winb (g_win g) x = true -> gwin_in g x.
Proof. intros g x H. left. exact H. Qed.
Lemma GWIN_win : forall st m mo g, GWIN st m mo g -> forall x, in_winb (g_win g) x = true -> lzf mo x = true -> RTSH st (bv_unsigned x) -> m x <> None.
Proof. intros st m mo g H x Hw. exact (H x (or_introl Hw)). Qed.
Lemma GWIN_ceilpage : forall st m mo g, GWIN st m mo g -> forall x, SH alloc_ceiling <= bv_unsigned x < SH alloc_ceiling + 4096 -> lzf mo x = true -> RTSH st (bv_unsigned x) -> m x <> None.
Proof. intros st m mo g H x Hv. exact (H x (or_intror Hv)). Qed.
(* [comment removed for export] *)
Lemma GWIN_grow : forall st m mo g g', GWIN st m mo g ->
  (forall x, in_winb (g_win g') x = true -> lzf mo x = true -> RTSH st (bv_unsigned x) -> in_winb (g_win g) x = true \/ m x <> None) ->
  GWIN st m mo g'.
Proof.
  intros st m mo g g' H NEW x [Hw|Hv] Hz Hr.
  - destruct (NEW x Hw Hz Hr) as [Ho|V]; [exact (H x (or_introl Ho) Hz Hr)| exact V].
  - exact (H x (or_intror Hv) Hz Hr).
Qed.

(* [comment removed for export] *)
Definition QUIET (st : rtstate) : Prop :=
  st_apend st = [] /\ st_spend st = [] /\ st_qpend st = [] /\ st_qtmp st = [] /\ st_qcur st = [].

(* [comment removed for export] *)
Definition sec_win (g : lghost) (mb n : Z) : Prop :=
  forall x : word, SH mb <= bv_unsigned x < SH (mb + smapsize n) -> in_winb (g_win g) x = true.
Definition SWIN (st : rtstate) (g : lghost) : Prop :=
  forall e, In e (st_sec st) -> sec_win g (fst e) (snd e).
Lemma SWIN_mono : forall st g g', SWIN st g -> gmono g g' -> SWIN st g'.
Proof.
  intros st g g' H GM e He x Hx. pose proof (H e He x Hx) as W. unfold in_winb in *. rewrite existsb_exists in W |- *.
  destruct W as (w & Hw & Hb). exists w. split; [apply GM; exact Hw| exact Hb].
Qed.
Lemma SWIN_st : forall st st' g, SWIN st g -> st_sec st' = st_sec st -> SWIN st' g.
Proof. intros st st' g H E e He. rewrite E in He. exact (H e He). Qed.
Lemma SWIN_nil : forall st g, st_sec st = [] -> SWIN st g.
Proof. intros st g E e He. rewrite E in He. destruct He. Qed.

Definition ARTd (sp0 SPB : Z) (LB : list cblock) (LF : list fframe) (TRS : list (list Z)) (B : Z)
                (m : word -> option byte) (mo : Model) (g : lghost) : Prop :=
  exists st, RTREP st m /\ RTWF st /\ RTMODEL st mo /\ LOK asegs mo /\ BINV mo g /\ GWIN st m mo g
        /\ FRONTR mo (g_res g)
        /\ st_sp0 st = sp0 /\ st_lb st = LB /\ st_lf st = LF /\ st_trs st = TRS /\ QUIET st
        /\ 0 <= B /\ B + rt_prov st <= g_res g /\ SPB <= sp0 /\ SWIN st g.

(* [comment removed for export] *)
Lemma ARTd_intro : forall st sp0 SPB LB LF TRS B m mo g,
  RTREP st m -> RTWF st -> RTMODEL st mo -> LOK asegs mo -> BINV mo g -> GWIN st m mo g -> FRONTR mo (g_res g) ->
  st_sp0 st = sp0 -> st_lb st = LB -> st_lf st = LF -> st_trs st = TRS -> QUIET st ->
  0 <= B -> B + rt_prov st <= g_res g -> SPB <= sp0 -> SWIN st g -> ARTd sp0 SPB LB LF TRS B m mo g.
Proof. intros. exists st. repeat (split; [assumption|]). assumption. Qed.

(* [comment removed for export] *)
Lemma GWIN_mem : forall st m m' mo g, GWIN st m mo g -> LOK asegs mo -> wmono asegs m m' -> GWIN st m' mo g.
Proof.
  intros st m m' mo g G2 HO WM x Hw Hz Hr.
  pose proof (G2 x Hw Hz Hr) as V. pose proof (lok_lazy_noseg asegs mo HO x (lzf_lazy mo x Hz)) as NS.
  apply (wview_noseg_some m' x NS). apply WM. unfold wview. destruct (m x); [discriminate| exfalso; exact (V eq_refl)].
Qed.
Lemma GWIN_vm_frame : forall st m mo mo' g, GWIN st m mo g ->
  m_vmmaps mo' = m_vmmaps mo -> m_vm_lazy mo' = m_vm_lazy mo -> GWIN st m mo' g.
Proof. intros st m mo mo' g G2 Hv Hl x Hw Hz. apply (G2 x Hw). unfold lzf in *. rewrite Hv, Hl in Hz. exact Hz. Qed.
(* [comment removed for export] *)
Lemma GWIN_st : forall st st' m mo g, GWIN st m mo g ->
  (forall b, In b (d_sblocks (st_depot st')) -> In b (d_sblocks (st_depot st))) -> GWIN st' m mo g.
Proof.
  intros st st' m mo g G2 SB x Hw Hz Hr. apply (G2 x Hw Hz).
  destruct Hr as [Hr|[Hr|(b & Hb & Hx)]]; [left; exact Hr| right; left; exact Hr| right; right; exists b; split; [apply SB; exact Hb| exact Hx]].
Qed.
(* [comment removed for export] *)
Lemma GWIN_open : forall st m mo G R lo hi R', GWIN st m mo (mkG G R) ->
  (forall x, lo <= bv_unsigned x < hi -> lzf mo x = true -> RTSH st (bv_unsigned x) -> m x <> None) ->
  GWIN st m mo (mkG ((lo, hi) :: G) R').
Proof.
  intros st m mo G R lo hi R' G2 NEWV. apply (GWIN_grow st m mo (mkG G R)); [exact G2|]. intros x Hw Hz Hr.
  cbn [g_win] in *. rewrite in_winb_cons in Hw. apply orb_true_iff in Hw as [Hw|Hw].
  - right. cbn [fst snd] in Hw. apply andb_true_iff in Hw as [A B]. apply Z.leb_le in A. apply Z.ltb_lt in B. apply NEWV; [lia| exact Hz| exact Hr].
  - left. exact Hw.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma qb_size_ge : forall b, QBATCH_SIZE <= qb_size b.
Proof.
  intros b. unfold qb_size.
  assert (G : forall l : list (Z * Z), 0 <= fold_right (fun (e : Z * Z) acc => Z.max (snd e) 1 + acc) 0 l).
  { induction l as [|e l IH]; cbn [fold_right]; [lia|]. pose proof (Z.le_max_r (snd e) 1). lia. }
  pose proof (G (qb_elems b)). lia.
Qed.

Lemma qc_bytes_cons : forall b q, qc_bytes (b :: q) = qb_size b + qc_bytes q.
Proof. reflexivity. Qed.
Lemma qc_bytes_nonneg : forall q, 0 <= qc_bytes q.
Proof. induction q as [|b q IH]; [cbn; lia|]. rewrite qc_bytes_cons. pose proof (qb_size_ge b). unfold QBATCH_SIZE in *. lia. Qed.

Lemma rt_prov_nonneg : forall st, RTWF st -> 0 <= rt_prov st.
Proof.
  intros st WF. unfold rt_prov.
  pose proof (prov_classes_nonneg st).
  assert (0 <= prov_nb st) by (unfold prov_nb; destruct (st_qthread st); unfold NB; lia).
  pose proof (prov_q_nonneg st (qc_bytes_nonneg _)).
  assert (0 <= prov_ptr st) by (unfold prov_ptr; lia).
  assert (0 <= prov_live st).
  { apply prov_live_nonneg. apply Forall_forall. intros b Hb.
    destruct (wk_block st (wf_blocks_ok st WF) b ltac:(unfold all_blocks; apply in_or_app; left; exact Hb)) as [Hn _]. lia. }
  pose proof (prov_quar_nonneg st).
  assert (0 <= prov_depot st).
  { unfold prov_depot. pose proof (wd_nnb_max st (wf_depot_ok st WF)) as HN. pose proof (wd_nsb_max st (wf_depot_ok st WF)) as HS.
    unfold NODEBLOCK_SIZE, STOREBLOCK_SIZE. nia. }
  pose proof (prov_slots_nonneg st). pose proof (prov_l24_nonneg st). pose proof (prov_emb_nonneg st).
  lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem artd_binv : forall sp0 SPB LB LF TRS B m mo g,
  ARTd sp0 SPB LB LF TRS B m mo g -> LOK asegs mo /\ BINV mo g /\ 0 <= B <= g_res g.
Proof.
  intros sp0 SPB LB LF TRS B m mo g (st & HR & WF & HM & HO & HB & HG & HFR & _ & _ & _ & _ & _ & H0 & H1 & H2 & HSW).
  pose proof (rt_prov_nonneg st WF). split; [exact HO|]. split; [exact HB|]. lia.
Qed.

Theorem artd_lower : forall sp0 SPB SPB' LB LF TRS B B' m mo g,
  ARTd sp0 SPB LB LF TRS B m mo g -> SPB' <= SPB -> 0 <= B' <= B -> ARTd sp0 SPB' LB LF TRS B' m mo g.
Proof.
  intros sp0 SPB SPB' LB LF TRS B B' m mo g (st & HR & WF & HM & HO & HB & HG & HFR & ? & ? & ? & ? & HQ & H0 & H1 & H2 & HSW) HS HB'.
  exists st. repeat (split; [assumption|]). split; [lia|]. split; [lia|]. split; [lia| exact HSW].
Qed.

Lemma LOK_vm_frame : forall mo mo', LOK asegs mo ->
  m_vmmaps mo' = m_vmmaps mo -> m_vm_lazy mo' = m_vm_lazy mo -> m_halted mo' = None -> LOK asegs mo'.
Proof.
  intros mo mo' HO Hv Hl Hh. destruct HO. constructor; rewrite ?Hv, ?Hl; try assumption.
Qed.

Lemma BINV_vm_frame : forall mo mo' g, BINV mo g ->
  m_vmmaps mo' = m_vmmaps mo -> m_vm_lazy mo' = m_vm_lazy mo -> BINV mo' g.
Proof.
  intros mo mo' g (H1 & H2 & H3) Hv Hl. unfold BINV, eager_used in *. rewrite Hv, Hl. auto.
Qed.

Theorem artd_model_frame : forall sp0 SPB LB LF TRS B m mo mo' g,
  ARTd sp0 SPB LB LF TRS B m mo g ->
  m_vmmaps mo' = m_vmmaps mo -> m_vm_lazy mo' = m_vm_lazy mo -> m_halted mo' = None ->
  ARTd sp0 SPB LB LF TRS B m mo' g.
Proof.
  intros sp0 SPB LB LF TRS B m mo mo' g (st & HR & WF & HM & HO & HB & HG & HFR & ? & ? & ? & ? & HQ & H0 & H1 & H2 & HSW) Hv Hl Hh.
  exists st. split; [exact HR|]. split; [exact WF|]. split; [eapply RTMODEL_vm_frame; eauto|].
  split; [eapply LOK_vm_frame; eauto|]. split; [eapply BINV_vm_frame; eauto|]. split; [eapply GWIN_vm_frame; eauto|].
  split; [eapply FRONTR_vm; eauto|].
  repeat (split; [assumption|]). assumption.
Qed.

Lemma NoDup_map_fst_app_l : forall {A B} (l1 l2 : list (A * B)), List.NoDup (map fst (l1 ++ l2)) -> List.NoDup (map fst l1).
Proof. intros A B l1 l2 H. rewrite map_app in H. apply NoDup_app_remove_r in H. exact H. Qed.

Theorem artd_nodup : forall sp0 SPB LB LF TRS B m mo g,
  ARTd sp0 SPB LB LF TRS B m mo g -> NoDup (map fst LB) /\ NoDup (map fst LF).
Proof.
  intros sp0 SPB LB LF TRS B m mo g (st & HR & WF & HM & HO & HB & HG & HFR & ? & <- & <- & ? & _ & _).
  split; apply NoDup_ListNoDup.
  - pose proof (wk_nodup st (wf_blocks_ok st WF)) as ND. unfold all_blocks in ND. eapply NoDup_map_fst_app_l. exact ND.
  - exact (wff_nodup st (wf_fs_ok st WF)).
Qed.

(* [comment removed for export] *)
Lemma R_link_at : forall m a v, R_link m -> alink_val a = Some v -> cells_at asegs m a [C8 (wz v)].
Proof. intros m a v [HL _] Hv. apply HL. apply alink_val_In. exact Hv. Qed.

Theorem artd_cjst : forall sp0 SPB LB LF TRS B m mo g, ARTd sp0 SPB LB LF TRS B m mo g -> ACJST m.
Proof.
  intros sp0 SPB LB LF TRS B m mo g (st & HR & _).
  pose proof (rr_consts st m HR) as HC. pose proof (rr_link st m HR) as HL.
  unfold ACJST. split; [|split; [|split]].
  - unfold R_consts in HC. apply proj2 in HC. do 19 (apply proj2 in HC). exact (proj1 HC).
  - destruct (gerror0_cell m) as [v Hv]. exists v. exact Hv.
  - destruct (gerror1_cell m) as [v Hv]. exists v. exact Hv.
  - apply (R_link_at m ALCONV ADOTSTR HL). vm_compute. reflexivity.
Qed.

Theorem artd_ssp : forall sp0 SPB LB LF TRS B m mo g, ARTd sp0 SPB LB LF TRS B m mo g ->
  cells_at asegs m AGOT_SSP [C8 (wz ASSP)] /\ exists canary : word, cells_at asegs m ASSP [C8 canary].
Proof.
  intros sp0 SPB LB LF TRS B m mo g (st & HR & _). pose proof (rr_link st m HR) as HL. split.
  - apply (R_link_at m AGOT_SSP ASSP HL). vm_compute. reflexivity.
  - destruct (ssp_cell m) as [v [Hv _]]. exists v. exact Hv.
Qed.

(* [comment removed for export] *)
Lemma got_ssp_image :
  forallb (fun a => match wview asegs (fun _ => None) (wa a) with Some _ => true | None => false end)
          (map (fun i => AGOT_SSP + Z.of_nat i) (seq 0 8)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma got_ssp_rw : forall m, R_link m -> rw_cells asegs m AGOT_SSP [C8 (wz ASSP)].
Proof.
  intros m HL. split; [apply (R_link_at m AGOT_SSP ASSP HL); vm_compute; reflexivity|].
  unfold wr_at. split; [unfold AGOT_SSP; lia|]. split; [unfold AGOT_SSP; cbn; lia|].
  intros i Hi. cbn in Hi. rewrite wview_empty. destruct (m (wa (AGOT_SSP + i))); [discriminate|].
  pose proof got_ssp_image as F. rewrite forallb_forall in F.
  specialize (F (AGOT_SSP + i) ltac:(apply in_map_iff; exists (Z.to_nat i); split; [lia| apply in_seq; lia])). cbn beta in F.
  destruct (wview asegs (fun _ => None) (wa (AGOT_SSP + i))); [discriminate| discriminate].
Qed.
Theorem artd_sspw : forall sp0 SPB LB LF TRS B m mo g, ARTd sp0 SPB LB LF TRS B m mo g ->
  exists canary : word, rw_cells asegs m 0xa2c08 [C8 (Z_to_bv 64 0x5fd290)] /\ rw_cells asegs m 0x5fd290 [C8 canary].
Proof.
  intros sp0 SPB LB LF TRS B m mo g (st & HR & _). destruct (ssp_cell m) as [v Hv]. exists v. split; [| exact Hv].
  exact (got_ssp_rw m (rr_link st m HR)).
Qed.

Theorem artd_lowshadow : forall sp0 SPB LB LF TRS B m mo g, ARTd sp0 SPB LB LF TRS B m mo g ->
  forall a, SH AIMG_LO <= a < SH AIMG_HI -> rw_cells asegs m a [C1 (zb (alowsh a))].
Proof. intros sp0 SPB LB LF TRS B m mo g (st & HR & _) a Ha. apply (rr_lowshadow st m HR). exact Ha. Qed.

(* [comment removed for export] *)
Lemma cflags_byte : forall m k, cells_at asegs m A_CFLAGS [CB 288 (map zb cflags_bytes)] -> (k < 288)%nat ->
  cells_at asegs m (A_CFLAGS + Z.of_nat k) [C1 (nth k (map zb cflags_bytes) (zb 0))].
Proof.
  intros m k [Hwf HB] Hk. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB.
  assert (L : length (map zb cflags_bytes) = 288%nat) by (cbn in Hwf; tauto).
  split; [cbn; tauto|]. cbn [cells_bytes cbytes]. destruct HB as (H0 & H1 & HB). split; [lia|]. split; [cbn; lia|].
  intros i Hi. cbn in Hi. assert (i = 0)%nat by lia. subst i. rewrite Z.add_0_r. rewrite (HB k) by lia.
  cbn [nth_error app]. apply nth_error_nth'. lia.
Qed.

(* [comment removed for export] *)
Lemma Z_to_le_bytes_nth : forall n z i, (i < n)%nat ->
  exists b : byte, nth_error (Z_to_le_bytes n z) i = Some b /\ bv_unsigned b = (z / 2 ^ (8 * Z.of_nat i)) mod 256.
Proof.
  intros n z i. revert n z. induction i as [|i IH]; intros n z Hi.
  - destruct n as [|n]; [lia|]. cbn [Z_to_le_bytes nth_error]. eexists. split; [reflexivity|].
    rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. rewrite Z.mul_0_r, Z.pow_0_r, Z.div_1_r. reflexivity.
  - destruct n as [|n]; [lia|]. cbn [Z_to_le_bytes nth_error]. destruct (IH n (Z.shiftr z 8) ltac:(lia)) as (b & Hb & Hv).
    exists b. split; [exact Hb|]. rewrite Hv. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_div by lia.
    rewrite <- Z.pow_add_r by lia. replace (8 + 8 * Z.of_nat i) with (8 * Z.of_nat (S i)) by lia. reflexivity.
Qed.

Lemma cells_at_C8_of_bytes : forall m a v, 0 <= v < 2^64 ->
  (forall i, (i < 8)%nat -> exists b : byte, cells_at asegs m (a + Z.of_nat i) [C1 b] /\ bv_unsigned b = (v / 2 ^ (8 * Z.of_nat i)) mod 256) ->
  cells_at asegs m a [C8 (wz v)].
Proof.
  intros m a v Hv H.
  destruct (H 0%nat ltac:(lia)) as (b0 & [_ (A0 & _ & _)] & _). destruct (H 7%nat ltac:(lia)) as (b7 & [_ (_ & A7 & _)] & _). change (Z.of_nat (length (cells_bytes [C1 b7]))) with 1 in A7.
  split; [cbn; tauto|]. cbn [cells_bytes cbytes flat_map app]. rewrite app_nil_r. split; [lia|]. split; [rewrite length_le8; lia|].
  intros i Hi. rewrite length_le8 in Hi. destruct (H i Hi) as (b & [_ (_ & _ & Hb)] & Hbv).
  specialize (Hb 0%nat ltac:(cbn; lia)). cbn [nth_error] in Hb. rewrite Z.add_0_r in Hb. rewrite Hb.
  unfold le8, word_to_le_bytes. destruct (Z_to_le_bytes_nth 8 (bv_unsigned (wz v)) i Hi) as (b' & Hb' & Hv'). rewrite Hb'. f_equal.
  apply bv_eq. rewrite Hbv, Hv'. unfold wz. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). rewrite (Z.mod_small v (2^64)) by lia. reflexivity.
Qed.

Lemma cells_at_C4_of_bytes : forall m a v, 0 <= v < 2^64 ->
  (forall i, (i < 4)%nat -> exists b : byte, cells_at asegs m (a + Z.of_nat i) [C1 b] /\ bv_unsigned b = (v / 2 ^ (8 * Z.of_nat i)) mod 256) ->
  cells_at asegs m a [C4 (wz v)].
Proof.
  intros m a v Hv H.
  destruct (H 0%nat ltac:(lia)) as (b0 & [_ (A0 & _ & _)] & _). destruct (H 3%nat ltac:(lia)) as (b7 & [_ (_ & A7 & _)] & _). change (Z.of_nat (length (cells_bytes [C1 b7]))) with 1 in A7.
  split; [cbn; tauto|]. cbn [cells_bytes cbytes flat_map app]. rewrite app_nil_r. split; [lia|]. split; [rewrite length_le4; lia|].
  intros i Hi. rewrite length_le4 in Hi. destruct (H i Hi) as (b & [_ (_ & _ & Hb)] & Hbv).
  specialize (Hb 0%nat ltac:(cbn; lia)). cbn [nth_error] in Hb. rewrite Z.add_0_r in Hb. rewrite Hb.
  unfold le4, word_to_le_bytes. destruct (Z_to_le_bytes_nth 4 (bv_unsigned (wz v)) i Hi) as (b' & Hb' & Hv'). rewrite Hb'. f_equal.
  apply bv_eq. rewrite Hbv, Hv'. unfold wz. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). rewrite (Z.mod_small v (2^64)) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma aflags_byte : forall m k, cells_at asegs m A_AFLAGS [CB 120 (map zb aflags_bytes)] -> (k < 120)%nat ->
  cells_at asegs m (A_AFLAGS + Z.of_nat k) [C1 (nth k (map zb aflags_bytes) (zb 0))].
Proof.
  intros m k [Hwf HB] Hk. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB.
  assert (L : length (map zb aflags_bytes) = 120%nat) by (cbn in Hwf; tauto).
  split; [cbn; tauto|]. cbn [cells_bytes cbytes]. destruct HB as (H0 & H1 & HB). split; [lia|]. split; [cbn; lia|].
  intros i Hi. cbn in Hi. assert (i = 0)%nat by lia. subst i. rewrite Z.add_0_r. rewrite (HB k) by lia.
  cbn [nth_error app]. apply nth_error_nth'. lia.
Qed.

(* [comment removed for export] *)
Lemma cflags_word : forall m k v, cells_at asegs m A_CFLAGS [CB 288 (map zb cflags_bytes)] -> (k + 8 <= 288)%nat -> 0 <= v < 2^64 ->
  (forall i, (i < 8)%nat -> nth (k + i) cflags_bytes 0 = (v / 2 ^ (8 * Z.of_nat i)) mod 256) ->
  cells_at asegs m (A_CFLAGS + Z.of_nat k) [C8 (wz v)].
Proof.
  intros m k v HC Hk Hv HB. apply cells_at_C8_of_bytes; [exact Hv|]. intros i Hi.
  exists (nth (k + i) (map zb cflags_bytes) (zb 0)). split.
  - replace (A_CFLAGS + Z.of_nat k + Z.of_nat i) with (A_CFLAGS + Z.of_nat (k + i)) by lia. apply cflags_byte; [exact HC| lia].
  - change (zb 0) with ((fun z => zb z) 0). rewrite map_nth. unfold zb. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
    rewrite (HB i Hi). apply Z.mod_mod. lia.
Qed.

Lemma rtrep_artcells : forall st m, RTREP st m -> ARTCELLS m.
Proof.
  intros st m HR.
  pose proof (rr_consts st m HR) as HC. pose proof (rr_link st m HR) as HL.
  unfold R_consts in HC.
  destruct HC as (Hsho & Huar & Haf & Hcf & Hpg & Hkhe & Hkmb & Hkme & Hinit & Hmcs & Hcanp & Htki & Htk & Hmrn & Hoom & Hdying & Hverb & Hmfh & Hlsan & Hia & Hhooks & Hlibc & Hmug & Hgreg & Htpcg & _).
  assert (W : forall z, wz z = Z_to_bv 64 z) by reflexivity.
  assert (W1' : forall z, zb z = Z_to_bv 8 z) by reflexivity.
  assert (CFB : forall k c, (k < 288)%nat -> nth k cflags_bytes 0 = c -> cells_at asegs m (A_CFLAGS + Z.of_nat k) [C1 (zb c)]).
  { intros k c Hk Hc. pose proof (cflags_byte m k Hcf Hk) as H. change (zb 0) with ((fun z => zb z) 0) in H. rewrite map_nth in H. rewrite Hc in H. exact H. }
  unfold ARTCELLS. rewrite <- !W, <- !W1'.
  repeat lazymatch goal with |- _ /\ _ => split | _ => idtac end;
    try (apply (R_link_at m _ _ HL); vm_compute; reflexivity).
  - exact Hsho.
  - exact Huar.
  - exact Hkmb.
  - exact Hkme.
  - exact Hkhe.
  - (* [comment removed for export] *)
    exact (proj1 (proj1 (cells_at_app m A_ASAN_INITED [C1 (zb 1); C1 (zb 1)] [C1 (zb 0)]) Hinit)).
  - apply (CFB 245%nat); [lia| reflexivity].
  - apply (CFB 251%nat); [lia| reflexivity].
  - exact Hcanp.
  - apply (cflags_word m 120 0xffffffffffffffff Hcf); [lia| lia|]. intros i Hi. do 8 (destruct i as [|i]; [vm_compute; reflexivity|]). lia.
  - exact Hpg.
  - apply (cflags_word m 144 0 Hcf); [lia| lia|]. intros i Hi. do 8 (destruct i as [|i]; [vm_compute; reflexivity|]). lia.
  - apply (CFB 244%nat); [lia| reflexivity].
  - apply (CFB 219%nat); [lia| reflexivity].
  - (* [comment removed for export] *)
    apply (proj2 (cells_at_app m 0xa1fc0 [C8 (wz 1)] [C8 (wz 0x13bd9c)])). split; apply (R_link_at m _ _ HL); vm_compute; reflexivity.
  - exact Hdying.
  - exact Hlibc.
  - destruct (ssp_cell m) as [v [Hv _]]. exists v. exact Hv.
  - apply (CFB 84%nat); [lia| reflexivity].
  - (* [comment removed for export] *)
    apply (cells_at_C4_of_bytes m _ 1); [lia|]. intros i Hi. exists (nth (24 + i) (map zb aflags_bytes) (zb 0)). split.
    + replace (0xa7a90 + Z.of_nat i) with (A_AFLAGS + Z.of_nat (24 + i)) by (unfold A_AFLAGS; lia). apply aflags_byte; [exact Haf| lia].
    + change (zb 0) with ((fun z => zb z) 0). rewrite map_nth. unfold zb. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
      do 4 (destruct i as [|i]; [vm_compute; reflexivity|]). lia.
  - exact Hmug.
  - exact Hgreg.
  - exact (proj2 HL).
  - exact Htpcg.
Qed.
Theorem artd_rtcells : forall sp0 SPB LB LF TRS B m mo g, ARTd sp0 SPB LB LF TRS B m mo g -> ARTCELLS m.
Proof. intros sp0 SPB LB LF TRS B m mo g (st & HR & _). exact (rtrep_artcells st m HR). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rw_cell1_some : forall m a v, rw_cells asegs m a [C1 v] -> AIMG_HI <= a -> m (wa a) <> None.
Proof.
  intros m a v [[_ (H0 & H1 & _)] (_ & _ & HW)] Ha. change (Z.of_nat (length (cells_bytes [C1 v]))) with 1 in H1.
  apply wview_noseg_some; [apply noseg_Z; lia|]. rewrite <- (Z.add_0_r a). apply HW. change (Z.of_nat (cells_size [C1 v])) with 1. lia.
Qed.

Lemma rw_cell1_shb : forall m x v, rw_cells asegs m (SH x) [C1 (zb v)] -> 0 <= x < 2^47 -> shb m x v.
Proof.
  intros m x v [[_ (H0 & H1 & HB)] _] Hx. unfold shb. apply rt_mrd_shadow; [exact Hx|].
  specialize (HB 0%nat ltac:(cbn; lia)). change (Z.of_nat 0) with 0 in HB. rewrite Z.add_0_r in HB. cbn in HB. exact HB.
Qed.

Definition glob_ok_b (a n : Z) : bool :=
  forallb (fun i => let v := alowsh (SH (a + i)) in (v =? 0) || (((a + i) mod 8 <? v) && (v <? 8)))
          (map Z.of_nat (seq 0 (Z.to_nat n))).

Lemma lowsh_shadow_ok : forall m a n, R_lowshadow m ->
  AIMG_LO <= a -> 0 < n -> a + n <= AIMG_HI -> glob_ok_b a n = true -> shadow_ok m a n.
Proof.
  intros m a n HL Ha Hn Hhi Hb. unfold AIMG_LO, AIMG_HI in *.
  assert (SHLO : SH 0x10000 = 0x7fffa000) by reflexivity. assert (SHHI : SH 0x5ff000 = 0x800b7e00) by reflexivity.
  split.
  - intros i Hi. unfold glob_ok_b in Hb. rewrite forallb_forall in Hb.
    specialize (Hb i ltac:(apply in_map_iff; exists (Z.to_nat i); split; [lia| apply in_seq; lia])). cbn beta in Hb. cbn zeta in Hb.
    exists (alowsh (SH (a + i))). split.
    + apply rw_cell1_shb; [|lia]. apply HL. unfold AIMG_LO, AIMG_HI. split; [|]; [pose proof (rt_SH_mono 0x10000 (a+i) ltac:(lia)); lia| pose proof (rt_SH_lt_of (a+i) 0x5ff000 ltac:(Z.div_mod_to_equations; lia)); lia].
    + apply orb_true_iff in Hb. destruct Hb as [Hb|Hb]; [left; apply Z.eqb_eq; exact Hb| right].
      apply andb_true_iff in Hb as [H1 H2]. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. lia.
  - intros j Hj. 
    pose proof (rt_SH_mono 0x10000 a ltac:(lia)) as M1. pose proof (rt_SH_lt_of (a + n - 1) 0x5ff000 ltac:(Z.div_mod_to_equations; lia)) as M2.
    assert (R : 0x7fffa000 <= j < 0x800b7e00) by (Z.div_mod_to_equations; lia).
    pose proof (HL j ltac:(unfold AIMG_LO, AIMG_HI; rewrite SHLO, SHHI; exact R)) as HC.
    eapply rw_cell1_some; [exact HC| unfold AIMG_HI; lia].
Qed.

(* [comment removed for export] *)
Lemma lowshadow_musl_lits : forall m, R_lowshadow m ->
  shadow_ok m 0x10b84 9 /\ shadow_ok m 0x1380a 19 /\ shadow_ok m 0x142a3 2.
Proof.
  intros m HL. unfold AIMG_LO, AIMG_HI.
  split; [| split]; (apply lowsh_shadow_ok; [exact HL| unfold AIMG_LO; lia| lia| unfold AIMG_HI; lia| vm_compute; reflexivity]).
Qed.

Theorem artd_global_shadow : forall sp0 SPB LB LF TRS B m mo g, ARTd sp0 SPB LB LF TRS B m mo g ->
  Forall (fun gs => shadow_ok m (fst gs) (snd gs)) AGLOB_STRS /\ shadow_ok m AHOOKS 24
  /\ shadow_ok m AGERROR0 8 /\ shadow_ok m AGERROR1 8.
Proof.
  intros sp0 SPB LB LF TRS B m mo g (st & HR & _). pose proof (rr_lowshadow st m HR) as HL.
  assert (T : forall a n, AIMG_LO <= a -> 0 < n -> a + n <= AIMG_HI -> glob_ok_b a n = true -> shadow_ok m a n)
    by (intros; eapply lowsh_shadow_ok; eauto).
  unfold AGLOB_STRS, AHOOKS, AGERROR0, AGERROR1, AIMG_LO, AIMG_HI in *.
  repeat lazymatch goal with
    | |- _ /\ _ => split
    | |- Forall _ _ => constructor
    | |- shadow_ok _ _ _ => cbn [fst snd]; apply T; [lia| lia| lia| vm_compute; reflexivity]
    end.
Qed.


End CeilWrap.
