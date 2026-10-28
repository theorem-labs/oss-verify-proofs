(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Tac Image ZBridge SysStep Walk.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Common Require Import SFModel.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Malloc Require Export MallocRep.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Export UImg.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree Malloc MallocCtrl.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Malloc Require Import ProgDeps.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import RunDraw.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.
Definition RCTX : Z := 0x4e330.
Definition RMLOCK : Z := 0x4e328.
Definition RLIBC : Z := 0x4e2b8.
Definition RNEED_LOCKS : Z := 0x4e2bb.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition RSIZE_CLASSES : Z := 0x1044c.
Definition RDEBRUIJN : Z := 0x1042c.
Definition RSMALL_CNT : Z := 0x104ac.
Definition RMED_CNT : Z := 0x104c7.
Definition RGOT_SSP : Z := 0x1ccb8.      (* [comment removed for export] *)
Definition RSSP_GUARD : Z := 0x4e298.    (* [comment removed for export] *)
Definition RATP : Z := 0x2e030.          (* [comment removed for export] *)
Definition RERRNO : Z := 0x2df8c.        (* [comment removed for export] *)

Definition rget_meta_entry : Z := 0x146a4.
Definition rmalloc_entry : Z := 0x14e64.      (* [comment removed for export] *)
Definition rfree_entry : Z := 0x144d8.        (* [comment removed for export] *)
Definition ralloc_meta_entry : Z := 0x14b8c.
Definition ralloc_slot_entry : Z := 0x151d4.
Definition renframe_entry : Z := 0x15a78.
Definition rnontrivial_free_entry : Z := 0x147b4.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rlock_entry : Z := 0x1b848.
Definition runlock_entry : Z := 0x1bad0.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ref_reserved : list (Z * Z) := [(0x10000, 0x2000); (0x12000, 0xa000); (0x1c000, 0x1000); (0x1d000, 0x32000)].

#[using="Type"] Lemma ref_reserved_plain : ref_reserved = ubsan_reserved.
Proof. reflexivity. Qed.

#[using="Type"] Lemma reservedZ_ref : reservedZ usegs = ref_reserved.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Section MREP.
Variable st : mstate.
Variable m : word -> option byte.

Definition rsecw : word := wz (SECRET * c_init_done (ctx st)).
Definition rctx_head_cells : list cell :=
  let c := ctx st in
  [C8 rsecw; C4 (wz (c_init_done c)); C4 (wz (c_mmap_counter c));
   C8 (pw st (c_free_meta_head c)); C8 (pw st (c_avail_meta c));
   C8 (wz (c_avail_meta_count c)); C8 (wz (c_avail_meta_area_count c)); C8 (wz (c_meta_alloc_shift c));
   C8 (pw st (c_meta_area_head c)); C8 (pw st (c_meta_area_tail c)); C8 (pw st (c_avail_meta_areas c))].
#[using="Type"] Lemma rctx_head_cells_tl : tl rctx_head_cells = tl (ctx_head_cells st).
Proof. reflexivity. Qed.


Definition rmrep_ctx : Prop :=
  rw_cells usegs m RCTX rctx_head_cells
  /\ u64arr usegs m (RCTX + 80) (actives st)
  /\ u64arr usegs m (RCTX + 464) (usages st)
  /\ u8arr usegs m (RCTX + 848) (unmap_seqs st)
  /\ u8arr usegs m (RCTX + 880) (bouncess st)
  /\ rw_cells usegs m (RCTX + 912) (ctx_tail_cells st).

Definition rmrep_globals : Prop :=
  rw_cells usegs m RMLOCK [C4 (wz 0)]
  /\ rw_cells usegs m RNEED_LOCKS [C1 (b8 0)]
  /\ rw_cells usegs m RPAGE_SIZE [C8 (wz 4096)]
  /\ rw_cells usegs m RGOT_SSP [C8 (wz RSSP_GUARD)]
  /\ rw_cells usegs m RSSP_GUARD [C8 CAN].

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rarea_rep (a : aptr) (ar : area) : Prop :=
  rw_cells usegs m (conc st a) [C8 (wz SECRET); C8 (pw st (a_next ar)); C4 (wz (a_nslots ar)); C4 (wz 0)]
  /\ (forall k, 0 <= k < NSLOTS ->
        rw_cells usegs m (conc st a + AREA_HDR + META_SIZE * k)
                 (meta_cells st (get_meta_rec st (aadd a (AREA_HDR + META_SIZE * k)))))
  /\ rw_cells usegs m (conc st a + 4064) [CB 32 (zeros 32)].
Definition rmrep_areas : Prop :=
  forall a ar, (s_areas st) !! a = Some ar -> rarea_rep a ar.

(* [comment removed for export] *)
Definition rgroup_rep (b : aptr) (gh : ghdr) : Prop :=
  exists w8 : byte,
    rw_cells usegs m (conc st b) [C8 (pw st (g_meta gh)); C1 w8]
    /\ Z.land (bv_unsigned w8) 31 = g_active_idx gh.
Definition rmrep_groups : Prop :=
  forall b gh, (s_groups st) !! b = Some gh -> rgroup_rep b gh.

(* [comment removed for export] *)
Definition rshadow_rep (rid : N) (r : region) : Prop :=
  wr_at usegs m (r_base r) (round_up_pg (r_len r))
  /\ forall o v, 0 <= o < round_up_pg (r_len r) ->
       cell_read (get_shadow st rid) o = Known v ->
       bytes_at usegs m (r_base r + o) [b8 v] /\ 0 <= v < 256.
Definition rmrep_shadow : Prop :=
  forall rid r, (s_regions st) !! rid = Some r -> r_kind r = RKGroup -> rshadow_rep rid r.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rstatics : Prop :=
  s_reserved st = ref_reserved /\ s_atop st = ATOP /\ s_secret st = 0.

#[using="Type"] Lemma rstatics_reserved : rstatics -> s_reserved st = ref_reserved. Proof. intros (H & _ & _); exact H. Qed.
#[using="Type"] Lemma rstatics_atop : rstatics -> s_atop st = ATOP. Proof. intros (_ & H & _); exact H. Qed.
#[using="Type"] Lemma rstatics_secret : rstatics -> s_secret st = 0. Proof. intros (_ & _ & H); exact H. Qed.

Definition rregions_wf : Prop :=
  rstatics
  /\ (forall rid r, (s_regions st) !! rid = Some r ->
        0 < r_base r /\ r_base r mod 4096 = 0 /\ 0 <= r_len r
        /\ r_base r + round_up_pg (r_len r) <= ATOP
        /\ ranges_free ref_reserved (r_base r) (round_up_pg (r_len r)) = true)
  /\ (forall rid1 r1 rid2 r2, (s_regions st) !! rid1 = Some r1 -> (s_regions st) !! rid2 = Some r2 -> rid1 <> rid2 ->
        r_base r1 + round_up_pg (r_len r1) <= lr_lo r2 \/ r_base r2 + round_up_pg (r_len r2) <= lr_lo r1)
  (* [comment removed for export] *)
  /\ (forall a ar, (s_areas st) !! a = Some ar ->
        exists r, (s_regions st) !! (fst a) = Some r /\ 0 <= snd a /\ snd a + 4096 <= round_up_pg (r_len r) /\ snd a mod 4096 = 0
                  /\ r_kind r <> RKGroup /\ lr_lo r <= r_base r + snd a)
  /\ (forall b gh, (s_groups st) !! b = Some gh ->
        exists r, (s_regions st) !! (fst b) = Some r /\ r_kind r = RKGroup /\ 0 <= snd b /\ snd b + 16 <= round_up_pg (r_len r) /\ snd b mod 16 = 0).

Definition rmrep : Prop :=
  rregions_wf /\ rmrep_ctx /\ rmrep_globals /\ rmrep_areas /\ rmrep_groups /\ rmrep_shadow.

End MREP.

#[using="Type"] Lemma rstatics_same : forall st st', s_reserved st' = s_reserved st -> s_atop st' = s_atop st -> s_secret st' = s_secret st ->
  rstatics st -> rstatics st'.
Proof. intros st st' E1 E2 E3 (H1 & H2 & H3). unfold rstatics. rewrite E1, E2, E3. auto. Qed.
#[using="Type"] Lemma rregions_wf_reserved : forall st, rregions_wf st -> s_reserved st = ref_reserved.
Proof. intros st ((H & _) & _). exact H. Qed.
#[using="Type"] Lemma rregions_wf_atop : forall st, rregions_wf st -> s_atop st = ATOP.
Proof. intros st ((_ & H & _) & _). exact H. Qed.

(* [comment removed for export] *)
Definition s_statics (st : mstate) : Z * Z * list (Z * Z) := (s_atop st, s_secret st, s_reserved st).
#[using="Type"] Lemma rregions_wf_restatics : forall st st',
  s_regions st' = s_regions st -> s_areas st' = s_areas st -> s_groups st' = s_groups st -> s_statics st' = s_statics st ->
  rregions_wf st -> rregions_wf st'.
Proof.
  intros st st' ER EA EG EST (RS & WR & DJ & WA & WG). unfold rregions_wf. rewrite ER, EA, EG.
  split; [|split; [exact WR|split; [exact DJ|split; [exact WA|exact WG]]]].
  unfold s_statics in EST. destruct RS as (R1 & R2 & R3). unfold rstatics.
  inversion EST. rewrite R1, R2, R3 in *. auto.
Qed.

(* [comment removed for export] *)
Definition rmrep_W (st : mstate) : list (Z * Z) :=
  (RCTX, RCTX + 928)
  :: map (fun kr : N * region => (r_base (snd kr), r_base (snd kr) + round_up_pg (r_len (snd kr)))) (map_to_list (s_regions st)).

(* [comment removed for export] *)
#[using="Type"] Lemma rmrep_shadow_read : forall st m rid r o v,
  rmrep st m -> (s_regions st) !! rid = Some r -> r_kind r = RKGroup ->
  0 <= o < round_up_pg (r_len r) ->
  cell_read (get_shadow st rid) o = Known v ->
  ov_read_bytes usegs m (wa (r_base r + o)) 1 = Some [b8 v] /\ 0 <= v < 256.
Proof.
  intros st m rid r o v (WF & _ & _ & _ & _ & SH) Hr Hk Ho Hc.
  destruct (SH rid r Hr Hk) as [HW HB]. destruct (HB o v Ho Hc) as [Hm Hv]. split; [|exact Hv].
  rewrite <- (Z.add_0_r (r_base r + o)). apply (bytes_at_read usegs m _ [b8 v] 0 1 Hm); [lia|cbn; lia].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rmrep_shadow_read2 : forall st m rid r o v0 v1,
  rmrep st m -> (s_regions st) !! rid = Some r -> r_kind r = RKGroup ->
  0 <= o -> o + 2 <= round_up_pg (r_len r) ->
  cell_read (get_shadow st rid) o = Known v0 ->
  cell_read (get_shadow st rid) (o + 1) = Known v1 ->
  ov_read_bytes usegs m (wa (r_base r + o)) 2 = Some [b8 v0; b8 v1] /\ 0 <= v0 < 256 /\ 0 <= v1 < 256.
Proof.
  intros st m rid r o v0 v1 MR Hr Hk Ho Ho2 H0 H1.
  pose proof MR as (WF & _ & _ & _ & _ & SH).
  destruct (SH rid r Hr Hk) as [HW HB].
  Local Ltac2 Set LiaHints.tbl := fun () => "0050>11311205413.2115042936624.2429255027187.2346177257579.1948586697148.2400000800900:00B00CS2Ho3Ho2SSS2Ho3Ho2S".
destruct (HB o v0 ltac:(lia) H0) as [B0 V0]. destruct (HB (o + 1) v1 ltac:(lia) H1) as [B1 V1].
  split; [|split; assumption].
  assert (B : bytes_at usegs m (r_base r + o) ([b8 v0] ++ [b8 v1])).
  { apply bytes_at_app. split; [exact B0|]. cbn [length Z.of_nat Pos.of_succ_nat].
    replace (r_base r + o + 1) with (r_base r + (o + 1)) by lia. exact B1. }
  rewrite <- (Z.add_0_r (r_base r + o)). apply (bytes_at_read usegs m _ _ 0 2 B); [lia|cbn; lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".


(* [comment removed for export] *)
Definition rsize_classes_bytes : list byte :=
  Eval vm_compute in (match image_bytes usegs RSIZE_CLASSES 96 with Some bs => bs | None => [] end).

#[using="Type"] Lemma rsize_classes_ro : forall m, mem_inv usegs m -> ro_cells usegs m RSIZE_CLASSES [CB 96 rsize_classes_bytes].
Proof. intros m MI. apply (ro_cells_image usegs m); [exact MI | vm_compute; reflexivity | unfold RSIZE_CLASSES; lia | unfold RSIZE_CLASSES; cbn; lia]. Qed.

#[using="Type"] Lemma rsize_classes_read : forall m sc, mem_inv usegs m -> 0 <= sc < 48 ->
  ov_read_bytes usegs m (wa (RSIZE_CLASSES + 2 * sc)) 2 = Some (le2 (wz (size_class sc))).
Proof.
  intros m sc MI Hsc.
  destruct (rsize_classes_ro m MI) as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
  Local Ltac2 Set LiaHints.tbl := fun () => "0060=3992865885.7 43018176766.647072781292.747639713657.660494359894.663308844160.600000800=00A00F00K00PS3Hsc2HnS3HscS2HnS3HscS3HscS3Hsc".
rewrite (bytes_at_read usegs m RSIZE_CLASSES rsize_classes_bytes (2 * sc) 2 B) by (cbn; lia).
  assert (Hn : exists n, sc = Z.of_nat n /\ (n < 48)%nat) by (exists (Z.to_nat sc); split; [lia|lia]).
  destruct Hn as (n & -> & Hn).
  replace (Z.to_nat (2 * Z.of_nat n)) with (2 * n)%nat by lia.
  Ltac solve_bytes := vm_compute; f_equal; repeat first [ reflexivity | apply f_equal2; [apply bv_eq; reflexivity|] ].
  do 48 (destruct n as [|n]; [solve_bytes |]). lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".


#[using="Type"] Lemma rmrep_meta_chunk : forall st m g,
  rmrep st m -> meta_slot st g ->
  rw_cells usegs m (conc st g) (meta_cells st (get_meta_rec st g)).
Proof.
  intros st m g MR (a & ar & k & Ha & Hk & ->).
  pose proof MR as (WF & _ & _ & AR & _ & _).
  destruct (AR a ar Ha) as (_ & SL & _).
  destruct WF as (_ & _ & _ & WA & _). destruct (WA a ar Ha) as (r & Hr & _).
  rewrite conc_aadd by (rewrite Hr; eauto).
  Local Ltac2 Set LiaHints.tbl := fun () => "0010=1223905946.14000001S".
replace (conc st a + (AREA_HDR + META_SIZE * k)) with (conc st a + AREA_HDR + META_SIZE * k) by lia. apply SL. exact Hk.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma rmrep_group_read : forall st m b gh,
  rmrep st m -> (s_groups st) !! b = Some gh ->
  ov_read_bytes usegs m (wa (conc st b)) 8 = Some (le8 (pw st (g_meta gh)))
  /\ exists w8 : byte, ov_read_bytes usegs m (wa (conc st b + 8)) 1 = Some [w8] /\ Z.land (bv_unsigned w8) 31 = g_active_idx gh.
Proof.
  intros st m b gh MR Hb. pose proof MR as (_ & _ & _ & _ & GR & _).
  destruct (GR b gh Hb) as (w8 & RW & Hw8). split.
  - rewrite <- (Z.add_0_r (conc st b)). apply (rw_cells_read_at usegs m _ _ 0 (C8 (pw st (g_meta gh))) 8 _ RW); reflexivity.
  - exists w8. split; [|exact Hw8].
    apply (rw_cells_read_at usegs m _ _ 8 (C1 w8) 1 _ RW); reflexivity.
Qed.

#[using="Type"] Lemma rmrep_area_check_read : forall st m a ar,
  rmrep st m -> (s_areas st) !! a = Some ar ->
  ov_read_bytes usegs m (wa (conc st a)) 8 = Some (le8 (wz SECRET)).
Proof.
  intros st m a ar MR Ha. pose proof MR as (_ & _ & _ & AR & _ & _).
  destruct (AR a ar Ha) as (HD & _ & _).
  rewrite <- (Z.add_0_r (conc st a)). apply (rw_cells_read_at usegs m _ _ 0 (C8 (wz SECRET)) 8 _ HD); reflexivity.
Qed.

#[using="Type"] Lemma rmrep_ctx_secret_read : forall st m,
  rmrep st m -> ov_read_bytes usegs m (wa RCTX) 8 = Some (le8 (rsecw st)).
Proof.
  intros st m (_ & (HD & _) & _).
  rewrite <- (Z.add_0_r RCTX). apply (rw_cells_read_at usegs m _ _ 0 (C8 (rsecw st)) 8 _ HD); reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rsecw_init : forall st, c_init_done (ctx st) = 1 -> rsecw st = wz SECRET.
Proof. intros st H. unfold rsecw. rewrite H, Z.mul_1_r. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma rreserved_disjoint : forall b n, ranges_free ref_reserved b n = true ->
  (b + n <= 0x10000 \/ 0x12000 <= b) /\ ((b + n <= 0x12000 \/ 0x1c000 <= b)
  /\ (b + n <= 0x1c000 \/ 0x1d000 <= b) /\ (b + n <= 0x1d000 \/ 0x4f000 <= b)).
Proof.
  intros b n H. unfold ranges_free, ref_reserved in H. cbn [forallb fst snd] in H.
  unfold iv_disjoint in H. rewrite !Bool.andb_true_iff, !Bool.orb_true_iff, !Z.leb_le in H. Local Ltac2 Set LiaHints.tbl := fun () => "0010=60005525103.4000003S1H".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma rreserved_disjoint1 : forall b n, ranges_free ref_reserved b n = true -> 0 < n ->
  b + n <= 0x10000 \/ 0x4f000 <= b.
Proof. intros b n H Hn. pose proof (rreserved_disjoint b n H). Local Ltac2 Set LiaHints.tbl := fun () => "0010=39421859112.6000007S2Hn2H0".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma rwr_in_image : forall st rid a len,
  rregions_wf st -> wr_in st rid a len ->
  ((a + len <= 0x1c000 \/ 0x1d000 <= a) /\ (a + len <= 0x1d000 \/ 0x4f000 <= a)) /\ 0 <= a /\ a + len <= 2^64.
Proof.
  intros st rid a len (_ & WR & _) (r & Hr & H1 & H2 & H3).
  destruct (WR rid r Hr) as (B0 & _ & L0 & BC & RF). atop_facts.
  destruct (rreserved_disjoint _ _ RF) as [_ D2]. pose proof (round_up_pg_ge (r_len r)). pose proof (lr_lo_ge r). Local Ltac2 Set LiaHints.tbl := fun () => "0010>42884193296.1900000LS2H12H22H32B02BC5ATOPR2D22H0".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma rwr_in_other : forall st rid a len rid' r',
  rregions_wf st -> wr_in st rid a len -> (s_regions st) !! rid' = Some r' -> rid' <> rid ->
  a + len <= lr_lo r' \/ r_base r' + round_up_pg (r_len r') <= a.
Proof.
  intros st rid a len rid' r' (_ & _ & DJ & _) (r & Hr & H1 & H2 & H3) Hr' Hne.
  destruct (DJ rid r rid' r' Hr Hr' ltac:(congruence)); lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rarea_lr_lo : forall st a ar r, rregions_wf st -> (s_areas st) !! a = Some ar -> (s_regions st) !! (fst a) = Some r ->
  lr_lo r <= r_base r + snd a.
Proof.
  intros st a ar r (_ & _ & _ & WA & _) Ha Hr. destruct (WA a ar Ha) as (r0 & Hr0 & _ & _ & _ & _ & LO).
  rewrite Hr in Hr0. inversion Hr0; subst. exact LO.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rregions_disjoint_full : forall st rid1 r1 rid2 r2,
  rregions_wf st -> (s_regions st) !! rid1 = Some r1 -> (s_regions st) !! rid2 = Some r2 -> rid1 <> rid2 ->
  r_kind r1 <> RKBrk -> r_kind r2 <> RKBrk ->
  r_base r1 + round_up_pg (r_len r1) <= r_base r2 \/ r_base r2 + round_up_pg (r_len r2) <= r_base r1.
Proof.
  intros st rid1 r1 rid2 r2 (_ & _ & DJ & _) H1 H2 NE K1 K2.
  pose proof (DJ rid1 r1 rid2 r2 H1 H2 NE) as X. rewrite (lr_lo_nbrk r1 K1), (lr_lo_nbrk r2 K2) in X. exact X.
Qed.

#[using="Type"] Lemma rregions_disjoint_grp : forall st rid1 r1 rid2 r2,
  rregions_wf st -> (s_regions st) !! rid1 = Some r1 -> (s_regions st) !! rid2 = Some r2 -> rid1 <> rid2 ->
  r_kind r1 = RKGroup ->
  r_base r1 + round_up_pg (r_len r1) <= lr_lo r2 \/ r_base r2 + round_up_pg (r_len r2) <= r_base r1.
Proof.
  intros st rid1 r1 rid2 r2 (_ & _ & DJ & _) H1 H2 NE K1.
  pose proof (DJ rid1 r1 rid2 r2 H1 H2 NE) as X. rewrite (lr_lo_group r1 K1) in X. exact X.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rmrep_ctx_ext : forall st st' m,
  ctx st' = ctx st -> (forall p, conc st' p = conc st p) -> rmrep_ctx st m -> rmrep_ctx st' m.
Proof.
  intros st st' m Hc Hconc H.
  assert (Hpw : forall p, pw st' p = pw st p). { intros [p|]; unfold pw, oconc; [rewrite Hconc|]; reflexivity. }
  assert (E1 : rctx_head_cells st' = rctx_head_cells st) by (unfold rctx_head_cells, rsecw; rewrite Hc, !Hpw; reflexivity).
  assert (E2 : actives st' = actives st). { unfold actives. apply map_ext. intros. unfold active. rewrite Hc. apply Hpw. }
  assert (E3 : usages st' = usages st). { unfold usages. apply map_ext. intros. unfold usage. rewrite Hc. reflexivity. }
  assert (E4 : unmap_seqs st' = unmap_seqs st). { unfold unmap_seqs. apply map_ext. intros. unfold unmap_seq. rewrite Hc. reflexivity. }
  assert (E5 : bouncess st' = bouncess st). { unfold bouncess. apply map_ext. intros. unfold bounces. rewrite Hc. reflexivity. }
  assert (E6 : ctx_tail_cells st' = ctx_tail_cells st). { unfold ctx_tail_cells, brk_word. rewrite Hc. destruct (c_brk (ctx st)); rewrite ?Hconc; reflexivity. }
  unfold rmrep_ctx in *. rewrite E1, E2, E3, E4, E5, E6. exact H.
Qed.

#[using="Type"] Lemma rarea_rep_ext : forall st st' m a ar,
  (forall p, conc st' p = conc st p) ->
  (forall k, 0 <= k < NSLOTS -> get_meta_rec st' (aadd a (AREA_HDR + META_SIZE * k)) = get_meta_rec st (aadd a (AREA_HDR + META_SIZE * k))) ->
  rarea_rep st m a ar -> rarea_rep st' m a ar.
Proof.
  intros st st' m a ar Hconc Hm (H1 & H2 & H3).
  assert (Hpw : forall p, pw st' p = pw st p). { intros [p|]; unfold pw, oconc; [rewrite Hconc|]; reflexivity. }
  assert (Hmc : forall mr, meta_cells st' mr = meta_cells st mr) by (intros; unfold meta_cells; rewrite !Hpw; reflexivity).
  unfold rarea_rep. rewrite !Hconc, Hpw. split; [exact H1|]. split; [|exact H3].
  intros k Hk. rewrite Hmc, Hm by exact Hk. apply H2. exact Hk.
Qed.

#[using="Type"] Lemma rgroup_rep_ext : forall st st' m b gh,
  (forall p, conc st' p = conc st p) -> rgroup_rep st m b gh -> rgroup_rep st' m b gh.
Proof.
  intros st st' m b gh Hconc (w8 & H1 & H2).
  assert (Hpw : forall p, pw st' p = pw st p). { intros [p|]; unfold pw, oconc; [rewrite Hconc|]; reflexivity. }
  exists w8. rewrite Hconc, Hpw. auto.
Qed.

#[using="Type"] Lemma rshadow_rep_ext : forall st st' m rid r,
  get_shadow st' rid = get_shadow st rid -> rshadow_rep st m rid r -> rshadow_rep st' m rid r.
Proof. intros st st' m rid r Hs [H1 H2]. split; [exact H1|]. intros o v Ho Hc. rewrite Hs in Hc. eauto. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rmrep_ctx_frame : forall st m a bs rid,
  rregions_wf st -> wr_in st rid a (Z.of_nat (length bs)) -> rmrep_ctx st m ->
  rmrep_ctx st (write_to_mem m (wa a) bs).
Proof.
  intros st m a bs rid WF WI (H1 & H2 & H3 & H4 & H5 & H6).
  destruct (rwr_in_image st rid a _ WF WI) as (D & A0 & A1).
  assert (L1 : length (actives st) = 48%nat) by (unfold actives; rewrite map_length, seq_length; reflexivity).
  assert (L2 : length (usages st) = 48%nat) by (unfold usages; rewrite map_length, seq_length; reflexivity).
  assert (L3 : length (unmap_seqs st) = 32%nat) by (unfold unmap_seqs; rewrite map_length, seq_length; reflexivity).
  assert (L4 : length (bouncess st) = 32%nat) by (unfold bouncess; rewrite map_length, seq_length; reflexivity).
  unfold rmrep_ctx. unfold RCTX in *. split; [|split; [|split; [|split; [|split]]]].
  - Local Ltac2 Set LiaHints.tbl := fun () => "0080>12455165270.2118484052587.212168967510.21 26983563229.2139880334863.2148784213334.2152717229398.219283808086.21 00000?00O00^00n01=01L01[01jS1D2L12L22L32L4S2A12L12L22L32L4S1D2L12L22L32L4S2A02L12L22L32L4S1D2L12L22L32L4S1D2L12L22L32L4S1D2L12L22L32L4S1D2L12L22L32L4".
apply rw_cells_frame; [exact H1|lia|lia|cbn; lia].
  - apply u64arr_frame; [exact H2|lia|lia|rewrite L1; cbn; lia].
  - apply u64arr_frame; [exact H3|lia|lia|rewrite L2; cbn; lia].
  - apply u8arr_frame; [exact H4|lia|lia|rewrite L3; cbn; lia].
  - apply u8arr_frame; [exact H5|lia|lia|rewrite L4; cbn; lia].
  - apply rw_cells_frame; [exact H6|lia|lia|cbn; lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma rmrep_globals_frame : forall st m a bs rid,
  rregions_wf st -> wr_in st rid a (Z.of_nat (length bs)) -> rmrep_globals m ->
  rmrep_globals (write_to_mem m (wa a) bs).
Proof.
  intros st m a bs rid WF WI (H1 & H2 & H3 & H4 & H5).
  destruct (rwr_in_image st rid a _ WF WI) as (D & A0 & A1).
  unfold rmrep_globals. unfold RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RGOT_SSP, RSSP_GUARD in *. split; [|split; [|split; [|split]]].
  - Local Ltac2 Set LiaHints.tbl := fun () => "0070>18484232684.1626983742554.1636212767368.1643633903752.1653872148648.1657510296200.1667622248584.1600000400800;00>00A00D00GS2A1S2A0S1DS1DS1DS1DS1D".
apply rw_cells_frame; [exact H1|lia|lia|cbn; lia].
  - apply rw_cells_frame; [exact H2|lia|lia|cbn; lia].
  - apply rw_cells_frame; [exact H3|lia|lia|cbn; lia].
  - apply rw_cells_frame; [exact H4|lia|lia|cbn; lia].
  - apply rw_cells_frame; [exact H5|lia|lia|cbn; lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma rarea_rep_frame : forall st m a bs ar0 ar,
  rregions_wf st -> (s_areas st) !! ar0 = Some ar ->
  0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
  (conc st ar0 + 4096 <= a \/ a + Z.of_nat (length bs) <= conc st ar0) ->
  rarea_rep st m ar0 ar -> rarea_rep st (write_to_mem m (wa a) bs) ar0 ar.
Proof.
  intros st m a bs ar0 ar WF Har A0 A1 D (H1 & H2 & H3).
  unfold rarea_rep. split; [|split].
  - Local Ltac2 Set LiaHints.tbl := fun () => "0070>18484118250.1518484129458.1726983617284.1726983628636.1539918677891.1548775373849.1556082225977.1700000400800<00@00C00F00LS2A1S2A1S2A0S2A0S1DS1DS1D2Hk".
apply rw_cells_frame; [exact H1|lia|lia|cbn; lia].
  - intros k Hk. apply rw_cells_frame; [apply H2; exact Hk|lia|lia|]. unfold AREA_HDR, META_SIZE, NSLOTS in *. cbn. lia.
  - apply rw_cells_frame; [exact H3|lia|lia|cbn; lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma rgroup_rep_frame : forall st m a bs b gh,
  0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
  (conc st b + 9 <= a \/ a + Z.of_nat (length bs) <= conc st b) ->
  rgroup_rep st m b gh -> rgroup_rep st (write_to_mem m (wa a) bs) b gh.
Proof.
  intros st m a bs b gh A0 A1 D (w8 & H1 & H2). exists w8. split; [|exact H2].
  Local Ltac2 Set LiaHints.tbl := fun () => "0030>18484117869.1326983627995.1345529351866.1300000400800;S2A1S2A0S1D".
apply rw_cells_frame; [exact H1|lia|lia|cbn; lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma rshadow_rep_frame : forall st m a bs rid r,
  0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
  (r_base r + round_up_pg (r_len r) <= a \/ a + Z.of_nat (length bs) <= r_base r) ->
  rshadow_rep st m rid r -> rshadow_rep st (write_to_mem m (wa a) bs) rid r.
Proof.
  intros st m a bs rid r A0 A1 D [HW HB]. split; [apply wr_at_write; exact HW|].
  intros o v Ho Hc. destruct (HB o v Ho Hc) as [Hb Hv]. split; [|exact Hv].
  Local Ltac2 Set LiaHints.tbl := fun () => "0030>18484126505.1826983620255.1866131088339.1800000400800>S2A1S2A0S1D2Ho".
apply bytes_at_write_other; [exact Hb|lia|lia|cbn; lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma rarea_conc : forall st a ar, rregions_wf st -> (s_areas st) !! a = Some ar ->
  exists r, (s_regions st) !! (fst a) = Some r /\ conc st a = r_base r + snd a
            /\ 0 <= snd a /\ snd a + 4096 <= round_up_pg (r_len r) /\ snd a mod 4096 = 0 /\ r_kind r <> RKGroup
            /\ 0 < r_base r /\ r_base r mod 4096 = 0 /\ r_base r + round_up_pg (r_len r) <= ATOP.
Proof.
  intros st a ar (_ & WR & _ & WA & _) Ha. destruct (WA a ar Ha) as (r & Hr & A0 & A1 & AL & NK & _).
  destruct (WR _ r Hr) as (B0 & BAL & _ & BC & _).
  exists r. rewrite (conc_region' st a r Hr). repeat split; auto.
Qed.

#[using="Type"] Lemma rgroup_conc : forall st b gh, rregions_wf st -> (s_groups st) !! b = Some gh ->
  exists r, (s_regions st) !! (fst b) = Some r /\ conc st b = r_base r + snd b
            /\ r_kind r = RKGroup /\ 0 <= snd b /\ snd b + 16 <= round_up_pg (r_len r) /\ snd b mod 16 = 0
            /\ 0 < r_base r /\ r_base r + round_up_pg (r_len r) <= ATOP.
Proof.
  intros st b gh (_ & WR & _ & _ & WG) Hb. destruct (WG b gh Hb) as (r & Hr & K & B0 & B1 & AL).
  destruct (WR _ r Hr) as (R0 & _ & _ & RC & _).
  exists r. rewrite (conc_region' st b r Hr). repeat split; auto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rmrep_wr8 : forall st m p v r,
  rmrep st m -> ticks_ok st ->
  (s_regions st) !! (fst p) = Some r -> r_kind r = RKGroup -> 0 <= snd p < round_up_pg (r_len r) ->
  (forall b gh, (s_groups st) !! b = Some gh -> fst b = fst p -> ~ (snd b <= snd p < snd b + 9)) ->
  0 <= v < 256 ->
  rmrep (wr8 p v st) (write_to_mem m (wa (r_base r + snd p)) [b8 v]).
Proof.
  intros st m p v r MR TK Hr Hk Ho Hgrp Hv.
  pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof (lr_lo_group r Hk) as LRr.
  assert (WI : wr_in st (fst p) (r_base r + snd p) (Z.of_nat (length [b8 v]))).
  { exists r. cbn. Local Ltac2 Set LiaHints.tbl := fun () => "00C0>15987572004.2020789248337.2026828900717.3844958483538.3147156037427.3249122391173.3649702777139.3649702777523.3149702839091.3149702839160.3549702839161.3667794750013.3767794800050.3568056908633.208317841514.31 8317842410.36 8317903264.36 8317903265.35 8317903338.31 00000400<00J00Q00[00e00i00m01101501901K01X01Y01`01g01n02502<S2HoS2Ho3LRrS2A13LRa1H3Sa1S2Hv2A1S2A13LR'1HS1D2A13NEoS2A1S2A1S2A1S2A1S2A1S2A13Sb03LRb1H3Sb1S4Hgrp1D2A11ESS2A02A1S2A02A1S2A02A1S2A02A1S2A02A1".
repeat split; auto; lia. }
  destruct (rwr_in_image st _ _ _ WF WI) as (D & A0 & A1). cbn [length Z.of_nat Pos.of_succ_nat Pos.to_nat] in D, A1.
  assert (Hconc : forall q, conc (wr8 p v st) q = conc st q) by (intros; reflexivity).
  split; [|split; [|split; [|split; [|split]]]].
  - (* [comment removed for export] *) exact WF.
  - eapply rmrep_ctx_ext; [reflexivity|exact Hconc|]. eapply rmrep_ctx_frame; eauto.
  - eapply rmrep_globals_frame; eauto.
  - intros a ar Ha. cbn in Ha. eapply rarea_rep_ext; [exact Hconc|intros; reflexivity|].
    destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & _).
    pose proof (rarea_lr_lo st a ar ra WF Ha Hra) as LRa.
    apply rarea_rep_frame; [exact WF|exact Ha|lia|cbn; lia| |exact (AR a ar Ha)]. rewrite Ca. cbn.
    destruct (N.eq_dec (fst a) (fst p)) as [E|NE].
    + rewrite E in Hra. rewrite Hr in Hra. inversion Hra; subst ra. congruence.
    + destruct (rwr_in_other st _ _ _ _ ra WF WI Hra NE); cbn in *; lia.
  - intros b gh Hb. cbn in Hb. eapply rgroup_rep_ext; [exact Hconc|].
    destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _). pose proof (lr_lo_group rb Kb) as LRb.
    apply rgroup_rep_frame; [lia|cbn; lia| |exact (GR b gh Hb)]. rewrite Cb. cbn.
    destruct (N.eq_dec (fst b) (fst p)) as [E|NE].
    + rewrite E in Hrb. rewrite Hr in Hrb. inversion Hrb; subst rb. specialize (Hgrp b gh Hb E). lia.
    + destruct (rwr_in_other st _ _ _ _ rb WF WI Hrb NE); cbn in *; lia.
  - intros rid r' Hr' Hk'. cbn in Hr'.
    destruct (N.eq_dec rid (fst p)) as [E|NE].
    + subst rid. rewrite Hr in Hr'. inversion Hr'; subst r'.
      destruct (SH (fst p) r Hr Hk) as [HW HB]. split; [apply wr_at_write; exact HW|].
      intros o v' Ho' Hc.
      destruct (Z.eq_dec o (snd p)) as [->|NEo].
      * rewrite cell_read_wr8_same in Hc by assumption. inversion Hc; subst v'. split; [|lia].
        apply bytes_at_write_same; cbn; lia.
      * rewrite cell_read_wr8_other in Hc by exact NEo. destruct (HB o v' Ho' Hc) as [Hb Hv']. split; [|exact Hv'].
        apply bytes_at_write_other; [exact Hb|lia|cbn; lia|cbn; lia].
    + eapply rshadow_rep_ext; [apply get_shadow_wr8_other; exact NE|].
      pose proof (lr_lo_group r' Hk') as LR'.
      apply rshadow_rep_frame; [lia|cbn; lia| |exact (SH rid r' Hr' Hk')].
      destruct (rwr_in_other st _ _ _ _ r' WF WI Hr' NE); cbn in *; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".


#[using="Type"] Lemma rmrep_wr16 : forall st m p v r,
  rmrep st m -> ticks_ok st ->
  (s_regions st) !! (fst p) = Some r -> r_kind r = RKGroup -> 0 <= snd p -> snd p + 2 <= round_up_pg (r_len r) ->
  (forall b gh, (s_groups st) !! b = Some gh -> fst b = fst p -> snd p + 2 <= snd b \/ snd b + 9 <= snd p) ->
  0 <= v < 65536 ->
  rmrep (wr16 p v st) (write_to_mem m (wa (r_base r + snd p)) (le2 (wz v))).
Proof.
  intros st m p v r MR TK Hr Hk Ho Ho2 Hg Hv.
  Local Ltac2 Set LiaHints.tbl := fun () => "00:0>11388831327.1613073110649.1616864712589.1418433020136.1418435116950.1526666315875.1534308240384.2054234166816.1557623808912.1463368324200.1400000800@00D00E00F00J00P00T00U00VS2Ho3Ho2S2Ho3Ho2S2HvSSS2HvS2Hg1ES2HvSS".
rewrite le2_split by lia.
  change (write_to_mem m (wa (r_base r + snd p)) [b8 (v mod 256); b8 (v / 256)])
    with (write_to_mem (write_to_mem m (wa (r_base r + snd p)) [b8 (v mod 256)]) (wa (r_base r + snd p) + 1) [b8 (v / 256)]).
  rewrite wa_succ. unfold wr16. rewrite (wr8_mod st p v).
  replace (r_base r + snd p + 1) with (r_base r + snd (aadd p 1)) by (unfold aadd; cbn; lia).
  replace (Z.shiftr v 8) with (v / 256) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  pose proof (Z.mod_pos_bound v 256 ltac:(lia)).
  assert (Hd : 0 <= v / 256 < 256) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  apply (rmrep_wr8 (wr8 p (v mod 256) st) _ (aadd p 1) (v / 256) r).
  - apply rmrep_wr8; auto; [lia|]. intros b gh Hb E. specialize (Hg b gh Hb E). lia.
  - apply ticks_ok_wr8. exact TK.
  - cbn. exact Hr.
  - exact Hk.
  - cbn. lia.
  - intros b gh Hb E. cbn in Hb, E |- *. specialize (Hg b gh Hb E). lia.
  - exact Hd.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".



(* [comment removed for export] *)
#[using="Type"] Lemma rmrep_meta_store4 : forall st m g (f : meta -> meta) (off : nat) v,
  rmrep st m -> meta_slot st g -> 0 <= v < 2^32 ->
  (forall mr, cell_at (meta_cells st mr) off = Some (C4 (wz (match off with 24%nat => m_avail mr | _ => m_freed mr end)))) ->
  (forall mr, cell_upd (meta_cells st mr) off (C4 (wz v)) = meta_cells st (f mr)) ->
  (off = 24%nat \/ off = 28%nat) ->
  rmrep (upd_meta g f st) (write_to_mem m (wa (conc st g + Z.of_nat off)) (le4 (wz v))).
Proof.
  intros st m g f off v MR (a & ar & k & Ha & Hk & Eg) Hv Hat Hupd Hoff.
  pose proof MR as (WF & CX & GL & AR & GR & SH).
  destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC). atop_facts.
  pose proof (rarea_lr_lo st a ar ra WF Ha Hra) as LRa.
  assert (HG : conc st g = conc st a + (AREA_HDR + META_SIZE * k)) by (rewrite Eg, conc_aadd by (rewrite Hra; eauto); reflexivity).
  unfold AREA_HDR, META_SIZE, NSLOTS in *.
  assert (WI : wr_in st (fst a) (conc st g + Z.of_nat off) (Z.of_nat (length (le4 (wz v))))).
  { exists ra. rewrite length_le4. cbn [Z.of_nat Pos.of_succ_nat Pos.to_nat]. split; [exact Hra|]. rewrite HG, Ca. Local Ltac2 Set LiaHints.tbl := fun () => "00F0>17223904932.5626828900717.5526831391212.5030899349610.4931509349922.5731509386111.5634754714246.5441190602145.4942959090410.5442959090791.5342960696718.5642960731905.4942960731978.4444937802903.5446793993823.3347156037427.4649702839091.4449702839160.4949702873591.5649704740894.5349704742547.5467794750013.5100000500B00a00e01D01W01[01_02102D02W02i03;03<03H03O04=04k05[06K07A07PS3Hk'S4LRa'1H4Sa1'S2Hk3Sa03SaL3RB04Sa0'4SaL'1E2PGS2HkS2Hk4Hoff3Sa03RB04Sa0'1E2PG3Hk0S4Hoff3RB04Sa0'3NEkS2HkS2HkS2Hk2Ca3Sa03RB02HGS2Hk2Ca3RB02HG4Sa0'S2Hk2Ca3RB02HG4Sa0'S2Hk2Ca3Sa03RB02HGS2Hk2Ca3Sa03RB02HGSS2Hk3Sa13LRaS3LR'1HS2Hk4Hoff2Ca3Sa03Sa13SaL3RB04RBAL3RBC5ATOPR2HGS2Hk4Hoff2Ca3Sa03Sa13SaL3RB04RBAL3RBC5ATOPR2HGS2Hk4Hoff2Ca3Sa13RB04RBAL3RBC5ATOPR2HG4SaL'4Sa0'S2Hk4Hoff2Ca3Sa13RB04RBAL3RBC5ATOPR2HG4SaL'4Sa0'S2Hk4Hoff2Ca3Sa03Sa13SaL3RB04RBAL3RBC5ATOPR2HG4Sa0'2PGS3Sb03LRb1H3Sb1".
destruct Hoff; subst; cbn; lia. }
  assert (Hconc : forall q, conc (upd_meta g f st) q = conc st q) by (intros; reflexivity).
  split; [|split; [|split; [|split; [|split]]]].
  - exact WF.
  - eapply rmrep_ctx_ext; [reflexivity|exact Hconc|]. eapply rmrep_ctx_frame; eauto.
  - eapply rmrep_globals_frame; eauto.
  - intros a' ar' Ha'. cbn in Ha'.
    assert (Hpw : forall q, pw (upd_meta g f st) q = pw st q) by (intros [q|]; reflexivity).
    assert (Hmc : forall mr, meta_cells (upd_meta g f st) mr = meta_cells st mr) by (intros; unfold meta_cells; rewrite !Hpw; reflexivity).
    destruct (rarea_conc st a' ar' WF Ha') as (ra' & Hra' & Ca' & Sa0' & Sa1' & SaL' & NK' & _).
    pose proof (rarea_lr_lo st a' ar' ra' WF Ha' Hra') as LRa'.
    destruct (decide (a' = a)) as [->|NEa].
    + (* [comment removed for export] *)
      rewrite Ha in Ha'. inversion Ha'; subst ar'.
      destruct (AR a ar Ha) as (HD & SL & PD). unfold rarea_rep. rewrite !Hconc, Hpw. rewrite length_le4 in *.
      split; [|split].
      * apply rw_cells_frame; [exact HD|lia|rewrite length_le4; cbn in *; lia|]. rewrite length_le4, HG. cbn. destruct Hoff; subst; cbn; lia.
      * intros k' Hk'. rewrite Hmc, get_meta_rec_upd.
        destruct (Z.eq_dec k' k) as [->|NEk].
        -- rewrite <- Eg, aptr_eqb_refl.
           replace (conc st g + Z.of_nat off) with (conc st a + 24 + 40 * k + Z.of_nat off) by (rewrite HG; lia).
           rewrite <- Hupd. unfold le4. change (Z_to_le_bytes 4 (bv_unsigned (wz v))) with (cbytes (C4 (wz v))).
           eapply rw_cells_write; [ | apply Hat | reflexivity | exact I].
           rewrite Eg. replace (24 + 40 * k) with (AREA_HDR + META_SIZE * k) by reflexivity. apply SL. unfold NSLOTS. lia.
        -- replace (aptr_eqb (aadd a (24 + 40 * k')) g) with false.
           2:{ symmetry. rewrite Eg. unfold aptr_eqb, aadd. cbn. rewrite N.eqb_refl. cbn. apply Z.eqb_neq. lia. }
           apply rw_cells_frame; [apply SL; lia|lia|rewrite length_le4; cbn in *; lia|].
           rewrite length_le4, HG. cbn [cells_size meta_cells csize Nat.add length]. unfold AREA_HDR, META_SIZE. destruct Hoff; subst; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; nia.
      * apply rw_cells_frame; [exact PD|lia|rewrite length_le4; cbn in *; lia|]. rewrite length_le4, HG. cbn. destruct Hoff; subst; cbn; lia.
    + (* [comment removed for export] *)
      assert (PG : fst a' <> fst a \/ (fst a' = fst a /\ (snd a' + 4096 <= snd a \/ snd a + 4096 <= snd a'))).
      { destruct (N.eq_dec (fst a') (fst a)) as [E|NE]; [right|left; exact NE]. split; [exact E|].
        assert (snd a' <> snd a) by (intros E2; apply NEa; destruct a, a'; cbn in *; congruence).
        Z.div_mod_to_equations. nia. }
      eapply rarea_rep_ext; [exact Hconc| |].
      { intros k0 Hk0. rewrite get_meta_rec_upd.
        replace (aptr_eqb (aadd a' (AREA_HDR + META_SIZE * k0)) g) with false; [reflexivity|].
        symmetry. rewrite Eg. unfold aptr_eqb, aadd, AREA_HDR, META_SIZE. cbn [fst snd].
        destruct PG as [NE|[E PG]].
        - rewrite (proj2 (N.eqb_neq _ _) NE). reflexivity.
        - rewrite E, N.eqb_refl. cbn [andb]. apply Z.eqb_neq. unfold NSLOTS in *. lia. }
      apply rarea_rep_frame; [exact WF|exact Ha'|lia|rewrite length_le4; cbn in *; lia| |exact (AR a' ar' Ha')].
      rewrite length_le4, Ca', HG, Ca. cbn [Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat].
      destruct PG as [NE|[E PG]].
      * destruct (rwr_in_other st _ _ _ _ ra' WF WI Hra' NE); rewrite ?HG, ?Ca in *; cbn in *; lia.
      * rewrite E, Hra in Hra'. inversion Hra'; subst ra'. destruct Hoff; subst; cbn; lia.
  - intros b gh Hb. cbn in Hb. eapply rgroup_rep_ext; [exact Hconc|].
    destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _). pose proof (lr_lo_group rb Kb) as LRb.
    apply rgroup_rep_frame; [lia|rewrite length_le4; cbn in *; lia| |exact (GR b gh Hb)]. rewrite Cb, length_le4. cbn.
    assert (NE : fst b <> fst a) by (intros E; rewrite E, Hra in Hrb; inversion Hrb; subst; congruence).
    destruct (rwr_in_other st _ _ _ _ rb WF WI Hrb NE); cbn in *; lia.
  - intros rid r' Hr' Hk'. cbn in Hr'.
    eapply rshadow_rep_ext; [reflexivity|]. pose proof (lr_lo_group r' Hk') as LR'.
    apply rshadow_rep_frame; [lia|rewrite length_le4; cbn in *; lia| |exact (SH rid r' Hr' Hk')]. rewrite length_le4. cbn.
    assert (NE : rid <> fst a) by (intros E; subst; rewrite Hra in Hr'; inversion Hr'; subst; congruence).
    destruct (rwr_in_other st _ _ _ _ r' WF WI Hr' NE); cbn in *; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma rmrep_meta_set_avail : forall st m g v,
  rmrep st m -> meta_slot st g -> 0 <= v < 2^32 ->
  rmrep (upd_meta g (m_set_avail v) st) (write_to_mem m (wa (conc st g + 24)) (le4 (wz v))).
Proof.
  intros. change 24 with (Z.of_nat 24).
  apply (rmrep_meta_store4 st m g (m_set_avail v) 24%nat v); auto; intros; reflexivity.
Qed.

#[using="Type"] Lemma rmrep_meta_set_freed : forall st m g v,
  rmrep st m -> meta_slot st g -> 0 <= v < 2^32 ->
  rmrep (upd_meta g (m_set_freed v) st) (write_to_mem m (wa (conc st g + 28)) (le4 (wz v))).
Proof.
  intros. change 28 with (Z.of_nat 28).
  apply (rmrep_meta_store4 st m g (m_set_freed v) 28%nat v); auto; intros; reflexivity.
Qed.


#[using="Type"] Lemma rmrep_set_active : forall st m sc v,
  rmrep st m -> 0 <= sc < 48 ->
  rmrep (set_active sc v st) (write_to_mem m (wa (RCTX + 80 + 8 * sc)) (le8 (pw st v))).
Proof.
  intros st m sc v MR Hsc. pose proof MR as (WF & (C1 & C2 & C3 & C4 & C5 & C6) & (G1 & G2 & G3 & G4 & G5) & AR & GR & SH).
  assert (Hconc : forall q, conc (set_active sc v st) q = conc st q) by (intros; reflexivity).
  assert (Hpw : forall q, pw (set_active sc v st) q = pw st q) by (intros [q|]; reflexivity).
  assert (L1 : length (actives st) = 48%nat) by (unfold actives; rewrite map_length, seq_length; reflexivity).
  pose proof (length_le8 (pw st v)) as L8.
  unfold RCTX in *.
  split; [|split; [|split; [|split; [|split]]]].
  - exact WF.
  - unfold rmrep_ctx.
    change (rctx_head_cells (set_active sc v st)) with (rctx_head_cells st).
    change (usages (set_active sc v st)) with (usages st).
    change (unmap_seqs (set_active sc v st)) with (unmap_seqs st).
    change (bouncess (set_active sc v st)) with (bouncess st).
    assert (E6 : ctx_tail_cells (set_active sc v st) = ctx_tail_cells st).
    { unfold ctx_tail_cells, brk_word, ctx. cbn [s_ctx set_active upd_ctx c_seq c_brk set_active_map]. destruct (c_brk (s_ctx st)); reflexivity. }
    Local Ltac2 Set LiaHints.tbl := fun () => "00H0>10779144230.2610779145770.3010781443212.3310781443212.3713939765561.301724943832.26 26837435895.3828781129176.2629746634820.303149430232.26 32506864441.2738449350969.3040822163924.3047072254424.2647147797417.3349698726536.3349698726536.3749704931374.3049704932898.2656607855929.3063726890809.3065408297944.2667786475175.377735385752.30 00000;00O00T00Y00m01801M01X01l02702B02V02j03503B03G03L03`03k04?04S04^05305CS3Hsc2L12L8S3Hsc2L12L82L22L32L4S3HscS3HscS3Hsc2L12L82L22L32L4S3Hsc2L12L8S3Hsc2L12L83Sa03Sa11DS3Hsc2L12L8S3Hsc2L12L82L22L32L4S3Hsc2L12L8S3Hsc2L12L8S3Hsc2L12L82L22L32L4S3Hsc2L12L82L22L32L4S3Hsc2L12L8S3Hsc2L12L81DS3HscS3HscS3Hsc2L12L82L22L32L4S3Hsc2L12L8S3Hsc2L12L82L22L32L4S3Hsc2L12L82L22L32L4S3Hsc2L12L8S3Hsc2L12L83Sb03Sb11DS2L12L82L22L32L4".
rewrite E6, actives_set_active by lia. unfold RCTX.
    assert (L2 : length (usages st) = 48%nat) by (unfold usages; rewrite map_length, seq_length; reflexivity).
    assert (L3 : length (unmap_seqs st) = 32%nat) by (unfold unmap_seqs; rewrite map_length, seq_length; reflexivity).
    assert (L4 : length (bouncess st) = 32%nat) by (unfold bouncess; rewrite map_length, seq_length; reflexivity).
    split; [|split; [|split; [|split; [|split]]]].
    + apply rw_cells_frame; [exact C1|lia|rewrite L8; lia|rewrite L8; cbn; lia].
    + replace (320304 + 80 + 8 * sc) with ((320304 + 80) + 8 * sc) by lia. apply u64arr_write; [exact C2| rewrite L1; lia].
    + apply u64arr_frame; [exact C3|lia|rewrite L8; lia|rewrite L8, L2; lia].
    + apply u8arr_frame; [exact C4|lia|rewrite L8; lia|rewrite L8, L3; lia].
    + apply u8arr_frame; [exact C5|lia|rewrite L8; lia|rewrite L8, L4; lia].
    + apply rw_cells_frame; [exact C6|lia|rewrite L8; lia|rewrite L8; cbn; lia].
  - unfold rmrep_globals, RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RGOT_SSP, RSSP_GUARD in *. split; [|split; [|split; [|split]]].
    + apply rw_cells_frame; [exact G1|lia|rewrite L8; lia|rewrite L8; cbn; lia].
    + apply rw_cells_frame; [exact G2|lia|rewrite L8; lia|rewrite L8; cbn; lia].
    + apply rw_cells_frame; [exact G3|lia|rewrite L8; lia|rewrite L8; cbn; lia].
    + apply rw_cells_frame; [exact G4|lia|rewrite L8; lia|rewrite L8; cbn; lia].
    + apply rw_cells_frame; [exact G5|lia|rewrite L8; lia|rewrite L8; cbn; lia].
  - intros a ar Ha. cbn in Ha. eapply rarea_rep_ext; [exact Hconc|intros; reflexivity|].
    destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & _).
    destruct WF as (_ & WR & _). destruct (WR _ ra Hra) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [_ D].
    apply rarea_rep_frame; [exact (proj1 MR)|exact Ha|lia|rewrite L8; lia| |exact (AR a ar Ha)].
    rewrite L8, Ca. pose proof (round_up_pg_ge (r_len ra)). cbn. lia.
  - intros b gh Hb. cbn in Hb. eapply rgroup_rep_ext; [exact Hconc|].
    destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & _ & Sb0 & Sb1 & _).
    destruct WF as (_ & WR & _). destruct (WR _ rb Hrb) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [_ D].
    apply rgroup_rep_frame; [lia|rewrite L8; lia| |exact (GR b gh Hb)]. rewrite L8, Cb. cbn. lia.
  - intros rid r' Hr' Hk'. cbn in Hr'. eapply rshadow_rep_ext; [reflexivity|].
    destruct WF as (_ & WR & _). destruct (WR _ r' Hr') as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [_ D].
    apply rshadow_rep_frame; [lia|rewrite L8; lia| |exact (SH rid r' Hr' Hk')]. rewrite L8. cbn. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".


#[using="Type"] Lemma rshadow_rep_le : forall st st' m rid r,
  shadow_le (get_shadow st rid) (get_shadow st' rid) -> rshadow_rep st m rid r -> rshadow_rep st' m rid r.
Proof. intros st st' m rid r [_ HL] [HW HB]. split; [exact HW|]. intros o v Ho Hc. apply HB; auto. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rmrep_upd_shadow : forall st m rid f,
  rmrep st m -> ticks_ok st ->
  (shadow_le (get_shadow st rid) (f (get_shadow st rid)) /\ sh_ticks (f (get_shadow st rid)) (s_tick st)) ->
  rmrep (upd_shadow rid f st) m /\ ticks_ok (upd_shadow rid f st).
Proof.
  intros st m rid f MR TK [HL HT]. pose proof MR as (WF & CX & GL & AR & GR & SH).
  assert (Hconc : forall q, conc (upd_shadow rid f st) q = conc st q) by (intros; reflexivity).
  assert (GS : forall rid', get_shadow (upd_shadow rid f st) rid' = if N.eqb rid' rid then f (get_shadow st rid) else get_shadow st rid').
  { intros rid'. rewrite (get_shadow_unfold (upd_shadow rid f st)). unfold upd_shadow, set_shadow. cbn [s_shadow].
    destruct (N.eqb_spec rid' rid); [subst; rewrite lookup_insert_eq; reflexivity| rewrite lookup_insert_ne by congruence; reflexivity]. }
  split.
  - split; [exact WF|]. split; [eapply rmrep_ctx_ext; [reflexivity|exact Hconc|exact CX]|]. split; [exact GL|].
    split; [intros a ar Ha; eapply rarea_rep_ext; [exact Hconc|intros; reflexivity|exact (AR a ar Ha)]|].
    split; [intros b gh Hb; eapply rgroup_rep_ext; [exact Hconc|exact (GR b gh Hb)]|].
    intros rid' r' Hr' Hk'. cbn in Hr'. eapply rshadow_rep_le; [|exact (SH rid' r' Hr' Hk')].
    rewrite GS. destruct (N.eqb_spec rid' rid); [subst; exact HL| apply shadow_le_refl].
  - destruct TK as [T1 T2]. destruct HT as [HT1 HT2]. split.
    + intros rid' sh u hl ch Hs Hu Hin. cbn [s_tick upd_shadow set_shadow] in *.
      pose proof (GS rid') as G. rewrite (get_shadow_unfold (upd_shadow rid f st)) in G. cbn [s_shadow upd_shadow set_shadow] in G. rewrite Hs in G. cbn in G.
      destruct (N.eqb_spec rid' rid); [subst sh; eapply HT1; eauto|].
      unfold get_shadow in G. destruct (s_shadow st !! rid') eqn:E; cbn in G; [subst; eapply T1; eauto| subst; rewrite lookup_empty in Hu; discriminate].
    + intros rid' sh pg t Hs Hp. cbn [s_tick upd_shadow set_shadow] in *.
      pose proof (GS rid') as G. rewrite (get_shadow_unfold (upd_shadow rid f st)) in G. cbn [s_shadow upd_shadow set_shadow] in G. rewrite Hs in G. cbn in G.
      destruct (N.eqb_spec rid' rid); [subst sh; eapply HT2; eauto|].
      unfold get_shadow in G. destruct (s_shadow st !! rid') eqn:E; cbn in G; [subst; eapply T2; eauto| subst; rewrite lookup_empty in Hp; discriminate].
Qed.

#[using="Type"] Lemma rmrep_havoc : forall st m p n, rmrep st m -> ticks_ok st -> rmrep (havoc p n st) m /\ ticks_ok (havoc p n st).
Proof.
  intros st m p n MR TK. unfold havoc. destruct (n <=? 0); [auto|].
  apply rmrep_upd_shadow; [exact MR|exact TK|].
  pose proof (sh_ticks_of_ticks_ok st (fst p) TK) as T0.
  set (sh := get_shadow st (fst p)) in *. destruct sh as [cells hav havp]. cbn [r_cells r_hav r_havp].
  destruct ((snd p + 4095) / 4096 <? (snd p + n) / 4096).
  - destruct (havoc_pages_le cells hav havp ((snd p + 4095) / 4096) ((snd p + n) / 4096) (s_tick st) T0) as [L1 T1].
    set (hav1 := if snd p <? (snd p + 4095) / 4096 * 4096 then havoc_units (snd p) ((snd p + 4095) / 4096 * 4096) (s_tick st) hav else hav).
    assert (S1 : shadow_le (mkShadow cells hav havp) (mkShadow cells hav1 havp) /\ sh_ticks (mkShadow cells hav1 havp) (s_tick st)).
    { subst hav1. destruct (snd p <? _); [apply havoc_units_le; exact T0| split; [apply shadow_le_refl|exact T0]]. }
    destruct S1 as [L2 T2].
    set (hav2 := if (snd p + n) / 4096 * 4096 <? snd p + n then havoc_units ((snd p + n) / 4096 * 4096) (snd p + n) (s_tick st) hav1 else hav1).
    assert (S2 : shadow_le (mkShadow cells hav1 havp) (mkShadow cells hav2 havp) /\ sh_ticks (mkShadow cells hav2 havp) (s_tick st)).
    { subst hav2. destruct (_ <? snd p + n); [apply havoc_units_le; exact T2| split; [apply shadow_le_refl|exact T2]]. }
    destruct S2 as [L3 T3].
    destruct (havoc_pages_le cells hav2 havp ((snd p + 4095) / 4096) ((snd p + n) / 4096) (s_tick st) T3) as [L4 T4].
    split; [|exact T4]. eapply shadow_le_trans; [exact L2|]. eapply shadow_le_trans; [exact L3|exact L4].
  - apply havoc_units_le. exact T0.
Qed.

#[using="Type"] Lemma rmrep_hdr_havoc : forall st m b, rmrep st m -> ticks_ok st -> rmrep (hdr_havoc b st) m /\ ticks_ok (hdr_havoc b st).
Proof.
  intros st m b MR TK. unfold hdr_havoc.
  apply rmrep_upd_shadow; [exact MR|exact TK|].
  pose proof (sh_ticks_of_ticks_ok st (fst b) TK) as T0.
  set (sh := get_shadow st (fst b)) in *. destruct sh as [cells hav havp]. cbn [r_cells r_hav r_havp].
  apply hav_unit_step. exact T0.
Qed.


(* [comment removed for export] *)

#[using="Type"] Lemma rmrep_transport_high : forall st m m' W,
  rmrep st m -> munch W m m' -> wmono usegs m m' -> W_high W -> rmrep st m'.
Proof.
  intros st m m' W (WF & CX & GL & AR & GR & SH) MU WM HW.
  pose proof WF as (Hres & WR & DJ & WA & WG).
  assert (D : forall a n, a + n <= ATOP -> disjoint_from W a n) by (intros; apply W_high_disjoint; assumption).
  atop_facts.
  assert (TC : forall A cs, rw_cells usegs m A cs -> A + Z.of_nat (cells_size cs) <= ATOP -> rw_cells usegs m' A cs).
  { intros A cs RC HB. eapply rw_cells_transport; eauto. }
  split; [exact WF|]. split; [|split; [|split; [|split]]].
  - (* [comment removed for export] *) destruct CX as (C1 & C2 & C3 & C4 & C5 & C6). unfold rmrep_ctx.
    split; [|split; [|split; [|split; [|split]]]].
    + Local Ltac2 Set LiaHints.tbl := fun () => "00@0>1383158332.26 14063599509.3831651838158.3834060269205.3834157072780.2636220399292.2736563670844.2636651264229.4045505143161.2745990148607.2753845710847.2760141258239.2762380861817.2764715174972.2667012713541.377505247036.26 00000700>00J00V00]00d00k01:01A01H01O01V01]01d020027S5ATOPRS2BC2HoS2Ca3Sa13RBCS2Ca3Sa13RBCS5ATOPRS5ATOPRS5ATOPRS2Ca3Sa13RBC2HkS5ATOPRS5ATOPRS5ATOPRS5ATOPRS5ATOPRS5ATOPRS2Cb3SbL3RBCS5ATOPR".
apply TC; [exact C1 | unfold RCTX; cbn; lia].
    + eapply u64arr_transport; eauto. apply D. unfold actives. rewrite map_length, seq_length. unfold RCTX; cbn; lia.
    + eapply u64arr_transport; eauto. apply D. unfold usages. rewrite map_length, seq_length. unfold RCTX; cbn; lia.
    + eapply u8arr_transport; eauto. apply D. unfold unmap_seqs. rewrite map_length, seq_length. unfold RCTX; cbn; lia.
    + eapply u8arr_transport; eauto. apply D. unfold bouncess. rewrite map_length, seq_length. unfold RCTX; cbn; lia.
    + apply TC; [exact C6 | unfold RCTX; cbn; lia].
  - (* [comment removed for export] *) destruct GL as (G1 & G2 & G3 & G4 & G5). split; [|split; [|split; [|split]]].
    + apply TC; [exact G1 | unfold RMLOCK; cbn; lia].
    + apply TC; [exact G2 | unfold RNEED_LOCKS; cbn; lia].
    + apply TC; [exact G3 | unfold RPAGE_SIZE; cbn; lia].
    + apply TC; [exact G4 | unfold RGOT_SSP; cbn; lia].
    + apply TC; [exact G5 | unfold RSSP_GUARD; cbn; lia].
  - (* [comment removed for export] *) intros a ar Ha. destruct (AR a ar Ha) as (A1 & A2 & A3).
    destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC). atop_facts.
    split; [|split].
    + apply TC; [exact A1 | cbn; lia].
    + intros k Hk. apply TC; [apply A2; exact Hk |]. unfold meta_cells; cbn [cells_size csize Nat.add]. unfold AREA_HDR, META_SIZE, NSLOTS in *. lia.
    + apply TC; [exact A3 | cbn; lia].
  - (* [comment removed for export] *) intros b gh Hb. destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|exact Hw8].
    destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Sb0 & Sb1 & SbL & RB0 & RBAL & RBC). atop_facts.
    apply TC; [exact R | cbn; lia].
  - (* [comment removed for export] *) intros rid r Hr Hk. destruct (SH rid r Hr Hk) as [HWr HB].
    destruct (WR rid r Hr) as (B0 & BAL & L0 & BC & _). atop_facts.
    split.
    + eapply wr_at_transport; eauto.
    + intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
      eapply bytes_at_transport; eauto. apply D. cbn. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".


(* [comment removed for export] *)
#[using="Type"] Lemma rmrep_set_tick : forall st m t, rmrep st m -> rmrep (set_tick t st) m.
Proof.
  intros st m t (WF & CX & GL & AR & GR & SH).
  split; [exact WF|]. split; [|split; [exact GL|split; [|split]]].
  - eapply rmrep_ctx_ext; [reflexivity | intros; reflexivity | exact CX].
  - intros a ar Ha. eapply rarea_rep_ext; [intros; reflexivity | intros; reflexivity | exact (AR a ar Ha)].
  - intros b gh Hb. eapply rgroup_rep_ext; [intros; reflexivity | exact (GR b gh Hb)].
  - intros rid r Hr Hk. eapply rshadow_rep_ext; [reflexivity | exact (SH rid r Hr Hk)].
Qed.


(* [comment removed for export] *)
#[using="Type"] Lemma rwr_at_bytes_exist : forall m a n,
  wr_at usegs m a n -> 0 <= n -> (a + n <= 0x10000 \/ 0x4f000 <= a) ->
  exists bs, length bs = Z.to_nat n /\ bytes_at usegs m a bs.
Proof.
  intros m a n (A0 & An & W) Hn Himg.
  assert (G : forall i, 0 <= i < n -> exists b, mrd usegs m (wa (a + i)) = Some b).
  { intros i Hi. specialize (W i Hi). Local Ltac2 Set LiaHints.tbl := fun () => "00>0>18206263784.2022766053480.1326050683285.1128154384612.1433644857362.1133644859293.1834440809382.1838032483938.1140728791319.1641365104877.1341432093230.1152026327389.186882689537.11 6982569598.18 00000900@00G00M00W00`00f00o01801<01=01F01P01VS2Hk1L2HiS2Hk2HiS2An2HkS2Hn1LS2A02Hn2HkS2A02Hk1LS2Hk1LS4Himg2HiS2Hn2Hk1LS2HkSS2An2Hk1LS2A02An2HiS2Hk1L".
rewrite ref_wview_overlay in W by (rewrite wa_unsigned by lia; lia).
    rewrite ref_mrd_overlay by (rewrite wa_unsigned by lia; lia).
    destruct (m (wa (a + i))) as [b|]; [exists b; reflexivity| exfalso; apply W; reflexivity]. }
  (* [comment removed for export] *)
  assert (REC : forall k, (k <= Z.to_nat n)%nat -> exists bs, length bs = k /\ bytes_at usegs m (a + (n - Z.of_nat k)) bs).
  { induction k as [|k IH]; intros Hk.
    - exists []. split; [reflexivity|]. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
    - destruct (IH ltac:(lia)) as (bs & L & B). destruct (G (n - Z.of_nat (S k)) ltac:(lia)) as (b & Hb).
      exists (b :: bs). split; [cbn; lia|].
      change (b :: bs) with ([b] ++ bs). apply bytes_at_app. split.
      + split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. destruct i; [|lia]. cbn. rewrite Z.add_0_r. exact Hb.
      + cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]. replace (a + (n - Z.of_nat (S k)) + 1) with (a + (n - Z.of_nat k)) by lia. exact B. }
  destruct (REC (Z.to_nat n) ltac:(lia)) as (bs & L & B). exists bs. split; [exact L|].
  replace (a + (n - Z.of_nat (Z.to_nat n))) with a in B by lia. exact B.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
End CANSEC1.
