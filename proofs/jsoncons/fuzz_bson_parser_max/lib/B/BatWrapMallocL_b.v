(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx As0StepLib As0Tables
     ArtMem ArtTac. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatPoison_b BatInitCache_b BatPopulate1_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtRuns ArtRunsMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatCls_b BatFp_b BatClsRep_b BatClsGfa2_b BatClsRefill_b BatCellEx_b BatByteCell_b BatCARSpec_b BatAlloc3Pure_b BatDepot_b BatUnwind_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtBridge. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatAllocate3_b BatSecAllocPost_b BatSecRSpec_b BatAllocate3L_b BatMallocTop3L_b BatInv_b BatInvMallocPure_b BatInvMallocFp_b BatInvMalloc_b BatInvMallocL_b BatInvMallocLB_b BatLift_b BatWrapPure_b BatWrapKit_b
     BatWrapMallocX_b BatWrapMallocH_b BatWrapMallocLA_b BatWrapMallocLX_b BatWrapMallocLC_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

(* [comment removed for export] *)
Lemma art_sec_events_null : forall msz r parr nch cm len r', In (AMmapNull len r') (art_sec_events msz r parr nch cm) -> len = msz /\ r' = r.
Proof.
  intros msz r parr nch cm len r' H. unfold art_sec_events in H. destruct H as [E|H]; [injection E as <- <-; split; reflexivity|].
  destruct cm; [destruct H|]. destruct H as [E|[]]. discriminate E.
Qed.
Lemma art_sec_events_no_nr : forall msz r parr nch cm a l, ~ In (AMmapFixedNR a l) (art_sec_events msz r parr nch cm).
Proof.
  intros msz r parr nch cm a l H. unfold art_sec_events in H. destruct H as [E|H]; [discriminate E|].
  destruct cm; [destruct H|]. destruct H as [E|[]]. discriminate E.
Qed.
Lemma art_sec_events_window : forall log msz r parr nch cm, In (art_shlo r, art_shhi r msz) (art_windows (log ++ art_sec_events msz r parr nch cm)).
Proof.
  intros log msz r parr nch cm. unfold art_windows. rewrite flat_map_app. apply in_or_app. right. unfold art_sec_events. cbn [flat_map]. left. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma art_window_allowed : forall (A' : list (Z * Z)) r msz u n, In (art_shlo r, art_shhi r msz) A' ->
  0 <= r -> r <= u -> 0 < n -> u + n <= r + msz -> r + msz <= 2 ^ 47 -> 8 * (r / 8) = r -> 8 * (msz / 8) = msz -> shadow_allowed A' u n.
Proof.
  intros A' r msz u n Hin Hr Hu Hn Hun Hhi E1 E2 x (X1 & X2). unfold HeapIfaceA.S, HeapIfaceA.SB in X1, X2.
  assert (D1 : r / 8 <= u / 8) by (apply Z.div_le_mono; lia).
  assert (E3 : (r + msz) / 8 = r / 8 + msz / 8). { rewrite <- E1 at 1. rewrite <- E2 at 1. replace (8 * (r / 8) + 8 * (msz / 8)) with ((r / 8 + msz / 8) * 8) by lia. apply Z.div_mul. lia. }
  assert (D2 : (u + n - 1) / 8 < (r + msz) / 8) by (apply Z.div_lt_upper_bound; lia).
  assert (D0 : 0 <= r / 8) by (apply Z.div_pos; lia).
  assert (D3 : (r + msz) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
  set (lo := art_shlo r) in *. set (hi := art_shhi r msz) in *.
  assert (Elo : exists a', lo = 4096 * a' /\ 4096 * a' <= r / 8 + 0x7fff8000).
  { exists ((r / 8 + 0x7fff8000) / 4096). unfold lo, art_shlo. split; [lia|]. apply Z.mul_div_le. lia. }
  assert (Ehi : exists b', hi = 4096 * b' /\ (r + msz) / 8 + 0x7fff8000 <= 4096 * b').
  { exists (((r + msz) / 8 + 0x7fff8000 + 4095) / 4096). unfold hi, art_shhi. split; [lia|].
    pose proof (Z.mul_succ_div_gt ((r + msz) / 8 + 0x7fff8000 + 4095) 4096 ltac:(lia)). lia. }
  destruct Elo as (a' & Elo & La). destruct Ehi as (b' & Ehi & Lb).
  assert (Rx : 0 <= x < 2 ^ 64) by lia.
  assert (Ux : U (Z_to_bv 64 x : word) = x) by (apply art_u_lit; lia).
  assert (PB : U (page_base (Z_to_bv 64 x)) = x / 4096 * 4096).
  { unfold page_base, page_base_of, page_size. rewrite Ux. apply art_u_lit. pose proof (Z.mul_div_le x 4096 ltac:(lia)). pose proof (Z.div_pos x 4096 ltac:(lia) ltac:(lia)). lia. }
  unfold page_allowedb. apply existsb_exists. exists (lo, hi). split; [exact Hin|]. cbn [fst snd]. rewrite PB. unfold page_size.
  pose proof (Z.mul_div_le x 4096 ltac:(lia)) as K1. pose proof (Z.mul_succ_div_gt x 4096 ltac:(lia)) as K2. set (k := x / 4096) in *.
  apply andb_true_intro. split; apply Z.leb_le; lia.
Qed.

(* [comment removed for export] *)
Lemma art_sec_evok1 : forall RES BUDGET log msz r0, 0 < msz -> msz mod 4096 = 0 -> msz <= LENMAX -> Z.of_nat (length (art_live log)) < KMAX ->
  art_cost_sum log + (msz + msz / 8 + 8192) <= BUDGET -> art_EVOK RES BUDGET LENMAX KMAX log (AMmapNull msz r0).
Proof.
  intros RES BUDGET log msz r0 H1 H2 H3 H4 H5. unfold art_EVOK. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
  rewrite art_cost_sum_snoc. cbn [art_cost]. lia.
Qed.
Lemma art_sec_evok2 : forall RES BUDGET log msz r parr, In (parr, 2 ^ 23) RES -> parr mod 4096 = 0 -> 0 <= msz ->
  art_cost_sum log + (msz + msz / 8 + 8192) + 131072 <= BUDGET ->
  art_EVOK RES BUDGET LENMAX KMAX (log ++ [AMmapNull msz r]) (AMmapFixed (parr + 8 * 0) 131072).
Proof.
  intros RES BUDGET log msz r parr HR Hp Hm HB. unfold art_EVOK. rewrite Z.mul_0_r, Z.add_0_r. split; [exact Hp|]. split; [reflexivity|]. split; [lia|].
  split. { exists (parr, 2 ^ 23). split; [exact HR|]. cbn [fst snd]. lia. }
  rewrite !art_cost_sum_snoc. cbn [art_cost]. lia.
Qed.

(* [comment removed for export] *)
Section ExitFs.
#[using="Type"] Lemma art_wmlc_fs : forall rn LB FF LK (A : list (Z * Z)) (lazy : list (word * word)) (M M1 : word -> option byte) (Sp nch r msz : Z) (cm : bool),
  let WL := art_malloc3L_fp Sp (rn_t rn) (rn_parr rn) nch r msz (rn_l2 rn) (rn_blk rn) cm in
  art_run_ok rn -> art_client_ok rn LB FF LK A M ->
  (forall x : word, art_out WL (U x) -> M1 x = M x) ->
  (forall x : word, art_shlo r <= U x < art_shhi r msz -> ~ (BatPoison_b.SB + r / 8 <= U x < BatPoison_b.SB + r / 8 + msz / 8) ->
        mkH lazy A x = false -> M x <> None -> M1 x = M x) ->
  (forall a : word, in_shadow_rw (U a) -> M a <> None) ->
  rn_HI rn + 4096 <= Sp - 4096 -> Sp <= 2 ^ 47 -> 0 <= nch <= 16384 ->
  art_sec_grant3 (rn_HI rn) (rn_t rn) (rn_ctx rn) (rn_parr rn) (rn_spb rn) (rn_l2 rn) (rn_blk rn) msz r -> apart r msz (ar_fs (rn_ar rn)) FS_BYTES ->
  apart r msz (rn_dtls rn) 4096 ->
  8 * (r / 8) = r -> 8 * (msz / 8) = msz -> 0 < msz ->
  ((LSH_LO <= art_shlo r /\ art_shhi r msz <= LSH_HI) \/ (HSH_LO <= art_shlo r /\ art_shhi r msz <= HSH_HI)) ->
  forall x : word, art_fs_zone rn (U x) -> M1 x = M x.
Proof.
  intros rn LB FF LK A lazy M M1 Sp nch r msz cm WL ROK CLI FRF FRW SHD HS HS47 Hnch GRANT Arf Ard E1 E2 Hmsz WOK x Z.
  pose proof (art_run_ok_tail rn ROK) as (Il2 & Iblk & _ & D0 & D1 & D2 & D3 & _).
  pose proof ROK as ROK'. rok_open ROK'. geo_open GEO.
  destruct GRANT as ((Hr4 & Hr & Hri & Hrm & APr & Art & Arc & Arp) & Ark & Arl2 & Arblk).
  destruct CLI as (CB & CND & CSA1 & CSA2 & CS1 & CS2 & CS3 & CS4 & CS5 & CS6 & CSI & CSP & CS16).
  unfold appmem, BatPoison_b.SB, BatPoison_b.kHighMemBeg in APr. unfold LSH_LO, LSH_HI, HSH_LO, HSH_HI in WOK.
  pose proof (u64_range x) as Rx.
  (* [comment removed for export] *)
  assert (SHEQ : forall lo len, 0 <= lo -> 0 < len -> lo + len <= 2 ^ 47 -> apart r msz lo len -> in_shadow_of lo len (U x) ->
                   page_allowedb A (page_base x) = true -> M1 x = M x).
  { intros lo len Hlo Hlen Hhi AP SH AL.
    pose proof (art_sh_apart r msz lo len (U x) E1 E2 Hlo Hlen AP SH) as NE.
    destruct SH as (SH1 & SH2). pose proof (art_S_ge lo 0 ltac:(lia)) as B0. pose proof (art_S_lt (lo + len - 1) (2 ^ 44) ltac:(lia)) as B2.
    destruct (Z_le_dec (art_shlo r) (U x)) as [L1|L1]; [destruct (Z_lt_dec (U x) (art_shhi r msz)) as [L2|L2]|].
    - apply FRW; [(clear - L1 L2 msz r x; lia)|exact NE|apply art_allowed_vis; exact AL|apply SHD; unfold in_shadow_rw, LSH_LO, LSH_HI, HSH_LO, HSH_HI; (clear - B0 B2 CS1 CS6 D2 Flo Hmsz Hr L1 L2 Plo SH1 SH2 WOK len lo msz r rn x; lia)].
    - apply FRF. unfold WL, art_malloc3L_fp. destruct Papp as (_ & Pap & _). unfold BIGSHADOW_LO, BIGSHADOW_HI in Pap.
      set (wlo := art_shlo r) in *. set (whi := art_shhi r msz) in *.
      clear - B0 B2 SH1 SH2 L2 HS G1 G10 APr Pap Al2s Abs Hnch. unfold apart in *. cbn [art_out fst snd]. destruct cm; repeat split; try exact I; lia.
    - apply FRF. unfold WL, art_malloc3L_fp. destruct Papp as (_ & Pap & _). unfold BIGSHADOW_LO, BIGSHADOW_HI in Pap.
      set (wlo := art_shlo r) in *. set (whi := art_shhi r msz) in *.
      clear - B0 B2 SH1 SH2 L1 HS G1 G10 APr Pap Al2s Abs Hnch. unfold apart in *. cbn [art_out fst snd]. destruct cm; repeat split; try exact I; lia. }
  assert (PBx : page_base x = page_base (Z_to_bv 64 (U x))) by (rewrite Z_to_bv_bv_unsigned; reflexivity).
  destruct Z as [Z|[Z|[Z|[(Z & NS)|[Z|Z]]]]].
  - (* [comment removed for export] *)
    apply FRF. unfold WL, art_malloc3L_fp. destruct Fapp as (_ & Fap & _). unfold BIGSHADOW_LO, BIGSHADOW_HI in Fap. set (wlo := art_shlo r) in *. set (whi := art_shhi r msz) in *.
    clear - Z HS G1 Fhi Fimg Aft Arf Fap WOK Afp Afl Afb Hnch. unfold apart, FS_BYTES in *. cbn [art_out fst snd]. destruct cm; repeat split; try exact I; lia.
  - (* [comment removed for export] *)
    apply FRF. apply (art_gap_out WL (U x) 1 (U x)); [|lia].
    unfold WL, art_malloc3L_fp. destruct Papp as (_ & Pap & _). unfold BIGSHADOW_LO, BIGSHADOW_HI in Pap. set (wlo := art_shlo r) in *. set (whi := art_shhi r msz) in *.
    clear - Z HS G1 G2 G4 G6 G7 G8 G9 G10 G11 Art WOK Apt Al2t Abt Hnch. unfold apart in *. cbn [art_gap fst snd]. unfold apart. destruct cm; repeat split; try exact I; lia.
  - (* [comment removed for export] *)
    apply (SHEQ (ar_fs (rn_ar rn)) FS_BYTES); [lia|unfold FS_BYTES; lia|unfold FS_BYTES in *; lia|exact Arf| |].
    + unfold in_shadow_of. pose proof (art_S_pred (ar_fs (rn_ar rn) + FS_BYTES)). lia.
    + rewrite PBx. apply CSA2. unfold in_shadow_of. pose proof (art_S_pred (ar_fs (rn_ar rn) + FS_BYTES)). lia.
  - (* [comment removed for export] *)
    apply FRF. unfold art_zone_statics in NS. unfold WL, art_malloc3L_fp. set (wlo := art_shlo r) in *. set (whi := art_shhi r msz) in *.
    clear - Z NS HS G1 G9 Hri WOK Plo Il2 Iblk Hnch. unfold apart in *. cbn [art_out fst snd]. destruct cm; repeat split; try exact I; lia.
  - (* [comment removed for export] *)
    apply (SHEQ 0x10000 (0x696000 - 0x10000)); [lia|lia|lia|unfold apart; lia| |].
    + unfold in_shadow_of. pose proof (art_S_pred 0x696000). replace (0x10000 + (0x696000 - 0x10000) - 1) with (0x696000 - 1) by lia. lia.
    + rewrite PBx. apply CSI. unfold in_shadow_of. pose proof (art_S_pred 0x696000). replace (0x10000 + (0x696000 - 0x10000) - 1) with (0x696000 - 1) by lia. lia.
  - (* [comment removed for export] *)
    apply FRF. unfold WL, art_malloc3L_fp. destruct D3 as (_ & Dap & _). unfold BIGSHADOW_LO, BIGSHADOW_HI in Dap. set (wlo := art_shlo r) in *. set (whi := art_shhi r msz) in *.
    pose proof (art_run_ok_tail rn ROK) as (_ & _ & _ & _ & _ & _ & _ & Adt & _ & _ & Adp & Adl & Adb & _).
    clear - Z HS G1 D0 D1 D2 Dap Ard Adt Adp Adl Adb WOK Hnch. unfold apart in *. cbn [art_out fst snd]. destruct cm; repeat split; try exact I; lia.
Qed.
End ExitFs.

(* [comment removed for export] *)
Lemma art_mod4096_8 : forall r, r mod 4096 = 0 -> 8 * (r / 8) = r.
Proof. intros r H. pose proof (Z.div_mod r 4096 ltac:(lia)) as D. rewrite H, Z.add_0_r in D. rewrite D at 1. replace (4096 * (r / 4096)) with ((512 * (r / 4096)) * 8) by lia. rewrite Z.div_mul by lia. lia. Qed.
Lemma art_rok_parr : forall rn, art_run_ok rn -> rn_parr rn mod 4096 = 0 /\ 0x696000 <= rn_parr rn /\ rn_parr rn + 2 ^ 23 <= rn_HI rn /\ rn_HI rn + 8388608 <= 2 ^ 47.
Proof. intros rn ROK. rok_open ROK. geo_open GEO. split; [exact Pal|]. split; [exact Plo|]. split; [exact Phi|exact G2]. Qed.
Lemma art_sec_sizes : forall n rz qz rs qr nd q msz lin ov, 8 <= n <= 2 ^ 27 -> rz = 16 * qz -> 2 <= qz <= 128 -> rs = 8 * qr -> n <= rs <= n + 7 -> 65536 < rs + rz ->
  nd = rs + rz + rz -> 4096 * (q - 1) < nd <= 4096 * q -> msz = 4096 * q + 4096 -> 2 <= lin -> 2 ^ 20 <= ov ->
  73721 <= msz <= 2 ^ 27 + 16384 /\ msz mod 4096 = 0 /\ 8 * (msz / 8) = msz /\ msz + msz / 8 + 8192 + 131072 + 2 ^ 19 <= lin * n + ov /\ 4096 < n /\ 4096 + rz + n <= msz /\ 32 <= rz <= 2048.
Proof.
  intros n rz qz rs qr nd q msz lin ov Hn Erz Hqz Ers Hrs Hsec End Hq Emsz Hlin Hov.
  assert (Hm4 : msz mod 4096 = 0). { rewrite Emsz. replace (4096 * q + 4096) with ((q + 1) * 4096) by lia. apply Z_mod_mult. }
  assert (Hm8 : msz / 8 = 512 * q + 512). { rewrite Emsz. replace (4096 * q + 4096) with ((512 * q + 512) * 8) by lia. apply Z.div_mul. lia. }
  assert (Hl : 2 * n <= lin * n) by (apply Z.mul_le_mono_nonneg_r; lia).
  split; [lia|]. split; [exact Hm4|]. split; [lia|]. split; [lia|]. split; [lia|]. split; lia.
Qed.

(* [comment removed for export] *)
Section Wrap.
Variable FSG : Type.
Variable FSINV : art_run -> FSG -> list fframe -> list fframe -> (word -> option byte) -> Prop.
Variables MAPS0 RESV0 NOACC0 : list (word * word).
Variables BASE BUDGET : Z.
Variable rn : art_run.
Variable scfg : SpuriousCfg.
Variable L : asan_layout.
Hypothesis Halloc : sc_alloc scfg = false.
Hypothesis Hwx : wx_segs_nowrap ASEGS.
Hypothesis STATIC : bridge_static ASEGS MAPS0 RESV0 NOACC0 (art_RES rn) (rn_HI rn) BUDGET LENMAX KMAX.
Hypothesis HLsegs : hl_segs L = ASEGS.
Hypothesis HLmalloc : hl_malloc L = 0x79818.
Hypothesis HLscr : hl_scr_malloc L = 4096.
Hypothesis HLtp : hl_tp L = rn_tp rn.
Hypothesis HLlo : hl_img_lo L = 0x10000.
Hypothesis HLhi : hl_img_hi L = 0x696000.
Hypothesis HLst : forall a, art_zone_statics a -> hl_rt_static L a.
Hypothesis HLk : 3 <= hl_k_per_malloc L.
Hypothesis HLlin : 2 <= hl_b_lin L.
Hypothesis HLov : 2 ^ 20 <= hl_b_overhead L.
Hypothesis FSLAW : art_fsinv_frame_law FSG FSINV.
Hypothesis FS_IN : forall gfs FF LK M, FSINV rn gfs FF LK M ->
  forall f, In f (FF ++ LK) -> ar_fs (rn_ar rn) <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= ar_fs (rn_ar rn) + FS_BYTES /\ 0 < ff_bytes (ff_class f).
Context {fx : PropExec.FPState}.

#[using="Halloc Hwx STATIC HLsegs HLscr HLtp HLlo HLhi HLst HLk HLlin HLov FSLAW FS_IN"] Theorem art_wrap_malloc_sec :
  forall (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z))
         (n rl rz qz rs qr qn m8 nd q msz : Z) (K : ShapeAlg.TSet),
    art_ri_inv FSG MAPS0 RESV0 NOACC0 BASE BUDGET FSINV rn LB FF LK cr A M (vml_of model) -> m_halted model = None -> MInv A model ->
    getr R 10 = Z_to_bv 64 n -> 8 <= n <= 2 ^ 27 ->
    rl = AsanTab.rz_log n -> rz = 16 * 2 ^ rl -> rz = 16 * qz -> 2 <= qz <= 128 -> n = 8 * qn + m8 -> 0 <= m8 <= 7 -> rs = 8 * qr -> n <= rs <= n + 7 ->
    65536 < rs + rz ->                                                          (* [comment removed for export] *)
    nd = rs + rz + rz -> 4096 * (q - 1) < nd <= 4096 * q -> msz = 4096 * q + 4096 ->
    acredit_ok L cr n -> getr R 4 = Z_to_bv 64 (hl_tp L) -> Hoare.ret_ok (getr R 1) ->
    astack_ok L (rn_ar rn) M (hl_scr_malloc L) (U (getr R 2)) ->
    amalloc_post L (rn_ar rn) scfg (art_iface FSG MAPS0 RESV0 NOACC0 BASE BUDGET FSINV rn) fx R M model LB FF LK cr A n K ->
    srealizes ASEGS scfg (mkCfg (mkst R (0x79818 : word) M (seg_rom ASEGS)) model) K.
Proof.
  intros R M model LB FF LK cr A n rl rz qz rs qr qn m8 nd q msz K RI Hhalt HMI H10 Hn Erl Erz Erz16 Hqz En Hm8 Ers Hrs Hsec End Hq Emsz ACR H4 Hret AST POST.
  destruct RI as (G & REPr & FS & BV & CRED & CLI & KN & LZ & EG). cbn [vml_of fst snd] in REPr, BV, LZ, EG.
  pose proof (BINV_elim _ _ _ _ _ _ _ _ _ _ _ BV Hhalt HMI) as B0.
  pose proof REPr as (ROK & _ & _ & _ & _ & SEC0 & _). destruct (art_rok_parr rn ROK) as (Pal & Plo & Phi & G2).
  set (Sp := U (getr R 2)) in *. assert (H2 : getr R 2 = Z_to_bv 64 Sp) by (unfold Sp; symmetry; apply Z_to_bv_bv_unsigned).
  rewrite HLscr in AST. destruct AST as (S16 & SHI & SLE & STOP & SWR & SDEF).
  assert (HIeq : ahl_ceil (rn_ar rn) = rn_HI rn) by reflexivity. rewrite HIeq in SHI.
  pose proof CLI as (_ & _ & _ & _ & CS1 & CS2 & CS3 & CS4 & CS5 & CS6 & _). rewrite HIeq in CS1, CS2.
  pose proof CRED as (CR1 & CR2 & CR3 & CR4 & CR5 & CR6 & CR7 & CR8). destruct ACR as (AC1 & AC2).
  destruct (g_depot FSG G) as [|kb] eqn:Edep; [exfalso; cbn in CR6; clear - CR6 AC1 HLk; lia|].
  set (nch := Z.of_nat (length (g_sec FSG G))) in *. set (cm := g_sec_committed FSG G) in *.
  destruct SEC0 as (_ & _ & _ & _ & _ & _ & CMT & _).
  assert (Hnch0 : cm = false -> nch = 0).
  { intros E. unfold nch. destruct (g_sec FSG G) as [|s0 l0] eqn:Eg; [reflexivity|]. exfalso. unfold cm in E. rewrite CMT in E by discriminate. discriminate E. }
  assert (Hnch : 0 <= nch /\ nch + 1 <= 16384) by (unfold nch; clear - CR5 AC1 HLk; lia).
  destruct (art_sec_sizes n rz qz rs qr nd q msz (hl_b_lin L) (hl_b_overhead L) Hn Erz16 Hqz Ers Hrs Hsec End Hq Emsz HLlin HLov) as (Hmsz & Hm4 & E2 & Hcost & Hbig & Hfitm & Hrz).
  assert (HS1 : rn_HI rn + 4096 <= Sp - 4096) by (clear - SHI; lia).
  assert (HS2 : Sp <= 2 ^ 47) by (clear - SLE STOP; lia).
  assert (HS3 : 0 <= ar_stack_bottom (rn_ar rn) /\ ar_stack_bottom (rn_ar rn) < ar_stack_top (rn_ar rn) /\ 4096 <= ar_stack_top (rn_ar rn) /\ ar_stack_top (rn_ar rn) < 2 ^ 63).
  { clear - CS1 CS2 CS3 CS4 CS5 G2 Phi Plo. lia. }
  destruct HS3 as (Hbot0 & Hbt & Htop4 & Htop63).
  pose proof (art_live_of_binv MAPS0 RESV0 NOACC0 BASE BUDGET rn _ _ _ _ B0 KN) as LIVE.
  set (Mr0 := mrestrict (mkH (m_vm_lazy model) A) M) in *.
  assert (W0 : wrA Mr0 (Sp - 4096) 4096). { apply (art_stack_wr FSG rn G A (m_vm_lazy model) M Sp 4096 ROK LZ ltac:(clear - HS1; lia) ltac:(clear; lia) ltac:(clear - HS2; lia)). rewrite <- HLsegs. exact SWR. }
  assert (RD0 : readable8 Mr0 Sp (ar_stack_top (rn_ar rn))). { apply (art_stack_readable FSG rn G A (m_vm_lazy model) M Sp (ar_stack_top (rn_ar rn)) ROK LZ ltac:(clear - HS1; lia) ltac:(clear - Htop63 CS4; lia) SDEF). }
  set (raw0 := getr R 1) in *.
  assert (H4' : getr R 4 = Z_to_bv 64 (rn_tp rn)) by (rewrite <- HLtp; exact H4).
  set (P := fun r : Z => art_GR (KN0 MAPS0 RESV0) (rn_HI rn) (g_log FSG G) Mr0 msz r).
  assert (HP : forall r, P r -> art_sec_grant3 (rn_HI rn) (rn_t rn) (rn_ctx rn) (rn_parr rn) (rn_spb rn) (rn_l2 rn) (rn_blk rn) msz r
                               /\ (forall p, In p (art_live (g_log FSG G)) -> apart r msz (fst p) (snd p))
                               /\ apart r msz (ar_fs (rn_ar rn)) FS_BYTES /\ apart r msz (rn_dtls rn) 4096 /\ apart r msz (rn_kbase rn) 0x2000011000).
  { intros r Pr. exact (art_gr_grant MAPS0 RESV0 rn (g_log FSG G) Mr0 msz r ROK KN (proj1 Hmsz) Pr). }
  set (Qm := fun (log' : list aev) (st : machine_state) =>
     exists r regs' (Mr' : word -> option byte) b1, P r /\ st = mkst regs' raw0 Mr' (seg_rom ASEGS) /\ log' = g_log FSG G ++ art_sec_events msz r (rn_parr rn) nch cm
       /\ getr regs' 10 = Z_to_bv 64 (4096 + r + rz) /\ getr regs' 2 = Z_to_bv 64 Sp
       /\ (forall x : reg, In x [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' x = getr R x)
       /\ art_malloc_out_sec rn Mr0 Mr' Sp n rz qz qn m8 nd msz r nch cm kb b1).
  apply (aruns_srealizes_h ASEGS scfg Halloc Hwx MAPS0 RESV0 NOACC0 (art_RES rn) (rn_HI rn) BASE BUDGET LENMAX KMAX STATIC Qm K model A M model (g_log FSG G))
    with (log := g_log FSG G) (s := restrict (bhid A model) (mkst R (0x79818 : word) M (seg_rom ASEGS))) (A := A) (model := model);
    [ | | reflexivity | exact B0 | apply bmodel_rt_refl | apply bhist_refl ].
  2: { (* [comment removed for export] *)
    rewrite restrict_mkst. change (mrestrict (bhid A model) M) with Mr0.
    eapply ar_steps; [apply art_malloc_thunk|].
    apply (art_wm_entry_sec FSG _ _ Qm P (g_log FSG G) R Mr0 (seg_rom ASEGS) raw0 rn G LB Sp n rl rz qz rs qr qn m8 nd q msz (ar_stack_top (rn_ar rn)) (ar_stack_bottom (rn_ar rn)) kb
             REPr eq_refl Hret H2 H4' H10 ltac:(clear - Hn; lia) Erl Erz Erz16 Hqz En Hm8 Ers Hrs Hsec End Hq Emsz HS1 HS2 S16 eq_refl eq_refl Hbot0 Hbt Htop4 Htop63
             W0 RD0 Edep (proj2 Hnch)).
    - intros Mx r GRr. exact GRr.
    - intros r Pr. exact (proj1 (HP r Pr)).
    - apply art_sec_evok1; [clear - Hmsz; lia|exact Hm4|unfold LENMAX; clear - Hmsz; lia|unfold KMAX in *; clear - CR4 AC1 HLk; lia|clear - CR3 AC2 Hcost; lia].
    - intros Ecm r Pr. fold nch. rewrite (Hnch0 Ecm). apply art_sec_evok2; [right; left; reflexivity|exact Pal|clear - Hmsz; lia|clear - CR3 AC2 Hcost; lia].
    - intros r regs' Mr' b1 Pr P10 P2 P1 PK OUT. exists r, regs', Mr', b1. split; [exact Pr|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact P10|]. split; [exact P2|]. split; [exact PK|exact OUT]. }
  (* [comment removed for export] *)
  intros log' A' ms' model' B1 RT BH (r & regs' & Mr' & b1 & Pr & Est & Elog & P10 & P2 & PK & OUT).
  destruct (restrict_eq_mkst _ _ _ _ _ _ Est) as (Ems & EMr). set (M1 := ms_mem ms') in *. rewrite Ems. subst Mr'.
  destruct (HP r Pr) as (GRANT & GLIVE & Arf & Ard & Arkb).
  pose proof GRANT as ((Hr4 & Hr & Hri & Hrm & APr & _) & _).
  assert (Hn28 : 8 <= n < 2 ^ 28) by (clear - Hn; lia).
  pose proof (art_alloc_rep_malloc_sec FSG rn G LB Mr0 (mrestrict (bhid A' model') M1) Sp n rz qz rs qr qn m8 nd q msz r kb b1
                REPr Hn28 Erz16 Hqz En Hm8 Ers Hrs Hsec End Hq Emsz HS1 Edep GRANT GLIVE OUT LIVE (proj2 Hnch)) as REP'.
  pose proof (art_lrep_new_shadow FSG rn G LB Mr0 (mrestrict (bhid A' model') M1) Sp n rz qz rs qr qn m8 nd q msz r kb b1
                REPr Hn28 Erz16 Hqz En Hm8 Ers Hrs Hsec End Hq Emsz HS1 Edep GRANT GLIVE OUT LIVE (proj2 Hnch)) as NSH.      (* [comment removed for export] *)
  pose proof (art_lrep_blocks_apart_r FSG rn G LB Mr0 rz msz r kb REPr Edep GRANT GLIVE) as BLK.
  pose proof (art_lrep_nfp_block FSG rn G LB Mr0 Sp rz qz rs qr nd q msz r kb REPr Erz16 Hqz Ers Hsec End Hq Emsz HS1 Edep GRANT GLIVE LIVE) as NFPB.
  fold nch in NFPB. fold cm in NFPB.
  set (u := 4096 + r + rz) in *.
  pose proof OUT as (GRW & AG & WIN & _ & WSr & _).
  assert (OUTL : art_malloc_out_sec rn Mr0 (mrestrict (bhid A' model') M1) Sp n rz qz qn m8 nd msz r nch cm kb b1) by exact OUT.
  destruct OUTL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & WSp).
  (* [comment removed for export] *)
  assert (WINA : In (art_shlo r, art_shhi r msz) A' /\ window_ok (art_shlo r, art_shhi r msz)).
  { apply (bi_windows _ _ _ _ _ _ _ _ _ _ _ B1). rewrite Elog. apply art_sec_events_window. }
  destruct WINA as (WinA & (_ & _ & _ & WOK)). cbn [fst snd] in WOK.
  assert (E1 : 8 * (r / 8) = r) by exact (art_mod4096_8 r Hr4).
  destruct (art_wmlc_mem A A' M M1 model model' (g_log FSG G) log' Sp (rn_t rn) (rn_parr rn) nch r msz (rn_l2 rn) (rn_blk rn) cm Elog BH
              (bi_shdef _ _ _ _ _ _ _ _ _ _ _ B1) WOK Plo ltac:(clear - Phi G2; lia) ltac:(clear - Hnch; lia) Hnch0 GRW AG WIN WSp) as (FRF & FRW & GRF & VISP).
  pose proof BH as (sfx & Esfx & INC & BH2 & _ & BH4 & BH5).
  assert (Esfx' : sfx = art_sec_events msz r (rn_parr rn) nch cm). { rewrite Elog in Esfx. apply app_inv_head in Esfx. symmetry. exact Esfx. }
  (* [comment removed for export] *)
  assert (LZ' : art_lazy_ok FSG rn (art_gs_malloc_sec G (rn_parr rn) msz r u n kb) A' (m_vm_lazy model')).
  { apply (art_wmlx_lazy FSG rn G A (m_vm_lazy model) A' (m_vm_lazy model') msz r u n kb LZ INC).
    - intros x Hx. exact (proj1 (BH2 x Hx)).
    - intros wd Hwd. destruct (BH4 wd Hwd) as [Hin|(len & r' & Hev & Ew)]; [left; exact Hin|]. right. rewrite Esfx' in Hev.
      destruct (art_sec_events_null _ _ _ _ _ _ _ Hev) as (-> & ->). exact Ew.
    - unfold LSH_LO, LSH_HI, HSH_LO, HSH_HI in WOK. clear - WOK. lia.
    - unfold LSH_LO, LSH_HI, HSH_LO, HSH_HI in WOK. clear - WOK. lia.
    - intros x Hx. destruct (BH5 x Hx) as [Hl|(a & l & Hev & _)]; [exact Hl|]. exfalso. rewrite Esfx' in Hev. exact (art_sec_events_no_nr _ _ _ _ _ _ _ Hev).
    - exact VISP. }
  (* [comment removed for export] *)
  assert (Hu1 : r + 4096 <= u) by (unfold u; clear - Hrz; lia).
  assert (Hu2 : u + n <= r + msz) by (unfold u; clear - Hfitm; lia).
  assert (Hr64 : 0 <= r /\ r + msz < 2 ^ 63) by (clear - Hr Hrm G2; lia).
  assert (Hu16 : u mod 16 = 0).
  { unfold u. pose proof (Z.div_mod r 4096 ltac:(clear; lia)) as D. rewrite Hr4, Z.add_0_r in D. rewrite D, Erz16.
    replace (4096 + 4096 * (r / 4096) + 16 * qz) with ((256 + 256 * (r / 4096) + qz) * 16) by (clear; lia). apply Z_mod_mult. }
  assert (DEFu : defined M1 u n).
  { intros i Hi. pose proof (art_wr_wview ASEGS (mrestrict (bhid A' model') M1) r msz ltac:(clear - Hr64; lia) ltac:(clear - Hr64; lia) WSr (Z_to_bv 64 (u + i))) as V.
    rewrite art_u_lit in V by (clear - Hi Hu1 Hu2 Hr64; lia). specialize (V ltac:(clear - Hi Hu1 Hu2; lia)).
    rewrite art_wview_off in V by (rewrite art_u_lit by (clear - Hi Hu1 Hu2 Hr64; lia); right; clear - Hi Hu1 Hri; lia). unfold mrestrict in V. destruct (bhid A' model' (Z_to_bv 64 (u + i))); [exfalso; apply V; reflexivity|exact V]. }
  assert (SHu : shadow_blk M1 u n).
  { destruct NSH as (SHz & SHp).
    split; [intros j Hj; exact (art_byte_unrestrict _ _ _ _ (SHz j Hj))|intros Hm; exact (art_byte_unrestrict _ _ _ _ (SHp Hm))]. }
  assert (SAu : shadow_allowed A' u n) by (apply (art_window_allowed A' r msz u n WinA); first [exact E1|exact E2|exact Hu2|(clear - Hr64 Hu1 Hbig Hrm G2; lia)]).
  assert (EG' : art_eager_ok ((u, n) :: LB) A' (m_vm_lazy model')).
  { pose proof GRANT as ((_ & _ & _ & _ & APr' & _ & _ & Arp') & _ & _ & Arblk').
    apply (art_wmlx_eager FSG rn (art_gs_malloc_sec G (rn_parr rn) msz r u n kb) LB A (m_vm_lazy model) A' (m_vm_lazy model') msz r u n EG (bi_awf _ _ _ _ _ _ _ _ _ _ _ B1) LZ').
    - intros x Hx. destruct (BH5 x Hx) as [Hl|(a & l & Hev & _)]; [exact Hl|]. exfalso. rewrite Esfx' in Hev. exact (art_sec_events_no_nr _ _ _ _ _ _ _ Hev).
    - unfold appmem, BatPoison_b.SB, BatPoison_b.kHighMemBeg in APr'. clear - APr'. lia.
    - exact Arblk'.
    - exact Arkb.
    - exact Arp'.
    - clear - Hu1. lia.
    - exact Hu2. }
  assert (SCR : forall a, Sp - 4096 <= a < Sp -> M (Z_to_bv 64 a) <> None).
  { intros a Ha. assert (WM : wrA M (Sp - 4096) 4096) by (intros d k Hd Hk; rewrite <- HLsegs; apply SWR; assumption).
    assert (Rs : 0x696000 <= Sp - 4096 /\ Sp < 2 ^ 63) by (clear - HS1 HS2 Phi Plo; lia).
    pose proof (art_wr_wview ASEGS M (Sp - 4096) 4096 ltac:(clear - Rs; lia) ltac:(clear - Rs; lia) WM (Z_to_bv 64 a)) as V. rewrite art_u_lit in V by (clear - Rs Ha; lia). specialize (V ltac:(clear - Ha; lia)).
    rewrite art_wview_off in V by (rewrite art_u_lit by (clear - Rs Ha; lia); right; clear - Rs Ha; lia). exact V. }
  destruct (art_wmlc_client L HLlo HLhi HLst rn LB FF LK A A' (m_vm_lazy model) M M1 Sp nch r msz u n cm ROK CLI INC GRF FRF FRW
              (bi_shdef _ _ _ _ _ _ _ _ _ _ _ B0) HS1 HS2 ltac:(clear - Hnch; lia) GRANT Arf E1 E2 ltac:(clear - Hmsz; lia) WOK BLK NFPB (FS_IN _ _ _ _ FS) SCR Hu1 Hu2 Hu16 Hbig DEFu SHu SAu)
    as (CLI' & ABR & BA & FFA & AHP).
  (* [comment removed for export] *)
  assert (RI' : art_ri_inv FSG MAPS0 RESV0 NOACC0 BASE BUDGET FSINV rn ((u, n) :: LB) FF LK (adebit L cr n) A' M1 (vml_of model')).
  { exists (art_gs_malloc_sec G (rn_parr rn) msz r u n kb). cbn [vml_of fst snd].
    split; [exact REP'|]. split.
    { cbn [art_gs_malloc_sec g_fs]. apply (FSLAW rn (g_fs FSG G) FF LK M M1 FS GRF).
      exact (art_wmlc_fs rn LB FF LK A (m_vm_lazy model) M M1 Sp nch r msz cm ROK CLI FRF FRW (bi_shdef _ _ _ _ _ _ _ _ _ _ _ B0) HS1 HS2 ltac:(clear - Hnch; lia)
               GRANT Arf Ard E1 E2 ltac:(clear - Hmsz; lia) WOK). }
    split. { cbn [art_gs_malloc_sec g_log]. fold nch. fold cm. pose proof B1 as B1'. rewrite Elog in B1'. exact (BINV_intro _ _ _ _ _ _ _ _ _ _ _ B1'). }
    split. { unfold adebit. apply (art_wmlx_credit FSG BUDGET rn G LB cr msz r u n kb _ _ CRED Edep); [clear - Hmsz; lia|clear - AC1 HLk; lia|exact Hcost|exact AC2]. }
    split; [exact CLI'|]. split; [exact KN|]. split; [exact LZ'|exact EG']. }
  unfold amalloc_post in POST. rewrite <- HLsegs.
  apply (POST regs' M1 model' A' u P10).
  - apply art_kept_preserved; [rewrite P2, H2; reflexivity|exact PK].
  - exact ABR.
  - exact BA.
  - exact FFA.
  - exact DEFu.
  - exact SHu.
  - rewrite HLscr. exact AHP.
  - exact RT.
  - exact INC.
  - exact (bi_minv _ _ _ _ _ _ _ _ _ _ _ B1).
  - exact RI'.
Qed.
End Wrap.
