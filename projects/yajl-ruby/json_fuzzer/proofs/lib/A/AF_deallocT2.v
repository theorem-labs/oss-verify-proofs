(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import base decidable list gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr NodesCfg ZBridge InitMem.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import AImages AImageFacts ExecA LazyModel NodesA ImplRzA NodesA_mm NodesA_mmW SysStepA StepA StepA2 Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree StrFun.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import
  AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanHoare AsanPS AsanRep AsanKern AsanClient AsanWf1 AsanWf2 AsanWf3 AsanWf4 AsanWf5 AsanWf6 AsanWf9
  AsanBudget AsanBudget2 AsanDepot AsanRepFrame AsanRepFrame2 AsanHit AsanRepHit AsanRepCa AsanRepX AsanFrame AsanRepFlip AsanRealloc AsanRefillM.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import
  A_iface AF_place AF_fakestack_rep AF_kit AF_kit2 AF_poison AF_free_kit AF_qkit AF_free1 AF_free1b AF_free1e AF_free1c AF_free1d
  A_policy5 A_slack5 A_budget5 A_live A_bundle A_benv5 A_init5 A_instD5 A_balloc5 A_bpolicy5 A_rtok5 A_bevents5 A_bframe
  AF_alloc_iface AF_dput_iface AF_free_iface AF_refill_iface AF_tkit AF_ainv_kit AX_unreg AX_Exit AF_statics AF_caT AF_casT AF_refill_room AF_deallocT1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).
#[warnings="-notation-for-abbreviation"] Notation wz := (fun z : Z => Z_to_bv 64 z).

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import LiaA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac lia ::= LiaA.liaA.
Ltac pg := match goal with |- ?g => idtac "GOAL:"; idtac g end.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition dsame (s0 s : astate) : Prop :=
     as_regions s = as_regions s0 /\ as_cache_inited s = as_cache_inited s0 /\ as_cache s = as_cache s0 /\ as_cache_stale s = as_cache_stale s0
  /\ as_cache_allocated s = as_cache_allocated s0 /\ as_cache_mapped s = as_cache_mapped s0 /\ as_ptr_committed s = as_ptr_committed s0
  /\ as_sec s = as_sec s0 /\ as_sec_stale s = as_sec_stale s0 /\ as_sec_stats s = as_sec_stats s0 /\ as_glob_allocated s = as_glob_allocated s0
  /\ as_glob_mapped s = as_glob_mapped s0 /\ as_oom s = as_oom s0 /\ as_chunks s = as_chunks s0 /\ as_dead s = as_dead s0
  /\ as_tq s = as_tq s0 /\ as_gq s = as_gq s0 /\ as_ia_inited s = as_ia_inited s0 /\ as_residue s = as_residue s0
  /\ as_nprim_ever s = as_nprim_ever s0 /\ as_everc s = as_everc s0 /\ as_ts s = as_ts s0.

Lemma dsame_refl : forall s, dsame s s. Proof. intros s. repeat split; reflexivity. Qed.

Ltac ds_close := lazymatch goal with H : dsame _ ?s |- dsame _ _ => revert H; clear; unfold dsame; destruct s; cbn; intros H; exact H end.

Lemma call_mmap_ordie_dsame : forall E s0 len fl, presW (dsame s0) (call_mmap_ordie E len fl).
Proof. intros; unfold call_mmap_ordie. pw. Qed.
Lemma store_alloc_once_dsame : forall E s0 c, presW (dsame s0) (store_alloc_once E c).
Proof. intros; unfold store_alloc_once. pw; try apply call_mmap_ordie_dsame; ds_close. Qed.
Lemma store_alloc_dsame : forall E s0 c, presW (dsame s0) (store_alloc E c).
Proof. intros; unfold store_alloc. pw; try apply store_alloc_once_dsame. Qed.
Lemma depot_put_dsame : forall E s0 k, presW (dsame s0) (depot_put E k).
Proof. intros; unfold depot_put. pw; try apply call_mmap_ordie_dsame; try apply store_alloc_dsame; ds_close. Qed.

(* [comment removed for export] *)
Definition ndsame (s1 s : astate) : Prop := as_ndepot_ins s = as_ndepot_ins s1.
Ltac nd_close := lazymatch goal with H : ndsame _ ?s |- ndsame _ _ => revert H; clear; unfold ndsame; destruct s; cbn; intros H; exact H end.
Lemma call_mmap_ordie_nd : forall E s1 len fl, presW (ndsame s1) (call_mmap_ordie E len fl).
Proof. intros; unfold call_mmap_ordie. pw. Qed.
Lemma store_alloc_once_nd : forall E s1 c, presW (ndsame s1) (store_alloc_once E c).
Proof. intros; unfold store_alloc_once. pw; try apply call_mmap_ordie_nd; nd_close. Qed.
Lemma store_alloc_nd : forall E s1 c, presW (ndsame s1) (store_alloc E c).
Proof. intros; unfold store_alloc. pw; try apply store_alloc_once_nd. Qed.
Lemma depot_put_nd : forall E s0 k, hoareW (fun s => s = s0) (depot_put E k) (fun s' _ => as_ndepot_ins s' = as_ndepot_ins s0 + 1).
Proof.
  intros E s0 k. unfold depot_put. apply hoareW_get_bind. intros s ->. apply hoareW_upd_bind. apply hoareW_pre. intros s (sx & -> & ->).
  set (s1 := upd_ndepot (fun k0 => k0 + 1) s0).
  apply (hoareW_conseq (ndsame s1) (fun s' => s' = s1) _ (fun s _ => ndsame s1 s));
    [| intros s ->; reflexivity| intros s r H; unfold ndsame in H; rewrite H; subst s1; destruct s0; reflexivity].
  lazymatch goal with |- hoareW ?I ?m _ => change (presW I m) end.
  pw; try apply call_mmap_ordie_nd; try apply store_alloc_nd; try nd_close.
Qed.

(* [comment removed for export] *)
Lemma img_depsep_asan : forall E, ae_ic E = asan_ic ->
  forall x y, In x (arep_img_ranges E) -> In y (depot_static E) -> fst x + snd x <= fst y \/ fst y + snd y <= fst x.
Proof.
  intros E IC x y Hx Hy. unfold arep_img_ranges, ae_instance in Hx. unfold depot_static in Hy. rewrite IC in Hx, Hy.
  cbn -[Z.add Z.le In] in Hx, Hy.
  destruct Hy as [<-|[<-|[]]]; cbn [fst snd]; repeat (destruct Hx as [<-|Hx]; [cbn [fst snd]; lia|]); destruct Hx.
Qed.

(* [comment removed for export] *)
Section DeallocT2.
Variable E0 : aenv.
Variable FSB0 : Z.
Variable HR0 : list (Z * Z).
Variables L0 RES0 : list (word * word).
Variable EB0 : Z.
Variable PL0 : fs_plumb.
Hypothesis HR0_ok : Forall (fun iv => fst iv <= snd iv) HR0 /\ A0_pages HR0 <= 8192.
Hypothesis EB0_ok : 0 <= EB0 <= 2^32.
Hypothesis ENV_depot : zlen (ae_keys0 E0) <= 1000 /\ 0 <= ae_frames0 E0 <= 4096.
Hypothesis ENV0 : env0_ok5 E0.
Hypothesis PL0OK : pl0_ok5 E0 PL0.
Hypothesis L0OK : l0_ok5 E0 L0 RES0.
(* [comment removed for export] *)
Hypothesis DPUT : depot_put_srz_stmt E0 FSB0 HR0 L0 RES0 EB0.
Hypothesis REFILL : refill_srz_stmt E0 FSB0 HR0 L0 RES0 EB0 PL0.

#[local] Notation RTOKc := (RTOK E0 FSB0 HR0 L0 RES0 EB0).
#[local] Notation ATOKc := (ATOK E0 FSB0 HR0 L0 RES0 EB0).
#[local] Notation AINVc := (AINV E0 FSB0 PL0).
#[local] Notation aSc := (A_bundle.aS E0 FSB0 HR0).
#[local] Notation aNc := (A_bundle.aN E0 FSB0 HR0).
#[local] Notation aEBc := (A_bundle.aEB EB0).
#[local] Notation SB := (ae_space_beg E0).
#[local] Notation T := (ae_thread E0).
#[local] Notation CTX := (fp_ctx PL0).
#[local] Notation INST := 0xaa518.
#[local] Notation PP := (AF_deallocT1.PP E0 FSB0 HR0).
#[local] Notation FPW1 := (AF_deallocT1.FPW1 E0).
#[local] Notation W15 := (AF_deallocT1.W15 E0).
#[local] Notation QPF_post := (AF_deallocT1.QPF_post E0 FSB0 HR0 L0 RES0 EB0).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma flip_rep : forall (s : aps) (mo mo5 : Model) (m m5 : mem) (a2 : astate) (cm : chunkmeta) (b1 aid fid lo usp cb : Z) (key : list Z),
  let a := aps_alloc s in let n := cm_n cm in let l8 := (n + 7) / 8 in let SHa := kShadowBase + (cb + 16) / 8 in
  AINVc a m mo -> ENVOK E0 FSB0 s ->
  as_chunks a !! cb = Some cm -> cm_state cm = CAllocated aid -> cm_user_beg cm = cb + 16 -> Z.land b1 127 = kHeaderByte1 ->
  (exists fuel orc evs orc', arun fuel (depot_put E0 key (upd_ts (ts_on_free n) a)) orc = Some (a2, ONorm fid, evs, orc')) ->
  1 <= fid -> AWf E0 [] [] a2 -> AKern E0 a2 mo5 -> alloc_ceiling <= lo ->
  wmono asegs m m5 -> (forall z, 0 <= z < 2^64 -> ~ FPW1 a2 lo usp cb n z -> m5 (wa z) = m (wa z)) ->
  DepotR asegs E0 a2 m5 ->
  rw_cells asegs m5 cb [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (wz (n / 2^32)); C4 (wz n); C8 (wz aid)] ->
  rw_cells asegs m5 (cb + 16) [C8 (wz fid)] ->
  rw_cells asegs m5 (T + 2824) [C8 (wz (ts_frees (as_ts a) + 1)); C8 (wz (ts_freed (as_ts a) + n))] ->
  rw_cells asegs m5 SHa [CB (Z.to_nat l8) (repeat (Z_to_bv 8 0xfd) (Z.to_nat l8))] ->
  ARep asegs E0 (DepotR asegs E0) (s3 a2 cb cm aid fid) m5.
Proof.
  intros until key. cbv zeta. intros AIV ENV Hcm ST UB HB1 RUN FID WF2 AK2 LOC WM AG DR HDR FIDc STc SHc.
  pose proof AIV as (Hrep & Hwf & Hkern & Hres & Hqb & Hdi & Hbinv & Hmi & Hrt & Hss & Hcs).
  set (a := aps_alloc s) in *.
  pose proof ENV0 as ENV0'. destruct ENV0' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IMGR & _ & _ & _ & _ & _ & IC0 & TDN & DNP).
  pose proof ENV as ENV'. destruct ENV' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & EE & EFS & [EI1 EI2]). rewrite EE in EI1, EI2.
  pose proof RUN as (fuel & orc & evs & orc' & RUNe).
  pose proof (hoareW_arun _ _ _ _ _ _ _ _ _ _ (depot_put_dsame E0 (upd_ts (ts_on_free (cm_n cm)) a) key) (dsame_refl _) RUNe)
    as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14 & D15 & D16 & D17 & D18 & D19 & D20 & D21 & D22).
  destruct PL0OK as (_ & _ & (TR1 & TR2 & _) & _). pose proof TR2 as (Tlo & Thi & Timg & Tband). unfold A_IMG_END, A_LOWAPP_END, A_HIGH_BEG in Timg, Tband.
  assert (RU8 : round_up (cm_n cm) 8 / 8 = (cm_n cm + 7) / 8) by (unfold round_up; clear; rewrite Z.div_mul by lia; f_equal; lia).
  apply (ARep_after_flip asegs E0 a a2 m m5 lo cb cm aid fid b1);
    [ exact D1 | exact D2 | exact D3 | exact D4 | exact D5 | exact D6 | exact D7 | exact D8 | exact D9 | exact D10 | exact D11
    | exact D12 | exact D13 | exact D14 | exact D15 | exact D16 | exact D17 | exact D18 | exact D19 | exact D20 | exact D21 | exact D22
    | exact Hcm | exact ST | exact HB1 | exact WM
    | (* [comment removed for export] *)
      intros z Z0 NF; apply AG; [exact Z0|]; intros F1; apply NF; unfold AF_deallocT1.FPW1 in F1; unfold FPWflip; rewrite UB, RU8; unfold kThrStats;
      clear -F1; decompose [or] F1; [left| right; left| do 2 right; left| do 2 right; left| do 3 right; left| do 4 right]; try assumption; lia
    | exact LOC | exact Hrep | exact Hwf | exact (blocks_sep_of E0 a mo ENV0 Hwf Hkern)
    | clear -Tlo Thi Timg; repeat split; lia
    | intros r Hr; pose proof (IMGR r Hr) as X; rewrite EI1; clear -X EI2; lia
    | rewrite EI1; clear; lia
    | exact IMGR
    | exact (img_depsep_asan E0 IC0)
    | exists mo; exact Hkern | exists mo5; exact AK2 | exact TDN | exact DR
    | exact HDR
    | rewrite UB; exact FIDc
    | unfold kThrStats; replace (T + 2800 + 24) with (T + 2824) by (clear; lia); exact STc
    | rewrite UB, RU8; exact SHc
    | exact WF2 | exact DNP | exact FID ].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma dfp_not_rt : forall (a : astate) mo z,
  AKern E0 a mo -> AWf E0 [] [] a -> fst (ae_img E0) = 0x10000 -> 0x5f3000 <= snd (ae_img E0) ->
  DepotFPd E0 a z -> rt_fpc E0 FSB0 PL0 z -> False.
Proof.
  intros a mo z K WF EI1 EI2 D RT. pose proof ceil_range as CR. 
  pose proof ENV0 as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & _ & _ & _ & _ & _ & _ & IC0 & TDN & DNP).
  pose proof PL0OK as ((c0 & cl & CR0 & CC1 & CC2) & (d0 & dl & DR0 & DD1 & DD2) & TR & CT & DT & CD & CIA).
  pose proof TR as (TR1 & TR2 & TR3 & TR4 & TR5 & TR6 & TR7 & TR8). pose proof TR2 as (Tlo & Thi & Timg & Tband). unfold A_IMG_END, A_LOWAPP_END, A_HIGH_BEG in Timg, Tband.
  pose proof CR0 as (CI & CP & _ & _ & _ & CS & _ & CN). pose proof DR0 as (DI & DP & _ & _ & _ & DS & _ & DN).
  pose proof (resv_range_num E0 c0 cl CR0 ltac:(clear -CC1 CC2; lia)) as (CQ1 & CQ2 & CQ3 & CQ4).
  pose proof (resv_range_num E0 d0 dl DR0 ltac:(clear -DD1 DD2; lia)) as (DQ1 & DQ2 & DQ3 & DQ4).
  destruct (rt_fpc_where2 E0 FSB0 PL0 z RT) as [[ZI NM]|RH].
  - (* [comment removed for export] *)
    destruct (dfp_cases E0 PL0 ENV0 PL0OK a mo z IC0 K WF EI1 EI2 D) as [ST|(b & bl & R & B0 & _)]; [| clear -ZI R B0; lia].
    apply NM. unfold in_cells, img_mut. cbn [aic_instance aic_internal_alloc_initialized aic_internal_allocator_instance aic_theDepot aic_stackStore asan_ic c_errno ACONSTS].
    destruct (Z_lt_dec z 0x18fa58).
    + exists (0x17fa48, 0x10010). split; [do 4 right; left; reflexivity| cbn [fst snd]; clear -ST l; lia].
    + exists (0x18fa58, 0x440010). split; [do 3 right; left; reflexivity| cbn [fst snd]; clear -ST n; lia].
  - (* [comment removed for export] *)
    unfold rt_high2 in RH.
    pose proof WF as (WE & _ & _ & _ & _ & WS & _).
    pose proof (wf_env_thread _ WE) as (WT1 & _). pose proof (wf_env_iarena _ WE) as (WI1 & _).
    destruct D as [ST|[(b & Hb & R)|(b & Hb & R)]]; change kDepotNodeBlockBytes with 1048576 in *; change kStoreBlockBytes with 8388608 in *.
    + destruct ST as (r & Hr & R). rewrite IC0 in Hr. cbn [aic_theDepot aic_stackStore asan_ic] in Hr.
      unfold kDepotStaticBytes, kStoreStaticBytes in Hr. destruct Hr as [<-|[<-|[]]]; cbn [fst snd] in R; clear -R RH Timg CQ3 DQ3 CC1 CC2 DD1 DD2; lia.
    + unfold node_blocks in Hb. destruct Hb as [<-|Hb].
      * clear -R RH TDN CN DN CC1 CC2 DD1 DD2. lia.
      * destruct (ak_blocks_sep _ _ _ K b 1048576 (or_introl (conj Hb eq_refl))) as (_ & _ & _ & _ & _ & B5).
        pose proof (B5 _ WT1) as BT. pose proof (B5 _ CI) as BC. pose proof (B5 _ DI) as BD. cbn [fst snd] in BT, BC, BD.
        clear -R RH BT BC BD CC1 CC2 DD1 DD2. lia.
    + unfold store_blocks in Hb. destruct Hb as [<-|Hb].
      * pose proof (ak_store_sep _ _ _ K) as (_ & _ & S3 & _). change kPageSize with 4096 in S3. clear -R RH S3 CS DS CC1 CC2 DD1 DD2. lia.
      * destruct (ak_blocks_sep _ _ _ K b 8388608 (or_intror (conj Hb eq_refl))) as (_ & _ & _ & _ & _ & B5).
        pose proof (B5 _ WT1) as BT. pose proof (B5 _ CI) as BC. pose proof (B5 _ DI) as BD. cbn [fst snd] in BT, BC, BD.
        clear -R RH BT BC BD CC1 CC2 DD1 DD2. lia.
Qed.

Lemma rt_misc5_cut2 : forall (a a2 : astate) (mo mo2 : Model) (m m5 : mem) (lo usp cb n : Z),
  rt_misc5 FSB0 PL0 E0 m -> AWf E0 [] [] a -> AKern E0 a mo -> AWf E0 [] [] a2 -> AKern E0 a2 mo2 ->
  fst (ae_img E0) = 0x10000 -> 0x5f3000 <= snd (ae_img E0) -> alloc_ceiling <= lo ->
  0x603000 <= cb -> cb + 16 + rounded n <= alloc_ceiling ->
  (cb + 16 + rounded n <= T \/ T + 4096 <= cb) -> (cb + 16 + rounded n <= ae_iarena E0 \/ ae_iarena E0 + kIArenaLen <= cb) ->
  ((exists c, 1 <= c <= kLargestClassID /\ region_beg SB c <= cb /\ cb + 16 + rounded n <= region_beg SB c + rg_mapped_user (get_region a c))
   \/ (exists sc, In sc (as_sec a) /\ sc_map_beg sc <= cb /\ cb + 16 + rounded n <= sc_map_beg sc + sc_map_size sc)) ->
  (forall z, 0 <= z < 2^64 -> ~ FPW1 a2 lo usp cb n z -> m5 (wa z) = m (wa z)) ->
  rt_misc5 FSB0 PL0 E0 m5.
Proof.
  intros a a2 mo mo2 m m5 lo usp cb n RT WF K WF2 K2 EI1 EI2 LOC CB0 CBC CBT CBI CBLOC AG. pose proof ceil_range as CR.
  pose proof PL0OK as ((c0 & cl & CR0 & CC1 & CC2) & (d0 & dl & DR0 & DD1 & DD2) & TR & CT & DT & CD & CIA).
  pose proof TR as (TR1 & TR2 & _). pose proof TR2 as (Tlo & Thi & Timg & Tband). unfold A_IMG_END, A_LOWAPP_END, A_HIGH_BEG in Timg, Tband.
  pose proof CR0 as (CI & _ & _ & CRS & _). pose proof DR0 as (DI & _ & _ & DRS & _).
  pose proof (resv_range_num E0 c0 cl CR0 ltac:(clear -CC1 CC2; lia)) as (CQ1 & CQ2 & CQ3 & CQ4).
  pose proof (resv_range_num E0 d0 dl DR0 ltac:(clear -DD1 DD2; lia)) as (DQ1 & DQ2 & DQ3 & DQ4).
  pose proof (rounded_ge n) as (RG1 & RG2 & RG3).
  pose proof WF as (WE & WR & _ & _ & _ & WS & _). destruct WS as (_ & _ & WS3 & _).
  pose proof (ak_resv_geom _ _ _ K) as (G1 & G2 & G3). change kSpaceSize with 137438953472 in G3. change kPageSize with 4096 in G3. change kResvLen with 137439023104 in G3, CRS, DRS.
  unfold kIArenaLen in CBI, CIA.
  (* [comment removed for export] *)
  assert (CBD : cb + 24 <= fp_dtls PL0 \/ fp_dtls PL0 + 4096 <= cb).
  { destruct CBLOC as [(c & Hc & L1 & L2)|(sc & Hsc & L1 & L2)].
    - unfold region_beg in L1, L2. destruct (proj2 WR c Hc) as (R1 & R2 & R3 & _). cbv zeta in R1, R3. unfold region_of in R1, R3.
      change kRegionSize with 4294967296 in L1, L2. change kFreeArrayOffset with 3758096384 in R3. unfold kLargestClassID in Hc.
      clear -L1 L2 Hc R1 R3 G1 G3 DRS DD1 DD2 RG1. nia.
    - destruct (WS3 sc Hsc) as (_ & _ & _ & _ & _ & _ & RSV). pose proof (RSV _ DI) as X. cbn [fst snd] in X. clear -X L1 L2 DD1 DD2 RG1. lia. }
  apply (rt_misc5_agree E0 FSB0 PL0 m m5 RT). intros z Hz.
  destruct (rt_fpc_where2 E0 FSB0 PL0 z Hz) as [[ZI NM]|RH].
  - apply AG; [clear -ZI; lia|]. intros F. unfold AF_deallocT1.FPW1 in F. unfold kShadowBase in F.
    destruct F as [F|[F|F]]; [clear -F ZI LOC CR; lia| exact (dfp_not_rt a2 mo2 z K2 WF2 EI1 EI2 F Hz)| clear -F ZI CB0 Timg Tlo; lia].
  - apply AG; [unfold rt_high2 in RH; clear -RH Tlo Thi CQ1 CQ2 CC1 CC2 DQ1 DQ2 DD1 DD2 CR; lia|]. intros F. unfold AF_deallocT1.FPW1 in F. unfold kShadowBase in F.
    destruct F as [F|[F|F]]; [unfold rt_high2 in RH; clear -F RH LOC Thi CQ2 CC2 DQ2 DD2; lia| exact (dfp_not_rt a2 mo2 z K2 WF2 EI1 EI2 F Hz)|].
    unfold rt_high2 in RH. destruct F as [F|[F|[F|F]]].
    + clear -F RH CBT CBI CIA CBD CC1 CC2 RG1. lia.
    + clear -F RH CBT CBI CIA CBD CC1 CC2 RG1. lia.
    + clear -F RH CT DT. lia.
    + clear -F RH Tband CQ4 CC1 CC2 DQ4 DD1 DD2 RG1 CR CB0 CBC. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma blocks_sep_ext : forall E (sx sy : astate), as_node_blocks sy = as_node_blocks sx -> as_store_blocks sy = as_store_blocks sx -> as_sec sy = as_sec sx ->
  blocks_sep E sx -> blocks_sep E sy.
Proof. intros E sx sy H1 H2 H3 B. unfold blocks_sep in *. rewrite H1, H2, H3. exact B. Qed.

(* [comment removed for export] *)
Lemma list_last_snoc : forall l b, list_last (l ++ [b]) = b_addr b.
Proof.
  intros l b. unfold list_last. rewrite (List.last_last l b (mkBatch 0 [] 0)). destruct l; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma arep_batch_list_snoc : forall sx l b m, arep_batch_list asegs sx (l ++ [b]) m -> arep_batch asegs sx b 0 m.
Proof.
  intros sx l b m. induction l as [|b0 l IH]; intros H.
  - cbn in H. exact (proj1 H).
  - cbn [app arep_batch_list] in H. exact (IH (proj2 H)).
Qed.

(* [comment removed for export] *)
Lemma enq_cells : forall (ax : astate) (m : mem) (P : list Z),
  ARep asegs E0 (DepotR asegs E0) ax m -> AWf E0 P [] ax -> ae_ic E0 = asan_ic ->
  let tq := as_tq ax in let l24 := get_cache ax kBatchClass in let ci := as_cache_inited ax in
  exists junk24,
     rw_cells asegs m (T + 80) [C8 (wz (qcount tq)); C8 (wz (list_first tq)); C8 (wz (list_last tq)); C8 (wz (tq_bytes ax))]
  /\ rw_cells asegs m (T + 2128) [C4 (wz (zlen l24)); C4 (wz (if ci then max_count kBatchClass else 0)); C8 (wz (if ci then 8192 else 0))]
  /\ u32arr asegs m (T + 2144) (map (fun z : Z => wz z) l24 ++ junk24) /\ (length l24 + length junk24 = 16)%nat
  /\ rw_cells asegs m (T + 2784) [C8 (wz (as_cache_allocated ax))]
  /\ rw_cells asegs m 0xaa538 [C8 (wz SB); C4 (wz 0xffffffff); C4 (wz 0); C8 (wz (ae_region_info E0))]
  /\ (forall l b, tq = l ++ [b] ->
        list_last tq = b_addr b /\ 1 <= qcount tq
        /\ rw_cells asegs m (b_addr b) [C8 (wz 0); C8 (wz (b_size b)); C8 (wz (zlen (b_items b)))]
        /\ (exists junkb, u64arr asegs m (b_addr b + 24) (map (fun cb => wz cb) (b_items b) ++ junkb) /\ (length (b_items b) + length junkb = 1021)%nat)
        /\ wf_batch E0 [] ax b /\ 1 <= zlen (b_items b)).
Proof.
  intros ax m P REP WF IC0. cbv zeta.
  pose proof REP as (Rins & Rri & Rrm & Rthr & Rsec & Rch & Rbat & Rdep & Rglob & Rsh).
  pose proof Rthr as (Ttop & T40 & Tq & Tcache & Tcst & Tst & Tby & Tunw).
  destruct (Tcache kBatchClass ltac:(unfold kBatchClass, kNumClasses; clear; lia)) as [PCR (junk24 & CARR & CLEN)].
  exists junk24.
  split; [unfold kThrQCache in Tq; exact Tq|].
  split. { unfold percls_cells, kThrCache, kPerClassSize, kBatchClass in PCR |- *. replace (T + 208 + 80 * 24) with (T + 2128) in PCR by (clear; lia).
           change (class_size 24) with 8192 in PCR. exact PCR. }
  split. { unfold kThrCache, kPerClassSize, kBatchClass in CARR |- *. replace (T + 208 + 80 * 24 + 16) with (T + 2144) in CARR by (clear; lia). exact CARR. }
  split; [exact CLEN|].
  split. { unfold kThrCacheStats in Tcst. apply (rwc_split asegs m _ [C8 (wz (as_cache_allocated ax))] [C8 (wz (as_cache_mapped ax))]) in Tcst.
           replace (T + (208 + 2560) + 16) with (T + 2784) in Tcst by (clear; lia). exact (proj1 Tcst). }
  split. { pose proof Rins as (Iin & _). unfold ae_instance in Iin. rewrite IC0 in Iin. cbn [aic_instance asan_ic kInsSpaceBeg Z.add] in Iin.
           apply (rwc_split asegs m _ [C8 (wz SB); C4 (wz 4294967295); C4 (wz 0); C8 (wz (ae_region_info E0))] [C1 (Z_to_bv 8 0)]) in Iin.
           exact (proj1 Iin). }
  intros l b Htq.
  assert (INb : In b (as_tq ax ++ as_gq ax)) by (rewrite Htq; apply in_app_iff; left; apply in_app_iff; right; left; reflexivity).
  pose proof WF as (_ & _ & _ & _ & (Q1 & _) & _). destruct (Q1 b INb) as [WB B1].
  split. { unfold list_last. rewrite Htq. destruct (l ++ [b]) eqn:E; [destruct l; discriminate| rewrite <- E, last_last; reflexivity]. }
  split. { unfold qcount. rewrite Htq, length_app. cbn [length]. clear; lia. }
  destruct Rbat as [RBt _]. rewrite Htq in RBt. destruct (arep_batch_list_snoc ax l b m RBt) as [HB (junkb & HI & HL)].
  split; [exact HB|]. split; [exists junkb; split; [exact HI| exact HL]|]. split; [exact WB| exact B1].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma cut2_model : forall (s : aps) (mo mo5 : Model) (m m5 : mem) (a2 : astate) (cm : chunkmeta) (aid fid cb C C' : Z) (key : list Z),
  let a := aps_alloc s in let n := cm_n cm in let a3 := s3 a2 cb cm aid fid in
  AINVc a m mo ->
  as_chunks a !! cb = Some cm -> cm_state cm = CAllocated aid ->
  (exists fuel orc evs orc', arun fuel (depot_put E0 key (upd_ts (ts_on_free n) a)) orc = Some (a2, ONorm fid, evs, orc')) ->
  1 <= fid -> AWf E0 [] [] a2 -> AKern E0 a2 mo5 -> RTOKc (C - 1) (C' - DSLACK) (sA a2 s) mo5 -> DepotR asegs E0 a2 m5 ->
     AWf E0 [cb] [] a3 /\ pending a3 cb n /\ AKern E0 a3 mo5 /\ RTOKc (C - 1) (C' - DSLACK) (sA a3 s) mo5
  /\ as_chunks a3 !! cb = Some (flipped cm aid fid) /\ (forall cb', cb' <> cb -> as_chunks a3 !! cb' = as_chunks a !! cb')
  /\ as_tq a3 = as_tq a /\ as_gq a3 = as_gq a /\ as_cache a3 = as_cache a /\ as_cache_inited a3 = as_cache_inited a
  /\ as_cache_allocated a3 = as_cache_allocated a /\ as_regions a3 = as_regions a /\ as_sec a3 = as_sec a
  /\ as_nprim_ever a3 = as_nprim_ever a /\ as_residue a3 = as_residue a /\ as_ndepot_ins a2 = as_ndepot_ins a + 1
  /\ as_ndepot_ins a3 = as_ndepot_ins a2 /\ as_ts a3 = ts_on_free n (as_ts a)
  /\ res_ok a3 /\ AQbound a3 /\ depot_inv E0 a3 /\ sstats_ok a3 /\ csmall a3
  /\ same_fp a2 a3 /\ dsame (upd_ts (ts_on_free n) a) a2.
Proof.
  intros until key. cbv zeta. intros AIV Hcm ST RUN FID WF2 AK2 TOK2 DR.
  pose proof AIV as (Hrep & Hwf & Hkern & Hres & Hqb & Hdi & Hbinv & Hmi & Hrt & Hss & Hcs).
  set (a := aps_alloc s) in *.
  pose proof RUN as (fuel & orc & evs & orc' & RUNe).
  pose proof (hoareW_arun _ _ _ _ _ _ _ _ _ _ (depot_put_dsame E0 (upd_ts (ts_on_free (cm_n cm)) a) key) (dsame_refl _) RUNe) as DS.
  pose proof DS as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14 & D15 & D16 & D17 & D18 & D19 & D20 & D21 & D22).
  cbn [as_regions as_cache_inited as_cache as_cache_stale as_cache_allocated as_cache_mapped as_ptr_committed as_sec as_sec_stale as_sec_stats
       as_glob_allocated as_glob_mapped as_oom as_chunks as_dead as_tq as_gq as_ia_inited as_residue as_nprim_ever as_everc as_ts upd_ts]
    in D1, D2, D3, D4, D5, D6, D7, D8, D9, D10, D11, D12, D13, D14, D15, D16, D17, D18, D19, D20, D21, D22.
  assert (Hcm2 : as_chunks a2 !! cb = Some cm) by (rewrite D14; exact Hcm).
  destruct (AWf_flip E0 [] a2 cb cm aid fid WF2 Hcm2 ST FID) as [WF3 NIB].
  (* [comment removed for export] *)
  pose proof (hoareW_arun _ _ _ _ _ _ _ _ _ _ (depot_put_nd E0 (upd_ts (ts_on_free (cm_n cm)) a) key) eq_refl RUNe) as ND2. cbn [as_ndepot_ins upd_ts] in ND2.
  assert (PEND : pending (s3 a2 cb cm aid fid) cb (cm_n cm)).
  { split.
    - exists (flipped cm aid fid), aid, fid. split; [unfold s3; cbn [as_chunks upd_chunks]; apply lookup_insert_eq| split; reflexivity].
    - intros b Hb. apply NIB. revert Hb. unfold s3. destruct a2; cbn; exact (fun H => H). }
  assert (DI3 : depot_inv E0 (s3 a2 cb cm aid fid)).
  { destruct DR as [DI _]. revert DI. unfold s3. clear. unfold depot_inv, depot_n_ids, dphi. destruct a2; cbn; exact (fun H => H). }
  split; [exact WF3|]. split; [exact PEND|].
  split; [apply (AKern_ext E0 a2); [reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| exact AK2]|].
  split; [eapply (RTOK_same_fp E0 FSB0 HR0 L0 RES0 EB0); [exact TOK2| repeat split; reflexivity| reflexivity| reflexivity]|].
  split; [unfold s3; cbn [as_chunks upd_chunks]; apply lookup_insert_eq|].
  split; [intros cb' NE; unfold s3; cbn [as_chunks upd_chunks]; rewrite lookup_insert_ne by (clear -NE; congruence); rewrite D14; reflexivity|].
  unfold s3; cbn [as_tq as_gq as_cache as_cache_inited as_cache_allocated as_regions as_sec as_nprim_ever as_residue as_ndepot_ins as_ts upd_chunks].
  split; [exact D16|]. split; [exact D17|]. split; [exact D3|]. split; [exact D2|]. split; [exact D5|]. split; [exact D1|]. split; [exact D8|].
  split; [exact D20|]. split; [exact D19|]. split; [exact ND2|]. split; [reflexivity|]. split; [exact D22|].
  split. { apply (res_ok_frame a); [| | exact Hres]; cbn; [intros sc H; rewrite <- D8; exact H| rewrite D19; apply incl_refl]. }
  split. { apply (AQbound_tg a); cbn; [exact D16| exact D17| exact Hqb]. }
  split; [exact DI3|].
  split. { revert Hss. unfold sstats_ok, sec_bytes, s3. cbn [as_sec_stats as_sec upd_chunks]. rewrite D10, D8. exact (fun H => H). }
  split. { intros cb' cm' H'. unfold s3 in H'. cbn [as_chunks upd_chunks] in H'. destruct (Z.eq_dec cb' cb) as [->|NE].
           - rewrite lookup_insert_eq in H'. injection H' as <-. cbn. exact (Hcs _ _ Hcm).
           - rewrite lookup_insert_ne in H' by (clear -NE; congruence). rewrite D14 in H'. exact (Hcs _ _ H'). }
  split; [repeat split; reflexivity| exact DS].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition enq1_st (a : astate) (l : list batch) (b : batch) (cb n : Z) : astate :=
  upd_tq (fun _ => l ++ [mkBatch (b_addr b) (b_items b ++ [cb]) (b_size b + n)]) a.
Definition bpop_st (a : astate) : astate :=
  let c := kBatchClass in let l := get_cache a c in let x := List.last l 0 in let i := Z.of_nat (Nat.pred (length l)) in
  upd_cache_allocated (fun al => al + class_size c)
    (upd_cache_stale (fun st => <[c := <[i := x]> (match st !! c with Some mm => mm | None => ∅ end)]> st)
       (set_cache c (removelast l) a)).
Definition bnew (a : astate) : Z := chunk_of_compact SB kBatchClass (List.last (get_cache a kBatchClass) 0).
Definition enq2_st (a : astate) (cb n : Z) : astate :=
  upd_tq (fun t => t ++ [mkBatch (bnew a) [cb] (kBatchSize + n)]) (bpop_st a).

(* [comment removed for export] *)
Definition renv_ok (a : astate) : Prop :=
     blocks_sep E0 a
  /\ ((0x1000 <= T /\ (T + 4096 <= 0x10000 \/ 0x603000 <= T)) /\ T + 4096 <= alloc_ceiling)
  /\ (forall r, In r (arep_img_ranges E0 ++ depot_static E0) -> fst (ae_img E0) <= fst r /\ fst r + snd r <= fst (ae_img E0) + snd (ae_img E0))
  /\ 0x10000 <= fst (ae_img E0)
  /\ (forall r, In r (arep_img_ranges E0 ++ depot_static E0) -> 0x10000 <= fst r /\ fst r + snd r <= 0x603000)
  /\ (forall x y, In x (arep_img_ranges E0) -> In y (depot_static E0) -> fst x + snd x <= fst y \/ fst y + snd y <= fst x)
  /\ (exists mo, AKern E0 a mo)
  /\ (T + 4096 <= ae_depot_nodes E0 \/ ae_depot_nodes E0 + kDepotNodeBlockBytes <= T)
  /\ (ae_depot_nodes E0 + kDepotNodeBlockBytes <= ae_ptr_array E0 \/ ae_ptr_array E0 + kPtrArrayLen <= ae_depot_nodes E0).

(* [comment removed for export] *)
Definition FPWe1 (lo ba bcnt : Z) (z : Z) : Prop :=
  lo <= z \/ (ba + 8 <= z < ba + 24) \/ (ba + 24 + 8 * bcnt <= z < ba + 24 + 8 * bcnt + 8) \/ (T + kThrQCache + 24 <= z < T + kThrQCache + 32).
Definition R2F1_stmt : Prop :=
  forall (a : astate) (m m' : mem) (lo cb n : Z) (l : list batch) (b : batch) (P : list Z),
  let bcnt := zlen (b_items b) in
  as_tq a = l ++ [b] -> bcnt < kBatchCap -> pending a cb n ->
  ARep asegs E0 (DepotR asegs E0) a m -> AWf E0 (cb :: P) [] a -> renv_ok a ->
  wmono asegs m m' -> (forall z, 0 <= z < 2^64 -> ~ FPWe1 lo (b_addr b) bcnt z -> m' (wa z) = m (wa z)) -> alloc_ceiling <= lo ->
  rw_cells asegs m' (T + kThrQCache + 24) [C8 (wz (tq_bytes a + n))] ->
  rw_cells asegs m' (b_addr b + 8) [C8 (wz (b_size b + n)); C8 (wz (bcnt + 1))] ->
  rw_cells asegs m' (b_addr b + 24 + 8 * bcnt) [C8 (wz cb)] ->
  ARep asegs E0 (DepotR asegs E0) (enq1_st a l b cb n) m'.

(* [comment removed for export] *)
Definition FPWe2 (a : astate) (lo nb : Z) (z : Z) : Prop :=
     lo <= z \/ (T + kThrQCache <= z < T + kThrQCache + 32)
  \/ (T + kThrCache + kPerClassSize * kBatchClass <= z < T + kThrCache + kPerClassSize * kBatchClass + 4)
  \/ (T + kThrCacheStats + 16 <= z < T + kThrCacheStats + 24)
  \/ (nb <= z < nb + 32)
  \/ (as_tq a <> [] /\ list_last (as_tq a) <= z < list_last (as_tq a) + 8).
     (* [comment removed for export] *)
Definition R2F2_stmt : Prop :=
  forall (a : astate) (m m' : mem) (lo cb n : Z) (P : list Z) (junk : list word),
  let l := get_cache a kBatchClass in let nb := bnew a in let tq := as_tq a in
  l <> [] -> as_cache_inited a = true -> pending a cb n ->
  ARep asegs E0 (DepotR asegs E0) a m -> AWf E0 (cb :: P) [] a -> renv_ok a ->
  wmono asegs m m' -> (forall z, 0 <= z < 2^64 -> ~ FPWe2 a lo nb z -> m' (wa z) = m (wa z)) -> alloc_ceiling <= lo ->
  rw_cells asegs m' (T + kThrQCache)
    [C8 (wz (qcount tq + 1)); C8 (wz (match tq with [] => nb | _ => list_first tq end)); C8 (wz nb); C8 (wz (tq_bytes a + (n + kBatchSize)))] ->
  rw_cells asegs m' (T + kThrCache + kPerClassSize * kBatchClass) [C4 (wz (zlen l - 1))] ->
  rw_cells asegs m' (T + kThrCacheStats + 16) [C8 (wz (as_cache_allocated a + class_size kBatchClass))] ->
  rw_cells asegs m' nb [C8 (wz 0); C8 (wz (n + kBatchSize)); C8 (wz 1)] ->
  u64arr asegs m' (nb + 24) (wz cb :: junk) -> length junk = 1020%nat ->
  (forall l0 b0, tq = l0 ++ [b0] -> rw_cells asegs m' (b_addr b0) [C8 (wz nb)]) ->
  ARep asegs E0 (DepotR asegs E0) (enq2_st a cb n) m'.

Hypothesis R2F1 : R2F1_stmt.
Hypothesis R2F2 : R2F2_stmt.

Lemma snoc_case : forall {A} (l : list A), l = [] \/ exists l' x, l = l' ++ [x].
Proof.
  intros A l. induction l as [|y l IH]; [left; reflexivity| right].
  destruct IH as [->|(l' & x & ->)]; [exists [], y; reflexivity| exists (y :: l'), x; reflexivity].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma tq_weights : forall E P D sx l b, AWf E P D sx -> as_tq sx = l ++ [b] ->
  kBatchSize <= b_size b /\ b_size b <= tq_bytes sx /\ 0 <= qbytes l /\ kBatchSize * qcount (as_tq sx) <= tq_bytes sx /\ tq_bytes sx = qbytes l + b_size b.
Proof.
  intros E P D sx l b WF Htq.
  pose proof (qbytes_ge E P D sx [b] WF ltac:(intros x [<-|[]]; rewrite Htq; apply in_app_iff; left; apply in_app_iff; right; left; reflexivity)) as B1.
  pose proof (qbytes_ge E P D sx l WF ltac:(intros x Hx; rewrite Htq; apply in_app_iff; left; apply in_app_iff; left; exact Hx)) as B2.
  pose proof (qbytes_ge E P D sx (as_tq sx) WF ltac:(intros x Hx; apply in_app_iff; left; exact Hx)) as B3.
  unfold tq_bytes. rewrite Htq in B3 |- *. rewrite qbytes_app in *. unfold zlen, qcount in *. cbn [qbytes fold_right length] in *.
  unfold kBatchSize in *. repeat split; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma live_block_other : forall E P D sx cb cm blo bsz, AWf E P D sx -> as_chunks sx !! cb = Some cm ->
  In (blo, bsz) (live_blocks sx) -> (blo, bsz) <> (cm_user_beg cm, cm_n cm) ->
  exists cb' cm' i, as_chunks sx !! cb' = Some cm' /\ cb' <> cb /\ cm_user_beg cm' = blo /\ cm_n cm' = bsz /\ cm_state cm' = CAllocated i.
Proof.
  intros E P D sx cb cm blo bsz WF Hcm Hin NE. unfold live_blocks, chunk_list in Hin.
  apply in_map_iff in Hin. destruct Hin as ([k cm'] & E1 & Hin). cbn in E1. injection E1 as E2 E3.
  apply filter_In in Hin. destruct Hin as [Hin AL]. cbn in AL.
  apply (proj2 (list_elem_of_In _ _)) in Hin. apply elem_of_map_to_list in Hin.
  destruct (cm_state cm') as [i|] eqn:ST'; [| discriminate].
  exists k, cm', i. split; [exact Hin|]. split; [| split; [exact E2| split; [exact E3| exact ST']]].
  intros ->. rewrite Hcm in Hin. injection Hin as <-. apply NE. rewrite E2, E3. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma chunk_live_in : forall (sx : astate) k cm i, as_chunks sx !! k = Some cm -> cm_state cm = CAllocated i ->
  In (cm_user_beg cm, cm_n cm) (live_blocks sx).
Proof.
  intros sx k cm i Hk ST. unfold live_blocks, chunk_list. apply in_map_iff. exists (k, cm). split; [reflexivity|].
  apply filter_In. split; [| cbn; rewrite ST; reflexivity].
  apply (proj1 (list_elem_of_In _ _)). apply elem_of_map_to_list. exact Hk.
Qed.

(* [comment removed for export] *)
Lemma live_apart_blk : forall E P D sx cb cm blo bsz, AWf E P D sx -> as_chunks sx !! cb = Some cm ->
  In (blo, bsz) (live_blocks sx) -> (blo, bsz) <> (cm_user_beg cm, cm_n cm) ->
  blo + bsz <= blk_lo cm \/ blk_hi sx cm <= blo.
Proof.
  intros E P D sx cb cm blo bsz WF Hcm Hin NE.
  destruct (live_block_other E P D sx cb cm blo bsz WF Hcm Hin NE) as (cb' & cm' & i & H' & NE' & <- & <- & _).
  pose proof (chunk_user_in_block E P D sx cb' cm' WF H') as (U1 & U2 & _). unfold user_lo, user_hi in U1, U2.
  destruct (chunks_disjoint E P D sx cb' cm' cb cm WF H' Hcm NE'); [left| right]; lia.
Qed.

(* [comment removed for export] *)
Lemma chunk_geo : forall E P D sx cb cm, AWf E P D sx -> as_chunks sx !! cb = Some cm ->
  blk_lo cm + 16 <= cm_user_beg cm /\ cm_user_beg cm + cm_n cm <= blk_hi sx cm /\ cb = cm_user_beg cm - 16
  /\ cm_user_beg cm + round_up (cm_n cm) 8 <= blk_hi sx cm /\ cm_user_beg cm + 8 <= blk_hi sx cm.
Proof.
  intros E P D sx cb cm WF Hcm.
  pose proof (chunk_user_in_block E P D sx cb cm WF Hcm) as (A0 & B0 & C0). unfold user_lo, user_hi, kChunkHeaderSize in A0, B0, C0.
  split; [exact A0|]. split; [exact B0|]. split; [exact C0|].
  pose proof WF as (WE & WR & WC & [K1 _] & _). destruct (K1 _ _ Hcm) as (A & B & C & D0 & _).
  unfold blk_hi, cm_chunk_beg, cm_user_beg in *. rewrite C in *.
  change (16 * 2 ^ rz_log (cm_n cm)) with (rz_size (cm_n cm)) in *.
  pose proof (rz_size_pos (cm_n cm)) as RP. pose proof (rounded_ge (cm_n cm)) as (RG1 & RG2 & RG3).
  assert (RU : round_up (cm_n cm) 8 <= rounded (cm_n cm) /\ 8 <= rounded (cm_n cm)) by (unfold round_up; clear -RG1 RG3 B; Z.div_mod_to_equations; lia).
  destruct (cm_prim cm) as [c|].
  - destruct D0 as (D1 & D2 & _). pose proof (proj1 (from_primary_iff (cm_n cm) ltac:(lia)) D1) as LE.
    pose proof (malloc_class_ok (cm_n cm) ltac:(lia)) as [_ NE]. rewrite <- D2 in NE. unfold needed1 in NE. clear -NE RU RP. lia.
  - destruct D0 as (D1 & _). pose proof (map_size_facts (cm_n cm)) as (_ & MG & _). unfold needed in MG. rewrite D1 in MG. unfold needed1 in MG. unfold kPageSize in *.
    clear -MG RU RP. lia.
Qed.

(* [comment removed for export] *)
Lemma batch_vs_live : forall E P sx b blo bsz, AWf E P [] sx -> In b (as_tq sx ++ as_gq sx) -> In (blo, bsz) (live_blocks sx) ->
  blo + bsz <= b_addr b \/ b_addr b + 8192 <= blo.
Proof.
  intros E P sx b blo bsz WF Hb Hin.
  destruct (live_block_loc E P [] sx blo bsz WF Hin) as (k & cm & Hk & UBk & Nk & N1 & B1 & B2 & LOC).
  pose proof WF as (WE & WR & _ & [K1 _] & WQ & (_ & _ & S3 & _) & _).
  destruct (batch_block E [] sx b WQ ltac:(unfold all_batches; rewrite app_assoc; apply in_app_iff; left; exact Hb)) as (CV & _ & _ & NCB).
  assert (CS : class_size kBatchClass = 8192) by reflexivity. assert (HB24 : 1 <= kBatchClass <= kLargestClassID) by (unfold kBatchClass, kLargestClassID; lia).
  destruct (K1 _ _ Hk) as (_ & _ & _ & D0 & _).
  destruct (cm_prim cm) as [c|] eqn:PR.
  - destruct LOC as (Hc & R1 & R2). destruct D0 as (_ & _ & CVc & _).
    unfold blk_lo, blk_hi in B1, B2. rewrite PR in B2.
    destruct (carved_blocks_disjoint E sx c (cm_alloc_beg cm) kBatchClass (b_addr b) Hc HB24 WR CVc CV) as [[_ EQ]|D].
    + exfalso. apply NCB. exists k, cm. split; [exact Hk| exact EQ].
    + clear -D B1 B2 CS. lia.
  - destruct LOC as (sc & Hsc & R1 & R2). pose proof (carved_in_space E sx kBatchClass _ HB24 WR CV) as [I1 I2].
    destruct (S3 sc Hsc) as (_ & _ & _ & _ & _ & SP & _).
    unfold kPageSize, kRegionSize, kSpaceSize in *. clear -B1 B2 R1 R2 I1 I2 SP CS. lia.
Qed.

(* [comment removed for export] *)
Lemma cache_vs_live : forall E P D sx c x blo bsz, AWf E P D sx -> 1 <= c <= kLargestClassID -> In x (get_cache sx c) -> In (blo, bsz) (live_blocks sx) ->
  blo + bsz <= chunk_of_compact (ae_space_beg E) c x \/ chunk_of_compact (ae_space_beg E) c x + class_size c <= blo.
Proof.
  intros E P D sx c x blo bsz WF Hc Hx Hin.
  destruct (live_block_loc E P D sx blo bsz WF Hin) as (k & cm & Hk & _ & _ & _ & B1 & B2 & _).
  destruct (cache_block_clear E P D sx c x k cm WF Hc Hx Hk); [left| right]; lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ARep_high_agree : forall P D (ax : astate) (m m' : mem) lo,
  ARep asegs E0 (DepotR asegs E0) ax m -> AWf E0 P D ax -> renv_ok ax -> alloc_ceiling <= lo ->
  wmono asegs m m' -> (forall z, 0 <= z < 2^64 -> z < lo -> m' (wa z) = m (wa z)) ->
  ARep asegs E0 (DepotR asegs E0) ax m'.
Proof.
  intros P D ax m m' lo REP WF RENV LOC WM AG. pose proof ceil_range as CR.
  destruct RENV as (BS & _ & IMG_IN & IMG_LO & _).
  eapply (ARep_frame_client asegs _ _ (DepotFP E0)); [| exact REP| exact WM|].
  - intros a0 mm mm' DD W' A'. eapply DepotR_frame; [exact DD| exact W'| exact A'].
  - intros x FPx.
    pose proof (fp_below_ceiling _ _ P D IMG_IN (DepotFP_where E0) _ _ WF BS FPx) as UB.
    assert (Hx : 0 <= x < 2^64).
    { destruct (fp_locate _ _ P D IMG_IN (DepotFP_where E0) _ _ WF BS FPx) as [(r & Hr & R)|[[R _]|[R _]]].
      - pose proof (IMG_IN r Hr). clear -H R IMG_LO UB CR. lia.
      - unfold sh_band, kLowShadowBeg, kShadowBase in R. rewrite kHighShadowBeg_val in R. clear -UB CR R. lia.
      - unfold app_addr in R. rewrite kHighMemBeg_val in R. clear -UB CR R. lia. }
    apply AG; [exact Hx| clear -UB LOC; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma aw_ok_mono : forall (a b a' b' : astate) lo sp sp' iv,
  (forall sc, In sc (as_sec b) \/ In sc (as_sec b') -> In sc (as_sec a) \/ In sc (as_sec a')) ->
  (forall x, In x (as_node_blocks b') -> In x (as_node_blocks a')) -> (forall x, In x (as_store_blocks b') -> In x (as_store_blocks a')) ->
  sp <= sp' -> aw_ok E0 b b' lo sp iv -> aw_ok E0 a a' lo sp' iv.
Proof.
  intros a b a' b' lo sp sp' [x y] HS HN HT LE H. unfold aw_ok in *. cbn [fst snd] in *.
  destruct H as [H|[H|[H|[H|[H|[(sc & Hsc & H1 & H2)|[(bb & Hb & H1 & H2)|[(bb & Hb & H1 & H2)|H]]]]]]]].
  - left. clear -H LE. lia.
  - right; left; exact H.
  - do 2 right; left; exact H.
  - do 3 right; left; exact H.
  - do 4 right; left; exact H.
  - do 5 right; left. exists sc. split; [exact (HS sc Hsc)| clear -H1 H2; lia].
  - do 6 right; left. exists bb. split; [destruct Hb as [<-|Hb]; [left; reflexivity| right; exact (HN _ Hb)]| clear -H1 H2; lia].
  - do 7 right; left. exists bb. split; [destruct Hb as [<-|Hb]; [left; reflexivity| right; exact (HT _ Hb)]| clear -H1 H2; lia].
  - do 8 right. exact H.
Qed.

Lemma aw_ok_ceiling : forall P D P' D' (a a' : astate) lo sp iv z,
  aw_ok E0 a a' lo sp iv -> AWf E0 P D a -> AWf E0 P' D' a' -> blocks_sep E0 a' -> fst iv <= z < snd iv ->
  z < alloc_ceiling \/ (lo <= fst iv /\ snd iv <= sp).
Proof.
  intros P D P' D' a a' lo sp [x y] z H WF WF' BS Hz. pose proof ceil_range as CR. unfold aw_ok in H. cbn [fst snd] in *.
  pose proof (proj1 WF) as WE. pose proof (wf_env_thread _ WE) as (_ & _ & WT3 & _).
  pose proof WE as (_ & _ & _ & _ & WEce & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & WEpa & _). change kResvLen with 137439023104 in *.
  pose proof PL0OK as (_ & _ & (_ & TR2 & _) & _). pose proof TR2 as (Tlo & Thi & _).
  pose proof ENV0 as (_ & _ & N3 & N4 & _). unfold placed, A_IMG_END in N3, N4.
  destruct H as [H|[(r & Hr & H1 & H2)|[(r & Hr & H1 & H2)|[H|[H|[(sc & Hsc & H1 & H2)|[(bb & Hb & H1 & H2)|[(bb & Hb & H1 & H2)|[H _]]]]]]]]].
  - right. exact H.
  - left. pose proof (img_mut_low r Hr) as X. clear -X H1 H2 Hz CR. lia.
  - left. unfold arep_thr_ranges in Hr. unfold kThrStackTop, kThrQCache, kThrCache, kPerClassSize, kNumClasses, kThrCacheStats, kThrStats, kThrUnwinding in Hr.
    repeat (destruct Hr as [<-|Hr]; [cbn [fst snd] in H1, H2; clear -H1 H2 Hz Thi; lia|]). destruct Hr.
  - left. clear -H Hz WEce. lia.
  - left. unfold kPtrArrayLen in *. clear -H Hz WEpa. lia.
  - left. destruct Hsc as [Hsc|Hsc];
      [pose proof WF as (_ & _ & _ & _ & _ & (_ & _ & S3 & _) & _)| pose proof WF' as (_ & _ & _ & _ & _ & (_ & _ & S3 & _) & _)];
      destruct (S3 sc Hsc) as (_ & _ & CE & _); clear -CE H1 H2 Hz; lia.
  - left. destruct (BS bb kDepotNodeBlockBytes (or_introl (conj Hb eq_refl))) as (_ & B2 & _). clear -B2 H1 H2 Hz. lia.
  - left. destruct (BS bb kStoreBlockBytes (or_intror (conj Hb eq_refl))) as (_ & B2 & _). clear -B2 H1 H2 Hz. lia.
  - left. unfold LSHI, A_base.A_SB in H. rewrite kHighMemBeg_val, kLowAppEnd_val in H. clear -H Hz CR. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma arun_orc_app2 : forall {R} f (t : stree aev aans (astate * aout R)) orc s o evs orc',
  arun f t orc = Some (s, o, evs, orc') ->
  exists used, orc = used ++ orc' /\ forall tail, arun f t (used ++ tail) = Some (s, o, evs, tail).
Proof.
  intros R f. induction f as [|f IH]; intros t orc s o evs orc' H; destruct t as [[s0 o0]|e k]; cbn in H |- *.
  - injection H as <- <- <- <-. exists []. split; [reflexivity| intros tail; reflexivity].
  - destruct orc; discriminate.
  - injection H as <- <- <- <-. exists []. split; [reflexivity| intros tail; reflexivity].
  - destruct orc as [|a0 rest]; [discriminate|].
    destruct (arun f (k a0) rest) as [[[[s1 o1] evs1] orc1]|] eqn:HR; [| discriminate]. injection H as <- <- <- <-.
    destruct (IH _ _ _ _ _ _ HR) as (used & -> & RUN). exists (a0 :: used). split; [reflexivity|].
    intros tail. cbn [app]. rewrite (RUN tail). reflexivity.
Qed.

(* [comment removed for export] *)
Definition neednew (tq : list batch) : bool :=
  match tq with [] => true | _ => (zlen (b_items (List.last tq (mkBatch 0 [] 0))) =? kBatchCap) end.

Lemma neednew_full : forall l b, zlen (b_items b) = kBatchCap -> neednew (l ++ [b]) = true.
Proof.
  intros l b H. unfold neednew. rewrite (List.last_last l b (mkBatch 0 [] 0)), H.
  destruct (l ++ [b]) eqn:E; [reflexivity| apply Z.eqb_refl].
Qed.

(* [comment removed for export] *)
Lemma arun_bind_pl : forall {R S} (mm : AM R) (k : R -> AM S) s0 f orc s1 r res,
  arun 0%nat (mm s0) orc = Some (s1, ONorm r, [], orc) -> arun f (k r s1) orc = Some res -> arun f (abind mm k s0) orc = Some res.
Proof.
  intros R S mm k s0 f orc s1 r [[[s2 o2] evs2] orc2] H1 H2.
  pose proof (arun_abind mm k s0 0%nat f orc s1 r [] orc s2 o2 evs2 orc2 H1 H2) as X. exact X.
Qed.
Lemma arun_bind_pr : forall {R S} (mm : AM R) (k : R -> AM S) s0 f orc s1 r evs orc1 s2 o2 orc2,
  arun f (mm s0) orc = Some (s1, ONorm r, evs, orc1) -> arun 0%nat (k r s1) orc1 = Some (s2, o2, [], orc2) ->
  arun f (abind mm k s0) orc = Some (s2, o2, evs, orc2).
Proof.
  intros R S mm k s0 f orc s1 r evs orc1 s2 o2 orc2 H1 H2.
  pose proof (arun_abind mm k s0 f 0%nat orc s1 r evs orc1 s2 o2 [] orc2 H1 H2) as X. rewrite Nat.add_0_r, app_nil_r in X. exact X.
Qed.

(* [comment removed for export] *)
Lemma arun_enqueue_F1 : forall (sx : astate) l b cb n orc, as_tq sx = l ++ [b] -> zlen (b_items b) < kBatchCap ->
  arun 0%nat (enqueue E0 cb n sx) orc = Some (enq1_st sx l b cb n, ONorm tt, [], orc).
Proof.
  intros sx l b cb n orc Htq CAP. unfold enqueue.
  eapply arun_bind_pl; [apply arun_aget|]. cbv beta zeta. fold (neednew (as_tq sx)).
  replace (neednew (as_tq sx)) with false.
  2:{ symmetry. unfold neednew. rewrite Htq, (List.last_last l b (mkBatch 0 [] 0)). destruct (l ++ [b]) eqn:E; [destruct l; discriminate|]. apply Z.eqb_neq. clear -CAP; lia. }
  rewrite arun_aupd. match goal with |- Some (?x, _, _, _) = _ => replace x with (enq1_st sx l b cb n); [reflexivity|] end.
  unfold enq1_st, upd_tq. cbv beta. rewrite Htq, (removelast_eq (l ++ [b])), (removelast_last l b), (List.last_last l b (mkBatch 0 [] 0)). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma arun_cache_pop24 : forall (sx : astate) orc, get_cache sx kBatchClass <> [] ->
  arun 0%nat (cache_pop E0 kBatchClass sx) orc = Some (bpop_st sx, ONorm (Some (bnew sx)), [], orc).
Proof.
  intros sx orc NE. unfold cache_pop.
  eapply arun_bind_pl; [apply arun_aget|]. cbv beta.
  destruct (get_cache sx kBatchClass) as [|x0 l0] eqn:Hl; [exfalso; exact (NE eq_refl)|].
  eapply arun_bind_pl; [apply arun_aret|]. cbn [negb].
  eapply arun_bind_pl; [apply arun_aget|]. cbv beta. rewrite Hl.
  eapply arun_bind_pl; [apply arun_aupd|]. rewrite arun_aret. unfold bpop_st, bnew. rewrite Hl. reflexivity.
Qed.

Lemma arun_enqueue_F2h : forall (sx : astate) cb n orc, neednew (as_tq sx) = true -> get_cache sx kBatchClass <> [] -> bnew sx <> 0 ->
  arun 0%nat (enqueue E0 cb n sx) orc = Some (enq2_st sx cb n, ONorm tt, [], orc).
Proof.
  intros sx cb n orc NN NE NZ. unfold enqueue.
  eapply arun_bind_pl; [apply arun_aget|]. cbv beta zeta. fold (neednew (as_tq sx)). rewrite NN.
  eapply arun_bind_pl.
  - unfold batch_alloc. eapply arun_bind_pl; [apply (arun_cache_pop24 sx _ NE)|]. cbv beta iota.
    replace (bnew sx =? 0) with false by (symmetry; apply Z.eqb_neq; exact NZ). apply arun_aret.
  - rewrite arun_aupd. reflexivity.
Qed.

Lemma arun_enqueue_F2m : forall (sx sr : astate) cb n fr orc evs orc', neednew (as_tq sx) = true -> get_cache sx kBatchClass = [] ->
  arun fr (refill E0 kBatchClass sx) orc = Some (sr, ONorm true, evs, orc') -> get_cache sr kBatchClass <> [] -> bnew sr <> 0 ->
  arun fr (enqueue E0 cb n sx) orc = Some (enq2_st sr cb n, ONorm tt, evs, orc').
Proof.
  intros sx sr cb n fr orc evs orc' NN EM RUNr NE NZ.
  destruct (get_cache sr kBatchClass) as [|x0 l0] eqn:Hl; [exfalso; exact (NE eq_refl)|]. unfold bnew in NZ. rewrite Hl in NZ.
  unfold enqueue.
  eapply arun_bind_pl; [apply arun_aget|]. cbv beta zeta. fold (neednew (as_tq sx)). rewrite NN.
  eapply arun_bind_pr.
  - unfold batch_alloc. eapply arun_bind_pr.
    + unfold cache_pop. eapply arun_bind_pl; [apply arun_aget|]. cbv beta. rewrite EM.
      eapply arun_bind_pr; [exact RUNr|]. cbn [negb].
      eapply arun_bind_pl; [apply arun_aget|]. cbv beta. rewrite Hl.
      eapply arun_bind_pl; [apply arun_aupd|]. apply arun_aret.
    + cbv beta iota.
      match goal with |- context [?bb =? 0] => replace (bb =? 0) with false by (symmetry; apply Z.eqb_neq; exact NZ) end.
      apply arun_aret.
  - rewrite arun_aupd. unfold enq2_st, bpop_st, bnew. rewrite Hl. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma qc_enq1 : forall (sx : astate) l b cb n, as_tq sx = l ++ [b] ->
     qcount (as_tq (enq1_st sx l b cb n)) = qcount (as_tq sx) /\ list_first (as_tq (enq1_st sx l b cb n)) = list_first (as_tq sx)
  /\ list_last (as_tq (enq1_st sx l b cb n)) = b_addr b /\ tq_bytes (enq1_st sx l b cb n) = tq_bytes sx + n
  /\ as_tq (enq1_st sx l b cb n) <> [].
Proof.
  intros sx l b cb n Htq. unfold enq1_st, tq_bytes. cbn [as_tq upd_tq]. rewrite Htq.
  split; [unfold qcount; rewrite !length_app; reflexivity|].
  split; [destruct l; reflexivity|].
  split; [rewrite list_last_snoc; reflexivity|].
  split; [rewrite !qbytes_app; cbn [qbytes fold_right b_size]; lia|].
  destruct l; discriminate.
Qed.

(* [comment removed for export] *)
Lemma qc_enq2 : forall (sx : astate) cb n,
     as_tq (enq2_st sx cb n) = as_tq sx ++ [mkBatch (bnew sx) [cb] (kBatchSize + n)]
  /\ qcount (as_tq (enq2_st sx cb n)) = qcount (as_tq sx) + 1
  /\ list_first (as_tq (enq2_st sx cb n)) = match as_tq sx with [] => bnew sx | _ => list_first (as_tq sx) end
  /\ list_last (as_tq (enq2_st sx cb n)) = bnew sx /\ tq_bytes (enq2_st sx cb n) = tq_bytes sx + (kBatchSize + n).
Proof.
  intros sx cb n. unfold enq2_st, bpop_st, tq_bytes. cbn [as_tq upd_tq upd_cache_allocated upd_cache_stale set_cache].
  split; [reflexivity|]. split; [unfold qcount; rewrite length_app; cbn [length]; lia|].
  split; [destruct (as_tq sx); reflexivity|]. split; [rewrite list_last_snoc; reflexivity|].
  rewrite qbytes_app. cbn [qbytes fold_right b_size]. lia.
Qed.

(* [comment removed for export] *)
Definition QE_post (s : aps) (mo : Model) (m : mem) (usp lo cb B C C' : Z) (key : list Z)
    (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (K : TSet) : Prop :=
  forall (t0 t1 t2 a0' a1' a2' a3' a4' a5 a6 a7 t3 t4 t5 t6 : word) (m6 : mem) (mo6 : Model) (a2 a4 : astate) (cm : chunkmeta) (aid fid : Z),
  let a := aps_alloc s in let n := cm_n cm in let a3 := AsanRepFlip.s3 a2 cb cm aid fid in
  (* [comment removed for export] *)
  as_chunks a !! cb = Some cm -> cm_state cm = CAllocated aid -> cm_user_beg cm = cb + 16 ->
  (* [comment removed for export] *)
  (exists fuel orc evs orc', arun fuel (depot_put E0 key (upd_ts (ts_on_free n) a)) orc = Some (a2, ONorm fid, evs, orc')) ->
  1 <= fid < 2^31 -> dsame (upd_ts (ts_on_free n) a) a2 -> as_ndepot_ins a2 = as_ndepot_ins a + 1 ->
  (exists fuel orc evs orc', arun fuel (enqueue E0 cb n a3) orc = Some (a4, ONorm tt, evs, orc')) ->
  as_chunks a4 = as_chunks a3 /\ as_sec a4 = as_sec a /\ as_ptr_committed a4 = as_ptr_committed a /\ as_gq a4 = as_gq a
  /\ as_nprim_ever a4 = as_nprim_ever a /\ as_residue a4 = as_residue a /\ as_ndepot_ins a4 = as_ndepot_ins a2
  /\ as_node_blocks a4 = as_node_blocks a2 /\ as_store_blocks a4 = as_store_blocks a2 /\ as_sec_stats a4 = as_sec_stats a ->
  AWf E0 [] [] a4 -> ARep asegs E0 (DepotR asegs E0) a4 m6 -> AKern E0 a4 mo6 ->
  RTOKc (C - 1) (C' - DSLACK) (sA a4 s) mo6 -> KIA (aSc (sA a4 s)) (aNc (sA a4 s)) (aEBc (sA a4 s)) mo6 ->
  res_ok a4 -> gq_bytes a4 <= kQuarantineMax -> 0 <= tq_bytes a4 <= kThreadQuarantineMax + 2^28 -> depot_inv E0 a4 -> sstats_ok a4 -> csmall a4 ->
  m_fs mo6 = m_fs mo -> m_fds mo6 = m_fds mo -> m_tid mo6 = m_tid mo ->
  (* [comment removed for export] *)
  mem_inv asegs m6 -> stk asegs m6 lo (usp - 80) -> wmono asegs m m6 -> rt_misc5 FSB0 PL0 E0 m6 ->
  (exists W, munch W m m6 /\ Forall (aw_ok E0 a a4 lo usp) W
             /\ Forall (fun iv => forall blo bsz, In (blo, bsz) (live_blocks a) -> (blo, bsz) <> (cb + 16, n) -> snd iv <= fst iv \/ snd iv <= blo \/ blo + bsz <= fst iv) W) ->
  rw_cells asegs m6 (usp - 80) [C8 (wz (T + 208)); C8 (wz B); C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs m6 (T + 80) [C8 (wz (qcount (as_tq a4))); C8 (wz (list_first (as_tq a4))); C8 (wz (list_last (as_tq a4))); C8 (wz (tq_bytes a4))] ->
  realizes_cfg acfg asegs
    (mkCfg (MS (mkR (wz 0x370b0) (wz (usp - 80)) gp tp t0 t1 t2 (wz (INST + 728)) (wz (T + 80)) a0' a1' a2' a3' a4' a5 a6 a7
                    (wz n) (wz B) (wz (T + 208)) (wz cb) (wz 0x100000) s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x370b0) fc None m6 (seg_rom asegs)) mo6) K.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma enqueue_srz :
  forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (mo : Model) (s : aps) (lo B C C' : Z) (key : list Z) (K : TSet)
         (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word) (m5 : mem) (mo5 : Model) (a2 : astate) (cm : chunkmeta) (b1 aid fid cb : Z),
  let a := aps_alloc s in let usp := bv_unsigned sp in let n := cm_n cm in let l8 := (n + 7) / 8 in let SHa := kShadowBase + (cb + 16) / 8 in
  K [] ->
  (* [comment removed for export] *)
  AINVc a m mo -> ENVOK E0 FSB0 s -> fbudget_pre a -> In (cb + 16, n) (live_blocks a) -> n <= 2^27 ->
  refill_room a kBatchClass -> room a kBatchClass ->
  alloc_ceiling <= lo -> lo <= usp - K_FREE -> usp mod 16 = 0 -> usp < 2^47 -> tp = wz 0x5e0b10 ->
  (* [comment removed for export] *)
  as_chunks a !! cb = Some cm -> cm_state cm = CAllocated aid -> cm_user_beg cm = cb + 16 -> Z.land b1 127 = kHeaderByte1 -> 0 <= b1 < 256 ->
  (exists fuel orc evs orc', arun fuel (depot_put E0 key (upd_ts (ts_on_free n) a)) orc = Some (a2, ONorm fid, evs, orc')) ->
  1 <= fid < 2^31 -> AWf E0 [] [] a2 -> same_alloc (upd_ts (ts_on_free n) a) a2 ->
  AKern E0 a2 mo5 -> RTOKc (C - 1) (C' - DSLACK) (sA a2 s) mo5 -> KIA (aSc (sA a2 s)) (aNc (sA a2 s)) (aEBc (sA a2 s)) mo5 ->
  m_fs mo5 = m_fs mo -> m_fds mo5 = m_fds mo -> m_tid mo5 = m_tid mo ->
  mem_inv asegs m5 -> stk asegs m5 lo (usp - 80) -> wmono asegs m m5 ->
  (exists Wd, munch (W15 usp cb n ++ Wd) m m5 /\ Forall (dput_w_ok E0 a2 lo (usp - 48)) Wd) ->
  (forall z, 0 <= z < 2^64 -> ~ FPW1 a2 lo usp cb n z -> m5 (wa z) = m (wa z)) ->
  DepotR asegs E0 a2 m5 ->
  rw_cells asegs m5 (usp - 80) [C8 (wz (T + 208)); C8 (wz B); C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs m5 cb [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (wz (n / 2^32)); C4 (wz n); C8 (wz aid)] ->
  rw_cells asegs m5 (cb + 16) [C8 (wz fid)] ->
  rw_cells asegs m5 (T + 2824) [C8 (wz (ts_frees (as_ts a) + 1)); C8 (wz (ts_freed (as_ts a) + n))] ->
  rw_cells asegs m5 SHa [CB (Z.to_nat l8) (repeat (Z_to_bv 8 0xfd) (Z.to_nat l8))] ->
  QE_post s mo m usp lo cb B C C' key ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc K ->
  realizes_cfg acfg asegs
    (mkCfg (MS (mkR (wz 0x370b0) (wz (usp - 80)) gp tp t0 t1 t2 (wz (INST + 728)) (wz (T + 80)) (wz (T + 80)) (wz (T + 208)) (wz B) (wz cb) (wz n) a5 a6 a7
                    (wz n) (wz B) (wz (T + 208)) (wz cb) (wz 0x100000) s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x370bc) fc None m5 (seg_rom asegs)) mo5) K.
Proof.
  intros until cb. cbv zeta. intros KN AIV ENV FB LIVE N27 RROOM ROOM LOC LO SPA SPH TP Hcm ST UB HB1 HB1' RUN FID WF2 SAME AK2 TOK2 KIA2 Ffs5 Ffds5 Ftid5
         MI5 SK5 WM5 MUW AG5 DR5 PF5 HDR5 FID5 ST5 SH5 QPOST.
  pose proof alloc_ceiling_range as CR. pose proof A_bundle.kHighMemBeg_val as KHB. pose proof kLowAppEnd_val as KLE.
  pose proof AIV as AIV0. destruct AIV as (Hrep & Hwf & Hkern & Hres & Hqb & Hdi & Hbinv & Hmi & Hrt & Hss & Hcs).
  set (a := aps_alloc s) in *. set (usp := bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range _ sp) as USPR. change (bv_modulus 64) with (2^64) in USPR. fold usp in USPR.
  unfold K_FREE in LO.
  pose proof ENV as ENV'. destruct ENV' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & EE & EFS & [EI1 EI2]). rewrite EE in EI1, EI2.
  pose proof ENV0 as ENV0'. destruct ENV0' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IMGR & _ & _ & _ & _ & _ & IC0 & TDN & DNP).
  pose proof PL0OK as ((c0 & cl & CR0 & CC1 & CC2) & (d0 & dl & DR0 & DD1 & DD2) & TRr & CT & DT & CD & CIA).
  pose proof TRr as (TR1 & TR2 & _). pose proof TR2 as (Tlo & Thi & Timg & Tband). unfold A_IMG_END, A_LOWAPP_END, A_HIGH_BEG in Timg, Tband.
  pose proof Hwf as (WE & WR & WC & WK & WQ & WS & WD).
  pose proof (wf_env_thread _ WE) as (WT1 & WT2 & WT3 & WT4 & _). pose proof (wf_env_iarena _ WE) as (WI1 & WI2 & WI3 & WI4 & WI5).
  (* [comment removed for export] *)
  destruct (freed_chunk_facts E0 s mo m (cb + 16) (cm_n cm) Hrep Hwf Hkern EI1 EI2 LIVE)
    as (cm' & aid' & b1x & Hcm' & UB' & Ecn & ST' & AID1 & N40 & _ & _ & _ & _ & CB0 & CBC & CBB & P16 & CBT & CBI & CBLOC).
  replace (cb + 16 - 16) with cb in * by (clear; lia).
  assert (Ecm : cm' = cm) by (rewrite Hcm in Hcm'; injection Hcm'; auto). subst cm'.
  assert (Eaid : aid' = aid) by (rewrite ST in ST'; injection ST'; auto). subst aid'. clear Hcm' ST' UB' b1x.
  pose proof (rounded_ge (cm_n cm)) as (RG1 & RG2 & RG3).
  (* [comment removed for export] *)
  pose proof (flip_rep s mo mo5 m m5 a2 cm b1 aid fid lo usp cb key AIV0 ENV Hcm ST UB HB1 RUN (proj1 FID) WF2 AK2 LOC WM5 AG5 DR5 HDR5 FID5 ST5 SH5) as REP3.
  destruct (cut2_model s mo mo5 m m5 a2 cm aid fid cb C C' key AIV0 Hcm ST RUN (proj1 FID) WF2 AK2 TOK2 DR5)
    as (WF3 & PEND3 & AK3 & TOK3 & Hcb3 & Hoth3 & Etq3 & Egq3 & Eca3 & Eci3 & Ecal3 & Ereg3 & Esec3 & Enp3 & Eres3 & ND2 & End3 & Ets3
        & RES3 & QB3 & DI3 & SS3 & CS3 & SFP23 & DS2).
  fold a in Hoth3, Etq3, Egq3, Eca3, Eci3, Ecal3, Ereg3, Esec3, Enp3, Eres3, ND2, Ets3.
  set (a3 := AsanRepFlip.s3 a2 cb cm aid fid) in *.
  pose proof DS2 as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14 & D15 & D16 & D17 & D18 & D19 & D20 & D21 & D22).
  cbn [as_regions as_cache_inited as_cache as_cache_stale as_cache_allocated as_cache_mapped as_ptr_committed as_sec as_sec_stale as_sec_stats
       as_glob_allocated as_glob_mapped as_oom as_chunks as_dead as_tq as_gq as_ia_inited as_residue as_nprim_ever as_everc as_ts upd_ts]
    in D1, D2, D3, D4, D5, D6, D7, D8, D9, D10, D11, D12, D13, D14, D15, D16, D17, D18, D19, D20, D21, D22.
  (* [comment removed for export] *)
  assert (RT5 : rt_misc5 FSB0 PL0 E0 m5).
  { eapply (rt_misc5_cut2 a a2 mo mo5 m m5 lo usp cb (cm_n cm) Hrt Hwf Hkern WF2 AK2 EI1 EI2 LOC CB0 CBC CBT CBI CBLOC AG5). }
  (* [comment removed for export] *)
  destruct (enq_cells a3 m5 [cb] REP3 WF3 IC0) as (junk24 & QC5 & ROW5 & CARR5 & CLEN5 & CST5 & INS5 & LASTF).
  (* [comment removed for export] *)
  destruct (RTOK_elim _ _ _ _ _ _ _ _ _ _ TOK3) as (R3 & R3' & ATK3 & HCR3 & HCR3' & GR3 & GD3 & RLE3).
  assert (ENV3 : ENVOK E0 FSB0 (sA a3 s)) by exact (ATOK_ENVOK _ _ _ _ _ _ _ _ _ _ ATK3).
  pose proof (proj1 WF3) as WE3.
  set (P3 := PP (sA a3 s) mo5).
  pose proof (PP_KIP E0 FSB0 HR0 L0 RES0 EB0 (sA a3 s) mo5 R3 R3' ATK3) as KIP3.
  assert (PSTK : forall y k, lo <= y -> y + Z.of_nat k <= usp - 80 -> P3 (Z_to_bv 64 y, k)).
  { intros y k H1 H2. unfold P3. rewrite <- EPOL. apply (pol_stack' E0 FSB0 HR0 (sA a3 s) mo5 AK3 WE3 ENV0); clear -H1 H2 LOC USPR CR; lia. }
  assert (PT : forall y k, T <= y -> y + Z.of_nat k <= T + 4096 -> P3 (Z_to_bv 64 y, k)).
  { intros y k H1 H2. unfold P3. rewrite <- EPOL. apply (pol_thread' E0 FSB0 HR0 (sA a3 s) mo5 AK3 WE3); clear -H1 H2; lia. }
  assert (PDAT : forall y k, 0xa4000 <= y -> y + Z.of_nat k <= 0x603000 -> P3 (Z_to_bv 64 y, k)).
  { intros y k H1 H2. unfold P3. rewrite <- EPOL. apply (pol_img' E0 FSB0 HR0 (sA a3 s) mo5 AK3 WE3 ENV3 ENV0); clear -H1 H2; lia. }
  assert (PUSR : forall y k, region_beg SB kBatchClass <= y -> y + Z.of_nat k <= region_beg SB kBatchClass + rg_mapped_user (get_region a3 kBatchClass) -> P3 (Z_to_bv 64 y, k)).
  { intros y k H1 H2. destruct k as [|k']; [apply PP_zero|]. unfold P3. rewrite <- EPOL.
    apply (pol_user E0 FSB0 HR0 (sA a3 s) mo5 [cb] [] AK3 WF3 kBatchClass); [unfold kBatchClass, kLargestClassID; clear; lia| exact H1| exact H2| clear; lia]. }
  assert (Hsp : bv_unsigned (Z_to_bv 64 (usp - 80)) = usp - 80) by (apply unsigned_lit; clear -USPR LO LOC CR; lia).
  assert (HTp3 : placed_s T 4096) by (unfold placed_s, A_IMG_END, A_LOWAPP_END, A_HIGH_BEG; clear -Tlo Thi Timg Tband; repeat split; lia).
  (* [comment removed for export] *)
  pose proof (ak_resv_geom _ _ _ AK3) as (G1 & G2 & G3). change kSpaceSize with 137438953472 in G3. change kPageSize with 4096 in G3. change kResvLen with 137439023104 in G3.
  destruct (proj2 (proj1 (proj2 WF3)) kBatchClass ltac:(unfold kBatchClass, kLargestClassID; clear; lia)) as (RG1' & RG2' & RG3' & _).
  cbv zeta in RG1', RG2', RG3'. unfold region_of in RG1', RG2', RG3'. change kFreeArrayOffset with 3758096384 in RG3'.
  assert (BLK : forall bb, carved E0 a3 kBatchClass bb ->
            region_beg SB kBatchClass <= bb /\ bb + 8192 <= region_beg SB kBatchClass + rg_mapped_user (get_region a3 kBatchClass)
            /\ kHighMemBeg <= bb /\ bb + 8192 <= alloc_ceiling /\ bb + 8192 <= SB + kSpaceSize /\ (bb + 8192 <= T \/ T + 4096 <= bb) /\ bb mod 16 = 0
            /\ ae_resv_beg E0 <= bb /\ bb + 8192 + 4096 <= ae_resv_beg E0 + 137439023104 /\ SB <= bb).
  { intros bb (k & K0 & KE & KB). unfold region_of in KB. change (class_size kBatchClass) with 8192 in KE, KB.
    unfold region_beg, kBatchClass in *. change kRegionSize with 4294967296 in *. change kResvLen with 137439023104. unfold kSpaceSize. rewrite KHB.
    pose proof WE3 as (_ & WEhi & _ & _ & WEce & _). rewrite KHB in WEhi.
    clear -K0 KE KB RG1' RG3' G1 G2 G3 WT4 WEhi WEce CR. repeat split; lia. }
  (* [comment removed for export] *)
  assert (RENV3 : renv_ok a3).
  { split; [apply (blocks_sep_ext E0 a2 a3); [reflexivity| reflexivity| reflexivity| exact (blocks_sep_of E0 a2 mo5 ENV0 WF2 AK2)]|].
    split; [clear -Tlo Thi Timg; repeat split; lia|].
    split; [intros r Hr; pose proof (IMGR r Hr) as X; rewrite EI1; clear -X EI2; lia|].
    split; [rewrite EI1; clear; lia|]. split; [exact IMGR|]. split; [exact (img_depsep_asan E0 IC0)|].
    split; [exists mo5; exact AK3|]. split; [exact TDN| exact DNP]. }
  (* [comment removed for export] *)
  pose proof CR0 as (CIn & _ & _ & CRS & _). pose proof DR0 as (DIn & _ & _ & DRS & _). change kResvLen with 137439023104 in CRS, DRS.
  pose proof (resv_range_num E0 c0 cl CR0 ltac:(clear -CC1 CC2; lia)) as (CQ1 & CQ2 & CQ3 & CQ4).
  pose proof (resv_range_num E0 d0 dl DR0 ltac:(clear -DD1 DD2; lia)) as (DQ1 & DQ2 & DQ3 & DQ4).
  unfold kIArenaLen in CIA, WI4.
  destruct WS as (_ & _ & WS3 & _).
  destruct MUW as (Wd & MU5 & FWd).
  assert (GRe3 : forall c', get_region a3 c' = get_region a c') by (intros c'; unfold get_region; rewrite Ereg3; reflexivity).
  destruct (refill_room_transport a a3 kBatchClass GRe3 Enp3 (conj RROOM ROOM)) as [RROOM3 ROOM3].
  assert (TQ0 : forall lx, qcount lx = 0 -> lx = []) by (intros [|bb ll] H; [reflexivity| exfalso; unfold qcount in H; cbn [length] in H; clear -H; lia]).
  (* [comment removed for export] *)
  pose proof QB3 as [TQB _]. unfold kThreadQuarantineMax in TQB.
  assert (ARM : (exists lq bq, as_tq a3 = lq ++ [bq] /\ zlen (b_items bq) < kBatchCap) \/ neednew (as_tq a3) = true).
  { destruct (snoc_case (as_tq a3)) as [E|(lq & bq & E)]; [right; rewrite E; reflexivity|].
    destruct (Z_lt_dec (zlen (b_items bq)) kBatchCap) as [LT|GE]; [left; exists lq, bq; split; [exact E| exact LT]| right].
    destruct (LASTF lq bq E) as (_ & _ & _ & _ & WB & _). pose proof WB as (_ & _ & _ & _ & CAPb & _).
    rewrite E. apply neednew_full. clear -GE CAPb. lia. }
  destruct ARM as [(lq & bq & Htq & ROOMB)|NN].
  - (* [comment removed for export] *)
    destruct (LASTF lq bq Htq) as (ELAST & QC1 & LB5 & (junkb & ITS5 & ILEN) & WB & B1).
    pose proof WB as (CVb & _ & _ & _ & CAPb & BSZb & _). pose proof (BLK _ CVb) as (Bb1 & Bb2 & Bb3 & Bb4 & Bb5 & Bb6 & Bb7 & Bb8 & Bb9 & Bb10).
    pose proof (tq_weights E0 [cb] [] a3 lq bq WF3 Htq) as (QW1 & QW2 & QW3 & QW4 & QW5). unfold kBatchSize in QW1, QW4.
    rewrite ELAST in QC5.
    set (bcnt := zlen (b_items bq)) in *. unfold kBatchCap in ROOMB.
    set (its := map (fun z : Z => Z_to_bv 64 z) (b_items bq) ++ junkb) in ITS5.
    assert (LITS : Z.of_nat (length its) = 1021) by (subst its; rewrite length_app, length_map; clear -ILEN; lia).
    set (DQ := fun ms6 => exists (a1' a2' a5' a6' a7' : word) (m6 : mem),
          ms6 = MS (mkR (wz 0x370b0) (wz (usp - 80)) gp tp t0 t1 t2 (wz (INST + 728)) (wz (T + 80)) (wz (T + 80)) a1' a2' (wz cb) (wz (cm_n cm)) a5' a6' a7'
                        (wz (cm_n cm)) (wz B) (wz (T + 208)) (wz cb) (wz 0x100000) s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x370b0) fc None m6 (seg_rom asegs)
          /\ mem_inv asegs m6 /\ stk asegs m6 lo (usp - 80) /\ wmono asegs m5 m6
          /\ munch [(usp - 144, usp - 80); (b_addr bq + 8, b_addr bq + 24); (b_addr bq + 24 + 8 * bcnt, b_addr bq + 24 + 8 * bcnt + 8); (T + 104, T + 112)] m5 m6
          /\ rw_cells asegs m6 (T + 80) [C8 (wz (qcount (as_tq a3))); C8 (wz (list_first (as_tq a3))); C8 (wz (b_addr bq)); C8 (wz (tq_bytes a3 + cm_n cm))]
          /\ rw_cells asegs m6 (b_addr bq) [C8 (wz 0); C8 (wz (b_size bq + cm_n cm)); C8 (wz (bcnt + 1))]
          /\ u64arr asegs m6 (b_addr bq + 24) (upd its (Z.to_nat bcnt) (wz cb))).
    eapply (rzA_seg_cfg asegs (aSc (sA a3 s)) (aNc (sA a3 s)) (aEBc (sA a3 s)) P3 DQ).
    { eapply (enqueue1_walk P3 (wz 0x370b0) (wz (usp - 80)) gp tp t0 t1 t2 (wz (INST + 728)) (wz (T + 80)) a5 a6 a7 (wz (cm_n cm)) (wz B) (wz (T + 208)) (wz cb) (wz 0x100000)
                s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc DQ m5 lo T (T + 208) B cb (cm_n cm) (qcount (as_tq a3)) (list_first (as_tq a3)) (b_addr bq) 0 (b_size bq) bcnt (tq_bytes a3) its);
        rewrite ?Hsp;
        [ exact SK5 | exact LOC | clear -LO; lia | clear -SPH LO LOC CR; lia | exact MI5 | exact HTp3 | exact QC5
        | clear -QC1 QW4 TQB; lia | clear -Bb3 Bb4 KHB; lia | exact Bb6 | exact LB5 | exact ITS5 | exact LITS
        | clear -ROOMB B1; subst bcnt; lia | clear -QW2 QW1 TQB N40; lia
        | exact PSTK | exact PT | intros y k Y1 Y2; apply PUSR; [clear -Y1 Bb1; lia| clear -Y2 Bb2; lia] | ].
      intros m6 a1' a2' a5' a6' a7' MI6 SK6 WM6 MU6 QC6 LB6 ITS6.
      rewrite ?Hsp in SK6. rewrite ?Hsp in MU6. replace (usp - 80 - 64) with (usp - 144) in MU6 by (clear; lia). replace (ret_pc (wz 0x370b0)) with (wz 0x370b0 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
      apply evtA_done. unfold DQ. exists a1', a2', a5', a6', a7', m6.
      split; [reflexivity|]. split; [exact MI6|]. split; [exact SK6|]. split; [exact WM6|]. split; [exact MU6|]. split; [exact QC6|]. split; [exact LB6| exact ITS6]. }
    { exact KIP3. }
    intros ms6 mo6 HQ6 AG6 KIP6. unfold DQ in HQ6.
    destruct HQ6 as (a1' & a2' & a5' & a6' & a7' & m6 & -> & MI6 & SK6 & WM6 & MU6 & QC6 & LB6 & ITS6).
    (* [comment removed for export] *)
    pose proof (magree_frame _ _ AG6) as (Ffds6 & Fvm6 & Flz6 & Ffs6 & Fh6 & Ftid6 & _).
    destruct KIP6 as [KIA6 _].
    pose proof (RTOK_magree _ _ _ _ _ _ _ _ _ _ _ TOK3 AG6 KIA6) as TOK6.
    pose proof (AKern_frame _ _ _ _ Fvm6 Flz6 AK3) as AK6.
    set (a4 := enq1_st a3 lq bq cb (cm_n cm)).
    assert (WF4 : AWf E0 [] [] a4) by exact (AWf_push_last E0 [] a3 cb (cm_n cm) lq bq WF3 PEND3 Htq ROOMB).
    assert (AK4 : AKern E0 a4 mo6) by (apply (AKern_ext E0 a3); [reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| exact AK6]).
    assert (SFP34 : same_fp a3 a4) by (repeat split; reflexivity).
    assert (TOK4 : RTOKc (C - 1) (C' - DSLACK) (sA a4 s) mo6) by (eapply (RTOK_same_fp E0 FSB0 HR0 L0 RES0 EB0); [exact TOK6| exact SFP34| reflexivity| reflexivity]).
    destruct (RTOK_elim _ _ _ _ _ _ _ _ _ _ TOK4) as (R4 & R4' & ATK4 & _).
    pose proof (ATOK_KIA _ _ _ _ _ _ _ _ _ _ ATK4) as KIA4.
    (* [comment removed for export] *)
    assert (AG56 : forall z, 0 <= z < 2^64 -> (z + 1 <= usp - 144 \/ usp - 80 <= z) -> (z + 1 <= b_addr bq + 8 \/ b_addr bq + 24 <= z) ->
              (z + 1 <= b_addr bq + 24 + 8 * bcnt \/ b_addr bq + 24 + 8 * bcnt + 8 <= z) -> (z + 1 <= T + 104 \/ T + 112 <= z) -> m6 (wa z) = m5 (wa z)).
    { intros z Z0 Z1 Z2 Z3 Z4. apply MU6. rewrite wa_unsigned by (clear -Z0; lia). cbn [outside]. clear -Z1 Z2 Z3 Z4. repeat split; try exact I; lia. }
    assert (BC8 : 0 <= 8 * bcnt /\ 8 * bcnt + 8 <= 8 * 1021) by (clear -ROOMB B1; subst bcnt; lia).
    (* [comment removed for export] *)
    assert (REP4 : ARep asegs E0 (DepotR asegs E0) a4 m6).
    { apply (R2F1 a3 m5 m6 lo cb (cm_n cm) lq bq [] Htq ROOMB PEND3 REP3 WF3 RENV3 WM6).
      - intros z Z0 NF. unfold FPWe1, kThrQCache in NF. apply AG56; [exact Z0| clear -NF LO; lia| clear -NF; lia| clear -NF; lia| clear -NF; lia].
      - exact LOC.
      - destruct (rwc_split asegs m6 (T + 80) [C8 (wz (qcount (as_tq a3))); C8 (wz (list_first (as_tq a3))); C8 (wz (b_addr bq))] [C8 (wz (tq_bytes a3 + cm_n cm))] QC6) as [_ X].
        cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in X. unfold kThrQCache. exact X.
      - destruct (rwc_split asegs m6 (b_addr bq) [C8 (wz 0)] [C8 (wz (b_size bq + cm_n cm)); C8 (wz (bcnt + 1))] LB6) as [_ X].
        cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in X. exact X.
      - replace (b_addr bq + 24 + 8 * bcnt) with (b_addr bq + 24 + 8 * Z.of_nat (Z.to_nat bcnt)) by (rewrite Z2Nat.id by (clear -BC8; lia); reflexivity).
        apply (u64arr_cell m6 (b_addr bq + 24) _ (Z.to_nat bcnt) (wz cb) ITS6). apply nth_error_upd_same. clear -LITS ROOMB B1. subst bcnt. lia. }
    (* [comment removed for export] *)
    assert (RT6 : rt_misc5 FSB0 PL0 E0 m6).
    { apply (rt_misc5_agree E0 FSB0 PL0 m5 m6 RT5). intros z Hz.
      destruct (rt_fpc_where2 E0 FSB0 PL0 z Hz) as [[ZI NM]|RH].
      - apply AG56; [clear -ZI; lia| clear -ZI LO LOC CR; lia| clear -ZI Bb3 KHB; lia| clear -ZI Bb3 KHB BC8; lia| clear -ZI Timg Tlo; lia].
      - unfold rt_high2 in RH. apply AG56; [clear -RH Tlo Thi CQ1 CQ2 CC1 CC2 DQ1 DQ2 DD1 DD2 CR; lia| clear -RH LO LOC Thi CQ2 CC2 DQ2 DD2; lia| | |].
        + clear -RH Bb6 Bb8 Bb9 CRS DRS CC1 CC2 DD1 DD2 CIA WI4. lia.
        + clear -RH Bb6 Bb8 Bb9 CRS DRS CC1 CC2 DD1 DD2 CIA WI4 BC8. lia.
        + clear -RH CT DT. lia. }
    (* [comment removed for export] *)
    set (W6 := [(usp - 144, usp - 80); (b_addr bq + 8, b_addr bq + 24); (b_addr bq + 24 + 8 * bcnt, b_addr bq + 24 + 8 * bcnt + 8); (T + 104, T + 112)]) in MU6.
    assert (MU06 : munch ((W15 usp cb (cm_n cm) ++ Wd) ++ W6) m m6).
    { eapply munch_trans; [eapply munch_weaken; [| exact MU5]| eapply munch_weaken; [| exact MU6]]; intros z Hz;
        apply (proj2 (outside_forall _ _)); intros lo' hi' Hin; apply (proj1 (outside_forall _ _) Hz); apply in_app_iff; [left| right]; exact Hin. }
    (* [comment removed for export] *)
    assert (CBAW : forall x y, cb <= x -> y <= cb + 16 + rounded (cm_n cm) ->
              (ae_resv_beg E0 <= x /\ y <= ae_resv_beg E0 + kResvLen) \/ (exists sc, (In sc (as_sec a) \/ In sc (as_sec a4)) /\ sc_map_beg sc <= x /\ y <= sc_map_beg sc + sc_map_size sc)).
    { intros x y X1 Y1. destruct CBLOC as [(c & Hc & L1 & L2)|(sc & Hsc & L1 & L2)].
      - left. unfold region_beg in L1, L2. destruct (proj2 WR c Hc) as (Rg1 & Rg2 & Rg3 & _). cbv zeta in Rg1, Rg3. unfold region_of in Rg1, Rg3.
        change kRegionSize with 4294967296 in L1, L2. change kFreeArrayOffset with 3758096384 in Rg3. unfold kLargestClassID in Hc. change kResvLen with 137439023104.
        pose proof (ak_resv_geom _ _ _ Hkern) as (G1' & _ & G3'). change kSpaceSize with 137438953472 in G3'. change kPageSize with 4096 in G3'. change kResvLen with 137439023104 in G3'.
        subst a. clear -X1 Y1 L1 L2 Hc Rg1 Rg3 G1' G3'. nia.
      - right. exists sc. split; [left; exact Hsc| clear -X1 Y1 L1 L2; lia]. }
    assert (HL8b : 8 * ((cm_n cm + 7) / 8) < cm_n cm + 8 /\ cm_n cm <= rounded (cm_n cm)) by (clear -N40 RG1; Z.div_mod_to_equations; lia).
    assert (G8 : 8 * ((cb + 16) / 8) = cb + 16) by (clear -P16; Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    unfold QE_post in QPOST.
    eapply (QPOST t0 t1 t2 (wz (T + 80)) a1' a2' (wz cb) (wz (cm_n cm)) a5' a6' a7' t3 t4 t5 t6 m6 mo6 a2 a4 cm aid fid);
      [ exact Hcm | exact ST | exact UB | exact RUN | exact FID | exact DS2 | exact ND2
      | exists 0%nat, [], [], []; apply (arun_enqueue_F1 a3 lq bq cb (cm_n cm)); [exact Htq| exact ROOMB]
      | (* [comment removed for export] *) unfold a4, enq1_st, a3, AsanRepFlip.s3;
        cbn [as_chunks as_sec as_ptr_committed as_gq as_nprim_ever as_residue as_ndepot_ins as_node_blocks as_store_blocks as_sec_stats upd_tq upd_chunks];
        repeat split; first [reflexivity| exact D8| exact D7| exact D17| exact D20| exact D19| exact D10]
      | exact WF4 | exact REP4 | exact AK4 | exact TOK4 | exact KIA4
      | (* [comment removed for export] *) apply (res_ok_frame a3); [cbn; intros sc H; exact H| cbn; apply incl_refl| exact RES3]
      | (* [comment removed for export] *) exact (proj2 QB3)
      | (* [comment removed for export] *) pose proof (qc_enq1 a3 lq bq cb (cm_n cm) Htq) as (_ & _ & _ & -> & _); unfold kThreadQuarantineMax; clear -QW1 QW2 TQB N40 N27; lia
      | (* [comment removed for export] *) revert DI3; clear; unfold depot_inv, depot_n_ids, dphi; exact (fun H => H)
      | (* [comment removed for export] *) revert SS3; clear; unfold sstats_ok, sec_bytes; exact (fun H => H)
      | (* [comment removed for export] *) intros cbx cmx Hx; apply (CS3 cbx cmx); revert Hx; unfold a4, enq1_st; cbn [as_chunks upd_tq]; exact (fun H => H)
      | rewrite Ffs6; exact Ffs5 | rewrite Ffds6; exact Ffds5 | rewrite Ftid6; exact Ftid5
      | exact MI6 | exact SK6 | exact (wmono_trans _ _ _ _ WM5 WM6) | exact RT6
      | (* [comment removed for export] *)
      | (* [comment removed for export] *) eapply AF_unwind.rw_cells_agree; [| exact PF5]; cbn -[Z.add Z.mul Z.of_nat Z.sub Z.div]; intros z Hz;
        apply AG56; [clear -Hz LO LOC CR USPR; lia| clear -Hz; lia| clear -Hz Bb4 LO LOC; lia| clear -Hz Bb4 LO LOC BC8; lia| clear -Hz Thi LO LOC; lia]
      | (* [comment removed for export] *) pose proof (qc_enq1 a3 lq bq cb (cm_n cm) Htq) as (-> & -> & -> & -> & _); exact QC6 ].
    (* [comment removed for export] *)
    exists ((W15 usp cb (cm_n cm) ++ Wd) ++ W6). split; [exact MU06|].
    assert (WDok : Forall (aw_ok E0 a a4 lo usp) Wd /\ Forall (fun iv => forall blo bsz, In (blo, bsz) (live_blocks a) -> (blo, bsz) <> (cb + 16, cm_n cm) -> snd iv <= fst iv \/ snd iv <= blo \/ blo + bsz <= fst iv) Wd).
    { split; apply Forall_forall; intros [x y] Hin; pose proof (proj1 (Forall_forall _ _) FWd _ Hin) as X; unfold dput_w_ok in X; cbn [fst snd] in X.
      - unfold aw_ok. cbn [fst snd]. destruct X as [X|[(r & Hr & X1 & X2)|[(b & Hb & X1 & X2)|(b & Hb & X1 & X2)]]].
        + left. clear -X; lia.
        + right; left. unfold depot_static in Hr. rewrite IC0 in Hr. cbn [aic_theDepot aic_stackStore asan_ic] in Hr.
          destruct Hr as [<-|[<-|[]]]; cbn [fst snd] in X1, X2.
          * exists (aic_theDepot asan_ic, 0x440010). split; [unfold img_mut; do 3 right; left; reflexivity| cbn [fst snd aic_theDepot asan_ic]; clear -X1 X2; lia].
          * exists (aic_stackStore asan_ic, 0x10010). split; [unfold img_mut; do 4 right; left; reflexivity| cbn [fst snd aic_stackStore asan_ic]; clear -X1 X2; lia].
        + do 6 right; left. exists b. split; [| clear -X1 X2; lia]. revert Hb. unfold a4, enq1_st, a3, AsanRepFlip.s3. cbn [as_node_blocks upd_tq upd_chunks]. exact (fun H => H).
        + do 7 right; left. exists b. split; [| clear -X1 X2; lia]. revert Hb. unfold a4, enq1_st, a3, AsanRepFlip.s3. cbn [as_store_blocks upd_tq upd_chunks]. exact (fun H => H).
      - intros blo bsz LIVEb NEb. cbn [fst snd]. destruct (live_block_where E0 a blo bsz Hwf LIVEb) as (Lw0 & Lw1 & Lw2 & Lw3). destruct (live_block_off_thread E0 a blo bsz Hwf LIVEb) as [_ BT].
        destruct X as [X|X]; [right; right; clear -X Lw1 LOC LO; lia|].
        assert (DZ : forall z, x <= z < y -> DepotFPd E0 a2 z).
        { intros z Hz. destruct X as [(r & Hr & X1 & X2)|[(b & Hb & X1 & X2)|(b & Hb & X1 & X2)]].
          - left. exists r. split; [unfold depot_static in Hr; destruct Hr as [<-|[<-|[]]]; [left| right; left]; reflexivity| clear -Hz X1 X2; lia].
          - right; left. exists b. split; [exact Hb| clear -Hz X1 X2; lia].
          - right; right. exists b. split; [exact Hb| clear -Hz X1 X2; lia]. }
        destruct (Z_lt_le_dec x y) as [O0|O0]; [| left; exact O0]. destruct (Z_lt_le_dec blo y) as [O1|O1]; [| right; left; exact O1]. destruct (Z_lt_le_dec x (blo + bsz)) as [O2|O2]; [| right; right; exact O2]. exfalso.
        set (z := Z.max x blo).
        assert (Zin : x <= z < y /\ blo <= z < blo + bsz) by (subst z; clear -O0 O1 O2 Lw0; lia).
        pose proof WE as (_ & WEhi & WErs & WEsp & _). change kSpaceSize with 137438953472 in WEsp.
        destruct (dfp_cases E0 PL0 ENV0 PL0OK a2 mo5 z IC0 AK2 WF2 EI1 EI2 (DZ z (proj1 Zin))) as [STz|(b & bl & R & Bb0 & Bce & Bbd & Brs & Bsc & BTb & BAb)].
        + (* [comment removed for export] *)
          destruct Lw3 as [[S1 S2]|(sc & Hsc & S1 & S2)]; [rewrite KHB in WEhi; clear -STz Zin S1 WEhi WErs; lia|].
          destruct (WS3 sc Hsc) as (_ & _ & _ & _ & _ & _ & SR). pose proof (SR _ (proj1 (wf_env_img _ WE))) as X1. rewrite EI1 in X1. cbn [fst snd] in X1. clear -STz Zin S1 S2 X1 EI2. lia.
        + (* [comment removed for export] *)
          change kResvLen with 137439023104 in Brs.
          destruct Lw3 as [[S1 S2]|(sc & Hsc & S1 & S2)]; [unfold kSpaceSize in S2; clear -R Zin S1 S2 Brs WErs WEsp; lia|].
          rewrite D8 in Bsc. destruct (Bsc sc Hsc); clear -R Zin S1 S2 H; lia. }
    pose proof (chunk_geo E0 [] [] a cb cm Hwf Hcm) as (CG1 & CG2 & CG3 & CG4 & CG5). rewrite UB in CG1, CG2, CG4, CG5.
    pose proof WE as (_ & WEhi & WErs & WEsp & _ & _ & WE7 & _ & WE9 & _ & _ & WE12 & _). change kSpaceSize with 137438953472 in WEsp. rewrite KHB in WEhi.
    split.
    { (* [comment removed for export] *)
      apply Forall_app; split; [apply Forall_app; split; [| exact (proj1 WDok)]|].
      + unfold AF_deallocT1.W15. repeat (apply Forall_cons; [unfold aw_ok; cbn [fst snd]|]); [.. | apply Forall_nil].
        * left. clear -LO; lia.
        * destruct (CBAW cb (cb + 4) ltac:(clear; lia) ltac:(clear -RG1; lia)) as [X|X]; [do 3 right; left; exact X| do 5 right; left; exact X].
        * destruct (CBAW (cb + 16) (cb + 24) ltac:(clear; lia) ltac:(clear -RG1; lia)) as [X|X]; [do 3 right; left; exact X| do 5 right; left; exact X].
        * right; right; left. exists (T + kThrStats, 112 + 8 * 32). split; [unfold arep_thr_ranges; do 5 right; left; reflexivity| cbn [fst snd]; unfold kThrStats; clear; lia].
        * do 8 right. split.
          -- unfold LSHI, A_base.A_SB, kShadowBase. rewrite ?KHB, ?KLE. rewrite KHB, KLE in CBB.
             destruct CBB as [LOW|HIGH]; [left; clear -LOW CB0 G8 HL8b RG1 CR| right; clear -HIGH CB0 CBC G8 HL8b RG1 CR]; Z.div_mod_to_equations; lia.
          -- intros z Hz. unfold A_base.A_SB, kShadowBase in *.
             assert (GR : cb + 16 <= 8 * (z - 2147450880) < cb + 16 + rounded (cm_n cm)) by (clear -Hz G8 HL8b; Z.div_mod_to_equations; lia).
             unfold sh_excluded.
             replace (in_fakestack E0 (8 * (z - 2147450880))) with false.
             2:{ symmetry. unfold in_fakestack. apply Bool.andb_false_iff.
                 destruct CBLOC as [(c & Hc & L1 & L2)|(sc & Hsc & L1 & L2)].
                 - unfold region_beg in L1, L2. destruct (proj2 WR c Hc) as (Rg1 & Rg2 & Rg3 & _). cbv zeta in Rg1, Rg3. unfold region_of in Rg1, Rg3.
                   change kRegionSize with 4294967296 in L1, L2. change kFreeArrayOffset with 3758096384 in Rg3. unfold kLargestClassID in Hc.
                   pose proof (ak_resv_geom _ _ _ Hkern) as (G1' & _ & G3'). change kSpaceSize with 137438953472 in G3'. change kPageSize with 4096 in G3'. change kResvLen with 137439023104 in G3'.
                   destruct WE12 as [X|X]; [right; apply Z.ltb_ge| left; apply Z.leb_gt]; subst a; clear -X GR L1 L2 Hc Rg1 Rg3 G1' G3'; nia.
                 - destruct (WS3 sc Hsc) as (_ & _ & _ & _ & _ & _ & SR). pose proof (SR _ WE9) as X. cbn [fst snd] in X.
                   destruct X as [X|X]; [left; apply Z.leb_gt| right; apply Z.ltb_ge]; clear -X GR L1 L2; lia. }
             replace (in_iarena E0 (8 * (z - 2147450880))) with false.
             2:{ symmetry. unfold in_iarena. apply Bool.andb_false_iff. unfold kIArenaLen in CBI |- *. destruct CBI as [X|X]; [left; apply Z.leb_gt| right; apply Z.ltb_ge]; clear -X GR; lia. }
             replace (in_reginfo E0 (8 * (z - 2147450880))) with false; [reflexivity|].
             symmetry. unfold in_reginfo. apply Bool.andb_false_iff. unfold kSpaceSize, kPageSize.
             destruct CBLOC as [(c & Hc & L1 & L2)|(sc & Hsc & L1 & L2)].
             ++ unfold region_beg in L1, L2. destruct (proj2 WR c Hc) as (Rg1 & Rg2 & Rg3 & _). cbv zeta in Rg1, Rg3. unfold region_of in Rg1, Rg3.
                change kRegionSize with 4294967296 in L1, L2. change kFreeArrayOffset with 3758096384 in Rg3. unfold kLargestClassID in Hc.
                left. apply Z.leb_gt. subst a. clear -GR L1 L2 Hc Rg1 Rg3. nia.
             ++ destruct (WS3 sc Hsc) as (_ & _ & _ & _ & _ & _ & SR). pose proof (SR _ WE7) as X. cbn [fst snd] in X.
                pose proof (ak_resv_geom _ _ _ Hkern) as (G1' & _ & G3'). change kSpaceSize with 137438953472 in G3'. change kPageSize with 4096 in G3'. change kResvLen with 137439023104 in G3', X.
                destruct X as [X|X]; [left; apply Z.leb_gt| right; apply Z.ltb_ge]; clear -X GR L1 L2 G1' G3'; lia.
      + subst W6. repeat (apply Forall_cons; [unfold aw_ok; cbn [fst snd]|]); [.. | apply Forall_nil].
        * left. clear -LO; lia.
        * do 3 right; left. change kResvLen with 137439023104. clear -Bb8 Bb9; lia.
        * do 3 right; left. change kResvLen with 137439023104. clear -Bb8 Bb9 BC8; lia.
        * right; right; left. exists (T + kThrQCache, 32). split; [unfold arep_thr_ranges; do 2 right; left; reflexivity| cbn [fst snd]; unfold kThrQCache; clear; lia].
    }
    { (* [comment removed for export] *)
      apply Forall_app; split; [apply Forall_app; split; [| exact (proj2 WDok)]|].
      + unfold AF_deallocT1.W15.
        repeat (apply Forall_cons; [cbn [fst snd]; intros blo bsz LIVEb NEb;
          destruct (live_block_where E0 a blo bsz Hwf LIVEb) as (Lw0 & Lw1 & Lw2 & Lw3); destruct (live_block_off_thread E0 a blo bsz Hwf LIVEb) as [_ BT];
          pose proof (live_apart_blk E0 [] [] a cb cm blo bsz Hwf Hcm LIVEb ltac:(rewrite UB; exact NEb)) as APT|]); [.. | apply Forall_nil].
        * right; right. clear -Lw1 LOC LO. lia.
        * right. clear -APT CG1 CG5. lia.
        * right. clear -APT CG1 CG5. lia.
        * right. clear -BT. lia.
        * right. unfold kShadowBase. rewrite KHB, KLE in Lw2. clear -Lw0 Lw2 CB0 CBC G8 HL8b CR. Z.div_mod_to_equations. lia.
      + subst W6.
        assert (INbq : In bq (as_tq a3 ++ as_gq a3)) by (rewrite Htq; apply in_app_iff; left; apply in_app_iff; right; left; reflexivity).
        assert (LIVE3 : forall blo bsz, In (blo, bsz) (live_blocks a) -> (blo, bsz) <> (cb + 16, cm_n cm) -> In (blo, bsz) (live_blocks a3)).
        { intros blo bsz LIVEb NEb. destruct (live_block_other E0 [] [] a cb cm blo bsz Hwf Hcm LIVEb ltac:(rewrite UB; exact NEb)) as (cb' & cm' & i & H' & NE' & <- & <- & ST').
          apply (chunk_live_in a3 cb' cm' i); [rewrite (Hoth3 cb' NE'); exact H'| exact ST']. }
        repeat (apply Forall_cons; [cbn [fst snd]; intros blo bsz LIVEb NEb;
          destruct (live_block_where E0 a blo bsz Hwf LIVEb) as (Lw0 & Lw1 & Lw2 & Lw3); destruct (live_block_off_thread E0 a blo bsz Hwf LIVEb) as [_ BT];
          pose proof (batch_vs_live E0 [cb] a3 bq blo bsz WF3 INbq (LIVE3 blo bsz LIVEb NEb)) as BV|]); [.. | apply Forall_nil].
        * right; right. clear -Lw1 LOC LO. lia.
        * right. clear -BV. lia.
        * right. clear -BV BC8. lia.
        * right. clear -BT. lia. }
  - (* [comment removed for export] *)
    set (cnt := qcount (as_tq a3)) in *.
    assert (HCNT : 0 <= cnt < 2^62).
    { destruct (snoc_case (as_tq a3)) as [E|(lq & bq & E)]; [subst cnt; rewrite E; unfold qcount; cbn [length Z.of_nat]; clear; lia|].
      pose proof (tq_weights E0 [cb] [] a3 lq bq WF3 E) as (_ & _ & _ & QW4 & _). unfold kBatchSize in QW4. subst cnt. unfold qcount in *. clear -QW4 TQB. lia. }
    assert (HQB : 0 <= tq_bytes a3 /\ tq_bytes a3 + cm_n cm + 8192 < 2^64).
    { split; [| clear -TQB N27 N40; lia]. destruct (snoc_case (as_tq a3)) as [E|(lq & bq & E)]; [unfold tq_bytes; rewrite E; cbn; clear; lia|].
      pose proof (tq_weights E0 [cb] [] a3 lq bq WF3 E) as (QW1 & QW2 & _). unfold kBatchSize in QW1. clear -QW1 QW2. lia. }
    (* [comment removed for export] *)
    assert (LASTX : cnt <> 0 -> exists lq bq, as_tq a3 = lq ++ [bq] /\ list_last (as_tq a3) = b_addr bq
              /\ rw_cells asegs m5 (b_addr bq) [C8 (wz 0); C8 (wz (b_size bq)); C8 (wz 1021)]
              /\ (kHighMemBeg <= b_addr bq /\ b_addr bq + 8192 <= alloc_ceiling /\ (b_addr bq + 8192 <= T \/ T + 4096 <= b_addr bq)
                  /\ ae_resv_beg E0 <= b_addr bq /\ b_addr bq + 8192 + 4096 <= ae_resv_beg E0 + 137439023104
                  /\ region_beg SB kBatchClass <= b_addr bq /\ b_addr bq + 8192 <= region_beg SB kBatchClass + rg_mapped_user (get_region a3 kBatchClass))
              /\ carved E0 a3 kBatchClass (b_addr bq) /\ ~ in_cache E0 a3 kBatchClass (b_addr bq) /\ In bq (as_tq a3 ++ as_gq a3)).
    { intros NZ. destruct (snoc_case (as_tq a3)) as [E|(lq & bq & E)]; [exfalso; apply NZ; subst cnt; rewrite E; reflexivity|].
      destruct (LASTF lq bq E) as (EL & _ & LB & _ & WB & _). pose proof WB as (CVb & _ & NICb & _ & CAPb & _).
      assert (FULL : zlen (b_items bq) = 1021).
      { rewrite E in NN. unfold neednew in NN. rewrite (List.last_last lq bq (mkBatch 0 [] 0)) in NN. destruct (lq ++ [bq]) eqn:E2; [destruct lq; discriminate|].
        apply Z.eqb_eq in NN. exact NN. }
      rewrite FULL in LB. pose proof (BLK _ CVb) as (Bb1 & Bb2 & Bb3 & Bb4 & Bb5 & Bb6 & Bb7 & Bb8 & Bb9 & Bb10).
      exists lq, bq. split; [exact E|]. split; [exact EL|]. split; [exact LB|]. split; [repeat split; assumption|].
      split; [exact CVb|]. split; [exact NICb|]. rewrite E. apply in_app_iff. left. apply in_app_iff. right. left. reflexivity. }
    assert (HSB : 0x603000 <= SB /\ SB mod 4096 = 0 /\ SB + kSpaceSize + 4096 <= alloc_ceiling).
    { pose proof WE3 as (_ & WEhi & WErs & _ & WEce & _). rewrite KHB in WEhi. unfold kSpaceSize. clear -WEhi WErs WEce G1 G2 G3. split; [lia|]. split; [Z.div_mod_to_equations; nia| lia]. }
    pose proof (rt_misc5_fsenv _ _ _ _ RT5) as FSE. assert (T8 : T mod 8 = 0) by (unfold FSEnv in FSE; decompose [and] FSE; assumption).
    assert (CR24 : get_cache a3 kBatchClass <> [] \/ get_cache a3 kBatchClass = []) by (destruct (get_cache a3 kBatchClass); [right; reflexivity| left; discriminate]).
    destruct CR24 as [NE24|EM24].
    + (* [comment removed for export] *)
      pose proof (proj1 (proj2 (proj2 WF3))) as WCc. pose proof WCc as (_ & WCIc & WC3c).
      assert (CI3 : as_cache_inited a3 = true).
      { destruct (as_cache_inited a3) eqn:CI0; [reflexivity| exfalso]. destruct (WCIc eq_refl) as [CE _]. apply NE24. unfold get_cache. rewrite CE. reflexivity. }
      rewrite CI3 in ROW5.
      set (l24 := get_cache a3 kBatchClass) in *. set (x := List.last l24 0).
      assert (HB24 : 1 <= kBatchClass <= kLargestClassID) by (unfold kBatchClass, kLargestClassID; clear; lia).
      destruct (WC3c kBatchClass HB24) as (WCL & _ & WCx). fold l24 in WCL, WCx.
      assert (LLEN : (1 <= length l24)%nat) by (clear -NE24; subst l24; destruct (get_cache a3 kBatchClass); [exfalso; exact (NE24 eq_refl)| cbn; lia]).
      set (cnt24 := zlen l24) in *.
      assert (C24 : 1 <= cnt24 <= 16) by (subst cnt24; unfold zlen; clear -LLEN CLEN5; lia).
      set (cws := map (fun z : Z => Z_to_bv 64 z) l24 ++ junk24) in CARR5.
      assert (CLEN : length cws = 16%nat) by (subst cws; rewrite length_app, length_map; exact CLEN5).
      assert (NTH : nth_error cws (Z.to_nat (cnt24 - 1)) = Some (Z_to_bv 64 x)).
      { subst cws cnt24 x. unfold zlen. replace (Z.to_nat (Z.of_nat (length l24) - 1)) with (Nat.pred (length l24)) by (clear -LLEN; lia).
        apply nth_error_map_app. apply last_nth_error. exact NE24. }
      assert (INx : In x l24) by (subst x; rewrite (app_removelast_last 0 NE24) at 2; apply in_app_iff; right; left; reflexivity).
      destruct (WCx x INx) as (CARVEDx & XAL & XNF).
      set (nb := bnew a3). assert (Enb0 : nb = chunk_of_compact SB kBatchClass x) by reflexivity.
      assert (Enb : nb = SB + 24 * 2^32 + 16 * x) by (rewrite Enb0; unfold chunk_of_compact, region_beg, kBatchClass, kRegionSize; clear; lia).
      rewrite <- Enb0 in CARVEDx. pose proof (BLK _ CARVEDx) as (Nb1 & Nb2 & Nb3 & Nb4 & Nb5 & Nb6 & Nb7 & Nb8 & Nb9 & Nb10).
      assert (XR : 0 <= x < 2^32).
      { pose proof CARVEDx as (kx & Kx0 & KxE & KxB). rewrite Enb in KxE. pose proof RG1' as RG1x. pose proof RG3' as RG3x.
        unfold region_of in KxB. unfold region_beg, kBatchClass in KxE, KxB, RG1x, RG3x. change kRegionSize with 4294967296 in KxE. change (class_size 24) with 8192 in KxE, KxB.
        clear -Kx0 KxE KxB RG1x RG3x. nia. }
      assert (INC : in_cache E0 a3 kBatchClass nb).
      { unfold in_cache. rewrite Enb0, compact_chunk_id. exact INx. }
      (* [comment removed for export] *)
      assert (HLo : cnt <> 0 -> kHighMemBeg <= list_last (as_tq a3) /\ list_last (as_tq a3) + 8192 <= alloc_ceiling
                /\ (list_last (as_tq a3) + 8192 <= T \/ T + 4096 <= list_last (as_tq a3)) /\ (list_last (as_tq a3) + 8192 <= nb \/ nb + 8192 <= list_last (as_tq a3))).
      { intros NZ. destruct (LASTX NZ) as (lq & bq & E & EL & _ & (L1 & L2 & L3 & _) & CVb & NICb & _). rewrite EL.
        split; [exact L1|]. split; [exact L2|]. split; [exact L3|].
        destruct (carved_blocks_disjoint E0 a3 kBatchClass (b_addr bq) kBatchClass nb HB24 HB24 (proj1 (proj2 WF3)) CVb CARVEDx) as [[_ EQ]|D].
        - exfalso. apply NICb. rewrite EQ. exact INC.
        - change (class_size kBatchClass) with 8192 in D. exact D. }
      set (lbsz := b_size (List.last (as_tq a3) (mkBatch 0 [] 0))).
      assert (LBo : cnt <> 0 -> rw_cells asegs m5 (list_last (as_tq a3)) [C8 (wz 0); C8 (wz lbsz); C8 (Z_to_bv 64 1021)]).
      { intros NZ. destruct (LASTX NZ) as (lq & bq & E & EL & LB & _). rewrite EL. subst lbsz. rewrite E, (List.last_last lq bq (mkBatch 0 [] 0)). exact LB. }
      set (alloc := as_cache_allocated a3 mod 2^64).
      assert (HAL : 0 <= alloc < 2^64) by (subst alloc; apply Z.mod_pos_bound; clear; lia).
      assert (CST5' : rw_cells asegs m5 (T + 2784) [C8 (wz alloc)]) by (subst alloc; rewrite Z_to_bv_mod64; exact CST5).
      assert (WRB5 : wr_at asegs m5 nb 8192).
      { pose proof REP3 as (_ & _ & Rrm3 & _). destruct (Rrm3 kBatchClass ltac:(unfold kBatchClass, kNumClasses; clear; lia)) as [WRu _].
        unfold region_of in WRu. eapply (wr_at_sub asegs m5 _ _ nb 8192 WRu); [exact Nb1| exact Nb2]. }
      set (DQh := fun ms6 => exists (t0' t1' t2' a1' a2' a5' a6' a7' : word) (m6 : mem) (junk : list word),
            ms6 = MS (mkR (wz 0x370b0) (wz (usp - 80)) gp tp t0' t1' t2' (wz (INST + 728)) (wz (T + 80)) (wz (T + 80)) a1' a2' (wz cb) (wz (cm_n cm + 8192)) a5' a6' a7'
                          (wz (cm_n cm)) (wz B) (wz (T + 208)) (wz cb) (wz 0x100000) s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x370b0) fc None m6 (seg_rom asegs)
            /\ mem_inv asegs m6 /\ stk asegs m6 lo (usp - 80) /\ wmono asegs m5 m6
            /\ munch [(usp - 144, usp - 80); (T + 80, T + 112); (T + 2128, T + 2132); (T + 2784, T + 2792); (nb, nb + 32); (list_last (as_tq a3), list_last (as_tq a3) + lz8 cnt)] m5 m6
            /\ rw_cells asegs m6 (T + 80) [C8 (wz (cnt + 1)); C8 (wz (if cnt =? 0 then nb else list_first (as_tq a3))); C8 (wz nb); C8 (wz (tq_bytes a3 + (cm_n cm + 8192)))]
            /\ rw_cells asegs m6 (T + 2128) [C4 (wz (cnt24 - 1)); C4 (wz (max_count kBatchClass)); C8 (wz 8192)]
            /\ rw_cells asegs m6 (T + 2784) [C8 (wz (alloc + 8192))]
            /\ rw_cells asegs m6 nb [C8 (wz 0); C8 (wz (cm_n cm + 8192)); C8 (wz 1)]
            /\ u64arr asegs m6 (nb + 24) (wz cb :: junk) /\ length junk = 1020%nat
            /\ (cnt <> 0 -> rw_cells asegs m6 (list_last (as_tq a3)) [C8 (wz nb); C8 (wz lbsz); C8 (wz 1021)])).
      eapply (rzA_seg_cfg asegs (aSc (sA a3 s)) (aNc (sA a3 s)) (aEBc (sA a3 s)) P3 DQh).
      { eapply (enq2_hit P3 (wz 0x370b0) (wz (usp - 80)) gp tp (wz (INST + 728)) (wz (T + 80)) (wz (cm_n cm)) (wz B) (wz (T + 208)) (wz cb) (wz 0x100000) s7 s8 s9 s10 s11 F fc DQh
                  lo T B cb (cm_n cm) cnt (list_first (as_tq a3)) (list_last (as_tq a3)) (tq_bytes a3) (wz 0) (wz lbsz) SB (ae_region_info E0) cnt24 x alloc (wz (max_count kBatchClass)) cws nb);
          rewrite ?Hsp;
          [ exact Enb | exact LOC | clear -LO; lia | clear -SPH LO LOC CR; lia | exact HTp3 | exact T8 | exact HSB | exact HCNT
          | clear -HQB; lia | exact XR | exact HAL | clear -Nb5 Nb3; split; [lia| lia] | exact Nb6 | exact HLo
          | exact PSTK | exact PDAT | exact PT
          | intros y k Y1 Y2; apply PUSR; [clear -Y1 Nb1; lia| clear -Y2 Nb2; lia]
          | intros NZ y k Y1 Y2; destruct (LASTX NZ) as (lq & bq & E & EL & _ & (_ & _ & _ & _ & _ & L6 & L7) & _); rewrite EL in Y1, Y2; apply PUSR; [clear -Y1 L6; lia| clear -Y2 L7; lia]
          | clear -HCNT; lia | exact C24 | exact CLEN | exact NTH | exact MI5 | exact SK5 | exact QC5 | exact ROW5 | exact CARR5 | exact CST5' | exact INS5 | exact WRB5 | exact LBo | ].
        intros m6 t0' t1' t2' a1' a2' a5' a6' a7' HP.
        destruct HP as (junk & MI6 & SK6 & WM6 & MU6 & QC6 & PC6 & ARR6 & STA6 & INS6 & NB6 & ITS6 & LJ6 & LB6).
        rewrite ?Hsp in SK6. unfold enq2W in MU6. rewrite ?Hsp in MU6. replace (usp - 80 - 64) with (usp - 144) in MU6 by (clear; lia).
        replace (ret_pc (wz 0x370b0)) with (wz 0x370b0 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
        apply evtA_done. unfold DQh. exists t0', t1', t2', a1', a2', a5', a6', a7', m6, junk.
        split; [reflexivity|]. split; [exact MI6|]. split; [exact SK6|]. split; [exact WM6|]. split; [exact MU6|]. split; [exact QC6|]. split; [exact PC6|].
        split; [exact STA6|]. split; [exact NB6|]. split; [exact ITS6|]. split; [exact LJ6| exact LB6]. }
      { exact KIP3. }
      intros ms6 mo6 HQ6 AG6 KIP6. unfold DQh in HQ6.
      destruct HQ6 as (t0' & t1' & t2' & a1' & a2' & a5' & a6' & a7' & m6 & junk & -> & MI6 & SK6 & WM6 & MU6 & QC6 & PC6 & STA6 & NB6 & ITS6 & LJ6 & LB6).
      (* [comment removed for export] *)
      pose proof (magree_frame _ _ AG6) as (Ffds6 & Fvm6 & Flz6 & Ffs6 & Fh6 & Ftid6 & _).
      destruct KIP6 as [KIA6 _].
      pose proof (RTOK_magree _ _ _ _ _ _ _ _ _ _ _ TOK3 AG6 KIA6) as TOK6.
      pose proof (AKern_frame _ _ _ _ Fvm6 Flz6 AK3) as AK6.
      assert (NZ : bnew a3 <> 0) by (fold nb; clear -Nb3 KHB; lia).
      pose proof (arun_enqueue_F2h a3 cb (cm_n cm) [] NN NE24 NZ) as RUNe.
      set (a4 := enq2_st a3 cb (cm_n cm)) in *.
      destruct (hoare_arun _ _ _ _ _ _ _ _ _ _ (enqueue_spec E0 [] a3 cb (cm_n cm) WF3 PEND3 ROOM3) eq_refl RUNe) as (WF4 & E4c & E4s & E4p & E4g & E4k & E4f).
      assert (AK4 : AKern E0 a4 mo6) by (apply (AKern_ext E0 a3); [reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| exact AK6]).
      assert (SFP34 : same_fp a3 a4) by (repeat split; reflexivity).
      assert (TOK4 : RTOKc (C - 1) (C' - DSLACK) (sA a4 s) mo6) by (eapply (RTOK_same_fp E0 FSB0 HR0 L0 RES0 EB0); [exact TOK6| exact SFP34| reflexivity| reflexivity]).
      destruct (RTOK_elim _ _ _ _ _ _ _ _ _ _ TOK4) as (R4 & R4' & ATK4 & _).
      pose proof (ATOK_KIA _ _ _ _ _ _ _ _ _ _ ATK4) as KIA4.
      (* [comment removed for export] *)
      assert (AG56 : forall z, 0 <= z < 2^64 -> (z + 1 <= usp - 144 \/ usp - 80 <= z) -> (z + 1 <= T + 80 \/ T + 112 <= z) -> (z + 1 <= T + 2128 \/ T + 2132 <= z)
                -> (z + 1 <= T + 2784 \/ T + 2792 <= z) -> (z + 1 <= nb \/ nb + 32 <= z) -> (z + 1 <= list_last (as_tq a3) \/ list_last (as_tq a3) + lz8 cnt <= z) -> m6 (wa z) = m5 (wa z)).
      { intros z Z0 Z1 Z2 Z3 Z4 Z5 Z6. apply MU6. rewrite wa_unsigned by (clear -Z0; lia). cbn [outside]. clear -Z1 Z2 Z3 Z4 Z5 Z6. repeat split; try exact I; lia. }
      assert (LZ : (cnt = 0 /\ lz8 cnt = 0 /\ as_tq a3 = []) \/ (cnt <> 0 /\ lz8 cnt = 8 /\ as_tq a3 <> [] /\ kHighMemBeg <= list_last (as_tq a3) /\ list_last (as_tq a3) + 8192 <= alloc_ceiling
                   /\ ae_resv_beg E0 <= list_last (as_tq a3) /\ list_last (as_tq a3) + 8192 + 4096 <= ae_resv_beg E0 + 137439023104 /\ (list_last (as_tq a3) + 8192 <= T \/ T + 4096 <= list_last (as_tq a3)))).
      { unfold lz8. destruct (Z.eq_dec cnt 0) as [C0|C1].
        - left. rewrite (proj2 (Z.eqb_eq cnt 0) C0). split; [exact C0|]. split; [reflexivity|]. apply TQ0. exact C0.
        - right. rewrite (proj2 (Z.eqb_neq cnt 0) C1). destruct (LASTX C1) as (lq & bq & E & EL & _ & (L1 & L2 & L3 & L4 & L5 & _) & _). rewrite EL.
          split; [exact C1|]. split; [reflexivity|]. split; [rewrite E; destruct lq; discriminate|]. repeat split; assumption. }
      (* [comment removed for export] *)
      assert (REP4 : ARep asegs E0 (DepotR asegs E0) a4 m6).
      { apply (R2F2 a3 m5 m6 lo cb (cm_n cm) [] junk NE24 CI3 PEND3 REP3 WF3 RENV3 WM6).
        - intros z Z0 NF. unfold FPWe2, kThrQCache, kThrCache, kPerClassSize, kThrCacheStats, kBatchClass in NF. fold nb in NF.
          apply AG56; [exact Z0| clear -NF LO; lia| clear -NF; lia| clear -NF; lia| clear -NF; lia| clear -NF; lia|].
          destruct LZ as [(C0 & -> & TQE)|(C1 & -> & TQN & _)]; [clear; lia|].
          assert (X : ~ (list_last (as_tq a3) <= z < list_last (as_tq a3) + 8)) by (intros H; apply NF; do 5 right; split; [exact TQN| exact H]). clear -X. lia.
        - exact LOC.
        - unfold kThrQCache. replace (match as_tq a3 with [] => bnew a3 | _ :: _ => list_first (as_tq a3) end) with (if cnt =? 0 then nb else list_first (as_tq a3)); [exact QC6|].
          fold nb. destruct LZ as [(C0 & _ & TQE)|(C1 & _ & TQN & _)]; [rewrite (proj2 (Z.eqb_eq cnt 0) C0), TQE; reflexivity| rewrite (proj2 (Z.eqb_neq cnt 0) C1)].
          destruct (as_tq a3); [exfalso; exact (TQN eq_refl)| reflexivity].
        - unfold kThrCache, kPerClassSize, kBatchClass. replace (T + 208 + 80 * 24) with (T + 2128) by (clear; lia).
          destruct (rwc_split asegs m6 (T + 2128) [C4 (wz (cnt24 - 1))] [C4 (wz (max_count 24)); C8 (wz 8192)] PC6) as [X _]. exact X.
        - unfold kThrCacheStats. replace (T + (208 + 2560) + 16) with (T + 2784) by (clear; lia). change (class_size kBatchClass) with 8192.
          replace (wz (as_cache_allocated a3 + 8192)) with (wz (alloc + 8192)); [exact STA6|].
          subst alloc. rewrite <- (Z_to_bv_mod64 (as_cache_allocated a3 mod 2 ^ 64 + 8192)), <- (Z_to_bv_mod64 (as_cache_allocated a3 + 8192)). f_equal.
          rewrite Zplus_mod_idemp_l. reflexivity.
        - exact NB6.
        - exact ITS6.
        - exact LJ6.
        - intros l0 b0 E. assert (C1 : cnt <> 0) by (subst cnt; rewrite E; unfold qcount; rewrite length_app; cbn [length]; clear; lia).
          destruct (rwc_split asegs m6 (list_last (as_tq a3)) [C8 (wz nb)] [C8 (wz lbsz); C8 (wz 1021)] (LB6 C1)) as [X _]. rewrite E, list_last_snoc in X. exact X. }
      (* [comment removed for export] *)
      assert (RT6 : rt_misc5 FSB0 PL0 E0 m6).
      { apply (rt_misc5_agree E0 FSB0 PL0 m5 m6 RT5). intros z Hz.
        destruct (rt_fpc_where2 E0 FSB0 PL0 z Hz) as [[ZI NM]|RH].
        - apply AG56; [clear -ZI; lia| clear -ZI LO LOC CR; lia| clear -ZI Timg Tlo; lia| clear -ZI Timg Tlo; lia| clear -ZI Timg Tlo; lia| clear -ZI Nb3 KHB; lia|].
          destruct LZ as [(_ & -> & _)|(_ & -> & _ & L1 & _)]; [clear; lia| clear -ZI L1 KHB; lia].
        - unfold rt_high2 in RH. apply AG56; [clear -RH Tlo Thi CQ1 CQ2 CC1 CC2 DQ1 DQ2 DD1 DD2 CR; lia| clear -RH LO LOC Thi CQ2 CC2 DQ2 DD2; lia| clear -RH CT DT; lia| clear -RH CT DT; lia| clear -RH CT DT; lia| |].
          + clear -RH Nb6 Nb8 Nb9 CRS DRS CC1 CC2 DD1 DD2 CIA WI4. lia.
          + destruct LZ as [(_ & -> & _)|(_ & -> & _ & L1 & L2 & L4 & L5 & L3)]; [clear; lia| clear -RH L3 L4 L5 CRS DRS CC1 CC2 DD1 DD2 CIA WI4; lia]. }
      (* [comment removed for export] *)
      set (WL := if cnt =? 0 then (@nil (Z * Z)) else [(list_last (as_tq a3), list_last (as_tq a3) + 8)]).
      set (W6 := [(usp - 144, usp - 80); (T + 80, T + 112); (T + 2128, T + 2132); (T + 2784, T + 2792); (nb, nb + 32)] ++ WL).
      assert (MU6' : munch W6 m5 m6).
      { eapply munch_weaken; [| exact MU6]. intros z Hz. subst W6 WL.
        destruct LZ as [(C0 & E0l & _)|(C1 & E1l & _)]; [rewrite (proj2 (Z.eqb_eq _ _) C0) in Hz| rewrite (proj2 (Z.eqb_neq _ _) C1) in Hz]; rewrite ?E0l, ?E1l;
          cbn [outside app] in Hz |- *; clear -Hz; repeat split; try exact I; lia. }
      assert (MU06 : munch ((W15 usp cb (cm_n cm) ++ Wd) ++ W6) m m6).
      { eapply munch_trans; [eapply munch_weaken; [| exact MU5]| eapply munch_weaken; [| exact MU6']]; intros z Hz;
          apply (proj2 (outside_forall _ _)); intros lo' hi' Hin; apply (proj1 (outside_forall _ _) Hz); apply in_app_iff; [left| right]; exact Hin. }
      (* [comment removed for export] *)
      assert (CBAW : forall x0 y0, cb <= x0 -> y0 <= cb + 16 + rounded (cm_n cm) ->
                (ae_resv_beg E0 <= x0 /\ y0 <= ae_resv_beg E0 + kResvLen) \/ (exists sc, (In sc (as_sec a) \/ In sc (as_sec a4)) /\ sc_map_beg sc <= x0 /\ y0 <= sc_map_beg sc + sc_map_size sc)).
      { intros x0 y0 X1 Y1. destruct CBLOC as [(c & Hc & L1 & L2)|(sc & Hsc & L1 & L2)].
        - left. unfold region_beg in L1, L2. destruct (proj2 WR c Hc) as (Rg1 & Rg2 & Rg3 & _). cbv zeta in Rg1, Rg3. unfold region_of in Rg1, Rg3.
          change kRegionSize with 4294967296 in L1, L2. change kFreeArrayOffset with 3758096384 in Rg3. unfold kLargestClassID in Hc. change kResvLen with 137439023104.
          pose proof (ak_resv_geom _ _ _ Hkern) as (G1' & _ & G3'). change kSpaceSize with 137438953472 in G3'. change kPageSize with 4096 in G3'. change kResvLen with 137439023104 in G3'.
          subst a. clear -X1 Y1 L1 L2 Hc Rg1 Rg3 G1' G3'. nia.
        - right. exists sc. split; [left; exact Hsc| clear -X1 Y1 L1 L2; lia]. }
      assert (HL8b : 8 * ((cm_n cm + 7) / 8) < cm_n cm + 8 /\ cm_n cm <= rounded (cm_n cm)) by (clear -N40 RG1; Z.div_mod_to_equations; lia).
      assert (G8 : 8 * ((cb + 16) / 8) = cb + 16) by (clear -P16; Z.div_mod_to_equations; lia).
      pose proof (qc_enq2 a3 cb (cm_n cm)) as (Etq4 & Eqc4 & Efst4 & Elst4 & Eby4). fold a4 nb in Etq4, Eqc4, Efst4, Elst4, Eby4.
      (* [comment removed for export] *)
      unfold QE_post in QPOST.
      eapply (QPOST t0' t1' t2' (wz (T + 80)) a1' a2' (wz cb) (wz (cm_n cm + 8192)) a5' a6' a7' t3 t4 t5 t6 m6 mo6 a2 a4 cm aid fid);
        [ exact Hcm | exact ST | exact UB | exact RUN | exact FID | exact DS2 | exact ND2
        | exists 0%nat, [], [], []; exact RUNe
        | (* [comment removed for export] *) unfold a4, enq2_st, bpop_st, bnew, a3, AsanRepFlip.s3;
          cbn [as_chunks as_sec as_ptr_committed as_gq as_nprim_ever as_residue as_ndepot_ins as_node_blocks as_store_blocks as_sec_stats upd_tq upd_cache_allocated upd_cache_stale set_cache upd_chunks];
          repeat split; first [reflexivity| exact D8| exact D7| exact D17| exact D20| exact D19| exact D10]
        | exact WF4 | exact REP4 | exact AK4 | exact TOK4 | exact KIA4
        | (* [comment removed for export] *) apply (res_ok_frame a3); [cbn; intros sc H; exact H| cbn; apply incl_refl| exact RES3]
        | (* [comment removed for export] *) exact (proj2 QB3)
        | (* [comment removed for export] *) rewrite Eby4; unfold kThreadQuarantineMax, kBatchSize; clear -HQB TQB N40 N27; lia
        | (* [comment removed for export] *) revert DI3; clear; unfold depot_inv, depot_n_ids, dphi; exact (fun H => H)
        | (* [comment removed for export] *) revert SS3; clear; unfold sstats_ok, sec_bytes; exact (fun H => H)
        | (* [comment removed for export] *) intros cbx cmx Hx; apply (CS3 cbx cmx); revert Hx; unfold a4, enq1_st, enq2_st, bpop_st; cbn [as_chunks upd_tq upd_cache_allocated upd_cache_stale set_cache]; exact (fun H => H)
        | rewrite Ffs6; exact Ffs5 | rewrite Ffds6; exact Ffds5 | rewrite Ftid6; exact Ftid5
        | exact MI6 | exact SK6 | exact (wmono_trans _ _ _ _ WM5 WM6) | exact RT6
        | (* [comment removed for export] *)
        | (* [comment removed for export] *) eapply AF_unwind.rw_cells_agree; [| exact PF5]; cbn -[Z.add Z.mul Z.of_nat Z.sub Z.div]; intros z Hz;
          apply AG56; [clear -Hz LO LOC CR USPR; lia| clear -Hz; lia| clear -Hz Thi LO LOC; lia| clear -Hz Thi LO LOC; lia| clear -Hz Thi LO LOC; lia| clear -Hz Nb4 LO LOC; lia|];
          destruct LZ as [(_ & -> & _)|(_ & -> & _ & _ & L2 & _)]; [clear; lia| clear -Hz L2 LO LOC; lia]
        | (* [comment removed for export] *) rewrite Eqc4, Efst4, Elst4, Eby4; unfold kBatchSize;
          replace (match as_tq a3 with [] => nb | _ :: _ => list_first (as_tq a3) end) with (if cnt =? 0 then nb else list_first (as_tq a3));
          [replace (tq_bytes a3 + (8192 + cm_n cm)) with (tq_bytes a3 + (cm_n cm + 8192)) by (clear; lia); exact QC6|];
          destruct LZ as [(C0 & _ & TQE)|(C1 & _ & TQN & _)]; [rewrite (proj2 (Z.eqb_eq cnt 0) C0), TQE; reflexivity| rewrite (proj2 (Z.eqb_neq cnt 0) C1)];
          destruct (as_tq a3); [exfalso; exact (TQN eq_refl)| reflexivity] ].
      (* [comment removed for export] *)
      exists ((W15 usp cb (cm_n cm) ++ Wd) ++ W6). split; [exact MU06|].
      assert (WDok : Forall (aw_ok E0 a a4 lo usp) Wd /\ Forall (fun iv => forall blo bsz, In (blo, bsz) (live_blocks a) -> (blo, bsz) <> (cb + 16, cm_n cm) -> snd iv <= fst iv \/ snd iv <= blo \/ blo + bsz <= fst iv) Wd).
      { split; apply Forall_forall; intros [x0 y0] Hin; pose proof (proj1 (Forall_forall _ _) FWd _ Hin) as X; unfold dput_w_ok in X; cbn [fst snd] in X.
        - unfold aw_ok. cbn [fst snd]. destruct X as [X|[(r & Hr & X1 & X2)|[(b & Hb & X1 & X2)|(b & Hb & X1 & X2)]]].
          + left. clear -X; lia.
          + right; left. unfold depot_static in Hr. rewrite IC0 in Hr. cbn [aic_theDepot aic_stackStore asan_ic] in Hr.
            destruct Hr as [<-|[<-|[]]]; cbn [fst snd] in X1, X2.
            * exists (aic_theDepot asan_ic, 0x440010). split; [unfold img_mut; do 3 right; left; reflexivity| cbn [fst snd aic_theDepot asan_ic]; clear -X1 X2; lia].
            * exists (aic_stackStore asan_ic, 0x10010). split; [unfold img_mut; do 4 right; left; reflexivity| cbn [fst snd aic_stackStore asan_ic]; clear -X1 X2; lia].
          + do 6 right; left. exists b. split; [| clear -X1 X2; lia]. revert Hb. unfold a4, enq2_st, bpop_st, a3, AsanRepFlip.s3. cbn [as_node_blocks upd_tq upd_cache_allocated upd_cache_stale set_cache upd_chunks]. exact (fun H => H).
          + do 7 right; left. exists b. split; [| clear -X1 X2; lia]. revert Hb. unfold a4, enq2_st, bpop_st, a3, AsanRepFlip.s3. cbn [as_store_blocks upd_tq upd_cache_allocated upd_cache_stale set_cache upd_chunks]. exact (fun H => H).
        - intros blo bsz LIVEb NEb. cbn [fst snd]. destruct (live_block_where E0 a blo bsz Hwf LIVEb) as (Lw0 & Lw1 & Lw2 & Lw3). destruct (live_block_off_thread E0 a blo bsz Hwf LIVEb) as [_ BT].
          destruct X as [X|X]; [right; right; clear -X Lw1 LOC LO; lia|].
          assert (DZ : forall z, x0 <= z < y0 -> DepotFPd E0 a2 z).
          { intros z Hz. destruct X as [(r & Hr & X1 & X2)|[(b & Hb & X1 & X2)|(b & Hb & X1 & X2)]].
            - left. exists r. split; [unfold depot_static in Hr; destruct Hr as [<-|[<-|[]]]; [left| right; left]; reflexivity| clear -Hz X1 X2; lia].
            - right; left. exists b. split; [exact Hb| clear -Hz X1 X2; lia].
            - right; right. exists b. split; [exact Hb| clear -Hz X1 X2; lia]. }
          destruct (Z_lt_le_dec x0 y0) as [O0|O0]; [| left; exact O0]. destruct (Z_lt_le_dec blo y0) as [O1|O1]; [| right; left; exact O1]. destruct (Z_lt_le_dec x0 (blo + bsz)) as [O2|O2]; [| right; right; exact O2]. exfalso.
          set (z := Z.max x0 blo).
          assert (Zin : x0 <= z < y0 /\ blo <= z < blo + bsz) by (subst z; clear -O0 O1 O2 Lw0; lia).
          pose proof WE as (_ & WEhi & WErs & WEsp & _). change kSpaceSize with 137438953472 in WEsp.
          destruct (dfp_cases E0 PL0 ENV0 PL0OK a2 mo5 z IC0 AK2 WF2 EI1 EI2 (DZ z (proj1 Zin))) as [STz|(b & bl & R & Bb0 & Bce & Bbd & Brs & Bsc & BTb & BAb)].
          + destruct Lw3 as [[S1 S2]|(sc & Hsc & S1 & S2)]; [rewrite KHB in WEhi; clear -STz Zin S1 WEhi WErs; lia|].
            destruct (WS3 sc Hsc) as (_ & _ & _ & _ & _ & _ & SR). pose proof (SR _ (proj1 (wf_env_img _ WE))) as X1. rewrite EI1 in X1. cbn [fst snd] in X1. clear -STz Zin S1 S2 X1 EI2. lia.
          + change kResvLen with 137439023104 in Brs.
            destruct Lw3 as [[S1 S2]|(sc & Hsc & S1 & S2)]; [unfold kSpaceSize in S2; clear -R Zin S1 S2 Brs WErs WEsp; lia|].
            rewrite D8 in Bsc. destruct (Bsc sc Hsc); clear -R Zin S1 S2 H; lia. }
      pose proof (chunk_geo E0 [] [] a cb cm Hwf Hcm) as (CG1 & CG2 & CG3 & CG4 & CG5). rewrite UB in CG1, CG2, CG4, CG5.
      pose proof WE as (_ & WEhi & WErs & WEsp & _ & _ & WE7 & _ & WE9 & _ & _ & WE12 & _). change kSpaceSize with 137438953472 in WEsp. rewrite KHB in WEhi.
      split.
      { (* [comment removed for export] *)
        apply Forall_app; split; [apply Forall_app; split; [| exact (proj1 WDok)]|].
        + unfold AF_deallocT1.W15. repeat (apply Forall_cons; [unfold aw_ok; cbn [fst snd]|]); [.. | apply Forall_nil].
          * left. clear -LO; lia.
          * destruct (CBAW cb (cb + 4) ltac:(clear; lia) ltac:(clear -RG1; lia)) as [X|X]; [do 3 right; left; exact X| do 5 right; left; exact X].
          * destruct (CBAW (cb + 16) (cb + 24) ltac:(clear; lia) ltac:(clear -RG1; lia)) as [X|X]; [do 3 right; left; exact X| do 5 right; left; exact X].
          * right; right; left. exists (T + kThrStats, 112 + 8 * 32). split; [unfold arep_thr_ranges; do 5 right; left; reflexivity| cbn [fst snd]; unfold kThrStats; clear; lia].
          * do 8 right. split.
            -- unfold LSHI, A_base.A_SB, kShadowBase. rewrite ?KHB, ?KLE. rewrite KHB, KLE in CBB.
               destruct CBB as [LOW|HIGH]; [left; clear -LOW CB0 G8 HL8b RG1 CR| right; clear -HIGH CB0 CBC G8 HL8b RG1 CR]; Z.div_mod_to_equations; lia.
            -- intros z Hz. unfold A_base.A_SB, kShadowBase in *.
               assert (GR : cb + 16 <= 8 * (z - 2147450880) < cb + 16 + rounded (cm_n cm)) by (clear -Hz G8 HL8b; Z.div_mod_to_equations; lia).
               unfold sh_excluded.
               replace (in_fakestack E0 (8 * (z - 2147450880))) with false.
               2:{ symmetry. unfold in_fakestack. apply Bool.andb_false_iff.
                   destruct CBLOC as [(c & Hc & L1 & L2)|(sc & Hsc & L1 & L2)].
                   - unfold region_beg in L1, L2. destruct (proj2 WR c Hc) as (Rg1 & Rg2 & Rg3 & _). cbv zeta in Rg1, Rg3. unfold region_of in Rg1, Rg3.
                     change kRegionSize with 4294967296 in L1, L2. change kFreeArrayOffset with 3758096384 in Rg3. unfold kLargestClassID in Hc.
                     pose proof (ak_resv_geom _ _ _ Hkern) as (G1' & _ & G3'). change kSpaceSize with 137438953472 in G3'. change kPageSize with 4096 in G3'. change kResvLen with 137439023104 in G3'.
                     destruct WE12 as [X|X]; [right; apply Z.ltb_ge| left; apply Z.leb_gt]; subst a; clear -X GR L1 L2 Hc Rg1 Rg3 G1' G3'; nia.
                   - destruct (WS3 sc Hsc) as (_ & _ & _ & _ & _ & _ & SR). pose proof (SR _ WE9) as X. cbn [fst snd] in X.
                     destruct X as [X|X]; [left; apply Z.leb_gt| right; apply Z.ltb_ge]; clear -X GR L1 L2; lia. }
               replace (in_iarena E0 (8 * (z - 2147450880))) with false.
               2:{ symmetry. unfold in_iarena. apply Bool.andb_false_iff. unfold kIArenaLen in CBI |- *. destruct CBI as [X|X]; [left; apply Z.leb_gt| right; apply Z.ltb_ge]; clear -X GR; lia. }
               replace (in_reginfo E0 (8 * (z - 2147450880))) with false; [reflexivity|].
               symmetry. unfold in_reginfo. apply Bool.andb_false_iff. unfold kSpaceSize, kPageSize.
               destruct CBLOC as [(c & Hc & L1 & L2)|(sc & Hsc & L1 & L2)].
               ++ unfold region_beg in L1, L2. destruct (proj2 WR c Hc) as (Rg1 & Rg2 & Rg3 & _). cbv zeta in Rg1, Rg3. unfold region_of in Rg1, Rg3.
                  change kRegionSize with 4294967296 in L1, L2. change kFreeArrayOffset with 3758096384 in Rg3. unfold kLargestClassID in Hc.
                  left. apply Z.leb_gt. subst a. clear -GR L1 L2 Hc Rg1 Rg3. nia.
               ++ destruct (WS3 sc Hsc) as (_ & _ & _ & _ & _ & _ & SR). pose proof (SR _ WE7) as X. cbn [fst snd] in X.
                  pose proof (ak_resv_geom _ _ _ Hkern) as (G1' & _ & G3'). change kSpaceSize with 137438953472 in G3'. change kPageSize with 4096 in G3'. change kResvLen with 137439023104 in G3', X.
                  destruct X as [X|X]; [left; apply Z.leb_gt| right; apply Z.ltb_ge]; clear -X GR L1 L2 G1' G3'; lia.
        + subst W6. apply Forall_app. split.
          * repeat (apply Forall_cons; [unfold aw_ok; cbn [fst snd]|]); [.. | apply Forall_nil].
            -- left. clear -LO; lia.
            -- right; right; left. exists (T + kThrQCache, 32). split; [unfold arep_thr_ranges; do 2 right; left; reflexivity| cbn [fst snd]; unfold kThrQCache; clear; lia].
            -- right; right; left. exists (T + kThrCache, kPerClassSize * kNumClasses). split; [unfold arep_thr_ranges; do 3 right; left; reflexivity| cbn [fst snd]; unfold kThrCache, kPerClassSize, kNumClasses; clear; lia].
            -- right; right; left. exists (T + kThrCacheStats + 16, 16). split; [unfold arep_thr_ranges; do 4 right; left; reflexivity| cbn [fst snd]; unfold kThrCacheStats; clear; lia].
            -- do 3 right; left. change kResvLen with 137439023104. clear -Nb8 Nb9; lia.
          * subst WL. destruct LZ as [(C0 & _ & _)|(C1 & _ & _ & L1 & L2 & L4 & L5 & L3)]; [rewrite (proj2 (Z.eqb_eq cnt 0) C0); apply Forall_nil| rewrite (proj2 (Z.eqb_neq cnt 0) C1)].
            apply Forall_cons; [unfold aw_ok; cbn [fst snd]| apply Forall_nil]. do 3 right; left. change kResvLen with 137439023104. clear -L4 L5; lia. }
      { (* [comment removed for export] *)
        assert (LIVE3 : forall blo bsz, In (blo, bsz) (live_blocks a) -> (blo, bsz) <> (cb + 16, cm_n cm) -> In (blo, bsz) (live_blocks a3)).
        { intros blo bsz LIVEb NEb. destruct (live_block_other E0 [] [] a cb cm blo bsz Hwf Hcm LIVEb ltac:(rewrite UB; exact NEb)) as (cb' & cm' & i & H' & NE' & <- & <- & ST').
          apply (chunk_live_in a3 cb' cm' i); [rewrite (Hoth3 cb' NE'); exact H'| exact ST']. }
        apply Forall_app; split; [apply Forall_app; split; [| exact (proj2 WDok)]|].
        + unfold AF_deallocT1.W15.
          repeat (apply Forall_cons; [cbn [fst snd]; intros blo bsz LIVEb NEb;
            destruct (live_block_where E0 a blo bsz Hwf LIVEb) as (Lw0 & Lw1 & Lw2 & Lw3); destruct (live_block_off_thread E0 a blo bsz Hwf LIVEb) as [_ BT];
            pose proof (live_apart_blk E0 [] [] a cb cm blo bsz Hwf Hcm LIVEb ltac:(rewrite UB; exact NEb)) as APT|]); [.. | apply Forall_nil].
          * right; right. clear -Lw1 LOC LO. lia.
          * right. clear -APT CG1 CG5. lia.
          * right. clear -APT CG1 CG5. lia.
          * right. clear -BT. lia.
          * right. unfold kShadowBase. rewrite KHB, KLE in Lw2. clear -Lw0 Lw2 CB0 CBC G8 HL8b CR. Z.div_mod_to_equations. lia.
        + subst W6. apply Forall_app. split.
          * repeat (apply Forall_cons; [cbn [fst snd]; intros blo bsz LIVEb NEb;
              destruct (live_block_where E0 a blo bsz Hwf LIVEb) as (Lw0 & Lw1 & Lw2 & Lw3); destruct (live_block_off_thread E0 a blo bsz Hwf LIVEb) as [_ BT];
              pose proof (cache_vs_live E0 [cb] [] a3 kBatchClass x blo bsz WF3 HB24 INx (LIVE3 blo bsz LIVEb NEb)) as CVL; rewrite <- Enb0 in CVL; change (class_size kBatchClass) with 8192 in CVL|]); [.. | apply Forall_nil].
            -- right; right. clear -Lw1 LOC LO. lia.
            -- right. clear -BT. lia.
            -- right. clear -BT. lia.
            -- right. clear -BT. lia.
            -- right. clear -CVL. lia.
          * subst WL. destruct LZ as [(C0 & _ & _)|(C1 & _ & TQN & _)]; [rewrite (proj2 (Z.eqb_eq cnt 0) C0); apply Forall_nil| rewrite (proj2 (Z.eqb_neq cnt 0) C1)].
            apply Forall_cons; [cbn [fst snd]| apply Forall_nil]. intros blo bsz LIVEb NEb.
            destruct (LASTX C1) as (lq & bq & E & EL & _ & _ & _ & _ & INbq). rewrite EL.
            pose proof (batch_vs_live E0 [cb] a3 bq blo bsz WF3 INbq (LIVE3 blo bsz LIVEb NEb)) as BV. right. clear -BV. lia. }
    + (* [comment removed for export] *)
      rewrite EM24 in ROW5. change (zlen []) with 0 in ROW5.
      set (lbsz := b_size (List.last (as_tq a3) (mkBatch 0 [] 0))).
      assert (LBo : cnt <> 0 -> rw_cells asegs m5 (list_last (as_tq a3)) [C8 (wz 0); C8 (wz lbsz); C8 (Z_to_bv 64 1021)]).
      { intros NZ. destruct (LASTX NZ) as (lq & bq & E & EL & LB & _). rewrite EL. subst lbsz. rewrite E, (List.last_last lq bq (mkBatch 0 [] 0)). exact LB. }
      assert (HB24 : 1 <= kBatchClass <= kLargestClassID) by (unfold kBatchClass, kLargestClassID; clear; lia).
      (* [comment removed for export] *)
      set (xph := 268434944). set (nbph := SB + 24 * 2^32 + 16 * xph).
      assert (PH : nbph + 8192 <= SB + kSpaceSize /\ kHighMemBeg <= nbph /\ (nbph + 8192 <= T \/ T + 4096 <= nbph)
                 /\ (cnt <> 0 -> kHighMemBeg <= list_last (as_tq a3) /\ list_last (as_tq a3) + 8192 <= alloc_ceiling
                       /\ (list_last (as_tq a3) + 8192 <= T \/ T + 4096 <= list_last (as_tq a3)) /\ (list_last (as_tq a3) + 8192 <= nbph \/ nbph + 8192 <= list_last (as_tq a3)))).
      { pose proof WE3 as (_ & WEhi & WErs & WEsp & WEce & _). rewrite KHB in WEhi. change kSpaceSize with 137438953472 in WEsp. change kResvLen with 137439023104 in G3.
        subst nbph xph. unfold kSpaceSize. rewrite KHB.
        split; [clear -G3; lia|]. split; [clear -WEhi G1; lia|]. split; [clear -WT4 G1 G3; lia|].
        intros NZ. destruct (LASTX NZ) as (lq & bq & E & EL & _ & (L1 & L2 & L3 & L4 & L5 & L6 & L7) & _). rewrite EL.
        split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. left. pose proof RG3' as RG3x. unfold region_beg, kBatchClass in L7, RG3x. change kRegionSize with 4294967296 in L7. clear -L7 RG3x. lia. }
      destruct PH as (PH1 & PH2 & PH3 & PH4).
      set (DQm := fun ms6 => exists (a6' a7' : word) (j8 : list byte) (m6 : mem),
            ms6 = MS (mkR (wz 0x37210) (wz (usp - 144)) gp tp t0 t1 t2 (wz (T + 2128)) (wz (T + 208)) (wz (T + 208)) (wz (T + 2128)) (wz INST) (wz 24) (wz (cm_n cm)) (wz INST) a6' a7'
                          (wz cb) (wz (T + 80)) (wz B) (wz (cm_n cm)) (wz 0x100000) s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x379f0) fc None m6 (seg_rom asegs)
            /\ mem_inv asegs m6 /\ stk asegs m6 lo (usp - 144) /\ wmono asegs m5 m6 /\ munch [(usp - 144, usp - 80)] m5 m6
            /\ rw_cells asegs m6 (usp - 144) [CB 8 j8; C8 (wz cb); C8 (wz (T + 208)); C8 (wz B); C8 (wz (cm_n cm)); C8 (wz (T + 80)); C8 (wz (INST + 728)); C8 (wz 0x370b0)]).
      eapply (rzA_seg_cfg asegs (aSc (sA a3 s)) (aNc (sA a3 s)) (aEBc (sA a3 s)) P3 DQm).
      { eapply (enq2_miss_front P3 (wz 0x370b0) (wz (usp - 80)) gp tp (wz (INST + 728)) (wz (T + 80)) (wz (cm_n cm)) (wz B) (wz (T + 208)) (wz cb) (wz 0x100000) s7 s8 s9 s10 s11 F fc DQm
                  lo T B cb (cm_n cm) cnt (list_first (as_tq a3)) (list_last (as_tq a3)) (tq_bytes a3) (wz 0) (wz lbsz) SB xph 0 (wz (if as_cache_inited a3 then max_count kBatchClass else 0)) nbph);
          rewrite ?Hsp;
          [ exact LOC | clear -LO; lia | clear -SPH LO LOC CR; lia | exact HTp3 | exact HSB | exact HCNT
          | clear -HQB; lia | subst xph; clear; lia | clear; lia | exact (conj PH1 PH2) | exact PH3 | exact PH4
          | exact PSTK | exact PT
          | intros NZ y k Y1 Y2; destruct (LASTX NZ) as (lq & bq & E & EL & _ & (_ & _ & _ & _ & _ & L6 & L7) & _); rewrite EL in Y1, Y2; apply PUSR; [clear -Y1 L6; lia| clear -Y2 L7; lia]
          | clear -HCNT; lia | exact MI5 | exact SK5 | exact QC5 | exact ROW5 | exact LBo | ].
        intros m6 a6' a7' j8 MI6 SK6 FR6 MU6 WM6 QC6 PC6 LB6.
        rewrite ?Hsp in SK6. rewrite ?Hsp in MU6. unfold enq_frame in FR6. rewrite ?Hsp in FR6.
        replace (usp - 80 - 64) with (usp - 144) in SK6 by (clear; lia). replace (usp - 80 - 64) with (usp - 144) in MU6 by (clear; lia). replace (usp - 80 - 64) with (usp - 144) in FR6 by (clear; lia).
        apply evtA_done. unfold DQm. exists a6', a7', j8, m6.
        split; [unfold enq2_refill_call; rewrite ?Hsp; replace (usp - 80 - 64) with (usp - 144) by (clear; lia); reflexivity|].
        split; [exact MI6|]. split; [exact SK6|]. split; [exact WM6|]. split; [exact MU6| exact FR6]. }
      { exact KIP3. }
      intros ms6 mo6 HQ6 AG6 KIP6. unfold DQm in HQ6.
      destruct HQ6 as (a6' & a7' & j8 & m6 & -> & MI6 & SK6 & WM6 & MU6 & FR6).
      pose proof (magree_frame _ _ AG6) as (Ffds6 & Fvm6 & Flz6 & Ffs6 & Fh6 & Ftid6 & _).
      destruct KIP6 as [KIA6 _].
      pose proof (RTOK_magree _ _ _ _ _ _ _ _ _ _ _ TOK3 AG6 KIA6) as TOK6.
      pose proof (AKern_frame _ _ _ _ Fvm6 Flz6 AK3) as AK6.
      assert (AG56 : forall z, 0 <= z < 2^64 -> (z + 1 <= usp - 144 \/ usp - 80 <= z) -> m6 (wa z) = m5 (wa z)).
      { intros z Z0 Z1. apply MU6. rewrite wa_unsigned by (clear -Z0; lia). cbn [outside]. clear -Z1. repeat split; try exact I; lia. }
      assert (REP6 : ARep asegs E0 (DepotR asegs E0) a3 m6).
      { apply (ARep_high_agree [cb] [] a3 m5 m6 lo REP3 WF3 RENV3 LOC WM6). intros z Z0 Z1. apply AG56; [exact Z0| clear -Z1 LO; lia]. }
      assert (RT6 : rt_misc5 FSB0 PL0 E0 m6).
      { apply (rt_misc5_agree E0 FSB0 PL0 m5 m6 RT5). intros z Hz.
        destruct (rt_fpc_where2 E0 FSB0 PL0 z Hz) as [[ZI NM]|RH]; [apply AG56; [clear -ZI; lia| clear -ZI LO LOC CR; lia]|].
        unfold rt_high2 in RH. apply AG56; [clear -RH Tlo Thi CQ1 CQ2 CC1 CC2 DQ1 DQ2 DD1 DD2 CR; lia| clear -RH LO LOC Thi CQ2 CC2 DQ2 DD2; lia]. }
      pose proof FB as (BU1 & BU2 & BU3). unfold kInitialCredit in BU3.
      assert (NP12 : 0 <= as_nprim_ever a3 <= 12000) by (rewrite Enp3; clear -BU1 BU2 BU3; lia).
      (* [comment removed for export] *)
      replace (Z_to_bv 64 (T + 2128)) with (Z_to_bv 64 (T + kThrCache + kPerClassSize * kBatchClass)) by (unfold kThrCache, kPerClassSize, kBatchClass; f_equal; clear; lia).
      eapply (REFILL (wz 0x37210) (wz (usp - 144)) gp tp t0 t1 t2 (wz (T + kThrCache + kPerClassSize * kBatchClass)) (wz (T + 208)) (wz (cm_n cm)) (wz INST) a6' a7' (wz cb) (wz (T + 80)) (wz B) (wz (cm_n cm)) (wz 0x100000)
                s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m6 mo6 (sA a3 s) [cb] [] kBatchClass lo (C - 1) (C' - DSLACK) K KN);
        rewrite ?(AF_deallocT1.aps_alloc_sA');
        [ exact TOK6
        | split; [exact REP6|]; split; [exact WF3|]; split; [exact AK6|]; split; [exact RES3|]; split; [exact QB3|]; split; [exact DI3|]; split; [exact MI6|]; split; [exact RT6|]; split; [exact SS3| exact CS3]
        | exact HB24 | exact EM24 | exact RROOM3 | exact NP12
        | rewrite (unsigned_lit (usp - 144)) by (clear -USPR LO LOC CR; lia); exact SK6
        | exact LOC
        | rewrite (unsigned_lit (usp - 144)) by (clear -USPR LO LOC CR; lia); unfold K_REFILL; clear -LO; lia
        | rewrite (unsigned_lit (usp - 144)) by (clear -USPR LO LOC CR; lia); clear -SPA; Z.div_mod_to_equations; lia
        | rewrite (unsigned_lit (usp - 144)) by (clear -USPR LO LOC CR; lia); clear -SPH SPA; Z.div_mod_to_equations; lia
        | exact TP | ].
      intros t0' t1' t2' a1' a2' a3' a4' a5' a6'' a7'' t3' t4' t5' t6' m8 mo8 a3r RP.
      rewrite (unsigned_lit (usp - 144)) in RP by (clear -USPR LO LOC CR; lia).
      destruct RP as (SK8 & WM68 & (Wr & MUr & FWr & FLr) & RUNr & RINV8 & TOK8 & Ffs8 & Ffds8 & Ftid8 & RSAME & ROTH & CI8 & HINT8).
      pose proof RINV8 as (REP8 & WF8 & AK8 & RES8 & QB8 & DI8 & MI8 & RT8 & SS8 & CS8).
      replace (ret_pc (wz 0x37210)) with (wz 0x37210 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
      pose proof RSAME as (Rch & Rdd & Rtq & Rgq & Rsec & Rsst & Rsss & Rptr & Rkeys & Rfr & Rnd & Rnp & Rres & Rnb & Rsb & Rstd & Ria & Rcal & Revc & Rga & Rgm & Room).
      change (hint kBatchClass) with 1 in HINT8.
      change (sA a3r (sA a3 s)) with (sA a3r s) in TOK8.
      pose proof (magree_frame _ _ AG6) as MF6.
      (* [comment removed for export] *)
      assert (BS8 : blocks_sep E0 a3r) by (apply (blocks_sep_ext E0 a3 a3r); [exact Rnb| exact Rsb| exact Rsec| exact (proj1 RENV3)]).
      assert (RENV8 : renv_ok a3r).
      { split; [exact BS8|]. pose proof RENV3 as (_ & X2 & X3 & X4 & X5 & X6 & _ & X8 & X9).
        split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split; [exact X5|]. split; [exact X6|]. split; [exists mo8; exact AK8|]. split; [exact X8| exact X9]. }
      assert (PEND8 : pending a3r cb (cm_n cm)) by (apply (pending_frame a3 a3r); [exact Rch| exact Rtq| exact Rgq| exact PEND3]).
      (* [comment removed for export] *)
      assert (AGr : forall z, usp - 144 <= z -> z < 2^64 -> m8 (wa z) = m6 (wa z)).
      { intros z Z1 Z2. apply MUr. rewrite wa_unsigned by (clear -Z1 Z2 LO LOC CR; lia). apply (proj2 (outside_forall _ _)). intros lo' hi' Hin Cz.
        pose proof (proj1 (Forall_forall _ _) FWr _ Hin) as AW.
        destruct (aw_ok_ceiling [cb] [] [cb] [] a3 a3r lo (usp - 144) (lo', hi') z AW WF3 WF8 BS8 ltac:(cbn [fst snd]; exact Cz)) as [X|X]; cbn [fst snd] in X; clear -X Z1 Cz LO LOC; lia. }
      assert (FR8 : rw_cells asegs m8 (usp - 144) [CB 8 j8; C8 (wz cb); C8 (wz (T + 208)); C8 (wz B); C8 (wz (cm_n cm)); C8 (wz (T + 80)); C8 (wz (INST + 728)); C8 (wz 0x370b0)]).
      { eapply AF_unwind.rw_cells_agree; [| exact FR6]. cbn -[Z.add Z.mul Z.of_nat Z.sub Z.div]. intros z Hz. apply AGr; clear -Hz USPR; lia. }
      assert (PF8 : rw_cells asegs m8 (usp - 80) [C8 (wz (T + 208)); C8 (wz B); C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
      { eapply AF_unwind.rw_cells_agree; [| exact PF5]. cbn -[Z.add Z.mul Z.of_nat Z.sub Z.div]. intros z Hz. rewrite AGr; [| clear -Hz; lia| clear -Hz USPR; lia]. apply AG56; clear -Hz USPR LO LOC CR; lia. }
      destruct (enq_cells a3r m8 [cb] REP8 WF8 IC0) as (junk8 & QC8 & ROW8 & CARR8 & CLEN8 & CST8 & INS8 & LASTF8).
      rewrite Rtq in QC8, LASTF8. rewrite CI8, HINT8 in ROW8. unfold tq_bytes in QC8. rewrite Rtq in QC8. fold (tq_bytes a3) in QC8. fold cnt in QC8.
      set (l24r := get_cache a3r kBatchClass) in *.
      assert (L8 : length l24r = 1%nat) by (unfold zlen in HINT8; clear -HINT8; lia).
      assert (NE8 : l24r <> []) by (intros E; rewrite E in L8; discriminate).
      set (xr := List.last l24r 0).
      set (cwr := map (fun z : Z => Z_to_bv 64 z) l24r ++ junk8) in CARR8.
      assert (CLENr : length cwr = 16%nat) by (subst cwr; rewrite length_app, length_map; exact CLEN8).
      assert (NTHr : nth_error cwr (Z.to_nat (1 - 1)) = Some (Z_to_bv 64 xr)).
      { subst cwr xr. replace (Z.to_nat (1 - 1)) with (Nat.pred (length l24r)) by (rewrite L8; reflexivity). apply nth_error_map_app. apply last_nth_error. exact NE8. }
      assert (INxr : In xr l24r) by (subst xr; rewrite (app_removelast_last 0 NE8) at 2; apply in_app_iff; right; left; reflexivity).
      pose proof (proj1 (proj2 (proj2 WF8))) as WCr. pose proof WCr as (_ & _ & WC3r). destruct (WC3r kBatchClass HB24) as (_ & _ & WCxr). fold l24r in WCxr.
      destruct (WCxr xr INxr) as (CARVEDr & XALr & XNFr).
      set (nbr := bnew a3r). assert (Enbr0 : nbr = chunk_of_compact SB kBatchClass xr) by reflexivity.
      assert (Enbr : nbr = SB + 24 * 2^32 + 16 * xr) by (rewrite Enbr0; unfold chunk_of_compact, region_beg, kBatchClass, kRegionSize; clear; lia).
      rewrite <- Enbr0 in CARVEDr.
      (* [comment removed for export] *)
      pose proof (ak_resv_geom _ _ _ AK8) as (G1r & G2r & G3r). change kSpaceSize with 137438953472 in G3r. change kPageSize with 4096 in G3r. change kResvLen with 137439023104 in G3r.
      destruct (proj2 (proj1 (proj2 WF8)) kBatchClass HB24) as (RG1r & RG2r & RG3r & _). cbv zeta in RG1r, RG2r, RG3r. unfold region_of in RG1r, RG2r, RG3r. change kFreeArrayOffset with 3758096384 in RG3r.
      pose proof (proj1 WF8) as WE8.
      assert (BLKr : forall bb, carved E0 a3r kBatchClass bb ->
                region_beg SB kBatchClass <= bb /\ bb + 8192 <= region_beg SB kBatchClass + rg_mapped_user (get_region a3r kBatchClass)
                /\ kHighMemBeg <= bb /\ bb + 8192 <= alloc_ceiling /\ bb + 8192 <= SB + kSpaceSize /\ (bb + 8192 <= T \/ T + 4096 <= bb) /\ bb mod 16 = 0
                /\ ae_resv_beg E0 <= bb /\ bb + 8192 + 4096 <= ae_resv_beg E0 + 137439023104 /\ SB <= bb).
      { intros bb (k & K0 & KE & KB). unfold region_of in KB. change (class_size kBatchClass) with 8192 in KE, KB.
        unfold region_beg, kBatchClass in *. change kRegionSize with 4294967296 in *. unfold kSpaceSize. rewrite KHB.
        pose proof WE8 as (_ & WEhi & _ & _ & WEce & _). rewrite KHB in WEhi. pose proof (wf_env_thread _ WE8) as (_ & _ & _ & WT4r & _).
        clear -K0 KE KB RG1r RG3r G1r G2r G3r WT4r WEhi WEce CR. repeat split; lia. }
      pose proof (BLKr _ CARVEDr) as (Nr1 & Nr2 & Nr3 & Nr4 & Nr5 & Nr6 & Nr7 & Nr8 & Nr9 & Nr10).
      assert (XRr : 0 <= xr < 2^32).
      { pose proof CARVEDr as (kx & Kx0 & KxE & KxB). rewrite Enbr in KxE. pose proof RG1r as RG1x. pose proof RG3r as RG3x.
        unfold region_of in KxB. unfold region_beg, kBatchClass in KxE, KxB, RG1x, RG3x. change kRegionSize with 4294967296 in KxE. change (class_size 24) with 8192 in KxE, KxB.
        clear -Kx0 KxE KxB RG1x RG3x. nia. }
      assert (INCr : in_cache E0 a3r kBatchClass nbr) by (unfold in_cache; rewrite Enbr0, compact_chunk_id; exact INxr).
      assert (LASTXr : cnt <> 0 -> exists lq bq, as_tq a3 = lq ++ [bq] /\ list_last (as_tq a3) = b_addr bq
                /\ rw_cells asegs m8 (b_addr bq) [C8 (wz 0); C8 (wz (b_size bq)); C8 (wz 1021)] /\ carved E0 a3r kBatchClass (b_addr bq) /\ ~ in_cache E0 a3r kBatchClass (b_addr bq) /\ In bq (as_tq a3r ++ as_gq a3r)).
      { intros NZ. destruct (LASTX NZ) as (lq & bq & E & EL & _). destruct (LASTF8 lq bq E) as (_ & _ & LB & _ & WB & _). pose proof WB as (CVb & _ & NICb & _ & CAPb & _).
        assert (FULL : zlen (b_items bq) = 1021).
        { rewrite E in NN. unfold neednew in NN. rewrite (List.last_last lq bq (mkBatch 0 [] 0)) in NN. destruct (lq ++ [bq]) eqn:E2; [destruct lq; discriminate|]. apply Z.eqb_eq in NN. exact NN. }
        rewrite FULL in LB. exists lq, bq. split; [exact E|]. split; [exact EL|]. split; [exact LB|]. split; [exact CVb|]. split; [exact NICb|].
        rewrite Rtq, Rgq, E. apply in_app_iff. left. apply in_app_iff. right. left. reflexivity. }
      assert (HLor : cnt <> 0 -> kHighMemBeg <= list_last (as_tq a3) /\ list_last (as_tq a3) + 8192 <= alloc_ceiling
                /\ (list_last (as_tq a3) + 8192 <= T \/ T + 4096 <= list_last (as_tq a3)) /\ (list_last (as_tq a3) + 8192 <= nbr \/ nbr + 8192 <= list_last (as_tq a3))).
      { intros NZ. destruct (LASTX NZ) as (lq & bq & E & EL & _ & (L1 & L2 & L3 & _) & _). destruct (LASTXr NZ) as (lq' & bq' & E' & EL' & _ & CVb & NICb & _).
        rewrite EL in EL'. rewrite EL. split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. rewrite EL'.
        destruct (carved_blocks_disjoint E0 a3r kBatchClass (b_addr bq') kBatchClass nbr HB24 HB24 (proj1 (proj2 WF8)) CVb CARVEDr) as [[_ EQ]|D].
        - exfalso. apply NICb. rewrite EQ. exact INCr.
        - change (class_size kBatchClass) with 8192 in D. exact D. }
      assert (LBor : cnt <> 0 -> rw_cells asegs m8 (list_last (as_tq a3)) [C8 (wz 0); C8 (wz lbsz); C8 (Z_to_bv 64 1021)]).
      { intros NZ. destruct (LASTXr NZ) as (lq & bq & E & EL & LB & _). rewrite EL. subst lbsz. rewrite E, (List.last_last lq bq (mkBatch 0 [] 0)). exact LB. }
      set (allocr := as_cache_allocated a3r mod 2^64).
      assert (HALr : 0 <= allocr < 2^64) by (subst allocr; apply Z.mod_pos_bound; clear; lia).
      assert (CST8' : rw_cells asegs m8 (T + 2784) [C8 (wz allocr)]) by (subst allocr; rewrite Z_to_bv_mod64; exact CST8).
      assert (WRB8 : wr_at asegs m8 nbr 8192).
      { pose proof REP8 as (_ & _ & Rrm8 & _). destruct (Rrm8 kBatchClass ltac:(unfold kBatchClass, kNumClasses; clear; lia)) as [WRu _].
        unfold region_of in WRu. eapply (wr_at_sub asegs m8 _ _ nbr 8192 WRu); [exact Nr1| exact Nr2]. }
      (* [comment removed for export] *)
      destruct (RTOK_elim _ _ _ _ _ _ _ _ _ _ TOK8) as (R8 & R8' & ATK8 & _).
      assert (ENV8 : ENVOK E0 FSB0 (sA a3r s)) by exact (ATOK_ENVOK _ _ _ _ _ _ _ _ _ _ ATK8).
      set (P8 := PP (sA a3r s) mo8).
      pose proof (PP_KIP E0 FSB0 HR0 L0 RES0 EB0 (sA a3r s) mo8 R8 R8' ATK8) as KIP8.
      assert (PSTK8 : forall y k, lo <= y -> y + Z.of_nat k <= usp - 80 -> P8 (Z_to_bv 64 y, k)).
      { intros y k H1 H2. unfold P8. rewrite <- EPOL. apply (pol_stack' E0 FSB0 HR0 (sA a3r s) mo8 AK8 WE8 ENV0); clear -H1 H2 LOC USPR CR; lia. }
      assert (PT8 : forall y k, T <= y -> y + Z.of_nat k <= T + 4096 -> P8 (Z_to_bv 64 y, k)).
      { intros y k H1 H2. unfold P8. rewrite <- EPOL. apply (pol_thread' E0 FSB0 HR0 (sA a3r s) mo8 AK8 WE8); clear -H1 H2; lia. }
      assert (PDAT8 : forall y k, 0xa4000 <= y -> y + Z.of_nat k <= 0x603000 -> P8 (Z_to_bv 64 y, k)).
      { intros y k H1 H2. unfold P8. rewrite <- EPOL. apply (pol_img' E0 FSB0 HR0 (sA a3r s) mo8 AK8 WE8 ENV8 ENV0); clear -H1 H2; lia. }
      assert (PUSR8 : forall y k, region_beg SB kBatchClass <= y -> y + Z.of_nat k <= region_beg SB kBatchClass + rg_mapped_user (get_region a3r kBatchClass) -> P8 (Z_to_bv 64 y, k)).
      { intros y k H1 H2. destruct k as [|k']; [apply PP_zero|]. unfold P8. rewrite <- EPOL.
        apply (pol_user E0 FSB0 HR0 (sA a3r s) mo8 [cb] [] AK8 WF8 kBatchClass); [exact HB24| exact H1| exact H2| clear; lia]. }
      (* [comment removed for export] *)
      set (DQb := fun ms9 => exists (t0x t1x t2x a1x a2x a5x a6x a7x : word) (m9 : mem) (junk : list word),
            ms9 = MS (mkR (wz 0x370b0) (wz (usp - 80)) gp tp t0x t1x t2x (wz (INST + 728)) (wz (T + 80)) (wz (T + 80)) a1x a2x (wz cb) (wz (cm_n cm + 8192)) a5x a6x a7x
                          (wz (cm_n cm)) (wz B) (wz (T + 208)) (wz cb) (wz 0x100000) s7 s8 s9 s10 s11 t3' t4' t5' t6') F (wz 0x370b0) fc None m9 (seg_rom asegs)
            /\ mem_inv asegs m9 /\ stk asegs m9 lo (usp - 80) /\ wmono asegs m8 m9
            /\ munch [(usp - 144, usp - 80); (T + 80, T + 112); (T + 2128, T + 2132); (T + 2784, T + 2792); (nbr, nbr + 32); (list_last (as_tq a3), list_last (as_tq a3) + lz8 cnt)] m8 m9
            /\ rw_cells asegs m9 (T + 80) [C8 (wz (cnt + 1)); C8 (wz (if cnt =? 0 then nbr else list_first (as_tq a3))); C8 (wz nbr); C8 (wz (tq_bytes a3 + (cm_n cm + 8192)))]
            /\ rw_cells asegs m9 (T + 2128) [C4 (wz (1 - 1)); C4 (wz (max_count kBatchClass)); C8 (wz 8192)]
            /\ rw_cells asegs m9 (T + 2784) [C8 (wz (allocr + 8192))]
            /\ rw_cells asegs m9 nbr [C8 (wz 0); C8 (wz (cm_n cm + 8192)); C8 (wz 1)]
            /\ u64arr asegs m9 (nbr + 24) (wz cb :: junk) /\ length junk = 1020%nat
            /\ (cnt <> 0 -> rw_cells asegs m9 (list_last (as_tq a3)) [C8 (wz nbr); C8 (wz lbsz); C8 (wz 1021)])).
      replace (Z_to_bv 64 (T + kThrCache + kPerClassSize * kBatchClass)) with (Z_to_bv 64 (T + 2128)) by (unfold kThrCache, kPerClassSize, kBatchClass; f_equal; clear; lia).
      eapply (rzA_seg_cfg asegs (aSc (sA a3r s)) (aNc (sA a3r s)) (aEBc (sA a3r s)) P8 DQb).
      { replace (usp - 144) with (usp - 80 - 64) by (clear; lia). rewrite <- Hsp.
        eapply (enq2_back P8 (wz 0x370b0) (wz (usp - 80)) gp tp (wz (INST + 728)) (wz (T + 80)) (wz (cm_n cm)) (wz B) (wz (T + 208)) (wz cb) (wz 0x100000) s7 s8 s9 s10 s11 F fc DQb
                  lo T B cb (cm_n cm) cnt (list_first (as_tq a3)) (list_last (as_tq a3)) (tq_bytes a3) (wz 0) (wz lbsz) SB (ae_region_info E0) 1 xr allocr (wz (max_count kBatchClass)) cwr nbr);
          rewrite ?Hsp;
          [ exact Enbr | exact LOC | clear -LO; lia | exact HTp3 | exact T8 | exact HSB | exact HCNT
          | clear -HQB; lia | exact XRr | exact HALr | clear -Nr5 Nr3; split; [lia| lia] | exact Nr6 | exact HLor
          | exact PSTK8 | exact PDAT8 | exact PT8
          | intros y k Y1 Y2; apply PUSR8; [clear -Y1 Nr1; lia| clear -Y2 Nr2; lia]
          | intros NZ y k Y1 Y2; destruct (LASTXr NZ) as (lq & bq & E & EL & _ & CVb & _); pose proof (BLKr _ CVb) as (L6 & L7 & _); rewrite EL in Y1, Y2; apply PUSR8; [clear -Y1 L6; lia| clear -Y2 L7; lia]
          | clear; lia | exact CLENr | exact NTHr | exact MI8 | replace (usp - 80 - 64) with (usp - 144) by (clear; lia); exact SK8
          | unfold enq_frame; rewrite ?Hsp; replace (usp - 80 - 64) with (usp - 144) by (clear; lia); exact FR8
          | exact QC8 | exact ROW8 | exact CARR8 | exact CST8' | exact INS8 | exact WRB8 | exact LBor | ].
        intros m9 t0x t1x t2x a1x a2x a5x a6x a7x HP.
        destruct HP as (junk & MI9 & SK9 & WM9 & MU9 & QC9 & PC9 & ARR9 & STA9 & INS9 & NB9 & ITS9 & LJ9 & LB9).
        rewrite ?Hsp in SK9. unfold enq2W in MU9. rewrite ?Hsp in MU9. replace (usp - 80 - 64) with (usp - 144) in MU9 by (clear; lia).
        replace (ret_pc (wz 0x370b0)) with (wz 0x370b0 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
        apply evtA_done. unfold DQb. exists t0x, t1x, t2x, a1x, a2x, a5x, a6x, a7x, m9, junk.
        split; [reflexivity|]. split; [exact MI9|]. split; [exact SK9|]. split; [exact WM9|]. split; [exact MU9|]. split; [exact QC9|]. split; [exact PC9|].
        split; [exact STA9|]. split; [exact NB9|]. split; [exact ITS9|]. split; [exact LJ9| exact LB9]. }
      { exact KIP8. }
      intros ms9 mo9 HQ9 AG9 KIP9. unfold DQb in HQ9.
      destruct HQ9 as (t0x & t1x & t2x & a1x & a2x & a5x & a6x & a7x & m9 & junk & -> & MI9 & SK9 & WM9 & MU9 & QC9 & PC9 & STA9 & NB9 & ITS9 & LJ9 & LB9).
      (* [comment removed for export] *)
      pose proof (magree_frame _ _ AG9) as (Ffds9 & Fvm9 & Flz9 & Ffs9 & Fh9 & Ftid9 & _).
      destruct KIP9 as [KIA9 _].
      pose proof (RTOK_magree _ _ _ _ _ _ _ _ _ _ _ TOK8 AG9 KIA9) as TOK9.
      pose proof (AKern_frame _ _ _ _ Fvm9 Flz9 AK8) as AK9.
      assert (NZ : bnew a3r <> 0) by (fold nbr; clear -Nr3 KHB; lia).
      pose proof RUNr as (fr & orcr & evsr & orcr' & RUNr1).
      pose proof (arun_enqueue_F2m a3 a3r cb (cm_n cm) fr orcr evsr orcr' NN EM24 RUNr1 NE8 NZ) as RUNe.
      set (a4 := enq2_st a3r cb (cm_n cm)) in *.
      destruct (hoare_arun _ _ _ _ _ _ _ _ _ _ (enqueue_spec E0 [] a3 cb (cm_n cm) WF3 PEND3 ROOM3) eq_refl RUNe) as (WF4 & E4c & E4s & E4p & E4g & E4k & E4f).
      assert (AK4 : AKern E0 a4 mo9) by (apply (AKern_ext E0 a3r); [reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| exact AK9]).
      assert (SFP34 : same_fp a3r a4) by (repeat split; reflexivity).
      assert (TOK4 : RTOKc (C - 1) (C' - DSLACK) (sA a4 s) mo9) by (eapply (RTOK_same_fp E0 FSB0 HR0 L0 RES0 EB0); [exact TOK9| exact SFP34| reflexivity| reflexivity]).
      destruct (RTOK_elim _ _ _ _ _ _ _ _ _ _ TOK4) as (R4 & R4' & ATK4 & _).
      pose proof (ATOK_KIA _ _ _ _ _ _ _ _ _ _ ATK4) as KIA4.
      assert (AG89 : forall z, 0 <= z < 2^64 -> (z + 1 <= usp - 144 \/ usp - 80 <= z) -> (z + 1 <= T + 80 \/ T + 112 <= z) -> (z + 1 <= T + 2128 \/ T + 2132 <= z)
                -> (z + 1 <= T + 2784 \/ T + 2792 <= z) -> (z + 1 <= nbr \/ nbr + 32 <= z) -> (z + 1 <= list_last (as_tq a3) \/ list_last (as_tq a3) + lz8 cnt <= z) -> m9 (wa z) = m8 (wa z)).
      { intros z Z0 Z1 Z2 Z3 Z4 Z5 Z6. apply MU9. rewrite wa_unsigned by (clear -Z0; lia). cbn [outside]. clear -Z1 Z2 Z3 Z4 Z5 Z6. repeat split; try exact I; lia. }
      assert (LZ : (cnt = 0 /\ lz8 cnt = 0 /\ as_tq a3 = []) \/ (cnt <> 0 /\ lz8 cnt = 8 /\ as_tq a3 <> [] /\ kHighMemBeg <= list_last (as_tq a3) /\ list_last (as_tq a3) + 8192 <= alloc_ceiling
                   /\ ae_resv_beg E0 <= list_last (as_tq a3) /\ list_last (as_tq a3) + 8192 + 4096 <= ae_resv_beg E0 + 137439023104 /\ (list_last (as_tq a3) + 8192 <= T \/ T + 4096 <= list_last (as_tq a3)))).
      { unfold lz8. destruct (Z.eq_dec cnt 0) as [C0|C1].
        - left. rewrite (proj2 (Z.eqb_eq cnt 0) C0). split; [exact C0|]. split; [reflexivity|]. apply TQ0. exact C0.
        - right. rewrite (proj2 (Z.eqb_neq cnt 0) C1). destruct (LASTX C1) as (lq & bq & E & EL & _ & (L1 & L2 & L3 & L4 & L5 & _) & _). rewrite EL.
          split; [exact C1|]. split; [reflexivity|]. split; [rewrite E; destruct lq; discriminate|]. repeat split; assumption. }
      (* [comment removed for export] *)
      assert (REP4 : ARep asegs E0 (DepotR asegs E0) a4 m9).
      { apply (R2F2 a3r m8 m9 lo cb (cm_n cm) [] junk NE8 CI8 PEND8 REP8 WF8 RENV8 WM9).
        - intros z Z0 NF. unfold FPWe2, kThrQCache, kThrCache, kPerClassSize, kThrCacheStats, kBatchClass in NF. fold nbr in NF. rewrite Rtq in NF.
          apply AG89; [exact Z0| clear -NF LO; lia| clear -NF; lia| clear -NF; lia| clear -NF; lia| clear -NF; lia|].
          destruct LZ as [(C0 & -> & TQE)|(C1 & -> & TQN & _)]; [clear; lia|].
          assert (X : ~ (list_last (as_tq a3) <= z < list_last (as_tq a3) + 8)) by (intros H; apply NF; do 5 right; split; [exact TQN| exact H]). clear -X. lia.
        - exact LOC.
        - unfold kThrQCache. rewrite Rtq. unfold tq_bytes. rewrite Rtq. fold (tq_bytes a3). fold cnt. fold nbr.
          replace (match as_tq a3 with [] => nbr | _ :: _ => list_first (as_tq a3) end) with (if cnt =? 0 then nbr else list_first (as_tq a3)); [exact QC9|].
          destruct LZ as [(C0 & _ & TQE)|(C1 & _ & TQN & _)]; [rewrite (proj2 (Z.eqb_eq cnt 0) C0), TQE; reflexivity| rewrite (proj2 (Z.eqb_neq cnt 0) C1)].
          destruct (as_tq a3); [exfalso; exact (TQN eq_refl)| reflexivity].
        - unfold kThrCache, kPerClassSize, kBatchClass. replace (T + 208 + 80 * 24) with (T + 2128) by (clear; lia). fold l24r. rewrite HINT8.
          destruct (rwc_split asegs m9 (T + 2128) [C4 (wz (1 - 1))] [C4 (wz (max_count 24)); C8 (wz 8192)] PC9) as [X _]. exact X.
        - unfold kThrCacheStats. replace (T + (208 + 2560) + 16) with (T + 2784) by (clear; lia). change (class_size kBatchClass) with 8192.
          replace (wz (as_cache_allocated a3r + 8192)) with (wz (allocr + 8192)); [exact STA9|].
          subst allocr. rewrite <- (Z_to_bv_mod64 (as_cache_allocated a3r mod 2 ^ 64 + 8192)), <- (Z_to_bv_mod64 (as_cache_allocated a3r + 8192)). f_equal.
          rewrite Zplus_mod_idemp_l. reflexivity.
        - exact NB9.
        - exact ITS9.
        - exact LJ9.
        - intros l0 b0 E. rewrite Rtq in E. assert (C1 : cnt <> 0) by (subst cnt; rewrite E; unfold qcount; rewrite length_app; cbn [length]; clear; lia).
          destruct (rwc_split asegs m9 (list_last (as_tq a3)) [C8 (wz nbr)] [C8 (wz lbsz); C8 (wz 1021)] (LB9 C1)) as [X _]. rewrite E, list_last_snoc in X. exact X. }
      (* [comment removed for export] *)
      assert (RT9 : rt_misc5 FSB0 PL0 E0 m9).
      { apply (rt_misc5_agree E0 FSB0 PL0 m8 m9 RT8). intros z Hz.
        destruct (rt_fpc_where2 E0 FSB0 PL0 z Hz) as [[ZI NM]|RH].
        - apply AG89; [clear -ZI; lia| clear -ZI LO LOC CR; lia| clear -ZI Timg Tlo; lia| clear -ZI Timg Tlo; lia| clear -ZI Timg Tlo; lia| clear -ZI Nr3 KHB; lia|].
          destruct LZ as [(_ & -> & _)|(_ & -> & _ & L1 & _)]; [clear; lia| clear -ZI L1 KHB; lia].
        - unfold rt_high2 in RH. apply AG89; [clear -RH Tlo Thi CQ1 CQ2 CC1 CC2 DQ1 DQ2 DD1 DD2 CR; lia| clear -RH LO LOC Thi CQ2 CC2 DQ2 DD2; lia| clear -RH CT DT; lia| clear -RH CT DT; lia| clear -RH CT DT; lia| |].
          + clear -RH Nr6 Nr8 Nr9 CRS DRS CC1 CC2 DD1 DD2 CIA WI4. lia.
          + destruct LZ as [(_ & -> & _)|(_ & -> & _ & L1 & L2 & L4 & L5 & L3)]; [clear; lia| clear -RH L3 L4 L5 CRS DRS CC1 CC2 DD1 DD2 CIA WI4; lia]. }
      (* [comment removed for export] *)
      set (WL := if cnt =? 0 then (@nil (Z * Z)) else [(list_last (as_tq a3), list_last (as_tq a3) + 8)]).
      set (W6 := [(usp - 144, usp - 80); (T + 80, T + 112); (T + 2128, T + 2132); (T + 2784, T + 2792); (nbr, nbr + 32)] ++ WL).
      assert (MU9' : munch W6 m8 m9).
      { eapply munch_weaken; [| exact MU9]. intros z Hz. subst W6 WL.
        destruct LZ as [(C0 & E0l & _)|(C1 & E1l & _)]; [rewrite (proj2 (Z.eqb_eq _ _) C0) in Hz| rewrite (proj2 (Z.eqb_neq _ _) C1) in Hz]; rewrite ?E0l, ?E1l;
          cbn [outside app] in Hz |- *; clear -Hz; repeat split; try exact I; lia. }
      set (WA := (W15 usp cb (cm_n cm) ++ Wd) ++ (((usp - 144, usp - 80) :: Wr) ++ W6)).
      assert (MU09 : munch WA m m9).
      { subst WA. eapply munch_trans; [eapply munch_weaken; [| exact MU5]|]; [| eapply munch_trans; [eapply munch_weaken; [| exact MU6]| eapply munch_trans; [eapply munch_weaken; [| exact MUr]| eapply munch_weaken; [| exact MU9']]]];
          intros z Hz; apply (proj2 (outside_forall _ _)); intros lo' hi' Hin; apply (proj1 (outside_forall _ _) Hz); apply in_app_iff;
          [left; exact Hin| right; apply in_app_iff; left; destruct Hin as [E|[]]; left; exact E| right; apply in_app_iff; left; right; exact Hin| right; apply in_app_iff; right; exact Hin]. }
      (* [comment removed for export] *)
      assert (CBAW : forall x0 y0, cb <= x0 -> y0 <= cb + 16 + rounded (cm_n cm) ->
                (ae_resv_beg E0 <= x0 /\ y0 <= ae_resv_beg E0 + kResvLen) \/ (exists sc, (In sc (as_sec a) \/ In sc (as_sec a4)) /\ sc_map_beg sc <= x0 /\ y0 <= sc_map_beg sc + sc_map_size sc)).
      { intros x0 y0 X1 Y1. destruct CBLOC as [(c & Hc & L1 & L2)|(sc & Hsc & L1 & L2)].
        - left. unfold region_beg in L1, L2. destruct (proj2 WR c Hc) as (Rg1 & Rg2 & Rg3 & _). cbv zeta in Rg1, Rg3. unfold region_of in Rg1, Rg3.
          change kRegionSize with 4294967296 in L1, L2. change kFreeArrayOffset with 3758096384 in Rg3. unfold kLargestClassID in Hc. change kResvLen with 137439023104.
          pose proof (ak_resv_geom _ _ _ Hkern) as (G1' & _ & G3'). change kSpaceSize with 137438953472 in G3'. change kPageSize with 4096 in G3'. change kResvLen with 137439023104 in G3'.
          subst a. clear -X1 Y1 L1 L2 Hc Rg1 Rg3 G1' G3'. nia.
        - right. exists sc. split; [left; exact Hsc| clear -X1 Y1 L1 L2; lia]. }
      assert (HL8b : 8 * ((cm_n cm + 7) / 8) < cm_n cm + 8 /\ cm_n cm <= rounded (cm_n cm)) by (clear -N40 RG1; Z.div_mod_to_equations; lia).
      assert (G8 : 8 * ((cb + 16) / 8) = cb + 16) by (clear -P16; Z.div_mod_to_equations; lia).
      pose proof (qc_enq2 a3r cb (cm_n cm)) as (Etq4 & Eqc4 & Efst4 & Elst4 & Eby4). fold a4 nbr in Etq4, Eqc4, Efst4, Elst4, Eby4. rewrite Rtq in Eqc4, Efst4. fold cnt in Eqc4.
      assert (Eby4' : tq_bytes a4 = tq_bytes a3 + (kBatchSize + cm_n cm)) by (rewrite Eby4; unfold tq_bytes; rewrite Rtq; reflexivity).
      (* [comment removed for export] *)
      unfold QE_post in QPOST.
      eapply (QPOST t0x t1x t2x (wz (T + 80)) a1x a2x (wz cb) (wz (cm_n cm + 8192)) a5x a6x a7x t3' t4' t5' t6' m9 mo9 a2 a4 cm aid fid);
        [ exact Hcm | exact ST | exact UB | exact RUN | exact FID | exact DS2 | exact ND2
        | exists fr, orcr, evsr, orcr'; exact RUNe
        | (* [comment removed for export] *) split; [exact E4c|]; unfold a4, enq2_st, bpop_st, bnew;
          cbn [as_chunks as_sec as_ptr_committed as_gq as_nprim_ever as_residue as_ndepot_ins as_node_blocks as_store_blocks as_sec_stats upd_tq upd_cache_allocated upd_cache_stale set_cache];
          rewrite Rsec, Rptr, Rgq, Rnp, Rres, Rnd, Rnb, Rsb, Rsss; unfold a3, AsanRepFlip.s3;
          cbn [as_chunks as_sec as_ptr_committed as_gq as_nprim_ever as_residue as_ndepot_ins as_node_blocks as_store_blocks as_sec_stats upd_chunks];
          repeat split; first [reflexivity| exact D8| exact D7| exact D17| exact D20| exact D19| exact D10]
        | exact WF4 | exact REP4 | exact AK4 | exact TOK4 | exact KIA4
        | (* [comment removed for export] *) apply (res_ok_frame a3r); [cbn; intros sc H; exact H| cbn; apply incl_refl| exact RES8]
        | (* [comment removed for export] *) exact (proj2 QB8)
        | (* [comment removed for export] *) rewrite Eby4'; unfold kThreadQuarantineMax, kBatchSize; clear -HQB TQB N40 N27; lia
        | (* [comment removed for export] *) revert DI8; clear; unfold depot_inv, depot_n_ids, dphi; exact (fun H => H)
        | (* [comment removed for export] *) revert SS8; clear; unfold sstats_ok, sec_bytes; exact (fun H => H)
        | (* [comment removed for export] *) intros cbx cmx Hx; apply (CS8 cbx cmx); revert Hx; unfold a4, enq2_st, bpop_st; cbn [as_chunks upd_tq upd_cache_allocated upd_cache_stale set_cache]; exact (fun H => H)
        | rewrite Ffs9, Ffs8, Ffs6; exact Ffs5 | rewrite Ffds9, Ffds8, Ffds6; exact Ffds5 | rewrite Ftid9, Ftid8, Ftid6; exact Ftid5
        | exact MI9 | exact SK9 | exact (wmono_trans _ _ _ _ WM5 (wmono_trans _ _ _ _ WM6 (wmono_trans _ _ _ _ WM68 WM9))) | exact RT9
        | (* [comment removed for export] *)
        | (* [comment removed for export] *) eapply AF_unwind.rw_cells_agree; [| exact PF8]; cbn -[Z.add Z.mul Z.of_nat Z.sub Z.div]; intros z Hz;
          apply AG89; [clear -Hz LO LOC CR USPR; lia| clear -Hz; lia| clear -Hz Thi LO LOC; lia| clear -Hz Thi LO LOC; lia| clear -Hz Thi LO LOC; lia| clear -Hz Nr4 LO LOC; lia|];
          destruct LZ as [(_ & -> & _)|(_ & -> & _ & _ & L2 & _)]; [clear; lia| clear -Hz L2 LO LOC; lia]
        | (* [comment removed for export] *) rewrite Eqc4, Efst4, Elst4, Eby4'; unfold kBatchSize;
          replace (match as_tq a3 with [] => nbr | _ :: _ => list_first (as_tq a3) end) with (if cnt =? 0 then nbr else list_first (as_tq a3));
          [replace (tq_bytes a3 + (8192 + cm_n cm)) with (tq_bytes a3 + (cm_n cm + 8192)) by (clear; lia); exact QC9|];
          destruct LZ as [(C0 & _ & TQE)|(C1 & _ & TQN & _)]; [rewrite (proj2 (Z.eqb_eq cnt 0) C0), TQE; reflexivity| rewrite (proj2 (Z.eqb_neq cnt 0) C1)];
          destruct (as_tq a3); [exfalso; exact (TQN eq_refl)| reflexivity] ].
      (* [comment removed for export] *)
      exists WA. split; [exact MU09|]. subst WA.
      assert (NB4 : forall b, In b (ae_depot_nodes E0 :: as_node_blocks a2) -> In b (ae_depot_nodes E0 :: as_node_blocks a4)).
      { intros b Hb. unfold a4, enq2_st, bpop_st. cbn [as_node_blocks upd_tq upd_cache_allocated upd_cache_stale set_cache]. rewrite Rnb. revert Hb. unfold a3, AsanRepFlip.s3. cbn [as_node_blocks upd_chunks]. exact (fun H => H). }
      assert (SB4 : forall b, In b (ae_store_blk E0 :: as_store_blocks a2) -> In b (ae_store_blk E0 :: as_store_blocks a4)).
      { intros b Hb. unfold a4, enq2_st, bpop_st. cbn [as_store_blocks upd_tq upd_cache_allocated upd_cache_stale set_cache]. rewrite Rsb. revert Hb. unfold a3, AsanRepFlip.s3. cbn [as_store_blocks upd_chunks]. exact (fun H => H). }
      assert (WDok : Forall (aw_ok E0 a a4 lo usp) Wd /\ Forall (fun iv => forall blo bsz, In (blo, bsz) (live_blocks a) -> (blo, bsz) <> (cb + 16, cm_n cm) -> snd iv <= fst iv \/ snd iv <= blo \/ blo + bsz <= fst iv) Wd).
      { split; apply Forall_forall; intros [x0 y0] Hin; pose proof (proj1 (Forall_forall _ _) FWd _ Hin) as X; unfold dput_w_ok in X; cbn [fst snd] in X.
        - unfold aw_ok. cbn [fst snd]. destruct X as [X|[(r & Hr & X1 & X2)|[(b & Hb & X1 & X2)|(b & Hb & X1 & X2)]]].
          + left. clear -X; lia.
          + right; left. unfold depot_static in Hr. rewrite IC0 in Hr. cbn [aic_theDepot aic_stackStore asan_ic] in Hr.
            destruct Hr as [<-|[<-|[]]]; cbn [fst snd] in X1, X2.
            * exists (aic_theDepot asan_ic, 0x440010). split; [unfold img_mut; do 3 right; left; reflexivity| cbn [fst snd aic_theDepot asan_ic]; clear -X1 X2; lia].
            * exists (aic_stackStore asan_ic, 0x10010). split; [unfold img_mut; do 4 right; left; reflexivity| cbn [fst snd aic_stackStore asan_ic]; clear -X1 X2; lia].
          + do 6 right; left. exists b. split; [exact (NB4 b Hb)| clear -X1 X2; lia].
          + do 7 right; left. exists b. split; [exact (SB4 b Hb)| clear -X1 X2; lia].
        - intros blo bsz LIVEb NEb. cbn [fst snd]. destruct (live_block_where E0 a blo bsz Hwf LIVEb) as (Lw0 & Lw1 & Lw2 & Lw3). destruct (live_block_off_thread E0 a blo bsz Hwf LIVEb) as [_ BT].
          destruct X as [X|X]; [right; right; clear -X Lw1 LOC LO; lia|].
          assert (DZ : forall z, x0 <= z < y0 -> DepotFPd E0 a2 z).
          { intros z Hz. destruct X as [(r & Hr & X1 & X2)|[(b & Hb & X1 & X2)|(b & Hb & X1 & X2)]].
            - left. exists r. split; [unfold depot_static in Hr; destruct Hr as [<-|[<-|[]]]; [left| right; left]; reflexivity| clear -Hz X1 X2; lia].
            - right; left. exists b. split; [exact Hb| clear -Hz X1 X2; lia].
            - right; right. exists b. split; [exact Hb| clear -Hz X1 X2; lia]. }
          destruct (Z_lt_le_dec x0 y0) as [O0|O0]; [| left; exact O0]. destruct (Z_lt_le_dec blo y0) as [O1|O1]; [| right; left; exact O1]. destruct (Z_lt_le_dec x0 (blo + bsz)) as [O2|O2]; [| right; right; exact O2]. exfalso.
          set (z := Z.max x0 blo).
          assert (Zin : x0 <= z < y0 /\ blo <= z < blo + bsz) by (subst z; clear -O0 O1 O2 Lw0; lia).
          pose proof WE as (_ & WEhi & WErs & WEsp & _). change kSpaceSize with 137438953472 in WEsp.
          destruct (dfp_cases E0 PL0 ENV0 PL0OK a2 mo5 z IC0 AK2 WF2 EI1 EI2 (DZ z (proj1 Zin))) as [STz|(b & bl & R & Bb0 & Bce & Bbd & Brs & Bsc & BTb & BAb)].
          + destruct Lw3 as [[S1 S2]|(sc & Hsc & S1 & S2)]; [rewrite KHB in WEhi; clear -STz Zin S1 WEhi WErs; lia|].
            destruct (WS3 sc Hsc) as (_ & _ & _ & _ & _ & _ & SR). pose proof (SR _ (proj1 (wf_env_img _ WE))) as X1. rewrite EI1 in X1. cbn [fst snd] in X1. clear -STz Zin S1 S2 X1 EI2. lia.
          + change kResvLen with 137439023104 in Brs.
            destruct Lw3 as [[S1 S2]|(sc & Hsc & S1 & S2)]; [unfold kSpaceSize in S2; clear -R Zin S1 S2 Brs WErs WEsp; lia|].
            rewrite D8 in Bsc. destruct (Bsc sc Hsc); clear -R Zin S1 S2 H; lia. }
      pose proof (chunk_geo E0 [] [] a cb cm Hwf Hcm) as (CG1 & CG2 & CG3 & CG4 & CG5). rewrite UB in CG1, CG2, CG4, CG5.
      pose proof WE as (_ & WEhi & WErs & WEsp & _ & _ & WE7 & _ & WE9 & _ & _ & WE12 & _). change kSpaceSize with 137438953472 in WEsp. rewrite KHB in WEhi.
      assert (LIVE3 : forall blo bsz, In (blo, bsz) (live_blocks a) -> (blo, bsz) <> (cb + 16, cm_n cm) -> In (blo, bsz) (live_blocks a3)).
      { intros blo bsz LIVEb NEb. destruct (live_block_other E0 [] [] a cb cm blo bsz Hwf Hcm LIVEb ltac:(rewrite UB; exact NEb)) as (cb' & cm' & i & H' & NE' & <- & <- & ST').
        apply (chunk_live_in a3 cb' cm' i); [rewrite (Hoth3 cb' NE'); exact H'| exact ST']. }
      assert (LIVE8 : forall blo bsz, In (blo, bsz) (live_blocks a) -> (blo, bsz) <> (cb + 16, cm_n cm) -> In (blo, bsz) (live_blocks a3r)).
      { intros blo bsz LIVEb NEb. unfold live_blocks, chunk_list. rewrite Rch. exact (LIVE3 blo bsz LIVEb NEb). }
      split.
      { (* [comment removed for export] *)
        apply Forall_app; split; [apply Forall_app; split; [| exact (proj1 WDok)]|].
        + unfold AF_deallocT1.W15. repeat (apply Forall_cons; [unfold aw_ok; cbn [fst snd]|]); [.. | apply Forall_nil].
          * left. clear -LO; lia.
          * destruct (CBAW cb (cb + 4) ltac:(clear; lia) ltac:(clear -RG1; lia)) as [X|X]; [do 3 right; left; exact X| do 5 right; left; exact X].
          * destruct (CBAW (cb + 16) (cb + 24) ltac:(clear; lia) ltac:(clear -RG1; lia)) as [X|X]; [do 3 right; left; exact X| do 5 right; left; exact X].
          * right; right; left. exists (T + kThrStats, 112 + 8 * 32). split; [unfold arep_thr_ranges; do 5 right; left; reflexivity| cbn [fst snd]; unfold kThrStats; clear; lia].
          * do 8 right. split.
            -- unfold LSHI, A_base.A_SB, kShadowBase. rewrite ?KHB, ?KLE. rewrite KHB, KLE in CBB.
               destruct CBB as [LOW|HIGH]; [left; clear -LOW CB0 G8 HL8b RG1 CR| right; clear -HIGH CB0 CBC G8 HL8b RG1 CR]; Z.div_mod_to_equations; lia.
            -- intros z Hz. unfold A_base.A_SB, kShadowBase in *.
               assert (GR : cb + 16 <= 8 * (z - 2147450880) < cb + 16 + rounded (cm_n cm)) by (clear -Hz G8 HL8b; Z.div_mod_to_equations; lia).
               unfold sh_excluded.
               replace (in_fakestack E0 (8 * (z - 2147450880))) with false.
               2:{ symmetry. unfold in_fakestack. apply Bool.andb_false_iff.
                   destruct CBLOC as [(c & Hc & L1 & L2)|(sc & Hsc & L1 & L2)].
                   - unfold region_beg in L1, L2. destruct (proj2 WR c Hc) as (Rg1 & Rg2 & Rg3 & _). cbv zeta in Rg1, Rg3. unfold region_of in Rg1, Rg3.
                     change kRegionSize with 4294967296 in L1, L2. change kFreeArrayOffset with 3758096384 in Rg3. unfold kLargestClassID in Hc.
                     pose proof (ak_resv_geom _ _ _ Hkern) as (G1' & _ & G3'). change kSpaceSize with 137438953472 in G3'. change kPageSize with 4096 in G3'. change kResvLen with 137439023104 in G3'.
                     destruct WE12 as [X|X]; [right; apply Z.ltb_ge| left; apply Z.leb_gt]; subst a; clear -X GR L1 L2 Hc Rg1 Rg3 G1' G3'; nia.
                   - destruct (WS3 sc Hsc) as (_ & _ & _ & _ & _ & _ & SR). pose proof (SR _ WE9) as X. cbn [fst snd] in X.
                     destruct X as [X|X]; [left; apply Z.leb_gt| right; apply Z.ltb_ge]; clear -X GR L1 L2; lia. }
               replace (in_iarena E0 (8 * (z - 2147450880))) with false.
               2:{ symmetry. unfold in_iarena. apply Bool.andb_false_iff. unfold kIArenaLen in CBI |- *. destruct CBI as [X|X]; [left; apply Z.leb_gt| right; apply Z.ltb_ge]; clear -X GR; lia. }
               replace (in_reginfo E0 (8 * (z - 2147450880))) with false; [reflexivity|].
               symmetry. unfold in_reginfo. apply Bool.andb_false_iff. unfold kSpaceSize, kPageSize.
               destruct CBLOC as [(c & Hc & L1 & L2)|(sc & Hsc & L1 & L2)].
               ++ unfold region_beg in L1, L2. destruct (proj2 WR c Hc) as (Rg1 & Rg2 & Rg3 & _). cbv zeta in Rg1, Rg3. unfold region_of in Rg1, Rg3.
                  change kRegionSize with 4294967296 in L1, L2. change kFreeArrayOffset with 3758096384 in Rg3. unfold kLargestClassID in Hc.
                  left. apply Z.leb_gt. subst a. clear -GR L1 L2 Hc Rg1 Rg3. nia.
               ++ destruct (WS3 sc Hsc) as (_ & _ & _ & _ & _ & _ & SR). pose proof (SR _ WE7) as X. cbn [fst snd] in X.
                  pose proof (ak_resv_geom _ _ _ Hkern) as (G1' & _ & G3'). change kSpaceSize with 137438953472 in G3'. change kPageSize with 4096 in G3'. change kResvLen with 137439023104 in G3', X.
                  destruct X as [X|X]; [left; apply Z.leb_gt| right; apply Z.ltb_ge]; clear -X GR L1 L2 G1' G3'; lia.
        + apply Forall_app. split.
          * apply Forall_cons; [unfold aw_ok; cbn [fst snd]; left; clear -LO; lia|].
            apply Forall_forall. intros iv Hin. apply (aw_ok_mono a a3 a4 a3r lo (usp - 144) usp iv); [| | | clear; lia| exact (proj1 (Forall_forall _ _) FWr _ Hin)].
            -- intros sc [Hsc|Hsc]; left; [rewrite <- Esec3| rewrite <- Esec3, <- Rsec]; exact Hsc.
            -- intros x0 Hx. unfold a4, enq2_st, bpop_st. cbn [as_node_blocks upd_tq upd_cache_allocated upd_cache_stale set_cache]. exact Hx.
            -- intros x0 Hx. unfold a4, enq2_st, bpop_st. cbn [as_store_blocks upd_tq upd_cache_allocated upd_cache_stale set_cache]. exact Hx.
          * subst W6. apply Forall_app. split.
            -- repeat (apply Forall_cons; [unfold aw_ok; cbn [fst snd]|]); [.. | apply Forall_nil].
               ++ left. clear -LO; lia.
               ++ right; right; left. exists (T + kThrQCache, 32). split; [unfold arep_thr_ranges; do 2 right; left; reflexivity| cbn [fst snd]; unfold kThrQCache; clear; lia].
               ++ right; right; left. exists (T + kThrCache, kPerClassSize * kNumClasses). split; [unfold arep_thr_ranges; do 3 right; left; reflexivity| cbn [fst snd]; unfold kThrCache, kPerClassSize, kNumClasses; clear; lia].
               ++ right; right; left. exists (T + kThrCacheStats + 16, 16). split; [unfold arep_thr_ranges; do 4 right; left; reflexivity| cbn [fst snd]; unfold kThrCacheStats; clear; lia].
               ++ do 3 right; left. change kResvLen with 137439023104. clear -Nr8 Nr9; lia.
            -- subst WL. destruct LZ as [(C0 & _ & _)|(C1 & _ & _ & L1 & L2 & L4 & L5 & L3)]; [rewrite (proj2 (Z.eqb_eq cnt 0) C0); apply Forall_nil| rewrite (proj2 (Z.eqb_neq cnt 0) C1)].
               apply Forall_cons; [unfold aw_ok; cbn [fst snd]| apply Forall_nil]. do 3 right; left. change kResvLen with 137439023104. clear -L4 L5; lia. }
      { (* [comment removed for export] *)
        apply Forall_app; split; [apply Forall_app; split; [| exact (proj2 WDok)]|].
        + unfold AF_deallocT1.W15.
          repeat (apply Forall_cons; [cbn [fst snd]; intros blo bsz LIVEb NEb;
            destruct (live_block_where E0 a blo bsz Hwf LIVEb) as (Lw0 & Lw1 & Lw2 & Lw3); destruct (live_block_off_thread E0 a blo bsz Hwf LIVEb) as [_ BT];
            pose proof (live_apart_blk E0 [] [] a cb cm blo bsz Hwf Hcm LIVEb ltac:(rewrite UB; exact NEb)) as APT|]); [.. | apply Forall_nil].
          * right; right. clear -Lw1 LOC LO. lia.
          * right. clear -APT CG1 CG5. lia.
          * right. clear -APT CG1 CG5. lia.
          * right. clear -BT. lia.
          * right. unfold kShadowBase. rewrite KHB, KLE in Lw2. clear -Lw0 Lw2 CB0 CBC G8 HL8b CR. Z.div_mod_to_equations. lia.
        + apply Forall_app. split.
          * apply Forall_cons; [cbn [fst snd]; intros blo bsz LIVEb NEb; destruct (live_block_off_thread E0 a blo bsz Hwf LIVEb) as [B1c _]; right; right; clear -B1c LOC LO; lia|].
            apply Forall_forall. intros iv Hin blo bsz LIVEb NEb. exact (proj1 (Forall_forall _ _) FLr _ Hin blo bsz (LIVE3 blo bsz LIVEb NEb)).
          * subst W6. apply Forall_app. split.
            -- repeat (apply Forall_cons; [cbn [fst snd]; intros blo bsz LIVEb NEb;
                 destruct (live_block_where E0 a blo bsz Hwf LIVEb) as (Lw0 & Lw1 & Lw2 & Lw3); destruct (live_block_off_thread E0 a blo bsz Hwf LIVEb) as [_ BT];
                 pose proof (cache_vs_live E0 [cb] [] a3r kBatchClass xr blo bsz WF8 HB24 INxr (LIVE8 blo bsz LIVEb NEb)) as CVL; rewrite <- Enbr0 in CVL; change (class_size kBatchClass) with 8192 in CVL|]); [.. | apply Forall_nil].
               ++ right; right. clear -Lw1 LOC LO. lia.
               ++ right. clear -BT. lia.
               ++ right. clear -BT. lia.
               ++ right. clear -BT. lia.
               ++ right. clear -CVL. lia.
            -- subst WL. destruct LZ as [(C0 & _ & _)|(C1 & _ & TQN & _)]; [rewrite (proj2 (Z.eqb_eq cnt 0) C0); apply Forall_nil| rewrite (proj2 (Z.eqb_neq cnt 0) C1)].
               apply Forall_cons; [cbn [fst snd]| apply Forall_nil]. intros blo bsz LIVEb NEb.
               destruct (LASTXr C1) as (lq & bq & E & EL & _ & _ & _ & INbq). rewrite EL.
               pose proof (batch_vs_live E0 [cb] a3r bq blo bsz WF8 INbq (LIVE8 blo bsz LIVEb NEb)) as BV. right. clear -BV. lia. }
Qed.

End DeallocT2.
End RC__1.
