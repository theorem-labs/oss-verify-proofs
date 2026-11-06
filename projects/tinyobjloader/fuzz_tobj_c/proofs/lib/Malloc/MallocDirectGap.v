(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "ex"; "iff"; "@Corelib.Init.Datatypes"; "pair"; "nat"; "cons"; "prod"; "app"; "nil"; "Some"; "bool"; "list"; "option"; "None"; "length"; "true"; "fst"; "snd"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "sub"; "mul"; "of_nat"; "modulo"; "pow"; "ltb"; "eqb"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "mslot"; "SP"; "UNIT"; "region"; "set_mmap_counter"; "MUsed"; "PGSZ"; "padd"; "st_metas"; "st_mmap_counter"; "st_regions"; "ameta"; "IB"; "am_mem"; "astate"; "st_init_done"; "FUser"; "META_SIZE"; "am_aidx"; "am_avail"; "am_freed"; "am_last"; "am_maplen"; "am_next"; "am_prev"; "am_sc"; "fkind"; "fr_kind"; "fr_n"; "fr_off"; "frame"; "mkSlot"; "nth_slot"; "prid"; "slot_start"; "slotst"; "stride_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "mcell"; "image"; "loc_addr"; "mc_w"; "usedX"; "LMem"; "U0"; "mc_loc"; "CTX_mmap_counter"; "Inv"; "footprint"; "loc"; "region_of"; "MT"; "areas_cells"; "group_cells"; "mc_val"; "meta_slot_cells"; "sval"; "sval_num"; "used_metas"; "user_blocks"; "CTX_SIZE"; "LCtx"; "MCell"; "VLo5"; "VSec"; "VZ"; "alloc_owned"; "hdr_byte3"; "hdr_off16"; "le_byte"; "ly_ctx"; "ly_reg"; "meta_bits"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocDirectGap.GapD"; "d_am6"; "d_s6"; "d_zG"; "d_r"; "d_len"; "d_off"; "d_res"; "d_ctr1"; "d_touched"; "dg_newcells"; "d_zP"; "cell_ok"; "d_e"; "d_st"; "d_code"; "d_meets"; "dg_spec"; "d_h16"; "d_h3"; "d_p"; "@Stdlib.Lists.List"; "In"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter"; "footer_cells"; "group_footer_cells"; "reserved_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocDirectPost"; "md_fr"; "md_hdr"; "md_stride"; "md_maplen"; "md_rg"; "md_s6"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MapGrow"; "s2"; "L'"; "mg_pre"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "mc_ctx"; "topL"; "wz"; "blocks"; "addr_of"; "mc_chk_guard"; "mc_chk_guard_got"; "mc_ctz_tab"; "mc_errno"; "mc_libc"; "mc_lock"; "mc_med_cnt_tab"; "mc_replaced"; "mc_size_classes"; "mc_small_cnt_tab"; "vm_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocDirectGap"; "ctr_cell"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame"; "upd_meta"; "ub_same"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "mkMA"; "MInv"; "layout_extends"; "@Corelib.Init.Specif"; "sumbool"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtImage"; "not_used"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI"; "MInvI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfMeta"; "am_frame"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2"; "xraw"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics State.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLayout MallocFooter MallocIface MallocIfaceI MallocLaws
  MallocLemmasBase MallocWfInv MallocWfMeta MallocWfFrame MallocWfGroup MallocWfRepr FpLaws WalkArith
  Zones2 ImageUpd ImageDelta FreeNtImage AllocMetaImage AllocMetaGrow AllocGroupImage MallocDirectPost MapGrow GapBlock NestTier.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition ctr_cell (v : Z) : mcell := ltac2:(tb__ "0|0|
S5fS5eS4fA1U4S62Vv;A1A3").

Lemma areas_cells_ext S1 S2 l : ltac2:(tb__ "0|0|
S1SfSaS21S22A2A1S2aVS1;A1S2aVS2;A1A3S1SfS47A1S55VS1;Vl;A2S55VS2;Vl;A2A3F_;").
Proof. intros E. induction l as [|a tl IH]; cbn [areas_cells]; [reflexivity|]. rewrite IH. unfold area_cells. rewrite E. reflexivity. Qed.
Lemma used_metas_ext S1 S2 : ltac2:(tb__ "0|0|
S1SfSaS21S22A2A1S2aVS1;A1S2aVS2;A1A3S1SfSaS21S2dA2A1S5bVS1;A1S5bVS2;A1A3F_;").
Proof. intros E. unfold used_metas. rewrite E. reflexivity. Qed.

Lemma image_set_mmap_counter v t c : ltac2:(tb__ "0|0|
S7eS47Vc;S48S26Vv;Vt;A2A1A3S4S1S47Vc;S9cVv;A1A3S7eS47Vc;S48Vt;A1A3A2F_;").
Proof.
  intros Hin. unfold image in Hin |- *.
  rewrite (areas_cells_ext (set_mmap_counter v t) t) in Hin by (destruct t; reflexivity).
  rewrite (used_metas_ext (set_mmap_counter v t) t) in Hin by (destruct t; reflexivity).
  replace (st_areas (set_mmap_counter v t)) with (st_areas t) in Hin by (destruct t; reflexivity).
  apply in_app_iff in Hin as [Hin|Hin]; [|right; apply in_app_iff; right; exact Hin].
  assert (CTX : forall c', In c' (ctx_cells (set_mmap_counter v t)) -> c' = ctr_cell v \/ In c' (ctx_cells t)).
  { clear. intros c' Hc. destruct t. unfold ctx_cells in *.
    cbn -[Z.add Z.mul Z.of_nat seq map app In optr andb Z.eqb PGSZ] in Hc |- *.
    apply in_app_iff in Hc as [Hc|Hc]; [|right; apply in_app_iff; right; exact Hc].
    cbn [In] in Hc. destruct Hc as [H|[H|[H|H]]]; [right|right|left; symmetry; exact H|right]; apply in_app_iff; left; cbn [In]; tauto. }
  destruct (CTX c Hin) as [E|H]; [left; exact E | right; apply in_app_iff; left; exact H].
Qed.
Lemma footer_set_mmap_counter v t : ltac2:(tb__ "0|0|
S1SfS47A1S80S26Vv;Vt;A2A1S80Vt;A1A3").
Proof. destruct t; reflexivity. Qed.
Lemma ctr_cell_In t : ltac2:(tb__ "0|0|
S7eS47S9cS2bVt;A1A1S48Vt;A1A3").
Proof. unfold image, ctx_cells. apply in_app_iff. left. apply in_app_iff. left. cbn [In]. tauto. Qed.

Lemma upd_meta_set_mmap_counter q x v t : ltac2:(tb__ "0|0|
S1S30S9dVq;Vx;S26Vv;Vt;A2A3S26Vv;S9dVq;Vx;Vt;A3A2A3").
Proof. destruct t; reflexivity. Qed.

Lemma tup3 {A B C' : Type} (a a' : A) (b b' : B) (c c' : C') : ltac2:(tb__ "0|1|
S1VA;Va;Va';A3S1VB;Vb;Vb';A3S1VC';Vc;Vc';A3S1SaSaVA;VB;A2M0VC';A2S7G0VC';S7VA;VB;Va;Vb;A4Vc;A4S7G0VC';S7VA;VB;Va';Vb';A4Vc';A4A3F_;F_;F_;").
Proof. intros -> -> ->. reflexivity. Qed.

Section GapD.
  Variables (C : mconsts) (s : astate) (n : Z) (L : layout) (vm0 : VmMaps) (zR : Z).
  Hypothesis MGP : ltac2:(tb__ "0|0|
S8bVC;Vs;Vn;VL;Vvm0;VzR;A6").
  Variables (s3 : astate) (L3 : layout) (g : sptr) (vm3 : VmMaps).
  Variables (rd0 rd1 : word -> option byte) (wok0 wok1 : word -> bool).
  Hypothesis HMI3 : ltac2:(tb__ "0|0|
Sa6VC;S9S21Vg;ScS21A1A3S11SaS21S0A2A1S4dSa1Vs3;VL3;A2Vrd0;Vwok0;Vvm3;A8").

  Hypothesis Hraw : ltac2:(tb__ "0|0|
Sa8S9S21Vg;ScS21A1A3Vs3;A2").
  Hypothesis Hinit3 : st_init_done s3 = true.
  Hypothesis Hframe : ltac2:(tb__ "0|0|
Sa7S89Vs;Vn;A2Vs3;A2").
  Hypothesis HusedX : ltac2:(tb__ "0|1|
S21S2dS6S4bS9S21Vg;ScS21A1M0A3Vs3;R2R1A4S4bG0S89Vs;Vn;A2R2R1A4A2Fa;Fq;").
  Hypothesis Hub3 : ltac2:(tb__ "0|0|
S9eS89Vs;Vn;A2Vs3;A2").
  Hypothesis Hkey : In g (keys s3).
  Hypothesis Hext : ltac2:(tb__ "0|0|
Sa3S8aVs;VL;VzR;A3VL3;S12S25S2cS89Vs;Vn;A2A1A2A3").
  Hypothesis HS : statics_in_image C.

  Lemma D_I : ltac2:(tb__ "0|0|
S50ScS21A1S11SaS21S0A2A1S4dVs;A4"). Proof using MGP. exact (mg_I _ _ _ _ _ _ MGP). Qed.
  Lemma D_n : direct_case n. Proof using MGP. exact (mg_n _ _ _ _ _ _ MGP). Qed.
  Lemma D_I3 : ltac2:(tb__ "0|0|
S50S9S21Vg;ScS21A1A3S11SaS21S0A2A1S4dVs3;A4"). Proof using HMI3. exact (mig_I HMI3). Qed.
  Lemma D_L3 : layout_ok L3 s3. Proof using HMI3. exact (mig_layout HMI3). Qed.
  Lemma D_ctr3 : ltac2:(tb__ "0|0|
S1S0S2bVs3;A1S2bVs;A1A3").
  Proof using Hframe MGP. destruct Hframe as (_ & _ & _ & _ & E). rewrite E. exact (proj1 (proj2 (proj2 (proj2 (s2_shape s n D_I))))). Qed.
  Lemma D_MT3 : ltac2:(tb__ "0|0|
S5S22S22S2S1S10S22A1S54Vs3;Vg;A2SdS22R1A2A3Sa5R1A1A2Lxold;A2").
  Proof using Hraw. destruct (Hraw g ltac:(left; reflexivity)) as [E|E]; eexists; (split; [exact E | exact I]). Qed.
  Lemma D_ND3 : List.NoDup (keys s3). Proof using HMI3. exact (proj1 (inv_keys D_I3)). Qed.

  Definition d_s6 : astate := ltac2:(tb__ "0|0|
S88Vs;Vn;Vs3;Vg;A4").
  Definition d_am6 : ameta := md_am6 s n.
  Definition d_p : sptr := md_p s n.
  Definition d_ctr1 : Z := md_ctr1 s.
  Definition d_len : Z := md_len n.
  Definition d_zG : Z := addr_of L3 g.
  Definition d_off : Z := md_off s n.
  Definition d_zP : Z := ltac2:(tb__ "0|0|
S16S16VzR;S24A2S1aS24S6fA2A2").
  Definition d_res : Z := md_reserved s n.
  Definition d_r : nat := md_r s.

  Lemma D_I6 : ltac2:(tb__ "0|0|
S50ScS21A1S11SaS21S0A2A1S4dS6bA4"). Proof using HMI3 Hframe HusedX MGP. exact (proj1 (Inv_s6 s n D_I D_n s3 g D_I3 Hframe HusedX)). Qed.
  Lemma D_fp : ltac2:(tb__ "0|0|
S1SfSaS52S0A2A1S51S6bA1S51Vs3;A1A3"). Proof using HMI3 Hframe Hkey Hraw Hub3 HusedX MGP. exact (footprint_s6 s n s3 g D_I3 Hraw Hkey Hframe HusedX Hub3 D_ctr3). Qed.
  Lemma D_regions : ltac2:(tb__ "0|0|
S1SfS25A1S2cS6bA1S2cVs3;A1A3"). Proof using HMI3 Hframe Hkey Hraw Hub3 HusedX MGP. exact (proj1 (s6_shape s n s3 g D_I3 Hraw Hkey Hframe HusedX Hub3 D_ctr3)). Qed.
  Lemma D_region_of k : ltac2:(tb__ "0|0|
S1S10S25A1S53S6bVk;A2S53Vs3;Vk;A2A3"). Proof using HMI3 Hframe Hkey Hraw Hub3 HusedX MGP. unfold region_of. rewrite D_regions. reflexivity. Qed.
  Lemma D_L6 : layout_ok L3 d_s6.
  Proof using HMI3 Hframe Hkey Hraw Hub3 HusedX MGP.
    pose proof D_L3 as (A1 & A2 & A3 & A4). split; [exact A1|]. split; [|rewrite D_fp; split; [exact A3 | exact A4]].
    intros k rg Hk Hl. rewrite D_region_of in Hk. exact (A2 k rg Hk Hl).
  Qed.
  Lemma D_X6 : xraw [] d_s6. Proof using . intros q []. Qed.
  Lemma D_MT6 : ltac2:(tb__ "0|0|
S1S10S22A1S54S6bVg;A2SdS22S27S6aA1A2A3"). Proof using . unfold d_s6. rewrite MT_s6, sptr_eqb_refl. reflexivity. Qed.
  Lemma D_u6 : ltac2:(tb__ "0|0|
S4bScS21A1S6bVg;S6aA4"). Proof using . apply usedX_intro; [reflexivity | exact D_MT6]. Qed.
  Lemma D_key6 : In g (keys d_s6).
  Proof using HMI3 Hframe Hkey Hraw Hub3 HusedX MGP. pose proof (s6_shape s n s3 g D_I3 Hraw Hkey Hframe HusedX Hub3 D_ctr3) as SH. unfold d_s6. rewrite (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 SH))))))))))))))))))). exact Hkey. Qed.
  Lemma D_ctr6 : ltac2:(tb__ "0|0|
S1S0S2bS6bA1S71A3").
  Proof using HMI3 Hframe Hkey Hraw Hub3 HusedX MGP. exact (proj1 (proj2 (proj2 (s6_shape s n s3 g D_I3 Hraw Hkey Hframe HusedX Hub3 D_ctr3)))). Qed.

  Lemma D_r_lt : ltac2:(tb__ "0|0|
S7fS6dS12S25S2cS89Vs;Vn;A2A1A2A2").
  Proof using MGP. unfold d_r, md_r, s2. rewrite (proj1 (proj2 (proj2 (s2_shape s n D_I)))), length_app. cbn. lia. Qed.
  Lemma D_reg3 : ltac2:(tb__ "0|0|
S2S1S10S25A1S53Vs3;S6dA2SdS25S87Vn;A1A2A3S1S0S68VL3;S6dA2VzR;A3A2").
  Proof using Hext Hframe MGP.
    split; [exact (region_s3 s n D_I s3 Hframe)|].
    destruct Hext as (_ & _ & _ & ER & _). rewrite (ER d_r D_r_lt). exact (mgLnew s L zR).
  Qed.
  Lemma D_eN_In : ltac2:(tb__ "0|0|
S7eSaS52S0A2S7S52S0S4cS23S6dZ0A2A1S6eA4S51Vs3;A1A3").
  Proof using Hext Hframe MGP. destruct D_reg3 as [RG _]. exact (footprint_region_In s3 _ _ RG eq_refl eq_refl). Qed.
  Lemma D_len : ltac2:(tb__ "0|0|
S2S17S1aZ20S28A2S6eA2S2S1S0S1cS6eS28A2Z0A3S2S17S6eS1dZ2Z3fA2A2S2S17S16Vn;Z14A2S6eA2S17Z1ffecVn;A2A2A2A2A2").
  Proof using MGP.
    pose proof (md_len_facts n D_n) as (L1 & L2 & L4 & L5 & L6). pose proof D_n as [N1 _].
    unfold md_needed, MMAP_THRESHOLD, IB, UNIT, PGSZ in *. unfold d_len. lia.
  Qed.
  Lemma D_zR : ltac2:(tb__ "0|1|
S2S17S28VzR;A2S2S17S16VzR;S6eA2S8dVL;A1M0A2S2S17G0Z7fffff800000A2S1S0S1cVzR;S28A2Z0A3A2A2A2").
  Proof using MGP. pose proof (mgA C s n L vm0 zR MGP) as (A1 & A2 & A3 & _). pose proof (mg_al _ _ _ _ _ _ MGP). unfold MapGrow.len, d_len in *. lia. Qed.

  Lemma D_am6_fields : ltac2:(tb__ "0|3|
S2S1S21S2fS6aA1S23S6dZ0M0A2A3S2S1S0S37S6aA1G0A3S2S1S0S38S6aA1S86Vn;A1A3S2S1S0S3bS6aA1Z3fA3S2S1S0S34S6aA1G0A3S2S1S0S35S6aA1G0A3S2S1S0S36S6aA1G0A3S2S1S10S21A1M1S3aS6aA1S11S21A1M2A3S2S1G1S39S6aA1G2A3S2S1S0S46S6aA1S85Vn;A1A3S2S1S45S42S6aG0A2S41SdSaS0S0A2S84Vs;Vn;A2A2SdS40S83Vs;Vn;A2A2A2A3S2S1S21S44S6aG0A2S23S6dS24A2A3S1S21S7dS23S6dS16S24S1aS24S6fA2A2A2A3A2A2A2A2A2A2A2A2A2A2A2A2").
  Proof using MGP.
    pose proof (stride_am4 s n D_n) as ST.
    pose proof (upd_slot_fields (md_am4 s n) 0 (mkSlot (Some (md_hdr s n)) (Some (md_fr s n)))) as (U1 & U2 & U3 & U4 & U5 & U6 & U7).
    assert (SS : slot_start (md_am4 s n) 0 = SP d_r UNIT).
    { unfold slot_start. rewrite ST, Z.mul_0_r, Z.add_0_r. unfold md_am4, direct_am. cbn [am_mem padd]. unfold d_r. f_equal. }
    unfold d_am6, md_am6. rewrite U1, U2, U3, U4, U5, U7. rewrite ST.
    repeat split; try reflexivity.
    - exact SS.
    - unfold d_p, md_p. rewrite SS. cbn [padd]. fold d_off. f_equal.
  Qed.
  Lemma D_nums : ltac2:(tb__ "0|4|
S2S2S17Z0M0S6fA2S17S6fZffA2A2S2S17S16S1aS24S6fA2M1Vn;A2S19S85Vn;A1M2S2eA2M3A2S2S1S0G2S19S6eS24A2A3S2S1S0S70S19S19G3G1A2Vn;A2A3S2S17G0S70A2S2S2S17G0S71A2S18S71S1dZ2Z20A2A2A2S1S0S69S6aA1S16Zfe0S6eA2A3A2A2A2A2A2A2").
  Proof using HMI3 Hframe HusedX MGP.
    pose proof (Inv_s6 s n D_I D_n s3 g D_I3 Hframe HusedX) as (_ & O1 & O2). pose proof (md_len_facts n D_n) as (_ & _ & L4 & _).
    pose proof (ctr_range s D_I) as [CR _].
    unfold d_off, d_res, md_reserved, d_len, d_ctr1 in *. repeat split; try lia.
    - unfold md_ctr1. apply Z.land_nonneg. right. lia.
    - unfold md_ctr1. change (2 ^ 32 - 1) with (Z.ones 32). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia.
    - unfold meta_bits. pose proof D_am6_fields as (_ & -> & -> & -> & _). unfold PGSZ in L4. lia.
  Qed.

  Lemma D_addr_r o : ltac2:(tb__ "0|0|
S1S0S90VL3;S23S6dVo;A2A2S16VzR;Vo;A2A3").
  Proof using Hext Hframe MGP. unfold addr_of, loc_addr. cbn [prid poff]. rewrite (proj2 D_reg3). reflexivity. Qed.

  Local Ltac tup := apply tup3; [lia | reflexivity | first [reflexivity | lia | unfold d_zG, addr_of; cbn [loc_addr]; lia] ].

  Definition dg_newcells : list mcell := ltac2:(tb__ "0|0|
S9S47S9cS71A1SbS47S58Vg;SdS22S27S6aA1A2A2SbS47S56Vg;S6aA2S81S6aA1A3A3A3").

  Definition d_touched (x : Z) : Prop := ltac2:(tb__ "0|1|
S4S2S17S6cVx;A2S18Vx;S16S6cS33A2A2A2S4S2S17S16S8cVC;A1S4fA2M0Vx;A2S18Vx;S16G0Z4A2A2A2S2S17VzR;Vx;A2S18Vx;S16VzR;S6eA2A2A2A2A2").
  Lemma d_touched_dec x : ltac2:(tb__ "0|1|
Sa4S72Vx;A1M0S3G0A1A2").
  Proof using .
    unfold d_touched. destruct (Z_le_dec d_zG x); destruct (Z_lt_dec x (d_zG + META_SIZE)); destruct (Z_le_dec (mc_ctx C + CTX_mmap_counter) x);
      destruct (Z_lt_dec x (mc_ctx C + CTX_mmap_counter + 4)); destruct (Z_le_dec zR x); destruct (Z_lt_dec x (zR + d_len)); try (left; lia); right; lia.
  Qed.

  Lemma D_s6_alt : ltac2:(tb__ "0|0|
S1S30S6bS26S71S9dVg;S27S6aA1Vs3;A3A2A3").
  Proof using .
    unfold d_s6, md_s6, md_s5, md_s4. fold d_am6. unfold d_ctr1. rewrite upd_meta_set_mmap_counter, upd_meta_twice. reflexivity.
  Qed.
  Lemma image6_cases c : ltac2:(tb__ "0|0|
S7eS47Vc;SbS47S48S6bA1S80S6bA1A3A3S4S7eS47Vc;S73A3S7eS47Vc;SbS47S48Vs3;A1S80Vs3;A1A3A3A2F_;").
  Proof using HMI3 Hraw.
    intros Hin. destruct D_MT3 as (xold & Hm & Hold). rewrite D_s6_alt in Hin. apply in_app_iff in Hin as [Hin|Hin].
    - apply image_set_mmap_counter in Hin as [->|Hin]; [left; left; reflexivity|].
      destruct (ui_image_In s3 g xold d_am6 D_ND3 Hm c Hin) as [H|[H|H]].
      + right. apply in_app_iff. left. exact H.
      + left. right. apply in_app_iff. left. exact H.
      + left. right. apply in_app_iff. right. apply in_app_iff. left. exact H.
    - rewrite footer_set_mmap_counter in Hin. destruct (ui_footer_In s3 g xold d_am6 D_ND3 Hm c Hin) as [H|H].
      + right. apply in_app_iff. right. exact H.
      + left. right. apply in_app_iff. right. apply in_app_iff. right. exact H.
  Qed.

  Definition d_st : Z := zR + UNIT.
  Definition d_e : Z := ltac2:(tb__ "0|0|
S19S16VzR;S6eA2S2eA2").
  Definition d_h3 : Z := ltac2:(tb__ "0|0|
S14S0S0S84Vs;Vn;A2A3").
  Definition d_h16 : Z := ltac2:(tb__ "0|0|
S15S0S0S84Vs;Vn;A2A3").
  Definition d_code : Z := md_rsv s n.
  Definition dg_spec : list (Z * nat * Z) := ltac2:(tb__ "0|f|
SbSaSaS0S8A2M0S0A2M1S9G1S7G0S0S7S0S8S16S8cVC;A1S4fA2U4M2A4S71A4S9G1S7G0S0S7S0S8S6cU8M3A4Z0M4A4S9G1S7G0S0S7S0S8S16S6cZ8M5A2G3A4G4A4S9G1S7G0S0S7S0S8S16S6cZ10A2G3A4VzR;A4S9G1S7G0S0S7S0S8S16S6cZ18A2G2A4G4A4S9G1S7G0S0S7S0S8S16S6cZ1cA2G2A4G4A4S9G1S7G0S0S7S0S8S16S6cZ20M6A2G3A4S16Zfe0S6eA2A4S9G1S7G0S0S7S0S8VzR;G3A4S6cA4S9G1S7G0S0S7S0S8S16VzR;G5A2G2A4G4A4S9G1S7G0S0S7S0S8S19S77Z4M7A2U1M8A4G4A4S9G1S7G0S0S7S0S8S19S77Z3M9A2G8A4S7cA4S9G1S7G0S0S7S0S8S19S77Z2MaA2U2MbA4S7bA4ScG1A1McA3A3A3A3A3A3A3A3A3A3A3A3SbG1SeSfG1A1L_;MdS1fS6fG4A2GcS9G1S7G0S0S7S0S8S19S74G7A2G8A4G4A4S9G1S7G0S0S7S0S8S19S74G9A2G8A4S1aG6S78A2A4S9G1S7G0S0S7S0S8S19S74GaA2GbA4S6fA4GcA3A3A3Xex2SbG1S9G1S7G0S0S7S0S8S76G8A4G4A4GcA3SbG1GdS1eG4S70A2S9G1S7G0S0S7S0S8S16S74Vn;A2G8A4G4A4GcA3GcXex2SbG1GdS20Z5MeS70A2S9G1S7G0S0S7S0S8S19S76G7A2G2A4S70A4GcA3GcXex2GdS1eGeS70A2S9G1S7G0S0S7S0S8S19S76GeA2G8A4G4A4GcA3GcXex2A3A3A3A3A3").

  Lemma D_ctx3 : ltac2:(tb__ "0|0|
S1S0S67VL3;A1S8cVC;A1A3"). Proof using HMI3. exact (mig_ctx HMI3). Qed.

  Lemma D_fr : ltac2:(tb__ "0|1|
S2S1S0S3fS83Vs;Vn;A2M0A1S6fA3S2S1S0S3eG0A1Vn;A3S1S3cS3dG0A1S32A3A2A2"). Proof using . repeat split; reflexivity. Qed.
  Lemma D_hb3 : ltac2:(tb__ "0|0|
S1S0S64S6aZ0S83Vs;Vn;A2A3S1aZ20S78A2A3").
  Proof using MGP.
    pose proof D_am6_fields as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Fst & _).
    unfold hdr_byte3. rewrite (proj2 (proj2 D_fr)). unfold rsv_code, d_code, md_rsv, md_reserved. rewrite Fst, (proj1 D_fr), (proj1 (proj2 D_fr)). unfold d_off. lia.
  Qed.
  Lemma D_ho16 : ltac2:(tb__ "0|0|
S1S0S65S6aZ0S83Vs;Vn;A2A3S6fA3").
  Proof using MGP.
    pose proof D_am6_fields as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Fst & _).
    unfold hdr_off16. rewrite Fst, Z.mul_0_r, (proj1 D_fr). unfold UNIT. rewrite Z.div_0_l by lia. apply Z.add_0_l.
  Qed.
  Lemma D_resv : ltac2:(tb__ "0|0|
S1S0S82S6aS83Vs;Vn;A2A2S70A3").
  Proof using HMI3 Hframe HusedX MGP.
    pose proof D_am6_fields as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Fst & _). pose proof D_nums as (_ & _ & _ & RS & _).
    unfold reserved_of. rewrite Fst, (proj1 D_fr), (proj1 (proj2 D_fr)). symmetry. exact RS.
  Qed.
  Lemma D_addr_g d : ltac2:(tb__ "0|0|
S1S0S49VL3;S4cS29Vg;Vd;A2A1A2S16S6cVd;A2A3").
  Proof using HMI3 Hkey Hraw HusedX. unfold d_zG, addr_of, loc_addr. destruct g; cbn [padd]. lia. Qed.
  Lemma D_addr_r1 o d : ltac2:(tb__ "0|0|
S1S0S49VL3;S4cS29S23S6dVo;A2Vd;A2A1A2S16S16VzR;Vo;A2Vd;A2A3").
  Proof using Hext Hframe MGP. cbn [padd loc_addr]. rewrite (proj2 D_reg3). lia. Qed.
  Lemma D_addr_r2 o d d' : ltac2:(tb__ "0|0|
S1S0S49VL3;S4cS29S29S23S6dVo;A2Vd;A2Vd';A2A1A2S16S16S16VzR;Vo;A2Vd;A2Vd';A2A3").
  Proof using Hext Hframe MGP. cbn [padd loc_addr]. rewrite (proj2 D_reg3). lia. Qed.
  Lemma D_addr_r0 o : ltac2:(tb__ "0|0|
S1S0S49VL3;S4cS23S6dVo;A2A1A2S16VzR;Vo;A2A3").
  Proof using Hext Hframe MGP. cbn [loc_addr]. rewrite (proj2 D_reg3). lia. Qed.

  Definition cell_ok (c : mcell) : Prop := ltac2:(tb__ "0|2|
S2S7eSaSaS0S8A2M0S0A2S7G0S0S7S0S8S49VL3;S4eVc;A1A2S4aVc;A1A4S5aVL3;S57Vc;A1M1A2A4S7aA3S2S0S3S1S59G1S60R1A1A3A1Fv;S3S1S59G1S61A3A1A2A2").
  Local Ltac fin k := split; [do k (apply in_app_iff; right) | split; [intros ? E; discriminate E | discriminate]].

  Lemma spec_ctr : cell_ok (ctr_cell d_ctr1).
  Proof using HMI3. unfold cell_ok, ctr_cell. cbn [mc_loc mc_w mc_val loc_addr sval_num]. rewrite D_ctx3. split; [left; reflexivity|]. split; [intros v E; discriminate E | discriminate]. Qed.

  Lemma spec_meta c : ltac2:(tb__ "0|0|
S7eS47Vc;S58Vg;SdS22S27S6aA1A2A2A3S75Vc;A1F_;").
  Proof using HMI3 Hext Hframe Hkey Hraw HusedX MGP.
    pose proof D_am6_fields as (Fmem & Flast & Fml & Fsc & Faidx & Fav & Ffr & Fpv & Fnx & Fst & Fsl & Fss & Fp). pose proof D_nums as (_ & _ & _ & _ & _ & _ & MB).
    intros Hin. unfold meta_slot_cells in Hin. rewrite Fpv, Fnx, Fmem, Fav, Ffr, MB in Hin. cbn [optr] in Hin.
    unfold META_prev, META_next, META_mem, META_avail, META_freed, META_bits in Hin. unfold cell_ok.
    destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [mc_loc mc_w mc_val sval_num]; rewrite D_addr_g; rewrite ?D_addr_r0;
      (split; [|split; [intros v E; discriminate E | discriminate]]);
      [right; left | do 2 right; left | do 3 right; left | do 4 right; left | do 5 right; left | do 6 right; left]; tup.
  Qed.

  Lemma spec_group c : ltac2:(tb__ "0|0|
S7eS47Vc;S56Vg;S6aA2A3S75Vc;A1F_;").
  Proof using HMI3 Hext Hframe HusedX MGP.
    pose proof D_am6_fields as (Fmem & Flast & Fml & Fsc & Faidx & Fav & Ffr & Fpv & Fnx & Fst & Fsl & Fss & Fp). pose proof D_nums as (O1 & O2 & ST & RS & R0 & CR & MB).
    pose proof (md_len_facts n D_n) as (_ & _ & L4 & L5 & _). pose proof D_fr as (FO & FN & FK).
    assert (ML : (am_maplen d_am6 =? 0) = false) by (rewrite Fml; apply Z.eqb_neq; lia).
    intros Hin. unfold group_cells in Hin. rewrite ML, Fmem, Faidx, Flast in Hin. change (zseq 0 (0 + 1)) with [0] in Hin. cbn [flat_map] in Hin. rewrite app_nil_r in Hin.
    unfold slot_cells in Hin. rewrite Fsl, Fss in Hin. cbn [ss_hdr ss_fr] in Hin. rewrite FO, D_hb3, D_ho16 in Hin. unfold cell_ok.
    apply in_app_iff in Hin as [Hin|Hin].
    - destruct Hin as [<-|[<-|[]]]; cbn [mc_loc mc_w mc_val sval_num]; rewrite ?D_addr_r1, ?D_addr_r0; (split; [|split; [intros v E; discriminate E | discriminate]]);
        [do 7 right; left | do 8 right; left]; tup.
    - apply in_app_iff in Hin as [Hin|Hin]; [|apply in_app_iff in Hin as [Hin|Hin]].
      + destruct Hin as [<-|[]]. cbn [mc_loc mc_w mc_val sval_num]. rewrite D_addr_r1. split; [do 9 right; left; unfold d_st; tup|]. split; [intros v E; discriminate E | discriminate].
      + rewrite (surjective_pairing (md_hdr s n)) in Hin. cbn iota in Hin.
        destruct Hin as [<-|[<-|[]]]; cbn [mc_loc mc_w mc_val sval_num]; rewrite D_addr_r1; (split; [|split; [intros v E; discriminate E | discriminate]]);
          [do 10 right; left | do 11 right; left]; unfold d_st, d_h3, d_h16; tup.
      + unfold dg_spec. destruct (d_off =? 0) eqn:E0; [destruct Hin|].
        destruct Hin as [<-|[<-|[<-|[]]]]; cbn [mc_loc mc_w mc_val sval_num]; rewrite D_addr_r2; (split; [|split; [intros v E; discriminate E | discriminate]]);
          apply in_app_iff; right; apply in_app_iff; left; cbn [In]; unfold d_zP; [left | right; left | right; right; left]; tup.
  Qed.

  Lemma spec_footer c : ltac2:(tb__ "0|0|
S7eS47Vc;S81S6aA1A3S75Vc;A1F_;").
  Proof using HMI3 Hext Hframe HusedX MGP.
    pose proof D_am6_fields as (Fmem & Flast & Fml & Fsc & Faidx & Fav & Ffr & Fpv & Fnx & Fst & Fsl & Fss & Fp). pose proof D_nums as (O1 & O2 & ST & RS & R0 & CR & MB).
    pose proof (md_len_facts n D_n) as (_ & _ & L4 & L5 & _). pose proof D_fr as (FO & FN & FK).
    intros Hin. unfold group_footer_cells in Hin. rewrite Flast in Hin. change (zseq 0 (0 + 1)) with [0] in Hin. cbn [flat_map] in Hin. rewrite Fsl in Hin. cbn [ss_fr] in Hin. rewrite app_nil_r in Hin.
    unfold cell_ok, dg_spec. destruct Hin as [<-|Hin].
    - unfold trailing_cell, trailing_loc. rewrite Fmem, Fst, Flast. cbn [mc_loc mc_w mc_val sval_num]. rewrite D_addr_r1.
      split; [|split; [intros v E; discriminate E | discriminate]]. do 2 (apply in_app_iff; right). apply in_app_iff; left. left. unfold d_e, IB, UNIT in *. tup.
    - unfold frame_footer_cells in Hin. rewrite FK, FN, D_resv in Hin. unfold frame_ptr, slot_end in Hin. rewrite Fss, Fst, FO in Hin.
      rewrite !in_app_iff in Hin. destruct Hin as [Hin|[Hin|Hin]].
      + destruct (0 <? d_res) eqn:E; [|destruct Hin]. destruct Hin as [<-|[]]. cbn [mc_loc mc_w mc_val sval_num]. rewrite D_addr_r2.
        split; [|split; [intros v E'; discriminate E' | discriminate]]. do 3 (apply in_app_iff; right). apply in_app_iff; left. left. unfold d_zP. tup.
      + destruct (5 <=? d_res) eqn:E; [|destruct Hin]. destruct Hin as [<-|[]]. cbn [mc_loc mc_w mc_val sval_num]. rewrite D_addr_r2.
        split; [|split; [intros v E'; discriminate E' | discriminate]]. do 4 (apply in_app_iff; right). apply in_app_iff; left. left. unfold d_e, IB, UNIT in *. tup.
      + destruct (5 <? d_res) eqn:E; [|destruct Hin]. destruct Hin as [<-|[]]. cbn [mc_loc mc_w mc_val sval_num]. rewrite D_addr_r2.
        split; [|split; [intros v E'; discriminate E' | discriminate]]. do 5 (apply in_app_iff; right). left. unfold d_e, IB, UNIT in *. tup.
  Qed.

  Theorem dg_newcells_spec c : ltac2:(tb__ "0|0|
S7eS47Vc;S73A3S75Vc;A1F_;").
  Proof using HMI3 Hext Hframe Hkey Hraw HusedX MGP.
    intros Hin. unfold dg_newcells in Hin. destruct Hin as [<-|Hin]; [exact spec_ctr|].
    apply in_app_iff in Hin as [Hin|Hin]; [exact (spec_meta c Hin)|].
    apply in_app_iff in Hin as [Hin|Hin]; [exact (spec_group c Hin) | exact (spec_footer c Hin)].
  Qed.

  Lemma D_top3 : ltac2:(tb__ "0|0|
S1S0S8dVL3;A1S8dVL;A1A3").
  Proof using Hext. destruct Hext as (_ & _ & _ & _ & ET). unfold topL. rewrite ET. reflexivity. Qed.
  Lemma D_zG : ltac2:(tb__ "0|0|
S2S17Z1000S6cA2S2S17S16S6cZ28A2S8dVL;A1A2S1S0S1cS6cZ8A2Z0A3A2A2").
  Proof using HMI3 Hext Hkey.
    rewrite <- D_top3.
    pose proof (Zones2.key_range [g] None U0 s3 L3 D_I3 D_L3 C vm3 g Hkey (mig_vm HMI3) (mig_ledger HMI3)) as (K1 & K2 & _).
    destruct (Zones2.key_area [g] None U0 s3 D_I3 g Hkey) as (a & k & Ha & Hk & Eq).
    pose proof (inv_areas D_I3) as (_ & AOK & _). destruct (AOK a Ha) as (r & o & rga & Ea & Hoo & _ & Hra & Hla & _).
    pose proof D_L3 as (_ & Halign & _). pose proof (Halign _ _ Hra Hla) as RA.
    split; [unfold d_zG, PGSZ in *; lia|]. split; [unfold d_zG, META_SIZE in *; lia|].
    unfold d_zG, addr_of, loc_addr. rewrite Eq, Ea. cbn [padd prid poff]. unfold AREA_HDR, META_SIZE, PGSZ in *. Z.to_euclidean_division_equations; lia.
  Qed.
  Lemma dg_spec_zone a w v : ltac2:(tb__ "0|1|
S7eSaSaS0S8A2M0S0A2S7G0S0S7S0S8Va;Vw;A4Vv;A4S7aA3S8S7fR1Vw;A2S72S16Va;S1bR2A1A2A1F_;Fk;F_;").
  Proof using HMI3 Hframe HusedX MGP.
    pose proof D_nums as (O1 & O2 & ST & RS & R0 & CR & MB). pose proof D_len as (Q1 & Q2 & Q3 & Q4 & Q5).
    intros Hin k Hk. unfold dg_spec in Hin. rewrite !in_app_iff in Hin. cbn [In] in Hin.
    unfold d_touched.
    destruct Hin as [Hin|[Hin|[Hin|[Hin|[Hin|Hin]]]]].
    - destruct Hin as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]]]]; injection E as <- <- <-; unfold CTX_mmap_counter, d_st, d_e, d_zP, UNIT, IB, PGSZ, META_SIZE in *; lia.
    - destruct (d_off =? 0); [destruct Hin|]. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <- <-; unfold CTX_mmap_counter, d_st, d_e, d_zP, UNIT, IB, PGSZ, META_SIZE in *; lia.
    - destruct Hin as [E|[]]; injection E as <- <- <-; unfold CTX_mmap_counter, d_st, d_e, d_zP, UNIT, IB, PGSZ, META_SIZE in *; lia.
    - destruct (0 <? d_res) eqn:E0; [|destruct Hin]. apply Z.ltb_lt in E0. destruct Hin as [E|[]]; injection E as <- <- <-; unfold CTX_mmap_counter, d_st, d_e, d_zP, UNIT, IB, PGSZ, META_SIZE in *; lia.
    - destruct (5 <=? d_res) eqn:E0; [|destruct Hin]. apply Z.leb_le in E0. destruct Hin as [E|[]]; injection E as <- <- <-; unfold CTX_mmap_counter, d_st, d_e, d_zP, UNIT, IB, PGSZ, META_SIZE in *; lia.
    - destruct (5 <? d_res) eqn:E0; [|destruct Hin]. apply Z.ltb_lt in E0. destruct Hin as [E|[]]; injection E as <- <- <-; unfold CTX_mmap_counter, d_st, d_e, d_zP, UNIT, IB, PGSZ, META_SIZE in *; lia.
  Qed.
  Lemma dg_new_zone c : ltac2:(tb__ "0|0|
S7eS47Vc;S73A3S8S7fR1S4aVc;A1A2S72S16S49VL3;S4eVc;A1A2S1bR2A1A2A1F_;Fk;F_;").
  Proof using HMI3 Hext Hframe Hkey Hraw HusedX MGP. intros Hin k Hk. destruct (dg_newcells_spec c Hin) as (Hs & _). exact (dg_spec_zone _ _ _ Hs k Hk). Qed.
  Lemma dg_new_w c : ltac2:(tb__ "0|0|
S7eS47Vc;S73A3S7fU0S4aVc;A1A2F_;").
  Proof using HMI3 Hext Hframe Hkey Hraw HusedX MGP.
    intros Hin. destruct (dg_newcells_spec c Hin) as (Hs & _). unfold dg_spec in Hs. rewrite !in_app_iff in Hs. cbn [In] in Hs.
    destruct Hs as [Hs|[Hs|[Hs|[Hs|[Hs|Hs]]]]].
    - destruct Hs as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]]]]; injection E as _ <- _; lia.
    - destruct (d_off =? 0); [destruct Hs|]. destruct Hs as [E|[E|[E|[]]]]; injection E as _ <- _; lia.
    - destruct Hs as [E|[]]; injection E as _ <- _; lia.
    - destruct (0 <? d_res); [|destruct Hs]. destruct Hs as [E|[]]; injection E as _ <- _; lia.
    - destruct (5 <=? d_res); [|destruct Hs]. destruct Hs as [E|[]]; injection E as _ <- _; lia.
    - destruct (5 <? d_res); [|destruct Hs]. destruct Hs as [E|[]]; injection E as _ <- _; lia.
  Qed.

  Definition d_meets (c : mcell) : Prop := ltac2:(tb__ "0|0|
S5S8S8S2S7fR1S4aVc;A1A2S72S16S49VL3;S4eVc;A1A2S1bR1A1A2A1A2Lk;A2").

  Lemma D_used6 q a : ltac2:(tb__ "0|2|
S4bScS21A1M0S6bVq;Va;A4S4S2S1S21Vq;Vg;A3M1S1S2dVa;S6aA3A2S2S3G1A1S4bS9S21Vg;G0A3Vs3;Vq;Va;A4A2A2F_;").
  Proof using .
    intros Hu. apply usedX_MT in Hu as [M _]. unfold d_s6 in M. rewrite MT_s6 in M.
    destruct (sptr_eqb q g) eqn:E.
    - apply sptr_eqb_eq in E. left. split; [exact E | injection M as M'; symmetry; exact M'].
    - right. assert (NE : q <> g) by (intros ->; rewrite sptr_eqb_refl in E; discriminate E).
      split; [exact NE|]. apply usedX_intro; [|exact M]. cbn. destruct (sptr_eqb q g) eqn:E'; [|reflexivity]. apply sptr_eqb_eq in E'. exfalso. exact (NE E').
  Qed.
  Lemma D_fresh q a : ltac2:(tb__ "0|0|
S4bS9S21Vg;ScS21A1A3Vs3;Vq;Va;A4S7fS43S2fVa;A1A1S6dA2F_;").
  Proof using HusedX MGP. intros Hu. apply HusedX in Hu. exact (fresh_s2 s n D_I q a Hu). Qed.

  Theorem meets_new c : ltac2:(tb__ "0|0|
S7eS47Vc;SbS47S48S6bA1S80S6bA1A3A3S79Vc;A1S7eS47Vc;S73A3F_;F_;").
  Proof using HMI3 Hext Hframe Hkey Hraw Hub3 HusedX MGP.
    intros Hin (k & Hk & T). pose proof D_zG as (G1 & G2 & G3). pose proof D_len as (L1 & _).
    destruct T as [T|[T|T]].
    -
      pose proof (Zones2.meta_zone [] None U0 d_s6 L3 D_I6 D_X6 D_L6 g c D_key6 Hin ltac:(exists k; split; [exact Hk | unfold d_zG in T; exact T])) as M.
      rewrite D_MT6 in M. right. apply in_app_iff. left. exact M.
    -
      destruct (Zones2.ctx_zone [] None U0 d_s6 L3 D_I6 D_X6 D_L6 c CTX_mmap_counter 4 Hin ltac:(unfold CTX_mmap_counter; lia) ltac:(unfold CTX_mmap_counter, CTX_SIZE; lia)
                  ltac:(exists k; split; [exact Hk | rewrite (mig_ctx HMI3 : ly_ctx L3 = mc_ctx C) || rewrite D_ctx3; exact T])) as (Hc & o & Ho & O1 & O2).
      left. rewrite <- D_ctr6. symmetry. apply (ctx_cells_at_ctr d_s6 c o Hc Ho); unfold CTX_mmap_counter in *; lia.
    -
      right. apply in_app_iff. right.
      assert (ER6 : In (Zones2.e_reg d_r (md_rg n)) (footprint d_s6)) by (rewrite D_fp; exact D_eN_In).
      assert (RI : range_incl (zR, d_len) (crange L3 (Zones2.e_reg d_r (md_rg n)))).
      { unfold range_incl, crange, Zones2.e_reg. cbn [fst snd loc_addr md_rg rg_len]. rewrite (proj2 D_reg3). unfold d_len. lia. }
      assert (CM : Zones2.cmeets L3 c zR d_len) by (exists k; split; [exact Hk | exact T]).
      destruct (Zones2.cell_cases [] None U0 d_s6 D_I6 D_X6 c Hin) as [Hc | [(a' & next & Ha' & Hc) | (q & am & Hu & Hc)]].
      + exfalso. refine (Zones2.meet_entries d_s6 L3 D_L6 c Zones2.e_ctx (Zones2.e_reg d_r (md_rg n)) zR d_len (Zones2.e_ctx_In d_s6) ER6 _ (Zones2.ctx_cell_in d_s6 L3 c Hc) RI CM). discriminate.
      + exfalso. refine (Zones2.meet_entries d_s6 L3 D_L6 c (Zones2.e_area a') (Zones2.e_reg d_r (md_rg n)) zR d_len (Zones2.e_area_In d_s6 a' Ha') ER6 _ (Zones2.area_cell_in d_s6 L3 a' next c Hc) RI CM).
        unfold Zones2.e_area, Zones2.e_reg. intros E. injection E as Ea _. pose proof (Zones2.area_not_origin [] None U0 d_s6 D_I6 a' Ha') as Z0. rewrite Ea in Z0. exact (Z0 eq_refl).
      + destruct (Zones2.group_cell_in [] None U0 d_s6 L3 D_I6 q am c Hu Hc) as (rg & Hrg & _ & _ & ERq & RIq & _).
        destruct (D_used6 q am Hu) as [[-> ->] | [NE Hu3]].
        * apply in_app_iff. exact Hc.
        * exfalso. pose proof (D_fresh q am Hu3) as FR.
          refine (Zones2.meet_entries d_s6 L3 D_L6 c (Zones2.e_reg (prid (am_mem am)) rg) (Zones2.e_reg d_r (md_rg n)) zR d_len ERq ER6 _ RIq RI CM).
          unfold Zones2.e_reg. intros E. injection E as Er _. lia.
  Qed.

  Corollary old_kept c : ltac2:(tb__ "0|0|
S7eS47Vc;SbS47S48S6bA1S80S6bA1A3A3S3S79Vc;A1A1S7eS47Vc;SbS47S48Vs3;A1S80Vs3;A1A3A3F_;F_;").
  Proof using HMI3 Hext Hframe Hkey Hraw HusedX MGP.
    intros Hin NM. destruct (image6_cases c Hin) as [N|O]; [|exact O]. exfalso. apply NM.
    exists 0%nat. split; [exact (dg_new_w c N) | exact (dg_new_zone c N 0%nat (dg_new_w c N))].
  Qed.

  Lemma D_bounded6 : bounded d_s6.
  Proof using HMI3 Hframe Hkey Hraw Hub3 HusedX MGP.
    pose proof (mig_bounded HMI3) as (B1 & B2 & B3 & B4). cbn [ma_s] in *.
    pose proof (s6_shape s n s3 g D_I3 Hraw Hkey Hframe HusedX Hub3 D_ctr3) as (R1 & R2 & _ & _ & _ & _ & _ & _ & R9 & _ & _ & _ & _ & R14 & R15 & _ & _ & R18 & _).
    unfold bounded, usage_of in *. unfold d_s6. rewrite R9, R15, R2, R14, R18, R1. auto.
  Qed.
  Lemma D_vm6 : ltac2:(tb__ "0|0|
S9bVL3;S6bVvm3;A3").
  Proof using HMI3 Hframe Hkey Hraw Hub3 HusedX MGP.
    pose proof (mig_vm HMI3) as HV. cbn [ma_s ma_L] in HV.
    pose proof (s6_shape s n s3 g D_I3 Hraw Hkey Hframe HusedX Hub3 D_ctr3) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & R10 & _).
    pose proof D_regions as RG. pose proof D_fp as FP. unfold d_s6 in RG, FP |- *.
    unfold vm_ok in *. rewrite FP, R10. unfold region_of in *. rewrite RG. exact HV.
  Qed.
  Lemma D_init6 : ltac2:(tb__ "0|0|
S1SeS31S6bA1S31Vs3;A1A3").
  Proof using HMI3 Hframe Hkey Hraw Hub3 HusedX MGP. exact (proj1 (proj2 (proj2 (proj2 (s6_shape s n s3 g D_I3 Hraw Hkey Hframe HusedX Hub3 D_ctr3))))). Qed.
  Lemma D_ub6 : ltac2:(tb__ "0|1|
SaS21S0A2M0S7eG0R1S5cVs3;A1A3S7eG0R2S5cS6bA1A3F_;Fb;").
  Proof using HMI3 Hraw.
    intros b Hb. destruct D_MT3 as (xold & Hm & Hold).
    destruct (ui_user_blocks_gen s3 g xold d_am6 D_ND3 Hm Hold) as (l1 & l2 & E1 & E2).
    rewrite D_s6_alt. replace (user_blocks (set_mmap_counter d_ctr1 (upd_meta g (MUsed d_am6) s3))) with (user_blocks (upd_meta g (MUsed d_am6) s3)) by (generalize (upd_meta g (MUsed d_am6) s3); intros t; destruct t; reflexivity).
    rewrite E2. rewrite E1 in Hb. rewrite !in_app_iff in *. tauto.
  Qed.

  Hypothesis HRO : reach_ok s.
  Lemma D_RO3 : reach_ok s3.
  Proof using HRO Hraw HusedX MGP.
    apply (reach_ok_same_used (s2 s n)); [|apply (reach_ok_same_metas s); [exact (proj1 (s2_shape s n D_I)) | exact HRO]].
    intros q am. split; intros M.
    - assert (NE : memb q [g] = false).
      { cbn. destruct (sptr_eqb q g) eqn:E; [|reflexivity]. apply sptr_eqb_eq in E. subst q. exfalso. destruct (Hraw g ltac:(left; reflexivity)) as [R|R]; rewrite R in M; discriminate M. }
      exact (proj1 (usedX_MT _ _ _ _ (proj1 (HusedX q am) (usedX_intro _ _ _ _ NE M)))).
    - pose proof (proj2 (HusedX q am) (usedX_intro [] _ _ _ eq_refl M)) as U. exact (proj1 (usedX_MT _ _ _ _ U)).
  Qed.
  Lemma D_RO6 : reach_ok d_s6.
  Proof using HMI3 HRO Hframe Hraw HusedX MGP.
    pose proof D_am6_fields as (Fmem & Flast & Fml & Fsc & Faidx & Fav & Ffr & Fpv & Fnx & Fst & Fsl & Fss & Fp). pose proof D_len as (L1 & _). pose proof D_nums as (_ & _ & ST & _).
    rewrite D_s6_alt. apply reach_ok_same_metas with (s := upd_meta g (MUsed d_am6) s3); [destruct (upd_meta g (MUsed d_am6) s3); reflexivity|].
    apply reach_ok_install; [| rewrite Fst; unfold UNIT, PGSZ in *; lia | | rewrite Fml; pose proof (md_len_facts n D_n); lia | rewrite Faidx, Flast; lia | exact D_RO3].
    - intros am M. destruct (Hraw g ltac:(left; reflexivity)) as [R|R]; rewrite R in M; discriminate M.
    - intros q am i M Hml Hi E. rewrite Flast in Hi. assert (i = 0) as -> by lia. rewrite Fss in E.
      assert (U : usedX [g] s3 q am).
      { apply usedX_intro; [|exact M]. cbn. destruct (sptr_eqb q g) eqn:Eq; [|reflexivity]. apply sptr_eqb_eq in Eq. subst q.
        destruct (Hraw g ltac:(left; reflexivity)) as [R|R]; rewrite R in M; discriminate M. }
      pose proof (D_fresh q am U) as FR. rewrite E in FR. cbn [prid] in FR. lia.
  Qed.

  Hypothesis V1 : ltac2:(tb__ "0|1|
S0S2S17Z0R1A2S18R1S1dZ2Z40A2A2A2S3S72R2A1A1S2S1S10S9fQ8A1A1Vrd1;S8eR3A1M0A1Vrd0;G0A1A3S1SeVwok1;G0A1Vwok0;G0A1A3A2F_;F_;Fx;").
  Hypothesis V2 : ltac2:(tb__ "0|1|
S0S72R1A1S63VL3;S6bR2A3S2S1SeVwok1;S8eR3A1A1S13A3S5S9fQ8A1M0G0S1S10G0A1Vrd1;S8eR4A1A1SdG0R1A2A3Lb;A2A2F_;F_;Fx;").
  Hypothesis V3 : ltac2:(tb__ "0|3|
S47S7eS47R1S73A3S8S7fR1S4aR3A1A2S2S1SeVwok1;S8eS16S49VL3;S4eR4A1A2S1bR2A1A2A1M0A1S13A3S1S10S9fQ8M1A1M2A1Vrd1;G0A1SdG2Sa0G1S66S5aVL3;S57R4A1A2S4aR4A1R2A3A2A2A3A2F_;Fj;F_;Fc;").

  Hypothesis HSD : ltac2:(tb__ "0|d|
S0S4S2S17S8cVC;A1M0R1A2S18R1S16G0S5dA2A2A2S2S17S94VC;A1M1R1A2S18R1S16G1Z4M2A2A2A2A2S2S3S2S17S95VC;A1M3R2A2S18R2S16G3Z38A2A2A2A1S2S3S2S17S98VC;A1M4R2A2S18R2S16G4G2A2A2A2A1S2S3S2S17S96VC;A1M5R2A2S18R2S16G5G2A2A2A2A1S2S3S2S17S99VC;A1M6R2A2S18R2S16G6Z60A2A2A2A1S2S3S2S17S9aVC;A1M7R2A2S18R2S16G7Z1bA2A2A2A1S2S3S2S17S97VC;A1M8R2A2S18R2S16G8G2A2A2A2A1S2S3S2S17S93VC;A1M9R2A2S18R2S16G9Z20A2A2A2A1S2S3S2S17S92VC;A1MaR2A2S18R2S16GaZ8MbA2A2A2A1S3S2S17S91VC;A1McR2A2S18R2S16GcGbA2A2A2A1A2A2A2A2A2A2A2A2F_;Fx;").

  Theorem minv6 : ltac2:(tb__ "0|0|
Sa2VC;Sa1S6bVL3;A2Vrd1;Vwok1;Vvm3;A5").
  Proof using HMI3 HRO HS HSD Hext Hframe Hinit3 Hkey Hraw Hub3 HusedX MGP V1 V2 V3.
    pose proof D_zG as (G1 & G2 & G3). pose proof D_zR as (Z1 & Z2 & Z3 & Z4). pose proof D_len as (L1 & _).
    pose proof HS as HSI'. unfold statics_in_image in HSI'. cbn beta zeta in HSI'.
    apply MInv_MInvG. split; [|exact D_RO6].
    refine (minv_postB C (Inv [g] None U0) WF s3 d_s6 L3 rd0 rd1 wok0 wok1 vm3 HMI3 D_I6 D_bounded6 D_L6 D_fp D_ub6 D_vm6
              d_touched d_touched_dec _ _ _ _ _ _ _ HS _ HSD _).
    - intros x Hx NT. destruct (V1 x Hx NT) as [E1 E2]. unfold bg_bv1, bg_bv0, bg_rv1, bg_rv0, byteview_of. unfold wz in E1, E2. rewrite E1, E2. split; reflexivity.
    - intros c Hin HM. pose proof (meets_new c Hin HM) as N. destruct (dg_newcells_spec c N) as (_ & NV & _).
      pose proof (Zones2.cell_spanI [] None U0 d_s6 L3 D_I6 D_X6 D_L6 c Hin) as [SP1 SP2].
      unfold cell_holds. destruct (mc_val c) as [v|q|v|] eqn:Ev; [| | exfalso; exact (NV v eq_refl) |];
        intros j Hj; destruct (V3 c N j Hj) as [E1 E2]; rewrite Ev in E2; unfold bg_bv1, byteview_of; unfold wz in E1, E2;
        (replace ((0 <=? loc_addr L3 (mc_loc c) + Z.of_nat j) && (loc_addr L3 (mc_loc c) + Z.of_nat j <? 2 ^ 64))%bool with true
           by (symmetry; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia));
        cbn [andb]; rewrite E1, E2; f_equal; apply Z_to_bv_small; change (bv_modulus 8) with 256; unfold le_byte; apply Z.mod_pos_bound; lia.
    - intros x Hx T OW. destruct (V2 x T OW) as [E1 [b E2]]. unfold bg_bv1, byteview_of. unfold wz in E1, E2.
      replace ((0 <=? x) && (x <? 2 ^ 64))%bool with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
      cbn [andb]. rewrite E1, E2. discriminate.
    - intros c Hin NM. exact (old_kept c Hin NM).
    - intros c Hin. exact (Zones2.cell_spanI [] None U0 d_s6 L3 D_I6 D_X6 D_L6 c Hin).
    - intros x Hx. exact (Zones2.owned_spanI d_s6 L3 D_L6 x Hx).
    - intros c Hin. exact (Zones2.cell_w_posI d_s6 c Hin).
    - intros x T Himg. pose proof (mgImg C s n L vm0 zR MGP x Himg) as NG. unfold MapGrow.len in NG. fold d_len in NG.
      pose proof (Zones2.key_range [g] None U0 s3 L3 D_I3 D_L3 C vm3 g Hkey (mig_vm HMI3) (mig_ledger HMI3)) as (_ & _ & KI).
      destruct T as [T|[T|T]]; [exfalso; unfold d_zG, META_SIZE in *; lia | left; unfold CTX_mmap_counter, CTX_SIZE in *; lia | exfalso; exact (NG T)].
    - intros Hf. exfalso. rewrite D_init6, Hinit3 in Hf. discriminate Hf.
  Qed.

  Theorem blocks6 : ltac2:(tb__ "0|2|
S5SfSaS0S0A2M0A1M1G1S5G1G1S2S1G1S8fVL3;S6bA2SbG0R2S9G0S7S0S0S74Vn;A4R1A3A3A3S1G1S8fVL;Vs;A2SbG0R2R1A3A3A2Ll2;A2Ll1;A2").
  Proof using HMI3 Hext Hframe Hub3 HusedX MGP.
    destruct (blocks_s6 s n D_I D_n s3 g D_I3 Hframe HusedX Hub3) as (l1 & l2 & E1 & E2).
    pose proof D_am6_fields as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Fp).
    exists (map (fun b : sptr * Z => (addr_of L3 (fst b), snd b)) l1), (map (fun b : sptr * Z => (addr_of L3 (fst b), snd b)) l2).
    unfold blocks. fold d_s6 in E1. rewrite E1, E2, !map_app. cbn [map fst snd]. split.
    - f_equal. f_equal. f_equal. fold d_p. rewrite Fp. rewrite D_addr_r. unfold d_zP, UNIT. lia.
    - rewrite <- !map_app. apply map_ext_in. intros [b k] Hb. cbn [fst snd]. f_equal.
      assert (UB : In (b, k) (user_blocks s)) by (rewrite E2; exact Hb).
      pose proof (user_block_below [] None U0 s D_I (xraw_nil s) (b, k) UB) as BL. cbn [fst] in BL.
      unfold addr_of. destruct Hext as (_ & _ & _ & ER & _). symmetry.
      pose proof (mgLub C s n L vm0 zR MGP (b, k) UB) as EU. cbn [fst] in EU. rewrite <- EU. unfold loc_addr. destruct b as [br bo]. cbn [prid] in BL.
      rewrite (ER br); [reflexivity|]. unfold s2. rewrite (proj1 (proj2 (proj2 (s2_shape s n D_I)))), length_app. cbn. lia.
  Qed.
End GapD.
