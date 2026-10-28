(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog MI_Inv MI_Read MI_Geom MI_Arith MI_Pres2 MI_WFree.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.Agent Require Import F_malloc_free_u MallocRep_u MallocTree_u MallocFacts_A_u MallocFacts_B_u MallocKit_A_u MallocBlocks_u MallocHINV_u Malloc_iface_u MallocFacts_inv_u MallocFacts_inv3_u F_malloc_top_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.Pm10 Require Import F_syscalls_u RMallocRep_u RMallocTree_u RMallocKit_B_u RF_get_meta_u RMalloc_iface_u RMalloc_ifaceP_u RF_malloc_top_u RF_malloc_spec_u RF_aligned_u.
Import ListNotations.
Import ITree.Exc.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.

Lemma byte_of_range : forall x k, 0 <= byte_of x k < 256.
Proof.
  intros x k. unfold byte_of. split; [apply Z.land_nonneg; right; lia|].
  change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia.
Qed.

Lemma le4_byte_of : forall r, 0 <= r < 2^32 ->
  le4 (wz r) = [b8 (byte_of r 0); b8 (byte_of r 1); b8 (byte_of r 2); b8 (byte_of r 3)].
Proof.
  intros r Hr. rewrite le4_bytes by lia. unfold byte_of. change 255 with (Z.ones 8). rewrite !Z.land_ones by lia.
  rewrite !Z.shiftr_div_pow2 by lia. change (2^(8*0)) with 1. change (2^(8*1)) with 256. change (2^(8*2)) with 65536. change (2^(8*3)) with 16777216.
  change (2^8) with 256. rewrite Z.div_1_r. f_equal. f_equal. f_equal. f_equal. f_equal. rewrite Z.mod_small; [reflexivity|].
  split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia.
Qed.

Lemma rw_cells_mk : forall m A cs, cells_wf cs -> bytes_at rsegs m A (cells_bytes cs) -> wr_at rsegs m A (Z.of_nat (cells_size cs)) -> rw_cells rsegs m A cs.
Proof. intros m A cs W B R. split; [split|]; assumption. Qed.

Lemma rmeta_addr_facts : forall st m g, rmrep st m -> meta_slot st g ->
  0 < conc st g /\ conc st g + 40 <= 2^64 /\ conc st (area_of g) = conc st g - conc st g mod 4096.
Proof.
  intros st m g MR MS. pose proof (rmeta_slot_bounds st _ g MR MS) as (GB0 & GB1 & _). pose_ceil.
  pose proof MR as (WF & _). pose proof WF as (Hres & WR & DISJ & WA & WG).
  destruct MS as (a & ara & k & Ha & Hkk & Eg).
  destruct (WA a ara Ha) as (rg & Hrg & A0 & A1 & AAL & ANG & _).
  assert (HG : conc st g = r_base rg + snd a + (AREA_HDR + META_SIZE * k)).
  { rewrite Eg, conc_aadd by (rewrite Hrg; eauto). rewrite (conc_region' st a rg Hrg). reflexivity. }
  destruct (WR (fst a) rg Hrg) as (RB0 & RBAL & RL0 & RBC & _). pose_ceil.
  assert (Hm : (r_base rg + snd a + (AREA_HDR + META_SIZE * k)) mod 4096 = AREA_HDR + META_SIZE * k).
  { unfold AREA_HDR, META_SIZE, NSLOTS in *.
    replace (r_base rg + snd a + (24 + 40 * k)) with ((24 + 40 * k) + (snd a / 4096 + r_base rg / 4096) * 4096) by (Z.div_mod_to_equations; nia).
    rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  split; [lia|]. split; [lia|].
  rewrite HG, Hm. unfold area_of. rewrite Eg. unfold aadd. cbn [fst snd]. rewrite (conc_region st (fst a) _ rg Hrg).
  replace ((snd a + (AREA_HDR + META_SIZE * k)) mod 4096) with (AREA_HDR + META_SIZE * k); [lia|].
  unfold AREA_HDR, META_SIZE, NSLOTS in *.
  replace (snd a + (24 + 40 * k)) with ((24 + 40 * k) + (snd a / 4096) * 4096) by (Z.div_mod_to_equations; nia).
  rewrite Z.mod_add by lia. symmetry. apply Z.mod_small. lia.
Qed.

Local Definition hide (P : Prop) : Prop := P.

Lemma raa_tail_spec :
  forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a0 : word) F fc (m : mem)
         (junk : list byte) (s1o s0o rao : word)
         (st : mstate) L BL LS (LB0 : list block) (c : cptr) (bo n : Z),
  rmrep st m -> mem_inv rsegs m -> CINV st LB0 -> INVL x0 st L BL LS -> In ((c, bo), n) BL ->
  (forall g i, (s_slots st) !! c = Some (g, i) -> get_stride (get_meta_rec st g) - IB - n < 2^31) ->
  rw_cells rsegs m (bv_unsigned sp) [CB 8 junk; C8 s1o; C8 s0o; C8 rao] ->
  alloc_ceiling <= bv_unsigned sp -> bv_unsigned sp + 32 <= 2^64 ->
  a0 = wz (conc st c + UNIT * bo) ->
  evt rsegs (raa_fin_post sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 s1o s0o rao F fc m)
      (MS (mkR (wz RAA_RET) sp gp tp t0 t1 t2 (wz 16) (wz n) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RAA_RET) fc None m (seg_rom rsegs)).
Proof.
  intros until n. intros MRP MI C INV Hk FIT FR CSP SPH HA0.
  destruct (block_facts x0 st L BL LS INV c bo n Hk) as (mt & bm & i & ai & a & ar & ka & BF).
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  pose proof MRP as (WF & CX & GL & ARS & GR & SH). pose proof WF as (Hres & WR & DISJ & WA & WG).

  pose proof (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF) as Hgh.
  destruct (WG bm _ Hgh) as (r & Hr & Hkd & Bm0 & Bm16r & BmAL).
  destruct (WR (fst bm) r Hr) as (RB0 & RBAL & RL0 & RBC & RFREE). pose_ceil.
  pose proof (proj1 (proj2 (proj2 (ir_shape _ _ _ IR _ _ Hr)))) as RLpos.
  pose proof (round_up_pg_ge (r_len r)) as RUP.
  pose proof (rreserved_disjoint1 _ _ RFREE ltac:(clear -RLpos RUP; lia)) as DRr.
  clear RFREE DISJ Hres.

  pose proof (ci_gmetas _ _ C bm mt ltac:(exists ai; exact Hgh)) as GO.
  pose proof (go_avail _ _ _ GO) as AV. pose proof (go_freed _ _ _ GO) as FRD. pose proof (go_li _ _ _ GO) as LI.
  pose proof (go_freeable _ _ _ GO) as FBL. pose proof (go_sc _ _ _ GO) as GSC. pose proof (go_maplen _ _ _ GO) as ML.
  pose proof (go_stride _ _ _ GO) as [S16 SMOD]. pose proof (go_mem _ _ _ GO) as Hmem.
  destruct (go_region _ _ _ GO) as (r' & Hr' & _ & _ & _ & SPAN & _). rewrite Hr in Hr'. assert (r' = r) by congruence. subst r'.
  unfold sstart_of in SPAN. rewrite Hmem in SPAN. cbn [default id snd] in SPAN.
  pose proof (ci_cx _ _ C) as (_ & _ & _ & _ & SE). clear C GO.
  set (mr := get_meta_rec st mt) in *.
  set (stride := get_stride mr) in *.

  pose proof (bf_slot _ _ _ _ _ _ _ _ _ _ _ BF) as Hs.
  pose proof (bf_c _ _ _ _ _ _ _ _ _ _ _ BF) as Ec.
  pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF) as Hi.
  pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF) as Hoff.
  pose proof (bf_n _ _ _ _ _ _ _ _ _ _ _ BF) as Hn.
  pose proof (bf_fit _ _ _ _ _ _ _ _ _ _ _ BF) as Hfit.
  pose proof (bf_notA _ _ _ _ _ _ _ _ _ _ _ BF) as NA.
  pose proof (bf_notF _ _ _ _ _ _ _ _ _ _ _ BF) as NF.
  pose proof (bf_sc _ _ _ _ _ _ _ _ _ _ _ BF) as BSC.
  pose proof (bf_top _ _ _ _ _ _ _ _ _ _ _ BF) as BTOP.
  destruct (bf_area _ _ _ _ _ _ _ _ _ _ _ BF) as (Ha & Hck & Hal & Hka & Emt).
  pose proof (bf_shadow _ _ _ _ _ _ _ _ _ _ _ BF) as SHB.
  pose proof (gbase_bm _ _ _ _ _ _ _ _ _ _ _ BF) as GB.
  pose proof (FIT mt i Hs) as FIT'. clear FIT BF Hk INV IR IA IM IL IG IS ISH.
  change (MR st) with (get_meta_rec st) in *. fold mr in Ec, Hi, Hfit, NA, NF, BSC, BTOP, SHB, GB, LI, FIT' |- *. fold stride in Hfit, BSC, FIT' |- *.
  unfold blk_shadow_ok in SHB. cbn [bslot boff bsize fst snd] in SHB. change (MR st mt) with mr in SHB. fold stride in SHB. rewrite GB in SHB.
  destruct SHB as (K4 & K3 & K2 & K1 & Q16 & K5 & Kr & KU). clear KU.
  assert (CF : fst c = fst bm) by (rewrite Ec; reflexivity).
  assert (CS : snd c = snd bm + 16 + stride * i) by (rewrite Ec; unfold sstart; cbn [snd]; rewrite GB; unfold UNIT; reflexivity).
  set (q := (snd c + UNIT * bo - snd bm - UNIT) / UNIT) in *.

  set (P := r_base r + (snd c + UNIT * bo)).
  assert (PM16 : hide (P mod 16 = 0)).
  { unfold hide. subst P. rewrite CS. unfold UNIT. replace (r_base r + (snd bm + 16 + stride * i + 16 * bo)) with (r_base r + snd bm + 16 + stride * i + 16 * bo) by (clear; lia).
    apply mod16_slot; [exact RBAL| exact BmAL| exact SMOD| clear -Hi; lia]. }
  assert (QE : UNIT * q = stride * i + UNIT * bo).
  { subst q. rewrite CS. unfold UNIT, IB in *.
    replace (snd bm + 16 + stride * i + 16 * bo - snd bm - 16) with (stride * i + 16 * bo) by (clear; lia).
    pose proof (Z.div_mod stride 16 ltac:(clear; lia)) as D. rewrite SMOD in D.
    replace (stride * i + 16 * bo) with ((stride / 16 * i + bo) * 16) by (clear -D; lia). rewrite Z.div_mul by (clear; lia). clear -D. lia. }
  clearbody q. clear RBAL BmAL SMOD Hal.

  unfold UNIT, IB in *.
  assert (SI0 : 0 <= stride * i) by (clear -S16 Hi; apply Z.mul_nonneg_nonneg; lia).
  assert (SIL : stride * i + stride <= stride * (m_last_idx mr + 1)).
  { rewrite <- (Z.mul_1_r stride) at 2. rewrite <- Z.mul_add_distr_l. apply Z.mul_le_mono_nonneg_l; clear -S16 Hi; lia. }
  set (B := r_base r + snd bm).
  set (EE := B + 16 + stride * (i + 1) - 4).
  set (res := EE - (P + n)).
  assert (HEE : EE = r_base r + snd c + stride - 4) by (subst EE B; rewrite CS; clear; lia).
  assert (HRES : res = stride - 4 - 16 * bo - n) by (subst res; rewrite HEE; subst P; clear; lia).
  assert (RES_eq : snd c + stride - 4 - (snd c + 16 * bo) - n = res) by (rewrite HRES; clear; lia).
  rewrite !RES_eq in K3, K5, Kr. clear RES_eq.
  clearbody res EE. subst B.
  assert (RES0 : 0 <= res < 2^31) by (clear -HRES Hfit FIT' Hoff Hn; lia).
  assert (EEH : EE + 4 <= alloc_ceiling) by (clear -HEE CS SIL SPAN RBC SI0; lia). pose_ceil.
  assert (HA0' : a0 = wz P). { rewrite HA0. subst P. rewrite (conc_region' st c r) by (rewrite CF; exact Hr). f_equal. clear. lia. }
  clear HA0.

  destruct (SH (fst bm) r Hr Hkd) as [WRr HB].
  assert (KB : forall o v, cell_read (get_shadow st (fst bm)) o = Known v -> 0 <= o < round_up_pg (r_len r) ->
               bytes_at rsegs m (r_base r + o) [b8 v] /\ 0 <= v < 256).
  { intros o v Ho Hor. exact (HB o v Hor Ho). }
  clear HB SH.
  unfold known, SHd in K4, K3, K2, K1, K5, Kr. cbn [fst snd] in K4, K3, K2, K1, K5, Kr. rewrite CF in K4, K3, K2, K1, K5, Kr.
  assert (PR : 12 <= snd c + 16 * bo - 4 /\ snd c + stride <= round_up_pg (r_len r)) by (clear -CS Hoff SI0 SIL SPAN Bm0; lia).
  assert (PR2 : 16 <= snd c) by (clear -CS Bm0 SI0; lia).
  destruct (KB _ _ K4 ltac:(clear -PR Hfit Hn; lia)) as [B4 _].
  destruct (KB _ _ K3 ltac:(clear -PR Hfit Hn; lia)) as [B3 V3].
  destruct (KB _ _ K2 ltac:(clear -PR Hfit Hn; lia)) as [B2 V2].
  destruct (KB _ _ K1 ltac:(clear -PR Hfit Hn; lia)) as [B1 V1].
  clear K4 K3 K2 K1.
  pose proof (u16_bytes q Q16) as QLH.
  pose proof (byte_of_range q 0) as Q0R. pose proof (byte_of_range q 1) as Q1R.
  set (q0 := byte_of q 0) in *. set (q1 := byte_of q 1) in *. clearbody q0 q1.

  destruct (rmrep_group_read st m bm _ MRP Hgh) as [RG _]. cbn [g_meta] in RG. unfold MallocRep_u.pw, oconc in RG.
  assert (MSL : meta_slot st mt) by (exists a, ar, ka; split; [exact Ha| split; [exact Hka| rewrite Emt; reflexivity]]).
  pose proof (rmrep_meta_chunk st m mt MRP MSL) as MM. fold mr in MM. unfold meta_cells in MM. rewrite Hmem in MM. unfold MallocRep_u.pw in MM. cbn [oconc] in MM.
  assert (Harea : s_areas st !! (area_of mt) = Some ar).
  { rewrite Emt, (area_of_mslot a ka); [exact Ha| | exact Hka].
    destruct (WA a ar Ha) as (ra & _ & _ & _ & AAL & _). exact AAL. }
  pose proof (rmrep_area_check_read st m (area_of mt) ar MRP Harea) as RA. rewrite Hck in RA. change (c_secret (s_ctx st)) with (c_secret (ctx st)) in RA.
  pose proof (rmrep_ctx_secret_read st m MRP) as RC.
  destruct (rmeta_addr_facts st m mt MRP MSL) as (GB0 & GB1 & HAR). change (hide (conc st (area_of mt) = conc st mt - conc st mt mod 4096)) in HAR.
  assert (CB : conc st bm = r_base r + snd bm) by (apply conc_region'; exact Hr).
  rewrite CB in MM, RG. clear CB MSL Harea Hck Ha Hka Emt WA WG WR ARS GR GL CX.

  rewrite HA0'. unfold RAA_RET.
  eapply (raa_tail_walk sp gp tp t0 t1 t2 (wz P) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m junk s1o s0o rao
            n P (conc st mt) (r_base r + snd bm) (conc st (area_of mt)) EE (P + n) stride res
            (i + 32 * Z.min res 5) q (m_avail mr) (m_freed mr) (m_last_idx mr) (m_freeable mr) (m_sizeclass mr) (m_maplen mr)
            (c_secret (ctx st)) (wz (oconc st (m_prev mr))) (wz (oconc st (m_next mr))));
    rewrite ?(land31_idx i (Z.min res 5)) by (clear -Hi LI RES0; lia).
  all: try exact FR. all: try exact CSP. all: try exact SPH. all: try exact RG. all: try exact RA. all: try exact RC. all: try exact HAR. all: try exact MM.
  all: try exact AV. all: try exact FRD. all: try exact SE. all: try exact NA. all: try exact NF. all: try exact V3. all: try exact EEH.
  - apply wz_unsigned. subst P. clear -RB0 PR EEH HEE Hfit Hn Hoff CEIL_RANGE__. lia.
  - subst P. clear -RB0 PR Bm0. lia.
  - exact PM16.
  -   subst P. clear -QE CS SI0 Bm0 RB0. lia.
  -   subst P. rewrite CS. clear -QE. lia.
  - clear -GB0. lia.
  - exact GB1.
  -   rewrite wz_unsigned by (subst P; clear -RB0 PR EEH HEE Hfit Hn Hoff CEIL_RANGE__; lia). apply rw_cells_mk.
    + cbn. repeat split; auto; clear; lia.
    + cbn [cells_bytes cbytes]. rewrite <- QLH. rewrite le2_lohi by assumption.
      apply (bytes_at_ext rsegs m _ ([b8 0] ++ [b8 (i + 32 * res `min` 5)] ++ [b8 q0] ++ [b8 q1])); [| reflexivity].
      apply (proj2 (bytes_at_app _ _ _ _ _)). split; [replace (P + -4) with (r_base r + (snd c + 16 * bo - 4)) by (subst P; clear; lia); exact B4|].
      apply (proj2 (bytes_at_app _ _ _ _ _)). split; [cbn [length Z.of_nat Pos.of_succ_nat]; replace (P + -4 + 1) with (r_base r + (snd c + 16 * bo - 3)) by (subst P; clear; lia); exact B3|].
      apply (proj2 (bytes_at_app _ _ _ _ _)). split; [cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; replace (P + -4 + 1 + 1) with (r_base r + (snd c + 16 * bo - 2)) by (subst P; clear; lia); exact B2|].
      cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]. replace (P + -4 + 1 + 1 + 1) with (r_base r + (snd c + 16 * bo - 1)) by (subst P; clear; lia). exact B1.
    + cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. eapply wr_at_sub; [exact WRr| subst P; clear -PR; lia| subst P; clear -PR Hfit Hn; lia].
  -   intros Hlt. apply rsize_classes_read; [exact MI| clear -Hlt GSC; lia].
  - clear -Q16; lia.
  - clear -LI Hi; lia.
  - rewrite FBL. clear; lia.
  - destruct GSC as [X|(X & ? & ?)]; clear -X; lia.
  - clear -ML; lia.
  - clear -Hi; lia.
  -   intros Hsc.
    destruct BSC as [(Hsc' & Hle & Hst)| E63]; [| exfalso; clear -Hsc E63; lia].
    pose proof (size_class_bound _ Hsc') as SB.
    assert (A16 : stride = 16 * size_class (m_sizeclass mr) \/ m_last_idx mr = 0) by tauto.
    assert (B16 : stride <= 16 * size_class (m_sizeclass mr) \/ 292 <= size_class (m_sizeclass mr)).
    { destruct Hle as [Hle|H28]; [left; exact Hle| right; apply size_class_28; clear -H28 Hsc'; lia]. }
    exact (guard16_arith _ _ _ _ _ _ _ (proj1 SB) QE Hfit Hn Hoff Hi A16 B16).
  -   intros Hsc. destruct GSC as [X|(X & Y & W)]; [exfalso; clear -X Hsc; lia|]. repeat split; clear -X Y W; lia.
  -   intros NM. destruct (BTOP NM) as [Bm00 GE].
    unfold gend, cnt_of, sstart in GE. rewrite GB, Bm00 in GE. fold stride in GE.
    assert (X : q <= m_maplen mr * 4096 / 16 - 1).
    { apply (guard17_arith stride i bo n q (m_last_idx mr) (m_maplen mr)); try assumption; clear -GE Hoff; lia. }
    replace (m_maplen mr * 4096 / 16) with (m_maplen mr * 256) in X; [exact X|].
    replace (m_maplen mr * 4096) with (m_maplen mr * 256 * 16) by (clear; lia). rewrite Z.div_mul by (clear; lia). reflexivity.
  -   subst stride. unfold get_stride. reflexivity.
  -   clear -CS HEE. lia.
  - reflexivity.
  -   rewrite HRES, HEE. subst P. clear. lia.
  - exact Hn.
  - exact RES0.
  -   rewrite HEE. subst P. clear -Hfit Hn Hoff. lia.
  - reflexivity.
  -   intros R0 R5. specialize (Kr R0). destruct (KB _ _ Kr ltac:(clear -PR Hfit Hn HRES R0 Hoff; lia)) as [BZ _].
    apply rw_cells_mk; [cbn; repeat split; auto; clear; lia| cbn [cells_bytes cbytes app]| cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat]].
    + replace (P + n) with (r_base r + (snd c + stride - 4 - res)) by (subst P; clear -HRES; lia). exact BZ.
    + eapply wr_at_sub; [exact WRr| subst P; clear -PR Hoff Hn RB0; lia| subst P; clear -PR Hfit Hn Hoff; lia].
  -   intros R5. destruct (K5 R5) as (E4 & E3 & E2 & E1 & E5 & R32).
    destruct (KB _ _ E4 ltac:(clear -PR PR2 S16; lia)) as [BE4 _]. destruct (KB _ _ E3 ltac:(clear -PR PR2 S16; lia)) as [BE3 _].
    destruct (KB _ _ E2 ltac:(clear -PR PR2 S16; lia)) as [BE2 _]. destruct (KB _ _ E1 ltac:(clear -PR PR2 S16; lia)) as [BE1 _].
    destruct (KB _ _ E5 ltac:(clear -PR PR2 S16; lia)) as [BE5 _].
    apply rw_cells_mk; [cbn; repeat split; auto; clear; lia| cbn [cells_bytes cbytes app]| cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]].
    + rewrite le4_byte_of by (clear -RES0 R32; lia).
      apply (bytes_at_ext rsegs m _ ([b8 0] ++ [b8 (byte_of res 0)] ++ [b8 (byte_of res 1)] ++ [b8 (byte_of res 2)] ++ [b8 (byte_of res 3)])); [| reflexivity].
      apply (proj2 (bytes_at_app _ _ _ _ _)). split; [replace (EE + -5) with (r_base r + (snd c + stride - 4 - 5)) by (rewrite HEE; clear; lia); exact BE5|].
      apply (proj2 (bytes_at_app _ _ _ _ _)). split; [cbn [length Z.of_nat Pos.of_succ_nat]; replace (EE + -5 + 1) with (r_base r + (snd c + stride - 4 - 4)) by (rewrite HEE; clear; lia); exact BE4|].
      apply (proj2 (bytes_at_app _ _ _ _ _)). split; [cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; replace (EE + -5 + 1 + 1) with (r_base r + (snd c + stride - 4 - 3)) by (rewrite HEE; clear; lia); exact BE3|].
      apply (proj2 (bytes_at_app _ _ _ _ _)). split; [cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; replace (EE + -5 + 1 + 1 + 1) with (r_base r + (snd c + stride - 4 - 2)) by (rewrite HEE; clear; lia); exact BE2|].
      cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]. replace (EE + -5 + 1 + 1 + 1 + 1) with (r_base r + (snd c + stride - 4 - 1)) by (rewrite HEE; clear; lia). exact BE1.
    + eapply wr_at_sub; [exact WRr| rewrite HEE; clear -PR PR2 S16 RB0; lia| rewrite HEE; clear -PR; lia].
  -   pose proof (bytes_at_overlay m _ _ B3 ltac:(cbn [length Z.of_nat Pos.of_succ_nat]; clear -DRr PR Hfit Hn; lia) 0%nat ltac:(cbn; clear; lia)) as X. cbn [nth_error] in X. rewrite Z.add_0_r in X.
    replace (P - 3) with (r_base r + (snd c + 16 * bo - 3)) by (subst P; clear; lia). exact X.
  -   intros R0. specialize (Kr R0). destruct (KB _ _ Kr ltac:(clear -PR Hfit Hn HRES R0 Hoff; lia)) as [BZ _].
    pose proof (bytes_at_overlay m _ _ BZ ltac:(cbn [length Z.of_nat Pos.of_succ_nat]; clear -DRr PR Hfit Hn HRES R0 Hoff; lia) 0%nat ltac:(cbn; clear; lia)) as X. cbn [nth_error] in X. rewrite Z.add_0_r in X.
    replace (EE - res) with (r_base r + (snd c + stride - 4 - res)) by (rewrite HEE; clear; lia). exact X.
  -   intros R5. destruct (K5 R5) as (_ & _ & _ & _ & E5 & _). destruct (KB _ _ E5 ltac:(clear -PR PR2 S16; lia)) as [BE5 _].
    pose proof (bytes_at_overlay m _ _ BE5 ltac:(cbn [length Z.of_nat Pos.of_succ_nat]; clear -DRr PR PR2 S16; lia) 0%nat ltac:(cbn; clear; lia)) as X. cbn [nth_error] in X. rewrite Z.add_0_r in X.
    replace (EE - 5) with (r_base r + (snd c + stride - 4 - 5)) by (rewrite HEE; clear; lia). exact X.
  -   intros R5 j Hj. destruct (K5 R5) as (E4 & E3 & E2 & E1 & E5 & R32).
    destruct (KB _ _ E4 ltac:(clear -PR PR2 S16; lia)) as [BE4 _]. destruct (KB _ _ E3 ltac:(clear -PR PR2 S16; lia)) as [BE3 _].
    destruct (KB _ _ E2 ltac:(clear -PR PR2 S16; lia)) as [BE2 _]. destruct (KB _ _ E1 ltac:(clear -PR PR2 S16; lia)) as [BE1 _].
    rewrite le4_byte_of by (clear -RES0 R32; lia).
    assert (BA : bytes_at rsegs m (EE - 4) ([b8 (byte_of res 0)] ++ [b8 (byte_of res 1)] ++ [b8 (byte_of res 2)] ++ [b8 (byte_of res 3)])).
    { apply (proj2 (bytes_at_app _ _ _ _ _)). split; [replace (EE - 4) with (r_base r + (snd c + stride - 4 - 4)) by (rewrite HEE; clear; lia); exact BE4|].
      apply (proj2 (bytes_at_app _ _ _ _ _)). split; [cbn [length Z.of_nat Pos.of_succ_nat]; replace (EE - 4 + 1) with (r_base r + (snd c + stride - 4 - 3)) by (rewrite HEE; clear; lia); exact BE3|].
      apply (proj2 (bytes_at_app _ _ _ _ _)). split; [cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; replace (EE - 4 + 1 + 1) with (r_base r + (snd c + stride - 4 - 2)) by (rewrite HEE; clear; lia); exact BE2|].
      cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]. replace (EE - 4 + 1 + 1 + 1) with (r_base r + (snd c + stride - 4 - 1)) by (rewrite HEE; clear; lia). exact BE1. }
    cbn [app] in BA. exact (bytes_at_overlay m _ _ BA ltac:(cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; clear -DRr PR PR2 S16 HEE; lia) j Hj).
Qed.

Definition RALIGNED_STACK : Z := RMALLOC_STACK + 32.

Definition raligned_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (n lo B : Z) (errv : word),
  RHEAP s LB m ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RALIGNED_STACK ->
  rw_cells rsegs m (errno_addr tp) [C4 errv] ->
  mem_inv rsegs m ->
  tp = Z_to_bv 64 RATP ->
  rw_cells rsegs m (RCTX + 928) [C4 (wz 0); C4 (wz 0)] ->
  a0 = Z_to_bv 64 16 -> a1 = Z_to_bv 64 n -> 0 <= n < 2^32 ->
  implM rsegs (raw_malloc n) s
        (rmalloc_post_fit ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RAA_SYM) fc None m (seg_rom rsegs)).

Lemma rmalloc_jstep : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m,
  mstep rsegs (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 RMALLOC_SYM) fc None m (seg_rom rsegs))
              (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 RMALLOC_IMPL) fc None m (seg_rom rsegs)).
Proof.
  intros. split; [reflexivity|]. unfold RMALLOC_SYM, RMALLOC_IMPL. cbn [ms_svc_pending].
  let fw := eval vm_compute in (fetch_word rsegs (Z_to_bv 64 692548)) in
  lazymatch fw with Some ?w =>
    let d := eval vm_compute in (decode_any w) in
    lazymatch d with Some (?i, ?sz) =>
      rewrite (step_gen rsegs _ F (Z_to_bv 64 692548) fc None m (seg_rom rsegs) w i sz) by vmc_refl;
      exec_pre i; exec_cbv; simp_is_x0; simp_regs; vnorm_for i
    end
  end.
  reflexivity.
Qed.

Lemma rw_cells_kept : forall m m' A cs,
  rw_cells rsegs m A cs ->
  (forall a, A <= a < A + Z.of_nat (cells_size cs) -> m' (wa a) = m (wa a) /\ (wview rsegs m (wa a) <> None -> wview rsegs m' (wa a) <> None)) ->
  rw_cells rsegs m' A cs.
Proof.
  intros m m' A cs [[Hwf (H0 & H1 & HB)] (W0 & W1 & HW)] K.
  pose proof (cells_bytes_length cs Hwf) as LEN.
  split; [split; [exact Hwf|]|].
  - split; [exact H0|]. split; [exact H1|].
    intros i Hi. unfold mrd. rewrite (proj1 (K (A + Z.of_nat i) ltac:(rewrite LEN in Hi; lia))).
    apply HB. exact Hi.
  - split; [exact W0|]. split; [exact W1|]. intros i Hi. apply (proj2 (K (A + i) ltac:(lia))). apply HW. exact Hi.
Qed.

Lemma ret_pc_RAA_RET : ret_pc (wz RAA_RET) = Z_to_bv 64 RAA_RET.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Theorem raligned_spec : raligned_stmt.
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB n lo B errv.
  intros HEAP AUXB SB ST CLO LO ERR MI TP REPL HA0 HA1 N.
  unfold RALIGNED_STACK, RMALLOC_STACK in LO. pose proof CLO as CLOv. pose_ceil.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (ETP : bv_unsigned tp + -164 = RERRNO) by (rewrite TP; unfold RATP, RERRNO; rewrite unsigned_lit by lia; reflexivity).
  rewrite ETP in ERR.

  eapply implM_evt.
  { eapply (raa_pre_walk ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo n);
      [exact ST| exact CLO| lia| exact MI| exact REPL| exact HA0| exact HA1| lia]. }
  cbv beta. intros ms1 (junk & m1 & -> & MU & WM & MI1 & FR).

  assert (OUTW : forall a, 0 <= a < bv_unsigned sp + -32 -> m1 (wa a) = m (wa a)).
  { intros a Ha. apply MU. cbn. split; [| exact I]. rewrite wa_unsigned by lia. lia. }
  assert (HEAP1 : RHEAP s LB m1).
  { eapply RHEAP_frame_proof; [exact HEAP| exact MU| exact WM|]. constructor; [| constructor]. left. cbn [fst]. lia. }
  assert (AUX1 : rauxv_ok m1 B).
  { eapply rauxv_ok_frame; [exact AUXB| exact MU| exact WM|]. constructor; [| constructor]. cbn [fst snd]. unfold RAUXV_CELL. lia. }
  assert (ST1 : stk rsegs m1 lo (bv_unsigned (wz (bv_unsigned sp + -32)))).
  { rewrite wz_unsigned by lia. destruct (stk_split rsegs m lo (bv_unsigned sp + -32) (bv_unsigned sp) ST ltac:(lia)) as [ST0 _].
    eapply stk_transport_disjoint; [exact ST0| exact MU| exact WM|]. cbn. lia. }
  assert (ERR1 : rw_cells rsegs m1 (bv_unsigned tp + -164) [C4 errv]).
  { rewrite ETP. eapply rw_cells_transport; [exact ERR| exact MU| exact WM|]. cbn. unfold RERRNO. lia. }

  pose proof (rmalloc_spec_fit (wz RAA_RET) (wz (bv_unsigned sp + -32)) gp tp t0 t1 t2 (wz 16) (wz n) (wz n) (wz n) (wz 16) a3 a4 a5 a6 a7
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 s LB n lo B errv
                HEAP1 AUX1 ltac:(rewrite wz_unsigned by lia; lia) ST1 CLO ltac:(rewrite wz_unsigned by lia; unfold RMALLOC_STACK; lia) ERR1 MI1 TP eq_refl N) as IMPL.
  pose proof (fun HQ HN => implM_after_step _ _ _ _ _ IMPL
                 (rmalloc_jstep (wz RAA_RET) (wz (bv_unsigned sp + -32)) gp tp t0 t1 t2 (wz 16) (wz n) (wz n) (wz n) (wz 16) a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1) HQ HN) as IMPL2.

  eapply implM_post_evt.
  { apply IMPL2.
    - intros r s' [POST _]. exfalso.
      destruct POST as (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & u14 & m' & errv' & E & _).
      apply (f_equal ms_pc) in E. cbn [ms_pc MS] in E. rewrite ret_pc_RAA_RET in E.
      apply (f_equal bv_unsigned) in E. unfold RMALLOC_SYM, RAA_RET in E. rewrite !unsigned_lit in E by lia. lia.
    - intros nd. apply at_node_svc_none. }
  cbv beta. intros r s' ms' [POST FITr].
  destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & errv' & -> &
                    MI' & ST' & ERR' & AUX' & HPRES & HDEEP & HIMG & PSF & PSO & RR).
  rewrite ret_pc_RAA_RET. rewrite wz_unsigned in ST', HPRES by lia.
  assert (FR' : rw_cells rsegs m' (bv_unsigned sp + -32) [CB 8 junk; C8 s1; C8 s0; C8 ra]).
  { eapply rw_cells_kept; [exact FR|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. intros a Ha. apply HPRES; [lia| left; lia]. }

  assert (POSTC : forall mf, mf = m' ->
      mem_inv rsegs mf /\ stk rsegs mf lo (bv_unsigned sp) /\ rw_cells rsegs mf (bv_unsigned tp + -164) [C4 errv'] /\ rauxv_ok mf B
      /\ rheap_pres LB (bv_unsigned sp) m mf /\ rdeep_pres lo m mf /\ rimg_pres m mf).
  { intros mf ->. split; [exact MI'|]. split.
    { replace (bv_unsigned sp) with (bv_unsigned sp + -32 + Z.of_nat (cells_size [CB 8 junk; C8 s1; C8 s0; C8 ra])) by (cbn; lia).
      apply stk_release; [exact ST'| exact FR'| lia]. }
    split; [exact ERR'|]. split; [exact AUX'|]. split.
    { intros a Ha HC. destruct (HPRES a Ha) as [E W].
      { destruct HC as [HC|[HC|HC]]; [left; lia| right; left; exact HC| right; right; exact HC]. }
      assert (NW : a < bv_unsigned sp + -32 \/ bv_unsigned sp <= a).
      { destruct HC as [HC|[[HC _]|(b & Hb & Hin)]]; [right; exact HC| left; lia| left].
        pose proof (RHEAP_block_range_proof s LB m b HEAP Hb) as (_ & _ & _ & X & _). pose_ceil. lia. }
      assert (E1 : m1 (wa a) = m (wa a)).
      { destruct NW as [NW|NW]; [apply OUTW; lia|]. apply MU. cbn. rewrite wa_unsigned by lia. lia. }
      split; [rewrite E; exact E1|]. intros Wv. apply W. apply WM. exact Wv. }
    split.
    { intros a Ha. rewrite (HDEEP a Ha). apply OUTW. pose_ceil. lia. }
    intros a Ha N1 N2. rewrite (HIMG a Ha N1 N2). apply OUTW. lia. }
  destruct r as [p|].
  -
    destruct RR as (A & ujunk & EA0 & RBR & HR' & UCH & EXPO). cbn [fst] in FITr.
    pose proof HR' as (st' & LB0' & PERM & Hst' & MR' & [BL' AR']).
    assert (Hin0 : In (p, A, n) LB0') by (eapply Permutation_in; [apply Permutation_sym; exact PERM| left; reflexivity]).
    destruct (areach_inv _ st' LB0' AR') as (L & LS & BL & INV & LIVE & RESV & SEC & CR).
    destruct (Forall2_In_l _ _ _ _ CR Hin0) as (k & Hk & (C1 & C2 & C3)).
    destruct k as [[c bo] n']. cbn [blk_slot blk_size blk_addr bslot bsize boff fst snd] in C1, C2, C3. subst n'.
    pose proof (areach_cinv_proof st' LB0' AR') as CI.
    assert (FIT' : forall g i, s_slots st' !! c = Some (g, i) -> get_stride (get_meta_rec st' g) - IB - n < 2^31).
    { intros g i Hs. rewrite <- (get_meta_rec_strip st'), Hst'. apply (FITr g i). rewrite <- Hst'. rewrite s_slots_strip. change (blk_slot (p, A, n)) with (fst p) in C1. rewrite C1. exact Hs. }
    eapply evt_mono.
    { eapply (raa_tail_spec (wz (bv_unsigned sp + -32)) gp tp t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6' a0'
                F fc m' junk s1 s0 ra st' L BL LS LB0' c bo n MR' MI' CI INV Hk FIT');
        rewrite ?wz_unsigned by lia; [exact FR'| exact CLO+ltac:(lia) | lia| rewrite EA0, C3; reflexivity]. }
    cbv beta. intros msf (v0 & v1 & v2 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w3' & w4' & w5' & w6' & ->).
    split; [| exact FITr]. unfold rmalloc_post.
    exists v0, v1, v2, a0', w1, w2, w3, w4, w5, w6, w7, w3', w4', w5', w6', m', errv'.
    split. { rewrite wz_unsigned by lia. replace (bv_unsigned sp + -32 + 32) with (bv_unsigned sp) by lia. unfold wz. rewrite Z_to_bv_bv_unsigned. reflexivity. }
    destruct (POSTC m' eq_refl) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7).
    split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|]. split; [exact Q5|]. split; [exact Q6|]. split; [exact Q7|].
    split; [exact PSF|]. split; [exact PSO|].
    exists A, ujunk. split; [exact EA0|]. split; [exact RBR|]. split; [exact HR'|]. split; [exact UCH| exact EXPO].
  -
    destruct RR as [EA0 HR'].
    eapply evt_mono.
    { rewrite EA0. unfold RAA_RET. rewrite <- (wz_unsigned (bv_unsigned sp + -32)) in FR' by lia.
      exact (raa_null_walk (wz (bv_unsigned sp + -32)) gp tp t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6' F fc m' junk s1 s0 ra n FR'). }
    cbv beta. intros msf ->.
    split; [| exact I]. unfold rmalloc_post.
    exists t0', t1', t2', (wz 0), a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m', errv'.
    split. { rewrite wz_unsigned by lia. replace (bv_unsigned sp + -32 + 32) with (bv_unsigned sp) by lia. unfold wz at 1. rewrite Z_to_bv_bv_unsigned. reflexivity. }
    destruct (POSTC m' eq_refl) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7).
    split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|]. split; [exact Q5|]. split; [exact Q6|]. split; [exact Q7|].
    split; [exact PSF|]. split; [exact PSO|]. split; [reflexivity| exact HR'].
Qed.
End CEIL_WRAP_1.

