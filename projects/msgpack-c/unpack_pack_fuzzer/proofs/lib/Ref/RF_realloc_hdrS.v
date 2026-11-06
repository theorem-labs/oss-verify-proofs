(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes Decode.
From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require Import A_F_malloc_free A_F_malloc_fast A_MallocKit_AB A_MallocKit_A A_MallocBlocks A_MallocHINV A_MallocFacts_B A_Malloc_iface.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc Require Import STree Malloc MallocCtrl MallocInv MI_Arith MI_Inv MI_Read MI_Geom MI_Pres2 MI_WFree.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require Import Monad Prog.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ref Require Import RMallocRep RMallocTree RMallocKit_B RMalloc_iface RMalloc_ifaceP RF_get_meta RF_malloc_top RMemEq.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ref Require Import RF_aligned16_W RF_aligned16 RF_realloc_hdr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require A_MallocFacts_inv A_MallocFacts_inv2 A_MallocFacts_inv3.

Set Keyed Unification.
Import ListNotations.
Import ITree.Exc.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import CeilLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Lemma hdr_spec :
  forall (ra1 sp gp tp t0 t1 y7 s0 s1 y12 y13 y14 y15 y16 y17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (st : mstate) (LB0 : list block) (bp : bptr) (old A n : Z),
  rmrep st m -> mem_inv rsegs m -> AREACH_from ref_reserved st LB0 -> In (bp, A, old) LB0 -> 0 <= n < 2^48 ->
  exists (g bg : aptr) (idx : Z) (r : region),
    s_slots st !! (fst bp) = Some (g, idx) /\ m_mem (get_meta_rec st g) = Some bg /\ s_regions st !! (fst bg) = Some r /\ r_kind r = RKGroup
    /\ fst (fst bp) = fst bg /\ conc st (fst bp) = conc st bg + 16 + get_stride (get_meta_rec st g) * idx
    /\ conc st bg = r_base r + snd bg /\ 0 <= old /\ A + old <= conc st (fst bp) + get_stride (get_meta_rec st g) - IB
    /\ conc st (fst bp) + get_stride (get_meta_rec st g) <= r_base r + round_up_pg (r_len r) /\ r_base r + round_up_pg (r_len r) <= alloc_ceiling
    /\ 0 <= m_sizeclass (get_meta_rec st g) < 64 /\ (48 <= m_sizeclass (get_meta_rec st g) -> m_sizeclass (get_meta_rec st g) = 63)
    /\ evt rsegs (hdr_post ra1 sp gp tp s0 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 F fc m A n old (conc st g) (conc st bg) (get_stride (get_meta_rec st g)) idx
                    (m_last_idx (get_meta_rec st g)) (m_freeable (get_meta_rec st g)) (m_sizeclass (get_meta_rec st g)) (m_maplen (get_meta_rec st g)))
      (MS (mkR ra1 sp gp tp t0 t1 y7 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 n) y12 y13 y14 y15 y16 y17
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 t5 t6)
          F (Z_to_bv 64 0x49a68) fc None m (seg_rom rsegs)).
Proof.
  intros until n. intros RMR MI AR Hb HN.
  pose proof RMR as (WF & CX & GL & ARS & GR & SH). pose proof WF as (Hres & WR & DISJ & WA & WG).
  destruct (A_MallocFacts_inv.areach_inv _ _ _ AR) as (L & LS & BL & INV & _ & _ & _ & CR).
  pose proof (A_MallocFacts_inv3.areach_cinv_proof _ _ AR) as C.
  destruct (A_MallocFacts_inv.Forall2_In_l _ _ _ _ CR Hb) as (k & Hk & (C1 & C2 & C3)).
  destruct k as [[c off] n']. cbn [bslot boff bsize blk_slot blk_size blk_addr fst snd] in C1, C2, C3. subst n'.
  assert (C1' : fst bp = c) by exact C1.
  destruct (block_facts x0 st L BL LS INV c off old Hk) as (mm & bm & i & ai & a & ar & ka & BF).
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  pose proof (bf_slot _ _ _ _ _ _ _ _ _ _ _ BF) as SL. pose proof (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF) as HG.
  pose proof (bf_mem _ _ _ _ _ _ _ _ _ _ _ BF) as HM. pose proof (bf_c _ _ _ _ _ _ _ _ _ _ _ BF) as EC.
  pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF) as Hi. pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF) as Hoff.
  pose proof (bf_n _ _ _ _ _ _ _ _ _ _ _ BF) as Ho. pose proof (bf_fit _ _ _ _ _ _ _ _ _ _ _ BF) as FIT.
  pose proof (bf_stride _ _ _ _ _ _ _ _ _ _ _ BF) as [S1 S2]. pose proof (bf_b16 _ _ _ _ _ _ _ _ _ _ _ BF) as [Bb0 Bb16].
  pose proof (bf_notA _ _ _ _ _ _ _ _ _ _ _ BF) as NA. pose proof (bf_notF _ _ _ _ _ _ _ _ _ _ _ BF) as NF. unfold tbit in NA, NF.
  pose proof (bf_top _ _ _ _ _ _ _ _ _ _ _ BF) as TOP. pose proof (bf_hdr0 _ _ _ _ _ _ _ _ _ _ _ BF) as H0E.
  destruct (bf_area _ _ _ _ _ _ _ _ _ _ _ BF) as (Ha & Hck & Hal & Hka & Emm).
  pose proof (q16 _ _ _ _ _ _ _ _ _ _ _ BF) as [Q1 Q2]. pose proof (p_mod16 _ _ _ _ _ _ _ _ _ _ _ BF) as PM16.
  pose proof (bf_shadow _ _ _ _ _ _ _ _ _ _ _ BF) as SHB. unfold blk_shadow_ok in SHB. cbn [bslot boff bsize fst snd] in SHB.
  rewrite (gbase_bm _ _ _ _ _ _ _ _ _ _ _ BF) in SHB.
  cbn [aadd snd] in Q1, Q2, PM16.
  set (q := (snd c + UNIT * off - snd bm - UNIT) / UNIT) in *.
  destruct SHB as (K4 & K3 & K2 & K1 & _ & K5 & Kr & KU).
  set (mr := MI_Inv.MR st mm) in *.
  set (stride := get_stride mr) in *.
  set (po := snd c + UNIT * off) in *.
  set (e := snd c + stride - IB) in *.
  set (res := e - po - old) in *.
  pose proof (ig_ok _ _ _ IG _ _ _ HG) as GOK.
  destruct (ig_region _ _ _ IG _ _ HG) as (r & Hr & Kr').
  pose proof (proj1 (List.Forall_forall _ _) (ci_blks _ _ C) _ Hb) as BK.
  destruct BK as [(g & i' & b0 & SL' & HB' & FB' & I' & NFR & _) NG SZ]. cbn [blk_slot blk_size fst snd] in SL', NG, SZ, FB'.
  rewrite ?C1, ?C1', SL in SL'. assert (g = mm /\ i' = i) as [-> ->] by (split; congruence). clear SL'.
  pose proof (ci_gmetas _ _ C b0 mm HB') as GO.
  assert (Eb0 : b0 = bm) by (pose proof (go_mem _ _ _ GO) as X; change (get_meta_rec st mm) with mr in X; rewrite HM in X; congruence). subst b0.
  destruct (go_region _ _ _ GO) as (r' & Hr' & _ & _ & _ & SPAN & _). rewrite Hr in Hr'. assert (r' = r) as -> by congruence.
  pose proof (go_avail _ _ _ GO) as AV. pose proof (go_freed _ _ _ GO) as FRD. pose proof (go_li _ _ _ GO) as LI.
  pose proof (go_freeable _ _ _ GO) as FB1. pose proof (go_maplen _ _ _ GO) as ML. pose proof (go_sc _ _ _ GO) as GSC.
  change (get_meta_rec st mm) with mr in AV, FRD, LI, FB1, ML, GSC, SPAN.
  pose proof (proj2 (proj2 (proj2 (proj2 (ci_cx _ _ C))))) as SE.
  unfold sstart_of in SPAN. rewrite HM in SPAN. cbn [default id snd] in SPAN. fold stride in SPAN.
  destruct (WR _ _ Hr) as (RrB0 & RBAL & RL0 & RBC & RF). pose_ceil.
  destruct (SH _ _ Hr Kr') as [WRr RDr].
  assert (FC : fst c = fst bm) by (rewrite EC; reflexivity).
  assert (SC' : snd c = snd bm + 16 + stride * i) by (rewrite EC; unfold sstart; rewrite (gbase_bm _ _ _ _ _ _ _ _ _ _ _ BF); reflexivity).
  assert (CC : conc st c = r_base r + snd c) by (apply conc_region'; rewrite FC; exact Hr).
  assert (CB : conc st bm = r_base r + snd bm) by (apply conc_region'; exact Hr).
  assert (SI0 : 0 <= stride * i) by (apply Z.mul_nonneg_nonneg; unfold UNIT in S1; lia).
  assert (SIL : stride * (i + 1) <= stride * (m_last_idx mr + 1)) by (apply Z.mul_le_mono_nonneg_l; unfold UNIT in S1; lia).
  assert (EHI' : e + IB <= round_up_pg (r_len r)).
  { clear - SC' SIL SPAN S1. subst e. rewrite SC'. unfold UNIT, IB in *. lia. }
  assert (HA : A = r_base r + po) by (subst po; rewrite C3, CC; unfold UNIT; clear; lia).
  assert (HE : e = snd bm + 16 + stride * i + stride - IB) by (subst e; rewrite SC'; clear; lia).
  assert (HPO : po = snd bm + 16 + 16 * q) by (subst po; rewrite SC'; clear - Q1; unfold UNIT in *; lia).
  assert (RESE : res = r_base r + e - A - old) by (subst res; rewrite HA; clear; lia).
  assert (AL : A mod 16 = 0) by (rewrite HA; clear - PM16 RBAL; Z.div_mod_to_equations; lia).
  assert (FIT' : po + old <= e) by (subst po e; unfold UNIT, IB in *; clear - FIT; lia).
  assert (PO16 : 16 <= po) by (rewrite HPO; clear - Bb0 Q2; lia).
  assert (RES0 : 0 <= res) by (subst res; clear - FIT'; lia).
  pose proof (round_up_pg_ge (r_len r)) as RUP.
  pose proof (rreserved_disjoint1 _ _ RF ltac:(clear - EHI' FIT' PO16 Ho; unfold IB in EHI'; lia)) as DRr.
  clearbody q po e res. clear PM16 Bb16 S2.
  assert (MSL : meta_slot st mm) by (exists a, ar, ka; split; [exact Ha|]; split; [exact Hka| exact Emm]).
  pose proof (rmeta_slot_bounds st m mm RMR MSL) as (GB0 & GB1 & _ & _ & _).
  destruct (WA a ar Ha) as (rg & Hrg & A0 & A1 & AAL & ANG & _).
  assert (HGc : conc st mm = r_base rg + snd a + (AREA_HDR + META_SIZE * ka)).
  { rewrite Emm. unfold mslot. rewrite conc_aadd by (rewrite Hrg; eauto). rewrite (conc_region' st a rg Hrg). reflexivity. }
  destruct (WR (fst a) rg Hrg) as (RgB0 & RgBAL & _ & RgBC & _). pose_ceil.
  assert (HAR : conc st (area_of mm) = conc st mm - conc st mm mod 4096).
  { rewrite Emm, (area_of_mslot a ka Hal Hka). rewrite <- Emm. rewrite HGc, (conc_region' st a rg Hrg).
    unfold AREA_HDR, META_SIZE, NSLOTS, PGSZ in *. clear - Hka Hal RgBAL A0.
    replace (r_base rg + snd a + (24 + 40 * ka)) with ((24 + 40 * ka) + (snd a / 4096 + r_base rg / 4096) * 4096) by (Z.div_mod_to_equations; nia).
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. Z.div_mod_to_equations; nia. }

  assert (RD : forall o v, cell_read (get_shadow st (fst c)) o = Known v -> 0 <= o < round_up_pg (r_len r) ->
            ov_read_bytes rsegs m (wa (r_base r + o)) 1 = Some [b8 v] /\ 0 <= v < 256).
  { intros o v Hoq Hor. rewrite FC in Hoq. exact (rmrep_shadow_read st m (fst bm) r o v RMR Hr Kr' Hor Hoq). }
  destruct (RD (po - 4) 0 K4 ltac:(clear - PO16 FIT' EHI' Ho; unfold IB in *; lia)) as [R4 _].
  destruct (RD (po - 3) _ K3 ltac:(clear - PO16 FIT' EHI' Ho; unfold IB in *; lia)) as [R3 B3R].
  assert (K2' : cell_read (get_shadow st (fst bm)) (po - 2) = Known (byte_of q 0)) by (rewrite <- FC; exact K2).
  assert (K1' : cell_read (get_shadow st (fst bm)) (po - 2 + 1) = Known (byte_of q 1)) by (rewrite <- FC; replace (po - 2 + 1) with (po - 1) by (clear; lia); exact K1).
  destruct (rmrep_shadow_read2 st m (fst bm) r (po - 2) _ _ RMR Hr Kr' ltac:(clear - PO16; lia) ltac:(clear - PO16 FIT' EHI' Ho; unfold IB in *; lia) K2' K1') as (R2 & LO8 & HI8).
  rewrite <- le2_lohi, (u16_bytes q Q2) in R2 by assumption.
  replace (r_base r + (po - 4)) with (A - 4) in R4 by (clear - HA; lia).
  replace (r_base r + (po - 3)) with (A - 3) in R3 by (clear - HA; lia).
  replace (r_base r + (po - 2)) with (A - 2) in R2 by (clear - HA; lia).
  destruct (rmrep_group_read st m bm _ RMR HG) as [RG _]. cbn [g_meta pw oconc] in RG.
  pose proof (rmrep_meta_chunk st m mm RMR MSL) as MM. change (get_meta_rec st mm) with mr in MM. unfold meta_cells in MM. rewrite HM in MM. cbn [pw oconc] in MM. change (pw st (Some bm)) with (wz (conc st bm)) in MM. unfold meta_word in MM.
  pose proof (rmrep_area_check_read st m a ar RMR Ha) as RA. rewrite Hck in RA. change (c_secret (s_ctx st)) with (c_secret (ctx st)) in RA.
  replace (conc st a) with (conc st mm - conc st mm mod 4096) in RA by (rewrite <- HAR, Emm, (area_of_mslot a ka Hal Hka); reflexivity).
  pose proof (rmrep_ctx_secret_read st m RMR) as RC.

  assert (RE0 : ov_read_bytes rsegs m (wa (r_base r + e)) 1 = Some [b8 0]).
  { apply (RD e 0); [| clear - PO16 FIT' EHI' Ho; unfold IB in *; lia].
    unfold known, SHd in H0E. cbn [fst snd] in H0E. rewrite <- FC in H0E. rewrite sstart_succ in H0E. fold mr stride in H0E.
    replace e with (sstart mr i + stride - IB); [exact H0E|]. rewrite HE. unfold sstart. fold mr. rewrite (gbase_bm _ _ _ _ _ _ _ _ _ _ _ BF). fold stride. unfold UNIT. clear; lia. }
  assert (RB0 : 0 < res -> ov_read_bytes rsegs m (wa (r_base r + e - res)) 1 = Some [b8 0]).
  { intros Hr0. replace (r_base r + e - res) with (r_base r + (e - res)) by (clear; lia). apply (RD (e - res) 0 (Kr Hr0)). clear - PO16 FIT' EHI' Ho Hr0 RES0 RESE HA; unfold IB in *; lia. }
  assert (RB5 : 5 <= res -> ov_read_bytes rsegs m (wa (r_base r + e - 5)) 1 = Some [b8 0] /\ ov_read_bytes rsegs m (wa (r_base r + e - 4)) 4 = Some (le4 (wz res))).
  { intros Hr5. destruct (K5 Hr5) as (E0 & E1 & E2 & E3 & E5 & R32). split.
    - replace (r_base r + e - 5) with (r_base r + (e - 5)) by (clear; lia). apply (RD (e - 5) 0 E5). clear - PO16 FIT' EHI' Ho Hr5; unfold IB in *; lia.
    - rewrite le4_bytes by (clear - RES0 R32; lia).
      rewrite <- (byte_of_0 res), <- (byte_of_1 res), <- (byte_of_2 res) by (clear - RES0; lia).
      replace (res / 16777216) with (byte_of res 3) by (rewrite byte_of_3 by (clear - RES0; lia); apply Z.mod_small; clear - RES0 R32; Z.div_mod_to_equations; lia).
      replace (wa (r_base r + e - 4)) with (wa (r_base r + (e - 4) + Z.of_nat 0)) by (unfold wa; f_equal; clear; lia).
      apply (bytes_at_ov_read rsegs m (r_base r + (e - 4)) [b8 (byte_of res 0); b8 (byte_of res 1); b8 (byte_of res 2); b8 (byte_of res 3)] 0 4); [| cbn; lia].
      apply bytes_at_4.
      + exact (proj1 (RDr (e - 4) _ ltac:(clear - PO16 FIT' EHI' Ho Hr5; unfold IB in *; lia) ltac:(rewrite <- FC; exact E0))).
      + replace (r_base r + (e - 4) + 1) with (r_base r + (e - 3)) by (clear; lia). exact (proj1 (RDr (e - 3) _ ltac:(clear - PO16 FIT' EHI' Ho Hr5; unfold IB in *; lia) ltac:(rewrite <- FC; exact E1))).
      + replace (r_base r + (e - 4) + 2) with (r_base r + (e - 2)) by (clear; lia). exact (proj1 (RDr (e - 2) _ ltac:(clear - PO16 FIT' EHI' Ho Hr5; unfold IB in *; lia) ltac:(rewrite <- FC; exact E2))).
      + replace (r_base r + (e - 4) + 3) with (r_base r + (e - 1)) by (clear; lia). exact (proj1 (RDr (e - 1) _ ltac:(clear - PO16 FIT' EHI' Ho Hr5; unfold IB in *; lia) ltac:(rewrite <- FC; exact E3))). }
  assert (RES32 : res < 2 ^ 32).
  { destruct (Z.lt_ge_cases res 5) as [LT|GE]; [clear - LT; lia|]. destruct (K5 GE) as (_ & _ & _ & _ & _ & R32). exact R32. }
  pose proof (bf_sc _ _ _ _ _ _ _ _ _ _ _ BF) as BSC. fold mr in BSC. fold stride in BSC.

  exists mm, bm, i, r. rewrite C1'. change (get_meta_rec st mm) with mr. fold stride.
  split; [exact SL|]. split; [exact HM|]. split; [exact Hr|]. split; [exact Kr'|]. split; [exact FC|].
  split; [rewrite CC, CB, SC'; clear; lia|]. split; [exact CB|]. split; [exact Ho|].
  split; [rewrite CC; fold stride; clear - HA FIT' HE SC'; unfold IB in *; lia|].
  split; [rewrite CC; fold stride; clear - EHI' HE SC'; unfold IB in *; lia|]. split; [clear - RBC; pose_ceil; lia|].
  split; [clear - GSC; lia|]. split; [clear - GSC; lia|].
  apply (hdr_428 ra1 sp gp tp t0 t1 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 F fc m
           A n old (conc st mm) (conc st bm) (conc st mm - conc st mm mod 4096) stride i res q
           (m_avail mr) (m_freed mr) (m_last_idx mr) (m_freeable mr) (m_sizeclass mr) (m_maplen mr) (c_secret (ctx st))
           (pw st (m_prev mr)) (pw st (m_next mr))).
  - exact Ho.
  - clear - HA RrB0 PO16. lia.
  - exact AL.
  - clear - HA HPO Bb0 RrB0. lia.
  - clear - HA FIT' EHI' RBC Ho RUP. unfold IB in *. lia.
  - clear - CB HA HPO. lia.
  - reflexivity.
  - clear - GB0. lia.
  - clear - GB1. lia.
  - exact R4.
  - exact R3.
  - exact R2.
  - exact RG.
  - exact MM.
  - exact RA.
  - exact RC.
  - intros Hlt. apply rsize_classes_read; [exact MI| clear - Hlt GSC; lia].
  - clear - Hi LI. lia.
  - exact Q2.
  - exact AV.
  - exact FRD.
  - exact SE.
  - clear - LI. lia.
  - rewrite FB1. clear. lia.
  - clear - GSC. lia.
  - clear - ML. lia.
  - clear - Hi. lia.
  - exact NA.
  - exact NF.
  - intros Hlt. destruct BSC as [(Hsc & Hle & Hst)| E63]; [| clear - Hlt E63; lia].
    pose proof (size_class_bound _ Hsc) as SB.
    assert (A' : stride = 16 * size_class (m_sizeclass mr) \/ m_last_idx mr = 0) by (clear - Hst; unfold UNIT in Hst; tauto).
    assert (B' : stride <= 16 * size_class (m_sizeclass mr) \/ 292 <= size_class (m_sizeclass mr)).
    { destruct Hle as [Hle|H28]; [left; unfold UNIT in Hle; exact Hle| right; apply size_class_28; clear - H28 Hsc; lia]. }
    clear - SB Q1 FIT Ho Hoff Hi A' B'. unfold UNIT, IB in *.
    exact (guard16_arith _ _ _ _ _ _ _ (proj1 SB) Q1 FIT Ho Hoff Hi A' B').
  - clear - GSC. lia.
  - intros NM. destruct (TOP NM) as [B0 GE]. unfold gend, cnt_of, sstart in GE. rewrite (gbase_bm _ _ _ _ _ _ _ _ _ _ _ BF), B0 in GE.
    fold mr in GE. fold stride in GE.
    replace (m_maplen mr * 256) with (m_maplen mr * 4096 / 16) by (rewrite <- (Z.div_mul (m_maplen mr * 256) 16) by lia; f_equal; lia).
    clear - S1 Q1 FIT Ho Hoff Hi GE. unfold UNIT, IB in *.
    eapply (guard17_arith stride i off old q); try eassumption; lia.
  - intros Hd. destruct GSC as [Hsc|(E63 & L0 & MLn)]; [| exfalso; clear - Hd L0 MLn; lia].
    split; [clear - Hsc; lia|]. subst stride. unfold get_stride.
    destruct Hd as [Hd|Hd]; [rewrite (proj2 (Z.eqb_eq _ _) Hd), andb_false_r; reflexivity| rewrite (proj2 (Z.eqb_neq _ _) Hd); reflexivity].
  - intros [L0 MLn]. subst stride. unfold get_stride. rewrite (proj2 (Z.eqb_eq _ _) L0). replace (m_maplen mr =? 0) with false by (symmetry; apply Z.eqb_neq; exact MLn). reflexivity.
  - clear - RES0 RES32. lia.
  - clear - RESE HE CB. unfold IB in *. lia.
  - clear - DRr EHI' HA PO16 HE CB FIT' Ho. unfold IB in *. lia.
  - clear - EHI' HE CB RBC RUP. unfold IB in *. lia.
  - intros H. replace (conc st bm + 16 + stride * (i + 1) - 4 - res) with (r_base r + e - res) by (clear - HE CB; unfold IB in *; lia). exact (RB0 H).
  - intros H. replace (conc st bm + 16 + stride * (i + 1) - 4 - 5) with (r_base r + e - 5) by (clear - HE CB; unfold IB in *; lia).
    replace (conc st bm + 16 + stride * (i + 1) - 4 - 4) with (r_base r + e - 4) by (clear - HE CB; unfold IB in *; lia). exact (RB5 H).
  - replace (conc st bm + 16 + stride * (i + 1) - 4) with (r_base r + e) by (clear - HE CB; unfold IB in *; lia). exact RE0.
Qed.

End CEIL.

From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Import Ubsan.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Tac OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Image OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Arr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Decode.
Import OSSVerify.msgpack_c.unpack_pack_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_F_malloc_free OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_F_malloc_fast OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocKit_AB OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocKit_A OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocBlocks OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocHINV OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocFacts_B OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_Malloc_iface.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Malloc OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MallocCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MallocInv OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MI_Arith OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MI_Inv OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MI_Read OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MI_Geom OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MI_Pres2 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MI_WFree.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.Monad OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.Prog.
Import RMallocRep.TwinB RMallocTree.TwinB RMallocKit_B.TwinB RMalloc_iface.TwinB RMalloc_ifaceP.TwinB RF_get_meta.TwinB RF_malloc_top.TwinB RMemEq.TwinB.
Import RF_aligned16_W.TwinB RF_aligned16.TwinB RF_realloc_hdr.TwinB.

Set Keyed Unification.
Import ListNotations.
Import ITree.Exc.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.CeilLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Lemma hdr_spec :
  forall (ra1 sp gp tp t0 t1 y7 s0 s1 y12 y13 y14 y15 y16 y17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (st : mstate) (LB0 : list block) (bp : bptr) (old A n : Z),
  rmrep st m -> mem_inv rsegs m -> AREACH_from ref_reserved st LB0 -> In (bp, A, old) LB0 -> 0 <= n < 2^48 ->
  exists (g bg : aptr) (idx : Z) (r : region),
    s_slots st !! (fst bp) = Some (g, idx) /\ m_mem (get_meta_rec st g) = Some bg /\ s_regions st !! (fst bg) = Some r /\ r_kind r = RKGroup
    /\ fst (fst bp) = fst bg /\ conc st (fst bp) = conc st bg + 16 + get_stride (get_meta_rec st g) * idx
    /\ conc st bg = r_base r + snd bg /\ 0 <= old /\ A + old <= conc st (fst bp) + get_stride (get_meta_rec st g) - IB
    /\ conc st (fst bp) + get_stride (get_meta_rec st g) <= r_base r + round_up_pg (r_len r) /\ r_base r + round_up_pg (r_len r) <= alloc_ceiling
    /\ 0 <= m_sizeclass (get_meta_rec st g) < 64 /\ (48 <= m_sizeclass (get_meta_rec st g) -> m_sizeclass (get_meta_rec st g) = 63)
    /\ evt rsegs (hdr_post ra1 sp gp tp s0 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 F fc m A n old (conc st g) (conc st bg) (get_stride (get_meta_rec st g)) idx
                    (m_last_idx (get_meta_rec st g)) (m_freeable (get_meta_rec st g)) (m_sizeclass (get_meta_rec st g)) (m_maplen (get_meta_rec st g)))
      (MS (mkR ra1 sp gp tp t0 t1 y7 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 n) y12 y13 y14 y15 y16 y17
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 t5 t6)
          F (Z_to_bv 64 0x4b26c) fc None m (seg_rom rsegs)).
Proof.
  intros until n. intros RMR MI AR Hb HN.
  pose proof RMR as (WF & CX & GL & ARS & GR & SH). pose proof WF as (Hres & WR & DISJ & WA & WG).
  destruct (A_MallocFacts_inv.areach_inv _ _ _ AR) as (L & LS & BL & INV & _ & _ & _ & CR).
  pose proof (A_MallocFacts_inv3.areach_cinv_proof _ _ AR) as C.
  destruct (A_MallocFacts_inv.Forall2_In_l _ _ _ _ CR Hb) as (k & Hk & (C1 & C2 & C3)).
  destruct k as [[c off] n']. cbn [bslot boff bsize blk_slot blk_size blk_addr fst snd] in C1, C2, C3. subst n'.
  assert (C1' : fst bp = c) by exact C1.
  destruct (block_facts x0 st L BL LS INV c off old Hk) as (mm & bm & i & ai & a & ar & ka & BF).
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  pose proof (bf_slot _ _ _ _ _ _ _ _ _ _ _ BF) as SL. pose proof (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF) as HG.
  pose proof (bf_mem _ _ _ _ _ _ _ _ _ _ _ BF) as HM. pose proof (bf_c _ _ _ _ _ _ _ _ _ _ _ BF) as EC.
  pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF) as Hi. pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF) as Hoff.
  pose proof (bf_n _ _ _ _ _ _ _ _ _ _ _ BF) as Ho. pose proof (bf_fit _ _ _ _ _ _ _ _ _ _ _ BF) as FIT.
  pose proof (bf_stride _ _ _ _ _ _ _ _ _ _ _ BF) as [S1 S2]. pose proof (bf_b16 _ _ _ _ _ _ _ _ _ _ _ BF) as [Bb0 Bb16].
  pose proof (bf_notA _ _ _ _ _ _ _ _ _ _ _ BF) as NA. pose proof (bf_notF _ _ _ _ _ _ _ _ _ _ _ BF) as NF. unfold tbit in NA, NF.
  pose proof (bf_top _ _ _ _ _ _ _ _ _ _ _ BF) as TOP. pose proof (bf_hdr0 _ _ _ _ _ _ _ _ _ _ _ BF) as H0E.
  destruct (bf_area _ _ _ _ _ _ _ _ _ _ _ BF) as (Ha & Hck & Hal & Hka & Emm).
  pose proof (q16 _ _ _ _ _ _ _ _ _ _ _ BF) as [Q1 Q2]. pose proof (p_mod16 _ _ _ _ _ _ _ _ _ _ _ BF) as PM16.
  pose proof (bf_shadow _ _ _ _ _ _ _ _ _ _ _ BF) as SHB. unfold blk_shadow_ok in SHB. cbn [bslot boff bsize fst snd] in SHB.
  rewrite (gbase_bm _ _ _ _ _ _ _ _ _ _ _ BF) in SHB.
  cbn [aadd snd] in Q1, Q2, PM16.
  set (q := (snd c + UNIT * off - snd bm - UNIT) / UNIT) in *.
  destruct SHB as (K4 & K3 & K2 & K1 & _ & K5 & Kr & KU).
  set (mr := MI_Inv.MR st mm) in *.
  set (stride := get_stride mr) in *.
  set (po := snd c + UNIT * off) in *.
  set (e := snd c + stride - IB) in *.
  set (res := e - po - old) in *.
  pose proof (ig_ok _ _ _ IG _ _ _ HG) as GOK.
  destruct (ig_region _ _ _ IG _ _ HG) as (r & Hr & Kr').
  pose proof (proj1 (List.Forall_forall _ _) (ci_blks _ _ C) _ Hb) as BK.
  destruct BK as [(g & i' & b0 & SL' & HB' & FB' & I' & NFR & _) NG SZ]. cbn [blk_slot blk_size fst snd] in SL', NG, SZ, FB'.
  rewrite ?C1, ?C1', SL in SL'. assert (g = mm /\ i' = i) as [-> ->] by (split; congruence). clear SL'.
  pose proof (ci_gmetas _ _ C b0 mm HB') as GO.
  assert (Eb0 : b0 = bm) by (pose proof (go_mem _ _ _ GO) as X; change (get_meta_rec st mm) with mr in X; rewrite HM in X; congruence). subst b0.
  destruct (go_region _ _ _ GO) as (r' & Hr' & _ & _ & _ & SPAN & _). rewrite Hr in Hr'. assert (r' = r) as -> by congruence.
  pose proof (go_avail _ _ _ GO) as AV. pose proof (go_freed _ _ _ GO) as FRD. pose proof (go_li _ _ _ GO) as LI.
  pose proof (go_freeable _ _ _ GO) as FB1. pose proof (go_maplen _ _ _ GO) as ML. pose proof (go_sc _ _ _ GO) as GSC.
  change (get_meta_rec st mm) with mr in AV, FRD, LI, FB1, ML, GSC, SPAN.
  pose proof (proj2 (proj2 (proj2 (proj2 (ci_cx _ _ C))))) as SE.
  unfold sstart_of in SPAN. rewrite HM in SPAN. cbn [default id snd] in SPAN. fold stride in SPAN.
  destruct (WR _ _ Hr) as (RrB0 & RBAL & RL0 & RBC & RF). pose_ceil.
  destruct (SH _ _ Hr Kr') as [WRr RDr].
  assert (FC : fst c = fst bm) by (rewrite EC; reflexivity).
  assert (SC' : snd c = snd bm + 16 + stride * i) by (rewrite EC; unfold sstart; rewrite (gbase_bm _ _ _ _ _ _ _ _ _ _ _ BF); reflexivity).
  assert (CC : conc st c = r_base r + snd c) by (apply conc_region'; rewrite FC; exact Hr).
  assert (CB : conc st bm = r_base r + snd bm) by (apply conc_region'; exact Hr).
  assert (SI0 : 0 <= stride * i) by (apply Z.mul_nonneg_nonneg; unfold UNIT in S1; lia).
  assert (SIL : stride * (i + 1) <= stride * (m_last_idx mr + 1)) by (apply Z.mul_le_mono_nonneg_l; unfold UNIT in S1; lia).
  assert (EHI' : e + IB <= round_up_pg (r_len r)).
  { clear - SC' SIL SPAN S1. subst e. rewrite SC'. unfold UNIT, IB in *. lia. }
  assert (HA : A = r_base r + po) by (subst po; rewrite C3, CC; unfold UNIT; clear; lia).
  assert (HE : e = snd bm + 16 + stride * i + stride - IB) by (subst e; rewrite SC'; clear; lia).
  assert (HPO : po = snd bm + 16 + 16 * q) by (subst po; rewrite SC'; clear - Q1; unfold UNIT in *; lia).
  assert (RESE : res = r_base r + e - A - old) by (subst res; rewrite HA; clear; lia).
  assert (AL : A mod 16 = 0) by (rewrite HA; clear - PM16 RBAL; Z.div_mod_to_equations; lia).
  assert (FIT' : po + old <= e) by (subst po e; unfold UNIT, IB in *; clear - FIT; lia).
  assert (PO16 : 16 <= po) by (rewrite HPO; clear - Bb0 Q2; lia).
  assert (RES0 : 0 <= res) by (subst res; clear - FIT'; lia).
  pose proof (round_up_pg_ge (r_len r)) as RUP.
  pose proof (rreserved_disjoint1 _ _ RF ltac:(clear - EHI' FIT' PO16 Ho; unfold IB in EHI'; lia)) as DRr.
  clearbody q po e res. clear PM16 Bb16 S2.
  assert (MSL : meta_slot st mm) by (exists a, ar, ka; split; [exact Ha|]; split; [exact Hka| exact Emm]).
  pose proof (rmeta_slot_bounds st m mm RMR MSL) as (GB0 & GB1 & _ & _ & _).
  destruct (WA a ar Ha) as (rg & Hrg & A0 & A1 & AAL & ANG & _).
  assert (HGc : conc st mm = r_base rg + snd a + (AREA_HDR + META_SIZE * ka)).
  { rewrite Emm. unfold mslot. rewrite conc_aadd by (rewrite Hrg; eauto). rewrite (conc_region' st a rg Hrg). reflexivity. }
  destruct (WR (fst a) rg Hrg) as (RgB0 & RgBAL & _ & RgBC & _). pose_ceil.
  assert (HAR : conc st (area_of mm) = conc st mm - conc st mm mod 4096).
  { rewrite Emm, (area_of_mslot a ka Hal Hka). rewrite <- Emm. rewrite HGc, (conc_region' st a rg Hrg).
    unfold AREA_HDR, META_SIZE, NSLOTS, PGSZ in *. clear - Hka Hal RgBAL A0.
    replace (r_base rg + snd a + (24 + 40 * ka)) with ((24 + 40 * ka) + (snd a / 4096 + r_base rg / 4096) * 4096) by (Z.div_mod_to_equations; nia).
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. Z.div_mod_to_equations; nia. }

  assert (RD : forall o v, cell_read (get_shadow st (fst c)) o = Known v -> 0 <= o < round_up_pg (r_len r) ->
            ov_read_bytes rsegs m (wa (r_base r + o)) 1 = Some [b8 v] /\ 0 <= v < 256).
  { intros o v Hoq Hor. rewrite FC in Hoq. exact (rmrep_shadow_read st m (fst bm) r o v RMR Hr Kr' Hor Hoq). }
  destruct (RD (po - 4) 0 K4 ltac:(clear - PO16 FIT' EHI' Ho; unfold IB in *; lia)) as [R4 _].
  destruct (RD (po - 3) _ K3 ltac:(clear - PO16 FIT' EHI' Ho; unfold IB in *; lia)) as [R3 B3R].
  assert (K2' : cell_read (get_shadow st (fst bm)) (po - 2) = Known (byte_of q 0)) by (rewrite <- FC; exact K2).
  assert (K1' : cell_read (get_shadow st (fst bm)) (po - 2 + 1) = Known (byte_of q 1)) by (rewrite <- FC; replace (po - 2 + 1) with (po - 1) by (clear; lia); exact K1).
  destruct (rmrep_shadow_read2 st m (fst bm) r (po - 2) _ _ RMR Hr Kr' ltac:(clear - PO16; lia) ltac:(clear - PO16 FIT' EHI' Ho; unfold IB in *; lia) K2' K1') as (R2 & LO8 & HI8).
  rewrite <- le2_lohi, (u16_bytes q Q2) in R2 by assumption.
  replace (r_base r + (po - 4)) with (A - 4) in R4 by (clear - HA; lia).
  replace (r_base r + (po - 3)) with (A - 3) in R3 by (clear - HA; lia).
  replace (r_base r + (po - 2)) with (A - 2) in R2 by (clear - HA; lia).
  destruct (rmrep_group_read st m bm _ RMR HG) as [RG _]. cbn [g_meta pw oconc] in RG.
  pose proof (rmrep_meta_chunk st m mm RMR MSL) as MM. change (get_meta_rec st mm) with mr in MM. unfold meta_cells in MM. rewrite HM in MM. cbn [pw oconc] in MM. change (pw st (Some bm)) with (wz (conc st bm)) in MM. unfold meta_word in MM.
  pose proof (rmrep_area_check_read st m a ar RMR Ha) as RA. rewrite Hck in RA. change (c_secret (s_ctx st)) with (c_secret (ctx st)) in RA.
  replace (conc st a) with (conc st mm - conc st mm mod 4096) in RA by (rewrite <- HAR, Emm, (area_of_mslot a ka Hal Hka); reflexivity).
  pose proof (rmrep_ctx_secret_read st m RMR) as RC.

  assert (RE0 : ov_read_bytes rsegs m (wa (r_base r + e)) 1 = Some [b8 0]).
  { apply (RD e 0); [| clear - PO16 FIT' EHI' Ho; unfold IB in *; lia].
    unfold known, SHd in H0E. cbn [fst snd] in H0E. rewrite <- FC in H0E. rewrite sstart_succ in H0E. fold mr stride in H0E.
    replace e with (sstart mr i + stride - IB); [exact H0E|]. rewrite HE. unfold sstart. fold mr. rewrite (gbase_bm _ _ _ _ _ _ _ _ _ _ _ BF). fold stride. unfold UNIT. clear; lia. }
  assert (RB0 : 0 < res -> ov_read_bytes rsegs m (wa (r_base r + e - res)) 1 = Some [b8 0]).
  { intros Hr0. replace (r_base r + e - res) with (r_base r + (e - res)) by (clear; lia). apply (RD (e - res) 0 (Kr Hr0)). clear - PO16 FIT' EHI' Ho Hr0 RES0 RESE HA; unfold IB in *; lia. }
  assert (RB5 : 5 <= res -> ov_read_bytes rsegs m (wa (r_base r + e - 5)) 1 = Some [b8 0] /\ ov_read_bytes rsegs m (wa (r_base r + e - 4)) 4 = Some (le4 (wz res))).
  { intros Hr5. destruct (K5 Hr5) as (E0 & E1 & E2 & E3 & E5 & R32). split.
    - replace (r_base r + e - 5) with (r_base r + (e - 5)) by (clear; lia). apply (RD (e - 5) 0 E5). clear - PO16 FIT' EHI' Ho Hr5; unfold IB in *; lia.
    - rewrite le4_bytes by (clear - RES0 R32; lia).
      rewrite <- (byte_of_0 res), <- (byte_of_1 res), <- (byte_of_2 res) by (clear - RES0; lia).
      replace (res / 16777216) with (byte_of res 3) by (rewrite byte_of_3 by (clear - RES0; lia); apply Z.mod_small; clear - RES0 R32; Z.div_mod_to_equations; lia).
      replace (wa (r_base r + e - 4)) with (wa (r_base r + (e - 4) + Z.of_nat 0)) by (unfold wa; f_equal; clear; lia).
      apply (bytes_at_ov_read rsegs m (r_base r + (e - 4)) [b8 (byte_of res 0); b8 (byte_of res 1); b8 (byte_of res 2); b8 (byte_of res 3)] 0 4); [| cbn; lia].
      apply bytes_at_4.
      + exact (proj1 (RDr (e - 4) _ ltac:(clear - PO16 FIT' EHI' Ho Hr5; unfold IB in *; lia) ltac:(rewrite <- FC; exact E0))).
      + replace (r_base r + (e - 4) + 1) with (r_base r + (e - 3)) by (clear; lia). exact (proj1 (RDr (e - 3) _ ltac:(clear - PO16 FIT' EHI' Ho Hr5; unfold IB in *; lia) ltac:(rewrite <- FC; exact E1))).
      + replace (r_base r + (e - 4) + 2) with (r_base r + (e - 2)) by (clear; lia). exact (proj1 (RDr (e - 2) _ ltac:(clear - PO16 FIT' EHI' Ho Hr5; unfold IB in *; lia) ltac:(rewrite <- FC; exact E2))).
      + replace (r_base r + (e - 4) + 3) with (r_base r + (e - 1)) by (clear; lia). exact (proj1 (RDr (e - 1) _ ltac:(clear - PO16 FIT' EHI' Ho Hr5; unfold IB in *; lia) ltac:(rewrite <- FC; exact E3))). }
  assert (RES32 : res < 2 ^ 32).
  { destruct (Z.lt_ge_cases res 5) as [LT|GE]; [clear - LT; lia|]. destruct (K5 GE) as (_ & _ & _ & _ & _ & R32). exact R32. }
  pose proof (bf_sc _ _ _ _ _ _ _ _ _ _ _ BF) as BSC. fold mr in BSC. fold stride in BSC.

  exists mm, bm, i, r. rewrite C1'. change (get_meta_rec st mm) with mr. fold stride.
  split; [exact SL|]. split; [exact HM|]. split; [exact Hr|]. split; [exact Kr'|]. split; [exact FC|].
  split; [rewrite CC, CB, SC'; clear; lia|]. split; [exact CB|]. split; [exact Ho|].
  split; [rewrite CC; fold stride; clear - HA FIT' HE SC'; unfold IB in *; lia|].
  split; [rewrite CC; fold stride; clear - EHI' HE SC'; unfold IB in *; lia|]. split; [clear - RBC; pose_ceil; lia|].
  split; [clear - GSC; lia|]. split; [clear - GSC; lia|].
  apply (hdr_428 ra1 sp gp tp t0 t1 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 F fc m
           A n old (conc st mm) (conc st bm) (conc st mm - conc st mm mod 4096) stride i res q
           (m_avail mr) (m_freed mr) (m_last_idx mr) (m_freeable mr) (m_sizeclass mr) (m_maplen mr) (c_secret (ctx st))
           (pw st (m_prev mr)) (pw st (m_next mr))).
  - exact Ho.
  - clear - HA RrB0 PO16. lia.
  - exact AL.
  - clear - HA HPO Bb0 RrB0. lia.
  - clear - HA FIT' EHI' RBC Ho RUP. unfold IB in *. lia.
  - clear - CB HA HPO. lia.
  - reflexivity.
  - clear - GB0. lia.
  - clear - GB1. lia.
  - exact R4.
  - exact R3.
  - exact R2.
  - exact RG.
  - exact MM.
  - exact RA.
  - exact RC.
  - intros Hlt. apply rsize_classes_read; [exact MI| clear - Hlt GSC; lia].
  - clear - Hi LI. lia.
  - exact Q2.
  - exact AV.
  - exact FRD.
  - exact SE.
  - clear - LI. lia.
  - rewrite FB1. clear. lia.
  - clear - GSC. lia.
  - clear - ML. lia.
  - clear - Hi. lia.
  - exact NA.
  - exact NF.
  - intros Hlt. destruct BSC as [(Hsc & Hle & Hst)| E63]; [| clear - Hlt E63; lia].
    pose proof (size_class_bound _ Hsc) as SB.
    assert (A' : stride = 16 * size_class (m_sizeclass mr) \/ m_last_idx mr = 0) by (clear - Hst; unfold UNIT in Hst; tauto).
    assert (B' : stride <= 16 * size_class (m_sizeclass mr) \/ 292 <= size_class (m_sizeclass mr)).
    { destruct Hle as [Hle|H28]; [left; unfold UNIT in Hle; exact Hle| right; apply size_class_28; clear - H28 Hsc; lia]. }
    clear - SB Q1 FIT Ho Hoff Hi A' B'. unfold UNIT, IB in *.
    exact (guard16_arith _ _ _ _ _ _ _ (proj1 SB) Q1 FIT Ho Hoff Hi A' B').
  - clear - GSC. lia.
  - intros NM. destruct (TOP NM) as [B0 GE]. unfold gend, cnt_of, sstart in GE. rewrite (gbase_bm _ _ _ _ _ _ _ _ _ _ _ BF), B0 in GE.
    fold mr in GE. fold stride in GE.
    replace (m_maplen mr * 256) with (m_maplen mr * 4096 / 16) by (rewrite <- (Z.div_mul (m_maplen mr * 256) 16) by lia; f_equal; lia).
    clear - S1 Q1 FIT Ho Hoff Hi GE. unfold UNIT, IB in *.
    eapply (guard17_arith stride i off old q); try eassumption; lia.
  - intros Hd. destruct GSC as [Hsc|(E63 & L0 & MLn)]; [| exfalso; clear - Hd L0 MLn; lia].
    split; [clear - Hsc; lia|]. subst stride. unfold get_stride.
    destruct Hd as [Hd|Hd]; [rewrite (proj2 (Z.eqb_eq _ _) Hd), andb_false_r; reflexivity| rewrite (proj2 (Z.eqb_neq _ _) Hd); reflexivity].
  - intros [L0 MLn]. subst stride. unfold get_stride. rewrite (proj2 (Z.eqb_eq _ _) L0). replace (m_maplen mr =? 0) with false by (symmetry; apply Z.eqb_neq; exact MLn). reflexivity.
  - clear - RES0 RES32. lia.
  - clear - RESE HE CB. unfold IB in *. lia.
  - clear - DRr EHI' HA PO16 HE CB FIT' Ho. unfold IB in *. lia.
  - clear - EHI' HE CB RBC RUP. unfold IB in *. lia.
  - intros H. replace (conc st bm + 16 + stride * (i + 1) - 4 - res) with (r_base r + e - res) by (clear - HE CB; unfold IB in *; lia). exact (RB0 H).
  - intros H. replace (conc st bm + 16 + stride * (i + 1) - 4 - 5) with (r_base r + e - 5) by (clear - HE CB; unfold IB in *; lia).
    replace (conc st bm + 16 + stride * (i + 1) - 4 - 4) with (r_base r + e - 4) by (clear - HE CB; unfold IB in *; lia). exact (RB5 H).
  - replace (conc st bm + 16 + stride * (i + 1) - 4) with (r_base r + e) by (clear - HE CB; unfold IB in *; lia). exact RE0.
Qed.

End CEIL.
End TwinB.
