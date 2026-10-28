(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes Decode.
From OssFuzzTheorems.openssl.ct.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import F_malloc_free F_malloc_enframe MallocBlocks MallocHINV MallocFacts_B. (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocKit_A MallocKit_B MallocKit_B2 MallocModel_B MallocKit_B3 MallocFacts_Bpres F_mm_syscalls F_ntf F_free_C F_free_K F_free.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B2 RMallocKit_B3 RF_get_meta RF_mm_syscalls.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RF_free_A RF_free_B RF_free_C RF_ntf RF_free_K RF_free RF_realloc_A.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import MI_Inv MI_Arith MI_Read MI_Pres2 MI_WFree.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.ZBridge.flia ::= first [ assumption | OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.ZBridge.slim; lia | lia ].
Local Ltac OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Lemma area_slot_mod (rb sa k : Z) : rb mod 4096 = 0 -> sa mod 4096 = 0 -> 0 <= k < NSLOTS ->
  (rb + sa + (AREA_HDR + META_SIZE * k)) mod 4096 = AREA_HDR + META_SIZE * k.
Proof.
  unfold AREA_HDR, META_SIZE, NSLOTS. intros Hb Ha Hk.
  pose proof (Z.div_mod rb 4096 ltac:(Lia.lia)) as E1. pose proof (Z.div_mod sa 4096 ltac:(Lia.lia)) as E2. rewrite Hb in E1. rewrite Ha in E2.
  replace (rb + sa + (24 + 40 * k)) with ((24 + 40 * k) + (sa / 4096 + rb / 4096) * 4096) by Lia.lia.
  rewrite Z.mod_add by Lia.lia. apply Z.mod_small. Lia.lia.
Qed.

(* [comment removed for export] *)
Lemma rrealloc_hdr_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (st : mstate) (LB : list block) (blk : block) (off n : Z) L BL LS,
  CINV st LB -> In blk LB -> 0 <= off -> blk_addr blk = conc st (blk_slot blk) + UNIT * off ->
  INVL x0 st L BL LS -> In ((blk_slot blk, off), blk_size blk) BL ->
  rmrep st m -> mem_inv ctusegs m -> c_init_done (ctx st) <> 0 ->
  a0 = Z_to_bv 64 (blk_addr blk) -> bv_unsigned a1 = n -> 0 <= n < 2^32 ->
  (forall g i, (s_slots st) !! (blk_slot blk) = Some (g, i) ->
     get_stride (get_meta_rec st g) - IB < n /\ (m_sizeclass (get_meta_rec st g) < 48 \/ n < MMAP_THRESHOLD)) ->
  evt ctusegs (rrealloc_hdr_post sp gp tp a0 a1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 (blk_addr blk + blk_size blk) F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x2b4fb4) fc None m (seg_rom ctusegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until LS. intros C Hin Hoff HA INV Hk HMR MI INI A0 HN NR MOVES.
  pose proof (KINV_of_CINV _ _ C) as K0.
  pose proof (proj1 (List.Forall_forall _ _) (ci_blks _ _ C) blk Hin) as BK.
  destruct BK as [(g & i & b & SL & HB & FB & I & NFR & (off' & O0 & OA & OS & OK & HK)) NG SZ].
  assert (off' = off) as -> by (rewrite HA in OA; unfold UNIT in OA; lia).
  clear OA.
  destruct (MOVES g i SL) as [MV1 MV2]. clear MOVES.
  set (c0 := blk_slot blk) in *. set (n0 := blk_size blk) in *.
  pose proof (ci_gmetas _ _ C b g HB) as GO.
  destruct (go_region _ _ _ GO) as (r & Hr & Kr & B0 & B16 & SPAN & TOP).
  pose proof HMR as (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DJ & WA & WG).
  destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RF).
  (* [comment removed for export] *)
  destruct (block_facts x0 st L BL LS INV c0 off n0 Hk) as (g' & bm & i' & ai & a & ar & ka & BF).
  pose proof (bf_slot _ _ _ _ _ _ _ _ _ _ _ BF) as SL'. rewrite SL in SL'. inversion SL'. subst g' i'. clear SL'.
  pose proof (bf_mem _ _ _ _ _ _ _ _ _ _ _ BF) as Hmem'. unfold MI_Inv.MR in Hmem'. rewrite (go_mem _ _ _ GO) in Hmem'. inversion Hmem'. subst bm. clear Hmem'.
  set (mr := get_meta_rec st g) in *.
  set (stride := get_stride mr) in *.
  pose proof (go_stride _ _ _ GO) as [S16 SM]. pose proof (go_li _ _ _ GO) as LI. fold mr in S16, SM, LI. fold stride in S16, SM.
  destruct (ki_slts _ _ _ K0 _ _ _ SL) as (GMg & Ec & _). fold c0 in Ec.
  assert (Hr0 : s_regions st !! fst c0 = Some r) by (rewrite <- FB; exact Hr).
  assert (Cc : conc st c0 = r_base r + snd c0) by (apply conc_region'; exact Hr0).
  assert (Cb : conc st b = r_base r + snd b) by (apply conc_region'; exact Hr).
  assert (Sc : snd c0 = snd b + 16 + stride * i).
  { rewrite Ec. rewrite (slot_start'_mem _ b i (go_mem _ _ _ GO)). cbn. unfold UNIT. subst stride mr. lia. }
  assert (SI0 : 0 <= stride * i) by (apply Z.mul_nonneg_nonneg; unfold UNIT in S16; lia).
  assert (SIL : stride * (i + 1) <= stride * (m_last_idx mr + 1)).
  { apply Z.mul_le_mono_nonneg_l; unfold UNIT in S16; lia. }
  unfold sstart_of in SPAN. fold mr in SPAN. rewrite (go_mem _ _ _ GO) in SPAN. cbn [default id snd] in SPAN. fold stride in SPAN.
  (* [comment removed for export] *)
  pose proof (bf_shadow _ _ _ _ _ _ _ _ _ _ _ BF) as S. unfold blk_shadow_ok in S. cbn [bslot boff bsize fst snd] in S.
  rewrite (gbase_bm st c0 off n0 g b i ai a ar ka BF) in S.
  unfold MI_Inv.MR in S. fold mr in S. fold stride in S.
  destruct S as (K4 & K3 & K2 & K1 & Q & K5 & Kr0 & KU).
  pose proof (q16 st c0 off n0 g b i ai a ar ka BF) as [Q16 _]. unfold MI_Inv.MR in Q16. fold mr in Q16. fold stride in Q16.
  pose proof (bf_hdr0 _ _ _ _ _ _ _ _ _ _ _ BF) as H0. unfold MI_Inv.MR in H0. fold mr in H0.
  pose proof (bf_fit _ _ _ _ _ _ _ _ _ _ _ BF) as FIT. unfold MI_Inv.MR in FIT. fold mr in FIT. fold stride in FIT.
  pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF) as OFF.
  unfold known, SHd in K4, K3, K2, K1, K5, Kr0, H0. cbn [fst snd] in K4, K3, K2, K1, K5, Kr0, H0.
  set (po := snd c0 + UNIT * off) in *.
  set (e := snd c0 + stride - IB) in *.
  set (res := e - po - n0) in *.
  set (q := (po - snd b - UNIT) / UNIT) in *.
  assert (RES0 : 0 <= res) by (subst res e po; unfold UNIT, IB in *; lia).
  assert (H0e : cell_read (get_shadow st (fst c0)) e = Known 0).
  { rewrite <- FB. replace e with (sstart mr (i + 1) - IB); [exact H0|].
    subst e. rewrite Sc. unfold sstart, gbase. rewrite (go_mem _ _ _ GO). cbn [default id snd]. fold stride. unfold UNIT, IB. lia. }
  cbn [aadd snd] in Q16. fold po in Q16. fold q in Q16.
  destruct (SH (fst c0) r Hr0 Kr) as [HWr HBy].
  rewrite Z.mul_add_distr_l, Z.mul_1_r in SIL.
  unfold OssFuzzTheorems.Proofs.openssl.ct.lib.Spec.Malloc.MCEIL in RBC.
  assert (PO16 : 16 <= po) by (subst po; unfold UNIT in *; lia).
  assert (EHIr : e + 4 <= round_up_pg (r_len r)) by (subst e; unfold UNIT, IB in *; lia).
  assert (POE : po + n0 + res = e) by (subst res; lia).
  (* [comment removed for export] *)
  set (b3 := i + 32 * Z.min res 5).
  assert (IDXe : Z.land b3 31 = i) by (apply land31_idx; lia).
  assert (RSV0e : Z.shiftr b3 5 = Z.min res 5) by (apply shiftr5_res; lia).
  set (rsv := if 160 <=? b3 then res else Z.shiftr b3 5).
  assert (RSVe : rsv = res).
  { unfold rsv. rewrite RSV0e. destruct (Z.leb_spec 160 b3); [reflexivity|]. subst b3. lia. }
  set (P := r_base r + po).
  assert (HP : bv_unsigned a0 = P).
  { rewrite A0, HA, Cc. unfold P, po. rewrite unsigned_lit; [lia|]. unfold UNIT in *. pose proof (round_up_pg_ge (r_len r)). lia. }
  (* [comment removed for export] *)
  destruct (rmrep_shadow_read st m (fst c0) r (po - 4) 0 HMR Hr0 Kr ltac:(lia) K4) as [R4 _].
  destruct (rmrep_shadow_read st m (fst c0) r (po - 3) b3 HMR Hr0 Kr ltac:(lia) K3) as [R3 B3R].
  destruct (rmrep_shadow_read2 st m (fst c0) r (po - 2) (byte_of q 0) (byte_of q 1) HMR Hr0 Kr ltac:(lia) ltac:(lia) K2
              ltac:(replace (po - 2 + 1) with (po - 1) by lia; exact K1)) as (R2 & LO & HI).
  rewrite <- le2_lohi in R2 by lia. rewrite (u16_bytes q Q) in R2.
  (* [comment removed for export] *)
  destruct HB as [ai0 Hgh].
  destruct (rmrep_group_read st m b _ HMR Hgh) as [RG _]. cbn [g_meta pw oconc] in RG.
  pose proof (rmrep_meta_chunk st m g HMR (go_slot _ _ _ GO)) as MM. fold mr in MM. unfold meta_cells in MM.
  rewrite (go_mem _ _ _ GO) in MM. cbn [pw oconc] in MM. unfold meta_word in MM.
  (* [comment removed for export] *)
  destruct (bf_area _ _ _ _ _ _ _ _ _ _ _ BF) as (Har & Hchk & Hal & Hka & Em).
  assert (EAO : area_of g = a) by (rewrite Em; apply area_of_mslot; assumption).
  pose proof (rmrep_area_check_read st m a ar HMR Har) as RA. rewrite Hchk in RA.
  pose proof (rmrep_ctx_secret_read st m HMR) as RC. rewrite (rsec_init _ _ INI) in RC.
  change (s_ctx st) with (ctx st) in RA.
  rewrite <- (wz_mod64 (c_secret (ctx st) + bv_unsigned rr_secret)) in RA, RC.
  destruct (WA a ar Har) as (rg & Hrg & A00 & A01 & AAL & ANG & _).
  destruct (WR (fst a) rg Hrg) as (RB0g & RBALg & RL0g & RBCg & _).
  unfold OssFuzzTheorems.Proofs.openssl.ct.lib.Spec.Malloc.MCEIL in RBCg.
  assert (HG : conc st g = r_base rg + snd a + (AREA_HDR + META_SIZE * ka)).
  { rewrite Em. unfold mslot. rewrite conc_aadd by (rewrite Hrg; eauto). rewrite (conc_region' st a rg Hrg). reflexivity. }
  assert (Hm : (r_base rg + snd a + (AREA_HDR + META_SIZE * ka)) mod 4096 = AREA_HDR + META_SIZE * ka).
  { apply area_slot_mod; [exact RBALg| exact AAL| exact Hka]. }
  assert (HAa : conc st a = conc st g - conc st g mod 4096).
  { rewrite HG, Hm. rewrite (conc_region' st a rg Hrg). lia. }
  pose proof (round_up_pg_ge (r_len rg)) as RUG.
  pose proof (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) blk Hin) as BC.
  destruct BC as [(r0 & Hr0' & _ & A16 & AEND & AL & UNK) _ _]. clear r0 Hr0' A16 AEND UNK.
  set (E := conc st b + 16 + stride * i + stride - 4).
  assert (EE : E = r_base r + e) by (subst E e; rewrite Cb, Sc; unfold IB; lia).
  assert (STRW : stride = (if (m_last_idx mr =? 0) && negb (m_maplen mr =? 0) then 4096 * m_maplen mr - 16 else 16 * size_class (m_sizeclass mr))).
  { unfold stride, get_stride. destruct ((m_last_idx mr =? 0) && negb (m_maplen mr =? 0)); unfold UNIT; lia. }
  pose proof (go_sc _ _ _ GO) as GSC. fold mr in GSC.
  pose proof (go_maplen _ _ _ GO) as GML. fold mr in GML.
  pose proof (go_avail _ _ _ GO) as GAV. pose proof (go_freed _ _ _ GO) as GFR. fold mr in GAV, GFR.
  pose proof (go_freeable _ _ _ GO) as GFB. fold mr in GFB.
  assert (NA : Z.testbit (m_avail mr) i = false) by (destruct (Z.testbit (m_avail mr) i) eqn:E1; [exfalso; apply NFR; right; exact E1| reflexivity]).
  assert (NF : Z.testbit (m_freed mr) i = false) by (destruct (Z.testbit (m_freed mr) i) eqn:E1; [exfalso; apply NFR; left; exact E1| reflexivity]).
  assert (PEQ : P = blk_addr blk) by (rewrite HA, Cc; unfold P, po; lia).
  unfold UNIT, IB in *.
  eapply rrealloc_hdr_walk_eq with (P:=P) (G:=conc st g) (B:=conc st b) (A:=conc st a) (n:=n) (b3:=b3) (off16:=q)
     (avail:=m_avail mr) (freed:=m_freed mr) (last_idx:=m_last_idx mr) (freeable:=m_freeable mr) (sc:=m_sizeclass mr) (maplen:=m_maplen mr)
     (secret:=(c_secret (ctx st) + bv_unsigned rr_secret) mod 2^64) (r32:=res) (prev:=pw st (m_prev mr)) (next:=pw st (m_next mr))
     (stride:=stride) (E:=E) (rsv:=rsv) (s2v:=blk_addr blk + n0).
  - exact STRW.
  - rewrite IDXe. reflexivity.
  - reflexivity.
  - rewrite RSVe, EE, <- PEQ. unfold P. unfold res. lia.
  - exact HP.
  - exact HN.
  - rewrite PEQ. exact AL.
  - unfold P, po. rewrite Sc. lia.
  - unfold P, po. rewrite Sc. pose proof (round_up_pg_ge (r_len r)). lia.
  - rewrite Cb. unfold P, po. rewrite Sc. lia.
  - exact HAa.
  - rewrite HG. unfold AREA_HDR, META_SIZE in *. lia.
  - rewrite HG. unfold AREA_HDR, META_SIZE, NSLOTS in *. lia.
  - replace (P - 4) with (r_base r + (po - 4)) by (unfold P; lia). exact R4.
  - replace (P - 3) with (r_base r + (po - 3)) by (unfold P; lia). exact R3.
  - replace (P - 2) with (r_base r + (po - 2)) by (unfold P; lia). exact R2.
  - exact RG.
  - exact MM.
  - exact RA.
  - exact RC.
  - intros Hlt. apply rsize_classes_read; [exact MI| first [solve [clear - GSC Hlt; lia] | lia]].
  - exact B3R.
  - exact Q.
  - exact GAV.
  - exact GFR.
  - apply rsec_range.
  - first [solve [clear - LI; lia] | lia].
  - first [solve [clear - GFB; lia] | lia].
  - first [solve [clear - GSC; lia] | lia].
  - first [solve [clear - GML; lia] | lia].
  - rewrite IDXe. first [solve [clear - I; lia] | lia].
  - rewrite IDXe. exact NA.
  - rewrite IDXe. exact NF.
  - intros Hsc. rewrite IDXe.
    destruct (bf_sc _ _ _ _ _ _ _ _ _ _ _ BF) as [(Hsc0 & Hle & Hst)| E63]; [| unfold MI_Inv.MR in E63; fold mr in E63; lia].
    unfold MI_Inv.MR in Hle, Hst. fold mr in Hle, Hst. fold stride in Hle, Hst. unfold UNIT in Hle, Hst.
    pose proof (size_class_bound _ Hsc0) as SB. unfold MI_Inv.MR in SB. fold mr in SB.
    assert (A1 : stride = 16 * size_class (m_sizeclass mr) \/ m_last_idx mr = 0) by tauto.
    assert (B1 : stride <= 16 * size_class (m_sizeclass mr) \/ 292 <= size_class (m_sizeclass mr)).
    { destruct Hle as [Hle|H28]; [left; exact Hle| right; apply size_class_28; lia]. }
    exact (guard16_arith _ _ _ _ _ _ _ (proj1 SB) Q16 FIT SZ OFF I A1 B1).
  - intros Hsc. first [solve [clear - GSC Hsc; lia] | lia].
  - intros Hml. destruct (TOP Hml) as [B00 TOPE].
    pose proof (guard17_arith stride i off n0 q (m_last_idx mr) (m_maplen mr) S16 Q16 FIT SZ Hoff I ltac:(lia)) as G17.
    replace (m_maplen mr * 4096 / 16) with (m_maplen mr * 256) in G17 by (rewrite <- (Z.div_mul (m_maplen mr * 256) 16) by lia; f_equal; lia).
    exact G17.
  - first [solve [clear - GSC; lia] | lia].
  - exact S16.
  - rewrite Cb. lia.
  - rewrite EE. unfold P, po, e. lia.
  - rewrite EE. first [solve [clear - EHIr RBC CEIL_RANGE__; unfold ceil_window in *; lia] | pose proof (round_up_pg_ge (r_len r)); lia].
  - intros H160. assert (R5 : 5 <= res) by (subst b3; lia).
    destruct (K5 R5) as (Y0 & Y1 & Y2 & Y3 & Y5 & R32).
    split; [rewrite RSV0e; lia|]. split; [lia|].
    pose proof (le4_of_bytes (b8 (byte_of res 0)) (b8 (byte_of res 1)) (b8 (byte_of res 2)) (b8 (byte_of res 3))) as L4.
    rewrite !b8_unsigned in L4 by (apply byte_of_range; lia). rewrite (u32_bytes res) in L4 by lia.
    split.
    + rewrite L4, EE.
      change [b8 (byte_of res 0); b8 (byte_of res 1); b8 (byte_of res 2); b8 (byte_of res 3)]
        with ([b8 (byte_of res 0)] ++ [b8 (byte_of res 1)] ++ [b8 (byte_of res 2)] ++ [b8 (byte_of res 3)]).
      apply bytes_at_app. split; [replace (r_base r + e - 4) with (r_base r + (e - 4)) by lia; exact (proj1 (HBy (e - 4) _ ltac:(lia) Y0))|].
      apply bytes_at_app. split; [replace (r_base r + e - 4 + Z.of_nat (length [b8 (byte_of res 0)])) with (r_base r + (e - 3)) by (cbn [length]; lia); exact (proj1 (HBy (e - 3) _ ltac:(lia) Y1))|].
      apply bytes_at_app. split.
      * replace (r_base r + e - 4 + Z.of_nat (length [b8 (byte_of res 0)]) + Z.of_nat (length [b8 (byte_of res 1)])) with (r_base r + (e - 2)) by (cbn [length]; lia).
        exact (proj1 (HBy (e - 2) _ ltac:(lia) Y2)).
      * replace (r_base r + e - 4 + Z.of_nat (length [b8 (byte_of res 0)]) + Z.of_nat (length [b8 (byte_of res 1)]) + Z.of_nat (length [b8 (byte_of res 2)])) with (r_base r + (e - 1)) by (cbn [length]; lia).
        exact (proj1 (HBy (e - 1) _ ltac:(lia) Y3)).
    + rewrite EE. replace (r_base r + e - 5) with (r_base r + (e - 5)) by lia. exact (proj1 (HBy (e - 5) _ ltac:(lia) Y5)).
  - rewrite RSVe, EE. unfold P. unfold res. lia.
  - rewrite RSVe, EE. destruct (Z.eq_dec res 0) as [E0|NE0].
    + rewrite E0, Z.sub_0_r. exact (proj1 (HBy e _ ltac:(lia) H0e)).
    + replace (r_base r + e - res) with (r_base r + (e - res)) by lia. exact (proj1 (HBy (e - res) _ ltac:(lia) (Kr0 ltac:(lia)))).
  - rewrite EE. exact (proj1 (HBy e _ ltac:(lia) H0e)).
  - exact NR.
  - rewrite EE. unfold P, po, e. lia.
  - unfold MMAP_THRESHOLD in MV2. lia.
Qed.
End WithCeiling0.
