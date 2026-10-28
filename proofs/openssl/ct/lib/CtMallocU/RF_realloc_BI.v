(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Znumtheory.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes Decode.
From OssFuzzTheorems.openssl.ct.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import F_malloc_free F_malloc_enframe MallocBlocks MallocHINV MallocFacts_B MallocFacts_A.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog MAlign.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocKit_A MallocKit_B MallocKit_B2 MallocModel_B MallocKit_B3 MallocFacts_Bpres F_mm_syscalls F_ntf F_free_C F_free_K F_free.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocFacts_inv MallocFacts_inv2 MallocFacts_inv3.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMallocKit_A RMallocKit_B RMallocKit_B2 RMallocKit_B3 RF_get_meta RF_mm_syscalls RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RF_free_A RF_free_B RF_free_C RF_ntf RF_free_K RF_free RF_realloc_A RF_realloc_B RF_realloc_BS RF_aligned_B RF_aligned_H RF_aligned_C RF_realloc_AS RF_realloc_AI.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import MI_Kit MI_Inv MI_Arith MI_Read MI_Pres2 MI_WFree MI_Geom.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.ZBridge.flia ::= first [ assumption | OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.ZBridge.slim; lia | lia ].
Local Ltac OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
Definition rrealloc_I_post (sp gp tp s7 s8 s9 s10 s11 ra0 s0v s1v s2v s3v s4v s5v s6v : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (st : mstate) (LB : list block) (blk : block) (off n : Z) : machine_state -> Prop :=
  fun ms' => exists (g : aptr) (i : Z) (r : region) (mR : mem) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    let P := blk_addr blk in
    let stride := get_stride (get_meta_rec st g) in
    let S := P - UNIT * off in let E := S + stride - IB in
    ms' = MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp + 64)) gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra0) fc None mR (seg_rom ctusegs)
    /\ s_slots st !! (blk_slot blk) = Some (g, i)
    /\ (s_regions st) !! (fst (blk_slot blk)) = Some r /\ r_kind r = RKGroup
    /\ (i = 0 \/ stride * (i + 1) < 2^20) /\ stride - UNIT * off - n < 2^32 /\ off <= 258
    /\ rmrep (fst (realign_at st g i n off 0)) mR /\ ticks_ok (fst (realign_at st g i n off 0))
    /\ wframe (raligned_W S P n E) (S - 3) (E - S + 3) m mR
    /\ r_base r + 16 <= S /\ E + 4 <= r_base r + round_up_pg (r_len r) /\ P + blk_size blk <= E /\ r_base r + round_up_pg (r_len r) <= alloc_ceiling
    /\ (r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0x355000 <= r_base r)
    /\ (forall b, In b LB -> blk_slot b <> blk_slot blk -> blk_addr b + blk_size b <= S - 4 \/ E <= blk_addr b).

Lemma rrealloc_hdr_spec_I : forall (ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (ra0 s0v s1v s2v s3v s4v s5v s6v : word) F fc m
    (st : mstate) (LB : list block) (blk : block) (off n : Z) L BL LS,
  CINV st LB -> In blk LB -> 0 <= off -> blk_addr blk = conc st (blk_slot blk) + UNIT * off ->
  INVL x0 st L BL LS -> CORR st LB BL ->
  rmrep st m -> ticks_ok st -> mem_inv ctusegs m -> c_init_done (ctx st) <> 0 ->
  bv_unsigned a1 = n -> 0 <= n <= blk_size blk -> n < MMAP_THRESHOLD ->
  (forall g i, s_slots st !! (blk_slot blk) = Some (g, i) ->
     m_sizeclass (get_meta_rec st g) <= size_to_class n + 1 /\ m_sizeclass (get_meta_rec st g) < 48) ->
  rw_cells ctusegs m (bv_unsigned sp) [C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra0] ->
  alloc_ceiling <= bv_unsigned sp -> bv_unsigned sp + 64 <= 2^64 ->
  evt ctusegs (rrealloc_I_post sp gp tp s7 s8 s9 s10 s11 ra0 s0v s1v s2v s3v s4v s5v s6v F fc m st LB blk off n)
      (MS (mkR ra sp gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 (blk_addr blk)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x2b4fb4) fc None m (seg_rom ctusegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until LS. intros C Hin OFF HA INV CR HMR TK MI INI HN NR NMM SCI FR CSP SPB.
  assert (N0 : 0 <= n) by (clear - NR; lia).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  (* [comment removed for export] *)
  destruct (MallocFacts_inv.Forall2_In_l _ _ _ _ CR Hin) as (k & Hk & (C1 & C2 & C3)).
  destruct k as [[ck bo] nk]. cbn [bslot boff bsize fst snd] in C1, C2, C3.
  assert (bo = off) as -> by (rewrite HA, <- C1 in C3; unfold UNIT in C3; lia).
  subst ck nk.
  (* [comment removed for export] *)
  pose proof (KINV_of_CINV _ _ C) as K0.
  pose proof (proj1 (List.Forall_forall _ _) (ci_blks _ _ C) blk Hin) as BK.
  destruct BK as [(g & i & b & SL & HB & FB & I & NFR & (off' & O0 & OA & OS & OK & HK)) NG SZ].
  assert (off' = off) as -> by (rewrite HA in OA; unfold UNIT in OA; lia).
  clear OA. destruct (SCI g i SL) as [SH1 SH2]. clear SCI.
  set (c0 := blk_slot blk) in *. set (n0 := blk_size blk) in *.
  pose proof (ci_gmetas _ _ C b g HB) as GO.
  destruct (go_region _ _ _ GO) as (r & Hr & Kr & B0 & B16 & SPAN & TOP).
  pose proof HMR as (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DJ & WA & WG).
  destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RF).
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
  unfold MallocFacts_B.sstart_of, sstart_of in SPAN. fold mr in SPAN. rewrite (go_mem _ _ _ GO) in SPAN. cbn [default id snd] in SPAN. fold stride in SPAN.
  (* [comment removed for export] *)
  pose proof (bf_shadow _ _ _ _ _ _ _ _ _ _ _ BF) as SHB. unfold blk_shadow_ok in SHB. cbn [bslot boff bsize fst snd] in SHB.
  rewrite (gbase_bm st c0 off n0 g b i ai a ar ka BF) in SHB.
  unfold MI_Inv.MR in SHB. fold mr in SHB. fold stride in SHB.
  destruct SHB as (K4 & K3 & K2 & K1 & Q & K5 & Kr0 & KU).
  pose proof (q16 st c0 off n0 g b i ai a ar ka BF) as [Q16 _]. unfold MI_Inv.MR in Q16. fold mr in Q16. fold stride in Q16.
  pose proof (bf_hdr0 _ _ _ _ _ _ _ _ _ _ _ BF) as H0. unfold MI_Inv.MR in H0. fold mr in H0.
  pose proof (bf_fit _ _ _ _ _ _ _ _ _ _ _ BF) as FIT. unfold MI_Inv.MR in FIT. fold mr in FIT. fold stride in FIT.
  unfold known, SHd in K4, K3, K2, K1, K5, Kr0, H0. cbn [fst snd] in K4, K3, K2, K1, K5, Kr0, H0.
  set (po := snd c0 + UNIT * off) in *.
  set (e := snd c0 + stride - IB) in *.
  set (res := e - po - n0) in *.
  set (q := (po - snd b - UNIT) / UNIT) in *.
  assert (RES0 : 0 <= res) by (subst res e po; unfold UNIT, IB in *; lia).
  cbn [aadd snd] in Q16. fold po in Q16. fold q in Q16.
  destruct (SH (fst c0) r Hr0 Kr) as [HWr HBy].
  rewrite Z.mul_add_distr_l, Z.mul_1_r in SIL.
  unfold OssFuzzTheorems.Proofs.openssl.ct.lib.Spec.Malloc.MCEIL in RBC.
  assert (PO16 : 16 <= po) by (subst po; unfold UNIT in *; lia).
  assert (EHIr : e + 4 <= round_up_pg (r_len r)) by (subst e; unfold UNIT, IB in *; lia).
  assert (POE : po + n0 + res = e) by (subst res; lia).
  (* [comment removed for export] *)
  set (b3 := i + 32 * Z.min res 5) in *.
  assert (IDXe : Z.land b3 31 = i) by (apply land31_idx; lia).
  set (P := r_base r + po).
  assert (PEQ : P = blk_addr blk) by (rewrite HA, Cc; unfold P, po; lia).
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
  destruct BC as [(r0 & Hr0' & _ & A16 & AEND & AL & UNK) _ _].
  fold c0 in Hr0'. rewrite Hr0 in Hr0'. inversion Hr0'. subst r0. clear Hr0' UNK.
  set (E := r_base r + e).
  set (Sa := r_base r + snd c0).
  assert (STRW : stride = (if (m_last_idx mr =? 0) && negb (m_maplen mr =? 0) then 4096 * m_maplen mr - 16 else 16 * size_class (m_sizeclass mr))).
  { unfold stride, get_stride. destruct ((m_last_idx mr =? 0) && negb (m_maplen mr =? 0)); unfold UNIT; lia. }
  pose proof (go_sc _ _ _ GO) as GSC. fold mr in GSC.
  pose proof (go_maplen _ _ _ GO) as GML. fold mr in GML.
  pose proof (go_avail _ _ _ GO) as GAV. pose proof (go_freed _ _ _ GO) as GFR. fold mr in GAV, GFR.
  pose proof (go_freeable _ _ _ GO) as GFB. fold mr in GFB.
  assert (NA : Z.testbit (m_avail mr) i = false) by (destruct (Z.testbit (m_avail mr) i) eqn:E1; [exfalso; apply NFR; right; exact E1| reflexivity]).
  assert (NF : Z.testbit (m_freed mr) i = false) by (destruct (Z.testbit (m_freed mr) i) eqn:E1; [exfalso; apply NFR; left; exact E1| reflexivity]).
  (* [comment removed for export] *)
  pose proof (bf_notH _ _ _ _ _ _ _ _ _ _ _ BF) as NH. pose proof (bf_c _ _ _ _ _ _ _ _ _ _ _ BF) as EC0. unfold MI_Inv.MR in EC0. fold mr in EC0.
  assert (HSTi : sstart mr i = snd c0) by (rewrite EC0; reflexivity).
  pose proof (sstart_succ st g i) as SS. unfold MI_Inv.MR in SS. fold mr in SS. fold stride in SS.
  assert (Hhosts : MI_Inv.hosts st b g) by (exists ai0; exact Hgh).
  assert (HiR : 0 <= i <= m_last_idx (MI_Inv.MR st g)) by (unfold MI_Inv.MR; fold mr; exact I).
  assert (NH' : s_groups st !! (fst b, sstart (MI_Inv.MR st g) i) = None) by (rewrite FB; unfold MI_Inv.MR; fold mr; rewrite HSTi, <- surjective_pairing; exact NH).
  assert (NOGRP : forall b' gh, s_groups st !! b' = Some gh -> fst b' = fst b -> snd b' + 9 <= snd c0 - 4 \/ e <= snd b').
  { intros b' gh Hb' Hf'. destruct (MallocFacts_inv2.hdr_hosts x0 st L BL LS INV b' gh Hb') as [m' Hm'].
    destruct (MallocFacts_inv3.sep_ghdr' x0 st L BL LS INV g b i m' b' Hhosts HiR NH' Hm' Hf') as [X|X];
      unfold MI_Inv.MR in X; fold mr in X; rewrite ?SS, ?HSTi in X; subst e; unfold IB; lia. }
  assert (NOBLK : forall b2, In b2 LB -> blk_slot b2 <> c0 -> blk_addr b2 + blk_size b2 <= Sa - 4 \/ E <= blk_addr b2).
  { intros b2 Hb2 NEb.
    destruct (MallocFacts_inv2.LB_geo x0 st L BL LS INV LB CR b2 Hb2) as (c2 & off2 & n2 & m2 & bm2 & i2 & r2 & Hk2 & C21 & C22 & Hm2 & Hi2 & Ec2 & NH2 & Hr2 & Kr2 & Ea2 & Ho2 & Hn2 & Fit2).
    pose proof (sstart_succ st m2 i2) as SS2.
    destruct (N.eq_dec (fst bm2) (fst b)) as [Ef|NEf].
    - rewrite Ef, Hr in Hr2. inversion Hr2. subst r2.
      assert (NE : m2 <> g \/ i2 <> i).
      { destruct (aptr_eq_dec m2 g) as [->|]; [right| now left]. intros ->. apply NEb. rewrite C21, Ec2, Ef, FB. fold mr. rewrite HSTi. destruct c0; reflexivity. }
      rewrite Ec2 in NH2.
      destruct (MI_Geom.sep_ext x0 st BL LS IM IG IS g b i Hhosts HiR NH' m2 bm2 i2 Hm2 Ef Hi2 NE NH2) as [X|X];
        rewrite Ea2, C22; clear - X SS SS2 Fit2 Hn2 Ho2 HSTi S16 SI0; subst E Sa e; unfold MI_Inv.MR, UNIT, IB in *; subst stride mr; lia.
    - pose proof (lr_lo_group r Kr) as LR. pose proof (lr_lo_group r2 Kr2) as LR2.
      pose proof (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) b2 Hb2) as BC2.
      destruct BC2 as [(r2' & Hr2' & _ & A16b & AENDb & _) _ _]. rewrite C21, Ec2 in Hr2'. cbn [fst] in Hr2'. rewrite Hr2 in Hr2'. inversion Hr2'. subst r2'. clear Hr2'.
      destruct (DJ _ _ _ _ Hr2 Hr0 ltac:(rewrite FB in NEf; exact NEf)) as [X|X]; rewrite ?LR, ?LR2 in X;
        clear - X A16b AENDb EHIr RB0 B0 SI0 Sc; subst E Sa e; unfold UNIT, IB in *; subst stride mr; lia. }
  (* [comment removed for export] *)
  destruct (MallocFacts_inv2.hosts_GO x0 st L BL LS INV b g Hhosts) as (aiG & _ & GOK).
  assert (Q20 : i = 0 \/ stride * (i + 1) < 2^20).
  { destruct (g_sc _ _ _ _ _ _ GOK) as [[Hsc48 _]|(_ & Hli0 & _)]; [| left; unfold MI_Inv.MR in Hli0; fold mr in Hli0; lia].
    right. destruct (g_stride _ _ _ _ _ _ GOK (proj2 Hsc48)) as (_ & _ & G20). unfold MI_Inv.MR, cnt_of in G20. fold mr in G20. fold stride in G20.
    clear - G20 SIL. lia. }
  assert (H0e : cell_read (get_shadow st (fst c0)) e = Known 0).
  { rewrite <- FB. replace e with (sstart mr (i + 1) - IB); [exact H0|].
    subst e. rewrite Sc. unfold sstart, gbase. rewrite (go_mem _ _ _ GO). cbn [default id snd]. fold stride. unfold UNIT, IB. clear; lia. }
  assert (RSV0e : Z.shiftr b3 5 = Z.min res 5) by (apply shiftr5_res; clear - I LI RES0; unfold MI_Inv.MR in *; lia).
  set (rsv := if 160 <=? b3 then res else Z.shiftr b3 5).
  assert (Ersv : rsv = (if 160 <=? b3 then res else Z.shiftr b3 5)) by reflexivity.
  assert (RSVe : rsv = res).
  { unfold rsv. rewrite RSV0e. destruct (Z.leb_spec 160 b3); [reflexivity|]. subst b3. clear - H RES0 I; lia. }
  assert (B3def : b3 = i + 32 * Z.min res 5) by reflexivity.
  clearbody rsv. clearbody q. clearbody b3.
  change (zopaqueP (i = 0 \/ stride * (i + 1) < 2 ^ 20)) in Q20.
  pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF) as OFF258.
  (* [comment removed for export] *)
  destruct (g_stride _ _ _ _ _ _ GOK ltac:(unfold MI_Inv.MR; fold mr; clear - SH2; lia)) as (_ & _ & G20).
  unfold MI_Inv.MR, cnt_of in G20. fold mr in G20. fold stride in G20.
  assert (LE1 : stride * 1 <= stride * (m_last_idx mr + 1)) by (apply Z.mul_le_mono_nonneg_l; clear - S16 LI; unfold UNIT in *; lia).
  assert (ST20 : stride < 2^20) by (clear - G20 LE1; lia).
  assert (EPS : e - po <= stride - 4) by (subst e po; clear - OFF S16; unfold UNIT, IB in *; lia).
  assert (N0E : n0 <= e - po) by (clear - POE RES0; lia).
  clear IR IA IM IL IG IS ISH K4 K2 K1 KU H0 CX GL AR GR WA WG Hres DJ NH NH' EC0 HSTi SS HiR GOK Har Hchk Hal Em Hrg RBALg RL0g Hm LO HI AAL ANG.
  unfold UNIT, IB in *.
  (* [comment removed for export] *)
  rewrite <- PEQ.
  eapply evt_mono.
  { eapply rrealloc_hdr_walk_eq_I with (P:=P) (G:=conc st g) (B:=conc st b) (A:=conc st a) (n:=n) (b3:=b3) (off16:=q)
       (avail:=m_avail mr) (freed:=m_freed mr) (last_idx:=m_last_idx mr) (freeable:=m_freeable mr) (sc:=m_sizeclass mr) (maplen:=m_maplen mr)
       (secret:=(c_secret (ctx st) + bv_unsigned rr_secret) mod 2^64) (r32:=res) (prev:=pw st (m_prev mr)) (next:=pw st (m_next mr))
       (stride:=stride) (E:=E) (rsv:=rsv).
    - exact STRW.
    - subst E e. rewrite IDXe, Cb, Sc. clear - CEIL_RANGE__; lia.
    - exact Ersv.
    - rewrite unsigned_lit; [reflexivity|]. subst E. unfold P. clear - RB0 PO16 N0E RES0 POE EHIr RBC SZ NR CEIL_RANGE__; lia.
    - exact HN.
    - rewrite PEQ. exact AL.
    - clear - Q16 SI0 OFF RB0 B0 Sc; lia.
    - clear - POE RES0 SZ EHIr RBC PO16 CEIL_RANGE__; lia.
    - rewrite Cb. clear - Q16 Sc; lia.
    - exact HAa.
    - rewrite HG. unfold AREA_HDR, META_SIZE in *. clear - RB0g A00 Hka; lia.
    - rewrite HG. unfold AREA_HDR, META_SIZE, NSLOTS in *. clear - RB0g A00 A01 Hka RBCg RUG CEIL_RANGE__; lia.
    - replace (P - 4) with (r_base r + (po - 4)) by (clear - CEIL_RANGE__; lia). exact R4.
    - replace (P - 3) with (r_base r + (po - 3)) by (clear - CEIL_RANGE__; lia). exact R3.
    - replace (P - 2) with (r_base r + (po - 2)) by (clear - CEIL_RANGE__; lia). exact R2.
    - exact RG.
    - exact MM.
    - exact RA.
    - exact RC.
    - intros Hlt. apply rsize_classes_read; [exact MI| clear - Hlt GSC; lia].
    - exact B3R.
    - exact Q.
    - exact GAV.
    - exact GFR.
    - apply rsec_range.
    - clear - LI; lia.
    - clear - GFB; lia.
    - clear - GSC; lia.
    - clear - GML; lia.
    - rewrite IDXe. clear - I; lia.
    - rewrite IDXe. exact NA.
    - rewrite IDXe. exact NF.
    - intros Hsc. rewrite IDXe.
      destruct (bf_sc _ _ _ _ _ _ _ _ _ _ _ BF) as [(Hsc0 & Hle & Hst)| E63]; [| unfold MI_Inv.MR in E63; fold mr in E63; clear - Hsc E63; lia].
      unfold MI_Inv.MR in Hle, Hst. fold mr in Hle, Hst. fold stride in Hle, Hst.
      pose proof (size_class_bound _ Hsc0) as SB. unfold MI_Inv.MR in SB. fold mr in SB.
      assert (A1 : stride = 16 * size_class (m_sizeclass mr) \/ m_last_idx mr = 0) by tauto.
      assert (B1 : stride <= 16 * size_class (m_sizeclass mr) \/ 292 <= size_class (m_sizeclass mr)).
      { destruct Hle as [Hle|H28]; [left; exact Hle| right; apply size_class_28; clear - H28 Hsc0 Hsc; lia]. }
      exact (guard16_arith _ _ _ _ _ _ _ (proj1 SB) Q16 FIT SZ OFF258 I A1 B1).
    - intros Hsc. clear - Hsc SH2; lia.
    - intros Hml. destruct (TOP Hml) as [B00 TOPE].
      pose proof (guard17_arith stride i off n0 q (m_last_idx mr) (m_maplen mr) S16 Q16 FIT SZ OFF I ltac:(clear - B00 TOPE SPAN; lia)) as G17.
      replace (m_maplen mr * 4096 / 16) with (m_maplen mr * 256) in G17
        by (clear - CEIL_RANGE__; rewrite <- (Z.div_mul (m_maplen mr * 256) 16) by lia; f_equal; lia).
      exact G17.
    - intros _. exact SH2.
    - exact S16.
    - rewrite Cb. clear - RB0 B0; lia.
    - subst E. unfold P. clear - N0E RES0 POE NR; lia.
    - subst E. clear - EHIr RBC CEIL_RANGE__; lia.
    - intros H160. assert (R5 : 5 <= res) by (rewrite B3def in H160; clear - H160 I LI RES0; unfold MI_Inv.MR in *; lia).
      destruct (K5 R5) as (Y0 & Y1 & Y2 & Y3 & Y5 & R32).
      split; [rewrite RSV0e; clear - R5; lia|]. split; [clear - R5 R32; lia|].
      pose proof (le4_of_bytes (b8 (byte_of res 0)) (b8 (byte_of res 1)) (b8 (byte_of res 2)) (b8 (byte_of res 3))) as L4.
      rewrite !b8_unsigned in L4 by (apply byte_of_range; lia). rewrite (u32_bytes res) in L4 by lia.
      split.
      + rewrite L4. subst E.
        change [b8 (byte_of res 0); b8 (byte_of res 1); b8 (byte_of res 2); b8 (byte_of res 3)]
          with ([b8 (byte_of res 0)] ++ [b8 (byte_of res 1)] ++ [b8 (byte_of res 2)] ++ [b8 (byte_of res 3)]).
        apply bytes_at_app. split; [replace (r_base r + e - 4) with (r_base r + (e - 4)) by lia; exact (proj1 (HBy (e - 4) _ ltac:(lia) Y0))|].
        apply bytes_at_app. split; [replace (r_base r + e - 4 + Z.of_nat (length [b8 (byte_of res 0)])) with (r_base r + (e - 3)) by (cbn [length]; lia); exact (proj1 (HBy (e - 3) _ ltac:(lia) Y1))|].
        apply bytes_at_app. split.
        * replace (r_base r + e - 4 + Z.of_nat (length [b8 (byte_of res 0)]) + Z.of_nat (length [b8 (byte_of res 1)])) with (r_base r + (e - 2)) by (cbn [length]; lia).
          exact (proj1 (HBy (e - 2) _ ltac:(lia) Y2)).
        * replace (r_base r + e - 4 + Z.of_nat (length [b8 (byte_of res 0)]) + Z.of_nat (length [b8 (byte_of res 1)]) + Z.of_nat (length [b8 (byte_of res 2)])) with (r_base r + (e - 1)) by (cbn [length]; lia).
          exact (proj1 (HBy (e - 1) _ ltac:(lia) Y3)).
      + subst E. replace (r_base r + e - 5) with (r_base r + (e - 5)) by lia. exact (proj1 (HBy (e - 5) _ ltac:(lia) Y5)).
    - rewrite RSVe. subst E. unfold P. clear - RES0 POE N0E NR; lia.
    - rewrite RSVe. subst E. destruct (Z.eq_dec res 0) as [E0|NE0].
      + rewrite E0, Z.sub_0_r. exact (proj1 (HBy e _ ltac:(lia) H0e)).
      + replace (r_base r + e - res) with (r_base r + (e - res)) by lia. exact (proj1 (HBy (e - res) _ ltac:(lia) (Kr0 ltac:(lia)))).
    - subst E. exact (proj1 (HBy e _ ltac:(lia) H0e)).
    - exact FR.
    - exact SPB.
    - (* [comment removed for export] *)
      destruct HWr as (_ & _ & HW). subst E. unfold P. split; [clear - RB0 PO16; lia|]. split; [clear - EHIr RBC CEIL_RANGE__; lia|].
      intros j Hj. replace (r_base r + po - 3 + j) with (r_base r + (po - 3 + j)) by (clear - CEIL_RANGE__; lia).
      apply HW. clear - Hj PO16 EHIr POE RES0; lia.
    - replace (P - 3) with (r_base r + (po - 3)) by (clear - CEIL_RANGE__; lia). exact (proj1 (HBy (po - 3) b3 ltac:(clear - PO16 EHIr POE RES0 SZ; lia) K3)).
    - reflexivity.
    - unfold P. clear - PO16 RB0; lia.
    - left. subst E. clear - EHIr RBC CSP; lia.
    - clear - NMM; unfold MMAP_THRESHOLD in *; lia.
    - subst E. unfold P. clear - EPS ST20; lia.
    - clear - NR N0 N0E EPS ST20; lia.
    - subst E. unfold P. clear - NR N0E; lia.
    - exact SH1.
    - exact SH2.
    - exact MI. }
  (* [comment removed for export] *)
  cbv beta. intros ms' RP. unfold rrealloc_ret_post in RP.
  destruct RP as (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & ->).
  unfold rrealloc_I_post.
  exists g, i, r. eexists. exists x5, x6, x7, x11, x12, x13, x14, x15, x16, x17, x28, x29, x30, x31.
  cbv zeta. unfold UNIT, IB. rewrite <- ?PEQ. fold mr. fold stride.
  replace (P - 16 * off) with Sa by (unfold P; clear - Sc CEIL_RANGE__; lia).
  replace (Sa + stride - 4) with E by (clear - CEIL_RANGE__; subst E e; lia).
  split. { reflexivity. }
  split; [exact SL|]. split; [exact Hr0|]. split; [exact Kr|].
  split; [exact Q20|]. split; [clear - ST20 OFF N0; lia|]. split; [clear - OFF258; lia|].
  (* [comment removed for export] *)
  pose proof (realign_rep st m g b r i n off 0 b3 HMR TK (go_mem _ _ _ GO) Hr Kr B0 S16 SI0 ltac:(clear - I LI; unfold MI_Inv.MR in *; lia) ltac:(clear - EHIr Sc; try subst stride; try subst mr; lia)
                OFF ltac:(clear; lia) ltac:(left; reflexivity) N0 ltac:(clear - FIT NR N0 POE RES0 Sc; try subst stride; try subst mr; lia)
                ltac:(clear - ST20 OFF N0; try subst stride; try subst mr; lia) Q20
                ltac:(clear - OFF258; lia) (proj1 B3R) IDXe
                ltac:(intros b' gh Hb' Hf'; destruct (NOGRP b' gh Hb' Hf') as [X|X]; [left| right]; clear - X Sc; try subst stride; try subst mr; lia)) as [MRR TKR].
  fold mr in MRR. fold stride in MRR. rewrite <- !Sc in MRR.
  unfold raligned_mem in MRR. cbn [Z.eqb] in MRR.
  replace (r_base r + (snd c0 + 16 * off)) with P in MRR by (unfold P; clear - CEIL_RANGE__; lia).
  replace (r_base r + (snd c0 + stride - 4)) with E in MRR by (clear - CEIL_RANGE__; subst E e; lia).
  split; [exact MRR|]. split; [exact TKR|].
  split.
  { destruct HWr as (_ & _ & HW).
    apply wframe_rss; [| unfold P; clear - OFF Sc; subst Sa; lia| clear - NR N0E POE RES0; subst E; unfold P; lia| exact N0].
    split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI|].
    subst Sa E e. split; [clear - RB0 B0 SI0 Sc; lia|]. split; [clear - EHIr RBC CEIL_RANGE__; lia|].
    intros j Hj. replace (r_base r + snd c0 - 3 + j) with (r_base r + (snd c0 - 3 + j)) by (clear - CEIL_RANGE__; lia).
    apply HW. clear - Hj B0 SI0 Sc EHIr S16; lia. }
  split; [clear - B0 SI0 Sc; subst Sa; lia|].
  split; [clear - EHIr; subst E; lia|]. split; [fold n0; clear - POE RES0; subst E; unfold P; lia|]. split; [exact RBC|].
  split.
  { pose proof (rregion_addr_facts st m (fst c0) r HMR Hr0) as (_ & _ & _ & RI). apply RI. clear - EHIr PO16 POE RES0 SZ; lia. }
  exact NOBLK.
Qed.
End WithCeiling0.
