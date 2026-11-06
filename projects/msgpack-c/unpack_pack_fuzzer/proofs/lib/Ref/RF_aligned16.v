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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ref Require Import RF_aligned16_W.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require A_MallocFacts_inv A_MallocFacts_inv2 A_MallocFacts_inv3.

Set Keyed Unification.
Import ListNotations.
Import ITree.Exc.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import CeilLia.
Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Definition RALIGNED16_SYM : Z := 0x47ec4.
Definition RALIGNED16_STACK : Z := RMALLOC_STACK + 32.

Definition RMREPL : Z := 0x87b38.

Definition raligned16_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (n lo B : Z) (errv : word),
  RHEAP s LB m ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RALIGNED16_STACK ->
  rw_cells rsegs m (errno_addr tp) [C4 errv] ->
  mem_inv rsegs m ->
  tp = Z_to_bv 64 RATP ->
  rw_cells rsegs m RMREPL [C4 (wz 0)] ->
  a0 = Z_to_bv 64 16 -> a1 = Z_to_bv 64 n -> 0 <= n < 2^48 ->
  implM rsegs (raw_malloc n) s
        (rmalloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RALIGNED16_SYM) fc None m (seg_rom rsegs)).

Lemma bytes_at_4 m a (x0 x1 x2 x3 : byte) :
  bytes_at rsegs m a [x0] -> bytes_at rsegs m (a + 1) [x1] -> bytes_at rsegs m (a + 2) [x2] -> bytes_at rsegs m (a + 3) [x3] ->
  bytes_at rsegs m a [x0; x1; x2; x3].
Proof.
  intros (A0 & _ & B0) (_ & _ & B1) (_ & _ & B2) (_ & A3 & B3). split; [exact A0|]. split; [cbn in *; lia|].
  intros k Hk. cbn in Hk.
  destruct k as [|[|[|[|k]]]]; cbn [nth_error].
  - exact (B0 0%nat ltac:(cbn; lia)).
  - specialize (B1 0%nat ltac:(cbn; lia)). cbn [nth_error Z.of_nat] in B1. rewrite <- B1. f_equal. f_equal. lia.
  - specialize (B2 0%nat ltac:(cbn; lia)). cbn [nth_error Z.of_nat] in B2. rewrite <- B2. f_equal. f_equal. lia.
  - specialize (B3 0%nat ltac:(cbn; lia)). cbn [nth_error Z.of_nat] in B3. rewrite <- B3. f_equal. f_equal. lia.
  - lia.
Qed.

Lemma raligned_tail_spec :
  forall (ra1 sp gp tp x5 x6 x7 a1v a2v a3v a4v a5v a6v a7v s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 t4 t5 t6 rav s0v s1v : word)
         (junk : list byte) (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (st : mstate) (LB0 : list block) (bp : bptr) (n A : Z),
  rmrep st m -> mem_inv rsegs m -> AREACH_from ref_reserved st LB0 -> In (bp, A, n) LB0 -> rslack (strip st) (fst bp) A n ->
  0 <= n < 2^48 -> bv_unsigned sp + 32 <= 2^64 ->
  rw_cells rsegs m (bv_unsigned sp) [CB 8 junk; C8 s1v; C8 s0v; C8 rav] ->
  evt rsegs (raligned_tail_post sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 rav s0v s1v (Z_to_bv 64 A) F fc m)
      (MS (mkR ra1 sp gp tp x5 x6 x7 (Z_to_bv 64 16) (Z_to_bv 64 n) (Z_to_bv 64 A) a1v a2v a3v a4v a5v a6v a7v
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 t4 t5 t6)
          F (Z_to_bv 64 0x47f64) fc None m (seg_rom rsegs)).
Proof.
  intros until A. intros RMR MI AR Hb RSL HN SPH FR.
  pose proof RMR as (WF & CX & GL & ARS & GR & SH). pose proof WF as (Hres & WR & DISJ & WA & WG).
  destruct (A_MallocFacts_inv.areach_inv _ _ _ AR) as (L & LS & BL & INV & _ & _ & _ & CR).
  pose proof (A_MallocFacts_inv3.areach_cinv_proof _ _ AR) as C.
  destruct (A_MallocFacts_inv.Forall2_In_l _ _ _ _ CR Hb) as (k & Hk & (C1 & C2 & C3)).
  destruct k as [[c off] n']. cbn [bslot boff bsize blk_slot blk_size blk_addr fst snd] in C1, C2, C3. subst n'.
  assert (C1' : fst bp = c) by exact C1.
  destruct (block_facts x0 st L BL LS INV c off n Hk) as (mm & bm & i & ai & a & ar & ka & BF).
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).

  pose proof (bf_slot _ _ _ _ _ _ _ _ _ _ _ BF) as SL. pose proof (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF) as HG.
  pose proof (bf_mem _ _ _ _ _ _ _ _ _ _ _ BF) as HM. pose proof (bf_c _ _ _ _ _ _ _ _ _ _ _ BF) as EC.
  pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF) as Hi. pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF) as Hoff.
  pose proof (bf_n _ _ _ _ _ _ _ _ _ _ _ BF) as Hn. pose proof (bf_fit _ _ _ _ _ _ _ _ _ _ _ BF) as FIT.
  pose proof (bf_stride _ _ _ _ _ _ _ _ _ _ _ BF) as [S1 S2]. pose proof (bf_b16 _ _ _ _ _ _ _ _ _ _ _ BF) as [Bb0 Bb16].
  pose proof (bf_notA _ _ _ _ _ _ _ _ _ _ _ BF) as NA. pose proof (bf_notF _ _ _ _ _ _ _ _ _ _ _ BF) as NF. unfold tbit in NA, NF.
  pose proof (bf_top _ _ _ _ _ _ _ _ _ _ _ BF) as TOP.
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
  set (res := e - po - n) in *.

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

  destruct RSL as (g2 & i2 & SL2 & RES). rewrite C1' in SL2, RES. change (s_slots (strip st)) with (s_slots st) in SL2. rewrite SL in SL2.
  assert (g2 = mm) as -> by congruence. clear SL2 i2.
  change (conc (strip st) c) with (conc st c) in RES. change (get_meta_rec (strip st) mm) with mr in RES. fold stride in RES.

  assert (HA : A = r_base r + po) by (subst po; rewrite C3, CC; unfold UNIT; clear; lia).
  assert (HE : e = snd bm + 16 + stride * i + stride - IB) by (subst e; rewrite SC'; clear; lia).
  assert (HPO : po = snd bm + 16 + 16 * q) by (subst po; rewrite SC'; clear - Q1; unfold UNIT in *; lia).
  assert (RESE : res = r_base r + e - A - n) by (subst res; rewrite HA; clear; lia).
  assert (RES31 : 0 <= res < 2^31) by (rewrite RESE, HE; rewrite CC, SC' in RES; unfold IB in *; clear - RES; lia).
  assert (AL : A mod 16 = 0) by (rewrite HA; clear - PM16 RBAL; Z.div_mod_to_equations; lia).
  assert (FIT' : po + n <= e) by (subst po e; unfold UNIT, IB in *; clear - FIT; lia).
  assert (PO16 : 16 <= po) by (rewrite HPO; clear - Bb0 Q2; lia).
  pose proof (round_up_pg_ge (r_len r)) as RUP.
  pose proof (rreserved_disjoint1 _ _ RF ltac:(clear - EHI' FIT' PO16 Hn; unfold IB in EHI'; lia)) as DRr.
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

  assert (K4' : cell_read (get_shadow st (fst bm)) (po - 4) = Known 0) by (rewrite <- FC; exact K4).
  assert (K3' : cell_read (get_shadow st (fst bm)) (po - 3) = Known (i + 32 * Z.min res 5)) by (rewrite <- FC; exact K3).
  assert (K2' : cell_read (get_shadow st (fst bm)) (po - 2) = Known (byte_of q 0)) by (rewrite <- FC; exact K2).
  assert (K1' : cell_read (get_shadow st (fst bm)) (po - 2 + 1) = Known (byte_of q 1)) by (rewrite <- FC; replace (po - 2 + 1) with (po - 1) by (clear; lia); exact K1).
  destruct (rmrep_shadow_read st m (fst bm) r (po - 4) 0 RMR Hr Kr' ltac:(clear - PO16 FIT' EHI' Hn; unfold IB in *; lia) K4') as [R4 _].
  destruct (rmrep_shadow_read st m (fst bm) r (po - 3) _ RMR Hr Kr' ltac:(clear - PO16 FIT' EHI' Hn; unfold IB in *; lia) K3') as [R3 B3R].
  destruct (rmrep_shadow_read2 st m (fst bm) r (po - 2) _ _ RMR Hr Kr' ltac:(clear - PO16; lia) ltac:(clear - PO16 FIT' EHI' Hn; unfold IB in *; lia) K2' K1') as (R2 & LO8 & HI8).
  rewrite <- le2_lohi, (u16_bytes q Q2) in R2 by assumption.
  replace (r_base r + (po - 4)) with (A - 4) in R4 by (clear - HA; lia).
  replace (r_base r + (po - 3)) with (A - 3) in R3 by (clear - HA; lia).
  replace (r_base r + (po - 2)) with (A - 2) in R2 by (clear - HA; lia).
  destruct (rmrep_group_read st m bm _ RMR HG) as [RG _]. cbn [g_meta pw oconc] in RG.
  pose proof (rmrep_meta_chunk st m mm RMR MSL) as MM. change (get_meta_rec st mm) with mr in MM. unfold meta_cells in MM. rewrite HM in MM. cbn [pw oconc] in MM. unfold meta_word in MM.
  pose proof (rmrep_area_check_read st m a ar RMR Ha) as RA. rewrite Hck in RA. change (c_secret (s_ctx st)) with (c_secret (ctx st)) in RA.
  replace (conc st a) with (conc st mm - conc st mm mod 4096) in RA by (rewrite <- HAR, Emm, (area_of_mslot a ka Hal Hka); reflexivity).
  pose proof (rmrep_ctx_secret_read st m RMR) as RC.

  assert (RDB : forall o v, cell_read (get_shadow st (fst c)) o = Known v -> 0 <= o < round_up_pg (r_len r) -> bytes_at rsegs m (r_base r + o) [b8 v]).
  { intros o v Ho Hor. rewrite FC in Ho. exact (proj1 (RDr o v Hor Ho)). }
  assert (B3AT : bytes_at rsegs m (A - 3) [b8 (i + 32 * Z.min res 5)]).
  { replace (A - 3) with (r_base r + (po - 3)) by (clear - HA; lia). apply RDB; [exact K3| clear - PO16 FIT' EHI' Hn; unfold IB in *; lia]. }
  assert (RB0 : 0 < res -> bytes_at rsegs m (r_base r + e - res) [b8 0]).
  { intros Hr0. replace (r_base r + e - res) with (r_base r + (e - res)) by (clear; lia). apply RDB; [exact (Kr Hr0)| clear - PO16 FIT' EHI' Hn Hr0 RESE HA; unfold IB in *; lia]. }
  assert (RB5 : 5 <= res -> bytes_at rsegs m (r_base r + e - 5) [b8 0] /\ bytes_at rsegs m (r_base r + e - 4) (le4 (wz res))).
  { intros Hr5. destruct (K5 Hr5) as (E0 & E1 & E2 & E3 & E5 & R32). split.
    - replace (r_base r + e - 5) with (r_base r + (e - 5)) by (clear; lia). apply RDB; [exact E5| clear - PO16 FIT' EHI' Hn Hr5; unfold IB in *; lia].
    - rewrite le4_bytes by (clear - RES31; lia).
      rewrite <- (byte_of_0 res), <- (byte_of_1 res), <- (byte_of_2 res) by (clear - RES31; lia).
      replace (res / 16777216) with (byte_of res 3) by (rewrite byte_of_3 by (clear - RES31; lia); apply Z.mod_small; clear - RES31; Z.div_mod_to_equations; lia).
      apply bytes_at_4.
      + replace (r_base r + e - 4) with (r_base r + (e - 4)) by (clear; lia). apply RDB; [exact E0| clear - PO16 FIT' EHI' Hn Hr5; unfold IB in *; lia].
      + replace (r_base r + e - 4 + 1) with (r_base r + (e - 3)) by (clear; lia). apply RDB; [exact E1| clear - PO16 FIT' EHI' Hn Hr5; unfold IB in *; lia].
      + replace (r_base r + e - 4 + 2) with (r_base r + (e - 2)) by (clear; lia). apply RDB; [exact E2| clear - PO16 FIT' EHI' Hn Hr5; unfold IB in *; lia].
      + replace (r_base r + e - 4 + 3) with (r_base r + (e - 1)) by (clear; lia). apply RDB; [exact E3| clear - PO16 FIT' EHI' Hn Hr5; unfold IB in *; lia]. }
  assert (WRX : forall x k, r_base r <= x -> x + k <= r_base r + round_up_pg (r_len r) -> 0 <= k -> wr_at rsegs m x k).
  { intros x kk H1 H2 H3. replace x with (r_base r + (x - r_base r)) by (clear; lia). eapply wr_at_sub; [exact WRr| clear - H1 H2 H3; lia| clear - H1 H2 H3; lia]. }
  pose proof (bf_sc _ _ _ _ _ _ _ _ _ _ _ BF) as BSC. fold mr in BSC. fold stride in BSC.
  apply (tail_a9c ra1 sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 rav s0v s1v junk F fc m
           A n (conc st mm) (conc st bm) (conc st mm - conc st mm mod 4096) stride i res q
           (m_avail mr) (m_freed mr) (m_last_idx mr) (m_freeable mr) (m_sizeclass mr) (m_maplen mr) (c_secret (ctx st))
           (pw st (m_prev mr)) (pw st (m_next mr))).
  - exact HN.
  - exact FR.
  - clear - HA RrB0 PO16. lia.
  - exact AL.
  - clear - HA HPO Bb0 RrB0. lia.
  - clear - HA FIT' EHI' RBC Hn RUP. unfold IB in *. lia.
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
  -
    intros Hlt. destruct BSC as [(Hsc & Hle & Hst)| E63]; [| clear - Hlt E63; lia].
    pose proof (size_class_bound _ Hsc) as SB.
    assert (A' : stride = 16 * size_class (m_sizeclass mr) \/ m_last_idx mr = 0) by (clear - Hst; unfold UNIT in Hst; tauto).
    assert (B' : stride <= 16 * size_class (m_sizeclass mr) \/ 292 <= size_class (m_sizeclass mr)).
    { destruct Hle as [Hle|H28]; [left; unfold UNIT in Hle; exact Hle| right; apply size_class_28; clear - H28 Hsc; lia]. }
    clear - SB Q1 FIT Hn Hoff Hi A' B'. unfold UNIT, IB in *.
    exact (guard16_arith _ _ _ _ _ _ _ (proj1 SB) Q1 FIT Hn Hoff Hi A' B').
  - clear - GSC. lia.
  -
    intros NM. destruct (TOP NM) as [B0 GE]. unfold gend, cnt_of, sstart in GE. rewrite (gbase_bm _ _ _ _ _ _ _ _ _ _ _ BF), B0 in GE.
    fold mr in GE. fold stride in GE.
    replace (m_maplen mr * 256) with (m_maplen mr * 4096 / 16) by (rewrite <- (Z.div_mul (m_maplen mr * 256) 16) by lia; f_equal; lia).
    clear - S1 Q1 FIT Hn Hoff Hi GE. unfold UNIT, IB in *.
    eapply (guard17_arith stride i off n q); try eassumption; lia.
  -
    intros Hd. destruct GSC as [Hsc|(E63 & L0 & MLn)]; [| exfalso; clear - Hd L0 MLn; lia].
    split; [clear - Hsc; lia|]. subst stride. unfold get_stride.
    destruct Hd as [Hd|Hd]; [rewrite (proj2 (Z.eqb_eq _ _) Hd), andb_false_r; reflexivity| rewrite (proj2 (Z.eqb_neq _ _) Hd); reflexivity].
  - intros [L0 MLn]. subst stride. unfold get_stride. rewrite (proj2 (Z.eqb_eq _ _) L0). replace (m_maplen mr =? 0) with false by (symmetry; apply Z.eqb_neq; exact MLn). reflexivity.
  - exact RES31.
  - clear - RESE HE CB. unfold IB in *. lia.
  - clear - DRr EHI' HA PO16 HE CB FIT' Hn. unfold IB in *. lia.
  - clear - EHI' HE CB RBC RUP. unfold IB in *. lia.
  - exact B3AT.
  - apply WRX; clear - HA PO16 FIT' EHI' RUP Hn; unfold IB in *; lia.
  - intros H. replace (conc st bm + 16 + stride * (i + 1) - 4 - res) with (r_base r + e - res) by (clear - HE CB; unfold IB in *; lia). exact (RB0 H).
  - intros H. apply WRX; clear - H HA PO16 FIT' EHI' RUP Hn HE CB RESE; unfold IB in *; lia.
  - intros H. replace (conc st bm + 16 + stride * (i + 1) - 4 - 5) with (r_base r + e - 5) by (clear - HE CB; unfold IB in *; lia).
    replace (conc st bm + 16 + stride * (i + 1) - 4 - 4) with (r_base r + e - 4) by (clear - HE CB; unfold IB in *; lia). exact (RB5 H).
  - intros H. apply WRX; clear - H HA PO16 FIT' EHI' RUP Hn HE CB RESE; unfold IB in *; lia.
Qed.

Lemma rheap_pres_stackframe s LB (sp : Z) m m1 :
  RHEAP s LB m -> munch [(sp - 32, sp)] m m1 -> wmono rsegs m m1 -> alloc_ceiling <= sp - 32 -> rheap_pres LB sp m m1.
Proof.
  intros HP MU WM LO.
  assert (PE : rpres_except (fun a => sp - 32 <= a < sp) m m1).
  { eapply rpres_except_of_munch'; [exact MU| exact WM|]. intros lo hi [E|[]] x Hx. inversion E; subst. exact Hx. }
  intros a Ha HC. apply PE; [exact Ha|]. intros HX.
  destruct HC as [HC|[[HC _]|(b & Hb & Hab)]]; [lia| pose_ceil; lia|].
  pose proof (RHEAP_block_range_proof s LB m b HP Hb) as (_ & _ & _ & R4 & _). lia.
Qed.

Lemma rauxcell_pres_stackframe (sp : Z) m m1 : munch [(sp - 32, sp)] m m1 -> alloc_ceiling <= sp - 32 -> rauxcell_pres m m1.
Proof.
  intros MU LO a Ha. apply MU. rewrite wa_unsigned by (unfold RAUXV_CELL in Ha; lia). cbn. pose_ceil; unfold RAUXV_CELL in *. lia.
Qed.

Section P.
Hypothesis HIMPL : rmalloc_impl_stmtX.

Theorem raligned16_spec_proof : raligned16_stmt.
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB n lo B errv.
  intros HEAP AUXB SB ST CLO LO ERR MI TP REPL HA0 HA1 HN.
  unfold RALIGNED16_STACK, RMALLOC_STACK in LO. unfold RALIGNED16_SYM. unfold RMREPL in REPL. subst a0 a1.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof CLO as CLOv. pose_ceil.
  assert (ETP : bv_unsigned tp + -164 = 422892) by (rewrite TP; unfold RATP; rewrite unsigned_lit by lia; reflexivity).
  rewrite ETP in ERR.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  unfold implM. iprefix.
  carve_frame 32%nat ST.

  step. step. step. step.

  step. step. step. if_false. step. step. if_false.
  step. step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. { exfalso. clear - K HN. lia. } clear K.

  step. step. step. if_true.

  step. step. if_false. step. step. step. step. step. step.
  apply evt_done. replace (Z_to_bv 64 (16 + n + -16)) with (Z_to_bv 64 n) by (f_equal; lia).

  lazymatch goal with |- impl _ _ _ _ (MS _ _ _ _ _ ?mX _) => rename mX into m1 end.
  assert (HEAP1 : RHEAP s LB m1).
  { eapply RHEAP_frame_proof; [exact HEAP| exact MU| exact WM|]. constructor; [| constructor]. left. cbn [fst]. lia. }
  assert (AUX1 : rauxv_ok m1 B).
  { eapply rauxv_ok_frame; [exact AUXB| exact MU| exact WM|]. constructor; [| constructor]. cbn [fst snd]. unfold RAUXV_CELL, RLIBC. lia. }
  pose proof (rheap_pres_stackframe s LB (bv_unsigned sp) m m1 HEAP ltac:(replace (bv_unsigned sp - 32) with (bv_unsigned sp + -32) by lia; exact MU) WM ltac:(lia)) as PRES1.
  pose proof (rauxcell_pres_stackframe (bv_unsigned sp) m m1 ltac:(replace (bv_unsigned sp - 32) with (bv_unsigned sp + -32) by lia; exact MU) ltac:(lia)) as AUXC1.
  clear MU WM.
  set (sp1 := Z_to_bv 64 (bv_unsigned sp + -32)) in *.
  assert (SP1 : bv_unsigned sp1 = bv_unsigned sp + -32) by (subst sp1; apply unsigned_lit; lia).

  eapply impl_post_evt.
  { pose proof HIMPL as X. unfold rmalloc_impl_stmtX, implM, rmalloc_entry in X.
    eapply X with (lo := lo) (B := B) (errv := errv); clear X; rewrite ?SP1.
    all: first [exact HEAP1| exact AUX1| exact ST| exact MI| exact TP| exact HN| reflexivity| unfold RMALLOC_STACK; lia| rewrite ETP; exact ERR]. }
  cbv beta. intros [|[r s']] ms' PO; [apply evt_done; exact I|]. cbn [epost fst snd] in PO |- *.
  destruct PO as (w0 & w1 & w2 & ra0 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & m' & errv' & -> & MI' & ST' & ERR' & AUX' & AUXC & PRES & EFA & ESO & RR).
  rewrite SP1 in ST', PRES.
  replace (ret_pc (Z_to_bv 64 294756)) with (Z_to_bv 64 294756) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

  apply (rheap_pres_rw_cells _ _ _ _ _ _ PRES) in FR; [| left; lia].
  assert (PRES2 : rheap_pres LB (bv_unsigned sp) m m').
  { eapply rheap_pres_trans; [exact PRES1|]. eapply rheap_pres_weaken; [exact PRES| lia| auto]. }
  assert (AUXC2 : rauxcell_pres m m') by (eapply rauxcell_pres_trans; [exact AUXC1| exact AUXC]).
  clear PRES1 AUXC1 HEAP1 AUX1 ERR REPL MI.
  destruct r as [p|].
  -
    destruct RR as (A & bj & -> & BR & HEAP2 & BLK & EXPO & RSL).
    pose proof HEAP2 as (st2 & LB2 & PERM & Hst & RMR & [BL2 AR2]).
    eapply evt_mono.
    { eapply (raligned_tail_spec _ sp1) with (st := st2) (LB0 := LB2) (bp := p); rewrite ?SP1;
        [exact RMR| exact MI'| exact AR2| | rewrite Hst; exact RSL| exact HN| lia| exact FR].
      eapply Permutation_in; [apply Permutation_sym; exact PERM| left; reflexivity]. }
    intros ms'' (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & m'' & -> & MEQ).
    rewrite SP1. replace (Z_to_bv 64 (bv_unsigned sp + -32 + 32)) with sp by (apply bv_eq; rewrite unsigned_lit by lia; lia).
    release_frame FR ST' (bv_unsigned sp).
    unfold rmalloc_post. do 17 eexists. split; [reflexivity|].
    split; [exact (mem_inv_memeq rsegs m' m'' MEQ MI')|].
    split; [exact (stk_memeq rsegs m' m'' lo _ MEQ ST')|].
    split; [exact (rw_cells_memeq rsegs m' m'' _ _ MEQ ERR')|].
    split; [exact (rauxv_ok_memeq m' m'' B MEQ AUX')|].
    split; [intros a Ha; rewrite (MEQ (wa a)); exact (AUXC2 a Ha)|].
    split; [exact (rheap_pres_memeq_r LB _ m m' m'' MEQ PRES2)|].
    split; [exact EFA|]. split; [exact ESO|].
    exists A, bj. split; [reflexivity|]. split; [exact BR|]. split; [exact (RHEAP_memeq _ _ m' m'' MEQ HEAP2)|].
    split; [exact (rw_cells_memeq rsegs m' m'' _ _ MEQ BLK)| exact EXPO].
  -
    destruct RR as [-> HEAP2]. clear SP1. subst sp1.
    step. if_true. step. step. step. step. step.
    replace (Z_to_bv 64 (bv_unsigned sp + -32 + 32)) with sp by (apply bv_eq; rewrite unsigned_lit by lia; lia).
    release_frame FR ST' (bv_unsigned sp).
    unfold rmalloc_post. apply evt_done. do 17 eexists. split; [reflexivity|].
    split; [exact MI'|]. split; [exact ST'|]. split; [exact ERR'|]. split; [exact AUX'|]. split; [exact AUXC2|].
    split; [exact PRES2|]. split; [exact EFA|]. split; [exact ESO|]. split; [reflexivity| exact HEAP2].
Qed.
End P.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ref Require RF_malloc_spec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Theorem raligned16_spec : raligned16_stmt.
Proof. exact (raligned16_spec_proof RF_malloc_spec.rmalloc_impl_specX). Qed.

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
Import RF_aligned16_W.TwinB.

Set Keyed Unification.
Import ListNotations.
Import ITree.Exc.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.CeilLia.
Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Definition RALIGNED16_SYM : Z := 0x496c8.
Definition RALIGNED16_STACK : Z := RMALLOC_STACK + 32.

Definition RMREPL : Z := 0x89338.

Definition raligned16_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (n lo B : Z) (errv : word),
  RHEAP s LB m ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RALIGNED16_STACK ->
  rw_cells rsegs m (errno_addr tp) [C4 errv] ->
  mem_inv rsegs m ->
  tp = Z_to_bv 64 RATP ->
  rw_cells rsegs m RMREPL [C4 (wz 0)] ->
  a0 = Z_to_bv 64 16 -> a1 = Z_to_bv 64 n -> 0 <= n < 2^48 ->
  implM rsegs (raw_malloc n) s
        (rmalloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RALIGNED16_SYM) fc None m (seg_rom rsegs)).

Lemma bytes_at_4 m a (x0 x1 x2 x3 : byte) :
  bytes_at rsegs m a [x0] -> bytes_at rsegs m (a + 1) [x1] -> bytes_at rsegs m (a + 2) [x2] -> bytes_at rsegs m (a + 3) [x3] ->
  bytes_at rsegs m a [x0; x1; x2; x3].
Proof.
  intros (A0 & _ & B0) (_ & _ & B1) (_ & _ & B2) (_ & A3 & B3). split; [exact A0|]. split; [cbn in *; lia|].
  intros k Hk. cbn in Hk.
  destruct k as [|[|[|[|k]]]]; cbn [nth_error].
  - exact (B0 0%nat ltac:(cbn; lia)).
  - specialize (B1 0%nat ltac:(cbn; lia)). cbn [nth_error Z.of_nat] in B1. rewrite <- B1. f_equal. f_equal. lia.
  - specialize (B2 0%nat ltac:(cbn; lia)). cbn [nth_error Z.of_nat] in B2. rewrite <- B2. f_equal. f_equal. lia.
  - specialize (B3 0%nat ltac:(cbn; lia)). cbn [nth_error Z.of_nat] in B3. rewrite <- B3. f_equal. f_equal. lia.
  - lia.
Qed.

Lemma raligned_tail_spec :
  forall (ra1 sp gp tp x5 x6 x7 a1v a2v a3v a4v a5v a6v a7v s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 t4 t5 t6 rav s0v s1v : word)
         (junk : list byte) (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (st : mstate) (LB0 : list block) (bp : bptr) (n A : Z),
  rmrep st m -> mem_inv rsegs m -> AREACH_from ref_reserved st LB0 -> In (bp, A, n) LB0 -> rslack (strip st) (fst bp) A n ->
  0 <= n < 2^48 -> bv_unsigned sp + 32 <= 2^64 ->
  rw_cells rsegs m (bv_unsigned sp) [CB 8 junk; C8 s1v; C8 s0v; C8 rav] ->
  evt rsegs (raligned_tail_post sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 rav s0v s1v (Z_to_bv 64 A) F fc m)
      (MS (mkR ra1 sp gp tp x5 x6 x7 (Z_to_bv 64 16) (Z_to_bv 64 n) (Z_to_bv 64 A) a1v a2v a3v a4v a5v a6v a7v
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 t4 t5 t6)
          F (Z_to_bv 64 0x49768) fc None m (seg_rom rsegs)).
Proof.
  intros until A. intros RMR MI AR Hb RSL HN SPH FR.
  pose proof RMR as (WF & CX & GL & ARS & GR & SH). pose proof WF as (Hres & WR & DISJ & WA & WG).
  destruct (A_MallocFacts_inv.areach_inv _ _ _ AR) as (L & LS & BL & INV & _ & _ & _ & CR).
  pose proof (A_MallocFacts_inv3.areach_cinv_proof _ _ AR) as C.
  destruct (A_MallocFacts_inv.Forall2_In_l _ _ _ _ CR Hb) as (k & Hk & (C1 & C2 & C3)).
  destruct k as [[c off] n']. cbn [bslot boff bsize blk_slot blk_size blk_addr fst snd] in C1, C2, C3. subst n'.
  assert (C1' : fst bp = c) by exact C1.
  destruct (block_facts x0 st L BL LS INV c off n Hk) as (mm & bm & i & ai & a & ar & ka & BF).
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).

  pose proof (bf_slot _ _ _ _ _ _ _ _ _ _ _ BF) as SL. pose proof (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF) as HG.
  pose proof (bf_mem _ _ _ _ _ _ _ _ _ _ _ BF) as HM. pose proof (bf_c _ _ _ _ _ _ _ _ _ _ _ BF) as EC.
  pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF) as Hi. pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF) as Hoff.
  pose proof (bf_n _ _ _ _ _ _ _ _ _ _ _ BF) as Hn. pose proof (bf_fit _ _ _ _ _ _ _ _ _ _ _ BF) as FIT.
  pose proof (bf_stride _ _ _ _ _ _ _ _ _ _ _ BF) as [S1 S2]. pose proof (bf_b16 _ _ _ _ _ _ _ _ _ _ _ BF) as [Bb0 Bb16].
  pose proof (bf_notA _ _ _ _ _ _ _ _ _ _ _ BF) as NA. pose proof (bf_notF _ _ _ _ _ _ _ _ _ _ _ BF) as NF. unfold tbit in NA, NF.
  pose proof (bf_top _ _ _ _ _ _ _ _ _ _ _ BF) as TOP.
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
  set (res := e - po - n) in *.

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

  destruct RSL as (g2 & i2 & SL2 & RES). rewrite C1' in SL2, RES. change (s_slots (strip st)) with (s_slots st) in SL2. rewrite SL in SL2.
  assert (g2 = mm) as -> by congruence. clear SL2 i2.
  change (conc (strip st) c) with (conc st c) in RES. change (get_meta_rec (strip st) mm) with mr in RES. fold stride in RES.

  assert (HA : A = r_base r + po) by (subst po; rewrite C3, CC; unfold UNIT; clear; lia).
  assert (HE : e = snd bm + 16 + stride * i + stride - IB) by (subst e; rewrite SC'; clear; lia).
  assert (HPO : po = snd bm + 16 + 16 * q) by (subst po; rewrite SC'; clear - Q1; unfold UNIT in *; lia).
  assert (RESE : res = r_base r + e - A - n) by (subst res; rewrite HA; clear; lia).
  assert (RES31 : 0 <= res < 2^31) by (rewrite RESE, HE; rewrite CC, SC' in RES; unfold IB in *; clear - RES; lia).
  assert (AL : A mod 16 = 0) by (rewrite HA; clear - PM16 RBAL; Z.div_mod_to_equations; lia).
  assert (FIT' : po + n <= e) by (subst po e; unfold UNIT, IB in *; clear - FIT; lia).
  assert (PO16 : 16 <= po) by (rewrite HPO; clear - Bb0 Q2; lia).
  pose proof (round_up_pg_ge (r_len r)) as RUP.
  pose proof (rreserved_disjoint1 _ _ RF ltac:(clear - EHI' FIT' PO16 Hn; unfold IB in EHI'; lia)) as DRr.
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

  assert (K4' : cell_read (get_shadow st (fst bm)) (po - 4) = Known 0) by (rewrite <- FC; exact K4).
  assert (K3' : cell_read (get_shadow st (fst bm)) (po - 3) = Known (i + 32 * Z.min res 5)) by (rewrite <- FC; exact K3).
  assert (K2' : cell_read (get_shadow st (fst bm)) (po - 2) = Known (byte_of q 0)) by (rewrite <- FC; exact K2).
  assert (K1' : cell_read (get_shadow st (fst bm)) (po - 2 + 1) = Known (byte_of q 1)) by (rewrite <- FC; replace (po - 2 + 1) with (po - 1) by (clear; lia); exact K1).
  destruct (rmrep_shadow_read st m (fst bm) r (po - 4) 0 RMR Hr Kr' ltac:(clear - PO16 FIT' EHI' Hn; unfold IB in *; lia) K4') as [R4 _].
  destruct (rmrep_shadow_read st m (fst bm) r (po - 3) _ RMR Hr Kr' ltac:(clear - PO16 FIT' EHI' Hn; unfold IB in *; lia) K3') as [R3 B3R].
  destruct (rmrep_shadow_read2 st m (fst bm) r (po - 2) _ _ RMR Hr Kr' ltac:(clear - PO16; lia) ltac:(clear - PO16 FIT' EHI' Hn; unfold IB in *; lia) K2' K1') as (R2 & LO8 & HI8).
  rewrite <- le2_lohi, (u16_bytes q Q2) in R2 by assumption.
  replace (r_base r + (po - 4)) with (A - 4) in R4 by (clear - HA; lia).
  replace (r_base r + (po - 3)) with (A - 3) in R3 by (clear - HA; lia).
  replace (r_base r + (po - 2)) with (A - 2) in R2 by (clear - HA; lia).
  destruct (rmrep_group_read st m bm _ RMR HG) as [RG _]. cbn [g_meta pw oconc] in RG.
  pose proof (rmrep_meta_chunk st m mm RMR MSL) as MM. change (get_meta_rec st mm) with mr in MM. unfold meta_cells in MM. rewrite HM in MM. cbn [pw oconc] in MM. unfold meta_word in MM.
  pose proof (rmrep_area_check_read st m a ar RMR Ha) as RA. rewrite Hck in RA. change (c_secret (s_ctx st)) with (c_secret (ctx st)) in RA.
  replace (conc st a) with (conc st mm - conc st mm mod 4096) in RA by (rewrite <- HAR, Emm, (area_of_mslot a ka Hal Hka); reflexivity).
  pose proof (rmrep_ctx_secret_read st m RMR) as RC.

  assert (RDB : forall o v, cell_read (get_shadow st (fst c)) o = Known v -> 0 <= o < round_up_pg (r_len r) -> bytes_at rsegs m (r_base r + o) [b8 v]).
  { intros o v Ho Hor. rewrite FC in Ho. exact (proj1 (RDr o v Hor Ho)). }
  assert (B3AT : bytes_at rsegs m (A - 3) [b8 (i + 32 * Z.min res 5)]).
  { replace (A - 3) with (r_base r + (po - 3)) by (clear - HA; lia). apply RDB; [exact K3| clear - PO16 FIT' EHI' Hn; unfold IB in *; lia]. }
  assert (RB0 : 0 < res -> bytes_at rsegs m (r_base r + e - res) [b8 0]).
  { intros Hr0. replace (r_base r + e - res) with (r_base r + (e - res)) by (clear; lia). apply RDB; [exact (Kr Hr0)| clear - PO16 FIT' EHI' Hn Hr0 RESE HA; unfold IB in *; lia]. }
  assert (RB5 : 5 <= res -> bytes_at rsegs m (r_base r + e - 5) [b8 0] /\ bytes_at rsegs m (r_base r + e - 4) (le4 (wz res))).
  { intros Hr5. destruct (K5 Hr5) as (E0 & E1 & E2 & E3 & E5 & R32). split.
    - replace (r_base r + e - 5) with (r_base r + (e - 5)) by (clear; lia). apply RDB; [exact E5| clear - PO16 FIT' EHI' Hn Hr5; unfold IB in *; lia].
    - rewrite le4_bytes by (clear - RES31; lia).
      rewrite <- (byte_of_0 res), <- (byte_of_1 res), <- (byte_of_2 res) by (clear - RES31; lia).
      replace (res / 16777216) with (byte_of res 3) by (rewrite byte_of_3 by (clear - RES31; lia); apply Z.mod_small; clear - RES31; Z.div_mod_to_equations; lia).
      apply bytes_at_4.
      + replace (r_base r + e - 4) with (r_base r + (e - 4)) by (clear; lia). apply RDB; [exact E0| clear - PO16 FIT' EHI' Hn Hr5; unfold IB in *; lia].
      + replace (r_base r + e - 4 + 1) with (r_base r + (e - 3)) by (clear; lia). apply RDB; [exact E1| clear - PO16 FIT' EHI' Hn Hr5; unfold IB in *; lia].
      + replace (r_base r + e - 4 + 2) with (r_base r + (e - 2)) by (clear; lia). apply RDB; [exact E2| clear - PO16 FIT' EHI' Hn Hr5; unfold IB in *; lia].
      + replace (r_base r + e - 4 + 3) with (r_base r + (e - 1)) by (clear; lia). apply RDB; [exact E3| clear - PO16 FIT' EHI' Hn Hr5; unfold IB in *; lia]. }
  assert (WRX : forall x k, r_base r <= x -> x + k <= r_base r + round_up_pg (r_len r) -> 0 <= k -> wr_at rsegs m x k).
  { intros x kk H1 H2 H3. replace x with (r_base r + (x - r_base r)) by (clear; lia). eapply wr_at_sub; [exact WRr| clear - H1 H2 H3; lia| clear - H1 H2 H3; lia]. }
  pose proof (bf_sc _ _ _ _ _ _ _ _ _ _ _ BF) as BSC. fold mr in BSC. fold stride in BSC.
  apply (tail_a9c ra1 sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 rav s0v s1v junk F fc m
           A n (conc st mm) (conc st bm) (conc st mm - conc st mm mod 4096) stride i res q
           (m_avail mr) (m_freed mr) (m_last_idx mr) (m_freeable mr) (m_sizeclass mr) (m_maplen mr) (c_secret (ctx st))
           (pw st (m_prev mr)) (pw st (m_next mr))).
  - exact HN.
  - exact FR.
  - clear - HA RrB0 PO16. lia.
  - exact AL.
  - clear - HA HPO Bb0 RrB0. lia.
  - clear - HA FIT' EHI' RBC Hn RUP. unfold IB in *. lia.
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
  -
    intros Hlt. destruct BSC as [(Hsc & Hle & Hst)| E63]; [| clear - Hlt E63; lia].
    pose proof (size_class_bound _ Hsc) as SB.
    assert (A' : stride = 16 * size_class (m_sizeclass mr) \/ m_last_idx mr = 0) by (clear - Hst; unfold UNIT in Hst; tauto).
    assert (B' : stride <= 16 * size_class (m_sizeclass mr) \/ 292 <= size_class (m_sizeclass mr)).
    { destruct Hle as [Hle|H28]; [left; unfold UNIT in Hle; exact Hle| right; apply size_class_28; clear - H28 Hsc; lia]. }
    clear - SB Q1 FIT Hn Hoff Hi A' B'. unfold UNIT, IB in *.
    exact (guard16_arith _ _ _ _ _ _ _ (proj1 SB) Q1 FIT Hn Hoff Hi A' B').
  - clear - GSC. lia.
  -
    intros NM. destruct (TOP NM) as [B0 GE]. unfold gend, cnt_of, sstart in GE. rewrite (gbase_bm _ _ _ _ _ _ _ _ _ _ _ BF), B0 in GE.
    fold mr in GE. fold stride in GE.
    replace (m_maplen mr * 256) with (m_maplen mr * 4096 / 16) by (rewrite <- (Z.div_mul (m_maplen mr * 256) 16) by lia; f_equal; lia).
    clear - S1 Q1 FIT Hn Hoff Hi GE. unfold UNIT, IB in *.
    eapply (guard17_arith stride i off n q); try eassumption; lia.
  -
    intros Hd. destruct GSC as [Hsc|(E63 & L0 & MLn)]; [| exfalso; clear - Hd L0 MLn; lia].
    split; [clear - Hsc; lia|]. subst stride. unfold get_stride.
    destruct Hd as [Hd|Hd]; [rewrite (proj2 (Z.eqb_eq _ _) Hd), andb_false_r; reflexivity| rewrite (proj2 (Z.eqb_neq _ _) Hd); reflexivity].
  - intros [L0 MLn]. subst stride. unfold get_stride. rewrite (proj2 (Z.eqb_eq _ _) L0). replace (m_maplen mr =? 0) with false by (symmetry; apply Z.eqb_neq; exact MLn). reflexivity.
  - exact RES31.
  - clear - RESE HE CB. unfold IB in *. lia.
  - clear - DRr EHI' HA PO16 HE CB FIT' Hn. unfold IB in *. lia.
  - clear - EHI' HE CB RBC RUP. unfold IB in *. lia.
  - exact B3AT.
  - apply WRX; clear - HA PO16 FIT' EHI' RUP Hn; unfold IB in *; lia.
  - intros H. replace (conc st bm + 16 + stride * (i + 1) - 4 - res) with (r_base r + e - res) by (clear - HE CB; unfold IB in *; lia). exact (RB0 H).
  - intros H. apply WRX; clear - H HA PO16 FIT' EHI' RUP Hn HE CB RESE; unfold IB in *; lia.
  - intros H. replace (conc st bm + 16 + stride * (i + 1) - 4 - 5) with (r_base r + e - 5) by (clear - HE CB; unfold IB in *; lia).
    replace (conc st bm + 16 + stride * (i + 1) - 4 - 4) with (r_base r + e - 4) by (clear - HE CB; unfold IB in *; lia). exact (RB5 H).
  - intros H. apply WRX; clear - H HA PO16 FIT' EHI' RUP Hn HE CB RESE; unfold IB in *; lia.
Qed.

Lemma rheap_pres_stackframe s LB (sp : Z) m m1 :
  RHEAP s LB m -> munch [(sp - 32, sp)] m m1 -> wmono rsegs m m1 -> alloc_ceiling <= sp - 32 -> rheap_pres LB sp m m1.
Proof.
  intros HP MU WM LO.
  assert (PE : rpres_except (fun a => sp - 32 <= a < sp) m m1).
  { eapply rpres_except_of_munch'; [exact MU| exact WM|]. intros lo hi [E|[]] x Hx. inversion E; subst. exact Hx. }
  intros a Ha HC. apply PE; [exact Ha|]. intros HX.
  destruct HC as [HC|[[HC _]|(b & Hb & Hab)]]; [lia| pose_ceil; lia|].
  pose proof (RHEAP_block_range_proof s LB m b HP Hb) as (_ & _ & _ & R4 & _). lia.
Qed.

Lemma rauxcell_pres_stackframe (sp : Z) m m1 : munch [(sp - 32, sp)] m m1 -> alloc_ceiling <= sp - 32 -> rauxcell_pres m m1.
Proof.
  intros MU LO a Ha. apply MU. rewrite wa_unsigned by (unfold RAUXV_CELL in Ha; lia). cbn. pose_ceil; unfold RAUXV_CELL in *. lia.
Qed.

Section P.
Hypothesis HIMPL : rmalloc_impl_stmtX.

Theorem raligned16_spec_proof : raligned16_stmt.
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB n lo B errv.
  intros HEAP AUXB SB ST CLO LO ERR MI TP REPL HA0 HA1 HN.
  unfold RALIGNED16_STACK, RMALLOC_STACK in LO. unfold RALIGNED16_SYM. unfold RMREPL in REPL. subst a0 a1.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof CLO as CLOv. pose_ceil.
  assert (ETP : bv_unsigned tp + -164 = 429036) by (rewrite TP; unfold RATP; rewrite unsigned_lit by lia; reflexivity).
  rewrite ETP in ERR.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  unfold implM. iprefix.
  carve_frame 32%nat ST.

  step. step. step. step.

  step. step. step. if_false. step. step. if_false.
  step. step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. { exfalso. clear - K HN. lia. } clear K.

  step. step. step. if_true.

  step. step. if_false. step. step. step. step. step. step.
  apply evt_done. replace (Z_to_bv 64 (16 + n + -16)) with (Z_to_bv 64 n) by (f_equal; lia).

  lazymatch goal with |- impl _ _ _ _ (MS _ _ _ _ _ ?mX _) => rename mX into m1 end.
  assert (HEAP1 : RHEAP s LB m1).
  { eapply RHEAP_frame_proof; [exact HEAP| exact MU| exact WM|]. constructor; [| constructor]. left. cbn [fst]. lia. }
  assert (AUX1 : rauxv_ok m1 B).
  { eapply rauxv_ok_frame; [exact AUXB| exact MU| exact WM|]. constructor; [| constructor]. cbn [fst snd]. unfold RAUXV_CELL, RLIBC. lia. }
  pose proof (rheap_pres_stackframe s LB (bv_unsigned sp) m m1 HEAP ltac:(replace (bv_unsigned sp - 32) with (bv_unsigned sp + -32) by lia; exact MU) WM ltac:(lia)) as PRES1.
  pose proof (rauxcell_pres_stackframe (bv_unsigned sp) m m1 ltac:(replace (bv_unsigned sp - 32) with (bv_unsigned sp + -32) by lia; exact MU) ltac:(lia)) as AUXC1.
  clear MU WM.
  set (sp1 := Z_to_bv 64 (bv_unsigned sp + -32)) in *.
  assert (SP1 : bv_unsigned sp1 = bv_unsigned sp + -32) by (subst sp1; apply unsigned_lit; lia).

  eapply impl_post_evt.
  { pose proof HIMPL as X. unfold rmalloc_impl_stmtX, implM, rmalloc_entry in X.
    eapply X with (lo := lo) (B := B) (errv := errv); clear X; rewrite ?SP1.
    all: first [exact HEAP1| exact AUX1| exact ST| exact MI| exact TP| exact HN| reflexivity| unfold RMALLOC_STACK; lia| rewrite ETP; exact ERR]. }
  cbv beta. intros [|[r s']] ms' PO; [apply evt_done; exact I|]. cbn [epost fst snd] in PO |- *.
  destruct PO as (w0 & w1 & w2 & ra0 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & m' & errv' & -> & MI' & ST' & ERR' & AUX' & AUXC & PRES & EFA & ESO & RR).
  rewrite SP1 in ST', PRES.
  replace (ret_pc (Z_to_bv 64 300904)) with (Z_to_bv 64 300904) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

  apply (rheap_pres_rw_cells _ _ _ _ _ _ PRES) in FR; [| left; lia].
  assert (PRES2 : rheap_pres LB (bv_unsigned sp) m m').
  { eapply rheap_pres_trans; [exact PRES1|]. eapply rheap_pres_weaken; [exact PRES| lia| auto]. }
  assert (AUXC2 : rauxcell_pres m m') by (eapply rauxcell_pres_trans; [exact AUXC1| exact AUXC]).
  clear PRES1 AUXC1 HEAP1 AUX1 ERR REPL MI.
  destruct r as [p|].
  -
    destruct RR as (A & bj & -> & BR & HEAP2 & BLK & EXPO & RSL).
    pose proof HEAP2 as (st2 & LB2 & PERM & Hst & RMR & [BL2 AR2]).
    eapply evt_mono.
    { eapply (raligned_tail_spec _ sp1) with (st := st2) (LB0 := LB2) (bp := p); rewrite ?SP1;
        [exact RMR| exact MI'| exact AR2| | rewrite Hst; exact RSL| exact HN| lia| exact FR].
      eapply Permutation_in; [apply Permutation_sym; exact PERM| left; reflexivity]. }
    intros ms'' (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & m'' & -> & MEQ).
    rewrite SP1. replace (Z_to_bv 64 (bv_unsigned sp + -32 + 32)) with sp by (apply bv_eq; rewrite unsigned_lit by lia; lia).
    release_frame FR ST' (bv_unsigned sp).
    unfold rmalloc_post. do 17 eexists. split; [reflexivity|].
    split; [exact (mem_inv_memeq rsegs m' m'' MEQ MI')|].
    split; [exact (stk_memeq rsegs m' m'' lo _ MEQ ST')|].
    split; [exact (rw_cells_memeq rsegs m' m'' _ _ MEQ ERR')|].
    split; [exact (rauxv_ok_memeq m' m'' B MEQ AUX')|].
    split; [intros a Ha; rewrite (MEQ (wa a)); exact (AUXC2 a Ha)|].
    split; [exact (rheap_pres_memeq_r LB _ m m' m'' MEQ PRES2)|].
    split; [exact EFA|]. split; [exact ESO|].
    exists A, bj. split; [reflexivity|]. split; [exact BR|]. split; [exact (RHEAP_memeq _ _ m' m'' MEQ HEAP2)|].
    split; [exact (rw_cells_memeq rsegs m' m'' _ _ MEQ BLK)| exact EXPO].
  -
    destruct RR as [-> HEAP2]. clear SP1. subst sp1.
    step. if_true. step. step. step. step. step.
    replace (Z_to_bv 64 (bv_unsigned sp + -32 + 32)) with sp by (apply bv_eq; rewrite unsigned_lit by lia; lia).
    release_frame FR ST' (bv_unsigned sp).
    unfold rmalloc_post. apply evt_done. do 17 eexists. split; [reflexivity|].
    split; [exact MI'|]. split; [exact ST'|]. split; [exact ERR'|]. split; [exact AUX'|]. split; [exact AUXC2|].
    split; [exact PRES2|]. split; [exact EFA|]. split; [exact ESO|]. split; [reflexivity| exact HEAP2].
Qed.
End P.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Theorem raligned16_spec : raligned16_stmt.
Proof. exact (raligned16_spec_proof RF_malloc_spec.TwinB.rmalloc_impl_specX). Qed.

End CEIL.
End TwinB.
