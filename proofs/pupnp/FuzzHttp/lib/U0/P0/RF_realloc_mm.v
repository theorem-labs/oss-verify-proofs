(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Image ZBridge SysStep SysMm SFModel Arr.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs ImgFacts.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.Malloc Require Import F_malloc_free F_malloc_fast F_malloc_enframe F_free_A F_free F_free_K F_free_spec MallocTree MallocKit_A MallocBlocks MallocHINV ASlot_W14
  MallocFacts_A MallocFacts_B MallocFacts_inv MallocFacts_inv2 MallocFacts_inv3 Malloc_iface Malloc_fp F_malloc_entry.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import STree Malloc MallocCtrl Prog KInv MI_Inv MI_Ext MI_Geom MI_Pres2 MI_Read MI_WGroup MI_WFree MI_WRealloc MI_WRealloc2
  MRemapOp MI_WRemap KRemapDef MI_Cnt MI_Kit MI_WAMeta.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import RMallocRep RMallocTree RMallocKit_A RMallocKit_B RMallocKit_B2 RMallocKit_B3 RMalloc_fp RMalloc_iface RMalloc_ifaceP RF_get_meta RF_free_A RF_free
  RF_free_spec RF_realloc_A RF_realloc_B RF_realloc_C RF_realloc_D RF_realloc_rep RF_realloc_ip RF_realloc_spec RF_realloc_M RF_realloc_mrep F_mm_syscalls.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac ulia := ceil_facts; unfold UNIT, IB; lia.
Local Ltac freeze H := lazymatch type of H with ?T => change (frozen T) in H end.
Local Ltac thaw H := unfold frozen in H.

Notation RAREACH := (AREACH_from p0_reserved).

Definition rrmm_at (sp gp tp s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m2 : mem) (gw : word) (nn n' dst off : Z)
    : machine_state -> Prop :=
  fun ms' => exists ra' t0 t1 t2 a0' a3 a4 a5 a6 a7 s2' s5' s6' t3 t4 t5 t6,
    ms' = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 nn) gw a0' (Z_to_bv 64 n') (Z_to_bv 64 dst) a3 a4 a5 a6 a7
                  s2' (Z_to_bv 64 (UNIT * off)) (Z_to_bv 64 4095) s5' s6' s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x19c50) fc None m2 (seg_rom rsegs).

Definition rrmm_callst (sp gp tp s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m1 : mem) (gw : word) (P B n' off nn on sz : Z)
    : machine_state -> Prop :=
  fun ms' => exists t0 a5 a6 a7 t4 t5 t6,
    ms' = MS (mkR (Z_to_bv 64 0x19c44) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 (Z_to_bv 64 (B + 16)) (Z_to_bv 64 0x1ffec) (Z_to_bv 64 nn) gw
                  (Z_to_bv 64 B) (Z_to_bv 64 on) (Z_to_bv 64 nn) (Z_to_bv 64 1) (Z_to_bv 64 on) a5 a6 a7
                  (Z_to_bv 64 (P + sz)) (Z_to_bv 64 (UNIT * off)) (Z_to_bv 64 4095) (Z_to_bv 64 P) (Z_to_bv 64 n') s7 s8 s9 s10 s11 (Z_to_bv 64 0x1ffeb) t4 t5 t6)
             F (Z_to_bv 64 0x19ed4) fc None m1 (seg_rom rsegs).

Definition rrmm_m1 {HGW : HasGuard} {HCEIL : HasCeiling} (ra sp s0 s1 s2 s3 s4 s5 s6 : word) (lo : Z) (st : mstate) (m m1 : mem) : Prop :=
  rw_cells rsegs m1 (bv_unsigned sp + -64) (rr_frame s6 s5 s4 s3 s2 s1 s0 ra)
  /\ stk rsegs m1 lo (bv_unsigned sp + -64)
  /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1 /\ rmrep st m1.

Section MM.
Context {HGW : HasGuard}.
Context {HCEIL : HasCeiling}.
Variables (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (LB : list block) (lo : Z).
Hypothesis LO : alloc_ceiling <= lo.

Theorem rrealloc_walk_mm : forall (ra sp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem)
    (st : mstate) (blk : block) (off n' : Z) (mm : aptr) (i : Z),
  RAREACH st LB -> In blk LB -> 0 <= off -> blk_addr blk = conc st (blk_slot blk) + UNIT * off ->
  (s_slots st) !! (blk_slot blk) = Some (mm, i) ->
  rmrep st m -> mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 64 ->
  a0 = Z_to_bv 64 (blk_addr blk) -> a1 = Z_to_bv 64 n' -> MMAP_THRESHOLD <= n' < 2^32 ->
  evt rsegs (fun ms' =>
        (m_sizeclass (get_meta_rec st mm) < 48
         /\ rrgen_prefix_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo (blk_addr blk) (blk_size blk) n' m ms')
        \/ (m_sizeclass (get_meta_rec st mm) = 63 /\ i = 0 /\ off <= 255
         /\ exists m1 rg, rrmm_m1 ra sp s0 s1 s2 s3 s4 s5 s6 lo st m m1
             /\ (s_regions st) !! (fst (blk_slot blk)) = Some rg /\ r_kind rg = RKGroup
             /\ m_maplen (get_meta_rec st mm) * 4096 = round_up_pg (r_len rg) /\ conc st (blk_slot blk) = r_base rg + 16
             /\ let on := m_maplen (get_meta_rec st mm) * 4096 in let nn := mremap_needed off n' in
                ((on = nn /\ rrmm_at sp gp tp s7 s8 s9 s10 s11 F fc m1 (wz (conc st mm)) nn n' (r_base rg) off ms')
                 \/ (on <> nn /\ rrmm_callst sp gp tp s7 s8 s9 s10 s11 F fc m1 (wz (conc st mm)) (blk_addr blk) (r_base rg) n' off nn on (blk_size blk) ms'))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 rrealloc_sym) fc None m (seg_rom rsegs)).
Proof using LO.
  intros until i. intros AR Hin Hoff HA Hs HMR MI ST SLO A0 A1 N.

  pose proof (areach_cinv_proof _ _ AR) as C. pose proof (ci_ticks _ _ C) as TK.
  destruct (areach_inv _ st LB AR) as (L & LS & BL & INV & _ & _ & _ & CR).
  destruct (Forall2_In_l _ _ _ _ CR Hin) as (k & Hk & (K1 & K2 & K3)).
  destruct k as [[c bo] n]. cbn [bslot boff bsize fst snd] in K1, K2, K3.
  assert (bo = off) as -> by (rewrite K1 in HA; rewrite HA in K3; unfold UNIT in K3; lia).
  rewrite K1 in Hs, HA |- *. rewrite K2. set (A := blk_addr blk) in *.
  destruct (block_facts x0 st L BL LS INV c off n Hk) as (g & bm & i' & ai & aa & ar & ka & BF).
  pose proof (bf_slot _ _ _ _ _ _ _ _ _ _ _ BF) as Hs'. rewrite Hs in Hs'. symmetry in Hs'. inversion Hs'. subst g i'. clear Hs'.
  pose proof (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF) as Hgh. pose proof (bf_mem _ _ _ _ _ _ _ _ _ _ _ BF) as Hmem.
  pose proof (bf_c _ _ _ _ _ _ _ _ _ _ _ BF) as Ec. pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF) as Hi. pose proof (bf_li _ _ _ _ _ _ _ _ _ _ _ BF) as Hli.
  pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF) as OFF. pose proof (bf_n _ _ _ _ _ _ _ _ _ _ _ BF) as N0. pose proof (bf_fit _ _ _ _ _ _ _ _ _ _ _ BF) as FIT.
  pose proof (bf_stride _ _ _ _ _ _ _ _ _ _ _ BF) as [S16 SMOD]. pose proof (bf_b16 _ _ _ _ _ _ _ _ _ _ _ BF) as [B0 BMOD].
  pose proof (bf_notA _ _ _ _ _ _ _ _ _ _ _ BF) as NA. pose proof (bf_notF _ _ _ _ _ _ _ _ _ _ _ BF) as NF. pose proof (bf_notH _ _ _ _ _ _ _ _ _ _ _ BF) as NH.
  pose proof (bf_sc _ _ _ _ _ _ _ _ _ _ _ BF) as BSC. pose proof (bf_top _ _ _ _ _ _ _ _ _ _ _ BF) as TOP. pose proof (bf_maplen _ _ _ _ _ _ _ _ _ _ _ BF) as ML0.
  destruct (bf_area _ _ _ _ _ _ _ _ _ _ _ BF) as (Ha & Hck & Hal & Hka & Emm).
  pose proof (bf_shadow _ _ _ _ _ _ _ _ _ _ _ BF) as SHD. pose proof (bf_hdr0 _ _ _ _ _ _ _ _ _ _ _ BF) as HDR0.
  pose proof (q16 _ _ _ _ _ _ _ _ _ _ _ BF) as (Q1 & Q2 & Q3). pose proof (p_mod16 _ _ _ _ _ _ _ _ _ _ _ BF) as PM16.
  cbn [aadd snd] in Q1, Q2, Q3, PM16.
  set (q := (snd c + UNIT * off - snd bm - UNIT) / UNIT) in *. clearbody q.
  change (frozen ((snd c + UNIT * off) mod 16 = 0)) in PM16.
  set (mr := get_meta_rec st mm) in *. change (MR st mm) with mr in *.
  set (stride := get_stride mr) in *.
  assert (HST : hosts st bm mm) by (exists ai; exact Hgh).
  pose proof (ci_gmetas _ _ C bm mm HST) as GO.
  destruct (go_region _ _ _ GO) as (r & Hr & Kr & _ & _ & SPAN & _).
  assert (Fc : fst c = fst bm) by (rewrite Ec; reflexivity).
  assert (Sc : snd c = snd bm + 16 + stride * i) by (rewrite Ec; cbn [snd]; unfold sstart; fold mr; unfold gbase; rewrite Hmem; cbn; unfold UNIT; lia).
  pose proof HMR as (WF & CX & GL & ARR & GR & SH). pose proof WF as (Hres & CE & WR & DJ & WA & WG).
  destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RF). freeze RBAL.
  pose proof (rreserved_disjoint1 _ _ RF) as DRr. freeze DRr.
  assert (Hrc : s_regions st !! fst c = Some r) by (rewrite Fc; exact Hr).
  assert (Cc : conc st c = r_base r + snd c) by (apply conc_region'; exact Hrc).
  assert (HAP : A = r_base r + snd c + UNIT * off) by (unfold A; rewrite Cc in HA; exact HA).
  assert (SI0 : 0 <= stride * i) by (apply Z.mul_nonneg_nonneg; unfold UNIT in S16; lia).
  assert (SIL : stride * i + stride <= stride * m_last_idx mr + stride).
  { clear -S16 Hi. unfold UNIT in S16. pose proof (Z.mul_le_mono_nonneg_l i (m_last_idx mr) stride ltac:(lia) ltac:(lia)). lia. }
  unfold sstart_of in SPAN. change (get_meta_rec st mm) with mr in SPAN. rewrite Hmem in SPAN. cbn [default id snd] in SPAN. fold stride in SPAN.
  rewrite Z.mul_add_distr_l, Z.mul_1_r in SPAN.
  assert (OFF16 : 16 * off + 16 <= stride).
  { clear -FIT N0 SMOD OFF S16. unfold UNIT, IB in *. Z.div_mod_to_equations. lia. }
  clear SMOD BMOD.
  set (P := r_base r + snd c + UNIT * off) in *.
  set (E := r_base r + snd c + stride - IB).
  assert (ETOP : snd c + stride - IB + 1 <= round_up_pg (r_len r)) by (rewrite Sc; unfold UNIT, IB in *; lia).
  pose proof (round_up_pg_ge (r_len r)) as RUP. ceil_facts.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.

  pose proof SHD as SHD'. unfold blk_shadow_ok in SHD'. cbn [bslot boff bsize fst snd] in SHD'. change (MR st mm) with mr in SHD'. fold stride in SHD'.
  unfold gbase in SHD'. rewrite Hmem in SHD'. cbn [default id snd] in SHD'.
  replace ((snd c + UNIT * off - snd bm - UNIT) / UNIT) with q in SHD'.
  2:{ clear -Q1 Sc. unfold UNIT in *. replace (snd c + 16 * off - snd bm - 16) with (q * 16) by lia. symmetry. apply Z.div_mul. lia. }
  destruct SHD' as (O4 & O3 & O2 & O1 & _ & O5 & OC & OU).
  assert (EA0 : (fst c, snd c + stride - IB) = (fst bm, sstart mr (i + 1) - IB)).
  { rewrite Ec. cbn [fst snd]. f_equal. unfold sstart. fold stride. rewrite Z.mul_add_distr_l, Z.mul_1_r. lia. }
  assert (HDR0' : known st (fst c, snd c + stride - IB) 0) by (rewrite EA0; exact HDR0).
  clear EA0.
  set (res := snd c + stride - IB - (snd c + UNIT * off) - n) in *.
  assert (RESEQ : res = stride - IB - UNIT * off - n) by (unfold res; lia). clearbody res.
  assert (RES0 : 0 <= res) by (unfold UNIT, IB in *; lia).
  assert (M5 : 0 <= Z.min res 5 <= 5 /\ Z.min res 5 <= res) by (clear -RES0; lia).
  assert (M5c : (5 <= res -> Z.min res 5 = 5) /\ (res < 5 -> Z.min res 5 = res)) by (clear -RES0; lia).
  set (r5 := Z.min res 5) in *. assert (R5EQ : r5 = Z.min res 5) by reflexivity. clearbody r5. freeze M5c. freeze R5EQ.
  set (b3 := i + 32 * r5) in *. assert (B3EQ : b3 = i + 32 * r5) by reflexivity.
  assert (B3R : 0 <= b3 < 256) by (clear -M5 Hi Hli; unfold b3; lia).
  assert (IDX : Z.land b3 31 = i) by (clear -M5 Hi Hli; unfold b3; apply land31_idx; lia).
  assert (SR5 : Z.shiftr b3 5 = r5) by (clear -M5 Hi Hli; unfold b3; apply shiftr5_res; lia).
  clearbody b3. freeze B3EQ.

  pose proof (areach_facts_proof _ _ AR) as MF.
  assert (HmemS : m_mem (get_meta_rec (strip st) mm) = Some bm) by (rewrite get_meta_rec_strip; exact Hmem).
  destruct (mf_gmeta _ _ MF mm bm HmemS) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S31 & _). rewrite get_meta_rec_strip in S31.
  change (get_meta_rec st mm) with mr in S31. fold stride in S31.
  pose proof (go_sc _ _ _ GO) as GSC. change (get_meta_rec st mm) with mr in GSC.
    assert (SC64 : 0 <= m_sizeclass mr < 64) by (clear -GSC; lia).
  assert (SC63 : 48 <= m_sizeclass mr -> m_sizeclass mr = 63) by (clear -GSC; lia).
  freeze GSC. freeze BSC. freeze TOP.
  destruct (SH _ r Hr Kr) as [HWr _].
  assert (KB : forall o v, known st (fst c, o) v -> snd c - 4 <= o < snd c + stride - IB + 1 ->
               bytes_at rsegs m (r_base r + o) [b8 v] /\ 0 <= v < 256).
  { intros o v Kn Ho. destruct (rmrep_shadow_read st m (fst c) r o v HMR Hrc Kr ltac:(clear -Ho Sc ETOP SI0 B0; unfold UNIT, IB in *; lia) Kn) as [RD VR].
    split; [| exact VR]. apply read1_bytes_at; [exact RD| lia| lia]. }

  unfold UNIT, IB in *.
  subst a0 a1.
  eapply evt_cut.
  { eapply (rrealloc_A0 ra sp gp tp t0 t1 t2 s0 s1 _ _ a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo A n');
      [reflexivity| unfold P in *; unfold UNIT, IB in *; lia| reflexivity| unfold MMAP_THRESHOLD in N; lia| exact ST| lia| exact SLO| exact MI]. }
  intros ms1 (m1 & -> & FR1 & ST1 & MU1 & WM1 & MI1).
  assert (MR1 : rmrep st m1).
  { eapply rmrep_transport_high; [exact HMR| exact MU1| exact WM1|]. intros l h [E1|[]]. inversion E1; subst. ceil_facts. lia. }
  assert (KB1 : forall o v, known st (fst c, o) v -> snd c - 4 <= o < snd c + stride - 3 -> bytes_at rsegs m1 (r_base r + o) [b8 v] /\ 0 <= v < 256).
  { intros o v Kn Ho. destruct (KB o v Kn ltac:(lia)) as [B V]. split; [| exact V].
    eapply bytes_at_transport; [exact B| exact MU1|]. cbn. lia. }

  pose proof (u16_bytes q ltac:(lia)) as U16.
  eapply evt_cut.
  { eapply (rrealloc_A1_spec ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 n') _ a3 a4 a5 a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 st (fst c, snd c + UNIT * off) r mm (mkGhdr (Some mm) ai) ar b3 (byte_of q 0) (byte_of q 1) bm);
      cbn [fst snd]; rewrite ?U16, ?IDX; change (get_meta_rec st mm) with mr.
    - unfold aadd. cbn [fst snd]. rewrite Fc. apply injective_projections; cbn [fst snd]; [reflexivity| ulia].
    - exact MR1.
    - exact MI1.
    - exact Hrc.
    - exact Kr.
    - unfold P in HAP. rewrite unsigned_lit by lia. ulia.
    - exact PM16.
    - ulia.
    - ulia.
    - ulia.
    - exact O4.
    - exact O3.
    - exact O2.
    - replace (snd c + UNIT * off - 1) with (snd c + UNIT * off - 1) by lia. exact O1.
    - exact Hgh.
    - reflexivity.
    - exists aa, ar, ka. split; [exact Ha|]. split; [exact Hka|]. exact Emm.
    - rewrite Emm. unfold mslot, aadd. cbn [snd]. destruct (WA aa ar Ha) as (rg0 & _ & A00 & _). unfold AREA_HDR, META_SIZE. lia.
    - exact Hmem.
    - rewrite Emm, (area_of_mslot aa ka Hal Hka). exact Ha.
    - exact Hck.
    - exact (go_avail _ _ _ GO).
    - exact (go_freed _ _ _ GO).
    - exact (proj2 (proj2 (proj2 (proj2 (ci_cx _ _ C))))).
    - lia.
    - rewrite (go_freeable _ _ _ GO). clear; lia.
    - exact SC64.
    - pose proof (go_maplen _ _ _ GO) as GML. change (get_meta_rec st mm) with mr in GML. clear -GML. lia.
    - clear -Hi. lia.
    - unfold tbit in NA. exact NA.
    - unfold tbit in NF. exact NF.
    - intros Hsc. thaw BSC. destruct BSC as [(Hsc' & Hle & Hst)| E63]; [| exfalso; clear -E63 Hsc; lia].
      assert (SC48 : 0 <= m_sizeclass mr < 48) by (clear -Hsc SC64; lia).
      pose proof (size_class_range _ SC48) as SB.
      apply (guard16_arith (size_class (m_sizeclass mr)) stride i off n q (m_last_idx mr)).
      + clear -SB; lia.
      + clear -Q1; unfold UNIT in *; lia.
      + clear -FIT; unfold UNIT, IB in *; lia.
      + exact N0.
      + exact OFF.
      + exact Hi.
      + clear -Hst; unfold UNIT in *; destruct Hst as [Hst|[Hst _]]; [left| right]; lia.
      + clear -Hle SC48; unfold UNIT in *; destruct Hle as [Hle|H28]; [left; lia| right; apply size_class_28; lia].
    - exact SC63.
  }
  intros ms2 (t3' & t4' & ->).
  assert (RSVeq : (if 160 <=? b3 then res else r5) = res).
  { destruct (Z.leb_spec 160 b3) as [H160|H160]; [reflexivity|]. thaw M5c.
    clear -H160 M5 M5c B3R SR5 RES0. pose proof (Z.shiftr_div_pow2 b3 5 ltac:(lia)) as SD. change (2^5) with 32 in SD. rewrite SD in SR5.
    assert (r5 < 5) by (Z.div_mod_to_equations; lia). lia. }

  assert (Cbm : conc st bm = r_base r + snd bm) by (apply conc_region'; exact Hr).
  assert (STRdef : stride = (if (m_last_idx mr =? 0) && negb (m_maplen mr =? 0) then m_maplen mr * 4096 - 16 else 16 * size_class (m_sizeclass mr))) by reflexivity.
  unfold meta_word.
  eapply evt_cut.
  { eapply (rrealloc_A3 ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t3' t4' t5 t6 s0 (Z_to_bv 64 A) (Z_to_bv 64 n') s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
              (wz (conc st mm)) F fc m1 P (conc st bm) b3 _ (m_last_idx mr) (m_freeable mr) (m_sizeclass mr) (m_maplen mr) stride res);
      rewrite ?U16, ?IDX.
    - unfold P in HAP. rewrite unsigned_lit by lia. lia.
    - lia.
    - unfold P. lia.
    - exact MI1.
    - exact B3R.
    - lia.
    - lia.
    - rewrite (go_freeable _ _ _ GO). lia.
    - exact SC64.
    - pose proof (go_maplen _ _ _ GO) as GML. change (get_meta_rec st mm) with mr in GML. lia.
    - intros Hml. thaw TOP. destruct (TOP Hml) as [Bz GE]. unfold gend, cnt_of, sstart in GE. unfold gbase in GE. rewrite Hmem in GE. cbn [default id snd] in GE.
      change (get_stride mr) with stride in GE. unfold UNIT in GE.
      pose proof (guard17_arith stride i off n q (m_last_idx mr) (m_maplen mr) ltac:(lia) ltac:(lia) ltac:(lia) N0 ltac:(lia) ltac:(lia) ltac:(lia)) as G17.
      replace (m_maplen mr * 4096 / 16) with (m_maplen mr * 256) in G17; [lia|].
      rewrite <- (Z.div_mul (m_maplen mr * 256) 16) by lia. f_equal. lia.
    - intros [Hml Hl0]. rewrite STRdef. rewrite (proj2 (Z.eqb_eq _ _) Hl0). replace (m_maplen mr =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hml). reflexivity.
    - intros HC. split; [| thaw GSC; clear -GSC HC; lia]. rewrite STRdef. destruct HC as [HC|HC]; [rewrite (proj2 (Z.eqb_eq _ _) HC), andb_false_r; reflexivity| rewrite (proj2 (Z.eqb_neq _ _) HC); reflexivity].
    - lia.
    - unfold P, E. lia.
    - lia.
    -   intros H160. rewrite SR5.
      assert (R55 : r5 = 5).
      { clear -H160 M5 B3R SR5. pose proof (Z.shiftr_div_pow2 b3 5 ltac:(lia)) as SD. change (2^5) with 32 in SD. rewrite SD in SR5. Z.div_mod_to_equations. lia. }
      thaw M5c. assert (R5 : 5 <= res) by (clear -R55 M5 M5c; lia).
      destruct (O5 R5) as (F0 & F1 & F2 & F3 & F5 & R32).
      split; [exact R55|]. split; [clear -R5 R32; lia|]. split.
      + rewrite (le4_byte_of res) by lia.
        destruct (KB1 _ _ F0 ltac:(lia)) as [BX0 _]. destruct (KB1 _ _ F1 ltac:(lia)) as [BX1 _].
        destruct (KB1 _ _ F2 ltac:(lia)) as [BX2 _]. destruct (KB1 _ _ F3 ltac:(lia)) as [BX3 _].
        replace (conc st bm + 16 + stride * i + stride - 4 - 4) with (r_base r + (snd c + stride - 4 - 4)) by lia.
        apply bytes_at_4; [exact BX0| | |];
          [replace (r_base r + (snd c + stride - 4 - 4) + 1) with (r_base r + (snd c + stride - 4 - 3)) by lia
          |replace (r_base r + (snd c + stride - 4 - 4) + 2) with (r_base r + (snd c + stride - 4 - 2)) by lia
          |replace (r_base r + (snd c + stride - 4 - 4) + 3) with (r_base r + (snd c + stride - 4 - 1)) by lia]; assumption.
      + destruct (KB1 _ _ F5 ltac:(lia)) as [BX5 _].
        replace (conc st bm + 16 + stride * i + stride - 4 - 5) with (r_base r + (snd c + stride - 4 - 5)) by lia. exact BX5.
    -   rewrite SR5. unfold P. destruct (160 <=? b3); clear -M5 RESEQ FIT N0 Cbm Sc; lia.
    -   rewrite SR5, RSVeq.
      destruct (Z.eq_dec res 0) as [R0|R0].
      + rewrite R0, Z.sub_0_r. destruct (KB1 _ _ HDR0' ltac:(lia)) as [BX _].
        replace (conc st bm + 16 + stride * i + stride - 4) with (r_base r + (snd c + stride - 4)) by lia. exact BX.
      + destruct (KB1 _ _ (OC ltac:(lia)) ltac:(lia)) as [BX _].
        replace (conc st bm + 16 + stride * i + stride - 4 - res) with (r_base r + (snd c + stride - 4 - res)) by lia. exact BX.
    - destruct (KB1 _ _ HDR0' ltac:(lia)) as [BX _].
      replace (conc st bm + 16 + stride * i + stride - 4) with (r_base r + (snd c + stride - 4)) by lia. exact BX. }
  intros ms3 (t4'' & ->). rewrite ?IDX, ?SR5, ?RSVeq.
  replace (conc st bm + 16 + stride * i + stride - 4) with E by (unfold E; clear -Cbm Sc; lia).

  thaw BSC. destruct BSC as [(SC48' & Hle & Hst)| E63].
  {
  eapply evt_mono; [| intros msX HX; left; split; [clear -SC48'; lia| exact HX]].
  eapply evt_cut.
  { eapply (rrealloc_B_gen ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp _ t4'' t5 t6 s0 (Z_to_bv 64 A) (Z_to_bv 64 n') s3 s4 s5 s6 s7 s8 s9 s10 s11
              (wz (conc st mm)) F fc m1 P (conc st bm) (m_sizeclass mr) _ stride E res b3 n');
      [reflexivity| unfold MMAP_THRESHOLD in N; lia| exact MI1| unfold P, E; lia| unfold E; lia| exact SC64|].
    right. split; [exact (proj1 N)| clear -SC48'; lia]. }
  intros ms4 (t0_ & t1_ & t2_ & t3_ & t4_ & a2_ & a3_ & a4_ & a5_ & a6_ & a7_ & ->).
  eapply evt_mono; [apply rrgen_tomalloc|]. intros ms5 ->.
  unfold rrgen_prefix_post. do 14 eexists. exists m1.
  replace (A + n) with (E - res) by (unfold E, P in *; clear -RESEQ HAP; lia).
  split; [rewrite HAP; reflexivity|].
  split; [exact FR1|]. split; [exact ST1|]. split; [exact MU1|]. split; [exact WM1| exact MI1]. }
  {

  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  destruct (hosts_ok x0 st LS IG bm mm HST) as (ai2 & Hg2 & GOK).
  destruct (g_sc _ _ _ _ _ _ GOK) as [[S48 _]|(_ & LI0 & ML & NIL)]; [exfalso; change (MR st mm) with mr in S48; clear -S48 E63; lia|].
  change (MR st mm) with mr in LI0, ML.
  assert (I0 : i = 0) by (clear -Hi LI0; lia). revert IDX. subst i. intros IDX.
  rewrite Z.mul_0_r, Z.add_0_r in Sc. rewrite Z.mul_0_r in *.
  thaw TOP. destruct (TOP ML) as [Bz GE].
  pose proof (g_facts x0 st L BL LS c mm 0 0 (m_maplen mr * 4096) INV Hs E63 eq_refl) as (_ & EC & _ & _ & _ & STR & _ & rg & Hrg & Krg & EON).
  rewrite Fc, Hr in Hrg. injection Hrg as <-.
  change (get_stride (MR st mm)) with stride in STR.
  eapply evt_mono; [| intros msX HX; right; split; [exact E63| split; [reflexivity| split; [clear -OFF; lia| exact HX]]]].
  rewrite E63.

  eapply evt_cut.
  { eapply (rrealloc_B_mm ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp _ _ _ _ t4'' t5 t6 s0 (wz (conc st mm)) (Z_to_bv 64 A) (Z_to_bv 64 n') _ _ _ _ _
              _ s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m1 n'); [reflexivity| exact N| exact MI1]. }
  intros ms4 ->.

  replace (m_last_idx mr + 32 * m_freeable mr + 64 * 63 + 4096 * m_maplen mr) with ((m_last_idx mr + 32 * m_freeable mr + 4032) + 4096 * m_maplen mr) by lia.
  replace (conc st bm + 16 + 0) with (conc st bm + 16) by lia.
  pose proof (go_freeable _ _ _ GO) as GFB. change (get_meta_rec st mm) with mr in GFB.
  pose proof (go_maplen _ _ _ GO) as GML. change (get_meta_rec st mm) with mr in GML.
  eapply evt_mono.
  { eapply (rrealloc_mm_pre ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp (Z_to_bv 64 E) t4'' t5 t6 s0 (wz (conc st mm)) _ _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m1
              A (conc st bm) n' off (m_last_idx mr + 32 * m_freeable mr + 4032) (m_maplen mr)).
    - rewrite HAP. unfold P. rewrite Cbm, Sc. unfold UNIT. lia.
    - exact OFF.
    - unfold MMAP_THRESHOLD in N. lia.
    - rewrite Cbm. thaw RBAL. clear -RB0 RBAL B0. Z.div_mod_to_equations. lia.
    - rewrite Cbm, Bz, Z.add_0_r. replace (4096 * m_maplen mr) with (m_maplen mr * 4096) by lia. rewrite EON. exact RBC.
    - clear -LI0 GFB. lia.
    - clear -ML GML. lia.
    - exact MI1. }
  cbv beta. intros msX HX.
  exists m1, r. split.
  { unfold rrmm_m1. split; [exact FR1|]. split; [exact ST1|]. split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1| exact MR1]. }
  split; [exact Hrc|]. split; [exact Kr|]. split; [rewrite <- EON; lia|]. split; [rewrite Cc, Sc; lia|].
  cbv zeta. replace (4096 * m_maplen mr) with (m_maplen mr * 4096) in HX by lia.
  fold (mremap_needed off n') in HX.
  destruct HX as [[EQ HJ]|[NE HC]]; [left| right].
  - split; [exact EQ|]. unfold rrmm_join in HJ. subst msX. unfold rrmm_at.
    rewrite Cbm, Bz, Z.add_0_r. do 17 eexists. reflexivity.
  - split; [exact NE|]. unfold rrmm_call in HC. subst msX. unfold rrmm_callst.
    rewrite Cbm, Bz, Z.add_0_r. replace (E - res) with (A + n) by (unfold E, P in *; clear -RESEQ HAP; lia). do 7 eexists. reflexivity. }
Qed.
End MM.

Lemma live_range_lr r b l : region_live_range r = (b, l) -> b = lr_lo r /\ b + l = r_base r + round_up_pg (r_len r).
Proof. unfold region_live_range, lr_lo. destruct (r_kind r); intros E; injection E as <- <-; unfold PGSZ; lia. Qed.

Lemma mremap_full_ctx st c off n n' dst : ctx (mremap_full st c off n n' dst) = ctx st.
Proof.
  rewrite <- (ctx_strip (mremap_full st c off n n' dst)), <- (ctx_strip st).
  destruct (s_slots st !! c) as [[g i]|] eqn:Hs.
  - rewrite (strip_mremap_full st c off n n' dst g i Hs). reflexivity.
  - unfold mremap_full. rewrite Hs. reflexivity.
Qed.

Lemma mremap_full_regions st c off n n' dst g i : s_slots st !! c = Some (g, i) ->
  s_regions (mremap_full st c off n n' dst) = <[fst c := mkRegion RKGroup dst (mremap_needed off n')]> (s_regions st).
Proof.
  intros Hs. rewrite <- (s_regions_strip (mremap_full st c off n n' dst)), (strip_mremap_full st c off n n' dst g i Hs). reflexivity.
Qed.

Lemma brk_link_mremap_full st c off n n' dst g i pbrk : s_slots st !! c = Some (g, i) ->
  match c_brk (ctx st) with BrkLive brid _ => brid <> fst c | _ => True end ->
  brk_link st pbrk -> brk_link (mremap_full st c off n n' dst) pbrk.
Proof.
  intros Hs NB BL. unfold brk_link in *. rewrite mremap_full_ctx. destruct (c_brk (ctx st)) as [| |brid boff]; [exact I| exact I|].
  unfold conc, get_region in *. cbn [fst snd] in *. rewrite (mremap_full_regions st c off n n' dst g i Hs), lookup_insert_ne by (intros E; apply NB; symmetry; exact E). exact BL.
Qed.

Lemma rset_size_mem_pres C m0 m P E n k :
  rpres_except C m0 m -> 3 <= P -> P + n <= E -> E + 1 <= 2^64 -> 0 <= n ->
  (forall x, P - 3 <= x < P \/ P + n <= x < E -> C x) ->
  rpres_except C m0 (rset_size_mem m P E n k).
Proof.
  intros PE P3 PN ET N0 HC. unfold rset_size_mem. cbv zeta.
  assert (L4 : forall w, length (le4 w) = 4%nat) by (intros; reflexivity).
  set (r := E - P - n).
  set (mF := if r =? 0 then _ else _).
  assert (PF : rpres_except C m0 mF).
  { subst mF. destruct (Z.eqb_spec r 0); [exact PE|]. apply rpres_write; [exact PE| lia| cbn; lia| cbn; intros x Hx; apply HC; right; lia]. }
  clearbody mF.
  set (mG := if 5 <=? r then _ else _).
  assert (PG : rpres_except C m0 (fst mG)).
  { subst mG. destruct (Z.leb_spec 5 r); cbn [fst snd].
    - apply rpres_write; [| lia| rewrite L4; lia| rewrite L4; intros x Hx; apply HC; right; lia].
      apply rpres_write; [exact PF| lia| cbn; lia| cbn; intros x Hx; apply HC; right; lia].
    - exact PF. }
  clearbody mG. destruct mG as [mg r2]. cbn [fst snd] in PG |- *.
  apply rpres_write; [exact PG| lia| cbn; lia| cbn; intros x Hx; apply HC; left; lia].
Qed.

Definition rrmm_spec_post {HGW : HasGuard} {HCEIL : HasCeiling} (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s' : PState) (LB : list block) (k : bptr) (A' sz n' lo : Z) (old : list byte) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' junk,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A') a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
    /\ (forall B, rauxv_ok m B -> bv_unsigned sp <= B -> rauxv_ok m' B)
    /\ (forall ev, rw_cells rsegs m RERRNO [C4 ev] -> rw_cells rsegs m' RERRNO [C4 ev])
    /\ rheap_pres (lb_remove k LB) (bv_unsigned sp) m m'
    /\ RHEAP s' ((k, A', n') :: lb_remove k LB) m'
    /\ rblock_range A' n'
    /\ rw_cells rsegs m' A' [CB (Z.to_nat n') (firstn (Z.to_nat (Z.min n' sz)) old ++ junk)].

Section FIN.
Context {HGW : HasGuard}.
Context {HCEIL : HasCeiling}.
Variables (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (ra sp : word).
Variables (s : PState) (LB LB0 : list block) (lo : Z) (st : mstate) (k : bptr) (A sz : Z) (old : list byte).
Variables (m m1 m2 : mem) (g : aptr) (rg : region) (off n' dst : Z).
Let c : cptr := fst k.
Let rid : N := fst c.
Let nn := mremap_needed off n'.
Let on := m_maplen (get_meta_rec st g) * 4096.
Let oldb := r_base rg.
Let M := Z.min on nn.
Let GA := conc st g.
Let P' := dst + 16 + UNIT * off.
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis SLO : lo <= bv_unsigned sp - 64.
Hypothesis PERM : Permutation LB0 LB.
Hypothesis Hst : strip st = ps_m s.
Hypothesis BL : brk_link st (ps_brk s).
Hypothesis AR : RAREACH st LB0.
Hypothesis Hin : In (k, A, sz) LB.
Hypothesis Hoff : 0 <= off.
Hypothesis HA : A = conc st c + UNIT * off.
Hypothesis Hs : (s_slots st) !! c = Some (g, 0).
Hypothesis SC : m_sizeclass (get_meta_rec st g) = 63.
Hypothesis Hrg : (s_regions st) !! rid = Some rg.
Hypothesis N : MMAP_THRESHOLD <= n' < 2^32.
Hypothesis CELLS : rw_cells rsegs m A [CB (Z.to_nat sz) old].
Hypothesis PE01 : rpres_except (fun a => lo <= a < bv_unsigned sp) m m1.
Hypothesis HMR : rmrep st m1.
Hypothesis OK : cremap_ok (strip st) c dst nn.
Hypothesis H2a : forall a, 0 <= a < 2^64 -> ~ (oldb <= a < oldb + on) -> ~ (dst <= a < dst + nn) -> m2 (wa a) = m1 (wa a).
Hypothesis H2b : forall o, 0 <= o < M -> m2 (wa (dst + o)) = m1 (wa (oldb + o)).
Hypothesis H2c : forall o, M <= o < nn -> m2 (wa (dst + o)) = Some (b8 0).
Hypothesis MI2 : mem_inv rsegs m2.
Hypothesis FR2 : rw_cells rsegs m2 (bv_unsigned sp + -64) (rr_frame s6 s5 s4 s3 s2 s1 s0 ra).
Hypothesis ST2 : stk rsegs m2 lo (bv_unsigned sp + -64).

Let s' : PState := set_m (cremap (ps_m s) rid g dst nn) s.

#[using="LB0 A m1 rg on oldb M LO SLO PERM Hst BL AR Hin Hoff HA Hs SC Hrg N CELLS PE01 HMR OK H2a H2b H2c MI2 FR2 ST2"] Theorem rrealloc_mm_finish : forall ms,
  rrmm_at sp gp tp s7 s8 s9 s10 s11 F fc m2 (wz GA) nn n' dst off ms ->
  evt rsegs (rrmm_spec_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s' LB k P' sz n' lo old m) ms.
Proof.
  intros ms HAT. pose proof N as NT. unfold MMAP_THRESHOLD in N.
  assert (Eon : on = m_maplen (get_meta_rec st g) * 4096) by reflexivity.
  assert (EMn : M = Z.min on nn) by reflexivity.
  assert (EP' : P' = dst + 16 + UNIT * off) by reflexivity.
  assert (Eold : oldb = r_base rg) by reflexivity.

  assert (Hin0 : In (k, A, sz) LB0) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hin]).
  pose proof (areach_cinv_proof _ _ AR) as C. pose proof (ci_ticks _ _ C) as TK.
  pose proof (remap_facts st LB0 (k, A, sz) m1 g off n' dst AR Hin0 HA Hs SC HMR OK) as RFX.
  change (blk_slot (k, A, sz)) with c in RFX. change (blk_addr (k, A, sz)) with A in RFX. change (blk_size (k, A, sz)) with sz in RFX. fold rid in RFX.
  destruct RFX as (rg' & gh & Hrg' & Krg & EON & ON0 & EC & MEMg & GRP & GM & NOGRP & GSLOT & (PCTX & PMET & PAR & PGM) & _ & FIT & SZ0 & CC & HAB & OFF & STR).
  rewrite Hrg in Hrg'. injection Hrg' as <-. fold on in EON, ON0, STR.
  pose proof OK as (D0 & DA & NA & N2 & NL & DC & RESV & DISJ0). unfold PGSZ, LEN_MAX in DA, NA, N2, NL.
  pose proof HMR as (WF & _). pose proof WF as (Hres & CE & WR & DJ & WA & WG).
  change (s_ceil (strip st)) with (s_ceil st) in DC. rewrite CE in DC. ceil_facts.
  assert (RESV' : ranges_free p0_reserved dst nn = true) by (rewrite <- Hres; change (s_reserved st) with (s_reserved (strip st)); exact RESV).
  assert (DISJ : forall k2 r2, (s_regions st) !! k2 = Some r2 -> k2 <> rid -> dst + nn <= lr_lo r2 \/ r_base r2 + round_up_pg (r_len r2) <= dst).
  { intros k2 r2 Hk2 NE. specialize (DISJ0 k2 r2). change (s_regions (strip st)) with (s_regions st) in DISJ0. specialize (DISJ0 Hk2 NE).
    destruct (region_live_range r2) as [b2 l2] eqn:ELR. destruct (live_range_lr _ _ _ ELR) as [E1 E2]. lia. }

  destruct (areach_inv _ st LB0 AR) as (L & LS & BLK & INV & _ & _ & _ & CR).
  destruct (Forall2_In_l _ _ _ _ CR Hin0) as (kk & Hk & (K1 & K2 & K3)).
  destruct kk as [[c0 bo] n0]. change (blk_slot (k, A, sz)) with c in K1. change (blk_addr (k, A, sz)) with A in K3. change (blk_size (k, A, sz)) with sz in K2. cbn [bslot boff bsize fst snd] in K1, K2, K3. subst c0 n0.
  assert (bo = off) as -> by (rewrite HA in K3; unfold UNIT in K3; clearbody c; lia).
  destruct (block_facts x0 st L BLK LS INV c off sz Hk) as (g' & bm & i & ai & aa & ar & ka & BF).
  pose proof (bf_slot _ _ _ _ _ _ _ _ _ _ _ BF) as Hs'. rewrite Hs in Hs'. injection Hs' as <- <-.
  pose proof (bf_shadow _ _ _ _ _ _ _ _ _ _ _ BF) as SHD. unfold blk_shadow_ok in SHD. cbn [bslot boff bsize fst snd] in SHD. fold rid in SHD.
  rewrite EC in SHD. cbn [snd] in SHD. change (MR st g) with (get_meta_rec st g) in SHD. rewrite STR in SHD.
  destruct SHD as (O4 & O3 & _).
  set (res := 16 + (on - UNIT) - IB - (16 + UNIT * off) - sz) in O3.
  set (kb := 0 + 32 * Z.min res 5) in O3.
  pose proof (bf_li _ _ _ _ _ _ _ _ _ _ _ BF) as LI. pose proof (bf_maplen _ _ _ _ _ _ _ _ _ _ _ BF) as ML0.
  pose proof HMR as (_ & CX & GL & ARR & GR & SH).
  assert (RD1 : forall o v, 0 <= o < on -> cell_read (get_shadow st rid) o = Known v -> m1 (wa (oldb + o)) = Some (b8 v) /\ 0 <= v < 256).
  { intros o v Ho Hc. destruct (SH rid rg Hrg Krg) as [HW HB]. rewrite <- EON in HB. destruct (HB o v Ho Hc) as [(_ & _ & Bt) Hv]. split; [| exact Hv].
    specialize (Bt 0%nat ltac:(cbn; lia)). cbn [nth_error] in Bt. rewrite Z.add_0_r in Bt. unfold mrd in Bt. fold oldb in Bt.
    destruct (m1 (wa (oldb + o))) as [b|] eqn:Eb; [congruence|]. exfalso.
    destruct (WR _ _ Hrg) as (RB0 & _ & _ & RBC & RF). rewrite <- EON in RF, RBC. pose proof (rreserved_disjoint1 _ _ RF ON0) as DR. fold oldb in DR, RB0, RBC. ceil_facts.
    rewrite p0_seg_rom_none2 in Bt; [discriminate|]. rewrite wa_unsigned by lia. lia. }
  destruct (WR _ _ Hrg) as (RB0 & RBAL & RL0 & RBC & RF). rewrite <- EON in RF, RBC. fold oldb in RB0, RBAL, RBC, RF. ceil_facts.
  assert (KB : m1 (wa (oldb + (16 + UNIT * off - 3))) = Some (b8 kb) /\ 0 <= kb < 256).
  { apply RD1; [unfold UNIT, IB in *; lia| exact O3]. }
  destruct KB as [KB KBR].

  destruct GSLOT as (a0 & ar0 & k0 & Ha0 & Hk0 & Eg).
  destruct (rarea_conc st a0 ar0 WF Ha0) as (rar & Hrar & Ca & Sa0 & Sa1 & SaL & NK & AB0 & ABAL & ABC).
  pose proof (rarea_lr_lo st a0 ar0 rar WF Ha0 Hrar) as ALO.
  assert (EGA : GA = r_base rar + snd a0 + AREA_HDR + META_SIZE * k0).
  { unfold GA. rewrite Eg, conc_aadd by (cbn; rewrite Hrar; eauto). rewrite Ca. lia. }
  assert (NEra : fst a0 <> rid) by (intros E; rewrite E, Hrg in Hrar; injection Hrar as <-; exact (NK Krg)).
  pose proof (DISJ _ _ Hrar NEra) as DGr. pose proof (DJ _ _ _ _ Hrar Hrg NEra) as DGo. rewrite (lr_lo_group rg Krg) in DGo. fold oldb in DGo. rewrite <- EON in DGo.
  ceil_facts; unfold AREA_HDR, META_SIZE, NSLOTS in *.
  pose proof (rmrep_meta_chunk st m1 g HMR ltac:(exists a0, ar0, k0; auto)) as MC1. fold GA in MC1.
  assert (AGm : forall a, GA <= a < GA + 40 -> m2 (wa a) = m1 (wa a)).
  { intros a Ha. apply H2a; [lia| |]; clear - Ha EGA DGr DGo ALO Sa0 Sa1 Hk0 AB0; intros X; lia. }
  assert (MC2 : rw_cells rsegs m2 GA (meta_cells st (get_meta_rec st g))).
  { eapply rrw_cells_agree'; [exact MC1|]. intros a Ha. apply AGm. cbn in Ha. exact Ha. }
  pose proof (rw_cells_read rsegs m2 GA _ 32 (C8 (wz (meta_word (get_meta_rec st g)))) MC2 eq_refl) as RMW. cbn [csize cbytes] in RMW.
  pose proof MC2 as [_ WG40]. cbn [cells_size csize meta_cells Nat.add] in WG40.

  pose proof (g_facts x0 st L BLK LS c g 0 0 on INV Hs SC eq_refl) as (_ & _ & LI0 & MLnz & _).
  change (MR st g) with (get_meta_rec st g) in LI0, MLnz.
  assert (HST : hosts st bm g) by (exists ai; exact (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF)).
  pose proof (ci_gmetas _ _ C bm g HST) as GO.
  pose proof (go_freeable _ _ _ GO) as GFB. pose proof (go_maplen _ _ _ GO) as GML.
  set (mr := get_meta_rec st g) in *.
  assert (MW : meta_word mr = 4064 + 4096 * m_maplen mr) by (unfold meta_word; rewrite LI0, GFB, SC; lia).
  assert (ML51 : 0 <= nn / 4096 < 2^51) by (clearbody nn; clear - NL N2; Z.div_mod_to_equations; lia).
  assert (MW' : meta_word (m_set_maplen (nn / 4096) mr) = 4064 + nn).
  { unfold meta_word, m_set_maplen. cbn [m_last_idx m_freeable m_sizeclass m_maplen]. rewrite LI0, GFB, SC.
    change (2 ^ 52 - 1) with (Z.ones 52). rewrite Z.land_ones by lia. rewrite Z.mod_small by lia. clearbody nn. clear - NA ML51. Z.div_mod_to_equations. lia. }
  assert (MWL : Z.lor (Z.land (meta_word mr) 4095) nn = meta_word (m_set_maplen (nn / 4096) mr)).
  { rewrite MW', MW. change 4095 with (Z.ones 12). rewrite Z.land_ones by lia.
    replace ((4064 + 4096 * m_maplen mr) mod 2 ^ 12) with 4064 by (change (2^12) with 4096; clear - GML; Z.div_mod_to_equations; lia).
    replace nn with (nn / 4096 * 2 ^ 12) at 1 by (change (2^12) with 4096; clearbody nn; clear - NA N2; Z.div_mod_to_equations; lia).
    rewrite (lor_small_shl (nn / 4096) 12 4064) by lia. change (2^12) with 4096. clearbody nn. clear - NA N2; Z.div_mod_to_equations; lia. }
  assert (MWR : 0 <= meta_word mr < 2^64) by (rewrite MW; clear - GML; lia).

  assert (NG : n' + UNIT * off + UNIT + IB <= nn < n' + UNIT * off + UNIT + IB + 4096).
  { unfold nn, mremap_needed. pose proof (round_up_pg_spec (n' + UNIT * off + UNIT + IB)). lia. }
  pose proof (round_up_pg_ge (r_len rg)) as RUP. pose proof (round_up_pg_ge (r_len rar)) as RUPa.
  unfold UNIT, IB in *.
  assert (D16 : 4096 <= dst) by (clear - D0 DA; Z.div_mod_to_equations; lia).
    assert (MGE1 : 16 + 16 * off + n' + 4 <= nn) by (clear - NG; lia).
  assert (MGE2 : 16 + 16 * off + sz + 4 <= on) by (clear - FIT STR; lia).
  assert (MGE3 : M <= nn /\ M <= on) by (clear - EMn; lia).
  assert (MGE4 : 16 + 16 * off <= M) by (clear -EMn MGE1 MGE2 SZ0 N; lia).
  assert (MGE0 : 16 + 16 * off + Z.min n' sz + 4 <= M) by (clear -EMn MGE1 MGE2; lia).
  assert (MGE : 16 + 16 * off + Z.min n' sz + 4 <= M /\ 16 + 16 * off + n' + 4 <= nn /\ 16 + 16 * off + sz + 4 <= on /\ M <= nn /\ M <= on /\ 16 + 16 * off <= M) by (clear - MGE0 MGE1 MGE2 MGE3 MGE4; lia).
  assert (OLDSOME : forall i0, 0 <= i0 < on -> exists b, m1 (wa (oldb + i0)) = Some b).
  { intros i0 Hi. destruct (SH rid rg Hrg Krg) as [(_ & _ & HWi) _]. rewrite <- EON in HWi. specialize (HWi i0 Hi). unfold wview in HWi. fold oldb in HWi.
    pose proof (rreserved_disjoint1 _ _ RF ON0) as DR.
    destruct (m1 (wa (oldb + i0))) as [b|] eqn:Em; [exists b; reflexivity| exfalso; apply HWi].
    rewrite p0_find_segment_none2; [reflexivity| lia| rewrite wa_unsigned by lia; clear - DR Hi RB0 RBC CEILB CEILA; lia]. }
  assert (W2 : wr_at rsegs m2 dst nn).
  { split; [lia|]. split; [lia|]. intros i0 Hi. unfold wview.
    destruct (Z_lt_le_dec i0 M) as [LT|GE].
    - rewrite H2b by lia. destruct (OLDSOME i0 ltac:(lia)) as [b ->]. discriminate.
    - rewrite H2c by lia. discriminate. }
  assert (BK : bytes_at rsegs m2 (P' - 3) [b8 kb]).
  { split; [unfold P'; lia|]. split; [unfold P'; cbn; lia|]. intros i0 Hi. cbn in Hi. assert (i0 = 0%nat) as -> by lia. cbn [nth_error Z.of_nat].
    rewrite Z.add_0_r. unfold mrd. replace (P' - 3) with (dst + (16 + 16 * off - 3)) by (unfold P'; lia). rewrite H2b by lia. rewrite KB. reflexivity. }
  pose proof (rreserved_disjoint1 _ _ RESV' ltac:(lia)) as DRd.
  pose proof (rreserved_disjoint1 _ _ RF ON0) as DRo.
  destruct (WR _ _ Hrar) as (_ & _ & _ & _ & RFa). pose proof (rreserved_disjoint1 _ _ RFa ltac:(lia)) as DRa.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.

  destruct HAT as (ra' & t0 & t1 & t2 & a0' & a3 & a4 & a5 & a6 & a7 & s2' & s5' & s6' & t3 & t4 & t5 & t6 & ->).
  eapply evt_mono.
  { eapply (rrealloc_mm_tail ra' sp gp tp t0 t1 t2 a0' a3 a4 a5 a6 a7 s2' s5' s6' s7 s8 s9 s10 s11 t3 t4 t5 t6 (wz GA) ra s0 s1 s2 s3 s4 s5 s6 F fc m2
              lo GA dst nn (meta_word mr) off n' kb).
    - apply wz_unsigned. lia.
    - exact MI2.
    - exact RMW.
    - exact MWR.
    - eapply (F_malloc_free.wr_at_sub rsegs m2 _ _ (GA + 16) 24 WG40); lia.
    - eapply (F_malloc_free.wr_at_sub rsegs m2 _ _ _ _ W2); unfold UNIT, IB; lia.
    - unfold UNIT. rewrite <- EP'. exact BK.
    - exact KBR.
    - unfold UNIT, IB. clear - DGr DGo ALO Sa0 Sa1 Hk0 AB0 EGA NG OFF D16 CEILB CEILA. lia.
    - lia.
    - exact FR2.
    - exact ST2.
    - unfold IB. lia.
    - exact SLO.
    - lia.
    - exact Hoff.
    - lia.
    - unfold UNIT, IB. lia.
    - unfold UNIT, IB. lia.
    - lia.
    - exact NA. }
  cbv beta. intros msf (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m' & -> & EM & MI' & ST').
  unfold UNIT, IB in EM.

  assert (RES0 : 0 <= get_stride mr - 4 - 16 * off - sz) by (clear - FIT; lia).
  pose proof (rremap_mrep st m1 m2 c g rg off sz n' dst HMR TK Hrg Krg EON ON0 MEMg NOGRP ltac:(exists a0, ar0, k0; auto) PCTX PMET PAR PGM
                D0 DA NA N2 DC RESV' DISJ H2a H2b H2c Hs ltac:(rewrite EC; reflexivity) Hoff ltac:(lia) RES0) as [MRz TKz].
  fold nn in MRz, TKz. change (get_meta_rec st g) with mr in MRz.
  assert (EMEM : rset_size_mem (write_to_mem (write_to_mem (write_to_mem m2 (wa (GA + 16)) (le8 (wz dst))) (wa (GA + 32)) (le8 (wz (meta_word (m_set_maplen (nn / 4096) mr))))) (wa (dst + nn - 4)) [b8 0])
                   (dst + 16 + 16 * off) (dst + nn - 4) n' (0 + 32 * Z.min (get_stride mr - 4 - 16 * off - sz) 5) = m').
  { rewrite EM. unfold rrmm_mem. rewrite MWL. unfold kb, res. rewrite STR. repeat (f_equal; try lia). }
  rewrite EMEM in MRz. clear EMEM.

  set (C2 := fun a : Z => lo <= a < bv_unsigned sp \/ GA + 16 <= a < GA + 40 \/ P' - 3 <= a < P' \/ P' + n' <= a < dst + nn).
  assert (L8 : forall w, length (le8 w) = 8%nat) by (intros; reflexivity).
  assert (PE2 : rpres_except C2 m2 m').
  { rewrite EM. unfold rrmm_mem. apply rset_size_mem_pres; [| lia| lia| lia| lia| intros x Hx; unfold C2; rewrite EP'; clear - Hx; lia].
    apply rpres_write; [| lia| cbn; lia| cbn; intros x Hx; unfold C2; clear - Hx MGE1 EP'; lia].
    apply rpres_write; [| lia| rewrite L8; lia| rewrite L8; intros x Hx; unfold C2; clear - Hx; lia].
    apply rpres_write; [apply rpres_except_refl| lia| rewrite L8; lia| rewrite L8; intros x Hx; unfold C2; clear - Hx; lia]. }
  set (Cbig := fun a : Z => lo <= a < bv_unsigned sp \/ oldb <= a < oldb + on \/ dst <= a < dst + nn \/ GA + 16 <= a < GA + 40).
  assert (PE12 : rpres_except Cbig m1 m2).
  { intros a Ha NC. assert (E : m2 (wa a) = m1 (wa a)) by (apply H2a; [exact Ha| intros X; apply NC; unfold Cbig; clear - X; lia| intros X; apply NC; unfold Cbig; clear - X; lia]).
    split; [exact E|]. unfold wview. rewrite E. exact (fun H => H). }
  assert (PE : rpres_except Cbig m m').
  { eapply rpres_except_trans; [eapply rpres_except_mono; [exact PE01| intros a X; unfold Cbig; left; exact X]|].
    eapply rpres_except_trans; [exact PE12|]. eapply rpres_except_mono; [exact PE2|]. intros a X. unfold Cbig. unfold C2 in X. clear - X EP' MGE1 OFF N. lia. }

  pose proof (ci_nodup _ _ C) as NDS.
  assert (NDSL : List.NoDup (map blk_slot LB)) by (eapply NoDup_map_perm; [exact PERM| exact NDS]).
  pose proof (lb_remove_lbrm LB k A sz NDSL Hin) as ELB.
  assert (NFP : forall a, 0 <= a < 2^64 -> rclient_addr (lb_remove k LB) (bv_unsigned sp) a -> ~ Cbig a).
  { intros a Ha CA X. unfold Cbig in X.
    destruct CA as [CA|[[CA NS]|(b' & Hb' & Hab)]].
    - clear - CA X LO SLO RBC DC EGA ABC Sa0 Sa1 Hk0 CEILB CEILA. lia.
    - clear - CA X LO DRo DRd DRa EGA Sa0 Sa1 Hk0 ALO RUPa CEILB CEILA. lia.
    - rewrite ELB in Hb'. pose proof (In_lbrm_perm _ _ _ _ (Permutation_sym PERM) Hb') as Hb0. unfold lbrm in Hb0.
      apply In_filter_iff in Hb0. destruct Hb0 as [Hb0 NEQ]. change (blk_slot (k, A, sz)) with c in NEQ.
      assert (NEQ' : blk_slot b' <> c) by (intros EE; rewrite EE, aptr_eqb_refl in NEQ; cbn in NEQ; congruence).
      destruct (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) b' Hb0) as [(r' & Hr' & Kr' & A16' & AEND' & _ & _) _ _].
      destruct (proj1 (List.Forall_forall _ _) (ci_blks _ _ C) b' Hb0) as [(g2 & i2 & bb2 & SL2 & _) _ SZ2].
      assert (NEr : fst (blk_slot b') <> rid).
      { intros EQ. destruct (rid_slots x0 st L BLK LS c g dst nn on INV Hs SC eq_refl D0 _ _ _ SL2 EQ) as [E2 _]. exact (NEQ' E2). }
      pose proof (DJ _ _ _ _ Hr' Hrg NEr) as D1. rewrite (lr_lo_group r' Kr'), (lr_lo_group rg Krg) in D1. fold oldb in D1. rewrite <- EON in D1.
      pose proof (DISJ _ _ Hr' NEr) as D2. rewrite (lr_lo_group r' Kr') in D2.
      assert (NEa : fst (blk_slot b') <> fst a0) by (intros EQ; rewrite EQ, Hrar in Hr'; injection Hr' as ->; exact (NK Kr')).
      pose proof (DJ _ _ _ _ Hr' Hrar NEa) as D3. rewrite (lr_lo_group r' Kr') in D3.
      destruct (WR _ _ Hr') as (_ & _ & _ & RBC' & _).
      clear - X Hab D1 D2 D3 A16' AEND' EGA ALO Sa0 Sa1 Hk0 SZ2 LO RBC' SLO.
      unfold in_block, blk_addr, blk_size in *. lia. }

  assert (Wn : wr_at rsegs m' dst nn).
  { pose proof MRz as (_ & _ & _ & _ & _ & SHz).
    destruct (SHz rid (mkRegion RKGroup dst nn)) as [HWz _]; [| reflexivity|].
    - rewrite (mremap_full_regions st c off sz n' dst g 0 Hs). fold rid nn. apply lookup_insert_eq.
    - cbn [r_base r_len] in HWz. rewrite (round_up_pg_id nn) in HWz by (unfold PGSZ; exact NA). exact HWz. }

  assert (LENold : length old = Z.to_nat sz) by (destruct CELLS as [[WFc _] _]; cbn in WFc; exact (proj1 WFc)).
  destruct CELLS as [[_ OLD] _]. cbn [cells_bytes cbytes app] in OLD. rewrite app_nil_r in OLD.
  set (mn := Z.to_nat (Z.min n' sz)). assert (Emn : mn = Z.to_nat (Z.min n' sz)) by reflexivity.
  assert (BS1 : bytes_at rsegs m' P' (firstn mn old)).
  { destruct OLD as (_ & _ & OB). split; [lia|]. split; [rewrite firstn_length; lia|]. intros i0 Hi. rewrite firstn_length in Hi.
    rewrite <- (firstn_skipn mn old) in OB. specialize (OB i0 ltac:(rewrite app_length, firstn_length; lia)). rewrite nth_error_app1 in OB by (rewrite firstn_length; lia).
    rewrite <- OB. unfold mrd.
    assert (E1 : m' (wa (P' + Z.of_nat i0)) = m2 (wa (P' + Z.of_nat i0))).
    { apply PE2; [lia|]. unfold C2. clear - Hi Emn EP' MGE1 DC LO DGr DGo ALO Sa0 Sa1 Hk0 AB0 EGA NG OFF D16 N SZ0. intros X. lia. }
    assert (E2 : m2 (wa (P' + Z.of_nat i0)) = m1 (wa (A + Z.of_nat i0))).
    { replace (P' + Z.of_nat i0) with (dst + (16 + 16 * off + Z.of_nat i0)) by lia. rewrite H2b by (clear - Hi Emn MGE0 N SZ0 OFF; lia). f_equal. rewrite HAB. fold oldb. f_equal. lia. }
    assert (E3 : m1 (wa (A + Z.of_nat i0)) = m (wa (A + Z.of_nat i0))).
    { apply PE01; [lia|]. clear - Hi Emn HAB MGE2 RBC LO N SZ0. intros X. lia. }
    destruct (OLDSOME (16 + 16 * off + Z.of_nat i0) ltac:(clear - Hi Emn MGE2 OFF N SZ0; lia)) as [b Eb].
    assert (Emb : m (wa (A + Z.of_nat i0)) = Some b).
    { rewrite <- E3. rewrite HAB. fold oldb. replace (oldb + 16 + 16 * off + Z.of_nat i0) with (oldb + (16 + 16 * off + Z.of_nat i0)) by lia. exact Eb. }
    rewrite E1, E2, E3, Emb. reflexivity. }
  assert (WRP : wr_at rsegs m' P' n') by (eapply (F_malloc_free.wr_at_sub rsegs m' _ _ P' n' Wn); clear - EP' MGE1 OFF N; lia).
  destruct (rwr_at_bytes_exist m' P' n' WRP ltac:(lia) ltac:(clear - DRd EP' MGE1 OFF N; lia)) as (bs & LBS & BS).
  assert (BS2 : bytes_at rsegs m' (P' + Z.of_nat mn) (skipn mn bs)).
  { rewrite <- (firstn_skipn mn bs) in BS. apply bytes_at_app in BS. destruct BS as [_ BS]. rewrite firstn_length, LBS in BS.
    replace (Z.of_nat (mn `min` Z.to_nat n')) with (Z.of_nat mn) in BS by (clear - Emn N SZ0; lia). exact BS. }

  unfold rrmm_spec_post. do 14 eexists. exists m', (skipn mn bs). split; [rewrite EP'; reflexivity|].
  split; [exact MI'|]. split; [exact ST'|]. split; [| split; [| split; [| split; [| split]]]].
  -   intros B AV HB. eapply rauxv_ok_pres; [exact AV| exact PE| |]; intros a Ha; unfold Cbig; unfold RAUXV_CELL in Ha;
      clear - Ha HB SLO LO RBC DC DRo DRd DRa EGA ALO Sa0 Sa1 Hk0 ABC RUPa CEILB CEILA; lia.
  -   intros ev ERR. eapply rpres_except_rw_cells; [exact PE| exact ERR|]. cbn. intros a Ha. unfold Cbig. unfold RERRNO in Ha.
      clear - Ha SLO LO RBC DC DRo DRd DRa EGA ALO Sa0 Sa1 Hk0 ABC RUPa CEILB CEILA; lia.
  -   intros a Ha CA. apply PE; [exact Ha|]. exact (NFP a Ha CA).
  -
    exists (mremap_full st c off sz n' dst), ((k, P', n') :: lbrm LB0 (k, A, sz)). split; [| split; [| split; [exact MRz| split]]].
    + rewrite ELB. apply perm_skip. apply lbrm_perm. exact PERM.
    + rewrite (strip_mremap_full st c off sz n' dst g 0 Hs). unfold s'. cbn [ps_m set_m]. rewrite <- Hst. reflexivity.
    + unfold s'. cbn [ps_brk set_m]. eapply (brk_link_mremap_full st c off sz n' dst g 0 (ps_brk s) Hs); [| exact BL].
      destruct PCTX as (_ & _ & _ & _ & _ & _ & PB). exact PB.
    + change ((k, P', n') :: lbrm LB0 (k, A, sz)) with ((blk_id (k, A, sz), P', n') :: lbrm LB0 (k, A, sz)). rewrite EP'.
      change c with (blk_slot (k, A, sz)). change sz with (blk_size (k, A, sz)) at 1.
      apply (areach_mremap st LB0 (k, A, sz) off n' dst g rg AR Hin0 Hoff HA ltac:(clear - N; lia) Hs SC Hrg OK).
  -   ceil_facts; unfold rblock_range. rewrite EP'. repeat split; try (clear - D16 DC MGE1 OFF N DRd CEILB CEILA; lia).
    clear - DA OFF. Z.div_mod_to_equations. lia.
  -   split; [split|].
    + cbn. rewrite app_length, firstn_length, skipn_length, LENold, LBS. split; [clear - Emn N SZ0; lia| exact Logic.I].
    + cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_at_app. split; [exact BS1|]. rewrite firstn_length, LENold.
      replace (Z.of_nat (mn `min` Z.to_nat sz)) with (Z.of_nat mn) by (clear - Emn N SZ0; lia). exact BS2.
    + cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by lia. exact WRP.
Qed.
End FIN.

Lemma same_raw_facts {HCEIL : HasCeiling} : forall (old on nn : Z) (mx : mem),
  0 < old -> 0 < on -> 0 < nn -> old + Z.max on nn <= alloc_ceiling ->
  (old + Z.max on nn <= 0x10000 \/ 0x2a000 <= old) ->
  let m2 := mremap_same_raw old on nn mx in
  (forall a, 0 <= a < 2^64 -> ~ (old <= a < old + on) -> ~ (old <= a < old + nn) -> m2 (wa a) = mx (wa a))
  /\ (forall o, 0 <= o < Z.min on nn -> m2 (wa (old + o)) = mx (wa (old + o)))
  /\ (forall o, Z.min on nn <= o < nn -> m2 (wa (old + o)) = Some (b8 0))
  /\ (mem_inv rsegs mx -> mem_inv rsegs m2)
  /\ (forall A cs, rw_cells rsegs mx A cs -> old + Z.max on nn <= A -> rw_cells rsegs m2 A cs).
Proof.
  intros old on nn mx O0 ON0 NN0 TOP IMG m2. ceil_facts. subst m2. unfold mremap_same_raw.
  destruct (Z.ltb_spec nn on) as [LT|GE].
  - split; [| split; [| split; [| split]]].
    + intros a Ha N1 N2. apply unmaps_outside; rewrite ?wa_unsigned by lia; lia.
    + intros o Ho. apply unmaps_outside; rewrite ?wa_unsigned by lia; lia.
    + intros o Ho. exfalso. lia.
    + intros MI. apply mem_inv_unmaps; try lia. exact MI.
    + intros A cs RC HA. eapply rw_cells_unmaps_other; [| | | exact RC|]; lia.
  - destruct (Z.ltb_spec on nn) as [LT2|GE2].
    + split; [| split; [| split; [| split]]].
      * intros a Ha N1 N2. apply zeros_outside; rewrite ?wa_unsigned by lia; lia.
      * intros o Ho. apply zeros_outside; rewrite ?wa_unsigned by lia; lia.
      * intros o Ho. apply zeros_inside; rewrite ?wa_unsigned by lia; lia.
      * intros MI. apply mem_inv_zeros; try lia; [exact MI|]. intros x Hx. apply p0_ro_addr_false. lia.
      * intros A cs RC HA. eapply rw_cells_zeros_other; [| | | exact RC|]; lia.
    + assert (on = nn) as -> by lia. split; [| split; [| split; [| split]]].
      * intros; reflexivity.
      * intros; reflexivity.
      * intros; exfalso; lia.
      * intros MI; exact MI.
      * intros A cs RC _; exact RC.
Qed.

Lemma move_raw_facts {HCEIL : HasCeiling} : forall (old on dst nn : Z) (mx : mem),
  0 < old -> 0 < on -> on < nn -> 0 < dst -> old + on <= alloc_ceiling -> dst + nn <= alloc_ceiling ->
  (dst + nn <= 0x10000 \/ 0x2a000 <= dst) ->
  let m2 := mremap_move_raw old on dst nn mx in
  (forall a, 0 <= a < 2^64 -> ~ (old <= a < old + on) -> ~ (dst <= a < dst + nn) -> m2 (wa a) = mx (wa a))
  /\ (forall o, 0 <= o < Z.min on nn -> m2 (wa (dst + o)) = mx (wa (old + o)))
  /\ (forall o, Z.min on nn <= o < nn -> m2 (wa (dst + o)) = Some (b8 0))
  /\ (mem_inv rsegs mx -> mem_inv rsegs m2)
  /\ (forall A cs, rw_cells rsegs mx A cs -> alloc_ceiling <= A -> rw_cells rsegs m2 A cs).
Proof.
  intros old on dst nn mx O0 ON0 LT D0 TOPo TOPd IMG m2. ceil_facts. subst m2. unfold mremap_move_raw.
  set (mu := apply_unmaps mx [(wa old, Z_to_bv 64 on)]). set (mz := apply_zeros mu [(wa (dst + on), Z_to_bv 64 (nn - on))]).
  split; [| split; [| split; [| split]]].
  - intros a Ha N1 N2. rewrite copy_outside; rewrite ?wa_unsigned by lia; try lia.
    subst mz. rewrite zeros_outside; rewrite ?wa_unsigned by lia; try lia. subst mu. apply unmaps_outside; rewrite ?wa_unsigned by lia; lia.
  - intros o Ho. unfold apply_copy. cbn [copy_dst copy_len copy_src]. rewrite !wa_unsigned by lia.
    replace ((dst <=? dst + o) && (dst + o <? dst + on)) with true by (symmetry; apply andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
    unfold wa. f_equal. f_equal. lia.
  - intros o Ho. rewrite copy_outside; rewrite ?wa_unsigned by lia; try lia. subst mz. apply zeros_inside; rewrite ?wa_unsigned by lia; lia.
  - intros MI. apply mem_inv_copy; rewrite ?wa_unsigned by lia; try lia.
    + subst mz. apply mem_inv_zeros; try lia; [subst mu; apply mem_inv_unmaps; try lia; exact MI|]. intros x Hx. apply p0_ro_addr_false. lia.
    + intros x Hx. apply p0_ro_addr_false. lia.
  - intros A cs RC HA. ceil_facts. pose proof (rw_cells_bound _ _ _ _ RC) as [B0 B1].
    apply rw_cells_copy_other; rewrite ?wa_unsigned by lia; try lia.
    subst mz. eapply rw_cells_zeros_other; [lia| lia| lia| | lia]. subst mu. eapply rw_cells_unmaps_other; [| | | exact RC|]; lia.
Qed.
