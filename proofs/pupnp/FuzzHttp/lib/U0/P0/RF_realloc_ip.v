(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs ImgFacts.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.Malloc Require Import F_malloc_free F_malloc_fast F_malloc_enframe F_free_A MallocTree MallocKit_A MallocBlocks
  MallocFacts_A MallocFacts_B MallocFacts_inv MallocFacts_inv2 MallocFacts_inv3 Malloc_fp F_malloc_entry.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import STree Malloc MallocCtrl KInv MI_Inv MI_Ext MI_Geom MI_Pres2 MI_Read MI_WGroup MI_WFree MI_WRealloc MI_WRealloc2.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import RMallocRep RMallocTree RMallocKit_A RMallocKit_B RMallocKit_B3 RMalloc_fp RF_get_meta RF_free_A RF_free
  RF_realloc_A RF_realloc_B RF_realloc_C RF_realloc_D RF_realloc_rep.
Import ListNotations.

Local Ltac arith_atom T := lazymatch T with
  | Z.le _ _ => idtac | Z.lt _ _ => idtac | Z.ge _ _ => idtac | Z.gt _ _ => idtac
  | @eq Z _ _ => idtac | @eq nat _ _ => idtac | @eq N _ _ => idtac | @eq positive _ _ => idtac
  | le _ _ => idtac | lt _ _ => idtac | ge _ _ => idtac | gt _ _ => idtac | N.le _ _ => idtac | N.lt _ _ => idtac
  | True => idtac | False => idtac end.
Local Ltac arith_prop T := lazymatch T with
  | ?A \/ ?B => arith_prop A; arith_prop B | ?A /\ ?B => arith_prop A; arith_prop B | not ?A => arith_prop A
  | ?A <-> ?B => arith_prop A; arith_prop B | ?A -> ?B => arith_prop A; arith_prop B | _ => arith_atom T end.
Local Ltac arith_goal := lazymatch goal with |- ?G => arith_prop G end.
Local Ltac clear_props := repeat match goal with H : ?T |- _ => lazymatch type of T with Prop => clear H end end.

Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac ulia := ceil_facts; unfold UNIT, IB; lia.
Local Ltac freeze H := lazymatch type of H with ?T => change (frozen T) in H end.
Local Ltac thaw H := unfold frozen in H.

Notation RAREACH := (AREACH_from p0_reserved).

Lemma rrealloc_A1_spec {HGW : HasGuard} {HCEIL : HasCeiling} : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    st (p : aptr) r g gh ar (b3 lo hi : Z) (base : aptr),
  let sh := get_shadow st (fst p) in
  let po := snd p in
  let off16 := lo + 256 * hi in
  let idx := Z.land b3 31 in
  let mr := get_meta_rec st g in
  aadd p (- (UNIT * off16) - UNIT) = base ->
  rmrep st m -> mem_inv rsegs m ->
  (s_regions st) !! (fst p) = Some r -> r_kind r = RKGroup ->
  bv_unsigned a0 = r_base r + po -> po mod 16 = 0 ->
  16 <= po -> 16 * off16 + 16 <= po -> po + 16 <= round_up_pg (r_len r) ->
  cell_read sh (po - 4) = Known 0 -> cell_read sh (po - 3) = Known b3 ->
  cell_read sh (po - 2) = Known lo -> cell_read sh (po - 1) = Known hi ->
  (s_groups st) !! base = Some gh -> g_meta gh = Some g -> meta_slot st g -> 0 <= snd g ->
  m_mem mr = Some base ->
  (s_areas st) !! (area_of g) = Some ar -> a_check ar = c_secret (ctx st) ->
  0 <= m_avail mr < 2^32 -> 0 <= m_freed mr < 2^32 -> 0 <= c_secret (ctx st) < 2^64 ->
  0 <= m_last_idx mr < 32 -> 0 <= m_freeable mr < 2 -> 0 <= m_sizeclass mr < 64 -> 0 <= m_maplen mr < 2^40 ->
  idx <= m_last_idx mr -> Z.testbit (m_avail mr) idx = false -> Z.testbit (m_freed mr) idx = false ->
  (m_sizeclass mr < 48 -> size_class (m_sizeclass mr) * idx <= off16 < size_class (m_sizeclass mr) * (idx + 1)) ->
  (48 <= m_sizeclass mr -> m_sizeclass mr = 63) ->
  evt rsegs (rr1_post ra sp gp tp t5 t6 s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m (wz (conc st g)) (conc st base)
               (m_sizeclass mr) (meta_word mr) off16 b3 (m_last_idx mr))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x199b8) fc None m (seg_rom rsegs)).
Proof.
  intros until base. intros sh po off16 idx mr Ebase MR MI Hr Hk HP AL P16 PLO PHI C4 C3 C2 C1 Hgh Hg MS G0 Hmem Har Hchk
         AV FR SE LI FB SC ML Hidx Hav Hfr Hsc Hsc63. subst base. set (base := aadd p (- (UNIT * off16) - UNIT)) in *.
  pose proof MR as (WF & CX & GL & AR & GR & SH).
  destruct WF as (Hres & CE & WR & DISJ & WA & WG).
  destruct (WR (fst p) r Hr) as (B0 & BAL & L0 & BC & _). ceil_facts.
  destruct (rmrep_shadow_read st m (fst p) r (po - 4) 0 MR Hr Hk ltac:(lia) C4) as [R4 _].
  destruct (rmrep_shadow_read st m (fst p) r (po - 3) b3 MR Hr Hk ltac:(lia) C3) as [R3 B3].
  destruct (rmrep_shadow_read2 st m (fst p) r (po - 2) lo hi MR Hr Hk ltac:(lia) ltac:(lia) C2 ltac:(replace (po - 2 + 1) with (po - 1) by lia; exact C1)) as (R2 & LO & HI).
  rewrite <- le2_lohi in R2 by lia.
  destruct (rmrep_group_read st m base gh MR Hgh) as [RG _]. rewrite Hg in RG. cbn [pw oconc] in RG.
  pose proof (rmrep_meta_chunk st m g MR MS) as MM. fold mr in MM. unfold meta_cells in MM. rewrite Hmem in MM. cbn [pw oconc] in MM.
  pose proof (rmrep_area_check_read st m (area_of g) ar MR Har) as RA.
  pose proof (rmrep_ctx_secret_read st m MR) as RC. set (secw := rsec (c_init_done (ctx st))) in RA, RC. pose proof (bv_unsigned_in_range 64 secw) as SECWR. change (bv_modulus 64) with (2^64) in SECWR. rewrite <- (Z_to_bv_bv_unsigned secw) in RA, RC. change (Z_to_bv 64 (bv_unsigned secw)) with (wz (bv_unsigned secw)) in RA, RC.
  destruct (WG base gh Hgh) as (rb & Hrb & _ & Bb0 & _). cbn [base aadd fst] in Hrb. rewrite Hr in Hrb. inversion Hrb; subst rb.
  assert (HB : conc st base = (r_base r + po) - 16 * off16 - 16).
  { unfold base. rewrite conc_aadd by (rewrite Hr; eauto). rewrite (conc_region' st p r Hr). unfold po, UNIT. lia. }
  destruct MS as (a & ara & k & Ha & Hkk & Eg).
  destruct (WA a ara Ha) as (rg & Hrg & A0 & A1 & AAL & ANG & _).
  assert (HG : conc st g = r_base rg + snd a + (AREA_HDR + META_SIZE * k)).
  { rewrite Eg, conc_aadd by (rewrite Hrg; eauto). rewrite (conc_region' st a rg Hrg). reflexivity. }
  destruct (WR (fst a) rg Hrg) as (RB0 & RBAL & RL0 & RBC & _). ceil_facts.
  assert (Hm : (r_base rg + snd a + (AREA_HDR + META_SIZE * k)) mod 4096 = AREA_HDR + META_SIZE * k).
  { unfold AREA_HDR, META_SIZE, NSLOTS in *.
    replace (r_base rg + snd a + (24 + 40 * k)) with ((24 + 40 * k) + (snd a / 4096 + r_base rg / 4096) * 4096) by (Z.div_mod_to_equations; nia).
    rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  assert (HA : conc st (area_of g) = conc st g - conc st g mod 4096).
  { rewrite HG, Hm. unfold area_of. rewrite Eg. unfold aadd. cbn [fst snd]. rewrite (conc_region st (fst a) _ rg Hrg).
    replace ((snd a + (AREA_HDR + META_SIZE * k)) mod 4096) with (AREA_HDR + META_SIZE * k); [lia|].
    unfold AREA_HDR, META_SIZE, NSLOTS in *.
    replace (snd a + (24 + 40 * k)) with ((24 + 40 * k) + (snd a / 4096) * 4096) by (Z.div_mod_to_equations; nia).
    rewrite Z.mod_add by lia. symmetry. apply Z.mod_small. lia. }
  unfold meta_word.
  eapply (rrealloc_A1 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
            (r_base r + po) (conc st g) (conc st base) (conc st (area_of g)) b3 off16 (m_avail mr) (m_freed mr)
            (m_last_idx mr) (m_freeable mr) (m_sizeclass mr) (m_maplen mr) (bv_unsigned secw)
            (pw st (m_prev mr)) (pw st (m_next mr))); try eassumption; try LiaTuning.alia.
  - replace (r_base r + po - 4) with (r_base r + (po - 4)) by lia. exact R4.
  - replace (r_base r + po - 3) with (r_base r + (po - 3)) by lia. exact R3.
  - replace (r_base r + po - 2) with (r_base r + (po - 2)) by lia. exact R2.
Qed.

Lemma read1_bytes_at m a b : ov_read_bytes rsegs m (wa a) 1 = Some [b] -> 0 <= a -> a + 1 <= 2^64 -> bytes_at rsegs m a [b].
Proof.
  intros H Ha Ha1. split; [exact Ha|]. split; [cbn; lia|]. intros k Hk. destruct k; [| cbn in Hk; lia].
  rewrite Z.add_0_r. cbn [nth_error]. rewrite ov_rdn, rdn_unfold in H.
  destruct (mrd rsegs m (wa a)) as [b0|]; [| discriminate]. cbn in H. congruence.
Qed.

Lemma bytes_at_4 m a x0 x1 x2 x3 :
  bytes_at rsegs m a [x0] -> bytes_at rsegs m (a + 1) [x1] -> bytes_at rsegs m (a + 2) [x2] -> bytes_at rsegs m (a + 3) [x3] ->
  bytes_at rsegs m a [x0; x1; x2; x3].
Proof.
  intros B0 B1 B2 B3. change [x0; x1; x2; x3] with ([x0] ++ ([x1] ++ ([x2] ++ [x3]))).
  apply bytes_at_app. split; [exact B0|]. apply bytes_at_app. split; [exact B1|].
  apply bytes_at_app. split; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; [replace (a + 1 + 1) with (a + 2) by lia; exact B2| replace (a + 1 + 1 + 1) with (a + 3) by lia; exact B3].
Qed.

Lemma le4_byte_of v : 0 <= v < 2^32 -> le4 (wz v) = [b8 (byte_of v 0); b8 (byte_of v 1); b8 (byte_of v 2); b8 (byte_of v 3)].
Proof.
  intros Hv. rewrite le4_bytes by lia. unfold byte_of. rewrite !Z.shiftr_div_pow2 by lia.
  change (2^(8*0)) with 1. change (2^(8*1)) with 256. change (2^(8*2)) with 65536. change (2^(8*3)) with 16777216.
  change 255 with (Z.ones 8). rewrite !Z.land_ones by lia. change (2^8) with 256. rewrite Z.div_1_r.
  rewrite (Z.mod_small (v / 16777216) 256) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]). reflexivity.
Qed.

Definition rrip_end {HGW : HasGuard} {HCEIL : HasCeiling} (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (st : mstate) (c : cptr) (off n n' P E : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rmrep (mresize st c off n n') m' /\ ticks_ok (mresize st c off n n') /\ ctrl_eq st (mresize st c off n n')
    /\ rpres_except (fun a => lo <= a < bv_unsigned sp \/ P - 3 <= a < P \/ P + n' <= a < E) m m'
    /\ wr_at rsegs m' P n'
    /\ (P + n' <= E /\ 16 <= P /\ P mod 16 = 0
        /\ (E + 1 <= 0x10000 \/ 0x2a000 <= P - 4) /\ (E + 1 <= 0x2a000 \/ 0x5d000 <= P - 4)
        /\ (exists r, (s_regions st) !! (fst c) = Some r /\ r_kind r = RKGroup /\ P = r_base r + snd c + UNIT * off
               /\ E + 1 <= r_base r + round_up_pg (r_len r) /\ r_base r + round_up_pg (r_len r) <= alloc_ceiling)).

Definition rrgen_prefix_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (A sz n' : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m1,
    ms' = MS (mkR (Z_to_bv 64 0x19cf8) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 n') (Z_to_bv 64 A) (Z_to_bv 64 n')
                  a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (A + sz)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 rmalloc_entry) fc None m1 (seg_rom rsegs)
    /\ rw_cells rsegs m1 (bv_unsigned sp + -64) (rr_frame s6 s5 s4 s3 s2 s1 s0 ra)
    /\ stk rsegs m1 lo (bv_unsigned sp + -64)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1.

Section IP.
Context {HGW : HasGuard}.
Context {HCEIL : HasCeiling}.
Variables (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (LB : list block) (lo : Z).
Hypothesis LO : alloc_ceiling <= lo.

Definition rr_inplace (st : mstate) (mm : aptr) (off n' : Z) : Prop :=
  UNIT * off + n' <= get_stride (get_meta_rec st mm) - IB /\ m_sizeclass (get_meta_rec st mm) <= size_to_class n' + 1.

Theorem rrealloc_walk : forall (ra sp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem)
    (st : mstate) (blk : block) (off n' : Z) (mm : aptr) (i : Z),
  RAREACH st LB -> In blk LB -> 0 <= off -> blk_addr blk = conc st (blk_slot blk) + UNIT * off ->
  (s_slots st) !! (blk_slot blk) = Some (mm, i) ->
  rmrep st m -> mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 64 ->
  a0 = Z_to_bv 64 (blk_addr blk) -> a1 = Z_to_bv 64 n' -> 0 <= n' < MMAP_THRESHOLD ->
  evt rsegs (fun ms' =>
        (rr_inplace st mm off n'
         /\ rrip_end ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 F fc lo st (blk_slot blk) off (blk_size blk) n'
               (blk_addr blk) (blk_addr blk - UNIT * off + get_stride (get_meta_rec st mm) - IB) m ms')
        \/ (~ rr_inplace st mm off n'
         /\ rrgen_prefix_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo (blk_addr blk) (blk_size blk) n' m ms'))
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
  assert (EE : A - UNIT * off + stride - IB = E) by (unfold E; rewrite HAP; lia). rewrite EE.
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
  pose proof (size_to_class_props n' N) as (SCR & _ & _).
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

  destruct (Sumbool.sumbool_and _ _ _ _ (Z_le_dec (16 * off + n') (stride - 4)) (Z_le_dec (m_sizeclass mr) (size_to_class n' + 1))) as [[FIT' CLS]|NIP].
  {
  assert (SC48 : 0 <= m_sizeclass mr < 48) by (thaw GSC; clear -GSC CLS SCR; lia).
  specialize (S31 (proj2 SC48)).
  eapply evt_mono; [| intros msX HX; left; split; [split; [exact FIT'| exact CLS]| exact HX]].

  eapply evt_cut.
  { eapply (rrealloc_B_ip ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp _ t4'' t5 t6 s0 (Z_to_bv 64 A) (Z_to_bv 64 n') s3 s4 s5 s6 s7 s8 s9 s10 s11
              (wz (conc st mm)) F fc m1 P (conc st bm) (m_sizeclass mr) _ stride E res b3 n');
      [reflexivity| exact N| exact MI1| unfold P, E; lia| unfold E; lia| clear -SC48; lia| unfold E, P; clear -FIT' ; lia| exact CLS]. }
  intros ms4 (t1_ & t2_ & t3_ & t4_ & a2_ & a3_ & a4_ & a5_ & a7_ & ->).

  pose proof MR1 as (_ & _ & _ & _ & _ & SH1). destruct (SH1 _ r Hr Kr) as [HWr1 _]. clear SH1.
  destruct (KB1 _ _ O3 ltac:(lia)) as [BK3 _].
  replace (r_base r + (snd c + 16 * off - 3)) with (P - 3) in BK3 by (unfold P; lia).
  eapply evt_mono.
  { eapply (rrealloc_ip_walk ra sp gp tp t1_ t2_ s0 (wz (conc st mm)) (Z_to_bv 64 A) (Z_to_bv 64 n') a2_ a3_ a4_ a5_ a7_ (Z_to_bv 64 (E - res))
              s3 s4 s5 s6 s7 s8 s9 s10 s11 t3_ t4_ t5 t6 ra s0 s1 s2 s3 s4 s5 s6 F fc m1 lo P E n' b3).
    - unfold P in HAP |- *. rewrite unsigned_lit by lia. lia.
    - reflexivity.
    - exact MI1.
    - eapply (F_malloc_free.wr_at_sub rsegs m1 _ _ (P - 3) (E - P + 3) HWr1); unfold P, E; lia.
    - exact BK3.
    - exact FR1.
    - exact ST1.
    - unfold E. lia.
    - exact SLO.
    - unfold P. lia.
    - unfold P, E. lia.
    - lia.
    - unfold P, E. clear -S31 OFF N. lia.
    - exact B3R. }
  intros msf (t0f & t1f & t2f & a1f & a2f & a3f & a4f & a5f & a6f & a7f & t3f & t4f & t5f & t6f & m' & -> & EM & MI' & ST').

  assert (NOGRP : forall b' gh, s_groups st !! b' = Some gh -> fst b' = fst c -> snd b' + 9 <= snd c - 3 \/ snd c + stride - IB <= snd b').
  { intros b' gh Hb' Hf'. destruct (blk_slot_nogrp x0 st L BL LS INV c mm i b' gh Hs NH Hb' Hf') as [X|X]; change (MR st mm) with mr in X; fold stride in X; unfold IB; lia. }
  assert (C4' : 4 <= snd c) by (clear -Sc B0 SI0; lia).
  assert (R32' : stride - IB - UNIT * off - n' < 2^32) by (clear -S31 OFF N; unfold UNIT, IB; lia).
  destruct (rresize_mrep st m1 c off n n' mm i r MR1 TK Hs Hrc Kr C4' ETOP NOGRP Hoff (proj1 N) FIT' R32')
    as (MRz & TKz & CEz).
  assert (EMEM : rset_size_mem m1 (r_base r + snd c + UNIT * off) (r_base r + snd c + get_stride (get_meta_rec st mm) - IB) n'
                   (i + 32 * Z.min (get_stride (get_meta_rec st mm) - IB - UNIT * off - n) 5) = m').
  { rewrite EM. thaw B3EQ. thaw R5EQ. rewrite B3EQ, R5EQ, RESEQ. reflexivity. }
  rewrite EMEM in MRz.
  unfold rrip_end. do 14 eexists. exists m'. split; [reflexivity|].
  split; [exact MI'|]. split; [exact ST'|]. split; [exact MRz|]. split; [exact TKz|]. split; [exact CEz|]. split; [| split].
  -   rewrite HAP.
    assert (PE1 : rpres_except (fun a => lo <= a < bv_unsigned sp \/ P - 3 <= a < P \/ P + n' <= a < E) m m1).
    { apply (rpres_except_of_munch_cov _ _ m m1 MU1 WM1). cbn [ivs_covered]. split; [| exact I]. intros x Hx. left. lia. }
    rewrite EM. unfold rset_size_mem.
    set (C0 := fun a : Z => lo <= a < bv_unsigned sp \/ P - 3 <= a < P \/ P + n' <= a < E) in *.
    assert (L4 : forall w, length (le4 w) = 4%nat) by (intros; reflexivity).
    set (rr := E - P - n').
    set (mF := if rr =? 0 then m1 else write_to_mem m1 (wa (E - rr)) [b8 0]).
    assert (PF : rpres_except C0 m mF).
    { subst mF. destruct (Z.eqb_spec rr 0); [exact PE1|]. apply rpres_write; [exact PE1| unfold rr, E, P; (first [solve [clear - Hoff N Hi S16 B0 Sc RB0; lia] | lia])| cbn; unfold rr, E, P; (first [solve [clear - SPAN Sc RBC SIL CEILB FIT'; lia] | lia])| cbn; intros x Hx; unfold C0; right; right; unfold rr in Hx; (first [solve [clear - FIT' n0 Hx; lia] | lia])]. }
    clearbody mF.
    set (mG := if 5 <=? rr then _ else _).
    assert (PG : rpres_except C0 m (fst mG) /\ 0 <= snd mG <= 5 + rr).
    { subst mG. destruct (Z.leb_spec 5 rr); cbn [fst snd].
      - split; [| lia]. apply rpres_write; [| unfold E, P; lia| rewrite L4; unfold E; lia| rewrite L4; intros x Hx; unfold C0; right; right; unfold rr in *; lia].
        apply rpres_write; [exact PF| unfold E, P; lia| cbn; unfold E; lia| cbn; intros x Hx; unfold C0; right; right; unfold rr in *; lia].
      - split; [exact PF| unfold rr; lia]. }
    clearbody mG. destruct mG as [mg r2]. cbn [fst snd] in PG |- *. destruct PG as [PG _].
    apply rpres_write; [exact PG| unfold P; lia| cbn; unfold P; lia| cbn; intros x Hx; unfold C0; right; left; lia].
  -
    rewrite HAP, EM. unfold rset_size_mem.
    destruct (5 <=? E - P - n'); destruct (E - P - n' =? 0); cbn iota beta;
      repeat apply wr_at_write; eapply (F_malloc_free.wr_at_sub rsegs m1 _ _ P n' HWr1); unfold P, E in *; lia.
  -   rewrite HAP. thaw PM16. thaw DRr. ceil_facts; unfold P, E. unfold P in PM16.
    split; [lia|]. split; [lia|]. split; [thaw RBAL; clear -PM16 RBAL; Z.div_mod_to_equations; lia|]. split; [| split].
    + clear -DRr OFF FIT' ETOP Sc B0 SI0 S16. specialize (DRr ltac:(lia)). lia.
    + clear -DRr OFF FIT' ETOP Sc B0 SI0 S16. specialize (DRr ltac:(lia)). lia.
    + exists r. split; [exact Hrc|]. split; [exact Kr|]. split; [reflexivity|]. split; [lia|]. exact RBC.
  }
  {
  eapply evt_mono; [| intros msX HX; right; split; [unfold rr_inplace; change (get_meta_rec st mm) with mr; fold stride; clear -NIP; unfold UNIT, IB; lia| exact HX]].
  eapply evt_cut.
  { eapply (rrealloc_B_gen ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp _ t4'' t5 t6 s0 (Z_to_bv 64 A) (Z_to_bv 64 n') s3 s4 s5 s6 s7 s8 s9 s10 s11
              (wz (conc st mm)) F fc m1 P (conc st bm) (m_sizeclass mr) _ stride E res b3 n');
      [reflexivity| unfold MMAP_THRESHOLD in N; lia| exact MI1| unfold P, E; lia| unfold E; lia| exact SC64|].
    left. split; [exact (proj2 N)|]. unfold E, P. clear -NIP N. lia. }
  intros ms4 (t0_ & t1_ & t2_ & t3_ & t4_ & a2_ & a3_ & a4_ & a5_ & a6_ & a7_ & ->).
  eapply evt_mono; [apply rrgen_tomalloc|]. intros ms5 ->.
  unfold rrgen_prefix_post. do 14 eexists. exists m1.
  replace (A + n) with (E - res) by (unfold E, P in *; clear -RESEQ HAP; lia).
  split; [rewrite HAP; reflexivity|].
  split; [exact FR1|]. split; [exact ST1|]. split; [exact MU1|]. split; [exact WM1| exact MI1]. }
Qed.
End IP.
