(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS MState.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_defs D_kit R_cache_defs R_prim_defs R_thread R_m2s R_leaves R_poison R_setshadow R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc R_refill R_refill_ic R_getfrom R_getfrom_A R_popfree R_popfree_B R_popfree_T R_mmapfixed R_prim_lists R_prim_kit R_allocate3 RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_malstate RT_freelift RT_geo0 RT_fkit RT_freestate RT_freeA RT_freeC RT_freeA2 RT_refillstmt RT_refillst RT_refillwf RT_rfkit RT_refillart RT_rfbytes RT_refillrun.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A.Shadow.GW}.
Section RfSlow.
Variables (Σ : rtsA) (m : mem) (c lo : Z) (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Hypothesis HW0 : rt_wf0 Σ.
Hypothesis HA : ARTc Σ m.
Hypothesis Hc : 1 <= c <= 30.
Hypothesis Hca : ca Σ c = [].
Hypothesis HROOM : refill_room Σ c.
Hypothesis MI : mem_inv bsegs m.
Hypothesis ST : stk bsegs m lo (bv_unsigned sp).
Hypothesis HLO : l_ACEIL (lay Σ) <= lo.
Hypothesis HLO2 : lo + 0x400 <= bv_unsigned sp.
Hypothesis HSP : bv_unsigned sp <= 2 ^ 47.
Hypothesis Hslow : Z.of_nat (length (r_fl (pr Σ c))) < MaxCount c / 2.
#[local] Notation usp := (bv_unsigned sp).
#[local] Notation L := (lay Σ).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation SB := (l_SB (lay Σ)).
#[local] Notation TCX := (l_TCX (lay Σ)).
#[local] Notation PRB := (l_PRB (lay Σ)).
#[local] Notation R := (rinfo (RIS_of (l_SB (lay Σ))) c).
#[local] Notation r := (pr Σ c).
#[local] Notation au := (ClassSize c * Z.of_nat (length (r_st (pr Σ c)))).
#[local] Notation mu := (r_muser (pr Σ c)).
#[local] Notation nf := (Z.of_nat (length (r_fl (pr Σ c)))).
#[local] Notation n := (MaxCount c / 2).
#[local] Notation P := (pc_addr (l_T (lay Σ)) c).
#[local] Notation msz := (rf_msz (pr Σ c) c).
#[local] Notation newc := (rf_newc (pr Σ c) c).
#[local] Notation WR := (W_R (l_T (lay Σ)) (l_SB (lay Σ)) c (ClassSize c * Z.of_nat (length (r_st (pr Σ c)))) (bv_unsigned sp)).

Lemma rs_c31 : 1 <= c <= 31. Proof using Hc. clear - Hc. lia. Qed.

Definition rr_svc1 (ms : machine_state) : Prop :=
  exists (t0' t1' t2' a6' t3' t4' t5' t6' : word) (m1 : mem) (gjunk junk : list byte) (ws chs1 : list word) (rand : word) (exh : byte)
         (pad : list byte) (nal nfr q0 q1 q2 q3 : Z),
    ms = MSsvc (mfi_regs (Z_to_bv 64 pfa_retB1) (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (usp - 32)) - 128)) - 64))
                         gp (Z_to_bv 64 tpA)
                         t0' t1' t2' a6' (rb SB c + mu) msz (Z_to_bv 64 str_regiondata) (Z_to_bv 64 (ClassSize c))
                         (Z_to_bv 64 INST) (Z_to_bv 64 1152921504606846976) (Z_to_bv 64 1500)
                         (Z_to_bv 64 16140901064495857663) s10 s11 t3' t4' t5' t6') F
                (Z_to_bv 64 mmap_ecall_pc) (Z_to_bv 64 222) fc None m1 (seg_rom bsegs)
    /\ munch WR m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
    /\ pfa_cells1 m1 (Z_to_bv 64 (usp - 32 - 128)) (Z_to_bv 64 gfa_retP) (Z_to_bv 64 R) (Z_to_bv 64 INST)
         (Z_to_bv 64 (R + 8)) (Z_to_bv 64 2305843009213693952) (Z_to_bv 64 (fa SB c)) (Z_to_bv 64 (P + 16)) (Z_to_bv 64 n)
         R (cstats T) (rb SB c) mu msz lo
    /\ rw_cells bsegs m1 (usp - 32 - 128)
         [CB 24 gjunk; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 P);
          C8 (Z_to_bv 64 refill_retB)]
    /\ ri_lock m1 R 1152921504606846976
    /\ ri_core m1 R nf (r_mfa r) au mu /\ ri_tail m1 R rand exh pad nal nfr q0 q1 q2 q3 /\ 0 <= nal < 2 ^ 64 /\ length pad = 3%nat
    /\ fl_arr m1 SB c ws /\ 4 * Z.of_nat (length ws) = r_mfa r /\ firstn (length (r_fl r)) ws = map (cpw c) (r_fl r)
    /\ u32arr bsegs m1 (P + 16) chs1 /\ length chs1 = 16%nat
    /\ inst_cells SB m1 /\ thread_cells TCX T m1 /\ ps_cells m1
    /\ stk bsegs m1 (T + 2768) (T + 3168) /\ stk bsegs m1 (shad (rb SB c)) (shad (rb SB c + 2 ^ 32))
    /\ stk bsegs m1 (rb SB c + au) (rb SB c + mu) /\ bytes_at bsegs m1 (shad (rb SB c + au)) (farun ((mu - au) / 8))
    /\ rw_cells bsegs m1 (usp - 32) [CB 8 junk; C8 s1; C8 s0; C8 ra] /\ pc_cells m1 P 0 (MaxCount c) (ClassSize c)
    /\ (forall j, 1 <= j <= 31 -> j <> c -> pclass_rep T j true (ca Σ j) m1).

Lemma rr_slow_nums : 0 < msz /\ msz mod 0x40000 = 0 /\ mu + msz <= 0xE0000000 /\ mu + msz < au + (n - nf) * ClassSize c + 0x40000
  /\ au + (n - nf) * ClassSize c <= mu + msz /\ 1 <= n <= 8 /\ 0 <= au <= mu /\ mu < au + (n - nf) * ClassSize c /\ mu mod 2 ^ 18 = 0
  /\ 0 <= r_mfa r <= 2 ^ 29 /\ r_mfa r mod 2 ^ 18 = 0.
Proof using HW0 Hc HROOM Hslow.
  pose proof rs_c31 as Hc31.
  clear - HW0 Hc HROOM Hslow Hc31. pose proof (rr_regwf Σ c HW0 Hc) as HWc. pose proof HWc as (W1 & W2 & W3 & W4 & W5 & W6 & _).
  pose proof (rf_msz_facts r c Hc31 HWc Hslow) as (M1 & M2 & M3 & M4). pose proof (MaxCount_half c Hc31) as HN.
  pose proof (ClassSize_range c Hc31) as (CS1 & CS2). unfold rf_k, rf_au, rf_nf, refill_room, kUserCap, kFaCap, kUMap in *.
  specialize (HROOM Hslow).
  assert (0 <= nf) by lia. assert (Hk : (n - nf) * ClassSize c <= 8 * 65536) by nia.
  split; [lia|]. split; [exact M2|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [nia|]. split; [nia|].
  split; [exact W2|]. split; [lia | exact W6].
Qed.

Lemma rr_slowA : forall t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6,
  evt bsegs rr_svc1 (refill_entry_st ra sp gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc T c m).
Proof using HW0 HA Hc Hca HROOM MI ST HLO HLO2 HSP Hslow.
  pose proof rs_c31 as Hc31.
  intros t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6.
  pose proof (rr_T Σ HW0) as HT. pose proof (rr_SB Σ HW0) as HSB. pose proof (rr_lo Σ lo HW0 HLO) as HLOH.
  pose proof (rr_usp Σ lo sp HW0 HLO HLO2 HSP) as (U1 & U2 & U3).
  pose proof (rr_geo Σ HW0) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
  pose proof (rr_regwf Σ c HW0 Hc) as HWc. pose proof HWc as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11).
  pose proof rr_slow_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11).
  pose proof (rr_reg0 Σ m c HA Hc) as (LK & RC & (rand & exh & pad & nal & nfr & q0 & q1 & q2 & q3 & RT) & (ws & FL & Hws & Hpre) & SU & SH & SS).
  pose proof HA as (CR & _). destruct CR as (IC & MMG & TC & _ & PSC & _ & _ & ICR).
  pose proof ICR as STS. do 31 (apply proj2 in STS). apply proj1 in STS. cbn [lay] in STS.
  eapply evt_cut; [exact (rr_front Σ m c lo ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc HW0 HA Hc Hca MI ST HLO HLO2 HSP
                             t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6)|].
  intros ms P1. destruct P1 as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & m1 & junk & -> & MU1 & WM1 & MI1 & FR1 & ST1 & K1).
  assert (RS : 0 <= usp - 32 < 2 ^ 64) by (clear - U1 U3; lia).
  assert (DF : forall a k, 0 <= k -> (PRB <= a /\ a + k <= PRB + 0x2000011000) \/ (SHB <= a /\ a + k <= 2 ^ 44 + SHB) \/ (0x10000 <= a /\ a + k <= SEGTOP_A)
                 \/ (l_TCX L <= a /\ a + k <= l_TCX L + 0x10000) \/ (T + 2768 <= a /\ a + k <= T + 4096) ->
            disjoint_from [(cacheT T, cstats T); (usp - 32, usp)] a k).
  { intros a k Hk Ha. pose proof (g_grant Σ (geo_of_wf0 Σ HW0) TCX 0x10000 ltac:(unfold startup_grants; right; right; right; left; reflexivity)) as (X1 & _ & X3 & X4 & X5).
    pose proof (g_apart Σ (geo_of_wf0 Σ HW0) 2 3 _ _ ltac:(lia) eq_refl eq_refl) as A23. cbn [fst snd] in A23. unfold apart in A23.
    unfold cacheT, cstats. cbn [disjoint_from]. clear - Ha Hk G3 G5 G6 G7 G8 G9 G13 U2 X3 A23.
    unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB, SEGTOP_A in *. split; [|split; [|exact I]]; destruct Ha as [Ha|[Ha|[Ha|[Ha|Ha]]]]; lia. }
  assert (HR0 : PRB <= R /\ R + 128 <= PRB + 0x2000011000) by (unfold rinfo, RIS_of; clear - G10 G11 Hc31; lia).
  unfold ri_lock, ri_core, ri_tail, fl_arr in *.
  pose proof (rw_cells_transport bsegs _ m m1 _ _ LK MU1 WM1 ltac:(apply DF; [cbn; lia | left; cbn [cells_size csize Nat.add]; lia])) as LK1.
  pose proof (rw_cells_transport bsegs _ m m1 _ _ RC MU1 WM1 ltac:(apply DF; [cbn; lia | left; cbn [cells_size csize Nat.add]; lia])) as RC1.
  pose proof (rw_cells_transport bsegs _ m m1 _ _ RT MU1 WM1 ltac:(apply DF; [cbn; lia | left; cbn [cells_size csize Nat.add]; lia])) as RT1.
  assert (HFA : PRB <= fa SB c /\ fa SB c + r_mfa r <= PRB + 0x2000011000) by (unfold fa, rb, kFaCap in *; clear - G10 G11 Hc31 W5; lia).
  pose proof (u32arr_transport bsegs _ m m1 _ _ FL MU1 WM1 ltac:(rewrite Hws; apply DF; [lia | left; lia])) as FL1.
  destruct IC as (IC1 & IC2).
  pose proof (rw_cells_transport bsegs _ m m1 _ _ IC1 MU1 WM1 ltac:(apply DF; [cbn; lia | right; right; left; unfold i_spacebeg, INST, g_instance, SEGTOP_A; cbn [cells_size csize Nat.add]; lia])) as IC1'.
  pose proof (rw_cells_transport bsegs _ m m1 _ _ IC2 MU1 WM1 ltac:(apply DF; [cbn; lia | right; right; left; unfold i_premapped, INST, g_instance, SEGTOP_A; cbn [cells_size csize Nat.add]; lia])) as IC2'.
  pose proof (K1 c Hc31) as (PC1 & chs1 & CH1 & CHL1 & _). rewrite Hca in PC1. cbn [length Z.of_nat] in PC1.
  set (nal' := bv_unsigned (Z_to_bv 64 nal)).
  assert (RT1' : rw_cells bsegs m1 (R + 64) [C4 rand; C1 exh; CB 3 pad; C8 (Z_to_bv 64 nal'); C8 (Z_to_bv 64 nfr); C8 (Z_to_bv 64 q0);
                                          C8 (Z_to_bv 64 q1); C8 (Z_to_bv 64 q2); C8 (Z_to_bv 64 q3)]) by (unfold nal'; rewrite Z_to_bv_bv_unsigned; exact RT1).
  assert (Hnal : 0 <= nal' < 2 ^ 64) by (unfold nal'; pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 nal)) as X; unfold bv_modulus in X; cbn [Z.of_N] in X; exact X).
  assert (Hpad : length pad = 3%nat) by (destruct RT1 as ((X & _) & _); cbn in X; lia).

  assert (MMG1 : mm_gcells m1).
  { destruct MMG as (M1 & M2 & M3 & M4 & M5). unfold mm_gcells.
    assert (DI : forall a k, 0 <= k -> 0x10000 <= a -> a + k <= SEGTOP_A -> disjoint_from [(cacheT T, cstats T); (usp - 32, usp)] a k)
      by (intros a k Hk H1 H2; apply DF; [exact Hk | right; right; left; lia]).
    split; [apply (rw_cells_transport bsegs _ m m1 _ _ M1 MU1 WM1); apply DI; cbn [cells_size csize Nat.add]; unfold SEGTOP_A; lia|].
    split; [apply (rw_cells_transport bsegs _ m m1 _ _ M2 MU1 WM1); apply DI; cbn [cells_size csize Nat.add]; unfold SEGTOP_A; lia|].
    split; [apply (rw_cells_transport bsegs _ m m1 _ _ M3 MU1 WM1); apply DI; cbn [cells_size csize Nat.add]; unfold SEGTOP_A; lia|].
    split; [apply (rw_cells_transport bsegs _ m m1 _ _ M4 MU1 WM1); apply DI; cbn [cells_size csize Nat.add]; unfold SEGTOP_A; lia|].
    apply (rw_cells_transport bsegs _ m m1 _ _ M5 MU1 WM1); apply DI; cbn [cells_size csize Nat.add]; unfold SEGTOP_A; lia. }

  eapply evt_cut.
  { apply (gfa_A_spec (Z_to_bv 64 refill_retB) (Z_to_bv 64 (usp - 32)) gp (Z_to_bv 64 tpA) x0 x1 x2 (Z_to_bv 64 P) (Z_to_bv 64 n) x3 x4 x5
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x6 x7 x8 x9 F fc m1 (l_ACEIL L) SB c R (cstats T) (P + 16) n nf (r_mfa r) au mu lo);
      rewrite ?(unsigned_lit (usp - 32)) by exact RS.
    all: try assumption. all: try reflexivity.
    all: try (clear - N6; lia). all: try (clear - Hslow; lia). all: try (clear - N7 N8 N9; lia). all: try (clear - N3; unfold umap_size, rf_msz, rf_au, rf_k, rf_nf in *; lia).
    all: try (clear - N10; lia). all: try (clear - HLO2; lia).
    all: try (clear - U3; lia).
    split; [exact IC1' | exact IC2']. }
  intros ms P2. destruct P2 as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & m2 & gjunk & -> & MU2 & WM2 & MI2 & PF2 & GF2 & LK2).
  rewrite (unsigned_lit (usp - 32)) in MU2, PF2, GF2 by exact RS.
  assert (DG : forall a k, 0 <= k -> (PRB <= a /\ a + k <= PRB + 0x2000011000 /\ (a + k <= R \/ R + 8 <= a)) \/ (SHB <= a /\ a + k <= 2 ^ 44 + SHB)
              \/ (0x10000 <= a /\ a + k <= SEGTOP_A) \/ (l_TCX L <= a /\ a + k <= l_TCX L + 0x10000) \/ (T <= a /\ a + k <= T + 4096) \/ usp - 32 <= a ->
            disjoint_from [(R, R + 8); (usp - 32 - 592, usp - 32)] a k).
  { intros a k Hk Ha. pose proof (g_grant Σ (geo_of_wf0 Σ HW0) TCX 0x10000 ltac:(unfold startup_grants; right; right; right; left; reflexivity)) as (X1 & _ & X3 & X4 & X5).
    pose proof (g_apart Σ (geo_of_wf0 Σ HW0) 0 3 _ _ ltac:(lia) eq_refl eq_refl) as A03. cbn [fst snd] in A03. unfold apart in A03.
    cbn [disjoint_from]. clear - Ha Hk G3 G5 G6 G7 G8 G9 G13 U2 HR0 X3 A03. unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB, SEGTOP_A in *.
    repeat split; try exact I; destruct Ha as [Ha|[Ha|[Ha|[Ha|[Ha|Ha]]]]]; lia. }
  apply evt_done.
  exists y0, y1, y2, y3, y4, y5, y6, y7, m2, gjunk, junk, ws, chs1, rand, exh, pad, nal', nfr, q0, q1, q2, q3.
  split; [reflexivity|].
  split; [apply (munch_trans WR m m1 m2); [refine (munch_weaken _ WR m m1 _ MU1); unfold W_R, cacheT, cstats; clear - U2; solve_sub_fp
                                           | refine (munch_weaken _ WR m1 m2 _ MU2); unfold W_R, rinfo, RIS_of; clear - U2; solve_sub_fp]|].
  split; [exact (wmono_trans bsegs _ _ _ WM1 WM2)|]. split; [exact MI2|]. split; [exact PF2|]. split; [exact GF2|]. split; [exact LK2|].
  split; [apply (rw_cells_transport bsegs _ m1 m2 _ _ RC1 MU2 WM2); cbn [cells_size csize Nat.add]; apply DG; [lia | left; lia]|].
  split; [apply (rw_cells_transport bsegs _ m1 m2 _ _ RT1' MU2 WM2); cbn [cells_size csize Nat.add]; apply DG; [lia | left; lia]|].
  split; [exact Hnal|]. split; [exact Hpad|].
  split; [apply (u32arr_transport bsegs _ m1 m2 _ _ FL1 MU2 WM2); rewrite Hws; apply DG; [lia | left; unfold fa, rinfo, RIS_of, rb, kFaCap in *; clear - HFA W5 Hc31; lia]|].
  split; [exact Hws|]. split; [exact Hpre|].
  split; [apply (u32arr_transport bsegs _ m1 m2 _ _ CH1 MU2 WM2); rewrite CHL1; apply DG; [lia | right; right; right; right; left; unfold pc_addr; clear - Hc31 G3; lia]|].
  split; [exact CHL1|].
  split; [split; [apply (rw_cells_transport bsegs _ m1 m2 _ _ IC1' MU2 WM2) | apply (rw_cells_transport bsegs _ m1 m2 _ _ IC2' MU2 WM2)];
          cbn [cells_size csize Nat.add]; apply DG; [lia | right; right; left; unfold i_spacebeg, i_premapped, INST, g_instance, SEGTOP_A; lia
                                                    | lia | right; right; left; unfold i_spacebeg, i_premapped, INST, g_instance, SEGTOP_A; lia]|].
  split.
  { apply (thread_cells_frame TCX T _ m1 m2 (thread_cells_frame TCX T _ m m1 TC MU1 WM1
             ltac:(apply DF; [unfold img_hull_lo, img_hull_hi; lia | right; right; left; unfold img_hull_lo, img_hull_hi, SEGTOP_A; lia])
             ltac:(apply DF; [lia | right; right; right; left; lia])) MU2 WM2).
    - apply DG; [unfold img_hull_lo, img_hull_hi; lia | right; right; left; unfold img_hull_lo, img_hull_hi, SEGTOP_A; lia].
    - apply DG; [lia | right; right; right; left; lia]. }
  split.
  { apply (ps_cells_framed m1 m2 _ (ps_cells_framed m m1 _ PSC MU1 WM1
             ltac:(apply DF; [unfold img_hull_lo, img_hull_hi; lia | right; right; left; unfold img_hull_lo, img_hull_hi, SEGTOP_A; lia])) MU2 WM2).
    apply DG; [unfold img_hull_lo, img_hull_hi; lia | right; right; left; unfold img_hull_lo, img_hull_hi, SEGTOP_A; lia]. }
  split; [exact (stk_wmono m m2 _ _ STS (wmono_trans bsegs _ _ _ WM1 WM2))|].
  split; [exact (stk_wmono m m2 _ _ SS (wmono_trans bsegs _ _ _ WM1 WM2))|].
  split; [exact (stk_wmono m m2 _ _ SU (wmono_trans bsegs _ _ _ WM1 WM2))|].
  split.
  { assert (SHR : SHB <= shad (rb SB c + au) /\ shad (rb SB c + au) + Z.max 0 ((mu - au) / 8) <= 2 ^ 44 + SHB).
    { assert (HSB0 : 0 <= SB) by (clear - G9 G10; unfold K_HIGH_SHADOW_hi in *; lia).
      assert (Hau : 0 <= au) by (clear - N7; lia).
      pose proof (shad_lo (rb SB c + au) ltac:(unfold rb; clear - HSB0 Hau Hc31; lia)) as Q1.
      pose proof (shad_hi (rb SB c + mu) ltac:(unfold rb, kUserCap in *; clear - W1 G4 G10 G11 G13 Hc31; lia)) as Q2.
      pose proof (fk_shad_le2 (rb SB c + au) (mu - au) ltac:(unfold rb; clear - HSB0 Hau Hc31; lia) ltac:(clear - W3; lia)) as E.
      replace (rb SB c + au + (mu - au)) with (rb SB c + mu) in E by ring.
      assert (0 <= (mu - au) / 8) by (apply Z.div_pos; clear - W3; lia). rewrite Z.max_r by (clear - H; lia). clear - Q1 Q2 E; lia. }
    apply (bytes_at_transport bsegs _ m1 m2 _ _ (bytes_at_transport bsegs _ m m1 _ _ SH MU1 ltac:(rewrite farun_len; apply DF; [lia | right; left; lia])) MU2).
    rewrite farun_len. apply DG; [lia | right; left; lia]. }
  split; [apply (rw_cells_transport bsegs _ m1 m2 _ _ FR1 MU2 WM2); cbn [cells_size csize Nat.add]; apply DG; [lia | right; right; right; right; right; lia]|].
  split; [apply (rw_cells_transport bsegs _ m1 m2 _ _ PC1 MU2 WM2); cbn [cells_size csize Nat.add]; apply DG; [lia | right; right; right; right; left; unfold pc_addr; clear - Hc31 G3; lia]|].
  intros j Hj Hne. apply (pclass_rep_transport _ T j true _ m1 m2 (K1 j Hj) MU2 WM2). unfold pclass_avoid. apply DG; [lia|].
  right; right; right; right; left. unfold pc_addr. clear - Hj G3. lia.
Qed.

End RfSlow.

End GWIN.
