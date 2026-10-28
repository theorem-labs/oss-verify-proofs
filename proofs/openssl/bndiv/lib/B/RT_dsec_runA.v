(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS MState.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import RT_iface D_defs D_kit R_sizeclass R_cache_defs R_prim_defs R_glue_defs R_m2s R_thread R_poison R_prim_kit R_depot_defs R_quar_defs R_qrec_defs R_qrecycle R_qdorec R_qcbrec R_sec_defs R_secgbb R_qcbrec_S R_flushshadow R_mmapordie R_secdealloc R_secdealloc_p3 R_secdealloc_A RT_state RT_rep RT_frame RT_trans RT_sep RT_freelift RT_geo0 RT_fkit RT_freestate RT_freeA RT_freeA2 RT_maltail RT_drain_defs RT_drain_pure RT_drain_led RT_drain_kit RT_drain_geo RT_drain_ldefs RT_drain_loop RT_drain_istmt RT_drain_qcbp RT_drain_itemp RT_dsec_fkit RT_dsec_kit RT_dsec_defs RT_dsec_geo RT_dsec_art.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Lemma outside_incl : forall W1 W2 x, (forall iv, In iv W1 -> In iv W2) -> outside W2 x -> outside W1 x.
Proof.
  intros W1 W2 x HI H. apply outside_Forall. apply Forall_forall. intros iv Hiv.
  exact (proj1 (Forall_forall _ _) (proj1 (outside_Forall W2 x) H) iv (HI iv Hiv)).
Qed.

Section RunA.
Variables (p : dlp) (j : list byte) (b : Z) (ib : nat) (ents : list (Z * Z)) (i : nat) (rest : list batch) (Σk : rtsA) (k : nat)
  (s : secst) (m : mem) (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word).
Hypothesis HOK : dl_ok p.
Hypothesis HWP : rt_wfP Σk ((b, skipn i ents) :: rest).
Hypothesis HS : dl_sig p Σk.
Hypothesis Hk : nth_error (sec Σk) k = Some s.
Hypothesis Hq : s_quar s = true.
Hypothesis DM : dl_mem p j Σk rest m.
Hypothesis QB : qbatch m b (qfirst rest) ents.
Hypothesis Hib : nth_error (r_st (pr Σk 24)) ib = Some CkBatch.
Hypothesis Eb : b = p_abeg (l_SB (lay Σk)) 24 ib.
#[local] Notation Σ0 := (dl_Σ0 p).
#[local] Notation usp := (dl_usp p).
#[local] Notation lo := (dl_lo p).
#[local] Notation C := (dl_usp p - 2288).
#[local] Notation L := (lay Σk).
#[local] Notation T := (l_T (lay Σk)).
#[local] Notation TCX := (l_TCX (lay Σk)).
#[local] Notation SB := (l_SB (lay Σk)).
#[local] Notation PAB := (l_PAB (lay Σk)).
#[local] Notation MB := (s_mb s).
#[local] Notation MSZ := (smsz (s_n s)).
#[local] Notation n := (s_n s).
#[local] Notation M := (s_mb s + 6128).
#[local] Notation NS := (length (sec Σk)).

Definition ds_ms : machine_state :=
  MS (mkR (Z_to_bv 64 0x197fcc) (Z_to_bv 64 (C - 112)) (dl_gp p) (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 C) (Z_to_bv 64 INST)
          (Z_to_bv 64 (C - 104)) (Z_to_bv 64 M) a2 a3 a4 a5 a6 a7
          (Z_to_bv 64 6947800) (Z_to_bv 64 6948424) (Z_to_bv 64 b) (Z_to_bv 64 (2^37)) (Z_to_bv 64 (Z.of_nat (length ents)))
          (Z_to_bv 64 (b + 152 + 8 * Z.of_nat i)) (Z_to_bv 64 (Z.of_nat (length ents) + 16)) (Z_to_bv 64 (16 + Z.of_nat i))
          (dl_s10 p) (dl_s11 p) t3 t4 t5 t6)
     (dl_F p) (Z_to_bv 64 qcbrec_entry) (dl_fc p) None m (seg_rom bsegs).

(* [comment removed for export] *)
Definition svc_mad : machine_state -> Prop :=
  fun ms => exists (t0' t1' t2' a4' a5' a6' t3' t4' t5' t6' : word) (mA : mem) (ws : list word) (lst : secst) (muw mudw : word),
    ms = MSsvc (sd_M_regs (Z_to_bv 64 (C - 112)) (dl_gp p) t0' t1' t2' MB MSZ a4' a5' a6' (Z_to_bv 64 6948424)
                  (Z_to_bv 64 b) (Z_to_bv 64 (2^37)) (Z_to_bv 64 (Z.of_nat (length ents)))
                  (Z_to_bv 64 (b + 152 + 8 * Z.of_nat i)) (Z_to_bv 64 (Z.of_nat (length ents) + 16)) (Z_to_bv 64 (16 + Z.of_nat i))
                  (dl_s10 p) (dl_s11 p) t3' t4' t5' t6')
               (dl_F p) (Z_to_bv 64 madv_ecall) (Z_to_bv 64 233) (dl_fc p) None mA (seg_rom bsegs)
    /\ munch (qcbrec_sec_W T (C - 112) ++ sd_W (C - 112) MB MSZ PAB (Z.of_nat k) (s_mb lst)) m mA /\ wmono bsegs m mA
    /\ mem_inv bsegs mA
    /\ sd_mid (Z_to_bv 64 (C - 112)) (Z_to_bv 64 0x197fcc) (Z_to_bv 64 C) (Z_to_bv 64 INST) (Z_to_bv 64 6947800) MB MSZ
         (needed n + rz_size n) TCX T lo muw mudw mA
    /\ sd_K1 MB MSZ PAB 0x4000 (Z.of_nat NS) (Z.of_nat k) (s_mb lst) ws mA
    /\ Z.of_nat (length ws) = 0x4000 /\ firstn NS ws = map (fun s0 => Z_to_bv 64 (s_mb s0)) (sec Σk)
    /\ nth_error (sec Σk) (NS - 1) = Some lst.

Lemma ds_run1 : evt bsegs svc_mad ds_ms.
Proof using HOK HWP HS Hk Hq DM QB Hib Eb.
  pose proof HOK as (FDO & MST & HLO & HLO2 & HSP & HG0).
  pose proof HS as (El & Elv & Efr & Ecr & Eql & Einit).
  pose proof (geo_of_wfP _ _ HWP) as HG.
  pose proof (dl_nums p HLO HLO2 HSP HG0) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9).
  assert (HLk : l_ACEIL L <= lo) by (rewrite El; exact N9).
  pose proof DM as (HA & MI & ST & WM0 & RP & FR & QR).
  pose proof (dg_ok Σk HG) as (HT & HSB & TSEP).
  pose proof HA as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11).
  pose proof (dg_consts L m A1) as (IC & MMG & TC & PS & STS & UB). destruct IC as (IC1 & IC2).
  (* [comment removed for export] *)
  pose proof HG as (HL & HR & HSW & HFW).
  pose proof HSW as (SW1 & SW2 & SW3 & SW4 & SW5 & SW6).
  pose proof (proj1 (Forall_forall _ _) SW4 s (nth_error_In _ _ Hk)) as ((Hn1 & Hn2) & (G1 & G2 & G3 & G4 & G5) & GP & GF & GS).
  pose proof (nth_error_lt _ _ _ Hk) as Hkl.
  assert (Hnres : sec_nres Σk = 0x4000) by (apply SW3; intros E; rewrite E in Hk; destruct k; discriminate).
  pose proof (smsz_big n ltac:(lia)) as Hbig.
  (* [comment removed for export] *)
  pose proof A5 as (SC & SPD & (ws & WS & Hwsl & Hwsf) & SPG & SRG & SJK & NMC).
  rewrite Hnres in SC, Hwsl.
  assert (HIN : firstn NS (map bv_unsigned ws) = map s_mb (sec Σk)).
  { rewrite firstn_map, Hwsf, map_map. apply map_ext_in. intros x Hx. apply unsigned_lit.
    pose proof (proj1 (Forall_forall _ _) SW4 x Hx) as ((Y1 & _) & (X1 & _ & X3 & _) & _). pose proof (smsz_pos (s_n x) Y1).
    pose proof (dk_geo Σk HG) as (_ & X & _). lia. }
  (* [comment removed for export] *)
  pose proof A4 as (_ & CS). pose proof (CS k s Hk) as X. unfold schunk in X. rewrite Hq in X.
  replace (s_mb s + 4096 + 2032) with M in X by lia. replace (s_mb s + 4096 + 2048) with (M + 16) in X by lia.
  destruct X as (SHD & WRM & LCH & (b1 & ctx & fid & Hb1 & QH) & STSH & SB1 & SB2 & SB3).
  apply (proj1 (rwc_app bsegs m _ [C1 (Z_to_bv 8 3); C1 b1; C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n)] [C8 ctx; C8 fid])) in QH.
  destruct QH as (QH & QH2).
  assert (Hb1r : 0 <= bv_unsigned b1 < 256) by (pose proof (bv_unsigned_in_range 8 b1) as X; unfold bv_modulus in X; cbn in X; lia).
  rewrite <- (stdpp.bitvector.definitions.Z_to_bv_bv_unsigned 8 b1) in QH.
  (* [comment removed for export] *)
  destruct (fl_two_c8 m (T + 2840) ltac:(apply (stk_within m _ _ _ _ STS); [lia | lia | pose proof HT as (X & _); lia])) as (rfw & rfdw & STW).
  rewrite <- (Z_to_bv_bv_unsigned rfw), <- (Z_to_bv_bv_unsigned rfdw) in STW.
  pose proof (dk_geo Σk HG) as (GG1 & GG2 & GG3 & GG4 & GG5 & GG6 & GG7 & GG8).
  pose proof (g_grant Σk HG PAB 0x800000 ltac:(unfold startup_grants; right; left; reflexivity)) as (PA1 & PA2 & PA3 & PA4 & PA5).
  pose proof (g_apart Σk HG 1 2 _ _ ltac:(lia) eq_refl eq_refl) as AP12. cbn [fst snd] in AP12. unfold apart in AP12.
  pose proof (proj1 (Forall_forall _ _) GS (T, 4096) ltac:(unfold startup_grants; right; right; left; reflexivity)) as AMT.
  cbn [fst snd] in AMT. unfold apart in GP, AMT.
  assert (RSP : bv_unsigned (Z_to_bv 64 (C - 112)) = C - 112) by (apply unsigned_lit; lia).
  eapply evt_cut.
  { unfold ds_ms.
    apply (qcbrec_sec_spec (Z_to_bv 64 0x197fcc) (Z_to_bv 64 (C - 112)) (dl_gp p) t0 t1 t2 (Z_to_bv 64 C) (Z_to_bv 64 INST) a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 6947800) (Z_to_bv 64 6948424) (Z_to_bv 64 b) (Z_to_bv 64 (2^37)) (Z_to_bv 64 (Z.of_nat (length ents)))
             (Z_to_bv 64 (b + 152 + 8 * Z.of_nat i)) (Z_to_bv 64 (Z.of_nat (length ents) + 16)) (Z_to_bv 64 (16 + Z.of_nat i))
             (dl_s10 p) (dl_s11 p) t3 t4 t5 t6 (dl_F p) (dl_fc p) m (l_ACEIL L) SB PAB 0x4000 (Z.of_nat NS) ws MB MSZ
             (needed n + rz_size n) (Z.of_nat k) M n (bv_unsigned b1) TCX T (bv_unsigned rfw) (bv_unsigned rfdw) (C - 104) lo);
      rewrite ?RSP.
    all: try assumption.
    - split; [exact SPG|]. split; [exact SC|]. split; [exact SPD|]. split; [exact WS | exact SHD].
    - rewrite Hwsl. clear - PA3 HLk. lia.
    - unfold hide, img_hull_lo, img_hull_hi. rewrite Hwsl. clear - PA5. unfold SEGTOP_A in *. lia.
    - rewrite Hwsl. clear - Hkl SW1. unfold SEC_MAX in *. lia.
    - rewrite Nat2Z.id, HIN. apply in_map. exact (nth_error_In _ _ Hk).
    - rewrite Nat2Z.id, HIN. apply Forall_forall. intros ch Hch. apply in_map_iff in Hch as (x & <- & Hx). intros Hle.
      destruct (In_nth_error _ _ Hx) as (jx & Hjx). destruct (Nat.eq_dec jx k) as [->|Hne].
      + rewrite Hk in Hjx. injection Hjx as <-. lia.
      + pose proof (SW5 jx k x s Hjx Hk Hne) as AX. unfold apart in AX.
        pose proof (proj1 (Forall_forall _ _) SW4 x Hx) as ((Y1 & _) & _). pose proof (smsz_pos (s_n x) Y1). clear - AX Hle Hbig H Hn1. lia.
    - clear - G3 HLk. lia.
    - clear; lia.
    - clear - Hbig Hn1. lia.
    - unfold hide. clear - GP GG6 GG7. lia.
    - clear - Hn1 Hn2. lia.
    - apply (proj1 (rwc_app bsegs m _ [C8 (Z_to_bv 64 SB)] [C8 (Z_to_bv 64 0xffffffff); C8 (Z_to_bv 64 (RIS_of SB))])) in IC1.
      exact (proj1 IC1).
    - unfold hide. rewrite Hwsl. clear - AP12. lia.
    - clear - N5. lia.
    - clear - N6. lia. }
  intros ms1 P1.
  destruct P1 as (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & m1 & -> & MU1 & WM1 & MI1 & K1 & ST1).
  destruct K1 as ((PG1 & SC1 & PD1 & WS1 & SHD1) & HD1 & STW1).
  rewrite RSP in MU1, ST1.
  (* [comment removed for export] *)
  assert (HTZ : Forall (fun z => T <= fst z /\ snd z <= T + 4096) (TZ_ST T)) by (unfold TZ_ST; repeat constructor; cbn; lia).
  assert (HTZd : disjoint_from (TZ_ST T) T 0x30 /\ disjoint_from (TZ_ST T) (T + 48) 16 /\ disjoint_from (TZ_ST T) (T + 0xc60) 1
            /\ (forall c', 1 <= c' <= 31 -> disjoint_from (TZ_ST T) (pc_addr T c') 80) /\ disjoint_from (TZ_ST T) (qcacheT T) 32).
  { unfold TZ_ST, pc_addr, qcacheT. cbn [disjoint_from]. split; [split; [lia | exact I]|]. split; [split; [lia | exact I]|].
    split; [split; [lia | exact I]|]. split; [intros c' Hc'; split; [lia | exact I] | split; [lia | exact I]]. }
  assert (CERT1 : Forall (dzoneP Σk [] [] [k; (NS - 1)%nat] (TZ_ST T) IZ_S [] lo (C - 112)) (qcbrec_sec_W T (C - 112))).
  { unfold qcbrec_sec_W. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    - left. exists (i_sec_mutex, i_sec_mutex + 4). split; [left; reflexivity | cbn; lia].
    - right; left. exists (T + 2768, T + 3168). split; [left; reflexivity | cbn; lia].
    - do 9 right. left. cbn. lia. }
  pose proof (da_consts Σk m m1 _ k (TZ_ST T) lo (C - 112) HG HTZ HTZd HLk CERT1 HA MU1 WM1) as CR1.
  pose proof (dg_consts L m1 CR1) as (IC1' & MMG1 & TC1 & PS1 & STS1 & UB1).
  pose proof (ds_rel L m1 CR1) as REL1.
  (* [comment removed for export] *)
  destruct (nth_error (sec Σk) (NS - 1)) as [lst|] eqn:Hlst; [|apply nth_error_None in Hlst; lia].
  pose proof (proj1 (Forall_forall _ _) SW4 lst (nth_error_In _ _ Hlst)) as ((Ln1 & Ln2) & (LG1 & LG2 & LG3 & LG4 & LG5) & LGP & LGF & LGS).
  pose proof (smsz_big (s_n lst) ltac:(lia)) as Lbig.
  pose proof (CS _ lst Hlst) as X. unfold schunk, shdr in X. destruct X as (LSHD & _).
  apply (proj1 (rwc_app bsegs m _ [C8 (Z_to_bv 64 (s_mb lst)); C8 (Z_to_bv 64 (smsz (s_n lst))); C8 (Z_to_bv 64 (needed (s_n lst) + rz_size (s_n lst)))]
                                 [C8 (Z_to_bv 64 (Z.of_nat (NS - 1)))])) in LSHD.
  destruct LSHD as (_ & LIDX). cbn [cells_size csize Nat.add Z.of_nat] in LIDX.
  (* [comment removed for export] *)
  pose proof (g_grant Σk HG TCX 0x10000 ltac:(unfold startup_grants; right; right; right; left; reflexivity)) as (X1 & X2 & X3 & X4 & X5).
  pose proof (g_grant Σk HG T 4096 ltac:(unfold startup_grants; right; right; left; reflexivity)) as (Y1 & Y2 & Y3 & Y4 & Y5).
  pose proof (g_apart Σk HG 1 3 _ _ ltac:(lia) eq_refl eq_refl) as AP13. pose proof (g_apart Σk HG 2 3 _ _ ltac:(lia) eq_refl eq_refl) as AP23.
  cbn [fst snd] in AP13, AP23. unfold apart in AP13, AP23.
  pose proof (proj1 (Forall_forall _ _) GS (PAB, 0x800000) ltac:(unfold startup_grants; right; left; reflexivity)) as AMP.
  pose proof (proj1 (Forall_forall _ _) GS (TCX, 0x10000) ltac:(unfold startup_grants; right; right; right; left; reflexivity)) as AMX.
  pose proof (proj1 (Forall_forall _ _) LGS (PAB, 0x800000) ltac:(unfold startup_grants; right; left; reflexivity)) as ALP.
  pose proof (proj1 (Forall_forall _ _) LGS (T, 4096) ltac:(unfold startup_grants; right; right; left; reflexivity)) as ALT.
  pose proof (proj1 (Forall_forall _ _) LGS (TCX, 0x10000) ltac:(unfold startup_grants; right; right; right; left; reflexivity)) as ALX.
  cbn [fst snd] in AMP, AMX, ALP, ALT, ALX. unfold apart in AMP, AMX, ALP, ALT, ALX.
  assert (ALM : s_mb lst = MB \/ s_mb lst + 32 <= MB \/ MB + MSZ <= s_mb lst).
  { destruct (Nat.eq_dec (NS - 1) k) as [E|E].
    - left. rewrite E in Hlst. rewrite Hk in Hlst. injection Hlst as <-. reflexivity.
    - pose proof (SW5 (NS - 1)%nat k lst s Hlst Hk E) as A. unfold apart in A. clear - A Lbig Ln1. lia. }
  (* [comment removed for export] *)
  assert (HWI : nth_error ws k = Some (Z_to_bv 64 MB)).
  { assert (E : nth_error (firstn NS ws) k = nth_error (map (fun s0 => Z_to_bv 64 (s_mb s0)) (sec Σk)) k) by (rewrite Hwsf; reflexivity).
    rewrite nth_error_firstn, nth_error_map, Hk in E. destruct (Nat.ltb_spec k NS); [exact E | lia]. }
  assert (HWL : nth_error ws (NS - 1) = Some (Z_to_bv 64 (s_mb lst))).
  { assert (E : nth_error (firstn NS ws) (NS - 1) = nth_error (map (fun s0 => Z_to_bv 64 (s_mb s0)) (sec Σk)) (NS - 1)) by (rewrite Hwsf; reflexivity).
    rewrite nth_error_firstn, nth_error_map, Hlst in E. destruct (Nat.ltb_spec (NS - 1) NS); [exact E | lia]. }
  (* [comment removed for export] *)
  destruct (fl_two_c8 m1 (T + 2888) ltac:(apply (stk_within m1 _ _ _ _ STS1); [lia | lia | pose proof HT as (X & _); lia])) as (muw & mudw & MUW).
  assert (MB8 : MB mod 8 = 0) by (apply (mod8_of _ 4096 ltac:(lia) G2); exists 512; reflexivity).
  assert (MSZ8 : MSZ mod 8 = 0).
  { unfold smsz, pg_up. apply Z.mod_divide; [lia|]. exists (((needed n + rz_size n + 4095) / 4096) * 512 + 512). lia. }
  assert (ESH : shad (MB + MSZ) = shad MB + MSZ / 8) by (apply shad_add8'; assumption).
  destruct (stk_CB m1 (shad MB) (MSZ / 8) ltac:(rewrite <- ESH; exact (stk_wmono m m1 _ _ STSH WM1)) ltac:(apply Z.div_pos; lia)) as (shj & SHJ).
  assert (LIDX1 : rw_cells bsegs m1 (s_mb lst + 24) [C8 (Z_to_bv 64 (Z.of_nat (NS - 1)))]).
  { apply (rw_cells_transport bsegs _ m m1 _ _ LIDX MU1 WM1). unfold qcbrec_sec_W. cbn [disjoint_from cells_size csize Nat.add Z.of_nat].
    unfold i_sec_mutex, INST, g_instance. clear - LG1 LG3 LG5 ALT HLk N5 Lbig Ln1. unfold img_hull_lo, img_hull_hi, SEGTOP_A in *.
    repeat split; try exact I; lia. }
  assert (SJ1 : sec_junk m1).
  { destruct SJK as ((bj & jj & w1 & w2 & w3 & w4 & J1) & (bl & Hbl & J2) & (ga & gm & J3)).
    unfold qcbrec_sec_W in MU1. unfold i_sec_sorted, i_sec_bylog, i_gstat_alloc, i_sec_mutex, INST, g_instance in *.
    split; [exists bj, jj, w1, w2, w3, w4; apply (rw_cells_transport bsegs _ m m1 _ _ J1 MU1 WM1); cbn [disjoint_from cells_size csize Nat.add Z.of_nat];
            clear - Y1 Y2 Y5 HLk N5 HSB; destruct HSB as (? & ?); unfold kHighShadowEnd, SEGTOP_A in *; repeat split; try exact I; lia|].
    split; [exists bl; split; [exact Hbl|]; apply (u64arr_transport bsegs _ m m1 _ _ J2 MU1 WM1); rewrite Hbl; cbn [disjoint_from Z.of_nat];
            clear - Y1 Y2 Y5 HLk N5 HSB; destruct HSB as (? & ?); unfold kHighShadowEnd, SEGTOP_A in *; repeat split; try exact I; lia|].
    exists ga, gm. apply (rw_cells_transport bsegs _ m m1 _ _ J3 MU1 WM1); cbn [disjoint_from cells_size csize Nat.add Z.of_nat];
      clear - Y1 Y2 Y5 HLk N5 HSB; destruct HSB as (? & ?); unfold kHighShadowEnd, SEGTOP_A in *; repeat split; try exact I; lia. }
  apply (proj1 (rwc_app bsegs m1 _ [C8 (Z_to_bv 64 MB); C8 (Z_to_bv 64 MSZ); C8 (Z_to_bv 64 (needed n + rz_size n))]
                                  [C8 (Z_to_bv 64 (Z.of_nat k))])) in SHD1.
  destruct SHD1 as (HDA & HDI). cbn [cells_size csize Nat.add Z.of_nat] in HDI.
  eapply evt_cut.
  { apply (secdealloc_A1_spec (Z_to_bv 64 0x197fcc) (Z_to_bv 64 (C - 112)) (dl_gp p) u0 u1 u2 (Z_to_bv 64 C) (Z_to_bv 64 INST) u3 u4 u5 u6 u7
             (Z_to_bv 64 6947800) (Z_to_bv 64 6948424) (Z_to_bv 64 b) (Z_to_bv 64 (2^37)) (Z_to_bv 64 (Z.of_nat (length ents)))
             (Z_to_bv 64 (b + 152 + 8 * Z.of_nat i)) (Z_to_bv 64 (Z.of_nat (length ents) + 16)) (Z_to_bv 64 (16 + Z.of_nat i))
             (dl_s10 p) (dl_s11 p) u8 u9 u10 u11 (dl_F p) (dl_fc p) m1 MB MSZ (needed n + rz_size n) (Z.of_nat k) PAB 0x4000 (Z.of_nat NS)
             (s_mb lst) (Z.of_nat (NS - 1)) TCX T lo ws muw mudw shj); rewrite ?RSP.
    all: try assumption.
    - split; [exact G2|]. split; [clear - Hbig Hn1; lia|].
      unfold smsz, pg_up. apply Z.mod_divide; [lia|]. exists (((needed n + rz_size n + 4095) / 4096) + 1). lia.
    - unfold gobj. clear - G1 G3 G4 G5 HLk. unfold img_hull_lo, img_hull_hi, SEGTOP_A, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in *. lia.
    - unfold gobj. clear - PA1 PA3 PA4 PA5 HLk. unfold img_hull_lo, img_hull_hi, SEGTOP_A, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in *. lia.
    - unfold gobj. clear - Y1 Y3 Y4 Y5 HLk. unfold img_hull_lo, img_hull_hi, SEGTOP_A, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in *. lia.
    - unfold gobj. clear - X1 X3 X4 X5 HLk. unfold img_hull_lo, img_hull_hi, SEGTOP_A, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in *. lia.
    - clear - LG1 LG3 LG4 LG5 HLk Lbig Ln1. unfold SEGTOP_A, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in *. lia.
    - unfold sapart. clear - ALP Lbig Ln1. lia.
    - unfold sapart. clear - AMX. lia.
    - unfold sapart. clear - AP23. lia.
    - unfold sapart. clear - AP12. lia.
    - unfold sapart. clear - AP13. lia.
    - unfold sapart. clear - ALT Lbig Ln1. lia.
    - unfold sapart. clear - ALX Lbig Ln1. lia.
    - clear - Hkl SW1 Hwsl. unfold SEC_MAX in *. lia.
    - rewrite Nat2Z.id. exact HWI.
    - replace (Z.to_nat (Z.of_nat NS - 1)) with (NS - 1)%nat by (clear - Hkl; lia). exact HWL.
    - clear - HSB HLk. destruct HSB as (? & _ & ? & _). unfold kHighShadowEnd in *. lia.
    - clear - N5. lia.
    - clear - N6. lia. }
  intros ms2 P2.
  destruct P2 as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & m2 & -> & MU2 & WM2 & MI2 & MID2 & K2).
  rewrite RSP in MU2.
  apply evt_done. unfold svc_mad.
  exists v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, m2, ws, lst, muw, mudw.
  split; [reflexivity|].
  split.
  { apply (munch_trans _ m m1 m2).
    - apply (munch_weaken (qcbrec_sec_W T (C - 112)) _ m m1); [|exact MU1]. intros x Hx. apply outside_app_inv in Hx. exact (proj1 Hx).
    - apply (munch_weaken (sd_W (C - 112) MB MSZ PAB (Z.of_nat k) (s_mb lst)) _ m1 m2); [|exact MU2]. intros x Hx.
      apply outside_app_inv in Hx. exact (proj2 Hx). }
  split; [exact (wmono_trans _ _ _ _ WM1 WM2)|]. split; [exact MI2|]. split; [exact MID2|]. split; [exact K2|].
  split; [exact Hwsl|]. split; [exact Hwsf | exact Hlst].
Qed.


(* [comment removed for export] *)
Lemma ds_fin : forall (W0 : list ivl) (lst : secst) (ws : list word) (m2 : mem) (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 muw mudw : word),
  nth_error (sec Σk) (NS - 1) = Some lst -> Z.of_nat (length ws) = 0x4000 ->
  firstn NS ws = map (fun s0 => Z_to_bv 64 (s_mb s0)) (sec Σk) ->
  munch (W0 ++ [(s_mb lst + 24, s_mb lst + 32)]) m m2 -> wmono bsegs m m2 ->
  Forall (dzoneP Σk [] [] [k] (TZ_ST T) IZ_S [] lo (C - 112)) W0 ->
  sd_K MB MSZ (needed n + rz_size n) PAB 0x4000 (Z.of_nat NS) (Z.of_nat k) (s_mb lst) T ws muw mudw m2 ->
  mem_inv bsegs m2 -> uod_frame m2 (Z_to_bv 64 (C - 112)) (Z_to_bv 64 0x197fcc) (Z_to_bv 64 C) (Z_to_bv 64 INST) (Z_to_bv 64 6947800) ->
  stk bsegs m2 lo (C - 112 - 48) ->
  svc_mun p j b ents i rest Σk k s
    (MSsvc (uod_regs (Z_to_bv 64 0x197fcc) (Z_to_bv 64 (C - 112)) (dl_gp p) (Z_to_bv 64 tpA) v0 v1 v2 MB MSZ v3 v4 v5 v6 v7
              (Z_to_bv 64 6948424) (Z_to_bv 64 b) (Z_to_bv 64 (2^37)) (Z_to_bv 64 (Z.of_nat (length ents)))
              (Z_to_bv 64 (b + 152 + 8 * Z.of_nat i)) (Z_to_bv 64 (Z.of_nat (length ents) + 16)) (Z_to_bv 64 (16 + Z.of_nat i))
              (dl_s10 p) (dl_s11 p) v8 v9 v10 v11)
           (dl_F p) (Z_to_bv 64 sec_munmap_ecall) (Z_to_bv 64 215) (dl_fc p) None m2 (seg_rom bsegs)).
Proof using HOK HWP HS Hk Hq DM QB Hib Eb.
  intros W0 lst ws m2 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 muw mudw Hlst Hwsl Hwsf MU WM CERT0 K2 MI2 UF2 ST2.
  pose proof HOK as (FDO & MST & HLO & HLO2 & HSP & HG0).
  pose proof HS as (El & Elv & Efr & Ecr & Eql & Einit).
  pose proof (geo_of_wfP _ _ HWP) as HG.
  pose proof (dl_nums p HLO HLO2 HSP HG0) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9).
  assert (HLk : l_ACEIL L <= lo) by (rewrite El; exact N9).
  pose proof DM as (HA & MI & ST & WM0 & RP & FR & QR).
  pose proof HG as (HL & HR & HSW & HFW).
  pose proof HSW as (SW1 & SW2 & SW3 & SW4 & SW5 & SW6).
  pose proof (nth_error_lt _ _ _ Hk) as Hkl.
  assert (Hnres : sec_nres Σk = 0x4000) by (apply SW3; intros E; rewrite E in Hk; destruct k; discriminate).
  pose proof (proj1 (Forall_forall _ _) SW4 lst (nth_error_In _ _ Hlst)) as ((Ln1 & Ln2) & (LG1 & LG2 & LG3 & LG4 & LG5) & LGP & LGF & LGS).
  pose proof (smsz_big (s_n lst) ltac:(clear - Ln1; lia)) as Lbig.
  pose proof (dk_geo Σk HG) as (GG1 & GG2 & GG3 & GG4 & GG5 & GG6 & GG7 & GG8).
  assert (HTZ : Forall (fun z => T <= fst z /\ snd z <= T + 4096) (TZ_ST T)) by (unfold TZ_ST; repeat constructor; cbn; lia).
  assert (HTZd : disjoint_from (TZ_ST T) T 0x30 /\ disjoint_from (TZ_ST T) (T + 48) 16 /\ disjoint_from (TZ_ST T) (T + 0xc60) 1
            /\ (forall c', 1 <= c' <= 31 -> disjoint_from (TZ_ST T) (pc_addr T c') 80) /\ disjoint_from (TZ_ST T) (qcacheT T) 32).
  { unfold TZ_ST, pc_addr, qcacheT. cbn [disjoint_from]. split; [split; [lia | exact I]|]. split; [split; [lia | exact I]|].
    split; [split; [lia | exact I]|]. split; [intros c' Hc'; split; [lia | exact I] | split; [lia | exact I]]. }
  destruct K2 as (SCK & PDK & SJK2 & WSK & LIK & _). rewrite Nat2Z.id in WSK.
  set (LC := [(s_mb lst + 24, s_mb lst + 32)]) in *.
  assert (HQB : Forall (fun b0 => exists j0, nth_error (r_st (pr Σk 24)) j0 = Some CkBatch /\ fst b0 = p_abeg (l_SB (lay Σk)) 24 j0) (ql Σk ++ qg Σk))
    by exact (hqb_of_wfP _ _ HWP).
  pose proof HWP as (_ & _ & Hlive & _ & _ & _ & _ & Hdep & _).
  assert (CERT : Forall (dzoneP Σk [] [] [k; (NS - 1)%nat] (TZ_ST T) IZ_S [] lo (C - 112)) (W0 ++ LC)).
  { apply Forall_app. split; [apply (dzoneP_mono_DS _ _ _ [k]); [intros x [E|[]]; left; exact E | exact CERT0]|].
    apply Forall_cons; [|apply Forall_nil]. do 7 right. left. exists (NS - 1)%nat, lst. split; [right; left; reflexivity|].
    split; [exact Hlst|]. cbn [fst snd]. clear - Lbig Ln1. lia. }
  (* [comment removed for export] *)
  assert (LCS : forall a n0, l_ACEIL L <= a -> disjoint_from LC a n0).
  { intros a n0 Ha. unfold LC. cbn [disjoint_from]. split; [|exact I]. clear - Ha LG3 Lbig Ln1. lia. }
  assert (STK_AV : forall a n0, C - 112 <= a -> a + n0 <= USTACK_TOP -> disjoint_from (W0 ++ LC) a n0).
  { intros a n0 H1 H2. apply dsj_app; [|apply LCS; clear - H1 HLk N5; lia].
    exact (dp_stack_hw Σk [] [] [k] (TZ_ST T) IZ_S [] lo (C - 112) HG (da_HD Σk) (da_HD Σk) da_HDC IZ_S_in HTZ HLk ltac:(clear - N5; lia) W0 CERT0 a n0 H1 H2). }
  assert (SLOT_AV : forall j', nth_error (r_st (pr Σk 24)) j' = Some CkBatch -> disjoint_from (W0 ++ LC) (p_abeg SB 24 j') 8192).
  { intros j' Hj'. pose proof (dp_slot_in Σk HG 24 j' _ ltac:(clear; lia) Hj') as (S1 & S2 & _). change (ClassSize 24) with 8192 in S1, S2 |- *.
    apply dsj_app.
    - exact (dp_slot_hw Σk [] [] [k] (TZ_ST T) IZ_S [] lo (C - 112) HG (da_HD Σk) (da_HD Σk) da_HDC IZ_S_in HTZ HLk W0 CERT0 24 j' CkBatch (p_abeg SB 24 j') 8192
               ltac:(clear; lia) Hj' ltac:(intros []) ltac:(clear; lia) ltac:(change (ClassSize 24) with 8192; clear; lia)).
    - unfold LC. cbn [disjoint_from]. split; [|exact I]. clear - S1 S2 LGP GG7 Lbig Ln1. unfold apart in LGP. lia. }
  unfold svc_mun. exists v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, m2. split; [reflexivity|].
  split.
  { (* [comment removed for export] *)
    apply (ds_artc Σk m m2 (W0 ++ LC) k s lst (TZ_ST T) lo (C - 112) ws HG Hk Hlst HTZ HTZd HLk CERT HA Hdep HQB MU WM).
    - rewrite Hnres. exact SCK.
    - exact PDK. - exact SJK2. - exact WSK. - rewrite Hnres. exact Hwsl. - exact Hwsf.
    - intros Hlt. split; [|exact LIK].
      assert (HnIn : ~ In (NS - 1)%nat [k]) by (intros [E|[]]; clear - E Hlt; lia).
      pose proof (kw_schunk Σk W0 [k] HG
                    (dp_shad_app_hw Σk [] [] [k] (TZ_ST T) IZ_S [] lo (C - 112) HG (da_HD Σk) (da_HD Σk) da_HDC IZ_S_in HTZ HLk W0 CERT0)
                    (dp_secmap_hw Σk [] [] [k] (TZ_ST T) IZ_S [] lo (C - 112) HG (da_HD Σk) (da_HD Σk) da_HDC IZ_S_in HTZ HLk W0 CERT0)
                    (NS - 1)%nat lst Hlst HnIn) as (LA1 & LA2 & LA3 & LA4 & LA5 & LA6).
      assert (LSH : forall a n0, 0 <= n0 -> shad (s_mb lst) <= a -> a + n0 <= shad (s_mb lst + smsz (s_n lst)) -> disjoint_from LC a n0).
      { intros a n0 H0 H1 H2. unfold LC. cbn [disjoint_from]. split; [|exact I].
        pose proof (dp_shad_rng (s_mb lst) ltac:(lia)). pose proof (dp_shad_rng (s_mb lst + smsz (s_n lst)) ltac:(lia)).
        clear - H0 H1 H2 H H3 LG4 Lbig Ln1. unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *. lia. }
      pose proof (dp_shad_mono (s_mb lst) (s_mb lst + 4096 + 2048) ltac:(lia)) as Q1.
      pose proof (fk_map Σk HG _ lst Hlst) as (_ & _ & _ & _ & _ & _ & _ & LRoom & LRu & _).
      assert (Hru : 8 <= ru8 (s_n lst) /\ s_n lst <= ru8 (s_n lst) /\ 6144 + ru8 (s_n lst) <= smsz (s_n lst)).
      { split; [|split; [exact LRu | exact LRoom]]. unfold ru8.
        assert (X : 1 <= (s_n lst + 7) / 8) by (apply Z.div_le_lower_bound; clear - Ln1; lia). clear - X; lia. }
      unfold schunk_avoid_nh. split; [|split; [|split; [|split; [|split]]]].
      + apply dsj_app; [apply (dsj_sub W0 (s_mb lst) 32); [exact LA1 | clear; lia | clear; lia]|]. unfold LC. cbn [disjoint_from]. split; [clear; lia | exact I].
      + apply dsj_app; [exact LA2|]. unfold LC. cbn [disjoint_from]. split; [clear; lia | exact I].
      + apply dsj_app; [exact LA3|]. unfold LC. cbn [disjoint_from]. split; [|exact I]. destruct (s_quar lst); clear; lia.
      + apply dsj_app; [exact LA4|]. apply LSH; [clear; lia | clear; lia|]. change ((4096 + 2048) / 8) with 768. rewrite Z.max_r by (clear; lia).
        pose proof (fk_shad_le2 (s_mb lst) 6144 ltac:(clear - LG1; lia) ltac:(clear; lia)) as LX1.
        pose proof (dp_shad_mono (s_mb lst + 6144) (s_mb lst + smsz (s_n lst)) ltac:(clear - Hru; lia)) as LX2. change (6144 / 8) with 768 in LX1. clear - LX1 LX2. lia.
      + apply dsj_app; [exact LA5|]. destruct Hru as (U1 & U2 & U3).
        pose proof (fk_shad_le2 (s_mb lst + 6144) (ru8 (s_n lst)) ltac:(clear - LG1; lia) ltac:(clear - U1; lia)) as E2.
        pose proof (dp_shad_mono (s_mb lst + 6144 + ru8 (s_n lst)) (s_mb lst + smsz (s_n lst)) ltac:(clear - U3; lia)) as E4.
        pose proof (dp_shad_mono (s_mb lst) (s_mb lst + 6144) ltac:(clear; lia)) as E5.
        assert (E7 : 0 <= ru8 (s_n lst) / 8) by (apply Z.div_pos; clear - U1; lia).
        replace (s_mb lst + 4096 + 2048) with (s_mb lst + 6144) by (clear; ring).
        apply LSH; [clear; lia | exact E5|].
        destruct (s_quar lst); [rewrite fdrun_lenZ by exact E7 | rewrite (fl_ushadow_len (s_n lst)) by (clear - Ln1; lia)]; clear - E2 E4; lia.
      + apply dsj_app; [exact LA6|]. destruct Hru as (U1 & U2 & U3).
        pose proof (fk_shad_le2 (s_mb lst + 6144 + ru8 (s_n lst)) (smsz (s_n lst) - 6144 - ru8 (s_n lst)) ltac:(clear - LG1 U1; lia) ltac:(clear - U3; lia)) as E3.
        replace (s_mb lst + 6144 + ru8 (s_n lst) + (smsz (s_n lst) - 6144 - ru8 (s_n lst))) with (s_mb lst + smsz (s_n lst)) in E3 by (clear; ring).
        pose proof (dp_shad_mono (s_mb lst) (s_mb lst + 6144 + ru8 (s_n lst)) ltac:(clear - U1; lia)) as E6.
        assert (E8 : 0 <= (smsz (s_n lst) - 6144 - ru8 (s_n lst)) / 8) by (apply Z.div_pos; clear - U3; lia).
        replace (s_mb lst + 4096 + 2048 + ru8 (s_n lst)) with (s_mb lst + 6144 + ru8 (s_n lst)) by (clear; ring).
        replace (smsz (s_n lst) - 4096 - 2048 - ru8 (s_n lst)) with (smsz (s_n lst) - 6144 - ru8 (s_n lst)) by (clear; ring).
        rewrite Z.max_r by exact E8.
        apply LSH; [exact E8 | exact E6 | clear - E3; lia]. }
  split; [exact MI2|]. split; [exact UF2|]. split; [exact ST2|].
  (* [comment removed for export] *)
  split.
  { destruct WM0 as (G & WG & HGo). exists G. split; [exact (wmono_out_wmono G _ m m2 WG WM) | exact HGo]. }
  split.
  { apply (rt_pres_trans _ _ _ _ m m2 RP). intros a Ha. apply MU.
    rewrite <- Elv, <- Efr in Ha.
    apply (ds_client Σk W0 k s lst (TZ_ST T) lo (C - 112) HG Hk Hq (nth_error_In _ _ Hlst) HTZ HLk ltac:(lia) CERT0 Hlive).
    destruct Ha as [Ha|Ha]; [left; clear - Ha; lia | right; exact Ha]. }
  pose proof FR as (FR1 & FR2 & FR3).
  split.
  { split; [|split].
    - apply (rw_cells_transport bsegs _ m m2 _ _ FR1 MU WM). apply STK_AV; cbn [cells_size csize Nat.add Z.of_nat]; clear - N6; unfold USTACK_TOP; lia.
    - apply (rw_cells_transport bsegs _ m m2 _ _ FR2 MU WM). apply STK_AV; cbn [cells_size csize Nat.add Z.of_nat]; clear - N6; unfold USTACK_TOP; lia.
    - apply (rw_cells_transport bsegs _ m m2 _ _ FR3 MU WM). apply STK_AV; cbn [cells_size csize Nat.add Z.of_nat]; clear - N6; unfold USTACK_TOP; lia. }
  split.
  { apply (qcache_rep_frame _ m m2 C rest QR MU WM); [apply STK_AV; clear - N6; unfold USTACK_TOP; lia|].
    apply Forall_forall. intros (b', ents') Hin.
    destruct (dl_batch_of_in Σk _ b' ents' HWP (or_intror Hin)) as (j' & Hj' & Eb'). cbn [fst]. rewrite Eb'. exact (SLOT_AV j' Hj'). }
  apply (qbatch_frame _ m m2 b (qfirst rest) ents QB MU WM). rewrite Eb. exact (SLOT_AV ib Hib).
Qed.

Definition mad_eff : SyscallEffect :=
  mkEffect (Z_to_bv 64 0) [] [(Z_to_bv 64 (pbeg (shad MB)), Z_to_bv 64 (pend (shad (MB + MSZ)) - pbeg (shad MB)))].

Lemma ds_run2 : forall ms0, svc_mad ms0 -> evt bsegs (svc_mun p j b ents i rest Σk k s) (nretA ms0 mad_eff).
Proof using HOK HWP HS Hk Hq DM QB Hib Eb.
  intros ms0 (t0' & t1' & t2' & a4' & a5' & a6' & t3' & t4' & t5' & t6' & mA & ws & lst & muw & mudw
              & -> & MU1 & WM1 & MI1 & MID & K1 & Hwsl & Hwsf & Hlst).
  pose proof HOK as (FDO & MST & HLO & HLO2 & HSP & HG0).
  pose proof HS as (El & Elv & Efr & Ecr & Eql & Einit).
  pose proof (geo_of_wfP _ _ HWP) as HG.
  pose proof (dl_nums p HLO HLO2 HSP HG0) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9).
  assert (HLk : l_ACEIL L <= lo) by (rewrite El; exact N9).
  pose proof (dg_ok Σk HG) as (HT & HSB & TSEP).
  pose proof HG as (HL & HR & HSW & HFW).
  pose proof HSW as (SW1 & SW2 & SW3 & SW4 & SW5 & SW6).
  pose proof (proj1 (Forall_forall _ _) SW4 s (nth_error_In _ _ Hk)) as ((Hn1 & Hn2) & (G1 & G2 & G3 & G4 & G5) & GP & GF & GS).
  pose proof (nth_error_lt _ _ _ Hk) as Hkl.
  pose proof (smsz_big n ltac:(clear - Hn1; lia)) as Hbig.
  pose proof (proj1 (Forall_forall _ _) SW4 lst (nth_error_In _ _ Hlst)) as ((Ln1 & Ln2) & (LG1 & LG2 & LG3 & LG4 & LG5) & LGP & LGF & LGS).
  pose proof (smsz_big (s_n lst) ltac:(clear - Ln1; lia)) as Lbig.
  pose proof (dk_geo Σk HG) as (GG1 & GG2 & GG3 & GG4 & GG5 & GG6 & GG7 & GG8).
  pose proof (g_grant Σk HG PAB 0x800000 ltac:(unfold startup_grants; right; left; reflexivity)) as (PA1 & PA2 & PA3 & PA4 & PA5).
  pose proof (g_grant Σk HG TCX 0x10000 ltac:(unfold startup_grants; right; right; right; left; reflexivity)) as (X1 & X2 & X3 & X4 & X5).
  pose proof (g_grant Σk HG T 4096 ltac:(unfold startup_grants; right; right; left; reflexivity)) as (Y1 & Y2 & Y3 & Y4 & Y5).
  pose proof (g_apart Σk HG 1 2 _ _ ltac:(clear; lia) eq_refl eq_refl) as AP12. pose proof (g_apart Σk HG 2 3 _ _ ltac:(clear; lia) eq_refl eq_refl) as AP23.
  cbn [fst snd] in AP12, AP23. unfold apart in AP12, AP23.
  pose proof (proj1 (Forall_forall _ _) GS (PAB, 0x800000) ltac:(unfold startup_grants; right; left; reflexivity)) as AMP.
  pose proof (proj1 (Forall_forall _ _) GS (T, 4096) ltac:(unfold startup_grants; right; right; left; reflexivity)) as AMT.
  pose proof (proj1 (Forall_forall _ _) LGS (T, 4096) ltac:(unfold startup_grants; right; right; left; reflexivity)) as ALT.
  cbn [fst snd] in AMP, AMT, ALT. unfold apart in AMP, AMT, ALT, GP.
  assert (ALM : s_mb lst = MB \/ s_mb lst + 32 <= MB \/ MB + MSZ <= s_mb lst).
  { destruct (Nat.eq_dec (NS - 1) k) as [E|E].
    - left. rewrite E in Hlst. rewrite Hk in Hlst. injection Hlst as <-. reflexivity.
    - pose proof (SW5 (NS - 1)%nat k lst s Hlst Hk E) as A. unfold apart in A. clear - A Lbig Ln1. lia. }
  assert (MB8 : MB mod 8 = 0) by (apply (mod8_of _ 4096 ltac:(clear; lia) G2); exists 512; reflexivity).
  assert (MSZ8 : MSZ mod 8 = 0).
  { unfold smsz, pg_up. apply Z.mod_divide; [clear; lia|]. exists (((needed n + rz_size n + 4095) / 4096) * 512 + 512). clear; lia. }
  assert (ESH : shad (MB + MSZ) = shad MB + MSZ / 8) by (apply shad_add8'; assumption).
  assert (RSP : bv_unsigned (Z_to_bv 64 (C - 112)) = C - 112) by (apply unsigned_lit; clear - N5 N6 N4; lia).
  eapply evt_cut.
  { unfold mad_eff.
    apply (secdealloc_A2_spec (Z_to_bv 64 0x197fcc) (Z_to_bv 64 (C - 112)) (dl_gp p) t0' t1' t2' (Z_to_bv 64 C) (Z_to_bv 64 INST) a4' a5' a6'
             (Z_to_bv 64 6947800) (Z_to_bv 64 6948424) (Z_to_bv 64 b) (Z_to_bv 64 (2^37)) (Z_to_bv 64 (Z.of_nat (length ents)))
             (Z_to_bv 64 (b + 152 + 8 * Z.of_nat i)) (Z_to_bv 64 (Z.of_nat (length ents) + 16)) (Z_to_bv 64 (16 + Z.of_nat i))
             (dl_s10 p) (dl_s11 p) t3' t4' t5' t6' (dl_F p) (dl_fc p) mA MB MSZ (needed n + rz_size n) (Z.of_nat k) PAB 0x4000 (Z.of_nat NS)
             (s_mb lst) TCX T lo ws muw mudw); rewrite ?RSP.
    all: try assumption.
    - split; [exact G2|]. split; [clear - Hbig Hn1; lia|].
      unfold smsz, pg_up. apply Z.mod_divide; [clear; lia|]. exists (((needed n + rz_size n + 4095) / 4096) + 1). clear; lia.
    - unfold gobj. clear - G1 G3 G4 G5 HLk. unfold img_hull_lo, img_hull_hi, SEGTOP_A, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in *. lia.
    - unfold gobj. clear - PA1 PA3 PA4 PA5 HLk. unfold img_hull_lo, img_hull_hi, SEGTOP_A, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in *. lia.
    - unfold gobj. clear - Y1 Y3 Y4 Y5 HLk. unfold img_hull_lo, img_hull_hi, SEGTOP_A, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in *. lia.
    - unfold gobj. clear - X1 X3 X4 X5 HLk. unfold img_hull_lo, img_hull_hi, SEGTOP_A, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in *. lia.
    - clear - LG1 LG3 LG4 LG5 HLk Lbig Ln1. unfold SEGTOP_A, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in *. lia.
    - unfold sapart. clear - AP23. lia.
    - unfold sapart. clear - AP12. lia.
    - unfold sapart. clear - ALT Lbig Ln1. lia.
    - clear - Hkl SW1 Hwsl. unfold SEC_MAX in *. lia.
    - clear - HSB HLk. destruct HSB as (? & _ & ? & _). unfold kHighShadowEnd in *. lia.
    - clear - N5. lia.
    - clear - N6. lia. }
  intros ms2 P2.
  destruct P2 as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & m2 & -> & MU2 & WM2 & MI2 & UF2 & ST2 & K2).
  rewrite RSP in MU2, ST2.
  apply evt_done.
  set (W0 := qcbrec_sec_W T (C - 112) ++ [(shad MB, shad MB + MSZ / 8); (C - 112 - 96, C - 112); (C - 112 - 32, C - 112);
                (i_sec_mutex, i_sec_mutex + 4); (i_sec_nres + 8, i_sec_nres + 16); (i_sec_sorted, i_sec_sorted + 40);
                (PAB + 8 * Z.of_nat k, PAB + 8 * Z.of_nat k + 8); (i_gstat_alloc, i_gstat_alloc + 16)] ++ sd_W3 (C - 112) MB MSZ T).
  apply (ds_fin W0 lst ws m2 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 muw mudw Hlst Hwsl Hwsf); [| exact (wmono_trans _ _ _ _ WM1 WM2) | | exact K2 | exact MI2 | exact UF2 | exact ST2].
  - apply (munch_trans (W0 ++ [(s_mb lst + 24, s_mb lst + 32)]) m mA m2).
    + apply (munch_weaken (qcbrec_sec_W T (C - 112) ++ sd_W (C - 112) MB MSZ PAB (Z.of_nat k) (s_mb lst)) _ m mA); [|exact MU1]. intros x Hx. refine (outside_incl _ _ x _ Hx).
      intros iv Hiv. subst W0. unfold qcbrec_sec_W, sd_W, sd_W1, sd_W3 in *. cbn [app In] in Hiv |- *. clear - Hiv.
      repeat (destruct Hiv as [Hiv|Hiv]; [subst iv; repeat (first [left; reflexivity | right]) |]). destruct Hiv.
    + apply (munch_weaken (sd_W3 (C - 112) MB MSZ T) _ mA m2); [|exact MU2]. intros x Hx. refine (outside_incl _ _ x _ Hx).
      intros iv Hiv. subst W0. unfold qcbrec_sec_W, sd_W, sd_W1, sd_W3 in *. cbn [app In] in Hiv |- *. clear - Hiv.
      repeat (destruct Hiv as [Hiv|Hiv]; [subst iv; repeat (first [left; reflexivity | right]) |]). destruct Hiv.
  - unfold W0, qcbrec_sec_W, sd_W3. cbn [app].
    repeat apply Forall_cons; try apply Forall_nil.
    + left. exists (i_sec_mutex, i_sec_mutex + 4). split; [left; reflexivity | cbn; clear; lia].
    + right; left. exists (T + 2768, T + 3168). split; [left; reflexivity | cbn; clear; lia].
    + do 9 right. left. cbn. clear - N5; lia.
    + do 8 right. left. exists k, s. split; [left; reflexivity|]. split; [exact Hk|]. cbn [fst snd]. rewrite ESH. clear; lia.
    + do 9 right. left. cbn. clear - N5; lia.
    + do 9 right. left. cbn. clear - N5; lia.
    + left. exists (i_sec_mutex, i_sec_mutex + 4). split; [left; reflexivity | cbn; clear; lia].
    + left. exists (i_sec_nres + 8, i_sec_nres + 16). split; [right; left; reflexivity | cbn; clear; lia].
    + left. exists (i_sec_sorted, i_sec_sorted + 40). split; [right; right; left; reflexivity | cbn; clear; lia].
    + do 10 right. cbn. clear - Hkl SW1. unfold SEC_MAX in *. lia.
    + left. exists (i_gstat_alloc, i_gstat_alloc + 16). split; [right; right; right; left; reflexivity | cbn; clear; lia].
    + (* [comment removed for export] *)
      do 8 right. left. exists k, s. split; [left; reflexivity|]. split; [exact Hk|]. cbn [fst snd].
      assert (SH0 : 0 <= shad MB) by (unfold shad, SHB; pose proof (Z.div_pos MB 8 ltac:(clear - G1; lia) ltac:(clear; lia)); lia).
      pose proof (pbeg_facts (shad MB) SH0) as (PBF & _).
      pose proof (pend_facts (shad (MB + MSZ)) ltac:(rewrite ESH; pose proof (Z.div_pos MSZ 8 ltac:(clear - Hbig Hn1; lia) ltac:(clear; lia)); lia)) as (PEF & _).
      clear - PBF PEF; lia.
    + do 9 right. left. cbn. clear - N5; lia.
    + right; left. exists (T + 2768, T + 3168). split; [left; reflexivity | cbn; clear; lia].
Qed.

End RunA.
