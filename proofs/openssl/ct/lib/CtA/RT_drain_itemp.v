(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Mem Frame Cells Step Arr Exec RzCPS MState ITree Nodes. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface D_defs R_cache_defs R_prim_defs R_glue_defs R_m2s R_thread R_poison R_prim_kit R_depot_defs R_quar_defs R_qrec_defs R_qrecycle R_qdorec R_qcbrec R_cdealloc RT_state RT_rep RT_frame RT_trans RT_sep RT_freelift RT_geo0 RT_fkit RT_freestate RT_freeE RT_sys_stmt RT_drain_defs RT_drain_pure RT_drain_led RT_drain_kit RT_drain_art3 RT_drain_geo RT_drain_qcbp RT_drain_cdk RT_drain_cdeal RT_drain_ldefs RT_drain_istmt RT_drain_loop.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Lemma skipn_nth_cons : forall {X} (l : list X) i d, (i < length l)%nat -> skipn i l = nth i l d :: skipn (S i) l.
Proof. intros X l. induction l as [|x l IH]; intros [|i] d H; cbn in *; try lia; [reflexivity|]. apply IH. lia. Qed.

(* [comment removed for export] *)
Lemma cps_pointwise : forall (Σ : rtsA) (PMc : Model -> Prop) (Pm : machine_state -> Prop) (Q : config -> Prop),
  (forall ms, Pm ms -> cps ctasegs (ASTA RTA Σ PMc (eq ms)) Q) -> cps ctasegs (ASTA RTA Σ PMc Pm) Q.
Proof.
  intros Σ PMc Pm Q H T cf (H1 & H2 & H3 & H4) Hk. apply (H _ H2 T cf); [|exact Hk].
  split; [exact H1|]. split; [reflexivity|]. split; [exact H3 | exact H4].
Qed.

(* [comment removed for export] *)
Lemma pres_munch : forall L F z (m m' : mem), rt_pres L F z m m' -> munch [(0, z); (USTACK_TOP, 2 ^ 64)] m m'.
Proof.
  intros L F z m m' H x Hx. apply H. cbn [outside] in Hx. left.
  pose proof (bv_unsigned_in_range 64 x) as X. unfold bv_modulus in X. cbn [Z.of_N] in X. lia.
Qed.

Lemma rt_pres_mono : forall L F z z' (m m' : mem), rt_pres L F z m m' -> z <= z' -> rt_pres L F z' m m'.
Proof. intros L F z z' m m' H Hz a Ha. apply H. destruct Ha as [Ha|Ha]; [left; lia | right; exact Ha]. Qed.

Lemma rt_pres_trans : forall L F z (m1 m2 m3 : mem), rt_pres L F z m1 m2 -> rt_pres L F z m2 m3 -> rt_pres L F z m1 m3.
Proof. intros L F z m1 m2 m3 H1 H2 a Ha. rewrite (H2 a Ha). exact (H1 a Ha). Qed.

(* [comment removed for export] *)
Section IpGeo.
Variables (Σ : rtsA) (c : Z) (ic : nat) (n C lo : Z).
Hypothesis HG : geo_ok Σ.
Hypothesis Hc : 1 <= c <= 31.
Hypothesis Hic : nth_error (r_st (pr Σ c)) ic = Some (CkQuar n).
Hypothesis HL1 : l_ACEIL (lay Σ) <= lo.
Hypothesis HL2 : lo <= C - 1136.
Hypothesis HL3 : C <= 2 ^ 47.
#[local] Notation SB := (l_SB (lay Σ)).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation AB := (p_abeg (l_SB (lay Σ)) c ic).
#[local] Notation W12 := (W_QCB (p_abeg (l_SB (lay Σ)) c ic) (p_abeg (l_SB (lay Σ)) c ic + rz_size n - 16) n (l_T (lay Σ)) C
                          ++ W_CD (l_T (lay Σ)) (l_SB (lay Σ)) c (C - 112)).

Lemma ip_facts : AB + 8 <= AB + ClassSize c /\ AB <= AB + rz_size n - 16 /\ AB + rz_size n - 16 + 4 <= AB + ClassSize c
  /\ SHB <= shad (AB + rz_size n - 16 + 16) /\ shad (AB + rz_size n - 16 + 16) + ru8 n / 8 <= 2 ^ 44 + SHB
  /\ SHB <= shad (rb SB c + kUserCap) /\ shad (rb SB c + 2 ^ 32) <= 2 ^ 44 + SHB
  /\ AB + ClassSize c <= SB + 2 ^ 37 /\ 0 <= AB.
Proof using HG Hc Hic.
  clear HL1 HL2 HL3. pose proof (qp_fit Σ c ic n HG Hc Hic) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12).
  pose proof (qp_slot Σ c ic n HG Hc Hic) as (P1 & P2 & P3 & P4 & P5 & G1 & G2 & G3).
  pose proof (dk_rb Σ HG c Hc) as (B1 & B2 & B3 & B4). pose proof (dk_geo Σ HG) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8).
  pose proof (shad_len (AB + rz_size n - 16 + 16) (ru8 n) ltac:(lia) ltac:(lia) ltac:(lia)) as (SL1 & SL2).
  assert (Z.max 0 (ru8 n / 8) = ru8 n / 8) by (apply Z.max_r; apply Z.div_pos; lia).
  pose proof (shad_len (rb SB c + kUserCap) (2 ^ 32 - kUserCap) ltac:(unfold rb, kUserCap in *; lia) ltac:(unfold kUserCap; lia)
                 ltac:(unfold rb, kUserCap in *; lia)) as (SL3 & _).
  pose proof (fk_shad_mono (rb SB c + 2 ^ 32) (2 ^ 47) ltac:(unfold rb in *; lia)) as SL4.
  assert (SL5 : shad (2 ^ 47) = 2 ^ 44 + SHB) by reflexivity.
  repeat split; lia.
Qed.

Lemma ip_batch_av : forall j', nth_error (r_st (pr Σ 24)) j' = Some CkBatch -> disjoint_from W12 (p_abeg SB 24 j') 8192.
Proof using HG Hc Hic HL1 HL2 HL3.
  intros j' Hj.
  pose proof ip_facts as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9).
  pose proof (g_slot_apart Σ HG c ic 24 j' _ _ Hc ltac:(lia) Hic Hj
                ltac:(destruct (Z.eq_dec c 24) as [->|X]; [right; intros <-; rewrite Hic in Hj; discriminate | left; exact X])) as AP.
  change (ClassSize 24) with 8192 in AP.
  pose proof (dk_slot_in Σ HG 24 j' _ ltac:(lia) Hj) as (U1 & U2 & U3 & U4 & U5 & U6). change (ClassSize 24) with 8192 in *.
  pose proof (dk_geo Σ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
  pose proof (dk_rb Σ HG c Hc) as (B1 & B2 & B3 & B4).
  pose proof (dg_ok Σ HG) as (HT & HSB & TSEP). pose proof HT as (T1 & T2 & T3 & T4 & T5). pose proof HSB as (Y1 & Y2 & Y3 & Y4).
  assert (HTT : T + 4096 <= SB \/ SB + 2 ^ 37 + 4096 <= T) by (destruct TSEP as (_ & _ & _ & _ & X & _); exact X).
  unfold W_QCB, W_CD. cbn [app disjoint_from]. unfold pc_addr, rinfo, RIS_of, fa, rb, kFaCap, kUserCap, SHB, kHighShadowEnd in *.
  repeat split; lia.
Qed.

Lemma ip_stack_av : forall a k, C - 112 <= a -> 0 <= k -> disjoint_from W12 a k.
Proof using HG Hc Hic HL1 HL2 HL3.
  intros a k Ha Hk.
  pose proof ip_facts as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9).
  pose proof (dk_geo Σ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
  pose proof (dk_rb Σ HG c Hc) as (B1 & B2 & B3 & B4).
  pose proof (dg_ok Σ HG) as (HT & HSB & TSEP). pose proof HT as (T1 & T2 & T3 & T4 & T5).
  unfold W_QCB, W_CD. cbn [app disjoint_from]. unfold pc_addr, rinfo, RIS_of, fa, rb, kFaCap, kUserCap, SHB in *.
  repeat split; lia.
Qed.

End IpGeo.

Lemma dl_batch_of_in : forall Σk P b' ents', rt_wfP Σk P -> In (b', ents') P ->
  exists j', nth_error (r_st (pr Σk 24)) j' = Some CkBatch /\ b' = p_abeg (l_SB (lay Σk)) 24 j'.
Proof.
  intros Σk P b' ents' (_ & _ & _ & _ & (_ & _ & _ & Q4 & _) & _) Hin. unfold qallP in Q4.
  assert (Hb : In (b', ents') (ql Σk ++ qg Σk ++ P)) by (apply in_app_iff; right; apply in_app_iff; right; exact Hin).
  destruct (proj1 (Forall_forall _ _) Q4 _ Hb) as (j' & Hj & Eb). exists j'. split; [exact Hj | exact Eb].
Qed.

Section ItemP.
Variable p : dlp.
Hypothesis FC : fixed_commit_node.
Hypothesis HOK : dl_ok p.
#[local] Notation Σ0 := (dl_Σ0 p).
#[local] Notation usp := (dl_usp p).
#[local] Notation lo := (dl_lo p).
#[local] Notation PMc := (dl_PMc p).
#[local] Notation C := (dl_usp p - 2288).

Theorem item_prim_ok : item_prim_stmt p.
Proof using FC HOK.
  intros j Σk b ib ents i rest c ic n Hi HWP HS Hib Eb Hc Hic Hent.
  pose proof HOK as (FDO & MST & HLO & HLO2 & HSP & HG0).
  pose proof HS as (El & Elv & Efr & Ecr & Eql & Einit).
  pose proof (geo_of_wfP _ _ HWP) as HG.
  pose proof HWP as (HL & HR & Hlive & HSW & HQW & HFW & HB & Hdep & _).
  pose proof (hqb_of_wfP _ _ HWP) as HQB.
  pose proof (dl_nums p HLO HLO2 HSP HG0) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9).
  assert (HLk : l_ACEIL (lay Σk) <= lo) by (rewrite El; exact N9).
  pose proof (proj1 (proj2 (proj2 HR)) c Hc) as (Hcnt & _ & Hcl0).
  assert (Hcl : Forall (fun x => 0 <= x < Z.of_nat (length (r_st (pr Σk c)))) (ca Σk c)) by (eapply Forall_impl; [|exact Hcl0]; intros x (X & _); exact X).
  pose proof (proj1 HR c Hc) as HRW.
  assert (HAw : A_bytes (aw Σk) <= CREDIT0) by (destruct HB as (X1 & _ & X3 & _); lia).
  assert (HEg : rt_eager (recp Σk c ic) <= 2 ^ 38)
    by (exact (proj1 (proj2 (proj2 (proj2 (budget_wf_recp Σk c ic (CkQuar n) HB HR HSW Hc Hic ltac:(discriminate) Einit)))))).
  (* [comment removed for export] *)
  assert (Esk : skipn i ents = (p_abeg (l_SB (lay Σk)) c ic + rz_size n - 16, n) :: skipn (S i) ents)
    by (rewrite (skipn_nth_cons ents i (0, 0) Hi), Hent; reflexivity).
  rewrite Esk in HWP.
  pose proof (rt_wfP_recp Σk b _ n (skipn (S i) ents) rest c ic HWP Hc Hic eq_refl Einit) as HWP'.
  apply cps_pointwise. intros ms (t0 & t1 & t2 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m & -> & DM & QB).
  pose proof DM as (HA & MI & ST & WM0 & RP & FR & QR).
  pose proof FR as (FR1 & FR2 & FR3). pose proof FR2 as CBP0.
  apply (proj1 (rwc_app ctasegs m _ [C8 (Z_to_bv 64 (l_T (lay Σ0) + 208))] [C8 (Z_to_bv 64 (usp - 2128))])) in CBP0.
  destruct CBP0 as (CBP & _). rewrite <- El in CBP.
  rewrite Hent. cbn [fst].
  eapply (cps_seq ctasegs).
  { eapply (dl_evt Σk PMc _ _ MST). intros ms0 <-.
    exact (qcbp_evt Σk m C lo c ic n (dl_gp p) t0 t1 t2 (Z_to_bv 64 C) (Z_to_bv 64 INST) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 6744600)
             (Z_to_bv 64 6745224) (Z_to_bv 64 b) (Z_to_bv 64 (2 ^ 37)) (Z_to_bv 64 (Z.of_nat (length ents)))
             (Z_to_bv 64 (b + 152 + 8 * Z.of_nat i)) (Z_to_bv 64 (Z.of_nat (length ents) + 16)) (Z_to_bv 64 (16 + Z.of_nat i))
             (dl_s10 p) (dl_s11 p) t3 t4 t5 t6 (dl_F p) (dl_fc p) HG HA Hc Hic CBP ST HLk ltac:(lia) ltac:(lia) MI Hlive Hdep HQB). }
  apply cps_pointwise. intros ms1 (t0' & t1' & t2' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & HA1 & MU1 & WM1 & MI1 & ST1 & RP1).
  assert (Esp : bv_unsigned (Z_to_bv 64 (C - 112)) = C - 112) by (apply unsigned_lit; lia).
  eapply (cps_conseq ctasegs).
  - exact (cd_lift Σk PMc m1 c ic (CkQuar n) lo (Z_to_bv 64 0x19e0c0) (Z_to_bv 64 (C - 112)) (dl_gp p) t0' t1' t2' (Z_to_bv 64 C)
             (Z_to_bv 64 INST) a4' a5' a6' a7' (Z_to_bv 64 6744600) (Z_to_bv 64 6745224) (Z_to_bv 64 b) (Z_to_bv 64 (2 ^ 37))
             (Z_to_bv 64 (Z.of_nat (length ents))) (Z_to_bv 64 (b + 152 + 8 * Z.of_nat i)) (Z_to_bv 64 (Z.of_nat (length ents) + 16))
             (Z_to_bv 64 (16 + Z.of_nat i)) (dl_s10 p) (dl_s11 p) t3' t4' t5' t6' (dl_F p) (dl_fc p)
             FDO MST FC HG HA1 Hc Hic Einit HRW Hcl Hcnt ltac:(rewrite Esp; exact ST1) HLk ltac:(rewrite Esp; lia) ltac:(rewrite Esp; lia)
             MI1 Hlive Hdep HQB HL HAw HEg).
  - intros cf Hcf. unfold ASTA in *. eapply AST_conseq; [exact Hcf | intros ms E; rewrite <- E; reflexivity | intros mo X; exact X].
  - intros cf Hcf. exists (recp Σk c ic). split.
    + unfold ASTA in *. eapply AST_conseq; [exact Hcf | | intros mo X; exact X].
      intros ms2 (t0'' & t1'' & t2'' & a0'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m2 & -> & HA2 & MU2 & WM2 & MI2 & ST2 & RP2).
      rewrite Esp in MU2, ST2, RP2.
      rewrite (ret_pc_even 0x19e0c0); [| lia | reflexivity].
      exists (Z_to_bv 64 0x19e0c0), t0'', t1'', t2'', a0'', a1'', a2'', a3'', a4'', a5'', a6'', a7'', t3'', t4'', t5'', t6'', m2. split; [reflexivity|].
      assert (RPa : rt_pres (live Σ0) (frames Σ0) (C - 112) m m2).
      { rewrite <- Elv, <- Efr. exact (rt_pres_trans _ _ _ m m1 m2 RP1 RP2). }
      pose proof (pres_munch _ _ _ m m2 RPa) as MUa.
      assert (WMa : wmono ctasegs m m2) by exact (wmono_trans _ _ _ _ WM1 WM2).
      assert (MUb : munch (W_QCB (p_abeg (l_SB (lay Σk)) c ic) (p_abeg (l_SB (lay Σk)) c ic + rz_size n - 16) n (l_T (lay Σk)) C
                           ++ W_CD (l_T (lay Σk)) (l_SB (lay Σk)) c (C - 112)) m m2).
      { apply (munch_trans _ m m1 m2); eapply munch_weaken; [| exact MU1 | | exact MU2]; intros x Hx; apply outside_app_inv in Hx; destruct Hx as [Hx1 Hx2]; first [exact Hx1 | exact Hx2]. }
      assert (HBAV : forall j', nth_error (r_st (pr Σk 24)) j' = Some CkBatch -> disjoint_from (W_QCB (p_abeg (l_SB (lay Σk)) c ic)
                        (p_abeg (l_SB (lay Σk)) c ic + rz_size n - 16) n (l_T (lay Σk)) C ++ W_CD (l_T (lay Σk)) (l_SB (lay Σk)) c (C - 112))
                        (p_abeg (l_SB (lay Σk)) 24 j') 8192)
        by exact (ip_batch_av Σk c ic n C lo HG Hc Hic HLk ltac:(lia) ltac:(lia)).
      split.
      * split; [exact HA2|]. split; [exact MI2|]. split; [exact ST2|].
        split; [destruct WM0 as (G & WG & HGo); exists G; split; [exact (wmono_out_wmono G _ m m2 WG WMa) | exact HGo]|].
        split; [exact (rt_pres_trans _ _ _ _ m m2 RP (rt_pres_mono _ _ (C - 112) (C + 32) m m2 RPa ltac:(lia)))|].
        split.
        -- split; [|split].
           ++ apply (rw_cells_transport ctasegs _ m m2 _ _ FR1 MUa WMa). cbn [disjoint_from cells_size csize Nat.add Z.of_nat]. unfold USTACK_TOP. lia.
           ++ apply (rw_cells_transport ctasegs _ m m2 _ _ FR2 MUa WMa). cbn [disjoint_from cells_size csize Nat.add Z.of_nat]. unfold USTACK_TOP. lia.
           ++ apply (rw_cells_transport ctasegs _ m m2 _ _ FR3 MUa WMa). cbn [disjoint_from cells_size csize Nat.add Z.of_nat]. unfold USTACK_TOP. lia.
        -- apply (qcache_rep_frame _ m m2 C rest QR MUb WMa).
           ++ exact (ip_stack_av Σk c ic n C lo HG Hc Hic HLk ltac:(lia) ltac:(lia) C 32 ltac:(lia) ltac:(lia)).
           ++ apply Forall_forall. intros (b', ents') Hin.
              destruct (dl_batch_of_in Σk _ b' ents' HWP (or_intror Hin)) as (j' & Hj' & Eb'). cbn [fst]. rewrite Eb'. exact (HBAV j' Hj').
      * apply (qbatch_frame _ m m2 b (qfirst rest) ents QB MUb WMa). rewrite Eb. exact (HBAV ib Hib).
    + split; [exact HWP'|]. split.
      * pose proof (recp_fields Σk c ic) as (X1 & X2 & _ & _ & _ & X6 & _ & _ & _ & _ & _ & X12 & X13 & X14).
        split; [rewrite X1; exact El|]. split; [rewrite X13; exact Elv|]. split; [rewrite X14; exact Efr|].
        split; [rewrite X12; exact Ecr|]. split; [rewrite X6; exact Eql | rewrite X2; exact Einit].
      * rewrite recp_st. destruct (Z.eqb_spec 24 c) as [E24|N24]; cbn [andb]; [|exact Hib].
        destruct (Nat.eqb_spec ic ib) as [<-|X]; [| exact Hib]. rewrite <- E24 in Hic. rewrite Hic in Hib. discriminate.
Qed.

End ItemP.
