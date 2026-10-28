(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Mem Frame Cells Step Arr Exec RzCPS MState. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface D_defs D_kit R_cache_defs R_prim_defs R_glue_defs R_thread R_m2s R_poison R_leaves R_setshadow R_depot_defs R_unwind_defs R_asan_defs R_allocate1 R_allocate2 R_allocate3 R_asan_malloc R_comballoc R_refill R_comballoc2 RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_facts RT_icfacts RT_malstate RT_maltail RT_freelift RT_geo0 RT_fkit RT_freestate RT_freeA RT_malart RT_malcore_stmt RT_malcore_p RT_refillstmt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Ltac pieceW W Hx k := let Hy := fresh "Hy" in intros Hy;
  eapply (not_outside W _ _ _ (nth_error_In W k eq_refl)); [|exact Hx]; cbn [fst snd]; unfold cstat_alloc, pc_addr in *; lia.
Ltac pieceWr W Hx k := let Hy := fresh "Hy" in intros Hy;
  eapply (not_outside W _ _ _ (nth_error_In W k eq_refl)); [|exact Hx]; cbn [fst snd lay refillΣ]; unfold cstat_alloc, pc_addr in *; lia.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Post.
Variables (Σ0 Σ : rtsA) (PMc : Model -> Prop) (mX0 mX : mem) (B : Z)
          (gp s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A : word) (n lo : Z) (tr : list Z).
Hypothesis MST : mat_stable PMc.
Hypothesis Hn : 1 <= n <= 64512.
Hypothesis Hlive : live_room (live Σ) n.   (* [comment removed for export] *)
Hypothesis Hcr : mcost n <= credit Σ.
Hypothesis HA : ART_A Σ mX.
Hypothesis LOW : l_ACEIL (lay Σ) <= lo.
Hypothesis LOR : lo + 0x1000 <= B + -144.
Hypothesis SPT : B + 16 <= USTACK_TOP.
Hypothesis SPA : B mod 16 = 0.
Hypothesis Htr : In tr T_MAIN.
Hypothesis Htrl : (1 <= length tr <= TR_MAX)%nat.
Hypothesis Hca : ca Σ (ClassID (needed2 n)) <> [].
Hypothesis E_live : live Σ = live Σ0.
Hypothesis E_frames : frames Σ = frames Σ0.
Hypothesis E_lay : lay Σ = lay Σ0.
Hypothesis E_credit : credit Σ = credit Σ0.
Hypothesis PRES0 : rt_pres (live Σ0) (frames Σ0) (B + -16) mX0 mX.
Hypothesis WM0 : wmono ctasegs mX0 mX.
#[local] Notation L := (lay Σ).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation SB := (l_SB (lay Σ)).
#[local] Notation DNB := (l_DNB (lay Σ)).
#[local] Notation SSB := (l_SSB (lay Σ)).
#[local] Notation c := (ClassID (needed2 n)).
#[local] Notation i := (Z.to_nat (last (ca Σ (ClassID (needed2 n))) 0)).
#[local] Notation AB := (p_abeg (l_SB (lay Σ)) (ClassID (needed2 n)) (Z.to_nat (last (ca Σ (ClassID (needed2 n))) 0))).
#[local] Notation S := (ClassSize (ClassID (needed2 n))).
#[local] Notation D' := (fst (depot_put (dep Σ) tr)).

Theorem post_of_tail : forall c1,
  AST SEGTOP_A (rtA_allow Σ) (tail_post Σ mX B gp s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A n lo tr)
      (fun mo => ARTM RTA Σ mo /\ PMc mo) c1 ->
  core_post Σ0 PMc B gp s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A n lo mX0 c1.
Proof using MST Hn Hlive Hcr HA LOW LOR SPT SPA Htr Htrl Hca E_live E_frames E_lay E_credit PRES0 WM0.
  intros c1 Hc1.
  pose proof (tl_cls n Hn) as (K1 & K2 & K3 & K4 & K5 & _). pose proof (tl_fp n Hn) as FP.
  assert (K7 : c = ClassID (needed n)) by (unfold needed2; rewrite FP; rewrite Z.add_0_r; reflexivity).
  pose proof (tl_geo Σ mX B n lo HA Hn Hca LOW LOR SPT SPA)
    as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21).
  pose proof (tl_dep Σ mX tr HA Htrl) as (OK & DI & OK' & DN2 & DT).
  pose proof (tl_shadows Σ mX B n lo HA Hn Hca LOW LOR SPT SPA) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8).
  pose proof (tl_room n Hn) as (R1 & R2 & R3 & R4 & R5).
  pose proof (rz_size_mod16 n) as RZ16. pose proof (rz_size_range n) as RZR.
  assert (HDinv : dep_inv D') by (apply dep_inv_put; [exact DI | exact Htr | lia]).
  assert (WF : rt_wf (mal_hit Σ c n D'))
    by exact (mal_hit_wf Σ mX c n D' HA ltac:(lia) Hca ltac:(lia) K3 K7 Hlive Hcr OK' HDinv).
  assert (Hsp' : l_ACEIL L <= B + -16) by lia.
  assert (Husp' : B + -16 <= USTACK_TOP) by lia.
  exists (mal_hit Σ c n D'), (p_ubeg SB c i n). split.
  - unfold ASTA. change (rt_allow RTA (mal_hit Σ c n D')) with (rtA_allow Σ).
    eapply AST_conseq; [exact Hc1 | |].
    + intros ms (m' & RS' & MU & WM & MI' & ST' & TF). exists m'. split; [exact RS'|].
      destruct TF as (HD & HL & US & RZ1 & RZ2 & DR & PC).
      assert (MU' : munch (W_mal T c DNB SSB AB S (l_ACEIL L) (B + -16)) mX m').
      { eapply (munch_weaken _ _ mX m'); [|exact MU]. intros x Hx. unfold W_tail. cbn [outside].
        split; [pieceW (W_mal T c DNB SSB AB S (l_ACEIL L) (B + -16)) Hx 0%nat|].
        split; [pieceW (W_mal T c DNB SSB AB S (l_ACEIL L) (B + -16)) Hx 1%nat|].
        split; [pieceW (W_mal T c DNB SSB AB S (l_ACEIL L) (B + -16)) Hx 7%nat|].
        split; [pieceW (W_mal T c DNB SSB AB S (l_ACEIL L) (B + -16)) Hx 5%nat|].
        split; [pieceW (W_mal T c DNB SSB AB S (l_ACEIL L) (B + -16)) Hx 6%nat|].
        split; [pieceW (W_mal T c DNB SSB AB S (l_ACEIL L) (B + -16)) Hx 2%nat|].
        split; [pieceW (W_mal T c DNB SSB AB S (l_ACEIL L) (B + -16)) Hx 2%nat|].
        split; [pieceW (W_mal T c DNB SSB AB S (l_ACEIL L) (B + -16)) Hx 3%nat|].
        split; [pieceW (W_mal T c DNB SSB AB S (l_ACEIL L) (B + -16)) Hx 2%nat|].
        split; [pieceW (W_mal T c DNB SSB AB S (l_ACEIL L) (B + -16)) Hx 2%nat|].
        split; [pieceW (W_mal T c DNB SSB AB S (l_ACEIL L) (B + -16)) Hx 4%nat | exact I]. }
      assert (SH1 : bytes_at ctasegs m' (shad AB) (farun (rz_size n / 8) ++ ushadow n)).
      { apply bytes_at_app. split; [exact RZ1|]. rewrite farun_lenZ by (apply Z.div_pos; lia). rewrite <- Q1. exact US. }
      pose proof (mal_ART Σ mX c n (B + -16) HA ltac:(lia) Hca ltac:(lia) K3 Hsp' Husp' m' D' MU' WM HD HL SH1 RZ2 PC DR
                    (mc_hash1 (dep Σ) tr DI) WF) as ART'.
      split; [exact ART'|]. split; [exact MI'|]. split; [exact (wmono_trans ctasegs _ _ _ WM0 WM)|]. split; [exact ST'|]. split.
      { intros a Ha. rewrite (MU' a (ma_client Σ mX c n (B + -16) HA ltac:(lia) Hca ltac:(lia) K3 Hsp' Husp' (bv_unsigned a)
                                       ltac:(rewrite E_live, E_frames; exact Ha))).
        exact (PRES0 a Ha). }
      pose proof (tl_chunk_stk Σ mX n HA Hn Hca m' WM) as CH.
      split.
      { unfold p_ubeg. destruct (stk_split ctasegs m' AB (AB + rz_size n) (AB + S) CH ltac:(lia)) as [_ X].
        destruct (stk_split ctasegs m' (AB + rz_size n) (AB + rz_size n + n) (AB + S) X ltac:(lia)) as [X2 _].
        exact (stk_wr_at' m' _ _ X2). }
      unfold p_ubeg. apply acc_ushadow; [|unfold K_HIGH_SHADOW_hi in *; lia|lia|exact US].
      rewrite Z.add_mod by lia. rewrite (mod8_of AB 16 ltac:(lia) G3 ltac:(exists 2; reflexivity)).
      rewrite (mod8_of (rz_size n) 16 ltac:(lia) RZ16 ltac:(exists 2; reflexivity)). reflexivity.
    + intros mo (HM & HP). split; [|exact HP]. cbn [ARTM RTA] in *. unfold ARTM_A in *. rewrite mal_hit_eager. exact HM.
  - cbn [rt_live rt_frames rt_sp0 rt_credit RTA]. unfold rtA_live, rtA_frames, rtA_sp0, rtA_credit, mal_hit.
    cbn [live frames lay credit].
    split; [rewrite E_live; reflexivity|]. split; [rewrite E_frames; reflexivity|]. split; [rewrite E_lay; reflexivity|].
    split; [rewrite E_credit; reflexivity|].
    unfold p_ubeg. split; [unfold K_HIGH_SHADOW_hi in *; lia|]. split.
    + rewrite Z.add_mod by lia. rewrite G3, RZ16. reflexivity.
    + unfold USTACK_TOP, rb, kUserCap in *. lia.
Qed.

End Post.

(* [comment removed for export] *)
Lemma aclient_split : forall Σ m sp x, ART_A Σ m -> aclient (live Σ) (frames Σ) sp x -> sp <= x \/ x < l_ACEIL (lay Σ).
Proof.
  intros Σ m sp x HA Hx. pose proof (rta_sp0_win Σ m HA) as SW. unfold l_ACEIL, rtA_sp0, STACK_WIN in *.
  destruct Hx as [H|[H|[H|[H|H]]]].
  - left; lia.
  - right. destruct H as ((lo & hi & Hin & Hlh) & _). unfold CLIENT_STATIC in Hin.
    destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; lia.
  - right. destruct H as (p & n & Hin & Hpx). pose proof (rta_live_range Σ m p n HA Hin) as (_ & X & _). unfold rtA_sp0, STACK_WIN in X. lia.
  - right. destruct H as (f & k & Hin & Hfx). destruct (sep_frame Σ m HA f k Hin) as (Y1 & Y2 & Y3).
    pose proof (geo_grant Σ m HA (l_FSB (lay Σ)) 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)) as (_ & _ & G3 & _).
    unfold l_ACEIL, STACK_WIN in G3. lia.
  - right. destruct H as (f & k & Hin & Hfx). destruct (sep_fshad Σ m HA f k Hin) as (_ & Y). unfold K_HIGH_SHADOW_hi in Y. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section CoreMiss.
Variables (Σ : rtsA) (PMc : Model -> Prop) (mX : mem) (B : Z)
          (gp s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word)
          (F : bvmap 5 word) (fc : bv 32) (n lo : Z) (tr : list Z) (tb : list word) (j0 : list byte).
Hypothesis RF : refill_stmt.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Hypothesis Hn : 1 <= n <= 64512.
Hypothesis Hlive : live_room (live Σ) n.   (* [comment removed for export] *)
Hypothesis Hcr : mcost n <= credit Σ.
Hypothesis HA : ART_A Σ mX.
Hypothesis MI : mem_inv ctasegs mX.
Hypothesis ST : stk ctasegs mX lo (B + -144).
Hypothesis LOW : l_ACEIL (lay Σ) <= lo.
Hypothesis LOR : lo + 0x1000 <= B + -144.
Hypothesis SPT : B + 16 <= USTACK_TOP.
Hypothesis SPT2 : B + 2144 <= USTACK_TOP.
Hypothesis SPA : B mod 16 = 0.
Hypothesis Htr : In tr T_MAIN.
Hypothesis Htrl : (1 <= length tr <= TR_MAX)%nat.
Hypothesis TRC : trc_cells B tr mX tb.
Hypothesis AFC : af_cells B s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A mX j0.
Hypothesis Hca0 : ca Σ (ClassID (needed2 n)) = [].
#[local] Notation L := (lay Σ).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation SB := (l_SB (lay Σ)).
#[local] Notation c := (ClassID (needed2 n)).
#[local] Notation P := (pc_addr (l_T (lay Σ)) (ClassID (needed2 n))).
#[local] Notation Σr := (refillΣ Σ (ClassID (needed2 n))).

(* [comment removed for export] *)
Lemma cm_cls : 1 <= c <= 30 /\ 1 <= needed2 n <= 65536.
Proof using Hn.
  clear - Hn. pose proof (tl_cls n Hn) as (K1 & _ & _ & _ & _ & K6 & _). pose proof (tl_fp n Hn) as FP.
  assert (E : needed2 n = needed n) by (unfold needed2; rewrite FP; lia). unfold from_primary in FP. apply Z.leb_le in FP.
  split; [exact K1 | lia].
Qed.

(* [comment removed for export] *)
Lemma cm_ca : ca Σr c <> [] /\ Z.of_nat (length (ca Σr c)) = MaxCount c / 2 /\ ca_init Σr = true.
Proof using HA Hn.
  clear - HA Hn. pose proof cm_cls as (K1 & _). pose proof (refillΣ_facts Σ c) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CI & _ & CA & _).
  pose proof (ART_wf Σ mX HA) as (_ & HR & _). destruct HR as (HR & _).
  pose proof (refill_ca_len (pr Σ c) c K1 (HR c ltac:(lia))) as LEN. pose proof (MaxCount_range c ltac:(lia)) as (M1 & M2).
  assert (M3 : 1 <= MaxCount c / 2) by (apply Z.div_le_lower_bound; lia).
  rewrite CA. split; [intros E; rewrite E in LEN; cbn in LEN; lia|]. split; [exact LEN | exact CI].
Qed.

(* [comment removed for export] *)
Lemma cm_evtA : exists mc cs, evt ctasegs (comballoc_miss_A_post (Z_to_bv 64 0x19bfbc) (Z_to_bv 64 (B + -144)) gp (Z_to_bv 64 tpA)
      (Z_to_bv 64 (Z.b2z (from_primary n))) (Z_to_bv 64 n) (Z_to_bv 64 8) (Z_to_bv 64 (needed2 n)) (Z_to_bv 64 (rz_size n))
      (Z_to_bv 64 n) (Z_to_bv 64 INST) (Z_to_bv 64 B) (Z_to_bv 64 (0 + - (8))) (Z_to_bv 64 7) (Z_to_bv 64 T) (Z_to_bv 64 1) F fc T c P lo mX
      (fun m' => pc_cells m' P 0 mc cs))
    (core_entry Σ B gp t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F fc n mX).
Proof.
  pose proof cm_cls as (K1 & K6).
  pose proof (ART_cache Σ mX HA c ltac:(lia)) as X. unfold pclass_rep in X. rewrite Hca0 in X. cbn [length Z.of_nat] in X.
  destruct X as (PC & _).
  exists (if ca_init Σ then MaxCount c else 0), (if ca_init Σ then ClassSize c else 0).
  assert (GT4 : T_ok (l_ACEIL L) T).
  { pose proof (geo_grant Σ mX HA T 4096 ltac:(unfold startup_grants; do 2 right; left; reflexivity)) as (T1 & T2 & T3 & _ & T5).
    unfold T_ok, img_hull_lo, img_hull_hi. unfold SEGTOP_A in T5. split; [lia|]. split; [exact T2|]. split; [exact T3|].
    split; [unfold USTACK_TOP in SPT; lia | exact T5]. }
  assert (RS : 0 <= B + -144 < 2 ^ 64) by (pose proof (rta_sp0_win Σ mX HA); unfold l_ACEIL, rtA_sp0, STACK_WIN, USTACK_TOP in *; lia).
  unfold core_entry.
  apply (comballoc_miss_A_spec (Z_to_bv 64 0x19bfbc) (Z_to_bv 64 (B + -144)) gp (Z_to_bv 64 tpA) t0 t1 t2
           (Z_to_bv 64 (Z.b2z (from_primary n))) (Z_to_bv 64 n) a4 a5 a6 a7 (Z_to_bv 64 8) (Z_to_bv 64 (needed2 n))
           (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n) (Z_to_bv 64 INST) (Z_to_bv 64 B) (Z_to_bv 64 (0 + - (8))) (Z_to_bv 64 7)
           (Z_to_bv 64 T) (Z_to_bv 64 1) t3 t4 t5 t6 F fc mX (l_ACEIL L) T (needed2 n) _ _ lo).
  all: rewrite ?unsigned_lit by exact RS.
  1: exact K6. 1: exact PC.
  1: destruct (ca_init Σ); [pose proof (MaxCount_range c ltac:(lia)); lia | lia].
  1: destruct (ca_init Σ); [pose proof (ClassSize_range c ltac:(lia)); lia | lia].
  1: exact GT4. 1: exact ST. 1: exact LOW.
  1: pose proof (rta_sp0_win Σ mX HA); unfold kHighShadowEnd, l_ACEIL, rtA_sp0, STACK_WIN in *; lia.
  1: lia. 1: unfold USTACK_TOP in SPT; lia. 1: exact MI.
Qed.

(* [comment removed for export] *)
Lemma cm_evtB : forall (m2 : mem) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32),
  ART_A Σr m2 -> mem_inv ctasegs m2 -> stk ctasegs m2 lo (B + -192) ->
  rw_cells ctasegs m2 (B + -192) [C8 (Z_to_bv 64 (rz_size n)); C8 (Z_to_bv 64 (needed2 n)); C8 (Z_to_bv 64 8); C8 (Z_to_bv 64 n);
                                C8 (Z_to_bv 64 (Z.b2z (from_primary n))); C8 (Z_to_bv 64 0x19bfbc)] ->
  af_cells B s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A m2 j0 -> trc_cells B tr m2 tb ->
  evt ctasegs (tail_post Σr m2 B gp s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A n lo tr)
    (MS (mkR (Z_to_bv 64 comballoc_retR) (Z_to_bv 64 (B + -192)) gp (Z_to_bv 64 tpA) t0' t1' t2' (Z_to_bv 64 c) (Z_to_bv 64 P)
             (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 8) (Z_to_bv 64 (cacheT T)) (Z_to_bv 64 INST) (Z_to_bv 64 n)
             (Z_to_bv 64 INST) (Z_to_bv 64 B) (Z_to_bv 64 (0 + - (8))) (Z_to_bv 64 7) (Z_to_bv 64 T) (Z_to_bv 64 1) t3' t4' t5' t6')
        F' (ret_pc (Z_to_bv 64 comballoc_retR)) fc' None m2 (seg_rom ctasegs)).
Proof.
  intros m2 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' HA2 MI2 ST2 FR2 AF2 TR2.
  pose proof cm_ca as (Hca & Hlen & Hinit).
  pose proof (tl_cls n Hn) as (K1 & K2 & K3 & K4 & K5 & _). pose proof (tl_fp n Hn) as FP.
  assert (K6 : 1 <= needed2 n <= 65536) by exact (proj2 cm_cls).
  pose proof (tl_entry Σr m2 n HA2 Hn Hca) as (E1 & E2 & _).
  assert (LOWr : l_ACEIL (lay Σr) <= lo) by exact LOW.
  pose proof (tl_geo Σr m2 B n lo HA2 Hn Hca LOWr LOR SPT SPA)
    as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21).
  pose proof (tl_apart Σr m2 HA2) as (A02 & A03 & A06 & A07 & A23 & A26 & A27 & A36 & A37 & A67 & TS & XS & TP & XP & DS & BS).
  pose proof (geo_prb Σr m2 HA2) as (P1 & P2 & P3).
  change (lay (refillΣ Σ (ClassID (needed2 n)))) with (lay Σ) in *.
  assert (E6 : 0 <= last (ca Σr c) 0 * ClassSize c < 2 ^ 32).
  { pose proof (ART_wf Σr m2 HA2) as (_ & HR & _). destruct HR as (HR & _).
    pose proof (HR c ltac:(lia)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & W11).
    split; [apply Z.mul_nonneg_nonneg; lia|].
    assert (last (ca Σr c) 0 * ClassSize c + ClassSize c <= ClassSize c * Z.of_nat (length (r_st (pr Σr c)))).
    { replace (ClassSize c * Z.of_nat (length (r_st (pr Σr c)))) with (Z.of_nat (length (r_st (pr Σr c))) * ClassSize c) by ring.
      replace (last (ca Σr c) 0 * ClassSize c + ClassSize c) with ((last (ca Σr c) 0 + 1) * ClassSize c) by ring.
      apply Z.mul_le_mono_nonneg_r; lia. }
    lia. }
  pose proof (ART_cache Σr m2 HA2 c ltac:(lia)) as X. unfold pclass_rep in X. rewrite Hinit in X.
  replace (if true then MaxCount c else 0) with (MaxCount c) in X by reflexivity.
  replace (if true then ClassSize c else 0) with (ClassSize c) in X by reflexivity.
  destruct X as (PC & chs & CH1 & CH2 & CH3).
  pose proof (ART_consts Σr m2 HA2) as ((SBC0 & _) & _ & _ & _ & _ & _ & _ & ICR).
  destruct ICR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & St & _).
  assert (SBC : rw_cells ctasegs m2 i_spacebeg [C8 (Z_to_bv 64 SB)]) by exact (rw_cells_app_l m2 _ [C8 (Z_to_bv 64 SB)] _ SBC0).
  assert (STJx : exists v, rw_cells ctasegs m2 (cstat_alloc T) [C8 v]).
  { unfold cstat_alloc. destruct (stk_split ctasegs m2 (T + 2768) (T + 2784) (T + 3168) St ltac:(lia)) as [_ Y].
    destruct (stk_split ctasegs m2 (T + 2784) (T + 2784 + 8) (T + 3168) Y ltac:(lia)) as [Y8 _].
    destruct (stk_CB m2 (T + 2784) 8 Y8 ltac:(lia)) as (bs & Hb). destruct (word_of_stk m2 (T + 2784) (T + 2784 + 8) (T + 2784) Y8 ltac:(lia) ltac:(lia)) as (v & Hv).
    exists v. split; [exact Hv | exact (proj2 Hb)]. }
  destruct STJx as (stj & STJ).
  assert (HT : T_ok (l_ACEIL L) T).
  { unfold T_ok, img_hull_lo, img_hull_hi. unfold SEGTOP_A in TP. split; [lia|]. split; [exact G9|]. split; [lia|]. split; [lia | exact TP]. }
  assert (HSB : SB_ok (l_ACEIL L) SB).
  { unfold SB_ok, kHighShadowEnd. unfold K_HIGH_SHADOW_hi in G7. split; [lia|]. split; [exact P3|]. split; [lia | lia]. }
  assert (RS : 0 <= B + -144 < 2 ^ 64) by (unfold USTACK_TOP in SPT; lia).
  rewrite (ret_pc_even comballoc_retR) by (unfold comballoc_retR; lia || reflexivity).
  replace (B + -192) with (bv_unsigned (Z_to_bv 64 (B + -144)) - 48) by (rewrite unsigned_lit by exact RS; lia).
  eapply evt_cut.
  { apply (comballoc_miss_B_spec (Z_to_bv 64 (B + -144)) gp (Z_to_bv 64 tpA) t0' t1' t2' (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7'
             (Z_to_bv 64 n) (Z_to_bv 64 INST) (Z_to_bv 64 B) (Z_to_bv 64 (0 + - (8))) (Z_to_bv 64 7) (Z_to_bv 64 T) (Z_to_bv 64 1)
             t3' t4' t5' t6' F' fc' m2 (Z_to_bv 64 (Z.b2z (from_primary n))) (Z_to_bv 64 n) (Z_to_bv 64 8) (Z_to_bv 64 (needed2 n))
             (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 0x19bfbc) (l_ACEIL L) T SB c (Z.of_nat (length (ca Σr c))) (MaxCount c) (ClassSize c) lo
             chs (cpw c (last (ca Σr c) 0)) stj).
    all: rewrite ?unsigned_lit by exact RS.
    1: exact K1. 1: rewrite unsigned_lit by lia; lia. 1: exact SBC. 1: exact PC.
    1: assert (1 <= MaxCount c / 2 <= 8) by (pose proof (MaxCount_range c ltac:(lia)); split; [apply Z.div_le_lower_bound | apply Z.div_le_upper_bound]; lia); lia.
    1: pose proof (MaxCount_range c ltac:(lia)); lia.
    1: pose proof (ClassSize_range c ltac:(lia)); lia.
    1: exact CH1. 1: exact CH2.
    1: replace (Z.to_nat (Z.of_nat (length (ca Σr c)) - 1)) with (length (ca Σr c) - 1)%nat by lia; exact (hit_w (cpw c) (ca Σr c) chs Hca CH3).
    1: exact STJ. 1: exact HT. 1: exact HSB.
    1: replace (B + -144 - 48) with (B + -192) by lia; exact FR2.
    1: replace (B + -144 - 48) with (B + -192) by lia; exact ST2.
    1: exact LOW.
    1: unfold kHighShadowEnd, SHB in *; lia.
    1: lia. 1: unfold USTACK_TOP in SPT; lia. 1: exact MI2. }
  intros ms (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m3 & stj' & -> & MU3 & WM3 & MI3 & PC3 & ARR3 & STA3 & SBC3 & ST3).
  rewrite unsigned_lit in MU3, ST3 by exact RS.
  rewrite (ret_pc_even 0x19bfbc) by (lia || reflexivity).
  rewrite (hit_addr SB c (last (ca Σr c) 0) ltac:(lia) E6 ltac:(clear - K5; apply Z.mod_divide in K5; [|lia]; apply Z.mod_divide; [lia|]; destruct K5 as [q Hq]; exists (2 * q); lia)).
  apply (tl_p2a Σr m2 B gp s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A F' fc' n lo tr HA2 Hn Hca LOWr LOR SPT SPA Htr Htrl
           m3 t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' tb j0).
  - eapply (munch_weaken _ _ m2 m3); [|exact MU3]. intros x Hx. cbn [outside].
    split; [pieceWr (W_tail Σr B n) Hx 0%nat|]. split; [pieceWr (W_tail Σr B n) Hx 1%nat|]. split; [pieceWr (W_tail Σr B n) Hx 2%nat | exact I].
  - exact WM3.
  - exact MI3.
  - exact ST3.
  - apply (af_transport B s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A tr Htrl _ m2 m3 j0 AF2 MU3 WM3).
    cbn [disjoint_from]. unfold cstat_alloc, pc_addr. split; [lia|]. split; [lia|]. split; [lia | exact I].
  - destruct TR2 as (T1 & T2 & T3). split; [|split; [|exact T3]].
    + apply (rw_cells_transport ctasegs _ m2 m3 _ _ T1 MU3 WM3). cbn [cells_size csize Nat.add disjoint_from]. unfold cstat_alloc, pc_addr.
      split; [lia|]. split; [lia|]. split; [lia | exact I].
    + apply (u64arr_transport ctasegs _ m2 m3 _ _ T2 MU3 WM3). cbn [disjoint_from]. unfold cstat_alloc, pc_addr.
      split; [lia|]. split; [lia|]. split; [lia | exact I].
  - pose proof (ART_chunk Σr m2 HA2) as (Pch & _). destruct (Pch c _ CkIdle ltac:(lia) E2) as (_ & SH). unfold pshadow_idle in SH.
    apply (bytes_at_transport ctasegs _ m2 m3 _ _ SH MU3). unfold farun. rewrite repeat_length, Z2Nat.id by (apply Z.div_pos; lia).
    pose proof (tl_shad Σr m2 B n lo HA2 Hn Hca LOWr LOR SPT SPA) as (S1 & S2 & S3).
    cbn [disjoint_from]. unfold cstat_alloc, pc_addr. change (lay (refillΣ Σ (ClassID (needed2 n)))) with (lay Σ) in *.
    unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *.
    split; [clear - S1 S2 S3 TS G8 G10 K1; destruct TS; lia|]. split; [clear - S1 S2 S3 TS G8 G10; destruct TS; lia|].
    split; [clear - S2 S3 G17 G18 G19; lia | exact I].
  - pose proof (tl_dep Σr m2 tr HA2 Htrl) as (OK & _).
    apply (depot_rep_frame _ _ _ _ _ _ m2 m3 (ART_dep Σr m2 HA2) OK MU3 WM3); cbn [disjoint_from]; unfold cstat_alloc, pc_addr;
      change (lay (refillΣ Σ (ClassID (needed2 n)))) with (lay Σ) in *; unfold apart, SEGTOP_A, SHB in *.
    + split; [clear - TP G8 K1; destruct TP; lia|]. split; [clear - TP G8; destruct TP; lia|]. split; [clear - G17 G18 G19; lia | exact I].
    + split; [clear - TP G8 K1; destruct TP; lia|]. split; [clear - TP G8; destruct TP; lia|]. split; [clear - G17 G18 G19; lia | exact I].
    + split; [clear - A26 K1; destruct A26; lia|]. split; [clear - A26; destruct A26; lia|]. split; [clear - G14 G18 G19; lia | exact I].
    + split; [clear - TP G8 K1; destruct TP; lia|]. split; [clear - TP G8; destruct TP; lia|]. split; [clear - G17 G18 G19; lia | exact I].
    + split; [clear - TP G8 K1; destruct TP; lia|]. split; [clear - TP G8; destruct TP; lia|]. split; [clear - G17 G18 G19; lia | exact I].
    + split; [clear - A27 K1; destruct A27; lia|]. split; [clear - A27; destruct A27; lia|]. split; [clear - G16 G18 G19; lia | exact I].
  - exact PC3.
Qed.

(* [comment removed for export] *)
Theorem cm_core : cps ctasegs (ASTA RTA Σ PMc (eq (core_entry Σ B gp t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F fc n mX)))
                            (core_post Σ PMc B gp s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A n lo mX).
Proof using RF FDO MST Hn Hlive Hcr HA MI ST LOW LOR SPT SPT2 SPA Htr Htrl TRC AFC Hca0.
  intros TT cf Hc Hk.
  pose proof cm_cls as (K1 & K6).
  destruct cm_evtA as (mc & cs & W1).
  assert (W1' : forall ms, eq (core_entry Σ B gp t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F fc n mX) ms -> evt ctasegs _ ms) by (intros ms <-; exact W1).
  apply (cps_realizes ctasegs _ _ _ cf (ast_evt ctasegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (fl_ASTA_mat_stable Σ PMc MST) W1') Hc).
  intros c1 Hc1. unfold comballoc_miss_A_post in Hc1.
  apply AST_exI in Hc1 as (t0' & Hc1). apply AST_exI in Hc1 as (t1' & Hc1). apply AST_exI in Hc1 as (t2' & Hc1).
  apply AST_exI in Hc1 as (a4' & Hc1). apply AST_exI in Hc1 as (a5' & Hc1). apply AST_exI in Hc1 as (a6' & Hc1).
  apply AST_exI in Hc1 as (a7' & Hc1). apply AST_exI in Hc1 as (t3' & Hc1). apply AST_exI in Hc1 as (t4' & Hc1).
  apply AST_exI in Hc1 as (t5' & Hc1). apply AST_exI in Hc1 as (t6' & Hc1). apply AST_exI in Hc1 as (m1 & Hc1).
  destruct Hc1 as (HM & HPm & HPM & HZ). destruct HPm as (Hms & MU1 & WM1 & MI1 & FR1 & ST1 & _).
  assert (RS : 0 <= B + -144 < 2 ^ 64) by (pose proof (rta_sp0_win Σ mX HA); unfold l_ACEIL, rtA_sp0, STACK_WIN, USTACK_TOP in *; lia).
  assert (RS2 : 0 <= B + -192 < 2 ^ 64) by (pose proof (rta_sp0_win Σ mX HA); unfold l_ACEIL, rtA_sp0, STACK_WIN, USTACK_TOP in *; lia).
  rewrite unsigned_lit in MU1, FR1, ST1, Hms by exact RS.
  replace (B + -144 - 48) with (B + -192) in MU1, FR1, ST1, Hms by lia.
  (* [comment removed for export] *)
  assert (Hsp1 : rtA_sp0 Σ - STACK_WIN <= B + -192) by (unfold l_ACEIL in LOW; unfold rtA_sp0; lia).
  assert (MUC : munch (W_client Σ (B + -192)) mX m1).
  { eapply (munch_weaken _ _ mX m1); [|exact MU1]. intros x Hx. unfold W_client in Hx. cbn [app outside] in Hx |- *.
    destruct Hx as (X1 & _). split; [lia | exact I]. }
  pose proof (ART_transport _ Σ mX m1 HA MUC WM1 (art_avoid_client Σ mX (B + -192) HA Hsp1)) as ART1.
  (* [comment removed for export] *)
  assert (Hc2 : ASTA RTA Σ PMc (eq (refill_entry_st (Z_to_bv 64 comballoc_retR) (Z_to_bv 64 (B + -192)) gp t0' t1' t2' (Z_to_bv 64 c)
                                     (Z_to_bv 64 P) a4' a5' a6' a7' (Z_to_bv 64 8) (Z_to_bv 64 (cacheT T)) (Z_to_bv 64 INST) (Z_to_bv 64 n)
                                     (Z_to_bv 64 INST) (Z_to_bv 64 B) (Z_to_bv 64 (0 + - (8))) (Z_to_bv 64 7) (Z_to_bv 64 T) (Z_to_bv 64 1)
                                     t3' t4' t5' t6' F fc T c m1)) c1).
  { split; [exact HM|]. split; [|split; [exact HPM | exact HZ]]. rewrite Hms. reflexivity. }
  apply (RF Σ PMc (Z_to_bv 64 comballoc_retR) (Z_to_bv 64 (B + -192)) gp t0' t1' t2' (Z_to_bv 64 c) (Z_to_bv 64 P) a4' a5' a6' a7'
           (Z_to_bv 64 8) (Z_to_bv 64 (cacheT T)) (Z_to_bv 64 INST) (Z_to_bv 64 n) (Z_to_bv 64 INST) (Z_to_bv 64 B) (Z_to_bv 64 (0 + - (8)))
           (Z_to_bv 64 7) (Z_to_bv 64 T) (Z_to_bv 64 1) t3' t4' t5' t6' F fc m1 c lo FDO MST K1 Hca0 ART1 MI1
           ltac:(rewrite unsigned_lit by exact RS2; exact ST1) LOW ltac:(rewrite unsigned_lit by exact RS2; lia)
           ltac:(rewrite unsigned_lit by exact RS2; unfold USTACK_TOP in SPT; lia)
           TT c1 Hc2).
  intros c2 Hc3.
  apply AST_exI in Hc3 as (m2 & Hc3).
  destruct Hc3 as (HM2 & HPm2 & HPM2 & HZ2). destruct HPm2 as (Hms2 & ART2 & MI2 & WM2 & ST2 & PR2).
  rewrite unsigned_lit in ST2, PR2 by exact RS2.
  destruct Hms2 as (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & F'' & fc'' & Hms2).
  pose proof (refillΣ_facts Σ c) as (E_lay & E_live & E_frames & E_credit & _).
  (* [comment removed for export] *)
  assert (AG : forall a k, B + -192 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m1 m2)
    by (intros a k H1 H2 x Hx; apply PR2; left; lia).
  assert (FR2 : rw_cells ctasegs m2 (B + -192) [C8 (Z_to_bv 64 (rz_size n)); C8 (Z_to_bv 64 (needed2 n)); C8 (Z_to_bv 64 8); C8 (Z_to_bv 64 n);
                                                C8 (Z_to_bv 64 (Z.b2z (from_primary n))); C8 (Z_to_bv 64 0x19bfbc)]).
  { apply (rw_cells_agree ctasegs m1 m2 _ _ FR1); [apply AG; cbn [cells_size csize Nat.add]; lia | exact WM2]. }
  assert (AF1 : af_cells B s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A m1 j0).
  { apply (af_transport B s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A tr Htrl _ mX m1 j0 AFC MU1 WM1).
    cbn [disjoint_from]. split; [lia | exact I]. }
  assert (AF2 : af_cells B s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A m2 j0).
  { destruct AF1 as (A1 & A2). unfold alloc_frame in *. split.
    - apply (rw_cells_agree ctasegs m1 m2 _ _ A1); [apply AG; cbn [cells_size csize Nat.add]; lia | exact WM2].
    - apply (rw_cells_agree ctasegs m1 m2 _ _ A2); [apply AG; cbn [cells_size csize Nat.add]; lia | exact WM2]. }
  assert (TR2 : trc_cells B tr m2 tb).
  { destruct TRC as (T1 & T2 & T3). split; [|split; [|exact T3]].
    - apply (rw_cells_agree ctasegs mX m2 _ _ T1); [|exact (wmono_trans ctasegs _ _ _ WM1 WM2)].
      intros x Hx. cbn [cells_size csize Nat.add] in Hx. rewrite (PR2 x ltac:(left; lia)). apply MU1. cbn [outside]. split; [lia | exact I].
    - apply (u64arr_agree ctasegs mX m2 _ _ T2); [|exact (wmono_trans ctasegs _ _ _ WM1 WM2)].
      intros x Hx. rewrite wr_trace_length in Hx by lia. rewrite (PR2 x ltac:(left; lia)). apply MU1. cbn [outside]. split; [lia | exact I]. }
  assert (Hc4 : ASTA RTA Σr PMc (eq (MS (mkR (Z_to_bv 64 comballoc_retR) (Z_to_bv 64 (B + -192)) gp (Z_to_bv 64 tpA) t0'' t1'' t2''
                 (Z_to_bv 64 c) (Z_to_bv 64 P) (Z_to_bv 64 1) a1'' a2'' a3'' a4'' a5'' a6'' a7'' (Z_to_bv 64 8) (Z_to_bv 64 (cacheT T))
                 (Z_to_bv 64 INST) (Z_to_bv 64 n) (Z_to_bv 64 INST) (Z_to_bv 64 B) (Z_to_bv 64 (0 + - (8))) (Z_to_bv 64 7) (Z_to_bv 64 T)
                 (Z_to_bv 64 1) t3'' t4'' t5'' t6'') F'' (ret_pc (Z_to_bv 64 comballoc_retR)) fc'' None m2 (seg_rom ctasegs))) c2).
  { split; [exact HM2|]. split; [|split; [exact HPM2 | exact HZ2]]. rewrite Hms2. reflexivity. }
  assert (W2 : forall ms, eq (MS (mkR (Z_to_bv 64 comballoc_retR) (Z_to_bv 64 (B + -192)) gp (Z_to_bv 64 tpA) t0'' t1'' t2''
                 (Z_to_bv 64 c) (Z_to_bv 64 P) (Z_to_bv 64 1) a1'' a2'' a3'' a4'' a5'' a6'' a7'' (Z_to_bv 64 8) (Z_to_bv 64 (cacheT T))
                 (Z_to_bv 64 INST) (Z_to_bv 64 n) (Z_to_bv 64 INST) (Z_to_bv 64 B) (Z_to_bv 64 (0 + - (8))) (Z_to_bv 64 7) (Z_to_bv 64 T)
                 (Z_to_bv 64 1) t3'' t4'' t5'' t6'') F'' (ret_pc (Z_to_bv 64 comballoc_retR)) fc'' None m2 (seg_rom ctasegs)) ms ->
               evt ctasegs (tail_post Σr m2 B gp s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A n lo tr) ms)
    by (intros ms <-; exact (cm_evtB m2 t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' F'' fc'' ART2 MI2 ST2 FR2 AF2 TR2)).
  apply (cps_realizes ctasegs _ _ _ c2 (ast_evt ctasegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σr) _ _ _ (fl_ASTA_mat_stable Σr PMc MST) W2) Hc4).
  intros c3 Hc5. apply Hk.
  pose proof cm_ca as (Hca & _ & _).
  assert (PRES0 : rt_pres (live Σ) (frames Σ) (B + -16) mX m2).
  { intros a Ha. rewrite (PR2 a ltac:(destruct Ha as [Ha|Ha]; [left; lia | right; exact Ha])).
    apply MU1. cbn [outside]. split; [|exact I]. intros Hr.
    destruct (aclient_split Σ mX (B + -16) (bv_unsigned a) HA Ha) as [X|X]; lia. }
  exact (post_of_tail Σ Σr PMc mX m2 B gp s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A n lo tr MST Hn
           ltac:(rewrite E_live; exact Hlive) ltac:(rewrite E_credit; exact Hcr) ART2 ltac:(rewrite E_lay; exact LOW) LOR SPT SPA Htr Htrl Hca
           E_live E_frames E_lay E_credit PRES0 (wmono_trans ctasegs _ _ _ WM1 WM2) c3 Hc5).
Qed.

End CoreMiss.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem core_prim : refill_stmt -> core_stmt_prim.
Proof.
  intros RF. unfold core_stmt_prim, core_case.
  intros Σ PMc mX B gp s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F fc n lo tr tb j0
    FDO MST HP Hn Hlen Hcr HA MI ST LOW LOR SPT SPA Htr Htrl TRC AFC.
  cbv beta in HP. assert (Hn' : 1 <= n <= 64512) by lia.
  destruct (ca Σ (ClassID (needed2 n))) eqn:E.
  - exact (cm_core Σ PMc mX B gp s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F fc n lo tr tb j0
             RF FDO MST Hn' Hlen Hcr HA MI ST LOW LOR ltac:(lia) SPT SPA Htr Htrl TRC AFC E).
  - exact (ch_core Σ PMc mX B gp s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F fc n lo tr tb j0
             FDO MST Hn' Hlen Hcr HA MI ST LOW LOR ltac:(lia) SPA Htr Htrl TRC AFC ltac:(rewrite E; discriminate)).
Qed.
