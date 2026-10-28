(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac MState Mem Frame Cells Step Exec ImageA RzCPS RegsEquiv StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2 RT_iface5. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs D_kit D_clx D_libiface D_auxv. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import TopA_iodefs. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_akit Sj_hkit Sj_num_akit Sj_acps. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_defsA Pj_defsA El_defsA El_frontA El_sitesA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import PropExec AxSymExec3.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import El_xs_core.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import El_xs_coreA El_xs_adaptA El_throwA El_xr_bbegin El_xr_bcast El_xr_bend El_throw_siteA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Import AX2.
Open Scope Z_scope.

Lemma el_unwA_bytes : forall m uw, rw_cells asegs m EL_UNW_A (uw_cellsA uw) ->
  bytes_at asegs m EL_UNW_XA (map (fun b => Z_to_bv 8 b) (uw_bytesA uw)) /\ wr_at asegs m EL_UNW_XA 8.
Proof.
  intros m uw [[_ B] W]. change EL_UNW_A with EL_UNW_XA in B, W. destruct uw; cbn -[bytes_at EL_UNW_XA Z_to_bv] in B; cbn [cells_size uw_cellsA csize repeat Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in W;
    (split; [exact B| exact W]).
Qed.
Lemma el_unwA_of_bytes : forall m, bytes_at asegs m EL_UNW_XA (map (fun b => Z_to_bv 8 b) (uw_bytesA true)) -> wr_at asegs m EL_UNW_XA 8 ->
  rw_cells asegs m EL_UNW_A (uw_cellsA true).
Proof.
  intros m B W. change EL_UNW_A with EL_UNW_XA. split; [split; [cbn; repeat split; reflexivity|]|].
  - cbn -[bytes_at EL_UNW_XA Z_to_bv]. cbn -[bytes_at EL_UNW_XA Z_to_bv] in B. exact B.
  - cbn [cells_size uw_cellsA csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. exact W.
Qed.
Lemma el_libA_after : forall m m', el_libA m ->
  agree_on (fun x => el_lib_rng x /\ ~ (EL_EHG_A <= x < EL_EHG_A + 12) /\ ~ (EL_UNW_A <= x < EL_UNW_A + 8)) m m' ->
  el_ehgA m' -> rw_cells asegs m' EL_UNW_A (uw_cellsA true) -> el_libA m'.
Proof.
  intros m m' [(S & L & LW) (E & U & T)] AG E' U'. unfold el_lib_rng in AG. split; [split; [| split]| split; [exact E'| split; [exists true; exact U'|]]].
  - eapply sj_lib_agree; [exact S|]. intros a Ha. apply AG. split; [left; exact (sj_lib_rng_fp _ Ha)|]. unfold sj_lib_rng in Ha. unfold EL_EHG_A, EL_UNW_A. lia.
  - eapply pj_locA_agree; [exact L|]. intros a Ha. apply AG. split; [left; exact (loc_rng_fp _ Ha)|]. unfold PJ_LOC_LO_A, PJ_LOC_HI_A in Ha. unfold EL_EHG_A, EL_UNW_A. lia.
  - eapply lockwA_agree; [exact LW|]. intros a Ha. apply AG. split; [left; exact (lock_rng_fp _ Ha)|]. unfold PJ_LOCKW_A in Ha. unfold EL_EHG_A, EL_UNW_A. lia.
  - eapply rw_cells_agree_nw; [exact T|]. intros a Ha. apply AG. cbn [cells_size csize Nat.add] in Ha. unfold EL_TPLOC_A, TPV_A in Ha. unfold EL_EHG_A, EL_UNW_A, EL_TPLOC_A, TPV_A.
    split; [right; right; lia| lia].
Qed.
Lemma outside_In : forall (W : list (Z * Z)) x lo hi, outside W x -> In (lo, hi) W -> ~ (lo <= x < hi).
Proof.
  induction W as [|[l h] W IH]; intros x lo hi Ho Hin; [destruct Hin|].
  cbn [outside] in Ho. destruct Ho as [H1 H2]. destruct Hin as [E|Hin]; [injection E as <- <-; exact H1| exact (IH x lo hi H2 Hin)].
Qed.
Lemma arm_WA_ehg : forall X, In (EL_EHG_A, EL_EHG_A + 12) (arm_WA X).
Proof. intros X. unfold arm_WA. apply in_or_app. left. cbn. tauto. Qed.
Lemma arm_WA_unw : forall X, In (EL_UNW_A, EL_UNW_A + 8) (arm_WA X).
Proof. intros X. unfold arm_WA, EL_LIB_FP. apply in_or_app. right. apply in_or_app. right. cbn. tauto. Qed.
Lemma ainv_rng_nostatic : forall RT (AF : art_facts RT) Σ (m : mem) E x, ART RT Σ m -> a_live RT Σ E -> aenvA_ok E -> ainv_rng E x ->
  ~ (0x10000 <= x < SEGTOP_A).
Proof.
  intros RT AF Σ m E x HA (LT & LS & LP & LF & _) OK Hx.
  destruct OK as [_ _ _ _ (? & ? & ? & ? & ?) (? & ? & ? & ? & ?) PT _ (D8 & ? & ? & DSEG & ?) _ _].
  unfold ainv_rng in Hx. destruct Hx as [Hx|[Hx|[Hx|[Hx|Hx]]]].
  - pose proof (af_live_range RT AF Σ m _ _ HA LT) as (_ & _ & [Y|Y]); lia.
  - pose proof (af_live_range RT AF Σ m _ _ HA LS) as (_ & _ & [Y|Y]); lia.
  - destruct LP as [E0|LP]; [rewrite E0 in Hx; unfold zlength in Hx; cbn [length] in Hx; lia|].
    assert (NE : ae_p1 E <> []) by (intros E0; rewrite E0 in Hx; unfold zlength in Hx; cbn [length] in Hx; lia). specialize (PT NE).
    pose proof (af_live_range RT AF Σ m _ _ HA LP) as (_ & _ & [Y|Y]); lia.
  - lia.
  - unfold shad, SHB, SEGTOP_A in *. pose proof (Z.div_pos (ae_DOC E) 8 ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma el_auxvA_of_D : forall lo m, D_auxv.el_auxvA lo m -> El_xs_adaptA.el_auxvA lo m.
Proof.
  intros lo m (av & x16 & x11 & rnd & C & B & L1 & L2 & L3 & R1 & R2 & R3). exists av, x16, 4096, x11, x11, 0, rnd.
  split; [exact C|]. split; [exact B|]. repeat split; lia.
Qed.

Definition wsB (RA : Z) (X : lfA) : list word :=
  if RA =? 0xb2d1c then [Z_to_bv 64 (shad (lf_F X)); Z_to_bv 64 (lf_F X); Z_to_bv 64 (lf_S1 X); Z_to_bv 64 (lf_usp X)]
  else [Z_to_bv 64 (lf_S1 X); Z_to_bv 64 (lf_usp X)].
Lemma wsB_regs : forall RA X s2 s3, kd_ok RA -> (RA = 0xb2d1c \/ (s2 = Z_to_bv 64 (lf_F X) /\ s3 = Z_to_bv 64 (shad (lf_F X)))) ->
  nth (kd_i0 RA) (wsB RA X) (Z_to_bv 64 0) = Z_to_bv 64 (lf_usp X) /\ nth (kd_i1 RA) (wsB RA X) (Z_to_bv 64 0) = Z_to_bv 64 (lf_S1 X)
  /\ kd_x18 RA (wsB RA X) s2 = Z_to_bv 64 (lf_F X) /\ kd_x19 RA (wsB RA X) s3 = Z_to_bv 64 (shad (lf_F X)).
Proof.
  intros RA X s2 s3 [-> |[-> | ->]] S23; unfold kd_i0, kd_i1, kd_x18, kd_x19, wsB; cbn [Z.eqb Pos.eqb nth];
    (destruct S23 as [S23|(S2 & S3)]; [try lia| rewrite ?S2, ?S3]); repeat split; reflexivity.
Qed.

Section BridgeB.
  Variable RT : rt_sig.
  Hypothesis AF : art_facts RT.
  Hypothesis RC : rt_contracts RT.
  Hypothesis ALC : aligned_alloc_contract RT.
  Variable WIN : rt_win RT.
  Variable PMc : Model -> Prop.
  Hypothesis XROW : forall c Σ (m : mem), ARTW RT WIN c Σ m -> io_ro_ok m.

  Local Ltac ul := unfold FUZZ_STACK in *; unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, SHB, EL_THROW_STACK_A, NORET_DEPTH, FUZZ_SP0GAP, EXC_SIZE in *; lia.

  Lemma throw_site_genB : forall (a pcs RA : Z) (XP : mem -> Z -> Prop) (RGS : Z -> word -> Prop),
    (fdfs_only PMc -> mat_stable PMc -> site_stmtB RT WIN PMc pcs RA XP RGS) ->
    (a = 22 \/ a = 23 \/ a = 24) -> kd_ok RA -> site_fszB pcs = kd_fsz RA ->
    (forall X j cv (m : mem), lfA_ok X -> length j = site_jlenB pcs -> site_cvB pcs cv ->
        rw_cells asegs m (lf_S1 X - site_fszB pcs) (site_frameB pcs X j cv) ->
        hcells_okA m (lf_S1 X - site_fszB pcs) 0 (kd_hcs RA) (wsB RA X) /\ XP m (lf_S1 X - site_fszB pcs)) ->
    (forall X s0 s1 s2 s3 s4 s8, lfA_ok X -> site_regsB pcs (lf_S1 X - site_fszB pcs) s0 s2 s3 s1 s4 s8 (lf_F X) -> RGS (lf_S1 X - site_fszB pcs) s1) ->
    throw_siteB RT PMc (ARTW RT WIN) a pcs.
  Proof.
    intros a pcs RA XP RGS HST KA KR FSZE HFR HRG.
    unfold throw_siteB. intros Σ K X E sel idx jr jos t j cv ra gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
      IN FDO MST LK OKE LE SEL IDX AL FRS LPA LVB CRB ARTg MIg STg NEED AM FRM XD AUX SP0 JL CV FR RG POST.
    pose proof LK as [(SPR & SPA') (SPT & SPA) (LLO & LOR) (FPOS & F64 & FSEG & FLO) (FSELF & SHB0 & SHT)].
    pose proof LE as (EDOC & EFD & EKD & ELO & EHI).
    pose proof AM as (C16 & C100 & C128 & CE & CO & CS & AI & LIB & NL & IOS).
    pose proof (af_sp0_range RT AF Σ m ARTg) as SP0R. pose proof AL as (ALT & ALS & ALP & ALF & WLO). rewrite ELO in WLO.
    destruct (HFR X j cv m LK JL CV FR) as [HC XP0]. pose proof (HRG X s0 s1 s2 s3 s4 s8 LK RG) as RG0.
    pose proof (site_frameB_size pcs X j cv JL) as CSZ. rewrite FSZE in CSZ.
    assert (S23 : RA = 0xb2d1c \/ (s2 = Z_to_bv 64 (lf_F X) /\ s3 = Z_to_bv 64 (shad (lf_F X)))).
    { destruct (Z.eqb_spec RA 0xb2d1c) as [EQ|NE]; [left; exact EQ| right].
      revert RG FSZE. unfold kd_fsz, site_fszB, site_regsB. apply Z.eqb_neq in NE. rewrite NE.
      destruct ((pcs =? EL_SITE_END_B) || (pcs =? 0xb2fb4)); intros RG FSZE; [destruct RG as (_ & R2 & R3 & _); split; assumption| lia]. }
    assert (S48 : s4 = Z_to_bv 64 (lf_F X + 32) /\ s8 = Z_to_bv 64 (lf_F X)).
    { revert RG. unfold site_regsB. destruct ((pcs =? EL_SITE_END_B) || (pcs =? 0xb2fb4)); intros RG;
        [destruct RG as (_ & _ & _ & R4 & R8)| destruct RG as (_ & R4 & R8)]; split; assumption. }
    destruct S48 as [S4E S8E].
    assert (FSZ : 32 <= kd_fsz RA <= 144 /\ kd_fsz RA mod 16 = 0) by (unfold kd_fsz; destruct (RA =? 0xb2d1c); (split; [lia| reflexivity])).
    rewrite FSZE in *. set (fsz := kd_fsz RA) in *. set (usp := lf_S1 X - fsz) in *.
    assert (U16 : usp mod 16 = 0) by (subst usp; destruct FSZ as [F1 F2]; clear - SPA' F1 F2; Z.div_mod_to_equations; lia).
    assert (UB4 : usp + fsz = lf_S1 X) by (subst usp; lia).
    pose proof LIB as [(LS & LL & LLW) (LE' & (uw & LU) & LT)].
    change TPV_A with TPV_XA.
    apply (HST FDO MST Σ K usp (lf_lo X) (lf_usp X) (wsB RA X) uw (site_frameB pcs X j cv) ra gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 _ s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
             RG0 XP0 HC FR CSZ LPA LVB ltac:(clear - CRB; lia) ARTg MIg STg LLO WLO
             ltac:(clear - NEED FSZ UB4; ul) ltac:(clear - SP0 SPR FSZ UB4; ul) ltac:(clear - SP0 SPR FSZ UB4; ul) U16).
    - change EL_EHG_XA with EL_EHG_A. exact LE'.
    - exact (el_unwA_bytes m uw LU).
    - exact XD.
    - destruct IOS as (g & _ & G2). exists g. exact G2.
    - exact (el_auxvA_of_D _ _ AUX).
    - clear - SPR UB4 FSZ; lia.
    -
      intros Σ2 m2 F2 t0' t1' t2' e0 e1 e2 e3 e4 e5 e6 e7 s6' s7' t3' t4' t5' t6' XPo.
      destruct (wsB_regs RA X s2 s3 KR S23) as (V0 & V1 & V2 & V3).
      rewrite V0, V1, V2, V3, S4E, S8E, UB4. change TPV_XA with TPV_A. change EL_LRET_XA with EL_LRET_A.
      apply (POST (rt_credit RT Σ - mcost EXC_SIZE) Σ2 m2 fc F2 (Z_to_bv 64 EL_LRET_A) t0' t1' t2' e0 e1 e2 e3 e4 e5 e6 e7 s6' s7' s8 s9 s10 s11 t3' t4' t5' t6').
      destruct XPo as (HA2 & MI2 & ST2 & LV2 & FR2 & SP02 & CR2 & EHG2 & UB2' & WR2 & PRES2). fold fsz in ST2, PRES2. rewrite UB4 in ST2, PRES2.
      assert (AG2 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) (lf_S1 X) (bv_unsigned x) ->
                ~ (EL_EHG_A <= bv_unsigned x < EL_EHG_A + 12) -> ~ (EL_UNW_A <= bv_unsigned x < EL_UNW_A + 8) -> m2 x = m x).
      { intros x Hx NE NU. apply (PRES2 x Hx); [exact NE| exact NU]. }
      unfold lret_postA, arm_postA. unfold artxA.
      split; [exact HA2|]. split; [exact MI2|]. split; [exact ST2|]. split; [exact FRM|].
      split; [exact LV2|]. split; [exact FR2|]. split; [exact SP02|].
      split; [replace (arm_costA a (ae_n E) (ae_sn E) (zlength (ae_p1 E))) with (mcost EXC_SIZE + 16) by (unfold arm_costA; destruct KA as [-> |[-> | ->]]; reflexivity); lia|].
      split. { intros x Hx Ho. apply (AG2 x Hx); [exact (outside_In _ _ _ _ Ho (arm_WA_ehg X))| exact (outside_In _ _ _ _ Ho (arm_WA_unw X))]. }
      split; [| intros _; clear - KA; lia].

      assert (AGhi : agree_on (fun x => lf_S1 X <= x < USTACK_TOP \/ lf_F X <= x < lf_F X + 1016 \/ shad (lf_F X) <= x < shad (lf_F X) + 128) m m2).
      { intros x Hx. apply AG2.
        - destruct Hx as [Hx|[Hx|Hx]]; [left; exact Hx| right; right; right; left| right; right; right; right]; exists (lf_F X), 4%nat; rewrite FRS; (split; [left; reflexivity|]);
            change (fs_size 4) with 1024; [lia|]. unfold shad in *. clear - Hx F64 FPOS. Z.div_mod_to_equations. lia.
        - unfold EL_EHG_A, shad, SHB in *. clear - Hx FSEG SPR SPT LLO LOR. ul.
        - unfold EL_UNW_A, shad, SHB in *. clear - Hx FSEG SPR SPT LLO LOR. ul. }
      exists jr, jos. unfold arm_memA.
      split; [eapply rw_cells_agree_nw; [exact C16|]; intros x Hx; apply AGhi; cbn [cells_size csize Nat.add] in Hx; left; clear - Hx SPT SPR; ul|].
      split; [eapply rw_cells_agree_nw; [exact C100|]; intros x Hx; apply AGhi; cbn [cells_size csize Nat.add] in Hx; left; clear - Hx SPT SPR; ul|].
      split; [eapply rw_cells_agree_nw; [exact C128|]; intros x Hx; apply AGhi; cbn [cells_size csize Nat.add] in Hx; left; clear - Hx SPT SPR; ul|].
      split; [eapply rw_cells_agree_nw; [exact CE|]; intros x Hx; apply AGhi; cbn [cells_size csize Nat.add] in Hx; right; left; lia|].
      split; [eapply rw_cells_agree_nw; [exact CO|]; intros x Hx; apply AGhi; cbn [cells_size csize Nat.add] in Hx; right; left; lia|].
      split; [eapply rw_cells_agree_nw; [exact CS|]; intros x Hx; apply AGhi; unfold el_shadow_armA in Hx; rewrite el_shadowA_size in Hx; right; right; lia|].
      split. { apply (AINV_A_agree E m m2 AI). intros x Hx. pose proof (ainv_rng_nostatic RT AF Σ m E _ ARTg AL OKE Hx) as NS.
               apply AG2; [exact (ainv_rng_aclient RT Σ E _ _ AL OKE Hx)| unfold EL_EHG_A; clear - NS; ul| unfold EL_UNW_A; clear - NS; ul]. }
      split. { apply (el_libA_after m m2 LIB); [| change EL_EHG_A with EL_EHG_XA; exact EHG2| exact (el_unwA_of_bytes m2 UB2' WR2)].
               intros x (Hx & NE & NU). apply AG2; [right; left; exact (proj1 (el_lib_rng_static _ Hx))| exact NE| exact NU]. }
      split. { apply (libc_nl_agree m m2 NL). intros x Hx. apply AG2; [right; left; exact (libc_nl_static _ Hx)| unfold LIBC_NL in Hx; unfold EL_EHG_A; lia| unfold LIBC_NL in Hx; unfold EL_UNW_A; lia]. }
      destruct IOS as (g & G1 & G2). exists g. split; [exact (proj1 (af_got_lib (rt_sigW RT (ARTW RT WIN (rt_credit RT Σ - mcost EXC_SIZE))) (w_facts RT WIN _) Σ2 m2 HA2))|].
      apply (ro_cells_agree asegs m m2 _ _ G2). intros x Hx. cbn [cells_size csize Nat.add] in Hx.
      apply AG2; [right; left; apply client_static_intro; lia| unfold EL_EHG_A; lia| unfold EL_UNW_A; lia].
  Qed.
End BridgeB.

Ltac peel H Hc base k :=
  lazymatch type of H with rw_cells _ ?m ?A (?c :: ?rest) =>
    change (rw_cells asegs m A (c :: rest)) with (rw_cells asegs m A ([c] ++ rest)) in H;
    apply (proj1 (rw_cells_app asegs m A [c] rest)) in H; destruct H as [Hc H]; cbn [cells_size csize Nat.add] in H;
    lazymatch type of H with rw_cells _ _ ?A' _ => replace A' with (base + k) in H by lia end
  end.
Ltac hc_fin := repeat lazymatch goal with
  | |- rw_cells _ _ _ _ /\ _ => split; [assumption|]
  | |- True => exact I
  | |- (_ = _ \/ _ = _)%nat /\ _ => split; [right; reflexivity|]
  | |- _ /\ _ => split; [lia|]
  end.

Lemma hcells_castB : forall (m : mem) X u j cv pcs,
  pcs <> EL_SITE_END_B -> pcs <> 0xb2fb4 ->
  rw_cells asegs m u (site_frameB pcs X j cv) -> hcells_okA m u 0 el_hcs_bcast (wsB 0xb2d1c X).
Proof.
  intros m X u j cv pcs N1 N2 H. unfold site_frameB in H.
  destruct (Z.eqb_spec pcs EL_SITE_END_B); [lia|]. destruct (Z.eqb_spec pcs 0xb2fb4); [lia|].
  replace u with (u + 0) in H by lia.
  peel H P0 u 8. peel H G0 u 16. peel H G1 u 24. peel H G2 u 32. peel H G3 u 40.
  unfold el_hcs_bcast, wsB. cbn [Z.eqb Pos.eqb hcells_okA cwA nth]. hc_fin.
Qed.

Lemma hcells_beginB : forall (m : mem) X u j cv, rw_cells asegs m u (site_frameB 0xb2fb4 X j cv) -> hcells_okA m u 0 el_hcs_bbegin (wsB 0xb3014 X).
Proof.
  intros m X u j cv H. unfold site_frameB, EL_SITE_END_B in H. cbn [Z.eqb Pos.eqb] in H. replace u with (u + 0) in H by lia.
  peel H P0 u 8. peel H G0 u 16. peel H G1 u 24.
  unfold el_hcs_bbegin, wsB. cbn [Z.eqb Pos.eqb hcells_okA cwA nth]. hc_fin.
Qed.
Lemma hcells_endB : forall (m : mem) X u j cv, rw_cells asegs m u (site_frameB EL_SITE_END_B X j cv) -> hcells_okA m u 0 el_hcs_bend (wsB 0xb31d0 X).
Proof.
  intros m X u j cv H. unfold site_frameB in H. rewrite Z.eqb_refl in H. replace u with (u + 0) in H by lia.
  peel H P0 u 8. peel H G0 u 16. peel H G1 u 24.
  unfold el_hcs_bend, wsB. cbn [Z.eqb Pos.eqb hcells_okA cwA nth]. hc_fin.
Qed.

Section SitesXB.
  Variable RT : rt_sig.
  Hypothesis AF : art_facts RT.
  Hypothesis RC : rt_contracts RT.
  Hypothesis ALC : aligned_alloc_contract RT.
  Variable WIN : rt_win RT.
  Variable PMc : Model -> Prop.
  Hypothesis XROW : forall c Σ (m : mem), ARTW RT WIN c Σ m -> io_ro_ok m.

  Local Ltac ul := unfold FUZZ_STACK in *; unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, SHB in *; lia.

  Lemma rgs_s1B : forall pcs X s0 s1 s2 s3 s4 s8, lfA_ok X -> site_regsB pcs (lf_S1 X - site_fszB pcs) s0 s2 s3 s1 s4 s8 (lf_F X) ->
    RGS_s1 (lf_S1 X - site_fszB pcs) s1.
  Proof.
    intros pcs X s0 s1 s2 s3 s4 s8 LK RG.
    assert (R1 : s1 = Z_to_bv 64 SHB) by (revert RG; unfold site_regsB; destruct ((pcs =? EL_SITE_END_B) || (pcs =? 0xb2fb4)); intros RG; apply RG).
    pose proof LK as [(SPR & _) (SPT & _) (LLO & LOR) _ _].
    assert (FZ : 0 <= site_fszB pcs <= 48) by (unfold site_fszB; destruct ((pcs =? EL_SITE_END_B) || (pcs =? 0xb2fb4)); lia).
    unfold RGS_s1. split; [exact R1|]. clear - SPR SPT LLO LOR FZ. ul.
  Qed.

  Local Ltac inst pcs RA RAW HFR :=
    apply (throw_site_genB RT AF WIN PMc _ pcs RA XP_none RGS_s1 (fun FDO MST => RAW RT AF RC ALC WIN PMc FDO MST XROW));
    [clear; lia| unfold kd_ok; tauto| reflexivity| HFR| intros X s0 s1 s2 s3 s4 s8 LK RG; exact (rgs_s1B pcs X s0 s1 s2 s3 s4 s8 LK RG)].

  Lemma TS_b2fb4 : throw_siteB RT PMc (ARTW RT WIN) 23 0xb2fb4.
  Proof using AF RC ALC XROW.
    inst 0xb2fb4 0xb3014 site_rawB_b2fb4 ltac:(intros X j cv m LK JL CV FR; split; [exact (hcells_beginB m X _ j cv FR)| exact I]).
  Qed.
  Lemma TS_b3170 : throw_siteB RT PMc (ARTW RT WIN) 24 EL_SITE_END_B.
  Proof using AF RC ALC XROW.
    inst EL_SITE_END_B 0xb31d0 site_rawB_b3170 ltac:(intros X j cv m LK JL CV FR; split; [exact (hcells_endB m X _ j cv FR)| exact I]).
  Qed.
  Local Ltac inst_cast pcs RAW :=
    inst pcs 0xb2d1c RAW
      ltac:(intros X j cv m LK JL CV FR; split; [exact (hcells_castB m X _ j cv pcs ltac:(unfold EL_SITE_END_B; lia) ltac:(lia) FR)| exact I]).
  Lemma TS_b272c : throw_siteB RT PMc (ARTW RT WIN) 22 0xb272c.  Proof using AF RC ALC XROW. inst_cast 0xb272c site_rawB_b272c. Qed.
  Lemma TS_b27f8 : throw_siteB RT PMc (ARTW RT WIN) 22 0xb27f8.  Proof using AF RC ALC XROW. inst_cast 0xb27f8 site_rawB_b27f8. Qed.
  Lemma TS_b29e8 : throw_siteB RT PMc (ARTW RT WIN) 22 0xb29e8.  Proof using AF RC ALC XROW. inst_cast 0xb29e8 site_rawB_b29e8. Qed.
  Lemma TS_b2ac4 : throw_siteB RT PMc (ARTW RT WIN) 22 0xb2ac4.  Proof using AF RC ALC XROW. inst_cast 0xb2ac4 site_rawB_b2ac4. Qed.
  Lemma TS_b2b84 : throw_siteB RT PMc (ARTW RT WIN) 22 0xb2b84.  Proof using AF RC ALC XROW. inst_cast 0xb2b84 site_rawB_b2b84. Qed.
  Lemma TS_b2c64 : throw_siteB RT PMc (ARTW RT WIN) 22 0xb2c64.  Proof using AF RC ALC XROW. inst_cast 0xb2c64 site_rawB_b2c64. Qed.
  Lemma TS_b2cc0 : throw_siteB RT PMc (ARTW RT WIN) 22 0xb2cc0.  Proof using AF RC ALC XROW. inst_cast 0xb2cc0 site_rawB_b2cc0. Qed.
  Lemma TS_b2d2c : throw_siteB RT PMc (ARTW RT WIN) 22 0xb2d2c.  Proof using AF RC ALC XROW. inst_cast 0xb2d2c site_rawB_b2d2c. Qed.

  Theorem throw_site23B : throw_siteB RT PMc (ARTW RT WIN) 23 0xb2fb4.
  Proof using AF RC ALC XROW. exact TS_b2fb4. Qed.
  Theorem throw_site24B : throw_siteB RT PMc (ARTW RT WIN) 24 EL_SITE_END_B.
  Proof using AF RC ALC XROW. exact TS_b3170. Qed.
  Theorem throw_site22B : forall pcs, throw_siteB RT PMc (ARTW RT WIN) 22 pcs.
  Proof using AF RC ALC XROW.
    intros pcs. unfold throw_siteB. intros Σ K X E sel idx jr jos t j cv ra gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m IN.
    generalize IN. revert Σ K X E sel idx jr jos t j cv ra gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
    cbn [el_site_pcsB Z.eqb Pos.eqb] in IN.
    destruct IN as [<- |[<- |[<- |[<- |[<- |[<- |[<- |[<- |[]]]]]]]]];
      [exact TS_b272c| exact TS_b27f8| exact TS_b29e8| exact TS_b2ac4| exact TS_b2b84| exact TS_b2c64| exact TS_b2cc0| exact TS_b2d2c].
  Qed.
End SitesXB.
