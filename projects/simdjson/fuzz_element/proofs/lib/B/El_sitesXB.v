(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac MState Mem Frame Cells Step Exec ImageA RzCPS RegsEquiv StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import Sj_stage1_kit.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.B Require Import Layout RT_iface RT_iface2 RT_iface5 D_defs D_kit D_clx D_libiface D_auxv TopA_iodefs Sj_akit Sj_hkit Sj_num_akit Sj_acps
     Atp_defsA Pj_defsA El_defsA El_frontA El_sitesA.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.AS Require Import PropExec AxSymExec3.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import El_xs_core.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.B Require Import El_xs_coreA El_xs_adaptA El_throwA El_xr_bbegin El_xr_bcast El_xr_bcstr El_xr_bend El_throw_siteA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Import AX2.
Open Scope Z_scope.

Lemma el_unwA_bytes : forall m uw, rw_cells bsegs m EL_UNW_A (uw_cellsA uw) ->
  bytes_at bsegs m EL_UNW_XA (map (fun b => Z_to_bv 8 b) (uw_bytesA uw)) /\ wr_at bsegs m EL_UNW_XA 8.
Proof.
  intros m uw [[_ B] W]. change EL_UNW_A with EL_UNW_XA in B, W. destruct uw; cbn -[bytes_at EL_UNW_XA Z_to_bv] in B; cbn [cells_size uw_cellsA csize repeat Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in W;
    (split; [exact B| exact W]).
Qed.
Lemma el_unwA_of_bytes : forall m, bytes_at bsegs m EL_UNW_XA (map (fun b => Z_to_bv 8 b) (uw_bytesA true)) -> wr_at bsegs m EL_UNW_XA 8 ->
  rw_cells bsegs m EL_UNW_A (uw_cellsA true).
Proof.
  intros m B W. change EL_UNW_A with EL_UNW_XA. split; [split; [cbn; repeat split; reflexivity|]|].
  - cbn -[bytes_at EL_UNW_XA Z_to_bv]. cbn -[bytes_at EL_UNW_XA Z_to_bv] in B. exact B.
  - cbn [cells_size uw_cellsA csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. exact W.
Qed.
Lemma el_libA_after : forall m m', el_libA m ->
  agree_on (fun x => el_lib_rng x /\ ~ (EL_EHG_A <= x < EL_EHG_A + 12) /\ ~ (EL_UNW_A <= x < EL_UNW_A + 8)) m m' ->
  el_ehgA m' -> rw_cells bsegs m' EL_UNW_A (uw_cellsA true) -> el_libA m'.
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
  if RA =? 0xb8614 then
    [Z_to_bv 64 (lf_F X + 96); Z_to_bv 64 (shad (lf_F X + 216)); Z_to_bv 64 SHB; Z_to_bv 64 (shad (lf_F X + 208)); Z_to_bv 64 (lf_F X + 216); Z_to_bv 64 (lf_F X + 208);
     Z_to_bv 64 (lf_F X + 32); Z_to_bv 64 (shad (lf_F X)); Z_to_bv 64 (lf_F X); Z_to_bv 64 (lf_S1 X); Z_to_bv 64 (lf_usp X)]
  else [Z_to_bv 64 (lf_F X + 32); Z_to_bv 64 (shad (lf_F X)); Z_to_bv 64 (lf_F X); Z_to_bv 64 (lf_S1 X); Z_to_bv 64 (lf_usp X)].
Lemma wsB_regs : forall RA X s5, kd_ok RA -> (RA = 0xb8614 \/ s5 = Z_to_bv 64 (lf_F X + 96)) ->
  nth (kd_i0 RA) (wsB RA X) (Z_to_bv 64 0) = Z_to_bv 64 (lf_usp X) /\ nth (kd_i1 RA) (wsB RA X) (Z_to_bv 64 0) = Z_to_bv 64 (lf_S1 X)
  /\ nth (kd_i2 RA) (wsB RA X) (Z_to_bv 64 0) = Z_to_bv 64 (lf_F X) /\ nth (kd_i3 RA) (wsB RA X) (Z_to_bv 64 0) = Z_to_bv 64 (shad (lf_F X))
  /\ nth (kd_i4 RA) (wsB RA X) (Z_to_bv 64 0) = Z_to_bv 64 (lf_F X + 32) /\ kd_s5 RA (wsB RA X) s5 = Z_to_bv 64 (lf_F X + 96).
Proof.
  intros RA X s5 [-> |[-> |[-> | ->]]] S5; unfold kd_i0, kd_i1, kd_i2, kd_i3, kd_i4, kd_s5, wsB; cbn [Z.eqb Pos.eqb nth]; (destruct S5 as [S5|S5]; [try lia| rewrite ?S5]); repeat split; reflexivity.
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

  Lemma throw_site_genB : forall (a pcs RA : Z) (XP : mem -> Z -> Prop) (RGS : Z -> word -> word -> word -> Prop),
    (fdfs_only PMc -> mat_stable PMc -> site_stmtB RT WIN PMc pcs RA XP RGS) ->
    (a = 22 \/ a = 23 \/ a = 24) -> kd_ok RA -> site_fszB pcs = kd_fsz RA ->
    (forall X j cv (m : mem), lfA_ok X -> length j = site_jlenB pcs -> site_cvB pcs cv ->
        rw_cells bsegs m (lf_S1 X - site_fszB pcs) (site_frameB pcs X j cv) ->
        hcells_okA m (lf_S1 X - site_fszB pcs) 0 (kd_hcs RA) (wsB RA X) /\ XP m (lf_S1 X - site_fszB pcs)) ->
    (forall X s0 s2 s3, lfA_ok X -> site_regsB pcs (lf_S1 X - site_fszB pcs) s0 s2 s3 -> RGS (lf_S1 X - site_fszB pcs) s0 s2 s3) ->
    throw_siteB RT PMc (ARTW RT WIN) a pcs.
  Proof.
    intros a pcs RA XP RGS HST KA KR FSZE HFR HRG.
    unfold throw_siteB. intros Σ K X E sel idx jr jos t j cv ra gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
      IN FDO MST LK OKE LE SEL IDX AL FRS LPA LVB CRB ARTg MIg STg NEED AM FRM XD AUX SP0 JL CV FR RG POST.
    pose proof LK as [(SPR & SPA') (SPT & SPA) (LLO & LOR) (FPOS & F64 & FSEG & FLO) (FSELF & SHB0 & SHT)].
    pose proof LE as (EDOC & EFD & EKD & ELO & EHI).
    pose proof AM as (C16 & C100 & C128 & CE & CO & CS & AI & LIB & NL & IOS).
    pose proof (af_sp0_range RT AF Σ m ARTg) as SP0R. pose proof AL as (ALT & ALS & ALP & ALF & WLO). rewrite ELO in WLO.
    destruct (HFR X j cv m LK JL CV FR) as [HC XP0]. pose proof (HRG X s0 s2 s3 LK RG) as RG0.
    pose proof (site_frameB_size pcs X j cv JL) as CSZ. rewrite FSZE in CSZ.
    assert (FSZ : 32 <= kd_fsz RA <= 144 /\ kd_fsz RA mod 16 = 0) by (unfold kd_fsz; destruct (RA =? 0xb5264); [| destruct (RA =? 0xb8614)]; (split; [lia| reflexivity])).
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
      destruct (wsB_regs RA X (Z_to_bv 64 (lf_F X + 96)) KR (or_intror eq_refl)) as (V0 & V1 & V2 & V3 & V4 & V5).
      rewrite V0, V1, V2, V3, V4, V5, UB4. change TPV_XA with TPV_A. change EL_LRET_XA with EL_LRET_A.
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
      apply (ro_cells_agree bsegs m m2 _ _ G2). intros x Hx. cbn [cells_size csize Nat.add] in Hx.
      apply AG2; [right; left; apply client_static_intro; lia| unfold EL_EHG_A; lia| unfold EL_UNW_A; lia].
  Qed.
End BridgeB.

Ltac peel H Hc base k :=
  lazymatch type of H with rw_cells _ ?m ?A (?c :: ?rest) =>
    change (rw_cells bsegs m A (c :: rest)) with (rw_cells bsegs m A ([c] ++ rest)) in H;
    apply (proj1 (rw_cells_app bsegs m A [c] rest)) in H; destruct H as [Hc H]; cbn [cells_size csize Nat.add] in H;
    lazymatch type of H with rw_cells _ _ ?A' _ => replace A' with (base + k) in H by lia end
  end.
Ltac hc_fin := repeat lazymatch goal with
  | |- rw_cells _ _ _ _ /\ _ => split; [assumption|]
  | |- True => exact I
  | |- (_ = _ \/ _ = _)%nat /\ _ => split; [right; reflexivity|]
  | |- _ /\ _ => split; [lia|]
  end.

Lemma hcells_savedB : forall (m : mem) X u b ra,
  rw_cells bsegs m (u + b) (lftoi_savedB X ++ [C8 (Z_to_bv 64 ra)]) -> 0 <= ra < 2^64 ->
  rw_cells bsegs m (u + b) [C8 (Z_to_bv 64 (lf_F X + 32))] /\ rw_cells bsegs m (u + (b + 8)) [C8 (Z_to_bv 64 (shad (lf_F X)))]
  /\ rw_cells bsegs m (u + (b + 16)) [C8 (Z_to_bv 64 (lf_F X))] /\ rw_cells bsegs m (u + (b + 24)) [C8 (Z_to_bv 64 (lf_S1 X))]
  /\ rw_cells bsegs m (u + (b + 32)) [C8 (Z_to_bv 64 (lf_usp X))] /\ rw_cells bsegs m (u + (b + 40)) [C8 (Z_to_bv 64 ra)].
Proof.
  intros m X u b ra H RA. unfold lftoi_savedB in H. cbn [app] in H.
  peel H G0 u (b + 8). peel H G1 u (b + 16). peel H G2 u (b + 24). peel H G3 u (b + 32). peel H G4 u (b + 40).
  split; [exact G0|]. split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4| exact H].
Qed.

Lemma hcells_kindB : forall (m : mem) X u b ra,
  rw_cells bsegs m (u + b) (lftoi_savedB X ++ [C8 (Z_to_bv 64 ra)]) -> 0 <= ra < 2^64 ->
  hcells_okA m u 0 [(b, 8%nat, HVopq); (b + 8, 8%nat, HVopq); (b + 16, 8%nat, HVopq); (b + 24, 8%nat, HVopq); (b + 32, 8%nat, HVopq); (b + 40, 8%nat, HVlit ra)]
             [Z_to_bv 64 (lf_F X + 32); Z_to_bv 64 (shad (lf_F X)); Z_to_bv 64 (lf_F X); Z_to_bv 64 (lf_S1 X); Z_to_bv 64 (lf_usp X)].
Proof.
  intros m X u b ra H RA. destruct (hcells_savedB m X u b ra H RA) as (G0 & G1 & G2 & G3 & G4 & G5).
  cbn [hcells_okA cwA nth]. hc_fin.
Qed.

Lemma hcells_endB : forall (m : mem) X u j cv, length j = 36%nat ->
  rw_cells bsegs m u (site_frameB EL_SITE_END_B X j cv) ->
  hcells_okA m u 0 el_hcs_bend (wsB 0xb8614 X) /\ rw_cells bsegs m (u + 88) [C4 (Z_to_bv 64 cv)].
Proof.
  intros m X u j cv JL H. unfold site_frameB, EL_SITE_END_B in H. cbn [Z.eqb Pos.eqb app] in H.
  replace u with (u + 0) in H by lia.
  peel H P0 u 8. peel H G0 u 16. peel H G1 u 24. peel H G2 u 32. peel H G3 u 40. peel H G4 u 48. peel H G5 u 56. peel H G6 u 64.
  peel H P1 u 88. peel H GC u 92. peel H P2 u 96.
  change (C8 (Z_to_bv 64 (lf_F X + 32)) :: C8 (Z_to_bv 64 (shad (lf_F X))) :: C8 (Z_to_bv 64 (lf_F X)) :: C8 (Z_to_bv 64 (lf_S1 X)) :: C8 (Z_to_bv 64 (lf_usp X)) :: [C8 (Z_to_bv 64 0xb2474)])
    with (lftoi_savedB X ++ [C8 (Z_to_bv 64 0xb2474)]) in H.
  destruct (hcells_savedB m X u 96 0xb2474 H ltac:(lia)) as (H0 & H1 & H2 & H3 & H4 & H5).
  split; [| exact GC]. unfold el_hcs_bend, wsB. cbn [Z.eqb Pos.eqb hcells_okA cwA nth]. hc_fin.
Qed.

Lemma hcells_svB : forall (m : mem) X u j cv, length j = 28%nat ->
  rw_cells bsegs m u (site_frameB EL_SITE_SV_B X j cv) ->
  hcells_okA m u 0 el_hcs_bcast (wsB 0xb5264 X) /\ rw_cells bsegs m (u + 24) [C4 (Z_to_bv 64 cv)].
Proof.
  intros m X u j cv JL H. unfold site_frameB, EL_SITE_SV_B, EL_SITE_END_B, EL_SITE_CSTR_B in H. cbn [Z.eqb Pos.eqb app] in H.
  replace u with (u + 0) in H by lia.
  peel H P0 u 8. peel H P1 u 24. peel H GC u 28. peel H P2 u 32.
  change (C8 (Z_to_bv 64 (lf_F X + 32)) :: C8 (Z_to_bv 64 (shad (lf_F X))) :: C8 (Z_to_bv 64 (lf_F X)) :: C8 (Z_to_bv 64 (lf_S1 X)) :: C8 (Z_to_bv 64 (lf_usp X)) :: [C8 (Z_to_bv 64 0xb2400)])
    with (lftoi_savedB X ++ [C8 (Z_to_bv 64 0xb2400)]) in H.
  split; [| exact GC]. unfold el_hcs_bcast, wsB. cbn [Z.eqb Pos.eqb]. exact (hcells_kindB m X u 32 0xb2400 H ltac:(lia)).
Qed.

Lemma hcells_castB : forall (m : mem) X u j cv pcs, length j = 32%nat ->
  pcs <> EL_SITE_END_B -> pcs <> 0xb5420 -> pcs <> EL_SITE_CSTR_B -> pcs <> EL_SITE_SV_B ->
  rw_cells bsegs m u (site_frameB pcs X j cv) -> hcells_okA m u 0 el_hcs_bcast (wsB 0xb5264 X).
Proof.
  intros m X u j cv pcs JL N1 N2 N3 N4 H. unfold site_frameB in H.
  destruct (Z.eqb_spec pcs EL_SITE_END_B); [lia|]. destruct (Z.eqb_spec pcs 0xb5420); [lia|]. destruct (Z.eqb_spec pcs EL_SITE_CSTR_B); [lia|]. destruct (Z.eqb_spec pcs EL_SITE_SV_B); [lia|].
  cbn [app] in H. replace u with (u + 0) in H by lia. peel H P0 u 32.
  change (C8 (Z_to_bv 64 (lf_F X + 32)) :: C8 (Z_to_bv 64 (shad (lf_F X))) :: C8 (Z_to_bv 64 (lf_F X)) :: C8 (Z_to_bv 64 (lf_S1 X)) :: C8 (Z_to_bv 64 (lf_usp X)) :: [C8 (Z_to_bv 64 0xb2400)])
    with (lftoi_savedB X ++ [C8 (Z_to_bv 64 0xb2400)]) in H.
  unfold el_hcs_bcast, wsB. cbn [Z.eqb Pos.eqb]. exact (hcells_kindB m X u 32 0xb2400 H ltac:(lia)).
Qed.

Lemma hcells_beginB : forall (m : mem) X u j cv, rw_cells bsegs m u (site_frameB 0xb5420 X j cv) -> hcells_okA m u 0 el_hcs_bbegin (wsB 0xb548c X).
Proof.
  intros m X u j cv H. unfold site_frameB, EL_SITE_END_B in H. cbn [Z.eqb Pos.eqb] in H. replace u with (u + 0) in H by lia.
  unfold el_hcs_bbegin, wsB. cbn [Z.eqb Pos.eqb]. exact (hcells_kindB m X u 0 0xb23cc H ltac:(lia)).
Qed.
Lemma hcells_cstrB : forall (m : mem) X u j cv, rw_cells bsegs m u (site_frameB EL_SITE_CSTR_B X j cv) -> hcells_okA m u 0 el_hcs_bcstr (wsB 0xb83c0 X).
Proof.
  intros m X u j cv H. unfold site_frameB, EL_SITE_END_B, EL_SITE_CSTR_B in H. cbn [Z.eqb Pos.eqb] in H. replace u with (u + 0) in H by lia.
  unfold el_hcs_bcstr, wsB. cbn [Z.eqb Pos.eqb]. exact (hcells_kindB m X u 0 0xb2400 H ltac:(lia)).
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

  Lemma rgs_s2B : forall pcs X s0 s2 s3, pcs <> EL_SITE_END_B -> lfA_ok X -> site_regsB pcs (lf_S1 X - site_fszB pcs) s0 s2 s3 -> RGS_s2 (lf_S1 X - site_fszB pcs) s0 s2 s3.
  Proof.
    intros pcs X s0 s2 s3 NE LK RG. unfold site_regsB in RG. destruct (Z.eqb_spec pcs EL_SITE_END_B); [lia|].
    pose proof LK as [(SPR & _) (SPT & _) (LLO & LOR) _ _].
    assert (FZ : 0 <= site_fszB pcs <= 144) by (unfold site_fszB; destruct (pcs =? EL_SITE_END_B); [lia|]; destruct ((pcs =? EL_SITE_CSTR_B) || (pcs =? 0xb5420)); lia).
    unfold RGS_s2. split; [exact RG|]. clear - SPR SPT LLO LOR FZ. ul.
  Qed.
  Lemma rgs_endB : forall X s0 s2 s3, lfA_ok X -> site_regsB EL_SITE_END_B (lf_S1 X - site_fszB EL_SITE_END_B) s0 s2 s3 -> RGS_b8570 (lf_S1 X - site_fszB EL_SITE_END_B) s0 s2 s3.
  Proof.
    intros X s0 s2 s3 LK RG. unfold site_regsB, site_fszB in *. rewrite Z.eqb_refl in *. destruct RG as (R0 & R2 & R3).
    pose proof LK as [(SPR & SPA') (SPT & _) (LLO & LOR) _ _].
    unfold RGS_b8570. split; [exact R0|]. split; [exact R2|]. split; [exact R3|]. clear - SPR SPA' SPT LLO LOR. unfold FUZZ_STACK, USTACK_TOP in *.
    split; [lia|]. split; [lia|]. Z.div_mod_to_equations. lia.
  Qed.

  Local Ltac inst pcs RA XP RGS RAW HFR HRG :=
    apply (throw_site_genB RT AF WIN PMc _ pcs RA XP RGS (fun FDO MST => RAW RT AF RC ALC WIN PMc FDO MST XROW));
    [clear; lia| unfold kd_ok; tauto| reflexivity| HFR| HRG].

  Lemma TS_b53f8 : throw_siteB RT PMc (ARTW RT WIN) 23 0xb5420.
  Proof using AF RC ALC XROW.
    inst 0xb5420 0xb548c XP_none RGS_s2 site_rawB_b53f8
      ltac:(intros X j cv m LK JL CV FR; split; [exact (hcells_beginB m X _ j cv FR)| exact I])
      ltac:(intros X s0 s2 s3 LK RG; exact (rgs_s2B 0xb5420 X s0 s2 s3 ltac:(unfold EL_SITE_END_B; lia) LK RG)).
  Qed.
  Lemma TS_cstr : throw_siteB RT PMc (ARTW RT WIN) 22 EL_SITE_CSTR_B.
  Proof using AF RC ALC XROW.
    inst EL_SITE_CSTR_B 0xb83c0 XP_none RGS_s2 site_rawB_b832c
      ltac:(intros X j cv m LK JL CV FR; split; [exact (hcells_cstrB m X _ j cv FR)| exact I])
      ltac:(intros X s0 s2 s3 LK RG; exact (rgs_s2B EL_SITE_CSTR_B X s0 s2 s3 ltac:(unfold EL_SITE_END_B, EL_SITE_CSTR_B; lia) LK RG)).
  Qed.
  Lemma TS_end : throw_siteB RT PMc (ARTW RT WIN) 24 EL_SITE_END_B.
  Proof using AF RC ALC XROW.
    inst EL_SITE_END_B 0xb8614 XP_b8570 RGS_b8570 site_rawB_b8570
      ltac:(intros X j cv m LK JL CV FR; destruct (hcells_endB m X _ j cv JL FR) as [H1 H2]; split; [exact H1| exists cv; split; [exact H2| unfold site_cvB in CV; cbn in CV; lia]])
      ltac:(intros X s0 s2 s3 LK RG; exact (rgs_endB X s0 s2 s3 LK RG)).
  Qed.
  Lemma TS_sv : throw_siteB RT PMc (ARTW RT WIN) 22 EL_SITE_SV_B.
  Proof using AF RC ALC XROW.
    inst EL_SITE_SV_B 0xb5264 XP_b4e2c RGS_s2 site_rawB_b4e2c
      ltac:(intros X j cv m LK JL CV FR; destruct (hcells_svB m X _ j cv JL FR) as [H1 H2]; split; [exact H1| exists cv; split; [exact H2| unfold site_cvB in CV; cbn in CV; lia]])
      ltac:(intros X s0 s2 s3 LK RG; exact (rgs_s2B EL_SITE_SV_B X s0 s2 s3 ltac:(unfold EL_SITE_END_B, EL_SITE_SV_B; lia) LK RG)).
  Qed.
  Local Ltac inst_cast pcs RAW :=
    inst pcs 0xb5264 XP_none RGS_s2 RAW
      ltac:(intros X j cv m LK JL CV FR; split; [exact (hcells_castB m X _ j cv pcs JL ltac:(unfold EL_SITE_END_B; lia) ltac:(lia) ltac:(unfold EL_SITE_CSTR_B; lia) ltac:(unfold EL_SITE_SV_B; lia) FR)| exact I])
      ltac:(intros X s0 s2 s3 LK RG; exact (rgs_s2B pcs X s0 s2 s3 ltac:(unfold EL_SITE_END_B; lia) LK RG)).
  Lemma TS_b4d9c : throw_siteB RT PMc (ARTW RT WIN) 22 0xb4dc4.  Proof using AF RC ALC XROW. inst_cast 0xb4dc4 site_rawB_b4d9c. Qed.
  Lemma TS_b4ec4 : throw_siteB RT PMc (ARTW RT WIN) 22 0xb4eec.  Proof using AF RC ALC XROW. inst_cast 0xb4eec site_rawB_b4ec4. Qed.
  Lemma TS_b4f50 : throw_siteB RT PMc (ARTW RT WIN) 22 0xb4f78.  Proof using AF RC ALC XROW. inst_cast 0xb4f78 site_rawB_b4f50. Qed.
  Lemma TS_b5018 : throw_siteB RT PMc (ARTW RT WIN) 22 0xb5040.  Proof using AF RC ALC XROW. inst_cast 0xb5040 site_rawB_b5018. Qed.
  Lemma TS_b50a8 : throw_siteB RT PMc (ARTW RT WIN) 22 0xb50d0.  Proof using AF RC ALC XROW. inst_cast 0xb50d0 site_rawB_b50a8. Qed.
  Lemma TS_b51d0 : throw_siteB RT PMc (ARTW RT WIN) 22 0xb51f8.  Proof using AF RC ALC XROW. inst_cast 0xb51f8 site_rawB_b51d0. Qed.

  Theorem throw_site23B : throw_siteB RT PMc (ARTW RT WIN) 23 0xb5420.
  Proof using AF RC ALC XROW. exact TS_b53f8. Qed.
  Theorem throw_site24B : throw_siteB RT PMc (ARTW RT WIN) 24 EL_SITE_END_B.
  Proof using AF RC ALC XROW. exact TS_end. Qed.
  Theorem throw_site22B : forall pcs, throw_siteB RT PMc (ARTW RT WIN) 22 pcs.
  Proof using AF RC ALC XROW.
    intros pcs. unfold throw_siteB. intros Σ K X E sel idx jr jos t j cv ra gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m IN.
    generalize IN. revert Σ K X E sel idx jr jos t j cv ra gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
    cbn [el_site_pcsB Z.eqb Pos.eqb] in IN.
    destruct IN as [<- |[<- |[<- |[<- |[<- |[<- |[<- |[<- |[]]]]]]]]];
      [exact TS_b4d9c| exact TS_sv| exact TS_b4ec4| exact TS_b4f50| exact TS_b5018| exact TS_b50a8| exact TS_b51d0| exact TS_cstr].
  Qed.
End SitesXB.
