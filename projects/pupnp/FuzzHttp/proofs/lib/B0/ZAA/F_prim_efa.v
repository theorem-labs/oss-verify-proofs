(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame ITree.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.LZ Require Import ITreeLZ NodesLZ.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import STRW_tac STRW_merge Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts AllocA0 ATac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAA Require Import AEnv ADepot ALayout APrim ATacA ACells LJ PEnv F_poison F_mm_D F_prim_L0 APrimSpec APrimLem AFrame.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Definition efa_entry := 0x364fc%Z.

Lemma land_alignK : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709289472 = x - x mod 262144.
Proof.
  intros x Hx.
  assert (D : x = Z.lor (Z.shiftl (Z.shiftr x 18) 18) (x mod 2^18)).
  { rewrite <- Z.ldiff_ones_r by lia. rewrite <- Z.land_ones by lia. symmetry. apply Z.lor_ldiff_and. }
  rewrite D at 1. rewrite zb_land_lor_distr_l.
  replace (Z.land (x mod 2^18) 18446744073709289472) with 0.
  2:{ symmetry. change 18446744073709289472 with (70368744177663 * 2^18).
      rewrite Z.land_comm. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
      destruct (Z.lt_ge_cases n 18) as [LT|GE].
      - rewrite Z.mul_pow2_bits_low by lia. reflexivity.
      - replace (Z.testbit (x mod 2^18) n) with false; [apply Bool.andb_false_r|].
        symmetry. pose proof (Z.mod_pos_bound x (2^18) ltac:(lia)) as B.
        destruct (Z.eq_dec (x mod 2^18) 0) as [E|NZ]; [rewrite E; apply Z.bits_0|].
        apply Z.bits_above_log2; [lia|]. apply (Z.lt_le_trans _ 18); [|lia]. apply Z.log2_lt_pow2; lia. }
  rewrite Z.lor_0_r.
  change 18446744073709289472 with (Z.shiftl (Z.ones 46) 18).
  rewrite <- Z.shiftl_land. rewrite Z.land_ones by lia.
  rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
  rewrite (Z.mod_small (x / 2^18) (2^46)).
  2:{ split. apply Z.div_pos; lia. apply Z.div_lt_upper_bound; lia. }
  change (2^18) with 262144. pose proof (Z.div_mod x 262144). lia.
Qed.

Section EFA.
  Context {HC : HasCeiling}.
  Variables (AL : alayout) (E : penv).
  Hypothesis AO : alayout_ok AL.
  Notation THR := (at_thr (al_thread AL)).

  Variables (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F_ : bvmap 5 word) (fc : bv 32).
  Variables (q lo c total : Z) (k : pclass) (mtx : Z) (m0 : mem) (H : word -> bool).
  Notation RI := (ri_addr AL c).
  Notation FA := (fa_base AL c).
  Notation k' := (ensure_fa k total).

  Definition efa_W : list (Z * Z) :=
    [(lo, q); (RI + 24, RI + 32); (FA + p_mfa k, FA + p_mfa k + (efa_new k total - p_mfa k));
     (sh (FA + p_mfa k), sh (FA + p_mfa k) + (efa_new k total - p_mfa k) / 8);
     (swlo (FA + p_mfa k), swhi (FA + p_mfa k) (efa_new k total - p_mfa k)); (THR + TSTATS_OFF, THR + TSTATS_OFF + 368)].

  Definition efa_post (j8 j64 j88 j96 j104 j112 : word) (jpad : list byte) : unit -> (word -> bool) -> machine_state -> Prop :=
    fun _ H' ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x28 x29 x30 x31 m',
      ms' = MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
               F_ (ret_pc ra) fc None m' (seg_rom asegs)
      /\ H' = H_efa AL c k total H
      /\ munch [(lo, q); (RI + 24, RI + 32); (FA + p_mfa k, FA + p_mfa k + (efa_new k total - p_mfa k));
                (sh (FA + p_mfa k), sh (FA + p_mfa k) + (efa_new k total - p_mfa k) / 8);
                (swlo (FA + p_mfa k), swhi (FA + p_mfa k) (efa_new k total - p_mfa k)); (THR + TSTATS_OFF, THR + TSTATS_OFF + 368)] m0 m'
      /\ wmono asegs m0 m' /\ mem_inv asegs m'
      /\ stk asegs m' lo q /\ poison_env E m' /\ thread_env (al_thread AL) m' /\ prim_env AL m' /\ shvis H' m'
      /\ rw_cells asegs m' RI (ri_cells mtx k' j8 j64 j88 j96 j104 j112 jpad)
      /\ fa_rep AL m' c k'
      /\ (exists ts, rw_cells asegs m' (THR + TSTATS_OFF) [CB 368 ts]).

  #[using="AO"] Lemma efa_spec : forall (t0 t1 t2 a4 a5 a6 a7 : word) (j8 j64 j88 j96 j104 j112 : word) (jpad : list byte),
    mem_inv asegs m0 -> mclean H m0 -> shvis H m0 -> poison_env E m0 -> thread_env (al_thread AL) m0 -> prim_env AL m0 ->
    stk asegs m0 lo q -> 0x10007fff8000 <= lo -> alloc_ceiling <= lo -> lo <= q - 48 - 400 -> q <= 2^47 -> q mod 16 = 0 ->
    1 <= c <= 31 -> 0 <= total -> 4 * total <= K_FA_SIZE ->
    p_nf k = Z.of_nat (length (p_fa k)) -> 4 * p_nf k <= p_mfa k -> 0 <= p_mfa k <= K_FA_SIZE -> p_mfa k mod K_MAP = 0 ->
    rw_cells asegs m0 RI (ri_cells mtx k j8 j64 j88 j96 j104 j112 jpad) -> fa_rep AL m0 c k ->
    (exists ts, rw_cells asegs m0 (THR + TSTATS_OFF) [CB 368 ts]) ->
    implA H (t_efa AL c k total) (efa_post j8 j64 j88 j96 j104 j112 jpad)
      (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz INSTANCE) (wz RI) (wz (region AL c)) (wz total) a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz efa_entry) fc None m0 (seg_rom asegs)).
  Proof.
    intros t0 t1 t2 a4 a5 a6 a7 j8 j64 j88 j96 j104 j112 jpad MI MC SV PE TE PRE ST LOH CLO LO QH AL16 Hc T0 TB Lnf NF4 MFA MFAM RIC FAR TS.
    unfold efa_entry. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    layout_facts AO 0%nat SPF. layout_facts AO 3%nat THF.
    destruct SPF as (SP1 & SP2 & SP3 & _ & SP5 & _ & _). destruct THF as (TH1 & TH2 & _ & _ & TH5 & _ & _).
    pose proof AO as AO'. destruct AO' as (_ & _ & SPAL & TLO & _ & _).
    pose proof (region_range AL c Hc) as RR.
    assert (Hreg : region AL c = al_space AL + c * K_REGION) by reflexivity.
    assert (Hfa : fa_base AL c = region AL c + FA_OFF) by reflexivity.
    layout_apart_fact AO 0%nat 3%nat AP03.
    unfold ri_cells in RIC. unfold ri_addr, RIB in *. unfold prim_env in PRE.
    destruct FAR as (ws & FAA & LEN & FX). destruct TS as (ts & TS).
    demod SP3. demod SPAL. demod MFAM. demod AL16.
    pose proof (munch_refl [(lo, q)] m0) as MU. pose proof (wmono_refl asegs m0) as WM.
    set (ria := al_space AL + K_SPACE + 128 * c) in *. assert (Hria : ria = al_space AL + K_SPACE + 128 * c) by reflexivity. clearbody ria.
    assert (Eq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
    rewrite <- Eq in ST. carve_frame 48%nat ST. rewrite !Eq in *. clear Eq.
    lz_go.
    do 6 sstep.
    zstep.
    zstep. zstep.
    replace (Z.shiftl total 2) with (4 * total) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    zstep. if_cases KB; zify_cond KB.
    -
      assert (LEB : (4 * total <=? p_mfa k) = true) by (apply Z.leb_le; lia).
      do 8 zstep. release_frame FR ST q.
      replace (t_efa AL c k total) with t_none.
      2:{ unfold t_efa, t_opt, efa_new. rewrite LEB, Z.eqb_refl; reflexivity. }
      lz_ret. unfold efa_post. finish.
      + unfold H_efa, H_opt, efa_new. rewrite LEB, Z.eqb_refl. reflexivity.
      + unfold efa_new, ri_addr, RIB. rewrite LEB. eapply munch_weaken; [| eassumption]. unfold sub_fp; cbn [outside]; intros; lia.
      + eapply poison_env_frame; [exact PE| eassumption| eassumption| env_clear].
      + eapply thread_env_frame; [exact TE| eassumption| eassumption|].
        pose proof TLO as TL. unfold thread_layout_ok in TL. destruct TL as (CX1 & CX2 & _ & _ & CXT & _). env_clear.
      + eapply shvis_wmono; [exact SV| assumption].
      + unfold ensure_fa, efa_new, ri_addr, RIB, ri_cells. rewrite LEB. cbn [p_nf p_mfa p_au p_mu p_nalloc p_nfreed]. rewrite <- Hria. exact RIC.
      + unfold fa_rep, ensure_fa, efa_new. rewrite LEB. cbn [p_mfa p_fa]. exists ws. split; [exact FAA| split; [exact LEN| exact FX]].
      + eexists. exact TS.
    -
      assert (LEB : (4 * total <=? p_mfa k) = false) by (apply Z.leb_gt; lia).
      pose proof (rup_ge (4 * total) K_MAP ltac:(lia)) as RG. pose proof (rup_mod (4 * total) K_MAP ltac:(lia)) as RM.
      pose proof (rup_le (4 * total) K_FA_SIZE K_MAP ltac:(lia) TB ltac:(reflexivity)) as RL.
      set (nm := rup (4 * total) K_MAP) in *. assert (Hnm : nm = rup (4 * total) K_MAP) by reflexivity. clearbody nm.
      set (beg := fa_base AL c + p_mfa k). set (size := nm - p_mfa k).
      assert (Hbeg : beg = fa_base AL c + p_mfa k) by reflexivity. assert (Hsize : size = nm - p_mfa k) by reflexivity.
      clearbody beg size.
      demod RM.
      assert (B8a : beg mod 4096 = 0) by lia. assert (B8b : size mod 4096 = 0) by lia. demod B8a. demod B8b.
      assert (SHE : sh (beg + size) = sh beg + size / 8) by (unfold sh; Z.div_mod_to_equations; nia).
      pose proof (sw_bounds beg size ltac:(lia) ltac:(lia)) as SWB. pose proof (sw_range beg size ltac:(lia) ltac:(lia) ltac:(lia)) as SWR.
      destruct SWB as (SW1 & SW2 & _ & _ & SW5 & _).

      set (W2 := [(lo, q); (ria + 24, ria + 32); (beg, beg + size); (sh beg, sh beg + size / 8); (swlo beg, swhi beg size);
                  (at_thr (al_thread AL) + 2800, at_thr (al_thread AL) + 3168)]).
      assert (AI2 : above_img W2) by (subst W2; env_clear).
      assert (TC2 : thread_clear (al_thread AL) W2).
      { subst W2. pose proof TLO as TL. unfold thread_layout_ok in TL. layout_apart_fact AO 0%nat 2%nat AP02.
        clear MU WM RIC PRE FAA TS FR ST MI SV PE TE FX LEN Lnf.
        destruct TL as (CX1 & CX2 & _ & _ & CXT & _). clear AI2.
        env_clear. }
      apply (munch_weaken _ W2) in MU; [| subst W2; unfold sub_fp; cbn [outside]; intros; lia]. subst W2.
      do 5 zstep.
      rewrite land_alignK by lia.
      replace (4 * total + 262143 - (4 * total + 262143) mod 262144) with nm by (rewrite Hnm; unfold rup; Z.div_mod_to_equations; nia).
      do 2 zstep. zstep. if_cases KC; zify_cond KC. { exfalso. lia. }
      zstep.
      do 2 zstep.
      zstep.   zstep.
      replace (p_mfa k + (region AL c + 3758096384)) with beg by lia.
      zstep. if_cases KZ; zify_cond KZ; [| exfalso; lia].
      zstep.   zstep.
      replace (nm - p_mfa k) with size by lia.
      do 4 zstep.
      zstep.
      replace (t_efa AL c k total) with (ebind (t_commit beg size) (fun a : unit => Ret (Ok a))).
      2:{ unfold t_efa, t_opt, efa_new. rewrite LEB, <- Hnm. replace (nm =? p_mfa k) with false by (symmetry; apply Z.eqb_neq; lia).
          cbn [negb]. rewrite <- Hbeg, <- Hsize. apply ebind_ret_r. }
      clear KB KC KZ.
      callA (rar_map_spec E _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (q + -48) lo beg size);
        [ assumption | assumption
        | eapply shvis_wmono; [exact SV| exact WM]
        | eapply poison_env_frame; [exact PE| exact MU| exact WM| exact AI2]
        | exact ST | lia | lia | lia | reflexivity | reflexivity | lia | lia | lia | lia | lia
        | unfold app_mem; right; lia | lia |].
      cbv beta. try clear SWR0; try clear SWB0; try clear SWB.
      match goal with P : stk asegs _ lo _, Z0 : rw_cells asegs _ beg _, Wn : stk asegs _ (swlo beg) _, E0 : poison_env E _, S0 : shvis _ _ |- _ =>
        rename P into ST1; rename Z0 into ZNEW; rename Wn into WIN; rename E0 into PE1; rename S0 into SV1 end.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => pose proof (wmono_refl asegs mX) as WMa end.

      replace beg with (fa_base AL c + 4 * Z.of_nat (length ws)) in ZNEW by lia.
      pose proof (u32arr_extend_zeros _ _ _ size FAA ltac:(lia) ltac:(lia) ZNEW) as FAA2.
      remember (ws ++ repeat (wz 0) (Z.to_nat (size / 4))) as ws2 eqn:Hws2.
      assert (L2 : 4 * Z.of_nat (length ws2) = nm).
      { subst ws2. rewrite length_app, repeat_length, Nat2Z.inj_add, Z2Nat.id by lia. Z.div_mod_to_equations. lia. }
      clear FAA ZNEW.
      zstep. if_cases K0; zify_cond K0. { exfalso. lia. } clear K0.
      zstep.
      zstep. if_cases K1; zify_cond K1. { exfalso. lia. } clear K1.
      do 3 zstep.
      zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
        destruct (stk_mid_chunk mX (swlo beg) (swhi beg size) (sh beg) (Z.to_nat (size / 8)) WIN ltac:(lia) ltac:(lia)) as [sj SHC] end.
      clear WIN.
      call (poison_shadow_spec E _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (q + -48) lo beg size 250);
        [ assumption | lia | unfold poison_range; lia | exact PE1 | exact ST1 | lia | exact SHC |].
      match goal with P : stk asegs _ lo _, E0 : poison_env E _ |- _ => rename P into ST2; rename E0 into PE2 end.
      zstep.
      call (gcts_spec (al_thread AL) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (q + -48) _ lo);
        [ exact ST2 | lia | lia | lia | lia
        | eapply thread_env_frame; [exact TE| exact MU| exact WM| exact TC2]
        | exact TLO | assumption |].
      match goal with P : stk asegs _ lo _ |- _ => rename P into ST3 end.
      zstep.   zstep.
      zstep. zstep.
      zstep. zstep.
      zstep.
      zstep.
      zstep.
      do 8 zstep. release_frame FR ST3 q.
      lz_ret. unfold efa_post. finish.
      all: first [ solve [ lazymatch goal with
        | |- _ = H_efa _ _ _ _ _ =>
            unfold H_efa, H_opt, H_commit, efa_new; rewrite LEB, <- ?Hnm; replace (nm =? p_mfa k) with false by (symmetry; apply Z.eqb_neq; lia);
            cbn [negb]; rewrite <- ?Hsize, <- ?Hbeg; reflexivity
        | |- munch _ _ _ =>
            unfold efa_new, ri_addr, RIB; rewrite LEB; rewrite <- ?Hnm, <- ?Hsize, <- ?Hbeg, <- ?Hria;
            eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros; lia
        | |- poison_env _ _ => eapply poison_env_frame; [exact PE| exact MU| exact WM| exact AI2]
        | |- thread_env _ _ => eapply thread_env_frame; [exact TE| exact MU| exact WM| exact TC2]
        | |- shvis _ _ => eapply shvis_wmono; [exact SV1| exact WMa]
        | |- rw_cells _ _ _ (ri_cells _ _ _ _ _ _ _ _ _) =>
            unfold ensure_fa, efa_new, ri_addr, RIB, ri_cells; rewrite LEB; cbn [p_nf p_mfa p_au p_mu p_nalloc p_nfreed]; rewrite <- ?Hnm, <- ?Hria; exact RIC
        | |- fa_rep _ _ _ _ =>
            unfold fa_rep, ensure_fa, efa_new; rewrite LEB; cbn [p_mfa p_fa]; rewrite <- ?Hnm; exists ws2;
            split; [exact FAA2| split; [exact L2|]]; subst ws2; rewrite firstn_app_le by lia; exact FX
        | |- ex _ => eapply rw_cells_ex_CB; [exact TS| reflexivity]
        end ] | match goal with |- ?G => idtac "LEFTOVER" G end ].
  Qed.
End EFA.
