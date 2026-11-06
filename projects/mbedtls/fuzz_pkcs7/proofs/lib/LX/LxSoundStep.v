(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith PArith NArith List Bool Lia.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec MState Mem Cells Step Frame Exec Arr.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtA AShadow.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxExpr LxDec LxMem LxStep LxRun LxDenot LxSoundExpr LxSoundDec LxSoundMem.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section LXH.
Context {lxHT : lx_hints}.

Section StepSound.
  Variable segs : list Segment.
  Variable G : gl.
  Variable C : lxcfg.

  Notation L := (g_L G).
  Notation CS := (g_CS G).
  Notation F := (g_F G).
  Notation fc := (g_fc G).
  Notation m0 := (g_m0 G).
  Notation ro := (seg_rom segs).

  (* [comment removed for export] *)
  Definition INV (E : env) (ss : sstate) (m : mem) : Prop :=
    Forall (mfact_ok segs L CS E m) (s_mf ss)
    /\ Forall (pfact_ok CS E) (s_pf ss)
    /\ munch (wden E (s_W ss)) (refm E ss) m /\ wmono segs (refm E ss) m /\ mem_inv segs m
    /\ (s_same ss = true -> m = g_me G).

  Lemma st_ok_INV : forall E ss ms, st_ok segs G E ss ms <-> exists m, ms = ms_den segs G E ss m /\ INV E ss m.
  Proof. intros E ss ms. unfold st_ok, INV. split; intros (m & H); exists m; tauto. Qed.

  (* [comment removed for export] *)
  Lemma same_gone : forall (P : Prop), false = true -> P.
  Proof. intros P H. discriminate. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Section WithEnv.
    Variable E : env.
    Hypothesis CFG : cfg_ok G C E.

    Lemma cfg_some : forall A, c_acc C = Some A ->
      cs_ok L CS /\ al_wf L /\
      (zdenp E (ac_sb A) = al_sb L /\ ac_img_lo A = al_img_lo L /\ ac_img_hi A = al_img_hi L
       /\ ac_got A = al_got L /\ ac_gsb A = al_gsb L).
    Proof. intros A H. pose proof CFG as X. unfold cfg_ok in X. rewrite H in X. exact X. Qed.
    Lemma cfg_none : c_acc C = None -> forall x, CS x.
    Proof. intros H. pose proof CFG as X. unfold cfg_ok in X. rewrite H in X. exact X. Qed.
    Lemma cfg_hsb : forall A, c_acc C = Some A -> zdenp E (ac_sb A) = al_sb L.
    Proof. intros A H. exact (proj1 (proj2 (proj2 (cfg_some A H)))). Qed.
    Lemma cfg_hst : forall A, c_acc C = Some A -> ac_got A = al_got L /\ ac_gsb A = al_gsb L /\ cs_ok L CS.
    Proof. intros A H. destruct (cfg_some A H) as (C1 & _ & _ & _ & _ & G1 & G2). exact (conj G1 (conj G2 C1)). Qed.

    Lemma acc_class_sound : forall ss a w cl,
      Forall (mfact_ok segs L CS E (m0)) (s_mf ss) \/ (exists m, Forall (mfact_ok segs L CS E m) (s_mf ss)) ->
      Forall (pfact_ok CS E) (s_pf ss) ->
      acc_class C ss a w = Some cl -> acls_ok L CS cl (zden E a) w.
    Proof.
      intros ss a w cl HM HP H. unfold acc_class in H.
      destruct (c_acc C) as [A|] eqn:HCA.
      2:{ injection H; intros <-. cbn. intros x _. exact (cfg_none HCA x). }
      destruct (cfg_some A HCA) as (_ & _ & cfg_A).
      assert (HM' : exists m, Forall (mfact_ok segs L CS E m) (s_mf ss)) by (destruct HM as [HM|HM]; [exists m0; exact HM| exact HM]).
      destruct HM' as [m HMm].
      pose proof (cranges_sound segs L CS E m _ _ HP HMm) as CR.
      assert (CL : in_some_crange (s_pf ss) (cranges (s_pf ss) (s_mf ss)) a (ELit w) = true -> acls_ok L CS AcClient (zden E a) w).
      { intros IC. cbn. apply (in_some_crange_sound CS E _ _ _ _ HP CR) in IC. exact IC. }
      (* [comment removed for export] *)
      assert (SHAD : forall x kr, shadow_split (ac_sb A) a = Some (x, kr) ->
                (if Z.eqb w 1 then in_some_crange (s_pf ss) (cranges (s_pf ss) (s_mf ss)) (sh_c x kr) (ELit 1)
                 else N.leb 3 (eal (oracle_of ss) x) && in_some_crange (s_pf ss) (cranges (s_pf ss) (s_mf ss)) (sh_c x kr) (ELit (8 * (w - 1) + 1))) = true ->
                acls_ok L CS AcShadow (zden E a) w).
      { intros x kr SS SHC.
        pose proof (shadow_addr L E A (proj1 cfg_A) a x kr SS) as SA.
        set (c := sh_c x kr) in *.
        assert (SH : forall n, in_some_crange (s_pf ss) (cranges (s_pf ss) (s_mf ss)) c (ELit n) = true ->
                     forall j, 0 <= j -> 8 * j < n -> exists c', CS c' /\ zden E a + j = shadow_of L c').
        { intros n Hn j Hj Hjn. apply (in_some_crange_sound CS E _ _ _ _ HP CR) in Hn. cbn [zden] in Hn.
          exists (zden E c + 8 * j). split; [apply Hn; lia|]. rewrite SA. unfold shadow_of.
          rewrite Z.add_comm with (m := 8 * j) at 1. rewrite Z.mul_comm, Z.div_add_l by lia. lia. }
        cbn. destruct (Z.eqb_spec w 1).
        + intros j Hj. apply (SH 1 SHC); lia.
        + apply andb_prop in SHC as [_ I2]. intros j Hj. apply (SH _ I2); lia. }
      destruct (is_lit a) as [z|] eqn:LA.
      - pose proof (is_lit_den E _ _ LA) as LA'. destruct cfg_A as (HSB0 & E1 & E2 & _).
        destruct (Z.leb_spec (ac_img_lo A) z); [destruct (Z.leb_spec (z + w) (ac_img_hi A))|]; cbn [andb] in H.
        + injection H; intros <-. cbn. rewrite LA'. lia.
        + destruct (in_some_crange (s_pf ss) (cranges (s_pf ss) (s_mf ss)) a (ELit w)) eqn:IC; [injection H; intros <-; apply CL; first [exact IC | reflexivity]|].
          destruct (shadow_split (ac_sb A) a) as [[x kr]|] eqn:SS; [|discriminate].
          match type of H with (if ?cnd then _ else _) = _ => destruct cnd eqn:SHC; [|discriminate] end. injection H; intros <-. exact (SHAD x kr eq_refl SHC).
        + destruct (in_some_crange (s_pf ss) (cranges (s_pf ss) (s_mf ss)) a (ELit w)) eqn:IC; [injection H; intros <-; apply CL; first [exact IC | reflexivity]|].
          destruct (shadow_split (ac_sb A) a) as [[x kr]|] eqn:SS; [|discriminate].
          match type of H with (if ?cnd then _ else _) = _ => destruct cnd eqn:SHC; [|discriminate] end. injection H; intros <-. exact (SHAD x kr eq_refl SHC).
      - assert (CI : acc_client_img A ss (cranges (s_pf ss) (s_mf ss)) a w = Some cl -> acls_ok L CS cl (zden E a) w).
        { unfold acc_client_img. intros HC.
          destruct (in_some_crange (s_pf ss) (cranges (s_pf ss) (s_mf ss)) a (ELit w)) eqn:IC.
          { injection HC; intros <-. apply CL; first [exact IC | reflexivity]. }
          destruct (e_in (oracle_of ss) a (ac_img_lo A) (ac_img_hi A - w)) eqn:EI; [|discriminate]. injection HC; intros <-.
          apply (e_in_sound E) in EI; [|exact (mk_oracle_sound CS E _ HP)]. destruct cfg_A as (_ & E1 & E2 & _). cbn. lia. }
        destruct (shadow_split (ac_sb A) a) as [[x kr]|] eqn:SS; [|exact (CI H)].
        match type of H with (if ?cnd then _ else _) = _ => destruct cnd eqn:SHC; [|exact (CI H)] end.
        injection H; intros <-. exact (SHAD x kr eq_refl SHC).
    Qed.

    Lemma acls_acc_ok : forall cl a (w : N),
      okw w = true -> acls_ok L CS cl a (Z.of_N w) -> acc_ok L CS [(Z_to_bv 64 a, N.to_nat w)].
    Proof.
      intros cl a w OKW H. destruct (c_acc C) as [A|] eqn:HCA.
      2:{ intros z _. left. exact (cfg_none HCA z). }
      destruct (cfg_some A HCA) as (CSOK & WF & _). pose proof CSOK as (C1 & C2 & C3 & C4). unfold al_wf in WF.
      assert (Wpos : 0 < Z.of_N w) by (destruct (okw_cases w OKW) as [-> |[-> |[-> | ->]]]; lia).
      assert (R : 0 <= a < 2 ^ 64).
      { destruct cl; cbn in H.
        - destruct (C1 a (H a ltac:(lia))); lia.
        - destruct (H 0 ltac:(lia)) as (c & Hc & Ha). destruct (C1 c Hc) as (_ & S1 & S2 & _). lia.
        - lia. }
      intros z (a' & n' & Hin & Hz). destruct Hin as [E1|[]]. injection E1; intros <- <-.
      rewrite Z_to_bv_unsigned in Hz. unfold bv_wrap, bv_modulus in Hz. cbn [Z.of_N] in Hz. rewrite Z.mod_small in Hz by lia.
      destruct cl; cbn in H.
      - left. apply H. lia.
      - right; left. destruct (H (z - a) ltac:(lia)) as (c & Hc & Hzc). exists c. split; [exact Hc| lia].
      - right; right. lia.
    Qed.
  End WithEnv.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma rd_reg_rsget : forall ss k, rd_reg ss k = rsget (s_rs ss) k.
  Proof. reflexivity. Qed.

  Lemma rget_den : forall E ss (r : bv 5) pcw,
    length (s_rs ss) = 31%nat ->
    rget (Core (regs_den E (s_rs ss)) F pcw fc None) r = Z_to_bv 64 (zden E (rd_expr ss (bv_unsigned r))).
  Proof.
    intros E ss r pcw Hlen. unfold rget, is_x0. cbn [c_regs].
    rewrite (regs_den_get E (s_rs ss) r Hlen). unfold rd_expr, rd_reg, rsget.
    destruct (Z.eqb_spec (bv_unsigned r) 0); [reflexivity|].
    rewrite expr_of_reg_den. reflexivity.
  Qed.

  Lemma wr_reg_len : forall ss k v, length (s_rs (wr_reg ss k v)) = length (s_rs ss).
  Proof. intros. unfold wr_reg. destruct (Z.eqb k 0); [reflexivity|]. cbn. apply lset_length. Qed.

  Lemma rset_den : forall E ss (rd : bv 5) v vr pcw pcw' mm rr,
    length (s_rs ss) = 31%nat -> rden E vr = v ->
    MS_of_core (rset rd v (with_pc pcw' (Core (regs_den E (s_rs ss)) F pcw fc None))) mm rr =
    MS (regs_den E (s_rs (wr_reg ss (bv_unsigned rd) vr))) F pcw' fc None mm rr.
  Proof.
    intros E ss rd v vr pcw pcw' mm rr Hlen Hv. unfold rset, is_x0, wr_reg, MS_of_core, with_regs, with_pc.
    destruct (Z.eqb_spec (bv_unsigned rd) 0); cbn; [reflexivity|].
    rewrite <- Hv. rewrite (regs_den_set E (s_rs ss) rd vr Hlen ltac:(assumption)). reflexivity.
  Qed.
  Lemma kden_eq : forall x y, kden KEq x y = bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y).
  Proof. intros. unfold bv_eqb, kden, zlow. rewrite !Z_to_bv_unsigned. reflexivity. Qed.
  Lemma kden_ltu : forall x y, kden KLtu x y = bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y).
  Proof. intros. unfold bv_ltu, kden, zlow. rewrite !Z_to_bv_unsigned. reflexivity. Qed.
  Lemma swrap64 : forall x, bv_swrap 64 (bv_wrap 64 x) = zswrap 64 x.
  Proof.
    intros x. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus, zswrap.
    change (2 ^ Z.of_N 64 `div` 2) with (2 ^ (64 - 1)). change (2 ^ Z.of_N 64) with (2 ^ 64).
    rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia). reflexivity.
  Qed.
  Lemma kden_lts : forall x y, kden KLts x y = bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y).
  Proof. intros. unfold bv_lts, kden, bv_signed. rewrite !Z_to_bv_unsigned, !swrap64. reflexivity. Qed.

  Lemma branch_taken_den : forall bc x y n k,
    ckind_of bc = (n, k) -> branch_taken bc (Z_to_bv 64 x) (Z_to_bv 64 y) = xorb n (kden k x y).
  Proof.
    intros bc x y n k H. destruct bc; cbn in H; injection H; intros <- <-; cbn [branch_taken xorb];
      rewrite ?kden_eq, ?kden_ltu, ?kden_lts; try reflexivity; destruct (bv_eqb _ _) || destruct (bv_ltu _ _) || destruct (bv_lts _ _); reflexivity.
  Qed.

  Section Env2.
    Variable E : env.
    Hypothesis CFG : cfg_ok G C E.

    Lemma shb_lookup_In : forall pf v c oa on, shb_lookup pf v = Some (c, oa, on) -> In (FShb v c oa on) pf.
    Proof.
      induction pf as [|f pf IH]; intros v c oa on H; cbn in H; [discriminate|].
      destruct f; try (right; apply IH; exact H).
      destruct (Pos.eqb_spec v k); [injection H; intros <- <- <-; subst; left; reflexivity| right; apply IH; exact H].
    Qed.

    Lemma shadow_slow_sound : forall pf a b,
      Forall (pfact_ok CS E) pf -> shadow_slow pf a b = true -> kden KLts (zden E a) (zden E b) = true.
    Proof.
      intros pf a b HP H. unfold shadow_slow in H.
      pose proof (lin_of_den E b) as LB. pose proof (lin_of_den E a) as LA.
      destruct (lin_of b) as [tb cb]. cbn [fst snd] in LB.
      destruct tb as [|[kb eb] tb']; [discriminate|]. destruct kb as [|pk|]; try discriminate. destruct pk; try discriminate.
      destruct eb as [|v| | | |]; try discriminate. destruct tb'; [|discriminate]. destruct cb; try discriminate.
      destruct (shb_lookup pf v) as [[[c oa] on]|] eqn:SL; [|discriminate].
      destruct (lin_of a) as [ta da]. cbn [fst snd] in LA.
      pose proof (shb_lookup_In _ _ _ _ _ SL) as IN.
      destruct ta as [|[ka ea] ta'].
      { (* [comment removed for export] *)
        apply andb_prop in H as [H DI]. apply andb_prop in H as [D0 K1]. apply Z.leb_le in D0.
        apply (dec_le_sound CS E _ _ _ HP) in K1. apply (dec_inside_sound CS E _ _ _ _ _ HP) in DI. cbn [zden] in K1, DI.
        cbn [tden] in LA, LB. rewrite List.Forall_forall in HP. specialize (HP _ IN). cbn -[Z.pow] in HP. rewrite !zdenp_ok in HP.
        cbn [zden opden] in LB. assert (Hb : zden E b = ez E v) by lia. rewrite Hb in *.
        specialize (HP (da + 1) ltac:(lia) ltac:(lia) ltac:(lia)).
        pose proof (Z.mod_pos_bound (zden E c) 8 ltac:(lia)).
        cbn [kden]. rewrite !zswrap_small by lia. apply Z.ltb_lt. lia. }
      destruct ka as [|pk|]; try discriminate. destruct pk; try discriminate.
      destruct ea as [| | | | |o c' m7]; try discriminate. destruct o; try discriminate.
      destruct m7 as [z7| | | | |]; try discriminate. destruct z7 as [|p|]; try discriminate.
      do 3 (destruct p as [p|p|]; try discriminate). destruct ta'; [|discriminate].
      apply andb_prop in H as [H DI]. apply andb_prop in H as [H K1]. apply andb_prop in H as [D0 EQ].
      apply expr_eqb_eq in EQ. subst c'. apply Z.leb_le in D0.
      apply (dec_le_sound CS E _ _ _ HP) in K1. apply (dec_inside_sound CS E _ _ _ _ _ HP) in DI. cbn [zden] in K1, DI.
      cbn [tden] in LA, LB.
      rewrite List.Forall_forall in HP. specialize (HP _ IN). cbn -[Z.pow] in HP. rewrite !zdenp_ok in HP.
      cbn [zden opden] in LA, LB. assert (Hb : zden E b = ez E v) by lia. rewrite Hb in *.
      specialize (HP (da + 1) ltac:(lia) ltac:(lia) ltac:(lia)).
      assert (Ha : zden E a = Z.land (zden E c) 7 + da) by lia. rewrite Ha.
      change 7 with (2 ^ 3 - 1) at 1. rewrite land_low_mask by lia.
      pose proof (Z.mod_pos_bound (zden E c) (2 ^ 3) ltac:(lia)). change (2 ^ 3) with 8 in *.
      cbn [kden]. rewrite !zswrap_small by lia. apply Z.ltb_lt. lia.
    Qed.
    Lemma e_win_inj : forall pf a b, Forall (pfact_ok CS E) pf -> e_win (mk_oracle pf) a b = true ->
      zlow 64 (zden E a) = zlow 64 (zden E b) -> zden E a = zden E b.
    Proof.
      intros pf a b HP H EQ. pose proof (mk_oracle_sound CS E pf HP) as HO. unfold e_win, e_s64 in H.
      assert (WIN : exists lo, lo <= zden E a < lo + 2 ^ 64 /\ lo <= zden E b < lo + 2 ^ 64).
      { apply orb_prop in H as [H|H]; apply andb_prop in H as [UA UB];
          (apply (e_in_sound E) in UA; [|exact HO]); (apply (e_in_sound E) in UB; [|exact HO]); unfold two63, two64 in *.
        - exists (- 9223372036854775808). lia.
        - exists 1. lia. }
      destruct WIN as (lo & WA & WB). unfold zlow in EQ.
      pose proof (Z.div_mod (zden E a) (2 ^ 64) ltac:(lia)) as DA. pose proof (Z.mod_pos_bound (zden E a) (2 ^ 64) ltac:(lia)) as RA.
      pose proof (Z.div_mod (zden E b) (2 ^ 64) ltac:(lia)) as DB. pose proof (Z.mod_pos_bound (zden E b) (2 ^ 64) ltac:(lia)) as RB.
      set (qa := zden E a / 2 ^ 64) in *. set (qb := zden E b / 2 ^ 64) in *.
      set (ra' := zden E a mod 2 ^ 64) in *. set (rb := zden E b mod 2 ^ 64) in *.
      change (2 ^ 64) with 18446744073709551616 in *. lia.
    Qed.

    Lemma decide_kind0_sound : forall pf k a b r,
      Forall (pfact_ok CS E) pf -> decide_kind0 (mk_oracle pf) pf k a b = Some r -> kden k (zden E a) (zden E b) = r.
    Proof.
      intros pf k a b r HP H. pose proof (mk_oracle_sound CS E pf HP) as HO. unfold decide_kind0 in H.
      assert (GEN : match k with
           | KEq => if dec_eq pf a b then Some true
                    else if ((e_u64 (mk_oracle pf) a && e_u64 (mk_oracle pf) b) || e_win (mk_oracle pf) a b) && (dec_lt pf a b || dec_lt pf b a) then Some false else None
           | KLtu => if e_u64 (mk_oracle pf) a && e_u64 (mk_oracle pf) b
                     then if dec_lt pf a b then Some true else if dec_le pf b a then Some false else None else None
           | KLts => if shadow_slow pf a b then Some true else
                     if e_s64 (mk_oracle pf) a && e_s64 (mk_oracle pf) b
                     then if dec_lt pf a b then Some true else if dec_le pf b a then Some false else None else None
           end = Some r -> kden k (zden E a) (zden E b) = r).
      { clear H. intros H. destruct k; [| | destruct (shadow_slow pf a b) eqn:SHS; [injection H; intros <-; exact (shadow_slow_sound pf a b HP SHS)|]]; cbn [kden].
        - destruct (dec_eq pf a b) eqn:DE.
          + injection H; intros <-. apply (dec_eq_sound CS E _ _ _ HP) in DE. rewrite DE. apply Z.eqb_refl.
          + match type of H with (if ?c && _ then _ else _) = _ => destruct c eqn:RNG; [|discriminate] end. cbn [andb] in H.
            assert (NE : zden E a <> zden E b -> zlow 64 (zden E a) <> zlow 64 (zden E b)).
            { intros NE. apply orb_prop in RNG as [RNG|RNG]; [apply andb_prop in RNG as [UA UB]|].
              - apply (e_in_sound E) in UA; [|exact HO]. apply (e_in_sound E) in UB; [|exact HO]. unfold two64 in *.
                unfold zlow; rewrite !Z.mod_small by lia. exact NE.
              - intros EQ. apply NE. exact (e_win_inj pf a b HP RNG EQ). }
            destruct (dec_lt pf a b) eqn:D1; [|destruct (dec_lt pf b a) eqn:D2; [|discriminate]]; injection H; intros <-;
              [apply (dec_lt_sound CS E _ _ _ HP) in D1 | apply (dec_lt_sound CS E _ _ _ HP) in D2]; apply Z.eqb_neq; apply NE; lia.
        - destruct (e_u64 (mk_oracle pf) a) eqn:UA; [|discriminate]. destruct (e_u64 (mk_oracle pf) b) eqn:UB; [|discriminate].
          cbn [andb] in H. apply (e_in_sound E) in UA; [|exact HO]. apply (e_in_sound E) in UB; [|exact HO]. unfold two64 in *.
          unfold zlow; rewrite !Z.mod_small by lia.
          destruct (dec_lt pf a b) eqn:D1; [|destruct (dec_le pf b a) eqn:D2; [|discriminate]]; injection H; intros <-.
          + apply (dec_lt_sound CS E _ _ _ HP) in D1. apply Z.ltb_lt. exact D1.
          + apply (dec_le_sound CS E _ _ _ HP) in D2. apply Z.ltb_ge. lia.
        - destruct (e_s64 (mk_oracle pf) a) eqn:UA; [|discriminate]. destruct (e_s64 (mk_oracle pf) b) eqn:UB; [|discriminate].
          cbn [andb] in H. unfold e_s64 in *. apply (e_in_sound E) in UA; [|exact HO]. apply (e_in_sound E) in UB; [|exact HO]. unfold two63 in *.
          rewrite !zswrap_small by lia.
          destruct (dec_lt pf a b) eqn:D1; [|destruct (dec_le pf b a) eqn:D2; [|discriminate]]; injection H; intros <-.
          + apply (dec_lt_sound CS E _ _ _ HP) in D1. apply Z.ltb_lt. exact D1.
          + apply (dec_le_sound CS E _ _ _ HP) in D2. apply Z.ltb_ge. lia. }
      destruct (is_lit a) as [x|] eqn:LA; [destruct (is_lit b) as [y|] eqn:LB|]; try (apply GEN; exact H).
      apply is_lit_den with (E := E) in LA. apply is_lit_den with (E := E) in LB. injection H; intros <-.
      rewrite LA, LB. destruct k; reflexivity.
    Qed.

    Lemma zlow_zlow : forall x, zlow 64 (zlow 64 x) = zlow 64 x.
    Proof. intros x. unfold zlow. apply Z.mod_mod. lia. Qed.

    Lemma zswrap_zswrap : forall k x, zswrap k (zswrap k x) = zswrap k x.
    Proof.
      intros k x. unfold zswrap. f_equal.
      replace ((x + 2 ^ (k - 1)) mod 2 ^ k - 2 ^ (k - 1) + 2 ^ (k - 1)) with ((x + 2 ^ (k - 1)) mod 2 ^ k) by lia.
      destruct (Z.eq_dec (2 ^ k) 0) as [Z0|NZ]; [rewrite Z0, !Zmod_0_r; reflexivity|].
      apply Z.mod_mod. exact NZ.
    Qed.

    Lemma kden_nlit : forall k a b, kden k (zden E (nlit k a)) (zden E (nlit k b)) = kden k (zden E a) (zden E b).
    Proof.
      intros k a b.
      assert (NL : forall e, zden E (nlit k e) = zden E e \/ zden E (nlit k e) = match k with KLts => zswrap 64 (zden E e) | _ => zlow 64 (zden E e) end).
      { intros e. destruct e; cbn [nlit]; [right; reflexivity| left; reflexivity ..]. }
      destruct k; cbn [kden];
        destruct (NL a) as [-> | ->]; destruct (NL b) as [-> | ->]; rewrite ?zlow_zlow, ?zswrap_zswrap; reflexivity.
    Qed.

    Lemma decide_kind_sound : forall pf k a b r,
      Forall (pfact_ok CS E) pf -> decide_kind (mk_oracle pf) pf k a b = Some r -> kden k (zden E a) (zden E b) = r.
    Proof.
      intros pf k a b r HP H. unfold decide_kind in H. rewrite <- kden_nlit. exact (decide_kind0_sound pf k _ _ r HP H).
    Qed.

    Lemma decide_cond_sound : forall pf c r,
      Forall (pfact_ok CS E) pf -> decide_cond (mk_oracle pf) pf c = Some r -> cnden E c = r.
    Proof.
      intros pf [n k a b] r HP H. unfold decide_cond in H. cbn [cnden]. rewrite !zdenp_ok.
      destruct (decide_kind (mk_oracle pf) pf k a b) as [r'|] eqn:DK; [|discriminate]. cbn in H. injection H; intros <-.
      rewrite (decide_kind_sound pf k a b r' HP DK). reflexivity.
    Qed.

    Lemma kind_facts_sound : forall pf k a b,
      Forall (pfact_ok CS E) pf -> Forall (pfact_ok CS E) (kind_facts (mk_oracle pf) k a b (kden k (zden E a) (zden E b))).
    Proof.
      intros pf k a b HP. pose proof (mk_oracle_sound CS E pf HP) as HO. unfold kind_facts.
      destruct k; cbn [kden].
      - do 2 unlazy1. destruct (e_win (mk_oracle pf) a b && negb (e_u64 (mk_oracle pf) a && e_u64 (mk_oracle pf) b)) eqn:SGN.
        + (* [comment removed for export] *)
          apply andb_prop in SGN as [SGN _].
          assert (INJ : zlow 64 (zden E a) = zlow 64 (zden E b) -> zden E a = zden E b) by (apply (e_win_inj pf); assumption).
          destruct (Z.eqb_spec (zlow 64 (zden E a)) (zlow 64 (zden E b))) as [EQ|NE].
          * apply INJ in EQ. repeat (apply List.Forall_cons; [unfold pfact_ok; rewrite !zdenp_ok, ?esub_den; lia|]). apply List.Forall_nil.
          * apply List.Forall_cons; [|apply List.Forall_nil]. unfold pfact_ok. rewrite !zdenp_ok. cbn [zden].
            destruct (Z.lt_trichotomy (zden E a) (zden E b)) as [LT|[EQ|GT]]; [lia| |lia]. exfalso. apply NE. rewrite EQ. reflexivity.
        + destruct (Z.eqb_spec (zlow 64 (zden E a)) (zlow 64 (zden E b)));
            repeat (apply List.Forall_cons; [unfold pfact_ok; rewrite !zdenp_ok, ?esub_den, !elow_den by (try exact HO; lia); cbn [zden]; unfold zlow in *; lia|]);
            apply List.Forall_nil.
      - destruct (Z.ltb_spec (zlow 64 (zden E a)) (zlow 64 (zden E b)));
          repeat (apply List.Forall_cons; [unfold pfact_ok; rewrite !zdenp_ok, ?esub_den, !elow_den by (try exact HO; lia); cbn [zden]; unfold zlow in *; lia|]);
          apply List.Forall_nil.
      - destruct (Z.ltb_spec (zswrap 64 (zden E a)) (zswrap 64 (zden E b)));
          repeat (apply List.Forall_cons; [unfold pfact_ok; rewrite !zdenp_ok, ?esub_den, !esx_den by (try exact HO; lia); cbn [zden]; lia|]);
          apply List.Forall_nil.
    Qed.

    Lemma cond_facts_sound : forall pf c,
      Forall (pfact_ok CS E) pf -> Forall (pfact_ok CS E) (cond_facts (mk_oracle pf) c (cnden E c)).
    Proof.
      intros pf [n k a b] HP. unfold cond_facts. cbn [cnden]. rewrite !zdenp_ok.
      replace (xorb n (xorb n (kden k (zden E a) (zden E b)))) with (kden k (zden E a) (zden E b)) by (destruct n, (kden k _ _); reflexivity).
      apply kind_facts_sound. exact HP.
    Qed.
  End Env2.

  Section Env3.
    Variable E : env.
    Hypothesis CFG : cfg_ok G C E.
    Hypothesis HPF : hp_frame segs (ehp E) (ecw E).   (* [comment removed for export] *)
    Hypothesis HBK : hp_blk (ecw E).                   (* [comment removed for export] *)

    Lemma w64_shl : forall x k, 0 <= k -> bv_shiftl (Z_to_bv 64 x) (Z_to_bv 64 k) = Z_to_bv 64 (x * 2 ^ (Z.land k 63)) \/ k >= 64.
    Proof.
      intros x k Hk. destruct (Z_lt_le_dec k 64); [left|right; lia].
      apply bv_eq. rewrite bv_shiftl_unsigned, !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
      rewrite (Z.mod_small k) by lia. rewrite Z.shiftl_mul_pow2 by lia.
      replace (Z.land k 63) with k.
      2:{ change 63 with (Z.ones 6). rewrite Z.land_ones by lia. rewrite Z.mod_small by lia. reflexivity. }
      rewrite Z.mul_mod_idemp_l by (apply Z.pow_nonzero; lia). reflexivity.
    Qed.

    Lemma alu_sll_lit : forall (u : word) k, 0 <= k ->
      alu64 ALU_SLL u (Z_to_bv 64 k) = bv_shiftl u (Z_to_bv 64 (Z.land k 63)).
    Proof.
      intros u k Hk. cbn -[bv_shiftl bv_and Z_to_bv]. f_equal. rewrite w64_and. f_equal.
    Qed.

    Lemma alu_srl_lit : forall (u : word) k, 0 <= k ->
      alu64 ALU_SRL u (Z_to_bv 64 k) = bv_shiftr u (Z_to_bv 64 (Z.land k 63)).
    Proof.
      intros u k Hk. cbn -[bv_shiftr bv_and Z_to_bv]. f_equal. rewrite w64_and. f_equal.
    Qed.

    Lemma land63_range : forall k, 0 <= Z.land k 63 < 64.
    Proof.
      intros k. change 63 with (Z.ones 6). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound k (2 ^ 6) ltac:(lia)). cbn in *. lia.
    Qed.

    Lemma w64_shl_exact : forall x s, 0 <= s < 64 -> bv_shiftl (Z_to_bv 64 x) (Z_to_bv 64 s) = Z_to_bv 64 (x * 2 ^ s).
    Proof.
      intros x s Hs. apply bv_eq. rewrite bv_shiftl_unsigned, !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
      rewrite (Z.mod_small s) by lia. rewrite Z.shiftl_mul_pow2 by lia.
      rewrite Z.mul_mod_idemp_l by (apply Z.pow_nonzero; lia). reflexivity.
    Qed.

    Lemma w64_shr_exact : forall x s, 0 <= s < 64 -> bv_shiftr (Z_to_bv 64 x) (Z_to_bv 64 s) = Z_to_bv 64 (Z.shiftr (zlow 64 x) s).
    Proof.
      intros x s Hs. apply bv_eq. rewrite bv_shiftr_unsigned, !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus, zlow. cbn [Z.of_N].
      rewrite (Z.mod_small s) by lia. symmetry. apply Z.mod_small.
      pose proof (Z.mod_pos_bound x (2 ^ 64) ltac:(lia)) as R. rewrite Z.shiftr_div_pow2 by lia.
      split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|].
      apply Z.lt_le_trans with (2 ^ 64); [lia|]. rewrite <- (Z.mul_1_l (2 ^ 64)) at 1.
      apply Z.mul_le_mono_nonneg_r; [lia|]. pose proof (Z.pow_pos_nonneg 2 s). lia.
    Qed.

    Lemma slt_val : forall bb : bool, (if bb then Z_to_bv 64 1 else Z_to_bv 64 0 : word) = Z_to_bv 64 (Z.b2z bb).
    Proof. intros [|]; reflexivity. Qed.

    Lemma kind_expr_den : forall O k a b, osound E O -> k <> KEq ->
      zden E (kind_expr O k a b) = Z.b2z (kden k (zden E a) (zden E b)).
    Proof.
      intros O k a b HO Hk. destruct k; [congruence| |]; cbn -[elow esx Z.ltb zlow zswrap].
      - rewrite !elow_den by (try exact HO; lia). unfold zlow. lia.
      - rewrite !esx_den by (try exact HO; lia). lia.
    Qed.

    Lemma alu_slt_den : forall k x y, k <> KEq ->
      alu64 (match k with KLts => ALU_SLT | _ => ALU_SLTU end) (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (Z.b2z (kden k x y)).
    Proof.
      intros k x y Hk. destruct k; [congruence| |]; cbn [alu64 alu]; rewrite <- slt_val; [rewrite <- kden_ltu|rewrite <- kden_lts]; reflexivity.
    Qed.

    Lemma alu_sra_lit : forall (u : word) k, 0 <= k ->
      alu64 ALU_SRA u (Z_to_bv 64 k) = bv_ashiftr u (Z_to_bv 64 (Z.land k 63)).
    Proof.
      intros u k Hk. cbn -[bv_ashiftr bv_and Z_to_bv]. f_equal. rewrite w64_and. f_equal.
    Qed.

    Lemma swrap64_lit : forall x, bv_signed (Z_to_bv 64 x) = zswrap 64 x.
    Proof. intros x. rewrite Z_to_bv_signed, <- (bv_swrap_wrap 64 x). apply swrap64. Qed.

    Lemma w64_ashr_exact : forall x s, 0 <= s < 64 ->
      bv_ashiftr (Z_to_bv 64 x) (Z_to_bv 64 s) = Z_to_bv 64 (Z.shiftr (zswrap 64 x) s).
    Proof.
      intros x s Hs. apply bv_eq. rewrite bv_ashiftr_unsigned, swrap64_lit, !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
      rewrite (Z.mod_small s) by lia. reflexivity.
    Qed.

    Lemma land_ones_mod : forall x j, 0 <= j -> Z.land x (2 ^ j - 1) = x mod 2 ^ j.
    Proof. intros. apply land_low_mask. assumption. Qed.

    (* [comment removed for export] *)
    Lemma w64_shr_sym : forall x y,
      bv_shiftr (Z_to_bv 64 x) (bv_and (Z_to_bv 64 y) (Z_to_bv 64 63)) = Z_to_bv 64 (Z.shiftr (zlow 64 x) (zlow 6 y)).
    Proof.
      intros x y. apply bv_eq. rewrite bv_shiftr_unsigned, w64_and, !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus, zlow. cbn [Z.of_N].
      assert (M : Z.land y 63 mod 2 ^ 64 = y mod 2 ^ 6).
      { change 63 with (2 ^ 6 - 1). rewrite land_ones_mod by lia. apply Z.mod_small. pose proof (Z.mod_pos_bound y (2 ^ 6) ltac:(lia)). lia. }
      rewrite M. symmetry. apply Z.mod_small.
      pose proof (Z.mod_pos_bound x (2 ^ 64) ltac:(lia)) as R. pose proof (Z.mod_pos_bound y (2 ^ 6) ltac:(lia)) as R6.
      rewrite Z.shiftr_div_pow2 by lia.
      split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|].
      apply Z.lt_le_trans with (2 ^ 64); [lia|]. rewrite <- (Z.mul_1_l (2 ^ 64)) at 1.
      apply Z.mul_le_mono_nonneg_r; [lia|]. pose proof (Z.pow_pos_nonneg 2 (y mod 2 ^ 6)). lia.
    Qed.

    Lemma w64_shl_sym : forall x y,
      bv_shiftl (Z_to_bv 64 x) (bv_and (Z_to_bv 64 y) (Z_to_bv 64 63)) = Z_to_bv 64 (Z.shiftl (zlow 64 x) (zlow 6 y)).
    Proof.
      intros x y. apply bv_eq. rewrite bv_shiftl_unsigned, w64_and, !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus, zlow. cbn [Z.of_N].
      assert (M : Z.land y 63 mod 2 ^ 64 = y mod 2 ^ 6).
      { change 63 with (2 ^ 6 - 1). rewrite land_ones_mod by lia. apply Z.mod_small. pose proof (Z.mod_pos_bound y (2 ^ 6) ltac:(lia)). lia. }
      rewrite M. reflexivity.
    Qed.

    Lemma sym_alu_sound : forall pf op a b e,
      Forall (pfact_ok CS E) pf ->
      sym_alu (mk_oracle pf) pf op a b = Some e ->
      Z_to_bv 64 (zden E e) = alu64 op (Z_to_bv 64 (zden E a)) (Z_to_bv 64 (zden E b)).
    Proof.
      intros pf op a b e HP H. pose proof (mk_oracle_sound CS E pf HP) as HO. unfold sym_alu in H.
      assert (LIT : forall x y, is_lit a = Some x -> is_lit b = Some y -> Some (ELit (zalu op x y)) = Some e ->
                    Z_to_bv 64 (zden E e) = alu64 op (Z_to_bv 64 (zden E a)) (Z_to_bv 64 (zden E b))).
      { intros x y La Lb He. injection He; intros <-. apply is_lit_den with (E := E) in La. apply is_lit_den with (E := E) in Lb.
        rewrite La, Lb. cbn [zden]. unfold zalu. apply w64_of_unsigned. }
      assert (SLT : forall k, k <> KEq ->
         match decide_kind (mk_oracle pf) pf k a b with
         | Some true => Some (ELit 1) | Some false => Some (ELit 0) | None => Some (kind_expr (mk_oracle pf) k a b) end = Some e ->
         Z_to_bv 64 (zden E e) = alu64 (match k with KLts => ALU_SLT | _ => ALU_SLTU end) (Z_to_bv 64 (zden E a)) (Z_to_bv 64 (zden E b))).
      { intros k Hk He. rewrite alu_slt_den by exact Hk.
        destruct (decide_kind (mk_oracle pf) pf k a b) as [r|] eqn:DK.
        - rewrite (decide_kind_sound E pf k a b r HP DK). destruct r; injection He; intros <-; reflexivity.
        - injection He; intros <-. rewrite (kind_expr_den _ k a b HO Hk). reflexivity. }
      (* [comment removed for export] *)
      assert (SRLSYM : Some (eatom (EOp OShr (elow (mk_oracle pf) a 64) (elow (mk_oracle pf) b 6))) = Some e ->
                       Z_to_bv 64 (zden E e) = alu64 ALU_SRL (Z_to_bv 64 (zden E a)) (Z_to_bv 64 (zden E b))).
      { intros He. injection He; intros <-. rewrite eatom_den. cbn [zden opden]. rewrite !elow_den by (try exact HO; lia).
        cbn [alu64 alu]. symmetry. apply w64_shr_sym. }
      (* [comment removed for export] *)
      assert (SLLSYM : Some (eatom (EOp OShl (elow (mk_oracle pf) a 64) (elow (mk_oracle pf) b 6))) = Some e ->
                       Z_to_bv 64 (zden E e) = alu64 ALU_SLL (Z_to_bv 64 (zden E a)) (Z_to_bv 64 (zden E b))).
      { intros He. injection He; intros <-. rewrite eatom_den. cbn [zden opden]. rewrite !elow_den by (try exact HO; lia).
        cbn [alu64 alu]. symmetry. apply w64_shl_sym. }
      destruct (is_lit a) as [x|] eqn:LA; destruct (is_lit b) as [y|] eqn:LB; destruct op;
        first [ exact (LIT x y eq_refl eq_refl H) | exact (SLT KLtu ltac:(discriminate) H) | exact (SLT KLts ltac:(discriminate) H)
              | exact (SRLSYM H) | exact (SLLSYM H) | idtac ];
        try discriminate; try (apply is_lit_den with (E := E) in LB).
      all: try (injection H; intros <-; cbn [alu64 alu]; first
        [ rewrite eadd_den; symmetry; apply w64_add
        | rewrite esub_den; symmetry; apply w64_sub
        | rewrite (eand_den E _ HO); symmetry; apply w64_and
        | rewrite (eor_den E _ HO); symmetry; apply w64_or
        | symmetry; etransitivity; [apply w64_xor|]; apply w64_eq; symmetry; apply exor_den ]; fail).
      (* [comment removed for export] *)
      all: destruct (Z.leb_spec 0 y); try discriminate; injection H; intros <-; rewrite LB;
           pose proof (land63_range y) as YR.
      - rewrite alu_sll_lit by assumption. rewrite (eshl_den E) by lia. symmetry. apply w64_shl_exact. exact YR.
      - rewrite alu_srl_lit by assumption. rewrite (eshr_den E _ HO) by lia. symmetry. apply w64_shr_exact. exact YR.
      - rewrite alu_sra_lit by assumption. rewrite eatom_den. cbn [zden opden]. rewrite (esx_den E _ HO) by lia.
        symmetry. apply w64_ashr_exact. exact YR.
    Qed.

    Lemma low32_lit : forall z, low32 (Z_to_bv 64 z) = Z_to_bv 32 z.
    Proof.
      intros z. unfold low32. apply bv_eq. rewrite extract_low_mod by lia. rewrite !Z_to_bv_unsigned.
      unfold bv_wrap, bv_modulus. cbn [Z.of_N]. apply mod_mod_pow2. lia.
    Qed.

    Lemma sext32_lit : forall z, Z_to_bv 64 (zswrap 32 z) = (sext 64 (Z_to_bv 32 z) : word).
    Proof.
      intros z. rewrite sext_small. f_equal. unfold bv_signed. rewrite Z_to_bv_unsigned.
      unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus, zswrap. cbn [Z.of_N].
      change (2 ^ 32 `div` 2) with (2 ^ (32 - 1)). rewrite Z.add_mod_idemp_l by lia. reflexivity.
    Qed.

    Lemma w32_and : forall x y, bv_and (Z_to_bv 32 x) (Z_to_bv 32 y) = Z_to_bv 32 (Z.land x y).
    Proof.
      intros. apply bv_eq. rewrite bv_and_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
      apply land_mod_pow2. cbn; lia.
    Qed.

    Lemma land31_range : forall k, 0 <= Z.land k 31 < 32.
    Proof.
      intros k. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound k (2 ^ 5) ltac:(lia)). cbn in *. lia.
    Qed.

    Lemma alu32_shift_lit : forall op (u : bv 32) k, 0 <= k ->
      match op with ALU_SLL | ALU_SRL | ALU_SRA => True | _ => False end ->
      alu32 op u (Z_to_bv 32 k) = alu32 op u (Z_to_bv 32 (Z.land k 31)).
    Proof.
      intros op u k Hk Hop. destruct op; try destruct Hop; cbn -[bv_shiftl bv_shiftr bv_ashiftr bv_and Z_to_bv];
        rewrite !w32_and; do 2 f_equal; rewrite <- Z.land_assoc, Z.land_diag; reflexivity.
    Qed.

    Lemma w32_shl_exact : forall x y, 0 <= y -> bv_shiftl (Z_to_bv 32 x) (bv_and (Z_to_bv 32 y) (Z_to_bv 32 31)) = Z_to_bv 32 (x * 2 ^ Z.land y 31).
    Proof.
      intros x y Hy. rewrite w32_and. pose proof (land31_range y) as Hs. set (s := Z.land y 31) in *.
      apply bv_eq. rewrite bv_shiftl_unsigned, !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
      rewrite (Z.mod_small s) by lia. rewrite Z.shiftl_mul_pow2 by lia.
      rewrite Z.mul_mod_idemp_l by (apply Z.pow_nonzero; lia). reflexivity.
    Qed.

    Lemma w32_shr_exact : forall x y, 0 <= y -> let s := Z.land y 31 in
      bv_shiftr (Z_to_bv 32 x) (bv_and (Z_to_bv 32 y) (Z_to_bv 32 31)) = Z_to_bv 32 (Z.shiftr (zlow 32 x) s)
      /\ 0 <= Z.shiftr (zlow 32 x) s < 2 ^ 32 /\ (1 <= s -> Z.shiftr (zlow 32 x) s < 2 ^ 31).
    Proof.
      intros x y Hy. rewrite w32_and. pose proof (land31_range y) as Hs. cbv zeta. set (s := Z.land y 31) in *.
      pose proof (Z.mod_pos_bound x (2 ^ 32) ltac:(lia)) as R. unfold zlow.
      assert (B : 0 <= (x mod 2 ^ 32) ≫ s < 2 ^ 32 /\ (1 <= s -> (x mod 2 ^ 32) ≫ s < 2 ^ 31)).
      { rewrite Z.shiftr_div_pow2 by lia. pose proof (Z.pow_pos_nonneg 2 s ltac:(lia) ltac:(lia)) as P.
        split; [split; [apply Z.div_pos; lia|]|].
        - apply Z.div_lt_upper_bound; [lia|]. apply Z.lt_le_trans with (2 ^ 32); [lia|]. nia.
        - intros H1. apply Z.div_lt_upper_bound; [lia|]. apply Z.lt_le_trans with (2 ^ 32); [lia|].
          replace (2 ^ 32) with (2 ^ 1 * 2 ^ 31) by reflexivity. apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.pow_le_mono_r; lia. }
      split; [|exact B].
      apply bv_eq. rewrite bv_shiftr_unsigned, !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
      rewrite (Z.mod_small s) by lia. symmetry. apply Z.mod_small. lia.
    Qed.

    Lemma swrap32_lit : forall x, bv_signed (Z_to_bv 32 x) = zswrap 32 x.
    Proof.
      intros x. rewrite Z_to_bv_signed. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus, zswrap.
      change (2 ^ Z.of_N 32 `div` 2) with (2 ^ (32 - 1)). change (2 ^ Z.of_N 32) with (2 ^ 32). reflexivity.
    Qed.

    Lemma zswrap32_range : forall x, - 2 ^ 31 <= zswrap 32 x < 2 ^ 31.
    Proof. intros x. unfold zswrap. pose proof (Z.mod_pos_bound (x + 2 ^ (32 - 1)) (2 ^ 32) ltac:(lia)). cbn in *. lia. Qed.

    Lemma w32_ashr_exact : forall x y, 0 <= y -> let s := Z.land y 31 in
      bv_ashiftr (Z_to_bv 32 x) (bv_and (Z_to_bv 32 y) (Z_to_bv 32 31)) = Z_to_bv 32 (Z.shiftr (zswrap 32 x) s)
      /\ - 2 ^ 31 <= Z.shiftr (zswrap 32 x) s < 2 ^ 31.
    Proof.
      intros x y Hy. rewrite w32_and. pose proof (land31_range y) as Hs. cbv zeta. set (s := Z.land y 31) in *.
      pose proof (zswrap32_range x) as R.
      split.
      - apply bv_eq. rewrite bv_ashiftr_unsigned, swrap32_lit, !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
        rewrite (Z.mod_small s) by lia. reflexivity.
      - rewrite Z.shiftr_div_pow2 by lia. pose proof (Z.pow_pos_nonneg 2 s ltac:(lia) ltac:(lia)) as P.
        split.
        + apply Z.div_le_lower_bound; [lia|]. nia.
        + apply Z.div_lt_upper_bound; [lia|]. nia.
    Qed.

    (* [comment removed for export] *)
    Lemma w32_shr_sym : forall x y,
      bv_shiftr (Z_to_bv 32 x) (bv_and (Z_to_bv 32 y) (Z_to_bv 32 31)) = Z_to_bv 32 (Z.shiftr (zlow 32 x) (zlow 5 y))
      /\ 0 <= Z.shiftr (zlow 32 x) (zlow 5 y) < 2 ^ 32.
    Proof.
      intros x y. rewrite w32_and.
      pose proof (Z.mod_pos_bound x (2 ^ 32) ltac:(lia)) as R. pose proof (Z.mod_pos_bound y (2 ^ 5) ltac:(lia)) as R5. unfold zlow.
      assert (M : Z.land y 31 = y mod 2 ^ 5) by (change 31 with (2 ^ 5 - 1); apply land_ones_mod; lia).
      assert (B : 0 <= (x mod 2 ^ 32) ≫ (y mod 2 ^ 5) < 2 ^ 32).
      { rewrite Z.shiftr_div_pow2 by lia. pose proof (Z.pow_pos_nonneg 2 (y mod 2 ^ 5) ltac:(lia) ltac:(lia)) as P.
        split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. nia. }
      split; [|exact B].
      apply bv_eq. rewrite bv_shiftr_unsigned, !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N]. rewrite M.
      rewrite (Z.mod_small (y mod 2 ^ 5)) by lia. symmetry. apply Z.mod_small. lia.
    Qed.

    Lemma w32_shl_sym : forall x y,
      bv_shiftl (Z_to_bv 32 x) (bv_and (Z_to_bv 32 y) (Z_to_bv 32 31)) = Z_to_bv 32 (zlow 32 (Z.shiftl (zlow 32 x) (zlow 5 y))).
    Proof.
      intros x y. rewrite w32_and. unfold zlow.
      assert (M : Z.land y 31 = y mod 2 ^ 5) by (change 31 with (2 ^ 5 - 1); apply land_ones_mod; lia).
      pose proof (Z.mod_pos_bound y (2 ^ 5) ltac:(lia)) as R5.
      apply bv_eq. rewrite bv_shiftl_unsigned, !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N]. rewrite M.
      rewrite (Z.mod_small (y mod 2 ^ 5)) by lia. rewrite Z.mod_mod by lia. reflexivity.
    Qed.

    Lemma sext32_small : forall v, - 2 ^ 31 <= v < 2 ^ 31 -> (sext 64 (Z_to_bv 32 v) : word) = Z_to_bv 64 v.
    Proof. intros v Hv. rewrite <- sext32_lit. f_equal. apply zswrap_small; lia. Qed.

    Lemma sym_alu32_sound : forall pf op a b e,
      Forall (pfact_ok CS E) pf ->
      sym_alu32 (mk_oracle pf) op a b = Some e ->
      Z_to_bv 64 (zden E e) = (sext 64 (alu32 op (low32 (Z_to_bv 64 (zden E a))) (low32 (Z_to_bv 64 (zden E b)))) : word).
    Proof.
      intros pf op a b e HP H. pose proof (mk_oracle_sound CS E pf HP) as HO. unfold sym_alu32 in H.
      assert (LIT : forall x y, is_lit a = Some x -> is_lit b = Some y -> Some (ELit (zalu32 op x y)) = Some e ->
                    Z_to_bv 64 (zden E e) = (sext 64 (alu32 op (low32 (Z_to_bv 64 (zden E a))) (low32 (Z_to_bv 64 (zden E b)))) : word)).
      { intros x y La Lb He. injection He; intros <-. apply is_lit_den with (E := E) in La. apply is_lit_den with (E := E) in Lb.
        rewrite La, Lb. cbn [zden]. unfold zalu32. apply w64_of_unsigned. }
      assert (A32 : forall x y, (alu32 ALU_ADD (Z_to_bv 32 x) (Z_to_bv 32 y)) = Z_to_bv 32 (x + y)).
      { intros x y. cbn [alu32 alu]. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. apply bv_wrap_add_idemp. }
      assert (S32 : forall x y, (alu32 ALU_SUB (Z_to_bv 32 x) (Z_to_bv 32 y)) = Z_to_bv 32 (x - y)).
      { intros x y. cbn [alu32 alu]. apply bv_eq. rewrite bv_sub_unsigned, !Z_to_bv_unsigned. apply bv_wrap_sub_idemp. }
      (* [comment removed for export] *)
      assert (SRLSYM : Some (esx (mk_oracle pf) (eatom (EOp OShr (elow (mk_oracle pf) a 32) (elow (mk_oracle pf) b 5))) 32) = Some e ->
                       Z_to_bv 64 (zden E e) = (sext 64 (alu32 ALU_SRL (low32 (Z_to_bv 64 (zden E a))) (low32 (Z_to_bv 64 (zden E b)))) : word)).
      { intros He. injection He; intros <-. rewrite (esx_den E _ HO) by lia. rewrite eatom_den. cbn [zden opden]. rewrite !elow_den by (try exact HO; lia).
        rewrite !low32_lit. cbn [alu32 alu]. destruct (w32_shr_sym (zden E a) (zden E b)) as [-> _]. apply sext32_lit. }
      (* [comment removed for export] *)
      assert (SLLSYM : Some (esx (mk_oracle pf) (elow (mk_oracle pf) (eatom (EOp OShl (elow (mk_oracle pf) a 32) (elow (mk_oracle pf) b 5))) 32) 32) = Some e ->
                       Z_to_bv 64 (zden E e) = (sext 64 (alu32 ALU_SLL (low32 (Z_to_bv 64 (zden E a))) (low32 (Z_to_bv 64 (zden E b)))) : word)).
      { intros He. injection He; intros <-. rewrite (esx_den E _ HO) by lia. rewrite elow_den by (try exact HO; lia). rewrite eatom_den. cbn [zden opden].
        rewrite !elow_den by (try exact HO; lia).
        rewrite !low32_lit. cbn [alu32 alu]. rewrite w32_shl_sym; rewrite <- sext32_lit; reflexivity. }
      destruct (is_lit a) as [x|] eqn:LA; destruct (is_lit b) as [y|] eqn:LB; destruct op;
        first [ exact (LIT x y eq_refl eq_refl H) | exact (SRLSYM H) | exact (SLLSYM H) | idtac ]; try discriminate;
        try (injection H; intros <-; rewrite (ew32_den E _ HO), !low32_lit; first
        [ rewrite eadd_den, A32; apply sext32_lit
        | rewrite esub_den, S32; apply sext32_lit ]; fail).
      (* [comment removed for export] *)
      all: apply is_lit_den with (E := E) in LB; destruct (Z.leb_spec 0 y) as [Y0|]; try discriminate; rewrite !low32_lit, LB; cbn [alu32 alu];
           pose proof (land31_range y) as YR.
      all: lazymatch goal with
           | |- _ = sext 64 (bv_shiftl _ _) =>
               injection H; intros <-; rewrite (ew32_den E _ HO), (eshl_den E) by lia; rewrite w32_shl_exact by exact Y0; apply sext32_lit
           | |- _ = sext 64 (bv_shiftr _ _) =>
               destruct (w32_shr_exact (zden E a) y Y0) as (EQ & B1 & B2); rewrite EQ;
               destruct (Z.eqb_spec (Z.land y 31) 0) as [Z0|NZ]; injection H; intros <-;
               [ rewrite (ew32_den E _ HO), Z0, Z.shiftr_0_r, <- sext32_lit; f_equal; symmetry; apply zswrap_mod; lia
               | rewrite eatom_den; cbn [zden opden]; rewrite elow_den by (try exact HO; lia); symmetry; apply sext32_small; unfold zlow in *; lia ]
           | |- _ = sext 64 (bv_ashiftr _ _) =>
               destruct (w32_ashr_exact (zden E a) y Y0) as (EQ & B1); rewrite EQ;
               destruct (Z.eqb_spec (Z.land y 31) 0) as [Z0|NZ]; injection H; intros <-;
               [ rewrite (ew32_den E _ HO), Z0, Z.shiftr_0_r, <- sext32_lit; f_equal; symmetry; apply zswrap_zswrap
               | rewrite eatom_den; cbn [zden opden]; rewrite (esx_den E _ HO) by lia; symmetry; apply sext32_small; lia ]
           end.
    Qed.

    Lemma sym_mul_sound : forall pf op a b e,
      Forall (pfact_ok CS E) pf ->
      sym_mul (mk_oracle pf) op a b = Some e ->
      Z_to_bv 64 (zden E e) = (mul_div op (Z_to_bv 64 (zden E a)) (Z_to_bv 64 (zden E b)) : word).
    Proof.
      intros pf op a b e HP H. pose proof (mk_oracle_sound CS E pf HP) as HO. unfold sym_mul in H.
      assert (MUL : Some (emulO (mk_oracle pf) a b) = Some e -> Z_to_bv 64 (zden E e) = (mul_div M_MUL (Z_to_bv 64 (zden E a)) (Z_to_bv 64 (zden E b)) : word)).
      { intros He. injection He; intros <-. rewrite (emulO_den E). cbn [mul_div]. symmetry. apply w64_mul. }
      assert (DIVREM : forall y, zden E b = y ->
        (Some (if Z.eqb (zlow 64 y) 0 then ELit (two64 - 1) else eatom (EOp ODivU (elow (mk_oracle pf) a 64) (ELit (zlow 64 y)))) = Some e ->
         Z_to_bv 64 (zden E e) = (mul_div M_DIVU (Z_to_bv 64 (zden E a)) (Z_to_bv 64 (zden E b)) : word))
        /\ (Some (if Z.eqb (zlow 64 y) 0 then a else eatom (EOp ORemU (elow (mk_oracle pf) a 64) (ELit (zlow 64 y)))) = Some e ->
         Z_to_bv 64 (zden E e) = (mul_div M_REMU (Z_to_bv 64 (zden E a)) (Z_to_bv 64 (zden E b)) : word))).
      { intros y Hy. cbn [mul_div]. rewrite Hy, zlow64_unsigned.
        pose proof (Z.mod_pos_bound (zden E a) (2 ^ 64) ltac:(lia)) as RA. pose proof (Z.mod_pos_bound y (2 ^ 64) ltac:(lia)) as RB.
        destruct (Z.eqb_spec (zlow 64 y) 0) as [Y0|YN]; split; intros He; injection He; intros <-.
        - cbn [zden]. apply w64_eq. reflexivity.
        - reflexivity.
        - rewrite eatom_den. cbn [zden opden]. rewrite elow_den by (try exact HO; lia). unfold zlow in *.
          apply bv_eq. rewrite bv_divu_unsigned, !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
          apply Z.mod_small. split; [apply Z.div_pos; lia|]. apply Z.le_lt_trans with (zden E a mod 2 ^ 64); [|lia].
          apply Z.div_le_upper_bound; [lia|]. nia.
        - rewrite eatom_den. cbn [zden opden]. rewrite elow_den by (try exact HO; lia). unfold zlow in *.
          apply bv_eq. rewrite bv_modu_unsigned, !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
          apply Z.mod_small. pose proof (Z.mod_pos_bound (zden E a mod 2 ^ 64) (y mod 2 ^ 64) ltac:(lia)). lia. }
      destruct (is_lit a) as [x|] eqn:LA; [destruct (is_lit b) as [y|] eqn:LB|].
      - injection H; intros <-. apply is_lit_den with (E := E) in LA. apply is_lit_den with (E := E) in LB.
        rewrite LA, LB. cbn [zden]. unfold zmuldiv. apply w64_of_unsigned.
      - destruct op; try discriminate; first [exact (MUL H) | idtac]; cbn [is_lit] in H; discriminate.
      - destruct op; try discriminate; first [exact (MUL H) | idtac];
          destruct (is_lit b) as [y|] eqn:LB; try discriminate; apply is_lit_den with (E := E) in LB;
          first [exact (proj1 (DIVREM y LB) H) | exact (proj2 (DIVREM y LB) H)].
    Qed.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)

    Definition sres_ok (ss : sstate) (m : mem) (r : sres) : Prop :=
      let ms := ms_den segs G E ss m in
      match r with
      | SNext ss' | SStop ss' =>
          length (s_rs ss') = 31%nat /\ exists m', mstepA segs L CS ms (ms_den segs G E ss' m') /\ INV E ss' m'
      | SBind ss' =>
          length (s_rs ss') = 31%nat /\
          (ss_wf C ss = true -> exists m' v, mstepA segs L CS ms (ms_den segs G (env_setz E (s_nx ss) v) ss' m')
                                           /\ INV (env_setz E (s_nx ss) v) ss' m')
      | SBranch c st sf =>
          length (s_rs st) = 31%nat /\ length (s_rs sf) = 31%nat /\
          exists m', mstepA segs L CS ms (ms_den segs G E (if cnden E c then st else sf) m') /\ INV E (if cnden E c then st else sf) m'
      | SFail _ => True
      end.

    Lemma liftA_ok : forall (c : core) (mm : mem) acc,
      liftA ro (MachineOk (@mkAccessReport _ (c, mm) acc)) = MachineOk (@mkAccessReport _ (MS_of_core c mm ro) acc).
    Proof. reflexivity. Qed.

    Lemma INV_pf : forall ss m fs, INV E ss m -> Forall (pfact_ok CS E) fs -> INV E (add_pfs ss fs) m.
    Proof.
      intros ss m fs (H1 & H2 & H3) HF. unfold add_pfs.
      revert ss H1 H2 H3. induction fs as [|f fs IH]; intros ss H1 H2 H3; [split; [exact H1|split; [exact H2| exact H3]]|].
      cbn [fold_left]. inversion HF; subst. apply IH; [assumption| | |]; unfold add_pf; cbn.
      - exact H1.
      - unfold pf_add. destruct (pf_mem f (s_pf ss)); [exact H2| constructor; assumption].
      - exact H3.
    Qed.

    Lemma add_pfs_pfok : forall E1 ss fs, Forall (pfact_ok CS E1) (s_pf ss) -> Forall (pfact_ok CS E1) fs -> Forall (pfact_ok CS E1) (s_pf (add_pfs ss fs)).
    Proof.
      intros E1 ss fs. unfold add_pfs. revert ss. induction fs as [|f fs IH]; intros ss H HF; [exact H|].
      cbn [fold_left]. inversion HF; subst. apply IH; [|assumption]. unfold add_pf, pf_add. cbn [s_pf].
      destruct (pf_mem f (s_pf ss)); [exact H| constructor; assumption].
    Qed.

    Lemma add_pfs_rs : forall ss fs, s_rs (add_pfs ss fs) = s_rs ss /\ s_pc (add_pfs ss fs) = s_pc ss /\ s_mf (add_pfs ss fs) = s_mf ss /\ s_nx (add_pfs ss fs) = s_nx ss
                                      /\ s_W (add_pfs ss fs) = s_W ss.
    Proof.
      intros ss fs. unfold add_pfs. revert ss. induction fs as [|f fs IH]; intros ss; [repeat split; reflexivity|].
      cbn [fold_left]. destruct (IH (add_pf ss f)) as (A1 & A2 & A3 & A4 & A5). rewrite A1, A2, A3, A4, A5. repeat split; reflexivity.
    Qed.

    Lemma add_pfs_same : forall ss fs, s_same (add_pfs ss fs) = s_same ss.
    Proof.
      intros ss fs. unfold add_pfs. revert ss. induction fs as [|f fs IH]; intros ss; [reflexivity|].
      cbn [fold_left]. rewrite IH. reflexivity.
    Qed.

    Lemma add_pfs_ref : forall ss fs, s_ref (add_pfs ss fs) = s_ref ss /\ s_nm (add_pfs ss fs) = s_nm ss.
    Proof.
      intros ss fs. unfold add_pfs. revert ss. induction fs as [|f fs IH]; intros ss; [split; reflexivity|].
      cbn [fold_left]. destruct (IH (add_pf ss f)) as [A B]. rewrite A, B. split; reflexivity.
    Qed.

    Lemma INV_same : forall ss ss' m, s_mf ss' = s_mf ss -> s_pf ss' = s_pf ss -> s_W ss' = s_W ss -> s_same ss' = s_same ss ->
      INV E ss m -> s_ref ss' = s_ref ss -> INV E ss' m.
    Proof. intros ss ss' m H1 H2 H3 H4 HI H5. unfold INV, refm in *. rewrite H1, H2, H3, H4, H5. exact HI. Qed.

    Lemma refm_irrel : forall E0 E' ss ss', eml E' = eml E0 -> s_ref ss' = s_ref ss -> refm E' ss' = refm E0 ss.
    Proof. intros E0 E' ss ss' H1 H2. unfold refm, em. rewrite H1, H2. reflexivity. Qed.

    Lemma wr_reg_ref : forall ss k v, s_ref (wr_reg ss k v) = s_ref ss.
    Proof. intros. unfold wr_reg. destruct (Z.eqb k 0); reflexivity. Qed.

    (* [comment removed for export] *)
    Ltac lx_ref_eq :=
      cbn [s_ref set_pc next_pc set_mf set_pf set_W bump add_pf settle];
      do 6 (try (first [ rewrite wr_reg_ref | rewrite (proj1 (add_pfs_ref _ _)) ];
                   cbn [s_ref set_pc next_pc set_mf set_pf set_W bump add_pf settle]));
      reflexivity.
    (* [comment removed for export] *)
    Ltac lx_refm E0 ss0 :=
      do 4 (try match goal with
             | |- context [refm ?E1 ?S1] =>
                 tryif (constr_eq E1 E0; constr_eq S1 ss0) then fail else
                 replace (refm E1 S1) with (refm E0 ss0) by (symmetry; apply refm_irrel; [reflexivity | lx_ref_eq])
             end).

    Lemma wr_reg_same : forall ss k v,
      s_mf (wr_reg ss k v) = s_mf ss /\ s_pf (wr_reg ss k v) = s_pf ss /\ s_pc (wr_reg ss k v) = s_pc ss /\ s_nx (wr_reg ss k v) = s_nx ss
      /\ s_W (wr_reg ss k v) = s_W ss.
    Proof. intros. unfold wr_reg. destruct (Z.eqb k 0); repeat split; reflexivity. Qed.

    Lemma wr_reg_sm : forall ss k v, s_same (wr_reg ss k v) = s_same ss.
    Proof. intros. unfold wr_reg. destruct (Z.eqb k 0); reflexivity. Qed.

    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)

    Lemma zden_setz : forall n v e, evars_lt n e = true -> zden (env_setz E n v) e = zden E e.
    Proof.
      intros n v e. induction e as [z|i|i|a IHa b IHb|c a IHa|o a IHa b IHb]; cbn -[Pos.ltb ez ew env_setz]; intros H; try reflexivity.
      - rewrite ez_setz. destruct (Pos.eqb_spec i n); [|reflexivity]. subst. apply Pos.ltb_lt in H. lia.
      - apply andb_prop in H as [H1 H2]. rewrite IHa, IHb by assumption. reflexivity.
      - rewrite IHa by assumption. reflexivity.
      - apply andb_prop in H as [H1 H2]. rewrite IHa, IHb by assumption. reflexivity.
    Qed.

    Lemma zdenp_setz : forall n v e, evars_lt n e = true -> zdenp (env_setz E n v) e = zdenp E e.
    Proof. intros. rewrite !zdenp_ok. apply zden_setz. assumption. Qed.

    Lemma rden_setz : forall n v r, rvars_lt n r = true -> rden (env_setz E n v) r = rden E r.
    Proof. intros n v [i|e] H; cbn -[zdenp]; [reflexivity|]. rewrite zdenp_setz by exact H. reflexivity. Qed.

    Lemma regs_den_setz : forall n v rs, forallb (rvars_lt n) rs = true -> regs_den (env_setz E n v) rs = regs_den E rs.
    Proof.
      intros n v rs H.
      assert (R : forall r, In r rs -> rden (env_setz E n v) r = rden E r).
      { intros r Hr. apply rden_setz. rewrite forallb_forall in H. apply H. exact Hr. }
      do 31 (destruct rs as [|? rs]; [reflexivity|]). destruct rs; [|reflexivity].
      cbn [regs_den]. rewrite !R by (cbn; tauto). reflexivity.
    Qed.

    Lemma cden_setz : forall n v c, cvars_lt n c = true -> cden (env_setz E n v) c = cden E c.
    Proof.
      intros n v c; induction c as [i|w e|w k|w i|c IH o l|wr er]; intros H; cbn -[zdenp N.to_nat cden]; cbn [cden]; try reflexivity.
      - cbn in H. rewrite !zdenp_setz by exact H. reflexivity.
      - cbn in H. fold (cden (env_setz E n v) c) (cden E c). rewrite (IH H). reflexivity.
      - cbn in H. rewrite !zdenp_setz by exact H. reflexivity.
    Qed.

    Lemma csden_setz : forall n v cs, forallb (cvars_lt n) cs = true -> csden (env_setz E n v) cs = csden E cs.
    Proof.
      intros n v cs H. unfold csden. induction cs as [|c cs IH]; [reflexivity|]. cbn in H. apply andb_prop in H as [H1 H2].
      cbn. rewrite cden_setz, IH by assumption. reflexivity.
    Qed.

    Lemma zdenps_setz : forall n v xs, forallb (evars_lt n) xs = true -> map (zdenp (env_setz E n v)) xs = map (zdenp E) xs.
    Proof.
      intros n v xs. induction xs as [|x xs IH]; cbn -[zdenp evars_lt env_setz]; intros H; [reflexivity|].
      apply andb_prop in H as [H1 H2]. rewrite zdenp_setz, IH by assumption. reflexivity.
    Qed.
    Lemma pfact_ok_setz : forall n v f, pfvars_lt n f = true -> pfact_ok CS (env_setz E n v) f <-> pfact_ok CS E f.
    Proof.
      intros n v f H.
      destruct f as [| | | | | | | | | | |pj pxs]; [| | | | | | | | | | | unfold pfact_ok, eprop; cbn [epr env_setz]; cbn [pfvars_lt] in H; rewrite (zdenps_setz n v pxs H); tauto].
      all: cbn -[zdenp Z.pow Z.of_N ez env_setz] in H |- *;
        repeat (apply andb_prop in H; destruct H as [H ?]); rewrite ?zdenp_setz by assumption; try tauto.
      (* [comment removed for export] *)
      rewrite !ez_setz. destruct (Pos.eqb_spec k n); [subst; apply Pos.ltb_lt in H; lia|]. tauto.
    Qed.

    Lemma wden_setz : forall n v W, forallb (fun lh => evars_lt n (fst lh) && evars_lt n (snd lh)) W = true ->
      wden (env_setz E n v) W = wden E W.
    Proof.
      intros n v W H. unfold wden. induction W as [|[l h] W IH]; [reflexivity|]. cbn in H.
      apply andb_prop in H as [H1 H2]. apply andb_prop in H1 as [Hl Hh]. cbn. rewrite !zdenp_setz, IH by assumption. reflexivity.
    Qed.

    Lemma ldenw_setz : forall n v l, lvars_lt n l = true -> ldenw (env_setz E n v) l = ldenw E l.
    Proof.
      intros n v l. induction l as [k|l IH i w e]; intros H; cbn -[zdenp] in H |- *; [reflexivity|].
      repeat (apply andb_prop in H; destruct H as [H ?]). rewrite IH, !zdenp_setz by assumption. reflexivity.
    Qed.

    Lemma ldenb_setz : forall n v l, lvars_lt n l = true -> ldenb (env_setz E n v) l = ldenb E l.
    Proof.
      intros n v l. induction l as [k|l IH i w e]; intros H; cbn -[zdenp wbytes upd_bytes] in H |- *; [reflexivity|].
      repeat (apply andb_prop in H; destruct H as [H ?]). rewrite IH, !zdenp_setz by assumption. reflexivity.
    Qed.

    Lemma blden_setz : forall n v bl, blvars_lt n bl = true -> blden (env_setz E n v) bl = blden E bl.
    Proof.
      intros n v bl. induction bl as [|a k bl IH|kv]; cbn -[zdenp evars_lt env_setz]; intros H; [reflexivity| |reflexivity].
      apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. rewrite !zdenp_setz, IH by assumption. reflexivity.
    Qed.
    (* [comment removed for export] *)
    Lemma mfact_ok_setz_heap : forall n v mm f, mfvars_lt n f = true ->
      match f with MHeap _ _ | MLawH _ _ _ _ _ _ | MCliH _ _ _ _ | MApartBl _ _ _ | MOqH _ _ | MHpr _ _ _ _ _ => True | _ => False end ->
      mfact_ok segs L CS (env_setz E n v) mm f <-> mfact_ok segs L CS E mm f.
    Proof.
      intros n v mm f H K. destruct f as [fa fcs|fa fcs|fa fn fk|flo fhi|foa fon|ok_k ok_l sh_l|ra_ rw_ rl_ rn_ rwr_|mW mi mj|mi mj|ml mX mi mj|ml ma mn|ml ma mn|qbl qok|ql qbl qsp qX qi qj|ql qs qa qn|qa qn qbl|ql qk|qj qo qn qxs qok]; try destruct K; cbn [mfvars_lt] in H;
        repeat (apply andb_prop in H; destruct H as [H ?]); cbn [mfact_ok].
      - rewrite (blden_setz n v qbl), (wden_setz n v qok) by assumption. unfold ehp, ecw, ecur. cbn [env_setz]. tauto.
      - rewrite (blden_setz n v qbl), (zdenp_setz _ _ qsp), (wden_setz n v qX) by assumption. unfold ehlaw, em. cbn [elh eml env_setz]. tauto.
      - rewrite !zdenp_setz by assumption. unfold hlawcli, ehlaw. cbn [elb0 elh env_setz]. tauto.
      - rewrite !zdenp_setz, (blden_setz n v qbl) by assumption. tauto.
      - unfold hlawopq, ehlaw, eo. cbn [elb0 elh eol env_setz]. tauto.
      - rewrite (blden_setz n v qo), (blden_setz n v qn), (wden_setz n v qok) by assumption.
        rewrite (map_ext_in (zdenp (env_setz E n v)) (zdenp E) qxs) by (intros e He; apply zdenp_setz; rewrite forallb_forall in *; auto).
        unfold ehres, ecw, elb0. cbn [ehr env_setz]. tauto.
    Qed.
    Lemma mfact_ok_setz : forall n v mm f, mfvars_lt n f = true -> mfact_ok segs L CS (env_setz E n v) mm f <-> mfact_ok segs L CS E mm f.
    Proof.
      intros n v mm f H.
      pose proof (mfact_ok_setz_heap n v mm f H) as HEAPC.
      destruct f as [fa fcs|fa fcs|fa fn fk|flo fhi|foa fon|ok_k ok_l sh_l|ra_ rw_ rl_ rn_ rwr_|mW mi mj|mi mj|ml mX mi mj|ml ma mn|ml ma mn|qbl qok|ql qbl qsp qX qi qj|ql qs qa qn|qa qn qbl|ql qk|qj qo qn qxs qok].
      13-18: exact (HEAPC I).
      all: clear HEAPC.
      7:{ cbn [mfvars_lt] in H. repeat (apply andb_prop in H; destruct H as [H ?]).
          cbn [mfact_ok]. rewrite !zdenp_setz, ?ldenw_setz, ?ldenb_setz by assumption. tauto. }
      (* [comment removed for export] *)
      7:{ cbn [mfvars_lt] in H. cbn [mfact_ok]. rewrite (wden_setz n v mW H). unfold em; cbn [eml env_setz]. tauto. }
      7:{ cbn [mfact_ok]. unfold em; cbn [eml env_setz]. tauto. }
      7:{ cbn [mfvars_lt] in H. cbn [mfact_ok]. rewrite (wden_setz n v mX H). unfold em, elaw; cbn [eml elw env_setz]. tauto. }
      7:{ cbn [mfvars_lt] in H. apply andb_prop in H as [H1 H2]. cbn [mfact_ok]. rewrite !zdenp_setz by assumption. unfold elaw; cbn [elw env_setz]. tauto. }
      7:{ cbn [mfvars_lt] in H. apply andb_prop in H as [H1 H2]. cbn [mfact_ok]. rewrite !zdenp_setz by assumption. unfold elaw; cbn [elw env_setz]. tauto. }
      all: try solve [cbn [mfvars_lt] in H; rewrite forallb_app in H; apply andb_prop in H as [H1 H2];
                   cbn [mfact_ok]; rewrite (wden_setz n v ok_l H1), (wden_setz n v sh_l H2); unfold eo; cbn [eol env_setz]; tauto].
      all: cbn -[zdenp csden] in H |- *;
        repeat (apply andb_prop in H; destruct H as [H ?]); rewrite ?zdenp_setz, ?csden_setz by assumption; try tauto.
    Qed.

    Lemma Forall_pf_setz : forall n v pf, forallb (pfvars_lt n) pf = true ->
      Forall (pfact_ok CS E) pf -> Forall (pfact_ok CS (env_setz E n v)) pf.
    Proof.
      intros n v pf H HF. induction HF as [|f pf Hf HF IH]; [constructor|]. cbn in H. apply andb_prop in H as [H1 H2].
      constructor; [apply (pfact_ok_setz n v f H1); exact Hf| apply IH; exact H2].
    Qed.

    Lemma Forall_mf_setz : forall n v mm mf, forallb (mfvars_lt n) mf = true ->
      Forall (mfact_ok segs L CS E mm) mf -> Forall (mfact_ok segs L CS (env_setz E n v) mm) mf.
    Proof.
      intros n v mm mf H HF. induction HF as [|f mf Hf HF IH]; [constructor|]. cbn in H. apply andb_prop in H as [H1 H2].
      constructor; [apply (mfact_ok_setz n v mm f H1); exact Hf| apply IH; exact H2].
    Qed.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    Lemma zden_setl : forall n l e, zden (env_setl E n l) e = zden E e.
    Proof. intros n l e. induction e; cbn; try reflexivity; try (rewrite IHe1, IHe2; reflexivity); try (rewrite IHe; reflexivity). Qed.
    Lemma zdenp_setl : forall n l e, zdenp (env_setl E n l) e = zdenp E e.
    Proof. intros. rewrite !zdenp_ok. apply zden_setl. Qed.
    Lemma rden_setl : forall n l r, rden (env_setl E n l) r = rden E r.
    Proof. intros n l [i|e]; cbn -[zdenp]; [reflexivity|]. rewrite zdenp_setl. reflexivity. Qed.
    Lemma regs_den_setl : forall n l rs, regs_den (env_setl E n l) rs = regs_den E rs.
    Proof.
      intros n l rs. do 31 (destruct rs as [|? rs]; [reflexivity|]). destruct rs; [|reflexivity].
      cbn [regs_den]. rewrite !rden_setl. reflexivity.
    Qed.
    Lemma pc_den_setl : forall n l p, pc_den (env_setl E n l) p = pc_den E p.
    Proof. intros n l [z|r]; cbn -[rden Z_to_bv]; [reflexivity|]. rewrite rden_setl. reflexivity. Qed.
    Lemma ms_den_setl : forall n l ss m, ms_den segs G (env_setl E n l) ss m = ms_den segs G E ss m.
    Proof. intros. unfold ms_den. rewrite regs_den_setl, pc_den_setl. reflexivity. Qed.
    Lemma cden_setl : forall n l c, cden (env_setl E n l) c = cden E c.
    Proof.
      intros n l c; induction c as [i|w e|w kb|w i|c IH o ln|wr er]; cbn -[zdenp N.to_nat cden]; cbn [cden]; try reflexivity.
      - rewrite !zdenp_setl. reflexivity.
      - fold (cden (env_setl E n l) c) (cden E c). rewrite IH. reflexivity.
      - rewrite !zdenp_setl. reflexivity.
    Qed.
    Lemma csden_setl : forall n l cs, csden (env_setl E n l) cs = csden E cs.
    Proof. intros n l cs. unfold csden. induction cs as [|c cs IH]; [reflexivity|]. cbn. rewrite cden_setl, IH. reflexivity. Qed.
    Lemma wden_setl : forall n l W, wden (env_setl E n l) W = wden E W.
    Proof. intros n l W. unfold wden. apply map_ext. intros [lo hi]. cbn [fst snd]. rewrite !zdenp_setl. reflexivity. Qed.
    Lemma zdenps_setl : forall n l xs, map (zdenp (env_setl E n l)) xs = map (zdenp E) xs.
    Proof. intros n l xs. induction xs as [|x xs IH]; cbn -[zdenp env_setl]; [reflexivity|]. rewrite zdenp_setl, IH. reflexivity. Qed.
    Lemma pfact_ok_setl : forall n l f, pfact_ok CS (env_setl E n l) f <-> pfact_ok CS E f.
    Proof.
      intros n l f.
      destruct f as [| | | | | | | | | | |pj pxs]; [| | | | | | | | | | | unfold pfact_ok, eprop; cbn [epr env_setl]; rewrite (zdenps_setl n l pxs); tauto].
      all: cbn -[zdenp Z.pow Z.of_N ez env_setl]; rewrite ?zdenp_setl; try tauto. all: rewrite !ez_setl; tauto.
    Qed.
    Lemma ldenw_setl : forall n l lx, llvars_lt n lx = true -> ldenw (env_setl E n l) lx = ldenw E lx.
    Proof.
      intros n l lx. induction lx as [kb|lx IH i w e]; cbn -[zdenp el Pos.ltb]; intros H.
      - rewrite el_setl. destruct (Pos.eqb_spec kb n); [subst; apply Pos.ltb_lt in H; lia| reflexivity].
      - rewrite IH, !zdenp_setl by exact H. reflexivity.
    Qed.
    Lemma ldenb_setl : forall n l lx, llvars_lt n lx = true -> ldenb (env_setl E n l) lx = ldenb E lx.
    Proof.
      intros n l lx. induction lx as [kb|lx IH i w e]; cbn -[zdenp el eb wbytes upd_bytes Pos.ltb]; intros H.
      - rewrite eb_setl. reflexivity.
      - rewrite IH, !zdenp_setl by exact H. reflexivity.
    Qed.
    Lemma blden_setl : forall n l bl, blden (env_setl E n l) bl = blden E bl.
    Proof. intros n l bl. induction bl as [|a k bl IH|kv]; cbn -[zdenp env_setl]; [reflexivity| |reflexivity]. rewrite !zdenp_setl, IH. reflexivity. Qed.
    Lemma mfact_ok_setl_heap : forall n l mm f,
      match f with MHeap _ _ | MLawH _ _ _ _ _ _ | MCliH _ _ _ _ | MApartBl _ _ _ | MOqH _ _ | MHpr _ _ _ _ _ => True | _ => False end ->
      mfact_ok segs L CS (env_setl E n l) mm f <-> mfact_ok segs L CS E mm f.
    Proof.
      intros n l mm f K. destruct f as [fa fcs|fa fcs|fa fn fk|flo fhi|foa fon|ok_k ok_l sh_l|ra_ rw_ rl_ rn_ rwr_|mW mi mj|mi mj|ml mX mi mj|ml ma mn|ml ma mn|qbl qok|ql qbl qsp qX qi qj|ql qs qa qn|qa qn qbl|ql qk|qj qo qn qxs qok]; try destruct K; cbn [mfact_ok].
      - rewrite (blden_setl n l qbl), (wden_setl n l qok). unfold ehp, ecw, ecur. cbn [env_setl]. tauto.
      - rewrite (blden_setl n l qbl), zdenp_setl, (wden_setl n l qX). unfold ehlaw, em. cbn [elh eml env_setl]. tauto.
      - rewrite !zdenp_setl. unfold hlawcli, ehlaw. cbn [elb0 elh env_setl]. tauto.
      - rewrite !zdenp_setl, (blden_setl n l qbl). tauto.
      - unfold hlawopq, ehlaw, eo. cbn [elb0 elh eol env_setl]. tauto.
      - rewrite (blden_setl n l qo), (blden_setl n l qn), (wden_setl n l qok).
        rewrite (map_ext _ _ (zdenp_setl n l)). unfold ehres, ecw, elb0. cbn [ehr env_setl]. tauto.
    Qed.
    Lemma mfact_ok_setl : forall n l mm f, mflvars_lt n f = true -> mfact_ok segs L CS (env_setl E n l) mm f <-> mfact_ok segs L CS E mm f.
    Proof.
      intros n l mm f H.
      pose proof (mfact_ok_setl_heap n l mm f) as HEAPC.
      destruct f as [fa fcs|fa fcs|fa fn fk|flo fhi|foa fon|ok_k ok_l sh_l|ra_ rw_ rl_ rn_ rwr_|mW mi mj|mi mj|ml mX mi mj|ml ma mn|ml ma mn|qbl qok|ql qbl qsp qX qi qj|ql qs qa qn|qa qn qbl|ql qk|qj qo qn qxs qok].
      13-18: exact (HEAPC I).
      all: clear HEAPC.
      7:{ cbn [mflvars_lt] in H. cbn [mfact_ok]. rewrite !zdenp_setl, ?ldenw_setl, ?ldenb_setl by exact H. tauto. }
      7:{ cbn [mfact_ok]. rewrite wden_setl, !em_setl. tauto. }
      7:{ cbn [mfact_ok]. rewrite !em_setl. tauto. }
      7:{ cbn [mfact_ok]. rewrite wden_setl, !em_setl, elaw_setl. tauto. }
      7:{ cbn [mfact_ok]. rewrite !zdenp_setl, elaw_setl. tauto. }
      7:{ cbn [mfact_ok]. rewrite !zdenp_setl, elaw_setl. tauto. }
      all: try solve [cbn [mfact_ok]; rewrite !wden_setl, eo_setl; tauto].
      all: cbn -[zdenp csden eb rw_cells ro_cells bytes_at stk aobj Z.of_nat] in H |- *; rewrite ?zdenp_setl, ?csden_setl, ?eb_setl; try tauto.
    Qed.
    Lemma Forall_pf_setl : forall n l pf, Forall (pfact_ok CS E) pf -> Forall (pfact_ok CS (env_setl E n l)) pf.
    Proof. intros n l pf H. eapply Forall_impl; [|exact H]. intros f Hf. apply pfact_ok_setl. exact Hf. Qed.
    Lemma Forall_mf_setl : forall n l mm mf, forallb (mflvars_lt n) mf = true ->
      Forall (mfact_ok segs L CS E mm) mf -> Forall (mfact_ok segs L CS (env_setl E n l) mm) mf.
    Proof.
      intros n l mm mf H HF. induction HF as [|f mf Hf HF IH]; [constructor|]. cbn in H. apply andb_prop in H as [H1 H2].
      constructor; [apply (mfact_ok_setl n l mm f H1); exact Hf| apply IH; exact H2].
    Qed.

    Lemma wr_reg_rs_ext : forall s1 s2 k v, s_rs s1 = s_rs s2 -> s_rs (wr_reg s1 k v) = s_rs (wr_reg s2 k v).
    Proof. intros s1 s2 k v H. unfold wr_reg. destruct (Z.eqb k 0); cbn; rewrite H; reflexivity. Qed.

    Lemma havoc_rd_with_ok : forall ss m pc sz (rd : bv 5) (V : word) extra,
      INV E ss m -> s_pc ss = PCz pc -> length (s_rs ss) = 31%nat ->
      step_accesses segs (ms_den segs G E ss m) =
        MachineOk (@mkAccessReport _ (MS_of_core (rset rd V (with_pc (Z_to_bv 64 pc + Z_to_bv 64 sz) (Core (regs_den E (s_rs ss)) F (Z_to_bv 64 pc) fc None))) m ro) []) ->
      Forall (pfact_ok CS (env_setz E (s_nx ss) (bv_unsigned V))) extra ->
      sres_ok ss m (havoc_rd_with ss (bv_unsigned rd) extra pc sz).
    Proof.
      intros ss m pc sz rd V extra HI Hpc Hlen Hst EXTRA. pose proof HI as (HM & HP & MU & WM & MI & SM).
      unfold havoc_rd_with. cbn [sres_ok].
      set (fs := [FGe (eatom (EZv (s_nx ss))); FGe (eadd (ELit (two64 - 1)) (emulc (-1) (eatom (EZv (s_nx ss)))))] ++ extra).
      destruct (add_pfs_rs (bump ss) fs) as (P1 & P2 & P3 & P4 & P5). cbn [s_rs s_pc s_mf s_nx bump] in P1, P2, P3, P4.
      split. { cbn [s_rs next_pc set_pc]. rewrite wr_reg_len, P1. exact Hlen. }
      intros WF. exists m, (bv_unsigned V).
      unfold ss_wf in WF. apply andb_prop in WF as [WF WSB]. apply andb_prop in WF as [WF WW]. apply andb_prop in WF as [WF WP]. apply andb_prop in WF as [WF WM']. apply andb_prop in WF as [WPC WR].
      set (E' := env_setz E (s_nx ss) (bv_unsigned V)).
      destruct (wr_reg_same (add_pfs (bump ss) fs) (bv_unsigned rd) (RZ (eatom (EZv (s_nx ss))))) as (W1 & W2 & W3 & W4 & W5). pose proof (wr_reg_sm (add_pfs (bump ss) fs) (bv_unsigned rd) (RZ (eatom (EZv (s_nx ss))))) as WS4.
      split.
      - split; [reflexivity|]. exists []. split; [|apply acc_ok_nil]. rewrite Hst.
        unfold ms_den, next_pc, set_pc. cbn [s_rs s_pc pc_den].
        rewrite (wr_reg_rs_ext _ ss) by exact P1.
        rewrite <- (regs_den_setz (s_nx ss) (bv_unsigned V) (s_rs ss) WR).
        rewrite (rset_den E' ss rd _ (RZ (eatom (EZv (s_nx ss))))); [| exact Hlen |].
        2:{ subst E'. cbn [rden zdenp eatom]. rewrite ez_setz, Pos.eqb_refl. apply w64_of_unsigned. }
        rewrite w64_add. reflexivity.
      - unfold INV. cbn [s_mf s_pf s_W next_pc set_pc]. rewrite W1, W2, W5, P3, P5. cbn [s_W bump]. split; [|split].
        + apply Forall_mf_setz; assumption.
        + assert (OLD : Forall (pfact_ok CS E') (s_pf ss)) by (apply Forall_pf_setz; assumption).
          pose proof (bv_unsigned_in_range 64 V) as VR. unfold bv_modulus in VR. cbn [Z.of_N] in VR.
          assert (N1 : pfact_ok CS E' (FGe (eatom (EZv (s_nx ss))))).
          { cbn -[eatom ez env_setz]. rewrite zdenp_ok, eatom_den. cbn -[ez env_setz]. subst E'. rewrite ez_setz, Pos.eqb_refl. lia. }
          assert (N2 : pfact_ok CS E' (FGe (eadd (ELit (two64 - 1)) (emulc (-1) (eatom (EZv (s_nx ss))))))).
          { cbn -[eadd eatom emulc ez env_setz two64]. rewrite zdenp_ok, eadd_den, emulc_den, eatom_den. cbn -[ez env_setz two64]. subst E'.
            rewrite ez_setz, Pos.eqb_refl. unfold two64. lia. }
          apply add_pfs_pfok; [cbn [s_pf bump]; exact OLD|]. unfold fs. constructor; [exact N1|]. constructor; [exact N2|]. exact EXTRA.
        + subst E'. rewrite (wden_setz (s_nx ss) (bv_unsigned V) (s_W ss) WW). lx_refm E ss. refine (conj MU (conj WM (conj MI _))).
          cbn [next_pc set_pc s_same]. rewrite WS4, add_pfs_same. cbn [s_same bump]. exact SM.
    Qed.

    Lemma havoc_rd_ok : forall ss m pc sz (rd : bv 5) (V : word),
      INV E ss m -> s_pc ss = PCz pc -> length (s_rs ss) = 31%nat ->
      step_accesses segs (ms_den segs G E ss m) =
        MachineOk (@mkAccessReport _ (MS_of_core (rset rd V (with_pc (Z_to_bv 64 pc + Z_to_bv 64 sz) (Core (regs_den E (s_rs ss)) F (Z_to_bv 64 pc) fc None))) m ro) []) ->
      sres_ok ss m (havoc_rd ss (bv_unsigned rd) pc sz).
    Proof. intros. unfold havoc_rd. apply havoc_rd_with_ok with (V := V); try assumption. constructor. Qed.

    Lemma havoc_rd_scaled_ok : forall ss m pc sz (rd : bv 5) (V : word) k x extra,
      INV E ss m -> s_pc ss = PCz pc -> length (s_rs ss) = 31%nat ->
      step_accesses segs (ms_den segs G E ss m) =
        MachineOk (@mkAccessReport _ (MS_of_core (rset rd V (with_pc (Z_to_bv 64 pc + Z_to_bv 64 sz) (Core (regs_den E (s_rs ss)) F (Z_to_bv 64 pc) fc None))) m ro) []) ->
      bv_unsigned V = k * x ->
      Forall (pfact_ok CS (env_setz E (s_nx ss) x)) extra ->
      sres_ok ss m (havoc_rd_scaled ss (bv_unsigned rd) k extra pc sz).
    Proof.
      intros ss m pc sz rd V k x extra HI Hpc Hlen Hst HV EXTRA. pose proof HI as (HM & HP & MU & WM & MI & SM).
      unfold havoc_rd_scaled. cbn [sres_ok].
      set (ev := emulc k (eatom (EZv (s_nx ss)))).
      set (fs := [FGe ev; FGe (eadd (ELit (two64 - 1)) (emulc (-1) ev))] ++ extra).
      destruct (add_pfs_rs (bump ss) fs) as (P1 & P2 & P3 & P4 & P5). cbn [s_rs s_pc s_mf s_nx bump] in P1, P2, P3, P4.
      split. { cbn [s_rs next_pc set_pc]. rewrite wr_reg_len, P1. exact Hlen. }
      intros WF. exists m, x.
      unfold ss_wf in WF. apply andb_prop in WF as [WF WSB]. apply andb_prop in WF as [WF WW]. apply andb_prop in WF as [WF WP]. apply andb_prop in WF as [WF WM']. apply andb_prop in WF as [WPC WR].
      set (E' := env_setz E (s_nx ss) x).
      assert (EVD : zden E' ev = bv_unsigned V).
      { subst ev E'. rewrite emulc_den, eatom_den. cbn [zden]. rewrite ez_setz, Pos.eqb_refl. lia. }
      destruct (wr_reg_same (add_pfs (bump ss) fs) (bv_unsigned rd) (RZ ev)) as (W1 & W2 & W3 & W4 & W5). pose proof (wr_reg_sm (add_pfs (bump ss) fs) (bv_unsigned rd) (RZ ev)) as WS4.
      split.
      - split; [reflexivity|]. exists []. split; [|apply acc_ok_nil]. rewrite Hst.
        unfold ms_den, next_pc, set_pc. cbn [s_rs s_pc pc_den].
        rewrite (wr_reg_rs_ext _ ss) by exact P1.
        rewrite <- (regs_den_setz (s_nx ss) x (s_rs ss) WR).
        rewrite (rset_den E' ss rd _ (RZ ev)); [| exact Hlen |].
        2:{ cbn [rden]. rewrite zdenp_ok, EVD. apply w64_of_unsigned. }
        rewrite w64_add. reflexivity.
      - unfold INV. cbn [s_mf s_pf s_W next_pc set_pc]. rewrite W1, W2, W5, P3, P5. cbn [s_W bump]. split; [|split].
        + apply Forall_mf_setz; assumption.
        + assert (OLD : Forall (pfact_ok CS E') (s_pf ss)) by (apply Forall_pf_setz; assumption).
          pose proof (bv_unsigned_in_range 64 V) as VR. unfold bv_modulus in VR. cbn [Z.of_N] in VR.
          assert (N1 : pfact_ok CS E' (FGe ev)).
          { unfold pfact_ok. rewrite zdenp_ok, EVD. lia. }
          assert (N2 : pfact_ok CS E' (FGe (eadd (ELit (two64 - 1)) (emulc (-1) ev)))).
          { unfold pfact_ok. rewrite zdenp_ok, eadd_den, emulc_den, EVD. cbn [zden]. unfold two64. lia. }
          apply add_pfs_pfok; [cbn [s_pf bump]; exact OLD|]. unfold fs. constructor; [exact N1|]. constructor; [exact N2|]. exact EXTRA.
        + subst E'. rewrite (wden_setz (s_nx ss) x (s_W ss) WW). lx_refm E ss. refine (conj MU (conj WM (conj MI _))).
          cbn [next_pc set_pc s_same]. rewrite WS4, add_pfs_same. cbn [s_same bump]. exact SM.
    Qed.

    Lemma elow_vars_lt : forall O n e k, evars_lt n e = true -> evars_lt n (elow O e k) = true.
    Proof.
      intros O n e k H. unfold elow. destruct (is_lit e); [reflexivity|]. destruct (e_in O e 0 (2 ^ k - 1)); [exact H|].
      cbn. rewrite H. reflexivity.
    Qed.

    (* [comment removed for export] *)
    Lemma finish_rd_ok : forall ss m pc sz (rd : bv 5) e (V : word),
      INV E ss m -> s_pc ss = PCz pc -> length (s_rs ss) = 31%nat ->
      Z_to_bv 64 (zden E e) = V ->
      step_accesses segs (ms_den segs G E ss m) =
        MachineOk (@mkAccessReport _ (MS_of_core (rset rd V (with_pc (Z_to_bv 64 pc + Z_to_bv 64 sz) (Core (regs_den E (s_rs ss)) F (Z_to_bv 64 pc) fc None))) m ro) []) ->
      sres_ok ss m (finish_rd ss (bv_unsigned rd) e pc sz).
    Proof.
      intros ss m pc sz rd e V HI Hpc Hlen Hv Hst. unfold finish_rd.
      destruct (ebig e).
      { apply havoc_rd_with_ok with (V := V); try assumption. unfold def_fact.
        destruct (evars_lt (s_nx ss) e) eqn:WE; [|constructor]. constructor; [|constructor].
        pose proof HI as (_ & HP & _). pose proof (mk_oracle_sound CS E _ HP) as HO.
        unfold pfact_ok. rewrite !zdenp_ok, eatom_den. cbn [zden]. rewrite ez_setz, Pos.eqb_refl.
        rewrite (zden_setz _ _ _ (elow_vars_lt _ _ _ 64 WE)). unfold oracle_of. rewrite (elow_den E (mk_oracle (s_pf ss)) HO e 64) by lia.
        rewrite <- Hv, Z_to_bv_unsigned. unfold bv_wrap. reflexivity. }
      cbn [sres_ok].
      split. { unfold next_pc, set_pc. cbn. rewrite wr_reg_len. exact Hlen. }
      destruct (wr_reg_same ss (bv_unsigned rd) (mkreg e)) as (W1 & W2 & W3 & W4 & W5). pose proof (wr_reg_sm ss (bv_unsigned rd) (mkreg e)) as WS1.
      exists m. split; [|eapply INV_same; [..|exact HI|lx_ref_eq]; unfold next_pc, set_pc; cbn; assumption].
      split; [reflexivity|]. exists []. split; [|apply acc_ok_nil].
      rewrite Hst. unfold ms_den, next_pc, set_pc. cbn [s_rs s_pc pc_den].
      rewrite (rset_den E ss rd V (mkreg e)); [| exact Hlen | rewrite mkreg_den; exact Hv].
      rewrite w64_add. reflexivity.
    Qed.

    Lemma do_slt_ok : forall D ss m pc sz (rd : bv 5) k a b (VA VB : word),
      INV E ss m -> s_pc ss = PCz pc -> length (s_rs ss) = 31%nat -> k <> KEq ->
      Z_to_bv 64 (zden E a) = VA -> Z_to_bv 64 (zden E b) = VB ->
      step_accesses segs (ms_den segs G E ss m) =
        MachineOk (@mkAccessReport _ (MS_of_core (rset rd (alu64 (match k with KLts => ALU_SLT | _ => ALU_SLTU end) VA VB)
                     (with_pc (Z_to_bv 64 pc + Z_to_bv 64 sz) (Core (regs_den E (s_rs ss)) F (Z_to_bv 64 pc) fc None))) m ro) []) ->
      sres_ok ss m (do_slt D ss k (bv_unsigned rd) a b pc sz).
    Proof.
      intros D ss m pc sz rd k a b VA VB HI Hpc Hlen Hk Ha Hb Hst.
      pose proof HI as (HM & HP & MU & WM & MI & SM). pose proof (mk_oracle_sound CS E _ HP) as HO.
      rewrite <- Ha, <- Hb, alu_slt_den in Hst by exact Hk.
      unfold do_slt. unfold oracle_of.
      destruct (decide_kind (mk_oracle (s_pf ss)) (s_pf ss) k a b) as [r|] eqn:DK.
      - rewrite (decide_kind_sound E (s_pf ss) k a b r HP DK) in Hst.
        destruct r; (eapply finish_rd_ok; [exact HI| exact Hpc| exact Hlen| reflexivity | exact Hst]).
      - destruct (D pc) as [[| |]|].
        + (* [comment removed for export] *) cbn [sres_ok].
          destruct (wr_reg_same (add_pfs ss (cond_facts (mk_oracle (s_pf ss)) (CN false k a b) true)) (bv_unsigned rd) (RZ (ELit 1))) as (T1 & T2 & T3 & T4 & T4'). pose proof (wr_reg_sm (add_pfs ss (cond_facts (mk_oracle (s_pf ss)) (CN false k a b) true)) (bv_unsigned rd) (RZ (ELit 1))) as WS2.
          destruct (wr_reg_same (add_pfs ss (cond_facts (mk_oracle (s_pf ss)) (CN false k a b) false)) (bv_unsigned rd) (RZ (ELit 0))) as (F1 & F2 & F3 & F4 & F4'). pose proof (wr_reg_sm (add_pfs ss (cond_facts (mk_oracle (s_pf ss)) (CN false k a b) false)) (bv_unsigned rd) (RZ (ELit 0))) as WS3.
          destruct (add_pfs_rs ss (cond_facts (mk_oracle (s_pf ss)) (CN false k a b) true)) as (T5 & T6 & T7 & T8 & T8').
          destruct (add_pfs_rs ss (cond_facts (mk_oracle (s_pf ss)) (CN false k a b) false)) as (F5 & F6 & F7 & F8 & F8').
          split. { unfold next_pc, set_pc. cbn [s_rs]. rewrite wr_reg_len, T5. exact Hlen. }
          split. { unfold next_pc, set_pc. cbn [s_rs]. rewrite wr_reg_len, F5. exact Hlen. }
          exists m.
          pose proof (cond_facts_sound E (s_pf ss) (CN false k a b) HP) as CF. cbn [cnden xorb] in CF |- *. rewrite !zdenp_ok in CF |- *.
          destruct (kden k (zden E a) (zden E b)) eqn:KD.
          * split.
            -- split; [reflexivity|]. exists []. split; [|apply acc_ok_nil]. rewrite Hst.
               unfold ms_den, next_pc, set_pc. cbn [s_rs s_pc pc_den].
               rewrite (wr_reg_rs_ext _ ss) by exact T5. rewrite (rset_den E ss rd _ (RZ (ELit 1))); [| exact Hlen | reflexivity].
               rewrite w64_add. reflexivity.
            -- pose proof (INV_pf ss m _ HI CF) as HI'. eapply INV_same; [..|exact HI'|lx_ref_eq]; unfold next_pc, set_pc; cbn [s_mf s_pf s_W]; assumption.
          * split.
            -- split; [reflexivity|]. exists []. split; [|apply acc_ok_nil]. rewrite Hst.
               unfold ms_den, next_pc, set_pc. cbn [s_rs s_pc pc_den].
               rewrite (wr_reg_rs_ext _ ss) by exact F5. rewrite (rset_den E ss rd _ (RZ (ELit 0))); [| exact Hlen | reflexivity].
               rewrite w64_add. reflexivity.
            -- pose proof (INV_pf ss m _ HI CF) as HI'. eapply INV_same; [..|exact HI'|lx_ref_eq]; unfold next_pc, set_pc; cbn [s_mf s_pf s_W]; assumption.
        + eapply finish_rd_ok; [exact HI| exact Hpc| exact Hlen| | exact Hst]. rewrite (kind_expr_den _ k a b HO Hk); reflexivity.
        + eapply finish_rd_ok; [exact HI| exact Hpc| exact Hlen| | exact Hst]. rewrite (kind_expr_den _ k a b HO Hk); reflexivity.
        + eapply finish_rd_ok; [exact HI| exact Hpc| exact Hlen| | exact Hst]. rewrite (kind_expr_den _ k a b HO Hk); reflexivity.
    Qed.
    Lemma interp_load : forall msz sx (addr : word) (rd : bv 5) (c : core) mm,
      interp_eff_accesses segs (load_val msz sx addr (fun v => EDone (rset rd v c))) mm =
      match ov_read_bytes segs mm addr (N.to_nat (msize_N msz)) with
      | Some bs => MachineOk (@mkAccessReport _ (rset rd (ld_val (msize_N msz) sx bs) c, mm) [(addr, N.to_nat (msize_N msz))])
      | None => MachineFault
      end.
    Proof.
      intros msz sx addr rd c mm. destruct msz; cbn -[ov_read_bytes rset ld_val le_bytes_to_word bv_extract sext zext];
        destruct (ov_read_bytes segs mm addr _); try reflexivity; destruct sx; reflexivity.
    Qed.

    Lemma interp_store : forall msz (addr v : word) (c : core) mm,
      interp_eff_accesses segs (store_val msz addr v (EDone c)) mm =
      if store_ok segs mm addr (N.to_nat (msize_N msz))
      then MachineOk (@mkAccessReport _ (c, write_to_mem mm addr (st_bytes (msize_N msz) v)) [(addr, N.to_nat (msize_N msz))])
      else MachineFault.
    Proof.
      intros msz addr v c mm. destruct msz; cbn -[store_ok write_to_mem Z_to_le_bytes st_bytes bv_unsigned bv_extract low32 N.to_nat msize_N width_bytes];
        cbn [msize_N N.to_nat width_bytes Pos.to_nat Pos.iter_op Nat.add];
        destruct (store_ok segs mm addr _); try reflexivity; cbn [st_bytes];
        first [rewrite store_bytes_1 | rewrite store_bytes_2 | rewrite store_bytes_4 | rewrite store_bytes_8]; reflexivity.
    Qed.

    Lemma okw_msize : forall msz, okw (msize_N msz) = true.
    Proof. intros []; reflexivity. Qed.

    Lemma exec_load : forall szw msz sx rd rs1 imm (c : core),
      exec szw (Load msz sx rd rs1 imm) c = load_val msz sx (rget c rs1 + sext 64 imm)%bv (fun v => EDone (rset rd v (with_pc (c_pc c + szw)%bv c))).
    Proof. reflexivity. Qed.

    Lemma exec_store : forall szw msz rs1 rs2 imm (c : core), c_resv c = None ->
      exec szw (Store msz rs1 rs2 imm) c = store_val msz (rget c rs1 + sext 64 imm)%bv (rget c rs2) (EDone (with_pc (c_pc c + szw)%bv c)).
    Proof. intros szw msz rs1 rs2 imm [R Fr p f rv] H. cbn in H. subst rv. reflexivity. Qed.
    Lemma zlow_bv : forall x, Z_to_bv 64 (zlow 64 x) = Z_to_bv 64 x.
    Proof. intros x. apply w64_eq. unfold zlow. rewrite Z.mod_mod by lia. reflexivity. Qed.

    (* [comment removed for export] *)

    (* [comment removed for export] *)
    Lemma land_align_down : forall x j, 0 <= x < 2^64 -> 0 <= j <= 64 ->
      Z.land x (2^64 - 2^j) = x - x mod 2^j.
    Proof.
      intros x j Hx Hj.
      replace (2^64 - 2^j)%Z with (Z.ldiff (Z.ones 64) (Z.ones j)).
      2:{ rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
          unfold Z.ones. rewrite Z.shiftl_mul_pow2 by lia.
          replace (2^64)%Z with (2^j * 2^(64-j))%Z by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
          replace (Z.pred (1 * (2 ^ j * 2 ^ (64 - j))))%Z with ((2^(64-j) - 1) * 2^j + (2^j - 1))%Z by lia.
          rewrite Z.div_add_l by lia. rewrite Z.div_small by (split; [lia| apply Z.lt_pred_l || lia]). lia. }
      rewrite Z.ldiff_land, Z.land_assoc. rewrite <- Z.ldiff_land.
      rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
      rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
      pose proof (Z.div_mod x (2^j) ltac:(lia)). lia.
    Qed.

    Lemma alu_extra_ok : forall ss op a b (A B : word),
      Forall (pfact_ok CS E) (s_pf ss) ->
      A = Z_to_bv 64 (zden E a) -> B = Z_to_bv 64 (zden E b) ->
      Forall (pfact_ok CS (env_setz E (s_nx ss) (bv_unsigned (alu64 op A B)))) (alu_extra (mk_oracle (s_pf ss)) op a b (s_nx ss)).
    Proof.
      intros ss op a b A B HP -> ->. unfold alu_extra.
      destruct op; try constructor. destruct (is_lit a) eqn:LA; [constructor|]. destruct (is_lit b) as [mm|] eqn:LB; [|constructor].
      destruct (high_mask_j mm) as [j|] eqn:HMJ; [|constructor].
      match goal with |- Forall _ (if ?c then _ else _) => destruct c eqn:CND; [|constructor] end.
      apply andb_prop in CND as [CND WA]. apply andb_prop in CND as [CND AL0]. apply andb_prop in CND as [CND J63]. apply andb_prop in CND as [U64 J1].
      apply Z.leb_le in J1. apply Z.leb_le in J63.
      pose proof (high_mask_j_ok mm j HMJ) as [J0 Hm].
      apply is_lit_den with (E := E) in LB.
      pose proof (e_in_sound E (mk_oracle (s_pf ss)) a 0 (two64 - 1) (mk_oracle_sound CS E (s_pf ss) HP) U64) as Ha. unfold two64 in Ha.
      set (x := zden E a) in *. set (v := bv_unsigned (alu64 ALU_AND (Z_to_bv 64 x) (Z_to_bv 64 (zden E b)))).
      assert (Hv : v = x - x mod 2 ^ j).
      { subst v. cbn [alu64 alu]. rewrite w64_and, Z_to_bv_unsigned, LB, Hm.
        unfold bv_wrap, bv_modulus. cbn [Z.of_N].
        rewrite <- land_mod_pow2 by lia.
        replace ((- 2 ^ j) mod 2 ^ 64) with (2 ^ 64 - 2 ^ j).
        2:{ replace (- 2 ^ j) with ((2 ^ 64 - 2 ^ j) + (-1) * 2 ^ 64) by lia. rewrite Z.mod_add by lia.
            rewrite Z.mod_small; [reflexivity|]. split; [|lia]. assert (2 ^ j <= 2 ^ 63) by (apply Z.pow_le_mono_r; lia).
            change (2 ^ 64) with (2 * 2 ^ 63). lia. }
        rewrite (Z.mod_small x) by lia. apply land_align_down; lia. }
      assert (EV : ez (env_setz E (s_nx ss) v) (s_nx ss) = v) by (rewrite ez_setz, Pos.eqb_refl; reflexivity).
      assert (EA : zden (env_setz E (s_nx ss) v) a = x) by (subst x; apply zden_setz; exact WA).
      pose proof (Z.mod_pos_bound x (2 ^ j) ltac:(lia)) as MB.
      constructor; [|constructor; [|constructor; [|constructor]]].
      - cbn -[esub eatom ez env_setz zden]. rewrite zdenp_ok. unfold esub. rewrite eadd_den, emulc_den, eatom_den, EA. cbn -[ez env_setz Z.mul Z.add Z.sub Z.modulo Z.pow]. rewrite EV. lia.
      - cbn -[esub eadd eatom ez env_setz zden]. rewrite zdenp_ok. unfold esub. rewrite !eadd_den, emulc_den, eatom_den, EA. cbn -[ez env_setz Z.mul Z.add Z.sub Z.modulo Z.pow]. rewrite EV. lia.
      - cbn -[ez env_setz Z.pow Z.modulo Z.of_N Z.to_N]. rewrite EV, Z2N.id by lia. rewrite Hv.
        rewrite Zminus_mod, Z.mod_mod, Z.sub_diag by lia. reflexivity.
    Qed.

    Lemma align_down_ok : forall ss op a b j (A B : word),
      Forall (pfact_ok CS E) (s_pf ss) ->
      A = Z_to_bv 64 (zden E a) -> B = Z_to_bv 64 (zden E b) ->
      align_down (mk_oracle (s_pf ss)) op a b (s_nx ss) = Some j ->
      bv_unsigned (alu64 op A B) = 2 ^ j * (bv_unsigned (alu64 op A B) / 2 ^ j)
      /\ Forall (pfact_ok CS (env_setz E (s_nx ss) (bv_unsigned (alu64 op A B) / 2 ^ j))) (align_facts a j (s_nx ss)).
    Proof.
      intros ss op a b j A B HP -> -> AD. unfold align_down in AD.
      destruct op; try discriminate. destruct (is_lit a) eqn:LA; [discriminate|]. destruct (is_lit b) as [mm|] eqn:LB; [|discriminate].
      destruct (high_mask_j mm) as [j'|] eqn:HMJ; [|discriminate].
      match type of AD with (if ?c then _ else _) = _ => destruct c eqn:CND; [|discriminate] end. injection AD; intros <-.
      apply andb_prop in CND as [CND WA]. apply andb_prop in CND as [CND AL0]. apply andb_prop in CND as [CND J63]. apply andb_prop in CND as [U64 J1].
      apply Z.leb_le in J1. apply Z.leb_le in J63.
      pose proof (high_mask_j_ok mm j' HMJ) as [J0 Hm].
      apply is_lit_den with (E := E) in LB.
      pose proof (e_in_sound E (mk_oracle (s_pf ss)) a 0 (two64 - 1) (mk_oracle_sound CS E (s_pf ss) HP) U64) as Ha. unfold two64 in Ha.
      set (x := zden E a) in *. set (v := bv_unsigned (alu64 ALU_AND (Z_to_bv 64 x) (Z_to_bv 64 (zden E b)))).
      assert (Hv : v = x - x mod 2 ^ j').
      { subst v. cbn [alu64 alu]. rewrite w64_and, Z_to_bv_unsigned, LB, Hm.
        unfold bv_wrap, bv_modulus. cbn [Z.of_N].
        rewrite <- land_mod_pow2 by lia.
        replace ((- 2 ^ j') mod 2 ^ 64) with (2 ^ 64 - 2 ^ j').
        2:{ replace (- 2 ^ j') with ((2 ^ 64 - 2 ^ j') + (-1) * 2 ^ 64) by lia. rewrite Z.mod_add by lia.
            rewrite Z.mod_small; [reflexivity|]. split; [|lia]. assert (2 ^ j' <= 2 ^ 63) by (apply Z.pow_le_mono_r; lia).
            change (2 ^ 64) with (2 * 2 ^ 63). lia. }
        rewrite (Z.mod_small x) by lia. apply land_align_down; lia. }
      pose proof (Z.mod_pos_bound x (2 ^ j') ltac:(lia)) as MB. pose proof (Z.div_mod x (2 ^ j') ltac:(lia)) as DM.
      assert (Hq : v = 2 ^ j' * (x / 2 ^ j')) by lia.
      assert (Hq' : v / 2 ^ j' = x / 2 ^ j') by (rewrite Hq, Z.mul_comm, Z.div_mul by lia; reflexivity).
      split; [rewrite Hq'; exact Hq|].
      set (E' := env_setz E (s_nx ss) (v / 2 ^ j')).
      assert (EA : zden E' a = x) by (subst x E'; apply zden_setz; exact WA).
      assert (EVz : ez E' (s_nx ss) = x / 2 ^ j') by (subst E'; rewrite ez_setz, Pos.eqb_refl; exact Hq').
      unfold align_facts. cbv zeta. constructor; [|constructor; [|constructor]].
      - unfold pfact_ok. rewrite zdenp_ok. unfold esub. rewrite !eadd_den, !emulc_den, !eatom_den, EA. cbn [zden]. rewrite EVz. lia.
      - unfold pfact_ok. rewrite zdenp_ok. unfold esub. rewrite !eadd_den, !emulc_den, !eatom_den, EA. cbn [zden]. rewrite EVz. lia.
    Qed.

    (* [comment removed for export] *)
    Lemma exec_amo : forall szw op wd aq rl rd rs1 rs2 (c : core), c_resv c = None ->
      exec szw (Amo op wd aq rl rd rs1 rs2) c =
        if negb (amo_aligned wd (rget c rs1)) then EFault c else
        match wd with
        | AW => ELoad 32 (rget c rs1) (fun old => EStore 32 (rget c rs1) (amo_val op old (low32 (rget c rs2)))
                  (EDone (rset rd (sext 64 old) (with_pc (c_pc c + szw)%bv c))))
        | AD => ELoad 64 (rget c rs1) (fun old => EStore 64 (rget c rs1) (amo_val op old (rget c rs2))
                  (EDone (rset rd old (with_pc (c_pc c + szw)%bv c))))
        end.
    Proof. intros szw op wd aq rl rd rs1 rs2 [R Fr p f rv] H. cbn in H. subst rv. destruct wd; reflexivity. Qed.

    Lemma interp_amo32 : forall (a : word) rd (f : bv 32 -> bv 32) (c : core) mm,
      interp_eff_accesses segs (ELoad 32 a (fun old => EStore 32 a (f old) (EDone (rset rd (sext 64 old) c)))) mm =
      match ov_read_bytes segs mm a 4 with
      | Some bs => let old := bv_extract 0 32 (le_bytes_to_word bs) in
          if store_ok segs mm a 4
          then MachineOk (@mkAccessReport _ (rset rd (sext 64 old) c, write_to_mem mm a (Z_to_le_bytes 4 (bv_unsigned (f old)))) [(a, 4%nat); (a, 4%nat)])
          else MachineFault
      | None => MachineFault
      end.
    Proof.
      intros a rd f c mm. cbn -[ov_read_bytes rset sext store_ok write_to_mem Z_to_le_bytes bv_unsigned bv_extract le_bytes_to_word].
      destruct (ov_read_bytes segs mm a 4); [|reflexivity]. destruct (store_ok segs mm a 4); reflexivity.
    Qed.

    Lemma interp_amo64 : forall (a : word) rd (f : bv 64 -> bv 64) (c : core) mm,
      interp_eff_accesses segs (ELoad 64 a (fun old => EStore 64 a (f old) (EDone (rset rd old c)))) mm =
      match ov_read_bytes segs mm a 8 with
      | Some bs => let old := bv_extract 0 64 (le_bytes_to_word bs) in
          if store_ok segs mm a 8
          then MachineOk (@mkAccessReport _ (rset rd old c, write_to_mem mm a (Z_to_le_bytes 8 (bv_unsigned (f old)))) [(a, 8%nat); (a, 8%nat)])
          else MachineFault
      | None => MachineFault
      end.
    Proof.
      intros a rd f c mm. cbn -[ov_read_bytes rset store_ok write_to_mem Z_to_le_bytes bv_unsigned bv_extract le_bytes_to_word].
      destruct (ov_read_bytes segs mm a 8); [|reflexivity]. destruct (store_ok segs mm a 8); reflexivity.
    Qed.

    Lemma w32_add : forall x y, (Z_to_bv 32 x + Z_to_bv 32 y)%bv = Z_to_bv 32 (x + y).
    Proof. intros. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. apply bv_wrap_add_idemp. Qed.
    Lemma w32_or : forall x y, bv_or (Z_to_bv 32 x) (Z_to_bv 32 y) = Z_to_bv 32 (Z.lor x y).
    Proof. intros. apply bv_eq. rewrite bv_or_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. apply lor_mod_pow2. cbn; lia. Qed.
    Lemma w32_xor : forall x y, bv_xor (Z_to_bv 32 x) (Z_to_bv 32 y) = Z_to_bv 32 (Z.lxor x y).
    Proof. intros. apply bv_eq. rewrite bv_xor_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. apply lxor_mod_pow2. cbn; lia. Qed.
    Lemma w32_eq_mod64 : forall x y, x mod 2 ^ 64 = y mod 2 ^ 64 -> Z_to_bv 32 x = Z_to_bv 32 y.
    Proof.
      intros x y H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
      rewrite <- (mod_mod_pow2 x 32 64), <- (mod_mod_pow2 y 32 64) by lia. rewrite H. reflexivity.
    Qed.

    Lemma amo_expr_sound64 : forall pf op oe se v, Forall (pfact_ok CS E) pf ->
      amo_expr (mk_oracle pf) op oe se = Some v ->
      amo_val op (Z_to_bv 64 (zden E oe)) (Z_to_bv 64 (zden E se)) = Z_to_bv 64 (zden E v).
    Proof.
      intros pf op oe se v HP H. pose proof (mk_oracle_sound CS E pf HP) as HO.
      destruct op; cbn [amo_expr] in H; try discriminate; injection H; intros <-; cbn [amo_val].
      - reflexivity.
      - rewrite w64_add, eadd_den. reflexivity.
      - rewrite w64_xor. apply w64_eq. symmetry. apply exor_den.
      - rewrite w64_and, (eand_den E _ HO). reflexivity.
      - rewrite w64_or, (eor_den E _ HO). reflexivity.
    Qed.

    Lemma amo_expr_sound32 : forall pf op oe se v, Forall (pfact_ok CS E) pf ->
      amo_expr (mk_oracle pf) op oe se = Some v ->
      amo_val op (low32 (Z_to_bv 64 (zden E oe))) (low32 (Z_to_bv 64 (zden E se))) = low32 (Z_to_bv 64 (zden E v)).
    Proof.
      intros pf op oe se v HP H. pose proof (mk_oracle_sound CS E pf HP) as HO. rewrite !low32_lit.
      destruct op; cbn [amo_expr] in H; try discriminate; injection H; intros <-; cbn [amo_val].
      - reflexivity.
      - rewrite w32_add, eadd_den. reflexivity.
      - rewrite w32_xor. apply w32_eq_mod64. symmetry. apply exor_den.
      - rewrite w32_and, (eand_den E _ HO). reflexivity.
      - rewrite w32_or, (eor_den E _ HO). reflexivity.
    Qed.

    Lemma low32_sext : forall x : bv 32, low32 (sext 64 x) = x.
    Proof.
      intros x. unfold low32. apply bv_eq. rewrite extract_low_mod by lia. rewrite sext_small. rewrite Z_to_bv_unsigned.
      unfold bv_wrap, bv_modulus. cbn [Z.of_N]. rewrite mod_mod_pow2 by lia.
      unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N].
      pose proof (bv_unsigned_in_range 32 x) as R. unfold bv_modulus in R. cbn [Z.of_N] in R.
      change (2 ^ 32 `div` 2) with (2 ^ 31).
      destruct (Z_lt_le_dec (bv_unsigned x) (2 ^ 31)).
      - rewrite (Z.mod_small (bv_unsigned x + 2 ^ 31)) by lia. replace (bv_unsigned x + 2 ^ 31 - 2 ^ 31) with (bv_unsigned x) by lia. apply Z.mod_small. lia.
      - replace ((bv_unsigned x + 2 ^ 31) mod 2 ^ 32) with (bv_unsigned x + 2 ^ 31 - 2 ^ 32).
        2:{ rewrite <- (Z.mod_add _ (-1)) by lia. symmetry. rewrite <- (Z.mod_small (bv_unsigned x + 2 ^ 31 - 2 ^ 32) (2 ^ 32)) by lia. f_equal. }
        replace (bv_unsigned x + 2 ^ 31 - 2 ^ 32 - 2 ^ 31) with (bv_unsigned x + (-1) * 2 ^ 32) by lia.
        rewrite Z.mod_add by lia. apply Z.mod_small. lia.
    Qed.

    Theorem sym_step_sound : forall D i sz ss pc w m,
      s_pc ss = PCz pc -> length (s_rs ss) = 31%nat ->
      fetch_word segs (Z_to_bv 64 pc) = Some w -> is_ecall w = false -> decode_any w = Some (i, sz) ->
      INV E ss m -> sres_ok ss m (sym_step C D i sz ss).
    Proof.
      intros D i sz ss pc w m Hpc Hlen HF HE HD HI.
      pose proof HI as (HM & HP & MU & WM & MI & SM).
      pose proof (mk_oracle_sound CS E _ HP) as HO.
      assert (STEP : step_accesses segs (ms_den segs G E ss m)
                      = liftA ro (interp_eff_accesses segs (exec (Z_to_bv 64 sz) i (Core (regs_den E (s_rs ss)) F (Z_to_bv 64 pc) fc None)) m)).
      { unfold ms_den. rewrite Hpc. cbn [pc_den]. apply (step_accesses_gen segs _ F (Z_to_bv 64 pc) fc None m ro w i sz HF HE HD). }
      set (CORE := Core (regs_den E (s_rs ss)) F (Z_to_bv 64 pc) fc None) in *.
      assert (RG : forall r, rget CORE r = Z_to_bv 64 (zden E (rd_expr ss (bv_unsigned r)))).
      { intros r. apply rget_den. exact Hlen. }
      assert (HAVOC : forall (rd : bv 5) (V : word),
        step_accesses segs (ms_den segs G E ss m) =
          MachineOk (@mkAccessReport _ (MS_of_core (rset rd V (with_pc (Z_to_bv 64 pc + Z_to_bv 64 sz) CORE)) m ro) []) ->
        sres_ok ss m (havoc_rd ss (bv_unsigned rd) pc sz)).
      { intros rd V Hst. subst CORE. exact (havoc_rd_ok ss m pc sz rd V HI Hpc Hlen Hst). }
      subst CORE.
      unfold sym_step. rewrite Hpc. unfold ridx.
      destruct i; try exact I.
      - (* [comment removed for export] *) apply (finish_rd_ok ss m pc sz _ _ (sext 64 (bv_concat 32 imm (Z_to_bv 12 0)) : word)); first [assumption | rewrite STEP; reflexivity | idtac]. cbn [zden]. unfold zlui. apply w64_of_unsigned.
      - (* [comment removed for export] *) apply (finish_rd_ok ss m pc sz _ _ (Z_to_bv 64 pc + sext 64 (bv_concat 32 imm (Z_to_bv 12 0)))%bv); first [assumption | rewrite STEP; reflexivity | idtac].
        cbn [zden]. unfold zlui. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold zlow, bv_wrap, bv_modulus. cbn [Z.of_N].
        rewrite Z.mod_mod by lia. rewrite Zplus_mod_idemp_l. reflexivity.
      - (* [comment removed for export] *) cbn [sres_ok]. split. { cbn [s_rs set_pc]. rewrite wr_reg_len. exact Hlen. }
        exists m. split.
        + split; [reflexivity|]. exists []. split; [|apply acc_ok_nil]. rewrite STEP.
          unfold ms_den. cbn -[Z_to_bv regs_den bv_add sext zlow rset MS_of_core with_pc wr_reg].
          cbn [s_rs s_pc set_pc pc_den].
          rewrite (rset_den E ss rd _ (RZ (ELit (zlow 64 (pc + sz))))); [| exact Hlen | cbn [rden zdenp]; rewrite w64_add; apply zlow_bv].
          rewrite sext_small, w64_add, !zlow_bv. reflexivity.
        + destruct (wr_reg_same ss (bv_unsigned rd) (RZ (ELit (zlow 64 (pc + sz))))) as (W1 & W2 & W3 & W4 & W5). pose proof (wr_reg_sm ss (bv_unsigned rd) (RZ (ELit (zlow 64 (pc + sz))))) as WS5.
          eapply INV_same; [..|exact HI|lx_ref_eq]; cbn [s_mf s_pf s_W set_pc]; assumption.
      - (* [comment removed for export] *)
        assert (LITCASE : forall r immz, rd_reg ss (bv_unsigned rs1) = r -> bv_signed imm = immz ->
          sres_ok ss m match is_lit (expr_of_reg r) with
            | Some t => SNext (set_pc (wr_reg ss (bv_unsigned rd) (RZ (ELit (zlow 64 (pc + sz))))) (PCz (Z.land (zlow 64 (t + immz)) (Z.lnot 1))))
            | None => SFail 2 end).
        { intros r immz Hr Himm. destruct (is_lit (expr_of_reg r)) as [t|] eqn:LT; [|exact I].
          apply is_lit_den with (E := E) in LT.
          cbn [sres_ok]. split. { cbn [s_rs set_pc]. rewrite wr_reg_len. exact Hlen. }
          exists m. split.
          + split; [reflexivity|]. exists []. split; [|apply acc_ok_nil]. rewrite STEP.
            unfold ms_den. cbn -[Z_to_bv regs_den bv_add sext zlow rset MS_of_core with_pc wr_reg bv_and bv_not w1 rget Z.land Z.lnot].
            cbn [s_rs s_pc set_pc pc_den].
            rewrite (rset_den E ss rd _ (RZ (ELit (zlow 64 (pc + sz))))); [| exact Hlen | cbn [rden zdenp]; rewrite w64_add; apply zlow_bv].
            rewrite RG. unfold rd_expr. rewrite Hr, LT, sext_small, Himm, w64_add.
            unfold w1. replace (bv_not (Z_to_bv 64 1)) with (Z_to_bv 64 (Z.lnot 1) : word) by (apply bv_eq; reflexivity).
            rewrite w64_and.
            replace (Z_to_bv 64 (Z.land (zlow 64 (t + immz)) (Z.lnot 1))) with (Z_to_bv 64 (Z.land (t + immz) (Z.lnot 1)) : word); [reflexivity|].
            apply w64_eq. unfold zlow. rewrite <- (land_mod_pow2 (t + immz)), <- (land_mod_pow2 ((t + immz) mod 2 ^ 64)), Z.mod_mod by lia. reflexivity.
          + destruct (wr_reg_same ss (bv_unsigned rd) (RZ (ELit (zlow 64 (pc + sz))))) as (W1 & W2 & W3 & W4 & W5). pose proof (wr_reg_sm ss (bv_unsigned rd) (RZ (ELit (zlow 64 (pc + sz))))) as WS6.
            eapply INV_same; [..|exact HI|lx_ref_eq]; cbn [s_mf s_pf s_W set_pc]; assumption. }
        destruct (rd_reg ss (bv_unsigned rs1)) as [j|e] eqn:HR.
        + destruct (bv_unsigned rd) as [|p|p] eqn:RD0; try (apply (LITCASE _ _ eq_refl eq_refl)).
          destruct (bv_signed imm) as [|q|q] eqn:IMM; try (apply (LITCASE _ _ eq_refl eq_refl)).
          (* [comment removed for export] *) cbn [sres_ok]. split; [exact Hlen|]. exists m. split.
          * split; [reflexivity|]. exists []. split; [|apply acc_ok_nil]. rewrite STEP.
            unfold ms_den. cbn -[Z_to_bv regs_den bv_add sext rset MS_of_core with_pc bv_and bv_not w1 rget].
            cbn [s_rs s_pc set_pc pc_den rden].
            unfold rset, is_x0. rewrite RD0. cbn [Z.eqb MS_of_core with_pc c_regs c_fregs c_pc c_fcsr c_resv].
            unfold MS_of_core, with_pc. cbn [c_regs c_fregs c_pc c_fcsr c_resv].
            rewrite RG. unfold rd_expr. rewrite HR. rewrite expr_of_reg_den. cbn [rden]. rewrite sext_small, IMM.
            unfold ret_pc, w1. replace (ew E j + Z_to_bv 64 0)%bv with (ew E j); [reflexivity|].
            symmetry. apply bv_eq. rewrite bv_add_unsigned, Z_to_bv_unsigned. cbn. rewrite Z.add_0_r.
            rewrite bv_wrap_small; [reflexivity| apply bv_unsigned_in_range].
          * eapply INV_same; [..|exact HI|lx_ref_eq]; reflexivity.
        + apply (LITCASE _ _ eq_refl eq_refl).
      - (* [comment removed for export] *)
        unfold do_branch. destruct (ckind_of c) as [n k] eqn:CK. unfold oracle_of.
        set (cc := CN n k (rd_expr ss (bv_unsigned rs1)) (rd_expr ss (bv_unsigned rs2))).
        assert (BT : branch_taken c (rget (Core (regs_den E (s_rs ss)) F (Z_to_bv 64 pc) fc None) rs1)
                                    (rget (Core (regs_den E (s_rs ss)) F (Z_to_bv 64 pc) fc None) rs2) = cnden E cc).
        { rewrite !RG. subst cc. cbn [cnden]. rewrite !zdenp_ok. apply branch_taken_den. exact CK. }
        assert (MSTEP : forall b ss', cnden E cc = b -> s_rs ss' = s_rs ss ->
                  s_pc ss' = PCz (if b then pc + bv_signed imm else pc + sz) ->
                  mstepA segs L CS (ms_den segs G E ss m) (ms_den segs G E ss' m)).
        { intros b ss' Hb Hrs Hpc'. split; [reflexivity|]. exists []. split; [|apply acc_ok_nil]. rewrite STEP.
          unfold ms_den. rewrite Hrs, Hpc'. cbn -[Z_to_bv regs_den bv_add sext rget branch_taken].
          rewrite BT, Hb, sext_small, !w64_add. destruct b; reflexivity. }
        destruct (decide_cond (mk_oracle (s_pf ss)) (s_pf ss) cc) as [b|] eqn:DC.
        + pose proof (decide_cond_sound E (s_pf ss) cc b HP DC) as Hb.
          destruct b; cbn [sres_ok]; (split; [exact Hlen|]); exists m; split;
            first [ eapply MSTEP; [exact Hb| reflexivity| reflexivity]
                  | eapply INV_same; [..|exact HI|lx_ref_eq]; reflexivity ].
        + cbn [sres_ok].
          destruct (add_pfs_rs ss (cond_facts (mk_oracle (s_pf ss)) cc true)) as (T5 & T6 & T7 & T8 & T8').
          destruct (add_pfs_rs ss (cond_facts (mk_oracle (s_pf ss)) cc false)) as (F5 & F6 & F7 & F8 & F8').
          split; [cbn [s_rs set_pc settle set_pf]; rewrite T5; exact Hlen|]. split; [cbn [s_rs set_pc settle set_pf]; rewrite F5; exact Hlen|].
          exists m. pose proof (cond_facts_sound E (s_pf ss) cc HP) as CF.
          assert (SETL : forall s1, INV E s1 m -> INV E (settle s1) m).
          { intros s1 (I1 & I2 & I3). split; [exact I1|]. split; [| exact I3]. cbn [settle set_pf s_pf]. apply (settle_seps_sound CS E). exact I2. }
          destruct (cnden E cc) eqn:CD; split.
          * eapply MSTEP; [reflexivity| cbn [s_rs set_pc settle set_pf]; exact T5 | reflexivity].
          * pose proof (SETL _ (INV_pf ss m _ HI CF)) as HI'. eapply INV_same; [..|exact HI'|lx_ref_eq]; cbn [s_mf s_pf s_W set_pc]; reflexivity.
          * eapply MSTEP; [reflexivity| cbn [s_rs set_pc settle set_pf]; exact F5 | reflexivity].
          * pose proof (SETL _ (INV_pf ss m _ HI CF)) as HI'. eapply INV_same; [..|exact HI'|lx_ref_eq]; cbn [s_mf s_pf s_W set_pc]; reflexivity.
      - (* [comment removed for export] *)
        unfold do_load.
        set (a := eadd (rd_expr ss (bv_unsigned rs1)) (ELit (bv_signed imm))).
        destruct (acc_class C ss a (Z.of_N (msize_N sz0))) as [cl|] eqn:AC; [|exact I].
        pose proof (acc_class_sound E CFG ss a _ cl (or_intror (ex_intro _ m HM)) HP AC) as ACL.
        pose proof (acls_acc_ok E CFG cl (zden E a) (msize_N sz0) (okw_msize sz0) ACL) as AOK.
        assert (ADDR : (rget (Core (regs_den E (s_rs ss)) F (Z_to_bv 64 pc) fc None) rs1 + sext 64 imm)%bv = Z_to_bv 64 (zden E a)).
        { rewrite RG, sext_small, w64_add. subst a. rewrite eadd_den. reflexivity. }
        rewrite exec_load, ADDR, interp_load in STEP. cbn [c_pc] in STEP.
        pose proof (sym_load_sound segs L CS E m C (cfg_hsb E CFG) ss a (msize_N sz0) signed HM HP) as LS.
        destruct (sym_load C ss a (msize_N sz0) signed) as [r|lo hi|c oa on|] eqn:SL; cbn [lres_ok] in LS; [| | | exact I].
        + (* [comment removed for export] *) destruct LS as (bs & RD & VAL). rewrite RD in STEP.
          cbn [sres_ok]. split. { cbn [s_rs next_pc set_pc]. rewrite wr_reg_len. exact Hlen. }
          exists m. split.
          * split; [reflexivity|]. eexists. split; [|exact AOK]. rewrite STEP, liftA_ok.
            unfold ms_den, next_pc, set_pc. cbn [s_rs s_pc pc_den].
            rewrite (rset_den E ss rd _ r); [| exact Hlen | symmetry; exact VAL]. rewrite w64_add. reflexivity.
          * destruct (wr_reg_same ss (bv_unsigned rd) r) as (W1 & W2 & W3 & W4 & W5). pose proof (wr_reg_sm ss (bv_unsigned rd) r) as WS7.
            eapply INV_same; [..|exact HI|lx_ref_eq]; cbn [s_mf s_pf s_W next_pc set_pc]; assumption.
        + (* [comment removed for export] *) destruct LS as (bs & RD & (v & VAL & RANGE)). rewrite RD in STEP.
          cbn [sres_ok]. split. { cbn [s_rs next_pc set_pc]. rewrite wr_reg_len. destruct (add_pfs_rs (bump ss) [FGe (eadd (eatom (EZv (s_nx ss))) (ELit (- lo))); FGe (eadd (emulc (-1) (eatom (EZv (s_nx ss)))) (ELit hi))]) as (P1 & _). rewrite P1. exact Hlen. }
          intros WF. exists m, v.
          unfold ss_wf in WF. apply andb_prop in WF as [WF WSB]. apply andb_prop in WF as [WF WW]. apply andb_prop in WF as [WF WP]. apply andb_prop in WF as [WF WM']. apply andb_prop in WF as [WPC WR].
          set (E' := env_setz E (s_nx ss) v).
          set (fs := [FGe (eadd (eatom (EZv (s_nx ss))) (ELit (- lo))); FGe (eadd (emulc (-1) (eatom (EZv (s_nx ss)))) (ELit hi))]).
          destruct (add_pfs_rs (bump ss) fs) as (P1 & P2 & P3 & P4 & P5). cbn [s_rs s_pc s_mf s_nx bump] in P1, P2, P3, P4.
          destruct (wr_reg_same (add_pfs (bump ss) fs) (bv_unsigned rd) (RZ (eatom (EZv (s_nx ss))))) as (W1 & W2 & W3 & W4 & W5). pose proof (wr_reg_sm (add_pfs (bump ss) fs) (bv_unsigned rd) (RZ (eatom (EZv (s_nx ss))))) as WS8.
          split.
          * split; [reflexivity|]. eexists. split; [|exact AOK]. rewrite STEP, liftA_ok.
            unfold ms_den, next_pc, set_pc. cbn [s_rs s_pc pc_den].
            rewrite (wr_reg_rs_ext _ ss) by exact P1.
            rewrite <- (regs_den_setz (s_nx ss) v (s_rs ss) WR).
            rewrite (rset_den E' ss rd _ (RZ (eatom (EZv (s_nx ss))))); [| exact Hlen |].
            2:{ rewrite VAL. subst E'. cbn [rden zdenp eatom]. rewrite ez_setz, Pos.eqb_refl. reflexivity. }
            rewrite w64_add. reflexivity.
          * unfold INV. cbn [s_mf s_pf s_W next_pc set_pc]. rewrite W1, W2, W5, P3, P5. cbn [s_W bump]. split; [|split; [|]].
            -- apply Forall_mf_setz; assumption.
            -- unfold add_pfs, fs. cbn [fold_left add_pf s_pf bump].
               assert (OLD : Forall (pfact_ok CS E') (s_pf ss)) by (apply Forall_pf_setz; assumption).
               assert (N1 : pfact_ok CS E' (FGe (eadd (eatom (EZv (s_nx ss))) (ELit (- lo))))).
               { cbn -[eadd eatom ez env_setz]. rewrite zdenp_ok, eadd_den. cbn -[ez env_setz]. subst E'. rewrite ez_setz, Pos.eqb_refl. lia. }
               assert (N2 : pfact_ok CS E' (FGe (eadd (emulc (-1) (eatom (EZv (s_nx ss)))) (ELit hi)))).
               { cbn -[eadd eatom emulc ez env_setz]. rewrite zdenp_ok, eadd_den, emulc_den. cbn -[ez env_setz]. subst E'. rewrite ez_setz, Pos.eqb_refl. lia. }
               unfold pf_add. repeat (match goal with |- context [if ?c then _ else _] => destruct c end); repeat (constructor; try assumption); assumption.
            -- subst E'. rewrite (wden_setz (s_nx ss) v (s_W ss) WW). lx_refm E ss. refine (conj MU (conj WM (conj MI _))).
               cbn [next_pc set_pc s_same]. rewrite WS8, add_pfs_same. cbn [s_same bump]. exact SM.
        + (* [comment removed for export] *) destruct LS as (W1' & kb & RD & VAL & KR & SHB).
          replace (N.to_nat (msize_N sz0)) with 1%nat in * by (rewrite W1'; reflexivity). rewrite RD in STEP.
          destruct (evars_lt (s_nx ss) c) eqn:Vc; [|exact I]. destruct (evars_lt (s_nx ss) oa) eqn:Voa; [|exact I].
          destruct (evars_lt (s_nx ss) on) eqn:Von; [|exact I]. cbn [andb].
          set (fs := [FGe (eatom (EZv (s_nx ss))); FGe (eadd (emulc (-1) (eatom (EZv (s_nx ss)))) (ELit 7)); FShb (s_nx ss) c oa on]).
          destruct (add_pfs_rs (bump ss) fs) as (P1 & P2 & P3 & P4 & P5). cbn [s_rs s_pc s_mf s_nx bump] in P1, P2, P3, P4.
          cbn [sres_ok]. split. { cbn [s_rs next_pc set_pc]. rewrite wr_reg_len. rewrite P1. exact Hlen. }
          intros WF. exists m, (bv_unsigned kb).
          unfold ss_wf in WF. apply andb_prop in WF as [WF WSB]. apply andb_prop in WF as [WF WW]. apply andb_prop in WF as [WF WP]. apply andb_prop in WF as [WF WM']. apply andb_prop in WF as [WPC WR].
          set (E' := env_setz E (s_nx ss) (bv_unsigned kb)).
          destruct (wr_reg_same (add_pfs (bump ss) fs) (bv_unsigned rd) (RZ (eatom (EZv (s_nx ss))))) as (W1 & W2 & W3 & W4 & W5). pose proof (wr_reg_sm (add_pfs (bump ss) fs) (bv_unsigned rd) (RZ (eatom (EZv (s_nx ss))))) as WS9.
          split.
          * split; [reflexivity|]. eexists. split; [|exact AOK]. rewrite STEP, liftA_ok.
            unfold ms_den, next_pc, set_pc. cbn [s_rs s_pc pc_den].
            rewrite (wr_reg_rs_ext _ ss) by exact P1.
            rewrite <- (regs_den_setz (s_nx ss) (bv_unsigned kb) (s_rs ss) WR).
            rewrite (rset_den E' ss rd _ (RZ (eatom (EZv (s_nx ss))))); [| exact Hlen |].
            2:{ rewrite W1', VAL. subst E'. cbn [rden zdenp eatom]. rewrite ez_setz, Pos.eqb_refl. reflexivity. }
            rewrite w64_add. reflexivity.
          * unfold INV. cbn [s_mf s_pf s_W next_pc set_pc]. rewrite W1, W2, W5, P3, P5. cbn [s_W bump]. split; [|split; [|]].
            -- apply Forall_mf_setz; assumption.
            -- unfold add_pfs, fs. cbn [fold_left add_pf s_pf bump].
               assert (OLD : Forall (pfact_ok CS E') (s_pf ss)) by (apply Forall_pf_setz; assumption).
               assert (N1 : pfact_ok CS E' (FGe (eatom (EZv (s_nx ss))))).
               { cbn -[eatom ez env_setz]. rewrite zdenp_ok. cbn -[ez env_setz]. subst E'. rewrite ez_setz, Pos.eqb_refl. lia. }
               assert (N2 : pfact_ok CS E' (FGe (eadd (emulc (-1) (eatom (EZv (s_nx ss)))) (ELit 7)))).
               { cbn -[eadd eatom emulc ez env_setz]. rewrite zdenp_ok, eadd_den, emulc_den. cbn -[ez env_setz]. subst E'. rewrite ez_setz, Pos.eqb_refl. lia. }
               assert (N3 : pfact_ok CS E' (FShb (s_nx ss) c oa on)).
               { cbn -[zdenp ez env_setz]. subst E'. rewrite !zdenp_setz, !zdenp_ok by assumption. rewrite !ez_setz, Pos.eqb_refl.
                 exact SHB. }
               unfold pf_add. repeat (match goal with |- context [if ?cnd then _ else _] => destruct cnd end); repeat (constructor; try assumption); assumption.
            -- subst E'. rewrite (wden_setz (s_nx ss) (bv_unsigned kb) (s_W ss) WW). lx_refm E ss. refine (conj MU (conj WM (conj MI _))).
               cbn [next_pc set_pc s_same]. rewrite WS9, add_pfs_same. cbn [s_same bump]. exact SM.
      - (* [comment removed for export] *)
        unfold do_store.
        set (a := eadd (rd_expr ss (bv_unsigned rs1)) (ELit (bv_signed imm))).
        destruct (acc_class C ss a (Z.of_N (msize_N sz0))) as [cl|] eqn:AC; [|exact I].
        pose proof (acc_class_sound E CFG ss a _ cl (or_intror (ex_intro _ m HM)) HP AC) as ACL.
        pose proof (acls_acc_ok E CFG cl (zden E a) (msize_N sz0) (okw_msize sz0) ACL) as AOK.
        assert (ADDR : (rget (Core (regs_den E (s_rs ss)) F (Z_to_bv 64 pc) fc None) rs1 + sext 64 imm)%bv = Z_to_bv 64 (zden E a)).
        { rewrite RG, sext_small, w64_add. subst a. rewrite eadd_den. reflexivity. }
        rewrite exec_store, ADDR, interp_store in STEP by reflexivity. cbn [c_pc] in STEP.
        destruct (sym_store C cl ss a (msize_N sz0) (rd_reg ss (bv_unsigned rs2))) as [mf' W'|code] eqn:SS; [|exact I].
        destruct (sym_store_sound segs L CS E m C (cfg_hst E CFG) (cfg_hsb E CFG) HPF HBK cl ss a (msize_N sz0) (rd_reg ss (bv_unsigned rs2)) mf' W'
                    HM HP ACL (okw_msize sz0) MI SS) as (SOK & MF' & [SUBW INW] & LEN & A0 & A1).
        unfold wa in SOK, MF'. rewrite SOK in STEP.
        cbn [sres_ok]. split; [exact Hlen|].
        eexists. split.
        + split; [reflexivity|]. eexists. split; [|exact AOK]. rewrite STEP, liftA_ok.
          unfold ms_den, next_pc, set_pc, set_mf, set_W. cbn [s_rs s_pc pc_den]. unfold MS_of_core, with_pc. cbn [c_regs c_fregs c_pc c_fcsr c_resv].
          rewrite w64_add, RG. unfold rd_expr. rewrite expr_of_reg_den. reflexivity.
        + unfold INV. cbn [s_mf s_pf s_W s_same next_pc set_pc set_mf set_W]. split; [exact MF'|]. split; [exact HP|]. split; [|split; [|split; [| apply same_gone]]].
          * lx_refm E ss. apply munch_write; [eapply munch_weaken; [exact SUBW| exact MU]| lia | rewrite LEN; lia |]. rewrite LEN. replace (Z.of_nat (N.to_nat (msize_N sz0))) with (Z.of_N (msize_N sz0)) by lia. exact INW.
          * lx_refm E ss. apply wmono_write. exact WM.
          * apply mem_inv_store; [exact MI|]. rewrite LEN. exact SOK.
      - (* [comment removed for export] *)
        assert (SLT : forall k, k <> KEq -> op = match k with KLts => ALU_SLT | _ => ALU_SLTU end ->
                  sres_ok ss m (do_slt D ss k (bv_unsigned rd) (rd_expr ss (bv_unsigned rs1)) (ELit (bv_signed imm)) pc sz)).
        { intros k Hk Hop. eapply (do_slt_ok D ss m pc sz rd k _ _ (rget (Core (regs_den E (s_rs ss)) F (Z_to_bv 64 pc) fc None) rs1) (sext 64 imm) HI Hpc Hlen Hk).
          - rewrite RG. reflexivity. - rewrite sext_small. reflexivity. - rewrite STEP, Hop. reflexivity. }
        destruct op; try (apply SLT; [discriminate|reflexivity]);
        lazymatch goal with |- sres_ok _ _ (match alu_extra ?O ?o ?a ?b ?v with _ => _ end) =>
          assert (XTRA : forall extra, alu_extra O o a b v = extra -> sres_ok ss m (havoc_rd_with ss (bv_unsigned rd) extra pc sz));
          [ intros extra HX; apply (havoc_rd_with_ok ss m pc sz rd (alu64 o (rget (Core (regs_den E (s_rs ss)) F (Z_to_bv 64 pc) fc None) rs1) (sext 64 imm)) extra HI Hpc Hlen); [rewrite STEP; reflexivity|];
            rewrite <- HX; apply alu_extra_ok; [exact HP| rewrite RG; reflexivity| rewrite sext_small; reflexivity]
          | destruct (alu_extra O o a b v) as [|f0 fs0] eqn:AX; [clear XTRA| apply (XTRA _ eq_refl)] ]
        end;
        lazymatch goal with |- sres_ok _ _ (match sym_alu ?O ?pf ?o ?a ?b with _ => _ end) =>
          destruct (sym_alu O pf o a b) as [e|] eqn:SA; [|apply (HAVOC _ (alu64 o (rget (Core (regs_den E (s_rs ss)) F (Z_to_bv 64 pc) fc None) rs1) (sext 64 imm))); rewrite STEP; reflexivity];
          apply (finish_rd_ok ss m pc sz _ _ (alu64 o (rget (Core (regs_den E (s_rs ss)) F (Z_to_bv 64 pc) fc None) rs1) (sext 64 imm))); first [assumption | rewrite STEP; reflexivity | idtac];
          rewrite RG, sext_small; exact (sym_alu_sound _ _ _ _ _ HP SA)
        end.
      - (* [comment removed for export] *)
        lazymatch goal with |- sres_ok _ _ (match sym_alu ?O ?pf ?o ?a ?b with _ => _ end) =>
          destruct (sym_alu O pf o a b) as [e|] eqn:SA; [|apply (HAVOC _ (alu64 o (rget (Core (regs_den E (s_rs ss)) F (Z_to_bv 64 pc) fc None) rs1) (zext 64 shamt))); rewrite STEP; reflexivity];
          apply (finish_rd_ok ss m pc sz _ _ (alu64 o (rget (Core (regs_den E (s_rs ss)) F (Z_to_bv 64 pc) fc None) rs1) (zext 64 shamt))); first [assumption | rewrite STEP; reflexivity | idtac];
          rewrite RG, zext_small; exact (sym_alu_sound _ _ _ _ _ HP SA)
        end.
      - (* [comment removed for export] *)
        assert (SLT : forall k, k <> KEq -> op = match k with KLts => ALU_SLT | _ => ALU_SLTU end ->
                  sres_ok ss m (do_slt D ss k (bv_unsigned rd) (rd_expr ss (bv_unsigned rs1)) (rd_expr ss (bv_unsigned rs2)) pc sz)).
        { intros k Hk Hop. eapply (do_slt_ok D ss m pc sz rd k _ _ (rget (Core (regs_den E (s_rs ss)) F (Z_to_bv 64 pc) fc None) rs1) (rget (Core (regs_den E (s_rs ss)) F (Z_to_bv 64 pc) fc None) rs2) HI Hpc Hlen Hk).
          - rewrite RG. reflexivity. - rewrite RG. reflexivity. - rewrite STEP, Hop. reflexivity. }
        destruct op; try (apply SLT; [discriminate|reflexivity]);
        lazymatch goal with |- sres_ok _ _ (match sym_alu ?O ?pf ?o ?a ?b with _ => _ end) =>
          destruct (sym_alu O pf o a b) as [e|] eqn:SA; [|apply (HAVOC _ (alu64 o (rget (Core (regs_den E (s_rs ss)) F (Z_to_bv 64 pc) fc None) rs1) (rget (Core (regs_den E (s_rs ss)) F (Z_to_bv 64 pc) fc None) rs2))); rewrite STEP; reflexivity];
          apply (finish_rd_ok ss m pc sz _ _ (alu64 o (rget (Core (regs_den E (s_rs ss)) F (Z_to_bv 64 pc) fc None) rs1) (rget (Core (regs_den E (s_rs ss)) F (Z_to_bv 64 pc) fc None) rs2))); first [assumption | rewrite STEP; reflexivity | idtac];
          rewrite !RG; exact (sym_alu_sound _ _ _ _ _ HP SA)
        end.
      - (* [comment removed for export] *)
        lazymatch goal with |- sres_ok _ _ (match sym_alu32 ?O ?o ?a ?b with _ => _ end) =>
          destruct (sym_alu32 O o a b) as [e|] eqn:SA; [|apply (HAVOC _ (sext 64 (alu32 ALU_ADD (low32 (rget (Core (regs_den E (s_rs ss)) F (Z_to_bv 64 pc) fc None) rs1)) (sext 32 imm)))); rewrite STEP; reflexivity];
          apply (finish_rd_ok ss m pc sz _ _ (sext 64 (alu32 ALU_ADD (low32 (rget (Core (regs_den E (s_rs ss)) F (Z_to_bv 64 pc) fc None) rs1)) (sext 32 imm)))); first [assumption | rewrite STEP; reflexivity | idtac];
          rewrite RG; replace (sext 32 imm) with (low32 (Z_to_bv 64 (zden E (ELit (bv_signed imm))))) by (cbn [zden]; rewrite low32_lit; reflexivity);
          exact (sym_alu32_sound _ _ _ _ _ HP SA)
        end.
      - (* [comment removed for export] *)
        lazymatch goal with |- sres_ok _ _ (match sym_alu32 ?O ?o ?a ?b with _ => _ end) =>
          destruct (sym_alu32 O o a b) as [e|] eqn:SA; [|apply (HAVOC _ (sext 64 (alu32 o (low32 (rget (Core (regs_den E (s_rs ss)) F (Z_to_bv 64 pc) fc None) rs1)) (zext 32 shamt)))); rewrite STEP; reflexivity];
          apply (finish_rd_ok ss m pc sz _ _ (sext 64 (alu32 o (low32 (rget (Core (regs_den E (s_rs ss)) F (Z_to_bv 64 pc) fc None) rs1)) (zext 32 shamt)))); first [assumption | rewrite STEP; reflexivity | idtac];
          rewrite RG; replace (zext 32 shamt) with (low32 (Z_to_bv 64 (zden E (ELit (bv_unsigned shamt))))) by (cbn [zden]; rewrite low32_lit; reflexivity);
          exact (sym_alu32_sound _ _ _ _ _ HP SA)
        end.
      - (* [comment removed for export] *)
        lazymatch goal with |- sres_ok _ _ (match sym_alu32 ?O ?o ?a ?b with _ => _ end) =>
          destruct (sym_alu32 O o a b) as [e|] eqn:SA; [|apply (HAVOC _ (sext 64 (alu32 o (low32 (rget (Core (regs_den E (s_rs ss)) F (Z_to_bv 64 pc) fc None) rs1)) (low32 (rget (Core (regs_den E (s_rs ss)) F (Z_to_bv 64 pc) fc None) rs2))))); rewrite STEP; reflexivity];
          apply (finish_rd_ok ss m pc sz _ _ (sext 64 (alu32 o (low32 (rget (Core (regs_den E (s_rs ss)) F (Z_to_bv 64 pc) fc None) rs1)) (low32 (rget (Core (regs_den E (s_rs ss)) F (Z_to_bv 64 pc) fc None) rs2))))); first [assumption | rewrite STEP; reflexivity | idtac];
          rewrite !RG; exact (sym_alu32_sound _ _ _ _ _ HP SA)
        end.
      - (* [comment removed for export] *) cbn [sres_ok]. split; [exact Hlen|]. exists m. split.
        + split; [reflexivity|]. exists []. split; [|apply acc_ok_nil].
          rewrite STEP. unfold ms_den. cbn -[Z_to_bv regs_den bv_add]. rewrite w64_add. reflexivity.
        + eapply INV_same; [..|exact HI|lx_ref_eq]; reflexivity.
      - (* [comment removed for export] *)
        lazymatch goal with |- sres_ok _ _ (match sym_mul ?O ?o ?a ?b with _ => _ end) =>
          destruct (sym_mul O o a b) as [e|] eqn:SA; [|apply (HAVOC _ (mul_div o (rget (Core (regs_den E (s_rs ss)) F (Z_to_bv 64 pc) fc None) rs1) (rget (Core (regs_den E (s_rs ss)) F (Z_to_bv 64 pc) fc None) rs2))); rewrite STEP; reflexivity];
          apply (finish_rd_ok ss m pc sz _ _ (mul_div o (rget (Core (regs_den E (s_rs ss)) F (Z_to_bv 64 pc) fc None) rs1) (rget (Core (regs_den E (s_rs ss)) F (Z_to_bv 64 pc) fc None) rs2))); first [assumption | rewrite STEP; reflexivity | idtac];
          rewrite !RG; exact (sym_mul_sound _ _ _ _ _ HP SA)
        end.
      - (* [comment removed for export] *)
        apply (HAVOC _ (sext 64 (mul_div op (low32 (rget (Core (regs_den E (s_rs ss)) F (Z_to_bv 64 pc) fc None) rs1)) (low32 (rget (Core (regs_den E (s_rs ss)) F (Z_to_bv 64 pc) fc None) rs2))))); rewrite STEP; reflexivity.
      - (* [comment removed for export] *)
        unfold do_amo.
        set (a := rd_expr ss (bv_unsigned rs1)).
        match goal with |- sres_ok _ _ (if negb ?al then _ else _) => destruct al eqn:ALN; [|exact I] end. cbn [negb].
        destruct (acc_class C ss a (Z.of_N (amo_w w0))) as [cl|] eqn:AC; [|exact I].
        assert (OKW : okw (amo_w w0) = true) by (destruct w0; reflexivity).
        pose proof (acc_class_sound E CFG ss a _ cl (or_intror (ex_intro _ m HM)) HP AC) as ACL.
        pose proof (acls_acc_ok E CFG cl (zden E a) (amo_w w0) OKW ACL) as AOK.
        pose proof (sym_load_sound segs L CS E m C (cfg_hsb E CFG) ss a (amo_w w0) true HM HP) as LS.
        destruct (sym_load C ss a (amo_w w0) true) as [r|lo hi|c oa on|] eqn:SL; cbn [lres_ok] in LS; try exact I.
        destruct LS as (bs & RD & VAL).
        destruct (amo_expr (oracle_of ss) op (expr_of_reg r) (rd_expr ss (bv_unsigned rs2))) as [v|] eqn:AX; [|exact I].
        destruct (sym_store C cl ss a (amo_w w0) (mkreg v)) as [mf' W'|code] eqn:SS; [|exact I].
        destruct (sym_store_sound segs L CS E m C (cfg_hst E CFG) (cfg_hsb E CFG) HPF HBK cl ss a (amo_w w0) (mkreg v) mf' W'
                    HM HP ACL OKW MI SS) as (SOK & MF' & [SUBW INW] & LEN & A0 & A1).
        assert (ADDR : rget (Core (regs_den E (s_rs ss)) F (Z_to_bv 64 pc) fc None) rs1 = Z_to_bv 64 (zden E a)) by (rewrite RG; reflexivity).
        assert (ALOK : amo_aligned w0 (Z_to_bv 64 (zden E a)) = true).
        { unfold amo_aligned. apply Z.eqb_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
          apply N.leb_le in ALN.
          pose proof (eal_mod E (oracle_of ss) a (match w0 with AW => 2%N | AD => 3%N end) HO ALN) as M.
          destruct w0; cbn [amo_bytes].
          - change ((zden E a mod 2 ^ 64) mod 4) with ((zden E a mod 2 ^ 64) mod 2 ^ 2). rewrite mod_mod_pow2 by lia. exact M.
          - change ((zden E a mod 2 ^ 64) mod 8) with ((zden E a mod 2 ^ 64) mod 2 ^ 3). rewrite mod_mod_pow2 by lia. exact M. }
        rewrite (exec_amo (Z_to_bv 64 sz) op w0 aq rl rd rs1 rs2 (Core (regs_den E (s_rs ss)) F (Z_to_bv 64 pc) fc None) eq_refl), ADDR, ALOK in STEP. cbn [negb c_pc] in STEP.
        (* [comment removed for export] *)
        cbn [sres_ok]. split. { cbn [s_rs next_pc set_pc set_W set_mf wr_reg]. rewrite wr_reg_len. exact Hlen. }
        unfold wa in SOK, MF'.
        exists (write_to_mem m (Z_to_bv 64 (zden E a)) (st_bytes (amo_w w0) (rden E (mkreg v)))). split.
        + split; [reflexivity|]. eexists. split; [| apply acc_ok_cons; [exact AOK| exact AOK]]. rewrite STEP.
          assert (OLD : low32 (Z_to_bv 64 (zden E (expr_of_reg r))) = low32 (rden E r)) by (rewrite expr_of_reg_den; reflexivity).
          assert (VBY : st_bytes (amo_w w0) (rden E (mkreg v)) =
                        match w0 with
                        | AW => Z_to_le_bytes 4 (bv_unsigned (amo_val op (low32 (rden E r)) (low32 (rget (Core (regs_den E (s_rs ss)) F (Z_to_bv 64 pc) fc None) rs2))))
                        | AD => Z_to_le_bytes 8 (bv_unsigned (amo_val op (rden E r) (rget (Core (regs_den E (s_rs ss)) F (Z_to_bv 64 pc) fc None) rs2)))
                        end).
          { rewrite mkreg_den, RG. destruct w0; cbn [amo_w st_bytes].
            - rewrite <- expr_of_reg_den, (amo_expr_sound32 _ _ _ _ _ HP AX), store_bytes_4'. reflexivity.
            - rewrite <- expr_of_reg_den, (amo_expr_sound64 _ _ _ _ _ HP AX), store_bytes_8'. reflexivity. }
          destruct w0; cbn [amo_w] in RD, SOK, VBY |- *.
          * change (N.to_nat 4) with 4%nat in RD, SOK. rewrite interp_amo32, RD. cbn zeta. rewrite SOK, liftA_ok. cbn [amo_w] in VAL. unfold ld_val in VAL. cbn in VAL.
            set (old := bv_extract 0 32 (le_bytes_to_word bs)) in *.
            assert (OLDEQ : old = low32 (rden E r)) by (rewrite <- VAL; symmetry; apply low32_sext).
            match goal with |- context [amo_val op old ?X] => replace (amo_val op old X) with (amo_val op (low32 (rden E r)) X) by (rewrite OLDEQ; reflexivity) end.
            rewrite <- VBY, VAL.
            unfold ms_den, next_pc, set_pc. cbn [s_rs s_pc pc_den].
            change (regs_den E (s_rs ss)) with (regs_den E (s_rs (set_W (set_mf ss mf') W'))).
            rewrite (rset_den E (set_W (set_mf ss mf') W') rd _ r); [| exact Hlen | reflexivity]. rewrite w64_add. reflexivity.
          * change (N.to_nat 8) with 8%nat in RD, SOK. rewrite interp_amo64, RD. cbn zeta. rewrite SOK, liftA_ok. cbn [amo_w] in VAL. unfold ld_val in VAL. cbn in VAL.
            rewrite VAL, <- VBY.
            unfold ms_den, next_pc, set_pc. cbn [s_rs s_pc pc_den].
            change (regs_den E (s_rs ss)) with (regs_den E (s_rs (set_W (set_mf ss mf') W'))).
            rewrite (rset_den E (set_W (set_mf ss mf') W') rd _ r); [| exact Hlen | reflexivity]. rewrite w64_add. reflexivity.
        + destruct (wr_reg_same (set_W (set_mf ss mf') W') (bv_unsigned rd) r) as (W1 & W2 & W3 & W4 & W5).
          pose proof (wr_reg_sm (set_W (set_mf ss mf') W') (bv_unsigned rd) r) as WS5.
          unfold INV. cbn [s_mf s_pf s_W s_same next_pc set_pc]. rewrite W1, W2, W5, WS5. cbn [s_mf s_pf s_W s_same set_W set_mf].
          split; [exact MF'|]. split; [exact HP|]. split; [|split; [|split; [| apply same_gone]]].
          * lx_refm E ss. apply munch_write; [eapply munch_weaken; [exact SUBW| exact MU]| lia | rewrite LEN; lia |]. rewrite LEN. replace (Z.of_nat (N.to_nat (amo_w w0))) with (Z.of_N (amo_w w0)) by lia. exact INW.
          * lx_refm E ss. apply wmono_write. exact WM.
          * apply mem_inv_store; [exact MI|]. rewrite LEN. exact SOK.
    Qed.
  End Env3.
End StepSound.

End LXH.
