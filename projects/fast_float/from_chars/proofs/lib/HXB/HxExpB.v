(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec FxLin FxCore FxSubst FxSound FxMem FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxDrv FxEnt FxRgs FxFacts FxPlan FxFrame FxWork FxWorkX.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxWork OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxWorkX.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Mem Cells Exec Frame Arr Step Image RegsEquiv MState.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Spf_text.
From OSSVerify.Proofs.fast_float.from_chars.lib.KX Require Import KxBridge KxRun.
From OSSVerify.Proofs.fast_float.from_chars.lib.HX Require Import HxGen.
From OSSVerify.Proofs.fast_float.from_chars.lib.HXB Require Import HxGenFp HxSemB HxBaseB HxIntB HxDefsB HxExpBW.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition EXP_KEYS : list Z := [7; 11; 14; 17; 23; 25; 28; 29; 30].
Definition exp_chk (X : xst) : bool :=
  let L := xs_st X in
  match s_resv L with
  | RNone => (txt_rgs_ok L && lin_eqb (rgl L 22) TXT_TL && lin_eqb (rgl L 19) (lconst SHBz) && lin_eqb (rgl L 16) (lconst 9)
              && forallb (fact_implied (s_facts L)) (txt_facts ++ [FRange (lsub (rgl L 25) TXT_T) 0 128; FRange (lsub TXT_TL (rgl L 25)) 1 128]))%bool
  | _ => false
  end.
Definition exp_newf (L : sst) : list fact :=
  let P' := lvar (fv (s_next L) 5) in
  [FRange (lvar (fv (s_next L) 0)) 0 EXPMAX; FRange (lsub P' TXT_T) 0 128; FRange (lsub TXT_TL P') 0 128; FRange P' 6537216 P47].
Definition exp_newfA (L : sst) : list fact := FRange (lsub TXT_TL (lvar (fv (s_next L) 5))) 1 128 :: exp_newf L.
Definition exp_newfB (L : sst) : list fact := FRange (lsub TXT_TL (lvar (fv (s_next L) 5))) 0 0 :: exp_newf L.
Definition EXP_EXITS : list hx_exit := [(0x94614, exp_newfA, nox); (0x9461c, exp_newfB, nox)].
Definition H_EXP : xst -> option (list xst) := hx_regm 0x93790 EXP_KEYS exp_chk EXP_EXITS.

Theorem exp_kit : hx_kitm_fp BSEGS xok_spd 0x93790 EXP_KEYS exp_chk EXP_EXITS.
Proof.
  intros L XL E ms m0 Hpc Hchk Hw Hd HxF Hm0.
  unfold exp_chk in Hchk. cbn [xs_st xs_x] in Hchk.
  destruct (s_resv L) eqn:Hrv; try discriminate.
  apply andb_prop in Hchk as [Hchk Hfx]. apply andb_prop in Hchk as [Hchk H16]. apply andb_prop in Hchk as [Hchk H19].
  apply andb_prop in Hchk as [Hrg H22]. apply lin_eqb_eq in H22, H19, H16.
  rewrite forallb_app in Hfx. apply andb_prop in Hfx as [Hfx HfS].
  pose proof (txt_bounds E ms L Hd Hfx) as (B1 & B2 & B3 & B4 & B5 & B6).
  destruct (txt_bytes E ms L Hd Hrg Hfx) as (bs & TXT & Hlen).
  pose proof (txt_shadow E ms L Hd Hrg Hfx) as SHT.
  destruct (sden_0 _ _ _ _ Hd) as (Hpc0 & Hsvc0 & Hresv0 & HR & HG & HD & HF & Hfrm).
  rewrite Hrv in Hresv0. cbn [rsv_ok] in Hresv0.
  set (Tz := bv_unsigned (E 1%positive)) in *. set (Lz := bv_unsigned (E 2%positive)) in *.
  set (Y0z := bv_unsigned (E 7%positive)) in *. set (Y1z := bv_unsigned (E 8%positive)) in *.
  set (Pl := rgl L 25) in *. set (Pz := bv_unsigned (lden E Pl)).
  pose proof (bv_unsigned_in_range _ (lden E Pl)) as BP. unfold bv_modulus in BP. change (2 ^ Z.of_N 64) with two64 in BP.
  cbn [forallb] in HfS. apply andb_prop in HfS as [F1 HfS]. apply andb_prop in HfS as [F2 _].
  pose proof (fact_implied_ok E _ _ HF F1) as X1. pose proof (fact_implied_ok E _ _ HF F2) as X2. cbn [fact_ok] in X1, X2.
  rewrite (u_sub E) in X1, X2. unfold TXT_TL, TXT_T, TXT_L in X1, X2. rewrite (u_add E) in X2.
  rewrite !lden_lvar in X1. rewrite !lden_lvar in X2. fold Tz Lz Pz in X1, X2.
  assert (M3 : (Tz + Lz) mod two64 = Tz + Lz) by (apply Z.mod_small; unfold two64 in *; lia).
  rewrite M3 in X2.
  assert (HS : Tz <= Pz < Tz + Lz) by (unfold two64 in *; split; Z.div_mod_to_equations; lia).
  assert (RG : forall k, getr (ms_regs ms) (Z_to_bv 5 k) = lden E (rgl L k)) by (intros k; rewrite (HR _); reflexivity).
  assert (R25 : getr (ms_regs ms) 25%bv = Z_to_bv 64 (Tz + (Pz - Tz))).
  { transitivity (lden E (rgl L 25)); [exact (RG 25)|]. replace (Tz + (Pz - Tz)) with Pz by lia. symmetry. apply Z_to_bv_bv_unsigned. }
  assert (R16 : getr (ms_regs ms) 16%bv = Z_to_bv 64 9).
  { transitivity (lden E (rgl L 16)); [exact (RG 16)|]. rewrite H16. rewrite lden_lconst. reflexivity. }
  assert (R22 : getr (ms_regs ms) 22%bv = Z_to_bv 64 (Tz + Lz)).
  { transitivity (lden E (rgl L 22)); [exact (RG 22)|]. rewrite H22. unfold TXT_TL, TXT_T, TXT_L. rewrite lden_ladd, !lden_lvar.
    apply bv_eq. rewrite bv_add_unsigned, u_Z_to_bv. reflexivity. }
  assert (R19 : getr (ms_regs ms) 19%bv = Z_to_bv 64 ASAN_B).
  { transitivity (lden E (rgl L 19)); [exact (RG 19)|]. rewrite H19. rewrite lden_lconst. reflexivity. }
  set (R := ms_regs ms) in *.
  assert (HK : evt BSEGS (exp_post (getr R 1) (getr R 2) (getr R 3) (getr R 4) (getr R 5) (getr R 6) (getr R 8) (getr R 9)
                 (getr R 10) (getr R 12) (getr R 13) (getr R 15) (getr R 18) (getr R 20) (getr R 21) (getr R 24) (getr R 26)
                 (getr R 27) (getr R 31) (ms_fregs ms) (ms_fcsr ms) (ms_mem ms) bs Tz)
             (kms BSEGS ms)).
  { assert (P1 : 1 <= Z.of_nat (length bs) <= 128) by (clear -Hlen B1; lia).
    assert (P2 : 6537216 <= Tz <= 140737488355072) by (clear -B2; lia).
    assert (P3 : 8 * Y0z <= Tz /\ Tz + Z.of_nat (length bs) <= 8 * Y1z) by (clear -Hlen B5 B6; lia).
    unfold kms, mkR_of. fold R. rewrite Hpc0, Hresv0, R25, R22, R19, R16, Hpc. rewrite <- Hlen.
    exact (blockE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bs Tz Y0z Y1z TXT P1 P2 SHT P3 (Pz - Tz) _ _ _ _ _ _ _ _ ltac:(lia)). }
  destruct (kit_run BSEGS _ ms Hsvc0 HK) as (ms1 & ms2 & Hst & Heq & Hpost). clear HK.
  destruct Hpost as (y7 & y11 & y14 & y17 & y23 & y25 & y28 & y29 & y30 & Hpost & Hy7 & Hy25).
  set (vs := [y7; y11; y14; y17; y23; y25; y28; y29; y30]).
  set (E' := E_of EXP_KEYS vs (s_next L) E).
  assert (Hag : agree (s_next L) E E') by apply E_of_agree.
  assert (Hv12 : (1 < s_next L)%positive /\ (2 < s_next L)%positive).
  { unfold state_wf in Hw. apply andb_prop in Hw as [Hw _]. apply andb_prop in Hw as [Hw _]. apply andb_prop in Hw as [_ Hwg].
    unfold txt_rgs_ok in Hrg. destruct (s_rgs L) as [|R0 [|R1' rs]] eqn:Hr; try discriminate.
    apply andb_prop in Hrg as [H0 _]. unfold rg_is in H0. apply andb_prop in H0 as [H0 _]. apply andb_prop in H0 as [H0 _].
    apply andb_prop in H0 as [Hb0 Hs0]. apply lin_eqb_eq in Hb0, Hs0. cbn [forallb] in Hwg. apply andb_prop in Hwg as [Hw0 _].
    unfold rwf in Hw0. apply andb_prop in Hw0 as [Hw0 _]. apply andb_prop in Hw0 as [Hw0a Hw0b]. rewrite Hb0 in Hw0a. rewrite Hs0 in Hw0b.
    unfold lwf, TXT_T, TXT_L, lvar in Hw0a, Hw0b. cbn in Hw0a, Hw0b. apply andb_prop in Hw0a as [Hw0a _]. apply andb_prop in Hw0b as [Hw0b _].
    apply Pos.ltb_lt in Hw0a, Hw0b. split; assumption. }
  assert (E1' : E' 1%positive = E 1%positive) by (unfold E'; apply E_of_old; lia).
  assert (E2' : E' 2%positive = E 2%positive) by (unfold E'; apply E_of_old; lia).
  assert (Hv0 : E' (fv (s_next L) 0) = y7).
  { exact (E_of_nth EXP_KEYS vs (s_next L) E 0 y7 eq_refl eq_refl). }
  assert (Hv5 : E' (fv (s_next L) 5) = y25).
  { exact (E_of_nth EXP_KEYS vs (s_next L) E 5 y25 eq_refl eq_refl). }
  assert (COMMON : forall pc1 (msx : machine_state), msx = MS (mkR (getr R 1) (getr R 2) (getr R 3) (getr R 4) (getr R 5) (getr R 6) y7
                     (getr R 8) (getr R 9) (getr R 10) y11 (getr R 12) (getr R 13) y14 (getr R 15) (Z_to_bv 64 9) y17 (getr R 18)
                     (Z_to_bv 64 ASAN_B) (getr R 20) (getr R 21) (Z_to_bv 64 (Tz + Z.of_nat (length bs))) y23 (getr R 24) y25
                     (getr R 26) (getr R 27) y28 y29 y30 (getr R 31))
                     (ms_fregs ms) (Z_to_bv 64 pc1) (ms_fcsr ms) None (ms_mem ms) (seg_rom BSEGS) ->
     ms_eqv ms1 (with_rom msx (ms_rom ms)) ->
     isteps BSEGS ms ms1 /\ length vs = length EXP_KEYS /\
      ms_mem ms1 = ms_mem ms /\ ms_fcsr ms1 = ms_fcsr ms /\ ms_resv ms1 = ms_resv ms /\ ms_svc_pending ms1 = None /\
      ms_pc_val ms1 = Z_to_bv 64 pc1 /\
      (forall r, ~ In (bv_unsigned r) EXP_KEYS -> getr (ms_regs ms1) r = getr (ms_regs ms) r) /\
      (forall i k v, nth_error EXP_KEYS i = Some k -> nth_error vs i = Some v -> getr (ms_regs ms1) (Z_to_bv 5 k) = v) /\
      (forall r, reg_get (ms_fregs ms1) r = reg_get (ms_fregs ms) r)).
  { intros pc1 msx -> Heq2. destruct Heq2 as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
    cbn [with_rom MS ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in E1, E2, E3, E4, E5, E6, E7, E8.
    split; [exact Hst|]. split; [reflexivity|]. split; [exact E7|]. split; [exact E6|]. split; [rewrite E5, Hresv0; reflexivity|].
    split; [exact E4|]. split; [exact E3|]. split; [|split; [|exact E2]].
    - intros r Hr. rewrite (E1 r). destruct (reg_of_nat r) as (n & -> & Hn). rewrite getr_mkR. rewrite u5 by lia. rewrite Nat2Z.id.
      unfold EXP_KEYS in Hr. cbn [In] in Hr. rewrite u5 in Hr by lia.
      do 32 (destruct n as [|n]; [cbn; first [reflexivity | (symmetry; exact R16) | (symmetry; exact R19)
                                              | (rewrite Hlen; symmetry; exact R22) | (symmetry; exact R22)
                                              | (exfalso; apply Hr; repeat (first [left; reflexivity | right]))]|]).
      lia.
    - intros i k v Hi Hv. rewrite (E1 _).
      destruct i as [|[|[|[|[|[|[|[|[|i]]]]]]]]]; cbn in Hi, Hv;
        first [ (injection Hi as <-; injection Hv as <-; reflexivity) | (destruct i; discriminate) ]. }
  assert (NF : forall pc1 newf, newf = exp_newfA \/ newf = exp_newfB ->
            (pc1 = 0x94614 -> bv_unsigned y25 < Tz + Lz) -> (pc1 = 0x9461c -> bv_unsigned y25 = Tz + Lz) ->
            (pc1 = 0x94614 /\ newf = exp_newfA \/ pc1 = 0x9461c /\ newf = exp_newfB) ->
            Forall (fact_ok E') (newf L)).
  { intros pc1 newf _ HA HB Hsel.
    assert (Ecom : Forall (fact_ok E') (exp_newf L)).
    { unfold exp_newf. constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]; cbn [fact_ok].
      - rewrite lden_lvar, Hv0. lia.
      - rewrite lden_lsub, bv_sub_unsigned, lden_lvar, Hv5. unfold TXT_T. rewrite lden_lvar, E1'. fold Tz.
        unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64. rewrite Z.mod_small by (unfold two64 in *; lia). lia.
      - rewrite lden_lsub, bv_sub_unsigned, lden_lvar, Hv5. unfold TXT_TL, TXT_T, TXT_L. rewrite lden_ladd, bv_add_unsigned, !lden_lvar, E1', E2'.
        fold Tz Lz. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64. rewrite (Z.mod_small (Tz + Lz)) by (unfold two64 in *; lia).
        rewrite Z.mod_small by (unfold two64 in *; lia). lia.
      - rewrite lden_lvar, Hv5. unfold P47. lia. }
    destruct Hsel as [(-> & ->)|(-> & ->)].
    - specialize (HA eq_refl). unfold exp_newfA. constructor; [|exact Ecom]. cbn [fact_ok].
      rewrite lden_lsub, bv_sub_unsigned, lden_lvar, Hv5. unfold TXT_TL, TXT_T, TXT_L. rewrite lden_ladd, bv_add_unsigned, !lden_lvar, E1', E2'.
      fold Tz Lz. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64. rewrite (Z.mod_small (Tz + Lz)) by (unfold two64 in *; lia).
      rewrite Z.mod_small by (unfold two64 in *; lia). lia.
    - specialize (HB eq_refl). unfold exp_newfB. constructor; [|exact Ecom]. cbn [fact_ok].
      rewrite lden_lsub, bv_sub_unsigned, lden_lvar, Hv5. unfold TXT_TL, TXT_T, TXT_L. rewrite lden_ladd, bv_add_unsigned, !lden_lvar, E1', E2'.
      fold Tz Lz. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64. rewrite (Z.mod_small (Tz + Lz)) by (unfold two64 in *; lia).
      rewrite HB. rewrite Z.sub_diag, Z.mod_0_l by (unfold two64; lia). lia. }
  destruct Hpost as [(Hms2 & HlA)|(Hms2 & HlB)].
  - exists 0x94614, exp_newfA, nox, ms1, vs. split; [left; reflexivity|].
    destruct (COMMON 0x94614 ms2 Hms2 Heq) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10).
    do 9 (split; [assumption|]). split; [|split; [constructor | exact C10]].
    apply (NF 0x94614 exp_newfA); [left; reflexivity | intros _; lia | intros X; discriminate | left; split; reflexivity].
  - exists 0x9461c, exp_newfB, nox, ms1, vs. split; [right; left; reflexivity|].
    destruct (COMMON 0x9461c ms2 Hms2 Heq) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10).
    do 9 (split; [assumption|]). split; [|split; [constructor | exact C10]].
    apply (NF 0x9461c exp_newfB); [right; reflexivity | intros X; discriminate | intros _; lia | right; split; reflexivity].
Qed.

Theorem H_EXP_ok : hand_okx_fp BSEGS xok_spd H_EXP.
Proof. apply hx_okm_fp. exact exp_kit. Qed.
