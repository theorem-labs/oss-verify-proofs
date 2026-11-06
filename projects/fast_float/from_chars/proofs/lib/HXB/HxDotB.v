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
From OSSVerify.Proofs.fast_float.from_chars.lib.HXB Require Import HxGenFp HxSemB HxBaseB HxIntB HxDotBW.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition DOT_KEYS : list Z := [11].
Definition dot_chk (X : xst) : bool :=
  let L := xs_st X in
  match s_resv L with
  | RNone => (txt_rgs_ok L && lin_eqb (rgl L 22) TXT_TL && lin_eqb (rgl L 19) (lconst SHBz) && lin_eqb (rgl L 1) (lconst 46)
              && forallb (fact_implied (s_facts L)) (txt_facts ++ [FRange (lsub (rgl L 10) TXT_T) 0 128; FRange (lsub TXT_TL (rgl L 10)) 0 128]))%bool
  | _ => false
  end.
Definition dot_newf (L : sst) : list fact := [FRange (lsub TXT_TL (rgl L 10)) 1 128].
Definition dot_newx (L : sst) : list xfact := [XF 2 [rgl L 10]].
Definition DOT_EXITS : list hx_exit := [(0x933a4, nof, nox); (0x93200, dot_newf, dot_newx)].
Definition H_DOT : xst -> option (list xst) := hx_regm 0x931e0 DOT_KEYS dot_chk DOT_EXITS.

Theorem dot_kit : hx_kitm_fp BSEGS xok_spd 0x931e0 DOT_KEYS dot_chk DOT_EXITS.
Proof.
  intros L XL E ms m0 Hpc Hchk Hw Hd HxF Hm0.
  unfold dot_chk in Hchk. cbn [xs_st xs_x] in Hchk.
  destruct (s_resv L) eqn:Hrv; try discriminate.
  apply andb_prop in Hchk as [Hchk Hfx]. apply andb_prop in Hchk as [Hchk H1]. apply andb_prop in Hchk as [Hchk H19].
  apply andb_prop in Hchk as [Hrg H22]. apply lin_eqb_eq in H22, H19, H1.
  rewrite forallb_app in Hfx. apply andb_prop in Hfx as [Hfx HfS].
  pose proof (txt_bounds E ms L Hd Hfx) as (B1 & B2 & B3 & B4 & B5 & B6).
  destruct (txt_bytes E ms L Hd Hrg Hfx) as (bs & TXT & Hlen).
  pose proof (txt_shadow E ms L Hd Hrg Hfx) as SHT.
  destruct (sden_0 _ _ _ _ Hd) as (Hpc0 & Hsvc0 & Hresv0 & HR & HG & HD & HF & Hfrm).
  rewrite Hrv in Hresv0. cbn [rsv_ok] in Hresv0.
  set (Tz := bv_unsigned (E 1%positive)) in *. set (Lz := bv_unsigned (E 2%positive)) in *.
  set (Y0z := bv_unsigned (E 7%positive)) in *. set (Y1z := bv_unsigned (E 8%positive)) in *.
  set (IEl := rgl L 10) in *. set (IEz := bv_unsigned (lden E IEl)).
  pose proof (bv_unsigned_in_range _ (lden E IEl)) as BIE. unfold bv_modulus in BIE. change (2 ^ Z.of_N 64) with two64 in BIE.
  cbn [forallb] in HfS. apply andb_prop in HfS as [F1 HfS]. apply andb_prop in HfS as [F2 _].
  pose proof (fact_implied_ok E _ _ HF F1) as X1. pose proof (fact_implied_ok E _ _ HF F2) as X2. cbn [fact_ok] in X1, X2.
  rewrite (u_sub E) in X1, X2. unfold TXT_TL, TXT_T, TXT_L in X1, X2. rewrite (u_add E) in X2.
  rewrite !lden_lvar in X1. rewrite !lden_lvar in X2. fold Tz Lz IEz in X1, X2.
  assert (M3 : (Tz + Lz) mod two64 = Tz + Lz) by (apply Z.mod_small; unfold two64 in *; lia).
  rewrite M3 in X2.
  assert (HS : Tz <= IEz <= Tz + Lz) by (unfold two64 in *; split; Z.div_mod_to_equations; lia).
  assert (RG : forall k, getr (ms_regs ms) (Z_to_bv 5 k) = lden E (rgl L k)) by (intros k; rewrite (HR _); reflexivity).
  assert (R10 : getr (ms_regs ms) 10%bv = Z_to_bv 64 IEz).
  { transitivity (lden E (rgl L 10)); [exact (RG 10)|]. symmetry. apply Z_to_bv_bv_unsigned. }
  assert (R1 : getr (ms_regs ms) 1%bv = Z_to_bv 64 46).
  { transitivity (lden E (rgl L 1)); [exact (RG 1)|]. rewrite H1. rewrite lden_lconst. reflexivity. }
  assert (R22 : getr (ms_regs ms) 22%bv = Z_to_bv 64 (Tz + Lz)).
  { transitivity (lden E (rgl L 22)); [exact (RG 22)|]. rewrite H22. unfold TXT_TL, TXT_T, TXT_L. rewrite lden_ladd, !lden_lvar.
    apply bv_eq. rewrite bv_add_unsigned, u_Z_to_bv. reflexivity. }
  assert (R19 : getr (ms_regs ms) 19%bv = Z_to_bv 64 ASAN_B).
  { transitivity (lden E (rgl L 19)); [exact (RG 19)|]. rewrite H19. rewrite lden_lconst. reflexivity. }
  set (R := ms_regs ms) in *.
  assert (HK : evt BSEGS (dot_post (getr R 2) (getr R 3) (getr R 4) (getr R 5) (getr R 6) (getr R 7) (getr R 8) (getr R 9)
                 (getr R 12) (getr R 13) (getr R 14) (getr R 15) (getr R 16) (getr R 17) (getr R 18) (getr R 20) (getr R 21)
                 (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) (getr R 28) (getr R 29) (getr R 30) (getr R 31)
                 (ms_fregs ms) (ms_fcsr ms) (ms_mem ms) bs Tz IEz)
             (kms BSEGS ms)).
  { assert (P1 : 1 <= Z.of_nat (length bs) <= 128) by (clear -Hlen B1; lia).
    assert (P2 : 6537216 <= Tz <= 140737488355072) by (clear -B2; lia).
    assert (P3 : 8 * Y0z <= Tz /\ Tz + Z.of_nat (length bs) <= 8 * Y1z) by (clear -Hlen B5 B6; lia).
    assert (P4 : Tz <= IEz <= Tz + Z.of_nat (length bs)) by (clear -Hlen HS; lia).
    unfold kms, mkR_of. fold R. rewrite Hpc0, Hresv0, R10, R22, R19, R1, Hpc. rewrite <- Hlen.
    exact (blockD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bs Tz IEz Y0z Y1z TXT P1 P2 SHT P3 P4 _). }
  destruct (kit_run BSEGS _ ms Hsvc0 HK) as (ms1 & ms2 & Hst & Heq & Hpost). clear HK.
  destruct Hpost as (y11 & Hpost).
  set (vs := [y11]).
  set (E' := E_of DOT_KEYS vs (s_next L) E).
  assert (Hag : agree (s_next L) E E') by apply E_of_agree.
  unfold state_wf in Hw. apply andb_prop in Hw as [Hw _]. apply andb_prop in Hw as [Hw _]. apply andb_prop in Hw as [Hwr Hwg].
  assert (HwIE : lwf (s_next L) IEl = true) by (exact (regs_wf_n_spec _ _ 31 Hwr 10%nat ltac:(lia))).
  assert (EIE : lden E' IEl = lden E IEl) by (symmetry; exact (lden_agree _ E E' IEl HwIE Hag)).
  assert (Hv12 : (1 < s_next L)%positive /\ (2 < s_next L)%positive).
  { unfold txt_rgs_ok in Hrg. destruct (s_rgs L) as [|R0 [|R1' rs]] eqn:Hr; try discriminate.
    apply andb_prop in Hrg as [H0 _]. unfold rg_is in H0. apply andb_prop in H0 as [H0 _]. apply andb_prop in H0 as [H0 _].
    apply andb_prop in H0 as [Hb0 Hs0]. apply lin_eqb_eq in Hb0, Hs0. cbn [forallb] in Hwg. apply andb_prop in Hwg as [Hw0 _].
    unfold rwf in Hw0. apply andb_prop in Hw0 as [Hw0 _]. apply andb_prop in Hw0 as [Hw0a Hw0b]. rewrite Hb0 in Hw0a. rewrite Hs0 in Hw0b.
    unfold lwf, TXT_T, TXT_L, lvar in Hw0a, Hw0b. cbn in Hw0a, Hw0b. apply andb_prop in Hw0a as [Hw0a _]. apply andb_prop in Hw0b as [Hw0b _].
    apply Pos.ltb_lt in Hw0a, Hw0b. split; assumption. }
  assert (E1' : E' 1%positive = E 1%positive) by (unfold E'; apply E_of_old; lia).
  assert (E2' : E' 2%positive = E 2%positive) by (unfold E'; apply E_of_old; lia).
  assert (COMMON : forall pc1 (msx : machine_state), msx = MS (mkR (Z_to_bv 64 46) (getr R 2) (getr R 3) (getr R 4) (getr R 5) (getr R 6) (getr R 7)
                     (getr R 8) (getr R 9) (Z_to_bv 64 IEz) y11 (getr R 12) (getr R 13) (getr R 14) (getr R 15) (getr R 16) (getr R 17) (getr R 18)
                     (Z_to_bv 64 ASAN_B) (getr R 20) (getr R 21) (Z_to_bv 64 (Tz + Z.of_nat (length bs))) (getr R 23) (getr R 24) (getr R 25)
                     (getr R 26) (getr R 27) (getr R 28) (getr R 29) (getr R 30) (getr R 31))
                     (ms_fregs ms) (Z_to_bv 64 pc1) (ms_fcsr ms) None (ms_mem ms) (seg_rom BSEGS) ->
     ms_eqv ms1 (with_rom msx (ms_rom ms)) ->
     isteps BSEGS ms ms1 /\ length vs = length DOT_KEYS /\
      ms_mem ms1 = ms_mem ms /\ ms_fcsr ms1 = ms_fcsr ms /\ ms_resv ms1 = ms_resv ms /\ ms_svc_pending ms1 = None /\
      ms_pc_val ms1 = Z_to_bv 64 pc1 /\
      (forall r, ~ In (bv_unsigned r) DOT_KEYS -> getr (ms_regs ms1) r = getr (ms_regs ms) r) /\
      (forall i k v, nth_error DOT_KEYS i = Some k -> nth_error vs i = Some v -> getr (ms_regs ms1) (Z_to_bv 5 k) = v) /\
      (forall r, reg_get (ms_fregs ms1) r = reg_get (ms_fregs ms) r)).
  { intros pc1 msx -> Heq2. destruct Heq2 as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
    cbn [with_rom MS ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in E1, E2, E3, E4, E5, E6, E7, E8.
    split; [exact Hst|]. split; [reflexivity|]. split; [exact E7|]. split; [exact E6|]. split; [rewrite E5, Hresv0; reflexivity|].
    split; [exact E4|]. split; [exact E3|]. split; [|split; [|exact E2]].
    - intros r Hr. rewrite (E1 r). destruct (reg_of_nat r) as (n & -> & Hn). rewrite getr_mkR. rewrite u5 by lia. rewrite Nat2Z.id.
      unfold DOT_KEYS in Hr. cbn [In] in Hr. rewrite u5 in Hr by lia.
      do 32 (destruct n as [|n]; [cbn; first [reflexivity | (symmetry; exact R10) | (symmetry; exact R19) | (symmetry; exact R1)
                                              | (rewrite Hlen; symmetry; exact R22) | (symmetry; exact R22)
                                              | (exfalso; apply Hr; repeat (first [left; reflexivity | right]))]|]).
      lia.
    - intros i k v Hi Hv. rewrite (E1 _).
      destruct i as [|i]; cbn in Hi, Hv;
        first [ (injection Hi as <-; injection Hv as <-; reflexivity) | (destruct i; discriminate) ]. }
  destruct Hpost as [Hms2|(Hms2 & HIEL & Hdot)].
  - exists 0x933a4, nof, nox, ms1, vs. split; [left; reflexivity|].
    destruct (COMMON 0x933a4 ms2 Hms2 Heq) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10).
    do 9 (split; [assumption|]). split; [constructor|]. split; [constructor | exact C10].
  - exists 0x93200, dot_newf, dot_newx, ms1, vs. split; [right; left; reflexivity|].
    destruct (COMMON 0x93200 ms2 Hms2 Heq) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10).
    do 9 (split; [assumption|]). fold E'. split; [|split; [|exact C10]].
    + unfold dot_newf. fold IEl. constructor; [|constructor]. cbn [fact_ok].
      rewrite lden_lsub, bv_sub_unsigned, EIE. unfold TXT_TL, TXT_T, TXT_L. rewrite lden_ladd, bv_add_unsigned, !lden_lvar, E1', E2'.
      fold Tz Lz IEz. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64. rewrite (Z.mod_small (Tz + Lz)) by (unfold two64 in *; lia).
      rewrite Z.mod_small by (unfold two64 in *; lia). lia.
    + unfold dot_newx. fold IEl. constructor; [|constructor]. unfold xfact_ok. cbn [xf_tag xf_args List.map xok_spd].
      rewrite EIE. fold IEz.
      exists Tz, bs. split.
      * apply (bytes_at_transport (ms_mem ms)); [exact TXT|]. intros i Hi.
        unfold txt_rgs_ok in Hrg. destruct (s_rgs L) as [|R0 [|R1' rs]] eqn:Hr; try discriminate.
        apply andb_prop in Hrg as [H0 _]. unfold rg_is in H0. apply andb_prop in H0 as [H0 _]. apply andb_prop in H0 as [H0 Hk0].
        apply andb_prop in H0 as [Hb0 Hs0]. apply lin_eqb_eq in Hb0, Hs0. destruct (rg_kind R0) eqn:Hk; cbn in Hk0; try discriminate.
        rewrite <- Hr in Hm0. exact (txt_frame E L ms m0 R0 (R1' :: rs) i Hr Hb0 Hs0 Hk Hm0 ltac:(lia) ltac:(unfold two64 in *; lia)).
      * split; [lia | exact Hdot].
Qed.

Theorem H_DOT_ok : hand_okx_fp BSEGS xok_spd H_DOT.
Proof. apply hx_okm_fp. exact dot_kit. Qed.
