(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec FxLin FxCore FxSubst FxSound FxMem FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxDrv FxEnt FxRgs FxFacts FxPlan FxFrame FxWork FxWorkX.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxWork OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxWorkX.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Mem Cells Exec Frame Arr Step Image RegsEquiv MState.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Spf_text.
From OSSVerify.Proofs.fast_float.from_chars.lib.KX Require Import KxBridge KxRun.
From OSSVerify.Proofs.fast_float.from_chars.lib.HX Require Import HxGen HxSem HxInt HxIntFW.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition int_chk_f (L : sst) : bool :=
  match s_resv L with
  | RNone => (txt_rgs_ok L && lin_eqb (rget (s_regs L) (rkz 23)) TXT_TL && lin_eqb (rget (s_regs L) (rkz 19)) (lconst SHBz)
              && forallb (fact_implied (s_facts L)) (txt_facts ++ [FRange (lsub (int_S L) TXT_T) 0 128; FRange (lsub TXT_TL (int_S L)) 0 128]))%bool
  | _ => false
  end.
Definition H_INT_F : xst -> option (list xst) := hx_reg 0x99a8c 0x99c60 INT_KEYS int_chk_f int_newf int_newx.

Theorem int_kit_f : hx_kit ASEGS xok_spd 0x99a8c 0x99c60 INT_KEYS int_chk_f int_newf int_newx.
Proof.
  intros L XL E ms m0 Hpc Hchk Hw Hd HxF Hm0.
  unfold int_chk_f in Hchk. destruct (s_resv L) eqn:Hrv; try discriminate.
  apply andb_prop in Hchk as [Hchk Hfx]. apply andb_prop in Hchk as [Hchk H19]. apply andb_prop in Hchk as [Hrg H23].
  apply lin_eqb_eq in H23, H19.
  rewrite forallb_app in Hfx. apply andb_prop in Hfx as [Hfx HfS].
  pose proof (txt_bounds E ms L Hd Hfx) as (B1 & B2 & B3 & B4 & B5 & B6).
  destruct (txt_bytes E ms L Hd Hrg Hfx) as (bs & TXT & Hlen).
  pose proof (txt_shadow E ms L Hd Hrg Hfx) as SHT.
  destruct (sden_0 _ _ _ _ Hd) as (Hpc0 & Hsvc0 & Hresv0 & HR & HG & HD & HF & Hfrm).
  rewrite Hrv in Hresv0. cbn [rsv_ok] in Hresv0.
  set (S := int_S L) in *. set (Sz := bv_unsigned (lden E S)).
  set (Tz := bv_unsigned (E 1%positive)) in *. set (Lz := bv_unsigned (E 2%positive)) in *.
  set (Y0z := bv_unsigned (E 7%positive)) in *. set (Y1z := bv_unsigned (E 8%positive)) in *.
  pose proof (bv_unsigned_in_range _ (lden E S)) as BS. unfold bv_modulus in BS. change (2 ^ Z.of_N 64) with two64 in BS.
  cbn [forallb] in HfS. apply andb_prop in HfS as [F1 HfS]. apply andb_prop in HfS as [F2 _].
  pose proof (fact_implied_ok E _ _ HF F1) as X1. pose proof (fact_implied_ok E _ _ HF F2) as X2. cbn [fact_ok] in X1, X2.
  rewrite (u_sub E) in X1, X2. unfold TXT_TL, TXT_T, TXT_L in X1, X2. rewrite (u_add E) in X2.
  rewrite !lden_lvar in X1. rewrite !lden_lvar in X2.
  fold Sz Tz Lz in X1, X2.
  assert (M3 : (Tz + Lz) mod two64 = Tz + Lz) by (apply Z.mod_small; unfold two64 in *; lia).
  rewrite M3 in X2.
  assert (HS : Tz <= Sz <= Tz + Lz) by (unfold two64 in *; split; Z.div_mod_to_equations; lia).
  (* [comment removed for export] *)
  assert (R22 : getr (ms_regs ms) 22%bv = Z_to_bv 64 Sz).
  { rewrite (HR 22%bv). change (rkey 22%bv) with (rkz 22). fold S. unfold Sz. symmetry. apply Z_to_bv_bv_unsigned. }
  assert (R23 : getr (ms_regs ms) 23%bv = Z_to_bv 64 (Tz + Lz)).
  { rewrite (HR 23%bv). change (rkey 23%bv) with (rkz 23). rewrite H23. unfold TXT_TL, TXT_T, TXT_L. rewrite lden_ladd, !lden_lvar.
    apply bv_eq. rewrite bv_add_unsigned, u_Z_to_bv. reflexivity. }
  assert (R19 : getr (ms_regs ms) 19%bv = Z_to_bv 64 ASAN_B).
  { rewrite (HR 19%bv). change (rkey 19%bv) with (rkz 19). rewrite H19. rewrite lden_lconst. reflexivity. }
  set (R := ms_regs ms) in *.
  assert (HK : evt ASEGS (int_post (getr R 1) (getr R 2) (getr R 3) (getr R 4) (getr R 5) (getr R 6) (getr R 7) (getr R 8) (getr R 9)
                 (getr R 17) (getr R 18) (getr R 20) (getr R 21) (getr R 24) (getr R 25) (getr R 26) (getr R 27) (getr R 28)
                 (getr R 29) (getr R 30) (getr R 31) (ms_fregs ms) (ms_fcsr ms) (ms_mem ms) bs Tz Sz)
             (kms ASEGS ms)).
  { unfold kms, mkR_of. fold R. rewrite Hpc0, Hresv0, R22, R23, R19, Hpc. rewrite <- Hlen.
    apply (blockI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bs Tz Sz Y0z Y1z TXT); [lia | lia | lia | exact SHT | split; lia]. }
  destruct (kit_run ASEGS _ ms Hsvc0 HK) as (ms1 & ms2 & Hst & Heq & Hpost). clear HK.
  destruct Hpost as (a0 & a1 & a2 & a3 & a4 & a5 & a6 & Hms2 & HIE & HDG). subst ms2.
  destruct Heq as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
  cbn [with_rom MS ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in E1, E2, E3, E4, E5, E6, E7, E8.
  exists ms1, [a0; a1; a2; a3; a4; a5; a6].
  split; [exact Hst|]. split; [reflexivity|]. split; [exact E7|]. split; [exact E6|]. split; [rewrite E5, Hresv0; reflexivity|].
  split; [exact E4|]. split; [exact E3|].
  split; [|split; [|split]].
  - (* [comment removed for export] *)
    intros r Hr. rewrite (E1 r). destruct (reg_of_nat r) as (n & -> & Hn). rewrite getr_mkR. rewrite u5 by lia. rewrite Nat2Z.id.
    unfold INT_KEYS in Hr. cbn [In] in Hr. rewrite u5 in Hr by lia.
    do 32 (destruct n as [|n]; [cbn; first [reflexivity | (symmetry; exact R22) | (symmetry; exact R23) | (rewrite Hlen; symmetry; exact R23)
                                            | (symmetry; exact R19) | (exfalso; apply Hr; repeat (first [left; reflexivity | right]))]|]).
    lia.
  - (* [comment removed for export] *)
    intros i k v Hi Hv. rewrite (E1 _).
    destruct i as [|[|[|[|[|[|[|i]]]]]]]; cbn in Hi, Hv;
      first [ (injection Hi as <-; injection Hv as <-; reflexivity) | (destruct i; discriminate) ].
  - (* [comment removed for export] *)
    set (E' := E_of INT_KEYS [a0; a1; a2; a3; a4; a5; a6] (s_next L) E).
    assert (Ha0 : E' (s_next L) = a0).
    { pose proof (E_of_nth INT_KEYS [a0; a1; a2; a3; a4; a5; a6] (s_next L) E 0 a0 eq_refl eq_refl) as X.
      rewrite Nat.add_0_r, Pos2Nat.id in X. exact X. }
    assert (Hag : agree (s_next L) E E') by apply E_of_agree.
    unfold state_wf in Hw. apply andb_prop in Hw as [Hw _]. apply andb_prop in Hw as [Hw _]. apply andb_prop in Hw as [Hwr Hwg].
    assert (HwS : lwf (s_next L) S = true) by (exact (regs_wf_n_spec _ _ 31 Hwr 22%nat ltac:(lia))).
    assert (Hv12 : (1 < s_next L)%positive /\ (2 < s_next L)%positive).
    { unfold txt_rgs_ok in Hrg. destruct (s_rgs L) as [|R0 [|R1 rs]] eqn:Hr; try discriminate.
      apply andb_prop in Hrg as [H0 _]. unfold rg_is in H0. apply andb_prop in H0 as [H0 _]. apply andb_prop in H0 as [H0 _].
      apply andb_prop in H0 as [Hb0 Hs0]. apply lin_eqb_eq in Hb0, Hs0. cbn [forallb] in Hwg. apply andb_prop in Hwg as [Hw0 _].
      unfold rwf in Hw0. apply andb_prop in Hw0 as [Hw0 _]. apply andb_prop in Hw0 as [Hw0a Hw0b]. rewrite Hb0 in Hw0a. rewrite Hs0 in Hw0b.
      unfold lwf, TXT_T, TXT_L, lvar in Hw0a, Hw0b. cbn in Hw0a, Hw0b. apply andb_prop in Hw0a as [Hw0a _]. apply andb_prop in Hw0b as [Hw0b _].
      apply Pos.ltb_lt in Hw0a, Hw0b. split; assumption. }
    assert (E1' : E' 1%positive = E 1%positive) by (unfold E'; apply E_of_old; lia).
    assert (E2' : E' 2%positive = E 2%positive) by (unfold E'; apply E_of_old; lia).
    assert (ES : lden E' S = lden E S) by (symmetry; exact (lden_agree _ E E' S HwS Hag)).
    unfold int_newf. fold S. constructor; [|constructor; [|constructor]]; cbn [fact_ok].
    + rewrite lden_lsub, bv_sub_unsigned, lden_lvar, Ha0, ES. fold Sz. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64.
      rewrite Z.mod_small by (unfold two64 in *; lia). lia.
    + rewrite lden_lsub, bv_sub_unsigned, lden_lvar, Ha0. unfold TXT_TL, TXT_T, TXT_L. rewrite lden_ladd, bv_add_unsigned, !lden_lvar, E1', E2'.
      fold Tz Lz. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64. rewrite (Z.mod_small (Tz + Lz)) by (unfold two64 in *; lia).
      rewrite Z.mod_small by (unfold two64 in *; lia). lia.
  - (* [comment removed for export] *)
    set (E' := E_of INT_KEYS [a0; a1; a2; a3; a4; a5; a6] (s_next L) E).
    assert (Ha0 : E' (s_next L) = a0).
    { pose proof (E_of_nth INT_KEYS [a0; a1; a2; a3; a4; a5; a6] (s_next L) E 0 a0 eq_refl eq_refl) as X.
      rewrite Nat.add_0_r, Pos2Nat.id in X. exact X. }
    assert (Hag : agree (s_next L) E E') by apply E_of_agree.
    unfold state_wf in Hw. apply andb_prop in Hw as [Hw _]. apply andb_prop in Hw as [Hw _]. apply andb_prop in Hw as [Hwr _].
    assert (HwS : lwf (s_next L) S = true) by (exact (regs_wf_n_spec _ _ 31 Hwr 22%nat ltac:(lia))).
    assert (ES : lden E' S = lden E S) by (symmetry; exact (lden_agree _ E E' S HwS Hag)).
    unfold int_newx. fold S. constructor; [|constructor]. unfold xfact_ok. cbn [xf_tag xf_args List.map xok_spd].
    rewrite ES, lden_lvar, Ha0. fold Sz.
    exists Tz, bs. split; [|split; [lia|split; [lia | exact HDG]]].
    apply (bytes_at_transport (ms_mem ms)); [exact TXT|]. intros i Hi.
    unfold txt_rgs_ok in Hrg. destruct (s_rgs L) as [|R0 [|R1 rs]] eqn:Hr; try discriminate.
    apply andb_prop in Hrg as [H0 _]. unfold rg_is in H0. apply andb_prop in H0 as [H0 _]. apply andb_prop in H0 as [H0 Hk0].
    apply andb_prop in H0 as [Hb0 Hs0]. apply lin_eqb_eq in Hb0, Hs0. destruct (rg_kind R0) eqn:Hk; cbn in Hk0; try discriminate.
    rewrite <- Hr in Hm0. exact (txt_frame E L ms m0 R0 (R1 :: rs) i Hr Hb0 Hs0 Hk Hm0 ltac:(lia) ltac:(unfold two64 in *; lia)).
Qed.

Theorem H_INT_F_ok : hand_okx ASEGS xok_spd H_INT_F.
Proof. apply hx_ok. exact int_kit_f. Qed.
