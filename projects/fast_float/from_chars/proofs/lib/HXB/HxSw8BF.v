(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
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
From OSSVerify.Proofs.fast_float.from_chars.lib.HXB Require Import HxGenFp HxSemB HxBaseB HxIntBF HxDefsBF HxSw8BWF.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Theorem sw8_kit : hx_kitm_fp BSEGS xok_spd 0x9b14c SW8_KEYS sw8_chk SW8_EXITS.
Proof.
  intros L XL E ms m0 Hpc Hchk Hw Hd HxF Hm0.
  unfold sw8_chk in Hchk. cbn [xs_st xs_x] in Hchk.
  destruct (s_resv L) eqn:Hrv; try discriminate.
  apply andb_prop in Hchk as [Hchk Hfx]. apply andb_prop in Hchk as [Hchk Hcs]. apply andb_prop in Hchk as [Hchk H1627].
  apply andb_prop in Hchk as [Hchk H624]. apply andb_prop in Hchk as [Hchk H12]. apply andb_prop in Hchk as [Hrg H19].
  apply lin_eqb_eq in H19, H12, H624, H1627.
  unfold SW8_CONSTS in Hcs. cbn [forallb] in Hcs. cbv beta iota in Hcs.
  repeat match type of Hcs with (?a && ?b)%bool = true => apply andb_prop in Hcs as [?C Hcs] end.
  apply lin_eqb_eq in C, C0, C1, C2, C3, C4, C5, C6, C7.
  rewrite forallb_app in Hfx. apply andb_prop in Hfx as [Hfx HfS].
  pose proof (txt_bounds E ms L Hd Hfx) as (B1 & B2 & B3 & B4 & B5 & B6).
  destruct (txt_bytes E ms L Hd Hrg Hfx) as (bs & TXT & Hlen).
  pose proof (txt_shadow E ms L Hd Hrg Hfx) as SHT.
  destruct (sden_0 _ _ _ _ Hd) as (Hpc0 & Hsvc0 & Hresv0 & HR & HG & HD & HF & Hfrm).
  rewrite Hrv in Hresv0. cbn [rsv_ok] in Hresv0.
  set (Tz := bv_unsigned (E 1%positive)) in *. set (Lz := bv_unsigned (E 2%positive)) in *.
  set (Y0z := bv_unsigned (E 7%positive)) in *. set (Y1z := bv_unsigned (E 8%positive)) in *.
  set (Xl := rgl L 24) in *. set (Xz := bv_unsigned (lden E Xl)).
  set (A1z := bv_unsigned (lden E (rgl L 11))). set (S8z := bv_unsigned (lden E (rgl L 1))).
  pose proof (bv_unsigned_in_range _ (lden E Xl)) as BX. pose proof (bv_unsigned_in_range _ (lden E (rgl L 11))) as BA1.
  pose proof (bv_unsigned_in_range _ (lden E (rgl L 1))) as BS8.
  unfold bv_modulus in BX, BA1, BS8. change (2 ^ Z.of_N 64) with two64 in BX, BA1, BS8.
  unfold sw8_facts in HfS. fold Xl in HfS. cbn [forallb] in HfS.
  repeat match type of HfS with (?a && ?b)%bool = true => apply andb_prop in HfS as [?F HfS] end.
  pose proof (fact_implied_ok E _ _ HF F) as X1. pose proof (fact_implied_ok E _ _ HF F0) as X2.
  pose proof (fact_implied_ok E _ _ HF F1) as X3. pose proof (fact_implied_ok E _ _ HF F2) as X4.
  pose proof (fact_implied_ok E _ _ HF F3) as X5.
  cbn [fact_ok] in X1, X2, X3, X4, X5. rewrite (u_sub E) in X1, X2, X3, X4. rewrite (u_sub E) in X3.
  rewrite (u_scale E), lden_laddc, u_Z_to_bv in X4. rewrite lden_laddc, u_Z_to_bv in X5.
  unfold TXT_TL, TXT_T, TXT_L in X1, X2, X3. rewrite (u_add E) in X2, X3. rewrite !lden_lvar in X1. rewrite !lden_lvar in X2.
  rewrite !lden_lvar in X3. fold Tz Lz Xz A1z S8z in X1, X2, X3, X4, X5.
  assert (M3 : (Tz + Lz) mod two64 = Tz + Lz) by (apply Z.mod_small; unfold two64 in *; lia).
  rewrite M3 in X2, X3.
  assert (HS : Tz <= Xz /\ Xz + 8 <= Tz + Lz) by (clear -X1 X2 BX B1 B2; unfold two64 in *; split; Z.div_mod_to_equations; lia).
  assert (HA1 : A1z = Tz + Lz - Xz).
  { clear -X3 HS BX BA1 B1 B2. unfold two64 in *. rewrite (Z.mod_small (Tz + Lz - Xz)) in X3 by lia.
    Z.div_mod_to_equations. lia. }
  assert (HS8 : S8z = ASAN_B + Xz / 8).
  { set (d := (S8z + - SHBz) mod two64) in *.
    assert (Hd8 : 0 <= d <= 2 ^ 48) by exact X5.
    assert (M8 : (8 * d) mod two64 = 8 * d) by (apply Z.mod_small; unfold two64; lia).
    rewrite M8 in X4.
    assert (HX8 : 8 * d <= Xz <= 8 * d + 7).
    { clear -X4 Hd8 HS BX B2. unfold two64 in *. Z.div_mod_to_equations. lia. }
    assert (Hq : d = Xz / 8) by (clear -HX8; Z.div_mod_to_equations; lia).
    assert (HdS : d = S8z - SHBz).
    { clear -X5 BS8 Hd8. unfold d, SHBz, two64 in *. Z.div_mod_to_equations. lia. }
    unfold SHBz in HdS. lia. }
  clear X1 X2 X3 X4 X5.
  assert (RG : forall k, getr (ms_regs ms) (Z_to_bv 5 k) = lden E (rgl L k)) by (intros k; rewrite (HR _); reflexivity).
  assert (Rc : forall k c, rgl L k = lconst c -> getr (ms_regs ms) (Z_to_bv 5 k) = Z_to_bv 64 c).
  { intros k c Hk. rewrite (RG k), Hk, lden_lconst. reflexivity. }
  assert (R10 : getr (ms_regs ms) 10%bv = Z_to_bv 64 10) by (exact (Rc 10 _ C)).
  assert (R13 : getr (ms_regs ms) 13%bv = Z_to_bv 64 7) by (exact (Rc 13 _ C0)).
  assert (R17 : getr (ms_regs ms) 17%bv = Z_to_bv 64 14974415777481871312) by (exact (Rc 17 _ C1)).
  assert (R28 : getr (ms_regs ms) 28%bv = Z_to_bv 64 9259542123273814144) by (exact (Rc 28 _ C2)).
  assert (R29 : getr (ms_regs ms) 29%bv = Z_to_bv 64 5063812098665367110) by (exact (Rc 29 _ C3)).
  assert (R30 : getr (ms_regs ms) 30%bv = Z_to_bv 64 100000000) by (exact (Rc 30 _ C4)).
  assert (R31 : getr (ms_regs ms) 31%bv = Z_to_bv 64 4294967296000100) by (exact (Rc 31 _ C5)).
  assert (R25 : getr (ms_regs ms) 25%bv = Z_to_bv 64 42949672960001) by (exact (Rc 25 _ C6)).
  assert (R26 : getr (ms_regs ms) 26%bv = Z_to_bv 64 1095216660735) by (exact (Rc 26 _ C7)).
  assert (R19 : getr (ms_regs ms) 19%bv = Z_to_bv 64 ASAN_B) by (exact (Rc 19 _ H19)).
  assert (Rw : forall k z, bv_unsigned (lden E (rgl L k)) = z -> getr (ms_regs ms) (Z_to_bv 5 k) = Z_to_bv 64 z).
  { intros k z Hz. rewrite RG. rewrite <- Hz. symmetry. apply Z_to_bv_bv_unsigned. }
  assert (R24' : getr (ms_regs ms) 24%bv = Z_to_bv 64 (Tz + (Xz - Tz))) by (apply (Rw 24); fold Xl Xz; ring).
  assert (R6' : getr (ms_regs ms) 6%bv = Z_to_bv 64 (Tz + (Xz - Tz))) by (apply (Rw 6); rewrite H624; fold Xl Xz; ring).
  assert (R11 : getr (ms_regs ms) 11%bv = Z_to_bv 64 (Z.of_nat (length bs) - (Xz - Tz))) by (apply (Rw 11); fold A1z; rewrite HA1, Hlen; ring).
  assert (R1 : getr (ms_regs ms) 1%bv = Z_to_bv 64 (ASAN_B + (Tz + (Xz - Tz)) / 8)).
  { apply (Rw 1). fold S8z. rewrite HS8. f_equal. f_equal. ring. }
  assert (R12 : getr (ms_regs ms) 12%bv = Z_to_bv 64 (Tz + (Xz - Tz) + 7)).
  { transitivity (lden E (rgl L 12)); [exact (RG 12)|]. rewrite H12. rewrite lden_laddc. fold Xl Xz. f_equal. ring. }
  assert (R27 : getr (ms_regs ms) 27%bv = getr (ms_regs ms) 16%bv).
  { transitivity (lden E (rgl L 27)); [exact (RG 27)|]. rewrite <- H1627. symmetry. exact (RG 16). }
  set (R := ms_regs ms) in *.
  assert (HK : evt BSEGS (sw8_post (getr R 2) (getr R 3) (getr R 4) (getr R 8) (getr R 9) (getr R 20) (getr R 21) (getr R 22) (getr R 16)
                 (ms_fregs ms) (ms_fcsr ms) (ms_mem ms) bs Tz Xz)
             (kms BSEGS ms)).
  { assert (P1 : 1 <= Z.of_nat (length bs) <= 128) by (clear -Hlen B1; lia).
    assert (P2 : 6537216 <= Tz <= 140737488355072) by (clear -B2; lia).
    assert (P3 : 8 * Y0z <= Tz /\ Tz + Z.of_nat (length bs) <= 8 * Y1z) by (clear -Hlen B5 B6; lia).
    assert (P4 : Tz <= Xz) by (clear -HS; lia).
    unfold kms, mkR_of. fold R. rewrite Hpc0, Hresv0, R1, R6', R10, R11, R12, R13, R17, R19, R24', R25, R26, R27, R28, R29, R30, R31, Hpc.
    exact (loop8 _ _ _ _ _ _ _ _ _ _ _ _ bs Tz Xz Y0z Y1z TXT P1 P2 SHT P3 P4 (Datatypes.S (Z.to_nat (Z.of_nat (length bs) - (Xz - Tz))))
             (Xz - Tz) _ _ _ _ _ _ ltac:(clear; lia) ltac:(clear; lia) ltac:(clear -Hlen HS; lia) ltac:(replace (Xz - Tz) with (Xz - Tz) by lia; apply digs_nil)). }
  destruct (kit_run BSEGS _ ms Hsvc0 HK) as (ms1 & ms2 & Hst & Heq & Hpost). clear HK.
  destruct Hpost as (y1 & y5 & y6 & y7 & y11 & y12 & y14 & y15 & y18 & y23 & y24 & y27 & Hms2 & HFE & HA1' & HDG).
  set (vs := [y1; y5; y6; y7; y11; y12; y14; y15; y18; y23; y24; y27]).
  set (E' := E_of SW8_KEYS vs (s_next L) E).
  assert (Hy24 : E' (fv (s_next L) 10) = y24) by (exact (E_of_nth SW8_KEYS vs (s_next L) E 10 y24 eq_refl eq_refl)).
  assert (Hy11 : E' (fv (s_next L) 4) = y11) by (exact (E_of_nth SW8_KEYS vs (s_next L) E 4 y11 eq_refl eq_refl)).
  assert (Hy6 : E' (fv (s_next L) 2) = y6) by (exact (E_of_nth SW8_KEYS vs (s_next L) E 2 y6 eq_refl eq_refl)).
  assert (Hy12 : E' (fv (s_next L) 5) = y12) by (exact (E_of_nth SW8_KEYS vs (s_next L) E 5 y12 eq_refl eq_refl)).
  assert (Hy27 : E' (fv (s_next L) 11) = y27) by (exact (E_of_nth SW8_KEYS vs (s_next L) E 11 y27 eq_refl eq_refl)).
  assert (Hag : agree (s_next L) E E') by apply E_of_agree.
  unfold state_wf in Hw. apply andb_prop in Hw as [Hw _]. apply andb_prop in Hw as [Hw _]. apply andb_prop in Hw as [Hwr Hwg].
  assert (HwX : lwf (s_next L) Xl = true) by (exact (regs_wf_n_spec _ _ 31 Hwr 24%nat ltac:(lia))).
  assert (Hw16 : lwf (s_next L) (rgl L 16) = true) by (exact (regs_wf_n_spec _ _ 31 Hwr 16%nat ltac:(lia))).
  assert (EX : lden E' Xl = lden E Xl) by (symmetry; exact (lden_agree _ E E' Xl HwX Hag)).
  assert (E16 : lden E' (rgl L 16) = lden E (rgl L 16)) by (symmetry; exact (lden_agree _ E E' _ Hw16 Hag)).
  assert (Hv12 : (1 < s_next L)%positive /\ (2 < s_next L)%positive).
  { unfold txt_rgs_ok in Hrg. destruct (s_rgs L) as [|R0 [|R1' rs]] eqn:Hr; try discriminate.
    apply andb_prop in Hrg as [H0 _]. unfold rg_is in H0. apply andb_prop in H0 as [H0 _]. apply andb_prop in H0 as [H0 _].
    apply andb_prop in H0 as [Hb0 Hs0]. apply lin_eqb_eq in Hb0, Hs0. cbn [forallb] in Hwg. apply andb_prop in Hwg as [Hw0 _].
    unfold rwf in Hw0. apply andb_prop in Hw0 as [Hw0 _]. apply andb_prop in Hw0 as [Hw0a Hw0b]. rewrite Hb0 in Hw0a. rewrite Hs0 in Hw0b.
    unfold lwf, TXT_T, TXT_L, lvar in Hw0a, Hw0b. cbn in Hw0a, Hw0b. apply andb_prop in Hw0a as [Hw0a _]. apply andb_prop in Hw0b as [Hw0b _].
    apply Pos.ltb_lt in Hw0a, Hw0b. split; assumption. }
  assert (E1' : E' 1%positive = E 1%positive) by (unfold E'; apply E_of_old; lia).
  assert (E2' : E' 2%positive = E 2%positive) by (unfold E'; apply E_of_old; lia).
  pose proof (bv_unsigned_in_range _ y24) as BY. unfold bv_modulus in BY. change (2 ^ Z.of_N 64) with two64 in BY.
  assert (COMMON : forall pc1 (msx : machine_state),
     msx = MS (mkR y1 (getr R 2) (getr R 3) (getr R 4) y5 y6 y7 (getr R 8) (getr R 9) (Z_to_bv 64 10) y11 y12 (Z_to_bv 64 7) y14 y15 (getr R 16)
                   (Z_to_bv 64 14974415777481871312) y18 (Z_to_bv 64 ASAN_B) (getr R 20) (getr R 21) (getr R 22) y23 y24
                   (Z_to_bv 64 42949672960001) (Z_to_bv 64 1095216660735) y27
                   (Z_to_bv 64 9259542123273814144) (Z_to_bv 64 5063812098665367110) (Z_to_bv 64 100000000) (Z_to_bv 64 4294967296000100))
              (ms_fregs ms) (Z_to_bv 64 pc1) (ms_fcsr ms) None (ms_mem ms) (seg_rom BSEGS) ->
     ms_eqv ms1 (with_rom msx (ms_rom ms)) ->
     isteps BSEGS ms ms1 /\ length vs = length SW8_KEYS /\
      ms_mem ms1 = ms_mem ms /\ ms_fcsr ms1 = ms_fcsr ms /\ ms_resv ms1 = ms_resv ms /\ ms_svc_pending ms1 = None /\
      ms_pc_val ms1 = Z_to_bv 64 pc1 /\
      (forall r, ~ In (bv_unsigned r) SW8_KEYS -> getr (ms_regs ms1) r = getr (ms_regs ms) r) /\
      (forall i k v, nth_error SW8_KEYS i = Some k -> nth_error vs i = Some v -> getr (ms_regs ms1) (Z_to_bv 5 k) = v) /\
      (forall r, reg_get (ms_fregs ms1) r = reg_get (ms_fregs ms) r)).
  { intros pc1 msx -> Heq2. destruct Heq2 as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
    cbn [with_rom MS ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in E1, E2, E3, E4, E5, E6, E7, E8.
    split; [exact Hst|]. split; [reflexivity|]. split; [exact E7|]. split; [exact E6|]. split; [rewrite E5, Hresv0; reflexivity|].
    split; [exact E4|]. split; [exact E3|]. split; [|split; [|exact E2]].
    - intros r Hr. rewrite (E1 r). destruct (reg_of_nat r) as (n & -> & Hn). rewrite getr_mkR. rewrite u5 by lia. rewrite Nat2Z.id.
      unfold SW8_KEYS in Hr. cbn [In] in Hr. rewrite u5 in Hr by lia.
      do 32 (destruct n as [|n]; [cbn; first [reflexivity | (symmetry; exact R10) | (symmetry; exact R13) | (symmetry; exact R17)
                                              | (symmetry; exact R19) | (symmetry; exact R25) | (symmetry; exact R26) | (symmetry; exact R28)
                                              | (symmetry; exact R29) | (symmetry; exact R30) | (symmetry; exact R31)
                                              | (exfalso; apply Hr; repeat (first [left; reflexivity | right]))]|]).
      lia.
    - intros i k v Hi Hv. rewrite (E1 _).
      destruct i as [|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]; cbn in Hi, Hv;
        first [ (injection Hi as <-; injection Hv as <-; reflexivity) | (destruct i; discriminate) ]. }
  (* [comment removed for export] *)
  assert (TLE : bv_unsigned (lden E' TXT_TL) = Tz + Lz).
  { unfold TXT_TL, TXT_T, TXT_L. rewrite lden_ladd, bv_add_unsigned, !lden_lvar, E1', E2'. fold Tz Lz. unfold bv_wrap, bv_modulus.
    change (2 ^ Z.of_N 64) with two64. apply Z.mod_small. unfold two64 in *. lia. }
  assert (FACTS : Forall (fact_ok E') (sw8_newf L) /\ Forall (xfact_ok xok_spd E' m0) (sw8_newx L)).
  { split.
    - unfold sw8_newf. fold Xl. repeat apply Forall_cons; try apply Forall_nil; cbn [fact_ok].
      + rewrite lden_lsub, bv_sub_unsigned, lden_lvar, Hy24, EX. fold Xz. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64.
        rewrite Z.mod_small by (unfold two64 in *; lia). lia.
      + rewrite lden_lsub, bv_sub_unsigned, lden_lvar, Hy24. unfold TXT_T. rewrite lden_lvar, E1'. fold Tz. unfold bv_wrap, bv_modulus.
        change (2 ^ Z.of_N 64) with two64. rewrite Z.mod_small by (unfold two64 in *; lia). lia.
      + rewrite lden_lsub, bv_sub_unsigned, TLE, lden_lvar, Hy24. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64.
        rewrite Z.mod_small by (unfold two64 in *; lia). lia.
      + rewrite lden_lsub, bv_sub_unsigned, lden_lvar, Hy11, lden_lsub, bv_sub_unsigned, TLE, lden_lvar, Hy24.
        unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64.
        rewrite (Z.mod_small (Tz + Lz - bv_unsigned y24)) by (unfold two64 in *; lia). rewrite HA1', Hlen. rewrite Z.sub_diag.
        change (0 mod two64) with 0. lia.
      + rewrite lden_lvar, Hy24. unfold P47. change (2 ^ 47) with 140737488355328. clear -HFE HS B1 B2 Hlen. lia.
    - unfold sw8_newx. fold Xl. constructor; [|constructor]. unfold xfact_ok. cbn [xf_tag xf_args List.map xok_spd].
      rewrite EX, lden_lvar, Hy24. fold Xz.
      exists Tz, bs. split.
      + apply (bytes_at_transport (ms_mem ms)); [exact TXT|]. intros i Hi.
        unfold txt_rgs_ok in Hrg. destruct (s_rgs L) as [|R0 [|R1' rs]] eqn:Hr; try discriminate.
        apply andb_prop in Hrg as [H0 _]. unfold rg_is in H0. apply andb_prop in H0 as [H0 _]. apply andb_prop in H0 as [H0 Hk0].
        apply andb_prop in H0 as [Hb0 Hs0]. apply lin_eqb_eq in Hb0, Hs0. destruct (rg_kind R0) eqn:Hk; cbn in Hk0; try discriminate.
        rewrite <- Hr in Hm0. exact (txt_frame E L ms m0 R0 (R1' :: rs) i Hr Hb0 Hs0 Hk Hm0 ltac:(lia) ltac:(unfold two64 in *; lia)).
      + split; [lia|]. split; [lia|]. exact HDG. }
  destruct Hms2 as [(Hms2 & H624' & H8)|(Hms2 & H127 & H27 & H7)].
  - exists 0x9b6e0, sw8_newfA, sw8_newx, ms1, vs. split; [left; reflexivity|].
    destruct (COMMON 0x9b6e0 ms2 Hms2 Heq) as (C1' & C2' & C3' & C4' & C5' & C6' & C7' & C8' & C9' & C10').
    do 9 (split; [assumption|]). fold E'. destruct FACTS as [FA FX]. split; [|split; [exact FX | exact C10']].
    unfold sw8_newfA. constructor; [|constructor; [|exact FA]]; cbn [fact_ok].
    + rewrite lden_lsub, bv_sub_unsigned, TLE, lden_lvar, Hy24. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64.
      rewrite Z.mod_small by (unfold two64 in *; lia). rewrite <- Hlen in *. lia.
    + rewrite lden_lsub, bv_sub_unsigned, !lden_lvar, Hy6, Hy24, H624', Z.sub_diag. unfold bv_wrap. rewrite Z.mod_0_l by (unfold bv_modulus; lia). lia.
  - exists 0x9b700, sw8_newfB, sw8_newx, ms1, vs. split; [right; left; reflexivity|].
    destruct (COMMON 0x9b700 ms2 Hms2 Heq) as (C1' & C2' & C3' & C4' & C5' & C6' & C7' & C8' & C9' & C10').
    do 9 (split; [assumption|]). fold E'. destruct FACTS as [FA FX]. split; [|split; [exact FX | exact C10']].
    unfold sw8_newfB. constructor; [|constructor; [|constructor; [|exact FA]]]; cbn [fact_ok].
    + rewrite lden_lsub, bv_sub_unsigned, TLE, lden_lvar, Hy24. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64.
      rewrite Z.mod_small by (unfold two64 in *; lia). rewrite <- Hlen in *. lia.
    + rewrite lden_lsub, bv_sub_unsigned, lden_lvar, Hy12, lden_laddc, lden_lvar, Hy24, u_Z_to_bv, H127.
      unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64.
      rewrite (Z.mod_small (bv_unsigned y24 + 7)) by (unfold two64 in *; lia). rewrite Z.sub_diag. change (0 mod two64) with 0. lia.
    + rewrite lden_lsub, bv_sub_unsigned, lden_lvar, Hy27, E16, H27. unfold R.
      replace (getr (ms_regs ms) 16) with (lden E (rgl L 16)) by (symmetry; exact (RG 16)). rewrite Z.sub_diag.
      unfold bv_wrap. rewrite Z.mod_0_l by (unfold bv_modulus; lia). lia.
Qed.

Theorem H_SW8_ok : hand_okx_fp BSEGS xok_spd H_SW8.
Proof. apply hx_okm_fp. exact sw8_kit. Qed.
