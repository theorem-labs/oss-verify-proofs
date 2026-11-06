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
From OSSVerify.Proofs.fast_float.from_chars.lib.HXB Require Import HxGenFp HxSemB HxBaseB HxIntB HxDefsB HxDigpB HxSw4B HxByteBW.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Theorem byte_kit : hx_kitm_fp BSEGS xok_spd 0x93954 BYTE_KEYS byte_chk [(0x939bc, byte_newf, byte_newx)].
Proof.
  intros L XL E ms m0 Hpc Hchk Hw Hd HxF Hm0.
  unfold byte_chk in Hchk. cbn [xs_st xs_x] in Hchk.
  destruct (s_resv L) eqn:Hrv; try discriminate.
  destruct (fp_of L) as [FPl|] eqn:Hfp; [|discriminate].
  apply andb_prop in Hchk as [Hchk Hx0]. apply andb_prop in Hchk as [Hchk Hfx]. apply andb_prop in Hchk as [Hchk H22].
  apply andb_prop in Hchk as [Hrg H19]. apply lin_eqb_eq in H19, H22.
  rewrite forallb_app in Hfx. apply andb_prop in Hfx as [Hfx HfS].
  rewrite forallb_app in HfS. apply andb_prop in HfS as [HfS HfFP]. cbn [forallb] in HfFP. apply andb_prop in HfFP as [HfFP _].
  pose proof (txt_bounds E ms L Hd Hfx) as (B1 & B2 & B3 & B4 & B5 & B6).
  destruct (txt_bytes E ms L Hd Hrg Hfx) as (bs & TXT & Hlen).
  pose proof (txt_shadow E ms L Hd Hrg Hfx) as SHT.
  destruct (sden_0 _ _ _ _ Hd) as (Hpc0 & Hsvc0 & Hresv0 & HR & HG & HD & HF & Hfrm).
  rewrite Hrv in Hresv0. cbn [rsv_ok] in Hresv0.
  pose proof (fact_implied_ok E _ _ HF HfFP) as XFP. cbn [fact_ok] in XFP. rewrite (u_sub E) in XFP. unfold TXT_T in XFP. rewrite lden_lvar in XFP.
  set (Tz := bv_unsigned (E 1%positive)) in *. set (Lz := bv_unsigned (E 2%positive)) in *.
  set (Y0z := bv_unsigned (E 7%positive)) in *. set (Y1z := bv_unsigned (E 8%positive)) in *.
  set (Xl := rgl L 24) in *. set (Xz := bv_unsigned (lden E Xl)).
  set (FPz := bv_unsigned (lden E FPl)) in *.
  pose proof (bv_unsigned_in_range _ (lden E Xl)) as BX. pose proof (bv_unsigned_in_range _ (lden E FPl)) as BFP.
  unfold bv_modulus in BX, BFP. change (2 ^ Z.of_N 64) with two64 in BX, BFP. fold Xz in BX. fold FPz in BFP.
  unfold byte_facts in HfS. fold Xl in HfS. cbn [forallb] in HfS.
  repeat match type of HfS with (?a && ?b)%bool = true => apply andb_prop in HfS as [?F HfS] end.
  pose proof (fact_implied_ok E _ _ HF F) as X1. pose proof (fact_implied_ok E _ _ HF F0) as X2.
  cbn [fact_ok] in X1, X2. rewrite (u_sub E) in X1, X2. unfold TXT_TL, TXT_T, TXT_L in X1, X2.
  rewrite (u_add E) in X2. rewrite !lden_lvar in X1. rewrite !lden_lvar in X2. fold Tz Lz Xz in X1, X2.
  assert (M3 : (Tz + Lz) mod two64 = Tz + Lz) by (apply Z.mod_small; unfold two64 in *; lia).
  rewrite M3 in X2.
  assert (HS : Tz <= Xz /\ Xz <= Tz + Lz) by (clear -X1 X2 BX B1 B2; unfold two64 in *; split; Z.div_mod_to_equations; lia).
  assert (HFT : Tz <= FPz) by (clear -XFP BFP B2; unfold two64 in *; Z.div_mod_to_equations; lia).
  assert (RG : forall k, getr (ms_regs ms) (Z_to_bv 5 k) = lden E (rgl L k)) by (intros k; rewrite (HR _); reflexivity).
  assert (Rw : forall k z, bv_unsigned (lden E (rgl L k)) = z -> getr (ms_regs ms) (Z_to_bv 5 k) = Z_to_bv 64 z).
  { intros k z Hz. rewrite RG. rewrite <- Hz. symmetry. apply Z_to_bv_bv_unsigned. }
  assert (R19 : getr (ms_regs ms) 19%bv = Z_to_bv 64 ASAN_B).
  { transitivity (lden E (rgl L 19)); [exact (RG 19)|]. rewrite H19. rewrite lden_lconst. reflexivity. }
  assert (R22 : getr (ms_regs ms) 22%bv = Z_to_bv 64 (Tz + Z.of_nat (length bs))).
  { transitivity (lden E (rgl L 22)); [exact (RG 22)|]. rewrite H22. unfold TXT_TL, TXT_T, TXT_L. rewrite lden_ladd, !lden_lvar.
    apply bv_eq. rewrite bv_add_unsigned, u_Z_to_bv. rewrite Hlen. reflexivity. }
  assert (R24' : getr (ms_regs ms) 24%bv = Z_to_bv 64 (Tz + (Xz - Tz))) by (apply (Rw 24); fold Xl Xz; ring).
  (* [comment removed for export] *)
  apply existsb_exists in Hx0 as (f0 & Hf0 & Hq0). apply xf_eqb_eq in Hq0. subst f0.
  rewrite Forall_forall in HxF. pose proof (HxF _ Hf0) as XD.
  unfold xfact_ok in XD. cbn [xf_tag xf_args List.map xok_spd] in XD. fold Xl in XD. fold FPz Xz in XD.
  assert (TXT0 : bytes_at BSEGS m0 Tz bs).
  { apply (bytes_at_transport (ms_mem ms)); [exact TXT|]. intros i Hi.
    unfold txt_rgs_ok in Hrg. destruct (s_rgs L) as [|R0 [|R1 rs]] eqn:Hr; try discriminate.
    apply andb_prop in Hrg as [H0 _]. unfold rg_is in H0. apply andb_prop in H0 as [H0 _]. apply andb_prop in H0 as [H0 Hk0].
    apply andb_prop in H0 as [Hb0 Hs0]. apply lin_eqb_eq in Hb0, Hs0. destruct (rg_kind R0) eqn:Hk; cbn in Hk0; try discriminate.
    rewrite <- Hr in Hm0. exact (txt_frame E L ms m0 R0 (R1 :: rs) i Hr Hb0 Hs0 Hk Hm0 ltac:(lia) ltac:(unfold two64 in *; lia)). }
  set (R := ms_regs ms) in *.
  assert (HK : evt BSEGS (byte_post (getr R 1) (getr R 2) (getr R 3) (getr R 4) (getr R 5) (getr R 6) (getr R 7) (getr R 8) (getr R 9) (getr R 10)
                 (getr R 18) (getr R 20) (getr R 21) (getr R 23) (getr R 25) (getr R 26) (getr R 27) (getr R 28) (getr R 29) (getr R 30) (getr R 31)
                 (ms_fregs ms) (ms_fcsr ms) (ms_mem ms) bs Tz Xz)
             (kms BSEGS ms)).
  { assert (P1 : 1 <= Z.of_nat (length bs) <= 128) by (clear -Hlen B1; lia).
    assert (P2 : 6537216 <= Tz <= 140737488355072) by (clear -B2; lia).
    assert (P3 : 8 * Y0z <= Tz /\ Tz + Z.of_nat (length bs) <= 8 * Y1z) by (clear -Hlen B5 B6; lia).
    assert (P4 : Tz <= Xz) by (clear -HS; lia).
    unfold kms, mkR_of. fold R. rewrite Hpc0, Hresv0, R19, R22, R24', Hpc.
    eapply (blockB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bs Tz Xz Y0z Y1z);
      first [ exact TXT | exact P1 | exact P2 | exact SHT | exact P3 | exact P4 | apply digs_nil | (clear -HS Hlen; lia) ]. }
  destruct (kit_run BSEGS _ ms Hsvc0 HK) as (ms1 & ms2 & Hst & Heq & Hpost). clear HK.
  destruct Hpost as (y11 & y12 & y13 & y14 & y15 & y16 & y17 & y24 & Hms2 & HFE & HDG). subst ms2.
  destruct Heq as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
  cbn [with_rom MS ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in E1, E2, E3, E4, E5, E6, E7, E8.
  set (vs := [y11; y12; y13; y14; y15; y16; y17; y24]).
  set (E' := E_of BYTE_KEYS vs (s_next L) E).
  assert (Hy24 : E' (fv (s_next L) 7) = y24) by (exact (E_of_nth BYTE_KEYS vs (s_next L) E 7 y24 eq_refl eq_refl)).
  assert (Hag : agree (s_next L) E E') by apply E_of_agree.
  unfold state_wf in Hw. apply andb_prop in Hw as [Hw _]. apply andb_prop in Hw as [Hw _]. apply andb_prop in Hw as [Hwr Hwg].
  assert (HwX : lwf (s_next L) Xl = true) by (exact (regs_wf_n_spec _ _ 31 Hwr 24%nat ltac:(lia))).
  assert (EX : lden E' Xl = lden E Xl) by (symmetry; exact (lden_agree _ E E' Xl HwX Hag)).
  assert (HwFP : lwf (s_next L) FPl = true).
  { unfold fp_of in Hfp. destruct (find_cell (s_rgs L) (laddc (rgl L 9) 56)) as [[[Rc o] l0]|] eqn:Hfc; [|discriminate].
    injection Hfp as ->. exact (find_cell_lwf _ _ _ _ _ _ Hwg Hfc). }
  assert (EFP : lden E' FPl = lden E FPl) by (symmetry; exact (lden_agree _ E E' FPl HwFP Hag)).
  assert (Hv12 : (1 < s_next L)%positive /\ (2 < s_next L)%positive).
  { unfold txt_rgs_ok in Hrg. destruct (s_rgs L) as [|R0 [|R1 rs]] eqn:Hr; try discriminate.
    apply andb_prop in Hrg as [H0 _]. unfold rg_is in H0. apply andb_prop in H0 as [H0 _]. apply andb_prop in H0 as [H0 _].
    apply andb_prop in H0 as [Hb0 Hs0]. apply lin_eqb_eq in Hb0, Hs0. cbn [forallb] in Hwg. apply andb_prop in Hwg as [Hw0 _].
    unfold rwf in Hw0. apply andb_prop in Hw0 as [Hw0 _]. apply andb_prop in Hw0 as [Hw0a Hw0b]. rewrite Hb0 in Hw0a. rewrite Hs0 in Hw0b.
    unfold lwf, TXT_T, TXT_L, lvar in Hw0a, Hw0b. cbn in Hw0a, Hw0b. apply andb_prop in Hw0a as [Hw0a _]. apply andb_prop in Hw0b as [Hw0b _].
    apply Pos.ltb_lt in Hw0a, Hw0b. split; assumption. }
  assert (E1' : E' 1%positive = E 1%positive) by (unfold E'; apply E_of_old; lia).
  assert (E2' : E' 2%positive = E 2%positive) by (unfold E'; apply E_of_old; lia).
  assert (TLE : bv_unsigned (lden E' TXT_TL) = Tz + Lz).
  { unfold TXT_TL, TXT_T, TXT_L. rewrite lden_ladd, bv_add_unsigned, !lden_lvar, E1', E2'. fold Tz Lz. unfold bv_wrap, bv_modulus.
    change (2 ^ Z.of_N 64) with two64. apply Z.mod_small. unfold two64 in *. lia. }
  assert (XD' : digp m0 FPz (bv_unsigned y24)).
  { apply (digp_extend m0 FPz Xz (bv_unsigned y24) Tz bs XD TXT0); [lia | lia | lia | exact HDG]. }
  pose proof XD as (Td & bsd & _ & (Hd1 & Hd2) & _).
  pose proof (bv_unsigned_in_range _ y24) as BY. unfold bv_modulus in BY. change (2 ^ Z.of_N 64) with two64 in BY.
  exists 0x939bc, byte_newf, byte_newx, ms1, vs. split; [left; reflexivity|].
  split; [exact Hst|]. split; [reflexivity|]. split; [exact E7|]. split; [exact E6|]. split; [rewrite E5, Hresv0; reflexivity|].
  split; [exact E4|]. split; [exact E3|].
  split; [|split; [|split; [|split; [|exact E2]]]].
  - intros r Hr. rewrite (E1 r). destruct (reg_of_nat r) as (n & -> & Hn). rewrite getr_mkR. rewrite u5 by lia. rewrite Nat2Z.id.
    unfold BYTE_KEYS in Hr. cbn [In] in Hr. rewrite u5 in Hr by lia.
    do 32 (destruct n as [|n]; [cbn; first [reflexivity | (symmetry; exact R19) | (symmetry; exact R22)
                                            | (exfalso; apply Hr; repeat (first [left; reflexivity | right]))]|]).
    lia.
  - intros i k v Hi Hv. rewrite (E1 _).
    destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; cbn in Hi, Hv;
      first [ (injection Hi as <-; injection Hv as <-; reflexivity) | (destruct i; discriminate) ].
  - fold E'. unfold byte_newf, fp_facts. rewrite Hfp. fold Xl. cbn [app].
    repeat apply Forall_cons; try apply Forall_nil; cbn [fact_ok].
    + rewrite lden_lsub, bv_sub_unsigned, lden_lvar, Hy24, EFP. fold FPz. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64.
      rewrite Z.mod_small by (unfold two64 in *; lia). clear -HFE HS Hd1 Hd2 B1 Hlen HFT. lia.
    + rewrite lden_lsub, bv_sub_unsigned, lden_lvar, Hy24, EX. fold Xz. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64.
      rewrite Z.mod_small by (unfold two64 in *; lia). clear -HFE HS B1 Hlen. lia.
    + rewrite lden_lsub, bv_sub_unsigned, lden_lvar, Hy24. unfold TXT_T. rewrite lden_lvar, E1'. fold Tz. unfold bv_wrap, bv_modulus.
      change (2 ^ Z.of_N 64) with two64. rewrite Z.mod_small by (unfold two64 in *; lia). clear -HFE HS B1 Hlen. lia.
    + rewrite lden_lsub, bv_sub_unsigned, TLE, lden_lvar, Hy24. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64.
      rewrite Z.mod_small by (unfold two64 in *; lia). clear -HFE HS B1 Hlen. lia.
    + rewrite lden_lvar, Hy24. unfold P47. change (2 ^ 47) with 140737488355328. clear -HFE HS B1 B2 Hlen. lia.
  - fold E'. unfold byte_newx. rewrite Hfp. constructor; [|constructor]. unfold xfact_ok. cbn [xf_tag xf_args List.map xok_spd].
    rewrite EFP, lden_lvar, Hy24. fold FPz. exact XD'.
Qed.

Theorem H_BYTE_ok : hand_okx_fp BSEGS xok_spd H_BYTE.
Proof. apply hx_okm_fp. exact byte_kit. Qed.
