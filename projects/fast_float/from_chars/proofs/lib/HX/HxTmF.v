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
From OSSVerify.Proofs.fast_float.from_chars.lib.HX Require Import HxGen HxSem HxInt HxTm HxTmFW.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition tm_facts_f (L : sst) : list fact :=
  let S := rgl L 22 in let IE := rgl L 10 in let fL := rgl L 12 in
  [FRange (lsub S TXT_T) 0 128; FRange (lsub IE S) 0 128; FRange (lsub TXT_TL IE) 0 128; FRange fL 0 128;
   FRange (lsub (rgl L 5) (ladd (lsub IE S) fL)) 0 0].
Definition tm_chk_f (X : xst) : bool :=
  let L := xs_st X in
  match s_resv L, is_const (rgl L 24) with
  | RNone, Some t3c =>
      (txt_rgs_ok L && lin_eqb (rgl L 23) TXT_TL && lin_eqb (rgl L 19) (lconst SHBz) && Z.eqb (t3c mod 256) 46 && rod_ok (s_rgs L)
       && forallb (fact_implied (s_facts L)) (txt_facts ++ tm_facts_f L)
       && existsb (xf_eqb (XF 0 [rgl L 22; rgl L 10])) (xs_x X)
       && existsb (xf_eqb (XF 1 [rgl L 10; rgl L 1; rgl L 12; TXT_TL])) (xs_x X))%bool
  | _, _ => false
  end.
Definition TM_EXITS_F : list hx_exit := [(0x9b51c, tm_newf0, nox); (0x9b51c, tm_newf1, nox)].
Definition H_TM_F : xst -> option (list xst) := hx_regm 0x9a3dc TM_KEYS tm_chk_f TM_EXITS_F.

Theorem tm_kit_f : hx_kitm ASEGS xok_spd 0x9a3dc TM_KEYS tm_chk_f TM_EXITS_F.
Proof.
  intros L XL E ms m0 Hpc Hchk Hw Hd HxF Hm0.
  unfold tm_chk_f in Hchk. cbn [xs_st xs_x] in Hchk.
  destruct (s_resv L) eqn:Hrv; try discriminate.
  destruct (is_const (rgl L 24)) as [t3c|] eqn:Ht3; [|discriminate].
  apply andb_prop in Hchk as [Hchk Hx1]. apply andb_prop in Hchk as [Hchk Hx0]. apply andb_prop in Hchk as [Hchk Hfx].
  apply andb_prop in Hchk as [Hchk Hrod]. apply andb_prop in Hchk as [Hchk Ht3m]. apply andb_prop in Hchk as [Hchk H19].
  apply andb_prop in Hchk as [Hrg H23]. apply lin_eqb_eq in H23, H19. apply Z.eqb_eq in Ht3m.
  rewrite forallb_app in Hfx. apply andb_prop in Hfx as [Hfx HfS].
  pose proof (txt_bounds E ms L Hd Hfx) as (B1 & B2 & B3 & B4 & B5 & B6).
  destruct (txt_bytes E ms L Hd Hrg Hfx) as (bs & TXT & Hlen).
  pose proof (txt_shadow E ms L Hd Hrg Hfx) as SHT.
  destruct (sden_0 _ _ _ _ Hd) as (Hpc0 & Hsvc0 & Hresv0 & HR & HG & HD & HF & Hfrm).
  rewrite Hrv in Hresv0. cbn [rsv_ok] in Hresv0.
  set (Tz := bv_unsigned (E 1%positive)) in *. set (Lz := bv_unsigned (E 2%positive)) in *.
  set (Y0z := bv_unsigned (E 7%positive)) in *. set (Y1z := bv_unsigned (E 8%positive)) in *.
  set (S := rgl L 22) in *. set (IE := rgl L 10) in *. set (fLl := rgl L 12) in *. set (fpl := rgl L 1) in *.
  set (Sz := bv_unsigned (lden E S)). set (IEz := bv_unsigned (lden E IE)). set (fLz := bv_unsigned (lden E fLl)).
  set (fpz := bv_unsigned (lden E fpl)).
  pose proof (bv_unsigned_in_range _ (lden E S)) as BS. pose proof (bv_unsigned_in_range _ (lden E IE)) as BIE.
  pose proof (bv_unsigned_in_range _ (lden E fLl)) as BfL.
  unfold bv_modulus in BS, BIE, BfL. change (2 ^ Z.of_N 64) with two64 in BS, BIE, BfL.
  (* [comment removed for export] *)
  unfold tm_facts_f in HfS. fold S IE fLl in HfS. cbn [forallb] in HfS.
  repeat match type of HfS with (?a && ?b)%bool = true => apply andb_prop in HfS as [?F HfS] end.
  pose proof (fact_implied_ok E _ _ HF F) as X1. pose proof (fact_implied_ok E _ _ HF F0) as X2.
  pose proof (fact_implied_ok E _ _ HF F1) as X3. pose proof (fact_implied_ok E _ _ HF F2) as X4.
  pose proof (fact_implied_ok E _ _ HF F3) as X6.
  cbn [fact_ok] in X1, X2, X3, X4, X6.
  rewrite (u_sub E) in X1, X2, X3, X6. rewrite (u_add E), (u_sub E) in X6. unfold TXT_TL, TXT_T, TXT_L in X1, X3.
  rewrite (u_add E) in X3. rewrite !lden_lvar in X1. rewrite !lden_lvar in X3.
  fold Sz Tz Lz IEz fLz in X1, X2, X3, X4, X6.
  assert (M3 : (Tz + Lz) mod two64 = Tz + Lz) by (apply Z.mod_small; unfold two64 in *; lia).
  rewrite M3 in X3.
  assert (HS : Tz <= Sz <= IEz /\ IEz <= Tz + Lz) by (unfold two64 in *; split; [split|]; Z.div_mod_to_equations; lia).
  set (dcz := bv_unsigned (lden E (rgl L 5))).
  assert (HDC : dcz = IEz - Sz + fLz).
  { unfold dcz. unfold two64 in *. rewrite (Z.mod_small (IEz - Sz)) in X6 by lia. rewrite (Z.mod_small (IEz - Sz + fLz)) in X6 by lia.
    pose proof (bv_unsigned_in_range _ (lden E (rgl L 5))) as Bd. unfold bv_modulus in Bd. change (2 ^ Z.of_N 64) with (2 ^ 64) in Bd.
    Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  assert (RG : forall k, getr (ms_regs ms) (Z_to_bv 5 k) = lden E (rgl L k)).
  { intros k. rewrite (HR _). reflexivity. }
  assert (Rw : forall k z, bv_unsigned (lden E (rgl L k)) = z -> getr (ms_regs ms) (Z_to_bv 5 k) = Z_to_bv 64 z).
  { intros k z Hz. rewrite RG. rewrite <- Hz. symmetry. apply Z_to_bv_bv_unsigned. }
  assert (RA1 : getr (ms_regs ms) 1%bv = Z_to_bv 64 fpz) by (apply (Rw 1); reflexivity).
  assert (R10 : getr (ms_regs ms) 10%bv = Z_to_bv 64 IEz) by (apply (Rw 10); reflexivity).
  assert (R12 : getr (ms_regs ms) 12%bv = Z_to_bv 64 fLz) by (apply (Rw 12); reflexivity).
  assert (R22 : getr (ms_regs ms) 22%bv = Z_to_bv 64 Sz) by (apply (Rw 22); reflexivity).
  assert (R5 : getr (ms_regs ms) 5%bv = Z_to_bv 64 ((IEz - Tz) - (Sz - Tz) + fLz)).
  { apply (Rw 5). fold dcz. rewrite HDC. ring. }
  assert (R24 : getr (ms_regs ms) 24%bv = Z_to_bv 64 t3c).
  { transitivity (lden E (rgl L 24)); [exact (RG 24)|]. destruct (is_const_sound E _ _ Ht3) as [X _]. exact X. }
  assert (Ht3r : 0 <= t3c < two64) by (exact (proj2 (is_const_sound E _ _ Ht3))).
  assert (R23 : getr (ms_regs ms) 23%bv = Z_to_bv 64 (Tz + Lz)).
  { transitivity (lden E (rgl L 23)); [exact (RG 23)|]. rewrite H23. unfold TXT_TL, TXT_T, TXT_L. rewrite lden_ladd, !lden_lvar.
    apply bv_eq. rewrite bv_add_unsigned, u_Z_to_bv. reflexivity. }
  assert (R19 : getr (ms_regs ms) 19%bv = Z_to_bv 64 ASAN_B).
  { transitivity (lden E (rgl L 19)); [exact (RG 19)|]. rewrite H19. rewrite lden_lconst. reflexivity. }
  (* [comment removed for export] *)
  assert (PR : pristine (ms_mem ms) 65536 188416).
  { unfold rod_ok in Hrod. apply existsb_exists in Hrod as (Rr & HRr & Hr). unfold rg_is in Hr.
    apply andb_prop in Hr as [Hr Hcr]. apply andb_prop in Hr as [Hr Hkr]. apply andb_prop in Hr as [Hbr Hsr].
    apply lin_eqb_eq in Hbr, Hsr. destruct (rg_kind Rr) eqn:Hk; cbn in Hkr; try discriminate.
    rewrite Forall_forall in HG.
    assert (PRb : pristine (ms_mem ms) 65536 (65536 + 188416)).
    { apply (pristine_of_rg_ro ASEGS E (ms_mem ms) Rr 65536 188416 (HG _ HRr) Hk).
      - rewrite Hbr, lden_lconst. reflexivity.
      - unfold rsz. rewrite Hsr, lden_lconst. reflexivity. }
    destruct PRb as (P1 & P2 & P3). split; [exact P1|]. split; [lia|]. intros i Hi. apply P3. lia. }
  (* [comment removed for export] *)
  apply existsb_exists in Hx0 as (f0 & Hf0 & Hq0). apply xf_eqb_eq in Hq0. subst f0.
  apply existsb_exists in Hx1 as (f1 & Hf1 & Hq1). apply xf_eqb_eq in Hq1. subst f1.
  rewrite Forall_forall in HxF. pose proof (HxF _ Hf0) as XD. pose proof (HxF _ Hf1) as XS.
  unfold xfact_ok in XD, XS. cbn [xf_tag xf_args List.map xok_spd] in XD, XS. fold Sz IEz fLz fpz in XD, XS.
  assert (TXT0 : bytes_at ASEGS m0 Tz bs).
  { apply (bytes_at_transport (ms_mem ms)); [exact TXT|]. intros i Hi.
    unfold txt_rgs_ok in Hrg. destruct (s_rgs L) as [|R0 [|R1 rs]] eqn:Hr; try discriminate.
    apply andb_prop in Hrg as [H0 _]. unfold rg_is in H0. apply andb_prop in H0 as [H0 _]. apply andb_prop in H0 as [H0 Hk0].
    apply andb_prop in H0 as [Hb0 Hs0]. apply lin_eqb_eq in Hb0, Hs0. destruct (rg_kind R0) eqn:Hk; cbn in Hk0; try discriminate.
    rewrite <- Hr in Hm0. exact (txt_frame E L ms m0 R0 (R1 :: rs) i Hr Hb0 Hs0 Hk Hm0 ltac:(lia) ltac:(unfold two64 in *; lia)). }
  destruct XD as (Td & bsd & TXd & Dd1 & Dd2 & DGd).
  assert (DGI : digs bs (Sz - Tz) (IEz - Tz)).
  { apply (digs_transport m0 Tz bs Td bsd Sz IEz TXT0 TXd); [lia | lia | lia | lia | exact DGd]. }
  assert (SPANS : ((fpz = 0 /\ fLz = 0) \/
                   (fpz = IEz + 1 /\ IEz < Tz + Lz /\ tx bs (IEz - Tz) = 46 /\ IEz + 1 + fLz <= Tz + Lz /\
                    digs bs (IEz - Tz + 1) (IEz - Tz + 1 + fLz)))%Z).
  { destruct XS as [XS|(Hfp & Hend & Ts & bss & TXs & Hs1 & Hs2 & Hdot & DGs)]; [left; exact XS|right].
    unfold TXT_TL, TXT_T, TXT_L in Hend. rewrite lden_ladd, bv_add_unsigned, !lden_lvar in Hend. fold Tz Lz in Hend.
    unfold bv_wrap, bv_modulus in Hend. change (2 ^ Z.of_N 64) with two64 in Hend. rewrite M3 in Hend.
    split; [exact Hfp|]. assert (HIEL : IEz < Tz + Lz) by lia.
    split; [exact HIEL|].
    split; [rewrite (tx_transport m0 Tz bs Ts bss IEz TXT0 TXs ltac:(lia) ltac:(lia)); exact Hdot|].
    split; [lia|].
    replace (IEz - Tz + 1 + fLz) with (IEz + 1 + fLz - Tz) by lia. replace (IEz - Tz + 1) with (IEz + 1 - Tz) by lia.
    apply (digs_transport m0 Tz bs Ts bss (IEz + 1) (IEz + 1 + fLz) TXT0 TXs); [lia | lia | lia | lia | exact DGs]. }
  (* [comment removed for export] *)
  set (R := ms_regs ms) in *.
  assert (HK : evt ASEGS (tm_post (getr R 2) (getr R 3) (getr R 4) (getr R 6) (getr R 8) (getr R 9) (getr R 17) (getr R 18)
                 (getr R 20) (getr R 21) (getr R 25) (getr R 26) (getr R 27) (getr R 29) (getr R 31)
                 (ms_fregs ms) (ms_fcsr ms) (ms_mem ms) bs Tz Sz fpz fLz t3c)
             (kms ASEGS ms)).
  { assert (P1 : 1 <= Z.of_nat (length bs) <= 128) by (clear -Hlen B1; lia).
    assert (P2 : 6529024 <= Tz <= 140737488355072) by (clear -B2; lia).
    assert (P3 : 8 * Y0z <= Tz /\ Tz + Z.of_nat (length bs) <= 8 * Y1z) by (clear -Hlen B5 B6; lia).
    assert (P4 : Tz <= Sz <= IEz /\ IEz <= Tz + Z.of_nat (length bs)) by (clear -Hlen HS; lia).
    assert (P5 : 0 <= fLz <= 128) by (clear -X4; lia).
    assert (P7 : t3c mod 256 = 46 /\ 0 <= t3c < 2 ^ 64) by (clear -Ht3m Ht3r; unfold two64 in *; lia).
    rewrite <- Hlen in SPANS.
    unfold kms, mkR_of. fold R. rewrite Hpc0, Hresv0, RA1, R5, R10, R12, R19, R22, R23, R24, Hpc. rewrite <- Hlen.
    exact (blockTM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bs Tz Sz IEz fpz fLz Y0z Y1z t3c TXT P1 P2 SHT P3 P4 DGI P5 SPANS P7 PR
             _ _ _ _ _ _ _ _). }
  destruct (kit_run ASEGS _ ms Hsvc0 HK) as (ms1 & ms2 & Hst & Heq & Hpost). clear HK.
  destruct Hpost as (y5 & y7 & y10 & y11 & y13 & y14 & y15 & y16 & y28 & y30 & Hms2 & HTM). subst ms2.
  destruct Heq as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
  cbn [with_rom MS ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in E1, E2, E3, E4, E5, E6, E7, E8.
  set (vs := [y5; y7; y10; y11; y13; y14; y15; y16; y28; y30]).
  set (E' := E_of TM_KEYS vs (s_next L) E).
  assert (Hy10 : E' (fv (s_next L) 2) = y10) by (exact (E_of_nth TM_KEYS vs (s_next L) E 2 y10 eq_refl eq_refl)).
  assert (Hy15 : E' (fv (s_next L) 6) = y15) by (exact (E_of_nth TM_KEYS vs (s_next L) E 6 y15 eq_refl eq_refl)).
  assert (COMMON : forall pc1 newf newx, pc1 = 0x9b51c -> Forall (fact_ok E') (newf L) -> Forall (xfact_ok xok_spd E' m0) (newx L) ->
     isteps ASEGS ms ms1 /\ length vs = length TM_KEYS /\
      ms_mem ms1 = ms_mem ms /\ ms_fcsr ms1 = ms_fcsr ms /\ ms_resv ms1 = ms_resv ms /\ ms_svc_pending ms1 = None /\
      ms_pc_val ms1 = Z_to_bv 64 pc1 /\
      (forall r, ~ In (bv_unsigned r) TM_KEYS -> getr (ms_regs ms1) r = getr (ms_regs ms) r) /\
      (forall i k v, nth_error TM_KEYS i = Some k -> nth_error vs i = Some v -> getr (ms_regs ms1) (Z_to_bv 5 k) = v) /\
      Forall (fact_ok E') (newf L) /\ Forall (xfact_ok xok_spd E' m0) (newx L)).
  { intros pc1 newf newx -> HnF HnX.
    split; [exact Hst|]. split; [reflexivity|]. split; [exact E7|]. split; [exact E6|]. split; [rewrite E5, Hresv0; reflexivity|].
    split; [exact E4|]. split; [exact E3|].
    split; [|split; [|split; [exact HnF | exact HnX]]].
    - intros r Hr. rewrite (E1 r). destruct (reg_of_nat r) as (n & -> & Hn). rewrite getr_mkR. rewrite u5 by lia. rewrite Nat2Z.id.
      unfold TM_KEYS in Hr. cbn [In] in Hr. rewrite u5 in Hr by lia.
      do 32 (destruct n as [|n]; [cbn; first [reflexivity | (symmetry; exact RA1) | (symmetry; exact R12) | (symmetry; exact R22)
                                              | (rewrite Hlen; symmetry; exact R23) | (symmetry; exact R23) | (symmetry; exact R19) | (symmetry; exact R24)
                                              | (exfalso; apply Hr; repeat (first [left; reflexivity | right]))]|]).
      lia.
    - intros i k v Hi Hv. rewrite (E1 _).
      destruct i as [|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]; cbn in Hi, Hv;
        first [ (injection Hi as <-; injection Hv as <-; reflexivity) | (destruct i; discriminate) ]. }
  destruct HTM as [H0|[H1 [H15 H15b]]].
  - exists 0x9b51c, tm_newf0, nox, ms1, vs. split; [left; reflexivity|].
    apply COMMON; [reflexivity | | constructor].
    unfold tm_newf0. constructor; [|constructor]. cbn [fact_ok]. rewrite lden_lvar, Hy10. lia.
  - exists 0x9b51c, tm_newf1, nox, ms1, vs. split; [right; left; reflexivity|].
    apply COMMON; [reflexivity | | constructor].
    unfold tm_newf1. constructor; [|constructor; [|constructor]]; cbn [fact_ok]; rewrite lden_lvar.
    + rewrite Hy10. lia.
    + rewrite Hy15. pose proof (bv_unsigned_in_range _ y15) as X. unfold bv_modulus in X. change (2 ^ Z.of_N 64) with (2 ^ 64) in X. lia.
Qed.

Theorem H_TM_F_ok : hand_okx ASEGS xok_spd H_TM_F.
Proof. apply hx_okm. exact tm_kit_f. Qed.
