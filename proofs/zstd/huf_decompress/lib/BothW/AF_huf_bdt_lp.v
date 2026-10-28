(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_FseDecompRT.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_tbl_iface RF_huf_bdt_model.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase RtCells AF_huf_tbl_iface AF_huf_bdt_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkArith StrFun.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_hint ::= bdtA_acc_hint.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.
Section LPA.
  Variables (ra gp tp : word) (F : bvmap 5 word) (fc : bv 32) (RNG : footprint).
  Variables (x6 x8 x9 x12 x14 x26 x27 x29 x31 : word).       (* [comment removed for export] *)
  Variables (m : amem) (NC WK TD : Z) (nc : list Z) (tl M1 : Z) (jt jw : list byte).
  Variable POST : machine_state -> Prop.
  Hypothesis HTL : 1 <= tl <= 12.
  Hypothesis HM1 : 1 <= M1 <= 256.
  Hypothesis HNCL : M1 <= zlen nc.
  Hypothesis HNCR : Forall (fun c => - 32768 <= c < 32768) nc.
  Hypothesis HJT : length jt = (4 * Z.to_nat (2^tl))%nat.
  Hypothesis HJW : (2 * Z.to_nat M1 <= length jw)%nat.
  Hypothesis BNC : ablk NC (NC + 2 * zlen nc).
  Hypothesis BTD : ablk TD (TD + 4 * 2^tl).
  Hypothesis BWK : ablk WK (WK + zlen jw).
  Hypothesis DNT : NC + 2 * zlen nc <= TD \/ TD + 4 * 2^tl <= NC.
  Hypothesis DNW : NC + 2 * zlen nc <= WK \/ WK + zlen jw <= NC.
  Hypothesis DTW : TD + 4 * 2^tl <= WK \/ WK + zlen jw <= TD.
  Hypothesis N2 : NC mod 2 = 0.
  Hypothesis W2 : WK mod 2 = 0.
  Hypothesis T4 : TD mod 4 = 0.
  Hypothesis ZN : zshadow m NC (2 * zlen nc).
  Hypothesis ZT : zshadow m TD (4 * 2^tl).
  Hypothesis ZW : zshadow m WK (zlen jw).
  Hypothesis RN : rng RNG NC (2 * zlen nc).
  Hypothesis RNS : rng RNG (shad NC) (nshad (2 * zlen nc + NC mod 8)).
  Hypothesis RT : rng RNG TD (4 * 2^tl).
  Hypothesis RTS : rng RNG (shad TD) (nshad (4 * 2^tl + TD mod 8)).
  Hypothesis RW : rng RNG WK (zlen jw).
  Hypothesis RWS : rng RNG (shad WK) (nshad (zlen jw + WK mod 8)).
  Variable SP : Z.
  Hypothesis FRW : rw_cells bsegs m (SP + 64) [C8 (Z_to_bv 64 (- WK - 1))].
  Hypothesis FRN : rw_cells bsegs m (SP + 72) [C8 (Z_to_bv 64 NC)].
  Hypothesis FWK : rw_cells bsegs m (SP + 80) [C8 (Z_to_bv 64 WK)].
  Hypothesis RSP : rng RNG (SP + 64) 24.
  Hypothesis DSPT : TD + 4 * 2^tl <= SP + 64 \/ SP + 88 <= TD.
  Hypothesis DSPW : WK + zlen jw <= SP + 64 \/ SP + 88 <= WK.

  Definition lpA_W : list (Z * Z) := [(TD, TD + 4 * 2^tl); (WK, WK + zlen jw)].

  Definition lpA_inv (m1 : amem) (syms : list (option Z)) (snext : list Z) : Prop :=
    u8arr bsegs m1 TD (tsym jt syms)
    /\ u8arr bsegs m1 WK (wkb jw snext) /\ (2 * length snext <= length jw)%nat
    /\ bytes_at bsegs m1 NC (u16s (map (Z_to_bv 64) nc))
    /\ munch lpA_W m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1.

  Definition lpA_ok (syms : list (option Z)) (snext : list Z) (hT fm : Z) : Prop :=
    length syms = Z.to_nat (2^tl) /\ Forall (fun v => 0 <= v < 65536) snext
    /\ 0 <= hT < 2^32 /\ (hT < 2^tl \/ hT = 2^32 - 1) /\ (fm = 0 \/ fm = 1).

  Notation STA pc mm s hT fm x5 x10 x13 x15 x30 :=
    (MS (mkR ra (Z_to_bv 64 SP) gp tp x5 x6 (Z_to_bv 64 ASHOFF) x8 x9 x10 (Z_to_bv 64 (- NC - 1)) x12 x13 x14 x15
             (Z_to_bv 64 (bv_swrap 32 hT)) (Z_to_bv 64 TD) (Z_to_bv 64 s) (Z_to_bv 64 M1) (Z_to_bv 64 1) (Z_to_bv 64 fm)
             (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (2^(tl-1))) (Z_to_bv 64 65535) x26 x27
             (Z_to_bv 64 (- TD - 1)) x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  Local Ltac acc_hint ::= wk_acc_hint.
  Lemma lp_mem : forall m1 syms snext, lpA_inv m1 syms snext ->
    zshadow m1 NC (2 * zlen nc) /\ zshadow m1 WK (zlen jw) /\ zshadow m1 TD (4 * 2^tl) /\
    rw_cells bsegs m1 (SP + 64) [C8 (Z_to_bv 64 (- WK - 1))] /\ rw_cells bsegs m1 (SP + 72) [C8 (Z_to_bv 64 NC)] /\
    rw_cells bsegs m1 (SP + 80) [C8 (Z_to_bv 64 WK)].
  Proof.
    intros m1 syms snext (UT & UW & LW & NCB & MU & WM & MI).
    pose proof (ablk_lin _ _ BTD) as (Ta & Tb & Tc & Td). pose proof (ablk_lin _ _ BWK) as (Wa & Wb & Wc & Wd).
    pose proof (ablk_lin _ _ BNC) as (Na & Nb & Nc & Nd).
    split; [|split; [|split; [|split; [|split]]]].
    - exact (zshadow_munch _ m m1 NC (2 * zlen nc) ZN MU
        (shad_outside2 NC (2 * zlen nc) TD (4 * 2^tl) WK (zlen jw) BTD BWK ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)).
    - exact (zshadow_munch _ m m1 WK (zlen jw) ZW MU
        (shad_outside2 WK (zlen jw) TD (4 * 2^tl) WK (zlen jw) BTD BWK ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)).
    - exact (zshadow_munch _ m m1 TD (4 * 2^tl) ZT MU
        (shad_outside2 TD (4 * 2^tl) TD (4 * 2^tl) WK (zlen jw) BTD BWK ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)).
    - apply (rw_cells_transport bsegs _ m m1 (SP + 64) _ FRW MU WM); unfold lpA_W; cbn [disjoint_from]; cbn; lia.
    - apply (rw_cells_transport bsegs _ m m1 (SP + 72) _ FRN MU WM); unfold lpA_W; cbn [disjoint_from]; cbn; lia.
    - apply (rw_cells_transport bsegs _ m m1 (SP + 80) _ FWK MU WM); unfold lpA_W; cbn [disjoint_from]; cbn; lia.
  Qed.

  Lemma lp_st1 : forall m1 syms snext p v, lpA_inv m1 syms snext -> 0 <= p < 2^tl -> 0 <= v < 256 ->
    length syms = Z.to_nat (2^tl) ->
    store_ok bsegs m1 (wa (TD + (4 * p + 2))) 1 = true /\
    lpA_inv (write_to_mem m1 (wa (TD + (4 * p + 2))) (le1 (Z_to_bv 64 v))) (oupd_nat (Z.to_nat p) v syms) snext.
  Proof.
    intros m1 syms snext p v (UT & UW & LW & NCB & MU & WM & MI) HP HV HL.
    pose proof (ablk_lin _ _ BTD) as (Ta & Tb & Tc & Td). pose proof (ablk_lin _ _ BWK) as (Wa & Wb & Wc & Wd).
    pose proof (ablk_lin _ _ BNC) as (Na & Nb & Nc & Nd).
    assert (LT : Z.of_nat (length (tsym jt syms)) = 4 * 2^tl) by (rewrite tsym_length, HJT; lia).
    assert (SOK : store_ok bsegs m1 (wa (TD + (4 * p + 2))) 1 = true)
      by (apply (u8arr_store_ok bsegs m1 TD (tsym jt syms) (4 * p + 2)); [exact UT | lia | reflexivity]).
    split; [exact SOK|].
    rewrite le1_byte, (unsigned_lit v) by lia. rewrite (Z.mod_small v 256) by lia.
    unfold lpA_inv. split; [|split; [|split; [|split; [|split; [|split]]]]].
    - rewrite <- tsym_store by (rewrite ?HJT, ?HL; lia).
      replace (4 * Z.to_nat p + 2)%nat with (Z.to_nat (4 * p + 2)) by lia.
      apply u8arr_write; [exact UT | lia].
    - apply u8arr_frame; [exact UW | lia | cbn [length]; lia | rewrite (wkb_length jw snext LW); cbn [length]; lia].
    - exact LW.
    - apply (bytes_at_write_other_n bsegs m1 (TD + (4 * p + 2)) _ NC _ 1); [reflexivity | lia | lia | exact NCB |].
      rewrite u16s_length, length_map. lia.
    - apply munch_write; [exact MU | lia | cbn [length]; lia | unfold lpA_W; cbn [inside length]; lia].
    - apply wmono_write; exact WM.
    - apply mem_inv_store; [exact MI | exact SOK].
  Qed.

  Lemma lp_st2 : forall m1 syms snext v, lpA_inv m1 syms snext -> (2 * length snext + 2 <= length jw)%nat ->
    store_ok bsegs m1 (wa (WK + 2 * zlen snext)) 2 = true /\
    lpA_inv (write_to_mem m1 (wa (WK + 2 * zlen snext)) (le2 (Z_to_bv 64 v))) syms (snext ++ [v]).
  Proof.
    intros m1 syms snext v (UT & UW & LW & NCB & MU & WM & MI) HLW.
    pose proof (ablk_lin _ _ BTD) as (Ta & Tb & Tc & Td). pose proof (ablk_lin _ _ BWK) as (Wa & Wb & Wc & Wd).
    pose proof (ablk_lin _ _ BNC) as (Na & Nb & Nc & Nd).
    assert (LK : length (wkb jw snext) = length jw) by (apply wkb_length; exact LW).
    assert (L2 : length (le2 (Z_to_bv 64 v)) = 2%nat) by reflexivity.
    assert (SOK : store_ok bsegs m1 (wa (WK + 2 * zlen snext)) 2 = true)
      by (apply (u8arr_store_ok_n bsegs m1 WK (wkb jw snext) (2 * zlen snext) 2%nat); [exact UW | lia | rewrite LK; lia | reflexivity]).
    split; [exact SOK|].
    unfold lpA_inv. split; [|split; [|split; [|split; [|split; [|split]]]]].
    - apply u8arr_frame; [exact UT | lia | rewrite L2; lia | rewrite L2, tsym_length, HJT; lia].
    - rewrite <- wkb_snoc by exact HLW.
      replace (2 * length snext)%nat with (Z.to_nat (2 * zlen snext)) by lia.
      apply u8arr_write_bytes; [exact UW | lia | rewrite L2, LK; lia].
    - rewrite length_app. cbn [length]. lia.
    - apply (bytes_at_write_other_n bsegs m1 (WK + 2 * zlen snext) _ NC _ 2); [rewrite L2; reflexivity | lia | lia | exact NCB |].
      rewrite u16s_length, length_map. lia.
    - apply munch_write; [exact MU | lia | rewrite L2; lia | unfold lpA_W; cbn [inside]; rewrite L2; lia].
    - apply wmono_write; exact WM.
    - apply mem_inv_store; [exact MI | rewrite L2; exact SOK].
  Qed.

  Lemma lp_loopA : forall f s syms snext hT fm r m1 (x5 x10 x13 x15 x30 : word),
    lowprob_loop nc tl f s syms snext hT fm = Ok r ->
    Z.of_nat f = M1 - s -> 0 <= s < M1 -> zlen snext = s ->
    lpA_ok syms snext hT fm -> lpA_inv m1 syms snext ->
    (forall m2 syms' snext' hT' fm' (y5 y10 y13 y15 y30 : word),
       r = (syms', snext', hT', fm') -> zlen snext' = M1 -> lpA_ok syms' snext' hT' fm' -> lpA_inv m2 syms' snext' ->
       evtF bsegs RNG POST (STA 0x97b48 m2 M1 hT' fm' y5 y10 y13 y15 y30)) ->
    evtF bsegs RNG POST (STA 0x97a50 m1 s hT fm x5 x10 x13 x15 x30).
Proof.
intros f. induction f as [|f IH]; intros s syms snext hT fm r m1 q5 q10 q13 q15 q30 HR HF HS HSN OK INV K; [lia|].
pose proof INV as INV0. pose proof OK as OK0.
destruct INV as (UT & UW & LW & NCB & MU & WM & MI).
destruct OK as (SL & SR & HT0 & HT1 & FM).
pose proof (ablk_lin _ _ BTD) as (Ta & Tb & Tc & Td).
pose proof (ablk_lin _ _ BWK) as (Wa & Wb & Wc & Wd).
pose proof (ablk_lin _ _ BNC) as (Na & Nb & Nc & Nd).
unfold AIMG_HI in Ta, Wa, Na.
unfold ASHOFF.
zstep.
pose proof (zshadow_munch _ m m1 NC (2 * zlen nc) ZN MU (shad_outside2 NC (2 * zlen nc) TD (4 * 2^tl) WK (zlen jw) BTD BWK ltac:(lia) ltac:(lia))
  ltac:(lia) ltac:(lia)) as ZN1.
pose proof (zshadow_munch _ m m1 WK (zlen jw) ZW MU (shad_outside2 WK (zlen jw) TD (4 * 2^tl) WK (zlen jw) BTD BWK ltac:(lia) ltac:(lia))
  ltac:(lia) ltac:(lia)) as ZW1.
pose proof (zshadow_munch _ m m1 TD (4 * 2^tl) ZT MU (shad_outside2 TD (4 * 2^tl) TD (4 * 2^tl) WK (zlen jw) BTD BWK ltac:(lia) ltac:(lia))
  ltac:(lia) ltac:(lia)) as ZT1.
assert (FRW1 : rw_cells bsegs m1 (SP + 64) [C8 (Z_to_bv 64 (- WK - 1))])
  by (apply (rw_cells_transport bsegs _ m m1 (SP + 64) _ FRW MU WM); unfold lpA_W; cbn [disjoint_from]; cbn; lia).
assert (FRN1 : rw_cells bsegs m1 (SP + 72) [C8 (Z_to_bv 64 NC)])
  by (apply (rw_cells_transport bsegs _ m m1 (SP + 72) _ FRN MU WM); unfold lpA_W; cbn [disjoint_from]; cbn; lia).
assert (FWK1 : rw_cells bsegs m1 (SP + 80) [C8 (Z_to_bv 64 WK)])
  by (apply (rw_cells_transport bsegs _ m m1 (SP + 80) _ FWK MU WM); unfold lpA_W; cbn [disjoint_from]; cbn; lia).
(wk_go [0x97a74; 0x97a50; 0x97b48]).
assert (NL : 0 <= s < Z.of_nat (length nc)) by lia.
pose proof (u16_znth bsegs m1 NC nc s (Z_to_bv 64 (NC + Z.shiftl s 1)) NCB NL
  ltac:(unfold wa; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RDN.
pose proof (Forall_Znth _ nc s HNCR ltac:(lia)) as NR. cbv beta in NR.
zstep. clear RDN.
rewrite zx16_short by lia.
zstep.
assert (LD : load nc s = Ok (Znth s nc))
  by (unfold load; replace ((0 <=? s) && (s <? FseNCount.Zlength nc)) with true; [reflexivity|];
      symmetry; apply andb_true_iff; split; [apply Z.leb_le; lia | apply Z.ltb_lt; unfold FseNCount.Zlength; lia]).
cbn [lowprob_loop] in HR. rewrite LD in HR. cbn [bind] in HR.
destruct (Z.eq_dec (Znth s nc) (-1)) as [EQ|NE].
- rewrite (proj2 (Z.eqb_eq _ _) EQ) in HR.
  destruct (ostore syms hT s) as [syms1| | |] eqn:OS; cbn [bind] in HR; try discriminate HR.
  apply ostore_Ok in OS as (HTR & ->).
  assert (SW : bv_swrap 32 hT = hT).
  { assert (HM : bv_half_modulus 32 = 2^31) by reflexivity. assert (MM : bv_modulus 32 = 2^32) by reflexivity.
    assert (2^tl <= 2^12) by (apply Z.pow_le_mono_r; lia).
    unfold bv_swrap, bv_wrap. rewrite HM, MM. rewrite Z.mod_small by lia. lia. }
  rewrite SW.
  wk_if_true.
  (wk_go [0x97ab8; 0x97a50; 0x97b48]).
assert (2^tl <= 2^12) by (apply Z.pow_le_mono_r; lia).
rewrite (shl32_shr30 hT) by lia.
(wk_go [0x97adc; 0x97a50; 0x97b48]).
assert (ODD : Z.land (TD + 4 * hT) 1 = 0).
{ change 1 with (Z.ones 1). rewrite Z.land_ones by lia. change (2^1) with 2.
  pose proof (Z.div_mod TD 4 ltac:(lia)) as TDM. rewrite T4, Z.add_0_r in TDM.
  replace (TD + 4 * hT) with ((2 * (TD / 4) + 2 * hT) * 2) by lia. apply Z.mod_mul. lia. }
rewrite ODD.
(wk_go [0x97adc; 0x97a50; 0x97b48]).
destruct (lp_st1 m1 syms snext hT s INV0 ltac:(lia) ltac:(lia) SL) as (SOK & INV2).
replace (wa (TD + (4 * hT + 2))) with (Z_to_bv 64 (TD + 4 * hT + 2)) in SOK, INV2 by (unfold wa; f_equal; lia).
zstep. clear SOK.
clear ZN1 ZW1 ZT1 FRW1 FRN1 FWK1.
destruct (lp_mem _ _ _ INV2) as (ZN2 & ZW2 & ZT2 & FRW2 & FRN2 & FWK2).
pose proof INV2 as INV3. destruct INV3 as (UT2 & UW2 & LW2 & NCB2 & MU2 & WM2 & MI2).
assert (LJW : (2 * length snext + 2 <= length jw)%nat) by lia.
(wk_go [0x97b08; 0x97a50; 0x97b48]).
destruct (lp_st2 _ _ _ 1 INV2 LJW) as (SOK2 & INV4).
replace (wa (WK + 2 * zlen snext)) with (Z_to_bv 64 (WK + Z.shiftl s 1)) in SOK2, INV4
  by (unfold wa; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
zstep. clear SOK2.
zstep.
assert (OK1 : lpA_ok (oupd_nat (Z.to_nat hT) s syms) (snext ++ [1]) (u32 (hT - 1)) fm).
{ unfold lpA_ok, u32. split; [rewrite oupd_nat_length; exact SL|].
  split; [apply Forall_app; split; [exact SR | constructor; [cbv beta; lia | constructor]]|].
  split; [apply Z.mod_pos_bound; lia|]. split; [|exact FM].
  destruct (Z.eq_dec hT 0) as [H0|H0]; [right; rewrite H0; reflexivity | left; rewrite Z.mod_small by lia; lia]. }
assert (SN1 : zlen (snext ++ [1]) = s + 1) by (rewrite length_app; cbn [length]; lia).
replace (hT + -1) with (hT - 1) by lia.
rewrite <- (swrap32_u32 (hT - 1)).
destruct (Z.eq_dec (s + 1) M1) as [EQ1|NE1].
+ destruct f as [|f]; [|lia]. cbn [lowprob_loop] in HR. injection HR as <-.
  (wk_go [0x97a50; 0x97b48]).
  rewrite EQ1 in SN1 |- *.
  exact (K _ _ _ _ _ _ _ _ _ _ eq_refl SN1 OK1 INV4).
+ destruct f as [|f]; [lia|].
  zstep. wk_if_true.
  exact (IH (s + 1) _ _ _ _ r _ _ _ _ _ _ HR ltac:(lia) ltac:(lia) SN1 OK1 INV4 K).
-
  rewrite (proj2 (Z.eqb_neq _ _) NE) in HR.
  wk_if_false.
  (wk_go [0x97a44; 0x97a50; 0x97b48]).
  assert (P1 : 1 <= 2^(tl-1) <= 2^11) by (split; [apply (Z.pow_le_mono_r 2 0 (tl - 1)); lia | apply Z.pow_le_mono_r; lia]).
  rewrite (srai48_short (Znth s nc)) by lia.
  rewrite (Z.mod_small (2^(tl-1)) 18446744073709551616) by lia.
  rewrite (slt_lit_mr (Znth s nc) (2^(tl-1))) by lia.
  rewrite (land_neg_b2z _ fm FM).
  set (fm1 := if Znth s nc <? 2^(tl-1) then fm else 0).
  assert (FM1 : (if to_short (2^(tl-1)) <=? Znth s nc then 0 else fm) = fm1).
  { unfold fm1, to_short. rewrite (Z.mod_small (2^(tl-1) + 2^15)) by lia. replace (2^(tl-1) + 2^15 - 2^15) with (2^(tl-1)) by lia.
    destruct (Z.ltb_spec (Znth s nc) (2^(tl-1))); [rewrite (proj2 (Z.leb_gt _ _)) by lia | rewrite (proj2 (Z.leb_le _ _)) by lia]; reflexivity. }
  rewrite FM1 in HR.
  assert (LJW : (2 * length snext + 2 <= length jw)%nat) by lia.
  destruct (lp_st2 _ _ _ (u16 (Znth s nc)) INV0 LJW) as (SOK2 & INV4).
  replace (wa (WK + 2 * zlen snext)) with (Z_to_bv 64 (WK + Z.shiftl s 1)) in SOK2, INV4
    by (unfold wa; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
  unfold u16 in INV4. change (2^16) with 65536 in INV4.
  zstep. clear SOK2.
  assert (OK1 : lpA_ok syms (snext ++ [Znth s nc mod 65536]) hT fm1).
  { unfold lpA_ok. split; [exact SL|].
    split; [apply Forall_app; split; [exact SR | constructor; [cbv beta; apply Z.mod_pos_bound; lia | constructor]]|].
    split; [lia|]. split; [exact HT1|]. unfold fm1. destruct (Znth s nc <? 2^(tl-1)); [exact FM | left; reflexivity]. }
  assert (SN1 : zlen (snext ++ [Znth s nc mod 65536]) = s + 1) by (rewrite length_app; cbn [length]; lia).
  unfold u16 in HR. change (2^16) with 65536 in HR.
  zstep. zstep.
  destruct (Z.eq_dec (s + 1) M1) as [EQ1|NE1].
  + destruct f as [|f]; [|lia]. cbn [lowprob_loop] in HR. injection HR as <-.
    wk_if_true.
    rewrite EQ1 in SN1 |- *.
    exact (K _ _ _ _ _ _ _ _ _ _ eq_refl SN1 OK1 INV4).
  + destruct f as [|f]; [lia|].
    wk_if_false.
    exact (IH (s + 1) _ _ _ _ r _ _ _ _ _ _ HR ltac:(lia) ltac:(lia) SN1 OK1 INV4 K).
Qed.
End LPA.
End CANSEC1.

