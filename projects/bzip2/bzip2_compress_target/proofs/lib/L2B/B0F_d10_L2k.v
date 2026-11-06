(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import ShapeAlg.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import ImageA RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Layout RT_iface D_defs D_kit I_read RT_liveprim RT_globals R_unwind_chain. Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.Layout.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_iface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_kit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_read.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_liveprim.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_globals.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_unwind_chain.TwinB__.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require L_libA D_libiface.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.L2B Require Import L2Kit L2Act L2Stmt L2StmtD B0_fs_L2f B0_sessK B0_b2bc_K B0F_decK.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0 SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel BzTac BzTables CmpMem AsanKit AsanKit2 AsanCut.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDefs BzInv BzContracts.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzDState DecCutB DecCutFB B0F_decV B0F_g10A B0F_g10C S0_cmp_bs.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutFB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decV OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_g10A OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_g10C.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
#[local] Notation mem := (word -> option byte).

Section D10K.
Context {ACEIL__ : ACeil}.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.

(* [comment removed for export] *)
Lemma act_geom_ext : forall lo P usp sp0 hasf k FB SHF FSZ SSZ fr live0 Wc (Σ : rts RT) (m : mem) l1 Wc',
  act_geom RT lo P usp sp0 hasf k FB SHF FSZ SSZ fr live0 Wc ->
  sig_ok RT sp0 hasf k FB fr live0 Σ -> ART RT Σ m -> rt_live RT Σ = l1 ++ live0 ->
  (forall x, ~ outside Wc' x -> aclient (l1 ++ live0) fr usp x) ->
  act_geom RT lo P usp sp0 hasf k FB SHF FSZ SSZ fr (l1 ++ live0) Wc' /\ sig_ok RT sp0 hasf k FB fr (l1 ++ live0) Σ.
Proof.
  intros lo P usp sp0 hasf k FB SHF FSZ SSZ fr live0 Wc Σ m l1 Wc' G SK ART0 LV WCL'.
  pose proof G as [FSZE SSZE SSB AX LOW LOR PUS SPT SPA GFR GSH SP0R CAP WCL].
  split.
  - refine (mkAG RT lo P usp sp0 hasf k FB SHF FSZ SSZ fr (l1 ++ live0) Wc' FSZE SSZE SSB AX LOW LOR PUS SPT SPA GFR GSH SP0R _ WCL').
    intros x [C|[C|[C|[C|C]]]].
    + apply (CAP x). left; exact C.
    + apply (CAP x). right; left; exact C.
    + destruct C as (p & n & IN & R). apply in_app_or in IN. destruct IN as [IN|IN]; [| apply (CAP x); right; right; left; exists p, n; split; assumption].
      assert (INL : In (p, n) (rt_live RT Σ)) by (rewrite LV; apply in_or_app; left; exact IN).
      pose proof (af_live_range RT AF Σ m _ _ ART0 INL) as (_ & L1 & _). rewrite (proj1 (proj2 SK)) in L1. unfold RT_STACK in LOR.
      destruct (hasf_cases RT _ _ _ _ _ _ _ _ _ _ _ _ _ G) as [(HT & FE)|(HF & F0 & S0)].
      * pose proof (sig_INF RT _ _ _ _ _ _ Σ HT SK) as FIN.
        pose proof (af_frames_range RT AF Σ m _ _ ART0 FIN) as (_ & _ & _ & FL). pose proof (af_fshadow_apart RT AF Σ m _ _ ART0 FIN) as (SL & _).
        pose proof (FL _ _ INL) as D1. pose proof (SL _ _ INL) as D2. rewrite FE in D1, D2. rewrite (SHFB G), (SHFE G) in D2.
        clear - R L1 LOW LOR D1 D2. lia.
      * clear - R L1 LOW LOR F0 S0. lia.
    + apply (CAP x). right; right; right; left; exact C.
    + apply (CAP x). right; right; right; right; exact C.
  - destruct SK as (F1 & S1 & _). split; [exact F1|]. split; [exact S1|]. intros e He. rewrite LV. exact He.
Qed.

(* [comment removed for export] *)
Lemma presi_compose : forall usp fr live0 Wc l1 Wc' (mi mk m' : mem),
  PRESI usp fr live0 Wc mi mk -> PRESI usp fr (l1 ++ live0) Wc' mk m' ->
  (forall x, aclient live0 fr usp x -> outside Wc x -> outside Wc' x) ->
  PRESI usp fr live0 Wc mi m'.
Proof.
  intros usp fr live0 Wc l1 Wc' mi mk m' P1 P2 H a [CA OUT].
  rewrite (P2 a); [exact (P1 a (conj CA OUT))|]. split; [| exact (H _ CA OUT)].
  apply (aclient_mono live0 fr usp (l1 ++ live0) fr usp _ CA); [intros e He; apply in_or_app; right; exact He| intros e He; exact He| apply Z.le_refl].
Qed.

(* [comment removed for export] *)
Lemma d10_new_apart : forall (Σ' : rts RT) (m' : mem) p n old, ART RT Σ' m' -> rt_live RT Σ' = (p, n) :: old ->
  (forall p2 n2, In (p2, n2) old -> disj p2 n2 p n) /\ (forall f k, In (f, k) (rt_frames RT Σ') -> f + fs_size k <= p \/ p + n <= f).
Proof.
  intros Σ' m' p n old ART' LV'. split.
  - intros p2 n2 IN. pose proof (af_live_disj RT AF Σ' m' p n p2 n2 [] old ART' LV' IN) as D. unfold disj. clear - D. lia.
  - intros f k FIN. pose proof (af_frames_range RT AF Σ' m' _ _ ART' FIN) as (_ & _ & _ & FL). apply (FL p n). rewrite LV'. left. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma d10_blkF : forall (m : mem) cx J, b_small cx = 0 -> 0 <= b_n cx ->
  rw_cells b0segs m (b_tt cx) [CB (Z.to_nat (4 * (100000 * b_n cx))) J] ->
  blk_at b0segs m cx (BlkF (zw32 (S0_cmp_bs.zarr_of_junkw J (100000 * b_n cx)) (100000 * b_n cx))).
Proof.
  intros m cx J E N0 H. cbn [blk_at]. split; [exact E|]. split; [exact (S0_cmp_bs.zw32_of_junk b0segs m _ _ J H ltac:(lia))|].
  rewrite zw32_length by lia. reflexivity.
Qed.
Lemma d10_blkS : forall (m : mem) cx J16 J4, b_small cx = 1 -> 0 <= b_n cx ->
  rw_cells b0segs m (b_ll16 cx) [CB (Z.to_nat (200000 * b_n cx)) J16] -> rw_cells b0segs m (b_ll4 cx) [CB (Z.to_nat (50000 * b_n cx)) J4] ->
  blk_at b0segs m cx (BlkS J16 J4).
Proof.
  intros m cx J16 J4 E N0 H16 H4. cbn [blk_at]. split; [exact E|].
  pose proof (proj2 (B0F_g10A.rw_cells_CB_C1s b0segs m _ _ _ H16)) as L16. pose proof (proj2 (B0F_g10A.rw_cells_CB_C1s b0segs m _ _ _ H4)) as L4.
  split; [exact (u8arr_of_rw_cells b0segs m _ _ J16 H16)|]. split; [rewrite L16; lia|].
  split; [exact (u8arr_of_rw_cells b0segs m _ _ J4 H4)|]. rewrite L4; lia.
Qed.

(* [comment removed for export] *)
Lemma d10_unwind : forall (m : mem) (A : act14) site,
  aframe A m -> In [site; bv_unsigned (a_ra A)] SITE_TRACES -> 0 <= site < 2^64 ->
  a_usp A mod 8 = 0 -> a_usp A <= USTACK_TOP -> 0 <= a_P A ->
  fp_stop (a_usp A) (bv_unsigned (a_s0 A)) ->
  unwind_ch m (Z_to_bv 64 site) (a_sp A) (Z_to_bv 64 (a_P A)).
Proof.
  intros m A site (zt & ng & jg & j24 & pos & j38 & fl & GEO & NG & FLP & FRM & FRT & FF & FS) INS SR U8 UT P0 STOP.
  pose proof (bv_unsigned_in_range 64 (a_sp A)) as SPR. unfold bv_modulus in SPR. cbn in SPR. fold (a_usp A) in SPR.
  exists [bv_unsigned (a_ra A)]. rewrite unsigned_lit by exact SR. split; [exact INS|].
  rewrite unsigned_lit by (clear - P0 GEO SPR; lia). fold (a_usp A).
  cbn [uw_chain]. split; [clear - GEO; lia|]. split; [exact U8|]. split; [exact UT|].
  exists (bv_unsigned (a_s0 A)). split; [pose proof (bv_unsigned_in_range 64 (a_s0 A)) as R; unfold bv_modulus in R; cbn in R; exact R|].
  split; [| exact STOP].
  destruct (B0F_g10A.rw_cells_cutZ b0segs m _ _ 12%nat FRT) as [_ REC]. unfold FT_REGS in REC. cbn [firstn skipn cells_size csize Nat.add] in REC.
  replace (a_P A + 760 + Z.of_nat (ng + 88)) with (a_usp A + -16) in REC by (clear - GEO; lia).
  rewrite !Z_to_bv_bv_unsigned. exact (n2k_C8C8 m _ _ _ REC).
Qed.

(* [comment removed for export] *)
Lemma d10_readers : forall (Σ : rts RT) (m : mem) (A : act14) zp zn,
  let cx := a_cx A in
  ART RT Σ m -> In (b_s cx, 64144) (rt_live RT Σ) -> In (zp, zn) (rt_live RT Σ) -> zp <= b_src cx -> b_src cx + b_len cx <= zp + zn ->
  b_s cx mod 8 = 0 -> sanchor (b_strm cx) (a_sht A) -> sanchor (a_fb A) (a_shf A) -> 0 < b_strm cx -> b_strm cx + 80 <= 2^47 ->
  bytes_at b0segs m (a_sht A) (repeat z8 10) ->
  (b_strm cx + 80 <= 0x7fff7000 \/ 0x10007fff8000 <= b_strm cx) -> (a_fb A + 64 <= 0x7fff7000 \/ 0x10007fff8000 <= a_fb A) -> 0x10007fff8000 <= a_P A ->
  (a_fb A + 64 <= b_s cx \/ b_s cx + 64144 <= a_fb A) -> (a_fb A + 64 <= b_strm cx \/ b_strm cx + 80 <= a_fb A) -> (a_fb A + 64 <= zp \/ zp + zn <= a_fb A) ->
  shzW b0segs (W10 A) m (b_s cx) (b_s cx + 64144) /\ shzW b0segs (W10 A) m (b_strm cx) (b_strm cx + 80) /\ shpW b0segs (W10 A) m (b_src cx) (b_src cx + b_len cx).
Proof.
  intros Σ m A zp zn cx ART0 SLIV ZLIV ZLO ZHI S8 ANT ANF T0 T1 ZSH OFFT OFFF OFFP DFS DFT DFZ. subst cx.
  pose proof (af_live_range RT AF Σ m _ _ ART0 SLIV) as (SL0 & SL1 & _). pose proof (af_live_offshadow RT AF Σ m _ _ ART0 SLIV) as SOFF.
  pose proof (af_live_range RT AF Σ m _ _ ART0 ZLIV) as (ZL0 & ZL1 & _).
  pose proof (af_sp0_range RT AF Σ m ART0) as (_ & SP0T). unfold USTACK_TOP, STACK_WIN in *.
  destruct (af_acc_live RT AF Σ m _ _ ART0 SLIV) as [_ ACCS]. destruct (af_acc_live RT AF Σ m _ _ ART0 ZLIV) as [_ ACCZ].
  pose proof (strm_acc m (b_strm (a_cx A)) (a_sht A) ANT ltac:(clear - T0; lia) ZSH) as ACCT.
  assert (DJ : forall x, 0 <= x < 2^47 -> (x < a_fb A \/ a_fb A + 64 <= x) -> disjoint_from (W10 A) (x / 8 + 2147450880) 1).
  { intros x X XF. unfold W10. cbn [disjoint_from].
    split; [apply shd_app; [exact X| clear - SOFF; unfold SH_LO, SH_HI; lia]|].
    split; [apply shd_app; [exact X| clear - SOFF; unfold SH_LO, SH_HI; lia]|].
    split; [apply shd_app; [exact X| clear - OFFT; unfold SH_LO, SH_HI; lia]|].
    split; [apply shd_app; [exact X| right; clear - OFFP; unfold SH_HI; lia]|].
    split; [apply shd_app; [exact X| clear - OFFF; unfold SH_LO, SH_HI; lia]|].
    split; [| exact I].
    pose proof (shd_anchor (a_fb A) (a_shf A) 0 8 x ANF ltac:(clear - XF; lia)) as H. rewrite Z.add_0_r in H. exact H. }
  split; [| split].
  - apply (shzW_of_acc_gen b0segs _ m (b_s (a_cx A)) 64144 _ _ ACCS); [clear - SL0; lia| clear; lia| clear - S8; Z.div_mod_to_equations; lia|].
    intros x Hx. apply DJ; [clear - Hx SL0 SL1 SP0T; lia| clear - Hx DFS; lia].
  - apply (shzW_of_acc_gen b0segs _ m (b_strm (a_cx A)) 80 _ _ ACCT); [clear - T0; lia| clear; lia| destruct ANT as [T8 _]; clear - T8; Z.div_mod_to_equations; lia|].
    intros x Hx. apply DJ; [clear - Hx T0 T1; lia| clear - Hx DFT; lia].
  - pose proof (L2Kit.acc_sub bsegs m zp zn (b_src (a_cx A)) (b_len (a_cx A)) ACCZ ZLO ZHI) as ACCP.
    apply (shpW_of_acc_gen b0segs _ m _ _ ACCP). intros x Hx. apply DJ; [clear - Hx ZLO ZHI ZL0 ZL1 SP0T; lia| clear - Hx DFZ ZLO ZHI; lia].
Qed.

(* [comment removed for export] *)
Section DecAct2.
Variables (lo P usp sp0 FB SHF : Z) (fr : list (Z * nat)) (live0 Wc : list (Z * Z)).
Hypothesis G : act_geom RT lo P usp sp0 true 0 FB SHF 64 8 fr live0 Wc.
Variable A : act14.
Hypothesis AP : a_P A = P.
Hypothesis AFB : a_fb A = FB.
Hypothesis ASHF : a_shf A = SHF.
Hypothesis AUSP : a_usp A = usp.

Lemma dec_aframe_xfer2 : forall Σ Σ' W (m m' mi : mem),
  sig_ok RT sp0 true 0 FB fr live0 Σ -> sig_ok RT sp0 true 0 FB fr live0 Σ' -> ART RT Σ' m' ->
  rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) P W m m' ->
  disjoint_from W P (usp - P) -> disjoint_from W FB 64 -> disjoint_from W SHF 8 ->
  aframe A m -> aframe A m'.
Proof.
  intros Σ Σ' W m m' mi SOK SOK' ART' STEP DP DF DS (zt & ng & jg & j24 & pos & j38 & fl & GEO & NG & FLP & FRM & FRT & FF & FS).
  destruct (release_inline2 AF G (mi := mi) Σ' m' eq_refl SOK' ART') as (_ & fl' & _ & FLP' & _).
  rewrite AP, AUSP in GEO. rewrite AP in FRM, FRT. rewrite AFB in FF. rewrite ASHF in FS.
  exists zt, ng, jg, j24, pos, j38, fl'. rewrite AP, AUSP, AFB, ASHF.
  split; [exact GEO|]. split; [exact NG|].
  split; [replace (FB + 56) with (FB + 64 - 8) by (clear; lia); exact (ro_C8_KN m' _ _ FLP')|].
  split. { apply (x_rw_cells RT P Σ W m m' STEP _ _ FRM).
           - apply (cls_rframe G Σ); [clear; lia| unfold FM_CELLS; cbn [cells_size csize Nat.add length]; clear - GEO; lia].
           - apply (dk_dj_sub W P (usp - P)); [exact DP| clear; lia| unfold FM_CELLS; cbn [cells_size csize Nat.add length]; clear - GEO; lia]. }
  split. { apply (x_rw_cells RT P Σ W m m' STEP _ _ FRT).
           - apply (cls_rframe G Σ); [clear; lia| unfold FT_REGS; cbn [cells_size csize Nat.add]; clear - GEO NG; lia].
           - apply (dk_dj_sub W P (usp - P)); [exact DP| clear; lia| unfold FT_REGS; cbn [cells_size csize Nat.add]; clear - GEO NG; lia]. }
  split.
  - apply (x_rw_cells RT P Σ W m m' STEP _ _ FF); cbn [cells_size csize Nat.add].
    + apply (cls_frame G Σ _ _ SOK); clear; lia.
    + apply (dk_dj_sub W FB 64); [exact DF| clear; lia| clear; lia].
  - apply (x_rw_cells RT P Σ W m m' STEP _ _ FS); cbn [cells_size csize Nat.add].
    + apply (cls_shadow G Σ _ _ SOK); clear; lia.
    + exact DS.
Qed.
End DecAct2.

End D10K.
