(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import ShapeAlg.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import ImageA RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Layout RT_iface D_defs D_kit I_read RT_liveprim RT_globals.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require L_libA D_libiface.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.L2 Require Import L2Kit L2Act L2Stmt L2StmtD A0_fs_L2f A0_sessK A0F_decK A0F_decX.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel BzTac BzTables CmpMem AsanKit AsanKit2 AsanCut.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDefs BzInv BzContracts.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState BzDBlock BzDOut BzDOK BzDOKp BzDFrame DecCutFA A0F_decV S0_bzd_loop1 S0F_bzd_loop1 S0F_bzd_loop3s A0F_bzdV A0F_bzd_skV A0F_bzd_skT.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOKp OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDFrame OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutFA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decV OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_bzd_loop1 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_bzdV OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_bzd_skV.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
#[local] Notation mem := (word -> option byte).

(* [comment removed for export] *)
Definition bz_setm0 (z : bzdctx) (m : mem) (F : bvmap 5 word) (fc : bv 32) : bzdctx :=
  BZC (z_cx z) (z_ra z) (z_sp z) (z_gp z) (z_tp z) (z_s0 z) (z_s1 z) (z_s2 z) (z_s3 z) (z_s4 z) (z_s5 z) (z_s6 z) (z_s7 z) (z_s8 z) (z_s9 z) (z_s10 z) (z_s11 z)
      F fc (z_g1 z) (z_sv z) (z_payload z) (z_lo z) m (z_fj z) (z_spi z).

Section BZDL2.
Context {ACEIL__ : ACeil}.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
Hypothesis DEC14 : decompress14_contract RT.
Variable z : bzdctx.                                   (* [comment removed for export] *)
Variable SHS : Z. Variable w0 : word.
Variables (sp0 : Z) (fr : list (Z * nat)) (live0 Wc : list (Z * Z)).
Notation usp := (bv_unsigned (z_sp z)). Notation uspi := (bv_unsigned (z_spi z)).
Hypothesis G : act_geom RT (z_lo z) uspi usp sp0 false 0 8 2147450881 0 0 fr live0 Wc.
Variable mi : mem.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc. Hypothesis MST : mat_stable PMc.
Variable T : TSet.
Notation PRESI := (PRESI usp fr live0 Wc mi).
Notation SOK Σ := (sig_ok RT sp0 false 0 8 fr live0 Σ).
Notation cx := (z_cx z).
Notation S := (b_s (z_cx z)). Notation STRM := (b_strm (z_cx z)). Notation DST := (b_dst (z_cx z)). Notation dlen := (b_dlen (z_cx z)).
Notation ZZ m F fc := (bz_setm0 z m F fc).

Hypothesis ZOK : bzdctx_okA z SHS.
Hypothesis ZTP : z_tp z = Z_to_bv 64 0x5fc0d8.
Hypothesis ZG1 : z_g1 z = A0F_decK.DG1. Hypothesis ZSV : z_sv z = A0F_decK.DSV.
Hypothesis NB1 : 1 <= b_n cx.
Hypothesis NN0 : b_small cx = 0 -> b_tt cx <> 0.
Hypothesis NN1 : b_small cx = 1 -> b_ll16 cx <> 0 /\ b_ll4 cx <> 0.
Hypothesis DPA : dpureA cx.
Hypothesis ROOM : z_lo z + RT_STACK + DEC_STACK <= uspi.
Hypothesis FRMAX : (length fr < FRAMES_MAX)%nat.
Hypothesis ACE : alloc_ceiling = sp0 - STACK_WIN.
(* [comment removed for export] *)
Variable LIVEK : list (Z * Z).
Variables (zp zn op on : Z) (fS : Z) (kS : nat).
Hypothesis SLIVK : In (S, 64144) LIVEK.
Hypothesis ZLIVK : In (zp, zn) LIVEK. Hypothesis ZLO : zp <= b_src cx. Hypothesis ZHI : b_src cx + b_len cx <= zp + zn.
Hypothesis OLIVK : In (op, on) LIVEK. Hypothesis OLO : op <= DST. Hypothesis OHI : DST + dlen <= op + on.
Hypothesis TLIVK : b_tt cx <> 0 -> In (b_tt cx, 400000 * b_n cx) LIVEK.
Hypothesis L16LIVK : b_ll16 cx <> 0 -> In (b_ll16 cx, 200000 * b_n cx) LIVEK.
Hypothesis L4LIVK : b_ll4 cx <> 0 -> In (b_ll4 cx, 50000 * b_n cx) LIVEK.
Hypothesis FSIN : In (fS, kS) fr. Hypothesis FSLO : fS <= STRM. Hypothesis FSHI : STRM + 80 <= fS + fs_size kS - 8.
Hypothesis WCS : forall x, (S <= x < S + 64144) \/ (STRM <= x < STRM + 80) \/ (DST <= x < DST + dlen) -> ~ outside Wc x.
Hypothesis BNEW : forall x, ~ outside (blk_ivls cx) x -> ~ aclient live0 fr usp x.
Hypothesis KLIB : forall m, PRESI m -> L_libA.LIB_A m.
Hypothesis KZSH : forall m, PRESI m -> bytes_at a0segs m (shad STRM) (repeat z8 10).
Variable CMIN : Z. Hypothesis CMIN0 : 0 <= CMIN.
Variable CMAX : Z.                                     (* [comment removed for export] *)
Variable R0 : Z * dst * dstrm.                         (* [comment removed for export] *)

(* [comment removed for export] *)
Definition TAILP (x : Z) : Prop := b_strm (z_cx z) + 44 <= x < b_strm (z_cx z) + 80.
Definition INVZ (Σ : rts RT) (m : mem) : Prop := SOK Σ /\ rt_live RT Σ = LIVEK /\ ART RT Σ m /\ KMem.mem_inv asegs m /\ PRESI m /\ agree_on TAILP mi m.

(* [comment removed for export] *)
Hypothesis HKZ : forall c' (Σ' : rts RT) (m' : mem) (rv' : Z) (J' : jk) (d' : dst) (s' : dstrm) (dbytes rest : list byte)
    (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F' fc',
  (rv', d', s') = R0 ->
  ASTA RT Σ' PMc (eq (MS (mkR (z_ra z) (z_sp z) (z_gp z) (z_tp z) t0 t1 t2 (z_s0 z) (z_s1 z) (Z_to_bv 64 rv') a1 a2 a3 a4 a5 a6 a7
                              (z_s2 z) (z_s3 z) (z_s4 z) (z_s5 z) (z_s6 z) (z_s7 z) (z_s8 z) (z_s9 z) (z_s10 z) (z_s11 z) t3 t4 t5 t6)
                         F' (ret_pc (z_ra z)) fc' None m' (seg_rom a0segs))) c' ->
  INVZ Σ' m' -> CMIN <= rt_credit RT Σ' <= CMAX ->
  dmem DI_A0 cx (z_g1 z) (z_sv z) (z_payload z) m' (dvF cx J' d' s') -> FDESTA z m' s' dbytes rest -> stk asegs m' (z_lo z) usp ->
  dpureF cx (bs_of cx J' s') (z_payload z) J' d' s' -> -5 <= rv' <= 4 ->
  realizes asegs c' T.

Ltac bz_norm := cbn [bz_setm0 z_cx z_ra z_sp z_gp z_tp z_s0 z_s1 z_s2 z_s3 z_s4 z_s5 z_s6 z_s7 z_s8 z_s9 z_s10 z_s11 z_F z_fc z_g1 z_sv z_payload z_lo z_m0 z_fj z_spi] in *.

Lemma bz_zok : forall m F fc, bzdctx_okA (ZZ m F fc) SHS.
Proof. intros. exact ZOK. Qed.

(* [comment removed for export] *)
Lemma bz_lin : 0 < S /\ S + 64144 <= z_lo z /\ 0 < STRM /\ STRM + 80 <= z_lo z /\ 0 < DST /\ DST + dlen <= z_lo z /\ 0 <= dlen /\ uspi = usp - 400 /\ z_lo z + 400 <= usp /\
  S mod 16 = 0 /\ STRM mod 8 = 0 /\ Z.of_nat (length (z_payload z)) = b_len cx.
Proof.
  destruct ZOK as (LIN & _). destruct LIN as ((A1 & A2) & (B1 & B2) & _ & (C1 & C2) & (D1 & _) & (E1 & E2) & _ & _ & (F1 & F2 & _) & H1 & _ & PL).
  repeat split; try assumption; lia.
Qed.

(* [comment removed for export] *)
Lemma bz_wla : forall m F fc x, ~ KFrame.outside (WLA (ZZ m F fc)) x ->
  (uspi <= x < usp) \/ (8 <= x < 8 + 0 - 8) \/ (2147450881 <= x < 2147450881 + 0) \/ ~ outside Wc x.
Proof.
  intros m F fc x Hx. pose proof bz_lin as (_ & _ & _ & _ & _ & _ & DL0 & EU & _). unfold WLA in Hx. bz_norm. cbn [KFrame.outside] in Hx.
  assert (C : (S <= x < S + 64144) \/ (STRM <= x < STRM + 80) \/ (DST <= x < DST + dlen) \/ (uspi <= x < usp)) by (clear - Hx EU DL0; lia).
  destruct C as [C|[C|[C|C]]]; [right; right; right; apply WCS; left; exact C| right; right; right; apply WCS; right; left; exact C
                               | right; right; right; apply WCS; right; right; exact C| left; exact C].
Qed.

(* [comment removed for export] *)
Lemma bz_dlive : forall Σ m, INVZ Σ m -> dliveA RT Σ m cx zp zn op on.
Proof.
  intros Σ m (SK & LV & ART0 & MI0 & PR0 & _). pose proof bz_lin as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & T8 & _).
  unfold dliveA. rewrite LV. repeat (split; [assumption|]).
  split; [| split; [exact T8| exact (KZSH m PR0)]].
  exists fS, kS. split; [| split; [exact FSLO| exact FSHI]]. rewrite (proj1 SK). cbn [app]. exact FSIN.
Qed.

(* [comment removed for export] *)
Lemma bz_w14 : forall x, ~ KFrame.outside ([(S, S + 64144); (STRM, STRM + 20)] ++ blk_ivls cx) x ->
  ((uspi <= x < usp) \/ (8 <= x < 8 + 0) \/ (2147450881 <= x < 2147450881 + 0)) \/ ~ outside Wc x \/ ~ aclient live0 fr usp x.
Proof.
  intros x Hx. right.
  destruct (outside_dec (blk_ivls cx) x) as [O|O]; [left| right; exact (BNEW x O)].
  apply WCS. cbn [app KFrame.outside] in Hx.
  assert (C : (S <= x < S + 64144) \/ (STRM <= x < STRM + 20)). { destruct (Z_lt_dec x S); destruct (Z_le_dec (S + 64144) x); destruct (Z_lt_dec x STRM); destruct (Z_le_dec (STRM + 20) x); try lia; exfalso; apply Hx; repeat split; try lia; exact O. }
  clear - C. lia.
Qed.

(* [comment removed for export] *)
Lemma bz_w14_lo : forall x, ~ KFrame.outside ([(S, S + 64144); (STRM, STRM + 20)] ++ blk_ivls cx) x -> 0 < x < z_lo z.
Proof.
  intros x Hx. pose proof bz_lin as (S0 & S1 & T0 & T1 & _).
  destruct ZOK as (LIN & _ & _ & ZT & ZL16 & ZL4 & _). destruct LIN as (_ & _ & _ & _ & _ & _ & SM01 & _ & (CL & _) & _).
  cbn [app KFrame.outside] in Hx.
  destruct (outside_dec (blk_ivls cx) x) as [O|O].
  - assert (C : (S <= x < S + 64144) \/ (STRM <= x < STRM + 20)). { destruct (Z_lt_dec x S); destruct (Z_le_dec (S + 64144) x); destruct (Z_lt_dec x STRM); destruct (Z_le_dec (STRM + 20) x); try lia; exfalso; apply Hx; repeat split; try lia; exact O. }
    clear - C S0 S1 T0 T1. lia.
  - unfold blk_ivls in O. destruct SM01 as [E|E]; rewrite E in O; cbn [Z.eqb KFrame.outside outside] in O.
    + destruct (ZT (NN0 E)) as ((B0 & B1) & _). clear - O B0 B1 CL. lia.
    + destruct (NN1 E) as [N16 N4]. destruct (ZL16 N16) as ((B0 & B1) & _). destruct (ZL4 N4) as ((C0 & C1) & _). clear - O B0 B1 C0 C1 CL. lia.
Qed.


(* [comment removed for export] *)
Lemma bz_dst_out : forall x, DST <= x < DST + dlen -> KFrame.outside ([(S, S + 64144); (STRM, STRM + 20)] ++ blk_ivls cx) x.
Proof.
  intros x Hx. destruct ZOK as (LIN & _ & SEP & ZT & ZL16 & ZL4 & _). destruct LIN as (_ & _ & _ & _ & _ & _ & SM01 & _).
  destruct SEP as (_ & _ & D3 & _ & D5 & _). unfold disj in D3, D5.
  cbn [app KFrame.outside]. split; [clear - Hx D3; lia|]. split; [clear - Hx D5; lia|].
  unfold blk_ivls. destruct SM01 as [E|E]; rewrite E; cbn [Z.eqb KFrame.outside].
  - destruct (ZT (NN0 E)) as (_ & _ & _ & B & _). unfold disj in B. clear - Hx B. lia.
  - destruct (NN1 E) as [N16 N4]. destruct (ZL16 N16) as (_ & _ & _ & B & _). destruct (ZL4 N4) as (_ & _ & _ & C & _). unfold disj in B, C. clear - Hx B C. lia.
Qed.


(* [comment removed for export] *)
Lemma bz_sh : forall Σ m F fc, INVZ Σ m -> bzd_sh (ZZ m F fc) (WLA (ZZ m F fc)) m.
Proof.
  intros Σ m F fc (SK & LV & ART0 & MI0 & PR0 & _).
  pose proof bz_lin as (S0 & S1 & T0 & T1 & D0 & D1 & DL0 & EU & LU & S16 & T8 & PLEN). pose proof alloc_ceiling_range as ACR.
  destruct ZOK as (LIN & _). destruct LIN as (_ & _ & _ & _ & _ & _ & _ & _ & (CL & _) & _).
  destruct DPA as (_ & _ & _ & _ & _ & TT16 & L1616 & L416 & _).
  assert (SLIV : In (S, 64144) (rt_live RT Σ)) by (rewrite LV; exact SLIVK).
  assert (OLIV : In (op, on) (rt_live RT Σ)) by (rewrite LV; exact OLIVK).
  assert (FIN : In (fS, kS) (rt_frames RT Σ)) by (rewrite (proj1 SK); cbn [app]; exact FSIN).
  pose proof (af_live_offshadow RT AF Σ m _ _ ART0 SLIV) as SOFF. pose proof (af_live_offshadow RT AF Σ m _ _ ART0 OLIV) as OOFF.
  pose proof (af_frames_hi RT AF Σ m _ _ ART0 FIN) as FOFF. pose proof (af_live_range RT AF Σ m _ _ ART0 OLIV) as (OL0 & OL1 & _).
  pose proof (af_sp0_range RT AF Σ m ART0) as (_ & SP0T). pose proof (ag_spt G) as GSPT. unfold USTACK_TOP, STACK_WIN in *.
  assert (APP : app_fp (WLA (ZZ m F fc))).
  { unfold WLA. cbn [bz_setm0 z_cx z_spi app_fp]. unfold SH_LO, SH_HI.
    repeat split; first [exact I| clear - SOFF; lia| clear - FOFF FSLO FSHI; lia| clear - OOFF OLO OHI DL0; lia| clear - CL LU EU ACR; lia]. }
  unfold bzd_sh. cbn [bz_setm0 z_cx].
  split; [exact (live_reader RT AF Σ m S 64144 _ ART0 SLIV ltac:(clear - S16; Z.div_mod_to_equations; lia) eq_refl APP)|].
  split. { apply (strm_reader m STRM (shad STRM) _); [split; [exact T8| reflexivity]| clear - T0; lia| clear - T1 LU GSPT; lia| exact (KZSH m PR0)| exact APP]. }
  split. { apply (shpW_sub a0segs _ _ m m op (op + on) _ _ (live_readerp RT AF Σ m op on _ ART0 OLIV APP) (munch_refl _ m)); [intros x H; exact H| exact OLO| exact OHI]. }
  split. { apply (shzW_of_acc a0segs _ m 802816 1024 _ _ (af_acc_crc RT AF Σ m ART0) APP); clear; Z.div_mod_to_equations; lia. }
  split. { apply (shzW_of_acc a0segs _ m 804096 2048 _ _ (af_acc_rnums RT AF Σ m ART0) APP); clear; Z.div_mod_to_equations; lia. }
  split.
  - intros E. assert (TLIV : In (b_tt cx, 400000 * b_n cx) (rt_live RT Σ)) by (rewrite LV; exact (TLIVK (NN0 E))).
    exact (live_reader RT AF Σ m _ _ _ ART0 TLIV ltac:(clear - TT16; Z.div_mod_to_equations; lia) ltac:(clear; Z.div_mod_to_equations; lia) APP).
  - intros E. destruct (NN1 E) as [N16 N4].
    assert (L16LIV : In (b_ll16 cx, 200000 * b_n cx) (rt_live RT Σ)) by (rewrite LV; exact (L16LIVK N16)).
    assert (L4LIV : In (b_ll4 cx, 50000 * b_n cx) (rt_live RT Σ)) by (rewrite LV; exact (L4LIVK N4)).
    split; [exact (live_reader RT AF Σ m _ _ _ ART0 L16LIV ltac:(clear - L1616; Z.div_mod_to_equations; lia) ltac:(clear; Z.div_mod_to_equations; lia) APP)
           | exact (live_reader RT AF Σ m _ _ _ ART0 L4LIV ltac:(clear - L416; Z.div_mod_to_equations; lia) ltac:(clear; Z.div_mod_to_equations; lia) APP)].
Qed.


(* [comment removed for export] *)
Lemma bz_tail_step : forall Σ W (m m' : mem), SOK Σ -> rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) uspi W m m' -> (forall x, TAILP x -> KFrame.outside W x) ->
  agree_on TAILP mi m -> agree_on TAILP mi m'.
Proof.
  intros Σ W m m' SK STEP HW TL. apply (agree_trans _ mi m m' TL). apply (agree_of_pres_fp _ _ _ W m m' _ STEP). intros x Hx. split; [| exact (HW x Hx)].
  apply (acl_caller G Σ x SK). right; right; right; left. exists fS, kS. split; [exact FSIN| unfold TAILP in Hx; clear - Hx FSLO FSHI; lia].
Qed.
Lemma bz_tail_wla : forall m F fc x, TAILP x -> KFrame.outside (WLA (ZZ m F fc)) x.
Proof.
  intros m F fc x Hx. unfold TAILP in Hx. pose proof bz_lin as (_ & _ & _ & T1 & _ & _ & _ & EU & LU & _).
  destruct ZOK as (_ & _ & SEP & _). destruct SEP as (D1 & _ & _ & _ & D5 & _). unfold disj in D1, D5.
  unfold WLA. cbn [bz_setm0 z_cx z_spi KFrame.outside]. repeat split; clear - Hx D1 D5 T1 EU LU; lia.
Qed.
Lemma bz_tail_w14 : forall x, TAILP x -> KFrame.outside ([(S, S + 64144); (STRM, STRM + 20)] ++ blk_ivls cx) x.
Proof.
  intros x Hx. unfold TAILP in Hx. destruct ZOK as (LIN & _ & SEP & ZT & ZL16 & ZL4 & _). destruct LIN as (_ & _ & _ & _ & _ & _ & SM01 & _).
  destruct SEP as (D1 & _). unfold disj in D1.
  cbn [app KFrame.outside]. split; [clear - Hx D1; lia|]. split; [clear - Hx; lia|].
  unfold blk_ivls. destruct SM01 as [E|E]; rewrite E; cbn [Z.eqb KFrame.outside].
  - destruct (ZT (NN0 E)) as (_ & _ & B & _). unfold disj in B. clear - Hx B. lia.
  - destruct (NN1 E) as [N16 N4]. destruct (ZL16 N16) as (_ & _ & B & _). destruct (ZL4 N4) as (_ & _ & C & _). unfold disj in B, C. clear - Hx B C. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bzd_loop_l2 : forall f (Σ : rts RT) (m : mem) F fc
    (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s7 t3 t4 t5 t6 w32 w104 w112 w120 w184 w192 w200 w208 w240 w248 : word)
    (rv : Z) (J : jk) (d : dst) (s : dstrm) (dbytes rest : list byte) c,
  INVZ Σ m -> Z.of_nat f + CMIN <= rt_credit RT Σ -> rt_credit RT Σ <= CMAX ->
  FCHA (ZZ m F fc) SHS w0 m J d s dbytes rest w32 w104 w112 w120 w184 w192 w200 w208 w240 w248 ->
  S0F_bzd_loop1.FFACTS (ZZ m F fc) J rv d s ->
  (d_state d = BZ_X_OUTPUT -> b_len cx / 6 - d_blockNo d < Z.of_nat f) ->
  K_L f (rv, d, s) = R0 ->
  ASTA RT Σ PMc (eq (MS (ZRA (ZZ m F fc) SHS ra t0 t1 t2 (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 s4 s7 t3 t4 t5 t6) F (Z_to_bv 64 0x87038) fc None m (seg_rom a0segs))) c ->
  realizes asegs c T.
Proof.
  induction f as [f IH] using lt_wf_ind.
  intros Σ m F fc ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s7 t3 t4 t5 t6 w32 w104 w112 w120 w184 w192 w200 w208 w240 w248 rv J d s dbytes rest c IV CRD CRU CH FF FUEL ER Hc.
  pose proof IV as (SK & LV & ART0 & MI0 & PR0 & TL0).
  pose proof bz_lin as (S0 & S1 & T0 & T1 & D0 & D1 & DL0 & EU & LU & S16 & T8 & PLEN).
  pose proof G as [_ _ _ _ GLOW GLOR GPUS GSPT GSPA _ _ _ _ _].
  pose proof (proj1 (proj2 SK)) as SP0E.
  assert (ST0 : stk asegs m (z_lo z) uspi) by (destruct CH as (_ & _ & _ & _ & _ & X); exact X).
  set (QF := fun (R : Z * dst * dstrm) (ms : machine_state) => R = R0 -> forall c', ASTA RT Σ PMc (eq ms) c' -> realizes asegs c' T).
  (* [comment removed for export] *)
  assert (KRET : A0_KRet (ZZ m F fc) QF (WLA (ZZ m F fc))).
  { unfold A0_KRet. intros q0 q1 q2 g1 g2 g3 g4 g5 g6 g7 q3 q4 q5 q6 m' rv' J' d' s' dbytes' rest' DM' CRC' DST' ST' MU' WM' NMI' DP' RV'.
    apply evt_done. intros ER' c' Hc'. bz_norm.
    destruct (after_l1 AF G Σ _ m m' SK ART0 MI0 ST0 PR0 NMI' MU' WM' (bz_wla m F fc)) as (ART' & MI' & _ & PR' & STEPL).
    pose proof (bz_tail_step Σ _ m m' SK STEPL (bz_tail_wla m F fc) TL0) as TL'.
    apply (HKZ c' Σ m' rv' J' d' s' dbytes' rest' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ER' Hc' (conj SK (conj LV (conj ART' (conj MI' (conj PR' TL'))))) ltac:(clear - CRD CRU; lia) DM' DST' ST' DP' RV'). }
  (* [comment removed for export] *)
  assert (KCALL : forall f', f = Datatypes.S f' -> A0_KCall (ZZ m F fc) SHS w0 QF (WLA (ZZ m F fc)) f').
  { intros f' EF. unfold A0_KCall.
    intros q0 q1 q2 g1 g2 g3 g4 g5 g6 g7 r4 r7 q3 q4 q5 q6 v32 v104 v112 v120 v184 v192 v200 v208 v240 v248 m' J' d' s' dbytes' rest' CH' MU' WM' NMI' DP' ST14 CC AV BND.
    apply evt_done. intros ER' c' Hc'. bz_norm.
    destruct (after_l1 AF G Σ _ m m' SK ART0 MI0 ST0 PR0 NMI' MU' WM' (bz_wla m F fc)) as (ART1 & MI1 & _ & PR1 & STEPL).
    pose proof (bz_tail_step Σ _ m m' SK STEPL (bz_tail_wla m F fc) TL0) as TL1.
    destruct CH' as (DM' & CRC' & (DSTA & DL & Edb & Lout) & FRS & FSV & STK'). bz_norm.
    pose proof (decompress_frame d' s' ltac:(rewrite ST14; unfold BZ_X_OUTPUT; clear; lia) ltac:(rewrite ST14; clear; lia)) as DF.
    unfold K_call in ER'. unfold ZRA in Hc'. bz_norm. rewrite ZTP in Hc'.
    refine (cps_realizes asegs _ _ T c' (DEC14 Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' cx (z_payload z) J' d' s' zp zn op on (z_lo z)
              FDO MST eq_refl eq_refl ltac:(rewrite SP0E; exact ACE) (dmemL_of m' cx _ _ _ _ DM') (KLIB m' PR1)
              (bz_dlive Σ m' (conj SK (conj LV (conj ART1 (conj MI1 (conj PR1 TL1)))))) DPA PLEN NB1 NN0 NN1 DP' ST14 AV
              ltac:(rewrite (proj1 SK); cbn [app]; exact FRMAX) ltac:(clear - CRD EF CMIN0; lia) ART1 MI1 STK' ltac:(rewrite SP0E; exact GLOW) ROOM
              ltac:(clear - GSPT GPUS; lia) GSPA) Hc' _).
    clear Hc'. intros c2 (Σ' & Hq & LV' & FR' & SP' & CR').
    destruct (ASTA_unpack RT Σ' _ _ c2 Hq) as (ms2 & (m2 & u0 & u1 & u2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & u3 & u4 & u5 & u6 & F2 & fc2 & J2 & POST) & Hc2). clear Hq.
    destruct (decompress d' s') as [[rv2 d2] s2] eqn:EDEC.
    destruct POST as (-> & ART2 & MI2 & ST2 & DML2 & LIB2 & DP2 & PW2 & STEP2).
    destruct DF as (Fout & Fav & Ftout & Fcc & Fbn & Fbn2 & Fst).
    rewrite (ret_pc_even 0x87038 ltac:(lia) eq_refl) in Hc2.
    (* [comment removed for export] *)
    assert (SK' : SOK Σ') by (exact (sig_ok_eq RT _ _ _ _ _ _ Σ Σ' SK LV' FR' SP')).
    pose proof (pres_step_new G Σ _ m' m2 SK PR1 STEP2 bz_w14) as PR2.
    pose proof (bz_tail_step Σ _ m' m2 SK STEP2 bz_tail_w14 TL1) as TL2.
    (* [comment removed for export] *)
    assert (AGU : agree_on (fun x => uspi <= x < usp) m' m2).
    { apply (agree_of_pres_fp _ _ _ _ m' m2 _ STEP2). intros x Hx. split; [left; unfold USTACK_TOP in *; clear - Hx GSPT; lia|].
      destruct (outside_dec ([(S, S + 64144); (STRM, STRM + 20)] ++ blk_ivls cx) x) as [O|O]; [exact O| exfalso]. pose proof (bz_w14_lo x O) as B. clear - B Hx LU EU. lia. }
    assert (FRS2 : rw_cells a0segs m2 uspi (bzd_slots S SHS w0 v32 v104 v112 v120 v184 v192 v200 v208 v240 v248)).
    { apply (n_rw_cells_agree a0segs m' m2 _ _ FRS). eapply agree_sub; [exact AGU|]. intros x Hx. cbv beta in Hx |- *. unfold bzd_slots in Hx. cbn [cells_size csize Nat.add] in Hx. clear - Hx EU. lia. }
    assert (FSV2 : rw_cells a0segs m2 (uspi + 296) (FSAVA (ZZ m F fc))).
    { apply (n_rw_cells_agree a0segs m' m2 _ _ FSV). eapply agree_sub; [exact AGU|]. intros x Hx. cbv beta in Hx |- *. unfold FSAVA in Hx. cbn [cells_size csize Nat.add] in Hx. clear - Hx EU. lia. }
    assert (DSTA2 : u8arr a0segs m2 DST dbytes').
    { apply (n_u8arr_agree a0segs m' m2 _ _ DSTA). apply (agree_of_pres_fp _ _ _ _ m' m2 _ STEP2). intros x Hx. cbv beta in Hx. rewrite DL in Hx. split.
      - right; right; left. exists op, on. split; [rewrite LV; exact OLIVK| clear - Hx OLO OHI; lia].
      - exact (bz_dst_out x Hx). }
    destruct (dec_img RT AF AF_DRV Σ' m2 ART2 LIB2) as (_ & _ & _ & CRC2).
    assert (DM2 : dmem DI_A0 cx (z_g1 z) (z_sv z) (z_payload z) m2 (dvF cx J2 d2 s2)) by (rewrite ZG1, ZSV; exact (dmem_of_L RT AF AF_DRV Σ' m2 cx _ _ ART2 LIB2 DML2)).
    assert (LV2 : rt_live RT Σ' = LIVEK) by (rewrite LV'; exact LV).
    assert (CRD' : Z.of_nat f' + CMIN <= rt_credit RT Σ') by (rewrite CR'; clear - CRD EF; lia).
    assert (CRU' : rt_credit RT Σ' <= CMAX) by (rewrite CR'; clear - CRU; lia).
    rewrite <- ZTP in Hc2.
    eapply (IH f' ltac:(clear - EF; lia) Σ' m2 F2 fc2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ v32 v104 v112 v120 v184 v192 v200 v208 v240 v248 rv2 J2 d2 s2 dbytes' rest' c2
              (conj SK' (conj LV2 (conj ART2 (conj MI2 (conj PR2 TL2))))) CRD' CRU').
    + unfold FCHA, FIMGA, FDESTA. bz_norm. rewrite Fout, Fav.
      split; [exact DM2|]. split; [exact CRC2|]. split; [split; [exact DSTA2| split; [exact DL| split; [exact Edb| exact Lout]]]|]. split; [exact FRS2|]. split; [exact FSV2| exact ST2].
    + unfold S0F_bzd_loop1.FFACTS. bz_norm. split; [exact (S0F_bzd_loop3s.S0F_bzd_loop3.dpureF_rebase _ _ _ _ _ _ _ DP2)|]. split; [exact Fst|]. split; [rewrite Fcc; exact CC|].
      split; [rewrite Fav; exact AV| exact PW2].
    + intros Hst2. specialize (Fbn2 Hst2 ltac:(rewrite ST14; clear; lia)). clear - Fbn2 BND. lia.
    + exact ER'.
    + unfold ZRA. bz_norm. exact Hc2. }
  eapply (l1_realizes RT AF Σ PMc _ T c MST Hc).
  eapply evt_mono;
    [ eapply (A0F_bzd_skT.A0_bzd_L (ZZ m F fc) SHS w0 QF (bz_zok m F fc) (fun _ => NN0) (fun _ => NN1) (bz_sh Σ m F fc IV) f KRET KCALL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m rv J d s dbytes rest CH
                (munch_refl _ m) (wmono_refl _ m) (kmem_inv_N _ _ MI0) FF FUEL)
    | intros ms' HQ; exact (HQ ER) ].
Qed.
End BZDL2.
