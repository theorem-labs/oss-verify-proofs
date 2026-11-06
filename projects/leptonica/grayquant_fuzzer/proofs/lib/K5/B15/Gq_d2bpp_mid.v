(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import Tac RzCPS NodesA SysStep Arr StoreFast.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import ImageA Layout RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit D_iface D_defs
  Lept_iface Lept_lits Lept_litmem Lept_env LeptC_kit Lept_leaf LeptC_leaf LeptL_kit Lept_objkit Lept_chain Lept_gmax_defs
  Gm_iface Gq_obj Gq_iface Gq_dt2tab Gq_dither2_l1 Gq_dither2_line Gq_dither2_rows Gq_cmaplin Gq_d2bpp_cmdefs.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import Lept_fuzzkit Lept_deserkit Gm_kit Gm_livekit Gm_livekit2 LeptB_guard LeptB_guard2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac park_ne := repeat match goal with H : (?a <> ?b) |- _ => lazymatch type of a with Z => change (a <> b) with (parked (a <> b)) in H end end.

(* [comment removed for export] *)
Ltac u32arr_side AG A :=
  eapply agree_sub; [exact AG|]; cbv beta; let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx;
  first [ acl_dispatch A | split; [acl_dispatch A | first [notin_side | outside_side]] ].
Ltac rt_transport_extra m m' AG ::=
  lept_rt_transport_extra m m' AG;
  repeat match goal with
  | H : u32arr asegs m ?A ?ws |- _ =>
      first [ match goal with WMx : wmono asegs m m', L : Z.of_nat (length ws) = ?n |- _ =>
                apply (u32arr_agree_yn m m' A ws n) in H; [ | exact L | solve [u32arr_side AG A] | exact WMx ] end
            | idtac "note: dropping u32arr fact at a runtime call:" H; clear H ]
  end.

(* [comment removed for export] *)
Lemma srliw30_guard : forall x, 0 <= x < 536870912 -> bv_swrap 32 (bv_wrap 32 (x + 536870912) / 1073741824) = 0.
Proof.
  intros x Hx. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32) with 4294967296.
  rewrite Z.mod_small by lia. rewrite Z.div_small by lia. reflexivity.
Qed.

Section D2MID.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis RC : rt_contracts RT.
Hypothesis CML : pixcmapCreateLinear24_cps RT.
Hypothesis SCM : pixSetColormap_cps RT.
Hypothesis CMF : d2_cmfree_cps RT.

Notation ONE := (Z_to_bv 64 1) (only parsing).

(* [comment removed for export] *)
Definition d2m_W (sa dat rd pixd : Z) : list (Z * Z) := [(dat, dat + rd); (pixd + 48, pixd + 56); (sa + 16, sa + 40); (sa + 56, sa + 144)].
Definition d2m_keep (L : list (Z * Z)) (frames : list (Z * nat)) (sa dat rd pixd : Z) (a : Z) : Prop :=
  aclient L frames sa a /\ outside (d2m_W sa dat rd pixd) a.

(* [comment removed for export] *)
Definition d2m_geom (sp0 lo sa usp fr pixd dat rd datas rs wpls wpld w h : Z) : Prop :=
  0 < w <= 20000 /\ 0 < h <= 20000 /\ wpls = (w * 8 + 31) / 32 /\ wpld = (w * 2 + 31) / 32 /\ rs = 4 * (wpls * h) /\ rd = 4 * (wpld * h) /\ rs <= 67108864
  /\ 0 < dat /\ dat mod 16 = 0 /\ dat + rd <= sp0 - STACK_WIN /\ (dat + rd <= 0x10000 \/ SEGTOP_A <= dat) /\ (dat + rd <= 0x7fff7000 \/ 0x10007fff8000 <= dat)
  /\ 0 < datas /\ datas mod 16 = 0 /\ datas + rs <= sp0 - STACK_WIN /\ (datas + rs <= 0x10000 \/ SEGTOP_A <= datas) /\ (datas + rs <= 0x7fff7000 \/ 0x10007fff8000 <= datas)
  /\ 0 < pixd /\ pixd mod 16 = 0 /\ pixd + 64 <= sp0 - STACK_WIN /\ (pixd + 64 <= 0x10000 \/ SEGTOP_A <= pixd) /\ (pixd + 64 <= 0x7fff7000 \/ 0x10007fff8000 <= pixd)
  /\ (dat + rd <= datas \/ datas + rs <= dat) /\ (pixd + 64 <= dat \/ dat + rd <= pixd) /\ (pixd + 64 <= datas \/ datas + rs <= pixd)
  /\ 0 < fr /\ fr mod 64 = 0 /\ fr + 256 <= sp0 - STACK_WIN /\ SEGTOP_A <= fr /\ (fr + 256 <= 0x7fff7000 \/ 0x10007fff8000 <= fr)
  /\ (fr + 256 <= dat \/ dat + rd <= fr) /\ (fr + 256 <= datas \/ datas + rs <= fr) /\ (fr + 256 <= pixd \/ pixd + 64 <= fr)
  /\ sp0 - STACK_WIN <= lo /\ 0 <= lo /\ lo + LSTK 10 <= sa /\ sa mod 32 = 0 /\ sa + 256 <= usp /\ usp <= sa + 272 /\ usp mod 16 = 0
  /\ usp + 16 <= USTACK_TOP /\ usp <= sp0 /\ SEGTOP_A + STACK_WIN <= sp0 <= USTACK_TOP /\ 0x7fff80000000 <= sp0.

(* [comment removed for export] *)
Definition d2m_post (Σ : rts RT) PMc (gp : word) (sa usp lo fr pixd dat rd : Z) (vd : pixv) (m0 : mem) : config -> Prop :=
  fun c => exists (Σ' : rts RT) (m' : mem) (cmap carr : Z)
                  (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s7' s8' s10' s11' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32),
    ASTA RT Σ' PMc (eq (MS (mkR ra' (Z_to_bv 64 sa) gp (Z_to_bv 64 TP_A) t0' t1' t2' (Z_to_bv 64 usp) (Z_to_bv 64 sa) a0' a1' a2' a3' a4' a5' a6' a7'
                                 (Z_to_bv 64 fr) (Z_to_bv 64 (fr + 112)) s4' s5' s6' s7' s8' (Z_to_bv 64 (fr / 8 + 2147450880)) s10' s11' t3' t4' t5' t6')
                            F' (Z_to_bv 64 0xa0394) (frm_clear fc') None m' (seg_rom asegs))) c
    /\ ART RT Σ' m' /\ mem_inv asegs m' /\ stk asegs m' lo sa /\ LIBH m' /\ io_ssp m'
    /\ rt_live RT Σ' = (carr, 16) :: (cmap, 24) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
    /\ rt_credit RT Σ - 6 <= rt_credit RT Σ'
    /\ cmap_obj (rt_live RT Σ') m' cmap (mkCmapv carr 2 4 4) /\ 0 < cmap /\ 0 < carr /\ cmap <> carr
    /\ (forall e, In e (rt_live RT Σ) -> fst e <> cmap /\ fst e <> carr)
    /\ (forall a, d2m_keep (rt_live RT Σ) (rt_frames RT Σ) sa dat rd pixd a -> (a < cmap \/ cmap + 24 <= a) /\ (a < carr \/ carr + 16 <= a))
    /\ rw_cells asegs m' pixd (pix_cells (mkPixv (p_w vd) (p_h vd) (p_d vd) (p_spp vd) (p_wpl vd) (p_xres vd) (p_yres vd) (p_inf vd) (p_spec vd) cmap (p_data vd)))
    /\ rw_cells asegs m' (sa + 24) [C8 (Z_to_bv 64 (fr + 80))] /\ wr_at asegs m' (sa + 16) 24 /\ wr_at asegs m' (sa + 56) 88
    /\ agree_on (d2m_keep (rt_live RT Σ) (rt_frames RT Σ) sa dat rd pixd) m0 m'.

(* [comment removed for export] *)
Lemma d2_mid2 : forall (Σ ΣX : rts RT) PMc (m0 mh : mem)
    (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (sa usp lo fr pixd dat rd datas rs wpls wpld w h fp1 bufs1 bufs2 tv t38 t14 : Z) (vd : pixv) (frs0 : list (Z * nat)) (j128 : list byte) (tw t38w t14w : list word),
  fdfs_only PMc -> mat_stable PMc ->
  d2m_geom (rt_sp0 RT Σ) lo sa usp fr pixd dat rd datas rs wpls wpld w h ->
  d2r_geom (rt_sp0 RT Σ) lo sa dat rd datas rs bufs1 bufs2 (wpls * 4) wpls wpld w h tv t38 t14 ->
  rt_live RT ΣX = (t14, 1024) :: (t38, 1024) :: (tv, 1024) :: (bufs2, wpls * 4) :: (bufs1, wpls * 4) :: rt_live RT Σ ->
  rt_frames RT ΣX = (fr, 2%nat) :: frs0 -> rt_frames RT Σ = (fr, 2%nat) :: frs0 -> rt_sp0 RT ΣX = rt_sp0 RT Σ -> rt_credit RT ΣX = rt_credit RT Σ ->
  NoDup [bufs1; bufs2; tv; t38; t14] ->
  (forall e, In e (rt_live RT Σ) -> fst e <> bufs1 /\ fst e <> bufs2 /\ fst e <> tv /\ fst e <> t38 /\ fst e <> t14) ->
  Z.of_nat (length (rt_live RT Σ)) + 7 <= LIVE_MAX -> Z.of_nat (length (rt_frames RT Σ)) + 3 <= Z.of_nat FRAMES_MAX -> 8 <= rt_credit RT Σ ->
  (forall p n, In (p, n) (rt_live RT Σ) -> 0 < n) ->
  rw_cells asegs mh pixd (pix_cells vd) -> pix_hdr_ok vd -> In (pixd, 64) (rt_live RT Σ) -> In (dat, rd) (rt_live RT Σ) -> In (datas, rs) (rt_live RT Σ) ->
  p_w vd = w -> p_h vd = h -> p_d vd = 2 -> p_wpl vd = wpld -> p_data vd = dat -> p_cmap vd = 0 ->
  0 <= fp1 < 2^64 -> chain_ok mh usp fp1 [RA_TOP] ->
  ART RT ΣX mh -> mem_inv asegs mh -> stk asegs mh lo sa -> LIBH mh -> io_ssp mh ->
  rw_cells asegs mh (usp + -16) [C8 (Z_to_bv 64 fp1); C8 (Z_to_bv 64 RA_FUZZ_OP1)] ->
  rw_cells asegs mh (sa + 16) [C8 (Z_to_bv 64 (h - 1)); C8 (Z_to_bv 64 (fr + 80)); C8 (Z_to_bv 64 1)] ->
  rw_cells asegs mh (sa + 48) [C8 (Z_to_bv 64 (fr + 112))] ->
  rw_cells asegs mh (sa + 56) (d2r_frame w wpls datas wpld dat tv t38 t14 (Z_to_bv 64 0)) ->
  rw_cells asegs mh (sa + 128) [CB 16 j128] ->
  rw_cells asegs mh (fr + 112) [C8 (Z_to_bv 64 pixd)] ->
  d2r_tabs mh tv t38 t14 tw t38w t14w -> Forall tsmall t38w -> Forall tsmall t14w ->
  agree_on (d2m_keep (rt_live RT Σ) (rt_frames RT Σ) sa dat rd pixd) m0 mh ->
  cps asegs (ASTA RT ΣX PMc (eq (MS (mkR ra (Z_to_bv 64 sa) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 sa) a0 a1 a2 a3 a4 a5 a6 a7
                                        (Z_to_bv 64 fr) (Z_to_bv 64 (wpls * 4)) s4 (Z_to_bv 64 bufs1) (Z_to_bv 64 dat) (Z_to_bv 64 h) (Z_to_bv 64 bufs2)
                                        (Z_to_bv 64 (fr / 8 + 2147450880)) s10 s11 t3 t4 t5 t6)
                                   F (Z_to_bv 64 0xa02c4) (frm_clear fc) None mh (seg_rom asegs))))
    (d2m_post Σ PMc gp sa usp lo fr pixd dat rd vd m0).
Proof using AF GP RC CML SCM CMF.
  intros Σ ΣX PMc m0 mh ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s10 s11 t3 t4 t5 t6 F fc sa usp lo fr pixd dat rd datas rs wpls wpld w h fp1 bufs1 bufs2 tv t38 t14
    vd frs0 j128 tw t38w t14w FDO MST GEOM DGEOM LVX FRSX FRS SP0X CRX ND5 FRESH5 LVB FRB CRB LVP PXD HOKD PDIN DDIN DSIN VW VH VD VWPL VDAT VCM FP1 UCX
    ART0 MI ST LH SSP UREC FRLO C48 FR56 J128 FPD TABS TS8 TS4 AG0.
  pose proof GEOM as (HW & HH & EWS & EWD & ERS & ERD & RS64 & DD0 & DD16 & CKR2 & CKS2 & CKH2 & DS0 & DS16 & CKR0 & CKS0 & CKH0
                      & PD0 & PD16 & CKR1 & CKS1 & CKH1 & APDS & APPD & APPS & FR0 & FR64 & FRHI & FRSEG & FRSH & FCD2 & FCD0 & FCD1
                      & LOW & STa & LOR & SA32 & SAU & USA & SPA & SPT & SPB & SP0R & SP0W).
  assert (WPLS : 0 < wpls <= 5001) by (rewrite EWS; clear - HW; Z.div_mod_to_equations; lia).
  assert (WPLD : 0 < wpld <= 1251) by (rewrite EWD; clear - HW; Z.div_mod_to_equations; lia).
  assert (RD0 : 0 < rd) by (rewrite ERD; clear - HH WPLD; nia).
  assert (SA16 : sa mod 16 = 0) by (clear - SA32; Z.div_mod_to_equations; lia).
  unfold LSTK, STDERR_STACK, STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in LOW, LOR, SPT, SP0R, CKR2, CKR0, CKR1, CKS2, CKS0, CKS1, FRHI, FRSEG.
  assert (USP0 : 0 <= sa) by (clear - LOR STa; lia).
  assert (USP1 : sa < 2^64) by (clear - SPB SAU SP0R; lia).
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  set (PF := d2m_keep (rt_live RT Σ) (rt_frames RT Σ) sa dat rd pixd) in AG0 |- *.
  (* [comment removed for export] *)
  assert (LSUBX : forall e, In e (rt_live RT Σ) -> In e (rt_live RT ΣX)) by (intros e He; rewrite LVX; do 5 right; exact He).
  assert (B1IN : In (bufs1, wpls * 4) (rt_live RT ΣX)) by (rewrite LVX; do 4 right; left; reflexivity).
  assert (B2IN : In (bufs2, wpls * 4) (rt_live RT ΣX)) by (rewrite LVX; do 3 right; left; reflexivity).
  assert (TVIN : In (tv, 1024) (rt_live RT ΣX)) by (rewrite LVX; do 2 right; left; reflexivity).
  assert (T8IN : In (t38, 1024) (rt_live RT ΣX)) by (rewrite LVX; right; left; reflexivity).
  assert (T4IN : In (t14, 1024) (rt_live RT ΣX)) by (rewrite LVX; left; reflexivity).
  pose proof (LSUBX _ DDIN) as DDINX. pose proof (LSUBX _ DSIN) as DSINX. pose proof (LSUBX _ PDIN) as PDINX.
  chunk_facts RT AF GP bufs1 (wpls * 4).
  lazymatch goal with H : bufs1 + _ <= rt_sp0 RT _ - _ |- _ => rename H into CKR_B1 end.
  chunk_facts RT AF GP bufs2 (wpls * 4).
  lazymatch goal with H : bufs2 + _ <= rt_sp0 RT _ - _ |- _ => rename H into CKR_B2 end.
  chunk_facts RT AF GP tv 1024.
  lazymatch goal with H : tv + _ <= rt_sp0 RT _ - _ |- _ => rename H into CKR_TV end.
  chunk_facts RT AF GP t38 1024.
  lazymatch goal with H : t38 + _ <= rt_sp0 RT _ - _ |- _ => rename H into CKR_T8 end.
  chunk_facts RT AF GP t14 1024.
  lazymatch goal with H : t14 + _ <= rt_sp0 RT _ - _ |- _ => rename H into CKR_T4 end.
  unfold STACK_WIN, SEGTOP_A in CKR_B1, CKR_B2, CKR_TV, CKR_T8, CKR_T4.
  (* [comment removed for export] *)
  pose proof (af_live_disj RT AF ΣX mh bufs1 (wpls * 4) pixd 64 [(t14, 1024); (t38, 1024); (tv, 1024); (bufs2, wpls * 4)] (rt_live RT Σ) ART0
                ltac:(rewrite LVX; reflexivity) ltac:(cbn [app]; do 4 right; exact PDIN)) as AP_B1_P.
  pose proof (af_live_disj RT AF ΣX mh bufs2 (wpls * 4) pixd 64 [(t14, 1024); (t38, 1024); (tv, 1024)] ((bufs1, wpls * 4) :: rt_live RT Σ) ART0
                ltac:(rewrite LVX; reflexivity) ltac:(cbn [app]; do 4 right; exact PDIN)) as AP_B2_P.
  assert (NC_B1 : forall a, PF a -> a < bufs1 \/ bufs1 + wpls * 4 <= a).
  { intros a Ha. apply (inner_chunk_apart RT AF ΣX mh bufs1 (wpls * 4) (rt_live RT Σ) (rt_frames RT Σ) sa a ART0 B1IN).
    - intros e He. split; [exact (LSUBX e He)| exact (proj1 (FRESH5 e He))].
    - rewrite FRSX, <- FRS. intros e He; exact He.
    - rewrite SP0X. unfold STACK_WIN. clear - LOW LOR; lia.
    - exact (proj1 Ha). }
  assert (NC_B2 : forall a, PF a -> a < bufs2 \/ bufs2 + wpls * 4 <= a).
  { intros a Ha. apply (inner_chunk_apart RT AF ΣX mh bufs2 (wpls * 4) (rt_live RT Σ) (rt_frames RT Σ) sa a ART0 B2IN).
    - intros e He. split; [exact (LSUBX e He)| exact (proj1 (proj2 (FRESH5 e He)))].
    - rewrite FRSX, <- FRS. intros e He; exact He.
    - rewrite SP0X. unfold STACK_WIN. clear - LOW LOR; lia.
    - exact (proj1 Ha). }
  (* [comment removed for export] *)
  assert (PFR : forall a, PF a -> d2r_keep (rt_live RT ΣX) (rt_frames RT ΣX) sa dat rd bufs1 bufs2 (wpls * 4) a).
  { intros a Ha. pose proof (NC_B1 a Ha) as N1. pose proof (NC_B2 a Ha) as N2. destruct Ha as [Ha1 Ha2]. split.
    - apply (aclient_mono _ _ sa _ _ _ _ Ha1); [exact LSUBX| rewrite FRSX, FRS; intros e He; exact He| clear; lia].
    - unfold d2m_W in Ha2. cbn [outside] in Ha2 |- *. clear - Ha2 N1 N2. lia. }
  assert (PFC : forall a, PF a -> d2cm_keep (rt_live RT Σ) (rt_frames RT ΣX) sa pixd a).
  { intros a [Ha1 Ha2]. split.
    - apply (aclient_mono _ _ sa _ _ _ _ Ha1); [intros e He; exact He| rewrite FRSX, FRS; intros e He; exact He| clear; lia].
    - unfold d2m_W in Ha2. cbn [outside] in Ha2 |- *. clear - Ha2. lia. }
  split_at FRLO 1%nat FRLO2.
  idtac "MARK mid2: setup".
  (* [comment removed for export] *)
  destruct TABS as (TA & TAL & T38 & T38L & T14 & T14L).
  eapply cps_seq with (Q := d2f_post RT ΣX PMc gp (Z_to_bv 64 usp) (Z_to_bv 64 fr) (Z_to_bv 64 (fr / 8 + 2147450880)) s10 s11
                              sa lo dat rd datas rs bufs1 bufs2 (wpls * 4) wpls wpld w h tv t38 t14 mh).
  { eapply (d2_finish RT AF GP RC ΣX PMc mh mh) with (lo := lo) (rd := rd) (datas := datas) (rs := rs) (n1 := wpls * 4) (wpld := wpld) (w := w)
                                                    (ta := tv) (t38 := t38) (t14 := t14) (tw := tw) (t38w := t38w) (t14w := t14w).
    all: lazymatch goal with
         | |- fdfs_only _ => exact FDO
         | |- mat_stable _ => exact MST
         | |- d2r_geom _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rewrite SP0X; exact DGEOM
         | |- In _ (rt_live _ _) => first [exact DDINX | exact DSINX | exact B1IN | exact B2IN | exact TVIN | exact T8IN | exact T4IN]
         | |- ART _ _ _ => exact ART0
         | |- mem_inv _ _ => exact MI
         | |- stk _ _ _ _ => exact ST
         | |- LIBH _ => exact LH
         | |- io_ssp _ => exact SSP
         | |- rw_cells _ _ _ [_] => exact FRLO
         | |- rw_cells _ _ _ (d2r_frame _ _ _ _ _ _ _ _ _) => exact FR56
         | |- d2r_tabs _ _ _ _ _ _ _ => split; [exact TA| split; [exact TAL| split; [exact T38| split; [exact T38L| split; [exact T14| exact T14L]]]]]
         | |- Forall _ _ => exact TS8
         | |- wmono _ _ _ => apply wmono_refl
         | |- agree_on _ _ _ => apply agree_refl
         | |- ?g => idtac "LEFT d2_finish:" g
         end. }
  idtac "MARK mid2: d2_finish applied".
  cps_open RT.
  lazymatch goal with Hx : ART RT ΣX ?m2 /\ _ |- _ =>
    destruct Hx as (ART2 & MI2 & ST2 & LH2 & SSP2 & FR2 & WM2 & AG2) end.
  (* [comment removed for export] *)
  lazymatch type of AG2 with agree_on _ mh ?m2 =>
    assert (UREC2 : rw_cells asegs m2 (usp + -16) [C8 (Z_to_bv 64 fp1); C8 (Z_to_bv 64 RA_FUZZ_OP1)])
      by (apply (rw_cells_agree_nw asegs mh m2 _ _ UREC); eapply agree_sub; [exact AG2|]; cbv beta; intros zx Hzx; cbn in Hzx;
          split; [left; unfold USTACK_TOP; clear - Hzx SAU SPT; lia| cbn [outside]; clear - Hzx SAU CKR2 CKR_B1 CKR_B2 LOW LOR; lia]);
    idtac end.
  (* [comment removed for export] *)
  pose proof (af_frames_range RT AF ΣX mh fr 2%nat ART0 ltac:(rewrite FRSX; left; reflexivity)) as (_ & _ & _ & FAP). change (fs_size 2%nat) with 256 in FAP.
  pose proof (FAP bufs1 (wpls * 4) B1IN) as FAB1. pose proof (FAP bufs2 (wpls * 4) B2IN) as FAB2. clear FAP.
  lazymatch type of AG2 with agree_on _ mh ?m2 =>
    assert (FRLO' : rw_cells asegs m2 (sa + 16) [C8 (Z_to_bv 64 (h - 1))])
      by (apply (rw_cells_agree_nw asegs mh m2 _ _ FRLO); eapply agree_sub; [exact AG2|]; cbv beta; intros zx Hzx; cbn in Hzx;
          split; [left; unfold USTACK_TOP; clear - Hzx SAU SPT; lia| cbn [outside]; clear - Hzx SAU CKR2 CKR_B1 CKR_B2 LOW LOR; lia]);
    assert (FRLO2' : rw_cells asegs m2 (sa + 24) [C8 (Z_to_bv 64 (fr + 80)); C8 (Z_to_bv 64 1)])
      by (apply (rw_cells_agree_nw asegs mh m2 _ _ FRLO2); eapply agree_sub; [exact AG2|]; cbv beta; intros zx Hzx; cbn in Hzx;
          split; [left; unfold USTACK_TOP; clear - Hzx SAU SPT; lia| cbn [outside]; clear - Hzx SAU CKR2 CKR_B1 CKR_B2 LOW LOR; lia]);
    assert (C48' : rw_cells asegs m2 (sa + 48) [C8 (Z_to_bv 64 (fr + 112))])
      by (apply (rw_cells_agree_nw asegs mh m2 _ _ C48); eapply agree_sub; [exact AG2|]; cbv beta; intros zx Hzx; cbn in Hzx;
          split; [left; unfold USTACK_TOP; clear - Hzx SAU SPT; lia| cbn [outside]; clear - Hzx SAU CKR2 CKR_B1 CKR_B2 LOW LOR; lia]);
    assert (J128' : rw_cells asegs m2 (sa + 128) [CB 16 j128])
      by (apply (rw_cells_agree_nw asegs mh m2 _ _ J128); eapply agree_sub; [exact AG2|]; cbv beta; intros zx Hzx; cbn in Hzx;
          split; [left; unfold USTACK_TOP; clear - Hzx SAU SPT; lia| cbn [outside]; clear - Hzx SAU CKR2 CKR_B1 CKR_B2 LOW LOR; lia]);
    assert (FPD' : rw_cells asegs m2 (fr + 112) [C8 (Z_to_bv 64 pixd)])
      by (apply (rw_cells_agree_nw asegs mh m2 _ _ FPD); eapply agree_sub; [exact AG2|]; cbv beta; intros zx Hzx; cbn in Hzx;
          split; [right; right; right; left; exists fr, 2%nat; split; [rewrite FRSX; left; reflexivity| change (fs_size 2%nat) with 256; clear - Hzx; lia]
                | cbn [outside]; clear - Hzx FCD2 FAB1 FAB2; lia]);
    assert (PXD' : rw_cells asegs m2 pixd (pix_cells vd))
      by (apply (rw_cells_agree_nw asegs mh m2 _ _ PXD); eapply agree_sub; [exact AG2|]; cbv beta; intros zx Hzx;
          unfold pix_cells in Hzx; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Hzx;
          split; [right; right; left; exists pixd, 64; split; [exact PDINX| clear - Hzx; lia] | cbn [outside]; clear - Hzx APPD AP_B1_P AP_B2_P; lia]);
    assert (UCX' : chain_ok m2 usp fp1 [RA_TOP])
      by (apply (chain_ok_keep [RA_TOP] mh m2 usp fp1 UCX); eapply agree_sub; [exact AG2|]; cbv beta; intros zx Hzx; unfold USTACK_TOP in Hzx;
          split; [left; unfold USTACK_TOP; clear - Hzx SAU; lia| cbn [outside]; clear - Hzx SAU CKR2 CKR_B1 CKR_B2 LOW LOR; lia])
  end.
  clear UREC FRLO FRLO2 C48 J128 FPD PXD UCX.
  idtac "MARK mid2: carried over the last row".
  (* [comment removed for export] *)
  pose proof FR2 as F112. unfold d2r_frame in F112. split_at F112 7%nat F112b. split_at F112b 2%nat F128x. clear F112 F128x.
  pose proof FRLO2' as C32. split_at C32 1%nat C32b. clear C32.
  lazymatch type of AG2 with agree_on _ mh ?m2 =>
    eapply cps_seq with (Q := d2cm_post RT ΣX PMc gp sa usp lo fr pixd vd (rt_live RT Σ) m2) end.
  { pose proof CMF as CM. unfold d2_cmfree_cps in CM.
    lazymatch type of AG2 with agree_on _ mh ?m2 =>
    eapply (CM ΣX PMc m2) with (lo := lo) (L0 := rt_live RT Σ) (frs0 := frs0) (n1 := wpls * 4) (vd := vd) (fp1 := fp1)
                                (bufs1 := bufs1) (bufs2 := bufs2) (tv := tv) (t38 := t38) (t14 := t14) (pixd := pixd) (fr := fr) (sa := sa) (usp := usp) end.
    (* [comment removed for export] *)
    all: first [ exact FDO | exact MST | exact LVX | exact FRSX | exact LVP | exact FRESH5 | exact ND5 | exact PDIN | exact VCM | exact FP1 | exact UCX'
               | exact STa | exact SA32 | exact SAU | exact USA | exact SPA | exact FR0 | exact FR64
               | exact ART2 | exact MI2 | exact ST2 | exact LH2 | exact SSP2 | exact UREC2 | exact FPD' | exact C32b | exact C48' | exact F112b
               | solve [clear - WPLS; lia]
               | solve [rewrite LVX; cbn [length]; clear - LVB; lia]
               | solve [rewrite FRSX; rewrite FRS in FRB; exact FRB]
               | solve [rewrite CRX; clear - CRB; lia]
               | solve [rewrite VDAT; unfold rsize; rewrite VWPL, VH, <- ERD; exact DDIN]
               | solve [rewrite VDAT; clear - DD0; lia]
               | solve [rewrite SP0X; unfold STACK_WIN; clear - LOW FRHI SPB; lia]
               | solve [unfold LSTK, STDERR_STACK, RT_STACK; clear - LOR; lia]
               | solve [unfold USTACK_TOP; clear - SPT; lia]
               | solve [split; [exact PXD'|]; split; [split; [exact PDINX| split; [exact PD0| split; [exact PD16| clear; lia]]]|]; split; [exact HOKD|];
                        split; [right; rewrite VDAT; unfold rsize; rewrite VWPL, VH, <- ERD; split; [split; [exact DDINX| split; [exact DD0| split; [exact DD16| exact RD0]]]| unpark APPD; clear - APPD RD0; lia]
                              | left; exact VCM]]
               | match goal with |- ?g => idtac "LEFT cmfree:" g end ]. }
  idtac "MARK mid2: cmfree applied".
  clear UREC2 C32b F112b.
  cps_open RT.
  lazymatch goal with Hx : ART RT ?S3 ?m3 /\ _ |- _ =>
    destruct Hx as (ART3 & MI3 & ST3 & LH3 & SSP3 & LV3 & FRS3 & SP03 & CR3 & CMO & CM0 & CA0 & CMNE & FRESHC & NCC & PXD3 & AG3) end.
  idtac "MARK mid2: cmfree opened".
  (* [comment removed for export] *)
  lazymatch type of AG3 with agree_on _ ?m2 ?m3 =>
    assert (FRLO3 : rw_cells asegs m3 (sa + 16) [C8 (Z_to_bv 64 (h - 1))])
      by (apply (rw_cells_agree_nw asegs m2 m3 _ _ FRLO'); eapply agree_sub; [exact AG3|]; cbv beta; intros zx Hzx; cbn in Hzx;
          split; [left; unfold USTACK_TOP; clear - Hzx SAU SPT; lia| cbn [outside]; clear - Hzx CKR1 LOW LOR; lia]);
    assert (FRLO23 : rw_cells asegs m3 (sa + 24) [C8 (Z_to_bv 64 (fr + 80)); C8 (Z_to_bv 64 1)])
      by (apply (rw_cells_agree_nw asegs m2 m3 _ _ FRLO2'); eapply agree_sub; [exact AG3|]; cbv beta; intros zx Hzx; cbn in Hzx;
          split; [left; unfold USTACK_TOP; clear - Hzx SAU SPT; lia| cbn [outside]; clear - Hzx CKR1 LOW LOR; lia]);
    assert (FR563 : rw_cells asegs m3 (sa + 56) (d2r_frame w wpls datas wpld dat tv t38 t14 z64))
      by (apply (rw_cells_agree_nw asegs m2 m3 _ _ FR2); eapply agree_sub; [exact AG3|]; cbv beta; intros zx Hzx;
          unfold d2r_frame in Hzx; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Hzx;
          split; [left; unfold USTACK_TOP; clear - Hzx SAU SPT; lia| cbn [outside]; clear - Hzx CKR1 LOW LOR; lia]);
    assert (J1283 : rw_cells asegs m3 (sa + 128) [CB 16 j128])
      by (apply (rw_cells_agree_nw asegs m2 m3 _ _ J128'); eapply agree_sub; [exact AG3|]; cbv beta; intros zx Hzx; cbn in Hzx;
          split; [left; unfold USTACK_TOP; clear - Hzx SAU SPT; lia| cbn [outside]; clear - Hzx CKR1 LOW LOR; lia])
  end.
  idtac "MARK mid2: carried over the tail".
  apply cps_finish. intros c Hc. subst QF. unfold d2m_post. cbv beta.
  lazymatch type of Hc with ASTA RT ?S3 PMc (eq (MS _ _ _ _ _ ?m3 _)) c =>
    lazymatch goal with CMOx : cmap_obj _ m3 ?cmap {| c_arr := ?carr; c_depth := _; c_nalloc := _; c_n := _ |} |- _ => exists S3, m3, cmap, carr end end.
  do 25 eexists. split; [exact Hc|].
  split; [exact ART3|]. split; [exact MI3|]. split; [exact ST3|]. split; [exact LH3|]. split; [exact SSP3|].
  split; [exact LV3|]. split; [rewrite FRS3, FRSX, FRS; reflexivity|]. split; [rewrite SP03, SP0X; reflexivity|].
  split; [rewrite <- CRX; exact CR3|].
  split; [exact CMO|]. split; [exact CM0|]. split; [exact CA0|]. split; [exact CMNE|].
  split; [intros e He; exact (FRESHC e (LSUBX e He))|].
  split; [intros a Ha; apply NCC; destruct Ha as [Ha1 _]; apply (aclient_mono _ _ sa _ _ _ _ Ha1); [exact LSUBX| rewrite FRSX, FRS; intros e He; exact He| clear; lia]|].
  split; [exact PXD3|].
  pose proof FRLO23 as C24. split_at C24 1%nat C24b.
  split; [exact C24|].
  split.
  { lazymatch type of FRLO3 with rw_cells _ ?m3 _ _ => apply (proj2 (wr_at_app m3 (sa + 16) 8 16 ltac:(clear; lia) ltac:(clear; lia))) end. split.
    - apply (rw_cells_wr_at asegs _ _ _ 8 FRLO3). cbn. clear; lia.
    - replace (sa + 16 + 8) with (sa + 24) by (clear; lia). apply (rw_cells_wr_at asegs _ _ _ 16 FRLO23). cbn. clear; lia. }
  split.
  { lazymatch type of FR563 with rw_cells _ ?m3 _ _ => apply (proj2 (wr_at_app m3 (sa + 56) 72 16 ltac:(clear; lia) ltac:(clear; lia))) end. split.
    - apply (rw_cells_wr_at asegs _ _ _ 72 FR563). unfold d2r_frame. cbn. clear; lia.
    - replace (sa + 56 + 72) with (sa + 128) by (clear; lia). apply (rw_cells_wr_at asegs _ _ _ 16 J1283). cbn. clear; lia. }
  lazymatch type of AG3 with agree_on _ ?m2 ?m3 =>
    apply (agree_trans PF m0 mh m3 AG0);
    apply (agree_trans PF mh m2 m3); [exact (agree_sub _ _ _ _ AG2 PFR)| exact (agree_sub _ _ _ _ AG3 PFC)] end.
Qed.
Lemma d2_mid : forall (Σ : rts RT) PMc (m : mem)
    (ra gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (sa usp lo fr pixd dat rd datas rs wpls wpld w h fp1 : Z) (vd : pixv) (frs0 : list (Z * nat)) (j56 j80 j112 : list byte),
  fdfs_only PMc -> mat_stable PMc ->
  d2m_geom (rt_sp0 RT Σ) lo sa usp fr pixd dat rd datas rs wpls wpld w h ->
  pix_obj (rt_live RT Σ) m pixd vd (mkCmapv 0 0 0 0) ->
  p_w vd = w -> p_h vd = h -> p_d vd = 2 -> p_wpl vd = wpld -> p_data vd = dat -> p_cmap vd = 0 ->
  In (datas, rs) (rt_live RT Σ) -> rt_frames RT Σ = (fr, 2%nat) :: frs0 ->
  Z.of_nat (length (rt_live RT Σ)) + 7 <= LIVE_MAX -> Z.of_nat (length (rt_frames RT Σ)) + 3 <= Z.of_nat FRAMES_MAX -> 8 <= rt_credit RT Σ ->
  (forall p n, In (p, n) (rt_live RT Σ) -> 0 < n) ->
  0 <= fp1 < 2^64 -> chain_ok m usp fp1 [RA_TOP] ->
  ART RT Σ m -> mem_inv asegs m -> stk asegs m lo sa -> LIBH m -> io_ssp m ->
  rw_cells asegs m (usp + -16) [C8 (Z_to_bv 64 fp1); C8 (Z_to_bv 64 RA_FUZZ_OP1)] ->
  wr_at asegs m (sa + 16) 24 ->
  rw_cells asegs m (sa + 48) [C8 (Z_to_bv 64 (fr + 112))] ->
  rw_cells asegs m (sa + 56) [CB 8 j56; C8 (Z_to_bv 64 wpld); C8 (Z_to_bv 64 dat); CB 8 j80; C8 (Z_to_bv 64 (fr + 48)); C8 (Z_to_bv 64 (fr + 32)); C8 (Z_to_bv 64 datas); CB 32 j112] ->
  rw_cells asegs m (fr + 32) [C4 (Z_to_bv 64 w)] -> rw_cells asegs m (fr + 48) [C4 (Z_to_bv 64 h)] -> rw_cells asegs m (fr + 112) [C8 (Z_to_bv 64 pixd)] ->
  cps asegs (ASTA RT Σ PMc (eq (MS (mkR ra (Z_to_bv 64 sa) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 sa) (Z_to_bv 64 wpls) a1 a2 a3 a4 a5 a6 a7
                                        (Z_to_bv 64 fr) (Z_to_bv 64 SHB) (Z_to_bv 64 (fr + 80)) (Z_to_bv 64 pixd) (Z_to_bv 64 5) (Z_to_bv 64 5) (Z_to_bv 64 wpls)
                                        (Z_to_bv 64 (fr / 8 + 2147450880)) (Z_to_bv 64 (fr + 80)) ONE t3 t4 t5 t6)
                                   F (Z_to_bv 64 0x9f804) (frm_clear fc) None m (seg_rom asegs))))
    (d2m_post Σ PMc gp sa usp lo fr pixd dat rd vd m).
Proof using AF GP RC CML SCM CMF.
  intros Σ PMc m ra gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc sa usp lo fr pixd dat rd datas rs wpls wpld w h fp1 vd frs0 j56 j80 j112
    FDO MST GEOM POD VW VH VD VWPL VDAT VCM DSIN FRS LVB FRB CRB LVP FP1 UCX ART0 MI ST LH SSP UREC WLO C48 FRBLK FW FH FPD.
  pose proof GEOM as (HW & HH & EWS & EWD & ERS & ERD & RS64 & DD0 & DD16 & CKR2 & CKS2 & CKH2 & DS0 & DS16 & CKR0 & CKS0 & CKH0
                      & PD0 & PD16 & CKR1 & CKS1 & CKH1 & APDS & APPD & APPS & FR0 & FR64 & FRHI & FRSEG & FRSH & FCD2 & FCD0 & FCD1
                      & LOW & STa & LOR & SA32 & SAU & USA & SPA & SPT & SPB & SP0R & SP0W).
  assert (WPLS : 0 < wpls <= 5001) by (rewrite EWS; clear - HW; Z.div_mod_to_equations; lia).
  assert (WPLD : 0 < wpld <= 1251) by (rewrite EWD; clear - HW; Z.div_mod_to_equations; lia).
  assert (WDS : wpld <= wpls /\ w <= 4 * wpls /\ w <= 16 * wpld) by (rewrite EWS, EWD; clear - HW; Z.div_mod_to_equations; lia).
  assert (RSB : 0 < rd <= rs) by (rewrite ERS, ERD; clear - HH WPLS WPLD WDS; nia).
  assert (SZ : hid (0 < wpls <= 5001 /\ 0 < wpld <= 1251 /\ wpld <= wpls /\ w <= 4 * wpls /\ w <= 16 * wpld /\ 0 < rd <= rs /\ rs <= 67108864
                    /\ rs = 4 * (wpls * h) /\ rd = 4 * (wpld * h) /\ 0 < w <= 20000 /\ 0 < h <= 20000)) by (unfold hid; clear - WPLS WPLD WDS RSB RS64 ERS ERD HW HH; tauto).
  assert (SP0H : hid (rt_sp0 RT Σ <= 2^47)) by (unfold hid; clear - SP0R; unfold USTACK_TOP in SP0R; lia).
  assert (SA16 : sa mod 16 = 0) by (clear - SA32; Z.div_mod_to_equations; lia).
  assert (FP1h : hid (0 <= fp1 < 2^64)) by exact FP1. clear FP1.   (* [comment removed for export] *)
  pose proof POD as (PXD & (PDIN & _ & _ & _) & HOKD & PDDATA & _).
  destruct PDDATA as [PDZ|((DDIN & _ & _ & DDN) & DDNE)]; [exfalso; rewrite VDAT in PDZ; clear - PDZ DD0; lia|].
  rewrite VDAT in DDIN, DDNE. unfold rsize in DDIN, DDN. rewrite VWPL, VH, <- ERD in DDIN, DDN.
  unfold pix_cells in PXD. rewrite VW, VH, VD, VWPL, VDAT, VCM in PXD.
  hide POD. hide HOKD.
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  unfold LSTK, STDERR_STACK in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  set (PF := d2m_keep (rt_live RT Σ) (rt_frames RT Σ) sa dat rd pixd).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> sa <= a \/ a < lo).
  { intros a [Ha _]. destruct (aclient_split RT AF Σ m sa a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; clear - H LOW; lia]. }
  assert (USP0 : 0 <= sa) by (clear - LOR STa; lia). assert (USP1 : sa < 2^64) by (unfold hid in SP0H; clear - SPB SAU SP0H; lia).
  (* [comment removed for export] *)
  assert (PFU : forall a, usp + -16 <= a < 140737488355328 -> PF a).
  { intros a Ha. unfold PF, d2m_keep. split; [left; unfold USTACK_TOP; clear - Ha SAU; lia|]. unfold d2m_W. cbn [outside]. clear - Ha SAU CKR2 CKR1 LOW LOR SPB. lia. }
  destruct (wr_at_rw_CB m (sa + 16) 24 WLO ltac:(clear; lia)) as [jlo FRLO]. change (Z.to_nat 24) with 24%nat in FRLO. clear WLO.
  clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
  idtac "MARK mid: setup".
  (* [comment removed for export] *)
  walk_to AF MST (@nil (Z * Z)) [e_calloc; 0x9ffc0].
  idtac "MARK mid: at calloc 1".
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; left; ul| exact I]])
                ltac:(fun Hx => let Hx2 := fresh "Ho" in pose proof (proj2 Hx) as Hx2; unfold d2m_W in Hx2; cbn [outside] in Hx2 |- *; clear - Hx2; lia).
  lazymatch goal with UR : rw_cells asegs ?mc (usp + -16) _ |- cps _ (ASTA RT _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
    assert (UCC : chain_ok mc sa usp [RA_FUZZ_OP1; RA_TOP])
      by (apply (chain_ok_push mc sa usp RA_FUZZ_OP1 fp1 [RA_TOP]);
            [ clear - SAU; lia | clear - SPA; Z.div_mod_to_equations; lia | unfold USTACK_TOP; clear - SPT; lia | unfold RA_FUZZ_OP1; clear; lia | let X := fresh "X" in pose proof FP1h as X; unfold hid in X; exact X | exact UR
            | apply (chain_ok_keep [RA_TOP] m _ usp fp1 UCX); eapply agree_sub; [exact AGF|]; cbv beta; intros zx Hzx; apply PFU; unfold USTACK_TOP in Hzx; clear - Hzx; lia ]) end.
  assert (TRc : In (0x9f80c :: [RA_FUZZ_OP1; RA_TOP]) CLIENT_TRACES) by (unfold RA_FUZZ_OP1, RA_TOP; apply ct_mem_In; vm_compute; reflexivity).
  eapply cps_seq.
  { pose proof (gp_calloc RT GP) as CC; unfold calloc_contract in CC; eapply CC with (lo := lo) (nmemb := wpls) (size := 4); rt_side idtac.
    all: lazymatch goal with
         | |- unwind_okC _ _ _ _ => exists [RA_FUZZ_OP1; RA_TOP]; rewrite ?unsigned_lit by (clear - USP0 USP1 SAU SPT; lia); split; [exact UCC| exact TRc]
         | |- _ => first [ unfold CALLOC_MAX; let X := fresh "X" in pose proof SZ as X; unfold hid in X; clear - X; lia
                         | unfold LIVE_MAX in *; clear - LVB; lia
                         | lazymatch goal with |- ?g => idtac "LEFT:" g end ]
         end. }
  idtac "MARK mid: calloc 1 applied".
  clear UCC TRc.
  after_call RT AF.
  fold_ag ltac:(fun Hx => apply (aclient_mono _ _ sa _ _ _ _ (proj1 Hx)); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| clear; lia]).
  idtac "MARK mid: after calloc 1".
  lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σb1; rename A into ARTb1 end.
  lazymatch goal with H : rt_live RT Σb1 = (?p, _) :: _ |- _ => rename H into LVb1N; rename p into bufs1 end.
  lazymatch goal with H : rw_cells asegs _ bufs1 [CB _ _] |- _ => rename H into Zbufs1 end.
  assert (FRSb1 : rt_frames RT Σb1 = (fr, 2%nat) :: frs0) by (repeat match goal with E : rt_frames RT Σb1 = _ |- _ => rewrite E end; first [exact FRS | assumption]).
  assert (SP0b1 : rt_sp0 RT Σb1 = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 RT Σb1 = _ |- _ => rewrite E end; first [reflexivity | assumption]).
  assert (CRb1 : rt_credit RT Σb1 = rt_credit RT Σ) by (repeat match goal with E : rt_credit RT Σb1 = _ |- _ => rewrite E end; first [reflexivity | assumption]).
  lazymatch goal with H : 0 < bufs1 |- _ => rename H into B10 end.
  lazymatch goal with H : bufs1 mod 16 = 0 |- _ => rename H into B116 end.
  lazymatch goal with A : ART RT Σb1 ?mm |- _ => pose proof (af_live_disj RT AF Σb1 mm bufs1 (wpls * 4) (dat) (rd) [] _ A LVb1N ltac:(cbn [app]; solve [in_live_tac])) as AP_B1_D end.
  lazymatch goal with A : ART RT Σb1 ?mm |- _ => pose proof (af_live_disj RT AF Σb1 mm bufs1 (wpls * 4) (datas) (rs) [] _ A LVb1N ltac:(cbn [app]; solve [in_live_tac])) as AP_B1_S end.
  lazymatch goal with A : ART RT Σb1 ?mm |- _ => pose proof (af_live_disj RT AF Σb1 mm bufs1 (wpls * 4) (pixd) (64) [] _ A LVb1N ltac:(cbn [app]; solve [in_live_tac])) as AP_B1_P end.
  (* [comment removed for export] *)
  lazymatch goal with A : ART RT Σb1 ?mm |- _ =>
    assert (NE_B1 : forall e, In e (rt_live RT Σ) -> fst e <> bufs1)
      by (intros e He; apply (fresh_chunk_ne RT AF Σb1 mm [] bufs1 (wpls * 4) _ e A LVb1N); [cbn [app]; exact He | let X := fresh "X" in pose proof SZ as X; unfold hid in X; clear - X; lia | destruct e as [eq ek]; exact (LVP eq ek He)]);
    assert (SUB_B1 : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σb1) /\ fst e <> bufs1)
      by (intros e He; split; [rewrite LVb1N; right; exact He | exact (NE_B1 e He)]);
    assert (NC_B1 : forall a, PF a -> a < bufs1 \/ bufs1 + wpls * 4 <= a)
      by (intros a Ha; apply (inner_chunk_apart RT AF Σb1 mm bufs1 (wpls * 4) (rt_live RT Σ) (rt_frames RT Σ) sa a A ltac:(rewrite LVb1N; left; reflexivity) SUB_B1);
          [ rewrite FRSb1, <- FRS; intros e He; exact He | rewrite SP0b1; unfold STACK_WIN; clear - LOW LOR; lia | exact (proj1 Ha) ]) end.

  assert (LVB1 : rt_live RT Σb1 = (bufs1, wpls * 4) :: rt_live RT Σ) by (rewrite LVb1N; reflexivity).
  chunk_facts RT AF GP bufs1 (wpls * 4). fframe_chunk RT AF fr 2%nat 256 bufs1 (wpls * 4).
  lazymatch goal with H : bufs1 + _ <= rt_sp0 RT _ - _ |- _ => rename H into CKR_B1 end.
  lazymatch goal with H : bufs1 + _ <= 65536 \/ _ <= bufs1 |- _ => rename H into CKS_B1 end.
  lazymatch goal with H : bufs1 + _ <= 2147446784 \/ _ <= bufs1 |- _ => rename H into CKH_B1 end.
  lazymatch goal with H : fr + 256 <= bufs1 \/ bufs1 + _ <= fr |- _ => rename H into FCD_B1 end.
  lazymatch goal with H : bufs1 + _ <= fr / 8 + _ \/ _ <= bufs1 |- _ => rename H into FCS_B1 end.
  clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
  walk_to AF MST [(sa + 16, sa + 40); (sa + 56, sa + 144)] [e_calloc; 0x9ffc0].
  idtac "MARK mid: at calloc 2".
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; left; ul| exact I]])
                ltac:(fun Hx => let Hx2 := fresh "Ho" in pose proof (proj2 Hx) as Hx2; unfold d2m_W in Hx2; cbn [outside] in Hx2 |- *; clear - Hx2; lia).
  lazymatch goal with UR : rw_cells asegs ?mc (usp + -16) _ |- cps _ (ASTA RT _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
    assert (UCC : chain_ok mc sa usp [RA_FUZZ_OP1; RA_TOP])
      by (apply (chain_ok_push mc sa usp RA_FUZZ_OP1 fp1 [RA_TOP]);
            [ clear - SAU; lia | clear - SPA; Z.div_mod_to_equations; lia | unfold USTACK_TOP; clear - SPT; lia | unfold RA_FUZZ_OP1; clear; lia | let X := fresh "X" in pose proof FP1h as X; unfold hid in X; exact X | exact UR
            | apply (chain_ok_keep [RA_TOP] m _ usp fp1 UCX); eapply agree_sub; [exact AGF|]; cbv beta; intros zx Hzx; apply PFU; unfold USTACK_TOP in Hzx; clear - Hzx; lia ]) end.
  assert (TRc : In (0x9f820 :: [RA_FUZZ_OP1; RA_TOP]) CLIENT_TRACES) by (unfold RA_FUZZ_OP1, RA_TOP; apply ct_mem_In; vm_compute; reflexivity).
  eapply cps_seq.
  { pose proof (gp_calloc RT GP) as CC; unfold calloc_contract in CC; eapply CC with (lo := lo) (nmemb := wpls) (size := 4); rt_side idtac.
    all: lazymatch goal with
         | |- unwind_okC _ _ _ _ => exists [RA_FUZZ_OP1; RA_TOP]; rewrite ?unsigned_lit by (clear - USP0 USP1 SAU SPT; lia); split; [exact UCC| exact TRc]
         | |- _ => first [ unfold CALLOC_MAX; let X := fresh "X" in pose proof SZ as X; unfold hid in X; clear - X; lia
                         | rewrite LVB1; cbn [length]; unfold LIVE_MAX in *; clear - LVB; lia
                         | lazymatch goal with |- ?g => idtac "LEFT:" g end ]
         end. }
  idtac "MARK mid: calloc 2 applied".
  clear UCC TRc.
  after_call RT AF.
  fold_ag ltac:(fun Hx => apply (aclient_mono _ _ sa _ _ _ _ (proj1 Hx)); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| clear; lia]).
  idtac "MARK mid: after calloc 2".
  lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σb2; rename A into ARTb2 end.
  lazymatch goal with H : rt_live RT Σb2 = (?p, _) :: _ |- _ => rename H into LVb2N; rename p into bufs2 end.
  lazymatch goal with H : rw_cells asegs _ bufs2 [CB _ _] |- _ => rename H into Zbufs2 end.
  assert (FRSb2 : rt_frames RT Σb2 = (fr, 2%nat) :: frs0) by (repeat match goal with E : rt_frames RT Σb2 = _ |- _ => rewrite E end; first [exact FRS | assumption]).
  assert (SP0b2 : rt_sp0 RT Σb2 = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 RT Σb2 = _ |- _ => rewrite E end; first [reflexivity | assumption]).
  assert (CRb2 : rt_credit RT Σb2 = rt_credit RT Σ) by (repeat match goal with E : rt_credit RT Σb2 = _ |- _ => rewrite E end; first [reflexivity | assumption]).
  lazymatch goal with H : 0 < bufs2 |- _ => rename H into B20 end.
  lazymatch goal with H : bufs2 mod 16 = 0 |- _ => rename H into B216 end.
  lazymatch goal with A : ART RT Σb2 ?mm |- _ => pose proof (af_live_disj RT AF Σb2 mm bufs2 (wpls * 4) (dat) (rd) [] _ A LVb2N ltac:(cbn [app]; solve [in_live_tac])) as AP_B2_D end.
  lazymatch goal with A : ART RT Σb2 ?mm |- _ => pose proof (af_live_disj RT AF Σb2 mm bufs2 (wpls * 4) (datas) (rs) [] _ A LVb2N ltac:(cbn [app]; solve [in_live_tac])) as AP_B2_S end.
  lazymatch goal with A : ART RT Σb2 ?mm |- _ => pose proof (af_live_disj RT AF Σb2 mm bufs2 (wpls * 4) (pixd) (64) [] _ A LVb2N ltac:(cbn [app]; solve [in_live_tac])) as AP_B2_P end.
  lazymatch goal with A : ART RT Σb2 ?mm |- _ => pose proof (af_live_disj RT AF Σb2 mm bufs2 (wpls * 4) (bufs1) (wpls * 4) [] _ A LVb2N ltac:(cbn [app]; solve [in_live_tac])) as AP_B2_B1 end.
  (* [comment removed for export] *)
  lazymatch goal with A : ART RT Σb2 ?mm |- _ =>
    assert (NE_B2 : forall e, In e (rt_live RT Σ) -> fst e <> bufs2)
      by (intros e He; apply (fresh_chunk_ne RT AF Σb2 mm [] bufs2 (wpls * 4) _ e A LVb2N); [cbn [app]; rewrite LVB1; right; exact He | let X := fresh "X" in pose proof SZ as X; unfold hid in X; clear - X; lia | destruct e as [eq ek]; exact (LVP eq ek He)]);
    assert (SUB_B2 : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σb2) /\ fst e <> bufs2)
      by (intros e He; split; [rewrite LVb2N; right; rewrite LVB1; right; exact He | exact (NE_B2 e He)]);
    assert (NC_B2 : forall a, PF a -> a < bufs2 \/ bufs2 + wpls * 4 <= a)
      by (intros a Ha; apply (inner_chunk_apart RT AF Σb2 mm bufs2 (wpls * 4) (rt_live RT Σ) (rt_frames RT Σ) sa a A ltac:(rewrite LVb2N; left; reflexivity) SUB_B2);
          [ rewrite FRSb2, <- FRS; intros e He; exact He | rewrite SP0b2; unfold STACK_WIN; clear - LOW LOR; lia | exact (proj1 Ha) ]) end.

  assert (LVB2 : rt_live RT Σb2 = (bufs2, wpls * 4) :: (bufs1, wpls * 4) :: rt_live RT Σ) by (rewrite LVb2N, LVB1; reflexivity).
  chunk_facts RT AF GP bufs2 (wpls * 4). fframe_chunk RT AF fr 2%nat 256 bufs2 (wpls * 4).
  lazymatch goal with H : bufs2 + _ <= rt_sp0 RT _ - _ |- _ => rename H into CKR_B2 end.
  lazymatch goal with H : bufs2 + _ <= 65536 \/ _ <= bufs2 |- _ => rename H into CKS_B2 end.
  lazymatch goal with H : bufs2 + _ <= 2147446784 \/ _ <= bufs2 |- _ => rename H into CKH_B2 end.
  lazymatch goal with H : fr + 256 <= bufs2 \/ bufs2 + _ <= fr |- _ => rename H into FCD_B2 end.
  lazymatch goal with H : bufs2 + _ <= fr / 8 + _ \/ _ <= bufs2 |- _ => rename H into FCS_B2 end.
  clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
  (* [comment removed for export] *)
  walk_to AF MST [(sa + 16, sa + 40); (sa + 56, sa + 144)] [e_calloc; 0x9ffc0].
  idtac "MARK mid: at calloc 3".
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; left; ul| exact I]])
                ltac:(fun Hx => let Hx2 := fresh "Ho" in pose proof (proj2 Hx) as Hx2; unfold d2m_W in Hx2; cbn [outside] in Hx2 |- *; clear - Hx2; lia).
  lazymatch goal with UR : rw_cells asegs ?mc (usp + -16) _ |- cps _ (ASTA RT _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
    assert (UCC : chain_ok mc sa usp [RA_FUZZ_OP1; RA_TOP])
      by (apply (chain_ok_push mc sa usp RA_FUZZ_OP1 fp1 [RA_TOP]);
            [ clear - SAU; lia | clear - SPA; Z.div_mod_to_equations; lia | unfold USTACK_TOP; clear - SPT; lia | unfold RA_FUZZ_OP1; clear; lia | let X := fresh "X" in pose proof FP1h as X; unfold hid in X; exact X | exact UR
            | apply (chain_ok_keep [RA_TOP] m _ usp fp1 UCX); eapply agree_sub; [exact AGF|]; cbv beta; intros zx Hzx; apply PFU; unfold USTACK_TOP in Hzx; clear - Hzx; lia ]) end.
  assert (TRc : In (0x9f840 :: [RA_FUZZ_OP1; RA_TOP]) CLIENT_TRACES) by (unfold RA_FUZZ_OP1, RA_TOP; apply ct_mem_In; vm_compute; reflexivity).
  eapply cps_seq.
  { pose proof (gp_calloc RT GP) as CC; unfold calloc_contract in CC; eapply CC with (lo := lo) (nmemb := 256) (size := 4); rt_side idtac.
    all: lazymatch goal with
         | |- unwind_okC _ _ _ _ => exists [RA_FUZZ_OP1; RA_TOP]; rewrite ?unsigned_lit by (clear - USP0 USP1 SAU SPT; lia); split; [exact UCC| exact TRc]
         | |- _ => first [ unfold CALLOC_MAX; clear; lia
                         | rewrite LVB2; cbn [length]; unfold LIVE_MAX in *; clear - LVB; lia
                         | lazymatch goal with |- ?g => idtac "LEFT:" g end ]
         end. }
  idtac "MARK mid: calloc 3 applied".
  clear UCC TRc.
  after_call RT AF.
  fold_ag ltac:(fun Hx => apply (aclient_mono _ _ sa _ _ _ _ (proj1 Hx)); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| clear; lia]).
  idtac "MARK mid: after calloc 3".
  lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σt1; rename A into ARTt1 end.
  lazymatch goal with H : rt_live RT Σt1 = (?p, _) :: _ |- _ => rename H into LVt1N; rename p into tv end.
  lazymatch goal with H : rw_cells asegs _ tv [CB _ _] |- _ => rename H into Ztv end.
  assert (FRSt1 : rt_frames RT Σt1 = (fr, 2%nat) :: frs0) by (repeat match goal with E : rt_frames RT Σt1 = _ |- _ => rewrite E end; first [exact FRS | assumption]).
  assert (SP0t1 : rt_sp0 RT Σt1 = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 RT Σt1 = _ |- _ => rewrite E end; first [reflexivity | assumption]).
  assert (CRt1 : rt_credit RT Σt1 = rt_credit RT Σ) by (repeat match goal with E : rt_credit RT Σt1 = _ |- _ => rewrite E end; first [reflexivity | assumption]).
  lazymatch goal with H : 0 < tv |- _ => rename H into TV0 end.
  lazymatch goal with H : tv mod 16 = 0 |- _ => rename H into TV16 end.
  lazymatch goal with A : ART RT Σt1 ?mm |- _ => pose proof (af_live_disj RT AF Σt1 mm tv (256 * 4) (dat) (rd) [] _ A LVt1N ltac:(cbn [app]; solve [in_live_tac])) as AP_TV_D end.
  lazymatch goal with A : ART RT Σt1 ?mm |- _ => pose proof (af_live_disj RT AF Σt1 mm tv (256 * 4) (datas) (rs) [] _ A LVt1N ltac:(cbn [app]; solve [in_live_tac])) as AP_TV_S end.
  lazymatch goal with A : ART RT Σt1 ?mm |- _ => pose proof (af_live_disj RT AF Σt1 mm tv (256 * 4) (pixd) (64) [] _ A LVt1N ltac:(cbn [app]; solve [in_live_tac])) as AP_TV_P end.
  lazymatch goal with A : ART RT Σt1 ?mm |- _ => pose proof (af_live_disj RT AF Σt1 mm tv (256 * 4) (bufs1) (wpls * 4) [] _ A LVt1N ltac:(cbn [app]; solve [in_live_tac])) as AP_TV_B1 end.
  lazymatch goal with A : ART RT Σt1 ?mm |- _ => pose proof (af_live_disj RT AF Σt1 mm tv (256 * 4) (bufs2) (wpls * 4) [] _ A LVt1N ltac:(cbn [app]; solve [in_live_tac])) as AP_TV_B2 end.
  (* [comment removed for export] *)
  lazymatch goal with A : ART RT Σt1 ?mm |- _ =>
    assert (NE_TV : forall e, In e (rt_live RT Σ) -> fst e <> tv)
      by (intros e He; apply (fresh_chunk_ne RT AF Σt1 mm [] tv (256 * 4) _ e A LVt1N); [cbn [app]; rewrite LVB2; right; right; exact He | clear; lia | destruct e as [eq ek]; exact (LVP eq ek He)]);
    assert (SUB_TV : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σt1) /\ fst e <> tv)
      by (intros e He; split; [rewrite LVt1N; right; rewrite LVB2; right; right; exact He | exact (NE_TV e He)]);
    assert (NC_TV : forall a, PF a -> a < tv \/ tv + 256 * 4 <= a)
      by (intros a Ha; apply (inner_chunk_apart RT AF Σt1 mm tv (256 * 4) (rt_live RT Σ) (rt_frames RT Σ) sa a A ltac:(rewrite LVt1N; left; reflexivity) SUB_TV);
          [ rewrite FRSt1, <- FRS; intros e He; exact He | rewrite SP0t1; unfold STACK_WIN; clear - LOW LOR; lia | exact (proj1 Ha) ]) end.

  assert (LVT1 : rt_live RT Σt1 = (tv, 1024) :: (bufs2, wpls * 4) :: (bufs1, wpls * 4) :: rt_live RT Σ) by (rewrite LVt1N, LVB2; reflexivity).
  chunk_facts RT AF GP tv (1024). fframe_chunk RT AF fr 2%nat 256 tv (1024).
  lazymatch goal with H : tv + _ <= rt_sp0 RT _ - _ |- _ => rename H into CKR_TV end.
  lazymatch goal with H : tv + _ <= 65536 \/ _ <= tv |- _ => rename H into CKS_TV end.
  lazymatch goal with H : tv + _ <= 2147446784 \/ _ <= tv |- _ => rename H into CKH_TV end.
  lazymatch goal with H : fr + 256 <= tv \/ tv + _ <= fr |- _ => rename H into FCD_TV end.
  lazymatch goal with H : tv + _ <= fr / 8 + _ \/ _ <= tv |- _ => rename H into FCS_TV end.
  clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
  walk_to AF MST (@nil (Z * Z)) [e_calloc; 0x9ffc0].
  idtac "MARK mid: at calloc 4".
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; left; ul| exact I]])
                ltac:(fun Hx => let Hx2 := fresh "Ho" in pose proof (proj2 Hx) as Hx2; unfold d2m_W in Hx2; cbn [outside] in Hx2 |- *; clear - Hx2; lia).
  lazymatch goal with UR : rw_cells asegs ?mc (usp + -16) _ |- cps _ (ASTA RT _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
    assert (UCC : chain_ok mc sa usp [RA_FUZZ_OP1; RA_TOP])
      by (apply (chain_ok_push mc sa usp RA_FUZZ_OP1 fp1 [RA_TOP]);
            [ clear - SAU; lia | clear - SPA; Z.div_mod_to_equations; lia | unfold USTACK_TOP; clear - SPT; lia | unfold RA_FUZZ_OP1; clear; lia | let X := fresh "X" in pose proof FP1h as X; unfold hid in X; exact X | exact UR
            | apply (chain_ok_keep [RA_TOP] m _ usp fp1 UCX); eapply agree_sub; [exact AGF|]; cbv beta; intros zx Hzx; apply PFU; unfold USTACK_TOP in Hzx; clear - Hzx; lia ]) end.
  assert (TRc : In (0x9f850 :: [RA_FUZZ_OP1; RA_TOP]) CLIENT_TRACES) by (unfold RA_FUZZ_OP1, RA_TOP; apply ct_mem_In; vm_compute; reflexivity).
  eapply cps_seq.
  { pose proof (gp_calloc RT GP) as CC; unfold calloc_contract in CC; eapply CC with (lo := lo) (nmemb := 256) (size := 4); rt_side idtac.
    all: lazymatch goal with
         | |- unwind_okC _ _ _ _ => exists [RA_FUZZ_OP1; RA_TOP]; rewrite ?unsigned_lit by (clear - USP0 USP1 SAU SPT; lia); split; [exact UCC| exact TRc]
         | |- _ => first [ unfold CALLOC_MAX; clear; lia
                         | rewrite LVT1; cbn [length]; unfold LIVE_MAX in *; clear - LVB; lia
                         | lazymatch goal with |- ?g => idtac "LEFT:" g end ]
         end. }
  idtac "MARK mid: calloc 4 applied".
  clear UCC TRc.
  after_call RT AF.
  fold_ag ltac:(fun Hx => apply (aclient_mono _ _ sa _ _ _ _ (proj1 Hx)); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| clear; lia]).
  idtac "MARK mid: after calloc 4".
  lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σt2; rename A into ARTt2 end.
  lazymatch goal with H : rt_live RT Σt2 = (?p, _) :: _ |- _ => rename H into LVt2N; rename p into t38 end.
  lazymatch goal with H : rw_cells asegs _ t38 [CB _ _] |- _ => rename H into Zt38 end.
  assert (FRSt2 : rt_frames RT Σt2 = (fr, 2%nat) :: frs0) by (repeat match goal with E : rt_frames RT Σt2 = _ |- _ => rewrite E end; first [exact FRS | assumption]).
  assert (SP0t2 : rt_sp0 RT Σt2 = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 RT Σt2 = _ |- _ => rewrite E end; first [reflexivity | assumption]).
  assert (CRt2 : rt_credit RT Σt2 = rt_credit RT Σ) by (repeat match goal with E : rt_credit RT Σt2 = _ |- _ => rewrite E end; first [reflexivity | assumption]).
  lazymatch goal with H : 0 < t38 |- _ => rename H into T80 end.
  lazymatch goal with H : t38 mod 16 = 0 |- _ => rename H into T816 end.
  lazymatch goal with A : ART RT Σt2 ?mm |- _ => pose proof (af_live_disj RT AF Σt2 mm t38 (256 * 4) (dat) (rd) [] _ A LVt2N ltac:(cbn [app]; solve [in_live_tac])) as AP_T8_D end.
  lazymatch goal with A : ART RT Σt2 ?mm |- _ => pose proof (af_live_disj RT AF Σt2 mm t38 (256 * 4) (datas) (rs) [] _ A LVt2N ltac:(cbn [app]; solve [in_live_tac])) as AP_T8_S end.
  lazymatch goal with A : ART RT Σt2 ?mm |- _ => pose proof (af_live_disj RT AF Σt2 mm t38 (256 * 4) (pixd) (64) [] _ A LVt2N ltac:(cbn [app]; solve [in_live_tac])) as AP_T8_P end.
  lazymatch goal with A : ART RT Σt2 ?mm |- _ => pose proof (af_live_disj RT AF Σt2 mm t38 (256 * 4) (bufs1) (wpls * 4) [] _ A LVt2N ltac:(cbn [app]; solve [in_live_tac])) as AP_T8_B1 end.
  lazymatch goal with A : ART RT Σt2 ?mm |- _ => pose proof (af_live_disj RT AF Σt2 mm t38 (256 * 4) (bufs2) (wpls * 4) [] _ A LVt2N ltac:(cbn [app]; solve [in_live_tac])) as AP_T8_B2 end.
  lazymatch goal with A : ART RT Σt2 ?mm |- _ => pose proof (af_live_disj RT AF Σt2 mm t38 (256 * 4) (tv) (256 * 4) [] _ A LVt2N ltac:(cbn [app]; solve [in_live_tac])) as AP_T8_TV end.
  (* [comment removed for export] *)
  lazymatch goal with A : ART RT Σt2 ?mm |- _ =>
    assert (NE_T8 : forall e, In e (rt_live RT Σ) -> fst e <> t38)
      by (intros e He; apply (fresh_chunk_ne RT AF Σt2 mm [] t38 (256 * 4) _ e A LVt2N); [cbn [app]; rewrite LVT1; do 3 right; exact He | clear; lia | destruct e as [eq ek]; exact (LVP eq ek He)]);
    assert (SUB_T8 : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σt2) /\ fst e <> t38)
      by (intros e He; split; [rewrite LVt2N; right; rewrite LVT1; do 3 right; exact He | exact (NE_T8 e He)]);
    assert (NC_T8 : forall a, PF a -> a < t38 \/ t38 + 256 * 4 <= a)
      by (intros a Ha; apply (inner_chunk_apart RT AF Σt2 mm t38 (256 * 4) (rt_live RT Σ) (rt_frames RT Σ) sa a A ltac:(rewrite LVt2N; left; reflexivity) SUB_T8);
          [ rewrite FRSt2, <- FRS; intros e He; exact He | rewrite SP0t2; unfold STACK_WIN; clear - LOW LOR; lia | exact (proj1 Ha) ]) end.

  assert (LVT2 : rt_live RT Σt2 = (t38, 1024) :: (tv, 1024) :: (bufs2, wpls * 4) :: (bufs1, wpls * 4) :: rt_live RT Σ) by (rewrite LVt2N, LVT1; reflexivity).
  chunk_facts RT AF GP t38 (1024). fframe_chunk RT AF fr 2%nat 256 t38 (1024).
  lazymatch goal with H : t38 + _ <= rt_sp0 RT _ - _ |- _ => rename H into CKR_T8 end.
  lazymatch goal with H : t38 + _ <= 65536 \/ _ <= t38 |- _ => rename H into CKS_T8 end.
  lazymatch goal with H : t38 + _ <= 2147446784 \/ _ <= t38 |- _ => rename H into CKH_T8 end.
  lazymatch goal with H : fr + 256 <= t38 \/ t38 + _ <= fr |- _ => rename H into FCD_T8 end.
  lazymatch goal with H : t38 + _ <= fr / 8 + _ \/ _ <= t38 |- _ => rename H into FCS_T8 end.
  clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
  walk_to AF MST [(sa + 16, sa + 40); (sa + 56, sa + 144)] [e_calloc; 0x9ffc0].
  idtac "MARK mid: at calloc 5".
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; left; ul| exact I]])
                ltac:(fun Hx => let Hx2 := fresh "Ho" in pose proof (proj2 Hx) as Hx2; unfold d2m_W in Hx2; cbn [outside] in Hx2 |- *; clear - Hx2; lia).
  lazymatch goal with UR : rw_cells asegs ?mc (usp + -16) _ |- cps _ (ASTA RT _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
    assert (UCC : chain_ok mc sa usp [RA_FUZZ_OP1; RA_TOP])
      by (apply (chain_ok_push mc sa usp RA_FUZZ_OP1 fp1 [RA_TOP]);
            [ clear - SAU; lia | clear - SPA; Z.div_mod_to_equations; lia | unfold USTACK_TOP; clear - SPT; lia | unfold RA_FUZZ_OP1; clear; lia | let X := fresh "X" in pose proof FP1h as X; unfold hid in X; exact X | exact UR
            | apply (chain_ok_keep [RA_TOP] m _ usp fp1 UCX); eapply agree_sub; [exact AGF|]; cbv beta; intros zx Hzx; apply PFU; unfold USTACK_TOP in Hzx; clear - Hzx; lia ]) end.
  assert (TRc : In (0x9f864 :: [RA_FUZZ_OP1; RA_TOP]) CLIENT_TRACES) by (unfold RA_FUZZ_OP1, RA_TOP; apply ct_mem_In; vm_compute; reflexivity).
  eapply cps_seq.
  { pose proof (gp_calloc RT GP) as CC; unfold calloc_contract in CC; eapply CC with (lo := lo) (nmemb := 256) (size := 4); rt_side idtac.
    all: lazymatch goal with
         | |- unwind_okC _ _ _ _ => exists [RA_FUZZ_OP1; RA_TOP]; rewrite ?unsigned_lit by (clear - USP0 USP1 SAU SPT; lia); split; [exact UCC| exact TRc]
         | |- _ => first [ unfold CALLOC_MAX; clear; lia
                         | rewrite LVT2; cbn [length]; unfold LIVE_MAX in *; clear - LVB; lia
                         | lazymatch goal with |- ?g => idtac "LEFT:" g end ]
         end. }
  idtac "MARK mid: calloc 5 applied".
  clear UCC TRc.
  after_call RT AF.
  fold_ag ltac:(fun Hx => apply (aclient_mono _ _ sa _ _ _ _ (proj1 Hx)); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| clear; lia]).
  idtac "MARK mid: after calloc 5".
  lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σt3; rename A into ARTt3 end.
  lazymatch goal with H : rt_live RT Σt3 = (?p, _) :: _ |- _ => rename H into LVt3N; rename p into t14 end.
  lazymatch goal with H : rw_cells asegs _ t14 [CB _ _] |- _ => rename H into Zt14 end.
  assert (FRSt3 : rt_frames RT Σt3 = (fr, 2%nat) :: frs0) by (repeat match goal with E : rt_frames RT Σt3 = _ |- _ => rewrite E end; first [exact FRS | assumption]).
  assert (SP0t3 : rt_sp0 RT Σt3 = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 RT Σt3 = _ |- _ => rewrite E end; first [reflexivity | assumption]).
  assert (CRt3 : rt_credit RT Σt3 = rt_credit RT Σ) by (repeat match goal with E : rt_credit RT Σt3 = _ |- _ => rewrite E end; first [reflexivity | assumption]).
  lazymatch goal with H : 0 < t14 |- _ => rename H into T40 end.
  lazymatch goal with H : t14 mod 16 = 0 |- _ => rename H into T416 end.
  lazymatch goal with A : ART RT Σt3 ?mm |- _ => pose proof (af_live_disj RT AF Σt3 mm t14 (256 * 4) (dat) (rd) [] _ A LVt3N ltac:(cbn [app]; solve [in_live_tac])) as AP_T4_D end.
  lazymatch goal with A : ART RT Σt3 ?mm |- _ => pose proof (af_live_disj RT AF Σt3 mm t14 (256 * 4) (datas) (rs) [] _ A LVt3N ltac:(cbn [app]; solve [in_live_tac])) as AP_T4_S end.
  lazymatch goal with A : ART RT Σt3 ?mm |- _ => pose proof (af_live_disj RT AF Σt3 mm t14 (256 * 4) (pixd) (64) [] _ A LVt3N ltac:(cbn [app]; solve [in_live_tac])) as AP_T4_P end.
  lazymatch goal with A : ART RT Σt3 ?mm |- _ => pose proof (af_live_disj RT AF Σt3 mm t14 (256 * 4) (bufs1) (wpls * 4) [] _ A LVt3N ltac:(cbn [app]; solve [in_live_tac])) as AP_T4_B1 end.
  lazymatch goal with A : ART RT Σt3 ?mm |- _ => pose proof (af_live_disj RT AF Σt3 mm t14 (256 * 4) (bufs2) (wpls * 4) [] _ A LVt3N ltac:(cbn [app]; solve [in_live_tac])) as AP_T4_B2 end.
  lazymatch goal with A : ART RT Σt3 ?mm |- _ => pose proof (af_live_disj RT AF Σt3 mm t14 (256 * 4) (tv) (256 * 4) [] _ A LVt3N ltac:(cbn [app]; solve [in_live_tac])) as AP_T4_TV end.
  lazymatch goal with A : ART RT Σt3 ?mm |- _ => pose proof (af_live_disj RT AF Σt3 mm t14 (256 * 4) (t38) (256 * 4) [] _ A LVt3N ltac:(cbn [app]; solve [in_live_tac])) as AP_T4_T8 end.
  (* [comment removed for export] *)
  lazymatch goal with A : ART RT Σt3 ?mm |- _ =>
    assert (NE_T4 : forall e, In e (rt_live RT Σ) -> fst e <> t14)
      by (intros e He; apply (fresh_chunk_ne RT AF Σt3 mm [] t14 (256 * 4) _ e A LVt3N); [cbn [app]; rewrite LVT2; do 4 right; exact He | clear; lia | destruct e as [eq ek]; exact (LVP eq ek He)]);
    assert (SUB_T4 : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σt3) /\ fst e <> t14)
      by (intros e He; split; [rewrite LVt3N; right; rewrite LVT2; do 4 right; exact He | exact (NE_T4 e He)]);
    assert (NC_T4 : forall a, PF a -> a < t14 \/ t14 + 256 * 4 <= a)
      by (intros a Ha; apply (inner_chunk_apart RT AF Σt3 mm t14 (256 * 4) (rt_live RT Σ) (rt_frames RT Σ) sa a A ltac:(rewrite LVt3N; left; reflexivity) SUB_T4);
          [ rewrite FRSt3, <- FRS; intros e He; exact He | rewrite SP0t3; unfold STACK_WIN; clear - LOW LOR; lia | exact (proj1 Ha) ]) end.

  assert (LVT3 : rt_live RT Σt3 = (t14, 1024) :: (t38, 1024) :: (tv, 1024) :: (bufs2, wpls * 4) :: (bufs1, wpls * 4) :: rt_live RT Σ) by (rewrite LVt3N, LVT2; reflexivity).
  chunk_facts RT AF GP t14 (1024). fframe_chunk RT AF fr 2%nat 256 t14 (1024).
  lazymatch goal with H : t14 + _ <= rt_sp0 RT _ - _ |- _ => rename H into CKR_T4 end.
  lazymatch goal with H : t14 + _ <= 65536 \/ _ <= t14 |- _ => rename H into CKS_T4 end.
  lazymatch goal with H : t14 + _ <= 2147446784 \/ _ <= t14 |- _ => rename H into CKH_T4 end.
  lazymatch goal with H : fr + 256 <= t14 \/ t14 + _ <= fr |- _ => rename H into FCD_T4 end.
  lazymatch goal with H : t14 + _ <= fr / 8 + _ \/ _ <= t14 |- _ => rename H into FCS_T4 end.
  clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
  idtac "MARK mid: tables allocated".
  (* [comment removed for export] *)
  walk_to AF MST [(sa + 16, sa + 40); (sa + 56, sa + 144); (tv, tv + 1024); (t38, t38 + 1024); (t14, t14 + 1024)] [0x9f8ec; 0xa03a8].
  idtac "MARK mid: at the table loop".
  (* [comment removed for export] *)
  assert (FLv : Z.land tv 3 = 0) by (change 3 with (Z.ones 2); rewrite Z.land_ones by (clear - TV0; lia); clear - TV0 TV16; Z.div_mod_to_equations; lia).
  assert (FL8 : Z.land t38 3 = 0) by (change 3 with (Z.ones 2); rewrite Z.land_ones by (clear - T80; lia); clear - T80 T816; Z.div_mod_to_equations; lia).
  assert (FL4 : Z.land t14 3 = 0) by (change 3 with (Z.ones 2); rewrite Z.land_ones by (clear - T40; lia); clear - T40 T416; Z.div_mod_to_equations; lia).
  rewrite !FLv, !FL8, !FL4. clear FLv FL8 FL4.
  rewrite !(proj2 (Z.ltb_lt 0 tv) TV0). rewrite !(proj2 (Z.ltb_lt 0 t38) T80). rewrite !(proj2 (Z.ltb_lt 0 t14) T40).
  change (0 <? 1) with true. change (Z.b2z true) with 1. change (Z.land 1 1) with 1.
  (* [comment removed for export] *)
  pose proof Ztv as X1; apply u8arr_of_rw_cells in X1; destruct (u8arr_u32arr _ tv _ 256 X1 ltac:(rewrite repeat_length, Z2Nat.id by (clear; lia); clear; lia)) as (ws1 & UA1 & UAL1); clear X1.
  pose proof Zt38 as X2; apply u8arr_of_rw_cells in X2; destruct (u8arr_u32arr _ t38 _ 256 X2 ltac:(rewrite repeat_length, Z2Nat.id by (clear; lia); clear; lia)) as (ws2 & UA2 & UAL2); clear X2.
  pose proof Zt14 as X3; apply u8arr_of_rw_cells in X3; destruct (u8arr_u32arr _ t14 _ 256 X3 ltac:(rewrite repeat_length, Z2Nat.id by (clear; lia); clear; lia)) as (ws3 & UA3 & UAL3); clear X3.
  clear Ztv Zt38 Zt14.
  (* [comment removed for export] *)
  pose proof FRBLK as CX56. split_at CX56 1%nat CXr. split_at CXr 6%nat CX112. split_at CX112 2%nat CXr2. clear CXr CXr2.
  assert (GEOT : dt2_geom tv t38 t14 sa).
  { unfold dt2_geom, SEGTOP_A. unfold hid in SP0H. unpark CKS_TV. unpark CKH_TV. unpark CKS_T8. unpark CKH_T8. unpark CKS_T4. unpark CKH_T4. unpark AP_T8_TV. unpark AP_T4_TV. unpark AP_T4_T8.
    clear - TV0 TV16 T80 T816 T40 T416 CKR_TV CKS_TV CKH_TV CKR_T8 CKS_T8 CKH_T8 CKR_T4 CKS_T4 CKH_T4 AP_T8_TV AP_T4_TV AP_T4_T8 SP0H SA32 SAU SPB LOW LOR.
    repeat lazymatch goal with |- _ /\ _ => split end; first [lia | Z.div_mod_to_equations; lia]. }
  idtac "MARK mid: GEOT".
  eapply evt_cut.
  { lazymatch goal with MIx : mem_inv asegs ?mm, A1 : acc asegs ?mm tv 1024, A2 : acc asegs ?mm t38 1024, A3 : acc asegs ?mm t14 1024 |- evt _ _ (MS _ ?F0 _ ?fc0 None ?mm _) =>
      eapply (dt2_tables 256%nat 0 _ _ _ _ _ _ _ _ _ _ _ F0 fc0 mm mm sa tv t38 t14 ws1 ws2 ws3
                eq_refl (Z.le_refl 0) ltac:(clear; lia) GEOT (munch_refl _ mm) (wmono_refl asegs mm) MIx
                UA1 UAL1 A1 UA2 UAL2 A2 UA3 UAL3 A3 (small_upto_0 ws2) (small_upto_0 ws3) (conj CX56 CX112)) end. }
  idtac "MARK mid: tables applied".
  clear UA1 UAL1 UA2 UAL2 UA3 UAL3 CX56 CX112.
  intros ms' PO. unfold dt2_exit in PO.
  destruct PO as (a0' & a1' & a2' & a3' & s4' & s10' & t3' & t4' & t6' & m' & tw & t38w & t14w & -> & MUl & WMl & MIl
                  & TA & TAL & ACT & T38 & T38L & AC8 & TS8 & T14 & T14L & AC4 & TS4 & CXl).
  clear ACT AC8 AC4 CXl.
  (* [comment removed for export] *)
  try clear Zbufs1. try clear Zbufs2.
  (* [comment removed for export] *)
  lazymatch type of MUl with munch _ ?ma ?mb =>
      loop_art RT AF Σt3 mb lo MUl ltac:(cbn [ivls_client];
        split; [intros zz Hzz; left; ul | split; [intros zz Hzz; left; ul
        | split; [intros zz Hzz; right; right; left; exists tv, 1024; split; [solve [in_live_tac]| clear - Hzz; lia]
        | split; [intros zz Hzz; right; right; left; exists t38, 1024; split; [solve [in_live_tac]| clear - Hzz; lia]
        | split; [intros zz Hzz; right; right; left; exists t14, 1024; split; [solve [in_live_tac]| clear - Hzz; lia] | exact I]]]]]) end.
  idtac "MARK mid: loop_art".
  lazymatch type of MUl with munch _ ?ma ?mb =>
    loop_transport ma mb MUl ltac:(fun Hx => unpark FCD_TV; unpark FCD_T8; unpark FCD_T4; unpark AP_TV_P; unpark AP_T8_P; unpark AP_T4_P; unpark CKS_TV; unpark CKS_T8; unpark CKS_T4;
      clear - Hx SZ CKR_TV CKR_T8 CKR_T4 CKS_TV CKS_T8 CKS_T4 FCD_TV FCD_T8 FCD_T4 AP_TV_P AP_T8_P AP_T4_P LOW LOR SAU SPB SP0H STa;
      unfold hid in *; first [lia | Z.div_mod_to_equations; lia]) end.
  idtac "MARK mid: loop_transport".
  clear MUl. unfold SHB.
  (* [comment removed for export] *)
  awalk [e_asan_memcpy; 0xa03a8].
  idtac "MARK mid: STOP D".
  (* [comment removed for export] *)
  rewrite (srliw30_guard wpls) by (pose proof SZ as X; unfold hid in X; clear - X; lia). brF.
  awalk [e_asan_memcpy; 0xa03a8].
  swrap_fix.
  idtac "MARK mid: at memcpy 0".
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; left; ul
        | split; [intros zz Hzz; right; right; left; exists tv, 1024; split; [solve [in_live_tac]| clear - Hzz; lia]
        | split; [intros zz Hzz; right; right; left; exists t38, 1024; split; [solve [in_live_tac]| clear - Hzz; lia]
        | split; [intros zz Hzz; right; right; left; exists t14, 1024; split; [solve [in_live_tac]| clear - Hzz; lia] | exact I]]]]])
                ltac:(fun Hx => let Ho := fresh "Ho" in pose proof (proj2 Hx) as Ho; pose proof (NC_TV _ Hx) as Ho3; pose proof (NC_T8 _ Hx) as Ho4; pose proof (NC_T4 _ Hx) as Ho5; unfold d2m_W in Ho; cbn [outside] in Ho |- *; clear - Ho Ho3 Ho4 Ho5; lia).
  idtac "MARK mid: at_call memcpy 0".
  lazymatch goal with A : ART RT Σt3 ?mm |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mm _))) _ =>
    pose proof (af_acc_live RT AF Σt3 mm datas rs A ltac:(solve [in_live_tac])) as (WRS & ACCS);
    pose proof (af_acc_live RT AF Σt3 mm bufs2 (wpls * 4) A ltac:(solve [in_live_tac])) as (WR2 & ACC2) end.
  pose proof SZ as SZv. unfold hid in SZv. assert (N1RS : wpls * 4 <= rs) by (clear - SZv; nia).
  apply wr_at_rw_CB in WRS; [| clear - SZv; lia]. destruct WRS as (sbs & SBC).
  pose proof SBC as [[[SBL _] _] _]. cbn in SBL.
  apply u8arr_of_rw_cells in SBC. destruct SBC as [SB _].
  rewrite <- (firstn_skipn (Z.to_nat (wpls * 4)) sbs) in SB. apply bytes_at_app in SB. destruct SB as [SB1 _].
  set (rowbs := firstn (Z.to_nat (wpls * 4)) sbs) in SB1.
  assert (SBL1 : Z.of_nat (length rowbs) = wpls * 4) by (subst rowbs; rewrite firstn_length_le; [| rewrite SBL]; clear - SZv N1RS; lia).
  clearbody rowbs. clear SBL sbs.
  assert (Q7a : 0 <= bufs2 <= 2^47) by (unfold hid in SP0H; clear - CKR_B2 SP0H B20 SZv; lia).
  assert (Q7b : 0 <= datas <= 2^47) by (unfold hid in SP0H; clear - CKR0 SP0H DS0 SZv; lia).
  assert (Q3 : bufs2 + wpls * 4 <= datas \/ datas + wpls * 4 <= bufs2) by (unpark AP_B2_S; clear - AP_B2_S N1RS; lia). park AP_B2_S.
  assert (Q4 : datas + wpls * 4 <= lo) by (clear - CKR0 LOW N1RS; lia).
  eapply cps_seq.
  { pose proof (rc_asan_memcpy RT RC) as MC0; unfold memcpy_icontract in MC0;
    eapply MC0 with (lo := lo) (d := bufs2) (s := datas) (bs := rowbs); rewrite ?SBL1.
    all: lazymatch goal with
         | |- fdfs_only _ => exact FDO
         | |- mat_stable _ => exact MST
         | |- Z_to_bv 64 _ = Z_to_bv 64 _ => f_equal; clear - SZv; lia
         | |- bytes_at _ _ _ _ => exact SB1
         | |- ART _ _ _ => assumption
         | |- mem_inv _ _ => assumption
         | |- checked_src _ _ _ _ _ _ _ =>
             unfold checked_src; rewrite ?unsigned_lit by (clear - USP0 USP1; lia);
             split; [intros _; split; [eapply acc_sub; [exact ACCS| clear; lia | clear - SZv N1RS; lia]
                                    | left; exists datas, rs; split; [solve [in_live_tac]| clear - SZv N1RS; lia]]
                   | left; exact Q4]
         | |- checked_dst _ _ _ _ _ _ =>
             unfold checked_dst; rewrite ?unsigned_lit by (clear - USP0 USP1; lia);
             split; [intros _; split; [exact ACC2| left; exists bufs2, (wpls * 4); split; [solve [in_live_tac]| clear; lia]]|];
             split; [intros i0 Hi; right; right; left; exists bufs2, (wpls * 4); split; [solve [in_live_tac]| clear - Hi; lia]| exact WR2]
         | |- call_ok _ _ _ _ _ => call_ok_tac
         | |- _ \/ _ => exact Q3
         | |- (_ <= _ <= _) => first [exact Q7a | exact Q7b]
         | |- (_ < _) => clear - SZv; lia
         | |- ?g => idtac "LEFT:" g
         end. }
  rewrite SBL1.   (* [comment removed for export] *)
  idtac "MARK mid: memcpy 0 applied".
  clear SB1 SBL1 ACCS ACC2 WR2 Q7a Q7b Q3 Q4 SZv N1RS.
  unpark AP_TV_S. unpark AP_T8_S. unpark AP_T4_S. unpark AP_TV_B2. unpark AP_T8_B2. unpark AP_T4_B2.
  after_call RT AF.
  park AP_TV_S. park AP_T8_S. park AP_T4_S. park AP_TV_B2. park AP_T8_B2. park AP_T4_B2.
  idtac "MARK mid: after_call memcpy 0".
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ sa _ _ _ _ (proj1 Hx)); [solve [live_add_tac] | solve [frames_sub_tac] | clear; lia]
                               | pose proof (NC_B2 _ Hx) as Hb; cbn [outside]; clear - Hb; lia]).
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj. park_ne.
  (* [comment removed for export] *)
  walk_to AF MST [(sa + 16, sa + 40); (sa + 56, sa + 144)] [0xa02c4; 0xa01f0; 0xa03a8].
  (* [comment removed for export] *)
  pose proof SZ as SZv. unfold hid in SZv.
  rewrite (unsigned_lit h) by (clear - SZv; lia). swrap_fix. brF.
  rewrite ?(sx32_small w) in * by (clear - SZv; lia).
  awalk [0xa02c4; 0xa01f0; 0xa03a8].
  idtac "MARK mid: at the h dispatch".
  lazymatch goal with FRx : rw_cells asegs ?mf (sa + 56) _ |- _ =>
    replace (Z.land bufs1 3) with 0 in FRx by (symmetry; change 3 with (Z.ones 2); rewrite Z.land_ones by (clear; lia); change (2 ^ 2) with 4; clear - B116; Z.div_mod_to_equations; lia) end.
  lazymatch goal with FRx : rw_cells asegs ?mf (sa + 16) _ |- _ => replace (h + -1) with (h - 1) in FRx by (clear; lia) end.
  (* [comment removed for export] *)
  assert (N1RS : wpls * 4 <= rs) by (clear - SZv; nia).
  unpark AP_B2_S. try unpark AP_B2_S. park_disj.
  assert (DGEOM : d2r_geom (rt_sp0 RT Σ) lo sa dat rd datas rs bufs1 bufs2 (wpls * 4) wpls wpld w h tv t38 t14).
  { unfold d2r_geom, LSTK, STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A. unfold hid in SP0H.
    repeat lazymatch goal with |- _ /\ _ => split end.
    all: first [ assumption
               | match goal with H : parked _ |- _ => unpark H; exact H end
               | solve [clear - SZv N1RS SP0H LOW LOR SAU SPT SPB SP0R0 SP0R1 SP0W STa SA32 B10 B20 TV0 T80 T40 DD0 DS0 PD0 CKR2 CKR0 CKR1 CKR_B1 CKR_B2 CKR_TV CKR_T8 CKR_T4; lia]
               | match goal with H : parked (_ \/ _) |- _ => solve [unpark H; try unpark H; clear - H; lia] end
               | match goal with |- ?g => idtac "LEFT DGEOM:" g end ]. }
  idtac "MARK mid: DGEOM".
  assert (ND5 : NoDup [bufs1; bufs2; tv; t38; t14]).
  { pose proof AP_B2_B1 as Q1. pose proof AP_TV_B1 as Q2. pose proof AP_TV_B2 as Q3. pose proof AP_T8_B1 as Q4. pose proof AP_T8_B2 as Q5. pose proof AP_T8_TV as Q6.
    pose proof AP_T4_B1 as Q7. pose proof AP_T4_B2 as Q8. pose proof AP_T4_TV as Q9. pose proof AP_T4_T8 as Q10.
    unpark Q1. unpark Q2. unpark Q3. unpark Q4. unpark Q5. unpark Q6. unpark Q7. unpark Q8. unpark Q9. unpark Q10.
    assert (N1 : bufs1 <> bufs2) by (clear - Q1 SZv; lia). assert (N2 : bufs1 <> tv) by (clear - Q2 SZv; lia). assert (N3 : bufs1 <> t38) by (clear - Q4 SZv; lia).
    assert (N4 : bufs1 <> t14) by (clear - Q7 SZv; lia). assert (N5 : bufs2 <> tv) by (clear - Q3 SZv; lia). assert (N6 : bufs2 <> t38) by (clear - Q5 SZv; lia).
    assert (N7 : bufs2 <> t14) by (clear - Q8 SZv; lia). assert (N8 : tv <> t38) by (clear - Q6; lia). assert (N9 : tv <> t14) by (clear - Q9; lia). assert (N10 : t38 <> t14) by (clear - Q10; lia).
    clear - N1 N2 N3 N4 N5 N6 N7 N8 N9 N10.
    repeat first [ apply NoDup_nil_2 | apply NoDup_cons_2; [ repeat (apply (proj2 (stdpp.list_basics.list.not_elem_of_cons _ _ _)); split; [congruence|]); apply stdpp.list_basics.list.not_elem_of_nil |] ]. }
  assert (FRESH5 : forall e, In e (rt_live RT Σ) -> fst e <> bufs1 /\ fst e <> bufs2 /\ fst e <> tv /\ fst e <> t38 /\ fst e <> t14)
    by (intros e He; exact (conj (NE_B1 e He) (conj (NE_B2 e He) (conj (NE_TV e He) (conj (NE_T8 e He) (NE_T4 e He)))))).
  (* [comment removed for export] *)
  lazymatch goal with FRx : rw_cells asegs ?mf (sa + 56) _ |- _ => split_at FRx 9%nat J128 end.
  destruct (Z.eq_dec h 1) as [HONE|HTWO].
  - (* [comment removed for export] *)
    brT.
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; left; ul| exact I]]).
    lazymatch goal with MUx : munch _ ?mm _ |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      lazymatch type of MUx with munch _ _ mc =>
        agf_munch AGF MUx ltac:(fun Hx => let Ho := fresh "Ho" in pose proof (proj2 Hx) as Ho; unfold d2m_W in Ho; cbn [outside] in Ho |- *; clear - Ho; lia) end end.
    idtac "MARK mid: h = 1 segment closed".
    lazymatch goal with A : ART RT Σt3 ?mq, FRLOx : rw_cells asegs ?mq (sa + 16) _, C48x : rw_cells asegs ?mq (sa + 48) _, FR56x : rw_cells asegs ?mq (sa + 56) _,
                         J128x : rw_cells asegs ?mq (sa + 128) _, FPDx : rw_cells asegs ?mq (fr + 112) _, PXDx : rw_cells asegs ?mq pixd _, URx : rw_cells asegs ?mq (usp + -16) _,
                         MIx : mem_inv asegs ?mq, STx : stk asegs ?mq lo sa, LHx : LIBH ?mq, SSPx : io_ssp ?mq,
                         TAx : u32arr asegs ?mq tv tw, T38x : u32arr asegs ?mq t38 t38w, T14x : u32arr asegs ?mq t14 t14w, AGx : agree_on PF m ?mq
                    |- cps _ (ASTA RT Σt3 _ (eq (MS _ _ _ _ _ ?mq _))) _ =>
      assert (UCXq : chain_ok mq usp fp1 [RA_TOP])
        by (apply (chain_ok_keep [RA_TOP] m mq usp fp1 UCX); eapply agree_sub; [exact AGx|]; cbv beta; intros zx Hzx; apply PFU; unfold USTACK_TOP in Hzx; clear - Hzx; lia);
      eapply (d2_mid2 Σ Σt3 PMc m mq) with (lo := lo) (fr := fr) (pixd := pixd) (dat := dat) (rd := rd) (datas := datas) (rs := rs) (wpls := wpls) (wpld := wpld) (w := w) (h := h)
                                         (fp1 := fp1) (bufs1 := bufs1) (bufs2 := bufs2) (tv := tv) (t38 := t38) (t14 := t14) (vd := vd) (frs0 := frs0) (tw := tw) (t38w := t38w) (t14w := t14w);
      first [ exact FDO | exact MST | exact GEOM | exact DGEOM | exact LVT3 | exact FRSt3 | exact FRS | exact SP0t3 | exact CRt3 | exact ND5 | exact FRESH5
            | exact LVB | exact FRB | exact CRB | exact LVP | exact PXDx | solve [unfold pix_cells; rewrite VW, VH, VD, VWPL, VDAT, VCM; exact PXDx] | exact PDIN | exact DDIN | exact DSIN
            | exact VW | exact VH | exact VD | exact VWPL | exact VDAT | exact VCM | exact UCXq
            | exact A | exact MIx | exact STx | exact LHx | exact SSPx | exact URx | exact FRLOx | exact C48x | exact FR56x | exact J128x | exact FPDx
            | exact TS8 | exact TS4 | exact AGx
            | solve [pose proof HOKD as X; unfold hid in X; exact X]
            | solve [pose proof FP1h as X; unfold hid in X; exact X]
            | solve [split; [exact TAx| split; [exact TAL| split; [exact T38x| split; [exact T38L| split; [exact T14x| exact T14L]]]]]]
            | match goal with |- ?g => idtac "LEFT mid2 apply:" g end ]
    end.
  - (* [comment removed for export] *)
    brF.
    awalk [0xa01f0; 0xa03a8].
    idtac "MARK mid: at the rows".
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; left; ul| exact I]]).
    lazymatch goal with MUx : munch _ ?mm _ |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      lazymatch type of MUx with munch _ _ mc =>
        agf_munch AGF MUx ltac:(fun Hx => let Ho := fresh "Ho" in pose proof (proj2 Hx) as Ho; unfold d2m_W in Ho; cbn [outside] in Ho |- *; clear - Ho; lia) end end.
    idtac "MARK mid: rows segment closed".
    replace (0 <? datas) with true by (symmetry; apply Z.ltb_lt; clear - DS0; lia).
    replace (0 <? dat) with true by (symmetry; apply Z.ltb_lt; clear - DD0; lia).
    cbn [Z.b2z].
    assert (RK1 : Z.of_nat (Z.to_nat (h - 1)) = h - 1 - 0) by (clear - SZv HTWO; lia).
    assert (RK3 : (1 <= Z.to_nat (h - 1))%nat) by (clear - SZv HTWO; lia).
    lazymatch goal with A : ART RT Σt3 ?mq |- cps _ (ASTA RT Σt3 _ (eq (MS _ _ _ _ _ ?mq _))) _ =>
      eapply cps_seq with (Q := d2r_post RT Σt3 PMc gp (Z_to_bv 64 usp) (Z_to_bv 64 fr) (Z_to_bv 64 (fr / 8 + 2147450880))
                                  sa lo dat rd datas rs bufs1 bufs2 (wpls * 4) wpls wpld w h tv t38 t14 (Z_to_bv 64 0) tw t38w t14w mq) end.
    { lazymatch goal with A : ART RT Σt3 ?mq, FR56x : rw_cells asegs ?mq (sa + 56) _, MIx : mem_inv asegs ?mq, STx : stk asegs ?mq lo sa, LHx : LIBH ?mq, SSPx : io_ssp ?mq,
                           TAx : u32arr asegs ?mq tv tw, T38x : u32arr asegs ?mq t38 t38w, T14x : u32arr asegs ?mq t14 t14w
                      |- cps _ (ASTA RT Σt3 _ (eq (MS _ _ _ _ _ ?mq _))) _ =>
        eapply (d2_rows RT AF GP RC (Z.to_nat (h - 1)) 0 Σt3 PMc mq) with (lo := lo) (rd := rd) (rs := rs) (wpld := wpld) (w := w) (t14 := t14);
        first [ exact RK1 | exact RK3 | exact FDO | exact MST | exact A | exact MIx | exact STx | exact LHx | exact SSPx | exact FR56x | exact TS8 | exact TS4
              | solve [clear; lia]
              | solve [rewrite SP0t3; exact DGEOM]
              | solve [rewrite LVT3; cbn [In]; repeat first [left; reflexivity | assumption | right]]
              | solve [split; [exact TAx| split; [exact TAL| split; [exact T38x| split; [exact T38L| split; [exact T14x| exact T14L]]]]]]
              | match goal with |- ?g => idtac "LEFT d2_rows:" g end ] end. }
    idtac "MARK mid: rows applied".
    clear RK1 RK3.
    cps_open RT.
    lazymatch goal with Hx : ART RT Σt3 ?mr /\ _ |- _ =>
      destruct Hx as (ARTr & MIr & STr & LHr & SSPr & FRr & TBr & WMr & AGr) end.
    idtac "MARK mid: rows opened".
    (* [comment removed for export] *)
    pose proof (af_frames_range RT AF Σt3 _ fr 2%nat ARTr ltac:(rewrite FRSt3; left; reflexivity)) as (_ & _ & _ & FAP). change (fs_size 2%nat) with 256 in FAP.
    pose proof (FAP bufs1 (wpls * 4) ltac:(rewrite LVT3; do 4 right; left; reflexivity)) as FAB1.
    pose proof (FAP bufs2 (wpls * 4) ltac:(rewrite LVT3; do 3 right; left; reflexivity)) as FAB2. clear FAP.
    lazymatch type of AGr with agree_on _ ?mq ?mr =>
      lazymatch goal with FRLOx : rw_cells asegs mq (sa + 16) _, C48x : rw_cells asegs mq (sa + 48) _, J128x : rw_cells asegs mq (sa + 128) _,
                          FPDx : rw_cells asegs mq (fr + 112) _, PXDx : rw_cells asegs mq pixd _, URx : rw_cells asegs mq (usp + -16) _, AGx : agree_on PF m mq |- _ =>
      assert (FRLOr : rw_cells asegs mr (sa + 16) [C8 (Z_to_bv 64 (h - 1)); C8 (Z_to_bv 64 (fr + 80)); C8 (Z_to_bv 64 1)])
        by (apply (rw_cells_agree_nw asegs mq mr _ _ FRLOx); eapply agree_sub; [exact AGr|]; cbv beta; intros zx Hzx; cbn in Hzx;
            split; [left; unfold USTACK_TOP; clear - Hzx SAU SPT; lia| cbn [outside]; clear - Hzx SAU CKR2 CKR_B1 CKR_B2 LOW LOR; lia]);
      assert (C48r : rw_cells asegs mr (sa + 48) [C8 (Z_to_bv 64 (fr + 112))])
        by (apply (rw_cells_agree_nw asegs mq mr _ _ C48x); eapply agree_sub; [exact AGr|]; cbv beta; intros zx Hzx; cbn in Hzx;
            split; [left; unfold USTACK_TOP; clear - Hzx SAU SPT; lia| cbn [outside]; clear - Hzx SAU CKR2 CKR_B1 CKR_B2 LOW LOR; lia]);
      assert (J128r : rw_cells asegs mr (sa + 128) [CB 16 (skipn 8 (skipn 8 j112))])
        by (apply (rw_cells_agree_nw asegs mq mr _ _ J128x); eapply agree_sub; [exact AGr|]; cbv beta; intros zx Hzx; cbn in Hzx;
            split; [left; unfold USTACK_TOP; clear - Hzx SAU SPT; lia| cbn [outside]; clear - Hzx SAU CKR2 CKR_B1 CKR_B2 LOW LOR; lia]);
      assert (URr : rw_cells asegs mr (usp + -16) [C8 (Z_to_bv 64 fp1); C8 (Z_to_bv 64 RA_FUZZ_OP1)])
        by (apply (rw_cells_agree_nw asegs mq mr _ _ URx); eapply agree_sub; [exact AGr|]; cbv beta; intros zx Hzx; cbn in Hzx;
            split; [left; unfold USTACK_TOP; clear - Hzx SAU SPT; lia| cbn [outside]; clear - Hzx SAU CKR2 CKR_B1 CKR_B2 LOW LOR; lia]);
      assert (FPDr : rw_cells asegs mr (fr + 112) [C8 (Z_to_bv 64 pixd)])
        by (apply (rw_cells_agree_nw asegs mq mr _ _ FPDx); eapply agree_sub; [exact AGr|]; cbv beta; intros zx Hzx; cbn in Hzx;
            split; [right; right; right; left; exists fr, 2%nat; split; [rewrite FRSt3; left; reflexivity| change (fs_size 2%nat) with 256; clear - Hzx; lia]
                  | cbn [outside]; unpark FCD2; clear - Hzx FCD2 FAB1 FAB2; lia]);
      assert (PXDr : rw_cells asegs mr pixd (pix_cells vd))
        by (unfold pix_cells; rewrite VW, VH, VD, VWPL, VDAT, VCM;
            apply (rw_cells_agree_nw asegs mq mr _ _ PXDx); eapply agree_sub; [exact AGr|]; cbv beta; intros zx Hzx;
            cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Hzx;
            split; [right; right; left; exists pixd, 64; split; [rewrite LVT3; do 5 right; exact PDIN| clear - Hzx; lia]
                  | cbn [outside]; unpark APPD; unpark AP_B1_P; unpark AP_B2_P; clear - Hzx APPD AP_B1_P AP_B2_P; lia]);
      assert (AGFr : agree_on PF m mr)
        by (apply (agree_trans PF m mq mr AGx); apply (agree_sub _ _ _ _ AGr); intros a Ha;
            pose proof (NC_B1 a Ha) as N1; pose proof (NC_B2 a Ha) as N2; destruct Ha as [Ha1 Ha2]; split;
            [ apply (aclient_mono _ _ sa _ _ _ _ Ha1); [intros e He; rewrite LVT3; do 5 right; exact He| rewrite FRSt3, FRS; intros e He; exact He| clear; lia]
            | unfold d2m_W in Ha2; cbn [outside] in Ha2 |- *; clear - Ha2 N1 N2; lia ]);
      clear FRLOx C48x J128x FPDx PXDx URx AGx; rename AGFr into AGF;
      lazymatch type of WMr with wmono _ mq mr => repeat match goal with Hy : context [mq] |- _ => lazymatch type of Hy with wmono _ mq mr => fail | _ => clear Hy end end end
      end end.
    lazymatch goal with TB : d2r_tabs _ tv t38 t14 tw t38w t14w |- _ => destruct TB as (TAr & _ & T38r & _ & T14r & _) end.
    idtac "MARK mid: after the rows".
    lazymatch goal with A : ART RT Σt3 ?mq, FRLOx : rw_cells asegs ?mq (sa + 16) _, C48x : rw_cells asegs ?mq (sa + 48) _, FR56x : rw_cells asegs ?mq (sa + 56) _,
                         J128x : rw_cells asegs ?mq (sa + 128) _, FPDx : rw_cells asegs ?mq (fr + 112) _, PXDx : rw_cells asegs ?mq pixd (pix_cells vd), URx : rw_cells asegs ?mq (usp + -16) _,
                         MIx : mem_inv asegs ?mq, STx : stk asegs ?mq lo sa, LHx : LIBH ?mq, SSPx : io_ssp ?mq,
                         TAx : u32arr asegs ?mq tv tw, T38x : u32arr asegs ?mq t38 t38w, T14x : u32arr asegs ?mq t14 t14w, AGx : agree_on PF m ?mq
                    |- cps _ (ASTA RT Σt3 _ (eq (MS _ _ _ _ _ ?mq _))) _ =>
      assert (UCXq : chain_ok mq usp fp1 [RA_TOP])
        by (apply (chain_ok_keep [RA_TOP] m mq usp fp1 UCX); eapply agree_sub; [exact AGx|]; cbv beta; intros zx Hzx; apply PFU; unfold USTACK_TOP in Hzx; clear - Hzx; lia);
      eapply (d2_mid2 Σ Σt3 PMc m mq) with (lo := lo) (fr := fr) (pixd := pixd) (dat := dat) (rd := rd) (datas := datas) (rs := rs) (wpls := wpls) (wpld := wpld) (w := w) (h := h)
                                         (fp1 := fp1) (bufs1 := bufs1) (bufs2 := bufs2) (tv := tv) (t38 := t38) (t14 := t14) (vd := vd) (frs0 := frs0) (tw := tw) (t38w := t38w) (t14w := t14w);
      first [ exact FDO | exact MST | exact GEOM | exact DGEOM | exact LVT3 | exact FRSt3 | exact FRS | exact SP0t3 | exact CRt3 | exact ND5 | exact FRESH5
            | exact LVB | exact FRB | exact CRB | exact LVP | exact PXDx | solve [unfold pix_cells; rewrite VW, VH, VD, VWPL, VDAT, VCM; exact PXDx] | exact PDIN | exact DDIN | exact DSIN
            | exact VW | exact VH | exact VD | exact VWPL | exact VDAT | exact VCM | exact UCXq
            | exact A | exact MIx | exact STx | exact LHx | exact SSPx | exact URx | exact FRLOx | exact C48x | exact FR56x | exact J128x | exact FPDx
            | exact TS8 | exact TS4 | exact AGx
            | solve [pose proof HOKD as X; unfold hid in X; exact X]
            | solve [pose proof FP1h as X; unfold hid in X; exact X]
            | solve [split; [exact TAx| split; [exact TAL| split; [exact T38x| split; [exact T38L| split; [exact T14x| exact T14L]]]]]]
            | match goal with |- ?g => idtac "LEFT mid2 apply:" g end ]
    end.
Qed.

End D2MID.
