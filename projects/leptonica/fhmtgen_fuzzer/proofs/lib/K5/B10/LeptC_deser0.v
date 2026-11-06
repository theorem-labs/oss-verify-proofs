(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import ImageA.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import Layout.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_lits Lept_env LeptC_kit LeptL_kit Lept_chain Lept_leaf LeptC_leaf Lept_objkit Lept_deserkit LeptC_deser2_defs Lept_deser_defs LeptC_deser0_defs LeptB_guard LeptB_guard2.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
Lemma lrm_cons0 : forall p e l, live_remove p (e :: l) = if fst e =? p then live_remove p l else e :: live_remove p l.
Proof. intros p e l. unfold live_remove. cbn. destruct (fst e =? p); cbn; reflexivity. Qed.
Lemma lrm_notin0 : forall p (l : list (Z * Z)), (forall e, In e l -> fst e <> p) -> live_remove p l = l.
Proof.
  intros p l. induction l as [|e l IH]; intros H; [reflexivity|]. rewrite lrm_cons0.
  replace (fst e =? p) with false by (symmetry; apply Z.eqb_neq; apply H; left; reflexivity).
  f_equal. apply IH. intros x Hx. apply H. right. exact Hx.
Qed.
Lemma live_destroy_hdr : forall pix v cv (L : list (Z * Z)), p_cmap v = 0 -> p_data v = 0 ->
  (forall e, In e L -> fst e <> pix) -> live_destroy pix v cv ((pix, 64) :: L) = L.
Proof.
  intros pix v cv L HC HD FRESH. unfold live_destroy, rm_opt. rewrite HC, HD. repeat (progress (change (0 =? 0) with true; cbv iota)).
  rewrite lrm_cons0. change (fst (pix, 64)) with pix. rewrite Z.eqb_refl. apply lrm_notin0. exact FRESH.
Qed.

(* [comment removed for export] *)
Lemma rw_cells_join : forall (m : mem) A cs1 B cs2, rw_cells asegs m A cs1 -> rw_cells asegs m B cs2 ->
  B = A + Z.of_nat (cells_size cs1) -> rw_cells asegs m A (cs1 ++ cs2).
Proof. intros m A cs1 B cs2 H1 H2 ->. apply rw_cells_app. split; assumption. Qed.

(* [comment removed for export] *)
Ltac d0_epi_null EPI AGF LVP :=
  eapply EPI with (pixr := 0) (v := mkPixv 0 0 0 0 0 0 0 0 0 0 0) (cv := mkCmapv 0 0 0 0);
  lazymatch goal with
  | |- ART _ _ _ => eassumption
  | |- mem_inv _ _ => assumption
  | |- stk _ _ _ _ => eassumption
  | |- rw_cells _ _ _ _ => eassumption
  | |- wr_at _ _ _ _ => assumption
  | |- LIBH _ => assumption
  | |- io_ssp _ => assumption
  | |- agree_on _ _ _ => exact AGF
  | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
  | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
  | |- _ <= rt_credit _ _ => repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end; lia
  | |- forall e, In e _ -> In e _ => solve [live_sub_tac]
  | |- _ \/ _ => left; reflexivity
  | |- 0 = 0 -> _ => intros _; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity
  | |- 0 <> 0 -> _ => let HH := fresh "HH" in intros HH; contradiction
  | |- forall p k, In (p, k) _ -> 0 < k => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact LVP
  | |- Z.of_nat _ <= _ => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; lia
  end.
Ltac d0_rerr_leaf RT AF GP MST RERR EPI AGF PFS NFA LVP usp lo A W :=
  at_call RT AF ltac:(ds_ivt) ltac:(fun Hx => ds_pft PFS NFA Hx);
  (let RE := fresh "RE" in pose proof RERR as RE; unfold returnError_cps in RE;
   eapply cps_seq; [eapply RE with (lo := lo); rt_side idtac; [lit_in | lit_in | lenv_tac | lres_tac..] |]);
  after_call RT AF;
  fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]);
  ds_refresh RT AF GP;
  ds_walk AF MST W;
  ds_to_epi RT AF AGF PFS NFA A;
  d0_epi_null EPI AGF LVP.

Section DESER0.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis LSE : lept_stderr_cps RT.
Hypothesis RERR : returnError_cps RT e_returnErrorPtr.
Hypothesis HDR : pixCreateHeader_cps RT.
Hypothesis DES : pixDestroy_cps RT.
Variables (Σ : rts RT) (PMc : Model -> Prop) (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (usp lo : Z) (m : mem)
          (QF : config -> Prop) (fr : Z) (dp n : Z) (ras : list Z).

Theorem deser_cut0_ok_0 :
  deser_ctx RT Σ PMc ra s0 usp lo m dp n ras 0xae1bc ->
  deser_epi_stmt_0 RT Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m QF fr ->
  deser_cut1_stmt_0 RT Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m QF fr dp n ->
  deser_cut0_stmt_0 RT Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m QF fr dp n.
Proof using AF RC GP LSE RERR HDR DES.
  (* [comment removed for export] *)
  intros (FDO & MST & ART0 & LOW & LOR & STa & SPT & SPA & SPB & FRB & LVB & CRB & NR & DP0 & DP8 & OWN & UCTX & RA4096 & TRS) EPI CUT1.
  unfold deser_cut0_stmt_0.
  intros Sc mc nc w h d j0 f0 f1 f2 vx px r1 r5 r6 r7 r10 r11 r13 r14 r15 r16 r17 r26 r28 r29 r30 r31 F' fc'
    ARTc MIc STc FR FRM FSH LH SSP AGF FRS ESP0 ECR LVE LVP NCR NSZ WR HR DR.
  unfold deser_epi_stmt_0 in EPI. unfold deser_cut1_stmt_0 in CUT1.
  set (PF := deser_PF RT Σ usp) in *.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  unfold entry_st.
  (* [comment removed for export] *)
  pose proof (af_frames_range RT AF Sc mc fr 1%nat ARTc ltac:(rewrite FRS; left; reflexivity)) as (FR0 & FRHI & _ & _).
  pose proof (af_frames_align RT AF Sc mc fr 1%nat ARTc ltac:(rewrite FRS; left; reflexivity)) as (FR64 & FRSEG).
  pose proof (af_frames_hi RT AF Sc mc fr 1%nat ARTc ltac:(rewrite FRS; left; reflexivity)) as FRSH.
  change (fs_size 1) with 128 in FRHI, FRSH. rewrite ESP0 in FRHI. unfold STACK_WIN, SEGTOP_A in FRHI, FRSEG.
  assert (NFA : forall a, PF a -> (a < fr \/ fr + 128 <= a) /\ (a < shad fr \/ shad (fr + 128) <= a)).
  { intros a Ha. apply (new_frame_apart RT AF Sc mc fr 1%nat (rt_frames RT Σ) (rt_live RT Σ) usp a ARTc FRS);
      [intros e He; rewrite LVE; exact He| rewrite ESP0; lia| rewrite ESP0; unfold STACK_WIN; lia| exact Ha]. }
  assert (FRTOP : fr + 128 <= 140737488355328) by (clear - FRHI SP0R; lia).
  unfold deser_fshadow in FSH.
  pose proof (proj2 FRM) as WFR. cbn [cells_size csize Nat.add] in WFR. change (Z.of_nat 120) with 120 in WFR.
  (* [comment removed for export] *)
  apply (rw_cells_split_CB asegs _ _ [] 48%nat j0 _ [8; 8; 8; 8; 16]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  split_at FRM 2%nat FRmid. split_at FRmid 1%nat FRhi. split_last_CB FRmid [12; 8; 24]%nat.
  (* [comment removed for export] *)
  destruct OWN as (dpp & dpk & DIN0 & DLO & DHI).
  assert (DIN : In (dpp, dpk) (rt_live RT Sc)) by (rewrite LVE; exact DIN0).
  assert (DPP0 : 0 < dpp) by exact (proj1 (af_live_range RT AF Sc mc dpp dpk ARTc DIN)).
  chunk_facts RT AF GP dpp dpk. fframe_chunk RT AF fr 1%nat 128 dpp dpk.
  pose proof (proj1 (af_acc_live RT AF Sc mc dpp dpk ARTc DIN)) as WRDP.
  pose proof (proj2 FSH) as WFS. cbn [cells_size csize Nat.add] in WFS. change (Z.of_nat 16) with 16 in WFS.
  assert (HLO : 1 <= h) by (clear - HR; lia). assert (HHI : h <= 1000000) by (clear - HR; lia).
  assert (WLO : 1 <= w) by (clear - WR; lia). assert (WHI : w <= 1000000) by (clear - WR; lia).
  assert (NLO : 28 <= n) by (clear - NR; lia). assert (NHI : n < 2^26) by (clear - NR; lia).
  assert (NC256 : nc <= 256) by (clear - NCR; lia). assert (DRLO : - 2^31 <= d) by (clear - DR; lia). assert (DRHI : d < 2^31) by (clear - DR; lia).
  assert (NCLO : 0 <= nc) by (clear - NCR; lia). assert (NCHI : nc < 2^31) by (clear - NCR; lia).
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. park_disj.
  Time walk_to AF MST [(usp - 208, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x92034; 0x9267c; 0x912f0; 0x91520; 0xae438; 0xae1c8].
  at_call RT AF ltac:(ds_ivt) ltac:(fun Hx => ds_pft PFS NFA Hx).
  eapply cps_seq.
  { pose proof HDR as HD0; unfold pixCreateHeader_cps in HD0.
    eapply HD0 with (lo := lo) (w := w) (h := h) (d := d); rt_side idtac.
    all: lazymatch goal with
         | |- s32 _ _ => unfold s32; split; [lia| reflexivity]
         | |- lenv _ _ _ _ _ _ => lenv_tac
         | |- lres _ _ _ _ _ => lres_tac
         | |- ?g => idtac "LEFTOVER:" g
         end. }
  Time after_call RT AF.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [intros e He; rewrite LVE; exact He| solve [frames_sub_tac]| lia]| exact I]).
  lazymatch goal with HD : ?p = 0 \/ (pix_obj _ _ ?p ?v _ /\ _) |- _ => rename p into pix1; rename v into v1; rename HD into HOBJ end.
  lazymatch goal with HL : rt_live RT ?X = (if pix1 =? 0 then _ else _) |- _ => rename HL into LV1 end.
  rewrite LVE in LV1.
  lazymatch goal with HF : rt_frames RT _ = rt_frames RT Sc |- _ => rewrite FRS in HF end.
  destruct HOBJ as [PZ|(POBJ & EW & EH & ED & EDATA & ECMAP)].
  1:{ (* [comment removed for export] *)
    subst pix1. change (0 =? 0) with true in LV1. cbv iota in LV1.
    ds_refresh RT AF GP.
    ds_walk AF MST [(usp - 208, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)].
    d0_rerr_leaf RT AF GP MST RERR EPI AGF PFS NFA LVP usp lo (usp + -160) [(usp - 208, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)].
  }
  (* [comment removed for export] *)
  destruct POBJ as (PXC & (INP & PX0 & PX16 & _) & HOK & _ & _).
  destruct v1 as [w1 h1 d1 spp wpl xres yres inf spec pcm data].
  cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data] in *. subst w1 h1 d1 data pcm.
  unfold pix_cells in PXC. cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data] in PXC.
  replace (pix1 =? 0) with false in LV1 by (symmetry; apply Z.eqb_neq; clear - PX0; lia).
  lazymatch goal with A : ART RT ?X ?mm |- cps _ (ASTA RT ?X _ _) _ =>
    pose proof (af_live_disj RT AF X mm pix1 64 dpp dpk [] (rt_live RT Σ) A LV1 DIN0) as PDD end.
  assert (FRESH : forall e, In e (rt_live RT Σ) -> fst e <> pix1).
  { intros [q j] Hq. cbn [fst].
    lazymatch goal with A : ART RT ?X _, LVx : rt_live RT ?X = (pix1, 64) :: _ |- _ =>
      lazymatch type of A with ART RT X ?mm => pose proof (af_live_disj RT AF X mm pix1 64 q j [] (rt_live RT Σ) A LV1 Hq) as DJ end end.
    pose proof (LVP q j Hq) as PJ. clear - DJ PJ. lia. }
  chunk_facts RT AF GP pix1 64. fframe_chunk RT AF fr 1%nat 128 pix1 64.
  assert (HSZ : 0 < 4 * (wpl * h) <= 67108864) by (destruct HOK as (_ & _ & _ & _ & HSZ); cbn [p_wpl p_h] in HSZ; clear - HSZ; lia).
  assert (EWPL : wpl = (w * d + 31) / 32) by (destruct HOK as (_ & _ & _ & HWPL & _); cbn [p_w p_d p_wpl] in HWPL; exact HWPL).
  set (rs := 4 * (wpl * h)) in *.
  assert (RSLO : 0 < rs) by (clear - HSZ; lia). assert (RSHI : rs <= 67108864) by (clear - HSZ; lia).
  ds_refresh RT AF GP.
  Time ds_walk AF MST [(usp - 208, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)].
  replace (bv_swrap 32 (nc + 0)) with nc in * by (rewrite Z.add_0_r; symmetry; apply bv_swrap_small; change (bv_half_modulus 32) with (2^31); clear - NCLO NCHI; lia).
  rewrite ?(Z.mod_small nc 18446744073709551616) in * by (clear - NCLO NCHI; lia).
  (* [comment removed for export] *)
  assert (WPLRb : 0 < wpl <= 16777216) by (pose proof HSZ as T; unfold rs in T; clear - T HLO; nia).
  rewrite ?(unsigned_lit wpl) by (clear - WPLRb; lia). rewrite ?(Z.mod_small (h * 4) 18446744073709551616) by (clear - HLO HHI; lia).
  try (replace (h * 4 * wpl) with rs in * by (unfold rs; ring)).
  rewrite ?(bv_swrap_small 32 rs) by (change (bv_half_modulus 32) with (2^31); clear - HSZ; lia). try br.
  Time ds_awalk.
  (* [comment removed for export] *)
  lazymatch goal with WRx : wr_at asegs ?mm dpp dpk |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (wr_at_sub mm dpp dpk (dp + nc * 4) 28 WRx ltac:(clear - DLO NCLO; lia) ltac:(clear - DHI NSZ; lia) ltac:(clear; lia)) as WRS end.
  apply wr_at_rw_CB in WRS; [| clear; lia]. destruct WRS as (dbs & DBC).
  pose proof DBC as [[[DBL _] _] _]. cbn in DBL. apply u8arr_of_rw_cells in DBC. destruct DBC as [DB _].
  lazymatch type of DB with bytes_at _ ?mm _ _ =>
    destruct (bytes_at_read4w mm (dp + nc * 4) dbs 24 DB ltac:(clear; lia) ltac:(rewrite DBL; clear; lia)) as (wim & RIM) end.
  lstep. clear RIM DB DBL.
  assert (WPLR : 0 < wpl <= 16777216) by (pose proof HSZ as T; unfold rs in T; clear - T HLO; nia).
  rewrite ?(sx32_small wpl) by (clear - WPLR; lia). rewrite ?(unsigned_lit wpl) by (clear - WPLR; lia).
  Time ds_awalk.
  (* [comment removed for export] *)
  try (replace (h * wpl * 4) with rs in * by (unfold rs; ring)).
  rewrite ?(bv_swrap_small 32 rs) in * by (change (bv_half_modulus 32) with (2^31); clear - HSZ; lia).
  (* [comment removed for export] *)
  split_at FRmid 1%nat FRp. split_at FRp 1%nat FRtail.
  pose proof FSH as SHC. split_at SHC 6%nat SHC2. split_at SHC2 1%nat SHC3. clear SHC SHC3.
  pose proof FR as FRrec. split_before FRrec (C8 s0) FRrec3. clear FRrec.
  at_call RT AF ltac:(ds_ivt) ltac:(fun Hx => ds_pft PFS NFA Hx).
  eapply cps_seq.
  { pose proof DES as DY. unfold pixDestroy_cps in DY.
    eapply DY with (lo := lo) (pp := fr + 48) (pix := pix1) (v := mkPixv w h d spp wpl xres yres inf spec 0 0) (cv := mkCmapv 0 0 0 0)
                   (ras := bv_unsigned ra :: ras); rt_side idtac.
    all: lazymatch goal with
         | |- optrL _ _ _ _ _ _ =>
             unfold optrL, parked in *; split;
             [ right; exists fr, 1%nat; change (fs_size 1) with 128;
               split; [repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; left; reflexivity|];
               split; [clear; lia|]; split; [clear; lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
               split; [clear - FR0; lia|]; split; [clear - FRTOP; lia|];
               replace (shad (fr + 48)) with (fr / 8 + 2147450886) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
               destruct SHC2 as [[_ B] _]; exact B
             | split; [clear - FR0; lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|]; split; [clear - FRSH; lia| right; clear - FRSEG; unfold SEGTOP_A; lia] ]
         | |- rw_cells _ _ _ [C8 _] => exact FRp
         | |- pix_obj _ _ _ _ _ =>
             unfold pix_obj, pix_cells, chunk, rsize; cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data];
             split; [exact PXC|]; split; [split; [solve [in_live_tac]| split; [exact PX0| split; [exact PX16| clear; lia]]]|];
             split; [exact HOK|]; split; left; reflexivity
         | |- uctx _ _ _ _ =>
             unfold uctx; rewrite !unsigned_lit by (clear - SPT LOR STa; lia);
             apply chain_ok_push with (fp1 := bv_unsigned s0);
             [ clear; lia | clear - SPA; Z.div_mod_to_equations; lia | unfold USTACK_TOP; clear - SPT; lia
             | split; [exact RA4096| apply bv_unsigned_in_range] | apply bv_unsigned_in_range
             | rewrite !Z_to_bv_bv_unsigned; exact FRrec3
             | eapply chain_ok_keep; [exact UCTX|]; eapply agree_sub; [exact AGF|]; cbv beta; intros xx Hxx; left; exact Hxx ]
         | |- Forall _ _ => rewrite ?unsigned_lit by (clear; lia); exact TRS
         | |- lenv _ _ _ _ _ _ => lenv_tac
         | |- lres _ _ _ _ _ => lres_tac
         | |- ?g => idtac "LEFTOVER:" g
         end. }
  Time after_call RT AF.
  (* [comment removed for export] *)
  lazymatch goal with H : rt_live RT ?X' = live_destroy _ _ _ _ |- _ =>
    rewrite LV1 in H; rewrite (live_destroy_hdr pix1 (mkPixv w h d spp wpl xres yres inf spec 0 0) (mkCmapv 0 0 0 0) (rt_live RT Σ) eq_refl eq_refl FRESH) in H end.
  lazymatch goal with HF : rt_frames RT _ = rt_frames RT ?Y, H2 : rt_frames RT ?Y = (fr, 1%nat) :: _ |- _ => rewrite H2 in HF end.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx);
                                    [intros e He; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact He| solve [frames_sub_tac]| lia]|
                                  cbn [outside]; destruct (NFA _ Hx) as [N1 _]; split; [lia| exact I]]).
  (* [comment removed for export] *)
  lazymatch goal with F1 : rw_cells asegs ?mm fr _, F2 : rw_cells asegs ?mm (fr + 36) _, F3 : rw_cells asegs ?mm (fr + 48) [C8 _],
                      F4 : rw_cells asegs ?mm (fr + 56) _, F5 : rw_cells asegs ?mm (fr + 80) _ |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mm _))) _ =>
    assert (WFR : wr_at asegs mm fr 120)
      by (apply (proj2 (wr_at_app mm fr 36 84 ltac:(lia) ltac:(lia))); split; [exact (proj2 F1)|];
          apply (proj2 (wr_at_app mm (fr + 36) 12 72 ltac:(lia) ltac:(lia))); split; [exact (proj2 F2)|];
          replace (fr + 36 + 12) with (fr + 48) by lia;
          apply (proj2 (wr_at_app mm (fr + 48) 8 64 ltac:(lia) ltac:(lia))); split; [exact (proj2 F3)|];
          replace (fr + 48 + 8) with (fr + 56) by lia;
          apply (proj2 (wr_at_app mm (fr + 56) 24 40 ltac:(lia) ltac:(lia))); split; [exact (proj2 F4)|];
          replace (fr + 56 + 24) with (fr + 80) by lia; exact (proj2 F5)) end.
  ds_refresh RT AF GP.
  Time ds_walk AF MST [(usp - 208, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)].
  (* [comment removed for export] *)
  rewrite ?(bv_swrap_small 32 (n - nc * 4)) by (change (bv_half_modulus 32) with (2^31); clear - NSZ NHI NCLO; lia).
  rewrite ?(Z.mod_small (n - nc * 4) 18446744073709551616) by (clear - NSZ NHI NCLO; lia).
  rewrite ?(bv_swrap_small 32 (n - nc * 4 + -28)) by (change (bv_half_modulus 32) with (2^31); clear - NSZ NHI NCLO; lia).
  brfork HMEM.
  1:{ (* [comment removed for export] *)
    ds_awalk.
    ds_msg_call RT AF GP LSE AGF PFS NFA usp lo [true; false; false; false].
    ds_walk AF MST [(usp - 208, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)].
    ds_to_epi RT AF AGF PFS NFA (usp + -160).
    d0_epi_null EPI AGF LVP.
  }
  ds_awalk.
  brfork HIM.
  1:{ (* [comment removed for export] *)
    ds_awalk.
    ds_msg_call RT AF GP LSE AGF PFS NFA usp lo [true; false; false; false].
    ds_walk AF MST [(usp - 208, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)].
    ds_to_epi RT AF AGF PFS NFA (usp + -160).
    d0_epi_null EPI AGF LVP. }
  (* [comment removed for export] *)
  lazymatch goal with P0 : rw_cells asegs ?mm (fr + 48) [C8 _] |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (rw_cells_join mm (fr + 36) _ (fr + 48) _ FRmid P0 ltac:(cbn [cells_size csize Nat.add]; clear; lia)) as J1 end.
  cbn [app] in J1.
  lazymatch type of J1 with rw_cells _ ?mm _ _ =>
    pose proof (rw_cells_join mm (fr + 36) _ (fr + 56) _ J1 FRtail ltac:(cbn [cells_size csize Nat.add]; clear; lia)) as J2; cbn [app] in J2;
    pose proof (rw_cells_join mm (fr + 36) _ (fr + 80) _ J2 FRhi ltac:(cbn [cells_size csize Nat.add]; clear; lia)) as J3 end.
  lazymatch type of J3 with rw_cells _ ?mm _ (?low ++ ?rest) =>
    pose proof (rw_cells_merge_prefix mm (fr + 36) low rest J3) as J4 end.
  lazymatch type of J4 with context [cells_size ?l] => let sz := eval lazy in (cells_size l) in change (cells_size l) with sz in J4 end.
  lazymatch type of J4 with rw_cells _ ?mm _ _ =>
    pose proof (rw_cells_join mm fr _ (fr + 36) _ FRM J4 ltac:(cbn [cells_size csize Nat.add]; clear; lia)) as J5 end.
  cbn [app] in J5.
  try (replace (dp + nc * 4) with (dp + 4 * nc) in FR by (clear; lia)).
  cps_stop. art_now RT AF ltac:(ds_ivt).
  lazymatch goal with MUx : munch _ ?mm ?mc' |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc' _))) _ =>
    agf_munch AGF MUx ltac:(fun Hx => ds_pft PFS NFA Hx) end.
  to_entry.
  eapply CUT1 with (nc := nc) (w := w) (h := h) (d := d) (psz := rs).
  all: lazymatch goal with
       | |- ART _ _ _ => eassumption
       | |- mem_inv _ _ => assumption
       | |- stk _ _ _ _ => eassumption
       | |- rw_cells _ _ (usp + -160) _ => exact FR
       | |- rw_cells _ _ fr _ => exact J5
       | |- rw_cells _ _ _ deser_fshadow => unfold deser_fshadow; exact FSH
       | |- LIBH _ => assumption
       | |- io_ssp _ => assumption
       | |- agree_on _ _ _ => exact AGF
       | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
       | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
       | |- _ <= rt_credit _ _ => repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end; lia
       | |- rt_live _ _ = _ => assumption
       | |- _ = 4 * _ => unfold rs; rewrite EWPL; reflexivity
       | |- _ = _ - _ - _ => clear - HMEM; lia
       | |- _ <= _ <= _ => first [clear - NCLO NC256; lia | clear - WLO WHI; lia | clear - HLO HHI; lia]
       | |- _ <= _ < _ => clear - DRLO DRHI; lia
       | |- _ < _ <= _ => clear - RSLO RSHI; lia
       | |- ?g => idtac "LEFTOVER:" g
       end.
Qed.
(* [comment removed for export] *)
Theorem deser_cut0_ok_16 :
  deser_ctx RT Σ PMc ra s0 usp lo m dp n ras 0xae1bc ->
  deser_epi_stmt_16 RT Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m QF fr ->
  deser_cut1_stmt_16 RT Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m QF fr dp n ->
  deser_cut0_stmt_16 RT Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m QF fr dp n.
Proof using AF RC GP LSE RERR HDR DES.
  (* [comment removed for export] *)
  intros (FDO & MST & ART0 & LOW & LOR & STa & SPT & SPA & SPB & FRB & LVB & CRB & NR & DP0 & DP8 & OWN & UCTX & RA4096 & TRS) EPI CUT1.
  unfold deser_cut0_stmt_16.
  intros Sc mc nc w h d j0 jp f0 f1 f2 vx px r1 r5 r6 r7 r10 r11 r13 r14 r15 r16 r17 r26 r28 r29 r30 r31 F' fc'
    ARTc MIc STc FR FRM FSH LH SSP AGF FRS ESP0 ECR LVE LVP NCR NSZ WR HR DR.
  unfold deser_epi_stmt_16 in EPI. unfold deser_cut1_stmt_16 in CUT1.
  set (PF := deser_PF RT Σ usp) in *.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  unfold entry_st.
  (* [comment removed for export] *)
  pose proof (af_frames_range RT AF Sc mc fr 1%nat ARTc ltac:(rewrite FRS; left; reflexivity)) as (FR0 & FRHI & _ & _).
  pose proof (af_frames_align RT AF Sc mc fr 1%nat ARTc ltac:(rewrite FRS; left; reflexivity)) as (FR64 & FRSEG).
  pose proof (af_frames_hi RT AF Sc mc fr 1%nat ARTc ltac:(rewrite FRS; left; reflexivity)) as FRSH.
  change (fs_size 1) with 128 in FRHI, FRSH. rewrite ESP0 in FRHI. unfold STACK_WIN, SEGTOP_A in FRHI, FRSEG.
  assert (NFA : forall a, PF a -> (a < fr \/ fr + 128 <= a) /\ (a < shad fr \/ shad (fr + 128) <= a)).
  { intros a Ha. apply (new_frame_apart RT AF Sc mc fr 1%nat (rt_frames RT Σ) (rt_live RT Σ) usp a ARTc FRS);
      [intros e He; rewrite LVE; exact He| rewrite ESP0; lia| rewrite ESP0; unfold STACK_WIN; lia| exact Ha]. }
  assert (FRTOP : fr + 128 <= 140737488355328) by (clear - FRHI SP0R; lia).
  unfold deser_fshadow in FSH.
  pose proof (proj2 FRM) as WFR. cbn [cells_size csize Nat.add] in WFR. change (Z.of_nat 120) with 120 in WFR.
  (* [comment removed for export] *)
  apply (rw_cells_split_CB asegs _ _ [] 48%nat j0 _ [8; 8; 8; 8; 16]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  split_at FRM 2%nat FRmid. split_at FRmid 1%nat FRhi. split_last_CB FRmid [12; 8; 24]%nat.
  (* [comment removed for export] *)
  destruct OWN as (dpp & dpk & DIN0 & DLO & DHI).
  assert (DIN : In (dpp, dpk) (rt_live RT Sc)) by (rewrite LVE; exact DIN0).
  assert (DPP0 : 0 < dpp) by exact (proj1 (af_live_range RT AF Sc mc dpp dpk ARTc DIN)).
  chunk_facts RT AF GP dpp dpk. fframe_chunk RT AF fr 1%nat 128 dpp dpk.
  pose proof (proj1 (af_acc_live RT AF Sc mc dpp dpk ARTc DIN)) as WRDP.
  pose proof (proj2 FSH) as WFS. cbn [cells_size csize Nat.add] in WFS. change (Z.of_nat 16) with 16 in WFS.
  assert (HLO : 1 <= h) by (clear - HR; lia). assert (HHI : h <= 1000000) by (clear - HR; lia).
  assert (WLO : 1 <= w) by (clear - WR; lia). assert (WHI : w <= 1000000) by (clear - WR; lia).
  assert (NLO : 28 <= n) by (clear - NR; lia). assert (NHI : n < 2^26) by (clear - NR; lia).
  assert (NC256 : nc <= 256) by (clear - NCR; lia). assert (DRLO : - 2^31 <= d) by (clear - DR; lia). assert (DRHI : d < 2^31) by (clear - DR; lia).
  assert (NCLO : 0 <= nc) by (clear - NCR; lia). assert (NCHI : nc < 2^31) by (clear - NCR; lia).
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. park_disj.
  Time walk_to AF MST [(usp - 224, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x92034; 0x9267c; 0x912f0; 0x91520; 0xae438; 0xae1c8].
  at_call RT AF ltac:(ds_ivt) ltac:(fun Hx => ds_pft PFS NFA Hx).
  eapply cps_seq.
  { pose proof HDR as HD0; unfold pixCreateHeader_cps in HD0.
    eapply HD0 with (lo := lo) (w := w) (h := h) (d := d); rt_side idtac.
    all: lazymatch goal with
         | |- s32 _ _ => unfold s32; split; [lia| reflexivity]
         | |- lenv _ _ _ _ _ _ => lenv_tac
         | |- lres _ _ _ _ _ => lres_tac
         | |- ?g => idtac "LEFTOVER:" g
         end. }
  Time after_call RT AF.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [intros e He; rewrite LVE; exact He| solve [frames_sub_tac]| lia]| exact I]).
  lazymatch goal with HD : ?p = 0 \/ (pix_obj _ _ ?p ?v _ /\ _) |- _ => rename p into pix1; rename v into v1; rename HD into HOBJ end.
  lazymatch goal with HL : rt_live RT ?X = (if pix1 =? 0 then _ else _) |- _ => rename HL into LV1 end.
  rewrite LVE in LV1.
  lazymatch goal with HF : rt_frames RT _ = rt_frames RT Sc |- _ => rewrite FRS in HF end.
  destruct HOBJ as [PZ|(POBJ & EW & EH & ED & EDATA & ECMAP)].
  1:{ (* [comment removed for export] *)
    subst pix1. change (0 =? 0) with true in LV1. cbv iota in LV1.
    ds_refresh RT AF GP.
    ds_walk AF MST [(usp - 224, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)].
    d0_rerr_leaf RT AF GP MST RERR EPI AGF PFS NFA LVP usp lo (usp + -176) [(usp - 224, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)].
  }
  (* [comment removed for export] *)
  destruct POBJ as (PXC & (INP & PX0 & PX16 & _) & HOK & _ & _).
  destruct v1 as [w1 h1 d1 spp wpl xres yres inf spec pcm data].
  cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data] in *. subst w1 h1 d1 data pcm.
  unfold pix_cells in PXC. cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data] in PXC.
  replace (pix1 =? 0) with false in LV1 by (symmetry; apply Z.eqb_neq; clear - PX0; lia).
  lazymatch goal with A : ART RT ?X ?mm |- cps _ (ASTA RT ?X _ _) _ =>
    pose proof (af_live_disj RT AF X mm pix1 64 dpp dpk [] (rt_live RT Σ) A LV1 DIN0) as PDD end.
  assert (FRESH : forall e, In e (rt_live RT Σ) -> fst e <> pix1).
  { intros [q j] Hq. cbn [fst].
    lazymatch goal with A : ART RT ?X _, LVx : rt_live RT ?X = (pix1, 64) :: _ |- _ =>
      lazymatch type of A with ART RT X ?mm => pose proof (af_live_disj RT AF X mm pix1 64 q j [] (rt_live RT Σ) A LV1 Hq) as DJ end end.
    pose proof (LVP q j Hq) as PJ. clear - DJ PJ. lia. }
  chunk_facts RT AF GP pix1 64. fframe_chunk RT AF fr 1%nat 128 pix1 64.
  assert (HSZ : 0 < 4 * (wpl * h) <= 67108864) by (destruct HOK as (_ & _ & _ & _ & HSZ); cbn [p_wpl p_h] in HSZ; clear - HSZ; lia).
  assert (EWPL : wpl = (w * d + 31) / 32) by (destruct HOK as (_ & _ & _ & HWPL & _); cbn [p_w p_d p_wpl] in HWPL; exact HWPL).
  set (rs := 4 * (wpl * h)) in *.
  assert (RSLO : 0 < rs) by (clear - HSZ; lia). assert (RSHI : rs <= 67108864) by (clear - HSZ; lia).
  ds_refresh RT AF GP.
  Time ds_walk AF MST [(usp - 224, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)].
  replace (bv_swrap 32 (nc + 0)) with nc in * by (rewrite Z.add_0_r; symmetry; apply bv_swrap_small; change (bv_half_modulus 32) with (2^31); clear - NCLO NCHI; lia).
  rewrite ?(Z.mod_small nc 18446744073709551616) in * by (clear - NCLO NCHI; lia).
  (* [comment removed for export] *)
  assert (WPLRb : 0 < wpl <= 16777216) by (pose proof HSZ as T; unfold rs in T; clear - T HLO; nia).
  rewrite ?(unsigned_lit wpl) by (clear - WPLRb; lia). rewrite ?(Z.mod_small (h * 4) 18446744073709551616) by (clear - HLO HHI; lia).
  try (replace (h * 4 * wpl) with rs in * by (unfold rs; ring)).
  rewrite ?(bv_swrap_small 32 rs) by (change (bv_half_modulus 32) with (2^31); clear - HSZ; lia). try br.
  Time ds_awalk.
  (* [comment removed for export] *)
  lazymatch goal with WRx : wr_at asegs ?mm dpp dpk |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (wr_at_sub mm dpp dpk (dp + nc * 4) 28 WRx ltac:(clear - DLO NCLO; lia) ltac:(clear - DHI NSZ; lia) ltac:(clear; lia)) as WRS end.
  apply wr_at_rw_CB in WRS; [| clear; lia]. destruct WRS as (dbs & DBC).
  pose proof DBC as [[[DBL _] _] _]. cbn in DBL. apply u8arr_of_rw_cells in DBC. destruct DBC as [DB _].
  lazymatch type of DB with bytes_at _ ?mm _ _ =>
    destruct (bytes_at_read4w mm (dp + nc * 4) dbs 24 DB ltac:(clear; lia) ltac:(rewrite DBL; clear; lia)) as (wim & RIM) end.
  lstep. clear RIM DB DBL.
  assert (WPLR : 0 < wpl <= 16777216) by (pose proof HSZ as T; unfold rs in T; clear - T HLO; nia).
  rewrite ?(sx32_small wpl) by (clear - WPLR; lia). rewrite ?(unsigned_lit wpl) by (clear - WPLR; lia).
  Time ds_awalk.
  (* [comment removed for export] *)
  try (replace (h * wpl * 4) with rs in * by (unfold rs; ring)).
  rewrite ?(bv_swrap_small 32 rs) in * by (change (bv_half_modulus 32) with (2^31); clear - HSZ; lia).
  (* [comment removed for export] *)
  split_at FRmid 1%nat FRp. split_at FRp 1%nat FRtail.
  pose proof FSH as SHC. split_at SHC 6%nat SHC2. split_at SHC2 1%nat SHC3. clear SHC SHC3.
  pose proof FR as FRrec. split_before FRrec (C8 s0) FRrec3. clear FRrec.
  at_call RT AF ltac:(ds_ivt) ltac:(fun Hx => ds_pft PFS NFA Hx).
  eapply cps_seq.
  { pose proof DES as DY. unfold pixDestroy_cps in DY.
    eapply DY with (lo := lo) (pp := fr + 48) (pix := pix1) (v := mkPixv w h d spp wpl xres yres inf spec 0 0) (cv := mkCmapv 0 0 0 0)
                   (ras := bv_unsigned ra :: ras); rt_side idtac.
    all: lazymatch goal with
         | |- optrL _ _ _ _ _ _ =>
             unfold optrL, parked in *; split;
             [ right; exists fr, 1%nat; change (fs_size 1) with 128;
               split; [repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; left; reflexivity|];
               split; [clear; lia|]; split; [clear; lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
               split; [clear - FR0; lia|]; split; [clear - FRTOP; lia|];
               replace (shad (fr + 48)) with (fr / 8 + 2147450886) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
               destruct SHC2 as [[_ B] _]; exact B
             | split; [clear - FR0; lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|]; split; [clear - FRSH; lia| right; clear - FRSEG; unfold SEGTOP_A; lia] ]
         | |- rw_cells _ _ _ [C8 _] => exact FRp
         | |- pix_obj _ _ _ _ _ =>
             unfold pix_obj, pix_cells, chunk, rsize; cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data];
             split; [exact PXC|]; split; [split; [solve [in_live_tac]| split; [exact PX0| split; [exact PX16| clear; lia]]]|];
             split; [exact HOK|]; split; left; reflexivity
         | |- uctx _ _ _ _ =>
             unfold uctx; rewrite !unsigned_lit by (clear - SPT LOR STa; lia);
             apply chain_ok_push with (fp1 := bv_unsigned s0);
             [ clear; lia | clear - SPA; Z.div_mod_to_equations; lia | unfold USTACK_TOP; clear - SPT; lia
             | split; [exact RA4096| apply bv_unsigned_in_range] | apply bv_unsigned_in_range
             | rewrite !Z_to_bv_bv_unsigned; exact FRrec3
             | eapply chain_ok_keep; [exact UCTX|]; eapply agree_sub; [exact AGF|]; cbv beta; intros xx Hxx; left; exact Hxx ]
         | |- Forall _ _ => rewrite ?unsigned_lit by (clear; lia); exact TRS
         | |- lenv _ _ _ _ _ _ => lenv_tac
         | |- lres _ _ _ _ _ => lres_tac
         | |- ?g => idtac "LEFTOVER:" g
         end. }
  Time after_call RT AF.
  (* [comment removed for export] *)
  lazymatch goal with H : rt_live RT ?X' = live_destroy _ _ _ _ |- _ =>
    rewrite LV1 in H; rewrite (live_destroy_hdr pix1 (mkPixv w h d spp wpl xres yres inf spec 0 0) (mkCmapv 0 0 0 0) (rt_live RT Σ) eq_refl eq_refl FRESH) in H end.
  lazymatch goal with HF : rt_frames RT _ = rt_frames RT ?Y, H2 : rt_frames RT ?Y = (fr, 1%nat) :: _ |- _ => rewrite H2 in HF end.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx);
                                    [intros e He; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact He| solve [frames_sub_tac]| lia]|
                                  cbn [outside]; destruct (NFA _ Hx) as [N1 _]; split; [lia| exact I]]).
  (* [comment removed for export] *)
  lazymatch goal with F1 : rw_cells asegs ?mm fr _, F2 : rw_cells asegs ?mm (fr + 36) _, F3 : rw_cells asegs ?mm (fr + 48) [C8 _],
                      F4 : rw_cells asegs ?mm (fr + 56) _, F5 : rw_cells asegs ?mm (fr + 80) _ |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mm _))) _ =>
    assert (WFR : wr_at asegs mm fr 120)
      by (apply (proj2 (wr_at_app mm fr 36 84 ltac:(lia) ltac:(lia))); split; [exact (proj2 F1)|];
          apply (proj2 (wr_at_app mm (fr + 36) 12 72 ltac:(lia) ltac:(lia))); split; [exact (proj2 F2)|];
          replace (fr + 36 + 12) with (fr + 48) by lia;
          apply (proj2 (wr_at_app mm (fr + 48) 8 64 ltac:(lia) ltac:(lia))); split; [exact (proj2 F3)|];
          replace (fr + 48 + 8) with (fr + 56) by lia;
          apply (proj2 (wr_at_app mm (fr + 56) 24 40 ltac:(lia) ltac:(lia))); split; [exact (proj2 F4)|];
          replace (fr + 56 + 24) with (fr + 80) by lia; exact (proj2 F5)) end.
  ds_refresh RT AF GP.
  Time ds_walk AF MST [(usp - 224, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)].
  (* [comment removed for export] *)
  rewrite ?(bv_swrap_small 32 (n - nc * 4)) by (change (bv_half_modulus 32) with (2^31); clear - NSZ NHI NCLO; lia).
  rewrite ?(Z.mod_small (n - nc * 4) 18446744073709551616) by (clear - NSZ NHI NCLO; lia).
  rewrite ?(bv_swrap_small 32 (n - nc * 4 + -28)) by (change (bv_half_modulus 32) with (2^31); clear - NSZ NHI NCLO; lia).
  brfork HMEM.
  1:{ (* [comment removed for export] *)
    ds_awalk.
    ds_msg_call RT AF GP LSE AGF PFS NFA usp lo [true; false; false; false].
    ds_walk AF MST [(usp - 224, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)].
    ds_to_epi RT AF AGF PFS NFA (usp + -176).
    d0_epi_null EPI AGF LVP.
  }
  ds_awalk.
  brfork HIM.
  1:{ (* [comment removed for export] *)
    ds_awalk.
    ds_msg_call RT AF GP LSE AGF PFS NFA usp lo [true; false; false; false].
    ds_walk AF MST [(usp - 224, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)].
    ds_to_epi RT AF AGF PFS NFA (usp + -176).
    d0_epi_null EPI AGF LVP. }
  (* [comment removed for export] *)
  lazymatch goal with P0 : rw_cells asegs ?mm (fr + 48) [C8 _] |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (rw_cells_join mm (fr + 36) _ (fr + 48) _ FRmid P0 ltac:(cbn [cells_size csize Nat.add]; clear; lia)) as J1 end.
  cbn [app] in J1.
  lazymatch type of J1 with rw_cells _ ?mm _ _ =>
    pose proof (rw_cells_join mm (fr + 36) _ (fr + 56) _ J1 FRtail ltac:(cbn [cells_size csize Nat.add]; clear; lia)) as J2; cbn [app] in J2;
    pose proof (rw_cells_join mm (fr + 36) _ (fr + 80) _ J2 FRhi ltac:(cbn [cells_size csize Nat.add]; clear; lia)) as J3 end.
  lazymatch type of J3 with rw_cells _ ?mm _ (?low ++ ?rest) =>
    pose proof (rw_cells_merge_prefix mm (fr + 36) low rest J3) as J4 end.
  lazymatch type of J4 with context [cells_size ?l] => let sz := eval lazy in (cells_size l) in change (cells_size l) with sz in J4 end.
  lazymatch type of J4 with rw_cells _ ?mm _ _ =>
    pose proof (rw_cells_join mm fr _ (fr + 36) _ FRM J4 ltac:(cbn [cells_size csize Nat.add]; clear; lia)) as J5 end.
  cbn [app] in J5.
  try (replace (dp + nc * 4) with (dp + 4 * nc) in FR by (clear; lia)).
  cps_stop. art_now RT AF ltac:(ds_ivt).
  lazymatch goal with MUx : munch _ ?mm ?mc' |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc' _))) _ =>
    agf_munch AGF MUx ltac:(fun Hx => ds_pft PFS NFA Hx) end.
  to_entry.
  eapply CUT1 with (nc := nc) (w := w) (h := h) (d := d) (psz := rs).
  all: lazymatch goal with
       | |- ART _ _ _ => eassumption
       | |- mem_inv _ _ => assumption
       | |- stk _ _ _ _ => eassumption
       | |- rw_cells _ _ (usp + -176) _ => exact FR
       | |- rw_cells _ _ fr _ => exact J5
       | |- rw_cells _ _ _ deser_fshadow => unfold deser_fshadow; exact FSH
       | |- LIBH _ => assumption
       | |- io_ssp _ => assumption
       | |- agree_on _ _ _ => exact AGF
       | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
       | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
       | |- _ <= rt_credit _ _ => repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end; lia
       | |- rt_live _ _ = _ => assumption
       | |- _ = 4 * _ => unfold rs; rewrite EWPL; reflexivity
       | |- _ = _ - _ - _ => clear - HMEM; lia
       | |- _ <= _ <= _ => first [clear - NCLO NC256; lia | clear - WLO WHI; lia | clear - HLO HHI; lia]
       | |- _ <= _ < _ => clear - DRLO DRHI; lia
       | |- _ < _ <= _ => clear - RSLO RSHI; lia
       | |- ?g => idtac "LEFTOVER:" g
       end.
Qed.
End DESER0.
