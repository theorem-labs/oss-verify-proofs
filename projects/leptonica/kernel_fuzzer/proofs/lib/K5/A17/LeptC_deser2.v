(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.A17 Require Import ImageA.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.A17 Require Import Layout.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.A17 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_lits Lept_env LeptC_kit Lept_chain Lept_leaf LeptC_leaf Lept_objkit Lept_deserkit LeptC_deser2_defs.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
Lemma live_remove_ne : forall (l : list (Z * Z)) p e, In e (live_remove p l) -> fst e <> p.
Proof.
  intros l p e He. unfold live_remove in He. apply stdpp.base.list_elem_of_In in He.
  apply stdpp.list_basics.list.list_elem_of_filter in He. destruct He as [HP _]. intros E. rewrite E, Z.eqb_refl in HP. exact HP.
Qed.
Lemma live_destroy_in_ne : forall pix v cv (live : list (Z * Z)) q k, p_data v <> 0 ->
  In (q, k) (live_destroy pix v cv live) -> q <> pix /\ q <> p_data v.
Proof.
  intros pix v cv live q k HD H. unfold live_destroy in H.
  split; [exact (live_remove_ne _ _ _ H)|]. apply live_remove_sub in H.
  assert (SUB : forall p l (e : Z * Z), In e (rm_opt p l) -> In e l).
  { intros p l e He. unfold rm_opt in He. destruct (p =? 0); [exact He| exact (live_remove_sub l p e He)]. }
  apply SUB in H. apply SUB in H. unfold rm_opt in H. replace (p_data v =? 0) with false in H by (symmetry; apply Z.eqb_neq; exact HD).
  exact (live_remove_ne _ _ _ H).
Qed.

(* [comment removed for export] *)
Lemma cmap_alt_agree : forall (live : list (Z * Z)) (P : Z -> Prop) (m m' : mem) pcm cv (X : Prop),
  (pcm = 0 \/ (cmap_obj live m pcm cv /\ X)) -> agree_on P m m' ->
  (forall a, cmap_obj live m pcm cv -> X -> pcm <= a < pcm + 24 -> P a) ->
  (pcm = 0 \/ (cmap_obj live m' pcm cv /\ X)).
Proof.
  intros live P m m' pcm cv X [Z0|(CMO & HX)] AG HP; [left; exact Z0| right]. split; [| exact HX].
  pose proof CMO as ((pad & CMC) & R). split; [| exact R]. exists pad.
  apply (rw_cells_agree_nw asegs m m' _ _ CMC). intros a Ha. apply AG. apply (HP _ CMO HX).
  cbn [cells_size cmap_cells csize Nat.add] in Ha. lia.
Qed.

Section Apart.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
(* [comment removed for export] *)
Lemma later_chunk_apart : forall (S : rts RT) (mc : mem) p k live0 frs usp a,
  ART RT S mc -> In (p, k) (rt_live RT S) -> (forall q j, In (q, j) live0 -> In (q, j) (rt_live RT S) /\ q <> p) ->
  (forall e, In e frs -> In e (rt_frames RT S)) -> rt_sp0 RT S - STACK_WIN <= usp ->
  aclient live0 frs usp a -> a < p \/ p + k <= a.
Proof using AF.
  intros S mc p k live0 frs usp a HA INL OLD FSUB SPL Ha.
  pose proof (af_live_range RT AF S mc p k HA INL) as (P0 & PHI & PSEG).
  unfold STACK_WIN, USTACK_TOP, SEGTOP_A in *.
  destruct Ha as [H|[H|[H|[H|H]]]].
  - right. lia.
  - pose proof (client_static_below a H) as HB. unfold SEGTOP_A in HB. pose proof (client_static_lo a H) as HL. lia.
  - destruct H as (q & j & Hin & Hq). destruct (OLD q j Hin) as [Hin' NE].
    pose proof (live_apart RT AF S mc p k q j HA INL Hin' ltac:(intros E; apply NE; symmetry; exact E)) as D. lia.
  - destruct H as (f & kk & Hin & Hf). apply FSUB in Hin.
    pose proof (af_frames_range RT AF S mc f kk HA Hin) as (_ & _ & _ & FLV). specialize (FLV p k INL). lia.
  - destruct H as (f & kk & Hin & Hf). apply FSUB in Hin.
    pose proof (af_fshadow_apart RT AF S mc f kk HA Hin) as (SA1 & _). specialize (SA1 p k INL). lia.
Qed.
End Apart.

(* [comment removed for export] *)
Ltac pcm_over_walk RT AF Sc mc ARTc ESP0 LOW PCM pcm cv lo side :=
  lazymatch type of PCM with _ \/ (cmap_obj ?live ?ma _ _ /\ ?X) =>
    lazymatch goal with MUx : munch ?W ma ?mb |- _ =>
      let AGW := fresh "AGW" in
      assert (AGW : agree_on (fun a => a < lo) ma mb)
        by (apply (agree_of_munch W ma mb (fun a => a < lo) MUx);
            let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; cbn [outside]; side Hx);
      let N := fresh "PCM" in
      assert (N : pcm = 0 \/ (cmap_obj live mb pcm cv /\ X))
        by (apply (cmap_alt_agree live (fun a => a < lo) ma mb pcm cv X PCM AGW);
            let a := fresh "a" in let CIN := fresh "CIN" in let Ha := fresh "Ha" in let LR := fresh "LR" in
            intros a (_ & (CIN & _) & _) _ Ha;
            pose proof (af_live_range RT AF Sc mc pcm 24 ARTc CIN) as (_ & LR & _); unfold STACK_WIN in LR; rewrite ESP0 in LR; clear - LR LOW Ha; lia);
      clear PCM AGW; rename N into PCM
    end end.
(* [comment removed for export] *)
Ltac pcm_over_call PCM pcm cv side :=
  lazymatch type of PCM with _ \/ (cmap_obj ?live ?ma _ _ /\ ?X) =>
    lazymatch goal with AGx : agree_on ?P ma ?mb |- _ =>
      let N := fresh "PCM" in
      assert (N : pcm = 0 \/ (cmap_obj live mb pcm cv /\ X))
        by (apply (cmap_alt_agree live P ma mb pcm cv X PCM AGx); side);
      clear PCM; rename N into PCM
    end end.

Section DESER2.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis RERR : returnError_cps RT e_returnErrorPtr.
Hypothesis DES : pixDestroy_cps RT.
Hypothesis VAL : pixcmapIsValid_cps RT.
Variables (Σ : rts RT) (PMc : Model -> Prop) (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (usp lo : Z) (m : mem)
          (QF : config -> Prop) (fr : Z) (dp n : Z) (ras : list Z).

Theorem deser_cut2_ok_0 :
  deser_ctx RT Σ PMc ra s0 usp lo m dp n ras 0x90b58 ->
  deser_epi_stmt_0 RT Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m QF fr ->
  deser_cut2_stmt_0 RT Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m QF fr dp n.
Proof using AF RC GP RERR DES VAL.
  (* [comment removed for export] *)
  intros (FDO & MST & ART0 & LOW & LOR & STa & SPT & SPA & SPB & FRB & LVB & CRB & NR & DP0 & DP8 & OWN & UCTX & RA4096 & TRS) EPI. unfold deser_cut2_stmt_0.
  intros Sc mc pixd cm nc v cv j0 j1 f0 f1 f2 c24 c40 c48 vx r1 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 r21 r22 r24 r26 r28 r29 r30 r31 F' fc'
    ARTc MIc STc FR FRM FSH LH SSP AGF FRS ESP0 ECR LSUB POBJ PDNZ NCR CMF CMZ PSZ LDES LVP LLEN.
  unfold deser_epi_stmt_0 in EPI.
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
  { intros a Ha. apply (new_frame_apart RT AF Sc mc fr 1%nat (rt_frames RT Σ) (rt_live RT Σ) usp a ARTc FRS LSUB);
      [rewrite ESP0; lia| rewrite ESP0; unfold STACK_WIN; lia| exact Ha]. }
  (* [comment removed for export] *)
  destruct POBJ as (PXC & (INP & PX0 & PX16 & _) & HOK & DAT & PCM).
  destruct DAT as [E|((IND & DA0 & DA16 & DAN) & DNE)]; [contradiction|].
  destruct v as [w h d spp wpl xres yres inf spec pcm data].
  cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data] in *.
  unfold pix_cells in PXC. cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data] in PXC.
  unfold rsize in *. cbn [p_wpl p_h] in *.
  set (rs := 4 * (wpl * h)) in *.
  (* [comment removed for export] *)
  assert (OLDNE : forall q j, In (q, j) (rt_live RT Σ) -> q <> pixd /\ q <> data).
  { intros q j Hq. rewrite <- LDES in Hq. exact (live_destroy_in_ne pixd (mkPixv w h d spp wpl xres yres inf spec pcm data) cv _ q j PDNZ Hq). }
  (* [comment removed for export] *)
  destruct OWN as (dpp & dpk & DIN0 & DLO & DHI).
  pose proof (LSUB _ DIN0) as DIN.
  pose proof (proj2 (OLDNE _ _ DIN0)) as DPNE. pose proof (proj1 (OLDNE _ _ DIN0)) as DPNP.
  pose proof (live_apart RT AF Sc mc data (rs) dpp dpk ARTc IND DIN ltac:(intros E; apply DPNE; symmetry; exact E)) as RAWD.
  pose proof (live_apart RT AF Sc mc data (rs) pixd 64 ARTc IND INP DNE) as DPD.
  (* [comment removed for export] *)
  assert (NCD : forall a, PF a -> a < data \/ data + rs <= a).
  { intros a Ha. apply (later_chunk_apart RT AF Sc mc data (rs) (rt_live RT Σ) (rt_frames RT Σ) usp a ARTc IND);
      [intros q j Hq; split; [exact (LSUB _ Hq)| exact (proj2 (OLDNE q j Hq))]| intros e He; rewrite FRS; right; exact He
      | rewrite ESP0; unfold STACK_WIN; lia| exact Ha]. }
  assert (NCP : forall a, PF a -> a < pixd \/ pixd + 64 <= a).
  { intros a Ha. apply (later_chunk_apart RT AF Sc mc pixd 64 (rt_live RT Σ) (rt_frames RT Σ) usp a ARTc INP);
      [intros q j Hq; split; [exact (LSUB _ Hq)| exact (proj1 (OLDNE q j Hq))]| intros e He; rewrite FRS; right; exact He
      | rewrite ESP0; unfold STACK_WIN; lia| exact Ha]. }
  chunk_facts RT AF GP pixd 64. chunk_facts RT AF GP data (rs). chunk_facts RT AF GP dpp dpk.
  fframe_chunk RT AF fr 1%nat 128 pixd 64. fframe_chunk RT AF fr 1%nat 128 data (rs). fframe_chunk RT AF fr 1%nat 128 dpp dpk.
  pose proof (proj1 (af_acc_live RT AF Sc mc dpp dpk ARTc DIN)) as WRDP.
  pose proof (proj1 (af_acc_live RT AF Sc mc data (rs) ARTc IND)) as WRRA.
  pose proof (proj2 FRM) as WFR. pose proof (proj2 FSH) as WFS. cbn [cells_size csize Nat.add deser_fshadow] in WFR, WFS.
  change (Z.of_nat 120) with 120 in WFR. change (Z.of_nat 16) with 16 in WFS.
  unfold deser_fshadow in FSH.
  assert (FRTOP : fr + 128 <= 140737488355328) by (clear - FRHI SP0R; lia).
  assert (NCPOS : nc <> 0 -> 0 < nc) by (clear - NCR; lia).
  assert (DPP0 : 0 < dpp) by exact (proj1 (af_live_range RT AF Sc mc dpp dpk ARTc DIN)).
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. park_disj.
  Time walk_to AF MST [(usp - 208, usp)] [0x5ca54; 0x8ef28; 0x8db30; 0x8cf08; 0x90b94].
  (* [comment removed for export] *)
  lazymatch goal with H : wr_at asegs ?mm dpp dpk |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (wr_at_sub mm dpp dpk (dp + 4 * nc + 28) (rs) H ltac:(clear - DLO NCR; lia) ltac:(clear - DHI PSZ; lia) ltac:(clear - DAN; lia)) as WRS end.
  apply wr_at_rw_CB in WRS; [| clear - DAN; lia]. destruct WRS as (sbs & SBC).
  pose proof SBC as [[[SBL _] _] _]. cbn in SBL. apply u8arr_of_rw_cells in SBC. destruct SBC as [SB _].
  assert (SBL' : Z.of_nat (length sbs) = rs) by (rewrite SBL; clear - DAN; lia).
  assert (HSZ : rs <= 67108864) by (destruct HOK as (_ & _ & _ & _ & HSZ); cbn [p_wpl p_h] in HSZ; unfold rs; clear - HSZ; lia).
  assert (Q1 : 0 <= data <= 2^47) by (clear - DA0 CKR0 SP0R DAN; lia).
  assert (Q2 : 0 <= dp + 4 * nc + 28 <= 2^47) by (clear - DP0 NCR DLO DHI CKR1 SP0R NR; lia).
  assert (Q3 : data + rs <= dp + 4 * nc + 28 \/ dp + 4 * nc + 28 + rs <= data)
    by (clear - RAWD DLO DHI PSZ NCR; unfold parked in RAWD; lia).
  assert (Q4 : dp + 4 * nc + 28 + rs <= lo) by (clear - DHI PSZ CKR1 LOW; lia).
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                ltac:(fun Hx => cbn [outside]; split; [destruct (PFS _ Hx); lia| exact I]).
  pcm_over_walk RT AF Sc mc ARTc ESP0 LOW PCM pcm cv lo ltac:(fun Hx => split; [clear - Hx LOR; lia| exact I]).
  eapply cps_seq.
  { pose proof (rc_asan_memcpy RT RC) as MC0; unfold memcpy_icontract in MC0;
    eapply MC0 with (lo := lo) (d := data) (s := dp + 4 * nc + 28) (bs := sbs); rewrite ?SBL'.
    all: lazymatch goal with
         | |- fdfs_only _ => exact FDO
         | |- mat_stable _ => exact MST
         | |- Z_to_bv 64 _ = Z_to_bv 64 _ => reflexivity
         | |- bytes_at _ _ _ _ => exact SB
         | |- ART _ _ _ => assumption
         | |- mem_inv _ _ => assumption
         | |- checked_src _ _ _ _ _ _ _ =>
             unfold checked_src; rewrite ?unsigned_lit by (clear - SPT LOR STa; lia);
             split; [intros _; split; [apply (acc_sub asegs _ dpp dpk); [assumption| clear - DLO NCR; lia| clear - DHI PSZ; lia]|
                                       left; exists dpp, dpk; split; [exact DIN| clear - DLO DHI PSZ NCR; lia]]| left; exact Q4]
         | |- checked_dst _ _ _ _ _ _ =>
             unfold checked_dst; rewrite ?unsigned_lit by (clear - SPT LOR STa; lia);
             split; [intros _; split; [assumption| left; exists data, (rs); split; [exact IND| clear; lia]]|];
             split; [intros i Hi; right; right; left; exists data, (rs); split; [exact IND| clear - Hi; lia]| assumption]
         | |- call_ok _ _ _ _ _ =>
             unfold call_ok; rewrite ?unsigned_lit by (clear - SPT LOR STa; lia); split; [assumption|];
             rewrite ESP0; unfold STACK_WIN, RT_STACK, USTACK_TOP; clear - LOW LOR SPT SPA; repeat split; first [lia | Z.div_mod_to_equations; lia]
         | |- _ \/ _ => exact Q3
         | |- (_ <= _ <= _) => first [exact Q1 | exact Q2]
         | |- (_ < _) => clear - HSZ; lia
         | |- ?g => idtac "LEFTOVER:" g
         end. }
  rewrite SBL'. clear SB.
  Time after_call RT AF.
  (* [comment removed for export] *)
  pcm_over_call PCM pcm cv ltac:(intros a (_ & (CIN & _) & _) (_ & _ & CND & _) Ha; split;
            [right; right; left; exists pcm, 24; split; [exact CIN| exact Ha]|
             pose proof (live_apart RT AF Sc mc pcm 24 data rs ARTc CIN IND CND) as LAP; clear - LAP Ha; lia]).
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [exact LSUB| solve [frames_sub_tac]| lia]| pose proof (NCD _ Hx); lia]).
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. park_disj.
  Time walk_to AF MST [(usp - 208, usp)] [0x8ef28; 0x8db30; 0x8cf08; 0x90b94].
  brfork HNC.
  1:{ (* [comment removed for export] *)
    cwalk [0x90b94].
    cps_stop. art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I]).
    lazymatch goal with MUx : munch _ ?mm ?mc' |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc' _))) _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; split; [destruct (PFS _ Hx); lia| exact I]) end.
    lazymatch goal with FRx : rw_cells asegs _ (usp + -192) _ |- _ => merge_low FRx 13%nat end.
    to_entry.
    eapply EPI with (pixr := pixd) (v := mkPixv w h d spp wpl xres yres inf spec pcm data) (cv := cv).
    all: lazymatch goal with
         | |- ART _ _ _ => eassumption
         | |- mem_inv _ _ => assumption
         | |- stk _ _ _ _ => assumption
         | |- rw_cells _ _ _ _ => lazymatch goal with FRx : rw_cells asegs _ (usp + -192) _ |- _ => exact FRx end
         | |- wr_at _ _ _ _ => assumption
         | |- LIBH _ => assumption
         | |- io_ssp _ => assumption
         | |- agree_on _ _ _ => exact AGF
         | |- rt_frames _ _ = _ => exact FRS
         | |- rt_sp0 _ _ = _ => exact ESP0
         | |- _ <= rt_credit _ _ => clear - ECR; lia
         | |- forall e, In e _ -> In e _ => exact LSUB
         | |- _ \/ _ =>
             right; split; [| exact PDNZ];
             unfold pix_obj, pix_cells, chunk, rsize; cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data];
             split; [exact PXC|]; split; [split; [exact INP| split; [exact PX0| split; [exact PX16| clear; lia]]]|];
             split; [exact HOK|]; split; [right; split; [split; [exact IND| split; [exact DA0| split; [exact DA16| exact DAN]]]| exact DNE]| exact PCM]
         | |- _ = 0 -> _ => intros E0; exfalso; clear - E0 PX0; lia
         | |- _ <> 0 -> _ => intros _; exact LDES
         | |- forall p k, In (p, k) _ -> 0 < k => exact LVP
         | |- Z.of_nat _ <= _ => exact LLEN
         | |- ?g => idtac "LEFTOVER:" g
         end.
  }
  (* [comment removed for export] *)
  pose proof (NCPOS HNC) as NC0.
  destruct (CMF NC0) as [CMNZ PCME]. subst cm.
  cwalk [0x8ef28].
  split_at FRM 1%nat FRv. split_at FRv 1%nat FRrest.
  lazymatch type of FSH with rw_cells _ ?mm _ _ => assert (SHV : bytes_at asegs mm (shad (fr + 32)) (ushadow 4)) end.
  { pose proof (rw_cells_head _ _ _ _ (rw_cells_tail _ _ _ _ (rw_cells_tail _ _ _ _ (rw_cells_tail _ _ _ _ (rw_cells_tail _ _ _ _ FSH))))) as [[_ X] _].
    cbn [cells_bytes cbytes app csize Z.of_nat Pos.of_succ_nat Pos.succ] in X.
    replace (shad (fr + 32)) with (fr / 8 + 2147450880 + 1 + 1 + 1 + 1) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia). exact X. }
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                ltac:(fun Hx => cbn [outside]; split; [destruct (PFS _ Hx); lia| exact I]).
  pcm_over_walk RT AF Sc mc ARTc ESP0 LOW PCM pcm cv lo ltac:(fun Hx => split; [clear - Hx LOR; lia| exact I]).
  pose proof PCM as PCMd. destruct PCMd as [PZ|(CMO & CNP & CAP & CND & CAD)]; [exfalso; exact (CMNZ PZ)|].
  pose proof CMO as (_ & (CIN & CP0 & CP16 & _) & _).
  fframe_chunk RT AF fr 1%nat 128 pcm 24.
  eapply cps_seq.
  { pose proof VAL as VL; unfold pixcmapIsValid_cps in VL.
    eapply VL with (lo := lo) (cmap := pcm) (pix := pixd) (pv := fr + 32) (cv := cv)
                   (v := mkPixv w h d spp wpl xres yres inf spec pcm data) (x := vx); rt_side idtac.
    all: lazymatch goal with
         | |- cmap_obj _ _ _ _ => exact CMO
         | |- _ \/ _ =>
             right; split; [| split; [exact PDNZ| reflexivity]];
             unfold pix_obj, pix_cells, chunk, rsize; cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data];
             split; [exact PXC|]; split; [split; [exact INP| split; [exact PX0| split; [exact PX16| clear; lia]]]|];
             split; [exact HOK|]; split; [right; split; [split; [exact IND| split; [exact DA0| split; [exact DA16| exact DAN]]]| exact DNE]| exact PCM]
         | |- optrF _ _ _ _ _ =>
             unfold optrF, own_frame; unfold parked in FRSH; split;
             [ exists fr, 1%nat; change (fs_size 1) with 128;
               split; [rewrite FRS; left; reflexivity|]; split; [clear; lia|]; split; [clear; lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
               split; [clear - FR0; lia|]; split; [clear - FRTOP; lia| exact SHV]
             | split; [clear - FR0; lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|]; split; [clear - FRSH; lia| right; clear - FRSEG; unfold SEGTOP_A; lia] ]
         | |- rw_cells _ _ _ [C4 _] => exact FRv
         | |- lenv _ _ _ _ _ _ => lenv_tac
         | |- lres _ _ _ _ _ => lres_tac
         | |- ?g => idtac "LEFTOVER:" g
         end. }
  Time after_call RT AF.
  pcm_over_call PCM pcm cv ltac:(intros a (_ & (CIN' & _) & _) _ Ha; split;
            [right; right; left; exists pcm, 24; split; [solve [in_live_tac]| exact Ha]|
             cbn [outside]; split; [match goal with H : context [pcm + 24 <= fr] |- _ => clear - H Ha; unfold parked in H; lia end| exact I]]).
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx);
                                    [intros e He; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact (LSUB e He)| solve [frames_sub_tac]| lia]|
                                  cbn [outside]; destruct (NFA _ Hx) as [N1 _]; split; [lia| exact I]]).
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. park_disj.
  Time walk_to AF MST [(usp - 208, usp)] [0x8db30; 0x8cf08; 0x90b94].
  brfork HV.
  2:{ (* [comment removed for export] *)
    cwalk [0x90b94].
    cps_stop. art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I]).
    lazymatch goal with MUx : munch _ ?mm ?mc' |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc' _))) _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; split; [destruct (PFS _ Hx); lia| exact I]) end.
    lazymatch goal with FRx : rw_cells asegs _ (usp + -192) _ |- _ => merge_low FRx 13%nat end.
    to_entry.
    eapply EPI with (pixr := pixd) (v := mkPixv w h d spp wpl xres yres inf spec pcm data) (cv := cv).
    all: repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end.
    all: lazymatch goal with
         | |- ART _ _ _ => eassumption
         | |- mem_inv _ _ => assumption
         | |- stk _ _ _ _ => assumption
         | |- rw_cells _ _ _ _ => lazymatch goal with FRx : rw_cells asegs _ (usp + -192) _ |- _ => exact FRx end
         | |- wr_at _ _ _ _ => assumption
         | |- LIBH _ => assumption
         | |- io_ssp _ => assumption
         | |- agree_on _ _ _ => exact AGF
         | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
         | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
         | |- _ <= rt_credit _ _ => repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end; lia
         | |- forall e, In e _ -> In e _ => exact LSUB
         | |- _ \/ _ =>
             right; split; [| exact PDNZ];
             unfold pix_obj, pix_cells, chunk, rsize; cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data];
             split; [exact PXC|]; split; [split; [exact INP| split; [exact PX0| split; [exact PX16| clear; lia]]]|];
             split; [exact HOK|]; split; [right; split; [split; [exact IND| split; [exact DA0| split; [exact DA16| exact DAN]]]| exact DNE]| exact PCM]
         | |- _ = 0 -> _ => intros E0; exfalso; clear - E0 PX0; lia
         | |- _ <> 0 -> _ => intros _; exact LDES
         | |- forall p k, In (p, k) _ -> 0 < k => exact LVP
         | |- Z.of_nat _ <= _ => exact LLEN
         | |- ?g => idtac "LEFTOVER:" g
         end.
  }
  (* [comment removed for export] *)
  cwalk [0x8db30].
  lazymatch goal with H : rw_cells asegs _ (fr + 36) _ |- _ => rename H into FRq end.
  split_at FRq 1%nat FRp. split_at FRp 1%nat FRtail.
  pose proof FSH as SHC. split_at SHC 10%nat SHC2. split_at SHC2 1%nat SHC3. clear SHC SHC3.
  pose proof FR as FRrec. split_before FRrec (C8 s0) FRrec3. clear FRrec.
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                ltac:(fun Hx => cbn [outside]; split; [destruct (PFS _ Hx); lia| exact I]).
  pcm_over_walk RT AF Sc mc ARTc ESP0 LOW PCM pcm cv lo ltac:(fun Hx => split; [clear - Hx LOR; lia| exact I]).
  eapply cps_seq.
  { pose proof DES as DY. unfold pixDestroy_cps in DY.
    eapply DY with (lo := lo) (pp := fr + 80) (pix := pixd) (v := mkPixv w h d spp wpl xres yres inf spec pcm data) (cv := cv)
                   (ras := bv_unsigned ra :: ras); rt_side idtac.
    all: repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end.
    all: lazymatch goal with
         | |- optrL _ _ _ _ _ _ =>
             unfold optrL, parked in *; split;
             [ right; exists fr, 1%nat; change (fs_size 1) with 128;
               split; [repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; left; reflexivity|];
               split; [clear; lia|]; split; [clear; lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
               split; [clear - FR0; lia|]; split; [clear - FRTOP; lia|];
               replace (shad (fr + 80)) with (fr / 8 + 2147450890) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
               destruct SHC2 as [[_ B] _]; exact B
             | split; [clear - FR0; lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|]; split; [clear - FRSH; lia| right; clear - FRSEG; unfold SEGTOP_A; lia] ]
         | |- rw_cells _ _ _ [C8 _] => exact FRp
         | |- pix_obj _ _ _ _ _ =>
             unfold pix_obj, pix_cells, chunk, rsize; cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data];
             split; [exact PXC|]; split; [split; [exact INP| split; [exact PX0| split; [exact PX16| clear; lia]]]|];
             split; [exact HOK|]; split; [right; split; [split; [exact IND| split; [exact DA0| split; [exact DA16| exact DAN]]]| exact DNE]| exact PCM]
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
    repeat match goal with H2 : rt_live RT _ = rt_live RT _ |- _ => rewrite H2 in H end; rewrite LDES in H end.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx);
                                    [intros e He; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact He| solve [frames_sub_tac]| lia]|
                                  cbn [outside]; destruct (NFA _ Hx) as [N1 _]; split; [lia| exact I]]).
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. park_disj.
  Time walk_to AF MST [(usp - 208, usp)] [0x8cf08; 0x90b94].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                ltac:(fun Hx => cbn [outside]; split; [destruct (PFS _ Hx); lia| exact I]).
  pose proof RERR as RE; unfold returnError_cps in RE.
  eapply cps_seq; [eapply RE with (lo := lo); rt_side idtac; [lit_in | lit_in | lenv_tac | lres_tac..] |].
  Time after_call RT AF.
  fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx);
                            [intros e He; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact He| solve [frames_sub_tac]| lia]).
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. park_disj.
  Time walk_to AF MST [(usp - 208, usp)] [0x90b94].
  (* [comment removed for export] *)
  lazymatch goal with F1 : rw_cells asegs ?mm fr _, F2 : rw_cells asegs ?mm (fr + 32) [C4 _], F3 : rw_cells asegs ?mm (fr + 36) _,
                      F4 : rw_cells asegs ?mm (fr + 80) [C8 _], F5 : rw_cells asegs ?mm (fr + 88) _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (WFR : wr_at asegs mm fr 120)
      by (apply (proj2 (wr_at_app mm fr 32 88 ltac:(lia) ltac:(lia))); split; [exact (proj2 F1)|];
          apply (proj2 (wr_at_app mm (fr + 32) 4 84 ltac:(lia) ltac:(lia))); split; [exact (proj2 F2)|];
          replace (fr + 32 + 4) with (fr + 36) by lia;
          apply (proj2 (wr_at_app mm (fr + 36) 44 40 ltac:(lia) ltac:(lia))); split; [exact (proj2 F3)|];
          replace (fr + 36 + 44) with (fr + 80) by lia;
          apply (proj2 (wr_at_app mm (fr + 80) 8 32 ltac:(lia) ltac:(lia))); split; [exact (proj2 F4)|];
          replace (fr + 80 + 8) with (fr + 88) by lia; exact (proj2 F5)) end.
  cps_stop. art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I]).
  lazymatch goal with MUx : munch _ ?mm ?mc' |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc' _))) _ =>
    agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; split; [destruct (PFS _ Hx); lia| exact I]) end.
  lazymatch goal with FRx : rw_cells asegs _ (usp + -192) _ |- _ => merge_low FRx 13%nat end.
  to_entry.
  eapply EPI with (pixr := 0) (v := mkPixv 0 0 0 0 0 0 0 0 0 0 0) (cv := mkCmapv 0 0 0 0).
  all: repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end.
  all: lazymatch goal with
       | |- ART _ _ _ => eassumption
       | |- mem_inv _ _ => assumption
       | |- stk _ _ _ _ => assumption
       | |- rw_cells _ _ _ _ => lazymatch goal with FRx : rw_cells asegs _ (usp + -192) _ |- _ => exact FRx end
       | |- wr_at _ _ _ _ => assumption
       | |- LIBH _ => assumption
       | |- io_ssp _ => assumption
       | |- agree_on _ _ _ => exact AGF
       | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
       | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
       | |- _ <= rt_credit _ _ => repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end; lia
       | |- forall e, In e _ -> In e _ => intros e He; exact He
       | |- _ \/ _ => left; reflexivity
       | |- 0 = 0 -> _ => intros _; reflexivity
       | |- 0 <> 0 -> _ => intros HH; contradiction
       | |- forall p k, In (p, k) _ -> 0 < k => intros p k Hp; exact (LVP p k (LSUB _ Hp))
       | |- Z.of_nat _ <= _ => clear; lia
       | |- ?g => idtac "LEFTOVER:" g
       end.
Qed.
(* [comment removed for export] *)
Theorem deser_cut2_ok_16 :
  deser_ctx RT Σ PMc ra s0 usp lo m dp n ras 0x90b58 ->
  deser_epi_stmt_16 RT Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m QF fr ->
  deser_cut2_stmt_16 RT Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m QF fr dp n.
Proof using AF RC GP RERR DES VAL.
  (* [comment removed for export] *)
  intros (FDO & MST & ART0 & LOW & LOR & STa & SPT & SPA & SPB & FRB & LVB & CRB & NR & DP0 & DP8 & OWN & UCTX & RA4096 & TRS) EPI. unfold deser_cut2_stmt_16.
  intros Sc mc pixd cm nc v cv j0 j1 jp f0 f1 f2 c24 c40 c48 vx r1 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 r21 r22 r24 r26 r28 r29 r30 r31 F' fc'
    ARTc MIc STc FR FRM FSH LH SSP AGF FRS ESP0 ECR LSUB POBJ PDNZ NCR CMF CMZ PSZ LDES LVP LLEN.
  unfold deser_epi_stmt_16 in EPI.
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
  { intros a Ha. apply (new_frame_apart RT AF Sc mc fr 1%nat (rt_frames RT Σ) (rt_live RT Σ) usp a ARTc FRS LSUB);
      [rewrite ESP0; lia| rewrite ESP0; unfold STACK_WIN; lia| exact Ha]. }
  (* [comment removed for export] *)
  destruct POBJ as (PXC & (INP & PX0 & PX16 & _) & HOK & DAT & PCM).
  destruct DAT as [E|((IND & DA0 & DA16 & DAN) & DNE)]; [contradiction|].
  destruct v as [w h d spp wpl xres yres inf spec pcm data].
  cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data] in *.
  unfold pix_cells in PXC. cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data] in PXC.
  unfold rsize in *. cbn [p_wpl p_h] in *.
  set (rs := 4 * (wpl * h)) in *.
  (* [comment removed for export] *)
  assert (OLDNE : forall q j, In (q, j) (rt_live RT Σ) -> q <> pixd /\ q <> data).
  { intros q j Hq. rewrite <- LDES in Hq. exact (live_destroy_in_ne pixd (mkPixv w h d spp wpl xres yres inf spec pcm data) cv _ q j PDNZ Hq). }
  (* [comment removed for export] *)
  destruct OWN as (dpp & dpk & DIN0 & DLO & DHI).
  pose proof (LSUB _ DIN0) as DIN.
  pose proof (proj2 (OLDNE _ _ DIN0)) as DPNE. pose proof (proj1 (OLDNE _ _ DIN0)) as DPNP.
  pose proof (live_apart RT AF Sc mc data (rs) dpp dpk ARTc IND DIN ltac:(intros E; apply DPNE; symmetry; exact E)) as RAWD.
  pose proof (live_apart RT AF Sc mc data (rs) pixd 64 ARTc IND INP DNE) as DPD.
  (* [comment removed for export] *)
  assert (NCD : forall a, PF a -> a < data \/ data + rs <= a).
  { intros a Ha. apply (later_chunk_apart RT AF Sc mc data (rs) (rt_live RT Σ) (rt_frames RT Σ) usp a ARTc IND);
      [intros q j Hq; split; [exact (LSUB _ Hq)| exact (proj2 (OLDNE q j Hq))]| intros e He; rewrite FRS; right; exact He
      | rewrite ESP0; unfold STACK_WIN; lia| exact Ha]. }
  assert (NCP : forall a, PF a -> a < pixd \/ pixd + 64 <= a).
  { intros a Ha. apply (later_chunk_apart RT AF Sc mc pixd 64 (rt_live RT Σ) (rt_frames RT Σ) usp a ARTc INP);
      [intros q j Hq; split; [exact (LSUB _ Hq)| exact (proj1 (OLDNE q j Hq))]| intros e He; rewrite FRS; right; exact He
      | rewrite ESP0; unfold STACK_WIN; lia| exact Ha]. }
  chunk_facts RT AF GP pixd 64. chunk_facts RT AF GP data (rs). chunk_facts RT AF GP dpp dpk.
  fframe_chunk RT AF fr 1%nat 128 pixd 64. fframe_chunk RT AF fr 1%nat 128 data (rs). fframe_chunk RT AF fr 1%nat 128 dpp dpk.
  pose proof (proj1 (af_acc_live RT AF Sc mc dpp dpk ARTc DIN)) as WRDP.
  pose proof (proj1 (af_acc_live RT AF Sc mc data (rs) ARTc IND)) as WRRA.
  pose proof (proj2 FRM) as WFR. pose proof (proj2 FSH) as WFS. cbn [cells_size csize Nat.add deser_fshadow] in WFR, WFS.
  change (Z.of_nat 120) with 120 in WFR. change (Z.of_nat 16) with 16 in WFS.
  unfold deser_fshadow in FSH.
  assert (FRTOP : fr + 128 <= 140737488355328) by (clear - FRHI SP0R; lia).
  assert (NCPOS : nc <> 0 -> 0 < nc) by (clear - NCR; lia).
  assert (DPP0 : 0 < dpp) by exact (proj1 (af_live_range RT AF Sc mc dpp dpk ARTc DIN)).
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. park_disj.
  Time walk_to AF MST [(usp - 224, usp)] [0x5ca54; 0x8ef28; 0x8db30; 0x8cf08; 0x90b94].
  (* [comment removed for export] *)
  lazymatch goal with H : wr_at asegs ?mm dpp dpk |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (wr_at_sub mm dpp dpk (dp + 4 * nc + 28) (rs) H ltac:(clear - DLO NCR; lia) ltac:(clear - DHI PSZ; lia) ltac:(clear - DAN; lia)) as WRS end.
  apply wr_at_rw_CB in WRS; [| clear - DAN; lia]. destruct WRS as (sbs & SBC).
  pose proof SBC as [[[SBL _] _] _]. cbn in SBL. apply u8arr_of_rw_cells in SBC. destruct SBC as [SB _].
  assert (SBL' : Z.of_nat (length sbs) = rs) by (rewrite SBL; clear - DAN; lia).
  assert (HSZ : rs <= 67108864) by (destruct HOK as (_ & _ & _ & _ & HSZ); cbn [p_wpl p_h] in HSZ; unfold rs; clear - HSZ; lia).
  assert (Q1 : 0 <= data <= 2^47) by (clear - DA0 CKR0 SP0R DAN; lia).
  assert (Q2 : 0 <= dp + 4 * nc + 28 <= 2^47) by (clear - DP0 NCR DLO DHI CKR1 SP0R NR; lia).
  assert (Q3 : data + rs <= dp + 4 * nc + 28 \/ dp + 4 * nc + 28 + rs <= data)
    by (clear - RAWD DLO DHI PSZ NCR; unfold parked in RAWD; lia).
  assert (Q4 : dp + 4 * nc + 28 + rs <= lo) by (clear - DHI PSZ CKR1 LOW; lia).
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                ltac:(fun Hx => cbn [outside]; split; [destruct (PFS _ Hx); lia| exact I]).
  pcm_over_walk RT AF Sc mc ARTc ESP0 LOW PCM pcm cv lo ltac:(fun Hx => split; [clear - Hx LOR; lia| exact I]).
  eapply cps_seq.
  { pose proof (rc_asan_memcpy RT RC) as MC0; unfold memcpy_icontract in MC0;
    eapply MC0 with (lo := lo) (d := data) (s := dp + 4 * nc + 28) (bs := sbs); rewrite ?SBL'.
    all: lazymatch goal with
         | |- fdfs_only _ => exact FDO
         | |- mat_stable _ => exact MST
         | |- Z_to_bv 64 _ = Z_to_bv 64 _ => reflexivity
         | |- bytes_at _ _ _ _ => exact SB
         | |- ART _ _ _ => assumption
         | |- mem_inv _ _ => assumption
         | |- checked_src _ _ _ _ _ _ _ =>
             unfold checked_src; rewrite ?unsigned_lit by (clear - SPT LOR STa; lia);
             split; [intros _; split; [apply (acc_sub asegs _ dpp dpk); [assumption| clear - DLO NCR; lia| clear - DHI PSZ; lia]|
                                       left; exists dpp, dpk; split; [exact DIN| clear - DLO DHI PSZ NCR; lia]]| left; exact Q4]
         | |- checked_dst _ _ _ _ _ _ =>
             unfold checked_dst; rewrite ?unsigned_lit by (clear - SPT LOR STa; lia);
             split; [intros _; split; [assumption| left; exists data, (rs); split; [exact IND| clear; lia]]|];
             split; [intros i Hi; right; right; left; exists data, (rs); split; [exact IND| clear - Hi; lia]| assumption]
         | |- call_ok _ _ _ _ _ =>
             unfold call_ok; rewrite ?unsigned_lit by (clear - SPT LOR STa; lia); split; [assumption|];
             rewrite ESP0; unfold STACK_WIN, RT_STACK, USTACK_TOP; clear - LOW LOR SPT SPA; repeat split; first [lia | Z.div_mod_to_equations; lia]
         | |- _ \/ _ => exact Q3
         | |- (_ <= _ <= _) => first [exact Q1 | exact Q2]
         | |- (_ < _) => clear - HSZ; lia
         | |- ?g => idtac "LEFTOVER:" g
         end. }
  rewrite SBL'. clear SB.
  Time after_call RT AF.
  (* [comment removed for export] *)
  pcm_over_call PCM pcm cv ltac:(intros a (_ & (CIN & _) & _) (_ & _ & CND & _) Ha; split;
            [right; right; left; exists pcm, 24; split; [exact CIN| exact Ha]|
             pose proof (live_apart RT AF Sc mc pcm 24 data rs ARTc CIN IND CND) as LAP; clear - LAP Ha; lia]).
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [exact LSUB| solve [frames_sub_tac]| lia]| pose proof (NCD _ Hx); lia]).
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. park_disj.
  Time walk_to AF MST [(usp - 224, usp)] [0x8ef28; 0x8db30; 0x8cf08; 0x90b94].
  brfork HNC.
  1:{ (* [comment removed for export] *)
    cwalk [0x90b94].
    cps_stop. art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I]).
    lazymatch goal with MUx : munch _ ?mm ?mc' |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc' _))) _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; split; [destruct (PFS _ Hx); lia| exact I]) end.
    lazymatch goal with FRx : rw_cells asegs _ (usp + -208) _ |- _ => merge_low FRx 13%nat end.
    to_entry.
    eapply EPI with (pixr := pixd) (v := mkPixv w h d spp wpl xres yres inf spec pcm data) (cv := cv).
    all: lazymatch goal with
         | |- ART _ _ _ => eassumption
         | |- mem_inv _ _ => assumption
         | |- stk _ _ _ _ => assumption
         | |- rw_cells _ _ _ _ => lazymatch goal with FRx : rw_cells asegs _ (usp + -208) _ |- _ => exact FRx end
         | |- wr_at _ _ _ _ => assumption
         | |- LIBH _ => assumption
         | |- io_ssp _ => assumption
         | |- agree_on _ _ _ => exact AGF
         | |- rt_frames _ _ = _ => exact FRS
         | |- rt_sp0 _ _ = _ => exact ESP0
         | |- _ <= rt_credit _ _ => clear - ECR; lia
         | |- forall e, In e _ -> In e _ => exact LSUB
         | |- _ \/ _ =>
             right; split; [| exact PDNZ];
             unfold pix_obj, pix_cells, chunk, rsize; cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data];
             split; [exact PXC|]; split; [split; [exact INP| split; [exact PX0| split; [exact PX16| clear; lia]]]|];
             split; [exact HOK|]; split; [right; split; [split; [exact IND| split; [exact DA0| split; [exact DA16| exact DAN]]]| exact DNE]| exact PCM]
         | |- _ = 0 -> _ => intros E0; exfalso; clear - E0 PX0; lia
         | |- _ <> 0 -> _ => intros _; exact LDES
         | |- forall p k, In (p, k) _ -> 0 < k => exact LVP
         | |- Z.of_nat _ <= _ => exact LLEN
         | |- ?g => idtac "LEFTOVER:" g
         end.
  }
  (* [comment removed for export] *)
  pose proof (NCPOS HNC) as NC0.
  destruct (CMF NC0) as [CMNZ PCME]. subst cm.
  cwalk [0x8ef28].
  split_at FRM 1%nat FRv. split_at FRv 1%nat FRrest.
  lazymatch type of FSH with rw_cells _ ?mm _ _ => assert (SHV : bytes_at asegs mm (shad (fr + 32)) (ushadow 4)) end.
  { pose proof (rw_cells_head _ _ _ _ (rw_cells_tail _ _ _ _ (rw_cells_tail _ _ _ _ (rw_cells_tail _ _ _ _ (rw_cells_tail _ _ _ _ FSH))))) as [[_ X] _].
    cbn [cells_bytes cbytes app csize Z.of_nat Pos.of_succ_nat Pos.succ] in X.
    replace (shad (fr + 32)) with (fr / 8 + 2147450880 + 1 + 1 + 1 + 1) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia). exact X. }
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                ltac:(fun Hx => cbn [outside]; split; [destruct (PFS _ Hx); lia| exact I]).
  pcm_over_walk RT AF Sc mc ARTc ESP0 LOW PCM pcm cv lo ltac:(fun Hx => split; [clear - Hx LOR; lia| exact I]).
  pose proof PCM as PCMd. destruct PCMd as [PZ|(CMO & CNP & CAP & CND & CAD)]; [exfalso; exact (CMNZ PZ)|].
  pose proof CMO as (_ & (CIN & CP0 & CP16 & _) & _).
  fframe_chunk RT AF fr 1%nat 128 pcm 24.
  eapply cps_seq.
  { pose proof VAL as VL; unfold pixcmapIsValid_cps in VL.
    eapply VL with (lo := lo) (cmap := pcm) (pix := pixd) (pv := fr + 32) (cv := cv)
                   (v := mkPixv w h d spp wpl xres yres inf spec pcm data) (x := vx); rt_side idtac.
    all: lazymatch goal with
         | |- cmap_obj _ _ _ _ => exact CMO
         | |- _ \/ _ =>
             right; split; [| split; [exact PDNZ| reflexivity]];
             unfold pix_obj, pix_cells, chunk, rsize; cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data];
             split; [exact PXC|]; split; [split; [exact INP| split; [exact PX0| split; [exact PX16| clear; lia]]]|];
             split; [exact HOK|]; split; [right; split; [split; [exact IND| split; [exact DA0| split; [exact DA16| exact DAN]]]| exact DNE]| exact PCM]
         | |- optrF _ _ _ _ _ =>
             unfold optrF, own_frame; unfold parked in FRSH; split;
             [ exists fr, 1%nat; change (fs_size 1) with 128;
               split; [rewrite FRS; left; reflexivity|]; split; [clear; lia|]; split; [clear; lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
               split; [clear - FR0; lia|]; split; [clear - FRTOP; lia| exact SHV]
             | split; [clear - FR0; lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|]; split; [clear - FRSH; lia| right; clear - FRSEG; unfold SEGTOP_A; lia] ]
         | |- rw_cells _ _ _ [C4 _] => exact FRv
         | |- lenv _ _ _ _ _ _ => lenv_tac
         | |- lres _ _ _ _ _ => lres_tac
         | |- ?g => idtac "LEFTOVER:" g
         end. }
  Time after_call RT AF.
  pcm_over_call PCM pcm cv ltac:(intros a (_ & (CIN' & _) & _) _ Ha; split;
            [right; right; left; exists pcm, 24; split; [solve [in_live_tac]| exact Ha]|
             cbn [outside]; split; [match goal with H : context [pcm + 24 <= fr] |- _ => clear - H Ha; unfold parked in H; lia end| exact I]]).
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx);
                                    [intros e He; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact (LSUB e He)| solve [frames_sub_tac]| lia]|
                                  cbn [outside]; destruct (NFA _ Hx) as [N1 _]; split; [lia| exact I]]).
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. park_disj.
  Time walk_to AF MST [(usp - 224, usp)] [0x8db30; 0x8cf08; 0x90b94].
  brfork HV.
  2:{ (* [comment removed for export] *)
    cwalk [0x90b94].
    cps_stop. art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I]).
    lazymatch goal with MUx : munch _ ?mm ?mc' |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc' _))) _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; split; [destruct (PFS _ Hx); lia| exact I]) end.
    lazymatch goal with FRx : rw_cells asegs _ (usp + -208) _ |- _ => merge_low FRx 13%nat end.
    to_entry.
    eapply EPI with (pixr := pixd) (v := mkPixv w h d spp wpl xres yres inf spec pcm data) (cv := cv).
    all: repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end.
    all: lazymatch goal with
         | |- ART _ _ _ => eassumption
         | |- mem_inv _ _ => assumption
         | |- stk _ _ _ _ => assumption
         | |- rw_cells _ _ _ _ => lazymatch goal with FRx : rw_cells asegs _ (usp + -208) _ |- _ => exact FRx end
         | |- wr_at _ _ _ _ => assumption
         | |- LIBH _ => assumption
         | |- io_ssp _ => assumption
         | |- agree_on _ _ _ => exact AGF
         | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
         | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
         | |- _ <= rt_credit _ _ => repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end; lia
         | |- forall e, In e _ -> In e _ => exact LSUB
         | |- _ \/ _ =>
             right; split; [| exact PDNZ];
             unfold pix_obj, pix_cells, chunk, rsize; cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data];
             split; [exact PXC|]; split; [split; [exact INP| split; [exact PX0| split; [exact PX16| clear; lia]]]|];
             split; [exact HOK|]; split; [right; split; [split; [exact IND| split; [exact DA0| split; [exact DA16| exact DAN]]]| exact DNE]| exact PCM]
         | |- _ = 0 -> _ => intros E0; exfalso; clear - E0 PX0; lia
         | |- _ <> 0 -> _ => intros _; exact LDES
         | |- forall p k, In (p, k) _ -> 0 < k => exact LVP
         | |- Z.of_nat _ <= _ => exact LLEN
         | |- ?g => idtac "LEFTOVER:" g
         end.
  }
  (* [comment removed for export] *)
  cwalk [0x8db30].
  lazymatch goal with H : rw_cells asegs _ (fr + 36) _ |- _ => rename H into FRq end.
  split_at FRq 1%nat FRp. split_at FRp 1%nat FRtail.
  pose proof FSH as SHC. split_at SHC 10%nat SHC2. split_at SHC2 1%nat SHC3. clear SHC SHC3.
  pose proof FR as FRrec. split_before FRrec (C8 s0) FRrec3. clear FRrec.
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                ltac:(fun Hx => cbn [outside]; split; [destruct (PFS _ Hx); lia| exact I]).
  pcm_over_walk RT AF Sc mc ARTc ESP0 LOW PCM pcm cv lo ltac:(fun Hx => split; [clear - Hx LOR; lia| exact I]).
  eapply cps_seq.
  { pose proof DES as DY. unfold pixDestroy_cps in DY.
    eapply DY with (lo := lo) (pp := fr + 80) (pix := pixd) (v := mkPixv w h d spp wpl xres yres inf spec pcm data) (cv := cv)
                   (ras := bv_unsigned ra :: ras); rt_side idtac.
    all: repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end.
    all: lazymatch goal with
         | |- optrL _ _ _ _ _ _ =>
             unfold optrL, parked in *; split;
             [ right; exists fr, 1%nat; change (fs_size 1) with 128;
               split; [repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; left; reflexivity|];
               split; [clear; lia|]; split; [clear; lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
               split; [clear - FR0; lia|]; split; [clear - FRTOP; lia|];
               replace (shad (fr + 80)) with (fr / 8 + 2147450890) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
               destruct SHC2 as [[_ B] _]; exact B
             | split; [clear - FR0; lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|]; split; [clear - FRSH; lia| right; clear - FRSEG; unfold SEGTOP_A; lia] ]
         | |- rw_cells _ _ _ [C8 _] => exact FRp
         | |- pix_obj _ _ _ _ _ =>
             unfold pix_obj, pix_cells, chunk, rsize; cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data];
             split; [exact PXC|]; split; [split; [exact INP| split; [exact PX0| split; [exact PX16| clear; lia]]]|];
             split; [exact HOK|]; split; [right; split; [split; [exact IND| split; [exact DA0| split; [exact DA16| exact DAN]]]| exact DNE]| exact PCM]
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
    repeat match goal with H2 : rt_live RT _ = rt_live RT _ |- _ => rewrite H2 in H end; rewrite LDES in H end.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx);
                                    [intros e He; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact He| solve [frames_sub_tac]| lia]|
                                  cbn [outside]; destruct (NFA _ Hx) as [N1 _]; split; [lia| exact I]]).
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. park_disj.
  Time walk_to AF MST [(usp - 224, usp)] [0x8cf08; 0x90b94].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                ltac:(fun Hx => cbn [outside]; split; [destruct (PFS _ Hx); lia| exact I]).
  pose proof RERR as RE; unfold returnError_cps in RE.
  eapply cps_seq; [eapply RE with (lo := lo); rt_side idtac; [lit_in | lit_in | lenv_tac | lres_tac..] |].
  Time after_call RT AF.
  fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx);
                            [intros e He; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact He| solve [frames_sub_tac]| lia]).
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. park_disj.
  Time walk_to AF MST [(usp - 224, usp)] [0x90b94].
  (* [comment removed for export] *)
  lazymatch goal with F1 : rw_cells asegs ?mm fr _, F2 : rw_cells asegs ?mm (fr + 32) [C4 _], F3 : rw_cells asegs ?mm (fr + 36) _,
                      F4 : rw_cells asegs ?mm (fr + 80) [C8 _], F5 : rw_cells asegs ?mm (fr + 88) _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (WFR : wr_at asegs mm fr 120)
      by (apply (proj2 (wr_at_app mm fr 32 88 ltac:(lia) ltac:(lia))); split; [exact (proj2 F1)|];
          apply (proj2 (wr_at_app mm (fr + 32) 4 84 ltac:(lia) ltac:(lia))); split; [exact (proj2 F2)|];
          replace (fr + 32 + 4) with (fr + 36) by lia;
          apply (proj2 (wr_at_app mm (fr + 36) 44 40 ltac:(lia) ltac:(lia))); split; [exact (proj2 F3)|];
          replace (fr + 36 + 44) with (fr + 80) by lia;
          apply (proj2 (wr_at_app mm (fr + 80) 8 32 ltac:(lia) ltac:(lia))); split; [exact (proj2 F4)|];
          replace (fr + 80 + 8) with (fr + 88) by lia; exact (proj2 F5)) end.
  cps_stop. art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I]).
  lazymatch goal with MUx : munch _ ?mm ?mc' |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc' _))) _ =>
    agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; split; [destruct (PFS _ Hx); lia| exact I]) end.
  lazymatch goal with FRx : rw_cells asegs _ (usp + -208) _ |- _ => merge_low FRx 13%nat end.
  to_entry.
  eapply EPI with (pixr := 0) (v := mkPixv 0 0 0 0 0 0 0 0 0 0 0) (cv := mkCmapv 0 0 0 0).
  all: repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end.
  all: lazymatch goal with
       | |- ART _ _ _ => eassumption
       | |- mem_inv _ _ => assumption
       | |- stk _ _ _ _ => assumption
       | |- rw_cells _ _ _ _ => lazymatch goal with FRx : rw_cells asegs _ (usp + -208) _ |- _ => exact FRx end
       | |- wr_at _ _ _ _ => assumption
       | |- LIBH _ => assumption
       | |- io_ssp _ => assumption
       | |- agree_on _ _ _ => exact AGF
       | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
       | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
       | |- _ <= rt_credit _ _ => repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end; lia
       | |- forall e, In e _ -> In e _ => intros e He; exact He
       | |- _ \/ _ => left; reflexivity
       | |- 0 = 0 -> _ => intros _; reflexivity
       | |- 0 <> 0 -> _ => intros HH; contradiction
       | |- forall p k, In (p, k) _ -> 0 < k => intros p k Hp; exact (LVP p k (LSUB _ Hp))
       | |- Z.of_nat _ <= _ => clear; lia
       | |- ?g => idtac "LEFTOVER:" g
       end.
Qed.
End DESER2.
