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
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import RT_iface RT_traces RT_gaps_iface I_strcmp_spec I_strcmp_lift LeptTac D_kit Lept_kit Lept_iface Lept_lits Lept_litmem Lept_env LeptC_kit Lept_chain Lept_leaf Lept_objkit Lept_fuzzkit Lept_deserkit Lept_gmax_defs D_iface D_defs D_libiface Gm_iface Gm_kit Gm_livekit Gm_livekit2 Gm_drvkit Gm_leaf Gm_fzkit Fh_iface Fh_statics Fh_gen_defs Fh_drvkit Fh_hmtkit Fh_hmt_defs LeptB_guard LeptB_guard2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
Ltac gd_resync RT AF GP AGF PFS NFA :=
  cps_stop;
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]);
  lazymatch goal with MUx : munch _ ?mm _ |- _ =>
    agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                       repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end;
  refresh RT AF; lib_refresh RT GP; unfold shad, SHB in *; park_disj.

Section HMT.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis RERR : returnError_cps RT e_returnErrorPtr.
Hypothesis ADDB : pixAddBorder1_cps RT e_pixAddBorder.
Hypothesis RMB : pixRemoveBorder1_cps RT e_pixRemoveBorder.
Hypothesis GEN : pixFHMTGen_1_cps RT.
Hypothesis GENNULL : fh_null_cps RT e_pixFHMTGen_1.
Hypothesis RMNULL : fh_null_cps RT e_pixRemoveBorder.
Hypothesis DESTROY : pixDestroy_cps RT.
Hypothesis DNULL : pixDestroy_null_cps RT.

Lemma fh_hmt_c0 : fh_hmt_case RT 0.
Proof using AF RC GP RERR ADDB RMB GEN GENNULL RMNULL DESTROY DNULL.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    pixs name vs cvs i ras FDO MST -> -> -> -> POS SDNZ NARG UCX RA0 -> LSEL ENV RES AL.
  unfold lpost, lpost_f, lenv, lres, keeps, keepsL in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW0 & LOR & SPT & SPA & SPB).
  destruct RES as (FRB & LVB & CRB & LVP). unfold uctx in UCX.
  pose proof POS as (PXS & (PSIN & PS0 & PS16 & _) & HOKS & _ & PSCM).
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  pose proof (bv_unsigned_in_range 64 s0) as RS0. unfold bv_modulus in RS0. change (2 ^ Z.of_N 64) with (2^64) in RS0.
  unfold entry_st, e_pixHMTDwa_1, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STDERR_STACK, HMT_COST, FHMTGEN_COST, BORDER1_COST, TEMPLATE_COST, RASTER_COST in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  lib_refresh RT GP.
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  chunk_facts RT AF GP pixs 64.
  unfold pix_cells in PXS.
  assert (DBND : 1 <= p_d vs <= 32) by (destruct HOKS as (HD1 & _); cbn [In] in HD1; lia).
  hide POS. hide PSCM. hide HOKS. hide UCX. hide NARG. hide LSEL.
  park_disj. carve_frame 128%nat ST.
  clear_acc.
  walk_to AF MST [(usp - 128, usp)] [e_stack_malloc 1%nat].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
  eapply cps_seq.
  { pose proof (gp_stack_malloc_1 RT GP) as SM1; unfold stack_malloc_contract' in SM1; eapply SM1 with (lo := lo); rt_side idtac. }
  after_call RT AF.
  lazymatch goal with |- cps _ (ASTA RT ?S _ _) _ => rename S into S0 end.
  fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
  fframe_open RT AF PF (rt_live RT Σ) usp 1%nat 128 ltac:(fun Ha => exact Ha).
  fframe_chunk RT AF fr 1%nat 128 pixs 64.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
  walk_to AF MST [(usp - 128, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0xb09f4].
  gd_resync RT AF GP AGF PFS NFA.
  assert (FRS0 : rt_frames RT S0 = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
  assert (LV0 : rt_live RT S0 = rt_live RT Σ) by (repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity).
  (* [comment removed for export] *)
  lazymatch goal with FRx : rw_cells asegs _ (usp + -128) ?cs |- _ =>
    assert (EPI : forall (S : rts RT) (mE : mem) (r : Z) (v : pixv) (cv : cmapv)
              (r1 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r20 r21 r22 r23 r24 r28 r29 r30 r31 : word) F' fc',
        r8 = Z_to_bv 64 usp ->
        ART RT S mE -> mem_inv asegs mE -> stk asegs mE lo (usp + -128) -> rw_cells asegs mE (usp + -128) cs ->
        wr_at asegs mE fr 8 -> wr_at asegs mE (fr / 8 + 2147450880) 16 ->
        LIBH mE -> io_ssp mE -> agree_on PF m mE ->
        (r = 0 \/ (pix_obj (rt_live RT S) mE r v cv /\ p_w v = p_w vs /\ p_h v = p_h vs /\ p_d v = 1 /\ p_data v <> 0)) ->
        (r = 0 -> rt_live RT S = rt_live RT Σ) -> (r <> 0 -> live_destroy r v cv (rt_live RT S) = rt_live RT Σ) ->
        (forall p n, In (p, n) (rt_live RT S) -> 0 < n) -> Z.of_nat (length (rt_live RT S)) <= Z.of_nat (length (rt_live RT Σ)) + 4 ->
        rt_frames RT S = (fr, 1%nat) :: rt_frames RT Σ -> rt_sp0 RT S = rt_sp0 RT Σ ->
        rt_credit RT Σ - (2 * (2 * 67108864 + 16384 + 32) + (2 * 67108864 + 16384 + 16 + 8) + 16) + 1 <= rt_credit RT S ->
        cps asegs (ASTA RT S PMc (eq (entry_st r1 (Z_to_bv 64 (usp + -128)) gp (Z_to_bv 64 TP_A) r5 r6 r7 r8 r9
                                        r10 r11 r12 r13 r14 r15 r16 r17 (Z_to_bv 64 r) (Z_to_bv 64 fr) r20 r21 r22 r23 r24 (Z_to_bv 64 (fr / 8 + 2147450880))
                                        (Z_to_bv 64 fr) s11 r28 r29 r30 r31 F' fc' 0xb0af4 mE))) QF) end.
  { intros S mE r v cv r1 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r20 r21 r22 r23 r24 r28 r29 r30 r31 F' fc'
      -> ARTE MIE STE FRE WFE WSE LHE SSPE AGE HPR ELV0 ELV LVPE LLENE EFR ESP0 ECR.
    clear AGF. rename AGE into AGF.
    repeat match goal with H : rw_cells asegs _ _ _ |- _ => lazymatch H with FRE => fail | _ => clear H end end.
    repeat match goal with H : ro_cells asegs _ _ _ |- _ => clear H end.
    repeat match goal with H : ART RT _ _ |- _ => lazymatch H with ARTE => fail | _ => clear H end end.
    repeat match goal with H : LIBH _ |- _ => lazymatch H with LHE => fail | _ => clear H end end.
    repeat match goal with H : io_ssp _ |- _ => lazymatch H with SSPE => fail | _ => clear H end end.
    repeat match goal with H : stk asegs _ _ _ |- _ => lazymatch H with STE => fail | _ => clear H end end.
    repeat match goal with H : mem_inv asegs _ |- _ => lazymatch H with MIE => fail | _ => clear H end end.
    repeat match goal with H : wmono asegs _ _ |- _ => clear H end.
    repeat match goal with H : munch _ _ _ |- _ => clear H end.
    repeat match goal with H : rt_frames RT _ = _ |- _ => lazymatch H with EFR => fail | _ => clear H end end.
    repeat match goal with H : rt_live RT _ = _ |- _ => clear H end.
    repeat match goal with H : rt_sp0 RT _ = _ |- _ => lazymatch H with ESP0 => fail | _ => clear H end end.
    repeat match goal with H : rt_credit RT _ = _ |- _ => clear H end.
    clear_acc.
    hide ELV0. hide ELV. hide HPR. hide LVPE. hide LLENE.
    destruct (wr_at_rw_CB mE fr 8 WFE ltac:(lia)) as (jfE & FRME). destruct (wr_at_rw_CB mE (fr / 8 + 2147450880) 16 WSE ltac:(lia)) as (jsE & FSHE).
    change (Z.to_nat 8) with 8%nat in FRME. change (Z.to_nat 16) with 16%nat in FSHE.
    assert (LOUT : forall b k, In (b, k) (rt_live RT S) -> forall x, b <= x < b + k ->
              outside [(usp - 128, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] x)
      by (intros bb kk Hb zz Hz; exact (live_outside_frame1 RT AF S mE fr usp (usp - 128) bb kk zz ARTE ltac:(rewrite EFR; left; reflexivity) ltac:(rewrite ESP0; ul) Hb Hz)).
    unfold entry_st.
    walk_to AF MST [(usp - 128, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0xb0b58].
    lazymatch goal with MUx : munch _ mE ?mc |- _ =>
      assert (KEEP1 : keeps_live (rt_live RT S) mE mc)
        by (let bb := fresh "bb" in let kk := fresh "kk" in let Hb := fresh "Hb" in let a := fresh "a" in let Ha := fresh "Ha" in
            intros bb kk Hb a Ha; apply MUx; exact (LOUT bb kk Hb _ Ha)) end.
    assert (LSUB : forall e, In e (rt_live RT Σ) -> In e (rt_live RT S)).
    { unfold hid in ELV0, ELV. intros e He. destruct (Z.eq_dec r 0) as [Z0|NZ]; [rewrite (ELV0 Z0); exact He| exact (ld_sub r v cv _ _ (ELV NZ) e He)]. }
    frame_release_k RT AF GP MST Σ fr 1%nat 128 PF AGF PFS usp lo 0xb0b60
      ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                        repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia])
      ltac:(fun Hx => exact Hx)
      ltac:(fun fl FLN => idtac).
    walk_to AF MST [(usp - 128, usp)] (@nil Z).
    fold usp. cwalk (@nil Z).
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I]).
    lazymatch goal with MUx : munch _ ?mm ?mc |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      assert (KEEP3 : keeps_live (rt_live RT S) mm mc)
        by (let bb := fresh "bb" in let kk := fresh "kk" in let Hb := fresh "Hb" in let a := fresh "a" in let Ha := fresh "Ha" in
            intros bb kk Hb a Ha; apply MUx; cbn [outside]; split; [exact (proj1 (LOUT bb kk Hb _ Ha))| exact I]);
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]) end.
    lazymatch goal with K3 : keeps_live _ _ ?mc |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      assert (KEEPF : keeps_live (rt_live RT S) mE mc)
        by (eapply keeps_live_trans; [exact KEEP1|]; eapply keeps_live_trans; [exact KEEPR| exact K3]) end.
    apply cps_finish. intros c Hc. subst QF. cbv beta.
    lazymatch type of Hc with ASTA RT ?S' _ _ _ => exists S', r, v, cv end.
    unfold hid in ELV0, ELV, HPR, LVPE, LLENE. unfold new_pix1, new_pix1_live.
    split.
    { eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists.
      split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
      split; [split; [split; [assumption| split; assumption]| split; assumption]|].
      split; [intros a Ha _; apply AGF; exact Ha|].
      rewrite LV2. destruct HPR as [HZ|(HO & HR)]; [left; exact HZ| right]. split; [| exact HR].
      exact (pix_obj_keep _ mE _ r v _ KEEPF HO). }
    rewrite LV2, FRS2, SP2, CR2.
    split; [split; [exact ELV0| split; [exact ELV| split; [exact LVPE| exact LLENE]]]|].
    split; [reflexivity|]. split; [exact ESP0|].
    unfold HMT_COST, FHMTGEN_COST, BORDER1_COST, TEMPLATE_COST, RASTER_COST in *.
    repeat match goal with H : context [rt_credit] |- _ => revert H end; clear; intros; lia. }
  split_last_CB FRM [8%nat; 8%nat; 24%nat; 8%nat; 24%nat; 8%nat; 16%nat].
  unfold hid in HOKS.
  destruct (Z.eq_dec (p_d vs) 1) as [D1|DN1].
  2:{ (* [comment removed for export] *)
    walk_to AF MST [(usp - 288, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_returnErrorPtr; e_pixAddBorder; e_pixFHMTGen_1; e_pixRemoveBorder; e_pixDestroy; e_pixCopy].
    cwalk [e_returnErrorPtr; e_pixAddBorder; e_pixFHMTGen_1; e_pixRemoveBorder; e_pixDestroy; e_pixCopy].
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                  repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
    pose proof RERR as RE. unfold returnError_cps in RE.
    eapply cps_seq.
    { eapply RE with (lo := lo); rt_side idtac; [lit_in_fast | lit_in_fast | lenv_tac | lres_tac..]. }
    after_call RT AF.
    fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]).
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
    walk_to AF MST [(usp - 288, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0xb0af4].
    cwalk [0xb0af4].
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
    lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                         repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
    pose proof FRM as FRH. split_at FRH 1%nat FRH2. clear FRH2.
    to_entry.
    eapply EPI with (r := 0) (v := vs) (cv := cvs); try eassumption.
    all: lazymatch goal with
         | |- _ = Z_to_bv 64 _ => first [reflexivity | symmetry; exact ESP]
         | |- wr_at asegs _ _ 8 => exact (proj2 FRH)
         | |- wr_at asegs _ _ 16 => exact (proj2 FSH)
         | |- _ \/ _ => left; reflexivity
         | |- 0 = 0 -> _ => intros _; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity
         | |- 0 <> 0 -> _ => intros C; exfalso; exact (C eq_refl)
         | |- forall p n, In _ _ -> _ => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact LVP
         | |- Z.of_nat _ <= _ => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; lia
         | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
         | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
         | |- _ <= rt_credit _ _ => repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end; lia
         | |- ?g => idtac "LEFT:" g
         end. }
  rewrite D1 in PXS.
  walk_to AF MST [(usp - 288, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_returnErrorPtr; e_pixAddBorder; e_pixFHMTGen_1; e_pixRemoveBorder; e_pixDestroy; e_pixCopy].
  cwalk [e_returnErrorPtr; e_pixAddBorder; e_pixFHMTGen_1; e_pixRemoveBorder; e_pixDestroy; e_pixCopy].
  pose proof FR as FRrec. split_before FRrec (C8 s0) FRrec2. clear FRrec.
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  assert (PML : forall q k a, In (q, k) (rt_live RT Σ) -> q <= a < q + k -> PF a)
    by (intros q k a Hq Ha; right; right; left; exists q, k; split; [exact Hq| lia]).
  unfold hid in POS.
  lazymatch goal with PX : rw_cells asegs ?mc pixs _, A : ART RT ?S ?mc |- cps _ (ASTA RT ?S _ _) _ =>
    assert (POS1 : pix_obj (rt_live RT S) mc pixs vs cvs)
      by (apply (pix_obj_mono (rt_live RT Σ) (rt_live RT S) mc pixs vs cvs); [solve [live_sub_tac]|];
          apply (pix_obj_agree (rt_live RT Σ) PF m mc pixs vs cvs POS AGF PML); unfold pix_cells; rewrite D1; exact PX) end.
  hide POS.
  pose proof ADDB as AB. unfold pixAddBorder1_cps in AB.
  unfold hid in UCX.
  eapply cps_seq.
  { eapply AB with (lo := lo) (pixs := pixs) (vs := vs) (cvs := cvs) (ras := HMT_RAS); rt_side idtac.
    all: lazymatch goal with
         | |- pix_obj _ _ _ _ _ => exact POS1
         | |- addborder1_args _ _ _ _ _ _ => right; repeat split; reflexivity
         | |- p_d _ = 1 => exact D1
         | |- p_data _ <> 0 => exact SDNZ
         | |- _ <> 0 -> _ =>
             intros _; split;
             [ unfold uctx, HMT_RAS; rewrite ?unsigned_lit by ul; rewrite <- RA0;
               apply (chain_ok_push _ (usp + -128) usp (bv_unsigned ra) (bv_unsigned s0) [RA_TOP]);
                 [ lia | clear - SPA; Z.div_mod_to_equations; lia | ul | rewrite RA0; lia | lia
                 | rewrite !Z_to_bv_bv_unsigned; exact FRrec2 | ];
               apply (chain_ok_keep [RA_TOP] m _ usp (bv_unsigned s0) UCX);
               eapply agree_sub; [exact AGF|]; intros zx Hzx; left; exact Hzx
             | rewrite ?unsigned_lit by ul; exact hmt_tr_addb ]
         | |- lenv _ _ _ _ _ _ => lenv_tac
         | |- lres _ _ _ _ _ => unfold BORDER1_COST, RASTER_COST; lres_tac
         | |- ?g => idtac "LEFT:" g
         end. }
  clear POS1.
  after_call RT AF.
  unfold new_pix1, new_pix1_live in *.
  unfold HMT_COST, FHMTGEN_COST, BORDER1_COST, TEMPLATE_COST, RASTER_COST in *.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]| exact I]).
  lazymatch goal with |- cps _ (ASTA RT ?S _ _) _ => rename S into S1 end.
  lazymatch goal with H : ?r = 0 \/ (pix_obj (rt_live RT S1) _ ?r ?vv ?cc /\ _) |- _ => rename H into PB; set (pixb := r) in *; set (vb := vv) in *; set (cvb := cc) in * end.
  lazymatch goal with H : (pixb = 0 -> rt_live RT S1 = _) /\ _ |- _ => destruct H as (LV1z & LV1n & LVP1 & LLEN1) end.
  rewrite LV0 in LV1z, LV1n, LLEN1.
  assert (FRS1 : rt_frames RT S1 = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
  assert (SPL1 : rt_sp0 RT S1 - 8388608 <= usp - 288) by (repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul).
  destruct (Z.eq_dec pixb 0) as [BZ|BNZ].
  { (* [comment removed for export] *)
    clear PB LV1n. specialize (LV1z BZ). rewrite BZ in *.
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
    walk_to AF MST [(usp - 288, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_returnErrorPtr; e_pixAddBorder; e_pixFHMTGen_1; e_pixRemoveBorder; e_pixDestroy; e_pixCopy].
    cwalk [e_returnErrorPtr; e_pixAddBorder; e_pixFHMTGen_1; e_pixRemoveBorder; e_pixDestroy; e_pixCopy].
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                  repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
    pose proof GENNULL as GN. unfold fh_null_cps in GN.
    eapply cps_seq.
    { eapply GN with (lo := lo); rt_side idtac.
      all: lazymatch goal with
           | |- _ = _ -> _ /\ _ => intros _; split; reflexivity
           | |- _ = _ -> _ = _ => intros C; exfalso; revert C; unfold e_pixFHMTGen_1, e_pixRemoveBorder; lia
           | |- lenv _ _ _ _ _ _ => lenv_tac
           | |- lres _ _ _ _ _ =>
               unfold lres, FRAMES_MAX, LIVE_MAX in *;
               split; [rewrite FRS1; cbn [length]; lia| split; [rewrite LV1z; lia| split; [lia| intros p n H; rewrite LV1z in H; exact (LVP p n H)]]]
           | |- ?g => idtac "LEFT:" g
           end. }
    after_call RT AF.
    fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]| exact I]).
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
    walk_to AF MST [(usp - 288, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_returnErrorPtr; e_pixAddBorder; e_pixFHMTGen_1; e_pixRemoveBorder; e_pixDestroy; e_pixCopy].
    cwalk [e_returnErrorPtr; e_pixAddBorder; e_pixFHMTGen_1; e_pixRemoveBorder; e_pixDestroy; e_pixCopy].
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                  repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
    pose proof RMNULL as RN. unfold fh_null_cps in RN.
    eapply cps_seq.
    { eapply RN with (lo := lo); rt_side idtac.
      all: lazymatch goal with
           | |- _ = _ -> _ /\ _ => intros C; exfalso; revert C; unfold e_pixFHMTGen_1, e_pixRemoveBorder; lia
           | |- _ = _ -> _ = _ => intros _; reflexivity
           | |- lenv _ _ _ _ _ _ => lenv_tac
           | |- lres _ _ _ _ _ =>
               unfold lres, FRAMES_MAX, LIVE_MAX in *;
               repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; cbn [length];
               split; [lia| split; [lia| split; [lia| exact LVP]]]
           | |- ?g => idtac "LEFT:" g
           end. }
    after_call RT AF.
    fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]| exact I]).
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
    walk_to AF MST [(usp - 288, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_returnErrorPtr; e_pixAddBorder; e_pixFHMTGen_1; e_pixRemoveBorder; e_pixDestroy; e_pixCopy].
    cwalk [e_returnErrorPtr; e_pixAddBorder; e_pixFHMTGen_1; e_pixRemoveBorder; e_pixDestroy; e_pixCopy].
    split_at FRM 4%nat PP1. split_at PP1 1%nat FRMc.
    pose proof FSH as SHB4. split_at SHB4 4%nat SHB4b. split_at SHB4b 1%nat SHB4c. clear SHB4 SHB4c.
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                  repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
    lazymatch goal with A : ART RT ?S _ |- cps _ (ASTA RT ?S _ _) _ =>
      assert (FRSn : rt_frames RT S = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity) end.
    pose proof DNULL as DN. unfold pixDestroy_null_cps in DN.
    eapply cps_seq.
    { eapply DN with (lo := lo) (pp := fr + 32); rt_side idtac.
      all: lazymatch goal with
           | |- optrL _ _ _ _ _ _ =>
               unfold optrL, parked in *; split;
               [ right; exists fr, 1%nat; rewrite FRSn; change (fs_size 1) with 128;
                 split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                 split; [lia|]; split; [lia|];
                 replace (shad (fr + 32)) with (fr / 8 + 2147450884) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                 destruct SHB4b as [[_ B] _]; exact B
               | unfold SEGTOP_A; repeat split; first [lia | clear - FR64; Z.div_mod_to_equations; lia] ]
           | |- rw_cells _ _ _ [C8 _] => exact PP1
           | |- lenv _ _ _ _ _ _ => lenv_tac
           | |- lres _ _ _ _ _ =>
               unfold lres, FRAMES_MAX, LIVE_MAX in *;
               repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; cbn [length];
               split; [lia| split; [lia| split; [lia| exact LVP]]]
           | |- ?g => idtac "LEFT:" g
           end. }
    clear FRSn SHB4b.
    after_call RT AF.
    fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]| exact I]).
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
    walk_to AF MST [(usp - 288, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_returnErrorPtr; e_pixAddBorder; e_pixFHMTGen_1; e_pixRemoveBorder; e_pixDestroy; e_pixCopy].
    cwalk [e_returnErrorPtr; e_pixAddBorder; e_pixFHMTGen_1; e_pixRemoveBorder; e_pixDestroy; e_pixCopy].
    split_at FRMc 1%nat PP2. split_at PP2 1%nat FRMd.
    pose proof FSH as SHB8. split_at SHB8 8%nat SHB8b. split_at SHB8b 1%nat SHB8c. clear SHB8 SHB8c.
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                  repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
    lazymatch goal with A : ART RT ?S _ |- cps _ (ASTA RT ?S _ _) _ =>
      assert (FRSn : rt_frames RT S = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity) end.
    eapply cps_seq.
    { eapply DN with (lo := lo) (pp := fr + 64); rt_side idtac.
      all: lazymatch goal with
           | |- optrL _ _ _ _ _ _ =>
               unfold optrL, parked in *; split;
               [ right; exists fr, 1%nat; rewrite FRSn; change (fs_size 1) with 128;
                 split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                 split; [lia|]; split; [lia|];
                 replace (shad (fr + 64)) with (fr / 8 + 2147450888) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                 destruct SHB8b as [[_ B] _]; exact B
               | unfold SEGTOP_A; repeat split; first [lia | clear - FR64; Z.div_mod_to_equations; lia] ]
           | |- rw_cells _ _ _ [C8 _] => exact PP2
           | |- lenv _ _ _ _ _ _ => lenv_tac
           | |- lres _ _ _ _ _ =>
               unfold lres, FRAMES_MAX, LIVE_MAX in *;
               repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; cbn [length];
               split; [lia| split; [lia| split; [lia| exact LVP]]]
           | |- ?g => idtac "LEFT:" g
           end. }
    clear FRSn SHB8b.
    after_call RT AF.
    fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]| exact I]).
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
    walk_to AF MST [(usp - 288, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0xb0af4].
    cwalk [0xb0af4].
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
    lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                         repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
    pose proof FRM as FRH. split_at FRH 1%nat FRH2. clear FRH2.
    to_entry.
    eapply EPI with (r := 0) (v := vs) (cv := cvs); try eassumption.
    all: lazymatch goal with
         | |- _ = Z_to_bv 64 _ => first [reflexivity | symmetry; exact ESP]
         | |- wr_at asegs _ _ 8 => exact (proj2 FRH)
         | |- wr_at asegs _ _ 16 => exact (proj2 FSH)
         | |- _ \/ _ => left; reflexivity
         | |- 0 = 0 -> _ => intros _; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity
         | |- 0 <> 0 -> _ => intros C; exfalso; exact (C eq_refl)
         | |- forall p n, In _ _ -> _ => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact LVP
         | |- Z.of_nat _ <= _ => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; lia
         | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
         | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
         | |- _ <= rt_credit _ _ => repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end; lia
         | |- ?g => idtac "LEFT:" g
         end. }
  (* [comment removed for export] *)
  destruct PB as [BZ|(POB & BW & BH & BD & BDATA)]; [exfalso; exact (BNZ BZ)|].
  specialize (LV1n BNZ). clear LV1z.
  assert (SUB1 : forall e, In e (rt_live RT Σ) -> In e (rt_live RT S1)) by (exact (ld_sub pixb vb cvb _ _ LV1n)).
  unfold hid in HOKS. pose proof HOKS as (_ & HSW & HSH & _). hide HOKS.
  hide POB.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
  walk_to AF MST [(usp - 288, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_returnErrorPtr; e_pixAddBorder; e_pixFHMTGen_1; e_pixRemoveBorder; e_pixDestroy; e_pixCopy].
  cwalk [e_returnErrorPtr; e_pixAddBorder; e_pixFHMTGen_1; e_pixRemoveBorder; e_pixDestroy; e_pixCopy].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  unfold hid in POB, NARG, LSEL. destruct NARG as (I10 & NIN & NB).
  lazymatch goal with |- cps _ (ASTA RT ?S _ (eq (entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mc))) _ =>
    lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT S ?mm |- _ =>
      assert (KL : keeps_live (rt_live RT S) mm mc)
        by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
            exact (live_outside_frame1 RT AF S mm fr usp (usp - 288) bb kk xx A ltac:(rewrite FRS1; left; reflexivity) SPL1 Hb Hx)) end;
    assert (NBc : bytes_at asegs mc name (hm_name i))
      by (apply (bytes_at_agree asegs m mc name _ NB); eapply agree_sub; [exact AGF|]; cbv beta;
          let xx := fresh "xx" in let Hxx := fresh "Hxx" in intros xx Hxx;
          rewrite (proj1 (proj2 (proj2 (hm_cmp i 0 I10 ltac:(lia))))) in Hxx; right; right; left; exists name, 8; split; [exact NIN| lia]);
    assert (LSELc : LIB_SEL mc)
      by (unfold LIB_SEL in *; apply (rw_cells_agree_nw asegs m mc _ _ LSEL); eapply agree_sub; [exact AGF|]; cbv beta;
          let xx := fresh "xx" in let Hxx := fresh "Hxx" in intros xx Hxx; right; left; apply sel_names_client;
          change (Z.of_nat (cells_size LIB_SEL_CELLS)) with 800 in Hxx; unfold LIB_SEL_AT in Hxx; lia)
  end.
  pose proof (pix_obj_keep _ _ _ pixb vb _ KL POB) as POB2. clear KL.
  hide NB. hide LSEL.
  pose proof GEN as GE. unfold pixFHMTGen_1_cps in GE.
  eapply cps_seq.
  { eapply GE with (lo := lo) (pixs := pixb) (name := name) (vs := vb) (cvs := cvb) (i := i); rt_side idtac.
    all: lazymatch goal with
         | |- pix_obj _ _ _ _ _ => exact POB2
         | |- p_d _ = 1 => exact BD
         | |- p_data _ <> 0 => exact BDATA
         | |- 64 < _ => first [rewrite BW | rewrite BH]; lia
         | |- hm_name_arg _ _ _ _ _ => split; [exact I10| split; [exact (SUB1 _ NIN)| exact NBc]]
         | |- LIB_SEL _ => exact LSELc
         | |- lenv _ _ _ _ _ _ => lenv_tac
         | |- lres _ _ _ _ _ =>
             unfold lres, FHMTGEN_COST, TEMPLATE_COST, RASTER_COST, FRAMES_MAX, LIVE_MAX in *;
             split; [rewrite FRS1; cbn [length]; lia| split; [lia| split; [lia| exact LVP1]]]
         | |- ?g => idtac "LEFT:" g
         end. }
  clear NBc LSELc.
  after_call RT AF.
  unfold HMT_COST, FHMTGEN_COST, BORDER1_COST, TEMPLATE_COST, RASTER_COST in *.
  lazymatch goal with AG : agree_on (fun a => aclient ?lv _ _ a /\ outside ?W a) ?ma ?mb |- _ =>
    assert (KL : keeps_live lv ma mb) by (apply (keeps_live_of_agree lv _ _ W ma mb AG); intros; exact I) end.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [intros e He; exact (SUB1 e He)| solve [frames_sub_tac]| lia]| exact I]).
  lazymatch goal with |- cps _ (ASTA RT ?S _ _) _ => rename S into S2 end.
  lazymatch goal with H : live_destroy ?pd ?vd0 ?cvd0 (rt_live RT S2) = _ |- _ =>
    rename pd into pixd; rename vd0 into vd; rename cvd0 into cvd; rename H into LV2n end.
  lazymatch goal with H : pix_obj (rt_live RT S2) _ pixd vd cvd |- _ => rename H into POD end.
  lazymatch goal with H : forall p n, In (p, n) (rt_live RT S2) -> 0 < n |- _ => rename H into LVP2 end.
  lazymatch goal with H : Z.of_nat (length (rt_live RT S2)) <= _ |- _ => rename H into LLEN2 end.
  lazymatch goal with H : p_w vd = p_w vb |- _ => rename H into DW end.
  lazymatch goal with H : p_h vd = p_h vb |- _ => rename H into DH end.
  lazymatch goal with H : p_d vd = 1 |- _ => rename H into DD end.
  lazymatch goal with H : p_data vd <> 0 |- _ => rename H into DDATA end.
  assert (SUB2 : forall e, In e (rt_live RT S1) -> In e (rt_live RT S2)) by (exact (ld_sub pixd vd cvd _ _ LV2n)).
  assert (FRS2 : rt_frames RT S2 = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
  assert (SPL2 : rt_sp0 RT S2 - 8388608 <= usp - 288) by (repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul).
  lazymatch goal with A : ART RT S2 ?mb |- _ =>
    pose proof (pix_obj_carry_gen (rt_live RT S1) (rt_live RT S2) _ mb pixb vb cvb POB2 KL SUB2) as POB3 end.
  assert (APBD : apart pixb vb cvb pixd vd cvd) by (exact (apart_of_alloc _ _ _ pixb vb cvb pixd vd cvd POB2 LV2n)).
  clear POB2 KL POB.
  hide POB3. hide POD. hide APBD.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
  walk_to AF MST [(usp - 288, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_returnErrorPtr; e_pixAddBorder; e_pixFHMTGen_1; e_pixRemoveBorder; e_pixDestroy; e_pixCopy].
  cwalk [e_returnErrorPtr; e_pixAddBorder; e_pixFHMTGen_1; e_pixRemoveBorder; e_pixDestroy; e_pixCopy].
  pose proof FR as FRrec. split_before FRrec (C8 s0) FRrec3. clear FRrec.
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  unfold hid in POD, POB3.
  lazymatch goal with |- cps _ (ASTA RT ?S _ (eq (entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mc))) _ =>
    lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT S ?mm |- _ =>
      assert (KL : keeps_live (rt_live RT S) mm mc)
        by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
            exact (live_outside_frame1 RT AF S mm fr usp (usp - 288) bb kk xx A ltac:(rewrite FRS2; left; reflexivity) SPL2 Hb Hx)) end end.
  pose proof (pix_obj_keep _ _ _ pixd vd _ KL POD) as POD2. pose proof (pix_obj_keep _ _ _ pixb vb _ KL POB3) as POB4. clear KL POD POB3.
  pose proof RMB as RB. unfold pixRemoveBorder1_cps in RB.
  eapply cps_seq.
  { eapply RB with (lo := lo) (pixs := pixd) (vs := vd) (cvs := cvd) (ras := HMT_RAS); rt_side idtac.
    all: lazymatch goal with
         | |- pix_obj _ _ _ _ _ => exact POD2
         | |- rmborder1_args _ _ _ _ _ => right; repeat split; reflexivity
         | |- p_d _ = 1 => exact DD
         | |- p_data _ <> 0 => exact DDATA
         | |- 64 < _ => first [rewrite DW, BW | rewrite DH, BH]; lia
         | |- _ <> 0 -> _ =>
             intros _; split;
             [ unfold uctx, HMT_RAS; rewrite ?unsigned_lit by ul; rewrite <- RA0;
               apply (chain_ok_push _ (usp + -128) usp (bv_unsigned ra) (bv_unsigned s0) [RA_TOP]);
                 [ lia | clear - SPA; Z.div_mod_to_equations; lia | ul | rewrite RA0; lia | lia
                 | rewrite !Z_to_bv_bv_unsigned; exact FRrec3 | ];
               apply (chain_ok_keep [RA_TOP] m _ usp (bv_unsigned s0) UCX);
               eapply agree_sub; [exact AGF|]; intros zx Hzx; left; exact Hzx
             | rewrite ?unsigned_lit by ul; exact hmt_tr_rmb ]
         | |- lenv _ _ _ _ _ _ => lenv_tac
         | |- lres _ _ _ _ _ =>
             unfold lres, BORDER1_COST, RASTER_COST, FRAMES_MAX, LIVE_MAX in *;
             split; [rewrite FRS2; cbn [length]; lia| split; [lia| split; [lia| exact LVP2]]]
         | |- ?g => idtac "LEFT:" g
         end. }
  clear FRrec3.
  after_call RT AF.
  unfold new_pix1, new_pix1_live in *.
  unfold HMT_COST, FHMTGEN_COST, BORDER1_COST, TEMPLATE_COST, RASTER_COST in *.
  lazymatch goal with |- cps _ (ASTA RT ?S _ _) _ => rename S into S3 end.
  lazymatch goal with H : ?r = 0 \/ (pix_obj (rt_live RT S3) _ ?r ?vv ?cc /\ _) |- _ => rename H into PR3; set (r3 := r) in *; set (v3 := vv) in *; set (cv3 := cc) in * end.
  lazymatch goal with H : (r3 = 0 -> rt_live RT S3 = _) /\ _ |- _ => destruct H as (LV3z & LV3n & LVP3 & LLEN3) end.
  assert (SUB3 : forall e, In e (rt_live RT S2) -> In e (rt_live RT S3)).
  { intros e He. destruct (Z.eq_dec r3 0) as [Z0|NZ]; [rewrite (LV3z Z0); exact He| exact (ld_sub r3 v3 cv3 _ _ (LV3n NZ) e He)]. }
  lazymatch goal with AG : agree_on (fun a => aclient ?lv _ _ a /\ outside ?W a) ?ma ?mb |- _ =>
    assert (KL : keeps_live lv ma mb) by (apply (keeps_live_of_agree lv _ _ W ma mb AG); intros; exact I) end.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [intros e He; exact (SUB2 e (SUB1 e He))| solve [frames_sub_tac]| lia]| exact I]).
  assert (FRS3 : rt_frames RT S3 = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
  assert (SPL3 : rt_sp0 RT S3 - 8388608 <= usp - 288) by (repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul).
  lazymatch goal with A : ART RT S3 ?mb |- _ =>
    pose proof (pix_obj_carry_gen (rt_live RT S2) (rt_live RT S3) _ mb pixb vb cvb POB4 KL SUB3) as POB5;
    pose proof (pix_obj_carry_gen (rt_live RT S2) (rt_live RT S3) _ mb pixd vd cvd POD2 KL SUB3) as POD3 end.
  (* [comment removed for export] *)
  assert (AP3 : r3 <> 0 -> apart pixb vb cvb r3 v3 cv3 /\ apart pixd vd cvd r3 v3 cv3).
  { intros NZ. split; [exact (apart_of_alloc _ _ _ pixb vb cvb r3 v3 cv3 POB4 (LV3n NZ))| exact (apart_of_alloc _ _ _ pixd vd cvd r3 v3 cv3 POD2 (LV3n NZ))]. }
  clear POB4 POD2 KL.
  hide POB5. hide POD3. hide PR3. hide AP3. hide LV3z. hide LV3n.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
  walk_to AF MST [(usp - 288, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_returnErrorPtr; e_pixAddBorder; e_pixFHMTGen_1; e_pixRemoveBorder; e_pixDestroy; e_pixCopy].
  cwalk [e_returnErrorPtr; e_pixAddBorder; e_pixFHMTGen_1; e_pixRemoveBorder; e_pixDestroy; e_pixCopy].
  (* [comment removed for export] *)
  split_at FRM 4%nat PP1. split_at PP1 1%nat FRMc.
  pose proof FSH as SHB4. split_at SHB4 4%nat SHB4b. split_at SHB4b 1%nat SHB4c. clear SHB4 SHB4c.
  pose proof FR as FRrec. split_before FRrec (C8 s0) FRrec4. clear FRrec.
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  unfold hid in POB5, POD3, PR3.
  lazymatch goal with |- cps _ (ASTA RT ?S _ (eq (entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mc))) _ =>
    lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT S ?mm |- _ =>
      assert (KL : keeps_live (rt_live RT S) mm mc)
        by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
            exact (live_outside_frame1 RT AF S mm fr usp (usp - 288) bb kk xx A ltac:(rewrite FRS3; left; reflexivity) SPL3 Hb Hx)) end end.
  pose proof (pix_obj_keep _ _ _ pixb vb _ KL POB5) as POB6. pose proof (pix_obj_keep _ _ _ pixd vd _ KL POD3) as POD4.
  assert (PR4 : r3 = 0 \/ (pix_obj (rt_live RT S3) _ r3 v3 cv3 /\ p_w v3 = p_w vd - 64 /\ p_h v3 = p_h vd - 64 /\ p_d v3 = 1 /\ p_data v3 <> 0))
    by (destruct PR3 as [Z0|(PO & R)]; [left; exact Z0| right; split; [exact (pix_obj_keep _ _ _ r3 v3 _ KL PO)| exact R]]).
  clear KL POB5 POD3 PR3.
  lazymatch goal with A : ART RT ?S _ |- cps _ (ASTA RT ?S _ _) _ =>
    assert (FRSn : rt_frames RT S = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity) end.
  pose proof DESTROY as DY. unfold pixDestroy_cps in DY.
  eapply cps_seq.
  { eapply DY with (lo := lo) (pp := fr + 32) (pix := pixb) (v := vb) (cv := cvb) (ras := HMT_RAS); rt_side idtac.
    all: lazymatch goal with
         | |- optrL _ _ _ _ _ _ =>
             unfold optrL, parked in *; split;
             [ right; exists fr, 1%nat; rewrite FRSn; change (fs_size 1) with 128;
               split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
               split; [lia|]; split; [lia|];
               replace (shad (fr + 32)) with (fr / 8 + 2147450884) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
               destruct SHB4b as [[_ B] _]; exact B
             | unfold SEGTOP_A; repeat split; first [lia | clear - FR64; Z.div_mod_to_equations; lia] ]
         | |- rw_cells _ _ _ [C8 _] => exact PP1
         | |- pix_obj _ _ _ _ _ => exact POB6
         | |- uctx _ _ _ _ =>
             unfold uctx, HMT_RAS; rewrite ?unsigned_lit by ul; rewrite <- RA0;
             apply (chain_ok_push _ (usp + -128) usp (bv_unsigned ra) (bv_unsigned s0) [RA_TOP]);
               [ lia | clear - SPA; Z.div_mod_to_equations; lia | ul | rewrite RA0; lia | lia
               | rewrite !Z_to_bv_bv_unsigned; exact FRrec4 | ];
             apply (chain_ok_keep [RA_TOP] m _ usp (bv_unsigned s0) UCX);
             eapply agree_sub; [exact AGF|]; intros zx Hzx; left; exact Hzx
         | |- Forall _ DESTROY_FREE_RAS => rewrite ?unsigned_lit by ul; exact hmt_tr_d1
         | |- lenv _ _ _ _ _ _ => lenv_tac
         | |- lres _ _ _ _ _ =>
             unfold lres, FRAMES_MAX, LIVE_MAX in *;
             split; [rewrite FRSn; cbn [length]; lia| split; [lia| split; [lia| exact LVP3]]]
         | |- ?g => idtac "LEFT:" g
         end. }
  clear FRSn SHB4b FRrec4.
  after_call RT AF.
  lazymatch goal with |- cps _ (ASTA RT ?S _ _) _ => rename S into S4 end.
  lazymatch goal with H : rt_live RT S4 = live_destroy pixb vb cvb _ |- _ => rename H into LV4 end.
  assert (FRS4 : rt_frames RT S4 = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
  assert (SPL4 : rt_sp0 RT S4 - 8388608 <= usp - 288) by (repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul).
  assert (SUB4 : forall e, In e (rt_live RT Σ) -> In e (rt_live RT S4)).
  { intros [p n] He. rewrite LV4. apply ld_in; [exact (SUB3 _ (SUB2 _ (SUB1 _ He)))|].
    apply (ld_notin pixb vb cvb (rt_live RT S1)); [rewrite LV1n; exact He|]. cbn [fst]. exact (proj1 (af_live_range RT AF Σ m p n ART0 He)). }
  lazymatch goal with AG : agree_on (fun a => aclient ?lv _ _ a /\ outside ?W a) ?ma ?mb, A : ART RT S4 ?mb |- _ =>
    assert (KL : keeps_live lv ma mb)
      by (apply (keeps_live_of_agree lv _ _ W ma mb AG); intros bb kk xx Hb Hx;
          exact (live_outside_local RT AF S4 mb fr 1%nat 32 bb kk xx A ltac:(rewrite FRS4; left; reflexivity) ltac:(lia) ltac:(change (fs_size 1) with 128; lia) Hb Hx)) end.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [intros e He; exact (SUB4 e He)| solve [frames_sub_tac]| lia]
                                 | cbn [outside]; destruct (NFA _ Hx) as [N1 N2]; split; [lia| exact I]]).
  unfold hid in APBD, AP3.
  lazymatch goal with A : ART RT S4 ?mb |- _ =>
    assert (POD5 : pix_obj (rt_live RT S4) mb pixd vd cvd)
      by (apply (pix_obj_keep _ _ _ pixd vd _ KL); rewrite LV4; exact (pix_obj_ld _ _ pixb vb cvb pixd vd cvd POD4 (apart_sym _ _ _ _ _ _ APBD)));
    assert (PR5 : r3 = 0 \/ (pix_obj (rt_live RT S4) mb r3 v3 cv3 /\ p_w v3 = p_w vd - 64 /\ p_h v3 = p_h vd - 64 /\ p_d v3 = 1 /\ p_data v3 <> 0))
      by (destruct PR4 as [Z0|(PO & R)]; [left; exact Z0| right; split; [| exact R]];
          assert (NZ : r3 <> 0) by (destruct PO as (_ & (_ & P0 & _) & _); lia);
          apply (pix_obj_keep _ _ _ r3 v3 _ KL); rewrite LV4; exact (pix_obj_ld _ _ pixb vb cvb r3 v3 cv3 PO (apart_sym _ _ _ _ _ _ (proj1 (AP3 NZ)))))
  end.
  assert (LVP4 : forall p n, In (p, n) (rt_live RT S4) -> 0 < n) by (intros p n H; rewrite LV4 in H; exact (LVP3 p n (ld_incl _ _ _ _ _ H))).
  assert (LLEN4 : Z.of_nat (length (rt_live RT S4)) <= Z.of_nat (length (rt_live RT S3))) by (rewrite LV4; apply live_destroy_le).
  clear KL POD4 PR4 POB6.
  hide POD5. hide PR5. hide APBD. hide AP3. hide LV4.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
  walk_to AF MST [(usp - 288, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_returnErrorPtr; e_pixAddBorder; e_pixFHMTGen_1; e_pixRemoveBorder; e_pixDestroy; e_pixCopy].
  cwalk [e_returnErrorPtr; e_pixAddBorder; e_pixFHMTGen_1; e_pixRemoveBorder; e_pixDestroy; e_pixCopy].
  (* [comment removed for export] *)
  lazymatch goal with H : rw_cells asegs _ (fr + 32) [C8 _] |- _ => rename H into PP1z end.
  split_at FRMc 1%nat PP2. split_at PP2 1%nat FRMd.
  pose proof FSH as SHB8. split_at SHB8 8%nat SHB8b. split_at SHB8b 1%nat SHB8c. clear SHB8 SHB8c.
  pose proof FR as FRrec. split_before FRrec (C8 s0) FRrec5. clear FRrec.
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  unfold hid in POD5, PR5.
  lazymatch goal with |- cps _ (ASTA RT ?S _ (eq (entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mc))) _ =>
    lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT S ?mm |- _ =>
      assert (KL : keeps_live (rt_live RT S) mm mc)
        by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
            exact (live_outside_frame1 RT AF S mm fr usp (usp - 288) bb kk xx A ltac:(rewrite FRS4; left; reflexivity) SPL4 Hb Hx)) end end.
  pose proof (pix_obj_keep _ _ _ pixd vd _ KL POD5) as POD6.
  assert (PR6 : r3 = 0 \/ (pix_obj (rt_live RT S4) _ r3 v3 cv3 /\ p_w v3 = p_w vd - 64 /\ p_h v3 = p_h vd - 64 /\ p_d v3 = 1 /\ p_data v3 <> 0))
    by (destruct PR5 as [Z0|(PO & R)]; [left; exact Z0| right; split; [exact (pix_obj_keep _ _ _ r3 v3 _ KL PO)| exact R]]).
  clear KL POD5 PR5.
  lazymatch goal with A : ART RT ?S _ |- cps _ (ASTA RT ?S _ _) _ =>
    assert (FRSn : rt_frames RT S = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity) end.
  eapply cps_seq.
  { eapply DY with (lo := lo) (pp := fr + 64) (pix := pixd) (v := vd) (cv := cvd) (ras := HMT_RAS); rt_side idtac.
    all: lazymatch goal with
         | |- optrL _ _ _ _ _ _ =>
             unfold optrL, parked in *; split;
             [ right; exists fr, 1%nat; rewrite FRSn; change (fs_size 1) with 128;
               split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
               split; [lia|]; split; [lia|];
               replace (shad (fr + 64)) with (fr / 8 + 2147450888) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
               destruct SHB8b as [[_ B] _]; exact B
             | unfold SEGTOP_A; repeat split; first [lia | clear - FR64; Z.div_mod_to_equations; lia] ]
         | |- rw_cells _ _ _ [C8 _] => exact PP2
         | |- pix_obj _ _ _ _ _ => exact POD6
         | |- uctx _ _ _ _ =>
             unfold uctx, HMT_RAS; rewrite ?unsigned_lit by ul; rewrite <- RA0;
             apply (chain_ok_push _ (usp + -128) usp (bv_unsigned ra) (bv_unsigned s0) [RA_TOP]);
               [ lia | clear - SPA; Z.div_mod_to_equations; lia | ul | rewrite RA0; lia | lia
               | rewrite !Z_to_bv_bv_unsigned; exact FRrec5 | ];
             apply (chain_ok_keep [RA_TOP] m _ usp (bv_unsigned s0) UCX);
             eapply agree_sub; [exact AGF|]; intros zx Hzx; left; exact Hzx
         | |- Forall _ DESTROY_FREE_RAS => rewrite ?unsigned_lit by ul; exact hmt_tr_d2
         | |- lenv _ _ _ _ _ _ => lenv_tac
         | |- lres _ _ _ _ _ =>
             unfold lres, FRAMES_MAX, LIVE_MAX in *;
             split; [rewrite FRSn; cbn [length]; lia| split; [lia| split; [lia| exact LVP4]]]
         | |- ?g => idtac "LEFT:" g
         end. }
  clear FRSn SHB8b FRrec5.
  after_call RT AF.
  lazymatch goal with |- cps _ (ASTA RT ?S _ _) _ => rename S into S5 end.
  lazymatch goal with H : rt_live RT S5 = live_destroy pixd vd cvd _ |- _ => rename H into LV5 end.
  assert (FRS5 : rt_frames RT S5 = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
  assert (SPL5 : rt_sp0 RT S5 - 8388608 <= usp - 288) by (repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul).
  assert (SUB5 : forall e, In e (rt_live RT Σ) -> In e (rt_live RT S5)).
  { intros [p n] He. rewrite LV5. apply ld_in; [exact (SUB4 _ He)|].
    apply (ld_notin pixd vd cvd (rt_live RT S2)); [rewrite LV2n; exact (SUB1 _ He)|]. cbn [fst]. exact (proj1 (af_live_range RT AF Σ m p n ART0 He)). }
  lazymatch goal with AG : agree_on (fun a => aclient ?lv _ _ a /\ outside ?W a) ?ma ?mb, A : ART RT S5 ?mb |- _ =>
    assert (KL : keeps_live lv ma mb)
      by (apply (keeps_live_of_agree lv _ _ W ma mb AG); intros bb kk xx Hb Hx;
          exact (live_outside_local RT AF S5 mb fr 1%nat 64 bb kk xx A ltac:(rewrite FRS5; left; reflexivity) ltac:(lia) ltac:(change (fs_size 1) with 128; lia) Hb Hx)) end.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [intros e He; exact (SUB5 e He)| solve [frames_sub_tac]| lia]
                                 | cbn [outside]; destruct (NFA _ Hx) as [N1 N2]; split; [lia| exact I]]).
  unfold hid in AP3.
  lazymatch goal with A : ART RT S5 ?mb |- _ =>
    assert (PR7 : r3 = 0 \/ (pix_obj (rt_live RT S5) mb r3 v3 cv3 /\ p_w v3 = p_w vd - 64 /\ p_h v3 = p_h vd - 64 /\ p_d v3 = 1 /\ p_data v3 <> 0))
      by (destruct PR6 as [Z0|(PO & R)]; [left; exact Z0| right; split; [| exact R]];
          assert (NZ : r3 <> 0) by (destruct PO as (_ & (_ & P0 & _) & _); lia);
          apply (pix_obj_keep _ _ _ r3 v3 _ KL); rewrite LV5; exact (pix_obj_ld _ _ pixd vd cvd r3 v3 cv3 PO (apart_sym _ _ _ _ _ _ (proj2 (AP3 NZ)))))
  end.
  assert (LVP5 : forall p n, In (p, n) (rt_live RT S5) -> 0 < n) by (intros p n H; rewrite LV5 in H; exact (LVP4 p n (ld_incl _ _ _ _ _ H))).
  (* [comment removed for export] *)
  unfold hid in LV4, LV3z, LV3n.
  assert (L5z : r3 = 0 -> rt_live RT S5 = rt_live RT Σ).
  { intros Z0. rewrite LV5, LV4, (LV3z Z0), live_destroy_comm, LV2n. exact LV1n. }
  assert (L5n : r3 <> 0 -> live_destroy r3 v3 cv3 (rt_live RT S5) = rt_live RT Σ).
  { intros NZ. rewrite LV5, LV4. rewrite (live_destroy_comm r3 v3 cv3 pixd vd cvd), (live_destroy_comm r3 v3 cv3 pixb vb cvb), (LV3n NZ).
    rewrite live_destroy_comm, LV2n. exact LV1n. }
  lazymatch goal with A : ART RT S5 ?mb |- _ =>
    assert (LLEN5 : Z.of_nat (length (rt_live RT S5)) <= Z.of_nat (length (rt_live RT Σ)) + 4)
      by (destruct (Z.eq_dec r3 0) as [Z0|NZ]; [rewrite (L5z Z0); lia|];
          pose proof (live_destroy_len r3 v3 cv3 _ (live_nodup RT AF S5 mb A LVP5)) as LL; rewrite (L5n NZ) in LL; exact LL) end.
  clear KL PR6 POD6.
  hide PR7. hide L5z. hide L5n. hide LVP5. hide LLEN5. hide LV5. hide LV4. hide LV3z. hide LV3n.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
  walk_to AF MST [(usp - 288, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0xb0af4].
  cwalk [0xb0af4].
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
  unfold hid in PR7.
  lazymatch goal with MUx : munch ?W ?mm ?mc, A : ART RT S5 ?mm |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
    assert (KL : keeps_live (rt_live RT S5) mm mc)
      by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
          exact (live_outside_frame1 RT AF S5 mm fr usp (usp - 288) bb kk xx A ltac:(rewrite FRS5; left; reflexivity) SPL5 Hb Hx));
    agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                       repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
  lazymatch goal with |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
    assert (PR8 : r3 = 0 \/ (pix_obj (rt_live RT S5) mc r3 v3 cv3 /\ p_w v3 = p_w vs /\ p_h v3 = p_h vs /\ p_d v3 = 1 /\ p_data v3 <> 0))
      by (destruct PR7 as [Z0|(PO & R1 & R2 & R3 & R4)]; [left; exact Z0| right];
          split; [exact (pix_obj_keep _ _ _ r3 v3 _ KL PO)|]; split; [rewrite R1, DW, BW; lia|]; split; [rewrite R2, DH, BH; lia|]; split; assumption) end.
  clear KL PR7.
  pose proof FRM as FRH. split_at FRH 1%nat FRH2. clear FRH2.
  unfold hid in L5z, L5n, LVP5, LLEN5.
  to_entry.
  eapply EPI with (r := r3) (v := v3) (cv := cv3); try eassumption.
  all: lazymatch goal with
       | |- _ = Z_to_bv 64 _ => first [reflexivity | symmetry; exact ESP]
       | |- wr_at asegs _ _ 8 => exact (proj2 FRH)
       | |- wr_at asegs _ _ 16 => exact (proj2 FSH)
       | |- rt_frames _ _ = _ => exact FRS5
       | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
       | |- _ <= rt_credit _ _ => repeat match goal with H : context [rt_credit] |- _ => revert H end; clear; intros; lia
       | |- ?g => idtac "LEFT:" g
       end.
Qed.
End HMT.
