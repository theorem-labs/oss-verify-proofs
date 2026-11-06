(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import ImageA.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import Layout.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_lits Lept_env LeptC_kit Lept_chain Lept_leaf LeptC_leaf Lept_objkit Lept_fuzzkit Lept_deserkit Lept_gmax_defs D_iface D_defs D_libiface
  Gm_iface Gq_iface Gm_kit Gm_leaf Gm_livekit Gm_livekit2 Gm_drvkit Gm_drvkit2 Gm_fzkit Gq_nz Gq_fzkit Gq_fuzz_defs LeptB_guard LeptB_guard2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
Lemma cps_ASTA_ret : forall (RT : rt_sig) (Σ : rts RT) (PMc : Model -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v : word) (Φ : mem -> Prop) (Q : config -> Prop),
  (forall (x : mem) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : word) (x14 : bvmap 5 word) (x15 : bv 32), Φ x ->
     cps asegs (ASTA RT Σ PMc (eq (MS (mkR ra sp gp tp x0 x1 x2 s0 s1 v x3 x4 x5 x6 x7 x8 x9 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x10 x11 x12 x13)
                                       x14 (ret_pc ra) (frm_clear x15) None x (seg_rom asegs)))) Q) ->
  cps asegs (ASTA RT Σ PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms /\ Φ m')) Q.
Proof.
  intros RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v Φ Q H.
  apply (cps_ASTA_ex RT); intros m'. apply (cps_ASTA_pure_r RT); intros HΦ. unfold ret_st.
  do 16 (apply (cps_ASTA_ex RT); intros ?). apply (cps_ASTA_eq_sym RT). apply H. exact HΦ.
Qed.
(* [comment removed for export] *)
Lemma cps_ASTA_ret0 : forall (RT : rt_sig) (Σ : rts RT) (PMc : Model -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v : word) (Q : config -> Prop),
  (forall (x : mem) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : word) (x14 : bvmap 5 word) (x15 : bv 32),
     cps asegs (ASTA RT Σ PMc (eq (MS (mkR ra sp gp tp x0 x1 x2 s0 s1 v x3 x4 x5 x6 x7 x8 x9 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x10 x11 x12 x13)
                                       x14 (ret_pc ra) (frm_clear x15) None x (seg_rom asegs)))) Q) ->
  cps asegs (ASTA RT Σ PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms)) Q.
Proof.
  intros RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v Q H.
  apply (cps_ASTA_ex RT); intros m'. unfold ret_st.
  do 16 (apply (cps_ASTA_ex RT); intros ?). apply (cps_ASTA_eq_sym RT). apply H.
Qed.
(* [comment removed for export] *)
Ltac cps_open RT ::=
  unfold malloc_post, free_post, icpt_post;
  repeat first [ apply cps_ex_l; intro | apply cps_and_pure_r; intro ];
  first [ apply (cps_ASTA_ret RT); intros
        | apply (cps_ASTA_ret0 RT); intros
        | unfold ret_st; repeat (cps_open1 RT) ].

(* [comment removed for export] *)
Lemma open_post1 : forall {A} (P : A -> config -> Prop) (Ψ : A -> Prop) (Q : config -> Prop),
  (forall x, Ψ x -> cps asegs (P x) Q) -> cps asegs (fun cf => exists x, P x cf /\ Ψ x) Q.
Proof. intros A P Ψ Q H. apply cps_ex_l; intros a. apply cps_and_pure_r; intros HΨ. exact (H a HΨ). Qed.
Lemma open_post2 : forall {A B} (P : A -> B -> config -> Prop) (Ψ : A -> B -> Prop) (Q : config -> Prop),
  (forall (x : A) (x0 : B), Ψ x x0 -> cps asegs (P x x0) Q) -> cps asegs (fun cf => exists x x0, P x x0 cf /\ Ψ x x0) Q.
Proof. intros A B P Ψ Q H. apply cps_ex_l; intros a. apply cps_ex_l; intros b. apply cps_and_pure_r; intros HΨ. exact (H a b HΨ). Qed.
Lemma open_post3 : forall {A B C} (P : A -> B -> C -> config -> Prop) (Ψ : A -> B -> C -> Prop) (Q : config -> Prop),
  (forall (x : A) (x0 : B) (x1 : C), Ψ x x0 x1 -> cps asegs (P x x0 x1) Q) -> cps asegs (fun cf => exists x x0 x1, P x x0 x1 cf /\ Ψ x x0 x1) Q.
Proof. intros A B C P Ψ Q H. do 3 (apply cps_ex_l; intros ?). apply cps_and_pure_r; intros HΨ. apply H. exact HΨ. Qed.
Lemma open_post4 : forall {A B C D} (P : A -> B -> C -> D -> config -> Prop) (Ψ : A -> B -> C -> D -> Prop) (Q : config -> Prop),
  (forall (x : A) (x0 : B) (x1 : C) (x2 : D), Ψ x x0 x1 x2 -> cps asegs (P x x0 x1 x2) Q) ->
  cps asegs (fun cf => exists x x0 x1 x2, P x x0 x1 x2 cf /\ Ψ x x0 x1 x2) Q.
Proof. intros A B C D P Ψ Q H. do 4 (apply cps_ex_l; intros ?). apply cps_and_pure_r; intros HΨ. apply H. exact HΨ. Qed.
Ltac cps_open RT ::=
  unfold malloc_post, free_post, icpt_post;
  first [ apply open_post4; do 5 intro | apply open_post3; do 4 intro | apply open_post2; do 3 intro | apply open_post1; do 2 intro | idtac ];
  repeat first [ apply cps_ex_l; intro | apply cps_and_pure_r; intro ];
  first [ apply (cps_ASTA_ret RT); intros
        | apply (cps_ASTA_ret0 RT); intros
        | unfold ret_st; repeat (cps_open1 RT) ].


Section FZ.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis DESER : pixDeserialize_nz_cps RT.
Hypothesis DESTROY : pixDestroy_cps RT.
Hypothesis DNULL : pixDestroy_null_cps RT.
Hypothesis PCOPY : pixCopy_cps RT.
Hypothesis OP1 : pixDitherTo2bpp_cps RT.
Hypothesis OP2 : pixDitherToBinary_cps RT.
Hypothesis OP3 : pixGenerateMaskByBand_cps RT.
Hypothesis OP4 : pixGenerateMaskByBand32_cps RT.
Hypothesis OP5 : pixGenerateMaskByDiscr32_cps RT.
Hypothesis OP6 : pixThresholdGrayArb_cps RT.

Theorem fuzz_c16 : fuzz_case RT 16.
Proof using AF RC GP DESER DESTROY DNULL PCOPY OP1 OP2 OP3 OP4 OP5 OP6.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d bs lo
    FDO MST -> -> -> RATOP DPOS BSL BYTES OWN FR0 LVP LVB CRB S0INV LIBm SSP ART0 MI ST LOW LOR SPT SPA SPB AL.
  destruct LIBm as ((LSEV & LALLOC & LDEALLOC) & (h0 & LHAND)).
  clear BYTES.
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, D_libiface.e_fuzz, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold D_libiface.FUZZ_STACK, D_libiface.FUZZ_COST, D_libiface.FUZZ_LIVE, LSTK, STDERR_STACK, RASTER_COST in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a /\ outside D_libiface.LIB_FP a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a [Ha _]. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  hide S0INV.
  park_disj. carve_frame 112%nat ST.
  clear_acc.
  Time walk_to AF MST [(usp - 112, usp)] [e_stack_malloc 1%nat].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
  eapply cps_seq.
  { pose proof (gp_stack_malloc_1 RT GP) as SM1; unfold stack_malloc_contract' in SM1; eapply SM1 with (lo := lo); rt_side idtac. }
  after_call RT AF.
  fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
  fframe_open RT AF PF (rt_live RT Σ) usp 1%nat 128 ltac:(fun Ha => exact (proj1 Ha)).
  refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
  destruct (Z_lt_ge_dec (Z.of_nat (length bs)) 3) as [SZ|SZ].
  - (* [comment removed for export] *)
    Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x90c70].
    frame_release_raw RT AF GP MST Σ fr 1%nat 128 PF AGF PFS usp lo 0x90c78
      ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                        repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia])
      ltac:(fun Hx => exact (proj1 Hx)) LSEV LALLOC LDEALLOC LHAND.
    refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
    walk_to AF MST [(usp - 112, usp)] (@nil Z).
    lazymatch goal with ST' : stk asegs _ lo (usp + -112), FR' : rw_cells asegs _ (usp + -112) _ |- _ => release_frame FR' ST' usp end.
    cps_stop.
    apply cps_finish; intros c Hc; subst QF; cbv beta.
    lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S end.
    split; [| alg_tac].
    eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists.
    split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
    split; [split; [assumption| split; assumption]|].
    split; [intros a Ha Ho; exact (AGF a (conj Ha Ho))|].
    unfold D_libiface.LIB_A.
    split; [split; [assumption| split; assumption]| exists h0; assumption].
  - (* [comment removed for export] *)
    Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16); (983072, 983080)]
                 [e_pixDeserialize; 0x95bd0; 0x9f3dc; 0x9d968; 0x9eb78; 0xa2460; 0xa2d20; 0xa0ce4; 0x941e0].
    lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
    destruct OWN as [(p0 & n0 & OIN & OLO & OHI & DAL)| ->]; [| cbn [length] in SZ; lia].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (LH : LIBH mc)
        by (unfold LIBH, LIB0, g_LeptMsgSeverity, g_pix_alloc, g_pix_dealloc, g_stderr_handler, e_devnull; split; [split; [|split]|]; assumption) end.
    clear LSEV LALLOC LDEALLOC LHAND.
    pose proof FR as FRrec. split_before FRrec (C8 s0) FRrec2. clear FRrec.
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| split; [intros zz Hzz; static_tac | exact I]]]])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; destruct Hx as [_ HxO];
                        unfold D_libiface.LIB_FP, g_stderr_handler in HxO; cbn [outside] in HxO; unfold shad, SHB in *;
                        repeat split; try exact I; first [lia | tauto | Z.div_mod_to_equations; lia]).
    pose proof DESER as DS. unfold pixDeserialize_nz_cps in DS.
    unfold hid in S0INV.
    eapply cps_seq.
    { eapply DS with (lo := lo) (dp := d) (n := Z.of_nat (length bs)) (ras := [RA_TOP]); rt_side idtac.
      - right. split; [exact DAL|]. exists p0, n0. repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end. split; [exact OIN | lia].
      - unfold uctx. (rewrite !unsigned_lit by lia). unfold parked in S0INV.
        (apply chain_ok_push with (fp1 := bv_unsigned s0)).
        + lia.
        + (clear - SPA; Z.div_mod_to_equations; lia).
        + (unfold USTACK_TOP; lia).
        + (unfold RA_TOP; lia).
        + (apply bv_unsigned_in_range).
        + (rewrite Z_to_bv_bv_unsigned; rewrite <- RATOP; rewrite Z_to_bv_bv_unsigned).
          (lazymatch type of FRrec2 with rw_cells _ _ ?a _ => replace (usp + -16) with a by lia end). (exact FRrec2).
        + (cbn [chain_ok]; unfold link_invalid; lia).
      - (exact tr_deser).
      - lenv_tac.
      - unfold RASTER_COST. lres_tac. }
    after_call RT AF.
    fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]| exact I]).
    lazymatch goal with H : ?p = 0 \/ _ |- _ => rename H into POBJ; set (pixs := p) in * end.
    lazymatch goal with H : pixs = 0 -> rt_live RT _ = _ |- _ => rename H into LVZ end.
    lazymatch goal with H : pixs <> 0 -> live_destroy _ _ _ _ = _ |- _ => rename H into LVD end.
    lazymatch goal with H : pixs <> 0 -> p_cmap _ <> 0 -> _ |- _ => rename H into NZC end.
    lazymatch goal with |- cps _ (ASTA RT ?S _ _) _ => rename S into Sb end.
    (* [comment removed for export] *)
    lazymatch goal with FRx : rw_cells asegs _ (usp + -112) ?cs |- _ =>
      assert (EPI : forall (S : rts RT) (mE : mem)
                (r1 r5 r6 r7 r9 r10 r11 r12 r13 r14 r15 r16 r17 r19 r20 r21 r22 r28 r29 r30 r31 : word) F' fc',
          ART RT S mE -> mem_inv asegs mE -> stk asegs mE lo (usp + -112) -> rw_cells asegs mE (usp + -112) cs ->
          wr_at asegs mE fr 8 -> wr_at asegs mE (fr / 8 + 2147450880) 16 ->
          LIBH mE -> io_ssp mE -> agree_on PF m mE ->
          rt_live RT S = rt_live RT Σ ->
          rt_frames RT S = (fr, 1%nat) :: rt_frames RT Σ -> rt_sp0 RT S = rt_sp0 RT Σ -> rt_credit RT Σ - 2 ^ 31 <= rt_credit RT S ->
          cps asegs (ASTA RT S PMc (eq (entry_st r1 (Z_to_bv 64 (usp + -112)) gp (Z_to_bv 64 TP_A) r5 r6 r7 (Z_to_bv 64 usp) r9
                                          r10 r11 r12 r13 r14 r15 r16 r17 (Z_to_bv 64 fr) r19 r20 r21 r22 (Z_to_bv 64 (fr / 8 + 2147450880))
                                          (Z_to_bv 64 fr) s9 s10 s11 r28 r29 r30 r31 F' fc' 0x90c14 mE))) QF) end.
    { intros S mE r1 r5 r6 r7 r9 r10 r11 r12 r13 r14 r15 r16 r17 r19 r20 r21 r22 r28 r29 r30 r31 F' fc'
        ARTE MIE STE FRE WFE WSE LHE SSPE AGE ELV EFR ESP0 ECR.
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
      repeat match goal with H : rt_frames RT _ = _ |- _ => lazymatch H with EFR => fail | FR0 => fail | _ => clear H end end.
      repeat match goal with H : rt_live RT _ = _ |- _ => lazymatch H with ELV => fail | _ => clear H end end.
      repeat match goal with H : rt_sp0 RT _ = _ |- _ => lazymatch H with ESP0 => fail | _ => clear H end end.
      repeat match goal with H : rt_credit RT _ = _ |- _ => clear H end.
      clear_acc.
      destruct (wr_at_rw_CB mE fr 8 WFE ltac:(lia)) as (jfE & FRME). destruct (wr_at_rw_CB mE (fr / 8 + 2147450880) 16 WSE ltac:(lia)) as (jsE & FSHE).
      change (Z.to_nat 8) with 8%nat in FRME. change (Z.to_nat 16) with 16%nat in FSHE.
      unfold entry_st.
      Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x90c70].
      lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
      Time frame_release_k RT AF GP MST Σ fr 1%nat 128 PF AGF PFS usp lo 0x90c78
        ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
        ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                          repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia])
        ltac:(fun Hx => exact (proj1 Hx))
        ltac:(fun fl FLN => idtac).
      Time walk_to AF MST [(usp - 112, usp)] (@nil Z).
      lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
      lazymatch goal with ST' : stk asegs _ lo (usp + -112), FR' : rw_cells asegs _ (usp + -112) _ |- _ => release_frame FR' ST' usp end.
      cps_stop.
      art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I]).
      lazymatch goal with MUx : munch _ ?mm ?mc |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
        agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]) end.
      apply cps_finish. intros c Hc. subst QF. cbv beta.
      lazymatch type of Hc with ASTA RT ?S' _ _ _ => exists S' end.
      split.
      { eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists.
        split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
        split; [split; [assumption| split; assumption]|].
        split; [intros a Ha Ho; exact (AGF a (conj Ha Ho))|].
        lazymatch goal with LHx : LIBH ?mm |- D_libiface.LIB_A ?mm => destruct LHx as (LH0 & LHH); split; [exact LH0| eexists; exact LHH] end. }
      rewrite LV2, FRS2, SP2, CR2.
      split; [exact ELV|]. split; [exact FR0|]. split; [exact ESP0| lia]. }
    destruct (Z.eq_dec pixs 0) as [PZ|PNZ].
    + (* [comment removed for export] *)
      clear POBJ LVD. pose proof (LVZ PZ) as LVE. clear LVZ. rewrite PZ in *.
      refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
      Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x90c14].
      lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
      cps_stop.
      art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
      lazymatch goal with MUx : munch _ ?mm _ |- _ =>
        agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                           repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
      pose proof FRM as FRH. split_at FRH 1%nat FRH2. clear FRH2.
      to_entry.
      eapply EPI; try eassumption.
      all: lazymatch goal with
           | |- wr_at asegs _ _ 8 => exact (proj2 FRH)
           | |- wr_at asegs _ _ 16 => exact (proj2 FSH)
           | |- rt_live _ _ = _ => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity
           | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
           | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
           | |- _ <= rt_credit _ _ => unfold RASTER_COST in *; repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H in * end; lia
           | |- ?g => idtac "LEFT:" g
           end.
    + (* [comment removed for export] *)
      destruct POBJ as [PZ|(POBJ & VDATA)]; [contradiction|]. clear LVZ. pose proof (LVD PNZ) as LVE. clear LVD.
      lazymatch type of POBJ with pix_obj _ _ _ ?vv ?cc => set (vs := vv) in *; set (cvs := cc) in * end.
      lazymatch goal with H : forall p n, In (p, n) (rt_live RT Sb) -> 0 < n |- _ => rename H into LVPb end.
      lazymatch goal with H : Z.of_nat (length (rt_live RT Sb)) <= _ |- _ => rename H into LVXb end.
      repeat match goal with E : rt_live RT _ = rt_live RT Σ |- _ => rewrite E in LVE end.
      repeat match goal with E : rt_live RT _ = rt_live RT Σ |- _ => rewrite E in LVXb end.
      assert (SUB0b : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Sb)) by (intros e He; rewrite <- LVE in He; exact (proj1 (live_destroy_In _ _ _ _ _ He))).
      assert (PS0 : 0 < pixs) by (destruct POBJ as (_ & (_ & P0 & _) & _); exact P0).
      pose proof POBJ as (_ & (PSIN & _) & _). chunk_facts RT AF GP pixs 64.
      split_last_CB FRM [8%nat; 8%nat; 24%nat; 8%nat; 24%nat; 8%nat; 16%nat].
      split_at FRM 4%nat PSc. split_at PSc 1%nat F5c. split_at F5c 1%nat P1c. split_at P1c 1%nat F7c. split_at F7c 1%nat P2c. split_at P2c 1%nat F9c.
      split_at FRM 1%nat FRMh2.
      hide POBJ.
      (* [comment removed for export] *)
      pose proof (gq_costs_ok (p_d vs)) as (K1P & K2P & K3P & K4P & K5P & K6P & KSUM). unfold RASTER_COST in KSUM.
      set (k1 := D2_COST (p_d vs)) in *. set (k2 := DBIN_COST (p_d vs)) in *. set (k3 := BAND_COST (p_d vs)) in *.
      set (k4 := BAND32_COST (p_d vs)) in *. set (k5 := DISCR32_COST (p_d vs)) in *. set (k6 := THR_COST (p_d vs)) in *.
      assert (NZV : cmap_nz vs cvs) by (unfold cmap_nz; destruct (Z.eq_dec (p_cmap vs) 0) as [Z0|NZ]; [left; exact Z0| right; exact (NZC PNZ NZ)]).
      lazymatch goal with FRx : rw_cells asegs _ (usp + -112) ?cs |- _ =>
        assert (FIN : forall (S : rts RT) (mE : mem) (x1 x2 : word)
                  (r1 r5 r6 r7 r9 r10 r11 r12 r13 r14 r15 r16 r17 r28 r29 r30 r31 : word) F' fc',
            ART RT S mE -> mem_inv asegs mE -> stk asegs mE lo (usp + -112) -> rw_cells asegs mE (usp + -112) cs ->
            rw_cells asegs mE fr [C8 (Z_to_bv 64 1102416563)] ->
            rw_cells asegs mE (fr + 32) [C8 (Z_to_bv 64 pixs)] -> rw_cells asegs mE (fr + 64) [C8 x1] -> rw_cells asegs mE (fr + 96) [C8 x2] ->
            rw_cells asegs mE (fr / 8 + 2147450880) [C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13))] ->
            LIBH mE -> io_ssp mE -> agree_on PF m mE -> pix_obj (rt_live RT Sb) mE pixs vs cvs ->
            rt_live RT S = rt_live RT Sb -> rt_frames RT S = (fr, 1%nat) :: rt_frames RT Σ -> rt_sp0 RT S = rt_sp0 RT Σ ->
            rt_credit RT Σ - (RASTER_COST + 65 + 6 * (TEMPLATE_COST + 2) + (k1 + k2 + k3 + k4 + k5 + k6)) <= rt_credit RT S ->
            cps asegs (ASTA RT S PMc (eq (entry_st r1 (Z_to_bv 64 (usp + -112)) gp (Z_to_bv 64 TP_A) r5 r6 r7 (Z_to_bv 64 usp) r9
                                          r10 r11 r12 r13 r14 r15 r16 r17 (Z_to_bv 64 fr) (Z_to_bv 64 (fr + 32)) (Z_to_bv 64 (fr + 96)) (Z_to_bv 64 (fr + 64)) (Z_to_bv 64 pixs) (Z_to_bv 64 (fr / 8 + 2147450880))
                                          (Z_to_bv 64 fr) s9 s10 s11 r28 r29 r30 r31 F' fc' 0x90c00 mE))) QF) end.
      { intros S mE wx1 wx2 r1 r5 r6 r7 r9 r10 r11 r12 r13 r14 r15 r16 r17 r28 r29 r30 r31 F' fc'
          ARTE MIE STE FRE FHE PSE P1E P2E FSE LHE SSPE AGE POSE ELV EFR ESP0 ECR.
        clear AGF. rename AGE into AGF.
        repeat match goal with H : rw_cells asegs _ _ _ |- _ => lazymatch H with FRE => fail | FHE => fail | PSE => fail | P1E => fail | P2E => fail | FSE => fail | _ => clear H end end.
        repeat match goal with H : ro_cells asegs _ _ _ |- _ => clear H end.
        repeat match goal with H : ART RT _ _ |- _ => lazymatch H with ARTE => fail | _ => clear H end end.
        repeat match goal with H : LIBH _ |- _ => lazymatch H with LHE => fail | _ => clear H end end.
        repeat match goal with H : io_ssp _ |- _ => lazymatch H with SSPE => fail | _ => clear H end end.
        repeat match goal with H : stk asegs _ _ _ |- _ => lazymatch H with STE => fail | _ => clear H end end.
        repeat match goal with H : mem_inv asegs _ |- _ => lazymatch H with MIE => fail | _ => clear H end end.
        repeat match goal with H : wmono asegs _ _ |- _ => clear H end.
        repeat match goal with H : munch _ _ _ |- _ => clear H end.
        repeat match goal with H : rt_frames RT _ = _ |- _ => lazymatch H with EFR => fail | FR0 => fail | _ => clear H end end.
        repeat match goal with H : rt_live RT _ = _ |- _ => lazymatch H with ELV => fail | _ => clear H end end.
        repeat match goal with H : rt_sp0 RT _ = _ |- _ => lazymatch H with ESP0 => fail | _ => clear H end end.
        repeat match goal with H : rt_credit RT _ = _ |- _ => clear H end.
        repeat match goal with H : rt_credit RT _ - _ <= _ |- _ => lazymatch H with ECR => fail | _ => clear H end end.
        clear_acc.
        pose proof FRE as FRrec. split_before FRrec (C8 s0) FRrec2. clear FRrec.
        assert (SPLE : rt_sp0 RT S - 8388608 <= usp - 112) by (rewrite ESP0; ul).
        hide POSE.
        unfold entry_st.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
        Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_pixDeserialize; 0x95bd0; 0x9f3dc; 0x9d968; 0x9eb78; 0xa2460; 0xa2d20; 0xa0ce4; 0x941e0].
        cwalk [e_pixDeserialize; 0x95bd0; 0x9f3dc; 0x9d968; 0x9eb78; 0xa2460; 0xa2d20; 0xa0ce4; 0x941e0].
        lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
        pose proof FSE as SHB4. split_at SHB4 4%nat SHB4b. split_at SHB4b 1%nat SHB4c. clear SHB4 SHB4c.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        unfold hid in POSE.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
          lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT Sx ?mm |- _ =>
            assert (KL : keeps_live (rt_live RT Sx) mm mc)
              by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
                  exact (live_outside_frame1 RT AF Sx mm fr usp (usp - 112) bb kk xx A ltac:(rewrite EFR; left; reflexivity) SPLE Hb Hx)) end end.
        rewrite ELV in KL. pose proof (pix_obj_keep _ _ _ pixs vs cvs KL POSE) as POS1. clear POSE KL.
        pose proof DESTROY as DY. unfold pixDestroy_cps in DY.
        eapply cps_seq.
        { eapply DY with (lo := lo) (pp := fr + 32) (pix := pixs) (v := vs) (cv := cvs) (ras := [RA_TOP]); rt_side idtac.
          all: lazymatch goal with
               | |- optrL _ _ _ _ _ _ =>
                   unfold optrL; split;
                   [ right; exists fr, 1%nat; rewrite EFR; change (fs_size 1) with 128;
                     split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                     split; [lia|]; split; [lia|];
                     replace (shad (fr + 32)) with (fr / 8 + 2147450884) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                     destruct SHB4b as [[_ B] _]; exact B
                   | let Q := fresh "Q" in pose proof FRSH as Q; unfold parked in Q; unfold SEGTOP_A;
                     repeat split; first [clear - FR0; lia | clear - FR64; Z.div_mod_to_equations; lia | clear - Q; lia | clear - FRSEG; lia] ]
               | |- rw_cells _ _ _ [C8 _] => exact PSE
               | |- pix_obj _ _ _ _ _ => rewrite ELV; exact POS1
               | |- uctx _ _ _ _ =>
                   unfold uctx; rewrite ?unsigned_lit by ul; unfold hid, parked in S0INV;
                   apply chain_ok_push with (fp1 := bv_unsigned s0);
                     [ lia | clear - SPA; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | unfold RA_TOP; lia | apply bv_unsigned_in_range
                     | rewrite Z_to_bv_bv_unsigned; rewrite <- RATOP; rewrite Z_to_bv_bv_unsigned; exact FRrec2
                     | cbn [chain_ok]; unfold link_invalid; lia ]
               | |- Forall _ DESTROY_FREE_RAS => rewrite ?unsigned_lit by ul; apply tr_destroy; unfold FUZZ_DESTROY_RAS; cbn [In]; tauto
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   unfold lres, TEMPLATE_COST, RASTER_COST, FRAMES_MAX, LIVE_MAX in *;
                   split; [rewrite EFR, FR0; cbn [length]; lia| split; [rewrite ELV; lia| split; [lia| rewrite ELV; exact LVPb]]]
               | |- ?g => idtac "LEFT:" g
               end. }
        clear POS1 SHB4b.
        after_call RT AF.
        lazymatch goal with H : rt_live RT ?Sx = live_destroy _ _ _ _ |- _ => rewrite ELV, LVE in H end.
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]|
                                        cbn [outside]; destruct (NFA _ Hx) as [N1 N2]; split; [lia| exact I]]).
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
        Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x90c14].
        cwalk [0x90c14].
        lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
        cps_stop.
        art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
        lazymatch goal with MUx : munch _ ?mm _ |- _ =>
          agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                             repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
        to_entry.
        eapply EPI; try eassumption.
        all: lazymatch goal with
             | |- wr_at asegs _ _ 8 => exact (proj2 FHE)
             | |- wr_at asegs _ _ 16 => exact (proj2 FSE)
             | |- rt_live _ _ = _ => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; first [reflexivity | exact LVE]
             | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
             | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
             | |- _ <= rt_credit _ _ => unfold TEMPLATE_COST, RASTER_COST in *; lia
             | |- ?g => idtac "LEFT:" g
             end. }
      lazymatch goal with FRx : rw_cells asegs _ (usp + -112) ?cs |- _ =>
        assert (CONT5 : forall (S : rts RT) (mE : mem) (x1 x2 : word)
                  (r1 r5 r6 r7 r9 r10 r11 r12 r13 r14 r15 r16 r17 r28 r29 r30 r31 : word) F' fc',
            ART RT S mE -> mem_inv asegs mE -> stk asegs mE lo (usp + -112) -> rw_cells asegs mE (usp + -112) cs ->
            rw_cells asegs mE fr [C8 (Z_to_bv 64 1102416563)] ->
            rw_cells asegs mE (fr + 32) [C8 (Z_to_bv 64 pixs)] -> rw_cells asegs mE (fr + 64) [C8 x1] -> rw_cells asegs mE (fr + 96) [C8 x2] ->
            rw_cells asegs mE (fr / 8 + 2147450880) [C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13))] ->
            LIBH mE -> io_ssp mE -> agree_on PF m mE -> pix_obj (rt_live RT Sb) mE pixs vs cvs ->
            rt_live RT S = rt_live RT Sb -> rt_frames RT S = (fr, 1%nat) :: rt_frames RT Σ -> rt_sp0 RT S = rt_sp0 RT Σ ->
            rt_credit RT Σ - (RASTER_COST + 65 + 5 * (TEMPLATE_COST + 2) + (k1 + k2 + k3 + k4 + k5)) <= rt_credit RT S ->
            cps asegs (ASTA RT S PMc (eq (entry_st r1 (Z_to_bv 64 (usp + -112)) gp (Z_to_bv 64 TP_A) r5 r6 r7 (Z_to_bv 64 usp) r9
                                          r10 r11 r12 r13 r14 r15 r16 r17 (Z_to_bv 64 fr) (Z_to_bv 64 (fr + 32)) (Z_to_bv 64 (fr + 96)) (Z_to_bv 64 (fr + 64)) (Z_to_bv 64 pixs) (Z_to_bv 64 (fr / 8 + 2147450880))
                                          (Z_to_bv 64 fr) s9 s10 s11 r28 r29 r30 r31 F' fc' 0x90bc0 mE))) QF) end.
      { intros S mE wx1 wx2 r1 r5 r6 r7 r9 r10 r11 r12 r13 r14 r15 r16 r17 r28 r29 r30 r31 F' fc'
          ARTE MIE STE FRE FHE PSE P1E P2E FSE LHE SSPE AGE POSE ELV EFR ESP0 ECR.
        clear AGF. rename AGE into AGF.
        repeat match goal with H : rw_cells asegs _ _ _ |- _ => lazymatch H with FRE => fail | FHE => fail | PSE => fail | P1E => fail | P2E => fail | FSE => fail | _ => clear H end end.
        repeat match goal with H : ro_cells asegs _ _ _ |- _ => clear H end.
        repeat match goal with H : ART RT _ _ |- _ => lazymatch H with ARTE => fail | _ => clear H end end.
        repeat match goal with H : LIBH _ |- _ => lazymatch H with LHE => fail | _ => clear H end end.
        repeat match goal with H : io_ssp _ |- _ => lazymatch H with SSPE => fail | _ => clear H end end.
        repeat match goal with H : stk asegs _ _ _ |- _ => lazymatch H with STE => fail | _ => clear H end end.
        repeat match goal with H : mem_inv asegs _ |- _ => lazymatch H with MIE => fail | _ => clear H end end.
        repeat match goal with H : wmono asegs _ _ |- _ => clear H end.
        repeat match goal with H : munch _ _ _ |- _ => clear H end.
        repeat match goal with H : rt_frames RT _ = _ |- _ => lazymatch H with EFR => fail | FR0 => fail | _ => clear H end end.
        repeat match goal with H : rt_live RT _ = _ |- _ => lazymatch H with ELV => fail | _ => clear H end end.
        repeat match goal with H : rt_sp0 RT _ = _ |- _ => lazymatch H with ESP0 => fail | _ => clear H end end.
        repeat match goal with H : rt_credit RT _ = _ |- _ => clear H end.
        repeat match goal with H : rt_credit RT _ - _ <= _ |- _ => lazymatch H with ECR => fail | _ => clear H end end.
        clear_acc.
        pose proof FRE as FRrec. split_before FRrec (C8 s0) FRrec2. clear FRrec.
        assert (SPLE : rt_sp0 RT S - 8388608 <= usp - 112) by (rewrite ESP0; ul).
        hide POSE.
        unfold entry_st.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
        Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_pixDeserialize; 0x95bd0; 0x9f3dc; 0x9d968; 0x9eb78; 0xa2460; 0xa2d20; 0xa0ce4; 0x941e0].
        cwalk [e_pixDeserialize; 0x95bd0; 0x9f3dc; 0x9d968; 0x9eb78; 0xa2460; 0xa2d20; 0xa0ce4; 0x941e0].
        lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        unfold hid in POSE.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
          lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT Sx ?mm |- _ =>
            assert (KL : keeps_live (rt_live RT Sx) mm mc)
              by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
                  exact (live_outside_frame1 RT AF Sx mm fr usp (usp - 112) bb kk xx A ltac:(rewrite EFR; left; reflexivity) SPLE Hb Hx)) end end.
        rewrite ELV in KL. pose proof (pix_obj_keep _ _ _ pixs vs cvs KL POSE) as POS1. clear POSE KL.
        pose proof PCOPY as PC. unfold pixCopy_cps in PC.
        eapply cps_seq.
        { eapply PC with (lo := lo) (pixs := pixs) (vs := vs) (cvs := cvs); rt_side idtac.
          all: lazymatch goal with
               | |- pix_obj _ _ _ _ _ => rewrite ELV; exact POS1
               | |- p_data _ <> 0 => exact VDATA
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   unfold lres, TEMPLATE_COST, RASTER_COST, FRAMES_MAX, LIVE_MAX in *;
                   split; [rewrite EFR, FR0; cbn [length]; lia| split; [rewrite ELV; lia| split; [lia| rewrite ELV; exact LVPb]]]
               | |- ?g => idtac "LEFT:" g
               end. }
        after_call RT AF.
        lazymatch goal with AG : agree_on (fun a => aclient ?lv _ _ a /\ outside ?W a) ?ma ?mb |- _ =>
          assert (KL : keeps_live lv ma mb) by (apply (keeps_live_of_agree lv _ _ W ma mb AG); intros; exact I) end.
        rewrite ELV in KL.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ _) _ => rename Sx into Sc end.
        lazymatch goal with H : pix_obj (rt_live RT Sc) _ ?p ?vv ?cc |- _ => rename H into PO1; set (p1 := p) in *; set (v1 := vv) in *; set (c1 := cc) in * end.
        lazymatch goal with H : live_destroy p1 v1 c1 _ = _ |- _ => rename H into LDS1 end. rewrite ELV in LDS1.
        lazymatch goal with H : forall p n, In (p, n) (rt_live RT Sc) -> 0 < n |- _ => rename H into LVPc end.
        lazymatch goal with H : Z.of_nat (length (rt_live RT Sc)) <= _ |- _ => rename H into LVXc end. rewrite ELV in LVXc.
        lazymatch goal with H : p_data v1 <> 0 |- _ => rename H into V1DATA end.
        lazymatch goal with H : p_d v1 = p_d vs |- _ => rename H into VD1 end.
        assert (NZV1 : cmap_nz v1 c1).
        { lazymatch goal with LNC : p_cmap vs = 0 -> _, LCN : p_cmap vs <> 0 -> _ |- _ =>
            unfold cmap_nz in *; destruct (Z.eq_dec (p_cmap vs) 0) as [Z0|NZ];
            [ left; exact (proj1 (LNC Z0)) | right; rewrite (LCN NZ); destruct NZV as [Z1|N1]; [exfalso; exact (NZ Z1)| exact N1] ] end. }
        lazymatch goal with H : p_cmap vs <> 0 -> _ |- _ => clear H end.
        lazymatch goal with H : p_cmap vs = 0 -> _ |- _ => clear H end.
        assert (SUBc : forall e, In e (rt_live RT Sb) -> In e (rt_live RT Sc)) by (intros e He; rewrite <- LDS1 in He; exact (proj1 (live_destroy_In _ _ _ _ _ He))).
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; rewrite ELV; apply SUB0b; exact He| solve [frames_sub_tac]| lia]| exact I]).
        assert (FRSc : rt_frames RT Sc = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
        assert (SPLc : rt_sp0 RT Sc - 8388608 <= usp - 112) by (repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul).
        lazymatch goal with A : ART RT Sc ?mm |- _ =>
          assert (NCP1 : forall a, PF a -> a < p1 \/ p1 + 64 <= a)
            by (intros a [Ha _]; apply (inner_chunk_apart RT AF Sc mm p1 64 (rt_live RT Σ) (rt_frames RT Σ) usp a A (proj1 (pix_obj_entries _ _ _ _ _ PO1)));
                [ intros e He; pose proof (SUB0b e He) as Hb; rewrite <- LDS1 in Hb; destruct (live_destroy_In _ _ _ _ _ Hb) as (Q1 & Q2 & _); split; [exact Q1| exact Q2]
                | solve [frames_sub_tac] | repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul | exact Ha ]) end.
        (* [comment removed for export] *)
        pose proof (proj1 (pix_obj_entries _ _ _ _ _ PO1)) as P1IN.
        chunk_facts RT AF GP p1 64. fframe_chunk RT AF fr 1%nat 128 p1 64.
        pose proof (pix_obj_keep _ _ _ pixs vs cvs KL POS1) as POS2. clear POS1 KL.
        hide PO1. hide POS2.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
        Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_pixDeserialize; 0x95bd0; 0x9f3dc; 0x9d968; 0x9eb78; 0xa2460; 0xa2d20; 0xa0ce4; 0x941e0].
        cwalk [e_pixDeserialize; 0x95bd0; 0x9f3dc; 0x9d968; 0x9eb78; 0xa2460; 0xa2d20; 0xa0ce4; 0x941e0].
        lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        unfold hid in PO1, POS2.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
          lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT Sx ?mm |- _ =>
            assert (KL : keeps_live (rt_live RT Sx) mm mc)
              by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
                  exact (live_outside_frame1 RT AF Sx mm fr usp (usp - 112) bb kk xx A ltac:(rewrite FRSc; left; reflexivity) SPLc Hb Hx)) end end.
        pose proof (pix_obj_keep _ _ _ p1 v1 c1 KL PO1) as PO1b. pose proof (pix_obj_keep _ _ _ pixs vs cvs (keeps_live_sub _ _ _ _ KL SUBc) POS2) as POS3. clear PO1 POS2 KL.
        (* [comment removed for export] *)
        pose proof OP6 as GK. unfold pixThresholdGrayArb_cps, gq_op_cps in GK.
        eapply cps_seq.
        { eapply GK with (lo := lo) (pix := p1) (v := v1) (cv := c1) (ras := [RA_TOP]); rt_side idtac.
          all: lazymatch goal with
               | |- pix_obj _ _ _ _ _ => exact PO1b
               | |- p_data _ <> 0 => exact V1DATA
               | |- cmap_nz _ _ => exact NZV1
               | |- uctx _ _ _ _ =>
                   unfold uctx; rewrite ?unsigned_lit by ul; unfold hid, parked in S0INV;
                   apply chain_ok_push with (fp1 := bv_unsigned s0);
                     [ lia | clear - SPA; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | unfold RA_TOP; lia | apply bv_unsigned_in_range
                     | rewrite Z_to_bv_bv_unsigned; rewrite <- RATOP; rewrite Z_to_bv_bv_unsigned; exact FRrec2
                     | cbn [chain_ok]; unfold link_invalid; lia ]
               | |- bv_unsigned _ = _ => rewrite ?unsigned_lit by ul; reflexivity
               | |- _ = [RA_TOP] => reflexivity
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   rewrite VD1; fold k6; unfold lres, TEMPLATE_COST, RASTER_COST, FRAMES_MAX, LIVE_MAX in *;
                   split; [rewrite FRSc, FR0; cbn [length]; lia| split; [lia| split; [lia| exact LVPc]]]
               | |- wZ _ _ => reflexivity
               | |- True => exact I
               | |- _ /\ _ =>      (* [comment removed for export] *)
                   repeat split;
                   first [ reflexivity
                         | unfold freg_is, fa0, fa1;
                           first [ etransitivity; [apply freg_get_same; reflexivity| vm_compute; reflexivity]
                                 | rewrite freg_get_other by reflexivity; etransitivity; [apply freg_get_same; reflexivity| vm_compute; reflexivity] ] ]
               | |- ?g => idtac "LEFT:" g
               end. }
        after_call RT AF.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ _) _ => rename Sx into Sd end.
        lazymatch goal with H : pix_obj (rt_live RT Sd) _ p1 v1 c1 |- _ => rename H into PO1d end.
        lazymatch goal with H : ?r = 0 \/ (pix_obj (rt_live RT Sd) _ ?r ?vv ?cc /\ _) |- _ => rename H into PRd; set (rr := r) in *; set (vr := vv) in *; set (cr := cc) in * end.
        lazymatch goal with H : rr = 0 -> rt_live RT Sd = _ |- _ => rename H into LZd end.
        lazymatch goal with H : rr <> 0 -> live_destroy rr vr cr _ = _ |- _ => rename H into LDd end.
        lazymatch goal with H : forall p n, In (p, n) (rt_live RT Sd) -> 0 < n |- _ => rename H into LVPd end.
        lazymatch goal with H : Z.of_nat (length (rt_live RT Sd)) <= _ |- _ => rename H into LVXd end.
        lazymatch goal with H : rt_credit RT Sc - _ <= rt_credit RT Sd |- _ => rewrite VD1 in H; fold k6 in H end.
        assert (SUBd : forall e, In e (rt_live RT Sc) -> In e (rt_live RT Sd)).
        { intros e He. destruct (Z.eq_dec rr 0) as [Z0|NZ]; [rewrite (LZd Z0); exact He|]. rewrite <- (LDd NZ) in He. exact (live_destroy_sub _ _ _ _ _ He). }
        (* [comment removed for export] *)
        lazymatch goal with AG : agree_on (fun a => aclient (rt_live RT Sc) _ _ a /\ outside _ a) ?ma ?mb, A : ART RT Sc ?mx |- _ =>
          assert (KL : keeps_live (rt_live RT Sb) ma mb)
            by (apply (keeps_live_others RT AF Sc mx _ _ (rt_live RT Sb) p1 64 (p1 + 20) (p1 + 24) ma mb A
                         (proj1 (pix_obj_entries _ _ _ _ _ PO1b)) ltac:(lia) ltac:(lia)
                         ltac:(intros e He; split; [exact (SUBc e He)| rewrite <- LDS1 in He; exact (proj1 (proj2 (live_destroy_In _ _ _ _ _ He)))]) AG)) end.
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; apply SUBc; apply SUB0b; exact He| solve [frames_sub_tac]| lia]|
                                        cbn [outside]; pose proof (NCP1 _ Hx) as NCPx; split; [clear - NCPx; lia| exact I]]).
        assert (FRSd : rt_frames RT Sd = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
        assert (SPLd : rt_sp0 RT Sd - 8388608 <= usp - 112) by (repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul).
        pose proof (pix_obj_keep _ _ _ pixs vs cvs KL POS3) as POS4. clear POS3 KL.
        hide PO1b. hide PO1d. hide POS4. hide PRd. hide LZd. hide LDd.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
        Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_pixDeserialize; 0x95bd0; 0x9f3dc; 0x9d968; 0x9eb78; 0xa2460; 0xa2d20; 0xa0ce4; 0x941e0].
        cwalk [e_pixDeserialize; 0x95bd0; 0x9f3dc; 0x9d968; 0x9eb78; 0xa2460; 0xa2d20; 0xa0ce4; 0x941e0].
        lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
        pose proof FSE as SHB8. split_at SHB8 8%nat SHB8b. split_at SHB8b 1%nat SHB8c. clear SHB8 SHB8c.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        unfold hid in PO1d, POS4, PRd.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
          lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT Sx ?mm |- _ =>
            assert (KL : keeps_live (rt_live RT Sx) mm mc)
              by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
                  exact (live_outside_frame1 RT AF Sx mm fr usp (usp - 112) bb kk xx A ltac:(rewrite FRSd; left; reflexivity) SPLd Hb Hx)) end end.
        pose proof (pix_obj_keep _ _ _ p1 v1 c1 KL PO1d) as PO1e.
        pose proof (pix_obj_keep _ _ _ pixs vs cvs (keeps_live_sub _ _ _ _ KL (fun e He => SUBd e (SUBc e He))) POS4) as POS5.
        assert (PRd3 : rr = 0 \/ (pix_obj (rt_live RT Sd) _ rr vr cr /\ p_data vr <> 0))
          by (destruct PRd as [Z0|(PO & DN)]; [left; exact Z0| right; split; [exact (pix_obj_keep _ _ _ rr vr cr KL PO)| exact DN]]).
        clear PO1d POS4 PRd KL.
        pose proof DESTROY as DY. unfold pixDestroy_cps in DY.
        eapply cps_seq.
        { eapply DY with (lo := lo) (pp := fr + 64) (pix := p1) (v := v1) (cv := c1) (ras := [RA_TOP]); rt_side idtac.
          all: lazymatch goal with
               | |- optrL _ _ _ _ _ _ =>
                   unfold optrL; split;
                   [ right; exists fr, 1%nat; rewrite FRSd; change (fs_size 1) with 128;
                     split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                     split; [lia|]; split; [lia|];
                     replace (shad (fr + 64)) with (fr / 8 + 2147450888) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                     destruct SHB8b as [[_ B] _]; exact B
                   | let Q := fresh "Q" in pose proof FRSH as Q; unfold parked in Q; unfold SEGTOP_A;
                     repeat split; first [clear - FR0; lia | clear - FR64; Z.div_mod_to_equations; lia | clear - Q; lia | clear - FRSEG; lia] ]
               | |- rw_cells _ _ _ [C8 _] => exact P1E
               | |- pix_obj _ _ _ _ _ => exact PO1e
               | |- uctx _ _ _ _ =>
                   unfold uctx; rewrite ?unsigned_lit by ul; unfold hid, parked in S0INV;
                   apply chain_ok_push with (fp1 := bv_unsigned s0);
                     [ lia | clear - SPA; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | unfold RA_TOP; lia | apply bv_unsigned_in_range
                     | rewrite Z_to_bv_bv_unsigned; rewrite <- RATOP; rewrite Z_to_bv_bv_unsigned; exact FRrec2
                     | cbn [chain_ok]; unfold link_invalid; lia ]
               | |- Forall _ DESTROY_FREE_RAS => rewrite ?unsigned_lit by ul; apply tr_destroy; unfold FUZZ_DESTROY_RAS; cbn [In]; tauto
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   unfold lres, TEMPLATE_COST, RASTER_COST, FRAMES_MAX, LIVE_MAX in *;
                   split; [rewrite FRSd, FR0; cbn [length]; lia| split; [lia| split; [lia| exact LVPd]]]
               | |- ?g => idtac "LEFT:" g
               end. }
        clear SHB8b.
        after_call RT AF.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ _) _ => rename Sx into Se end.
        lazymatch goal with H : rt_live RT Se = _ |- _ => rename H into LVe end.
        assert (FRSe : rt_frames RT Se = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
        assert (SPLe : rt_sp0 RT Se - 8388608 <= usp - 112) by (repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul).
        assert (SUBe : forall e, In e (rt_live RT Sb) -> In e (rt_live RT Se))
          by (intros e He; rewrite LVe; rewrite <- LDS1 in He; exact (live_destroy_mono p1 v1 c1 _ _ SUBd e He)).
        lazymatch goal with AG : agree_on (fun a => aclient ?lv _ _ a /\ outside ?W a) ?ma ?mb, A : ART RT Se ?mb |- _ =>
          assert (KL : keeps_live lv ma mb)
            by (apply (keeps_live_of_agree lv _ _ W ma mb AG); intros bb kk xx Hb Hx;
                exact (live_outside_local RT AF Se mb fr 1%nat 64 bb kk xx A ltac:(rewrite FRSe; left; reflexivity) ltac:(lia) ltac:(change (fs_size 1) with 128; lia) Hb Hx)) end.
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; apply SUBe; apply SUB0b; exact He| solve [frames_sub_tac]| lia]|
                                        cbn [outside]; destruct (NFA _ Hx) as [N1 N2]; split; [lia| exact I]]).
        pose proof (pix_obj_keep _ _ _ pixs vs cvs (keeps_live_sub _ _ _ _ KL SUBe) POS5) as POS6.
        assert (LVPe : forall p n, In (p, n) (rt_live RT Se) -> 0 < n)
          by (intros p n H; rewrite LVe in H; exact (LVPd p n (live_destroy_sub _ _ _ _ _ H))).
        assert (LVXe : Z.of_nat (length (rt_live RT Se)) <= Z.of_nat (length (rt_live RT Sd)))
          by (rewrite LVe; pose proof (live_destroy_len p1 v1 c1 (rt_live RT Sd)); lia).
        unfold hid in LZd, LDd, PO1b.
        destruct (Z.eq_dec rr 0) as [RZ|RNZ].
        - (* [comment removed for export] *)
          clear PRd3. assert (LVe0 : rt_live RT Se = rt_live RT Sb) by (rewrite LVe, (LZd RZ); exact LDS1).
          clear LVe KL. rewrite RZ in *.
          hide POS6.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
        Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_pixDeserialize; 0x95bd0; 0x9f3dc; 0x9d968; 0x9eb78; 0xa2460; 0xa2d20; 0xa0ce4; 0x941e0].
        cwalk [e_pixDeserialize; 0x95bd0; 0x9f3dc; 0x9d968; 0x9eb78; 0xa2460; 0xa2d20; 0xa0ce4; 0x941e0].
        lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
        pose proof FSE as SHB12. split_at SHB12 12%nat SHB12b. split_at SHB12b 1%nat SHB12c. clear SHB12 SHB12c.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        unfold hid in POS6.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
          lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT Sx ?mm |- _ =>
            assert (KL : keeps_live (rt_live RT Sx) mm mc)
              by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
                  exact (live_outside_frame1 RT AF Sx mm fr usp (usp - 112) bb kk xx A ltac:(rewrite FRSe; left; reflexivity) SPLe Hb Hx)) end end.
        pose proof (pix_obj_keep _ _ _ pixs vs cvs (keeps_live_sub _ _ _ _ KL SUBe) POS6) as POS7. clear POS6 KL.
        pose proof DNULL as DN. unfold pixDestroy_null_cps in DN.
        eapply cps_seq.
        { eapply DN with (lo := lo) (pp := fr + 96); rt_side idtac.
          all: lazymatch goal with
               | |- optrL _ _ _ _ _ _ =>
                   unfold optrL; split;
                   [ right; exists fr, 1%nat; rewrite FRSe; change (fs_size 1) with 128;
                     split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                     split; [lia|]; split; [lia|];
                     replace (shad (fr + 96)) with (fr / 8 + 2147450892) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                     destruct SHB12b as [[_ B] _]; exact B
                   | let Q := fresh "Q" in pose proof FRSH as Q; unfold parked in Q; unfold SEGTOP_A;
                     repeat split; first [clear - FR0; lia | clear - FR64; Z.div_mod_to_equations; lia | clear - Q; lia | clear - FRSEG; lia] ]
               | |- rw_cells _ _ _ [C8 _] => exact P2E
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   unfold lres, TEMPLATE_COST, RASTER_COST, FRAMES_MAX, LIVE_MAX in *;
                   split; [rewrite FRSe, FR0; cbn [length]; lia| split; [rewrite LVe0; lia| split; [lia| exact LVPe]]]
               | |- ?g => idtac "LEFT:" g
               end. }
        clear SHB12b.
        after_call RT AF.
        lazymatch goal with AG : agree_on (fun a => aclient ?lv _ _ a /\ outside ?W a) ?ma ?mb |- _ =>
          assert (KL : keeps_live lv ma mb) by (apply (keeps_live_of_agree lv _ _ W ma mb AG); intros; exact I) end.
        lazymatch goal with H : rt_live RT ?Sx = rt_live RT Se |- _ => rewrite LVe0 in H; rewrite H in KL end.
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; apply SUB0b; exact He| solve [frames_sub_tac]| lia]| exact I]).
        pose proof (pix_obj_keep _ _ _ pixs vs cvs KL POS7) as POS8. clear POS7 KL.
          to_entry.
          eapply FIN; try eassumption.
          all: lazymatch goal with
               | |- pix_obj _ _ _ _ _ => exact POS8
               | |- rt_live _ _ = _ => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity
               | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
               | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
               | |- _ <= rt_credit _ _ => unfold TEMPLATE_COST, RASTER_COST in *; lia
               | |- ?g => idtac "LEFT:" g
               end.
        - (* [comment removed for export] *)
          destruct PRd3 as [Z0|(POR & RDATA)]; [exfalso; exact (RNZ Z0)|].
          pose proof (obj_fresh_of_eq (rt_live RT Sd) (rt_live RT Sc) _ rr vr cr _ p1 v1 c1 (LDd RNZ) POR PO1b) as FRESH.
          pose proof (pix_obj_in_destroy (rt_live RT Sd) _ rr vr cr p1 v1 c1 POR FRESH) as PORe0. rewrite <- LVe in PORe0.
          pose proof (pix_obj_keep _ _ _ rr vr cr KL PORe0) as PORe. clear POR PORe0 FRESH KL.
          assert (LVf0 : live_destroy rr vr cr (rt_live RT Se) = rt_live RT Sb)
            by (rewrite LVe, live_destroy_comm, (LDd RNZ); exact LDS1).
          hide POS6. hide PORe. hide LVf0.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
        Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_pixDeserialize; 0x95bd0; 0x9f3dc; 0x9d968; 0x9eb78; 0xa2460; 0xa2d20; 0xa0ce4; 0x941e0].
        cwalk [e_pixDeserialize; 0x95bd0; 0x9f3dc; 0x9d968; 0x9eb78; 0xa2460; 0xa2d20; 0xa0ce4; 0x941e0].
        lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
        pose proof FSE as SHB12. split_at SHB12 12%nat SHB12b. split_at SHB12b 1%nat SHB12c. clear SHB12 SHB12c.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        unfold hid in POS6, PORe.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
          lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT Sx ?mm |- _ =>
            assert (KL : keeps_live (rt_live RT Sx) mm mc)
              by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
                  exact (live_outside_frame1 RT AF Sx mm fr usp (usp - 112) bb kk xx A ltac:(rewrite FRSe; left; reflexivity) SPLe Hb Hx)) end end.
        pose proof (pix_obj_keep _ _ _ pixs vs cvs (keeps_live_sub _ _ _ _ KL SUBe) POS6) as POS7. pose proof (pix_obj_keep _ _ _ rr vr cr KL PORe) as POR2. clear POS6 PORe KL.
        eapply cps_seq.
        { eapply DY with (lo := lo) (pp := fr + 96) (pix := rr) (v := vr) (cv := cr) (ras := [RA_TOP]); rt_side idtac.
          all: lazymatch goal with
               | |- optrL _ _ _ _ _ _ =>
                   unfold optrL; split;
                   [ right; exists fr, 1%nat; rewrite FRSe; change (fs_size 1) with 128;
                     split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                     split; [lia|]; split; [lia|];
                     replace (shad (fr + 96)) with (fr / 8 + 2147450892) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                     destruct SHB12b as [[_ B] _]; exact B
                   | let Q := fresh "Q" in pose proof FRSH as Q; unfold parked in Q; unfold SEGTOP_A;
                     repeat split; first [clear - FR0; lia | clear - FR64; Z.div_mod_to_equations; lia | clear - Q; lia | clear - FRSEG; lia] ]
               | |- rw_cells _ _ _ [C8 _] => exact P2E
               | |- pix_obj _ _ _ _ _ => exact POR2
               | |- uctx _ _ _ _ =>
                   unfold uctx; rewrite ?unsigned_lit by ul; unfold hid, parked in S0INV;
                   apply chain_ok_push with (fp1 := bv_unsigned s0);
                     [ lia | clear - SPA; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | unfold RA_TOP; lia | apply bv_unsigned_in_range
                     | rewrite Z_to_bv_bv_unsigned; rewrite <- RATOP; rewrite Z_to_bv_bv_unsigned; exact FRrec2
                     | cbn [chain_ok]; unfold link_invalid; lia ]
               | |- Forall _ DESTROY_FREE_RAS => rewrite ?unsigned_lit by ul; apply tr_destroy; unfold FUZZ_DESTROY_RAS; cbn [In]; tauto
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   unfold lres, TEMPLATE_COST, RASTER_COST, FRAMES_MAX, LIVE_MAX in *;
                   split; [rewrite FRSe, FR0; cbn [length]; lia| split; [lia| split; [lia| exact LVPe]]]
               | |- ?g => idtac "LEFT:" g
               end. }
        clear POR2 SHB12b.
        after_call RT AF.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ _) _ => rename Sx into Sf end.
        lazymatch goal with H : rt_live RT Sf = _ |- _ => rename H into LVf end.
        unfold hid in LVf0. rewrite LVf0 in LVf.
        assert (FRSf : rt_frames RT Sf = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
        lazymatch goal with AG : agree_on (fun a => aclient ?lv _ _ a /\ outside ?W a) ?ma ?mb, A : ART RT Sf ?mb |- _ =>
          assert (KL : keeps_live lv ma mb)
            by (apply (keeps_live_of_agree lv _ _ W ma mb AG); intros bb kk xx Hb Hx;
                exact (live_outside_local RT AF Sf mb fr 1%nat 96 bb kk xx A ltac:(rewrite FRSf; left; reflexivity) ltac:(lia) ltac:(change (fs_size 1) with 128; lia) Hb Hx)) end.
        rewrite LVf in KL.
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; rewrite LVf; apply SUB0b; exact He| solve [frames_sub_tac]| lia]|
                                        cbn [outside]; destruct (NFA _ Hx) as [N1 N2]; split; [lia| exact I]]).
        pose proof (pix_obj_keep _ _ _ pixs vs cvs KL POS7) as POS8. clear POS7 KL.
          to_entry.
          eapply FIN; try eassumption.
          all: lazymatch goal with
               | |- pix_obj _ _ _ _ _ => exact POS8
               | |- rt_live _ _ = _ => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity
               | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
               | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
               | |- _ <= rt_credit _ _ => unfold TEMPLATE_COST, RASTER_COST in *; lia
               | |- ?g => idtac "LEFT:" g
               end.
      }
      lazymatch goal with FRx : rw_cells asegs _ (usp + -112) ?cs |- _ =>
        assert (CONT4 : forall (S : rts RT) (mE : mem) (x1 x2 : word)
                  (r1 r5 r6 r7 r9 r10 r11 r12 r13 r14 r15 r16 r17 r28 r29 r30 r31 : word) F' fc',
            ART RT S mE -> mem_inv asegs mE -> stk asegs mE lo (usp + -112) -> rw_cells asegs mE (usp + -112) cs ->
            rw_cells asegs mE fr [C8 (Z_to_bv 64 1102416563)] ->
            rw_cells asegs mE (fr + 32) [C8 (Z_to_bv 64 pixs)] -> rw_cells asegs mE (fr + 64) [C8 x1] -> rw_cells asegs mE (fr + 96) [C8 x2] ->
            rw_cells asegs mE (fr / 8 + 2147450880) [C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13))] ->
            LIBH mE -> io_ssp mE -> agree_on PF m mE -> pix_obj (rt_live RT Sb) mE pixs vs cvs ->
            rt_live RT S = rt_live RT Sb -> rt_frames RT S = (fr, 1%nat) :: rt_frames RT Σ -> rt_sp0 RT S = rt_sp0 RT Σ ->
            rt_credit RT Σ - (RASTER_COST + 65 + 4 * (TEMPLATE_COST + 2) + (k1 + k2 + k3 + k4)) <= rt_credit RT S ->
            cps asegs (ASTA RT S PMc (eq (entry_st r1 (Z_to_bv 64 (usp + -112)) gp (Z_to_bv 64 TP_A) r5 r6 r7 (Z_to_bv 64 usp) r9
                                          r10 r11 r12 r13 r14 r15 r16 r17 (Z_to_bv 64 fr) (Z_to_bv 64 (fr + 32)) (Z_to_bv 64 (fr + 96)) (Z_to_bv 64 (fr + 64)) (Z_to_bv 64 pixs) (Z_to_bv 64 (fr / 8 + 2147450880))
                                          (Z_to_bv 64 fr) s9 s10 s11 r28 r29 r30 r31 F' fc' 0x90b8c mE))) QF) end.
      { intros S mE wx1 wx2 r1 r5 r6 r7 r9 r10 r11 r12 r13 r14 r15 r16 r17 r28 r29 r30 r31 F' fc'
          ARTE MIE STE FRE FHE PSE P1E P2E FSE LHE SSPE AGE POSE ELV EFR ESP0 ECR.
        clear AGF. rename AGE into AGF.
        repeat match goal with H : rw_cells asegs _ _ _ |- _ => lazymatch H with FRE => fail | FHE => fail | PSE => fail | P1E => fail | P2E => fail | FSE => fail | _ => clear H end end.
        repeat match goal with H : ro_cells asegs _ _ _ |- _ => clear H end.
        repeat match goal with H : ART RT _ _ |- _ => lazymatch H with ARTE => fail | _ => clear H end end.
        repeat match goal with H : LIBH _ |- _ => lazymatch H with LHE => fail | _ => clear H end end.
        repeat match goal with H : io_ssp _ |- _ => lazymatch H with SSPE => fail | _ => clear H end end.
        repeat match goal with H : stk asegs _ _ _ |- _ => lazymatch H with STE => fail | _ => clear H end end.
        repeat match goal with H : mem_inv asegs _ |- _ => lazymatch H with MIE => fail | _ => clear H end end.
        repeat match goal with H : wmono asegs _ _ |- _ => clear H end.
        repeat match goal with H : munch _ _ _ |- _ => clear H end.
        repeat match goal with H : rt_frames RT _ = _ |- _ => lazymatch H with EFR => fail | FR0 => fail | _ => clear H end end.
        repeat match goal with H : rt_live RT _ = _ |- _ => lazymatch H with ELV => fail | _ => clear H end end.
        repeat match goal with H : rt_sp0 RT _ = _ |- _ => lazymatch H with ESP0 => fail | _ => clear H end end.
        repeat match goal with H : rt_credit RT _ = _ |- _ => clear H end.
        repeat match goal with H : rt_credit RT _ - _ <= _ |- _ => lazymatch H with ECR => fail | _ => clear H end end.
        clear_acc.
        pose proof FRE as FRrec. split_before FRrec (C8 s0) FRrec2. clear FRrec.
        assert (SPLE : rt_sp0 RT S - 8388608 <= usp - 112) by (rewrite ESP0; ul).
        hide POSE.
        unfold entry_st.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
        Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_pixDeserialize; 0x95bd0; 0x9f3dc; 0x9d968; 0x9eb78; 0xa2460; 0xa2d20; 0xa0ce4; 0x941e0].
        cwalk [e_pixDeserialize; 0x95bd0; 0x9f3dc; 0x9d968; 0x9eb78; 0xa2460; 0xa2d20; 0xa0ce4; 0x941e0].
        lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        unfold hid in POSE.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
          lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT Sx ?mm |- _ =>
            assert (KL : keeps_live (rt_live RT Sx) mm mc)
              by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
                  exact (live_outside_frame1 RT AF Sx mm fr usp (usp - 112) bb kk xx A ltac:(rewrite EFR; left; reflexivity) SPLE Hb Hx)) end end.
        rewrite ELV in KL. pose proof (pix_obj_keep _ _ _ pixs vs cvs KL POSE) as POS1. clear POSE KL.
        pose proof PCOPY as PC. unfold pixCopy_cps in PC.
        eapply cps_seq.
        { eapply PC with (lo := lo) (pixs := pixs) (vs := vs) (cvs := cvs); rt_side idtac.
          all: lazymatch goal with
               | |- pix_obj _ _ _ _ _ => rewrite ELV; exact POS1
               | |- p_data _ <> 0 => exact VDATA
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   unfold lres, TEMPLATE_COST, RASTER_COST, FRAMES_MAX, LIVE_MAX in *;
                   split; [rewrite EFR, FR0; cbn [length]; lia| split; [rewrite ELV; lia| split; [lia| rewrite ELV; exact LVPb]]]
               | |- ?g => idtac "LEFT:" g
               end. }
        after_call RT AF.
        lazymatch goal with AG : agree_on (fun a => aclient ?lv _ _ a /\ outside ?W a) ?ma ?mb |- _ =>
          assert (KL : keeps_live lv ma mb) by (apply (keeps_live_of_agree lv _ _ W ma mb AG); intros; exact I) end.
        rewrite ELV in KL.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ _) _ => rename Sx into Sc end.
        lazymatch goal with H : pix_obj (rt_live RT Sc) _ ?p ?vv ?cc |- _ => rename H into PO1; set (p1 := p) in *; set (v1 := vv) in *; set (c1 := cc) in * end.
        lazymatch goal with H : live_destroy p1 v1 c1 _ = _ |- _ => rename H into LDS1 end. rewrite ELV in LDS1.
        lazymatch goal with H : forall p n, In (p, n) (rt_live RT Sc) -> 0 < n |- _ => rename H into LVPc end.
        lazymatch goal with H : Z.of_nat (length (rt_live RT Sc)) <= _ |- _ => rename H into LVXc end. rewrite ELV in LVXc.
        lazymatch goal with H : p_data v1 <> 0 |- _ => rename H into V1DATA end.
        lazymatch goal with H : p_d v1 = p_d vs |- _ => rename H into VD1 end.
        assert (NZV1 : cmap_nz v1 c1).
        { lazymatch goal with LNC : p_cmap vs = 0 -> _, LCN : p_cmap vs <> 0 -> _ |- _ =>
            unfold cmap_nz in *; destruct (Z.eq_dec (p_cmap vs) 0) as [Z0|NZ];
            [ left; exact (proj1 (LNC Z0)) | right; rewrite (LCN NZ); destruct NZV as [Z1|N1]; [exfalso; exact (NZ Z1)| exact N1] ] end. }
        lazymatch goal with H : p_cmap vs <> 0 -> _ |- _ => clear H end.
        lazymatch goal with H : p_cmap vs = 0 -> _ |- _ => clear H end.
        assert (SUBc : forall e, In e (rt_live RT Sb) -> In e (rt_live RT Sc)) by (intros e He; rewrite <- LDS1 in He; exact (proj1 (live_destroy_In _ _ _ _ _ He))).
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; rewrite ELV; apply SUB0b; exact He| solve [frames_sub_tac]| lia]| exact I]).
        assert (FRSc : rt_frames RT Sc = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
        assert (SPLc : rt_sp0 RT Sc - 8388608 <= usp - 112) by (repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul).
        lazymatch goal with A : ART RT Sc ?mm |- _ =>
          assert (NCP1 : forall a, PF a -> a < p1 \/ p1 + 64 <= a)
            by (intros a [Ha _]; apply (inner_chunk_apart RT AF Sc mm p1 64 (rt_live RT Σ) (rt_frames RT Σ) usp a A (proj1 (pix_obj_entries _ _ _ _ _ PO1)));
                [ intros e He; pose proof (SUB0b e He) as Hb; rewrite <- LDS1 in Hb; destruct (live_destroy_In _ _ _ _ _ Hb) as (Q1 & Q2 & _); split; [exact Q1| exact Q2]
                | solve [frames_sub_tac] | repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul | exact Ha ]) end.
        (* [comment removed for export] *)
        pose proof (proj1 (pix_obj_entries _ _ _ _ _ PO1)) as P1IN.
        chunk_facts RT AF GP p1 64. fframe_chunk RT AF fr 1%nat 128 p1 64.
        pose proof (pix_obj_keep _ _ _ pixs vs cvs KL POS1) as POS2. clear POS1 KL.
        hide PO1. hide POS2.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
        Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_pixDeserialize; 0x95bd0; 0x9f3dc; 0x9d968; 0x9eb78; 0xa2460; 0xa2d20; 0xa0ce4; 0x941e0].
        cwalk [e_pixDeserialize; 0x95bd0; 0x9f3dc; 0x9d968; 0x9eb78; 0xa2460; 0xa2d20; 0xa0ce4; 0x941e0].
        lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        unfold hid in PO1, POS2.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
          lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT Sx ?mm |- _ =>
            assert (KL : keeps_live (rt_live RT Sx) mm mc)
              by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
                  exact (live_outside_frame1 RT AF Sx mm fr usp (usp - 112) bb kk xx A ltac:(rewrite FRSc; left; reflexivity) SPLc Hb Hx)) end end.
        pose proof (pix_obj_keep _ _ _ p1 v1 c1 KL PO1) as PO1b. pose proof (pix_obj_keep _ _ _ pixs vs cvs (keeps_live_sub _ _ _ _ KL SUBc) POS2) as POS3. clear PO1 POS2 KL.
        (* [comment removed for export] *)
        pose proof OP5 as GK. unfold pixGenerateMaskByDiscr32_cps, gq_op_cps in GK.
        eapply cps_seq.
        { eapply GK with (lo := lo) (pix := p1) (v := v1) (cv := c1) (ras := [RA_TOP]); rt_side idtac.
          all: lazymatch goal with
               | |- pix_obj _ _ _ _ _ => exact PO1b
               | |- p_data _ <> 0 => exact V1DATA
               | |- cmap_nz _ _ => exact NZV1
               | |- uctx _ _ _ _ =>
                   unfold uctx; rewrite ?unsigned_lit by ul; unfold hid, parked in S0INV;
                   apply chain_ok_push with (fp1 := bv_unsigned s0);
                     [ lia | clear - SPA; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | unfold RA_TOP; lia | apply bv_unsigned_in_range
                     | rewrite Z_to_bv_bv_unsigned; rewrite <- RATOP; rewrite Z_to_bv_bv_unsigned; exact FRrec2
                     | cbn [chain_ok]; unfold link_invalid; lia ]
               | |- bv_unsigned _ = _ => rewrite ?unsigned_lit by ul; reflexivity
               | |- _ = [RA_TOP] => reflexivity
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   rewrite VD1; fold k5; unfold lres, TEMPLATE_COST, RASTER_COST, FRAMES_MAX, LIVE_MAX in *;
                   split; [rewrite FRSc, FR0; cbn [length]; lia| split; [lia| split; [lia| exact LVPc]]]
               | |- wZ _ _ => reflexivity
               | |- True => exact I
               | |- _ /\ _ =>      (* [comment removed for export] *)
                   repeat split;
                   first [ reflexivity
                         | unfold freg_is, fa0, fa1;
                           first [ etransitivity; [apply freg_get_same; reflexivity| vm_compute; reflexivity]
                                 | rewrite freg_get_other by reflexivity; etransitivity; [apply freg_get_same; reflexivity| vm_compute; reflexivity] ] ]
               | |- ?g => idtac "LEFT:" g
               end. }
        after_call RT AF.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ _) _ => rename Sx into Sd end.
        lazymatch goal with H : pix_obj (rt_live RT Sd) _ p1 v1 c1 |- _ => rename H into PO1d end.
        lazymatch goal with H : ?r = 0 \/ (pix_obj (rt_live RT Sd) _ ?r ?vv ?cc /\ _) |- _ => rename H into PRd; set (rr := r) in *; set (vr := vv) in *; set (cr := cc) in * end.
        lazymatch goal with H : rr = 0 -> rt_live RT Sd = _ |- _ => rename H into LZd end.
        lazymatch goal with H : rr <> 0 -> live_destroy rr vr cr _ = _ |- _ => rename H into LDd end.
        lazymatch goal with H : forall p n, In (p, n) (rt_live RT Sd) -> 0 < n |- _ => rename H into LVPd end.
        lazymatch goal with H : Z.of_nat (length (rt_live RT Sd)) <= _ |- _ => rename H into LVXd end.
        lazymatch goal with H : rt_credit RT Sc - _ <= rt_credit RT Sd |- _ => rewrite VD1 in H; fold k5 in H end.
        assert (SUBd : forall e, In e (rt_live RT Sc) -> In e (rt_live RT Sd)).
        { intros e He. destruct (Z.eq_dec rr 0) as [Z0|NZ]; [rewrite (LZd Z0); exact He|]. rewrite <- (LDd NZ) in He. exact (live_destroy_sub _ _ _ _ _ He). }
        (* [comment removed for export] *)
        lazymatch goal with AG : agree_on (fun a => aclient (rt_live RT Sc) _ _ a /\ outside _ a) ?ma ?mb, A : ART RT Sc ?mx |- _ =>
          assert (KL : keeps_live (rt_live RT Sb) ma mb)
            by (apply (keeps_live_others RT AF Sc mx _ _ (rt_live RT Sb) p1 64 (p1 + 20) (p1 + 24) ma mb A
                         (proj1 (pix_obj_entries _ _ _ _ _ PO1b)) ltac:(lia) ltac:(lia)
                         ltac:(intros e He; split; [exact (SUBc e He)| rewrite <- LDS1 in He; exact (proj1 (proj2 (live_destroy_In _ _ _ _ _ He)))]) AG)) end.
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; apply SUBc; apply SUB0b; exact He| solve [frames_sub_tac]| lia]|
                                        cbn [outside]; pose proof (NCP1 _ Hx) as NCPx; split; [clear - NCPx; lia| exact I]]).
        assert (FRSd : rt_frames RT Sd = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
        assert (SPLd : rt_sp0 RT Sd - 8388608 <= usp - 112) by (repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul).
        pose proof (pix_obj_keep _ _ _ pixs vs cvs KL POS3) as POS4. clear POS3 KL.
        hide PO1b. hide PO1d. hide POS4. hide PRd. hide LZd. hide LDd.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
        Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_pixDeserialize; 0x95bd0; 0x9f3dc; 0x9d968; 0x9eb78; 0xa2460; 0xa2d20; 0xa0ce4; 0x941e0].
        cwalk [e_pixDeserialize; 0x95bd0; 0x9f3dc; 0x9d968; 0x9eb78; 0xa2460; 0xa2d20; 0xa0ce4; 0x941e0].
        lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
        pose proof FSE as SHB8. split_at SHB8 8%nat SHB8b. split_at SHB8b 1%nat SHB8c. clear SHB8 SHB8c.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        unfold hid in PO1d, POS4, PRd.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
          lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT Sx ?mm |- _ =>
            assert (KL : keeps_live (rt_live RT Sx) mm mc)
              by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
                  exact (live_outside_frame1 RT AF Sx mm fr usp (usp - 112) bb kk xx A ltac:(rewrite FRSd; left; reflexivity) SPLd Hb Hx)) end end.
        pose proof (pix_obj_keep _ _ _ p1 v1 c1 KL PO1d) as PO1e.
        pose proof (pix_obj_keep _ _ _ pixs vs cvs (keeps_live_sub _ _ _ _ KL (fun e He => SUBd e (SUBc e He))) POS4) as POS5.
        assert (PRd3 : rr = 0 \/ (pix_obj (rt_live RT Sd) _ rr vr cr /\ p_data vr <> 0))
          by (destruct PRd as [Z0|(PO & DN)]; [left; exact Z0| right; split; [exact (pix_obj_keep _ _ _ rr vr cr KL PO)| exact DN]]).
        clear PO1d POS4 PRd KL.
        pose proof DESTROY as DY. unfold pixDestroy_cps in DY.
        eapply cps_seq.
        { eapply DY with (lo := lo) (pp := fr + 64) (pix := p1) (v := v1) (cv := c1) (ras := [RA_TOP]); rt_side idtac.
          all: lazymatch goal with
               | |- optrL _ _ _ _ _ _ =>
                   unfold optrL; split;
                   [ right; exists fr, 1%nat; rewrite FRSd; change (fs_size 1) with 128;
                     split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                     split; [lia|]; split; [lia|];
                     replace (shad (fr + 64)) with (fr / 8 + 2147450888) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                     destruct SHB8b as [[_ B] _]; exact B
                   | let Q := fresh "Q" in pose proof FRSH as Q; unfold parked in Q; unfold SEGTOP_A;
                     repeat split; first [clear - FR0; lia | clear - FR64; Z.div_mod_to_equations; lia | clear - Q; lia | clear - FRSEG; lia] ]
               | |- rw_cells _ _ _ [C8 _] => exact P1E
               | |- pix_obj _ _ _ _ _ => exact PO1e
               | |- uctx _ _ _ _ =>
                   unfold uctx; rewrite ?unsigned_lit by ul; unfold hid, parked in S0INV;
                   apply chain_ok_push with (fp1 := bv_unsigned s0);
                     [ lia | clear - SPA; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | unfold RA_TOP; lia | apply bv_unsigned_in_range
                     | rewrite Z_to_bv_bv_unsigned; rewrite <- RATOP; rewrite Z_to_bv_bv_unsigned; exact FRrec2
                     | cbn [chain_ok]; unfold link_invalid; lia ]
               | |- Forall _ DESTROY_FREE_RAS => rewrite ?unsigned_lit by ul; apply tr_destroy; unfold FUZZ_DESTROY_RAS; cbn [In]; tauto
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   unfold lres, TEMPLATE_COST, RASTER_COST, FRAMES_MAX, LIVE_MAX in *;
                   split; [rewrite FRSd, FR0; cbn [length]; lia| split; [lia| split; [lia| exact LVPd]]]
               | |- ?g => idtac "LEFT:" g
               end. }
        clear SHB8b.
        after_call RT AF.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ _) _ => rename Sx into Se end.
        lazymatch goal with H : rt_live RT Se = _ |- _ => rename H into LVe end.
        assert (FRSe : rt_frames RT Se = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
        assert (SPLe : rt_sp0 RT Se - 8388608 <= usp - 112) by (repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul).
        assert (SUBe : forall e, In e (rt_live RT Sb) -> In e (rt_live RT Se))
          by (intros e He; rewrite LVe; rewrite <- LDS1 in He; exact (live_destroy_mono p1 v1 c1 _ _ SUBd e He)).
        lazymatch goal with AG : agree_on (fun a => aclient ?lv _ _ a /\ outside ?W a) ?ma ?mb, A : ART RT Se ?mb |- _ =>
          assert (KL : keeps_live lv ma mb)
            by (apply (keeps_live_of_agree lv _ _ W ma mb AG); intros bb kk xx Hb Hx;
                exact (live_outside_local RT AF Se mb fr 1%nat 64 bb kk xx A ltac:(rewrite FRSe; left; reflexivity) ltac:(lia) ltac:(change (fs_size 1) with 128; lia) Hb Hx)) end.
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; apply SUBe; apply SUB0b; exact He| solve [frames_sub_tac]| lia]|
                                        cbn [outside]; destruct (NFA _ Hx) as [N1 N2]; split; [lia| exact I]]).
        pose proof (pix_obj_keep _ _ _ pixs vs cvs (keeps_live_sub _ _ _ _ KL SUBe) POS5) as POS6.
        assert (LVPe : forall p n, In (p, n) (rt_live RT Se) -> 0 < n)
          by (intros p n H; rewrite LVe in H; exact (LVPd p n (live_destroy_sub _ _ _ _ _ H))).
        assert (LVXe : Z.of_nat (length (rt_live RT Se)) <= Z.of_nat (length (rt_live RT Sd)))
          by (rewrite LVe; pose proof (live_destroy_len p1 v1 c1 (rt_live RT Sd)); lia).
        unfold hid in LZd, LDd, PO1b.
        destruct (Z.eq_dec rr 0) as [RZ|RNZ].
        - (* [comment removed for export] *)
          clear PRd3. assert (LVe0 : rt_live RT Se = rt_live RT Sb) by (rewrite LVe, (LZd RZ); exact LDS1).
          clear LVe KL. rewrite RZ in *.
          hide POS6.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
        Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_pixDeserialize; 0x95bd0; 0x9f3dc; 0x9d968; 0x9eb78; 0xa2460; 0xa2d20; 0xa0ce4; 0x941e0].
        cwalk [e_pixDeserialize; 0x95bd0; 0x9f3dc; 0x9d968; 0x9eb78; 0xa2460; 0xa2d20; 0xa0ce4; 0x941e0].
        lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
        pose proof FSE as SHB12. split_at SHB12 12%nat SHB12b. split_at SHB12b 1%nat SHB12c. clear SHB12 SHB12c.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        unfold hid in POS6.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
          lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT Sx ?mm |- _ =>
            assert (KL : keeps_live (rt_live RT Sx) mm mc)
              by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
                  exact (live_outside_frame1 RT AF Sx mm fr usp (usp - 112) bb kk xx A ltac:(rewrite FRSe; left; reflexivity) SPLe Hb Hx)) end end.
        pose proof (pix_obj_keep _ _ _ pixs vs cvs (keeps_live_sub _ _ _ _ KL SUBe) POS6) as POS7. clear POS6 KL.
        pose proof DNULL as DN. unfold pixDestroy_null_cps in DN.
        eapply cps_seq.
        { eapply DN with (lo := lo) (pp := fr + 96); rt_side idtac.
          all: lazymatch goal with
               | |- optrL _ _ _ _ _ _ =>
                   unfold optrL; split;
                   [ right; exists fr, 1%nat; rewrite FRSe; change (fs_size 1) with 128;
                     split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                     split; [lia|]; split; [lia|];
                     replace (shad (fr + 96)) with (fr / 8 + 2147450892) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                     destruct SHB12b as [[_ B] _]; exact B
                   | let Q := fresh "Q" in pose proof FRSH as Q; unfold parked in Q; unfold SEGTOP_A;
                     repeat split; first [clear - FR0; lia | clear - FR64; Z.div_mod_to_equations; lia | clear - Q; lia | clear - FRSEG; lia] ]
               | |- rw_cells _ _ _ [C8 _] => exact P2E
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   unfold lres, TEMPLATE_COST, RASTER_COST, FRAMES_MAX, LIVE_MAX in *;
                   split; [rewrite FRSe, FR0; cbn [length]; lia| split; [rewrite LVe0; lia| split; [lia| exact LVPe]]]
               | |- ?g => idtac "LEFT:" g
               end. }
        clear SHB12b.
        after_call RT AF.
        lazymatch goal with AG : agree_on (fun a => aclient ?lv _ _ a /\ outside ?W a) ?ma ?mb |- _ =>
          assert (KL : keeps_live lv ma mb) by (apply (keeps_live_of_agree lv _ _ W ma mb AG); intros; exact I) end.
        lazymatch goal with H : rt_live RT ?Sx = rt_live RT Se |- _ => rewrite LVe0 in H; rewrite H in KL end.
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; apply SUB0b; exact He| solve [frames_sub_tac]| lia]| exact I]).
        pose proof (pix_obj_keep _ _ _ pixs vs cvs KL POS7) as POS8. clear POS7 KL.
          to_entry.
          eapply CONT5; try eassumption.
          all: lazymatch goal with
               | |- pix_obj _ _ _ _ _ => exact POS8
               | |- rt_live _ _ = _ => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity
               | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
               | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
               | |- _ <= rt_credit _ _ => unfold TEMPLATE_COST, RASTER_COST in *; lia
               | |- ?g => idtac "LEFT:" g
               end.
        - (* [comment removed for export] *)
          destruct PRd3 as [Z0|(POR & RDATA)]; [exfalso; exact (RNZ Z0)|].
          pose proof (obj_fresh_of_eq (rt_live RT Sd) (rt_live RT Sc) _ rr vr cr _ p1 v1 c1 (LDd RNZ) POR PO1b) as FRESH.
          pose proof (pix_obj_in_destroy (rt_live RT Sd) _ rr vr cr p1 v1 c1 POR FRESH) as PORe0. rewrite <- LVe in PORe0.
          pose proof (pix_obj_keep _ _ _ rr vr cr KL PORe0) as PORe. clear POR PORe0 FRESH KL.
          assert (LVf0 : live_destroy rr vr cr (rt_live RT Se) = rt_live RT Sb)
            by (rewrite LVe, live_destroy_comm, (LDd RNZ); exact LDS1).
          hide POS6. hide PORe. hide LVf0.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
        Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_pixDeserialize; 0x95bd0; 0x9f3dc; 0x9d968; 0x9eb78; 0xa2460; 0xa2d20; 0xa0ce4; 0x941e0].
        cwalk [e_pixDeserialize; 0x95bd0; 0x9f3dc; 0x9d968; 0x9eb78; 0xa2460; 0xa2d20; 0xa0ce4; 0x941e0].
        lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
        pose proof FSE as SHB12. split_at SHB12 12%nat SHB12b. split_at SHB12b 1%nat SHB12c. clear SHB12 SHB12c.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        unfold hid in POS6, PORe.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
          lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT Sx ?mm |- _ =>
            assert (KL : keeps_live (rt_live RT Sx) mm mc)
              by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
                  exact (live_outside_frame1 RT AF Sx mm fr usp (usp - 112) bb kk xx A ltac:(rewrite FRSe; left; reflexivity) SPLe Hb Hx)) end end.
        pose proof (pix_obj_keep _ _ _ pixs vs cvs (keeps_live_sub _ _ _ _ KL SUBe) POS6) as POS7. pose proof (pix_obj_keep _ _ _ rr vr cr KL PORe) as POR2. clear POS6 PORe KL.
        eapply cps_seq.
        { eapply DY with (lo := lo) (pp := fr + 96) (pix := rr) (v := vr) (cv := cr) (ras := [RA_TOP]); rt_side idtac.
          all: lazymatch goal with
               | |- optrL _ _ _ _ _ _ =>
                   unfold optrL; split;
                   [ right; exists fr, 1%nat; rewrite FRSe; change (fs_size 1) with 128;
                     split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                     split; [lia|]; split; [lia|];
                     replace (shad (fr + 96)) with (fr / 8 + 2147450892) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                     destruct SHB12b as [[_ B] _]; exact B
                   | let Q := fresh "Q" in pose proof FRSH as Q; unfold parked in Q; unfold SEGTOP_A;
                     repeat split; first [clear - FR0; lia | clear - FR64; Z.div_mod_to_equations; lia | clear - Q; lia | clear - FRSEG; lia] ]
               | |- rw_cells _ _ _ [C8 _] => exact P2E
               | |- pix_obj _ _ _ _ _ => exact POR2
               | |- uctx _ _ _ _ =>
                   unfold uctx; rewrite ?unsigned_lit by ul; unfold hid, parked in S0INV;
                   apply chain_ok_push with (fp1 := bv_unsigned s0);
                     [ lia | clear - SPA; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | unfold RA_TOP; lia | apply bv_unsigned_in_range
                     | rewrite Z_to_bv_bv_unsigned; rewrite <- RATOP; rewrite Z_to_bv_bv_unsigned; exact FRrec2
                     | cbn [chain_ok]; unfold link_invalid; lia ]
               | |- Forall _ DESTROY_FREE_RAS => rewrite ?unsigned_lit by ul; apply tr_destroy; unfold FUZZ_DESTROY_RAS; cbn [In]; tauto
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   unfold lres, TEMPLATE_COST, RASTER_COST, FRAMES_MAX, LIVE_MAX in *;
                   split; [rewrite FRSe, FR0; cbn [length]; lia| split; [lia| split; [lia| exact LVPe]]]
               | |- ?g => idtac "LEFT:" g
               end. }
        clear POR2 SHB12b.
        after_call RT AF.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ _) _ => rename Sx into Sf end.
        lazymatch goal with H : rt_live RT Sf = _ |- _ => rename H into LVf end.
        unfold hid in LVf0. rewrite LVf0 in LVf.
        assert (FRSf : rt_frames RT Sf = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
        lazymatch goal with AG : agree_on (fun a => aclient ?lv _ _ a /\ outside ?W a) ?ma ?mb, A : ART RT Sf ?mb |- _ =>
          assert (KL : keeps_live lv ma mb)
            by (apply (keeps_live_of_agree lv _ _ W ma mb AG); intros bb kk xx Hb Hx;
                exact (live_outside_local RT AF Sf mb fr 1%nat 96 bb kk xx A ltac:(rewrite FRSf; left; reflexivity) ltac:(lia) ltac:(change (fs_size 1) with 128; lia) Hb Hx)) end.
        rewrite LVf in KL.
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; rewrite LVf; apply SUB0b; exact He| solve [frames_sub_tac]| lia]|
                                        cbn [outside]; destruct (NFA _ Hx) as [N1 N2]; split; [lia| exact I]]).
        pose proof (pix_obj_keep _ _ _ pixs vs cvs KL POS7) as POS8. clear POS7 KL.
          to_entry.
          eapply CONT5; try eassumption.
          all: lazymatch goal with
               | |- pix_obj _ _ _ _ _ => exact POS8
               | |- rt_live _ _ = _ => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity
               | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
               | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
               | |- _ <= rt_credit _ _ => unfold TEMPLATE_COST, RASTER_COST in *; lia
               | |- ?g => idtac "LEFT:" g
               end.
      }
      lazymatch goal with FRx : rw_cells asegs _ (usp + -112) ?cs |- _ =>
        assert (CONT3 : forall (S : rts RT) (mE : mem) (x1 x2 : word)
                  (r1 r5 r6 r7 r9 r10 r11 r12 r13 r14 r15 r16 r17 r28 r29 r30 r31 : word) F' fc',
            ART RT S mE -> mem_inv asegs mE -> stk asegs mE lo (usp + -112) -> rw_cells asegs mE (usp + -112) cs ->
            rw_cells asegs mE fr [C8 (Z_to_bv 64 1102416563)] ->
            rw_cells asegs mE (fr + 32) [C8 (Z_to_bv 64 pixs)] -> rw_cells asegs mE (fr + 64) [C8 x1] -> rw_cells asegs mE (fr + 96) [C8 x2] ->
            rw_cells asegs mE (fr / 8 + 2147450880) [C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13))] ->
            LIBH mE -> io_ssp mE -> agree_on PF m mE -> pix_obj (rt_live RT Sb) mE pixs vs cvs ->
            rt_live RT S = rt_live RT Sb -> rt_frames RT S = (fr, 1%nat) :: rt_frames RT Σ -> rt_sp0 RT S = rt_sp0 RT Σ ->
            rt_credit RT Σ - (RASTER_COST + 65 + 3 * (TEMPLATE_COST + 2) + (k1 + k2 + k3)) <= rt_credit RT S ->
            cps asegs (ASTA RT S PMc (eq (entry_st r1 (Z_to_bv 64 (usp + -112)) gp (Z_to_bv 64 TP_A) r5 r6 r7 (Z_to_bv 64 usp) r9
                                          r10 r11 r12 r13 r14 r15 r16 r17 (Z_to_bv 64 fr) (Z_to_bv 64 (fr + 32)) (Z_to_bv 64 (fr + 96)) (Z_to_bv 64 (fr + 64)) (Z_to_bv 64 pixs) (Z_to_bv 64 (fr / 8 + 2147450880))
                                          (Z_to_bv 64 fr) s9 s10 s11 r28 r29 r30 r31 F' fc' 0x90b50 mE))) QF) end.
      { intros S mE wx1 wx2 r1 r5 r6 r7 r9 r10 r11 r12 r13 r14 r15 r16 r17 r28 r29 r30 r31 F' fc'
          ARTE MIE STE FRE FHE PSE P1E P2E FSE LHE SSPE AGE POSE ELV EFR ESP0 ECR.
        clear AGF. rename AGE into AGF.
        repeat match goal with H : rw_cells asegs _ _ _ |- _ => lazymatch H with FRE => fail | FHE => fail | PSE => fail | P1E => fail | P2E => fail | FSE => fail | _ => clear H end end.
        repeat match goal with H : ro_cells asegs _ _ _ |- _ => clear H end.
        repeat match goal with H : ART RT _ _ |- _ => lazymatch H with ARTE => fail | _ => clear H end end.
        repeat match goal with H : LIBH _ |- _ => lazymatch H with LHE => fail | _ => clear H end end.
        repeat match goal with H : io_ssp _ |- _ => lazymatch H with SSPE => fail | _ => clear H end end.
        repeat match goal with H : stk asegs _ _ _ |- _ => lazymatch H with STE => fail | _ => clear H end end.
        repeat match goal with H : mem_inv asegs _ |- _ => lazymatch H with MIE => fail | _ => clear H end end.
        repeat match goal with H : wmono asegs _ _ |- _ => clear H end.
        repeat match goal with H : munch _ _ _ |- _ => clear H end.
        repeat match goal with H : rt_frames RT _ = _ |- _ => lazymatch H with EFR => fail | FR0 => fail | _ => clear H end end.
        repeat match goal with H : rt_live RT _ = _ |- _ => lazymatch H with ELV => fail | _ => clear H end end.
        repeat match goal with H : rt_sp0 RT _ = _ |- _ => lazymatch H with ESP0 => fail | _ => clear H end end.
        repeat match goal with H : rt_credit RT _ = _ |- _ => clear H end.
        repeat match goal with H : rt_credit RT _ - _ <= _ |- _ => lazymatch H with ECR => fail | _ => clear H end end.
        clear_acc.
        pose proof FRE as FRrec. split_before FRrec (C8 s0) FRrec2. clear FRrec.
        assert (SPLE : rt_sp0 RT S - 8388608 <= usp - 112) by (rewrite ESP0; ul).
        hide POSE.
        unfold entry_st.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
        Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_pixDeserialize; 0x95bd0; 0x9f3dc; 0x9d968; 0x9eb78; 0xa2460; 0xa2d20; 0xa0ce4; 0x941e0].
        cwalk [e_pixDeserialize; 0x95bd0; 0x9f3dc; 0x9d968; 0x9eb78; 0xa2460; 0xa2d20; 0xa0ce4; 0x941e0].
        lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        unfold hid in POSE.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
          lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT Sx ?mm |- _ =>
            assert (KL : keeps_live (rt_live RT Sx) mm mc)
              by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
                  exact (live_outside_frame1 RT AF Sx mm fr usp (usp - 112) bb kk xx A ltac:(rewrite EFR; left; reflexivity) SPLE Hb Hx)) end end.
        rewrite ELV in KL. pose proof (pix_obj_keep _ _ _ pixs vs cvs KL POSE) as POS1. clear POSE KL.
        pose proof PCOPY as PC. unfold pixCopy_cps in PC.
        eapply cps_seq.
        { eapply PC with (lo := lo) (pixs := pixs) (vs := vs) (cvs := cvs); rt_side idtac.
          all: lazymatch goal with
               | |- pix_obj _ _ _ _ _ => rewrite ELV; exact POS1
               | |- p_data _ <> 0 => exact VDATA
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   unfold lres, TEMPLATE_COST, RASTER_COST, FRAMES_MAX, LIVE_MAX in *;
                   split; [rewrite EFR, FR0; cbn [length]; lia| split; [rewrite ELV; lia| split; [lia| rewrite ELV; exact LVPb]]]
               | |- ?g => idtac "LEFT:" g
               end. }
        after_call RT AF.
        lazymatch goal with AG : agree_on (fun a => aclient ?lv _ _ a /\ outside ?W a) ?ma ?mb |- _ =>
          assert (KL : keeps_live lv ma mb) by (apply (keeps_live_of_agree lv _ _ W ma mb AG); intros; exact I) end.
        rewrite ELV in KL.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ _) _ => rename Sx into Sc end.
        lazymatch goal with H : pix_obj (rt_live RT Sc) _ ?p ?vv ?cc |- _ => rename H into PO1; set (p1 := p) in *; set (v1 := vv) in *; set (c1 := cc) in * end.
        lazymatch goal with H : live_destroy p1 v1 c1 _ = _ |- _ => rename H into LDS1 end. rewrite ELV in LDS1.
        lazymatch goal with H : forall p n, In (p, n) (rt_live RT Sc) -> 0 < n |- _ => rename H into LVPc end.
        lazymatch goal with H : Z.of_nat (length (rt_live RT Sc)) <= _ |- _ => rename H into LVXc end. rewrite ELV in LVXc.
        lazymatch goal with H : p_data v1 <> 0 |- _ => rename H into V1DATA end.
        lazymatch goal with H : p_d v1 = p_d vs |- _ => rename H into VD1 end.
        assert (NZV1 : cmap_nz v1 c1).
        { lazymatch goal with LNC : p_cmap vs = 0 -> _, LCN : p_cmap vs <> 0 -> _ |- _ =>
            unfold cmap_nz in *; destruct (Z.eq_dec (p_cmap vs) 0) as [Z0|NZ];
            [ left; exact (proj1 (LNC Z0)) | right; rewrite (LCN NZ); destruct NZV as [Z1|N1]; [exfalso; exact (NZ Z1)| exact N1] ] end. }
        lazymatch goal with H : p_cmap vs <> 0 -> _ |- _ => clear H end.
        lazymatch goal with H : p_cmap vs = 0 -> _ |- _ => clear H end.
        assert (SUBc : forall e, In e (rt_live RT Sb) -> In e (rt_live RT Sc)) by (intros e He; rewrite <- LDS1 in He; exact (proj1 (live_destroy_In _ _ _ _ _ He))).
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; rewrite ELV; apply SUB0b; exact He| solve [frames_sub_tac]| lia]| exact I]).
        assert (FRSc : rt_frames RT Sc = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
        assert (SPLc : rt_sp0 RT Sc - 8388608 <= usp - 112) by (repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul).
        lazymatch goal with A : ART RT Sc ?mm |- _ =>
          assert (NCP1 : forall a, PF a -> a < p1 \/ p1 + 64 <= a)
            by (intros a [Ha _]; apply (inner_chunk_apart RT AF Sc mm p1 64 (rt_live RT Σ) (rt_frames RT Σ) usp a A (proj1 (pix_obj_entries _ _ _ _ _ PO1)));
                [ intros e He; pose proof (SUB0b e He) as Hb; rewrite <- LDS1 in Hb; destruct (live_destroy_In _ _ _ _ _ Hb) as (Q1 & Q2 & _); split; [exact Q1| exact Q2]
                | solve [frames_sub_tac] | repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul | exact Ha ]) end.
        (* [comment removed for export] *)
        pose proof (proj1 (pix_obj_entries _ _ _ _ _ PO1)) as P1IN.
        chunk_facts RT AF GP p1 64. fframe_chunk RT AF fr 1%nat 128 p1 64.
        pose proof (pix_obj_keep _ _ _ pixs vs cvs KL POS1) as POS2. clear POS1 KL.
        hide PO1. hide POS2.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
        Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_pixDeserialize; 0x95bd0; 0x9f3dc; 0x9d968; 0x9eb78; 0xa2460; 0xa2d20; 0xa0ce4; 0x941e0].
        cwalk [e_pixDeserialize; 0x95bd0; 0x9f3dc; 0x9d968; 0x9eb78; 0xa2460; 0xa2d20; 0xa0ce4; 0x941e0].
        lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        unfold hid in PO1, POS2.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
          lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT Sx ?mm |- _ =>
            assert (KL : keeps_live (rt_live RT Sx) mm mc)
              by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
                  exact (live_outside_frame1 RT AF Sx mm fr usp (usp - 112) bb kk xx A ltac:(rewrite FRSc; left; reflexivity) SPLc Hb Hx)) end end.
        pose proof (pix_obj_keep _ _ _ p1 v1 c1 KL PO1) as PO1b. pose proof (pix_obj_keep _ _ _ pixs vs cvs (keeps_live_sub _ _ _ _ KL SUBc) POS2) as POS3. clear PO1 POS2 KL.
        (* [comment removed for export] *)
        pose proof OP4 as GK. unfold pixGenerateMaskByBand32_cps, gq_op_cps in GK.
        eapply cps_seq.
        { eapply GK with (lo := lo) (pix := p1) (v := v1) (cv := c1) (ras := [RA_TOP]); rt_side idtac.
          all: lazymatch goal with
               | |- pix_obj _ _ _ _ _ => exact PO1b
               | |- p_data _ <> 0 => exact V1DATA
               | |- cmap_nz _ _ => exact NZV1
               | |- uctx _ _ _ _ =>
                   unfold uctx; rewrite ?unsigned_lit by ul; unfold hid, parked in S0INV;
                   apply chain_ok_push with (fp1 := bv_unsigned s0);
                     [ lia | clear - SPA; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | unfold RA_TOP; lia | apply bv_unsigned_in_range
                     | rewrite Z_to_bv_bv_unsigned; rewrite <- RATOP; rewrite Z_to_bv_bv_unsigned; exact FRrec2
                     | cbn [chain_ok]; unfold link_invalid; lia ]
               | |- bv_unsigned _ = _ => rewrite ?unsigned_lit by ul; reflexivity
               | |- _ = [RA_TOP] => reflexivity
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   rewrite VD1; fold k4; unfold lres, TEMPLATE_COST, RASTER_COST, FRAMES_MAX, LIVE_MAX in *;
                   split; [rewrite FRSc, FR0; cbn [length]; lia| split; [lia| split; [lia| exact LVPc]]]
               | |- wZ _ _ => reflexivity
               | |- True => exact I
               | |- _ /\ _ =>      (* [comment removed for export] *)
                   repeat split;
                   first [ reflexivity
                         | unfold freg_is, fa0, fa1;
                           first [ etransitivity; [apply freg_get_same; reflexivity| vm_compute; reflexivity]
                                 | rewrite freg_get_other by reflexivity; etransitivity; [apply freg_get_same; reflexivity| vm_compute; reflexivity] ] ]
               | |- ?g => idtac "LEFT:" g
               end. }
        after_call RT AF.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ _) _ => rename Sx into Sd end.
        lazymatch goal with H : pix_obj (rt_live RT Sd) _ p1 v1 c1 |- _ => rename H into PO1d end.
        lazymatch goal with H : ?r = 0 \/ (pix_obj (rt_live RT Sd) _ ?r ?vv ?cc /\ _) |- _ => rename H into PRd; set (rr := r) in *; set (vr := vv) in *; set (cr := cc) in * end.
        lazymatch goal with H : rr = 0 -> rt_live RT Sd = _ |- _ => rename H into LZd end.
        lazymatch goal with H : rr <> 0 -> live_destroy rr vr cr _ = _ |- _ => rename H into LDd end.
        lazymatch goal with H : forall p n, In (p, n) (rt_live RT Sd) -> 0 < n |- _ => rename H into LVPd end.
        lazymatch goal with H : Z.of_nat (length (rt_live RT Sd)) <= _ |- _ => rename H into LVXd end.
        lazymatch goal with H : rt_credit RT Sc - _ <= rt_credit RT Sd |- _ => rewrite VD1 in H; fold k4 in H end.
        assert (SUBd : forall e, In e (rt_live RT Sc) -> In e (rt_live RT Sd)).
        { intros e He. destruct (Z.eq_dec rr 0) as [Z0|NZ]; [rewrite (LZd Z0); exact He|]. rewrite <- (LDd NZ) in He. exact (live_destroy_sub _ _ _ _ _ He). }
        (* [comment removed for export] *)
        lazymatch goal with AG : agree_on (fun a => aclient (rt_live RT Sc) _ _ a /\ outside _ a) ?ma ?mb, A : ART RT Sc ?mx |- _ =>
          assert (KL : keeps_live (rt_live RT Sb) ma mb)
            by (apply (keeps_live_others RT AF Sc mx _ _ (rt_live RT Sb) p1 64 (p1 + 20) (p1 + 24) ma mb A
                         (proj1 (pix_obj_entries _ _ _ _ _ PO1b)) ltac:(lia) ltac:(lia)
                         ltac:(intros e He; split; [exact (SUBc e He)| rewrite <- LDS1 in He; exact (proj1 (proj2 (live_destroy_In _ _ _ _ _ He)))]) AG)) end.
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; apply SUBc; apply SUB0b; exact He| solve [frames_sub_tac]| lia]|
                                        cbn [outside]; pose proof (NCP1 _ Hx) as NCPx; split; [clear - NCPx; lia| exact I]]).
        assert (FRSd : rt_frames RT Sd = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
        assert (SPLd : rt_sp0 RT Sd - 8388608 <= usp - 112) by (repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul).
        pose proof (pix_obj_keep _ _ _ pixs vs cvs KL POS3) as POS4. clear POS3 KL.
        hide PO1b. hide PO1d. hide POS4. hide PRd. hide LZd. hide LDd.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
        Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_pixDeserialize; 0x95bd0; 0x9f3dc; 0x9d968; 0x9eb78; 0xa2460; 0xa2d20; 0xa0ce4; 0x941e0].
        cwalk [e_pixDeserialize; 0x95bd0; 0x9f3dc; 0x9d968; 0x9eb78; 0xa2460; 0xa2d20; 0xa0ce4; 0x941e0].
        lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
        pose proof FSE as SHB8. split_at SHB8 8%nat SHB8b. split_at SHB8b 1%nat SHB8c. clear SHB8 SHB8c.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        unfold hid in PO1d, POS4, PRd.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
          lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT Sx ?mm |- _ =>
            assert (KL : keeps_live (rt_live RT Sx) mm mc)
              by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
                  exact (live_outside_frame1 RT AF Sx mm fr usp (usp - 112) bb kk xx A ltac:(rewrite FRSd; left; reflexivity) SPLd Hb Hx)) end end.
        pose proof (pix_obj_keep _ _ _ p1 v1 c1 KL PO1d) as PO1e.
        pose proof (pix_obj_keep _ _ _ pixs vs cvs (keeps_live_sub _ _ _ _ KL (fun e He => SUBd e (SUBc e He))) POS4) as POS5.
        assert (PRd3 : rr = 0 \/ (pix_obj (rt_live RT Sd) _ rr vr cr /\ p_data vr <> 0))
          by (destruct PRd as [Z0|(PO & DN)]; [left; exact Z0| right; split; [exact (pix_obj_keep _ _ _ rr vr cr KL PO)| exact DN]]).
        clear PO1d POS4 PRd KL.
        pose proof DESTROY as DY. unfold pixDestroy_cps in DY.
        eapply cps_seq.
        { eapply DY with (lo := lo) (pp := fr + 64) (pix := p1) (v := v1) (cv := c1) (ras := [RA_TOP]); rt_side idtac.
          all: lazymatch goal with
               | |- optrL _ _ _ _ _ _ =>
                   unfold optrL; split;
                   [ right; exists fr, 1%nat; rewrite FRSd; change (fs_size 1) with 128;
                     split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                     split; [lia|]; split; [lia|];
                     replace (shad (fr + 64)) with (fr / 8 + 2147450888) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                     destruct SHB8b as [[_ B] _]; exact B
                   | let Q := fresh "Q" in pose proof FRSH as Q; unfold parked in Q; unfold SEGTOP_A;
                     repeat split; first [clear - FR0; lia | clear - FR64; Z.div_mod_to_equations; lia | clear - Q; lia | clear - FRSEG; lia] ]
               | |- rw_cells _ _ _ [C8 _] => exact P1E
               | |- pix_obj _ _ _ _ _ => exact PO1e
               | |- uctx _ _ _ _ =>
                   unfold uctx; rewrite ?unsigned_lit by ul; unfold hid, parked in S0INV;
                   apply chain_ok_push with (fp1 := bv_unsigned s0);
                     [ lia | clear - SPA; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | unfold RA_TOP; lia | apply bv_unsigned_in_range
                     | rewrite Z_to_bv_bv_unsigned; rewrite <- RATOP; rewrite Z_to_bv_bv_unsigned; exact FRrec2
                     | cbn [chain_ok]; unfold link_invalid; lia ]
               | |- Forall _ DESTROY_FREE_RAS => rewrite ?unsigned_lit by ul; apply tr_destroy; unfold FUZZ_DESTROY_RAS; cbn [In]; tauto
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   unfold lres, TEMPLATE_COST, RASTER_COST, FRAMES_MAX, LIVE_MAX in *;
                   split; [rewrite FRSd, FR0; cbn [length]; lia| split; [lia| split; [lia| exact LVPd]]]
               | |- ?g => idtac "LEFT:" g
               end. }
        clear SHB8b.
        after_call RT AF.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ _) _ => rename Sx into Se end.
        lazymatch goal with H : rt_live RT Se = _ |- _ => rename H into LVe end.
        assert (FRSe : rt_frames RT Se = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
        assert (SPLe : rt_sp0 RT Se - 8388608 <= usp - 112) by (repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul).
        assert (SUBe : forall e, In e (rt_live RT Sb) -> In e (rt_live RT Se))
          by (intros e He; rewrite LVe; rewrite <- LDS1 in He; exact (live_destroy_mono p1 v1 c1 _ _ SUBd e He)).
        lazymatch goal with AG : agree_on (fun a => aclient ?lv _ _ a /\ outside ?W a) ?ma ?mb, A : ART RT Se ?mb |- _ =>
          assert (KL : keeps_live lv ma mb)
            by (apply (keeps_live_of_agree lv _ _ W ma mb AG); intros bb kk xx Hb Hx;
                exact (live_outside_local RT AF Se mb fr 1%nat 64 bb kk xx A ltac:(rewrite FRSe; left; reflexivity) ltac:(lia) ltac:(change (fs_size 1) with 128; lia) Hb Hx)) end.
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; apply SUBe; apply SUB0b; exact He| solve [frames_sub_tac]| lia]|
                                        cbn [outside]; destruct (NFA _ Hx) as [N1 N2]; split; [lia| exact I]]).
        pose proof (pix_obj_keep _ _ _ pixs vs cvs (keeps_live_sub _ _ _ _ KL SUBe) POS5) as POS6.
        assert (LVPe : forall p n, In (p, n) (rt_live RT Se) -> 0 < n)
          by (intros p n H; rewrite LVe in H; exact (LVPd p n (live_destroy_sub _ _ _ _ _ H))).
        assert (LVXe : Z.of_nat (length (rt_live RT Se)) <= Z.of_nat (length (rt_live RT Sd)))
          by (rewrite LVe; pose proof (live_destroy_len p1 v1 c1 (rt_live RT Sd)); lia).
        unfold hid in LZd, LDd, PO1b.
        destruct (Z.eq_dec rr 0) as [RZ|RNZ].
        - (* [comment removed for export] *)
          clear PRd3. assert (LVe0 : rt_live RT Se = rt_live RT Sb) by (rewrite LVe, (LZd RZ); exact LDS1).
          clear LVe KL. rewrite RZ in *.
          hide POS6.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
        Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_pixDeserialize; 0x95bd0; 0x9f3dc; 0x9d968; 0x9eb78; 0xa2460; 0xa2d20; 0xa0ce4; 0x941e0].
        cwalk [e_pixDeserialize; 0x95bd0; 0x9f3dc; 0x9d968; 0x9eb78; 0xa2460; 0xa2d20; 0xa0ce4; 0x941e0].
        lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
        pose proof FSE as SHB12. split_at SHB12 12%nat SHB12b. split_at SHB12b 1%nat SHB12c. clear SHB12 SHB12c.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        unfold hid in POS6.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
          lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT Sx ?mm |- _ =>
            assert (KL : keeps_live (rt_live RT Sx) mm mc)
              by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
                  exact (live_outside_frame1 RT AF Sx mm fr usp (usp - 112) bb kk xx A ltac:(rewrite FRSe; left; reflexivity) SPLe Hb Hx)) end end.
        pose proof (pix_obj_keep _ _ _ pixs vs cvs (keeps_live_sub _ _ _ _ KL SUBe) POS6) as POS7. clear POS6 KL.
        pose proof DNULL as DN. unfold pixDestroy_null_cps in DN.
        eapply cps_seq.
        { eapply DN with (lo := lo) (pp := fr + 96); rt_side idtac.
          all: lazymatch goal with
               | |- optrL _ _ _ _ _ _ =>
                   unfold optrL; split;
                   [ right; exists fr, 1%nat; rewrite FRSe; change (fs_size 1) with 128;
                     split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                     split; [lia|]; split; [lia|];
                     replace (shad (fr + 96)) with (fr / 8 + 2147450892) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                     destruct SHB12b as [[_ B] _]; exact B
                   | let Q := fresh "Q" in pose proof FRSH as Q; unfold parked in Q; unfold SEGTOP_A;
                     repeat split; first [clear - FR0; lia | clear - FR64; Z.div_mod_to_equations; lia | clear - Q; lia | clear - FRSEG; lia] ]
               | |- rw_cells _ _ _ [C8 _] => exact P2E
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   unfold lres, TEMPLATE_COST, RASTER_COST, FRAMES_MAX, LIVE_MAX in *;
                   split; [rewrite FRSe, FR0; cbn [length]; lia| split; [rewrite LVe0; lia| split; [lia| exact LVPe]]]
               | |- ?g => idtac "LEFT:" g
               end. }
        clear SHB12b.
        after_call RT AF.
        lazymatch goal with AG : agree_on (fun a => aclient ?lv _ _ a /\ outside ?W a) ?ma ?mb |- _ =>
          assert (KL : keeps_live lv ma mb) by (apply (keeps_live_of_agree lv _ _ W ma mb AG); intros; exact I) end.
        lazymatch goal with H : rt_live RT ?Sx = rt_live RT Se |- _ => rewrite LVe0 in H; rewrite H in KL end.
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; apply SUB0b; exact He| solve [frames_sub_tac]| lia]| exact I]).
        pose proof (pix_obj_keep _ _ _ pixs vs cvs KL POS7) as POS8. clear POS7 KL.
          to_entry.
          eapply CONT4; try eassumption.
          all: lazymatch goal with
               | |- pix_obj _ _ _ _ _ => exact POS8
               | |- rt_live _ _ = _ => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity
               | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
               | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
               | |- _ <= rt_credit _ _ => unfold TEMPLATE_COST, RASTER_COST in *; lia
               | |- ?g => idtac "LEFT:" g
               end.
        - (* [comment removed for export] *)
          destruct PRd3 as [Z0|(POR & RDATA)]; [exfalso; exact (RNZ Z0)|].
          pose proof (obj_fresh_of_eq (rt_live RT Sd) (rt_live RT Sc) _ rr vr cr _ p1 v1 c1 (LDd RNZ) POR PO1b) as FRESH.
          pose proof (pix_obj_in_destroy (rt_live RT Sd) _ rr vr cr p1 v1 c1 POR FRESH) as PORe0. rewrite <- LVe in PORe0.
          pose proof (pix_obj_keep _ _ _ rr vr cr KL PORe0) as PORe. clear POR PORe0 FRESH KL.
          assert (LVf0 : live_destroy rr vr cr (rt_live RT Se) = rt_live RT Sb)
            by (rewrite LVe, live_destroy_comm, (LDd RNZ); exact LDS1).
          hide POS6. hide PORe. hide LVf0.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
        Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_pixDeserialize; 0x95bd0; 0x9f3dc; 0x9d968; 0x9eb78; 0xa2460; 0xa2d20; 0xa0ce4; 0x941e0].
        cwalk [e_pixDeserialize; 0x95bd0; 0x9f3dc; 0x9d968; 0x9eb78; 0xa2460; 0xa2d20; 0xa0ce4; 0x941e0].
        lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
        pose proof FSE as SHB12. split_at SHB12 12%nat SHB12b. split_at SHB12b 1%nat SHB12c. clear SHB12 SHB12c.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        unfold hid in POS6, PORe.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
          lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT Sx ?mm |- _ =>
            assert (KL : keeps_live (rt_live RT Sx) mm mc)
              by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
                  exact (live_outside_frame1 RT AF Sx mm fr usp (usp - 112) bb kk xx A ltac:(rewrite FRSe; left; reflexivity) SPLe Hb Hx)) end end.
        pose proof (pix_obj_keep _ _ _ pixs vs cvs (keeps_live_sub _ _ _ _ KL SUBe) POS6) as POS7. pose proof (pix_obj_keep _ _ _ rr vr cr KL PORe) as POR2. clear POS6 PORe KL.
        eapply cps_seq.
        { eapply DY with (lo := lo) (pp := fr + 96) (pix := rr) (v := vr) (cv := cr) (ras := [RA_TOP]); rt_side idtac.
          all: lazymatch goal with
               | |- optrL _ _ _ _ _ _ =>
                   unfold optrL; split;
                   [ right; exists fr, 1%nat; rewrite FRSe; change (fs_size 1) with 128;
                     split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                     split; [lia|]; split; [lia|];
                     replace (shad (fr + 96)) with (fr / 8 + 2147450892) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                     destruct SHB12b as [[_ B] _]; exact B
                   | let Q := fresh "Q" in pose proof FRSH as Q; unfold parked in Q; unfold SEGTOP_A;
                     repeat split; first [clear - FR0; lia | clear - FR64; Z.div_mod_to_equations; lia | clear - Q; lia | clear - FRSEG; lia] ]
               | |- rw_cells _ _ _ [C8 _] => exact P2E
               | |- pix_obj _ _ _ _ _ => exact POR2
               | |- uctx _ _ _ _ =>
                   unfold uctx; rewrite ?unsigned_lit by ul; unfold hid, parked in S0INV;
                   apply chain_ok_push with (fp1 := bv_unsigned s0);
                     [ lia | clear - SPA; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | unfold RA_TOP; lia | apply bv_unsigned_in_range
                     | rewrite Z_to_bv_bv_unsigned; rewrite <- RATOP; rewrite Z_to_bv_bv_unsigned; exact FRrec2
                     | cbn [chain_ok]; unfold link_invalid; lia ]
               | |- Forall _ DESTROY_FREE_RAS => rewrite ?unsigned_lit by ul; apply tr_destroy; unfold FUZZ_DESTROY_RAS; cbn [In]; tauto
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   unfold lres, TEMPLATE_COST, RASTER_COST, FRAMES_MAX, LIVE_MAX in *;
                   split; [rewrite FRSe, FR0; cbn [length]; lia| split; [lia| split; [lia| exact LVPe]]]
               | |- ?g => idtac "LEFT:" g
               end. }
        clear POR2 SHB12b.
        after_call RT AF.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ _) _ => rename Sx into Sf end.
        lazymatch goal with H : rt_live RT Sf = _ |- _ => rename H into LVf end.
        unfold hid in LVf0. rewrite LVf0 in LVf.
        assert (FRSf : rt_frames RT Sf = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
        lazymatch goal with AG : agree_on (fun a => aclient ?lv _ _ a /\ outside ?W a) ?ma ?mb, A : ART RT Sf ?mb |- _ =>
          assert (KL : keeps_live lv ma mb)
            by (apply (keeps_live_of_agree lv _ _ W ma mb AG); intros bb kk xx Hb Hx;
                exact (live_outside_local RT AF Sf mb fr 1%nat 96 bb kk xx A ltac:(rewrite FRSf; left; reflexivity) ltac:(lia) ltac:(change (fs_size 1) with 128; lia) Hb Hx)) end.
        rewrite LVf in KL.
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; rewrite LVf; apply SUB0b; exact He| solve [frames_sub_tac]| lia]|
                                        cbn [outside]; destruct (NFA _ Hx) as [N1 N2]; split; [lia| exact I]]).
        pose proof (pix_obj_keep _ _ _ pixs vs cvs KL POS7) as POS8. clear POS7 KL.
          to_entry.
          eapply CONT4; try eassumption.
          all: lazymatch goal with
               | |- pix_obj _ _ _ _ _ => exact POS8
               | |- rt_live _ _ = _ => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity
               | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
               | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
               | |- _ <= rt_credit _ _ => unfold TEMPLATE_COST, RASTER_COST in *; lia
               | |- ?g => idtac "LEFT:" g
               end.
      }
      lazymatch goal with FRx : rw_cells asegs _ (usp + -112) ?cs |- _ =>
        assert (CONT2 : forall (S : rts RT) (mE : mem) (x1 x2 : word)
                  (r1 r5 r6 r7 r9 r10 r11 r12 r13 r14 r15 r16 r17 r28 r29 r30 r31 : word) F' fc',
            ART RT S mE -> mem_inv asegs mE -> stk asegs mE lo (usp + -112) -> rw_cells asegs mE (usp + -112) cs ->
            rw_cells asegs mE fr [C8 (Z_to_bv 64 1102416563)] ->
            rw_cells asegs mE (fr + 32) [C8 (Z_to_bv 64 pixs)] -> rw_cells asegs mE (fr + 64) [C8 x1] -> rw_cells asegs mE (fr + 96) [C8 x2] ->
            rw_cells asegs mE (fr / 8 + 2147450880) [C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13))] ->
            LIBH mE -> io_ssp mE -> agree_on PF m mE -> pix_obj (rt_live RT Sb) mE pixs vs cvs ->
            rt_live RT S = rt_live RT Sb -> rt_frames RT S = (fr, 1%nat) :: rt_frames RT Σ -> rt_sp0 RT S = rt_sp0 RT Σ ->
            rt_credit RT Σ - (RASTER_COST + 65 + 2 * (TEMPLATE_COST + 2) + (k1 + k2)) <= rt_credit RT S ->
            cps asegs (ASTA RT S PMc (eq (entry_st r1 (Z_to_bv 64 (usp + -112)) gp (Z_to_bv 64 TP_A) r5 r6 r7 (Z_to_bv 64 usp) r9
                                          r10 r11 r12 r13 r14 r15 r16 r17 (Z_to_bv 64 fr) (Z_to_bv 64 (fr + 32)) (Z_to_bv 64 (fr + 96)) (Z_to_bv 64 (fr + 64)) (Z_to_bv 64 pixs) (Z_to_bv 64 (fr / 8 + 2147450880))
                                          (Z_to_bv 64 fr) s9 s10 s11 r28 r29 r30 r31 F' fc' 0x90b18 mE))) QF) end.
      { intros S mE wx1 wx2 r1 r5 r6 r7 r9 r10 r11 r12 r13 r14 r15 r16 r17 r28 r29 r30 r31 F' fc'
          ARTE MIE STE FRE FHE PSE P1E P2E FSE LHE SSPE AGE POSE ELV EFR ESP0 ECR.
        clear AGF. rename AGE into AGF.
        repeat match goal with H : rw_cells asegs _ _ _ |- _ => lazymatch H with FRE => fail | FHE => fail | PSE => fail | P1E => fail | P2E => fail | FSE => fail | _ => clear H end end.
        repeat match goal with H : ro_cells asegs _ _ _ |- _ => clear H end.
        repeat match goal with H : ART RT _ _ |- _ => lazymatch H with ARTE => fail | _ => clear H end end.
        repeat match goal with H : LIBH _ |- _ => lazymatch H with LHE => fail | _ => clear H end end.
        repeat match goal with H : io_ssp _ |- _ => lazymatch H with SSPE => fail | _ => clear H end end.
        repeat match goal with H : stk asegs _ _ _ |- _ => lazymatch H with STE => fail | _ => clear H end end.
        repeat match goal with H : mem_inv asegs _ |- _ => lazymatch H with MIE => fail | _ => clear H end end.
        repeat match goal with H : wmono asegs _ _ |- _ => clear H end.
        repeat match goal with H : munch _ _ _ |- _ => clear H end.
        repeat match goal with H : rt_frames RT _ = _ |- _ => lazymatch H with EFR => fail | FR0 => fail | _ => clear H end end.
        repeat match goal with H : rt_live RT _ = _ |- _ => lazymatch H with ELV => fail | _ => clear H end end.
        repeat match goal with H : rt_sp0 RT _ = _ |- _ => lazymatch H with ESP0 => fail | _ => clear H end end.
        repeat match goal with H : rt_credit RT _ = _ |- _ => clear H end.
        repeat match goal with H : rt_credit RT _ - _ <= _ |- _ => lazymatch H with ECR => fail | _ => clear H end end.
        clear_acc.
        pose proof FRE as FRrec. split_before FRrec (C8 s0) FRrec2. clear FRrec.
        assert (SPLE : rt_sp0 RT S - 8388608 <= usp - 112) by (rewrite ESP0; ul).
        hide POSE.
        unfold entry_st.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
        Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_pixDeserialize; 0x95bd0; 0x9f3dc; 0x9d968; 0x9eb78; 0xa2460; 0xa2d20; 0xa0ce4; 0x941e0].
        cwalk [e_pixDeserialize; 0x95bd0; 0x9f3dc; 0x9d968; 0x9eb78; 0xa2460; 0xa2d20; 0xa0ce4; 0x941e0].
        lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        unfold hid in POSE.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
          lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT Sx ?mm |- _ =>
            assert (KL : keeps_live (rt_live RT Sx) mm mc)
              by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
                  exact (live_outside_frame1 RT AF Sx mm fr usp (usp - 112) bb kk xx A ltac:(rewrite EFR; left; reflexivity) SPLE Hb Hx)) end end.
        rewrite ELV in KL. pose proof (pix_obj_keep _ _ _ pixs vs cvs KL POSE) as POS1. clear POSE KL.
        pose proof PCOPY as PC. unfold pixCopy_cps in PC.
        eapply cps_seq.
        { eapply PC with (lo := lo) (pixs := pixs) (vs := vs) (cvs := cvs); rt_side idtac.
          all: lazymatch goal with
               | |- pix_obj _ _ _ _ _ => rewrite ELV; exact POS1
               | |- p_data _ <> 0 => exact VDATA
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   unfold lres, TEMPLATE_COST, RASTER_COST, FRAMES_MAX, LIVE_MAX in *;
                   split; [rewrite EFR, FR0; cbn [length]; lia| split; [rewrite ELV; lia| split; [lia| rewrite ELV; exact LVPb]]]
               | |- ?g => idtac "LEFT:" g
               end. }
        after_call RT AF.
        lazymatch goal with AG : agree_on (fun a => aclient ?lv _ _ a /\ outside ?W a) ?ma ?mb |- _ =>
          assert (KL : keeps_live lv ma mb) by (apply (keeps_live_of_agree lv _ _ W ma mb AG); intros; exact I) end.
        rewrite ELV in KL.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ _) _ => rename Sx into Sc end.
        lazymatch goal with H : pix_obj (rt_live RT Sc) _ ?p ?vv ?cc |- _ => rename H into PO1; set (p1 := p) in *; set (v1 := vv) in *; set (c1 := cc) in * end.
        lazymatch goal with H : live_destroy p1 v1 c1 _ = _ |- _ => rename H into LDS1 end. rewrite ELV in LDS1.
        lazymatch goal with H : forall p n, In (p, n) (rt_live RT Sc) -> 0 < n |- _ => rename H into LVPc end.
        lazymatch goal with H : Z.of_nat (length (rt_live RT Sc)) <= _ |- _ => rename H into LVXc end. rewrite ELV in LVXc.
        lazymatch goal with H : p_data v1 <> 0 |- _ => rename H into V1DATA end.
        lazymatch goal with H : p_d v1 = p_d vs |- _ => rename H into VD1 end.
        assert (NZV1 : cmap_nz v1 c1).
        { lazymatch goal with LNC : p_cmap vs = 0 -> _, LCN : p_cmap vs <> 0 -> _ |- _ =>
            unfold cmap_nz in *; destruct (Z.eq_dec (p_cmap vs) 0) as [Z0|NZ];
            [ left; exact (proj1 (LNC Z0)) | right; rewrite (LCN NZ); destruct NZV as [Z1|N1]; [exfalso; exact (NZ Z1)| exact N1] ] end. }
        lazymatch goal with H : p_cmap vs <> 0 -> _ |- _ => clear H end.
        lazymatch goal with H : p_cmap vs = 0 -> _ |- _ => clear H end.
        assert (SUBc : forall e, In e (rt_live RT Sb) -> In e (rt_live RT Sc)) by (intros e He; rewrite <- LDS1 in He; exact (proj1 (live_destroy_In _ _ _ _ _ He))).
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; rewrite ELV; apply SUB0b; exact He| solve [frames_sub_tac]| lia]| exact I]).
        assert (FRSc : rt_frames RT Sc = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
        assert (SPLc : rt_sp0 RT Sc - 8388608 <= usp - 112) by (repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul).
        lazymatch goal with A : ART RT Sc ?mm |- _ =>
          assert (NCP1 : forall a, PF a -> a < p1 \/ p1 + 64 <= a)
            by (intros a [Ha _]; apply (inner_chunk_apart RT AF Sc mm p1 64 (rt_live RT Σ) (rt_frames RT Σ) usp a A (proj1 (pix_obj_entries _ _ _ _ _ PO1)));
                [ intros e He; pose proof (SUB0b e He) as Hb; rewrite <- LDS1 in Hb; destruct (live_destroy_In _ _ _ _ _ Hb) as (Q1 & Q2 & _); split; [exact Q1| exact Q2]
                | solve [frames_sub_tac] | repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul | exact Ha ]) end.
        (* [comment removed for export] *)
        pose proof (proj1 (pix_obj_entries _ _ _ _ _ PO1)) as P1IN.
        chunk_facts RT AF GP p1 64. fframe_chunk RT AF fr 1%nat 128 p1 64.
        pose proof (pix_obj_keep _ _ _ pixs vs cvs KL POS1) as POS2. clear POS1 KL.
        hide PO1. hide POS2.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
        Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_pixDeserialize; 0x95bd0; 0x9f3dc; 0x9d968; 0x9eb78; 0xa2460; 0xa2d20; 0xa0ce4; 0x941e0].
        cwalk [e_pixDeserialize; 0x95bd0; 0x9f3dc; 0x9d968; 0x9eb78; 0xa2460; 0xa2d20; 0xa0ce4; 0x941e0].
        lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        unfold hid in PO1, POS2.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
          lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT Sx ?mm |- _ =>
            assert (KL : keeps_live (rt_live RT Sx) mm mc)
              by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
                  exact (live_outside_frame1 RT AF Sx mm fr usp (usp - 112) bb kk xx A ltac:(rewrite FRSc; left; reflexivity) SPLc Hb Hx)) end end.
        pose proof (pix_obj_keep _ _ _ p1 v1 c1 KL PO1) as PO1b. pose proof (pix_obj_keep _ _ _ pixs vs cvs (keeps_live_sub _ _ _ _ KL SUBc) POS2) as POS3. clear PO1 POS2 KL.
        (* [comment removed for export] *)
        pose proof OP3 as GK. unfold pixGenerateMaskByBand_cps, gq_op_cps in GK.
        eapply cps_seq.
        { eapply GK with (lo := lo) (pix := p1) (v := v1) (cv := c1) (ras := [RA_TOP]); rt_side idtac.
          all: lazymatch goal with
               | |- pix_obj _ _ _ _ _ => exact PO1b
               | |- p_data _ <> 0 => exact V1DATA
               | |- cmap_nz _ _ => exact NZV1
               | |- uctx _ _ _ _ =>
                   unfold uctx; rewrite ?unsigned_lit by ul; unfold hid, parked in S0INV;
                   apply chain_ok_push with (fp1 := bv_unsigned s0);
                     [ lia | clear - SPA; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | unfold RA_TOP; lia | apply bv_unsigned_in_range
                     | rewrite Z_to_bv_bv_unsigned; rewrite <- RATOP; rewrite Z_to_bv_bv_unsigned; exact FRrec2
                     | cbn [chain_ok]; unfold link_invalid; lia ]
               | |- bv_unsigned _ = _ => rewrite ?unsigned_lit by ul; reflexivity
               | |- _ = [RA_TOP] => reflexivity
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   rewrite VD1; fold k3; unfold lres, TEMPLATE_COST, RASTER_COST, FRAMES_MAX, LIVE_MAX in *;
                   split; [rewrite FRSc, FR0; cbn [length]; lia| split; [lia| split; [lia| exact LVPc]]]
               | |- wZ _ _ => reflexivity
               | |- True => exact I
               | |- _ /\ _ =>      (* [comment removed for export] *)
                   repeat split;
                   first [ reflexivity
                         | unfold freg_is, fa0, fa1;
                           first [ etransitivity; [apply freg_get_same; reflexivity| vm_compute; reflexivity]
                                 | rewrite freg_get_other by reflexivity; etransitivity; [apply freg_get_same; reflexivity| vm_compute; reflexivity] ] ]
               | |- ?g => idtac "LEFT:" g
               end. }
        after_call RT AF.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ _) _ => rename Sx into Sd end.
        lazymatch goal with H : pix_obj (rt_live RT Sd) _ p1 v1 c1 |- _ => rename H into PO1d end.
        lazymatch goal with H : ?r = 0 \/ (pix_obj (rt_live RT Sd) _ ?r ?vv ?cc /\ _) |- _ => rename H into PRd; set (rr := r) in *; set (vr := vv) in *; set (cr := cc) in * end.
        lazymatch goal with H : rr = 0 -> rt_live RT Sd = _ |- _ => rename H into LZd end.
        lazymatch goal with H : rr <> 0 -> live_destroy rr vr cr _ = _ |- _ => rename H into LDd end.
        lazymatch goal with H : forall p n, In (p, n) (rt_live RT Sd) -> 0 < n |- _ => rename H into LVPd end.
        lazymatch goal with H : Z.of_nat (length (rt_live RT Sd)) <= _ |- _ => rename H into LVXd end.
        lazymatch goal with H : rt_credit RT Sc - _ <= rt_credit RT Sd |- _ => rewrite VD1 in H; fold k3 in H end.
        assert (SUBd : forall e, In e (rt_live RT Sc) -> In e (rt_live RT Sd)).
        { intros e He. destruct (Z.eq_dec rr 0) as [Z0|NZ]; [rewrite (LZd Z0); exact He|]. rewrite <- (LDd NZ) in He. exact (live_destroy_sub _ _ _ _ _ He). }
        (* [comment removed for export] *)
        lazymatch goal with AG : agree_on (fun a => aclient (rt_live RT Sc) _ _ a /\ outside _ a) ?ma ?mb, A : ART RT Sc ?mx |- _ =>
          assert (KL : keeps_live (rt_live RT Sb) ma mb)
            by (apply (keeps_live_others RT AF Sc mx _ _ (rt_live RT Sb) p1 64 (p1 + 20) (p1 + 24) ma mb A
                         (proj1 (pix_obj_entries _ _ _ _ _ PO1b)) ltac:(lia) ltac:(lia)
                         ltac:(intros e He; split; [exact (SUBc e He)| rewrite <- LDS1 in He; exact (proj1 (proj2 (live_destroy_In _ _ _ _ _ He)))]) AG)) end.
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; apply SUBc; apply SUB0b; exact He| solve [frames_sub_tac]| lia]|
                                        cbn [outside]; pose proof (NCP1 _ Hx) as NCPx; split; [clear - NCPx; lia| exact I]]).
        assert (FRSd : rt_frames RT Sd = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
        assert (SPLd : rt_sp0 RT Sd - 8388608 <= usp - 112) by (repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul).
        pose proof (pix_obj_keep _ _ _ pixs vs cvs KL POS3) as POS4. clear POS3 KL.
        hide PO1b. hide PO1d. hide POS4. hide PRd. hide LZd. hide LDd.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
        Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_pixDeserialize; 0x95bd0; 0x9f3dc; 0x9d968; 0x9eb78; 0xa2460; 0xa2d20; 0xa0ce4; 0x941e0].
        cwalk [e_pixDeserialize; 0x95bd0; 0x9f3dc; 0x9d968; 0x9eb78; 0xa2460; 0xa2d20; 0xa0ce4; 0x941e0].
        lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
        pose proof FSE as SHB8. split_at SHB8 8%nat SHB8b. split_at SHB8b 1%nat SHB8c. clear SHB8 SHB8c.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        unfold hid in PO1d, POS4, PRd.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
          lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT Sx ?mm |- _ =>
            assert (KL : keeps_live (rt_live RT Sx) mm mc)
              by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
                  exact (live_outside_frame1 RT AF Sx mm fr usp (usp - 112) bb kk xx A ltac:(rewrite FRSd; left; reflexivity) SPLd Hb Hx)) end end.
        pose proof (pix_obj_keep _ _ _ p1 v1 c1 KL PO1d) as PO1e.
        pose proof (pix_obj_keep _ _ _ pixs vs cvs (keeps_live_sub _ _ _ _ KL (fun e He => SUBd e (SUBc e He))) POS4) as POS5.
        assert (PRd3 : rr = 0 \/ (pix_obj (rt_live RT Sd) _ rr vr cr /\ p_data vr <> 0))
          by (destruct PRd as [Z0|(PO & DN)]; [left; exact Z0| right; split; [exact (pix_obj_keep _ _ _ rr vr cr KL PO)| exact DN]]).
        clear PO1d POS4 PRd KL.
        pose proof DESTROY as DY. unfold pixDestroy_cps in DY.
        eapply cps_seq.
        { eapply DY with (lo := lo) (pp := fr + 64) (pix := p1) (v := v1) (cv := c1) (ras := [RA_TOP]); rt_side idtac.
          all: lazymatch goal with
               | |- optrL _ _ _ _ _ _ =>
                   unfold optrL; split;
                   [ right; exists fr, 1%nat; rewrite FRSd; change (fs_size 1) with 128;
                     split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                     split; [lia|]; split; [lia|];
                     replace (shad (fr + 64)) with (fr / 8 + 2147450888) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                     destruct SHB8b as [[_ B] _]; exact B
                   | let Q := fresh "Q" in pose proof FRSH as Q; unfold parked in Q; unfold SEGTOP_A;
                     repeat split; first [clear - FR0; lia | clear - FR64; Z.div_mod_to_equations; lia | clear - Q; lia | clear - FRSEG; lia] ]
               | |- rw_cells _ _ _ [C8 _] => exact P1E
               | |- pix_obj _ _ _ _ _ => exact PO1e
               | |- uctx _ _ _ _ =>
                   unfold uctx; rewrite ?unsigned_lit by ul; unfold hid, parked in S0INV;
                   apply chain_ok_push with (fp1 := bv_unsigned s0);
                     [ lia | clear - SPA; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | unfold RA_TOP; lia | apply bv_unsigned_in_range
                     | rewrite Z_to_bv_bv_unsigned; rewrite <- RATOP; rewrite Z_to_bv_bv_unsigned; exact FRrec2
                     | cbn [chain_ok]; unfold link_invalid; lia ]
               | |- Forall _ DESTROY_FREE_RAS => rewrite ?unsigned_lit by ul; apply tr_destroy; unfold FUZZ_DESTROY_RAS; cbn [In]; tauto
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   unfold lres, TEMPLATE_COST, RASTER_COST, FRAMES_MAX, LIVE_MAX in *;
                   split; [rewrite FRSd, FR0; cbn [length]; lia| split; [lia| split; [lia| exact LVPd]]]
               | |- ?g => idtac "LEFT:" g
               end. }
        clear SHB8b.
        after_call RT AF.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ _) _ => rename Sx into Se end.
        lazymatch goal with H : rt_live RT Se = _ |- _ => rename H into LVe end.
        assert (FRSe : rt_frames RT Se = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
        assert (SPLe : rt_sp0 RT Se - 8388608 <= usp - 112) by (repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul).
        assert (SUBe : forall e, In e (rt_live RT Sb) -> In e (rt_live RT Se))
          by (intros e He; rewrite LVe; rewrite <- LDS1 in He; exact (live_destroy_mono p1 v1 c1 _ _ SUBd e He)).
        lazymatch goal with AG : agree_on (fun a => aclient ?lv _ _ a /\ outside ?W a) ?ma ?mb, A : ART RT Se ?mb |- _ =>
          assert (KL : keeps_live lv ma mb)
            by (apply (keeps_live_of_agree lv _ _ W ma mb AG); intros bb kk xx Hb Hx;
                exact (live_outside_local RT AF Se mb fr 1%nat 64 bb kk xx A ltac:(rewrite FRSe; left; reflexivity) ltac:(lia) ltac:(change (fs_size 1) with 128; lia) Hb Hx)) end.
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; apply SUBe; apply SUB0b; exact He| solve [frames_sub_tac]| lia]|
                                        cbn [outside]; destruct (NFA _ Hx) as [N1 N2]; split; [lia| exact I]]).
        pose proof (pix_obj_keep _ _ _ pixs vs cvs (keeps_live_sub _ _ _ _ KL SUBe) POS5) as POS6.
        assert (LVPe : forall p n, In (p, n) (rt_live RT Se) -> 0 < n)
          by (intros p n H; rewrite LVe in H; exact (LVPd p n (live_destroy_sub _ _ _ _ _ H))).
        assert (LVXe : Z.of_nat (length (rt_live RT Se)) <= Z.of_nat (length (rt_live RT Sd)))
          by (rewrite LVe; pose proof (live_destroy_len p1 v1 c1 (rt_live RT Sd)); lia).
        unfold hid in LZd, LDd, PO1b.
        destruct (Z.eq_dec rr 0) as [RZ|RNZ].
        - (* [comment removed for export] *)
          clear PRd3. assert (LVe0 : rt_live RT Se = rt_live RT Sb) by (rewrite LVe, (LZd RZ); exact LDS1).
          clear LVe KL. rewrite RZ in *.
          hide POS6.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
        Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_pixDeserialize; 0x95bd0; 0x9f3dc; 0x9d968; 0x9eb78; 0xa2460; 0xa2d20; 0xa0ce4; 0x941e0].
        cwalk [e_pixDeserialize; 0x95bd0; 0x9f3dc; 0x9d968; 0x9eb78; 0xa2460; 0xa2d20; 0xa0ce4; 0x941e0].
        lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
        pose proof FSE as SHB12. split_at SHB12 12%nat SHB12b. split_at SHB12b 1%nat SHB12c. clear SHB12 SHB12c.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        unfold hid in POS6.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
          lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT Sx ?mm |- _ =>
            assert (KL : keeps_live (rt_live RT Sx) mm mc)
              by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
                  exact (live_outside_frame1 RT AF Sx mm fr usp (usp - 112) bb kk xx A ltac:(rewrite FRSe; left; reflexivity) SPLe Hb Hx)) end end.
        pose proof (pix_obj_keep _ _ _ pixs vs cvs (keeps_live_sub _ _ _ _ KL SUBe) POS6) as POS7. clear POS6 KL.
        pose proof DNULL as DN. unfold pixDestroy_null_cps in DN.
        eapply cps_seq.
        { eapply DN with (lo := lo) (pp := fr + 96); rt_side idtac.
          all: lazymatch goal with
               | |- optrL _ _ _ _ _ _ =>
                   unfold optrL; split;
                   [ right; exists fr, 1%nat; rewrite FRSe; change (fs_size 1) with 128;
                     split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                     split; [lia|]; split; [lia|];
                     replace (shad (fr + 96)) with (fr / 8 + 2147450892) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                     destruct SHB12b as [[_ B] _]; exact B
                   | let Q := fresh "Q" in pose proof FRSH as Q; unfold parked in Q; unfold SEGTOP_A;
                     repeat split; first [clear - FR0; lia | clear - FR64; Z.div_mod_to_equations; lia | clear - Q; lia | clear - FRSEG; lia] ]
               | |- rw_cells _ _ _ [C8 _] => exact P2E
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   unfold lres, TEMPLATE_COST, RASTER_COST, FRAMES_MAX, LIVE_MAX in *;
                   split; [rewrite FRSe, FR0; cbn [length]; lia| split; [rewrite LVe0; lia| split; [lia| exact LVPe]]]
               | |- ?g => idtac "LEFT:" g
               end. }
        clear SHB12b.
        after_call RT AF.
        lazymatch goal with AG : agree_on (fun a => aclient ?lv _ _ a /\ outside ?W a) ?ma ?mb |- _ =>
          assert (KL : keeps_live lv ma mb) by (apply (keeps_live_of_agree lv _ _ W ma mb AG); intros; exact I) end.
        lazymatch goal with H : rt_live RT ?Sx = rt_live RT Se |- _ => rewrite LVe0 in H; rewrite H in KL end.
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; apply SUB0b; exact He| solve [frames_sub_tac]| lia]| exact I]).
        pose proof (pix_obj_keep _ _ _ pixs vs cvs KL POS7) as POS8. clear POS7 KL.
          to_entry.
          eapply CONT3; try eassumption.
          all: lazymatch goal with
               | |- pix_obj _ _ _ _ _ => exact POS8
               | |- rt_live _ _ = _ => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity
               | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
               | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
               | |- _ <= rt_credit _ _ => unfold TEMPLATE_COST, RASTER_COST in *; lia
               | |- ?g => idtac "LEFT:" g
               end.
        - (* [comment removed for export] *)
          destruct PRd3 as [Z0|(POR & RDATA)]; [exfalso; exact (RNZ Z0)|].
          pose proof (obj_fresh_of_eq (rt_live RT Sd) (rt_live RT Sc) _ rr vr cr _ p1 v1 c1 (LDd RNZ) POR PO1b) as FRESH.
          pose proof (pix_obj_in_destroy (rt_live RT Sd) _ rr vr cr p1 v1 c1 POR FRESH) as PORe0. rewrite <- LVe in PORe0.
          pose proof (pix_obj_keep _ _ _ rr vr cr KL PORe0) as PORe. clear POR PORe0 FRESH KL.
          assert (LVf0 : live_destroy rr vr cr (rt_live RT Se) = rt_live RT Sb)
            by (rewrite LVe, live_destroy_comm, (LDd RNZ); exact LDS1).
          hide POS6. hide PORe. hide LVf0.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
        Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_pixDeserialize; 0x95bd0; 0x9f3dc; 0x9d968; 0x9eb78; 0xa2460; 0xa2d20; 0xa0ce4; 0x941e0].
        cwalk [e_pixDeserialize; 0x95bd0; 0x9f3dc; 0x9d968; 0x9eb78; 0xa2460; 0xa2d20; 0xa0ce4; 0x941e0].
        lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
        pose proof FSE as SHB12. split_at SHB12 12%nat SHB12b. split_at SHB12b 1%nat SHB12c. clear SHB12 SHB12c.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        unfold hid in POS6, PORe.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
          lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT Sx ?mm |- _ =>
            assert (KL : keeps_live (rt_live RT Sx) mm mc)
              by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
                  exact (live_outside_frame1 RT AF Sx mm fr usp (usp - 112) bb kk xx A ltac:(rewrite FRSe; left; reflexivity) SPLe Hb Hx)) end end.
        pose proof (pix_obj_keep _ _ _ pixs vs cvs (keeps_live_sub _ _ _ _ KL SUBe) POS6) as POS7. pose proof (pix_obj_keep _ _ _ rr vr cr KL PORe) as POR2. clear POS6 PORe KL.
        eapply cps_seq.
        { eapply DY with (lo := lo) (pp := fr + 96) (pix := rr) (v := vr) (cv := cr) (ras := [RA_TOP]); rt_side idtac.
          all: lazymatch goal with
               | |- optrL _ _ _ _ _ _ =>
                   unfold optrL; split;
                   [ right; exists fr, 1%nat; rewrite FRSe; change (fs_size 1) with 128;
                     split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                     split; [lia|]; split; [lia|];
                     replace (shad (fr + 96)) with (fr / 8 + 2147450892) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                     destruct SHB12b as [[_ B] _]; exact B
                   | let Q := fresh "Q" in pose proof FRSH as Q; unfold parked in Q; unfold SEGTOP_A;
                     repeat split; first [clear - FR0; lia | clear - FR64; Z.div_mod_to_equations; lia | clear - Q; lia | clear - FRSEG; lia] ]
               | |- rw_cells _ _ _ [C8 _] => exact P2E
               | |- pix_obj _ _ _ _ _ => exact POR2
               | |- uctx _ _ _ _ =>
                   unfold uctx; rewrite ?unsigned_lit by ul; unfold hid, parked in S0INV;
                   apply chain_ok_push with (fp1 := bv_unsigned s0);
                     [ lia | clear - SPA; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | unfold RA_TOP; lia | apply bv_unsigned_in_range
                     | rewrite Z_to_bv_bv_unsigned; rewrite <- RATOP; rewrite Z_to_bv_bv_unsigned; exact FRrec2
                     | cbn [chain_ok]; unfold link_invalid; lia ]
               | |- Forall _ DESTROY_FREE_RAS => rewrite ?unsigned_lit by ul; apply tr_destroy; unfold FUZZ_DESTROY_RAS; cbn [In]; tauto
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   unfold lres, TEMPLATE_COST, RASTER_COST, FRAMES_MAX, LIVE_MAX in *;
                   split; [rewrite FRSe, FR0; cbn [length]; lia| split; [lia| split; [lia| exact LVPe]]]
               | |- ?g => idtac "LEFT:" g
               end. }
        clear POR2 SHB12b.
        after_call RT AF.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ _) _ => rename Sx into Sf end.
        lazymatch goal with H : rt_live RT Sf = _ |- _ => rename H into LVf end.
        unfold hid in LVf0. rewrite LVf0 in LVf.
        assert (FRSf : rt_frames RT Sf = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
        lazymatch goal with AG : agree_on (fun a => aclient ?lv _ _ a /\ outside ?W a) ?ma ?mb, A : ART RT Sf ?mb |- _ =>
          assert (KL : keeps_live lv ma mb)
            by (apply (keeps_live_of_agree lv _ _ W ma mb AG); intros bb kk xx Hb Hx;
                exact (live_outside_local RT AF Sf mb fr 1%nat 96 bb kk xx A ltac:(rewrite FRSf; left; reflexivity) ltac:(lia) ltac:(change (fs_size 1) with 128; lia) Hb Hx)) end.
        rewrite LVf in KL.
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; rewrite LVf; apply SUB0b; exact He| solve [frames_sub_tac]| lia]|
                                        cbn [outside]; destruct (NFA _ Hx) as [N1 N2]; split; [lia| exact I]]).
        pose proof (pix_obj_keep _ _ _ pixs vs cvs KL POS7) as POS8. clear POS7 KL.
          to_entry.
          eapply CONT3; try eassumption.
          all: lazymatch goal with
               | |- pix_obj _ _ _ _ _ => exact POS8
               | |- rt_live _ _ = _ => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity
               | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
               | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
               | |- _ <= rt_credit _ _ => unfold TEMPLATE_COST, RASTER_COST in *; lia
               | |- ?g => idtac "LEFT:" g
               end.
      }
      lazymatch goal with FRx : rw_cells asegs _ (usp + -112) ?cs |- _ =>
        assert (CONT1 : forall (S : rts RT) (mE : mem) (x1 x2 : word)
                  (r1 r5 r6 r7 r9 r10 r11 r12 r13 r14 r15 r16 r17 r22 r28 r29 r30 r31 : word) F' fc',
            ART RT S mE -> mem_inv asegs mE -> stk asegs mE lo (usp + -112) -> rw_cells asegs mE (usp + -112) cs ->
            rw_cells asegs mE fr [C8 (Z_to_bv 64 1102416563)] ->
            rw_cells asegs mE (fr + 32) [C8 (Z_to_bv 64 pixs)] -> rw_cells asegs mE (fr + 64) [C8 x1] -> rw_cells asegs mE (fr + 96) [C8 x2] ->
            rw_cells asegs mE (fr / 8 + 2147450880) [C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13))] ->
            LIBH mE -> io_ssp mE -> agree_on PF m mE -> pix_obj (rt_live RT Sb) mE pixs vs cvs ->
            rt_live RT S = rt_live RT Sb -> rt_frames RT S = (fr, 1%nat) :: rt_frames RT Σ -> rt_sp0 RT S = rt_sp0 RT Σ ->
            rt_credit RT Σ - (RASTER_COST + 65 + 1 * (TEMPLATE_COST + 2) + (k1)) <= rt_credit RT S ->
            cps asegs (ASTA RT S PMc (eq (entry_st r1 (Z_to_bv 64 (usp + -112)) gp (Z_to_bv 64 TP_A) r5 r6 r7 (Z_to_bv 64 usp) r9
                                          r10 r11 r12 r13 r14 r15 r16 r17 (Z_to_bv 64 fr) (Z_to_bv 64 (fr + 32)) (Z_to_bv 64 (fr + 96)) (Z_to_bv 64 (fr + 64)) r22 (Z_to_bv 64 (fr / 8 + 2147450880))
                                          (Z_to_bv 64 fr) s9 s10 s11 r28 r29 r30 r31 F' fc' 0x90aec mE))) QF) end.
      { intros S mE wx1 wx2 r1 r5 r6 r7 r9 r10 r11 r12 r13 r14 r15 r16 r17 r22 r28 r29 r30 r31 F' fc'
          ARTE MIE STE FRE FHE PSE P1E P2E FSE LHE SSPE AGE POSE ELV EFR ESP0 ECR.
        clear AGF. rename AGE into AGF.
        repeat match goal with H : rw_cells asegs _ _ _ |- _ => lazymatch H with FRE => fail | FHE => fail | PSE => fail | P1E => fail | P2E => fail | FSE => fail | _ => clear H end end.
        repeat match goal with H : ro_cells asegs _ _ _ |- _ => clear H end.
        repeat match goal with H : ART RT _ _ |- _ => lazymatch H with ARTE => fail | _ => clear H end end.
        repeat match goal with H : LIBH _ |- _ => lazymatch H with LHE => fail | _ => clear H end end.
        repeat match goal with H : io_ssp _ |- _ => lazymatch H with SSPE => fail | _ => clear H end end.
        repeat match goal with H : stk asegs _ _ _ |- _ => lazymatch H with STE => fail | _ => clear H end end.
        repeat match goal with H : mem_inv asegs _ |- _ => lazymatch H with MIE => fail | _ => clear H end end.
        repeat match goal with H : wmono asegs _ _ |- _ => clear H end.
        repeat match goal with H : munch _ _ _ |- _ => clear H end.
        repeat match goal with H : rt_frames RT _ = _ |- _ => lazymatch H with EFR => fail | FR0 => fail | _ => clear H end end.
        repeat match goal with H : rt_live RT _ = _ |- _ => lazymatch H with ELV => fail | _ => clear H end end.
        repeat match goal with H : rt_sp0 RT _ = _ |- _ => lazymatch H with ESP0 => fail | _ => clear H end end.
        repeat match goal with H : rt_credit RT _ = _ |- _ => clear H end.
        repeat match goal with H : rt_credit RT _ - _ <= _ |- _ => lazymatch H with ECR => fail | _ => clear H end end.
        clear_acc.
        pose proof FRE as FRrec. split_before FRrec (C8 s0) FRrec2. clear FRrec.
        assert (SPLE : rt_sp0 RT S - 8388608 <= usp - 112) by (rewrite ESP0; ul).
        hide POSE.
        unfold entry_st.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
        Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_pixDeserialize; 0x95bd0; 0x9f3dc; 0x9d968; 0x9eb78; 0xa2460; 0xa2d20; 0xa0ce4; 0x941e0].
        cwalk [e_pixDeserialize; 0x95bd0; 0x9f3dc; 0x9d968; 0x9eb78; 0xa2460; 0xa2d20; 0xa0ce4; 0x941e0].
        lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        unfold hid in POSE.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
          lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT Sx ?mm |- _ =>
            assert (KL : keeps_live (rt_live RT Sx) mm mc)
              by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
                  exact (live_outside_frame1 RT AF Sx mm fr usp (usp - 112) bb kk xx A ltac:(rewrite EFR; left; reflexivity) SPLE Hb Hx)) end end.
        rewrite ELV in KL. pose proof (pix_obj_keep _ _ _ pixs vs cvs KL POSE) as POS1. clear POSE KL.
        pose proof PCOPY as PC. unfold pixCopy_cps in PC.
        eapply cps_seq.
        { eapply PC with (lo := lo) (pixs := pixs) (vs := vs) (cvs := cvs); rt_side idtac.
          all: lazymatch goal with
               | |- pix_obj _ _ _ _ _ => rewrite ELV; exact POS1
               | |- p_data _ <> 0 => exact VDATA
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   unfold lres, TEMPLATE_COST, RASTER_COST, FRAMES_MAX, LIVE_MAX in *;
                   split; [rewrite EFR, FR0; cbn [length]; lia| split; [rewrite ELV; lia| split; [lia| rewrite ELV; exact LVPb]]]
               | |- ?g => idtac "LEFT:" g
               end. }
        after_call RT AF.
        lazymatch goal with AG : agree_on (fun a => aclient ?lv _ _ a /\ outside ?W a) ?ma ?mb |- _ =>
          assert (KL : keeps_live lv ma mb) by (apply (keeps_live_of_agree lv _ _ W ma mb AG); intros; exact I) end.
        rewrite ELV in KL.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ _) _ => rename Sx into Sc end.
        lazymatch goal with H : pix_obj (rt_live RT Sc) _ ?p ?vv ?cc |- _ => rename H into PO1; set (p1 := p) in *; set (v1 := vv) in *; set (c1 := cc) in * end.
        lazymatch goal with H : live_destroy p1 v1 c1 _ = _ |- _ => rename H into LDS1 end. rewrite ELV in LDS1.
        lazymatch goal with H : forall p n, In (p, n) (rt_live RT Sc) -> 0 < n |- _ => rename H into LVPc end.
        lazymatch goal with H : Z.of_nat (length (rt_live RT Sc)) <= _ |- _ => rename H into LVXc end. rewrite ELV in LVXc.
        lazymatch goal with H : p_data v1 <> 0 |- _ => rename H into V1DATA end.
        lazymatch goal with H : p_d v1 = p_d vs |- _ => rename H into VD1 end.
        assert (NZV1 : cmap_nz v1 c1).
        { lazymatch goal with LNC : p_cmap vs = 0 -> _, LCN : p_cmap vs <> 0 -> _ |- _ =>
            unfold cmap_nz in *; destruct (Z.eq_dec (p_cmap vs) 0) as [Z0|NZ];
            [ left; exact (proj1 (LNC Z0)) | right; rewrite (LCN NZ); destruct NZV as [Z1|N1]; [exfalso; exact (NZ Z1)| exact N1] ] end. }
        lazymatch goal with H : p_cmap vs <> 0 -> _ |- _ => clear H end.
        lazymatch goal with H : p_cmap vs = 0 -> _ |- _ => clear H end.
        assert (SUBc : forall e, In e (rt_live RT Sb) -> In e (rt_live RT Sc)) by (intros e He; rewrite <- LDS1 in He; exact (proj1 (live_destroy_In _ _ _ _ _ He))).
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; rewrite ELV; apply SUB0b; exact He| solve [frames_sub_tac]| lia]| exact I]).
        assert (FRSc : rt_frames RT Sc = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
        assert (SPLc : rt_sp0 RT Sc - 8388608 <= usp - 112) by (repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul).
        lazymatch goal with A : ART RT Sc ?mm |- _ =>
          assert (NCP1 : forall a, PF a -> a < p1 \/ p1 + 64 <= a)
            by (intros a [Ha _]; apply (inner_chunk_apart RT AF Sc mm p1 64 (rt_live RT Σ) (rt_frames RT Σ) usp a A (proj1 (pix_obj_entries _ _ _ _ _ PO1)));
                [ intros e He; pose proof (SUB0b e He) as Hb; rewrite <- LDS1 in Hb; destruct (live_destroy_In _ _ _ _ _ Hb) as (Q1 & Q2 & _); split; [exact Q1| exact Q2]
                | solve [frames_sub_tac] | repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul | exact Ha ]) end.
        (* [comment removed for export] *)
        pose proof (proj1 (pix_obj_entries _ _ _ _ _ PO1)) as P1IN.
        chunk_facts RT AF GP p1 64. fframe_chunk RT AF fr 1%nat 128 p1 64.
        pose proof (pix_obj_keep _ _ _ pixs vs cvs KL POS1) as POS2. clear POS1 KL.
        hide PO1. hide POS2.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
        Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_pixDeserialize; 0x95bd0; 0x9f3dc; 0x9d968; 0x9eb78; 0xa2460; 0xa2d20; 0xa0ce4; 0x941e0].
        cwalk [e_pixDeserialize; 0x95bd0; 0x9f3dc; 0x9d968; 0x9eb78; 0xa2460; 0xa2d20; 0xa0ce4; 0x941e0].
        lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        unfold hid in PO1, POS2.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
          lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT Sx ?mm |- _ =>
            assert (KL : keeps_live (rt_live RT Sx) mm mc)
              by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
                  exact (live_outside_frame1 RT AF Sx mm fr usp (usp - 112) bb kk xx A ltac:(rewrite FRSc; left; reflexivity) SPLc Hb Hx)) end end.
        pose proof (pix_obj_keep _ _ _ p1 v1 c1 KL PO1) as PO1b. pose proof (pix_obj_keep _ _ _ pixs vs cvs (keeps_live_sub _ _ _ _ KL SUBc) POS2) as POS3. clear PO1 POS2 KL.
        (* [comment removed for export] *)
        pose proof OP2 as GK. unfold pixDitherToBinary_cps, gq_op_cps in GK.
        eapply cps_seq.
        { eapply GK with (lo := lo) (pix := p1) (v := v1) (cv := c1) (ras := [RA_TOP]); rt_side idtac.
          all: lazymatch goal with
               | |- pix_obj _ _ _ _ _ => exact PO1b
               | |- p_data _ <> 0 => exact V1DATA
               | |- cmap_nz _ _ => exact NZV1
               | |- uctx _ _ _ _ =>
                   unfold uctx; rewrite ?unsigned_lit by ul; unfold hid, parked in S0INV;
                   apply chain_ok_push with (fp1 := bv_unsigned s0);
                     [ lia | clear - SPA; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | unfold RA_TOP; lia | apply bv_unsigned_in_range
                     | rewrite Z_to_bv_bv_unsigned; rewrite <- RATOP; rewrite Z_to_bv_bv_unsigned; exact FRrec2
                     | cbn [chain_ok]; unfold link_invalid; lia ]
               | |- bv_unsigned _ = _ => rewrite ?unsigned_lit by ul; reflexivity
               | |- _ = [RA_TOP] => reflexivity
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   rewrite VD1; fold k2; unfold lres, TEMPLATE_COST, RASTER_COST, FRAMES_MAX, LIVE_MAX in *;
                   split; [rewrite FRSc, FR0; cbn [length]; lia| split; [lia| split; [lia| exact LVPc]]]
               | |- wZ _ _ => reflexivity
               | |- True => exact I
               | |- _ /\ _ =>      (* [comment removed for export] *)
                   repeat split;
                   first [ reflexivity
                         | unfold freg_is, fa0, fa1;
                           first [ etransitivity; [apply freg_get_same; reflexivity| vm_compute; reflexivity]
                                 | rewrite freg_get_other by reflexivity; etransitivity; [apply freg_get_same; reflexivity| vm_compute; reflexivity] ] ]
               | |- ?g => idtac "LEFT:" g
               end. }
        after_call RT AF.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ _) _ => rename Sx into Sd end.
        lazymatch goal with H : pix_obj (rt_live RT Sd) _ p1 v1 c1 |- _ => rename H into PO1d end.
        lazymatch goal with H : ?r = 0 \/ (pix_obj (rt_live RT Sd) _ ?r ?vv ?cc /\ _) |- _ => rename H into PRd; set (rr := r) in *; set (vr := vv) in *; set (cr := cc) in * end.
        lazymatch goal with H : rr = 0 -> rt_live RT Sd = _ |- _ => rename H into LZd end.
        lazymatch goal with H : rr <> 0 -> live_destroy rr vr cr _ = _ |- _ => rename H into LDd end.
        lazymatch goal with H : forall p n, In (p, n) (rt_live RT Sd) -> 0 < n |- _ => rename H into LVPd end.
        lazymatch goal with H : Z.of_nat (length (rt_live RT Sd)) <= _ |- _ => rename H into LVXd end.
        lazymatch goal with H : rt_credit RT Sc - _ <= rt_credit RT Sd |- _ => rewrite VD1 in H; fold k2 in H end.
        assert (SUBd : forall e, In e (rt_live RT Sc) -> In e (rt_live RT Sd)).
        { intros e He. destruct (Z.eq_dec rr 0) as [Z0|NZ]; [rewrite (LZd Z0); exact He|]. rewrite <- (LDd NZ) in He. exact (live_destroy_sub _ _ _ _ _ He). }
        (* [comment removed for export] *)
        lazymatch goal with AG : agree_on (fun a => aclient (rt_live RT Sc) _ _ a /\ outside _ a) ?ma ?mb, A : ART RT Sc ?mx |- _ =>
          assert (KL : keeps_live (rt_live RT Sb) ma mb)
            by (apply (keeps_live_others RT AF Sc mx _ _ (rt_live RT Sb) p1 64 (p1 + 20) (p1 + 24) ma mb A
                         (proj1 (pix_obj_entries _ _ _ _ _ PO1b)) ltac:(lia) ltac:(lia)
                         ltac:(intros e He; split; [exact (SUBc e He)| rewrite <- LDS1 in He; exact (proj1 (proj2 (live_destroy_In _ _ _ _ _ He)))]) AG)) end.
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; apply SUBc; apply SUB0b; exact He| solve [frames_sub_tac]| lia]|
                                        cbn [outside]; pose proof (NCP1 _ Hx) as NCPx; split; [clear - NCPx; lia| exact I]]).
        assert (FRSd : rt_frames RT Sd = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
        assert (SPLd : rt_sp0 RT Sd - 8388608 <= usp - 112) by (repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul).
        pose proof (pix_obj_keep _ _ _ pixs vs cvs KL POS3) as POS4. clear POS3 KL.
        hide PO1b. hide PO1d. hide POS4. hide PRd. hide LZd. hide LDd.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
        Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_pixDeserialize; 0x95bd0; 0x9f3dc; 0x9d968; 0x9eb78; 0xa2460; 0xa2d20; 0xa0ce4; 0x941e0].
        cwalk [e_pixDeserialize; 0x95bd0; 0x9f3dc; 0x9d968; 0x9eb78; 0xa2460; 0xa2d20; 0xa0ce4; 0x941e0].
        lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
        pose proof FSE as SHB8. split_at SHB8 8%nat SHB8b. split_at SHB8b 1%nat SHB8c. clear SHB8 SHB8c.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        unfold hid in PO1d, POS4, PRd.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
          lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT Sx ?mm |- _ =>
            assert (KL : keeps_live (rt_live RT Sx) mm mc)
              by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
                  exact (live_outside_frame1 RT AF Sx mm fr usp (usp - 112) bb kk xx A ltac:(rewrite FRSd; left; reflexivity) SPLd Hb Hx)) end end.
        pose proof (pix_obj_keep _ _ _ p1 v1 c1 KL PO1d) as PO1e.
        pose proof (pix_obj_keep _ _ _ pixs vs cvs (keeps_live_sub _ _ _ _ KL (fun e He => SUBd e (SUBc e He))) POS4) as POS5.
        assert (PRd3 : rr = 0 \/ (pix_obj (rt_live RT Sd) _ rr vr cr /\ p_data vr <> 0))
          by (destruct PRd as [Z0|(PO & DN)]; [left; exact Z0| right; split; [exact (pix_obj_keep _ _ _ rr vr cr KL PO)| exact DN]]).
        clear PO1d POS4 PRd KL.
        pose proof DESTROY as DY. unfold pixDestroy_cps in DY.
        eapply cps_seq.
        { eapply DY with (lo := lo) (pp := fr + 64) (pix := p1) (v := v1) (cv := c1) (ras := [RA_TOP]); rt_side idtac.
          all: lazymatch goal with
               | |- optrL _ _ _ _ _ _ =>
                   unfold optrL; split;
                   [ right; exists fr, 1%nat; rewrite FRSd; change (fs_size 1) with 128;
                     split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                     split; [lia|]; split; [lia|];
                     replace (shad (fr + 64)) with (fr / 8 + 2147450888) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                     destruct SHB8b as [[_ B] _]; exact B
                   | let Q := fresh "Q" in pose proof FRSH as Q; unfold parked in Q; unfold SEGTOP_A;
                     repeat split; first [clear - FR0; lia | clear - FR64; Z.div_mod_to_equations; lia | clear - Q; lia | clear - FRSEG; lia] ]
               | |- rw_cells _ _ _ [C8 _] => exact P1E
               | |- pix_obj _ _ _ _ _ => exact PO1e
               | |- uctx _ _ _ _ =>
                   unfold uctx; rewrite ?unsigned_lit by ul; unfold hid, parked in S0INV;
                   apply chain_ok_push with (fp1 := bv_unsigned s0);
                     [ lia | clear - SPA; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | unfold RA_TOP; lia | apply bv_unsigned_in_range
                     | rewrite Z_to_bv_bv_unsigned; rewrite <- RATOP; rewrite Z_to_bv_bv_unsigned; exact FRrec2
                     | cbn [chain_ok]; unfold link_invalid; lia ]
               | |- Forall _ DESTROY_FREE_RAS => rewrite ?unsigned_lit by ul; apply tr_destroy; unfold FUZZ_DESTROY_RAS; cbn [In]; tauto
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   unfold lres, TEMPLATE_COST, RASTER_COST, FRAMES_MAX, LIVE_MAX in *;
                   split; [rewrite FRSd, FR0; cbn [length]; lia| split; [lia| split; [lia| exact LVPd]]]
               | |- ?g => idtac "LEFT:" g
               end. }
        clear SHB8b.
        after_call RT AF.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ _) _ => rename Sx into Se end.
        lazymatch goal with H : rt_live RT Se = _ |- _ => rename H into LVe end.
        assert (FRSe : rt_frames RT Se = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
        assert (SPLe : rt_sp0 RT Se - 8388608 <= usp - 112) by (repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul).
        assert (SUBe : forall e, In e (rt_live RT Sb) -> In e (rt_live RT Se))
          by (intros e He; rewrite LVe; rewrite <- LDS1 in He; exact (live_destroy_mono p1 v1 c1 _ _ SUBd e He)).
        lazymatch goal with AG : agree_on (fun a => aclient ?lv _ _ a /\ outside ?W a) ?ma ?mb, A : ART RT Se ?mb |- _ =>
          assert (KL : keeps_live lv ma mb)
            by (apply (keeps_live_of_agree lv _ _ W ma mb AG); intros bb kk xx Hb Hx;
                exact (live_outside_local RT AF Se mb fr 1%nat 64 bb kk xx A ltac:(rewrite FRSe; left; reflexivity) ltac:(lia) ltac:(change (fs_size 1) with 128; lia) Hb Hx)) end.
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; apply SUBe; apply SUB0b; exact He| solve [frames_sub_tac]| lia]|
                                        cbn [outside]; destruct (NFA _ Hx) as [N1 N2]; split; [lia| exact I]]).
        pose proof (pix_obj_keep _ _ _ pixs vs cvs (keeps_live_sub _ _ _ _ KL SUBe) POS5) as POS6.
        assert (LVPe : forall p n, In (p, n) (rt_live RT Se) -> 0 < n)
          by (intros p n H; rewrite LVe in H; exact (LVPd p n (live_destroy_sub _ _ _ _ _ H))).
        assert (LVXe : Z.of_nat (length (rt_live RT Se)) <= Z.of_nat (length (rt_live RT Sd)))
          by (rewrite LVe; pose proof (live_destroy_len p1 v1 c1 (rt_live RT Sd)); lia).
        unfold hid in LZd, LDd, PO1b.
        destruct (Z.eq_dec rr 0) as [RZ|RNZ].
        - (* [comment removed for export] *)
          clear PRd3. assert (LVe0 : rt_live RT Se = rt_live RT Sb) by (rewrite LVe, (LZd RZ); exact LDS1).
          clear LVe KL. rewrite RZ in *.
          hide POS6.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
        Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_pixDeserialize; 0x95bd0; 0x9f3dc; 0x9d968; 0x9eb78; 0xa2460; 0xa2d20; 0xa0ce4; 0x941e0].
        cwalk [e_pixDeserialize; 0x95bd0; 0x9f3dc; 0x9d968; 0x9eb78; 0xa2460; 0xa2d20; 0xa0ce4; 0x941e0].
        lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
        pose proof FSE as SHB12. split_at SHB12 12%nat SHB12b. split_at SHB12b 1%nat SHB12c. clear SHB12 SHB12c.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        unfold hid in POS6.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
          lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT Sx ?mm |- _ =>
            assert (KL : keeps_live (rt_live RT Sx) mm mc)
              by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
                  exact (live_outside_frame1 RT AF Sx mm fr usp (usp - 112) bb kk xx A ltac:(rewrite FRSe; left; reflexivity) SPLe Hb Hx)) end end.
        pose proof (pix_obj_keep _ _ _ pixs vs cvs (keeps_live_sub _ _ _ _ KL SUBe) POS6) as POS7. clear POS6 KL.
        pose proof DNULL as DN. unfold pixDestroy_null_cps in DN.
        eapply cps_seq.
        { eapply DN with (lo := lo) (pp := fr + 96); rt_side idtac.
          all: lazymatch goal with
               | |- optrL _ _ _ _ _ _ =>
                   unfold optrL; split;
                   [ right; exists fr, 1%nat; rewrite FRSe; change (fs_size 1) with 128;
                     split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                     split; [lia|]; split; [lia|];
                     replace (shad (fr + 96)) with (fr / 8 + 2147450892) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                     destruct SHB12b as [[_ B] _]; exact B
                   | let Q := fresh "Q" in pose proof FRSH as Q; unfold parked in Q; unfold SEGTOP_A;
                     repeat split; first [clear - FR0; lia | clear - FR64; Z.div_mod_to_equations; lia | clear - Q; lia | clear - FRSEG; lia] ]
               | |- rw_cells _ _ _ [C8 _] => exact P2E
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   unfold lres, TEMPLATE_COST, RASTER_COST, FRAMES_MAX, LIVE_MAX in *;
                   split; [rewrite FRSe, FR0; cbn [length]; lia| split; [rewrite LVe0; lia| split; [lia| exact LVPe]]]
               | |- ?g => idtac "LEFT:" g
               end. }
        clear SHB12b.
        after_call RT AF.
        lazymatch goal with AG : agree_on (fun a => aclient ?lv _ _ a /\ outside ?W a) ?ma ?mb |- _ =>
          assert (KL : keeps_live lv ma mb) by (apply (keeps_live_of_agree lv _ _ W ma mb AG); intros; exact I) end.
        lazymatch goal with H : rt_live RT ?Sx = rt_live RT Se |- _ => rewrite LVe0 in H; rewrite H in KL end.
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; apply SUB0b; exact He| solve [frames_sub_tac]| lia]| exact I]).
        pose proof (pix_obj_keep _ _ _ pixs vs cvs KL POS7) as POS8. clear POS7 KL.
          to_entry.
          eapply CONT2; try eassumption.
          all: lazymatch goal with
               | |- pix_obj _ _ _ _ _ => exact POS8
               | |- rt_live _ _ = _ => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity
               | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
               | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
               | |- _ <= rt_credit _ _ => unfold TEMPLATE_COST, RASTER_COST in *; lia
               | |- ?g => idtac "LEFT:" g
               end.
        - (* [comment removed for export] *)
          destruct PRd3 as [Z0|(POR & RDATA)]; [exfalso; exact (RNZ Z0)|].
          pose proof (obj_fresh_of_eq (rt_live RT Sd) (rt_live RT Sc) _ rr vr cr _ p1 v1 c1 (LDd RNZ) POR PO1b) as FRESH.
          pose proof (pix_obj_in_destroy (rt_live RT Sd) _ rr vr cr p1 v1 c1 POR FRESH) as PORe0. rewrite <- LVe in PORe0.
          pose proof (pix_obj_keep _ _ _ rr vr cr KL PORe0) as PORe. clear POR PORe0 FRESH KL.
          assert (LVf0 : live_destroy rr vr cr (rt_live RT Se) = rt_live RT Sb)
            by (rewrite LVe, live_destroy_comm, (LDd RNZ); exact LDS1).
          hide POS6. hide PORe. hide LVf0.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
        Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_pixDeserialize; 0x95bd0; 0x9f3dc; 0x9d968; 0x9eb78; 0xa2460; 0xa2d20; 0xa0ce4; 0x941e0].
        cwalk [e_pixDeserialize; 0x95bd0; 0x9f3dc; 0x9d968; 0x9eb78; 0xa2460; 0xa2d20; 0xa0ce4; 0x941e0].
        lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
        pose proof FSE as SHB12. split_at SHB12 12%nat SHB12b. split_at SHB12b 1%nat SHB12c. clear SHB12 SHB12c.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        unfold hid in POS6, PORe.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
          lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT Sx ?mm |- _ =>
            assert (KL : keeps_live (rt_live RT Sx) mm mc)
              by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
                  exact (live_outside_frame1 RT AF Sx mm fr usp (usp - 112) bb kk xx A ltac:(rewrite FRSe; left; reflexivity) SPLe Hb Hx)) end end.
        pose proof (pix_obj_keep _ _ _ pixs vs cvs (keeps_live_sub _ _ _ _ KL SUBe) POS6) as POS7. pose proof (pix_obj_keep _ _ _ rr vr cr KL PORe) as POR2. clear POS6 PORe KL.
        eapply cps_seq.
        { eapply DY with (lo := lo) (pp := fr + 96) (pix := rr) (v := vr) (cv := cr) (ras := [RA_TOP]); rt_side idtac.
          all: lazymatch goal with
               | |- optrL _ _ _ _ _ _ =>
                   unfold optrL; split;
                   [ right; exists fr, 1%nat; rewrite FRSe; change (fs_size 1) with 128;
                     split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                     split; [lia|]; split; [lia|];
                     replace (shad (fr + 96)) with (fr / 8 + 2147450892) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                     destruct SHB12b as [[_ B] _]; exact B
                   | let Q := fresh "Q" in pose proof FRSH as Q; unfold parked in Q; unfold SEGTOP_A;
                     repeat split; first [clear - FR0; lia | clear - FR64; Z.div_mod_to_equations; lia | clear - Q; lia | clear - FRSEG; lia] ]
               | |- rw_cells _ _ _ [C8 _] => exact P2E
               | |- pix_obj _ _ _ _ _ => exact POR2
               | |- uctx _ _ _ _ =>
                   unfold uctx; rewrite ?unsigned_lit by ul; unfold hid, parked in S0INV;
                   apply chain_ok_push with (fp1 := bv_unsigned s0);
                     [ lia | clear - SPA; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | unfold RA_TOP; lia | apply bv_unsigned_in_range
                     | rewrite Z_to_bv_bv_unsigned; rewrite <- RATOP; rewrite Z_to_bv_bv_unsigned; exact FRrec2
                     | cbn [chain_ok]; unfold link_invalid; lia ]
               | |- Forall _ DESTROY_FREE_RAS => rewrite ?unsigned_lit by ul; apply tr_destroy; unfold FUZZ_DESTROY_RAS; cbn [In]; tauto
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   unfold lres, TEMPLATE_COST, RASTER_COST, FRAMES_MAX, LIVE_MAX in *;
                   split; [rewrite FRSe, FR0; cbn [length]; lia| split; [lia| split; [lia| exact LVPe]]]
               | |- ?g => idtac "LEFT:" g
               end. }
        clear POR2 SHB12b.
        after_call RT AF.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ _) _ => rename Sx into Sf end.
        lazymatch goal with H : rt_live RT Sf = _ |- _ => rename H into LVf end.
        unfold hid in LVf0. rewrite LVf0 in LVf.
        assert (FRSf : rt_frames RT Sf = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
        lazymatch goal with AG : agree_on (fun a => aclient ?lv _ _ a /\ outside ?W a) ?ma ?mb, A : ART RT Sf ?mb |- _ =>
          assert (KL : keeps_live lv ma mb)
            by (apply (keeps_live_of_agree lv _ _ W ma mb AG); intros bb kk xx Hb Hx;
                exact (live_outside_local RT AF Sf mb fr 1%nat 96 bb kk xx A ltac:(rewrite FRSf; left; reflexivity) ltac:(lia) ltac:(change (fs_size 1) with 128; lia) Hb Hx)) end.
        rewrite LVf in KL.
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; rewrite LVf; apply SUB0b; exact He| solve [frames_sub_tac]| lia]|
                                        cbn [outside]; destruct (NFA _ Hx) as [N1 N2]; split; [lia| exact I]]).
        pose proof (pix_obj_keep _ _ _ pixs vs cvs KL POS7) as POS8. clear POS7 KL.
          to_entry.
          eapply CONT2; try eassumption.
          all: lazymatch goal with
               | |- pix_obj _ _ _ _ _ => exact POS8
               | |- rt_live _ _ = _ => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity
               | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
               | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
               | |- _ <= rt_credit _ _ => unfold TEMPLATE_COST, RASTER_COST in *; lia
               | |- ?g => idtac "LEFT:" g
               end.
      }
      lazymatch goal with FRx : rw_cells asegs _ (usp + -112) ?cs |- _ =>
        assert (CONT0 : forall (S : rts RT) (mE : mem) (jS j1 j2 : list byte)
                  (r1 r5 r6 r7 r9 r11 r12 r13 r14 r15 r16 r17 r20 r21 r22 r28 r29 r30 r31 : word) F' fc',
            ART RT S mE -> mem_inv asegs mE -> stk asegs mE lo (usp + -112) -> rw_cells asegs mE (usp + -112) cs ->
            rw_cells asegs mE fr [C8 (Z_to_bv 64 1102416563)] ->
            rw_cells asegs mE (fr + 32) [CB 8 jS] -> rw_cells asegs mE (fr + 64) [CB 8 j1] -> rw_cells asegs mE (fr + 96) [CB 8 j2] ->
            rw_cells asegs mE (fr / 8 + 2147450880) [C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-8)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-8)); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13))] ->
            LIBH mE -> io_ssp mE -> agree_on PF m mE -> pix_obj (rt_live RT Sb) mE pixs vs cvs ->
            rt_live RT S = rt_live RT Sb -> rt_frames RT S = (fr, 1%nat) :: rt_frames RT Σ -> rt_sp0 RT S = rt_sp0 RT Σ ->
            rt_credit RT Σ - (RASTER_COST + 65 + 0 * (TEMPLATE_COST + 2) + 0) <= rt_credit RT S ->
            cps asegs (ASTA RT S PMc (eq (entry_st r1 (Z_to_bv 64 (usp + -112)) gp (Z_to_bv 64 TP_A) r5 r6 r7 (Z_to_bv 64 usp) r9
                                          (Z_to_bv 64 pixs) r11 r12 r13 r14 r15 r16 r17 (Z_to_bv 64 fr) (Z_to_bv 64 (fr + 32)) r20 r21 r22 (Z_to_bv 64 (fr / 8 + 2147450880))
                                          (Z_to_bv 64 fr) s9 s10 s11 r28 r29 r30 r31 F' fc' 0x90aa8 mE))) QF) end.
      { intros S mE jjS jj1 jj2 r1 r5 r6 r7 r9 r11 r12 r13 r14 r15 r16 r17 r20 r21 r22 r28 r29 r30 r31 F' fc'
          ARTE MIE STE FRE FHE PSE P1E P2E FSE LHE SSPE AGE POSE ELV EFR ESP0 ECR.
        clear AGF. rename AGE into AGF.
        repeat match goal with H : rw_cells asegs _ _ _ |- _ => lazymatch H with FRE => fail | FHE => fail | PSE => fail | P1E => fail | P2E => fail | FSE => fail | _ => clear H end end.
        repeat match goal with H : ro_cells asegs _ _ _ |- _ => clear H end.
        repeat match goal with H : ART RT _ _ |- _ => lazymatch H with ARTE => fail | _ => clear H end end.
        repeat match goal with H : LIBH _ |- _ => lazymatch H with LHE => fail | _ => clear H end end.
        repeat match goal with H : io_ssp _ |- _ => lazymatch H with SSPE => fail | _ => clear H end end.
        repeat match goal with H : stk asegs _ _ _ |- _ => lazymatch H with STE => fail | _ => clear H end end.
        repeat match goal with H : mem_inv asegs _ |- _ => lazymatch H with MIE => fail | _ => clear H end end.
        repeat match goal with H : wmono asegs _ _ |- _ => clear H end.
        repeat match goal with H : munch _ _ _ |- _ => clear H end.
        repeat match goal with H : rt_frames RT _ = _ |- _ => lazymatch H with EFR => fail | FR0 => fail | _ => clear H end end.
        repeat match goal with H : rt_live RT _ = _ |- _ => lazymatch H with ELV => fail | _ => clear H end end.
        repeat match goal with H : rt_sp0 RT _ = _ |- _ => lazymatch H with ESP0 => fail | _ => clear H end end.
        repeat match goal with H : rt_credit RT _ = _ |- _ => clear H end.
        repeat match goal with H : rt_credit RT _ - _ <= _ |- _ => lazymatch H with ECR => fail | _ => clear H end end.
        clear_acc.
        pose proof FRE as FRrec. split_before FRrec (C8 s0) FRrec2. clear FRrec.
        assert (SPLE : rt_sp0 RT S - 8388608 <= usp - 112) by (rewrite ESP0; ul).
        hide POSE.
        unfold entry_st.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
        Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_pixDeserialize; 0x95bd0; 0x9f3dc; 0x9d968; 0x9eb78; 0xa2460; 0xa2d20; 0xa0ce4; 0x941e0].
        cwalk [e_pixDeserialize; 0x95bd0; 0x9f3dc; 0x9d968; 0x9eb78; 0xa2460; 0xa2d20; 0xa0ce4; 0x941e0].
        lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        unfold hid in POSE.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
          lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT Sx ?mm |- _ =>
            assert (KL : keeps_live (rt_live RT Sx) mm mc)
              by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
                  exact (live_outside_frame1 RT AF Sx mm fr usp (usp - 112) bb kk xx A ltac:(rewrite EFR; left; reflexivity) SPLE Hb Hx)) end end.
        rewrite ELV in KL. pose proof (pix_obj_keep _ _ _ pixs vs cvs KL POSE) as POS1. clear POSE KL.
        pose proof PCOPY as PC. unfold pixCopy_cps in PC.
        eapply cps_seq.
        { eapply PC with (lo := lo) (pixs := pixs) (vs := vs) (cvs := cvs); rt_side idtac.
          all: lazymatch goal with
               | |- pix_obj _ _ _ _ _ => rewrite ELV; exact POS1
               | |- p_data _ <> 0 => exact VDATA
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   unfold lres, TEMPLATE_COST, RASTER_COST, FRAMES_MAX, LIVE_MAX in *;
                   split; [rewrite EFR, FR0; cbn [length]; lia| split; [rewrite ELV; lia| split; [lia| rewrite ELV; exact LVPb]]]
               | |- ?g => idtac "LEFT:" g
               end. }
        after_call RT AF.
        lazymatch goal with AG : agree_on (fun a => aclient ?lv _ _ a /\ outside ?W a) ?ma ?mb |- _ =>
          assert (KL : keeps_live lv ma mb) by (apply (keeps_live_of_agree lv _ _ W ma mb AG); intros; exact I) end.
        rewrite ELV in KL.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ _) _ => rename Sx into Sc end.
        lazymatch goal with H : pix_obj (rt_live RT Sc) _ ?p ?vv ?cc |- _ => rename H into PO1; set (p1 := p) in *; set (v1 := vv) in *; set (c1 := cc) in * end.
        lazymatch goal with H : live_destroy p1 v1 c1 _ = _ |- _ => rename H into LDS1 end. rewrite ELV in LDS1.
        lazymatch goal with H : forall p n, In (p, n) (rt_live RT Sc) -> 0 < n |- _ => rename H into LVPc end.
        lazymatch goal with H : Z.of_nat (length (rt_live RT Sc)) <= _ |- _ => rename H into LVXc end. rewrite ELV in LVXc.
        lazymatch goal with H : p_data v1 <> 0 |- _ => rename H into V1DATA end.
        lazymatch goal with H : p_d v1 = p_d vs |- _ => rename H into VD1 end.
        assert (NZV1 : cmap_nz v1 c1).
        { lazymatch goal with LNC : p_cmap vs = 0 -> _, LCN : p_cmap vs <> 0 -> _ |- _ =>
            unfold cmap_nz in *; destruct (Z.eq_dec (p_cmap vs) 0) as [Z0|NZ];
            [ left; exact (proj1 (LNC Z0)) | right; rewrite (LCN NZ); destruct NZV as [Z1|N1]; [exfalso; exact (NZ Z1)| exact N1] ] end. }
        lazymatch goal with H : p_cmap vs <> 0 -> _ |- _ => clear H end.
        lazymatch goal with H : p_cmap vs = 0 -> _ |- _ => clear H end.
        assert (SUBc : forall e, In e (rt_live RT Sb) -> In e (rt_live RT Sc)) by (intros e He; rewrite <- LDS1 in He; exact (proj1 (live_destroy_In _ _ _ _ _ He))).
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; rewrite ELV; apply SUB0b; exact He| solve [frames_sub_tac]| lia]| exact I]).
        assert (FRSc : rt_frames RT Sc = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
        assert (SPLc : rt_sp0 RT Sc - 8388608 <= usp - 112) by (repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul).
        lazymatch goal with A : ART RT Sc ?mm |- _ =>
          assert (NCP1 : forall a, PF a -> a < p1 \/ p1 + 64 <= a)
            by (intros a [Ha _]; apply (inner_chunk_apart RT AF Sc mm p1 64 (rt_live RT Σ) (rt_frames RT Σ) usp a A (proj1 (pix_obj_entries _ _ _ _ _ PO1)));
                [ intros e He; pose proof (SUB0b e He) as Hb; rewrite <- LDS1 in Hb; destruct (live_destroy_In _ _ _ _ _ Hb) as (Q1 & Q2 & _); split; [exact Q1| exact Q2]
                | solve [frames_sub_tac] | repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul | exact Ha ]) end.
        (* [comment removed for export] *)
        pose proof (proj1 (pix_obj_entries _ _ _ _ _ PO1)) as P1IN.
        chunk_facts RT AF GP p1 64. fframe_chunk RT AF fr 1%nat 128 p1 64.
        pose proof (pix_obj_keep _ _ _ pixs vs cvs KL POS1) as POS2. clear POS1 KL.
        hide PO1. hide POS2.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
        Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_pixDeserialize; 0x95bd0; 0x9f3dc; 0x9d968; 0x9eb78; 0xa2460; 0xa2d20; 0xa0ce4; 0x941e0].
        cwalk [e_pixDeserialize; 0x95bd0; 0x9f3dc; 0x9d968; 0x9eb78; 0xa2460; 0xa2d20; 0xa0ce4; 0x941e0].
        lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        unfold hid in PO1, POS2.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
          lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT Sx ?mm |- _ =>
            assert (KL : keeps_live (rt_live RT Sx) mm mc)
              by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
                  exact (live_outside_frame1 RT AF Sx mm fr usp (usp - 112) bb kk xx A ltac:(rewrite FRSc; left; reflexivity) SPLc Hb Hx)) end end.
        pose proof (pix_obj_keep _ _ _ p1 v1 c1 KL PO1) as PO1b. pose proof (pix_obj_keep _ _ _ pixs vs cvs (keeps_live_sub _ _ _ _ KL SUBc) POS2) as POS3. clear PO1 POS2 KL.
        (* [comment removed for export] *)
        pose proof OP1 as GK. unfold pixDitherTo2bpp_cps, gq_op_cps in GK.
        eapply cps_seq.
        { eapply GK with (lo := lo) (pix := p1) (v := v1) (cv := c1) (ras := [RA_TOP]); rt_side idtac.
          all: lazymatch goal with
               | |- pix_obj _ _ _ _ _ => exact PO1b
               | |- p_data _ <> 0 => exact V1DATA
               | |- cmap_nz _ _ => exact NZV1
               | |- uctx _ _ _ _ =>
                   unfold uctx; rewrite ?unsigned_lit by ul; unfold hid, parked in S0INV;
                   apply chain_ok_push with (fp1 := bv_unsigned s0);
                     [ lia | clear - SPA; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | unfold RA_TOP; lia | apply bv_unsigned_in_range
                     | rewrite Z_to_bv_bv_unsigned; rewrite <- RATOP; rewrite Z_to_bv_bv_unsigned; exact FRrec2
                     | cbn [chain_ok]; unfold link_invalid; lia ]
               | |- bv_unsigned _ = _ => rewrite ?unsigned_lit by ul; reflexivity
               | |- _ = [RA_TOP] => reflexivity
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   rewrite VD1; fold k1; unfold lres, TEMPLATE_COST, RASTER_COST, FRAMES_MAX, LIVE_MAX in *;
                   split; [rewrite FRSc, FR0; cbn [length]; lia| split; [lia| split; [lia| exact LVPc]]]
               | |- wZ _ _ => reflexivity
               | |- True => exact I
               | |- _ /\ _ =>      (* [comment removed for export] *)
                   repeat split;
                   first [ reflexivity
                         | unfold freg_is, fa0, fa1;
                           first [ etransitivity; [apply freg_get_same; reflexivity| vm_compute; reflexivity]
                                 | rewrite freg_get_other by reflexivity; etransitivity; [apply freg_get_same; reflexivity| vm_compute; reflexivity] ] ]
               | |- ?g => idtac "LEFT:" g
               end. }
        after_call RT AF.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ _) _ => rename Sx into Sd end.
        lazymatch goal with H : pix_obj (rt_live RT Sd) _ p1 v1 c1 |- _ => rename H into PO1d end.
        lazymatch goal with H : ?r = 0 \/ (pix_obj (rt_live RT Sd) _ ?r ?vv ?cc /\ _) |- _ => rename H into PRd; set (rr := r) in *; set (vr := vv) in *; set (cr := cc) in * end.
        lazymatch goal with H : rr = 0 -> rt_live RT Sd = _ |- _ => rename H into LZd end.
        lazymatch goal with H : rr <> 0 -> live_destroy rr vr cr _ = _ |- _ => rename H into LDd end.
        lazymatch goal with H : forall p n, In (p, n) (rt_live RT Sd) -> 0 < n |- _ => rename H into LVPd end.
        lazymatch goal with H : Z.of_nat (length (rt_live RT Sd)) <= _ |- _ => rename H into LVXd end.
        lazymatch goal with H : rt_credit RT Sc - _ <= rt_credit RT Sd |- _ => rewrite VD1 in H; fold k1 in H end.
        assert (SUBd : forall e, In e (rt_live RT Sc) -> In e (rt_live RT Sd)).
        { intros e He. destruct (Z.eq_dec rr 0) as [Z0|NZ]; [rewrite (LZd Z0); exact He|]. rewrite <- (LDd NZ) in He. exact (live_destroy_sub _ _ _ _ _ He). }
        (* [comment removed for export] *)
        lazymatch goal with AG : agree_on (fun a => aclient (rt_live RT Sc) _ _ a /\ outside _ a) ?ma ?mb, A : ART RT Sc ?mx |- _ =>
          assert (KL : keeps_live (rt_live RT Sb) ma mb)
            by (apply (keeps_live_others RT AF Sc mx _ _ (rt_live RT Sb) p1 64 (p1 + 20) (p1 + 24) ma mb A
                         (proj1 (pix_obj_entries _ _ _ _ _ PO1b)) ltac:(lia) ltac:(lia)
                         ltac:(intros e He; split; [exact (SUBc e He)| rewrite <- LDS1 in He; exact (proj1 (proj2 (live_destroy_In _ _ _ _ _ He)))]) AG)) end.
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; apply SUBc; apply SUB0b; exact He| solve [frames_sub_tac]| lia]|
                                        cbn [outside]; pose proof (NCP1 _ Hx) as NCPx; split; [clear - NCPx; lia| exact I]]).
        assert (FRSd : rt_frames RT Sd = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
        assert (SPLd : rt_sp0 RT Sd - 8388608 <= usp - 112) by (repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul).
        pose proof (pix_obj_keep _ _ _ pixs vs cvs KL POS3) as POS4. clear POS3 KL.
        hide PO1b. hide PO1d. hide POS4. hide PRd. hide LZd. hide LDd.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
        Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_pixDeserialize; 0x95bd0; 0x9f3dc; 0x9d968; 0x9eb78; 0xa2460; 0xa2d20; 0xa0ce4; 0x941e0].
        cwalk [e_pixDeserialize; 0x95bd0; 0x9f3dc; 0x9d968; 0x9eb78; 0xa2460; 0xa2d20; 0xa0ce4; 0x941e0].
        lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
        pose proof FSE as SHB8. split_at SHB8 8%nat SHB8b. split_at SHB8b 1%nat SHB8c. clear SHB8 SHB8c.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        unfold hid in PO1d, POS4, PRd.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
          lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT Sx ?mm |- _ =>
            assert (KL : keeps_live (rt_live RT Sx) mm mc)
              by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
                  exact (live_outside_frame1 RT AF Sx mm fr usp (usp - 112) bb kk xx A ltac:(rewrite FRSd; left; reflexivity) SPLd Hb Hx)) end end.
        pose proof (pix_obj_keep _ _ _ p1 v1 c1 KL PO1d) as PO1e.
        pose proof (pix_obj_keep _ _ _ pixs vs cvs (keeps_live_sub _ _ _ _ KL (fun e He => SUBd e (SUBc e He))) POS4) as POS5.
        assert (PRd3 : rr = 0 \/ (pix_obj (rt_live RT Sd) _ rr vr cr /\ p_data vr <> 0))
          by (destruct PRd as [Z0|(PO & DN)]; [left; exact Z0| right; split; [exact (pix_obj_keep _ _ _ rr vr cr KL PO)| exact DN]]).
        clear PO1d POS4 PRd KL.
        pose proof DESTROY as DY. unfold pixDestroy_cps in DY.
        eapply cps_seq.
        { eapply DY with (lo := lo) (pp := fr + 64) (pix := p1) (v := v1) (cv := c1) (ras := [RA_TOP]); rt_side idtac.
          all: lazymatch goal with
               | |- optrL _ _ _ _ _ _ =>
                   unfold optrL; split;
                   [ right; exists fr, 1%nat; rewrite FRSd; change (fs_size 1) with 128;
                     split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                     split; [lia|]; split; [lia|];
                     replace (shad (fr + 64)) with (fr / 8 + 2147450888) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                     destruct SHB8b as [[_ B] _]; exact B
                   | let Q := fresh "Q" in pose proof FRSH as Q; unfold parked in Q; unfold SEGTOP_A;
                     repeat split; first [clear - FR0; lia | clear - FR64; Z.div_mod_to_equations; lia | clear - Q; lia | clear - FRSEG; lia] ]
               | |- rw_cells _ _ _ [C8 _] => exact P1E
               | |- pix_obj _ _ _ _ _ => exact PO1e
               | |- uctx _ _ _ _ =>
                   unfold uctx; rewrite ?unsigned_lit by ul; unfold hid, parked in S0INV;
                   apply chain_ok_push with (fp1 := bv_unsigned s0);
                     [ lia | clear - SPA; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | unfold RA_TOP; lia | apply bv_unsigned_in_range
                     | rewrite Z_to_bv_bv_unsigned; rewrite <- RATOP; rewrite Z_to_bv_bv_unsigned; exact FRrec2
                     | cbn [chain_ok]; unfold link_invalid; lia ]
               | |- Forall _ DESTROY_FREE_RAS => rewrite ?unsigned_lit by ul; apply tr_destroy; unfold FUZZ_DESTROY_RAS; cbn [In]; tauto
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   unfold lres, TEMPLATE_COST, RASTER_COST, FRAMES_MAX, LIVE_MAX in *;
                   split; [rewrite FRSd, FR0; cbn [length]; lia| split; [lia| split; [lia| exact LVPd]]]
               | |- ?g => idtac "LEFT:" g
               end. }
        clear SHB8b.
        after_call RT AF.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ _) _ => rename Sx into Se end.
        lazymatch goal with H : rt_live RT Se = _ |- _ => rename H into LVe end.
        assert (FRSe : rt_frames RT Se = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
        assert (SPLe : rt_sp0 RT Se - 8388608 <= usp - 112) by (repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul).
        assert (SUBe : forall e, In e (rt_live RT Sb) -> In e (rt_live RT Se))
          by (intros e He; rewrite LVe; rewrite <- LDS1 in He; exact (live_destroy_mono p1 v1 c1 _ _ SUBd e He)).
        lazymatch goal with AG : agree_on (fun a => aclient ?lv _ _ a /\ outside ?W a) ?ma ?mb, A : ART RT Se ?mb |- _ =>
          assert (KL : keeps_live lv ma mb)
            by (apply (keeps_live_of_agree lv _ _ W ma mb AG); intros bb kk xx Hb Hx;
                exact (live_outside_local RT AF Se mb fr 1%nat 64 bb kk xx A ltac:(rewrite FRSe; left; reflexivity) ltac:(lia) ltac:(change (fs_size 1) with 128; lia) Hb Hx)) end.
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; apply SUBe; apply SUB0b; exact He| solve [frames_sub_tac]| lia]|
                                        cbn [outside]; destruct (NFA _ Hx) as [N1 N2]; split; [lia| exact I]]).
        pose proof (pix_obj_keep _ _ _ pixs vs cvs (keeps_live_sub _ _ _ _ KL SUBe) POS5) as POS6.
        assert (LVPe : forall p n, In (p, n) (rt_live RT Se) -> 0 < n)
          by (intros p n H; rewrite LVe in H; exact (LVPd p n (live_destroy_sub _ _ _ _ _ H))).
        assert (LVXe : Z.of_nat (length (rt_live RT Se)) <= Z.of_nat (length (rt_live RT Sd)))
          by (rewrite LVe; pose proof (live_destroy_len p1 v1 c1 (rt_live RT Sd)); lia).
        unfold hid in LZd, LDd, PO1b.
        destruct (Z.eq_dec rr 0) as [RZ|RNZ].
        - (* [comment removed for export] *)
          clear PRd3. assert (LVe0 : rt_live RT Se = rt_live RT Sb) by (rewrite LVe, (LZd RZ); exact LDS1).
          clear LVe KL. rewrite RZ in *.
          hide POS6.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
        Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_pixDeserialize; 0x95bd0; 0x9f3dc; 0x9d968; 0x9eb78; 0xa2460; 0xa2d20; 0xa0ce4; 0x941e0].
        cwalk [e_pixDeserialize; 0x95bd0; 0x9f3dc; 0x9d968; 0x9eb78; 0xa2460; 0xa2d20; 0xa0ce4; 0x941e0].
        lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
        pose proof FSE as SHB12. split_at SHB12 12%nat SHB12b. split_at SHB12b 1%nat SHB12c. clear SHB12 SHB12c.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        unfold hid in POS6.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
          lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT Sx ?mm |- _ =>
            assert (KL : keeps_live (rt_live RT Sx) mm mc)
              by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
                  exact (live_outside_frame1 RT AF Sx mm fr usp (usp - 112) bb kk xx A ltac:(rewrite FRSe; left; reflexivity) SPLe Hb Hx)) end end.
        pose proof (pix_obj_keep _ _ _ pixs vs cvs (keeps_live_sub _ _ _ _ KL SUBe) POS6) as POS7. clear POS6 KL.
        pose proof DNULL as DN. unfold pixDestroy_null_cps in DN.
        eapply cps_seq.
        { eapply DN with (lo := lo) (pp := fr + 96); rt_side idtac.
          all: lazymatch goal with
               | |- optrL _ _ _ _ _ _ =>
                   unfold optrL; split;
                   [ right; exists fr, 1%nat; rewrite FRSe; change (fs_size 1) with 128;
                     split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                     split; [lia|]; split; [lia|];
                     replace (shad (fr + 96)) with (fr / 8 + 2147450892) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                     destruct SHB12b as [[_ B] _]; exact B
                   | let Q := fresh "Q" in pose proof FRSH as Q; unfold parked in Q; unfold SEGTOP_A;
                     repeat split; first [clear - FR0; lia | clear - FR64; Z.div_mod_to_equations; lia | clear - Q; lia | clear - FRSEG; lia] ]
               | |- rw_cells _ _ _ [C8 _] => exact P2E
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   unfold lres, TEMPLATE_COST, RASTER_COST, FRAMES_MAX, LIVE_MAX in *;
                   split; [rewrite FRSe, FR0; cbn [length]; lia| split; [rewrite LVe0; lia| split; [lia| exact LVPe]]]
               | |- ?g => idtac "LEFT:" g
               end. }
        clear SHB12b.
        after_call RT AF.
        lazymatch goal with AG : agree_on (fun a => aclient ?lv _ _ a /\ outside ?W a) ?ma ?mb |- _ =>
          assert (KL : keeps_live lv ma mb) by (apply (keeps_live_of_agree lv _ _ W ma mb AG); intros; exact I) end.
        lazymatch goal with H : rt_live RT ?Sx = rt_live RT Se |- _ => rewrite LVe0 in H; rewrite H in KL end.
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; apply SUB0b; exact He| solve [frames_sub_tac]| lia]| exact I]).
        pose proof (pix_obj_keep _ _ _ pixs vs cvs KL POS7) as POS8. clear POS7 KL.
          to_entry.
          eapply CONT1; try eassumption.
          all: lazymatch goal with
               | |- pix_obj _ _ _ _ _ => exact POS8
               | |- rt_live _ _ = _ => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity
               | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
               | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
               | |- _ <= rt_credit _ _ => unfold TEMPLATE_COST, RASTER_COST in *; lia
               | |- ?g => idtac "LEFT:" g
               end.
        - (* [comment removed for export] *)
          destruct PRd3 as [Z0|(POR & RDATA)]; [exfalso; exact (RNZ Z0)|].
          pose proof (obj_fresh_of_eq (rt_live RT Sd) (rt_live RT Sc) _ rr vr cr _ p1 v1 c1 (LDd RNZ) POR PO1b) as FRESH.
          pose proof (pix_obj_in_destroy (rt_live RT Sd) _ rr vr cr p1 v1 c1 POR FRESH) as PORe0. rewrite <- LVe in PORe0.
          pose proof (pix_obj_keep _ _ _ rr vr cr KL PORe0) as PORe. clear POR PORe0 FRESH KL.
          assert (LVf0 : live_destroy rr vr cr (rt_live RT Se) = rt_live RT Sb)
            by (rewrite LVe, live_destroy_comm, (LDd RNZ); exact LDS1).
          hide POS6. hide PORe. hide LVf0.
        refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
        Time walk_to AF MST [(usp - 112, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_pixDeserialize; 0x95bd0; 0x9f3dc; 0x9d968; 0x9eb78; 0xa2460; 0xa2d20; 0xa0ce4; 0x941e0].
        cwalk [e_pixDeserialize; 0x95bd0; 0x9f3dc; 0x9d968; 0x9eb78; 0xa2460; 0xa2d20; 0xa0ce4; 0x941e0].
        lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.
        pose proof FSE as SHB12. split_at SHB12 12%nat SHB12b. split_at SHB12b 1%nat SHB12c. clear SHB12 SHB12c.
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
        unfold hid in POS6, PORe.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
          lazymatch goal with MUx : munch ?W ?mm mc, A : ART RT Sx ?mm |- _ =>
            assert (KL : keeps_live (rt_live RT Sx) mm mc)
              by (apply (keeps_live_of_munch _ W mm mc MUx); intros bb kk xx Hb Hx;
                  exact (live_outside_frame1 RT AF Sx mm fr usp (usp - 112) bb kk xx A ltac:(rewrite FRSe; left; reflexivity) SPLe Hb Hx)) end end.
        pose proof (pix_obj_keep _ _ _ pixs vs cvs (keeps_live_sub _ _ _ _ KL SUBe) POS6) as POS7. pose proof (pix_obj_keep _ _ _ rr vr cr KL PORe) as POR2. clear POS6 PORe KL.
        eapply cps_seq.
        { eapply DY with (lo := lo) (pp := fr + 96) (pix := rr) (v := vr) (cv := cr) (ras := [RA_TOP]); rt_side idtac.
          all: lazymatch goal with
               | |- optrL _ _ _ _ _ _ =>
                   unfold optrL; split;
                   [ right; exists fr, 1%nat; rewrite FRSe; change (fs_size 1) with 128;
                     split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
                     split; [lia|]; split; [lia|];
                     replace (shad (fr + 96)) with (fr / 8 + 2147450892) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                     destruct SHB12b as [[_ B] _]; exact B
                   | let Q := fresh "Q" in pose proof FRSH as Q; unfold parked in Q; unfold SEGTOP_A;
                     repeat split; first [clear - FR0; lia | clear - FR64; Z.div_mod_to_equations; lia | clear - Q; lia | clear - FRSEG; lia] ]
               | |- rw_cells _ _ _ [C8 _] => exact P2E
               | |- pix_obj _ _ _ _ _ => exact POR2
               | |- uctx _ _ _ _ =>
                   unfold uctx; rewrite ?unsigned_lit by ul; unfold hid, parked in S0INV;
                   apply chain_ok_push with (fp1 := bv_unsigned s0);
                     [ lia | clear - SPA; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | unfold RA_TOP; lia | apply bv_unsigned_in_range
                     | rewrite Z_to_bv_bv_unsigned; rewrite <- RATOP; rewrite Z_to_bv_bv_unsigned; exact FRrec2
                     | cbn [chain_ok]; unfold link_invalid; lia ]
               | |- Forall _ DESTROY_FREE_RAS => rewrite ?unsigned_lit by ul; apply tr_destroy; unfold FUZZ_DESTROY_RAS; cbn [In]; tauto
               | |- lenv _ _ _ _ _ _ => lenv_tac
               | |- lres _ _ _ _ _ =>
                   unfold lres, TEMPLATE_COST, RASTER_COST, FRAMES_MAX, LIVE_MAX in *;
                   split; [rewrite FRSe, FR0; cbn [length]; lia| split; [lia| split; [lia| exact LVPe]]]
               | |- ?g => idtac "LEFT:" g
               end. }
        clear POR2 SHB12b.
        after_call RT AF.
        lazymatch goal with |- cps _ (ASTA RT ?Sx _ _) _ => rename Sx into Sf end.
        lazymatch goal with H : rt_live RT Sf = _ |- _ => rename H into LVf end.
        unfold hid in LVf0. rewrite LVf0 in LVf.
        assert (FRSf : rt_frames RT Sf = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity).
        lazymatch goal with AG : agree_on (fun a => aclient ?lv _ _ a /\ outside ?W a) ?ma ?mb, A : ART RT Sf ?mb |- _ =>
          assert (KL : keeps_live lv ma mb)
            by (apply (keeps_live_of_agree lv _ _ W ma mb AG); intros bb kk xx Hb Hx;
                exact (live_outside_local RT AF Sf mb fr 1%nat 96 bb kk xx A ltac:(rewrite FRSf; left; reflexivity) ltac:(lia) ltac:(change (fs_size 1) with 128; lia) Hb Hx)) end.
        rewrite LVf in KL.
        fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; rewrite LVf; apply SUB0b; exact He| solve [frames_sub_tac]| lia]|
                                        cbn [outside]; destruct (NFA _ Hx) as [N1 N2]; split; [lia| exact I]]).
        pose proof (pix_obj_keep _ _ _ pixs vs cvs KL POS7) as POS8. clear POS7 KL.
          to_entry.
          eapply CONT1; try eassumption.
          all: lazymatch goal with
               | |- pix_obj _ _ _ _ _ => exact POS8
               | |- rt_live _ _ = _ => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity
               | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
               | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
               | |- _ <= rt_credit _ _ => unfold TEMPLATE_COST, RASTER_COST in *; lia
               | |- ?g => idtac "LEFT:" g
               end.
      }
      unfold hid in POBJ.
      to_entry.
      eapply CONT0; try eassumption.
      all: lazymatch goal with
           | |- pix_obj _ _ _ _ _ => exact POBJ
           | |- rt_live _ _ = _ => reflexivity
           | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
           | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
           | |- _ <= rt_credit _ _ => unfold TEMPLATE_COST, RASTER_COST in *; repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H in * end; lia
           | |- ?g => idtac "LEFT:" g
           end.
Qed.
End FZ.
