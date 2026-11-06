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
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import Tac RzCPS NodesA SysStep Arr StoreFast.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import ImageA Layout RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit D_iface D_defs
  Lept_iface Lept_lits Lept_litmem Lept_env LeptC_kit Lept_leaf LeptC_leaf LeptL_kit Lept_objkit Lept_chain Lept_gmax_defs Gq_iface Gq_opcase Gq_clone Gq_band_loop.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import Lept_fuzzkit Lept_deserkit LeptC_leaf Gm_kit Gm_livekit Gm_livekit2 Gm_leaf LeptB_guard LeptB_guard2.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import Gq_band_exit.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
(* [comment removed for export] *)
Ltac subfp_tac ::= clear; let z := fresh "z" in let Hz := fresh "Hz" in intros z Hz; cbn [outside] in Hz |- *; cbn [outside]; lia.
Lemma EVQ_exit : forall (P : machine_state -> Prop) ms ms', evt asegs P ms' -> ms' = ms -> evt asegs P ms.
Proof. intros P ms ms' H E. subst. exact H. Qed.
(* [comment removed for export] *)
Ltac forget_junk H :=
  repeat match type of H with context [CB _ ?bs] =>
    lazymatch bs with
    | firstn _ _ => let j := fresh "jq" in set (j := bs) in *; clearbody j
    | skipn _ _ => let j := fresh "jq" in set (j := bs) in *; clearbody j
    end end.
Ltac forget_junk_in A := repeat match goal with H : rw_cells _ _ A ?cs |- _ =>
    lazymatch cs with context [CB _ (firstn _ _)] => forget_junk H | context [CB _ (skipn _ _)] => forget_junk H end end.
(* [comment removed for export] *)
Ltac diet_chains := repeat match goal with H : wmono _ _ ?b |- _ => lazymatch goal with |- context [b] => fail | _ => clear H end end;
                    repeat match goal with H : munch _ _ ?b |- _ => lazymatch goal with |- context [b] => fail | _ => clear H end end.
(* [comment removed for export] *)
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

Section BANDC.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis RERR : returnError_cps RT e_returnErrorPtr.
Hypothesis PCS : pixCreate_sure_cps RT.
Hypothesis PCR : pixCopyResolution_cps RT.
Hypothesis PCI : pixCopyInputFormat_cps RT.
Hypothesis PDR : pixDestroy_rc_cps RT.

Local Ltac eqv :=
  repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end;
  repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end;
  repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity.

(* [comment removed for export] *)
Local Ltac join_cells H1 H2 :=
  lazymatch type of H1 with rw_cells _ ?m ?A ?cs1 =>
  lazymatch type of H2 with rw_cells _ ?m ?B ?cs2 =>
    let J := fresh "J" in
    assert (J : rw_cells asegs m A (cs1 ++ cs2))
      by (apply (proj2 (rw_cells_app m A cs1 cs2)); split;
          [ exact H1
          | cbn [cells_size csize Nat.add]; lazymatch goal with |- rw_cells _ _ ?X _ => replace X with B by lia end; exact H2 ]);
    clear H1 H2; cbn [app] in J; rename J into H1 end end.

Lemma band_c0 : gq_op_case RT 0 e_pixGenerateMaskByBand RA_FUZZ_OP3 7 4 2 BAND_COST
    (fun a1 a2 a3 a4 _ _ => wZ a1 1 /\ wZ a2 2 /\ wZ a3 1 /\ wZ a4 1).
Proof using AF GP RERR PCS PCR PCI PDR.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pix v cv ras
    FDO MST -> -> (A1 & A2 & A3 & A4) POBJ VDATA CNZ UC RAF RAS ENV RES AL.
  unfold wZ in A1, A2, A3, A4. subst a1 a2 a3 a4.
  unfold lpost_f, lpost, lenv, keeps, keepsL, lres in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct RES as (FRB & LVB & CRB & LVP).
  pose proof POBJ as (PXC & (PIN & PX0 & PX16 & _) & (HD1 & HW1 & HH1 & HWPL & HRS) & PDATA & _).
  destruct PDATA as [DZ|((DIN & D0 & D16 & DSZ) & DNE)]; [contradiction|].
  unfold BAND_COST, OP_COST, MSG_COST in *.
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_pixGenerateMaskByBand, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STDERR_STACK in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  chunk_facts RT AF GP pix 64.
  chunk_facts RT AF GP (p_data v) (rsize v).
  unfold pix_cells in PXC.
  assert (PML : forall q k a, In (q, k) (rt_live RT Σ) -> q <= a < q + k -> PF a).
  { intros q k a Hq Ha. right; right; left; exists q, k; split; [exact Hq| lia]. }
  hide POBJ.
  carve_frame 192%nat ST.
  try forget_junk_in (usp + -192). try diet_chains.
  walk_to AF MST [(usp - 192, usp)] [e_stack_malloc 1%nat].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
  eapply cps_seq.
  { pose proof (gp_stack_malloc_1 RT GP) as SM2; unfold stack_malloc_contract' in SM2; eapply SM2 with (lo := lo); rt_side idtac.
  all: try (clear - CRB; destruct (is_d248 (p_d v)); unfold RASTER_COST in CRB; lia).
  }
  after_call RT AF.
  fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
  fframe_open RT AF PF (rt_live RT Σ) usp 1%nat 128 ltac:(fun Ha => exact Ha).
  fframe_chunk RT AF fr 1%nat 128 pix 64.
  fframe_chunk RT AF fr 1%nat 128 (p_data v) (4 * (p_wpl v * p_h v)).
  refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
  idtac "MARK frame open".
  try forget_junk_in (usp + -192). try forget_junk_in fr. try forget_junk_in (fr / 8 + 2147450880). try diet_chains.
  walk_to AF MST [(usp - 192, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x9ecb0].
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
  lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                         repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *.
  local_acc FSH fr 4%nat 32 FR64 FR1 ACCW. local_acc FSH fr 6%nat 48 FR64 FR1 ACCH. local_acc FSH fr 8%nat 64 FR64 FR1 ACCD.
  park_disj.
  (* [comment removed for export] *)
  try forget_junk_in (usp + -192). try forget_junk_in fr. try forget_junk_in (fr / 8 + 2147450880). try diet_chains.
  walk_to AF MST [(usp - 256, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x9ecdc; 0x9ed7c; e_stack_malloc 1%nat].
  (* [comment removed for export] *)
  assert (DR : 1 <= p_d v <= 32) by (clear - HD1; cbn [In] in HD1; lia).
  rewrite !(sx32_small (p_d v)) by lia.
  destruct (is_d248 (p_d v)) eqn:D248.
  all: cycle 1.
  (* [comment removed for export] *)
  cut2f 0x9ed7c (Z_to_bv 5 10) (Z_to_bv 5 11) (fun _ _ : word => True).
  { clear - HD1 D248. cbn [In] in HD1.
    destruct HD1 as [E|[E|[E|[E|[E|[E|[E|[]]]]]]]]; rewrite <- E in *; cbn in D248; try discriminate D248.
    all: try (lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let b := eval vm_compute in c in change c with b; cbv iota end).
    all: awalk [0x9ed7c; 0x9ecdc].
    all: cut2f_done ltac:(exact I). }
  clear HP.
  awalk [e_returnErrorPtr].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                  repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  assert (CR4 : 4 <= rt_credit RT Σ) by (clear - CRB D248; try rewrite D248 in CRB; exact CRB).
  pose proof RERR as RE. unfold returnError_cps in RE.
  eapply cps_seq.
  { eapply RE with (lo := lo); rt_side idtac.
  1: lit_in_fast.
  1: lit_in_fast.
  lenv_tac.
  }
  after_call RT AF.
  fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]).
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
  try forget_junk_in (usp + -192). try forget_junk_in fr. try forget_junk_in (fr / 8 + 2147450880). try diet_chains.
  (* [comment removed for export] *)
  Time walk_to AF MST [(usp - 256, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x9eef0].
  idtac "MARK at pokes".
  try unfold hid in FRM. try unfold hid in FSH. split_at FRM 1%nat FRMr.
  Time (eapply evt_cut;
  [ eapply EVQ_exit;
    [ eapply band_exit_x1; [exact FR0| exact FR64| clear - FRHI SP0R1; lia| exact FRM| exact FSH| reflexivity| assumption]
    | cbn [mkR]; repeat first [ lazymatch goal with |- @eq Z _ _ => clear; lia end | progress f_equal | reflexivity ] ]
  | ]).
  clear FRM FSH. intros ms' PO. destruct PO as (mx & -> & MUx & WMx & MIx & FRM & FSH). unfold band_exit_W, SHB in MUx. unfold band_sh_f5 in FSH.
  idtac "MARK pokes applied".
  Time (lazymatch goal with A : ART RT ?Sx _ |- _ => loop_art RT AF Sx mx lo MUx ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]) end).
  Time (lazymatch type of MUx with munch _ ?ma ?mb =>
    loop_transport ma mb MUx ltac:(fun Hx => cbn [outside]; unfold shad, SHB in *;
        first [ first [pose proof FRSEG as XFRSEG | pose proof I as XFRSEG]; first [pose proof SP0W as XSP0W | pose proof I as XSP0W]; first [pose proof FRSH as XFRSH | pose proof I as XFRSH];
                clear - Hx FRHI LOW LOR FR64 FR0 SP0R1 SP0R0 XFRSEG XSP0W XFRSH;
                unfold parked, hid in *; unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *; repeat split; try exact I; solve [first [lia | Z.div_mod_to_equations; lia]]
              | repeat split; try exact I; notin_side ]) end).
  join_cells FRM FRMr.
  frame_release RT AF GP MST Σ fr 1%nat 128 PF AGF PFS usp lo 0x9ef60
        ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
        ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *; repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  try forget_junk_in (usp + -192). try forget_junk_in fr. try forget_junk_in (fr / 8 + 2147450880). try diet_chains.
  walk_to AF MST [(usp - 256, usp)] (@nil Z).
  cps_stop.
  apply cps_finish; intros c Hc; subst QF; cbv beta.
  lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S, 0, v, cv end.
  split.
  2: {
  split; [intros _; eqv|].
  split; [intros N; exfalso; apply N; reflexivity|].
  split; [repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact LVP|].
  split; [repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; lia|].
  split; [eqv|]. split; [eqv|].
  try rewrite D248. repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H in * end. lia.
  }
  eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists.
  split; [unfold ret_st; rewrite ?ESP; do 16 eexists; reflexivity|].
  split; [unfold rt_after_f; split; [split; [assumption| split; assumption]| split; assumption]|].
  split; [intros a Ha _; exact (AGF a Ha)|].
  split.
  { lazymatch goal with |- pix_obj (rt_live RT ?S) ?mc _ _ _ =>
      assert (KL0 : keeps_live (rt_live RT Σ) m mc) by (intros b kk Hb a Ha; apply AGF; exact (PML b kk _ Hb Ha));
      replace (rt_live RT S) with (rt_live RT Σ) by (symmetry; eqv);
      unfold hid in POBJ; exact (pix_obj_keep _ m mc pix v cv KL0 POBJ) end.
  }
  left; reflexivity.
  (* [comment removed for export] *)
  idtac "MARK live arm".
  (* [comment removed for export] *)
  cut2f 0x9ecdc (Z_to_bv 5 10) (Z_to_bv 5 11) (fun _ _ : word => True).
  { clear - HD1 D248. cbn [In] in HD1.
    destruct HD1 as [E|[E|[E|[E|[E|[E|[E|[]]]]]]]]; rewrite <- E in *; cbn in D248; try discriminate D248.
    all: try (lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let b := eval vm_compute in c in change c with b; cbv iota end).
    all: awalk [0x9ed7c; 0x9ecdc].
    all: cut2f_done ltac:(exact I). }
  clear HP.
  assert (D248R : p_d v = 2 \/ p_d v = 4 \/ p_d v = 8) by (clear - D248; unfold is_d248 in D248; lia).
  (* [comment removed for export] *)
  awalk [e_pixClone; 0x9ed44; 0x9edb4].
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
  lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                         repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
  set (PF1 := fun a => PF a /\ outside [(pix + 20, pix + 24)] a).
  lazymatch type of AGF with agree_on _ _ ?mm =>
    assert (AGF1 : agree_on PF1 m mm) by (eapply agree_sub; [exact AGF| intros zz [Hz _]; exact Hz]) end.
  clear AGF. rename AGF1 into AGF.
  assert (PFS1 : forall a, PF1 a -> usp <= a \/ a < lo) by (intros a [Ha _]; exact (PFS a Ha)).
  assert (NFA1 : forall a, PF1 a -> (a < fr \/ fr + 128 <= a) /\ (a < shad fr \/ shad (fr + 128) <= a)) by (intros a [Ha _]; exact (NFA a Ha)).
  assert (PFO : forall a, PF1 a -> a < pix + 20 \/ pix + 24 <= a) by (intros a [_ Ho]; cbn [outside] in Ho; lia).
  refresh RT AF. unfold shad, SHB in *.
  try forget_junk_in (usp + -192). try forget_junk_in fr. try forget_junk_in (fr / 8 + 2147450880). try diet_chains.
  walk_to AF MST [(usp + -192 - 16, usp + -192); (pix + 20, pix + 24)] [e_pixClone].   (* [comment removed for export] *)
  eapply evt_cut.
  { lazymatch goal with MIx : mem_inv asegs ?mm, STx : stk asegs ?mm lo (usp + -192), ACx : acc asegs ?mm pix 64,
                       G1x : ro_cells asegs ?mm 965088 _, G2x : ro_cells asegs ?mm 1013304 _, PXx : rw_cells asegs ?mm pix _
        |- evt _ _ (MS _ ?F0 _ ?fc0 None ?mm _) =>
      epose proof (pixClone_evt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F0 fc0 mm (usp + -192) lo pix v 1
                     PXx ACx ltac:(lia) PX0 PX16 G1x G2x STx ltac:(lia) ltac:(lia) ltac:(lia) ltac:(clear - CKR LOW; lia)
                     ltac:(clear - CKH; unfold parked in CKH; lia) ltac:(clear - CKS; unfold parked, SEGTOP_A in *; lia) MIx) as ZR end.
    unfold e_pixClone in ZR. exact ZR. }
  intros ms' PO. unfold pixClone_post in PO.
  destruct PO as (a1q & a2q & a3q & mq & -> & MUl & WMl & MIl & STl & PXC2).
  idtac "MARK clone applied".
  (* [comment removed for export] *)
  assert (FCS' : pix + 64 <= fr / 8 + 2147450880 \/ fr / 8 + 2147450880 + 16 <= pix)
    by (clear - FCS; unfold parked in FCS; Z.div_mod_to_equations; lia).
  lazymatch type of MUl with munch _ ?ma ?mb =>
      lazymatch goal with A : ART RT ?S ma |- _ =>
        loop_art RT AF S mb lo MUl ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists pix, 64; split; [solve [in_live_tac]| lia]| exact I]]) end end.
  lazymatch type of MUl with munch _ ?ma _ =>
    repeat match goal with H : rw_cells asegs ma pix _ |- _ => clear H end; repeat match goal with H : stk asegs ma _ _ |- _ => clear H end end.
  lazymatch type of MUl with munch _ ?ma ?mb =>
      loop_transport ma mb MUl ltac:(fun Hx => clear - Hx CKR CKS CKH FCD FCS' FRSH FRHI FR0 FRSEG FR64 LOW LOR SPT SPB STa SP0W SP0R0 SP0R1 PX0; unfold parked in *; first [lia | Z.div_mod_to_equations; lia]) end.
  fix_ret_pc.
  unfold pix_cells_rc in PXC2. change (1 + 1) with 2 in PXC2.
  idtac "MARK clone transported".
  (* [comment removed for export] *)
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists pix, 64; split; [solve [in_live_tac]| lia]| exact I]]).
  lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS1 _ Hx) as PFSx; pose proof (PFO _ Hx) as PFOx; clear - PFSx PFOx LOR; repeat split; try exact I; lia) end.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *.
  local_acc FSH fr 4%nat 32 FR64 FR1 ACCW. local_acc FSH fr 6%nat 48 FR64 FR1 ACCH. local_acc FSH fr 8%nat 64 FR64 FR1 ACCD.
  park_disj.
  (* [comment removed for export] *)
  try forget_junk_in (usp + -192). try forget_junk_in fr. try forget_junk_in (fr / 8 + 2147450880). try diet_chains.
  walk_to AF MST [(usp - 256, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_pixCreate; 0x9edf8; 0x9ee4c; 0x9eea0].
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  assert (PSRC : forall (lv : list (Z * Z)) (rc : Z) (mc : mem), (forall e, In e (rt_live RT Σ) -> In e lv) -> agree_on PF1 m mc ->
            rw_cells asegs mc pix (pix_cells_rc v rc) -> pix_obj_rc lv mc pix v cv rc).
  { intros lv rc mc SUB AG PX. unfold hid in POBJ. destruct POBJ as (_ & PCH & HOK & PDATA & PCMAP).
    split; [exact PX|]. split; [exact (chunk_mono _ _ _ _ SUB PCH)|]. split; [exact HOK|].
    split; [destruct PDATA as [Z0|(DCH & DN)]; [left; exact Z0| right; split; [exact (chunk_mono _ _ _ _ SUB DCH)| exact DN]]|].
    destruct PCMAP as [Z0|(CO & NN)]; [left; exact Z0| right]. split; [| exact NN].
    apply (cmap_obj_mono _ _ mc _ cv SUB).
    pose proof CO as (_ & (CI & C0 & _) & _).
    apply (cmap_obj_agree (rt_live RT Σ) PF1 m mc (p_cmap v) cv CO AG). intros a Ha.
    pose proof (live_apart2 RT AF Σ m (p_cmap v) 24 pix 64 ART0 CI PIN ltac:(intros E; inversion E; destruct NN as (N1 & _); exact (N1 ltac:(assumption)))) as DJ.
    split; [right; right; left; exists (p_cmap v), 24; split; [exact CI| exact Ha]| cbn [outside]; split; [clear - DJ Ha; lia| exact I]]. }
  (* [comment removed for export] *)
  rewrite !(sx32_small (p_w v)) by lia. rewrite !(sx32_small (p_h v)) by lia.
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
  ltac:(fun Hx => cbn [outside]; pose proof (PFS1 _ Hx); destruct (NFA1 _ Hx) as [N1 N2]; unfold shad, SHB in *;
  repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  assert (WR : 0 < p_w v <= 20000) by lia. assert (HR : 0 < p_h v <= 20000) by lia.
  assert (HAO : hdr_args_ok (p_w v) (p_h v) 1) by (unfold hdr_args_ok; split; [cbn [In]; tauto|]; split; [exact WR|]; split; [exact HR|]; clear - WR HR; split; [| assert ((p_w v * 1 + 31) / 32 <= 626) by (Z.div_mod_to_equations; lia); nia]; assert (1 <= (p_w v * 1 + 31) / 32) by (Z.div_mod_to_equations; lia); nia).
  assert (CRD : RASTER_COST + 64 <= rt_credit RT Σ) by (clear - CRB; lia).
  eapply cps_seq.
  {
  eapply PCS with (lo := lo) (w := p_w v) (h := p_h v) (d := 1).
    - exact FDO.
    - exact MST.
    - reflexivity.
    - split; [lia| reflexivity].
    - split; [lia| reflexivity].
    - split; [lia| reflexivity].
    - exact HAO.
    - lenv_tac.
    - unfold lres; repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; cbn [length]; unfold FRAMES_MAX, LIVE_MAX in *; repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H in * end; repeat split; [lia| lia| lia| exact LVP].
  }
  idtac "MARK pixCreate applied".
  (* [comment removed for export] *)
  after_call RT AF.
  (* [comment removed for export] *)
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]| exact I]).
  (* [comment removed for export] *)
  lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σc; rename A into ARTC end.
  lazymatch goal with H : pix_obj (rt_live RT Σc) _ ?p ?vv _ |- _ => rename H into POD; rename p into pixd; rename vv into v1 end.
  lazymatch goal with H : rt_live RT Σc = _ |- _ => rename H into LVN end.
  lazymatch goal with H : p_w v1 = _ |- _ => rename H into VW end.
  lazymatch goal with H : p_h v1 = _ |- _ => rename H into VH end.
  lazymatch goal with H : p_d v1 = _ |- _ => rename H into VD end.
  lazymatch goal with H : p_data v1 <> 0 |- _ => rename H into VDATA1 end.
  lazymatch goal with H : p_cmap v1 = 0 |- _ => rename H into VCMAP end.
  assert (FRSc : rt_frames RT Σc = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σc = _ |- _ => rewrite E end; exact FRS).
  assert (LVC : rt_live RT Σc = (p_data v1, rsize v1) :: (pixd, 64) :: rt_live RT Σ) by (rewrite LVN; repeat match goal with E : rt_live _ _ = rt_live RT Σ |- _ => rewrite E end; reflexivity).
  assert (SP0C : rt_sp0 RT Σc = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; reflexivity).
  assert (CRC : rt_credit RT Σ - (RASTER_COST + 9) <= rt_credit RT Σc) by (repeat match goal with E : rt_credit _ _ = _ |- _ => rewrite E in * end; lia).
  pose proof POD as (PXD & (PDIN & PD0 & PD16 & _) & HOKD & PDDATA & _).
  destruct PDDATA as [PDZ|((DDIN & DD0 & DD16 & DDN) & DDNE)]; [exfalso; exact (VDATA1 PDZ)|].
  set (dat := p_data v1) in *. set (rs := rsize v1) in *.
  assert (SUBP : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σc) /\ fst e <> pixd)
    by (intros e He; split; [rewrite LVC; right; right; exact He|];
        apply (fresh_chunk_ne RT AF Σc _ [(dat, rs)] pixd 64 _ e ARTC LVC); [ cbn [app]; right; exact He | lia | destruct e as [eq ek]; exact (LVP eq ek He) ]).
  assert (SUBD : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σc) /\ fst e <> dat)
    by (intros e He; split; [rewrite LVC; right; right; exact He|];
        apply (fresh_chunk_ne RT AF Σc _ [] dat rs _ e ARTC LVC); [ cbn [app]; right; exact He | lia | destruct e as [eq ek]; exact (LVP eq ek He) ]).
  assert (NCP : forall a, PF a -> a < pixd \/ pixd + 64 <= a)
    by (intros a Ha; apply (inner_chunk_apart RT AF Σc _ pixd 64 (rt_live RT Σ) (rt_frames RT Σ) usp a ARTC PDIN SUBP);
        [ rewrite FRSc; intros e He; right; exact He | rewrite SP0C; ul | exact Ha ]).
  assert (NCD : forall a, PF a -> a < dat \/ dat + rs <= a)
    by (intros a Ha; apply (inner_chunk_apart RT AF Σc _ dat rs (rt_live RT Σ) (rt_frames RT Σ) usp a ARTC DDIN SUBD);
        [ rewrite FRSc; intros e He; right; exact He | rewrite SP0C; ul | exact Ha ]).
  assert (NPS : pix <> pixd) by (exact (proj2 (SUBP (pix, 64) PIN))).
  assert (NDS : pix <> dat) by (exact (proj2 (SUBD (pix, 64) PIN))).
  assert (NSP : p_data v <> pixd) by (exact (proj2 (SUBP (p_data v, 4 * (p_wpl v * p_h v)) DIN))).
  assert (NSD : p_data v <> dat) by (exact (proj2 (SUBD (p_data v, 4 * (p_wpl v * p_h v)) DIN))).
  idtac "MARK names".
  (* [comment removed for export] *)
  chunk_facts RT AF GP pixd 64. chunk_facts RT AF GP dat rs.
  fframe_chunk RT AF fr 1%nat 128 pixd 64. fframe_chunk RT AF fr 1%nat 128 dat rs.
  unfold pix_cells in PXD. rewrite VW, VH, VD, VCMAP in PXD. fold dat in PXD.
  assert (EWD : p_wpl v1 = (p_w v + 31) / 32) by (destruct HOKD as (_ & _ & _ & Q4 & _); rewrite VW, VD in Q4; rewrite Q4; f_equal; lia).
  assert (ERS : rs = 4 * (p_wpl v1 * p_h v)) by (unfold rs, rsize; rewrite VH; reflexivity).
  assert (RSD : 0 < 4 * (p_wpl v1 * p_h v) <= 67108864) by (destruct HOKD as (_ & _ & _ & _ & Q5); rewrite VH in Q5; exact Q5).
  hide POD. hide SUBP. hide SUBD. hide HOKD.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
  idtac "MARK before walk to PCR".
  (* [comment removed for export] *)
  try forget_junk_in (usp + -192). try forget_junk_in fr. try forget_junk_in (fr / 8 + 2147450880). try diet_chains.
  walk_to AF MST [(usp - 256, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_pixCopyResolution].
  (* [comment removed for export] *)
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS1 _ Hx); destruct (NFA1 _ Hx) as [N1 N2]; unfold shad, SHB in *;
                        repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  assert (LSUB : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σc)) by (intros e He; rewrite LVC; right; right; exact He).
  unfold hid in POD.
  lazymatch goal with PX : rw_cells asegs ?mc pixd _, PS : rw_cells asegs ?mc pix _ |- cps _ (ASTA RT Σc _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
    assert (POD1 : pix_obj (rt_live RT Σc) mc pixd v1 (mkCmapv 0 0 0 0))
      by (destruct POD as (_ & CH & HOK & HD & _); split; [unfold pix_cells; rewrite VW, VH, VD, VCMAP; exact PX| split; [exact CH| split; [exact HOK| split; [exact HD| left; exact VCMAP]]]]);
    assert (POS1 : pix_obj_rc (rt_live RT Σc) mc pix v cv 2)
      by (exact (PSRC (rt_live RT Σc) 2 mc LSUB AGF PS)) end.
  hide POD.
  idtac "MARK objs for PCR".
  (* [comment removed for export] *)
  eapply cps_seq.
  {
  eapply PCR with (lo := lo) (pixd := pixd) (pixs := pix) (vd := v1) (vs := v) (cvd := mkCmapv 0 0 0 0) (cvs := cv) (rc := 2).
  - exact FDO.
  - exact MST.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - exact POD1.
  - exact POS1.
  - intros E; apply NPS; symmetry; exact E.
  - lenv_tac.
  }
  idtac "MARK PCR applied".
  (* [comment removed for export] *)
  clear POD1 POS1.
  lazymatch goal with A : ART RT Σc ?mm |- _ =>
    pose proof (live_apart2 RT AF Σc mm pix 64 pixd 64 A (LSUB _ PIN) PDIN ltac:(intros E; inversion E; exact (NPS ltac:(assumption)))) as DSP;
    pose proof (live_apart2 RT AF Σc mm pix 64 dat rs A (LSUB _ PIN) DDIN ltac:(intros E; inversion E; exact (NDS ltac:(assumption)))) as DSD;
    pose proof (live_apart2 RT AF Σc mm pixd 64 dat rs A PDIN DDIN ltac:(intros E; inversion E; apply DDNE; symmetry; assumption)) as DPD;
    pose proof (live_apart2 RT AF Σc mm (p_data v) (4 * (p_wpl v * p_h v)) pixd 64 A (LSUB _ DIN) PDIN ltac:(intros E; inversion E; exact (NSP ltac:(assumption)))) as DRP;
    pose proof (live_apart2 RT AF Σc mm (p_data v) (4 * (p_wpl v * p_h v)) dat rs A (LSUB _ DIN) DDIN ltac:(intros E; inversion E; exact (NSD ltac:(assumption)))) as DRD end.
  park DSP. park DSD. park DPD. park DRP. park DRD.
  after_call RT AF.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; repeat match goal with E : rt_live _ _ = rt_live RT Σc |- _ => rewrite E end; apply LSUB; exact He| solve [frames_sub_tac]| lia]|
                                  cbn [outside]; pose proof (NCP _ (proj1 Hx)); split; [lia| exact I]]).
  idtac "MARK after PCR".
  (* [comment removed for export] *)
  lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σr; rename A into ARTR end.
  lazymatch goal with H : rw_cells asegs _ pixd (pix_cells _) |- _ => rename H into PXD end.
  unfold pix_cells in PXD. cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data] in PXD. rewrite VW, VH, VD, VCMAP in PXD. fold dat in PXD.
  assert (LVR : rt_live RT Σr = rt_live RT Σc) by (repeat match goal with E : rt_live RT Σr = _ |- _ => rewrite E end; reflexivity).
  assert (FRSr : rt_frames RT Σr = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σr = _ |- _ => rewrite E end; exact FRSc).
  assert (SP0r : rt_sp0 RT Σr = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; reflexivity).
  assert (CRr : rt_credit RT Σ - (RASTER_COST + 9) <= rt_credit RT Σr) by (lazymatch goal with E : rt_credit RT Σc <= rt_credit RT Σr |- _ => clear - E CRC; lia end).
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
  try forget_junk_in (usp + -192). try forget_junk_in fr. try forget_junk_in (fr / 8 + 2147450880). try diet_chains.
  walk_to AF MST [(usp - 256, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_pixCopyInputFormat].
  (* [comment removed for export] *)
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS1 _ Hx); destruct (NFA1 _ Hx) as [N1 N2]; unfold shad, SHB in *;
                        repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  assert (LSUBr : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σr)) by (intros e He; rewrite LVR; apply LSUB; exact He).
  unfold hid in POD.
  lazymatch goal with PX : rw_cells asegs ?mc pixd _, PS : rw_cells asegs ?mc pix _ |- cps _ (ASTA RT Σr _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
    assert (POD2 : pix_obj (rt_live RT Σr) mc pixd (pv_res v1 v) (mkCmapv 0 0 0 0))
      by (destruct POD as (_ & CH & HOK & HD & _); rewrite LVR;
          split; [unfold pix_cells, pv_res; cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data]; rewrite VW, VH, VD, VCMAP; exact PX|
          split; [exact CH| split; [exact HOK| split; [exact HD| left; exact VCMAP]]]]);
    assert (POS2 : pix_obj_rc (rt_live RT Σr) mc pix v cv 2)
      by (exact (PSRC (rt_live RT Σr) 2 mc LSUBr AGF PS)) end.
  hide POD.
  eapply cps_seq.
  {
  eapply PCI with (lo := lo) (pixd := pixd) (pixs := pix) (vd := pv_res v1 v) (vs := v) (cvd := mkCmapv 0 0 0 0) (cvs := cv) (rc := 2).
  - exact FDO.
  - exact MST.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - exact POD2.
  - exact POS2.
  - intros E; apply NPS; symmetry; exact E.
  - lenv_tac.
  }
  clear POD2 POS2.
  idtac "MARK PCI applied".
  (* [comment removed for export] *)
  after_call RT AF.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; repeat match goal with E : rt_live _ _ = rt_live RT Σr |- _ => rewrite E end; apply LSUBr; exact He| solve [frames_sub_tac]| lia]|
                                  cbn [outside]; pose proof (NCP _ (proj1 Hx)); split; [lia| exact I]]).
  lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σi; rename A into ARTI end.
  lazymatch goal with H : rw_cells asegs _ pixd (pix_cells _) |- _ => rename H into PXD end.
  unfold pix_cells, pv_inf, pv_res in PXD. cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data] in PXD. rewrite VW, VH, VD, VCMAP in PXD. fold dat in PXD.
  assert (LVI : rt_live RT Σi = (dat, rs) :: (pixd, 64) :: rt_live RT Σ) by (repeat match goal with E : rt_live RT Σi = _ |- _ => rewrite E end; rewrite LVR; exact LVC).
  assert (FRSi : rt_frames RT Σi = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σi = _ |- _ => rewrite E end; exact FRSr).
  assert (SP0i : rt_sp0 RT Σi = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; reflexivity).
  assert (CRi : rt_credit RT Σ - (RASTER_COST + 9) <= rt_credit RT Σi) by (lazymatch goal with E : rt_credit RT Σr <= rt_credit RT Σi |- _ => clear - E CRr; lia end).
  assert (LSUBi : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σi)) by (intros e He; rewrite LVI; right; right; exact He).
  assert (PDINi : In (pixd, 64) (rt_live RT Σi)) by (rewrite LVI; right; left; reflexivity).
  assert (DDINi : In (dat, rs) (rt_live RT Σi)) by (rewrite LVI; left; reflexivity).
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  idtac "MARK after PCI".
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  try forget_junk_in (usp + -192). try forget_junk_in fr. try forget_junk_in (fr / 8 + 2147450880). try diet_chains.
  walk_to AF MST [(usp - 256, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x9f050; 0x9f318].
  rewrite !(sx32_small (p_h v)) by lia.
  awalk [0x9f098; 0x9f318].
  idtac "MARK at row head".
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
  lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS1 _ Hx); destruct (NFA1 _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                         repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
  lazymatch goal with A : ART RT Σi ?ma, WMa : wmono asegs ?ma ?mm |- cps _ (ASTA RT Σi _ (eq (MS _ _ _ _ _ ?mm _))) _ =>
      pose proof (wr_at_transport asegs ma mm dat rs (proj1 (af_acc_live RT AF Σi ma dat rs A DDINi)) WMa) as WRD end.
  lazymatch goal with WMa : wmono asegs m ?mm |- cps _ (ASTA RT Σi _ (eq (MS _ _ _ _ _ ?mm _))) _ =>
      pose proof (wr_at_transport asegs m mm (p_data v) (4 * (p_wpl v * p_h v)) (proj1 (af_acc_live RT AF Σ m (p_data v) (4 * (p_wpl v * p_h v)) ART0 DIN)) WMa) as WRS end.
  rewrite ERS in WRD.
  apply wr_at_rw_CB in WRD; [| clear - RSD0; lia]. destruct WRD as (dbs & DBC).
  pose proof DBC as [[[DBL _] _] _]. cbn in DBL. apply u8arr_of_rw_cells in DBC.
  lazymatch type of DBC with u8arr _ ?mm _ _ =>
      destruct (u8arr_u32arr mm dat dbs (p_wpl v1 * p_h v) DBC ltac:(rewrite DBL; clear - RSD0; lia)) as (wd & UAD & UADL) end.
  apply wr_at_rw_CB in WRS; [| clear - HRS0; lia]. destruct WRS as (sbs & SBC).
  pose proof SBC as [[[SBL _] _] _]. cbn in SBL. apply u8arr_of_rw_cells in SBC.
  destruct SBC as [HBS _].
  assert (WSR : 0 < p_wpl v <= 2^20 /\ p_w v * p_d v <= 32 * p_wpl v) by (rewrite HWPL; clear - HW0 HW2 D248R; Z.div_mod_to_equations; lia).
  destruct WSR as (WSR & WSW).
  assert (WDR : 0 < p_wpl v1 <= 2^20 /\ p_w v <= 32 * p_wpl v1) by (rewrite EWD; clear - HW0 HW2; Z.div_mod_to_equations; lia).
  destruct WDR as (WDR & WDW).

  rewrite !(sx32_small (p_w v)) in FRM by (clear - HW0 HW2; lia). rewrite !(sx32_small (p_h v)) in FRM by (clear - HH0 HH2; lia).
  rewrite !(sx32_small (p_d v)) in FRM by (clear - D248R; lia).
  (* [comment removed for export] *)
  split_at FRM 4%nat FC. split_at FC 5%nat FRMt.
  (* [comment removed for export] *)
  rewrite ?(sx32_small (p_wpl v1)) in FR by (clear - WDR; lia). rewrite ?(sx32_small (p_wpl v)) in FR by (clear - WSR; lia).
  rewrite ?(unsigned_lit (p_wpl v)) in FR by (clear - WSR; lia).
  split_before FR (C8 (Z_to_bv 64 (p_wpl v1))) SL. split_at SL 4%nat FRhi.
  replace (usp + -160) with (usp + -192 + 32) in SL by (clear; lia).
  try forget_junk_in (usp + -192). try forget_junk_in fr. try forget_junk_in (fr / 8 + 2147450880). try diet_chains.
  walk_to AF MST [(dat, dat + 4 * (p_wpl v1 * p_h v)); (usp + -192 + 32, usp + -192 + 64)] [0x9f098].   (* [comment removed for export] *)
  rewrite ?(sx32_small (p_wpl v1)) by (clear - WDR; lia).
  rewrite ?(sx32_small (p_wpl v)) by (clear - WSR; lia). rewrite ?(unsigned_lit (p_wpl v)) by (clear - WSR; lia).
  try (replace (p_wpl v * 4) with (4 * p_wpl v) by (clear; lia)).
  (* [comment removed for export] *)
  assert (EP : (0 <? p_data v) = true) by (apply Z.ltb_lt; exact D0).
  assert (ED : (0 <? dat) = true) by (apply Z.ltb_lt; exact DD0).
  rewrite ?EP, ?ED. change (Z.b2z true) with 1.
  assert (GEO : band_geom (usp + -192) fr (p_data v) dat (p_wpl v) (p_wpl v1) (p_w v) (p_h v) (p_d v)).
  { unfold band_geom, SEGTOP_A.
    clear - HW0 HW2 WSR WSW WDR WDW HH0 HH2 HRS1 RSD1 D0 D16 CKR0 SP0R1 CKH0 CKS0 DD0 DD16 CKR2 ERS CKH2 CKS2 DRD FR0 FR64 FRSEG FRSH FCD2 FRHI LOW LOR SPT SPA SPB STa SP0W USP0 SP0R0 CKR FCD FCD0.
    unfold parked in *.
    repeat lazymatch goal with |- _ /\ _ => split end; first [lia | Z.div_mod_to_equations; lia]. }
  assert (HDIN : In (p_d v) [2; 4; 8]) by (clear - D248R; cbn [In]; lia).
  idtac "MARK geom".
  (* [comment removed for export] *)
  eapply evt_cut.
  { lazymatch goal with MIx : mem_inv asegs ?mm, ACCSx : acc asegs ?mm (p_data v) _, ACCDx : acc asegs ?mm dat _ |- evt _ _ (MS _ ?F0 _ ?fc0 None ?mm _) =>
      lazymatch type of FC with rw_cells _ _ _ [C4 _; CB 12 ?p0; C4 _; CB 12 ?p1; C4 _] =>
        assert (INV : band_inv mm (usp + -192) fr (p_data v) dat (p_wpl v) (p_wpl v1) (p_w v) (p_h v) (p_d v) (0 * p_wpl v) sbs wd p0 p1)
          by (unfold band_inv; split; [exact MIx|]; split; [exact HBS|]; split; [rewrite SBL; clear - HRS0; lia|]; split; [exact ACCSx|]; split; [exact UAD|]; split; [exact UADL|];
              split; [rewrite <- ERS; exact ACCDx|]; split; [exact FC| exact SL]);
        epose proof (band_rows (p_d v) HDIN (Z.to_nat (p_h v)) 0 _ _ gp _ _ _ _ _ _ _ _ _ _ _ _ _ _ F0 fc0 mm (usp + -192) fr (p_data v) dat (p_wpl v) (p_wpl v1) (p_w v) (p_h v)
                       sbs wd p0 p1 ltac:(clear - HH0; lia) ltac:(clear; lia) ltac:(clear - HH0; lia) GEO INV) as ZR end end.
    unfold SHB in ZR.
    exact ZR. }
  idtac "MARK rows applied".
  (* [comment removed for export] *)
  intros ms' PO. unfold band_exit in PO.
  destruct PO as (ra' & t2' & a0' & a1' & a2' & a3' & a7' & t3' & t4' & t5' & t6' & mr & wdr & iacr & -> & MUr & WMr & INVr).
  destruct INVr as (MIr & HBr & HBLr & ACCSr & UADr & UADLr & ACCDr & FCr & SLr).
  unfold SHB.
  assert (FCS2' : dat + rs <= fr / 8 + 2147450880 \/ fr / 8 + 2147450880 + 16 <= dat)
    by (clear - FCS2; unfold parked in FCS2; Z.div_mod_to_equations; lia).
  loop_art RT AF Σi mr lo MUr ltac:(cbn [ivls_client]; split; [intros zz Hzz; right; right; left; exists dat, rs; split; [exact DDINi| rewrite ERS; lia]| split; [intros zz Hzz; left; ul| exact I]]).
  clear HBS SBL UAD UADL DBC DBL SL FC HBr HBLr ACCSr UADr UADLr ACCDr.
  lazymatch type of MUr with munch _ ?ma ?mb =>
      loop_transport ma mb MUr ltac:(fun Hx => clear - Hx CKR2 CKS2 ERS RSD0 FCD2 FCS2' DSD DPD DRD CKR0 CKR CKR1 FRSH FRHI FR0 FRSEG FR64 LOW LOR SPT SPB STa SP0W SP0R0 SP0R1; unfold parked in *; first [lia | Z.div_mod_to_equations; lia]) end.
  join_cells FR SLr. join_cells FR FRhi. join_cells FRM FCr. join_cells FRM FRMt.
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; right; right; left; exists dat, rs; split; [exact DDINi| rewrite ERS; lia]| split; [intros zz Hzz; left; ul| exact I]]).
  lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (NCD _ (proj1 Hx)) as NCDx; pose proof (PFS1 _ Hx) as PFSx; clear - NCDx PFSx ERS LOR LOW; repeat split; try exact I; lia) end.
  idtac "MARK loop done".
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
  try forget_junk_in (usp + -192). try forget_junk_in fr. try forget_junk_in (fr / 8 + 2147450880). try diet_chains.
  walk_to AF MST [(usp - 256, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [e_pixDestroy].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS1 _ Hx); destruct (NFA1 _ Hx) as [N1 N2]; unfold shad, SHB in *;
                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  (* [comment removed for export] *)
  split_at FRM 10%nat PPC. split_at PPC 1%nat FRMb.
  pose proof FSH as SH10. split_at SH10 10%nat SH10b. split_at SH10b 1%nat SH10c. clear SH10 SH10c.
  lazymatch goal with PS : rw_cells asegs ?mc pix _ |- cps _ (ASTA RT Σi _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
    assert (POS3 : pix_obj_rc (rt_live RT Σi) mc pix v cv 2) by (exact (PSRC (rt_live RT Σi) 2 mc LSUBi AGF PS));
    assert (OPP : optrL RT (rt_live RT Σi) Σi mc (fr + 80) 8)
      by (unfold optrL, accok; split;
          [ right; exists fr, 1%nat; rewrite FRSi; change (fs_size 1) with 128;
            split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|]; split; [lia|];
            split; [clear - FRHI SP0R1; lia|];
            replace (shad (fr + 80)) with (fr / 8 + 2147450890) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
            destruct SH10b as [[_ B] _]; cbn [cells_bytes cbytes app] in B; change (ushadow 8) with [Z_to_bv 8 0]; exact B
          | split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|]; unfold SEGTOP_A; split; [clear - FRSH; unfold parked in FRSH; lia| clear - FRSEG; lia] ]) end.
  idtac "MARK destroy args".
  (* [comment removed for export] *)
  assert (CR1 : 1 <= rt_credit RT Σi) by (clear - CRi CRB; unfold RASTER_COST in *; lia).
  eapply cps_seq.
  {
  eapply PDR with (lo := lo) (pp := fr + 80) (pix := pix) (v := v) (cv := cv) (rc := 2).
  - exact FDO.
  - exact MST.
  - reflexivity.
  - reflexivity.
  - exact OPP.
  - exact PPC.
  - exact POS3.
  - lia.
  - clear - FCD; unfold parked in FCD; lia.
  - lenv_tac.
  - unfold lres; rewrite FRSi, LVI; cbn [length]; unfold FRAMES_MAX, LIVE_MAX in *; repeat split; [lia| lia| exact CR1|].
    intros p n Hp; cbn [In] in Hp; destruct Hp as [Hp|[Hp|Hp]]; [injection Hp as <- <-; exact DDN| injection Hp as <- <-; lia| exact (LVP p n Hp)].
  }
  clear POS3 OPP PPC.
  idtac "MARK PDR applied".
  (* [comment removed for export] *)
  try clear SH10b.
  after_call RT AF.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (proj1 Hx)); [intros e He; repeat match goal with E : rt_live _ _ = rt_live RT Σi |- _ => rewrite E end; apply LSUBi; exact He| solve [frames_sub_tac]| lia]|
                                  cbn [outside]; pose proof (PFO _ Hx) as PFOx; destruct (NFA1 _ Hx) as [N1 N2]; clear - PFOx N1; repeat split; try exact I; lia]).
  lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σp; rename A into ARTP end.
  lazymatch goal with H : rw_cells asegs _ pix (pix_cells_rc v _) |- _ => rename H into PXC1 end.
  lazymatch goal with H : rw_cells asegs _ (fr + 80) [C8 _] |- _ => rename H into PPZ end.
  change (2 - 1) with 1 in PXC1. unfold pix_cells_rc in PXC1.
  join_cells FRM PPZ. join_cells FRM FRMb.
  assert (LVPp : rt_live RT Σp = (dat, rs) :: (pixd, 64) :: rt_live RT Σ) by (repeat match goal with E : rt_live RT Σp = _ |- _ => rewrite E end; exact LVI).
  assert (FRSp : rt_frames RT Σp = (fr, 1%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σp = _ |- _ => rewrite E end; exact FRSi).
  assert (SP0p : rt_sp0 RT Σp = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; reflexivity).
  assert (CRp : rt_credit RT Σ - (RASTER_COST + 10) <= rt_credit RT Σp) by (lazymatch goal with E : rt_credit RT Σi - 1 <= rt_credit RT Σp |- _ => clear - E CRi; lia end).
  idtac "MARK after PDR".
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
  try forget_junk_in (usp + -192). try forget_junk_in fr. try forget_junk_in (fr / 8 + 2147450880). try diet_chains.
  (* [comment removed for export] *)
  Time walk_to AF MST [(usp - 256, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0x9eef0].
  idtac "MARK at pokes".
  try unfold hid in FRM. try unfold hid in FSH. split_at FRM 1%nat FRMr.
  Time (eapply evt_cut;
  [ eapply EVQ_exit;
    [ eapply band_exit_x1; [exact FR0| exact FR64| clear - FRHI SP0R1; lia| exact FRM| exact FSH| reflexivity| assumption]
    | cbn [mkR]; repeat first [ lazymatch goal with |- @eq Z _ _ => clear; lia end | progress f_equal | reflexivity ] ]
  | ]).
  clear FRM FSH. intros ms' PO. destruct PO as (mx & -> & MUx & WMx & MIx & FRM & FSH). unfold band_exit_W, SHB in MUx. unfold band_sh_f5 in FSH.
  idtac "MARK pokes applied".
  Time (lazymatch goal with A : ART RT ?Sx _ |- _ => loop_art RT AF Sx mx lo MUx ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]) end).
  Time (lazymatch type of MUx with munch _ ?ma ?mb =>
    loop_transport ma mb MUx ltac:(fun Hx => cbn [outside]; unfold shad, SHB in *;
        first [ first [pose proof FRSEG as XFRSEG | pose proof I as XFRSEG]; first [pose proof SP0W as XSP0W | pose proof I as XSP0W]; first [pose proof FRSH as XFRSH | pose proof I as XFRSH];
                clear - Hx FRHI LOW LOR FR64 FR0 SP0R1 SP0R0 XFRSEG XSP0W XFRSH;
                unfold parked, hid in *; unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *; repeat split; try exact I; solve [first [lia | Z.div_mod_to_equations; lia]]
              | repeat split; try exact I; notin_side ]) end).
  join_cells FRM FRMr.
  (* [comment removed for export] *)
  frame_release_g RT AF GP MST Σ fr 1%nat 128 PF1 AGF PFS1 usp lo 0x9ef60
        ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
        ltac:(fun Hx => cbn [outside]; pose proof (PFS1 _ Hx); destruct (NFA1 _ Hx) as [N1 N2]; unfold shad, SHB in *; repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia])
        ltac:(fun Hx => exact (proj1 Hx)) ltac:(fun fl FLN => idtac).
  idtac "MARK frame released".
  refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
  try forget_junk_in (usp + -192). try forget_junk_in fr. try forget_junk_in (fr / 8 + 2147450880). try diet_chains.
  walk_to AF MST [(usp - 256, usp)] (@nil Z).
  (* [comment removed for export] *)
  try rewrite ESP. rewrite ?(unsigned_lit usp) by (clear - USP0 USP1; lia).
  awalk (@nil Z).
  cps_stop.
  idtac "MARK epilogue walked".
  apply cps_finish; intros c Hc; subst QF; cbv beta.
  set (vf := pv_inf (pv_res v1 v) v).
  assert (VFC : p_cmap vf = 0) by (exact VCMAP).
  assert (VFD : p_data vf = dat) by reflexivity.
  unfold hid in SUBP, SUBD, HOKD.
  lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S, pixd, vf, (mkCmapv 0 0 0 0) end.
  split.
  2: {
  split; [intros Z0; exfalso; clear - Z0 PD0; lia|].
  split.
  { intros _. rewrite LV2, LVPp.
    pose proof (live_destroy_tmpl (rt_live RT Σ) pixd dat rs 0 0 0 vf (mkCmapv 0 0 0 0) VFD VFC
                  (fun N => False_ind _ (N eq_refl)) VDATA1 DDNE (fun N => False_ind _ (N eq_refl))
                  (fun e He => conj (proj2 (SUBP e He)) (proj2 (SUBD e He))) (fun N => False_ind _ (N eq_refl))) as LD.
    cbn [Z.eqb] in LD. exact LD. }
  split.
  { intros p n Hp. rewrite LV2, LVPp in Hp. cbn [In] in Hp. destruct Hp as [Hp|[Hp|Hp]]; [injection Hp as <- <-; exact DDN| injection Hp as <- <-; lia| exact (LVP p n Hp)]. }
  split; [rewrite LV2, LVPp; cbn [length]; lia|].
  split; [exact FRS2|]. split; [rewrite SP2; exact SP0p|].
  try rewrite D248. rewrite CR2. clear - CRp. unfold RASTER_COST in *. lia.
  }
  eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists.
  split; [unfold ret_st; rewrite ?ESP; do 16 eexists; reflexivity|].
  split; [unfold rt_after_f; split; [split; [assumption| split; assumption]| split; assumption]|].
  split; [intros a Ha Ho; apply AGF; split; [exact Ha| exact Ho]|].
  split.
  { lazymatch goal with PS : rw_cells asegs ?mc pix _ |- pix_obj (rt_live RT ?S) ?mc pix v cv =>
      exact (PSRC (rt_live RT S) 1 mc ltac:(intros e He; rewrite LV2, LVPp; right; right; exact He) AGF PS) end. }
  right. split; [| rewrite VFD; exact VDATA1].
  rewrite LV2, LVPp.
  split; [unfold pix_cells, vf, pv_inf, pv_res; cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data]; rewrite VW, VH, VD, VCMAP; exact PXD|].
  split; [split; [right; left; reflexivity| split; [exact PD0| split; [exact PD16| lia]]]|].
  split; [exact HOKD|].
  split; [right; split; [split; [left; reflexivity| split; [exact DD0| split; [exact DD16| exact DDN]]]| exact DDNE]| left; exact VFC].
Qed.
End BANDC.
