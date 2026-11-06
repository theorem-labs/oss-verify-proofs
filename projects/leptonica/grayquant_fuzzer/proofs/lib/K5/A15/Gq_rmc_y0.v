(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import ImageA.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Malloc Require Import MallocKit_AB.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import Layout.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit Lept_leaf Lept_chain LeptC_leaf Lept_objkit LeptL_kit Lept_gmax_defs Lept_fuzzkit
  Gm_iface Gq_iface Gq_cmap_iface Gm_kit Gm_leaf Gm_livekit Gm_livekit2 Gq_clone Gq_rmc_defs Gq_rmc_statics Ed_statics Ed_fpkit Gq_rmc_gray Gq_rmc_rows.
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


(* [comment removed for export] *)
Ltac apart2 RT AF NAME p n q k NE :=
  lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ =>
    assert (NAME : p + n <= q \/ q + k <= p)
      by (apply (live_apart2 RT AF S mm p n q k A);
          [ solve [in_live_tac] | solve [in_live_tac] | let E := fresh in intro E; injection E; intros; apply NE; congruence ])
  end.
(* [comment removed for export] *)
Ltac join_cells H1 H2 :=
  lazymatch type of H1 with rw_cells _ ?m ?A ?cs1 =>
  lazymatch type of H2 with rw_cells _ ?m ?B ?cs2 =>
    let J := fresh "J" in
    assert (J : rw_cells asegs m A (cs1 ++ cs2))
      by (apply (proj2 (rw_cells_app m A cs1 cs2)); split;
          [ exact H1
          | cbn [cells_size csize Nat.add]; lazymatch goal with |- rw_cells _ _ ?X _ => replace X with B by (clear; lia) end; exact H2 ]);
    clear H1 H2; cbn [app] in J; rename J into H1 end end.

(* [comment removed for export] *)
Ltac ctx_gc RT :=
  lazymatch goal with
  | |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      repeat match goal with
      | H : ART RT _ ?m' |- _ => tryif constr_eq m' mc then fail else clear H
      | H : mem_inv asegs ?m' |- _ => tryif constr_eq m' mc then fail else clear H
      | H : stk asegs ?m' _ _ |- _ => tryif constr_eq m' mc then fail else clear H
      | H : LIBH ?m' |- _ => tryif constr_eq m' mc then fail else clear H
      | H : io_ssp ?m' |- _ => tryif constr_eq m' mc then fail else clear H
      | H : acc asegs ?m' _ _ |- _ => tryif constr_eq m' mc then fail else clear H
      | H : wmono asegs _ _ |- _ => clear H
      | H : True |- _ => clear H
      end;
      repeat match goal with x : word |- _ => clear x end;
      repeat match goal with x : bvmap 5 word |- _ => clear x end;
      repeat match goal with x : bv 32 |- _ => clear x end;
      repeat match goal with x : list byte |- _ => clear x end;
      repeat match goal with x : mem |- _ => clear x end
  end.

(* [comment removed for export] *)
Ltac sigma_gc RT S0 Sx :=
  repeat match goal with S : rts RT |- _ =>
    tryif constr_eq S S0 then fail else tryif constr_eq S Sx then fail else
      (repeat match goal with H : context [S] |- _ => clear H end; clear S) end.
(* [comment removed for export] *)
Ltac park_ne := repeat match goal with H : (?a <> ?b) |- _ => lazymatch type of a with Z => change (a <> b) with (parked (a <> b)) in H end end.
(* [comment removed for export] *)
Ltac fold_mkR :=
  lazymatch goal with |- context [MS (TNode
    (TNode (TNode (TNode (TNode (TNode TEmpty (Some ?x31) TEmpty) (Some ?x15) TEmpty) (Some ?x7) (TNode TEmpty (Some ?x23) TEmpty)) (Some ?x3) (TNode (TNode TEmpty (Some ?x19) TEmpty) (Some ?x11) (TNode TEmpty (Some ?x27) TEmpty)))
       (Some ?x1) (TNode (TNode (TNode TEmpty (Some ?x17) TEmpty) (Some ?x9) (TNode TEmpty (Some ?x25) TEmpty)) (Some ?x5) (TNode (TNode TEmpty (Some ?x21) TEmpty) (Some ?x13) (TNode TEmpty (Some ?x29) TEmpty))))
    None
    (TNode (TNode (TNode (TNode TEmpty (Some ?x16) TEmpty) (Some ?x8) (TNode TEmpty (Some ?x24) TEmpty)) (Some ?x4) (TNode (TNode TEmpty (Some ?x20) TEmpty) (Some ?x12) (TNode TEmpty (Some ?x28) TEmpty))) (Some ?x2)
       (TNode (TNode (TNode TEmpty (Some ?x18) TEmpty) (Some ?x10) (TNode TEmpty (Some ?x26) TEmpty)) (Some ?x6) (TNode (TNode TEmpty (Some ?x22) TEmpty) (Some ?x14) (TNode TEmpty (Some ?x30) TEmpty))))) _ _ _ _ _ _] =>
    let t := constr:(mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) in
    lazymatch goal with |- context [MS ?R _ _ _ _ _ _] => change R with t end
  end.
Definition osd_keep (P : Prop) : Prop := P.
Ltac osd_has T := match goal with _ : osd_keep T |- _ => idtac end.
Ltac osd_mark H :=
  lazymatch type of H with ?T =>
    tryif osd_has T then idtac else (let K := fresh "OSD" in pose proof H as K; change T with (osd_keep T) in K) end.
Ltac osd_mark_about t :=
  repeat match goal with H : ?T |- _ =>
    lazymatch T with
    | osd_keep _ => fail
    | hid _ => fail
    | context [asegs] => fail
    | context [@In] => fail
    | context [rt_live] => fail
    | context [t] => lazymatch type of T with Prop => tryif osd_has T then fail else (let K := fresh "OSD" in pose proof H as K; change T with (osd_keep T) in K) end
    end end.
Ltac osd_clear := repeat match goal with H : osd_keep _ |- _ => clear H end.
(* [comment removed for export] *)
Ltac osd_prune :=
  repeat match goal with H : ?T |- _ =>
    lazymatch T with
    | osd_keep _ => fail
    | _ => lazymatch type of T with Prop => clear H end
    end end;
  repeat match goal with H : osd_keep ?T |- _ => change (osd_keep T) with T in H; try unfold parked in H end.
Ltac osd_lia := zn_lits; unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, shad, SHB in *; first [lia | Z.div_mod_to_equations; lia].
Ltac outside_side ::=
  cbn [outside];
  first [ exact I
        | lazymatch goal with _ : osd_keep _ |- _ => idtac end;
          lazymatch goal with Hx : (_ <= ?x < _)%Z |- _ => revert Hx end;
          osd_prune; intros ?Hx; repeat split; osd_lia
        | repeat split; notin_side ].
Ltac static_in_P ::=
  let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
  first [ right; left; exact Ha
        | split; [ right; left; exact Ha
                 | first [ cbn [outside]; exact I
                         | lazymatch goal with _ : osd_keep _ |- _ => idtac end;
                           cbn [outside]; generalize (client_static_below a Ha); generalize (client_static_ge a Ha);
                           osd_prune; intros ?Hb ?Hc; repeat split; osd_lia
                         | let Hc := fresh in intros Hc;
                           pose proof (client_static_below a Ha); pose proof (client_static_ge a Ha); unfold SEGTOP_A in *; first [ lia | tlia ]
                         | cbn [outside]; pose proof (client_static_below a Ha); pose proof (client_static_ge a Ha);
                           unfold SEGTOP_A in *; repeat split; tlia ] ] ].
(* [comment removed for export] *)
Ltac fix_ret_pc ::=
  repeat match goal with
  | |- context [ret_pc (Z_to_bv 64 ?z)] => rewrite (ret_pc_even z) by (clear; first [lia | reflexivity])
  end.

(* [comment removed for export] *)
Lemma CB4_cell : forall (mm : mem) A bs, rw_cells asegs mm A [CB 4 bs] -> exists x : word, rw_cells asegs mm A [C4 x].
Proof.
  intros mq Aq bq Hq. pose proof Hq as [[W _] _]. cbn in W. destruct W as [Lq _].
  destruct bq as [|b0 [|b1 [|b2 [|b3 [|]]]]]; cbn in Lq; try discriminate.
  exists (Z_to_bv 64 (bytes_le_to_Z [b0; b1; b2; b3])).
  apply (rw_cells_recell mq Aq _ [C4 _] Hq); [cbn; tauto | | reflexivity].
  cbn [cells_bytes cbytes app].
  unfold le4. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
  rewrite (Z_to_le_bytes_mod 4 _ 64) by lia. pose proof (le_bytes_roundtrip [b0; b1; b2; b3]) as RT4. cbn [length] in RT4. rewrite RT4. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma not_In_ct : forall t, ct_mem t = false -> ~ In t CLIENT_TRACES.
Proof.
  intros t H Hin. assert (E : ct_mem t = true); [| rewrite H in E; discriminate].
  unfold ct_mem. apply existsb_exists. exists t. split; [exact Hin|].
  clear. induction t as [|hx t IH]; cbn; [reflexivity|]. rewrite Z.eqb_refl. exact IH.
Qed.
(* [comment removed for export] *)
Lemma EVQ : forall (P : machine_state -> Prop) ms ms', evt asegs P ms' -> ms' = ms -> evt asegs P ms.
Proof. intros P ms ms' E <-. exact E. Qed.
(* [comment removed for export] *)
Ltac forget_junk H :=
  repeat match type of H with context [CB _ ?bs] =>
    lazymatch bs with
    | firstn _ _ => let j := fresh "jq" in set (j := bs) in *; clearbody j
    | skipn _ _ => let j := fresh "jq" in set (j := bs) in *; clearbody j
    end end.

Section RMC_Y0.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis RC : rt_contracts RT.
Hypothesis TOARR : pixcmapToArrays_cps RT.
Hypothesis PCS : pixCreate_sure_cps RT.
Hypothesis PCR : pixCopyResolution_cps RT.
Hypothesis PCI : pixCopyInputFormat_cps RT.

Theorem pixRemoveColormap_y0 : pixRemoveColormap_case RT 0 true.
Proof using AF GP RC TOARR PCS PCR PCI.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pix v cv ras
    FDO MST -> -> -> POBJ D8 VDATA NZV UC TRS ENV RES AL CM.
  unfold lpost, lpost_f, lenv, lres, keeps, keepsL in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct RES as (FRB & LVB & CRB & LVP).
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_pixRemoveColormap, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  clearbody usp.
  unfold LSTK, STDERR_STACK, REMOVE_COST, RASTER_COST in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  set (LVF := rt_live RT Σ) in *.
  set (PF0 := fun a => aclient LVF (rt_frames RT Σ) usp a).
  pose proof (agree_refl PF0 m) as AGF.
  assert (LVFS : forall e, In e LVF -> In e (rt_live RT Σ)) by (intros e He; exact He).
  assert (PFS : forall a, PF0 a -> usp <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  pose proof POBJ as POBJ0. hide POBJ0.
  assert (PML : forall q k a, In (q, k) (rt_live RT Σ) -> q <= a < q + k -> PF0 a).
  { intros q k a Hq Ha. right; right; left; exists q, k; split; [exact Hq| lia]. }
  destruct POBJ as (PXC & (PIN & PX0 & PX16 & _) & HDROK & PDAT & PCM).
  cbv iota in CM.
  destruct PCM as [PCM|(COBJ & CNP & CAP & CND & CAD)]; [exfalso; exact (CM PCM)|].
  destruct PDAT as [PDAT|((DIN & D0 & D16 & DSZ) & DNE)]; [exfalso; exact (VDATA PDAT)|].
  pose proof COBJ as ((cpad & CMC) & (CIN & C0 & C16 & _) & (AIN & A0 & A16 & ASZ) & (CDEP & CNAL & CN0 & CNN) & CANE).
  unfold cmap_nz in NZV. destruct NZV as [NZV|NZV]; [exfalso; exact (CM NZV)|].
  unfold cmap_cells in CMC.
  pose proof (af_live_range RT AF Σ m pix 64 ART0 PIN) as (_ & PXR & PXS). unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in PXR, PXS.
  pose proof (gp_live_hi RT GP Σ m pix 64 ART0 PIN) as PXH.
  unfold pix_cells in PXC. rewrite D8 in PXC.
  specialize (TRS CM).
  unfold rsize in *.
  park_ne. unpark CM. unpark VDATA.
  chunk_facts RT AF GP (p_cmap v) 24. chunk_facts RT AF GP (c_arr cv) (4 * c_nalloc cv). chunk_facts RT AF GP (p_data v) (4 * (p_wpl v * p_h v)).
  park_disj. carve_frame 320%nat ST.
  idtac "MARK carved".
  Time walk_to AF MST [(usp - 320, usp)] [e_stack_malloc 3%nat].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
  eapply cps_seq.
  { pose proof (gp_stack_malloc_3 RT GP) as SM3; unfold stack_malloc_contract' in SM3; eapply SM3 with (lo := lo); rt_side idtac. }
  after_call RT AF.
  fold_ag ltac:(fun Hx => apply (aclient_mono LVF _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
  fframe_open RT AF PF0 (rt_live RT Σ) usp 3%nat 512 ltac:(fun Ha => exact Ha).
  fframe_chunk RT AF fr 3%nat 512 pix 64.
  fframe_chunk RT AF fr 3%nat 512 (p_data v) (4 * (p_wpl v * p_h v)).
  fframe_chunk RT AF fr 3%nat 512 (p_cmap v) 24.
  fframe_chunk RT AF fr 3%nat 512 (c_arr cv) (4 * c_nalloc cv).
  pose proof (proj2 FSH) as WRSH. cbn [cells_size csize Nat.add] in WRSH. change (Z.of_nat 64) with 64 in WRSH.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
  idtac "MARK frame open".
  Time walk_to AF MST [(usp - 448, usp); (fr, fr + 504); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 64)] [0x9a59c].
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
  lazymatch goal with MUx : munch _ ?mm _ |- _ =>
    agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                                       repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *.
  local_acc FSH fr 10%nat 80 FR64 FR64 ACCW. local_acc FSH fr 12%nat 96 FR64 FR64 ACCH. local_acc FSH fr 14%nat 112 FR64 FR64 ACCD.
  park_disj.
  idtac "MARK header done".
  forget_junk FR. forget_junk FRM. forget_junk FSH.
  Time walk_to AF MST [(usp - 448, usp); (fr, fr + 504); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 64)] [e_pixcmapToArrays; 0x95318; 0x9a5c8; 0x9a740; 0x9a688].
  assert (CN256 : c_nalloc cv <= 256).
  { clear - CDEP CNAL. rewrite CNAL. cbn [In] in CDEP. destruct CDEP as [E|[E|[E|[E|E]]]]; try (rewrite <- E; cbv; discriminate). destruct E. }
  lazymatch goal with |- context [bv_swrap 32 ?e] => let r := eval vm_compute in (bv_swrap 32 e) in change (bv_swrap 32 e) with r end.
  rewrite (sx32_small (c_n cv)) by lia.
  brT.
  Time awalk [e_pixcmapToArrays; 0x95318; 0x9a5c8; 0x9a740; 0x9a688].
  (* [comment removed for export] *)
  split_last_CB FRM [60%nat; 8%nat; 24%nat; 8%nat; 24%nat; 8%nat; 24%nat; 8%nat; 224%nat].
  split_at FRM 9%nat FRb. split_at FRb 1%nat PRC. split_at PRC 1%nat FRc. split_at FRc 1%nat PGC. split_at PGC 1%nat FRd.
  split_at FRd 1%nat PBC. split_at PBC 1%nat FRe. split_at FRe 1%nat PAC. split_at PAC 1%nat FRf.
  assert (CB8 : forall (mm : mem) A bs, rw_cells asegs mm A [CB 8 bs] -> exists x : word, rw_cells asegs mm A [C8 x]).
  { clear.
    assert (RNG : forall bs : list byte, (0 <= bytes_le_to_Z bs < 2^(8 * Z.of_nat (length bs)))%Z).
    { clear. induction bs as [|b bs IH]; cbn [bytes_le_to_Z length]; [cbn; lia|].
      pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2^Z.of_N 8)%Z with (2^8)%Z in Hb.
      assert (Hs : (0 <= Z.shiftl (bytes_le_to_Z bs) 8)%Z) by (apply Z.shiftl_nonneg; lia).
      split. { apply Z.lor_nonneg. lia. }
      pose proof (Z.add_lor_land (bv_unsigned b) (Z.shiftl (bytes_le_to_Z bs) 8)) as E.
      pose proof (Z.land_nonneg (bv_unsigned b) (Z.shiftl (bytes_le_to_Z bs) 8)) as L.
      rewrite Z.shiftl_mul_pow2 in * by lia.
      replace (2 ^ (8 * Z.of_nat (S (length bs))))%Z with (2^8 * 2 ^ (8 * Z.of_nat (length bs)))%Z.
      2:{ rewrite <- Z.pow_add_r by lia. f_equal. lia. }
      nia. }
    intros mq Aq bq Hq. exists (le_bytes_to_word bq). pose proof Hq as [[W _] _]. cbn in W. destruct W as [Lq _].
    apply (rw_cells_recell mq Aq _ [C8 (le_bytes_to_word bq)] Hq); [cbn; tauto | | reflexivity].
    cbn [cells_bytes cbytes app]. f_equal. unfold le8, word_to_le_bytes, le_bytes_to_word.
    pose proof (RNG bq) as HR. rewrite Lq in HR. change (2 ^ (8 * Z.of_nat 8))%Z with (2^64)%Z in HR.
    rewrite unsigned_lit by lia. rewrite <- Lq. apply le_bytes_roundtrip. }
  destruct (CB8 _ _ _ PRC) as (xr & PRC1). destruct (CB8 _ _ _ PGC) as (xg & PGC1). destruct (CB8 _ _ _ PBC) as (xb & PBC1). destruct (CB8 _ _ _ PAC) as (xa & PAC1).
  clear PRC PGC PBC PAC CB8.
  pose proof FSH as SHR. split_at SHR 22%nat SHR2. split_at SHR2 1%nat SHR3. clear SHR SHR3.
  pose proof FSH as SHG. split_at SHG 26%nat SHG2. split_at SHG2 1%nat SHG3. clear SHG SHG3.
  pose proof FSH as SHB_. split_at SHB_ 30%nat SHB2. split_at SHB2 1%nat SHB3. clear SHB_ SHB3.
  pose proof FSH as SHA. split_at SHA 34%nat SHA2. split_at SHA2 1%nat SHA3. clear SHA SHA3.
  idtac "MARK cells".
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  idtac "MARK at_call toarr".
  lazymatch goal with |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
    assert (COBJ1 : cmap_obj (rt_live RT S) mc (p_cmap v) cv)
      by (unfold cmap_obj, chunk; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; fold LVF;
          split; [exists cpad; exact CMC|]; split; [repeat split; try assumption; lia|]; split; [repeat split; try assumption; lia|];
          split; [unfold cmap_ok; repeat split; assumption| exact CANE]) end.
  eapply cps_seq.
  { pose proof TOARR as TA; unfold pixcmapToArrays_cps in TA.
    eapply TA with (lo := lo) (cmap := p_cmap v) (cv := cv) (pr := fr + 176) (pg := fr + 208) (pb := fr + 240) (pa := fr + 272)
                      (x1 := xr) (x2 := xg) (x3 := xb) (x4 := xa); rt_side idtac.
    all: lazymatch goal with
         | |- cmap_obj _ _ _ _ => exact COBJ1
         | |- optrF _ _ _ ?p _ =>
             unfold optrF; split;
             [ exists fr, 3%nat; rewrite FRS; change (fs_size 3) with 512;
               split; [left; reflexivity|]; split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
               split; [lia|]; split; [lia|];
               lazymatch p with
               | (_ + 176) => replace (shad (fr + 176)) with (fr / 8 + 2147450902) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia); destruct SHR2 as [[_ B] _]; exact B
               | (_ + 208) => replace (shad (fr + 208)) with (fr / 8 + 2147450906) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia); destruct SHG2 as [[_ B] _]; exact B
               | (_ + 240) => replace (shad (fr + 240)) with (fr / 8 + 2147450910) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia); destruct SHB2 as [[_ B] _]; exact B
               | (_ + 272) => replace (shad (fr + 272)) with (fr / 8 + 2147450914) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia); destruct SHA2 as [[_ B] _]; exact B
               end
             | let Q := fresh "Q" in pose proof FRSH as Q; unfold parked in Q; unfold SEGTOP_A;
               repeat split; first [clear - FR0; lia | clear - FR64; Z.div_mod_to_equations; lia | clear - Q; lia | clear - FRSEG; lia] ]
         | |- rw_cells _ _ _ _ => first [exact PRC1 | exact PGC1 | exact PBC1 | exact PAC1]
         | |- _ <> _ /\ _ => clear; lia
         | |- 1 <= _ => exact NZV
         | |- lenv _ _ _ _ _ _ => lenv_tac
         | |- lres _ _ _ _ _ => unfold LVF in *; lres_tac
         | |- ?g => idtac "LEFT:" g
         end. }
  idtac "MARK toarr applied".
  after_call RT AF.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono LVF _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]
                                 | cbn [outside]; destruct (NFA _ Hx) as [N1 N2]; repeat split; try exact I; lia]).
  lazymatch goal with H : rt_live RT ?S = (?a, _) :: (?b, _) :: (?g, _) :: (?r, _) :: rt_live RT _ |- _ =>
    rename H into LVT; rename r into rmap; rename g into gmap; rename b into bmap; rename a into amap end.
  repeat match goal with H : byte_arr _ _ _ |- _ => clear H end.     (* [comment removed for export] *)
  lazymatch goal with H : rw_cells asegs _ (fr + 176) [C8 _] |- _ => rename H into PRC1 end.
  lazymatch goal with H : rw_cells asegs _ (fr + 208) [C8 _] |- _ => rename H into PGC1 end.
  lazymatch goal with H : rw_cells asegs _ (fr + 240) [C8 _] |- _ => rename H into PBC1 end.
  lazymatch goal with H : rw_cells asegs _ (fr + 272) [C8 _] |- _ => rename H into PAC1 end.
  clear COBJ1 SHR2 SHG2 SHB2 SHA2.
  chunk_facts RT AF GP rmap (4 * c_n cv). chunk_facts RT AF GP gmap (4 * c_n cv). chunk_facts RT AF GP bmap (4 * c_n cv). chunk_facts RT AF GP amap (4 * c_n cv).
  park_disj.
  lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σt; rename A into ARTT end.
  assert (FRSt : rt_frames RT Σt = (fr, 3%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σt = _ |- _ => rewrite E end; exact FRS).
  assert (LVT4 : rt_live RT Σt = (amap, 4 * c_n cv) :: (bmap, 4 * c_n cv) :: (gmap, 4 * c_n cv) :: (rmap, 4 * c_n cv) :: rt_live RT Σ)
    by (rewrite LVT; repeat match goal with E : rt_live _ _ = rt_live RT Σ |- _ => rewrite E end; reflexivity).
  assert (SP0T : rt_sp0 RT Σt = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; reflexivity).
  assert (CRT : rt_credit RT Σ - 1 <= rt_credit RT Σt) by (repeat match goal with E : rt_credit _ _ = _ |- _ => rewrite E in * end; lia).
  assert (N4 : 0 < 4 * c_n cv) by lia.
  assert (SUBR : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σt) /\ fst e <> rmap)
    by (intros e He; split; [rewrite LVT4; right; right; right; right; exact He|];
        apply (fresh_chunk_ne RT AF Σt _ [(amap, 4 * c_n cv); (bmap, 4 * c_n cv); (gmap, 4 * c_n cv)] rmap (4 * c_n cv) _ e ARTT LVT4);
        [ cbn [app In]; right; right; right; exact He | lia | destruct e as [eq ek]; exact (LVP eq ek He) ]).
  assert (SUBG : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σt) /\ fst e <> gmap)
    by (intros e He; split; [rewrite LVT4; right; right; right; right; exact He|];
        apply (fresh_chunk_ne RT AF Σt _ [(amap, 4 * c_n cv); (bmap, 4 * c_n cv)] gmap (4 * c_n cv) _ e ARTT LVT4);
        [ cbn [app In]; right; right; right; exact He | lia | destruct e as [eq ek]; exact (LVP eq ek He) ]).
  assert (SUBB : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σt) /\ fst e <> bmap)
    by (intros e He; split; [rewrite LVT4; right; right; right; right; exact He|];
        apply (fresh_chunk_ne RT AF Σt _ [(amap, 4 * c_n cv)] bmap (4 * c_n cv) _ e ARTT LVT4);
        [ cbn [app In]; right; right; right; exact He | lia | destruct e as [eq ek]; exact (LVP eq ek He) ]).
  assert (SUBA : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σt) /\ fst e <> amap)
    by (intros e He; split; [rewrite LVT4; right; right; right; right; exact He|];
        apply (fresh_chunk_ne RT AF Σt _ [] amap (4 * c_n cv) _ e ARTT LVT4);
        [ cbn [app In]; right; right; right; exact He | lia | destruct e as [eq ek]; exact (LVP eq ek He) ]).
  assert (NCR : forall a, PF0 a -> a < rmap \/ rmap + 4 * c_n cv <= a)
    by (intros a Ha; apply (inner_chunk_apart RT AF Σt _ rmap (4 * c_n cv) (rt_live RT Σ) (rt_frames RT Σ) usp a ARTT ltac:(solve [in_live_tac]) SUBR);
        [ rewrite FRSt; intros e He; right; exact He | rewrite SP0T; ul | exact Ha ]).
  assert (NCG : forall a, PF0 a -> a < gmap \/ gmap + 4 * c_n cv <= a)
    by (intros a Ha; apply (inner_chunk_apart RT AF Σt _ gmap (4 * c_n cv) (rt_live RT Σ) (rt_frames RT Σ) usp a ARTT ltac:(solve [in_live_tac]) SUBG);
        [ rewrite FRSt; intros e He; right; exact He | rewrite SP0T; ul | exact Ha ]).
  assert (NCB : forall a, PF0 a -> a < bmap \/ bmap + 4 * c_n cv <= a)
    by (intros a Ha; apply (inner_chunk_apart RT AF Σt _ bmap (4 * c_n cv) (rt_live RT Σ) (rt_frames RT Σ) usp a ARTT ltac:(solve [in_live_tac]) SUBB);
        [ rewrite FRSt; intros e He; right; exact He | rewrite SP0T; ul | exact Ha ]).
  assert (NCA : forall a, PF0 a -> a < amap \/ amap + 4 * c_n cv <= a)
    by (intros a Ha; apply (inner_chunk_apart RT AF Σt _ amap (4 * c_n cv) (rt_live RT Σ) (rt_frames RT Σ) usp a ARTT ltac:(solve [in_live_tac]) SUBA);
        [ rewrite FRSt; intros e He; right; exact He | rewrite SP0T; ul | exact Ha ]).
  hide SUBR. hide SUBG. hide SUBB. hide SUBA.
  idtac "MARK toarr names".
  fframe_chunk RT AF fr 3%nat 512 rmap (4 * c_n cv). fframe_chunk RT AF fr 3%nat 512 gmap (4 * c_n cv).
  fframe_chunk RT AF fr 3%nat 512 bmap (4 * c_n cv). fframe_chunk RT AF fr 3%nat 512 amap (4 * c_n cv).
  park_disj.
  idtac "MARK parked".
  (* [comment removed for export] *)
  idtac "MARK join".
  join_cells FRM FRb. join_cells FRM PRC1. join_cells FRM FRc. join_cells FRM PGC1. join_cells FRM FRd. join_cells FRM PBC1. join_cells FRM FRe. join_cells FRM PAC1. join_cells FRM FRf.
  idtac "MARK joined".
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  ctx_gc RT.
  idtac "MARK after toarr".
  Time walk_to AF MST [(usp - 448, usp); (fr, fr + 504); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 64)] [e_pixCreate; e_pixcmapToArrays; 0x95318; 0x9a700; 0x9a900; 0x9a9a4; 0x9aebc].
  (* [comment removed for export] *)
  rewrite !(sx32_small (p_w v)) by (clear - HDROK; destruct HDROK as (_ & Q & _); lia).
  rewrite !(sx32_small (p_h v)) by (clear - HDROK; destruct HDROK as (_ & _ & Q & _); lia).
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  assert (HAO : hdr_args_ok (p_w v) (p_h v) 8).
  { clear - HDROK D8. destruct HDROK as (Q1 & Q2 & Q3 & Q4 & Q5). rewrite D8 in Q4. rewrite Q4 in Q5.
    unfold hdr_args_ok. split; [cbn [In]; tauto|]. split; [exact Q2|]. split; [exact Q3| exact Q5]. }
  assert (LVPt : forall p n, In (p, n) (rt_live RT Σt) -> 0 < n).
  { intros p n Hp. rewrite LVT4 in Hp. cbn [In] in Hp.
    destruct Hp as [Hp|[Hp|[Hp|[Hp|Hp]]]]; try (injection Hp as <- <-; exact N4). exact (LVP p n Hp). }
  idtac "MARK at pixCreate".
  eapply cps_seq.
  { pose proof PCS as PC1; unfold pixCreate_sure_cps in PC1.
    eapply PC1 with (lo := lo) (w := p_w v) (h := p_h v) (d := 8).
    - exact FDO.
    - exact MST.
    - reflexivity.
    - split; [clear - HAO; unfold hdr_args_ok in HAO; lia| reflexivity].
    - split; [clear - HAO; unfold hdr_args_ok in HAO; lia| reflexivity].
    - split; [lia| reflexivity].
    - exact HAO.
    - lenv_tac.
    - unfold lres; unfold FRAMES_MAX, LIVE_MAX, RASTER_COST in *; unfold LVF in *;
      split; [rewrite FRSt; cbn [length]; lia|]; split; [rewrite LVT4; cbn [length]; lia|]; split; [lia| exact LVPt]. }
  idtac "MARK pixCreate applied".
  after_call RT AF.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono LVF _ usp _ _ _ _ Hx); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]| exact I]).
  idtac "MARK after pixCreate".
  lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σc; rename A into ARTC end.
  lazymatch goal with H : pix_obj (rt_live RT Σc) _ ?p ?vv _ |- _ => rename H into POD; rename p into pixd; rename vv into v1 end.
  lazymatch goal with H : rt_live RT Σc = _ |- _ => rename H into LVN end.
  lazymatch goal with H : p_w v1 = _ |- _ => rename H into VW end.
  lazymatch goal with H : p_h v1 = _ |- _ => rename H into VH end.
  lazymatch goal with H : p_d v1 = _ |- _ => rename H into VD end.
  lazymatch goal with H : p_data v1 <> 0 |- _ => rename H into VDATA1 end.
  lazymatch goal with H : p_cmap v1 = 0 |- _ => rename H into VCMAP end.
  assert (FRSc : rt_frames RT Σc = (fr, 3%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σc = _ |- _ => rewrite E end; exact FRSt).
  assert (LVC : rt_live RT Σc = (p_data v1, rsize v1) :: (pixd, 64) :: (amap, 4 * c_n cv) :: (bmap, 4 * c_n cv) :: (gmap, 4 * c_n cv) :: (rmap, 4 * c_n cv) :: rt_live RT Σ)
    by (rewrite LVN; rewrite LVT4; reflexivity).
  assert (SP0C : rt_sp0 RT Σc = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; reflexivity).
  lazymatch goal with H : rt_credit RT Σt - _ <= rt_credit RT Σc |- _ => rename H into CRN end.
  assert (CRC : rt_credit RT Σ - (RASTER_COST + 9) <= rt_credit RT Σc) by (clear - CRT CRN; lia).
  pose proof POD as (PXD & (PDIN & PD0 & PD16 & _) & HOKD & PDDATA & _).
  destruct PDDATA as [PDZ|((DDIN & DD0 & DD16 & DDN) & DDNE)]; [exfalso; exact (VDATA1 PDZ)|].
  set (dat := p_data v1) in *. set (rs := rsize v1) in *.
  idtac "MARK names c".
  assert (SUBP : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σc) /\ fst e <> pixd)
    by (intros e He; split; [rewrite LVC; do 6 right; exact He|];
        apply (fresh_chunk_ne RT AF Σc _ [(dat, rs)] pixd 64 _ e ARTC LVC); [ cbn [app In]; do 5 right; exact He | lia | destruct e as [eq ek]; exact (LVP eq ek He) ]).
  assert (SUBD : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σc) /\ fst e <> dat)
    by (intros e He; split; [rewrite LVC; do 6 right; exact He|];
        apply (fresh_chunk_ne RT AF Σc _ [] dat rs _ e ARTC LVC); [ cbn [app In]; do 5 right; exact He | lia | destruct e as [eq ek]; exact (LVP eq ek He) ]).
  assert (NCP : forall a, PF0 a -> a < pixd \/ pixd + 64 <= a)
    by (intros a Ha; apply (inner_chunk_apart RT AF Σc _ pixd 64 (rt_live RT Σ) (rt_frames RT Σ) usp a ARTC PDIN SUBP);
        [ rewrite FRSc; intros e He; right; exact He | rewrite SP0C; ul | exact Ha ]).
  assert (NCD : forall a, PF0 a -> a < dat \/ dat + rs <= a)
    by (intros a Ha; apply (inner_chunk_apart RT AF Σc _ dat rs (rt_live RT Σ) (rt_frames RT Σ) usp a ARTC DDIN SUBD);
        [ rewrite FRSc; intros e He; right; exact He | rewrite SP0C; ul | exact Ha ]).
  assert (NPS : pix <> pixd) by (exact (proj2 (SUBP (pix, 64) PIN))).
  assert (NPS0 : pixd <> pix) by (intro E; apply NPS; symmetry; exact E).
  assert (NPC0 : pixd <> p_cmap v) by (intro E; apply (proj2 (SUBP (p_cmap v, 24) CIN)); symmetry; exact E).
  assert (NDS : pix <> dat) by (exact (proj2 (SUBD (pix, 64) PIN))).
  assert (NDS0 : dat <> pix) by (intro E; apply NDS; symmetry; exact E).
  assert (NDC0 : dat <> p_cmap v) by (intro E; apply (proj2 (SUBD (p_cmap v, 24) CIN)); symmetry; exact E).
  assert (NSP : p_data v <> pixd) by (exact (proj2 (SUBP (p_data v, 4 * (p_wpl v * p_h v)) DIN))).
  assert (NSD : p_data v <> dat) by (exact (proj2 (SUBD (p_data v, 4 * (p_wpl v * p_h v)) DIN))).
  idtac "MARK apart c".
  chunk_facts RT AF GP pixd 64. chunk_facts RT AF GP dat rs.
  fframe_chunk RT AF fr 3%nat 512 pixd 64. fframe_chunk RT AF fr 3%nat 512 dat rs.
  park_disj.
  unfold pix_cells in PXD. rewrite VW, VH, VD, VCMAP in PXD. fold dat in PXD.
  assert (EWD : p_wpl v1 = p_wpl v) by (destruct HOKD as (_ & _ & _ & Q4 & _); destruct HDROK as (_ & _ & _ & R4 & _); rewrite VW, VD in Q4; rewrite D8 in R4; rewrite Q4, R4; reflexivity).
  assert (ERS : rs = 4 * (p_wpl v * p_h v)) by (unfold rs, rsize; rewrite VH, EWD; reflexivity).
  assert (RSD : 0 < 4 * (p_wpl v * p_h v) <= 67108864) by (destruct HDROK as (_ & _ & _ & _ & Q5); exact Q5).
  rewrite EWD in PXD.
  apart2 RT AF APP pixd 64 pix 64 NPS0. apart2 RT AF APC pixd 64 (p_cmap v) 24 NPC0.
  apart2 RT AF ADP dat rs pix 64 NDS0. apart2 RT AF ADC dat rs (p_cmap v) 24 NDC0. apart2 RT AF ADX dat rs pixd 64 DDNE.
  park_disj.
  hide POD. hide SUBP. hide SUBD. hide HOKD.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  ctx_gc RT.
  park_ne.
  idtac "MARK before PCR".
  Time walk_to AF MST [(usp - 448, usp); (fr, fr + 504); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 64)] [e_pixCopyResolution; e_pixCopyInputFormat; e_calloc; e_pixCreate; 0x95318].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx) as P1; destruct (NFA _ Hx) as [N1 N2]; clear - P1 N1 N2 LOW LOR SPT SPA SPB FR0 FR64;
                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  assert (LSUB : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σc)) by (intros e He; rewrite LVC; do 6 right; exact He).
  unfold hid in POD, POBJ0.
  lazymatch goal with PX : rw_cells asegs ?mc pixd _, PS : rw_cells asegs ?mc pix _ |- cps _ (ASTA RT Σc _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
    assert (POD1 : pix_obj (rt_live RT Σc) mc pixd v1 (mkCmapv 0 0 0 0))
      by (destruct POD as (_ & CH & HOK & HD & _); split; [unfold pix_cells; rewrite VW, VH, VD, VCMAP, EWD; exact PX| split; [exact CH| split; [exact HOK| split; [exact HD| left; exact VCMAP]]]]);
    assert (POS1 : pix_obj (rt_live RT Σc) mc pix v cv)
      by (apply (pix_obj_mono (rt_live RT Σ) _ mc pix v cv LSUB); apply (pix_obj_agree (rt_live RT Σ) PF0 m mc pix v cv POBJ0 AGF PML); unfold pix_cells; rewrite D8; exact PS) end.
  hide POD. hide POBJ0.
  idtac "MARK objs for PCR".
  eapply cps_seq.
  { pose proof PCR as PCR1; unfold pixCopyResolution_cps in PCR1.
    eapply PCR1 with (lo := lo) (pixd := pixd) (pixs := pix) (vd := v1) (vs := v) (cvd := mkCmapv 0 0 0 0) (cvs := cv) (rc := 1).
    - exact FDO.
    - exact MST.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - exact POD1.
    - exact POS1.
    - exact NPS0.
    - lenv_tac. }
  idtac "MARK PCR applied".
  clear POD1 POS1.
  clear PXD.
  osd_mark_about pixd.
  osd_mark LOW. osd_mark LOR. osd_mark SPT. osd_mark SPB. osd_mark STa. osd_mark SP0R0. osd_mark SP0R1. osd_mark FR0. osd_mark FRHI. osd_mark FRSEG. osd_mark FRSH.
  after_call RT AF.
  osd_clear.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono LVF _ usp _ _ _ _ Hx); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]|
                                  cbn [outside]; pose proof (NCP _ Hx); split; [lia| exact I]]).
  idtac "MARK after PCR".
  lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σr; rename A into ARTR end.
  lazymatch goal with H : rw_cells asegs _ pixd (pix_cells _) |- _ => rename H into PXD end.
  unfold pix_cells in PXD. cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data] in PXD. rewrite VW, VH, VD, VCMAP, EWD in PXD. fold dat in PXD.
  assert (LVR : rt_live RT Σr = rt_live RT Σc) by (repeat match goal with E : rt_live RT Σr = _ |- _ => rewrite E end; reflexivity).
  assert (FRSr : rt_frames RT Σr = (fr, 3%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σr = _ |- _ => rewrite E end; exact FRSc).
  assert (SP0r : rt_sp0 RT Σr = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; reflexivity).
  assert (CRr : rt_credit RT Σ - (RASTER_COST + 9) <= rt_credit RT Σr) by (lazymatch goal with E : rt_credit RT Σc <= rt_credit RT Σr |- _ => clear - E CRC; lia end).
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  ctx_gc RT.
  Time walk_to AF MST [(usp - 448, usp); (fr, fr + 504); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 64)] [e_pixCopyInputFormat; e_calloc; e_pixCreate; 0x95318].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx) as P1; destruct (NFA _ Hx) as [N1 N2]; clear - P1 N1 N2 LOW LOR SPT SPA SPB FR0 FR64;
                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  assert (LSUBr : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σr)) by (intros e He; rewrite LVR; apply LSUB; exact He).
  unfold hid in POD, POBJ0.
  lazymatch goal with PX : rw_cells asegs ?mc pixd _, PS : rw_cells asegs ?mc pix _ |- cps _ (ASTA RT Σr _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
    assert (POD2 : pix_obj (rt_live RT Σr) mc pixd (pv_res v1 v) (mkCmapv 0 0 0 0))
      by (destruct POD as (_ & CH & HOK & HD & _); rewrite LVR;
          split; [unfold pix_cells, pv_res; cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data]; rewrite VW, VH, VD, VCMAP, EWD; exact PX|
          split; [exact CH| split; [exact HOK| split; [exact HD| left; exact VCMAP]]]]);
    assert (POS2 : pix_obj (rt_live RT Σr) mc pix v cv)
      by (apply (pix_obj_mono (rt_live RT Σ) _ mc pix v cv LSUBr); apply (pix_obj_agree (rt_live RT Σ) PF0 m mc pix v cv POBJ0 AGF PML); unfold pix_cells; rewrite D8; exact PS) end.
  hide POD. hide POBJ0.
  eapply cps_seq.
  { pose proof PCI as PCI1; unfold pixCopyInputFormat_cps in PCI1.
    eapply PCI1 with (lo := lo) (pixd := pixd) (pixs := pix) (vd := pv_res v1 v) (vs := v) (cvd := mkCmapv 0 0 0 0) (cvs := cv) (rc := 1).
    - exact FDO.
    - exact MST.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - exact POD2.
    - exact POS2.
    - exact NPS0.
    - lenv_tac. }
  clear POD2 POS2.
  idtac "MARK PCI applied".
  clear PXD.
  osd_mark_about pixd.
  osd_mark LOW. osd_mark LOR. osd_mark SPT. osd_mark SPB. osd_mark STa. osd_mark SP0R0. osd_mark SP0R1. osd_mark FR0. osd_mark FRHI. osd_mark FRSEG. osd_mark FRSH.
  after_call RT AF.
  osd_clear.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono LVF _ usp _ _ _ _ Hx); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]|
                                  cbn [outside]; pose proof (NCP _ Hx); split; [lia| exact I]]).
  lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σi; rename A into ARTI end.
  lazymatch goal with H : rw_cells asegs _ pixd (pix_cells _) |- _ => rename H into PXD end.
  unfold pix_cells, pv_inf, pv_res in PXD. cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data] in PXD. rewrite VW, VH, VD, VCMAP, EWD in PXD. fold dat in PXD.
  assert (LVI : rt_live RT Σi = rt_live RT Σc) by (repeat match goal with E : rt_live RT Σi = _ |- _ => rewrite E end; exact LVR).
  assert (FRSi : rt_frames RT Σi = (fr, 3%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σi = _ |- _ => rewrite E end; exact FRSr).
  assert (SP0i : rt_sp0 RT Σi = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; reflexivity).
  assert (CRi : rt_credit RT Σ - (RASTER_COST + 9) <= rt_credit RT Σi) by (lazymatch goal with E : rt_credit RT Σr <= rt_credit RT Σi |- _ => clear - E CRr; lia end).
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  ctx_gc RT.
  idtac "MARK after PCI".
  Time walk_to AF MST [(usp - 448, usp); (fr, fr + 504); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 64)] [e_calloc; e_pixCreate; 0x95318].
  (* [comment removed for export] *)
  assert (TR5 : In (0x9b04c :: bv_unsigned ra :: ras) CLIENT_TRACES).
  { pose proof TRS as T5. rewrite Forall_forall in T5. destruct (T5 0x9b04c ltac:(cbn; tauto)) as [H|H]; [exact H|].
    exfalso. apply (not_In_ct [0x9b04c]); [vm_compute; reflexivity| exact H]. }
  pose proof (client_trace_facts _ TR5) as [_ RAF]. apply Forall_inv_tail in RAF. apply Forall_inv in RAF. destruct RAF as [RALO _].
  pose proof (bv_unsigned_in_range 64 s0) as RS0. unfold bv_modulus in RS0. change (2 ^ Z.of_N 64) with (2^64) in RS0.
  pose proof UC as UCX. unfold uctx in UCX. rewrite ESP in UCX. rewrite unsigned_lit in UCX by lia.
  pose proof FR as FRrec. split_at FRrec 35%nat FRrec2. clear FRrec.
  idtac "MARK calloc prep".
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx) as P1; destruct (NFA _ Hx) as [N1 N2]; clear - P1 N1 N2 LOW LOR SPT SPA SPB FR0 FR64;
                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  idtac "MARK at_call calloc".
  eapply cps_seq.
  { pose proof (gp_calloc RT GP) as CC; unfold calloc_contract in CC; eapply CC with (lo := lo) (nmemb := 256) (size := 4); rt_side idtac.
    all: lazymatch goal with
         | |- unwind_okC _ _ _ _ =>
             exists (bv_unsigned ra :: ras); rewrite ?unsigned_lit by ul; split; [| exact TR5];
             apply (chain_ok_push _ (usp + -320) usp (bv_unsigned ra) (bv_unsigned s0) ras);
               [ clear - USP0; lia | clear - SPA; Z.div_mod_to_equations; lia | clear - SPT; ul | exact RALO | exact RS0
               | rewrite !Z_to_bv_bv_unsigned; first [exact FRrec2 | lazymatch type of FRrec2 with rw_cells _ _ ?A _ => replace (usp + -16) with A by (clear; lia); exact FRrec2 end]
               | ];
             apply (chain_ok_keep ras m _ usp (bv_unsigned s0) UCX);
             eapply agree_sub; [exact AGF|]; intros zx Hzx; left; exact Hzx
         | |- _ => first [ unfold CALLOC_MAX; clear; lia
                         | rewrite LVI, LVC; cbn [length]; unfold LIVE_MAX in *; unfold LVF in LVB; clear - LVB; lia
                         | lazymatch goal with |- ?g => idtac "LEFT:" g end ]
         end. }
  idtac "MARK calloc applied".
  clear FRrec2 UCX.
  after_call RT AF.
  fold_ag ltac:(fun Hx => apply (aclient_mono LVF _ usp _ _ _ _ Hx); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]).
  idtac "MARK after calloc".
  lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σg; rename A into ARTG; rename mm into mg end.
  lazymatch goal with H : rt_live RT Σg = (?p, 256 * 4) :: _ |- _ => rename H into LVGN; rename p into gm end.
  lazymatch goal with H : rw_cells asegs _ gm [CB _ _] |- _ => rename H into GMZ end.
  change (256 * 4) with 1024 in *. change (Z.to_nat 1024) with 1024%nat in GMZ.
  assert (LVG : rt_live RT Σg = (gm, 1024) :: (dat, rs) :: (pixd, 64) :: (amap, 4 * c_n cv) :: (bmap, 4 * c_n cv) :: (gmap, 4 * c_n cv) :: (rmap, 4 * c_n cv) :: rt_live RT Σ)
    by (rewrite LVGN, LVI, LVC; reflexivity).
  assert (FRSg : rt_frames RT Σg = (fr, 3%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σg = _ |- _ => rewrite E end; exact FRSi).
  assert (SP0g : rt_sp0 RT Σg = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; reflexivity).
  assert (CRg : rt_credit RT Σ - (RASTER_COST + 9) <= rt_credit RT Σg) by (lazymatch goal with E : rt_credit RT Σg = _ |- _ => rewrite E; exact CRi end).
  sigma_gc RT Σ Σg.
  assert (GIN : In (gm, 1024) (rt_live RT Σg)) by (rewrite LVG; left; reflexivity).
  assert (DDIN : In (dat, rs) (rt_live RT Σg)) by (rewrite LVG; right; left; reflexivity).
  assert (PDIN : In (pixd, 64) (rt_live RT Σg)) by (rewrite LVG; do 2 right; left; reflexivity).
  assert (AMIN : In (amap, 4 * c_n cv) (rt_live RT Σg)) by (rewrite LVG; do 3 right; left; reflexivity).
  assert (BMIN : In (bmap, 4 * c_n cv) (rt_live RT Σg)) by (rewrite LVG; do 4 right; left; reflexivity).
  assert (GMIN : In (gmap, 4 * c_n cv) (rt_live RT Σg)) by (rewrite LVG; do 5 right; left; reflexivity).
  assert (RMIN : In (rmap, 4 * c_n cv) (rt_live RT Σg)) by (rewrite LVG; do 6 right; left; reflexivity).
  assert (LSUBg : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σg)) by (intros e He; rewrite LVG; do 7 right; exact He).
  assert (NCGM : forall a, PF0 a -> a < gm \/ gm + 1024 <= a).
  { intros a Ha. apply (new_chunk_apart RT AF Σg mg gm 1024 _ _ usp a ARTG LVG FRSg); [rewrite SP0g; clear - LOR LOW; unfold STACK_WIN; lia|].
    apply (aclient_mono LVF (rt_frames RT Σ) usp _ _ usp a Ha); [intros e He; do 6 right; exact He| intros e He; right; exact He| clear; lia]. }
  assert (LVG2 : rt_live RT Σg = [] ++ (gm, 1024) :: ((dat, rs) :: (pixd, 64) :: (amap, 4 * c_n cv) :: (bmap, 4 * c_n cv) :: (gmap, 4 * c_n cv) :: (rmap, 4 * c_n cv) :: rt_live RT Σ)) by (rewrite LVG; reflexivity).
  pose proof (af_live_disj RT AF Σg mg gm 1024 dat rs _ _ ARTG LVG2 ltac:(cbn [app]; left; reflexivity)) as AGD.
  pose proof (af_live_disj RT AF Σg mg gm 1024 pixd 64 _ _ ARTG LVG2 ltac:(cbn [app]; right; left; reflexivity)) as AGP.
  pose proof (af_live_disj RT AF Σg mg gm 1024 amap (4 * c_n cv) _ _ ARTG LVG2 ltac:(cbn [app]; do 2 right; left; reflexivity)) as AGA.
  pose proof (af_live_disj RT AF Σg mg gm 1024 bmap (4 * c_n cv) _ _ ARTG LVG2 ltac:(cbn [app]; do 3 right; left; reflexivity)) as AGB.
  pose proof (af_live_disj RT AF Σg mg gm 1024 gmap (4 * c_n cv) _ _ ARTG LVG2 ltac:(cbn [app]; do 4 right; left; reflexivity)) as AGG.
  pose proof (af_live_disj RT AF Σg mg gm 1024 rmap (4 * c_n cv) _ _ ARTG LVG2 ltac:(cbn [app]; do 5 right; left; reflexivity)) as AGR.
  pose proof (af_live_disj RT AF Σg mg gm 1024 (p_data v) (4 * (p_wpl v * p_h v)) _ _ ARTG LVG2 ltac:(cbn [app]; do 6 right; exact DIN)) as AGS.
  pose proof (af_live_disj RT AF Σg mg gm 1024 pix 64 _ _ ARTG LVG2 ltac:(cbn [app]; do 6 right; exact PIN)) as AGX.
  pose proof (af_live_disj RT AF Σg mg gm 1024 (p_cmap v) 24 _ _ ARTG LVG2 ltac:(cbn [app]; do 6 right; exact CIN)) as AGC.
  clear LVG2.
  chunk_facts RT AF GP gm 1024. fframe_chunk RT AF fr 3%nat 512 gm 1024.
  park_disj. park_ne.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  ctx_gc RT.
  lazymatch goal with MIx : mem_inv asegs mg |- _ => pose proof (rmc_ro_facts mg MIx) as RORMC; pose proof (proj2 (ed_ro_facts mg MIx)) as ROHALF end.
  unfold RMC_RO, RO_RMCW, RO_HALF in RORMC, ROHALF.
  idtac "MARK gm facts".
  Time walk_to AF MST [(usp - 448, usp); (fr, fr + 504); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 64)] [0x9b0a4; 0x9b188].
  (* [comment removed for export] *)
  cps_stop.
  Time walk_to AF MST [(gm, gm + 1024)] [0x9b0a4].
  pose proof (af_live_align RT AF Σg mg rmap _ ARTG RMIN) as RM16.
  pose proof (af_live_align RT AF Σg mg gmap _ ARTG GMIN) as GM16.
  pose proof (af_live_align RT AF Σg mg bmap _ ARTG BMIN) as BM16.
  pose proof (af_live_align RT AF Σg mg gm _ ARTG GIN) as W16.
  destruct (wr_at_rw_CB mg rmap (4 * c_n cv) (proj1 (af_acc_live RT AF Σg mg rmap (4 * c_n cv) ARTG RMIN)) ltac:(clear - N4; lia)) as (rbs & RBC).
  pose proof RBC as [[[RBL _] _] _]. cbn in RBL. apply u8arr_of_rw_cells in RBC.
  destruct (u8arr_u32arr mg rmap rbs (c_n cv) RBC ltac:(rewrite RBL; clear - N4; lia)) as (rws & UAR & UARL). clear RBC RBL.
  destruct (wr_at_rw_CB mg gmap (4 * c_n cv) (proj1 (af_acc_live RT AF Σg mg gmap (4 * c_n cv) ARTG GMIN)) ltac:(clear - N4; lia)) as (gbs & GBC).
  pose proof GBC as [[[GBL _] _] _]. cbn in GBL. apply u8arr_of_rw_cells in GBC.
  destruct (u8arr_u32arr mg gmap gbs (c_n cv) GBC ltac:(rewrite GBL; clear - N4; lia)) as (gws2 & UAGm & UAGmL). clear GBC GBL.
  destruct (wr_at_rw_CB mg bmap (4 * c_n cv) (proj1 (af_acc_live RT AF Σg mg bmap (4 * c_n cv) ARTG BMIN)) ltac:(clear - N4; lia)) as (bbs & BBC).
  pose proof BBC as [[[BBL _] _] _]. cbn in BBL. apply u8arr_of_rw_cells in BBC.
  destruct (u8arr_u32arr mg bmap bbs (c_n cv) BBC ltac:(rewrite BBL; clear - N4; lia)) as (bws & UAB & UABL). clear BBC BBL.
  pose proof GMZ as GMU. apply u8arr_of_rw_cells in GMU.
  destruct (u8arr_u32arr mg gm _ 256 GMU ltac:(rewrite repeat_length; reflexivity)) as (gws & UAG & UAGL). clear GMU.
  idtac "MARK gray arrays".
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (ACR : acc asegs mm rmap (4 * c_n cv)) by assumption;
    assert (ACG : acc asegs mm gmap (4 * c_n cv)) by assumption;
    assert (ACB : acc asegs mm bmap (4 * c_n cv)) by assumption;
    assert (ACW : acc asegs mm gm 1024) by assumption end.
  assert (Q1 : Z.of_nat (Z.to_nat (c_n cv)) = c_n cv - 0) by (clear - NZV; lia).
  assert (Q3 : (1 <= Z.to_nat (c_n cv))%nat) by (clear - NZV; lia).
  assert (Q4 : c_n cv <= 256) by (clear - CNN CN256; lia).
  assert (R5 : rmap mod 8 = 0) by (clear - RM16; Z.div_mod_to_equations; lia).
  assert (G5 : gmap mod 8 = 0) by (clear - GM16; Z.div_mod_to_equations; lia).
  assert (B5 : bmap mod 8 = 0) by (clear - BM16; Z.div_mod_to_equations; lia).
  assert (W5 : gm mod 8 = 0) by (clear - W16; Z.div_mod_to_equations; lia).
  idtac "MARK gray premises".
  replace (Z_to_bv 64 gm) with (Z_to_bv 64 (gm + 4 * 0)) by (f_equal; clear; lia).
  replace (Z_to_bv 64 rmap) with (Z_to_bv 64 (rmap + 4 * 0)) by (f_equal; clear; lia).
  replace (Z_to_bv 64 gmap) with (Z_to_bv 64 (gmap + 4 * 0)) by (f_equal; clear; lia).
  replace (Z_to_bv 64 bmap) with (Z_to_bv 64 (bmap + 4 * 0)) by (f_equal; clear; lia).
  replace (Z_to_bv 64 (c_n cv)) with (Z_to_bv 64 (c_n cv - 0)) by (f_equal; clear; lia).
  eapply evt_cut.
  { eapply (gray_loop (Z.to_nat (c_n cv)) 0).
    all: pose proof (proj1 (af_live_range RT AF Σg mg rmap _ ARTG RMIN)) as R0; pose proof (proj1 (af_live_range RT AF Σg mg gmap _ ARTG GMIN)) as G0;
         pose proof (proj1 (af_live_range RT AF Σg mg bmap _ ARTG BMIN)) as B0; pose proof (proj1 (af_live_range RT AF Σg mg gm _ ARTG GIN)) as W0.
    all: lazymatch goal with
         | |- Z.of_nat (Z.to_nat _) = _ => exact Q1
         | |- 0 <= 0 => clear; lia
         | |- (1 <= _)%nat => exact Q3
         | |- _ <= 256 => exact Q4
         | |- u32arr _ _ _ _ => first [exact UAR | exact UAGm | exact UAB | exact UAG]
         | |- _ => idtac
         end.
    all: lazymatch goal with
         | |- Z.of_nat (length _) = _ => first [assumption | idtac "LEFT-len"]
         | |- acc _ _ _ _ => first [assumption | idtac "LEFT-acc"]
         | |- 0 < _ => first [assumption | idtac "LEFT-pos"]
         | |- _ mod 8 = 0 => first [assumption | idtac "LEFT-mod"]
         | |- _ + _ <= 2 ^ _ => first [clear - CKR2 CKR3 CKR4 CKR8 SP0R1; lia | idtac "LEFT-hi"]
         | |- mem_inv _ _ => first [assumption | idtac "LEFT-mi"]
         | |- _ \/ _ => unfold SEGTOP_A; first [ assumption | match goal with H : parked ?T |- _ => unfold parked in H; exact H end | idtac "LEFT-disj" ]
         | |- ?g => idtac "LEFT:" g
         end.
  }
  idtac "MARK gray applied".
  intros ms' PO. unfold gray_exit in PO.
  destruct PO as (t0r & t1r & t2r & a1r & a2r & a3r & a4r & a5r & a6r & a7r & t3r & t4r & t5r & Fr & fcr & mr & -> & MUr & WMr & MIr).
  replace (gm + 4 * 0) with gm by (clear; lia).
  clear UAR UARL UAGm UAGmL UAB UABL UAG UAGL GMZ rws gws2 bws gws rbs gbs bbs ACR ACG ACB ACW Q1 Q3 Q4 R5 G5 B5 W5.
  assert (ARTl : ART RT Σg mr).
  { apply (art_client_writes RT AF Σg mg mr lo [(gm, gm + 1024)] ARTG MUr WMr).
    - rewrite SP0g. ul.
    - cbn [ivls_client]. split; [intros zz Hzz; right; right; left; exists gm, 1024; split; [exact GIN| clear - Hzz; lia]| exact I]. }
  idtac "MARK gray loop_art".
  lazymatch type of MUr with munch _ ?ma ?mb =>
    loop_transport ma mb MUr ltac:(fun Hx => lazymatch type of Hx with (?A <= _ < _)%Z =>
      lazymatch A with
      | fr => clear - Hx FCD9
      | (fr / 8 + _)%Z => clear - Hx FCS9 FR64 FR0
      | pix => clear - Hx AGX
      | p_cmap v => clear - Hx AGC
      | pixd => clear - Hx AGP
      | (usp + _)%Z => clear - Hx CKR8 LOW LOR
      | (usp - _)%Z => clear - Hx CKR8 LOW LOR
      | lo => clear - Hx CKR8 LOW LOR
      | _ => clear - Hx CKS8
      end; unfold parked in *; unfold SEGTOP_A, shad, SHB in *; repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia] end) end.
  idtac "MARK gray loop_transport".
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; right; right; left; exists gm, 1024; split; [exact GIN| clear - Hzz; lia]| exact I]).
  lazymatch goal with MUx : munch _ ?mm mr |- _ =>
    agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (NCGM _ Hx) as NCx; clear - NCx; split; [lia| exact I]) end.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
  ctx_gc RT.
  idtac "MARK after gray".
  clear G0 G5 G6 G7 GSEV0.
  Time walk_to AF MST [(usp - 448, usp); (fr, fr + 504); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 64)] [0x9b220; 0x9c04c].
  rewrite !(sx32_small (p_h v)) by (clear - HDROK; destruct HDROK as (_ & _ & Q & _); lia).
  lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with false; [cbv iota| symmetry] end.
  2:{ change z64 with (Z_to_bv 64 0). rewrite bv_lts_zero_l. rewrite unsigned_lit by (clear - HDROK; destruct HDROK as (_ & _ & Q & _); lia).
      clear - HDROK. destruct HDROK as (_ & _ & Q & _).
      replace (0 <? p_h v) with true by (symmetry; apply Z.ltb_lt; lia). replace (p_h v <? 2 ^ 63) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
  Time awalk [0x9b220; 0x9c04c].
  idtac "MARK at rows".
  fold_mkR.
  (* [comment removed for export] *)
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
  lazymatch goal with MUx : munch _ mr ?mm |- _ =>
    agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx) as P1; destruct (NFA _ Hx) as [N1 N2]; clear - P1 N1 N2 LOW LOR SPT SPA SPB FR0 FR64;
                                         repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  ctx_gc RT.
  idtac "MARK rows art".
  assert (WB : 0 < p_w v <= 20000 /\ 0 < p_h v <= 20000 /\ p_wpl v = (p_w v * 8 + 31) / 32)
    by (clear - HDROK D8; destruct HDROK as (_ & Q2 & Q3 & Q4 & _); rewrite D8 in Q4; split; [exact Q2| split; [exact Q3| exact Q4]]).
  destruct WB as (WB & HB & EWPL).
  assert (WPLB : 0 < p_wpl v <= 5001) by (rewrite EWPL; clear - WB; Z.div_mod_to_equations; lia).
  rewrite !(sx32_small (p_wpl v)) in FR by (clear - WPLB; lia). rewrite !(unsigned_lit (p_wpl v)) in FR by (clear - WPLB; lia).
  replace (p_wpl v * 4) with (4 * p_wpl v) in FR by (clear; lia).
  rewrite (sx32_small (p_w v)) in FRM by (clear - WB; lia). rewrite (sx32_small (p_h v)) in FRM by (clear - HB; lia). rewrite (sx32_small 8) in FRM by (clear; lia).
  (* [comment removed for export] *)
  lazymatch type of FRM with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: CB 56 ?j :: ?rest) =>
    change (c0 :: c1 :: c2 :: CB 56 j :: rest) with ([c0; c1; c2] ++ CB 56 j :: rest) in FRM;
    apply (rw_cells_split_CB asegs _ _ [c0; c1; c2] 56 j rest [24; 4; 28]%nat) in FRM; [| reflexivity]; cbn [mk_CB_cells app] in FRM end.
  split_at FRM 4%nat FRMq. split_at FRMq 1%nat FRMb.
  destruct (CB4_cell _ _ _ FRMq) as (gv0 & FGV). clear FRMq.
  pose proof FRMb as T. split_at T 1%nat T80. split_at T80 1%nat T2. clear T T2.
  pose proof FRMb as T. split_at T 3%nat T96. split_at T96 1%nat T2. clear T T2.
  pose proof FRMb as T. split_at T 5%nat T112. split_at T112 1%nat T2. clear T T2.
  pose proof FR as T. split_at T 7%nat S56. split_at S56 2%nat T2. clear T T2.
  pose proof FR as T. split_at T 11%nat S96. split_at S96 1%nat T2. clear T T2.
  pose proof FR as T. split_at T 14%nat S128. split_at S128 8%nat T2. clear T T2.
  idtac "MARK rows cells".
  assert (RSD' : 4 * (p_wpl v * p_h v) <= 67108864) by (clear - RSD1; lia).
  assert (S8 : p_data v mod 8 = 0) by (clear - D16; Z.div_mod_to_equations; lia).
  assert (SHI : p_data v + 4 * (p_wpl v * p_h v) <= 2 ^ 47) by (clear - CKR1 SP0R1; lia).
  assert (T8 : dat mod 8 = 0) by (clear - DD16; Z.div_mod_to_equations; lia).
  lazymatch goal with H : dat + rs <= rt_sp0 RT Σ - _ |- _ => assert (THI : dat + 4 * (p_wpl v * p_h v) <= 2 ^ 47) by (clear - H ERS SP0R1; lia) end.
  assert (W8 : gm mod 8 = 0) by (clear - W16; Z.div_mod_to_equations; lia).
  assert (WHI : gm + 1024 <= 2 ^ 47) by (clear - CKR8 SP0R1; lia).
  assert (SSH : p_data v + 4 * (p_wpl v * p_h v) <= 0x7fff7000 \/ 0x10007fff8000 <= p_data v) by (clear - CKH1; unfold parked in CKH1; lia).
  assert (SSG : p_data v + 4 * (p_wpl v * p_h v) <= 0x10000 \/ SEGTOP_A <= p_data v) by (clear - CKS1; unfold parked in CKS1; unfold SEGTOP_A; lia).
  lazymatch goal with H1 : parked (dat + rs <= 2147446784 \/ _), H2 : parked (dat + rs <= 65536 \/ _) |- _ =>
    assert (TSH : dat + 4 * (p_wpl v * p_h v) <= 0x7fff7000 \/ 0x10007fff8000 <= dat) by (clear - H1 ERS; unfold parked in H1; lia);
    assert (TSG : dat + 4 * (p_wpl v * p_h v) <= 0x10000 \/ SEGTOP_A <= dat) by (clear - H2 ERS; unfold parked in H2; unfold SEGTOP_A; lia) end.
  assert (WSH : gm + 1024 <= 0x7fff7000 \/ 0x10007fff8000 <= gm) by (clear - CKH8; unfold parked in CKH8; lia).
  assert (WSG : gm + 1024 <= 0x10000 \/ SEGTOP_A <= gm) by (clear - CKS8; unfold parked in CKS8; unfold SEGTOP_A; lia).
  assert (AGD' : gm + 1024 <= dat \/ dat + 4 * (p_wpl v * p_h v) <= gm) by (clear - AGD ERS; unfold parked in AGD; lia).
  lazymatch goal with A : ART RT Σg m0 |- _ =>
    pose proof (live_apart2 RT AF Σg m0 (p_data v) (4 * (p_wpl v * p_h v)) dat rs A (LSUBg _ DIN) DDIN ltac:(intros E; injection E as E1 E2; exact (NSD E1))) as ASD end.
  assert (ASD' : p_data v + 4 * (p_wpl v * p_h v) <= dat \/ dat + 4 * (p_wpl v * p_h v) <= p_data v) by (clear - ASD ERS; lia). clear ASD.
  assert (F0 : 0 < fr) by exact FR0.
  assert (F32 : fr mod 32 = 0) by (clear - FR64; Z.div_mod_to_equations; lia).
  assert (FHI' : fr + 320 <= 2 ^ 47) by (clear - FRHI SP0R1; lia).
  assert (FHS : fr + 320 <= 0x7fff7000 \/ 0x10007fff8000 <= fr) by (clear - FRSH; unfold parked in FRSH; lia).
  assert (FSG : fr + 320 <= 0x10000 \/ SEGTOP_A <= fr) by (clear - FRSEG; unfold SEGTOP_A; lia).
  lazymatch goal with H : parked (fr + 512 <= dat \/ dat + rs <= fr) |- _ => assert (FAD : fr + 320 <= dat \/ dat + 4 * (p_wpl v * p_h v) <= fr) by (clear - H ERS; unfold parked in H; lia) end.
  assert (FAS : fr + 320 <= p_data v \/ p_data v + 4 * (p_wpl v * p_h v) <= fr) by (clear - FCD0; unfold parked in FCD0; lia).
  assert (FAG : fr + 320 <= gm \/ gm + 1024 <= fr) by (clear - FCD9; unfold parked in FCD9; lia).
  assert (B0 : 0 < usp + -320) by (clear - LOR STa; lia).
  assert (B8 : (usp + -320) mod 8 = 0) by (clear - SPA; Z.div_mod_to_equations; lia).
  assert (BHI : usp + -320 + 192 <= 2 ^ 47) by (clear - SPT; lia).
  lazymatch goal with H : dat + rs <= rt_sp0 RT Σ - _ |- _ => assert (BAD : usp + -320 + 192 <= dat \/ dat + 4 * (p_wpl v * p_h v) <= usp + -320) by (clear - H ERS LOW LOR; lia) end.
  assert (BAF : usp + -320 + 192 <= fr \/ fr + 320 <= usp + -320) by (clear - FRHI LOW LOR; lia).
  (* [comment removed for export] *)
  lazymatch goal with A : ART RT Σg m0 |- _ =>
    destruct (wr_at_rw_CB m0 (p_data v) (4 * (p_wpl v * p_h v)) (proj1 (af_acc_live RT AF Σg m0 _ _ A (LSUBg _ DIN))) ltac:(clear - RSD0; lia)) as (sbs & SBC);
    destruct (wr_at_rw_CB m0 dat rs (proj1 (af_acc_live RT AF Σg m0 _ _ A DDIN)) ltac:(clear - RSD0 ERS; lia)) as (dbs & DBC);
    destruct (wr_at_rw_CB m0 gm 1024 (proj1 (af_acc_live RT AF Σg m0 _ _ A GIN)) ltac:(clear; lia)) as (wbs & WBC) end.
  pose proof SBC as [[[SBL _] _] _]. cbn in SBL. apply u8arr_of_rw_cells in SBC.
  destruct (u8arr_u32arr m0 (p_data v) sbs (p_wpl v * p_h v) SBC ltac:(rewrite SBL; clear - RSD0; lia)) as (ws & UAS & UASL). clear SBC SBL.
  pose proof DBC as [[[DBL _] _] _]. cbn in DBL. apply u8arr_of_rw_cells in DBC. rewrite ERS in DBL.
  destruct (u8arr_u32arr m0 dat dbs (p_wpl v * p_h v) DBC ltac:(rewrite DBL; clear - RSD0; lia)) as (wd & UAD & UADL). clear DBC DBL.
  pose proof WBC as [[[WBL _] _] _]. cbn in WBL. apply u8arr_of_rw_cells in WBC.
  destruct (u8arr_u32arr m0 gm wbs 256 WBC ltac:(rewrite WBL; clear; lia)) as (gws & UAW & UAWL). clear WBC WBL.
  lazymatch goal with |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mm _))) _ =>
    assert (ACS : acc asegs mm (p_data v) (4 * (p_wpl v * p_h v))) by assumption;
    assert (ACD : acc asegs mm dat (4 * (p_wpl v * p_h v))) by (rewrite <- ERS; assumption);
    assert (ACW : acc asegs mm gm 1024) by assumption end.
  assert (Q1 : Z.of_nat (Z.to_nat (p_h v)) = p_h v - 0) by (clear - HB; lia).
  assert (Q3 : (1 <= Z.to_nat (p_h v))%nat) by (clear - HB; lia).
  idtac "MARK rows premises".
  Time walk_to AF MST [(dat, dat + 4 * (p_wpl v * p_h v)); (fr + 48, fr + 48 + 4)] [0x9b220].
  eapply evt_cut.
  { eapply EVQ.
    { eapply (rmc_rows (Z.to_nat (p_h v)) 0) with (datas := p_data v) (datad := dat) (gm := gm) (wpl := p_wpl v) (w := p_w v) (h := p_h v) (fr := fr) (sb := usp + -320)
                                               (ws := ws) (wd := wd) (gws := gws) (gv := gv0).
      all: lazymatch goal with
         | |- Z.of_nat (Z.to_nat _) = _ => exact Q1
         | |- 0 <= 0 => clear; lia
         | |- (1 <= _)%nat => exact Q3
         | |- 0 < _ <= 20000 => first [exact WB | exact HB]
         | |- _ = (_ * 8 + 31) / 32 => exact EWPL
         | |- 4 * _ <= _ => exact RSD'
         | |- u32arr _ _ _ _ => first [exact UAS | exact UAD | exact UAW]
         | |- Z.of_nat (length _) = _ => first [assumption | idtac "LEFT-len"]
         | |- acc _ _ _ _ => first [assumption | idtac "LEFT-acc"]
         | |- 0 < _ => first [assumption | idtac "LEFT-pos"]
         | |- _ mod _ = 0 => first [assumption | idtac "LEFT-mod"]
         | |- _ + _ <= 2 ^ _ => first [assumption | idtac "LEFT-hi"]
         | |- mem_inv _ _ => first [assumption | idtac "LEFT-mi"]
         | |- rw_cells _ ?mm ?A ?cs => first [ assumption | match goal with H : rw_cells _ mm ?B cs |- _ => replace A with B by (clear; lia); exact H end | idtac "LEFT-cells" A ]
         | |- _ \/ _ => first [ assumption | exact SSH | exact SSG | exact TSH | exact TSG | exact WSH | exact WSG | exact ASD' | exact AGD' | exact FHS | exact FSG | exact FAD | exact FAS | exact FAG | exact BAD | exact BAF | idtac "LEFT-disj" ]
         | |- ?g => idtac "LEFT:" g
         end.
      replace (usp + -320 + 128) with (usp + -192) by (clear; lia). exact S128. }
    cbn [mkR].
    repeat first [ lazymatch goal with |- @eq Z _ _ => clear; lia end | progress f_equal | reflexivity ]. }
  idtac "MARK rows applied".
  intros ms' PO. unfold rmc_rows_exit in PO.
  destruct PO as (rar & t0q & t1q & t2q & a0q & a1q & a2q & a3q & a4q & a5q & a6q & a7q & s4q & s5q & s6q & s8q & t3q & t4q & t5q & gv1 & mw & wd1 & -> & MUw & WMw & MIw
                 & UASw & ACSw & UAWw & ACWw & UADw & UADLw & ACDw & T80w & FGVw & T96w & T112w & S56w & S96w & S128w).
  try fold_mkR.
  idtac "MARK rows post".
  clear T80 T96 T112 S56 S96 S128 FGV UAS UASL UAD UADL UAW UAWL ACS ACD ACW Q1 Q3 RORMC ROHALF.
  lazymatch goal with H : parked (fr + 512 <= pixd \/ _) |- _ => rename H into FCDP end.
  lazymatch goal with H : parked (fr + 512 <= dat \/ _) |- _ => rename H into FCDD end.
  lazymatch goal with H : parked (dat + rs <= fr / 8 + _ \/ _) |- _ => rename H into FCSD end.
  lazymatch goal with H : parked (fr + 512 <= pix \/ _) |- _ => rename H into FCDX end.
  lazymatch goal with H : parked (fr + 512 <= p_cmap v \/ _) |- _ => rename H into FCDC end.
  lazymatch goal with H : dat + rs <= rt_sp0 RT Σ - _ |- _ => rename H into CKRD end.
  lazymatch goal with H : parked (dat + rs <= 65536 \/ _) |- _ => rename H into CKSD end.
  loop_art RT AF Σg mw lo MUw ltac:(cbn [ivls_client]; split; [intros zz Hzz; right; right; left; exists dat, rs; split; [exact DDIN| clear - Hzz ERS; lia]| split; [intros zz Hzz; fframe_tac| exact I]]).
  idtac "MARK rows loop_art".
  lazymatch type of MUw with munch _ ?ma ?mb =>
    loop_transport ma mb MUw ltac:(fun Hx => lazymatch type of Hx with (?A <= _ < _)%Z =>
      lazymatch A with
      | fr => clear - Hx FCDD ERS
      | (fr + _)%Z => clear - Hx FCDD ERS
      | (fr / 8 + _)%Z => clear - Hx FCSD ERS FR64 FR0 FRSEG FRSH
      | pix => clear - Hx ADP ERS FCDX
      | p_cmap v => clear - Hx ADC ERS FCDC
      | pixd => clear - Hx ADX ERS FCDP
      | (usp + _)%Z => clear - Hx CKRD ERS LOW LOR FRHI
      | (usp - _)%Z => clear - Hx CKRD ERS LOW LOR FRHI
      | lo => clear - Hx CKRD ERS LOW LOR FRHI
      | _ => clear - Hx CKSD ERS FRSEG
      end; unfold parked in *; unfold SEGTOP_A, shad, SHB in *; repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia] end) end.
  idtac "MARK rows loop_transport".
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; right; right; left; exists dat, rs; split; [exact DDIN| clear - Hzz ERS; lia]| split; [intros zz Hzz; fframe_tac| exact I]]).
  lazymatch goal with MUx : munch _ ?mm mw |- _ =>
    agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (NCD _ Hx) as NCx; destruct (NFA _ Hx) as [N1 N2]; clear - NCx N1 ERS; repeat split; try exact I; lia) end.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
  ctx_gc RT.
  idtac "MARK after rows".
  clear T80w T96w T112w S56w S96w S128w UASw UAWw UADw UADLw. try clear ACSw. try clear ACWw. try clear ACDw. try clear ws. try clear wd1. try clear gws.
  join_cells FRM FGVw. join_cells FRM FRMb.
  (* [comment removed for export] *)
  assert (LVPg : forall e, In e (rt_live RT Σg) -> 0 < snd e).
  { intros [q k] Hq. rewrite LVG in Hq. cbn [In] in Hq. cbn [snd].
    destruct Hq as [E|[E|[E|[E|[E|[E|[E|Hq]]]]]]];
      [injection E as <- <-; clear; lia | injection E as <- <-; clear - RSD0 ERS; lia | injection E as <- <-; clear; lia
      | injection E as <- <-; exact N4 | injection E as <- <-; exact N4 | injection E as <- <-; exact N4 | injection E as <- <-; exact N4 | exact (LVP q k Hq)]. }
  lazymatch goal with A : ART RT Σg ?mm |- _ =>
    assert (NEW : forall e, In e ((dat, rs) :: (pixd, 64) :: (amap, 4 * c_n cv) :: (bmap, 4 * c_n cv) :: (gmap, 4 * c_n cv) :: (rmap, 4 * c_n cv) :: rt_live RT Σ) -> fst e <> gm)
      by (intros e He; apply (fresh_chunk_ne RT AF Σg mm [] gm 1024 ((dat, rs) :: (pixd, 64) :: (amap, 4 * c_n cv) :: (bmap, 4 * c_n cv) :: (gmap, 4 * c_n cv) :: (rmap, 4 * c_n cv) :: rt_live RT Σ) e A); [exact LVG | exact He | clear; lia | apply LVPg; rewrite LVG; right; exact He]);
    assert (NER : forall e, In e ([(gm, 1024); (dat, rs); (pixd, 64); (amap, 4 * c_n cv); (bmap, 4 * c_n cv); (gmap, 4 * c_n cv)] ++ rt_live RT Σ) -> fst e <> rmap)
      by (intros e He; apply (fresh_chunk_ne RT AF Σg mm [(gm, 1024); (dat, rs); (pixd, 64); (amap, 4 * c_n cv); (bmap, 4 * c_n cv); (gmap, 4 * c_n cv)] rmap (4 * c_n cv) (rt_live RT Σ) e A); [rewrite LVG; reflexivity | exact He | exact N4
          | apply LVPg; rewrite LVG; cbn [app In] in He |- *; tauto]);
    assert (NEG : forall e, In e ([(gm, 1024); (dat, rs); (pixd, 64); (amap, 4 * c_n cv); (bmap, 4 * c_n cv)] ++ (rmap, 4 * c_n cv) :: rt_live RT Σ) -> fst e <> gmap)
      by (intros e He; apply (fresh_chunk_ne RT AF Σg mm [(gm, 1024); (dat, rs); (pixd, 64); (amap, 4 * c_n cv); (bmap, 4 * c_n cv)] gmap (4 * c_n cv) ((rmap, 4 * c_n cv) :: rt_live RT Σ) e A); [rewrite LVG; reflexivity | exact He | exact N4
          | apply LVPg; rewrite LVG; cbn [app In] in He |- *; tauto]);
    assert (NEB : forall e, In e ([(gm, 1024); (dat, rs); (pixd, 64); (amap, 4 * c_n cv)] ++ (gmap, 4 * c_n cv) :: (rmap, 4 * c_n cv) :: rt_live RT Σ) -> fst e <> bmap)
      by (intros e He; apply (fresh_chunk_ne RT AF Σg mm [(gm, 1024); (dat, rs); (pixd, 64); (amap, 4 * c_n cv)] bmap (4 * c_n cv) ((gmap, 4 * c_n cv) :: (rmap, 4 * c_n cv) :: rt_live RT Σ) e A); [rewrite LVG; reflexivity | exact He | exact N4
          | apply LVPg; rewrite LVG; cbn [app In] in He |- *; tauto]);
    assert (NEA : forall e, In e ([(gm, 1024); (dat, rs); (pixd, 64)] ++ (bmap, 4 * c_n cv) :: (gmap, 4 * c_n cv) :: (rmap, 4 * c_n cv) :: rt_live RT Σ) -> fst e <> amap)
      by (intros e He; apply (fresh_chunk_ne RT AF Σg mm [(gm, 1024); (dat, rs); (pixd, 64)] amap (4 * c_n cv) ((bmap, 4 * c_n cv) :: (gmap, 4 * c_n cv) :: (rmap, 4 * c_n cv) :: rt_live RT Σ) e A); [rewrite LVG; reflexivity | exact He | exact N4
          | apply LVPg; rewrite LVG; cbn [app In] in He |- *; tauto]) end.
  idtac "MARK NE facts".
  (* [comment removed for export] *)
  Time walk_to AF MST [(usp - 448, usp); (fr, fr + 504); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 64)] [e_free; 0x9ae8c].
  try fold_mkR.
  pose proof (bv_unsigned_in_range 64 s0) as RS0. unfold bv_modulus in RS0. change (2 ^ Z.of_N 64) with (2^64) in RS0.
  pose proof (bv_unsigned_in_range 64 ra) as RRA. unfold bv_modulus in RRA. change (2 ^ Z.of_N 64) with (2^64) in RRA.
  assert (RALO : 4096 <= bv_unsigned ra < 2^64) by (split; [lazymatch goal with H : 4096 <= bv_unsigned ra |- _ => exact H | H : 4096 <= bv_unsigned ra < _ |- _ => exact (proj1 H) end | exact (proj2 RRA)]). clear RRA.
  pose proof UC as UCX. unfold uctx in UCX. rewrite ESP in UCX. rewrite unsigned_lit in UCX by (clear - USP0 USP1; lia).
  assert (TR6 : In (0x9c05c :: bv_unsigned ra :: ras) CLIENT_TRACES).
  { pose proof TRS as T6. rewrite Forall_forall in T6. destruct (T6 0x9c05c ltac:(cbn; tauto)) as [H|H]; [exact H|].
    exfalso. apply (not_In_ct [0x9c05c]); [vm_compute; reflexivity| exact H]. }
  pose proof FR as FRrec. split_at FRrec 35%nat FRrec2. clear FRrec.
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx) as P1; destruct (NFA _ Hx) as [N1 N2]; clear - P1 N1 N2 LOW LOR SPT SPA SPB FR0 FR64;
                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  idtac "MARK at_call free gm".
  eapply cps_seq.
  { pose proof (gp_free RT GP) as FC; unfold free_contractC in FC; eapply FC with (lo := lo) (p := gm) (n := 1024); rt_side idtac.
    all: lazymatch goal with
         | |- In _ _ => exact GIN
         | |- unwind_okC _ _ _ _ =>
             exists (bv_unsigned ra :: ras); rewrite ?unsigned_lit by ul; split; [| exact TR6];
             apply (chain_ok_push _ (usp + -320) usp (bv_unsigned ra) (bv_unsigned s0) ras);
               [ clear - USP0; lia | clear - SPA; Z.div_mod_to_equations; lia | clear - SPT; ul | exact RALO | exact RS0
               | rewrite !Z_to_bv_bv_unsigned; first [exact FRrec2 | lazymatch type of FRrec2 with rw_cells _ _ ?A _ => replace (usp + -16) with A by (clear; lia); exact FRrec2 end]
               | ];
             apply (chain_ok_keep ras m _ usp (bv_unsigned s0) UCX);
             eapply agree_sub; [exact AGF|]; intros zx Hzx; left; exact Hzx
         | |- ?g => idtac "LEFT:" g
         end. }
  idtac "MARK free gm applied".
  clear FRrec2 RS0 RALO UCX.
  (* [comment removed for export] *)
  assert (NXW : parked (pix <> gm)) by (exact (NEW (pix, 64) ltac:(do 6 right; exact PIN))).
  assert (NCW : parked (p_cmap v <> gm)) by (exact (NEW (p_cmap v, 24) ltac:(do 6 right; exact CIN))).
  assert (NPW : parked (pixd <> gm)) by (exact (NEW (pixd, 64) ltac:(cbn; tauto))).
  assert (NDW : parked (dat <> gm)) by (exact (NEW (dat, rs) ltac:(cbn; tauto))).
  assert (NSW : parked (p_data v <> gm)) by (exact (NEW (p_data v, 4 * (p_wpl v * p_h v)) ltac:(do 6 right; exact DIN))).
  assert (NAW : parked (c_arr cv <> gm)) by (exact (NEW (c_arr cv, 4 * c_nalloc cv) ltac:(do 6 right; exact AIN))).
  assert (NXR : parked (pix <> rmap)) by (exact (NER (pix, 64) ltac:(cbn [app]; do 6 right; exact PIN))).
  assert (NCR' : parked (p_cmap v <> rmap)) by (exact (NER (p_cmap v, 24) ltac:(cbn [app]; do 6 right; exact CIN))).
  assert (NPR : parked (pixd <> rmap)) by (exact (NER (pixd, 64) ltac:(cbn; tauto))).
  assert (NDR : parked (dat <> rmap)) by (exact (NER (dat, rs) ltac:(cbn; tauto))).
  assert (NSR : parked (p_data v <> rmap)) by (exact (NER (p_data v, 4 * (p_wpl v * p_h v)) ltac:(cbn [app]; do 6 right; exact DIN))).
  assert (NAR : parked (c_arr cv <> rmap)) by (exact (NER (c_arr cv, 4 * c_nalloc cv) ltac:(cbn [app]; do 6 right; exact AIN))).
  assert (NXG : parked (pix <> gmap)) by (exact (NEG (pix, 64) ltac:(cbn [app]; do 6 right; exact PIN))).
  assert (NCG' : parked (p_cmap v <> gmap)) by (exact (NEG (p_cmap v, 24) ltac:(cbn [app]; do 6 right; exact CIN))).
  assert (NPG : parked (pixd <> gmap)) by (exact (NEG (pixd, 64) ltac:(cbn; tauto))).
  assert (NDG : parked (dat <> gmap)) by (exact (NEG (dat, rs) ltac:(cbn; tauto))).
  assert (NSG : parked (p_data v <> gmap)) by (exact (NEG (p_data v, 4 * (p_wpl v * p_h v)) ltac:(cbn [app]; do 6 right; exact DIN))).
  assert (NAG : parked (c_arr cv <> gmap)) by (exact (NEG (c_arr cv, 4 * c_nalloc cv) ltac:(cbn [app]; do 6 right; exact AIN))).
  assert (NXB : parked (pix <> bmap)) by (exact (NEB (pix, 64) ltac:(cbn [app]; do 6 right; exact PIN))).
  assert (NCB' : parked (p_cmap v <> bmap)) by (exact (NEB (p_cmap v, 24) ltac:(cbn [app]; do 6 right; exact CIN))).
  assert (NPB : parked (pixd <> bmap)) by (exact (NEB (pixd, 64) ltac:(cbn; tauto))).
  assert (NDB : parked (dat <> bmap)) by (exact (NEB (dat, rs) ltac:(cbn; tauto))).
  assert (NSB : parked (p_data v <> bmap)) by (exact (NEB (p_data v, 4 * (p_wpl v * p_h v)) ltac:(cbn [app]; do 6 right; exact DIN))).
  assert (NAB : parked (c_arr cv <> bmap)) by (exact (NEB (c_arr cv, 4 * c_nalloc cv) ltac:(cbn [app]; do 6 right; exact AIN))).
  assert (NXA : parked (pix <> amap)) by (exact (NEA (pix, 64) ltac:(cbn [app]; do 6 right; exact PIN))).
  assert (NCA' : parked (p_cmap v <> amap)) by (exact (NEA (p_cmap v, 24) ltac:(cbn [app]; do 6 right; exact CIN))).
  assert (NPA : parked (pixd <> amap)) by (exact (NEA (pixd, 64) ltac:(cbn; tauto))).
  assert (NDA : parked (dat <> amap)) by (exact (NEA (dat, rs) ltac:(cbn; tauto))).
  assert (NSA : parked (p_data v <> amap)) by (exact (NEA (p_data v, 4 * (p_wpl v * p_h v)) ltac:(cbn [app]; do 6 right; exact DIN))).
  assert (NAA : parked (c_arr cv <> amap)) by (exact (NEA (c_arr cv, 4 * c_nalloc cv) ltac:(cbn [app]; do 6 right; exact AIN))).
  idtac "MARK NE parked".
  after_call RT AF.
  lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σ1; rename A into ART1; rename mm into m1f end.
  lazymatch goal with H : rt_live RT Σ1 = live_remove gm _ |- _ => rename H into LV1r end.
  assert (LV1 : rt_live RT Σ1 = (dat, rs) :: (pixd, 64) :: (amap, 4 * c_n cv) :: (bmap, 4 * c_n cv) :: (gmap, 4 * c_n cv) :: (rmap, 4 * c_n cv) :: rt_live RT Σ).
  { rewrite LV1r, LVG, live_remove_head. apply live_remove_fresh. exact NEW. }
  fold_ag ltac:(fun Hx => apply (aclient_mono LVF _ usp _ _ _ _ Hx); [intros e He; rewrite LV1; do 6 right; exact He| solve [frames_sub_tac]| clear; lia]).
  idtac "MARK after free gm".
  (* [comment removed for export] *)
  assert (NMAR : parked (amap <> rmap)) by (exact (NER (amap, 4 * c_n cv) ltac:(cbn; tauto))).
  assert (NMBR : parked (bmap <> rmap)) by (exact (NER (bmap, 4 * c_n cv) ltac:(cbn; tauto))).
  assert (NMGR : parked (gmap <> rmap)) by (exact (NER (gmap, 4 * c_n cv) ltac:(cbn; tauto))).
  assert (NMAG : parked (amap <> gmap)) by (exact (NEG (amap, 4 * c_n cv) ltac:(cbn; tauto))).
  assert (NMBG : parked (bmap <> gmap)) by (exact (NEG (bmap, 4 * c_n cv) ltac:(cbn; tauto))).
  assert (NMAB : parked (amap <> bmap)) by (exact (NEB (amap, 4 * c_n cv) ltac:(cbn; tauto))).
  (* [comment removed for export] *)
  assert (FRS1 : rt_frames RT Σ1 = (fr, 3%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σ1 = _ |- _ => rewrite E end; first [exact FRSg | assumption]).
  assert (SP01 : rt_sp0 RT Σ1 = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; reflexivity).
  assert (CR1 : rt_credit RT Σ - (RASTER_COST + 9) <= rt_credit RT Σ1) by (repeat match goal with E : rt_credit RT Σ1 = _ |- _ => rewrite E end; assumption).
  sigma_gc RT Σ Σ1.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
  ctx_gc RT.
  idtac "MARK before free 2".
  walk_to AF MST [(usp - 448, usp); (fr, fr + 504); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 64)] [e_free; 0x9a78c].
  assert (TR7 : In (0x9c0dc :: bv_unsigned ra :: ras) CLIENT_TRACES).
  { pose proof TRS as T6. rewrite Forall_forall in T6. destruct (T6 0x9c0dc ltac:(cbn; tauto)) as [H|H]; [exact H|].
    exfalso. apply (not_In_ct [0x9c0dc]); [vm_compute; reflexivity| exact H]. }
  pose proof (bv_unsigned_in_range 64 s0) as RS0. unfold bv_modulus in RS0. change (2 ^ Z.of_N 64) with (2^64) in RS0.
  pose proof (bv_unsigned_in_range 64 ra) as RRA. unfold bv_modulus in RRA. change (2 ^ Z.of_N 64) with (2^64) in RRA.
  assert (RALO : 4096 <= bv_unsigned ra < 2^64) by (split; [lazymatch goal with H : 4096 <= bv_unsigned ra |- _ => exact H | H : 4096 <= bv_unsigned ra < _ |- _ => exact (proj1 H) end | exact (proj2 RRA)]). clear RRA.
  pose proof UC as UCX. unfold uctx in UCX. rewrite ESP in UCX. rewrite unsigned_lit in UCX by (clear - USP0 USP1; lia).
  pose proof FR as FRrec. split_at FRrec 35%nat FRrec2. clear FRrec.
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx) as P1; destruct (NFA _ Hx) as [N1 N2]; clear - P1 N1 N2 LOW LOR SPT SPA SPB FR0 FR64;
                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  eapply cps_seq.
  { pose proof (gp_free RT GP) as FC; unfold free_contractC in FC; eapply FC with (lo := lo) (p := rmap) (n := 4 * c_n cv); rt_side idtac.
    all: lazymatch goal with
         | |- In _ _ => rewrite LV1; do 5 right; left; reflexivity
         | |- unwind_okC _ _ _ _ =>
             exists (bv_unsigned ra :: ras); rewrite ?unsigned_lit by ul; split; [| exact TR7];
             apply (chain_ok_push _ (usp + -320) usp (bv_unsigned ra) (bv_unsigned s0) ras);
               [ clear - USP0; lia | clear - SPA; Z.div_mod_to_equations; lia | clear - SPT; ul | exact RALO | exact RS0
               | rewrite !Z_to_bv_bv_unsigned; first [exact FRrec2 | lazymatch type of FRrec2 with rw_cells _ _ ?A _ => replace (usp + -16) with A by (clear; lia); exact FRrec2 end]
               | ];
             apply (chain_ok_keep ras m _ usp (bv_unsigned s0) UCX);
             eapply agree_sub; [exact AGF|]; intros zx Hzx; left; exact Hzx
         | |- ?g => idtac "LEFT:" g
         end. }
  idtac "MARK free 2 applied".
  clear FRrec2 RS0 RALO UCX.
  try (assert (PDINF : In (pixd, 64) ((dat, rs) :: (pixd, 64) :: rt_live RT Σ)) by (right; left; reflexivity)).
  after_call RT AF.
  lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σ2; rename A into ART2f end.
  lazymatch goal with H : rt_live RT Σ2 = live_remove rmap _ |- _ => rename H into LV2r end.
  assert (LV2 : rt_live RT Σ2 = (dat, rs) :: (pixd, 64) :: (amap, 4 * c_n cv) :: (bmap, 4 * c_n cv) :: (gmap, 4 * c_n cv) :: rt_live RT Σ).
  { rewrite LV2r, LV1. rewrite ?live_remove_other by assumption. rewrite live_remove_head.
    rewrite (live_remove_fresh rmap (rt_live RT Σ)); [reflexivity|]. intros e He. apply NER. cbn [app]; do 6 right; exact He. }
  fold_ag ltac:(fun Hx => apply (aclient_mono LVF _ usp _ _ _ _ Hx); [intros e He; rewrite LV2; do 5 right; exact He| solve [frames_sub_tac]| clear; lia]).
  idtac "MARK after free 2".
  (* [comment removed for export] *)
  assert (FRS2 : rt_frames RT Σ2 = (fr, 3%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σ2 = _ |- _ => rewrite E end; first [exact FRSg | assumption]).
  assert (SP02 : rt_sp0 RT Σ2 = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; reflexivity).
  assert (CR2 : rt_credit RT Σ - (RASTER_COST + 9) <= rt_credit RT Σ2) by (repeat match goal with E : rt_credit RT Σ2 = _ |- _ => rewrite E end; assumption).
  sigma_gc RT Σ Σ2.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
  ctx_gc RT.
  idtac "MARK before free 3".
  walk_to AF MST [(usp - 448, usp); (fr, fr + 504); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 64)] [e_free; 0x9a78c].
  assert (TR8 : In (0x9c0e4 :: bv_unsigned ra :: ras) CLIENT_TRACES).
  { pose proof TRS as T6. rewrite Forall_forall in T6. destruct (T6 0x9c0e4 ltac:(cbn; tauto)) as [H|H]; [exact H|].
    exfalso. apply (not_In_ct [0x9c0e4]); [vm_compute; reflexivity| exact H]. }
  pose proof (bv_unsigned_in_range 64 s0) as RS0. unfold bv_modulus in RS0. change (2 ^ Z.of_N 64) with (2^64) in RS0.
  pose proof (bv_unsigned_in_range 64 ra) as RRA. unfold bv_modulus in RRA. change (2 ^ Z.of_N 64) with (2^64) in RRA.
  assert (RALO : 4096 <= bv_unsigned ra < 2^64) by (split; [lazymatch goal with H : 4096 <= bv_unsigned ra |- _ => exact H | H : 4096 <= bv_unsigned ra < _ |- _ => exact (proj1 H) end | exact (proj2 RRA)]). clear RRA.
  pose proof UC as UCX. unfold uctx in UCX. rewrite ESP in UCX. rewrite unsigned_lit in UCX by (clear - USP0 USP1; lia).
  pose proof FR as FRrec. split_at FRrec 35%nat FRrec2. clear FRrec.
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx) as P1; destruct (NFA _ Hx) as [N1 N2]; clear - P1 N1 N2 LOW LOR SPT SPA SPB FR0 FR64;
                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  eapply cps_seq.
  { pose proof (gp_free RT GP) as FC; unfold free_contractC in FC; eapply FC with (lo := lo) (p := gmap) (n := 4 * c_n cv); rt_side idtac.
    all: lazymatch goal with
         | |- In _ _ => rewrite LV2; do 4 right; left; reflexivity
         | |- unwind_okC _ _ _ _ =>
             exists (bv_unsigned ra :: ras); rewrite ?unsigned_lit by ul; split; [| exact TR8];
             apply (chain_ok_push _ (usp + -320) usp (bv_unsigned ra) (bv_unsigned s0) ras);
               [ clear - USP0; lia | clear - SPA; Z.div_mod_to_equations; lia | clear - SPT; ul | exact RALO | exact RS0
               | rewrite !Z_to_bv_bv_unsigned; first [exact FRrec2 | lazymatch type of FRrec2 with rw_cells _ _ ?A _ => replace (usp + -16) with A by (clear; lia); exact FRrec2 end]
               | ];
             apply (chain_ok_keep ras m _ usp (bv_unsigned s0) UCX);
             eapply agree_sub; [exact AGF|]; intros zx Hzx; left; exact Hzx
         | |- ?g => idtac "LEFT:" g
         end. }
  idtac "MARK free 3 applied".
  clear FRrec2 RS0 RALO UCX.
  try (assert (PDINF : In (pixd, 64) ((dat, rs) :: (pixd, 64) :: rt_live RT Σ)) by (right; left; reflexivity)).
  after_call RT AF.
  lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σ3; rename A into ART3f end.
  lazymatch goal with H : rt_live RT Σ3 = live_remove gmap _ |- _ => rename H into LV3r end.
  assert (LV3 : rt_live RT Σ3 = (dat, rs) :: (pixd, 64) :: (amap, 4 * c_n cv) :: (bmap, 4 * c_n cv) :: rt_live RT Σ).
  { rewrite LV3r, LV2. rewrite ?live_remove_other by assumption. rewrite live_remove_head.
    rewrite (live_remove_fresh gmap (rt_live RT Σ)); [reflexivity|]. intros e He. apply NEG. cbn [app]; do 6 right; exact He. }
  fold_ag ltac:(fun Hx => apply (aclient_mono LVF _ usp _ _ _ _ Hx); [intros e He; rewrite LV3; do 4 right; exact He| solve [frames_sub_tac]| clear; lia]).
  idtac "MARK after free 3".
  (* [comment removed for export] *)
  assert (FRS3 : rt_frames RT Σ3 = (fr, 3%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σ3 = _ |- _ => rewrite E end; first [exact FRSg | assumption]).
  assert (SP03 : rt_sp0 RT Σ3 = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; reflexivity).
  assert (CR3 : rt_credit RT Σ - (RASTER_COST + 9) <= rt_credit RT Σ3) by (repeat match goal with E : rt_credit RT Σ3 = _ |- _ => rewrite E end; assumption).
  sigma_gc RT Σ Σ3.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
  ctx_gc RT.
  idtac "MARK before free 4".
  walk_to AF MST [(usp - 448, usp); (fr, fr + 504); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 64)] [e_free; 0x9a78c].
  assert (TR9 : In (0x9c0f0 :: bv_unsigned ra :: ras) CLIENT_TRACES).
  { pose proof TRS as T6. rewrite Forall_forall in T6. destruct (T6 0x9c0f0 ltac:(cbn; tauto)) as [H|H]; [exact H|].
    exfalso. apply (not_In_ct [0x9c0f0]); [vm_compute; reflexivity| exact H]. }
  pose proof (bv_unsigned_in_range 64 s0) as RS0. unfold bv_modulus in RS0. change (2 ^ Z.of_N 64) with (2^64) in RS0.
  pose proof (bv_unsigned_in_range 64 ra) as RRA. unfold bv_modulus in RRA. change (2 ^ Z.of_N 64) with (2^64) in RRA.
  assert (RALO : 4096 <= bv_unsigned ra < 2^64) by (split; [lazymatch goal with H : 4096 <= bv_unsigned ra |- _ => exact H | H : 4096 <= bv_unsigned ra < _ |- _ => exact (proj1 H) end | exact (proj2 RRA)]). clear RRA.
  pose proof UC as UCX. unfold uctx in UCX. rewrite ESP in UCX. rewrite unsigned_lit in UCX by (clear - USP0 USP1; lia).
  pose proof FR as FRrec. split_at FRrec 35%nat FRrec2. clear FRrec.
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx) as P1; destruct (NFA _ Hx) as [N1 N2]; clear - P1 N1 N2 LOW LOR SPT SPA SPB FR0 FR64;
                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  eapply cps_seq.
  { pose proof (gp_free RT GP) as FC; unfold free_contractC in FC; eapply FC with (lo := lo) (p := bmap) (n := 4 * c_n cv); rt_side idtac.
    all: lazymatch goal with
         | |- In _ _ => rewrite LV3; do 3 right; left; reflexivity
         | |- unwind_okC _ _ _ _ =>
             exists (bv_unsigned ra :: ras); rewrite ?unsigned_lit by ul; split; [| exact TR9];
             apply (chain_ok_push _ (usp + -320) usp (bv_unsigned ra) (bv_unsigned s0) ras);
               [ clear - USP0; lia | clear - SPA; Z.div_mod_to_equations; lia | clear - SPT; ul | exact RALO | exact RS0
               | rewrite !Z_to_bv_bv_unsigned; first [exact FRrec2 | lazymatch type of FRrec2 with rw_cells _ _ ?A _ => replace (usp + -16) with A by (clear; lia); exact FRrec2 end]
               | ];
             apply (chain_ok_keep ras m _ usp (bv_unsigned s0) UCX);
             eapply agree_sub; [exact AGF|]; intros zx Hzx; left; exact Hzx
         | |- ?g => idtac "LEFT:" g
         end. }
  idtac "MARK free 4 applied".
  clear FRrec2 RS0 RALO UCX.
  try (assert (PDINF : In (pixd, 64) ((dat, rs) :: (pixd, 64) :: rt_live RT Σ)) by (right; left; reflexivity)).
  after_call RT AF.
  lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σ4; rename A into ART4f end.
  lazymatch goal with H : rt_live RT Σ4 = live_remove bmap _ |- _ => rename H into LV4r end.
  assert (LV4 : rt_live RT Σ4 = (dat, rs) :: (pixd, 64) :: (amap, 4 * c_n cv) :: rt_live RT Σ).
  { rewrite LV4r, LV3. rewrite ?live_remove_other by assumption. rewrite live_remove_head.
    rewrite (live_remove_fresh bmap (rt_live RT Σ)); [reflexivity|]. intros e He. apply NEB. cbn [app]; do 6 right; exact He. }
  fold_ag ltac:(fun Hx => apply (aclient_mono LVF _ usp _ _ _ _ Hx); [intros e He; rewrite LV4; do 3 right; exact He| solve [frames_sub_tac]| clear; lia]).
  idtac "MARK after free 4".
  (* [comment removed for export] *)
  assert (FRS4 : rt_frames RT Σ4 = (fr, 3%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σ4 = _ |- _ => rewrite E end; first [exact FRSg | assumption]).
  assert (SP04 : rt_sp0 RT Σ4 = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; reflexivity).
  assert (CR4 : rt_credit RT Σ - (RASTER_COST + 9) <= rt_credit RT Σ4) by (repeat match goal with E : rt_credit RT Σ4 = _ |- _ => rewrite E end; assumption).
  sigma_gc RT Σ Σ4.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
  ctx_gc RT.
  idtac "MARK before free 5".
  walk_to AF MST [(usp - 448, usp); (fr, fr + 504); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 64)] [e_free; 0x9a78c].
  assert (TR10 : In (0x9c0fc :: bv_unsigned ra :: ras) CLIENT_TRACES).
  { pose proof TRS as T6. rewrite Forall_forall in T6. destruct (T6 0x9c0fc ltac:(cbn; tauto)) as [H|H]; [exact H|].
    exfalso. apply (not_In_ct [0x9c0fc]); [vm_compute; reflexivity| exact H]. }
  pose proof (bv_unsigned_in_range 64 s0) as RS0. unfold bv_modulus in RS0. change (2 ^ Z.of_N 64) with (2^64) in RS0.
  pose proof (bv_unsigned_in_range 64 ra) as RRA. unfold bv_modulus in RRA. change (2 ^ Z.of_N 64) with (2^64) in RRA.
  assert (RALO : 4096 <= bv_unsigned ra < 2^64) by (split; [lazymatch goal with H : 4096 <= bv_unsigned ra |- _ => exact H | H : 4096 <= bv_unsigned ra < _ |- _ => exact (proj1 H) end | exact (proj2 RRA)]). clear RRA.
  pose proof UC as UCX. unfold uctx in UCX. rewrite ESP in UCX. rewrite unsigned_lit in UCX by (clear - USP0 USP1; lia).
  pose proof FR as FRrec. split_at FRrec 35%nat FRrec2. clear FRrec.
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx) as P1; destruct (NFA _ Hx) as [N1 N2]; clear - P1 N1 N2 LOW LOR SPT SPA SPB FR0 FR64;
                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  eapply cps_seq.
  { pose proof (gp_free RT GP) as FC; unfold free_contractC in FC; eapply FC with (lo := lo) (p := amap) (n := 4 * c_n cv); rt_side idtac.
    all: lazymatch goal with
         | |- In _ _ => rewrite LV4; do 2 right; left; reflexivity
         | |- unwind_okC _ _ _ _ =>
             exists (bv_unsigned ra :: ras); rewrite ?unsigned_lit by ul; split; [| exact TR10];
             apply (chain_ok_push _ (usp + -320) usp (bv_unsigned ra) (bv_unsigned s0) ras);
               [ clear - USP0; lia | clear - SPA; Z.div_mod_to_equations; lia | clear - SPT; ul | exact RALO | exact RS0
               | rewrite !Z_to_bv_bv_unsigned; first [exact FRrec2 | lazymatch type of FRrec2 with rw_cells _ _ ?A _ => replace (usp + -16) with A by (clear; lia); exact FRrec2 end]
               | ];
             apply (chain_ok_keep ras m _ usp (bv_unsigned s0) UCX);
             eapply agree_sub; [exact AGF|]; intros zx Hzx; left; exact Hzx
         | |- ?g => idtac "LEFT:" g
         end. }
  idtac "MARK free 5 applied".
  clear FRrec2 RS0 RALO UCX.
  try (assert (PDINF : In (pixd, 64) ((dat, rs) :: (pixd, 64) :: rt_live RT Σ)) by (right; left; reflexivity)).
  after_call RT AF.
  lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σ5; rename A into ART5f end.
  lazymatch goal with H : rt_live RT Σ5 = live_remove amap _ |- _ => rename H into LV5r end.
  assert (LV5 : rt_live RT Σ5 = (dat, rs) :: (pixd, 64) :: rt_live RT Σ).
  { rewrite LV5r, LV4. rewrite ?live_remove_other by assumption. rewrite live_remove_head.
    rewrite (live_remove_fresh amap (rt_live RT Σ)); [reflexivity|]. intros e He. apply NEA. cbn [app]; do 6 right; exact He. }
  fold_ag ltac:(fun Hx => apply (aclient_mono LVF _ usp _ _ _ _ Hx); [intros e He; rewrite LV5; do 2 right; exact He| solve [frames_sub_tac]| clear; lia]).
  idtac "MARK after free 5".
  (* [comment removed for export] *)
  assert (FRS5 : rt_frames RT Σ5 = (fr, 3%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σ5 = _ |- _ => rewrite E end; first [exact FRS4 | assumption]).
  assert (SP05 : rt_sp0 RT Σ5 = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; reflexivity).
  assert (CR5 : rt_credit RT Σ - (RASTER_COST + 9) <= rt_credit RT Σ5) by (repeat match goal with E : rt_credit RT Σ5 = _ |- _ => rewrite E end; assumption).
  sigma_gc RT Σ Σ5.
  assert (PDIN5 : In (pixd, 64) (rt_live RT Σ5)) by (rewrite LV5; right; left; reflexivity).
  assert (DDIN5 : In (dat, rs) (rt_live RT Σ5)) by (rewrite LV5; left; reflexivity).
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
  ctx_gc RT.
  idtac "MARK before exit".
  forget_junk FR. forget_junk FRM. try forget_junk FSH.
  (* [comment removed for export] *)
  clear_acc.
  repeat match goal with H : rw_cells asegs _ ?b _ |- _ =>
    lazymatch b with fr => fail | (fr + _)%Z => fail | (fr / 8 + _)%Z => fail | (fr / 8 + _ + _)%Z => fail | (usp + _)%Z => fail | (usp - _)%Z => fail
    | pix => fail | pixd => fail | _ => clear H end end.
  repeat match goal with H : u8arr _ _ _ _ |- _ => clear H | H : u32arr _ _ _ _ |- _ => clear H | H : bytes_at _ _ _ _ |- _ => clear H end.
  hide FRSH. hide DDNE. hide VDATA1. hide CM.
  repeat match goal with H : parked ?T |- _ =>
    lazymatch T with
    | context [fr] => lazymatch T with context [pixd] => fail | context [pix] => fail | _ => clear H end
    | _ => clear H
    end end.
  unfold hid in FRSH, DDNE, VDATA1, CM. try unpark FRSH.
  idtac "MARK exit diet".
  walk_to AF MST [(usp - 448, usp); (fr, fr + 504); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 64)] [e_set_shadow 245].
  try fold_mkR.
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx) as P1; destruct (NFA _ Hx) as [N1 N2]; clear - P1 N1 N2 LOW LOR SPT SPA SPB FR0 FR64;
                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  idtac "MARK at_call set_shadow".
  eapply cps_seq.
  { pose proof (rc_set_shadow RT RC 245) as SS; unfold set_shadow_contract in SS; eapply SS with (lo := lo) (d := fr / 8 + 2147450880) (n := 64); rt_side idtac.
    all: first [ exact WRSH | unfold set_shadow_vals; cbn; tauto | lazymatch goal with |- ?g => idtac "LEFT:" g end ]. }
  idtac "MARK set_shadow applied".
  osd_mark_about (fr / 8). osd_mark LOW. osd_mark LOR. osd_mark SPT. osd_mark SPB. osd_mark STa. osd_mark SP0R0. osd_mark SP0R1. osd_mark FR0. osd_mark FRHI. osd_mark FRSEG. osd_mark FRSH. osd_mark FR64.
  after_call RT AF.
  osd_clear.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono LVF _ usp _ _ _ _ Hx); [intros e He; rewrite LV5; do 2 right; exact He| solve [frames_sub_tac]| clear; lia]
                                 | pose proof (NFA _ Hx) as [N1 N2]; clear - N1 N2; cbn [outside]; unfold shad, SHB in *; repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]]).
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  ctx_gc RT.
  idtac "MARK after set_shadow".
  walk_to AF MST [(usp - 448, usp); (fr, fr + 504); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 64)] [0x9a7e0].
  frame_release_g RT AF GP MST Σ fr 3%nat 512 PF0 AGF PFS usp lo 0x9a7e8
    ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
    ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx) as P1; destruct (NFA _ Hx) as [N1 N2]; clear - P1 N1 N2 LOW LOR SPT SPA SPB FR0 FR64; unfold shad, SHB in *;
                    repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia])
    ltac:(fun Hx => exact Hx)
    ltac:(fun fl FLN => idtac).
  idtac "MARK released".
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  walk_to AF MST [(usp - 448, usp)] (@nil Z).
  
  cps_stop.
  try fold_mkR.
  apply cps_finish. intros c Hc. subst QF. cbv beta.
  set (vf := pv_inf (pv_res v1 v) v).
  assert (VFC : pix_cells vf = [C4 (Z_to_bv 64 (p_w v)); C4 (Z_to_bv 64 (p_h v)); C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 (p_spp v1)); C4 (Z_to_bv 64 (p_wpl v)); C4 (Z_to_bv 64 1);
                                C4 (Z_to_bv 64 (p_xres v)); C4 (Z_to_bv 64 (p_yres v)); C4 (Z_to_bv 64 (p_inf v)); C4 (Z_to_bv 64 (p_spec v1)); C8 z64; C8 z64; C8 (Z_to_bv 64 dat)])
    by (unfold vf, pix_cells, pv_inf, pv_res; cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data]; rewrite VW, VH, VD, VCMAP, EWD; reflexivity).
  assert (LVE : rt_live RT S2 = (dat, rs) :: (pixd, 64) :: LVF) by (rewrite LV2, LV5; reflexivity).
  unfold hid in POBJ0, HOKD.
  exists S2, pixd, vf.
  split.
  - eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists.
    split; [unfold ret_st; do 16 eexists; reflexivity|].
    split; [split; [split; [exact ART2| split; assumption]| split; assumption]|].
    split; [intros a Ha Ho; apply AGF; exact Ha|].
    right. split; [exact CM|].
    split.
    { lazymatch goal with |- pix_obj _ ?mc _ _ _ =>
        apply (pix_obj_mono LVF _ mc pix v cv); [intros e He; rewrite LVE; do 2 right; exact He|];
        apply (pix_obj_agree LVF PF0 m mc pix v cv POBJ0 AGF PML); unfold pix_cells; rewrite D8; exact PXC end. }
    split.
    { split; [rewrite VFC; exact PXD|].
      split; [rewrite LVE; split; [right; left; reflexivity| split; [exact PD0| split; [exact PD16| clear; lia]]]|].
      split; [exact HOKD|].
      split; [right; split; [rewrite LVE; split; [left; unfold vf, pv_inf, pv_res, rsize; cbn [p_data p_wpl p_h]; rewrite VH, EWD; fold dat; rewrite <- ERS; reflexivity
                                                 | split; [exact DD0| split; [exact DD16| unfold vf, pv_inf, pv_res, rsize; cbn [p_wpl p_h]; rewrite VH, EWD, <- ERS; exact DDN]]]
                            | exact DDNE]|].
      left. exact VCMAP. }
    unfold vf, pv_inf, pv_res; cbn [p_w p_h p_d p_data p_cmap]. repeat split; first [exact VW | exact VH | exact VD | exact VDATA1 | exact VCMAP].
  - split; [intros Z0; exfalso; exact (CM Z0)|].
    split; [intros _; rewrite LVE; unfold vf, pv_inf, pv_res; cbn [p_data p_wpl p_h]; rewrite VH, EWD; fold dat; rewrite <- ERS; reflexivity|].
    split; [exact FRS2|]. split; [rewrite SP2; exact SP05|].
    rewrite CR2. clear - CR5. unfold RASTER_COST in *. lia.
Qed.
End RMC_Y0.
